#lang racket

(module piet racket
  (provide compile compile/with-debugging with-codal-size run-program
           program->instr-list instr-list->racket
           optimize-program->instr-list
           optimize-instr-list->racket
           restrained-inlining
           remove-unnecessary-defs
           noop +s /s >s dup in-char
           push -s %s pointer rolls
           out-num pop *s nots switch
           in-num out-char)
  (require 2htdp/image)
  (require (for-syntax syntax/parse racket/match
                       racket/set racket/list
                       2htdp/image))

  ;; for debugging interpreter
  (define debugging #f)

  ;; for representing a "key" codal
  ;; intersection("color", "codal") = "col"
  (struct col (hue lightness))

  ;; colour block
  (define-struct block (color size tl tr rt rb br bl lb lt) #:transparent)

  ;; "key" colors are in this table
  (define color-table
    (make-hash (list
                (cons #xffc0c0 (col 0 0)) (cons #xff0000 (col 0 1)) (cons #xc00000 (col 0 2))
                (cons #xffffc0 (col 1 0)) (cons #xffff00 (col 1 1)) (cons #xc0c000 (col 1 2))
                (cons #xc0ffc0 (col 2 0)) (cons #x00ff00 (col 2 1)) (cons #x00c000 (col 2 2))
                (cons #xc0ffff (col 3 0)) (cons #x00ffff (col 3 1)) (cons #x00c0c0 (col 3 2))
                (cons #xc0c0ff (col 4 0)) (cons #x0000ff (col 4 1)) (cons #x0000c0 (col 4 2))
                (cons #xffc0ff (col 5 0)) (cons #xff00ff (col 5 1)) (cons #xc000c0 (col 5 2)))))

  ;; coordinate<->idx helper
  (define (xy->idx x y width height)
    (+ x (* y width)))

  (define (idx->xy idx width height)
    (let ([x (modulo idx width)])
      (values x (/ (- idx x) width))))

  ;; image helper function
  ;; turn a image into hash table
  (define (image->hash img)
    (for/hash ([i (in-range (* (image-width img) (image-height img)))]
               [color (image->color-list img)])
      (values i color)))

  (define (hash->image ht width height)
    (color-list->bitmap (for/list ([i (in-range (* width height))])
                          (hash-ref ht i 0))
                        width
                        height))

  ;; rgba to hex
  (define (col->value c)
    (+ (color-blue c)
       (arithmetic-shift (color-green c) 8)
       (arithmetic-shift (color-red c) 16)))
  ;;  #xffc0c0 to (color 255 192 192 255)

  ;; give image hash-table x y width height default
  ;; return the value of pixel at x y
  ;; return default if x y out of boundary
  ;; default usually is black
  (define (2d-hash-ref ht x y width height default)
    (if (or (< x 0) (< y 0) (>= x width) (>= y height))
        default
        (hash-ref ht (xy->idx x y width height) default)))

  ;; calculate the block we're in given some coordinate in an image
  ;; left/right neighboring codals should be as far left/right as possible
  ;; up/down neighboring codals should be as far up/down as possible
  (define (get-block ht x y width height)
    (let ([c (col->value (2d-hash-ref ht x y width height (make-color 0 0 0)))]
          [sz 0] [visited (make-hash)]
          [tlx x] [tly y]
          [trx x] [try y]
          [brx x] [bry y]
          [blx x] [bly y]
          [rtx x] [rty y]
          [rbx x] [rby y]
          [lbx x] [lby y]
          [ltx x] [lty y])
      (begin
        (let loop ([x^ x]
                   [y^ y])
          (begin
            ;; typical search with DFS
            (if (or (< x^ 0) (< y^ 0) (>= x^ width) (>= y^ height))
                #f
                (let ([idx (xy->idx x^ y^ width height)])
                  (if (eqv? (hash-ref visited idx #f) #t)
                      #f
                      (and
                       (eqv? c (col->value (2d-hash-ref ht x^ y^ width height #x000000)))
                       (begin
                         (hash-set! visited idx #t)
                         (set! sz (add1 sz))
                         ;; calculate top neighbors
                         (and (< y^ tly) (set! tlx x^) (set! tly y^))
                         (and (eqv? y^ tly) (< x^ tlx) (set! tlx x^))
                         (and (< y^ try) (set! trx x^) (set! try y^))
                         (and (eqv? y^ try) (> x^ trx) (set! trx x^))

                         ;; right
                         (and (> x^ rtx) (set! rtx x^) (set! rty y^))
                         (and (eqv? x^ rtx) (< y^ rty) (set! rty y^))
                         (and (> x^ rbx) (set! rbx x^) (set! rby y^))
                         (and (eqv? x^ rbx) (> y^ rby) (set! rby y^))

                         ;; bottom
                         (and (> y^ bry) (set! brx x^) (set! bry y^))
                         (and (eqv? y^ bry) (> x^ brx) (set! brx x^))
                         (and (> y^ bly) (set! blx x^) (set! bly y^))
                         (and (eqv? y^ bly) (< x^ blx) (set! blx x^))

                         ;; left
                         (and (< x^ lbx) (set! lbx x^) (set! lby y^))
                         (and (eqv? x^ lbx) (> y^ lby) (set! lby y^))
                         (and (< x^ ltx) (set! ltx x^) (set! lty y^))
                         (and (eqv? x^ ltx) (< y^ lty) (set! lty y^))

                         (loop (sub1 x^) y^)
                         (loop (add1 x^) y^)
                         (loop x^ (sub1 y^))
                         (loop x^ (add1 y^)))))))))
        ;; calculate neighbors given top-left,
        ;; top-right, right-top, right-bottom,
        ;; bottom-right, bottom-left, left-bottom,
        ;; left-top codals of this block
        (make-block c sz
                    (cons tlx (sub1 tly))
                    (cons trx (sub1 try))
                    (cons (add1 rtx) rty)
                    (cons (add1 rbx) rby)
                    (cons brx (add1 bry))
                    (cons blx (add1 bly))
                    (cons (sub1 lbx) lby)
                    (cons (sub1 ltx) lty)))))


  ;; determine which neighbor from a block
  ;; should be chosen given dp + cc
  (define (dp+cc->block-func dp cc)
    (match (list (modulo dp 4) (modulo cc 2))
      ['(0 0) block-rt]
      ['(1 0) block-br]
      ['(2 0) block-lb]
      ['(3 0) block-tl]
      ['(0 1) block-rb]
      ['(1 1) block-bl]
      ['(2 1) block-lt]
      ['(3 1) block-tr]))

  ;; for displaying a color
  ;; (debugging)
  (define (color->bitmap col)
    (let ([c (make-color
              (color-red col)
              (color-green col)
              (color-blue col))])
      (color-list->bitmap (list c) 1 1)))

  ;; calculate diff between two hue
  (define (hue-sub a b)
    (cond
      [(>= a b) (- a b)]
      [else (+ a (- 6 b))]))

  ;; calculate diff between two hue
  (define (light-sub a b)
    (cond
      [(>= a b) (- a b)]
      [else (+ a (- 3 b))]))

  ;; change x based on DP
  (define (apply-dp-x dp x)
    (match (modulo dp 4)
      ['0 (add1 x)]
      ['1 x]
      ['2 (sub1 x)]
      ['3 x]))

  ;; change y based on DP
  (define (apply-dp-y dp y)
    (match (modulo dp 4)
      ['0 y]
      ['1 (add1 y)]
      ['2 y]
      ['3 (sub1 y)]))

  ;; takes the first depth elements
  ;; of the stack and places them into
  ;; a new list L. Drop depth elements
  ;; from the original list and place that
  ;; into a new list K

  ;; then moves the first num elements
  ;; of L to the end
  ;; (when num is negative, moves the
  ;; last num elements of L to the front)

  ;; returns updated L appended with K
  (define (roll stack num depth)
    (let* ([sub (take stack depth)]
           [m (modulo num depth)]
           [idx (if (< m 0) (+ depth m) m)])
      (append
       (append (drop sub idx)
               (take sub idx))
       (drop stack depth))))

  ;; get new codal based on x y
  (define (get-new-codal ht width height x y)
    (col->value (2d-hash-ref ht x y width height (make-color 0 0 0))))

  ;; determine the codal to visit given the current block,
  ;; dp + cc
  (define (search-next-codal ht width height dp cc curr-block)
    (let* ([new-func (dp+cc->block-func dp cc)]
           [new-xy (new-func curr-block)]
           [new-codal (get-new-codal ht width height (car new-xy) (cdr new-xy))])
      (values new-codal new-xy)))

  ;; instruction processing for interpreter
  ;; return (op stack dp cc)
  (define (update-by-instruction new-codal codal curr-block stack dp cc)
    (let
        ([hue-diff (hue-sub (col-hue new-codal) (col-hue codal))]
         [light-diff (light-sub (col-lightness new-codal) (col-lightness codal))])
      (match (list hue-diff light-diff stack)
        [`(0 0 ,_) (values 'no-op stack dp cc)]
        [`(1 0 (,a ,b . ,rest))
         (values '+ (cons (+ b a) rest) dp cc)]
        [`(1 0 ,_)
         (error (format "stack only has ~a elements (2 required) when trying to add" (length stack)))]
        [`(2 0 (,a ,b . ,rest))
         (let ([rem (modulo b a)])
           (values '/ (cons (if (zero? rem) (/ b a) (/ (- b rem) a)) rest) dp cc))]
        [`(2 0 ,_)
         (error (format "stack only has ~a elements (2 required) when trying to multiply" (length stack)))]
        [`(3 0 (,a ,b . ,rest))
         (values '> (cons (if (> b a) 1 0) rest) dp cc)]
        [`(3 0 ,_)
         (error (format "stack only has ~a elements (2 required) when trying to compute greater" (length stack)))]
        [`(4 0 (,a . ,rest))
         (values 'dup (cons a stack) dp cc)]
        [`(4 0 ,_)
         (error (format "stack only has ~a elements (1 required) when trying to duplicate"
                        (length stack)))]
        [`(5 0 ,_)
         (values 'in-char (cons (char->integer (string-ref (format "~a" (read)) 0)) stack) dp cc)]
        [`(0 1 ,_)
         (values 'push (cons (block-size curr-block) stack) dp cc)]
        [`(1 1 (,a ,b . ,rest))
         (values '- (cons (- b a) rest) dp cc)]
        [`(1 1 ,_)
         (error (format "stack only has ~a elements (2 required) when trying to subtract" (length stack)))]
        [`(2 1 (,a ,b . ,rest))
         (values '% (cons (modulo b a) rest) dp cc)]
        [`(2 1 ,_)
         (error (format "stack only has ~a elements (2 required) when trying to mod" (length stack)))]
        [`(3 1 (,a . ,rest))
         (values 'pointer rest (modulo (+ dp a) 4) cc)]
        [`(4 1 (,n ,d . ,rest))
         (when (< d 0)
           (error (format "negative depth not allowed for rolling // (stack: ~a)" stack)))
         (values 'roll (roll rest n d) dp cc)]
        [`(4 1 ,_)
         (error (format "stack only has ~a elements (2 required) when trying to roll" (length stack)))]
        [`(5 1 (,a . ,rest))
         (printf "~a" a)
         (values 'out-num rest dp cc)]
        [`(5 1 ,_)
         (error (format "stack only has ~a elements (1 required) when trying to print num" (length stack)))]
        [`(0 2 (,a . ,rest))
         (values 'pop rest dp cc)]
        [`(0 2 ,_)
         (error (format "stack only has ~a elements (1 required) when trying to pop" (length stack)))]
        [`(1 2 (,a ,b . ,rest))
         (values '* (cons (* b a) rest) dp cc)]
        [`(1 2 ,_)
         (error (format "stack only has ~a elements (2 required) when trying to multiply" (length stack)))]
        [`(2 2 (,a . ,rest))
         (values '! (cons (if (zero? a) 1 0) rest) dp cc)]
        [`(2 2 ,_)
         (error (format "stack only has ~a elements (1 required) when trying to perform not" (length stack)))]
        [`(3 2 (,a . ,rest))
         (values 'switch rest dp (modulo (+ cc a) 2))]
        [`(4 2 ,_)
         (define new-stack (cons
                            (match (read)
                              [`,a #:when (integer? a) a]
                              [`,a (error (format "not an integer: ~a" a))])
                            stack))
         (values 'in-num new-stack dp cc)]
        [`(5 2 (,a . ,rest))
         (printf "~a" (integer->char a))
         (values 'out-char rest dp cc)]
        [`(5 2 ,_)
         (error (format "stack only has ~a elements (1 required) when trying to print char" (length stack)))]
        [`,x (values (string->symbol (format "ignoring command: ~a" x)) stack dp cc)])))

  ;; interpret a program (image)
  (define (run-program prg)
    (let ([ht (image->hash prg)]
          [width (image-width prg)]
          [height (image-height prg)]
          [visited (make-hash)]
          [dp 0]
          [cc 0]
          [stack (list 0)]
          [x 0]
          [y 0]
          ;; for debugging
          [op 'no-op])
      (begin
        (let loop ()
          (let* ([idx (xy->idx x y width height)]
                 [c (col->value (2d-hash-ref ht x y width height (make-color 0 0 0)))])
            (cond
              ;; stop if we hit a black codal
              [(eqv? c #x000000) #f]
              [(hash-ref color-table c #f)
               => (λ (codal)
                    ;; get the current block we're in
                    (let ([curr-block (get-block ht x y width height)]
                          [next #f])
                      ;; determine the next codal we should go to,
                      ;; given the first nonzero block around this one
                      (for ([i (in-range 8)])
                        #:break next
                        (begin
                          (let-values ([(new-codal new-xy) (search-next-codal ht width height dp cc curr-block)])
                            (if (zero? new-codal)
                                (if (even? i)
                                    (set! cc (modulo (add1 cc) 2))
                                    (set! dp (modulo (add1 dp) 4)))
                                (set! next new-xy)))))
                      ;; if there is a next codal to go to, go to it
                      (and next
                           (begin
                             (let ([new-codal (hash-ref color-table (get-new-codal ht width height (car next) (cdr next)) #f)])
                               ;; if the next codal is not white, then...
                               (and new-codal
                                    ;; determine the instruction to evaluate
                                    (let-values ([(new-op new-stack new-dp new-cc) (update-by-instruction new-codal codal curr-block stack dp cc)])
                                      (begin
                                        ;; and evaluate it, updating the
                                        ;; stack, dp, and cc
                                        (set! op new-op)
                                        (set! stack new-stack)
                                        (set! dp new-dp)
                                        (set! cc new-cc)))
                                    (when debugging
                                      (begin
                                        (display "[no-sl] ")
                                        (display (scale 30 (color->bitmap (2d-hash-ref ht x y width height (make-color 0 0 0)))))
                                        (display (scale 30 (color->bitmap (2d-hash-ref ht (car next) (cdr next) width height (make-color 0 0 0)))))
                                        (printf " ~a" op)
                                        (printf " [~a ~a] " dp cc)
                                        (display curr-block)
                                        (printf " ~a\n" stack)))))
                             ;; go to the next codal
                             (set! x (car next))
                             (set! y (cdr next))
                             (loop)))))]
              ;; Sliding
              [else
               (when debugging (displayln (format "Sliding on ~a" c)))
               ;; when sliding leads to an infinite loop,
               ;; the program terminates
               
               ;; so we keep track of where we've been,
               ;; and what direction we were facing
               (define slide-already (hash-ref visited idx (set)))
               (let* ([new-x (apply-dp-x dp x)]
                      [new-y (apply-dp-y dp y)]
                      [new-codal (col->value (2d-hash-ref ht new-x new-y width height (make-color 0 0 0)))])
                 (when debugging
                   (printf "[slide] ~a~a ~a (~a ~a) <~a, ~a> -> <~a, ~a>\n"
                           (scale 30 (color->bitmap (2d-hash-ref ht x y width height (make-color 0 0 0))))
                           (scale 30 (color->bitmap (2d-hash-ref ht new-x new-y width height (make-color 0 0 0))))
                           (2d-hash-ref ht new-x new-y width height (make-color 0 0 0))
                           dp cc x y new-x new-y))
                 (and
                  ;; if we've been here already facing the same direction,
                  ;; terminate the program
                  (not (set-member? slide-already dp))
                  (begin
                    ;; say we've been here
                    (hash-set! visited idx (set-add slide-already dp))
                    (and (hash-ref color-table new-codal #f) (set! visited (make-hash)))
                    ;; when we hit a wall, we need to update the dp
                    ;; think of those sliding/ice puzzles
                    (if (eqv? new-codal #x000000)
                        (set! dp (modulo (add1 dp) 4))
                        (begin
                          (set! x new-x)
                          (set! y new-y)))
                    (loop))))])))
        (void))))

  ;; compute instruction to generate
  ;; during compilation
  (define (compute-possible-instr codal new-codal)
    (if new-codal
        (let ([hue-diff (hue-sub (col-hue new-codal) (col-hue codal))]
              [light-diff (light-sub (col-lightness new-codal) (col-lightness codal))])
          (match (list hue-diff light-diff)
            [`(0 0) 'noop]
            [`(1 0) '+s]
            [`(2 0) '/s]
            [`(3 0) '>s]
            [`(4 0) 'dup]
            [`(5 0) 'in-char]
            [`(0 1) 'push]
            [`(1 1) '-s]
            [`(2 1) '%s]
            [`(3 1) 'pointer]
            [`(4 1) 'rolls]
            [`(5 1) 'out-num]
            [`(0 2) 'pop]
            [`(1 2) '*s]
            [`(2 2) 'nots]
            [`(3 2) 'switch]
            [`(4 2) 'in-num]
            [`(5 2) 'out-char]
            [_ #f]))
        #f))

  ;; compiles a program to an
  ;; ,(? expr? expr)

  ;; where expr? determines if something is an expr
  ;; and an expr is one of:
  ;; (stop)
  ;; (return)
  ;; (set-dp ,dp ,(expr? expr))
  ;; (easy-going-codal ,block ,dp ,cc ,size ,instr ,(? expr? expr))
  ;; (codal ,block (,dp ,cc ,size ,instr ,(? expr? expr)) ...)
  ;; (block-ref ,block)
  (define (program->instr-list prg)
    (let ([ht (image->hash prg)]
          [width (image-width prg)]
          [height (image-height prg)]
          [visited-blocks (make-hash)]
          [visited (make-hash)]
          [stack (cons 0 null)])
      (begin
        ;; similar to the interpreter,
        ;; keep track of where we are in the program
        (let loop ([x 0] [y 0] [dp 0] [cc 0] [last-codal #f])
          (let* ([idx (xy->idx x y width height)]
                 [c (col->value (2d-hash-ref ht x y width height (make-color 0 0 0)))])
            (cond
              ;; stop if we reach black
              [(eqv? c #x000000)
               `(stop)]
              [(hash-ref color-table c #f)
               => (λ (codal)
                    (define curr-block (get-block ht x y width height))
                    (define visited-block (hash-ref visited-blocks curr-block #f))
                    ;; if we've visited this block already,
                    ;; call the code we already generated
                    (if visited-block `(block-ref ,visited-block)
                        (begin
                          (let*
                              ;; the dp and cc are unknown,
                              ;; (their values depend on the actual
                              ;; operations which occur in the program)
                              ;; so we generate what should happen given
                              ;; any dp, cc
                              ([dp 0]
                               [cc 0]
                               [size (block-size curr-block)]
                               [continuation-list null]
                               [block-name (gensym (string->symbol
                                            (format "b~a_~a_" x y)))])
                            (begin
                              (hash-set! visited-blocks curr-block block-name)
                              (for ([i (in-range 8)])
                                (let* ([new-func (dp+cc->block-func dp cc)]
                                       [new-xy (new-func curr-block)]
                                       [color-value (col->value
                                                     (2d-hash-ref ht (car new-xy)
                                                                  (cdr new-xy)
                                                                  width
                                                                  height
                                                                  (make-color 0 0 0)))]
                                       [new-codal (hash-ref
                                                   color-table
                                                   color-value
                                                   #f)]
                                       [possible-instr (compute-possible-instr codal new-codal)]
                                       ;; get subexpressions generated by the rest
                                       ;; of the program
                                       [new-exps (loop (car new-xy)
                                                       (cdr new-xy)
                                                       dp
                                                       cc
                                                       codal)])
                                  (begin
                                    ;; generate expressions for this
                                    ;; dp, cc
                                    (set! continuation-list
                                          (cons `(,dp ,cc ,size ,possible-instr
                                                      ,(if (eqv? color-value 0)
                                                           '(return)
                                                           new-exps))
                                                continuation-list))
                                    (if (even? i)
                                        (set! cc (modulo (add1 cc) 2))
                                        (set! dp (modulo (add1 dp) 4))))))
                              `(codal ,block-name ,continuation-list))))))]
              [else
               (define here-already (hash-ref visited idx (set)))
               (if (set-member? here-already dp)
                   ;; if sliding causes an infinite loop, terminate
                   '(stop)
                   (begin
                     (hash-set! visited idx (set-add here-already dp))
                     (let* ([new-x (apply-dp-x dp x)]
                            [new-y (apply-dp-y dp y)]
                            [new-codal
                             (col->value
                              (2d-hash-ref ht new-x new-y width height
                                           (make-color 0 0 0)))])
                       (if (eqv? new-codal #x000000)
                           (begin
                             (loop x y (modulo (add1 dp) 4) cc #f))
                           (if (hash-ref color-table new-codal #f)
                               (begin
                                 (set! visited (make-hash))
                                 ;; we've maybe explicitly set the dp, cc after
                                 ;; sliding so we also explicitly set them in the
                                 ;; compiled code
                                 `(set-dp ,dp
                                   ,(loop new-x new-y dp cc #f)))
                               (loop new-x new-y dp cc #f))))))]))))))

  (define (var? v)
    (match v
      [`(Var ,x ,exp) #t]
      [_ #f]))
  (define (just? v)
    (match v
      [`(Just ,_) #t]
      [_ #f]))

  ;; returns whether program flow is deterministic, updated stack, dp + cc
  ;; todo optimize pointer and switch operations

  ;; TODO: implement one of two solutions for this:
  ;; 1.) process the program through another function which records
  ;; all possible dp/cc values for a given codal, then just
  ;; generate instructions for the ones that are used
  ;;
  ;; 2.) Keep track of the instructions which cause a switch/pointer
  ;; operation to happen and then if pointer/switch does *not* reference
  ;; that value, this function returns #t for deterministic program flow
  (define (maybe-optimize-instruction instr size dp cc stack)
    (match (list instr stack)
      [`(noop ,_) (values #f #f #t stack dp cc)]
      [`(+s (Just ((Just ,a) (Just ,b) . ,rest))) (values (+ b a) 2 #t `(Just ((Just ,(+ b a)) . ,rest)) dp cc)]
      [`(+s (Just (,-a ,-b . ,rest))) (values #f #f #t `(Just ((Var ,(gensym 'x) (+ ,-a ,-b)) . ,rest)) dp cc)]
      [`(+s ,-stack) (values #f #f #t `(Var ,(gensym 'x) (cons (cons (+ (cadr ,-stack) (car ,-stack)) (cddr ,-stack)))) dp cc)]
      [`(/s (Just ((Just ,a) (Just ,b) . ,rest)))
       #:when (not (zero? a))
       (define rem (modulo b a))
       (define res (if (zero? rem) (/ b a) (/ (- b rem) a)))
       (values res #t 2 `(Just ((Just ,res) . ,rest)) dp cc)]
      [`(/s (Just (,-a ,-b . ,rest)))
       (values #f #f #t `(Just ((Var ,(gensym 'x) (/ ,-a ,-b)) . ,rest)) dp cc)]
      [`(/s ,-stack) (values #f #f #t `(Var ,(gensym 'x) (cons (/ (cadr ,-stack) (car ,-stack)) (cddr ,-stack))) dp cc)]
      [`(>s (Just ((Just ,a) (Just ,b) . ,rest)))
       (define res (if (> b a) 1 0))
       (values res 2 #t `(Just ((Just ,res) . ,rest)) dp cc)]
      [`(>s (Just (,-a ,-b . ,rest))) (values #f #f #t `(Just ((Var ,(gensym 'x) (> ,-a ,-b)) . ,rest)) dp cc)]
      [`(>s ,-stack) (values #f #f #t `(Var ,(gensym 'x) (cons (> (cadr ,-stack) (car ,-stack)) (cddr ,-stack))) dp cc)]
      [`(dup (Just ((Just ,a) . ,rest))) (values a 0 #t `(Just ((Just ,a) (Just ,a) . ,rest)) dp cc)]
      [`(dup (Just (,-a . ,rest))) (values #f #f #t `(Just (,-a ,-a . ,rest)) dp cc)]
      [`(dup ,-stack) (values #f #f #t `(Var ,(gensym 'x) (cons (car ,-stack) (cons (car ,-stack) (cdr ,-stack)))) dp cc)]
      [`(in-char (Just ,stack))
       (values #f #f #t `(Just ((Var ,(gensym 'x) (in-char)) . ,stack)) dp cc)]
      [`(in-char ,-stack) (values #f #f #t `(Var ,(gensym 'x) (cons (in-char) ,-stack)) dp cc)]
      [`(push (Just ,stack)) (values size 0 #t `(Just ((Just ,size) . ,stack)) dp cc)]
      [`(push ,-stack) (values size 0 #t `(Var ,(gensym 'x) (cons ,size ,-stack)) dp cc)]
      [`(-s (Just ((Just ,a) (Just ,b) . ,rest))) (values (- b a) 2 #t `(Just ((Just ,(- b a)) . ,rest)) dp cc)]
      [`(-s (Just (,-a ,-b . ,rest))) (values #f #f #t `(Just ((Var ,(gensym 'x) (- ,-a ,-b)) . ,rest)) dp cc)]
      [`(-s ,-stack) (values #f #f #t `(Var ,(gensym 'x) (cons (cons (- (cadr ,-stack) (car ,-stack)) (cddr ,-stack)))) dp cc)]
      [`(%s (Just ((Just ,a) (Just ,b) . ,rest)))
       #:when (not (zero? a))
       (values (modulo b a) 2 #t `(Just ((Just ,(modulo b a)) . ,rest)) dp cc)]
      [`(%s (Just (,-a ,-b . ,rest))) (values #f #f #t `(Just ((Var ,(gensym 'x) (% ,-a ,-b)) . ,rest)) dp cc)]
      [`(%s ,-stack) (values #f #f #t `(Var ,(gensym 'x) (cons (cons (% (cadr ,-stack) (car ,-stack)) (cddr ,-stack)))) dp cc)]
      [`(pointer (Just ((Just ,a) . ,rest))) (values #f #f #f `(Just ,rest) (modulo (+ dp a) 4) cc)]
      [`(pointer (Just (,-a . ,rest))) (values #f #f #f `(Just ,rest) dp cc)]
      [`(pointer ,-stack) (values #f #f #f `(Var ,(gensym 'x) (cdr ,-stack)) dp cc)]
      [`(rolls (Just ((Just ,n) (Just ,d) . ,rest)))
       #:when (not (zero? d))
       (values #f #f #t `(Just ,(roll rest n d)) dp cc)]
      [`(rolls (Just (,-a ,-b . ,rest))) (values #f #f #t `(Var ,(gensym 'x) (roll ,-a ,-b ,rest)) dp cc)]
      [`(rolls ,-stack) (values #f #f #t `(Var ,(gensym 'x) (roll (car ,-stack) (cadr ,-stack) (cddr ,-stack))) dp cc)]
      [`(out-num (Just (,_ . ,rest))) (values #f #f #t `(Just ,rest) dp cc)]
      [`(out-num ,-stack) (values #f #f #t `(Var ,(gensym 'x) (cdr ,-stack)) dp cc)]
      [`(pop (Just ((Just ,a) . ,rest))) (values #f 1 #t `(Just ,rest) dp cc)]
      [`(pop (Just (,-a . ,rest))) (values #f #f #t `(Just ,rest) dp cc)]
      [`(pop ,-stack) (values #f #f #t `(Var ,(gensym 'x) (cdr ,-stack)) dp cc)]
      [`(*s (Just ((Just ,a) (Just ,b) . ,rest))) (values (* b a) #f #t `(Just ((Just ,(* b a)) . ,rest)) dp cc)]
      [`(*s (Just (,-a ,-b . ,rest))) (values #f #f #t `(Just ((Var ,(gensym 'x) (* ,-a ,-b)) . ,rest)) dp cc)]
      [`(*s ,-stack) (values #f #f #t `(Var ,(gensym 'x) (cons (* (cadr ,-stack) (car ,-stack)) (cddr ,-stack))) dp cc)]
      [`(nots (Just ((Just ,a) . ,rest)))
       (define res (if a 0 1))
       (values res #f #t `(Just ((Just ,res) . ,rest)) dp cc)]
      [`(nots (Just (,-a . ,rest))) (values #f #f #t `(Just ((Just (Var ,(gensym 'x) (not ,-a))) .  ,rest)) dp cc)]
      [`(nots ,-stack) (values #f #f #t `(Var ,(gensym 'x) (cons (not (car ,-stack)) (cdr ,-stack))) dp cc)]
      [`(switch (Just ((Just ,a) . ,rest))) (values #f #f #f `(Just ,rest) dp (modulo (+ cc a) 2))]
      [`(switch (Just (,-a . ,rest))) (values #f #f #f `(Just ,rest) dp cc)]
      [`(switch ,-stack) (values #f #f #f `(Var ,(gensym 'x) (cdr ,-stack)) dp cc)]
      [`(in-num (Just ,stack)) (values #f #f #t `(Just ((Var ,(gensym 'x) (in-num)) . ,stack)) dp cc)]
      [`(in-num ,-stack) (values #f #f #t `(Var ,(gensym 'x) (cons (in-num) ,-stack)) dp cc)]
      [`(out-char (Just (,_ . ,rest))) (values #f #f #t `(Just ,rest) dp cc)]
      [`(out-char ,-stack) (values #f #f #t `(Var ,(gensym 'x) (cdr ,-stack)) dp cc)]
      [_ (values #f #f #f stack dp cc)]))

  ;; program->instr-list, generating only necessary instructions
  ;; when the program flow is deterministic
  (define (optimize-program->instr-list prg)
    (let ([ht (image->hash prg)]
          [width (image-width prg)]
          [height (image-height prg)]
          [visited-blocks (make-hash)]
          [visited-dblocks (make-hash)]
          [visited (make-hash)])
      (begin
        (let loop ([x 0] [y 0] [dp 0] [cc 0]
                   [last-codal #f]
                   ;; maybe-stack, for keeping track of
                   ;; things that will happen on the stack
                   ;; during runtime
                   [stack `(Just ,(cons '(Just 0) null))]
                   ;; whether or not we definitely know how
                   ;; we got to this x, y
                   [deterministic-flow #t])
          (let* ([idx (xy->idx x y width height)]
                 [c (col->value (2d-hash-ref ht x y width height (make-color 0 0 0)))])
            (cond
              [(eqv? c #x000000)
               `(stop)]
              ;; when we know how we got to this x, y,
              ;; then we can just generate a single
              ;; instruction for this codal
              ;; (since this codal doesn't do much work,
              ;; it's an easy-going-codal)
              [(and deterministic-flow (hash-ref color-table c #f))
               => (λ (codal)
                    (define curr-block (get-block ht x y width height))
                    (define visited-block (hash-ref visited-dblocks (list curr-block dp cc) #f))
                    (if visited-block
                        `(block-ref ,visited-block)
                        (begin
                          (let*
                              ([dp dp]
                               [cc cc]
                               [size (block-size curr-block)]
                               [continuation-list null]
                               [block-name (gensym (string->symbol
                                                    (format "b~a_~a_" x y)))]
                               [rest-of-the-program #f]
                               [new-instr #f])
                            (begin
                              (hash-set! visited-dblocks (list curr-block dp cc) block-name)
                              (for ([i (in-range 8)])
                                #:break rest-of-the-program
                                (let* ([new-func (dp+cc->block-func dp cc)]
                                       [new-xy (new-func curr-block)]
                                       [color-value (col->value
                                                     (2d-hash-ref ht (car new-xy)
                                                                  (cdr new-xy)
                                                                  width
                                                                  height
                                                                  (make-color 0 0 0)))]
                                       [new-codal (hash-ref
                                                   color-table
                                                   color-value
                                                   #f)]
                                       [possible-instr (compute-possible-instr codal new-codal)])
                                  (let-values ([(imm-push imm-pop preserves-determinism maybe-stack new-dp new-cc)
                                                (maybe-optimize-instruction possible-instr size dp cc stack)])
                                    (if (not (zero? color-value))
                                        ;; use the first nonzero instruction as the instruction
                                        ;; for this codal
                                        (begin
                                          (set! new-instr possible-instr)
                                          (set! rest-of-the-program
                                                (loop (car new-xy) (cdr new-xy)
                                                      new-dp new-cc codal
                                                      maybe-stack preserves-determinism)))
                                        (if (even? i)
                                            (set! cc (modulo (add1 cc) 2))
                                            (set! dp (modulo (add1 dp) 4)))))))
                              ;; generate easy-going-codal
                              `(easy-going-codal
                                ,block-name ,dp ,cc ,size ,new-instr
                                ,(if rest-of-the-program rest-of-the-program '(stop))))))))]
              ;; the rest is the same as in regular program->instr-list
              [(hash-ref color-table c #f)
               => (λ (codal)
                    (define curr-block (get-block ht x y width height))
                    (define visited-block (hash-ref visited-blocks curr-block #f))
                    (if visited-block `(block-ref ,visited-block)
                        (begin
                          (let*
                              ([dp 0]
                               [cc 0]
                               [size (block-size curr-block)]
                               [continuation-list null]
                               [block-name (gensym (string->symbol
                                            (format "b~a_~a_" x y)))])
                            (begin
                              (hash-set! visited-blocks curr-block block-name)
                              (for ([i (in-range 8)])
                                (let* ([new-func (dp+cc->block-func dp cc)]
                                       [new-xy (new-func curr-block)]
                                       [color-value (col->value
                                                     (2d-hash-ref ht (car new-xy)
                                                                  (cdr new-xy)
                                                                  width
                                                                  height
                                                                  (make-color 0 0 0)))]
                                       [new-codal (hash-ref
                                                   color-table
                                                   color-value
                                                   #f)]
                                       [possible-instr (compute-possible-instr codal new-codal)])
                                  (let-values ([(imm-push imm-pop preserves-determinism maybe-stack new-dp new-cc)
                                                (maybe-optimize-instruction possible-instr size dp cc stack)])
                                    (let ([new-exps (loop (car new-xy) (cdr new-xy)
                                                         new-dp new-cc codal
                                                         maybe-stack preserves-determinism)])
                                      (begin
                                        (when (not (zero? color-value))
                                          (set! continuation-list
                                                (cons `(,dp ,cc ,size ,possible-instr ,new-exps)
                                                      continuation-list)))
                                        (if (even? i)
                                            (set! cc (modulo (add1 cc) 2))
                                            (set! dp (modulo (add1 dp) 4))))))))
                              `(codal ,block-name ,continuation-list))))))]
              [else
               (define here-already (hash-ref visited idx (set)))
               (if (set-member? here-already dp)
                   '(stop)
                   (begin
                     (hash-set! visited idx (set-add here-already dp))
                     (let* ([new-x (apply-dp-x dp x)]
                            [new-y (apply-dp-y dp y)]
                            [new-codal
                             (col->value
                              (2d-hash-ref ht new-x new-y width height
                                           (make-color 0 0 0)))])
                       (if (eqv? new-codal #x000000)
                           (begin
                             (loop x y (modulo (add1 dp) 4) cc #f stack deterministic-flow))
                           (if (hash-ref color-table new-codal #f)
                               (begin
                                 (set! visited (make-hash))
                                 `(set-dp ,dp
                                   ,(loop new-x new-y dp cc #f stack deterministic-flow)))
                               (loop new-x new-y dp cc #f stack deterministic-flow))))))]))))))

  ;; get the list of blocks which
  ;; will actually be referenced
  ;; during runtime
  (define (get-referenced-block-vars l)
    (match l
      [`(stop) (set)]
      [`(return) (set)]
      [`(set-dp ,_ ,more) (get-referenced-block-vars more)]
      [`(codal ,_ ((,_ ,_ ,_ ,_ ,more) ...))
       (foldr set-union (set) (map get-referenced-block-vars more))]
      [`(easy-going-codal ,_ ,_ ,_ ,_ ,_ ,more) (get-referenced-block-vars more)]
      [`(block-ref ,block-name) (set block-name)]))

  ;; run unoptimized compiler
  (define (compile prog)
    ((instr-list->racket #f) (program->instr-list prog)))

  ;; debug unoptimized compiler
  (define (compile/with-debugging prog)
    ((instr-list->racket #t) (program->instr-list prog)))

  ;; predicates for formatting debug info
  (define (returns-value? instr)
    (match instr
      ['out-char #t]
      ['out-num #t]
      [_ #f]))

  (define (prompts-value? instr)
    (match instr
      ['in-char #t]
      ['in-num #t]
      [_ #f]))

  ;; convert an ,(? expr? expr) to racket code
  (define instr-list->racket
    (λ (debugging)
      (λ (l)
        #;(define what-becomes-a-define (get-referenced-block-vars l))
        (define-values (defs exps)
          (let loop ([l l])
            (match l
              ;; some basic aliases (these could become macros)
              [`(stop) (values '() '(void))]
              [`(return) (values '() ''return)]
              [`(set-dp ,dp ,more)
               (define-values (defs exps) (loop more))
               (values defs `(let ([dp ,dp])
                               ,exps))]
              ;; codals become defines
              ;; (although the codals which aren't referenced
              ;; more than once can simply be inlined, we simply
              ;; generate defines for each codal for readability)
              [`(codal ,block-name ((,dps ,ccs ,sizes ,instrs ,more) ...))
               (define match-defs '())
               (define match-exps '())
               (for ([dp dps]
                     [cc ccs]
                     [size sizes]
                     [instr instrs]
                     [subexp more])
                 (let-values
                     ([(defs^ exps^) (loop subexp)])
                   (begin
                     (set! match-defs (append defs^ match-defs))
                     ;; convert list of continuum expressions
                     ;; to a match
                     (let ([continuation
                            `(let-values
                                 ([(dp cc stack) (,instr dp cc ,size stack)])
                               ,exps^)])
                       (set! match-exps
                             (cons
                              `['(,dp ,cc)
                                ,(if instr
                                     (if debugging
                                         ;; when debugging, generate additional things
                                         `(begin
                                            ,(string->symbol
                                              (format "(printf \"~a\" `(~a ,dp ,cc ~a ,stack))"
                                                      "~a" instr size))
                                            ,@(match instr
                                                [(? returns-value?) (list (string->symbol "(printf \" => \")"))]
                                                [(? prompts-value?) (list (string->symbol "(printf \" ? \")"))]
                                                [_ (list)])
                                            ;; for this match case, call this instruction
                                            (let-values
                                                ([(dp cc stack) (,instr dp cc ,size stack)])
                                              (begin
                                                ,(string->symbol "(printf \"\\n\")")
                                                ,exps^)))
                                         continuation)
                                     exps^)]
                              match-exps))))))
               (define defs
                 ;; place the match inside a define
                 (cons `(define (,block-name dp cc stack)
                          (let loop ([dp dp] [cc cc] [i 0])
                            (when (< i 8)
                              (begin
                                ;; return causes the next dp, cc combination to be
                                ;; tried instead
                                (if (eqv?
                                     (match (list dp cc) ,@match-exps)
                                     'return)
                                    (if (even? i)
                                        (loop dp (modulo (add1 cc) 2) (add1 i))
                                        (loop (modulo (add1 dp) 4) cc (add1 i)))
                                    (void))))))
                       match-defs))
               ;; call the definition inside the actual expression generated
               (define exps
                 `(,block-name dp cc stack))
               (values defs exps)]
              [`(block-ref ,block-name) (values '() `(,block-name dp cc stack))])))
        ;; sandwich everything together and
        ;; run the expressions
        (append defs (list
                      `(let ([dp 0]
                             [cc 0]
                             [stack (list 0)])
                         ,exps))))))

  ;; like instr-list->racket, but with optimization
  (define optimize-instr-list->racket
    (λ (debugging)
      (λ (l)
        (define what-becomes-a-define (get-referenced-block-vars l))
        (define-values (defs exps)
          (let loop ([l l])
            (match l
              [`(stop) (values '() '(void))]
              [`(return) (values '() ''return)]
              [`(set-dp ,dp ,more)
               (define-values (defs exps) (loop more))
               (values defs `(let ([dp ,dp])
                               ,exps))]
              [`(easy-going-codal ,name ,dp ,cc ,size #f ,more)
               (define-values (defs exps) (loop more))
               (if (set-member? what-becomes-a-define name)
                   (values (cons `(define (,name dp cc stack) ,exps) defs)
                           `(,name ,dp ,cc stack))
                   (values defs exps))]
              ;; the easy-going-codal form is added
              [`(easy-going-codal ,name ,dp ,cc ,size ,instr ,more)
               ;; we do inline easy-going-codals...
               (define-values (defs exps) (loop more))
               (if (set-member? what-becomes-a-define name)
                   ;; ...unless they are used during loops
                   ;; in that case, generate a function for them
                   (values (cons `(define (,name dp cc stack)
                                    (let-values ([(dp cc stack)
                                                  (,instr dp cc ,size stack)])
                                      ,exps))
                                 defs)
                           `(,name ,dp ,cc stack))
                   (values defs
                           `(let-values
                                ([(dp cc stack)
                                  (,instr ,dp ,cc ,size stack)])
                              ,exps)))]
              [`(codal ,block-name ((,dps ,ccs ,sizes ,instrs ,more) ...))
               (define match-defs '())
               (define match-exps '())
               (for ([dp dps]
                     [cc ccs]
                     [size sizes]
                     [instr instrs]
                     [subexp more])
                 (let-values
                     ([(defs^ exps^) (loop subexp)])
                   (begin
                     (set! match-defs (append defs^ match-defs))
                     (let ([continuation
                            `(let-values
                                 ([(dp cc stack) (,instr dp cc ,size stack)])
                               ,exps^)])
                       (set! match-exps
                             (cons
                              `['(,dp ,cc)
                                ,(if instr
                                     (if debugging
                                         `(begin
                                            ,(string->symbol
                                              (format "(printf \"~a\" `(~a ,dp ,cc ~a ,stack))"
                                                      "~a" instr size))
                                            ,@(match instr
                                                [(? returns-value?) (list (string->symbol "(printf \" => \")"))]
                                                [(? prompts-value?) (list (string->symbol "(printf \" ? \")"))]
                                                [_ (list)])
                                            (let-values
                                                ([(dp cc stack) (,instr ,dp ,cc ,size stack)])
                                              (begin
                                                ,(string->symbol "(printf \"\\n\")")
                                                ,exps^)))
                                         continuation)
                                     exps^)]
                              match-exps))))))
               (define defs
                 (cons `(define (,block-name dp cc stack)
                          (block-loop dp cc stack
                                      (match (list dp cc)
                                        ,@match-exps
                                        [_ 'return]))
                          #;(let loop ([dp dp] [cc cc] [i 0])
                            (when (< i 8)
                              (begin
                                (if (eqv?
                                     (match (list dp cc)
                                       ,@match-exps
                                       [_ 'return])
                                     'return)
                                    (if (even? i)
                                        (loop dp (modulo (add1 cc) 2) (add1 i))
                                        (loop (modulo (add1 dp) 4) cc (add1 i)))
                                    (void))))))
                       match-defs))
               (define exps
                 `(,block-name dp cc stack))
               (values defs exps)]
              [`(block-ref ,block-name) (values '() `(,block-name dp cc stack))])))
        (append defs (list
                      `(let ([dp 0]
                             [cc 0]
                             [stack (list 0)])
                         ,exps))))))

  (define def-table (make-hash))
  (define (init-env) '())
  (define (extend-env env x v) (cons (cons x v) env))
  (define (lookup env x)
    (define pair (assv x env))
    (if pair (cdr pair) (error 'lookup "value for id ~a not found" x)))
  (define (list=? a b)
    (match (list a b)
      [`(,x ,y) #:when (eqv? x y) #t]
      [`(() ()) #t]
      [`((,x . ,xs) (,y . ,ys))
       #:when (list=? x y)
       (list=? xs ys)]
      [_ #f]))
  (define (assv-list v l)
    (match l
      ['() #f]
      [`((,x . ,val) . ,more)
       (if (list=? v x) (cons x val) (assv-list v more))]))

  (define (constant? e)
    (match e
      [(? number?) #t]
      [`(void) #t]
      [`',x #t]
      [`(list ,xs ...)
       #:when (andmap constant? xs)
       #t]
      [_ #f]))

  (define (constant->value c)
    (match c
      [(? number?) c]
      [`(void) (void)]
      [`',x x]
      [`(list ,xs ...)
       (foldr cons '() (map constant->value xs))]
      [_ `',c]))

  (define (value->constant v)
    (match v
      [(? number?) v]
      [(? void?) `(void)]
      [`(,xs ...)
       `(list ,@(foldr cons '() (map value->constant xs)))]
      [_ `',v]))

  (define keywords
    (set 'noop '+s '/s '>s 'dup 'push
         '-s '%s 'pointer 'rolls 'pop
         '*s 'nots 'switch))
  (define se-keywords
    (set 'in-char 'out-char 'in-num 'out-num))

  (define (keyword->func kw)
    (match kw
      ['noop noop]
      ['+s +s]
      ['/s /s]
      ['>s >s]
      ['dup dup]
      ['push push]
      ['-s -s]
      ['%s %s]
      ['pointer pointer]
      ['rolls rolls]
      ['pop pop]
      ['*s *s]
      ['nots nots]
      ['switch switch]))

  (define max-depth 5)
  (define (do-restrained-inlining e env g-env)
    (define (recur x) (do-restrained-inlining x env g-env))
    (define (keyword? kw) (set-member? keywords kw))
    (match e
      [(? symbol?) (lookup env e)]
      [(? number?) e]
      [`(void) `(void)]
      [`',x e]
      [`(,(? keyword? op) ,(app recur es) ...)
       #:when (andmap constant? es)
       (define-values (dp cc stack) (apply (keyword->func op)
                                           (map constant->value es)))
       `(values ,(value->constant dp)
                ,(value->constant cc)
                ,(value->constant stack))]
      [`(,op ,es ...)
       #:when (or (set-member? keywords op)
                  (set-member? se-keywords op))
       `(,op ,@(map recur es))]
      [`(begin ,(app recur xs) ...) `(begin ,@xs)]
      [`(printf . ,xs) `(printf ,@xs)]
      [`(list ,(app recur xs) ...) `(list ,@xs)]
      [`(block-loop ,dp ,cc ,stack ,b)
       (if (and (constant? (recur dp)) (constant? (recur cc)))
           (recur b)
           `(block-loop ,(recur dp) ,(recur cc) ,(recur stack) ,(recur b)))]
      [`(match ,(app recur l) ,clauses ...)
       #:when (constant? l)
       (define l^ (constant->value l))
       (define clauses^ (map (λ (xy) (cons (constant->value (car xy)) (cadr xy))) clauses))
       (define l-result (assv-list l^ clauses^))
       (if l-result (recur (cdr l-result)) ''return)]
      [`(match ,(app recur l) ,clauses ...)
       `(match ,l ,@(map (λ (xy) `[,(car xy) ,(recur (cadr xy))]) clauses))]
      [`(let ([,xs ,(app recur vs)] ...) ,b)
       (define non-reducible
         (for/fold ([res '()])
                   ([x xs]
                    [v vs])
           (if (or (symbol? v) (constant? v)) res (cons (cons x v) res))))
       (define constant-fold-env
         (for/fold ([env env])
                   ([x xs]
                    [v vs])
           (if (constant? v) (extend-env env x v) env)))
       (define copy-prop-env
         (for/fold ([env constant-fold-env])
                   ([x xs]
                    [v vs])
           (if (symbol? v) (extend-env env x (lookup env v)) env)))
       (define new-env
         (for/fold ([env copy-prop-env])
                   ([xv non-reducible])
           (extend-env env (car xv) (car xv))))
       (if (empty? non-reducible)
           (do-restrained-inlining b new-env g-env)
           `(let-values ([,(map car non-reducible)
                          (values ,@(map cdr non-reducible))])
              ,(do-restrained-inlining b new-env g-env)))]
      [`(let-values ([,xs ,(app recur vs)]) ,b)
       (match vs
         [`(out-num ,_ ,_ ,_ ,(? constant? stack))
          (define stack- (constant->value stack))
          (define new-b (do-restrained-inlining
                         b
                         (extend-env env 'stack (value->constant (cdr stack-))) g-env))
          (define reduced `(printf "~a" ,(car stack-)))
          (match new-b
            [_ `(begin ,reduced ,new-b)])]
         [`(out-char ,_ ,_ ,_ ,(? constant? stack))
          (define stack- (constant->value stack))
          (define new-b (do-restrained-inlining
                         b
                         (extend-env env 'stack (value->constant (cdr stack-))) g-env))
          (define reduced `(printf "~a" ,(integer->char (car stack-))))
          (match new-b
            [_ `(begin ,reduced ,new-b)])]
         [`(values . ,vs)
          (recur
              (for/fold ([res b])
                        ([x xs] [v vs])
                `(let ([,x ,v]) ,res)))]
         [_
          (define new-env (for/fold ([env env]) ([x xs]) (extend-env env x x)))
          `(let-values ([,xs ,vs]) ,(do-restrained-inlining b new-env g-env))])]
      [`(,rator ,(app recur rands) ...)
       (define depth (hash-ref def-table rator 0))
       #;`(,rator ,@rands)
       (if (> depth max-depth)
           `(,rator ,@rands)
           (begin
             (hash-set! def-table rator (add1 depth))
             (let ([inlined (inline-app rator rands env g-env)])
               (define new-depth (hash-ref def-table rator))
               (when (zero? depth) (hash-set! def-table rator depth))
               (if (>= new-depth max-depth)
                   `(,rator ,@rands)
                   inlined))))]))

  (define (inline-app rator rands env g-env)
    (define def (assv rator g-env))
    (unless def (error 'inline-app "global definition ~a not found" rator))
    (match (cdr def)
      [`(,xs ,b)
       (define new-env (append (map cons xs rands) env))
       (do-restrained-inlining b new-env g-env)]))
  
  (define (do-restrained-inlining-def d env g-env)
    (match d
      [`(define (,name ,xs ...) ,b)
       (define new-env (append (map cons xs xs) env))
       `(define (,name ,@xs) ,b)]))
  
  (define (make-global-env defs)
    (match defs
      [`() (values '() '())]
      [`((define (,name ,xs ...) ,b) ,more ...)
       (define-values (subenv subgenv) (make-global-env more))
       (values (extend-env subenv name name)
               (cons `(,name ,xs ,b) subgenv))]))

  ;; pass 3
  (define (restrained-inlining e)
    (match e
      [`(,defs ... ,e)
       (define-values (env g-env) (make-global-env defs))
       (append
        (map (λ (x) (begin (set! def-table (make-hash))
                           (do-restrained-inlining-def x env g-env)))
             defs)
        (list (begin (set! def-table (make-hash))
                     (do-restrained-inlining e env g-env))))]))

  (define (get-function-calls e defs)
    
    (let ([calls (set)])
      (let ([base-result
             (let recur ([e e])
               (match e
                 [(? symbol?) (set)]
                 [(? number?) (set)]
                 [`(void) (set)]
                 [`',x (set)]
                 [`(,op ,es ...)
                  #:when (or (set-member? keywords op)
                             (set-member? se-keywords op))
                  (foldr set-union (set) (map recur es))]
                 [`(begin ,(app recur xs) ...) (foldr set-union (set) xs)]
                 [`(printf . ,xs) (set)]
                 [`(list ,(app recur xs) ...) (foldr set-union (set) xs)]
                 [`(block-loop ,dp ,cc ,stack ,(app recur b)) b]
                 [`(match ,l ,clauses ...)
                  (foldr (λ (xy almost) (set-union (recur (cadr xy)) almost)) (set) clauses)]
                 [`(let ([,xs ,(app recur vs)] ...) ,(app recur b))
                  (set-union b (foldr set-union (set) vs))]
                 [`(let-values ([,xs ,(app recur vs)]) ,(app recur b))
                  (set-union b vs)]
                 [`(,rator ,(app recur rands) ...)
                  (if (set-member? calls rator) (set)
                      (match (assv rator defs)
                        [`(,name ,xs ,b)
                         (set! calls (set-add calls name))
                         (recur b)]))]))])
        (set-union base-result calls))))
  
  ;; pass 4
  (define (remove-unnecessary-defs e)
    (match e
      [`(,defs ... ,e)
       (define-values (env g-env) (make-global-env defs))
       (define calls (get-function-calls e g-env))
       `(,@(filter
            (λ (d)
              (match d
                [`(define (,name ,xs ...) ,b)
                 (set-member? calls name)]))
            defs)
         ,e)]))

  ;; shrink an image by an influence of 1/codal-size
  (define (with-codal-size size img)
    (let ([img-hash (image->hash img)]
          [width (image-width img)]
          [height (image-height img)]
          [divide-size (λ (v) (if (zero? (modulo v size))
                                  (/ v size)
                                  (add1 (/ (- v (modulo v size)) size))))])
      (color-list->bitmap
       (for*/list ([y height]
                   [x width]
                   #:when (zero? (modulo x size))
                   #:when (zero? (modulo y size)))
         (hash-ref img-hash (xy->idx x y width height)))
       (divide-size width)
       (divide-size height))))

  (define (noop dp cc imm stack)
    (values dp cc stack))

  (define (+s dp cc imm stack)
    (match stack
      [`(,a ,b . ,rest) (values dp cc (cons (+ b a) rest))]))

  (define (/s dp cc imm stack)
    (match stack
      [`(,a ,b . ,rest)
       (define rem (modulo b a))
       (values dp cc
               (cons (if (zero? rem)
                         (/ b a)
                         (/ (- b rem) a))
                     rest))]))

  (define (>s dp cc imm stack)
    (match stack
      [`(,a ,b . ,rest) (values dp cc (cons (if (> b a) 1 0) rest))]))

  (define (dup dp cc imm stack)
    (match stack
      [`(,a . ,rest) (values dp cc (cons a (cons a rest)))]))

  (define (in-char dp cc imm stack)
    (values dp cc (cons
                   (char->integer
                    (string-ref (format "~a" (read)) 0))
                   stack)))

  (define (push dp cc imm stack)
    (values dp cc (cons imm stack)))

  (define (-s dp cc imm stack)
    (match stack
      [`(,a ,b . ,rest) (values dp cc (cons (- b a) rest))]))

  (define (%s dp cc imm stack)
    (match stack
      [`(,a ,b . ,rest) (values dp cc (cons (modulo b a) rest))]))

  (define (pointer dp cc imm stack)
    (match stack
      [`(,a . ,rest) (values (modulo (+ a dp) 4) cc rest)]))

  (define (rolls dp cc imm stack)
    (match stack
      [`(,n ,d . ,rest) (values dp cc (roll rest n d))]))

  (define (out-num dp cc imm stack)
    (match stack
      [`(,a . ,rest)
       (printf "~a" a)
       (values dp cc rest)]))

  (define (pop dp cc imm stack)
    (match stack
      [`(,a . ,rest) (values dp cc rest)]))

  (define (*s dp cc imm stack)
    (match stack
      [`(,a ,b . ,rest) (values dp cc (cons (* b a) rest))]))

  (define (nots dp cc imm stack)
    (match stack
      [`(,a . ,rest) (values dp cc (cons (if (eqv? a 0) 1 0) rest))]))

  (define (switch dp cc imm stack)
    (match stack
      [`(,a . ,rest) (values dp (modulo (+ cc a) 2) rest)]))

  (define (in-num dp cc imm stack)
    (values dp cc (cons
                   (match (read)
                     [`,a #:when (integer? a) a]
                     [`,a (error (format "not an integer: ~a" a))])
                   stack)))

  (define (out-char dp cc imm stack)
    (match stack
      [`(,a . ,rest)
       (printf "~a" (integer->char a))
       (values dp cc rest)])))

(module reader racket
  (require 2htdp/image)
  (require (submod ".." piet))
  
  (define (my-read-syntax a b c d e f)
    (define compiled
      (let loop ([codal-size 11]
                 [interp #f])
        (define x (read-syntax a b))
        (if (eof-object? x) null
            (let ([x-datum (syntax->datum x)])
              (match x-datum
                ;; support running images with multiple codal sizes
                ;; syntax: codal-size 11
                ;; or another valid value instead
                ['codal-size
                 (define size-stx (read-syntax a b))
                 (when (eof-object? size-stx)
                   (raise-syntax-error
                    'read-syntax
                    "expected codal size after operator `codal-size`" #f #f (list x)))
                 (define size (syntax->datum size-stx))
                 (unless (number? size)
                   (raise-syntax-error
                    'read-syntax
                    "expected codal size after operator `codal-size`" #f #f (list x)))
                 (unless (and (integer? size) (> size 0))
                   (raise-syntax-error
                    'read-syntax
                    "codal size must be an integer that is greater than 0"
                    #f #f (list size-stx)))
                 (loop size interp)]
                ;; use interpreter to run the next immediate image
                ['interp (loop codal-size #t)]
                ;; support for images as programs
                [(? image?)
                 #:when interp
                 ;; interpret image
                 (append `((run-program (with-codal-size ,codal-size ,x-datum)))
                         (loop codal-size #f))]
                [(? image?)
                 ;; compile image
                 #;(define compiled-img (compile (with-codal-size codal-size x-datum)))
                 (define compiled-img (remove-unnecessary-defs
                                       (restrained-inlining
                                        ((optimize-instr-list->racket #f)
                                         (optimize-program->instr-list
                                          (with-codal-size codal-size x-datum))))))
                 (append compiled-img (loop codal-size #f))]
                [_ (raise-syntax-error 'read-syntax "value given is not an image" #f #f (list x))])))))
    #`(module whatever racket-piet (#%module-begin #,@compiled)))

  (provide (rename-out [my-read-syntax read-syntax])))

(require (for-syntax syntax/parse))
(define-syntax (block-loop stx)
  (syntax-parse stx #:literals (match)
    [(_ dp- cc- stack (match match-v match-es ...))
     #'(let loop ([dp dp-] [cc cc-] [i 0])
         (when (< i 8)
           (begin (if (eqv?
                       (match (list dp cc)
                         match-es ...)
                       'return)
                      (if (even? i)
                          (loop dp (modulo (add1 cc) 2) (add1 i))
                          (loop (modulo (add1 dp) 4) cc (add1 i)))
                      (void)))))]))
#;
(let loop ([dp dp] [cc cc] [i 0])
                            (when (< i 8)
                              (begin
                                (if (eqv?
                                     (match (list dp cc)
                                       ,@match-exps
                                       [_ 'return])
                                     'return)
                                    (if (even? i)
                                        (loop dp (modulo (add1 cc) 2) (add1 i))
                                        (loop (modulo (add1 dp) 4) cc (add1 i)))
                                    (void)))))
(require 'piet)
;; basic top-interaction support
;; (just use run-program to avoid complications)
;; (those complications being that images can't
;; be extrapolated directly from syntax objects
;; during expansion time)
(define-syntax (ti stx)
  (syntax-parse stx
    [(_ . e)
     #`(#%top-interaction . (run-program (with-codal-size 11 e)))]))

(provide #%datum
         (rename-out [ti #%top-interaction])
         run-program with-codal-size
         block-loop)