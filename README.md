# racket-piet

Base implementation by stevengeeky (https://github.com/stevengeeky) and mofas (https://github.com/mofas)

## Installation

`raco pkg install https://github.com/stevengeeky/racket-piet.git`

## Usage

Make a new `example.rkt` file and in DrRacket type

```scheme
#lang racket-piet

codal-size 11
```

![hello-world.png](https://raw.githubusercontent.com/stevengeeky/racket-piet/master/examples/hello-world.png)

Make sure you include the image in the file, since the image is the program to run.

> If you're going to run the above program, make sure you right-click and save the image first, then insert it into DrRacket by going to Insert->Image. If you copy and paste the image into DrRacket, it will have antialiasing and will not be correctly compiled.
