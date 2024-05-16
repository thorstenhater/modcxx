NEURON {
    SUFFIX test
    NONSPECIFIC_CURRENT i
}

STATE { x y }

INITIAL {
  x = 42
  y = 23
}

BREAKPOINT {
    SOLVE dX METHOD cnexp
    SOLVE dY METHOD cnexp

    i = x*y
}

DERIVATIVE dX { x' = -0.1*x }

DERIVATIVE dY { y' = -0.1*y }
