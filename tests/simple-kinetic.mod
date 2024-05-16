NEURON {
  SUFFIX simple_kinetic
  NONSPECIFIC_CURRENT il
}

STATE { A B C D }

BREAKPOINT {
  SOLVE foobar METHOD sparse
  il = A + B^0 + C^1 + D*1 + 0
}

INITIAL {
  A = 1
  B = 2
  C = 3
  D = 4
}

KINETIC foobar {
  LOCAL x, y

  x = 23*v
  y = 42^v

  ~ 3 *A + 7 *B <-> B (x, y)
}
