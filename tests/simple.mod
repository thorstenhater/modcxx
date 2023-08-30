NEURON {
  SUFFIX simple
  USEION na READ ena WRITE x
}

INITIAL {

}

BREAKPOINT {
     x = 42
}
