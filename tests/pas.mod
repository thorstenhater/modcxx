NEURON {
    SUFFIX pas
    NONSPECIFIC_CURRENT i
    RANGE g
    GLOBAL e
}

UNITS {
    (mV) = (millivolt)
    (S) = (siemens)
}

ASSIGNED { gamma}

STATE {
    k
}

PARAMETER {
    v
    g = .001 (S/cm2)  <0,1>
    e = -70  (mV) : Taken from nrn
}

INITIAL {
  LOCAL x
  x = x + 42
  k = x
}

BREAKPOINT {
    i = g*(v - e)
}
