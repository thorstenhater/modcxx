#pragma once

#include <cmath>
#include <arbor/version.hpp>
#include <arbor/mechanism_abi.h>

extern "C" {
  arb_mechanism_type make__simple_type() {
    // Tables
    static arb_field_info* globals = NULL;
    static arb_size_type n_globals = 0;
    static arb_field_info* state_vars = NULL;
    static arb_size_type n_state_vars = 0;
    static arb_field_info* parameters = NULL;
    static arb_size_type n_parameters = 0;
    static arb_ion_info ions[] = {{ "na", false, false, false, false, true, false, false, 0 } };
    static arb_size_type n_ions = 1;

    arb_mechanism_type result;
    result.abi_version=ARB_MECH_ABI_VERSION;
    result.fingerprint="<placeholder>";
    result.name="simple";
    result.kind=arb_mechanism_kind_density;
    result.is_linear=true;
    result.has_post_events=false;
    result.globals=globals;
    result.n_globals=n_globals;
    result.ions=ions;
    result.n_ions=n_ions;
    result.state_vars=state_vars;
    result.n_state_vars=n_state_vars;
    result.parameters=parameters;
    result.n_parameters=n_parameters;
    return result;
  }

  arb_mechanism_interface* make__simple_interface_multicore();
  arb_mechanism_interface* make__simple_interface_gpu();

  #ifndef ARB_GPU_ENABLED
  arb_mechanism_interface* make__simple_interface_gpu() { return nullptr; }
  #endif

  arb_mechanism make__simple() {
    static arb_mechanism result = {};
    result.type  = make__simple_type;
    result.i_cpu = make__simple_interface_multicore;
    result.i_gpu = make__simple_interface_gpu;
    return result;
  }
} // extern C
