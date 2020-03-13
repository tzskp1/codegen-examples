From codegen Require Import codegen.
Require Import BinNat.
Require Import mt.

CodeGen Terminate Monomorphization N.land.
CodeGen Terminate Monomorphization N.lor.
CodeGen Terminate Monomorphization N.lxor.
CodeGen Terminate Monomorphization N.shiftl.
CodeGen Terminate Monomorphization N.shiftr.
CodeGen Terminate Monomorphization N.testbit.
CodeGen Monomorphization initialize_random_state.
CodeGen Monomorphization next_random_state.
Print _initialize_random_state.
Print _generate_state_vector.
Print _next_random_state.

CodeGen GenCFile "mt_generated.c"
        _generate_state_vector
        _initialize_random_state
        _next_random_state.
