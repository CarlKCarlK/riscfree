import Riscfree.NormalForm
import Riscfree.StateRun
import Riscfree.RV32.Effects

/-!
# The Sail decoder, simplified once for machine mode

`decodeMachineMode word state` is the `simp` normal form of Sail's
`encdec_backwards word state` for a symbolic word, in a state whose privilege
is machine mode and whose landing pads are disabled. Every decode passes
through the `Zicfilp` check, which reads both. `decodeMachineMode.eq` states
the equality under those two facts.

For a concrete word, `decode_word` rewrites with `decodeMachineMode.eq` and lets
the kernel reduce the result. This decodes the base integer instructions,
`Zicsr`, `Zifencei`, `Zicond`, and the system instructions without any
per-instruction lemma. Instructions enabled by a `misa` bit (the M, A, and B
extensions) still read `misa` here; `decode_word` falls back to `simp` for them.

Building this module takes about 15 minutes, once.
-/

namespace Riscfree.RV32

open LeanRV32D LeanRV32D.Functions

-- The hypotheses are used by the normal-form simp, which the linter cannot see.
set_option linter.unusedVariables false in
set_option maxHeartbeats 0 in
normal_form decodeMachineMode (word : BitVec 32) (state : Machine)
    (privilege : Sail.readReg Register.cur_privilege state = .ok .Machine state)
    (landingPad : get_xLPE .Machine state = .ok false state) :
    encdec_backwards word state
  expanding [encdec_backwards]
  unfolding LeanRV32D
  using [bind_run, pure_run, continueWith_ok, continueWith_error, continueWith_ite,
    continueWith_dite, ite_run, dite_run, Bool.true_and, Bool.false_and, Bool.and_true,
    Bool.and_false, Bool.true_or, Bool.false_or, Bool.or_true, Bool.or_false, Bool.not_true,
    Bool.not_false, Bool.false_eq_true, eq_self_iff_true]

end Riscfree.RV32
