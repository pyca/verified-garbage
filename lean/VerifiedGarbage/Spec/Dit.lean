module

public import VerifiedGarbage.TCB.Artifact

/-!
# Data independent timing: entering and leaving it

**Trusted** (as every file in `Spec/`). Not a cryptographic algorithm: the
two functions with which the Rust code runs verified code with data
independent timing on, on a CPU that has it. On AArch64 that is PSTATE.DIT
(FEAT_DIT): Arm guarantees the timing of the data-independent-time
instructions, which the leakage model of every proof assumes, only while it
is 1 (see "PSTATE.DIT" in `TCB/AArch64/Isa.lean`).

* `vg_dit_enter` returns 1 if data independent timing was on, and 0 if it
  was off, and turns it on.
* `vg_dit_clear` turns it off. A caller calls it only if `vg_dit_enter`
  returned 0, so that it leaves the mode as it found it.

A contract here is one for every target, stated on the arguments, the memory
and the return value (`Sig.contract`), which cannot name the mode, a part of
the state of one ISA. So these contracts say only what every contract says:
the functions take no argument, write no memory, keep what the calling
convention preserves, and take a time that depends on nothing secret (they
have no secret input). What each does to the mode is proven of its code, as
a theorem of its proofs (`Proof/Dit/`), against the same model.

`vg_dit_enter`'s contract also makes the mode public (`Abi.withMode`): its time
may depend on whether the mode was on, so that it need not turn on a mode
that already is (writing PSTATE.DIT takes tens of nanoseconds on Apple's
cores). The Rust code turns the mode on for an operation whatever data the
operation is given, so whether it is on depends on nothing secret.
-/

@[expose] public section

namespace VG.Spec.Dit

/-- `vg_dit_enter() -> u32`. -/
def enterSig : Sig where
  params := []
  ret := some .u32

/-- `vg_dit_enter`: no argument, no memory written, a `u32` returned, and
the mode public. -/
def enterContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  enterSig.contract (A.withMode true) (post := fun _m _m' _r => True) (stack := stack)

/-- `vg_dit_enter` on every target that has the mode. -/
def enterApi : Api where
  module := "dit"
  name := "vg_dit_enter"
  sig := enterSig
  contracts := some fun A stack => enterContract A stack
  pubMode := true
  summary := "Turns data independent timing on (on AArch64, PSTATE.DIT), and returns 1 if it \
    was already on and 0 if it was off. Writes no memory. Its time may depend on whether the \
    mode was on, which is public.\n\n\
    Contract: `VG.Spec.Dit.enterContract`, and its effect on the mode is \
    `VG.Proof.Dit.AArch64.enter_dit` (on AArch64)."
  safety := []

/-- `vg_dit_clear()`. -/
def clearSig : Sig where
  params := []

/-- `vg_dit_clear`: no argument, no memory written. -/
def clearContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  clearSig.contract A (post := fun _m _m' _r => True) (stack := stack)

/-- `vg_dit_clear` on every target that has the mode. -/
def clearApi : Api where
  module := "dit"
  name := "vg_dit_clear"
  sig := clearSig
  contracts := some fun A stack => clearContract A stack
  summary := "Turns data independent timing off (on AArch64, PSTATE.DIT). Writes no memory. \
    Call it only after `vg_dit_enter` returned 0, so that the mode is left as it was.\n\n\
    Contract: `VG.Spec.Dit.clearContract`, and its effect on the mode is \
    `VG.Proof.Dit.AArch64.clear_dit` (on AArch64)."
  safety := []

end VG.Spec.Dit
