module

public import VerifiedGarbage.TCB.Artifact

/-!
# MXCSR-configuration-dependent timing: entering Intel's mitigation

**Trusted** (as every file in `Spec/`). Not a cryptographic algorithm: the
function with which the generated dispatchers run, on x86, the verified code
that uses the instructions Intel lists as affected by MXCSR-configuration-dependent timing
(MCDT), under the mitigation Intel prescribes for them: MXCSR holding
`0x1FBF`, loaded before them and followed by `lfence` (see "MCDT" in
`TCB/X86_64/Isa.lean`).

`0x1FBF` is MXCSR's default control bits (`0x1F80`: every exception masked,
rounding to nearest, neither DAZ nor FTZ) with its six status flags (5:0)
set. The calling convention makes the control bits callee-saved and the
status flags caller-saved (System V AMD64 psABI §3.4.1, "Special
Registers"), and Rust assumes the default control bits; so the function
sets the status flags, keeps the control bits, and needs no partner to undo
it: nothing but a load of MXCSR clears the flags (SDM Vol. 1 §10.2.3.1,
"once set, they remain set until explicitly cleared").

* `vg_mcdt_enter` returns 1 at once if MXCSR holds `0x1FBF`; otherwise it
  sets the six status flags of MXCSR, keeping its control bits, then
  `lfence`, and returns 1 if MXCSR then holds `0x1FBF` (its control bits
  were the default), and 0 if not, when the caller must not run the
  affected code with secret data.

Its contract also makes the mode public (`Abi.withMode`; on x86-64,
MXCSR): its time may depend on whether MXCSR already holds `0x1FBF`, so
that it need not load MXCSR and wait for `lfence` when an earlier call left
it so, as it nearly always has. That MXCSR is public is the caller's
assumption, as PSTATE.DIT's is for `vg_dit_enter`: the verified code loads
it only with `0x1FBF` and values it saved, but the status flags also record
which floating-point exceptions the program's own code raised. So the first
call on a thread may reveal whether that code had raised all six (they stay
set after it, until the program loads MXCSR).

A contract here is one for every target, stated on the arguments, the memory
and the return value (`Sig.contract`), which cannot name MXCSR, a part of
the state of one ISA. So this contract says only what every contract says:
the function takes no argument, writes no memory but its stack, keeps what
the calling convention preserves (on x86-64, MXCSR's control bits), and
takes a time that depends on nothing secret (it has no secret input). What
it does to MXCSR, and what it returns, are proven of its code, as a theorem
of its proofs (`Proof/Mcdt/`), against the same model.
-/

@[expose] public section

namespace VG.Spec.Mcdt

/-- `vg_mcdt_enter() -> u32`. -/
def enterSig : Sig where
  params := []
  ret := some .u32

/-- `vg_mcdt_enter`: no argument, no memory written but its stack, a `u32`
returned, and the mode public. -/
def enterContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  enterSig.contract (A.withMode true) (post := fun _m _m' _r => True) (stack := stack)

/-- `vg_mcdt_enter` on every target that has MXCSR. -/
def enterApi : Api where
  module := "mcdt"
  name := "vg_mcdt_enter"
  sig := enterSig
  contracts := some fun A stack => enterContract A stack
  pubMode := true
  summary := "Unless MXCSR already holds `0x1FBF`, sets its six status flags, keeping its \
    control bits, then runs `lfence`, for Intel's mitigation of MXCSR-configuration-dependent timing, and returns 1 if \
    MXCSR then holds `0x1FBF` (its control bits were the default `0x1F80`) and 0 if not. Writes \
    no memory but its stack. Its time may depend on whether MXCSR already held `0x1FBF`, which \
    is public.\n\n\
    Contract: `VG.Spec.Mcdt.enterContract`, and its effect on MXCSR and its result are \
    `VG.Proof.Mcdt.X86_64.enter_mxcsr` (on x86-64)."
  safety := []

end VG.Spec.Mcdt
