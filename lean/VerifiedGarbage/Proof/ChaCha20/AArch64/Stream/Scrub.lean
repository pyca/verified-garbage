module

public import VerifiedGarbage.Spec.ChaCha20.Contract
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.Variants.ChaCha20Xor.AArch64
public import VerifiedGarbage.Impl.ChaCha20.AArch64.Stream
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Stream.ApplyCT
import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.ChaCha20.ScrubLocal

/-!
# ChaCha20's `apply` on AArch64, without secret residue

Its postcondition reads the memory on return only within the state and the
data (`ScrubLocal.applyPost_out`, which RISC-V uses too). It has no frame
(its stack is 0), so the function as emitted (`Impl.ChaCha20.AArch64.Fn.apply`)
returns with every register it may leave secret cleared, over any
implementation of the keystream it calls (`Fn.apply`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20.AArch64.Stream.Scrub

open VG.AArch64 VG.AArch64.ScrubAll VG.Spec.ChaCha20

theorem applyOk (W : Nat) :
    ScrubAllOk (applyContract abi W) W (applySig.retBits abi.ptrBits) :=
  scrubAllOk_any (sig := applySig) (post := ScrubLocal.applyPost 64) (Nat.le_of_ble_eq_true rfl)
    (ScrubLocal.applyPost_out 64 rfl)

/-! ## What the cleanup needs of the code

Of `apply` with any stream `c`, from the same of `apply` with `stub` (its own
instructions) and of `c`'s code. -/

/-- A stream that does nothing: `apply` with it has its own instructions
only. -/
private def stub : Impl.ChaCha20.AArch64.XorCallee :=
  { name := "", code := .block [], suffix := "", clear := ⟨[], [], []⟩ }

private theorem apply_all {p : Instr → Bool} (c : Impl.ChaCha20.AArch64.XorCallee)
    (h0 : sideAll p (Impl.ChaCha20.AArch64.Stream.apply stub) = true) (hc : sideAll p c.code = true) :
    sideAll p (Impl.ChaCha20.AArch64.Stream.apply c) = true := by
  simp only [Impl.ChaCha20.AArch64.Stream.apply, Impl.ChaCha20.AArch64.Stream.part2,
    Impl.ChaCha20.AArch64.XorCallee.inPlace, Impl.ChaCha20.AArch64.XorCallee.callWith, stub, sideAll,
    Bool.and_eq_true] at h0 ⊢
  simp only [h0, hc, and_self]

/-- `apply`'s own instructions write only the registers `Impl/` states
(`Impl.ChaCha20.AArch64.Fn.applyOwn`). -/
private theorem apply_own :
    calleeSide (Impl.ChaCha20.AArch64.Stream.apply stub) Impl.ChaCha20.AArch64.Fn.applyOwn = true := by
  kernel_rfl

private theorem depth_of_noFrames {c : Prog isa} (h : c.noFrames = true) : c.aarch64Depth = 0 := by
  induction c <;> simp_all [Code.noFrames, Code.aarch64Depth]

theorem apply_side (v : Proof.ChaCha20.AArch64.XorImpl) :
    scrubSide (Impl.ChaCha20.AArch64.Stream.apply v.callee) 0 32
      (Impl.ChaCha20.AArch64.Fn.applyOwn.union v.callee.clear) [] = true := by
  refine scrubSide_union0 ?_ (by decide)
    (apply_all v.callee (sideAll_union_left apply_own) (sideAll_union_right v.scrub)) (by decide)
  simp only [Impl.ChaCha20.AArch64.Stream.apply, Impl.ChaCha20.AArch64.Stream.part2,
    Impl.ChaCha20.AArch64.XorCallee.inPlace, Impl.ChaCha20.AArch64.XorCallee.callWith, Code.aarch64Depth,
    depth_of_noFrames v.noFrames]
  decide

end VG.Proof.ChaCha20.AArch64.Stream.Scrub

/-! ## The function

`vg_chacha20_apply` as `Artifacts/ChaCha20/AArch64.lean` registers it, with
the stream `v`: the code that is emitted (`Impl.ChaCha20.AArch64.Fn.apply`)
meets its contract in constant time and returns without secret residue. -/

namespace VG.Proof.ChaCha20.AArch64.Fn

open VG.AArch64 VG.AArch64.ScrubAll VG.Spec.ChaCha20

theorem apply (v : Proof.ChaCha20.AArch64.XorImpl) :
    VerifiedScrubbed target (Impl.ChaCha20.AArch64.Fn.apply v.callee) (applyContract abi 0) 32 :=
  verifiedScrubbed (api := applyApi)
    { code := Impl.ChaCha20.AArch64.Stream.apply v.callee,
      verified := Proof.ChaCha20.AArch64.Stream.apply_verified v }
    _ (Stream.Scrub.applyOk 0) (Stream.Scrub.apply_side v)

end VG.Proof.ChaCha20.AArch64.Fn
