module

import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.By
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Split.Verified
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Callee
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Whole.Verified
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratchWipe

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, x86-64: the instances

Untrusted: everything here is checked by Lean. The instance of
`vg_chacha20_poly1305_seal_gather` for an implementation of
`vg_chacha20_xor` copies as many bytes at a time as its CPUs can (`width`).
With the AVX-512 implementations of `vg_poly1305_blocks`, it calls that
implementation's `vg_chacha20_poly1305_seal` (`Whole.sealFn`) for at most
960 bytes of data (1024 without IFMA, `byLim`), and its `vg_chacha20_poly1305_seal_split` (`sealSplitFn`)
for more (`sealGatherBy`). The others always gather every slice and call
`seal` (`sealGatherWhole`): their `seal_split` would copy the first slice
too (`gatherCode`, `gather_verified`). The code writes `rsp` only in frames
(`gather_spSafe`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.X86_64.Gather

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.SealGather

open VG.Proof.ChaCha20.X86_64 VG.Impl.StackScratch.X86_64 in
/-- The instance of `vg_chacha20_poly1305_seal_split` calling the
implementation `v` of `vg_chacha20_xor`, with its working space in a frame
of its own. -/
def sealSplitFn (v : XorImpl) : SealSplitFn where
  name := "vg_chacha20_poly1305_seal_split" ++ v.suffix
  code := withStackArgScratchWipedX 1736 3 42
    (Impl.ChaCha20Poly1305.X86_64.SealSplit.sealSplitFor v.callee v.poly)
  verified := Split.sealSplit_framed v
  sp := SpSafe.of_all (X86_64.withStackArgScratchWipedX_spSafe (Split.sealSplitFor_spSafe v))
  depth := by
    have := Split.sealSplitFor_xdepth v
    simp only [withStackArgScratchWipedX, withStackArgScratch, Code.x86_64Depth, X86_64.Instr.frameBytes,
      Nat.zero_max, Nat.max_zero, Nat.max_le]
    omega

open VG.Proof.ChaCha20.X86_64 in
/-- How many bytes at a time the instance for `v` copies: as many as the
CPUs of the instance of `vg_chacha20_poly1305_seal_split` it calls can. -/
def width (v : XorImpl) : Width := .ofBlocks v.poly

open VG.Proof.ChaCha20.X86_64 in
/-- No instruction of the code, or of the instance it calls, writes `rsp`
but its frames' pushes and pops. -/
theorem sealGather_spSafe (v : XorImpl) :
    (sealGather (width v) (sealSplitFn v).name (sealSplitFn v).code).all
      (fun i => !X86_64.isa.writesSp i) = true := by
  have hc : (sealSplitFn v).code.all (fun i => !X86_64.isa.writesSp i) = true :=
    X86_64.withStackArgScratchWipedX_spSafe (Split.sealSplitFor_spSafe v)
  simp only [sealGather, Code.all, hc, Bool.and_true]
  cases width v <;> decide +kernel

open VG.Proof.ChaCha20.X86_64 in
/-- The code of the instance for `v`. -/
def gatherCode (v : XorImpl) : Prog isa :=
  match v.poly with
  | .avx512 | .ifma => sealGatherBy (byLim v.poly) (width v) (Whole.sealFn v).name (Whole.sealFn v).code (sealSplitFn v).name
      (sealSplitFn v).code
  | _ => sealGatherWhole (width v) (Whole.sealFn v).name (Whole.sealFn v).code

open VG.Proof.ChaCha20.X86_64 in
theorem byLim_cases (v : XorImpl) : byLim v.poly = 961 ∨ byLim v.poly = 1025 := by
  generalize v.poly = b
  cases b <;> decide

open VG.Proof.ChaCha20.X86_64 in
theorem gather_verified (v : XorImpl) :
    Verified X86_64.target (gatherCode v) (Spec.ChaCha20Poly1305.sealGatherContract X86_64.abi 1880) := by
  unfold gatherCode
  split
  all_goals first
    | exact sealGatherBy_verified (byLim_cases v) _ _ _
    | exact sealGatherWhole_verified _ _

open VG.Proof.ChaCha20.X86_64 in
theorem gather_spSafe (v : XorImpl) : (gatherCode v).all (fun i => !X86_64.isa.writesSp i) = true := by
  have hw := Whole.sealGather_spSafe v
  have hs := sealGather_spSafe v
  unfold gatherCode
  split
  all_goals first
    | exact hw
    | (simp only [sealGatherBy, Code.all, Bool.and_eq_true]
       exact ⟨by rcases byLim_cases v with h | h <;> rw [h] <;> decide, hw, hs⟩)

end VG.Proof.ChaCha20Poly1305.X86_64.Gather
