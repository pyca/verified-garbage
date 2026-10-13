module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Verified
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Split.Verified
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
public import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratchWipe

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, x86-64: the instances

Untrusted: everything here is checked by Lean. The instance of
`vg_chacha20_poly1305_seal_gather` for an implementation of
`vg_chacha20_xor` calls the instance of `vg_chacha20_poly1305_seal_split`
for it (`sealSplitFn`), copying as many bytes at a time as its CPUs can
(`width`); its code writes `rsp` only in frames (`sealGather_spSafe`).
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
  name := Spec.ChaCha20Poly1305.sealSplitApi.name ++ v.suffix
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

end VG.Proof.ChaCha20Poly1305.X86_64.Gather
