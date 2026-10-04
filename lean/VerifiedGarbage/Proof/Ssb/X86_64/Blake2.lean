import VerifiedGarbage.Proof.Framework.X86_64.Ssb
import VerifiedGarbage.Proof.Blake2.X86_64.Compress
import VerifiedGarbage.Proof.Blake2.X86_64.Lit

/-!
# Prototype: BLAKE2 compression (x86-64) under speculative store bypass

The compression function keeps the block pointer, the count of blocks and the
offset counter in `scratch` and reloads them (`Impl/Blake2/X86_64.lean`). It
is speculatively constant time for windows of up to 7 instructions
(`compressB_specCT`, `compressS_specCT`); from 8 the analysis fails: the
first block's `copy` reloads the block pointer 8 instructions after `setup`
stored it, so under store bypass it may see what `scratch` held before the
call, and dereference it.

`compressF`, the same code with an `lfence` after `setup` (not emitted, and
not proven correct), is speculatively constant time for a window of 64.
-/

namespace VG.Proof.Ssb.X86_64.Blake2

open VG.X86_64 VG.Proof.Blake2 VG.Proof.Blake2.X86_64 VG.Impl.Blake2.X86_64

theorem compressB_specCT : Ssb.SpecCT 7 (compressX86_64 Spec.Blake2.b).pre (compressX86_64 Spec.Blake2.b).pub
    (compress Spec.Blake2.b) :=
  Ssb.specCT (τ₀ 64) (fun _ _ h₁ h₂ hp => agree₀ (.inl rfl) h₁ h₂ hp) rfl (by taint_decide)

theorem compressS_specCT : Ssb.SpecCT 7 (compressX86_64 Spec.Blake2.s).pre (compressX86_64 Spec.Blake2.s).pub
    (compress Spec.Blake2.s) :=
  Ssb.specCT (τ₀ 32) (fun _ _ h₁ h₂ hp => agree₀ (.inr rfl) h₁ h₂ hp) rfl (by taint_decide)

def compressF {w : Nat} (P : Spec.Blake2.Params w) : Prog X86_64.isa :=
  .seq (.block (save ++ setup ++ [.lfence]))
    (.seq flag (.seq (.ite .e (.block []) (.loop (body P) .ne)) (.block restore)))

theorem compressFB_specCT : Ssb.SpecCT 64 (compressX86_64 Spec.Blake2.b).pre (compressX86_64 Spec.Blake2.b).pub
    (compressF Spec.Blake2.b) :=
  Ssb.specCT (τ₀ 64) (fun _ _ h₁ h₂ hp => agree₀ (.inl rfl) h₁ h₂ hp) rfl (by taint_decide)

end VG.Proof.Ssb.X86_64.Blake2
