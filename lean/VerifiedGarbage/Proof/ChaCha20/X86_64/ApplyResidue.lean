module

public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Spec.ChaCha20.Contract
public import VerifiedGarbage.Impl.ChaCha20.X86_64.Stream
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Lit
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Ssse3.Lit
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.LitSplit
public meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public meta import VerifiedGarbage.Spec.ChaCha20.Contract
public meta import VerifiedGarbage.Impl.ChaCha20.X86_64.Stream
public meta import VerifiedGarbage.Proof.ChaCha20.X86_64.Lit
public meta import VerifiedGarbage.Proof.ChaCha20.X86_64.Ssse3.Lit
public meta import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.LitSplit

-- separate module: the residue analysis of `vg_chacha20_apply` over each implementation of
-- `vg_chacha20_xor`, which `Variant.lean` gives them, without importing the analysis into
-- every ChaCha20 proof

/-!
# The residue analysis of `vg_chacha20_apply` on x86-64

`vg_chacha20_apply` over each implementation of `vg_chacha20_xor`, analysed
for what it may leave of secrets (`X86_64.RScrub.Analysed`), with the 8
bytes of the state that hold the number of bytes of keystream left public
(`applyPubs`), which its contract lets it leak.
-/

@[expose] public section

namespace VG.Proof.ChaCha20.X86_64

open VG.X86_64 VG.Impl.ChaCha20.X86_64

/-- The bytes of keystream left: bytes 128–135 of the state (buffer 0). -/
def applyPubs : List (Nat × Nat × Nat) := [(0, 128, 8)]

def scalarApplyKs : List Nat := keep_for% Spec.ChaCha20.applyApi.sig 24 (Stream.apply Callee.scalar) applyPubs

theorem scalarApply_ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.ChaCha20.applyApi.sig 24 applyPubs) (Stream.apply Callee.scalar)
      h).any (RScrub.resOkB · 24 scalarApplyKs (Impl.Scrub.X86_64.chunks 24)) = true :=
  RScrub.Analysed.ok_of scalarApplyKs (by taint_decide)

/-- The analysis of `vg_chacha20_apply` over `Callee.scalar`. -/
def scalarApply : RScrub.Analysed Spec.ChaCha20.applyApi.sig 24 applyPubs (Stream.apply Callee.scalar) :=
  ⟨scalarApplyKs, scalarApply_ok⟩

def ssse3ApplyKs : List Nat := keep_for% Spec.ChaCha20.applyApi.sig 24 (Stream.apply Callee.ssse3) applyPubs

theorem ssse3Apply_ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.ChaCha20.applyApi.sig 24 applyPubs) (Stream.apply Callee.ssse3)
      h).any (RScrub.resOkB · 24 ssse3ApplyKs (Impl.Scrub.X86_64.chunks 24)) = true :=
  RScrub.Analysed.ok_of ssse3ApplyKs (by taint_decide)

/-- The analysis of `vg_chacha20_apply` over `Callee.ssse3`. -/
def ssse3Apply : RScrub.Analysed Spec.ChaCha20.applyApi.sig 24 applyPubs (Stream.apply Callee.ssse3) :=
  ⟨ssse3ApplyKs, ssse3Apply_ok⟩

def avx2ApplyKs : List Nat := keep_for% Spec.ChaCha20.applyApi.sig 24 (Stream.apply Callee.avx2) applyPubs

theorem avx2Apply_ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.ChaCha20.applyApi.sig 24 applyPubs) (Stream.apply Callee.avx2)
      h).any (RScrub.resOkB · 24 avx2ApplyKs (Impl.Scrub.X86_64.chunks 24)) = true :=
  RScrub.Analysed.ok_of avx2ApplyKs (by taint_decide)

/-- The analysis of `vg_chacha20_apply` over `Callee.avx2`. -/
def avx2Apply : RScrub.Analysed Spec.ChaCha20.applyApi.sig 24 applyPubs (Stream.apply Callee.avx2) :=
  ⟨avx2ApplyKs, avx2Apply_ok⟩

def avx512ApplyKs : List Nat := keep_for% Spec.ChaCha20.applyApi.sig 24 (Stream.apply Callee.avx512) applyPubs

theorem avx512Apply_ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.ChaCha20.applyApi.sig 24 applyPubs) (Stream.apply Callee.avx512)
      h).any (RScrub.resOkB · 24 avx512ApplyKs (Impl.Scrub.X86_64.chunks 24)) = true :=
  RScrub.Analysed.ok_of avx512ApplyKs (by taint_decide)

/-- The analysis of `vg_chacha20_apply` over `Callee.avx512`. -/
def avx512Apply : RScrub.Analysed Spec.ChaCha20.applyApi.sig 24 applyPubs (Stream.apply Callee.avx512) :=
  ⟨avx512ApplyKs, avx512Apply_ok⟩

def avx512vlApplyKs : List Nat := keep_for% Spec.ChaCha20.applyApi.sig 24 (Stream.apply Callee.avx512vl) applyPubs

theorem avx512vlApply_ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.ChaCha20.applyApi.sig 24 applyPubs) (Stream.apply Callee.avx512vl)
      h).any (RScrub.resOkB · 24 avx512vlApplyKs (Impl.Scrub.X86_64.chunks 24)) = true :=
  RScrub.Analysed.ok_of avx512vlApplyKs (by taint_decide)

/-- The analysis of `vg_chacha20_apply` over `Callee.avx512vl`. -/
def avx512vlApply : RScrub.Analysed Spec.ChaCha20.applyApi.sig 24 applyPubs (Stream.apply Callee.avx512vl) :=
  ⟨avx512vlApplyKs, avx512vlApply_ok⟩

end VG.Proof.ChaCha20.X86_64
