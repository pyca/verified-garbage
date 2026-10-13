module

public import VerifiedGarbage.Proof.X25519.X86_64.Base.Verified
public import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.ScalarBase
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCTLit
import VerifiedGarbage.Proof.Ed25519.X86_64.Zmm.Keep
import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Sym
import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.Ed25519.Recode
import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Ops
import VerifiedGarbage.Proof.Ed25519.X86_64.Zmm.Half
import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Block
import VerifiedGarbage.Spec.EcKey.Generic
import VerifiedGarbage.Spec.Ecdsa.Generic

/-!
# Fixed-base X25519 with AVX512_IFMA: `Verified`

`x25519BaseIfma` is `x25519Base adx` with Ed25519's comb with AVX512_IFMA
(`Proof.Ed25519.X86_64.Ifma.combOk`); MXCSR's control bits kept, as the comb
loads MXCSR only between saving it in `r11` and loading it back (`ctlOk`).
-/

@[expose] public section

namespace VG.Proof.X25519.X86_64.Base

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.X25519.X86_64.Base VG.Proof.Ed25519.X86_64

/-- The engine with the comb with AVX512_IFMA. -/
abbrev engineIfma : Prog isa :=
  engineOf Impl.X25519.X86_64.adx (Impl.Ed25519.X86_64.Zmm.combMultiply Impl.X25519.X86_64.adx)

theorem engineIfma_ok [DivstepInv] : UEngineOk engineIfma.inline := engineOf_ok Ifma.combOk Ifma.comb_inline

theorem engineIfma_public (base k T : Addr) :
    RelCT isa (fun x y => BaseEnginePre base k T x ∧ BaseEnginePre base k T y) engineIfma.inline
      (fun _ _ => True) :=
  engineOf_ct Ifma.combOk Ifma.comb_inline base k T

theorem x25519BaseIfma_ok [DivstepInv] (s : State) (hs : baseLocal.pre s) :
    ∃ tr t, Exec isa x25519BaseIfma.inline s tr t ∧ abiPreserved s t ∧ baseLocal.post s t := by
  obtain ⟨tr, t, he, h⟩ := x25519BaseWith_correct _ engineIfma_ok hs
  rw [← scalarBaseWith_inline] at he
  exact ⟨tr, t, he, abiPreserved_of_ctl (by lit_decide) he h.1, h.2⟩

theorem x25519BaseIfma_ct [DivstepInv] : ConstantTime isa baseLocal.pre baseLocal.pub x25519BaseIfma.inline := by
  rw [x25519BaseIfma, scalarBaseWith_inline]
  exact x25519BaseWith_ct _ engineIfma_ok engineIfma_public

theorem x25519BaseIfma_verified [DivstepInv] : Verified X86_64.target x25519BaseIfma
    (Spec.X25519.x25519BaseContract (X86_64.abi.withConsts combConsts) 8) :=
  base_verified_of (by lit_decide) x25519BaseIfma_ok x25519BaseIfma_ct

end VG.Proof.X25519.X86_64.Base
