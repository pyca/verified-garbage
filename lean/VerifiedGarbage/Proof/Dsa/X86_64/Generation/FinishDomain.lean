module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedPack
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedValidate
public import VerifiedGarbage.Proof.Dsa.Generation.ParamsEncoding
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.SeedSearch
import VerifiedGarbage.Proof.Framework.Omega

/-! # Packing and final validation implement the last seed-acceptance decision -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

theorem finishDomain_ok (M : Mont) (Sq : MontS)
    {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (a : Spec.Dsa.Params)
    (hp : a.p < 256 ^ p.geo.pLen) (hq : a.q < 256 ^ p.geo.qLen) (hg : a.g < 256 ^ p.geo.pLen)
    (bp : Spec.Rsa.bytesAt s.mem (off p.geo.B VG.Impl.Dsa.Generation.Layout.p) p.geo.pLen = Spec.Dsa.encodeBE p.geo.pLen a.p)
    (bq : Spec.Rsa.bytesAt s.mem (off p.geo.B q) p.geo.qLen = Spec.Dsa.encodeBE p.geo.qLen a.q)
    (bg : Spec.Rsa.bytesAt s.mem (off p.geo.B g) p.geo.pLen = Spec.Dsa.encodeBE p.geo.pLen a.g) :
    WP isa (Impl.Dsa.X86_64.Generation.finishDomain Sq.mm M.mm p.geo.pLen p.geo.qLen) s fun t =>
      GenerationMemory p (upd W 19 (BitVec.ofNat 64 (if Spec.Dsa.parametersValid a then 1 else 3))) t ∧
      Spec.Rsa.bytesAt t.mem (off p.geo.B packed) (2 * p.geo.pLen + p.geo.qLen) = Spec.Dsa.encodeParams p.geo.pLen p.geo.qLen a ∧
      Frame p.changed s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  unfold Impl.Dsa.X86_64.Generation.finishDomain
  refine WP.seq (WP.mono (seedPack_ok h _ _ _ (VG.Proof.Dsa.encodeBE_length _ _)
    (VG.Proof.Dsa.encodeBE_length _ _) (VG.Proof.Dsa.encodeBE_length _ _) bp bq bg)
    fun u ⟨hu, bytes, fu, ru, wu⟩ => ?_)
  have check := VG.Proof.Dsa.Generation.check_encodedParams p.geo.validLengths hp hq hg
  have call := seedValidate_ok M Sq hu (Spec.Dsa.encodeParams p.geo.pLen p.geo.qLen a)
    (VG.Proof.Dsa.Generation.encodeParams_length _ _ _) bytes
  rw [check] at call
  simp only [decide_eq_true_eq] at call
  refine WP.mono call fun t ⟨ht, bt, ft, rt, wt⟩ => ?_
  exact ⟨ht, bt, fu.trans ft, rt.trans ru, wt.trans wu⟩

end VG.Proof.Dsa.X86_64.Generation
