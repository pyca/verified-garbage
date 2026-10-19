module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedGenerator
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.FinishDomain
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedOutcome
import VerifiedGarbage.Proof.Framework.Omega

/-! # Generator selection and final validation produce one complete seed result -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

theorem seedGeneratorFinish_ok (M : Mont)
    {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (value qval : Nat)
    (domain : VG.Proof.Dsa.Generation.PDomain p.geo.pLen value) (qfit : qval < 256 ^ p.geo.qLen)
    (bp : Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.geo.B VG.Impl.Dsa.Generation.Layout.p) p.geo.pLen = Spec.Dsa.encodeBE p.geo.pLen value)
    (be : Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.geo.B exponent) p.geo.pLen = Spec.Dsa.encodeBE p.geo.pLen ((value - 1) / qval))
    (bq : Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.geo.B q) p.geo.qLen = Spec.Dsa.encodeBE p.geo.qLen qval)
    {used : Nat} (h16 : W 16 = BitVec.ofNat 64 used) (hu : used ≤ p.rand.bytes.length) :
    WP isa (.seq (Impl.Dsa.AArch64.Generation.generatorSearch M.mm p.geo.pLen)
      (Impl.Dsa.AArch64.Generation.onSuccess (Impl.Dsa.AArch64.Generation.finishDomain M.mm p.geo.pLen p.geo.qLen))) s
      (SeedFinished p W (VG.Proof.Dsa.Generation.generatorResult value qval
        ((Spec.Dsa.generationChunks p.geo.pLen p.hs.bytes).map Spec.Dsa.decodeBE) (p.rand.bytes.drop used)) s) := by
  have pfit : value < 256 ^ p.geo.pLen := by
    simpa only [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul] using domain.upper
  refine WP.seq (WP.mono (seedGenerator_ok M h value qval domain bp be bq)
    fun u ⟨Wu, mu, slots, bpu, bqu, result, fu, ru, wu⟩ => ?_)
  have u16 : Wu 16 = BitVec.ofNat 64 used := (slots 16 (by simp [generatorSlots])).trans h16
  have uslots : ∀ k ∈ searchSlots, Wu k = W k := fun k hk => slots k (searchSlots_generator hk)
  rcases result with ⟨h19, hr⟩ | ⟨gv, h19, hr, _, upper, bgu⟩
  · apply onSuccess_generation_ok mu
    · intro t _ _ _ hs
      have impossible : (3 : BitVec 64) = 1 := h19.symm.trans hs
      exact False.elim (by cases impossible)
    · intro t mt hm kt _
      refine ⟨Wu, used, mt, hu, u16, uslots, Or.inr (Or.inl ⟨h19, ?_⟩), ?_, kt.rd.trans ru, kt.wr.trans wu⟩
      · simp only [VG.Proof.Dsa.Generation.generatorResult, hr]
      · rw [hm]; exact fu
  · apply onSuccess_generation_ok mu
    · intro v mv hm kv _
      have pv : Spec.Rsa.bytesAt v.mem (VG.Proof.Bignum.off p.geo.B VG.Impl.Dsa.Generation.Layout.p) p.geo.pLen = Spec.Dsa.encodeBE p.geo.pLen value := hm ▸ bpu
      have qv : Spec.Rsa.bytesAt v.mem (VG.Proof.Bignum.off p.geo.B q) p.geo.qLen = Spec.Dsa.encodeBE p.geo.qLen qval := hm ▸ bqu
      have gvbytes : Spec.Rsa.bytesAt v.mem (VG.Proof.Bignum.off p.geo.B g) p.geo.pLen = Spec.Dsa.encodeBE p.geo.pLen gv := hm ▸ bgu
      refine WP.mono (finishDomain_ok M mv ⟨value, qval, gv⟩ pfit qfit (Nat.lt_trans upper pfit) pv qv gvbytes)
        fun t ⟨mt, bytes, ft, rt, wt⟩ => ?_
      refine ⟨_, used, mt, hu, ?_, ?_, ?_, ?_, rt.trans (kv.rd.trans ru), wt.trans (kv.wr.trans wu)⟩
      · simpa [upd] using u16
      · intro k hk
        simpa [upd, searchSlots_not_status hk] using uslots k hk
      · by_cases valid : Spec.Dsa.parametersValid ⟨value, qval, gv⟩
        · refine Or.inr (Or.inr ⟨by simp [upd, valid], ⟨value, qval, gv⟩, ?_, bytes⟩)
          simp only [VG.Proof.Dsa.Generation.generatorResult, hr, valid, ite_true]
        · refine Or.inr (Or.inl ⟨by simp [upd, valid], ?_⟩)
          simp only [VG.Proof.Dsa.Generation.generatorResult, hr, valid, ite_false]
      · exact (show Frame p.changed s.mem v.mem by rw [hm]; exact fu).trans ft
    · intro _ _ _ _ hn
      exact False.elim (hn h19)

end VG.Proof.Dsa.AArch64.Generation
