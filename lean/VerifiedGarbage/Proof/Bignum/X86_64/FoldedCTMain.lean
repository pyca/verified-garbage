import VerifiedGarbage.Proof.Bignum.X86_64.FoldedCT
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedMain
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT

namespace VG.Proof.Bignum.X86_64.FoldedPublic
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64
open VG.Proof.Bignum.X86_64

def publicData (q : DPub × BitVec 64) : PublicData := ⟨DPub.L q,q.1.N⟩

theorem db_pre {q : DPub × BitVec 64} {s : State} (h : DB q s) : Pre (publicData q) s := by
  obtain ⟨X,x,hc,hf,_⟩ := VG.Proof.Bignum.X86_64.db_pre h
  exact ⟨X,x,hc,⟨hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1⟩,hf.2.2.2.2⟩

theorem exp_fw (M : Mont) {q : DPub × BitVec 64} {s : State} (h : DB q s) :
    WP isa (Folded.exp65537 M.mm) s (DD q) := by
  obtain ⟨X,x,hc,hf,hlt,hx⟩ := db_pre h
  obtain ⟨xb,σ,g,_⟩ := h
  refine WP.mono (exp65537_factor_ok M hc hf.1 hf.2.1 hf.2.2.1 hf.2.2.2 hlt hx rfl)
    fun t ⟨gt,_,ft,kt⟩ => ?_
  exact ⟨xb,σ,g.step (ft.mono (pExpRanges_pdAll _)) kt
    (ft.word_eq (pExpRanges_hdr _ (by decide) (by decide) (by decide) (by decide) (by decide))
      (by unfold sMask sFn; omega)),gt⟩

theorem rest_ct (M : Mont)
    (hfinal : RelCT isa (Two GoodL) (M.mm aY aX aY) (fun _ _ => True)) :
    RelCT isa (Two DRel) (Folded.rest M.mm) (fun _ _ => True) := by
  rw [rest_eq]
  refine RelCT.seqs_append (by simp [pdIn]) (by simp [phases]) (RelCT.seq pdSetup_ct ?_)
  refine RelCT.seqs_append (by simp [phases]) (by simp [outSteps,outStepsArr])
    (RelCT.seq (R := Two DD) ?_ ?_)
  · exact RelCT.seq (pdMm_ct (M := M))
      (two_post (two_map publicData (fun _ _ h => db_pre h) (exp65537_ct M hfinal))
        (fun _ _ h => exp_fw M h))
  · exact two_map (fun q => (⟨DPub.L q,q.1.k,q.1.op⟩ : OPub))
      (fun _ _ h => dd_oPre h) out_ct

end VG.Proof.Bignum.X86_64.FoldedPublic
