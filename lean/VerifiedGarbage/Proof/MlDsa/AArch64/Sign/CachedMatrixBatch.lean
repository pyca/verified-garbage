import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedMatrixCall

namespace VG.Proof.MlDsa.AArch64.Sign.CachedMatrix
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call
open VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej
open VG.Proof.MlDsa.Sign

theorem aseeds2_eq {p : Params} {D : Nat} {σ s : State} {e : Nat} (h : AS p D σ e 2 s) {k : Nat} (hk : k<2) :
    seed4 s.mem (pa s (sc oRS4)) k=seedE p σ (e+k) := by
  unfold seed4
  rw [pa_sc_add]
  exact h.done k hk

def twoChk (p : Params) (e : Nat) : Bool :=
  let a := pS (aBase p+e)
  let ws : List (Ptr × Nat) := [(a,2048),(sc (oR4 p),8192)]
  rej2Chk (sgR p) (sgW p) (sc oRS4) a (sc (oR4 p)) && stChk p ws && stChk p [] &&
    keepB (sgR p) (sgW p) ws (sc oRS) 32 && famChk (sgR p) (sgW p) ws (aBase p) (e)

theorem twoBatch_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {σ : State} {e : Nat}
    (hc : twoChk p e = true) {s : State} (h : AS p D σ (e) 2 s) :
    WP isa (.seq (callAt "vg_mldsa_rej_ntt_poly2_sha3" Two.code
      (rej2Args (sc oRS4) (pS (aBase p+e)) (sc (oR4 p)))) (.block and24)) s
      (IA p D σ (e+2)) := by
  simp only [twoChk,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨cr,cst⟩,c0⟩,crs⟩,cfam⟩ := hc
  refine WP.seq (WP.mono (rej2Call_ok hP.s64 h.ia.st.lay cr) fun s1 ⟨hp,h24,hred,hout,hmax⟩ => ?_)
  have S1 := h.ia.st.step hp cst
  refine WP.mono (and24_ok s1) fun t ⟨kt,et⟩ => ?_
  have hpt : PPostB D s1 t [] := postB24 kt _
  have hr : (s1.gpr .x0).setWidth 32 = 1 ∨ (s1.gpr .x0).setWidth 32 = 0 := by
    rcases hout with ⟨h1,_⟩ | ⟨h0,_⟩; exacts [.inl h1,.inr h0]
  have et' : t.gpr .x24 = BitVec.setWidth 64 ((s.gpr .x24).setWidth 32 &&& (s1.gpr .x0).setWidth 32) := by rw [et,h24]
  refine ⟨S1.step hpt c0,by rw [kt.mem,hpt.pa (by decide),h.ia.st.lay.keepBytes hp crs]; exact h.ia.rs,
    ?_,fun ht => ?_,fun ht => ?_⟩
  · rw [et']
    rcases h.ia.r01 with e0 | e0 <;> rcases hr with e1 | e1 <;> rw [e0,e1] <;> decide
  · have hs : s.gpr .x24 = 1 ∧ (s1.gpr .x0).setWidth 32 = 1 := by
      rw [et'] at ht
      rcases h.ia.r01 with e0 | e0 <;> rcases hr with e1 | e1 <;> rw [e0,e1] at ht <;>
        first | exact ⟨e0,e1⟩ | exact absurd ht (by decide)
    obtain ⟨ok,fam⟩ := h.ia.ok hs.1
    have fm := Fam.of_eq kt.mem (hpt.bs _ (by decide)) (Fam.keep h.ia.st.lay hp cfam fam)
    refine ⟨fun e' he' => ?_,fun e' he' => ?_⟩
    · by_cases hlt : e' < e
      · exact ok e' hlt
      · obtain ⟨k,rfl⟩ : ∃ k,e'=e+k := ⟨e'-e,by omega⟩
        rw [← aseeds2_eq h (by omega)]; exact hmax hs.2 k (by omega)
    · by_cases hlt : e' < e
      · exact fm e' hlt
      · obtain ⟨k,rfl⟩ : ∃ k,e'=e+k := ⟨e'-e,by omega⟩
        have hk : k < 2 := by omega
        have hm := hmax hs.2 k hk
        have hv : polyAt s1.mem (poly4 (pa s (pS (aBase p+e))) k) = aVal p σ (e+k) := by
          obtain ⟨_,hb⟩ | ⟨h0,_⟩ := hout
          · have hv := rej_val (.inl ⟨hs.2,hb k hk⟩) hs.2 hm
            rw [aseeds2_eq h hk] at hv
            exact hv
          · rw [hs.2] at h0; cases h0
        show PolyIs t.mem (pa t (pS (aBase p+(e+k)))) (aVal p σ (e+k))
        rw [kt.mem,hpt.pa (by change Reg.x28 ∈ keptRegs; decide),hp.pa (by change Reg.x28 ∈ keptRegs; decide),← Nat.add_assoc,← pa_poly4]
        exact ⟨hred hs.2 k hk,hv⟩
  · rw [et'] at ht
    rcases h.ia.r01 with e0 | e0
    · obtain ⟨e',he',hn⟩ := h.ia.bad e0; exact ⟨e',by omega,hn⟩
    · rcases hr with e1 | e1
      · rw [e0,e1] at ht; exact absurd ht (by decide)
      · rcases hout with ⟨h1,_⟩ | ⟨_,k,hk,hn⟩
        · exact absurd (e1.symm.trans h1) (by decide)
        · exact ⟨e+k,by omega,by rw [← aseeds2_eq h hk]; exact hn⟩

end VG.Proof.MlDsa.AArch64.Sign.CachedMatrix
