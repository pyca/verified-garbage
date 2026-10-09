import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedCommitment
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseC

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc)
open VG.Spec.Sha3 (bytesAt)

theorem PositiveICw.step {p : Params} {S : Nat} {σ s u : State} {t i : Nat}
    (h : PositiveICw p S σ t i s) {ws : List (Ptr × Nat)}
    (hP : PPostB S s u ws) (hy : u.syms=s.syms) (hc : icwChk p ws i=true)
    (hw : ∀w∈ws,inB (sgW p) w.1 w.2=true) : PositiveICw p S σ t i u := by
  simp only [icwChk,Bool.and_eq_true] at hc
  have hm : positiveIcmChk p ws p.ℓ=true := by
    simp only [positiveIcmChk,Bool.and_eq_true,List.all_eq_true]
    exact ⟨hc.1,hw⟩
  exact ⟨h.masks.step hP hy hm,h.w.keep h.masks.l.st.lay hP hc.2⟩

structure PositiveICh (p : Params) (S : Nat) (σ : State) (t i : Nat) (s : State) : Prop where
  c : PositiveICw p S σ t p.k s
  w1 : bytesAt s.mem (pa s (sc oW1)) (w1Len p*i)=w1Enc p σ (p.ℓ*t) i

theorem packWrite_ok {p : Params} (hp : Ok3 p) : ∀i<p.k,
    inB (sgW p) (sc (oW1+w1Len p*i)) (w1Len p)=true := by
  rcases hp with rfl | rfl | rfl <;> decide

theorem positiveW1R_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : Ok3 p) {σ s : State} {t i : Nat} (hi : i<p.k)
    (hc : hChk p i=true) (h : PositiveICh p S σ t i s) :
    WP isa (w1R P p i) s (PositiveICh p S σ t (i+1)) := by
  simp only [hChk,Bool.and_eq_true,decide_eq_true_eq] at hc
  obtain ⟨⟨⟨cr,ck⟩,ce⟩,hg⟩ := hc
  unfold w1R
  refine WP.mono_syms (highPackAt_ok hP.s64 (hP.highPack p.γ₂ hg) h.c.masks.l.st.lay cr (h.c.w i hi).1)
    fun u ⟨hPu,_,hq⟩ hy => ?_
  have Iu := h.c.step hPu hy ck (by simpa using packWrite_ok hp i hi)
  rw [(h.c.w i hi).2] at hq
  refine ⟨Iu,?_⟩
  have b1 : bytesAt u.mem (pa u (sc oW1)) (w1Len p*i)=w1Enc p σ (p.ℓ*t) i := by
    rw [h.c.masks.l.st.lay.keepBytes hPu ce,h.w1]
  have b2 : bytesAt u.mem (pa u (sc (oW1+w1Len p*i))) (w1Len p)=
      simpleBitPack (VG.Proof.MlDsa.Sign.w1F p (Am p σ) (rppOf p σ) (p.ℓ*t) i) (w1Max p) := by
    rw [hPu.pa (sc_bases _),hq]
    rfl
  rw [Nat.mul_succ,VG.Proof.MlKem.bytesAt_add,pa_sc_add,b1,b2,w1Enc,w1Enc,
    List.range_succ,List.flatMap_append,List.flatMap_singleton]

theorem positivePackRows_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : Ok3 p) {σ s : State} {t : Nat} (h : PositiveICw p S σ t p.k s) :
    WP isa (VG.Impl.MlDsa.AArch64.Call.seqR (w1R P p) 0 p.k) s (PositiveICh p S σ t p.k) := by
  have hc := cChk_ok hp
  simp only [cChk,Bool.and_eq_true,List.all_eq_true,List.mem_range] at hc
  obtain ⟨⟨⟨⟨_,_⟩,hh⟩,_⟩,_⟩ := hc
  simpa only [Nat.zero_add] using seqR_ok (I := fun i s => PositiveICh p S σ t i s) p.k 0
    (fun i _ hi s hs => positiveW1R_ok hP hp (by omega) (hh i (by omega)) hs) s
    ⟨h,by simp [w1Enc]; rfl⟩

end VG.Proof.MlDsa.AArch64.Sign
