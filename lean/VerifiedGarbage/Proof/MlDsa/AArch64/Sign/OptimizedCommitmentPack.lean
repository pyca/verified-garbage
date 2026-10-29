module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedMasks
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedDot

import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseC
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackCall
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.MlKem.Mem

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Sign/OptimizedCommitment.lean`, which only this module imported.
section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.AArch64.Optimized

structure PositiveICw (p : Params) (S : Nat) (σ : State) (t i : Nat) (s : State) : Prop where
  masks : PositiveICm p S σ t p.ℓ s
  w : Fam s (wBase p) i (Wv p σ (p.ℓ*t))

def positiveRowChk (p : Params) (i : Nat) : Bool :=
  optimizedDotChk p i && positiveIcmChk p (dotWrites p i) p.ℓ &&
    famChk (sgR p) (sgW p) (dotWrites p i) (wBase p) i

theorem positiveRowChk_ok {p : Params} (hp : Ok3 p) : ∀i<p.k,positiveRowChk p i=true := by
  rcases hp with rfl | rfl | rfl <;> decide +kernel

theorem positiveRowW_ok {p : Params} {S : Nat} {σ s : State} {t i : Nat}
    (hp : Ok3 p) (hi : i<p.k) (h : PositiveICw p S σ t i s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.rowW p i) s (PositiveICw p S σ t (i+1)) := by
  have hc := positiveRowChk_ok hp i hi
  simp only [positiveRowChk,Bool.and_eq_true] at hc
  obtain ⟨⟨hd,hm⟩,hw⟩ := hc
  have hA j (hj : j<p.ℓ) : PolyIs s.mem
      (pa s (aP p i 0)+BitVec.ofNat 64 (1024*j)) (Am p σ i j) := by
    have he : p.ℓ*i+j<p.k*p.ℓ := by
      have hl := Nat.mul_le_mul_left p.ℓ (show i+1≤p.k by omega)
      simp only [Nat.mul_add,Nat.mul_one] at hl
      rw [Nat.mul_comm p.k p.ℓ]; omega
    have hv := h.masks.l.k.d.im.A (p.ℓ*i+j) he
    rw [aVal_ij hj] at hv
    change PolyIs s.mem (pa s (pS (aBase p+(p.ℓ*i+j)))) _ at hv
    rw [← Nat.add_assoc,dot_pS_addr] at hv
    simpa only [aP,Nat.add_zero] using hv
  have hB j (hj : j<p.ℓ) : PosPolyIs s.mem
      (pa s (yhP p 0)+BitVec.ofNat 64 (1024*j)) (YHv p σ (p.ℓ*t) j) := by
    have hv := h.masks.yh j hj
    change PosPolyIs s.mem (pa s (pS (yhBase p+j))) _ at hv
    rw [dot_pS_addr] at hv
    simpa only [yhP,Nat.add_zero] using hv
  refine WP.mono_syms (optimizedDot_ok hp hd ⟨h.masks.l.st,h.masks.l.k.d.roots⟩
    (fun j hj => (PosPolyIs.of_canonical (hA j hj)).bound)
    (fun j hj => (hB j hj).bound)) fun u ⟨_,_,hP,hv⟩ hy => ?_
  refine ⟨h.masks.step hP hy hm,(h.w.keep h.masks.l.st.lay hP hw).snoc ?_⟩
  change PolyIs u.mem (pa u (wP p i)) _
  have he : dotNTT
      (fun j => polyAt s.mem (pa s (aP p i 0)+BitVec.ofNat 64 (1024*j)))
      (fun j => polyAt s.mem (pa s (yhP p 0)+BitVec.ofNat 64 (1024*j))) p.ℓ =
      dotNTT (Am p σ i) (YHv p σ (p.ℓ*t)) p.ℓ := by
    unfold dotNTT
    apply congrArg (fun xs : List Poly => xs.foldl add zero)
    apply List.map_congr_left
    intro j hj
    rw [List.mem_range] at hj
    dsimp only
    rw [(hA j hj).2,(hB j hj).value]
  rw [he] at hv
  exact hv

/-- All matrix rows use the fused dot/inverse kernel while preserving the
mask vectors and the secret transforms for the later response checks. -/
theorem positiveRows_ok {p : Params} {S : Nat} {σ s : State} {t : Nat}
    (hp : Ok3 p) (h : PositiveICm p S σ t p.ℓ s) :
    WP isa (VG.Impl.MlDsa.AArch64.Call.seqR
      (Impl.MlDsa.AArch64.Sign.Optimized.rowW p) 0 p.k) s (PositiveICw p S σ t p.k) := by
  simpa only [Nat.zero_add] using seqR_ok (I := fun i s => PositiveICw p S σ t i s) p.k 0
    (fun i _ hi s hs => positiveRowW_ok hp (by omega) hs) s ⟨h,by simp [Fam]⟩

end VG.Proof.MlDsa.AArch64.Sign
end

end

@[expose] public section

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
