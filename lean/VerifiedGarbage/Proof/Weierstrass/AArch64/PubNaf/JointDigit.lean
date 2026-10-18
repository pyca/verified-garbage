module
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Digit
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.PubNaf
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64.PubNaf
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open Spec.Weierstrass
/-- The digit operation also accepts an accumulator involving a second public scalar. -/
structure JointDigitPost (K : WinCfg) (C : Curve) (base : Addr) (size : Nat) (P : Point C) (s₀ s : State)
    (j : Nat) (A : Point C) : Prop where
  st : NSt K C base size P s₀ s
  x19 : s.gpr .x19 = BitVec.ofNat 64 j
  rlt : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s.mem base x K.M.n < C.p
  r : InvJ C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z) A
  cache : CacheOk K C base s

theorem jointDigit_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : NafLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) (hone : K.one < C.p)
    {P : Point C} (hP : onCurve C P = true) {A : Point C} (hA : onCurve C A = true) {s₀ s : State}
    (h : NSt K C base size P s₀ s) (hF : NafFixed K C base s₀ P k) (hc : CacheOk K C base s) {j : Nat}
    (hj : j < 64 * K.M.n + 1) (h19 : s.gpr .x19 = BitVec.ofNat 64 j)
    (Dl : ∀ x ∈ [K.D.x, K.D.y, K.D.z], wordsVal s.mem base x K.M.n < C.p)
    (DJ : InvJ C (tmv C K.M.n base s K.D.x) (tmv C K.M.n base s K.D.y) (tmv C K.M.n base s K.D.z)
      A) :
    WP isa (PubNaf.digit K) s fun t => JointDigitPost K C base size P s₀ t j (Spec.Weierstrass.add A (Naf5.point C P k j)) := by
  have hW := hL.win
  have hn := h.scr.nowrap
  have hb4 := hL.al.bits4
  have hbits := hW.bits
  have hdig := hL.digits
  have h10 : K.M.n < 10 := by have := hL.n6; omega
  obtain ⟨-, a2, -, a4, -, -, -, -⟩ := rcbApart_naf hW
  have sD : ∀ x ∈ [K.D.x, K.D.y, K.D.z], x ∈ winRo K ++ winOther K :=
    fun x hx => List.mem_append_right _ (D_other K x hx)
  have sE : ∀ x ∈ [K.E.x, K.E.y, K.E.z], x ∈ winRo K ++ winOther K :=
    fun x hx => List.mem_append_right _ (E_other K x hx)
  rw [PubNaf.digit]
  apply WP.seq
  refine WP.mono (nafRead_ok h.scr (by omega) (by omega) h19 (h.digits hL hF j hj) .x2)
    fun u ⟨u2, ku⟩ => ?_
  have Su := h.regs hW ku (fun r hr => nafClob_mem (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp))
    (by decide)
  have u19 : u.gpr .x19 = BitVec.ofNat 64 j := (ku.gpr _ (by decide)).trans h19
  have cu := CacheUpTo.ofMem ku.mem hc
  have tu : ∀ x, tmv C K.M.n base u x = tmv C K.M.n base s x := fun x => by
    show toM _ _ _ = toM _ _ _; rw [ku.mem]
  have Dlu : ∀ x ∈ [K.D.x, K.D.y, K.D.z], wordsVal u.mem base x K.M.n < C.p := by rw [ku.mem]; exact Dl
  have DJu : InvJ C (tmv C K.M.n base u K.D.x) (tmv C K.M.n base u K.D.y) (tmv C K.M.n base u K.D.z)
      A := by rw [tu, tu, tu]; exact DJ
  have rol := (Su.ro hW hF).1
  refine WP.ite (decide (Naf5.magnitude k j ≠ 0)) (by
    change some (u.read .x .x2 != 0) = _
    rw [read_x, u2, byteTest, nafMagnitude_byte]) (fun hnz => ?_) (fun hz => ?_)
  · have hm0 : Naf5.magnitude k j ≠ 0 := of_decide_eq_true hnz
    apply WP.seq
    refine WP.mono (signedEntry_ok hL hp Su hF cu hj u19 u2 hm0) fun v Ev => ?_
    have Sv := Ev.st
    have v19 := Ev.x19
    have El := Ev.elt
    have EJ := Ev.e
    -- `D` survives the entry.
    have Dv : ∀ x ∈ [K.D.x, K.D.y, K.D.z], wordsVal v.mem base x K.M.n = wordsVal u.mem base x K.M.n := by
      intro x hx
      have hxD : x ∈ rcbW K.S K.D := by rcases mem3 hx with rfl | rfl | rfl <;> simp [rcbW]
      refine Ev.keep x (winOther_mem (D_other K x hx)) fun hE => ?_
      obtain ⟨-, -, -, hRE, -, -, -, hEn, -, -⟩ := hW.other_ne
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hE
      rcases hE with rfl | rfl | rfl | rfl | rfl
      · exact hEn _ (by simp) (List.mem_cons_of_mem _ hxD)
      · exact hEn _ (by simp) (List.mem_cons_of_mem _ hxD)
      · exact hEn _ (by simp) (List.mem_cons_of_mem _ hxD)
      · exact hRE K.R.y (by simp) (by simp only [List.mem_append]; exact Or.inr hxD)
      · exact hRE K.R.z (by simp) (by simp only [List.mem_append]; exact Or.inr hxD)
    have tv : ∀ x ∈ [K.D.x, K.D.y, K.D.z], tmv C K.M.n base v x = tmv C K.M.n base u x := fun x hx => by
      show toM _ _ _ = toM _ _ _; rw [Dv x hx]
    let V := winRo K ++ [K.D.x, K.D.y, K.D.z, K.E.x, K.E.y, K.E.z, K.R.y, K.R.z]
    have hVs : ∀ x ∈ V, x ∈ winSlots K := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact winRo_slots K x hx
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with h | h | h | h | h | h | h | h <;> subst h <;>
          simp only [winSlots, winRo, winOther, rcbW, List.mem_append, List.mem_cons, true_or, or_true]
    have hVl : ∀ x ∈ V, wordsVal v.mem base x K.M.n < C.p := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact (Sv.ro hW hF).1 x hx
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with h' | h' | h' | h' | h' | h' | h' | h' <;> subst h'
        · rw [Dv _ (by simp)]; exact Dlu _ (by simp)
        · rw [Dv _ (by simp)]; exact Dlu _ (by simp)
        · rw [Dv _ (by simp)]; exact Dlu _ (by simp)
        · exact El _ (by simp)
        · exact El _ (by simp)
        · exact El _ (by simp)
        · exact Ev.rlt _ (by simp)
        · exact Ev.rlt _ (by simp)
    have hRV : ∀ x ∈ rcbR K.S K.D K.E, x ∈ V := by
      intro x hx
      simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with h' | h' | h' | h' | h' | h' | h' | h' <;> subst h' <;> simp [V, winRo]
    have sl := winJ_sl (o := K.R) (p := K.D) (q := K.E) (R_other K) sD sE
    have DJv : InvJ C (tmv C K.M.n base v K.D.x) (tmv C K.M.n base v K.D.y) (tmv C K.M.n base v K.D.z)
        A := by
      rw [tv _ (by simp), tv _ (by simp), tv _ (by simp)]; exact DJu
    refine WP.mono (addCB_ok hW.lay hL.al.al hL.n4 hp hC hM3 a2 sl.1 (hL.al.low sl.2.2)
      (inv_of Sv.scr Sv.mod hVs hVl) hRV (by simp [V]) (by simp [V]) Ev.zz Ev.zzz hone
      hA (Naf5.onCurve_point hC hP k j) DJv EJ) fun t ht => ?_
    obtain ⟨sct, kt, Ut, Mt, rlt, rJ, -, -⟩ := jacPost_frame hW Sv.scr Sv.mod (Or.inl rfl) ht
    exact ⟨Sv.next hW sct (kt.mono clob_nafClob) Ut, (kt.gpr _ (x19_not_clob _)).trans v19, rlt, rJ,
      CacheOk.unch hW hL.cache Ev.cache Ut hn⟩
  · have hm0 : Naf5.magnitude k j = 0 := by simpa only [ne_eq, not_not] using of_decide_eq_false hz
    have he : Spec.Weierstrass.add A (Naf5.point C P k j)=A := by
      unfold Naf5.point
      rw [hm0,Spec.Weierstrass.mul]
      simp only [ite_true]
      cases A <;> split <;> rfl
    -- `R = D`.
    have a4' : RcbApart K.S K.D K.D K.R := by
      obtain ⟨-, a2', -, -, -, -, -, -⟩ := rcbApart_naf hW
      exact ⟨a2'.nodup, fun x hx => a2'.apart x (rcbR_self_mem _ _ _ hx)⟩
    let V := winRo K ++ [K.D.x, K.D.y, K.D.z]
    have hVs : ∀ x ∈ V, x ∈ winSlots K := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact winRo_slots K x hx
      · exact winOther_mem (D_other K x hx)
    have hVl : ∀ x ∈ V, wordsVal u.mem base x K.M.n < C.p := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact rol x hx
      · exact Dlu x hx
    have hRV : ∀ x ∈ rcbR K.S K.D K.D, x ∈ V := by
      intro x hx
      simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with h' | h' | h' | h' | h' | h' | h' | h' <;> subst h' <;> simp [V, winRo]
    have sl := winJ_sl (o := K.R) (p := K.D) (q := K.D) (R_other K) sD sD
    refine WP.mono (copyPointJ_ok hW.lay hL.al.al a4' sl.1 (inv_of Su.scr Su.mod hVs hVl) hRV DJu)
      fun t ht => ?_
    obtain ⟨sct, kt, Ut, Mt, rlt, rJ, -, -⟩ := jacPost_frame hW Su.scr Su.mod (Or.inl rfl) ht
    rw [he]
    exact ⟨Su.next hW sct (kt.mono clob_nafClob) Ut, (kt.gpr _ (x19_not_clob _)).trans u19, rlt, rJ,
      CacheOk.unch hW hL.cache cu Ut hn⟩

end VG.Proof.Weierstrass.AArch64.PubNaf
