module

public import VerifiedGarbage.Impl.Weierstrass.AArch64.TCombGeneral
public import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombGeneralSum
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Comb

/-! # General-curve fixed-base comb: loop correctness and frame -/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

/-- An iteration. -/
theorem generalStep_ok {K : TCombCfg} {C : Curve} {base : Addr} {size k : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hA : CombA K.toComb) (hC : Law C)
    (b3 : Nat) (hb : b3 < C.p) (hbm : toM C.p (2 ^ (64 * K.M.n)) b3 = Fin.ofNat C.p (3 * C.b))
    (hG : onCurve C (G C) = true) (hV : TCombVals K C tbl)
    (hpn : C.p < 2 ^ (64 * K.M.n)) {s₀ : State}
    (hF : TCombFixed K C base size s₀ k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl))
    {j : Nat} {s : State} (hj : 1 ≤ j) (hjn : j ≤ K.J)
    (hI : TCombInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s₀ s j) :
    WP isa (K.generalStep b3) s fun s' =>
      TCombInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s₀ s' (j - 1) ∧
        s'.gpr .x19 = BitVec.ofNat 64 (j - 1) := by
  have hn := hI.scr.nowrap
  have hJ := hL.comb.J
  rw [TCombCfg.toComb_J] at hJ
  have hn4 := hL.n8
  have hle : ∀ x, x ∈ combSlots K.toComb → x + 8 * K.M.n ≤ size := fun x hx => hL.comb.lay.le x hx
  have hmoW := combW_mo hL.comb hI.mod
  have hEW := entryW_sub (K := K.toComb)
  dsimp only [TCombCfg.toComb] at hEW
  refine WP.of_syms ?_
  unfold TCombCfg.generalStep
  refine WP.seq ?_
  rw [List.cons_append, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono_syms (decCounter_ok s hj (by omega_using [hjn, hJ]) hI.x19) fun s₁ h₁ sy₁ => ?_
  obtain ⟨b₁, k₁⟩ := h₁
  have hs₁ := hI.scr.of_keeps k₁ (by decide)
  have hm₁ : s₁.mem = s.mem := k₁.mem
  have hM₁ : ModOkA K.M size C.p s₁.mem base := by rw [hm₁]; exact hI.mod
  have hbits₁ : ∀ t < K.w * K.J, s₁.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0 :=
    fun t ht => by rw [hm₁]; exact hI.bits t ht
  have hzW := tcombW_ro hL (x := K.zero) (by simp [combRo, TCombCfg.toComb])
  have hz : wordsVal s₁.mem base K.zero K.M.n = 0 := by
    rw [hm₁, hI.unch.wordsVal hzW (by have := hle K.zero (by tcomb_mem); omega_using [hn, this]), hF.zero]
  have hT : s₁.syms K.tsym = T := by rw [sy₁]; exact hI.tsym
  have hTM : TblMem s₁ T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) :=
    hI.tbl.unch (by rw [k₁.rd, k₁.wr]) fun _ _ _ _ => by rw [hm₁]
  refine tentry_ok (publicLookup := false) hL hA hC hV hpn hs₁ hM₁ (i := j - 1) (by omega_using [hjn, hJ]) b₁ hbits₁ hz hT hTM hF.out
    fun s₃ E₃ => ?_
  have U₁₃ : Unch base (combW K.toComb) s.mem s₃.mem := by
    rw [← hm₁]
    exact E₃.unch.mono fun w hw => hEW w hw
  have U₃ : Unch base (tcombW K) s₀.mem s₃.mem :=
    (hI.unch.trans U₁₃).mono fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · exact hw
      · exact List.mem_append_left _ hw
  have hM₃ : ModOkA K.M size C.p s₃.mem base := hI.mod.unch U₁₃ hmoW hn
  -- What `A` and the read-only slots hold at `s₃`.
  have hnd := hL.comb.nodup
  dsimp only [TCombCfg.toComb] at hnd
  simp only [combWs, rcbW, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hnd
  have hAx : ∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s₃.mem base x K.M.n = wordsVal s.mem base x K.M.n :=
    fun x hx => by
      have hxs : x ∈ combWs K.toComb := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl <;> tcomb_mem
      rw [E₃.unch.wordsVal (fun w hw => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hw with rfl | rfl | rfl | rfl | rfl
        · exact hL.comb.apart₂ hxs (by tcomb_mem) (by rcases hx with rfl | rfl | rfl <;> [exact hnd.1.2.2.1; exact hnd.2.1.2.1; exact hnd.2.2.1.1])
        · exact hL.comb.apart₂ hxs (by tcomb_mem) (by rcases hx with rfl | rfl | rfl <;> [exact hnd.1.2.2.2.1; exact hnd.2.1.2.2.1; exact hnd.2.2.1.2.1])
        · exact hL.comb.apart₂ hxs (by tcomb_mem) (by rcases hx with rfl | rfl | rfl <;> [exact hnd.1.2.2.2.2.1; exact hnd.2.1.2.2.2.1; exact hnd.2.2.1.2.2.1])
        · exact hL.comb.apart₂ hxs (by tcomb_mem) (by rcases hx with rfl | rfl | rfl <;> [exact hnd.1.2.2.2.2.2.1; exact hnd.2.1.2.2.2.2.1; exact hnd.2.2.1.2.2.2.1])
        · exact hL.comb.lay.tmp x (combWs_slots _ x hxs))
        (by have := hle x (combWs_slots _ x hxs); omega_using [hn, this]), hm₁]
  have hro : ∀ x ∈ combRo K.toComb, wordsVal s₃.mem base x K.M.n = wordsVal s₀.mem base x K.M.n :=
    fun x hx => U₃.wordsVal (tcombW_ro hL hx) (by
      have := hle x (combRo_slots x hx); omega_using [hn, this])
  have hlt₃ : ∀ x ∈ rcbR K.toComb.S K.toComb.A K.toComb.E, wordsVal s₃.mem base x K.M.n < C.p := by
    intro x hx
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false, TCombCfg.toComb] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hro _ (by simp [combRo, TCombCfg.toComb])]; exact hF.ro_lt _ (by simp [combRo, TCombCfg.toComb])
    · rw [hro _ (by simp [combRo, TCombCfg.toComb])]; exact hF.ro_lt _ (by simp [combRo, TCombCfg.toComb])
    · rw [hAx _ (by simp)]; exact hI.lt _ (by simp)
    · rw [hAx _ (by simp)]; exact hI.lt _ (by simp)
    · rw [hAx _ (by simp)]; exact hI.lt _ (by simp)
    · exact E₃.lt _ (by simp)
    · exact E₃.lt _ (by simp)
    · exact E₃.lt _ (by simp)
  unfold TCombCfg.generalSum
  refine WP.mono (generalSum_ok hL.comb hA hV.unit hpn hb E₃.scr hM₃ hlt₃) fun s₄ S₄ => ?_
  dsimp only [TCombCfg.toComb] at S₄
  have ta : tmv C K.M.n base s₃ K.S.a = Fin.ofNat C.p C.a := by
    show toM _ _ _ = _; rw [hro _ (by simp [combRo, TCombCfg.toComb])]; exact hF.a
  have hRA : Rep C (tmv C K.M.n base s₃ K.A.x) (tmv C K.M.n base s₃ K.A.y)
      (tmv C K.M.n base s₃ K.A.z) (mul (combEW K.w k K.J j) (G C)) := by
    have ex : tmv C K.M.n base s₃ K.A.x = tmv C K.M.n base s K.A.x := by
      show toM _ _ _ = toM _ _ _; rw [hAx _ (by simp)]
    have ey : tmv C K.M.n base s₃ K.A.y = tmv C K.M.n base s K.A.y := by
      show toM _ _ _ = toM _ _ _; rw [hAx _ (by simp)]
    have ez : tmv C K.M.n base s₃ K.A.z = tmv C K.M.n base s K.A.z := by
      show toM _ _ _ = toM _ _ _; rw [hAx _ (by simp)]
    rw [ex, ey, ez]; exact hI.rep
  have hS := S₄.val
  rw [ta, hbm] at hS
  have hP := hC.onCurve_mul hG (combEW K.w k K.J j)
  have hQ : onCurve C (signedPtW C K.w k (j - 1)) = true := by
    unfold signedPtW combPtW
    split
    · exact hC.onCurve_mul hG _
    · exact onCurve_negPt (hC.onCurve_mul hG _)
  have hR := hC.add hP hQ hRA E₃.rep hS.symm
  have hadd := combW_add hC hG (w := K.w) (k := k) (J := K.J) (j := j - 1) (by omega_using [hjn, hJ])
  rw [Nat.sub_add_cancel hj] at hadd
  have hsp : signedPtW C K.w k (j - 1) = (if 2 ^ (K.w - 1) ≤ combWin K.w k (j - 1) then
      combPtW C K.w (j - 1) (combWin K.w k (j - 1) - 2 ^ (K.w - 1))
      else negPt (combPtW C K.w (j - 1) (2 ^ (K.w - 1) - combWin K.w k (j - 1)))) := rfl
  rw [hsp, hadd] at hR
  have hx₄ : s₄.gpr .x19 = BitVec.ofNat 64 (j - 1) := by
    rw [S₄.keep.gpr _ (x19_not_clob _), E₃.x19, b₁]
  have U₄ : Unch base (combW K.toComb) s.mem s₄.mem := (U₁₃.trans S₄.unch).mono fun w hw => by
    rcases List.mem_append.mp hw with hw | hw <;> exact hw
  intro sy₄
  refine ⟨⟨S₄.scr, hx₄, ?_, (U₃.trans S₄.unch).mono fun w hw => ?_,
    hM₃.unch S₄.unch (combW_mo hL.comb hM₃) hn, S₄.lt, hR, fun t ht => ?_, ?_,
    by rw [sy₄]; exact hI.tsym⟩, hx₄⟩
  · refine (((hI.keep.trans ((Keeps.regs k₁).mono ?_)).trans E₃.keep).trans
      (S₄.keep.mono fun r hr => ?_))
    · intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact combClob_tcombClob _ (by simp [combClob])
    · exact combClob_tcombClob _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_append_right _ hr)))
  · rcases List.mem_append.mp hw with hw | hw
    · exact hw
    · exact List.mem_append_left _ hw
  · have hb := hL.bits
    have hz : K.w * K.J ≤ K.kbytes + 8 * K.zw := by unfold TCombCfg.zw; have := hL.kbytes; omega_using []
    rw [U₄.byte (combW_bits hL ht) (by omega_using [hb, hz, ht, hn])]
    exact hI.bits t ht
  · exact TblMem.of_unch hI.tbl (by rw [S₄.keep.rd, S₄.keep.wr, E₃.keep.rd, E₃.keep.wr, k₁.rd, k₁.wr])
      U₄ (fun w hw => tcombW_size hL hI.mod w (List.mem_append_left _ hw)) hF.out


/-- `[k]G` into `A`, for `k < 2^kbytes` whose bits are the table at `K.bits`;
only `tcombClob` and `tcombW` change. -/
theorem generalComb_ok {K : TCombCfg} {C : Curve} {base : Addr} {size k : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hA : CombA K.toComb) (hC : Law C)
    (b3 : Nat) (hb : b3 < C.p) (hbm : toM C.p (2 ^ (64 * K.M.n)) b3 = Fin.ofNat C.p (3 * C.b))
    (hG : onCurve C (G C) = true) (hV : TCombVals K C tbl)
    (hpn : C.p < 2 ^ (64 * K.M.n)) {s : State} (hs : Scr s base size)
    (hM : ModOkA K.M size C.p s.mem base)
    (hF : TCombFixed K C base size s k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl)) :
    WP isa (K.generalComb b3) s fun s' => KeepRegs (tcombClob K.M.n) s s' ∧ Unch base (tcombW K) s.mem s'.mem ∧
      ModOkA K.M size C.p s'.mem base ∧
      (∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      Rep C (tmv C K.M.n base s' K.A.x) (tmv C K.M.n base s' K.A.y) (tmv C K.M.n base s' K.A.z)
        (mul k (G C)) := by
  have hJ := hL.comb.J
  rw [TCombCfg.toComb_J] at hJ
  have hk : k < 2 ^ (K.w * K.J) :=
    Nat.lt_of_lt_of_le hF.k_lt (Nat.pow_le_pow_right (by decide) hL.kbytes)
  unfold TCombCfg.generalComb
  refine WP.seq (WP.mono (tcomb_init_ok hL hA hV hpn hs hM hF) fun s₆ I₆ => ?_)

  exact countLoop_ok (Inv := fun j s' =>
      TCombInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s s' j) (n := K.J)
    (by omega_using [hJ]) (fun j s' h1 h2 hi => generalStep_ok hL hA hC b3 hb hbm hG hV hpn hF h1 h2 hi)
    (fun s' hi => ⟨hi.keep, hi.unch, hi.mod, hi.lt, by rw [← combEW_zero hk]; exact hi.rep⟩)
    hJ.1 I₆

end VG.Proof.Weierstrass.AArch64
