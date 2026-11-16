module

public import VerifiedGarbage.Impl.Weierstrass.AArch64.TCombGeneral
public import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Comb
import VerifiedGarbage.Proof.Weierstrass.AArch64.Unch
import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
import VerifiedGarbage.Proof.Weierstrass.AArch64.Fprog
import VerifiedGarbage.Proof.Framework.AArch64.Syms

/-! ### `Weierstrass.AArch64.TCombGeneralSum`, which only this module used -/

section

/-! # General-curve addition followed by accumulator copy for the table comb -/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass Spec.Weierstrass

structure GeneralSumPost (K : CombCfg) (C : Curve) (b : Fin C.p) (base : Addr) (size : Nat) (s s' : State) : Prop where
  scr : Scr s' base size
  keep : KeepRegs (clob K.M.n) s s'
  unch : Unch base (combW K) s.mem s'.mem
  lt : ∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s'.mem base x K.M.n < C.p
  val : (tmv C K.M.n base s' K.A.x, tmv C K.M.n base s' K.A.y, tmv C K.M.n base s' K.A.z) =
    VG.Proof.Weierstrass.rcbAdd (tmv C K.M.n base s K.S.a) b
      (tmv C K.M.n base s K.A.x) (tmv C K.M.n base s K.A.y) (tmv C K.M.n base s K.A.z)
      (tmv C K.M.n base s K.E.x) (tmv C K.M.n base s K.E.y) (tmv C K.M.n base s K.E.z)

/-- `A = A + E` by the complete addition into `D`, then copied. -/
theorem generalSumCore_ok {K : CombCfg} {C : Curve} {base : Addr} {size : Nat} (hL : CombLay K size)
    (hA : CombA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {s : State} (hs : Scr s base size)
    (hM : ModOkA K.M size C.p s.mem base)
    (hlt : ∀ x ∈ rcbR { K.S with b3 := K.neg } K.A K.E, wordsVal s.mem base x K.M.n < C.p)
    (hApart : RcbApart { K.S with b3 := K.neg } K.A K.E K.D) :
    WP isa (.seq (fprogB K.M (rcb { K.S with b3 := K.neg } K.A K.E K.D)) (.block (copyPt K.M.n K.A K.D))) s
      (GeneralSumPost K C (tmv C K.M.n base s K.neg) base size s) := by
  have hn := hs.nowrap
  obtain hR : ∀ x ∈ rcbR { K.S with b3 := K.neg } K.A K.E, x ∈ combSlots K := by
    intro x hx
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> comb_mem
  obtain hI : Inv K.M base size C.p (· ∈ combSlots K) (rcbR { K.S with b3 := K.neg } K.A K.E) (tmv C K.M.n base s) s :=
    ⟨hs, hM, hR, hlt, fun _ _ => rfl⟩
  obtain hSl : ∀ x ∈ rcbW { K.S with b3 := K.neg } K.D ++ rcbR { K.S with b3 := K.neg } K.A K.E, x ∈ combSlots K := by
    intro x hx
    simp only [rcbW, rcbR, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> comb_mem
  obtain W := rcb_ok hL.lay hA.al hp hApart hSl (hA.low hSl) hI (fun x hx => hx)
  refine WP.seq (WP.mono W fun s₁ h₁ => ?_)
  obtain ⟨k₁, I₁, v₁, _⟩ := h₁
  have hnd := hL.nodup
  simp only [combWs, rcbW, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hnd
  obtain le : ∀ x ∈ combWs K, x + 8 * K.M.n ≤ size := fun x hx => hL.lay.le x (combWs_slots K x hx)
  obtain al : ∀ x ∈ combWs K, x % 8 = 0 := fun x hx => hA.sl x (combWs_slots K x hx)
  obtain axd := hL.apart₂ (x := K.A.x) (y := K.D.x) (by comb_mem) (by comb_mem) (by nd_find hnd)
  obtain ayd := hL.apart₂ (x := K.A.y) (y := K.D.y) (by comb_mem) (by comb_mem) (by nd_find hnd)
  obtain azd := hL.apart₂ (x := K.A.z) (y := K.D.z) (by comb_mem) (by comb_mem) (by nd_find hnd)
  obtain axy := hL.apart₂ (x := K.A.x) (y := K.A.y) (by comb_mem) (by comb_mem) (by nd_find hnd)
  obtain axz := hL.apart₂ (x := K.A.x) (y := K.A.z) (by comb_mem) (by comb_mem) (by nd_find hnd)
  obtain ayz := hL.apart₂ (x := K.A.y) (y := K.A.z) (by comb_mem) (by comb_mem) (by nd_find hnd)
  obtain dxay := hL.apart₂ (x := K.D.x) (y := K.A.y) (by comb_mem) (by comb_mem) (by nd_find hnd)
  obtain dxaz := hL.apart₂ (x := K.D.x) (y := K.A.z) (by comb_mem) (by comb_mem) (by nd_find hnd)
  obtain dyaz := hL.apart₂ (x := K.D.y) (y := K.A.z) (by comb_mem) (by comb_mem) (by nd_find hnd)
  obtain hs₁ := k₁.scr hs
  rw [copyPt, List.append_assoc, WP.block_append_iff]
  obtain b64 : ∀ x ∈ combWs K, x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by
    have := le x hx; omega_using [this, hn]
  obtain W2 := copy_ok K.M.n hs₁ (le _ (by comb_mem)) (le _ (by comb_mem)) (al _ (by comb_mem))
    (al _ (by comb_mem)) (o := K.A.x) (a := K.D.x) (axd.imp (fun h => by omega_using [h]) id)
  refine WP.mono W2 fun s₂ h₂ => ?_
  obtain ⟨e₂, k₂, O₂⟩ := h₂
  obtain hs₂ := hs₁.of_keepRegs k₂ (by decide)
  rw [WP.block_append_iff]
  obtain W3 := copy_ok K.M.n hs₂ (le _ (by comb_mem)) (le _ (by comb_mem)) (al _ (by comb_mem))
    (al _ (by comb_mem)) (o := K.A.y) (a := K.D.y) (ayd.imp (fun h => by omega_using [h]) id)
  refine WP.mono W3 fun s₃ h₃ => ?_
  obtain ⟨e₃, k₃, O₃⟩ := h₃
  obtain hs₃ := hs₂.of_keepRegs k₃ (by decide)
  obtain W4 := copy_ok K.M.n hs₃ (le _ (by comb_mem)) (le _ (by comb_mem)) (al _ (by comb_mem))
    (al _ (by comb_mem)) (o := K.A.z) (a := K.D.z) (azd.imp (fun h => by omega_using [h]) id)
  refine WP.mono W4 fun s₄ h₄ => ?_
  obtain ⟨e₄, k₄, O₄⟩ := h₄
  obtain dyax := hL.apart₂ (x := K.D.y) (y := K.A.x) (by comb_mem) (by comb_mem) (by nd_find hnd)
  obtain dzax := hL.apart₂ (x := K.D.z) (y := K.A.x) (by comb_mem) (by comb_mem) (by nd_find hnd)
  obtain dzay := hL.apart₂ (x := K.D.z) (y := K.A.y) (by comb_mem) (by comb_mem) (by nd_find hnd)
  obtain hDx : K.D.x ∈ rcbW { K.S with b3 := K.neg } K.D ++ rcbR { K.S with b3 := K.neg } K.A K.E := by simp [rcbW]
  obtain hDy : K.D.y ∈ rcbW { K.S with b3 := K.neg } K.D ++ rcbR { K.S with b3 := K.neg } K.A K.E := by simp [rcbW]
  obtain hDz : K.D.z ∈ rcbW { K.S with b3 := K.neg } K.D ++ rcbR { K.S with b3 := K.neg } K.A K.E := by simp [rcbW]
  obtain bAx := b64 K.A.x (by comb_mem)
  obtain bAy := b64 K.A.y (by comb_mem)
  obtain bAz := b64 K.A.z (by comb_mem)
  obtain bDx := b64 K.D.x (by comb_mem)
  obtain bDy := b64 K.D.y (by comb_mem)
  obtain bDz := b64 K.D.z (by comb_mem)
  obtain wx : wordsVal s₄.mem base K.A.x K.M.n = wordsVal s₁.mem base K.D.x K.M.n := by
    rw [O₄.wordsVal axz bAx, O₃.wordsVal axy bAx, e₂]
  obtain wy : wordsVal s₄.mem base K.A.y K.M.n = wordsVal s₁.mem base K.D.y K.M.n := by
    rw [O₄.wordsVal ayz bAy, e₃, O₂.wordsVal dyax bDy]
  obtain wz : wordsVal s₄.mem base K.A.z K.M.n = wordsVal s₁.mem base K.D.z K.M.n := by
    rw [e₄, O₃.wordsVal dzay bDz, O₂.wordsVal dzax bDz]
  refine ⟨hs₃.of_keepRegs k₄ (by decide), ?_, ?_, ?_, ?_⟩
  · have c1 : ∀ r ∈ [Reg.x1], r ∈ clob K.M.n := by intro r hr; simp at hr; subst hr; simp [clob]
    exact ((⟨k₁.gpr, k₁.rd, k₁.wr, k₁.sp⟩ : KeepRegs (clob K.M.n) s s₁).trans
      ((k₂.mono c1).trans ((k₃.mono c1).trans (k₄.mono c1))))
  · refine (k₁.unch.trans (O₂.unch.trans (O₃.unch.trans O₄.unch))).mono ?_
    intro w hw
    simp only [combW, combWs, rcbW, List.map_append, List.map_cons, List.map_nil, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    grind
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [wx]; exact I₁.lt _ hDx
    · rw [wy]; exact I₁.lt _ hDy
    · rw [wz]; exact I₁.lt _ hDz
  · rw [← v₁]
    show (toM _ _ _, toM _ _ _, toM _ _ _) = _
    rw [wx, wy, wz, I₁.val _ hDx, I₁.val _ hDy, I₁.val _ hDz]


/-- Refresh `3b` in the negation scratch, then add with the general formula. -/
theorem generalSum_ok {K : CombCfg} {C : Curve} {base : Addr} {size b : Nat}
    (hL : CombLay K size) (hA : CombA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n)))
    (hpn : C.p < 2 ^ (64 * K.M.n)) (hb : b < C.p)
    {s : State} (hs : Scr s base size) (hM : ModOkA K.M size C.p s.mem base)
    (hlt : ∀ x ∈ rcbR K.S K.A K.E, wordsVal s.mem base x K.M.n < C.p) :
    WP isa (.seq (.block (setConst K.M.n K.neg b))
      (.seq (fprogB K.M (rcb { K.S with b3 := K.neg } K.A K.E K.D))
        (.block (copyPt K.M.n K.A K.D)))) s
      (GeneralSumPost K C (toM C.p (2 ^ (64 * K.M.n)) b) base size s) := by
  have hn := hs.nowrap
  obtain hnS : K.neg ∈ combSlots K := by comb_mem
  obtain hnW : K.neg ∈ combWs K := by comb_mem
  obtain hne : ∀ x ∈ rcbR K.S K.A K.E, x ≠ K.neg := by
    have hnd := hL.nodup
    have hro := hL.ro
    simp only [combWs, combRo, rcbW, List.cons_append, List.nil_append,
      List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd hro ⊢
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false]
    grind
  obtain ha : ∀ x ∈ rcbR K.S K.A K.E,
      x + 8 * K.M.n ≤ K.neg ∨ K.neg + 8 * K.M.n ≤ x := by
    intro x hx
    apply hL.lay.apart x K.neg _ hnS (hne x hx)
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> comb_mem
  obtain hApart : RcbApart { K.S with b3 := K.neg } K.A K.E K.D := by
    refine ⟨hL.add.nodup, ?_⟩
    intro x hx
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hL.add.apart _ (by simp [rcbR])
    · have hnd := hL.nodup
      simp only [combWs, rcbW, List.cons_append, List.nil_append, List.nodup_cons,
        List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd ⊢
      grind
    all_goals exact hL.add.apart _ (by simp [rcbR])
  refine WP.seq (WP.mono (setConst_ok hs (n := K.M.n) (o := K.neg) (x := b)
    (hL.lay.le _ hnS) (hA.sl _ hnS) (Nat.lt_trans hb hpn)) fun s₁ ⟨e₁,k₁,O₁⟩ => ?_)
  obtain hs₁ := hs.of_keepRegs k₁ (by decide)
  obtain hm₁ : ModOkA K.M size C.p s₁.mem base :=
    hM.unch O₁.unch (fun w hw => by
      obtain rfl := List.mem_singleton.mp hw
      exact (hL.lay.mo K.neg hnS).symm) hn
  obtain read₁ : ∀ x ∈ rcbR K.S K.A K.E,
      wordsVal s₁.mem base x K.M.n = wordsVal s.mem base x K.M.n := by
    intro x hx
    exact O₁.wordsVal (ha x hx) (by
      obtain hxs : x ∈ combSlots K := by
        simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> comb_mem
      have := hL.lay.le x hxs; omega_using [hn, this])
  obtain hl₁ : ∀ x ∈ rcbR { K.S with b3 := K.neg } K.A K.E,
      wordsVal s₁.mem base x K.M.n < C.p := by
    intro x hx
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [read₁ _ (by simp [rcbR])]; exact hlt _ (by simp [rcbR])
    · rw [e₁]; exact hb
    all_goals (rw [read₁ _ (by simp [rcbR])]; exact hlt _ (by simp [rcbR]))
  refine WP.mono (generalSumCore_ok hL hA hp hs₁ hm₁ hl₁ hApart) fun s₂ h₂ => ?_
  refine ⟨h₂.scr, ?_, ?_, h₂.lt, ?_⟩
  · exact (k₁.mono fun r hr => by
      obtain rfl := List.mem_singleton.mp hr; simp [clob]).trans h₂.keep
  · exact (O₁.unch.trans h₂.unch).mono fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · obtain rfl := List.mem_singleton.mp hw
        exact List.mem_append_left _ (List.mem_map_of_mem hnW)
      · exact hw
  · have v := h₂.val
    simp only [tmv] at v ⊢
    rw [e₁] at v
    rw [read₁ K.S.a (by simp [rcbR]), read₁ K.A.x (by simp [rcbR]),
      read₁ K.A.y (by simp [rcbR]), read₁ K.A.z (by simp [rcbR]),
      read₁ K.E.x (by simp [rcbR]), read₁ K.E.y (by simp [rcbR]),
      read₁ K.E.z (by simp [rcbR])] at v
    exact v

end VG.Proof.Weierstrass.AArch64

end

end


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
  obtain hle : ∀ x, x ∈ combSlots K.toComb → x + 8 * K.M.n ≤ size := fun x hx => hL.comb.lay.le x hx
  obtain hmoW := combW_mo hL.comb hI.mod
  obtain hEW := entryW_sub (K := K.toComb)
  dsimp only [TCombCfg.toComb] at hEW
  refine WP.of_syms ?_
  unfold TCombCfg.generalStep
  refine WP.seq ?_
  rw [List.cons_append, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono_syms (decCounter_ok s hj (by omega_using [hjn, hJ]) hI.x19) fun s₁ h₁ sy₁ => ?_
  obtain ⟨b₁, k₁⟩ := h₁
  obtain hs₁ := hI.scr.of_keeps k₁ (by decide)
  have hm₁ : s₁.mem = s.mem := k₁.mem
  obtain hM₁ : ModOkA K.M size C.p s₁.mem base := by rw [hm₁]; exact hI.mod
  obtain hbits₁ : ∀ t < K.w * K.J, s₁.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0 :=
    fun t ht => by rw [hm₁]; exact hI.bits t ht
  obtain hzW := tcombW_ro hL (x := K.zero) (by simp [combRo, TCombCfg.toComb])
  obtain hz : wordsVal s₁.mem base K.zero K.M.n = 0 := by
    rw [hm₁, hI.unch.wordsVal hzW (by have := hle K.zero (by tcomb_mem); omega_using [hn, this]), hF.zero]
  obtain hT : s₁.syms K.tsym = T := by rw [sy₁]; exact hI.tsym
  obtain hTM : TblMem s₁ T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) :=
    hI.tbl.unch (by rw [k₁.rd, k₁.wr]) fun _ _ _ _ => by rw [hm₁]
  refine tentry_ok (publicLookup := false) hL hA hC hV hpn hs₁ hM₁ (i := j - 1) (by omega_using [hjn, hJ]) b₁ hbits₁ hz hT hTM hF.out
    fun s₃ E₃ => ?_
  obtain U₁₃ : Unch base (combW K.toComb) s.mem s₃.mem := by
    rw [← hm₁]
    exact E₃.unch.mono fun w hw => hEW w hw
  obtain U₃ : Unch base (tcombW K) s₀.mem s₃.mem :=
    (hI.unch.trans U₁₃).mono fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · exact hw
      · exact List.mem_append_left _ hw
  obtain hM₃ : ModOkA K.M size C.p s₃.mem base := hI.mod.unch U₁₃ hmoW hn
  -- What `A` and the read-only slots hold at `s₃`.
  have hnd := hL.comb.nodup
  dsimp only [TCombCfg.toComb] at hnd
  simp only [combWs, rcbW, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hnd
  obtain hAx : ∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s₃.mem base x K.M.n = wordsVal s.mem base x K.M.n :=
    fun x hx => by
      obtain hxs : x ∈ combWs K.toComb := by
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
  obtain hro : ∀ x ∈ combRo K.toComb, wordsVal s₃.mem base x K.M.n = wordsVal s₀.mem base x K.M.n :=
    fun x hx => U₃.wordsVal (tcombW_ro hL hx) (by
      have := hle x (combRo_slots x hx); omega_using [hn, this])
  obtain hlt₃ : ∀ x ∈ rcbR K.toComb.S K.toComb.A K.toComb.E, wordsVal s₃.mem base x K.M.n < C.p := by
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
  obtain ta : tmv C K.M.n base s₃ K.S.a = Fin.ofNat C.p C.a := by
    show toM _ _ _ = _; rw [hro _ (by simp [combRo, TCombCfg.toComb])]; exact hF.a
  obtain hRA : Rep C (tmv C K.M.n base s₃ K.A.x) (tmv C K.M.n base s₃ K.A.y)
      (tmv C K.M.n base s₃ K.A.z) (mul (combEW K.w k K.J j) (G C)) := by
    obtain ex : tmv C K.M.n base s₃ K.A.x = tmv C K.M.n base s K.A.x := by
      show toM _ _ _ = toM _ _ _; rw [hAx _ (by simp)]
    obtain ey : tmv C K.M.n base s₃ K.A.y = tmv C K.M.n base s K.A.y := by
      show toM _ _ _ = toM _ _ _; rw [hAx _ (by simp)]
    obtain ez : tmv C K.M.n base s₃ K.A.z = tmv C K.M.n base s K.A.z := by
      show toM _ _ _ = toM _ _ _; rw [hAx _ (by simp)]
    rw [ex, ey, ez]; exact hI.rep
  have hS := S₄.val
  rw [ta, hbm] at hS
  obtain hP := hC.onCurve_mul hG (combEW K.w k K.J j)
  obtain hQ : onCurve C (signedPtW C K.w k (j - 1)) = true := by
    unfold signedPtW combPtW
    split
    · exact hC.onCurve_mul hG _
    · exact onCurve_negPt (hC.onCurve_mul hG _)
  obtain hR := hC.add hP hQ hRA E₃.rep hS.symm
  obtain hadd := combW_add hC hG (w := K.w) (k := k) (J := K.J) (j := j - 1) (by omega_using [hjn, hJ])
  rw [Nat.sub_add_cancel hj] at hadd
  have hsp : signedPtW C K.w k (j - 1) = (if 2 ^ (K.w - 1) ≤ combWin K.w k (j - 1) then
      combPtW C K.w (j - 1) (combWin K.w k (j - 1) - 2 ^ (K.w - 1))
      else negPt (combPtW C K.w (j - 1) (2 ^ (K.w - 1) - combWin K.w k (j - 1)))) := rfl
  rw [hsp, hadd] at hR
  obtain hx₄ : s₄.gpr .x19 = BitVec.ofNat 64 (j - 1) := by
    rw [S₄.keep.gpr _ (x19_not_clob _), E₃.x19, b₁]
  obtain U₄ : Unch base (combW K.toComb) s.mem s₄.mem := (U₁₃.trans S₄.unch).mono fun w hw => by
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
    obtain hz : K.w * K.J ≤ K.kbytes + 8 * K.zw := by unfold TCombCfg.zw; have := hL.kbytes; omega_using []
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
  obtain hk : k < 2 ^ (K.w * K.J) :=
    Nat.lt_of_lt_of_le hF.k_lt (Nat.pow_le_pow_right (by decide) hL.kbytes)
  unfold TCombCfg.generalComb
  refine WP.seq (WP.mono (tcomb_init_ok hL hA hV hpn hs hM hF) fun s₆ I₆ => ?_)

  exact countLoop_ok (Inv := fun j s' =>
      TCombInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s s' j) (n := K.J)
    (by omega_using [hJ]) (fun j s' h1 h2 hi => generalStep_ok hL hA hC b3 hb hbm hG hV hpn hF h1 h2 hi)
    (fun s' hi => ⟨hi.keep, hi.unch, hi.mod, hi.lt, by rw [← combEW_zero hk]; exact hi.rep⟩)
    hJ.1 I₆

end VG.Proof.Weierstrass.AArch64
