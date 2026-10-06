import VerifiedGarbage.Impl.Weierstrass.AArch64.Jacobian
import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
import VerifiedGarbage.Proof.Weierstrass.JacAdd

/-! Fixed-base public comb with a Jacobian accumulator. -/
namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open Spec.Weierstrass

structure JacCombInv (K : TCombCfg) (C : Curve) (base : Addr) (size k : Nat) (T : Addr)
    (ws : List (BitVec 64)) (s₀ s : State) (j : Nat) : Prop where
  scr : Scr s base size
  x19 : s.gpr .x19 = BitVec.ofNat 64 j
  keep : KeepRegs (tcombClob K.M.n) s₀ s
  unch : Unch base (tcombW K) s₀.mem s.mem
  mod : ModOkA K.M size C.p s.mem base
  lt : ∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s.mem base x K.M.n < C.p
  rep : InvJ C (tmv C K.M.n base s K.A.x) (tmv C K.M.n base s K.A.y) (tmv C K.M.n base s K.A.z)
    (mul (combEW K.w k K.J j) (G C))
  bits : ∀ t < K.w * K.J, s.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0
  tbl : TblMem s T ws
  tsym : s.syms K.tsym = T

theorem jacComb_init_values_ok {K : TCombCfg} {C : Curve} {base : Addr} {size k : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hA : CombA K.toComb)
    (hV : TCombVals K C tbl)
    (hpn : C.p < 2 ^ (64 * K.M.n)) {s : State} (hs : Scr s base size)
    (hM : ModOkA K.M size C.p s.mem base)
    (hF : TCombFixed K C base size s k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl)) :
    WP isa (.block K.init) s fun s' =>
      JacCombInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s s' K.J ∧
      wordsVal s'.mem base K.A.x K.M.n = K.start.1 ∧
      wordsVal s'.mem base K.A.y K.M.n = K.start.2 ∧
      wordsVal s'.mem base K.A.z K.M.n = K.one := by
  have hn := hs.nowrap
  have hJ := hL.comb.J
  rw [TCombCfg.toComb_J] at hJ
  have hnd := hL.comb.nodup
  dsimp only [TCombCfg.toComb] at hnd
  simp only [combWs, rcbW, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hnd
  have le : ∀ x ∈ combWs K.toComb, x + 8 * K.M.n ≤ size := fun x hx =>
    hL.comb.lay.le x (combWs_slots _ x hx)
  have al : ∀ x ∈ combWs K.toComb, x % 8 = 0 := fun x hx => hA.sl x (combWs_slots _ x hx)
  have b64 : ∀ x ∈ combWs K.toComb, x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by
    have := le x hx; omega_using [this, hn]
  have axy := hL.comb.apart₂ (x := K.A.x) (y := K.A.y) (by tcomb_mem) (by tcomb_mem) (by grind)
  have axz := hL.comb.apart₂ (x := K.A.x) (y := K.A.z) (by tcomb_mem) (by tcomb_mem) (by grind)
  have ayz := hL.comb.apart₂ (x := K.A.y) (y := K.A.z) (by tcomb_mem) (by tcomb_mem) (by grind)
  dsimp only [TCombCfg.toComb] at axy axz ayz
  have hsl : ∀ x ∈ combWs K.toComb, K.bits + K.kbytes + 8 * K.zw ≤ x ∨ x + 8 * K.M.n ≤ K.bits + K.kbytes :=
    fun x hx => hL.bits_sl x (List.mem_cons_of_mem _ (combWs_slots _ x hx))
  have hbz := hL.bits
  have hzw : K.w * K.J ≤ K.kbytes + 8 * K.zw := by unfold TCombCfg.zw; have := hL.kbytes; omega
  refine WP.of_syms ?_
  have e : K.init = setConst K.M.n K.A.x K.start.1 ++ (setConst K.M.n K.A.y K.start.2 ++
      (setConst K.M.n K.A.z K.one ++ ([zero7] ++ ((List.range K.zw).map
        (fun i => st .x7 (K.bits + K.kbytes + 8 * i)) ++ [.movz .x .x19 (BitVec.ofNat 16 K.J) 0])))) := by
    unfold TCombCfg.init TCombCfg.zw
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [e, WP.block_append_iff]
  have W1 := setConst_ok hs (n := K.M.n) (o := K.A.x) (x := K.start.1) (le _ (by tcomb_mem))
    (al _ (by tcomb_mem)) (Nat.lt_trans hV.start_lt.1 hpn)
  refine WP.mono W1 fun s₁ h₁ => ?_
  obtain ⟨e₁, k₁, O₁⟩ := h₁
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [WP.block_append_iff]
  have W2 := setConst_ok hs₁ (n := K.M.n) (o := K.A.y) (x := K.start.2) (le _ (by tcomb_mem))
    (al _ (by tcomb_mem)) (Nat.lt_trans hV.start_lt.2 hpn)
  refine WP.mono W2 fun s₂ h₂ => ?_
  obtain ⟨e₂, k₂, O₂⟩ := h₂
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  rw [WP.block_append_iff]
  have W3 := setConst_ok hs₂ (n := K.M.n) (o := K.A.z) (x := K.one) (le _ (by tcomb_mem))
    (al _ (by tcomb_mem)) (Nat.lt_trans hV.one_lt hpn)
  refine WP.mono W3 fun s₃ h₃ => ?_
  obtain ⟨e₃, k₃, O₃⟩ := h₃
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (zero7_ok s₃) fun s₄ h₄ => ?_
  obtain ⟨z₄, k₄⟩ := h₄
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (zstores_ok hs₄ z₄ hL.bits8 K.zw hL.bits) fun s₅ h₅ => ?_
  obtain ⟨k₅, O₅, z₅⟩ := h₅
  have hs₅ := hs₄.of_keepRegs k₅ (by simp)
  refine WP.mono (setCounter_ok s₅ (j := K.J) (by omega)) fun s₆ h₆ => ?_
  obtain ⟨b₆, k₆⟩ := h₆
  have m₆ : s₆.mem = s₅.mem := k₆.mem
  have U₃ : Unch base (combW K.toComb) s.mem s₃.mem :=
    (O₁.unch.trans (O₂.unch.trans O₃.unch)).mono fun w hw => by
      simp only [combW, combWs, rcbW, List.map_append, List.map_cons, List.map_nil, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false, TCombCfg.toComb] at hw ⊢
      grind
  have U₆ : Unch base (tcombW K) s.mem s₆.mem := by
    rw [m₆]
    refine (U₃.trans (show Unch base [(K.bits + K.kbytes, 8 * K.zw)] s₃.mem s₅.mem by
      rw [← k₄.mem]; exact O₅.unch)).mono fun w hw => hw
  have hmo : ∀ w ∈ tcombW K, K.M.mo + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ K.M.mo := by
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · exact combW_mo hL.comb hM w hw
    · simp only [List.mem_singleton] at hw; subst hw
      have := hL.bits_sl K.M.mo (List.mem_cons_self ..); dsimp only; omega
  -- `A`, apart from the cleared words.
  have hA5 : ∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s₆.mem base x K.M.n = wordsVal s₃.mem base x K.M.n :=
    fun x hx => by
      have hxs : x ∈ combWs K.toComb := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl <;> tcomb_mem
      rw [m₆, O₅.wordsVal (by have := hsl x hxs; omega) (b64 x hxs), k₄.mem]
  have vx : wordsVal s₆.mem base K.A.x K.M.n = K.start.1 := by
    rw [hA5 _ (by simp), O₃.wordsVal axz (b64 _ (by tcomb_mem)), O₂.wordsVal axy (b64 _ (by tcomb_mem)), e₁]
  have vy : wordsVal s₆.mem base K.A.y K.M.n = K.start.2 := by
    rw [hA5 _ (by simp), O₃.wordsVal ayz (b64 _ (by tcomb_mem)), e₂]
  have vz : wordsVal s₆.mem base K.A.z K.M.n = K.one := by rw [hA5 _ (by simp), e₃]
  have hk : k < 2 ^ (K.w * K.J) :=
    Nat.lt_of_lt_of_le hF.k_lt (Nat.pow_le_pow_right (by decide) hL.kbytes)
  intro sy₆
  have I₆ : JacCombInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s s₆ K.J := by
    refine ⟨hs₅.of_keeps k₆ (by decide), b₆, ?_, U₆, hM.unch U₆ hmo hn, ?_, ?_, fun t ht => ?_, ?_,
      by rw [sy₆]; exact hF.tsym⟩
    · have c1 : ∀ r ∈ [Reg.x1], r ∈ tcombClob K.M.n := fun r hr => combClob_tcombClob _
        (combClob_mem (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hr))))
      exact ((((k₁.mono c1).trans (k₂.mono c1)).trans (k₃.mono c1)).trans
        ((Keeps.regs k₄).mono fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact combClob_tcombClob _ (combClob_mem (by simp)))).trans
        ((k₅.mono fun r hr => absurd hr (List.not_mem_nil)).trans
        ((Keeps.regs k₆).mono fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact combClob_tcombClob _ (by simp [combClob])))
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · rw [vx]; exact hV.start_lt.1
      · rw [vy]; exact hV.start_lt.2
      · rw [vz]; exact hV.one_lt
    · show InvJ C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
      rw [vx, vy, vz, hV.one, combEW_top]
      exact Or.inr (by simpa only [Lean.Grind.Semiring.mul_one, TCombCfg.H] using hV.start)
    · by_cases htk : t < K.kbytes
      · rw [U₆.byte (fun w hw => by
          rcases List.mem_append.mp hw with hw | hw
          · exact combW_bits hL ht w hw
          · simp only [List.mem_singleton] at hw; subst hw; dsimp only; omega)
          (by omega_using [hbz, hzw, ht, hn])]
        exact hF.bits t htk
      · have := z₅ (t - K.kbytes) (by omega)
        rw [show K.bits + K.kbytes + (t - K.kbytes) = K.bits + t by omega] at this
        rw [m₆, this, Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hF.k_lt
          (Nat.pow_le_pow_right (by decide) (by omega)))]
        rfl
    · exact TblMem.of_unch hF.tbl (by rw [k₆.rd, k₆.wr, k₅.rd, k₅.wr, k₄.rd, k₄.wr, k₃.rd, k₃.wr,
        k₂.rd, k₂.wr, k₁.rd, k₁.wr]) U₆ (tcombW_size hL hM) hF.out
  exact ⟨I₆,vx,vy,vz⟩


theorem jacComb_init_ok {K : TCombCfg} {C : Curve} {base : Addr} {size k : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hA : CombA K.toComb)
    (hV : TCombVals K C tbl)
    (hpn : C.p < 2 ^ (64 * K.M.n)) {s : State} (hs : Scr s base size)
    (hM : ModOkA K.M size C.p s.mem base)
    (hF : TCombFixed K C base size s k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl)) :
    WP isa (.block K.init) s fun s' =>
      JacCombInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s s' K.J :=
  WP.mono (jacComb_init_values_ok hL hA hV hpn hs hM hF) fun _ h => h.1

/-- The result of one mixed Jacobian addition and accumulator copy. -/
structure JacCombSumPost (K : TCombCfg) (C : Curve) (base : Addr) (size : Nat)
    (P Q : Point C) (s s' : State) : Prop where
  scr : Scr s' base size
  keep : KeepRegs (clob K.M.n) s s'
  unch : Unch base (combW K.toComb) s.mem s'.mem
  lt : ∀ x ∈ [K.A.x,K.A.y,K.A.z], wordsVal s'.mem base x K.M.n < C.p
  rep : InvJ C (tmv C K.M.n base s' K.A.x) (tmv C K.M.n base s' K.A.y)
    (tmv C K.M.n base s' K.A.z) (Spec.Weierstrass.add P Q)

/-- The field-program proof is independent of the scalar recoding and tables. -/
def JacCombSumCorrect (K : TCombCfg) (C : Curve) (base : Addr) (size : Nat) : Prop :=
  ∀ (s : State) (P Q : Point C), Scr s base size → ModOkA K.M size C.p s.mem base →
    (∀ x ∈ rcbR K.S K.A K.E, wordsVal s.mem base x K.M.n < C.p) →
    tmv C K.M.n base s K.S.b3 = Fin.ofNat C.p C.b →
    onCurve C P = true → onCurve C Q = true →
    InvJ C (tmv C K.M.n base s K.A.x) (tmv C K.M.n base s K.A.y) (tmv C K.M.n base s K.A.z) P →
    Rep C (tmv C K.M.n base s K.E.x) (tmv C K.M.n base s K.E.y) (tmv C K.M.n base s K.E.z) Q →
    tmv C K.M.n base s K.E.z = 1 →
    WP isa (Jacobian.jacCombSum K) s (JacCombSumPost K C base size P Q s)

theorem jacComb_step_ok {K : TCombCfg} {C : Curve} {base : Addr} {size k : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hA : CombA K.toComb) (hC : Law C)
    (hG : onCurve C (G C) = true) (hV : TCombVals K C tbl)
    (hpn : C.p < 2 ^ (64 * K.M.n))
    (hSum : JacCombSumCorrect K C base size) {s₀ : State}
    (hF : TCombFixed K C base size s₀ k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl))
    {j : Nat} {s : State} (hj : 1 ≤ j) (hjn : j ≤ K.J)
    (hI : JacCombInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s₀ s j) :
    WP isa (Jacobian.jacCombStep K) s fun s' =>
      JacCombInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s₀ s' (j - 1) ∧
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
  unfold Jacobian.jacCombStep
  refine WP.seq ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono_syms (decCounter_ok s hj (by omega) hI.x19) fun d ⟨bd,kd⟩ syd => ?_
  have hwi : K.w * (j-1) + K.w ≤ K.w * K.J := by
    rw [← Nat.mul_succ, show (j-1).succ=j by omega]
    exact Nat.mul_le_mul_left K.w hjn
  have hb : K.bits + K.w * K.J ≤ size := by
    have := hL.bits
    have := hL.kbytes
    unfold TCombCfg.zw at *
    omega
  refine WP.mono_syms (digitW_ok K (hI.scr.of_keeps kd (by decide)) (k := k)
    (j := j-1) (N := K.w*K.J) (by have := hL.w; omega) (by have := hL.w; omega)
    hwi hb (by have := hL.bitsw; omega) bd (fun q hq => by rw [kd.mem]; exact hI.bits q hq))
    fun s₁ ⟨mag,kbit⟩ sybit => ?_
  have k₁ : Keeps [.x19,.x2,.x3,.x4,.x9,.x16] s s₁ :=
    (kd.mono (by simp)).trans (kbit.mono (by simp))
  have b₁ : s₁.gpr .x19 = BitVec.ofNat 64 (j-1) := by rw [kbit.gpr _ (by decide),bd]
  have sy₁ : s₁.syms = s.syms := sybit.trans syd
  have hs₁ := hI.scr.of_keeps k₁ (by decide)
  have hm₁ : s₁.mem = s.mem := k₁.mem
  have hM₁ : ModOkA K.M size C.p s₁.mem base := by rw [hm₁]; exact hI.mod
  have hbits₁ : ∀ t < K.w * K.J, s₁.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0 :=
    fun t ht => by rw [hm₁]; exact hI.bits t ht
  have hzW := tcombW_ro hL (x := K.zero) (by simp [combRo, TCombCfg.toComb])
  have hz : wordsVal s₁.mem base K.zero K.M.n = 0 := by
    rw [hm₁, hI.unch.wordsVal hzW (by have := hle K.zero (by tcomb_mem); omega), hF.zero]
  have hT : s₁.syms K.tsym = T := by rw [sy₁]; exact hI.tsym
  have hTM : TblMem s₁ T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) :=
    hI.tbl.unch (by rw [k₁.rd, k₁.wr]) fun _ _ _ _ => by rw [hm₁]
  have hmaglt : magH K.H (combWin K.w k (j-1)) < 2^64 := by
    have hw := hL.w
    have eh : 2^K.w = 2*K.H := by
      unfold TCombCfg.H
      rw [← Nat.pow_succ']
      congr 1
      omega
    have hm := magH_le (by rw [← eh]; exact combWin_lt K.w k (j-1))
    have hH : K.H ≤ 128 := Nat.le_trans
      (Nat.pow_le_pow_right (by decide) (show K.w-1≤7 by omega)) (by decide)
    omega
  refine WP.ite (decide (magH K.H (combWin K.w k (j-1)) ≠ 0))
    (by
      have hz : BitVec.ofNat 64 (magH K.H (combWin K.w k (j-1))) = 0 ↔
          magH K.H (combWin K.w k (j-1)) = 0 := by
        constructor
        · intro h
          have he : (BitVec.ofNat 64 (magH K.H (combWin K.w k (j-1)))).toNat = 0 := congrArg BitVec.toNat h
          simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hmaglt] using he
        · intro h; rw [h]; rfl
      by_cases he : magH K.H (combWin K.w k (j-1)) = 0
      · simp [eval,State.read,Size.bits,mag,he]
      · have hn := mt hz.mp he
        simp [eval,State.read,Size.bits,mag,he]
        exact hn)
    (fun hnonzero => ?_) (fun hzero => ?_)
  · have hnonzero : 1 ≤ magH K.H (combWin K.w k (j-1)) := by
      simp only [decide_eq_true_eq] at hnonzero
      omega
    refine WP.seq ?_
    rw [WP.block_append_iff]
    simp only [← WP.seq_iff]
    refine WP.seq ?_
    refine tentry_after_digit_ok (publicLookup := true) hL hA hC hV hpn hs₁ hM₁
      (i := j-1) (by omega) b₁ mag hbits₁ hz hT hTM hF.out
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
          · exact hL.comb.apart₂ hxs (by tcomb_mem) (by grind)
          · exact hL.comb.apart₂ hxs (by tcomb_mem) (by grind)
          · exact hL.comb.apart₂ hxs (by tcomb_mem) (by grind)
          · exact hL.comb.apart₂ hxs (by tcomb_mem) (by grind)
          · exact hL.comb.lay.tmp x (combWs_slots _ x hxs))
          (by have := hle x (combWs_slots _ x hxs); omega), hm₁]
    have hro : ∀ x ∈ combRo K.toComb, wordsVal s₃.mem base x K.M.n = wordsVal s₀.mem base x K.M.n :=
      fun x hx => U₃.wordsVal (tcombW_ro hL hx) (by
        have := hle x (combRo_slots x hx); omega)
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
    have tb : tmv C K.M.n base s₃ K.S.b3 = Fin.ofNat C.p C.b := by
      show toM _ _ _ = _; rw [hro _ (by simp [combRo, TCombCfg.toComb])]; exact hF.b
    have hRA : InvJ C (tmv C K.M.n base s₃ K.A.x) (tmv C K.M.n base s₃ K.A.y)
        (tmv C K.M.n base s₃ K.A.z) (mul (combEW K.w k K.J j) (G C)) := by
      have ex : tmv C K.M.n base s₃ K.A.x = tmv C K.M.n base s K.A.x := by
        show toM _ _ _ = toM _ _ _; rw [hAx _ (by simp)]
      have ey : tmv C K.M.n base s₃ K.A.y = tmv C K.M.n base s K.A.y := by
        show toM _ _ _ = toM _ _ _; rw [hAx _ (by simp)]
      have ez : tmv C K.M.n base s₃ K.A.z = tmv C K.M.n base s K.A.z := by
        show toM _ _ _ = toM _ _ _; rw [hAx _ (by simp)]
      rw [ex, ey, ez]; exact hI.rep
    have hP := hC.onCurve_mul hG (combEW K.w k K.J j)
    have hQ : onCurve C (signedPtW C K.w k (j - 1)) = true := by
      unfold signedPtW combPtW
      split
      · exact hC.onCurve_mul hG _
      · exact onCurve_negPt (hC.onCurve_mul hG _)
    have hez : tmv C K.M.n base s₃ K.E.z = 1 := by
      show toM _ _ _ = _
      rw [E₃.z,ite_eq_left hnonzero,hV.one]
    refine WP.mono (hSum s₃ _ _ E₃.scr hM₃ hlt₃ tb hP hQ hRA E₃.rep hez) fun s₄ S₄ => ?_
    have hR := S₄.rep
    have hadd := combW_add hC hG (w := K.w) (k := k) (J := K.J) (j := j - 1) (by omega)
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
      · intro r hr
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | hr
        · exact combClob_tcombClob _ (by simp [combClob])
        · exact tcombClob_sub _ hn4 _ (by
            simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
            grind)
      · exact combClob_tcombClob _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_append_right _ hr)))
    · rcases List.mem_append.mp hw with hw | hw
      · exact hw
      · exact List.mem_append_left _ hw
    · have hb := hL.bits
      have hz : K.w * K.J ≤ K.kbytes + 8 * K.zw := by unfold TCombCfg.zw; have := hL.kbytes; omega
      rw [U₄.byte (combW_bits hL ht) (by omega_using [hb, hz, ht, hn])]
      exact hI.bits t ht
    · exact TblMem.of_unch hI.tbl (by rw [S₄.keep.rd, S₄.keep.wr, E₃.keep.rd, E₃.keep.wr, k₁.rd, k₁.wr])
        U₄ (fun w hw => tcombW_size hL hI.mod w (List.mem_append_left _ hw)) hF.out
  
  · have hm0 : magH K.H (combWin K.w k (j-1)) = 0 := by
      simpa only [decide_eq_false_iff_not, not_not] using hzero
    have hw0 : combWin K.w k (j-1) = K.H := by
      unfold magH at hm0
      split at hm0 <;> omega
    have he : combEW K.w k K.J (j-1) = combEW K.w k K.J j := by
      have he := combEW_step (w := K.w) (k := k) (J := K.J) (j := j-1) (by omega)
      rw [Nat.sub_add_cancel hj,hw0] at he
      exact Nat.add_right_cancel he
    refine WP.block_nil ?_
    intro _
    refine ⟨⟨hs₁,b₁,?_,?_,hM₁,?_,?_,hbits₁,hTM,hT⟩,b₁⟩
    · exact hI.keep.trans ((Keeps.regs k₁).mono (by
        intro r hr
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | hr
        · exact combClob_tcombClob _ (by simp [combClob])
        · exact tcombClob_sub _ hn4 _ (by
            simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
            grind)))
    · rw [hm₁]; exact hI.unch
    · rw [hm₁]; exact hI.lt
    · simpa only [tmv,hm₁,he] using hI.rep


theorem jacComb_loop_ok {K : TCombCfg} {C : Curve} {base : Addr} {size k : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hA : CombA K.toComb) (hC : Law C)
    (hG : onCurve C (G C) = true) (hV : TCombVals K C tbl)
    (hpn : C.p < 2 ^ (64 * K.M.n))
    (hSum : JacCombSumCorrect K C base size) {s : State} (hs : Scr s base size)
    (hM : ModOkA K.M size C.p s.mem base)
    (hF : TCombFixed K C base size s k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl)) :
    WP isa (Jacobian.jacCombLoop K) s fun s' => KeepRegs (tcombClob K.M.n) s s' ∧ Unch base (tcombW K) s.mem s'.mem ∧
      ModOkA K.M size C.p s'.mem base ∧
      (∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      InvJ C (tmv C K.M.n base s' K.A.x) (tmv C K.M.n base s' K.A.y) (tmv C K.M.n base s' K.A.z)
        (mul k (G C)) := by
  have hJ := hL.comb.J
  rw [TCombCfg.toComb_J] at hJ
  have hk : k < 2 ^ (K.w * K.J) :=
    Nat.lt_of_lt_of_le hF.k_lt (Nat.pow_le_pow_right (by decide) hL.kbytes)
  unfold Jacobian.jacCombLoop
  refine WP.seq (WP.mono (jacComb_init_ok hL hA hV hpn hs hM hF) fun s₆ I₆ => ?_)

  exact countLoop_ok (Inv := fun j s' =>
      JacCombInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s s' j) (n := K.J)
    (by omega) (fun j s' h1 h2 hi => jacComb_step_ok hL hA hC hG hV hpn hSum hF h1 h2 hi)
    (fun s' hi => ⟨hi.keep, hi.unch, hi.mod, hi.lt, by rw [← combEW_zero hk]; exact hi.rep⟩)
    hJ.1 I₆

end VG.Proof.Weierstrass.AArch64
