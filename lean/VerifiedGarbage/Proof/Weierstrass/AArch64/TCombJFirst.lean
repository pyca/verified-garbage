import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombJEntry
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombJInvariant
import VerifiedGarbage.Proof.Weierstrass.AArch64.Window

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open Spec.Weierstrass

theorem firstJ_ok {K : TCombCfg} {C : Curve} {base : Addr} {size k : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hA : CombA K.toComb) (hC : Law C)
    (hG : onCurve C (G C) = true) (hV : TCombVals K C tbl) (hpn : C.p < 2 ^ (64 * K.M.n))
    (hb1 : 1 ≤ K.bits) {s : State} (hs : Scr s base size) (hM : ModOkA K.M size C.p s.mem base)
    (hF : TCombFixed K C base size s k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl)) :
    WP isa K.first s fun s' =>
      TCombJInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s s' 1 := by
  have hn := hs.nowrap
  have hJ := hL.comb.J
  rw [TCombCfg.toComb_J] at hJ
  have hw := hL.w
  have hnd := hL.comb.nodup
  dsimp only [TCombCfg.toComb] at hnd
  simp only [combWs, rcbW, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hnd
  have hle : ∀ x, x ∈ combSlots K.toComb → x + 8 * K.M.n ≤ size := fun x hx => hL.comb.lay.le x hx
  have b64 : ∀ x ∈ combSlots K.toComb, x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by
    have := hle x hx; omega_using [this, hn]
  have hsl : ∀ x ∈ combSlots K.toComb, K.bits + K.kbytes + 8 * K.zw ≤ x ∨ x + 8 * K.M.n ≤ K.bits + K.kbytes :=
    fun x hx => hL.bits_sl x (List.mem_cons_of_mem _ hx)
  have hbz := hL.bits
  have hzw : K.w * K.J ≤ K.kbytes + 8 * K.zw := by unfold TCombCfg.zw; have := hL.kbytes; omega
  have hk : k < 2 ^ (K.w * K.J) :=
    Nat.lt_of_lt_of_le hF.k_lt (Nat.pow_le_pow_right (by decide) hL.kbytes)
  have hmo : ∀ w ∈ tcombW K, K.M.mo + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ K.M.mo := by
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · exact combW_mo hL.comb hM w hw
    · simp only [List.mem_singleton] at hw; subst hw
      have := hL.bits_sl K.M.mo (List.mem_cons_self ..); dsimp only; omega
  -- `A`, apart from the cleared words.
  refine WP.of_syms ?_
  unfold TCombCfg.first
  refine WP.seq ?_
  have e : K.clearBits ++ [.movz .x .x19 0 0] ++ K.bdigit false ++ K.select = [zero7] ++
      ((List.range K.zw).map (fun i => st .x7 (K.bits + K.kbytes + 8 * i)) ++
        ([.movz .x .x19 0 0] ++ (K.bdigit false ++ K.select))) := by
    unfold TCombCfg.clearBits
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rfl
  rw [e, WP.block_append_iff]
  refine WP.mono_syms (zero7_ok s) fun s₁ ⟨z₁, k₁⟩ sy₁ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono_syms (zstores_ok hs₁ z₁ hL.bits8 K.zw hL.bits) fun s₂ ⟨k₂, O₂, z₂⟩ sy₂ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by simp)
  rw [WP.block_append_iff]
  refine WP.mono_syms (movz_ok s₂ .x19 0) fun s₃ ⟨b₃, k₃⟩ sy₃ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  have m₃ : s₃.mem = s₂.mem := k₃.mem
  have U₃ : Unch base [(K.bits + K.kbytes, 8 * K.zw)] s.mem s₃.mem := by
    rw [m₃, ← k₁.mem]; exact O₂.unch
  have U₃' : Unch base (tcombW K) s.mem s₃.mem := U₃.mono fun w hw => List.mem_append_right _ hw
  have hro : ∀ x ∈ combSlots K.toComb, wordsVal s₃.mem base x K.M.n = wordsVal s.mem base x K.M.n :=
    fun x hx => by rw [m₃, O₂.wordsVal (by have := hsl x hx; omega) (b64 x hx), k₁.mem]
  have hM₃ : ModOkA K.M size C.p s₃.mem base := hM.unch U₃' hmo hn
  have hz₃ : wordsVal s₃.mem base K.zero K.M.n = 0 := by rw [hro _ (by tcomb_mem)]; exact hF.zero
  have hbits₃ : ∀ t < K.w * K.J, s₃.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0 := by
    intro t ht
    by_cases htk : t < K.kbytes
    · rw [U₃.byte (fun w hw => by
        simp only [List.mem_singleton] at hw; subst hw; dsimp only; omega)
        (by omega_using [hbz, hzw, ht, hn])]
      exact hF.bits t htk
    · have := z₂ (t - K.kbytes) (by omega)
      rw [show K.bits + K.kbytes + (t - K.kbytes) = K.bits + t by omega] at this
      rw [m₃, this, Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hF.k_lt
        (Nat.pow_le_pow_right (by decide) (by omega)))]
      rfl
  have hT₃ : s₃.syms K.tsym = T := by rw [sy₃, sy₂, sy₁]; exact hF.tsym
  have hTM₃ : TblMem s₃ T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) :=
    TblMem.of_unch hF.tbl (by rw [k₃.rd, k₃.wr, k₂.rd, k₂.wr, k₁.rd, k₁.wr]) U₃'
      (tcombW_size hL hM) hF.out
  refine tentryJ_ok hL hA hC hV hpn hs₃ hM₃ (i := 0) (by omega) b₃ hb1 (c := false)
    (Or.inr ⟨rfl, rfl⟩) hbits₃ hz₃ hT₃ hTM₃ hF.out fun s₅ E₅ => ?_
  rw [WP.block_append_iff]
  have hAE : ∀ x ∈ [K.A.x, K.A.y, K.A.z, K.E.x, K.E.y, K.E.z], x ∈ combWs K.toComb := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> tcomb_mem
  refine WP.mono (copyPt_ok E₅.scr (o := K.A) (a := K.E) (n := K.M.n)
    (fun x hx => hle x (combWs_slots _ x (hAE x hx)))
    (fun x hx => hA.sl x (combWs_slots _ x (hAE x hx)))
    (fun x hx y hy hxy => hL.comb.apart₂ (hAE x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; rcases hx with h | h | h <;> simp [h]))
      (hAE y hy) hxy)
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> grind)
    ⟨by grind, by grind, by grind⟩) fun s₆ ⟨ex₆, ey₆, ez₆, k₆, U₆⟩ => ?_
  refine WP.mono (movz_ok s₆ .x19 1) fun s₇ ⟨b₇, k₇⟩ sy₇ => ?_
  have m₇ : s₇.mem = s₆.mem := k₇.mem
  have hEW : ∀ w ∈ [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n), (K.neg, 8 * K.M.n),
      (K.M.tmp, 8 * K.M.n)], w ∈ combW K.toComb := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [combW, combWs, List.mem_append, List.mem_map, List.mem_cons,
      List.not_mem_nil, or_false, TCombCfg.toComb]
    rcases hw with h | h | h | h | h <;> subst h <;> simp
  have hAW : ∀ w ∈ [(K.A.x, 8 * K.M.n), (K.A.y, 8 * K.M.n), (K.A.z, 8 * K.M.n)], w ∈ combW K.toComb := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [combW, combWs, List.mem_append, List.mem_map, List.mem_cons,
      List.not_mem_nil, or_false, TCombCfg.toComb]
    rcases hw with h | h | h <;> subst h <;> simp
  have U : Unch base (combW K.toComb) s₃.mem s₇.mem := by
    rw [m₇]; exact (E₅.unch.trans U₆).mono fun w hw => by
      rcases List.mem_append.mp hw with h | h
      · exact hEW w h
      · exact hAW w h
  have UT : Unch base (tcombW K) s.mem s₇.mem := (U₃'.trans U).mono fun w hw => by
    rcases List.mem_append.mp hw with h | h
    · exact h
    · exact List.mem_append_left _ h
  refine ⟨E₅.scr.of_keepRegs k₆ (by decide) |>.of_keeps k₇ (by decide), b₇, ?_, UT, hM.unch UT hmo hn,
    ?_, ?_, fun t ht => ?_, ?_, by rw [sy₇]; exact hF.tsym⟩
  · have c : ∀ r∈[Reg.x7],r∈tcombClob K.M.n := by
      intro r hr; rw [List.mem_singleton.mp hr]; simp [tcombClob,combClob,clob]
    have cb : ∀ r∈[Reg.x19],r∈tcombClob K.M.n := by
      intro r hr; rw [List.mem_singleton.mp hr]; simp [tcombClob,combClob]
    have c1 : ∀ r∈[Reg.x1],r∈tcombClob K.M.n := by
      intro r hr; rw [List.mem_singleton.mp hr]; simp [tcombClob,combClob,clob]
    exact (((((Keeps.regs k₁).mono c).trans (k₂.mono fun r hr => absurd hr List.not_mem_nil)).trans
      ((Keeps.regs k₃).mono cb)).trans E₅.keep).trans
      ((k₆.mono c1).trans ((Keeps.regs k₇).mono cb))
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [m₇, ex₆]; exact E₅.lt _ (by simp)
    · rw [m₇, ey₆]; exact E₅.lt _ (by simp)
    · rw [m₇, ez₆]; exact E₅.lt _ (by simp)
  · have e : ∀ {x y : Nat}, wordsVal s₇.mem base x K.M.n = wordsVal s₅.mem base y K.M.n →
        tmv C K.M.n base s₇ x = tmv C K.M.n base s₅ y := fun h => by show toM _ _ _ = toM _ _ _; rw [h]
    rw [e (by rw [m₇, ex₆]), e (by rw [m₇, ey₆]), e (by rw [m₇, ez₆])]
    rw [show (1 : Nat) = 0 + 1 from rfl, bpart_succ_pt hC hG (by omega), bpart_zero,
      show zmul (0 : Int) (G C) = .infinity by simp [zmul, Spec.Weierstrass.mul], infinity_add']
    refine InvJ.of_rep01 E₅.rep ?_
    change toM _ _ (wordsVal s₅.mem base K.E.z K.M.n)=1 ∨ toM _ _ (wordsVal s₅.mem base K.E.z K.M.n)=0
    rw [E₅.z]; split
    · exact Or.inl hV.one
    · exact Or.inr (toM_zero _ _)
  · rw [U.byte (combW_bits hL ht) (by omega_using [hbz, hzw, ht, hn])]
    exact hbits₃ t ht
  · exact TblMem.of_unch hF.tbl (by rw [k₇.rd, k₇.wr, k₆.rd, k₆.wr, E₅.keep.rd, E₅.keep.wr,
      k₃.rd, k₃.wr, k₂.rd, k₂.wr, k₁.rd, k₁.wr]) UT (tcombW_size hL hM) hF.out


end VG.Proof.Weierstrass.AArch64
