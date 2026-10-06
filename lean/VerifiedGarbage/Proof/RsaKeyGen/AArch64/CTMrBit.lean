import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMs
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrLoop

/-!
# A candidate on AArch64: constant time of a bit of Miller–Rabin's exponentiation

`mrExpBit`, for runs that agree on the working space (`mrExpBit_ct`): the
multiplications (`Mont.ct`), the copy and the comparisons (after `ws`), the
selection (its pointers and count pinned after its block, `bitSel_ok`), and
the blocks that only address the header. Between the pieces each run keeps
`c`, `-c⁻¹` and the witness (`B1`), and `[aXm] < c` before the second
multiplication.
-/

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.Public (aN aAcc aTmp aXm aY sCnt)

/-- The working space. -/
def WsQ (L : WsP) (s : State) : Prop := Ws s L.B L.Z L.w

theorem pins_wsq : Pins WsQ [.x0] := pins_ws' (fun L : WsP => L.B) (fun L : WsP => L.Z) (fun L : WsP => L.w) fun _ _ h => h

/-- `eqMask j` leaks the same in runs with the same working space. -/
theorem eqMask_ct {j : Nat} (hj : j < 16) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block [movi .x9 0, mov .x14 .x12])
      (.seq (.block (base aY .x16 ++ base j .x17)) (.seq (countLoop .x14 xorBody)
        (.block ([movi .x7 0, movi .x4 1, .subs .x .x3 .x9 .x4] ++ borrowMask))))) hc).isSome = true) :
    RelCT isa (Two WsQ) (seqs (eqMask j)) (Two WsQ) :=
  ws_ct (fun L : WsP => L.B) (fun L : WsP => L.Z) (fun L : WsP => L.w) (fun _ _ h => h) ht fun _ _ h =>
    WP.mono (eqMask_ok h hj) fun _ ⟨_, hm, k⟩ => h.congr' (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k
      (by decide)

theorem shr63_bit (V : BitVec 64) : ∃ bt : Bool, V >>> 63 = BitVec.ofNat 64 bt.toNat := by
  have hV := V.isLt
  refine ⟨decide (2 ^ 63 ≤ V.toNat), BitVec.eq_of_toNat_eq ?_⟩
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  rcases Nat.lt_or_ge V.toNat (2 ^ 63) with h | h
  · rw [decide_eq_false (by omega), Nat.div_eq_of_lt h]; rfl
  · have e : V.toNat / 2 ^ 63 = 1 := Nat.div_eq_of_lt_le (k := 1) (by rw [Nat.one_mul]; exact h) (by omega)
    rw [decide_eq_true h, e]; rfl

/-! ## What the pieces keep -/

/-- What `mrExpBit` needs. -/
def B0 (L : WsP) (s : State) : Prop :=
  4 ≤ L.w ∧ L.w ≤ 64 ∧ ∃ c b y, MrCtx s L.B L.Z L.w c (b * 2 ^ (64 * L.w) % c) ∧ c % 2 = 1 ∧ 1 < c ∧
    wv s.mem L.B (slot L.w aY) L.w = y * 2 ^ (64 * L.w) % c

/-- `c`, `-c⁻¹` and the witness. -/
def B1 (L : WsP) (s : State) : Prop :=
  4 ≤ L.w ∧ L.w ≤ 64 ∧ ∃ c b, MrCtx s L.B L.Z L.w c (b * 2 ^ (64 * L.w) % c) ∧ c % 2 = 1 ∧ 1 < c

/-- With `[aXm] < c`. -/
def B2 (L : WsP) (s : State) : Prop :=
  4 ≤ L.w ∧ L.w ≤ 64 ∧ ∃ c b, MrCtx s L.B L.Z L.w c (b * 2 ^ (64 * L.w) % c) ∧ c % 2 = 1 ∧ 1 < c ∧
    wv s.mem L.B (slot L.w aXm) L.w < c

/-- Before the selection. -/
def B3 (L : WsP) (s : State) : Prop :=
  B2 L s ∧ s.gpr .x14 = BitVec.ofNat 64 L.w ∧ s.gpr .x16 = off L.B (slot L.w aB) ∧
    s.gpr .x17 = off L.B (slot L.w aXm) ∧ ∃ bt, s.gpr .x15 = mask bt

theorem b2_mm (M : Mont) {L : WsP} {s : State} {o a b : Nat} (h : B2 L s) (ho : o < 8) (ha : a < 8) (hb : b < 8)
    (d1 : o ≠ aAcc) (d2 : o ≠ aTmp) (d3 : a ≠ aAcc) (d4 : b ≠ aAcc) (d5 : a ≠ aTmp) (d6 : b ≠ aTmp)
    (hB : ∀ c, wv s.mem L.B (slot L.w aXm) L.w < c → wv s.mem L.B (slot L.w aN) L.w = c →
      wv s.mem L.B (slot L.w b) L.w < c)
    (hr : ∀ r ∈ [(slot L.w aAcc, 8 * (L.w + 2)), (slot L.w aTmp, 8 * (L.w + 2)), (slot L.w o, 8 * (L.w + 2))],
      r ∈ bitRanges L.w) :
    WP isa (M.mm o a b) s (B1 L) := by
  obtain ⟨h4, h64, c, bb, hc, hodd, hc1, hX⟩ := h
  have hg := hc.good
  refine WP.mono (M.mm_ok hg.1 hg.2 (by omega) (by omega) ho ha hb d1 d2 d3 d4 hc.inv
    (by rw [hc.n]; exact hB c hX hc.n) d5 d6) fun t ⟨_, _, _, har, k⟩ =>
    ⟨h4, h64, c, bb, hc.of_bit (Frm.of_arrays har (by simp)) hr k (by decide), hodd, hc1⟩

/-! ## The pieces -/

theorem bitMul1_ct (M : Mont) : RelCT isa (Two B0) (M.mm aY aY aY) (Two B1) :=
  two_post (two_map id (fun _ _ ⟨_, _, _, _, _, hc, _⟩ => ⟨_, hc.good⟩)
    (M.ct (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))) fun L s ⟨h4, h64, c, b, y, hc, hodd, hc1, hY⟩ =>
    WP.mono (M.mm_ok hc.good.1 hc.good.2 (by omega) (by omega) (o := aY) (a := aY) (b := aY) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.inv
      (by rw [hY, hc.n]; exact Nat.mod_lt _ (by omega))) fun t ⟨_, _, _, har, k⟩ =>
      ⟨h4, h64, c, b, hc.of_bit (Frm.of_arrays har (rs := mulRanges L.w) (by simp [mulRanges])) (mulRanges_sub L.w)
        k (by decide), hodd, hc1⟩

theorem bitCopy_ct : RelCT isa (Two B1) (copyA aXm aR1) (Two B2) := by
  have e : copyA aXm aR1 = .seq (.block (ws ++ (base aR1 .x16 ++ base aXm .x17))) copyWords := by
    simp only [copyA, List.append_assoc]
  rw [e]
  refine ws_ct (fun L : WsP => L.B) (fun L : WsP => L.Z) (fun L : WsP => L.w) (fun _ _ h => ?_) (by taint_decide)
    fun L s h => ?_
  · obtain ⟨-, -, c, b, hc, -⟩ := h; exact hc.ws
  rw [← e]
  obtain ⟨h4, h64, c, b, hc, hodd, hc1⟩ := h
  have hn := hc.ws.scr.nowrap
  have sXm := hc.ws.sl (show aXm < 16 by decide)
  refine WP.mono (copyA_ok hc.ws (o := aXm) (a := aR1) (by decide) (by decide) (by decide))
    fun t ⟨hv, o, _, _, k⟩ => ⟨h4, h64, c, b, hc.of_bit (Frm.of_outside (o.mono (o' := slot L.w aXm)
      (n' := 8 * (L.w + 2)) (Nat.le_refl _) (by omega)) (rs := mulRanges L.w) (by simp [mulRanges]))
      (mulRanges_sub L.w) k (by decide), hodd, hc1, ?_⟩
  rw [hv, hc.r1]; exact Nat.mod_lt _ (by omega)

theorem bitSel_ct : RelCT isa (Two B2) (.block (bitMask ++ ws ++ base aB .x16 ++ base aXm .x17 ++ [mov .x14 .x12]))
    (Two B3) :=
  two_piece [.x0] (pins_ws' (fun L : WsP => L.B) (fun L : WsP => L.Z) (fun L : WsP => L.w)
    fun _ _ ⟨_, _, _, _, hc, _⟩ => hc.ws) (by taint_decide) fun _ s h => by
    obtain ⟨-, -, c, b, hc, -⟩ := id h
    obtain ⟨bt, hbt⟩ := shr63_bit (word s.mem _ (8 * kV))
    exact WP.mono (bitSel_ok hc.ws rfl hbt) fun t ⟨⟨h15, h14, h16, h17, hm⟩, k⟩ => by
      obtain ⟨h4, h64, c, b, hc, hodd, hc1, hX⟩ := h
      exact ⟨⟨h4, h64, c, b, hc.of_bit (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k (by decide),
        hodd, hc1, by rw [hm]; exact hX⟩, h14, h16, h17, bt, h15⟩

theorem selLoop_ct : RelCT isa (Two B3) Crt.selLoop (Two B2) :=
  two_piece [.x14, .x16, .x17] (pins_of _ (fun L r => match r with
      | .x14 => BitVec.ofNat 64 L.w | .x16 => off L.B (slot L.w aB) | _ => off L.B (slot L.w aXm))
    fun _ _ ⟨_, h14, h16, h17, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h14
      · exact h16
      · exact h17) (by taint_decide) fun L s h => by
    obtain ⟨⟨h4, h64, c, b, hc, hodd, hc1, hX⟩, h14, h16, h17, bt, h15⟩ := h
    have hn := hc.ws.scr.nowrap
    have hZ := hc.ws.hZ
    have sXm := hc.ws.sl (show aXm < 16 by decide)
    have sB := hc.ws.sl (show aB < 16 by decide)
    refine WP.mono (selLoop_ok hc.ws.scr h16 h17 h14 h15 (by omega) (by omega) (by omega) (by omega)
      (Or.inl (by simp only [slot, aXm, aB]; omega))) fun t ⟨hv, o, k⟩ =>
      ⟨h4, h64, c, b, hc.of_bit (Frm.of_outside (o.mono (o' := slot L.w aXm) (n' := 8 * (L.w + 2)) (Nat.le_refl _)
        (by omega)) (rs := mulRanges L.w) (by simp [mulRanges])) (mulRanges_sub L.w) k (by decide), hodd, hc1, ?_⟩
    rw [hv]
    split
    · rw [hc.b]; exact Nat.mod_lt _ (by omega)
    · exact hX

theorem bitMul2_ct (M : Mont) : RelCT isa (Two B2) (M.mm aY aY aXm) (Two WsQ) :=
  two_post (two_map id (fun _ _ ⟨_, _, _, _, hc, _⟩ => ⟨_, hc.good⟩)
    (M.ct (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))) fun L s h =>
    WP.mono (b2_mm M h (o := aY) (a := aY) (b := aXm) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (fun _ h _ => h) (by simp [bitRanges]))
      fun _ ⟨_, _, _, _, hc, _⟩ => hc.ws

theorem kG_ct : RelCT isa (Two WsQ) (.block [sth .x15 kG]) (Two WsQ) :=
  two_piece [.x0] pins_wsq (by taint_decide) fun L s h => by
    have hn := h.scr.nowrap
    have h256 := h.h256
    refine WP.mono (WP.keep [] (Q := fun t => t.mem = s.mem.writeW (off L.B (8 * kG)) (s.gpr .x15)) (by
      brun [h.x0, hdr_enc (show kG < 32 by decide), h.scr.st (d := 8 * kG) (by simp only [kG]; omega)])
      (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, k⟩ => ?_
    exact h.congr' (Frm.of_outside (by rw [hm]; exact writeW_outside _ _ _ (by simp only [kG]; omega))
      (List.mem_singleton_self (8 * kG, 8))) (by msb_mut) k (by decide)

/-- `mrExpBit` leaks the same in runs that agree on the working space. -/
theorem mrExpBit_ct (M : Mont) : RelCT isa (Two B0) (seqs (mrExpBit M.mm)) fun _ _ => True := by
  rw [mrExpBit_eq]
  refine ct_app' (by simp) (by simp [eqMask, eqA]) (RelCT.seq (bitMul1_ct M) (RelCT.seq bitCopy_ct
    (RelCT.seq bitSel_ct (RelCT.seq selLoop_ct (bitMul2_ct M))))) ?_
  refine ct_app' (by simp [eqMask, eqA]) (by simp) (eqMask_ct (by decide) (by taint_decide)) ?_
  refine ct_app' (by simp) (by simp [eqMask, eqA]) kG_ct ?_
  exact ct_app' (by simp [eqMask, eqA]) (by simp) (eqMask_ct (by decide) (by taint_decide))
    (two_taint [.x0] pins_wsq (by taint_decide))

end VG.Proof.RsaKeyGen.AArch64
