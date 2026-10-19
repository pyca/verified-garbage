module

public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Sound
import VerifiedGarbage.Proof.MlKem.X86_64.VLay42
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Sym
import VerifiedGarbage.Proof.Framework.X86_64.Words
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# ML-KEM on x86-64: the NTT on registers, each instruction agrees

`step_ok`: an instruction `St.step` follows runs, and its terms hold after
it; `run_ok`: so do a block's.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.NttR

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.NttR

theorem Y.get_ofFn (f : Nat → E) {e : Nat} (he : e < 16) : (Y.ofFn f).get e = f e := by
  simp only [Y.get, Y.ofFn, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range he,
    Option.map_some, Option.getD_some]

/-! ## Words of the permutations -/

theorem extract_perm (y : BitVec 256) (o : BitVec 8) {e : Nat} (he : e < 16) :
    (permQwords y o).extractLsb' (16 * e) 16 = y.extractLsb' (16 * (4 * sel4 o.toNat (e / 4) + e % 4)) 16 := by
  have hq := Proof.Poly1305.X86_64.Avx2.qword256_perm y o (k := e / 4) (by omega)
  have h1 : ∀ x : BitVec 256, x.extractLsb' (16 * e) 16 = (qword256 x (e / 4)).extractLsb' (16 * (e % 4)) 16 := by
    intro x
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    simp only [qword256, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and,
      decide_eq_true (show 16 * (e % 4) + j < 64 by omega)]
    exact congrArg _ (by omega)
  have h2 : ∀ x : BitVec 256, ∀ m < 4,
      (qword256 x m).extractLsb' (16 * (e % 4)) 16 = x.extractLsb' (16 * (4 * m + e % 4)) 16 := by
    intro x m _
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    simp only [qword256, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and,
      decide_eq_true (show 16 * (e % 4) + j < 64 by omega)]
    exact congrArg _ (by omega)
  rw [h1, hq, h2 _ _ (Proof.Poly1305.X86_64.Avx2.sel4_lt _ _)]
  rfl

theorem word_cat (a b : BitVec 64) {i : Nat} (hi : i < 8) :
    word (a ++ b) i = (if i < 4 then b else a).extractLsb' (16 * (i % 4)) 16 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [word, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hj, decide_true, Bool.true_and]
  split
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega : i < 4))]
    exact congrArg _ (by omega)
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega : ¬ i < 4))]
    exact congrArg _ (by omega)

theorem extract16 (x : BitVec 64) (t : Nat) : x.extractLsb' t 16 = BitVec.ofNat 16 (x.toNat / 2 ^ t % 2 ^ 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.mod_mod, Nat.shiftRight_eq_div_pow]

section
variable {L : Nat → Nat → BitVec 16} {O : Nat → BitVec 16}

/-- The words of lane `e / 8` of a register, from its words. -/
theorem lane_word {σ : St} {s : State} (hr : ∀ r e, e < 16 → Hd L O ((σ.reg r).get e) (wd s r e))
    (r : XReg) {e : Nat} (he : e < 16) {j : Nat} (hj : j < 8) :
    Hd L O ((σ.reg r).get (8 * (e / 8) + j)) (word (s.lane r (e / 8)) j) := by
  have := hr r (8 * (e / 8) + j) (by omega)
  rwa [wd, show (8 * (e / 8) + j) / 8 = e / 8 by omega, show (8 * (e / 8) + j) % 8 = j by omega] at this

theorem wd_vbin (op : VBinOp) (d a b : XReg) (s : State) (r : XReg) (e : Nat) :
    wd ((VOp.vbin op .l256 d a b).exec s) r e =
      if r = d then word (op.sse.eval (s.lane a (e / 8)) (s.lane b (e / 8))) (e % 8) else wd s r e := by
  simp only [wd, lane_vbin256]; split <;> rfl

theorem wd_vshift (op : XShiftOp) (d a : XReg) (n : BitVec 8) (s : State) (r : XReg) (e : Nat) :
    wd ((VOp.vshift op .l256 d a n).exec s) r e =
      if r = d then word (op.eval (s.lane a (e / 8)) n) (e % 8) else wd s r e := by
  simp only [wd, lane_vshift256]; split <;> rfl

theorem bin_ok {R : Rules} (hM : Model R L O) {σ : St} {s : State} (hr : ∀ r e, e < 16 → Hd L O ((σ.reg r).get e) (wd s r e))
    {op : VBinOp} {a b : XReg} (hok : binOk op (a == b) = true) {e : Nat} (he : e < 16) :
    Hd L O (binW R op (σ.reg a) (σ.reg b) e) (word (op.sse.eval (s.lane a (e / 8)) (s.lane b (e / 8))) (e % 8)) := by
  have hi : e % 8 < 8 := Nat.mod_lt _ (by decide)
  have hA := fun {j} (hj : j < 8) => lane_word hr a he hj
  have hB := fun {j} (hj : j < 8) => lane_word hr b he hj
  cases op <;> simp only [binOk, Bool.false_eq_true] at hok <;> simp only [binW, VBinOp.sse]
  · rw [word_pxor, show a = b from beq_iff_eq.1 hok, BitVec.xor_self]; exact Hd.of_eq rfl
  · rw [word_pand]
    exact mk2_ok .and (· &&& ·) (fun _ _ => rfl) (hA hi) (hB hi)
  · rw [word_punpckldq _ _ hi]
    split
    · exact hA (by omega)
    · exact hB (by omega)
  · rw [word_punpckhdq _ _ hi]
    split
    · exact hA (by omega)
    · exact hB (by omega)
  · rw [word_punpcklqdq _ _ hi]
    split
    · exact hA hi
    · exact hB (by omega)
  · rw [word_punpckhqdq _ _ hi]
    split
    · exact hA (by omega)
    · exact hB hi
  · rw [word_paddw _ _ hi]; exact mkAdd_ok hM (hA hi) (hB hi)
  · rw [word_psubw _ _ hi]; exact mkSub_ok hM (hA hi) (hB hi)
  · rw [word_pmullw _ _ hi]
    exact mk2_ok .mlo (fun x y => (mulWordsSigned x y).extractLsb' 0 16) (fun _ _ => rfl) (hA hi) (hB hi)
  · rw [word_pmulhw _ _ hi]
    exact mk2_ok .mhi (fun x y => (mulWordsSigned x y).extractLsb' 16 16) (fun _ _ => rfl) (hA hi) (hB hi)
  · rw [word_packssdw _ _ hi]
    by_cases hc : e % 8 < 4
    · simp only [hc, ite_true]
      exact pk_ok hM hc (hA (by omega)) (hA (by omega))
    · simp only [hc, ite_false]
      exact pk_ok hM (by omega) (hB (by omega)) (hB (by omega))
  · rw [word_punpcklwd _ _ hi]
    split
    · exact hA (by omega)
    · exact hB (by omega)
  · rw [word_punpckhwd _ _ hi]
    split
    · exact hA (by omega)
    · exact hB (by omega)

theorem shift_ok {σ : St} {s : State} (hr : ∀ r e, e < 16 → Hd L O ((σ.reg r).get e) (wd s r e))
    {op : XShiftOp} {n : BitVec 8} {a : XReg} (hok : shiftOk op n.toNat = true) {e : Nat} (he : e < 16) :
    Hd L O (shiftW op (σ.reg a) e) (word (op.eval (s.lane a (e / 8)) n) (e % 8)) := by
  have hi : e % 8 < 8 := Nat.mod_lt _ (by decide)
  have hA := fun {j} (hj : j < 8) => lane_word hr a he hj
  cases op <;> simp only [shiftOk, beq_iff_eq, Bool.false_eq_true] at hok <;> simp only [shiftW]
  · have hn : n = 32 := BitVec.eq_of_toNat_eq hok
    subst hn
    rw [word_psllq32 _ hi]
    split
    · rename_i h; rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]; exact Hd.of_eq rfl
    · rename_i h; rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
        show e - 2 = 8 * (e / 8) + (e % 8 - 2) by omega]
      exact hA (by omega)
  · have hn : n = 32 := BitVec.eq_of_toNat_eq hok
    subst hn
    rw [word_psrlq32 _ hi]
    split
    · rename_i h; rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)),
        show e + 2 = 8 * (e / 8) + (e % 8 + 2) by omega]
      exact hA (by omega)
    · rename_i h; rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]; exact Hd.of_eq rfl
  · rw [word_psraw _ _ hi, hok]
    have := hA hi
    rw [show 8 * (e / 8) + e % 8 = e by omega] at this
    exact mkSra_ok this

theorem vop_ok {R : Rules} (hM : Model R L O) {rs : List Rg} {σ σ' : St} {s₀ s : State} (h : Rel rs L O σ s₀ s) {o : VOp}
    (e : σ.vop R o = some σ') : Rel rs L O σ' s₀ (o.exec s) := by
  have hr := h.reg
  unfold St.vop at e
  split at e
  · rename_i op d a b
    split at e <;> [skip; cases e]
    rename_i hok
    cases e
    refine h.setReg (fun e he => ?_) (fun r hr' e _ => by rw [wd_vbin, ite_eq_right_of_eq_false _ _ (eq_false hr')])
      (by simp only [VOp.exec]; rfl) (vm_vop h.eq _ (by intro c; cases c))
    rw [Y.get_ofFn _ he, wd_vbin, ite_eq_left_of_eq_true _ _ (eq_true rfl)]
    exact bin_ok hM hr hok he
  · rename_i op d a n
    split at e <;> [skip; cases e]
    rename_i hok
    cases e
    refine h.setReg (fun e he => ?_) (fun r hr' e _ => by rw [wd_vshift, ite_eq_right_of_eq_false _ _ (eq_false hr')])
      (by simp only [VOp.exec]; rfl) (vm_vop h.eq _ (by intro c; cases c))
    rw [Y.get_ofFn _ he, wd_vshift, ite_eq_left_of_eq_true _ _ (eq_true rfl)]
    exact shift_ok hr hok he
  · -- vpblendd
    rename_i d a b sel
    cases e
    refine h.setReg (fun e he => ?_) (fun r hr' e _ => ?_) (by simp only [VOp.exec]; rfl)
      (vm_vop h.eq _ (by intro c; cases c))
    · rw [Y.get_ofFn _ he]
      simp only [VOp.exec, wd_setV256, ite_true]
      have hl : (if e / 8 = 0 then blendDwords (s.lane a 0) (s.lane b 0) (sel.extractLsb' 0 4)
          else blendDwords (s.lane a 1) (s.lane b 1) (sel.extractLsb' 4 4)) =
          blendDwords (s.lane a (e / 8)) (s.lane b (e / 8)) (sel.extractLsb' (4 * (e / 8)) 4) := by
        by_cases h0 : e / 8 = 0
        · rw [ite_eq_left_of_eq_true _ _ (eq_true h0), h0]
        · rw [ite_eq_right_of_eq_false _ _ (eq_false h0), show e / 8 = 1 by omega]
      rw [hl, word_blend _ _ _ (Nat.mod_lt _ (by decide)), BitVec.getLsbD_extractLsb',
        decide_eq_true (show e % 8 / 2 < 4 by omega), Bool.true_and, ← BitVec.testBit_toNat,
        show 4 * (e / 8) + e % 8 / 2 = e / 2 by omega]
      simp only [blendW]
      split
      · have := lane_word hr b he (j := e % 8) (by omega)
        rwa [show 8 * (e / 8) + e % 8 = e by omega] at this
      · have := lane_word hr a he (j := e % 8) (by omega)
        rwa [show 8 * (e / 8) + e % 8 = e by omega] at this
    · simp only [VOp.exec, wd_setV256, ite_eq_right_of_eq_false _ _ (eq_false hr')]
  · -- vpermq
    rename_i d a o
    cases e
    refine h.setReg (fun e he => ?_) (fun r hr' e _ => ?_) (by simp only [VOp.exec]; rfl)
      (vm_vop h.eq _ (by intro c; cases c))
    · rw [Y.get_ofFn _ he]
      simp only [VOp.exec, wd_setV256, ite_true]
      rw [word_split _ he, extract_perm _ _ he,
        ymm_word _ _ (show 4 * sel4 o.toNat (e / 4) + e % 4 < 16 by
          have := Proof.Poly1305.X86_64.Avx2.sel4_lt o.toNat (e / 4); simp only [sel4] at this ⊢; omega)]
      exact h.reg a _ (by have := Proof.Poly1305.X86_64.Avx2.sel4_lt o.toNat (e / 4); simp only [sel4] at this ⊢; omega)
    · simp only [VOp.exec, wd_setV256, ite_eq_right_of_eq_false _ _ (eq_false hr')]
  · -- vperm2i128
    rename_i d a b sel
    cases e
    refine h.setReg (fun e he => ?_) (fun r hr' e _ => ?_) (by simp only [VOp.exec]; rfl)
      (vm_vop h.eq _ (by intro c; cases c))
    · rw [Y.get_ofFn _ he]
      simp only [VOp.exec, wd_setV256, ite_true]
      have hl : (if e / 8 = 0 then perm2Lanes (s.lane a) (s.lane b) sel 0 else perm2Lanes (s.lane a) (s.lane b) sel 1) =
          perm2Lanes (s.lane a) (s.lane b) sel (e / 8) := by
        by_cases h0 : e / 8 = 0
        · rw [ite_eq_left_of_eq_true _ _ (eq_true h0), h0]
        · rw [ite_eq_right_of_eq_false _ _ (eq_false h0), show e / 8 = 1 by omega]
      rw [hl]
      simp only [perm2Lanes, perm2W, ← BitVec.testBit_toNat]
      have hk : (sel.extractLsb' (4 * (e / 8)) 2).toNat = sel.toNat / 16 ^ (e / 8) % 4 := by
        rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.pow_mul]
      rw [hk]
      split
      · exact Hd.of_eq (by simp [word, E.eval])
      · have hk4 : sel.toNat / 16 ^ (e / 8) % 4 < 4 := Nat.mod_lt _ (by decide)
        split
        · have := h.reg a (8 * (sel.toNat / 16 ^ (e / 8) % 4 % 2) + e % 8) (by omega)
          rwa [wd, show (8 * (sel.toNat / 16 ^ (e / 8) % 4 % 2) + e % 8) / 8 = sel.toNat / 16 ^ (e / 8) % 4 % 2 by omega,
            show (8 * (sel.toNat / 16 ^ (e / 8) % 4 % 2) + e % 8) % 8 = e % 8 by omega] at this
        · have := h.reg b (8 * (sel.toNat / 16 ^ (e / 8) % 4 % 2) + e % 8) (by omega)
          rwa [wd, show (8 * (sel.toNat / 16 ^ (e / 8) % 4 % 2) + e % 8) / 8 = sel.toNat / 16 ^ (e / 8) % 4 % 2 by omega,
            show (8 * (sel.toNat / 16 ^ (e / 8) % 4 % 2) + e % 8) % 8 = e % 8 by omega] at this
    · simp only [VOp.exec, wd_setV256, ite_eq_right_of_eq_false _ _ (eq_false hr')]
  · cases e

end

/-! ## Memory -/

theorem findAux_ok {base : Reg} {d : Nat} : ∀ (rs : List Rg) (k0 : Nat) {k j : Nat}, findAux base d rs k0 = some (k, j) →
    k0 ≤ k ∧ k - k0 < rs.length ∧ (rs.getD (k - k0) default).1 = base ∧
      (rs.getD (k - k0) default).2.1 + 2 * j = d ∧ j + 16 ≤ (rs.getD (k - k0) default).2.2.1 ∧ j % 16 = 0
  | [], _, _, _, h => by cases h
  | r :: rs, k0, k, j, h => by
    unfold findAux at h
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
      simp only [Nat.sub_self, List.getD_cons_zero, List.length_cons]
      exact ⟨Nat.le_refl _, by omega, h1, by omega, h4, by omega⟩
    · obtain ⟨a, b, c, e, f, g⟩ := findAux_ok rs (k0 + 1) h
      have hk : k - k0 = (k - (k0 + 1)) + 1 := by omega
      rw [hk, List.getD_cons_succ]
      exact ⟨by omega, by simp only [List.length_cons]; omega, c, e, f, g⟩

theorem ea_of {m : MemOp} (hi : m.index = none) (h0 : 0 ≤ m.disp) (s : State) :
    s.ea m = s.gpr m.base + BitVec.ofNat 64 m.disp.toNat := by
  unfold State.ea
  rw [hi]
  simp only
  congr 1
  conv => lhs; rw [← Int.toNat_of_nonneg h0]
  exact BitVec.ofInt_natCast _ _

theorem find_ok {rs : List Rg} {m : MemOp} {k j : Nat} (h : find rs m = some (k, j)) :
    k < rs.length ∧ j + 16 ≤ rlen rs k ∧ j % 16 = 0 ∧ ∀ s : State, s.ea m = s.gpr (rs.getD k default).1 +
      BitVec.ofNat 64 (rs.getD k default).2.1 + BitVec.ofNat 64 (2 * j) := by
  unfold find at h
  split at h
  · rename_i hc
    obtain ⟨hi, h0, h32⟩ := hc
    obtain ⟨-, hk, hb, hd, hj, h16⟩ := findAux_ok rs 0 h
    simp only [Nat.sub_zero] at hk hb hd hj
    refine ⟨hk, hj, h16, fun s => ?_⟩
    rw [ea_of hi h0, hb, BitVec.add_assoc, ← BitVec.ofNat_add, hd]
  · cases h

theorem inR_sub {wr : List Region} {B : Addr} {n j : Nat} (h : InRegions wr B (2 * n)) (hj : j + 16 ≤ n) :
    InRegions wr (B + BitVec.ofNat 64 (2 * j)) 32 := by
  obtain ⟨R, hR, hc⟩ := h
  refine ⟨R, hR, ?_⟩
  unfold Region.Contains at *
  have e : B + BitVec.ofNat 64 (2 * j) - R.base = (B - R.base) + BitVec.ofNat 64 (2 * j) := by
    rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 (2 * j)),
      ← BitVec.add_assoc]
  rw [e, BitVec.toNat_add]
  have := Nat.mod_le ((B - R.base).toNat + (BitVec.ofNat 64 (2 * j)).toNat) (2 ^ 64)
  have := Nat.mod_le (2 * j) (2 ^ 64)
  rw [BitVec.toNat_ofNat] at *
  omega

theorem sep_sub {a b : Addr} {n k : Nat} (h : Mem.Sep a n b k) {i c j d : Nat} (hi : i + c ≤ n) (hj : j + d ≤ k)
    (hn : n ≤ 2 ^ 64) (hk : k ≤ 2 ^ 64) : Mem.Sep (a + BitVec.ofNat 64 i) c (b + BitVec.ofNat 64 j) d := by
  intro x h1 h2
  rw [Offset.lt_iff x a (by omega)] at h1
  rw [Offset.lt_iff x b (by omega)] at h2
  exact h x (by omega) (by omega)

theorem wordAt_in (m : Mem) (B : Addr) {j i : Nat} (v : BitVec 256) (h1 : j ≤ i) (h2 : i < j + 16) :
    wordAt (m.writeW (B + BitVec.ofNat 64 (2 * j)) v) B i = v.extractLsb' (16 * (i - j)) 16 := by
  unfold wordAt wAddr
  rw [show B + BitVec.ofNat 64 (2 * i) = B + BitVec.ofNat 64 (2 * j) + BitVec.ofNat 64 (2 * (i - j)) by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega]
  have := readW_writeW_inside m (B + BitVec.ofNat 64 (2 * j)) v (k := 2 * (i - j)) (n := 2) (by omega) (by decide)
  rw [show 8 * (2 * (i - j)) = 16 * (i - j) by omega] at this
  exact this

theorem wordAt_out (m : Mem) (B a : Addr) {i : Nat} (v : BitVec 256) (h : Mem.Sep (B + BitVec.ofNat 64 (2 * i)) 2 a 32) :
    wordAt (m.writeW a v) B i = wordAt m B i :=
  Mem.readW_writeW_sep (w := 16) (w' := 256) h (by decide)

theorem getD_set_mem {α : Type} (l : List (List α)) (k k' : Nat) (v : List α) (hk : k < l.length) :
    (l.set k v).getD k' [] = if k' = k then v else l.getD k' [] := by
  by_cases h : k' = k
  · subst h; simp [List.getD_eq_getElem?_getD, hk]
  · simp [List.getD_eq_getElem?_getD, Ne.symm h, h]

section
variable {L : Nat → Nat → BitVec 16} {O : Nat → BitVec 16}

theorem load_ok {rs : List Rg} {σ : St} {s₀ s : State} (hc : Ctx rs s₀) (h : Rel rs L O σ s₀ s) {d : XReg}
    {m : MemOp} {k j : Nat} (hf : find rs m = some (k, j)) :
    ∃ s', exec (.vmovdquLoad .l256 d m) s = some s' ∧
      Rel rs L O (σ.set d ((σ.mem.getD k []).getD (j / 16) [])) s₀ s' := by
  obtain ⟨hk, hj, h16, hea⟩ := find_ok hf
  have ea : s.ea m = rbase rs s₀ k + BitVec.ofNat 64 (2 * j) := by rw [hea, h.gpr]; rfl
  have hin : InRegions (s.rd ++ s.wr) (s.ea m) 32 := by
    rw [ea, h.wr, h.rd]
    exact inR_sub (hc.rd k hk) hj
  refine ⟨_, by simp only [exec, State.load256, hin, ite_true, Option.map_some]; rfl, ?_⟩
  refine h.setReg (fun e he => ?_) (fun r hr e _ => by rw [wd_setV256, ite_eq_right_of_eq_false _ _ (eq_false hr)])
    (by rfl) (vm_setV h.eq _ _ _ _)
  rw [wd_setV256, ite_eq_left_of_eq_true _ _ (eq_true rfl), word_split _ he,
    show BitVec.extractLsb' (16 * e) 16 (s.mem.readW (s.ea m) 256) =
      s.mem.readW (s.ea m + BitVec.ofNat 64 (2 * e)) 16 by
        have := readW_extract (k := 2 * e) (n := 2) s.mem (s.ea m) (w := 256) (by omega)
        rwa [show 8 * (2 * e) = 16 * e by omega] at this]
  have hm := h.mem k (j + e) hk (by unfold rlen at hj ⊢; omega)
  rw [show (j + e) / 16 = j / 16 by omega, show (j + e) % 16 = e by omega] at hm
  unfold wordAt wAddr at hm
  rwa [ea, BitVec.add_assoc, ← BitVec.ofNat_add, show 2 * j + 2 * e = 2 * (j + e) by omega]

theorem store_ok {rs : List Rg} {σ : St} {s₀ s : State} (hc : Ctx rs s₀) (h : Rel rs L O σ s₀ s) {r : XReg}
    {m : MemOp} {k j : Nat} (hf : find rs m = some (k, j)) (hw : (rs.getD k default).2.2.2 = true)
    (hl : j / 16 < (σ.mem.getD k []).length) :
    ∃ s', exec (.vmovdquStore .l256 m r) s = some s' ∧
      Rel rs L O { σ with mem := σ.mem.set k ((σ.mem.getD k []).set (j / 16) (σ.reg r)) } s₀ s' := by
  obtain ⟨hk, hj, h16, hea⟩ := find_ok hf
  have ea : s.ea m = rbase rs s₀ k + BitVec.ofNat 64 (2 * j) := by rw [hea, h.gpr]; rfl
  have hin : InRegions s.wr (s.ea m) 32 := by rw [ea, h.wr]; exact inR_sub (hc.wr k hk hw) hj
  refine ⟨_, by simp only [exec, State.store256, hin, ite_true]; rfl, ?_⟩
  have hsh := hc.short
  refine ⟨fun r' e he => ?_, fun k' i hk' hi => ?_, ?_, ?_, ?_⟩
  · exact h.reg r' e he
  · simp only [ea]
    rw [getD_set_mem _ _ _ _ (by rw [h.len.1]; exact hk)]
    split
    · rename_i hkk; rw [hkk] at hi ⊢
      rw [getD_set_mem _ _ _ _ hl]
      split
      · rename_i hji
        rw [wordAt_in _ _ _ (by omega) (by omega), ymm_word _ _ (by omega), show i % 16 = i - j by omega]
        exact h.reg r (i - j) (by omega)
      · rename_i hji
        rw [wordAt_out]
        · exact h.mem k i hk hi
        · have := (hsh k hk).1
          unfold rbase
          exact Offset.sep _ (by omega) (by omega) (by omega)
    · rename_i hkk
      rw [wordAt_out]
      · exact h.mem k' i hk' hi
      · have h1 := (hsh k hk).1; have h2 := (hsh k' hk').1
        have hs := hc.sep k' k hk' hk hkk
        have := sep_sub hs (i := 2 * i) (c := 2) (j := 2 * j) (d := 32) (by omega) (by omega)
          (by omega) (by omega)
        exact this
  · rw [← h.eq]; rfl
  · exact ⟨by simp only [List.length_set, h.len.1], h.len.2⟩
  · intro x hx
    simp only [ea, Mem.writeW]
    rw [Mem.write_apply]
    · exact h.fr x hx
    · intro hlt
      have hb := (hsh k hk).1
      have := hx k hk hw
      rw [Offset.lt_iff x _ (by omega)] at hlt
      unfold rlen at hj this
      omega

end

section
variable {L : Nat → Nat → BitVec 16} {O : Nat → BitVec 16}

theorem tbl_ok {rs : List Rg} {σ : St} {s₀ s : State} (hc : Ctx rs s₀) (h : Rel rs L O σ s₀ s) {d : XReg}
    {m : MemOp} {ws : List (BitVec 64)} (hb : m.base = .r8) (hi : m.index = none) (h0 : 0 ≤ m.disp)
    (h8 : m.disp.toNat % 8 = 0) (hl : m.disp.toNat / 8 + 4 ≤ ws.length) (h32 : m.disp.toNat < 2 ^ 32) :
    ∃ s', exec (.vmovdquTbl d m tblName ws) s = some s' ∧
      Rel rs L O (σ.set d (Y.ofFn fun e => tblW ws (m.disp.toNat / 8 + e / 4) (e % 4))) s₀ s' := by
  have hoff : (s.ea m - s.gpr m.base).toNat = m.disp.toNat := by
    rw [ea_of hi h0, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hr8 : s.gpr m.base = s.syms tblName := by rw [hb, h.gpr, h.syms, hc.r8]
  have hoff' : (s.ea m - s.syms tblName).toNat = m.disp.toNat := by rw [← hr8]; exact hoff
  refine ⟨_, by simp only [exec, hr8, hoff', h8, hl, and_self, ite_true]; rfl, ?_⟩
  refine h.setReg (fun e he => ?_) (fun r hr e _ => by rw [wd_setV256, ite_eq_right_of_eq_false _ _ (eq_false hr)])
    (by rfl) (vm_setV h.eq _ _ _ _)
  rw [Y.get_ofFn _ he, wd_setV256, ite_eq_left_of_eq_true _ _ (eq_true rfl)]
  refine Hd.of_eq ?_
  simp only [tblW, E.eval]
  have hl8 : e % 8 < 8 := Nat.mod_lt _ (by decide)
  by_cases h0' : e / 8 = 0
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h0'), word_cat _ _ hl8, extract16, show e % 8 % 4 = e % 4 by omega]
    by_cases h4 : e % 8 < 4
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h4), show e / 4 = 0 by omega]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h4), show e / 4 = 1 by omega]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h0'), word_cat _ _ hl8, extract16, show e % 8 % 4 = e % 4 by omega]
    by_cases h4 : e % 8 < 4
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h4), show e / 4 = 2 by omega]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h4), show e / 4 = 3 by omega]

theorem step_ok {R : Rules} (hM : Model R L O) {rs : List Rg} {σ σ' : St} {s₀ s : State} (hc : Ctx rs s₀) (h : Rel rs L O σ s₀ s)
    {i : Instr} (e : σ.step R rs i = some σ') : ∃ s', exec i s = some s' ∧ Rel rs L O σ' s₀ s' := by
  unfold St.step at e
  split at e
  · rename_i o; exact ⟨_, rfl, vop_ok hM h e⟩
  · rename_i d m name ws
    split at e <;> [skip; cases e]
    rename_i hcond
    obtain ⟨hb, hi, hn, h0, h8, hl, h32⟩ := hcond
    cases e; subst hn
    exact tbl_ok hc h hb hi h0 h8 hl h32
  · rename_i d m
    obtain ⟨⟨k, j⟩, hf, rfl⟩ := Option.map_eq_some_iff.1 e
    exact load_ok hc h hf
  · rename_i m r
    obtain ⟨⟨k, j⟩, hf, e⟩ := Option.bind_eq_some_iff.1 e
    dsimp only at e
    split at e <;> [skip; cases e]
    rename_i hw
    cases e
    exact store_ok hc h hf hw.1 hw.2
  · cases e

theorem run_ok {R : Rules} (hM : Model R L O) {rs : List Rg} {s₀ : State} (hc : Ctx rs s₀) :
    ∀ (is : List Instr) {σ σ' : St} {s : State}, Rel rs L O σ s₀ s → σ.run R rs is = some σ' →
      WP isa (.block is) s (Rel rs L O σ' s₀)
  | [], _, _, _, h, e => by cases e; exact WP.block_nil h
  | i :: is, _, _, _, h, e => by
    simp only [St.run, Option.bind_eq_some_iff] at e
    obtain ⟨σ₁, e₁, e₂⟩ := e
    obtain ⟨s₁, hx, h₁⟩ := step_ok hM hc h e₁
    exact WP.block_cons_iff.2 ⟨s₁, hx, run_ok hM hc is h₁ e₂⟩

end

end VG.Proof.MlKem.X86_64.NttR
