module

public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Run
public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Sound
import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.MlKem.X86_64.YNtt
import VerifiedGarbage.Proof.MlKem.X86_64.VPack
import VerifiedGarbage.Proof.MlKem.X86_64.Ntt
public import VerifiedGarbage.Proof.MlKem.Blocks
public import VerifiedGarbage.Proof.MlKem.X86_64.VLay
import VerifiedGarbage.Proof.MlKem.X86_64.VLay42
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Sym
import VerifiedGarbage.Proof.Framework.X86_64.Avx

/-! ### `MlKem.X86_64.NttR.Step`, which this module and modules that import it used -/

section

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
  have hq := Proof.Poly1305.X86_64.Avx2.qword256_perm y o (k := e / 4) (by omega_arith)
  have h1 : ∀ x : BitVec 256, x.extractLsb' (16 * e) 16 = (qword256 x (e / 4)).extractLsb' (16 * (e % 4)) 16 := by
    intro x
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    simp only [qword256, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and,
      decide_eq_true (show 16 * (e % 4) + j < 64 by omega_arith)]
    exact congrArg _ (by omega_arith)
  have h2 : ∀ x : BitVec 256, ∀ m < 4,
      (qword256 x m).extractLsb' (16 * (e % 4)) 16 = x.extractLsb' (16 * (4 * m + e % 4)) 16 := by
    intro x m _
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    simp only [qword256, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and,
      decide_eq_true (show 16 * (e % 4) + j < 64 by omega_arith)]
    exact congrArg _ (by omega_arith)
  rw [h1, hq, h2 _ _ (Proof.Poly1305.X86_64.Avx2.sel4_lt _ _)]
  rfl

theorem word_cat (a b : BitVec 64) {i : Nat} (hi : i < 8) :
    word (a ++ b) i = (if i < 4 then b else a).extractLsb' (16 * (i % 4)) 16 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [word, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hj, decide_true, Bool.true_and]
  split
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega_arith : i < 4))]
    exact congrArg _ (by omega_arith)
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith : ¬ i < 4))]
    exact congrArg _ (by omega_arith)

theorem extract16 (x : BitVec 64) (t : Nat) : x.extractLsb' t 16 = BitVec.ofNat 16 (x.toNat / 2 ^ t % 2 ^ 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.mod_mod, Nat.shiftRight_eq_div_pow]

section
variable {L : Nat → Nat → BitVec 16} {O : Nat → BitVec 16}

/-- The words of lane `e / 8` of a register, from its words. -/
theorem lane_word {σ : St} {s : State} (hr : ∀ r e, e < 16 → Hd L O ((σ.reg r).get e) (wd s r e))
    (r : XReg) {e : Nat} (he : e < 16) {j : Nat} (hj : j < 8) :
    Hd L O ((σ.reg r).get (8 * (e / 8) + j)) (word (s.lane r (e / 8)) j) := by
  have := hr r (8 * (e / 8) + j) (by omega_arith)
  rwa [wd, show (8 * (e / 8) + j) / 8 = e / 8 by omega_arith, show (8 * (e / 8) + j) % 8 = j by omega_arith] at this

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
    · exact hA (by omega_arith)
    · exact hB (by omega_arith)
  · rw [word_punpckhdq _ _ hi]
    split
    · exact hA (by omega_arith)
    · exact hB (by omega_arith)
  · rw [word_punpcklqdq _ _ hi]
    split
    · exact hA hi
    · exact hB (by omega_arith)
  · rw [word_punpckhqdq _ _ hi]
    split
    · exact hA (by omega_arith)
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
      exact pk_ok hM hc (hA (by omega_arith)) (hA (by omega_arith))
    · simp only [hc, ite_false]
      exact pk_ok hM (by omega_arith) (hB (by omega_arith)) (hB (by omega_arith))
  · rw [word_punpcklwd _ _ hi]
    split
    · exact hA (by omega_arith)
    · exact hB (by omega_arith)
  · rw [word_punpckhwd _ _ hi]
    split
    · exact hA (by omega_arith)
    · exact hB (by omega_arith)

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
    · rename_i h; rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega_arith))]; exact Hd.of_eq rfl
    · rename_i h; rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith)),
        show e - 2 = 8 * (e / 8) + (e % 8 - 2) by omega_arith]
      exact hA (by omega_arith)
  · have hn : n = 32 := BitVec.eq_of_toNat_eq hok
    subst hn
    rw [word_psrlq32 _ hi]
    split
    · rename_i h; rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega_arith)),
        show e + 2 = 8 * (e / 8) + (e % 8 + 2) by omega_arith]
      exact hA (by omega_arith)
    · rename_i h; rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith))]; exact Hd.of_eq rfl
  · rw [word_psraw _ _ hi, hok]
    have := hA hi
    rw [show 8 * (e / 8) + e % 8 = e by omega_arith] at this
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
        · rw [ite_eq_right_of_eq_false _ _ (eq_false h0), show e / 8 = 1 by omega_arith]
      rw [hl, word_blend _ _ _ (Nat.mod_lt _ (by decide)), BitVec.getLsbD_extractLsb',
        decide_eq_true (show e % 8 / 2 < 4 by omega_arith), Bool.true_and, ← BitVec.testBit_toNat,
        show 4 * (e / 8) + e % 8 / 2 = e / 2 by omega_arith]
      simp only [blendW]
      split
      · have := lane_word hr b he (j := e % 8) (by omega_arith)
        rwa [show 8 * (e / 8) + e % 8 = e by omega_arith] at this
      · have := lane_word hr a he (j := e % 8) (by omega_arith)
        rwa [show 8 * (e / 8) + e % 8 = e by omega_arith] at this
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
          have := Proof.Poly1305.X86_64.Avx2.sel4_lt o.toNat (e / 4); simp only [sel4] at this ⊢; omega_arith)]
      exact h.reg a _ (by have := Proof.Poly1305.X86_64.Avx2.sel4_lt o.toNat (e / 4); simp only [sel4] at this ⊢; omega_arith)
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
        · rw [ite_eq_right_of_eq_false _ _ (eq_false h0), show e / 8 = 1 by omega_arith]
      rw [hl]
      simp only [perm2Lanes, perm2W, ← BitVec.testBit_toNat]
      have hk : (sel.extractLsb' (4 * (e / 8)) 2).toNat = sel.toNat / 16 ^ (e / 8) % 4 := by
        rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.pow_mul]
      rw [hk]
      split
      · exact Hd.of_eq (by simp [word, E.eval])
      · have hk4 : sel.toNat / 16 ^ (e / 8) % 4 < 4 := Nat.mod_lt _ (by decide)
        split
        · have := h.reg a (8 * (sel.toNat / 16 ^ (e / 8) % 4 % 2) + e % 8) (by omega_arith)
          rwa [wd, show (8 * (sel.toNat / 16 ^ (e / 8) % 4 % 2) + e % 8) / 8 = sel.toNat / 16 ^ (e / 8) % 4 % 2 by omega_arith,
            show (8 * (sel.toNat / 16 ^ (e / 8) % 4 % 2) + e % 8) % 8 = e % 8 by omega_arith] at this
        · have := h.reg b (8 * (sel.toNat / 16 ^ (e / 8) % 4 % 2) + e % 8) (by omega_arith)
          rwa [wd, show (8 * (sel.toNat / 16 ^ (e / 8) % 4 % 2) + e % 8) / 8 = sel.toNat / 16 ^ (e / 8) % 4 % 2 by omega_arith,
            show (8 * (sel.toNat / 16 ^ (e / 8) % 4 % 2) + e % 8) % 8 = e % 8 by omega_arith] at this
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
      exact ⟨Nat.le_refl _, by omega_arith, h1, by omega_arith, h4, by omega_arith⟩
    · obtain ⟨a, b, c, e, f, g⟩ := findAux_ok rs (k0 + 1) h
      have hk : k - k0 = (k - (k0 + 1)) + 1 := by omega_arith
      rw [hk, List.getD_cons_succ]
      exact ⟨by omega_arith, by simp only [List.length_cons]; omega_arith, c, e, f, g⟩

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
  omega_arith

theorem sep_sub {a b : Addr} {n k : Nat} (h : Mem.Sep a n b k) {i c j d : Nat} (hi : i + c ≤ n) (hj : j + d ≤ k)
    (hn : n ≤ 2 ^ 64) (hk : k ≤ 2 ^ 64) : Mem.Sep (a + BitVec.ofNat 64 i) c (b + BitVec.ofNat 64 j) d := by
  intro x h1 h2
  rw [Offset.lt_iff x a (by omega_arith)] at h1
  rw [Offset.lt_iff x b (by omega_arith)] at h2
  exact h x (by omega_arith) (by omega_arith)

theorem wordAt_in (m : Mem) (B : Addr) {j i : Nat} (v : BitVec 256) (h1 : j ≤ i) (h2 : i < j + 16) :
    wordAt (m.writeW (B + BitVec.ofNat 64 (2 * j)) v) B i = v.extractLsb' (16 * (i - j)) 16 := by
  unfold wordAt wAddr
  rw [show B + BitVec.ofNat 64 (2 * i) = B + BitVec.ofNat 64 (2 * j) + BitVec.ofNat 64 (2 * (i - j)) by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega_arith]
  have := readW_writeW_inside m (B + BitVec.ofNat 64 (2 * j)) v (k := 2 * (i - j)) (n := 2) (by omega_arith) (by decide)
  rw [show 8 * (2 * (i - j)) = 16 * (i - j) by omega_arith] at this
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
        have := readW_extract (k := 2 * e) (n := 2) s.mem (s.ea m) (w := 256) (by omega_arith)
        rwa [show 8 * (2 * e) = 16 * e by omega_arith] at this]
  have hm := h.mem k (j + e) hk (by unfold rlen at hj ⊢; omega_arith)
  rw [show (j + e) / 16 = j / 16 by omega_arith, show (j + e) % 16 = e by omega_arith] at hm
  unfold wordAt wAddr at hm
  rwa [ea, BitVec.add_assoc, ← BitVec.ofNat_add, show 2 * j + 2 * e = 2 * (j + e) by omega_arith]

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
        rw [wordAt_in _ _ _ (by omega_arith) (by omega_arith), ymm_word _ _ (by omega_arith), show i % 16 = i - j by omega_arith]
        exact h.reg r (i - j) (by omega_arith)
      · rename_i hji
        rw [wordAt_out]
        · exact h.mem k i hk hi
        · have := (hsh k hk).1
          unfold rbase
          exact Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)
    · rename_i hkk
      rw [wordAt_out]
      · exact h.mem k' i hk' hi
      · have h1 := (hsh k hk).1; have h2 := (hsh k' hk').1
        have hs := hc.sep k' k hk' hk hkk
        have := sep_sub hs (i := 2 * i) (c := 2) (j := 2 * j) (d := 32) (by omega_arith) (by omega_arith)
          (by omega_arith) (by omega_arith)
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
      rw [Offset.lt_iff x _ (by omega_arith)] at hlt
      unfold rlen at hj this
      omega_arith

end

section
variable {L : Nat → Nat → BitVec 16} {O : Nat → BitVec 16}

theorem tbl_ok {rs : List Rg} {σ : St} {s₀ s : State} (hc : Ctx rs s₀) (h : Rel rs L O σ s₀ s) {d : XReg}
    {m : MemOp} {ws : List (BitVec 64)} (hb : m.base = .r8) (hi : m.index = none) (h0 : 0 ≤ m.disp)
    (h8 : m.disp.toNat % 8 = 0) (hl : m.disp.toNat / 8 + 4 ≤ ws.length) (h32 : m.disp.toNat < 2 ^ 32) :
    ∃ s', exec (.vmovdquTbl d m tblName ws) s = some s' ∧
      Rel rs L O (σ.set d (Y.ofFn fun e => tblW ws (m.disp.toNat / 8 + e / 4) (e % 4))) s₀ s' := by
  have hoff : (s.ea m - s.gpr m.base).toNat = m.disp.toNat := by
    rw [ea_of hi h0, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
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
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h0'), word_cat _ _ hl8, extract16, show e % 8 % 4 = e % 4 by omega_arith]
    by_cases h4 : e % 8 < 4
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h4), show e / 4 = 0 by omega_arith]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h4), show e / 4 = 1 by omega_arith]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h0'), word_cat _ _ hl8, extract16, show e % 8 % 4 = e % 4 by omega_arith]
    by_cases h4 : e % 8 < 4
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h4), show e / 4 = 2 by omega_arith]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h4), show e / 4 = 3 by omega_arith]

/-- The words of four quadwords of a table, found once (`St.step`), are those
read from the table. -/
theorem tbl4_eq {ws : List (BitVec 64)} {k : Nat} {a b c d : BitVec 64} {t : List (BitVec 64)}
    (h : ws.drop k = a :: b :: c :: d :: t) :
    (Y.ofFn fun e => tblW [a, b, c, d] (e / 4) (e % 4)) = Y.ofFn fun e => tblW ws (k + e / 4) (e % 4) := by
  refine List.map_congr_left fun e he => ?_
  have he' : e / 4 < 4 := by have := List.mem_range.mp he; omega_arith
  have hg : ws.getD (k + e / 4) 0 = [a, b, c, d].getD (e / 4) 0 := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, ← List.getElem?_drop, h]
    match e / 4, he' with
    | 0, _ | 1, _ | 2, _ | 3, _ => rfl
  simp only [tblW, hg]

theorem step_ok {R : Rules} (hM : Model R L O) {rs : List Rg} {σ σ' : St} {s₀ s : State} (hc : Ctx rs s₀) (h : Rel rs L O σ s₀ s)
    {i : Instr} (e : σ.step R rs i = some σ') : ∃ s', exec i s = some s' ∧ Rel rs L O σ' s₀ s' := by
  unfold St.step at e
  split at e
  · rename_i o; exact ⟨_, rfl, vop_ok hM h e⟩
  · rename_i d m name ws
    split at e <;> [skip; cases e]
    rename_i hcond
    obtain ⟨hb, hi, hn, h0, h8, hl, h32⟩ := hcond
    split at e <;> [skip; cases e]
    rename_i hd
    cases e; subst hn
    rw [tbl4_eq hd]
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

end

end

/-! ### `MlKem.X86_64.NttR.Model`, which this module and modules that import it used -/

section

/-! ### `MlKem.X86_64.NttLazy`, which this module and modules that import it used -/

section

/-! ### `MlKem.X86_64.Lazy`, which this module and modules that import it used -/

section

/-!
# ML-KEM on x86-64: the layers of the NTT and its inverse on lazily reduced words

The butterflies of the lazy layers do exactly what `fwdW` and `invW` do to
the words, and those words are only congruent to the coefficients modulo `q`,
within a bound (`Rep`). Each butterfly is a step of a block of words
(`wBlockN`, which `BlkOk`, as the specification's blocks do), and a layer of
blocks of these butterflies keeps the congruence with the specification's
layer, its bound growing by `q` for `NTT` (`fwdW_rep`) and doubling for
`NTT⁻¹` (`invW_rep`), coefficient by coefficient (`layF_rep`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG.Spec.MlKem
open W (montW caddW)

/-- 256 words. -/
abbrev WPoly := Vector (BitVec 16) n

/-- The word of the zeta `ζ`, `ζ · 2¹⁶ mod q`, as the table of zetas holds it. -/
def zw (ζ : Zq) : BitVec 16 := BitVec.ofNat 16 (ζ.val * 65536 % 3329)

/-- The butterfly of the lazy layers of `NTT` on words. -/
def fwdW (a b : BitVec 16) (ζ : Zq) : BitVec 16 × BitVec 16 := (a + montW b (zw ζ), a - montW b (zw ζ))

/-- The butterfly of the lazy layers of `NTT⁻¹` on words. -/
def invW (a b : BitVec 16) (ζ : Zq) : BitVec 16 × BitVec 16 := (a + b, montW (b - a) (zw ζ))

/-- `2¹⁶ mod q`: `montW d rW ≡ d (mod q)`. -/
def rW : BitVec 16 := 2285

/-! ## Words congruent to coefficients -/

/-- The word `w` is congruent to `v` modulo `q`, and less than `b · q` in
magnitude. -/
def Rep (b : Nat) (w : BitVec 16) (v : Zq) : Prop :=
  -((b : Int) * 3329) < w.toInt ∧ w.toInt < (b : Int) * 3329 ∧ (w.toInt - (v.val : Int)) % 3329 = 0

theorem Rep.mono {b b' : Nat} {w : BitVec 16} {v : Zq} (h : Rep b w v) (hb : b ≤ b') : Rep b' w v := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨by have : (b : Int) ≤ b' := Int.ofNat_le.mpr hb; omega_arith, by have : (b : Int) ≤ b' := Int.ofNat_le.mpr hb; omega_arith, h3⟩

/-- A canonical word represents its value. -/
theorem Rep.of_can {w : BitVec 16} {v : Zq} (h : w.toNat = v.val) : Rep 1 w v := by
  have hv := val_lt v
  have hi := W.toInt_of_lt (a := w) (by rw [h]; exact hv)
  rw [h] at hi
  refine ⟨by rw [hi]; omega_arith, by rw [hi]; omega_arith, by rw [hi, Int.sub_self]; rfl⟩

theorem zw_toNat (ζ : Zq) : (zw ζ).toNat = ζ.val * 65536 % 3329 := by
  rw [zw, BitVec.toNat_ofNat]
  have : ζ.val * 65536 % 3329 < 3329 := Nat.mod_lt _ (by decide)
  omega_arith

theorem zw_toInt (ζ : Zq) : (zw ζ).toInt = (ζ.val : Int) * 65536 % 3329 := by
  rw [W.toInt_of_lt (by rw [zw_toNat]; exact Nat.mod_lt _ (by decide)), zw_toNat]
  omega_arith

/-- `montW d (zw ζ)` represents `ζ · y` for any word `d ≡ y (mod q)`. -/
theorem mont_rep {d : BitVec 16} {y : Zq} (ζ : Zq) (h : (d.toInt - (y.val : Int)) % 3329 = 0) :
    Rep 1 (montW d (zw ζ)) (ζ * y) := by
  have hz := zw_toInt ζ
  have hz1 : 0 ≤ (zw ζ).toInt := by rw [hz]; omega_arith
  have hz2 : (zw ζ).toInt < 3329 := by rw [hz]; omega_arith
  have hd := W.toInt16_bounds d
  have hn : (d.toInt * (zw ζ).toInt).natAbs ≤ 32768 * 3328 := by
    rw [Int.natAbs_mul]; exact Nat.mul_le_mul (by omega_arith) (by omega_arith)
  have h1 := Int.le_natAbs (a := d.toInt * (zw ζ).toInt)
  have h2 := Int.le_natAbs (a := -(d.toInt * (zw ζ).toInt))
  rw [Int.natAbs_neg] at h2
  obtain ⟨m1, m2, m3⟩ := W.montW_spec (d := d) (z := zw ζ) (by omega_arith) (by omega_arith)
  have hm := W.mul_zm (ζ := (ζ.val : Int)) h hz
  have hc := W.cancel_R m3 hm
  have e1 : ((ζ * y).val : Int) = ((y.val : Int) * ζ.val) % 3329 := by
    rw [val_mul, Nat.mul_comm, Int.natCast_emod, Int.natCast_mul]; rfl
  refine ⟨by omega_using [m1], by omega_using [m2], ?_⟩
  rw [e1]
  generalize (montW d (zw ζ)).toInt = M at hc ⊢
  generalize (y.val : Int) * (ζ.val : Int) = P at hc ⊢
  omega_using [hc]

/-- `montW d rW` represents `v` for any word `d ≡ v (mod q)`. -/
theorem red_rep {d : BitVec 16} {v : Zq} (h : (d.toInt - (v.val : Int)) % 3329 = 0) : Rep 1 (montW d rW) v := by
  have hc : rW.toInt = 2285 := by decide
  have hd := W.toInt16_bounds d
  have hn : (d.toInt * rW.toInt).natAbs ≤ 32768 * 2285 := by
    rw [Int.natAbs_mul, hc]; exact Nat.mul_le_mul (by omega_arith) (by decide)
  have h1 := Int.le_natAbs (a := d.toInt * rW.toInt)
  have h2 := Int.le_natAbs (a := -(d.toInt * rW.toInt))
  rw [Int.natAbs_neg] at h2
  obtain ⟨m1, m2, m3⟩ := W.montW_spec (d := d) (z := rW) (by omega_arith) (by omega_arith)
  rw [hc] at m3
  have e := W.cancel_R (Y := (v.val : Int)) m3 (by omega_using [h])
  refine ⟨by omega_using [m1], by omega_using [m2], ?_⟩
  omega_using [e]

/-- A word in `(-q, q)` congruent to `v`, made canonical by `caddW`. -/
theorem cadd_rep {d : BitVec 16} {v : Zq} (h : Rep 1 d v) : (caddW d).toNat = v.val := by
  obtain ⟨h1, h2, h3⟩ := h
  have c := W.caddW_spec (d := d) (by omega_using [h1]) (by omega_using [h2])
  have hv := val_lt v
  have n := W.toNat_of_toInt (a := caddW d) (by rw [c]; exact Int.emod_nonneg _ (by decide))
  rw [c] at n
  omega_using [n, h3, hv]

/-- The lazy butterfly of `NTT`: the bound grows by `q`. -/
theorem fwdW_rep {k : Nat} (hk : (k + 1) * 3329 ≤ 32768) {a b : BitVec 16} {x y : Zq} (ζ : Zq)
    (ha : Rep k a x) (hb : (b.toInt - (y.val : Int)) % 3329 = 0) :
    Rep (k + 1) (fwdW a b ζ).1 (x + ζ * y) ∧ Rep (k + 1) (fwdW a b ζ).2 (x - ζ * y) := by
  obtain ⟨t1, t2, t3⟩ := mont_rep ζ hb
  obtain ⟨a1, a2, a3⟩ := ha
  have hk' : (k : Int) * 3329 + 3329 ≤ 32768 := by omega_using [hk]
  simp only [fwdW, Rep]
  generalize montW b (zw ζ) = t at t1 t2 t3 ⊢
  have t1' : -3329 < t.toInt := by omega_using [t1]
  have t2' : t.toInt < 3329 := by omega_using [t2]
  have hx := val_lt x
  have hz := val_lt (ζ * y)
  have p := W.toInt_add16 (a := a) (b := t) (by omega_using [a1, t1', hk']) (by omega_using [a2, t2', hk'])
  have m := W.toInt_sub16 (a := a) (b := t) (by omega_using [a1, t2', hk']) (by omega_using [a2, t1', hk'])
  have v1 : ((x + ζ * y).val : Int) = ((x.val : Int) + ((ζ * y).val : Int)) % 3329 := by
    rw [val_add']; simp only [q]; omega_arith
  have v2 : ((x - ζ * y).val : Int) = ((x.val : Int) + (3329 - ((ζ * y).val : Int))) % 3329 := by
    rw [val_sub']; simp only [q]; omega_arith
  rw [p, m, v1, v2]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;> omega_using [a1, a2, a3, t1', t2', t3, hk', hx, hz]

/-- The lazy butterfly of `NTT⁻¹`: the bound of the sum doubles. -/
theorem invW_rep {k : Nat} (hk : 2 * k * 3329 ≤ 32768) {a b : BitVec 16} {x y : Zq} (ζ : Zq)
    (ha : Rep k a x) (hb : Rep k b y) :
    Rep (2 * k) (invW a b ζ).1 (x + y) ∧ Rep 1 (invW a b ζ).2 (ζ * (y - x)) := by
  obtain ⟨a1, a2, a3⟩ := ha
  obtain ⟨b1, b2, b3⟩ := hb
  have hk' : 2 * (k : Int) * 3329 ≤ 32768 := by omega_using [hk]
  have hx := val_lt x
  have hy := val_lt y
  have p := W.toInt_add16 (a := a) (b := b) (by omega_using [a1, b1, hk']) (by omega_using [a2, b2, hk'])
  have m := W.toInt_sub16 (a := b) (b := a) (by omega_using [a2, b1, hk']) (by omega_using [a1, b2, hk'])
  have v1 : ((x + y).val : Int) = ((x.val : Int) + (y.val : Int)) % 3329 := by
    rw [val_add']; simp only [q]; omega_arith
  have v2 : ((y - x).val : Int) = ((y.val : Int) + (3329 - (x.val : Int))) % 3329 := by
    rw [val_sub']; simp only [q]; omega_arith
  refine ⟨?_, mont_rep ζ ?_⟩
  · simp only [invW, Rep]
    rw [p, v1]
    refine ⟨?_, ?_, ?_⟩ <;> omega_using [a1, a2, a3, b1, b2, b3, hk', hx, hy]
  · rw [m, v2]
    omega_using [a3, b3, hx, hy]

/-! ## Polynomials of words -/

/-- Each word of `W` represents the coefficient of `F`, within `b · q`. -/
def PolyRep (b : Nat) (W : WPoly) (F : Poly) : Prop := ∀ i < 256, Rep b W[i]! F[i]!

/-- A layer of butterflies `wop` on words, each representing the
specification's `sop`, represents the layer of the specification. -/
theorem layF_rep {wop : BitVec 16 → BitVec 16 → Zq → BitVec 16 × BitVec 16} {sop : Zq → Zq → Zq → Zq × Zq}
    {wblk : WPoly → Nat → Nat → Nat → Nat → WPoly} {sblk : Poly → Nat → Nat → Nat → Nat → Poly}
    (hw : BlkOk wblk wop) (hs : BlkOk sblk sop) {k k' : Nat}
    (hop : ∀ a b x y ζ, Rep k a x → Rep k b y → Rep k' (wop a b ζ).1 (sop x y ζ).1 ∧ Rep k' (wop a b ζ).2 (sop x y ζ).2)
    {len : Nat} (hlen : len ∈ [2, 4, 8, 16, 32, 64, 128]) (zi : Nat → Nat) {W : WPoly} {F : Poly}
    (h : PolyRep k W F) :
    PolyRep k' (layF wblk W len zi (128 / len)) (layF sblk F len zi (128 / len)) := by
  have hl : 0 < len ∧ 2 * len * (128 / len) = 256 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlen
    rcases hlen with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  intro j hj
  have hj' : j < 2 * len * (128 / len) := by rw [hl.2]; exact hj
  rw [layF_get hw W hl.1 zi (by rw [hl.2]) hj, layF_get hs F hl.1 zi (by rw [hl.2]) hj,
    ite_eq_left_of_eq_true _ _ (eq_true hj'), ite_eq_left_of_eq_true _ _ (eq_true hj')]
  have hb : ∀ j < 256, (j % (2 * len) < len → j + len < 256) ∧ (¬ j % (2 * len) < len → len ≤ j) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlen
    rcases hlen with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> intro j hj <;> omega_arith
  by_cases c : j % (2 * len) < len
  · rw [ite_eq_left_of_eq_true _ _ (eq_true c), ite_eq_left_of_eq_true _ _ (eq_true c)]
    exact (hop _ _ _ _ _ (h j hj) (h _ ((hb j hj).1 c))).1
  · rw [ite_eq_right_of_eq_false _ _ (eq_false c), ite_eq_right_of_eq_false _ _ (eq_false c)]
    exact (hop _ _ _ _ _ (h _ (by omega_arith)) (h j hj)).2

end VG.Proof.MlKem.X86_64

end

end

/-!
# ML-KEM on x86-64: the bounds of the lazy butterflies

`fwd_hop` and `inv_hop` bound a lazy butterfly of `NTT` (`fwdW`) and of
`NTT⁻¹` (`invW`), for the NTT on registers (`NttR/Model.lean`,
`NttR/InvModel.lean`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

theorem fwd_hop {k : Nat} (hk : (k + 1) * 3329 ≤ 32768) :
    ∀ (a b : BitVec 16) (x y ζ : Zq), Rep k a x → Rep k b y →
      Rep (k + 1) (fwdW a b ζ).1 ((fun x y z => (x + z * y, x - z * y)) x y ζ).1 ∧
        Rep (k + 1) (fwdW a b ζ).2 ((fun x y z => (x + z * y, x - z * y)) x y ζ).2 :=
  fun _ _ _ _ ζ ha hb => fwdW_rep hk ζ ha hb.2.2

theorem inv_hop {k : Nat} (hk : 2 * k * 3329 ≤ 32768) (hk1 : 1 ≤ 2 * k) :
    ∀ (a b : BitVec 16) (x y ζ : Zq), Rep k a x → Rep k b y →
      Rep (2 * k) (invW a b ζ).1 ((fun x y z => (x + y, z * (y - x))) x y ζ).1 ∧
        Rep (2 * k) (invW a b ζ).2 ((fun x y z => (x + y, z * (y - x))) x y ζ).2 :=
  fun _ _ _ _ ζ ha hb => ⟨(invW_rep hk ζ ha hb).1, (invW_rep hk ζ ha hb).2.mono hk1⟩

theorem getElem!_map {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) (v : Vector α n) {i : Nat} (hi : i < 256) :
    (v.map f)[i]! = f v[i]! := by
  rw [getElem!_pos _ i (by rw [n_eq]; exact hi), getElem!_pos _ i (by rw [n_eq]; exact hi), Vector.getElem_map]

end VG.Proof.MlKem.X86_64

end

end

/-!
# ML-KEM on x86-64: the NTT on registers, the words of its layers

The polynomial's words after `st` lazy layers (`LW`), as the existing AVX2
code computes them (`fwdW`, `layF`), obey the butterflies `Sym.run` collapses
(`model`), and their reduction (`Of`) is the coefficient of `NTT`
(`Of_ntt`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.NttR

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.NttR
open VG.Spec.MlKem
open VG.Proof.MlKem.X86_64 (WPoly fwdW zw PolyRep fwd_hop layF_rep red_rep cadd_rep rW)
open VG.Proof.MlKem (wBlockN wBlk_ok layF_get nttBlk_ok)

/-- The distance of the butterflies of layer `st` of `NTT`. -/
def lenOf (st : Nat) : Nat := 128 >>> st

/-- The words after the first `st` layers. -/
def LW (W : WPoly) (st : Nat) : WPoly :=
  (nttLens.take st).foldl (fun W len => layF (wBlockN fwdW) W len (fun c => 128 / len + c) (128 / len)) W

def Lf (W : WPoly) (st p : Nat) : BitVec 16 := (LW W st)[p]!

/-- The reduced word `p` after the seven layers. -/
def Of (W : WPoly) (p : Nat) : BitVec 16 := caddQ (mtW (Lf W 7 p) (zmTab 0) (zmTab 0 * qinvN % 65536))

theorem lenOf_cases {st : Nat} (h : st < 7) :
    nttLens[st]? = some (lenOf st) := by
  rcases (by omega_using [h] : st = 0 ∨ st = 1 ∨ st = 2 ∨ st = 3 ∨ st = 4 ∨ st = 5 ∨ st = 6) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem fwd_ops {st : Nat} (h : st < 7) : fwdRules.ops[st]? = some (.ct (lenOf st)) := by
  rcases (by omega_using [h] : st = 0 ∨ st = 1 ∨ st = 2 ∨ st = 3 ∨ st = 4 ∨ st = 5 ∨ st = 6) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem fwd_ops_none {st : Nat} (h : 7 ≤ st) : fwdRules.ops[st]? = none :=
  List.getElem?_eq_none (by simp only [fwdRules, List.length_cons, List.length_nil]; omega_using [h])

theorem LW_succ (W : WPoly) {st : Nat} (h : st < 7) :
    LW W (st + 1) = layF (wBlockN fwdW) (LW W st) (lenOf st) (fun c => 128 / lenOf st + c) (128 / lenOf st) := by
  unfold LW
  rw [List.take_add_one, List.foldl_append, lenOf_cases h]
  rfl

theorem setWidth_signExtend16 (a : BitVec 16) : (a.signExtend 32).setWidth 16 = a := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_signExtend, BitVec.toNat_setWidth]
  have := a.isLt
  split <;> omega_using []

theorem lo_mul (a b : BitVec 16) : (mulWordsSigned a b).extractLsb' 0 16 = a * b := by
  rw [mulWordsSigned, ← BitVec.setWidth_eq_extractLsb' (by decide), BitVec.setWidth_mul _ _ (by decide),
    setWidth_signExtend16, setWidth_signExtend16]

/-- `vmont` with the precomputed `ζ q⁻¹` is `montW`. -/
theorem mtW_eq (b : BitVec 16) (k : Nat) :
    W.montW b (zw (zeta k)) = mtW b (zmTab k) (zmTab k * qinvN % 65536) := by
  have hz : zw (zeta k) = BitVec.ofNat 16 (zmTab k) := by rw [zw, zmTab_eq]
  have hq : W.qW = BitVec.ofNat 16 qN := rfl
  have hk : zmTab k < 3329 := by rw [zmTab_eq]; exact Nat.mod_lt _ (by decide)
  have hm : BitVec.ofNat 16 (zmTab k) * W.qinvW = BitVec.ofNat 16 (zmTab k * qinvN % 65536) := by
    apply BitVec.eq_of_toNat_eq
    have hq' : W.qinvW.toNat = 62209 := by decide
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, hq', Nat.mod_eq_of_lt (show zmTab k < 2 ^ 16 by omega_using [hk])]
    simp only [qinvN]
    omega_using []
  rw [W.montW, mtW, hz, hq, lo_mul, lo_mul, lo_mul, BitVec.mul_assoc, hm]

theorem model (W : WPoly) (hW : ∀ p < 256, (W[p]!).toNat < 32768) : Model fwdRules (Lf W) (Of W) := by
  refine ⟨fun p hp => hW p hp, fun st p p' z z' hb => ?_, fun st p p' h => ?_, fun st p p' z z' h => ?_,
    fun st p h => ?_, fun _ _ => rfl⟩
  rotate_left
  · rcases Nat.lt_or_ge st 7 with hs | hs
    · simp [gsPairOk, fwd_ops hs] at h
    · simp [gsPairOk, fwd_ops_none hs] at h
  · rcases Nat.lt_or_ge st 7 with hs | hs
    · simp [gsOk, fwd_ops hs] at h
    · simp [gsOk, fwd_ops_none hs] at h
  · rcases Nat.lt_or_ge st 7 with hs | hs
    · simp [redOk, fwd_ops hs] at h
    · simp [redOk, fwd_ops_none hs] at h
  have hst : st < 7 := by
    by_contra hs
    simp [bflyOk, fwd_ops_none (Nat.le_of_not_lt hs)] at hb
  rw [bflyOk, fwd_ops hst] at hb
  have hb' := hb
  simp only [pairOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hb'
  obtain ⟨⟨⟨⟨rfl, hm⟩, hp'⟩, rfl⟩, rfl⟩ := hb'
  have hlen : 0 < lenOf st ∧ 2 * lenOf st * (128 / lenOf st) = 256 := by
    rcases (by omega_using [hst] : st = 0 ∨ st = 1 ∨ st = 2 ∨ st = 3 ∨ st = 4 ∨ st = 5 ∨ st = 6) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hd : (p + lenOf st) / (2 * lenOf st) = p / (2 * lenOf st) ∧
      (p + lenOf st) % (2 * lenOf st) = p % (2 * lenOf st) + lenOf st ∧ p + lenOf st - lenOf st = p := by
    rcases (by omega_using [hst] : st = 0 ∨ st = 1 ∨ st = 2 ∨ st = 3 ∨ st = 4 ∨ st = 5 ∨ st = 6) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [lenOf, Nat.reduceShiftRight] at hm ⊢ <;> omega_using [hm]
  simp only [Lf]
  rw [LW_succ W hst, layF_get (wBlk_ok fwdW) _ hlen.1 _ (by rw [hlen.2]) (by omega_using [hp']),
    layF_get (wBlk_ok fwdW) _ hlen.1 _ (by rw [hlen.2]) hp']
  rw [ite_eq_left_of_eq_true _ _ (eq_true (show p < _ by rw [hlen.2]; omega_using [hp'])),
    ite_eq_left_of_eq_true _ _ (eq_true (show p + lenOf st < _ by rw [hlen.2]; omega_using [hp'])),
    ite_eq_left_of_eq_true _ _ (eq_true hm),
    ite_eq_right_of_eq_false _ _ (eq_false (show ¬ (p + lenOf st) % (2 * lenOf st) < lenOf st by omega_using [hd])),
    hd.2.2, hd.1]
  simp only [fwdW, mtW_eq]
  exact ⟨trivial, trivial⟩

theorem lenOf_mem {st : Nat} (h : st < 7) : lenOf st ∈ [2, 4, 8, 16, 32, 64, 128] := by
  rcases (by omega_using [h] : st = 0 ∨ st = 1 ∨ st = 2 ∨ st = 3 ∨ st = 4 ∨ st = 5 ∨ st = 6) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The words after `st` layers represent the specification's, within `(st + 1) q`. -/
theorem LW_rep (W : WPoly) (F : Poly) (h : PolyRep 1 W F) :
    ∀ st, st ≤ 7 → PolyRep (st + 1) (LW W st) ((nttLens.take st).foldl nttLayer F)
  | 0, _ => h
  | st + 1, hs => by
    have ih := LW_rep W F h st (by omega_using [hs])
    rw [LW_succ W (by omega_using [hs]), List.take_add_one, List.foldl_append, lenOf_cases (by omega_using [hs])]
    simp only [Option.toList, List.foldl_cons, List.foldl_nil]
    rw [VG.Proof.MlKem.X86_64.nttLayer_eq]
    exact layF_rep (wBlk_ok fwdW) nttBlk_ok (fwd_hop (k := st + 1) (by omega_using [hs])) (lenOf_mem (by omega_using [hs])) _ ih

/-- The reduced words after the seven layers are the coefficients of `NTT`. -/
theorem Of_ntt (W : WPoly) (F : Poly) (h : PolyRep 1 W F) {p : Nat} (hp : p < 256) :
    (Of W p).toNat = ((ntt F)[p]!).val := by
  have h7 := LW_rep W F h 7 (by decide)
  have hz : zw (zeta 0) = rW := by rw [zw, ← zmTab_eq]; decide
  have e : Of W p = VG.Proof.MlKem.X86_64.W.caddW (VG.Proof.MlKem.X86_64.W.montW (Lf W 7 p) rW) := by
    rw [Of, ← mtW_eq _ 0, hz]; rfl
  rw [e, ntt_eq_layers]
  exact cadd_rep (red_rep (h7 p hp).2.2)

end VG.Proof.MlKem.X86_64.NttR

end

end

/-!
# ML-KEM on x86-64: the NTT on registers

`nttR pb` (`pb` pass B storing to `d`, as `check` says) leaves `NTT` of the
polynomial at `rdi` at `d` (`nttR_ok`): after `pro`, the terms of `initA`
hold, with the polynomial's words after `st` layers `Lf W st` for its words
`W` and their reductions `Of W`; pass A keeps them (`run_ok`) in the regions
`rsA`, pass B in the regions `rsB d`, and `check` says the output's terms are
`Of W`, which `Of_ntt` takes to `NTT`.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.NttR

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.NttR
open VG.Spec.MlKem
open VG.Proof.MlKem.X86_64 (WPoly PolyRep wordAt wAddr pR Keep yconst_ok)

/-! ## Coefficients as words -/

theorem coeff_words (m : Mem) (p : Addr) (i : Nat) :
    coeffAt m p i = wordAt m p (2 * i + 1) ++ wordAt m p (2 * i) := by
  have h0 := readW_extract m (p + BitVec.ofNat 64 (4 * i)) (w := 32) (k := 0) (n := 2) (by omega_arith)
  have h1 := readW_extract m (p + BitVec.ofNat 64 (4 * i)) (w := 32) (k := 2) (n := 2) (by omega_arith)
  have a0 : p + BitVec.ofNat 64 (4 * i) + BitVec.ofNat 64 0 = wAddr p (2 * i) := by
    simp only [wAddr, BitVec.add_zero]; congr 2; omega_arith
  have a1 : p + BitVec.ofNat 64 (4 * i) + BitVec.ofNat 64 2 = wAddr p (2 * i + 1) := by
    rw [wAddr, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega_arith
  rw [a0] at h0; rw [a1] at h1
  have h0' : (m.readW (p + BitVec.ofNat 64 (4 * i)) 32).extractLsb' 0 16 = m.readW (wAddr p (2 * i)) 16 := h0
  have h1' : (m.readW (p + BitVec.ofNat 64 (4 * i)) 32).extractLsb' 16 16 = m.readW (wAddr p (2 * i + 1)) 16 := h1
  unfold wordAt coeffAt
  rw [← h0', ← h1']
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  split
  · simp only [show j < 16 by omega_arith, decide_true, Bool.true_and]; exact congrArg _ (by omega_arith)
  · simp only [show j - 16 < 16 by omega_arith, decide_true, Bool.true_and]; exact congrArg _ (by omega_arith)

/-- The words of the input's coefficients. -/
def inW (m : Mem) (p : Addr) : WPoly := Vector.ofFn fun i => wordAt m p (2 * i.val)

theorem inW_get (m : Mem) (p : Addr) {i : Nat} (hi : i < 256) : (inW m p)[i]! = wordAt m p (2 * i) := by
  rw [getElem!_pos _ i (by rw [n_eq]; exact hi)]; simp [inW]

theorem toNat_app16 (a b : BitVec 16) : (a ++ b).toNat = a.toNat * 65536 + b.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt b.isLt, Nat.shiftLeft_eq]

theorem reduced_words {m : Mem} {p : Addr} (h : Reduced m p) {i : Nat} (hi : i < 256) :
    wordAt m p (2 * i + 1) = 0 ∧ (wordAt m p (2 * i)).toNat = (coeffAt m p i).toNat := by
  have hc : (coeffAt m p i).toNat < 3329 := h i (by rw [n_eq]; exact hi)
  rw [coeff_words, toNat_app16] at hc ⊢
  exact ⟨BitVec.eq_of_toNat_eq (by rw [show (0 : BitVec 16).toNat = 0 from rfl]; omega_arith), by omega_arith⟩

/-! ## The prologue -/

theorem word_q {i : Nat} (hi : i < 8) : word (ofDwords 0x0D010D01 0x0D010D01 0x0D010D01 0x0D010D01) i = 3329 := by
  rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem pro_ok (s : State) :
    WP isa (.block pro) s fun s1 => s1.gpr .r8 = s1.syms tblName ∧ (∀ e < 16, wd s1 .xmm15 e = 3329) ∧
      s1.mem = s.mem ∧ Keep [.rax, .r8] s s1 := by
  unfold pro
  rw [WP.block_append_iff]
  refine WP.mono (yconst_ok .xmm15 0x0D010D01 s) fun s2 ⟨hl, k2, hm, _, _⟩ => ?_
  refine WP.block_cons_iff.2 ⟨_, rfl, WP.block_nil ⟨rfl, fun e he => ?_, hm, ?_⟩⟩
  · simp only [wd, VG.Proof.MlKem.X86_64.lane_setReg]
    rw [hl _ (by omega_arith), word_q (Nat.mod_lt _ (by decide))]
  · refine ⟨fun r hr => ?_, k2.2.1, k2.2.2⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [RegUpd.gpr_setReg_of_ne _ _ hr.2]
    exact k2.1 r (by simpa using hr.1)

/-! ## The regions -/

/-- A region of `S` and `X`: readable, `S` writable (and `X` if `w`), apart. -/
theorem ctx2 {s : State} {X : Reg} {w : Bool} (hS : pR (s.gpr .rsi) ∈ s.wr)
    (hX : pR (s.gpr X) ∈ s.rd ++ s.wr) (hXw : w = true → pR (s.gpr X) ∈ s.wr)
    (hD : (pR (s.gpr X)).Disjoint (pR (s.gpr .rsi))) (h8 : s.gpr .r8 = s.syms tblName) :
    Ctx [(.rsi, oS, 256, true), (X, 0, 512, w)] s := by
  have cS : (pR (s.gpr .rsi)).Contains (s.gpr .rsi + BitVec.ofNat 64 oS) 512 := by
    unfold Region.Contains
    rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat]; simp [oS]
  have cX : (pR (s.gpr X)).Contains (s.gpr X + BitVec.ofNat 64 0) 1024 := by
    unfold Region.Contains
    rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
  have sep : Mem.Sep (s.gpr .rsi + BitVec.ofNat 64 oS) 512 (s.gpr X + BitVec.ofNat 64 0) 1024 := by
    intro x h1 h2
    rw [Offset.lt_iff x _ (by decide)] at h1
    rw [Offset.lt_iff x _ (by decide)] at h2
    exact hD x (by show (x - s.gpr X).toNat + 1 ≤ 1024; omega_arith)
      (by show (x - s.gpr .rsi).toNat + 1 ≤ 1024; simp only [oS] at h1; omega_arith)
  refine ⟨fun k hk => ?_, fun k hk hw => ?_, fun k k' hk hk' hne => ?_, fun k hk => ?_, h8⟩
  · simp only [List.length_cons, List.length_nil] at hk
    rcases (by omega_arith : k = 0 ∨ k = 1) with rfl | rfl
    · exact ⟨_, List.mem_append_right _ hS, cS⟩
    · exact ⟨_, hX, cX⟩
  · simp only [List.length_cons, List.length_nil] at hk
    rcases (by omega_arith : k = 0 ∨ k = 1) with rfl | rfl
    · exact ⟨_, hS, cS⟩
    · exact ⟨_, hXw hw, cX⟩
  · simp only [List.length_cons, List.length_nil] at hk hk'
    rcases (by omega_arith : k = 0 ∧ k' = 1 ∨ k = 1 ∧ k' = 0) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact sep
    · exact fun x h1 h2 => sep x h2 h1
  · simp only [List.length_cons, List.length_nil] at hk
    rcases (by omega_arith : k = 0 ∨ k = 1) with rfl | rfl <;> simp [rlen, oS]

/-! ## The terms where each pass starts -/

theorem initA_reg (r : XReg) :
    initA.reg r = if r = .xmm15 then List.replicate 16 (.c qN) else List.replicate 16 .junk := by
  cases r <;> rfl

theorem get_replicate (x : E) {e : Nat} (he : e < 16) : Y.get (List.replicate 16 x) e = x := by
  rw [Y.get, List.getD_eq_getElem?_getD, List.getElem?_replicate, ite_eq_left_of_eq_true _ _ (eq_true he)]; rfl

theorem junks_get (n c e : Nat) : Y.get ((junks n).getD c []) e = .junk := by
  rw [junks, List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split
  · rw [Option.getD_some, Y.get, List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl
  · rfl

theorem inTerms_get {j : Nat} (hj : j < 512) :
    Y.get (inTerms.getD (j / 16) []) (j % 16) = if j % 2 = 0 then .lv 0 (j / 2) else .c 0 := by
  rw [inTerms, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega_arith), Option.map_some,
    Option.getD_some, Y.get, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (Nat.mod_lt _ (by decide)), Option.map_some, Option.getD_some,
    show 16 * (j / 16) + j % 16 = j by omega_arith]

theorem initA_rel {L : Nat → Nat → BitVec 16} {O : Nat → BitVec 16} {s₁ : State}
    (hL : ∀ p < 256, L 0 p = wordAt s₁.mem (s₁.gpr .rdi) (2 * p))
    (hz : ∀ p < 256, wordAt s₁.mem (s₁.gpr .rdi) (2 * p + 1) = 0)
    (hq : ∀ e < 16, wd s₁ .xmm15 e = 3329) : Rel rsA L O initA s₁ s₁ := by
  refine ⟨fun r e he => ?_, fun k j hk hj => ?_, by cases s₁; rfl, ⟨by simp only [initA, rsA, List.length_cons, List.length_nil], by simp [initA]⟩, fun _ _ => rfl⟩
  · rw [initA_reg]
    split
    · rename_i hr; subst hr
      rw [get_replicate _ he, hq e he]; exact Hd.of_eq rfl
    · rw [get_replicate _ he]; exact Hd.junk _
  · simp only [rsA, List.length_cons, List.length_nil] at hk
    rcases (by omega_arith : k = 0 ∨ k = 1) with rfl | rfl
    · left
      rw [show initA.mem.getD 0 [] = junks 16 by simp only [initA, List.getD_cons_zero], junks_get]; rfl
    · have hj' : j < 512 := hj
      have hb : rbase rsA s₁ 1 = s₁.gpr .rdi := by simp [rbase, rsA]
      have ht : Y.get ((initA.mem.getD 1 []).getD (j / 16) []) (j % 16) =
          if j % 2 = 0 then .lv 0 (j / 2) else .c 0 := by
        rw [show initA.mem.getD 1 [] = inTerms by simp only [initA, List.getD_cons_succ, List.getD_cons_zero],
          inTerms_get hj']
      rw [ht, hb]
      split
      · rename_i h2
        refine Hd.of_eq ?_
        simp only [E.eval]
        rw [hL _ (by omega_arith), show 2 * (j / 2) = j by omega_arith]
      · refine Hd.of_eq ?_
        rw [show j = 2 * (j / 2) + 1 by omega_arith, hz _ (by omega_arith)]; rfl

/-- Pass B starts from the registers and `S` pass A leaves. -/
theorem reframe {L : Nat → Nat → BitVec 16} {O : Nat → BitVec 16} {X d : Reg} {n : Nat} {σ : St} {s₀ s : State}
    (h : Rel [(.rsi, oS, 256, true), (X, 0, n, false)] L O σ s₀ s) :
    Rel [(.rsi, oS, 256, true), (d, 0, 512, true)] L O (toB σ) s₀ s := by
  refine ⟨fun r e he => ?_, fun k j hk hj => ?_, h.eq, ⟨rfl, by simp [toB, St.set, h.len.2]⟩,
    fun x hx => h.fr x ?_⟩
  · show Hd L O (((σ.set .xmm3 (List.replicate 16 .junk)).reg r).get e) _
    rw [St.reg_set _ _ _ _ h.len.2]
    split
    · rw [get_replicate _ he]; exact Hd.junk _
    · exact h.reg r e he
  · simp only [List.length_cons, List.length_nil] at hk
    rcases (by omega_arith : k = 0 ∨ k = 1) with rfl | rfl
    · exact h.mem 0 j (by simp) hj
    · left
      rw [show (toB σ).mem.getD 1 [] = junks 32 by simp only [toB, List.getD_cons_succ, List.getD_cons_zero],
        junks_get]; rfl
  · intro k hk hw
    simp only [List.length_cons, List.length_nil] at hk
    rcases (by omega_arith : k = 0 ∨ k = 1) with rfl | rfl
    · exact hx 0 (by simp) rfl
    · cases hw

/-! ## The NTT -/

theorem outOk_get {σ : St} (h : outOk σ = true) {i : Nat} (hi : i < 512) :
    Y.get ((σ.mem.getD 1 []).getD (i / 16) []) (i % 16) = if i % 2 = 0 then .out (i / 2) else .c 0 :=
  E.beq_eq (List.all_eq_true.1 h i (List.mem_range.2 hi))

/-- `nttR pb` leaves `NTT` of the polynomial at `rdi` at `d`, if `check pb d`. -/
theorem nttR_ok {pb : List Instr} {d : Reg} (hc : check pb d = true) (hd : d = .rdi ∨ d = .r10) {s : State}
    (hS : pR (s.gpr .rsi) ∈ s.wr) (hI : pR (s.gpr .rdi) ∈ s.rd ++ s.wr) (hO : pR (s.gpr d) ∈ s.wr)
    (hDI : (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi))) (hDO : (pR (s.gpr d)).Disjoint (pR (s.gpr .rsi)))
    (hred : Reduced s.mem (s.gpr .rdi)) :
    WP isa (nttR pb) s fun s' => PolyIs s'.mem (s.gpr d) (ntt (polyAt s.mem (s.gpr .rdi))) ∧
      Frame [pR (s.gpr d), pR (s.gpr .rsi)] s.mem s'.mem ∧ Keep [.rax, .r8] s s' := by
  unfold check at hc
  split at hc <;> [skip; cases hc]
  rename_i σA hA
  split at hc <;> [skip; cases hc]
  rename_i σB hB
  unfold nttR
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (pro_ok s) fun s1 ⟨h8, hq, hm1, k1⟩ => ?_
  have g : ∀ r, r ≠ .rax → r ≠ .r8 → s1.gpr r = s.gpr r := fun r h1 h2 =>
    k1.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h1, h2⟩)
  have gdi : s1.gpr .rdi = s.gpr .rdi := g _ (by decide) (by decide)
  have gsi : s1.gpr .rsi = s.gpr .rsi := g _ (by decide) (by decide)
  have gd : s1.gpr d = s.gpr d := g _ (by rcases hd with rfl | rfl <;> decide) (by rcases hd with rfl | rfl <;> decide)
  let W := inW s.mem (s.gpr .rdi)
  let F := polyAt s.mem (s.gpr .rdi)
  have hW : ∀ p < 256, (W[p]!).toNat = (F[p]!).val := fun p hp => by
    rw [inW_get _ _ hp, (reduced_words hred hp).2, VG.Proof.MlKem.polyAt_val hred (by rw [n_eq]; exact hp)]
  have hM : Model fwdRules (Lf W) (Of W) := model W fun p hp => by
    rw [hW p hp]; have := (F[p]!).isLt; simp only [q] at this; omega_arith
  have hrep : PolyRep 1 W F := fun p hp => VG.Proof.MlKem.X86_64.Rep.of_can (hW p hp)
  have hrel0 : Rel rsA (Lf W) (Of W) initA s1 s1 := by
    refine initA_rel (fun p hp => ?_) (fun p hp => ?_) hq
    · show (LW W 0)[p]! = _
      rw [gdi, hm1]; exact inW_get _ _ hp
    · rw [gdi, hm1]; exact (reduced_words hred hp).1
  have cA : Ctx rsA s1 := ctx2 (by rw [gsi, k1.2.2]; exact hS) (by rw [gdi, k1.2.1, k1.2.2]; exact hI)
    (fun h => by cases h) (by rw [gdi, gsi]; exact hDI) h8
  have cB : Ctx (rsB d) s1 := ctx2 (by rw [gsi, k1.2.2]; exact hS) (by rw [gd, k1.2.1, k1.2.2]; exact List.mem_append_right _ hO)
    (fun _ => by rw [gd, k1.2.2]; exact hO) (by rw [gd, gsi]; exact hDO) h8
  refine WP.mono (run_ok hM cA passA hrel0 hA) fun s2 hr2 => ?_
  refine WP.mono (run_ok hM cB pb (reframe hr2) hB) fun s3 hr3 => ?_
  refine WP.block_cons_iff.2 ⟨_, rfl, WP.block_nil ⟨?_, ?_, ?_⟩⟩
  · have hb : rbase (rsB d) s1 1 = s.gpr d := by simp [rbase, rsB, gd]
    refine VG.Proof.MlKem.polyIs_of_toNat fun p hp => ?_
    rw [n_eq] at hp
    have h0 := hr3.mem 1 (2 * p) (by simp [rsB]) (by simp [rlen, rsB]; omega_arith)
    have h1 := hr3.mem 1 (2 * p + 1) (by simp [rsB]) (by simp [rlen, rsB]; omega_arith)
    rw [outOk_get hc (by omega_arith), hb] at h0 h1
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega_arith)), show 2 * p / 2 = p by omega_arith] at h0
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith))] at h1
    have e0 := h0.eq rfl
    have e1 := h1.eq rfl
    show (coeffAt s3.mem (s.gpr d) p).toNat = _
    rw [coeff_words, toNat_app16, e0, e1]
    simp only [E.eval]
    rw [Of_ntt W F hrep hp]
    simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_mul, Nat.zero_add]
    rfl
  · intro x hx
    show s3.mem x = s.mem x
    rw [← hm1]
    refine hr3.fr x fun k hk hw hlt => ?_
    simp only [rsB, List.length_cons, List.length_nil] at hk
    rcases (by omega_arith : k = 0 ∨ k = 1) with rfl | rfl
    · refine hx (pR (s.gpr .rsi)) (by simp) ?_
      simp only [rbase, rlen, rsB, List.getD_cons_zero, gsi] at hlt
      rw [Offset.lt_iff x _ (by decide)] at hlt
      show (x - s.gpr .rsi).toNat + 1 ≤ 1024
      simp only [oS] at hlt; omega_arith
    · refine hx (pR (s.gpr d)) (by simp) ?_
      simp only [rbase, rlen, rsB, List.getD_cons_succ, List.getD_cons_zero, gd] at hlt
      rw [Offset.lt_iff x _ (by decide)] at hlt
      show (x - s.gpr d).toNat + 1 ≤ 1024
      omega_arith
  · refine ⟨fun r hr => ?_, ?_, ?_⟩
    · show s3.gpr r = s.gpr r
      rw [hr3.gpr]; exact k1.1 r hr
    · show s3.rd = s.rd
      rw [hr3.rd]; exact k1.2.1
    · show s3.wr = s.wr
      rw [hr3.wr]; exact k1.2.2

end VG.Proof.MlKem.X86_64.NttR
