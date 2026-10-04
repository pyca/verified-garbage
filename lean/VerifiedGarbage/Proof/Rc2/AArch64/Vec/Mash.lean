import VerifiedGarbage.Proof.Rc2.AArch64.Vec.Round

/-!
# Reverse mashing on eight blocks

`rmash_ok`: the reverse mash of word `i` of a set. Each lane's index is the
low six bits of the word before it, made into the bytes `2 j`, `2 j + 1`
(`514 j + 256`), which `select false` looks up in the schedule; the lane's
low 16 bits are then the schedule word `j`.
-/

namespace VG.Proof.Rc2.AArch64.Vec

open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Tbl VG.Impl.Tbl.AArch64 VG.Impl.Rc2.AArch64
  VG.Impl.Rc2.AArch64.Vec

theorem exec_mul4 (s : State) (d n m : VReg) :
    exec (.vop (.mul d n m)) s = some (s.setV d (VArr.s4.map2 (fun _ x y => x * y) (s.v n) (s.v m))) :=
  rfl

theorem exec_add4 (s : State) (d n m : VReg) :
    exec (.vop (.add .s4 d n m)) s = some (s.setV d (VArr.s4.map2 (fun _ x y => x + y) (s.v n) (s.v m))) :=
  rfl

/-- Byte `c` of lane `b`. -/
theorem vbyte_lane (x : BitVec 128) {b c : Nat} (hc : c < 4) :
    vbyte x (4 * b + c) = (vword x b).extractLsb' (8 * c) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro t ht
  simp [vbyte, vword, ht, show 8 * c + t < 32 by omega,
    show 8 * (4 * b + c) + t = 32 * b + (8 * c + t) by omega]

/-- A lane's index: `514 j + 256`, `j` the low six bits of its word. -/
theorem index_lane (x : BitVec 32) :
    (x &&& (BitVec.ofNat 64 63).setWidth 32) * (BitVec.ofNat 64 514).setWidth 32 +
        (BitVec.ofNat 64 256).setWidth 32 =
      BitVec.ofNat 32 (256 + 514 * (x.setWidth 16 &&& 63).toNat) := by
  have a : ∀ n : Nat, n &&& 63 = n % 64 := fun n => Nat.and_two_pow_sub_one_eq_mod n 6
  rw [show (BitVec.ofNat 64 63).setWidth 32 = (63 : BitVec 32) from rfl,
    show (BitVec.ofNat 64 514).setWidth 32 = (514 : BitVec 32) from rfl,
    show (BitVec.ofNat 64 256).setWidth 32 = (256 : BitVec 32) from rfl]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_and, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat, show (63 : BitVec 32).toNat = 63 from rfl,
    show (63 : BitVec 16).toNat = 63 from rfl, show (514 : BitVec 32).toNat = 514 from rfl,
    show (256 : BitVec 32).toNat = 256 from rfl, a, Nat.mod_mod_of_dvd _ (by decide : 64 ∣ 2 ^ 16)]
  have : x.toNat % 64 < 64 := Nat.mod_lt _ (by decide)
  generalize x.toNat % 64 = y at *
  omega

theorem index_lt (x : BitVec 16) : (x &&& 63).toNat < 64 := by
  rw [BitVec.toNat_and, show (63 : BitVec 16).toNat = 2 ^ 6 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem vword_dup4 (w : BitVec 32) {b : Nat} (hb : b < 4) : vword (ofVWords w w w w) b = w := by
  rw [vword_ofVWords _ _ _ _ hb]
  rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;> rfl

/-- A block keeps the stack pointer. -/
theorem runBlock_sp {is : List Instr} {s s' : State} (hr : runBlock isa is s = some s') :
    s'.sp = s.sp := by
  induction is generalizing s with
  | nil => cases hr; rfl
  | cons i is ih =>
    cases he : exec i s with
    | none => rw [runBlock_cons, he] at hr; cases hr
    | some u => rw [runBlock_cons, he, runStep_some] at hr; rw [ih hr]; exact exec_sp he

theorem wreg_ne (h i : Nat) (hh : h < 2) : wreg h i ≠ .v0 ∧ wreg h i ≠ .v1 ∧ wreg h i ≠ .v2 ∧
    wreg h i ≠ .v3 ∧ wreg h i ≠ .v4 ∧ wreg h i ≠ .v5 ∧ wreg h i ≠ .v6 ∧ wreg h i ≠ .v7 :=
  treg_ne8 (8 + 4 * h + i % 4) (by omega)

theorem rmash_ok {s : State} {m : Mem} {p : Addr} (hs : SchedV s m p) {h i : Nat} (hh : h < 2)
    (hi : i < 4) {vs : Nat → Spec.Rc2.State} (hv : VWords s h vs) :
    ∃ s', runBlock isa (rmash h i) s = some s' ∧
      VWords s' h (fun b => Spec.Rc2.reverseMash (Spec.Rc2.scheduleAt m p) i (vs b)) ∧
      (∀ r, r ≠ wreg h i → r ≠ .v0 → r ≠ .v1 → r ≠ .v2 → r ≠ .v3 → r ≠ .v4 → r ≠ .v5 →
        s'.v r = s.v r) ∧
      Keep [.x9, .x6] s s' ∧ s'.sp = s.sp := by
  have wn := wreg_ne h (i + 3) hh
  let W := s.v (wreg h (i + 3))
  let s₁ := s.write .x .x9 (BitVec.ofNat 64 63)
  let s₂ := s₁.setV .v1 (ofVWords ((s₁.gpr .x9).setWidth 32) ((s₁.gpr .x9).setWidth 32)
    ((s₁.gpr .x9).setWidth 32) ((s₁.gpr .x9).setWidth 32))
  let s₃ := s₂.setV .v0 (s₂.v (wreg h (i + 3)) &&& s₂.v .v1)
  let s₄ := s₃.write .x .x9 (BitVec.ofNat 64 514)
  let s₅ := s₄.setV .v4 (ofVWords ((s₄.gpr .x9).setWidth 32) ((s₄.gpr .x9).setWidth 32)
    ((s₄.gpr .x9).setWidth 32) ((s₄.gpr .x9).setWidth 32))
  let s₆ := s₅.setV .v0 (VArr.s4.map2 (fun _ x y => x * y) (s₅.v .v0) (s₅.v .v4))
  let s₇ := s₆.write .x .x9 (BitVec.ofNat 64 256)
  let s₈ := s₇.setV .v1 (ofVWords ((s₇.gpr .x9).setWidth 32) ((s₇.gpr .x9).setWidth 32)
    ((s₇.gpr .x9).setWidth 32) ((s₇.gpr .x9).setWidth 32))
  let s₉ := s₈.setV .v0 (VArr.s4.map2 (fun _ x y => x + y) (s₈.v .v0) (s₈.v .v1))
  have run₉ : runBlock isa ([imm .x9 63, .vop (.dup .s4 .v1 .x9),
      .vop (.logic .and .v0 (wreg h (i + 3)) .v1), imm .x9 514, .vop (.dup .s4 .v4 .x9),
      .vop (.mul .v0 .v0 .v4), imm .x9 256, .vop (.dup .s4 .v1 .x9),
      .vop (.add .s4 .v0 .v0 .v1)] : List Instr) s = some s₉ := by
    rw [runBlock_cons, exec_imm _ _ _ (by decide), runStep_some, runBlock_cons, exec_dups,
      runStep_some, runBlock_cons, exec_and, runStep_some, runBlock_cons,
      exec_imm _ _ _ (by decide), runStep_some, runBlock_cons, exec_dups, runStep_some,
      runBlock_cons, exec_mul4, runStep_some, runBlock_cons, exec_imm _ _ _ (by decide),
      runStep_some, runBlock_cons, exec_dups, runStep_some, runBlock_cons, exec_add4,
      runStep_some, runBlock_nil]
  -- The index of each lane.
  let J (b : Nat) : Nat := (lw W b &&& 63).toNat
  have l₉ : ∀ b < 4, vword (s₉.v .v0) b = BitVec.ofNat 32 (256 + 514 * J b) := by
    intro b hb
    have : vword (s₉.v .v0) b = (vword W b &&& (BitVec.ofNat 64 63).setWidth 32) *
        (BitVec.ofNat 64 514).setWidth 32 + (BitVec.ofNat 64 256).setWidth 32 := by
      simp only [s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, v_setV_self, v_write,
        v_setV_of_ne _ _ (by decide : VReg.v0 ≠ .v1), v_setV_of_ne _ _ (by decide : VReg.v0 ≠ .v4),
        v_setV_of_ne _ _ wn.2.1, gpr_write_self, BitVec.setWidth_eq,
        vword_map2 _ _ _ hb, vword_and, vword_dup4 _ hb]
      rfl
    rw [this, index_lane]
  let I : Nat → BitVec 8 := fun e => vbyte (s₉.v .v0) e
  have hI : ∀ e < 16, (I e).toNat =
      if e % 4 = 0 then 2 * J (e / 4) else if e % 4 = 1 then 2 * J (e / 4) + 1 else 0 := by
    intro e he
    simp only [I]
    rw [show e = 4 * (e / 4) + e % 4 by omega, vbyte_lane _ (by omega), l₉ _ (by omega),
      show (4 * (e / 4) + e % 4) / 4 = e / 4 by omega, show (4 * (e / 4) + e % 4) % 4 = e % 4 by omega]
    exact index_bytes _ (index_lt _) e
  obtain ⟨d, rund, d1, _, dv, dk⟩ := quarters_run false s₉
  have d0 : d.v .v0 = s₉.v .v0 := dv _ (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨f, runf, f0, fv⟩ := select_half_run (s := d) I
    (fun e he => by
      have : J (e / 4) < 64 := index_lt _
      rw [hI e he]; split <;> (try split) <;> omega)
    (fun e he => by rw [d0])
    (fun e he => by rw [d1 e he])
  let s' := f.setV (wreg h i) (VArr.s4.map2 (fun _ x y => x - y) (f.v (wreg h i)) (f.v .v0))
  -- Everything but `v0`–`v5` is kept up to the subtraction.
  have keepV : ∀ r, r ≠ .v0 → r ≠ .v1 → r ≠ .v2 → r ≠ .v3 → r ≠ .v4 → r ≠ .v5 →
      f.v r = s.v r := by
    intro r a0 a1 a2 a3 a4 a5
    rw [fv.2 r (by simp [a0, a1, a2, a3]), dv r a1 a2 a3 a4 a5]
    simp only [s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, v_setV_of_ne _ _ a0, v_setV_of_ne _ _ a1,
      v_setV_of_ne _ _ a4, v_write]
  have tab : ∀ k < 128, tbyte d.v k = m (p + BitVec.ofNat 64 k) := by
    intro k hk
    have : ∀ a < 16, d.v (treg a) = s.v (treg a) := by
      intro a ha
      obtain ⟨a0, a1, a2, a3, a4, a5, -, -⟩ := treg_ne8 a ha
      rw [dv _ a1 a2 a3 a4 a5]
      simp only [s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, v_setV_of_ne _ _ a0, v_setV_of_ne _ _ a1,
        v_setV_of_ne _ _ a4, v_write]
    rw [tbyte_congr' this _ (by omega)]
    exact tbyte_loaded m p hs k hk
  have run : runBlock isa (rmash h i) s = some s' :=
    runBlock_cat_some (runBlock_cat_some (runBlock_cat_some run₉ rund) runf)
      (by rw [runBlock_cons, exec_sub4, runStep_some, runBlock_nil])
  refine ⟨s', run, fun i' hi' b hb => ?_, fun r h0 a0 a1 a2 a3 a4 a5 => ?_, ?_, runBlock_sp run⟩
  · have wi := wreg_ne h i hh
    simp only [Spec.Rc2.reverseMash]
    rw [getD_set _ hi']
    by_cases he : i' = i
    · subst he
      rw [ite_eq_left rfl]
      have hw : lw (f.v .v0) b = (Spec.Rc2.scheduleAt m p).getD (J b) 0 := by
        have hj : J b < 64 := index_lt _
        have e0 : (I (4 * b)).toNat = 2 * J b := by
          rw [hI _ (by omega), show 4 * b % 4 = 0 by omega, show 4 * b / 4 = b by omega]; rfl
        have e1 : (I (4 * b + 1)).toNat = 2 * J b + 1 := by
          rw [hI _ (by omega), show (4 * b + 1) % 4 = 1 by omega,
            show (4 * b + 1) / 4 = b by omega]; rfl
        rw [lw_bytes, f0 _ (by omega), f0 _ (by omega), e0, e1, tab _ (by omega),
          tab _ (by omega), scheduleAt_getD _ _ _ hj]
      have : lw (s'.v (wreg h i')) b = lw (s.v (wreg h i')) b - lw (f.v .v0) b := by
        simp only [s', lw, v_setV_self, vword_map2 _ _ _ hb]
        rw [setWidth16_sub, keepV _ wi.1 wi.2.1 wi.2.2.1 wi.2.2.2.1 wi.2.2.2.2.1 wi.2.2.2.2.2.1]
      have hJ : J b = ((vs b).getD ((i' + 3) % 4) 0 &&& 63).toNat := by
        simp only [J, W]; rw [wreg_mod h (i' + 3), hv _ (Nat.mod_lt _ (by decide)) b hb]
      rw [this, hw, hv i' hi' b hb, hJ]
    · obtain ⟨o1, -, -, -⟩ := regs_other h i i' hh hi hi' he
      have wi' := wreg_ne h i' hh
      rw [ite_eq_right he, ← hv i' hi' b hb]
      simp only [s', v_setV_of_ne _ _ o1]
      rw [keepV _ wi'.1 wi'.2.1 wi'.2.2.1 wi'.2.2.2.1 wi'.2.2.2.2.1 wi'.2.2.2.2.2.1]
  · simp only [s', v_setV_of_ne _ _ h0]
    exact keepV r a0 a1 a2 a3 a4 a5
  · have k₉ : Keep [.x9, .x6] s s₉ :=
      ⟨fun r hr => by
        have h9 : ¬r = .x9 := fun e => hr (by simp [e])
        simp only [s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, gpr_setV, gpr_write_of_ne _ _ _ h9],
        rfl, rfl, rfl⟩
    exact k₉.trans ((dk.weaken (by simp)).trans
      ⟨fun r _ => by simp only [s', gpr_setV, fv.gpr], by simp only [s', mem_setV, fv.mem],
        by simp only [s', rd_setV, fv.rd], by simp only [s', wr_setV, fv.wr]⟩)

end VG.Proof.Rc2.AArch64.Vec
