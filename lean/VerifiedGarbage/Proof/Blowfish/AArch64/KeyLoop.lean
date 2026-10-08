import VerifiedGarbage.Proof.Blowfish.AArch64.Ecb
import VerifiedGarbage.Proof.Blowfish.KeySched

/-!
# Key expansion: the 521 encryptions

Each encryption runs the batch code's sixteen rounds on lane 0 of `A` and
`B`, under the schedule as written so far, and its output replaces the
next two entries (`replace`): the P-array's, as words, then the S-boxes',
a byte per plane. `encryptions_run`: after the 521, the schedule is
`expandKey`'s.
-/

namespace VG.Proof.Blowfish.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Blowfish.AArch64
open VG.Spec.Blowfish VG.Proof.Blowfish
open VG.AArch64.Tbl (VOnly)

theorem exec_strb {s : State} {t n : Reg} {off : Nat} (ho : off < 4096)
    (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 1) :
    exec (.strb t n off) s =
      some { s with mem := s.mem.write (s.gpr n + BitVec.ofNat 64 off) 1 ((s.read .w t).setWidth 8) } := by
  simp only [exec, addr, Nat.mod_one, show off < 4096 * 1 by omega, and_self, ite_true, Option.bind_some,
    State.store, h]

theorem exec_umov_w0 (s : State) (d : Reg) (n : VReg) :
    exec (.umov .w d n 0) s = some (s.write .w d (vword (s.v n) 0)) := rfl

theorem read_write_w (s : State) (r : Reg) (v : BitVec 32) : (s.write .w r v).read .w r = v := by
  simp [State.read, State.write, Size.bits]

theorem shr_byte (x : BitVec 32) (k : Nat) : (x >>> k).setWidth 8 = x.extractLsb' k 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb', hi,
    decide_true, Bool.true_and]

theorem set!_eq_set {α : Type} {n : Nat} (xs : Vector α n) {i : Nat} (h : i < n) (x : α) :
    xs.set! i x = xs.set i x h := by
  apply Vector.toArray_inj.mp
  simp [Vector.toArray_set!, Array.set!_eq_setIfInBounds, Array.setIfInBounds, h]

/-- The bytes of the word in `w` at offsets `e`, `256 + e`, `512 + e` and
`768 + e` of `x14`. -/
theorem storeEntry_run {t : State} {w : Reg} (hw : w ≠ .x13) {e : Nat} (he : e < 2)
    (hW : ∀ b < 4, InRegions t.wr (t.gpr .x14 + BitVec.ofNat 64 (256 * b + e)) 1) :
    ∃ t', runBlock isa (storeEntry w e) t = some t' ∧
      t'.mem = (((t.mem.write (t.gpr .x14 + BitVec.ofNat 64 (256 * 0 + e)) 1
          ((t.read .w w).extractLsb' 0 8)).write
        (t.gpr .x14 + BitVec.ofNat 64 (256 * 1 + e)) 1 ((t.read .w w).extractLsb' 8 8)).write
        (t.gpr .x14 + BitVec.ofNat 64 (256 * 2 + e)) 1 ((t.read .w w).extractLsb' 16 8)).write
        (t.gpr .x14 + BitVec.ofNat 64 (256 * 3 + e)) 1 ((t.read .w w).extractLsb' 24 8) ∧
      (∀ r, r ≠ .x13 → t'.gpr r = t.gpr r) ∧ t' = { t with gpr := t'.gpr, mem := t'.mem } := by
  let W := t.read .w w
  let wb (u : State) (o : Nat) (v : BitVec 8) : State :=
    { u with mem := u.mem.write (u.gpr .x14 + BitVec.ofNat 64 o) 1 v }
  let t₁ := wb t e ((t.read .w w).setWidth 8)
  let t₂ := t₁.write .w .x13 (t₁.read .w w >>> 8)
  let t₃ := wb t₂ (256 + e) ((t₂.read .w .x13).setWidth 8)
  let t₄ := t₃.write .w .x13 (t₃.read .w w >>> 16)
  let t₅ := wb t₄ (512 + e) ((t₄.read .w .x13).setWidth 8)
  let t₆ := t₅.write .w .x13 (t₅.read .w w >>> 24)
  let t₇ := wb t₆ (768 + e) ((t₆.read .w .x13).setWidth 8)
  have g₁₄ : ∀ (u : State) (v : BitVec 32), (u.write .w .x13 v).gpr .x14 = u.gpr .x14 := fun u v =>
    gpr_write_of_ne u .w v (by decide)
  have rW : ∀ (u : State) (v : BitVec 32), (u.write .w .x13 v).read .w w = u.read .w w := fun u v => by
    simp only [State.read, gpr_write_of_ne u .w v hw]
  refine ⟨t₇, ?_, ?_, fun r hr => ?_, rfl⟩
  · rw [storeEntry, runBlock_cons, exec_strb (by omega) (by simpa using hW 0 (by decide)), runStep_some,
      runBlock_cons, exec_lsr_w (by decide), runStep_some, runBlock_cons,
      exec_strb (by omega) (by exact hW 1 (by decide)), runStep_some,
      runBlock_cons, exec_lsr_w (by decide), runStep_some, runBlock_cons,
      exec_strb (by omega) (by exact hW 2 (by decide)), runStep_some,
      runBlock_cons, exec_lsr_w (by decide), runStep_some, runBlock_cons,
      exec_strb (by omega) (by exact hW 3 (by decide)), runStep_some, runBlock_nil]
  · have hm : ∀ u o v, (wb u o v).mem = u.mem.write (u.gpr .x14 + BitVec.ofNat 64 o) 1 v := fun _ _ _ => rfl
    have hg : ∀ u o v, (wb u o v).gpr = u.gpr := fun _ _ _ => rfl
    have hr : ∀ u o v sz r, (wb u o v).read sz r = u.read sz r := fun _ _ _ _ _ => rfl
    have h8 : ∀ x : BitVec 32, x.setWidth 8 = x.extractLsb' 0 8 := fun x => by
      apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]
    simp only [t₇, t₆, t₅, t₄, t₃, t₂, t₁, hm, hg, hr, mem_write, g₁₄, read_write_w, rW,
      Nat.mul_zero, Nat.zero_add, Nat.mul_one, shr_byte]
    rw [h8]
  · simp only [wb, t₇, t₆, t₅, t₄, t₃, t₂, t₁, gpr_write_of_ne _ .w _ hr]

/-! ## Replacing two entries -/

/-- The S-box entries written after `j` encryptions. -/
def sDone (j : Nat) : Nat := 2 * (j - 9)

/-- The stores of `replace`. -/
def storeOut : Prog isa :=
  .ite (.nonzero .x .x9)
    (.block [.str .w .x6 .x12 0, .str .w .x8 .x12 4, .addImm .x .x12 .x12 8, .subImm .x .x9 .x9 1])
    (.seq (.block (storeEntry .x6 0 ++ storeEntry .x8 1 ++
        [.addImm .x .x14 .x14 2, .subImm .x .x10 .x10 2]))
      (.ite (.zero .x .x10) (.block [.addImm .x .x14 .x14 768, .movz .x .x10 256 0]) (.block [])))

theorem replace_eq : replace =
    .seq (.block [.umov .w .x6 (bReg 0) 0, .umov .w .x8 (aReg 0) 0])
      (.seq storeOut (.block [.vop (.mov .v0 (aReg 0)), .vop (.mov (aReg 0) (bReg 0)),
        .vop (.mov (bReg 0) .v0), .subImm .x .x15 .x15 1])) := rfl

/-- Where the `j`-th output goes. -/
structure StoreIn (S : Addr) (j : Nat) (t : State) : Prop where
  lt : j < 521
  wr : ∀ off n, off + n ≤ 4168 → InRegions t.wr (S + BitVec.ofNat 64 off) n
  x9 : t.gpr .x9 = BitVec.ofNat 64 (9 - j)
  x12 : t.gpr .x12 = S + BitVec.ofNat 64 (4096 + 8 * min j 9)
  x14 : t.gpr .x14 = S + BitVec.ofNat 64 (1024 * (sDone j / 256) + sDone j % 256)
  x10 : t.gpr .x10 = BitVec.ofNat 64 (256 - sDone j % 256)

/-- The registers `storeOut` writes. -/
abbrev StoreRegs (r : Reg) : Prop := r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x12 ∧ r ≠ .x13 ∧ r ≠ .x14

structure StoreOut (S : Addr) (j : Nat) (t t' : State) : Prop where
  sched : scheduleAt t'.mem S =
    ((scheduleAt t.mem S).set! (2 * j) (t.read .w .x6)).set! (2 * j + 1) (t.read .w .x8)
  x9 : t'.gpr .x9 = BitVec.ofNat 64 (9 - (j + 1))
  x12 : t'.gpr .x12 = S + BitVec.ofNat 64 (4096 + 8 * min (j + 1) 9)
  x14 : t'.gpr .x14 = S + BitVec.ofNat 64 (1024 * (sDone (j + 1) / 256) + sDone (j + 1) % 256)
  x10 : t'.gpr .x10 = BitVec.ofNat 64 (256 - sDone (j + 1) % 256)
  frame : Frame [⟨S, 4168⟩] t.mem t'.mem
  gpr : ∀ r, StoreRegs r → t'.gpr r = t.gpr r
  eq : t' = { t with gpr := t'.gpr, mem := t'.mem }

theorem ofNat_sub_one {a : Nat} (h : 0 < a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 1 = BitVec.ofNat 64 (a - 1) := by
  apply BitVec.eq_of_toNat_eq; simp; omega

theorem ofNat_sub_two {a : Nat} (h : 2 ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 2 = BitVec.ofNat 64 (a - 2) := by
  apply BitVec.eq_of_toNat_eq; simp; omega

/-- The first nine outputs go to the P-array. -/
theorem storeP_run {S : Addr} {j : Nat} {t : State} (I : StoreIn S j t) (hj : j < 9) :
    WP isa storeOut t (StoreOut S j t) := by
  apply WP.ite true (eval_nonzero t .x9 I.x9 (by omega) |>.trans (by simp; omega)) _ (fun h => nomatch h)
  intro _
  have a₀ : t.gpr .x12 + BitVec.ofNat 64 0 = S + BitVec.ofNat 64 (4096 + 4 * (2 * j)) := by
    rw [I.x12, Offset.add_add]; congr 2; omega
  have a₄ : t.gpr .x12 + BitVec.ofNat 64 4 = S + BitVec.ofNat 64 (4096 + 4 * (2 * j + 1)) := by
    rw [I.x12, Offset.add_add]; congr 2; omega
  let t₁ : State := { t with mem := t.mem.writeW (t.gpr .x12 + BitVec.ofNat 64 0) ((t.gpr .x6).setWidth 32) }
  let t₂ : State := { t₁ with mem := t₁.mem.writeW (t₁.gpr .x12 + BitVec.ofNat 64 4) ((t₁.gpr .x8).setWidth 32) }
  let t₃ := t₂.write .x .x12 (t₂.read .x .x12 + BitVec.ofNat _ 8)
  let t₄ := t₃.write .x .x9 (t₃.read .x .x9 - BitVec.ofNat _ 1)
  have m₄ : t₄.mem = (t.mem.writeW (S + BitVec.ofNat 64 (4096 + 4 * (2 * j))) (t.read .w .x6)).writeW
      (S + BitVec.ofNat 64 (4096 + 4 * (2 * j + 1))) (t.read .w .x8) := by
    show (t.mem.writeW (t.gpr .x12 + BitVec.ofNat 64 0) _).writeW (t.gpr .x12 + BitVec.ofNat 64 4) _ = _
    rw [a₀, a₄]; rfl
  refine WP.of_runBlock ⟨t₄, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl⟩⟩
  · rw [runBlock_cons, exec_str_w (by decide) (by rw [a₀]; exact I.wr _ _ (by omega)), runStep_some,
      runBlock_cons, exec_str_w (by decide) (by show InRegions t.wr (t.gpr .x12 + _) 4; rw [a₄]; exact I.wr _ _ (by omega)),
      runStep_some,
      runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons, exec_subImm_x (by decide),
      runStep_some, runBlock_nil]
  · rw [m₄, scheduleAt_writeW_P _ _ (by omega), scheduleAt_writeW_P _ _ (by omega),
      set!_eq_set _ (by omega), set!_eq_set _ (by omega)]
  · simp only [t₄, t₃, gpr_write_self, State.read, BitVec.setWidth_eq,
      gpr_write_of_ne _ .x _ (by decide : Reg.x9 ≠ .x12)]
    show t.gpr .x9 - _ = _
    rw [I.x9, ofNat_sub_one (by omega) (by omega)]; congr 1
  · simp only [t₄, t₃, gpr_write_of_ne _ .x _ (by decide : Reg.x12 ≠ .x9), gpr_write_self, State.read,
      BitVec.setWidth_eq]
    show t.gpr .x12 + _ = _
    rw [I.x12, Offset.add_add]; congr 2; omega
  · simp only [t₄, t₃, gpr_write_of_ne _ .x _ (by decide : Reg.x14 ≠ .x9),
      gpr_write_of_ne _ .x _ (by decide : Reg.x14 ≠ .x12)]
    show t.gpr .x14 = _
    rw [I.x14, sDone, sDone, show j + 1 - 9 = j - 9 by omega]
  · simp only [t₄, t₃, gpr_write_of_ne _ .x _ (by decide : Reg.x10 ≠ .x9),
      gpr_write_of_ne _ .x _ (by decide : Reg.x10 ≠ .x12)]
    show t.gpr .x10 = _
    rw [I.x10, sDone, sDone, show j + 1 - 9 = j - 9 by omega]
  · rw [m₄]
    refine (Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_ |>.writeW (List.mem_singleton_self _) _ ?_
    · exact Offset.contains_base S (by simp only [Size.bits]; omega) (by omega)
    · exact Offset.contains_base S (by simp only [Size.bits]; omega) (by omega)
  · simp only [t₄, t₃, gpr_write_of_ne _ .x _ hr.1, gpr_write_of_ne _ .x _ hr.2.2.1]
    rfl

/-- Entry `2 j` is byte `sDone j` of the S-boxes, at its offset in `x14`. -/
theorem entryOff_sbox {j b : Nat} (hj : 9 ≤ j) (hj' : j < 521) (k : Nat) (hk : k < 2) :
    1024 * (sDone j / 256) + sDone j % 256 + (256 * b + k) = entryOff (2 * j + k) b := by
  unfold entryOff sDone; simp only [show ¬ 2 * j + k < 18 by omega, ite_false]; omega

/-- The other 512 outputs go to the S-boxes, a byte per plane. -/
theorem storeS_run {S : Addr} {j : Nat} {t : State} (I : StoreIn S j t) (hj : 9 ≤ j) :
    WP isa storeOut t (StoreOut S j t) := by
  have hlt := I.lt
  apply WP.ite false (eval_nonzero t .x9 I.x9 (by omega) |>.trans (by simp; omega)) (fun h => nomatch h)
  intro _
  have ad : ∀ (u : State), u.gpr .x14 = t.gpr .x14 → ∀ k < 2, ∀ b < 4,
      u.gpr .x14 + BitVec.ofNat 64 (256 * b + k) = S + BitVec.ofNat 64 (entryOff (2 * j + k) b) :=
    fun u hu k hk b hb => by rw [hu, I.x14, Offset.add_add, entryOff_sbox hj hlt k hk]
  have inS : ∀ k < 2, ∀ b < 4, entryOff (2 * j + k) b + 1 ≤ 4168 := fun k hk b hb => by
    have := entryOff_lt (i := 2 * j + k) (b := b) (by omega) hb; omega
  have W : ∀ (u : State), u.gpr .x14 = t.gpr .x14 → u.wr = t.wr → ∀ k < 2, ∀ b < 4,
      InRegions u.wr (u.gpr .x14 + BitVec.ofNat 64 (256 * b + k)) 1 := fun u hu hw k hk b hb => by
    rw [ad u hu k hk b hb, hw]; exact I.wr _ _ (inS k hk b hb)
  obtain ⟨t₁, r₁, m₁, g₁, e₁⟩ := storeEntry_run (t := t) (w := .x6) (by decide) (e := 0) (by decide)
    (W t rfl rfl 0 (by decide))
  have h14₁ : t₁.gpr .x14 = t.gpr .x14 := g₁ _ (by decide)
  have wr₁ : t₁.wr = t.wr := by rw [e₁]
  obtain ⟨t₂, r₂, m₂, g₂, e₂⟩ := storeEntry_run (t := t₁) (w := .x8) (by decide) (e := 1) (by decide)
    (W t₁ h14₁ wr₁ 1 (by decide))
  have h14₂ : t₂.gpr .x14 = t.gpr .x14 := (g₂ _ (by decide)).trans h14₁
  have r8 : t₁.read .w .x8 = t.read .w .x8 := by simp only [State.read, g₁ _ (by decide : Reg.x8 ≠ .x13)]
  -- the memory
  have mem₂ : t₂.mem = (((((((t.mem.write (S + BitVec.ofNat 64 (entryOff (2 * j) 0)) 1
        ((t.read .w .x6).extractLsb' 0 8)).write
      (S + BitVec.ofNat 64 (entryOff (2 * j) 1)) 1 ((t.read .w .x6).extractLsb' 8 8)).write
      (S + BitVec.ofNat 64 (entryOff (2 * j) 2)) 1 ((t.read .w .x6).extractLsb' 16 8)).write
      (S + BitVec.ofNat 64 (entryOff (2 * j) 3)) 1 ((t.read .w .x6).extractLsb' 24 8)).write
      (S + BitVec.ofNat 64 (entryOff (2 * j + 1) 0)) 1 ((t.read .w .x8).extractLsb' 0 8)).write
      (S + BitVec.ofNat 64 (entryOff (2 * j + 1) 1)) 1 ((t.read .w .x8).extractLsb' 8 8)).write
      (S + BitVec.ofNat 64 (entryOff (2 * j + 1) 2)) 1 ((t.read .w .x8).extractLsb' 16 8)).write
      (S + BitVec.ofNat 64 (entryOff (2 * j + 1) 3)) 1 ((t.read .w .x8).extractLsb' 24 8) := by
    rw [m₂, m₁, r8, ad t₁ h14₁ 1 (by decide) 0 (by decide), ad t₁ h14₁ 1 (by decide) 1 (by decide),
      ad t₁ h14₁ 1 (by decide) 2 (by decide), ad t₁ h14₁ 1 (by decide) 3 (by decide),
      ad t rfl 0 (by decide) 0 (by decide), ad t rfl 0 (by decide) 1 (by decide),
      ad t rfl 0 (by decide) 2 (by decide), ad t rfl 0 (by decide) 3 (by decide), Nat.add_zero]
  have sched₂ : scheduleAt t₂.mem S =
      ((scheduleAt t.mem S).set! (2 * j) (t.read .w .x6)).set! (2 * j + 1) (t.read .w .x8) := by
    rw [mem₂, scheduleAt_write_bytes _ _ (by omega), scheduleAt_write_bytes _ _ (by omega),
      set!_eq_set _ (by omega), set!_eq_set _ (by omega)]
  have fr₂ : Frame [⟨S, 4168⟩] t.mem t₂.mem := by
    have c : ∀ k < 2, ∀ b < 4, (⟨S, 4168⟩ : Region).Contains (S + BitVec.ofNat 64 (entryOff (2 * j + k) b)) 1 :=
      fun k hk b hb => Offset.contains_base S (inS k hk b hb) (by have := inS k hk b hb; omega)
    have mm := List.mem_singleton_self (⟨S, 4168⟩ : Region)
    rw [mem₂]
    exact ((((((((Frame.refl _ _).write mm _ (c 0 (by decide) 0 (by decide))).write mm _
      (c 0 (by decide) 1 (by decide))).write mm _ (c 0 (by decide) 2 (by decide))).write mm _
      (c 0 (by decide) 3 (by decide))).write mm _ (c 1 (by decide) 0 (by decide))).write mm _
      (c 1 (by decide) 1 (by decide))).write mm _ (c 1 (by decide) 2 (by decide))).write mm _
      (c 1 (by decide) 3 (by decide))
  -- the registers
  let t₃ := t₂.write .x .x14 (t₂.read .x .x14 + BitVec.ofNat _ 2)
  let t₄ := t₃.write .x .x10 (t₃.read .x .x10 - BitVec.ofNat _ 2)
  have hg₂ : ∀ r, r ≠ .x13 → t₂.gpr r = t.gpr r := fun r hr => (g₂ r hr).trans (g₁ r hr)
  have e₂' : t₂ = { t with gpr := t₂.gpr, mem := t₂.mem } := by rw [e₂, e₁]
  have hr10 : sDone j % 256 ≤ 254 := by unfold sDone; omega
  have x10₄ : t₄.gpr .x10 = BitVec.ofNat 64 (256 - sDone j % 256 - 2) := by
    simp only [t₄, t₃, gpr_write_self, State.read, BitVec.setWidth_eq,
      gpr_write_of_ne _ .x _ (by decide : Reg.x10 ≠ .x14)]
    rw [hg₂ _ (by decide), I.x10, ofNat_sub_two (by omega) (by omega)]
  have x14₄ : t₄.gpr .x14 = S + BitVec.ofNat 64 (1024 * (sDone j / 256) + sDone j % 256 + 2) := by
    simp only [t₄, t₃, gpr_write_of_ne _ .x _ (by decide : Reg.x14 ≠ .x10), gpr_write_self, State.read,
      BitVec.setWidth_eq]
    rw [h14₂, I.x14, Offset.add_add]
  have g₄' : ∀ r, r ≠ .x13 → r ≠ .x14 → r ≠ .x10 → t₄.gpr r = t.gpr r := fun r h13 h14 h10 => by
    simp only [t₄, t₃, gpr_write_of_ne _ .x _ h10, gpr_write_of_ne _ .x _ h14]
    exact hg₂ r h13
  have g₄ : ∀ r, StoreRegs r → t₄.gpr r = t.gpr r := fun r hr => g₄' r hr.2.2.2.1 hr.2.2.2.2 hr.2.1
  have e₄ : t₄ = { t with gpr := t₄.gpr, mem := t₄.mem } := by
    simp only [t₄, t₃, State.write]; rw [e₂']
  have x9' : t.gpr .x9 = BitVec.ofNat 64 (9 - (j + 1)) := by rw [I.x9, show 9 - j = 9 - (j + 1) by omega]
  have x12' : t.gpr .x12 = S + BitVec.ofNat 64 (4096 + 8 * min (j + 1) 9) := by
    rw [I.x12, show min j 9 = min (j + 1) 9 by omega]
  apply WP.seq
  refine WP.of_runBlock ⟨t₄, ?_, ?_⟩
  · rw [List.append_assoc]
    refine cat_run r₁ (cat_run r₂ ?_)
    rw [runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons, exec_subImm_x (by decide),
      runStep_some, runBlock_nil]
  apply WP.ite _ (eval_zero t₄ .x10 x10₄ (by omega))
  · intro hz
    have h254 : sDone j % 256 = 254 := by simp at hz; omega
    let t₅ := t₄.write .x .x14 (t₄.read .x .x14 + BitVec.ofNat _ 768)
    let t₆ := t₅.write .x .x10 ((256 : BitVec 16).setWidth 64 <<< (16 * 0))
    refine WP.of_runBlock ⟨t₆, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_⟩⟩
    · rw [runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons]; rfl
    · exact sched₂
    · simp only [t₆, t₅, gpr_write_of_ne _ .x _ (by decide : Reg.x9 ≠ .x10),
        gpr_write_of_ne _ .x _ (by decide : Reg.x9 ≠ .x14)]
      rw [g₄' _ (by decide) (by decide) (by decide)]; exact x9'
    · simp only [t₆, t₅, gpr_write_of_ne _ .x _ (by decide : Reg.x12 ≠ .x10),
        gpr_write_of_ne _ .x _ (by decide : Reg.x12 ≠ .x14)]
      rw [g₄' _ (by decide) (by decide) (by decide)]; exact x12'
    · simp only [t₆, t₅, gpr_write_of_ne _ .x _ (by decide : Reg.x14 ≠ .x10), gpr_write_self, State.read,
        BitVec.setWidth_eq]
      rw [x14₄, Offset.add_add]; congr 2; unfold sDone at h254 ⊢; omega
    · simp only [t₆, gpr_write_self]
      rw [show sDone (j + 1) % 256 = 0 by unfold sDone at h254 ⊢; omega]; rfl
    · exact fr₂
    · simp only [t₆, t₅, gpr_write_of_ne _ .x _ hr.2.1, gpr_write_of_ne _ .x _ hr.2.2.2.2]
      exact g₄ r hr
    · simp only [t₆, t₅, State.write]; rw [e₄]
  · intro hz
    have h254 : sDone j % 256 ≠ 254 := by simp at hz; omega
    refine WP.block_nil ⟨sched₂, ?_, ?_, ?_, ?_, fr₂, g₄, e₄⟩
    · rw [g₄' _ (by decide) (by decide) (by decide)]; exact x9'
    · rw [g₄' _ (by decide) (by decide) (by decide)]; exact x12'
    · rw [x14₄]; congr 2; unfold sDone at h254 ⊢; omega
    · rw [x10₄]; congr 1; unfold sDone at h254 ⊢; omega

/-! ## The loop -/

/-- The general-purpose registers the encryptions write. -/
def encGprs : List Reg := [.x5, .x6, .x7, .x8, .x9, .x10, .x12, .x13, .x14, .x15]

/-- What the loop needs of the state it starts in: the schedule at `x2`, writable. -/
structure EncEnv (S : Addr) (s₀ : State) : Prop where
  x2 : s₀.gpr .x2 = S
  wrS : ∀ off n, off + n ≤ 4168 → InRegions s₀.wr (S + BitVec.ofNat 64 off) n
  consts : Consts s₀

/-- After `j` encryptions. -/
structure EncInv (key : List Byte) (S : Addr) (s₀ : State) (j : Nat) (u : State) : Prop where
  le : j ≤ 521
  sched : scheduleAt u.mem S = (ksIter key j).1
  xl : vword (u.v .v4) 0 = (ksIter key j).2.1
  xr : vword (u.v .v8) 0 = (ksIter key j).2.2
  x15 : u.gpr .x15 = BitVec.ofNat 64 (521 - j)
  x9 : u.gpr .x9 = BitVec.ofNat 64 (9 - j)
  x12 : u.gpr .x12 = S + BitVec.ofNat 64 (4096 + 8 * min j 9)
  x14 : u.gpr .x14 = S + BitVec.ofNat 64 (1024 * (sDone j / 256) + sDone j % 256)
  x10 : u.gpr .x10 = BitVec.ofNat 64 (256 - sDone j % 256)
  frame : Frame [⟨S, 4168⟩] s₀.mem u.mem
  gpr : ∀ r, r ∉ encGprs → u.gpr r = s₀.gpr r
  v : ∀ r, r ∉ roundRegs → u.v r = s₀.v r
  eq : u = { s₀ with gpr := u.gpr, v := u.v, mem := u.mem }

theorem enc_step {key : List Byte} {S : Addr} {s₀ : State} (E : EncEnv S s₀) {j : Nat} (hj : j < 521)
    {u : State} (I : EncInv key S s₀ j u) :
    WP isa (.seq (cipher .x2 true) replace) u (EncInv key S s₀ (j + 1)) := by
  have hrd : u.rd = s₀.rd := by rw [I.eq]
  have hwr : u.wr = s₀.wr := by rw [I.eq]
  have x2 : u.gpr .x2 = S := (I.gpr _ (by decide)).trans E.x2
  have hS : SchedIn u .x2 := fun off n h => by
    rw [x2, hwr]
    obtain ⟨r, hr, hc⟩ := E.wrS off n h
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have hc : Consts u := ⟨fun e he => by rw [I.v _ c_notin.1]; exact E.consts.1 e he,
    fun e he => by rw [I.v _ c_notin.2]; exact E.consts.2 e he⟩
  apply WP.seq
  refine WP.mono (cipher_run hS hc (by decide) true) fun u₁ ⟨hl, o₁⟩ => ?_
  obtain ⟨hlb, hla⟩ := hl 0 (by decide)
  let K := (ksIter key j).1
  let out := encryptWords K (ksIter key j).2.1 (ksIter key j).2.2
  have o8 : vword (u₁.v .v8) 0 = out.1 := by
    have : vword (u₁.v .v8) 0 = (feistel (scheduleAt u.mem (u.gpr .x2)) (order true)
      (vword (u.v .v4) 0) (vword (u.v .v8) 0)).1 := hlb
    rw [this, x2, I.sched, order_true, I.xl, I.xr]; rfl
  have o4 : vword (u₁.v .v4) 0 = out.2 := by
    have : vword (u₁.v .v4) 0 = (feistel (scheduleAt u.mem (u.gpr .x2)) (order true)
      (vword (u.v .v4) 0) (vword (u.v .v8) 0)).2 := hla
    rw [this, x2, I.sched, order_true, I.xl, I.xr]; rfl
  rw [replace_eq]
  apply WP.seq
  let u₁' := u₁.write .w .x6 (vword (u₁.v (bReg 0)) 0)
  let u₂ := u₁'.write .w .x8 (vword (u₁'.v (aReg 0)) 0)
  refine WP.of_runBlock ⟨u₂, rfl, ?_⟩
  have g₂ : ∀ r, r ∉ encGprs → u₂.gpr r = u.gpr r := fun r hr => by
    simp only [encGprs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [u₂, u₁', gpr_write_of_ne _ .w _ hr.2.2.2.1, gpr_write_of_ne _ .w _ hr.2.1]
    exact o₁.g r (by simp [hr.1, hr.2.1, hr.2.2.1])
  have g₂' : ∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → u₂.gpr r = u.gpr r := fun r h5 h6 h7 h8 => by
    simp only [u₂, u₁', gpr_write_of_ne _ .w _ h8, gpr_write_of_ne _ .w _ h6]
    exact o₁.g r (by simp [h5, h6, h7])
  have wr₂ : u₂.wr = s₀.wr := by rw [show u₂.wr = u₁.wr from rfl, o₁.wr, hwr]
  have mem₂ : u₂.mem = u.mem := o₁.mem
  have SI : StoreIn S j u₂ := by
    refine ⟨hj, fun off n h => by rw [wr₂]; exact E.wrS off n h, ?_, ?_, ?_, ?_⟩
    · rw [g₂' _ (by decide) (by decide) (by decide) (by decide)]; exact I.x9
    · rw [g₂' _ (by decide) (by decide) (by decide) (by decide)]; exact I.x12
    · rw [g₂' _ (by decide) (by decide) (by decide) (by decide)]; exact I.x14
    · rw [g₂' _ (by decide) (by decide) (by decide) (by decide)]; exact I.x10
  have st : WP isa storeOut u₂ (StoreOut S j u₂) :=
    if h : j < 9 then storeP_run SI h else storeS_run SI (by omega)
  apply WP.seq
  refine WP.mono st fun u₃ O => ?_
  have v₃ : u₃.v = u₁.v := by rw [O.eq]; rfl
  let a := u₃.setV .v0 (u₃.v (aReg 0))
  let b := a.setV (aReg 0) (a.v (bReg 0))
  let c := b.setV (bReg 0) (b.v .v0)
  let u₄ := c.write .x .x15 (c.read .x .x15 - BitVec.ofNat _ 1)
  have v₄ : ∀ r, r ≠ .v0 → r ≠ .v4 → r ≠ .v8 → u₄.v r = u₁.v r := fun r h0 h4 h8 => by
    simp only [u₄, c, b, a, v_write, v_setV_of_ne _ _ h0, v_setV_of_ne _ _ h4, v_setV_of_ne _ _ h8,
      show bReg 0 = .v8 from rfl, show aReg 0 = .v4 from rfl, v₃]
  have g₄ : ∀ r, r ≠ .x15 → u₄.gpr r = u₃.gpr r := fun r hr => by
    simp only [u₄, gpr_write_of_ne _ .x _ hr]; rfl
  refine WP.of_runBlock ⟨u₄, ?_, ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_,
    fun r hr => ?_, ?_⟩⟩
  · rw [runBlock_cons, exec_vmov, runStep_some, runBlock_cons, exec_vmov, runStep_some, runBlock_cons,
      exec_vmov, runStep_some, runBlock_cons, exec_subImm_x (by decide), runStep_some, runBlock_nil]
  · have r6 : u₂.read .w .x6 = out.1 := by
      have : u₂.gpr .x6 = u₁'.gpr .x6 := gpr_write_of_ne _ .w _ (by decide)
      show (u₂.gpr .x6).setWidth 32 = _
      rw [this]; exact (read_write_w u₁ .x6 _).trans o8
    have r8 : u₂.read .w .x8 = out.2 := by rw [read_write_w]; exact o4
    rw [show u₄.mem = u₃.mem from rfl, O.sched, mem₂, I.sched, r6, r8, ksIter_succ]; rfl
  · show vword (u₃.v .v8) 0 = _
    rw [v₃, o8, ksIter_succ]; rfl
  · show vword (u₃.v .v4) 0 = _
    rw [v₃, o4, ksIter_succ]; rfl
  · simp only [u₄, gpr_write_self, State.read, BitVec.setWidth_eq]
    show u₃.gpr .x15 - _ = _
    rw [O.gpr _ (by decide), g₂' _ (by decide) (by decide) (by decide) (by decide), I.x15,
      ofNat_sub_one (by omega) (by omega)]
    congr 1
  · rw [g₄ _ (by decide)]; exact O.x9
  · rw [g₄ _ (by decide)]; exact O.x12
  · rw [g₄ _ (by decide)]; exact O.x14
  · rw [g₄ _ (by decide)]; exact O.x10
  · rw [show u₄.mem = u₃.mem from rfl]
    exact I.frame.trans (mem₂ ▸ O.frame)
  · simp only [encGprs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g₄ _ hr.2.2.2.2.2.2.2.2.2, O.gpr _ ⟨hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.1⟩, g₂ r (by simp [encGprs]; omega), I.gpr r (by simp [encGprs]; omega)]
  · have h0 : r ≠ .v0 := fun h => hr (h ▸ by decide)
    have h4 : r ≠ .v4 := fun h => hr (h ▸ by decide)
    have h8 : r ≠ .v8 := fun h => hr (h ▸ by decide)
    rw [v₄ r h0 h4 h8, o₁.v r hr, I.v r hr]
  · rw [show u₄ = { u₃ with gpr := u₄.gpr, v := u₄.v } from rfl, O.eq,
      show u₂ = { u₁ with gpr := u₂.gpr } from rfl, o₁.eq, I.eq]

theorem exec_movi0 (s : State) (d : VReg) : exec (.vop (.movi0 d)) s = some (s.setV d 0) := rfl

theorem exec_movz_x0 (s : State) (d : Reg) (imm : BitVec 16) :
    exec (.movz .x d imm 0) s = some (s.write .x d (imm.setWidth 64 <<< (16 * 0))) := rfl

theorem ksIter_zero (key : List Byte) : ksIter key 0 = (keyed key, 0, 0) := rfl

/-- The 521 encryptions, from the keyed schedule at `x2`. -/
theorem encryptions_run {key : List Byte} {S : Addr} {s₀ : State} (E : EncEnv S s₀)
    (hK : scheduleAt s₀.mem S = keyed key) :
    WP isa encryptions s₀ (EncInv key S s₀ 521) := by
  rw [encryptions]
  apply WP.seq
  let s₁ := ((((((((s₀.setV .v4 0).setV .v8 0).setV .v5 0).setV .v9 0).setV .v6 0).setV .v10 0).setV
    .v7 0).setV .v11 0)
  let s₂ := s₁.write .x .x9 ((9 : BitVec 16).setWidth 64 <<< (16 * 0))
  let s₃ := s₂.write .x .x12 (s₂.read .x .x2 + BitVec.ofNat _ 2048)
  let s₄ := s₃.write .x .x12 (s₃.read .x .x12 + BitVec.ofNat _ 2048)
  let s₅ := s₄.write .x .x14 (s₄.read .x .x2 + BitVec.ofNat _ 0)
  let s₆ := s₅.write .x .x10 ((256 : BitVec 16).setWidth 64 <<< (16 * 0))
  let s₇ := s₆.write .x .x15 ((521 : BitVec 16).setWidth 64 <<< (16 * 0))
  refine WP.of_runBlock ⟨s₇, ?_, ?_⟩
  · rw [show (List.range 4).flatMap (fun k => [Instr.vop (.movi0 (aReg k)), .vop (.movi0 (bReg k))]) =
        [.vop (.movi0 .v4), .vop (.movi0 .v8), .vop (.movi0 .v5), .vop (.movi0 .v9), .vop (.movi0 .v6),
          .vop (.movi0 .v10), .vop (.movi0 .v7), .vop (.movi0 .v11)] from rfl]
    simp only [List.cons_append, List.nil_append]
    rw [runBlock_cons, exec_movi0, runStep_some, runBlock_cons, exec_movi0, runStep_some,
      runBlock_cons, exec_movi0, runStep_some, runBlock_cons, exec_movi0, runStep_some,
      runBlock_cons, exec_movi0, runStep_some, runBlock_cons, exec_movi0, runStep_some,
      runBlock_cons, exec_movi0, runStep_some, runBlock_cons, exec_movi0, runStep_some,
      runBlock_cons, exec_movz_x0, runStep_some, runBlock_cons, exec_addImm_x (by decide), runStep_some,
      runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons, exec_addImm_x (by decide),
      runStep_some, runBlock_cons, exec_movz_x0, runStep_some, runBlock_cons, exec_movz_x0, runStep_some,
      runBlock_nil]
  refine WP.loop (M := isa) (fun m u => ∃ j, j < 521 ∧ m = 521 - j ∧ EncInv key S s₀ j u) ?_ 521 s₇
    ⟨0, by omega, rfl, ?_⟩
  · intro m u ⟨j, hj, hm, I⟩
    refine WP.mono (enc_step E hj I) fun u' I' => ?_
    have flag := eval_nonzero u' .x15 I'.x15 (by omega)
    by_cases h : j + 1 = 521
    · left; exact ⟨by rw [flag]; simp; omega, h ▸ I'⟩
    · right; exact ⟨by rw [flag]; simp; omega, 521 - (j + 1), by omega, j + 1, by omega, rfl, I'⟩
  · have hm : s₇.mem = s₀.mem := by simp only [s₇, s₆, s₅, s₄, s₃, s₂, s₁, mem_write, mem_setV]
    refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, fun r hr => ?_, ?_⟩
    · rw [hm, hK]; rfl
    · simp only [ksIter_zero]
      simp only [s₇, s₆, s₅, s₄, s₃, s₂, s₁, v_write, v_setV_of_ne _ _ (by decide : VReg.v4 ≠ .v11),
        v_setV_of_ne _ _ (by decide : VReg.v4 ≠ .v7), v_setV_of_ne _ _ (by decide : VReg.v4 ≠ .v10),
        v_setV_of_ne _ _ (by decide : VReg.v4 ≠ .v6), v_setV_of_ne _ _ (by decide : VReg.v4 ≠ .v9),
        v_setV_of_ne _ _ (by decide : VReg.v4 ≠ .v5), v_setV_of_ne _ _ (by decide : VReg.v4 ≠ .v8),
        v_setV_self]
      rfl
    · simp only [ksIter_zero]
      simp only [s₇, s₆, s₅, s₄, s₃, s₂, s₁, v_write, v_setV_of_ne _ _ (by decide : VReg.v8 ≠ .v11),
        v_setV_of_ne _ _ (by decide : VReg.v8 ≠ .v7), v_setV_of_ne _ _ (by decide : VReg.v8 ≠ .v10),
        v_setV_of_ne _ _ (by decide : VReg.v8 ≠ .v6), v_setV_of_ne _ _ (by decide : VReg.v8 ≠ .v9),
        v_setV_of_ne _ _ (by decide : VReg.v8 ≠ .v5), v_setV_self]
      rfl
    · simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, State.setV, State.write]
    · simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, State.setV, State.write]
    · simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, State.setV, State.write, State.read, E.x2, Offset.add_add]
    · simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, State.setV, State.write, State.read, E.x2, sDone]
    · simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, State.setV, State.write, sDone]
    · rw [hm]; exact Frame.refl _ _
    · simp only [encGprs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, State.setV, State.write, hr]
    · have : r ∉ halfRegs := fun h => hr (by simp [roundRegs, h])
      simp only [halfRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at this
      simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, State.setV, State.write, this]
    · simp only [s₇, s₆, s₅, s₄, s₃, s₂, s₁, State.setV, State.write]

end VG.Proof.Blowfish.AArch64
