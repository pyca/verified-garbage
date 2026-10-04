import VerifiedGarbage.Proof.Argon2.Arm.CompressContract

/-!
# Argon2 compression on ARMv7: correctness

The prologue saving the caller's registers and `out` (`prologue_ok`), the
initialization of both halves of scratch with X XOR Y (`init_ok`, one word at
a time), the rows and columns (`Proof/Argon2/Arm/Rounds.lean`), and the
epilogue writing the output and restoring the registers: `correct`.
-/

namespace VG.Proof.Argon2.Arm

open VG VG.Arm VG.Spec.Argon2
open VG.Impl.Argon2.Arm (prologue initWord finishWord epilogue saved spill outOff)
open VG.Proof.Sha512.Arm (A A_eq Reg64 rd64 mem_rd contains_A)
open VG.Proof.MdStream.Arm (Upd Mupd wp_ldr wp_str op2_reg readW_writeW_save)
open VG.Proof.Sha512.Arm (wp_eor)

/-- A word of `B + d` after a store at `B + e`, separate from it. -/
theorem readW_writeW_A (m : Mem) (v : BitVec 32) {B : BitVec 32} {d e : Nat}
    (hd : B.toNat + d + 4 ≤ 2 ^ 32) (he : B.toNat + e + 4 ≤ 2 ^ 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (A B e) v).readW (A B d) 32 = m.readW (A B d) 32 := by
  rw [A_eq (by omega), A_eq (by omega)]
  exact readW_writeW_save m _ v (by omega) (by omega) h

theorem spill_slots : Spill.Slots 2048 2088 spill := by decide

theorem saved_slots : Spill.Slots 2048 2084 saved := by decide

theorem saved_restorable : Spill.Restorable .r3 saved := by decide

/-- 32-bit word `i` of X XOR Y. -/
def xy (s₀ : State) (i : Nat) : BitVec 32 :=
  s₀.mem.readW (A (xp s₀) (4 * i)) 32 ^^^ s₀.mem.readW (A (yp s₀) (4 * i)) 32

/-- After the prologue and the first `n` words of the initialization. -/
structure InitInv (s₀ s : State) (n : Nat) : Prop where
  regs : ∀ r, r ≠ .r4 → r ≠ .r5 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [scrR s₀] s₀.mem s.mem
  saved : Spill.Saved s.mem (State.addr (scr s₀)) s₀.gpr spill
  low : Words s.mem (scr s₀) 0 (xy s₀) n
  high : Words s.mem (scr s₀) 1024 (xy s₀) n

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem prologue_ok {rest : List Instr} {Q : State → Prop} (k : ∀ s, InitInv s₀ s 0 → WP isa (.block rest) s Q) :
    WP isa (.block (prologue ++ rest)) s₀ Q := by
  have fits := hp.scr_fits
  unfold prologue
  refine Spill.save_slots_ok spill_slots (by show (scr s₀).toNat + 2088 ≤ _; omega) (fun d h₁ h₂ => ?_) (k _ ⟨fun _ _ _ => rfl, rfl, rfl, rfl,
    ?_, Spill.saveMem_saved _ _ _ _ spill_slots, fun i hi => absurd hi (Nat.not_lt_zero _),
    fun i hi => absurd hi (Nat.not_lt_zero _)⟩)
  · exact ⟨scrR s₀, by simp [hp.wr], Offset.contains_base _ (by omega) (by omega)⟩
  · exact Spill.saveMem_frame_of _ _ (List.mem_singleton_self _) _ _ fun p hpm => by
      have := spill_slots.bound hpm
      exact Offset.contains_base _ (by omega) (by omega)

/-- One word of the initialization. -/
theorem initWord_ok {s : State} {n : Nat} (hn : n < 256) (h : InitInv s₀ s n) :
    WP isa (.block (initWord n)) s (InitInv s₀ · (n + 1)) := by
  have hm : scrR s₀ ∈ [scrR s₀] := List.mem_singleton_self _
  have fits := hp.scr_fits
  unfold initWord
  refine wp_ldr (by omega) (by rw [h.regs _ (by decide) (by decide)]) (hp.in_x h.rd (by omega)) fun s₁ u₁ => ?_
  refine wp_ldr (by omega) (by rw [u₁.other _ (by decide), h.regs _ (by decide) (by decide)])
    (by rw [u₁.rd, u₁.wr]; exact hp.in_y h.rd (by omega)) fun s₂ u₂ => ?_
  refine wp_eor (op2_reg _ _) fun s₃ u₃ => ?_
  have v₃ : s₃.gpr .r4 = xy s₀ n := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, u₁.mem,
      hp.x_frame (h.frame.mono (by simp)) (by omega), hp.y_frame (h.frame.mono (by simp)) (by omega)]; rfl
  have r3 : s₃.gpr .r3 = scr s₀ := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.regs _ (by decide) (by decide)]
  refine wp_str (by omega) (by rw [r3]) (by rw [u₃.wr, u₂.wr, u₁.wr, h.wr]; exact hp.scr_wr rfl (by omega))
    fun s₄ u₄ => ?_
  refine wp_str (by omega) (by rw [u₄.gpr, r3])
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]; exact hp.scr_wr rfl (by omega)) fun s₅ u₅ => WP.block_nil ?_
  have m₅ : s₅.mem = (s.mem.writeW (A (scr s₀) (4 * n)) (xy s₀ n)).writeW (A (scr s₀) (1024 + 4 * n)) (xy s₀ n) := by
    rw [u₅.mem, u₄.gpr, u₄.mem, u₃.mem, u₂.mem, u₁.mem, v₃]
  have r₅ : ∀ e, e + 4 ≤ 4096 → (e + 4 ≤ 4 * n ∨ 4 * n + 4 ≤ e) →
      (e + 4 ≤ 1024 + 4 * n ∨ 1024 + 4 * n + 4 ≤ e) →
      s₅.mem.readW (A (scr s₀) e) 32 = s.mem.readW (A (scr s₀) e) 32 := by
    intro e he h1 h2
    rw [m₅, readW_writeW_A _ _ (by omega) (by omega) h2, readW_writeW_A _ _ (by omega) (by omega) h1]
  refine ⟨fun r h4 h5 => ?_, ?_, ?_, ?_, ?_, fun p hpm => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [u₅.gpr, u₄.gpr, u₃.other _ h4, u₂.other _ h5, u₁.other _ h4, h.regs r h4 h5]
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
  · rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp]
  · rw [m₅]
    exact (h.frame.writeW hm _ (hp.scr_contains (by omega))).writeW hm _ (hp.scr_contains (by omega))
  · have := spill_slots.bound hpm
    have e := r₅ p.2 (by omega) (by omega) (by omega)
    rw [A_eq (by omega)] at e
    rw [e]; exact h.saved p hpm
  · by_cases e : i = n
    · subst e
      rw [m₅, readW_writeW_A _ _ (by omega) (by omega) (by omega), Nat.zero_add, Mem.readW_writeW_self32]
    · rw [r₅ _ (by omega) (by omega) (by omega)]; exact h.low i (by omega)
  · by_cases e : i = n
    · subst e; rw [m₅, Mem.readW_writeW_self32]
    · rw [r₅ _ (by omega) (by omega) (by omega)]; exact h.high i (by omega)

theorem init_ok {s : State} (h : InitInv s₀ s 0) (n : Nat) (hn : n ≤ 256) :
    WP isa (.block ((List.range n).flatMap initWord)) s (InitInv s₀ · n) := by
  induction n with
  | zero => exact WP.block_nil h
  | succ n ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    exact WP.block_append ((ih (by omega)).mono fun t ht => initWord_ok hp (by omega) ht)

end

/-! ## The epilogue -/

/-- Word `i` of the output: the permuted block XOR R, in memory `m`. -/
def outWord (B : BitVec 32) (m : Mem) (i : Nat) : BitVec 32 :=
  m.readW (A B (1024 + 4 * i)) 32 ^^^ m.readW (A B (4 * i)) 32

/-- After the first `n` words of the output, from the state `s₄` after the rounds. -/
structure FinInv (s₀ s₄ s : State) (n : Nat) : Prop where
  r3 : s.gpr .r3 = scr s₀
  r2 : s.gpr .r2 = op s₀
  regs : ∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r2 → s.gpr r = s₄.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [outR s₀] s₄.mem s.mem
  out : Words s.mem (op s₀) 0 (outWord (scr s₀) s₄.mem) n

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem finishWord_ok {s₄ s : State} {n : Nat} (hn : n < 256) (h : FinInv s₀ s₄ s n) :
    WP isa (.block (finishWord n)) s (FinInv s₀ s₄ · (n + 1)) := by
  have hm : outR s₀ ∈ [outR s₀] := List.mem_singleton_self _
  have fits := hp.out_fits
  have sfits := hp.scr_fits
  unfold finishWord
  refine wp_ldr (by omega) (by rw [h.r3]) (hp.in_scr h.wr (by omega)) fun s₁ u₁ => ?_
  refine wp_ldr (by omega) (by rw [u₁.other .r3 (by decide), h.r3])
    (by rw [u₁.rd, u₁.wr]; exact hp.in_scr h.wr (by omega)) fun s₂ u₂ => ?_
  refine wp_eor (op2_reg _ _) fun s₃ u₃ => ?_
  have v₃ : s₃.gpr .r4 = outWord (scr s₀) s₄.mem n := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, u₁.mem, hp.scr_frame h.frame (by omega),
      hp.scr_frame h.frame (by omega)]; rfl
  refine wp_str (by omega) (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.r2])
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact hp.out_wr h.wr (by omega)) fun s₄' u₄ => WP.block_nil ?_
  have m₄ : s₄'.mem = s.mem.writeW (A (op s₀) (4 * n)) (outWord (scr s₀) s₄.mem n) := by
    rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem, v₃]
  refine ⟨?_, ?_, fun r h4 h5 h2 => ?_, ?_, ?_, ?_, ?_, fun i hi => ?_⟩
  · rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.r3]
  · rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.r2]
  · rw [u₄.gpr, u₃.other _ h4, u₂.other _ h5, u₁.other _ h4, h.regs r h4 h5 h2]
  · rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
  · rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp]
  · rw [m₄]; exact h.frame.writeW hm _ (contains_A fits (by omega))
  · rw [m₄]
    by_cases e : i = n
    · subst e; rw [Nat.zero_add, Mem.readW_writeW_self32]
    · rw [readW_writeW_A _ _ (by omega) (by omega) (by omega)]
      exact h.out i (by omega)

theorem finish_ok {s₄ s : State} (h : FinInv s₀ s₄ s 0) (n : Nat) (hn : n ≤ 256) :
    WP isa (.block ((List.range n).flatMap finishWord)) s (FinInv s₀ s₄ · n) := by
  induction n with
  | zero => exact WP.block_nil h
  | succ n ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    exact WP.block_append ((ih (by omega)).mono fun t ht => finishWord_ok hp (by omega) ht)

end

/-! ## The whole function -/

theorem permR_sub {B : BitVec 32} : Region.Sub (permR B) ⟨State.addr B, 4096⟩ := Offset.sub_base _ (by decide)

section
variable {B : BitVec 32} (hfit : B.toNat + 4096 ≤ 2 ^ 32)
include hfit

/-- A word of `scratch` outside the permuted block is unchanged by its writes. -/
theorem outside_perm {m m' : Mem} (hf : Frame [permR B] m m') {d : Nat} (hd : d + 4 ≤ 4096)
    (ho : d + 4 ≤ 1024 ∨ 2048 ≤ d) : m'.readW (A B d) 32 = m.readW (A B d) 32 := by
  refine hf.readW (r := ⟨A B d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  simp only [List.mem_singleton, forall_eq]
  rw [A_eq (by omega)]
  exact Offset.disjoint _ (by omega) (by omega) (by omega)

theorem low_perm {m m' : Mem} (hf : Frame [permR B] m m') :
    VG.Proof.Argon2.Arm.blk m' B 0 = VG.Proof.Argon2.Arm.blk m B 0 := by
  apply Vector.ext
  intro j hj
  simp only [blk, Vector.getElem_ofFn, rd64]
  rw [outside_perm hfit hf (by omega) (by omega), outside_perm hfit hf (by omega) (by omega)]

end

theorem words_zero {m : Mem} {B : BitVec 32} {f : Nat → BitVec 32} (h : Words m B 0 f 256) :
    blk m B 0 = ofWords f := blk_of_words fun i hi => h i hi

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa Impl.Argon2.Arm.compress s₀ fun t =>
      (∀ r ∈ preserved, t.gpr r = s₀.gpr r) ∧ compressArm.post s₀ t := by
  have fits := hp.scr_fits
  unfold Impl.Argon2.Arm.compress Impl.Argon2.Arm.rounds
  refine WP.seq (prologue_ok hp fun s₁ h₁ => (init_ok hp h₁ 256 (Nat.le_refl _)).mono fun s₂ h₂ => ?_)
  have A₂ : At (scr s₀) s₂ := ⟨by rw [h₂.regs _ (by decide) (by decide)], fun o ho => by
    rw [h₂.wr]; exact ⟨hp.scr_wr rfl (by omega), hp.scr_wr rfl (by omega)⟩⟩
  refine WP.seq (WP.seq ((rounds_ok fits rowIndex Proof.Argon2.rowIndex_injective (List.finRange 8)
    A₂).mono fun s₃ st₃ => (rounds_ok fits colIndex Proof.Argon2.colIndex_injective
      (List.finRange 8) (A₂.of_step st₃)).mono fun s₄ st₄ => ?_))
  have k₄ := st₃.keep.trans st₄.keep
  have pf : Frame [permR (scr s₀)] s₂.mem s₄.mem := st₃.frame.trans st₄.frame
  have r3₄ : s₄.gpr .r3 = scr s₀ := by rw [k₄.r3, h₂.regs _ (by decide) (by decide)]
  have sv₄ : Spill.Saved s₄.mem (State.addr (scr s₀)) s₀.gpr spill :=
    h₂.saved.frame spill_slots pf fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega) (by omega) (by omega)
  unfold Impl.Argon2.Arm.epilogue
  simp only [List.cons_append]
  have i₄ : InRegions (s₄.rd ++ s₄.wr) (A (scr s₀) outOff) 4 := by
    rw [k₄.rd, k₄.wr, h₂.rd, h₂.wr]; exact hp.in_scr rfl (by decide)
  refine wp_ldr (by decide) (by rw [r3₄]) i₄ fun s₅ u₅ => ?_
  have e₅ : s₅.gpr .r2 = op s₀ := by
    rw [u₅.gpr]
    have := sv₄ (.r2, outOff) (by decide)
    rw [A_eq (by simp only [outOff]; omega)]; exact this
  have h₅ : FinInv s₀ s₄ s₅ 0 :=
    ⟨by rw [u₅.other _ (by decide), r3₄], e₅, fun r _ _ h2 => u₅.other r h2,
      by rw [u₅.rd, k₄.rd, h₂.rd], by rw [u₅.wr, k₄.wr, h₂.wr], by rw [u₅.sp, k₄.sp, h₂.sp],
      by rw [u₅.mem]; exact Frame.refl _ _, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  refine WP.block_append ((finish_ok hp h₅ 256 (Nat.le_refl _)).mono fun s₆ h₆ => ?_)
  have sv₆ : Spill.Saved s₆.mem (State.addr (scr s₀)) s₀.gpr saved := fun p hpm =>
    h₆.frame.readW (r := ⟨State.addr (scr s₀) + BitVec.ofNat 64 p.2, 4⟩) (Region.contains_self _ _) (by
      have := saved_slots.bound hpm
      simp only [List.mem_singleton, forall_eq]
      exact (hp.out_scr.sub_right (Offset.sub_base _ (by omega))).symm) (by decide) |>.trans
      (sv₄ p (List.mem_append_left _ hpm))
  rw [← List.append_nil (List.map _ saved)]
  refine Spill.restore_slots_ok saved_slots saved_restorable (g := s₀.gpr) (by rw [h₆.r3]; omega)
    (fun d h₁ h₂ => by rw [h₆.r3, h₆.rd, h₆.wr, ← A_eq (by omega)]; exact hp.in_scr rfl (by omega))
    (by rw [h₆.r3]; exact sv₆) fun t ht ho hm hrd hwr hsp => WP.block_nil ⟨?_, ?_⟩
  · intro r hr
    exact Spill.restored_of ht (by decide) r hr
  · -- The output.
    have R₂ : blk s₂.mem (scr s₀) 0 = ofWords (xy s₀) := words_zero h₂.low
    have W₂ : working s₂.mem (scr s₀) = ofWords (xy s₀) := by
      rw [working_eq]; exact blk_of_words fun i hi => h₂.high i hi
    have X : xorBlock (blockAt s₀.mem (State.addr (xp s₀))) (blockAt s₀.mem (State.addr (yp s₀))) =
        ofWords (xy s₀) := by
      rw [blockAt_eq hp.x_fits, blockAt_eq hp.y_fits,
        blk_of_words (f := fun i => s₀.mem.readW (A (xp s₀) (4 * i)) 32)
          (fun i _ => by rw [Nat.zero_add]),
        blk_of_words (f := fun i => s₀.mem.readW (A (yp s₀) (4 * i)) 32)
          (fun i _ => by rw [Nat.zero_add]), xor_words]
      rfl
    have O : blk t.mem (op s₀) 0 = xorBlock (working s₄.mem (scr s₀)) (blk s₄.mem (scr s₀) 0) := by
      rw [hm, words_zero h₆.out, working_eq,
        blk_of_words (f := fun i => s₄.mem.readW (A (scr s₀) (1024 + 4 * i)) 32) (fun _ _ => rfl),
        blk_of_words (f := fun i => s₄.mem.readW (A (scr s₀) (4 * i)) 32)
          (fun i _ => by rw [Nat.zero_add]), xor_words]
      rfl
    show blockAt t.mem (State.addr (op s₀)) = _
    rw [blockAt_eq hp.out_fits, O, low_perm fits pf, R₂, st₄.working, st₃.working, W₂, ← X]
    simp only [compress]

end VG.Proof.Argon2.Arm
