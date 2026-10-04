import VerifiedGarbage.Proof.Argon2.Arm.HPrime.Body
import VerifiedGarbage.Proof.Argon2.Initial

/-!
# Argon2 H′ on ARMv7: the first digest

`first_ok`: `first` leaves H(min(out_len, 64), LE32(out_len) ‖ input) at the
start of the digest, `scratch[768, 832)`. The input is read before anything
is written to the output, so the two may overlap.
-/

namespace VG.Proof.Argon2.Arm.HPrime

open VG VG.Arm VG.Spec.Blake2
open VG.Impl.Argon2.Arm.HPrime (init update finalize absorbFixed chooseLength absorbInput finishInput first
  cmpLeft)
open VG.Proof.MdStream.Arm (Upd Fupd wp_mov wp_add wp_sub wp_cmp op2_reg op2_imm op2_lsr eval_eq eval_ne
  ofNat_beq_zero)
open VG.Proof.Blake2.Arm.Stream (wp_adds wp_adc)

/-- `(x - 1) >> 6 = 0` exactly when `1 ≤ x ≤ 64`. -/
theorem le64_beq {x : Nat} (h₁ : 1 ≤ x) (h₂ : x < 2 ^ 32) :
    ((BitVec.ofNat 32 x - 1) >>> 6 - 0 == 0) = decide (x ≤ 64) := by
  rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, MdStream.Arm.sub_ofNat h₁, show ∀ y : BitVec 32, y - 0 = y from fun y => BitVec.sub_zero y,
    MdStream.Arm.ofNat_shr (by omega), ofNat_beq_zero (by omega)]
  by_cases h : x ≤ 64
  · simp only [h, decide_true, decide_eq_true_eq]; omega
  · simp only [h, decide_false, decide_eq_false_iff_not]; omega

/-- The comparisons with 64 of the bytes left (in `r8`). -/
theorem cmpLeft_ok {s : State} {x : Nat} (hx : s.gpr .r8 = BitVec.ofNat 32 x) (h₁ : 1 ≤ x) (h₂ : x < 2 ^ 32) :
    WP isa (.block cmpLeft) s fun t => isa.eval .eq t = some (decide (x ≤ 64)) ∧
      (∀ r, r ≠ .r0 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  unfold cmpLeft
  refine wp_sub (op2_imm (by decide)) fun s₁ u₁ => wp_mov (op2_lsr (by decide)) fun s₂ u₂ =>
    wp_cmp (op2_imm (by decide)) fun s₃ f₃ z₃ => WP.block_nil ⟨?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · show VG.Arm.eval .eq s₃ = _
    rw [eval_eq, z₃, u₂.gpr, u₁.gpr, hx]
    exact congrArg some (le64_beq h₁ h₂)
  · rw [f₃.gpr, u₂.other _ hr, u₁.other _ hr]
  · rw [f₃.mem, u₂.mem, u₁.mem]
  · rw [f₃.rd, u₂.rd, u₁.rd]
  · rw [f₃.wr, u₂.wr, u₁.wr]
  · rw [f₃.sp, u₂.sp, u₁.sp]

section
variable {s₀ : State} (hp : Pre s₀)
include hp

/-- `r1 := min(out_len, 64)`. -/
theorem choose_ok {s : State} (_b : Body s₀ s) (o : Out s₀ s []) :
    WP isa chooseLength s fun t => t.gpr .r1 = BitVec.ofNat 32 (min (ol s₀) 64) ∧
      Keeps (scr s₀) (sp₀ s₀) s t := by
  have hol := (s₀.gpr .r3).isLt
  have hpos := hp.ol_pos
  have l₀ : s.gpr .r8 = BitVec.ofNat 32 (ol s₀) := by rw [o.left]; rfl
  unfold chooseLength
  refine WP.seq (wp_sub (op2_imm (by decide)) fun s₁ u₁ => wp_mov (op2_lsr (by decide)) fun s₂ u₂ =>
    wp_cmp (op2_imm (by decide)) fun s₃ f₃ z₃ => WP.block_nil ?_)
  have k₃ : Keeps (scr s₀) (sp₀ s₀) s s₃ := Keeps.same (fun r hr => by
      rw [f₃.gpr, u₂.other _ (kept_ne r hr).2.1, u₁.other _ (kept_ne r hr).2.1])
    (by rw [f₃.sp, u₂.sp, u₁.sp]) (by rw [f₃.mem, u₂.mem, u₁.mem]) (by rw [f₃.rd, u₂.rd, u₁.rd])
    (by rw [f₃.wr, u₂.wr, u₁.wr])
  have r8₃ : s₃.gpr .r8 = BitVec.ofNat 32 (ol s₀) := by rw [k₃.gpr _ (by decide), l₀]
  refine WP.ite (decide (ol s₀ ≤ 64)) (by
      show VG.Arm.eval .eq s₃ = _
      rw [eval_eq, z₃, u₂.gpr, u₁.gpr, l₀]; exact congrArg some (le64_beq hpos hol))
    (fun h => wp_mov (op2_reg _ _) fun s₄ u₄ => WP.block_nil ⟨?_, ?_⟩)
    (fun h => wp_mov (op2_imm (by decide)) fun s₄ u₄ => WP.block_nil ⟨?_, ?_⟩)
  · have : ol s₀ ≤ 64 := by simpa using h
    rw [u₄.gpr, r8₃, Nat.min_eq_left this]
  · exact k₃.trans (Keeps.same (fun r hr => u₄.other r (kept_ne r hr).2.1) u₄.sp u₄.mem u₄.rd u₄.wr)
  · have : 64 ≤ ol s₀ := by simp at h; omega
    rw [u₄.gpr, Nat.min_eq_right this]; rfl
  · exact k₃.trans (Keeps.same (fun r hr => u₄.other r (kept_ne r hr).2.1) u₄.sp u₄.mem u₄.rd u₄.wr)

end

/-! ## The steps of `first` -/

/-- The state before and between the steps of `first`: the body, no output
yet, and the input kept. -/
structure F0 (s₀ s : State) : Prop where
  body : Body s₀ s
  out : Out s₀ s []
  input : bytesAt s.mem (State.addr (inp s₀)) (inl s₀) = bytesAt s₀.mem (State.addr (inp s₀)) (inl s₀)

/-- The length of the first digest. -/
abbrev nF (s₀ : State) : Nat := min (ol s₀) 64

/-- The input, on entry. -/
abbrev inB (s₀ : State) : List Byte := bytesAt s₀.mem (State.addr (inp s₀)) (inl s₀)

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem F0.keeps {s t : State} (h : F0 s₀ s) (k : Keeps (scr s₀) (sp₀ s₀) s t) : F0 s₀ t := by
  refine ⟨h.body.keeps hp k, h.out.keeps hp k, ?_⟩
  have hif := hp.in_fits
  have := k.bytes (R := inR s₀) (by simp; omega)
    (hp.in_scr.sub_right (Region.sub_prefix (by decide))) hp.stk_in.symm
  simp only at this
  rw [this, h.input]

theorem nF_pos : 1 ≤ nF s₀ := by have := hp.ol_pos; simp only [nF]; omega

theorem first_choose {s : State} (h : F0 s₀ s) :
    WP isa chooseLength s fun t => F0 s₀ t ∧ t.gpr .r1 = BitVec.ofNat 32 (nF s₀) :=
  (choose_ok hp h.body h.out).mono fun _ ⟨e, k⟩ => ⟨h.keeps hp k, e⟩

theorem first_init {s : State} (h : F0 s₀ s ∧ s.gpr .r1 = BitVec.ofNat 32 (nF s₀)) :
    WP isa init s fun t => F0 s₀ t ∧ Repr b (Spec.Blake2.init b (nF s₀) 0) t.mem (P s₀) [] := by
  have c := h.1.body.ctx hp
  refine (init_ok c h.2 (nF_pos hp) (Nat.min_le_right _ _)).mono fun t ⟨r, cs, rd, wr, sp, f⟩ => ⟨?_, r⟩
  refine h.1.keeps hp (Keeps.of_call cs sp rd wr f fun r hr => ?_)
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩

theorem pfx_cov {s : State} (b : Body s₀ s) : Covers [⟨P s₀ + BitVec.ofNat 64 832, 4⟩] s.wr := by
  rw [b.wr, hp.wr]
  exact Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨scrR s₀, by simp, 832, rfl, by simp⟩

theorem first_fixed {s : State}
    (h : F0 s₀ s ∧ Repr b (Spec.Blake2.init b (nF s₀) 0) s.mem (P s₀) []) :
    WP isa (absorbFixed 832 4) s fun t => F0 s₀ t ∧
      Repr b (Spec.Blake2.init b (nF s₀) 0) t.mem (P s₀) (Spec.Argon2.le32 (ol s₀)) := by
  have hs := hp.scr_fits
  refine (absorbFixed_ok (h.1.body.ctx hp) (offset := 832) (size := 4) (by decide) (by decide) (by omega)
    (by decide) (by decide) (by decide) (pfx_cov hp h.1.body) (hp.stk_scr.sub_right (Offset.sub_base _ (by decide)))
    h.2).mono fun t ⟨r, k⟩ => ⟨h.1.keeps hp k, ?_⟩
  rw [show BitVec.ofNat 64 832 = (832 : Addr) from rfl, h.1.body.pfx] at r
  exact r

theorem first_input {s : State}
    (h : F0 s₀ s ∧ Repr b (Spec.Blake2.init b (nF s₀) 0) s.mem (P s₀) (Spec.Argon2.le32 (ol s₀))) :
    WP isa absorbInput s fun t => F0 s₀ t ∧
      Repr b (Spec.Blake2.init b (nF s₀) 0) t.mem (P s₀) (Spec.Argon2.le32 (ol s₀) ++ inB s₀) := by
  have hif := hp.in_fits
  have hil := (s₀.gpr .r1).isLt
  unfold absorbInput
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_mov (op2_imm (by decide)) fun s₂ u₂ =>
    wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => WP.block_nil ?_)
  have o₄ : ∀ r, r ≠ .r2 → r ≠ .r3 → r ≠ .r9 → r ≠ .r10 → s₄.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₄.other _ h4, u₃.other _ h3, u₂.other _ h2, u₁.other _ h1]
  have k₄ : Keeps (scr s₀) (sp₀ s₀) s s₄ := Keeps.same (fun r hr => o₄ r (kept_ne r hr).2.2.1
      (kept_ne r hr).2.2.2.1 (kept_ne r hr).2.2.2.2.1 (kept_ne r hr).2.2.2.2.2.1)
    (by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp]) (by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem])
    (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr])
  have F₄ := h.1.keeps hp k₄
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have cnt₄ : s₄.gpr .r3 ++ s₄.gpr .r2 = BitVec.ofNat 64 (Spec.Argon2.le32 (ol s₀)).length := by
    rw [Proof.Argon2.le32_length, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]; rfl
  have r9 : s₄.gpr .r9 = inp s₀ := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.1.body.r5]
  have r10 : (s₄.gpr .r10).toNat = inl s₀ := by
    rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.1.body.r6]
  have hDc : Covers [⟨State.addr (inp s₀), inl s₀⟩] (s₄.rd ++ s₄.wr) := by
    rw [F₄.body.rd, hp.rd]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨inR s₀, by simp, 0, by simp, by simp⟩
  refine (update_ok (F₄.body.ctx hp) (h0 := Spec.Blake2.init Spec.Blake2.b (nF s₀) 0) r9 r10 hif hDc
    (hp.in_scr.sub_right (Region.sub_prefix (by decide))) hp.stk_in (by rw [m₄]; exact h.2) cnt₄
    (by rw [Proof.Argon2.le32_length]; omega)).mono fun s₅ ⟨r₅, cs₅, rd₅, wr₅, sp₅, f₅⟩ => ?_
  rw [F₄.input] at r₅
  refine ⟨F₄.keeps hp (Keeps.of_call cs₅ sp₅ rd₅ wr₅ f₅ fun r hr => ?_), r₅⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩

omit hp in
theorem count4 (x : Nat) (hx : x < 2 ^ 32) :
    ((0 : BitVec 32) + 0 + (if decide (2 ^ 32 ≤ (BitVec.ofNat 32 x).toNat + (4 : BitVec 32).toNat) = true
      then 1 else 0)) ++ (BitVec.ofNat 32 x + 4) = BitVec.ofNat 64 (x + 4) := by
  rw [Proof.Blake2.Arm.Stream.add64]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, Proof.Blake2.Arm.Stream.toNat_append32]
  simp [Nat.mod_eq_of_lt hx] <;> omega

theorem first_finish {s : State}
    (h : F0 s₀ s ∧ Repr b (Spec.Blake2.init b (nF s₀) 0) s.mem (P s₀) (Spec.Argon2.le32 (ol s₀) ++ inB s₀)) :
    WP isa finishInput s fun t => F0 s₀ t ∧
      (digest s₀ t).take (nF s₀) = Spec.Argon2.H (nF s₀) (Spec.Argon2.le32 (ol s₀) ++ inB s₀) := by
  have hif := hp.in_fits
  have hil := (s₀.gpr .r1).isLt
  unfold finishInput
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_adds (op2_imm (by decide)) fun s₂ u₂ c₂ =>
    wp_adc (op2_imm (by decide)) fun s₃ u₃ _ => WP.block_nil ?_)
  have o₃ : ∀ r, r ≠ .r2 → r ≠ .r3 → s₃.gpr r = s.gpr r := fun r h1 h2 => by
    rw [u₃.other _ h2, u₂.other _ h1, u₁.other _ h2]
  have k₃ : Keeps (scr s₀) (sp₀ s₀) s s₃ := Keeps.same (fun r hr => o₃ r (kept_ne r hr).2.2.1
      (kept_ne r hr).2.2.2.1)
    (by rw [u₃.sp, u₂.sp, u₁.sp]) (by rw [u₃.mem, u₂.mem, u₁.mem]) (by rw [u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₃.wr, u₂.wr, u₁.wr])
  have F₃ := h.1.keeps hp k₃
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have r6 : s₁.gpr .r6 = BitVec.ofNat 32 (inl s₀) := by rw [u₁.other _ (by decide), h.1.body.r6]; simp
  have cnt : s₃.gpr .r3 ++ s₃.gpr .r2 = BitVec.ofNat 64 (Spec.Argon2.le32 (ol s₀) ++ inB s₀).length := by
    rw [u₃.gpr, u₃.other _ (by decide), u₂.gpr, u₂.other _ (by decide), u₁.gpr, c₂, r6, List.length_append,
      Proof.Argon2.le32_length]
    simp only [inB, bytesAt, List.length_map, List.length_range]
    rw [show 4 + inl s₀ = inl s₀ + 4 by omega]
    exact count4 _ hil
  refine (finalize_ok (F₃.body.ctx hp) (by rw [m₃]; exact h.2) cnt
    (by simp only [List.length_append, Proof.Argon2.le32_length, inB, bytesAt, List.length_map,
      List.length_range]; omega)).mono ?_
  rintro t ⟨d, cs, rd, wr, sp, f⟩
  refine ⟨F₃.keeps hp (Keeps.of_call cs sp rd wr f fun r hr => ?_), ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
  · show (bytesAt t.mem (P s₀ + 768) 64).take _ = _
    rw [d, Proof.Argon2.H_stream]

/-- `first` hashes the length prefix and the input. -/
theorem first_ok {s : State} (h : F0 s₀ s) :
    WP isa first s fun t => F0 s₀ t ∧
      (digest s₀ t).take (nF s₀) = Spec.Argon2.H (nF s₀) (Spec.Argon2.le32 (ol s₀) ++ inB s₀) := by
  unfold first
  exact WP.seq ((first_choose hp h).mono fun _ h₁ => WP.seq ((first_init hp h₁).mono fun _ h₂ =>
    WP.seq ((first_fixed hp h₂).mono fun _ h₃ => WP.seq ((first_input hp h₃).mono fun _ h₄ =>
      first_finish hp h₄))))

end

end VG.Proof.Argon2.Arm.HPrime
