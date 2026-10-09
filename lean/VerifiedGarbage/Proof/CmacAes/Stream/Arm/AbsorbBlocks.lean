import VerifiedGarbage.Proof.CmacAes.Stream.Arm.Common

section

/-!
# Streaming AES-CMAC on ARMv7: copying bytes

`copy` copies the `r1` bytes at `r6` to `r2`, a byte at a time (none if `r1`
is 0), advancing `r6` past them and taking them off `r7`, and changing only
`r1`, `r2`, `r6`, `r7`, `r12` and the flags.
-/

namespace VG.Proof.CmacAes.Stream.Arm

open VG VG.Arm VG.Impl.CmacAes.Stream.Arm VG.WriteBytes
open VG.Proof.MdStream.Arm (Upd op2_imm op2_reg wp_add wp_sub wp_subs wp_cmp wp_ldrb wp_strb eval_ne
  ofNat_beq_zero sub_ofNat)
open VG.Proof.CmacAes.Arm (byte_rt32)

/-- What `copy` leaves. -/
structure Copied (s : State) (p c : BitVec 32) (L x : Nat) (s' : State) : Prop where
  mem : s'.mem = writeBytes s.mem (State.addr c) (Spec.Aes.bytesAt s.mem (State.addr p) L)
  r6 : s'.gpr .r6 = p + BitVec.ofNat 32 L
  r7 : s'.gpr .r7 = BitVec.ofNat 32 (x - L)
  other : ∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r6 → r ≠ .r7 → r ≠ .r12 → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- The loop, for `L > 0` bytes. -/
theorem copyLoop_wp {s : State} {p c : BitVec 32} {L : Nat} (hL₀ : 0 < L)
    (h6 : s.gpr .r6 = p) (h2 : s.gpr .r2 = c) (h1 : s.gpr .r1 = BitVec.ofNat 32 L)
    (fp : p.toNat + L ≤ 2 ^ 32) (fc : c.toNat + L ≤ 2 ^ 32)
    (hr : Covers [⟨State.addr p, L⟩] (s.rd ++ s.wr)) (hw : Covers [⟨State.addr c, L⟩] s.wr)
    (hd : (⟨State.addr p, L⟩ : Region).Disjoint ⟨State.addr c, L⟩) :
    WP isa (.loop (.block copyBody) .ne) s fun s' =>
      s'.mem = writeBytes s.mem (State.addr c) (Spec.Aes.bytesAt s.mem (State.addr p) L) ∧
      s'.gpr .r6 = p + BitVec.ofNat 32 L ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r6 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.loop (M := isa) (body := .block copyBody) (c := .ne)
    (fun (n : Nat) (t : State) => ∃ i, n = L - i ∧ i < L ∧ t.gpr .r6 = p + BitVec.ofNat 32 i ∧
      t.gpr .r2 = c + BitVec.ofNat 32 i ∧ t.gpr .r1 = BitVec.ofNat 32 (L - i) ∧
      t.mem = writeBytes s.mem (State.addr c) (Spec.Aes.bytesAt s.mem (State.addr p) i) ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r6 → r ≠ .r12 → t.gpr r = s.gpr r) ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (L - 0) _
    ⟨0, rfl, hL₀, by rw [h6]; exact (BitVec.add_zero p).symm, by rw [h2]; exact (BitVec.add_zero c).symm,
      by rw [h1, Nat.sub_zero], by simp [Spec.Aes.bytesAt, writeBytes_nil], fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
  rintro n t ⟨i, rfl, hi, x6, x2, x1, mem, g, sp, rd, wr⟩
  have aP : State.addr (p + BitVec.ofNat 32 i) = State.addr p + BitVec.ofNat 64 i := addr_add (by omega_arith)
  have aC : State.addr (c + BitVec.ofNat 32 i) = State.addr c + BitVec.ofNat 64 i := addr_add (by omega_arith)
  refine wp_ldrb (a := State.addr p + BitVec.ofNat 64 i) (by decide) (by rw [x6, BitVec.add_zero, aP])
    (by rw [rd, wr]; exact hr _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    fun t₁ u₁ => ?_
  refine wp_strb (a := State.addr c + BitVec.ofNat 64 i) (by decide)
    (by rw [u₁.other _ (by decide), x2, BitVec.add_zero, aC])
    (by rw [u₁.wr, wr]; exact hw _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    fun t₂ v₂ => ?_
  refine wp_add (op2_imm (by decide)) fun t₃ u₃ => wp_add (op2_imm (by decide)) fun t₄ u₄ =>
    wp_subs (op2_imm (by decide)) fun t₅ u₅ z₅ => WP.block_nil ?_
  have hlen : (Spec.Aes.bytesAt s.mem (State.addr p) i).length = i := Proof.Cmac.bytesAt_length _ _ _
  have hx : writeBytes s.mem (State.addr c) (Spec.Aes.bytesAt s.mem (State.addr p) i) (State.addr p + BitVec.ofNat 64 i) =
      s.mem (State.addr p + BitVec.ofNat 64 i) :=
    (writeBytes_frame s.mem (State.addr c) _ (R := ⟨State.addr c, i⟩) (by rw [hlen]; exact Region.contains_self _ _)) _
      fun r hr hcon => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hd _ (Offset.contains_base _ (by omega_arith) (by omega_arith)) (Region.sub_prefix (by omega_arith) _ hcon)
  have hmem : t₅.mem = writeBytes s.mem (State.addr c) (Spec.Aes.bytesAt s.mem (State.addr p) (i + 1)) := by
    rw [u₅.mem, u₄.mem, u₃.mem, v₂.mem, u₁.gpr, u₁.mem, mem, byte_rt32, hx, Proof.Cmac.bytesAt_succ,
      writeBytes_snoc s.mem _ _ _ (by rw [hlen]; omega_arith), hlen]
  have x1' : t₅.gpr .r1 = BitVec.ofNat 32 (L - (i + 1)) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), x1,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega_arith)]; rfl
  have ev : isa.eval .ne t₅ = some !decide (L - (i + 1) = 0) := by
    show VG.Arm.eval .ne t₅ = _
    rw [eval_ne, z₅, u₄.other _ (by decide), u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), x1,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega_arith), Nat.sub_sub,
      ofNat_beq_zero (by omega_arith)]
  have gg : ∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r6 → r ≠ .r12 → t₅.gpr r = s.gpr r := fun r h₁ h₂ h₆ h₁₂ => by
    rw [u₅.other _ h₁, u₄.other _ h₂, u₃.other _ h₆, v₂.gpr, u₁.other _ h₁₂, g r h₁ h₂ h₆ h₁₂]
  have x2' : t₅.gpr .r2 = c + BitVec.ofNat 32 (i + 1) := by
    rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), x2,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.add_add]
  have x6' : t₅.gpr .r6 = p + BitVec.ofNat 32 (i + 1) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, v₂.gpr, u₁.other _ (by decide), x6,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.add_add]
  have sp' : t₅.sp = s.sp := by rw [u₅.sp, u₄.sp, u₃.sp, v₂.sp, u₁.sp, sp]
  have rd' : t₅.rd = s.rd := by rw [u₅.rd, u₄.rd, u₃.rd, v₂.rd, u₁.rd, rd]
  have wr' : t₅.wr = s.wr := by rw [u₅.wr, u₄.wr, u₃.wr, v₂.wr, u₁.wr, wr]
  by_cases he : i + 1 = L
  · left
    exact ⟨by rw [ev]; simp [he], by rw [hmem, he], by rw [x6', he], gg, sp', rd', wr'⟩
  · right
    exact ⟨by rw [ev]; simp; omega_arith, L - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, x6', x2', x1', hmem, gg,
      sp', rd', wr'⟩

/-- What copying `L > 0` bytes from `p` to `c` needs. -/
structure CopyOk (s : State) (p c : BitVec 32) (L : Nat) : Prop where
  fp : p.toNat + L ≤ 2 ^ 32
  fc : c.toNat + L ≤ 2 ^ 32
  hr : Covers [⟨State.addr p, L⟩] (s.rd ++ s.wr)
  hw : Covers [⟨State.addr c, L⟩] s.wr
  hd : (⟨State.addr p, L⟩ : Region).Disjoint ⟨State.addr c, L⟩

theorem copy_wp {s : State} {p c : BitVec 32} {L x : Nat} (hLx : L ≤ x) (hx : x < 2 ^ 32)
    (h6 : s.gpr .r6 = p) (h2 : s.gpr .r2 = c) (h1 : s.gpr .r1 = BitVec.ofNat 32 L)
    (h7 : s.gpr .r7 = BitVec.ofNat 32 x) (ok : 0 < L → CopyOk s p c L) :
    WP isa copy s (Copied s p c L x) := by
  refine WP.seq (wp_sub (op2_reg _ _) fun s₁ u₁ => wp_cmp (op2_imm (by decide)) fun s₂ f₂ z₂ => WP.block_nil ?_)
  have g₂ : ∀ r, r ≠ .r7 → s₂.gpr r = s.gpr r := fun r hr => by rw [f₂.gpr, u₁.other _ hr]
  have r7₂ : s₂.gpr .r7 = BitVec.ofNat 32 (x - L) := by rw [f₂.gpr, u₁.gpr, h7, h1, sub_ofNat hLx]
  rw [show s₁.gpr .r1 = BitVec.ofNat 32 L by rw [u₁.other _ (by decide), h1]] at z₂
  have ev := eq_iff s₂ z₂ (by omega_arith)
  have sp₂ : s₂.sp = s.sp := by rw [f₂.sp, u₁.sp]
  have rd₂ : s₂.rd = s.rd := by rw [f₂.rd, u₁.rd]
  have wr₂ : s₂.wr = s.wr := by rw [f₂.wr, u₁.wr]
  have m₂ : s₂.mem = s.mem := by rw [f₂.mem, u₁.mem]
  by_cases hL : L = 0
  · subst hL
    refine WP.ite true (by rw [ev]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    exact ⟨by rw [m₂]; simp [Spec.Aes.bytesAt, writeBytes_nil],
      (by rw [g₂ _ (by decide), h6]; exact (BitVec.add_zero p).symm), r7₂, fun r _ _ _ h₇ _ => g₂ r h₇, sp₂, rd₂,
      wr₂⟩
  · obtain ⟨fp, fc, hr, hw, hd⟩ := ok (by omega_arith)
    refine WP.ite false (by rw [ev]; simp [hL]) (fun h => by cases h) fun _ => ?_
    refine WP.mono (copyLoop_wp (by omega_arith) (by rw [g₂ _ (by decide), h6]) (by rw [g₂ _ (by decide), h2])
      (by rw [g₂ _ (by decide), h1]) fp fc (by rw [rd₂, wr₂]; exact hr) (by rw [wr₂]; exact hw) hd)
      fun s' ⟨mm, r6, g, sp, rd, wr⟩ => ⟨by rw [mm, m₂], r6, by rw [g _ (by decide) (by decide) (by decide)
        (by decide), r7₂], fun r h₁ h₂ h₆ h₇ h₁₂ => by rw [g r h₁ h₂ h₆ h₁₂, g₂ r h₇], by rw [sp, sp₂],
        by rw [rd, rd₂], by rw [wr, wr₂]⟩

end VG.Proof.CmacAes.Stream.Arm

end

/-!
# Streaming AES-CMAC on ARMv7: `vg_cmac_aes_absorb`'s straight-line code

What each piece of code between the copies and calls computes, in terms of
`count` (`c`) and `len` (`L`): the bytes held back `h = held c`, the bytes
copied after them `f = min L (16 - h)`, the data left `L - f`, whether to
chain the block held back (`b1`), the blocks chained after it (`nb`), and the
rest (`rest`).
-/

namespace VG.Proof.CmacAes.Stream.Arm

open VG VG.Arm VG.Impl.CmacAes.Stream.Arm
open VG.Impl.CmacAes.Arm (mov)
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg op2_lsr op2_lsl wp_mov wp_add wp_sub wp_and wp_orr
  wp_cmp cmp0 sub_ofNat ofNat_shr)
open VG.Proof.Cmac.Stream (held held_le held_zero)

/-! ## The numbers -/

/-- The bytes copied after the `held c` held back. -/
def fOf (c L : Nat) : Nat := min L (16 - held c)

/-- The data left after them. -/
def leftOf (c L : Nat) : Nat := L - fOf c L

/-- The number of blocks the first call chains: the block held back, if data is left. -/
def b1Of (c L : Nat) : Nat := if leftOf c L = 0 then 0 else 1

/-- The number of whole blocks of `x` bytes but its last 1 to 16 (none for none). -/
def nbx (x : Nat) : Nat := if x = 0 then 0 else (x - 1) / 16

/-- The number of blocks the second call chains: those of the data left but its
last 1 to 16 bytes. -/
def nbOf (c L : Nat) : Nat := nbx (leftOf c L)

/-- The bytes copied to the start of the bytes held back at the end. -/
def restOf (c L : Nat) : Nat := leftOf c L - 16 * nbOf c L

theorem f_le (c L : Nat) : fOf c L ≤ L ∧ fOf c L + held c ≤ 16 := by
  have := held_le c; unfold fOf; omega_arith

theorem nb_le (c L : Nat) : fOf c L + 16 * nbOf c L + restOf c L = L := by
  have := f_le c L; unfold restOf nbOf nbx leftOf; split <;> omega_arith

theorem rest_le (c L : Nat) : restOf c L ≤ 16 := by
  unfold restOf nbOf nbx leftOf; split <;> omega_arith

/-! ## Arithmetic on registers -/

theorem ite_neg' {α : Type} {p : Prop} [Decidable p] {a b : α} (h : ¬p) : (if p then a else b) = b := by
  simp [h]

theorem ite_pos' {α : Type} {p : Prop} [Decidable p] {a b : α} (h : p) : (if p then a else b) = a := by
  simp [h]

theorem shl4 (n : Nat) : BitVec.ofNat 32 n <<< 4 = BitVec.ofNat 32 (16 * n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_arith

theorem shr4 {a : Nat} (h : a < 2 ^ 32) : BitVec.ofNat 32 a >>> 4 = BitVec.ofNat 32 (a / 16) := ofNat_shr h

/-! ## `held`: the bytes held back -/

theorem held_wp {s : State} {c : Nat} (hc : c < 2 ^ 64)
    (hcnt : (s.gpr .r3 ++ s.gpr .r2 : BitVec 64) = BitVec.ofNat 64 c) :
    WP isa held s fun s' => s'.gpr .r0 = BitVec.ofNat 32 (held c) ∧
      (∀ r, r ≠ .r0 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  refine WP.seq (wp_sub (op2_imm (by decide)) fun s₁ u₁ => wp_and (op2_imm (by decide)) fun s₂ u₂ =>
    wp_add (op2_imm (by decide)) fun s₃ u₃ => wp_orr (op2_reg _ _) fun s₄ u₄ =>
    wp_cmp (op2_imm (by decide)) fun s₅ f₅ z₅ => WP.block_nil ?_)
  have g : ∀ r, r ≠ .r0 → r ≠ .r12 → s₅.gpr r = s.gpr r := fun r a b => by
    rw [f₅.gpr, u₄.other _ b, u₃.other _ a, u₂.other _ a, u₁.other _ a]
  have ev : isa.eval .eq s₅ = some (decide (c = 0)) := by
    show VG.Arm.eval .eq s₅ = _
    rw [VG.Proof.MdStream.Arm.eval_eq, z₅, u₄.gpr]
    simp (disch := decide) only [u₃.other, u₂.other, u₁.other]
    exact congrArg some (or_beq_zero hcnt hc)
  have r0 : s₅.gpr .r0 = ((s.gpr .r2 - 1) &&& 15) + 1 := by
    rw [f₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.gpr]
  have m : s₅.mem = s.mem := by rw [f₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have sp : s₅.sp = s.sp := by rw [f₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  have rd : s₅.rd = s.rd := by rw [f₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr : s₅.wr = s.wr := by rw [f₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  by_cases h0 : c = 0
  · subst h0
    refine WP.ite true (by rw [ev]; rfl) (fun _ => wp_mov (op2_imm (by decide)) fun t u => WP.block_nil ?_)
      (fun h => by cases h)
    exact ⟨by rw [u.gpr, held_zero]; rfl, fun r a b => by rw [u.other _ a, g r a b], by rw [u.mem, m],
      by rw [u.sp, sp], by rw [u.rd, rd], by rw [u.wr, wr]⟩
  · refine WP.ite false (by rw [ev]; simp [h0]) (fun h => by cases h) fun _ => WP.block_nil ?_
    exact ⟨by rw [r0]; exact held_lo hcnt hc h0, g, m, sp, rd, wr⟩

/-! ## `fill`: how many bytes to copy, and where -/

theorem fill_wp {s : State} {St : BitVec 32} {h L : Nat} (hh : h ≤ 16) (hL : L < 2 ^ 32)
    (h0 : s.gpr .r0 = BitVec.ofNat 32 h) (h7 : s.gpr .r7 = BitVec.ofNat 32 L) (h4 : s.gpr .r4 = St) :
    WP isa fill s fun s' => s'.gpr .r1 = BitVec.ofNat 32 (min L (16 - h)) ∧
      s'.gpr .r2 = St + BitVec.ofNat 32 (288 + h) ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.sp = s.sp ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_sub (op2_reg _ _) fun s₂ u₂ =>
    wp_mov (op2_lsr (by decide)) fun s₃ u₃ => wp_cmp (op2_imm (by decide)) fun s₄ f₄ z₄ => WP.block_nil ?_)
  have g₄ : ∀ r, r ≠ .r1 → r ≠ .r12 → s₄.gpr r = s.gpr r := fun r a b => by
    rw [f₄.gpr, u₃.other _ b, u₂.other _ a, u₁.other _ a]
  have r1₄ : s₄.gpr .r1 = BitVec.ofNat 32 (16 - h) := by
    rw [f₄.gpr, u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), h0]; exact sub_ofNat hh
  have z : s₄.z = (BitVec.ofNat 32 (L / 16) - 0 == 0) := by
    rw [z₄, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h7, shr4 hL]
  have ev := eq_iff s₄ z (by omega_arith)
  refine WP.seq (WP.mono (Q := fun (s₅ : State) => s₅.gpr .r1 = BitVec.ofNat 32 (min L (16 - h)) ∧
    (∀ r, r ≠ .r1 → r ≠ .r12 → s₅.gpr r = s.gpr r) ∧ s₅.mem = s.mem ∧ s₅.sp = s.sp ∧ s₅.rd = s.rd ∧
      s₅.wr = s.wr) ?_ ?_)
  · refine WP.mono (Q := fun (s₅ : State) => s₅.gpr .r1 = BitVec.ofNat 32 (min L (16 - h)) ∧
      (∀ r, r ≠ .r1 → r ≠ .r12 → s₅.gpr r = s₄.gpr r) ∧ s₅.mem = s₄.mem ∧ s₅.sp = s₄.sp ∧ s₅.rd = s₄.rd ∧
        s₅.wr = s₄.wr) ?_ fun s₅ ⟨r1, g, m, sp, rd, wr⟩ => ⟨r1, fun r a b => by rw [g r a b, g₄ r a b],
          by rw [m, f₄.mem, u₃.mem, u₂.mem, u₁.mem], by rw [sp, f₄.sp, u₃.sp, u₂.sp, u₁.sp],
          by rw [rd, f₄.rd, u₃.rd, u₂.rd, u₁.rd], by rw [wr, f₄.wr, u₃.wr, u₂.wr, u₁.wr]⟩
    by_cases hl : L / 16 = 0
    · refine WP.ite true (by rw [ev]; simp [hl]) (fun _ => ?_) (fun h => by cases h)
      refine WP.seq (wp_add (op2_reg _ _) fun t₁ v₁ => wp_mov (op2_lsr (by decide)) fun t₂ v₂ =>
        wp_cmp (op2_imm (by decide)) fun t₃ e₃ y₃ => WP.block_nil ?_)
      have zz : t₃.z = (BitVec.ofNat 32 ((L + h) / 16) - 0 == 0) := by
        rw [y₃, v₂.gpr, v₁.gpr, g₄ .r7 (by decide) (by decide), g₄ .r0 (by decide) (by decide), h7, h0,
          ← BitVec.ofNat_add, shr4 (by omega_arith)]
      have ev' := eq_iff t₃ zz (by omega_arith)
      have gt : ∀ r, r ≠ .r12 → t₃.gpr r = s₄.gpr r := fun r a => by rw [e₃.gpr, v₂.other _ a, v₁.other _ a]
      have mt : t₃.mem = s₄.mem := by rw [e₃.mem, v₂.mem, v₁.mem]
      have spt : t₃.sp = s₄.sp := by rw [e₃.sp, v₂.sp, v₁.sp]
      have rdt : t₃.rd = s₄.rd := by rw [e₃.rd, v₂.rd, v₁.rd]
      have wrt : t₃.wr = s₄.wr := by rw [e₃.wr, v₂.wr, v₁.wr]
      by_cases hl' : (L + h) / 16 = 0
      · refine WP.ite true (by rw [ev']; simp [hl']) (fun _ => wp_mov (op2_reg _ _) fun t₄ v₄ =>
          WP.block_nil ?_) (fun h => by cases h)
        refine ⟨by rw [v₄.gpr, gt _ (by decide), g₄ _ (by decide) (by decide), h7, Nat.min_eq_left (by omega_arith)],
          fun r a b => by rw [v₄.other _ a, gt _ b], by rw [v₄.mem, mt], by rw [v₄.sp, spt], by rw [v₄.rd, rdt],
          by rw [v₄.wr, wrt]⟩
      · refine WP.ite false (by rw [ev']; simp [hl']) (fun h => by cases h) fun _ => WP.block_nil ?_
        exact ⟨by rw [gt _ (by decide), r1₄, Nat.min_eq_right (by omega_arith)], fun r _ b => gt r b, mt, spt, rdt,
          wrt⟩
    · refine WP.ite false (by rw [ev]; simp [hl]) (fun h => by cases h) fun _ => WP.block_nil ?_
      exact ⟨by rw [r1₄, Nat.min_eq_right (by omega_arith)], fun _ _ _ => rfl, rfl, rfl, rfl, rfl⟩
  · intro s₅ ⟨r1, g, m, sp, rd, wr⟩
    refine wp_add (op2_reg _ _) fun t₁ v₁ => wp_add (op2_imm (by decide)) fun t₂ v₂ => WP.block_nil ?_
    refine ⟨by rw [v₂.other _ (by decide), v₁.other _ (by decide), r1], ?_,
      fun r a b c => by rw [v₂.other _ b, v₁.other _ b, g r a c], by rw [v₂.mem, v₁.mem, m],
      by rw [v₂.sp, v₁.sp, sp], by rw [v₂.rd, v₁.rd, rd], by rw [v₂.wr, v₁.wr, wr]⟩
    rw [v₂.gpr, v₁.gpr, g _ (by decide) (by decide), g _ (by decide) (by decide), h4, h0, BitVec.add_assoc,
      show (288 : BitVec 32) = BitVec.ofNat 32 288 from rfl, ← BitVec.ofNat_add, Nat.add_comm]

/-! ## `chain1`: the arguments of the first call -/

theorem chain1_wp {s : State} {St : BitVec 32} {x : Nat} (hx : x < 2 ^ 32) (h7 : s.gpr .r7 = BitVec.ofNat 32 x)
    (h4 : s.gpr .r4 = St) :
    WP isa chain1 s fun s' => s'.gpr .r9 = BitVec.ofNat 32 (if x = 0 then 0 else 1) ∧ s'.gpr .r0 = St ∧
      s'.gpr .r1 = s.gpr .r5 ∧ s'.gpr .r2 = St + BitVec.ofNat 32 272 ∧ s'.gpr .r3 = St + BitVec.ofNat 32 288 ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r9 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_cmp (op2_imm (by decide)) fun s₂ f₂ z₂ =>
    WP.block_nil ?_)
  have ev := eq_iff s₂ (k := x) (by rw [z₂, u₁.other _ (by decide), h7]) hx
  refine WP.seq (WP.mono (Q := fun (s₃ : State) => s₃.gpr .r9 = BitVec.ofNat 32 (if x = 0 then 0 else 1) ∧
    (∀ r, r ≠ .r9 → s₃.gpr r = s.gpr r) ∧ s₃.mem = s.mem ∧ s₃.sp = s.sp ∧ s₃.rd = s.rd ∧ s₃.wr = s.wr) ?_ ?_)
  · have g₂ : ∀ r, r ≠ .r9 → s₂.gpr r = s.gpr r := fun r a => by rw [f₂.gpr, u₁.other _ a]
    by_cases h0 : x = 0
    · refine WP.ite true (by rw [ev]; simp [h0]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      exact ⟨by rw [f₂.gpr, u₁.gpr, h0]; rfl, g₂, by rw [f₂.mem, u₁.mem], by rw [f₂.sp, u₁.sp],
        by rw [f₂.rd, u₁.rd], by rw [f₂.wr, u₁.wr]⟩
    · refine WP.ite false (by rw [ev]; simp [h0]) (fun h => by cases h) fun _ =>
        wp_mov (op2_imm (by decide)) fun t u => WP.block_nil ?_
      exact ⟨by rw [u.gpr, ite_neg' h0]; rfl, fun r a => by rw [u.other _ a, g₂ r a],
        by rw [u.mem, f₂.mem, u₁.mem], by rw [u.sp, f₂.sp, u₁.sp], by rw [u.rd, f₂.rd, u₁.rd],
        by rw [u.wr, f₂.wr, u₁.wr]⟩
  · intro s₃ ⟨r9, g, m, sp, rd, wr⟩
    refine wp_mov (op2_reg _ _) fun t₁ v₁ => wp_mov (op2_reg _ _) fun t₂ v₂ => wp_add (op2_imm (by decide))
      fun t₃ v₃ => wp_add (op2_imm (by decide)) fun t₄ v₄ => WP.block_nil ?_
    refine ⟨by simp (disch := decide) only [v₄.other, v₃.other, v₂.other, v₁.other, r9],
      by simp (disch := decide) only [v₄.other, v₃.other, v₂.other, v₁.gpr, g, h4],
      by simp (disch := decide) only [v₄.other, v₃.other, v₂.gpr, v₁.other, g],
      by simp (disch := decide) only [v₄.other, v₃.gpr, v₂.other, v₁.other, g, h4]; rfl,
      by simp (disch := decide) only [v₄.gpr, v₃.other, v₂.other, v₁.other, g, h4]; rfl,
      fun r a b c d e => by rw [v₄.other _ d, v₃.other _ c, v₂.other _ b, v₁.other _ a, g r e],
      by rw [v₄.mem, v₃.mem, v₂.mem, v₁.mem, m], by rw [v₄.sp, v₃.sp, v₂.sp, v₁.sp, sp],
      by rw [v₄.rd, v₃.rd, v₂.rd, v₁.rd, rd], by rw [v₄.wr, v₃.wr, v₂.wr, v₁.wr, wr]⟩

/-! ## `chain2`: the arguments of the second call -/

theorem chain2_wp {s : State} {St Dd : BitVec 32} {x : Nat} (hx : x < 2 ^ 32) (h7 : s.gpr .r7 = BitVec.ofNat 32 x)
    (h4 : s.gpr .r4 = St) (h6 : s.gpr .r6 = Dd) :
    WP isa chain2 s fun s' => s'.gpr .r9 = BitVec.ofNat 32 (nbx x) ∧
      s'.gpr .r8 = BitVec.ofNat 32 (16 * nbx x) ∧ s'.gpr .r3 = (if x = 0 then St else Dd) ∧
      s'.gpr .r0 = St ∧ s'.gpr .r1 = s.gpr .r5 ∧ s'.gpr .r2 = St + BitVec.ofNat 32 272 ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r8 → r ≠ .r9 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.seq (wp_cmp (op2_imm (by decide)) fun s₁ f₁ z₁ => WP.block_nil ?_)
  have ev := eq_iff s₁ (k := x) (by rw [z₁, h7]) hx
  refine WP.seq (WP.mono (Q := fun (s₂ : State) => s₂.gpr .r9 = BitVec.ofNat 32 (nbx x) ∧
    s₂.gpr .r8 = BitVec.ofNat 32 (16 * nbx x) ∧ s₂.gpr .r3 = (if x = 0 then St else Dd) ∧
    (∀ r, r ≠ .r3 → r ≠ .r8 → r ≠ .r9 → s₂.gpr r = s.gpr r) ∧ s₂.mem = s.mem ∧ s₂.sp = s.sp ∧ s₂.rd = s.rd ∧
      s₂.wr = s.wr) ?_ ?_)
  · by_cases h0 : x = 0
    · refine WP.ite true (by rw [ev]; simp [h0]) (fun _ => wp_mov (op2_imm (by decide)) fun t₁ v₁ =>
        wp_mov (op2_imm (by decide)) fun t₂ v₂ => wp_mov (op2_reg _ _) fun t₃ v₃ => WP.block_nil ?_)
        (fun h => by cases h)
      refine ⟨by rw [v₃.other _ (by decide), v₂.other _ (by decide), v₁.gpr, nbx, ite_pos' h0]; rfl,
        by rw [v₃.other _ (by decide), v₂.gpr, nbx, ite_pos' h0]; rfl,
        by rw [v₃.gpr, v₂.other _ (by decide), v₁.other _ (by decide), f₁.gpr, h4, ite_pos' h0],
        fun r a b c => by rw [v₃.other _ a, v₂.other _ b, v₁.other _ c, f₁.gpr],
        by rw [v₃.mem, v₂.mem, v₁.mem, f₁.mem], by rw [v₃.sp, v₂.sp, v₁.sp, f₁.sp],
        by rw [v₃.rd, v₂.rd, v₁.rd, f₁.rd], by rw [v₃.wr, v₂.wr, v₁.wr, f₁.wr]⟩
    · refine WP.ite false (by rw [ev]; simp [h0]) (fun h => by cases h) fun _ =>
        wp_sub (op2_imm (by decide)) fun t₁ v₁ => wp_mov (op2_lsr (by decide)) fun t₂ v₂ =>
        wp_mov (op2_lsl (by decide)) fun t₃ v₃ => wp_mov (op2_reg _ _) fun t₄ v₄ => WP.block_nil ?_
      have e9 : t₂.gpr .r9 = BitVec.ofNat 32 ((x - 1) / 16) := by
        rw [v₂.gpr, v₁.gpr, f₁.gpr, h7, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega_arith),
          shr4 (by omega_arith)]
      refine ⟨by rw [v₄.other _ (by decide), v₃.other _ (by decide), e9, nbx, ite_neg' h0],
        by rw [v₄.other _ (by decide), v₃.gpr, e9, shl4, nbx, ite_neg' h0],
        by rw [v₄.gpr, v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide), f₁.gpr, h6,
          ite_neg' h0],
        fun r a b c => by rw [v₄.other _ a, v₃.other _ b, v₂.other _ c, v₁.other _ c, f₁.gpr],
        by rw [v₄.mem, v₃.mem, v₂.mem, v₁.mem, f₁.mem], by rw [v₄.sp, v₃.sp, v₂.sp, v₁.sp, f₁.sp],
        by rw [v₄.rd, v₃.rd, v₂.rd, v₁.rd, f₁.rd], by rw [v₄.wr, v₃.wr, v₂.wr, v₁.wr, f₁.wr]⟩
  · intro s₂ ⟨r9, r8, r3, g, m, sp, rd, wr⟩
    refine wp_mov (op2_reg _ _) fun t₁ v₁ => wp_mov (op2_reg _ _) fun t₂ v₂ => wp_add (op2_imm (by decide))
      fun t₃ v₃ => WP.block_nil ?_
    refine ⟨by simp (disch := decide) only [v₃.other, v₂.other, v₁.other, r9],
      by simp (disch := decide) only [v₃.other, v₂.other, v₁.other, r8],
      by simp (disch := decide) only [v₃.other, v₂.other, v₁.other, r3],
      by simp (disch := decide) only [v₃.other, v₂.other, v₁.gpr, g, h4],
      by simp (disch := decide) only [v₃.other, v₂.gpr, v₁.other, g],
      by simp (disch := decide) only [v₃.gpr, v₂.other, v₁.other, g, h4]; rfl,
      fun r a b c d e f => by rw [v₃.other _ c, v₂.other _ b, v₁.other _ a, g r d e f],
      by rw [v₃.mem, v₂.mem, v₁.mem, m], by rw [v₃.sp, v₂.sp, v₁.sp, sp],
      by rw [v₃.rd, v₂.rd, v₁.rd, rd], by rw [v₃.wr, v₂.wr, v₁.wr, wr]⟩

/-! ## `rest`: the arguments of the last copy -/

theorem rest_wp {s : State} {St P : BitVec 32} {x n : Nat} (hn : 16 * n ≤ x)
    (h6 : s.gpr .r6 = P) (h7 : s.gpr .r7 = BitVec.ofNat 32 x) (h8 : s.gpr .r8 = BitVec.ofNat 32 (16 * n))
    (h4 : s.gpr .r4 = St) :
    WP isa (.block rest) s fun s' => s'.gpr .r6 = P + BitVec.ofNat 32 (16 * n) ∧
      s'.gpr .r7 = BitVec.ofNat 32 (x - 16 * n) ∧ s'.gpr .r1 = BitVec.ofNat 32 (x - 16 * n) ∧
      s'.gpr .r2 = St + BitVec.ofNat 32 288 ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r6 → r ≠ .r7 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine wp_add (op2_reg _ _) fun t₁ v₁ => wp_sub (op2_reg _ _) fun t₂ v₂ => wp_mov (op2_reg _ _) fun t₃ v₃ =>
    wp_add (op2_imm (by decide)) fun t₄ v₄ => WP.block_nil ?_
  have r7 : t₂.gpr .r7 = BitVec.ofNat 32 (x - 16 * n) := by
    rw [v₂.gpr, v₁.other _ (by decide), v₁.other _ (by decide), h7, h8, sub_ofNat hn]
  refine ⟨by rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide), v₁.gpr, h6, h8],
    by rw [v₄.other _ (by decide), v₃.other _ (by decide), r7], by rw [v₄.other _ (by decide), v₃.gpr, r7],
    by rw [v₄.gpr, v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide), h4]; rfl,
    fun r a b c d => by rw [v₄.other _ b, v₃.other _ a, v₂.other _ d, v₁.other _ c],
    by rw [v₄.mem, v₃.mem, v₂.mem, v₁.mem], by rw [v₄.sp, v₃.sp, v₂.sp, v₁.sp],
    by rw [v₄.rd, v₃.rd, v₂.rd, v₁.rd], by rw [v₄.wr, v₃.wr, v₂.wr, v₁.wr]⟩

end VG.Proof.CmacAes.Stream.Arm
