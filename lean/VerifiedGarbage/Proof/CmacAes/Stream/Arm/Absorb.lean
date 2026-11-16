module

public import VerifiedGarbage.Impl.CmacAes.Stream.Arm
public import VerifiedGarbage.Proof.Cmac.Stream
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.CmacAes.Stream.Arm.Common
import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.CmacAes.Arm.Finalize
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.CmacAes.Stream.Arm.Call

/-! ### `CmacAes.Stream.Arm.AbsorbBlocks`, which only this module used -/

section

@[expose] public section

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
  obtain aP : State.addr (p + BitVec.ofNat 32 i) = State.addr p + BitVec.ofNat 64 i := addr_add (by omega_arith)
  obtain aC : State.addr (c + BitVec.ofNat 32 i) = State.addr c + BitVec.ofNat 64 i := addr_add (by omega_arith)
  refine wp_ldrb (a := State.addr p + BitVec.ofNat 64 i) (by decide) (by rw [x6, BitVec.add_zero, aP])
    (by rw [rd, wr]; exact hr _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    fun t₁ u₁ => ?_
  refine wp_strb (a := State.addr c + BitVec.ofNat 64 i) (by decide)
    (by rw [u₁.other _ (by decide), x2, BitVec.add_zero, aC])
    (by rw [u₁.wr, wr]; exact hw _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    fun t₂ v₂ => ?_
  refine wp_add (op2_imm (by decide)) fun t₃ u₃ => wp_add (op2_imm (by decide)) fun t₄ u₄ =>
    wp_subs (op2_imm (by decide)) fun t₅ u₅ z₅ => WP.block_nil ?_
  obtain hlen : (Spec.Aes.bytesAt s.mem (State.addr p) i).length = i := Proof.Cmac.bytesAt_length _ _ _
  obtain hx : writeBytes s.mem (State.addr c) (Spec.Aes.bytesAt s.mem (State.addr p) i) (State.addr p + BitVec.ofNat 64 i) =
      s.mem (State.addr p + BitVec.ofNat 64 i) :=
    (writeBytes_frame s.mem (State.addr c) _ (R := ⟨State.addr c, i⟩) (by rw [hlen]; exact Region.contains_self _ _)) _
      fun r hr hcon => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hd _ (Offset.contains_base _ (by omega_arith) (by omega_arith)) (Region.sub_prefix (by omega_arith) _ hcon)
  obtain hmem : t₅.mem = writeBytes s.mem (State.addr c) (Spec.Aes.bytesAt s.mem (State.addr p) (i + 1)) := by
    rw [u₅.mem, u₄.mem, u₃.mem, v₂.mem, u₁.gpr, u₁.mem, mem, byte_rt32, hx, Proof.Cmac.bytesAt_succ,
      writeBytes_snoc s.mem _ _ _ (by rw [hlen]; omega_arith), hlen]
  obtain x1' : t₅.gpr .r1 = BitVec.ofNat 32 (L - (i + 1)) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), x1,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega_arith)]; rfl
  obtain ev : isa.eval .ne t₅ = some !decide (L - (i + 1) = 0) := by
    show VG.Arm.eval .ne t₅ = _
    rw [eval_ne, z₅, u₄.other _ (by decide), u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), x1,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega_arith), Nat.sub_sub,
      ofNat_beq_zero (by omega_arith)]
  obtain gg : ∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r6 → r ≠ .r12 → t₅.gpr r = s.gpr r := fun r h₁ h₂ h₆ h₁₂ => by
    rw [u₅.other _ h₁, u₄.other _ h₂, u₃.other _ h₆, v₂.gpr, u₁.other _ h₁₂, g r h₁ h₂ h₆ h₁₂]
  obtain x2' : t₅.gpr .r2 = c + BitVec.ofNat 32 (i + 1) := by
    rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), x2,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.add_add]
  obtain x6' : t₅.gpr .r6 = p + BitVec.ofNat 32 (i + 1) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, v₂.gpr, u₁.other _ (by decide), x6,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.add_add]
  obtain sp' : t₅.sp = s.sp := by rw [u₅.sp, u₄.sp, u₃.sp, v₂.sp, u₁.sp, sp]
  obtain rd' : t₅.rd = s.rd := by rw [u₅.rd, u₄.rd, u₃.rd, v₂.rd, u₁.rd, rd]
  obtain wr' : t₅.wr = s.wr := by rw [u₅.wr, u₄.wr, u₃.wr, v₂.wr, u₁.wr, wr]
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
  obtain g₂ : ∀ r, r ≠ .r7 → s₂.gpr r = s.gpr r := fun r hr => by rw [f₂.gpr, u₁.other _ hr]
  obtain r7₂ : s₂.gpr .r7 = BitVec.ofNat 32 (x - L) := by rw [f₂.gpr, u₁.gpr, h7, h1, sub_ofNat hLx]
  rw [show s₁.gpr .r1 = BitVec.ofNat 32 L by rw [u₁.other _ (by decide), h1]] at z₂
  obtain ev := eq_iff s₂ z₂ (by omega_arith)
  obtain sp₂ : s₂.sp = s.sp := by rw [f₂.sp, u₁.sp]
  obtain rd₂ : s₂.rd = s.rd := by rw [f₂.rd, u₁.rd]
  obtain wr₂ : s₂.wr = s.wr := by rw [f₂.wr, u₁.wr]
  obtain m₂ : s₂.mem = s.mem := by rw [f₂.mem, u₁.mem]
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
  obtain g : ∀ r, r ≠ .r0 → r ≠ .r12 → s₅.gpr r = s.gpr r := fun r a b => by
    rw [f₅.gpr, u₄.other _ b, u₃.other _ a, u₂.other _ a, u₁.other _ a]
  obtain ev : isa.eval .eq s₅ = some (decide (c = 0)) := by
    show VG.Arm.eval .eq s₅ = _
    rw [VG.Proof.MdStream.Arm.eval_eq, z₅, u₄.gpr]
    simp (disch := decide) only [u₃.other, u₂.other, u₁.other]
    exact congrArg some (or_beq_zero hcnt hc)
  obtain r0 : s₅.gpr .r0 = ((s.gpr .r2 - 1) &&& 15) + 1 := by
    rw [f₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.gpr]
  obtain m : s₅.mem = s.mem := by rw [f₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain sp : s₅.sp = s.sp := by rw [f₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  obtain rd : s₅.rd = s.rd := by rw [f₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  obtain wr : s₅.wr = s.wr := by rw [f₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
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
  obtain g₄ : ∀ r, r ≠ .r1 → r ≠ .r12 → s₄.gpr r = s.gpr r := fun r a b => by
    rw [f₄.gpr, u₃.other _ b, u₂.other _ a, u₁.other _ a]
  obtain r1₄ : s₄.gpr .r1 = BitVec.ofNat 32 (16 - h) := by
    rw [f₄.gpr, u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), h0]; exact sub_ofNat hh
  obtain z : s₄.z = (BitVec.ofNat 32 (L / 16) - 0 == 0) := by
    rw [z₄, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h7, shr4 hL]
  obtain ev := eq_iff s₄ z (by omega_arith)
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
      obtain zz : t₃.z = (BitVec.ofNat 32 ((L + h) / 16) - 0 == 0) := by
        rw [y₃, v₂.gpr, v₁.gpr, g₄ .r7 (by decide) (by decide), g₄ .r0 (by decide) (by decide), h7, h0,
          ← BitVec.ofNat_add, shr4 (by omega_arith)]
      obtain ev' := eq_iff t₃ zz (by omega_arith)
      obtain gt : ∀ r, r ≠ .r12 → t₃.gpr r = s₄.gpr r := fun r a => by rw [e₃.gpr, v₂.other _ a, v₁.other _ a]
      obtain mt : t₃.mem = s₄.mem := by rw [e₃.mem, v₂.mem, v₁.mem]
      obtain spt : t₃.sp = s₄.sp := by rw [e₃.sp, v₂.sp, v₁.sp]
      obtain rdt : t₃.rd = s₄.rd := by rw [e₃.rd, v₂.rd, v₁.rd]
      obtain wrt : t₃.wr = s₄.wr := by rw [e₃.wr, v₂.wr, v₁.wr]
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
  obtain ev := eq_iff s₂ (k := x) (by rw [z₂, u₁.other _ (by decide), h7]) hx
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
  obtain ev := eq_iff s₁ (k := x) (by rw [z₁, h7]) hx
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
      obtain e9 : t₂.gpr .r9 = BitVec.ofNat 32 ((x - 1) / 16) := by
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
  obtain r7 : t₂.gpr .r7 = BitVec.ofNat 32 (x - 16 * n) := by
    rw [v₂.gpr, v₁.other _ (by decide), v₁.other _ (by decide), h7, h8, sub_ofNat hn]
  refine ⟨by rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide), v₁.gpr, h6, h8],
    by rw [v₄.other _ (by decide), v₃.other _ (by decide), r7], by rw [v₄.other _ (by decide), v₃.gpr, r7],
    by rw [v₄.gpr, v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide), h4]; rfl,
    fun r a b c d => by rw [v₄.other _ b, v₃.other _ a, v₂.other _ d, v₁.other _ c],
    by rw [v₄.mem, v₃.mem, v₂.mem, v₁.mem], by rw [v₄.sp, v₃.sp, v₂.sp, v₁.sp],
    by rw [v₄.rd, v₃.rd, v₂.rd, v₁.rd], by rw [v₄.wr, v₃.wr, v₂.wr, v₁.wr]⟩

end VG.Proof.CmacAes.Stream.Arm

end

end


/-!
# Streaming AES-CMAC on ARMv7: `vg_cmac_aes_absorb` up to the first call

The code saves the registers, computes the bytes held back `h`, copies `f =
min(len, 16 - h)` bytes after them, and sets up the first call of
`vg_cmac_aes_update`, which chains the block held back if data is left
(`AMid₁`).
-/

@[expose] public section

namespace VG.Proof.CmacAes.Stream.Arm

open VG VG.Arm VG.Impl.CmacAes.Stream.Arm VG.WriteBytes
open VG.Impl.CmacAes.Arm (mov)
open VG.Proof.MdStream.Arm (Upd Mupd op2_reg wp_mov wp_ldrSp saveMem saveList_ok saveMem_frame
  readW_writeW_save)
open VG.Proof.CmacAes.Arm (saveMem_congr)
open VG.Proof.Cmac.Stream (held held_le)

/-- The precondition, by name: the state `St`, the `L` bytes of data at `D`,
the scratch buffer `S` and the rounds `R`. -/
structure APre (s₀ : State) (St D S : BitVec 32) (L R : Nat) : Prop where
  r0 : s₀.gpr .r0 = St
  a0 : stackArg s₀ 0 = D
  a1 : (stackArg s₀ 1).toNat = L
  a2 : stackArg s₀ 2 = S
  r1 : (s₀.gpr .r1).toNat = R
  rd : s₀.rd = [⟨State.addr D, L⟩, ⟨stackArgAddr s₀ 0, 12⟩]
  wr : s₀.wr = [⟨State.addr St, 304⟩, ⟨State.addr S, 2304⟩]
  st_d : (⟨State.addr St, 304⟩ : Region).Disjoint ⟨State.addr D, L⟩
  st_s : (⟨State.addr St, 304⟩ : Region).Disjoint ⟨State.addr S, 2304⟩
  d_s : (⟨State.addr D, L⟩ : Region).Disjoint ⟨State.addr S, 2304⟩
  a_st : (⟨stackArgAddr s₀ 0, 12⟩ : Region).Disjoint ⟨State.addr St, 304⟩
  a_s : (⟨stackArgAddr s₀ 0, 12⟩ : Region).Disjoint ⟨State.addr S, 2304⟩
  b_st : (blw16 s₀).Disjoint ⟨State.addr St, 304⟩
  b_d : (blw16 s₀).Disjoint ⟨State.addr D, L⟩
  b_s : (blw16 s₀).Disjoint ⟨State.addr S, 2304⟩
  fSt : St.toNat + 304 ≤ 2 ^ 32
  fD : D.toNat + L ≤ 2 ^ 32
  fS : S.toNat + 2304 ≤ 2 ^ 32
  sp : 16 ≤ s₀.sp.toNat
  spf : s₀.sp.toNat + 12 ≤ 2 ^ 32
  rounds : R = 10 ∨ R = 12 ∨ R = 14

theorem APre.of {s₀ : State} (h : absorbArm.pre s₀) :
    APre s₀ (s₀.gpr .r0) (stackArg s₀ 0) (stackArg s₀ 2) (stackArg s₀ 1).toNat (s₀.gpr .r1).toNat :=
  let ⟨a, b, c, d, e, f, g, i, j, k, l, m, n, o, p, q⟩ := h
  ⟨rfl, rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, i, j, k, l, m, n, o, p, q⟩

section
variable {s₀ : State} {St D S : BitVec 32} {L R : Nat} (hp : APre s₀ St D S L R)
include hp

theorem APre.lt : L < 2 ^ 32 := by rw [← hp.a1]; exact BitVec.isLt _

theorem APre.a1' : stackArg s₀ 1 = BitVec.ofNat 32 L :=
  BitVec.eq_of_toNat_eq (by rw [hp.a1, toNat_ofNat32 hp.lt])

theorem APre.r1' : s₀.gpr .r1 = BitVec.ofNat 32 R :=
  BitVec.eq_of_toNat_eq (by rw [hp.r1, toNat_ofNat32 (by rcases hp.rounds with h | h | h <;> omega_using [h])])

theorem APre.argAddr {k : Nat} (hk : k < 3) : stackArgAddr s₀ k = stackArgAddr s₀ 0 + BitVec.ofNat 64 (4 * k) := by
  have := hp.spf
  simp only [stackArgAddr]
  rw [addr_add (by omega_using [hk, this]), addr_add (by omega_using [])]
  simp

theorem APre.arg_sub {k : Nat} (hk : k < 3) : Region.Sub ⟨stackArgAddr s₀ k, 4⟩ ⟨stackArgAddr s₀ 0, 12⟩ := by
  rw [hp.argAddr hk]; exact Offset.sub_base _ (by omega_using [hk])

theorem APre.arg_in {k : Nat} (hk : k < 3) : InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ k) 4 := by
  refine ⟨⟨stackArgAddr s₀ 0, 12⟩, by rw [hp.rd]; simp, ?_⟩
  rw [hp.argAddr hk]; exact Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])

/-- Offsets in the state. -/
theorem APre.aS {k : Nat} (hk : k < 304) : State.addr (St + BitVec.ofNat 32 k) = State.addr St + BitVec.ofNat 64 k :=
  addr_add (by have := hp.fSt; omega_using [hk, this])

theorem APre.inSt {d n : Nat} (h : d + n ≤ 304) :
    Covers [⟨State.addr St + BitVec.ofNat 64 d, n⟩] s₀.wr := by
  rw [hp.wr]
  exact Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨State.addr St, 304⟩, by simp, d, rfl, h⟩

theorem APre.inS {d n : Nat} (h : d + n ≤ 2304) :
    Covers [⟨State.addr S + BitVec.ofNat 64 d, n⟩] s₀.wr := by
  rw [hp.wr]
  exact Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨State.addr S, 2304⟩, by simp, d, rfl, h⟩

theorem APre.inD {d n : Nat} (h : d + n ≤ L) :
    Covers [⟨State.addr D + BitVec.ofNat 64 d, n⟩] (s₀.rd ++ s₀.wr) := by
  rw [hp.rd, hp.wr]
  exact Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨State.addr D, L⟩, by simp, d, rfl, h⟩

/-- The arguments of a call of `vg_cmac_aes_update` on `n` blocks at `Dd`,
from a state with the permissions and stack of `s₀`. -/
theorem APre.uargs {s : State} {Dd : BitVec 32} {n : Nat} (hr0 : s.gpr .r0 = St) (hr1 : s.gpr .r1 = s₀.gpr .r1)
    (hr2 : s.gpr .r2 = St + BitVec.ofNat 32 272) (hr3 : s.gpr .r3 = Dd) (hr9 : s.gpr .r9 = BitVec.ofNat 32 n)
    (hr10 : s.gpr .r10 = S) (hsp : s.sp = s₀.sp) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hn : 16 * n < 2 ^ 32)
    (hdc : (⟨State.addr Dd, 16 * n⟩ : Region).Disjoint ⟨State.addr St + BitVec.ofNat 64 272, 16⟩)
    (hds : (⟨State.addr Dd, 16 * n⟩ : Region).Disjoint ⟨State.addr S, 2304⟩)
    (hbd : (blw16 s₀).Disjoint ⟨State.addr Dd, 16 * n⟩) (hfD : Dd.toNat + 16 * n ≤ 2 ^ 32)
    (hcov : Covers [⟨State.addr Dd, 16 * n⟩] (s₀.rd ++ s₀.wr)) :
    UArgs s St (St + BitVec.ofNat 32 272) Dd S R n := by
  have hw := hp.fSt
  obtain a272 := hp.aS (k := 272) (by decide)
  obtain c272 : Region.Sub ⟨State.addr St + BitVec.ofNat 64 272, 16⟩ ⟨State.addr St, 304⟩ :=
    Offset.sub_base _ (by decide)
  obtain hb : blw16 s = blw16 s₀ := by rw [blw16, hsp]
  exact
  { r0 := hr0, r2 := hr2, r3 := hr3, r9 := hr9, r10 := hr10, rounds := hp.rounds, hn := hn
    r1 := by rw [hr1]; exact hp.r1'
    hsp := by rw [hsp]; exact hp.sp
    wc := by rw [a272]; exact Offset.base_disjoint _ (by decide) (by omega_using [])
    ws := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    dc := by rw [a272]; exact hdc
    ds := hds.sub_right (Region.sub_prefix (by decide))
    cs := by rw [a272]; exact (hp.st_s.sub_left c272).sub_right (Region.sub_prefix (by decide))
    bw := by rw [hb]; exact hp.b_st.sub_right (Region.sub_prefix (by decide))
    bd := by rw [hb]; exact hbd
    bc := by rw [hb, a272]; exact hp.b_st.sub_right c272
    bs := by rw [hb]; exact hp.b_s.sub_right (Region.sub_prefix (by decide))
    fW := by omega_using [hw]
    fC := by rw [toNat_add_ofNat (by omega_using [hw])]; omega_using [hw]
    fD := hfD
    fS := by have := hp.fS; omega_using [this]
    reads := by
      rw [hrd, hwr]
      intro a k hi
      obtain ⟨r, hr, hc⟩ := hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Covers.right (hp.inSt (d := 0) (n := 240) (by decide)) a k
          ⟨_, List.mem_singleton_self _, by rw [BitVec.add_zero]; exact hc⟩
      · exact hcov a k ⟨_, List.mem_singleton_self _, hc⟩
    writes := by
      rw [hwr]
      intro a k hi
      obtain ⟨r, hr, hc⟩ := hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [a272] at hc; exact hp.inSt (d := 272) (n := 16) (by decide) a k ⟨_, List.mem_singleton_self _, hc⟩
      · exact hp.inS (d := 0) (n := 2176) (by decide) a k
          ⟨_, List.mem_singleton_self _, by rw [BitVec.add_zero]; exact hc⟩ }

end

/-! ## Saving the registers -/

theorem saved_bound : ∀ p ∈ saved, 2176 ≤ p.2 ∧ p.2 + 4 ≤ 2208 := by decide

theorem saved_ne_r12 : ∀ p ∈ saved, p.1 ≠ .r12 := by decide

theorem save_eq : save = .ldrSp .r12 8 :: (saved.map (fun p => Instr.str p.1 .r12 p.2) ++
    [mov .r4 .r0, mov .r5 .r1, .ldrSp .r6 0, .ldrSp .r7 4, mov .r10 .r12]) := rfl

/-- The memory after saving the registers. -/
def aMem (s₀ : State) (S : BitVec 32) : Mem := saveMem s₀.mem (State.addr S) s₀.gpr saved

theorem saved_slots : Spill.Slots 2176 2208 saved := by decide

theorem aMem_slot (s₀ : State) (S : BitVec 32) {r : Reg} {d : Nat} (h : (r, d) ∈ saved) :
    (aMem s₀ S).readW (State.addr S + BitVec.ofNat 64 d) 32 = s₀.gpr r :=
  Spill.saveMem_saved (State.addr S) s₀.gpr s₀.mem saved saved_slots (r, d) h

theorem aMem_frame (s₀ : State) (S : BitVec 32) : Frame [⟨State.addr S, 2304⟩] s₀.mem (aMem s₀ S) :=
  Spill.saveMem_frame _ _ _ (by decide) saved (by decide)

/-- What the saves leave. -/
structure ASave (s₀ : State) (St D S : BitVec 32) (L : Nat) (s : State) : Prop where
  r2 : s.gpr .r2 = s₀.gpr .r2
  r3 : s.gpr .r3 = s₀.gpr .r3
  r4 : s.gpr .r4 = St
  r5 : s.gpr .r5 = s₀.gpr .r1
  r6 : s.gpr .r6 = D
  r7 : s.gpr .r7 = BitVec.ofNat 32 L
  r10 : s.gpr .r10 = S
  keep : ∀ r ∈ preserved, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → r ≠ .r10 → s.gpr r = s₀.gpr r
  mem : s.mem = aMem s₀ S
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem save_wp {s₀ : State} {St D S : BitVec 32} {L R : Nat} (hp : APre s₀ St D S L R) :
    WP isa (.block save) s₀ (ASave s₀ St D S L) := by
  have hS := hp.fS
  rw [save_eq]
  refine wp_ldrSp (a := stackArgAddr s₀ 2) (by decide) rfl (hp.arg_in (by decide)) fun s₁ u₁ => ?_
  obtain h12 : s₁.gpr .r12 = S := by rw [u₁.gpr]; exact hp.a2
  refine saveList_ok saved s₁ _ (fun p hp' => ?_) fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  · have := saved_bound p hp'
    rw [h12, u₁.wr, hp.wr]
    exact ⟨by omega_using [this], by omega_using [hS, this], ⟨⟨State.addr S, 2304⟩, by simp, Offset.contains_base _ (by omega_using [this]) (by omega_using [this])⟩⟩
  obtain hm₂ : s₂.mem = aMem s₀ S := by
    rw [m₂, u₁.mem, h12, aMem]
    exact saveMem_congr _ _ _ fun p hp' => u₁.other _ (saved_ne_r12 p hp')
  have arg (k : Nat) (hk : k < 3) : (aMem s₀ S).readW (stackArgAddr s₀ k) 32 = stackArg s₀ k :=
    (aMem_frame s₀ S).readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.a_s.sub_left (hp.arg_sub hk)) (by decide)
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => ?_
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) (by rw [u₄.sp, u₃.sp, sp₂, u₁.sp]; rfl)
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂, wr₂, u₁.rd, u₁.wr]; exact hp.arg_in (by decide)) fun s₅ u₅ => ?_
  refine wp_ldrSp (a := stackArgAddr s₀ 1) (by decide) (by rw [u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp]; rfl)
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂, wr₂, u₁.rd, u₁.wr]; exact hp.arg_in (by decide))
    fun s₆ u₆ => wp_mov (op2_reg _ _) fun s₇ u₇ => WP.block_nil ?_
  obtain mm : ∀ {t : State}, t.mem = s₂.mem → t.mem = aMem s₀ S := fun h => h.trans hm₂
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr a b c d e => ?_, ?_, ?_, ?_, ?_⟩
  · simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, g₂, u₁.other]
  · simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, g₂, u₁.other]
  · simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.other, u₃.gpr, g₂, u₁.other, hp.r0]
  · simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.gpr, u₃.other, g₂, u₁.other]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem, hm₂, arg 0 (by decide), hp.a0]
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.mem, u₄.mem, u₃.mem, hm₂, arg 1 (by decide), hp.a1']
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      g₂, h12]
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl a
    | exact absurd rfl b
    | exact absurd rfl c
    | exact absurd rfl d
    | exact absurd rfl e
    | simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, g₂, u₁.other]
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, hm₂]
  · rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp]
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr]

/-! ## Up to the first call -/

/-- The memory after the saves and the first copy. -/
def m4 (s₀ : State) (St D S : BitVec 32) (c L : Nat) : Mem :=
  writeBytes (aMem s₀ S) (State.addr (St + BitVec.ofNat 32 (288 + held c)))
    (Spec.Aes.bytesAt (aMem s₀ S) (State.addr D) (fOf c L))

/-- What the code before the first call leaves. -/
structure AMid₁ (s₀ : State) (St D S : BitVec 32) (L R : Nat) (s : State) : Prop where
  args : UArgs s St (St + BitVec.ofNat 32 272) (St + BitVec.ofNat 32 288) S R (b1Of (countArm s₀).toNat L)
  r4 : s.gpr .r4 = St
  r5 : s.gpr .r5 = s₀.gpr .r1
  r6 : s.gpr .r6 = D + BitVec.ofNat 32 (fOf (countArm s₀).toNat L)
  r7 : s.gpr .r7 = BitVec.ofNat 32 (leftOf (countArm s₀).toNat L)
  r10 : s.gpr .r10 = S
  sp : s.sp = s₀.sp
  keep : ∀ r ∈ preserved, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  mem : s.mem = m4 s₀ St D S (countArm s₀).toNat L
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem absorbPre_wp {s₀ : State} {St D S : BitVec 32} {L R : Nat} (hp : APre s₀ St D S L R) :
    WP isa absorbPre s₀ (AMid₁ s₀ St D S L R) := by
  generalize hc : (countArm s₀).toNat = c
  obtain hcl : c < 2 ^ 64 := by rw [← hc]; exact BitVec.isLt _
  have hL := hp.lt
  have hw := hp.fSt
  have hD := hp.fD
  have ⟨hfL, hfh⟩ := f_le c L
  obtain hh := held_le c
  refine WP.seq (WP.mono (save_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (held_wp (c := c) hcl (by rw [h₁.r3, h₁.r2, count_eq, hc]))
    fun s₂ ⟨r0₂, g₂, m₂, sp₂, rd₂, wr₂⟩ => ?_)
  refine WP.seq (WP.mono (fill_wp (St := St) (held_le c) hL r0₂ (by rw [g₂ _ (by decide) (by decide), h₁.r7])
    (by rw [g₂ _ (by decide) (by decide), h₁.r4])) fun s₃ ⟨r1₃, r2₃, g₃, m₃, sp₃, rd₃, wr₃⟩ => ?_)
  have g (r : Reg) (a : r ≠ .r0) (b : r ≠ .r1) (c : r ≠ .r2) (d : r ≠ .r12) : s₃.gpr r = s₁.gpr r := by
    rw [g₃ r b c d, g₂ r a d]
  obtain rd₃' : s₃.rd = s₀.rd := by rw [rd₃, rd₂, h₁.rd]
  obtain wr₃' : s₃.wr = s₀.wr := by rw [wr₃, wr₂, h₁.wr]
  refine WP.seq (WP.mono (copy_wp (p := D) (c := St + BitVec.ofNat 32 (288 + held c)) (L := fOf c L) (x := L)
    hfL hL (by rw [g _ (by decide) (by decide) (by decide) (by decide), h₁.r6]) r2₃ (by rw [r1₃]; rfl)
    (by rw [g _ (by decide) (by decide) (by decide) (by decide), h₁.r7]) fun hpos => ?_) fun s₄ h₄ => ?_)
  · have hlt : 288 + held c < 304 := by unfold fOf at hpos; omega_using [hpos]
    obtain aDst' : State.addr (St + BitVec.ofNat 32 (288 + held c)) = State.addr St + BitVec.ofNat 64 (288 + held c) :=
      hp.aS hlt
    exact
    { fp := by omega_using [hD, hfL]
      fc := by rw [toNat_add_ofNat (by omega_using [hw, hlt])]; omega_using [hw, hfh]
      hr := by
        rw [rd₃', wr₃']
        have := hp.inD (d := 0) (n := fOf c L) (by omega_using [hfL])
        rwa [BitVec.add_zero] at this
      hw := by rw [wr₃', aDst']; exact hp.inSt (by omega_using [hfh])
      hd := by
        rw [aDst']
        exact (hp.st_d.sub_left (Offset.sub_base _ (by omega_using [hfh]))).symm.sub_left (Region.sub_prefix hfL) }
  have g' (r : Reg) (a : r ≠ .r0) (b : r ≠ .r1) (c : r ≠ .r2) (d : r ≠ .r12) (e : r ≠ .r6) (f : r ≠ .r7) :
      s₄.gpr r = s₁.gpr r := by rw [h₄.other r b c e f d, g r a b c d]
  refine WP.mono (chain1_wp (x := leftOf c L) (by unfold leftOf; omega_using [hL]) (by rw [h₄.r7]; rfl)
    (by rw [g' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h₁.r4])) fun s₅ h₅ => ?_
  obtain ⟨r9₅, r0₅, r1₅, r2₅, r3₅, g₅, m₅, sp₅, rd₅, wr₅⟩ := h₅
  have k (r : Reg) (a : r ≠ .r0) (b : r ≠ .r1) (c : r ≠ .r2) (d : r ≠ .r3) (e : r ≠ .r9) (f : r ≠ .r12) (i : r ≠ .r6)
      (j : r ≠ .r7) : s₅.gpr r = s₁.gpr r := by rw [g₅ r a b c d e, g' r a b c f i j]
  obtain hrd : s₅.rd = s₀.rd := by rw [rd₅, h₄.rd, rd₃']
  obtain hwr : s₅.wr = s₀.wr := by rw [wr₅, h₄.wr, wr₃']
  obtain hsp : s₅.sp = s₀.sp := by rw [sp₅, h₄.sp, sp₃, sp₂, h₁.sp]
  obtain hb1 : 16 * b1Of c L ≤ 16 := by unfold b1Of; split <;> omega_using []
  obtain a288 := hp.aS (k := 288) (by decide)
  obtain c288 : Region.Sub ⟨State.addr (St + BitVec.ofNat 32 288), 16 * b1Of c L⟩ ⟨State.addr St, 304⟩ := by
    rw [a288]; exact Offset.sub_base _ (by omega_using [hb1])
  subst hc
  refine ⟨hp.uargs (Dd := St + BitVec.ofNat 32 288) r0₅ (by rw [r1₅, h₄.other _ (by decide) (by decide) (by decide)
      (by decide) (by decide), g _ (by decide) (by decide) (by decide) (by decide), h₁.r5]) r2₅ r3₅
      (by rw [r9₅, b1Of, leftOf]) (by rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), h₁.r10]) hsp hrd hwr (by omega_using [hb1])
      (by rw [a288]; exact Offset.disjoint _ (by omega_using []) (by omega_using [hb1]) (by omega_using []))
      ((hp.st_s.sub_left c288))
      (hp.b_st.sub_right c288) (by rw [toNat_add_ofNat (by omega_using [hw])]; omega_using [hw, hb1])
      (Covers.right (by rw [a288]; exact hp.inSt (by omega_using [hb1]))), ?_, ?_, ?_, ?_, ?_, hsp, ?_, ?_, hrd, hwr⟩
  · rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h₁.r4]
  · rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h₁.r5]
  · rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide), h₄.r6]
  · rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide), h₄.r7]; rfl
  · rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h₁.r10]
  · intro r hr a b c d e f
    have : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [k r this.1 this.2.1 this.2.2.1 this.2.2.2.1 e this.2.2.2.2 c d, h₁.keep r hr a b c d f]
  · rw [m₅, h₄.mem, m₃, m₂, h₁.mem, m4]

end VG.Proof.CmacAes.Stream.Arm
