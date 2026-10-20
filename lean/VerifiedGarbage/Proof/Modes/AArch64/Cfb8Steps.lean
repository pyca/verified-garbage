module

import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Impl.Modes.AArch64.Cfb8
public import Mathlib.Data.List.Induction
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.PlainSimp
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Modes.AArch64.Steps
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Spec.Aes
import VerifiedGarbage.Proof.AesCtr.Inc

/-!
# CFB8 on AArch64, for any core: the byte and the shift

As on x86-64 (`Proof/Modes/X86_64/Cfb8Steps.lean`). `cfb8Xor_wp`: the
output's first byte XORed into the data's byte, the ciphertext byte left in
`x6`. `cfb8Shift_wp`: the input block, at the IV, shifted left by a byte in
place, with the low byte of `x6` shifted in: each byte but the last is the
one after it (`shl1`, one `shiftByte` at a time), and the last is `x6`'s.
-/

@[expose] public section

namespace VG.Proof.Modes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Modes.AArch64
open VG.Impl.Aes.AArch64 (sb movR ldS stS eorR)
open VG.Spec.Aes (bytesAt)
open VG.WriteBytes (writeW8_apply)

variable {c : Core}

theorem read_one (m : Mem) (a : Addr) : m.read a 1 = m a := by
  apply BitVec.eq_of_toNat_eq
  simp only [Mem.read, BitVec.toNat_append]
  simp

/-- `ldrb wd, [r, #off]`. -/
theorem ldrb_ok (s : State) (d r : Reg) {off : Nat} (ho : off < 4096)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr r + BitVec.ofNat 64 off) 1) :
    ∃ s', runBlock isa [.ldrb d r off] s = some s' ∧
      s'.gpr d = (s.mem (s.gpr r + BitVec.ofNat 64 off)).setWidth 64 ∧
      (∀ x, x ≠ d → s'.gpr x = s.gpr x) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨s.write .w d ((s.mem.read (s.gpr r + BitVec.ofNat 64 off) 1).setWidth 32), ?_, ?_,
    fun x hx => RegUpd.gpr_write_of_ne _ _ _ hx, rfl, rfl, rfl⟩
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, Nat.mod_one,
      show off < 4096 * 1 by omega, and_self, ite_true, Option.bind_some, State.load, hr, Option.map_some]
  · rw [RegUpd.gpr_write_self]
    apply BitVec.eq_of_toNat_eq
    have := (s.mem (s.gpr r + BitVec.ofNat 64 off)).isLt
    simp only [read_one, BitVec.toNat_setWidth, Size.bits]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

/-- `strb wv, [r, #off]`. -/
theorem strb_ok (s : State) (r v : Reg) {off : Nat} (ho : off < 4096)
    (hw : InRegions s.wr (s.gpr r + BitVec.ofNat 64 off) 1) :
    ∃ s', runBlock isa [.strb v r off] s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr r + BitVec.ofNat 64 off) ((s.gpr v).setWidth 8) ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨{ s with mem := s.mem.writeW (s.gpr r + BitVec.ofNat 64 off) ((s.gpr v).setWidth 8) }, ?_, rfl, rfl, rfl,
    rfl⟩
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, Nat.mod_one,
    show off < 4096 * 1 by omega, and_self, ite_true, Option.bind_some, State.store, hw, State.read, Size.bits]
  rw [BitVec.setWidth_setWidth_of_le _ (by decide)]
  rfl

theorem setWidth_byte (b : Byte) : (b.setWidth 64).setWidth 8 = b := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

theorem setWidth_xor_byte (a b : Byte) : (a.setWidth 64 ^^^ b.setWidth 64).setWidth 8 = a ^^^ b := by
  rw [BitVec.setWidth_xor, setWidth_byte, setWidth_byte]

/-- The output's first byte, at `T` (`sb + 8 buf`), XORed into the data's
byte at `A` (`dataReg`): the data's byte becomes their XOR, and `x6`'s low
byte the ciphertext byte. -/
theorem cfb8Xor_wp (enc : Bool) (hbI : 8 * c.buf < 4096) {s : State} {A T : Addr} (hA : s.gpr c.dataReg = A)
    (hT : s.gpr sb + BitVec.ofNat 64 (8 * c.buf) = T) (d6 : c.dataReg ≠ .x6) (d7 : c.dataReg ≠ .x7)
    (wA : InRegions s.wr A 1) (rT : InRegions (s.rd ++ s.wr) T 1) :
    WP isa (.block (c.cfb8Xor enc)) s fun s' => (∀ x, x ≠ .x6 → x ≠ .x7 → s'.gpr x = s.gpr x) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem.writeW A (s.mem A ^^^ s.mem T) ∧
      (s'.gpr .x6).setWidth 8 = (if enc then s.mem A ^^^ s.mem T else s.mem A) := by
  have p0 : ∀ X : Addr, X + BitVec.ofNat 64 0 = X := fun X => by simp
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := ldrb_ok s .x6 c.dataReg (off := 0) (by decide)
    (by rw [hA, p0]; exact inRd wA)
  obtain ⟨s₂, e₂, v₂, o₂, m₂, rd₂, wr₂⟩ := ldrb_ok s₁ .x7 sb (off := 8 * c.buf) hbI
    (by rw [rd₁, wr₁, o₁ _ (by decide), hT]; exact rT)
  have a₂ : s₂.gpr .x6 = (s.mem A).setWidth 64 := by rw [o₂ _ (by decide), v₁, hA, p0]
  have b₂ : s₂.gpr .x7 = (s.mem T).setWidth 64 := by rw [v₂, m₁, o₁ _ (by decide), hT]
  have d₂ : s₂.gpr c.dataReg = A := by rw [o₂ _ d7, o₁ _ d6, hA]
  cases enc
  · obtain ⟨s₃, e₃, v₃, o₃, m₃, rd₃, wr₃⟩ := eor_ok s₂ .x7 .x7 .x6
    obtain ⟨s₄, e₄, m₄, g₄, rd₄, wr₄⟩ := strb_ok s₃ c.dataReg .x7 (off := 0) (by decide)
      (by rw [wr₃, wr₂, wr₁, o₃ _ d7, d₂, p0]; exact wA)
    refine WP.of_runBlock ⟨s₄, ?_, fun x h1 h2 => by rw [g₄, o₃ x h2, o₂ x h2, o₁ x h1], by
      rw [rd₄, rd₃, rd₂, rd₁], by rw [wr₄, wr₃, wr₂, wr₁], ?_, ?_⟩
    · simp only [Core.cfb8Xor, Bool.false_eq_true, ite_false]
      rw [show ([.ldrb .x6 c.dataReg 0, .ldrb .x7 sb (8 * c.buf), eorR .x7 .x7 .x6, .strb .x7 c.dataReg 0] :
        List Instr) = [.ldrb .x6 c.dataReg 0] ++ ([.ldrb .x7 sb (8 * c.buf)] ++ ([eorR .x7 .x7 .x6] ++
        [.strb .x7 c.dataReg 0])) from rfl, runBlock_app, e₁, Option.bind_some, runBlock_app, e₂,
        Option.bind_some, runBlock_app, e₃, Option.bind_some, e₄]
    · rw [m₄, m₃, m₂, m₁, o₃ _ d7, d₂, p0, v₃, a₂, b₂, setWidth_xor_byte, BitVec.xor_comm]
    · rw [g₄, o₃ _ (by decide), a₂, setWidth_byte]; rfl
  · obtain ⟨s₃, e₃, v₃, o₃, m₃, rd₃, wr₃⟩ := eor_ok s₂ .x6 .x6 .x7
    obtain ⟨s₄, e₄, m₄, g₄, rd₄, wr₄⟩ := strb_ok s₃ c.dataReg .x6 (off := 0) (by decide)
      (by rw [wr₃, wr₂, wr₁, o₃ _ d6, d₂, p0]; exact wA)
    refine WP.of_runBlock ⟨s₄, ?_, fun x h1 h2 => by rw [g₄, o₃ x h1, o₂ x h2, o₁ x h1], by
      rw [rd₄, rd₃, rd₂, rd₁], by rw [wr₄, wr₃, wr₂, wr₁], ?_, ?_⟩
    · simp only [Core.cfb8Xor, ite_true]
      rw [show ([.ldrb .x6 c.dataReg 0, .ldrb .x7 sb (8 * c.buf), eorR .x6 .x6 .x7, .strb .x6 c.dataReg 0] :
        List Instr) = [.ldrb .x6 c.dataReg 0] ++ ([.ldrb .x7 sb (8 * c.buf)] ++ ([eorR .x6 .x6 .x7] ++
        [.strb .x6 c.dataReg 0])) from rfl, runBlock_app, e₁, Option.bind_some, runBlock_app, e₂,
        Option.bind_some, runBlock_app, e₃, Option.bind_some, e₄]
    · rw [m₄, m₃, m₂, m₁, o₃ _ d6, d₂, p0, v₃, a₂, b₂, setWidth_xor_byte]
    · rw [g₄, v₃, a₂, b₂, setWidth_xor_byte]; rfl

/-- `m` with each of the first `i` bytes at `P` replaced by the byte after
it. -/
def shl1 (m : Mem) (P : Addr) (i : Nat) : Mem := fun x => if (x - P).toNat < i then m (x + 1) else m x

theorem shl1_zero (m : Mem) (P : Addr) : shl1 m P 0 = m := by funext x; simp [shl1]

theorem sub_eq_iff {x P : Addr} {i : Nat} (hi : i < 2 ^ 64) : x = P + BitVec.ofNat 64 i ↔ (x - P).toNat = i := by
  constructor
  · rintro rfl; rw [VG.Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]
  · intro h
    have : x - P = BitVec.ofNat 64 i := BitVec.eq_of_toNat_eq (by rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi])
    rw [← this, BitVec.add_comm, BitVec.sub_add_cancel]

theorem ofNat_succ (i : Nat) : BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 i + 1 := by
  rw [← BitVec.ofNat_add_ofNat]; rfl

/-- The shift's byte moves, then the last byte. -/
theorem cfb8Shift_wp {ivR : Reg} (i7 : ivR ≠ .x7) {s : State} {P : Addr} (hc : s.gpr ivR = P)
    (hwP : (⟨P, 8 * c.bw⟩ : Region) ∈ s.wr) (hbw : 0 < c.bw) (hbw2 : c.bw ≤ 2) :
    WP isa (.block (c.cfb8Shift ivR)) s fun s' => (∀ x, x ≠ .x7 → s'.gpr x = s.gpr x) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ (∀ u < 8 * c.bw, s'.mem (P + BitVec.ofNat 64 u) =
        if u + 1 < 8 * c.bw then s.mem (P + BitVec.ofNat 64 (u + 1)) else (s.gpr .x6).setWidth 8) ∧
      Frame [⟨P, 8 * c.bw⟩] s.mem s'.mem := by
  have c₁ := hc
  have inP : ∀ {u}, u < 8 * c.bw → InRegions s.wr (P + BitVec.ofNat 64 u) 1 := fun hu =>
    ⟨_, hwP, VG.Offset.contains_base P (by omega) (by omega)⟩
  -- The byte moves.
  have hmv : WP isa (.block ((List.range (8 * c.bw - 1)).flatMap (Core.shiftByte ivR))) s fun s₂ =>
      (∀ x, x ≠ .x7 → s₂.gpr x = s.gpr x) ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr ∧
        s₂.mem = shl1 s.mem P (8 * c.bw - 1) := by
    refine wp_range_flatMap (M := isa) (N := 8 * c.bw - 1) (fun i s₂ => (∀ x, x ≠ .x7 → s₂.gpr x = s.gpr x) ∧
        s₂.rd = s.rd ∧ s₂.wr = s.wr ∧ s₂.mem = shl1 s.mem P i)
      (fun i s₂ hi ⟨g₂, rd₂, wr₂, m₂⟩ => ?_) _ (Nat.le_refl _) s ⟨fun _ _ => rfl, rfl, rfl, by rw [shl1_zero]⟩
    have hc : s₂.gpr ivR = P := by rw [g₂ _ i7, c₁]
    obtain ⟨s₃, e₃, v₃, o₃, m₃, rd₃, wr₃⟩ := ldrb_ok s₂ .x7 ivR (off := i + 1) (by omega)
      (by rw [rd₂, wr₂, hc]; exact inRd (inP (by omega)))
    obtain ⟨s₄, e₄, m₄, g₄, rd₄, wr₄⟩ := strb_ok s₃ ivR .x7 (off := i) (by omega)
      (by rw [wr₃, wr₂, o₃ _ i7, hc]; exact inP (by omega))
    refine WP.of_runBlock ⟨s₄, by
      rw [Core.shiftByte, show ([.ldrb .x7 ivR (i + 1), .strb .x7 ivR i] : List Instr) =
        [.ldrb .x7 ivR (i + 1)] ++ [.strb .x7 ivR i] from rfl, runBlock_app, e₃, Option.bind_some, e₄],
      fun x hx => by rw [g₄, o₃ x hx, g₂ x hx], by rw [rd₄, rd₃, rd₂], by rw [wr₄, wr₃, wr₂], ?_⟩
    rw [m₄, m₃, o₃ _ i7, v₃, hc, setWidth_byte, m₂]
    funext x
    rw [writeW8_apply]
    have h64 : 8 * c.bw < 2 ^ 64 := by omega
    have hP1 : shl1 s.mem P i (P + BitVec.ofNat 64 (i + 1)) = s.mem (P + BitVec.ofNat 64 (i + 1)) := by
      simp only [shl1]; rw [VG.Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        ite_eq_right (by omega)]
    rw [hP1]
    by_cases hx : x = P + BitVec.ofNat 64 i
    · rw [ite_eq_left hx]
      simp only [shl1]
      rw [ite_eq_left (by rw [(sub_eq_iff (by omega)).mp hx]; omega), hx, BitVec.add_assoc, ofNat_succ]
    · rw [ite_eq_right hx]
      have hne : (x - P).toNat ≠ i := fun h => hx ((sub_eq_iff (by omega)).mpr h)
      simp only [shl1]
      by_cases h1 : (x - P).toNat < i
      · rw [ite_eq_left h1, ite_eq_left (by omega)]
      · rw [ite_eq_right h1, ite_eq_right (by omega)]
  refine WP.block_append (WP.mono hmv fun s₂ ⟨g₂, rd₂, wr₂, m₂⟩ => ?_)
  have hc : s₂.gpr ivR = P := by rw [g₂ _ i7, c₁]
  obtain ⟨s₃, e₃, m₃, g₃, rd₃, wr₃⟩ := strb_ok s₂ ivR .x6 (off := 8 * c.bw - 1) (by omega)
    (by rw [wr₂, hc]; exact inP (by omega))
  refine WP.of_runBlock ⟨s₃, e₃, fun x h2 => by rw [g₃, g₂ x h2], by rw [rd₃, rd₂],
    by rw [wr₃, wr₂], fun u hu => ?_, ?_⟩
  · rw [m₃, hc, writeW8_apply, g₂ _ (by decide), m₂]
    by_cases hl : u + 1 < 8 * c.bw
    · rw [ite_eq_right (fun h => by
        have := (sub_eq_iff (x := P + BitVec.ofNat 64 u) (P := P) (by omega)).mp h
        rw [VG.Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        omega), ite_eq_left hl]
      simp only [shl1]
      rw [VG.Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), ite_eq_left (by omega),
        BitVec.add_assoc, ofNat_succ]
    · rw [ite_eq_left (by congr 2; omega), ite_eq_right hl]
  · rw [m₃, hc, m₂]
    intro x hx
    have hx' : ¬ (x - P).toNat < 8 * c.bw := fun h => hx _ List.mem_cons_self (by
      simp only [Region.Contains]; omega)
    rw [writeW8_apply, ite_eq_right (fun h => hx' (by rw [(sub_eq_iff (by omega)).mp h]; omega))]
    simp only [shl1]
    rw [ite_eq_right (by omega)]

end VG.Proof.Modes.AArch64
