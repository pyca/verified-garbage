module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyWs
public import VerifiedGarbage.Proof.Rsa.PPC64LE.Loops
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontStep
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The operations on the arrays of the working space: subtraction, selection, copy

As on ARMv7 (`Proof/Rsa/Arm/KeyOps.lean`): `sub3_ok`, `sel_ok` and
`copy_ok`, on arrays apart from each other, each keeping the working space
(`Ws`), the memory but the array it writes (`KeyWorkspace.Keep`), and the
registers but `opRegs`.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Keys

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Loops
open VG.Impl.Rsa.PPC64LE.Keys (ptr sub3 sel copy subBody selBody copyBody countLoop)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot arr_disj)

/-- The registers the operations may change. -/
abbrev opRegs : List Reg := [.r0, .r3, .r5, .r6, .r7, .r8, .r9]

/-- The pointers of three arrays into `r5`, `r6` and `r7`. -/
theorem ptr3_ok {s : State} {B : Addr} {Z w N : Nat} (h : Ws s B Z w N) {o a b : Nat}
    (ho : o < 2 ^ 15) (ha : a < 2 ^ 15) (hb : b < 2 ^ 15) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, t.gpr .r5 = off B (arr w o) → t.gpr .r6 = off B (arr w a) → t.gpr .r7 = off B (arr w b) →
      Keep [.r5, .r6, .r7] s t → t.mem = s.mem → WP isa (.block rest) t Q) :
    WP isa (.block (ptr .r5 o ++ ptr .r6 a ++ ptr .r7 b ++ rest)) s Q := by
  rw [List.append_assoc, List.append_assoc]
  refine ptr_ok h (by decide) (by decide) (by decide) ho ?_
  refine ptr_ok (h.of_keep (Keep.write _ _ _)) (by decide) (by decide) (by decide) ha ?_
  refine ptr_ok ((h.of_keep (Keep.write _ _ _)).of_keep (Keep.write _ _ _)) (by decide) (by decide)
    (by decide) hb ?_
  exact k _ (by simp [gpr_write]) (by simp [gpr_write]) (by simp [gpr_write])
    (((Keep.write _ _ _).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)) rfl

/-- Two arrays apart are each ahead of the other. -/
theorem ahead_of_ne {w o a : Nat} (h : o ≠ a) : Ahead (arr w o) (arr w a) w := by
  have := arr_disj (w := w) h
  simp only [S] at this
  unfold Ahead; omega

/-- `sub3 o a b`: `[o] = [a] - [b]` with the borrow in `r9`. -/
theorem sub3_ok {s : State} {B : Addr} {Z w N o a b : Nat} (h : Ws s B Z w N)
    (ho : o < N) (ha : a < N) (hb : b < N) (hN : N ≤ 256) (hoa : o ≠ a) (hob : o ≠ b) :
    WP isa (sub3 o a b) s fun t => Ws t B Z w N ∧ KeyWorkspace.Keep B w [o] [] s.mem t.mem ∧
      num t.mem B w o + num s.mem B w b = num s.mem B w a + 2 ^ (32 * w) * (t.gpr .r9).toNat ∧
      (t.gpr .r9).toNat ≤ 1 ∧ Keep opRegs s t := by
  have fo := h.arr_fit ho
  have fa := h.arr_fit ha
  have fb := h.arr_fit hb
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wle
  rw [sub3, WP.seq_iff]
  refine ptr3_ok h (by omega) (by omega) (by omega) fun t p5 p6 p7 kt mt => ?_
  have ht : Ws t B Z w N := h.of_keep kt
  have hb : WP isa (.block [.addi .r8 .r29 0, .li .r9 0]) t fun u =>
      (u.gpr .r5 = off B (arr w o) ∧ u.gpr .r6 = off B (arr w a) ∧ u.gpr .r7 = off B (arr w b) ∧
        u.gpr .r8 = BitVec.ofNat 64 w ∧ u.gpr .r9 = 0 ∧ u.mem = t.mem) ∧ Keep [.r8, .r9] t u := by
    refine WP.keep _ ?_ (by decide)
    prun [p5, p6, p7, ht.r29, BitVec.add_zero]
    rfl
  refine WP.mono hb fun u ⟨⟨u5, u6, u7, u8, u9, mu⟩, ku⟩ => ?_
  have k₁ : Keep opRegs s u := (kt.trans ku).mono
  have hu : Ws u B Z w N := h.of_keep k₁
  refine WP.mono (subLoop_ok hu.scr u5 u6 u7 u8 (by rw [u9]; decide) h.wpos (by omega) (by omega)
    (by omega) (by omega) (ahead_of_ne hoa) (ahead_of_ne hob)) ?_
  intro t' ⟨b9, v, out, kt'⟩
  rw [u9, mu, mt] at v
  rw [mu, mt] at out
  exact ⟨hu.of_keep kt', KeyWorkspace.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using out)
    (by omega) (by simp), by simpa using v, b9, k₁.trans' kt'⟩

/-- The mask of a slot holding 0 or 1. -/
theorem mask_of_slot (x : BitVec 32) (h : x.toNat ≤ 1) :
    x.setWidth 64 = BitVec.ofNat 64 (if x.toNat = 0 then 0 else 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_ext32]
  split <;> simp only [BitVec.toNat_ofNat] <;> omega

/-- `sel o a b sl`: `[o] = [b]` if the slot `sl` is 1, `[a]` if it is 0. -/
theorem sel_ok {s : State} {B : Addr} {Z w N o a b sl : Nat} (h : Ws s B Z w N)
    (ho : o < N) (ha : a < N) (hb : b < N) (hN : N ≤ 256) (hoa : o ≠ a) (hob : o ≠ b)
    (hsl : sl + 4 ≤ KeyWorkspace.hdr) (bit : slot s.mem B sl ≤ 1) :
    WP isa (sel o a b sl) s fun t => Ws t B Z w N ∧ KeyWorkspace.Keep B w [o] [] s.mem t.mem ∧
      num t.mem B w o = (if slot s.mem B sl = 0 then num s.mem B w a else num s.mem B w b) ∧
      Keep opRegs s t := by
  have fo := h.arr_fit ho
  have fa := h.arr_fit ha
  have fb := h.arr_fit hb
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wle
  have hz : 160 ≤ Z := h.hdr_le
  have hsl' : sl + 4 ≤ 160 := hsl
  rw [sel, WP.seq_iff]
  refine ptr3_ok h (by omega) (by omega) (by omega) fun t p5 p6 p7 kt mt => ?_
  have ht : Ws t B Z w N := h.of_keep kt
  have hb : WP isa (.block [.addi .r8 .r29 0, .load .w .r9 .r31 sl, .li .r0 0, .sub .r9 .r0 .r9]) t
      fun u => (u.gpr .r5 = off B (arr w o) ∧ u.gpr .r6 = off B (arr w a) ∧ u.gpr .r7 = off B (arr w b) ∧
        u.gpr .r8 = BitVec.ofNat 64 w ∧
        u.gpr .r9 = BitVec.ofNat 64 0 - (t.mem.readW (off B sl) 32).setWidth 64 ∧ u.mem = t.mem) ∧
        Keep [.r0, .r8, .r9] t u := by
    refine WP.keep _ ?_ (by rfl)
    prun [p5, p6, p7, ht.r29, ht.r31, BitVec.add_zero, ht.scr.ld (show sl + 4 ≤ Z by omega),
      exec_load_w (show Reg.r31 ≠ .r0 by decide) (show sl < 2 ^ 15 by omega)]
  refine WP.mono hb fun u ⟨⟨u5, u6, u7, u8, u9, mu⟩, ku⟩ => ?_
  have k₁ : Keep opRegs s u := (kt.trans ku).mono
  have hu : Ws u B Z w N := h.of_keep k₁
  rw [mt, mask_of_slot _ bit] at u9
  refine WP.mono (selLoop_ok (b := decide (slot s.mem B sl ≠ 0)) hu.scr u5 u6 u7 u8
    (by rw [u9]; by_cases h0 : slot s.mem B sl = 0 <;> simp [h0]) h.wpos (by omega) (by omega)
    (by omega) (by omega) (ahead_of_ne hoa) (ahead_of_ne hob)) ?_
  intro t' ⟨v, out, kt'⟩
  rw [mu, mt] at v out
  refine ⟨hu.of_keep kt', KeyWorkspace.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using out)
    (by omega) (by simp), ?_, k₁.trans' (kt'.mono)⟩
  change val32 _ _ _ _ = _
  rw [v]
  by_cases h0 : slot s.mem B sl = 0 <;> simp [h0]

/-- `copy o a`: `[o] = [a]`. -/
theorem copy_ok {s : State} {B : Addr} {Z w N o a : Nat} (h : Ws s B Z w N)
    (ho : o < N) (ha : a < N) (hN : N ≤ 256) (hoa : o ≠ a) :
    WP isa (copy o a) s fun t => Ws t B Z w N ∧ KeyWorkspace.Keep B w [o] [] s.mem t.mem ∧
      num t.mem B w o = num s.mem B w a ∧ Keep opRegs s t ∧
      w32 t.mem B (arr w o + 4 * w) = w32 s.mem B (arr w o + 4 * w) := by
  have fo := h.arr_fit ho
  have fa := h.arr_fit ha
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wle
  have nw := h.nowrap
  rw [copy, WP.seq_iff]
  refine ptr_ok h (by decide) (by decide) (by decide) (show o < 2 ^ 15 by omega) ?_
  refine ptr_ok (h.of_keep (Keep.write _ _ _)) (by decide) (by decide) (by decide)
    (show a < 2 ^ 15 by omega) ?_
  let t : State := (s.write .r5 (off B (arr w o))).write .r6 (off B (arr w a))
  have kt : Keep [.r5, .r6] s t := (Keep.write _ _ _).trans (Keep.write _ _ _)
  have ht : Ws t B Z w N := h.of_keep kt
  have hb : WP isa (.block [.addi .r8 .r29 0]) t fun u =>
      (u.gpr .r5 = off B (arr w o) ∧ u.gpr .r6 = off B (arr w a) ∧ u.gpr .r8 = BitVec.ofNat 64 w ∧
        u.mem = t.mem) ∧ Keep [.r8] t u := by
    refine WP.keep _ ?_ (by decide)
    prun [t, h.r29, BitVec.add_zero]
  refine WP.mono hb fun u ⟨⟨u5, u6, u8, mu⟩, ku⟩ => ?_
  have k₁ : Keep opRegs s u := (kt.trans ku).mono
  have hu : Ws u B Z w N := h.of_keep k₁
  refine WP.mono (copyLoop_ok hu.scr u5 u6 u8 h.wpos (by omega) (by omega) (by omega)
    (ahead_of_ne hoa)) ?_
  intro t' ⟨v, out, kt'⟩
  have mt : t.mem = s.mem := rfl
  rw [mu, mt] at v out
  exact ⟨hu.of_keep kt', KeyWorkspace.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using out)
    (by omega) (by simp), v, k₁.trans' kt', out.w32 (by omega) (by omega)⟩

end VG.Proof.Rsa.PPC64LE.Keys
