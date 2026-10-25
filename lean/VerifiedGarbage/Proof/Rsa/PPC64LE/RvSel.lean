module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyOps
import VerifiedGarbage.Proof.Framework.Block

/-!
# A selection into one of its operands

`sel_self_ok`: `sel o o b sl`, which `sel_ok` leaves out (its operands are
apart from its output), keeps `[o]` or replaces it by `[b]`: the loop reads
each digit of `[o]` before it writes it.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Keys

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Loops
open VG.Impl.Rsa.PPC64LE.Keys (ptr sel selBody countLoop)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

/-- `sel o o b sl`: `[o] := [b]` if the slot `sl` is 1, kept if it is 0. -/
theorem sel_self_ok {s : State} {B : Addr} {Z w N o b sl : Nat} (h : Ws s B Z w N)
    (ho : o < N) (hb : b < N) (hN : N ≤ 256) (hob : o ≠ b)
    (hsl : sl + 4 ≤ KeyWorkspace.hdr) (bit : slot s.mem B sl ≤ 1) :
    WP isa (sel o o b sl) s fun t => Ws t B Z w N ∧ KeyWorkspace.Keep B w [o] [] s.mem t.mem ∧
      num t.mem B w o = (if slot s.mem B sl = 0 then num s.mem B w o else num s.mem B w b) ∧
      Keep opRegs s t := by
  have fo := h.arr_fit ho
  have fb := h.arr_fit hb
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wle
  have hz : 160 ≤ Z := h.hdr_le
  have hsl' : sl + 4 ≤ 160 := hsl
  rw [sel, WP.seq_iff]
  refine ptr3_ok h (by omega) (by omega) (by omega) fun t p5 p6 p7 kt mt => ?_
  have ht : Ws t B Z w N := h.of_keep kt
  have hb : WP isa (.block [.addi .r8 .r29 0, .load .w .r9 .r31 sl, .li .r0 0, .sub .r9 .r0 .r9]) t
      fun u => (u.gpr .r5 = off B (arr w o) ∧ u.gpr .r6 = off B (arr w o) ∧ u.gpr .r7 = off B (arr w b) ∧
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
    (by omega) (by omega) (.inl (Nat.le_refl _)) (ahead_of_ne hob)) ?_
  intro t' ⟨v, out, kt'⟩
  rw [mu, mt] at v out
  refine ⟨hu.of_keep kt', KeyWorkspace.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using out)
    (by omega) (by simp), ?_, k₁.trans' (kt'.mono)⟩
  change val32 _ _ _ _ = _
  rw [v]
  by_cases h0 : slot s.mem B sl = 0 <;> simp [h0]

end VG.Proof.Rsa.PPC64LE.Keys
