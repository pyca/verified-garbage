module

public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.Ops
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyBits
import VerifiedGarbage.Proof.Rsa.PPC64LE.Loops
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontStep
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_keygen_key` on PPC64LE: the operations beyond the key routines'

`notS_ok`, `andNotS_ok` and `selS_ok` (the flag slots), `setDigit_ok` (a
digit of an array), and `sub3_self_ok` and `sel_self_ok`, the key routines'
subtraction and selection into their first operand, which their loops allow
(each digit is read before it is written).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Key

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Loops
open VG.Proof.Rsa VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (ptr sub3 sel subBody selBody countLoop)
open VG.Impl.RsaKeyGen.PPC64LE.Key (notS andNotS selS setDigit)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

/-! ## Flags -/

theorem not_arith (x : BitVec 32) (hx : x.toNat ≤ 1) :
    ((x.setWidth 64 ^^^ BitVec.ofNat 64 1).setWidth 32).toNat = 1 - x.toNat := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_xor, toNat_ext32]
  rcases (show x.toNat = 0 ∨ x.toNat = 1 by omega) with e | e <;> rw [e] <;> decide

theorem andNot_arith (x y : BitVec 32) (hx : x.toNat ≤ 1) (hy : y.toNat ≤ 1) :
    (((x.setWidth 64 ^^^ BitVec.ofNat 64 1) &&& y.setWidth 64).setWidth 32).toNat =
      if x.toNat = 0 ∧ y.toNat = 1 then 1 else 0 := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_xor, toNat_ext32, toNat_ext32]
  rcases (show x.toNat = 0 ∨ x.toNat = 1 by omega) with e | e <;>
    rcases (show y.toNat = 0 ∨ y.toNat = 1 by omega) with f | f <;> rw [e, f] <;> decide

theorem selS_arith (x y z : BitVec 32) (hx : x.toNat ≤ 1) (hy : y.toNat ≤ 1) (hz : z.toNat ≤ 1) :
    ((x.setWidth 64 ^^^ ((y.setWidth 64 ^^^ x.setWidth 64) &&& z.setWidth 64)).setWidth 32).toNat =
      if z.toNat = 1 then y.toNat else x.toNat := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_xor, BitVec.toNat_and, BitVec.toNat_xor, toNat_ext32,
    toNat_ext32, toNat_ext32]
  rcases (show x.toNat = 0 ∨ x.toNat = 1 by omega) with e | e <;>
    rcases (show y.toNat = 0 ∨ y.toNat = 1 by omega) with f | f <;>
    rcases (show z.toNat = 0 ∨ z.toNat = 1 by omega) with g | g <;> rw [e, f, g] <;> decide

/-- `notS d a`: the slot `d` := `1 - a`. -/
theorem notS_ok {s : State} {B : Addr} {Z w N d a : Nat} (h : Ws s B Z w N)
    (hd : d + 4 ≤ 160) (ha : a + 4 ≤ 160) (ba : slot s.mem B a ≤ 1) {rest : List Instr}
    {Q : State → Prop}
    (k : ∀ t, Ws t B Z w N → KeyWorkspace.Keep B w [] [d] s.mem t.mem →
      slot t.mem B d = 1 - slot s.mem B a → Keep opRegs s t → WP isa (.block rest) t Q) :
    WP isa (.block (notS d a ++ rest)) s Q := by
  have hz : 160 ≤ Z := h.hdr_le
  have nw := h.nowrap
  rw [WP.block_append_iff]
  have hk : WP isa (.block (notS d a)) s fun u =>
      (u.mem = s.mem.writeW (off B d) (((s.mem.readW (off B a) 32).setWidth 64 ^^^
        BitVec.ofNat 64 1).setWidth 32)) ∧ Keep opRegs s u := by
    refine WP.mono (WP.keep [.r0, .r3] ?_ (by rfl)) fun u ⟨m, k⟩ => ⟨m, k.mono⟩
    prun [notS, h.r31, h.scr.ld (show a + 4 ≤ Z by omega), h.scr.st (show d + 4 ≤ Z by omega),
      exec_load_w (show Reg.r31 ≠ .r0 by decide) (show a < 2 ^ 15 by omega),
      exec_store_w (show Reg.r31 ≠ .r0 by decide) (show d < 2 ^ 15 by omega)]
  refine WP.mono hk fun u ⟨mu, ku⟩ => k u (h.of_keep ku) (by rw [mu]; exact keep_slot _ _ (by simp) (by omega))
    ?_ ku
  rw [mu, slot_write_self, not_arith _ ba]

/-- `andNotS d a b`: the slot `d` := `(1 - a) b`. -/
theorem andNotS_ok {s : State} {B : Addr} {Z w N d a b : Nat} (h : Ws s B Z w N)
    (hd : d + 4 ≤ 160) (ha : a + 4 ≤ 160) (hb : b + 4 ≤ 160)
    (ba : slot s.mem B a ≤ 1) (bb : slot s.mem B b ≤ 1) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Ws t B Z w N → KeyWorkspace.Keep B w [] [d] s.mem t.mem →
      slot t.mem B d = (if slot s.mem B a = 0 ∧ slot s.mem B b = 1 then 1 else 0) →
      Keep opRegs s t → WP isa (.block rest) t Q) :
    WP isa (.block (andNotS d a b ++ rest)) s Q := by
  have hz : 160 ≤ Z := h.hdr_le
  have nw := h.nowrap
  rw [WP.block_append_iff]
  have hk : WP isa (.block (andNotS d a b)) s fun u =>
      (u.mem = s.mem.writeW (off B d) ((((s.mem.readW (off B a) 32).setWidth 64 ^^^ BitVec.ofNat 64 1) &&&
        (s.mem.readW (off B b) 32).setWidth 64).setWidth 32)) ∧ Keep opRegs s u := by
    refine WP.mono (WP.keep [.r0, .r3] ?_ (by rfl)) fun u ⟨m, k⟩ => ⟨m, k.mono⟩
    prun [andNotS, h.r31, h.scr.ld (show a + 4 ≤ Z by omega), h.scr.ld (show b + 4 ≤ Z by omega),
      h.scr.st (show d + 4 ≤ Z by omega),
      exec_load_w (show Reg.r31 ≠ .r0 by decide) (show a < 2 ^ 15 by omega),
      exec_load_w (show Reg.r31 ≠ .r0 by decide) (show b < 2 ^ 15 by omega),
      exec_store_w (show Reg.r31 ≠ .r0 by decide) (show d < 2 ^ 15 by omega)]
  refine WP.mono hk fun u ⟨mu, ku⟩ => k u (h.of_keep ku) (by rw [mu]; exact keep_slot _ _ (by simp) (by omega))
    ?_ ku
  rw [mu, slot_write_self, andNot_arith _ _ ba bb]

/-- `selS d a b c`: the slot `d` := `b` if `c` is 1, `a` if it is 0. -/
theorem selS_ok {s : State} {B : Addr} {Z w N d a b c : Nat} (h : Ws s B Z w N)
    (hd : d + 4 ≤ 160) (ha : a + 4 ≤ 160) (hb : b + 4 ≤ 160) (hc : c + 4 ≤ 160)
    (ba : slot s.mem B a ≤ 1) (bb : slot s.mem B b ≤ 1) (bc : slot s.mem B c ≤ 1) {rest : List Instr}
    {Q : State → Prop}
    (k : ∀ t, Ws t B Z w N → KeyWorkspace.Keep B w [] [d] s.mem t.mem →
      slot t.mem B d = (if slot s.mem B c = 1 then slot s.mem B b else slot s.mem B a) →
      Keep opRegs s t → WP isa (.block rest) t Q) :
    WP isa (.block (selS d a b c ++ rest)) s Q := by
  have hz : 160 ≤ Z := h.hdr_le
  have nw := h.nowrap
  rw [WP.block_append_iff]
  have hk : WP isa (.block (selS d a b c)) s fun u =>
      (u.mem = s.mem.writeW (off B d) (((s.mem.readW (off B a) 32).setWidth 64 ^^^
        (((s.mem.readW (off B b) 32).setWidth 64 ^^^ (s.mem.readW (off B a) 32).setWidth 64) &&&
          (s.mem.readW (off B c) 32).setWidth 64)).setWidth 32)) ∧ Keep opRegs s u := by
    refine WP.mono (WP.keep [.r0, .r3, .r9] ?_ (by rfl)) fun u ⟨m, k⟩ => ⟨m, k.mono⟩
    prun [selS, h.r31, h.scr.ld (show a + 4 ≤ Z by omega), h.scr.ld (show b + 4 ≤ Z by omega),
      h.scr.ld (show c + 4 ≤ Z by omega), h.scr.st (show d + 4 ≤ Z by omega),
      exec_load_w (show Reg.r31 ≠ .r0 by decide) (show a < 2 ^ 15 by omega),
      exec_load_w (show Reg.r31 ≠ .r0 by decide) (show b < 2 ^ 15 by omega),
      exec_load_w (show Reg.r31 ≠ .r0 by decide) (show c < 2 ^ 15 by omega),
      exec_store_w (show Reg.r31 ≠ .r0 by decide) (show d < 2 ^ 15 by omega)]
  refine WP.mono hk fun u ⟨mu, ku⟩ => k u (h.of_keep ku) (by rw [mu]; exact keep_slot _ _ (by simp) (by omega))
    ?_ ku
  rw [mu, slot_write_self, selS_arith _ _ _ ba bb bc]

/-! ## A digit of an array -/

/-- A number is its digits below `k`, digit `k` and the digits above. -/
theorem val32_split (m : Mem) (B : Addr) (d : Nat) {k n : Nat} (hk : k < n) :
    val32 m B d n = val32 m B d k + 2 ^ (32 * k) * w32 m B (d + 4 * k) +
      2 ^ (32 * (k + 1)) * val32 m B (d + 4 * k + 4) (n - k - 1) := by
  have e1 := val32_append m B d k (n - k)
  rw [show k + (n - k) = n by omega] at e1
  rw [e1]
  obtain ⟨j, hj⟩ : ∃ j, n - k = j + 1 := ⟨n - k - 1, by omega⟩
  rw [hj, val32, pow32_succ, Nat.add_sub_cancel, Nat.mul_add, ← Nat.mul_assoc (2 ^ (32 * k)) (2 ^ 32),
    Nat.mul_comm (2 ^ (32 * k)) (2 ^ 32)]
  omega

/-- `setDigit j x`: the digit of `[j]` at the byte offset `4 k` in `r6` := `x`. -/
theorem setDigit_ok {s : State} {B : Addr} {Z w N j x k : Nat} (h : Ws s B Z w N) (hj : j < N)
    (hN : N ≤ 256) (hx : x < 2 ^ 15) (hk : k < w) (h6 : s.gpr .r6 = BitVec.ofNat 64 (4 * k))
    {rest : List Instr} {Q : State → Prop}
    (kk : ∀ t, Ws t B Z w N → KeyWorkspace.Keep B w [j] [] s.mem t.mem →
      num t.mem B w j + 2 ^ (32 * k) * w32 s.mem B (arr w j + 4 * k) =
        num s.mem B w j + 2 ^ (32 * k) * x → Keep [.r0, .r5] s t →
      w32 t.mem B (arr w j + 4 * w) = w32 s.mem B (arr w j + 4 * w) → WP isa (.block rest) t Q) :
    WP isa (.block (setDigit j x ++ rest)) s Q := by
  have fit := h.arr_fit hj
  have nw := h.nowrap
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wle
  unfold setDigit
  rw [List.append_assoc]
  refine ptr_ok h (by decide) (by decide) (by decide) (show j < 2 ^ 15 by omega) ?_
  rw [WP.block_append_iff]
  have k₀ : Keep [.r5] s (s.write .r5 (off B (arr w j))) := Keep.write _ _ _
  have e5 : off B (arr w j) + BitVec.ofNat 64 (4 * k) + BitVec.ofNat 64 0 = off B (arr w j + 4 * k) := by
    rw [BitVec.add_zero, off_add]
  have hk' : WP isa (.block [.add .r5 .r5 .r6, .li .r0 x, .store .w .r0 .r5 0])
      (s.write .r5 (off B (arr w j))) fun u =>
        (u.mem = s.mem.writeW (off B (arr w j + 4 * k)) ((BitVec.ofNat 64 x).setWidth 32)) ∧
          Keep [.r0, .r5] (s.write .r5 (off B (arr w j))) u := by
    refine WP.keep _ ?_ (by rfl)
    prun [h6, e5, exec_li hx, h.scr.st (show arr w j + 4 * k + 4 ≤ Z by omega)]
  refine WP.mono hk' fun u ⟨mu, ku⟩ => ?_
  have kt : Keep [.r0, .r5] s u := (k₀.trans ku).mono
  have o := writeW32_outside s.mem B (d := arr w j + 4 * k) ((BitVec.ofNat 64 x).setWidth 32) (by omega)
  refine kk u (h.of_keep kt) ?_ ?_ kt ?_
  · rw [mu]; exact KeyWorkspace.Keep.of_arr (d := 4 * k) o (by omega) (by simp)
  · have hv : ((BitVec.ofNat 64 x).setWidth 32).toNat = x := by
      rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
    have lo := o.val32 (d := arr w j) (k := k) (by omega) (by omega)
    have hi := o.val32 (d := arr w j + 4 * k + 4) (k := w - k - 1) (by omega) (by omega)
    simp only [num]
    rw [val32_split _ _ _ hk, val32_split s.mem _ _ hk, mu, lo, hi, w32_write_self, hv]
    grind
  · rw [mu]; exact o.w32 (by omega) (by omega)

/-! ## Into the first operand -/

/-- `sub3 o o b`: `[o] := [o] - [b]`, the borrow in `r9`. -/
theorem sub3_self_ok {s : State} {B : Addr} {Z w N o b : Nat} (h : Ws s B Z w N)
    (ho : o < N) (hb : b < N) (hN : N ≤ 256) (hob : o ≠ b) :
    WP isa (sub3 o o b) s fun t => Ws t B Z w N ∧ KeyWorkspace.Keep B w [o] [] s.mem t.mem ∧
      num t.mem B w o + num s.mem B w b = num s.mem B w o + 2 ^ (32 * w) * (t.gpr .r9).toNat ∧
      (t.gpr .r9).toNat ≤ 1 ∧ Keep opRegs s t := by
  have fo := h.arr_fit ho
  have fb := h.arr_fit hb
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wle
  rw [sub3, WP.seq_iff]
  refine ptr3_ok h (by omega) (by omega) (by omega) fun t p5 p6 p7 kt mt => ?_
  have ht : Ws t B Z w N := h.of_keep kt
  have hb' : WP isa (.block [.addi .r8 .r29 0, .li .r9 0]) t fun u =>
      (u.gpr .r5 = off B (arr w o) ∧ u.gpr .r6 = off B (arr w o) ∧ u.gpr .r7 = off B (arr w b) ∧
        u.gpr .r8 = BitVec.ofNat 64 w ∧ u.gpr .r9 = 0 ∧ u.mem = t.mem) ∧ Keep [.r8, .r9] t u := by
    refine WP.keep _ ?_ (by decide)
    prun [p5, p6, p7, ht.r29, BitVec.add_zero]
    rfl
  refine WP.mono hb' fun u ⟨⟨u5, u6, u7, u8, u9, mu⟩, ku⟩ => ?_
  have k₁ : Keep opRegs s u := (kt.trans ku).mono
  have hu : Ws u B Z w N := h.of_keep k₁
  refine WP.mono (subLoop_ok hu.scr u5 u6 u7 u8 (by rw [u9]; decide) h.wpos (by omega) (by omega)
    (by omega) (by omega) (.inl (Nat.le_refl _)) (ahead_of_ne hob)) ?_
  intro t' ⟨b9, v, out, kt'⟩
  rw [u9, mu, mt] at v
  rw [mu, mt] at out
  exact ⟨hu.of_keep kt', KeyWorkspace.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using out)
    (by omega) (by simp), by simpa using v, b9, k₁.trans' kt'⟩

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
  have hb' : WP isa (.block [.addi .r8 .r29 0, .load .w .r9 .r31 sl, .li .r0 0, .sub .r9 .r0 .r9]) t
      fun u => (u.gpr .r5 = off B (arr w o) ∧ u.gpr .r6 = off B (arr w o) ∧ u.gpr .r7 = off B (arr w b) ∧
        u.gpr .r8 = BitVec.ofNat 64 w ∧
        u.gpr .r9 = BitVec.ofNat 64 0 - (t.mem.readW (off B sl) 32).setWidth 64 ∧ u.mem = t.mem) ∧
        Keep [.r0, .r8, .r9] t u := by
    refine WP.keep _ ?_ (by rfl)
    prun [p5, p6, p7, ht.r29, ht.r31, BitVec.add_zero, ht.scr.ld (show sl + 4 ≤ Z by omega),
      exec_load_w (show Reg.r31 ≠ .r0 by decide) (show sl < 2 ^ 15 by omega)]
  refine WP.mono hb' fun u ⟨⟨u5, u6, u7, u8, u9, mu⟩, ku⟩ => ?_
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

end VG.Proof.RsaKeyGen.PPC64LE.Key
