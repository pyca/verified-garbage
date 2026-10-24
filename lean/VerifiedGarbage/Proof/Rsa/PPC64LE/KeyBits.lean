module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyOps
import VerifiedGarbage.Proof.Rsa.PPC64LE.Shifts
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontStep
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Rsa.PPC64LE.KeyWs
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Mont.Words32

/-!
# The operations on the slots and the low digits of the arrays

As on ARMv7 (`Proof/Rsa/Arm/KeyBits.lean`, `KeyWord.lean`): the blocks that
write a slot of the header (`bitOf`, `andS`, `stBorrow`) or the low digit of
an array (`setOne`, `orOne`, `clrLow`), as prefixes of a block, with a
continuation.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Keys

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Loops
open VG.Impl.Rsa.PPC64LE.Keys (ptr bitOf andS stBorrow setOne orOne clrLow)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot num_write0 num_mod2 num_mod32)

/-! ## Bit vectors -/

theorem and_one_arith (x : BitVec 32) :
    ((x.setWidth 64 &&& BitVec.ofNat 64 1).setWidth 32).toNat = x.toNat % 2 := by
  have := x.isLt
  rw [BitVec.toNat_setWidth, BitVec.toNat_and, toNat_ext32, BitVec.toNat_ofNat,
    show 1 % 2 ^ 64 = 1 by decide, Nat.and_one_is_mod]
  omega_arith

theorem and_arith (x y : BitVec 32) (hx : x.toNat ≤ 1) (hy : y.toNat ≤ 1) :
    ((x.setWidth 64 &&& y.setWidth 64).setWidth 32).toNat =
      if x.toNat = 1 ∧ y.toNat = 1 then 1 else 0 := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_and, toNat_ext32, toNat_ext32]
  rcases (show x.toNat = 0 ∨ x.toNat = 1 by omega_arith) with e | e <;>
    rcases (show y.toNat = 0 ∨ y.toNat = 1 by omega_arith) with f | f <;> rw [e, f] <;> decide

theorem or_one_arith (x : BitVec 32) :
    ((x.setWidth 64 ||| BitVec.ofNat 64 1).setWidth 32).toNat = 2 * (x.toNat / 2) + 1 := by
  have hx := x.isLt
  rw [BitVec.toNat_setWidth, BitVec.toNat_or, toNat_ext32, BitVec.toNat_ofNat,
    show 1 % 2 ^ 64 = 1 by decide]
  have hr : x.toNat % 2 < 2 ^ 1 := Nat.mod_lt _ (by decide)
  have r1 : x.toNat % 2 ||| 1 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one x.toNat with e | e <;> rw [e] <;> decide
  have e : x.toNat ||| 1 = 2 ^ 1 * (x.toNat / 2) + 1 := by
    conv => lhs; rw [show x.toNat = 2 ^ 1 * (x.toNat / 2) + x.toNat % 2 by omega_arith]
    rw [Nat.two_pow_add_eq_or_of_lt hr, Nat.or_assoc, r1,
      ← Nat.two_pow_add_eq_or_of_lt (show 1 < 2 ^ 1 by decide)]
  rw [e]
  omega_arith

theorem clr_arith (x : BitVec 32) :
    ((x.setWidth 64 >>> 1 <<< 1).setWidth 32).toNat = 2 * (x.toNat / 2) := by
  have hx := x.isLt
  rw [BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, toNat_ext32,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  omega_arith

/-! ## Slots -/

theorem slot_write_self (m : Mem) (B : Addr) (d : Nat) (v : BitVec 32) :
    slot (m.writeW (off B d) v) B d = v.toNat :=
  w32_write_self m B d v

theorem keep_slot {B : Addr} {w d : Nat} {js ds : List Nat} (m : Mem) (v : BitVec 32)
    (hd : d ∈ ds) (fit : d + 4 ≤ 2 ^ 64) : KeyWorkspace.Keep B w js ds m (m.writeW (off B d) v) :=
  KeyWorkspace.Keep.of_slot (writeW32_outside m B v fit) hd

/-- `stBorrow sl`: the slot `sl` := the borrow in `r9`. -/
theorem stBorrow_ok {s : State} {B : Addr} {Z w N sl : Nat} (h : Ws s B Z w N)
    (hsl : sl + 4 ≤ 160) (b9 : (s.gpr .r9).toNat ≤ 1) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Ws t B Z w N → KeyWorkspace.Keep B w [] [sl] s.mem t.mem →
      slot t.mem B sl = (s.gpr .r9).toNat → Keep opRegs s t → WP isa (.block rest) t Q) :
    WP isa (.block (stBorrow sl ++ rest)) s Q := by
  have hz : 160 ≤ Z := h.hdr_le
  have nw := h.nowrap
  rw [WP.block_append_iff]
  have hb : WP isa (.block (stBorrow sl)) s fun u =>
      u.mem = s.mem.writeW (off B sl) ((s.gpr .r9).setWidth 32) ∧ Keep opRegs s u := by
    refine WP.mono (WP.keep [] (Q := fun u => u.mem = s.mem.writeW (off B sl) ((s.gpr .r9).setWidth 32))
      ?_ (by rfl)) fun u ⟨m, k⟩ => ⟨m, k.mono (by simp)⟩
    prun [stBorrow, h.r31, h.scr.st (show sl + 4 ≤ Z by omega_arith),
      exec_store_w (show Reg.r31 ≠ .r0 by decide) (show sl < 2 ^ 15 by omega_arith)]
  refine WP.mono hb fun u ⟨mu, ku⟩ => k u (h.of_keep ku) (by rw [mu]; exact keep_slot _ _ (by simp) (by omega_arith))
    ?_ ku
  rw [mu, slot_write_self, BitVec.toNat_setWidth]
  omega_arith

/-- `andS d a b`: the slot `d` := the slots `a` and `b` and'ed. -/
theorem andS_ok {s : State} {B : Addr} {Z w N d a b : Nat} (h : Ws s B Z w N)
    (hd : d + 4 ≤ 160) (ha : a + 4 ≤ 160) (hb : b + 4 ≤ 160)
    (ba : slot s.mem B a ≤ 1) (bb : slot s.mem B b ≤ 1) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Ws t B Z w N → KeyWorkspace.Keep B w [] [d] s.mem t.mem →
      slot t.mem B d = (if slot s.mem B a = 1 ∧ slot s.mem B b = 1 then 1 else 0) →
      Keep opRegs s t → WP isa (.block rest) t Q) :
    WP isa (.block (andS d a b ++ rest)) s Q := by
  have hz : 160 ≤ Z := h.hdr_le
  have nw := h.nowrap
  rw [WP.block_append_iff]
  have hk : WP isa (.block (andS d a b)) s fun u =>
      (u.mem = s.mem.writeW (off B d) (((s.mem.readW (off B a) 32).setWidth 64 &&&
        (s.mem.readW (off B b) 32).setWidth 64).setWidth 32)) ∧ Keep opRegs s u := by
    refine WP.mono (WP.keep [.r0, .r3] ?_ (by rfl)) fun u ⟨m, k⟩ => ⟨m, k.mono⟩
    prun [andS, h.r31, h.scr.ld (show a + 4 ≤ Z by omega_arith), h.scr.ld (show b + 4 ≤ Z by omega_arith),
      h.scr.st (show d + 4 ≤ Z by omega_arith),
      exec_load_w (show Reg.r31 ≠ .r0 by decide) (show a < 2 ^ 15 by omega_arith),
      exec_load_w (show Reg.r31 ≠ .r0 by decide) (show b < 2 ^ 15 by omega_arith),
      exec_store_w (show Reg.r31 ≠ .r0 by decide) (show d < 2 ^ 15 by omega_arith)]
  refine WP.mono hk fun u ⟨mu, ku⟩ => k u (h.of_keep ku) (by rw [mu]; exact keep_slot _ _ (by simp) (by omega_arith))
    ?_ ku
  rw [mu, slot_write_self, and_arith _ _ ba bb]

/-- A block on the low digit of `[j]` (at `r5`) whose result's value is `f` of
the digit's. -/
theorem lowOp_ok {s : State} {B : Addr} {Z w N j : Nat} (h : Ws s B Z w N) (hj : j < N)
    (hN : N ≤ 256) {ops rest : List Instr} {Q : State → Prop} {f : BitVec 32 → BitVec 32}
    (hops : ∀ u : State, u.gpr .r5 = off B (arr w j) → u.mem = s.mem → Keep opRegs s u →
      WP isa (.block ops) u fun u' =>
        u'.mem = s.mem.writeW (off B (arr w j)) (f (s.mem.readW (off B (arr w j)) 32)) ∧ Keep opRegs u u')
    (k : ∀ t, Ws t B Z w N → KeyWorkspace.Keep B w [j] [] s.mem t.mem →
      num t.mem B w j = (f (s.mem.readW (off B (arr w j)) 32)).toNat + 2 ^ 32 * (num s.mem B w j / 2 ^ 32) →
      Keep opRegs s t → w32 t.mem B (arr w j + 4 * w) = w32 s.mem B (arr w j + 4 * w) →
      WP isa (.block rest) t Q) :
    WP isa (.block (ptr .r5 j ++ ops ++ rest)) s Q := by
  have fit := h.arr_fit hj
  have nw := h.nowrap
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wpos
  rw [List.append_assoc]
  refine ptr_ok h (by decide) (by decide) (by decide) (show j < 2 ^ 15 by omega_arith) ?_
  rw [WP.block_append_iff]
  have k₀ : Keep opRegs s (s.write .r5 (off B (arr w j))) := (Keep.write _ _ _).mono
  refine WP.mono (hops _ (by simp [gpr_write]) rfl k₀) fun u ⟨mu, ku⟩ => ?_
  have kt : Keep opRegs s u := k₀.trans' ku
  have o := writeW32_outside s.mem B (d := arr w j) (f (s.mem.readW (off B (arr w j)) 32)) (by omega_arith)
  have keep : KeyWorkspace.Keep B w [j] [] s.mem u.mem := by
    rw [mu]; exact KeyWorkspace.Keep.of_arr (d := 0) (by simpa using o) (by omega_arith) (by simp)
  refine k u (h.of_keep kt) keep ?_ kt ?_
  · rw [mu, num_write0 _ _ (by omega_arith) (by omega_arith)]
  · rw [mu]; exact o.w32 (by omega_arith) (by omega_arith)

/-- `setOne j`: the low digit of `[j]` := 1. -/
theorem setOne_ok {s : State} {B : Addr} {Z w N j : Nat} (h : Ws s B Z w N) (hj : j < N)
    (hN : N ≤ 256) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Ws t B Z w N → KeyWorkspace.Keep B w [j] [] s.mem t.mem →
      num t.mem B w j = 1 + 2 ^ 32 * (num s.mem B w j / 2 ^ 32) → Keep opRegs s t →
      WP isa (.block rest) t Q) :
    WP isa (.block (setOne j ++ rest)) s Q := by
  have fit := h.arr_fit hj
  have nw := h.nowrap
  have hS : S w = 4 * (w + 2) := rfl
  refine lowOp_ok (f := fun _ => 1) h hj hN (fun u u5 um ku => ?_) fun t ht kt v kr _ => k t ht kt v kr
  refine WP.mono (WP.keep [.r0] ?_ (by decide)) fun u' ⟨m, k⟩ => ⟨m, k.mono⟩
  prun [u5, um, (h.scr.congr ku.wr).st (show arr w j + 4 ≤ Z by omega_arith)]
  rfl

/-- `orOne j`: the low bit of `[j]` set. -/
theorem orOne_ok {s : State} {B : Addr} {Z w N j : Nat} (h : Ws s B Z w N) (hj : j < N)
    (hN : N ≤ 256) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Ws t B Z w N → KeyWorkspace.Keep B w [j] [] s.mem t.mem →
      num t.mem B w j = 2 * (num s.mem B w j / 2) + 1 → Keep opRegs s t → WP isa (.block rest) t Q) :
    WP isa (.block (orOne j ++ rest)) s Q := by
  have fit := h.arr_fit hj
  have nw := h.nowrap
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wpos
  refine lowOp_ok (f := fun x => (x.setWidth 64 ||| BitVec.ofNat 64 1).setWidth 32) h hj hN
    (fun u u5 um ku => ?_) fun t ht kt v kr _ => k t ht kt ?_ kr
  · refine WP.mono (WP.keep [.r0, .r3] ?_ (by decide)) fun u' ⟨m, k⟩ => ⟨m, k.mono⟩
    prun [u5, um, (h.scr.congr ku.wr).ld (show arr w j + 4 ≤ Z by omega_arith),
      (h.scr.congr ku.wr).st (show arr w j + 4 ≤ Z by omega_arith)]
  · rw [v, or_one_arith]
    have e := num_mod32 s.mem B (w := w) (j := j) (by omega_arith)
    change _ = (s.mem.readW (off B (arr w j)) 32).toNat at e
    rw [← e]
    omega_arith

/-- `clrLow j`: the low bit of `[j]` cleared. -/
theorem clrLow_ok {s : State} {B : Addr} {Z w N j : Nat} (h : Ws s B Z w N) (hj : j < N)
    (hN : N ≤ 256) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Ws t B Z w N → KeyWorkspace.Keep B w [j] [] s.mem t.mem →
      num t.mem B w j = 2 * (num s.mem B w j / 2) → Keep opRegs s t →
      w32 t.mem B (arr w j + 4 * w) = w32 s.mem B (arr w j + 4 * w) → WP isa (.block rest) t Q) :
    WP isa (.block (clrLow j ++ rest)) s Q := by
  have fit := h.arr_fit hj
  have nw := h.nowrap
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wpos
  refine lowOp_ok (f := fun x => (x.setWidth 64 >>> 1 <<< 1).setWidth 32) h hj hN
    (fun u u5 um ku => ?_) fun t ht kt v kr ktop => k t ht kt ?_ kr ktop
  · refine WP.mono (WP.keep [.r0] ?_ (by decide)) fun u' ⟨m, k⟩ => ⟨m, k.mono⟩
    prun [u5, um, (h.scr.congr ku.wr).ld (show arr w j + 4 ≤ Z by omega_arith),
      (h.scr.congr ku.wr).st (show arr w j + 4 ≤ Z by omega_arith)]
  · rw [v, clr_arith]
    have e := num_mod32 s.mem B (w := w) (j := j) (by omega_arith)
    change _ = (s.mem.readW (off B (arr w j)) 32).toNat at e
    rw [← e]
    omega_arith

/-- `bitOf sl j`: the slot `sl` := the low bit of `[j]`. -/
theorem bitOf_ok {s : State} {B : Addr} {Z w N j sl : Nat} (h : Ws s B Z w N)
    (hj : j < N) (hN : N ≤ 256) (hsl : sl + 4 ≤ 160) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Ws t B Z w N → KeyWorkspace.Keep B w [] [sl] s.mem t.mem →
      slot t.mem B sl = num s.mem B w j % 2 → Keep opRegs s t → WP isa (.block rest) t Q) :
    WP isa (.block (bitOf sl j ++ rest)) s Q := by
  have fit := h.arr_fit hj
  have nw := h.nowrap
  have hS : S w = 4 * (w + 2) := rfl
  have hz : 160 ≤ Z := h.hdr_le
  have := h.wpos
  unfold bitOf
  rw [List.append_assoc]
  refine ptr_ok h (by decide) (by decide) (by decide) (show j < 2 ^ 15 by omega_arith) ?_
  rw [WP.block_append_iff]
  have k₀ : Keep opRegs s (s.write .r5 (off B (arr w j))) := (Keep.write _ _ _).mono
  have hk : WP isa (.block [.load .w .r0 .r5 0, .li .r3 1, .logic .and .r0 .r0 .r3, .store .w .r0 .r31 sl])
      (s.write .r5 (off B (arr w j))) fun u =>
        (u.mem = s.mem.writeW (off B sl) (((s.mem.readW (off B (arr w j)) 32).setWidth 64 &&&
          BitVec.ofNat 64 1).setWidth 32)) ∧ Keep [.r0, .r3] (s.write .r5 (off B (arr w j))) u := by
    refine WP.keep _ ?_ (by rfl)
    prun [h.r31, h.scr.ld (show arr w j + 4 ≤ Z by omega_arith), h.scr.st (show sl + 4 ≤ Z by omega_arith),
      exec_store_w (show Reg.r31 ≠ .r0 by decide) (show sl < 2 ^ 15 by omega_arith)]
  refine WP.mono hk fun u ⟨mu, ku⟩ => ?_
  have kt : Keep opRegs s u := k₀.trans' ku.mono
  refine k u (h.of_keep kt) (by rw [mu]; exact keep_slot _ _ (by simp) (by omega_arith)) ?_ kt
  rw [mu, slot_write_self, and_one_arith, num_mod2 _ _ (by omega_arith)]

end VG.Proof.Rsa.PPC64LE.Keys
