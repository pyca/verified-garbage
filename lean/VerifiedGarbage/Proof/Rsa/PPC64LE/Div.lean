module

public import VerifiedGarbage.Impl.Rsa.PPC64LE.Div
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyBits
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontStep
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rsa.PPC64LE.Shifts
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyOps

/-!
# The division of the RSA key operations on PPC64LE: the parts of a step

`shift_ok`: the quotient (`w` digits) and the remainder (`w + 1`) shifted
left together, the quotient's top bit into the remainder; `subtract_ok`:
`[t] := [r] - [d]` over `w + 1` digits; `keep_ok`: `[r] := mask ? [t] : [r]`;
`setBit_ok`: the new bit into the quotient's low digit.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Keys

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Loops
open VG.Impl.Rsa.PPC64LE.Keys (ptr countLoop subBody selBody)
open VG.Impl.Rsa.PPC64LE.Div (shift subtract keep setBit shlBody)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot arr_disj)

/-- The `w + 1` digits of array `j`. -/
abbrev num1 (m : Mem) (B : Addr) (w j : Nat) : Nat := val32 m B (arr w j) (w + 1)

/-- The pointer of an array into `r5` and the count `w + c` into `r8`, for
the loops of the division. -/
theorem ptrCount_ok {s : State} {B : Addr} {Z w N j c : Nat} (h : Ws s B Z w N) (hj : j < N)
    (hN : N ≤ 256) (hc : c ≤ 1) {extra : List Instr} {Q : State → Prop}
    (hx : extra = [.addi .r8 .r29 c] ∨ extra = [.addi .r8 .r29 c, .li .r9 0])
    (k : ∀ u, u.gpr .r5 = off B (arr w j) → u.gpr .r8 = BitVec.ofNat 64 (w + c) →
      (extra.length = 2 → u.gpr .r9 = 0) → (extra.length = 1 → u.gpr .r9 = s.gpr .r9) →
      u.mem = s.mem → Keep [.r5, .r8, .r9] s u → Q u) :
    WP isa (.block (ptr .r5 j ++ extra)) s Q := by
  have := h.wle
  refine ptr_ok h (by decide) (by decide) (by decide) (show j < 2 ^ 15 by omega_arith) ?_
  have h1 : Ws (s.write .r5 (off B (arr w j))) B Z w N := h.of_keep (Keep.write _ _ _)
  rcases hx with rfl | rfl
  · refine WP.mono (WP.keep [.r8] (Q := fun u => u.gpr .r5 = off B (arr w j) ∧
      u.gpr .r8 = BitVec.ofNat 64 (w + c) ∧ u.gpr .r9 = s.gpr .r9 ∧ u.mem = s.mem) ?_ (by rfl))
      fun u ⟨⟨u5, u8, u9, um⟩, ku⟩ => k u u5 u8 (by simp) (fun _ => u9) um
        (((Keep.write _ _ _).trans ku).mono)
    prun [h.r29, exec_addi (show Reg.r29 ≠ .r0 by decide) (show c < 2 ^ 15 by omega_arith),
      BitVec.ofNat_add]
  · refine WP.mono (WP.keep [.r8, .r9] (Q := fun u => u.gpr .r5 = off B (arr w j) ∧
      u.gpr .r8 = BitVec.ofNat 64 (w + c) ∧ u.gpr .r9 = 0 ∧ u.mem = s.mem) ?_ (by rfl))
      fun u ⟨⟨u5, u8, u9, um⟩, ku⟩ => k u u5 u8 (fun _ => u9) (by simp) um
        (((Keep.write _ _ _).trans ku).mono)
    prun [h.r29, exec_addi (show Reg.r29 ≠ .r0 by decide) (show c < 2 ^ 15 by omega_arith),
      BitVec.ofNat_add]
    rfl

/-- `shift q r`: `[q]' + 2^(32 w) c = 2 [q]` and `[r]' + 2^(32 (w + 1)) c' = 2 [r] + c`, `[r]` of
`w + 1` digits. -/
theorem shift_ok {s : State} {B : Addr} {Z w N q r : Nat} (h : Ws s B Z w N)
    (hq : q < N) (hr : r < N) (hN : N ≤ 256) (hqr : q ≠ r) :
    WP isa (shift q r) s fun t => Ws t B Z w N ∧ KeyWorkspace.Keep B w [q, r] [] s.mem t.mem ∧
      (∃ c ≤ 1, num t.mem B w q + 2 ^ (32 * w) * c = 2 * num s.mem B w q ∧
        ∃ c' ≤ 1, num1 t.mem B w r + 2 ^ (32 * (w + 1)) * c' = 2 * num1 s.mem B w r + c) ∧
      Keep opRegs s t := by
  have fq := h.arr_fit hq
  have fr := h.arr_fit hr
  have nw := h.nowrap
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wpos
  have := h.wle
  rw [shift, WP.seq_iff]
  refine ptrCount_ok (c := 0) h hq hN (by decide) (.inr rfl) fun u u5 u8 u9 _ um ku => ?_
  have hu : Ws u B Z w N := h.of_keep ku
  rw [WP.seq_iff]
  refine WP.mono (shlLoop_ok hu.scr u5 u8 (by rw [u9 rfl]; decide) (by omega_arith) (by omega_arith)
    (by omega_arith)) fun v ⟨c9, vq, vout, kv⟩ => ?_
  have hv : Ws v B Z w N := hu.of_keep kv
  rw [WP.seq_iff]
  refine ptrCount_ok (c := 1) hv hr hN (by decide) (.inl rfl) fun x x5 x8 _ x9 xm kx => ?_
  have hx : Ws x B Z w N := hv.of_keep kx
  refine WP.mono (shlLoop_ok hx.scr x5 x8 (by rw [x9 rfl]; exact c9) (by omega_arith) (by omega_arith)
    (by omega_arith)) fun y ⟨c9', vr, yout, ky⟩ => ?_
  have k₁ : KeyWorkspace.Keep B w [q, r] [] s.mem v.mem := by
    rw [← um]; exact KeyWorkspace.Keep.of_arr (d := 0) (by simpa using vout) (by omega_arith) (by simp)
  have k₂ : KeyWorkspace.Keep B w [q, r] [] v.mem y.mem := by
    rw [← xm]; exact KeyWorkspace.Keep.of_arr (d := 0) (by simpa using yout) (by omega_arith) (by simp)
  have rq : num y.mem B w q = num v.mem B w q := by
    rw [← xm]; exact yout.val32 (by have := arr_disj (w := w) hqr; omega_arith) (by omega_arith)
  have rr : val32 v.mem B (arr w r) (w + 1) = val32 s.mem B (arr w r) (w + 1) := by
    rw [← um]; exact vout.val32 (by have := arr_disj (w := w) hqr; omega_arith) (by omega_arith)
  refine ⟨hx.of_keep ky, k₁.trans k₂, ⟨_, c9, ?_, _, c9', ?_⟩, ((ku.trans kv).trans (kx.trans ky)).mono⟩
  · rw [rq]; rw [u9 rfl, um] at vq; simpa using vq
  · rw [xm, x9 rfl, rr] at vr; exact vr

/-- Two distinct arrays, over `w + 1` digits, are each ahead of the other. -/
theorem ahead1_of_ne {w o a : Nat} (h : o ≠ a) : Ahead (arr w o) (arr w a) (w + 1) := by
  have := arr_disj (w := w) h
  simp only [S] at this
  unfold Ahead; omega_arith

/-- `subtract r d t`: `[t] + [d] = [r] + 2^(32 (w + 1)) β`, over `w + 1` digits. -/
theorem subtract_ok {s : State} {B : Addr} {Z w N r d t : Nat} (h : Ws s B Z w N)
    (hr : r < N) (hd : d < N) (ht : t < N) (hN : N ≤ 256) (htr : t ≠ r) (htd : t ≠ d) :
    WP isa (subtract r d t) s fun u => Ws u B Z w N ∧ KeyWorkspace.Keep B w [t] [] s.mem u.mem ∧
      num1 u.mem B w t + num1 s.mem B w d = num1 s.mem B w r + 2 ^ (32 * (w + 1)) * (u.gpr .r9).toNat ∧
      (u.gpr .r9).toNat ≤ 1 ∧ Keep opRegs s u := by
  have fr := h.arr_fit hr
  have fd := h.arr_fit hd
  have ft := h.arr_fit ht
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wle
  rw [subtract, WP.seq_iff]
  refine ptr3_ok h (by omega_arith) (by omega_arith) (by omega_arith) fun x p5 p6 p7 kx mx => ?_
  have hb : WP isa (.block [.addi .r8 .r29 1, .li .r9 0]) x fun u =>
      (u.gpr .r5 = off B (arr w t) ∧ u.gpr .r6 = off B (arr w r) ∧ u.gpr .r7 = off B (arr w d) ∧
        u.gpr .r8 = BitVec.ofNat 64 (w + 1) ∧ u.gpr .r9 = 0 ∧ u.mem = x.mem) ∧ Keep [.r8, .r9] x u := by
    refine WP.keep _ ?_ (by decide)
    prun [p5, p6, p7, (h.of_keep kx).r29, BitVec.ofNat_add]
    rfl
  refine WP.mono hb fun u ⟨⟨u5, u6, u7, u8, u9, mu⟩, ku⟩ => ?_
  have k₁ : Keep opRegs s u := (kx.trans ku).mono
  have hu : Ws u B Z w N := h.of_keep k₁
  refine WP.mono (subLoop_ok hu.scr u5 u6 u7 u8 (by rw [u9]; decide) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (ahead1_of_ne htr) (ahead1_of_ne htd)) ?_
  intro v ⟨b9, vv, out, kv⟩
  rw [u9, mu, mx] at vv
  rw [mu, mx] at out
  exact ⟨hu.of_keep kv, KeyWorkspace.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using out)
    (by omega_arith) (by simp), by simpa using vv, b9, k₁.trans' kv⟩

/-- `keep r t`: `[r] := b ? [t] : [r]` over `w + 1` digits, the mask of `b` in `r9`. -/
theorem keep_ok {s : State} {B : Addr} {Z w N r t : Nat} (h : Ws s B Z w N)
    (hr : r < N) (ht : t < N) (hN : N ≤ 256) (hrt : r ≠ t) {b : Bool}
    (h9 : s.gpr .r9 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0)) :
    WP isa (keep r t) s fun u => Ws u B Z w N ∧ KeyWorkspace.Keep B w [r] [] s.mem u.mem ∧
      num1 u.mem B w r = (if b then num1 s.mem B w t else num1 s.mem B w r) ∧
      Keep [.r0, .r3, .r5, .r6, .r7, .r8] s u := by
  have fr := h.arr_fit hr
  have ft := h.arr_fit ht
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wle
  rw [keep, WP.seq_iff]
  refine ptr3_ok h (by omega_arith) (by omega_arith) (by omega_arith) fun x p5 p6 p7 kx mx => ?_
  have hb : WP isa (.block [.addi .r8 .r29 1]) x fun u =>
      (u.gpr .r5 = off B (arr w r) ∧ u.gpr .r6 = off B (arr w r) ∧ u.gpr .r7 = off B (arr w t) ∧
        u.gpr .r8 = BitVec.ofNat 64 (w + 1) ∧ u.gpr .r9 = x.gpr .r9 ∧ u.mem = x.mem) ∧ Keep [.r8] x u := by
    refine WP.keep _ ?_ (by decide)
    prun [p5, p6, p7, (h.of_keep kx).r29, BitVec.ofNat_add]
  refine WP.mono hb fun u ⟨⟨u5, u6, u7, u8, u9, mu⟩, ku⟩ => ?_
  have k₁ : Keep [.r5, .r6, .r7, .r8] s u := (kx.trans ku).mono
  have hu : Ws u B Z w N := h.of_keep k₁
  have e9 : u.gpr .r9 = s.gpr .r9 := u9.trans (kx.gpr _ (by decide))
  refine WP.mono (selLoop_ok hu.scr u5 u6 u7 u8 (by rw [e9, h9]) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (Or.inl (Nat.le_refl _)) (ahead1_of_ne hrt)) ?_
  intro v ⟨vv, out, kv⟩
  rw [mu, mx] at vv out
  exact ⟨hu.of_keep kv, KeyWorkspace.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using out)
    (by omega_arith) (by simp), vv, (k₁.trans kv).mono⟩

/-- The quotient bit and the mask: from the borrow `β` in `r9`, `r10 = 1 - β` and
`r9` the mask of `β = 0`. -/
theorem bit_ok {s : State} (b9 : (s.gpr .r9).toNat ≤ 1) :
    WP isa (.block VG.Impl.Rsa.PPC64LE.Div.bit) s fun u =>
      (u.gpr .r10 = BitVec.ofNat 64 (if (s.gpr .r9).toNat = 0 then 1 else 0) ∧
        u.gpr .r9 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if (s.gpr .r9).toNat = 0 then 1 else 0) ∧
        u.mem = s.mem) ∧ Keep [.r0, .r9, .r10] s u := by
  have e : BitVec.ofNat 64 1 ^^^ s.gpr .r9 = BitVec.ofNat 64 (if (s.gpr .r9).toNat = 0 then 1 else 0) := by
    rcases (show (s.gpr .r9).toNat = 0 ∨ (s.gpr .r9).toNat = 1 by omega_arith) with z | z
    · have : s.gpr .r9 = 0 := BitVec.eq_of_toNat_eq z
      rw [this]; rfl
    · have : s.gpr .r9 = 1 := BitVec.eq_of_toNat_eq z
      rw [this]; rfl
  refine WP.keep _ ?_ (by decide)
  prun [VG.Impl.Rsa.PPC64LE.Div.bit, e]

/-- An even digit or'ed with a bit is their sum. -/
theorem or_bit_arith (x : BitVec 32) (c : BitVec 64) (hx : x.toNat % 2 = 0) (hc : c.toNat ≤ 1) :
    ((x.setWidth 64 ||| c).setWidth 32).toNat = x.toNat + c.toNat := by
  have h := x.isLt
  rw [BitVec.toNat_setWidth, BitVec.toNat_or, toNat_ext32,
    show x.toNat = 2 ^ 1 * (x.toNat / 2) by omega_arith,
    ← Nat.two_pow_add_eq_or_of_lt (show c.toNat < 2 ^ 1 by omega_arith)]
  omega_arith

/-- `setBit q`: the bit in `r10` added to the even `[q]`, and `r4` decremented. -/
theorem setBit_ok {s : State} {B : Addr} {Z w N q : Nat} (h : Ws s B Z w N) (hq : q < N)
    (hN : N ≤ 256) (even : num s.mem B w q % 2 = 0) (b10 : (s.gpr .r10).toNat ≤ 1) :
    WP isa (.block (setBit q)) s fun u => Ws u B Z w N ∧ KeyWorkspace.Keep B w [q] [] s.mem u.mem ∧
      num u.mem B w q = num s.mem B w q + (s.gpr .r10).toNat ∧
      u.gpr .r4 = s.gpr .r4 - BitVec.ofNat 64 1 ∧ Keep [.r0, .r4, .r5] s u := by
  have fit := h.arr_fit hq
  have nw := h.nowrap
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wpos
  have := h.wle
  unfold setBit
  refine ptr_ok h (by decide) (by decide) (by decide) (show q < 2 ^ 15 by omega_arith) ?_
  have hb : WP isa (.block [.load .w .r0 .r5 0, .logic .or .r0 .r0 .r10, .store .w .r0 .r5 0,
      .subi .r4 .r4 1]) (s.write .r5 (off B (arr w q))) fun u =>
        (u.mem = s.mem.writeW (off B (arr w q))
          (((s.mem.readW (off B (arr w q)) 32).setWidth 64 ||| s.gpr .r10).setWidth 32) ∧
          u.gpr .r4 = s.gpr .r4 - BitVec.ofNat 64 1) ∧ Keep [.r0, .r4] (s.write .r5 (off B (arr w q))) u := by
    refine WP.keep _ ?_ (by decide)
    prun [h.scr.ld (show arr w q + 4 ≤ Z by omega_arith), h.scr.st (show arr w q + 4 ≤ Z by omega_arith)]
  refine WP.mono hb fun u ⟨⟨mu, u4⟩, ku⟩ => ?_
  have kt : Keep [.r0, .r4, .r5] s u := ((Keep.write _ _ _).trans ku).mono
  have o := writeW32_outside s.mem B (d := arr w q)
    (((s.mem.readW (off B (arr w q)) 32).setWidth 64 ||| s.gpr .r10).setWidth 32) (by omega_arith)
  have e0 := VG.Proof.Rsa.KeyWorkspace.num_mod2 s.mem B (w := w) (j := q) (by omega_arith)
  have e32 := VG.Proof.Rsa.KeyWorkspace.num_mod32 s.mem B (w := w) (j := q) (by omega_arith)
  change _ = (s.mem.readW (off B (arr w q)) 32).toNat % 2 at e0
  change _ = (s.mem.readW (off B (arr w q)) 32).toNat at e32
  refine ⟨h.of_keep kt, ?_, ?_, u4, kt⟩
  · rw [mu]; exact KeyWorkspace.Keep.of_arr (d := 0) (by simpa using o) (by omega_arith) (by simp)
  · rw [mu, VG.Proof.Rsa.KeyWorkspace.num_write0 _ _ (by omega_arith) (by omega_arith),
      or_bit_arith _ _ (by omega_arith) b10]
    have := Nat.mod_add_div (num s.mem B w q) (2 ^ 32)
    omega_arith

end VG.Proof.Rsa.PPC64LE.Keys
