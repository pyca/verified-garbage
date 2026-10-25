module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyWs
public import VerifiedGarbage.Proof.Rsa.PPC64LE.Loops
import VerifiedGarbage.Proof.Rsa.PPC64LE.EvenW
import VerifiedGarbage.Proof.Rsa.PPC64LE.WordLoops
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFios
import VerifiedGarbage.Proof.Framework.PPC64LE.Carry
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontStep
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The operations on the arrays of the working space: subtraction, selection, copy

As on ARMv7 (`Proof/Rsa/Arm/KeyOps.lean`): `sub3_ok`, `sel_ok` and
`copy_ok`, on arrays apart from each other, each keeping the working space
(`Ws`), the memory but the array it writes (`KeyWorkspace.Keep`), and the
registers but `opRegs`; `sub3_gen_ok` and `sel_gen_ok` also for an output
that is an operand. For an even `w` they run over words (`WordLoops.lean`),
for an odd one over digits (`Loops.lean`).
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Keys

open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Loops
open VG.Impl.Rsa.PPC64LE.Keys (ptr sub3 sel copy subBody selBody copyBody subWBody selWBody copyWBody countLoop)
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
  unfold Ahead; omega_arith

/-- The pointers of three arrays into `r5`–`r7`, the rest of a block after them. -/
theorem ptr3_ok' {s : State} {B : Addr} {Z w N : Nat} (h : Ws s B Z w N) {o a b : Nat}
    (ho : o < 2 ^ 15) (ha : a < 2 ^ 15) (hb : b < 2 ^ 15) {c : Prog isa} {Q : State → Prop}
    (k : ∀ t, t.gpr .r5 = off B (arr w o) → t.gpr .r6 = off B (arr w a) → t.gpr .r7 = off B (arr w b) →
      Keep [.r5, .r6, .r7] s t → t.mem = s.mem → WP isa c t Q) :
    WP isa (.seq (.block (ptr .r5 o ++ ptr .r6 a ++ ptr .r7 b)) c) s Q := by
  rw [WP.seq_iff, ← List.append_nil (ptr .r5 o ++ ptr .r6 a ++ ptr .r7 b)]
  exact ptr3_ok h ho ha hb fun t p5 p6 p7 kt mt => WP.block_nil (k t p5 p6 p7 kt mt)

/-- `[o] := [a] - [b]` for `o` ahead of `a` and `b` (apart from them, or one
of them), the borrow out in `r9`. -/
theorem sub3_gen_ok {s : State} {B : Addr} {Z w N o a b : Nat} (h : Ws s B Z w N)
    (ho : o < N) (ha : a < N) (hb : b < N) (hN : N ≤ 256) (aA : Ahead (arr w o) (arr w a) w)
    (aB : Ahead (arr w o) (arr w b) w) :
    WP isa (sub3 o a b) s fun t => Ws t B Z w N ∧ KeyWorkspace.Keep B w [o] [] s.mem t.mem ∧
      num t.mem B w o + num s.mem B w b = num s.mem B w a + 2 ^ (32 * w) * (t.gpr .r9).toNat ∧
      (t.gpr .r9).toNat ≤ 1 ∧ Keep opRegs s t := by
  have fo := h.arr_fit ho
  have fa := h.arr_fit ha
  have fb := h.arr_fit hb
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wle
  have := h.wpos
  rw [sub3]
  refine ptr3_ok' h (by omega_arith) (by omega_arith) (by omega_arith) fun t p5 p6 p7 kt mt => ?_
  have ht : Ws t B Z w N := h.of_keep kt
  refine evenW_ok ht (fun hev u mu ku => ?_) (fun hodd u mu ku => ?_)
  · -- Words, the borrow in the carry bit.
    have u5 : u.gpr .r5 = off B (arr w o) := by rw [ku.gpr _ (by decide)]; exact p5
    have u6 : u.gpr .r6 = off B (arr w a) := by rw [ku.gpr _ (by decide)]; exact p6
    have u7 : u.gpr .r7 = off B (arr w b) := by rw [ku.gpr _ (by decide)]; exact p7
    have hu : Ws u B Z w N := ht.of_keep ku
    rw [WP.seq_iff]
    refine WP.mono (WP.keep [.r0, .r8] (Q := fun x => x.gpr .r5 = off B (arr w o) ∧ x.gpr .r6 = off B (arr w a) ∧
      x.gpr .r7 = off B (arr w b) ∧ x.gpr .r8 = BitVec.ofNat 64 (w / 2) ∧
      x.ca = decide (2 ^ 64 ≤ (BitVec.ofNat 64 (w / 2)).toNat + (2 ^ 64 - 1 - (BitVec.ofNat 64 (w / 2)).toNat) + 1) ∧
      x.mem = u.mem) ?_ (by decide)) fun v ⟨⟨v5, v6, v7, v8, vc, vm⟩, kv⟩ => ?_
    · mcrun [u5, u6, u7, hu.r29, lsr1_ofNat (show w < 2 ^ 64 by omega_arith)]
    have vc' : v.ca = true := by
      rw [vc]; exact decide_eq_true (by have := (BitVec.ofNat 64 (w / 2)).isLt; omega_arith)
    have hv : Ws v B Z w N := hu.of_keep kv
    rw [WP.seq_iff]
    refine WP.mono (subWLoop_ok hv.scr v5 v6 v7 v8 (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
      (aheadW hev aA) (aheadW hev aB)) fun t' ⟨veq, out, kt', _⟩ => ?_
    have ht' : Ws t' B Z w N := hv.of_keep kt'
    refine WP.mono (WP.keep [.r0, .r9] (Q := fun x => x.gpr .r9 = BitVec.ofNat 64 (t'.ca.toNat) ^^^ 1#64 ∧
      x.mem = t'.mem) ?_ (by decide)) fun x ⟨⟨x9, xm⟩, kx⟩ => ?_
    · mcrun [exec_adde]
      apply BitVec.eq_of_toNat_eq; simp
    have b9 : (x.gpr .r9).toNat = 1 - t'.ca.toNat := by
      rw [x9]; cases t'.ca <;> rfl
    rw [vc', vm, mu, mt] at veq
    rw [vm, mu, mt] at out
    refine ⟨ht'.of_keep kx, ?_, ?_, by rw [b9]; omega_arith, ?_⟩
    · rw [xm]
      exact KeyWorkspace.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero, show 8 * (w / 2) = 4 * w by omega_arith]
        using out) (by omega_arith) (by simp)
    · rw [xm, num_words _ _ hev, num_words _ _ hev, num_words _ _ hev, b9,
        show 32 * w = 64 * (w / 2) by omega_arith]
      simpa using veq
    · exact Keep.mono (rs' := opRegs) ((((kt.trans ku).trans kv).trans kt').trans kx) (by decide)
  · -- Digits, the borrow in `r9`.
    have hb' : WP isa (.block [.addi .r8 .r29 0, .li .r9 0]) u fun v =>
        (v.gpr .r5 = off B (arr w o) ∧ v.gpr .r6 = off B (arr w a) ∧ v.gpr .r7 = off B (arr w b) ∧
          v.gpr .r8 = BitVec.ofNat 64 w ∧ v.gpr .r9 = 0 ∧ v.mem = u.mem) ∧ Keep [.r8, .r9] u v := by
      refine WP.keep _ ?_ (by decide)
      prun [ku.gpr (r := .r5) (by decide), ku.gpr (r := .r6) (by decide), ku.gpr (r := .r7) (by decide), p5, p6,
        p7, (ht.of_keep ku).r29, BitVec.add_zero]
      rfl
    rw [WP.seq_iff]
    refine WP.mono hb' fun v ⟨⟨v5, v6, v7, v8, v9, vm⟩, kv⟩ => ?_
    have k₁ : Keep opRegs s v := ((kt.trans ku).trans kv).mono (by decide)
    have hv : Ws v B Z w N := h.of_keep k₁
    refine WP.mono (subLoop_ok hv.scr v5 v6 v7 v8 (by rw [v9]; decide) h.wpos (by omega_arith) (by omega_arith)
      (by omega_arith) (by omega_arith) aA aB) ?_
    intro t' ⟨b9, veq, out, kt'⟩
    rw [v9, vm, mu, mt] at veq
    rw [vm, mu, mt] at out
    exact ⟨hv.of_keep kt', KeyWorkspace.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using out)
      (by omega_arith) (by simp), by simpa using veq, b9, k₁.trans' kt'⟩

/-- `sub3 o a b`: `[o] := [a] - [b]` for arrays apart, the borrow out in `r9`. -/
theorem sub3_ok {s : State} {B : Addr} {Z w N o a b : Nat} (h : Ws s B Z w N)
    (ho : o < N) (ha : a < N) (hb : b < N) (hN : N ≤ 256) (hoa : o ≠ a) (hob : o ≠ b) :
    WP isa (sub3 o a b) s fun t => Ws t B Z w N ∧ KeyWorkspace.Keep B w [o] [] s.mem t.mem ∧
      num t.mem B w o + num s.mem B w b = num s.mem B w a + 2 ^ (32 * w) * (t.gpr .r9).toNat ∧
      (t.gpr .r9).toNat ≤ 1 ∧ Keep opRegs s t :=
  sub3_gen_ok h ho ha hb hN (ahead_of_ne hoa) (ahead_of_ne hob)

/-- The mask of a slot holding 0 or 1. -/
theorem mask_of_slot (x : BitVec 32) (h : x.toNat ≤ 1) :
    x.setWidth 64 = BitVec.ofNat 64 (if x.toNat = 0 then 0 else 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_ext32]
  split <;> simp only [BitVec.toNat_ofNat] <;> omega_arith

/-- `sel o a b sl` for `o` ahead of `a` and `b`: `[o] = [b]` if the slot `sl` is 1, `[a]` if it is 0. -/
theorem sel_gen_ok {s : State} {B : Addr} {Z w N o a b sl : Nat} (h : Ws s B Z w N)
    (ho : o < N) (ha : a < N) (hb : b < N) (hN : N ≤ 256) (aA : Ahead (arr w o) (arr w a) w)
    (aB : Ahead (arr w o) (arr w b) w) (hsl : sl + 4 ≤ KeyWorkspace.hdr) (bit : slot s.mem B sl ≤ 1) :
    WP isa (sel o a b sl) s fun t => Ws t B Z w N ∧ KeyWorkspace.Keep B w [o] [] s.mem t.mem ∧
      num t.mem B w o = (if slot s.mem B sl = 0 then num s.mem B w a else num s.mem B w b) ∧
      Keep opRegs s t := by
  have fo := h.arr_fit ho
  have fa := h.arr_fit ha
  have fb := h.arr_fit hb
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wle
  have := h.wpos
  have hz : 160 ≤ Z := h.hdr_le
  have hsl' : sl + 4 ≤ 160 := hsl
  rw [sel, WP.seq_iff]
  refine ptr3_ok h (by omega_arith) (by omega_arith) (by omega_arith) fun t p5 p6 p7 kt mt => ?_
  have ht : Ws t B Z w N := h.of_keep kt
  have hb : WP isa (.block [.load .w .r9 .r31 sl, .li .r0 0, .sub .r9 .r0 .r9]) t
      fun u => (u.gpr .r5 = off B (arr w o) ∧ u.gpr .r6 = off B (arr w a) ∧ u.gpr .r7 = off B (arr w b) ∧
        u.gpr .r9 = BitVec.ofNat 64 0 - (t.mem.readW (off B sl) 32).setWidth 64 ∧ u.mem = t.mem) ∧
        Keep [.r0, .r9] t u := by
    refine WP.keep _ ?_ (by rfl)
    prun [p5, p6, p7, ht.r31, ht.scr.ld (show sl + 4 ≤ Z by omega_arith),
      exec_load_w (show Reg.r31 ≠ .r0 by decide) (show sl < 2 ^ 15 by omega_arith)]
  refine WP.mono hb fun u ⟨⟨u5, u6, u7, u9, mu⟩, ku⟩ => ?_
  have k₁ : Keep opRegs s u := (kt.trans ku).mono (by decide)
  have hu : Ws u B Z w N := h.of_keep k₁
  rw [mt, mask_of_slot _ bit] at u9
  have h9 : u.gpr .r9 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if decide (slot s.mem B sl ≠ 0) then 1 else 0) := by
    rw [u9]; by_cases h0 : slot s.mem B sl = 0 <;> simp [h0]
  have post : ∀ x : Nat, x = (if decide (slot s.mem B sl ≠ 0) then num s.mem B w b else num s.mem B w a) →
      x = (if slot s.mem B sl = 0 then num s.mem B w a else num s.mem B w b) := fun x e => by
    rw [e]; by_cases h0 : slot s.mem B sl = 0 <;> simp [h0]
  refine evenW_ok hu (fun hev v mv kv => ?_) (fun hodd v mv kv => ?_)
  · have v5 : v.gpr .r5 = off B (arr w o) := by rw [kv.gpr _ (by decide)]; exact u5
    have v6 : v.gpr .r6 = off B (arr w a) := by rw [kv.gpr _ (by decide)]; exact u6
    have v7 : v.gpr .r7 = off B (arr w b) := by rw [kv.gpr _ (by decide)]; exact u7
    have v9 : v.gpr .r9 = u.gpr .r9 := kv.gpr _ (by decide)
    have hv : Ws v B Z w N := hu.of_keep kv
    rw [WP.seq_iff]
    refine WP.mono (WP.keep [.r8] (Q := fun x => x.gpr .r5 = off B (arr w o) ∧ x.gpr .r6 = off B (arr w a) ∧
      x.gpr .r7 = off B (arr w b) ∧ x.gpr .r8 = BitVec.ofNat 64 (w / 2) ∧ x.gpr .r9 = v.gpr .r9 ∧ x.mem = v.mem)
      (by prun [v5, v6, v7, hv.r29, lsr1_ofNat (show w < 2 ^ 64 by omega_arith)]) (by decide))
      fun x ⟨⟨x5, x6, x7, x8, x9, xm⟩, kx⟩ => ?_
    have hx : Ws x B Z w N := hv.of_keep kx
    refine WP.mono (selWLoop_ok (b := decide (slot s.mem B sl ≠ 0)) hx.scr x5 x6 x7 x8 (by rw [x9, v9, h9])
      (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (aheadW hev aA) (aheadW hev aB)) ?_
    intro t' ⟨veq, out, kt', _⟩
    rw [xm, mv, mu, mt] at veq out
    refine ⟨hx.of_keep kt', KeyWorkspace.Keep.of_arr (d := 0)
      (by simpa only [Nat.add_zero, show 8 * (w / 2) = 4 * w by omega_arith] using out) (by omega_arith) (by simp), ?_,
      Keep.mono (rs' := opRegs) (((k₁.trans kv).trans kx).trans kt') (by decide)⟩
    apply post
    rw [num_words _ _ hev, veq, num_words _ _ hev, num_words _ _ hev]
  · have hb' : WP isa (.block [.addi .r8 .r29 0]) v fun x =>
        (x.gpr .r5 = off B (arr w o) ∧ x.gpr .r6 = off B (arr w a) ∧ x.gpr .r7 = off B (arr w b) ∧
          x.gpr .r8 = BitVec.ofNat 64 w ∧ x.gpr .r9 = u.gpr .r9 ∧ x.mem = v.mem) ∧ Keep [.r8] v x := by
      refine WP.keep _ ?_ (by decide)
      prun [kv.gpr (r := .r5) (by decide), kv.gpr (r := .r6) (by decide), kv.gpr (r := .r7) (by decide),
        kv.gpr (r := .r9) (by decide), u5, u6, u7, (hu.of_keep kv).r29, BitVec.add_zero]
    rw [WP.seq_iff]
    refine WP.mono hb' fun x ⟨⟨x5, x6, x7, x8, x9, xm⟩, kx⟩ => ?_
    have k₂ : Keep opRegs s x := ((k₁.trans kv).trans kx).mono (by decide)
    have hx : Ws x B Z w N := h.of_keep k₂
    refine WP.mono (selLoop_ok (b := decide (slot s.mem B sl ≠ 0)) hx.scr x5 x6 x7 x8 (by rw [x9, h9])
      h.wpos (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) aA aB) ?_
    intro t' ⟨veq, out, kt'⟩
    rw [xm, mv, mu, mt] at veq out
    exact ⟨hx.of_keep kt', KeyWorkspace.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using out)
      (by omega_arith) (by simp), post _ veq, k₂.trans' kt'.mono⟩

/-- `sel o a b sl`: `[o] = [b]` if the slot `sl` is 1, `[a]` if it is 0. -/
theorem sel_ok {s : State} {B : Addr} {Z w N o a b sl : Nat} (h : Ws s B Z w N)
    (ho : o < N) (ha : a < N) (hb : b < N) (hN : N ≤ 256) (hoa : o ≠ a) (hob : o ≠ b)
    (hsl : sl + 4 ≤ KeyWorkspace.hdr) (bit : slot s.mem B sl ≤ 1) :
    WP isa (sel o a b sl) s fun t => Ws t B Z w N ∧ KeyWorkspace.Keep B w [o] [] s.mem t.mem ∧
      num t.mem B w o = (if slot s.mem B sl = 0 then num s.mem B w a else num s.mem B w b) ∧
      Keep opRegs s t :=
  sel_gen_ok h ho ha hb hN (ahead_of_ne hoa) (ahead_of_ne hob) hsl bit

/-- `sel o o b sl`: `[o] := [b]` if the slot `sl` is 1, kept if it is 0. -/
theorem sel_self_ok {s : State} {B : Addr} {Z w N o b sl : Nat} (h : Ws s B Z w N)
    (ho : o < N) (hb : b < N) (hN : N ≤ 256) (hob : o ≠ b)
    (hsl : sl + 4 ≤ KeyWorkspace.hdr) (bit : slot s.mem B sl ≤ 1) :
    WP isa (sel o o b sl) s fun t => Ws t B Z w N ∧ KeyWorkspace.Keep B w [o] [] s.mem t.mem ∧
      num t.mem B w o = (if slot s.mem B sl = 0 then num s.mem B w o else num s.mem B w b) ∧
      Keep opRegs s t :=
  sel_gen_ok h ho ho hb hN (.inl (Nat.le_refl _)) (ahead_of_ne hob) hsl bit

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
  have := h.wpos
  have nw := h.nowrap
  rw [copy, WP.seq_iff, ← List.append_nil (ptr .r5 o ++ ptr .r6 a), List.append_assoc]
  refine ptr_ok h (by decide) (by decide) (by decide) (show o < 2 ^ 15 by omega_arith) ?_
  refine ptr_ok (h.of_keep (Keep.write _ _ _)) (by decide) (by decide) (by decide)
    (show a < 2 ^ 15 by omega_arith) (WP.block_nil ?_)
  let t : State := (s.write .r5 (off B (arr w o))).write .r6 (off B (arr w a))
  have kt : Keep [.r5, .r6] s t := (Keep.write _ _ _).trans (Keep.write _ _ _)
  have ht : Ws t B Z w N := h.of_keep kt
  have t5 : t.gpr .r5 = off B (arr w o) := rfl
  have t6 : t.gpr .r6 = off B (arr w a) := rfl
  have post : ∀ t' : State, Outside B (arr w o) (4 * w) s.mem t'.mem → Ws t' B Z w N →
      num t'.mem B w o = num s.mem B w a → Keep opRegs s t' →
      Ws t' B Z w N ∧ KeyWorkspace.Keep B w [o] [] s.mem t'.mem ∧
        num t'.mem B w o = num s.mem B w a ∧ Keep opRegs s t' ∧
        w32 t'.mem B (arr w o + 4 * w) = w32 s.mem B (arr w o + 4 * w) := fun t' out hw v k =>
    ⟨hw, KeyWorkspace.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using out) (by omega_arith) (by simp), v, k,
      out.w32 (by omega_arith) (by omega_arith)⟩
  refine evenW_ok ht (fun hev u mu ku => ?_) (fun hodd u mu ku => ?_)
  · have hu := ht.of_keep ku
    rw [WP.seq_iff]
    refine WP.mono (WP.keep [.r8] (Q := fun x => x.gpr .r5 = off B (arr w o) ∧ x.gpr .r6 = off B (arr w a) ∧
      x.gpr .r8 = BitVec.ofNat 64 (w / 2) ∧ x.mem = u.mem)
      (by prun [ku.gpr (r := .r5) (by decide), ku.gpr (r := .r6) (by decide), t5, t6, hu.r29,
        lsr1_ofNat (show w < 2 ^ 64 by omega_arith)]) (by decide)) fun x ⟨⟨x5, x6, x8, xm⟩, kx⟩ => ?_
    have hx := hu.of_keep kx
    refine WP.mono (copyWLoop_ok hx.scr x5 x6 x8 (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
      (aheadW hev (ahead_of_ne hoa))) fun t' ⟨v, out, kt'⟩ => ?_
    have mt : t.mem = s.mem := rfl
    rw [xm, mu, mt] at v out
    exact post t' (by simpa only [show 8 * (w / 2) = 4 * w by omega_arith] using out) (hx.of_keep kt')
      (by rw [num_words _ _ hev, num_words _ _ hev, v])
      (Keep.mono (rs' := opRegs) (((kt.trans ku).trans kx).trans kt') (by decide))
  · have hu := ht.of_keep ku
    rw [WP.seq_iff]
    refine WP.mono (WP.keep [.r8] (Q := fun x => x.gpr .r5 = off B (arr w o) ∧ x.gpr .r6 = off B (arr w a) ∧
      x.gpr .r8 = BitVec.ofNat 64 w ∧ x.mem = u.mem)
      (by prun [ku.gpr (r := .r5) (by decide), ku.gpr (r := .r6) (by decide), t5, t6, hu.r29, BitVec.add_zero])
      (by decide)) fun x ⟨⟨x5, x6, x8, xm⟩, kx⟩ => ?_
    have hx := hu.of_keep kx
    refine WP.mono (copyLoop_ok hx.scr x5 x6 x8 h.wpos (by omega_arith) (by omega_arith) (by omega_arith)
      (ahead_of_ne hoa)) fun t' ⟨v, out, kt'⟩ => ?_
    have mt : t.mem = s.mem := rfl
    rw [xm, mu, mt] at v out
    exact post t' out (hx.of_keep kt') v (Keep.mono (rs' := opRegs) (((kt.trans ku).trans kx).trans kt') (by decide))

end VG.Proof.Rsa.PPC64LE.Keys
