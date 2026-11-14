module

public import VerifiedGarbage.Impl.Rsa.PPC64LE.MontKey
public import VerifiedGarbage.Proof.Rsa.PPC64LE.IbOps
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyOps
import VerifiedGarbage.Proof.Rsa.MontCheckMath
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRound
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMinv
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Block

/-!
# Products for the RSA key checks on PPC64LE: correct

`mulLo_ok`: `mulLo o x y len` leaves `[o] = [x] [y] mod 2^(32 w)`, over the
`⌈len / 4⌉` low digits of `[x]`, by `mulLo_row` (`Proof/Rsa/MontCheckMath.lean`)
over the rows. `montMul_ok`: `montMul` leaves `[a] < 2^(32 K)`, and, for
`[y] < [m]`, `[a] < [m]` with `[a] 2^(32 c) ≡ [x] [y] (mod [m])`, by
`mont_step` over the steps.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.MontKey

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Proof.Rsa.PPC64LE.Loops (Ahead loopRegs)
open VG.Proof.Rsa.PPC64LE.InvBatch (macLoop_ok keep_val keep_word)
open VG.Impl.Rsa.PPC64LE.Keys (ptr seqs countLoop copyBody subBody selBody)
open VG.Impl.Rsa.PPC64LE.InvBatch (macBody)
open VG.Impl.Rsa.PPC64LE.MontKey
open VG.Proof.Bignum.PPC64LE (Pub.minv_ok)
open VG.Proof.Rsa.KeyWorkspace (arr S num arr_disj)

/-- The registers the products change. -/
abbrev mkRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12]

theorem off_shift (B : Addr) (o x i : Nat) :
    off B o + (off B (x + 4 * i) - off B x) = off B (o + 4 * i) := by
  apply BitVec.eq_of_toNat_eq
  simp only [off, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega_using []

/-! ## `mulLo` -/

/-- The state between the rows: `i` rows done. -/
structure LoInv (s t : State) (B : Addr) (Z w N o x y c : Nat) (i : Nat) : Prop where
  ws : Ws t B Z w N
  r4 : t.gpr .r4 = BitVec.ofNat 64 (c - i)
  r10 : t.gpr .r10 = off B (arr w x + 4 * i)
  r12 : t.gpr .r12 = BitVec.ofNat 64 (w - i)
  keep : KeyWorkspace.Keep B w [o] [] s.mem t.mem
  val : num t.mem B w o = val32 s.mem B (arr w x) i * num s.mem B w y % 2 ^ (32 * w)
  regs : Keep mkRegs s t

theorem row_ok {s t : State} {B : Addr} {Z w N o x y c i : Nat} (hN : N ≤ 256) (ho : o < N) (hx : x < N)
    (hy : y < N) (hox : o ≠ x) (hoy : o ≠ y) (hi : i < c) (hcw : c ≤ w) (h : LoInv s t B Z w N o x y c i) :
    WP isa (mulLoRow o x y) t fun t' => LoInv s t' B Z w N o x y c (i + 1) ∧
      t'.gpr .r4 = t.gpr .r4 - BitVec.ofNat 64 1 := by
  have hw := h.ws
  have fo := hw.arr_fit ho
  have fx := hw.arr_fit hx
  have fy := hw.arr_fit hy
  have hS : S w = 4 * (w + 2) := rfl
  have := hw.wle
  have hnw := hw.nowrap
  have dox := arr_disj (w := w) hox
  have doy := arr_disj (w := w) hoy
  -- The setup: `x_i`, the pointers and the count.
  have xi : w32 t.mem B (arr w x + 4 * i) = w32 s.mem B (arr w x + 4 * i) := by
    have := keep_word (b := 32) (o := 4 * i) h.keep (j := x) (by simp only [S]; omega_using [hi, hcw])
      (by simp only [List.mem_singleton]; exact fun _ e => e ▸ hox) (by simp) (hw.fit64 hx)
    exact congrArg BitVec.toNat this
  rw [mulLoRow, WP.seq_iff]
  have hb1 : WP isa (.block ([.load .w .r11 .r10 0] ++ ptr .r5 o ++ ptr .r6 x ++
      ([.sub .r6 .r10 .r6, .add .r5 .r5 .r6, .addi .r6 .r5 0] : List Instr) ++ ptr .r7 y ++
      ([.addi .r8 .r12 0, .li .r9 0] : List Instr))) t fun u =>
      u.gpr .r5 = off B (arr w o + 4 * i) ∧ u.gpr .r6 = off B (arr w o + 4 * i) ∧
      u.gpr .r7 = off B (arr w y) ∧ u.gpr .r8 = BitVec.ofNat 64 (w - i) ∧ u.gpr .r9 = 0 ∧
      (u.gpr .r11).toNat = w32 s.mem B (arr w x + 4 * i) ∧ u.mem = t.mem ∧
      Keep [.r5, .r6, .r7, .r8, .r9, .r11] t u := by
    rw [show ([.load .w .r11 .r10 0] : List Instr) ++ ptr .r5 o ++ ptr .r6 x ++
        ([.sub .r6 .r10 .r6, .add .r5 .r5 .r6, .addi .r6 .r5 0] : List Instr) ++ ptr .r7 y ++
        ([.addi .r8 .r12 0, .li .r9 0] : List Instr) = [.load .w .r11 .r10 0] ++ (ptr .r5 o ++ (ptr .r6 x ++
        (([.sub .r6 .r10 .r6, .add .r5 .r5 .r6, .addi .r6 .r5 0] : List Instr) ++ (ptr .r7 y ++
        ([.addi .r8 .r12 0, .li .r9 0] : List Instr))))) by simp only [List.append_assoc]]
    rw [WP.block_append_iff]
    refine WP.mono (WP.keep [.r11] (Q := fun u => (u.gpr .r11).toNat = w32 s.mem B (arr w x + 4 * i) ∧
      u.mem = t.mem) (by
        prun [h.r10, BitVec.add_zero, hw.scr.ld (show arr w x + 4 * i + 4 ≤ Z by omega_using [hi, hcw, fx, hS])]
        rw [BitVec.toNat_setWidth, ← xi]; exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide))) (by decide))
      fun u1 ⟨⟨a11, am⟩, k1⟩ => ?_
    have h1 := hw.of_keep k1
    refine ptr_ok h1 (r := .r5) (by decide) (by decide) (by decide) (show o < 2 ^ 15 by omega_using [hN, ho]) ?_
    refine ptr_ok (h1.of_keep (Keep.write _ _ _)) (r := .r6) (by decide) (by decide) (by decide)
      (show x < 2 ^ 15 by omega_using [hN, hx]) ?_
    rw [WP.block_append_iff]
    have u10 : u1.gpr .r10 = off B (arr w x + 4 * i) := (k1.gpr _ (by decide)).trans h.r10
    refine WP.mono (WP.keep [.r5, .r6] (Q := fun u => u.gpr .r5 = off B (arr w o + 4 * i) ∧
      u.gpr .r6 = off B (arr w o + 4 * i) ∧ u.mem = u1.mem) (by
        prun [gpr_write, mem_write, u10, BitVec.add_zero]
        rw [off_shift]) (by decide)) fun u2 ⟨⟨b5, b6, bm⟩, k2⟩ => ?_
    have h2 := (h1.of_keep ((Keep.write _ .r5 _).trans (Keep.write _ .r6 _))).of_keep k2
    refine ptr_ok h2 (r := .r7) (by decide) (by decide) (by decide) (show y < 2 ^ 15 by omega_using [hN, hy]) ?_
    have u12 : u2.gpr .r12 = t.gpr .r12 := (k2.gpr _ (by decide)).trans (by
      simp only [gpr_write]; exact k1.gpr _ (by decide))
    refine WP.mono (WP.keep [.r8, .r9] (Q := fun u => u.gpr .r8 = BitVec.ofNat 64 (w - i) ∧ u.gpr .r9 = 0 ∧
      u.mem = u2.mem) (by prun [gpr_write, mem_write, u12, h.r12, BitVec.add_zero]; rfl) (by decide))
      fun u3 ⟨⟨c8, c9, cm⟩, k3⟩ => ?_
    have kall : Keep [.r5, .r6, .r7, .r8, .r9, .r11] t u3 :=
      ((((k1.trans ((Keep.write _ .r5 _).trans (Keep.write _ .r6 _))).trans k2).trans (Keep.write _ .r7 _)).trans
        k3).mono (by decide)
    refine ⟨?_, ?_, ?_, c8, c9, ?_, ?_, kall⟩
    · rw [k3.gpr _ (by decide)]; simp only [gpr_write]; exact b5
    · rw [k3.gpr _ (by decide)]; simp only [gpr_write]; exact b6
    · rw [k3.gpr _ (by decide)]; simp only [gpr_write, ite_true]
    · rw [k3.gpr _ (by decide)]; simp only [gpr_write]
      rw [k2.gpr _ (by decide)]; simp only [gpr_write]; exact a11
    · simp only [cm, bm, am]
  refine WP.mono hb1 fun u ⟨u5, u6, u7, u8, u9, u11, um, ku⟩ => ?_
  have hu := hw.of_keep ku
  rw [WP.seq_iff]
  refine WP.mono (macLoop_ok hu.scr u5 u6 u7 u8 (by rw [u9]; decide) (by rw [u11]; exact BitVec.isLt _)
    (by omega_using [hi, hcw]) (by omega_using [this]) (by omega_using [hi, hcw, fo, hS]) (by omega_using [hi, hcw, fo, hS]) (by omega_using [fy, hS]) (Or.inl (Nat.le_refl _))
    (by unfold Ahead; omega_using [hS, doy])) fun v ⟨_, veq, _, vout, kv⟩ => ?_
  have hv := hu.of_keep kv
  refine WP.mono (WP.keep [.r4, .r10, .r12] (Q := fun t' => t'.gpr .r10 = v.gpr .r10 + BitVec.ofNat 64 4 ∧
      t'.gpr .r12 = v.gpr .r12 - BitVec.ofNat 64 1 ∧ t'.gpr .r4 = v.gpr .r4 - BitVec.ofNat 64 1 ∧
      t'.mem = v.mem) (by prun) (by decide)) fun t' ⟨⟨e10, e12, e4, em⟩, kt⟩ => ?_
  have k : Keep mkRegs t t' := ((ku.trans kv).trans kt).mono (by decide)
  have v4 : v.gpr .r4 = t.gpr .r4 := (kv.gpr _ (by decide)).trans (ku.gpr _ (by decide))
  have v10 : v.gpr .r10 = t.gpr .r10 := (kv.gpr _ (by decide)).trans (ku.gpr _ (by decide))
  have v12 : v.gpr .r12 = t.gpr .r12 := (kv.gpr _ (by decide)).trans (ku.gpr _ (by decide))
  rw [um, u9, u11, show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero] at veq
  rw [um] at vout
  refine ⟨⟨hv.of_keep kt, ?_, ?_, ?_, ?_, ?_, h.regs.trans' k⟩, by rw [e4, v4]⟩
  · rw [e4, v4, h.r4]; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega_using [hi]
  · rw [e10, v10, h.r10]; simp only [off, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2
  · rw [e12, v12, h.r12]; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega_using [hi, hcw]
  · rw [em]
    exact h.keep.trans (KeyWorkspace.Keep.of_arr (d := 4 * i) vout (by omega_using [hi, hcw, hS]) (by simp))
  · -- The row's arithmetic.
    rw [em]
    have split : ∀ (m : Mem) (d : Nat), val32 m B d w =
        val32 m B d i + 2 ^ (32 * i) * val32 m B (d + 4 * i) (w - i) := fun m d => by
      have := val32_append m B d i (w - i); rwa [show i + (w - i) = w by omega_using [hi, hcw]] at this
    have lo : val32 v.mem B (arr w o) i = val32 t.mem B (arr w o) i :=
      vout.val32 (Or.inl (Nat.le_refl _)) (by omega_using [hi, hcw, fo, hS, hnw])
    have ys : val32 t.mem B (arr w y) w = num s.mem B w y := by
      rw [keep_val h.keep (by omega_using []) (by simp only [List.mem_singleton]; exact fun _ e => e ▸ hoy) (by simp) (hw.fit64 hy)]
    have yk : val32 t.mem B (arr w y) (w - i) % 2 ^ (32 * (w - i)) = num s.mem B w y % 2 ^ (32 * (w - i)) := by
      have := val32_append t.mem B (arr w y) (w - i) i
      rw [show w - i + i = w by omega_using [hi, hcw], ys] at this
      rw [this, Nat.add_mul_mod_self_left]
    have row := VG.Proof.Rsa.mulLo_row (P := 2 ^ (32 * i)) (Q := 2 ^ (32 * (w - i)))
      (L := val32 t.mem B (arr w o) i) (H := val32 t.mem B (arr w o + 4 * i) (w - i))
      (H' := val32 v.mem B (arr w o + 4 * i) (w - i)) (x := w32 s.mem B (arr w x + 4 * i))
      (Y := num s.mem B w y) (Nat.two_pow_pos _) (val32_lt _ _ _ _) (val32_lt _ _ _ _) veq yk
    have W : 2 ^ (32 * i) * 2 ^ (32 * (w - i)) = 2 ^ (32 * w) := by
      rw [← Nat.pow_add]; congr 1; omega_using [hi, hcw]
    show val32 v.mem B (arr w o) w = _
    rw [split, lo, row, ← split, W]
    show (num t.mem B w o + _) % _ = _
    rw [h.val, val32_succ, ← xi, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_mul, Nat.mul_assoc]

theorem shr2_ofNat {L : Nat} (hL : L + 3 < 2 ^ 64) :
    (BitVec.ofNat 64 L + BitVec.ofNat 64 3) >>> 2 = BitVec.ofNat 64 ((L + 3) / 4) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega_using [hL]

/-- `mulLo o x y len`, `len` holding `L` with `1 ≤ L ≤ 4 w`: `[o] := [x] [y]
mod 2^(32 w)` over the `⌈L / 4⌉` low digits of `[x]`. -/
theorem mulLo_ok {s : State} {B : Addr} {Z w N o x y L : Nat} (h : Ws s B Z w N) (hN : N ≤ 256) (ho : o < N)
    (hx : x < N) (hy : y < N) (hox : o ≠ x) (hoy : o ≠ y) {len : Reg} (hlen : s.gpr len = BitVec.ofNat 64 L)
    (hL1 : 1 ≤ L) (hLw : L ≤ 4 * w) (hr : len ∉ [.r5, .r8, .r10]) (hl0 : len ≠ .r0) :
    WP isa (mulLo o x y len) s fun t => Ws t B Z w N ∧ KeyWorkspace.Keep B w [o] [] s.mem t.mem ∧
      num t.mem B w o = val32 s.mem B (arr w x) ((L + 3) / 4) * num s.mem B w y % 2 ^ (32 * w) ∧
      Keep mkRegs s t := by
  have fo := h.arr_fit ho
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wle
  have := h.wpos
  have hnw := h.nowrap
  rw [mulLo]; simp only [seqs]; rw [WP.seq_iff]
  -- `[o]`'s pointer, `w` and 0.
  have hb1 : WP isa (.block (mulLoInit o)) s fun u => u.gpr .r5 = off B (arr w o) ∧
      u.gpr .r8 = BitVec.ofNat 64 w ∧ u.gpr .r0 = 0 ∧ u.mem = s.mem ∧ Keep [.r0, .r5, .r8] s u := by
    refine ptr_ok h (r := .r5) (by decide) (by decide) (by decide) (show o < 2 ^ 15 by omega_using [hN, ho]) ?_
    refine WP.mono (WP.keep [.r0, .r8] (Q := fun u => u.gpr .r8 = BitVec.ofNat 64 w ∧ u.gpr .r0 = 0 ∧
      u.mem = s.mem) (by prun [gpr_write, mem_write, h.r29, BitVec.add_zero]; rfl) (by decide))
      fun u ⟨⟨u8, u0, um⟩, ku⟩ => ⟨by rw [ku.gpr _ (by decide)]; simp [gpr_write], u8, u0, um,
        ((Keep.write _ .r5 _).trans ku).mono (by decide)⟩
  refine WP.mono hb1 fun u ⟨u5, u8, u0, um, ku⟩ => ?_
  have hu := h.of_keep ku
  rw [WP.seq_iff]
  refine WP.mono (VG.Proof.Rsa.PPC64LE.Loops.zeroLoop_ok hu.scr u5 u8 u0 (by omega_using [this]) (by omega_arith) (by omega_using [fo, hS]))
    fun v ⟨z, vout, kv⟩ => ?_
  have hv := hu.of_keep kv
  rw [WP.seq_iff]
  -- `x`'s pointer and the counts.
  have l1 : len ∉ [.r5, .r8] := fun hm => hr (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢; rcases hm with e | e <;> simp [e])
  have l2 : len ∉ [.r0, .r5, .r8] := fun hm => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with e | e | e
    · exact hl0 e
    · exact hr (by simp [e])
    · exact hr (by simp [e])
  have vl : v.gpr len = BitVec.ofNat 64 L := by
    rw [kv.gpr _ l1, ku.gpr _ l2]; exact hlen
  have hb2 : WP isa (.block (mulLoSet x len)) v fun u' => u'.gpr .r10 = off B (arr w x) ∧
      u'.gpr .r4 = BitVec.ofNat 64 ((L + 3) / 4) ∧ u'.gpr .r12 = BitVec.ofNat 64 w ∧ u'.mem = v.mem ∧
      Keep [.r4, .r10, .r12] v u' := by
    refine ptr_ok hv (r := .r10) (by decide) (by decide) (by decide) (show x < 2 ^ 15 by omega_using [hN, hx]) ?_
    have l10 : len ≠ .r10 := fun e => hr (by simp [e])
    refine WP.mono (WP.keep [.r4, .r12] (Q := fun u' => u'.gpr .r4 = BitVec.ofNat 64 ((L + 3) / 4) ∧
      u'.gpr .r12 = BitVec.ofNat 64 w ∧ u'.mem = v.mem) (by
        prun [exec_addi hl0 (show 3 < 2 ^ 15 by decide), gpr_write, mem_write, l10, vl, hv.r29, BitVec.add_zero,
          shr2_ofNat (show L + 3 < 2 ^ 64 by omega_arith)]) (by rfl))
      fun u' ⟨⟨a4, a12, am⟩, ka⟩ => ⟨by rw [ka.gpr _ (by decide)]; simp [gpr_write], a4, a12, am,
        ((Keep.write _ .r10 _).trans ka).mono (by decide)⟩
  refine WP.mono hb2 fun t0 ⟨a10, a4, a12, am, kt0⟩ => ?_
  have ht0 := hv.of_keep kt0
  have c1 : 1 ≤ (L + 3) / 4 := by omega_using [hL1]
  have cw : (L + 3) / 4 ≤ w := by omega_using [hLw]
  have I0 : LoInv s t0 B Z w N o x y ((L + 3) / 4) 0 := by
    refine ⟨ht0, by rw [a4, Nat.sub_zero], by rw [a10]; rfl, by rw [a12, Nat.sub_zero], ?_, ?_, ?_⟩
    · rw [am, ← um]
      exact KeyWorkspace.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using vout) (by omega_using [hS]) (by simp)
    · have z0 : num v.mem B w o = 0 :=
        VG.Proof.Bignum.PPC64LE.val32_zero (k := w) (fun j hj => by simpa only [Nat.add_zero] using z j hj)
      rw [am, z0, val32, Nat.zero_mul, Nat.zero_mod]
    · exact ((ku.trans kv).trans kt0).mono (by decide)
  refine WP.mono (wp_countdown (body := mulLoRow o x y) (cnt := .r4) (N := (L + 3) / 4) (by omega_arith) c1
    (fun i t => LoInv s t B Z w N o x y ((L + 3) / 4) i)
    (fun i hi t ht _ => row_ok hN ho hx hy hox hoy hi cw ht) I0 a4)
    fun t ht => ⟨ht.ws, ht.keep, ht.val, ht.regs⟩

/-! ## `mulHalf` -/

/-- The state between the rows of `mulHalf`: `i` rows done, the digits from `i + c` on zero. -/
structure HiInv (s t : State) (B : Addr) (Z w N o x y c : Nat) (i : Nat) : Prop where
  ws : Ws t B Z w N
  r4 : t.gpr .r4 = BitVec.ofNat 64 (c - i)
  r10 : t.gpr .r10 = off B (arr w x + 4 * i)
  r12 : t.gpr .r12 = BitVec.ofNat 64 c
  keep : KeyWorkspace.Keep B w [o] [] s.mem t.mem
  val : val32 t.mem B (arr w o) (i + c) = val32 s.mem B (arr w x) i * val32 s.mem B (arr w y) c
  top : ∀ j, i + c ≤ j → j < w → w32 t.mem B (arr w o + 4 * j) = 0
  regs : Keep mkRegs s t

theorem rowH_ok {s t : State} {B : Addr} {Z w N o x y c i : Nat} (hN : N ≤ 256) (ho : o < N) (hx : x < N)
    (hy : y < N) (hox : o ≠ x) (hoy : o ≠ y) (hi : i < c) (hcw : 2 * c ≤ w) (h : HiInv s t B Z w N o x y c i) :
    WP isa (mulHalfRow o x y) t fun t' => HiInv s t' B Z w N o x y c (i + 1) ∧
      t'.gpr .r4 = t.gpr .r4 - BitVec.ofNat 64 1 := by
  have hw := h.ws
  have fo := hw.arr_fit ho
  have fx := hw.arr_fit hx
  have fy := hw.arr_fit hy
  have hS : S w = 4 * (w + 2) := rfl
  have := hw.wle
  have hnw := hw.nowrap
  have dox := arr_disj (w := w) hox
  have doy := arr_disj (w := w) hoy
  have xi : w32 t.mem B (arr w x + 4 * i) = w32 s.mem B (arr w x + 4 * i) := by
    have := keep_word (b := 32) (o := 4 * i) h.keep (j := x) (by simp only [S]; omega_using [hi, hcw])
      (by simp only [List.mem_singleton]; exact fun _ e => e ▸ hox) (by simp) (hw.fit64 hx)
    exact congrArg BitVec.toNat this
  rw [mulHalfRow, WP.seq_iff]
  have hb1 : WP isa (.block ([.load .w .r11 .r10 0] ++ ptr .r5 o ++ ptr .r6 x ++
      ([.sub .r6 .r10 .r6, .add .r5 .r5 .r6, .addi .r6 .r5 0] : List Instr) ++ ptr .r7 y ++
      ([.addi .r8 .r12 0, .li .r9 0] : List Instr))) t fun u =>
      u.gpr .r5 = off B (arr w o + 4 * i) ∧ u.gpr .r6 = off B (arr w o + 4 * i) ∧
      u.gpr .r7 = off B (arr w y) ∧ u.gpr .r8 = BitVec.ofNat 64 c ∧ u.gpr .r9 = 0 ∧
      (u.gpr .r11).toNat = w32 s.mem B (arr w x + 4 * i) ∧ u.mem = t.mem ∧
      Keep [.r5, .r6, .r7, .r8, .r9, .r11] t u := by
    rw [show ([.load .w .r11 .r10 0] : List Instr) ++ ptr .r5 o ++ ptr .r6 x ++
        ([.sub .r6 .r10 .r6, .add .r5 .r5 .r6, .addi .r6 .r5 0] : List Instr) ++ ptr .r7 y ++
        ([.addi .r8 .r12 0, .li .r9 0] : List Instr) = [.load .w .r11 .r10 0] ++ (ptr .r5 o ++ (ptr .r6 x ++
        (([.sub .r6 .r10 .r6, .add .r5 .r5 .r6, .addi .r6 .r5 0] : List Instr) ++ (ptr .r7 y ++
        ([.addi .r8 .r12 0, .li .r9 0] : List Instr))))) by simp only [List.append_assoc]]
    rw [WP.block_append_iff]
    refine WP.mono (WP.keep [.r11] (Q := fun u => (u.gpr .r11).toNat = w32 s.mem B (arr w x + 4 * i) ∧
      u.mem = t.mem) (by
        prun [h.r10, BitVec.add_zero, hw.scr.ld (show arr w x + 4 * i + 4 ≤ Z by omega_using [hi, hcw, fx, hS])]
        rw [BitVec.toNat_setWidth, ← xi]; exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide))) (by decide))
      fun u1 ⟨⟨a11, am⟩, k1⟩ => ?_
    have h1 := hw.of_keep k1
    refine ptr_ok h1 (r := .r5) (by decide) (by decide) (by decide) (show o < 2 ^ 15 by omega_using [hN, ho]) ?_
    refine ptr_ok (h1.of_keep (Keep.write _ _ _)) (r := .r6) (by decide) (by decide) (by decide)
      (show x < 2 ^ 15 by omega_using [hN, hx]) ?_
    rw [WP.block_append_iff]
    have u10 : u1.gpr .r10 = off B (arr w x + 4 * i) := (k1.gpr _ (by decide)).trans h.r10
    refine WP.mono (WP.keep [.r5, .r6] (Q := fun u => u.gpr .r5 = off B (arr w o + 4 * i) ∧
      u.gpr .r6 = off B (arr w o + 4 * i) ∧ u.mem = u1.mem) (by
        prun [gpr_write, mem_write, u10, BitVec.add_zero]
        rw [off_shift]) (by decide)) fun u2 ⟨⟨b5, b6, bm⟩, k2⟩ => ?_
    have h2 := (h1.of_keep ((Keep.write _ .r5 _).trans (Keep.write _ .r6 _))).of_keep k2
    refine ptr_ok h2 (r := .r7) (by decide) (by decide) (by decide) (show y < 2 ^ 15 by omega_using [hN, hy]) ?_
    have u12 : u2.gpr .r12 = t.gpr .r12 := (k2.gpr _ (by decide)).trans (by
      simp only [gpr_write]; exact k1.gpr _ (by decide))
    refine WP.mono (WP.keep [.r8, .r9] (Q := fun u => u.gpr .r8 = BitVec.ofNat 64 c ∧ u.gpr .r9 = 0 ∧
      u.mem = u2.mem) (by prun [gpr_write, mem_write, u12, h.r12, BitVec.add_zero]; rfl) (by decide))
      fun u3 ⟨⟨c8, c9, cm⟩, k3⟩ => ?_
    have kall : Keep [.r5, .r6, .r7, .r8, .r9, .r11] t u3 :=
      ((((k1.trans ((Keep.write _ .r5 _).trans (Keep.write _ .r6 _))).trans k2).trans (Keep.write _ .r7 _)).trans
        k3).mono (by decide)
    refine ⟨?_, ?_, ?_, c8, c9, ?_, ?_, kall⟩
    · rw [k3.gpr _ (by decide)]; simp only [gpr_write]; exact b5
    · rw [k3.gpr _ (by decide)]; simp only [gpr_write]; exact b6
    · rw [k3.gpr _ (by decide)]; simp only [gpr_write, ite_true]
    · rw [k3.gpr _ (by decide)]; simp only [gpr_write]
      rw [k2.gpr _ (by decide)]; simp only [gpr_write]; exact a11
    · simp only [cm, bm, am]
  refine WP.mono hb1 fun u ⟨u5, u6, u7, u8, u9, u11, um, ku⟩ => ?_
  have hu := hw.of_keep ku
  rw [WP.seq_iff]
  refine WP.mono (macLoop_ok hu.scr u5 u6 u7 u8 (by rw [u9]; decide) (by rw [u11]; exact BitVec.isLt _)
    (by omega_using [hi]) (by omega_using [hcw, this]) (by omega_using [hi, hcw, fo, hS]) (by omega_using [hi, hcw, fo, hS]) (by omega_using [hcw, fy, hS]) (Or.inl (Nat.le_refl _))
    (by unfold Ahead; omega_using [hi, hcw, hS, doy])) fun v ⟨v9, veq, v5, vout, kv⟩ => ?_
  have hv := hu.of_keep kv
  have hvs := hv.scr
  refine WP.mono (WP.keep [.r4, .r10] (Q := fun t' => t'.gpr .r10 = v.gpr .r10 + BitVec.ofNat 64 4 ∧
      t'.gpr .r4 = v.gpr .r4 - BitVec.ofNat 64 1 ∧
      t'.mem = v.mem.writeW (off B (arr w o + 4 * i + 4 * c)) ((v.gpr .r9).setWidth 32)) (by
        prun [v5, BitVec.add_zero, hvs.st (show arr w o + 4 * i + 4 * c + 4 ≤ Z by omega_using [hi, hcw, fo, hS])]) (by decide))
    fun t' ⟨⟨e10, e4, em⟩, kt⟩ => ?_
  have k : Keep mkRegs t t' := ((ku.trans kv).trans kt).mono (by decide)
  have v4 : v.gpr .r4 = t.gpr .r4 := (kv.gpr _ (by decide)).trans (ku.gpr _ (by decide))
  have v10 : v.gpr .r10 = t.gpr .r10 := (kv.gpr _ (by decide)).trans (ku.gpr _ (by decide))
  have v12 : v.gpr .r12 = t.gpr .r12 := (kv.gpr _ (by decide)).trans (ku.gpr _ (by decide))
  rw [um, u9, u11, show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero] at veq
  rw [um] at vout
  have wout : Outside B (arr w o + 4 * i + 4 * c) 4 v.mem t'.mem := by
    rw [em]; exact writeW32_outside _ B _ (by omega_using [hi, hcw, fo, hS, hnw])
  have rout : Outside B (arr w o + 4 * i) (4 * (c + 1)) t.mem t'.mem :=
    (vout.mono (Nat.le_refl _) (by omega_using [])).trans (wout.mono (by omega_using []) (by omega_using []))
  have r9v : ((v.gpr .r9).setWidth 32).toNat = (v.gpr .r9).toNat := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt v9
  refine ⟨⟨hv.of_keep kt, ?_, ?_, by rw [(kt.gpr _ (by decide)), v12, h.r12], ?_, ?_, ?_, h.regs.trans' k⟩,
    by rw [e4, v4]⟩
  · rw [e4, v4, h.r4]; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega_using [hi]
  · rw [e10, v10, h.r10]; simp only [off, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2
  · exact h.keep.trans (KeyWorkspace.Keep.of_arr (d := 4 * i) rout (by omega_using [hi, hcw, hS]) (by simp))
  · -- The row: `x_i [y]`'s low `c` digits and the carry above them.
    have ys : val32 t.mem B (arr w y) c = val32 s.mem B (arr w y) c :=
      keep_val h.keep (by omega_using [hcw]) (by simp only [List.mem_singleton]; exact fun _ e => e ▸ hoy) (by simp)
        (hw.fit64 hy)
    have lo : val32 t'.mem B (arr w o) i = val32 t.mem B (arr w o) i :=
      rout.val32 (Or.inl (Nat.le_refl _)) (by omega_using [hi, hcw, fo, hS, hnw])
    have hrow : val32 t'.mem B (arr w o + 4 * i) (c + 1) =
        val32 t.mem B (arr w o + 4 * i) c + w32 s.mem B (arr w x + 4 * i) * val32 s.mem B (arr w y) c := by
      rw [em, val32_write_top _ _ _ _ _ (by omega_using [hi, hcw, fo, hS, hnw]), r9v, veq, ys]
    have e1 := val32_append t'.mem B (arr w o) i (c + 1)
    have e2 := val32_append t.mem B (arr w o) i c
    rw [show i + (c + 1) = i + 1 + c by omega_using []] at e1
    rw [e1, lo, hrow, val32_succ s.mem B (arr w x) i, ← xi]
    rw [h.val] at e2
    rw [Nat.mul_add, ← Nat.add_assoc, ← e2, Nat.add_mul, xi, Nat.mul_assoc]
  · intro j hj1 hj2
    rw [rout.w32 (by omega_using [hj1]) (by omega_using [fo, hS, hnw, hj2])]
    exact h.top j (by omega_using [hj1]) hj2

/-- `mulHalf o x y len`, `len` holding `L` with `1 ≤ L` and `2 ⌈L / 4⌉ ≤ w`: `[o] := [x] [y]` over the
`⌈L / 4⌉` low digits of each. -/
theorem mulHalf_ok {s : State} {B : Addr} {Z w N o x y L : Nat} (h : Ws s B Z w N) (hN : N ≤ 256) (ho : o < N)
    (hx : x < N) (hy : y < N) (hox : o ≠ x) (hoy : o ≠ y) {len : Reg} (hlen : s.gpr len = BitVec.ofNat 64 L)
    (hL1 : 1 ≤ L) (hLw : 2 * ((L + 3) / 4) ≤ w) (hr : len ∉ [.r5, .r8, .r10]) (hl0 : len ≠ .r0) :
    WP isa (mulHalf o x y len) s fun t => Ws t B Z w N ∧ KeyWorkspace.Keep B w [o] [] s.mem t.mem ∧
      num t.mem B w o = val32 s.mem B (arr w x) ((L + 3) / 4) * val32 s.mem B (arr w y) ((L + 3) / 4) ∧
      Keep mkRegs s t := by
  have fo := h.arr_fit ho
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wle
  have := h.wpos
  have hnw := h.nowrap
  rw [mulHalf]; simp only [seqs]; rw [WP.seq_iff]
  have hb1 : WP isa (.block (mulLoInit o)) s fun u => u.gpr .r5 = off B (arr w o) ∧
      u.gpr .r8 = BitVec.ofNat 64 w ∧ u.gpr .r0 = 0 ∧ u.mem = s.mem ∧ Keep [.r0, .r5, .r8] s u := by
    refine ptr_ok h (r := .r5) (by decide) (by decide) (by decide) (show o < 2 ^ 15 by omega_using [hN, ho]) ?_
    refine WP.mono (WP.keep [.r0, .r8] (Q := fun u => u.gpr .r8 = BitVec.ofNat 64 w ∧ u.gpr .r0 = 0 ∧
      u.mem = s.mem) (by prun [gpr_write, mem_write, h.r29, BitVec.add_zero]; rfl) (by decide))
      fun u ⟨⟨u8, u0, um⟩, ku⟩ => ⟨by rw [ku.gpr _ (by decide)]; simp [gpr_write], u8, u0, um,
        ((Keep.write _ .r5 _).trans ku).mono (by decide)⟩
  refine WP.mono hb1 fun u ⟨u5, u8, u0, um, ku⟩ => ?_
  have hu := h.of_keep ku
  rw [WP.seq_iff]
  refine WP.mono (VG.Proof.Rsa.PPC64LE.Loops.zeroLoop_ok hu.scr u5 u8 u0 (by omega_using [this]) (by omega_arith) (by omega_using [fo, hS]))
    fun v ⟨z, vout, kv⟩ => ?_
  have hv := hu.of_keep kv
  rw [WP.seq_iff]
  have l1 : len ∉ [.r5, .r8] := fun hm => hr (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢; rcases hm with e | e <;> simp [e])
  have l2 : len ∉ [.r0, .r5, .r8] := fun hm => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with e | e | e
    · exact hl0 e
    · exact hr (by simp [e])
    · exact hr (by simp [e])
  have vl : v.gpr len = BitVec.ofNat 64 L := by
    rw [kv.gpr _ l1, ku.gpr _ l2]; exact hlen
  have hb2 : WP isa (.block (mulHalfSet x len)) v fun u' => u'.gpr .r10 = off B (arr w x) ∧
      u'.gpr .r4 = BitVec.ofNat 64 ((L + 3) / 4) ∧ u'.gpr .r12 = BitVec.ofNat 64 ((L + 3) / 4) ∧
      u'.mem = v.mem ∧ Keep [.r4, .r10, .r12] v u' := by
    refine ptr_ok hv (r := .r10) (by decide) (by decide) (by decide) (show x < 2 ^ 15 by omega_using [hN, hx]) ?_
    have l10 : len ≠ .r10 := fun e => hr (by simp [e])
    refine WP.mono (WP.keep [.r4, .r12] (Q := fun u' => u'.gpr .r4 = BitVec.ofNat 64 ((L + 3) / 4) ∧
      u'.gpr .r12 = BitVec.ofNat 64 ((L + 3) / 4) ∧ u'.mem = v.mem) (by
        prun [exec_addi hl0 (show 3 < 2 ^ 15 by decide), gpr_write, mem_write, l10, vl, BitVec.add_zero,
          shr2_ofNat (show L + 3 < 2 ^ 64 by omega_arith)]) (by rfl))
      fun u' ⟨⟨a4, a12, am⟩, ka⟩ => ⟨by rw [ka.gpr _ (by decide)]; simp [gpr_write], a4, a12, am,
        ((Keep.write _ .r10 _).trans ka).mono (by decide)⟩
  refine WP.mono hb2 fun t0 ⟨a10, a4, a12, am, kt0⟩ => ?_
  have ht0 := hv.of_keep kt0
  have c1 : 1 ≤ (L + 3) / 4 := by omega_using [hL1]
  have zt : ∀ j < w, w32 t0.mem B (arr w o + 4 * j) = 0 := fun j hj => by rw [am]; exact z j hj
  have I0 : HiInv s t0 B Z w N o x y ((L + 3) / 4) 0 := by
    refine ⟨ht0, by rw [a4, Nat.sub_zero], by rw [a10]; rfl, a12, ?_, ?_, fun j _ hj => zt j hj, ?_⟩
    · rw [am, ← um]
      exact KeyWorkspace.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using vout) (by omega_using [hS]) (by simp)
    · rw [Nat.zero_add, VG.Proof.Bignum.PPC64LE.val32_zero (fun j hj => zt j (by omega_using [hLw, hj])), val32, Nat.zero_mul]
    · exact ((ku.trans kv).trans kt0).mono (by decide)
  refine WP.mono (wp_countdown (body := mulHalfRow o x y) (cnt := .r4) (N := (L + 3) / 4) (by omega_arith) c1
    (fun i t => HiInv s t B Z w N o x y ((L + 3) / 4) i)
    (fun i hi t ht _ => rowH_ok hN ho hx hy hox hoy hi hLw ht) I0 a4)
    fun t ht => ⟨ht.ws, ht.keep, ?_, ht.regs⟩
  have e := val32_append t.mem B (arr w o) ((L + 3) / 4 + (L + 3) / 4) (w - ((L + 3) / 4 + (L + 3) / 4))
  rw [show (L + 3) / 4 + (L + 3) / 4 + (w - ((L + 3) / 4 + (L + 3) / 4)) = w by omega_using [hLw], ht.val,
    VG.Proof.Bignum.PPC64LE.val32_zero (m := t.mem) (d := arr w o + 4 * ((L + 3) / 4 + (L + 3) / 4))
      (k := w - ((L + 3) / 4 + (L + 3) / 4)) (fun j hj => by
      rw [show arr w o + 4 * ((L + 3) / 4 + (L + 3) / 4) + 4 * j =
        arr w o + 4 * ((L + 3) / 4 + (L + 3) / 4 + j) by omega_using []]
      exact ht.top _ (by omega_using []) (by omega_using [hj])), Nat.mul_zero, Nat.add_zero] at e
  exact e

/-! ## `montMul` -/

/-- The state between the steps of `montMul a x y m tt`: `i` steps done, the
accumulator `[a]` (`K + 1` digits, those above zero) below `3 · 2^(32 (K - 1))`,
and, for `Y < mv`, below `2 mv` and `≡ X_i Y 2^(-32 i)`. -/
structure MInv (s t : State) (B : Addr) (Z w N a x tt c K iv mv Y i : Nat) : Prop where
  ws : Ws t B Z w N
  r4 : t.gpr .r4 = BitVec.ofNat 64 (c - i)
  r10 : t.gpr .r10 = off B (arr w x + 4 * i)
  r12 : t.gpr .r12 = BitVec.ofNat 64 K
  ivEq : w32 t.mem B (arr w tt) = iv
  keep : KeyWorkspace.Keep B w [a, tt] [] s.mem t.mem
  top : ∀ j, K + 1 ≤ j → j < w + 2 → w32 t.mem B (arr w a + 4 * j) = 0
  bound : val32 t.mem B (arr w a) (K + 1) < 3 * 2 ^ (32 * (K - 1))
  cong : Y < mv → val32 t.mem B (arr w a) (K + 1) < 2 * mv ∧
    val32 t.mem B (arr w a) (K + 1) * 2 ^ (32 * i) % mv = val32 s.mem B (arr w x) i * Y % mv
  regs : Keep mkRegs s t

/-- The facts a run of `montMul a x y m tt` holds throughout. -/
structure MEnv (s : State) (B : Addr) (Z w N a x y m tt K iv mv Y : Nat) : Prop where
  hN : N ≤ 256
  ha : a < N
  hx : x < N
  hy : y < N
  hm : m < N
  ht : tt < N
  hax : a ≠ x
  hay : a ≠ y
  ham : a ≠ m
  hat : a ≠ tt
  htx : tt ≠ x
  hty : tt ≠ y
  htm : tt ≠ m
  K2 : 2 ≤ K
  Kw : K ≤ w + 1
  mvEq : val32 s.mem B (arr w m) K = mv
  mtop : mv < 2 ^ (32 * (K - 1))
  inv : (mv % 2 ^ 32 * iv + 1) % 2 ^ 32 = 0
  ivlt : iv < 2 ^ 32
  YEq : val32 s.mem B (arr w y) K = Y
  ytop : Y < 2 ^ (32 * (K - 1))

/-- An array the run only reads. -/
theorem MEnv.rd {s t : State} {B : Addr} {Z w N a x y m tt K iv mv Y : Nat}
    (e : MEnv s B Z w N a x y m tt K iv mv Y) (hw : Ws t B Z w N)
    (k : KeyWorkspace.Keep B w [a, tt] [] s.mem t.mem) {j : Nat} (hj : j < N) (hja : a ≠ j) (hjt : tt ≠ j)
    {n : Nat} (hn : n ≤ w + 2) : val32 t.mem B (arr w j) n = val32 s.mem B (arr w j) n :=
  keep_val k hn (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ (rfl | rfl) <;> with_reducible assumption)
    (by simp) (hw.fit64 hj)

theorem pow_K {K : Nat} (h : 1 ≤ K) : 2 ^ (32 * K) = 2 ^ 32 * 2 ^ (32 * (K - 1)) := by
  rw [← Nat.pow_add]; congr 1; omega_using [h]

/-- The pointers of a loop over `K` digits, `[o]`, `[a]` and `[b]` at `r5`–`r7`, the
count from `r12` and no carry. -/
theorem ptrs_ok {t : State} {B : Addr} {Z w N : Nat} (hw : Ws t B Z w N) {o a b K : Nat} (ho : o < 2 ^ 15)
    (ha : a < 2 ^ 15) (hb : b < 2 ^ 15) (h12 : t.gpr .r12 = BitVec.ofNat 64 K) :
    WP isa (.block (ptr .r5 o ++ ptr .r6 a ++ ptr .r7 b ++ ([.addi .r8 .r12 0, .li .r9 0] : List Instr))) t fun u =>
      u.gpr .r5 = off B (arr w o) ∧ u.gpr .r6 = off B (arr w a) ∧ u.gpr .r7 = off B (arr w b) ∧
      u.gpr .r8 = BitVec.ofNat 64 K ∧ u.gpr .r9 = 0 ∧ u.mem = t.mem ∧ Keep [.r5, .r6, .r7, .r8, .r9] t u := by
  refine ptr3_ok hw ho ha hb fun u p5 p6 p7 ku mu => ?_
  have u12 : u.gpr .r12 = BitVec.ofNat 64 K := (ku.gpr _ (by decide)).trans h12
  refine WP.mono (WP.keep [.r8, .r9] (Q := fun v => v.gpr .r8 = BitVec.ofNat 64 K ∧ v.gpr .r9 = 0 ∧ v.mem = u.mem)
    (by prun [u12, BitVec.add_zero]; rfl) (by decide)) fun v ⟨⟨v8, v9, vm⟩, kv⟩ => ?_
  exact ⟨by rw [kv.gpr _ (by decide)]; exact p5, by rw [kv.gpr _ (by decide)]; exact p6,
    by rw [kv.gpr _ (by decide)]; exact p7, v8, v9, vm.trans mu, (ku.trans kv).mono (by decide)⟩

theorem macPtrs_ok {t : State} {B : Addr} {Z w N : Nat} (hw : Ws t B Z w N) {a b K : Nat} (ha : a < 2 ^ 15)
    (hb : b < 2 ^ 15) (h12 : t.gpr .r12 = BitVec.ofNat 64 K) :
    WP isa (.block (ptr .r5 a ++ ptr .r6 a ++ ptr .r7 b ++ ([.addi .r8 .r12 0, .li .r9 0] : List Instr))) t fun u =>
      u.gpr .r5 = off B (arr w a) ∧ u.gpr .r6 = off B (arr w a) ∧ u.gpr .r7 = off B (arr w b) ∧
      u.gpr .r8 = BitVec.ofNat 64 K ∧ u.gpr .r9 = 0 ∧ u.mem = t.mem ∧ Keep [.r5, .r6, .r7, .r8, .r9] t u :=
  ptrs_ok hw ha ha hb h12

/-- A number of `K + 1` digits below `2^(32 K)` has a zero top digit. -/
theorem top_zero {m : Mem} {B : Addr} {d K : Nat} (h : val32 m B d (K + 1) < 2 ^ (32 * K)) :
    w32 m B (d + 4 * K) = 0 := by
  rw [val32_succ] at h
  by_contra hne
  have : 2 ^ (32 * K) ≤ 2 ^ (32 * K) * w32 m B (d + 4 * K) := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hne)
  omega_using [h, this]

theorem three_lt {K : Nat} (h : 1 ≤ K) : 3 * 2 ^ (32 * (K - 1)) < 2 ^ (32 * K) := by
  rw [pow_K h]; have := Nat.two_pow_pos (32 * (K - 1)); omega_using [this]

/-- `montAddX`: `[a] += x_i [y]`, the carry to digit `K`. -/
theorem addX_ok {s t : State} {B : Addr} {Z w N a x y m tt c K iv mv Y i : Nat}
    (e : MEnv s B Z w N a x y m tt K iv mv Y) (h : MInv s t B Z w N a x tt c K iv mv Y i) (hi : i < c)
    (hcw : c ≤ w) :
    WP isa (montAddX a y) t fun u => Ws u B Z w N ∧ Keep [.r0, .r3, .r5, .r6, .r7, .r8, .r9, .r11] t u ∧
      Outside B (arr w a) (4 * (K + 1)) t.mem u.mem ∧
      val32 u.mem B (arr w a) (K + 1) = val32 t.mem B (arr w a) (K + 1) + w32 s.mem B (arr w x + 4 * i) * Y := by
  have hw := h.ws
  have := hw.wle
  have hnw := hw.nowrap
  have hS : S w = 4 * (w + 2) := rfl
  have fa := hw.arr_fit e.ha
  have fx := hw.arr_fit e.hx
  have fy := hw.arr_fit e.hy
  have K2 := e.K2
  have Kw := e.Kw
  have := e.hN; have := e.ha; have := e.hy; have := e.hx
  have xi : w32 t.mem B (arr w x + 4 * i) = w32 s.mem B (arr w x + 4 * i) := by
    have := keep_word (b := 32) (o := 4 * i) h.keep (j := x) (by simp only [S]; omega_using [hi, hcw])
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ (rfl | rfl); exact e.hax; exact e.htx)
      (by simp) (hw.fit64 e.hx)
    exact congrArg BitVec.toNat this
  have yt : val32 t.mem B (arr w y) K = Y := by
    rw [e.rd hw h.keep e.hy e.hay e.hty (by omega_using [Kw])]; exact e.YEq
  have a0 : w32 t.mem B (arr w a + 4 * K) = 0 :=
    top_zero (Nat.lt_trans h.bound (three_lt (by omega_using [K2])))
  rw [montAddX, WP.seq_iff, show ([.load .w .r11 .r10 0] : List Instr) ++ ptr .r5 a ++ ptr .r6 a ++ ptr .r7 y ++
      ([.addi .r8 .r12 0, .li .r9 0] : List Instr) = [.load .w .r11 .r10 0] ++ (ptr .r5 a ++ ptr .r6 a ++ ptr .r7 y ++
      ([.addi .r8 .r12 0, .li .r9 0] : List Instr)) by simp only [List.append_assoc], WP.block_append_iff]
  refine WP.mono (WP.keep [.r11] (Q := fun u => (u.gpr .r11).toNat = w32 s.mem B (arr w x + 4 * i) ∧
      u.mem = t.mem) (by
        prun [h.r10, BitVec.add_zero, hw.scr.ld (show arr w x + 4 * i + 4 ≤ Z by omega_using [hi, hcw, hS, fx])]
        rw [BitVec.toNat_setWidth, ← xi]; exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide)))
      (by decide)) fun u1 ⟨⟨a11, am⟩, k1⟩ => ?_
  have h1 := hw.of_keep k1
  refine WP.mono (macPtrs_ok h1 (a := a) (b := y) (K := K) (by omega_arith) (by omega_arith)
    ((k1.gpr _ (by decide)).trans h.r12)) fun u2 ⟨p5, p6, p7, p8, p9, m2, k2⟩ => ?_
  have h2 := h1.of_keep k2
  have u11 : (u2.gpr .r11).toNat = w32 s.mem B (arr w x + 4 * i) := by rw [k2.gpr _ (by decide)]; exact a11
  rw [WP.seq_iff]
  refine WP.mono (macLoop_ok h2.scr p5 p6 p7 p8 (by rw [p9]; decide) (by rw [u11]; exact BitVec.isLt _)
    (by omega_using [K2]) (by omega_arith) (by omega_using [hS, fa, Kw]) (by omega_using [hS, fa, Kw]) (by omega_using [hS, fy, Kw]) (Or.inl (Nat.le_refl _))
    (by unfold Ahead; have := arr_disj (w := w) e.hay; simp only [S] at this; omega_using [Kw, this]))
    fun u3 ⟨c3, v3, r5, out3, k3⟩ => ?_
  have h3 := h2.of_keep k3
  refine WP.mono (WP.keep [] (Q := fun u => u.mem = u3.mem.writeW (off B (arr w a + 4 * K)) ((u3.gpr .r9).setWidth 32))
    (by prun [r5, BitVec.add_zero, h3.scr.st (show arr w a + 4 * K + 4 ≤ Z by omega_using [hS, fa, Kw])]) (by decide))
    fun u4 ⟨m4, k4⟩ => ?_
  have k : Keep [.r0, .r3, .r5, .r6, .r7, .r8, .r9, .r11] t u4 :=
    (((k1.trans k2).trans k3).trans k4).mono (by decide)
  rw [m2, am, p9, u11, yt, show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero] at v3
  rw [m2, am] at out3
  refine ⟨h3.of_keep k4, k, ?_, ?_⟩
  · rw [m4]
    exact (out3.mono (by omega_using []) (by omega_using [])).trans ((writeW32_outside _ B _ (by omega_using [hnw, hS, fa, Kw])).mono (by omega_using []) (by omega_using []))
  · rw [m4, val32_write_top _ _ _ _ _ (by omega_using [hnw, hS, fa, Kw]), BitVec.toNat_setWidth, Nat.mod_eq_of_lt c3, val32_succ t.mem, a0,
      Nat.mul_zero, Nat.add_zero, v3]

/-- `k = a₀ iv mod 2^32` into `r11`, from `iv` in digit 0 of `[tt]`. -/
theorem kOf_ok {t : State} {B : Addr} {Z w N a tt : Nat} (hw : Ws t B Z w N) (ha : a < N) (ht : tt < N)
    (hN : N ≤ 256) :
    WP isa (.block (ptr .r5 tt ++ ([.load .w .r3 .r5 0] : List Instr) ++ ptr .r5 a ++
      ([.load .w .r0 .r5 0, .mul .r11 .r0 .r3, .lsr .w .r11 .r11 0] : List Instr))) t fun u =>
      (u.gpr .r11).toNat = w32 t.mem B (arr w a) * w32 t.mem B (arr w tt) % 2 ^ 32 ∧ u.mem = t.mem ∧
      Keep [.r0, .r3, .r5, .r11] t u := by
  have fa := hw.arr_fit ha
  have ft := hw.arr_fit ht
  have hS : S w = 4 * (w + 2) := rfl
  have := hw.wle
  rw [List.append_assoc, List.append_assoc]
  refine ptr_ok hw (r := .r5) (by decide) (by decide) (by decide) (show tt < 2 ^ 15 by omega_using [ht, hN]) ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r3] (Q := fun u => u.gpr .r3 = (t.mem.readW (off B (arr w tt)) 32).setWidth 64 ∧
    u.mem = t.mem) (by prun [gpr_write, mem_write, BitVec.add_zero, hw.scr.ld (show arr w tt + 4 ≤ Z by omega_using [ft, hS])])
    (by decide)) fun u1 ⟨⟨a3, am⟩, k1⟩ => ?_
  have h1 := (hw.of_keep (Keep.write _ .r5 _)).of_keep k1
  refine ptr_ok h1 (r := .r5) (by decide) (by decide) (by decide) (show a < 2 ^ 15 by omega_using [ha, hN]) ?_
  refine WP.mono (WP.keep [.r0, .r11] (Q := fun u => (u.gpr .r11).toNat =
      w32 t.mem B (arr w a) * w32 t.mem B (arr w tt) % 2 ^ 32 ∧ u.mem = t.mem) ?_ (by decide))
    fun u ⟨⟨u11, um⟩, ku⟩ => ⟨u11, by rw [um], (((Keep.write _ .r5 _).trans k1).trans
      ((Keep.write _ .r5 _).trans ku)).mono (by decide)⟩
  prun [gpr_write, mem_write, am, a3, BitVec.add_zero, h1.scr.ld (show arr w a + 4 ≤ Z by omega_using [fa, hS])]
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_zero, BitVec.toNat_setWidth,
    BitVec.toNat_mul, toNat_ext32, toNat_ext32]
  generalize (t.mem.readW (off B (arr w a)) 32).toNat * (t.mem.readW (off B (arr w tt)) 32).toNat = P
  omega_using []

/-- `montAddM`: `[a] += k [m]`, `k = a₀ iv mod 2^32`, the carry added to
digit `K`. -/
theorem addM_ok {s u : State} {B : Addr} {Z w N a x y m tt K iv mv Y : Nat}
    (e : MEnv s B Z w N a x y m tt K iv mv Y) (hw : Ws u B Z w N) (h12 : u.gpr .r12 = BitVec.ofNat 64 K)
    (hiv : w32 u.mem B (arr w tt) = iv) (hmv : val32 u.mem B (arr w m) K = mv)
    (hb : val32 u.mem B (arr w a) (K + 1) + w32 u.mem B (arr w a) * iv % 2 ^ 32 * mv < 4 * 2 ^ (32 * K)) :
    WP isa (montAddM a m tt) u fun v => Ws v B Z w N ∧ Keep [.r0, .r3, .r5, .r6, .r7, .r8, .r9, .r11] u v ∧
      Outside B (arr w a) (4 * (K + 1)) u.mem v.mem ∧
      val32 v.mem B (arr w a) (K + 1) =
        val32 u.mem B (arr w a) (K + 1) + w32 u.mem B (arr w a) * iv % 2 ^ 32 * mv := by
  have := hw.wle
  have hnw := hw.nowrap
  have hS : S w = 4 * (w + 2) := rfl
  have fa := hw.arr_fit e.ha
  have fm := hw.arr_fit e.hm
  have K2 := e.K2
  have Kw := e.Kw
  have := e.hN; have := e.ha; have := e.hm; have := e.ht
  rw [montAddM, WP.seq_iff, WP.block_append_iff]
  refine WP.mono (kOf_ok hw e.ha e.ht e.hN) fun u1 ⟨k11, m1, k1⟩ => ?_
  rw [hiv] at k11
  have h1 := hw.of_keep k1
  refine WP.mono (macPtrs_ok h1 (a := a) (b := m) (K := K) (by omega_arith) (by omega_arith)
    ((k1.gpr _ (by decide)).trans h12)) fun u2 ⟨p5, p6, p7, p8, p9, m2, k2⟩ => ?_
  have h2 := h1.of_keep k2
  have u11 : (u2.gpr .r11).toNat = w32 u.mem B (arr w a) * iv % 2 ^ 32 := by
    rw [k2.gpr _ (by decide)]; exact k11
  rw [WP.seq_iff]
  refine WP.mono (macLoop_ok h2.scr p5 p6 p7 p8 (by rw [p9]; decide) (by rw [u11]; exact Nat.mod_lt _ (by decide))
    (by omega_using [K2]) (by omega_arith) (by omega_using [hS, fa, Kw]) (by omega_using [hS, fa, Kw]) (by omega_using [hS, fm, Kw]) (Or.inl (Nat.le_refl _))
    (by unfold Ahead; have := arr_disj (w := w) e.ham; simp only [S] at this; omega_using [Kw, this]))
    fun u3 ⟨c3, v3, r5, out3, k3⟩ => ?_
  have h3 := h2.of_keep k3
  rw [m2, m1, p9, u11, hmv, show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero] at v3
  rw [m2, m1] at out3
  have dK : w32 u3.mem B (arr w a + 4 * K) = w32 u.mem B (arr w a + 4 * K) :=
    out3.w32 (Or.inr (by omega_using [])) (by omega_using [hnw, hS, fa, Kw])
  refine WP.mono (WP.keep [.r0] (Q := fun v => v.mem = u3.mem.writeW (off B (arr w a + 4 * K))
      (((u3.mem.readW (off B (arr w a + 4 * K)) 32).setWidth 64 + u3.gpr .r9).setWidth 32))
    (by prun [r5, BitVec.add_zero, h3.scr.ld (show arr w a + 4 * K + 4 ≤ Z by omega_using [hS, fa, Kw]),
      h3.scr.st (show arr w a + 4 * K + 4 ≤ Z by omega_using [hS, fa, Kw])]) (by decide)) fun v ⟨mv4, k4⟩ => ?_
  have k : Keep [.r0, .r3, .r5, .r6, .r7, .r8, .r9, .r11] u v := (((k1.trans k2).trans k3).trans k4).mono (by decide)
  refine ⟨h3.of_keep k4, k, ?_, ?_⟩
  · rw [mv4]
    exact (out3.mono (by omega_using []) (by omega_using [])).trans ((writeW32_outside _ B _ (by omega_using [hnw, hS, fa, Kw])).mono (by omega_using []) (by omega_using []))
  · -- The top digit and the carry.
    have eT : (((u3.mem.readW (off B (arr w a + 4 * K)) 32).setWidth 64 + u3.gpr .r9).setWidth 32).toNat =
        (w32 u.mem B (arr w a + 4 * K) + (u3.gpr .r9).toNat) % 2 ^ 32 := by
      rw [BitVec.toNat_setWidth, BitVec.toNat_add, toNat_ext32]
      show ((w32 u3.mem B (arr w a + 4 * K)) + _) % _ % _ = _
      rw [dK]; have := (u3.gpr .r9).isLt; omega_using []
    have sp := val32_succ u.mem B (arr w a) K
    have hp : 0 < 2 ^ (32 * K) := Nat.two_pow_pos _
    have hlt : w32 u.mem B (arr w a + 4 * K) + (u3.gpr .r9).toNat < 2 ^ 32 := by
      have e1 : val32 u3.mem B (arr w a) K + 2 ^ (32 * K) * (w32 u.mem B (arr w a + 4 * K) + (u3.gpr .r9).toNat) =
          val32 u.mem B (arr w a) (K + 1) + w32 u.mem B (arr w a) * iv % 2 ^ 32 * mv := by
        rw [sp, Nat.mul_add]; omega_using [v3]
      have : 2 ^ (32 * K) * (w32 u.mem B (arr w a + 4 * K) + (u3.gpr .r9).toNat) < 2 ^ (32 * K) * 4 := by omega_using [hb, e1]
      have := Nat.lt_of_mul_lt_mul_left this
      omega_using [this]
    rw [mv4, val32_write_top _ _ _ _ _ (by omega_using [hnw, hS, fa, Kw]), eT, Nat.mod_eq_of_lt hlt, sp, Nat.mul_add]
    omega_using [v3]

theorem shl2_ofNat (K : Nat) : BitVec.ofNat 64 K <<< 2 = BitVec.ofNat 64 (4 * K) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_using []

/-- `montShift`: `[a] := [a] / 2^32` (a multiple of `2^32`), `x`'s next digit
and one step less. -/
theorem shift_ok {u : State} {B : Addr} {Z w N a K : Nat} (hw : Ws u B Z w N) (ha : a < N) (hN : N ≤ 256)
    (hK1 : 1 ≤ K) (hKw : K ≤ w + 1) (h12 : u.gpr .r12 = BitVec.ofNat 64 K)
    (hT : val32 u.mem B (arr w a) (K + 1) % 2 ^ 32 = 0) :
    WP isa (montShift a) u fun v => Ws v B Z w N ∧ Keep [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10] u v ∧
      Outside B (arr w a) (4 * (K + 1)) u.mem v.mem ∧
      val32 v.mem B (arr w a) (K + 1) = val32 u.mem B (arr w a) (K + 1) / 2 ^ 32 ∧
      v.gpr .r10 = u.gpr .r10 + BitVec.ofNat 64 4 ∧ v.gpr .r4 = u.gpr .r4 - BitVec.ofNat 64 1 := by
  have := hw.wle
  have hnw := hw.nowrap
  have hS : S w = 4 * (w + 2) := rfl
  have fa := hw.arr_fit ha
  rw [montShift, WP.seq_iff]
  have hb1 : WP isa (.block (ptr .r5 a ++ ([.addi .r6 .r5 4, .addi .r8 .r12 0] : List Instr))) u fun v =>
      v.gpr .r5 = off B (arr w a) ∧ v.gpr .r6 = off B (arr w a + 4) ∧ v.gpr .r8 = BitVec.ofNat 64 K ∧
      v.mem = u.mem ∧ Keep [.r5, .r6, .r8] u v := by
    refine ptr_ok hw (r := .r5) (by decide) (by decide) (by decide) (show a < 2 ^ 15 by omega_using [ha, hN]) ?_
    refine WP.mono (WP.keep [.r6, .r8] (Q := fun v => v.gpr .r6 = off B (arr w a + 4) ∧
      v.gpr .r8 = BitVec.ofNat 64 K ∧ v.mem = u.mem) (by
        prun [gpr_write, mem_write, h12, BitVec.add_zero]) (by decide))
      fun v ⟨⟨v6, v8, vm⟩, kv⟩ => ⟨by rw [kv.gpr _ (by decide)]; simp [gpr_write], v6, v8, vm,
        ((Keep.write _ .r5 _).trans kv).mono (by decide)⟩
  refine WP.mono hb1 fun v ⟨p5, p6, p8, vm, kv⟩ => ?_
  have hv := hw.of_keep kv
  rw [WP.seq_iff]
  refine WP.mono (VG.Proof.Rsa.PPC64LE.Loops.copyLoop_ok hv.scr p5 p6 p8 hK1 (by omega_using [hKw, this]) (by omega_using [hKw, hS, fa]) (by omega_using [hKw, hS, fa])
    (Or.inl (by omega_using []))) fun v2 ⟨cv, out2, k2⟩ => ?_
  have h2 := hv.of_keep k2
  have v12 : v2.gpr .r12 = BitVec.ofNat 64 K := (k2.gpr _ (by decide)).trans ((kv.gpr _ (by decide)).trans h12)
  refine ptr_ok h2 (r := .r5) (by decide) (by decide) (by decide) (show a < 2 ^ 15 by omega_using [ha, hN]) ?_
  refine WP.mono (WP.keep [.r0, .r4, .r5, .r10] (Q := fun x => x.mem = v2.mem.writeW (off B (arr w a + 4 * K)) 0#32 ∧
      x.gpr .r10 = v2.gpr .r10 + BitVec.ofNat 64 4 ∧ x.gpr .r4 = v2.gpr .r4 - BitVec.ofNat 64 1) (by
        have e5 : off B (arr w a) + BitVec.ofNat 64 K <<< 2 = off B (arr w a + 4 * K) := by
          rw [shl2_ofNat]; simp only [off, BitVec.add_assoc, ← BitVec.ofNat_add]
        prun [gpr_write, mem_write, v12, e5, BitVec.add_zero, h2.scr.st (show arr w a + 4 * K + 4 ≤ Z by omega_using [hKw, hS, fa])]
        rfl) (by decide)) fun x ⟨⟨xm, x10, x4⟩, kx⟩ => ?_
  have k : Keep [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10] u x :=
    ((kv.trans k2).trans ((Keep.write _ .r5 _).trans kx)).mono (by decide)
  have u10 : v2.gpr .r10 = u.gpr .r10 := (k2.gpr _ (by decide)).trans (kv.gpr _ (by decide))
  have u4 : v2.gpr .r4 = u.gpr .r4 := (k2.gpr _ (by decide)).trans (kv.gpr _ (by decide))
  rw [vm] at cv out2
  refine ⟨(h2.of_keep (Keep.write _ .r5 _)).of_keep kx, k, ?_, ?_, by rw [x10, u10], by rw [x4, u4]⟩
  · rw [xm]
    exact (out2.mono (by omega_using []) (by omega_using [])).trans ((writeW32_outside _ B _ (by omega_using [hKw, hnw, hS, fa])).mono (by omega_using []) (by omega_using []))
  · rw [xm, val32_write_top _ _ _ _ _ (by omega_using [hKw, hnw, hS, fa]), cv, show (0#32).toNat = 0 from rfl, Nat.mul_zero,
      Nat.add_zero]
    have ev : val32 u.mem B (arr w a) (K + 1) = w32 u.mem B (arr w a) + 2 ^ 32 * val32 u.mem B (arr w a + 4) K := rfl
    have a0lt : w32 u.mem B (arr w a) < 2 ^ 32 := BitVec.isLt _
    rw [ev, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt a0lt] at hT
    rw [ev, hT, Nat.zero_add, Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]

/-- A step of `montMul`. -/
theorem step_ok {s t : State} {B : Addr} {Z w N a x y m tt c K iv mv Y i : Nat}
    (e : MEnv s B Z w N a x y m tt K iv mv Y) (h : MInv s t B Z w N a x tt c K iv mv Y i) (hi : i < c)
    (hcw : c ≤ w) :
    WP isa (montStep a y m tt) t fun t' => MInv s t' B Z w N a x tt c K iv mv Y (i + 1) ∧
      t'.gpr .r4 = t.gpr .r4 - BitVec.ofNat 64 1 := by
  have hw := h.ws
  have := hw.wle
  have hnw := hw.nowrap
  have hS : S w = 4 * (w + 2) := rfl
  have fa := hw.arr_fit e.ha
  have K2 := e.K2
  have Kw := e.Kw
  have := e.hN; have := e.ha; have := e.hm; have := e.ht
  have M0 : 0 < 2 ^ (32 * (K - 1)) := Nat.two_pow_pos _
  have pK := pow_K (K := K) (by omega_using [K2])
  -- The arrays outside `[a]`'s `K + 1` digits.
  have outw : ∀ {m₁ m₂ : Mem}, Outside B (arr w a) (4 * (K + 1)) m₁ m₂ → ∀ {j : Nat}, j < N → j ≠ a →
      ∀ {n : Nat}, n ≤ w + 2 → val32 m₂ B (arr w j) n = val32 m₁ B (arr w j) n := fun o j hj hja n hn =>
    o.val32 (by have := arr_disj (w := w) hja; have := hw.arr_fit hj; simp only [S] at *; omega_arith)
      (by have := hw.fit64 hj; simp only [S] at *; omega_using [hn, this])
  rw [montStep]; simp only [seqs]; rw [WP.seq_iff]
  refine WP.mono (addX_ok e h hi hcw) fun u ⟨hu, ku, ou, vu⟩ => ?_
  have u12 : u.gpr .r12 = BitVec.ofNat 64 K := (ku.gpr _ (by decide)).trans h.r12
  have uiv : w32 u.mem B (arr w tt) = iv := by
    have := outw ou e.ht e.hat.symm (n := 1) (by omega_using []); simp only [val32] at this; have := h.ivEq; omega_arith
  have umv : val32 u.mem B (arr w m) K = mv := by
    rw [outw ou e.hm e.ham.symm (by omega_using [Kw]), e.rd hw h.keep e.hm e.ham e.htm (by omega_using [Kw])]; exact e.mvEq
  have xi_lt : w32 s.mem B (arr w x + 4 * i) < 2 ^ 32 := BitVec.isLt _
  have Ylt := e.ytop
  have mlt := e.mtop
  have Alt := h.bound
  have hXY : w32 s.mem B (arr w x + 4 * i) * Y < 2 ^ (32 * K) := by
    rw [pK]; exact Nat.mul_lt_mul_of_lt_of_le xi_lt (Nat.le_of_lt Ylt) M0
  have k_lt : w32 u.mem B (arr w a) * iv % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have hkm : w32 u.mem B (arr w a) * iv % 2 ^ 32 * mv < 2 ^ (32 * K) := by
    rw [pK]; exact Nat.mul_lt_mul_of_lt_of_le k_lt (Nat.le_of_lt mlt) M0
  rw [WP.seq_iff]
  refine WP.mono (addM_ok e hu u12 uiv umv (by rw [vu]; omega_using [pK, Alt, hXY, hkm])) fun v ⟨hv, kv, ov, vv⟩ => ?_
  have v12 : v.gpr .r12 = BitVec.ofNat 64 K := (kv.gpr _ (by decide)).trans u12
  -- `T` is a multiple of `2^32`.
  have a0 : w32 u.mem B (arr w a) = val32 u.mem B (arr w a) (K + 1) % 2 ^ 32 := by
    show _ = (w32 u.mem B (arr w a) + 2 ^ 32 * val32 u.mem B (arr w a + 4) K) % 2 ^ 32
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (BitVec.isLt _)]
  have hT : val32 v.mem B (arr w a) (K + 1) % 2 ^ 32 = 0 := by
    rw [vv, a0]
    exact VG.Proof.Rsa.mont_div e.inv
  refine WP.mono (shift_ok hv e.ha e.hN (by omega_using [K2]) Kw v12 hT) fun t' ⟨ht', kt, ot, vt, t10, t4⟩ => ?_
  have k3 : Keep mkRegs t t' := ((ku.trans kv).trans kt).mono (by decide)
  have u4 : t'.gpr .r4 = t.gpr .r4 - BitVec.ofNat 64 1 := by
    rw [t4, kv.gpr _ (by decide), ku.gpr _ (by decide)]
  have o3 : Outside B (arr w a) (4 * (K + 1)) t.mem t'.mem := (ou.trans ov).trans ot
  -- The new accumulator.
  have eA : val32 t'.mem B (arr w a) (K + 1) = (val32 t.mem B (arr w a) (K + 1) +
      w32 s.mem B (arr w x + 4 * i) * Y + w32 u.mem B (arr w a) * iv % 2 ^ 32 * mv) / 2 ^ 32 := by
    rw [vt, vv, vu]
  refine ⟨⟨ht', ?_, ?_, (kt.gpr _ (by decide)).trans v12, ?_, ?_, ?_, ?_, ?_, h.regs.trans' k3⟩, u4⟩
  · rw [u4, h.r4]; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega_using [hi]
  · rw [t10, kv.gpr _ (by decide), ku.gpr _ (by decide), h.r10]
    simp only [off, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2
  · have := outw o3 e.ht e.hat.symm (n := 1) (by omega_using []); simp only [val32] at this
    have := h.ivEq; omega_arith
  · exact h.keep.trans (KeyWorkspace.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using o3) (by omega_using [hS, Kw])
      (by simp))
  · intro j hj1 hj2
    rw [o3.w32 (Or.inr (by omega_using [hj1])) (by omega_using [hnw, hS, fa, hj2])]; exact h.top j hj1 hj2
  · rw [eA]; exact VG.Proof.Rsa.mont_bound mlt Ylt Alt xi_lt k_lt
  · intro hYm
    obtain ⟨b2, cg⟩ := h.cong hYm
    refine ⟨by rw [eA]; exact VG.Proof.Rsa.mont_bound2 hYm b2 xi_lt k_lt, ?_⟩
    have hTt : (val32 t.mem B (arr w a) (K + 1) + w32 s.mem B (arr w x + 4 * i) * Y +
        w32 u.mem B (arr w a) * iv % 2 ^ 32 * mv) % 2 ^ 32 = 0 := by rw [← vu, ← vv]; exact hT
    rw [eA, VG.Proof.Rsa.mont_cong hTt cg, val32_succ]

/-- `montInit`: `-m⁻¹ mod 2^32` to digit 0 of `[tt]`, `K` into `r12`, the
pointers of `[x]` and `[a]`, `w + 2` and 0. -/
theorem init_ok {s : State} {B : Addr} {Z w N a x m tt L : Nat} (hw : Ws s B Z w N) (hN : N ≤ 256)
    (ha : a < N) (hx : x < N) (hm : m < N) (ht : tt < N)
    (hodd : w32 s.mem B (arr w m) % 2 = 1) {len : Reg} (hlen : s.gpr len = BitVec.ofNat 64 L)
    (hL : L + 7 < 2 ^ 64) (hr : len ∉ mkRegs) (hl0 : len ≠ .r0) :
    WP isa (.block (montInit a x m tt len)) s fun u => ∃ iv : Nat, iv < 2 ^ 32 ∧
      (w32 s.mem B (arr w m) * iv + 1) % 2 ^ 32 = 0 ∧ Ws u B Z w N ∧
      u.gpr .r12 = BitVec.ofNat 64 ((L + 3) / 4 + 1) ∧ u.gpr .r10 = off B (arr w x) ∧
      u.gpr .r5 = off B (arr w a) ∧ u.gpr .r8 = BitVec.ofNat 64 (w + 2) ∧ u.gpr .r0 = 0 ∧
      u.mem = s.mem.writeW (off B (arr w tt)) (BitVec.ofNat 32 iv) ∧ Keep mkRegs s u := by
  have := hw.wle
  have hnw := hw.nowrap
  have hS : S w = 4 * (w + 2) := rfl
  have fm := hw.arr_fit hm
  have ft := hw.arr_fit ht
  simp only [montInit, List.append_assoc]
  refine ptr_ok hw (r := .r10) (by decide) (by decide) (by decide) (show m < 2 ^ 15 by omega_using [hN, hm]) ?_
  rw [WP.block_append_iff]
  have wodd : (word (s.write .r10 (off B (arr w m))).mem B (arr w m)).toNat % 2 = 1 := by
    rw [mem_write, word_eq_w32]; omega_using [hodd]
  refine WP.mono (Pub.minv_ok ((hw.of_keep (Keep.write _ .r10 _)).scr) (by simp [gpr_write]) (by omega_using [hS, fm]) wodd)
    fun u1 ⟨⟨i1, inv1, m1⟩, k1⟩ => ?_
  rw [mem_write] at m1 inv1
  have h1 := (hw.of_keep (Keep.write _ .r10 _)).of_keep k1
  have n4 : len ∉ [.r0, .r3, .r4, .r12] := fun hm => hr (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢; rcases hm with e | e | e | e <;> simp [e])
  have n10 : len ≠ .r10 := fun e => hr (by simp [e])
  have n5 : len ≠ .r5 := fun e => hr (by simp [e])
  have l1 : u1.gpr len = BitVec.ofNat 64 L := by
    rw [k1.gpr _ n4]; simp only [gpr_write, n10, ↓reduceIte]; exact hlen
  refine ptr_ok h1 (r := .r5) (by decide) (by decide) (by decide) (show tt < 2 ^ 15 by omega_using [hN, ht]) ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r12] (Q := fun u => u.gpr .r12 = BitVec.ofNat 64 ((L + 3) / 4 + 1) ∧
      u.mem = u1.mem.writeW (off B (arr w tt)) ((u1.gpr .r12).setWidth 32)) (by
        prun [gpr_write, mem_write, exec_addi hl0 (show 3 < 2 ^ 15 by decide), n5, l1, BitVec.add_zero,
          h1.scr.st (show arr w tt + 4 ≤ Z by omega_using [hS, ft]), shr2_ofNat (show L + 3 < 2 ^ 64 by omega_using [hL])]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using []) (by rfl)) fun u2 ⟨⟨a12, am⟩, k2⟩ => ?_
  have h2 := (h1.of_keep (Keep.write _ .r5 _)).of_keep k2
  refine ptr_ok h2 (r := .r10) (by decide) (by decide) (by decide) (show x < 2 ^ 15 by omega_using [hN, hx]) ?_
  refine ptr_ok (h2.of_keep (Keep.write _ .r10 _)) (r := .r5) (by decide) (by decide) (by decide)
    (show a < 2 ^ 15 by omega_using [hN, ha]) ?_
  refine WP.mono (WP.keep [.r0, .r8] (Q := fun u => u.gpr .r8 = BitVec.ofNat 64 (w + 2) ∧ u.gpr .r0 = 0 ∧
      u.mem = u2.mem) (by prun [gpr_write, mem_write, h2.r29, BitVec.add_zero]; exact ⟨(BitVec.ofNat_add _ _).symm, rfl⟩) (by decide))
    fun u3 ⟨⟨c8, c0, cm⟩, k3⟩ => ?_
  refine ⟨(u1.gpr .r12).toNat, i1, inv1, ?_, ?_, ?_, ?_, c8, c0, ?_, ?_⟩
  · exact ((h2.of_keep (Keep.write _ .r10 _)).of_keep (Keep.write _ .r5 _)).of_keep k3
  · rw [k3.gpr _ (by decide)]; simp only [gpr_write]; exact a12
  · rw [k3.gpr _ (by decide)]; simp [gpr_write]
  · rw [k3.gpr _ (by decide)]; simp [gpr_write]
  · rw [cm, am, m1]
    congr 1
  · exact (((((Keep.write _ .r10 _).trans k1).trans (Keep.write _ .r5 _)).trans k2).trans
      (((Keep.write _ .r10 _).trans (Keep.write _ .r5 _)).trans k3)).mono (by decide)

/-- `montFinal`: `[a] := [a] - [m]` where that does not borrow, over `K`
digits, through `[tt]`. -/
theorem final_ok {v : State} {B : Addr} {Z w N a m tt K A mv : Nat} (hw : Ws v B Z w N) (hN : N ≤ 256)
    (ha : a < N) (hm : m < N) (ht : tt < N) (ham : a ≠ m) (hat : a ≠ tt) (htm : tt ≠ m) (hK1 : 1 ≤ K)
    (hKw : K ≤ w + 1) (h12 : v.gpr .r12 = BitVec.ofNat 64 K) (hA : val32 v.mem B (arr w a) (K + 1) = A)
    (hAK : A < 2 ^ (32 * K)) (hmv : val32 v.mem B (arr w m) K = mv) :
    WP isa (montFinal a m tt) v fun t => Ws t B Z w N ∧ Keep [.r0, .r3, .r5, .r6, .r7, .r8, .r9] v t ∧
      KeyWorkspace.Keep B w [a, tt] [] v.mem t.mem ∧
      (∀ j, K ≤ j → j < w + 2 → w32 t.mem B (arr w a + 4 * j) = w32 v.mem B (arr w a + 4 * j)) ∧
      val32 t.mem B (arr w a) K = (if mv ≤ A then A - mv else A) := by
  have := hw.wle
  have hnw := hw.nowrap
  have hS : S w = 4 * (w + 2) := rfl
  have fa := hw.arr_fit ha
  have fm := hw.arr_fit hm
  have ft := hw.arr_fit ht
  have dat := arr_disj (w := w) hat
  have dam := arr_disj (w := w) ham
  have dtm := arr_disj (w := w) htm
  simp only [S] at dat dam dtm
  have vaK : val32 v.mem B (arr w a) K = A := by
    have := top_zero (hA ▸ hAK : val32 v.mem B (arr w a) (K + 1) < 2 ^ (32 * K))
    rw [← hA, val32_succ, this, Nat.mul_zero, Nat.add_zero]
  rw [montFinal]; simp only [seqs]; rw [WP.seq_iff]
  refine WP.mono (ptrs_ok hw (o := tt) (a := a) (b := m) (K := K) (by omega_using [hN, ht]) (by omega_using [hN, ha]) (by omega_using [hN, hm]) h12)
    fun u ⟨p5, p6, p7, p8, p9, mu, ku⟩ => ?_
  have hu := hw.of_keep ku
  rw [WP.seq_iff]
  refine WP.mono (VG.Proof.Rsa.PPC64LE.Loops.subLoop_ok hu.scr p5 p6 p7 p8 (by rw [p9]; decide) hK1 (by omega_using [hKw, this])
    (by omega_using [hKw, hS, ft]) (by omega_using [hKw, hS, fa]) (by omega_using [hKw, hS, fm]) (by unfold Ahead; omega_using [hKw, dat]) (by unfold Ahead; omega_using [hKw, dtm]))
    fun u2 ⟨b2, e2, out2, k2⟩ => ?_
  have h2 := hu.of_keep k2
  rw [mu, p9, show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero, vaK, hmv] at e2
  rw [mu] at out2
  have u12 : u2.gpr .r12 = BitVec.ofNat 64 K := (k2.gpr _ (by decide)).trans ((ku.gpr _ (by decide)).trans h12)
  rw [WP.seq_iff]
  -- The mask of the borrow, and the pointers.
  have hb3 : WP isa (.block (ptr .r5 a ++ ptr .r6 tt ++ ptr .r7 a ++
      ([.addi .r8 .r12 0, .li .r0 0, .sub .r9 .r0 .r9] : List Instr))) u2 fun x =>
      x.gpr .r5 = off B (arr w a) ∧ x.gpr .r6 = off B (arr w tt) ∧ x.gpr .r7 = off B (arr w a) ∧
      x.gpr .r8 = BitVec.ofNat 64 K ∧ x.gpr .r9 = 0#64 - u2.gpr .r9 ∧ x.mem = u2.mem ∧
      Keep [.r0, .r5, .r6, .r7, .r8, .r9] u2 x := by
    refine ptr3_ok h2 (show a < 2 ^ 15 by omega_using [hN, ha]) (show tt < 2 ^ 15 by omega_using [hN, ht]) (show a < 2 ^ 15 by omega_using [hN, ha])
      fun y q5 q6 q7 ky my => ?_
    have y12 : y.gpr .r12 = BitVec.ofNat 64 K := (ky.gpr _ (by decide)).trans u12
    have y9 : y.gpr .r9 = u2.gpr .r9 := ky.gpr _ (by decide)
    refine WP.mono (WP.keep [.r0, .r8, .r9] (Q := fun z => z.gpr .r8 = BitVec.ofNat 64 K ∧
      z.gpr .r9 = 0#64 - u2.gpr .r9 ∧ z.mem = y.mem) (by prun [y12, y9, BitVec.add_zero]) (by decide))
      fun z ⟨⟨z8, z9, zm⟩, kz⟩ => ?_
    exact ⟨by rw [kz.gpr _ (by decide)]; exact q5, by rw [kz.gpr _ (by decide)]; exact q6,
      by rw [kz.gpr _ (by decide)]; exact q7, z8, z9, zm.trans my, (ky.trans kz).mono (by decide)⟩
  refine WP.mono hb3 fun u3 ⟨r5, r6, r7, r8, r9, m3, k3⟩ => ?_
  have h3 := h2.of_keep k3
  have e9 : ∀ y : BitVec 64, y.toNat ≤ 1 →
      0#64 - y = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if decide (y.toNat = 1) then 1 else 0) := by
    intro y hy
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hy with e | e
    · have : y = 0#64 := BitVec.eq_of_toNat_eq e
      subst this; rfl
    · have : y = 1#64 := BitVec.eq_of_toNat_eq e
      subst this; rfl
  refine WP.mono (VG.Proof.Rsa.PPC64LE.Loops.selLoop_ok (b := decide ((u2.gpr .r9).toNat = 1)) h3.scr
    r5 r6 r7 r8 (by rw [r9]; exact e9 _ b2) hK1 (by omega_using [hKw, this]) (by omega_using [hKw, hS, fa]) (by omega_using [hKw, hS, ft]) (by omega_using [hKw, hS, fa])
    (by unfold Ahead; omega_using [hKw, dat]) (Or.inl (Nat.le_refl _))) fun t ⟨sv, out4, k4⟩ => ?_
  refine ⟨h3.of_keep k4, (((ku.trans k2).trans k3).trans k4).mono (by decide), ?_, ?_, ?_⟩
  · rw [m3] at out4
    exact (KeyWorkspace.Keep.of_arr (o := tt) (d := 0) (by simpa only [Nat.add_zero] using out2) (by omega_using [hKw, hS])
      (by simp)).trans (KeyWorkspace.Keep.of_arr (o := a) (d := 0) (by simpa only [Nat.add_zero] using out4)
        (by omega_using [hKw, hS]) (by simp))
  · intro j hj1 hj2
    rw [m3] at out4
    rw [out4.w32 (Or.inr (by omega_using [hj1])) (by omega_using [hK1, hKw, this, hnw, hS, fa, fm, ft, dat, dam, dtm, hj1, hj2]), out2.w32 (by omega_using [hKw, dat, hj2]) (by omega_using [hK1, hKw, this, hnw, hS, fa, fm, ft, dat, dam, dtm, hj1, hj2])]
  · rw [sv, m3]
    have vt : val32 u2.mem B (arr w tt) K + mv = A + 2 ^ (32 * K) * (u2.gpr .r9).toNat := e2
    have vtl := val32_lt u2.mem B (arr w tt) K
    have va2 : val32 u2.mem B (arr w a) K = A := by
      rw [out2.val32 (by omega_using [hKw, dat]) (by omega_using [hKw, hnw, hS, fa])]; exact vaK
    by_cases eb : (u2.gpr .r9).toNat = 1
    · simp only [eb, decide_true, ↓reduceIte]
      rw [va2]
      have : ¬ mv ≤ A := by rw [eb] at vt; omega_using [vt, vtl]
      simp only [this, ↓reduceIte]
    · have e0 : (u2.gpr .r9).toNat = 0 := by omega_using [b2, eb]
      simp only [eb, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [e0, Nat.mul_zero, Nat.add_zero] at vt
      have : mv ≤ A := by omega_using [vt]
      simp only [this, ↓reduceIte]; omega_using [vt]


theorem val32_ext_zero {m : Mem} {B : Addr} {d K n R : Nat} (h : val32 m B d K = R) (hKn : K ≤ n)
    (hz : ∀ j, K ≤ j → j < n → w32 m B (d + 4 * j) = 0) : val32 m B d n = R := by
  have := val32_append m B d K (n - K)
  rw [show K + (n - K) = n by omega_using [hKn]] at this
  rw [this, h, VG.Proof.Bignum.PPC64LE.val32_zero (k := n - K) (fun j hj => by
    rw [Nat.add_assoc, ← Nat.mul_add]; exact hz (K + j) (by omega_using []) (by omega_using [hj])), Nat.mul_zero, Nat.add_zero]

theorem val32_drop_top {m : Mem} {B : Addr} {d n R : Nat} (h : val32 m B d (n + 1) = R) (hR : R < 2 ^ (32 * n)) :
    val32 m B d n = R := by
  rw [val32_succ] at h
  have := val32_lt m B d n
  by_cases hz : w32 m B (d + 4 * n) = 0
  · rw [hz, Nat.mul_zero, Nat.add_zero] at h; exact h
  · have : 2 ^ (32 * n) ≤ 2 ^ (32 * n) * w32 m B (d + 4 * n) := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hz)
    omega_using [h, hR, this]

/-- `montCore a x y m tt len cnt`, `cnt` setting `r4` to `c` steps (`1 ≤ c ≤ w`),
`len` holding `L` (`m`'s length in bytes, `1 ≤ ⌈L / 4⌉ ≤ w`), for an odd
`mv = [m]` and `Y = [y]` below `2^(32 ⌈L / 4⌉)`: for `Y < mv`, `[a] < mv` and
`[a] 2^(32 c) ≡ x Y (mod mv)`, `x` the low `c` digits of `[x]`. -/
theorem montCoreC_ok {s : State} {B : Addr} {Z w N a x y m tt L mv Y : Nat} (hw : Ws s B Z w N) (hN : N ≤ 256)
    (ha : a < N) (hx : x < N) (hy : y < N) (hm : m < N) (ht : tt < N) (hax : a ≠ x) (hay : a ≠ y)
    (ham : a ≠ m) (hat : a ≠ tt) (htx : tt ≠ x) (hty : tt ≠ y) (htm : tt ≠ m) {len : Reg}
    (hlen : s.gpr len = BitVec.ofNat 64 L) (hL1 : 1 ≤ L) (hLw : (L + 3) / 4 ≤ w) (hr : len ∉ mkRegs)
    (hl0 : len ≠ .r0) (hmv : val32 s.mem B (arr w m) ((L + 3) / 4 + 1) = mv)
    (hmt : mv < 2 ^ (32 * ((L + 3) / 4))) (hodd : mv % 2 = 1)
    (hY : val32 s.mem B (arr w y) ((L + 3) / 4 + 1) = Y) (hYt : Y < 2 ^ (32 * ((L + 3) / 4)))
    {c : Nat} {cnt : List Instr} (hc1 : 1 ≤ c) (hcw : c ≤ w)
    (hcnt : ∀ u : State, Keep mkRegs s u → u.gpr .r29 = BitVec.ofNat 64 w →
      WP isa (.block cnt) u fun t0 => (t0.gpr .r4 = BitVec.ofNat 64 c ∧ t0.mem = u.mem) ∧ Keep [.r4] u t0) :
    WP isa (montCore a x y m tt len cnt) s fun t => Ws t B Z w N ∧ KeyWorkspace.Keep B w [a, tt] [] s.mem t.mem ∧
      (Y < mv → num t.mem B w a < mv ∧
        num t.mem B w a * 2 ^ (32 * c) % mv = val32 s.mem B (arr w x) c * Y % mv) ∧
      Keep mkRegs s t := by
  have := hw.wle
  have := hw.wpos
  have hnw := hw.nowrap
  have hS : S w = 4 * (w + 2) := rfl
  have fa := hw.arr_fit ha
  have ft := hw.arr_fit ht
  have dat := arr_disj (w := w) hat
  simp only [S] at dat
  generalize hK : (L + 3) / 4 + 1 = K at hmv hY
  have hK' : (L + 3) / 4 = K - 1 := by omega_using [hK]
  rw [hK'] at hmt hYt
  have K2 : 2 ≤ K := by omega_using [hL1, hK]
  have Kw : K ≤ w + 1 := by omega_using [hLw, hK]
  have m0 : w32 s.mem B (arr w m) = mv % 2 ^ 32 := by
    obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega_using [hK]⟩
    rw [← hmv]; show _ = (w32 s.mem B (arr w m) + 2 ^ 32 * val32 s.mem B (arr w m + 4) k) % 2 ^ 32
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (BitVec.isLt _)]
  rw [montCore]; simp only [seqs]; rw [WP.seq_iff]
  refine WP.mono (init_ok hw hN ha hx hm ht (by rw [m0]; omega_using [hodd]) hlen (by omega_arith) hr hl0)
    fun u ⟨iv, ivl, inv, hu, u12, u10, u5, u8, u0, um, ku⟩ => ?_
  rw [hK] at u12
  rw [WP.seq_iff]
  refine WP.mono (VG.Proof.Rsa.PPC64LE.Loops.zeroLoop_ok hu.scr u5 u8 u0 (by omega_using []) (by omega_arith) (by omega_arith))
    fun v ⟨z, vout, kv⟩ => ?_
  have hv := hu.of_keep kv
  rw [WP.seq_iff]
  refine WP.mono (hcnt v ((ku.trans kv).mono (by decide)) hv.r29) fun t0 ⟨⟨a4, am⟩, k0⟩ => ?_
  have h0 := hv.of_keep k0
  rw [WP.seq_iff]
  have e : MEnv s B Z w N a x y m tt K iv mv Y :=
    ⟨hN, ha, hx, hy, hm, ht, hax, hay, ham, hat, htx, hty, htm, K2, Kw, hmv, hmt, by rw [← m0]; exact inv, ivl,
      hY, hYt⟩
  -- The memory before the steps.
  have mem0 : t0.mem = v.mem := am
  have zero0 : ∀ j < w + 2, w32 t0.mem B (arr w a + 4 * j) = 0 := fun j hj => by rw [mem0]; exact z j hj
  have I0 : MInv s t0 B Z w N a x tt c K iv mv Y 0 := by
    refine ⟨h0, by rw [a4, Nat.sub_zero], ?_, ?_, ?_, ?_, fun j _ hj2 => zero0 j hj2, ?_, ?_, ?_⟩
    · rw [k0.gpr _ (by decide), kv.gpr _ (by decide), u10]; rfl
    · rw [k0.gpr _ (by decide), kv.gpr _ (by decide), u12]
    · rw [mem0, vout.w32 (by omega_using [dat]) (by omega_using [hnw, hS, ft]), um, w32_write_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ivl]
    · rw [mem0]
      have wo : Outside B (arr w tt) 4 s.mem (s.mem.writeW (off B (arr w tt)) (BitVec.ofNat 32 iv)) :=
        writeW32_outside s.mem B (BitVec.ofNat 32 iv) (by omega_using [hnw, hS, ft])
      have k1 : KeyWorkspace.Keep B w [a, tt] [] s.mem u.mem := by
        rw [um]
        exact KeyWorkspace.Keep.of_arr (o := tt) (d := 0) (by simpa only [Nat.add_zero] using wo) (by omega_using [hS])
          (by simp)
      exact k1.trans (KeyWorkspace.Keep.of_arr (o := a) (d := 0) (by simpa only [Nat.add_zero] using vout)
        (by omega_using [hS]) (by simp))
    · rw [VG.Proof.Bignum.PPC64LE.val32_zero (k := K + 1) (fun j hj => by
        simpa only [Nat.add_zero] using zero0 j (by omega_using [Kw, hj]))]
      exact Nat.mul_pos (by decide) (Nat.two_pow_pos _)
    · intro hYm
      rw [VG.Proof.Bignum.PPC64LE.val32_zero (k := K + 1) (fun j hj => by
        simpa only [Nat.add_zero] using zero0 j (by omega_using [Kw, hj]))]
      refine ⟨by omega_using [hodd], ?_⟩
      simp [val32]
    · exact ((ku.trans kv).trans k0).mono (by decide)
  refine WP.mono (wp_countdown (body := montStep a y m tt) (cnt := .r4) (N := c) (by omega_arith) (by omega_using [hc1])
    (fun i t => MInv s t B Z w N a x tt c K iv mv Y i)
    (fun i hi t ht _ => step_ok e ht hi hcw) I0 a4) fun t1 h1 => ?_
  -- The final subtraction.
  have hAK : val32 t1.mem B (arr w a) (K + 1) < 2 ^ (32 * K) := Nat.lt_trans h1.bound (three_lt (by omega_using [hK]))
  have mv1 : val32 t1.mem B (arr w m) K = mv := by rw [e.rd h1.ws h1.keep hm ham htm (by omega_using [hLw, hK])]; exact hmv
  refine WP.mono (final_ok h1.ws hN ha hm ht ham hat htm (by omega_using [hK]) Kw h1.r12 rfl hAK mv1)
    fun t ⟨ht', kt, Kt, digs, vR⟩ => ⟨ht', h1.keep.trans Kt, fun hYm => ?_, h1.regs.trans' (kt.mono (by decide))⟩
  obtain ⟨b2, cg⟩ := h1.cong hYm
  generalize hA : val32 t1.mem B (arr w a) (K + 1) = A at b2 cg vR hAK
  have hR : (if mv ≤ A then A - mv else A) = A % mv := by
    split
    · rw [Nat.mod_eq_sub_mod (by assumption), Nat.mod_eq_of_lt (by omega_using [b2])]
    · rw [Nat.mod_eq_of_lt (by omega_arith)]
  rw [hR] at vR
  have Rlt : A % mv < mv := Nat.mod_lt _ (by omega_using [hodd])
  have aK : w32 t1.mem B (arr w a + 4 * K) = 0 := top_zero (hA ▸ hAK)
  have vW : val32 t.mem B (arr w a) (w + 1) = A % mv :=
    val32_ext_zero vR Kw fun j hj1 hj2 => by
      rw [digs j hj1 (by omega_using [hj2])]
      rcases Nat.eq_or_lt_of_le hj1 with e | e
      · rw [← e]; exact aK
      · exact h1.top j (by omega_using [e]) (by omega_using [hj2])
  have Rw : A % mv < 2 ^ (32 * w) :=
    Nat.lt_of_lt_of_le Rlt (Nat.le_trans (Nat.le_of_lt hmt) (Nat.pow_le_pow_right (by decide) (by omega_using [hLw, hK])))
  have nm : num t.mem B w a = A % mv := val32_drop_top vW Rw
  refine ⟨by rw [nm]; exact Rlt, ?_⟩
  rw [nm, Nat.mod_mul_mod, cg]

/-- `cntLen len`: `⌈L / 4⌉` into `r4`, `len` holding `L`. -/
theorem cntLen_ok {u : State} {len : Reg} {L : Nat} (hl0 : len ≠ .r0) (hlen : u.gpr len = BitVec.ofNat 64 L)
    (hL : L < 2 ^ 32) :
    WP isa (.block (cntLen len)) u fun t0 =>
      (t0.gpr .r4 = BitVec.ofNat 64 ((L + 3) / 4) ∧ t0.mem = u.mem) ∧ Keep [.r4] u t0 :=
  WP.keep [.r4] (Q := fun t0 => t0.gpr .r4 = BitVec.ofNat 64 ((L + 3) / 4) ∧ t0.mem = u.mem) (by
    prun [cntLen, gpr_write, exec_addi hl0 (show 3 < 2 ^ 15 by decide), hlen]
    exact shr2_ofNat (by omega_using [hL])) (by cases len <;> decide)

/-- `montCore a x y m tt len cntW`, `len` holding `L` (`m`'s length in bytes,
`1 ≤ ⌈L / 4⌉ ≤ w`), for an odd `mv = [m]` and `Y = [y]` below
`2^(32 ⌈L / 4⌉)`: for `Y < mv`, `[a] < mv` and `[a] 2^(32 w) ≡ [x] Y (mod mv)`. -/
theorem montCore_ok {s : State} {B : Addr} {Z w N a x y m tt L mv Y : Nat} (hw : Ws s B Z w N) (hN : N ≤ 256)
    (ha : a < N) (hx : x < N) (hy : y < N) (hm : m < N) (ht : tt < N) (hax : a ≠ x) (hay : a ≠ y)
    (ham : a ≠ m) (hat : a ≠ tt) (htx : tt ≠ x) (hty : tt ≠ y) (htm : tt ≠ m) {len : Reg}
    (hlen : s.gpr len = BitVec.ofNat 64 L) (hL1 : 1 ≤ L) (hLw : (L + 3) / 4 ≤ w) (hr : len ∉ mkRegs)
    (hl0 : len ≠ .r0) (hmv : val32 s.mem B (arr w m) ((L + 3) / 4 + 1) = mv)
    (hmt : mv < 2 ^ (32 * ((L + 3) / 4))) (hodd : mv % 2 = 1)
    (hY : val32 s.mem B (arr w y) ((L + 3) / 4 + 1) = Y) (hYt : Y < 2 ^ (32 * ((L + 3) / 4))) :
    WP isa (montCore a x y m tt len cntW) s fun t => Ws t B Z w N ∧ KeyWorkspace.Keep B w [a, tt] [] s.mem t.mem ∧
      (Y < mv → num t.mem B w a < mv ∧ num t.mem B w a * 2 ^ (32 * w) % mv = num s.mem B w x * Y % mv) ∧
      Keep mkRegs s t :=
  montCoreC_ok hw hN ha hx hy hm ht hax hay ham hat htx hty htm hlen hL1 hLw hr hl0 hmv hmt hodd hY hYt
    (Nat.le_trans (by omega_using [hL1]) hLw) (Nat.le_refl _) fun _ _ h29 =>
      WP.keep [.r4] (Q := fun t0 => t0.gpr .r4 = BitVec.ofNat 64 w ∧ t0.mem = _)
        (by prun [cntW, h29, BitVec.add_zero]) (by decide)

/-- The low `K` digits of a number below `2^(32 K)`. -/
theorem val32_low {m : Mem} {B : Addr} {d n K R : Nat} (h : val32 m B d n = R) (hK : K ≤ n)
    (hR : R < 2 ^ (32 * K)) : val32 m B d K = R := by
  have := val32_append m B d K (n - K)
  rw [show K + (n - K) = n by omega_using [hK], h] at this
  have hl := val32_lt m B d K
  by_cases hz : val32 m B (d + 4 * K) (n - K) = 0
  · rw [hz, Nat.mul_zero, Nat.add_zero] at this; exact this.symm
  · have : 2 ^ (32 * K) ≤ 2 ^ (32 * K) * val32 m B (d + 4 * K) (n - K) :=
      Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hz)
    omega_arith

theorem off_add (B : Addr) (a b : Nat) : off B a + BitVec.ofNat 64 b = off B (a + b) := by
  simp only [off, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- `montTops`: digit `w` of `[m]` and of `[y]` zeroed. -/
theorem tops_ok {s : State} {B : Addr} {Z w N m y : Nat} (hw : Ws s B Z w N) (hN : N ≤ 256) (hm : m < N)
    (hy : y < N) (hmy : m ≠ y) :
    WP isa (.block (montTops m y)) s fun u => Ws u B Z w N ∧ Keep [.r0, .r3, .r5] s u ∧
      KeyWorkspace.Keep B w [m, y] [] s.mem u.mem ∧ num u.mem B w m = num s.mem B w m ∧
      num u.mem B w y = num s.mem B w y ∧ w32 u.mem B (arr w m + 4 * w) = 0 ∧
      w32 u.mem B (arr w y + 4 * w) = 0 := by
  have := hw.wle
  have hnw := hw.nowrap
  have hS : S w = 4 * (w + 2) := rfl
  have fm := hw.arr_fit hm
  have fy := hw.arr_fit hy
  have dmy := arr_disj (w := w) hmy
  simp only [S] at dmy
  have e4 : BitVec.ofNat 64 w <<< 2 = BitVec.ofNat 64 (4 * w) := shl2_ofNat w
  simp only [montTops, List.append_assoc]
  refine ptr_ok hw (r := .r5) (by decide) (by decide) (by decide) (show m < 2 ^ 15 by omega_using [hN, hm]) ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r0, .r3, .r5] (Q := fun u => u.mem = s.mem.writeW (off B (arr w m + 4 * w)) 0#32 ∧
      u.gpr .r0 = BitVec.ofNat 64 (4 * w) ∧ u.gpr .r3 = 0) (by
        prun [gpr_write, mem_write, hw.r29, e4, off_add, hw.scr.st (show arr w m + 4 * w + 4 ≤ Z by omega_using [hS, fm])]
        exact ⟨rfl, rfl⟩) (by decide))
    fun u1 ⟨⟨m1, r0, r3⟩, k1⟩ => ?_
  have h1 := (hw.of_keep (Keep.write _ .r5 _)).of_keep k1
  refine ptr_ok h1 (r := .r5) (by decide) (by decide) (by decide) (show y < 2 ^ 15 by omega_using [hN, hy]) ?_
  refine WP.mono (WP.keep [.r5] (Q := fun u => u.mem = u1.mem.writeW (off B (arr w y + 4 * w)) 0#32) (by
      prun [gpr_write, mem_write, r0, r3, off_add, h1.scr.st (show arr w y + 4 * w + 4 ≤ Z by omega_using [hS, fy])]; rfl)
      (by decide))
    fun u ⟨mu, ku⟩ => ?_
  have o1 : Outside B (arr w m + 4 * w) 4 s.mem u1.mem := by rw [m1]; exact writeW32_outside _ B _ (by omega_using [hnw, hS, fm])
  have o2 : Outside B (arr w y + 4 * w) 4 u1.mem u.mem := by rw [mu]; exact writeW32_outside _ B _ (by omega_using [hnw, hS, fy])
  refine ⟨(h1.of_keep (Keep.write _ .r5 _)).of_keep ku, (((Keep.write _ .r5 _).trans k1).trans
    ((Keep.write _ .r5 _).trans ku)).mono (by decide), ?_, ?_, ?_, ?_, ?_⟩
  · exact (KeyWorkspace.Keep.of_arr (o := m) (d := 4 * w) o1 (by simp only [S]; omega_using []) (by simp)).trans
      (KeyWorkspace.Keep.of_arr (o := y) (d := 4 * w) o2 (by simp only [S]; omega_using []) (by simp))
  · show val32 u.mem B (arr w m) w = val32 s.mem B (arr w m) w
    rw [o2.val32 (by omega_using [dmy]) (by omega_using [hnw, hS, fm]), o1.val32 (by omega_using []) (by omega_using [hnw, hS, fm])]
  · show val32 u.mem B (arr w y) w = val32 s.mem B (arr w y) w
    rw [o2.val32 (by omega_using []) (by omega_using [hnw, hS, fy]), o1.val32 (by omega_using [dmy]) (by omega_using [hnw, hS, fy])]
  · rw [o2.w32 (by omega_using [dmy]) (by omega_using [hnw, hS, fm]), m1, w32_write_self]; rfl
  · rw [mu, w32_write_self]; rfl

/-- `montMul a x y m tt len cnt`, `cnt` setting `r4` to `c` steps (`1 ≤ c ≤ w`)
for `[x] < 2^(32 c)`, `len` holding `L` (`m`'s length in bytes,
`1 ≤ ⌈L / 4⌉ ≤ w`), for an odd `mv = [m]` and `Y = [y]` below
`2^(32 ⌈L / 4⌉)`: for `Y < mv`, `[a] < mv` and `[a] 2^(32 c) ≡ [x] Y (mod mv)`;
`[m]` and `[y]` keep their values (their digit `w` is zeroed). -/
theorem montMulC_ok {s : State} {B : Addr} {Z w N a x y m tt L mv Y : Nat} (hw : Ws s B Z w N) (hN : N ≤ 256)
    (ha : a < N) (hx : x < N) (hy : y < N) (hm : m < N) (ht : tt < N) (hax : a ≠ x) (hay : a ≠ y)
    (ham : a ≠ m) (hat : a ≠ tt) (htx : tt ≠ x) (hty : tt ≠ y) (htm : tt ≠ m) (hmy : m ≠ y) {len : Reg}
    (hlen : s.gpr len = BitVec.ofNat 64 L) (hL1 : 1 ≤ L) (hLw : (L + 3) / 4 ≤ w) (hr : len ∉ mkRegs)
    (hl0 : len ≠ .r0) (hmv : num s.mem B w m = mv) (hmt : mv < 2 ^ (32 * ((L + 3) / 4))) (hodd : mv % 2 = 1)
    (hY : num s.mem B w y = Y) (hYt : Y < 2 ^ (32 * ((L + 3) / 4)))
    {c : Nat} {cnt : List Instr} (hc1 : 1 ≤ c) (hcw : c ≤ w) (hX : num s.mem B w x < 2 ^ (32 * c))
    (hcnt : ∀ u : State, Keep mkRegs s u → u.gpr .r29 = BitVec.ofNat 64 w →
      WP isa (.block cnt) u fun t0 => (t0.gpr .r4 = BitVec.ofNat 64 c ∧ t0.mem = u.mem) ∧ Keep [.r4] u t0) :
    WP isa (montMul a x y m tt len cnt) s fun t => Ws t B Z w N ∧
      KeyWorkspace.Keep B w [a, tt, m, y] [] s.mem t.mem ∧ num t.mem B w m = mv ∧ num t.mem B w y = Y ∧
      w32 t.mem B (arr w m + 4 * w) = 0 ∧
      (Y < mv → num t.mem B w a < mv ∧ num t.mem B w a * 2 ^ (32 * c) % mv = num s.mem B w x * Y % mv) ∧
      Keep mkRegs s t := by
  have := hw.wle
  have hS : S w = 4 * (w + 2) := rfl
  rw [montMul, WP.seq_iff]
  refine WP.mono (tops_ok hw hN hm hy hmy) fun u ⟨hu, ku, Ku, num_m, num_y, tm, ty⟩ => ?_
  have K1 : (L + 3) / 4 + 1 ≤ w + 1 := by omega_using [hLw]
  have toK : ∀ {j R : Nat}, num u.mem B w j = R → w32 u.mem B (arr w j + 4 * w) = 0 →
      R < 2 ^ (32 * ((L + 3) / 4)) → val32 u.mem B (arr w j) ((L + 3) / 4 + 1) = R := fun {j R} e z lt => by
    have e1 : val32 u.mem B (arr w j) (w + 1) = R := by rw [val32_succ, z, Nat.mul_zero, Nat.add_zero]; exact e
    exact val32_low e1 K1 (Nat.lt_of_lt_of_le lt (Nat.pow_le_pow_right (by decide) (by omega_using [])))
  have n3 : len ∉ [.r0, .r3, .r5] := fun hm' => hr (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm' ⊢; rcases hm' with e | e | e <;> simp [e])
  have ul : u.gpr len = BitVec.ofNat 64 L := by rw [ku.gpr _ n3]; exact hlen
  have hx' : num u.mem B w x = num s.mem B w x := by
    by_cases e1 : x = m
    · rw [e1, num_m, hmv, ← hmv, ← e1]
    · by_cases e2 : x = y
      · rw [e2, num_y]
      · exact keep_val Ku (by omega_using []) (by
          intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz; rcases hz with rfl | rfl <;> omega_arith)
          (by simp) (hw.fit64 hx)
  have xc : val32 u.mem B (arr w x) c = num s.mem B w x := val32_low hx' hcw hX
  refine WP.mono (montCoreC_ok hu hN ha hx hy hm ht hax hay ham hat htx hty htm ul hL1 hLw hr hl0
    (toK (num_m.trans hmv) tm hmt) hmt hodd (toK (num_y.trans hY) ty hYt) hYt hc1 hcw
    fun v kv h29 => hcnt v ((ku.trans kv).mono (by decide)) h29)
    fun t ⟨ht', Kt, cg, kt⟩ => ⟨ht', ?_, ?_, ?_, ?_, fun hYm => by rw [← xc]; exact cg hYm,
      (ku.trans kt).mono (by decide)⟩
  · exact (Ku.mono (by simp)).trans (Kt.mono (by simp))
  · show val32 t.mem B (arr w m) w = mv
    rw [keep_val Kt (by omega_using []) (by
      intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz; rcases hz with rfl | rfl <;> omega_arith)
      (by simp) (hw.fit64 hm)]
    exact num_m.trans hmv
  · show val32 t.mem B (arr w y) w = Y
    rw [keep_val Kt (by omega_using []) (by
      intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz; rcases hz with rfl | rfl <;> omega_arith)
      (by simp) (hw.fit64 hy)]
    exact num_y.trans hY
  · have := keep_word (b := 32) (o := 4 * w) Kt (j := m) (by simp only [S]; omega_using []) (by
      intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz; rcases hz with rfl | rfl <;> omega_arith)
      (by simp) (hw.fit64 hm)
    rw [show w32 t.mem B (arr w m + 4 * w) = w32 u.mem B (arr w m + 4 * w) from congrArg BitVec.toNat this, tm]

/-- `montMul a x y m tt len cntW`, `len` holding `L` (`m`'s length in bytes,
`1 ≤ ⌈L / 4⌉ ≤ w`), for an odd `mv = [m]` and `Y = [y]` below
`2^(32 ⌈L / 4⌉)`: for `Y < mv`, `[a] < mv` and `[a] 2^(32 w) ≡ [x] Y (mod mv)`;
`[m]` and `[y]` keep their values (their digit `w` is zeroed). -/
theorem montMul_ok {s : State} {B : Addr} {Z w N a x y m tt L mv Y : Nat} (hw : Ws s B Z w N) (hN : N ≤ 256)
    (ha : a < N) (hx : x < N) (hy : y < N) (hm : m < N) (ht : tt < N) (hax : a ≠ x) (hay : a ≠ y)
    (ham : a ≠ m) (hat : a ≠ tt) (htx : tt ≠ x) (hty : tt ≠ y) (htm : tt ≠ m) (hmy : m ≠ y) {len : Reg}
    (hlen : s.gpr len = BitVec.ofNat 64 L) (hL1 : 1 ≤ L) (hLw : (L + 3) / 4 ≤ w) (hr : len ∉ mkRegs)
    (hl0 : len ≠ .r0) (hmv : num s.mem B w m = mv) (hmt : mv < 2 ^ (32 * ((L + 3) / 4))) (hodd : mv % 2 = 1)
    (hY : num s.mem B w y = Y) (hYt : Y < 2 ^ (32 * ((L + 3) / 4))) :
    WP isa (montMul a x y m tt len cntW) s fun t => Ws t B Z w N ∧
      KeyWorkspace.Keep B w [a, tt, m, y] [] s.mem t.mem ∧ num t.mem B w m = mv ∧ num t.mem B w y = Y ∧
      w32 t.mem B (arr w m + 4 * w) = 0 ∧
      (Y < mv → num t.mem B w a < mv ∧ num t.mem B w a * 2 ^ (32 * w) % mv = num s.mem B w x * Y % mv) ∧
      Keep mkRegs s t :=
  montMulC_ok hw hN ha hx hy hm ht hax hay ham hat htx hty htm hmy hlen hL1 hLw hr hl0 hmv hmt hodd hY hYt
    (Nat.le_trans (by omega_using [hL1]) hLw) (Nat.le_refl _) (val32_lt _ _ _ _) fun _ _ h29 =>
      WP.keep [.r4] (Q := fun t0 => t0.gpr .r4 = BitVec.ofNat 64 w ∧ t0.mem = _)
        (by prun [cntW, h29, BitVec.add_zero]) (by decide)

end VG.Proof.Rsa.PPC64LE.MontKey
