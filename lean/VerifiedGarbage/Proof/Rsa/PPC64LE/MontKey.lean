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
open VG.Proof.Rsa.KeyWorkspace (arr S num arr_disj)

/-- The registers the products change. -/
abbrev mkRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12]

theorem off_shift (B : Addr) (o x i : Nat) :
    off B o + (off B (x + 4 * i) - off B x) = off B (o + 4 * i) := by
  simp only [off, BitVec.ofNat_add]
  rw [show B + (BitVec.ofNat 64 x + BitVec.ofNat 64 (4 * i)) - (B + BitVec.ofNat 64 x) =
    BitVec.ofNat 64 (4 * i) by bv_omega]
  ac_rfl

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
    have := keep_word (b := 32) (o := 4 * i) h.keep (j := x) (by simp only [S]; omega)
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
        prun [h.r10, BitVec.add_zero, hw.scr.ld (show arr w x + 4 * i + 4 ≤ Z by omega)]
        rw [BitVec.toNat_setWidth, ← xi]; exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide))) (by decide))
      fun u1 ⟨⟨a11, am⟩, k1⟩ => ?_
    have h1 := hw.of_keep k1
    refine ptr_ok h1 (r := .r5) (by decide) (by decide) (by decide) (show o < 2 ^ 15 by omega) ?_
    refine ptr_ok (h1.of_keep (Keep.write _ _ _)) (r := .r6) (by decide) (by decide) (by decide)
      (show x < 2 ^ 15 by omega) ?_
    rw [WP.block_append_iff]
    have u10 : u1.gpr .r10 = off B (arr w x + 4 * i) := (k1.gpr _ (by decide)).trans h.r10
    refine WP.mono (WP.keep [.r5, .r6] (Q := fun u => u.gpr .r5 = off B (arr w o + 4 * i) ∧
      u.gpr .r6 = off B (arr w o + 4 * i) ∧ u.mem = u1.mem) (by
        prun [gpr_write, mem_write, u10, BitVec.add_zero]
        rw [off_shift]) (by decide)) fun u2 ⟨⟨b5, b6, bm⟩, k2⟩ => ?_
    have h2 := (h1.of_keep ((Keep.write _ .r5 _).trans (Keep.write _ .r6 _))).of_keep k2
    refine ptr_ok h2 (r := .r7) (by decide) (by decide) (by decide) (show y < 2 ^ 15 by omega) ?_
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
    (by omega) (by omega) (by omega) (by omega) (by omega) (Or.inl (Nat.le_refl _))
    (by unfold Ahead; omega)) fun v ⟨_, veq, _, vout, kv⟩ => ?_
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
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  · rw [e10, v10, h.r10]; simp only [off, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2
  · rw [e12, v12, h.r12]; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  · rw [em]
    exact h.keep.trans (KeyWorkspace.Keep.of_arr (d := 4 * i) vout (by omega) (by simp))
  · -- The row's arithmetic.
    rw [em]
    have split : ∀ (m : Mem) (d : Nat), val32 m B d w =
        val32 m B d i + 2 ^ (32 * i) * val32 m B (d + 4 * i) (w - i) := fun m d => by
      have := val32_append m B d i (w - i); rwa [show i + (w - i) = w by omega] at this
    have lo : val32 v.mem B (arr w o) i = val32 t.mem B (arr w o) i :=
      vout.val32 (Or.inl (Nat.le_refl _)) (by omega)
    have ys : val32 t.mem B (arr w y) w = num s.mem B w y := by
      rw [keep_val h.keep (by omega) (by simp only [List.mem_singleton]; exact fun _ e => e ▸ hoy) (by simp) (hw.fit64 hy)]
    have yk : val32 t.mem B (arr w y) (w - i) % 2 ^ (32 * (w - i)) = num s.mem B w y % 2 ^ (32 * (w - i)) := by
      have := val32_append t.mem B (arr w y) (w - i) i
      rw [show w - i + i = w by omega, ys] at this
      rw [this, Nat.add_mul_mod_self_left]
    have row := VG.Proof.Rsa.mulLo_row (P := 2 ^ (32 * i)) (Q := 2 ^ (32 * (w - i)))
      (L := val32 t.mem B (arr w o) i) (H := val32 t.mem B (arr w o + 4 * i) (w - i))
      (H' := val32 v.mem B (arr w o + 4 * i) (w - i)) (x := w32 s.mem B (arr w x + 4 * i))
      (Y := num s.mem B w y) (Nat.two_pow_pos _) (val32_lt _ _ _ _) (val32_lt _ _ _ _) veq yk
    have W : 2 ^ (32 * i) * 2 ^ (32 * (w - i)) = 2 ^ (32 * w) := by
      rw [← Nat.pow_add]; congr 1; omega
    show val32 v.mem B (arr w o) w = _
    rw [split, lo, row, ← split, W]
    show (num t.mem B w o + _) % _ = _
    rw [h.val, val32_succ, ← xi, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_mul, Nat.mul_assoc]

theorem shr2_ofNat {L : Nat} (hL : L + 3 < 2 ^ 64) :
    (BitVec.ofNat 64 L + BitVec.ofNat 64 3) >>> 2 = BitVec.ofNat 64 ((L + 3) / 4) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- `mulLo o x y len`, `len` holding `L` with `1 ≤ L ≤ 4 w`: `[o] := [x] [y]
mod 2^(32 w)` over the `⌈L / 4⌉` low digits of `[x]`. -/
theorem mulLo_ok {s : State} {B : Addr} {Z w N o x y L : Nat} (h : Ws s B Z w N) (hN : N ≤ 256) (ho : o < N)
    (hx : x < N) (hy : y < N) (hox : o ≠ x) (hoy : o ≠ y) {len : Reg} (hlen : s.gpr len = BitVec.ofNat 64 L)
    (hL1 : 1 ≤ L) (hLw : L ≤ 4 * w) (hr : len ∉ mkRegs) (hl0 : len ≠ .r0) :
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
    refine ptr_ok h (r := .r5) (by decide) (by decide) (by decide) (show o < 2 ^ 15 by omega) ?_
    refine WP.mono (WP.keep [.r0, .r8] (Q := fun u => u.gpr .r8 = BitVec.ofNat 64 w ∧ u.gpr .r0 = 0 ∧
      u.mem = s.mem) (by prun [gpr_write, mem_write, h.r29, BitVec.add_zero]; rfl) (by decide))
      fun u ⟨⟨u8, u0, um⟩, ku⟩ => ⟨by rw [ku.gpr _ (by decide)]; simp [gpr_write], u8, u0, um,
        ((Keep.write _ .r5 _).trans ku).mono (by decide)⟩
  refine WP.mono hb1 fun u ⟨u5, u8, u0, um, ku⟩ => ?_
  have hu := h.of_keep ku
  rw [WP.seq_iff]
  refine WP.mono (VG.Proof.Rsa.PPC64LE.Loops.zeroLoop_ok hu.scr u5 u8 u0 (by omega) (by omega) (by omega))
    fun v ⟨z, vout, kv⟩ => ?_
  have hv := hu.of_keep kv
  rw [WP.seq_iff]
  -- `x`'s pointer and the counts.
  have l1 : len ∉ [.r5, .r8] := fun hm => hr (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢; rcases hm with e | e <;> simp [e])
  have l2 : len ∉ [.r0, .r5, .r8] := fun hm => hr (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢; rcases hm with e | e | e <;> simp [e])
  have vl : v.gpr len = BitVec.ofNat 64 L := by
    rw [kv.gpr _ l1, ku.gpr _ l2]; exact hlen
  have hb2 : WP isa (.block (mulLoSet x len)) v fun u' => u'.gpr .r10 = off B (arr w x) ∧
      u'.gpr .r4 = BitVec.ofNat 64 ((L + 3) / 4) ∧ u'.gpr .r12 = BitVec.ofNat 64 w ∧ u'.mem = v.mem ∧
      Keep [.r4, .r10, .r12] v u' := by
    refine ptr_ok hv (r := .r10) (by decide) (by decide) (by decide) (show x < 2 ^ 15 by omega) ?_
    have l10 : len ≠ .r10 := fun e => hr (by simp [e])
    refine WP.mono (WP.keep [.r4, .r12] (Q := fun u' => u'.gpr .r4 = BitVec.ofNat 64 ((L + 3) / 4) ∧
      u'.gpr .r12 = BitVec.ofNat 64 w ∧ u'.mem = v.mem) (by
        prun [exec_addi hl0 (show 3 < 2 ^ 15 by decide), gpr_write, mem_write, l10, vl, hv.r29, BitVec.add_zero,
          shr2_ofNat (show L + 3 < 2 ^ 64 by omega)]) (by rfl))
      fun u' ⟨⟨a4, a12, am⟩, ka⟩ => ⟨by rw [ka.gpr _ (by decide)]; simp [gpr_write], a4, a12, am,
        ((Keep.write _ .r10 _).trans ka).mono (by decide)⟩
  refine WP.mono hb2 fun t0 ⟨a10, a4, a12, am, kt0⟩ => ?_
  have ht0 := hv.of_keep kt0
  have c1 : 1 ≤ (L + 3) / 4 := by omega
  have cw : (L + 3) / 4 ≤ w := by omega
  have I0 : LoInv s t0 B Z w N o x y ((L + 3) / 4) 0 := by
    refine ⟨ht0, by rw [a4, Nat.sub_zero], by rw [a10]; rfl, by rw [a12, Nat.sub_zero], ?_, ?_, ?_⟩
    · rw [am, ← um]
      exact KeyWorkspace.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using vout) (by omega) (by simp)
    · have z0 : num v.mem B w o = 0 :=
        VG.Proof.Bignum.PPC64LE.val32_zero (k := w) (fun j hj => by simpa only [Nat.add_zero] using z j hj)
      rw [am, z0, val32, Nat.zero_mul, Nat.zero_mod]
    · exact ((ku.trans kv).trans kt0).mono (by decide)
  refine WP.mono (wp_countdown (body := mulLoRow o x y) (cnt := .r4) (N := (L + 3) / 4) (by omega) c1
    (fun i t => LoInv s t B Z w N o x y ((L + 3) / 4) i)
    (fun i hi t ht _ => row_ok hN ho hx hy hox hoy hi cw ht) I0 a4)
    fun t ht => ⟨ht.ws, ht.keep, ht.val, ht.regs⟩

end VG.Proof.Rsa.PPC64LE.MontKey
