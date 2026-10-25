module

import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.DdLoop
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Lane
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Narrow
public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Dd4
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.DdSplit
public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Dword
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.DdStore
public import VerifiedGarbage.Proof.MlKem.AArch64.Common
public import VerifiedGarbage.Impl.MlKem1024.AArch64.Compress
import VerifiedGarbage.Proof.Rc4.AArch64.Vec

/-!
# ML-KEM-1024 on AArch64: `dd5Half`

Two groups of 40 bits, in the doublewords of a register, split into their eight values of ten bits
(`ddSplit_ok`), each split into two values of five bits (`dd5Quarter_ok`: USHR, AND, ZIP1 and ZIP2),
decompressed and stored (`dd5Half_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem1024.AArch64.CodecV

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem1024.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64
  VG.Proof.MlKem.AArch64.CodecV VG.Spec.MlKem
open VG.Proof.MlKem.AArch64.DD (wp_strq2 vword_G)

/-- The value of five bits `m` of two groups of 40 bits. -/
abbrev dig5 (Gv : Nat → Nat) (m : Nat) : Nat := Gv (m / 8) / 2 ^ (5 * (m % 8)) % 2 ^ 5

/-- The values of five bits of four values `P` of ten bits, in order. -/
abbrev pair5 (P : Nat → Nat) (i : Nat) : Nat := P (i / 2) / 2 ^ (5 * (i % 2)) % 2 ^ 5

theorem dd5Quarter_ok {s : State} {a : VReg} (ha : a = .v2 ∨ a = .v3) {o : Nat}
    (ho : o % 16 = 0 ∧ o + 16 < 4096 * 16) (hc : DConsts 5 s) (h22 : Lanes (s.v .v22) fun _ => 2 ^ 5 - 1)
    {P : Nat → Nat} (hP : Lanes (s.v a) P) (hPl : ∀ e < 4, P e < 2 ^ 10)
    {p : Addr} {m₀ : Mem} {t : Nat} {Gf old : Nat → BitVec 32} {is : List Instr} {Q : State → Prop}
    (hw : ∀ i, i + 4 ≤ 256 → InRegions s.wr (coeffAddr p i) 16)
    (h3 : s.gpr .x3 + BitVec.ofNat 64 o = coeffAddr p t) (ht : t + 8 ≤ 256) (hcu : CoeffsUpTo s.mem p t Gf old)
    (hf : Frame [polyRegion p] m₀ s.mem)
    (hval : ∀ i < 8, Gf (t + i) = BitVec.ofNat 32 (df 5 (pair5 P i)))
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r, r ≠ a → r ≠ .v0 → r ≠ .v1 → s'.v r = s.v r) →
      CoeffsUpTo s'.mem p (t + 8) Gf old → Frame [polyRegion p] m₀ s'.mem → WP isa (.block is) s' Q) :
    WP isa (.block (dd5Quarter a o ++ is)) s Q := by
  have a0 : a ≠ .v0 := by rcases ha with rfl | rfl <;> decide
  have a1 : a ≠ .v1 := by rcases ha with rfl | rfl <;> decide
  have a16 : a ≠ .v16 := by rcases ha with rfl | rfl <;> decide
  have a17 : a ≠ .v17 := by rcases ha with rfl | rfl <;> decide
  have a22 : a ≠ .v22 := by rcases ha with rfl | rfl <;> decide
  unfold dd5Quarter
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine wp_vop (eval_shift (by decide)) fun s1 h1 => wp_vop rfl fun s2 h2 => wp_vop rfl fun s3 h3' =>
    wp_vop rfl fun s4 h4 => wp_nil ?_
  have L1 : Lanes (s1.v .v1) fun e => P e / 2 ^ 5 := by rw [h1.v]; exact lanes_ushr hP 5 _
  have L2 : Lanes (s2.v a) fun e => P e % 2 ^ 5 := by
    rw [h2.v]
    exact lanes_mask (lanes_get h1 a1 hP) (by rw [h1.get .v22 (by decide)]; exact h22)
  -- the values in order: `pair5 P i` for `i < 4` in `v0`, `4 ≤ i < 8` in `a`
  have hi : ∀ i < 8, (if i % 2 = 0 then P (i / 2) % 2 ^ 5 else P (i / 2) / 2 ^ 5) = pair5 P i := fun i hi8 => by
    have := hPl (i / 2) (by omega_arith)
    simp only [pair5]
    rcases Nat.mod_two_eq_zero_or_one i with h | h
    · rw [ite_eq_left h, h, Nat.mul_zero, Nat.pow_zero, Nat.div_one]
    · rw [ite_eq_right (by omega_arith), h, Nat.mul_one]; omega_arith
  have L3 : Lanes (s3.v .v0) fun e => pair5 P e := fun e he => by
    rw [h3'.v, vword_zip1_s4' _ _ he]
    show _ = pair5 P e
    rw [← hi e (by omega_arith)]
    split
    · exact L2 _ (by omega_arith)
    · rw [h2.get .v1 (Ne.symm a1)]; exact L1 _ (by omega_arith)
  have L4 : Lanes (s4.v a) fun e => pair5 P (4 + e) := fun e he => by
    rw [h4.v, vword_zip2_s4 _ _ he]
    show _ = pair5 P (4 + e)
    rw [← hi (4 + e) (by omega_arith), h3'.get a a0, h3'.get .v1 (by decide),
      h2.get .v1 (Ne.symm a1), show (4 + e) / 2 = 2 + e / 2 by omega_arith, show (4 + e) % 2 = e % 2 by omega_arith]
    split
    · exact L2 _ (by omega_arith)
    · exact L1 _ (by omega_arith)
  have c4 : VChg [.v1, a, .v0, a] s s4 := ((h1.chg.trans h2.chg).trans h3'.chg).trans h4.chg
  have cs4 : DConsts 5 s4 := hc.chg c4 (by simp [Ne.symm a16]) (by simp [Ne.symm a17])
  have plt : ∀ i, pair5 P i < 2 ^ 5 := fun i => Nat.mod_lt _ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (decV_ok (v := .v0) (by decide) (by decide) cs4.q cs4.h (by decide)
    (Lanes.chg h4.chg (by simp [Ne.symm a0]) L3)
    fun e _ => plt e) fun b1 ⟨d1, r0⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (decV_ok (v := a) (by decide) (by decide) (cs4.chg d1).q (cs4.chg d1).h a17
    (Lanes.chg d1 (by simp [a0]) L4) fun e _ => plt _) fun b2 ⟨d2, ra⟩ => ?_
  have c := c4.trans (d1.trans d2)
  simp only [List.cons_append, List.nil_append]
  refine wp_strq2 (by rw [c.wr]; exact hw) (by rw [c.gpr]; exact h3) ho ht (by rw [c.mem]; exact hcu)
    (by rw [c.mem]; exact hf)
    (vword_G (Lanes.chg d2 (by simp [Ne.symm a0]) r0) fun e he => by rw [hval e (by omega_arith)])
    (vword_G ra fun e he => by rw [Nat.add_assoc, hval (4 + e) (by omega_arith)])
    fun s' st o f => k s' (by rw [st.gpr, c.gpr]) (by rw [st.rd, c.rd]) (by rw [st.wr, c.wr])
      (by rw [st.sp, c.sp]) (fun r x y z => by rw [st.v, c.v r (by simp [x, y, z])]) o f

theorem dd5Half_ok {s : State} {g : VReg} (hg : g = .v6 ∨ g = .v7) {o : Nat}
    (ho : o % 16 = 0 ∧ o + 48 < 4096 * 16) (hc : DConsts 5 s)
    (h18 : Lanes (s.v .v18) fun _ => 2 ^ 20 - 1) (h19 : Lanes (s.v .v19) fun _ => 2 ^ 10 - 1)
    (h22 : Lanes (s.v .v22) fun _ => 2 ^ 5 - 1)
    {Gv : Nat → Nat} (hG : DLanes (s.v g) Gv)
    {p : Addr} {m₀ : Mem} {t : Nat} {Gf old : Nat → BitVec 32} {is : List Instr} {Q : State → Prop}
    (hw : ∀ i, i + 4 ≤ 256 → InRegions s.wr (coeffAddr p i) 16)
    (h3 : s.gpr .x3 + BitVec.ofNat 64 o = coeffAddr p t) (ht : t + 16 ≤ 256) (hcu : CoeffsUpTo s.mem p t Gf old)
    (hf : Frame [polyRegion p] m₀ s.mem)
    (hval : ∀ m < 16, Gf (t + m) = BitVec.ofNat 32 (df 5 (dig5 Gv m)))
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r, r ≠ g → r ≠ .v0 → r ≠ .v1 → r ≠ .v2 → r ≠ .v3 → s'.v r = s.v r) →
      CoeffsUpTo s'.mem p (t + 16) Gf old → Frame [polyRegion p] m₀ s'.mem → WP isa (.block is) s' Q) :
    WP isa (.block (dd5Half g o ++ is)) s Q := by
  have g0 : g ≠ .v0 := by rcases hg with rfl | rfl <;> decide
  have g1 : g ≠ .v1 := by rcases hg with rfl | rfl <;> decide
  have g2 : g ≠ .v2 := by rcases hg with rfl | rfl <;> decide
  have g3 : g ≠ .v3 := by rcases hg with rfl | rfl <;> decide
  have g16 : g ≠ .v16 := by rcases hg with rfl | rfl <;> decide
  have g17 : g ≠ .v17 := by rcases hg with rfl | rfl <;> decide
  have g18 : g ≠ .v18 := by rcases hg with rfl | rfl <;> decide
  have g19 : g ≠ .v19 := by rcases hg with rfl | rfl <;> decide
  have g22 : g ≠ .v22 := by rcases hg with rfl | rfl <;> decide
  unfold dd5Half
  simp only [List.append_assoc]
  refine ddSplit_ok (b := 10) (.inl rfl) h18 h19 hG g1 g2 g18 g19 fun a7 c7 L2 L3 => ?_
  have cs7 : DConsts 5 a7 := hc.chg c7 (by simp [g16.symm]) (by simp [g17.symm])
  have l22 : Lanes (a7.v .v22) fun _ => 2 ^ 5 - 1 := Lanes.chg c7 (by simp [g22.symm]) h22
  have dlt : ∀ m, dig 10 Gv m < 2 ^ 10 := fun m => Nat.mod_lt _ (by decide)
  -- the values of five bits of the values of ten bits
  have pq : ∀ (j : Nat) (X : Nat), j < 8 →
      (X / 2 ^ (10 * (j / 2)) % 2 ^ 10) / 2 ^ (5 * (j % 2)) % 2 ^ 5 = X / 2 ^ (5 * j) % 2 ^ 5 := by
    intro j X hj
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 by omega_arith) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega_arith
  refine dd5Quarter_ok (a := .v2) (.inl rfl) (o := o) ⟨ho.1, by omega_arith⟩ cs7 l22 L2 (fun e _ => dlt e)
    (by rw [c7.wr]; exact hw) (by rw [c7.gpr]; exact h3) (by omega_arith) (by rw [c7.mem]; exact hcu)
    (by rw [c7.mem]; exact hf)
    (fun i hi => by
      rw [hval i (by omega_arith)]
      simp only [pair5, dig, dig5]
      rw [show i / 2 / 4 = 0 by omega_arith, show i / 2 % 4 = i / 2 by omega_arith, show i / 8 = 0 by omega_arith,
        show i % 8 = i by omega_arith, pq i _ hi])
    fun s1 g1' rd1 wr1 sp1 v1 o1 f1 => ?_
  refine dd5Quarter_ok (a := .v3) (.inr rfl) (o := o + 32) ⟨by omega_arith, by omega_arith⟩
    ⟨by rw [v1 .v16 (by decide) (by decide) (by decide)]; exact cs7.q,
     by rw [v1 .v17 (by decide) (by decide) (by decide)]; exact cs7.h⟩
    (by rw [v1 .v22 (by decide) (by decide) (by decide)]; exact l22)
    (by rw [v1 .v3 (by decide) (by decide) (by decide)]; exact L3) (fun e _ => dlt _)
    (by rw [wr1, c7.wr]; exact hw)
    (by rw [g1', c7.gpr, ← ptr_add, h3]; exact coeffAddr_off _ _ 8)
    (by omega_arith) o1 f1
    (fun i hi => by
      rw [show t + 8 + i = t + (8 + i) by omega_arith, hval (8 + i) (by omega_arith)]
      simp only [pair5, dig, dig5]
      rw [show (4 + i / 2) / 4 = 1 by omega_arith, show (4 + i / 2) % 4 = i / 2 by omega_arith, show (8 + i) / 8 = 1 by omega_arith,
        show (8 + i) % 8 = i by omega_arith, pq i _ hi])
    fun s2 g2' rd2 wr2 sp2 v2 o2 f2 => ?_
  exact k s2 (by rw [g2', g1', c7.gpr]) (by rw [rd2, rd1, c7.rd]) (by rw [wr2, wr1, c7.wr])
    (by rw [sp2, sp1, c7.sp]) (fun r a b c d e => by
      rw [v2 r e b c, v1 r d b c, c7.v r (by simp [a, c, d, e])])
    (by rw [show t + 16 = t + 8 + 8 by omega_arith]; exact o2) f2

end VG.Proof.MlKem1024.AArch64.CodecV
