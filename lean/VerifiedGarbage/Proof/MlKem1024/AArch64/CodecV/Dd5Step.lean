module

public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.DdStore
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Lane
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Blocks
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Dd10Step
public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Dword
public import VerifiedGarbage.Proof.MlKem.AArch64.Common
public import VerifiedGarbage.Impl.MlKem1024.AArch64.Compress
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
import VerifiedGarbage.Proof.MlKem1024.AArch64.CodecV.Widths
public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce10

/-! ### `MlKem1024.AArch64.CodecV.Dd5`, which only this module used -/

section

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
  obtain a0 : a ≠ .v0 := by rcases ha with rfl | rfl <;> decide
  obtain a1 : a ≠ .v1 := by rcases ha with rfl | rfl <;> decide
  obtain a16 : a ≠ .v16 := by rcases ha with rfl | rfl <;> decide
  obtain a17 : a ≠ .v17 := by rcases ha with rfl | rfl <;> decide
  obtain a22 : a ≠ .v22 := by rcases ha with rfl | rfl <;> decide
  unfold dd5Quarter
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine wp_vop (eval_shift (by decide)) fun s1 h1 => wp_vop rfl fun s2 h2 => wp_vop rfl fun s3 h3' =>
    wp_vop rfl fun s4 h4 => wp_nil ?_
  obtain L1 : Lanes (s1.v .v1) fun e => P e / 2 ^ 5 := by rw [h1.v]; exact lanes_ushr hP 5 _
  obtain L2 : Lanes (s2.v a) fun e => P e % 2 ^ 5 := by
    rw [h2.v]
    exact lanes_mask (lanes_get h1 a1 hP) (by rw [h1.get .v22 (by decide)]; exact h22)
  -- the values in order: `pair5 P i` for `i < 4` in `v0`, `4 ≤ i < 8` in `a`
  obtain hi : ∀ i < 8, (if i % 2 = 0 then P (i / 2) % 2 ^ 5 else P (i / 2) / 2 ^ 5) = pair5 P i := fun i hi8 => by
    have := hPl (i / 2) (by omega_arith)
    simp only [pair5]
    rcases Nat.mod_two_eq_zero_or_one i with h | h
    · rw [ite_eq_left h, h, Nat.mul_zero, Nat.pow_zero, Nat.div_one]
    · rw [ite_eq_right (by omega_arith), h, Nat.mul_one]; omega_arith
  obtain L3 : Lanes (s3.v .v0) fun e => pair5 P e := fun e he => by
    rw [h3'.v, vword_zip1_s4' _ _ he]
    show _ = pair5 P e
    rw [← hi e (by omega_arith)]
    split
    · exact L2 _ (by omega_arith)
    · rw [h2.get .v1 (Ne.symm a1)]; exact L1 _ (by omega_arith)
  obtain L4 : Lanes (s4.v a) fun e => pair5 P (4 + e) := fun e he => by
    rw [h4.v, vword_zip2_s4 _ _ he]
    show _ = pair5 P (4 + e)
    rw [← hi (4 + e) (by omega_arith), h3'.get a a0, h3'.get .v1 (by decide),
      h2.get .v1 (Ne.symm a1), show (4 + e) / 2 = 2 + e / 2 by omega_arith, show (4 + e) % 2 = e % 2 by omega_arith]
    split
    · exact L2 _ (by omega_arith)
    · exact L1 _ (by omega_arith)
  obtain c4 : VChg [.v1, a, .v0, a] s s4 := ((h1.chg.trans h2.chg).trans h3'.chg).trans h4.chg
  obtain cs4 : DConsts 5 s4 := hc.chg c4 (by simp [Ne.symm a16]) (by simp [Ne.symm a17])
  obtain plt : ∀ i, pair5 P i < 2 ^ 5 := fun i => Nat.mod_lt _ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (decV_ok (v := .v0) (by decide) (by decide) cs4.q cs4.h (by decide)
    (Lanes.chg h4.chg (by simp [Ne.symm a0]) L3)
    fun e _ => plt e) fun b1 ⟨d1, r0⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (decV_ok (v := a) (by decide) (by decide) (cs4.chg d1).q (cs4.chg d1).h a17
    (Lanes.chg d1 (by simp [a0]) L4) fun e _ => plt _) fun b2 ⟨d2, ra⟩ => ?_
  obtain c := c4.trans (d1.trans d2)
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
  obtain g0 : g ≠ .v0 := by rcases hg with rfl | rfl <;> decide
  obtain g1 : g ≠ .v1 := by rcases hg with rfl | rfl <;> decide
  obtain g2 : g ≠ .v2 := by rcases hg with rfl | rfl <;> decide
  obtain g3 : g ≠ .v3 := by rcases hg with rfl | rfl <;> decide
  obtain g16 : g ≠ .v16 := by rcases hg with rfl | rfl <;> decide
  obtain g17 : g ≠ .v17 := by rcases hg with rfl | rfl <;> decide
  obtain g18 : g ≠ .v18 := by rcases hg with rfl | rfl <;> decide
  obtain g19 : g ≠ .v19 := by rcases hg with rfl | rfl <;> decide
  obtain g22 : g ≠ .v22 := by rcases hg with rfl | rfl <;> decide
  unfold dd5Half
  simp only [List.append_assoc]
  refine ddSplit_ok (b := 10) (.inl rfl) h18 h19 hG g1 g2 g18 g19 fun a7 c7 L2 L3 => ?_
  obtain cs7 : DConsts 5 a7 := hc.chg c7 (by simp [g16.symm]) (by simp [g17.symm])
  obtain l22 : Lanes (a7.v .v22) fun _ => 2 ^ 5 - 1 := Lanes.chg c7 (by simp [g22.symm]) h22
  obtain dlt : ∀ m, dig 10 Gv m < 2 ^ 10 := fun m => Nat.mod_lt _ (by decide)
  -- the values of five bits of the values of ten bits
  obtain pq : ∀ (j : Nat) (X : Nat), j < 8 →
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

end

end


/-!
# ML-KEM-1024 on AArch64: an iteration of `dd5Body`

Bytes `20 k … 20 k + 19` of the input, as four groups of 40 bits in doublewords (TBL, as for
`d = 10`), to coefficients `32 k … 32 k + 31` of the output.
-/

@[expose] public section

namespace VG.Proof.MlKem1024.AArch64.DD

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem1024.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64
  VG.Proof.MlKem.AArch64.CodecV VG.Proof.MlKem.AArch64.DD VG.Proof.MlKem1024.AArch64
  VG.Proof.MlKem1024.AArch64.CodecV
open VG.Spec.MlKem

/-- The constants of `dd5Body` besides those of `decV`. -/
abbrev K5 (s : State) : Prop := (Lanes (s.v .v18) fun _ => 2 ^ 20 - 1) ∧ (Lanes (s.v .v19) fun _ => 2 ^ 10 - 1) ∧
  s.v .v20 = idxVec dd10Idx ∧ s.v .v21 = idxVec dd10IdxHi ∧ (Lanes (s.v .v22) fun _ => 2 ^ 5 - 1)

/-- The bytes of a group, from its five bytes. -/
theorem num5' (s₀ : State) (g : Nat) :
    num width5 s₀ g 5 = byte width5 s₀ (5 * g) + byte width5 s₀ (5 * g + 1) * 2 ^ 8 +
      byte width5 s₀ (5 * g + 2) * 2 ^ 16 + byte width5 s₀ (5 * g + 3) * 2 ^ 24 +
      byte width5 s₀ (5 * g + 4) * 2 ^ 32 := by
  rw [num_succ, num_succ, num_succ, num_succ, num_succ, num, List.range_zero, List.map_nil, digits_nil]
  simp only [show width5.nb = 5 from rfl, Nat.add_zero]
  omega_using []

/-- Coefficient `32 k + m` of the output for `d = 5`. -/
theorem G5 (s₀ : State) {k m : Nat} (hk : k < 8) (hm : m < 32) :
    DD.G width5 s₀ (32 * k + m) = BitVec.ofNat 32 (df 5 (dig5 (fun l => num width5 s₀ (4 * k + l) 5) m)) := by
  rw [show 32 * k + m = width5.c * (4 * k + m / 8) + m % 8 by simp [width5]; omega_using [],
    G_eq width5_ok s₀ (by simp [width5]; omega_using [hk, hm]) (by simp [width5]; omega_using [])]
  simp only [show width5.d = 5 from rfl, show width5.nb = 5 from rfl, df, dig5]

theorem step5 {s₀ : State} (hp : Pre width5 s₀) {k : Nat} (hk : k < 8) {s : State}
    (h : DInv width5 4 K5 s₀ k s) :
    WP isa (.block dd5Body) s fun t =>
      DInv width5 4 K5 s₀ (k + 1) t ∧ ((t.gpr .x11).toNat ≠ 0 ↔ k + 1 ≠ 8) := by
  obtain x0 : s.gpr .x0 = bP s₀ + BitVec.ofNat 64 (20 * k) := by
    rw [h.x0, show width5.nb * 4 * k = 20 * k by simp [width5]; try omega_arith]
  unfold dd5Body
  simp only [List.cons_append, List.append_assoc]
  refine wp_ldrq (by decide) (by rw [ptr_zero, x0]) (h.in16 width5_ok hp (by simp [width5]; omega_arith))
    fun s1 h1 => ?_
  obtain in4 : InRegions (s1.rd ++ s1.wr) (bP s₀ + BitVec.ofNat 64 (20 * k + 16)) 4 := by
    rw [h1.rd, h1.wr, h.rd, h.wr, hp.rd, hp.wr]
    exact in_rd (in_regions (List.mem_singleton_self _) (contains_off (by simp [width5]; omega_arith) (by decide)))
  refine wp_scalar (is := [.ldr .w .x9 .x0 16]) (by decide) (wp_ldrw (a := bP s₀ + BitVec.ofNat 64 (20 * k + 16))
    (by decide) (by rw [h1.gpr, x0, ptr_add]) in4 fun t o e =>
      wp_nil (Q := fun t => Only [.x9] s1 t ∧ t.gpr .x9 = (s1.mem.readW (bP s₀ + BitVec.ofNat 64 (20 * k + 16)) 32).setWidth 64)
      ⟨o, e⟩) fun s2 ⟨o2, e2⟩ v2 => ?_
  refine wp_vop rfl fun s3 h3 => wp_vop rfl fun s4 h4 => wp_vop rfl fun s5 h5 => ?_
  -- the 20 bytes, as a table of two registers
  obtain tab : ∀ i < 20, (if i < 16 then vbyte (s3.v .v4) i else vbyte (s3.v .v5) (i - 16)).toNat =
      byte width5 s₀ (20 * k + i) := fun i hi => by
    by_cases hi' : i < 16
    · rw [ite_eq_left hi', h3.get .v4 (by decide), v2, h1.v]
      exact vbyte_input width5_ok hp h.frame (by simp [width5]; omega_arith) hi'
    · rw [ite_eq_right hi', h3.v, vbyte_setLane0 _ _ (by omega_arith), e2, h1.mem, readW32_byte _ _ (by omega_arith),
        ptr_add, show 20 * k + 16 + (i - 16) = 20 * k + i by omega_arith]
      exact hp.byte_eq h.frame (by simp [width5]; omega_arith) (by decide)
  obtain k20 : s3.v .v20 = idxVec dd10Idx := by
    rw [h3.get .v20 (by decide), v2, h1.get .v20 (by decide)]; exact h.K.2.2.1
  obtain k21 : s4.v .v21 = idxVec dd10IdxHi := by
    rw [h4.get .v21 (by decide), h3.get .v21 (by decide), v2, h1.get .v21 (by decide)]; exact h.K.2.2.2.1
  -- the groups
  let Gv : Nat → Nat := fun l => num width5 s₀ (4 * k + l) 5
  have lane (x : BitVec 128) (l : Nat) (gb : Nat)
      (hx : ∀ b < 8, (vbyte x (8 * l + b)).toNat = if b < 5 then byte width5 s₀ (5 * gb + b) else 0) :
      (vdword x l).toNat = num width5 s₀ gb 5 := by
    rw [num5']
    exact dword5 x l (fun b => byte width5 s₀ (5 * gb + b)) hx
  obtain D6 : DLanes (s5.v .v6) Gv := fun l hl => lane _ l _ fun b hb => by
    rw [h5.get .v6 (by decide), h4.v]
    obtain hk : (vbyte (s3.v .v20) (8 * l + b)).toNat = dd10Idx.getD (8 * l + b) 255 := by
      rw [k20, toNat_idxVec _ (by decide) (by omega_arith)]
    rw [dd10Idx_eq _ (by omega_arith), show (8 * l + b) % 8 = b by omega_arith, show (8 * l + b) / 8 = l by omega_arith] at hk
    by_cases h5' : b < 5
    · rw [ite_eq_left h5'] at hk ⊢
      rw [vbyte_tbl2 (by omega_arith) hk (by omega_arith), show VReg.v4.succ = .v5 from rfl, tab _ (by omega_arith)]
      congr 1; omega_arith
    · rw [ite_eq_right h5'] at hk ⊢
      rw [vbyte_tbl2_out (by omega_arith) hk (by omega_arith)]; rfl
  obtain D7 : DLanes (s5.v .v7) fun l => Gv (2 + l) := fun l hl => lane _ l _ fun b hb => by
    rw [h5.v]
    obtain hk : (vbyte (s4.v .v21) (8 * l + b)).toNat = dd10IdxHi.getD (8 * l + b) 255 := by
      rw [k21, toNat_idxVec _ (by decide) (by omega_arith)]
    rw [dd10IdxHi_eq _ (by omega_arith), show (8 * l + b) % 8 = b by omega_arith, show (8 * l + b) / 8 = l by omega_arith] at hk
    by_cases h5' : b < 5
    · rw [ite_eq_left h5'] at hk ⊢
      rw [vbyte_tbl2 (by omega_arith) hk (by omega_arith), show VReg.v4.succ = .v5 from rfl, h4.get .v4 (by decide),
        h4.get .v5 (by decide), tab _ (by omega_arith)]
      congr 1; omega_arith
    · rw [ite_eq_right h5'] at hk ⊢
      rw [vbyte_tbl2_out (by omega_arith) hk (by omega_arith)]; rfl
  -- the frame so far
  obtain g5 : ∀ r, r ≠ .x9 → s5.gpr r = s.gpr r := fun r hr => by
    rw [h5.gpr, h4.gpr, h3.gpr, o2.gpr r (by simpa using hr), h1.gpr]
  obtain v5 : ∀ r, r ≠ .v4 → r ≠ .v5 → r ≠ .v6 → r ≠ .v7 → s5.v r = s.v r := fun r a b c d => by
    rw [h5.get r d, h4.get r c, h3.get r b, v2, h1.get r a]
  obtain m5 : s5.mem = s.mem := by rw [h5.mem, h4.mem, h3.mem, o2.mem, h1.mem]
  obtain wr5 : s5.wr = s.wr := by rw [h5.wr, h4.wr, h3.wr, o2.wr, h1.wr]
  obtain cs5 : DConsts 5 s5 := ⟨by rw [v5 .v16 (by decide) (by decide) (by decide) (by decide)]; exact h.cs.q,
    by rw [v5 .v17 (by decide) (by decide) (by decide) (by decide)]; exact h.cs.h⟩
  obtain l18 : Lanes (s5.v .v18) fun _ => 2 ^ 20 - 1 := by
    rw [v5 .v18 (by decide) (by decide) (by decide) (by decide)]; exact h.K.1
  obtain l19 : Lanes (s5.v .v19) fun _ => 2 ^ 10 - 1 := by
    rw [v5 .v19 (by decide) (by decide) (by decide) (by decide)]; exact h.K.2.1
  obtain l22 : Lanes (s5.v .v22) fun _ => 2 ^ 5 - 1 := by
    rw [v5 .v22 (by decide) (by decide) (by decide) (by decide)]; exact h.K.2.2.2.2
  obtain x3 : s.gpr .x3 = coeffAddr (fP s₀) (32 * k) := by
    rw [h.x3, show width5.c * 4 * k = 32 * k by simp [width5]; try omega_arith]
  obtain out : CoeffsUpTo s5.mem (fP s₀) (32 * k) (DD.G width5 s₀) (old s₀) := by
    rw [m5, show 32 * k = width5.c * 4 * k by simp [width5]; try omega_arith]; exact h.out
  refine dd5Half_ok (Or.inl rfl) (o := 0) (by decide) cs5 l18 l19 l22 D6
    (fun i hi => by rw [wr5]; exact h.out16 hp hi) (by rw [g5 .x3 (by decide), x3, ptr_zero]) (by omega_arith) out
    (by rw [m5]; exact h.frame) (fun m hm => G5 s₀ hk (by omega_arith)) fun s6 g6 rd6 wr6 sp6 v6 o6 f6 => ?_
  obtain v6' : ∀ r : VReg, r ≠ .v6 → r ≠ .v0 → r ≠ .v1 → r ≠ .v2 → r ≠ .v3 → r ≠ .v4 → r ≠ .v5 → r ≠ .v7 →
      s6.v r = s.v r := fun r a b c d e f g' i => by rw [v6 r a b c d e, v5 r f g' a i]
  refine dd5Half_ok (Or.inr rfl) (o := 64) (by decide)
    ⟨by rw [v6 .v16 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact cs5.q,
     by rw [v6 .v17 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact cs5.h⟩
    (by rw [v6 .v18 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact l18)
    (by rw [v6 .v19 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact l19)
    (by rw [v6 .v22 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact l22)
    (by rw [v6 .v7 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact D7)
    (fun i hi => by rw [wr6, wr5]; exact h.out16 hp hi)
    (by rw [g6, g5 .x3 (by decide), x3]; exact coeffAddr_off _ _ 16) (by omega_arith) o6 f6
    (fun m hm => by
      rw [show 32 * k + 16 + m = 32 * k + (16 + m) by omega_arith, G5 s₀ hk (by omega_arith)]
      simp only [dig5]
      rw [show (16 + m) / 8 = 2 + m / 8 by omega_arith, show (16 + m) % 8 = m % 8 by omega_arith])
    fun s7 g7 rd7 wr7 sp7 v7 o7 f7 => ?_
  obtain k4 : k < 256 / (width5.c * 4) := by simp [width5]; omega_arith
  obtain gg : ∀ r, r ≠ .x9 → s7.gpr r = s.gpr r := fun r hr => by rw [g7, g6, g5 r hr]
  refine WP.mono (dtail_ok (w := width5) (Ng := 4) (s₀ := s₀) k4 (by rw [gg .x0 (by decide), h.x0])
    (by rw [gg .x3 (by decide), h.x3]) (by rw [gg .x11 (by decide), h.x11]) (by decide) (by decide))
    fun u ⟨o, uv, u0, u3, u11, uc⟩ => ?_
  obtain hv : ∀ r, r ∉ [VReg.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7] → u.v r = s.v r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := hr
    rw [uv, v7 r a7 a0 a1 a2 a3, v6' r a6 a0 a1 a2 a3 a4 a5 a7]
  refine ⟨⟨by rw [o.rd, rd7, rd6, h5.rd, h4.rd, h3.rd, o2.rd, h1.rd, h.rd], by rw [o.wr, wr7, wr6, wr5, h.wr],
    by rw [o.sp, sp7, sp6, h5.sp, h4.sp, h3.sp, o2.sp, h1.sp, h.sp], u0, u3, u11,
    ⟨by rw [hv .v16 (by decide)]; exact h.cs.q, by rw [hv .v17 (by decide)]; exact h.cs.h⟩,
    ⟨by rw [hv .v18 (by decide)]; exact h.K.1, by rw [hv .v19 (by decide)]; exact h.K.2.1,
     by rw [hv .v20 (by decide)]; exact h.K.2.2.1, by rw [hv .v21 (by decide)]; exact h.K.2.2.2.1,
     by rw [hv .v22 (by decide)]; exact h.K.2.2.2.2⟩,
    ?_, by rw [o.mem]; exact f7⟩, by rw [show 256 / (width5.c * 4) = 8 from rfl] at uc; exact uc⟩
  rw [o.mem, show width5.c * 4 * (k + 1) = 32 * k + 16 + 16 by simp [width5]; omega_arith]
  exact o7

end VG.Proof.MlKem1024.AArch64.DD
