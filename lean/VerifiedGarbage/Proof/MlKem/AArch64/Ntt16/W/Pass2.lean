module

public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.W.Pass1
public import VerifiedGarbage.Proof.MlKem.AArch64.Common
public import VerifiedGarbage.Proof.MlKem.Mem16Bytes
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Pass2
import VerifiedGarbage.Proof.MlKem.AArch64.Coeff16
import VerifiedGarbage.Proof.Framework.Range

/-!
# ML-KEM's 16-bit NTT on AArch64, of a polynomial stored with 16 bits: pass 2

`pass2BodyW` (blocks `b < 8`): the 32 coefficients of block `b` from
`scratch` and its table (`p2_loadsOf`), its last four layers and the
reduction of each lane (`p2_arith`), and its four vectors stored into `f`
at `64b`, the bytes `64b … 64b + 63` of the transform (`L2.out`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Ntt16.W

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem VG.Spec.MlKem
open VG.Proof.MlKem.AArch64.Ntt16
open Impl.MlKem.AArch64.Ntt16

/-- The bytes of `NTT(P)` stored with 16 bits. -/
abbrev nttBytes (P : Poly) : Nat → Byte := bytesW16 fun i => ((nttL 7 P)[i]!).val

/-- After `b` blocks of pass 2, from the memory `mB` that pass 1 left, with the table at `t`. -/
structure L2 (s₀ : State) (mB : Mem) (b : Nat) (s : State) (t : Addr) : Prop where
  st : St s₀ s
  x2 : s.gpr .x2 = sP s₀ + BitVec.ofNat 64 (64 * b)
  x6 : s.gpr .x6 = t + BitVec.ofNat 64 (64 * b)
  x4 : s.gpr .x4 = fP s₀ + BitVec.ofNat 64 (64 * b)
  x5 : (s.gpr .x5).toNat = 8 - b
  frame : Frame [fR s₀] mB s.mem
  tableRead : ∀ o, o + 16 ≤ 512 → InRegions (s₀.rd ++ s₀.wr) (t + BitVec.ofNat 64 o) 16
  tableApart : (fR s₀).Disjoint ⟨t, 512⟩
  tab : ∀ j < 64, mB.readW (t + BitVec.ofNat 64 (8 * j)) 64 = hw4 tableHalves j
  scr : ∀ r < 8, ∀ c' < 4, Rep (mB.read (sP s₀ + BitVec.ofNat 64 (64 * r + 16 * c')) 16)
    (fun e => (nttL 3 (P₀ s₀))[32 * r + 8 * c' + e]!) (4 * 3329)
  out : BytesUpTo s.mem (fP s₀) 512 (64 * b) (nttBytes (P₀ s₀)) fun j => mB (fP s₀ + BitVec.ofNat 64 j)
  q : Cst (s.v .v31) fun _ => 3329
  c10 : Cst (s.v .v30) fun _ => 10

/-- `scratch` as pass 1 left it. -/
theorem L2.read {s₀ : State} (hp : Pre s₀) {mB : Mem} {b : Nat} {s : State} {t : Addr} (h : L2 s₀ mB b s t)
    {o : Nat} (ho : o + 16 ≤ 512) :
    s.mem.read (sP s₀ + BitVec.ofNat 64 o) 16 = mB.read (sP s₀ + BitVec.ofNat 64 o) 16 :=
  h.frame.read (r := sR s₀) (contains_off ho (by decide))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.disj.symm) (by decide)

section
variable {rest : List Instr} {Q : State → Prop}

theorem p2_body {s₀ : State} (hp : Pre s₀) {mB : Mem} {b : Nat} (hb : b < 8) {sb : State}
    {t : Addr} (h : L2 s₀ mB b sb t) :
    WP isa (.block pass2BodyW) sb fun s' => L2 s₀ mB (b + 1) s' t ∧ ((s'.gpr .x5).toNat ≠ 0 ↔ b + 1 ≠ 8) := by
  simp only [pass2BodyW, pass2Loads, List.cons_append, List.nil_append, List.append_assoc]
  have ht : ∀ j < 64, sb.mem.readW (t + BitVec.ofNat 64 (8 * j)) 64 = hw4 tableHalves j :=
    fun j hj => by
      rw [h.frame.readW (r := ⟨t, 512⟩) (contains_off (by omega) (by decide))
        (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.tableApart.symm) (by decide)]
      exact h.tab j hj
  refine p2_loadsOf (P := P₀ s₀) (sP := sP s₀) (t := t)
    (fun i _ => by rw [h.x2, ptr_add]) (fun i _ => by rw [h.x6, ptr_add])
    (fun i _ => in_rd_wr (inS hp h.st (by omega)))
    (fun i _ => by rw [h.st.rd, h.st.wr]; exact h.tableRead _ (by omega))
    (fun i hi => by
      rw [h.read hp (by omega)]
      refine (h.scr b hb i hi).congr fun e he => ?_
      rw [seg_getD _ he, Nat.add_assoc])
    (fun i hi e he => by
      have := vhalf_table (off := 0) (by simpa only [Nat.zero_add] using ht) (i := 4 * b + i) (by omega) he
      rw [show 0 + 16 * (4 * b + i) = 64 * b + 16 * i by omega,
        show 8 * (4 * b + i) + e = 32 * b + (8 * i + e) by omega, tableHalves_get hb (by omega)] at this
      exact this)
    fun s c₀ a0 a1 a2 a3 t20 t21 t22 t23 => ?_
  refine p2_arith hb a0 a1 a2 a3 t20 t21 t22 t23 (by rw [c₀.get .v31]; exact h.q)
    (by rw [c₀.get .v30]; exact h.c10) fun s₂₆ C' out => ?_
  have CC := c₀.trans C'
  have st₂₆ : St s₀ s₂₆ := h.st.vchg CC
  -- the four stored vectors are the bytes `64 b … 64 b + 63` of the transform
  have bytes : ∀ i < 4, ∀ j < 16, (s₂₆.v (row i)).extractLsb' (8 * j) 8 =
      nttBytes (P₀ s₀) (64 * b + 16 * i + j) := fun i hi j hj => by
    rw [show 64 * b + 16 * i + j = 2 * (32 * b + 8 * i) + j by omega]
    exact halves_bytes (out i hi) j hj
  rw [List.map_eq_flatMap, WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (fun i w => w.gpr = s₂₆.gpr ∧ w.rd = s₂₆.rd ∧
      w.wr = s₂₆.wr ∧ w.sp = s₂₆.sp ∧ w.v = s₂₆.v ∧ Frame [fR s₀] s₂₆.mem w.mem ∧
      BytesUpTo w.mem (fP s₀) 512 (64 * b + 16 * i) (nttBytes (P₀ s₀))
        fun j => mB (fP s₀ + BitVec.ofNat 64 j))
    (fun i w hi ⟨g, r, wr, sp, v, fr, co⟩ => ?_) 4 (Nat.le_refl _) s₂₆
    ⟨rfl, rfl, rfl, rfl, rfl, Frame.refl _ _, by rw [Nat.mul_zero, Nat.add_zero, CC.mem]; exact h.out⟩)
    fun w ⟨g, r, wr, sp, v, fr, co⟩ => ?_
  · have st : St s₀ w := ⟨by rw [r, st₂₆.rd], by rw [wr, st₂₆.wr], by rw [sp, st₂₆.sp],
      by rw [g, st₂₆.x0], by rw [g, st₂₆.x1]⟩
    refine wp_strq (a := fP s₀ + BitVec.ofNat 64 (64 * b + 16 * i)) (by omega)
      (by rw [g, CC.gpr, h.x4, ptr_add]) (inF hp st (by omega)) fun w₁ h₁ => wp_nil ?_
    refine ⟨by rw [h₁.gpr, g], by rw [h₁.rd, r], by rw [h₁.wr, wr], by rw [h₁.sp, sp], by rw [h₁.v, v],
      ?_, ?_⟩
    · rw [h₁.mem]
      exact fr.write (List.mem_singleton_self _) _ (contains_off (by omega) (by decide))
    · rw [h₁.mem, show 64 * b + 16 * (i + 1) = 64 * b + 16 * i + 16 by omega]
      exact co.writeN (by decide) (by omega) fun j hj => by rw [v]; exact bytes i hi j hj
  refine WP.mono (WP.keepV (Q := fun w' => Keep [.x2, .x6, .x4, .x5] w w' ∧ w'.mem = w.mem ∧
      w'.gpr .x2 = w.gpr .x2 + BitVec.ofNat 64 64 ∧ w'.gpr .x6 = w.gpr .x6 + BitVec.ofNat 64 64 ∧
      w'.gpr .x4 = w.gpr .x4 + BitVec.ofNat 64 64 ∧ w'.gpr .x5 = w.gpr .x5 - BitVec.ofNat 64 1) (by decide)
    (wp_addImm (by decide) fun w₁ k₁ e₁ => wp_addImm (by decide) fun w₂ k₂ e₂ =>
      wp_addImm (by decide) fun w₃ k₃ e₃ => wp_subImm (by decide) fun w₄ k₄ e₄ =>
        wp_nil ⟨(((k₁.keep.trans k₂.keep).trans k₃.keep).trans k₄.keep).mono,
          by rw [k₄.mem, k₃.mem, k₂.mem, k₁.mem],
          by rw [k₄.gpr .x2 (by decide), k₃.gpr .x2 (by decide), k₂.gpr .x2 (by decide), e₁],
          by rw [k₄.gpr .x6 (by decide), k₃.gpr .x6 (by decide), e₂, k₁.gpr .x6 (by decide)],
          by rw [k₄.gpr .x4 (by decide), e₃, k₂.gpr .x4 (by decide), k₁.gpr .x4 (by decide)],
          by rw [e₄, k₃.gpr .x5 (by decide), k₂.gpr .x5 (by decide), k₁.gpr .x5 (by decide)]⟩))
    fun w' ⟨⟨kw, mw, e2, e6, e4, e5⟩, hv⟩ => ?_
  have gw : w.gpr = sb.gpr := by rw [g, CC.gpr]
  have x5' : (w'.gpr .x5).toNat = 8 - (b + 1) := by
    rw [e5, gw, toNat_sub_n (by rw [h.x5]; simp; omega), h.x5]; simp; omega
  have st : St s₀ w := ⟨by rw [r, st₂₆.rd], by rw [wr, st₂₆.wr], by rw [sp, st₂₆.sp],
    by rw [g, st₂₆.x0], by rw [g, st₂₆.x1]⟩
  have vv : ∀ r ∈ [VReg.v30, .v31], w'.v r = sb.v r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> rw [hv, v, CC.get _ (by decide)]
  refine ⟨⟨st.keep kw, by rw [e2, gw, h.x2, ptr_add]; congr 2,
    by rw [e6, gw, h.x6, ptr_add]; congr 2,
    by rw [e4, gw, h.x4, ptr_add]; congr 2, x5',
    by rw [mw]; exact h.frame.trans (by rw [← CC.mem]; exact fr), h.tableRead, h.tableApart, h.tab, h.scr,
    by rw [mw, show 64 * (b + 1) = 64 * b + 16 * 4 by omega]; exact co,
    by rw [vv .v31 (by decide)]; exact h.q, by rw [vv .v30 (by decide)]; exact h.c10⟩, by rw [x5']; omega⟩

end

end VG.Proof.MlKem.AArch64.Ntt16.W
