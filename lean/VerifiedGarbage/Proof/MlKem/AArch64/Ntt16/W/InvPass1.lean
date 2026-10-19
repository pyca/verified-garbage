module

public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.W.Pass1
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.InvPass1
import VerifiedGarbage.Proof.Framework.Range

/-!
# ML-KEM's 16-bit inverse NTT on AArch64, of a polynomial stored with 16 bits: pass 1

`invPass1BodyW` (blocks `b < 8`): the 32 coefficients of block `b`, four
vectors of `f` (`i_loadsW`), the first four layers of the inverse
(`ip1_arith`), stored into `scratch` at `64b` as `invPass1Body` stores them.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Ntt16.W

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem VG.Spec.MlKem
open VG.Proof.MlKem.AArch64.Ntt16
open Impl.MlKem.AArch64.Ntt16

/-- After `b` blocks of pass 1 of the inverse, with the table at `t`. -/
structure LI1 (s₀ : State) (b : Nat) (s : State) (t : Addr) : Prop where
  st : St s₀ s
  x2 : s.gpr .x2 = fP s₀ + BitVec.ofNat 64 (64 * b)
  x3 : s.gpr .x3 = sP s₀ + BitVec.ofNat 64 (64 * b)
  x6 : s.gpr .x6 = t + BitVec.ofNat 64 (64 * b)
  x5 : (s.gpr .x5).toNat = 8 - b
  frame : Frame [sR s₀] s₀.mem s.mem
  tableRead : ∀ o, o + 16 ≤ 512 → InRegions (s₀.rd ++ s₀.wr) (t + BitVec.ofNat 64 o) 16
  tableApart : (sR s₀).Disjoint ⟨t, 512⟩
  tab : ∀ j < 64, s.mem.readW (t + BitVec.ofNat 64 (8 * j)) 64 = hw4 invTableHalves j
  scr : ∀ r < b, ∀ i < 4, Rep (s.mem.read (sP s₀ + BitVec.ofNat 64 (64 * r + 16 * i)) 16)
    (fun e => (nttInvL 4 (P₀ s₀))[32 * r + 8 * i + e]!) (2 * 3329)
  q : Cst (s.v .v31) fun _ => 3329
  c10 : Cst (s.v .v30) fun _ => 10

section
variable {rest : List Instr} {Q : State → Prop}

/-- The four vectors of block `b` from the polynomial `P` stored with 16 bits at `f`. -/
theorem i_loadsW {s₀ : State} (hp : Pre s₀) {P : Poly} {b : Nat} (hb : b < 8) {s : State}
    (hst : St s₀ s) (hx2 : s.gpr .x2 = fP s₀ + BitVec.ofNat 64 (64 * b))
    (hpoly : PolyIsW 16 s.mem (fP s₀) P)
    (k : ∀ s', VChg ildRegs s s' → (∀ i < 4, IRepI P 0 (32 * b) (seg (8 * i)) 3329 (s'.v (row i))) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (((List.range 4).map fun i => Instr.ldrq (row i) .x2 (16 * i)) ++ rest)) s Q := by
  rw [List.map_eq_flatMap, WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n s' => VChg ildRegs s s' ∧ ∀ i < n, IRepI P 0 (32 * b) (seg (8 * i)) 3329 (s'.v (row i)))
    (fun r w hr ⟨cw, hw⟩ => ?_) 4 (Nat.le_refl _) s ⟨VChg.refl _ _, fun r hr => absurd hr (Nat.not_lt_zero r)⟩)
    fun s' ⟨c', h'⟩ => k s' c' h'
  have st := hst.vchg cw
  refine wp_ldrq (a := fP s₀ + BitVec.ofNat 64 (2 * (32 * b + 8 * r))) (by omega)
    (by rw [cw.gpr, hx2, ptr_add]; congr 2; omega) (in_rd_wr (inF hp st (by omega))) fun w₁ h₁ => ?_
  refine wp_nil ⟨(cw.trans h₁.chg).mono fun x hx => ?_, fun r' hr' => ?_⟩
  · simp only [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hx
    · rw [List.mem_singleton.mp hx]; exact row_mem_ild hr
  · by_cases e : r' = r
    · subst e
      rw [h₁.v, cw.mem]
      refine (rep_loadW hpoly (by omega)).congr fun e he => ?_
      rw [seg_getD _ he, Nat.add_assoc]; rfl
    · rw [h₁.get _ (fun h => e (row_inj r' (by omega) r (by omega) h))]
      exact hw r' (by omega)

end

theorem ip1_body {s₀ : State} (hp : Pre s₀) {b : Nat} (hb : b < 8) {sb : State} {t : Addr}
    (h : LI1 s₀ b sb t) :
    WP isa (.block invPass1BodyW) sb fun s' => LI1 s₀ (b + 1) s' t ∧ ((s'.gpr .x5).toNat ≠ 0 ↔ b + 1 ≠ 8) := by
  simp only [invPass1BodyW, List.append_assoc]
  have hpoly : PolyIsW 16 sb.mem (fP s₀) (P₀ s₀) :=
    polyIsW16_frame h.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.disj) hp.red
  refine i_loadsW hp hb h.st h.x2 hpoly fun s c₀ R => ?_
  have st := h.st.vchg c₀
  have a6 : ∀ i < 4, s.gpr .x6 + BitVec.ofNat 64 (16 * i) =
      t + BitVec.ofNat 64 (64 * b + 16 * i) := fun i _ => by rw [c₀.gpr, h.x6, ptr_add]
  have i6 : ∀ i < 4, InRegions (s.rd ++ s.wr) (t + BitVec.ofNat 64 (64 * b + 16 * i)) 16 :=
    fun i hi => by rw [st.rd, st.wr]; exact h.tableRead _ (by omega)
  have tl : ∀ i < 4, ∀ e < 8, vhalf (s.mem.read (t + BitVec.ofNat 64 (64 * b + 16 * i)) 16) e =
      BitVec.ofNat 16 ((invBlockHalves b).getD (8 * i + e) 0) := fun i hi e he => by
    have ht : ∀ j < 64, s.mem.readW (t + BitVec.ofNat 64 (8 * j)) 64 = hw4 invTableHalves j :=
      fun j hj => by rw [c₀.mem]; exact h.tab j hj
    have := vhalf_table (off := 0) (by simpa only [Nat.zero_add] using ht) (i := 4 * b + i) (by omega) he
    rw [show 0 + 16 * (4 * b + i) = 64 * b + 16 * i by omega,
      show 8 * (4 * b + i) + e = 32 * b + (8 * i + e) by omega, invTableHalves_get hb (by omega)] at this
    exact this
  refine ip1_arith hb a6 i6 tl R (by rw [c₀.get .v31]; exact h.q) (by rw [c₀.get .v30]; exact h.c10)
    fun s₃₀ C' rows => ?_
  have CC := c₀.trans C'
  have st₃₀ : St s₀ s₃₀ := h.st.vchg CC
  refine wp_storesN 512 (by decide) (p := sP s₀) (base := fun r => 64 * b + 16 * r)
    (fun r _ => by rw [CC.gpr, h.x3, ptr_add]) (fun r hr => ⟨by omega, by omega⟩)
    (fun r hr => by omega) (fun r hr r' hr' e => by omega) (fun r hr => inS hp st₃₀ (by omega))
    fun s₃₁ h₃₁ => ?_
  refine WP.mono (WP.keepV (Q := fun w' => Keep [.x2, .x3, .x6, .x5] s₃₁ w' ∧ w'.mem = s₃₁.mem ∧
      w'.gpr .x2 = s₃₁.gpr .x2 + BitVec.ofNat 64 64 ∧ w'.gpr .x3 = s₃₁.gpr .x3 + BitVec.ofNat 64 64 ∧
      w'.gpr .x6 = s₃₁.gpr .x6 + BitVec.ofNat 64 64 ∧ w'.gpr .x5 = s₃₁.gpr .x5 - BitVec.ofNat 64 1)
    (by decide)
    (wp_addImm (by decide) fun w₁ k₁ e₁ => wp_addImm (by decide) fun w₂ k₂ e₂ =>
      wp_addImm (by decide) fun w₃ k₃ e₃ => wp_subImm (by decide) fun w₄ k₄ e₄ =>
        wp_nil ⟨(((k₁.keep.trans k₂.keep).trans k₃.keep).trans k₄.keep).mono,
          by rw [k₄.mem, k₃.mem, k₂.mem, k₁.mem],
          by rw [k₄.gpr .x2 (by decide), k₃.gpr .x2 (by decide), k₂.gpr .x2 (by decide), e₁],
          by rw [k₄.gpr .x3 (by decide), k₃.gpr .x3 (by decide), e₂, k₁.gpr .x3 (by decide)],
          by rw [k₄.gpr .x6 (by decide), e₃, k₂.gpr .x6 (by decide), k₁.gpr .x6 (by decide)],
          by rw [e₄, k₃.gpr .x5 (by decide), k₂.gpr .x5 (by decide), k₁.gpr .x5 (by decide)]⟩))
    fun w ⟨⟨kw, mw, e2, e3, e6, e5⟩, hv⟩ => ?_
  have gw : s₃₁.gpr = sb.gpr := by rw [h₃₁.gpr, CC.gpr]
  have x5' : (w.gpr .x5).toNat = 8 - (b + 1) := by
    rw [e5, gw, toNat_sub_n (by rw [h.x5]; simp; omega), h.x5]; simp; omega
  have vv : ∀ r ∈ [VReg.v30, .v31], w.v r = sb.v r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> rw [hv, h₃₁.v, CC.get _ (by decide)]
  refine ⟨⟨(st₃₀.keep h₃₁.keep).keep kw, by rw [e2, gw, h.x2, ptr_add]; congr 2,
    by rw [e3, gw, h.x3, ptr_add]; congr 2, by rw [e6, gw, h.x6, ptr_add]; congr 2, x5',
    by rw [mw]; exact h.frame.trans (by rw [← CC.mem]; exact h₃₁.frame), h.tableRead, h.tableApart,
    fun j hj => ?_, fun r hr i hi => ?_, by rw [vv .v31 (by decide)]; exact h.q,
    by rw [vv .v30 (by decide)]; exact h.c10⟩, by rw [x5']; omega⟩
  · rw [mw, h₃₁.frame.readW (r := ⟨t, 512⟩) (contains_off (by omega) (by decide))
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.tableApart.symm) (by decide),
      CC.mem]
    exact h.tab j hj
  · rw [mw]
    by_cases e : r = b
    · subst e
      rw [h₃₁.st i hi]
      refine (rows i hi).congr fun e he => ?_
      rw [seg_getD _ he, Nat.add_assoc]
    · rw [h₃₁.other _ 16 (by omega) (fun r' hr' => by omega), CC.mem]
      exact h.scr r (by omega) i hi

end VG.Proof.MlKem.AArch64.Ntt16.W
