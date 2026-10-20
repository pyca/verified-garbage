module

public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Pass1
public import VerifiedGarbage.Spec.MlKem.Kpke16
import VerifiedGarbage.Proof.MlKem.AArch64.Coeff16
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Rc4.AArch64.Vec

/-!
# ML-KEM's 16-bit NTT on AArch64, of a polynomial stored with 16 bits: pass 1

`pass1BodyW` (chunks `c < 4`): the rows of chunk `c`, each eight coefficients
of `f` loaded at once (`p1_loadsW`), the first three layers on them
(`p1_arith`), and the rows stored into `scratch` at `64r + 16c`, as
`pass1Body` stores them.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Ntt16.W

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem VG.Spec.MlKem
open VG.Proof.MlKem.AArch64.Ntt16
open Impl.MlKem.AArch64.Ntt16

section
variable (s₀ : State)

/-- The polynomial, 512 bytes. -/
abbrev fR : Region := ⟨fP s₀, 512⟩
/-- The working space of pass 1, 512 bytes. -/
abbrev sR : Region := ⟨sP s₀, 512⟩
/-- The polynomial to transform. -/
abbrev P₀ : Poly := polyAtW 16 s₀.mem (fP s₀)

end

/-- The precondition. -/
structure Pre (s₀ : State) : Prop where
  wr : s₀.wr = [fR s₀, sR s₀]
  disj : (fR s₀).Disjoint (sR s₀)
  red : ReducedW 16 s₀.mem (fP s₀)

theorem inF {s₀ s : State} (hp : Pre s₀) (h : St s₀ s) {o : Nat} (ho : o + 16 ≤ 512) :
    InRegions s.wr (fP s₀ + BitVec.ofNat 64 o) 16 := by
  rw [h.wr, hp.wr]
  exact in_regions (List.mem_cons_self ..) (contains_off ho (by decide))

theorem inS {s₀ s : State} (hp : Pre s₀) (h : St s₀ s) {o : Nat} (ho : o + 16 ≤ 512) :
    InRegions s.wr (sP s₀ + BitVec.ofNat 64 o) 16 := by
  rw [h.wr, hp.wr]
  exact in_regions (R := sR s₀) (by simp) (contains_off ho (by decide))

/-- A polynomial stored with 16 bits in a region a frame does not write. -/
theorem polyIsW16_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 512⟩ : Region).Disjoint r) (hr : ReducedW 16 m p) :
    PolyIsW 16 m' p (polyAtW 16 m p) := by
  have hc : ∀ i < 256, coeffAtW 16 m' p i = coeffAtW 16 m p i := fun i hi =>
    hf.readW (r := ⟨p, 512⟩) (contains_off (show 2 * i + 16 / 8 ≤ 512 by omega) (by decide)) hd (by decide)
  refine ⟨fun i hi => by rw [hc i hi]; exact hr i hi, Vector.ext fun i hi => ?_⟩
  simp only [polyAtW, Vector.getElem_ofFn]
  rw [hc i hi]

/-- Eight coefficients from `j` of a polynomial stored with 16 bits, in one vector. -/
theorem rep_loadW {m : Mem} {p : Addr} {P : Poly} (h : PolyIsW 16 m p P) {j : Nat} (hj : j + 8 ≤ 256) :
    Rep (m.read (p + BitVec.ofNat 64 (2 * j)) 16) (fun e => P[j + e]!) 3329 := fun e he => by
  have hv := vhalf_read_coeff m p j he
  rw [polyIsW16_toNat h (by omega)] at hv
  have hl : (P[j + e]!).val < 3329 := Fin.isLt _
  rw [LRep, BitVec.toInt_eq_toNat_of_lt (by omega), hv]
  exact ⟨by omega, by omega, by simp⟩

section
variable {rest : List Instr} {Q : State → Prop}

/-- The eight rows of chunk `c`, from the polynomial `P` stored with 16 bits at `f`. -/
theorem p1_loadsW {s₀ : State} (hp : Pre s₀) {P : Poly} {c : Nat} (hc : c < 4) {s : State}
    (hst : St s₀ s) (hx2 : s.gpr .x2 = fP s₀ + BitVec.ofNat 64 (16 * c))
    (hpoly : PolyIsW 16 s.mem (fP s₀) P)
    (k : ∀ s', VChg ldRegs s s' → Rows P c (List.replicate 8 0) 8 s' → WP isa (.block rest) s' Q) :
    WP isa (.block (((List.range 8).map fun r => Instr.ldrq (row r) .x2 (64 * r)) ++ rest)) s Q := by
  rw [List.map_eq_flatMap, WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n s' => VChg ldRegs s s' ∧ Rows P c (List.replicate 8 0) n s') (fun r w hr ⟨cw, hw⟩ => ?_) 8
    (Nat.le_refl _) s ⟨VChg.refl _ _, fun r hr => absurd hr (Nat.not_lt_zero r)⟩)
    fun s' ⟨c', h'⟩ => k s' c' h'
  have st := hst.vchg cw
  refine wp_ldrq (a := fP s₀ + BitVec.ofNat 64 (2 * (32 * r + 8 * c))) (by omega)
    (by rw [cw.gpr, hx2, ptr_add]; congr 2; omega) (in_rd_wr (inF hp st (by omega))) fun w₁ h₁ => ?_
  refine wp_nil ⟨(cw.trans h₁.chg).mono fun x hx => ?_, fun r' hr' => ?_⟩
  · simp only [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hx
    · rw [List.mem_singleton.mp hx]; exact row_mem_ld hr
  · simp only [getD_rep0, Nat.zero_add, Nat.one_mul, nttL_zero]
    by_cases e : r' = r
    · subst e
      rw [h₁.v, cw.mem]
      exact rep_loadW hpoly (by omega)
    · rw [h₁.get _ (fun h => e (row_inj r' (by omega) r hr h))]
      have := hw r' (by omega)
      simp only [getD_rep0, Nat.zero_add, Nat.one_mul, nttL_zero] at this
      exact this

end

/-! ## A chunk -/

/-- After `c` chunks of pass 1. -/
structure L1 (s₀ : State) (c : Nat) (s : State) : Prop where
  st : St s₀ s
  x2 : s.gpr .x2 = fP s₀ + BitVec.ofNat 64 (16 * c)
  x3 : s.gpr .x3 = sP s₀ + BitVec.ofNat 64 (16 * c)
  x5 : (s.gpr .x5).toNat = 4 - c
  frame : Frame [sR s₀] s₀.mem s.mem
  scr : ∀ r < 8, ∀ c' < c, Rep (s.mem.read (sP s₀ + BitVec.ofNat 64 (64 * r + 16 * c')) 16)
    (fun e => (nttL 3 (P₀ s₀))[32 * r + 8 * c' + e]!) (4 * 3329)
  z : ∀ k < 7, vhalf (s.v .v18) k = BitVec.ofNat 16 (Impl.MlKem.AArch64.Ntt16.zeta (k + 1)) ∧
    vhalf (s.v .v19) k = BitVec.ofNat 16 (tw (Impl.MlKem.AArch64.Ntt16.zeta (k + 1)))
  q : Cst (s.v .v31) fun _ => 3329
  c10 : Cst (s.v .v30) fun _ => 10
  c0 : Cst (s.v .v29) fun _ => 0

theorem p1_body {s₀ : State} (hp : Pre s₀) {c : Nat} (hc : c < 4) {s : State} (h : L1 s₀ c s) :
    WP isa (.block pass1BodyW) s fun s' => L1 s₀ (c + 1) s' ∧ ((s'.gpr .x5).toNat ≠ 0 ↔ c + 1 ≠ 4) := by
  simp only [pass1BodyW, List.append_assoc]
  have hpoly : PolyIsW 16 s.mem (fP s₀) (P₀ s₀) :=
    polyIsW16_frame h.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.disj) hp.red
  refine p1_loadsW hp hc h.st h.x2 hpoly fun s₁ c₁ h₁ => ?_
  have z₁ : ∀ k < 7, vhalf (s₁.v .v18) k = BitVec.ofNat 16 (Impl.MlKem.AArch64.Ntt16.zeta (k + 1)) ∧
      vhalf (s₁.v .v19) k = BitVec.ofNat 16 (tw (Impl.MlKem.AArch64.Ntt16.zeta (k + 1))) := by
    rw [c₁.get .v18, c₁.get .v19]; exact h.z
  have q₁ : Cst (s₁.v .v31) fun _ => 3329 := by rw [c₁.get .v31]; exact h.q
  refine p1_arith hc h₁ z₁ q₁ fun s₈ c₈ h₈ => ?_
  have C := c₁.trans c₈
  have st₈ : St s₀ s₈ := h.st.vchg C
  refine wp_storesN 512 (by decide) (p := sP s₀) (base := fun r => 64 * r + 16 * c)
    (fun r _ => by rw [C.gpr, h.x3, ptr_add]; congr 2; omega) (fun r hr => ⟨by omega, by omega⟩)
    (fun r hr => by omega) (fun r hr r' hr' e => by omega) (fun r hr => inS hp st₈ (by omega))
    fun s₉ h₉ => ?_
  refine WP.mono (WP.keepV (Q := fun w' => Keep [.x2, .x3, .x5] s₉ w' ∧ w'.mem = s₉.mem ∧
      w'.gpr .x2 = s₉.gpr .x2 + BitVec.ofNat 64 16 ∧ w'.gpr .x3 = s₉.gpr .x3 + BitVec.ofNat 64 16 ∧
      w'.gpr .x5 = s₉.gpr .x5 - BitVec.ofNat 64 1) (by decide)
    (wp_addImm (by decide) fun w₁ k₁ e₁ => wp_addImm (by decide) fun w₂ k₂ e₂ =>
      wp_subImm (by decide) fun w₃ k₃ e₃ => wp_nil ⟨((k₁.keep.trans k₂.keep).trans k₃.keep).mono,
        by rw [k₃.mem, k₂.mem, k₁.mem], by rw [k₃.gpr .x2 (by decide), k₂.gpr .x2 (by decide), e₁],
        by rw [k₃.gpr .x3 (by decide), e₂, k₁.gpr .x3 (by decide)],
        by rw [e₃, k₂.gpr .x5 (by decide), k₁.gpr .x5 (by decide)]⟩))
    fun w ⟨⟨kw, mw, e2, e3, e5⟩, hv⟩ => ?_
  have g₉ : s₉.gpr = s.gpr := by rw [h₉.gpr, C.gpr]
  have v₉ : w.v = s₈.v := by rw [hv, h₉.v]
  have x5' : (w.gpr .x5).toNat = 4 - (c + 1) := by
    rw [e5, g₉, toNat_sub_n (by rw [h.x5]; simp; omega), h.x5]; simp; omega
  refine ⟨⟨(st₈.keep h₉.keep).keep kw, ?_, ?_, x5', ?_, fun r hr c' hc' => ?_, ?_, ?_, ?_, ?_⟩,
    by rw [x5']; omega⟩
  · rw [e2, g₉, h.x2, ptr_add]; congr 2
  · rw [e3, g₉, h.x3, ptr_add]; congr 2
  · rw [mw]; exact h.frame.trans (C.mem ▸ h₉.frame)
  · rw [mw]
    by_cases e : c' = c
    · subst e
      rw [h₉.st r hr]
      have := h₈ r hr
      rw [getD_rep_lt hr] at this
      exact this
    · rw [h₉.other _ 16 (by omega) (fun r' hr' => by omega), C.mem]
      exact h.scr r hr c' (by omega)
  · intro k hk; rw [v₉, C.get .v18, C.get .v19]; exact h.z k hk
  · rw [v₉, C.get .v31]; exact h.q
  · rw [v₉, C.get .v30]; exact h.c10
  · rw [v₉, C.get .v29]; exact h.c0

end VG.Proof.MlKem.AArch64.Ntt16.W
