module

public import VerifiedGarbage.Proof.MlKem.AArch64.Codec12W.Enc
public import VerifiedGarbage.Proof.MlKem.AArch64.DotW.Lane
public import VerifiedGarbage.Impl.MlKem.AArch64.AddSubW

/-!
# Sums of polynomials stored with 16 bits, on AArch64

`accW op` is proven once for any step `op` that computes a function `F` of
two coefficients less than `q` in halfwords (`HOpSpec`): `haddOp` computes
`(a + b) mod q`, and `accW_ok` writes `G f g` to `f` for the `G` whose
coefficients `F` computes (`addW_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.AddSubW

open VG VG.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Spec.MlKem
open VG.Impl.MlKem.AArch64.AddSubW
open VG.Proof.MlKem.AArch64.Codec12W (WP.vcs)
open VG.Proof.MlKem.AArch64.DotW (HLanes hlanes_coeffs)

section
variable {rest : List Instr} {Q : State → Prop}

theorem hlanes_map2 {s : State} {f : (w : Nat) → BitVec w → BitVec w → BitVec w} {n m : VReg}
    {A B C : Nat → Nat} (hn : HLanes (s.v n) A) (hm : HLanes (s.v m) B)
    (hf : ∀ e < 8, (f 16 (BitVec.ofNat 16 (A e)) (BitVec.ofNat 16 (B e))).toNat = C e) :
    HLanes (VArr.h8.map2 f (s.v n) (s.v m)) C := fun e he => by
  have a : vhalf (s.v n) e = BitVec.ofNat 16 (A e) := by
    apply BitVec.eq_of_toNat_eq; rw [hn e he, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hn e he ▸ (vhalf _ e).isLt)]
  have b : vhalf (s.v m) e = BitVec.ofNat 16 (B e) := by
    apply BitVec.eq_of_toNat_eq; rw [hm e he, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hm e he ▸ (vhalf _ e).isLt)]
  rw [Ntt16.vhalf_map2 _ _ _ he, a, b, hf e he]

/-- `hcsub`: `x mod q` of halfwords `x < 2q`. -/
theorem hcsub_ok {s : State} (hq : HLanes (s.v .v16) fun _ => 3329) {X : Nat → Nat}
    (hx : HLanes (s.v .v2) X) (hb : ∀ e < 8, X e < 2 * 3329)
    (k : ∀ s', VChg [.v3, .v2] s s' → HLanes (s'.v .v2) (fun e => X e % 3329) → WP isa (.block rest) s' Q) :
    WP isa (.block (hcsub ++ rest)) s Q := by
  simp only [hcsub, List.cons_append, List.nil_append]
  refine wp_vop (d := .v3) rfl fun s₁ h₁ => wp_vop (d := .v3) rfl fun s₂ h₂ =>
    wp_vop (d := .v2) rfl fun s₃ h₃ => k s₃ ((h₁.chg.trans h₂.chg).trans h₃.chg |>.mono) ?_
  intro e he
  have b := hb e he
  rw [h₃.v, Ntt16.vhalf_map2 _ _ _ he, h₂.v, h₂.get .v2, h₁.get .v2]
  dsimp only
  have va : ∀ x y : BitVec 128, vhalf (x &&& y) e = vhalf x e &&& vhalf y e := fun x y => by
    simp only [vhalf, BitVec.extractLsb'_and]
  rw [va,
    h₁.get .v16, h₁.v, Ntt16.vhalf_map2 _ _ _ he]
  have hx' := hx e he
  have hq' := hq e he
  split
  · rename_i c
    simp only [VCmpOp.test, hx', hq', decide_eq_true_eq] at c
    simp only [BitVec.allOnes_and, BitVec.toNat_sub, hx', hq']
    omega
  · rename_i c
    simp only [VCmpOp.test, hx', hq', decide_eq_true_eq] at c
    have z : (0 : BitVec 16) &&& vhalf (s.v .v16) e = 0 := by ext; simp
    rw [z, BitVec.toNat_sub, hx']; simp
    omega

/-- `op` computes `F a b` in the halfwords of `v2` from those of `v0 = a` and `v1 = b`, with `q`
in the halfwords of `v16`, changing only `v2` and `v3`. -/
def HOpSpec (op : List Instr) (F : Nat → Nat → Nat) : Prop :=
  ∀ (is : List Instr) (s : State) (Q : State → Prop) (A B : Nat → Nat), (∀ e < 8, A e < 3329) →
    (∀ e < 8, B e < 3329) → HLanes (s.v .v0) A → HLanes (s.v .v1) B → HLanes (s.v .v16) (fun _ => 3329) →
    (∀ s', VChg [.v2, .v3] s s' → HLanes (s'.v .v2) (fun e => F (A e) (B e)) → WP isa (.block is) s' Q) →
    WP isa (.block (op ++ is)) s Q

theorem haddOp_spec : HOpSpec haddOp fun a b => (a + b) % 3329 := by
  intro is s Q A B hA hB lA lB hq k
  simp only [haddOp, List.cons_append]
  refine wp_vop (d := .v2) rfl fun s₁ h₁ => ?_
  have l₁ : HLanes (s₁.v .v2) fun e => A e + B e := by
    rw [h₁.v]
    refine hlanes_map2 lA lB fun e he => ?_
    have := hA e he; have := hB e he
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  refine hcsub_ok (by rw [h₁.get .v16]; exact hq) l₁ (fun e he => by have := hA e he; have := hB e he; omega)
    fun s₂ h₂ l₂ => k s₂ ((h₁.chg.trans h₂).mono) l₂

/-! ## The loop -/

/-- What `accW` needs of the state `s₀` it starts in: the reduced polynomials at `x0`, which
it can write, and at `x1`, apart. -/
structure AccData (s₀ : State) : Prop where
  rf : ∀ j, j + 16 ≤ 512 → InRegions s₀.wr (s₀.gpr .x0 + BitVec.ofNat 64 j) 16
  rg : ∀ j, j + 16 ≤ 512 → InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x1 + BitVec.ofNat 64 j) 16
  apart : (⟨s₀.gpr .x0, 512⟩ : Region).Disjoint ⟨s₀.gpr .x1, 512⟩
  f : ReducedW 16 s₀.mem (s₀.gpr .x0)
  g : ReducedW 16 s₀.mem (s₀.gpr .x1)

/-- The registers `accW` writes. -/
abbrev accClob : List Reg := [.x0, .x1, .x9, .x11]

/-- Coefficient `i` of the result. -/
def newW (F : Nat → Nat → Nat) (s₀ : State) (i : Nat) : BitVec 16 :=
  BitVec.ofNat 16 (F (coeffAtW 16 s₀.mem (s₀.gpr .x0) i).toNat (coeffAtW 16 s₀.mem (s₀.gpr .x1) i).toNat)

/-- After `k` iterations. -/
structure AccInv (F : Nat → Nat → Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ accClob → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x0 : s.gpr .x0 = s₀.gpr .x0 + BitVec.ofNat 64 (16 * k)
  x1 : s.gpr .x1 = s₀.gpr .x1 + BitVec.ofNat 64 (16 * k)
  count : (s.gpr .x11).toNat = 32 - k
  q : HLanes (s.v .v16) fun _ => 3329
  out : CoeffsInW s.mem (s₀.gpr .x0) (· < 8 * k) (newW F s₀) fun i => coeffAtW 16 s₀.mem (s₀.gpr .x0) i
  frame : Frame [⟨s₀.gpr .x0, 512⟩] s₀.mem s.mem

theorem acc_step {op : List Instr} {F : Nat → Nat → Nat} (hop : HOpSpec op F)
    (hF : ∀ a < 3329, ∀ b < 3329, F a b < 2 ^ 16) {s₀ : State} (hd : AccData s₀) {k : Nat} (hk : k < 32)
    {s : State} (h : AccInv F s₀ k s) :
    WP isa (.block (accBodyW op)) s fun s' => AccInv F s₀ (k + 1) s' ∧ ((s'.gpr .x11).toNat ≠ 0 ↔ k + 1 ≠ 32) := by
  simp only [accBodyW, List.cons_append, List.nil_append]
  refine wp_ldrq (a := s₀.gpr .x0 + BitVec.ofNat 64 (2 * (8 * k))) (by decide)
    (by rw [h.x0, BitVec.add_zero]; congr 2; omega)
    (by rw [h.rd, h.wr]; exact in_rd_wr (hd.rf _ (by omega))) fun s₁ h₁ => ?_
  refine wp_ldrq (a := s₀.gpr .x1 + BitVec.ofNat 64 (2 * (8 * k))) (by decide)
    (by rw [h₁.gpr, h.x1, BitVec.add_zero]; congr 2; omega)
    (by rw [h₁.rd, h₁.wr, h.rd, h.wr]; exact hd.rg _ (by omega)) fun s₂ h₂ => ?_
  have cf : ∀ e < 8, (coeffAtW 16 s.mem (s₀.gpr .x0) (8 * k + e)) = coeffAtW 16 s₀.mem (s₀.gpr .x0) (8 * k + e) :=
    fun e he => by rw [h.out _ (by omega), ite_eq_right (by omega)]
  have cg : ∀ e < 8, (coeffAtW 16 s.mem (s₀.gpr .x1) (8 * k + e)) = coeffAtW 16 s₀.mem (s₀.gpr .x1) (8 * k + e) :=
    fun e he => h.frame.readW (r := ⟨s₀.gpr .x1, 512⟩) (contains_off (by omega) (by decide))
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd.apart.symm) (by decide)
  have lA : HLanes (s₂.v .v0) fun e => (coeffAtW 16 s₀.mem (s₀.gpr .x0) (8 * k + e)).toNat := by
    rw [h₂.get .v0, h₁.v]; exact hlanes_coeffs _ _ _ fun e he => by rw [cf e he]
  have lB : HLanes (s₂.v .v1) fun e => (coeffAtW 16 s₀.mem (s₀.gpr .x1) (8 * k + e)).toNat := by
    rw [h₂.v, h₁.mem]; exact hlanes_coeffs _ _ _ fun e he => by rw [cg e he]
  refine hop _ s₂ _ _ _ (fun e _ => hd.f _ (by show _ < 256; omega)) (fun e _ => hd.g _ (by show _ < 256; omega))
    lA lB (by rw [h₂.get .v16, h₁.get .v16]; exact h.q) fun s₃ h₃ l₃ => ?_
  have g₃ : s₃.gpr = s.gpr := by rw [h₃.gpr, h₂.gpr, h₁.gpr]
  refine wp_strq (a := s₀.gpr .x0 + BitVec.ofNat 64 (2 * (8 * k))) (by decide)
    (by rw [g₃, h.x0, BitVec.add_zero]; congr 2; omega)
    (by rw [h₃.wr, h₂.wr, h₁.wr, h.wr]; exact hd.rf _ (by omega)) fun s₄ h₄ => ?_
  refine WP.mono (WP.keepV (Q := fun w' => Only [.x0, .x1, .x11] s₄ w' ∧
      w'.gpr .x0 = s₄.gpr .x0 + BitVec.ofNat 64 16 ∧ w'.gpr .x1 = s₄.gpr .x1 + BitVec.ofNat 64 16 ∧
      w'.gpr .x11 = s₄.gpr .x11 - BitVec.ofNat 64 1) (by decide)
    (wp_addImm (by decide) fun s₅ h₅ e₅ => wp_addImm (by decide) fun s₆ h₆ e₆ =>
      wp_subImm (by decide) fun s₇ h₇ e₇ => wp_nil ⟨((h₅.trans h₆).trans h₇).mono,
        by rw [h₇.get .x0, h₆.get .x0, e₅], by rw [h₇.get .x1, e₆, h₅.get .x1],
        by rw [e₇, h₆.get .x11, h₅.get .x11]⟩))
    fun s' ⟨⟨k', e0, e1, e11⟩, hv⟩ => ?_
  have g₄ : s₄.gpr = s.gpr := by rw [h₄.gpr, g₃]
  have c11 : (s₄.gpr .x11).toNat = 32 - k := by rw [g₄, h.count]
  have v11 : (s'.gpr .x11).toNat = 32 - (k + 1) := by
    rw [e11, toNat_sub_n (by rw [c11]; simp; omega), c11]; simp; omega
  have mm : s'.mem = s.mem.write (s₀.gpr .x0 + BitVec.ofNat 64 (2 * (8 * k))) 16 (s₃.v .v2) := by
    rw [k'.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, v11, ?_, ?_, ?_⟩, by rw [v11]; omega⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [k'.gpr r (by simp [hr.1, hr.2.1, hr.2.2.2]), g₄, h.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2])]
  · rw [k'.rd, h₄.rd, h₃.rd, h₂.rd, h₁.rd, h.rd]
  · rw [k'.wr, h₄.wr, h₃.wr, h₂.wr, h₁.wr, h.wr]
  · rw [k'.sp, h₄.sp, h₃.sp, h₂.sp, h₁.sp, h.sp]
  · rw [e0, g₄, h.x0, ptr_add]; congr 2
  · rw [e1, g₄, h.x1, ptr_add]; congr 2
  · rw [hv, h₄.v, h₃.v .v16 (by decide), h₂.get .v16, h₁.get .v16]; exact h.q
  · rw [mm]
    refine h.out.write16 (by omega) (fun e he => BitVec.eq_of_toNat_eq ?_) (fun i _ => by omega)
    rw [l₃ e he, newW, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hF _ (hd.f _ (by show _ < 256; omega)) _
      (hd.g _ (by show _ < 256; omega)))]
  · rw [mm]; exact h.frame.write (List.mem_singleton_self _) _ (contains_off (by omega) (by decide))

theorem acc_init (F : Nat → Nat → Nat) (s : State) :
    WP isa (.block [.movz .x .x9 3329 0, .vop (.dup .h8 .v16 .x9), .movz .x .x11 32 0]) s (AccInv F s 0) := by
  show WP isa (.block ([Instr.movz .x .x9 3329 0] ++ (.vop (.dup .h8 .v16 .x9) ::
    (([.movz .x .x11 32 0] : List Instr) ++ [])))) s _
  refine wp_scalar (by decide) (P := fun s₁ => Only [.x9] s s₁ ∧ (s₁.gpr .x9).toNat = 3329)
    (wp_movz fun s₁ h₁ e₁ => wp_nil ⟨h₁, by rw [e₁]; rfl⟩) fun s₁ ⟨k₁, e9⟩ _ => ?_
  refine wp_vop (d := .v16) rfl fun s₂ h₂ => ?_
  refine wp_scalar (by decide) (P := fun s₃ => Only [.x11] s₂ s₃ ∧ (s₃.gpr .x11).toNat = 32)
    (wp_movz fun s₃ h₃ e₃ => wp_nil ⟨h₃, by rw [e₃]; rfl⟩) fun s₃ ⟨k₃, e11⟩ hv₃ => wp_nil ?_
  have m : s₃.mem = s.mem := by rw [k₃.mem, h₂.mem, k₁.mem]
  have k₃ := (k₁.keep.trans h₂.keep).trans k₃.keep
  refine ⟨fun r hr => k₃.gpr r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or, List.append_nil, List.cons_append,
      List.nil_append] at hr ⊢
    exact ⟨hr.2.2.1, hr.2.2.2⟩), k₃.rd, k₃.wr, k₃.sp,
    by rw [k₃.get .x0]; exact (BitVec.add_zero _).symm, by rw [k₃.get .x1]; exact (BitVec.add_zero _).symm,
    e11, fun e he => ?_, fun i _ => by rw [m, ite_eq_right (by omega)], by rw [m]; exact Frame.refl _ _⟩
  rw [hv₃, h₂.v, Ntt16.vhalf_ofVHalves _ he]
  simp only [BitVec.toNat_setWidth, e9]

theorem accW_ok {op : List Instr} {F : Nat → Nat → Nat} (hop : HOpSpec op F)
    (hF : ∀ a < 3329, ∀ b < 3329, F a b < 3329) {G : Poly → Poly → Poly}
    (hG : ∀ P R : Poly, ∀ i < 256, ((G P R)[i]!).val = F (P[i]!).val (R[i]!).val)
    (hv : (instrs (accW op)).all (fun i => preservedV.all fun r => vdstOf i != some r) = true)
    {s : State} (hd : AccData s) :
    WP isa (accW op) s fun s' => Keep accClob s s' ∧ Frame [⟨s.gpr .x0, 512⟩] s.mem s'.mem ∧
      PolyIsW 16 s'.mem (s.gpr .x0) (G (polyAtW 16 s.mem (s.gpr .x0)) (polyAtW 16 s.mem (s.gpr .x1))) := by
  refine WP.mono (WP.vcs hv (WP.seq (WP.mono (acc_init F s) fun s₁ h₁ =>
    count_loop (by decide) (AccInv F s) (fun k hk t ht => acc_step hop (fun a ha b hb => by
      have := hF a ha b hb; omega) hd hk ht) h₁)))
    fun s' ⟨h', vcs⟩ => ⟨⟨h'.gpr, h'.rd, h'.wr, h'.sp, vcs⟩, h'.frame,
      h'.out.polyIs (fun i hi => by omega) fun i hi => ?_⟩
  · have hl : i < 256 := hi
    rw [newW, BitVec.toNat_ofNat, hG _ _ i hl, Nat.mod_eq_of_lt (by have := hF _ (hd.f i hl) _ (hd.g i hl); omega)]
    simp only [polyAtW]
    rw [getElem!_eq _ hl, getElem!_eq _ hl, Vector.getElem_ofFn, Vector.getElem_ofFn, val_ofNat, val_ofNat,
      Nat.mod_eq_of_lt (hd.f i hl), Nat.mod_eq_of_lt (hd.g i hl)]

theorem addW_ok {s : State} (hd : AccData s) :
    WP isa addW s fun s' => Keep accClob s s' ∧ Frame [⟨s.gpr .x0, 512⟩] s.mem s'.mem ∧
      PolyIsW 16 s'.mem (s.gpr .x0) (add (polyAtW 16 s.mem (s.gpr .x0)) (polyAtW 16 s.mem (s.gpr .x1))) :=
  accW_ok haddOp_spec (fun a _ b _ => Nat.mod_lt _ (by decide))
    (fun P R i hi => by
      have : (P[i]!).val < 3329 := Fin.isLt _
      have : (R[i]!).val < 3329 := Fin.isLt _
      have hq : q = 3329 := rfl
      rw [add_get _ _ hi, val_add, condSub]; split <;> omega) (by decide +kernel) hd

end VG.Proof.MlKem.AArch64.AddSubW
