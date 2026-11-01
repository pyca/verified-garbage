module

public import VerifiedGarbage.Proof.MlKem.PPC64LE.Reduce
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.MlKem.PPC64LE.Add
import VerifiedGarbage.Proof.MlKem.PPC64LE.Ntt
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Reduce
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Add
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Ntt
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Run
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.PPC64LE.RunR
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RunR

/-!
# ML-KEM on PPC64LE: `vg_mlkem_multiply_ntts`

As on 32-bit ARM (`Proof/MlKem/Arm/Mul.lean`): `r14` and `r15` saved and
the table of the `γᵢ` stored (`setup_ok`); then one pair of coefficients per
iteration (`multiplyNTTs_even`, `multiplyNTTs_odd`), whose body is
symbolically executed once for any pointers (`body_ok`); the invariant says
which coefficients of `h` are written, and that `h` is the only memory
written since the setup (`Inv`); then the registers restored.
-/

@[expose] public section

namespace VG.Proof.MlKem.PPC64LE.Mul

open VG VG.PPC64LE VG.Impl.MlKem.PPC64LE
open VG.Spec.MlKem

/-! ## Values -/

theorem red_mac (x y z w : Zq) :
    (red (BitVec.ofNat 64 x.val * BitVec.ofNat 64 y.val + BitVec.ofNat 64 z.val * BitVec.ofNat 64 w.val)).setWidth 32 =
      BitVec.ofNat 32 (x * y + z * w).val := by
  have hx := val_lt x
  have hy := val_lt y
  have hz := val_lt z
  have hw := val_lt w
  have p1 := mul_lt_q2 hx hy
  have p2 := mul_lt_q2 hz hw
  have hs : (BitVec.ofNat 64 x.val * BitVec.ofNat 64 y.val + BitVec.ofNat 64 z.val * BitVec.ofNat 64 w.val).toNat =
      x.val * y.val + z.val * w.val := by
    rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_mul, toNat_val64, toNat_val64, toNat_val64, toNat_val64,
      Nat.mod_eq_of_lt (a := x.val * y.val) (by omega_arith), Nat.mod_eq_of_lt (a := z.val * w.val) (by omega_arith)]
    exact Nat.mod_eq_of_lt (by omega_arith)
  refine setWidth32_ofNat ?_ (by have := val_lt (x * y + z * w); omega_arith)
  rw [red_toNat (by rw [hs]; omega_arith), hs, val_add', val_mul, val_mul, ← Nat.add_mod]

theorem even_eq (a b c d γ : Zq) :
    (red (BitVec.ofNat 64 a.val * BitVec.ofNat 64 b.val +
      red (BitVec.ofNat 64 c.val * BitVec.ofNat 64 d.val) * BitVec.ofNat 64 γ.val)).setWidth 32 =
      BitVec.ofNat 32 (a * b + c * d * γ).val := by
  have : red (BitVec.ofNat 64 c.val * BitVec.ofNat 64 d.val) = BitVec.ofNat 64 (c * d).val := by
    apply BitVec.eq_of_toNat_eq; rw [red_mul, toNat_val64]
  rw [this]; exact red_mac a b (c * d) γ

/-! ## The loop body -/

section
variable {s : State} {x3 x4 x5 x6 c : BitVec 64}

theorem body_ok (h3 : s.gpr .r3 = x3) (h4 : s.gpr .r4 = x4) (h5 : s.gpr .r5 = x5) (h6 : s.gpr .r6 = x6)
    (h8 : s.gpr .r8 = C) (h9 : s.gpr .r9 = 3329) (h11 : s.gpr .r11 = c)
    (if0 : InRegions (s.rd ++ s.wr) x4 4) (if1 : InRegions (s.rd ++ s.wr) (x4 + BitVec.ofNat 64 4) 4)
    (ig0 : InRegions (s.rd ++ s.wr) x5 4) (ig1 : InRegions (s.rd ++ s.wr) (x5 + BitVec.ofNat 64 4) 4)
    (iγ : InRegions (s.rd ++ s.wr) x6 4)
    (o0 : InRegions s.wr x3 4) (o1 : InRegions s.wr (x3 + BitVec.ofNat 64 4) 4) :
    WP isa (.block mulBody) s fun s' =>
      s'.gpr .r3 = x3 + 8 ∧ s'.gpr .r4 = x4 + 8 ∧ s'.gpr .r5 = x5 + 8 ∧ s'.gpr .r6 = x6 + 4 ∧
      s'.gpr .r8 = C ∧ s'.gpr .r9 = 3329 ∧ s'.gpr .r11 = c - 1 ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      s'.lr = s.lr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = (s.mem.writeW x3
          ((red ((s.mem.readW x4 32).setWidth 64 * (s.mem.readW x5 32).setWidth 64 +
            red ((s.mem.readW (x4 + BitVec.ofNat 64 4) 32).setWidth 64 *
              (s.mem.readW (x5 + BitVec.ofNat 64 4) 32).setWidth 64) *
            (s.mem.readW x6 32).setWidth 64)).setWidth 32)).writeW (x3 + BitVec.ofNat 64 4)
          ((red ((s.mem.readW x4 32).setWidth 64 * (s.mem.readW (x5 + BitVec.ofNat 64 4) 32).setWidth 64 +
            (s.mem.readW (x4 + BitVec.ofNat 64 4) 32).setWidth 64 * (s.mem.readW x5 32).setWidth 64)).setWidth 32) := by
  crunr [mulBody, reduce, barrett, fixup, red, bar, fixq, kept, h3, h4, h5, h6, h8, h9, h11, if0, if1, ig0,
    ig1, iγ, o0, o1, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, List.cons_append, List.nil_append]
  simp [Mem.writeW, Mem.readW, Mem.read]

end

/-! ## The loop -/

section
variable (s₀ : State)

abbrev H : Addr := s₀.gpr .r3
abbrev F : Addr := s₀.gpr .r4
abbrev G : Addr := s₀.gpr .r5
abbrev S : Addr := s₀.gpr .r6
abbrev fp : Poly := polyAt s₀.mem (F s₀)
abbrev gp : Poly := polyAt s₀.mem (G s₀)

/-- Coefficient `j` of the output. -/
def out (j : Nat) : BitVec 32 := BitVec.ofNat 32 ((multiplyNTTs (fp s₀) (gp s₀))[j]!).val

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [polyRegion (F s₀), polyRegion (G s₀)]
  wr : s₀.wr = [polyRegion (H s₀), polyRegion (S s₀)]
  hf : (polyRegion (H s₀)).Disjoint (polyRegion (F s₀))
  hg : (polyRegion (H s₀)).Disjoint (polyRegion (G s₀))
  hs : (polyRegion (H s₀)).Disjoint (polyRegion (S s₀))
  fs : (polyRegion (F s₀)).Disjoint (polyRegion (S s₀))
  gs : (polyRegion (G s₀)).Disjoint (polyRegion (S s₀))
  fitH : (H s₀).toNat + 1024 ≤ 2 ^ 64
  fitF : (F s₀).toNat + 1024 ≤ 2 ^ 64
  fitG : (G s₀).toNat + 1024 ≤ 2 ^ 64
  fitS : (S s₀).toNat + 1024 ≤ 2 ^ 64
  redF : Reduced s₀.mem (F s₀)
  redG : Reduced s₀.mem (G s₀)

/-- What the setup leaves in memory `m₁`. -/
structure Setup (s₀ : State) (m₁ : Mem) : Prop where
  sav : Saved m₁ (S s₀ + BitVec.ofNat 64 512) s₀.gpr
  tab : ∀ j < 128, m₁.readW (S s₀ + BitVec.ofNat 64 (4 * j)) 32 = BitVec.ofNat 32 (gammaTable.getD j 0)
  f : ∀ j < 256, coeffAt m₁ (F s₀) j = coeffAt s₀.mem (F s₀) j
  g : ∀ j < 256, coeffAt m₁ (G s₀) j = coeffAt s₀.mem (G s₀) j

/-- After `i` pairs, from the memory `m₁` the setup left. -/
structure Inv (s₀ : State) (m₁ : Mem) (i : Nat) (s : State) : Prop where
  r3 : s.gpr .r3 = H s₀ + BitVec.ofNat 64 (8 * i)
  r4 : s.gpr .r4 = F s₀ + BitVec.ofNat 64 (8 * i)
  r5 : s.gpr .r5 = G s₀ + BitVec.ofNat 64 (8 * i)
  r6 : s.gpr .r6 = S s₀ + BitVec.ofNat 64 (4 * i)
  r8 : s.gpr .r8 = C
  r9 : s.gpr .r9 = 3329
  r11 : s.gpr .r11 = BitVec.ofNat 64 (128 - i)
  kept : ∀ r ∈ kept, s.gpr r = s₀.gpr r
  lr : s.lr = s₀.lr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [polyRegion (H s₀)] m₁ s.mem
  coeff : ∀ j < 256, coeffAt s.mem (H s₀) j = if j < 2 * i then out s₀ j else coeffAt m₁ (H s₀) j

theorem out_even (s₀ : State) {i : Nat} (hi : i < 128) :
    out s₀ (2 * i) = BitVec.ofNat 32 ((fp s₀)[2 * i]! * (gp s₀)[2 * i]! +
      (fp s₀)[2 * i + 1]! * (gp s₀)[2 * i + 1]! * gamma i).val := by
  rw [out, multiplyNTTs_even _ _ hi]

theorem out_odd (s₀ : State) {i : Nat} (hi : i < 128) :
    out s₀ (2 * i + 1) = BitVec.ofNat 32 ((fp s₀)[2 * i]! * (gp s₀)[2 * i + 1]! +
      (fp s₀)[2 * i + 1]! * (gp s₀)[2 * i]!).val := by
  rw [out, multiplyNTTs_odd _ _ hi]

/-- A coefficient, zero-extended, is the element of `ℤ_q` it represents. -/
theorem wide {m : Mem} {p : Addr} {f : Poly} {j : Nat}
    (h : coeffAt m p j = BitVec.ofNat 32 (f[j]!).val) :
    (coeffAt m p j).setWidth 64 = BitVec.ofNat 64 (f[j]!).val := by
  rw [h, setWidth64_ofNat (by have := val_lt f[j]!; omega_arith)]

theorem step {s₀ : State} (hp : Pre s₀) {m₁ : Mem} (hm : Setup s₀ m₁) {i : Nat} (hi : i < 128) {s : State}
    (h : Inv s₀ m₁ i s) :
    WP isa (.block mulBody) s fun s' => Inv s₀ m₁ (i + 1) s' ∧ (s'.gpr .r11 != 0) = decide (i + 1 ≠ 128) := by
  have e0 : ∀ p : Addr, p + BitVec.ofNat 64 (8 * i) = coeffAddr p (2 * i) := fun p => by
    rw [show 8 * i = 4 * (2 * i) by omega_arith]
  have e1 : ∀ p : Addr, p + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 4 = coeffAddr p (2 * i + 1) := fun p => by
    rw [ptr_add, show 8 * i + 4 = 4 * (2 * i + 1) by omega_arith]
  have fS := hp.fitS
  have cF0 := coeff_contains (F s₀) (i := 2 * i) (by rw [n_eq]; omega_arith)
  have cF1 := coeff_contains (F s₀) (i := 2 * i + 1) (by rw [n_eq]; omega_arith)
  have cG0 := coeff_contains (G s₀) (i := 2 * i) (by rw [n_eq]; omega_arith)
  have cG1 := coeff_contains (G s₀) (i := 2 * i + 1) (by rw [n_eq]; omega_arith)
  have cH0 := coeff_contains (H s₀) (i := 2 * i) (by rw [n_eq]; omega_arith)
  have cH1 := coeff_contains (H s₀) (i := 2 * i + 1) (by rw [n_eq]; omega_arith)
  have cS : (polyRegion (S s₀)).Contains (S s₀ + BitVec.ofNat 64 (4 * i)) 4 :=
    Offset.contains_base _ (by omega_arith) (by omega_arith)
  have iR : ∀ {R : Region} {a : Addr} {n : Nat}, R ∈ s₀.rd ++ s₀.wr → R.Contains a n →
      InRegions (s.rd ++ s.wr) a n := fun hR hc => by rw [h.rd, h.wr]; exact ⟨_, hR, hc⟩
  have iW : ∀ {R : Region} {a : Addr} {n : Nat}, R ∈ s₀.wr → R.Contains a n → InRegions s.wr a n :=
    fun hR hc => by rw [h.wr]; exact ⟨_, hR, hc⟩
  -- The values read.
  have vF : ∀ j < 256, coeffAt s.mem (F s₀) j = BitVec.ofNat 32 ((fp s₀)[j]!).val := fun j hj => by
    rw [coeffAt_congr (bytes_frame h.frame (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact hp.hf.symm) (by decide)) (by rw [n_eq]; exact hj), hm.f j hj]
    exact ofNat_val_eq (polyAt_val hp.redF (by rw [n_eq]; exact hj)).symm
  have vG : ∀ j < 256, coeffAt s.mem (G s₀) j = BitVec.ofNat 32 ((gp s₀)[j]!).val := fun j hj => by
    rw [coeffAt_congr (bytes_frame h.frame (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact hp.hg.symm) (by decide)) (by rw [n_eq]; exact hj), hm.g j hj]
    exact ofNat_val_eq (polyAt_val hp.redG (by rw [n_eq]; exact hj)).symm
  have vS : (s.mem.readW (S s₀ + BitVec.ofNat 64 (4 * i)) 32).setWidth 64 = BitVec.ofNat 64 (gamma i).val := by
    rw [h.frame.readW cS (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.hs.symm)
      (by decide), hm.tab i hi, gammaTable_eq, gammas_getD hi,
      setWidth64_ofNat (by have := val_lt (gamma i); omega_arith)]
  refine WP.mono (body_ok h.r3 h.r4 h.r5 h.r6 h.r8 h.r9 h.r11
    (by rw [e0]; exact iR (by simp [hp.rd]) cF0) (by rw [e1]; exact iR (by simp [hp.rd]) cF1)
    (by rw [e0]; exact iR (by simp [hp.rd]) cG0) (by rw [e1]; exact iR (by simp [hp.rd]) cG1)
    (iR (by simp [hp.wr]) cS) (by rw [e0]; exact iW (by simp [hp.wr]) cH0)
    (by rw [e1]; exact iW (by simp [hp.wr]) cH1))
    fun s' ⟨r3, r4, r5, r6, r8, r9, r11, kp, lr, rd, wr, sp, m⟩ => ⟨⟨?_, ?_, ?_, ?_, r8, r9, ?_,
      fun r hr => (kp r hr).trans (h.kept r hr), lr.trans h.lr, rd.trans h.rd, wr.trans h.wr, sp.trans h.sp,
      ?_, ?_⟩, ?_⟩
  · rw [r3]; exact ptr_succ _ 8 i
  · rw [r4]; exact ptr_succ _ 8 i
  · rw [r5]; exact ptr_succ _ 8 i
  · rw [r6]; exact ptr_succ _ 4 i
  · rw [r11]; exact count_sub hi
  · rw [m, e1 (H s₀), e0 (H s₀)]
    exact (h.frame.writeW (List.mem_singleton_self _) _ cH0).writeW (List.mem_singleton_self _) _ cH1
  · rw [m, e1, e1, e1, e0, e0, e0, vS]
    show ∀ j < 256, coeffAt ((s.mem.writeW (coeffAddr (H s₀) (2 * i)) _).writeW _ _) _ j = _
    rw [← coeffAt_eq, ← coeffAt_eq, ← coeffAt_eq, ← coeffAt_eq, wide (vF _ (by omega_arith)), wide (vF _ (by omega_arith)),
      wide (vG _ (by omega_arith)), wide (vG _ (by omega_arith)), even_eq, red_mac, ← out_even s₀ hi, ← out_odd s₀ hi,
      show 2 * (i + 1) = 2 * i + 1 + 1 by omega_arith]
    exact coeff_one (a := 2 * i + 1) (by omega_arith) (coeff_one (a := 2 * i) (by omega_arith) h.coeff rfl) rfl
  · rw [r11, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, count_sub hi]
    exact count_nz hi (by decide)

/-! ## Setup and the end -/

/-- `r14` and `r15` saved and the table stored. -/
theorem setup_base {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (saveRegs .r6 512 ++ table gammaTable .r6)) s₀ fun s =>
      Setup s₀ s.mem ∧ (∀ r, r ≠ .r12 → s.gpr r = s₀.gpr r) ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧
        s.sp = s₀.sp ∧ s.lr = s₀.lr := by
  have fS := hp.fitS
  have wS : ∀ {o k : Nat}, o + k ≤ 1024 → InRegions s₀.wr (S s₀ + BitVec.ofNat 64 o) k := fun h => by
    rw [hp.wr]; exact ⟨_, by simp, Offset.contains_base _ h (by omega_arith)⟩
  have e8 : S s₀ + BitVec.ofNat 64 512 + BitVec.ofNat 64 8 = S s₀ + BitVec.ofNat 64 520 := ptr_add _ _ _
  rw [WP.block_append_iff]
  refine WP.mono (save_ok (b := .r6) (by decide) (off := 512) (by decide) (by decide) rfl (wS (by omega_arith))
    (by rw [e8]; exact wS (by omega_arith))) fun s₁ ⟨g1, lr1, sp1, rd1, wr1, m1⟩ => ?_
  refine WP.mono (table_ok gammaTable (by decide) (b := .r6) (by decide) (by decide) (by rw [g1])
    fun k hk => by rw [wr1]; exact wS (by omega_arith)) fun s₂ h₂ => ?_
  have fr : Frame [polyRegion (S s₀)] s₀.mem s₂.mem := by
    have f1 : Frame [polyRegion (S s₀)] s₀.mem s₁.mem := by
      rw [m1, e8]
      exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
        ).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
    refine f1.trans (h₂.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    rw [List.mem_singleton] at hr; subst hr
    exact Ntt.sub_low _ (by omega_arith)
  have hsav : Saved s₁.mem (S s₀ + BitVec.ofNat 64 512) s₀.gpr := by
    rw [m1]; exact saved_write _ _ _
  have hm : Setup s₀ s₂.mem := by
    refine ⟨⟨?_, ?_⟩, fun j hj => h₂.tab j hj, fun j hj => ?_, fun j hj => ?_⟩
    · rw [h₂.frame.readW (Region.contains_self _ 8) (fun r hr => by
        rw [List.mem_singleton] at hr; subst hr; exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)) (by decide)]
      exact hsav.1
    · rw [h₂.frame.readW (Region.contains_self _ 8) (fun r hr => by
        rw [List.mem_singleton] at hr; subst hr; rw [e8]
        exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)) (by decide)]
      exact hsav.2
    · exact coeffAt_congr (bytes_frame fr (fun r hr => by
        rw [List.mem_singleton] at hr; subst hr; exact hp.fs) (by decide)) (by rw [n_eq]; exact hj)
    · exact coeffAt_congr (bytes_frame fr (fun r hr => by
        rw [List.mem_singleton] at hr; subst hr; exact hp.gs) (by decide)) (by rw [n_eq]; exact hj)
  exact ⟨hm, fun r hr => (h₂.gpr r hr).trans (by rw [g1]), h₂.rd.trans rd1, h₂.wr.trans wr1,
    h₂.sp.trans sp1, h₂.lr.trans lr1⟩

theorem tail_ok {s : State} :
    WP isa (.block (consts ++ ([.li .r11 128] : List Instr))) s
      fun s' => s'.gpr .r3 = s.gpr .r3 ∧ s'.gpr .r4 = s.gpr .r4 ∧ s'.gpr .r5 = s.gpr .r5 ∧
        s'.gpr .r6 = s.gpr .r6 ∧ s'.gpr .r8 = C ∧ s'.gpr .r9 = 3329 ∧ s'.gpr .r11 = 128 ∧
        (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ s'.lr = s.lr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        s'.sp = s.sp := by
  crunr [consts, kept, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, List.cons_append, List.nil_append]
  decide

theorem setup_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (saveRegs .r6 512 ++ table gammaTable .r6 ++ consts ++ ([.li .r11 128] : List Instr))) s₀
      fun s => Setup s₀ s.mem ∧ Inv s₀ s.mem 0 s := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (setup_base hp) fun s₂ ⟨hm, e, rd, wr, sp, lr⟩ => ?_
  refine WP.mono tail_ok fun s ⟨r3, r4, r5, r6, r8, r9, r11, kp, lr', m, rd', wr', sp'⟩ => ?_
  rw [m]
  refine ⟨hm, ⟨by rw [r3, e .r3 (by decide)]; simp, by rw [r4, e .r4 (by decide)]; simp,
    by rw [r5, e .r5 (by decide)]; simp, by rw [r6, e .r6 (by decide)]; simp, r8, r9, r11, fun r hr => ?_,
    lr'.trans lr, rd'.trans rd, wr'.trans wr, sp'.trans sp, by rw [m]; exact Frame.refl _ _,
    fun j _ => by rw [m]; rfl⟩⟩
  rw [kp r hr, e r (by revert r hr; decide)]

theorem restore_end {s₀ : State} (hp : Pre s₀) {m₁ : Mem} (hm : Setup s₀ m₁) {s : State}
    (h : Inv s₀ m₁ 128 s) :
    WP isa (.block (restoreRegs .r6 0)) s fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧
      s'.sp = s₀.sp ∧ s'.lr = s₀.lr ∧ PolyIs s'.mem (H s₀) (multiplyNTTs (fp s₀) (gp s₀)) := by
  have fS := hp.fitS
  have e8 : S s₀ + BitVec.ofNat 64 512 + BitVec.ofNat 64 8 = S s₀ + BitVec.ofNat 64 520 := ptr_add _ _ _
  have rS : ∀ {o k : Nat}, o + k ≤ 1024 → InRegions (s.rd ++ s.wr) (S s₀ + BitVec.ofNat 64 o) k := fun h' => by
    rw [h.rd, h.wr, hp.rd, hp.wr]; exact ⟨_, by simp, Offset.contains_base _ h' (by omega_arith)⟩
  have dj : ∀ {o : Nat}, o + 8 ≤ 1024 → ∀ r ∈ [polyRegion (H s₀)],
      Region.Disjoint ⟨S s₀ + BitVec.ofNat 64 o, 8⟩ r := fun ho r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact hp.hs.symm.sub_left (Offset.sub_base _ ho)
  refine WP.mono (restore_ok (b := .r6) (by decide) (by decide) (off := 0) (by decide) (by decide)
    (A := S s₀ + BitVec.ofNat 64 512) (by rw [h.r6, BitVec.add_zero]) (rS (by omega_arith))
    (by rw [e8]; exact rS (by omega_arith))) fun s' ⟨r14, r15, kp, lr, sp, m⟩ =>
      ⟨preserved_of (g := s₀.gpr) ?_ ?_ (fun r hr => (kp r hr).trans (h.kept r hr)),
        sp.trans h.sp, lr.trans h.lr, ?_⟩
  · rw [r14, h.frame.readW (Region.contains_self _ 8) (dj (by omega_arith)) (by decide)]
    exact hm.sav.1
  · rw [r15, e8, h.frame.readW (Region.contains_self _ 8) (dj (by omega_arith)) (by decide), ← e8]
    exact hm.sav.2
  · rw [m]
    exact polyIs_of_coeffAt fun j hj => by
      rw [h.coeff j (by rw [n_eq] at hj; exact hj), ite_eq_left (by rw [n_eq] at hj; omega_arith)]; rfl

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa multiplyNTTs s₀ fun s => (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧ s.lr = s₀.lr ∧
      PolyIs s.mem (H s₀) (Spec.MlKem.multiplyNTTs (fp s₀) (gp s₀)) := by
  refine WP.seq (WP.mono (setup_ok hp) fun s₁ ⟨hm, h₁⟩ => WP.seq ?_)
  exact wp_loop_nz (Inv s₀ s₁.mem) (N := 128) (by decide) (fun i hi s h => step hp hm hi h)
    (fun s h => restore_end hp hm h) h₁

/-! ## Verified -/

theorem pre_of {s : State} (h : (Proof.MlKem.mulContract PPC64LE.abi).pre s) : Pre s := by
  sig_pre [Proof.MlKem.mulContract, Proof.MlKem.mulSig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | .r6 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x2000, 1024⟩, ⟨0x3000, 1024⟩]
  wr := [⟨0x1000, 1024⟩, ⟨0x4000, 1024⟩]

theorem verified : Verified PPC64LE.target Impl.MlKem.PPC64LE.multiplyNTTs (Proof.MlKem.mulContract PPC64LE.abi) := by
  refine ⟨fun s hs => ?_, Add.ctRegs [.r3, .r4, .r5, .r6] (fun s₁ s₂ h => ?_) (fun s₁ s₂ h => ?_)
    (by taint_decide), ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, hlr, h⟩ := correct (pre_of hs)
    refine ⟨t, s', he, ⟨hpres, hsp, hlr⟩, ?_⟩
    sig_post [Proof.MlKem.mulContract, Proof.MlKem.mulSig, PPC64LE.abi, PPC64LE.argRegs]
    exact h
  · sig_pub [Proof.MlKem.mulContract, Proof.MlKem.mulSig, PPC64LE.abi, PPC64LE.argRegs] at h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2.1
    · exact h.2.2.2.2
  · sig_pub [Proof.MlKem.mulContract, Proof.MlKem.mulSig, PPC64LE.abi, PPC64LE.argRegs] at h
    exact h.1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlKem.mulContract, Proof.MlKem.mulSig, PPC64LE.abi, PPC64LE.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | exact Add.reduced_zero _
        | decide +kernel

end VG.Proof.MlKem.PPC64LE.Mul
