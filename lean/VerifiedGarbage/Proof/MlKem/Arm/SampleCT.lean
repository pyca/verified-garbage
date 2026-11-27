module

public import VerifiedGarbage.Proof.MlKem.Arm.Sample
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlKem.Arm.Sample
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha3.Arm.Stream.Absorb
meta import VerifiedGarbage.Proof.Sha3.Arm.Stream.Absorb
public import VerifiedGarbage.Proof.MlKem.KPke
public import VerifiedGarbage.Impl.MlKem.Arm.Top
public import VerifiedGarbage.Proof.MlKem.Arm.Keccak
public import VerifiedGarbage.Proof.MlKem.PolyContract
public import VerifiedGarbage.Proof.MlKem.Arm.Reduce
public import VerifiedGarbage.Proof.MlKem.Arm.Add
import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.MlKem.Arm.Add
meta import VerifiedGarbage.Proof.MlKem.Arm.Keccak
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.MlKem.Arm.Reduce

/-! ### `MlKem.Arm.HashTop`, which the modules that import this one used -/

section

/-! ### `MlKem.Arm.Prims`, which this module and modules that import it used -/

section

/-! ### `MlKem.Arm.Mul`, which only this module used -/

section

/-!
# ML-KEM on 32-bit ARM: `vg_mlkem_multiply_ntts`

The registers saved and the table of the `γᵢ` stored (`setup_ok`); then one
pair of coefficients per iteration (`multiplyNTTs_even`, `multiplyNTTs_odd`),
whose body is symbolically executed once for any pointers (`body_ok`) and
stores the reductions of the sums of products (`even_eq`, `red_mac`); the
invariant says which coefficients of `h` are written, and that `h` is the only
memory written since the setup (`Inv`); then the registers restored.
-/

@[expose] public section

namespace VG.Proof.MlKem.Arm.Mul

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Proof.MlKem.Arm.Add (ptr_succ reduced_zero)

/-! ## Values -/

theorem toNat_mul_zq (x y : Zq) :
    (BitVec.ofNat 32 x.val * BitVec.ofNat 32 y.val).toNat = x.val * y.val := by
  have p := mul_lt_q2 (val_lt x) (val_lt y)
  rw [BitVec.toNat_mul, toNat_zq, toNat_zq]
  exact Nat.mod_eq_of_lt (by omega_using [p])

theorem red_mac (x y z w : Zq) :
    red (BitVec.ofNat 32 x.val * BitVec.ofNat 32 y.val + BitVec.ofNat 32 z.val * BitVec.ofNat 32 w.val) =
      BitVec.ofNat 32 (x * y + z * w).val := by
  obtain p1 := mul_lt_q2 (val_lt x) (val_lt y)
  obtain p2 := mul_lt_q2 (val_lt z) (val_lt w)
  obtain hs : (BitVec.ofNat 32 x.val * BitVec.ofNat 32 y.val + BitVec.ofNat 32 z.val * BitVec.ofNat 32 w.val).toNat =
      x.val * y.val + z.val * w.val := by
    rw [BitVec.toNat_add, toNat_mul_zq, toNat_mul_zq]
    exact Nat.mod_eq_of_lt (by omega_using [p1, p2])
  refine ofNat_val_eq ?_
  rw [red_toNat (by rw [hs]; omega_using [p1, p2]), hs, val_add', val_mul, val_mul, ← Nat.add_mod]

theorem even_eq (a b c d γ : Zq) :
    red (BitVec.ofNat 32 a.val * BitVec.ofNat 32 b.val +
      bar (BitVec.ofNat 32 c.val * BitVec.ofNat 32 d.val) * BitVec.ofNat 32 γ.val) =
      BitVec.ofNat 32 (a * b + c * d * γ).val := by
  obtain p1 := mul_lt_q2 (val_lt a) (val_lt b)
  obtain p2 := mul_lt_q2 (val_lt c) (val_lt d)
  have hcd : (BitVec.ofNat 32 c.val * BitVec.ofNat 32 d.val).toNat < 2 ^ 25 := by
    rw [toNat_mul_zq]; omega_using [p2]
  have eB := bar_toNat hcd
  have hB : barrett32 (c.val * d.val) < 2 * 3329 := barrett32_lt (by omega_using [p2])
  have hBm := barrett32_mod (x := c.val * d.val) (by omega_using [p2])
  rw [toNat_mul_zq] at eB
  have hg := val_lt γ
  have p3 : barrett32 (c.val * d.val) * γ.val ≤ 6657 * 3328 :=
    Nat.mul_le_mul (by omega_using [hB]) (by omega_using [hg])
  have hm : (bar (BitVec.ofNat 32 c.val * BitVec.ofNat 32 d.val) * BitVec.ofNat 32 γ.val).toNat =
      barrett32 (c.val * d.val) * γ.val := by
    rw [BitVec.toNat_mul, eB, toNat_zq]
    exact Nat.mod_eq_of_lt (by omega_using [p3])
  have hs : (BitVec.ofNat 32 a.val * BitVec.ofNat 32 b.val +
      bar (BitVec.ofNat 32 c.val * BitVec.ofNat 32 d.val) * BitVec.ofNat 32 γ.val).toNat =
      a.val * b.val + barrett32 (c.val * d.val) * γ.val := by
    rw [BitVec.toNat_add, toNat_mul_zq, hm]
    exact Nat.mod_eq_of_lt (by omega_using [p1, p3])
  refine ofNat_val_eq ?_
  have e : barrett32 (c.val * d.val) * γ.val % q = c.val * d.val % q * γ.val % q := by
    rw [Nat.mul_mod, hBm, Nat.mul_mod_mod]
  rw [red_toNat (by rw [hs]; omega_using [p1, p3]), hs, val_add', val_mul, val_mul, val_mul, Nat.add_mod, e]

/-! ## The loop body -/

section
variable {s : State} {x0 x1 x2 x3 c : BitVec 32}

theorem body_ok (h0 : s.gpr .r0 = x0) (h1 : s.gpr .r1 = x1) (h2 : s.gpr .r2 = x2) (h3 : s.gpr .r3 = x3)
    (h8 : s.gpr .r8 = C) (h11 : s.gpr .r11 = c) (h12 : s.gpr .r12 = Nq)
    (if0 : InRegions (s.rd ++ s.wr) (State.addr (x1 + BitVec.ofNat 32 0)) 4)
    (if1 : InRegions (s.rd ++ s.wr) (State.addr (x1 + BitVec.ofNat 32 4)) 4)
    (ig0 : InRegions (s.rd ++ s.wr) (State.addr (x2 + BitVec.ofNat 32 0)) 4)
    (ig1 : InRegions (s.rd ++ s.wr) (State.addr (x2 + BitVec.ofNat 32 4)) 4)
    (iγ : InRegions (s.rd ++ s.wr) (State.addr (x3 + BitVec.ofNat 32 0)) 4)
    (o0 : InRegions s.wr (State.addr (x0 + BitVec.ofNat 32 0)) 4)
    (o1 : InRegions s.wr (State.addr (x0 + BitVec.ofNat 32 4)) 4) :
    WP isa (.block mulBody) s fun s' =>
      s'.gpr .r0 = x0 + 8 ∧ s'.gpr .r1 = x1 + 8 ∧ s'.gpr .r2 = x2 + 8 ∧ s'.gpr .r3 = x3 + 4 ∧
      s'.gpr .r8 = C ∧ s'.gpr .r11 = c - 1 ∧ s'.gpr .r12 = Nq ∧ s'.z = (c - 1 == 0) ∧ s'.gpr .lr = s.gpr .lr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = (s.mem.writeW (State.addr (x0 + BitVec.ofNat 32 0))
          (red (s.mem.readW (State.addr (x1 + BitVec.ofNat 32 0)) 32 *
              s.mem.readW (State.addr (x2 + BitVec.ofNat 32 0)) 32 +
            bar (s.mem.readW (State.addr (x1 + BitVec.ofNat 32 4)) 32 *
              s.mem.readW (State.addr (x2 + BitVec.ofNat 32 4)) 32) *
            s.mem.readW (State.addr (x3 + BitVec.ofNat 32 0)) 32))).writeW
        (State.addr (x0 + BitVec.ofNat 32 4))
          (red (s.mem.readW (State.addr (x1 + BitVec.ofNat 32 4)) 32 *
              s.mem.readW (State.addr (x2 + BitVec.ofNat 32 0)) 32 +
            s.mem.readW (State.addr (x1 + BitVec.ofNat 32 0)) 32 *
              s.mem.readW (State.addr (x2 + BitVec.ofNat 32 4)) 32)) := by
  run_block [↓RegUpd.gpr_setReg, ↓reduceIte, mulBody, reduce, barrett, csubN, red, bar, csn, h0, h1, h2, h3, h8,
    h11, h12, if0, if1, ig0, ig1, iγ, o0, o1, and_self, and_true]

end

/-! ## The loop -/

section
variable (s₀ : State)

abbrev ph : BitVec 32 := s₀.gpr .r0
abbrev pf : BitVec 32 := s₀.gpr .r1
abbrev pg : BitVec 32 := s₀.gpr .r2
abbrev ps : BitVec 32 := s₀.gpr .r3
abbrev H : Addr := State.addr (ph s₀)
abbrev F : Addr := State.addr (pf s₀)
abbrev G : Addr := State.addr (pg s₀)
abbrev S : Addr := State.addr (ps s₀)
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
  fitH : (ph s₀).toNat + 1024 ≤ 2 ^ 32
  fitF : (pf s₀).toNat + 1024 ≤ 2 ^ 32
  fitG : (pg s₀).toNat + 1024 ≤ 2 ^ 32
  fitS : (ps s₀).toNat + 1024 ≤ 2 ^ 32
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
  r0 : s.gpr .r0 = ph s₀ + BitVec.ofNat 32 (8 * i)
  r1 : s.gpr .r1 = pf s₀ + BitVec.ofNat 32 (8 * i)
  r2 : s.gpr .r2 = pg s₀ + BitVec.ofNat 32 (8 * i)
  r3 : s.gpr .r3 = ps s₀ + BitVec.ofNat 32 (4 * i)
  r8 : s.gpr .r8 = C
  r11 : s.gpr .r11 = BitVec.ofNat 32 (1 * (128 - i))
  r12 : s.gpr .r12 = Nq
  lr : s.gpr .lr = s₀.gpr .lr
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

/-- The odd coefficient, with its products in the order the code adds them. -/
theorem out_odd' (s₀ : State) {i : Nat} (hi : i < 128) :
    out s₀ (2 * i + 1) = BitVec.ofNat 32 ((fp s₀)[2 * i + 1]! * (gp s₀)[2 * i]! +
      (fp s₀)[2 * i]! * (gp s₀)[2 * i + 1]!).val := by
  rw [out_odd s₀ hi]
  refine congrArg (BitVec.ofNat 32) ?_
  rw [val_add', val_add', Nat.add_comm]

theorem step {s₀ : State} (hp : Pre s₀) {m₁ : Mem} (hm : Setup s₀ m₁) {i : Nat} (hi : i < 128) {s : State}
    (h : Inv s₀ m₁ i s) :
    WP isa (.block mulBody) s fun s' => Inv s₀ m₁ (i + 1) s' ∧ s'.z = decide (i + 1 = 128) := by
  have fH := hp.fitH
  have fF := hp.fitF
  have fG := hp.fitG
  have fS := hp.fitS
  obtain eF0 := addr_coeff (i := 8 * i) (o := 0) (j := 2 * i) fF (by omega_arith) (by omega_arith)
  obtain eF1 := addr_coeff (i := 8 * i) (o := 4) (j := 2 * i + 1) fF (by omega_arith) (by omega_arith)
  obtain eG0 := addr_coeff (i := 8 * i) (o := 0) (j := 2 * i) fG (by omega_arith) (by omega_arith)
  obtain eG1 := addr_coeff (i := 8 * i) (o := 4) (j := 2 * i + 1) fG (by omega_arith) (by omega_arith)
  obtain eH0 := addr_coeff (i := 8 * i) (o := 0) (j := 2 * i) fH (by omega_arith) (by omega_arith)
  obtain eH1 := addr_coeff (i := 8 * i) (o := 4) (j := 2 * i + 1) fH (by omega_arith) (by omega_arith)
  obtain eS := addr_ptr (ps s₀) (4 * i) 0 (by omega_arith)
  obtain cF0 := coeff_contains (F s₀) (i := 2 * i) (by rw [n_eq]; omega_arith)
  obtain cF1 := coeff_contains (F s₀) (i := 2 * i + 1) (by rw [n_eq]; omega_arith)
  obtain cG0 := coeff_contains (G s₀) (i := 2 * i) (by rw [n_eq]; omega_arith)
  obtain cG1 := coeff_contains (G s₀) (i := 2 * i + 1) (by rw [n_eq]; omega_arith)
  obtain cH0 := coeff_contains (H s₀) (i := 2 * i) (by rw [n_eq]; omega_arith)
  obtain cH1 := coeff_contains (H s₀) (i := 2 * i + 1) (by rw [n_eq]; omega_arith)
  obtain cS : (polyRegion (S s₀)).Contains (S s₀ + BitVec.ofNat 64 (4 * i + 0)) 4 :=
    contains_off (by omega_arith) (by omega_arith)
  obtain iR : ∀ {R : Region} {a : Addr} {n : Nat}, R ∈ s₀.rd ++ s₀.wr → R.Contains a n →
      InRegions (s.rd ++ s.wr) a n := fun hR hc => by rw [h.rd, h.wr]; exact inRegions_of hR hc
  obtain iW : ∀ {R : Region} {a : Addr} {n : Nat}, R ∈ s₀.wr → R.Contains a n → InRegions s.wr a n :=
    fun hR hc => by rw [h.wr]; exact inRegions_of hR hc
  -- The values read.
  obtain vF : ∀ j < 256, coeffAt s.mem (F s₀) j = BitVec.ofNat 32 ((fp s₀)[j]!).val := fun j hj => by
    rw [frame_coeff h.frame (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.hf.symm)
      (by rw [n_eq]; exact hj), hm.f j hj]
    exact ofNat_val_eq (polyAt_val hp.redF (by rw [n_eq]; exact hj)).symm
  obtain vG : ∀ j < 256, coeffAt s.mem (G s₀) j = BitVec.ofNat 32 ((gp s₀)[j]!).val := fun j hj => by
    rw [frame_coeff h.frame (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.hg.symm)
      (by rw [n_eq]; exact hj), hm.g j hj]
    exact ofNat_val_eq (polyAt_val hp.redG (by rw [n_eq]; exact hj)).symm
  obtain vS : s.mem.readW (S s₀ + BitVec.ofNat 64 (4 * i + 0)) 32 = BitVec.ofNat 32 (gamma i).val := by
    rw [h.frame.readW cS (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.hs.symm)
      (by decide), Nat.add_zero, hm.tab i hi, gammaTable_eq, gammas_getD hi]
  refine WP.mono (body_ok h.r0 h.r1 h.r2 h.r3 h.r8 h.r11 h.r12
    (by rw [eF0]; exact iR (by simp [hp.rd]) cF0) (by rw [eF1]; exact iR (by simp [hp.rd]) cF1)
    (by rw [eG0]; exact iR (by simp [hp.rd]) cG0) (by rw [eG1]; exact iR (by simp [hp.rd]) cG1)
    (by rw [eS]; exact iR (by simp [hp.wr]) cS) (by rw [eH0]; exact iW (by simp [hp.wr]) cH0)
    (by rw [eH1]; exact iW (by simp [hp.wr]) cH1))
    fun s' ⟨r0, r1, r2, r3, r8, r11, r12, z, lr, rd, wr, sp, m⟩ => ⟨⟨?_, ?_, ?_, ?_, r8, ?_, r12, lr.trans h.lr,
      rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, ?_, ?_⟩, ?_⟩
  · rw [r0]; exact ptr_succ _ 8 i
  · rw [r1]; exact ptr_succ _ 8 i
  · rw [r2]; exact ptr_succ _ 8 i
  · rw [r3]; exact ptr_succ _ 4 i
  · rw [r11]; exact count_sub (k := 1) hi
  · rw [m, eH0, eH1]
    exact (h.frame.writeW (List.mem_singleton_self _) _ cH0).writeW (List.mem_singleton_self _) _ cH1
  · rw [m, eF0, eF1, eG0, eG1, eH0, eH1, eS]
    show ∀ j < 256, coeffAt ((s.mem.writeW (coeffAddr (H s₀) (2 * i)) _).writeW _ _) _ j = _
    rw [← coeffAt_eq, ← coeffAt_eq, ← coeffAt_eq, ← coeffAt_eq, vF _ (by omega_arith), vF _ (by omega_arith),
      vG _ (by omega_arith), vG _ (by omega_arith), vS, even_eq, red_mac, ← out_even s₀ hi, ← out_odd' s₀ hi,
      show 2 * (i + 1) = 2 * i + 1 + 1 by omega_arith]
    exact coeff_one (a := 2 * i + 1) (by omega_arith) (coeff_one (a := 2 * i) (by omega_arith) h.coeff rfl) rfl
  · rw [z]; exact count_z (k := 1) hi (by decide) (by decide)

/-! ## Setup and the end -/

theorem setup_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (saveRegs .r3 512 ++ table gammaTable .r3 ++ consts ++
      ([.movw .r12 0xF2FF, .movt .r12 0xFFFF, .mov .r11 (.imm 128)] : List Instr)))
      s₀ fun s => Setup s₀ s.mem ∧ Inv s₀ s.mem 0 s := by
  have fS := hp.fitS
  obtain wS : ∀ {o n : Nat}, o + n ≤ 1024 → InRegions s₀.wr (S s₀ + BitVec.ofNat 64 o) n := fun h => by
    rw [hp.wr]; exact inRegions_of (by simp) (contains_off h (by omega_arith))
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (saveRegs_ok .r3 (off := 512) (by decide) (fit_le (by decide) fS) fun i hi => by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact wS (by omega_arith)) fun s₁ h₁ => ?_
  rw [WP.block_append_iff]
  obtain g3 : (s₁.gpr .r3) = ps s₀ := by rw [h₁.gpr]
  refine WP.mono (table_ok gammaTable (by decide) (b := .r3) (by decide) (by rw [g3]; exact fit_le (by decide) fS)
    fun k hk => by rw [g3, h₁.wr]; exact wS (by omega_arith)) fun s₂ h₂ => ?_
  -- The memory after the setup, and its bytes outside `scratch`.
  obtain hS : (S s₀).toNat + 1024 ≤ 2 ^ 64 := addr_fit _ (by decide)
  obtain fr : Frame [polyRegion (S s₀)] s₀.mem s₂.mem := by
    refine (h₁.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      (h₂.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    · rw [List.mem_singleton] at hr; subst hr
      exact region_sub_off (by decide)
    · rw [List.mem_singleton] at hr; subst hr
      rw [g3, ← add_ofNat_zero (State.addr (ps s₀))]
      exact region_sub_off (by decide)
  obtain hm : Setup s₀ s₂.mem := by
    refine ⟨fun i hi => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩
    · rw [h₂.frame.readW (r := ⟨S s₀ + BitVec.ofNat 64 512 + BitVec.ofNat 64 (4 * i), 4⟩)
        (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
      · exact h₁.saved i hi
      · rw [List.mem_singleton] at hr; subst hr
        rw [g3, add_ofNat_add, ← add_ofNat_zero (State.addr (ps s₀))]
        exact region_disj_off (by omega_arith) (by omega_arith) (by omega_arith) hS
    · have := h₂.tab j hj; rwa [g3] at this
    · exact frame_coeff fr (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.fs)
        (by rw [n_eq]; exact hj)
    · exact frame_coeff fr (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.gs)
        (by rw [n_eq]; exact hj)
  obtain e : ∀ r, r ≠ .r12 → s₂.gpr r = s₀.gpr r := fun r hr => (h₂.gpr r hr).trans (by rw [h₁.gpr])
  obtain e0 := e .r0 (by decide)
  obtain e1 := e .r1 (by decide)
  obtain e2 := e .r2 (by decide)
  obtain e3 := e .r3 (by decide)
  obtain elr := e .lr (by decide)
  run_block [↓RegUpd.gpr_setReg, ↓reduceIte, consts, e0, e1, e2, e3, elr, h₂.rd, h₁.rd, h₂.wr, h₁.wr, h₂.sp, h₁.sp,
    consts_val, constsN_val, hm, true_and]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, Frame.refl _ _, fun j _ => ?_⟩ <;>
    simp [e0, e1, e2, e3, elr]

theorem restore_ok {s₀ : State} (hp : Pre s₀) {m₁ : Mem} (hm : Setup s₀ m₁) {s : State}
    (h : Inv s₀ m₁ 128 s) :
    WP isa (.block (restoreRegs .r3 0)) s fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧
      s'.sp = s₀.sp ∧ PolyIs s'.mem (H s₀) (multiplyNTTs (fp s₀) (gp s₀)) := by
  have fS := hp.fitS
  obtain hS : (S s₀).toNat + 1024 ≤ 2 ^ 64 := addr_fit _ (by decide)
  obtain e3 : State.addr (s.gpr .r3) + BitVec.ofNat 64 0 = S s₀ + BitVec.ofNat 64 512 := by
    rw [h.r3, addr_add (by omega_arith), add_ofNat_zero]
  refine WP.mono (restoreRegs_ok .r3 (by decide) (off := 0) (by decide) (by rw [h.r3]; bv_omega)
    (g := s₀.gpr) (by
      rw [e3]
      intro i hi
      rw [h.frame.readW (r := ⟨S s₀ + BitVec.ofNat 64 512 + BitVec.ofNat 64 (4 * i), 4⟩)
        (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
      · exact hm.sav i hi
      · rw [List.mem_singleton] at hr; subst hr
        refine hp.hs.symm.sub_left ?_
        rw [add_ofNat_add]
        exact region_sub_off (by omega_arith))
    fun i hi => by
      rw [e3, h.rd, h.wr, hp.wr, add_ofNat_add]
      exact inRegions_of (R := polyRegion (S s₀)) (by simp) (contains_off (by omega_arith) (by omega_arith)))
    fun s' h' => ⟨preserved_of_restore h' h.lr, h'.sp.trans h.sp, ?_⟩
  rw [h'.mem]
  exact polyIs_of_coeffAt fun j hj => by
    rw [h.coeff j (by rw [n_eq] at hj; exact hj), ite_eq_left (by rw [n_eq] at hj; omega_arith)]; rfl

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa multiplyNTTs s₀ fun s => (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧
      PolyIs s.mem (H s₀) (Spec.MlKem.multiplyNTTs (fp s₀) (gp s₀)) := by
  refine WP.seq (WP.mono (setup_ok hp) fun s₁ ⟨hm, h₁⟩ => WP.seq ?_)
  exact wp_loop_ne (Inv s₀ s₁.mem) (N := 128) (by decide) (fun i hi s h => step hp hm hi h)
    (fun s h => restore_ok hp hm h) h₁

end VG.Proof.MlKem.Arm.Mul

end

end

/-!
# ML-KEM on 32-bit ARM: calling the primitives

For each primitive, a contract written with the precondition of its proof
(`Add.Pre`, …) and what its correctness proof shows (`kAdd`, …), from which a
caller runs a call of it (`add_call`, …, by `WP.call`, or `WP.callF` for
`vg_mlkem_sample_ntt`, which has frames), given its arguments in the registers
and its buffers where it may access them (`AccArgs`, …); and that two runs
that call it with the same pointers leak the same trace (`add_ct`, …, by
`RelCT.call`, with constant time from the taint analysis of its code, or from
`Sample.all_ct`).
-/

@[expose] public section

namespace VG.Proof.MlKem.Arm

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-! ## Generic -/

/-- A contract from a precondition, what the code leaves and the public data. -/
def mkK (P : State → Prop) (Q : State → State → Prop) (pub : State → State → Prop) : Contract isa :=
  { pre := P, post := Q, pub := pub }

/-- The registers `rs` are the same. -/
def regsEq (rs : List Reg) (s₁ s₂ : State) : Prop := ∀ r ∈ rs, s₁.gpr r = s₂.gpr r

theorem mkK_ok {c : Prog isa} {P : State → Prop} {Q : State → State → Prop} {pub : State → State → Prop}
    (h : ∀ s₀, P s₀ → WP isa c s₀ fun s => (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧ Q s₀ s) :
    ∀ s, (mkK P Q pub).pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (mkK P Q pub).post s s' :=
  fun s hs => let ⟨t, s', he, h1, h2, h3⟩ := h s hs; ⟨t, s', he, ⟨h1, h2⟩, h3⟩

/-- The state a callee runs from, with the permissions it is given. -/
abbrev view (s : State) (rd wr : List Region) : State := s.callEntry.withRegions rd wr

theorem view_gpr' (s : State) (rd wr : List Region) {r : Reg} (hr : r ∉ linkRegs) :
    (view s rd wr).gpr r = s.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr]

/-- A call of a primitive without calls: what it keeps, and its postcondition. -/
theorem call_kept {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hn : c.noCalls = true) {s : State} {rd wr : List Region} (hpre : k.pre (view s rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept wr s s' → k.post (view s rd wr) (s'.withRegions rd wr) → Q s') :
    WP isa (.call n c) s Q :=
  WP.call hv hpre hc hw (fun s' hrd hwr hsp hf hcs _ hp => hQ s' ⟨hcs, hsp, hrd, hwr, hf⟩ hp) hn

theorem covers_append {rs ts ws : List Region} (h₁ : Covers rs ws) (h₂ : Covers ts ws) : Covers (rs ++ ts) ws :=
  fun x n ⟨q, hq, hc⟩ => (List.mem_append.mp hq).elim (fun h => h₁ x n ⟨q, h, hc⟩) (fun h => h₂ x n ⟨q, h, hc⟩)

theorem covers_cons' {r : Region} {rs ws : List Region} (h₁ : Covers [r] ws) (h₂ : Covers rs ws) :
    Covers (r :: rs) ws := covers_append (rs := [r]) h₁ h₂

theorem covers_nil' {ws : List Region} : Covers [] ws := fun _ _ ⟨_, h, _⟩ => absurd h List.not_mem_nil

theorem covers_wr {rs rd wr : List Region} (h : Covers rs wr) : Covers rs (rd ++ wr) := fun x n hi =>
  let ⟨r, hr, hc⟩ := h x n hi; ⟨r, List.mem_append_right _ hr, hc⟩

/-! ## `vg_mlkem_add` and `vg_mlkem_sub` -/

def kAdd : Contract isa := mkK Add.Pre
  (fun s₀ s => PolyIs s.mem (Add.F s₀) (add (polyAt s₀.mem (Add.F s₀)) (polyAt s₀.mem (Add.G s₀))))
  (regsEq [.r0, .r1])

def kSub : Contract isa := mkK Add.Pre
  (fun s₀ s => PolyIs s.mem (Add.F s₀) (sub (polyAt s₀.mem (Add.F s₀)) (polyAt s₀.mem (Add.G s₀))))
  (regsEq [.r0, .r1])

theorem kAdd_ok : ∀ s, kAdd.pre s → ∃ t s', Exec isa Impl.MlKem.Arm.add s t s' ∧ abiPreserved s s' ∧
    kAdd.post s s' :=
  mkK_ok fun _ hp => WP.mono (Add.loop_ok hp (Add.add_hb hp)) fun _ h =>
    ⟨h.pres, h.sp, Add.polyIs_of_inv h fun _ _ => rfl⟩

theorem kSub_ok : ∀ s, kSub.pre s → ∃ t s', Exec isa Impl.MlKem.Arm.sub s t s' ∧ abiPreserved s s' ∧
    kSub.post s s' :=
  mkK_ok fun _ hp => WP.mono (Add.loop_ok hp (Add.sub_hb hp)) fun _ h =>
    ⟨h.pres, h.sp, Add.polyIs_of_inv h fun _ _ => rfl⟩

/-- The arguments of `vg_mlkem_add` or `vg_mlkem_sub`: `f` and `g`. -/
structure AccArgs (s : State) (f g : BitVec 32) : Prop where
  r0 : s.gpr .r0 = f
  r1 : s.gpr .r1 = g
  disj : (polyRegion (State.addr f)).Disjoint (polyRegion (State.addr g))
  ff : f.toNat + 1024 ≤ 2 ^ 32
  fg : g.toNat + 1024 ≤ 2 ^ 32
  redF : Reduced s.mem (State.addr f)
  redG : Reduced s.mem (State.addr g)
  cw : Covers [polyRegion (State.addr f)] s.wr
  cr : Covers [polyRegion (State.addr g)] (s.rd ++ s.wr)

theorem acc_pre {s : State} {f g : BitVec 32} (h : AccArgs s f g) :
    Add.Pre (view s [polyRegion (State.addr g)] [polyRegion (State.addr f)]) := by
  have e0 := view_gpr' s [polyRegion (State.addr g)] [polyRegion (State.addr f)] (r := .r0) (by decide)
  have e1 := view_gpr' s [polyRegion (State.addr g)] [polyRegion (State.addr f)] (r := .r1) (by decide)
  rw [h.r0] at e0; rw [h.r1] at e1
  exact ⟨by simp only [Add.G, Add.pg, e1]; rfl, by simp only [Add.F, Add.pf, e0]; rfl,
    by simp only [Add.F, Add.G, Add.pf, Add.pg, e0, e1]; exact h.disj,
    by simp only [Add.pf, e0]; exact h.ff, by simp only [Add.pg, e1]; exact h.fg,
    by simp only [Add.F, Add.pf, e0]; exact h.redF, by simp only [Add.G, Add.pg, e1]; exact h.redG⟩

theorem add_call {s : State} {f g : BitVec 32} (h : AccArgs s f g) {Q : State → Prop}
    (hQ : ∀ s', Kept [polyRegion (State.addr f)] s s' →
      PolyIs s'.mem (State.addr f) (add (polyAt s.mem (State.addr f)) (polyAt s.mem (State.addr g))) → Q s') :
    WP isa (.call "vg_mlkem_add" Impl.MlKem.Arm.add) s Q :=
  call_kept (k := kAdd) kAdd_ok (by decide +kernel) (acc_pre h) (covers_append h.cr (covers_wr h.cw)) h.cw
    fun s' hk hp => hQ s' hk (by
      have e0 := view_gpr' s [polyRegion (State.addr g)] [polyRegion (State.addr f)] (r := .r0) (by decide)
      have e1 := view_gpr' s [polyRegion (State.addr g)] [polyRegion (State.addr f)] (r := .r1) (by decide)
      rw [h.r0] at e0; rw [h.r1] at e1
      simpa only [kAdd, mkK, Add.F, Add.G, Add.pf, Add.pg, e0, e1, State.withRegions_mem,
        State.callEntry_mem] using hp)

theorem sub_call {s : State} {f g : BitVec 32} (h : AccArgs s f g) {Q : State → Prop}
    (hQ : ∀ s', Kept [polyRegion (State.addr f)] s s' →
      PolyIs s'.mem (State.addr f) (sub (polyAt s.mem (State.addr f)) (polyAt s.mem (State.addr g))) → Q s') :
    WP isa (.call "vg_mlkem_sub" Impl.MlKem.Arm.sub) s Q :=
  call_kept (k := kSub) kSub_ok (by decide +kernel) (acc_pre h) (covers_append h.cr (covers_wr h.cw)) h.cw
    fun s' hk hp => hQ s' hk (by
      have e0 := view_gpr' s [polyRegion (State.addr g)] [polyRegion (State.addr f)] (r := .r0) (by decide)
      have e1 := view_gpr' s [polyRegion (State.addr g)] [polyRegion (State.addr f)] (r := .r1) (by decide)
      rw [h.r0] at e0; rw [h.r1] at e1
      simpa only [kSub, mkK, Add.F, Add.G, Add.pf, Add.pg, e0, e1, State.withRegions_mem,
        State.callEntry_mem] using hp)

/-! ## `vg_mlkem_multiply_ntts` -/

def kMul : Contract isa := mkK Mul.Pre
  (fun s₀ s => PolyIs s.mem (Mul.H s₀) (multiplyNTTs (Mul.fp s₀) (Mul.gp s₀))) (regsEq [.r0, .r1, .r2, .r3])

theorem kMul_ok : ∀ s, kMul.pre s → ∃ t s', Exec isa Impl.MlKem.Arm.multiplyNTTs s t s' ∧ abiPreserved s s' ∧
    kMul.post s s' :=
  mkK_ok fun _ hp => Mul.correct hp

/-- The arguments of `vg_mlkem_multiply_ntts`. -/
structure MulArgs (s : State) (h f g scr : BitVec 32) : Prop where
  r0 : s.gpr .r0 = h
  r1 : s.gpr .r1 = f
  r2 : s.gpr .r2 = g
  r3 : s.gpr .r3 = scr
  hf : (polyRegion (State.addr h)).Disjoint (polyRegion (State.addr f))
  hg : (polyRegion (State.addr h)).Disjoint (polyRegion (State.addr g))
  hs : (polyRegion (State.addr h)).Disjoint (polyRegion (State.addr scr))
  fs : (polyRegion (State.addr f)).Disjoint (polyRegion (State.addr scr))
  gs : (polyRegion (State.addr g)).Disjoint (polyRegion (State.addr scr))
  fh : h.toNat + 1024 ≤ 2 ^ 32
  ff : f.toNat + 1024 ≤ 2 ^ 32
  fg : g.toNat + 1024 ≤ 2 ^ 32
  fscr : scr.toNat + 1024 ≤ 2 ^ 32
  redF : Reduced s.mem (State.addr f)
  redG : Reduced s.mem (State.addr g)
  cw : Covers [polyRegion (State.addr h), polyRegion (State.addr scr)] s.wr
  cr : Covers [polyRegion (State.addr f), polyRegion (State.addr g)] (s.rd ++ s.wr)

abbrev mulRd (f g : BitVec 32) : List Region := [polyRegion (State.addr f), polyRegion (State.addr g)]
abbrev mulWr (h scr : BitVec 32) : List Region := [polyRegion (State.addr h), polyRegion (State.addr scr)]

theorem mul_pre {s : State} {h f g scr : BitVec 32} (a : MulArgs s h f g scr) :
    Mul.Pre (view s (mulRd f g) (mulWr h scr)) := by
  have e0 := view_gpr' s (mulRd f g) (mulWr h scr) (r := .r0) (by decide)
  have e1 := view_gpr' s (mulRd f g) (mulWr h scr) (r := .r1) (by decide)
  have e2 := view_gpr' s (mulRd f g) (mulWr h scr) (r := .r2) (by decide)
  have e3 := view_gpr' s (mulRd f g) (mulWr h scr) (r := .r3) (by decide)
  rw [a.r0] at e0; rw [a.r1] at e1; rw [a.r2] at e2; rw [a.r3] at e3
  exact ⟨by simp only [Mul.F, Mul.G, Mul.pf, Mul.pg, e1, e2]; rfl, by simp only [Mul.H, Mul.S, Mul.ph, Mul.ps, e0, e3]; rfl,
    by simp only [Mul.H, Mul.F, Mul.ph, Mul.pf, e0, e1]; exact a.hf,
    by simp only [Mul.H, Mul.G, Mul.ph, Mul.pg, e0, e2]; exact a.hg,
    by simp only [Mul.H, Mul.S, Mul.ph, Mul.ps, e0, e3]; exact a.hs,
    by simp only [Mul.F, Mul.S, Mul.pf, Mul.ps, e1, e3]; exact a.fs,
    by simp only [Mul.G, Mul.S, Mul.pg, Mul.ps, e2, e3]; exact a.gs,
    by simp only [Mul.ph, e0]; exact a.fh, by simp only [Mul.pf, e1]; exact a.ff,
    by simp only [Mul.pg, e2]; exact a.fg, by simp only [Mul.ps, e3]; exact a.fscr,
    by simp only [Mul.F, Mul.pf, e1]; exact a.redF, by simp only [Mul.G, Mul.pg, e2]; exact a.redG⟩

theorem mul_call {s : State} {h f g scr : BitVec 32} (a : MulArgs s h f g scr) {Q : State → Prop}
    (hQ : ∀ s', Kept (mulWr h scr) s s' →
      PolyIs s'.mem (State.addr h) (multiplyNTTs (polyAt s.mem (State.addr f)) (polyAt s.mem (State.addr g))) →
      Q s') :
    WP isa (.call "vg_mlkem_multiply_ntts" Impl.MlKem.Arm.multiplyNTTs) s Q :=
  call_kept (k := kMul) kMul_ok (by decide +kernel) (mul_pre a) (covers_append a.cr (covers_wr a.cw)) a.cw
    fun s' hk hp => hQ s' hk (by
      have e0 := view_gpr' s (mulRd f g) (mulWr h scr) (r := .r0) (by decide)
      have e1 := view_gpr' s (mulRd f g) (mulWr h scr) (r := .r1) (by decide)
      have e2 := view_gpr' s (mulRd f g) (mulWr h scr) (r := .r2) (by decide)
      rw [a.r0] at e0; rw [a.r1] at e1; rw [a.r2] at e2
      simpa only [kMul, mkK, Mul.H, Mul.fp, Mul.gp, Mul.F, Mul.G, Mul.ph, Mul.pf, Mul.pg, e0, e1, e2,
        State.withRegions_mem, State.callEntry_mem] using hp)

end VG.Proof.MlKem.Arm

end

end

/-! ### `MlKem.Arm.Lay`, which this module and modules that import it used -/

section

/-!
# ML-KEM on 32-bit ARM: the buffers of the top-level functions

The top-level functions work on a few buffers (`Lay`): `scratch` (buffer 0),
the 8 bytes below the stack pointer (buffer 1), and their arguments; the
contracts make them pairwise disjoint (`Lay.Ok`). A region is `l` bytes at
offset `o` of buffer `i` (`Lay.R`), and two regions are disjoint when a
computation on the offsets says so (`sepB`, decided by the kernel), so what a
call writes and what the proofs keep track of are lists of triples `(i, o,
l)`.

A state `s` in which the functions run their parts is `Ctx`: `r7` points to
`scratch`, and the stack pointer is the one of buffer 1. `Kept rs s s'`
(`Keccak.lean`) says what a part changes.
-/

@[expose] public section

namespace VG.Proof.MlKem.Arm

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem

/-- Buffers: their pointers and sizes. -/
structure Lay where
  ptr : Nat → BitVec 32
  sizes : List Nat

/-- Whether the regions `a` and `b` (buffer, offset, length) are within
their buffers and apart. -/
def sepB (sz : List Nat) (a b : Nat × Nat × Nat) : Bool :=
  a.1 < sz.length && b.1 < sz.length && a.2.1 + a.2.2 ≤ sz.getD a.1 0 && b.2.1 + b.2.2 ≤ sz.getD b.1 0 &&
    (a.1 != b.1 || a.2.1 + a.2.2 ≤ b.2.1 || b.2.1 + b.2.2 ≤ a.2.1)

/-- `a` is apart from every region of `W`. -/
def sepAll (sz : List Nat) (a : Nat × Nat × Nat) (W : List (Nat × Nat × Nat)) : Bool := W.all (sepB sz a)

namespace Lay

variable (L : Lay)

abbrev size (i : Nat) : Nat := L.sizes.getD i 0

/-- `l` bytes at offset `o` of buffer `i`. -/
abbrev R (i o l : Nat) : Region := ⟨State.addr (L.ptr i) + BitVec.ofNat 64 o, l⟩

/-- The regions of the triples `W`. -/
abbrev RL (W : List (Nat × Nat × Nat)) : List Region := W.map fun w => L.R w.1 w.2.1 w.2.2

/-- The buffers fit in the address space and are pairwise disjoint. -/
structure Ok : Prop where
  fit : ∀ i < L.sizes.length, (L.ptr i).toNat + L.size i ≤ 2 ^ 32
  disj : ∀ i < L.sizes.length, ∀ j < L.sizes.length, i ≠ j →
    (⟨State.addr (L.ptr i), L.size i⟩ : Region).Disjoint ⟨State.addr (L.ptr j), L.size j⟩

variable {L}

theorem R_sub {i o l : Nat} (h : o + l ≤ L.size i) :
    Region.Sub (L.R i o l) ⟨State.addr (L.ptr i), L.size i⟩ := by
  intro a ha
  simp only [Region.Contains] at ha ⊢
  bv_omega

theorem disj (hL : L.Ok) {i o l j o' l' : Nat} (h : sepB L.sizes (i, o, l) (j, o', l') = true) :
    (L.R i o l).Disjoint (L.R j o' l') := by
  simp only [sepB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨ha, hb⟩, hla⟩, hlb⟩, hs⟩ := h
  by_cases e : i = j
  · subst e
    have hf : (L.ptr i).toNat + L.sizes.getD i 0 ≤ 2 ^ 32 := hL.fit i ha
    have hs' : o + l ≤ o' ∨ o' + l' ≤ o := by
      rcases hs with (hs | hs) | hs
      · exact absurd rfl hs
      · exact .inl hs
      · exact .inr hs
    exact region_disj_off hs' hla hlb (addr_fit _ (by omega_using [hf]))
  · exact ((hL.disj _ ha _ hb e).sub_left (R_sub hla)).sub_right (R_sub hlb)

theorem disjAll (hL : L.Ok) {i o l : Nat} {W : List (Nat × Nat × Nat)} (h : sepAll L.sizes (i, o, l) W = true) :
    ∀ r ∈ L.RL W, (L.R i o l).Disjoint r := by
  intro r hr
  obtain ⟨⟨j, o', l'⟩, hw, rfl⟩ := List.mem_map.mp hr
  exact disj hL (List.all_eq_true.mp h _ hw)

/-- The address of a pointer into a buffer. -/
theorem addr_off (hL : L.Ok) {i o : Nat} (hi : i < L.sizes.length) (ho : o < L.size i) :
    State.addr (L.ptr i + BitVec.ofNat 32 o) = State.addr (L.ptr i) + BitVec.ofNat 64 o :=
  addr_add (by have := hL.fit i hi; omega_using [ho, this])

theorem regA_off (hL : L.Ok) {i o l : Nat} (hi : i < L.sizes.length) (ho : o < L.size i) :
    regA (L.ptr i + BitVec.ofNat 32 o) l = L.R i o l := by
  simp only [regA, addr_off hL hi ho]

theorem regA_zero (i l : Nat) : regA (L.ptr i) l = L.R i 0 l := by
  simp only [regA, Lay.R, add_ofNat_zero]

theorem fit_off (hL : L.Ok) {i o l : Nat} (hi : i < L.sizes.length) (h : o + l ≤ L.size i) (hl : 0 < l) :
    (L.ptr i + BitVec.ofNat 32 o).toNat + l ≤ 2 ^ 32 := by
  have := hL.fit i hi
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega_using [h, hl, this]),
    Nat.mod_eq_of_lt (by omega_using [h, hl, this])]
  omega_using [h, this]

/-- A part of a buffer the state may access. -/
theorem covers {i o l : Nat} {ws : List Region} (hin : ⟨State.addr (L.ptr i), L.size i⟩ ∈ ws)
    (h : o + l ≤ L.size i) : Covers [L.R i o l] ws := by
  intro x n ⟨q, hq, hc⟩
  rw [List.mem_singleton] at hq; subst hq
  refine ⟨_, hin, ?_⟩
  simp only [Region.Contains] at hc ⊢
  bv_omega

theorem polyIs_keep (hL : L.Ok) {W : List (Nat × Nat × Nat)} {m m' : Mem} (hf : Frame (L.RL W) m m')
    {i o : Nat} (h : sepAll L.sizes (i, o, 1024) W = true) {f : Poly}
    (hp : PolyIs m (State.addr (L.ptr i) + BitVec.ofNat 64 o) f) :
    PolyIs m' (State.addr (L.ptr i) + BitVec.ofNat 64 o) f :=
  polyIs_frame hf (disjAll hL h) hp

theorem bytes_keep (hL : L.Ok) {W : List (Nat × Nat × Nat)} {m m' : Mem} (hf : Frame (L.RL W) m m')
    {i o l : Nat} (h : sepAll L.sizes (i, o, l) W = true) (hl : l ≤ 2 ^ 64) :
    Spec.Sha3.bytesAt m' (State.addr (L.ptr i) + BitVec.ofNat 64 o) l =
      Spec.Sha3.bytesAt m (State.addr (L.ptr i) + BitVec.ofNat 64 o) l :=
  bytesAt_frame hf (disjAll hL h) hl

/-- `Ok` from the disjointness of the buffers `i < j`. -/
theorem ok_of (hfit : ∀ i < L.sizes.length, (L.ptr i).toNat + L.size i ≤ 2 ^ 32)
    (hd : ∀ i < L.sizes.length, ∀ j < L.sizes.length, i < j →
      (⟨State.addr (L.ptr i), L.size i⟩ : Region).Disjoint ⟨State.addr (L.ptr j), L.size j⟩) : L.Ok := by
  refine ⟨hfit, fun i hi j hj hij => ?_⟩
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact hd i hi j hj h
  · exact (hd j hj i hi h).symm

end Lay

/-! ## What changes -/

theorem Kept.refl (rs : List Region) (s : State) : Kept rs s s :=
  ⟨fun _ _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩

theorem Kept.trans {rs : List Region} {s₁ s₂ s₃ : State} (h₁ : Kept rs s₁ s₂) (h₂ : Kept rs s₂ s₃) :
    Kept rs s₁ s₃ :=
  ⟨fun r hr h => by rw [h₂.cs r hr h, h₁.cs r hr h], by rw [h₂.sp, h₁.sp], by rw [h₂.rd, h₁.rd],
    by rw [h₂.wr, h₁.wr], h₁.frame.trans h₂.frame⟩

theorem Kept.mono {rs rs' : List Region} {s s' : State} (h : Kept rs s s') (hs : ∀ r ∈ rs, r ∈ rs') :
    Kept rs' s s' :=
  ⟨h.cs, h.sp, h.rd, h.wr, h.frame.mono hs⟩

/-- The same, for regions given by triples. -/
theorem Kept.monoL {L : Lay} {W W' : List (Nat × Nat × Nat)} {s s' : State} (h : Kept (L.RL W) s s')
    (hs : ∀ w ∈ W, w ∈ W') : Kept (L.RL W') s s' :=
  h.mono fun r hr => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    exact List.mem_map.mpr ⟨w, hs w hw, rfl⟩

/-- A state that differs only in registers other than the callee-saved ones. -/
structure Only (s s' : State) : Prop where
  cs : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Only.kept {s s' : State} (h : Only s s') (rs : List Region) : Kept rs s s' :=
  ⟨h.cs, h.sp, h.rd, h.wr, by rw [h.mem]; exact Frame.refl _ _⟩

theorem Only.of_gpr {s : State} (g : Reg → BitVec 32) (h : ∀ r ∈ preserved, r ≠ .lr → g r = s.gpr r) :
    Only s { s with gpr := g } :=
  ⟨h, rfl, rfl, rfl, rfl⟩

/-! ## The setting of the parts -/

/-- `s` runs a part of a top-level function: `scratch` (buffer 0, writable,
of which the parts use the first 32768 bytes) in `r7`, and the 8 bytes
below the stack pointer (buffer 1). -/
structure Ctx (L : Lay) (s : State) : Prop where
  ok : L.Ok
  sz0 : 32768 ≤ L.size 0
  sz1 : L.size 1 = 8
  len : 2 ≤ L.sizes.length
  r7 : s.gpr .r7 = L.ptr 0
  sp8 : 8 ≤ s.sp.toNat
  sp : L.ptr 1 = s.sp - BitVec.ofNat 32 8
  cw : (⟨State.addr (L.ptr 0), L.size 0⟩ : Region) ∈ s.wr

theorem Ctx.bel {L : Lay} {s : State} (h : Ctx L s) : below s 8 = L.R 1 0 8 := by
  simp only [Lay.R, h.sp, addr_sub h.sp8, add_ofNat_zero]

theorem Ctx.kept {L : Lay} {s s' : State} (h : Ctx L s) {rs : List Region} (hk : Kept rs s s') : Ctx L s' :=
  ⟨h.ok, h.sz0, h.sz1, h.len, by rw [hk.cs .r7 (by decide) (by decide), h.r7], by rw [hk.sp]; exact h.sp8,
    by rw [hk.sp]; exact h.sp, by rw [hk.wr]; exact h.cw⟩

theorem Ctx.only {L : Lay} {s s' : State} (h : Ctx L s) (hk : Only s s') : Ctx L s' := h.kept (hk.kept [])

/-- A part of `scratch` the state may write. -/
theorem Ctx.cs {L : Lay} {s : State} (h : Ctx L s) {o l : Nat} (hl : o + l ≤ 32768) :
    Covers [L.R 0 o l] s.wr := Lay.covers h.cw (Nat.le_trans hl h.sz0)

theorem Ctx.addr {L : Lay} {s : State} (h : Ctx L s) {o : Nat} (ho : o < 32768) :
    State.addr (L.ptr 0 + BitVec.ofNat 32 o) = State.addr (L.ptr 0) + BitVec.ofNat 64 o :=
  Lay.addr_off h.ok (by have := h.len; omega_using [this]) (Nat.lt_of_lt_of_le ho h.sz0)

theorem Ctx.regAo {L : Lay} {s : State} (h : Ctx L s) {o : Nat} (ho : o < 32768) (l : Nat) :
    regA (L.ptr 0 + BitVec.ofNat 32 o) l = L.R 0 o l :=
  Lay.regA_off h.ok (by have := h.len; omega_using [this]) (Nat.lt_of_lt_of_le ho h.sz0)

theorem Ctx.fit {L : Lay} {s : State} (h : Ctx L s) : (L.ptr 0).toNat + 32768 ≤ 2 ^ 32 := by
  have := h.ok.fit 0 (by have := h.len; omega_using [this]); have := h.sz0; omega_arith

theorem Ctx.fitO {L : Lay} {s : State} (h : Ctx L s) {o l : Nat} (hl : o + l ≤ 32768) (hl0 : 0 < l) :
    (L.ptr 0 + BitVec.ofNat 32 o).toNat + l ≤ 2 ^ 32 :=
  Lay.fit_off h.ok (by have := h.len; omega_using [this]) (Nat.le_trans hl h.sz0) hl0

end VG.Proof.MlKem.Arm

end

end

/-!
# ML-KEM-768 on 32-bit ARM: the hash routine

`hash` (`Impl/MlKem/Arm/Top.lean`) computes the sponge of the concatenation of
its input pieces, and writes consecutive output to its output pieces
(`hash_ok`): from the all-zero state (`repr_nil`), each `absorb` continues the
message from the position the previous one returned, the padding, and each
`squeeze` continues the output. It changes only the Keccak state and working
space, the outputs, the 8 bytes below the stack pointer, and registers that
are not callee-saved (or `lr`).
-/

@[expose] public section

namespace VG.Proof.MlKem.Arm

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.Sha3 (Repr stateAt bytesAt absorb pad squeezeFrom rates)

theorem pres_ne {r : Reg} (h : r ∈ preserved) (hl : r ≠ .lr) :
    r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
  revert r; decide

theorem enc200 : encodable (BitVec.ofNat 32 200) = true := by decide
theorem enc0 : encodable (BitVec.ofNat 32 0) = true := by decide

/-- The arguments of an `absorb` or a `squeeze`. -/
theorem kargs_ok {s : State} {rate : Nat} (first : Bool) {p : Piece} (hb : p.base ∈ preserved ∧ p.base ≠ .lr)
    (hre : encodable (BitVec.ofNat 32 rate) = true) (hoe : encodable (BitVec.ofNat 32 p.off) = true)
    (hle : encodable (BitVec.ofNat 32 p.len) = true) :
    WP isa (.block (keccakArgs rate first ++ pieceArgs p)) s fun s' => Only s s' ∧
      s'.gpr .r0 = s.gpr .r7 ∧ s'.gpr .r1 = BitVec.ofNat 32 rate ∧
      s'.gpr .r2 = (if first then BitVec.ofNat 32 0 else s.gpr .r0) ∧
      s'.gpr .r3 = s.gpr p.base + BitVec.ofNat 32 p.off ∧ s'.gpr .r12 = BitVec.ofNat 32 p.len ∧
      s'.gpr .lr = s.gpr .r7 + BitVec.ofNat 32 200 := by
  obtain ⟨n0, n1, n2, n3, n12⟩ := pres_ne hb.1 hb.2
  have nl := hb.2
  cases first <;>
  · run_block [keccakArgs, pieceArgs, ptrTo, hre, hoe, hle, enc200, enc0, n0, n1, n2, n3, n12, nl]
    refine ⟨Only.of_gpr _ fun r hr hl => ?_, trivial⟩
    obtain ⟨m0, m1, m2, m3, m12⟩ := pres_ne hr hl
    simp only [m0, m1, m2, m3, m12, hl, ite_false]

/-- The arguments of a `pad`. -/
theorem pargs_ok {s : State} {rate sfx : Nat} (hre : encodable (BitVec.ofNat 32 rate) = true)
    (hse : encodable (BitVec.ofNat 32 sfx) = true) :
    WP isa (.block (keccakArgs rate false ++ ([.mov .r3 (.imm (BitVec.ofNat 32 sfx))] : List Instr))) s
      fun s' => Only s s' ∧ s'.gpr .r0 = s.gpr .r7 ∧ s'.gpr .r1 = BitVec.ofNat 32 rate ∧
        s'.gpr .r2 = s.gpr .r0 ∧ s'.gpr .r3 = BitVec.ofNat 32 sfx ∧ s'.gpr .lr = s.gpr .r7 + BitVec.ofNat 32 200 := by
  run_block [keccakArgs, ptrTo, hre, hse, enc200]
  refine ⟨Only.of_gpr _ fun r hr hl => ?_, trivial⟩
  obtain ⟨m0, m1, m2, m3, m12⟩ := pres_ne hr hl
  simp only [m0, m1, m2, m3, hl, ite_false]

/-! ## Regions in `scratch` and below the stack pointer -/

theorem Ctx.sep00 {L : Lay} {s : State} (hc : Ctx L s) {o l o' l' : Nat} (h₁ : o + l ≤ 32768)
    (h₂ : o' + l' ≤ 32768) (h : o + l ≤ o' ∨ o' + l' ≤ o) : sepB L.sizes (0, o, l) (0, o', l') = true := by
  have := hc.len; have := hc.sz0
  simp only [sepB, Lay.size] at this ⊢
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, not_true_eq_false,
    false_or]
  omega_arith

theorem Ctx.sep01 {L : Lay} {s : State} (hc : Ctx L s) {o l o' l' : Nat} (h₁ : o + l ≤ 32768)
    (h₂ : o' + l' ≤ 8) : sepB L.sizes (0, o, l) (1, o', l') = true := by
  have h0 := hc.len; have h1 := hc.sz0; have h2 := hc.sz1
  simp only [Lay.size] at h1 h2
  simp only [sepB, h2, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
  omega_using [h₁, h₂, h0, h1]

theorem sepB_symm {sz : List Nat} {a b : Nat × Nat × Nat} (h : sepB sz a b = true) : sepB sz b a = true := by
  simp only [sepB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h ⊢
  omega_using [h]

/-- The regions of the sponge functions: the state, the working space and the stack arguments. -/
abbrev kRegs : List (Nat × Nat × Nat) := [(0, 0, 200), (0, 200, 640), (1, 0, 8)]

theorem Ctx.kregs {L : Lay} {s : State} (hc : Ctx L s) :
    regA (L.ptr 0) 200 = L.R 0 0 200 ∧ regA (L.ptr 0 + BitVec.ofNat 32 200) 640 = L.R 0 200 640 ∧
      below s 8 = L.R 1 0 8 :=
  ⟨Lay.regA_zero _ _, hc.regAo (by decide) _, hc.bel⟩

/-! ## Pieces -/

/-- Piece `p` is the region `L.R (idx p.base) p.off p.len`, which the state
may read (or write, if `w`), apart from the sponge's regions. -/
structure PieceOk (L : Lay) (idx : Reg → Nat) (s : State) (w : Bool) (p : Piece) : Prop where
  base : p.base ∈ preserved ∧ p.base ≠ .lr
  ptr : s.gpr p.base = L.ptr (idx p.base)
  oenc : encodable (BitVec.ofNat 32 p.off) = true
  lenc : encodable (BitVec.ofNat 32 p.len) = true
  pos : 0 < p.len
  lt : p.off + p.len < 2 ^ 32
  sep : sepAll L.sizes (idx p.base, p.off, p.len) kRegs = true
  cov : (⟨State.addr (L.ptr (idx p.base)), L.size (idx p.base)⟩ : Region) ∈ (if w then s.wr else s.rd ++ s.wr)

/-- The region of a piece. -/
abbrev Lay.P (L : Lay) (idx : Reg → Nat) (p : Piece) : Region := L.R (idx p.base) p.off p.len

/-- The bytes of a piece. -/
abbrev Lay.pb (L : Lay) (idx : Reg → Nat) (m : Mem) (p : Piece) : List Byte :=
  bytesAt m (State.addr (L.ptr (idx p.base)) + BitVec.ofNat 64 p.off) p.len

theorem sepAll_head {sz : List Nat} {a w : Nat × Nat × Nat} {W : List (Nat × Nat × Nat)}
    (h : sepAll sz a (w :: W) = true) : sepB sz a w = true := by
  simp only [sepAll, List.all_cons, Bool.and_eq_true] at h; exact h.1

theorem sepB_bounds {sz : List Nat} {i o l : Nat} {w : Nat × Nat × Nat} (h : sepB sz (i, o, l) w = true) :
    i < sz.length ∧ o + l ≤ sz.getD i 0 := by
  simp only [sepB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.2⟩

theorem PieceOk.bounds {L : Lay} {idx : Reg → Nat} {s : State} {w : Bool} {p : Piece} (h : PieceOk L idx s w p) :
    idx p.base < L.sizes.length ∧ p.off + p.len ≤ L.size (idx p.base) :=
  sepB_bounds (sepAll_head h.sep)

theorem PieceOk.sepK {L : Lay} {idx : Reg → Nat} {s : State} {w : Bool} {p : Piece} (h : PieceOk L idx s w p) :
    sepB L.sizes (idx p.base, p.off, p.len) (0, 0, 200) = true ∧
      sepB L.sizes (idx p.base, p.off, p.len) (0, 200, 640) = true ∧
      sepB L.sizes (idx p.base, p.off, p.len) (1, 0, 8) = true := by
  have := h.sep
  simp only [sepAll, List.all_cons, List.all_nil, Bool.and_eq_true, Bool.and_true] at this
  exact ⟨this.1, this.2.1, this.2.2⟩

theorem PieceOk.regA {L : Lay} {idx : Reg → Nat} {s : State} {w : Bool} {p : Piece} (hL : L.Ok)
    (h : PieceOk L idx s w p) : regA (L.ptr (idx p.base) + BitVec.ofNat 32 p.off) p.len = L.P idx p :=
  Lay.regA_off hL h.bounds.1 (by have := h.bounds.2; have := h.pos; omega_arith)

theorem RL_kRegs (L : Lay) : L.RL kRegs = [L.R 0 0 200, L.R 0 200 640, L.R 1 0 8] := rfl

/-- The position the next call starts from: 0 first, or the one the last
call returned. -/
def Pos (first : Bool) (s : State) : Nat := if first then 0 else (s.gpr .r0).toNat

theorem pos_r2 (first : Bool) (s : State) :
    (if first then BitVec.ofNat 32 0 else s.gpr .r0) = BitVec.ofNat 32 (Pos first s) := by
  cases first
  · simp only [Pos, Bool.false_eq_true, ite_false, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rfl

theorem rate_pos {rate : Nat} (h : rate ∈ rates) : 0 < rate := by
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at h; omega_using [h]

/-- The registers and permissions of `s₀`. -/
structure Rg (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  cs : ∀ r ∈ preserved, r ≠ .lr → s.gpr r = s₀.gpr r

theorem Kept.rg {rs : List Region} {s₀ s : State} (h : Kept rs s₀ s) : Rg s₀ s := ⟨h.rd, h.wr, h.sp, h.cs⟩

theorem Rg.kept {rs : List Region} {s₀ s s' : State} (h : Rg s₀ s) (hk : Kept rs s s') : Rg s₀ s' :=
  ⟨by rw [hk.rd, h.rd], by rw [hk.wr, h.wr], by rw [hk.sp, h.sp],
    fun r hr hl => by rw [hk.cs r hr hl, h.cs r hr hl]⟩

theorem Rg.ctx {L : Lay} {s₀ s : State} (hc : Ctx L s₀) (h : Rg s₀ s) : Ctx L s :=
  ⟨hc.ok, hc.sz0, hc.sz1, hc.len, by rw [h.cs .r7 (by decide) (by decide), hc.r7], by rw [h.sp]; exact hc.sp8,
    by rw [h.sp]; exact hc.sp, by rw [h.wr]; exact hc.cw⟩

theorem PieceOk.covR {L : Lay} {idx : Reg → Nat} {s₀ s : State} {p : Piece} (h : PieceOk L idx s₀ false p)
    (hg : Rg s₀ s) : Covers [L.P idx p] (s.rd ++ s.wr) := by
  have := h.cov
  simp only [Bool.false_eq_true, ite_false] at this
  rw [hg.rd, hg.wr]
  exact Lay.covers this h.bounds.2

theorem PieceOk.covW {L : Lay} {idx : Reg → Nat} {s₀ s : State} {p : Piece} (h : PieceOk L idx s₀ true p)
    (hg : Rg s₀ s) : Covers [L.P idx p] s.wr := by
  have := h.cov
  simp only [ite_true] at this
  rw [hg.wr]
  exact Lay.covers this h.bounds.2

theorem PieceOk.fit {L : Lay} {idx : Reg → Nat} {s : State} {w : Bool} {p : Piece} (hL : L.Ok)
    (h : PieceOk L idx s w p) : (L.ptr (idx p.base) + BitVec.ofNat 32 p.off).toNat + p.len ≤ 2 ^ 32 :=
  Lay.fit_off hL h.bounds.1 h.bounds.2 h.pos

theorem PieceOk.len32 {L : Lay} {idx : Reg → Nat} {s : State} {w : Bool} {p : Piece} (h : PieceOk L idx s w p)
    (_hL : L.Ok) : p.len < 2 ^ 32 := by
  have := h.lt; omega_using [this]

theorem PieceOk.addr {L : Lay} {idx : Reg → Nat} {s : State} {w : Bool} {p : Piece} (hL : L.Ok)
    (h : PieceOk L idx s w p) :
    State.addr (L.ptr (idx p.base) + BitVec.ofNat 32 p.off) = State.addr (L.ptr (idx p.base)) + BitVec.ofNat 64 p.off :=
  Lay.addr_off hL h.bounds.1 (by have := h.bounds.2; have := h.pos; omega_arith)

theorem covers_kregs {L : Lay} {s : State} (hc : Ctx L s) :
    Covers [regA (L.ptr 0) 200, regA (L.ptr 0 + BitVec.ofNat 32 200) 640] s.wr := by
  rw [hc.kregs.1, hc.kregs.2.1]
  exact covers_cons' (hc.cs (by decide)) (covers_cons' (hc.cs (by decide)) covers_nil')

/-! ## The absorbs -/

theorem absorbs_ok {L : Lay} {idx : Reg → Nat} {rate : Nat} (hrate : rate ∈ rates)
    (hre : encodable (BitVec.ofNat 32 rate) = true) {s₀ : State} (hc : Ctx L s₀) :
    ∀ (ps : List Piece) (first : Bool) (s : State) (msg : List Byte),
      (∀ p ∈ ps, PieceOk L idx s₀ false p) →
      Kept (L.RL kRegs) s₀ s → Repr s.mem (State.addr (L.ptr 0)) rate msg →
      Pos first s = msg.length % rate →
      WP isa (absorbs rate first ps) s fun s' =>
        Kept (L.RL kRegs) s₀ s' ∧
        Repr s'.mem (State.addr (L.ptr 0)) rate (msg ++ (ps.map (L.pb idx s₀.mem)).flatten) ∧
        Pos (first && ps.isEmpty) s' = (msg ++ (ps.map (L.pb idx s₀.mem)).flatten).length % rate := by
  intro ps
  induction ps with
  | nil => exact fun first s msg _ hk hr hpos => WP.block_nil ⟨hk, by simpa using hr, by simpa using hpos⟩
  | cons p ps ih =>
    intro first s msg hps hk hr hpos
    have hp := hps p (List.mem_cons_self ..)
    have hL := hc.ok
    have rpos := rate_pos hrate
    have hcs := hk.rg.ctx hc
    refine WP.seq (WP.mono (kargs_ok first hp.base hre hp.oenc hp.lenc) fun s₁ ⟨o₁, g0, g1, g2, g3, g12, glr⟩ => ?_)
    have hc₁ := hcs.only o₁
    have gb : s.gpr p.base = L.ptr (idx p.base) := by rw [hk.cs _ hp.base.1 hp.base.2, hp.ptr]
    rw [hcs.r7] at g0 glr
    rw [gb] at g3
    rw [pos_r2] at g2
    have hpos' : Pos first s < rate := by rw [hpos]; exact Nat.mod_lt _ rpos
    obtain ⟨e0, e1, e2⟩ := hc₁.kregs
    have er := hp.regA hL
    have hg₁ : Rg s₀ s₁ := hk.rg.kept (o₁.kept [])
    have hA : AbsorbArgs s₁ (L.ptr 0) (L.ptr 0 + BitVec.ofNat 32 200) (L.ptr (idx p.base) + BitVec.ofNat 32 p.off)
        rate (Pos first s) p.len := by
      refine ⟨g0, g1, g2, g3, g12, glr, hrate, hpos', hp.len32 hL, hc₁.sp8, fit_le (by decide) hc.fit,
        hp.fit hL, hc.fitO (by decide) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, covers_kregs hc₁, ?_⟩
      · rw [e0, e1]; exact Lay.disj hL (hc.sep00 (by decide) (by decide) (by decide))
      · rw [er, e0]; exact Lay.disj hL hp.sepK.1
      · rw [er, e1]; exact Lay.disj hL hp.sepK.2.1
      · rw [e2, e0]; exact Lay.disj hL (sepB_symm (hc.sep01 (by decide) (by decide)))
      · rw [e2, e1]; exact Lay.disj hL (sepB_symm (hc.sep01 (by decide) (by decide)))
      · rw [e2, er]; exact Lay.disj hL (sepB_symm hp.sepK.2.2)
      · rw [er]; exact hp.covR hg₁
    refine WP.seq (absorb_ok hA fun s₂ k₂ r₂ ret₂ => ?_)
    rw [e0, e1, e2, ← RL_kRegs] at k₂
    have hk₂ : Kept (L.RL kRegs) s₀ s₂ := hk.trans ((o₁.kept _).trans k₂)
    have eb : bytesAt s₁.mem (State.addr (L.ptr (idx p.base) + BitVec.ofNat 32 p.off)) p.len = L.pb idx s₀.mem p := by
      rw [o₁.mem, hp.addr hL]
      exact Lay.bytes_keep hL hk.frame hp.sep (by have := hp.len32 hL; omega_using [this])
    have rep := r₂ msg (by rw [o₁.mem]; exact hr) hpos
    rw [eb] at rep
    refine WP.mono (ih false s₂ (msg ++ L.pb idx s₀.mem p) (fun q hq => hps q (List.mem_cons_of_mem _ hq)) hk₂ rep
      ?_) fun s' ⟨k', r', p'⟩ => ?_
    · show (s₂.gpr .r0).toNat = _
      rw [ret₂, hpos, List.length_append, bytesAt_length, Nat.mod_add_mod]
    · simp only [List.map_cons, List.flatten_cons, List.isEmpty_cons, Bool.and_false, ← List.append_assoc]
        at r' p' ⊢
      exact ⟨k', r', p'⟩

/-! ## The squeezes -/

/-- The triple of a piece. -/
abbrev trip (idx : Reg → Nat) (p : Piece) : Nat × Nat × Nat := (idx p.base, p.off, p.len)

/-- The output pieces hold consecutive output from the state `P`, from
position `c` on. -/
def Outs (L : Lay) (idx : Reg → Nat) (m : Mem) (rate : Nat) (P : Spec.Sha3.State) : Nat → List Piece → Prop
  | _, [] => True
  | c, p :: ps => L.pb idx m p = squeezeFrom rate P c p.len ∧ Outs L idx m rate P (c + p.len) ps

theorem sepAll_append {sz : List Nat} {a : Nat × Nat × Nat} {W W' : List (Nat × Nat × Nat)}
    (h : sepAll sz a W = true) (h' : sepAll sz a W' = true) : sepAll sz a (W ++ W') = true := by
  simp only [sepAll, List.all_append, Bool.and_eq_true] at h h' ⊢; exact ⟨h, h'⟩

theorem sepAll_map {α : Type} {sz : List Nat} {a : Nat × Nat × Nat} {ps : List α} {f : α → Nat × Nat × Nat}
    (h : ∀ q ∈ ps, sepB sz a (f q) = true) : sepAll sz a (ps.map f) = true := by
  simp only [sepAll, List.all_map, List.all_eq_true, Function.comp]; exact h

theorem squeezes_ok {L : Lay} {idx : Reg → Nat} {rate : Nat} (hrate : rate ∈ rates)
    (hre : encodable (BitVec.ofNat 32 rate) = true) {s₀ : State} (hc : Ctx L s₀) {P : Spec.Sha3.State} :
    ∀ (ps : List Piece) (first : Bool) (s : State) (c : Nat),
      (∀ p ∈ ps, PieceOk L idx s₀ true p) → ps.Pairwise (fun p q => sepB L.sizes (trip idx p) (trip idx q) = true) →
      Rg s₀ s → Pos first s ≤ rate →
      (∀ d, squeezeFrom rate (stateAt s.mem (State.addr (L.ptr 0))) (Pos first s) d = squeezeFrom rate P c d) →
      WP isa (squeezes rate first ps) s fun s' =>
        Kept (L.RL (kRegs ++ ps.map (trip idx))) s s' ∧ Outs L idx s'.mem rate P c ps := by
  intro ps
  induction ps with
  | nil => exact fun _ s _ _ _ _ _ _ => WP.block_nil ⟨Kept.refl _ _, trivial⟩
  | cons p ps ih =>
    intro first s c hps hpw hg hple hcont
    have hp := hps p (List.mem_cons_self ..)
    have hL := hc.ok
    have rpos := rate_pos hrate
    have rle := rates_lt hrate
    have hcs := hg.ctx hc
    refine WP.seq (WP.mono (kargs_ok first hp.base hre hp.oenc hp.lenc) fun s₁ ⟨o₁, g0, g1, g2, g3, g12, glr⟩ => ?_)
    have hc₁ := hcs.only o₁
    have gb : s.gpr p.base = L.ptr (idx p.base) := by rw [hg.cs _ hp.base.1 hp.base.2, hp.ptr]
    rw [hcs.r7] at g0 glr
    rw [gb] at g3
    rw [pos_r2] at g2
    obtain ⟨e0, e1, e2⟩ := hc₁.kregs
    have er := hp.regA hL
    have hg₁ : Rg s₀ s₁ := hg.kept (o₁.kept [])
    have hS : SqueezeArgs s₁ (L.ptr 0) (L.ptr 0 + BitVec.ofNat 32 200) (L.ptr (idx p.base) + BitVec.ofNat 32 p.off)
        rate (Pos first s) p.len := by
      refine ⟨g0, g1, g2, g3, g12, glr, hrate, hple, hp.len32 hL, hc₁.sp8, fit_le (by decide) hc.fit,
        hp.fit hL, hc.fitO (by decide) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [e0, er]; exact Lay.disj hL (sepB_symm hp.sepK.1)
      · rw [e0, e1]; exact Lay.disj hL (hc.sep00 (by decide) (by decide) (by decide))
      · rw [er, e1]; exact Lay.disj hL hp.sepK.2.1
      · rw [e2, e0]; exact Lay.disj hL (sepB_symm (hc.sep01 (by decide) (by decide)))
      · rw [e2, er]; exact Lay.disj hL (sepB_symm hp.sepK.2.2)
      · rw [e2, e1]; exact Lay.disj hL (sepB_symm (hc.sep01 (by decide) (by decide)))
      · rw [e0, er, e1]
        exact covers_cons' (hc₁.cs (by decide)) (covers_cons' (hp.covW hg₁)
          (covers_cons' (hc₁.cs (by decide)) covers_nil'))
    refine WP.seq (squeeze_ok hS fun s₂ k₂ b₂ r₂ n₂ => ?_)
    rw [e0, er, e1, e2] at k₂
    have out₂ : L.pb idx s₂.mem p = squeezeFrom rate P c p.len := by
      show bytesAt s₂.mem (State.addr (L.ptr (idx p.base)) + BitVec.ofNat 64 p.off) p.len = _
      rw [← hp.addr hL, b₂, o₁.mem, hcont]
    have cont₂ : ∀ d, squeezeFrom rate (stateAt s₂.mem (State.addr (L.ptr 0))) (Pos false s₂) d =
        squeezeFrom rate P (c + p.len) d := fun d => by
      rw [show Pos false s₂ = (s₂.gpr .r0).toNat from rfl, n₂, o₁.mem]
      exact squeezeFrom_shift rpos (by omega_using [rle]) hcont p.len d
    have pw := List.pairwise_cons.mp hpw
    have hg₂ : Rg s₀ s₂ := hg₁.kept k₂
    refine WP.mono (ih false s₂ (c + p.len) (fun q hq => hps q (List.mem_cons_of_mem _ hq)) pw.2 hg₂ r₂ cont₂)
      fun s' ⟨k', o'⟩ => ⟨?_, ?_, o'⟩
    · refine (o₁.kept _).trans ((k₂.mono fun r hr => ?_).trans (k'.monoL fun w hw => ?_))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        simp only [Lay.RL, List.map_append, List.map_cons, List.mem_append, List.mem_cons, List.mem_map]
        rcases hr with rfl | rfl | rfl | rfl <;> simp
      · simp only [List.mem_append, List.mem_map, List.map_cons, List.mem_cons] at hw ⊢
        rcases hw with hw | ⟨q, hq, rfl⟩
        · exact .inl hw
        · exact .inr (.inr ⟨q, hq, rfl⟩)
    · rw [← out₂]
      exact Lay.bytes_keep hL k'.frame (sepAll_append hp.sep (sepAll_map pw.1)) (by have := hp.len32 hL; omega_using [this])

/-! ## The whole hash -/

theorem zeroState_ok {L : Lay} {s : State} (hc : Ctx L s) :
    WP isa (.block (zeroState .r7)) s fun s' =>
      Kept (L.RL [(0, 0, 200)]) s s' ∧ stateAt s'.mem (State.addr (L.ptr 0)) = Spec.Sha3.zero := by
  rw [zeroState, ← List.singleton_append, WP.block_append_iff]
  have hmov : WP isa (.block [.mov .r12 (.imm 0)]) s fun s₁ => s₁.gpr = (s.setReg .r12 0).gpr ∧
      s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.sp = s.sp := by
    run_block []
  refine WP.mono hmov fun s₁ ⟨g, m, rd, wr, sp⟩ => ?_
  have e7 : s₁.gpr .r7 = L.ptr 0 := by rw [g]; simp [State.setReg, hc.r7]
  refine WP.mono (Sample.zeroWords_ok .r7 (s₁ := s₁) (by rw [g]; simp [State.setReg])
    (by rw [e7]; exact fit_le (by decide) hc.fit) fun k hk => by
      rw [e7, wr]
      exact hc.cs (o := 4 * k) (l := 4) (by omega_using [hk]) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩)
    fun s₂ h₂ => ?_
  have hf := h₂.frame
  have hz := h₂.zero
  rw [e7] at hf hz
  refine ⟨⟨fun r hr hl => ?_, by rw [h₂.sp, sp], by rw [h₂.rd, rd], by rw [h₂.wr, wr], ?_⟩,
    Sample.stateAt_zero hz⟩
  · rw [h₂.gpr, g]
    obtain ⟨-, -, -, -, n12⟩ := pres_ne hr hl
    simp [State.setReg, n12]
  · rw [← m]
    refine hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
    rw [List.mem_singleton] at hr; subst hr
    show Region.Sub _ (L.R 0 0 200)
    rw [← Lay.regA_zero]; exact fun _ h => h

theorem sfx8 {sfx : Nat} (h : sfx < 256) : (BitVec.ofNat 32 sfx).setWidth 8 = BitVec.ofNat 8 sfx := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [h] : sfx < 2 ^ 32)]

/-- `hash`: the sponge of the pieces `ins`, output into the pieces `outs`. -/
theorem hash_ok {L : Lay} {idx : Reg → Nat} {rate sfx : Nat} (hrate : rate ∈ rates)
    (hre : encodable (BitVec.ofNat 32 rate) = true) (hse : encodable (BitVec.ofNat 32 sfx) = true)
    (hsfx : sfx < 256) {s₀ : State} (hc : Ctx L s₀) {ins outs : List Piece} (hne : ins ≠ [])
    (hin : ∀ p ∈ ins, PieceOk L idx s₀ false p) (hout : ∀ p ∈ outs, PieceOk L idx s₀ true p)
    (hpw : outs.Pairwise (fun p q => sepB L.sizes (trip idx p) (trip idx q) = true)) :
    WP isa (hash rate sfx ins outs) s₀ fun s' =>
      Kept (L.RL (kRegs ++ outs.map (trip idx))) s₀ s' ∧
      Outs L idx s'.mem rate (absorb rate (pad rate (BitVec.ofNat 8 sfx) (ins.map (L.pb idx s₀.mem)).flatten)) 0
        outs := by
  have hL := hc.ok
  have rpos := rate_pos hrate
  refine WP.seq (WP.mono (zeroState_ok hc) fun s₁ ⟨k₁, z₁⟩ => ?_)
  refine WP.seq (WP.mono (absorbs_ok hrate hre hc ins true s₁ [] hin (k₁.monoL (by simp)) (repr_nil z₁)
    (by simp [Pos])) fun s₂ ⟨k₂, r₂, p₂⟩ => ?_)
  have hie : ins.isEmpty = false := by cases ins; exact absurd rfl hne; rfl
  rw [hie, Bool.and_false] at p₂
  rw [List.nil_append] at r₂ p₂
  have hc₂ := k₂.rg.ctx hc
  refine WP.seq (WP.mono (pargs_ok hre hse) fun s₃ ⟨o₃, g0, g1, g2, g3, glr⟩ => ?_)
  have hc₃ := hc₂.only o₃
  rw [hc₂.r7] at g0 glr
  obtain ⟨e0, e1, e2⟩ := hc₃.kregs
  have hP : PadArgs s₃ (L.ptr 0) (L.ptr 0 + BitVec.ofNat 32 200) rate (s₂.gpr .r0).toNat (BitVec.ofNat 32 sfx) := by
    refine ⟨g0, g1, by rw [g2, BitVec.ofNat_toNat, BitVec.setWidth_eq], g3, glr, hrate,
      by rw [show (s₂.gpr .r0).toNat = Pos false s₂ from rfl, p₂]; exact Nat.mod_lt _ rpos, hc₃.sp8,
      fit_le (by decide) hc.fit, hc.fitO (by decide) (by decide), ?_, ?_, ?_, covers_kregs hc₃⟩
    · rw [e0, e1]; exact Lay.disj hL (hc.sep00 (by decide) (by decide) (by decide))
    · rw [e2, e0]; exact Lay.disj hL (sepB_symm (hc.sep01 (by decide) (by decide)))
    · rw [e2, e1]; exact Lay.disj hL (sepB_symm (hc.sep01 (by decide) (by decide)))
  refine WP.seq (pad_ok hP fun s₄ k₄ st₄ => ?_)
  rw [e0, e1, e2, ← RL_kRegs] at k₄
  have st := st₄ _ (by rw [o₃.mem]; exact r₂) p₂
  rw [sfx8 hsfx] at st
  have hg₄ : Rg s₀ s₄ := (k₂.trans ((o₃.kept _).trans k₄)).rg
  refine WP.mono (squeezes_ok hrate hre hc outs true s₄ 0 hout hpw hg₄ (Nat.zero_le _)
    (fun d => by rw [st]; rfl)) fun s' ⟨k', o'⟩ => ⟨?_, o'⟩
  refine ((k₂.trans ((o₃.kept _).trans k₄)).monoL fun w hw => List.mem_append_left _ hw).trans k'

/-! ## The arguments of the sponge functions, for the constant-time proofs -/

theorem absorbArgs_of {L : Lay} {idx : Reg → Nat} {rate : Nat} (hrate : rate ∈ rates) {s₀ s₁ : State}
    {p : Piece} (hc₁ : Ctx L s₁) (hg : Rg s₀ s₁) (hp : PieceOk L idx s₀ false p) {pos : Nat} (hpos : pos < rate)
    (g0 : s₁.gpr .r0 = L.ptr 0) (g1 : s₁.gpr .r1 = BitVec.ofNat 32 rate) (g2 : s₁.gpr .r2 = BitVec.ofNat 32 pos)
    (g3 : s₁.gpr .r3 = L.ptr (idx p.base) + BitVec.ofNat 32 p.off) (g12 : s₁.gpr .r12 = BitVec.ofNat 32 p.len)
    (glr : s₁.gpr .lr = L.ptr 0 + BitVec.ofNat 32 200) :
    AbsorbArgs s₁ (L.ptr 0) (L.ptr 0 + BitVec.ofNat 32 200) (L.ptr (idx p.base) + BitVec.ofNat 32 p.off)
      rate pos p.len := by
  have hL := hc₁.ok
  obtain ⟨e0, e1, e2⟩ := hc₁.kregs
  have er := hp.regA hL
  refine ⟨g0, g1, g2, g3, g12, glr, hrate, hpos, hp.len32 hL, hc₁.sp8, fit_le (by decide) hc₁.fit,
    hp.fit hL, hc₁.fitO (by decide) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, covers_kregs hc₁, ?_⟩
  · rw [e0, e1]; exact Lay.disj hL (hc₁.sep00 (by decide) (by decide) (by decide))
  · rw [er, e0]; exact Lay.disj hL hp.sepK.1
  · rw [er, e1]; exact Lay.disj hL hp.sepK.2.1
  · rw [e2, e0]; exact Lay.disj hL (sepB_symm (hc₁.sep01 (by decide) (by decide)))
  · rw [e2, e1]; exact Lay.disj hL (sepB_symm (hc₁.sep01 (by decide) (by decide)))
  · rw [e2, er]; exact Lay.disj hL (sepB_symm hp.sepK.2.2)
  · rw [er]; exact hp.covR hg

theorem squeezeArgs_of {L : Lay} {idx : Reg → Nat} {rate : Nat} (hrate : rate ∈ rates) {s₀ s₁ : State}
    {p : Piece} (hc₁ : Ctx L s₁) (hg : Rg s₀ s₁) (hp : PieceOk L idx s₀ true p) {pos : Nat} (hpos : pos ≤ rate)
    (g0 : s₁.gpr .r0 = L.ptr 0) (g1 : s₁.gpr .r1 = BitVec.ofNat 32 rate) (g2 : s₁.gpr .r2 = BitVec.ofNat 32 pos)
    (g3 : s₁.gpr .r3 = L.ptr (idx p.base) + BitVec.ofNat 32 p.off) (g12 : s₁.gpr .r12 = BitVec.ofNat 32 p.len)
    (glr : s₁.gpr .lr = L.ptr 0 + BitVec.ofNat 32 200) :
    SqueezeArgs s₁ (L.ptr 0) (L.ptr 0 + BitVec.ofNat 32 200) (L.ptr (idx p.base) + BitVec.ofNat 32 p.off)
      rate pos p.len := by
  have hL := hc₁.ok
  obtain ⟨e0, e1, e2⟩ := hc₁.kregs
  have er := hp.regA hL
  refine ⟨g0, g1, g2, g3, g12, glr, hrate, hpos, hp.len32 hL, hc₁.sp8, fit_le (by decide) hc₁.fit,
    hp.fit hL, hc₁.fitO (by decide) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e0, er]; exact Lay.disj hL (sepB_symm hp.sepK.1)
  · rw [e0, e1]; exact Lay.disj hL (hc₁.sep00 (by decide) (by decide) (by decide))
  · rw [er, e1]; exact Lay.disj hL hp.sepK.2.1
  · rw [e2, e0]; exact Lay.disj hL (sepB_symm (hc₁.sep01 (by decide) (by decide)))
  · rw [e2, er]; exact Lay.disj hL (sepB_symm hp.sepK.2.2)
  · rw [e2, e1]; exact Lay.disj hL (sepB_symm (hc₁.sep01 (by decide) (by decide)))
  · rw [e0, er, e1]
    exact covers_cons' (hc₁.cs (by decide)) (covers_cons' (hp.covW hg)
      (covers_cons' (hc₁.cs (by decide)) covers_nil'))

theorem padArgs_of {L : Lay} {rate : Nat} (hrate : rate ∈ rates) {s₁ : State} (hc₁ : Ctx L s₁) {pos : Nat}
    (hpos : pos < rate) {sfx : BitVec 32}
    (g0 : s₁.gpr .r0 = L.ptr 0) (g1 : s₁.gpr .r1 = BitVec.ofNat 32 rate) (g2 : s₁.gpr .r2 = BitVec.ofNat 32 pos)
    (g3 : s₁.gpr .r3 = sfx) (glr : s₁.gpr .lr = L.ptr 0 + BitVec.ofNat 32 200) :
    PadArgs s₁ (L.ptr 0) (L.ptr 0 + BitVec.ofNat 32 200) rate pos sfx := by
  have hL := hc₁.ok
  obtain ⟨e0, e1, e2⟩ := hc₁.kregs
  refine ⟨g0, g1, g2, g3, glr, hrate, hpos, hc₁.sp8, fit_le (by decide) hc₁.fit,
    hc₁.fitO (by decide) (by decide), ?_, ?_, ?_, covers_kregs hc₁⟩
  · rw [e0, e1]; exact Lay.disj hL (hc₁.sep00 (by decide) (by decide) (by decide))
  · rw [e2, e0]; exact Lay.disj hL (sepB_symm (hc₁.sep01 (by decide) (by decide)))
  · rw [e2, e1]; exact Lay.disj hL (sepB_symm (hc₁.sep01 (by decide) (by decide)))

/-- The 64 bytes of `G(c)` squeezed at once: both of its outputs. -/
theorem G_split (c : List Byte) :
    Spec.Sha3.squeezeFrom 72 (VG.Proof.MlKem.padded 72 Spec.Sha3.sha3Suffix c) 0 64 =
      (Spec.MlKem.G c).1 ++ (Spec.MlKem.G c).2 := by
  simp only [Spec.MlKem.G, VG.Proof.MlKem.sha3_512_eq, List.take_append_drop]

end VG.Proof.MlKem.Arm

end

end

/-!
# ML-KEM on 32-bit ARM: `vg_mlkem_sample_ntt`, constant time and `Verified`

Two runs from states that agree on the public data (the pointers, the stack
pointer and the seed, which the contract lets the function leak) leak the same
trace (`RelCT`), phase by phase: the blocks by the taint analysis, from
registers that hold pointers in both runs (`taint_block`); the calls of the
sponge functions by `absorb_ct`, …, from their arguments, which are the same
in both runs; and the loop of Algorithm 7 iteration by iteration, whose
branches are on the same values in both runs because the XOF output is the
same, being that of the same seed (`body_ct`). What each run is at each point
comes from the correctness proof (`RelCT.wp`).
-/

@[expose] public section

namespace VG.Proof.MlKem.Arm.Sample

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (stateAt)

/-- Two runs, from states that agree on the public data. -/
structure Two (s₁ s₂ : State) : Prop where
  hp₁ : Pre s₁
  hp₂ : Pre s₂
  sp : s₁.sp = s₂.sp
  seed : pseed s₁ = pseed s₂
  a : pa s₁ = pa s₂
  scr : pscr s₁ = pscr s₂
  B : B s₁ = B s₂

theorem taint_block {P : State → State → Prop} {is : List Instr} (rs : List Reg)
    (hP : ∀ a b, P a b → ∀ r ∈ rs, a.gpr r = b.gpr r) {hc : VG.Taint.Hint VG.Arm.taint.T}
    (h : (VG.Arm.taint.check (Taint.ofRegs rs) (.block is) hc).isSome = true) :
    RelCT isa P (.block is) fun _ _ => True :=
  RelCT.taint (A := VG.Arm.taint) (Taint.ofRegs rs) (fun a b hab => Taint.agree_ofRegs (hP a b hab)) h

theorem relct_wp {c : Prog isa} {P : State → State → Prop} {F₁ F₂ : State → Prop}
    (hct : RelCT isa P c fun _ _ => True) (hw : ∀ a b, P a b → WP isa c a F₁ ∧ WP isa c b F₂) :
    RelCT isa P c fun a b => F₁ a ∧ F₂ b :=
  (hct.wp hw).mono (fun _ _ h => h) fun _ _ h => ⟨h.2.1, h.2.2⟩

section
variable {s₁ s₂ : State} (h : Two s₁ s₂)
include h

theorem Ls_eq (t : Nat) : Ls s₁ t = Ls s₂ t := by simp only [Ls, h.B]

theorem D1_eq (t : Nat) : D1 s₁ t = D1 s₂ t := by simp only [D1, h.B]

theorem D2_eq (t : Nat) : D2 s₁ t = D2 s₂ t := by simp only [D2, h.B]

/-! ## The loop -/

omit h in
/-- A candidate accepted or not, in both runs alike. -/
theorem accept_ct {d : Reg} (hd : d = .r10 ∨ d = .r11) {P : State → State → Prop} (hz : ∀ a b, P a b → a.z = b.z)
    (h1 : ∀ a b, P a b → a.gpr .r1 = b.gpr .r1) : RelCT isa P (accept d) fun _ _ => True := by
  refine RelCT.ite (fun a b hab => by show some a.z = some b.z; rw [hz a b hab]) ?_ ?_
  · exact taint_block [] (fun _ _ _ _ hr => absurd hr List.not_mem_nil) (by taint_decide)
  · rcases hd with rfl | rfl
    · exact taint_block [.r1] (fun a b hab r hr => by
        rw [List.mem_singleton] at hr; subst hr; exact h1 a b hab.1) (by taint_decide)
    · exact taint_block [.r1] (fun a b hab r hr => by
        rw [List.mem_singleton] at hr; subst hr; exact h1 a b hab.1) (by taint_decide)

theorem body_ct {t : Nat} (ht : t < 280) :
    RelCT isa (fun a b => Inv s₁ t a ∧ Inv s₂ t b) rejBody fun a b =>
      (Inv s₁ (t + 1) a ∧ a.z = decide (t + 1 = 280)) ∧ (Inv s₂ (t + 1) b ∧ b.z = decide (t + 1 = 280)) := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  refine relct_wp ?_ fun a b hab => ⟨body_ok hp₁ ht hab.1, body_ok hp₂ ht hab.2⟩
  refine RelCT.seq (R := fun a b => P1 s₁ t a ∧ P1 s₂ t b) (relct_wp ?_ fun a b hab =>
    ⟨piece1 hp₁ ht hab.1, piece1 hp₂ ht hab.2⟩) ?_
  · exact taint_block [.r0] (fun a b hab r hr => by
      rw [List.mem_singleton] at hr; subst hr; rw [hab.1.r0, hab.2.r0, h.scr]) (by taint_decide)
  refine RelCT.seq (R := fun a b => P2 s₁ t a ∧ P2 s₂ t b) (relct_wp ?_ fun a b hab =>
    ⟨piece2 hp₁ hab.1, piece2 hp₂ hab.2⟩) ?_
  · refine accept_ct (.inl rfl) (fun a b hab => by rw [hab.1.z, hab.2.z, D1_eq h, Ls_eq h]) fun a b hab => ?_
    rw [hab.1.ls.r1, hab.2.ls.r1, h.a, Ls_eq h]
  refine RelCT.seq (R := fun a b => P3 s₁ t a ∧ P3 s₂ t b) (relct_wp ?_ fun a b hab =>
    ⟨piece3 hab.1, piece3 hab.2⟩) ?_
  · exact taint_block [] (fun _ _ _ _ hr => absurd hr List.not_mem_nil) (by taint_decide)
  refine RelCT.seq (R := fun a b => P4 s₁ t a ∧ P4 s₂ t b) (relct_wp ?_ fun a b hab =>
    ⟨piece4 hp₁ hab.1, piece4 hp₂ hab.2⟩) ?_
  · refine accept_ct (.inr rfl) (fun a b hab => by rw [hab.1.z, hab.2.z, D1_eq h, D2_eq h, Ls_eq h])
      fun a b hab => ?_
    rw [hab.1.p2.ls.r1, hab.2.p2.ls.r1, h.a, Ls_eq h, D1_eq h]
  · exact taint_block [] (fun _ _ _ _ hr => absurd hr List.not_mem_nil) (by taint_decide)

theorem loop_ct :
    RelCT isa (fun a b => Inv s₁ 0 a ∧ Inv s₂ 0 b) (.loop rejBody .ne) fun a b =>
      Inv s₁ 280 a ∧ Inv s₂ 280 b := by
  refine RelCT.mono (RelCT.loop (M := isa) (body := rejBody) (c := .ne)
    (Q := fun a b => Inv s₁ 280 a ∧ Inv s₂ 280 b)
    (fun n a b => ∃ t, t < 280 ∧ n = 280 - t ∧ Inv s₁ t a ∧ Inv s₂ t b) (fun n => ?_) 280)
    (fun a b hab => ⟨0, by decide, rfl, hab⟩) (fun _ _ h => h)
  refine RelCT.mono (P := fun a b => ∃ t, t < 280 ∧ n = 280 - t ∧ Inv s₁ t a ∧ Inv s₂ t b)
    (RelCT.exists_ fun t => ?_) (fun _ _ hab => hab) (fun _ _ h => h)
  by_cases ht : t < 280
  · by_cases hn : n = 280 - t
    · refine RelCT.mono (P := fun a b => Inv s₁ t a ∧ Inv s₂ t b) (body_ct h ht) (fun _ _ hab => hab.2.2)
        fun a b ⟨⟨i₁, z₁⟩, ⟨i₂, z₂⟩⟩ => ⟨?_, fun e => ?_, fun e => ?_⟩
      · show some (!a.z) = some (!b.z); rw [z₁, z₂]
      · have : t + 1 = 280 := by
          have e' : (!a.z) = false := Option.some.inj e
          rw [z₁] at e'; simpa using e'
        rw [this] at i₁ i₂; exact ⟨i₁, i₂⟩
      · have : t + 1 ≠ 280 := by
          have e' : (!a.z) = true := Option.some.inj e
          rw [z₁] at e'; simpa using e'
        exact ⟨280 - (t + 1), by omega_using [ht, hn], t + 1, by omega_using [ht, this], rfl, i₁, i₂⟩
    · exact RelCT.of_false fun _ _ hab => hn hab.2.1
  · exact RelCT.of_false fun _ _ hab => ht hab.1

/-! ## The sponge -/

theorem absorbPhase_ct :
    RelCT isa (fun a b => (SEnv s₁ a ∧ stateAt a.mem (S s₁) = Spec.Sha3.zero) ∧
      (SEnv s₂ b ∧ stateAt b.mem (S s₂) = Spec.Sha3.zero)) (.seq (.block absorbSeedArgs) absorbCall)
      fun _ _ => True := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  let F : State → State → Prop := fun s₀ s' => SEnv s₀ s' ∧ s'.gpr .r0 = pscr s₀ ∧
    s'.gpr .r1 = BitVec.ofNat 32 168 ∧ s'.gpr .r2 = BitVec.ofNat 32 0 ∧ s'.gpr .r3 = pseed s₀ ∧
    s'.gpr .r12 = BitVec.ofNat 32 34 ∧ s'.gpr .lr = pscr s₀ + BitVec.ofNat 32 200
  have hw : ∀ (s₀ s : State), SEnv s₀ s → WP isa (.block absorbSeedArgs) s (F s₀) := fun s₀ s hs =>
    WP.mono (absorbSeedArgs_ok hs.r4 hs.r6) fun _ ⟨hr, g0, g1, g2, g3, g12, glr⟩ =>
      ⟨hr.env hs, g0, g1, g2, g3, g12, glr⟩
  refine RelCT.seq (R := fun a b => F s₁ a ∧ F s₂ b) (relct_wp ?_ fun a b hab =>
    ⟨hw _ _ hab.1.1, hw _ _ hab.2.1⟩) (absorb_ct fun a b ⟨⟨e₁, a0, a1, a2, a3, a12, alr⟩, ⟨e₂, b0, b1, b2, b3, b12, blr⟩⟩ =>
    ⟨by rw [e₁.sp, e₂.sp, h.sp], _, _, _, _, _, _, absorb_args hp₁ e₁ a0 a1 a2 a3 a12 alr, by
      have := absorb_args hp₂ e₂ b0 b1 b2 b3 b12 blr
      rwa [← h.scr, ← h.seed] at this⟩)
  exact taint_block [.r4, .r6] (fun a b hab r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [hab.1.1.r4, hab.2.1.r4, h.seed]
    · rw [hab.1.1.r6, hab.2.1.r6, h.scr]) (by taint_decide)

theorem padPhase_ct :
    RelCT isa (fun a b => (SEnv s₁ a ∧ Spec.Sha3.Repr a.mem (S s₁) 168 (B s₁) ∧ (a.gpr .r0).toNat = 34) ∧
      (SEnv s₂ b ∧ Spec.Sha3.Repr b.mem (S s₂) 168 (B s₂) ∧ (b.gpr .r0).toNat = 34))
      (.seq (.block padArgs) padCall) fun _ _ => True := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  let F : State → State → Prop := fun s₀ s' => SEnv s₀ s' ∧ s'.gpr .r0 = pscr s₀ ∧
    s'.gpr .r1 = BitVec.ofNat 32 168 ∧ s'.gpr .r2 = BitVec.ofNat 32 34 ∧ s'.gpr .r3 = BitVec.ofNat 32 0x1f ∧
    s'.gpr .lr = pscr s₀ + BitVec.ofNat 32 200
  have hw : ∀ (s₀ s : State), SEnv s₀ s → (s.gpr .r0).toNat = 34 → WP isa (.block padArgs) s (F s₀) :=
    fun s₀ s hs h0 => WP.mono (padArgs_ok (BitVec.eq_of_toNat_eq (by rw [h0]; rfl)) hs.r6)
      fun _ ⟨hr, g0, g1, g2, g3, glr⟩ => ⟨hr.env hs, g0, g1, g2, g3, glr⟩
  refine RelCT.seq (R := fun a b => F s₁ a ∧ F s₂ b) (relct_wp ?_ fun a b hab =>
    ⟨hw _ _ hab.1.1 hab.1.2.2, hw _ _ hab.2.1 hab.2.2.2⟩) (pad_ct fun a b ⟨⟨e₁, a0, a1, a2, a3, alr⟩, ⟨e₂, b0, b1, b2, b3, blr⟩⟩ =>
    ⟨by rw [e₁.sp, e₂.sp, h.sp], _, _, _, _, _, pad_args hp₁ e₁ a0 a1 a2 a3 alr, by
      have := pad_args hp₂ e₂ b0 b1 b2 b3 blr
      rwa [← h.scr] at this⟩)
  exact taint_block [.r6] (fun a b hab r hr => by
    rw [List.mem_singleton] at hr; subst hr; rw [hab.1.1.r6, hab.2.1.r6, h.scr]) (by taint_decide)

theorem squeezePhase_ct :
    RelCT isa (fun a b => (SEnv s₁ a ∧ stateAt a.mem (S s₁) = VG.Proof.MlKem.padded 168 Spec.Sha3.shakeSuffix (B s₁)) ∧
      (SEnv s₂ b ∧ stateAt b.mem (S s₂) = VG.Proof.MlKem.padded 168 Spec.Sha3.shakeSuffix (B s₂)))
      (.seq (.block squeezeArgs) squeezeCall) fun _ _ => True := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  let F : State → State → Prop := fun s₀ s' => SEnv s₀ s' ∧ s'.gpr .r0 = pscr s₀ ∧
    s'.gpr .r1 = BitVec.ofNat 32 168 ∧ s'.gpr .r2 = BitVec.ofNat 32 0 ∧
    s'.gpr .r3 = pscr s₀ + BitVec.ofNat 32 840 ∧ s'.gpr .r12 = BitVec.ofNat 32 840 ∧
    s'.gpr .lr = pscr s₀ + BitVec.ofNat 32 200
  have hw : ∀ (s₀ s : State), SEnv s₀ s → WP isa (.block squeezeArgs) s (F s₀) := fun s₀ s hs =>
    WP.mono (squeezeArgs_ok hs.r6) fun _ ⟨hr, g0, g1, g2, g3, g12, glr⟩ => ⟨hr.env hs, g0, g1, g2, g3, g12, glr⟩
  refine RelCT.seq (R := fun a b => F s₁ a ∧ F s₂ b) (relct_wp ?_ fun a b hab =>
    ⟨hw _ _ hab.1.1, hw _ _ hab.2.1⟩) (squeeze_ct fun a b ⟨⟨e₁, a0, a1, a2, a3, a12, alr⟩, ⟨e₂, b0, b1, b2, b3, b12, blr⟩⟩ =>
    ⟨by rw [e₁.sp, e₂.sp, h.sp], _, _, _, _, _, _, squeeze_args hp₁ e₁ a0 a1 a2 a3 a12 alr, by
      have := squeeze_args hp₂ e₂ b0 b1 b2 b3 b12 blr
      rwa [← h.scr] at this⟩)
  exact taint_block [.r6] (fun a b hab r hr => by
    rw [List.mem_singleton] at hr; subst hr; rw [hab.1.1.r6, hab.2.1.r6, h.scr]) (by taint_decide)

/-! ## The whole function -/

/-- What holds after each phase, in one run. -/
abbrev E1 (s₀ s : State) : Prop := SEnv s₀ s ∧ stateAt s.mem (S s₀) = Spec.Sha3.zero
abbrev E2 (s₀ s : State) : Prop := SEnv s₀ s ∧ Spec.Sha3.Repr s.mem (S s₀) 168 (B s₀) ∧ (s.gpr .r0).toNat = 34
abbrev E3 (s₀ s : State) : Prop :=
  SEnv s₀ s ∧ stateAt s.mem (S s₀) = VG.Proof.MlKem.padded 168 Spec.Sha3.shakeSuffix (B s₀)
abbrev E4 (s₀ s : State) : Prop :=
  SEnv s₀ s ∧ Spec.Sha3.bytesAt s.mem (S s₀ + BitVec.ofNat 64 840) 840 = xof (B s₀) 840

theorem all_ct : RelCT isa (fun a b => a = s₁ ∧ b = s₂) sampleNTT fun _ _ => True := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  refine RelCT.seq (R := fun a b => E1 s₁ a ∧ E1 s₂ b) (relct_wp ?_ fun a b hab =>
    ⟨by rw [hab.1]; exact setup_ok hp₁, by rw [hab.2]; exact setup_ok hp₂⟩) ?_
  · exact taint_block [.r0, .r1, .r2] (fun a b hab r hr => by
      rw [hab.1, hab.2]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h.seed
      · exact h.a
      · exact h.scr) (by taint_decide)
  refine RelCT.seq (R := fun a b => E2 s₁ a ∧ E2 s₂ b) (relct_wp (absorbPhase_ct h) fun a b hab =>
    ⟨absorb_phase hp₁ hab.1.1 hab.1.2, absorb_phase hp₂ hab.2.1 hab.2.2⟩) ?_
  refine RelCT.seq (R := fun a b => E3 s₁ a ∧ E3 s₂ b) (relct_wp (padPhase_ct h) fun a b hab =>
    ⟨pad_phase hp₁ hab.1.1 hab.1.2.1 hab.1.2.2, pad_phase hp₂ hab.2.1 hab.2.2.1 hab.2.2.2⟩) ?_
  refine RelCT.seq (R := fun a b => E4 s₁ a ∧ E4 s₂ b) (relct_wp (squeezePhase_ct h) fun a b hab =>
    ⟨squeeze_phase hp₁ hab.1.1 hab.1.2, squeeze_phase hp₂ hab.2.1 hab.2.2⟩) ?_
  refine RelCT.seq (R := fun a b => Inv s₁ 0 a ∧ Inv s₂ 0 b) (relct_wp ?_ fun a b hab =>
    ⟨init_ok hab.1.1 hab.1.2, init_ok hab.2.1 hab.2.2⟩) ?_
  · exact taint_block [.r5, .r6] (fun a b hab r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [hab.1.1.r5, hab.2.1.r5, h.a]
      · rw [hab.1.1.r6, hab.2.1.r6, h.scr]) (by taint_decide)
  refine RelCT.seq (R := fun a b => Inv s₁ 280 a ∧ Inv s₂ 280 b) (loop_ct h) ?_
  exact taint_block [.r6] (fun a b hab r hr => by
    rw [List.mem_singleton] at hr; subst hr; rw [hab.1.ls.env.r6, hab.2.ls.env.r6, h.scr]) (by taint_decide)

end

/-! ## Verified -/

theorem polyAt_toPoly {m : Mem} {p : Addr} {L : List Zq} (hl : L.length = n)
    (h : ∀ k < L.length, coeffAt m p k = BitVec.ofNat 32 (L.getD k 0).val) :
    PolyIs m p (VG.Proof.MlKem.toPoly L) := by
  refine polyIs_of_coeffAt fun i hi => ?_
  rw [h i (by rw [hl]; exact hi), getElem!_eq _ hi]
  simp only [VG.Proof.MlKem.toPoly, Vector.getElem_ofFn]

end VG.Proof.MlKem.Arm.Sample
