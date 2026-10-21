module

public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Step
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Table
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Readonly
public import VerifiedGarbage.Spec.MlKem.Kpke16
public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.RunW
public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Model
import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Ctx
import VerifiedGarbage.Proof.MlKem.AArch64.Coeff16
import VerifiedGarbage.Proof.MlKem.Mem16
import VerifiedGarbage.Proof.MlKem.Mem16Bytes

/-!
# ML-KEM on AArch64: the 16-bit NTT of a polynomial stored with 16 bits, by the machine

`Impl.MlKem.AArch64.Ntt16.Readonly.fwdW` transforms the polynomial at `x0`
(`fwdW_run`): the machine's state at the start (`initW`) holds of the
caller's (`initW_rel`), in regions that are apart (`ctxW`), and its run
(`checkW_ok`) leaves the reduced coefficients of `NTT` in the polynomial.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.NttR

open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Ntt16 (hw4 vhalf_table LRep)

/-- What `fwdW` needs of the state it starts from: the polynomial at `x0`
and the working space at `x1`, writable and apart, the polynomial reduced,
and the table, readable and apart from both. -/
structure InW (s : State) : Prop where
  wr : s.wr = [⟨s.gpr .x0, 512⟩, ⟨s.gpr .x1, 512⟩]
  disj : Region.Disjoint ⟨s.gpr .x0, 512⟩ ⟨s.gpr .x1, 512⟩
  red : ReducedW 16 s.mem (s.gpr .x0)
  table : ∀ j < 64, s.mem.readW (s.syms "VG_MLKEM_NTT16_ZETAS" + BitVec.ofNat 64 (8 * j)) 64 =
    hw4 Impl.MlKem.AArch64.Ntt16.tableHalves j
  readable : Covers [⟨s.syms "VG_MLKEM_NTT16_ZETAS", 512⟩] (s.rd ++ s.wr)
  apartOutput : Region.Disjoint ⟨s.gpr .x0, 512⟩ ⟨s.syms "VG_MLKEM_NTT16_ZETAS", 512⟩
  apartScratch : Region.Disjoint ⟨s.gpr .x1, 512⟩ ⟨s.syms "VG_MLKEM_NTT16_ZETAS", 512⟩

/-- The input's coefficients. -/
def Wi (s₀ : State) (p : Nat) : BitVec 16 := coeffAtW 16 s₀.mem (s₀.gpr .x0) p

/-- The regions of `rsW`. -/
def regW (s₀ : State) : List Region :=
  [⟨s₀.gpr .x0, 512⟩, ⟨s₀.gpr .x1, 512⟩, ⟨s₀.syms "VG_MLKEM_NTT16_ZETAS", 512⟩]

theorem ctxW {s₀ : State} (hi : InW s₀) : Ctx rsW s₀ := by
  have h3 : rsW.length = 3 := rfl
  have cases3 : ∀ k < rsW.length, k = 0 ∨ k = 1 ∨ k = 2 := fun k hk => by rw [h3] at hk; omega
  have w0 : (⟨s₀.gpr .x0, 512⟩ : Region) ∈ s₀.wr := by rw [hi.wr]; exact List.mem_cons_self ..
  have w1 : (⟨s₀.gpr .x1, 512⟩ : Region) ∈ s₀.wr := by rw [hi.wr]; simp
  refine Ctx.of (fun k => (regW s₀).getD k ⟨0, 0⟩) (by decide) (fun k hk => ?_) (fun k hk => ?_)
    (fun k hk a ha => ?_) (fun k hk hw a ha => ?_) (fun k k' hk hk' hne => ?_)
  · rcases cases3 k hk with rfl | rfl | rfl <;> decide
  · rcases cases3 k hk with rfl | rfl | rfl <;> exact contains_off (by decide) (by decide)
  · rcases cases3 k hk with rfl | rfl | rfl
    · exact in_rd_wr (in_regions w0 ha)
    · exact in_rd_wr (in_regions w1 ha)
    · exact hi.readable _ _ (in_regions (List.mem_singleton_self _) ha)
  · rcases cases3 k hk with rfl | rfl | rfl
    · exact in_regions w0 ha
    · exact in_regions w1 ha
    · exact absurd hw (by decide)
  · rcases cases3 k hk with rfl | rfl | rfl <;> rcases cases3 k' hk' with rfl | rfl | rfl
    all_goals first
      | exact absurd rfl hne
      | exact hi.disj | exact hi.disj.symm | exact hi.apartOutput | exact hi.apartOutput.symm
      | exact hi.apartScratch | exact hi.apartScratch.symm

theorem initW_rel {s₀ : State} (hi : InW s₀) : Rel rsW s₀ (Lf (Wi s₀)) (Of (Wi s₀)) initW s₀ := by
  refine ⟨fun r e he => ?_, fun r => ?_, fun k hk j hj e he => ?_, rfl, rfl, rfl, rfl⟩
  · have : (initW.vreg r).get e = junkT := by
      show slot tw (slot yw 0 (vi r)) e = 0
      rw [slot_zero, slot_zero]
    rw [this]; exact Hd.junk _
  · unfold initW
    rw [greg_setG, greg_setG]
    by_cases h1 : r = .x1
    · subst h1
      rw [ite_eq_left rfl]
      exact GHd.code (rs := rsW) ⟨by decide, by decide, by decide, by
        show s₀.gpr .x1 = s₀.gpr .x1 + BitVec.ofNat 64 0 + BitVec.ofNat 64 0
        rw [ptr_zero, ptr_zero]⟩
    · rw [ite_eq_right h1]
      by_cases h0 : r = .x0
      · subst h0
        rw [ite_eq_left rfl]
        exact GHd.code (rs := rsW) ⟨by decide, by decide, by decide, by
          show s₀.gpr .x0 = s₀.gpr .x0 + BitVec.ofNat 64 0 + BitVec.ofNat 64 0
          rw [ptr_zero, ptr_zero]⟩
      · rw [ite_eq_right h0]
        show GHd rsW s₀ (G.ofCode (slot gw 0 (gi r))) _
        rw [slot_zero]
        trivial
  · have h3 : rsW.length = 3 := rfl
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
    · have hj' : j < 32 := hj
      rw [initW_f j hj' e he]
      refine (Hd.mk (by decide)).2 ?_
      rw [eval_mk, Nat.zero_mod, Nat.mod_eq_of_lt (show 8 * j + e < 512 by omega)]
      apply BitVec.eq_of_toNat_eq
      show (vhalf (s₀.mem.read (s₀.gpr .x0 + BitVec.ofNat 64 0 + BitVec.ofNat 64 (16 * j)) 16) e).toNat = _
      rw [ptr_zero, show 16 * j = 2 * (8 * j) by omega, vhalf_read_coeff _ _ _ he]
      rfl
    · have hj' : j < 32 := hj
      rw [initW_s j hj' e he]; exact Hd.junk _
    · have hj' : j < 32 := hj
      have ea : caddr rsW s₀ 2 j = s₀.syms "VG_MLKEM_NTT16_ZETAS" + BitVec.ofNat 64 (0 + 16 * j) := by
        show s₀.syms "VG_MLKEM_NTT16_ZETAS" + BitVec.ofNat 64 0 + BitVec.ofNat 64 (16 * j) = _
        rw [ptr_zero, Nat.zero_add]
      have hv := vhalf_table (m := s₀.mem) (p := s₀.syms "VG_MLKEM_NTT16_ZETAS") (off := 0) (N := 64)
        (H := Impl.MlKem.AArch64.Ntt16.tableHalves) (fun j hj => by rw [Nat.zero_add]; exact hi.table j hj)
        (i := j) (by omega) he
      rw [initW_t hj' he, ea, hv]
      exact Hd.cT _

/-- The coefficients of a reduced polynomial represent themselves. -/
theorem lrep_red {m : Mem} {p : Addr} (h : ReducedW 16 m p) {i : Nat} (hi : i < 256) :
    LRep (coeffAtW 16 m p i) (polyAtW 16 m p)[i]! 3329 := by
  have hv := polyIsW16_toNat (⟨h, rfl⟩ : PolyIsW 16 m p (polyAtW 16 m p)) hi
  have hl : (coeffAtW 16 m p i).toNat < 3329 := h i hi
  have hz : ((polyAtW 16 m p)[i]!).val < 3329 := ((polyAtW 16 m p)[i]!).isLt
  rw [LRep, BitVec.toInt_eq_toNat_of_lt (by omega), hv]
  exact ⟨by omega, by omega, by simp⟩

theorem fwdW_run (s₀ : State) (hi : InW s₀) :
    WP isa Impl.MlKem.AArch64.Ntt16.Readonly.fwdW s₀ fun s' =>
      s'.sp = s₀.sp ∧ PolyIsW 16 s'.mem (s₀.gpr .x0) (ntt (polyAtW 16 s₀.mem (s₀.gpr .x0))) := by
  have hc := checkW_ok
  generalize hx : initW.runP fwdRules rsW 16 Impl.MlKem.AArch64.Ntt16.Readonly.fwdW = x at hc
  cases x with
  | none => cases hc
  | some σ =>
    have hout : ∀ j < 32, ∀ e < 8, (σ.chunk 0 j).get e = outT (8 * j + e) := by
      simpa only [Option.elim, outW, List.all_eq_true, List.mem_range, Nat.beq_eq] using hc
    refine WP.mono (runP_ok (model (Wi s₀)) (ctxW hi) 16 _ (initW_rel hi) hx) fun s' h' => ⟨h'.sp, ?_⟩
    refine polyIsW_of_toNat fun i hi' => ?_
    have hi256 : i < 256 := hi'
    have hm := h'.mem 0 (by decide) (i / 8) (by show i / 8 < 32; omega) (i % 8) (Nat.mod_lt _ (by decide))
    rw [hout _ (by omega) _ (Nat.mod_lt _ (by decide)), show 8 * (i / 8) + i % 8 = i by omega] at hm
    have hv := (Hd.mk (by decide)).1 hm
    rw [eval_mk, Nat.mod_eq_of_lt (show i < 512 by omega)] at hv
    have hr := vhalf_read_coeff s'.mem (s₀.gpr .x0) (8 * (i / 8)) (Nat.mod_lt i (show 0 < 8 by decide))
    rw [show 8 * (i / 8) + i % 8 = i by omega, show 2 * (8 * (i / 8)) = 16 * (i / 8) by omega] at hr
    rw [← hr]
    change (vhalf (s'.mem.read (s₀.gpr .x0 + BitVec.ofNat 64 0 + BitVec.ofNat 64 (16 * (i / 8))) 16)
      (i % 8)) = _ at hv
    rw [ptr_zero] at hv
    rw [hv]
    exact Of_ntt (Wi s₀) _ (fun p hp => lrep_red hi.red hp) hi256

end VG.Proof.MlKem.AArch64.NttR
