module

public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Step
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Table
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Fast
public import VerifiedGarbage.Proof.MlKem.Kpke16Contract
public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.RunF
public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Model
public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.FwdW
import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Ctx
import VerifiedGarbage.Proof.MlKem.AArch64.Coeff16
import VerifiedGarbage.Proof.MlKem.Mem16

/-!
# ML-KEM on AArch64: `vg_mlkem16_ntt` (mlkem-native's schedule), by the machine

`Impl.MlKem.AArch64.Ntt16.Fast.fwdFast` transforms the polynomial at `x0`
(`fwdF_run`): the machine's state at the start (`initF`) holds of the
caller's (`initF_rel`), in regions that are apart (`ctxF`), and its run
(`checkF_ok`) leaves the reduced coefficients of `NTT` in the polynomial.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.NttR

open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem VG.Proof.MlKem.AArch64
open VG.Impl.MlKem.AArch64.Ntt16.Fast
open VG.Proof.MlKem.AArch64.Ntt16 (hw4 vhalf_table)

/-- What `fwdFast` needs of the state it starts from: the polynomial at `x0`,
writable and reduced, and the table, readable and apart from it. -/
structure InF (s : State) : Prop where
  wr : (⟨s.gpr .x0, 512⟩ : Region) ∈ s.wr
  red : ReducedW 16 s.mem (s.gpr .x0)
  table : ∀ j < 116, s.mem.readW (s.syms name + BitVec.ofNat 64 (8 * j)) 64 = hw4 tab j
  readable : Covers [⟨s.syms name, 928⟩] (s.rd ++ s.wr)
  apart : Region.Disjoint ⟨s.gpr .x0, 512⟩ ⟨s.syms name, 928⟩

/-- The regions of `rsF`. -/
def regF (s₀ : State) : List Region := [⟨s₀.gpr .x0, 512⟩, ⟨s₀.syms name, 928⟩]

theorem ctxF {s₀ : State} (hi : InF s₀) : Ctx rsF s₀ := by
  have h2 : rsF.length = 2 := rfl
  have cases2 : ∀ k < rsF.length, k = 0 ∨ k = 1 := fun k hk => by rw [h2] at hk; omega
  refine Ctx.of (fun k => (regF s₀).getD k ⟨0, 0⟩) (by decide) (fun k hk => ?_) (fun k hk => ?_)
    (fun k hk a ha => ?_) (fun k hk hw a ha => ?_) (fun k k' hk hk' hne => ?_)
  · rcases cases2 k hk with rfl | rfl <;> decide
  · rcases cases2 k hk with rfl | rfl <;> exact contains_off (by decide) (by decide)
  · rcases cases2 k hk with rfl | rfl
    · exact in_rd_wr (in_regions hi.wr ha)
    · exact hi.readable _ _ (in_regions (List.mem_singleton_self _) ha)
  · rcases cases2 k hk with rfl | rfl
    · exact in_regions hi.wr ha
    · exact absurd hw (by decide)
  · rcases cases2 k hk with rfl | rfl <;> rcases cases2 k' hk' with rfl | rfl
    all_goals first
      | exact absurd rfl hne
      | exact hi.apart | exact hi.apart.symm

theorem initF_rel {s₀ : State} (hi : InF s₀) : Rel rsF s₀ (Lf (Wi s₀)) (Of (Wi s₀)) initF s₀ := by
  refine ⟨fun r e he => ?_, fun r => ?_, fun k hk j hj e he => ?_, rfl, rfl, rfl, rfl⟩
  · have : (initF.vreg r).get e = junkT := by
      show slot tw (slot yw 0 (vi r)) e = 0
      rw [slot_zero, slot_zero]
    rw [this]; exact Hd.junk _
  · unfold initF
    rw [greg_setG]
    by_cases h0 : r = .x0
    · subst h0
      rw [ite_eq_left rfl]
      exact GHd.code (rs := rsF) ⟨by decide, by decide, by decide, by
        show s₀.gpr .x0 = s₀.gpr .x0 + BitVec.ofNat 64 0 + BitVec.ofNat 64 0
        rw [ptr_zero, ptr_zero]⟩
    · rw [ite_eq_right h0]
      show GHd rsF s₀ (G.ofCode (slot gw 0 (gi r))) _
      rw [slot_zero]
      trivial
  · have h2 : rsF.length = 2 := rfl
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · have hj' : j < 32 := hj
      rw [initF_f j hj' e he]
      refine (Hd.mk (by decide)).2 ?_
      rw [eval_mk, Nat.zero_mod, Nat.mod_eq_of_lt (show 8 * j + e < 512 by omega)]
      apply BitVec.eq_of_toNat_eq
      show (vhalf (s₀.mem.read (s₀.gpr .x0 + BitVec.ofNat 64 0 + BitVec.ofNat 64 (16 * j)) 16) e).toNat = _
      rw [ptr_zero, show 16 * j = 2 * (8 * j) by omega, vhalf_read_coeff _ _ _ he]
      rfl
    · have hj' : j < 58 := hj
      have ea : caddr rsF s₀ 1 j = s₀.syms name + BitVec.ofNat 64 (0 + 16 * j) := by
        show s₀.syms name + BitVec.ofNat 64 0 + BitVec.ofNat 64 (16 * j) = _
        rw [ptr_zero, Nat.zero_add]
      have hv := vhalf_table (m := s₀.mem) (p := s₀.syms name) (off := 0) (N := 116)
        (H := tab) (fun j hj => by rw [Nat.zero_add]; exact hi.table j hj) (i := j) (by omega) he
      rw [initF_t hj' he, ea, hv]
      exact Hd.cT _

theorem fwdF_run (s₀ : State) (hi : InF s₀) :
    WP isa fwdFast s₀ fun s' =>
      s'.sp = s₀.sp ∧ PolyIsW 16 s'.mem (s₀.gpr .x0) (ntt (polyAtW 16 s₀.mem (s₀.gpr .x0))) := by
  have hc := checkF_ok
  generalize hx : initF.runP fwdRules rsF 16 fwdFast = x at hc
  cases x with
  | none => cases hc
  | some σ =>
    have hout : ∀ j < 32, ∀ e < 8, (σ.chunk 0 j).get e = outT (8 * j + e) := by
      simpa only [Option.elim, outW, List.all_eq_true, List.mem_range, Nat.beq_eq] using hc
    refine WP.mono (runP_ok (model (Wi s₀)) (ctxF hi) 16 _ (initF_rel hi) hx) fun s' h' => ⟨h'.sp, ?_⟩
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
