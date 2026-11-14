module

public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.ReadonlyCalls
public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.FastTable
public import VerifiedGarbage.Proof.MlKem.Kpke16Contract
public import VerifiedGarbage.Proof.MlKem.AArch64.KeccakCall
public import VerifiedGarbage.Spec.MlKem
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Readonly.Call
import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Step
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Table
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Fast
public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.RunF
public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Model
public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.FwdW
import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Ctx
import VerifiedGarbage.Proof.MlKem.AArch64.Coeff16
import VerifiedGarbage.Proof.MlKem.Mem16
public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.AbiF
import VerifiedGarbage.Proof.MlKem.AArch64.PrimCall
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.FastInv
public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.RunFI
public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.ModelFI
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Sym
public import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
public import VerifiedGarbage.Proof.Framework.AArch64.Inline
public import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.MlKem.AArch64.NttR.LitFI

/-! ### `MlKem.AArch64.NttR.FwdF`, which only this module used -/

section

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
  have cases2 : ∀ k < rsF.length, k = 0 ∨ k = 1 := fun k hk => by rw [h2] at hk; omega_using [hk]
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
    rcases (by omega_using [hk, h2] : k = 0 ∨ k = 1) with rfl | rfl
    · have hj' : j < 32 := hj
      rw [initF_f j hj' e he]
      refine (Hd.mk (by decide)).2 ?_
      rw [eval_mk, Nat.zero_mod, Nat.mod_eq_of_lt (show 8 * j + e < 512 by omega_using [he, hj'])]
      apply BitVec.eq_of_toNat_eq
      show (vhalf (s₀.mem.read (s₀.gpr .x0 + BitVec.ofNat 64 0 + BitVec.ofNat 64 (16 * j)) 16) e).toNat = _
      rw [ptr_zero, show 16 * j = 2 * (8 * j) by omega_using [], vhalf_read_coeff _ _ _ he]
      rfl
    · have hj' : j < 58 := hj
      have ea : caddr rsF s₀ 1 j = s₀.syms name + BitVec.ofNat 64 (0 + 16 * j) := by
        show s₀.syms name + BitVec.ofNat 64 0 + BitVec.ofNat 64 (16 * j) = _
        rw [ptr_zero, Nat.zero_add]
      have hv := vhalf_table (m := s₀.mem) (p := s₀.syms name) (off := 0) (N := 116)
        (H := tab) (fun j hj => by rw [Nat.zero_add]; exact hi.table j hj) (i := j) (by omega_using [hj']) he
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
    have hm := h'.mem 0 (by decide) (i / 8) (by show i / 8 < 32; omega_using [hi256]) (i % 8) (Nat.mod_lt _ (by decide))
    rw [hout _ (by omega_using [hi256]) _ (Nat.mod_lt _ (by decide)), show 8 * (i / 8) + i % 8 = i by omega_using []] at hm
    have hv := (Hd.mk (by decide)).1 hm
    rw [eval_mk, Nat.mod_eq_of_lt (show i < 512 by omega_using [hi256])] at hv
    have hr := vhalf_read_coeff s'.mem (s₀.gpr .x0) (8 * (i / 8)) (Nat.mod_lt i (show 0 < 8 by decide))
    rw [show 8 * (i / 8) + i % 8 = i by omega_using [], show 2 * (8 * (i / 8)) = 16 * (i / 8) by omega_using []] at hr
    rw [← hr]
    change (vhalf (s'.mem.read (s₀.gpr .x0 + BitVec.ofNat 64 0 + BitVec.ofNat 64 (16 * (i / 8))) 16)
      (i % 8)) = _ at hv
    rw [ptr_zero] at hv
    rw [hv]
    exact Of_ntt (Wi s₀) _ (fun p hp => lrep_red hi.red hp) hi256

end VG.Proof.MlKem.AArch64.NttR

end

end

/-! ### `MlKem.AArch64.NttR.InvFI`, which only this module used -/

section

/-!
# ML-KEM on AArch64: `vg_mlkem16_inv_ntt` (mlkem-native's schedule), by the machine

`Impl.MlKem.AArch64.Ntt16.FastInv.invFast` transforms the polynomial at `x0`
(`invFI_run`): the machine's state at the start (`initFI`) holds of the
caller's (`initFI_rel`), in regions that are apart (`ctxFII`), and its run
(`checkFI_ok`) leaves the reduced coefficients of `NTT⁻¹` in the polynomial.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.NttR

open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem VG.Proof.MlKem.AArch64
open VG.Impl.MlKem.AArch64.Ntt16.FastInv
open VG.Proof.MlKem.AArch64.Ntt16 (hw4 vhalf_table)

/-- What `invFast` needs of the state it starts from: the polynomial at `x0`,
writable and reduced, and the table, readable and apart from it. -/
structure InFI (s : State) : Prop where
  wr : (⟨s.gpr .x0, 512⟩ : Region) ∈ s.wr
  red : ReducedW 16 s.mem (s.gpr .x0)
  table : ∀ j < 116, s.mem.readW (s.syms name + BitVec.ofNat 64 (8 * j)) 64 = hw4 tab j
  readable : Covers [⟨s.syms name, 928⟩] (s.rd ++ s.wr)
  apart : Region.Disjoint ⟨s.gpr .x0, 512⟩ ⟨s.syms name, 928⟩

/-- The regions of `rsFI`. -/
def regFI (s₀ : State) : List Region := [⟨s₀.gpr .x0, 512⟩, ⟨s₀.syms name, 928⟩]

theorem ctxFI {s₀ : State} (hi : InFI s₀) : Ctx rsFI s₀ := by
  have h2 : rsFI.length = 2 := rfl
  have cases2 : ∀ k < rsFI.length, k = 0 ∨ k = 1 := fun k hk => by rw [h2] at hk; omega_using [hk]
  refine Ctx.of (fun k => (regFI s₀).getD k ⟨0, 0⟩) (by decide) (fun k hk => ?_) (fun k hk => ?_)
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

theorem initFI_rel {s₀ : State} (hi : InFI s₀) : Rel rsFI s₀ (Lfi (Wi s₀)) (Ofi (Wi s₀)) initFI s₀ := by
  refine ⟨fun r e he => ?_, fun r => ?_, fun k hk j hj e he => ?_, rfl, rfl, rfl, rfl⟩
  · have : (initFI.vreg r).get e = junkT := by
      show slot tw (slot yw 0 (vi r)) e = 0
      rw [slot_zero, slot_zero]
    rw [this]; exact Hd.junk _
  · unfold initFI
    rw [greg_setG]
    by_cases h0 : r = .x0
    · subst h0
      rw [ite_eq_left rfl]
      exact GHd.code (rs := rsFI) ⟨by decide, by decide, by decide, by
        show s₀.gpr .x0 = s₀.gpr .x0 + BitVec.ofNat 64 0 + BitVec.ofNat 64 0
        rw [ptr_zero, ptr_zero]⟩
    · rw [ite_eq_right h0]
      show GHd rsFI s₀ (G.ofCode (slot gw 0 (gi r))) _
      rw [slot_zero]
      trivial
  · have h2 : rsFI.length = 2 := rfl
    rcases (by omega_using [hk, h2] : k = 0 ∨ k = 1) with rfl | rfl
    · have hj' : j < 32 := hj
      rw [initFI_f j hj' e he]
      refine (Hd.mk (by decide)).2 ?_
      rw [eval_mk, Nat.zero_mod, Nat.mod_eq_of_lt (show 8 * j + e < 512 by omega_using [he, hj'])]
      apply BitVec.eq_of_toNat_eq
      show (vhalf (s₀.mem.read (s₀.gpr .x0 + BitVec.ofNat 64 0 + BitVec.ofNat 64 (16 * j)) 16) e).toNat = _
      rw [ptr_zero, show 16 * j = 2 * (8 * j) by omega_using [], vhalf_read_coeff _ _ _ he]
      rfl
    · have hj' : j < 58 := hj
      have ea : caddr rsFI s₀ 1 j = s₀.syms name + BitVec.ofNat 64 (0 + 16 * j) := by
        show s₀.syms name + BitVec.ofNat 64 0 + BitVec.ofNat 64 (16 * j) = _
        rw [ptr_zero, Nat.zero_add]
      have hv := vhalf_table (m := s₀.mem) (p := s₀.syms name) (off := 0) (N := 116)
        (H := tab) (fun j hj => by rw [Nat.zero_add]; exact hi.table j hj) (i := j) (by omega_using [hj']) he
      rw [initFI_t hj' he, ea, hv]
      exact Hd.cT _

theorem invFI_run (s₀ : State) (hi : InFI s₀) :
    WP isa invFast s₀ fun s' =>
      s'.sp = s₀.sp ∧ PolyIsW 16 s'.mem (s₀.gpr .x0) (nttInv (polyAtW 16 s₀.mem (s₀.gpr .x0))) := by
  have hc := checkFI_ok
  generalize hx : initFI.runP fastInvRules rsFI 16 invFast = x at hc
  cases x with
  | none => cases hc
  | some σ =>
    have hout : ∀ j < 32, ∀ e < 8, (σ.chunk 0 j).get e = outT (8 * j + e) := by
      simpa only [Option.elim, outW, List.all_eq_true, List.mem_range, Nat.beq_eq] using hc
    refine WP.mono (runP_ok (modelFI (Wi s₀)) (ctxFI hi) 16 _ (initFI_rel hi) hx) fun s' h' => ⟨h'.sp, ?_⟩
    refine polyIsW_of_toNat fun i hi' => ?_
    have hi256 : i < 256 := hi'
    have hm := h'.mem 0 (by decide) (i / 8) (by show i / 8 < 32; omega_using [hi256]) (i % 8) (Nat.mod_lt _ (by decide))
    rw [hout _ (by omega_using [hi256]) _ (Nat.mod_lt _ (by decide)), show 8 * (i / 8) + i % 8 = i by omega_using []] at hm
    have hv := (Hd.mk (by decide)).1 hm
    rw [eval_mk, Nat.mod_eq_of_lt (show i < 512 by omega_using [hi256])] at hv
    have hr := vhalf_read_coeff s'.mem (s₀.gpr .x0) (8 * (i / 8)) (Nat.mod_lt i (show 0 < 8 by decide))
    rw [show 8 * (i / 8) + i % 8 = i by omega_using [], show 2 * (8 * (i / 8)) = 16 * (i / 8) by omega_using []] at hr
    rw [← hr]
    change (vhalf (s'.mem.read (s₀.gpr .x0 + BitVec.ofNat 64 0 + BitVec.ofNat 64 (16 * (i / 8))) 16)
      (i % 8)) = _ at hv
    rw [ptr_zero] at hv
    rw [hv]
    exact Ofi_nttInv (Wi s₀) _ (fun p hp => lrep_red hi.red hp) hi256

end VG.Proof.MlKem.AArch64.NttR

end

end

/-! ### `MlKem.AArch64.NttR.AbiFI`, which only this module used -/

section

/-!
# ML-KEM on AArch64: `vg_mlkem16_inv_ntt` keeps what the ABI preserves

`invFast` keeps the low halves of `v8`–`v15` in `x7`–`x14` (`save`), which
the transform (`core`) does not write, and puts them back at the end
(`Fast.restore`); it writes none of `x19`–`x28` and `x30`, and leaves `sp` alone.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.NttR

open VG VG.AArch64 VG.Impl.MlKem.AArch64.Ntt16.FastInv

theorem saveI_eq : save = umovOf lanesF ++ ([.adrSym .x1 name, .addImm .x .x2 .x1 160] : List Instr) := rfl

theorem saveI_ok (s : State) :
    WP isa (.block save) s fun t => ∀ k ∈ lanesF, t.gpr k.1 = laneOf s k.2.1 k.2.2 := by
  rw [saveI_eq]
  refine WP.block_append (WP.mono (umovOf_ok lanesF s (by decide) (by decide)) fun t ⟨_, _, _, _, ht, _⟩ => ?_)
  refine WP.block_cons_iff.mpr ⟨_, exec_adrSym, WP.block_cons_iff.mpr ⟨_, exec_addImm_x (imm := 160) (by decide), WP.block_nil ?_⟩⟩
  intro k hk
  have h1 : k.1 ≠ .x1 := by revert k; decide
  have h2 : k.1 ≠ .x2 := by revert k; decide
  rw [RegUpd.gpr_write_of_ne (s := _) _ _ h2, RegUpd.gpr_write_of_ne (s := _) _ _ h1]
  exact ht k hk

/-- No instruction of `core` writes `x7`–`x14`. -/
theorem coreI_keeps : core.allInstrs (fun i => lanesF.all fun k => !clobbers i k.1) = true := by
  decide +kernel

/-- No instruction of `invFast` writes `x19`–`x28` or `x30`. -/
theorem invFast_keeps : invFast.allInstrs (fun i => preserved.all fun r => !clobbers i r) = true := by
  lit_decide

theorem invFast_abi {s s' : State} {t : List Leak} (he : Exec isa invFast s t s') : abiPreserved s s' := by
  refine ⟨fun r hr => Exec.gpr (fun i hi => ?_) he, Exec.sp he, fun r hr => ?_⟩
  · have := List.all_eq_true.mp ((Code.allInstrs_eq _ invFast) ▸ invFast_keeps) i hi
    simpa using List.all_eq_true.mp this r hr
  · cases he with
    | seq h1 h23 =>
    cases h23 with
    | seq h2 h3 =>
    obtain ⟨_, t1, e1, hs⟩ := saveI_ok s
    have hk : ∀ k ∈ lanesF, ∀ i ∈ instrs core, clobbers i k.1 = false := fun k hk i hi => by
      have := List.all_eq_true.mp ((Code.allInstrs_eq _ core) ▸ coreI_keeps) i hi
      simpa using List.all_eq_true.mp this k hk
    rw [restore_eq] at h3
    obtain ⟨_, t3, e3, -, -, -, -, -, h3l, -⟩ := insOf_ok lanesF _ (by decide) (by decide)
    rw [← (Exec.det h3 e3).2] at h3l
    rw [← (Exec.det h1 e1).2] at hs
    have hl : ∀ k ∈ lanesF, laneOf s' k.2.1 k.2.2 = laneOf s k.2.1 k.2.2 := fun k hkm => by
      rw [h3l k hkm, Exec.gpr (hk k hkm) h2, hs k hkm]
    simp only [preservedV, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hl (.x7, .v8, 0) (by decide) | exact hl (.x8, .v9, 0) (by decide)
      | exact hl (.x9, .v10, 0) (by decide) | exact hl (.x10, .v11, 0) (by decide)
      | exact hl (.x11, .v12, 0) (by decide) | exact hl (.x12, .v13, 0) (by decide)
      | exact hl (.x13, .v14, 0) (by decide) | exact hl (.x14, .v15, 0) (by decide)

end VG.Proof.MlKem.AArch64.NttR

end

end

/-!
# ML-KEM on AArch64: the 16-bit NTT and its inverse of polynomials stored with 16 bits, at offsets

`vg_mlkem16_ntt` and `vg_mlkem16_inv_ntt` called on the polynomial at an offset of `x28`
(`nttAtWithW_ok`, `nttInvAtWithW_ok`). The polynomial and the working space are 512 bytes
each.
-/

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/NttR/CallF.lean`, which only this module imported.
section

/-!
# ML-KEM on AArch64: calling `vg_mlkem16_ntt`

`fwdFast` as a callee: correct under its own contract (`fastC`), and its
call on the polynomial at `f` (`ntt16_call`), with the table as `FastReady`
says.
-/

section

namespace VG.Proof.MlKem.AArch64.NttR

open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem VG.Proof.MlKem.AArch64
open VG.Impl.MlKem.AArch64.Ntt16.Fast (fwdFast name)

/-- `fwdFast`'s contract as the code sees it. -/
def fastC : Contract isa where
  pre s := InF s
  post s t := PolyIsW 16 t.mem (s.gpr .x0) (ntt (polyAtW 16 s.mem (s.gpr .x0)))
  pub s t := s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧ s.syms name = t.syms name

theorem fastC_correct (s : State) (h : fastC.pre s) :
    ∃ tr t, Exec isa fwdFast s tr t ∧ abiPreserved s t ∧ fastC.post s t := by
  obtain ⟨tr, t, he, -, hp⟩ := fwdF_run s h
  exact ⟨tr, t, he, fwdFast_abi he, hp⟩

/-- `vg_mlkem16_ntt(f, _)`: `NTT` of the polynomial with 16-bit coefficients at `f`. -/
theorem ntt16_call {s : State} {f : Addr} (h0 : s.gpr .x0 = f) (hr : ReducedW 16 s.mem f)
    (hw : Covers [⟨f, 512⟩] s.wr) {w : Addr} (ht : FastReady s f w) {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨f, 512⟩] s s' → PolyIsW 16 s'.mem f (ntt (polyAtW 16 s.mem f)) → Q s') :
    WP isa (.call "vg_mlkem16_ntt" fwdFast) s Q := by
  have c0 : s.callEntry.gpr .x0 = f := (entry s).trans h0
  refine WP.callV (k := fastC) fastC_correct (rd := [fastRegion s]) (wr := [⟨f, 512⟩]) ?_
    (ht.readable.append_left hw.right) hw ?_
  · have hsy : (s.callEntry.withRegions [fastRegion s] [⟨f, 512⟩]).syms = s.syms := rfl
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [State.withRegions_wr, State.withRegions_gpr, c0]; exact List.mem_singleton_self _
    · simpa only [State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr, c0] using hr
    · simpa only [State.withRegions_mem, State.callEntry_mem, hsy] using ht.table
    · simp only [State.withRegions_rd, State.withRegions_wr, hsy]
      exact Covers.of_mem (fun r h => List.mem_append_left _ h)
    · simpa only [State.withRegions_gpr, hsy, c0] using ht.output.sub_left (Region.sub_prefix (by decide : 512 ≤ 1024))
  · intro s' hrd hwr hsp hf hcs _ hvec hpost
    simp only [fastC, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0] at hpost
    exact hQ s' ⟨hcs, hsp, hrd, hwr, hf, hvec⟩ hpost

end VG.Proof.MlKem.AArch64.NttR
end

end

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/NttR/CallFI.lean`, which only this module imported.
section

/-!
# ML-KEM on AArch64: calling `vg_mlkem16_inv_ntt`

`invFast` as a callee: correct under its own contract (`fastInvC`), and its
call on the polynomial at `f` (`nttInv16_call`), with the table as
`FastInvReady` says.
-/

section

namespace VG.Proof.MlKem.AArch64.NttR

open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem VG.Proof.MlKem.AArch64
open VG.Impl.MlKem.AArch64.Ntt16.FastInv (invFast name)

/-- `invFast`'s contract as the code sees it. -/
def fastInvC : Contract isa where
  pre s := InFI s
  post s t := PolyIsW 16 t.mem (s.gpr .x0) (nttInv (polyAtW 16 s.mem (s.gpr .x0)))
  pub s t := s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧ s.syms name = t.syms name

theorem fastInvC_correct (s : State) (h : fastInvC.pre s) :
    ∃ tr t, Exec isa invFast s tr t ∧ abiPreserved s t ∧ fastInvC.post s t := by
  obtain ⟨tr, t, he, -, hp⟩ := invFI_run s h
  exact ⟨tr, t, he, invFast_abi he, hp⟩

/-- `vg_mlkem16_inv_ntt(f, _)`: `NTT⁻¹` of the polynomial with 16-bit coefficients at `f`. -/
theorem nttInv16_call {s : State} {f : Addr} (h0 : s.gpr .x0 = f) (hr : ReducedW 16 s.mem f)
    (hw : Covers [⟨f, 512⟩] s.wr) {w : Addr} (ht : FastInvReady s f w) {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨f, 512⟩] s s' → PolyIsW 16 s'.mem f (nttInv (polyAtW 16 s.mem f)) → Q s') :
    WP isa (.call "vg_mlkem16_inv_ntt" invFast) s Q := by
  have c0 : s.callEntry.gpr .x0 = f := (entry s).trans h0
  refine WP.callV (k := fastInvC) fastInvC_correct (rd := [fastInvRegion s]) (wr := [⟨f, 512⟩]) ?_
    (ht.readable.append_left hw.right) hw ?_
  · have hsy : (s.callEntry.withRegions [fastInvRegion s] [⟨f, 512⟩]).syms = s.syms := rfl
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [State.withRegions_wr, State.withRegions_gpr, c0]; exact List.mem_singleton_self _
    · simpa only [State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr, c0] using hr
    · simpa only [State.withRegions_mem, State.callEntry_mem, hsy] using ht.table
    · simp only [State.withRegions_rd, State.withRegions_wr, hsy]
      exact Covers.of_mem (fun r h => List.mem_append_left _ h)
    · simpa only [State.withRegions_gpr, hsy, c0] using ht.output.sub_left (Region.sub_prefix (by decide : 512 ≤ 1024))
  · intro s' hrd hwr hsp hf hcs _ hvec hpost
    simp only [fastInvC, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0] at hpost
    exact hQ s' ⟨hcs, hsp, hrd, hwr, hf, hvec⟩ hpost

end VG.Proof.MlKem.AArch64.NttR
end

end

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Ntt16.W
open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Ntt16
open VG.Proof.MlKem.AArch64.Ntt16.Readonly (TableReady)
open VG.Impl.MlKem.AArch64.Ntt16

theorem nttAtWithW_ok {s : State} {off ns : Nat} {f w : Addr} {F : Poly}
    (hoff : off<65536) (hns : ns<65536)
    (hf : s.gpr .x28+BitVec.ofNat 64 off=f) (hw : s.gpr .x28+BitVec.ofNat 64 ns=w)
    (_hd : (Region.mk f 512).Disjoint ⟨w,512⟩) (hp : PolyIsW 16 s.mem f F)
    (hc : Covers [⟨f,512⟩,⟨w,512⟩] s.wr) (ht : NttR.FastReady s f w) :
    WP isa (Impl.MlKem.AArch64.Ntt16.Readonly.nttAtWithW off ns) s fun t=>
      Kept [⟨f,512⟩,⟨w,512⟩] s t ∧ PolyIsW 16 t.mem f (ntt F) := by
  have prep : WP isa (.block (Impl.MlKem.AArch64.ptrTo .x0 .x28 off ++ Impl.MlKem.AArch64.ptrTo .x1 .x28 ns)) s
      fun z=>Only [.x0,.x1] s z ∧ z.gpr .x0=f ∧ z.gpr .x1=w := by
    refine wp_ptrTo (by decide) hoff fun a ha ea=>wp_ptrTo' (by decide) hns fun z hz ez=>?_
    exact ⟨(ha.trans hz).mono (by simp),by rw [hz.get .x0 (by decide),ea]; exact hf,
      by rw [ez,ha.get .x28 (by decide)]; exact hw⟩
  refine WP.seq (WP.mono_syms prep fun z ⟨oz,z0,_⟩ zs=>?_)
  have table : NttR.FastReady z f w :=
    ⟨by simpa only [zs,oz.mem] using ht.table,
      by simpa only [NttR.sRegion,zs,oz.rd,oz.wr] using ht.readable,
      by simpa only [NttR.sRegion,zs] using ht.output,by simpa only [NttR.sRegion,zs] using ht.scratch⟩
  exact NttR.ntt16_call z0 (by rw [oz.mem]; exact hp.1) (by rw [oz.wr]; exact Covers.head hc) table
    fun t kt pt=>⟨(Kept.of_keep oz.keep oz.mem (by decide)).trans
      (kt.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self),
      by simpa only [oz.mem,hp.2] using pt⟩

theorem nttInvAtWithW_ok {s : State} {off ns : Nat} {f w : Addr} {F : Poly}
    (hoff : off<65536) (hns : ns<65536)
    (hf : s.gpr .x28+BitVec.ofNat 64 off=f) (hw : s.gpr .x28+BitVec.ofNat 64 ns=w)
    (_hd : (Region.mk f 512).Disjoint ⟨w,512⟩) (hp : PolyIsW 16 s.mem f F)
    (hc : Covers [⟨f,512⟩,⟨w,512⟩] s.wr) (ht : NttR.FastInvReady s f w) :
    WP isa (Impl.MlKem.AArch64.Ntt16.Readonly.nttInvAtWithW off ns) s fun t=>
      Kept [⟨f,512⟩,⟨w,512⟩] s t ∧ PolyIsW 16 t.mem f (nttInv F) := by
  have prep : WP isa (.block (Impl.MlKem.AArch64.ptrTo .x0 .x28 off ++ Impl.MlKem.AArch64.ptrTo .x1 .x28 ns)) s
      fun z=>Only [.x0,.x1] s z ∧ z.gpr .x0=f ∧ z.gpr .x1=w := by
    refine wp_ptrTo (by decide) hoff fun a ha ea=>wp_ptrTo' (by decide) hns fun z hz ez=>?_
    exact ⟨(ha.trans hz).mono (by simp),by rw [hz.get .x0 (by decide),ea]; exact hf,
      by rw [ez,ha.get .x28 (by decide)]; exact hw⟩
  refine WP.seq (WP.mono_syms prep fun z ⟨oz,z0,_⟩ zs=>?_)
  have table : NttR.FastInvReady z f w :=
    ⟨by simpa only [zs,oz.mem] using ht.table,
      by simpa only [NttR.sRegion,zs,oz.rd,oz.wr] using ht.readable,
      by simpa only [NttR.sRegion,zs] using ht.output,by simpa only [NttR.sRegion,zs] using ht.scratch⟩
  exact NttR.nttInv16_call z0 (by rw [oz.mem]; exact hp.1) (by rw [oz.wr]; exact Covers.head hc) table
    fun t kt pt=>⟨(Kept.of_keep oz.keep oz.mem (by decide)).trans
      (kt.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self),
      by simpa only [oz.mem,hp.2] using pt⟩

end VG.Proof.MlKem.AArch64.Ntt16.W
