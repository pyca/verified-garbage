module

public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Fast
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
public import VerifiedGarbage.Proof.Framework.AArch64.Inline
public import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.MlKem.AArch64.NttR.LitF

/-!
# ML-KEM on AArch64: `vg_mlkem16_ntt` keeps what the ABI preserves

`fwdFast` keeps the low halves of `v8`–`v15` in `x7`–`x14` (`save`), which
the transform (`core`) does not write, and puts them back at the end
(`restore`); it writes none of `x19`–`x28` and `x30`, and leaves `sp` alone.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.NttR

open VG VG.AArch64 VG.Impl.MlKem.AArch64.Ntt16.Fast

/-- `x7 + k` kept in lane 0 of `v8 + k`. -/
def lanesF : List (Reg × VReg × Nat) :=
  [(.x7, .v8, 0), (.x8, .v9, 0), (.x9, .v10, 0), (.x10, .v11, 0),
   (.x11, .v12, 0), (.x12, .v13, 0), (.x13, .v14, 0), (.x14, .v15, 0)]

theorem save_eq : save = umovOf lanesF ++ ([.adrSym .x1 name, .addImm .x .x2 .x1 160] : List Instr) := rfl

theorem restore_eq : restore = insOf lanesF := rfl

theorem save_ok (s : State) :
    WP isa (.block save) s fun t => ∀ k ∈ lanesF, t.gpr k.1 = laneOf s k.2.1 k.2.2 := by
  rw [save_eq]
  refine WP.block_append (WP.mono (umovOf_ok lanesF s (by decide) (by decide)) fun t ⟨_, _, _, _, ht, _⟩ => ?_)
  refine WP.block_cons_iff.mpr ⟨_, exec_adrSym, WP.block_cons_iff.mpr ⟨_, exec_addImm_x (imm := 160) (by decide), WP.block_nil ?_⟩⟩
  intro k hk
  have h1 : k.1 ≠ .x1 := by revert k; decide
  have h2 : k.1 ≠ .x2 := by revert k; decide
  rw [RegUpd.gpr_write_of_ne (s := _) _ _ h2, RegUpd.gpr_write_of_ne (s := _) _ _ h1]
  exact ht k hk

/-- No instruction of `core` writes `x7`–`x14`. -/
theorem core_keeps : core.allInstrs (fun i => lanesF.all fun k => !clobbers i k.1) = true := by
  decide +kernel

/-- No instruction of `fwdFast` writes `x19`–`x28` or `x30`. -/
theorem fwdFast_keeps : fwdFast.allInstrs (fun i => preserved.all fun r => !clobbers i r) = true := by
  lit_decide

theorem fwdFast_abi {s s' : State} {t : List Leak} (he : Exec isa fwdFast s t s') : abiPreserved s s' := by
  refine ⟨fun r hr => Exec.gpr (fun i hi => ?_) he, Exec.sp he, fun r hr => ?_⟩
  · have := List.all_eq_true.mp ((Code.allInstrs_eq _ fwdFast) ▸ fwdFast_keeps) i hi
    simpa using List.all_eq_true.mp this r hr
  · cases he with
    | seq h1 h23 =>
    cases h23 with
    | seq h2 h3 =>
    obtain ⟨_, t1, e1, hs⟩ := save_ok s
    have hk : ∀ k ∈ lanesF, ∀ i ∈ instrs core, clobbers i k.1 = false := fun k hk i hi => by
      have := List.all_eq_true.mp ((Code.allInstrs_eq _ core) ▸ core_keeps) i hi
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
