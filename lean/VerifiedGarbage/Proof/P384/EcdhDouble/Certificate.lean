module

public import VerifiedGarbage.Impl.P384.EcdhDouble
meta import VerifiedGarbage.Impl.P384.EcdhDouble
public import VerifiedGarbage.Impl.P384.EcdhAllocatedCode
meta import VerifiedGarbage.Impl.P384.EcdhAllocatedCode
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Kernel
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Checked
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Kernel
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Observed
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Observed
public import VerifiedGarbage.Proof.Weierstrass.AArch64.AllocatedFrame
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.AllocatedFrame
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint

import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
meta import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# P-384's allocated doublings agree with their raw arithmetic

For each direction (`R` into `D`, and `D` into `R`), the allocated code
(`Impl/P384/EcdhAllocatedCode.lean`) leaves every word of the working space
but the spill slots (`EcdhDouble.spillSlots`) as the raw doubling does
(`refine`), changes only the registers `EcdhDouble.regs` and the slots of
the output and the spills (`work`), and runs in constant time (`ct`).
-/

@[expose] public section

namespace VG.Proof.P384.EcdhDouble.Certificate
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64 VG.Impl.P384.EcdhDouble
open VG.Proof.Weierstrass.AArch64.Forward

/-- The words both blocks must agree on: all but the spill slots. -/
def observe (off : Nat) : Prop := ∀ x ∈ spillSlots, off < x ∨ x + 48 ≤ off
instance (off : Nat) : Decidable (observe off) := by unfold observe; infer_instance

/-- What the allocated blocks into `b` write. -/
def work (b : Pt) : List (Nat × Nat) := ([b.x, b.y, b.z] ++ spillSlots).map (·, 48)

/-! ## `R` into `D` -/

def originalRD := raw K.R K.D
def optimizedRD := Impl.P384.EcdhAllocatedCode.doubleRD
materialize_value leftRD := originalRD
materialize_value rightRD := optimizedRD
forward_state bundleRD :=
  let ns := (buildPair 8192 originalRD optimizedRD).getD ⟨.empty,.empty⟩
  (ns,(evalData (certDom ns) 8192 originalRD initialEnv).getD (.empty,.empty,none),
    (evalData (certDom ns) 8192 optimizedRD initialEnv).getD (.empty,.empty,none))
noncomputable def nodesRD := bundleRD.1
theorem originalRD_lit : originalRD = leftRD.lit := leftRD.lit_eq
theorem optimizedRD_lit : optimizedRD = rightRD.lit := rightRD.lit_eq

theorem validRD : CertValid nodesRD := valid_of_validK (by decide +kernel)
theorem inputsRD : Inputs nodesRD 8192 := inputs_of_allBelow (by decide +kernel)

noncomputable def leftEnvRD : Env Nat := fromData initialEnv bundleRD.2.1
noncomputable def rightEnvRD : Env Nat := fromData initialEnv bundleRD.2.2

theorem evalLeftRD : eval (certDom nodesRD) 8192 originalRD initialEnv = some leftEnvRD := by
  rw [originalRD_lit]
  exact eval_of_dataK (by kernel_rfl)

theorem evalRightRD : eval (certDom nodesRD) 8192 optimizedRD initialEnv = some rightEnvRD := by
  rw [optimizedRD_lit]
  exact eval_of_dataK (by kernel_rfl)

theorem sameRD : ∀ off, observe off → off % 8 = 0 → off + 8 ≤ 8192 →
    leftEnvRD.slot off = rightEnvRD.slot off :=
  fun off hv _ _ => same_of_sameK observe (by decide +kernel) off hv

theorem leftBoundRD : ∀ i ∈ originalRD, instrBound i ≤ 8192 := by
  rw [originalRD_lit]; exact bound_of_listAllK (by decide +kernel)

private theorem rightOkRD : listAllK (instrOkK 8192 (RegSet.ofList regs) (work K.D)) rightRD.lit = true := by
  decide +kernel

theorem rightBoundRD : ∀ i ∈ optimizedRD, instrBound i ≤ 8192 := by
  rw [optimizedRD_lit]; exact bound_of_instrOk rightOkRD

theorem clobRD : ∀ r ∈ optimizedRD.flatMap instrClob, r ∈ regs := by
  rw [optimizedRD_lit]; exact clob_of_instrOk rightOkRD

theorem writesRD : ∀ w ∈ optimizedRD.flatMap instrWrites,
    ∃ w' ∈ work K.D, w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2 := by
  rw [optimizedRD_lit]; exact cover_of_instrOk rightOkRD

noncomputable def checkedRD : CheckedObserved 8192 observe originalRD optimizedRD where
  nodes := nodesRD
  valid := validRD
  initial := initialEnv
  left := leftEnvRD
  right := rightEnvRD
  evalLeft := evalLeftRD
  evalRight := evalRightRD
  same := sameRD

open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass.AArch64 in
/-- The allocated block refines the raw one. -/
theorem refineRD {base : Addr} {s : State} (hs : Scr s base 8192) {Q : State → Prop}
    (hq : WP isa (.block originalRD) s Q) :
    WP isa (.block optimizedRD) s fun t => ∃ u, Q u ∧
      (∀ off, observe off → off % 8 = 0 → off + 8 ≤ 8192 → word t.mem base off = word u.mem base off) ∧
      AllocatedFrame regs base (work K.D) s t :=
  WP.mono (checkedRD.refine (word s.mem base) (by decide) hs (initial_rel inputsRD s base)
    leftBoundRD rightBoundRD hq) fun _ ⟨u, hu, hw, hk, hm⟩ => ⟨u, hu, hw, hk.mono clobRD, hm.cover writesRD⟩

theorem ctRD : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0]))
    (.block optimizedRD) := by
  rw [optimizedRD_lit]
  exact VG.Taint.constantTime (A := taint) (hc := .block (List.replicate 5 (Taint.ofRegs [.x0])))
    (Taint.ofRegs [.x0]) (fun _ _ _ _ h => h) (by decide +kernel)

/-! ## `D` into `R` -/

def originalDR := raw K.D K.R
def optimizedDR := Impl.P384.EcdhAllocatedCode.doubleDR
materialize_value leftDR := originalDR
materialize_value rightDR := optimizedDR
forward_state bundleDR :=
  let ns := (buildPair 8192 originalDR optimizedDR).getD ⟨.empty,.empty⟩
  (ns,(evalData (certDom ns) 8192 originalDR initialEnv).getD (.empty,.empty,none),
    (evalData (certDom ns) 8192 optimizedDR initialEnv).getD (.empty,.empty,none))
noncomputable def nodesDR := bundleDR.1
theorem originalDR_lit : originalDR = leftDR.lit := leftDR.lit_eq
theorem optimizedDR_lit : optimizedDR = rightDR.lit := rightDR.lit_eq

theorem validDR : CertValid nodesDR := valid_of_validK (by decide +kernel)
theorem inputsDR : Inputs nodesDR 8192 := inputs_of_allBelow (by decide +kernel)

noncomputable def leftEnvDR : Env Nat := fromData initialEnv bundleDR.2.1
noncomputable def rightEnvDR : Env Nat := fromData initialEnv bundleDR.2.2

theorem evalLeftDR : eval (certDom nodesDR) 8192 originalDR initialEnv = some leftEnvDR := by
  rw [originalDR_lit]
  exact eval_of_dataK (by kernel_rfl)

theorem evalRightDR : eval (certDom nodesDR) 8192 optimizedDR initialEnv = some rightEnvDR := by
  rw [optimizedDR_lit]
  exact eval_of_dataK (by kernel_rfl)

theorem sameDR : ∀ off, observe off → off % 8 = 0 → off + 8 ≤ 8192 →
    leftEnvDR.slot off = rightEnvDR.slot off :=
  fun off hv _ _ => same_of_sameK observe (by decide +kernel) off hv

theorem leftBoundDR : ∀ i ∈ originalDR, instrBound i ≤ 8192 := by
  rw [originalDR_lit]; exact bound_of_listAllK (by decide +kernel)

private theorem rightOkDR : listAllK (instrOkK 8192 (RegSet.ofList regs) (work K.R)) rightDR.lit = true := by
  decide +kernel

theorem rightBoundDR : ∀ i ∈ optimizedDR, instrBound i ≤ 8192 := by
  rw [optimizedDR_lit]; exact bound_of_instrOk rightOkDR

theorem clobDR : ∀ r ∈ optimizedDR.flatMap instrClob, r ∈ regs := by
  rw [optimizedDR_lit]; exact clob_of_instrOk rightOkDR

theorem writesDR : ∀ w ∈ optimizedDR.flatMap instrWrites,
    ∃ w' ∈ work K.R, w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2 := by
  rw [optimizedDR_lit]; exact cover_of_instrOk rightOkDR

noncomputable def checkedDR : CheckedObserved 8192 observe originalDR optimizedDR where
  nodes := nodesDR
  valid := validDR
  initial := initialEnv
  left := leftEnvDR
  right := rightEnvDR
  evalLeft := evalLeftDR
  evalRight := evalRightDR
  same := sameDR

open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass.AArch64 in
/-- The allocated block refines the raw one. -/
theorem refineDR {base : Addr} {s : State} (hs : Scr s base 8192) {Q : State → Prop}
    (hq : WP isa (.block originalDR) s Q) :
    WP isa (.block optimizedDR) s fun t => ∃ u, Q u ∧
      (∀ off, observe off → off % 8 = 0 → off + 8 ≤ 8192 → word t.mem base off = word u.mem base off) ∧
      AllocatedFrame regs base (work K.R) s t :=
  WP.mono (checkedDR.refine (word s.mem base) (by decide) hs (initial_rel inputsDR s base)
    leftBoundDR rightBoundDR hq) fun _ ⟨u, hu, hw, hk, hm⟩ => ⟨u, hu, hw, hk.mono clobDR, hm.cover writesDR⟩

theorem ctDR : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0]))
    (.block optimizedDR) := by
  rw [optimizedDR_lit]
  exact VG.Taint.constantTime (A := taint) (hc := .block (List.replicate 5 (Taint.ofRegs [.x0])))
    (Taint.ofRegs [.x0]) (fun _ _ _ _ h => h) (by decide +kernel)

end VG.Proof.P384.EcdhDouble.Certificate
