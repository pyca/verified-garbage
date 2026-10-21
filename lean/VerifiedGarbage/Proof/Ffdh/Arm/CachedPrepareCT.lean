module

public import VerifiedGarbage.Proof.Ffdh.Arm.CachedPrepareState
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.PrepareCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.PdImportCT
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Impl.Ffdh.Arm.CachedPrepare
meta import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack

/-! Cached preparation composes the existing public RSA setup, import and inverse timing laws. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem cachedPrepareSource_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block VG.Impl.Ffdh.Arm.CachedPrepare.source) (fun _ _ => True) := by
  have add : RelCT isa (fun _ _ : State => True)
      (.block [.dp .add .r4 .r4 (.imm 24)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  exact RelCT.block_append ((loadStack_ct .r4 52).seq (add.mono (fun _ _ _ => trivial) (fun _ _ h => h)))

theorem cachedPrepareBody_ct {p : Inputs} {slots : List Nat}
    (stable : stableSlots slots = true) (h52 : 52 ∈ slots) :
    RelCT isa (fun s t => CachedPrepareInitial p slots s ∧ CachedPrepareInitial p slots t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.CachedPrepare.body (fun _ _ => True) := by
  have init := (prepareInput_ct (base := p.base) (src := p.domain) (len := p.len) (k := p.k)).mono
    (P' := fun (s t : State) => CachedPrepareInitial p slots s ∧ CachedPrepareInitial p slots t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.input, h.2.1.input, h.2.2⟩) (fun _ _ h => h)
  have source := cachedPrepareSource_ct.mono
    (P' := fun (s t : State) => CachedPrepareReady p slots s ∧ CachedPrepareReady p slots t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ h => h)
  have imported := pdImport_ct.mono
    (P' := fun (s t : State) => CachedPrepareLoaded p s ∧ CachedPrepareLoaded p t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.input, h.2.1.input⟩) (fun _ _ h => h)
  have inverse := precomputeInverse_ct.mono
    (P' := fun (s t : State) => PrecomputeModulus p.base p.len p.w s ∧
      PrecomputeModulus p.base p.len p.w t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1, h.2.1⟩) (fun _ _ h => h)
  exact relCT_chain init (cachedPrepare_init_next · stable) (cachedPrepare_init_next · stable)
    (relCT_chain source (cachedPrepare_source_next · h52) (cachedPrepare_source_next · h52)
      (relCT_chain imported (fun s h => cachedPrepare_import_next s h) (fun s h => cachedPrepare_import_next s h) inverse))

end VG.Proof.Ffdh.Arm
