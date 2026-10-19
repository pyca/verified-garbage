module

public import VerifiedGarbage.Proof.Dsa.X86_64.PublicScheduleCT
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.X86_64.PublicScheduleCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Constant time of DSA domain and public-key validation -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem publicKey_ct (M : Mont) (Sq : MontS) (inputs : SchedulePublic → List (Operand × Nat))
    (stable : ∀ p a, a ∈ inputs p → a.1.length ≠ .mask ∧ stablePointer a.1.pointer)
    (hg : ∀ p, (Core.generator, p.layout.pLen) ∈ inputs p)
    (hy : ∀ p, (Core.publicValue, p.layout.pLen) ∈ inputs p)
    (_hq : ∀ p, (⟨.input .q, .qLen⟩, p.layout.qLen) ∈ inputs p) :
    RelCT isa (Two (PublicKeyPre inputs)) (Checks.publicKey Sq.mm M.mm)
      (Two (ScheduleState inputs)) := by
  have hgct := publicSubgroup_ct M Sq inputs stable Core.generator (by trivial) (by simp [stablePointer, Core.generator]) hg (by taint_decide)
  have hyct := publicSubgroup_ct M Sq inputs stable Core.publicValue (by trivial) (by simp [stablePointer, Core.publicValue]) hy (by taint_decide)
  have hone := publicIsOne_ct inputs stable
  unfold Checks.publicKey
  apply RelCT.seqs_append (a := [Checks.range pWorkspace Core.generator true,
    Checks.range pWorkspace Core.publicValue true, Checks.modulusMinus pWorkspace 1 (Core.element t),
    Core.reduce M.mm (Core.element t) (Core.scalar u), Checks.zero (Core.scalar u),
    Checks.modulusMinus qWorkspace 2 (Core.scalar qMinusTwo)]) (by simp) (by simp)
  exact (RelCT.seq (publicPrefix_known_ct M inputs stable hg hy)
    (RelCT.seq hgct (RelCT.seq hone (RelCT.seq hyct hone)))).mono
    (fun _ _ h => h) (fun _ _ ⟨p, hs, ht⟩ => ⟨p, hs.1, ht.1⟩)

theorem signingKey_ct (M : Mont) (Sq : MontS) (inputs : SchedulePublic → List (Operand × Nat))
    (stable : ∀ p a, a ∈ inputs p → a.1.length ≠ .mask ∧ stablePointer a.1.pointer)
    (hg : ∀ p, (Core.generator, p.layout.pLen) ∈ inputs p)
    (hy : ∀ p, (Core.publicValue, p.layout.pLen) ∈ inputs p)
    (_hq : ∀ p, (⟨.input .q, .qLen⟩, p.layout.qLen) ∈ inputs p) :
    RelCT isa (Two (PublicKeyPre inputs)) (Checks.signingKey Sq.mm M.mm)
      (Two (ScheduleState inputs)) := by
  have hgct := publicSubgroup_ct M Sq inputs stable Core.generator (by trivial) (by simp [stablePointer, Core.generator]) hg (by taint_decide)
  have hone := publicIsOne_ct inputs stable
  unfold Checks.signingKey
  apply RelCT.seqs_append (a := [Checks.range pWorkspace Core.generator true,
    Checks.range pWorkspace Core.publicValue true, Checks.modulusMinus pWorkspace 1 (Core.element t),
    Core.reduce M.mm (Core.element t) (Core.scalar u), Checks.zero (Core.scalar u),
    Checks.modulusMinus qWorkspace 2 (Core.scalar qMinusTwo)]) (by simp) (by simp)
  exact (RelCT.seq (publicPrefix_known_ct M inputs stable hg hy)
    (RelCT.seq hgct hone)).mono
    (fun _ _ h => h) (fun _ _ ⟨p, hs, ht⟩ => ⟨p, hs.1, ht.1⟩)

end VG.Proof.Dsa.X86_64
