module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Prepared.Derive
public import VerifiedGarbage.Proof.Gcm.Prepared8Contract
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
import VerifiedGarbage.Proof.Aes.KeyExp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Prepared.Derive
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
meta import VerifiedGarbage.Proof.Aes.KeyExp
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TacticTemplate

/-!
# AES-GCM on AArch64: `vg_aes_gcm_derive_prepared8` is `Verified`

Untrusted: everything here is checked by Lean. Correctness (`derive_wp`, for
the algebra `PrepPow`), constant time (every load, store and branch depends
only on the two pointers), a state satisfying the precondition, and the
shared contract.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.Impl.AesGcm.AArch64
open VG.Proof.Gcm.AArch64.Pmull (PrepPow)

theorem derive_correct (hP : PrepPow) (s : State) (hs : derivePrepared8AArch64.pre s) :
    ∃ t s', Exec isa Impl.AesGcm.AArch64.Prepared.derive s t s' ∧ abiPreserved s s' ∧
      derivePrepared8AArch64.post s s' :=
  WP.withPreservedV (derive_wp hP hs) (by lit_decide)

theorem derive_ct : ConstantTime isa derivePrepared8AArch64.pre derivePrepared8AArch64.pub
    Impl.AesGcm.AArch64.Prepared.derive := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h0, h1, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h0
  · exact h1

/-- A state satisfying `vg_aes_gcm_derive_prepared8`'s precondition. -/
def deriveSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | _ => 0
  sp := 0x5000
  mem _ := 0
  rd := [⟨0x1000, 256⟩]
  wr := [⟨0x2000, 384⟩]

theorem derive_verified (hP : PrepPow) :
    Verified AArch64.target Impl.AesGcm.AArch64.Prepared.derive
      (Proof.Gcm.derivePrepared8Contract AArch64.abi) :=
  Verified.of_correct (derive_correct hP) derive_ct (by
    sig_implies [Proof.Gcm.derivePrepared8Contract, Proof.Gcm.derivePrepared8Sig, Proof.Gcm.derivePrepared8Post,
      derivePrepared8AArch64, AArch64.abi, AArch64.argRegs] [deriveSat] using deriveSat)

end VG.Proof.AesGcm.AArch64
