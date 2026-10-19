module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Prepared.Derive
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Prepared.Derive
import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Impl.Aes.AArch64.Alloc
import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
import VerifiedGarbage.Proof.AesGcm.AArch64.Env
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Gcm.Bits
import VerifiedGarbage.Proof.Gcm.Stream
meta import VerifiedGarbage.Impl.Aes.AArch64.Alloc
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Env
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Mem
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Gcm.Bits
meta import VerifiedGarbage.Proof.Gcm.Stream

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
      (Spec.Gcm.derivePrepared8Contract AArch64.abi) :=
  Verified.of_correct (derive_correct hP) derive_ct (by
    sig_implies [Spec.Gcm.derivePrepared8Contract, Spec.Gcm.derivePrepared8Sig, Spec.Gcm.derivePrepared8Post,
      derivePrepared8AArch64, AArch64.abi, AArch64.argRegs] [deriveSat] using deriveSat)

end VG.Proof.AesGcm.AArch64
