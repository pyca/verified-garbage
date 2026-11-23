module

public import VerifiedGarbage.Proof.TripleDes.X86.Ssse3Core
public import VerifiedGarbage.Proof.TripleDes.X86.CbcVerified
public import VerifiedGarbage.Proof.Framework.X86.ScrubSel
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.X86.Scrub
import VerifiedGarbage.Proof.TripleDes.X86.Ssse3Lit
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.TripleDes.X86.Ssse3Core
meta import VerifiedGarbage.Proof.TripleDes.X86.CbcVerified
meta import VerifiedGarbage.Proof.Framework.X86.ScrubSel
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.TripleDes.X86.Scrub
meta import VerifiedGarbage.Proof.TripleDes.X86.Ssse3Lit
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# Triple DES's modes with its S-boxes by `pshufb` on x86 (32-bit) meet their contracts

`cbcEncryptChained_wp`: CBC encryption that updates the chaining value
(`Cbc.cbcEncryptChained_wp_of`) over the core of one block by `pshufb`
(`ssse3CoreSpec`, `ssse3Fits`), with the working space, 118 64-bit words,
as the fifth argument (`Fb.fbX86`): the contract, taint and narrowing
(`Fb.fb_verified`) of the functions over the other cores. It is constant
time by the taint analysis of its code with the SSE instructions
(`X86.sseTaint`); `_framed` runs it with its working space on the stack,
zeroed on return.

As emitted (`Impl.TripleDes.X86.Ssse3.Fn`), the function then zeroes, of the
984 bytes of stack its contract reserves below `esp`, the six doublewords
that the residue analysis (`X86.rtaint`) finds it may leave different in two
runs, the header of that frame, clears the registers a callee may change,
and returns without secret residue (`X86.Scrub.verifiedScrubbedSel`, the
kernel evaluating the analysis of the code with its cleanup:
`taint_decide_ct`).
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86.Ssse3

open VG VG.X86 VG.X86.Scrub VG.Impl.TripleDes.X86.Ssse3
open VG.Proof.TripleDes.X86.Fb
open VG.Proof.TripleDes.X86.Cbc (encPost cbcEncryptChained_wp_of wide_implies_enc)

theorem cbcEncryptChained_wp {s₀ : State} (hp : (fbX86 118 8 encPost).pre s₀) :
    WP isa cbcEncryptChained s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 118 8 encPost).post s₀ s' :=
  cbcEncryptChained_wp_of ssse3Fits (fun _ => rfl) hp

theorem cbcEncryptChained_ct :
    ConstantTime isa (fbX86 118 8 encPost).pre (fbX86 118 8 encPost).pub cbcEncryptChained :=
  VG.Taint.constantTime (A := VG.X86.sseTaint) (fbTaint 118) (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp)
    (by taint_decide)

theorem cbcEncryptChained_verified :
    Verified X86.target cbcEncryptChained (Proof.TripleDes.cbcEncChainedScratchContract X86.abi 118 16) :=
  fb_verified (fun _ hs => cbcEncryptChained_wp hs) cbcEncryptChained_ct (fun _ _ _ _ _ _ h => h) wide_implies_enc

/-- `cbcEncryptChained` with its working space on the stack. -/
theorem cbcEncryptChained_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 968 4 236 cbcEncryptChained)
      (Spec.TripleDes.cbcEncryptChainedContract X86.abi 984) :=
  X86.Verified.stackScratchWiped (sig := Spec.TripleDes.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 118) (post := Proof.TripleDes.cbcEncChainedPost X86.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 968) cbcEncryptChained_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.TripleDes.cbcEncChainedPost_local _) (Proof.TripleDes.cbcEncChainedPostOut_local _) (Cbc.frameSat_pre _)

/-! ## The functions as emitted -/

/-- `Spec.TripleDes.cbcEncryptChainedApi` as emitted (`Impl.TripleDes.X86.Ssse3.Fn.cbcEncryptChained`)
meets its contract in constant time and returns without secret residue. -/
theorem cbcEncryptChained_scrubbed :
    VerifiedScrubbed X86.target Fn.cbcEncryptChained (Spec.TripleDes.cbcEncryptChainedContract X86.abi 984) 0 :=
  verifiedScrubbedSel (api := Spec.TripleDes.cbcEncryptChainedApi) (W := 984)
    { code := Impl.StackScratch.X86.withStackScratchWiped 968 4 236 cbcEncryptChained
      verified := cbcEncryptChained_framed }
    Fn.words Scrub.cbcEncryptOut (by decide) ⟨_, by taint_decide_ct⟩

end VG.Proof.TripleDes.X86.Ssse3
