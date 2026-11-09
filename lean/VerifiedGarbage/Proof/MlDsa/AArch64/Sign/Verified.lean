module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Inst
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Inv
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.SignCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Correct
public import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-DSA signing on AArch64: verified

The internal `signContractT` has the same outcome and full rejection
leakage as `signContract`. It permits stopping at the first failing
response or low-part polynomial; coefficient norm checks remain complete.
-/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sign

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- `signContract`, with `signLeak` for `signLeak`. -/
def signContractT (p : Params) {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (signSig p).contract A
    (post := fun sk mu rnd sig _scratch m m' r =>
      Outcome (fun b => signMu p b (bytesAt m sk p.skLen) (bytesAt m mu 64) (bytesAt m rnd 32)) r
        (bytesAt m' sig p.sigLen))
    (writeArgs := true)
    (stack := stack)
    (leak := some fun sk mu rnd _sig _scratch m =>
      signLeak p (bytesAt m sk p.skLen) (bytesAt m mu 64) (bytesAt m rnd 32))

/-- A state satisfying `signContractT`'s precondition. -/
def signSat (p : Params) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x3000 | .x2 => 0x3100 | .x3 => 0x4000 | .x4 => 0x10000 | _ => 0
  sp := 0x80000
  mem _ := 0
  rd := [⟨0x1000, p.skLen⟩, ⟨0x3000, 64⟩, ⟨0x3100, 32⟩]
  wr := [⟨0x4000, p.sigLen⟩, ⟨0x10000, 8 * scratchWords p⟩]

end VG.Proof.MlDsa.AArch64.Sign
