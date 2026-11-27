module

public import VerifiedGarbage.Impl.RsaPss.RISCV64.Fn
public import VerifiedGarbage.Proof.RsaPss.RISCV64.SignP
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
public import VerifiedGarbage.Proof.Rsa.RISCV64.Scrub

/-!
# RSASSA-PSS on RISC-V, as emitted

`vg_rsa_pss_verify_precomputed` and `vg_rsa_pss_sign_precomputed`, over the
Merkle–Damgård hash functions of their tables, with their cleanup
(`Impl.RsaPss.RISCV64.Fn`): each meets its contract in constant time and
returns without secret residue (`VerifiedScrubbed`, by
`RISCV64.Scrub.verifiedScrubbedAll`), which is what its registration binds. What
the cleanup needs of each function's code (`Scrub.scrubSide`) is evaluated
here, by the kernel, apart from the theorems, which take the tables'
coherence (`OK`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.RISCV64.Fn

open VG.RISCV64 VG.RISCV64.Scrub
open VG.Proof.MdHashTable.RISCV64 (vars tables fnsOf fns3)

theorem verifyPrecomputed_side :
    scrubSide (Impl.RsaPss.RISCV64.verifyPrecomputed (fnsOf vars) (fns3 vars)) 336 32
      [("hash", tables vars), ("mgf1", tables vars)] = true := by
  lit_decide

theorem signPrecomputed_side :
    scrubSide (Impl.RsaPss.RISCV64.Sign.signP (fnsOf vars) (fns3 vars)) 3488 32
      [("hash", tables vars), ("mgf1", tables vars)] = true := by
  lit_decide

theorem verifyPrecomputed (h : OK vars vars) :
    VerifiedScrubbed target (Impl.RsaPss.RISCV64.Fn.verifyPrecomputed (fnsOf vars) (fns3 vars))
      (Spec.RsaPss.verifyPrecomputedMdTableContract
        (abi.withTables Spec.RsaPss.verifyPrecomputedMdTableSig
          [("hash", tables vars), ("mgf1", tables vars)]) 336) 32 :=
  verifiedScrubbedAll (api := Spec.RsaPss.verifyPrecomputedMdTableApi) (W := 336)
    { tables := [("hash", tables vars), ("mgf1", tables vars)]
      code := Impl.RsaPss.RISCV64.verifyPrecomputed (fnsOf vars) (fns3 vars)
      verified := verify_ok h }
    (Proof.Rsa.RISCV64.Scrub.pssVerifyOut _ _ _) verifyPrecomputed_side

theorem signPrecomputed (h : OK vars vars) :
    VerifiedScrubbed target (Impl.RsaPss.RISCV64.Fn.signPrecomputed (fnsOf vars) (fns3 vars))
      (Spec.RsaPss.signPrecomputedMdTableContract
        (abi.withTables Spec.RsaPss.signPrecomputedMdTableSig
          [("hash", tables vars), ("mgf1", tables vars)]) 3488) 32 :=
  verifiedScrubbedAll (api := Spec.RsaPss.signPrecomputedMdTableApi) (W := 3488)
    { tables := [("hash", tables vars), ("mgf1", tables vars)]
      code := Impl.RsaPss.RISCV64.Sign.signP (fnsOf vars) (fns3 vars)
      verified := signP_ok h }
    (Proof.Rsa.RISCV64.Scrub.pssSignOut _ _ _) signPrecomputed_side

end VG.Proof.RsaPss.RISCV64.Fn
