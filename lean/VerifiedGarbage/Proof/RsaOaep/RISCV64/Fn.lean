module

public import VerifiedGarbage.Impl.RsaOaep.RISCV64.Fn
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Inst
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
public import VerifiedGarbage.Proof.Rsa.RISCV64.Scrub

/-!
# RSAES-OAEP on RISC-V, as emitted

`vg_rsa_oaep_decrypt_precomputed` and `vg_rsa_oaep_encrypt_precomputed`, over
the Merkle–Damgård hash functions of their tables, with their cleanup
(`Impl.RsaOaep.RISCV64.Fn`): each meets its contract in constant time and
returns without secret residue (`VerifiedScrubbed`, by
`RISCV64.Scrub.verifiedScrubbed`), which is what its registration binds. What
the cleanup needs of each function's code (`Scrub.scrubSide`) is evaluated
here, by the kernel, apart from the theorems, which take the tables'
coherence (`OK`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.RISCV64.Fn

open VG.RISCV64 VG.RISCV64.Scrub
open VG.Proof.MdHashTable.RISCV64 (vars tables fns3)

theorem decryptPrecomputed_side :
    scrubSide (Impl.RsaOaep.RISCV64.Dec.decryptP (fns3 vars)) 3488 32
      [("hash", tables vars), ("mgf1", tables vars)] = true := by
  lit_decide

theorem encryptPrecomputed_side :
    scrubSide (Impl.RsaOaep.RISCV64.encrypt (fns3 vars)) 336 32
      [("hash", tables vars), ("mgf1", tables vars)] = true := by
  lit_decide

theorem decryptPrecomputed (h : OK vars) :
    VerifiedScrubbed target (Impl.RsaOaep.RISCV64.Fn.decryptPrecomputed (fns3 vars))
      (Spec.RsaOaep.decryptPrecomputedMdTablesContract
        (abi.withTables Spec.RsaOaep.decryptPrecomputedMdTablesSig
          [("hash", tables vars), ("mgf1", tables vars)]) 3488) 32 :=
  verifiedScrubbed (api := Spec.RsaOaep.decryptPrecomputedMdTablesApi) (W := 3488)
    { tables := [("hash", tables vars), ("mgf1", tables vars)]
      code := Impl.RsaOaep.RISCV64.Dec.decryptP (fns3 vars)
      verified := decP_ok vars h }
    (Proof.Rsa.RISCV64.Scrub.oaepDecryptOut _ _) decryptPrecomputed_side

theorem encryptPrecomputed (h : OK vars) :
    VerifiedScrubbed target (Impl.RsaOaep.RISCV64.Fn.encryptPrecomputed (fns3 vars))
      (Spec.RsaOaep.encryptMdTablesContract
        (abi.withTables Spec.RsaOaep.encryptMdTablesSig
          [("hash", tables vars), ("mgf1", tables vars)]) 336) 32 :=
  verifiedScrubbed (api := Spec.RsaOaep.encryptMdTablesApi) (W := 336)
    { tables := [("hash", tables vars), ("mgf1", tables vars)]
      code := Impl.RsaOaep.RISCV64.encrypt (fns3 vars)
      verified := enc_ok vars h }
    (Proof.Rsa.RISCV64.Scrub.oaepEncryptOut _ _) encryptPrecomputed_side

end VG.Proof.RsaOaep.RISCV64.Fn
