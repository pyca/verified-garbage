module

public import VerifiedGarbage.Proof.Seed.X86_64.CbcVerified
public import VerifiedGarbage.Proof.Seed.X86_64.ModesLit
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.TaintSum

/-! # SEED-CBC artifacts on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.SeedCbc.X86_64

/-- How the functions compute SEED, and the mode. -/
def note : String :=
  "Baseline x86-64: through `vg_seed_ecb_encrypt` and `vg_seed_ecb_decrypt`'s batch of sixteen blocks \
  (inlined), with SEED's S-boxes computed bitsliced from AES's circuit and no table lookups; decryption \
  deciphers sixteen blocks per batch; encryption, whose blocks depend on each other, one, with the other \
  fifteen lanes unused. The schedule is copied into the working space once per call. The mode is the \
  generic CBC of `Impl/Modes/X86_64/`."

def artifacts : List Artifact := [
  { Spec.Seed.cbcEncryptApi with
    target := X86_64.target
    doc := Spec.Seed.cbcEncryptApi.doc (notes := [note])
    code := Impl.StackScratch.X86_64.withStackScratchWiped 1512 .r8 188 Impl.Seed.X86_64.cbcEncrypt
    contract := Spec.Seed.cbcEncryptContract X86_64.abi 1512
    stack := 1512
    verified := Proof.Seed.X86_64.cbcEncrypt_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Seed.cbcDecryptApi with
    target := X86_64.target
    doc := Spec.Seed.cbcDecryptApi.doc (notes := [note])
    code := Impl.StackScratch.X86_64.withStackScratchWiped 1512 .r8 188 Impl.Seed.X86_64.cbcDecrypt
    contract := Spec.Seed.cbcDecryptContract X86_64.abi 1512
    stack := 1512
    verified := Proof.Seed.X86_64.cbcDecrypt_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.SeedCbc.X86_64
