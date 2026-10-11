import VerifiedGarbage.Proof.Seed.X86_64.FbVerified

/-! # SEED-CFB128 artifacts on baseline x86-64 -/

namespace VG.Artifacts.SeedCfb.X86_64

/-- How the functions compute SEED, and the mode. -/
def note : String :=
  "Baseline x86-64: through `vg_seed_ecb_encrypt` and `vg_seed_ecb_decrypt`'s batch of sixteen blocks \
  (inlined), with SEED's S-boxes computed bitsliced from AES's circuit and no table lookups; one block per \
  batch, of which the other fifteen lanes are unused. The schedule is copied into the working space once \
  per call. The mode is the generic CFB of `Impl/Modes/X86_64/`."

def artifacts : List Artifact := [
  { Spec.Seed.cfbEncryptApi with
    target := X86_64.target
    doc := Spec.Seed.cfbEncryptApi.doc (notes := [note])
    code := Impl.StackScratch.X86_64.withStackScratchWiped 1512 .r8 188 Impl.Seed.X86_64.cfbEncrypt
    contract := Spec.Seed.cfbEncryptContract X86_64.abi 1512
    stack := 1512
    verified := Proof.Seed.X86_64.cfbEncrypt_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Seed.cfbDecryptApi with
    target := X86_64.target
    doc := Spec.Seed.cfbDecryptApi.doc (notes := [note])
    code := Impl.StackScratch.X86_64.withStackScratchWiped 1512 .r8 188 Impl.Seed.X86_64.cfbDecrypt
    contract := Spec.Seed.cfbDecryptContract X86_64.abi 1512
    stack := 1512
    verified := Proof.Seed.X86_64.cfbDecrypt_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.SeedCfb.X86_64
