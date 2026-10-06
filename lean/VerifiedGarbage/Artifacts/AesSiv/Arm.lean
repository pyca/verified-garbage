import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.AesSiv.Arm.Frame

/-!
# AES-SIV (RFC 5297) on ARMv7

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation.

`init` calls `vg_cmac_aes_subkeys`, which uses 8 bytes of stack, and keeps
its 2560-byte working space in a frame of its own
(`Proof/AesSiv/Arm/Verified.lean`). `encrypt` and `decrypt` run in a frame
of 2608 bytes holding their working space (`Proof/AesSiv/Arm/Frame.lean`).
In it they call `vg_cmac_aes_update`, `vg_cmac_aes_finalize` and
`vg_aes_ctr32` in frames that push their two stack arguments, and the CMAC
functions' own frames push two more: 2624 bytes of stack in all.
-/

namespace VG.Artifacts.AesSiv.Arm

open VG.Proof.AesSiv.Arm

/-- Which functions `init` calls. -/
def initNote : String := "This implementation expands the keys with `vg_aes_expand_key_scratch` and computes the CMAC \
  subkeys with `vg_cmac_aes_subkeys`."

/-- Which functions `encrypt` and `decrypt` call. -/
def callNote : String := "This implementation computes S2V's CMACs with `vg_cmac_aes_update` and \
  `vg_cmac_aes_finalize`, and encrypts with `vg_aes_ctr32`."

def artifacts : List Artifact := [
  { Spec.Siv.initApi with
    target := Arm.target
    doc := Spec.Siv.initApi.doc (notes := [initNote])
    code := Impl.StackScratch.Arm.withRegScratch 2560 .r3 Impl.AesSiv.Arm.init
    contract := Spec.Siv.initContract Arm.abi 2568
    stack := 2568
    verified := init_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Siv.encryptApi with
    target := Arm.target
    doc := Spec.Siv.encryptApi.doc (notes := [callNote])
    code := Impl.StackScratch.Arm.withStackScratch 2608 3 Impl.AesSiv.Arm.encrypt
    contract := Spec.Siv.encryptContract Arm.abi 2624
    stack := 2624
    verified := encrypt_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Siv.decryptApi with
    target := Arm.target
    doc := Spec.Siv.decryptApi.doc (notes := [callNote,
      "It compares the synthetic IVs and overwrites the data with zeros without a branch on the result."])
    code := Impl.StackScratch.Arm.withStackScratch 2608 3 Impl.AesSiv.Arm.decrypt
    contract := Spec.Siv.decryptContract Arm.abi 2624
    stack := 2624
    verified := decrypt_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.AesSiv.Arm
