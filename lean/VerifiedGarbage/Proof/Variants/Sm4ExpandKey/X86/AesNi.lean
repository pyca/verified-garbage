module

public import VerifiedGarbage.Proof.Sm4Gcm.X86.CtrCall
public import VerifiedGarbage.Proof.Sm4.X86.AesNiKey
import VerifiedGarbage.Proof.Sm4.X86.AesNiKeyLit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit

/-!
# `Sm4ExpandKey` on x86 (32-bit): the AES S-box

`Impl.Sm4.X86.AesNiKey.expandKey`, as the internal function
`vg_sm4_expand_key_core_aesni`, with the stack that `vg_sm4_gcm_init` leaves
the key schedule it calls (`Proof.Sm4Gcm.X86.keyK`).
-/

@[expose] public section

namespace VG.Proof.Variants.Sm4ExpandKey.X86.AesNi

open VG VG.X86

def variant : Proof.Sm4Gcm.X86.KeyImpl where
  fn := ⟨"vg_sm4_expand_key_core_aesni", Impl.Sm4.X86.AesNiKey.expandKey⟩
  ok := Proof.Sm4.X86.AesNiKey.expandKey_verifiedK.1
  ct := Proof.Sm4.X86.AesNiKey.expandKey_verifiedK.2.1
  nosp := NoSp.of_all (by lit_decide)
  stack := by lit_decide
  spSafe := Code.all_of_spTest (by lit_decide)
  scrub := by lit_decide
  suffix := "_aesni"
  features := ["aes", "ssse3"]

end VG.Proof.Variants.Sm4ExpandKey.X86.AesNi
