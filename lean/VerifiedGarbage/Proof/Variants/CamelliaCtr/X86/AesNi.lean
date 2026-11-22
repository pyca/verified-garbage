module

public import VerifiedGarbage.Proof.Camellia.X86.CtrFinal
public import VerifiedGarbage.Proof.Camellia.X86.AesNiWideModes
public import VerifiedGarbage.Impl.Camellia.X86.AesNiWideFn
import VerifiedGarbage.Proof.Camellia.X86.AesNiWideLit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Camellia.X86.CtrFinal
meta import VerifiedGarbage.Proof.Camellia.X86.AesNiWideModes
meta import VerifiedGarbage.Impl.Camellia.X86.AesNiWideFn
meta import VerifiedGarbage.Proof.Camellia.X86.AesNiWideLit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# `CamelliaCtr` on x86 (32-bit): the AES S-box

`Impl.Camellia.X86.AesNiWide.ctrFramed`, CTR over the core that enciphers
four blocks at a time, in its frame, as the internal function
`vg_camellia_ctr_core_aesni`, with the stack that `vg_camellia_ctr_final`
leaves the code it calls (`Proof.Camellia.X86.CtrFinal.calleeK`), and the
doublewords that function zeroes when it calls it.
-/

@[expose] public section

namespace VG.Proof.Variants.CamelliaCtr.X86.AesNi

open VG VG.X86 VG.X86.Scrub

def variant : Proof.Camellia.X86.CtrFinal.CtrImpl where
  name := "vg_camellia_ctr_core_aesni"
  code := Impl.Camellia.X86.AesNiWide.ctrFramed
  ok := Proof.Camellia.X86.AesNiWide.Modes.ctr_framedK.1
  ct := Proof.Camellia.X86.AesNiWide.Modes.ctr_framedK.2.1
  nosp := NoSp.of_all (by unfold Impl.Camellia.X86.AesNiWide.ctrFramed; lit_decide)
  stack := by unfold Impl.Camellia.X86.AesNiWide.ctrFramed; lit_decide
  spSafe := Code.all_of_spTest (by unfold Impl.Camellia.X86.AesNiWide.ctrFramed; lit_decide)
  suffix := "_aesni"
  features := ["aes", "ssse3"]
  words := Impl.Camellia.X86.AesNiWide.Fn.ctrFinalWords
  wordsOk := by decide
  residue := by exact ⟨_, by taint_decide_ct⟩

end VG.Proof.Variants.CamelliaCtr.X86.AesNi
