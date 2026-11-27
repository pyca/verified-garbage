module

public import VerifiedGarbage.Proof.Sm4.X86.CtrFinal
public import VerifiedGarbage.Proof.Sm4.X86.AesNiWideModes
public import VerifiedGarbage.Impl.Sm4.X86.AesNiWideFn
import VerifiedGarbage.Proof.Sm4.X86.AesNiWideLit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Sm4.X86.CtrFinal
meta import VerifiedGarbage.Proof.Sm4.X86.AesNiWideModes
meta import VerifiedGarbage.Impl.Sm4.X86.AesNiWideFn
meta import VerifiedGarbage.Proof.Sm4.X86.AesNiWideLit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# `Sm4Ctr` on x86 (32-bit): the AES S-box

`Impl.Sm4.X86.AesNiWide.ctrFramed`, CTR over the core that enciphers four
blocks at a time, in its frame, as the internal function
`vg_sm4_ctr_core_aesni`, with the stack that `vg_sm4_ctr_final` leaves the
code it calls (`Proof.Sm4.X86.CtrFinal.calleeK`), and the doublewords that
function zeroes when it calls it.
-/

@[expose] public section

namespace VG.Proof.Variants.Sm4Ctr.X86.AesNi

open VG VG.X86 VG.X86.Scrub

def variant : Proof.Sm4.X86.CtrFinal.CtrImpl where
  name := "vg_sm4_ctr_core_aesni"
  code := Impl.Sm4.X86.AesNiWide.ctrFramed
  ok := Proof.Sm4.X86.AesNiWide.Modes.ctr_framedK.1
  ct := Proof.Sm4.X86.AesNiWide.Modes.ctr_framedK.2.1
  nosp := NoSp.of_all (by unfold Impl.Sm4.X86.AesNiWide.ctrFramed; lit_decide)
  stack := by unfold Impl.Sm4.X86.AesNiWide.ctrFramed; lit_decide
  spSafe := Code.all_of_spTest (by unfold Impl.Sm4.X86.AesNiWide.ctrFramed; lit_decide)
  suffix := "_aesni"
  features := ["aes", "ssse3"]
  words := Impl.Sm4.X86.AesNiWide.Fn.ctrFinalWords
  wordsOk := by decide
  residue := by exact ⟨_, by taint_decide_ct⟩

end VG.Proof.Variants.Sm4Ctr.X86.AesNi
