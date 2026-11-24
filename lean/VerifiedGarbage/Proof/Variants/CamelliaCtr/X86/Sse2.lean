module

public import VerifiedGarbage.Proof.Camellia.X86.CtrFinal
public import VerifiedGarbage.Proof.Camellia.X86.SseModes
public import VerifiedGarbage.Impl.Camellia.X86.SseFn
import VerifiedGarbage.Proof.Camellia.X86.SseLit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Camellia.X86.CtrFinal
meta import VerifiedGarbage.Proof.Camellia.X86.SseModes
meta import VerifiedGarbage.Impl.Camellia.X86.SseFn
meta import VerifiedGarbage.Proof.Camellia.X86.SseLit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# `CamelliaCtr` on x86 (32-bit): XMM registers, without AES-NI

`Impl.Camellia.X86.Sse.ctrFramed`, CTR over the core that enciphers
sixteen blocks at a time, in its frame, as the internal function
`vg_camellia_ctr_core`, with the stack that `vg_camellia_ctr_final`
leaves the code it calls (`Proof.Camellia.X86.CtrFinal.calleeK`), and the
doublewords that function zeroes when it calls it.
-/

@[expose] public section

namespace VG.Proof.Variants.CamelliaCtr.X86.Sse2

open VG VG.X86 VG.X86.Scrub

def variant : Proof.Camellia.X86.CtrFinal.CtrImpl where
  name := "vg_camellia_ctr_core"
  code := Impl.Camellia.X86.Sse.ctrFramed
  ok := Proof.Camellia.X86.Sse.Modes.ctr_framedK.1
  ct := Proof.Camellia.X86.Sse.Modes.ctr_framedK.2.1
  nosp := NoSp.of_all (by unfold Impl.Camellia.X86.Sse.ctrFramed; lit_decide)
  stack := by unfold Impl.Camellia.X86.Sse.ctrFramed; lit_decide
  spSafe := Code.all_of_spTest (by unfold Impl.Camellia.X86.Sse.ctrFramed; lit_decide)
  suffix := ""
  features := []
  words := Impl.Camellia.X86.Sse.Fn.ctrFinalWords
  wordsOk := by decide
  residue := by exact ⟨_, by taint_decide_ct⟩

end VG.Proof.Variants.CamelliaCtr.X86.Sse2
