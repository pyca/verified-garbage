module

import VerifiedGarbage.Proof.Weierstrass.X86.TComb
meta import VerifiedGarbage.Proof.Weierstrass.X86.TComb
import VerifiedGarbage.Proof.Weierstrass.X86.TCombJ
meta import VerifiedGarbage.Proof.Weierstrass.X86.TCombJ
import VerifiedGarbage.Proof.Framework.X86.TaintSym
meta import VerifiedGarbage.Proof.Framework.X86.TaintSym
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.TCB.Axioms

/-! Audit the comb core before public artifacts are connected to it. -/

#assert_standard_axioms VG.Proof.Weierstrass.X86.tcombJ_ok
#assert_standard_axioms VG.Proof.Weierstrass.X86.savePtr_ok
#assert_standard_axioms VG.X86.Taint.pushSym_sound
#assert_standard_axioms VG.X86.taintSym
