module
public import VerifiedGarbage.Proof.Dsa.X86_64.ReadyCalls

import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleOperands
import VerifiedGarbage.Proof.Dsa.X86_64.CoreJoint
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import Mathlib.Tactic.Set

/-! # Joint exponentiation preserving the DSA execution context -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem readyJoint_ok (M : Mont) (Sq : MontS) {L : ExecutionLayout} {s : State} (h : Ready L s)
    (hm : 1 < L.modulus) (hodd : L.modulus % 2 = 1)
    (a b : Operand) {ba bb : List Byte} (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (has : OperandBytes s L.base activeBytes a ba) (hbs : OperandBytes s L.base activeBytes b bb)
    (ha1 : 1 ≤ ba.length) (haw : (ba.length + 7) / 8 ≤ ModulusSide.p.words L)
    (hb1 : 1 ≤ bb.length) (hbw : (bb.length + 7) / 8 ≤ ModulusSide.p.words L)
    {eb fb : List Byte}
    (he : OperandBytes s L.base activeBytes (Core.scalar u) eb)
    (hf : OperandBytes s L.base activeBytes (Core.scalar v) fb)
    (hel : eb.length = L.qLen) (hfl : fb.length = L.qLen)
    (d : Nat) (hd : activeBytes ≤ d) (hend : d + ModulusSide.p.length L ≤ usedBytes) :
    WP isa (Core.joint Sq.mm M.mm ModulusSide.p.offset a b ⟨.local d, ModulusSide.p.lengthField⟩) s
      (CallResult L .p d (Spec.Dsa.powMod (Spec.Dsa.decodeBE ba) (Spec.Dsa.decodeBE eb) L.modulus *
        Spec.Dsa.powMod (Spec.Dsa.decodeBE bb) (Spec.Dsa.decodeBE fb) L.modulus % L.modulus) s) := by
  obtain ⟨hw2, hw48, hlo, ho, hhi, hk1, hk31⟩ := ModulusSide.p.bounds L
  have hdp : pointerFits (.local d) := by
    change d < 2 ^ 31
    have : usedBytes < 2 ^ 31 := by decide
    omega
  refine WP.mono (coreJoint_ok M Sq h.parent (h.child .p) (by decide) hlo hhi ho (by decide)
    hw2 hw48 hw48 (by decide) hm hodd a b ⟨.local d, ModulusSide.p.lengthField⟩ ha hb hdp
    has hbs ha1 haw hb1 hbw he.source hf.source (hel.trans hfl.symm).symm
    (by rw [hel]; exact L.widths.1) (by rw [hel]; have := L.widths; omega)
    (by simpa only [hel, ModulusSide.length, ModulusSide.lengthField] using h.length .q) (h.length .p) hk1 hk31 rfl
    (h.local_write hend) (h.local_out hd hend)) ?_
  intro t ⟨hp, hc, hv, hf, hk⟩
  exact ⟨h.afterCall .p hp hc hf hk hd hend, hv, hf, hk⟩


end VG.Proof.Dsa.X86_64
