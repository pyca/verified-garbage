module

public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
public import VerifiedGarbage.Proof.Dsa.X86_64.Modulus
import VerifiedGarbage.Proof.Dsa.X86_64.CoreCalls
import VerifiedGarbage.Proof.Dsa.X86_64.CoreReduce
import VerifiedGarbage.Proof.Dsa.X86_64.CoreAdd
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp

/-! # Arithmetic calls preserving the complete DSA execution context -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure CallResult (L : ExecutionLayout) (side : ModulusSide) (d value : Nat) (s t : State) : Prop where
  ready : Ready L t
  bytes : Spec.Rsa.bytesAt t.mem (off L.base d) (side.length L) = Spec.Dsa.encodeBE (side.length L) value
  frame : CallFrame L.base side.offset (side.words L) (off L.base d) (side.length L) s.mem t.mem
  keep : Keep coreRegs s t

theorem readyPow_ok (M : Mont) (Sq : MontS) {L : ExecutionLayout} {s : State} (h : Ready L s)
    (side : ModulusSide) (hm : 1 < side.value L) (hodd : side.value L % 2 = 1)
    (a b : Operand) {ba bb : List Byte} (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (has : OperandBytes s L.base activeBytes a ba) (hbs : OperandBytes s L.base activeBytes b bb)
    (ha1 : 1 ≤ ba.length) (haw : (ba.length + 7) / 8 ≤ side.words L)
    (hb1 : 1 ≤ bb.length) (hb2 : bb.length ≤ 1024)
    (d : Nat) (hd : activeBytes ≤ d) (hend : d + side.length L ≤ usedBytes) :
    WP isa (Core.pow Sq.mm M.mm side.offset a b ⟨.local d, side.lengthField⟩) s
      (CallResult L side d (Spec.Dsa.powMod (Spec.Dsa.decodeBE ba) (Spec.Dsa.decodeBE bb) (side.value L)) s) := by
  obtain ⟨hw2, hw48, hlo, ho, hhi, hk1, hk31⟩ := side.bounds L
  have hdp : pointerFits (.local d) := by
    change d < 2 ^ 31
    have : usedBytes < 2 ^ 31 := by decide
    omega
  refine WP.mono (corePow_ok M Sq h.parent (h.child side) (by decide) hlo hhi ho
    hw2 hw48 hw48 (by decide) hm hodd a b ⟨.local d, side.lengthField⟩ ha hb hdp
    has hbs ha1 haw hb1 hb2 (h.length side) hk1 hk31 rfl
    (h.local_write hend) (h.local_out hd hend)) ?_
  intro t ⟨hp, hc, hv, hf, hk⟩
  exact ⟨h.afterCall side hp hc hf hk hd hend, hv, hf, hk⟩

theorem readyProduct_ok (M : Mont) {L : ExecutionLayout} {s : State} (h : Ready L s)
    (side : ModulusSide) (hm : 1 < side.value L) (hodd : side.value L % 2 = 1)
    (a b : Operand) {ba bb : List Byte} (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (has : OperandBytes s L.base activeBytes a ba) (hbs : OperandBytes s L.base activeBytes b bb)
    (ha1 : 1 ≤ ba.length) (haw : (ba.length + 7) / 8 ≤ side.words L)
    (hb1 : 1 ≤ bb.length) (hbw : (bb.length + 7) / 8 ≤ side.words L)
    (d : Nat) (hd : activeBytes ≤ d) (hend : d + side.length L ≤ usedBytes) :
    WP isa (Core.product M.mm side.offset a b ⟨.local d, side.lengthField⟩) s
      (CallResult L side d (Spec.Dsa.decodeBE ba * Spec.Dsa.decodeBE bb % side.value L) s) := by
  obtain ⟨hw2, hw48, hlo, ho, hhi, hk1, hk31⟩ := side.bounds L
  have hdp : pointerFits (.local d) := by
    change d < 2 ^ 31
    have : usedBytes < 2 ^ 31 := by decide
    omega
  refine WP.mono (coreProduct_ok M h.parent (h.child side) (by decide) hlo hhi ho
    hw2 hw48 hw48 (by decide) hm hodd a b ⟨.local d, side.lengthField⟩ ha hb hdp
    has hbs ha1 haw hb1 hbw (h.length side) hk1 hk31 rfl
    (h.local_write hend) (h.local_out hd hend)) ?_
  intro t ⟨hp, hc, hv, hf, hk⟩
  exact ⟨h.afterCall side hp hc hf hk hd hend, hv, hf, hk⟩

theorem readyReduce_ok (M : Mont) {L : ExecutionLayout} {s : State} (h : Ready L s)
    (hm : 255 < L.subgroup) (hodd : L.subgroup % 2 = 1)
    (a : Operand) {ba : List Byte} (ha : pointerFits a.pointer)
    (has : OperandBytes s L.base activeBytes a ba) (hal : ba.length < 2 ^ 64)
    (d : Nat) (hd : activeBytes ≤ d) (hend : d + L.qLen ≤ usedBytes) :
    WP isa (Core.reduce M.mm a (Core.scalar d)) s
      (CallResult L .q d (Spec.Dsa.decodeBE ba % L.subgroup) s) := by
  obtain ⟨hw2, hw48, hlo, _, hhi, hk1, hk31⟩ := ModulusSide.q.bounds L
  have hdp : pointerFits (.local d) := by
    change d < 2 ^ 31
    have : usedBytes < 2 ^ 31 := by decide
    omega
  refine WP.mono (coreReduce_ok M h.parent h.qChild (by decide) hlo hhi hw2 hw48 hm hodd
    a (Core.scalar d) ha hdp has hal (h.length .q) hk1 hk31 rfl
    (h.local_write hend) (h.local_out hd hend)) ?_
  intro t ⟨hp, hc, hv, hf, hk⟩
  exact ⟨h.afterQ hp hc hf hk hd hend, hv, hf, hk⟩

theorem readyAdd_ok {L : ExecutionLayout} {s : State} (h : Ready L s)
    (a b : Operand) {ba bb : List Byte} (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (has : OperandBytes s L.base activeBytes a ba) (hbs : OperandBytes s L.base activeBytes b bb)
    (ha1 : 1 ≤ ba.length) (haw : (ba.length + 7) / 8 ≤ L.qWords)
    (hb1 : 1 ≤ bb.length) (hbw : (bb.length + 7) / 8 ≤ L.qWords)
    (har : Spec.Dsa.decodeBE ba < L.subgroup) (hbr : Spec.Dsa.decodeBE bb < L.subgroup)
    (d : Nat) (hd : activeBytes ≤ d) (hend : d + L.qLen ≤ usedBytes) :
    WP isa (Core.add a b (Core.scalar d)) s
      (CallResult L .q d ((Spec.Dsa.decodeBE ba + Spec.Dsa.decodeBE bb) % L.subgroup) s) := by
  obtain ⟨hw2, hw48, hlo, _, hhi, hk1, hk31⟩ := ModulusSide.q.bounds L
  have hdp : pointerFits (.local d) := by
    change d < 2 ^ 31
    have : usedBytes < 2 ^ 31 := by decide
    omega
  refine WP.mono (coreAdd_ok h.parent h.qChild (by decide) hlo hhi hw2 hw48 hw48 (by decide)
    a b (Core.scalar d) ha hb hdp has hbs ha1 haw hb1 hbw har hbr
    (h.length .q) hk1 hk31 rfl (h.local_write hend) (h.local_out hd hend)) ?_
  intro t ⟨hp, hc, hv, hf, hk⟩
  exact ⟨h.afterQ hp hc hf hk hd hend, hv, hf, hk⟩

end VG.Proof.Dsa.X86_64
