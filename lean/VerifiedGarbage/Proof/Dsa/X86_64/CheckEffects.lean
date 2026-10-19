module
public import VerifiedGarbage.Impl.Dsa.X86_64.Checks
public import VerifiedGarbage.Proof.Dsa.X86_64.LocalCallFrame
public import VerifiedGarbage.Proof.Dsa.X86_64.ReadyCalls

import VerifiedGarbage.Proof.Dsa.X86_64.ReadyChecks
import VerifiedGarbage.Proof.Dsa.X86_64.ModulusMinus
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Dsa.X86_64.Equal
import VerifiedGarbage.Proof.Dsa.X86_64.Range
import VerifiedGarbage.Proof.Dsa.X86_64.Zero
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Dsa.X86_64.IsOne
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp

/-! # Validation effects shared by the DSA key-check schedules -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure CheckEffect (L : ExecutionLayout) (valid : Bool) (s t : State) : Prop where
  ready : Ready L t
  mask : word t.mem L.base Field.mask.offset = VG.Proof.Bignum.mask valid
  frame : Outside L.base 128 (activeBytes - 128) s.mem t.mem
  keep : Keep coreRegs s t

theorem checkFrame_outside {B : Addr} {o wx : Nat} {mem mem' : Mem}
    (hf : Frm B (localCallRanges o wx Field.mask.offset 8) mem mem')
    (ho : pWorkspace ≤ o) (hhi : o + slot wx 8 + tabBytes wx ≤ activeBytes) :
    Outside B 128 (activeBytes - 128) mem mem' := by
  have hslot : 136 ≤ slot wx 8 + tabBytes wx := by unfold slot hdrBytes; omega
  have hlo : 128 ≤ pWorkspace := by decide
  have hma : Field.mask.offset + 8 ≤ activeBytes := by decide
  have hml : 128 ≤ Field.mask.offset := by decide
  intro x hx
  apply hf x
  intro range hr
  simp only [localCallRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> simp only at * <;> omega

theorem readyRange_ok {L : ExecutionLayout} {s : State} (h : Ready L s) (side : ModulusSide)
    (a : Operand) (ha : pointerFits a.pointer) {bytes : List Byte}
    (hb : OperandBytes s L.base activeBytes a bytes)
    (h1 : 1 ≤ bytes.length) (hw : (bytes.length + 7) / 8 ≤ side.words L)
    (aboveOne : Bool) {valid : Bool} (hm : word s.mem L.base Field.mask.offset = mask valid) :
    WP isa (Checks.range side.offset a aboveOne) s
      (CheckEffect L (decide ((if aboveOne then 1 else 0) < Spec.Dsa.decodeBE bytes ∧
        Spec.Dsa.decodeBE bytes < side.value L) && valid) s) := by
  obtain ⟨hw2, hw48, hlo, ho, hhi, _, _⟩ := side.bounds L
  have hfield : 368 ≤ side.offset := by cases side <;> decide
  have hpw : pWorkspace ≤ side.offset := by cases side <;> decide
  refine WP.mono (range_ok h.parent (h.child side) (by decide) hlo hfield hhi ho
    hw2 hw48 hw48 (by decide) a ha hb.length hb.source h1 hw aboveOne hm) ?_
  intro t ⟨hp, hc, hm', hf, hk⟩
  exact ⟨h.afterCheck side hp hc hf hk, hm',
    checkFrame_outside (rangeFrame_local hf (Nat.le_trans hhi (by decide))) hpw hhi, hk⟩

theorem readyIsOne_ok {L : ExecutionLayout} {s : State} (h : Ready L s) (side : ModulusSide)
    (a : Operand) (ha : pointerFits a.pointer) {bytes : List Byte}
    (hb : OperandBytes s L.base activeBytes a bytes)
    (h1 : 1 ≤ bytes.length) (hw : (bytes.length + 7) / 8 ≤ side.words L)
    {valid : Bool} (hm : word s.mem L.base Field.mask.offset = mask valid) :
    WP isa (Checks.isOne side.offset a) s
      (CheckEffect L (decide (Spec.Dsa.decodeBE bytes = 1) && valid) s) := by
  obtain ⟨hw2, hw48, hlo, ho, hhi, _, _⟩ := side.bounds L
  have hfield : 368 ≤ side.offset := by cases side <;> decide
  have hpw : pWorkspace ≤ side.offset := by cases side <;> decide
  refine WP.mono (isOne_ok h.parent (h.child side) (by decide) hlo hfield hhi ho
    hw2 hw48 hw48 (by decide) a ha hb.length hb.source h1 hw hm) ?_
  intro t ⟨hp, hc, hm', hf, hk⟩
  exact ⟨h.afterCheck side hp hc hf hk, hm',
    checkFrame_outside (rangeFrame_local hf (Nat.le_trans hhi (by decide))) hpw hhi, hk⟩

theorem readyZero_ok {L : ExecutionLayout} {s : State} (h : Ready L s)
    (a : Operand) (ha : pointerFits a.pointer) {bytes : List Byte}
    (hb : OperandBytes s L.base activeBytes a bytes) (h1 : 0 < bytes.length) (h64 : bytes.length < 2 ^ 64)
    (nonzero : Bool) {valid : Bool} (hm : word s.mem L.base Field.mask.offset = mask valid) :
    WP isa (Checks.zero a nonzero) s
      (CheckEffect L ((if nonzero then !decide (∀ b ∈ bytes, b = 0) else decide (∀ b ∈ bytes, b = 0)) && valid) s) := by
  refine WP.mono (zero_ok h.parent (by decide) a ha hb.length hb.source h1 h64 nonzero hm) ?_
  intro t ⟨hp, hm', hf, hk⟩
  exact ⟨h.afterMask hp hf hk, hm', hf.mono (by decide) (by decide), hk⟩

theorem readyEqual_ok {L : ExecutionLayout} {s : State} (h : Ready L s)
    (a b : Operand) (ha : pointerFits a.pointer) (hb : pointerFits b.pointer) {as bs : List Byte}
    (has : OperandBytes s L.base activeBytes a as) (hbs : OperandBytes s L.base activeBytes b bs)
    (hlen : as.length = bs.length) (h1 : 0 < as.length) (h64 : as.length < 2 ^ 64)
    (unequal : Bool) {valid : Bool} (hm : word s.mem L.base Field.mask.offset = mask valid) :
    WP isa (Checks.equal a b unequal) s
      (CheckEffect L ((if unequal then !decide (as = bs) else decide (as = bs)) && valid) s) := by
  refine WP.mono (equal_ok h.parent (by decide) a b ha hb has.length has.source hbs.source hlen h1 h64 unequal hm) ?_
  intro t ⟨hp, hm', hf, hk⟩
  exact ⟨h.afterMask hp hf hk, hm', hf.mono (by decide) (by decide), hk⟩

theorem readyMinus_ok {L : ExecutionLayout} {s : State} (h : Ready L s) (side : ModulusSide)
    (amount : Nat) (ha : amount < 2 ^ 31) (ham : amount ≤ side.value L)
    (d : Nat) (hd : activeBytes ≤ d) (hend : d + side.length L ≤ usedBytes) :
    WP isa (Checks.modulusMinus side.offset amount ⟨.local d, side.lengthField⟩) s
      (CallResult L side d (side.value L - amount) s) := by
  obtain ⟨hw2, hw48, hlo, ho, hhi, hk1, hk31⟩ := side.bounds L
  have hdp : pointerFits (.local d) := by
    change d < 2 ^ 31
    have : usedBytes < 2 ^ 31 := by decide
    omega
  refine WP.mono (modulusMinus_ok h.parent (h.child side) (by decide) hlo hhi ho hw2
    (Nat.lt_of_le_of_lt hw48 (by decide)) ha ham ⟨.local d, side.lengthField⟩ hdp
    (h.length side) hk1 hk31 rfl (h.local_write hend) (h.local_out hd hend)) ?_
  intro t ⟨hp, hc, hv, hf, hk⟩
  exact ⟨h.afterCall side hp hc hf hk hd hend, hv, hf, hk⟩

end VG.Proof.Dsa.X86_64
