module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.ReadEnv
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Digit
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Stable
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! One proved comb row doubles the running exponent and adds one five-tooth entry. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

structure Running (p : Parameters) (bs : List Byte) (E i : Nat) (s : State) : Prop where
 power : Power p E s
 controls : Controls p.B p.src p.ctx bs.length p.N s
 counter : Counter p.B i s
 tablePointer : TablePointer p.B p.table s
 reads : ReadEnv p bs s

theorem Running.after_arrays {p : Parameters} {bs : List Byte} {E E' i : Nat} {s t : State} {js : List Nat}
 (h : Running p bs E i s) (power : Power p E' t) (frame : Arrays p.B p.w js s.mem t.mem)
 (rest : Keep mmRegs s t) (within : ∀ j∈js,j<8) : Running p bs E' i t :=
 ⟨power,h.controls.after_arrays frame,(arrays_header frame (by decide)).trans h.counter,
  (arrays_header frame (by decide)).trans h.tablePointer,h.reads.after_arrays frame rest within⟩

theorem running_step (M : Mont) {p : Parameters} {bs : List Byte} {E i : Nat} {s : State}
 (h : Running p bs E (i+1) s) (size : bs.length<2^31) (widthBound : p.N≤8*bs.length)
 (positions : i+5*Spec.Rsa.FixedBaseComb.rows p.N<2^63) (bound : Spec.Rsa.os2ip bs<2^p.N) :
 WP isa (Comb.step M.mm) s fun t =>
 Running p bs (2*E+Spec.Rsa.FixedBaseComb.exponent p.N (VG.Proof.Rsa.FixedBaseComb.digit p.N (Spec.Rsa.os2ip bs) i)) i t ∧
 StableHeader p.B s.mem t.mem ∧ t.gpr .x3=BitVec.ofNat 64 i ∧ Keep mmRegs s t := by
 unfold Comb.step
 rw [WP.seq_iff]
 refine WP.mono (power_square M h.power) ?_
 rintro a ⟨powerA,frameA,keepA⟩
 have hA := h.after_arrays powerA frameA keepA (by simp)
 rw [WP.seq_iff]
 refine WP.mono (digit_ok powerA.good p.room hA.controls hA.counter hA.reads.source
  size widthBound positions bound) ?_
 rintro b ⟨goodB,controlsB,counterB,digitB,frameB,keepB⟩
 have powerB := powerA.after_header goodB frameB (by decide : sD<32)
 have readsB := hA.reads.after_header frameB keepB (by decide : sD<32)
 have tableB : TablePointer p.B p.table b :=
  (header_other frameB (by decide) (by decide) (by decide)).trans hA.tablePointer
 rw [WP.seq_iff]
 let v := VG.Proof.Rsa.FixedBaseComb.digit p.N (Spec.Rsa.os2ip bs) i
 have hv : v<32 := VG.Proof.Rsa.FixedBaseComb.digit_lt _ _ _
 refine WP.mono (select_ok goodB p.room (by have := p.positive;omega) p.width hv tableB digitB
  readsB.tableRead readsB.tableOutside) ?_
 rintro c ⟨goodC,selectedC,frameC,keepC⟩
 have powerC := powerB.after_arrays goodC frameC (by decide) (by decide) (by decide) (by decide)
 have selected : wv c.mem p.B (slot p.w 5) p.w=
  Spec.Rsa.powMod p.G (Spec.Rsa.FixedBaseComb.exponent p.N v) p.P*2^(64*p.w)%p.P :=
  selectedC.trans (readsB.table v hv)
 have runB : Running p bs (2*E) (i+1) b := ⟨powerB,controlsB,counterB,tableB,readsB⟩
 have runC := runB.after_arrays powerC frameC keepC (by simp)
 rw [WP.seq_iff]
 refine WP.mono (power_product M powerC selected) ?_
 rintro d ⟨powerD,frameD,keepD⟩
 have runD := runC.after_arrays powerD frameD keepD (by simp)
 refine WP.mono (decrement_control_ok powerD.good p.room (by decide : 16≤sI) (by decide : sI<32)
  (by omega : 0<i+1) runD.counter) ?_
 rintro t ⟨goodT,counterT,indexT,frameT,keepT⟩
 have powerT := powerD.after_header goodT frameT (by decide : sI<32)
 have tableT : TablePointer p.B p.table t :=
  (header_other frameT (by decide) (by decide) (by decide)).trans runD.tablePointer
 refine ⟨⟨powerT,runD.controls.after_counter frameT,?_,tableT,
  runD.reads.after_header frameT keepT (by decide : sI<32)⟩,?_,?_,
  ((((keepA.trans keepB).trans keepC).trans keepD).trans keepT).mono (by decide)⟩
 · simpa only [Counter,Nat.add_sub_cancel] using counterT
 · exact ((((StableHeader.of_arrays frameA).trans (StableHeader.of_control frameB (Or.inr (Or.inl rfl)))).trans
    (StableHeader.of_arrays frameC)).trans (StableHeader.of_arrays frameD)).trans
    (StableHeader.of_control frameT (Or.inl rfl))
 · simpa only [Nat.add_sub_cancel] using indexT

end VG.Proof.Ffdh.AArch64.Cached
