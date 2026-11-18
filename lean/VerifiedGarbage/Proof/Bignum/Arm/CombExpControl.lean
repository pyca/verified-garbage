module

import VerifiedGarbage.Proof.Bignum.Arm.ExpControl
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Bignum.Arm.CombExpKernel
import VerifiedGarbage.Proof.Rsa.FixedBaseCombMont
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Math

/-! ### `Bignum.Arm.CombExpStep`, which this module and modules that import it used -/

section

/-! A shared square and a shared product implement one comb Horner row. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombExp
open VG VG.Arm
open VG.Proof.Rsa.Mont (numAt Operand)
open VG.Proof.X25519.Arm (Rest)

private theorem operand (q : Nat) (h : q=1 ∨ q=4 ∨ q=6 ∨ q=7) : Operand q := by
  rcases h with rfl | rfl | rfl | rfl <;> simp [Operand,Proof.Rsa.Mont.aAcc,Proof.Rsa.Mont.aTmp]

theorem square_ok {base : BitVec 32} {len w M g E : Nat} {P : State→Prop} {regions : List Region}
    (A : TwoExp.Montgomery base len w P regions) (s : State)
    (h : Power base len w M g E s) (hp : P s) :
    WP isa (A.op 6 6 6) s fun t => Power base len w M g (2*E) t ∧ P t ∧
      TwoExp.HeaderKept base s t ∧ Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (A.op_ok s 6 6 6 h.ready hp (operand 6 (by simp)) (operand 6 (by simp))
    (operand 6 (by simp)) (by decide) (by rw [h.modulus]; exact h.bound)) ?_
  rintro t ⟨ready,modulus,bound,value,keeps,pt,frame,rest⟩
  rw [h.modulus] at modulus bound value
  exact ⟨h.after_y ready modulus keeps bound (mont_sq h.coprime h.value value),pt,
    TwoExp.header_of_keeps h.ready keeps,frame,rest⟩

theorem multiply_ok {base : BitVec 32} {len w M g E F : Nat} {P : State→Prop} {regions : List Region}
    (A : TwoExp.Montgomery base len w P regions) (s : State)
    (h : Power base len w M g E s) (hp : P s)
    (selectedBound : numAt s.mem (State.addr base) w 1 < M)
    (selectedValue : numAt s.mem (State.addr base) w 1 % M = g^F*2^(64*w)%M) :
    WP isa (A.op 6 6 1) s fun t => Power base len w M g (E+F) t ∧ P t ∧
      TwoExp.HeaderKept base s t ∧ Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (A.op_ok s 6 6 1 h.ready hp (operand 6 (by simp)) (operand 6 (by simp))
    (operand 1 (by simp)) (by decide) (by rw [h.modulus]; exact selectedBound)) ?_
  rintro t ⟨ready,modulus,bound,value,keeps,pt,frame,rest⟩
  rw [h.modulus] at modulus bound value
  have left : numAt s.mem (State.addr base) w 6 = Spec.Rsa.powMod g E M*2^(64*w)%M := by
    calc
      _ = numAt s.mem (State.addr base) w 6 % M := (Nat.mod_eq_of_lt h.bound).symm
      _ = _ := by rw [h.value,powMod_eq,Nat.mod_mul_mod]
  have right : numAt s.mem (State.addr base) w 1 = Spec.Rsa.powMod g F M*2^(64*w)%M := by
    calc
      _ = numAt s.mem (State.addr base) w 1 % M := (Nat.mod_eq_of_lt selectedBound).symm
      _ = _ := by rw [selectedValue,powMod_eq,Nat.mod_mul_mod]
  have encoded := VG.Proof.Rsa.FixedBaseComb.mont_product_encoded h.coprime bound left right value
  have result : numAt t.mem (State.addr base) w 6 % M = g^(E+F)*2^(64*w)%M := by
    rw [encoded,Nat.mod_mod,powMod_eq,Nat.mod_mul_mod]
  exact ⟨h.after_y ready modulus keeps bound result,pt,TwoExp.header_of_keeps h.ready keeps,frame,rest⟩

theorem row_ok {base source table : BitVec 32} {len w bytes N M g x i : Nat}
    {P : State→Prop} {regions : List Region}
    (K : Kernel base source table len w bytes N M g x P regions) (s : State)
    (hi : i<Spec.Rsa.FixedBaseComb.rows N)
    (h : Power base len w M g (VG.Proof.Rsa.FixedBaseComb.high N x (i+1)) s)
    (hp : P s) (controls : Controls base source table bytes N s) (counter : Counter base (i+1) s) :
    WP isa (.seq (K.arithmetic.op 6 6 6)
      (.seq VG.Impl.Bignum.Arm.CombExp.choose (K.arithmetic.op 6 6 1))) s fun t =>
      Power base len w M g (VG.Proof.Rsa.FixedBaseComb.high N x i) t ∧ P t ∧
      Controls base source table bytes N t ∧ Counter base (i+1) t ∧
      Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [WP.seq_iff]
  refine WP.mono (square_ok K.arithmetic s h hp) ?_
  rintro u ⟨powerU,pu,headerU,frameU,restU⟩
  have controlsU := controls.after_header headerU
  have counterU : Counter base (i+1) u := (headerU 192 (by decide)).trans counter
  rw [WP.seq_iff]
  refine WP.mono (K.choose_ok u i _ hi powerU pu controlsU counterU) ?_
  rintro v ⟨powerV,pv,controlsV,counterV,boundV,valueV,frameV,restV⟩
  refine WP.mono (multiply_ok K.arithmetic v powerV pv boundV valueV) ?_
  rintro t ⟨powerT,pt,headerT,frameT,restT⟩
  rw [←VG.Proof.Rsa.FixedBaseComb.high_step N x i hi] at powerT
  exact ⟨powerT,pt,controlsV.after_header headerT,(headerT 192 (by decide)).trans counterV,
    frameU.trans (frameV.trans frameT),restU.trans (restV.trans restT)⟩

end VG.Proof.Bignum.Arm.CombExp

end

end

/-! Only the public remaining row count changes after a comb step. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombExp
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem Controls.after_counter {base source table : BitVec 32} {bytes N : Nat} {s t : State}
    (h : Controls base source table bytes N s) {value : BitVec 32}
    (mem : t.mem=s.mem.writeW (off (State.addr base) 192) value) :
    Controls base source table bytes N t := by
  have outside := writeW32_outside s.mem (State.addr base) (d:=192) value (by decide)
  rw [←mem] at outside
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [outside_read32 outside (d:=128) (by decide) (by decide)]; exact h.sourcePtr
  · rw [outside_read32 outside (d:=132) (by decide) (by decide)]; exact h.byteCount
  · rw [outside_read32 outside (d:=136) (by decide) (by decide)]; exact h.bitCount
  · rw [outside_read32 outside (d:=204) (by decide) (by decide)]; exact h.spacing
  · rw [outside_read32 outside (d:=232) (by decide) (by decide)]; exact h.tablePtr

theorem next_ok {base source table : BitVec 32} {len w bytes N M g E i : Nat}
    {P : State→Prop} {regions : List Region}
    (A : TwoExp.Montgomery base len w P regions) (s : State)
    (h : Power base len w M g E s) (hp : P s) (controls : Controls base source table bytes N s)
    (counter : Counter base (i+1) s) (fits : i+1<2^32) :
    WP isa (.block VG.Impl.Bignum.Arm.CombExp.next) s fun t =>
      Power base len w M g E t ∧ P t ∧ Controls base source table bytes N t ∧ Counter base i t ∧
      t.z=decide (i=0) ∧ Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  have size : 256≤8*len := by
    have arrayFits := h.ready.width ▸ h.ready.layout.2.2.1
    simp only [Proof.Rsa.Mont.arrAt,Proof.Rsa.Mont.hdrBytes] at arrayFits
    omega_using [arrayFits]
  refine WP.mono (expDecrement_ok s h.ready.workspace (by omega_using [size]) h.ready.ptr (by omega_using []) fits counter) ?_
  rintro t ⟨mem,flag,rest⟩
  have r : Rest roundClobbers s t := rest.mono (by decide)
  obtain ⟨powerT,frame⟩ := h.after_header (d:=192) (by decide) (by decide) mem rest
    ((rest.gpr .r0 (by decide)).trans h.ready.ptr)
  refine ⟨powerT,A.stable frame r hp,controls.after_counter mem,?_,?_,
    frame.mono (by simpa using A.workspace),r⟩
  · change t.mem.readW (off (State.addr base) 192) 32=BitVec.ofNat 32 i
    rw [mem,Mem.readW_writeW_self32]
    congr 1
  · rw [flag]
    exact decide_eq_decide.mpr (by omega_using [])

theorem round_ok {base source table : BitVec 32} {len w bytes N M g x i : Nat}
    {P : State→Prop} {regions : List Region}
    (K : Kernel base source table len w bytes N M g x P regions) (s : State)
    (hi : i<Spec.Rsa.FixedBaseComb.rows N) (fits : i+1<2^32)
    (h : Power base len w M g (VG.Proof.Rsa.FixedBaseComb.high N x (i+1)) s)
    (hp : P s) (controls : Controls base source table bytes N s) (counter : Counter base (i+1) s) :
    WP isa (VG.Impl.Bignum.Arm.CombExp.round K.arithmetic.op) s fun t =>
      Power base len w M g (VG.Proof.Rsa.FixedBaseComb.high N x i) t ∧ P t ∧
      Controls base source table bytes N t ∧ Counter base i t ∧ t.z=decide (i=0) ∧
      Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Bignum.Arm.CombExp.round,WP.seq_iff]
  refine WP.mono (row_ok K s hi h hp controls counter) ?_
  rintro u ⟨powerU,pu,controlsU,counterU,frameU,restU⟩
  refine WP.mono (next_ok K.arithmetic u powerU pu controlsU counterU fits) ?_
  rintro t ⟨powerT,pt,controlsT,counterT,flag,frameT,restT⟩
  exact ⟨powerT,pt,controlsT,counterT,flag,frameU.trans frameT,restU.trans restT⟩

end VG.Proof.Bignum.Arm.CombExp
