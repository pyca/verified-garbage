module

public import VerifiedGarbage.Proof.Bignum.Arm.CombExpKernel
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomeryCT
public import VerifiedGarbage.Proof.Framework.RelCT

/-! Timing relates independent secret exponents under one public comb schedule. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombExp
open VG VG.Arm
open VG.Proof.Rsa.Mont (Operand numAt)

structure RowInput (base source table : BitVec 32) (len w bytes N M g E i : Nat)
    (P : State→Prop) (s : State) : Prop where
  power : Power base len w M g E s
  persistent : P s
  controls : Controls base source table bytes N s
  counter : Counter base (i+1) s

structure SelectedInput (base source table : BitVec 32) (len w bytes N M g E i : Nat)
    (P : State→Prop) (s : State) : Prop extends RowInput base source table len w bytes N M g E i P s where
  selectedBound : numAt s.mem (State.addr base) w 1<M

/-- The predicates may describe different secret buffers; code and public controls agree. -/
structure Timing {base source table : BitVec 32} {len w bytes N M g x1 x2 : Nat}
    {P1 P2 : State→Prop} {regions1 regions2 : List Region}
    (K1 : Kernel base source table len w bytes N M g x1 P1 regions1)
    (K2 : Kernel base source table len w bytes N M g x2 P2 regions2) : Prop where
  same : K1.arithmetic.op=K2.arithmetic.op
  op_ct : ∀ o a b, Operand o → Operand a → Operand b →
    RelCT isa (fun s t => TwoExp.OpInput base len w P1 b s ∧
      TwoExp.OpInput base len w P2 b t ∧ s.sp=t.sp) (K1.arithmetic.op o a b) (fun _ _ => True)
  choose_ct : ∀ i E1 E2, i<Spec.Rsa.FixedBaseComb.rows N →
    RelCT isa (fun s t => RowInput base source table len w bytes N M g E1 i P1 s ∧
      RowInput base source table len w bytes N M g E2 i P2 t ∧ s.sp=t.sp)
      VG.Impl.Bignum.Arm.CombExp.choose (fun _ _ => True)

end VG.Proof.Bignum.Arm.CombExp
