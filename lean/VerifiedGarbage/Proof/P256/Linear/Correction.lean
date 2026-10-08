import VerifiedGarbage.Impl.P256.Linear
import VerifiedGarbage.Proof.P256.Linear.CorrectionWords
import VerifiedGarbage.Proof.Ed25519.AArch64.SqrRows

namespace VG.Proof.P256.Linear
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64
open VG.Proof.P256.VerifySparse (four)

def correction : List Instr := ((Impl.P256.Linear.linear129 0 0 0).drop 52).take 20

theorem correction_eq129 (o a b : Nat) :
    ((Impl.P256.Linear.linear129 o a b).drop 52).take 20=correction := rfl

theorem correction_eq38 (o a b : Nat) :
    ((Impl.P256.Linear.linear38 o a b).drop 42).take 20=correction := rfl

private theorem correction_core (s : State) (hz : s.gpr .x17=0) :
    WP isa (.block correction) s fun t =>
      (t.gpr .x3,t.gpr .x4,t.gpr .x5,t.gpr .x6)=
        correctionWords (s.gpr .x3) (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) ∧
      Keeps [.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x16] s t := by
  apply WP.of_runBlock
  simp only [correction,Impl.P256.Linear.linear129,List.drop_succ_cons,List.drop_zero,
    List.take_succ_cons,List.take_zero,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,Size.bits,
    RegUpd.gpr_write,RegUpd.c_write,RegUpd.gpr_addWithCarry,RegUpd.c_addWithCarry,
    BitVec.setWidth_eq,show 16*0<64 by decide,show 32<64 by decide,
    ite_true,ite_false,reduceCtorEq,hz,Option.some.injEq,exists_eq_left']
  refine ⟨?_,?_,rfl,rfl,rfl,rfl⟩
  · rfl
  · reg_keeps

theorem correction_ok (s : State) (hz : s.gpr .x17=0)
    (hn : regsVal s [.x3,.x4,.x5,.x6,.x7]<21*p) :
    WP isa (.block correction) s fun t =>
      regsVal t [.x3,.x4,.x5,.x6]=regsVal s [.x3,.x4,.x5,.x6,.x7]%p ∧
      Keeps [.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x16] s t := by
  have hs : regsVal s [.x3,.x4,.x5,.x6,.x7]=
      five (s.gpr .x3) (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) := by
    simp only [regsVal,five,four,Nat.mul_zero,Nat.add_zero,Nat.mul_add,←Nat.mul_assoc,Nat.add_assoc]
  refine WP.mono (correction_core s hz) fun t ⟨he,hk⟩ => ⟨?_,hk⟩
  have ht : regsVal t [.x3,.x4,.x5,.x6]=four (t.gpr .x3) (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) := by
    simp only [regsVal,four,Nat.mul_zero,Nat.add_zero,Nat.mul_add,←Nat.mul_assoc]
  rw [ht,hs]
  change (let w:=(t.gpr .x3,t.gpr .x4,t.gpr .x5,t.gpr .x6);four w.1 w.2.1 w.2.2.1 w.2.2.2)=_
  rw [he]
  exact correctionWords_value _ _ _ _ _ (by rw [←hs]; exact hn)

end VG.Proof.P256.Linear
