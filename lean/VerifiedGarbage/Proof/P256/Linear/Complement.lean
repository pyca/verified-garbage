import VerifiedGarbage.Impl.P256.Linear
import VerifiedGarbage.Proof.Mont.AArch64.Ops
import VerifiedGarbage.Proof.Ed25519.AArch64.SqrRows
import VerifiedGarbage.Proof.Mont.AArch64.P256Square.Arithmetic

namespace VG.Proof.P256.Linear
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64

private abbrev p := VG.Spec.P256.curve.p

def complement (b : Nat) : List Instr := (Impl.P256.Linear.linear129 0 0 b).take 18

theorem complement_eq129 (o a b : Nat) :
    (Impl.P256.Linear.linear129 o a b).take 18=complement b := rfl

theorem complement_eq38 (o a b : Nat) :
    (Impl.P256.Linear.linear38 o a b).take 18=complement b := rfl

private def compWords (a b c d : Word) : Word × Word × Word × Word :=
  let c0 := carryOut (-1) (~~~a) true
  let c1 := carryOut 0xffffffff (~~~b) c0
  let c2 := carryOut 0 (~~~c) c1
  (addCarry (-1) (~~~a) true,addCarry 0xffffffff (~~~b) c0,
    addCarry 0 (~~~c) c1,addCarry 0xffffffff00000001 (~~~d) c2)

private def compValue (a b c d : Word) : Nat :=
  let w := compWords a b c d
  val4 w.1 w.2.1 w.2.2.1 w.2.2.2

private theorem comp_value (a b c d : Word) (h : val4 a b c d<p) :
    compValue a b c d=p-val4 a b c d := by
  have he := sub4_value (-1) 0xffffffff 0 0xffffffff00000001 a b c d true
  have hl := val4_lt (compWords a b c d).1 (compWords a b c d).2.1
    (compWords a b c d).2.2.1 (compWords a b c d).2.2.2
  have hc : val4 (-1) 0xffffffff 0 0xffffffff00000001=p := by decide
  simp only [Bool.toNat_true,Nat.sub_self,Nat.add_zero,hc] at he
  change compValue a b c d+val4 a b c d = _ at he
  change compValue a b c d<2^256 at hl
  have hb := Bool.toNat_le (carryOut 0xffffffff00000001 (~~~d)
    (carryOut 0 (~~~c) (carryOut 0xffffffff (~~~b) (carryOut (-1) (~~~a) true))))
  omega

private theorem complement_core {s : State} {base : Addr} {size b : Nat}
    (hs : Scr s base size) (hb : b+32≤size) (hb8 : b%8=0)
    :
    WP isa (.block (complement b)) s fun t =>
      (t.gpr .x9,t.gpr .x10,t.gpr .x11,t.gpr .x12)=
        compWords (VG.Proof.Mont.word s.mem base b) (VG.Proof.Mont.word s.mem base (b+8))
          (VG.Proof.Mont.word s.mem base (b+16)) (VG.Proof.Mont.word s.mem base (b+24)) ∧
      t.gpr .x17=0 ∧ Keeps [.x2,.x9,.x10,.x11,.x12,.x17] s t := by
  have h0 := hs.enc8 (d:=b) (by omega) hb8
  have h8 := hs.enc8 (d:=b+8) (by omega) (by omega)
  have h16 := hs.enc8 (d:=b+16) (by omega) (by omega)
  have h24 := hs.enc8 (d:=b+24) (by omega) (by omega)
  have l0 := hs.ld (d:=b) (by omega)
  have l8 := hs.ld (d:=b+8) (by omega)
  have l16 := hs.ld (d:=b+16) (by omega)
  have l24 := hs.ld (d:=b+24) (by omega)
  rw [hs.x0] at l0 l8 l16 l24
  apply WP.of_runBlock
  simp only [complement,Impl.P256.Linear.linear129,List.take_succ_cons,List.take_zero,
    runBlock_cons,runStep_some,runBlock_nil,exec,read_x,Size.bits,Size.bytes,
    RegUpd.gpr_write,RegUpd.c_write,RegUpd.mem_write,RegUpd.rd_write,RegUpd.wr_write,
    RegUpd.mem_addWithCarry,RegUpd.rd_addWithCarry,RegUpd.wr_addWithCarry,RegUpd.gpr_addWithCarry,RegUpd.c_addWithCarry,
    BitVec.setWidth_eq,Nat.add_zero,show 16*0<64 by decide,show 16*1<64 by decide,
    show 16*2<64 by decide,show 16*3<64 by decide,
    and_self,ite_true,ite_false,reduceCtorEq,addr,h0,h8,h16,h24,Option.bind_some,
    State.load,hs.x0,l0,l8,l16,l24,Option.map_some,Option.some.injEq,exists_eq_left']
  refine ⟨?_,rfl,?_,rfl,rfl,rfl,rfl⟩
  · rfl
  · reg_keeps

theorem complement_ok {s : State} {base : Addr} {size b : Nat}
    (hs : Scr s base size) (hb : b+32≤size) (hb8 : b%8=0)
    (hB : wordsVal s.mem base b 4<p) :
    WP isa (.block (complement b)) s fun t =>
      regsVal t [.x9,.x10,.x11,.x12]=p-wordsVal s.mem base b 4 ∧
      t.gpr .x17=0 ∧ Keeps [.x2,.x9,.x10,.x11,.x12,.x17] s t := by
  refine WP.mono (complement_core hs hb hb8) fun t ⟨he,hz,hk⟩ => ⟨?_,hz,hk⟩
  have hv : val4 (VG.Proof.Mont.word s.mem base b) (VG.Proof.Mont.word s.mem base (b+8))
      (VG.Proof.Mont.word s.mem base (b+16)) (VG.Proof.Mont.word s.mem base (b+24)) = wordsVal s.mem base b 4 := by
    simp only [val4,wordsVal,Nat.mul_zero,Nat.add_zero,Nat.mul_add,←Nat.mul_assoc,Nat.add_assoc]
  have hc := comp_value (VG.Proof.Mont.word s.mem base b) (VG.Proof.Mont.word s.mem base (b+8))
    (VG.Proof.Mont.word s.mem base (b+16)) (VG.Proof.Mont.word s.mem base (b+24)) (by rw [hv]; exact hB)
  rw [hv] at hc
  have ht : regsVal t [.x9,.x10,.x11,.x12]=val4 (t.gpr .x9) (t.gpr .x10) (t.gpr .x11) (t.gpr .x12) := by
    simp only [regsVal,val4,Nat.mul_zero,Nat.add_zero,Nat.mul_add,←Nat.mul_assoc,Nat.add_assoc]
  rw [ht]
  change (let w := (t.gpr .x9,t.gpr .x10,t.gpr .x11,t.gpr .x12); val4 w.1 w.2.1 w.2.2.1 w.2.2.2)=_
  rw [he]
  exact hc

end VG.Proof.P256.Linear
