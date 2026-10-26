module

public import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Recode
import VerifiedGarbage.Proof.X448.AArch64.BitWrite
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X448.AArch64.Mem

/-! Store one signed digit and advance its bounded public counter. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.Ed448.AArch64.Sparse
open VG.Impl.X448.AArch64 (BITS)
open VG.Proof.X448.AArch64 (Scr Keeps off write1_eq)

theorem encode_digit {d : Int} (hd : -127≤d ∧ d≤127) :
    (BitVec.ofInt 64 d).setWidth 8 = BitVec.ofInt 8 d := by
  have hc : ∀ (n : Nat), n<255 → (BitVec.ofInt 64 ((n : Int)-127)).setWidth 8 =
      BitVec.ofInt 8 ((n : Int)-127) := by decide +kernel
  obtain ⟨n,hn,he⟩ : ∃ (n : Nat), n<255 ∧ d=(n : Int)-127 := by
    refine ⟨(d+127).toNat,?_,?_⟩ <;> omega
  rw [he]
  exact hc n hn

theorem writeDigit_ok {s : State} {base : Addr} (hs : Scr s base) {i : Nat}
    (hi : i<464) (hp : s.gpr .x2=off base i) (hc : s.gpr .x19=BitVec.ofNat 64 i) :
    WP isa (.block writeDigit) s fun u =>
      u.gpr .x19=BitVec.ofNat 64 (i+1) ∧ Keeps [.x19] s u ∧
      u.mem=s.mem.writeW (off base (BITS+i)) ((s.gpr .x7).setWidth 8) := by
  have enc : BITS%1=0 ∧ BITS<4096 := ⟨Nat.mod_one _,by decide⟩
  have ea : off base i + BitVec.ofNat 64 BITS=off base (BITS+i) := by
    rw [off,off,Offset.add_add]
    congr 2
    omega
  have hw := hs.write (d:=BITS+i) (n:=1) (by simp only [BITS];omega)
  apply WP.of_runBlock
  simp only [writeDigit,runBlock_cons,runStep_some,runBlock_nil,exec,addr,enc,and_self,
    hp,ea,State.store,State.read,Size.bits,BitVec.setWidth_setWidth_of_le _ (by decide : 8≤32),
    hw,ite_true,Option.bind_some,write1_eq,Nat.reduceLT,RegUpd.gpr_write,
    BitVec.setWidth_eq,hc,Option.some.injEq,exists_eq_left']
  refine ⟨?_,⟨fun r hr => ?_,rfl,rfl⟩,rfl⟩
  · exact (BitVec.ofNat_add i 1).symm
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_write,hr,ite_false]

private theorem counter_fact : ∀ i<456,
    (BitVec.ofNat 64 (i+1)-BitVec.ofNat 64 456 == 0)=decide (i+1=456) := by decide +kernel

theorem counter_ok {s : State} {i : Nat} (hi:i<456) (hc:s.gpr .x19=BitVec.ofNat 64 (i+1)) :
    WP isa (.block [.subImm .x .x9 .x19 456]) s fun u =>
      (u.gpr .x9==0)=decide (i+1=456) ∧ Keeps [.x9] s u ∧ u.mem=s.mem := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,State.read,Size.bits,
    Nat.reduceLT,ite_true,RegUpd.gpr_write,BitVec.setWidth_eq,hc,
    Option.some.injEq,exists_eq_left']
  exact ⟨counter_fact i hi,⟨fun r hr => by
    simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_write,hr,ite_false],rfl,rfl⟩,rfl⟩

end VG.Proof.Ed448.AArch64.Sparse
