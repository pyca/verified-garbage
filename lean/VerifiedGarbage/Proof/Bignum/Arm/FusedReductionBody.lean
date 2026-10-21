module

import VerifiedGarbage.Proof.Bignum.Arm.FusedReductionFirst
import VerifiedGarbage.Proof.Bignum.Arm.FusedReductionTop
import VerifiedGarbage.Proof.Bignum.Arm.FusedReductionMath
import VerifiedGarbage.Proof.Bignum.Arm.DownRow
import VerifiedGarbage.Proof.Bignum.Arm.RowCarryMemory
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Bignum.Arm.FusedReduction
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState

/-! The fused cancellation row computes the quotient without moving its array. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.FusedReduction
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem code_ok (s : State) {base : BitVec 32} {size acc mod n : Nat}
    (ws : Workspace s base size) (positive : 1<n) (accFit : acc+4*(n+2)≤size)
    (modFit : mod+4*n≤size)
    (separate : acc+4*(n+2)≤mod ∨ mod+4*n≤acc)
    (ptr : s.gpr .r0=base+BitVec.ofNat 32 acc)
    (source : s.gpr .r12=base+BitVec.ofNat 32 mod)
    (count : s.gpr .lr=BitVec.ofNat 32 n) (carry : s.gpr .r11=0)
    (cancel : ((s.gpr .r1).toNat*w32 s.mem (State.addr base) mod+
      w32 s.mem (State.addr base) acc)%2^32=0)
    (capacity : val32 s.mem (State.addr base) acc (n+2)+
      (s.gpr .r1).toNat*val32 s.mem (State.addr base) mod n<2^(32*(n+2))) :
    WP isa VG.Impl.Bignum.Arm.FusedReduction.code s fun t =>
      2^32*val32 t.mem (State.addr base) acc (n+1)=
        val32 s.mem (State.addr base) acc (n+2)+
          (s.gpr .r1).toNat*val32 s.mem (State.addr base) mod n ∧
      t.gpr .r0=base+BitVec.ofNat 32 (acc+4*(n+1)) ∧
      Outside (State.addr base) acc (4*(n+1)) s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Bignum.Arm.FusedReduction.code,WP.seq_iff]
  refine WP.mono (first_ok s ws (by omega) (by omega) (by omega) ptr source count carry cancel) ?_
  rintro u ⟨ptrU,sourceU,countU,scalarU,first,memU,restU⟩
  have ctx : DownRow.Ctx u base size acc (mod+4) (n-1) :=
    ⟨ws.nowrap,by omega,by omega,by rcases separate with h|h <;> omega,
      by rw [restU.wr];exact ws.writable⟩
  rw [WP.seq_iff]
  refine WP.mono (DownRow.code_ok u ctx (by omega) ptrU sourceU countU) ?_
  intro v row
  let P := 2^(32*(n-1))
  let H := val32 s.mem (State.addr base) (acc+4*n) 2
  let L := val32 s.mem (State.addr base) (acc+4) (n-1)
  let Q := (s.gpr .r1).toNat
  have rowValue : val32 v.mem (State.addr base) acc (n-1)+P*(v.gpr .r11).toNat=
      L+Q*val32 s.mem (State.addr base) (mod+4) (n-1)+(u.gpr .r11).toNat := by
    simpa only [memU,scalarU] using row.value
  have accSplit : val32 s.mem (State.addr base) acc (n+2)=
      w32 s.mem (State.addr base) acc+2^32*(L+P*H) := by
    rw [show n+2=(n+1)+1 by omega,val32]
    have split := val32_append s.mem (State.addr base) (acc+4) (n-1) 2
    simpa only [show n-1+2=n+1 by omega,show acc+4+4*(n-1)=acc+4*n by omega] using
      congrArg (fun x => w32 s.mem (State.addr base) acc+2^32*x) split
  have modSplit : val32 s.mem (State.addr base) mod n=
      w32 s.mem (State.addr base) mod+2^32*val32 s.mem (State.addr base) (mod+4) (n-1) := by
    calc
      _ = val32 s.mem (State.addr base) mod ((n-1)+1) := by congr 1;omega
      _ = _ := rfl
  have total : 2^32*(val32 v.mem (State.addr base) acc (n-1)+P*(H+(v.gpr .r11).toNat))=
      val32 s.mem (State.addr base) acc (n+2)+Q*val32 s.mem (State.addr base) mod n :=
    quotient_value accSplit modSplit first rowValue rfl
  have power : 2^32*(P*2^64)=2^(32*(n+2)) := by
    dsimp only [P]
    rw [←Nat.pow_add,←Nat.pow_add]
    congr 1
    omega
  have topBound : H+(v.gpr .r11).toNat<2^64 := by
    have cap := capacity
    change _+Q*_< _ at cap
    rw [←total,←power] at cap
    have small : 2^32*(P*(H+(v.gpr .r11).toNat))<2^32*(P*2^64) :=
      Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.le_add_left _ _)) cap
    exact Nat.lt_of_mul_lt_mul_left (Nat.lt_of_mul_lt_mul_left small)
  have outside : Outside (State.addr base) acc (4*(n-1)) s.mem v.mem := by
    simpa only [memU] using row.outside
  have oldTop (j : Nat) (hj : j<2) :
      w32 v.mem (State.addr base) (acc+4*n+4*j)=w32 s.mem (State.addr base) (acc+4*n+4*j) :=
    outside.w32 (by omega) (by have := ws.nowrap;omega)
  have fitTop : acc+4*(n-1)+12≤size := by omega
  have native : Rest roundClobbers u v := (row.rest.mono (by simp [DownRow.loopClobbers,roundClobbers]))
  have rest : Rest roundClobbers s v := restU.trans native
  have workspaceV := ws.congr rest.wr
  refine WP.mono (top_ok v workspaceV fitTop row.outPtr ?_) ?_
  · have lo := oldTop 0 (by decide)
    have hi := oldTop 1 (by decide)
    simp only [Nat.mul_zero,Nat.add_zero,Nat.mul_one] at lo hi
    rw [show acc+4*(n-1)+4=acc+4*n by omega,
      show acc+4*(n-1)+8=acc+4*n+4 by omega,lo,hi]
    simpa only [H,val32,Nat.mul_zero,Nat.add_zero,Nat.add_assoc] using topBound
  · rintro t ⟨topValue,memT,ptrT,restT⟩
    have nowrap : (State.addr base).toNat+size≤2^32 := by
      simpa only [VG.Proof.X25519.Arm.addr_toNat] using ws.nowrap
    obtain ⟨outTop,whole⟩ := rowCarry_memory (base:=State.addr base) (n:=n-1)
      nowrap (by omega) memT
    have topEquation : (t.gpr .r3).toNat+2^32*(t.gpr .r4).toNat=H+(v.gpr .r11).toNat := by
      have lo := oldTop 0 (by decide)
      have hi := oldTop 1 (by decide)
      simp only [Nat.mul_zero,Nat.add_zero,Nat.mul_one] at lo hi
      rw [show acc+4*(n-1)+4=acc+4*n by omega,
        show acc+4*(n-1)+8=acc+4*n+4 by omega,lo,hi] at topValue
      simpa only [H,val32,Nat.mul_zero,Nat.add_zero,Nat.add_assoc] using topValue
    refine ⟨?_,?_,?_,?_⟩
    · rw [show n+1=(n-1)+2 by omega,whole,topEquation]
      exact total
    · rw [ptrT]
      congr 2
      omega
    · exact (outside.mono (Nat.le_refl _) (by omega)).trans
        (outTop.mono (by omega) (by omega))
    · exact rest.trans (restT.mono (by simp [roundClobbers]))

end VG.Proof.Bignum.Arm.FusedReduction
