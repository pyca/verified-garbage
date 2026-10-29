module

public import VerifiedGarbage.Impl.Bignum.Arm.FusedReduction
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState

import VerifiedGarbage.Proof.Bignum.Arm.DownRow
import VerifiedGarbage.Proof.Bignum.Arm.RowCarryMemory
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Bignum.Arm.Mac
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.X25519.Arm.Instr
/-! The fused cancellation row computes the quotient without moving its array. -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/FusedReductionFirst.lean`, which only this module imported.
section

/-! The low Montgomery word cancels without being stored or shifted. -/

section
namespace VG.Proof.Bignum.Arm.FusedReduction
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_mov wp_dp wp_subs op2_reg op2_imm dpVal)

theorem first_ok (s : State) {base : BitVec 32} {size acc mod n : Nat}
    (ws : Workspace s base size) (accFit : acc+4≤size) (modFit : mod+4≤size)
    (positive : 0<n) (ptr : s.gpr .r0=base+BitVec.ofNat 32 acc)
    (source : s.gpr .r12=base+BitVec.ofNat 32 mod)
    (count : s.gpr .lr=BitVec.ofNat 32 n) (carry : s.gpr .r11=0)
    (cancel : ((s.gpr .r1).toNat*w32 s.mem (State.addr base) mod+
      w32 s.mem (State.addr base) acc)%2^32=0) :
    WP isa VG.Impl.Bignum.Arm.FusedReduction.first s fun t =>
      t.gpr .r0=base+BitVec.ofNat 32 acc ∧
      t.gpr .r12=base+BitVec.ofNat 32 (mod+4) ∧
      t.gpr .lr=BitVec.ofNat 32 (n-1) ∧ t.gpr .r1=s.gpr .r1 ∧
      2^32*(t.gpr .r11).toNat=(s.gpr .r1).toNat*w32 s.mem (State.addr base) mod+
        w32 s.mem (State.addr base) acc ∧
      t.mem=s.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Bignum.Arm.FusedReduction.first, WP.seq_iff]
  have args : WP isa (.block VG.Impl.Bignum.Arm.FusedReduction.firstArgs) s fun u =>
      u.gpr .r2=s.mem.readW (off (State.addr base) mod) 32 ∧
      u.gpr .r10=s.mem.readW (off (State.addr base) acc) 32 ∧
      u.mem=s.mem ∧ Rest [.r2,.r10] s u := by
    unfold VG.Impl.Bignum.Arm.FusedReduction.firstArgs
    refine wp_ldr (a:=off (State.addr base) mod) (by decide)
      (by simpa only [Nat.add_zero] using ws.ea source (imm:=0) (by omega)) (ws.read modFit) fun u h => ?_
    refine wp_ldr (a:=off (State.addr base) acc) (by decide)
      (by rw [h.other .r0 (by decide)]; simpa only [Nat.add_zero] using ws.ea ptr (imm:=0) (by omega))
      (by rw [h.rd,h.wr]; exact ws.read accFit) fun v k => WP.block_nil ?_
    exact ⟨(k.other .r2 (by decide)).trans h.gpr,
      by rw [k.gpr,h.mem],k.mem.trans h.mem,(h.rest (by decide)).trans (k.rest (by decide))⟩
  refine WP.mono args ?_
  rintro u ⟨input,accumulator,memU,restU⟩
  rw [WP.seq_iff]
  refine WP.mono (mac_ok u) ?_
  rintro v ⟨value,frame⟩
  have r0 : v.gpr .r0=base+BitVec.ofNat 32 acc :=
    (frame.regs .r0 (by decide)).trans ((restU.gpr .r0 (by decide)).trans ptr)
  have r1 : v.gpr .r1=s.gpr .r1 :=
    (frame.regs .r1 (by decide)).trans (restU.gpr .r1 (by decide))
  have r12 : v.gpr .r12=base+BitVec.ofNat 32 mod :=
    (frame.regs .r12 (by decide)).trans ((restU.gpr .r12 (by decide)).trans source)
  have lr : v.gpr .lr=BitVec.ofNat 32 n :=
    (frame.regs .lr (by decide)).trans ((restU.gpr .lr (by decide)).trans count)
  rw [restU.gpr .r1 (by decide),input,accumulator,restU.gpr .r11 (by decide),carry] at value
  simp only [show (0:BitVec 32).toNat=0 from rfl,Nat.add_zero] at value
  have high : 2^32*(v.gpr .r4).toNat=(s.gpr .r1).toNat*w32 s.mem (State.addr base) mod+
      w32 s.mem (State.addr base) acc := by
    change (v.gpr .r3).toNat+(v.gpr .r4).toNat*2^32=_ at value
    have low := (v.gpr .r3).isLt
    dsimp only [w32] at cancel ⊢
    omega
  have kept : Rest roundClobbers s v := (restU.mono (by decide)).trans
    ((show Rest clobbers u v from ⟨frame.regs,frame.rd,frame.wr,frame.sp⟩).mono
      (by decide))
  unfold VG.Impl.Bignum.Arm.FusedReduction.firstNext
  refine wp_mov (op2_reg _ _) fun a ha => ?_
  refine wp_dp (op2_imm (by decide)) fun b hb => ?_
  refine wp_subs (op2_imm (by decide)) fun t ht _zero => WP.block_nil ?_
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · rw [ht.other .r0 (by decide),hb.other .r0 (by decide),ha.other .r0 (by decide)]; exact r0
  · rw [ht.other .r12 (by decide),hb.gpr,dpVal,ha.other .r12 (by decide),r12]
    exact Offset.add_add _ _ _
  · rw [ht.gpr,hb.other .lr (by decide),ha.other .lr (by decide),lr]
    exact BitVec.ofNat_sub_ofNat_of_le n 1 (by decide) positive
  · rw [ht.other .r1 (by decide),hb.other .r1 (by decide),ha.other .r1 (by decide)]; exact r1
  · rw [ht.other .r11 (by decide),hb.other .r11 (by decide),ha.gpr]; exact high
  · rw [ht.mem,hb.mem,ha.mem,frame.mem,memU]
  · exact kept.trans ((ha.rest (by decide)).trans
      ((hb.rest (by decide)).trans (ht.rest (by decide))))

end VG.Proof.Bignum.Arm.FusedReduction
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/FusedReductionTop.lean`, which only this module imported.
section

/-! Add the last row carry and store the two high quotient words directly. -/

section
namespace VG.Proof.Bignum.Arm.FusedReduction
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_str wp_dp op2_imm dpVal)

theorem top_ok (s : State) {base : BitVec 32} {size d : Nat}
    (ws : Workspace s base size) (fit : d+12≤size)
    (ptr : s.gpr .r0=base+BitVec.ofNat 32 d)
    (bound : w32 s.mem (State.addr base) (d+4)+2^32*w32 s.mem (State.addr base) (d+8)+
      (s.gpr .r11).toNat<2^64) :
    WP isa VG.Impl.Bignum.Arm.FusedReduction.top s fun t =>
      (t.gpr .r3).toNat+2^32*(t.gpr .r4).toNat=
        w32 s.mem (State.addr base) (d+4)+2^32*w32 s.mem (State.addr base) (d+8)+
          (s.gpr .r11).toNat ∧
      t.mem=(s.mem.writeW (off (State.addr base) d) (t.gpr .r3)).writeW
        (off (State.addr base) (d+4)) (t.gpr .r4) ∧
      t.gpr .r0=base+BitVec.ofNat 32 (d+8) ∧ Rest [.r0,.r3,.r4] s t := by
  rw [VG.Impl.Bignum.Arm.FusedReduction.top,WP.seq_iff]
  have loads : WP isa (.block [.ldr .r3 .r0 4,.ldr .r4 .r0 8]) s fun u =>
      u.gpr .r3=s.mem.readW (off (State.addr base) (d+4)) 32 ∧
      u.gpr .r4=s.mem.readW (off (State.addr base) (d+8)) 32 ∧
      u.mem=s.mem ∧ Rest [.r3,.r4] s u := by
    refine wp_ldr (a:=off (State.addr base) (d+4)) (by decide) (ws.ea ptr (by omega))
      (ws.read (by omega)) fun u h => ?_
    refine wp_ldr (a:=off (State.addr base) (d+8)) (by decide)
      (by rw [h.other .r0 (by decide)];exact ws.ea ptr (by omega))
      (by rw [h.rd,h.wr];exact ws.read (by omega)) fun v k => WP.block_nil ?_
    exact ⟨(k.other .r3 (by decide)).trans h.gpr,by rw [k.gpr,h.mem],
      k.mem.trans h.mem,(h.rest (by decide)).trans (k.rest (by decide))⟩
  refine WP.mono loads ?_
  rintro u ⟨low,high,memU,restU⟩
  have carry : u.gpr .r11=s.gpr .r11 := restU.gpr .r11 (by decide)
  rw [WP.seq_iff]
  refine WP.mono (addWord_ok u .r11 (by rw [low,high,carry];dsimp only [w32] at bound;omega)) ?_
  rintro v ⟨value,frame⟩
  have pv : v.gpr .r0=base+BitVec.ofNat 32 d :=
    (frame.regs .r0 (by decide)).trans ((restU.gpr .r0 (by decide)).trans ptr)
  have mv : v.mem=s.mem := frame.mem.trans memU
  have wv : v.wr=s.wr := frame.wr.trans restU.wr
  have wsv := ws.congr wv
  refine wp_str (a:=off (State.addr base) d) (by decide)
    (by simpa only [Nat.add_zero] using wsv.ea pv (imm:=0) (by omega))
    (by rw [wv];exact ws.write (by omega)) fun a ha => ?_
  refine wp_str (a:=off (State.addr base) (d+4)) (by decide)
    (by rw [ha.gpr];exact wsv.ea pv (by omega))
    (by rw [ha.wr,wv];exact ws.write (by omega)) fun b hb => ?_
  refine wp_dp (op2_imm (by decide)) fun t ht => WP.block_nil ?_
  refine ⟨?_,?_,?_,?_⟩
  · rw [ht.other .r3 (by decide),ht.other .r4 (by decide),hb.gpr,ha.gpr]
    rw [low,high,carry] at value
    simpa only [w32,Nat.mul_comm] using value
  · rw [ht.mem,hb.mem,ha.mem,mv,ht.other .r3 (by decide),ht.other .r4 (by decide),hb.gpr,ha.gpr]
  · rw [ht.gpr,dpVal,hb.gpr,ha.gpr,pv]
    exact Offset.add_add _ _ _
  · have rv : Rest [.r3,.r4] s v := restU.trans ⟨frame.regs,frame.rd,frame.wr,frame.sp⟩
    exact (rv.mono (by decide)).trans ((ha.rest _).trans
      ((hb.rest _).trans (ht.rest (by decide))))

end VG.Proof.Bignum.Arm.FusedReduction
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/FusedReductionMath.lean`, which only this module imported.
section

/-! The cancellation carry and the downward row together divide exactly. -/

section
namespace VG.Proof.Bignum.Arm.FusedReduction

theorem quotient_value {B P T M t0 tl th m0 ml q c0 rl cr rh : Nat}
    (acc : T=t0+B*(tl+P*th)) (modulus : M=m0+B*ml)
    (first : B*c0=q*m0+t0) (row : rl+P*cr=tl+q*ml+c0)
    (top : rh=th+cr) : B*(rl+P*rh)=T+q*M := by
  have step := congrArg (fun x => B*x) row
  grind

end VG.Proof.Bignum.Arm.FusedReduction
end

end

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
  refine WP.mono (first_ok s ws (by omega_arith) (by omega_arith) (by omega_arith) ptr source count carry cancel) ?_
  rintro u ⟨ptrU,sourceU,countU,scalarU,first,memU,restU⟩
  have ctx : DownRow.Ctx u base size acc (mod+4) (n-1) :=
    ⟨ws.nowrap,by omega_arith,by omega_arith,by rcases separate with h|h <;> omega_arith,
      by rw [restU.wr];exact ws.writable⟩
  rw [WP.seq_iff]
  refine WP.mono (DownRow.code_ok u ctx (by omega_arith) ptrU sourceU countU) ?_
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
    rw [show n+2=(n+1)+1 by omega_arith,val32]
    have split := val32_append s.mem (State.addr base) (acc+4) (n-1) 2
    simpa only [show n-1+2=n+1 by omega_arith,show acc+4+4*(n-1)=acc+4*n by omega_arith] using
      congrArg (fun x => w32 s.mem (State.addr base) acc+2^32*x) split
  have modSplit : val32 s.mem (State.addr base) mod n=
      w32 s.mem (State.addr base) mod+2^32*val32 s.mem (State.addr base) (mod+4) (n-1) := by
    calc
      _ = val32 s.mem (State.addr base) mod ((n-1)+1) := by congr 1;omega_arith
      _ = _ := rfl
  have total : 2^32*(val32 v.mem (State.addr base) acc (n-1)+P*(H+(v.gpr .r11).toNat))=
      val32 s.mem (State.addr base) acc (n+2)+Q*val32 s.mem (State.addr base) mod n :=
    quotient_value accSplit modSplit first rowValue rfl
  have power : 2^32*(P*2^64)=2^(32*(n+2)) := by
    dsimp only [P]
    rw [←Nat.pow_add,←Nat.pow_add]
    congr 1
    omega_arith
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
    outside.w32 (by omega_arith) (by have := ws.nowrap;omega_arith)
  have fitTop : acc+4*(n-1)+12≤size := by omega_arith
  have native : Rest roundClobbers u v := (row.rest.mono (by decide))
  have rest : Rest roundClobbers s v := restU.trans native
  have workspaceV := ws.congr rest.wr
  refine WP.mono (top_ok v workspaceV fitTop row.outPtr ?_) ?_
  · have lo := oldTop 0 (by decide)
    have hi := oldTop 1 (by decide)
    simp only [Nat.mul_zero,Nat.add_zero,Nat.mul_one] at lo hi
    rw [show acc+4*(n-1)+4=acc+4*n by omega_arith,
      show acc+4*(n-1)+8=acc+4*n+4 by omega_arith,lo,hi]
    simpa only [H,val32,Nat.mul_zero,Nat.add_zero,Nat.add_assoc] using topBound
  · rintro t ⟨topValue,memT,ptrT,restT⟩
    have nowrap : (State.addr base).toNat+size≤2^32 := by
      simpa only [VG.Proof.X25519.Arm.addr_toNat] using ws.nowrap
    obtain ⟨outTop,whole⟩ := rowCarry_memory (base:=State.addr base) (n:=n-1)
      nowrap (by omega_arith) memT
    have topEquation : (t.gpr .r3).toNat+2^32*(t.gpr .r4).toNat=H+(v.gpr .r11).toNat := by
      have lo := oldTop 0 (by decide)
      have hi := oldTop 1 (by decide)
      simp only [Nat.mul_zero,Nat.add_zero,Nat.mul_one] at lo hi
      rw [show acc+4*(n-1)+4=acc+4*n by omega_arith,
        show acc+4*(n-1)+8=acc+4*n+4 by omega_arith,lo,hi] at topValue
      simpa only [H,val32,Nat.mul_zero,Nat.add_zero,Nat.add_assoc] using topValue
    refine ⟨?_,?_,?_,?_⟩
    · rw [show n+1=(n-1)+2 by omega_arith,whole,topEquation]
      exact total
    · rw [ptrT]
      congr 2
      omega_arith
    · exact (outside.mono (Nat.le_refl _) (by omega_arith)).trans
        (outTop.mono (by omega_arith) (by omega_arith))
    · exact rest.trans (restT.mono (by decide))

end VG.Proof.Bignum.Arm.FusedReduction
