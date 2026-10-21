module

import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeCore
public import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Proof.Ffdh.Arm.Locals
import VerifiedGarbage.Proof.Ffdh.Arm.Locals

/-! Native public counter initialization and decrement for basis squaring. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Impl.Ffdh.Arm.CombPrecompute
open VG.Proof.X25519.Arm (Rest ofNat_beq_zero)

theorem squaresInit_raw (s : State) {base : BitVec 32} {len d : Nat}
    (locals : Locals base len s)
    (saved : s.mem.readW (off (State.addr s.sp) 44) 32=BitVec.ofNat 32 d) :
    WP isa (.block squaresInit) s fun t =>
      t.mem=s.mem.writeW (off (State.addr s.sp) 68) (BitVec.ofNat 32 d) ∧ Rest [.r3,.r12] s t := by
  have a44 : State.addr (s.sp+BitVec.ofNat 32 44)=off (State.addr s.sp) 44 := addr_add (by have := locals.space.nowrap; omega)
  have a68 : State.addr (s.sp+BitVec.ofNat 32 68)=off (State.addr s.sp) 68 := addr_add (by have := locals.space.nowrap; omega)
  have read := locals.read (d:=44) (by decide)
  have write := locals.space.write (off:=68) (by decide)
  refine withRest (c:=.block squaresInit) [.r3,.r12] ?_ (by
    intro r hr i hi
    simp only [instrs,squaresInit,VG.Impl.Ffdh.Arm.Domain.st,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl <;> simp [clobbers,dstOf] at * <;> grind) rfl
  unfold squaresInit VG.Impl.Ffdh.Arm.Domain.st
  ffrun [a44,a68,read,write,saved,off,BitVec.add_zero]

theorem squaresNext_raw (s : State) {base : BitVec 32} {len n : Nat}
    (locals : Locals base len s) (positive : 0<n) (fit : n<2^32)
    (saved : s.mem.readW (off (State.addr s.sp) 68) 32=BitVec.ofNat 32 n) :
    WP isa (.block squaresNext) s fun t =>
      (t.mem=s.mem.writeW (off (State.addr s.sp) 68) (BitVec.ofNat 32 (n-1)) ∧ t.z=decide (n-1=0)) ∧ Rest [.r3,.r12] s t := by
  have a68 : State.addr (s.sp+BitVec.ofNat 32 68)=off (State.addr s.sp) 68 := addr_add (by have := locals.space.nowrap; omega)
  have read := locals.read (d:=68) (by decide)
  have write := locals.space.write (off:=68) (by decide)
  have sub : BitVec.ofNat 32 n-1=BitVec.ofNat 32 (n-1) := BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) positive
  have val : (BitVec.ofNat 32 (n-1)).toNat=n-1 := Nat.mod_eq_of_lt (by omega)
  refine withRest (c:=.block squaresNext) [.r3,.r12] ?_ (by
    intro r hr i hi
    simp only [instrs,squaresNext,VG.Impl.Ffdh.Arm.Domain.st,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl <;> simp [clobbers,dstOf] at * <;> grind) rfl
  unfold squaresNext VG.Impl.Ffdh.Arm.Domain.st
  ffrun [a68,read,write,saved,sub,val,off,BitVec.add_zero,subFlags]
  exact ofNat_beq_zero (by omega)

end VG.Proof.Ffdh.Arm.CombBuilder
