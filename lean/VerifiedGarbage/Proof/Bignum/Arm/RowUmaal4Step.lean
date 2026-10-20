module

public import VerifiedGarbage.Impl.Bignum.Arm.RowUmaal4
public import VerifiedGarbage.Proof.Bignum.Arm.RowUmaal
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! The first three words need no saved accumulator register. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Arm.RegUpd VG.Impl.Bignum.Arm

theorem rowFirstAtU_exec {k : Nat} (hk : k < 4096) (n : State)
    (hr : InRegions (n.rd ++ n.wr) (State.addr (n.gpr .r12 + BitVec.ofNat 32 k)) 4)
    (hw : InRegions n.wr (State.addr (n.gpr .r0 + BitVec.ofNat 32 k)) 4) :
    execBlock isa (rowFirstAtU k) n = some ((stepNew k n).setReg .r5 (n.gpr .r5),
      [.addr (State.addr (n.gpr .r12 + BitVec.ofNat 32 k)), .addr (State.addr (n.gpr .r0 + BitVec.ofNat 32 k)),
        .addr (State.addr (n.gpr .r0 + BitVec.ofNat 32 k))]) := by
  have hr0 : InRegions (n.rd ++ n.wr) (State.addr (n.gpr .r0 + BitVec.ofNat 32 k)) 4 := by
    obtain ⟨R, hR, hc⟩ := hw; exact ⟨R, List.mem_append_right _ hR, hc⟩
  simp only [rowFirstAtU, execBlock, isa, exec, hk, ↓reduceIte, State.load32, State.store32,
    gpr_setReg, reduceCtorEq, rd_setReg, wr_setReg, mem_setReg, hr, hr0, hw, Option.map_some, addrs,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  congr 2
  simp only [stepNew, State.setReg]
  congr 1
  funext r
  cases r <;> simp [inW, accW]

def advState4 (s : State) : State :=
  (subFlags ((s.setReg .r0 (s.gpr .r0 + 16)).setReg .r12 (s.gpr .r12 + 16)) (s.gpr .lr) 4).setReg .lr
    (s.gpr .lr - 4)

theorem advState4_exec (s : State) : execBlock isa rowAdvance4 s = some (advState4 s, []) := by
  simp only [rowAdvance4, execBlock, isa, exec, Op2.eval, Option.map_some, addrs,
    List.map_nil, List.append_nil]
  rfl

end VG.Proof.Bignum.Arm
