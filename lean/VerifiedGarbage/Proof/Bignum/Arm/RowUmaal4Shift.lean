module

public import VerifiedGarbage.Proof.Bignum.Arm.RowUmaal4Step
import VerifiedGarbage.Proof.Framework.Arm.RegUpd

/-! Moving the pointer advance across two more UMAAL words. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Arm.RegUpd VG.Impl.Bignum.Arm

def shift8 (s : State) : State :=
  ((s.setReg .r0 (s.gpr .r0 + 8)).setReg .r12 (s.gpr .r12 + 8)).setReg .lr (s.gpr .lr - 2)

theorem inW_shift8 (k : Nat) (s : State) : inW k (shift8 s) = inW (8 + k) s := by
  simp only [inW, shift8, mem_setReg, gpr_setReg, reduceCtorEq, ↓reduceIte]
  congr 2
  rw [BitVec.add_assoc]
  congr 1
  exact (BitVec.ofNat_add 8 k).symm

theorem accW_shift8 (k : Nat) (s : State) : accW k (shift8 s) = accW (8 + k) s := by
  simp only [accW, shift8, mem_setReg, gpr_setReg, reduceCtorEq, ↓reduceIte]
  congr 2
  rw [BitVec.add_assoc]
  congr 1
  exact (BitVec.ofNat_add 8 k).symm

theorem stepNew_shift8 (k : Nat) (s : State) :
    stepNew k (shift8 s) = shift8 (stepNew (8 + k) s) := by
  simp only [stepNew, inW_shift8, accW_shift8]
  simp only [shift8, gpr_setReg, reduceCtorEq, ↓reduceIte, mem_setReg]
  have address : (s.gpr .r0 + 8) + BitVec.ofNat 32 k = s.gpr .r0 + BitVec.ofNat 32 (8 + k) := by
    rw [BitVec.add_assoc]
    congr 1
    exact (BitVec.ofNat_add 8 k).symm
  rw [address]
  simp only [State.setReg]
  congr 1
  funext r
  cases r <;> rfl

theorem stepNew_noFlags (k : Nat) {s t : State} (h : NoFlags s t) :
    NoFlags (stepNew k s) (stepNew k t) := by
  obtain ⟨g, sp, m, rd, wr, u, sy⟩ := h
  cases s; cases t
  dsimp only at g sp m rd wr u sy
  subst g sp m rd wr u sy
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem advState_shift8 (s : State) : NoFlags (advState s) (shift8 s) :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem advState_noFlags_eq {s t : State} (h : NoFlags s t) : advState s = advState t := by
  have equal := advance_noFlags h
  rw [advState_exec, advState_exec] at equal
  exact (Prod.mk.inj (Option.some.inj equal)).1

theorem advState4_noFlags_eq {s t : State} (h : NoFlags s t) : advState4 s = advState4 t := by
  obtain ⟨g, sp, m, rd, wr, u, sy⟩ := h
  cases s; cases t
  dsimp only at g sp m rd wr u sy
  subst g sp m rd wr u sy
  rfl

theorem advState_shift8_four (s : State) : NoFlags (advState (shift8 s)) (advState4 s) := by
  constructor
  · funext r
    cases r <;> simp only [advState, shift8, advState4, subFlags, gpr_setReg, reduceCtorEq, ↓reduceIte]
    all_goals simp only [BitVec.add_assoc, BitVec.sub_sub]
    all_goals rfl
  all_goals rfl

theorem advState_shift8_zero (s : State) (h : s.gpr .lr = 4) :
    advState (shift8 s) = advState4 s := by
  apply (advState_shift8_four s).eq
  all_goals simp only [advState, shift8, advState4, subFlags, n_setReg, z_setReg, c_setReg,
    v_setReg, gpr_setReg, reduceCtorEq, ↓reduceIte, h]
  all_goals decide

end VG.Proof.Bignum.Arm
