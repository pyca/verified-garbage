module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyReady
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyFrame
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyView
import VerifiedGarbage.Proof.Rsa.Arm.KeyBits
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! Increment the native halving count and test the new exponent's low bit. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.Ffdh.Arm
open VG.Proof.X25519.Arm (Rest ofNat_beq_zero)
open VG.Proof.Rsa.Arm.Keys (num arr S)

theorem halfCountTail_ok {s : State} {base : BitVec 32} {capacity w count : Nat}
    (workspace : Workspace s base (8 * capacity)) (ready : KeyReady base capacity w s)
    (stack : Workspace s s.sp 72)
    (saved : s.mem.readW (State.addr (s.sp + 60#32)) 32 = BitVec.ofNat 32 count)
    (separate : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.halfCountTail) s fun t =>
      (t.mem = s.mem.writeW (State.addr (s.sp + 60#32)) (BitVec.ofNat 32 (count + 1)) ∧
        t.z = decide (num s.mem (base + 96#32) (2 * w + 2) 29 % 2 = 0)) ∧
      Rest [.r0, .r1, .r12] s t := by
  have read : InRegions (s.rd ++ s.wr) (State.addr (s.sp + 60#32)) 4 := by
    rw [VG.Arm.addr_add (by have := stack.nowrap; omega)]
    exact stack.read (by decide)
  have write : InRegions s.wr (State.addr (s.sp + 60#32)) 4 := by
    rw [VG.Arm.addr_add (by have := stack.nowrap; omega)]
    exact stack.write (by decide)
  let B := base + 96#32
  let d := arr (2 * w + 2) 29
  have nativeAddr : State.addr (B + BitVec.ofNat 32 d) = off (State.addr B) d :=
    ready.addr (by have := ready.arr_fit (j := 29) (by decide); simp only [S] at this; omega)
  have realRead : InRegions (s.rd ++ s.wr) (State.addr (B + BitVec.ofNat 32 d)) 4 := by
    rw [nativeAddr]
    rw [VG.Arm.addr_add (ready.baseShiftFits workspace)]
    unfold off
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, keyView_array]
    exact workspace.read (by have := ready.arrayFit (j := 29) (by decide); omega)
  have stackSep : (⟨State.addr (s.sp + 60#32), 4⟩ : Region).Disjoint
      ⟨State.addr (B + BitVec.ofNat 32 d), 4⟩ := by
    have a : State.addr (B + BitVec.ofNat 32 d) = off (State.addr base) (Proof.Rsa.Mont.arrAt w 29) := by
      rw [nativeAddr, VG.Arm.addr_add (ready.baseShiftFits workspace)]
      unfold off
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, keyView_array]
    rw [a, VG.Arm.addr_add (by have := stack.nowrap; omega)]
    exact separate.sub_left (Offset.sub_base _ (by decide : 60 + 4 ≤ 72)) |>.sub_right
      (Offset.sub_base _ (by have := ready.arrayFit (j := 29) (by decide); omega))
  have lowUnchanged : (s.mem.writeW (State.addr (s.sp + 60#32)) (BitVec.ofNat 32 (count + 1))).readW
      (State.addr (B + BitVec.ofNat 32 d)) 32 = s.mem.readW (State.addr (B + BitVec.ofNat 32 d)) 32 :=
    Mem.readW_writeW_sep stackSep.symm (by decide)
  have ptrValue : BitVec.ofNat 32 29 * BitVec.ofNat 32 (S (2 * w + 2)) + B + 160 = B + BitVec.ofNat 32 d :=
    VG.Proof.Rsa.Arm.Keys.ptr_val B 29 (S (2 * w + 2))
  change BitVec.ofNat 32 29 * BitVec.ofNat 32 (S (2 * w + 2)) + B +
    BitVec.ofNat 32 VG.Impl.Rsa.Arm.Keys.hdr = B + BitVec.ofNat 32 d at ptrValue
  have r7 : s.gpr .r7 = BitVec.ofNat 32 (S (2 * w + 2)) := ready.r7
  have r8 : s.gpr .r8 = B := ready.r8
  have plus : BitVec.ofNat 32 count + 1 = BitVec.ofNat 32 (count + 1) := by
    change BitVec.ofNat 32 count + BitVec.ofNat 32 1 = _
    exact BitVec.ofNat_add_ofNat count 1
  have parity : (s.mem.readW (State.addr (B + BitVec.ofNat 32 d)) 32 &&& 1 == 0) =
      decide (num s.mem B (2 * w + 2) 29 % 2 = 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    rw [← BitVec.toNat_inj, VG.Proof.Rsa.Arm.Keys.bv_and_one, nativeAddr,
      ← VG.Proof.Rsa.Arm.Keys.num_mod2 s.mem B (by omega : 0 < 2 * w + 2)]
    rfl
  refine withRest_all [.r0, .r1, .r12] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.halfCountTail VG.Impl.Ffdh.Arm.ParameterCandidate.save
    VG.Impl.Rsa.Arm.Keys.ptr
  ffrun [List.cons_append, List.nil_append, BitVec.add_zero, read, write, saved, plus, r7, r8,
    ptrValue, realRead, lowUnchanged]
  change (_ - 0#32 == 0#32) = _
  rw [BitVec.sub_zero]
  exact parity

end VG.Proof.Ffdh.Arm.ParameterCandidate
