module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Mask
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! Derive the first-byte mask from the public bit length. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm
open VG.Proof.X25519.Arm (Rest)

theorem maskCount (bits : Nat) (positive : 0 < bits) (fits : bits < 2 ^ 32) :
    ((BitVec.ofNat 32 bits - 1) &&& 7) + 1 = BitVec.ofNat 32 ((bits - 1) % 8 + 1) := by
  change ((BitVec.ofNat 32 bits - BitVec.ofNat 32 1) &&& 7) + 1 = _
  rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) positive]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : bits - 1 < 2 ^ 32)]
  change ((bits - 1 &&& (2 ^ 3 - 1)) + 1) % 2 ^ 32 = (((bits - 1) % 8 + 1) % 2 ^ 32)
  rw [Nat.and_two_pow_sub_one_eq_mod]

theorem shapeMaskHead_ok (s : State) {bits : Nat} (positive : 0 < bits) (fits : bits < 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (State.addr (s.sp + 24)) 4)
    (value : s.mem.readW (State.addr (s.sp + 24)) 32 = BitVec.ofNat 32 bits) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.shapeMaskHead) s fun t =>
      (t.gpr .r6 = BitVec.ofNat 32 ((bits - 1) % 8 + 1) ∧ t.gpr .r7 = 0 ∧ t.mem = s.mem) ∧
        Rest [.r6, .r7] s t := by
  refine withRest_all [.r6, .r7] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.shapeMaskHead
  ffrun [show (24#32) = (24 : BitVec 32) from rfl, read, value, maskCount bits positive fits]

theorem shapeMasks_ok (s : State) {bits : Nat} (positive : 0 < bits) (fits : bits < 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (State.addr (s.sp + 24)) 4)
    (value : s.mem.readW (State.addr (s.sp + 24)) 32 = BitVec.ofNat 32 bits) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.shapeMasks s fun t =>
      t.gpr .r7 = BitVec.ofNat 32 (2 ^ ((bits - 1) % 8 + 1) - 1) ∧ t.mem = s.mem ∧
        Rest [.r6, .r7] s t := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.shapeMasks
  refine WP.seq (WP.mono (shapeMaskHead_ok s positive fits read value) ?_)
  rintro u ⟨⟨count, mask, mem⟩, rest⟩
  have small := Nat.mod_lt (bits - 1) (by decide : 0 < 8)
  refine WP.mono (maskLoop_ok u (by omega) (by omega) mask count) ?_
  rintro t ⟨result, _, memory, keep⟩
  exact ⟨result, memory.trans mem, rest.trans keep⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
