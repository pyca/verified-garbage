module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SaveWord
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit

/-! Select the shared compact Miller–Rabin kernel's shift in 1..=4. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Ffdh.Arm
open VG.Proof.X25519.Arm (Rest ofNat_beq_zero wp_mov op2_imm)

def countShift (count : Nat) : Nat := if count % 4 = 0 then 4 else count % 4

theorem countShift_bounds (count : Nat) : 0 < countShift count ∧ countShift count ≤ 4 := by
  unfold countShift
  split <;> omega

private theorem maskCount (count : Nat) : BitVec.ofNat 32 count &&& 3 = BitVec.ofNat 32 (count % 4) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  change (count % 2 ^ 32 &&& (2 ^ 2 - 1)) = (count % 4) % 2 ^ 32
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod_of_dvd count (by decide : 4 ∣ 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : count % 4 < 2 ^ 32)]

private theorem sigmaHead_ok {s : State} {count : Nat} (stack : Workspace s s.sp 72)
    (saved : s.mem.readW (State.addr (s.sp + 60#32)) 32 = BitVec.ofNat 32 count) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.exponentSigmaHead) s fun t =>
      (t.gpr .r1 = BitVec.ofNat 32 (count % 4) ∧ t.z = decide (count % 4 = 0) ∧ t.mem = s.mem) ∧
      Rest [.r1] s t := by
  have read : InRegions (s.rd ++ s.wr) (State.addr (s.sp + 60#32)) 4 := by
    rw [VG.Arm.addr_add (by have := stack.nowrap; omega)]
    exact stack.read (by decide)
  refine withRest [.r1] ?_ (by
    intro r hr op hop
    have checked : (instrs (.block VG.Impl.Ffdh.Arm.ParameterCandidate.exponentSigmaHead : Prog isa)).all
        (fun op => !(clobbers op r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have h := List.all_eq_true.mp checked op hop
    cases hc : clobbers op r <;> simp_all) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.exponentSigmaHead
  ffrun [BitVec.add_zero, read, saved, maskCount count]
  change (_ - 0#32 == 0#32) = _
  rw [BitVec.sub_zero]
  exact ofNat_beq_zero (by omega : count % 4 < 2 ^ 32)

private theorem sigmaChoice_ok {s : State} {count : Nat}
    (value : s.gpr .r1 = BitVec.ofNat 32 (count % 4)) (zero : s.z = decide (count % 4 = 0)) :
    WP isa (.ite .eq (.block [.mov .r1 (.imm 4)]) (.block [])) s fun t =>
      t.gpr .r1 = BitVec.ofNat 32 (countShift count) ∧ t.mem = s.mem ∧ Rest [.r1] s t := by
  by_cases divisible : count % 4 = 0
  · refine WP.ite true (by change some s.z = some true; simp only [zero, divisible, decide_true]) ?_
      (by intro h; cases h)
    intro _
    refine wp_mov (op2_imm (by decide)) fun t u => WP.block_nil ?_
    refine ⟨?_, u.mem, u.rest (by simp)⟩
    simp only [countShift, divisible, ite_true]
    exact u.gpr
  · refine WP.ite false (by change some s.z = some false; simp only [zero, divisible, decide_false])
      (by intro h; cases h) ?_
    intro _
    exact WP.block_nil ⟨by simpa only [countShift, divisible, ite_false] using value, rfl, Rest.refl _ _⟩

theorem exponentSigma_ok {s : State} {count : Nat} (stack : Workspace s s.sp 72)
    (saved : s.mem.readW (State.addr (s.sp + 60#32)) 32 = BitVec.ofNat 32 count) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.exponentSigma s fun t =>
      t.mem = s.mem.writeW (State.addr (s.sp + 64#32)) (BitVec.ofNat 32 (countShift count)) ∧
      Rest [.r1, .r12] s t := by
  simp only [VG.Impl.Ffdh.Arm.ParameterCandidate.exponentSigma, VG.Impl.Ffdh.Arm.ParameterCandidate.seqs]
  refine WP.seq (WP.mono (sigmaHead_ok stack saved) ?_)
  rintro u ⟨⟨valueU, zeroU, memU⟩, restU⟩
  refine WP.seq (WP.mono (sigmaChoice_ok valueU zeroU) ?_)
  rintro v ⟨valueV, memV, restV⟩
  have restUV := restU.trans restV
  have stackV : Workspace v v.sp 72 := by rw [restUV.sp]; exact stack.congr restUV.wr
  refine WP.seq (WP.mono (saveR1_ok stackV (d := 64) (by decide)) ?_)
  rintro t ⟨memT, restT⟩
  exact WP.block_nil ⟨by rw [memT, valueV, memV, memU, restUV.sp],
    (restUV.mono (by simp)).trans (restT.mono (by simp))⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
