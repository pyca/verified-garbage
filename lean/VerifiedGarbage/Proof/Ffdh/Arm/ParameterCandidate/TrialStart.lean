module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.Proof.RsaKeyGen.Trial16
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Bignum.Arm.TrialDivision16
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! Initialize the shared RSA trial reducer from FFDH's public frame. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm
open VG.Proof.X25519.Arm

theorem trialStart_ok (s : State) (dst : BitVec 32) (n : Nat)
    (readOut : InRegions (s.rd ++ s.wr) (State.addr (s.sp + 4)) 4)
    (readWidth : InRegions (s.rd ++ s.wr) (State.addr (s.sp + 12)) 4)
    (out : s.mem.readW (State.addr (s.sp + 4)) 32 = dst)
    (width : s.mem.readW (State.addr (s.sp + 12)) 32 = BitVec.ofNat 32 n) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.trialStart) s fun t =>
      (t.gpr .r0 = dst + BitVec.ofNat 32 n ∧ t.gpr .r1 = BitVec.ofNat 32 n ∧
        t.gpr .r2 = 0 ∧ t.gpr .r3 = s.gpr .r7 ∧
        t.gpr .r4 = VG.Proof.RsaKeyGen.ninv (s.gpr .r7) ∧ t.mem = s.mem) ∧
        Rest [.r0, .r1, .r2, .r3, .r4, .r5, .r6] s t := by
  refine withRest_all [.r0, .r1, .r2, .r3, .r4, .r5, .r6] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.trialStart
  simp only [List.cons_append, List.nil_append]
  refine wp_mov (op2_reg _ _) fun u1 v1 => wp_mov (op2_reg _ _) fun u2 v2 =>
    VG.Proof.Bignum.Arm.TrialDivision16.newton_ok fun u3 k3 m3 e3 =>
    VG.Proof.Bignum.Arm.TrialDivision16.newton_ok fun u4 k4 m4 e4 =>
    VG.Proof.Bignum.Arm.TrialDivision16.newton_ok fun u5 k5 m5 e5 => ?_
  have keep2 : Rest [.r3, .r4, .r5, .r6] s u2 :=
    (v1.rest (by simp)).trans (v2.rest (by simp))
  have keep3 := keep2.trans (k3.mono (by simp))
  have keep4 := keep3.trans (k4.mono (by simp))
  have keep5 := keep4.trans (k5.mono (by simp))
  have div2 : u2.gpr .r3 = s.gpr .r7 := by rw [v2.other _ (by decide), v1.gpr]
  have div3 : u3.gpr .r3 = s.gpr .r7 := (k3.gpr _ (by simp)).trans div2
  have div4 : u4.gpr .r3 = s.gpr .r7 := (k4.gpr _ (by simp)).trans div3
  have div5 : u5.gpr .r3 = s.gpr .r7 := (k5.gpr _ (by simp)).trans div4
  have start : u2.gpr .r4 = s.gpr .r7 := by rw [v2.gpr, v1.gpr]
  have n1 : u3.gpr .r4 = VG.Proof.RsaKeyGen.nstep (s.gpr .r7) (s.gpr .r7) := by
    rw [e3, div2, start]
  have n2 : u4.gpr .r4 = VG.Proof.RsaKeyGen.nstep (s.gpr .r7)
      (VG.Proof.RsaKeyGen.nstep (s.gpr .r7) (s.gpr .r7)) := by rw [e4, div3, n1]
  have n3 : u5.gpr .r4 = VG.Proof.RsaKeyGen.nstep (s.gpr .r7)
      (VG.Proof.RsaKeyGen.nstep (s.gpr .r7) (VG.Proof.RsaKeyGen.nstep (s.gpr .r7) (s.gpr .r7))) := by
    rw [e5, div4, n2]
  have memory : u5.mem = s.mem := by rw [m5, m4, m3, v2.mem, v1.mem]
  ffrun [show (4#32) = (4 : BitVec 32) from rfl,
    show (12#32) = (12 : BitVec 32) from rfl, n3, div5, memory, keep5.sp, keep5.rd, keep5.wr, readOut, readWidth, out, width,
    VG.Proof.RsaKeyGen.ninv]

end VG.Proof.Ffdh.Arm.ParameterCandidate
