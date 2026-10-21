module

public import VerifiedGarbage.Proof.Bignum.Arm.SquareState
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Impl.Bignum.Arm.SquareUmaal
import VerifiedGarbage.Proof.Bignum.Arm.SquareUmaalDiag
import VerifiedGarbage.Proof.Bignum.Arm.SquareBody
import VerifiedGarbage.Proof.Bignum.Arm.SquareCross
import VerifiedGarbage.Proof.Framework.Block

/-! The fused UMAAL diagonal establishes the shared square product invariant. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

section
variable {m0 : Mem} {base : BitVec 32} {size out a mod M n : Nat} {inv : BitVec 32}

theorem sqBodyU_ok (s : State) (h : SqEnv s.mem base size out a mod M n inv s)
    (p6 : s.gpr .r6 = base + BitVec.ofNat 32 M) (p7 : s.gpr .r7 = BitVec.ofNat 32 n)
    (p8 : s.gpr .r8 = base + BitVec.ofNat 32 a) (p10 : s.gpr .r10 = base + BitVec.ofNat 32 out) :
    WP isa sqBodyU s fun t =>
      val32 t.mem (State.addr base) out n < val32 s.mem (State.addr base) mod n ∧
      2 ^ (32 * n) * val32 t.mem (State.addr base) out n % val32 s.mem (State.addr base) mod n =
        val32 s.mem (State.addr base) a n * val32 s.mem (State.addr base) a n %
          val32 s.mem (State.addr base) mod n ∧
      Outs (State.addr base) [(M, 4 * (2 * n + 8)), (out, 4 * n)] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [sqBodyU, WP.seq_iff]
  refine WP.mono (sqInit_ok s h p6 p7 p8 p10) ?_
  rintro s1 ⟨h1, r1⟩
  rw [WP.seq_iff]
  refine WP.mono (crossRows_ok s1 h1) ?_
  rintro s2 ⟨h2, r2⟩
  rw [WP.seq_iff]
  refine WP.mono (sqDiagPhaseU_ok s2 h2) ?_
  rintro s4 ⟨h4, r4⟩
  rw [WP.seq_iff]
  refine WP.mono (sqReduce_ok s4 h4) ?_
  rintro s5 ⟨h5, r5⟩
  refine WP.mono (sqFinish_ok s5 h5) ?_
  rintro t ⟨lt, value, outs, r6⟩
  refine ⟨lt, value, ?_, r1.trans (r2.trans (r4.trans (r5.trans r6)))⟩
  exact (h5.env.frame.mono (by simp)).trans outs

end

end VG.Proof.Bignum.Arm
