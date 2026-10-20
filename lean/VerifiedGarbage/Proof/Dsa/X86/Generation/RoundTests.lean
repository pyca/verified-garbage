module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.MillerRabinMath
public import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundEffects
import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundLoop
import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundResult

/-! # The prepared public-input Miller–Rabin round returns zero or one -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation
open VG.Proof.Ecdsa.X86

def roundAnswer (m k z : Nat) : Bool := if z = 1 ∨ z = m - 1 then true else publicMrSquares m k z

theorem roundTests_ok {base : Addr} {n m size k : Nat} {s : State} (R : RoundReady base n m size s)
    (bound : k < 2 ^ 32) (count : s.mem.readW (off base roundCount) 32 = BitVec.ofNat 32 k) :
    WP isa (roundTests n) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (roundAnswer m k (wordsVal s.mem base (slot n 6) n)).toNat ∧
      Outs base (roundWrites n) s.mem t.mem ∧ Keeps clob s t := by
  let z := wordsVal s.mem base (slot n 6) n
  let answer := roundAnswer m k z
  have finish {a : State} (Ra : RoundReady base n m size a)
      (status : a.mem.readW (off base roundStatus) 32 &&& 1 = BitVec.ofNat 32 answer.toNat)
      (O : Outs base (roundWrites n) s.mem a.mem) (K : Keeps clob s a) :
      WP isa (.block roundResult) a fun t => t.gpr .eax = BitVec.ofNat 32 answer.toNat ∧
        Outs base (roundWrites n) s.mem t.mem ∧ Keeps clob s t := by
    refine WP.mono (roundResult_ok Ra) fun t ⟨value, mem, Kt⟩ => ?_
    exact ⟨value.trans status, by rw [mem]; exact O, K.trans Kt⟩
  unfold roundTests
  refine WP.seq (WP.mono (roundCompare_ready R) fun a ⟨Ra, zf, status, value, ca, Oa, Ka⟩ => ?_)
  change a.zf = some (decide (¬ (z = 1 ∨ z = m - 1))) at zf
  by_cases terminal : z = 1 ∨ z = m - 1
  · refine WP.seq (WP.ite true (by simp [eval, zf, terminal]) (fun _ => ?_) (fun e => Bool.noConfusion e))
    refine WP.mono (roundAccept_ok Ra) fun t ⟨Rt, st, Ot, Kt⟩ => ?_
    apply finish Rt ?_ (Oa.trans Ot) (Ka.trans Kt)
    rw [st]
    simp [answer, roundAnswer, terminal]
  · refine WP.seq (WP.ite false (by simp [eval, zf, terminal]) (fun e => Bool.noConfusion e) (fun _ => ?_))
    refine WP.seq (WP.mono (roundCountTest_ok Ra bound (ca.trans count)) fun b ⟨zb, mb, Kb⟩ => ?_)
    have Rb := Ra.unchanged mb Kb (by decide) (by decide)
    have Ob : Outs base (roundWrites n) s.mem b.mem := by rw [mb]; exact Oa
    have Ksb := Ka.trans Kb
    by_cases zero : k = 0
    · refine WP.ite true (by simp [eval, zb, zero]) (fun _ => WP.block_nil ?_) (fun e => Bool.noConfusion e)
      apply finish Rb ?_ Ob Ksb
      rw [mb, status]
      change mask32 (z = m - 1) &&& 1 = BitVec.ofNat 32 answer.toNat
      have af : answer = false := by simp only [answer, roundAnswer, terminal, ite_false, zero, publicMrSquares]
      rw [af]
      simp only [mask32, show ¬ z = m - 1 from fun h => terminal (.inr h), ite_false]
      rfl
    · refine WP.ite false (by simp [eval, zb, zero]) (fun e => Bool.noConfusion e) (fun _ => ?_)
      refine WP.mono (roundLoop_ok Rb (by omega) bound (by rw [mb, ca, count])) fun t ⟨Rt, st, Ot, Kt⟩ => ?_
      apply finish Rt ?_ (Ob.trans Ot) (Ksb.trans Kt)
      rw [st, mask32_low, mb, value]
      simp only [answer, roundAnswer, terminal, ite_false, z]
end VG.Proof.Dsa.X86.Generation
