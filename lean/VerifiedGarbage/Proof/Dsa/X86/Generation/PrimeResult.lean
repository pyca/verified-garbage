module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PrimeControl
public import VerifiedGarbage.Proof.Ecdsa.X86.Flags
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeControl
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeUniform
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Commit the primality round's public decision and uniform count -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86 VG.Impl.Dsa.X86.Generation VG.Proof.Ecdsa.X86

def primeResultStatus (passed : Bool) (uniform checks : Nat) : Nat :=
  if passed then if uniform < checks then 4 else 1 else 3

theorem primeRoundResult_ok {s : State} {base : Addr} {size uniform checks : Nat} {isUniform passed : Bool}
    (S : Scr s base size) (room : primeIsUniform + 4 ≤ size)
    (bound : uniform + 1 < 2 ^ 32) (checks32 : checks < 2 ^ 32)
    (answer : s.gpr .eax = BitVec.ofNat 32 passed.toNat)
    (flag : s.mem.readW (off base primeIsUniform) 32 = mask32 (isUniform = true))
    (count : s.mem.readW (off base primeUniform) 32 = BitVec.ofNat 32 uniform) :
    WP isa (primeRoundResult checks) s fun t =>
      t.mem.readW (off base primeStatus) 32 =
        BitVec.ofNat 32 (primeResultStatus passed (uniform + isUniform.toNat) checks) ∧
      t.mem.readW (off base primeUniform) 32 =
        BitVec.ofNat 32 (if passed then uniform + isUniform.toNat else uniform) ∧
      Outs base [(primeUniform, 4), (primeStatus, 4)] s.mem t.mem ∧ Keeps [.eax, .ecx] s t := by
  have statusRoom : primeStatus + 4 ≤ size := by unfold primeStatus primeIsUniform at *; omega
  have finish {a : State} (Sa : Scr a base size) {status u : Nat}
      (cu : a.mem.readW (off base primeUniform) 32 = BitVec.ofNat 32 u) :
      WP isa (.block (primeMark status)) a fun t =>
        t.mem.readW (off base primeStatus) 32 = BitVec.ofNat 32 status ∧
        t.mem.readW (off base primeUniform) 32 = BitVec.ofNat 32 u ∧
        Outs base [(primeUniform, 4), (primeStatus, 4)] a.mem t.mem ∧ Keeps [.eax, .ecx] a t := by
    refine WP.mono (primeMark_ok Sa statusRoom) fun t ⟨mt, Ot, Kt⟩ => ?_
    refine ⟨by rw [mt, Mem.readW_writeW_self32], ?_, Outs.of_outside Ot (by simp), Kt.mono (by decide)⟩
    apply Eq.trans ?_ cu
    apply BitVec.eq_of_toNat_eq
    exact Ot.w32 (by decide) (by decide)
  unfold primeRoundResult
  refine WP.seq (wp_cmpi fun a sa _ za => WP.block_nil ?_)
  have Sa := S.of_keeps (sa.keeps [.eax, .ecx]) (by decide)
  have za' : a.zf = some (!passed) := by rw [za, answer]; cases passed <;> decide +kernel
  cases passed with
  | false =>
    refine WP.ite true (by simp [eval, za']) (fun _ => ?_) (fun e => Bool.noConfusion e)
    refine WP.mono (finish (status := 3) (u := uniform) Sa (by rw [sa.mem, count])) fun t ⟨status, cu, O, K⟩ => ?_
    exact ⟨status, cu, by rw [← sa.mem]; exact O, (sa.keeps _).trans K⟩
  | true =>
    refine WP.ite false (by simp [eval, za']) (fun e => Bool.noConfusion e) (fun _ => ?_)
    refine WP.seq (WP.mono (primeUniformUpdate_ok (isUniform := isUniform) (uniform := uniform) Sa room bound checks32
      (by rw [sa.mem, flag]) (by rw [sa.mem, count])) fun b ⟨cb, cf, Ob, Kb⟩ => ?_)
    have Sb := Sa.of_keeps Kb (by decide)
    have done {status : Nat} (hs : primeResultStatus true (uniform + isUniform.toNat) checks = status) :
        WP isa (.block (primeMark status)) b fun t =>
          t.mem.readW (off base primeStatus) 32 = BitVec.ofNat 32 (primeResultStatus true (uniform + isUniform.toNat) checks) ∧
          t.mem.readW (off base primeUniform) 32 = BitVec.ofNat 32 (uniform + isUniform.toNat) ∧
          Outs base [(primeUniform, 4), (primeStatus, 4)] s.mem t.mem ∧ Keeps [.eax, .ecx] s t := by
      refine WP.mono (finish Sb cb) fun t ⟨st, cu, O, K⟩ => ?_
      refine ⟨by rw [hs]; exact st, cu, ?_, ((sa.keeps _).trans Kb).trans K⟩
      rw [← sa.mem]
      exact (Outs.of_outside Ob (by simp)).trans O
    by_cases enough : uniform + isUniform.toNat < checks
    · refine WP.ite false (by simp [eval, cf, enough]) (fun e => Bool.noConfusion e) (fun _ => ?_)
      exact done (by simp [primeResultStatus, enough])
    · refine WP.ite true (by simp [eval, cf, enough]) (fun _ => ?_) (fun e => Bool.noConfusion e)
      exact done (by simp [primeResultStatus, enough])
end VG.Proof.Dsa.X86.Generation
