import VerifiedGarbage.Proof.P256.EcdhInverse.Packed
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvBatchStart
import VerifiedGarbage.Proof.Weierstrass.AArch64.AllocatedFrame

namespace VG.Proof.P256.EcdhInverse
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps)

def batchRegs : List Reg := .x19::(allocatedRegs.filter (· != .x20))

theorem words_ok {base : Addr} {s : State} (hs : Scr s base 8192)
    {I : Divstep.IState} (hI : IInv p256.invP base I s) (hd : |I.d|≤2^30) (hf1 : I.f%2=1)
    (hz : s.gpr .x27=0) {j : Nat} (hj : 1≤j) (hj' : j<2^64)
    (h19 : s.gpr .x19=BitVec.ofNat 64 j) :
    WP isa (.block p256.invP.batchStart) s fun s₁ =>
      WP isa (.block Impl.P256.EcdhInverse.packed) s₁ fun t =>
      let m:=Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)
      t.gpr .x1=BitVec.ofInt 64 m.d ∧ t.gpr .x4=BitVec.ofInt 64 m.u ∧
      t.gpr .x5=BitVec.ofInt 64 m.v ∧ t.gpr .x6=BitVec.ofInt 64 m.q ∧ t.gpr .x7=BitVec.ofInt 64 m.r ∧
      t.gpr .x19=BitVec.ofNat 64 (j-1) ∧ t.mem=s.mem ∧ KeepRegs batchRegs s t ∧ t.gpr .x27=0 := by
  refine WP.mono (batchStart_ok hs (P:=p256.invP) (by decide) (by decide) (by decide) (by decide) hj hj' h19)
    fun s₁ ⟨c19,c11,c12,c2,c3,c4,c5,c6,c7,m₁,k₁⟩ => ?_
  have low (a : Nat) (x : Int)
      (h : (wordsVal s.mem base a p256.invP.L : Int)%((2^(64*p256.invP.L):Nat):Int)=x%((2^(64*p256.invP.L):Nat):Int)) :
      word s.mem base a=BitVec.ofInt 64 x := by
    have hc := congrArg (fun z : Int => z%2^64) h
    have hdvd : (2:Int)^64 ∣ ((2^(64*p256.invP.L):Nat):Int) := by
      rw [Nat.cast_pow,Nat.cast_ofNat]; exact pow_dvd_pow 2 (by decide)
    simp only [Int.emod_emod_of_dvd _ hdvd] at hc
    have low : (wordsVal s.mem base a p256.invP.L : Int)%2^64=((word s.mem base a).toNat:Int) := by
      simp only [show p256.invP.L=5 from rfl,wordsVal]
      push_cast
      rw [Int.add_mul_emod_self_left]
      exact Int.emod_eq_of_lt (by omega) (by have := (word s.mem base a).isLt; omega)
    rw [low] at hc
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofInt]
    omega
  refine WP.mono (packed_ok s₁ I.d I.f I.g
    (by rw [k₁.gpr _ (by decide)]; exact hI.d)
    (by rw [c2]; exact low _ _ hI.f) (by rw [c3]; exact low _ _ hI.g)
    (by rw [k₁.gpr _ (by decide)]; exact hz) hf1 (by omega))
    fun t ⟨d,u,v,q,r,hk⟩ => ?_
  exact ⟨d,u,v,q,r,by rw [hk.gpr _ (by decide),c19],by rw [hk.mem,m₁],
    (k₁.mono (by decide)).trans ((VG.Proof.Mont.AArch64.Keeps.regs hk).mono (by decide)),
    by rw [hk.gpr _ (by decide),k₁.gpr _ (by decide),hz]⟩
end VG.Proof.P256.EcdhInverse
