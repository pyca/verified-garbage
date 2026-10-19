module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeCall
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PAttempt
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateWidth
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Memory

/-! # A full-width p candidate enters the complete shared primality routine -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.Rsa.AArch64 VG.Proof.RsaOaep.AArch64 VG.Proof.MillerRabin.AArch64

theorem pTest_full_ok (M : Mont) (K : Kernel) {p : PrimeCallPlan} {used : Nat} {s : State}
    {V : Nat → Byte} {bs : List Byte} {pp : Addr}
    (L : Lay s p.F p.hash) (R : Rep s.mem p.F p.hash V p.W)
    (h : Ws s p.prime.B p.prime.Z p.prime.w)
    (hptr : VG.Proof.Bignum.word s.mem p.prime.B 160 = pp)
    (hbound : p.prime.N < 256 ^ p.prime.len)
    (hbytes : Spec.Rsa.bytesAt s.mem pp p.prime.len = Spec.Dsa.encodeBE p.prime.len p.prime.N)
    (hrd : InRegions (s.rd ++ s.wr) pp 1) (hfull : ¬ p.prime.N < 2 ^ (8 * p.prime.len - 1))
    (hwords : p.prime.w = p.prime.len / 8) (hdraw : p.prime.drawBytes = p.prime.len)
    (hchecks : p.prime.checks = if p.prime.len ≤ 256 then 64 else 128)
    (hcandidate : p.candidate = Impl.Dsa.Generation.Layout.p)
    (hused : p.W 16 = BitVec.ofNat 64 used) (hu : used ≤ p.prime.rand.length)
    (htape : Src s p.prime.B p.prime.Z p.prime.rp p.prime.rand)
    (hout : ∀ i < p.prime.len, InRegions s.wr (VG.Proof.Bignum.off p.prime.p i) 1)
    (hlen : bs.length = p.prime.len) (hvalue : Spec.Rsa.os2ip bs = p.prime.N)
    (hsrc : Src s p.prime.B p.prime.Z (p.W 5 + BitVec.ofNat 64 p.candidate) bs) :
    WP isa (Impl.Dsa.AArch64.Generation.pTest M.mm K.run p.prime.len) s fun t =>
      let res := Spec.Dsa.probablePrime p.prime.N (p.prime.rand.drop used)
      ∃ used' status, used' ≤ p.prime.rand.length ∧ Lay t p.F p.hash ∧
        Rep t.mem p.F p.hash V (upd (upd p.W 16 (BitVec.ofNat 64 used')) 19 status) ∧
        (res = none → status = BitVec.ofNat 64 0) ∧
        (∀ b rest, res = some (b, rest) → status = BitVec.ofNat 64 (if b then 1 else 3) ∧
          used' = p.prime.rand.length - rest.length) ∧
        Frame p.changed s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  unfold Impl.Dsa.AArch64.Generation.pTest
  refine WP.seq (WP.mono (candidateWidth_ok h hptr (by have := p.prime.len2; omega)
    hbound hbytes hrd) fun u ⟨hcf, hm, ku⟩ => ?_)
  have Ru : Rep u.mem p.F p.hash V p.W := hm ▸ R
  have Lu := lay_of_rep L R Ru rfl ku.sp ku.wr
  refine WP.ite false (by simp [hcf, hfull]) (fun he => Bool.noConfusion he) (fun _ => ?_)
  have hcode : Impl.Dsa.AArch64.Generation.checkPrime M.mm K.run (p.prime.len / 8)
      Impl.Dsa.Generation.Layout.p p.prime.len p.prime.len (if p.prime.len ≤ 256 then 64 else 128) =
      Impl.Dsa.AArch64.Generation.checkPrime M.mm K.run p.prime.w p.candidate p.prime.len
        p.prime.drawBytes p.prime.checks := by rw [hwords, hdraw, hchecks, hcandidate]
  rw [hcode]
  refine WP.mono (primeCall_ok M K Lu Ru (h.scr.congr ku.wr)
    ((ku.gpr _ (by decide)).trans h.x0) hused hu
    (htape.congrK (fun a _ => by rw [hm]) ku)
    (fun i hi => by rw [ku.wr]; exact hout i hi) hlen hvalue
    (hsrc.congrK (fun a _ => by rw [hm]) ku))
    fun t ⟨used', status, hb, Lt, Rt, he, hr, ft, rdt, wrt⟩ => ?_
  exact ⟨used', status, hb, Lt, Rt, he, hr, hm ▸ ft, rdt.trans ku.rd, wrt.trans ku.wr⟩

end VG.Proof.Dsa.AArch64.Generation
