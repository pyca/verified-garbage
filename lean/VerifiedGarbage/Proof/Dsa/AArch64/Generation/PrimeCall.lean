module
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeState
public import VerifiedGarbage.Proof.Dsa.AArch64.Run
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Kernel
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Arguments
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CheckPrime
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeFootprint
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeResult
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Memory

/-! # Complete primality call returning its cursor and status to the generation frame -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Proof.RsaOaep.AArch64
open VG.Proof.MillerRabin.AArch64 VG.Impl.RsaKeyGen.AArch64.Candidate

structure PrimeCallPlan where
  prime : PrimeParams
  F : Addr
  hash : Addr
  candidate : Nat
  W : Nat → BitVec 64
  size : prime.Z = Impl.Dsa.Generation.Layout.arithmeticBytes
  candidateMax : candidate < 2 ^ 16
  checksMax : prime.checks < 2 ^ 16
  wordsMax : prime.w ≤ 48
  tableRoom : VG.Proof.Bignum.slot prime.w aTab + 2048 ≤ prime.Z
  large : 8161 < prime.N
  policy : 1024 < Spec.Dsa.bitLength prime.N ↔ 16 < prime.w
  checks : prime.checks = Spec.Dsa.primeChecks (Spec.Dsa.bitLength prime.N)
  witnessPtr : W 5 + BitVec.ofNat 64 Impl.Dsa.Generation.Layout.witness = prime.p
  tapePtr : W 14 = prime.rp
  tapeLength : W 15 = BitVec.ofNat 64 prime.rand.length
  frameHeaders : ∀ k < 34, ∀ j < 32,
    Mem.Sep (VG.Proof.Bignum.off F (8 * k)) 8 (VG.Proof.Bignum.off prime.B (8 * j)) 8
  frameOutside : ∀ k < 34, ∀ i < 8, prime.Z ≤ ofs prime.B (VG.Proof.Bignum.off (VG.Proof.Bignum.off F (8 * k)) i)
  framePrime : ∀ r ∈ [⟨prime.B, Impl.Dsa.Generation.Layout.arithmeticBytes⟩,
      ⟨prime.p, prime.len⟩], (⟨F, frameBytes⟩ : Region).Disjoint r
  hashPrime : ∀ r ∈ [⟨prime.B, Impl.Dsa.Generation.Layout.arithmeticBytes⟩,
      ⟨prime.p, prime.len⟩], (⟨hash, oRsa⟩ : Region).Disjoint r

def PrimeCallPlan.changed (p : PrimeCallPlan) : List Region :=
  [⟨p.prime.B, Impl.Dsa.Generation.Layout.arithmeticBytes⟩,
    ⟨p.prime.p, p.prime.len⟩, ⟨p.F, frameBytes⟩]

theorem primeCall_ok (M : Mont) (K : Kernel) {p : PrimeCallPlan} {used : Nat} {s : State}
    {V : Nat → Byte} {bs : List Byte}
    (L : Lay s p.F p.hash) (R : Rep s.mem p.F p.hash V p.W)
    (hS : Scr s p.prime.B p.prime.Z) (hdi : s.gpr .x0 = p.prime.B)
    (hused : p.W 16 = BitVec.ofNat 64 used) (hu : used ≤ p.prime.rand.length)
    (htape : Src s p.prime.B p.prime.Z p.prime.rp p.prime.rand)
    (hout : ∀ i < p.prime.len, InRegions s.wr (VG.Proof.Bignum.off p.prime.p i) 1)
    (hlen : bs.length = p.prime.len) (hvalue : Spec.Rsa.os2ip bs = p.prime.N)
    (hsrc : Src s p.prime.B p.prime.Z (p.W 5 + BitVec.ofNat 64 p.candidate) bs) :
    WP isa (.seq (Impl.Dsa.AArch64.Generation.checkPrime M.mm K.run p.prime.w
      p.candidate p.prime.len p.prime.drawBytes p.prime.checks)
      (.block Impl.Dsa.AArch64.Generation.primeResult)) s fun t =>
      let res := Spec.Dsa.probablePrime p.prime.N (p.prime.rand.drop used)
      ∃ used' status, used' ≤ p.prime.rand.length ∧ Lay t p.F p.hash ∧
        Rep t.mem p.F p.hash V (upd (upd p.W 16 (BitVec.ofNat 64 used')) 19 status) ∧
        (res = none → status = BitVec.ofNat 64 0) ∧
        (∀ b rest, res = some (b, rest) → status = BitVec.ofNat 64 (if b then 1 else 3) ∧
          used' = p.prime.rand.length - rest.length) ∧
        Frame p.changed s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  refine WP.seq (WP.mono (checkPrime_ok M K hS hdi p.candidateMax p.checksMax L.sp
    (fun k hk => L.ld (d := 8 * k) (n := 8) (by unfold frameBytes; omega)) (fun k hk => R.fr k hk)
    p.frameHeaders p.frameOutside p.witnessPtr p.tapePtr p.tapeLength hused htape hout
    hlen hvalue hsrc hu p.wordsMax p.tableRoom p.large p.policy p.checks)
    fun u ⟨used', hu, hbound, he, hr, fu, ku⟩ => ?_)
  have fg : Frame [⟨p.prime.B, Impl.Dsa.Generation.Layout.arithmeticBytes⟩,
      ⟨p.prime.p, p.prime.len⟩] s.mem u.mem :=
    prime_global_frame fu (checkPrimeRanges_bound p.wordsMax)
  have Ru := rep_of_disjoint_frame R fg p.framePrime p.hashPrime
  have Lu := lay_of_rep L R Ru rfl ku.sp ku.wr
  refine WP.mono (primeResult_ok Lu Ru hu.ws.x0
    (hu.ws.scr.ld (d := 216) (by have := hu.ws.h256; omega))
    (hu.ws.scr.ld (d := 248) (by have := hu.ws.h256; omega)) hu.used rfl
    (fun a ha hb => p.frameHeaders 16 (by decide) 31 (by decide) a hb ha))
    fun t ⟨Lt, Rt, ft, kt⟩ => ?_
  refine ⟨used', VG.Proof.Bignum.word u.mem p.prime.B 248, hbound, Lt, Rt, he, hr, ?_,
    kt.rd.trans ku.rd, kt.wr.trans ku.wr⟩
  have ff : Frame p.changed u.mem t.mem := by
    intro a ha
    apply ft a
    right
    have hn := ha ⟨p.F, frameBytes⟩ (by simp [PrimeCallPlan.changed])
    change ¬ ofs p.F a < frameBytes at hn
    unfold frameBytes at hn
    omega
  exact (fg.mono (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp [PrimeCallPlan.changed])).trans ff

end VG.Proof.Dsa.AArch64.Generation
