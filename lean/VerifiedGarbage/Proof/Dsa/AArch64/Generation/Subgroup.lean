module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SubgroupState
import VerifiedGarbage.Proof.Framework.Omega

/-! # Complete native subgroup-candidate generation and primality testing -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Proof.RsaOaep.AArch64
open VG.Proof.MillerRabin.AArch64 VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Impl.Bignum.AArch64 (seqs)

theorem subgroup_ok {G1 G256 : Impl.Pbkdf2.Md.AArch64.Hash}
    (h1 : Pbkdf2.Md.AArch64.Calls.StreamOK G1.stream) (h256 : Pbkdf2.Md.AArch64.Calls.StreamOK G256.stream)
    (he1 : ∀ x, Spec.Mgf1.sha1.hash x = h1.SH.H.hash x)
    (he256 : ∀ x, Spec.Mgf1.sha256.hash x = h256.SH.H.hash x)
    (hs1 : ∀ x, (Spec.Mgf1.sha1.hash x).length = G1.D)
    (hs256 : ∀ x, (Spec.Mgf1.sha256.hash x).length = G256.D)
    (hd1 : G1.D = 20) (hd256 : G256.D = 32) (M : Mont) (K : Kernel)
    {p : SubgroupPlan} {used : Nat} {s : State} (h : SubgroupState p used s) :
    WP isa (Impl.Dsa.AArch64.Generation.subgroup G1 G256 M.mm K.run p.prime.len) s fun t =>
      let res := Spec.Dsa.probablePrime p.prime.N (p.prime.rand.drop used)
      ∃ used' status V', used' ≤ p.prime.rand.length ∧
        Lay t p.F p.hash ∧
        Rep t.mem p.F p.hash V' (upd (upd p.W 16 (BitVec.ofNat 64 used')) 19 status) ∧
        Spec.Rsa.bytesAt t.mem p.output p.prime.len = Spec.Dsa.encodeBE p.prime.len p.prime.N ∧
        (res = none → status = BitVec.ofNat 64 0) ∧
        (∀ b rest, res = some (b, rest) → status = BitVec.ofNat 64 (if b then 1 else 3) ∧
          used' = p.prime.rand.length - rest.length) ∧
        Frame p.changed s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain ⟨V, R⟩ := h.rep
  have plen : p.prime.len ≤ 32 := by rcases p.width with hh | hh <;> omega
  unfold Impl.Dsa.AArch64.Generation.subgroup
  simp only [seqs]
  refine WP.seq (WP.mono (qBuild_ok h1 h256 he1 he256 hs1 hs256 hd1 hd256 p.width
    h.layout R h.label p.outputSlot h.outputWrite p.outputFrame.symm p.outputScratch)
    fun u ⟨uq, stepU, fu, Lu, Vu, Ru⟩ => ?_)
  have urd := stepU.rd
  have uwr := stepU.wr
  have ubytes : Spec.Rsa.bytesAt u.mem p.output p.prime.len = Spec.Dsa.encodeBE p.prime.len p.prime.N := by
    rw [uq, h.seed, ← p.modulus]
  refine WP.seq (WP.mono (workspaceBase_ok Lu Ru p.base) fun v ⟨hdi, hm, kv⟩ => ?_)
  have Rv : Rep v.mem p.F p.hash Vu p.W := hm ▸ Ru
  have tapeU := source_of_frame h.tape fu p.tapeHash p.prime.randMax urd uwr
  have tapeV := tapeU.congrK (fun a _ => by rw [hm]) kv
  let bs := Spec.Rsa.bytesAt v.mem p.output p.prime.len
  have blen : bs.length = p.prime.len := bytesAt_length _ _ _
  have bval : Spec.Rsa.os2ip bs = p.prime.N := by
    dsimp only [bs]
    rw [hm, ubytes]
    exact p.encoding
  have src : Src v p.prime.B p.prime.Z (p.W 5 + BitVec.ofNat 64 Impl.Dsa.Generation.Layout.q) bs := by
    rw [p.outputPtr]
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      rw [blen] at hi
      have hw : InRegions v.wr (VG.Proof.Bignum.off p.output i) 1 := by rw [kv.wr, uwr]; exact h.outputWrite i hi
      obtain ⟨r, hr, hc⟩ := hw
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    · intro i hi
      simp [bs, Spec.Rsa.bytesAt]
    · intro i hi; exact p.outputOutside i (blen ▸ hi)
  have hw48 : p.prime.w ≤ 48 := by rw [p.words]; decide
  have hpolicy : 1024 < Spec.Dsa.bitLength p.prime.N ↔ 16 < p.prime.w := by
    rw [p.bits, p.words]
    rcases p.width with hh | hh <;> rw [hh] <;> decide
  have hchecks : p.prime.checks = Spec.Dsa.primeChecks (Spec.Dsa.bitLength p.prime.N) := by
    rw [p.checks, p.bits]
    rcases p.width with hh | hh <;> rw [hh] <;> decide
  have hcode : Impl.Dsa.AArch64.Generation.checkPrime M.mm K.run 4 Impl.Dsa.Generation.Layout.q
      p.prime.len (if p.prime.len = 20 then 24 else 32) 64 =
      Impl.Dsa.AArch64.Generation.checkPrime M.mm K.run p.prime.w Impl.Dsa.Generation.Layout.q
        p.prime.len p.prime.drawBytes p.prime.checks := by
    rw [p.words, p.draw, p.checks]
  rw [hcode]
  refine WP.seq (WP.mono (checkPrime_ok M K (h.scratch.congr (kv.wr.trans uwr)) hdi
    (by decide : Impl.Dsa.Generation.Layout.q < 2 ^ 16) (by rw [p.checks]; decide)
    (kv.sp.trans Lu.sp)
    (fun k hk => by rw [kv.rd, kv.wr]; exact Lu.ld (d := 8 * k) (n := 8) (by unfold frameBytes; omega))
    (fun k hk => Rv.fr k (by change k < 34; exact hk)) p.frameHeaders p.frameOutside
    p.witnessPtr p.tapePtr p.tapeLength h.usedSlot tapeV
    (fun i hi => by rw [kv.wr, uwr]; exact h.witnessWrite i hi) blen bval src h.usedBound hw48
    (by rw [p.words, p.size]; decide) p.large hpolicy hchecks)
    fun z ⟨used', hz, huz, he, hres, fz, kz⟩ => ?_)
  have fg : Frame p.primeWrites v.mem z.mem := prime_global_frame fz (checkPrimeRanges_bound hw48)
  have Rz := rep_of_disjoint_frame Rv fg p.framePrime p.hashPrime
  have Lz := lay_of_rep Lu Ru Rz rfl (kz.sp.trans kv.sp) (kz.wr.trans kv.wr)
  have zbytes : Spec.Rsa.bytesAt z.mem p.output p.prime.len = Spec.Dsa.encodeBE p.prime.len p.prime.N := by
    rw [VG.Proof.Dsa.Generation.frame_bytesAt fg p.outputPrime (by omega), hm, ubytes]
  refine WP.mono (primeResult_ok Lz Rz hz.ws.x0
    (hz.ws.scr.ld (d := 216) (by have := hz.ws.h256; omega))
    (hz.ws.scr.ld (d := 248) (by have := hz.ws.h256; omega)) hz.used
    (show VG.Proof.Bignum.word z.mem p.prime.B 248 = VG.Proof.Bignum.word z.mem p.prime.B 248 from rfl)
    (fun a ha hb => p.frameHeaders 16 (by decide) 31 (by decide) a hb ha))
    fun t ⟨Lt, Rt, ft, kt⟩ => ?_
  have ff : Frame [⟨p.F, frameBytes⟩] z.mem t.mem := by
    intro a ha
    apply ft a
    right
    have hn := ha ⟨p.F, frameBytes⟩ (by simp)
    change ¬ ofs p.F a < frameBytes at hn
    unfold frameBytes at hn
    omega
  refine ⟨used', VG.Proof.Bignum.word z.mem p.prime.B 248, Vu, huz, Lt, Rt, ?_, he, hres, ?_,
    kt.rd.trans (kz.rd.trans (kv.rd.trans urd)), kt.wr.trans (kz.wr.trans (kv.wr.trans uwr))⟩
  · rw [VG.Proof.Dsa.Generation.frame_bytesAt ff (by
      intro r hr; rcases List.mem_singleton.mp hr with rfl; exact p.outputFrame) (by omega), zbytes]
  · have fu' : Frame p.hashWrites s.mem v.mem := by rw [hm]; exact fu
    exact ((fu'.mono (by intro r hr; simp [SubgroupPlan.changed, hr])).trans
      (fg.mono (by intro r hr; simp [SubgroupPlan.changed, hr]))).trans (ff.mono (by simp [SubgroupPlan.changed]))

end VG.Proof.Dsa.AArch64.Generation
