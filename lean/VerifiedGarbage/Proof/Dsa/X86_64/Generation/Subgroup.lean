module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SubgroupState
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Subgroup
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Kernel
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.WorkspaceBase
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeResult
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeFootprint
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CheckPrime
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.QBuild
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SourceFrame
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Bignum.Octets

/-! # Complete native subgroup-candidate generation and primality testing -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.RsaOaep.X86_64 VG.Proof.RsaOaep.X86_64
open VG.Proof.MillerRabin.X86_64 VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Impl.Bignum.X86_64 (seqs)

theorem subgroup_ok {G1 G256 : Impl.Pbkdf2.Md.X86_64.Stream}
    (h1 : Pbkdf2.Md.X86_64.Calls.StreamOK G1) (h256 : Pbkdf2.Md.X86_64.Calls.StreamOK G256)
    (he1 : ∀ x, Spec.Mgf1.sha1.hash x = h1.SH.H.hash x)
    (he256 : ∀ x, Spec.Mgf1.sha256.hash x = h256.SH.H.hash x)
    (hs1 : ∀ x, (Spec.Mgf1.sha1.hash x).length = G1.D)
    (hs256 : ∀ x, (Spec.Mgf1.sha256.hash x).length = G256.D)
    (hd1 : G1.D = 20) (hd256 : G256.D = 32) (M : Mont) (K : Kernel)
    {p : SubgroupPlan} {used : Nat} {s : State} (h : SubgroupState p used s) :
    WP isa (Impl.Dsa.X86_64.Generation.subgroup G1 G256 M.mm K.run p.prime.len) s fun t =>
      let res := Spec.Dsa.probablePrime p.prime.N (p.prime.rand.drop used)
      ∃ used' status V', used' ≤ p.prime.rand.length ∧
        Lay t p.prime.sp p.hash ∧
        Rep t.mem p.prime.sp p.hash V' (upd (upd p.W 16 (BitVec.ofNat 64 used')) 19 status) ∧
        Spec.Rsa.bytesAt t.mem p.output p.prime.len = Spec.Dsa.encodeBE p.prime.len p.prime.N ∧
        (res = none → status = BitVec.ofNat 64 0) ∧
        (∀ b rest, res = some (b, rest) → status = BitVec.ofNat 64 (if b then 1 else 3) ∧
          used' = p.prime.rand.length - rest.length) ∧
        Frame p.changed s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain ⟨V, R⟩ := h.rep
  have plen : p.prime.len ≤ 32 := by rcases p.width with hh | hh <;> omega
  unfold Impl.Dsa.X86_64.Generation.subgroup
  simp only [seqs]
  refine WP.seq (WP.mono (qCandidate_ok h1 h256 he1 he256 hs1 hs256 hd1 hd256 p.width
    h.layout R h.label p.outputSlot h.outputWrite (fun i hi j hj => ?_) p.outputHash)
    fun u ⟨uq, urd, uwr, _, fu, Lu, Vu, Ru⟩ => ?_)
  · have he := p.outputHash.scratch j hj (oDig + i) (by unfold oDig oRsa; omega)
    simpa only [off_off] using Ne.symm he
  have ubytes : Spec.Rsa.bytesAt u.mem p.output p.prime.len = Spec.Dsa.encodeBE p.prime.len p.prime.N := by
    rw [uq, h.seed, ← p.modulus]
  refine WP.seq (WP.mono (workspaceBase_ok Lu Ru p.base) fun v ⟨hdi, hm, kv⟩ => ?_)
  have Rv : Rep v.mem p.prime.sp p.hash Vu p.W := hm ▸ Ru
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
      have hw : InRegions v.wr (off p.output i) 1 := by rw [kv.2.2, uwr]; exact h.outputWrite i hi
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
  have hcode : Impl.Dsa.X86_64.Generation.checkPrime M.mm K.run 4 Impl.Dsa.Generation.Layout.q
      p.prime.len (if p.prime.len = 20 then 24 else 32) 64 =
      Impl.Dsa.X86_64.Generation.checkPrime M.mm K.run p.prime.w Impl.Dsa.Generation.Layout.q
        p.prime.len p.prime.drawBytes p.prime.checks := by
    rw [p.words, p.draw, p.checks]
  rw [hcode]
  refine WP.seq (WP.mono (checkPrime_ok M K (h.scratch.congr (kv.2.2.trans uwr)) hdi
    (by decide : Impl.Dsa.Generation.Layout.q < 2 ^ 31) (by rw [p.checks]; decide)
    ((kv.gpr (by decide)).trans Lu.rsp)
    (fun k hk => by rw [kv.2.1, kv.2.2]; exact Lu.ld (by unfold frameBytes; omega))
    (fun k hk => Rv.fr k (by change k < 37; exact hk)) p.frameHeaders p.frameOutside
    p.witnessPtr p.tapePtr p.tapeLength h.usedSlot tapeV
    (fun i hi => by rw [kv.2.2, uwr]; exact h.witnessWrite i hi) blen bval src h.usedBound hw48
    (by rw [p.words, p.size]; decide) p.large hpolicy hchecks)
    fun z ⟨mi', used', hz, huz, he, hres, fz, kz⟩ => ?_)
  have fg : Frame p.primeWrites v.mem z.mem := prime_global_frame fz (checkPrimeRanges_bound hw48)
  have Rz := rep_of_disjoint_frame Rv fg p.framePrime p.hashPrime
  have Lz := lay_of_rep Lu Ru Rz rfl ((kz.gpr (by decide)).trans (kv.gpr (by decide))) (kz.2.2.trans kv.2.2)
  have zbytes : Spec.Rsa.bytesAt z.mem p.output p.prime.len = Spec.Dsa.encodeBE p.prime.len p.prime.N := by
    rw [VG.Proof.Dsa.Generation.frame_bytesAt fg p.outputPrime (by omega), hm, ubytes]
  refine WP.mono (primeResult_ok Lz Rz hz.good.rdi
    (hz.good.scr.ld (d := 200) (by have := p.prime.z256; omega))
    (hz.good.scr.ld (d := 232) (by have := p.prime.z256; omega)) hz.used
    (show word z.mem p.prime.B 232 = word z.mem p.prime.B 232 from rfl)
    (fun a ha hb => p.frameHeaders 16 (by decide) 29 (by decide) a hb ha))
    fun t ⟨Lt, Rt, ft, kt⟩ => ?_
  have ff : Frame [⟨p.prime.sp, frameBytes⟩] z.mem t.mem := by
    intro a ha
    apply ft a
    right
    have hn := ha ⟨p.prime.sp, frameBytes⟩ (by simp)
    change ¬ ofs p.prime.sp a < frameBytes at hn
    unfold frameBytes at hn
    omega
  refine ⟨used', word z.mem p.prime.B 232, Vu, huz, Lt, Rt, ?_, he, hres, ?_,
    kt.2.1.trans (kz.2.1.trans (kv.2.1.trans urd)), kt.2.2.trans (kz.2.2.trans (kv.2.2.trans uwr))⟩
  · rw [VG.Proof.Dsa.Generation.frame_bytesAt ff (by
      intro r hr; rcases List.mem_singleton.mp hr with rfl; exact p.outputFrame) (by omega), zbytes]
  · have fu' : Frame p.hashWrites s.mem v.mem := by rw [hm]; exact fu
    exact ((fu'.mono (by intro r hr; simp [SubgroupPlan.changed, hr])).trans
      (fg.mono (by intro r hr; simp [SubgroupPlan.changed, hr]))).trans (ff.mono (by simp [SubgroupPlan.changed]))

end VG.Proof.Dsa.X86_64.Generation
