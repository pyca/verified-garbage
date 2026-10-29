module

public import VerifiedGarbage.Proof.Dsa.Generation.SeedResult
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedOutcome
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.SeedSearch
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Hashes

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedSubgroup
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSuccess
import VerifiedGarbage.Proof.Dsa.Generation.RandomSuffix
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedPack
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedValidate
import VerifiedGarbage.Proof.Dsa.Generation.ParamsEncoding
import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Context
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Spec.Ffdh
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedGenerator
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedPrime
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import Mathlib.Algebra.Group.Nat.Defs
/-! # A complete native seed attempt implements all parameter-generation decisions -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/FinishDomain.lean`, which only this module imported.
section

/-! # Packing and final validation implement the last seed-acceptance decision -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout


variable {checkName : String}

theorem finishDomain_ok (M : Mont) (Sq : MontS)
    {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (a : Spec.Dsa.Params)
    (hp : a.p < 256 ^ p.geo.pLen) (hq : a.q < 256 ^ p.geo.qLen) (hg : a.g < 256 ^ p.geo.pLen)
    (bp : Spec.Rsa.bytesAt s.mem (off p.geo.B VG.Impl.Dsa.Generation.Layout.p) p.geo.pLen = Spec.Dsa.encodeBE p.geo.pLen a.p)
    (bq : Spec.Rsa.bytesAt s.mem (off p.geo.B q) p.geo.qLen = Spec.Dsa.encodeBE p.geo.qLen a.q)
    (bg : Spec.Rsa.bytesAt s.mem (off p.geo.B g) p.geo.pLen = Spec.Dsa.encodeBE p.geo.pLen a.g) :
    WP isa (Impl.Dsa.X86_64.Generation.finishDomain (checkName := checkName) Sq.mm M.mm p.geo.pLen p.geo.qLen) s fun t =>
      GenerationMemory p (upd W 19 (BitVec.ofNat 64 (if Spec.Dsa.parametersValid a then 1 else 3))) t ∧
      Spec.Rsa.bytesAt t.mem (off p.geo.B packed) (2 * p.geo.pLen + p.geo.qLen) = Spec.Dsa.encodeParams p.geo.pLen p.geo.qLen a ∧
      Frame p.changed s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  unfold Impl.Dsa.X86_64.Generation.finishDomain
  refine WP.seq (WP.mono (seedPack_ok h _ _ _ (VG.Proof.Dsa.encodeBE_length _ _)
    (VG.Proof.Dsa.encodeBE_length _ _) (VG.Proof.Dsa.encodeBE_length _ _) bp bq bg)
    fun u ⟨hu, bytes, fu, ru, wu⟩ => ?_)
  have check := VG.Proof.Dsa.Generation.check_encodedParams p.geo.validLengths hp hq hg
  have call := seedValidate_ok (checkName := checkName) M Sq hu (Spec.Dsa.encodeParams p.geo.pLen p.geo.qLen a)
    (VG.Proof.Dsa.Generation.encodeParams_length _ _ _) bytes
  rw [check] at call
  simp only [decide_eq_true_eq] at call
  refine WP.mono call fun t ⟨ht, bt, ft, rt, wt⟩ => ?_
  exact ⟨ht, bt, fu.trans ft, rt.trans ru, wt.trans wu⟩

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/SeedGeneratorFinish.lean`, which only this module imported.
section

/-! # Generator selection and final validation produce one complete seed result -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout


variable {checkName : String}

theorem seedGeneratorFinish_ok (M : Mont) (Sq : MontS)
    {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (value qval : Nat)
    (domain : VG.Proof.Dsa.Generation.PDomain p.geo.pLen value) (qfit : qval < 256 ^ p.geo.qLen)
    (bp : Spec.Rsa.bytesAt s.mem (off p.geo.B VG.Impl.Dsa.Generation.Layout.p) p.geo.pLen = Spec.Dsa.encodeBE p.geo.pLen value)
    (be : Spec.Rsa.bytesAt s.mem (off p.geo.B exponent) p.geo.pLen = Spec.Dsa.encodeBE p.geo.pLen ((value - 1) / qval))
    (bq : Spec.Rsa.bytesAt s.mem (off p.geo.B q) p.geo.qLen = Spec.Dsa.encodeBE p.geo.qLen qval)
    {used : Nat} (h16 : W 16 = BitVec.ofNat 64 used) (hu : used ≤ p.rand.bytes.length) :
    WP isa (.seq (Impl.Dsa.X86_64.Generation.generatorSearch Sq.mm M.mm p.geo.pLen)
      (Impl.Dsa.X86_64.Generation.onSuccess (Impl.Dsa.X86_64.Generation.finishDomain (checkName := checkName) Sq.mm M.mm p.geo.pLen p.geo.qLen))) s
      (SeedFinished p W (VG.Proof.Dsa.Generation.generatorResult value qval
        ((Spec.Dsa.generationChunks p.geo.pLen p.hs.bytes).map Spec.Dsa.decodeBE) (p.rand.bytes.drop used)) s) := by
  have pfit : value < 256 ^ p.geo.pLen := by
    simpa only [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul] using domain.upper
  refine WP.seq (WP.mono (seedGenerator_ok M Sq h value qval domain bp be bq)
    fun u ⟨Wu, mu, slots, bpu, bqu, result, fu, ru, wu⟩ => ?_)
  have u16 : Wu 16 = BitVec.ofNat 64 used := (slots 16 (by simp [generatorSlots])).trans h16
  have uslots : ∀ k ∈ searchSlots, Wu k = W k := fun k hk => slots k (searchSlots_generator hk)
  rcases result with ⟨h19, hr⟩ | ⟨gv, h19, hr, _, upper, bgu⟩
  · apply onSuccess_generation_ok mu
    · intro t _ _ _ hs
      have impossible : (3 : BitVec 64) = 1 := h19.symm.trans hs
      exact False.elim (by cases impossible)
    · intro t mt hm kt _
      refine ⟨Wu, used, mt, hu, u16, uslots, Or.inr (Or.inl ⟨h19, ?_⟩), ?_, kt.2.1.trans ru, kt.2.2.trans wu⟩
      · simp only [VG.Proof.Dsa.Generation.generatorResult, hr]
      · rw [hm]; exact fu
  · apply onSuccess_generation_ok mu
    · intro v mv hm kv _
      have pv : Spec.Rsa.bytesAt v.mem (off p.geo.B VG.Impl.Dsa.Generation.Layout.p) p.geo.pLen = Spec.Dsa.encodeBE p.geo.pLen value := hm ▸ bpu
      have qv : Spec.Rsa.bytesAt v.mem (off p.geo.B q) p.geo.qLen = Spec.Dsa.encodeBE p.geo.qLen qval := hm ▸ bqu
      have gvbytes : Spec.Rsa.bytesAt v.mem (off p.geo.B g) p.geo.pLen = Spec.Dsa.encodeBE p.geo.pLen gv := hm ▸ bgu
      refine WP.mono (finishDomain_ok (checkName := checkName) M Sq mv ⟨value, qval, gv⟩ pfit qfit (Nat.lt_trans upper pfit) pv qv gvbytes)
        fun t ⟨mt, bytes, ft, rt, wt⟩ => ?_
      refine ⟨_, used, mt, hu, ?_, ?_, ?_, ?_, rt.trans (kv.2.1.trans ru), wt.trans (kv.2.2.trans wu)⟩
      · simpa [upd] using u16
      · intro k hk
        simpa [upd, searchSlots_not_status hk] using uslots k hk
      · by_cases valid : Spec.Dsa.parametersValid ⟨value, qval, gv⟩
        · refine Or.inr (Or.inr ⟨by simp [upd, valid], ⟨value, qval, gv⟩, ?_, bytes⟩)
          simp only [VG.Proof.Dsa.Generation.generatorResult, hr, valid, ite_true]
        · refine Or.inr (Or.inl ⟨by simp [upd, valid], ?_⟩)
          simp only [VG.Proof.Dsa.Generation.generatorResult, hr, valid, ite_false]
      · exact (show Frame p.changed s.mem v.mem by rw [hm]; exact fu).trans ft
    · intro _ _ _ _ hn
      exact False.elim (hn h19)

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/SeedPrimeFinish.lean`, which only this module imported.
section

/-! # Bounded p search, generator search, and final validation form one native continuation -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout
open VG.Proof.MillerRabin.X86_64


variable {checkName : String}

theorem seedPrimeFinish_ok (H : GenerationHashes) (M : Mont) (Sq : MontS) (T : PrimeTest)
    {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (seed : GenerationTape p.geo) (hlen : seed.bytes.length = p.geo.qLen)
    (hseed : GenerationTapeMemory seed s) (h1 : W 1 = seed.ptr)
    (hq : Spec.Rsa.bytesAt s.mem (off p.geo.B q) p.geo.qLen =
      Spec.Dsa.encodeBE p.geo.qLen (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes))
    {used : Nat} (h16 : W 16 = BitVec.ofNat 64 used) (hu : used ≤ p.rand.bytes.length) :
    WP isa (.seq (Impl.Dsa.X86_64.Generation.primeSearch H.sha1 H.sha256 T.run p.geo.pLen p.geo.qLen)
      (Impl.Dsa.X86_64.Generation.onSuccess
        (.seq (Impl.Dsa.X86_64.Generation.generatorSearch Sq.mm M.mm p.geo.pLen)
          (Impl.Dsa.X86_64.Generation.onSuccess (Impl.Dsa.X86_64.Generation.finishDomain (checkName := checkName) Sq.mm M.mm p.geo.pLen p.geo.qLen))))) s
      (SeedFinished p W (VG.Proof.Dsa.Generation.primeResult (8 * p.geo.pLen) (8 * p.geo.qLen)
        (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes) seed.bytes
        ((Spec.Dsa.generationChunks p.geo.pLen p.hs.bytes).map Spec.Dsa.decodeBE) (p.rand.bytes.drop used)) s) := by
  have qfit : Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes < 256 ^ p.geo.qLen := by
    have shape := VG.Proof.Dsa.Generation.qCandidate_shape
      (by rcases p.geo.qWidth with hh | hh <;> omega : 2 ≤ 8 * p.geo.qLen) seed.bytes
    simpa only [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul] using shape.2.2
  refine WP.seq (WP.mono (seedPrime_ok H T h seed hlen hseed h1 hq h16 hu)
    fun u ⟨Wu, usedu, huu, mu, u16, slots, bqu, result, fu, ru, wu⟩ => ?_)
  rcases result with ⟨h19, hr⟩ | ⟨h19, value, hr, domain, bp, be⟩ | ⟨h19, hr⟩
  · apply onSuccess_generation_ok mu
    · intro _ _ _ _ hs
      have impossible : (0 : BitVec 64) = 1 := h19.symm.trans hs
      exact False.elim (by cases impossible)
    · intro t mt hm kt _
      refine ⟨Wu, usedu, mt, huu, u16, slots, Or.inl ⟨h19, ?_⟩, ?_, kt.2.1.trans ru, kt.2.2.trans wu⟩
      · simp only [VG.Proof.Dsa.Generation.primeResult, hr]
      · rw [hm]; exact fu
  · apply onSuccess_generation_ok mu
    · intro v mv hm kv _
      have bv : Spec.Rsa.bytesAt v.mem (off p.geo.B VG.Impl.Dsa.Generation.Layout.p) p.geo.pLen = Spec.Dsa.encodeBE p.geo.pLen value := hm ▸ bp
      have ev : Spec.Rsa.bytesAt v.mem (off p.geo.B exponent) p.geo.pLen = Spec.Dsa.encodeBE p.geo.pLen
          ((value - 1) / Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes) := hm ▸ be
      have qv : Spec.Rsa.bytesAt v.mem (off p.geo.B q) p.geo.qLen = Spec.Dsa.encodeBE p.geo.qLen
          (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes) := hm ▸ bqu
      have call := seedGeneratorFinish_ok (checkName := checkName) M Sq mv value (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes)
        domain qfit bv ev qv u16 huu
      have expected : VG.Proof.Dsa.Generation.primeResult (8 * p.geo.pLen) (8 * p.geo.qLen)
          (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes) seed.bytes
          ((Spec.Dsa.generationChunks p.geo.pLen p.hs.bytes).map Spec.Dsa.decodeBE) (p.rand.bytes.drop used) =
          VG.Proof.Dsa.Generation.generatorResult value (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes)
          ((Spec.Dsa.generationChunks p.geo.pLen p.hs.bytes).map Spec.Dsa.decodeBE) (p.rand.bytes.drop usedu) := by
        simp only [VG.Proof.Dsa.Generation.primeResult, hr]
      rw [expected]
      refine WP.mono call fun t ht => ?_
      exact ht.prepend slots (by rw [hm]; exact fu) (kv.2.1.trans ru) (kv.2.2.trans wu)
    · intro _ _ _ _ hn
      exact False.elim (hn h19)
  · apply onSuccess_generation_ok mu
    · intro _ _ _ _ hs
      have impossible : (3 : BitVec 64) = 1 := h19.symm.trans hs
      exact False.elim (by cases impossible)
    · intro t mt hm kt _
      refine ⟨Wu, usedu, mt, huu, u16, slots, Or.inr (Or.inl ⟨h19, ?_⟩), ?_, kt.2.1.trans ru, kt.2.2.trans wu⟩
      · simp only [VG.Proof.Dsa.Generation.primeResult, hr]
      · rw [hm]; exact fu

end VG.Proof.Dsa.X86_64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout
open VG.Proof.MillerRabin.X86_64


variable {checkName : String}

theorem seedAttempt_ok (H : GenerationHashes) (M : Mont) (Sq : MontS) (T : PrimeTest)
    {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (seed : GenerationTape p.geo) (hlen : seed.bytes.length = p.geo.qLen)
    (hseed : GenerationTapeMemory seed s) (h1 : W 1 = seed.ptr)
    {used : Nat} (h16 : W 16 = BitVec.ofNat 64 used) (hu : used ≤ p.rand.bytes.length) :
    WP isa (Impl.Dsa.X86_64.Generation.seedAttempt (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run p.geo.pLen p.geo.qLen) s
      (SeedFinished p W (VG.Proof.Dsa.Generation.seedResult (8 * p.geo.pLen) (8 * p.geo.qLen) seed.bytes
        ((Spec.Dsa.generationChunks p.geo.pLen p.hs.bytes).map Spec.Dsa.decodeBE) (p.rand.bytes.drop used)) s) := by
  unfold Impl.Dsa.X86_64.Generation.seedAttempt
  refine WP.seq (WP.mono (seedSubgroup_ok H T h seed hlen hseed h1 h16 hu)
    fun u ⟨usedu, status, huu, mu, bqu, fail, result, fu, ru, wu⟩ => ?_)
  let Wu := upd (upd (seedWords W p.geo.qLen) 16 (BitVec.ofNat 64 usedu)) 19 status
  have u16 : Wu 16 = BitVec.ofNat 64 usedu := by simp [Wu, upd]
  have u19 : Wu 19 = status := by simp [Wu, upd]
  have slots : ∀ k ∈ searchSlots, Wu k = W k := by
    intro k hk
    simp only [searchSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | rfl
      | simpa [Wu, seedWords, upd] using ((h.slots 28 (by simp [generationSlots])).trans p.hashLenSlot).symm
  have u1 : Wu 1 = seed.ptr := (slots 1 (by simp [searchSlots])).trans h1
  have seedu := hseed.frame fu ru wu
  cases qr : Spec.Dsa.probablePrime (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes) (p.rand.bytes.drop used) with
  | none =>
    have hs : Wu 19 = 0 := u19.trans (fail qr)
    apply onSuccess_generation_ok mu
    · intro _ _ _ _ accepted
      have impossible : (0 : BitVec 64) = 1 := hs.symm.trans accepted
      exact False.elim (by cases impossible)
    · intro t mt hm kt _
      refine ⟨Wu, usedu, mt, huu, u16, slots, Or.inl ⟨hs, ?_⟩, ?_, kt.2.1.trans ru, kt.2.2.trans wu⟩
      · simp only [VG.Proof.Dsa.Generation.seedResult, qr]
      · rw [hm]; exact fu
  | some pair =>
    rcases pair with ⟨accepted, rest⟩
    obtain ⟨hs, cursor⟩ := result accepted rest qr
    have suffix : p.rand.bytes.drop usedu = rest := by
      rw [cursor]
      exact VG.Proof.Dsa.Generation.probablePrime_cursor qr
    cases accepted with
    | false =>
      have hstatus : Wu 19 = 3 := u19.trans hs
      apply onSuccess_generation_ok mu
      · intro _ _ _ _ accepted
        have impossible : (3 : BitVec 64) = 1 := hstatus.symm.trans accepted
        exact False.elim (by cases impossible)
      · intro t mt hm kt _
        refine ⟨Wu, usedu, mt, huu, u16, slots, Or.inr (Or.inl ⟨hstatus, ?_⟩), ?_, kt.2.1.trans ru, kt.2.2.trans wu⟩
        · simp only [VG.Proof.Dsa.Generation.seedResult, qr, suffix]
        · rw [hm]; exact fu
    | true =>
      have hstatus : Wu 19 = 1 := u19.trans hs
      apply onSuccess_generation_ok mu
      · intro v mv hm kv _
        have seedv := seedu.frame (p := p) (by rw [hm]; exact Frame.refl _ _) kv.2.1 kv.2.2
        have qv : Spec.Rsa.bytesAt v.mem (off p.geo.B q) p.geo.qLen =
            Spec.Dsa.encodeBE p.geo.qLen (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes) := hm ▸ bqu
        have call := seedPrimeFinish_ok (checkName := checkName) H M Sq T mv seed hlen seedv u1 qv u16 huu
        have expected : VG.Proof.Dsa.Generation.seedResult (8 * p.geo.pLen) (8 * p.geo.qLen) seed.bytes
            ((Spec.Dsa.generationChunks p.geo.pLen p.hs.bytes).map Spec.Dsa.decodeBE) (p.rand.bytes.drop used) =
            VG.Proof.Dsa.Generation.primeResult (8 * p.geo.pLen) (8 * p.geo.qLen)
            (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes) seed.bytes
            ((Spec.Dsa.generationChunks p.geo.pLen p.hs.bytes).map Spec.Dsa.decodeBE) (p.rand.bytes.drop usedu) := by
          simp only [VG.Proof.Dsa.Generation.seedResult, qr, suffix]
        rw [expected]
        refine WP.mono call fun t ht => ?_
        exact ht.prepend slots (by rw [hm]; exact fu) (kv.2.1.trans ru) (kv.2.2.trans wu)
      · intro _ _ _ _ hn
        exact False.elim (hn hstatus)

end VG.Proof.Dsa.X86_64.Generation
