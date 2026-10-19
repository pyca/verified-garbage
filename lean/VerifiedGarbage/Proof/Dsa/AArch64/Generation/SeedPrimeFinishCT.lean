module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedPrimeResultCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedGeneratorFinishCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedPrimeCT

/-! # Prime search composes with generator selection and final domain checking -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Proof.MillerRabin.AArch64 VG.Impl.Dsa.AArch64.Generation

theorem seedGeneratorBefore_congr {pLen qLen : Nat} {p : SeedGeneratorPublic} {s t : State}
    (h : SeedGeneratorBefore pLen qLen p s) (hm : t.mem = s.mem) (hk : Keep [.x3, .x4] s t) :
    SeedGeneratorBefore pLen qLen p t :=
  ⟨seedPrimeBefore_congr h.1 hm hk, hm ▸ h.2.1, hm ▸ h.2.2⟩

theorem seedPrimeAfter_congr {pLen qLen : Nat} {p : SeedPublic} {s t : State}
    (h : SeedPrimeAfter pLen qLen p s) (hm : t.mem = s.mem) (hk : Keep [.x3, .x4] s t) :
    SeedPrimeAfter pLen qLen p t := by
  obtain ⟨⟨W, hW, hs⟩, next⟩ := h
  refine ⟨⟨W, hW.congr hm hk, hs⟩, fun ha => ?_⟩
  obtain ⟨value, rest, hr, domain, ht⟩ := next ha
  exact ⟨value, rest, hr, domain, seedGeneratorBefore_congr ht hm hk⟩

theorem seedPrimeAfter_related {pLen qLen : Nat} {s t : State}
    (h : Two (fun p s => SeedPrimeAfter pLen qLen p s ∧ p.primeStatus = 1) s t) :
    Two (SeedGeneratorBefore pLen qLen) s t := by
  obtain ⟨p, hs, ht, hsp⟩ := h
  obtain ⟨vs, rs, hrs, ds, hgs⟩ := hs.1.2 hs.2
  obtain ⟨vt, rt, hrt, dt, hgt⟩ := ht.1.2 ht.2
  have eqs := Option.some.inj (hrs.symm.trans hrt)
  have hv := Option.some.inj (congrArg Prod.fst eqs)
  have hr : rs = rt := congrArg Prod.snd eqs
  subst vt; subst rt
  exact ⟨p.generatorPublic vs rs ds, hgs, hgt, hsp⟩

theorem seedPrimeFinish_ct (H : GenerationHashes) (M : Mont)  (K : Kernel)
    (pLen qLen : Nat) (sizes : GenerationSizes pLen qLen) :
    RelCT isa (Two (SeedPrimeBefore pLen qLen))
      (.seq (primeSearch H.sha1 H.sha256 M.mm K.run pLen qLen)
        (onSuccess (.seq (generatorSearch M.mm pLen) (onSuccess (finishDomain M.mm pLen qLen)))))
      (fun _ _ => True) := by
  refine RelCT.seq (two_post (seedPrime_ct H M K pLen qLen sizes)
    (fun _ _ h => seedPrime_after H M K h)) ?_
  apply onSuccess_ct (Φ := SeedPrimeAfter pLen qLen) SeedPublic.context SeedPublic.primeStatus
    (fun _ _ h => h.1) (fun _ _ _ h hm hk => seedPrimeAfter_congr h hm hk)
  exact (seedGeneratorFinish_ct M pLen qLen sizes).mono
    (fun _ _ h => seedPrimeAfter_related h) (fun _ _ h => h)

end VG.Proof.Dsa.AArch64.Generation
