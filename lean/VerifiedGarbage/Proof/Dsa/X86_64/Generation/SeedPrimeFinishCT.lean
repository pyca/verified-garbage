module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedPrimeResultCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PConstructCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedGeneratorFinishCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedPrimeCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedPhaseStableCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OnSuccessCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSuccess
import VerifiedGarbage.Proof.RsaOaep.X86_64.Hash

/-! # Prime search composes with generator selection and final domain checking -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Proof.MillerRabin.X86_64 VG.Impl.Dsa.X86_64.Generation

theorem seedGeneratorBefore_congr {n pLen qLen : Nat} {p : SeedGeneratorPublic} {s t : State}
    (h : SeedGeneratorBefore n pLen qLen p s) (hm : t.mem = s.mem) (hk : Keep [.rax] s t) :
    SeedGeneratorBefore n pLen qLen p t :=
  ⟨seedPrimeBefore_congr h.1 hm hk, hm ▸ h.2.1, hm ▸ h.2.2⟩

theorem seedPrimeAfter_congr {n pLen qLen : Nat} {p : SeedPublic} {s t : State}
    (h : SeedPrimeAfter n pLen qLen p s) (hm : t.mem = s.mem) (hk : Keep [.rax] s t) :
    SeedPrimeAfter n pLen qLen p t := by
  obtain ⟨⟨W, hW, hs⟩, next⟩ := h
  refine ⟨⟨W, hW.congr hm hk, hs⟩, fun ha => ?_⟩
  obtain ⟨value, rest, hr, domain, ht⟩ := next ha
  exact ⟨value, rest, hr, domain, seedGeneratorBefore_congr ht hm hk⟩

theorem seedPrimeAfter_related {n pLen qLen : Nat} {s t : State}
    (h : Two (fun p s => SeedPrimeAfter n pLen qLen p s ∧ p.primeStatus = 1) s t) :
    Two (SeedGeneratorBefore n pLen qLen) s t := by
  obtain ⟨p, hs, ht⟩ := h
  obtain ⟨vs, rs, hrs, ds, hgs⟩ := hs.1.2 hs.2
  obtain ⟨vt, rt, hrt, dt, hgt⟩ := ht.1.2 ht.2
  have eqs := Option.some.inj (hrs.symm.trans hrt)
  have hv := Option.some.inj (congrArg Prod.fst eqs)
  have hr : rs = rt := congrArg Prod.snd eqs
  subst vt; subst rt
  exact ⟨p.generatorPublic vs rs ds, hgs, hgt⟩

theorem seedPrimeFinish_ct (H : GenerationHashes) (M : Mont) (Sq : MontS) (K : Kernel)
    (n : Nat) (hn : n = 2 ∨ n = 3) (pLen qLen : Nat) (sizes : GenerationSizes pLen qLen) :
    RelCT isa (Two (SeedPrimeBefore n pLen qLen))
      (.seq (primeSearch H.sha1 H.sha256 M.mm K.run pLen qLen)
        (onSuccess (.seq (generatorSearch Sq.mm M.mm pLen) (onSuccess (finishDomain Sq.mm M.mm pLen qLen)))))
      (fun _ _ => True) := by
  refine RelCT.seq (two_post (seedPrime_ct H M K n hn pLen qLen sizes)
    (fun _ _ h => seedPrime_after H M K h)) ?_
  apply onSuccess_ct (Φ := SeedPrimeAfter n pLen qLen) SeedPublic.context SeedPublic.primeStatus
    (fun _ _ h => h.1) (fun _ _ _ h hm hk => seedPrimeAfter_congr h hm hk)
  exact (seedGeneratorFinish_ct M Sq n pLen qLen sizes).mono
    (fun _ _ h => seedPrimeAfter_related h) (fun _ _ h => h)

end VG.Proof.Dsa.X86_64.Generation
