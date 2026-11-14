module
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PConstructCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedSearchPlanCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchInitCT
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchIterationCTState
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchIterationCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashChoice

/-! ### `Dsa.AArch64.Generation.SeedSearchStateCT`, which only this module used -/

section

/-! # Instantiate the public prime-search state from actual persistent-frame words -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

theorem seedPrime_memory {p : SeedPublic} {s : State} {W : Nat → BitVec 64}
    (hm : GenerationMemory p.context W s) (seed : GenerationTapeMemory p.seed s)
    (h1 : W 1 = p.seed.ptr) (h10 : W 10 = p.seedCursor)
    (hq : Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.context.geo.B q) p.context.geo.qLen =
      Spec.Dsa.encodeBE p.context.geo.qLen (Spec.Dsa.qCandidate (8 * p.context.geo.qLen) p.seed.bytes)) :
    SearchMemory p.searchPlan W s := by
  have state := hm.searchState p.seed p.length seed h1 hq
  have h5 : W 5 = p.context.saved 5 := hm.slots 5 (by simp [generationSlots])
  refine {
    layout := state.layout
    rep := state.rep
    slots := seedPrime_words hm h1 h10
    label := state.label.congr rfl rfl rfl ?_
    seedRead := state.seedRead
    wrappedWrite := state.wrappedWrite
    hashWrite := state.hashWrite
    seed := state.seed
    scratch := state.scratch
    qSource := ?_
    tape := state.tape
    shapedWrite := ?_
    pWrite := ?_
    exponentWrite := ?_
    witnessWrite := ?_
    arena := ?_
    tapeCover := state.tapeCover }
  · change p.context.saved 26 = W 26
    exact (hm.slots 26 (by simp [generationSlots])).symm
  · have src := state.qSource
    change Src s (VG.Proof.Bignum.off p.context.geo.B arithmetic) arithmeticBytes (VG.Proof.Bignum.off (W 5) q) _ at src
    change Src s (VG.Proof.Bignum.off p.context.geo.B arithmetic) arithmeticBytes (VG.Proof.Bignum.off (p.context.saved 5) q) _
    rw [h5] at src
    exact src
  · have write := state.shapedWrite
    change ∀ i < p.context.geo.pLen, InRegions s.wr (VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) shaped) i) 1 at write
    change ∀ i < p.context.geo.pLen, InRegions s.wr (VG.Proof.Bignum.off (VG.Proof.Bignum.off (p.context.saved 5) shaped) i) 1
    rw [h5] at write
    exact write
  · have write := state.pWrite
    change ∀ i < p.context.geo.pLen, InRegions s.wr (VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) VG.Impl.Dsa.Generation.Layout.p) i) 1 at write
    change ∀ i < p.context.geo.pLen, InRegions s.wr (VG.Proof.Bignum.off (VG.Proof.Bignum.off (p.context.saved 5) VG.Impl.Dsa.Generation.Layout.p) i) 1
    rw [h5] at write
    exact write
  · have write := state.exponentWrite
    change ∀ i < p.context.geo.pLen, InRegions s.wr (VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) exponent) i) 1 at write
    change ∀ i < p.context.geo.pLen, InRegions s.wr (VG.Proof.Bignum.off (VG.Proof.Bignum.off (p.context.saved 5) exponent) i) 1
    rw [h5] at write
    exact write
  · have write := state.witnessWrite
    change ∀ i < p.context.geo.pLen, InRegions s.wr (VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) witness) i) 1 at write
    change ∀ i < p.context.geo.pLen, InRegions s.wr (VG.Proof.Bignum.off (VG.Proof.Bignum.off (p.context.saved 5) witness) i) 1
    rw [h5] at write
    exact write
  · have a := state.arena
    change Scr s (W 5) domainCheck at a
    change Scr s (p.context.saved 5) domainCheck
    rw [h5] at a
    exact a

theorem seedPrime_start {pLen qLen : Nat} {p : SeedPublic} {s : State}
    (h : SeedPrimeBefore pLen qLen p s) : SearchStart pLen qLen p.search s := by
  obtain ⟨⟨⟨W, hm, h1, h16, h10⟩, seed, heQ⟩, heP, hq⟩ := h
  exact ⟨⟨W, seedPrime_memory hm seed h1 h10 hq, h16⟩,
    hm.scratch.sub (p.context.geo.small_bound (d := control) (n := 24) (by decide) (by decide)) (by decide),
    p.bound, heP, heQ, rfl⟩

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.NativeSearchCT`, which only this module used -/

section

/-! ### `Dsa.AArch64.Generation.PSearchLoopCT`, which only this module used -/

section

/-! # Timing of the bounded native p search, including its exact retry cursor -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64
open VG.Proof.Pbkdf2.Md.AArch64 VG.Impl.Dsa.AArch64.Generation VG.Impl.Bignum.AArch64

private def searchLoopInv (pLen qLen remaining : Nat) : State → State → Prop :=
  Two fun p s => 32 * pLen - p.counter = remaining ∧ SearchBefore pLen qLen p s

section
variable (G1 G256 : Impl.Pbkdf2.Md.AArch64.Hash)
variable (T : PrimeTest) (H : Spec.Mgf1.Hash) (pLen qLen : Nat)
variable (sizes : GenerationSizes pLen qLen)
variable (hG : Calls.StreamOK (if qLen = 20 then G1 else G256).stream)
variable (hmatch : ∀ x, H.hash x = hG.SH.H.hash x)
variable (hsize : ∀ x, (H.hash x).length = (if qLen = 20 then G1 else G256).D)
variable (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * qLen) bs)
variable (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * qLen) bs).length = 8 * qLen)
variable (hd : (if qLen = 20 then G1 else G256).D = qLen)

include hG hmatch hsize hhash hseedsize hd sizes

theorem searchIteration_ready {p : SearchPublic} {s : State} (h : SearchBefore pLen qLen p s) :
    WP isa (pSearchIteration (pAttempt G1 G256 T.run pLen qLen)
      (32 * pLen) ((8 * pLen - 1) / (8 * qLen) + 1)) s (SearchIterationAfter pLen qLen p) := by
  unfold pSearchIteration
  simp only [seqs]
  refine WP.seq (WP.mono (searchBody_ready G1 G256 T hG hmatch hsize hhash hseedsize hd h)
    fun _ ht => searchIteration_tail ⟨ht, h.2.2.2⟩ ?_ ?_)
  all_goals rcases sizes with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

private theorem searchLoop_step (remaining : Nat) :
    RelCT isa (searchLoopInv pLen qLen remaining)
      (pSearchIteration (pAttempt G1 G256 T.run pLen qLen)
        (32 * pLen) ((8 * pLen - 1) / (8 * qLen) + 1))
      (fun s t => isa.eval (.zero .x .x3) s = isa.eval (.zero .x .x3) t ∧ (isa.eval (.zero .x .x3) s = some false → True) ∧
        (isa.eval (.zero .x .x3) s = some true → ∃ next < remaining, searchLoopInv pLen qLen next s t)) := by
  have step : RelCT isa (searchLoopInv pLen qLen remaining)
      (pSearchIteration (pAttempt G1 G256 T.run pLen qLen)
        (32 * pLen) ((8 * pLen - 1) / (8 * qLen) + 1))
      (Two fun p s => 32 * pLen - p.counter = remaining ∧ SearchIterationAfter pLen qLen p s) := by
    refine two_post ((searchIteration_ct G1 G256 T H pLen qLen sizes hG hmatch hsize hhash hseedsize hd).mono
      (fun _ _ => two_mono fun _ _ h => h.2) (fun _ _ _ => True.intro)) ?_
    intro p s h
    exact WP.mono (searchIteration_ready G1 G256 T H pLen qLen sizes hG hmatch hsize hhash hseedsize hd h.2)
      fun _ ht => ⟨h.1, ht⟩
  refine step.mono (fun _ _ h => h) ?_
  rintro s t ⟨p, ⟨hr, hs⟩, ⟨_, ht⟩, hsp⟩
  refine ⟨hs.1.trans ht.1.symm, fun _ => True.intro, fun he => ?_⟩
  have cont : p.continues = true := Option.some.inj (hs.1.symm.trans he)
  have next := hs.2 cont
  have bound : p.counter + 1 < 32 * pLen := by
    have hb := (of_decide_eq_true cont).2
    rw [show p.plan.attempt.construct.len = pLen from next.2.2.2.1] at hb
    exact hb
  refine ⟨32 * pLen - (p.counter + 1), by omega_using [hr, bound], p.next cont, ⟨rfl, next⟩, ⟨rfl, ht.2 cont⟩, hsp⟩

theorem pSearchLoop_ct : RelCT isa (Two (SearchBefore pLen qLen))
    (.loop (pSearchIteration (pAttempt G1 G256 T.run pLen qLen)
      (32 * pLen) ((8 * pLen - 1) / (8 * qLen) + 1)) (.zero .x .x3)) (fun _ _ => True) := by
  rintro s t a b s' t' ⟨p, hs, ht, hsp⟩ es et
  exact RelCT.loop (searchLoopInv pLen qLen)
    (searchLoop_step G1 G256 T H pLen qLen sizes hG hmatch hsize hhash hseedsize hd)
    (32 * pLen - p.counter) s t a b s' t' ⟨p, ⟨rfl, hs⟩, ⟨rfl, ht⟩, hsp⟩ es et

end
end VG.Proof.Dsa.AArch64.Generation

end

end


/-! # The complete bounded native p search has a public trace -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64
open VG.Proof.Pbkdf2.Md.AArch64 VG.Impl.Dsa.AArch64.Generation

theorem primeSearch_ct (G1 G256 : Impl.Pbkdf2.Md.AArch64.Hash)
    (T : PrimeTest) (H : Spec.Mgf1.Hash) (pLen qLen : Nat)
    (sizes : GenerationSizes pLen qLen)
    (hG : Calls.StreamOK (if qLen = 20 then G1 else G256).stream)
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x)
    (hsize : ∀ x, (H.hash x).length = (if qLen = 20 then G1 else G256).D)
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * qLen) bs)
    (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * qLen) bs).length = 8 * qLen)
    (hd : (if qLen = 20 then G1 else G256).D = qLen) :
    RelCT isa (Two (SearchStart pLen qLen)) (primeSearch G1 G256 T.run pLen qLen)
      (fun _ _ => True) := by
  unfold primeSearch pSearch
  refine RelCT.seq (two_post ((two_map SearchPublic.returnFrame (fun _ _ h => searchStart_frame h)
    controlBase_ct).mono (fun _ _ h => h) (fun _ _ _ => True.intro))
    (fun _ _ h => searchBase_ready h)) (RelCT.seq (searchInit_ct pLen qLen) ?_)
  exact pSearchLoop_ct G1 G256 T H pLen qLen sizes hG hmatch hsize hhash hseedsize hd

end VG.Proof.Dsa.AArch64.Generation

end

end


/-! # The accepted subgroup enters the complete public-trace prime search -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64

theorem seedPrime_ct (H : GenerationHashes) (T : PrimeTest)
    (pLen qLen : Nat) (sizes : GenerationSizes pLen qLen) :
    RelCT isa (Two (SeedPrimeBefore pLen qLen))
      (Impl.Dsa.AArch64.Generation.primeSearch H.sha1 H.sha256 T.run pLen qLen) (fun _ _ => True) := by
  have hq : qLen = 20 ∨ qLen = 32 := by
    rcases sizes with h | h | h <;> simp [h.2]
  exact two_map SeedPublic.search (fun _ _ h => seedPrime_start h)
    (primeSearch_ct H.sha1 H.sha256 T (generationHash qLen) pLen qLen sizes
      (H.streamOK qLen) (H.hash_matches qLen) (H.hash_size qLen)
      (generationHash_seed hq) (H.seed_size hq) (H.hash_width hq))

end VG.Proof.Dsa.AArch64.Generation
