module

public import VerifiedGarbage.Impl.Dsa.X86_64.Fn
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillVerified
public import VerifiedGarbage.Proof.Dsa.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubFillG
import VerifiedGarbage.Proof.Framework.X86_64.ScrubCall
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.KernelRfl

/-!
# DSA's parameter search on x86-64, without secret residue

`vg_dsa_parameter_search` as emitted (`Impl.Dsa.X86_64.Fn.parameterSearch`),
over a pair of a SHA-1 and a SHA-256 implementation (`Hashes`) and any
implementation of the Miller–Rabin round (`RoundImpl`), with its whole stack
wiped by its cleanup at the higher of their levels.

Its code calls a search for each width, whose code is generic over the round
only through the call of the prime test (`ProbablePrime.primeTest`): over a
stub of that call it is closed for each implementation of the hash it runs,
which the kernel evaluates once for each (`sha1_side`, `sha256_side`, by the
variants the search is emitted for, `Hashes.mem1`, `Hashes.mem256`), and the
prime test's code is its code over stubs of the round and its multiplication
(`prime_side`).
-/

-- separate module: the kernel's evaluation of the cleanup's side conditions, which a registration file may not hold

@[expose] public section

namespace VG.Proof.Dsa.X86_64.Generation.SearchScrub

open VG.X86_64 VG.X86_64.Scrub VG.Impl.Scrub.X86_64
open VG.Proof.MillerRabin.X86_64 (RoundImpl)
open VG.Proof.Pbkdf2.Md.X86_64 (MdHash)
open VG.Proof.Dsa.X86_64.Generation.RefillBackend (Hashes body name)

/-! ## The prime test -/

/-- The stack the round (called) and the multiplication (inline) need. -/
def primeStack : String → Nat := fun s => if s = "r" then 128 else 0

/-- The prime test's code over stubs of the multiplication and the round. -/
def primeStub : Prog isa :=
  Impl.Dsa.X86_64.ProbablePrime.code (fun _ _ _ => .call "mm" (.block []))
    (Impl.MillerRabin.X86_64.Caller.call "r" (.block []))

theorem prime_stub : stubCalleeG primeStub VecLevel.sse.level primeStack 184 = true := by lit_decide

theorem prime_side (v : RoundImpl) :
    calleeSide (ProbablePrime.testCode v) v.level.level 184 = true := by
  have hm := v.inlineSide
  have hr := v.side
  refine calleeSide_of_fillG (n := primeStack) ?_ (Nat.zero_le _) prime_stub
  unfold primeStub ProbablePrime.testCode VG.Proof.MillerRabin.X86_64.Kernel.called
  fill_gen

/-! ## The search for one width -/

/-- The level of the hash implementation `h`'s code. -/
def hashLevel (h : MdHash) : VecLevel := if h.features.contains "avx" then .avx else .sse

/-- The stack the prime test (called) needs. -/
def ptStack : String → Nat := fun _ => 192

/-- The search for width `p` with the hash `h`, over a stub of the call of
the prime test. -/
def bodyStub (h : MdHash) (p : Nat) : Prog isa :=
  Impl.Dsa.X86_64.Generation.Refill.code (checkName := Proof.Dsa.X86_64.Generation.SharedChecker.name)
    h.H.stream h.H.stream RefillBackend.arith.inlineMont.toS.mm RefillBackend.arith.inlineMont.mm
    (.call "pt" (.block [])) p (Spec.Dsa.generationQLen p)

/-- The prime test over `v`, by the name its stub calls it by. -/
def ptSigma (v : RoundImpl) (f : String) : Option (String × Prog isa) :=
  if f = "pt" then some ((ProbablePrime.primeTest v).name, (ProbablePrime.primeTest v).code) else none

theorem ptSigma_side (v : RoundImpl) {k : Nat} (hk : v.level.level ≤ k) :
    ∀ f g d, ptSigma v f = some (g, d) → calleeSide (.call g d) k (ptStack f) = true := by
  intro f g d h
  unfold ptSigma at h
  split at h
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact FillG.calleeSide_call _ (calleeSide_mono hk (Nat.le_refl _) (prime_side v))
  · cases h

theorem hashLevel_le (h : MdHash) (v : RoundImpl) : v.level.level ≤ ((hashLevel h).join v.level).level :=
  level_join_right _ _

/-- What the cleanup of the search needs of its search for width 128, with each
implementation of the hash. -/
theorem sha1_side128 (h : MdHash) (hm : h ∈ VG.Proof.Variants.MdHash.X86_64.sha1Variants) (v : RoundImpl) :
    calleeSide (body h v 128) ((hashLevel h).join v.level).level 568 = true := by
  simp only [VG.Proof.Variants.MdHash.X86_64.sha1Variants, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl
  · have e : body VG.Proof.Variants.MdHash.X86_64.sha1ShaNi v 128 = fillCallsG (ptSigma v) (bodyStub VG.Proof.Variants.MdHash.X86_64.sha1ShaNi 128) := by
      unfold body RefillBackend.backendCode VG.Proof.Dsa.X86_64.Generation.PrimeTest.run bodyStub; kernel_rfl
    exact calleeSide_of_fillG (ks := (hashLevel VG.Proof.Variants.MdHash.X86_64.sha1ShaNi).level) (n := ptStack)
      (e ▸ fillG_of (ptSigma_side v (hashLevel_le _ v)) _) (level_join_left _ _) (by lit_decide)
  · have e : body VG.Proof.Variants.MdHash.X86_64.sha1AvxBmi v 128 = fillCallsG (ptSigma v) (bodyStub VG.Proof.Variants.MdHash.X86_64.sha1AvxBmi 128) := by
      unfold body RefillBackend.backendCode VG.Proof.Dsa.X86_64.Generation.PrimeTest.run bodyStub; kernel_rfl
    exact calleeSide_of_fillG (ks := (hashLevel VG.Proof.Variants.MdHash.X86_64.sha1AvxBmi).level) (n := ptStack)
      (e ▸ fillG_of (ptSigma_side v (hashLevel_le _ v)) _) (level_join_left _ _) (by lit_decide)
  · have e : body VG.Proof.Variants.MdHash.X86_64.sha1 v 128 = fillCallsG (ptSigma v) (bodyStub VG.Proof.Variants.MdHash.X86_64.sha1 128) := by
      unfold body RefillBackend.backendCode VG.Proof.Dsa.X86_64.Generation.PrimeTest.run bodyStub; kernel_rfl
    exact calleeSide_of_fillG (ks := (hashLevel VG.Proof.Variants.MdHash.X86_64.sha1).level) (n := ptStack)
      (e ▸ fillG_of (ptSigma_side v (hashLevel_le _ v)) _) (level_join_left _ _) (by lit_decide)

/-- What the cleanup of the search needs of its search for width 256, with each
implementation of the hash. -/
theorem sha256_side256 (h : MdHash) (hm : h ∈ VG.Proof.Variants.MdHash.X86_64.sha256Variants) (v : RoundImpl) :
    calleeSide (body h v 256) ((hashLevel h).join v.level).level 568 = true := by
  simp only [VG.Proof.Variants.MdHash.X86_64.sha256Variants, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl
  · have e : body VG.Proof.Variants.MdHash.X86_64.sha256ShaNi v 256 = fillCallsG (ptSigma v) (bodyStub VG.Proof.Variants.MdHash.X86_64.sha256ShaNi 256) := by
      unfold body RefillBackend.backendCode VG.Proof.Dsa.X86_64.Generation.PrimeTest.run bodyStub; kernel_rfl
    exact calleeSide_of_fillG (ks := (hashLevel VG.Proof.Variants.MdHash.X86_64.sha256ShaNi).level) (n := ptStack)
      (e ▸ fillG_of (ptSigma_side v (hashLevel_le _ v)) _) (level_join_left _ _) (by lit_decide)
  · have e : body VG.Proof.Variants.MdHash.X86_64.sha256Avx2 v 256 = fillCallsG (ptSigma v) (bodyStub VG.Proof.Variants.MdHash.X86_64.sha256Avx2 256) := by
      unfold body RefillBackend.backendCode VG.Proof.Dsa.X86_64.Generation.PrimeTest.run bodyStub; kernel_rfl
    exact calleeSide_of_fillG (ks := (hashLevel VG.Proof.Variants.MdHash.X86_64.sha256Avx2).level) (n := ptStack)
      (e ▸ fillG_of (ptSigma_side v (hashLevel_le _ v)) _) (level_join_left _ _) (by lit_decide)
  · have e : body VG.Proof.Variants.MdHash.X86_64.sha256 v 256 = fillCallsG (ptSigma v) (bodyStub VG.Proof.Variants.MdHash.X86_64.sha256 256) := by
      unfold body RefillBackend.backendCode VG.Proof.Dsa.X86_64.Generation.PrimeTest.run bodyStub; kernel_rfl
    exact calleeSide_of_fillG (ks := (hashLevel VG.Proof.Variants.MdHash.X86_64.sha256).level) (n := ptStack)
      (e ▸ fillG_of (ptSigma_side v (hashLevel_le _ v)) _) (level_join_left _ _) (by lit_decide)

/-- What the cleanup of the search needs of its search for width 384, with each
implementation of the hash. -/
theorem sha256_side384 (h : MdHash) (hm : h ∈ VG.Proof.Variants.MdHash.X86_64.sha256Variants) (v : RoundImpl) :
    calleeSide (body h v 384) ((hashLevel h).join v.level).level 568 = true := by
  simp only [VG.Proof.Variants.MdHash.X86_64.sha256Variants, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl
  · have e : body VG.Proof.Variants.MdHash.X86_64.sha256ShaNi v 384 = fillCallsG (ptSigma v) (bodyStub VG.Proof.Variants.MdHash.X86_64.sha256ShaNi 384) := by
      unfold body RefillBackend.backendCode VG.Proof.Dsa.X86_64.Generation.PrimeTest.run bodyStub; kernel_rfl
    exact calleeSide_of_fillG (ks := (hashLevel VG.Proof.Variants.MdHash.X86_64.sha256ShaNi).level) (n := ptStack)
      (e ▸ fillG_of (ptSigma_side v (hashLevel_le _ v)) _) (level_join_left _ _) (by lit_decide)
  · have e : body VG.Proof.Variants.MdHash.X86_64.sha256Avx2 v 384 = fillCallsG (ptSigma v) (bodyStub VG.Proof.Variants.MdHash.X86_64.sha256Avx2 384) := by
      unfold body RefillBackend.backendCode VG.Proof.Dsa.X86_64.Generation.PrimeTest.run bodyStub; kernel_rfl
    exact calleeSide_of_fillG (ks := (hashLevel VG.Proof.Variants.MdHash.X86_64.sha256Avx2).level) (n := ptStack)
      (e ▸ fillG_of (ptSigma_side v (hashLevel_le _ v)) _) (level_join_left _ _) (by lit_decide)
  · have e : body VG.Proof.Variants.MdHash.X86_64.sha256 v 384 = fillCallsG (ptSigma v) (bodyStub VG.Proof.Variants.MdHash.X86_64.sha256 384) := by
      unfold body RefillBackend.backendCode VG.Proof.Dsa.X86_64.Generation.PrimeTest.run bodyStub; kernel_rfl
    exact calleeSide_of_fillG (ks := (hashLevel VG.Proof.Variants.MdHash.X86_64.sha256).level) (n := ptStack)
      (e ▸ fillG_of (ptSigma_side v (hashLevel_le _ v)) _) (level_join_left _ _) (by lit_decide)

/-! ## The search -/

/-- The level of the search's cleanup over `p` and `v`. -/
def level (p : Hashes) (v : RoundImpl) : VecLevel := ((hashLevel p.sha1).join (hashLevel p.sha256)).join v.level

theorem le1 (a b c : VecLevel) : (a.join c).level ≤ ((a.join b).join c).level := by
  cases a <;> cases b <;> cases c <;> decide

theorem le2 (a b c : VecLevel) : (b.join c).level ≤ ((a.join b).join c).level := by
  cases a <;> cases b <;> cases c <;> decide

/-- The stack the search for each width (called) needs. -/
def searchStack : String → Nat := fun _ => 576

theorem search_stub :
    stubSideG (Impl.Dsa.X86_64.ParameterSearch.widths "a" "b" "c" (.block []) (.block []) (.block []))
      VecLevel.sse.level searchStack 632 [] = true := by lit_decide

/-- The search for each width over `p` and `v`, by the name its stub calls it by. -/
def searchSigma (p : Hashes) (v : RoundImpl) (f : String) : Option (String × Prog isa) :=
  if f = "a" then some (name "sha1" p.sha1 v 128, body p.sha1 v 128)
  else if f = "b" then some (name "sha256" p.sha256 v 256, body p.sha256 v 256)
  else if f = "c" then some (name "sha256" p.sha256 v 384, body p.sha256 v 384)
  else none

theorem searchSigma_side (p : Hashes) (v : RoundImpl) :
    ∀ f g d, searchSigma p v f = some (g, d) → calleeSide (.call g d) (level p v).level (searchStack f) = true := by
  have h1 := calleeSide_mono (le1 (hashLevel p.sha1) (hashLevel p.sha256) v.level) (Nat.le_refl _)
    (sha1_side128 p.sha1 p.mem1 v)
  have h2 := calleeSide_mono (le2 (hashLevel p.sha1) (hashLevel p.sha256) v.level) (Nat.le_refl _)
    (sha256_side256 p.sha256 p.mem256 v)
  have h3 := calleeSide_mono (le2 (hashLevel p.sha1) (hashLevel p.sha256) v.level) (Nat.le_refl _)
    (sha256_side384 p.sha256 p.mem256 v)
  intro f g d h
  unfold searchSigma at h
  split at h
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h); exact FillG.calleeSide_call _ h1
  split at h
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h); exact FillG.calleeSide_call _ h2
  split at h
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h); exact FillG.calleeSide_call _ h3
  cases h

theorem search_eq (p : Hashes) (v : RoundImpl) :
    RefillBackend.searchCode p.sha1 p.sha256 v = fillCallsG (searchSigma p v)
      (Impl.Dsa.X86_64.ParameterSearch.widths "a" "b" "c" (.block []) (.block []) (.block [])) := by
  unfold RefillBackend.searchCode; kernel_rfl

/-- `Spec.Dsa.parameterSearchApi`'s function as emitted over `p` and `v`
meets its contract in constant time and returns without secret residue. -/
theorem search_scrubbed (p : Hashes) (v : RoundImpl) :
    VerifiedScrubbed target
      (Impl.Dsa.X86_64.Fn.parameterSearch (level p v) (name "sha1" p.sha1 v 128) (name "sha256" p.sha256 v 256)
        (name "sha256" p.sha256 v 384) (body p.sha1 v 128) (body p.sha256 v 256) (body p.sha256 v 384))
      (Spec.Dsa.parameterSearchApi.contract X86_64.abi 632) 32 :=
  verifiedScrubbedAllFillG (api := Spec.Dsa.parameterSearchApi)
    { code := RefillBackend.searchCode p.sha1 p.sha256 v
      verified := RefillBackend.search_verified p.sha1 p.sha256 v p.h1 p.h256
      spSafe := RefillBackend.searchCode_spSafe p.sha1 p.sha256 v } _
    (Proof.Dsa.X86_64.Scrub.parameterSearchOut _)
    ((search_eq p v) ▸ fillG_of (searchSigma_side p v) _) (Nat.zero_le _) (Nat.le_refl _) (ha := search_stub)

theorem search_spSafe (p : Hashes) (v : RoundImpl) :
    (Impl.Dsa.X86_64.Fn.parameterSearch (level p v) (name "sha1" p.sha1 v 128) (name "sha256" p.sha256 v 256)
      (name "sha256" p.sha256 v 384) (body p.sha1 v 128) (body p.sha256 v 256) (body p.sha256 v 384)).all
      (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (RefillBackend.searchCode_spSafe p.sha1 p.sha256 v)

end VG.Proof.Dsa.X86_64.Generation.SearchScrub
