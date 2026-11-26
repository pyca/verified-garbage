module

public import VerifiedGarbage.Proof.Dsa.ParameterPublic
public import VerifiedGarbage.Impl.Dsa.X86_64.Fn
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillVerified
public import VerifiedGarbage.Proof.Dsa.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubFillG
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubFns
import VerifiedGarbage.Proof.Framework.X86_64.ScrubCall
import VerifiedGarbage.Proof.Framework.X86_64.ScrubChunks
import VerifiedGarbage.Proof.Framework.X86_64.MxCall
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.KernelRfl

/-!
# DSA's parameter search on x86-64, without secret residue

`vg_dsa_parameter_search` as emitted (`Impl.Dsa.X86_64.Fn.parameterSearch`),
over a pair of a SHA-1 and a SHA-256 implementation (`Hashes`) and any
implementation of the Miller–Rabin round (`RoundImpl`), with its whole stack
wiped by its cleanup at the higher of their levels.

Its code calls a search for each width, which calls its hash's `update` and
`finalize` and the prime test indirectly, by the addresses the search passes
it (`RefillBackend.addrs`), which its contract makes public
(`Abi.withFns`): two runs agree on the addresses of every function it calls
indirectly, as the cleanup needs (`Verified.scrubM`). The search for a width
is generic over the round only through the prime test, the candidate of its
indirect call: over a stub of that candidate (`bodyStub`) it is closed for
each implementation of the hash it runs, which the kernel evaluates once for
each (`stub_sha1`, `stub_sha256`, by the variants the search is emitted for,
`Hashes.mem1`, `Hashes.mem256`), and the prime test's code is its code over
stubs of the round and its multiplication (`prime_side`).
-/

-- separate module: the kernel's evaluation of the cleanup's side conditions, which a registration file may not hold

@[expose] public section

namespace VG.Proof.Dsa.X86_64.Generation.SearchScrub

open VG.X86_64 VG.X86_64.Scrub VG.Impl.Scrub.X86_64
open VG.Proof.MillerRabin.X86_64 (RoundImpl)
open VG.Proof.Pbkdf2.Md.X86_64 (MdHash)
open VG.Proof.Dsa.X86_64.Generation.RefillBackend (Hashes body name addrs fns)

/-! ## The prime test -/

/-- The stack the round (called) and the multiplication (inline) need. -/
def primeStack : String → Nat := fun s => if s = "r" then 128 else 0

/-- The prime test's code over stubs of the multiplication and the round. -/
def primeStub (shared : Bool := false) : Prog isa :=
  Impl.Dsa.X86_64.ProbablePrime.code (fun _ _ _ => .call "mm" (.block []))
    (Impl.MillerRabin.X86_64.Caller.call "r" (.block []))
    (let prepare := Impl.Dsa.X86_64.Generation.primeSetup (fun _ _ _ => .call "mm" (.block []))
     if shared then .call "prep" prepare else prepare)

theorem prime_stub : stubCalleeG (primeStub false) VecLevel.sse.level primeStack 184 = true := by lit_decide

theorem prime_call_stub : stubCalleeG (primeStub true) VecLevel.sse.level primeStack 184 = true := by
  lit_decide

theorem prime_side (v : RoundImpl) :
    calleeSide (ProbablePrime.testCode v) v.level.level 184 = true := by
  have hm := v.inlineSide
  have hr := v.side
  by_cases h : v.arithSuffix = ""
  · refine calleeSide_of_fillG (n := primeStack) ?_ (Nat.zero_le _) prime_stub
    unfold primeStub ProbablePrime.testCode VG.Proof.MillerRabin.X86_64.Kernel.called
      Preparation.forRound
    simp only [h, ↓reduceIte, Bool.false_eq_true]
    unfold Preparation.inlined
    fill_gen
  · refine calleeSide_of_fillG (n := primeStack) ?_ (Nat.zero_le _) prime_call_stub
    unfold primeStub ProbablePrime.testCode VG.Proof.MillerRabin.X86_64.Kernel.called
      Preparation.forRound
    simp only [h, ↓reduceIte]
    unfold Preparation.called
    fill_gen

/-! ## The search for one width -/

/-- The level of the hash implementation `h`'s code. -/
def hashLevel (h : MdHash) : VecLevel := if h.features.contains "avx" then .avx else .sse

/-- What the cleanup needs of the instructions of code: vector instructions of
at most the level `k`, and no load of MXCSR. -/
abbrev Ins (k : Nat) : Instr → Bool := fun i => decide (i.vecLevelR ≤ k) && !loadsMxcsr i

/-- What the cleanup needs of the search for a width with the hash `h` over
a stub of its prime test, called indirectly by the name `"pt"`: the level
of its instructions, and that it calls indirectly only `h`'s `update` and
`finalize` and `"pt"`. -/
noncomputable def stubOk (h : MdHash) (a : Prog isa) : Bool :=
  a.allInstrs (Ins (hashLevel h).level) &&
    (UpperLock.inames a).all fun n => decide (n ∈ [h.H.stream.updN, h.H.stream.finN, "pt"])

/-- The search for width `p` with the hash `h`, over a stub of the code of
the prime test it calls indirectly. -/
def bodyStub (h : MdHash) (p : Nat) : Prog isa :=
  Impl.Dsa.X86_64.Generation.Refill.code (checkName := Proof.Dsa.X86_64.Generation.SharedChecker.name)
    h.H.stream h.H.stream RefillBackend.arith.inlineMont.toS.mm RefillBackend.arith.inlineMont.mm
    (Impl.Dsa.X86_64.Generation.viaSlot Impl.Dsa.X86_64.Generation.primeSlot "pt" (.block [])) p
    (Spec.Dsa.generationQLen p)

/-- The prime test over `v`, by the name its stub is called by. -/
def ptSigma (v : RoundImpl) (f : String) : Option (String × Prog isa) :=
  if f = "pt" then some ((ProbablePrime.primeTest v).name, (ProbablePrime.primeTest v).code) else none

theorem stub_sha1 (h : MdHash) (hm : h ∈ VG.Proof.Variants.MdHash.X86_64.sha1Variants) :
    stubOk h (bodyStub h 128) = true := by
  simp only [VG.Proof.Variants.MdHash.X86_64.sha1Variants, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl <;> lit_decide

theorem stub_sha256 (h : MdHash) (hm : h ∈ VG.Proof.Variants.MdHash.X86_64.sha256Variants) (p : Nat)
    (hp : p = 256 ∨ p = 384) : stubOk h (bodyStub h p) = true := by
  simp only [VG.Proof.Variants.MdHash.X86_64.sha256Variants, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hp with rfl | rfl <;> rcases hm with rfl | rfl | rfl <;> lit_decide

theorem body_eq1 (h : MdHash) (hm : h ∈ VG.Proof.Variants.MdHash.X86_64.sha1Variants) (v : RoundImpl) :
    body h v 128 = fillI (ptSigma v) (bodyStub h 128) := by
  simp only [VG.Proof.Variants.MdHash.X86_64.sha1Variants, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl <;>
    (unfold body RefillBackend.backendCode VG.Proof.Dsa.X86_64.Generation.PrimeTest.run bodyStub; kernel_rfl)

theorem body_eq256 (h : MdHash) (hm : h ∈ VG.Proof.Variants.MdHash.X86_64.sha256Variants) (v : RoundImpl)
    (p : Nat) (hp : p = 256 ∨ p = 384) : body h v p = fillI (ptSigma v) (bodyStub h p) := by
  simp only [VG.Proof.Variants.MdHash.X86_64.sha256Variants, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hp with rfl | rfl <;> rcases hm with rfl | rfl | rfl <;>
    (unfold body RefillBackend.backendCode VG.Proof.Dsa.X86_64.Generation.PrimeTest.run bodyStub; kernel_rfl)

/-- What the cleanup needs of the search for width `p` with the hash `h` and
Miller–Rabin `v`, from its stub's: its instructions at the level of both, and
that it calls indirectly only `h`'s `update` and `finalize` and the test. -/
theorem body_side (h : MdHash) (v : RoundImpl) (p : Nat) (he : body h v p = fillI (ptSigma v) (bodyStub h p))
    (hs : stubOk h (bodyStub h p) = true) :
    (body h v p).allInstrs (Ins ((hashLevel h).join v.level).level) = true ∧
      ∀ n ∈ UpperLock.inames (body h v p),
        n ∈ [h.H.stream.updN, h.H.stream.finN, (ProbablePrime.primeTest v).name] := by
  simp only [stubOk, Bool.and_eq_true] at hs
  have hp := prime_side v
  simp only [calleeSide, lvAll_eq, Bool.and_eq_true, List.isEmpty_iff] at hp
  rw [he]
  refine ⟨fillI_allInstrs (fun f g d hf => ?_) _ (side_mono (level_join_left _ _) hs.1),
    fillI_inames (fun f g d hf => ?_) _ fun n hn => ?_⟩
  · unfold ptSigma at hf
    split at hf
    · obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hf)
      exact side_mono (level_join_right _ _) hp.1.2
    · cases hf
  · unfold ptSigma at hf
    split at hf
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hf)
      exact ⟨by simp, hp.2⟩
    · cases hf
  · have := List.all_eq_true.mp hs.2 n hn
    simp only [decide_eq_true_eq, List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl
    · exact .inl (by simp)
    · exact .inl (by simp)
    · exact .inr (by simp [ptSigma])

/-! ## The search -/

/-- The level of the search's cleanup over `p` and `v`. -/
def level (p : Hashes) (v : RoundImpl) : VecLevel := ((hashLevel p.sha1).join (hashLevel p.sha256)).join v.level

theorem le1 (a b c : VecLevel) : (a.join c).level ≤ ((a.join b).join c).level := by
  cases a <;> cases b <;> cases c <;> decide

theorem le2 (a b c : VecLevel) : (b.join c).level ≤ ((a.join b).join c).level := by
  cases a <;> cases b <;> cases c <;> decide

theorem width_ins {k : Nat} {u f q n : String} {c : Prog isa} (hc : c.allInstrs (Ins k) = true) :
    (Impl.Dsa.X86_64.ParameterSearch.width (Impl.Dsa.X86_64.ParameterSearch.fnAddrs u f q) n c).allInstrs
      (Ins k) = true := by
  change (Ins k (.alloc 56) && (Code.allInstrs (Ins k)
    (.block (Impl.ForwardCall.X86_64.copies 56 2 ++ Impl.Dsa.X86_64.ParameterSearch.fnAddrs u f q)) &&
      c.allInstrs (Ins k)) && Ins k (.free 56)) = true
  rw [hc]; rfl

theorem widths_ins {k : Nat} {u₁ f₁ q₁ u₂ f₂ q₂ u₃ f₃ q₃ n₁ n₂ n₃ : String} {c₁ c₂ c₃ : Prog isa}
    (h₁ : c₁.allInstrs (Ins k) = true) (h₂ : c₂.allInstrs (Ins k) = true) (h₃ : c₃.allInstrs (Ins k) = true) :
    (Impl.Dsa.X86_64.ParameterSearch.widths (Impl.Dsa.X86_64.ParameterSearch.fnAddrs u₁ f₁ q₁)
      (Impl.Dsa.X86_64.ParameterSearch.fnAddrs u₂ f₂ q₂) (Impl.Dsa.X86_64.ParameterSearch.fnAddrs u₃ f₃ q₃)
      n₁ n₂ n₃ c₁ c₂ c₃).allInstrs (Ins k) = true := by
  have w₁ := width_ins (u := u₁) (f := f₁) (q := q₁) (n := n₁) h₁
  have w₂ := width_ins (u := u₂) (f := f₂) (q := q₂) (n := n₂) h₂
  have w₃ := width_ins (u := u₃) (f := f₃) (q := q₃) (n := n₃) h₃
  simp only [Impl.Dsa.X86_64.ParameterSearch.widths, Code.iteCold, Code.allInstrs, w₁, w₂, w₃,
    Bool.and_true]
  rfl

theorem widths_inames {u₁ f₁ q₁ u₂ f₂ q₂ u₃ f₃ q₃ n₁ n₂ n₃ : String} {c₁ c₂ c₃ : Prog isa} :
    UpperLock.inames (Impl.Dsa.X86_64.ParameterSearch.widths (Impl.Dsa.X86_64.ParameterSearch.fnAddrs u₁ f₁ q₁)
      (Impl.Dsa.X86_64.ParameterSearch.fnAddrs u₂ f₂ q₂) (Impl.Dsa.X86_64.ParameterSearch.fnAddrs u₃ f₃ q₃)
      n₁ n₂ n₃ c₁ c₂ c₃) = UpperLock.inames c₁ ++ (UpperLock.inames c₂ ++ UpperLock.inames c₃) := by
  simp only [Impl.Dsa.X86_64.ParameterSearch.widths, Impl.Dsa.X86_64.ParameterSearch.width, Code.iteCold,
    UpperLock.inames, List.nil_append, List.append_nil]

theorem widths_depth {u₁ f₁ q₁ u₂ f₂ q₂ u₃ f₃ q₃ n₁ n₂ n₃ : String} {c₁ c₂ c₃ : Prog isa}
    (h₁ : c₁.x86_64Depth ≤ 568) (h₂ : c₂.x86_64Depth ≤ 568) (h₃ : c₃.x86_64Depth ≤ 568) :
    (Impl.Dsa.X86_64.ParameterSearch.widths (Impl.Dsa.X86_64.ParameterSearch.fnAddrs u₁ f₁ q₁)
      (Impl.Dsa.X86_64.ParameterSearch.fnAddrs u₂ f₂ q₂) (Impl.Dsa.X86_64.ParameterSearch.fnAddrs u₃ f₃ q₃)
      n₁ n₂ n₃ c₁ c₂ c₃).x86_64Depth ≤ 632 := by
  simp only [Impl.Dsa.X86_64.ParameterSearch.widths, Impl.Dsa.X86_64.ParameterSearch.width, Code.iteCold,
    Code.x86_64Depth, Instr.frameBytes, Nat.zero_max, Nat.max_zero, Nat.max_le]
  omega

/-- `verifiedScrubbedAllFns` for the search's code `c`, whose contract makes
public the addresses of the functions it calls indirectly (`Abi.withFns`). -/
theorem scrubbedFns {c : Prog isa} {x : String} {xs : List String} (v : VecLevel)
    (h : Verified target c (Proof.Dsa.parameterSearchAskedContract (abi.withFns (x :: xs)) 632))
    (hsp : c.all (fun i => !isa.writesSp i) = true) (hd : c.x86_64Depth ≤ 632)
    (hins : c.allInstrs (Ins v.level) = true) (hin : ∀ n ∈ UpperLock.inames c, n ∈ x :: xs) :
    VerifiedScrubbed target (scrubAll v 32 632 c) (Proof.Dsa.parameterSearchAskedContract (abi.withFns (x :: xs)) 632)
      32 := by
  obtain ⟨hlv, hmx⟩ := allInstrs_level (Nat.le_refl _) hins
  exact verifiedScrubbedAllFns v h (Proof.Dsa.X86_64.Scrub.parameterSearchOut 632) hsp hd hlv
    (mxSame_of_noLoad hmx) hin

/-- `Proof.Dsa.parameterSearchAskedApi`'s function as emitted over `p` and `v`
meets its contract in constant time and returns without secret residue. -/
theorem search_asked (p : Hashes) (v : RoundImpl) :
    VerifiedScrubbed target
      (Impl.Dsa.X86_64.Fn.parameterSearch (level p v) (addrs p.sha1 v) (addrs p.sha256 v) (addrs p.sha256 v)
        (name 128) (name 256) (name 384) (body p.sha1 v 128) (body p.sha256 v 256) (body p.sha256 v 384))
      (Proof.Dsa.parameterSearchAskedApi.contract (X86_64.abi.withFns (fns p.sha1 p.sha256 v)) 632) 32 := by
  obtain ⟨i₁, n₁⟩ := body_side p.sha1 v 128 (body_eq1 p.sha1 p.mem1 v) (stub_sha1 p.sha1 p.mem1)
  obtain ⟨i₂, n₂⟩ := body_side p.sha256 v 256 (body_eq256 p.sha256 p.mem256 v 256 (.inl rfl))
    (stub_sha256 p.sha256 p.mem256 256 (.inl rfl))
  obtain ⟨i₃, n₃⟩ := body_side p.sha256 v 384 (body_eq256 p.sha256 p.mem256 v 384 (.inr rfl))
    (stub_sha256 p.sha256 p.mem256 384 (.inr rfl))
  refine scrubbedFns (level p v) (RefillBackend.search_verified p.sha1 p.sha256 v p.h1 p.h256)
    (RefillBackend.searchCode_spSafe p.sha1 p.sha256 v)
    (widths_depth (RefillBackend.single_depth _ _ _) (RefillBackend.single_depth _ _ _)
      (RefillBackend.single_depth _ _ _))
    (widths_ins (side_mono (le1 _ _ _) i₁) (side_mono (le2 _ _ _) i₂) (side_mono (le2 _ _ _) i₃)) ?_
  intro n hn
  simp only [RefillBackend.addrs, widths_inames, List.mem_append] at hn
  rcases hn with hn | hn | hn
  · have := n₁ n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl <;> simp
  · have := n₂ n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl <;> simp
  · have := n₃ n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl <;> simp

theorem search_scrubbed (p : Hashes) (v : RoundImpl) :
    VerifiedScrubbed target
      (Impl.Dsa.X86_64.Fn.parameterSearch (level p v) (addrs p.sha1 v) (addrs p.sha256 v) (addrs p.sha256 v)
        (name 128) (name 256) (name 384) (body p.sha1 v 128) (body p.sha256 v 256) (body p.sha256 v 384))
      (Spec.Dsa.parameterSearchContract (X86_64.abi.withFns (fns p.sha1 p.sha256 v)) 632) 32 :=
  Proof.Dsa.parameterSearch_imp (search_asked p v) id

theorem search_public (p : Hashes) (v : RoundImpl) :
    Spec.Dsa.parameterSearchOut.Of X86_64.abi
      (Impl.Dsa.X86_64.Fn.parameterSearch (level p v) (addrs p.sha1 v) (addrs p.sha256 v) (addrs p.sha256 v)
        (name 128) (name 256) (name 384) (body p.sha1 v 128) (body p.sha256 v 256) (body p.sha256 v 384))
      (Spec.Dsa.parameterSearchContract (X86_64.abi.withFns (fns p.sha1 p.sha256 v)) 632) :=
  Proof.Dsa.parameterSearch_public (search_asked p v)

theorem search_spSafe (p : Hashes) (v : RoundImpl) :
    (Impl.Dsa.X86_64.Fn.parameterSearch (level p v) (addrs p.sha1 v) (addrs p.sha256 v) (addrs p.sha256 v)
      (name 128) (name 256) (name 384) (body p.sha1 v 128) (body p.sha256 v 256) (body p.sha256 v 384)).all
      (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (RefillBackend.searchCode_spSafe p.sha1 p.sha256 v)

end VG.Proof.Dsa.X86_64.Generation.SearchScrub
