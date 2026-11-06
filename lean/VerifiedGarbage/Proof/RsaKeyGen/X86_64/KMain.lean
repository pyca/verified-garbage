module

import VerifiedGarbage.Proof.RsaKeyGen.X86_64.KTail
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Close
public import VerifiedGarbage.Proof.RsaKeyGen.CandSpec
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.KEnd
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.LoadC
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrRound
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.TrialLoop
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.GcdE

/-!
# A candidate on x86-64: once `rand` has its octets

`MainCtx`: what `kMainWith` needs from the header and the buffers, and
what its stages keep.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- What `kMainWith` needs, for the `k` octets of a prime. -/
structure MainCtx (s : State) (B : Addr) (Z k : Nat) (op up eP pP rP : Addr) (eB pB r : List Byte) : Prop where
  scr : Scr s B Z
  rdi : s.gpr .rdi = B
  z : slot (k / 8) aTab + 2048 ≤ Z
  zx : slot (k / 8) aRm1 + 8 * (k / 8 + 2) ≤ Z
  k1 : 32 ≤ k
  k2 : k ≤ 512
  k8 : k % 8 = 0
  out : word s.mem B (8 * kOut) = op
  len : word s.mem B (8 * kLen) = BitVec.ofNat 64 k
  usedP : word s.mem B (8 * kUsedP) = up
  e : word s.mem B (8 * kE) = eP
  elen : word s.mem B (8 * kElen) = BitVec.ofNat 64 eB.length
  p : word s.mem B (8 * kP) = pP
  plen : word s.mem B (8 * kPlen) = BitVec.ofNat 64 pB.length
  rand : word s.mem B (8 * kRand) = rP
  rlen : word s.mem B (8 * kRandLen) = BitVec.ofNat 64 r.length
  esrc : Src s B Z eP eB
  psrc : Src s B Z pP pB
  rsrc : Src s B Z rP r
  el1 : 1 ≤ eB.length
  el8 : eB.length ≤ 8
  pl : pB.length = 0 ∨ pB.length = k
  rl : r.length < 2 ^ 64
  rk : k ≤ r.length
  ou : OutUp s B Z op up k

theorem seg_zero (r : List Byte) (n : Nat) : VG.Proof.RsaKeyGen.seg r 0 n = r.take n := by
  simp [VG.Proof.RsaKeyGen.seg]

/-- A stage past `loadC` keeps the first 26 header words and memory past
the scratch space. -/
theorem stage {B : Addr} {Z : Nat} {m₀ m m' : Mem} {rs : List (Nat × Nat)} (hf : Frm B rs m m')
    (h208 : ∀ r ∈ rs, 208 ≤ r.1) (hrZ : ∀ r ∈ rs, r.1 + r.2 ≤ Z)
    (h : (∀ i ≤ 25, word m B (8 * i) = word m₀ B (8 * i)) ∧ InScr B Z m₀ m) :
    (∀ i ≤ 25, word m' B (8 * i) = word m₀ B (8 * i)) ∧ InScr B Z m₀ m' :=
  ⟨fun i hi => (hf.word_eq (fun r hr => Or.inl (by have := h208 r hr; omega_arith)) (by omega_arith)).trans (h.1 i hi),
    h.2.trans (InScr.of_frm hf hrZ)⟩

/-- `finUsed st` ends a candidate. -/
theorem finUsed_end {s sX : State} {B : Addr} {Z : Nat} {op up : Addr} {k st u : Nat} (hs : Scr sX B Z)
    (hdi : sX.gpr .rdi = B) (h8 : 8 * 32 ≤ Z) (hst : st < 2 ^ 31) (hu : word sX.mem B (8 * kUsed) = BitVec.ofNat 64 u)
    (hU : word sX.mem B (8 * kUsedP) = up) (ho : OutUp sX B Z op up k)
    (hlo : ∀ i < 6, word sX.mem B (8 * i) = word s.mem B (8 * i)) (hhi : InScr B Z s.mem sX.mem)
    (kk : Keep mmRegs s sX) :
    WP isa (finUsed st) sX fun t => KEnd s t B Z op up k st u none :=
  WP.mono (finUsed_ok hs hdi h8 hst hu hU ho.upw ho.upZ) fun _ h =>
    (KEnd.of_fin ho h).trans_pre hlo (fun x hx => hhi x hx) kk ho.outZ

/-- What `kMainWith`'s frames need of the ranges `closeCheck` changes. -/
theorem closeRanges_fr (w : Nat) : (∀ r ∈ closeRanges w, 208 ≤ r.1) ∧ (∀ r ∈ closeRanges w, r.1 + r.2 ≤ slot w 8) ∧
    (∀ r ∈ closeRanges w, slot w aN + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w aN) ∧
    (∀ r ∈ closeRanges w, r.1 + r.2 ≤ slot w aTab + 2048) := by
  have hs : VG.Proof.RsaKeyGen.SlotShape w (closeRanges w) [] [aX, aAcc, aTmp] := fun r hr => by
    simp only [closeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [.inr ⟨_, .head _, rfl⟩, .inr ⟨_, .tail _ (.head _), rfl⟩, .inr ⟨_, .tail _ (.tail _ (.head _)), rfl⟩]
  exact ⟨hs.geD rfl rfl, hs.leD rfl rfl, hs.apartW rfl rfl,
    fun r hr => Nat.le_trans (hs.leD (a := aTab) rfl rfl r hr) (Nat.le_add_right _ _)⟩

/-- The same for the ranges the trial division changes. -/
theorem trialRanges_fr (w : Nat) :
    (∀ r ∈ [(slot w aTab, 2048), (8 * kT0, 8), (8 * kT1, 8), (8 * kT2, 8)], 208 ≤ r.1) ∧
    (∀ r ∈ [(slot w aTab, 2048), (8 * kT0, 8), (8 * kT1, 8), (8 * kT2, 8)], r.1 + r.2 ≤ slot w aTab + 2048) ∧
    (∀ r ∈ [(slot w aTab, 2048), (8 * kT0, 8), (8 * kT1, 8), (8 * kT2, 8)],
      slot w aN + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w aN) :=
  ⟨by rng_le, by rng_le, by rng_disj⟩

/-- The same for the ranges the gcd check changes. -/
theorem gcdRanges_fr (w : Nat) :
    (∀ r ∈ [(slot w aX, 8 * (w + 2)), (8 * kG, 8)], 208 ≤ r.1) ∧
    (∀ r ∈ [(slot w aX, 8 * (w + 2)), (8 * kG, 8)], r.1 + r.2 ≤ slot w 8) ∧
    (∀ r ∈ [(slot w aX, 8 * (w + 2)), (8 * kG, 8)], slot w aN + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w aN) ∧
    (∀ r ∈ [(slot w aX, 8 * (w + 2)), (8 * kG, 8)], r.1 + r.2 ≤ slot w aTab + 2048) := by
  have hs : VG.Proof.RsaKeyGen.SlotShape w [(slot w aX, 8 * (w + 2)), (8 * kG, 8)] [(8 * kG, 8)] [aX] :=
    fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [.inr ⟨_, .head _, rfl⟩, .inl (.head _)]
  exact ⟨hs.geD rfl rfl, hs.leD rfl rfl, hs.apartW rfl rfl,
    fun r hr => Nat.le_trans (hs.leD (a := aTab) rfl rfl r hr) (Nat.le_add_right _ _)⟩

/-- The header words `kMainWith` keeps across `loadC`. -/
theorem loadCRanges_hdr (w : Nat) : ∀ i ∈ [kOut, kLen, kUsedP, kE, kElen, kP, kPlen, kRand, kRandLen],
    ∀ r ∈ loadCRanges w, 8 * i + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * i := by
  have h : ∀ i ∈ [kOut, kLen, kUsedP, kE, kElen, kP, kPlen, kRand, kRandLen], 8 * i + 8 ≤ VG.Impl.Bignum.hdrBytes ∧
      ∀ h ∈ ([(48, 8), (64, 64), (200, 8)] : List (Nat × Nat)), 8 * i + 8 ≤ h.1 ∨ h.1 + h.2 ≤ 8 * i := by
    decide
  exact fun i hi => VG.Proof.RsaKeyGen.hdr_of_shape (loadCRanges_shape w) (h i hi).1 (h i hi).2

end VG.Proof.RsaKeyGen.X86_64
