module

import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedMain
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedEnd
public import VerifiedGarbage.Impl.RsaKeyGen.X86_64.SharedCandidate
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Kernel
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedCall
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.KTail
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrShift
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedRanges

/-! # Montgomery setup and RSA's shared Miller–Rabin witness loop -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.MillerRabin.X86_64
open VG.Proof.MlKem.X86_64

/-- How a primality test's result ends a candidate `c`. -/
def SharedTestEnd (s t : State) (B sp : Addr) (Z : Nat) (op up : Addr) (k : Nat) (r : List Byte) (c : Nat) :
    Option (Bool × List Byte) → Prop
  | none => SharedKEnd s t B sp Z op up k 0 0 none
  | some (true, rest) => SharedKEnd s t B sp Z op up k 1 (r.length - rest.length) (some c)
  | some (false, rest) => SharedKEnd s t B sp Z op up k 3 (r.length - rest.length) none

/-- `montSetup`, `millerRabin` and `mrResult`, for the candidate `c` in
`aN`, from offset `8 w` of `rand`. -/
theorem sharedKTail_ok (M : Mont) {mm : Nat → Nat → Nat → Prog isa} (hmc : MmCalls M mm) (R : Kernel) {s : State} {B sp : Addr} {Z w : Nat} {mi : BitVec 64} {c : Nat} {op up rp : Addr}
    {r : List Byte} (henv : SharedEnv B Z sp s) (hZ28 : slot w 28 ≤ Z) (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z) (hXZ : slot w aRm1 + 8 * (w + 2) ≤ Z) (hw4 : 4 ≤ w)
    (hw64 : w ≤ 64) (hn : wv s.mem B (slot w aN) w = c) (hsh : VG.Proof.RsaKeyGen.PrimeShape (64 * w) c)
    (ho : OutUp s B Z op up (8 * w)) (hO : word s.mem B (8 * kOut) = op)
    (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w)) (hU : word s.mem B (8 * kUsedP) = up)
    (hrp : word s.mem B (8 * kRand) = rp) (hrlen : word s.mem B (8 * kRandLen) = BitVec.ofNat 64 r.length)
    (hus : word s.mem B (8 * kUsed) = BitVec.ofNat 64 (8 * w)) (hsrc : Src s B Z rp r) (hrl : r.length < 2 ^ 64)
    (hrk : 8 * w ≤ r.length) :
    WP isa (seqs (montSetup mm ++ expSetup ++ millerRabinWith mm R.run ++ [mrResult])) s fun t =>
      SharedTestEnd s t B sp Z op up (8 * w) r c (Spec.RsaKeyGen.primalityTest c (r.drop (8 * w))) := by
  have hnw := hg.scr.nowrap
  have hd : MrDims B Z w := ⟨hZ, hXZ, hw4, by omega_arith⟩
  obtain ⟨hodd, hlo, hhi⟩ := hsh
  have htop : 2 ^ (64 * w - 1) ≤ c := by
    have : 2 ^ (64 * w - 1) = 2 ^ (64 * w - 2) * 2 := by rw [← Nat.pow_succ]; congr 1; omega_arith
    omega_arith
  have hc1 : 1 < c := by
    have : 2 ≤ 2 ^ (64 * w - 1) := Nat.le_trans (by decide) (Nat.pow_le_pow_right (by decide) (show 1 ≤ 64 * w - 1 by omega_arith))
    omega_arith
  rw [List.append_assoc, List.append_assoc]
  refine wp_seqs_append (by simp [montSetup]) (by simp [expSetup, lowWord]) ?_
  refine WP.mono (montSetup_call_ok M hmc henv hg hZ hXZ hw4 hw64 hn hodd htop) fun s₀ ⟨mi', hg₀, hinv₀, hr2₀, hr1₀, hrm₀, hch₀,
    hf₀, k₀⟩ => ?_
  have hn₀ : wv s₀.mem B (slot w aN) w = c := by
    rw [SharedFrame.array hf₀ henv (d := slot w aN) (k := w) (by simp only [msRanges]; rng_disj)
      (by have := slot_le (w := w) (show aN < 8 by decide); omega_arith) hnw]; exact hn
  refine wp_seqs_append (by simp [expSetup, lowWord]) (by simp [millerRabinWith]) ?_
  refine WP.mono (expSetup_ok hg₀ hd hn₀ hodd hc1) fun s₁ ⟨hE₁, hfE, hg₁, kEx⟩ => ?_
  have hf₁ : SharedFrame B sp (msRanges w ++ [(slot w aE, 8 * (w + 1))]) s.mem s₁.mem :=
    (hf₀.mono fun r hr => List.mem_append_left _ hr).trans (hfE.work.mono fun r hr => List.mem_append_right _ hr)
  have k₁ : Keep mmRegs s s₁ := (k₀.trans kEx).mono (by decide)
  have hEw : ∀ {d k : Nat}, d + 8 * k ≤ slot w aE ∨ slot w aE + 8 * (w + 1) ≤ d → d + 8 * k ≤ 2 ^ 64 →
      wv s₁.mem B d k = wv s₀.mem B d k := fun h h' => hfE.wv_eq (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact h) h'
  have hinv₁ : ((word s₁.mem B (slot w aN)).toNat * mi'.toNat + 1) % 2 ^ 64 = 0 := by
    rw [hfE.word_eq (d := slot w aN) (by rng_disj) (by have := slot_le (w := w) (show aN < 8 by decide); omega_arith)]
    exact hinv₀
  have hr2₁ : wv s₁.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c := by
    rw [hEw (Or.inl (by simp only [slot, hdrBytes, aR2, aE]; omega)) (by have := slot_le (w := w) (show aR2 < 8 by decide); omega_arith)]; exact hr2₀
  have hr1₁ : wv s₁.mem B (slot w aR1) w = 2 ^ (64 * w) % c := by
    rw [hEw (Or.inr (by simp only [slot, hdrBytes, aR1, aE]; omega)) (by unfold slot aR1 aRm1 at *; omega_arith)]; exact hr1₀
  have hrm₁ : wv s₁.mem B (slot w aRm1) w = c - 2 ^ (64 * w) % c := by
    rw [hEw (Or.inr (by simp only [slot, hdrBytes, aRm1, aE]; omega)) (by omega_arith)]; exact hrm₀
  have hch₁ : word s₁.mem B (8 * kChecks) = BitVec.ofNat 64 (checksW w) := by
    rw [hfE.word_eq (d := 8 * kChecks) (by rng_disj) (by unfold kChecks kE sFn; omega_arith)]; exact hch₀
  have hw₁ : ∀ {k}, k = kRand ∨ k = kLen ∨ k = kRandLen ∨ k = kUsed ∨ k = kOut ∨ k = kUsedP →
      word s₁.mem B (8 * k) = word s.mem B (8 * k) := fun {k} hk => by
    have hk32 : k < 32 := by rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hd : ∀ r ∈ msRanges w ++ [(slot w aE, 8 * (w + 1))], 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k := by
      simp only [msRanges, List.cons_append, List.nil_append]
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> rng_disj
    exact SharedFrame.word hf₁ henv hd (by have := hdr_lt_slot w 8 hk32; omega_arith) hnw
  have hsl₁ : ∀ r ∈ msRanges w ++ [(slot w aE, 8 * (w + 1))], r.1 + r.2 ≤ Z := fun r hr => by
    have : r.1 + r.2 ≤ slot w aRm1 + 8 * (w + 2) := by
      revert r hr; simp only [msRanges, List.cons_append, List.nil_append]; rng_le
    omega_arith
  have hc₁ : MrCtx s₁ B Z w mi' c (wv s₁.mem B (slot w aB) w) :=
    ⟨hg₁, hinv₁, by rw [hfE.wv_eq (d := slot w aN) (k := w) (by rng_disj)
      (by have := slot_le (w := w) (show aN < 8 by decide); omega_arith)]; exact hn₀, rfl, hr1₁, hrm₁⟩
  have hsrc₁ := hsrc.shared henv hf₁ hsl₁ k₁
  have hres : mrRest c (checksW w) r 1 0 (8 * w) = Spec.RsaKeyGen.primalityTest c (r.drop (8 * w)) := by
    rw [VG.Proof.RsaKeyGen.primalityTest_cand (by omega_arith) ⟨hodd, hlo, hhi⟩, checksW_eq w (by omega_arith) hw4]
  refine wp_seqs_append (by simp [millerRabinWith]) (by simp) ?_
  refine WP.mono (sharedMillerRabin_ok M hmc R hd hZ28 hc1 ⟨hodd, hlo, hhi⟩ hrl (by unfold checksW; split <;> (try split) <;>
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> decide) (henv.kept k₁ (by decide)) hc₁ hE₁ hr2₁
    (by rw [hw₁ (Or.inl rfl)]; exact hrp) (by rw [hw₁ (Or.inr (Or.inl rfl))]; exact hK)
    (by rw [hw₁ (Or.inr (Or.inr (Or.inl rfl)))]; exact hrlen) hch₁ hsrc₁
    (by rw [hw₁ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]; exact hus) (Nat.le_refl _) hrk)
    fun s₂ ⟨⟨bm, hc₂⟩, h0, h1, hf₂, k₂⟩ => ?_
  rw [hres] at h0 h1
  have hw₂ : ∀ {k}, k = kRand ∨ k = kLen ∨ k = kRandLen ∨ k = kUsed ∨ k = kOut ∨ k = kUsedP →
      k ≠ kUsed → word s₂.mem B (8 * k) = word s.mem B (8 * k) := fun {k} hk hku => by
    have hk32 : k < 32 := by rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [← hw₁ hk]
    refine SharedFrame.word hf₂ henv (sharedRoundRanges_hdr w ?_)
      (by have := hdr_lt_slot w 8 hk32; omega_arith) hnw
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact absurd rfl hku | simp only [true_or, or_true]
  have hsl₂ : ∀ r ∈ sharedRoundRanges w, r.1 + r.2 ≤ Z := fun r hr => by
    have := sharedRoundRanges_le w r hr; omega_arith
  have hhi : ∀ x, ¬(below sp 128).Contains x 1 → Z ≤ ofs B x → s₂.mem x = s.mem x := by
    intro x he hx
    apply Eq.trans (hf₂ x (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact he) (fun r hr => Or.inr (Nat.le_trans (hsl₂ r hr) hx)))
    exact hf₁ x (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact he) (fun r hr => Or.inr (Nat.le_trans (hsl₁ r hr) hx))
  have hout : ∀ j < 8 * w, s₂.mem (op + BitVec.ofNat 64 j) = s.mem (op + BitVec.ofNat 64 j) := by
    intro j hj
    exact hhi _ (henv.clear.miss wr_mem (ho.outw j hj) (by simp)) (ho.outZ j hj)
  have hlo : ∀ i < 6, word s₂.mem B (8 * i) = word s.mem B (8 * i) := fun i hi => by
    have h2 : ∀ r ∈ sharedRoundRanges w, 8 * i + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * i := fun r hr => by
      have : 48 ≤ r.1 := sharedRoundRanges_low w r hr
      omega_arith
    have h1' : ∀ r ∈ msRanges w ++ [(slot w aE, 8 * (w + 1))], 8 * i + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * i := fun r hr => by
      have : 48 ≤ r.1 := by revert r hr; simp only [msRanges, List.cons_append, List.nil_append]; rng_le
      omega_arith
    rw [SharedFrame.word hf₂ henv h2 (by omega_arith) hnw, SharedFrame.word hf₁ henv h1' (by omega_arith) hnw]
  have k12 : Keep mmRegs s s₂ := (k₁.trans k₂).mono (by decide)
  have ho₂ := ho.congr (k12.2.2)
  refine WP.mono (mrResult_ok (r := r) hc₂.good hZ (by omega_arith) (by omega_arith) hc₂.n ho₂
    (by rw [hw₂ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (by decide)]; exact hO)
    (by rw [hw₂ (Or.inr (Or.inl rfl)) (by decide)]; exact hK)
    (by rw [hw₂ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) (by decide)]; exact hU) h0 h1) fun t ht => ?_
  rcases hp : Spec.RsaKeyGen.primalityTest c (r.drop (8 * w)) with _ | ⟨b, rest⟩
  · rw [hp] at ht; exact ht.shared.trans_pre hlo hhi hout k12
  · rw [hp] at ht; cases b <;> exact ht.shared.trans_pre hlo hhi hout k12

end VG.Proof.RsaKeyGen.X86_64
