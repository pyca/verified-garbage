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
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.KMain
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.TrialLoop
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.GcdE

/-! ### `RsaKeyGen.X86_64.SharedTail`, which only this module used -/

section

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

/-- `montSetup`, `millerRabinWith` and `mrResult`, for the candidate `c` in
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
  obtain hd : MrDims B Z w := ⟨hZ, hXZ, hw4, by omega_arith⟩
  obtain ⟨hodd, hlo, hhi⟩ := hsh
  obtain htop : 2 ^ (64 * w - 1) ≤ c := by
    have : 2 ^ (64 * w - 1) = 2 ^ (64 * w - 2) * 2 := by rw [← Nat.pow_succ]; congr 1; omega_arith
    omega_arith
  obtain hc1 : 1 < c := by
    have : 2 ≤ 2 ^ (64 * w - 1) := Nat.le_trans (by decide) (Nat.pow_le_pow_right (by decide) (show 1 ≤ 64 * w - 1 by omega_arith))
    omega_arith
  rw [List.append_assoc, List.append_assoc]
  refine wp_seqs_append (by simp [montSetup]) (by simp [expSetup, lowWord]) ?_
  refine WP.mono (montSetup_call_ok M hmc henv hg hZ hXZ hw4 hw64 hn hodd htop) fun s₀ ⟨mi', hg₀, hinv₀, hr2₀, hr1₀, hrm₀, hch₀,
    hf₀, k₀⟩ => ?_
  obtain hn₀ : wv s₀.mem B (slot w aN) w = c := by
    rw [SharedFrame.array hf₀ henv (d := slot w aN) (k := w) (by simp only [msRanges]; rng_disj)
      (by have := slot_le (w := w) (show aN < 8 by decide); omega_arith) hnw]; exact hn
  refine wp_seqs_append (by simp [expSetup, lowWord]) (by simp [millerRabinWith]) ?_
  refine WP.mono (expSetup_ok hg₀ hd hn₀ hodd hc1) fun s₁ ⟨hE₁, hfE, hg₁, kEx⟩ => ?_
  obtain hf₁ : SharedFrame B sp (msRanges w ++ [(slot w aE, 8 * (w + 1))]) s.mem s₁.mem :=
    (hf₀.mono fun r hr => List.mem_append_left _ hr).trans (hfE.work.mono fun r hr => List.mem_append_right _ hr)
  obtain k₁ : Keep mmRegs s s₁ := (k₀.trans kEx).mono (by decide)
  obtain hEw : ∀ {d k : Nat}, d + 8 * k ≤ slot w aE ∨ slot w aE + 8 * (w + 1) ≤ d → d + 8 * k ≤ 2 ^ 64 →
      wv s₁.mem B d k = wv s₀.mem B d k := fun h h' => hfE.wv_eq (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact h) h'
  obtain hinv₁ : ((word s₁.mem B (slot w aN)).toNat * mi'.toNat + 1) % 2 ^ 64 = 0 := by
    rw [hfE.word_eq (d := slot w aN) (by rng_disj) (by have := slot_le (w := w) (show aN < 8 by decide); omega_arith)]
    exact hinv₀
  obtain hr2₁ : wv s₁.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c := by
    rw [hEw (Or.inl (by simp only [slot, hdrBytes, aR2, aE]; omega_using [])) (by have := slot_le (w := w) (show aR2 < 8 by decide); omega_arith)]; exact hr2₀
  obtain hr1₁ : wv s₁.mem B (slot w aR1) w = 2 ^ (64 * w) % c := by
    rw [hEw (Or.inr (by simp only [slot, hdrBytes, aR1, aE]; omega_using [])) (by unfold slot aR1 aRm1 at *; omega_arith)]; exact hr1₀
  obtain hrm₁ : wv s₁.mem B (slot w aRm1) w = c - 2 ^ (64 * w) % c := by
    rw [hEw (Or.inr (by simp only [slot, hdrBytes, aRm1, aE]; omega_using [])) (by omega_arith)]; exact hrm₀
  obtain hch₁ : word s₁.mem B (8 * kChecks) = BitVec.ofNat 64 (checksW w) := by
    rw [hfE.word_eq (d := 8 * kChecks) (by rng_disj) (by unfold kChecks kE sFn; omega_arith)]; exact hch₀
  obtain hw₁ : ∀ {k}, k = kRand ∨ k = kLen ∨ k = kRandLen ∨ k = kUsed ∨ k = kOut ∨ k = kUsedP →
      word s₁.mem B (8 * k) = word s.mem B (8 * k) := fun {k} hk => by
    obtain hk32 : k < 32 := by rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    obtain hd : ∀ r ∈ msRanges w ++ [(slot w aE, 8 * (w + 1))], 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k := by
      simp only [msRanges, List.cons_append, List.nil_append]
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> rng_disj
    exact SharedFrame.word hf₁ henv hd (by have := hdr_lt_slot w 8 hk32; omega_arith) hnw
  obtain hsl₁ : ∀ r ∈ msRanges w ++ [(slot w aE, 8 * (w + 1))], r.1 + r.2 ≤ Z := fun r hr => by
    have : r.1 + r.2 ≤ slot w aRm1 + 8 * (w + 2) := by
      revert r hr; simp only [msRanges, List.cons_append, List.nil_append]; rng_le
    omega_arith
  obtain hc₁ : MrCtx s₁ B Z w mi' c (wv s₁.mem B (slot w aB) w) :=
    ⟨hg₁, hinv₁, by rw [hfE.wv_eq (d := slot w aN) (k := w) (by rng_disj)
      (by have := slot_le (w := w) (show aN < 8 by decide); omega_arith)]; exact hn₀, rfl, hr1₁, hrm₁⟩
  obtain hsrc₁ := hsrc.shared henv hf₁ hsl₁ k₁
  obtain hres : mrRest c (checksW w) r 1 0 (8 * w) = Spec.RsaKeyGen.primalityTest c (r.drop (8 * w)) := by
    rw [VG.Proof.RsaKeyGen.primalityTest_cand (by omega_arith) ⟨hodd, hlo, hhi⟩, checksW_eq w (by omega_arith) hw4]
  refine wp_seqs_append (by simp [millerRabinWith]) (by simp) ?_
  refine WP.mono (sharedMillerRabin_ok M hmc R hd hZ28 hc1 ⟨hodd, hlo, hhi⟩ hrl (by unfold checksW; split <;> (try split) <;>
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> decide) (henv.kept k₁ (by decide)) hc₁ hE₁ hr2₁
    (by rw [hw₁ (Or.inl rfl)]; exact hrp) (by rw [hw₁ (Or.inr (Or.inl rfl))]; exact hK)
    (by rw [hw₁ (Or.inr (Or.inr (Or.inl rfl)))]; exact hrlen) hch₁ hsrc₁
    (by rw [hw₁ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]; exact hus) (Nat.le_refl _) hrk)
    fun s₂ ⟨⟨bm, hc₂⟩, h0, h1, hf₂, k₂⟩ => ?_
  rw [hres] at h0 h1
  obtain hw₂ : ∀ {k}, k = kRand ∨ k = kLen ∨ k = kRandLen ∨ k = kUsed ∨ k = kOut ∨ k = kUsedP →
      k ≠ kUsed → word s₂.mem B (8 * k) = word s.mem B (8 * k) := fun {k} hk hku => by
    obtain hk32 : k < 32 := by rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [← hw₁ hk]
    refine SharedFrame.word hf₂ henv (sharedRoundRanges_hdr w ?_)
      (by have := hdr_lt_slot w 8 hk32; omega_arith) hnw
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact absurd rfl hku | simp only [true_or, or_true]
  obtain hsl₂ : ∀ r ∈ sharedRoundRanges w, r.1 + r.2 ≤ Z := fun r hr => by
    have := sharedRoundRanges_le w r hr; omega_arith
  obtain hhi : ∀ x, ¬(below sp 128).Contains x 1 → Z ≤ ofs B x → s₂.mem x = s.mem x := by
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
  obtain hout : ∀ j < 8 * w, s₂.mem (op + BitVec.ofNat 64 j) = s.mem (op + BitVec.ofNat 64 j) := by
    intro j hj
    exact hhi _ (henv.clear.miss wr_mem (ho.outw j hj) (by simp)) (ho.outZ j hj)
  obtain hlo : ∀ i < 6, word s₂.mem B (8 * i) = word s.mem B (8 * i) := fun i hi => by
    obtain h2 : ∀ r ∈ sharedRoundRanges w, 8 * i + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * i := fun r hr => by
      have : 48 ≤ r.1 := sharedRoundRanges_low w r hr
      omega_arith
    obtain h1' : ∀ r ∈ msRanges w ++ [(slot w aE, 8 * (w + 1))], 8 * i + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * i := fun r hr => by
      have : 48 ≤ r.1 := by revert r hr; simp only [msRanges, List.cons_append, List.nil_append]; rng_le
      omega_arith
    rw [SharedFrame.word hf₂ henv h2 (by omega_arith) hnw, SharedFrame.word hf₁ henv h1' (by omega_arith) hnw]
  obtain k12 : Keep mmRegs s s₂ := (k₁.trans k₂).mono (by decide)
  obtain ho₂ := ho.congr (k12.2.2)
  refine WP.mono (mrResult_ok (r := r) hc₂.good hZ (by omega_arith) (by omega_arith) hc₂.n ho₂
    (by rw [hw₂ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (by decide)]; exact hO)
    (by rw [hw₂ (Or.inr (Or.inl rfl)) (by decide)]; exact hK)
    (by rw [hw₂ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) (by decide)]; exact hU) h0 h1) fun t ht => ?_
  rcases hp : Spec.RsaKeyGen.primalityTest c (r.drop (8 * w)) with _ | ⟨b, rest⟩
  · rw [hp] at ht; exact ht.shared.trans_pre hlo hhi hout k12
  · rw [hp] at ht; cases b <;> exact ht.shared.trans_pre hlo hhi hout k12

end VG.Proof.RsaKeyGen.X86_64

end

end


/-! # All candidate checks followed by the shared prepared round -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.MillerRabin.X86_64
open VG.Proof.MlKem.X86_64

theorem kMainWith_eq (mul : Nat → Nat → Nat → Prog isa) (body : Prog isa) : kMainWith mul body =
    seqs (loadC ++ (closeCheck ++ ([.ite .ne (finUsed 2) (seqs (trial ++
      ([.ite .ne (finUsed 3) (seqs (gcdCheck ++
        ([.ite .ne (finUsed 3) (seqs (montSetup mul ++ expSetup ++ millerRabinWith mul body ++ [mrResult]))] : List (Prog isa))))] : List (Prog isa))))] : List (Prog isa)))) := by
  unfold kMainWith; rw [List.append_assoc]

/-- `kMainWith`. -/
theorem sharedKMain_ok (M : Mont) {mm : Nat → Nat → Nat → Prog isa} (hmc : MmCalls M mm) (R : Kernel) {s : State} {B sp : Addr} {Z w : Nat} {op up eP pP rP : Addr} {eB pB r : List Byte}
    (henv : SharedEnv B Z sp s) (hZ28 : slot w 28 ≤ Z) (h : MainCtx s B Z (8 * w) op up eP pP rP eB pB r) :
    WP isa (kMainWith mm R.run) s fun t => SharedCandEnd s t B sp Z op up (8 * w) r
      (VG.Proof.RsaKeyGen.afterDraw (64 * w) (Spec.Rsa.os2ip eB) (Spec.RsaKeyGen.otherPrime pB)
        (Spec.RsaKeyGen.candidate (64 * w) (Spec.Rsa.os2ip (r.take (8 * w)))) (r.drop (8 * w))) := by
  have hs := h.scr
  have hn := hs.nowrap
  have hk1 := h.k1
  have hk2 := h.k2
  obtain hw8 : 8 * w / 8 = w := by omega_arith
  have hTZ := h.z
  rw [hw8] at hTZ
  obtain hZ : slot w 8 ≤ Z := by unfold slot aTab at *; omega_arith
  obtain hl8 : 8 * 32 ≤ Z := by have := hdr_lt_slot w 8 (show 31 < 32 by decide); omega_arith
  rw [kMainWith_eq]
  refine wp_seqs_append (by simp [loadC]) (by simp [closeCheck]) ?_
  -- The candidate.
  obtain hsrcr : Src s B Z rP (r.take (8 * w)) := by
    have := VG.Proof.RsaKeyGen.X86_64.Src.seg h.rsrc (a := 0) (n := 8 * w) (by have := h.rk; omega_arith)
    rwa [seg_zero, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at this
  refine WP.mono (loadC_ok hs h.rdi (by rw [hw8]; exact hZ) (by omega_arith) (by omega_arith) (by omega_arith) h.len h.rand hsrcr
    (by simp; have := h.rk; omega_arith)) fun s₁ ⟨hc₁, hus₁, hsw₁, harr₁, hf₁, hdi₁, h12₁, k₁⟩ => ?_
  rw [hw8, show 8 * (8 * w) = 64 * w by omega_arith] at hc₁
  rw [hw8] at hsw₁ harr₁ hf₁
  generalize hcv : Spec.RsaKeyGen.candidate (64 * w) (Spec.Rsa.os2ip (r.take (8 * w))) = c at hc₁ ⊢
  obtain hsh : VG.Proof.RsaKeyGen.PrimeShape (64 * w) c := hcv ▸ VG.Proof.RsaKeyGen.candidate_shape (by omega_arith) _
  obtain hg₁ : Good s₁ B Z w (word s₁.mem B (8 * sMinv)) := ⟨hs.congr k₁.2.2, hdi₁, ⟨hsw₁, rfl, harr₁⟩⟩
  obtain hh₁ : ∀ {i}, i = kOut ∨ i = kLen ∨ i = kUsedP ∨ i = kE ∨ i = kElen ∨ i = kP ∨ i = kPlen ∨ i = kRand ∨
      i = kRandLen → word s₁.mem B (8 * i) = word s.mem B (8 * i) := fun {i} hi => by
    obtain hi32 : i < 32 := by rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    refine hf₁.word_eq ?_ (by omega_arith)
    simp only [loadCRanges]
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rng_disj
  obtain hin₁ : InScr B Z s.mem s₁.mem := InScr.of_frm hf₁ (by simp only [loadCRanges]; rng_le)
  obtain hsv₁ : ∀ i < 6, word s₁.mem B (8 * i) = word s.mem B (8 * i) := fun i hi =>
    hf₁.word_eq (fun r hr => Or.inl (by revert r hr; simp only [loadCRanges]; rng_le)) (by omega_arith)
  obtain st₁ : (∀ i ≤ 25, word s₁.mem B (8 * i) = word s₁.mem B (8 * i)) ∧ InScr B Z s₁.mem s₁.mem :=
    ⟨fun _ _ => rfl, InScr.refl _ _ _⟩
  obtain ho₁ := h.ou.congr k₁.2.2
  -- Too close to `p`.
  refine wp_seqs_append (by simp [closeCheck]) (by simp) ?_
  refine WP.mono (closeCheck_ok hg₁ hZ (by omega_arith) (by omega_arith) (by rw [hh₁ (by simp)]; exact h.p)
    (by rw [hh₁ (by simp)]; exact h.len) (by rw [hh₁ (by simp)]; exact h.plen) h.pl (h.psrc.congrK hin₁ k₁))
    fun s₂ ⟨hz₂, hg₂, hf₂, k₂⟩ => ?_
  rw [hc₁] at hz₂
  obtain st₂ := stage hf₂ (by simp only [closeRanges]; rng_le) (fun r hr => by
    have : r.1 + r.2 ≤ slot w 8 := by revert r hr; simp only [closeRanges]; rng_le
    omega_arith) st₁
  obtain k12 : Keep mmRegs s s₂ := (k₁.trans k₂).mono (by decide)
  obtain hsv₂ : ∀ i < 6, word s₂.mem B (8 * i) = word s.mem B (8 * i) := fun i hi =>
    (st₂.1 i (by omega_arith)).trans (hsv₁ i hi)
  obtain hin₂ : InScr B Z s.mem s₂.mem := hin₁.trans st₂.2
  obtain hk₂ : ∀ {i}, i = kOut ∨ i = kLen ∨ i = kUsedP ∨ i = kE ∨ i = kElen ∨ i = kP ∨ i = kPlen ∨ i = kRand ∨
      i = kRandLen → word s₂.mem B (8 * i) = word s.mem B (8 * i) := fun {i} hi => by
    have : i ≤ 25 := by rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [st₂.1 i this, hh₁ hi]
  obtain hu₂ : word s₂.mem B (8 * kUsed) = BitVec.ofNat 64 (8 * w) := by rw [st₂.1 kUsed (by decide), hus₁]
  refine WP.ite (Spec.RsaKeyGen.tooClose (64 * w) (Spec.RsaKeyGen.otherPrime pB) c) (by simp [eval, hz₂])
    (fun hcl => ?_) (fun hcl => ?_)
  · refine WP.mono (sharedFinUsed_end (sp := sp) hg₂.scr hg₂.rdi hl8 (by decide) hu₂ (by rw [hk₂ (by simp)]; exact h.usedP)
      (h.ou.congr k12.2.2) hsv₂ hin₂ k12) fun t ht => ?_
    unfold VG.Proof.RsaKeyGen.afterDraw
    rw [hcl]
    simp only [↓reduceIte, SharedCandEnd, List.length_drop]
    rwa [show r.length - (r.length - 8 * w) = 8 * w by have := h.rk; omega_arith]
  obtain hc₂ : wv s₂.mem B (slot w aN) w = c := by
    rw [hf₂.wv_eq (d := slot w aN) (k := w) (by simp only [closeRanges]; rng_disj)
      (by have := slot_le (w := w) (show aN < 8 by decide); omega_arith)]; exact hc₁
  obtain hgt : 8161 < c := by
    obtain ⟨_, hlo, _⟩ := hsh
    have : 2 ^ 13 ≤ 2 ^ (64 * w - 2) := Nat.pow_le_pow_right (by decide) (by omega_arith)
    omega_arith
  obtain hend : ∀ {sX : State} {mi : BitVec 64}, Good sX B Z w mi → Keep mmRegs s sX →
      (∀ i ≤ 25, word sX.mem B (8 * i) = word s₁.mem B (8 * i)) → InScr B Z s₁.mem sX.mem →
      WP isa (finUsed 3) sX fun t => SharedKEnd s t B sp Z op up (8 * w) 3 (8 * w) none := by
    intro sX mi hgX kX hX hinX
    exact sharedFinUsed_end (sp := sp) hgX.scr hgX.rdi hl8 (by decide) (by rw [hX kUsed (by decide), hus₁])
      (by rw [hX kUsedP (by decide), hh₁ (by simp)]; exact h.usedP) (h.ou.congr kX.2.2)
      (fun i hi => (hX i (by omega_arith)).trans (hsv₁ i hi)) (hin₁.trans hinX) kX
  obtain hrej : ∀ t, SharedKEnd s t B sp Z op up (8 * w) 3 (8 * w) none → SharedCandEnd s t B sp Z op up (8 * w) r
      (some (.rejected, r.drop (8 * w))) := fun t ht => by
    simp only [SharedCandEnd, List.length_drop]
    rwa [show r.length - (r.length - 8 * w) = 8 * w by have := h.rk; omega_arith]
  -- Trial division.
  refine wp_seqs_append (by simp [trial]) (by simp) ?_
  refine WP.mono (trial_ok hg₂ hZ hTZ (by omega_arith) (by omega_arith)) fun s₃ ⟨hz₃, hg₃, hf₃, k₃⟩ => ?_
  rw [hc₂, trialAny_eq hgt] at hz₃
  obtain st₃ := stage hf₃ (by rng_le) (fun r hr => by
    have : r.1 + r.2 ≤ slot w aTab + 2048 := by revert r hr; rng_le
    omega_arith) st₂
  obtain k13 : Keep mmRegs s s₃ := (k12.trans k₃).mono (by decide)
  refine WP.ite (Spec.RsaKeyGen.obviouslyComposite (64 * w) c) (by simp [eval, hz₃]) (fun hoc => ?_) (fun hoc => ?_)
  · refine WP.mono (hend hg₃ k13 st₃.1 st₃.2) fun t ht => ?_
    unfold VG.Proof.RsaKeyGen.afterDraw
    simp only [hcl, hoc, Bool.false_eq_true, ↓reduceIte, Bool.not_true, Bool.false_and]
    exact hrej t ht
  obtain hc₃ : wv s₃.mem B (slot w aN) w = c := by
    rw [hf₃.wv_eq (d := slot w aN) (k := w) (by rng_disj)
      (by have := slot_le (w := w) (show aN < 8 by decide); omega_arith)]; exact hc₂
  obtain hk₃ : ∀ {i}, i = kOut ∨ i = kLen ∨ i = kUsedP ∨ i = kE ∨ i = kElen ∨ i = kP ∨ i = kPlen ∨ i = kRand ∨
      i = kRandLen → word s₃.mem B (8 * i) = word s.mem B (8 * i) := fun {i} hi => by
    have : i ≤ 25 := by rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [st₃.1 i this, hh₁ hi]
  -- `gcd(c − 1, e)`.
  refine wp_seqs_append (by simp [gcdCheck, loadE]) (by simp) ?_
  refine WP.mono (gcdCheck_ok hg₃ hZ (by omega_arith) (by omega_arith) (by rw [hc₃]; exact hsh.1)
    (by rw [hc₃]; omega_arith) (by rw [hk₃ (by simp)]; exact h.e) (by rw [hk₃ (by simp)]; exact h.elen) h.el1 h.el8
    (h.esrc.congrK (hin₁.trans st₃.2) k13)) fun s₄ ⟨hz₄, hg₄, hf₄, k₄⟩ => ?_
  rw [hc₃] at hz₄
  obtain st₄ := stage hf₄ (by rng_le) (fun r hr => by
    have : r.1 + r.2 ≤ slot w 8 := by revert r hr; rng_le
    omega_arith) st₃
  obtain k14 : Keep mmRegs s s₄ := (k13.trans k₄).mono (by decide)
  refine WP.ite (!decide (Nat.gcd (c - 1) (Spec.Rsa.os2ip eB) = 1)) (by simp [eval, hz₄]) (fun hgc => ?_)
    (fun hgc => ?_)
  · refine WP.mono (hend hg₄ k14 st₄.1 st₄.2) fun t ht => ?_
    simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hgc
    unfold VG.Proof.RsaKeyGen.afterDraw
    simp only [hcl, hoc, hgc, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and, beq_iff_eq]
    exact hrej t ht
  simp only [Bool.not_eq_false', decide_eq_true_eq] at hgc
  obtain hc₄ : wv s₄.mem B (slot w aN) w = c := by
    rw [hf₄.wv_eq (d := slot w aN) (k := w) (by rng_disj)
      (by have := slot_le (w := w) (show aN < 8 by decide); omega_arith)]; exact hc₃
  obtain hk₄ : ∀ {i}, i = kOut ∨ i = kLen ∨ i = kUsedP ∨ i = kE ∨ i = kElen ∨ i = kP ∨ i = kPlen ∨ i = kRand ∨
      i = kRandLen → word s₄.mem B (8 * i) = word s.mem B (8 * i) := fun {i} hi => by
    have : i ≤ 25 := by rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [st₄.1 i this, hh₁ hi]
  have hXZ := h.zx
  rw [hw8] at hXZ
  refine WP.mono (sharedKTail_ok M hmc R (henv.kept k14 (by decide)) hZ28 hg₄ hZ hXZ (by omega_arith) (by omega_arith) hc₄ hsh (h.ou.congr k14.2.2)
    (by rw [hk₄ (by simp)]; exact h.out) (by rw [hk₄ (by simp)]; exact h.len) (by rw [hk₄ (by simp)]; exact h.usedP)
    (by rw [hk₄ (by simp)]; exact h.rand) (by rw [hk₄ (by simp)]; exact h.rlen)
    (by rw [st₄.1 kUsed (by decide), hus₁]) (h.rsrc.congrK (hin₁.trans st₄.2) k14) h.rl h.rk) fun t ht => ?_
  obtain hlo : ∀ i < 6, word s₄.mem B (8 * i) = word s.mem B (8 * i) := fun i hi =>
    (st₄.1 i (by omega_arith)).trans (hsv₁ i hi)
  obtain hhi : ∀ x, Z ≤ ofs B x → s₄.mem x = s.mem x := fun x hx => ((hin₁.trans st₄.2) x hx)
  unfold VG.Proof.RsaKeyGen.afterDraw
  simp only [hcl, hoc, hgc, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and, beq_self_eq_true]
  rcases hp : Spec.RsaKeyGen.primalityTest c (r.drop (8 * w)) with _ | ⟨b, rest⟩
  · rw [hp] at ht; exact SharedKEnd.trans_pre ht hlo (fun x _ hx => hhi x hx) (fun j hj => hhi _ (h.ou.outZ j hj)) k14
  · rw [hp] at ht
    cases b
    · exact SharedKEnd.trans_pre ht hlo (fun x _ hx => hhi x hx) (fun j hj => hhi _ (h.ou.outZ j hj)) k14
    · exact SharedKEnd.trans_pre ht hlo (fun x _ hx => hhi x hx) (fun j hj => hhi _ (h.ou.outZ j hj)) k14

end VG.Proof.RsaKeyGen.X86_64
