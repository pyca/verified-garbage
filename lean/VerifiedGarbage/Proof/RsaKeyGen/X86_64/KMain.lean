import VerifiedGarbage.Proof.RsaKeyGen.X86_64.KTail
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Close
import VerifiedGarbage.Proof.RsaKeyGen.Table

/-!
# A candidate on x86-64: once `rand` has its octets

`kMain_ok`: from the header and the buffers, `kMain` ends as `afterDraw`
for the candidate from the first `k` octets of `rand` (`CandEnd`).
-/

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- How a candidate's result ends it. -/
def CandEnd (s t : State) (B : Addr) (Z : Nat) (op up : Addr) (k : Nat) (r : List Byte) :
    Option (Spec.RsaKeyGen.Candidate × List Byte) → Prop
  | none => KEnd s t B Z op up k 0 0 none
  | some (.prime c, rest) => KEnd s t B Z op up k 1 (r.length - rest.length) (some c)
  | some (.close, rest) => KEnd s t B Z op up k 2 (r.length - rest.length) none
  | some (.rejected, rest) => KEnd s t B Z op up k 3 (r.length - rest.length) none

/-- What `kMain` needs, for the `k` octets of a prime. -/
structure MainCtx (s : State) (B : Addr) (Z k : Nat) (op up eP pP rP : Addr) (eB pB r : List Byte) : Prop where
  scr : Scr s B Z
  rdi : s.gpr .rdi = B
  z : slot (k / 8) aTab + 2048 ≤ Z
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

theorem kMain_eq (mul : Nat → Nat → Nat → Prog isa) : kMain mul =
    seqs (loadC ++ (closeCheck ++ ([.ite .ne (finUsed 2) (seqs (trial ++
      ([.ite .ne (finUsed 3) (seqs (gcdCheck ++
        ([.ite .ne (finUsed 3) (seqs (montSetup mul ++ millerRabin mul ++ [mrResult]))] : List (Prog isa))))] : List (Prog isa))))] : List (Prog isa)))) := by
  unfold kMain; rw [List.append_assoc]

theorem seg_zero (r : List Byte) (n : Nat) : VG.Proof.RsaKeyGen.seg r 0 n = r.take n := by
  simp [VG.Proof.RsaKeyGen.seg]

/-- A stage past `loadC` keeps the first 26 header words and memory past
the scratch space. -/
theorem stage {B : Addr} {Z : Nat} {m₀ m m' : Mem} {rs : List (Nat × Nat)} (hf : Frm B rs m m')
    (h208 : ∀ r ∈ rs, 208 ≤ r.1) (hrZ : ∀ r ∈ rs, r.1 + r.2 ≤ Z)
    (h : (∀ i ≤ 25, word m B (8 * i) = word m₀ B (8 * i)) ∧ InScr B Z m₀ m) :
    (∀ i ≤ 25, word m' B (8 * i) = word m₀ B (8 * i)) ∧ InScr B Z m₀ m' :=
  ⟨fun i hi => (hf.word_eq (fun r hr => Or.inl (by have := h208 r hr; omega)) (by omega)).trans (h.1 i hi),
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

/-- `kMain`. -/
theorem kMain_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {op up eP pP rP : Addr} {eB pB r : List Byte}
    (h : MainCtx s B Z (8 * w) op up eP pP rP eB pB r) :
    WP isa (kMain M.mm) s fun t => CandEnd s t B Z op up (8 * w) r
      (VG.Proof.RsaKeyGen.afterDraw (64 * w) (Spec.Rsa.os2ip eB) (Spec.RsaKeyGen.otherPrime pB)
        (Spec.RsaKeyGen.candidate (64 * w) (Spec.Rsa.os2ip (r.take (8 * w)))) (r.drop (8 * w))) := by
  have hs := h.scr
  have hn := hs.nowrap
  have hk1 := h.k1
  have hk2 := h.k2
  have hw8 : 8 * w / 8 = w := by omega
  have hTZ := h.z
  rw [hw8] at hTZ
  have hZ : slot w 8 ≤ Z := by unfold slot aTab at *; omega
  have hl8 : 8 * 32 ≤ Z := by have := hdr_lt_slot w 8 (show 31 < 32 by decide); omega
  rw [kMain_eq]
  refine wp_seqs_append (by simp [loadC]) (by simp [closeCheck]) ?_
  -- The candidate.
  have hsrcr : Src s B Z rP (r.take (8 * w)) := by
    have := VG.Proof.RsaKeyGen.X86_64.Src.seg h.rsrc (a := 0) (n := 8 * w) (by have := h.rk; omega)
    rwa [seg_zero, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at this
  refine WP.mono (loadC_ok hs h.rdi (by rw [hw8]; exact hZ) (by omega) (by omega) (by omega) h.len h.rand hsrcr
    (by simp; have := h.rk; omega)) fun s₁ ⟨hc₁, hus₁, hsw₁, harr₁, hf₁, hdi₁, h12₁, k₁⟩ => ?_
  rw [hw8, show 8 * (8 * w) = 64 * w by omega] at hc₁
  rw [hw8] at hsw₁ harr₁ hf₁
  generalize hcv : Spec.RsaKeyGen.candidate (64 * w) (Spec.Rsa.os2ip (r.take (8 * w))) = c at hc₁ ⊢
  have hsh : VG.Proof.RsaKeyGen.PrimeShape (64 * w) c := hcv ▸ VG.Proof.RsaKeyGen.candidate_shape (by omega) _
  have hg₁ : Good s₁ B Z w (word s₁.mem B (8 * sMinv)) := ⟨hs.congr k₁.2.2, hdi₁, ⟨hsw₁, rfl, harr₁⟩⟩
  have hh₁ : ∀ {i}, i = kOut ∨ i = kLen ∨ i = kUsedP ∨ i = kE ∨ i = kElen ∨ i = kP ∨ i = kPlen ∨ i = kRand ∨
      i = kRandLen → word s₁.mem B (8 * i) = word s.mem B (8 * i) := fun {i} hi => by
    have hi32 : i < 32 := by rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    refine hf₁.word_eq ?_ (by omega)
    simp only [loadCRanges]
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rng_disj
  have hin₁ : InScr B Z s.mem s₁.mem := InScr.of_frm hf₁ (by simp only [loadCRanges]; rng_le)
  have hsv₁ : ∀ i < 6, word s₁.mem B (8 * i) = word s.mem B (8 * i) := fun i hi =>
    hf₁.word_eq (fun r hr => Or.inl (by revert r hr; simp only [loadCRanges]; rng_le)) (by omega)
  have st₁ : (∀ i ≤ 25, word s₁.mem B (8 * i) = word s₁.mem B (8 * i)) ∧ InScr B Z s₁.mem s₁.mem :=
    ⟨fun _ _ => rfl, InScr.refl _ _ _⟩
  have ho₁ := h.ou.congr k₁.2.2
  -- Too close to `p`.
  refine wp_seqs_append (by simp [closeCheck]) (by simp) ?_
  refine WP.mono (closeCheck_ok hg₁ hZ (by omega) (by omega) (by rw [hh₁ (by simp)]; exact h.p)
    (by rw [hh₁ (by simp)]; exact h.len) (by rw [hh₁ (by simp)]; exact h.plen) h.pl (h.psrc.congrK hin₁ k₁))
    fun s₂ ⟨hz₂, hg₂, hf₂, k₂⟩ => ?_
  rw [hc₁] at hz₂
  have st₂ := stage hf₂ (by simp only [closeRanges]; rng_le) (fun r hr => by
    have : r.1 + r.2 ≤ slot w 8 := by revert r hr; simp only [closeRanges]; rng_le
    omega) st₁
  have k12 : Keep mmRegs s s₂ := (k₁.trans k₂).mono (by decide)
  have hsv₂ : ∀ i < 6, word s₂.mem B (8 * i) = word s.mem B (8 * i) := fun i hi =>
    (st₂.1 i (by omega)).trans (hsv₁ i hi)
  have hin₂ : InScr B Z s.mem s₂.mem := hin₁.trans st₂.2
  have hk₂ : ∀ {i}, i = kOut ∨ i = kLen ∨ i = kUsedP ∨ i = kE ∨ i = kElen ∨ i = kP ∨ i = kPlen ∨ i = kRand ∨
      i = kRandLen → word s₂.mem B (8 * i) = word s.mem B (8 * i) := fun {i} hi => by
    have : i ≤ 25 := by rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [st₂.1 i this, hh₁ hi]
  have hu₂ : word s₂.mem B (8 * kUsed) = BitVec.ofNat 64 (8 * w) := by rw [st₂.1 kUsed (by decide), hus₁]
  refine WP.ite (Spec.RsaKeyGen.tooClose (64 * w) (Spec.RsaKeyGen.otherPrime pB) c) (by simp [eval, hz₂])
    (fun hcl => ?_) (fun hcl => ?_)
  · refine WP.mono (finUsed_end hg₂.scr hg₂.rdi hl8 (by decide) hu₂ (by rw [hk₂ (by simp)]; exact h.usedP)
      (h.ou.congr k12.2.2) hsv₂ hin₂ k12) fun t ht => ?_
    unfold VG.Proof.RsaKeyGen.afterDraw
    rw [hcl]
    simp only [↓reduceIte, CandEnd, List.length_drop]
    rwa [show r.length - (r.length - 8 * w) = 8 * w by have := h.rk; omega]
  have hc₂ : wv s₂.mem B (slot w aN) w = c := by
    rw [hf₂.wv_eq (d := slot w aN) (k := w) (by simp only [closeRanges]; rng_disj)
      (by have := slot_le (w := w) (show aN < 8 by decide); omega)]; exact hc₁
  have hgt : 8161 < c := by
    obtain ⟨_, hlo, _⟩ := hsh
    have : 2 ^ 13 ≤ 2 ^ (64 * w - 2) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hend : ∀ {sX : State} {mi : BitVec 64}, Good sX B Z w mi → Keep mmRegs s sX →
      (∀ i ≤ 25, word sX.mem B (8 * i) = word s₁.mem B (8 * i)) → InScr B Z s₁.mem sX.mem →
      WP isa (finUsed 3) sX fun t => KEnd s t B Z op up (8 * w) 3 (8 * w) none := by
    intro sX mi hgX kX hX hinX
    exact finUsed_end hgX.scr hgX.rdi hl8 (by decide) (by rw [hX kUsed (by decide), hus₁])
      (by rw [hX kUsedP (by decide), hh₁ (by simp)]; exact h.usedP) (h.ou.congr kX.2.2)
      (fun i hi => (hX i (by omega)).trans (hsv₁ i hi)) (hin₁.trans hinX) kX
  have hrej : ∀ t, KEnd s t B Z op up (8 * w) 3 (8 * w) none → CandEnd s t B Z op up (8 * w) r
      (some (.rejected, r.drop (8 * w))) := fun t ht => by
    simp only [CandEnd, List.length_drop]
    rwa [show r.length - (r.length - 8 * w) = 8 * w by have := h.rk; omega]
  -- Trial division.
  refine wp_seqs_append (by simp [trial]) (by simp) ?_
  refine WP.mono (trial_ok hg₂ hZ hTZ (by omega) (by omega)) fun s₃ ⟨hz₃, hg₃, hf₃, k₃⟩ => ?_
  rw [hc₂, trialAny_eq hgt] at hz₃
  have st₃ := stage hf₃ (by rng_le) (fun r hr => by
    have : r.1 + r.2 ≤ slot w aTab + 2048 := by revert r hr; rng_le
    omega) st₂
  have k13 : Keep mmRegs s s₃ := (k12.trans k₃).mono (by decide)
  refine WP.ite (Spec.RsaKeyGen.obviouslyComposite (64 * w) c) (by simp [eval, hz₃]) (fun hoc => ?_) (fun hoc => ?_)
  · refine WP.mono (hend hg₃ k13 st₃.1 st₃.2) fun t ht => ?_
    unfold VG.Proof.RsaKeyGen.afterDraw
    simp only [hcl, hoc, Bool.false_eq_true, ↓reduceIte, Bool.not_true, Bool.false_and]
    exact hrej t ht
  have hc₃ : wv s₃.mem B (slot w aN) w = c := by
    rw [hf₃.wv_eq (d := slot w aN) (k := w) (by rng_disj)
      (by have := slot_le (w := w) (show aN < 8 by decide); omega)]; exact hc₂
  have hk₃ : ∀ {i}, i = kOut ∨ i = kLen ∨ i = kUsedP ∨ i = kE ∨ i = kElen ∨ i = kP ∨ i = kPlen ∨ i = kRand ∨
      i = kRandLen → word s₃.mem B (8 * i) = word s.mem B (8 * i) := fun {i} hi => by
    have : i ≤ 25 := by rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [st₃.1 i this, hh₁ hi]
  -- `gcd(c − 1, e)`.
  refine wp_seqs_append (by simp [gcdCheck, loadE]) (by simp) ?_
  refine WP.mono (gcdCheck_ok hg₃ hZ (by omega) (by omega) (by rw [hc₃]; exact hsh.1)
    (by rw [hc₃]; omega) (by rw [hk₃ (by simp)]; exact h.e) (by rw [hk₃ (by simp)]; exact h.elen) h.el1 h.el8
    (h.esrc.congrK (hin₁.trans st₃.2) k13)) fun s₄ ⟨hz₄, hg₄, hf₄, k₄⟩ => ?_
  rw [hc₃] at hz₄
  have st₄ := stage hf₄ (by rng_le) (fun r hr => by
    have : r.1 + r.2 ≤ slot w 8 := by revert r hr; rng_le
    omega) st₃
  have k14 : Keep mmRegs s s₄ := (k13.trans k₄).mono (by decide)
  refine WP.ite (!decide (Nat.gcd (c - 1) (Spec.Rsa.os2ip eB) = 1)) (by simp [eval, hz₄]) (fun hgc => ?_)
    (fun hgc => ?_)
  · refine WP.mono (hend hg₄ k14 st₄.1 st₄.2) fun t ht => ?_
    simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hgc
    unfold VG.Proof.RsaKeyGen.afterDraw
    simp only [hcl, hoc, hgc, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and, beq_iff_eq]
    exact hrej t ht
  simp only [Bool.not_eq_false', decide_eq_true_eq] at hgc
  have hc₄ : wv s₄.mem B (slot w aN) w = c := by
    rw [hf₄.wv_eq (d := slot w aN) (k := w) (by rng_disj)
      (by have := slot_le (w := w) (show aN < 8 by decide); omega)]; exact hc₃
  have hk₄ : ∀ {i}, i = kOut ∨ i = kLen ∨ i = kUsedP ∨ i = kE ∨ i = kElen ∨ i = kP ∨ i = kPlen ∨ i = kRand ∨
      i = kRandLen → word s₄.mem B (8 * i) = word s.mem B (8 * i) := fun {i} hi => by
    have : i ≤ 25 := by rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [st₄.1 i this, hh₁ hi]
  refine WP.mono (kTail_ok M hg₄ hZ hTZ (by omega) (by omega) hc₄ hsh (h.ou.congr k14.2.2)
    (by rw [hk₄ (by simp)]; exact h.out) (by rw [hk₄ (by simp)]; exact h.len) (by rw [hk₄ (by simp)]; exact h.usedP)
    (by rw [hk₄ (by simp)]; exact h.rand) (by rw [hk₄ (by simp)]; exact h.rlen)
    (by rw [st₄.1 kUsed (by decide), hus₁]) (h.rsrc.congrK (hin₁.trans st₄.2) k14) h.rl h.rk) fun t ht => ?_
  have hlo : ∀ i < 6, word s₄.mem B (8 * i) = word s.mem B (8 * i) := fun i hi =>
    (st₄.1 i (by omega)).trans (hsv₁ i hi)
  have hhi : ∀ x, Z ≤ ofs B x → s₄.mem x = s.mem x := fun x hx => ((hin₁.trans st₄.2) x hx)
  unfold VG.Proof.RsaKeyGen.afterDraw
  simp only [hcl, hoc, hgc, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and, beq_self_eq_true]
  rcases hp : Spec.RsaKeyGen.primalityTest c (r.drop (8 * w)) with _ | ⟨b, rest⟩
  · rw [hp] at ht; exact KEnd.trans_pre ht hlo hhi k14 h.ou.outZ
  · rw [hp] at ht
    cases b
    · exact KEnd.trans_pre ht hlo hhi k14 h.ou.outZ
    · exact KEnd.trans_pre ht hlo hhi k14 h.ou.outZ

end VG.Proof.RsaKeyGen.X86_64
