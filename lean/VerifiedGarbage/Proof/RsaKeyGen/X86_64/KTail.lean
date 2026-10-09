import VerifiedGarbage.Proof.RsaKeyGen.X86_64.KEnd

/-!
# A candidate on x86-64: Montgomery setup, Miller–Rabin and the result

`mrResult_ok`: the end from `kStat`; `kTail_ok`: `montSetup`, `millerRabin`
and `mrResult` end as `primalityTest c` on the octets after the candidate.
-/

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- How a primality test's result ends a candidate `c`. -/
def TestEnd (s t : State) (B : Addr) (Z : Nat) (op up : Addr) (k : Nat) (r : List Byte) (c : Nat) :
    Option (Bool × List Byte) → Prop
  | none => KEnd s t B Z op up k 0 0 none
  | some (true, rest) => KEnd s t B Z op up k 1 (r.length - rest.length) (some c)
  | some (false, rest) => KEnd s t B Z op up k 3 (r.length - rest.length) none

/-- `mrResult`, after `millerRabin` ended with `res`. -/
theorem mrResult_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {c : Nat} {op up : Addr} {r : List Byte}
    {res : Option (Bool × List Byte)} (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 27)
    (hn : wv s.mem B (slot w aN) w = c) (ho : OutUp s B Z op up (8 * w))
    (hO : word s.mem B (8 * kOut) = op) (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w))
    (hU : word s.mem B (8 * kUsedP) = up)
    (h0 : res = none → word s.mem B (8 * kStat) = BitVec.ofNat 64 0)
    (h1 : ∀ b rest, res = some (b, rest) → word s.mem B (8 * kStat) = BitVec.ofNat 64 (if b then 1 else 3) ∧
      word s.mem B (8 * kUsed) = BitVec.ofNat 64 (r.length - rest.length)) :
    WP isa mrResult s fun t => TestEnd s t B Z op up (8 * w) r c res := by
  have hn' := hg.scr.nowrap
  have h8 : 8 * 32 ≤ Z := by have := hdr_lt_slot w 8 (show 31 < 32 by decide); omega
  have hl : InRegions (s.rd ++ s.wr) (off B (8 * kStat)) 8 :=
    hg.scr.ld (by have := hdr_lt_slot w 8 (show kStat < 32 by decide); omega)
  unfold mrResult
  rcases hres : res with _ | ⟨b, rest⟩
  · have hS := h0 hres
    refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun t => t.zf = some true ∧ t.mem = s.mem) (by
      xrun [State.ea, hdr, hg.rdi, hdrOff, hl, hS]) rfl) fun s₁ ⟨⟨hz, hm⟩, k₁⟩ => ?_)
    refine WP.ite true (by simp [eval, hz]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine WP.mono (finNone_ok (hg.scr.congr k₁.2.2) ((k₁.gpr (by decide)).trans hg.rdi) h8 (by rw [hm]; exact hU)
      (by rw [k₁.2.2]; exact ho.upw) ho.upZ) fun t h => ?_
    exact (KEnd.of_fin (ho.congr k₁.2.2) h).trans_pre (fun i _ => by rw [hm]) (fun x _ => by rw [hm])
      (k₁.mono (by decide)) ho.outZ
  · obtain ⟨hS, hu⟩ := h1 b rest hres
    have hv : (if b then 1 else 3 : Nat) < 2 ^ 63 := by cases b <;> decide
    refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun t => t.zf = some false ∧
        t.gpr .rax = BitVec.ofNat 64 (if b then 1 else 3) ∧ t.mem = s.mem) (by
      xrun [State.ea, hdr, hg.rdi, hdrOff, hl, hS, BitVec.and_self]; cases b <;> decide) rfl)
      fun s₁ ⟨⟨hz, hax₁, hm⟩, k₁⟩ => ?_)
    refine WP.ite false (by simp [eval, hz]) (fun h => absurd h (by decide)) (fun _ => ?_)
    refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun t => t.zf = some b ∧ t.mem = s.mem) (by
      xrun [hax₁, hm]; cases b <;> decide) rfl) fun s₂ ⟨⟨hz₂, hm₂⟩, k₂⟩ => ?_)
    have hs₂ := (hg.scr.congr k₁.2.2).congr k₂.2.2
    have hdi₂ : s₂.gpr .rdi = B := (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hg.rdi)
    have ho₂ := (ho.congr k₁.2.2).congr k₂.2.2
    have k12 : Keep mmRegs s s₂ := (k₁.trans k₂).mono (by decide)
    refine WP.ite b (by simp [eval, hz₂]) (fun hb => ?_) (fun hb => ?_)
    · subst hb
      have hg₂ : Good s₂ B Z w mi := ⟨hs₂, hdi₂, by rw [hm₂]; exact hg.hdr⟩
      refine WP.mono (finPrime_ok (u := r.length - rest.length) hg₂ hZ hw hw' (by rw [hm₂]; exact hu) (by rw [hm₂]; exact hO)
        (by rw [hm₂]; exact hK) (by rw [hm₂]; exact hU) ho₂.upw ho₂.upZ ho₂.outw ho₂.outZ ho₂.ou)
        fun t ⟨hb, hax, hus, hsv, hfr, k⟩ => ?_
      refine ⟨hax, hus, by rw [hm₂, hn] at hb; exact hb, fun i hi => by rw [hsv i hi, hm₂],
        fun x hx hx' hx'' => by rw [hfr x hx hx' hx'', hm₂], (k12.trans k).mono (by decide)⟩
    · subst hb
      refine WP.mono (finUsed_ok (u := r.length - rest.length) hs₂ hdi₂ h8 (by decide) (by rw [hm₂]; exact hu) (by rw [hm₂]; exact hU)
        ho₂.upw ho₂.upZ) fun t h => ?_
      exact (KEnd.of_fin ho₂ h).trans_pre (fun i _ => by rw [hm₂]) (fun x _ => by rw [hm₂]) k12 ho.outZ

/-- `montSetup`, `millerRabin` and `mrResult`, for the candidate `c` in
`aN`, from offset `8 w` of `rand`. -/
theorem kTail_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {c : Nat} {op up rp : Addr}
    {r : List Byte} (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z) (hTZ : slot w aTab + 2048 ≤ Z) (hw4 : 4 ≤ w)
    (hw64 : w ≤ 64) (hn : wv s.mem B (slot w aN) w = c) (hsh : VG.Proof.RsaKeyGen.PrimeShape (64 * w) c)
    (ho : OutUp s B Z op up (8 * w)) (hO : word s.mem B (8 * kOut) = op)
    (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w)) (hU : word s.mem B (8 * kUsedP) = up)
    (hrp : word s.mem B (8 * kRand) = rp) (hrlen : word s.mem B (8 * kRandLen) = BitVec.ofNat 64 r.length)
    (hus : word s.mem B (8 * kUsed) = BitVec.ofNat 64 (8 * w)) (hsrc : Src s B Z rp r) (hrl : r.length < 2 ^ 64)
    (hrk : 8 * w ≤ r.length) :
    WP isa (seqs (montSetup M.mm ++ millerRabin M.mm ++ [mrResult])) s fun t =>
      TestEnd s t B Z op up (8 * w) r c (Spec.RsaKeyGen.primalityTest c (r.drop (8 * w))) := by
  have hnw := hg.scr.nowrap
  have hXZ : slot w aRm1 + 8 * (w + 2) ≤ Z := by unfold slot aRm1 aTab at *; omega_arith
  have hd : MrDims B Z w := ⟨hZ, hXZ, hw4, hw64⟩
  obtain ⟨hodd, hlo, hhi⟩ := hsh
  have htop : 2 ^ (64 * w - 1) ≤ c := by
    have : 2 ^ (64 * w - 1) = 2 ^ (64 * w - 2) * 2 := by rw [← Nat.pow_succ]; congr 1; omega_arith
    omega_arith
  have hc1 : 1 < c := by
    have : 2 ≤ 2 ^ (64 * w - 1) := Nat.le_trans (by decide) (Nat.pow_le_pow_right (by decide) (show 1 ≤ 64 * w - 1 by omega_arith))
    omega_arith
  rw [List.append_assoc]
  refine wp_seqs_append (by simp [montSetup]) (by simp) ?_
  refine WP.mono (montSetup_ok M hg hZ hXZ hw4 hw64 hn hodd htop) fun s₁ ⟨mi', hg₁, hinv₁, hr2₁, hr1₁, hrm₁, hch₁,
    hf₁, k₁⟩ => ?_
  have hw₁ : ∀ {k}, k = kRand ∨ k = kLen ∨ k = kRandLen ∨ k = kUsed ∨ k = kOut ∨ k = kUsedP →
      word s₁.mem B (8 * k) = word s.mem B (8 * k) := fun {k} hk => by
    have hk32 : k < 32 := by rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hd : ∀ r ∈ msRanges w, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k := by
      simp only [msRanges]
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> rng_disj
    exact hf₁.word_eq hd (by omega_arith)
  have hsl₁ : ∀ r ∈ msRanges w, r.1 + r.2 ≤ Z := fun r hr => by
    have : r.1 + r.2 ≤ slot w aRm1 + 8 * (w + 2) := by
      revert r hr; simp only [msRanges]; rng_le
    omega_arith
  have hc₁ : MrCtx s₁ B Z w mi' c (wv s₁.mem B (slot w aB) w) :=
    ⟨hg₁, hinv₁, by rw [hf₁.wv_eq (d := slot w aN) (k := w) (by simp only [msRanges]; rng_disj)
      (by have := slot_le (w := w) (show aN < 8 by decide); omega_arith)]; exact hn, rfl, hr1₁, hrm₁⟩
  have hsrc₁ := hsrc.congrK (InScr.of_frm hf₁ hsl₁) k₁
  have hres : mrRest c (checksW w) r 1 0 (8 * w) = Spec.RsaKeyGen.primalityTest c (r.drop (8 * w)) := by
    rw [VG.Proof.RsaKeyGen.primalityTest_cand (by omega_arith) ⟨hodd, hlo, hhi⟩, checksW_eq w (by omega_arith) hw4]
  refine wp_seqs_append (by simp [millerRabin]) (by simp) ?_
  refine WP.mono (millerRabin_ok M hd hc1 ⟨hodd, hlo, hhi⟩ hrl (by unfold checksW; split <;> (try split) <;>
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> decide) hc₁ hr2₁
    (by rw [hw₁ (Or.inl rfl)]; exact hrp) (by rw [hw₁ (Or.inr (Or.inl rfl))]; exact hK)
    (by rw [hw₁ (Or.inr (Or.inr (Or.inl rfl)))]; exact hrlen) hch₁ hsrc₁
    (by rw [hw₁ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]; exact hus) (Nat.le_refl _) hrk)
    fun s₂ ⟨⟨bm, hc₂⟩, h0, h1, hf₂, k₂⟩ => ?_
  rw [hres] at h0 h1
  have hw₂ : ∀ {k}, k = kRand ∨ k = kLen ∨ k = kRandLen ∨ k = kUsed ∨ k = kOut ∨ k = kUsedP →
      k ≠ kUsed → word s₂.mem B (8 * k) = word s.mem B (8 * k) := fun {k} hk hku => by
    have hk32 : k < 32 := by rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [← hw₁ hk]
    refine hf₂.word_eq (roundRanges_hdr w ?_) (by omega_arith)
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact absurd rfl hku | simp only [true_or, or_true]
  have hsl₂ : ∀ r ∈ roundRanges w, r.1 + r.2 ≤ Z := fun r hr => by
    have := roundRanges_le w r hr; omega_arith
  have hhi : ∀ x, Z ≤ ofs B x → s₂.mem x = s.mem x := fun x hx =>
    (InScr.of_frm hf₂ hsl₂ x hx).trans (InScr.of_frm hf₁ hsl₁ x hx)
  have hlo : ∀ i < 6, word s₂.mem B (8 * i) = word s.mem B (8 * i) := fun i hi => by
    have h2 : ∀ r ∈ roundRanges w, 8 * i + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * i := fun r hr => by
      have : 48 ≤ r.1 := by
        revert r hr
        simp only [roundRanges, preRanges, witRanges, expRanges, bitRanges, List.cons_append, List.nil_append]
        rng_le
      omega_arith
    have h1' : ∀ r ∈ msRanges w, 8 * i + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * i := fun r hr => by
      have : 48 ≤ r.1 := by revert r hr; simp only [msRanges]; rng_le
      omega_arith
    rw [hf₂.word_eq h2 (by omega_arith), hf₁.word_eq h1' (by omega_arith)]
  have k12 : Keep mmRegs s s₂ := (k₁.trans k₂).mono (by decide)
  have ho₂ := ho.congr (k12.2.2)
  refine WP.mono (mrResult_ok (r := r) hc₂.good hZ (by omega_arith) (by omega_arith) hc₂.n ho₂
    (by rw [hw₂ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (by decide)]; exact hO)
    (by rw [hw₂ (Or.inr (Or.inl rfl)) (by decide)]; exact hK)
    (by rw [hw₂ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) (by decide)]; exact hU) h0 h1) fun t ht => ?_
  rcases hp : Spec.RsaKeyGen.primalityTest c (r.drop (8 * w)) with _ | ⟨b, rest⟩
  · rw [hp] at ht; exact KEnd.trans_pre ht hlo hhi k12 ho.outZ
  · rw [hp] at ht; cases b <;> exact KEnd.trans_pre ht hlo hhi k12 ho.outZ

end VG.Proof.RsaKeyGen.X86_64
