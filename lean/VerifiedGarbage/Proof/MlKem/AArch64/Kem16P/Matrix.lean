module

public import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.Pair
public import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.Last
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Matrix
public import VerifiedGarbage.Impl.MlKem.AArch64.Kem16P
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemMatrixTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemMatrixPost
import VerifiedGarbage.Proof.Framework.AArch64.Syms

/-!
# The matrix after `G`, computing PRF outputs

After `G` has written `r` to `RB`, the matrix's pairs (`Kem16P.pairP`) and its
singleton (`Kem16P.lastP`) compute `PRF₂(r, N)` into buffer `N`
(`bufOff`), in `TP` and `PP` (`bufsR`). `PInvW`: the paired matrix's
invariant, the writes since `G` (`bWP`), and the first `c` PRF outputs
(`PrfAt`). `paired_stepP`: a pair computing them.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Kem16P

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Proof.MlKem.AArch64.Hybrid (Stk128 MT3 bW3 stR_sc far3 safe_frame)
open VG.Proof.Sha3.AArch64.Hybrid.X3 (stR)
open VG.Proof.MlKem.AArch64.Noise (rateR Rate128)
open VG.Spec.Sha3 (keccakF bytesAt)
open VG.Spec.MlKem
open VG.Proof.MlKem

variable {P : KemLay} {L : Layout}

/-- The buffers of the PRF outputs: `TP` and `PP`. -/
abbrev bufsR (P : KemLay) (L : Layout) (s₀ : State) : Region := R (kA s₀) L.sc (TP P) 2048

/-- What the matrix writes after `G`. -/
abbrev bWP (P : KemLay) (L : Layout) (s₀ : State) : List Region := bW3 P L s₀ ++ [bufsR P L s₀]

/-- `PRF₂(r, N)`, `r` at `RB` in `mR`, in buffer `N`. -/
def PrfAt (P : KemLay) (L : Layout) (s₀ : State) (m mR : Mem) (N : Nat) : Prop :=
  Rate128 m (sA L s₀ (Impl.MlKem.AArch64.Kem16P.bufOff P N))
    (keccakF (Noise.seedState mR (sA L s₀ RB) N))

/-- After `n` entries of `Â` and the first `c` PRF outputs, from the memory `mA`
right after `G`. -/
structure PInvW (w16 : Bool) (P : KemLay) (L : Layout) (s₀ : State) (mA : Mem) (ρ : List Byte)
    (n c : Nat) (s : State) : Prop where
  b : BInvW w16 P L s₀ s.mem ρ n s
  fr : Frame (bWP P L s₀) mA s.mem
  prf : ∀ N < c, PrfAt P L s₀ s.mem mA N

theorem PrfAt.frame {s₀ : State} {m m' mR : Mem} {N : Nat} (h : PrfAt P L s₀ m mR N) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (rateR (sA L s₀ (Impl.MlKem.AArch64.Kem16P.bufOff P N))).Disjoint r) :
    PrfAt P L s₀ m' mR N :=
  rate128_frame h hf hd

/-- `r` is not written after `G`. -/
theorem r_far {s₀ : State} (hp : Pre P L s₀) (hk : Stk128 P L s₀) :
    ∀ r ∈ bWP P L s₀, (Region.mk (sA L s₀ RB) 32).Disjoint r := by
  have hw := hp.wf
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · rcases List.mem_append.mp hr with hr | hr
    · rcases mem4 hr with rfl | rfl | rfl | rfl
      · exact sdisj hp (by lom) (by lom) (by lom)
      · exact sdisj hp (by lom) (by lom) (by lom)
      · exact sdisj hp (by lom) (by lom) (by lom)
      · exact below_R hp hp.scb (hp.fs (by lom))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sdisj hp (by lom) (by lom) (by lom)
      · exact (hk.R hp.scb (hp.fs (by lom))).symm
  · rw [List.mem_singleton.mp hr]; exact sdisj hp (by lom) (by lom) (by lom)

/-- `PRF₂(r, N)` with `r` read from the memory after `G`. -/
theorem seed_mA {s₀ : State} (hp : Pre P L s₀) (hk : Stk128 P L s₀) {mA m : Mem}
    (hf : Frame (bWP P L s₀) mA m) (N : Nat) :
    Noise.seedState m (sA L s₀ RB) N = Noise.seedState mA (sA L s₀ RB) N :=
  seedState_frame hf (r_far hp hk)

/-- What a PRF pair needs beyond `Paired.BeginInput`. -/
theorem prf_input {s₀ s : State} (hp : Pre P L s₀) (hk : Stk128 P L s₀) {e N₀ : Nat}
    (he : e + 1 < P.k * P.k) (hN : N₀ + 3 ≤ 12) (h : KB P L s₀ s) (tb : MT3 P L s₀ s) :
    PrfInput (sA L s₀ SS) (aP L s₀ e) (aP L s₀ (e + 1)) (s.syms "VG_MLKEM_REJ_SHUFFLE") (kA s₀ L.sc)
      (sA L s₀ RB) (sA L s₀ (Impl.MlKem.AArch64.Kem16P.bufOff P N₀)) s := by
  have hw := hp.wf
  have bR : bufR (sA L s₀ (Impl.MlKem.AArch64.Kem16P.bufOff P N₀)) = R (kA s₀) L.sc (TP P + 168 * N₀) 504 := rfl
  have tS : (Region.mk (s.syms "VG_MLKEM_REJ_SHUFFLE") 4096).Disjoint (R (kA s₀) L.sc 0 200) :=
    tb.t.apart.sub_right (scratch_sub hp (by lom))
  refine ⟨⟨cov_s hp h (o := SS) (l := 2048) (by lom), by rw [stR_sc]; exact cov_s hp h (by lom),
    by rw [h.sp]; exact hk.sp, by rw [stR_sc]; exact sdisj hp (by lom) (by lom) (by lom),
    by rw [h.sp]; exact hk.R hp.scb (hp.fs (o := SS) (l := 2048) (by lom)),
    by rw [h.sp, stR_sc]; exact hk.R hp.scb (hp.fs (by lom)),
    cov_sr hp h (o := RB) (l := 32) (by lom), by rw [stR_sc]; exact sdisj hp (by lom) (by lom) (by lom),
    sdisj hp (by lom) (by lom) (by lom), by rw [h.sp]; exact hk.R hp.scb (hp.fs (by lom)),
    by rw [bR]; exact cov_s hp h (by lom), by rw [stR_sc, bR]; exact sdisj hp (by lom) (by lom) (by lom),
    by rw [bR]; exact sdisj hp (by lom) (by lom) (by lom),
    by rw [h.sp, bR]; exact hk.R hp.scb (hp.fs (by lom)),
    by rw [bR]; exact sdisj hp (by lom) (by lom) (by lom)⟩,
    h.x28, by rw [stR_sc]; exact tS, by rw [h.sp]; exact tb.stk,
    by rw [stR_sc]; exact sdisj hp (o₁ := AH + 1024 * e) (l₁ := 1024) (by lom) (by lom) (by lom),
    by rw [stR_sc]; exact sdisj hp (o₁ := AH + 1024 * (e + 1)) (l₁ := 1024) (by lom) (by lom) (by lom),
    by rw [bR]; exact sdisj hp (o₁ := AH + 1024 * e) (l₁ := 1024) (by lom) (by lom) (by lom),
    by rw [bR]; exact sdisj hp (o₁ := AH + 1024 * (e + 1)) (l₁ := 1024) (by lom) (by lom) (by lom),
    by rw [bR]; exact tb.t.apart.sub_right (scratch_sub hp (by lom))⟩

/-- What the PRF pair of entries `e`, `e + 1` writes, computing outputs from `N₀`. -/
abbrev pairWritesM (P : KemLay) (L : Layout) (s₀ : State) (e N₀ : Nat) : List Region :=
  pairWritesP (sA L s₀ SS) (aP L s₀ e) (aP L s₀ (e + 1)) (kA s₀ L.sc) s₀.sp
    (sA L s₀ (Impl.MlKem.AArch64.Kem16P.bufOff P N₀))

theorem bufR_eq (s₀ : State) (N₀ : Nat) :
    bufR (sA L s₀ (Impl.MlKem.AArch64.Kem16P.bufOff P N₀)) = R (kA s₀) L.sc (TP P + 168 * N₀) 504 := rfl

theorem pairP_far {s₀ : State} (hp : Pre P L s₀) (hk : Stk128 P L s₀) {e N₀ : Nat} (he : e + 1 < P.k * P.k)
    {o l : Nat} (hf : o + l ≤ SV P + 48)
    (hs : (o + l ≤ SS ∨ SS + 2048 ≤ o) ∧ (o + l ≤ AH + 1024 * e ∨ AH + 1024 * (e + 2) ≤ o)) (h200 : 200 ≤ o)
    (hb : o + l ≤ TP P + 168 * N₀ ∨ TP P + 168 * N₀ + 504 ≤ o) (hN : N₀ + 3 ≤ 12) :
    ∀ r ∈ pairWritesM P L s₀ e N₀, (R (kA s₀) L.sc o l).Disjoint r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact far3 hp hk he hf hs h200 r hr
  · rw [List.mem_singleton.mp hr, bufR_eq]
    have hw := hp.wf
    exact sdisj hp hf (by lom) hb

/-- The paired matrix's invariant after a PRF pair (as `Hybrid.BInvW.paired3`). -/
theorem BInvW.pairedP {w16 : Bool} {s₀ s t : State} (hp : Pre P L s₀) (hk : Stk128 P L s₀) {mA : Mem}
    {ρ : List Byte} {Rr : Addr} {e N₀ m : Nat} (he : e + 1 < P.k * P.k) (hN : N₀ + 3 ≤ 12)
    (h : BInvW w16 P L s₀ mA ρ e s)
    (ht : PairPOutcomeW w16 (matSeed ρ (e / P.k) (e % P.k)) (matSeed ρ ((e + 1) / P.k) ((e + 1) % P.k))
      (sA L s₀ SS) (aP L s₀ e) (aP L s₀ (e + 1)) (kA s₀ L.sc) Rr
      (sA L s₀ (Impl.MlKem.AArch64.Kem16P.bufOff P N₀)) N₀ m s t) :
    BInvW w16 P L s₀ t.mem ρ (e + 2) t := by
  have hw := hp.wf
  have fr : Frame (pairWritesM P L s₀ e N₀) s.mem t.mem := by
    have f := ht.frame; rw [h.kb.sp] at f; exact f
  have old {j : Nat} (hj : j < e) := pairP_far hp hk he (o := AH + 1024 * j) (l := 1024) (N₀ := N₀)
    (by lom) (by constructor <;> lom) (by lom) (.inl (by lom)) hN
  refine ⟨h.kb.frame ht.keep fr (by decide) ?_, Frame.refl _ _, ?_, ?_, ?_, ?_⟩
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_append.mp hr with hr | hr
      · simp only [Paired.stepWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> exact safe_scr hp (by lom)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [stR_sc]; exact safe_scr hp (by lom)
        · exact safe_frame hp hk
    · rw [List.mem_singleton.mp hr, bufR_eq]; exact safe_scr hp (by lom)
  · rw [bytesAt_frame fr (pairP_far hp hk he (o := SB) (l := 32) (by lom) (by constructor <;> lom) (by lom)
      (.inl (by lom)) hN) (by decide)]
    exact h.rho
  · have hall : okR P ρ (e + 2) ↔ (okR P ρ e ∧ (sampleNTT 280 (matSeed ρ (e / P.k) (e % P.k))).isSome) ∧
        (sampleNTT 280 (matSeed ρ ((e + 1) / P.k) ((e + 1) % P.k))).isSome := by
      rw [show e + 2 = (e + 1) + 1 by omega, okR_succ, okR_succ]
    rw [ht.status, h.acc]
    by_cases ha : okR P ρ e <;>
      by_cases hb : (sampleNTT 280 (matSeed ρ (e / P.k) (e % P.k))).isSome <;>
      by_cases hc : (sampleNTT 280 (matSeed ρ ((e + 1) / P.k) ((e + 1) % P.k))).isSome <;>
      simp [hall, ha, hb, hc]
  · intro j hj
    rcases (by omega : j < e ∨ j = e ∨ j = e + 1) with hj | rfl | rfl
    · exact reducedW_frame fr (old hj) (h.red j hj)
    · exact ht.reducedLeft
    · exact ht.reducedRight
  · intro j hj
    rcases (by omega : j < e ∨ j = e ∨ j = e + 1) with hj | rfl | rfl
    · rw [polyAtW_frame fr (old hj)]; exact h.res j hj
    · exact ht.left
    · exact ht.right

theorem pairM_sub {s₀ : State} {e N₀ : Nat} (he : e + 1 < P.k * P.k) (hN : N₀ + 3 ≤ 12) :
    ∀ r ∈ pairWritesM P L s₀ e N₀, ∃ r' ∈ bWP P L s₀, Region.Sub r r' := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨r', hr', hs⟩ := pair_sub (L := L) (s₀ := s₀) he r hr
      exact ⟨r', List.mem_append_left _ (List.mem_append_left _ hr'), hs⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨R (kA s₀) L.sc 0 200, by simp, by rw [stR_sc]; exact fun _ h => h⟩
      · exact ⟨Hybrid.frame s₀.sp, by simp, fun _ h => h⟩
  · rw [List.mem_singleton.mp hr, bufR_eq]
    exact ⟨bufsR P L s₀, by simp, R.sub2 (by omega) (by omega)⟩

/-- **A pair computing PRF outputs** `N₀`, …, `N₀ + m - 1`. -/
theorem paired_stepP {s₀ s : State} (hp : Pre P L s₀) (hk : Stk128 P L s₀) {mA : Mem} {ρ : List Byte}
    {i N₀ m : Nat} (he : 2 * i + 1 < P.k * P.k) (hN : N₀ + 3 ≤ 12) (hm : m ≤ 3)
    (h : PInvW true P L s₀ mA ρ (2 * i) N₀ s) (tb : MT3 P L s₀ s) :
    WP isa (Impl.MlKem.AArch64.Kem16P.pairP P (2 * i) N₀ m) s fun t =>
      PInvW true P L s₀ mA ρ (2 * i + 2) (N₀ + m) t ∧ MT3 P L s₀ t := by
  have hw := hp.wf
  have hbo : Impl.MlKem.AArch64.Kem16P.bufOff P (N₀ + 2) < 65536 := by
    simp only [Impl.MlKem.AArch64.Kem16P.bufOff]; lom
  rw [pairP_iff]
  have hf := hw.facts
  have hkk : P.k * P.k ≤ 16 := hf.2.2.1
  have hoa : AH + 1024 * (2 * i) < 65536 := by simp only [KEM.AH]; omega_using [he, hkk]
  have hob : AH + 1024 * (2 * i + 1) < 65536 := by simp only [KEM.AH]; omega_using [he, hkk]
  have hk1 : 0 < P.k := hf.1
  have hk2 : P.k ≤ 256 := by omega_using [hf.2.1]
  have pin := pair_input (L := L) hp he h.b.kb tb.t
  have hin := prf_input hp hk he hN h.b.kb tb
  refine WP.mono_syms (pairPCode_ok P (a := 2 * i) (m := m) (by omega) hbo (by decide) (by decide) (by decide)
    hoa hob pin hin rfl rfl (Hybrid.x24_bit h.b)) fun t ht sy => ?_
  have post := ht.outcome hk1 hk2
  have seed {j : Nat} : Paired.seedBytes s.mem (sA L s₀ SB) j P.k = matSeed ρ (j / P.k) (j % P.k) := by
    simp only [Paired.seedBytes, h.b.rho, matSeed]
  rw [seed, seed] at post
  have fr : Frame (pairWritesM P L s₀ (2 * i) N₀) s.mem t.mem := by
    have f := post.frame; rw [h.b.kb.sp] at f; exact f
  refine ⟨⟨BInvW.pairedP hp hk he hN h.b post, h.fr.trans (fr.sub (pairM_sub he hN)), fun N hN' => ?_⟩, ?_⟩
  · by_cases hlt : N < N₀
    · refine (h.prf N hlt).frame fr (pairP_far hp hk he (o := TP P + 168 * N) (l := 128) (by lom) (by constructor <;> lom) (by lom)
        (.inl (by omega)) hN)
    · have hk' : N - N₀ < min 3 m := by omega
      have pr := post.prf (N - N₀) hk'
      rw [show N₀ + (N - N₀) = N by omega, seed_mA hp hk h.fr] at pr
      show Rate128 t.mem (sA L s₀ (Impl.MlKem.AArch64.Kem16P.bufOff P N)) _
      have e : sA L s₀ (Impl.MlKem.AArch64.Kem16P.bufOff P N) =
          bufAt (sA L s₀ (Impl.MlKem.AArch64.Kem16P.bufOff P N₀)) (N - N₀) := by
        simp only [bufAt, Impl.MlKem.AArch64.Kem16P.bufOff, sA, ptr_add]
        congr 2; omega
      rw [e]; exact pr
  · refine tb.frame post.keep.rd post.keep.wr sy fr fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_append.mp hr with hr | hr
      · exact .inl (pair_scratch hp he r hr)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact .inl (by rw [stR_sc]; exact scratch_sub hp (by lom))
        · exact .inr rfl
    · rw [List.mem_singleton.mp hr, bufR_eq]; exact .inl (scratch_sub hp (by lom))

end VG.Proof.MlKem.AArch64.Kem16P
