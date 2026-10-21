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

/-- The paired matrix's writes miss buffer `N`. -/
theorem buf_bW {s₀ : State} (hp : Pre P L s₀) {N : Nat} (hN : N < 12) :
    ∀ r ∈ bW P L s₀, (rateR (sA L s₀ (Impl.MlKem.AArch64.Kem16P.bufOff P N))).Disjoint r := by
  have hw := hp.wf
  intro r hr
  show (R (kA s₀) L.sc (TP P + 168 * N) 128).Disjoint r
  rcases mem4 hr with rfl | rfl | rfl | rfl
  · exact sdisj hp (by lom) (by lom) (by lom)
  · exact sdisj hp (by lom) (by lom) (by lom)
  · exact sdisj hp (by lom) (by lom) (by lom)
  · exact below_R hp hp.scb (hp.fs (by lom))

/-- **A pair computing no PRF output** after `G`. -/
theorem paired_stepQ {s₀ s : State} (hp : Pre P L s₀) {mA : Mem} {ρ : List Byte} {e c : Nat}
    (he : e + 1 < P.k * P.k) (hc : c ≤ 12)
    (h : PInvW true P L s₀ mA ρ e c s) (tb : MT3 P L s₀ s) :
    WP isa (Impl.MlKem.AArch64.Paired.pair P false e true) s fun t =>
      PInvW true P L s₀ mA ρ (e + 2) c t ∧ MT3 P L s₀ t := by
  refine WP.mono_syms (paired_step hp he h.b tb.t) fun t ⟨hb, mt⟩ sy => ?_
  exact ⟨⟨Hybrid.binv_rebase hb, h.fr.trans (hb.fr.mono fun r hr => List.mem_append_left _ (Hybrid.bW_sub r hr)),
    fun N hN => (h.prf N hN).frame hb.fr (buf_bW hp (by omega))⟩, mt, by rw [sy]; exact tb.stk⟩

/-- **The singleton computing no PRF output** after `G`. -/
theorem singleton_stepQ {s₀ s : State} (hp : Pre P L s₀) {mA : Mem} {ρ : List Byte} {e c : Nat}
    (he : e < P.k * P.k) (hc : c ≤ 12)
    (h : PInvW true P L s₀ mA ρ e c s) (tb : MT3 P L s₀ s) :
    WP isa (Paired.lastCode SB SS e P.k (AH + 1024 * e) true) s fun t =>
      PInvW true P L s₀ mA ρ (e + 1) c t ∧ MT3 P L s₀ t := by
  refine WP.mono_syms (singleton_step hp he h.b tb.t) fun t ⟨hb, mt⟩ sy => ?_
  exact ⟨⟨Hybrid.binv_rebase hb, h.fr.trans (hb.fr.mono fun r hr => List.mem_append_left _ (Hybrid.bW_sub r hr)),
    fun N hN => (h.prf N hN).frame hb.fr (buf_bW hp (by omega))⟩, mt, by rw [sy]; exact tb.stk⟩

/-- `Paired.LastOutcomeW`, with the singleton's PRF outputs. -/
structure LastOutcomeP (w16 : Bool) (B : List Byte) (p out R B₀ : Addr) (N₀ : Nat) (s t : State) : Prop where
  keep : Keep Paired.pairRegs s t
  frame : Frame (fullWritesP p out B₀) s.mem t.mem
  reduced : ReducedW (cw w16) t.mem out
  result : sampleNTT 280 B = none ∨ sampleNTT 280 B = some (polyAtW (cw w16) t.mem out)
  status : t.gpr .x24 = s.gpr .x24 &&& BitVec.ofNat 64 (if (sampleNTT 280 B).isSome then 1 else 0)
  prf : PrfBufs t.mem B₀ s.mem R N₀ 3

theorem LastPostP.outcome {w16 : Bool} {B : List Byte} {p out R B₀ : Addr} {N₀ : Nat} {s t : State}
    (h : LastPostP w16 B p out R B₀ N₀ s t) : LastOutcomeP w16 B p out R B₀ N₀ s t := by
  refine ⟨h.keep, h.frame, h.reduced, ?_, ?_, h.prf⟩
  · rcases h.result with ⟨_, hr⟩ | ⟨_, hr⟩; exact Or.inr hr; exact Or.inl hr
  · rw [h.status]
    rcases h.result with ⟨hl, hr⟩ | ⟨hl, hr⟩ <;> simp [hl, hr]

/-- The singleton's writes, with its buffers. -/
abbrev lastWritesM (P : KemLay) (L : Layout) (s₀ : State) (e N₀ : Nat) : List Region :=
  fullWritesP (sA L s₀ SS) (aP L s₀ e) (sA L s₀ (Impl.MlKem.AArch64.Kem16P.bufOff P N₀))

theorem lastP_far {s₀ : State} (hp : Pre P L s₀) {e N₀ : Nat} (he : e < P.k * P.k)
    {o l : Nat} (hf : o + l ≤ SV P + 48)
    (hs : (o + l ≤ SS ∨ SS + 2048 ≤ o) ∧ (o + l ≤ AH + 1024 * e ∨ AH + 1024 * (e + 1) ≤ o))
    (hb : o + l ≤ TP P + 168 * N₀ ∨ TP P + 168 * N₀ + 504 ≤ o) (hN : N₀ + 3 ≤ 12) :
    ∀ r ∈ lastWritesM P L s₀ e N₀, (R (kA s₀) L.sc o l).Disjoint r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact last_far hp he hf hs r hr
  · rw [List.mem_singleton.mp hr, bufR_eq]
    have hw := hp.wf
    exact sdisj hp hf (by lom) hb

/-- The paired matrix's invariant after the singleton computing PRF outputs. -/
theorem BInvW.singletonP {w16 : Bool} {s₀ s t : State} (hp : Pre P L s₀) {mA : Mem} {ρ : List Byte}
    {Rr : Addr} {e N₀ : Nat} (he : e < P.k * P.k) (hN : N₀ + 3 ≤ 12) (h : BInvW w16 P L s₀ mA ρ e s)
    (ht : LastOutcomeP w16 (matSeed ρ (e / P.k) (e % P.k)) (sA L s₀ SS) (aP L s₀ e) Rr
      (sA L s₀ (Impl.MlKem.AArch64.Kem16P.bufOff P N₀)) N₀ s t) :
    BInvW w16 P L s₀ t.mem ρ (e + 1) t := by
  have hw := hp.wf
  have fr : Frame (lastWritesM P L s₀ e N₀) s.mem t.mem := ht.frame
  have old {i : Nat} (hi : i < e) := lastP_far hp he (o := AH + 1024 * i) (l := 1024) (N₀ := N₀)
    (by lom) (by constructor <;> lom) (.inl (by lom)) hN
  refine ⟨h.kb.frame ht.keep fr (by decide) ?_, Frame.refl _ _, ?_, ?_, ?_, ?_⟩
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · simp only [Paired.fullWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact safe_scr hp (by lom)
    · rw [List.mem_singleton.mp hr, bufR_eq]; exact safe_scr hp (by lom)
  · rw [bytesAt_frame fr (lastP_far hp he (o := SB) (l := 32) (by lom) (by constructor <;> lom)
      (.inl (by lom)) hN) (by decide)]
    exact h.rho
  · rw [ht.status, h.acc]
    by_cases ha : okR P ρ e <;>
      by_cases hb : (sampleNTT 280 (matSeed ρ (e / P.k) (e % P.k))).isSome <;>
      simp [okR_succ, ha, hb]
  · intro i hi
    rcases (by omega : i < e ∨ i = e) with hi | rfl
    · exact reducedW_frame fr (old hi) (h.red i hi)
    · exact ht.reduced
  · intro i hi
    rcases (by omega : i < e ∨ i = e) with hi | rfl
    · rw [polyAtW_frame fr (old hi)]; exact h.res i hi
    · exact ht.result

/-- **The singleton computing PRF outputs** `N₀`, `N₀ + 1`, `N₀ + 2` after `G`. -/
theorem singleton_stepP {s₀ s : State} (hp : Pre P L s₀) (hk : Stk128 P L s₀) {mA : Mem} {ρ : List Byte}
    {N₀ : Nat} (hN : N₀ + 3 ≤ 12)
    (h : PInvW true P L s₀ mA ρ (P.k * P.k - 1) N₀ s) (tb : MT3 P L s₀ s) :
    WP isa (Impl.MlKem.AArch64.Kem16P.lastP P N₀) s fun t =>
      PInvW true P L s₀ mA ρ (P.k * P.k - 1 + 1) (N₀ + 3) t ∧ MT3 P L s₀ t := by
  have hw := hp.wf
  have hbo : Impl.MlKem.AArch64.Kem16P.bufOff P N₀ < 65536 := by
    simp only [Impl.MlKem.AArch64.Kem16P.bufOff]; lom
  have hf := hw.facts
  have hkk : P.k * P.k ≤ 16 := hf.2.2.1
  have hk1 : 0 < P.k := hf.1
  have hn : 0 < P.k * P.k := Nat.mul_pos hk1 hk1
  have he : P.k * P.k - 1 < P.k * P.k := by omega
  have hoff : AH + 1024 * (P.k * P.k - 1) < 65536 := by simp only [KEM.AH]; omega_using [hkk]
  have bR := bufR_eq (L := L) (P := P) s₀ N₀
  have lay : LayB (sA L s₀ SS) (sA L s₀ RB) (sA L s₀ (Impl.MlKem.AArch64.Kem16P.bufOff P N₀)) s :=
    ⟨cov_s hp h.b.kb (o := SS) (l := 2048) (by lom), cov_sr hp h.b.kb (o := RB) (l := 32) (by lom),
      sdisj hp (by lom) (by lom) (by lom), by rw [bR]; exact cov_s hp h.b.kb (by lom),
      by rw [bR]; exact sdisj hp (by lom) (by lom) (by lom),
      by rw [bR]; exact sdisj hp (by lom) (by lom) (by lom)⟩
  have ap : BufApart (sA L s₀ SS) (sA L s₀ SB) (aP L s₀ (P.k * P.k - 1)) (s.syms "VG_MLKEM_REJ_SHUFFLE")
      (sA L s₀ RB) (sA L s₀ (Impl.MlKem.AArch64.Kem16P.bufOff P N₀)) :=
    ⟨by rw [bR]; exact sdisj hp (by lom) (by lom) (by lom), by rw [bR]; exact sdisj hp (by lom) (by lom) (by lom),
      by rw [bR]; exact sdisj hp (o₂ := AH + 1024 * (P.k * P.k - 1)) (l₂ := 1024) (by lom) (by lom) (by lom),
      by rw [bR]; exact tb.t.apart.sub_right (scratch_sub hp (by lom))⟩
  rw [lastP_eq]
  refine WP.mono_syms (lastCodeP_ok P (a := P.k * P.k - 1) (by omega) hbo (by decide) (by decide) (by decide) hoff
    hk1 (by omega) (e28 h.b.kb SS) (e28 h.b.kb SB) (e28 h.b.kb _) (fun j hj => ?_)
    (sdisj hp (by lom) (by lom) (by decide)) (sdisj hp (o₂ := AH + 1024 * (P.k * P.k - 1)) (l₂ := 1024)
      (by lom) (by lom) (by lom))
    (singleton_context hp he h.b.kb tb.t) rfl (Hybrid.x24_bit h.b) lay ap (e28 h.b.kb RB) (e28 h.b.kb _))
    fun t ht sy => ?_
  · rw [ptr_add]
    exact in_R (cov_sr hp h.b.kb (o := SB) (l := 32) (by lom)) (k := 8 * j) (by omega) (by omega)
  · have post := ht.outcome
    have seed : Paired.seedBytes s.mem (sA L s₀ SB) (P.k * P.k - 1) P.k =
        matSeed ρ ((P.k * P.k - 1) / P.k) ((P.k * P.k - 1) % P.k) := by
      simp only [Paired.seedBytes, h.b.rho, matSeed]
    rw [seed] at post
    have fr : Frame (lastWritesM P L s₀ (P.k * P.k - 1) N₀) s.mem t.mem := post.frame
    refine ⟨⟨BInvW.singletonP hp he hN h.b post, h.fr.trans (fr.sub fun r hr => ?_), fun N hN' => ?_⟩,
      ?_, by rw [sy]; exact tb.stk⟩
    · rcases List.mem_append.mp hr with hr | hr
      · obtain ⟨r', hr', hs⟩ := last_sub (L := L) (s₀ := s₀) he r hr
        exact ⟨r', List.mem_append_left _ (List.mem_append_left _ hr'), hs⟩
      · rw [List.mem_singleton.mp hr, bR]
        exact ⟨bufsR P L s₀, by simp, R.sub2 (by omega) (by omega)⟩
    · by_cases hlt : N < N₀
      · exact (h.prf N hlt).frame fr (lastP_far hp he (o := TP P + 168 * N) (l := 128) (by lom)
          (by constructor <;> lom) (.inl (by omega)) hN)
      · have pr := post.prf (N - N₀) (by omega)
        rw [show N₀ + (N - N₀) = N by omega, seed_mA hp hk h.fr] at pr
        show Rate128 t.mem (sA L s₀ (Impl.MlKem.AArch64.Kem16P.bufOff P N)) _
        have e : sA L s₀ (Impl.MlKem.AArch64.Kem16P.bufOff P N) =
            bufAt (sA L s₀ (Impl.MlKem.AArch64.Kem16P.bufOff P N₀)) (N - N₀) := by
          simp only [bufAt, Impl.MlKem.AArch64.Kem16P.bufOff, sA, ptr_add]
          congr 2; omega
        rw [e]; exact pr
    · refine tb.t.frame post.keep.rd post.keep.wr sy fr fun r hr => ?_
      rcases List.mem_append.mp hr with hr | hr
      · exact last_scratch hp he r hr
      · rw [List.mem_singleton.mp hr, bR]; exact scratch_sub hp (by lom)

/-! ## The matrix -/

theorem filter_lt_range (h : Nat) : ∀ n, (List.range n).filter (· < h) = List.range (min h n)
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.filter_append, filter_lt_range h n]
    by_cases hn : n < h
    · rw [show min h (n + 1) = min h n + 1 by omega, List.range_succ, show min h n = n by omega]
      simp [hn]
    · rw [show min h (n + 1) = min h n by omega]
      simp [hn]

theorem filter_ge_range (h : Nat) : ∀ n, (List.range n).filter (h ≤ ·) = (List.range (n - h)).map (· + h)
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.filter_append, filter_ge_range h n]
    by_cases hn : h ≤ n
    · rw [show n + 1 - h = n - h + 1 by omega, List.range_succ, List.map_append]
      simp [hn, show n - h + h = n by omega]
    · rw [show n + 1 - h = n - h by omega]
      simp [hn]

/-- The PRF outputs the matrix leaves: `placed` if the singleton computes its three. -/
def finalCount (P : KemLay) (hp : Nat) : Nat :=
  if Impl.MlKem.AArch64.Kem16P.single P = true ∧
      Impl.MlKem.AArch64.Kem16P.placed P hp ≥ 3 * (Impl.MlKem.AArch64.Kem16P.pairs P - hp) + 3 then
    3 * (Impl.MlKem.AArch64.Kem16P.pairs P - hp) + 3
  else min (Impl.MlKem.AArch64.Kem16P.placed P hp) (3 * (Impl.MlKem.AArch64.Kem16P.pairs P - hp))

theorem placed_le {hp : Nat} (hw : P.Wf) : Impl.MlKem.AArch64.Kem16P.placed P hp ≤ 9 := by
  have := hw.facts
  simp only [Impl.MlKem.AArch64.Kem16P.placed, Impl.MlKem.AArch64.Kem16P.prfs]
  omega

/-- **The matrix**: the pairs hashing the message, `between` (`G`), whose
outcome `Gp` the rest keeps, then the pairs and the singleton computing PRF
outputs. -/
theorem matrixP_ok {M : Hybrid.Msg} {s₀ s : State} (hp : Pre P L s₀) (hk : Stk128 P L s₀)
    (hM : Hybrid.MsgOk P L M s₀) (ho : Hybrid.HashOk P M.S) {between : Prog isa} {Gp : Mem → Prop}
    {mA : Mem} {ρ E : List Byte}
    (h : Hybrid.HInvW true P L M s₀ mA ρ E 0 0 s) (tb : MT3 P L s₀ s)
    (hb : ∀ u, Hybrid.HInvW true P L M s₀ mA ρ E (2 * Impl.MlKem.AArch64.Hybrid.hashPairs M.S)
        (Impl.MlKem.AArch64.Hybrid.hashPairs M.S) u → MT3 P L s₀ u →
      WP isa between u fun v => Gp v.mem ∧
        PInvW true P L s₀ v.mem ρ (2 * Impl.MlKem.AArch64.Hybrid.hashPairs M.S) 0 v ∧ MT3 P L s₀ v) :
    WP isa (Impl.MlKem.AArch64.Kem16P.matrixP P M.S between) s fun t => ∃ mG, Gp mG ∧
      PInvW true P L s₀ mG ρ (P.k * P.k) (finalCount P (Impl.MlKem.AArch64.Hybrid.hashPairs M.S)) t ∧
      MT3 P L s₀ t := by
  have hw := hp.wf
  have hk' : 0 < P.k := hw.facts.1
  have hn : 0 < P.k * P.k := Nat.mul_pos hk' hk'
  have hP := ho.pairs
  have h9 := placed_le (P := P) (hp := Impl.MlKem.AArch64.Hybrid.hashPairs M.S) hw
  generalize hH : Impl.MlKem.AArch64.Hybrid.hashPairs M.S = H at hP h9 hb ⊢
  have hpairs : Impl.MlKem.AArch64.Kem16P.pairs P = P.k * P.k / 2 := rfl
  unfold Impl.MlKem.AArch64.Kem16P.matrixP
  simp only [hH, filter_lt_range, filter_ge_range, List.map_map]
  rw [show min H (Impl.MlKem.AArch64.Kem16P.pairs P) = H by omega]
  apply WPs.seqs (by simp)
  refine WPs.append (WPs.append (WPs.append ?_))
  -- The pairs hashing the message.
  refine WPs.mono (WPs.range (I := fun i t => Hybrid.HInvW true P L M s₀ mA ρ E (2 * i) i t ∧ MT3 P L s₀ t)
    (fun i hi t ht => ?_) ⟨h, tb⟩) fun t ht => ?_
  · have hb' : 136 * (3 * i + 2) < M.S.len := by
      have := ho.part; have := ho.three
      rw [← hH] at hi
      simp only [Impl.MlKem.AArch64.Hybrid.hashPairs, Impl.MlKem.AArch64.Hybrid.blocks] at hi
      omega
    refine WP.mono (Hybrid.paired_step3 hp hk hM (by omega) hb' ht.1 ht.2) fun u hu => ?_
    rw [show 2 * (i + 1) = 2 * i + 2 by omega]
    exact hu
  -- `G`.
  refine WPs.single (WP.mono (hb t ht.1 ht.2) fun u ⟨gu, pu, mu⟩ => ?_)
  -- The pairs computing PRF outputs.
  refine WPs.mono (WPs.range (I := fun j t => PInvW true P L s₀ u.mem ρ (2 * (j + H))
      (min (Impl.MlKem.AArch64.Kem16P.placed P H) (3 * j)) t ∧ MT3 P L s₀ t)
    (fun j hj t ht => ?_) ⟨by simpa using pu, mu⟩) fun t ht => ?_
  · have he : 2 * (j + H) + 1 < P.k * P.k := by omega
    simp only [Function.comp]
    by_cases hc : Impl.MlKem.AArch64.Kem16P.pairCount P H (j + H) = 0
    · rw [ite_eq_left hc]
      have hc' : Impl.MlKem.AArch64.Kem16P.placed P H ≤ 3 * j := by
        simp only [Impl.MlKem.AArch64.Kem16P.pairCount] at hc; omega
      refine WP.mono (paired_stepQ hp he (by omega) ht.1 ht.2) fun v hv => ?_
      rw [show 2 * (j + 1 + H) = 2 * (j + H) + 2 by omega,
        show min (Impl.MlKem.AArch64.Kem16P.placed P H) (3 * (j + 1)) =
          min (Impl.MlKem.AArch64.Kem16P.placed P H) (3 * j) by omega]
      exact hv
    · rw [ite_eq_right hc]
      have hc' : 3 * j < Impl.MlKem.AArch64.Kem16P.placed P H := by
        simp only [Impl.MlKem.AArch64.Kem16P.pairCount] at hc; omega
      have h0 := ht.1
      rw [show min (Impl.MlKem.AArch64.Kem16P.placed P H) (3 * j) = 3 * (j + H - H) by omega] at h0
      refine WP.mono (paired_stepP hp hk he (by omega) (by simp only [Impl.MlKem.AArch64.Kem16P.pairCount]; omega)
        h0 ht.2) fun v hv => ?_
      rw [show 2 * (j + 1 + H) = 2 * (j + H) + 2 by omega,
        show min (Impl.MlKem.AArch64.Kem16P.placed P H) (3 * (j + 1)) =
          3 * (j + H - H) + Impl.MlKem.AArch64.Kem16P.pairCount P H (j + H) by
          simp only [Impl.MlKem.AArch64.Kem16P.pairCount]; omega]
      exact hv
  -- The singleton.
  rw [show Impl.MlKem.AArch64.Kem16P.pairs P - H + H = P.k * P.k / 2 by omega] at ht
  by_cases hodd : Impl.MlKem.AArch64.Kem16P.single P = true
  · rw [ite_eq_left hodd]
    have hodd' : P.k * P.k % 2 = 1 := by
      simpa [Impl.MlKem.AArch64.Kem16P.single] using hodd
    have idx : 2 * (P.k * P.k / 2) = P.k * P.k - 1 := by omega
    rw [idx] at ht
    apply WPs.single
    by_cases hl : Impl.MlKem.AArch64.Kem16P.placed P H ≥ 3 * (Impl.MlKem.AArch64.Kem16P.pairs P - H) + 3
    · rw [ite_eq_left hl]
      have h0 := ht.1
      rw [show min (Impl.MlKem.AArch64.Kem16P.placed P H) (3 * (Impl.MlKem.AArch64.Kem16P.pairs P - H)) =
        3 * (Impl.MlKem.AArch64.Kem16P.pairs P - H) by omega] at h0
      refine WP.mono (singleton_stepP hp hk (by omega) h0 ht.2) fun v hv => ⟨u.mem, gu, ?_, hv.2⟩
      rw [Nat.sub_add_cancel hn] at hv
      simpa only [finalCount, hodd, hl, and_self, ite_true] using hv.1
    · rw [ite_eq_right hl, Paired.lastSample_eq]
      refine WP.mono (singleton_stepQ hp (by omega : P.k * P.k - 1 < P.k * P.k) (by omega) ht.1 ht.2)
        fun v hv => ⟨u.mem, gu, ?_, hv.2⟩
      rw [Nat.sub_add_cancel hn] at hv
      simpa only [finalCount, hodd, hl, and_false, ite_false, Bool.false_eq_true] using hv.1
  · rw [ite_eq_right hodd]
    have hev : P.k * P.k % 2 = 0 := by
      simp only [Impl.MlKem.AArch64.Kem16P.single, decide_eq_true_eq] at hodd; omega
    have idx : 2 * (P.k * P.k / 2) = P.k * P.k := by omega
    rw [idx] at ht
    refine ⟨u.mem, gu, ?_, ht.2⟩
    simpa only [finalCount, hodd, Bool.false_eq_true, false_and, ite_false] using ht.1

end VG.Proof.MlKem.AArch64.Kem16P
