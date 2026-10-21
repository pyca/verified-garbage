module

public import VerifiedGarbage.Proof.MlKem.AArch64.KgH.Inv
public import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.Pair
public import VerifiedGarbage.Impl.MlKem.AArch64.Kem16P
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenMatrixTable
import VerifiedGarbage.Proof.MlKem.AArch64.KgH.Pair
import VerifiedGarbage.Proof.MlKem.AArch64.KgH.Row
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenMatrixTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenMatrixPair
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Output
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Correct

/-! # Key generation's first two pairs, computing PRF outputs

The first two pairs of key generation's matrix absorb no block of `ek`
(`Kem16.hashedBy`): `Kem16P.kgPairP` computes `PRF₂(σ, 3p)`, …,
`PRF₂(σ, 3p + 2)` in the third state of their `x3` calls instead, into the
buffers from `KG.TP`. `FInv n c`: after `G`, `n` entries of `Â` and the
first `c` PRF outputs in their buffers. `first_step`: a pair keeps it. -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt)
open VG.Proof.MlKem.AArch64.Optimized
open VG.Proof.Sha3.AArch64.Hybrid.X3 (stR)
open VG.Proof.MlKem.AArch64.Hybrid (TStk frame)
open VG.Proof.MlKem.AArch64.Kem16P (PrfInput bufR bufAt PairPOutcomeW pairWritesP)

variable {P : KemLay}

/-- Buffer `N` holds `PRF₂(σ, N)`. -/
def PrfK (P : KemLay) (s₀ : State) (m : Mem) (N : Nat) : Prop :=
  bytesAt m (kA s₀ 3 + BitVec.ofNat 64 (TP P + 168 * N)) 128 =
    prf 2 (KPke.kgSigma P.params (dB s₀)) (BitVec.ofNat 8 N)

/-- After `G`: `n` entries of `Â` and the first `c` PRF outputs. -/
structure FInv (P : KemLay) (s₀ : State) (n c : Nat) (s : State) : Prop where
  b : BInvW true P s₀ n s
  prf : ∀ N < c, PrfK P s₀ s.mem N
  tables : Tables s
  tstk : TStk s

theorem FInv.zero {s₀ s : State} (h : AfterA P s₀ s) (ta : Tables s) (tk : TStk s) : FInv P s₀ 0 0 s :=
  ⟨⟨h.kb, h.rho, h.sig,
    by rw [h.x24, ite_eq_left (show allOk P s₀ 0 from fun e he => absurd he (Nat.not_lt_zero e))],
    fun e he => absurd he (Nat.not_lt_zero e), fun e he => absurd he (Nat.not_lt_zero e)⟩,
    fun N hN => absurd hN (Nat.not_lt_zero N), ta, tk⟩

/-- The buffers of PRF outputs `N₀`, `N₀ + 1` and `N₀ + 2`. -/
theorem bufR_k (s₀ : State) (N₀ : Nat) :
    bufR (kA s₀ 3 + BitVec.ofNat 64 (Impl.MlKem.AArch64.Kem16P.bufOff (TP P) N₀)) =
      R (kA s₀) 3 (TP P + 168 * N₀) 504 := rfl

/-- Two regions of `scratch`. -/
theorem sdisjK {s₀ : State} (hp : Pre P s₀) {o₁ l₁ o₂ l₂ : Nat} (f₁ : o₁ + l₁ ≤ kL P 3) (f₂ : o₂ + l₂ ≤ kL P 3)
    (h : o₁ + l₁ ≤ o₂ ∨ o₂ + l₂ ≤ o₁) : (R (kA s₀) 3 o₁ l₁).Disjoint (R (kA s₀) 3 o₂ l₂) :=
  hp.args.rdisj (by decide) (by decide) f₁ f₂ (.inr h)

/-- What a pair of key generation computing PRF outputs needs beyond `Paired.BeginInput`. -/
theorem prf_inputK {s₀ s : State} (hp : Pre P s₀) (hk : Stk128K P s₀) {e N₀ : Nat}
    (he : e + 1 < P.k * P.k) (hN : N₀ + 3 ≤ 6) (h : KB P s₀ s) (tk : TStk s) (mt : MatrixTable P s₀ s) :
    PrfInput (kA s₀ 3 + BitVec.ofNat 64 SS) (kA s₀ 3 + BitVec.ofNat 64 (AH + 1024 * e))
      (kA s₀ 3 + BitVec.ofNat 64 (AH + 1024 * (e + 1))) (s.syms "VG_MLKEM_REJ_SHUFFLE") (kA s₀ 3)
      (kA s₀ 3 + BitVec.ofNat 64 SG) (kA s₀ 3 + BitVec.ofNat 64 (Impl.MlKem.AArch64.Kem16P.bufOff (TP P) N₀)) s := by
  have hw := hp.wf
  have tp : TP P = AH + 1024 * (P.k * P.k) + 1024 * P.k + 1024 := rfl
  have sv : SV P = TP P + 2048 := rfl
  have hsv := hp.sv
  have cst : 200 ≤ SG ∧ SG + 32 ≤ SS ∧ SS + 2048 ≤ AH := by decide
  have fS : 0 + 200 ≤ kL P 3 := by omega_using [hsv, sv, tp, cst]
  have fP : SS + 2048 ≤ kL P 3 := by omega_using [hsv, sv, tp, cst]
  have fR : SG + 32 ≤ kL P 3 := by omega_using [hsv, sv, tp, cst]
  have fB : TP P + 168 * N₀ + 504 ≤ kL P 3 := by omega_using [hsv, sv, tp, cst, hN]
  have f1 : AH + 1024 * e + 1024 ≤ kL P 3 := by omega_using [hsv, sv, tp, cst, he]
  have f2 : AH + 1024 * (e + 1) + 1024 ≤ kL P 3 := by omega_using [hsv, sv, tp, cst, he]
  have x0 : SS + 2048 ≤ TP P + 168 * N₀ := by omega_using [tp, cst]
  have x1 : SG + 32 ≤ TP P + 168 * N₀ := by omega_using [tp, cst]
  have x2 : AH + 1024 * (e + 1) + 1024 ≤ TP P + 168 * N₀ := by omega_using [tp, cst, he]
  simp only [Impl.MlKem.AArch64.Kem16P.bufOff]
  refine ⟨⟨cov_w hp h (b := 3) (by decide) fP, by rw [stR_scratch]; exact cov_w hp h (b := 3) (by decide) fS,
    by rw [h.sp]; exact hk.sp, by rw [stR_scratch]; exact sdisjK hp fS fP (.inl (by omega_using [cst])),
    by rw [h.sp]; exact hk.R (by decide) fP, by rw [h.sp, stR_scratch]; exact hk.R (by decide) fS,
    cov_r hp h (b := 3) (by decide) fR, by rw [stR_scratch]; exact sdisjK hp fS fR (.inl (by omega_using [cst])),
    sdisjK hp fP fR (.inr (by omega_using [cst])), by rw [h.sp]; exact hk.R (by decide) fR,
    cov_w hp h (b := 3) (by decide) fB, by rw [stR_scratch]; exact sdisjK hp fS fB (.inl (by omega_using [cst, x1])),
    sdisjK hp fP fB (.inl x0), by rw [h.sp]; exact hk.R (by decide) fB,
    sdisjK hp fR fB (.inl x1)⟩,
    h.x28, by rw [stR_scratch]; exact mt.apart.sub_right (R.sub fS), tk.shuffle,
    by rw [stR_scratch]; exact sdisjK hp f1 fS (.inr (by omega_using [cst])),
    by rw [stR_scratch]; exact sdisjK hp f2 fS (.inr (by omega_using [cst])),
    sdisjK hp f1 fB (.inl (by omega_using [x2])), sdisjK hp f2 fB (.inl x2),
    mt.apart.sub_right (R.sub fB)⟩

/-- What a pair of key generation computing PRF outputs from `N₀` writes. -/
abbrev pairWritesK (P : KemLay) (s₀ : State) (e N₀ : Nat) : List Region :=
  pairWritesP (kA s₀ 3 + BitVec.ofNat 64 SS) (kA s₀ 3 + BitVec.ofNat 64 (AH + 1024 * e))
    (kA s₀ 3 + BitVec.ofNat 64 (AH + 1024 * (e + 1))) (kA s₀ 3) s₀.sp
    (kA s₀ 3 + BitVec.ofNat 64 (Impl.MlKem.AArch64.Kem16P.bufOff (TP P) N₀))

theorem pairK_far {s₀ : State} (hp : Pre P s₀) (hk : Stk128K P s₀) {e N₀ : Nat} (he : e + 1 < P.k * P.k)
    (hN : N₀ + 3 ≤ 6) {b o l : Nat} (hb : b < 4) (hf : o + l ≤ kL P b)
    (hs : b ≠ 3 ∨ ((o + l ≤ SS ∨ SS + 2048 ≤ o) ∧ (o + l ≤ AH + 1024 * e ∨ AH + 1024 * (e + 2) ≤ o) ∧ 200 ≤ o ∧
      (o + l ≤ TP P + 168 * N₀ ∨ TP P + 168 * N₀ + 504 ≤ o))) :
    ∀ r ∈ pairWritesK P s₀ e N₀, (R (kA s₀) b o l).Disjoint r := by
  have hw := hp.wf
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact pairH_far hp hk he hb hf (by rcases hs with hs | hs; exacts [.inl hs, .inr ⟨hs.1, hs.2.1, hs.2.2.1⟩]) r hr
  · rw [List.mem_singleton.mp hr]
    show (R (kA s₀) b o l).Disjoint (R (kA s₀) 3 (TP P + 168 * N₀) 504)
    exact hp.args.rdisj hb (by decide) hf (by kl) (by rcases hs with hs | hs; exacts [.inl hs, .inr hs.2.2.2])

/-- The writes of a pair computing PRF outputs lie in `scratch` and the frame. -/
theorem pairK_wr {s₀ s : State} (hp : Pre P s₀) (hk : KB P s₀ s) {e N₀ : Nat} (he : e + 1 < P.k * P.k)
    (hN : N₀ + 3 ≤ 6) : ∀ q ∈ pairWritesK P s₀ e N₀, ∃ q' ∈ s.wr ++ [frame s.sp], Region.Sub q q' := by
  have hw := hp.wf
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact pairH_wr hp hk he q hq
  · rw [List.mem_singleton.mp hq]
    have sc : (⟨kA s₀ 3, kL P 3⟩ : Region) ∈ s.wr ++ [frame s.sp] := by rw [hk.wr, hp.wr]; simp
    exact ⟨_, sc, R.sub (A := kA s₀) (b := 3) (o := TP P + 168 * N₀) (l := 504) (by kl)⟩

/-- The matrix's invariant after a pair computing PRF outputs (as `BInvW.pairedH`). -/
theorem BInvW.pairedK {s₀ s t : State} (hp : Pre P s₀) (hk : Stk128K P s₀) {e N₀ m : Nat}
    (he : e + 1 < P.k * P.k) (hN : N₀ + 3 ≤ 6) (h : BInvW true P s₀ e s) {Rr : Addr}
    (ht : PairPOutcomeW true (matSeed (rhoK P s₀) (e / P.k) (e % P.k))
      (matSeed (rhoK P s₀) ((e + 1) / P.k) ((e + 1) % P.k))
      (kA s₀ 3 + BitVec.ofNat 64 SS) (kA s₀ 3 + BitVec.ofNat 64 (AH + 1024 * e))
      (kA s₀ 3 + BitVec.ofNat 64 (AH + 1024 * (e + 1))) (kA s₀ 3) Rr
      (kA s₀ 3 + BitVec.ofNat 64 (Impl.MlKem.AArch64.Kem16P.bufOff (TP P) N₀)) N₀ m s t) :
    BInvW true P s₀ (e + 2) t := by
  have hw := hp.wf
  have fr : Frame (pairWritesK P s₀ e N₀) s.mem t.mem := by
    have f := ht.frame; rw [h.kb.sp] at f; exact f
  have far {b o l : Nat} (hb : b < 4) (hf : o + l ≤ kL P b) hs := pairK_far hp hk he hN hb hf hs
  have old {i : Nat} (hi : i < e) := far (b := 3) (o := AH + 1024 * i) (l := 1024)
    (by decide) (by simp only [kL]; lom) (.inr ⟨.inr (by lom), .inl (by lom), by lom, .inl (by lom)⟩)
  have kbt : KB P s₀ t := h.kb.frame ht.keep fr (by decide) fun r hr =>
    ⟨far (b := 3) (o := SV P) (l := 48) (by decide) hp.sv
      (.inr ⟨.inr (by lom), .inr (by lom), by lom, .inr (by lom)⟩) r hr,
     far (b := 0) (o := 0) (l := 64) (by decide) (by kl) (.inl (by decide)) r hr⟩
  refine ⟨kbt, ?_, ?_, ?_, ?_, ?_⟩
  · rw [bytesAt_frame fr (far (by decide) (by kl) (.inr ⟨.inl (by lom), .inl (by lom), by lom, .inl (by lom)⟩))
      (by decide)]
    exact h.rho
  · rw [bytesAt_frame fr (far (by decide) (by kl) (.inr ⟨.inl (by lom), .inl (by lom), by lom, .inl (by lom)⟩))
      (by decide)]
    exact h.sig
  · have hall : allOk P s₀ (e + 2) ↔ (allOk P s₀ e ∧
        (sampleNTT 280 (matSeed (rhoK P s₀) (e / P.k) (e % P.k))).isSome) ∧
        (sampleNTT 280 (matSeed (rhoK P s₀) ((e + 1) / P.k) ((e + 1) % P.k))).isSome := by
      rw [show e + 2 = (e + 1) + 1 by omega, allOk_succ, allOk_succ]
    rw [ht.status, h.acc]
    by_cases ha : allOk P s₀ e <;>
      by_cases hb : (sampleNTT 280 (matSeed (rhoK P s₀) (e / P.k) (e % P.k))).isSome <;>
      by_cases hc : (sampleNTT 280 (matSeed (rhoK P s₀) ((e + 1) / P.k) ((e + 1) % P.k))).isSome <;>
      simp [hall, ha, hb, hc]
  · intro i hi
    rcases (by omega : i < e ∨ i = e ∨ i = e + 1) with hi | rfl | rfl
    · exact reducedW_frame fr (old hi) (h.red i hi)
    · exact ht.reducedLeft
    · exact ht.reducedRight
  · intro i hi
    rcases (by omega : i < e ∨ i = e ∨ i = e + 1) with hi | rfl | rfl
    · rw [aAtW, polyAtW_frame fr (old hi)]; exact h.res i hi
    · exact ht.left
    · exact ht.right

/-- **Pair `p < 2`** of key generation's matrix, computing `PRF₂(σ, 3p)`, …, `PRF₂(σ, 3p + 2)`. -/
theorem first_step {s₀ s : State} (hp : Pre P s₀) (hk : Stk128K P s₀) {p : Nat} (hp2 : p < 2)
    (hk3 : 3 ≤ P.k) (H : FInv P s₀ (2 * p) (3 * p) s) :
    WP isa (Impl.MlKem.AArch64.Kem16P.kgPairP P p) s (FInv P s₀ (2 * p + 2) (3 * p + 3)) := by
  have hw := hp.wf
  have kb := H.b.kb
  have hf := hw.facts
  have hkk : P.k * P.k ≤ 16 := hf.2.2.1
  have he : 2 * p + 1 < P.k * P.k := by
    have := Nat.mul_le_mul hk3 hk3; omega
  have hN : 3 * p + 3 ≤ 6 := by omega
  have hoa : AH + 1024 * (2 * p) < 65536 := by simp only [KG.AH]; omega
  have hob : AH + 1024 * (2 * p + 1) < 65536 := by simp only [KG.AH]; omega
  have hbo : Impl.MlKem.AArch64.Kem16P.bufOff (TP P) (3 * p + 2) < 65536 := by
    have h3 := kL_le hw 3
    have hsv := hp.sv
    have sv : SV P = TP P + 2048 := rfl
    simp only [Impl.MlKem.AArch64.Kem16P.bufOff]; omega_using [h3, hsv, sv, hp2]
  have hk1 : 0 < P.k := by omega
  have hk2 : P.k ≤ 256 := by omega
  have mt := matrixTable_of hp kb H.tables
  have pin := pair_input hp he kb mt
  have hin := prf_inputK hp hk he hN kb H.tstk mt
  unfold Impl.MlKem.AArch64.Kem16P.kgPairP
  rw [Kem16P.pairP_iff]
  refine WP.mono_syms (Kem16P.pairPCode_ok P SG (TP P) (a := 2 * p) (N₀ := 3 * p) (m := 3) (by omega) hbo
    (by decide) (by decide) (by decide) hoa hob pin hin rfl (by decide) (by decide) rfl
    (by rw [H.b.acc]; split; exacts [Or.inr rfl, Or.inl rfl])) fun t ht sy => ?_
  have post := ht.outcome hk1 hk2
  simp only [Paired.seedBytes, H.b.rho] at post
  have fr : Frame (pairWritesK P s₀ (2 * p) (3 * p)) s.mem t.mem := by
    have f := post.frame; rw [kb.sp] at f; exact f
  have bt := BInvW.pairedK hp hk he hN H.b post
  refine ⟨bt, fun N hN' => ?_, ?_, H.tstk.of sy (by rw [bt.kb.sp, kb.sp])⟩
  · by_cases hlt : N < 3 * p
    · unfold PrfK
      rw [bytesAt_frame fr (pairK_far hp hk he hN (b := 3) (o := TP P + 168 * N) (l := 128) (by decide) (by kl)
        (.inr ⟨.inr (by lom), .inr (by lom), by lom, .inl (by omega)⟩)) (by decide)]
      exact H.prf N hlt
    · have hk' : N - 3 * p < min 3 3 := by omega
      have pr := post.prf (N - 3 * p) hk'
      rw [show 3 * p + (N - 3 * p) = N by omega] at pr
      have ob := Noise.output_prf (by omega) pr
      rw [H.b.sig] at ob
      unfold PrfK
      refine Eq.trans (congrArg (fun a => bytesAt t.mem a 128) ?_) ob
      simp only [bufAt, Impl.MlKem.AArch64.Kem16P.bufOff]
      rw [BitVec.add_assoc, ← BitVec.ofNat_add,
        show TP P + 168 * (3 * p) + 168 * (N - 3 * p) = TP P + 168 * N by omega]
  · exact Hybrid.tables_frame128 H.tables H.tstk sy post.keep.rd post.keep.wr post.keep.sp
      (fr.sub (pairK_wr hp kb he hN))

/-- **The first two pairs** of key generation's matrix, computing the first six PRF outputs. -/
theorem first_ok {s₀ s : State} (hp : Pre P s₀) (hk : Stk128K P s₀) (hk3 : 3 ≤ P.k) (H : FInv P s₀ 0 0 s) :
    WP isa (.seq (Impl.MlKem.AArch64.Kem16P.kgPairP P 0) (Impl.MlKem.AArch64.Kem16P.kgPairP P 1)) s
      (FInv P s₀ 4 6) :=
  WP.seq (WP.mono (first_step hp hk (p := 0) (by decide) hk3 H) fun _ h => first_step hp hk (p := 1) (by decide) hk3 h)

end VG.Proof.MlKem.AArch64.KeyGen
