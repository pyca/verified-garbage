module

public import VerifiedGarbage.Impl.MlKem.AArch64.Kem16P
public import VerifiedGarbage.Proof.MlKem.AArch64.KgH.Pair
public import VerifiedGarbage.Proof.Sha3.AArch64.Variant
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Correct
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Permute
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.KeyGenPrefix
import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Interface
public import VerifiedGarbage.Proof.MlKem.AArch64.KgCommon
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TransformTables
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Layout
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cover
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TableApart
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cbd16Call
public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.FastTable
public import VerifiedGarbage.Impl.MlKem.AArch64.NoiseWith
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.ReadonlyCalls
public import VerifiedGarbage.Proof.MlKem.AArch64.KeccakCall
public import VerifiedGarbage.Proof.MlKem.Mem16
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Output
import VerifiedGarbage.Proof.MlKem.CoeffW
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.W.Call
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.Pair

/-! ### `MlKem.AArch64.KgH.Prefix`, which this module and modules that import it used -/

section

/-! ### `MlKem.AArch64.KgH.First`, which this module and modules that import it used -/

section

/-! # Key generation's first two pairs, computing PRF outputs

The first two pairs of key generation's matrix absorb no block of `ek`
(`Kem16.hashedBy`): `Kem16P.kgPairP` computes `PRF₂(σ, 3p)`, …,
`PRF₂(σ, 3p + 2)` in the third state of their `x3` calls instead, into the
buffers from `KG.TP`. `FInv n c`: after `G`, `n` entries of `Â` and the
first `c` PRF outputs in their buffers. `first_step`: a pair keeps it. -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.KeyGen
variable {sha3 : Bool}

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
      rw [show e + 2 = (e + 1) + 1 by omega_arith, allOk_succ, allOk_succ]
    rw [ht.status, h.acc]
    by_cases ha : allOk P s₀ e <;>
      by_cases hb : (sampleNTT 280 (matSeed (rhoK P s₀) (e / P.k) (e % P.k))).isSome <;>
      by_cases hc : (sampleNTT 280 (matSeed (rhoK P s₀) ((e + 1) / P.k) ((e + 1) % P.k))).isSome <;>
      simp [hall, ha, hb, hc]
  · intro i hi
    rcases (by omega_arith : i < e ∨ i = e ∨ i = e + 1) with hi | rfl | rfl
    · exact reducedW_frame fr (old hi) (h.red i hi)
    · exact ht.reducedLeft
    · exact ht.reducedRight
  · intro i hi
    rcases (by omega_arith : i < e ∨ i = e ∨ i = e + 1) with hi | rfl | rfl
    · rw [aAtW, polyAtW_frame fr (old hi)]; exact h.res i hi
    · exact ht.left
    · exact ht.right

/-- **Pair `p < 2`** of key generation's matrix, computing `PRF₂(σ, 3p)`, …, `PRF₂(σ, 3p + 2)`. -/
theorem first_step {s₀ s : State} (hp : Pre P s₀) (hk : Stk128K P s₀) {p : Nat} (hp2 : p < 2)
    (hk3 : 3 ≤ P.k) (H : FInv P s₀ (2 * p) (3 * p) s) :
    WP isa (Impl.MlKem.AArch64.Kem16P.kgPairP sha3 P p) s (FInv P s₀ (2 * p + 2) (3 * p + 3)) := by
  have hw := hp.wf
  have kb := H.b.kb
  have hf := hw.facts
  have hkk : P.k * P.k ≤ 16 := hf.2.2.1
  have he : 2 * p + 1 < P.k * P.k := by
    have := Nat.mul_le_mul hk3 hk3; omega_arith
  have hN : 3 * p + 3 ≤ 6 := by omega_arith
  have hoa : AH + 1024 * (2 * p) < 65536 := by simp only [KG.AH]; omega_arith
  have hob : AH + 1024 * (2 * p + 1) < 65536 := by simp only [KG.AH]; omega_arith
  have hbo : Impl.MlKem.AArch64.Kem16P.bufOff (TP P) (3 * p + 2) < 65536 := by
    have h3 := kL_le hw 3
    have hsv := hp.sv
    have sv : SV P = TP P + 2048 := rfl
    simp only [Impl.MlKem.AArch64.Kem16P.bufOff]; omega_using [h3, hsv, sv, hp2]
  have hk1 : 0 < P.k := by omega_arith
  have hk2 : P.k ≤ 256 := by omega_arith
  have mt := matrixTable_of hp kb H.tables
  have pin := pair_input hp he kb mt
  have hin := prf_inputK hp hk he hN kb H.tstk mt
  unfold Impl.MlKem.AArch64.Kem16P.kgPairP
  rw [Kem16P.pairP_iff]
  refine WP.mono_syms (Kem16P.pairPCode_ok (sha3 := sha3) P SG (TP P) (a := 2 * p) (N₀ := 3 * p) (m := 3) (by omega_arith) hbo
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
        (.inr ⟨.inr (by lom), .inr (by lom), by lom, .inl (by omega_arith)⟩)) (by decide)]
      exact H.prf N hlt
    · have hk' : N - 3 * p < min 3 3 := by omega_arith
      have pr := post.prf (N - 3 * p) hk'
      rw [show 3 * p + (N - 3 * p) = N by omega_arith] at pr
      have ob := Noise.output_prf (by omega_arith) pr
      rw [H.b.sig] at ob
      unfold PrfK
      refine Eq.trans (congrArg (fun a => bytesAt t.mem a 128) ?_) ob
      simp only [bufAt, Impl.MlKem.AArch64.Kem16P.bufOff]
      rw [BitVec.add_assoc, ← BitVec.ofNat_add,
        show TP P + 168 * (3 * p) + 168 * (N - 3 * p) = TP P + 168 * N by omega_arith]
  · exact Hybrid.tables_frame128 H.tables H.tstk sy post.keep.rd post.keep.wr post.keep.sp
      (fr.sub (pairK_wr hp kb he hN))

end VG.Proof.MlKem.AArch64.KeyGen

end

end

/-! ### `MlKem.AArch64.KgH.NoiseK`, which only this module used -/

section

/-! ### `MlKem.AArch64.Noise.Writes`, which only this module used -/

section

/-! # Exact paired-noise footprints and separated retained outputs -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Noise
variable {sha3 : Bool}
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Proof.Sha3.AArch64.Neon

def writes (L : KemLay) (kg : Bool) (B : Addr) (n : Nat) : List Region :=
 pairWrites (B+BitVec.ofNat 64 (scratchOff kg))
   (B+BitVec.ofNat 64 (outOff L kg n)) (B+BitVec.ofNat 64 (outOff L kg (n+1)))
   (B+BitVec.ofNat 64 (nttOff kg))

theorem writes_apart {L : KemLay} (wf : L.Wf) (room : Room L) (kg : Bool) (B : Addr)
    {n off len : Nat} (hn : n+1<2*L.k) (hfit : off+len≤L.scl)
    (hss : off+len≤scratchOff kg ∨ scratchOff kg+2048≤off)
    (hns : off+len≤nttOff kg ∨ nttOff kg+1024≤off)
    (hf : off+len≤outOff L kg n ∨ outOff L kg n+1024≤off)
    (hg : off+len≤outOff L kg (n+1) ∨ outOff L kg (n+1)+1024≤off) :
    ∀r∈writes L kg B n, (Region.mk (B+BitVec.ofNat 64 off) len).Disjoint r := by
  obtain lim := layout_limits wf kg
  obtain f0 := outOff_fits wf room kg (by omega_using [hn] : n<2*L.k)
  obtain f1 := outOff_fits wf room kg hn
  have sep {o k : Nat} (h : off+len≤o ∨ o+k≤off) (fit : o+k≤L.scl) :=
    Offset.disjoint B h (by omega_using [hfit, lim] : off+len≤2^64) (by omega_using [lim, fit] : o+k≤2^64)
  intro r hr
  simp only [writes,pairWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (Region.mk (B+BitVec.ofNat 64 off) len).Disjoint
      ⟨B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 1800,48⟩
    rw [BitVec.add_assoc,← BitVec.ofNat_add]
    exact sep (by omega_using [hss]) (by omega_using [lim])
  · exact sep (by omega_using [hss]) (by omega_using [lim])
  · change (Region.mk (B+BitVec.ofNat 64 off) len).Disjoint
      ⟨B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 400,128⟩
    rw [BitVec.add_assoc,← BitVec.ofNat_add]
    exact sep (by omega_using [hss]) (by omega_using [lim])
  · change (Region.mk (B+BitVec.ofNat 64 off) len).Disjoint
      ⟨B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 528,128⟩
    rw [BitVec.add_assoc,← BitVec.ofNat_add]
    exact sep (by omega_using [hss]) (by omega_using [lim])
  · change (Region.mk (B+BitVec.ofNat 64 off) len).Disjoint
      ⟨B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 1536,136⟩
    rw [BitVec.add_assoc,← BitVec.ofNat_add]
    exact sep (by omega_using [hss]) (by omega_using [lim])
  · exact sep hf f0
  · exact sep hg f1
  · exact sep hns lim.2.2.1

theorem writes_old_far {L : KemLay} (wf : L.Wf) (room : Room L) (kg : Bool) (B : Addr)
    {n j : Nat} (hn : n+1<2*L.k) (hj : j<n) :
    ∀r∈writes L kg B n, (polyRegion (B+BitVec.ofNat 64 (outOff L kg j))).Disjoint r := by
  obtain lim := layout_limits wf kg
  obtain lo := outOff_low wf room kg j
  change nttOff kg+1024≤_ at lo
  obtain f := outOff_fits wf room kg (by omega_using [hn, hj] : j<2*L.k)
  exact writes_apart wf room kg B hn f (Or.inr (by omega_using [lim, lo])) (Or.inr lo)
    (Or.inl (outOff_order wf room kg hj)) (Or.inl (outOff_order wf room kg (by omega_using [hj])))

end VG.Proof.MlKem.AArch64.Noise

end

end

/-! ### `MlKem.AArch64.Noise.ReadonlyLayoutPair`, which only this module used -/

section

/-! ### `MlKem.AArch64.Noise.ReadonlyPairTail`, which only this module used -/

section

/-! ### `MlKem.AArch64.Noise.OutWith`, which only this module used -/

section

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Noise
variable {sha3 : Bool}
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

def outCodeWith (nttAt : Nat→Nat→Prog isa) (off ns buf : Nat) (tr : Bool) :
    Prog isa :=
 seqs [.block (([.addImm .x .x0 .x19 buf] : List Instr)++ptrTo .x1 .x28 off),
   Impl.MlKem.AArch64.Noise.cbdCall,if tr then nttAt off ns else .block []]

theorem out_okWith {s : State} {off ns buf : Nat} {b f w : Addr} (transform : Bool)
 (nttAt : Nat→Nat→Prog isa) (hoff : off<65536) (hbuf : buf<4096)
 (hb : s.gpr .x19+BitVec.ofNat 64 buf=b) (hf : s.gpr .x28+BitVec.ofNat 64 off=f)
 (hbf : (Region.mk b 128).Disjoint ⟨f,1024⟩)
 (hc : Covers [⟨b,128⟩,⟨f,1024⟩] (s.rd++s.wr))
 (hcw : Covers [⟨f,1024⟩,⟨w,1024⟩] s.wr)
 (hn : ∀v, Kept [⟨f,1024⟩,⟨w,1024⟩] s v → v.syms=s.syms →
   PolyIsW (cw true) v.mem f (samplePolyCBD 2 (bytesAt s.mem b 128)) →
   WP isa (nttAt off ns) v fun t=> Kept [⟨f,1024⟩,⟨w,1024⟩] v t ∧
     PolyIsW (cw true) t.mem f (ntt (samplePolyCBD 2 (bytesAt s.mem b 128)))) :
 WP isa (outCodeWith nttAt off ns buf transform) s fun t=>
   Kept [⟨f,1024⟩,⟨w,1024⟩] s t ∧
   PolyIsW (cw true) t.mem f (if transform then ntt (samplePolyCBD 2 (bytesAt s.mem b 128))
     else samplePolyCBD 2 (bytesAt s.mem b 128)) := by
 obtain sample : WP isa (.seq (.block (([.addImm .x .x0 .x19 buf] : List Instr)++ptrTo .x1 .x28 off))
     (Impl.MlKem.AArch64.Noise.cbdCall)) s fun v=>Kept [⟨f,1024⟩,⟨w,1024⟩] s v ∧
       PolyIsW (cw true) v.mem f (samplePolyCBD 2 (bytesAt s.mem b 128)) := by
  refine WP.seq (wp_addImm hbuf fun a ha ea=>wp_ptrTo' (by decide) hoff fun u hu eu=>?_)
  obtain ou : Only [.x0,.x1] s u := (ha.trans hu).mono (by simp)
  obtain ku : Kept [⟨f,1024⟩,⟨w,1024⟩] s u := Kept.of_keep ou.keep ou.mem (by decide)
  exact cbdW_call (by rw [hu.get .x0 (by decide),ea]; exact hb)
    (by rw [eu,ha.get .x28 (by decide)]; exact hf) hbf
    (by rw [ou.rd,ou.wr]; exact hc)
    (by rw [ou.wr]; intro a n ⟨r,hr,ha⟩; exact hcw a n ⟨r,by simp at hr; simp [hr],ha⟩)
    (fun v kv pv=>⟨ku.trans (kv.mono (by simp)),by simpa only [ou.mem] using pv⟩)
 apply WP.assoc
 refine WP.seq (WP.mono_syms sample fun v ⟨kv,pv⟩ sv=>?_)
 cases transform
 · exact wp_nil ⟨kv,pv⟩
 · exact WP.mono (hn v kv sv pv) fun t ⟨kt,pt⟩=>⟨kv.trans kt,pt⟩
end VG.Proof.MlKem.AArch64.Noise

end

end

/-! # Paired PRF call, both polynomial outputs and register restoration -/

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Noise/ReadonlyOut.lean`, which only this module imported.
section

section
namespace VG.Proof.MlKem.AArch64.Noise
variable {sha3 : Bool}
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- One noise output with 16-bit coefficients, transformed (`nttAtWithW`) if `transform`. -/
theorem readonly_out_okW {s : State} {off ns buf : Nat} {b f w : Addr} (transform : Bool)
 (hoff : off<65536) (hns : ns<65536) (hbuf : buf<4096)
 (hb : s.gpr .x19+BitVec.ofNat 64 buf=b) (hf : s.gpr .x28+BitVec.ofNat 64 off=f)
 (hw : s.gpr .x28+BitVec.ofNat 64 ns=w)
 (hbf : (Region.mk b 128).Disjoint ⟨f,1024⟩) (hfw : (polyRegion f).Disjoint (polyRegion w))
 (hc : Covers [⟨b,128⟩,⟨f,1024⟩] (s.rd++s.wr))
 (hcw : Covers [⟨f,1024⟩,⟨w,1024⟩] s.wr)
 (ht : NttR.FastReady s f w) :
 WP isa (outCodeWith Ntt16.Readonly.nttAtWithW off ns buf transform) s fun t=>
   Kept [⟨f,1024⟩,⟨w,1024⟩] s t ∧
   PolyIsW (cw true) t.mem f (if transform then ntt (samplePolyCBD 2 (bytesAt s.mem b 128))
     else samplePolyCBD 2 (bytesAt s.mem b 128)) := by
 refine out_okWith transform _ hoff hbuf hb hf hbf hc hcw fun v kv sv pv=>?_
 obtain table := ht.frame sv kv.rd kv.wr kv.frame (by
   intro r hr
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
   rcases hr with rfl|rfl
   · exact ht.output.symm
   · exact ht.scratch.symm)
 obtain sub : ∀ x ∈ [Region.mk f 512, ⟨w,512⟩], ∃ r ∈ [Region.mk f 1024, ⟨w,1024⟩], Region.Sub x r := by
   intro x hx
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
   rcases hx with rfl|rfl
   · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide : 512 ≤ 1024)⟩
   · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Region.sub_prefix (by decide : 512 ≤ 1024)⟩
 refine WP.mono (Ntt16.W.nttAtWithW_ok hoff hns
   (by rw [kv.cs .x28 (by decide) (by decide)]; exact hf)
   (by rw [kv.cs .x28 (by decide) (by decide)]; exact hw)
   (hfw.sub_left (Region.sub_prefix (by decide : 512 ≤ 1024)) |>.sub_right (Region.sub_prefix (by decide : 512 ≤ 1024)))
   pv (by
     rw [kv.wr]
     exact Covers.cons (covers_prefix (by decide : 512 ≤ 1024) (Covers.head hcw))
       (Covers.cons (covers_prefix (by decide : 512 ≤ 1024) (Covers.head (Covers.tail hcw))) Covers.nil))
   table) fun t ⟨kt,pt⟩ => ⟨Kept.sub kt sub, pt⟩
end VG.Proof.MlKem.AArch64.Noise
end

end

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Noise
variable {sha3 : Bool}
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

theorem readonly_pair_tail_ok {initial s : State} {p a f g w : Addr} {off0 off1 ns n : Nat}
    (tr0 tr1 : Bool) (hn : n+1<256) (h0 : off0<65536) (h1 : off1<65536) (hns : ns<65536)
    (hk : Partial (pairWrites p f g w) initial s) (sv : Saved p initial s.mem)
    (hp : s.gpr .x19=p) (ha : s.gpr .x20=p+400) (hb : s.gpr .x21=p+528)
    (hf : s.gpr .x28+BitVec.ofNat 64 off0=f)
    (hg : s.gpr .x28+BitVec.ofNat 64 off1=g)
    (hw : s.gpr .x28+BitVec.ofNat 64 ns=w)
    (hs : TailSetup s p f g w)
    (hpair : PairAt s.mem p (seedState initial.mem a n) (seedState initial.mem a (n+1)))
    (ht0 : NttR.FastReady s f w)
    (ht1 : NttR.FastReady s g w)
    (hfar : ∀r∈pairWrites p f g w,(NttR.fastRegion s).Disjoint r) :
    WP isa (seqs [Impl.MlKem.AArch64.Noise.squeezePair sha3,outCodeWith Ntt16.Readonly.nttAtWithW off0 ns 400 tr0,outCodeWith Ntt16.Readonly.nttAtWithW off1 ns 528 tr1,
      .block (Paired.saved.zipIdx.reverse.map fun (r,i) => .ldr .x r .x19 (1800+8*i))]) s fun t =>
      Kept (pairWrites p f g w) initial t ∧
      PolyIsW (cw true) t.mem f (sampled initial.mem a n tr0) ∧
      PolyIsW (cw true) t.mem g (sampled initial.mem a (n+1) tr1) := by
  simp only [seqs]
  refine WP.seq (WP.mono_syms (squeezePair_ok (sha3 := sha3) hp ha hb (by rw [hp])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) hpair hs.pair hs.rateA hs.rateB
    (Offset.disjoint p (by decide) (by decide) (by decide))
    (Offset.base_disjoint p (by decide) (by decide))
    (Offset.base_disjoint p (by decide) (by decide))
    (Offset.base_disjoint p (by decide) (by decide)) hs.call) fun u ⟨ku,_,ra,rb,fu,vu⟩ su => ?_)
  have pu : Partial (pairWrites p f g w) initial u := hk.trans
    ⟨fun r hr hn => ku.gpr r (by revert r hr hn; decide),ku.rd,ku.wr,ku.sp,vu,fu.mono (by simp [pairWrites])⟩
  obtain svu : Saved p initial u.mem := sv.frame fu (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Offset.disjoint_base p (by decide) (by decide)
    · exact Offset.disjoint p (by decide) (by decide) (by decide)
    · exact Offset.disjoint p (by decide) (by decide) (by decide)
    · exact Offset.disjoint p (by decide) (by decide) (by decide))
  obtain tab0 := ht0.frame su ku.rd ku.wr fu (by
    intro r hr; exact hfar r (by simp only [pairWrites,List.mem_cons,List.not_mem_nil,or_false] at hr ⊢; grind))
  obtain tab1 := ht1.frame su ku.rd ku.wr fu (by
    intro r hr; exact hfar r (by simp only [pairWrites,List.mem_cons,List.not_mem_nil,or_false] at hr ⊢; grind))
  obtain r0 := output_prf (by omega_using [hn] : n<256) ra
  obtain r1 := output_prf hn rb
  refine WP.seq (WP.mono_syms (readonly_out_okW tr0 h0 hns (by decide)
    (by rw [ku.gpr .x19 (by decide),hp]; rfl)
    (by rw [ku.gpr .x28 (by decide)]; exact hf)
    (by rw [ku.gpr .x28 (by decide)]; exact hw)
    hs.bufA hs.fw (by rw [ku.rd,ku.wr]; exact hs.cbdA)
    (by rw [ku.wr]; exact hs.nttA) tab0) fun v ⟨kv,pv⟩ vuSym => ?_)
  obtain pvv : PolyIsW (cw true) v.mem f (sampled initial.mem a n tr0) := by simpa only [r0,sampled] using pv
  obtain pkeep : Partial (pairWrites p f g w) initial v := pu.trans ((Partial.of_kept kv).mono (by simp [pairWrites]))
  obtain svv : Saved p initial v.mem := svu.frame kv.frame (by
    intro r hr; apply hs.savedFar r
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
    rcases hr with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h))
  obtain r1v : bytesAt v.mem (p+528) 128 = prf 2 (bytesAt initial.mem a 32) (BitVec.ofNat 8 (n+1)) :=
    (Proof.MlKem.bytesAt_frame kv.frame hs.next (by decide)).trans r1
  obtain tab1v := tab1.frame vuSym kv.rd kv.wr kv.frame (by
    intro r hr
    simp only [NttR.sRegion, su]
    exact hfar r (by simp only [pairWrites,List.mem_cons,List.not_mem_nil,or_false] at hr ⊢; grind))
  refine WP.seq (WP.mono (readonly_out_okW tr1 h1 hns (by decide)
    (by rw [kv.cs .x19 (by decide) (by decide),ku.gpr .x19 (by decide),hp]; rfl)
    (by rw [kv.cs .x28 (by decide) (by decide),ku.gpr .x28 (by decide)]; exact hg)
    (by rw [kv.cs .x28 (by decide) (by decide),ku.gpr .x28 (by decide)]; exact hw)
    hs.bufB hs.gw (by rw [kv.rd,kv.wr,ku.rd,ku.wr]; exact hs.cbdB)
    (by rw [kv.wr,ku.wr]; exact hs.nttB) tab1v) fun z ⟨kz,pz⟩ => ?_)
  obtain pzz : PolyIsW (cw true) z.mem g (sampled initial.mem a (n+1) tr1) := by simpa only [r1v,sampled] using pz
  obtain pfz : PolyIsW (cw true) z.mem f (sampled initial.mem a n tr0) :=
    Proof.MlKem.polyIsW_frame_poly kz.frame (by simpa using And.intro hs.fg hs.fw) pvv
  obtain pkeepz := pkeep.trans ((Partial.of_kept kz).mono (by simp [pairWrites]))
  obtain svz : Saved p initial z.mem := svv.frame kz.frame (by
    intro r hr; apply hs.savedFar r; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢; exact Or.inr hr)
  refine WP.mono (restores_ok (by
    rw [kz.cs .x19 (by decide) (by decide),kv.cs .x19 (by decide) (by decide),ku.gpr .x19 (by decide),hp]) svz
    (fun i hi => by rw [kz.rd,kz.wr,kv.rd,kv.wr,ku.rd,ku.wr]; exact hs.saved i hi)) fun t ⟨ot,rt⟩ => ?_
  exact ⟨pkeepz.restore ot rt,by rw [ot.mem]; exact pfz,by rw [ot.mem]; exact pzz⟩

end VG.Proof.MlKem.AArch64.Noise

end

end

/-! # Execute a pair using only the public scratch allocation -/

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Noise/ReadonlyPair.lean`, which only this module imported.
section

/-! # Complete paired-noise operation -/
section
namespace VG.Proof.MlKem.AArch64.Noise
variable {sha3 : Bool}
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlKem (PolyIsW)
open VG.Proof.MlKem (cw)

theorem readonly_noisePair_ok {s : State} {L : KemLay} (kg : Bool) {n : Nat} {p a f g w : Addr}
    (hn : n+1<256)
    (h0 : outOff L kg n <65536) (h1 : outOff L kg (n+1)<65536)
    (hp : s.gpr .x28+BitVec.ofNat 64 (if kg then KG.SS else KEM.SS)=p)
    (ha : s.gpr .x28+BitVec.ofNat 64 (if kg then KG.SG else KEM.RB)=a)
    (hf : s.gpr .x28+BitVec.ofNat 64 (outOff L kg n)=f)
    (hg : s.gpr .x28+BitVec.ofNat 64 (outOff L kg (n+1))=g)
    (hw : s.gpr .x28+BitVec.ofNat 64 (if kg then KG.NS else KEM.NS)=w)
    (hin : ∀j<4, InRegions (s.rd++s.wr) (a+BitVec.ofNat 64 (8*j)) 8)
    (hwr : ∀j<25, InRegions s.wr (wordAddr p j) 16)
    (hsv : ∀j<6, InRegions s.wr (p+BitVec.ofNat 64 (1800+8*j)) 8)
    (has : (Region.mk a 32).Disjoint (savedR p))
    (hap : (Region.mk a 32).Disjoint (pairR p))
    (hs : TailSetup s p f g w)
    (ht0 : NttR.FastReady s f w)
    (ht1 : NttR.FastReady s g w)
    (hfar : ∀r∈pairWrites p f g w,(NttR.fastRegion s).Disjoint r) :
    WP isa (Impl.MlKem.AArch64.Noise.noisePairWith sha3 Ntt16.Readonly.nttAtWithW L kg n) s fun t =>
      Kept (pairWrites p f g w) s t ∧
      PolyIsW (cw true) t.mem f (sampled s.mem a n (transformed L kg n)) ∧
      PolyIsW (cw true) t.mem g (sampled s.mem a (n+1) (transformed L kg (n+1))) := by
  change WP isa (.seq (.block (Impl.MlKem.AArch64.Noise.noiseInit L kg n))
    (seqs [Impl.MlKem.AArch64.Noise.squeezePair sha3,
      outCodeWith Ntt16.Readonly.nttAtWithW (outOff L kg n) (if kg then KG.NS else KEM.NS) 400 (transformed L kg n),
      outCodeWith Ntt16.Readonly.nttAtWithW (outOff L kg (n+1)) (if kg then KG.NS else KEM.NS) 528 (transformed L kg (n+1)),
      .block (Paired.saved.zipIdx.reverse.map fun (r,i) => .ldr .x r .x19 (1800+8*i))])) s _
  refine WP.seq (WP.mono_syms (init_ok (by cases kg <;> decide) hn
    (by cases kg <;> decide) (by cases kg <;> decide) hp ha hin hwr hsv has hap
    (Offset.disjoint_base p (by decide) (by decide))) fun u ⟨ku,fu,sv,h19,h20,h21,pair⟩ us => ?_)
  obtain pu : Partial (pairWrites p f g w) s u :=
    ⟨fun r hr hn => ku.gpr r (by revert r hr hn; decide),ku.rd,ku.wr,ku.sp,ku.vcs,
      fu.mono (by simp [pairWrites])⟩
  obtain t0 := ht0.frame us ku.rd ku.wr fu (by
    intro r hr; exact hfar r (by simp only [pairWrites,List.mem_cons,List.not_mem_nil,or_false] at hr ⊢; grind))
  obtain t1 := ht1.frame us ku.rd ku.wr fu (by
    intro r hr; exact hfar r (by simp only [pairWrites,List.mem_cons,List.not_mem_nil,or_false] at hr ⊢; grind))
  exact readonly_pair_tail_ok (transformed L kg n) (transformed L kg (n+1)) hn h0 h1
    (by cases kg <;> decide) pu sv h19 h20 h21
    (by rw [ku.gpr .x28 (by decide)]; exact hf)
    (by rw [ku.gpr .x28 (by decide)]; exact hg)
    (by rw [ku.gpr .x28 (by decide)]; exact hw)
    (hs.regions ku.rd ku.wr) pair t0 t1 (by simpa only [NttR.fastRegion, NttR.sRegion, us] using hfar)

end VG.Proof.MlKem.AArch64.Noise
end

end

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Noise
variable {sha3 : Bool}
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Proof.MlKem (PolyIsW)
open VG.Proof.MlKem (cw)
open VG.Proof.Sha3.AArch64.Neon


theorem readonly_noisePair_layout {s : State} {L : KemLay} (wf : L.Wf) (room : Room L) (kg : Bool)
    {B : Addr} {n : Nat} (hn : n+1<2*L.k) (hB : s.gpr .x28=B)
    (hc : Covers [⟨B,L.scl⟩] s.wr)
    (ht0 : NttR.FastReady s
      (B+BitVec.ofNat 64 (outOff L kg n)) (B+BitVec.ofNat 64 (nttOff kg)))
    (ht1 : NttR.FastReady s
      (B+BitVec.ofNat 64 (outOff L kg (n+1))) (B+BitVec.ofNat 64 (nttOff kg)))
    (hfar : ∀r∈pairWrites (B+BitVec.ofNat 64 (scratchOff kg))
      (B+BitVec.ofNat 64 (outOff L kg n)) (B+BitVec.ofNat 64 (outOff L kg (n+1)))
      (B+BitVec.ofNat 64 (nttOff kg)), (NttR.fastRegion s).Disjoint r) :
    WP isa (Impl.MlKem.AArch64.Noise.noisePairWith sha3 Ntt16.Readonly.nttAtWithW L kg n) s fun t =>
      Kept (pairWrites (B+BitVec.ofNat 64 (scratchOff kg))
        (B+BitVec.ofNat 64 (outOff L kg n)) (B+BitVec.ofNat 64 (outOff L kg (n+1)))
        (B+BitVec.ofNat 64 (nttOff kg))) s t ∧
      PolyIsW (cw true) t.mem (B+BitVec.ofNat 64 (outOff L kg n))
        (sampled s.mem (B+BitVec.ofNat 64 (seedOff kg)) n (transformed L kg n)) ∧
      PolyIsW (cw true) t.mem (B+BitVec.ofNat 64 (outOff L kg (n+1)))
        (sampled s.mem (B+BitVec.ofNat 64 (seedOff kg)) (n+1) (transformed L kg (n+1))) := by
  obtain lim := layout_limits wf kg
  obtain fit0 := outOff_fits wf room kg (by omega_using [hn] : n<2*L.k)
  obtain fit1 := outOff_fits wf room kg hn
  obtain low0 := outOff_low wf room kg n
  obtain low1 := outOff_low wf room kg (n+1)
  change nttOff kg+1024≤outOff L kg n at low0
  change nttOff kg+1024≤outOff L kg (n+1) at low1
  obtain order := outOff_order wf room kg (Nat.lt_succ_self n)
  obtain size : L.scl<2^64 := by omega_using [lim]
  have iw {o l : Nat} (h : o+l≤L.scl) := inScratch hc h size
  have ir {o l : Nat} (h : o+l≤L.scl) : InRegions (s.rd++s.wr) (B+BitVec.ofNat 64 o) l :=
    by obtain ⟨r,hr,hc⟩ := iw h; exact ⟨r,List.mem_append_right _ hr,hc⟩
  have cw {o l : Nat} (h : o+l≤L.scl) := coversScratch hc h
  have sep {o l d k : Nat} (h : o+l≤d ∨ d+k≤o) (ho : o+l≤L.scl) (hd : d+k≤L.scl) :=
    Offset.disjoint B h (by omega_using [lim, ho] : o+l≤2^64) (by omega_using [lim, hd] : d+k≤2^64)
  have snorm (k : Nat) : B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 k =
      B+BitVec.ofNat 64 (scratchOff kg+k) := by rw [BitVec.add_assoc,← BitVec.ofNat_add]
  refine readonly_noisePair_ok (sha3 := sha3) kg (by have := wf.facts; omega_using [hn, this]) (by omega_using [lim, fit0]) (by omega_using [lim, fit1])
    (by rw [hB]; rfl) (by rw [hB]; rfl) (by rw [hB]) (by rw [hB]) (by rw [hB]; rfl)
    (fun j hj => ?_) (fun j hj => ?_) (fun j hj => ?_) ?_ ?_ ?_ ht0 ht1 hfar
  · rw [BitVec.add_assoc,← BitVec.ofNat_add]
    exact ir (by omega_using [lim, hj])
  · change InRegions s.wr (B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 (16*j)) 16
    rw [snorm]; exact iw (by omega_using [lim, hj])
  · rw [snorm]; exact iw (by omega_using [lim, hj])
  · change (Region.mk (B+BitVec.ofNat 64 (seedOff kg)) 32).Disjoint
      ⟨B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 1800,48⟩
    rw [snorm]; exact sep (Or.inl (by omega_using [lim])) (by omega_using [lim]) (by omega_using [lim])
  · exact sep (Or.inl lim.2.1) (by omega_using [lim]) (by omega_using [lim])
  · constructor
    · intro i hi
      change InRegions (s.rd++s.wr) (B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 (16*i)) 16
      rw [snorm]; exact ir (by omega_using [lim, hi])
    · intro i hi
      change InRegions s.wr ((B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 400)+BitVec.ofNat 64 (8*i)) 8
      rw [snorm,BitVec.add_assoc,← BitVec.ofNat_add]; exact iw (by omega_using [lim, hi])
    · intro i hi
      change InRegions s.wr ((B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 528)+BitVec.ofNat 64 (8*i)) 8
      rw [snorm,BitVec.add_assoc,← BitVec.ofNat_add]; exact iw (by omega_using [lim, hi])
    · change Covers [⟨B+BitVec.ofNat 64 (scratchOff kg),400⟩,
        ⟨B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 1536,136⟩] s.wr
      rw [snorm]; exact coversTwo (cw (by omega_using [lim])) (cw (by omega_using [lim]))
    · intro i hi; rw [snorm]; exact ir (by omega_using [lim, hi])
    · change Covers [⟨B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 400,128⟩,
        ⟨B+BitVec.ofNat 64 (outOff L kg n),1024⟩] (s.rd++s.wr)
      rw [snorm]; exact covers_rw' (coversTwo (cw (by omega_using [lim])) (cw fit0))
    · change Covers [⟨B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 528,128⟩,
        ⟨B+BitVec.ofNat 64 (outOff L kg (n+1)),1024⟩] (s.rd++s.wr)
      rw [snorm]; exact covers_rw' (coversTwo (cw (by omega_using [lim])) (cw fit1))
    · exact coversTwo (cw fit0) (cw lim.2.2.1)
    · exact coversTwo (cw fit1) (cw lim.2.2.1)
    · change (Region.mk (B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 400) 128).Disjoint _
      rw [snorm]; exact sep (Or.inl (by omega_using [lim, low0])) (by omega_using [lim]) fit0
    · change (Region.mk (B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 528) 128).Disjoint _
      rw [snorm]; exact sep (Or.inl (by omega_using [lim, low1])) (by omega_using [lim]) fit1
    · intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      change (Region.mk (B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 528) 128).Disjoint r
      rw [snorm]
      rcases hr with rfl | rfl
      · exact sep (Or.inl (by omega_using [lim, low0])) (by omega_using [lim]) fit0
      · exact sep (Or.inl (by omega_using [lim])) (by omega_using [lim]) lim.2.2.1
    · exact sep (Or.inl order) fit0 fit1
    · exact sep (Or.inr low0) fit0 lim.2.2.1
    · exact sep (Or.inr low1) fit1 lim.2.2.1
    · intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      change (Region.mk (B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 1800) 48).Disjoint r
      rw [snorm]
      rcases hr with rfl | rfl | rfl
      · exact sep (Or.inl (by omega_using [lim, low0])) (by omega_using [lim]) fit0
      · exact sep (Or.inl (by omega_using [lim, low1])) (by omega_using [lim]) fit1
      · exact sep (Or.inl (by omega_using [lim])) (by omega_using [lim]) lim.2.2.1

end VG.Proof.MlKem.AArch64.Noise

end

end


/-! # Key generation's noise from the first pairs' PRF outputs

`kgOut_ok`: `SamplePolyCBD₂` of buffer `N` into `ŝ[N]` or `ê[N - k]`,
transformed (`Kem16P.kgOut`). `noiseK_ok`: the six buffers the first two
pairs filled, then paired `PRF₂` for the rest of the noise, leave `ŝ` and `ê`
(`NK`) with `Â` as the pairs left it. -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.KeyGen
variable {sha3 : Bool}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem (cw)
open VG.Impl.MlKem.AArch64.Noise (noiseOff)

variable {P : KemLay}

theorem kgTarget_eq (P : KemLay) (N : Nat) :
    Impl.MlKem.AArch64.Kem16P.kgTarget P N = Noise.outOff P true N := rfl

/-- `ŝ[N]` for `N < k`, `ê[N - k]` after. -/
abbrev kgPoly (P : KemLay) (s₀ : State) (N : Nat) : Poly :=
  if N < P.k then KPke.kgS P.params (dB s₀) N else KPke.kgE P.params (dB s₀) (N - P.k)

theorem kgPoly_eq (s₀ : State) (N : Nat) :
    kgPoly P s₀ N = ntt (samplePolyCBD 2 (prf 2 (KPke.kgSigma P.params (dB s₀)) (BitVec.ofNat 8 N))) := by
  unfold kgPoly
  split
  · rfl
  · rename_i h
    simp only [KPke.kgE, VG.Proof.MlKem.cbd, KemLay.params]
    rw [Nat.add_sub_cancel' (by omega_arith)]

/-- The polynomials of the noise lie between `NS + 1024` and the end of `scratch`, apart from
`TP`'s buffers. -/
theorem out_far (hw : P.Wf) (hr : Noise.Room P) {N : Nat} (hN : N < 2 * P.k) :
    NS + 1024 ≤ Noise.outOff P true N ∧ Noise.outOff P true N + 1024 ≤ P.scl ∧
      (Noise.outOff P true N + 1024 ≤ TP P ∨ SV P + 48 ≤ Noise.outOff P true N) ∧
      SH P ≤ Noise.outOff P true N := by
  obtain lo := Noise.outOff_low hw hr true N
  change KG.NS + 1024 ≤ _ at lo
  refine ⟨lo, Noise.outOff_fits hw hr true hN, ?_⟩
  have tp : TP P = SH P + 1024 * P.k + 1024 := rfl
  have sv : SV P = TP P + 2048 := rfl
  unfold Noise.outOff
  split
  · rename_i h
    simp only [ite_true]
    have so : KG.sOff P N = SH P + 1024 * N := rfl
    rw [so]
    have := Nat.mul_le_mul_left 1024 (show N + 1 ≤ P.k by omega_arith)
    omega_arith
  · have := Noise.noise_past_kg hr (N - P.k)
    omega_arith

/-- **`kgOut`**: `SamplePolyCBD₂` of buffer `N` into its polynomial, transformed. -/
theorem kgOut_ok {s₀ s : State} (hp : Pre P s₀) (hr : Noise.Room P) (h : KB P s₀ s)
    (htr : Optimized.TransformTables s) {N : Nat} (hN6 : N < 6) (hN : N < 2 * P.k) :
    WP isa (Impl.MlKem.AArch64.Kem16P.kgOut P N) s fun t => KB P s₀ t ∧
      Frame [R (kA s₀) 3 (Noise.outOff P true N) 1024, R (kA s₀) 3 NS 1024] s.mem t.mem ∧
      t.gpr .x24 = s.gpr .x24 ∧ t.syms = s.syms ∧
      PolyIsW 16 t.mem (kA s₀ 3 + BitVec.ofNat 64 (Noise.outOff P true N))
        (ntt (samplePolyCBD 2 (bytesAt s.mem (kA s₀ 3 + BitVec.ofNat 64 (TP P + 168 * N)) 128))) := by
  have hw := hp.wf
  obtain ⟨tN, tS, tB, -⟩ := out_far hw hr hN
  generalize ht : Noise.outOff P true N = T at tN tS tB
  obtain h3 := kL_le hw 3
  have hsv := hp.sv
  have sv : SV P = TP P + 2048 := rfl
  have kl3 : kL P 3 = P.scl := rfl
  obtain cst : SV P + 48 ≤ P.scl ∧ KG.NS + 1024 ≤ TP P := ⟨by omega_using [hsv, kl3], by lom⟩
  obtain t64 : T < 65536 := by omega_using [tS, h3, kl3]
  obtain hbo : TP P + 168 * N < 65536 := by omega_using [hsv, sv, h3, hN6]
  obtain fT : T + 1024 ≤ kL P 3 := by omega_using [tS, kl3]
  obtain fN : KG.NS + 1024 ≤ kL P 3 := by omega_using [cst, hsv, sv]
  obtain fB : TP P + 168 * N + 128 ≤ kL P 3 := by omega_using [hsv, sv, hN6]
  obtain dBT : (R (kA s₀) 3 (TP P + 168 * N) 128).Disjoint (R (kA s₀) 3 T 1024) :=
    sdisjK hp fB fT (by rcases tB with h | h <;> omega_arith)
  obtain dTN : (R (kA s₀) 3 T 1024).Disjoint (R (kA s₀) 3 KG.NS 1024) := sdisjK hp fT fN (.inr tN)
  obtain cT : Covers [R (kA s₀) 3 T 1024] s.wr := cov_w hp h (b := 3) (by decide) fT
  obtain cN : Covers [R (kA s₀) 3 KG.NS 1024] s.wr := cov_w hp h (b := 3) (by decide) fN
  obtain cB : Covers [R (kA s₀) 3 (TP P + 168 * N) 128] (s.rd ++ s.wr) := cov_r hp h (b := 3) (by decide) fB
  obtain sT := kb_disj hp (b := 3) (o := T) (l := 1024) (by decide) fT
    (.inr (by rcases tB with h | h <;> omega_arith)) (by decide)
  obtain sN := kb_disj hp (b := 3) (o := KG.NS) (l := 1024) (by decide) fN (.inr (.inr (by omega_arith))) (by decide)
  unfold Impl.MlKem.AArch64.Kem16P.kgOut
  rw [kgTarget_eq, ht]
  simp only [seqs, Impl.MlKem.AArch64.Kem16P.bufOff]
  obtain sample : WP isa (.seq (.block (Impl.MlKem.AArch64.ptrTo .x0 .x28 (TP P + 168 * N) ++
      Impl.MlKem.AArch64.ptrTo .x1 .x28 T)) Impl.MlKem.AArch64.Noise.cbdCall) s fun v =>
      Kept [R (kA s₀) 3 T 1024] s v ∧
      PolyIsW (cw true) v.mem (kA s₀ 3 + BitVec.ofNat 64 T)
        (samplePolyCBD 2 (bytesAt s.mem (kA s₀ 3 + BitVec.ofNat 64 (TP P + 168 * N)) 128)) := by
    refine WP.seq (wp_ptrTo (by decide) hbo fun a ha ea => wp_ptrTo' (by decide) t64 fun u hu eu => ?_)
    obtain ou : Only [.x0, .x1] s u := (ha.trans hu).mono (by simp)
    obtain ku : Kept [R (kA s₀) 3 T 1024] s u := Kept.of_keep ou.keep ou.mem (by decide)
    exact cbdW_call (by rw [hu.get .x0 (by decide), ea, h.x28])
      (by rw [eu, ha.get .x28 (by decide), h.x28]) dBT
      (by rw [ou.rd, ou.wr]; exact Covers.cons (Covers.head cB) (Covers.right cT))
      (by rw [ou.wr]; exact cT)
      (fun v kv pv => ⟨ku.trans kv, by simpa only [ou.mem] using pv⟩)
  apply WP.assoc
  refine WP.seq (WP.mono_syms sample fun v ⟨kv, pv⟩ sv' => ?_)
  obtain kbv := h.call kv (fun r hr => by rw [List.mem_singleton.mp hr]; exact sT)
  obtain tv := htr.frame sv' kv.rd kv.wr kv.sp kv.frame cT
  obtain cv : Covers [polyRegion (kA s₀ 3 + BitVec.ofNat 64 T), polyRegion (kA s₀ 3 + BitVec.ofNat 64 KG.NS)] v.wr := by
    rw [kv.wr]; exact Covers.cons (Covers.head cT) (Covers.cons (Covers.head cN) Covers.nil)
  refine WP.mono_syms (Ntt16.W.nttAtWithW_ok t64 (by decide) (by rw [kbv.x28]) (by rw [kbv.x28])
    (dTN.sub_left (Region.sub_prefix (by decide : 512 ≤ 1024)) |>.sub_right
      (Region.sub_prefix (by decide : 512 ≤ 1024))) pv
    (Covers.cons (covers_prefix (by decide : 512 ≤ 1024) (Covers.head cv))
      (Covers.cons (covers_prefix (by decide : 512 ≤ 1024) (Covers.head (Covers.tail cv))) Covers.nil))
    (tv.fast.ready cv)) fun t ⟨kt, pt⟩ st => ?_
  obtain kt' : Kept [R (kA s₀) 3 T 1024, R (kA s₀) 3 KG.NS 1024] v t := kt.sub fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide : 512 ≤ 1024)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Region.sub_prefix (by decide : 512 ≤ 1024)⟩
  refine ⟨kbv.call kt' fun r hr => ?_, (kv.frame.mono (by simp)).trans kt'.frame,
    (kt'.cs .x24 (by decide) (by decide)).trans (kv.cs .x24 (by decide) (by decide)), st.trans sv', pt⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact sT
  · exact sN

/-- After `G`, the first two pairs and the first `j` polynomials of the noise. -/
structure NK (P : KemLay) (s₀ s : State) (j : Nat) (t : State) : Prop where
  c : CInvW P s₀ s.mem (s.gpr .x24) 4 t
  syms : t.syms = s.syms
  tt : Optimized.TransformTables t
  buf : ∀ N < 6, bytesAt t.mem (kA s₀ 3 + BitVec.ofNat 64 (TP P + 168 * N)) 128 =
    bytesAt s.mem (kA s₀ 3 + BitVec.ofNat 64 (TP P + 168 * N)) 128
  done : ∀ N < j, PolyIsW 16 t.mem (kA s₀ 3 + BitVec.ofNat 64 (Noise.outOff P true N)) (kgPoly P s₀ N)

/-- A region of `scratch` past `NS` and apart from `TP`'s buffers misses `σ`, `ρ`, `Â`, the
saved registers, the seed and the buffers. -/
theorem noise_regionK {s₀ : State} (hp : Pre P s₀) {o l : Nat} (hf : o + l ≤ kL P 3) (hNS : KG.NS ≤ o)
    (hm : o + l ≤ AH ∨ SH P ≤ o) (hb : o + l ≤ TP P ∨ SV P + 48 ≤ o) :
    ((R (kA s₀) 3 SB 32).Disjoint (R (kA s₀) 3 o l) ∧ (R (kA s₀) 3 SG 32).Disjoint (R (kA s₀) 3 o l) ∧
      (R (kA s₀) 3 AH (1024 * (P.k * P.k))).Disjoint (R (kA s₀) 3 o l)) ∧
    ((svR P s₀).Disjoint (R (kA s₀) 3 o l) ∧ (R (kA s₀) 0 0 64).Disjoint (R (kA s₀) 3 o l)) ∧
    ∀ N < 6, (R (kA s₀) 3 (TP P + 168 * N) 128).Disjoint (R (kA s₀) 3 o l) := by
  have hw := hp.wf
  have hsv := hp.sv
  have sv : SV P = TP P + 2048 := rfl
  have sh : SH P = AH + 1024 * (P.k * P.k) := rfl
  have tp : TP P = SH P + 1024 * P.k + 1024 := rfl
  obtain cst : SB + 32 ≤ SG ∧ SG + 32 ≤ KG.NS := by decide
  refine ⟨⟨sdisjK hp (by kl) hf (.inl (by omega_using [cst, hNS])),
    sdisjK hp (by kl) hf (.inl (by omega_using [cst, hNS])), sdisjK hp (by kl) hf (by omega_using [hm, sh])⟩,
    kb_disj hp (by decide) hf (.inr (by omega_using [hb, sv])) (by decide), fun N hN => ?_⟩
  exact sdisjK hp (by omega_using [hsv, sv, hN]) hf (by omega_using [hb, sv, hN, hm, tp, sh])

theorem NK.zero {s₀ s : State} (hk3 : 3 ≤ P.k) (H : FInv P s₀ 4 6 s) : NK P s₀ s 0 s :=
  ⟨⟨H.b.kb, H.b.rho, H.b.sig, rfl, by have := Nat.mul_le_mul hk3 hk3; omega_arith,
    fun e he => ⟨H.b.red e he, rfl⟩⟩, rfl, H.tables.transforms, fun _ _ => rfl,
    fun N hN => absurd hN (Nat.not_lt_zero N)⟩

/-- `kgOut` keeps `NK`. -/
theorem kgOut_step {s₀ s t : State} (hp : Pre P s₀) (hr : Noise.Room P) {j : Nat} (hj6 : j < 6)
    (hj : j < 2 * P.k) (hprf : PrfK P s₀ s.mem j) (H : NK P s₀ s j t) :
    WP isa (Impl.MlKem.AArch64.Kem16P.kgOut P j) t (NK P s₀ s (j + 1)) := by
  have hw := hp.wf
  refine WP.mono (kgOut_ok hp hr H.c.kb H.tt hj6 hj) fun u ⟨ku, fu, xu, su, pu⟩ => ?_
  obtain ⟨tN, tS, tB, tH⟩ := out_far hw hr hj
  have kl3 : kL P 3 = P.scl := rfl
  have sh : SH P = AH + 1024 * (P.k * P.k) := rfl
  have tp : TP P = SH P + 1024 * P.k + 1024 := rfl
  obtain fT : Noise.outOff P true j + 1024 ≤ kL P 3 := by omega_using [tS, kl3]
  obtain fN : KG.NS + 1024 ≤ kL P 3 := by kl
  obtain rT := noise_regionK hp fT (by omega_using [tN]) (.inr tH) tB
  obtain c0 : KG.NS + 1024 ≤ AH := by decide
  obtain rN := noise_regionK hp fN (Nat.le_refl _) (.inl (by decide)) (.inl (by omega_using [tp, sh, c0]))
  obtain far : ∀ r ∈ [R (kA s₀) 3 (Noise.outOff P true j) 1024, R (kA s₀) 3 KG.NS 1024],
      (((R (kA s₀) 3 SB 32).Disjoint r ∧ (R (kA s₀) 3 SG 32).Disjoint r ∧
        (R (kA s₀) 3 AH (1024 * (P.k * P.k))).Disjoint r) ∧
      ((svR P s₀).Disjoint r ∧ (R (kA s₀) 0 0 64).Disjoint r) ∧
      ∀ N < 6, (R (kA s₀) 3 (TP P + 168 * N) 128).Disjoint r) := by
    intro r hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact rT
    · exact rN
  have rdt : t.rd = s₀.rd := H.c.kb.rd
  have wrt : t.wr = s₀.wr := H.c.kb.wr
  refine ⟨H.c.frame ku xu fu fun r hr' => (far r hr').1, su.trans H.syms,
    H.tt.frame su (ku.rd.trans rdt.symm) (ku.wr.trans wrt.symm) (ku.sp.trans H.c.kb.sp.symm) fu
      (Covers.cons (Covers.head (cov_w hp H.c.kb (b := 3) (by decide) fT))
        (Covers.cons (Covers.head (cov_w hp H.c.kb (b := 3) (by decide) fN)) Covers.nil)),
    fun N hN => ?_, fun N hN => ?_⟩
  · rw [bytesAt_frame fu (fun r hr' => (far r hr').2.2 N hN) (by decide)]
    exact H.buf N hN
  · rcases (by omega_arith : N < j ∨ N = j) with hN | rfl
    · obtain ⟨tN', tS', -, -⟩ := out_far hw hr (N := N) (by omega_arith)
      obtain fT' : Noise.outOff P true N + 1024 ≤ kL P 3 := by omega_using [tS', kl3]
      obtain ord := Noise.outOff_order hw hr true hN
      refine polyIsW_frame_poly (w16 := true) fu (fun r hr' => ?_) (H.done N hN)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact sdisjK hp fT' fT (.inl ord)
      · exact sdisjK hp fT' fN (.inr tN')
    · rw [H.buf N hj6, hprf, ← kgPoly_eq] at pu
      exact pu

/-- The writes of a noise pair miss a region apart from its working space and outputs. -/
theorem writes_apartK {B : Addr} {n : Nat} {r : Region}
    (hs : r.Disjoint ⟨B + BitVec.ofNat 64 (Noise.scratchOff true), 2048⟩)
    (hn : r.Disjoint ⟨B + BitVec.ofNat 64 (Noise.nttOff true), 1024⟩)
    (ho : r.Disjoint ⟨B + BitVec.ofNat 64 (Noise.outOff P true n), 1024⟩)
    (ho' : r.Disjoint ⟨B + BitVec.ofNat 64 (Noise.outOff P true (n + 1)), 1024⟩) :
    ∀ q ∈ Noise.writes P true B n, r.Disjoint q := by
  intro q hq
  simp only [Noise.writes, Noise.pairWrites, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hs.sub_right (Offset.sub_base _ (d := 1800) (n := 48) (k := 2048) (by decide))
  · exact hs.sub_right (Region.sub_prefix (by decide : 400 ≤ 2048))
  · exact hs.sub_right (Offset.sub_base _ (d := 400) (n := 128) (k := 2048) (by decide))
  · exact hs.sub_right (Offset.sub_base _ (d := 528) (n := 128) (k := 2048) (by decide))
  · exact hs.sub_right (Offset.sub_base _ (d := 1536) (n := 136) (k := 2048) (by decide))
  · exact ho
  · exact ho'
  · exact hn

/-- A noise pair (`Noise.noisePairWith`) for outputs `n` and `n + 1` keeps `NK`. -/
theorem pairK_step {s₀ s t : State} (hp : Pre P s₀) (hr : Noise.Room P) {n : Nat} (hn : n + 1 < 2 * P.k)
    (H : NK P s₀ s n t) :
    WP isa (Impl.MlKem.AArch64.Noise.noisePairWith sha3 Ntt16.Readonly.nttAtWithW P true n) t (NK P s₀ s (n + 2)) := by
  have hw := hp.wf
  have kb := H.c.kb
  have kl3 : kL P 3 = P.scl := rfl
  obtain hc : Covers [⟨kA s₀ 3, P.scl⟩] t.wr := by
    simpa only [R, ptr_zero] using cov_w hp kb (b := 3) (o := 0) (l := P.scl) (by decide) (by kl)
  obtain lim := Noise.layout_limits hw true
  simp only [Noise.scratchOff, Noise.nttOff, Noise.seedOff, ite_true] at lim
  obtain ⟨oN, oS, oB, oH⟩ := out_far hw hr (N := n) (by omega_arith)
  obtain ⟨oN', oS', oB', oH'⟩ := out_far hw hr (N := n + 1) hn
  obtain fO : Noise.outOff P true n + 1024 ≤ kL P 3 := by omega_using [oS, kl3]
  obtain fO' : Noise.outOff P true (n + 1) + 1024 ≤ kL P 3 := by omega_using [oS', kl3]
  obtain fS : KG.SS + 2048 ≤ kL P 3 := by kl
  obtain fN : KG.NS + 1024 ≤ kL P 3 := by kl
  have cvs {o l : Nat} (h : o + l ≤ P.scl) := Noise.coversScratch hc h
  have rdy (m : Nat) (hm : m < 2 * P.k) :=
    H.tt.fast.ready (Noise.coversTwo (cvs (Noise.outOff_fits hw hr true hm)) (cvs (o := KG.NS) (l := 1024) (by omega_using [fN, kl3])))
  -- Every region apart from the pair's working space, `NS` and both outputs misses its writes.
  have away {r : Region} (h1 : r.Disjoint (R (kA s₀) 3 KG.SS 2048)) (h2 : r.Disjoint (R (kA s₀) 3 KG.NS 1024))
      (h3 : r.Disjoint (R (kA s₀) 3 (Noise.outOff P true n) 1024))
      (h4 : r.Disjoint (R (kA s₀) 3 (Noise.outOff P true (n + 1)) 1024)) :
      ∀ q ∈ Noise.writes P true (kA s₀ 3) n, r.Disjoint q :=
    writes_apartK (P := P) h1 h2 h3 h4
  have tfar (sym : String) (H' : List Nat) (tt : Optimized.TransformTable t sym H') :
      ∀ q ∈ Noise.writes P true (kA s₀ 3) n, (Region.mk (t.syms sym) 512).Disjoint q :=
    away (tt.apart (cov_w hp kb (b := 3) (by decide) fS)) (tt.apart (cov_w hp kb (b := 3) (by decide) fN))
      (tt.apart (cov_w hp kb (b := 3) (by decide) fO)) (tt.apart (cov_w hp kb (b := 3) (by decide) fO'))
  obtain ffar : ∀ q ∈ Noise.writes P true (kA s₀ 3) n, (NttR.fastRegion t).Disjoint q :=
    away (H.tt.fast.apart (cov_w hp kb (b := 3) (by decide) fS)) (H.tt.fast.apart (cov_w hp kb (b := 3) (by decide) fN))
      (H.tt.fast.apart (cov_w hp kb (b := 3) (by decide) fO)) (H.tt.fast.apart (cov_w hp kb (b := 3) (by decide) fO'))
  obtain ifar : ∀ q ∈ Noise.writes P true (kA s₀ 3) n, (NttR.fastInvRegion t).Disjoint q :=
    away (H.tt.inverse.apart (cov_w hp kb (b := 3) (by decide) fS)) (H.tt.inverse.apart (cov_w hp kb (b := 3) (by decide) fN))
      (H.tt.inverse.apart (cov_w hp kb (b := 3) (by decide) fO)) (H.tt.inverse.apart (cov_w hp kb (b := 3) (by decide) fO'))
  have sc (o l : Nat) (hf : o + l ≤ kL P 3) (hs : o + l ≤ KG.SS) :
      ∀ q ∈ Noise.writes P true (kA s₀ 3) n, (R (kA s₀) 3 o l).Disjoint q :=
    away (sdisjK hp hf fS (.inl hs)) (sdisjK hp hf fN (.inl (by omega_using [hs, lim])))
      (sdisjK hp hf fO (.inl (by omega_using [hs, lim, oN]))) (sdisjK hp hf fO' (.inl (by omega_using [hs, lim, oN'])))
  have hi (o l : Nat) (hf : o + l ≤ kL P 3) (h1 : KG.NS + 1024 ≤ o)
      (h2 : o + l ≤ Noise.outOff P true n ∨ Noise.outOff P true n + 1024 ≤ o)
      (h3 : o + l ≤ Noise.outOff P true (n + 1) ∨ Noise.outOff P true (n + 1) + 1024 ≤ o) :
      ∀ q ∈ Noise.writes P true (kA s₀ 3) n, (R (kA s₀) 3 o l).Disjoint q :=
    away (sdisjK hp hf fS (.inr (by omega_using [h1, lim]))) (sdisjK hp hf fN (.inr h1))
      (sdisjK hp hf fO h2) (sdisjK hp hf fO' h3)
  refine WP.mono_syms (Noise.readonly_noisePair_layout (sha3 := sha3) (B := kA s₀ 3) hw hr true hn kb.x28 hc
    (rdy n (by omega_arith)) (rdy (n + 1) hn) ffar) fun u ⟨ku, pu, qu⟩ sy => ?_
  have sv : SV P = TP P + 2048 := rfl
  have tp : TP P = SH P + 1024 * P.k + 1024 := rfl
  have sh : SH P = AH + 1024 * (P.k * P.k) := rfl
  have hsv := hp.sv
  obtain cst : KG.SB + 32 ≤ KG.SG ∧ KG.SG + 32 ≤ KG.SS ∧ KG.NS + 1024 ≤ AH := by decide
  obtain seed0 : ∀ q ∈ Noise.writes P true (kA s₀ 3) n, (R (kA s₀) 0 0 64).Disjoint q :=
    away (seed_disj hp (b := 3) (by decide) fS (by decide)) (seed_disj hp (b := 3) (by decide) fN (by decide))
      (seed_disj hp (b := 3) (by decide) fO (by decide)) (seed_disj hp (b := 3) (by decide) fO' (by decide))
  obtain kbu : KB P s₀ u := kb.call ku fun r hr' =>
    ⟨hi (SV P) 48 hsv (by omega_using [sv, tp, sh, cst]) (by omega_using [oB, oH, sv, tp])
        (by omega_using [oB', oH', sv, tp]) r hr', seed0 r hr'⟩
  have hsig : bytesAt t.mem (kA s₀ 3 + BitVec.ofNat 64 KG.SG) 32 = KPke.kgSigma P.params (dB s₀) := H.c.sig
  have samp {m : Nat} (hm : m < 2 * P.k) (h' : PolyIsW (cw true) u.mem (kA s₀ 3 + BitVec.ofNat 64 (Noise.outOff P true m))
      (Noise.sampled t.mem (kA s₀ 3 + BitVec.ofNat 64 (Noise.seedOff true)) m (Noise.transformed P true m))) :
      PolyIsW 16 u.mem (kA s₀ 3 + BitVec.ofNat 64 (Noise.outOff P true m)) (kgPoly P s₀ m) := by
    rw [kgPoly_eq]
    simpa only [Noise.sampled, Noise.seedOff, Noise.transformed, Bool.true_or, ite_true, hsig, cw] using h'
  refine ⟨H.c.frame kbu (ku.cs .x24 (by decide) (by decide)) ku.frame fun r hr' =>
      ⟨sc KG.SB 32 (by kl) (by omega_using [cst]) r hr', sc KG.SG 32 (by kl) (by omega_using [cst]) r hr',
        hi AH (1024 * (P.k * P.k)) (by kl) (by omega_using [cst]) (by omega_using [oH, sh]) (by omega_using [oH', sh]) r hr'⟩,
    ?_, ?_, fun N hN => ?_, fun N hN => ?_⟩
  · rw [sy]; exact H.syms
  · exact H.tt.frameFar sy ku.rd ku.wr ku.sp ku.frame fun r hr' =>
      ⟨tfar _ _ H.tt.forward r hr', ifar r hr', ffar r hr'⟩
  · rw [bytesAt_frame ku.frame (hi (TP P + 168 * N) 128 (by omega_using [hsv, sv, hN]) (by omega_using [tp, sh, cst])
      (by omega_using [oB, oH, sv, tp, hN]) (by omega_using [oB', oH', sv, tp, hN])) (by decide)]
    exact H.buf N hN
  · rcases (by omega_arith : N < n ∨ N = n ∨ N = n + 1) with hN' | rfl | rfl
    · exact polyIsW_frame_poly (w16 := true) ku.frame (Noise.writes_old_far hw hr true (kA s₀ 3) hn hN') (H.done N hN')
    · exact samp (by omega_arith) pu
    · exact samp hn qu

/-- **The noise** from the first pairs' buffers, then paired `PRF₂` for the rest. -/
theorem noiseK_ok {s₀ s : State} (hp : Pre P s₀) (hr : Noise.Room P) (hk3 : 3 ≤ P.k) (H : FInv P s₀ 4 6 s) :
    WPs (((List.range 6).map (Impl.MlKem.AArch64.Kem16P.kgOut P)) ++
      ((List.range (P.k - 3)).map fun i =>
        Impl.MlKem.AArch64.Noise.noisePairWith sha3 Ntt16.Readonly.nttAtWithW P true (6 + 2 * i))) s
      (NK P s₀ s (2 * P.k)) := by
  refine WPs.append (WPs.mono (WPs.range (I := NK P s₀ s) (fun j hj t ht =>
    kgOut_step hp hr hj (by omega_arith) (H.prf j hj) ht) (NK.zero hk3 H)) fun t ht => ?_)
  obtain r := WPs.range (f := fun i => Impl.MlKem.AArch64.Noise.noisePairWith sha3 Ntt16.Readonly.nttAtWithW P true (6 + 2 * i))
    (I := fun i => NK P s₀ s (6 + 2 * i)) (n := P.k - 3) (fun i hi u hu => by
      obtain st := pairK_step (sha3 := sha3) hp hr (n := 6 + 2 * i) (by omega_arith) hu
      rwa [show 6 + 2 * i + 2 = 6 + 2 * (i + 1) by omega_arith] at st) ht
  rwa [show 6 + 2 * (P.k - 3) = 2 * P.k by omega_arith] at r

/-- The noise as `KgRows` encodes `ŝ` from it. -/
theorem NK.encode {s₀ s t : State} (H : NK P s₀ s (2 * P.k) t) :
    EncodeInvW P s₀ s.mem t.mem (s.gpr .x24) 4 0 t := by
  refine ⟨H.c, fun j hj => ?_, fun j hj => ?_, fun _ hj => absurd hj (Nat.not_lt_zero _), Frame.refl _ _⟩
  · have d := H.done j (by omega_arith)
    simp only [kgPoly, ite_true, hj, Noise.outOff] at d
    exact d
  · have d := H.done (P.k + j) (by omega_arith)
    simp only [kgPoly, Noise.outOff, show ¬ P.k + j < P.k by omega_arith, ite_false, Nat.add_sub_cancel_left] at d
    exact d

end VG.Proof.MlKem.AArch64.KeyGen

end

end


/-! # After the first two pairs: the noise, `ŝ` into `dk`, the all-zero third state

`pre_ok`: after `G` and the first two pairs of the matrix (`FInv`),
`Kem16P.kgPre` establishes the interleaved invariant with the first four entries
of the matrix and nothing of the rows or the hash done. -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.KeyGen
variable {sha3 : Bool}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt)
open VG.Proof.MlKem.AArch64.Optimized
open VG.Proof.MlKem.AArch64.Hybrid (TStk)

variable {P : KemLay}

/-- The third state, `scratch`'s first 200 bytes, is apart from the other values. -/
theorem st_far {s₀ : State} (hp : Pre P s₀) {b o l : Nat} (hb : b < 4) (f : o + l ≤ kL P b)
    (hs : b ≠ 3 ∨ 200 ≤ o) : (R (kA s₀) b o l).Disjoint (R (kA s₀) 3 0 200) := by
  have hw := hp.wf
  exact hp.args.rdisj hb (by decide) f (by kl) (by rcases hs with hs | hs <;> omega_using [hs])

/-- The all-zero third state. -/
theorem zero_ok {s₀ s : State} (hp : Pre P s₀) (hr : Noise.Room P) {mB mN : Mem} {v : BitVec 64} {n : Nat}
    (h : EncodeInvW P s₀ mB mN v n P.k s) :
    WP isa (.block (zeroState .x28 KG.ST)) s fun t =>
      EncodeInvW P s₀ mB t.mem v n P.k t ∧ stateAt t.mem (kA s₀ 3) = Spec.Sha3.zero := by
  have hw := hp.wf
  have kb := h.c.kb
  refine WP.mono (zeroState_ok (hsetup hp kb (rate := 136) (by decide)) ⟨rfl, rfl, rfl, fun _ _ _ => rfl⟩)
    fun t ⟨kt, zt⟩ => ?_
  obtain e : STr .x28 KG.ST s = R (kA s₀) 3 0 200 := by simp only [STr, R, kb.x28, KG.ST]
  rw [e] at kt
  rw [kb.x28, show KG.ST = 0 from rfl, ptr_zero] at zt
  obtain kbt := kb.call kt fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ⟨(st_far hp (b := 3) (o := SV P) (l := 48) (by decide) hp.sv (.inr (by lom))),
      st_far hp (by decide) (by kl) (.inl (by decide))⟩
  obtain far : ∀ {b o l : Nat}, b < 4 → o + l ≤ kL P b → (b ≠ 3 ∨ 200 ≤ o) →
      ∀ r ∈ [R (kA s₀) 3 0 200], (R (kA s₀) b o l).Disjoint r := fun hb f hs r hr => by
    rw [List.mem_singleton.mp hr]; exact st_far hp hb f hs
  refine ⟨⟨h.c.frame kbt (kt.cs .x24 (by decide) (by decide)) kt.frame fun r hr => ⟨far (by decide) (by kl) (.inr (by decide)) r hr,
      far (by decide) (by kl) (.inr (by decide)) r hr, far (by decide) (by kl) (.inr (by lom)) r hr⟩,
    fun j hj => polyIsW_frame_poly (w16 := true) kt.frame (far (by decide) (by kl) (.inr (by lom))) (h.sp j hj),
    fun j hj => ?_, fun j hj => ?_, Frame.refl _ _⟩, zt⟩
  · exact polyIsW_frame_poly (w16 := true) kt.frame (far (by decide) (Noise.noise_fits hr hj)
      (.inr (by have := Noise.noise_past_kg hr j; lom))) (h.errors j hj)
  · rw [bytesAt_frame kt.frame (far (by decide) (by kl) (.inl (by decide))) (by decide)]
    exact h.dk j hj

/-- **The noise, `ŝ` into `dk` and the all-zero third state**, after `G` and the first two
pairs of the matrix (`Kem16P.kgPre`). -/
theorem pre_ok {s₀ s : State} (hp : Pre P s₀) (hr : Noise.Room P) (hk3 : 3 ≤ P.k) (H : FInv P s₀ 4 6 s)
    (depth : (Impl.MlKem.AArch64.Kem16P.kgPre sha3 P).aarch64Depth ≤ 1) :
    WP isa (Impl.MlKem.AArch64.Kem16P.kgPre sha3 P) s (IL P s₀ 4 0 0) := by
  have hw := hp.wf
  obtain body : WP isa (Impl.MlKem.AArch64.Kem16P.kgPre sha3 P) s fun v => ∃ mN,
      EncodeInvW P s₀ s.mem mN (s.gpr .x24) 4 P.k v ∧ stateAt v.mem (kA s₀ 3) = Spec.Sha3.zero := by
    unfold Impl.MlKem.AArch64.Kem16P.kgPre
    refine WPs.seqs (by simp) (WPs.append (WPs.append (WPs.mono (noiseK_ok (sha3 := sha3) hp hr hk3 H) fun t ht => ?_)))
    exact WPs.mono (encode_okW hp hr ht.encode) fun u eu =>
      WPs.single (WP.mono (zero_ok hp hr eu) fun v ⟨ev, zv⟩ => ⟨_, ev, zv⟩)
  refine WP.mono_syms (WP.tablesDepth body H.tables depth) fun v ⟨⟨mN, ev, zv⟩, tv⟩ hs => ?_
  have kbv := ev.c.kb
  refine ⟨⟨kbv, ev.c.rho, ev.c.sig, by rw [ev.c.x24, H.b.acc], fun e he => (ev.c.ahat e he).1,
      fun e he => ?_⟩,
    ev.sp, ev.errors, ev.dk, fun i hi => absurd hi (Nat.not_lt_zero _), by simp,
    ev.c.le, Nat.zero_le _, ?_, by simp, tv,
    H.tstk.of hs (by rw [kbv.sp, H.b.kb.sp])⟩
  · rcases H.b.res e he with h | h
    · exact .inl h
    · refine .inr (h.trans ?_)
      exact congrArg some ((ev.c.ahat e he).2).symm
  · rw [zv, Hybrid.hstate_zero]

end VG.Proof.MlKem.AArch64.KeyGen

end

end

/-! ### `MlKem.AArch64.KgH.Matrix`, which this module and modules that import it used -/

section

/-! # The matrix with the rows of `t̂` between its pairs

`matrixRows_ok`: `Kem16P.kgMatrixRows`, from the interleaved invariant with
the first two pairs done (`Kem16P.kgPairP`, which absorb nothing,
`rowsBy_two`) to the whole matrix, every row and the blocks `hashedBy (k² / 2)`
of `ek`. Pair `p` starts after `2 p` entries, `rowsBy p` rows and
`hashedBy p` blocks; it absorbs only blocks the rows before it encoded
(`hashed_le`), and the rows after it use only entries it or its predecessors
sampled. -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.KeyGen
variable {sha3 : Bool}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Impl.MlKem.AArch64.Kem16 (rowsBy hashedBy kgRows kgPair)

variable {P : KemLay}

theorem rowsBy_mono (P : KemLay) (p : Nat) : rowsBy P p ≤ rowsBy P (p + 1) := by
  simp only [rowsBy]
  have := Nat.div_le_div_right (c := P.k) (show 2 * p ≤ 2 * (p + 1) by omega_using [])
  omega_using [this]

/-- The first `rowsBy p` rows use only the first `2 p` entries. -/
theorem rowsBy_mul (P : KemLay) (p : Nat) : P.k * rowsBy P p ≤ 2 * p := by
  simp only [rowsBy]
  exact Nat.le_trans (Nat.mul_le_mul_left _ (Nat.min_le_right _ _)) (Nat.mul_div_le _ _)

theorem rowsBy_le (P : KemLay) (p : Nat) : rowsBy P p ≤ P.k := Nat.min_le_left _ _

/-- The blocks absorbed before pair `p` are among those the rows before it encoded. -/
theorem hashed_le (P : KemLay) : ∀ p, 136 * hashedBy P p ≤ 384 * rowsBy P p
  | 0 => by simp [hashedBy]
  | p + 1 => by
    have ih := hashed_le P p
    have hm := rowsBy_mono P p
    have hA : hashedBy P p ≤ 384 * rowsBy P p / 136 := (Nat.le_div_iff_mul_le (by decide)).2 (by omega_using [ih])
    have hB : 136 * (384 * rowsBy P p / 136) ≤ 384 * rowsBy P p := Nat.mul_div_le _ _
    simp only [hashedBy]
    have := Nat.min_le_right 3 (384 * rowsBy P p / 136 - hashedBy P p)
    omega_using [ih, hm]

theorem hashed_succ (P : KemLay) (p : Nat) :
    hashedBy P (p + 1) = hashedBy P p + (hashedBy P (p + 1) - hashedBy P p) := by
  simp only [hashedBy]; omega_using []

/-- `n` steps, each a list of programs, by an invariant `I i` before step `i`. -/
theorem wps_flatMap_range {f : Nat → List (Prog isa)} {I : Nat → State → Prop} :
    ∀ {n : Nat}, (∀ i < n, ∀ s, I i s → WPs (f i) s (I (i + 1))) →
      ∀ {s : State}, I 0 s → WPs ((List.range n).flatMap f) s (I n)
  | 0, _, _, h => h
  | n + 1, hf, _, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WPs.append (WPs.mono (wps_flatMap_range (fun i hi => hf i (by omega_using [hi])) h)
      fun s' h' => hf n (by omega_using []) s' h')

/-- Rows `a` to `a + d - 1` of `t̂`, once the matrix holds their entries. -/
theorem rows_ok {s₀ : State} (hp : Pre P s₀) (hr : Noise.Room P) {n h : Nat} :
    ∀ (d a : Nat), a + d ≤ P.k → P.k * (a + d) ≤ n → ∀ {s : State}, IL P s₀ n a h s →
      WPs (kgRows P a (a + d)) s (IL P s₀ n (a + d) h)
  | 0, a, _, _, _, H => by
    simp only [kgRows, Nat.add_zero, Nat.sub_self, List.range'_zero, List.map_nil, WPs]
    exact H
  | d + 1, a, hd, hn, s, H => by
    have e : kgRows P a (a + (d + 1)) = Kem16.kgRow P a :: kgRows P (a + 1) (a + 1 + d) := by
      simp only [kgRows, show a + (d + 1) - a = d + 1 by omega_using [], show a + 1 + d - (a + 1) = d by omega_using [],
        List.range'_succ, List.map_cons]
    rw [e]
    refine WPs.cons (WP.mono (row_step hp hr (by omega_using [hd])
      (Nat.le_trans (Nat.mul_le_mul_left _ (by omega_using [])) hn) H) fun t ht => ?_)
    have e2 : a + 1 + d = a + (d + 1) := by omega_using []
    have r := rows_ok hp hr d (a + 1) (by omega_using [hd]) (by rw [e2]; exact hn) ht
    exact WPs.mono r fun u hu => by rwa [e2] at hu

/-- Pair `p` of the matrix and the rows of `t̂` it completes. -/
theorem pairRows_ok {s₀ : State} (hp : Pre P s₀) (hk : Stk128K P s₀) (hr : Noise.Room P) {p : Nat}
    (hp' : p < P.k * P.k / 2) {s : State} (Hs : IL P s₀ (2 * p) (rowsBy P p) (hashedBy P p) s) :
    WPs (kgPair sha3 P p :: kgRows P (rowsBy P p) (rowsBy P (p + 1))) s
      (IL P s₀ (2 * (p + 1)) (rowsBy P (p + 1)) (hashedBy P (p + 1))) := by
  have hw := hp.wf
  have hf := hw.facts
  have hek : 384 * P.k < P.ekLen := by simp only [KemLay.ekLen]; omega_using []
  have hmono := rowsBy_mono P p
  have hle := rowsBy_le P (p + 1)
  have h2 := hashed_le P (p + 1)
  have hrk := rowsBy_le P p
  refine WPs.cons (WP.mono (pair_step (sha3 := sha3) hp hk hr (p := p) (r := rowsBy P p) (h := hashedBy P p)
    (m := hashedBy P (p + 1) - hashedBy P p) (by omega_using [hp'])
    (by simp only [hashedBy]; omega_using []) (fun k hk' => ?_) ?_ Hs) fun t ht => ?_)
  · have := Nat.mul_le_mul_left 384 hrk
    have h3 := hashed_le P (p + 1)
    simp only [hashedBy] at h3 hk' ⊢
    have : 136 * (384 * rowsBy P p / 136) ≤ 384 * rowsBy P p := Nat.mul_div_le _ _
    omega_using [hek, hmono, hle, hk']
  · rw [← hashed_succ]
    have hA : hashedBy P p ≤ 384 * rowsBy P p / 136 :=
      (Nat.le_div_iff_mul_le (by decide)).2 (by have := hashed_le P p; omega_using [this])
    have hB : 136 * (384 * rowsBy P p / 136) ≤ 384 * rowsBy P p := Nat.mul_div_le _ _
    simp only [hashedBy]
    have := Nat.min_le_right 3 (384 * rowsBy P p / 136 - hashedBy P p)
    omega_using [hA]
  · rw [← hashed_succ] at ht
    have r := rows_ok hp hr (n := 2 * p + 2) (rowsBy P (p + 1) - rowsBy P p) (rowsBy P p) (by omega_using [hmono, hle])
      (by rw [Nat.add_sub_cancel' hmono]; exact Nat.le_trans (rowsBy_mul P (p + 1)) (by omega_using [])) ht
    rw [Nat.add_sub_cancel' hmono] at r
    exact r

/-- No row is complete, and no block of `ek` absorbed, before the third pair. -/
theorem rowsBy_two (hk3 : 3 ≤ P.k) : rowsBy P 1 = 0 ∧ hashedBy P 2 = 0 := by
  have r1 : rowsBy P 1 = 0 := by
    simp only [rowsBy, Nat.mul_one, Nat.div_eq_of_lt (show 2 < P.k by omega_using [hk3]), Nat.min_zero]
  refine ⟨r1, ?_⟩
  simp only [hashedBy, r1, show rowsBy P 0 = 0 by simp [rowsBy]]
  rfl

/-- **The matrix after its first two pairs, and the rows of `t̂`.** -/
theorem matrixRows_ok {s₀ s : State} (hp : Pre P s₀) (hk : Stk128K P s₀) (hr : Noise.Room P)
    (hk3 : 3 ≤ P.k) (H : IL P s₀ 4 0 0 s) :
    WPs (Impl.MlKem.AArch64.Kem16P.kgMatrixRows sha3 P) s
      (IL P s₀ (P.k * P.k) P.k (hashedBy P (P.k * P.k / 2))) := by
  have hw := hp.wf
  have hf := hw.facts
  have hkk := Nat.mul_le_mul hk3 hk3
  have h2 := (rowsBy_two (P := P) hk3).2
  have first := rows_ok hp hr (n := 4) (h := 0) (rowsBy P 2) 0 (by have := rowsBy_le P 2; omega_using [this])
    (by rw [Nat.zero_add]; exact rowsBy_mul P 2) H
  rw [Nat.zero_add] at first
  unfold Impl.MlKem.AArch64.Kem16P.kgMatrixRows Impl.MlKem.AArch64.Kem16P.pairs
    Impl.MlKem.AArch64.Kem16P.single
  refine WPs.append (WPs.append (WPs.mono first fun t ht => WPs.mono (wps_flatMap_range (n := P.k * P.k / 2 - 2)
    (I := fun q s => IL P s₀ (2 * (q + 2)) (rowsBy P (q + 2)) (hashedBy P (q + 2)) s)
    (f := fun q => kgPair sha3 P (q + 2) :: kgRows P (rowsBy P (q + 2)) (rowsBy P (q + 3)))
    (fun q hq s Hs => pairRows_ok hp hk hr (p := q + 2) (by omega_using [hq]) Hs)
    (show IL P s₀ 4 (rowsBy P 2) (hashedBy P 2) t by rw [h2]; exact ht)) fun u hu => ?_))
  have e2 : P.k * P.k / 2 - 2 + 2 = P.k * P.k / 2 := by omega_using [hkk]
  rw [e2] at hu
  have hle := rowsBy_le P (P.k * P.k / 2)
  by_cases ho : P.k * P.k % 2 = 1
  · rw [show decide (P.k * P.k % 2 = 1) = true from decide_eq_true ho, ite_eq_left rfl]
    have e : 2 * (P.k * P.k / 2) = P.k * P.k - 1 := by omega_using [ho]
    rw [e] at hu
    refine WPs.cons (WP.mono (last_step (sha3 := sha3) hp hr ho hu) fun v hv => ?_)
    have r := rows_ok hp hr (n := P.k * P.k) (P.k - rowsBy P (P.k * P.k / 2)) (rowsBy P (P.k * P.k / 2))
      (by omega_using [hle]) (by rw [Nat.add_sub_cancel' hle]) hv
    rwa [Nat.add_sub_cancel' hle] at r
  · rw [show decide (P.k * P.k % 2 = 1) = false from decide_eq_false ho, ite_eq_right Bool.false_ne_true]
    have e : 2 * (P.k * P.k / 2) = P.k * P.k := by omega_using [ho]
    have er : rowsBy P (P.k * P.k / 2) = P.k := by
      simp only [rowsBy, e, Nat.mul_div_cancel_left _ (show 0 < P.k by omega_using [hk3]), Nat.min_self]
    rw [e, er] at hu
    exact hu

end VG.Proof.MlKem.AArch64.KeyGen

end

end

/-! ### `MlKem.AArch64.KgH.Tail`, which only this module used -/

section

/-! # The tail of the key generation hashing `ek` during the matrix

`tail_ok`: once every row of `t̂` is encoded and the third state has absorbed
the first `h` blocks of `ek`, `Kem16.kgTail`: `ρ` into both keys, each further
block of `ek` absorbed and permuted by `v`'s single-state permutation
(`block_step`), `H(ek)`, the first 32 bytes of the third state, and `z` into
`dk`, and the epilogue. -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.KeyGen
variable {sha3 : Bool}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt keccakF)
open VG.Proof.MlKem.AArch64.Optimized
open VG.Proof.Sha3.AArch64.Hybrid.X3 (stR)
open VG.Proof.MlKem.AArch64.Hybrid (hstate)

variable {P : KemLay}

/-- `ek`, encoded. -/
abbrev ekK (P : KemLay) (s₀ : State) (mB : Mem) : List Byte := KPke.ekPKE P.params (aMW P s₀ mB) (dB s₀)

/-- After `ρ` and `b` blocks of `ek` in the third state. -/
structure TT (P : KemLay) (s₀ : State) (mB : Mem) (v : BitVec 64) (b : Nat) (s : State) : Prop where
  kb : KB P s₀ s
  e : EndInvW P s₀ mB v (P.k * P.k) s
  hash : stateAt s.mem (kA s₀ 3) = hstate (ekK P s₀ mB) b (Hybrid.dB (Kem16.kgSrc P))

theorem TT.ek {s₀ s : State} {mB : Mem} {v : BitVec 64} {b : Nat} (h : TT P s₀ mB v b s) :
    bytesAt s.mem (kA s₀ 1) P.ekLen = ekK P s₀ mB :=
  ek_at (T := tVW P s₀ mB) (ρ := rhoK P s₀) (fun i hi => (h.e.tl.ek i hi).1) h.e.rek

/-- The third state and the permutation's working space. -/
theorem st_wk_far {s₀ : State} (hp : Pre P s₀) {o l : Nat} (f : o + l ≤ 840) :
    Far P s₀ (R (kA s₀) 3 o l) := by
  have hw := hp.wf
  exact far_R hp (by decide) (by simp only [kL]; lom) (fun _ => .inl f) (by decide) (fun h => absurd h (by decide))

/-- **One more block of `ek`**, absorbed and permuted. -/
theorem block_step (v : Proof.Sha3.AArch64.Permutation) {s₀ s : State} (hp : Pre P s₀)
    {mB : Mem} {vv : BitVec 64} {b : Nat} (hb : 136 * b < P.ekLen) (H : TT P s₀ mB vv b s) :
    WP isa (.seq (.block (Hybrid.absorbBlock (Kem16.kgSrc P) b)) (Kem16.kgPerm v.callee)) s
      (TT P s₀ mB vv (b + 1)) := by
  have hw := hp.wf
  obtain hsv : 200 ≤ SV P := by lom
  have kb := H.kb
  obtain ek : (⟨kA s₀ 1, (Kem16.kgSrc P).len⟩ : Region) = R (kA s₀) 1 0 (kL P 1) := ekR s₀
  obtain fS : 0 + 200 ≤ kL P 3 := by
    show 0 + 200 ≤ P.scl; omega_using [hw.facts.2.2.2.2.2.2.2.2.1]
  obtain fE : 0 + kL P 1 ≤ kL P 1 := by omega_using []
  refine WP.seq (WP.mono (Hybrid.absorbBlock_ok (Kem16.kgSrc P) (srcOkK hw)
    (by show s.gpr .x26 + BitVec.ofNat 64 0 = kA s₀ 1; rw [kb.x26, ptr_zero]) kb.x28 hb H.ek H.hash
    (by rw [ek]; exact cov_r hp kb (b := 1) (o := 0) (l := kL P 1) (by decide) fE)
    (by rw [stR_scratch]; exact cov_w hp kb (b := 3) (o := 0) (l := 200) (by decide) fS)
    (by rw [stR_scratch, ek]
        exact hp.args.rdisj (b₁ := 3) (o₁ := 0) (l₁ := 200) (b₂ := 1) (o₂ := 0) (l₂ := kL P 1)
          (by decide) (by decide) fS fE (.inl (by decide)))) fun t ⟨kt, ft, st⟩ => ?_)
  rw [stR_scratch] at ft
  obtain kbt := kb.frame kt ft (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ⟨(st_far hp (b := 3) (o := SV P) (l := 48) (by decide) hp.sv (.inr hsv)),
      (st_far hp (by decide) (by kl) (.inl (by decide)))⟩
  obtain et := H.e.frame hp kbt (kt.get .x24) ft fun r hr => by
    rw [List.mem_singleton.mp hr]; exact st_wk_far hp (by decide)
  refine WP.mono (FixedHash.permute_ok v (hsetup hp kbt (rate := 136) (by decide))
    ⟨rfl, rfl, rfl, fun _ _ _ => rfl⟩) fun w ⟨kw, sw⟩ => ?_
  obtain e3 : STr .x28 KG.ST t = R (kA s₀) 3 0 200 := by simp only [STr, R, kbt.x28, KG.ST]
  obtain e4 : (⟨t.gpr .x28 + BitVec.ofNat 64 KG.WK, 512⟩ : Region) = R (kA s₀) 3 KG.WK 512 := by
    simp only [R, kbt.x28]
  rw [e3, e4] at kw
  obtain far : ∀ r ∈ [R (kA s₀) 3 0 200, R (kA s₀) 3 KG.WK 512], Far P s₀ r := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact st_wk_far hp (by decide)
    · exact st_wk_far hp (by decide)
  obtain kbw := kbt.call kw fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨(st_far hp (b := 3) (o := SV P) (l := 48) (by decide) hp.sv (.inr hsv)),
        (st_far hp (by decide) (by kl) (.inl (by decide)))⟩
    · exact ⟨hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (.inr (.inr (by lom))),
        hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (.inl (by decide))⟩
  refine ⟨kbw, et.frame hp kbw (kw.cs .x24 (by decide) (by decide)) kw.frame far, ?_⟩
  rw [kbt.x28, show KG.ST = 0 from rfl, ptr_zero] at sw
  rw [sw, ← st]

/-- Blocks `b` to `b + d - 1` of `ek`. -/
theorem blocks_ok (v : Proof.Sha3.AArch64.Permutation) {s₀ : State} (hp : Pre P s₀) {mB : Mem}
    {vv : BitVec 64} : ∀ (d b : Nat), b + d ≤ Hybrid.blocks (Kem16.kgSrc P) → ∀ {s : State},
      TT P s₀ mB vv b s →
      WPs ((List.range' b d).map fun b => .seq (.block (Hybrid.absorbBlock (Kem16.kgSrc P) b))
        (Kem16.kgPerm v.callee)) s (TT P s₀ mB vv (b + d))
  | 0, b, _, s, H => by simpa only [List.range'_zero, List.map_nil, WPs, Nat.add_zero] using H
  | d + 1, b, hd, s, H => by
    have hw := hp.wf
    have hf := hw.facts
    obtain hb : 136 * b < P.ekLen := by
      simp only [Hybrid.blocks, Kem16.kgSrc, KemLay.ekLen] at hd ⊢
      have := Nat.lt_succ_iff.mp (show b < (384 * P.k + 32) / 136 + 1 by omega_using [hd])
      have := (Nat.le_div_iff_mul_le (by decide)).1 this
      omega_using [hd, hf]
    rw [List.range'_succ, List.map_cons]
    refine WPs.cons (WP.mono (block_step v hp hb H) fun t ht => ?_)
    obtain r := blocks_ok v hp d (b + 1) (by omega_using [hd]) ht
    rwa [show b + 1 + d = b + (d + 1) by omega_using []] at r

/-- `H(ek)` and `z` into `dk`, and the epilogue. -/
theorem final_ok {s₀ s : State} (hp : Pre P s₀) {mB : Mem} {vv : BitVec 64}
    (HT : TT P s₀ mB vv (Hybrid.blocks (Kem16.kgSrc P)) s) :
    WP isa (.block (copy32 .x28 KG.ST .x27 (768 * P.k + 32) ++ copy32 .x25 32 .x27 (768 * P.k + 64) ++
      [mov .x0 .x24, .ldr .x .x30 .x28 (KG.SV P + 40), .ldr .x .x24 .x28 (KG.SV P),
        .ldr .x .x25 .x28 (KG.SV P + 8), .ldr .x .x26 .x28 (KG.SV P + 16),
        .ldr .x .x27 .x28 (KG.SV P + 24), .ldr .x .x28 .x28 (KG.SV P + 32)])) s (DoneW P s₀ mB vv) := by
  have hw := hp.wf
  have kb := HT.kb
  obtain hfull : stateAt s.mem (kA s₀ 3) = Spec.Sha3.absorb 136 (Spec.Sha3.pad 136 (BitVec.ofNat 8 6) (ekK P s₀ mB)) := by
    rw [HT.hash]
    apply Hybrid.hstate_done
    rw [← HT.ek, VG.Proof.MlKem.bytesAt_length]
    simp only [Hybrid.blocks, Kem16.kgSrc]
    omega_using []
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (copy_ok (S := kA s₀ 3) (D := kA s₀ 2) (so := KG.ST) (dO := 768 * P.k + 32) (by decide) (by decide)
    (by decide) (by lom) (hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (by kl))
    kb.x28 kb.x27 (cov_r hp kb (b := 3) (by decide) (by kl))
    (cov_w hp kb (b := 2) (by decide) (by kl))) fun s₂ ⟨k₂, f₂, b₂⟩ => ?_
  obtain kb₂ := kb.frame k₂ f₂ (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact kb_disj hp (b := 2) (o := 768 * P.k + 32) (l := 32) (by decide) (by kl) (.inl (by decide)) (by decide)
  obtain h₂ := HT.e.frame hp kb₂ (k₂.get .x24) f₂ fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact far_R hp (by decide) (by kl) (by kl) (by decide) (by kl)
  obtain hh₂ : bytesAt s₂.mem (kA s₀ 2 + BitVec.ofNat 64 (768 * P.k + 32)) 32 = H (ekK P s₀ mB) := by
    rw [b₂, show KG.ST = 0 from rfl, ptr_zero, H_eq, Hybrid.bytesAt_squeeze, hfull]; rfl
  refine WP.mono (copy_ok (S := kA s₀ 0) (D := kA s₀ 2) (so := 32) (dO := 768 * P.k + 64) (by decide) (by decide)
    (by decide) (by lom) (hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (by kl))
    kb₂.x25 kb₂.x27 (cov_r hp kb₂ (b := 0) (by decide) (by kl))
    (cov_w hp kb₂ (b := 2) (by decide) (by kl))) fun s₃ ⟨k₃, f₃, b₃⟩ => ?_
  obtain kb₃ := kb₂.frame k₃ f₃ (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact kb_disj hp (b := 2) (o := 768 * P.k + 64) (l := 32) (by decide) (by kl) (.inl (by decide)) (by decide)
  obtain far₃ : ∀ r ∈ [R (kA s₀) 2 (768 * P.k + 64) 32], Far P s₀ r := fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact far_R hp (by decide) (by kl) (by kl) (by decide) (by kl)
  obtain h₃ := h₂.frame hp kb₃ (k₃.get .x24) f₃ far₃
  obtain hh₃ : bytesAt s₃.mem (kA s₀ 2 + BitVec.ofNat 64 (768 * P.k + 32)) 32 = H (ekK P s₀ mB) := by
    rw [bytesAt_frame f₃ (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (by kl)) (by decide)]
    exact hh₂
  obtain z₃ : bytesAt s₃.mem (kA s₀ 2 + BitVec.ofNat 64 (768 * P.k + 64)) 32 = zB s₀ := by rw [b₃]; exact kb₂.z
  obtain ek₃ : bytesAt s₃.mem (kA s₀ 1) P.ekLen = ekK P s₀ mB :=
    ek_at (T := tVW P s₀ mB) (ρ := rhoK P s₀) (fun i hi => (h₃.tl.ek i hi).1) h₃.rek
  obtain dk₃ : bytesAt s₃.mem (kA s₀ 2) P.dkLen = KPke.dkPKE P.params (dB s₀) ++
      ekK P s₀ mB ++ H (ekK P s₀ mB) ++ zB s₀ :=
    dk_at (cat_at (T := KPke.kgS P.params (dB s₀)) fun j hj => h₃.tl.dk j hj)
      (ek_at (T := tVW P s₀ mB) (ρ := rhoK P s₀) (fun i hi => by rw [ptr_add]; exact (h₃.tl.ek i hi).2)
        (by rw [ptr_add, show 384 * P.k + 384 * P.k = 768 * P.k by omega_using []]; exact h₃.rdk)) hh₃ z₃
  refine WP.mono (restore_ok hp kb₃) fun s' ⟨abi, x0, hm⟩ => ⟨abi, by rw [x0, h₃.tl.c.x24], ?_, ?_⟩
  · rw [hm]; exact ek₃
  · rw [hm]; exact dk₃

/-- **The tail**, once every row is encoded and the matrix has absorbed its blocks of `ek`. -/
theorem tail_ok (v : Proof.Sha3.AArch64.Permutation) {s₀ s : State} (hp : Pre P s₀)
    (H : IL P s₀ (P.k * P.k) P.k (Kem16.hashedBy P (P.k * P.k / 2)) s) :
    WP isa (Kem16.kgTail v.callee P) s (DoneW P s₀ s.mem (s.gpr .x24)) := by
  have hw := hp.wf
  have hf := hw.facts
  have kb := H.b.kb
  have hh := H.hr
  obtain hle : 136 * Kem16.hashedBy P (P.k * P.k / 2) ≤ P.ekLen := by
    simp only [KemLay.ekLen]; omega_using [hh]
  obtain tl : TLW P s₀ s.mem (s.gpr .x24) (P.k * P.k) P.k s :=
    ⟨⟨kb, H.b.rho, H.b.sig, rfl, Nat.le_refl _, fun e he => ⟨H.b.red e he, rfl⟩⟩, H.sp, H.dk, H.rows⟩
  unfold Kem16.kgTail
  refine WPs.seqs (by simp) (WPs.append (WPs.append ?_))
  refine WPs.cons (WP.mono (rho_okW hp tl) fun s₁ ⟨kb₁, e₁, f₁⟩ => ?_)
  simp only [WPs]
  obtain ek₁ : bytesAt s₁.mem (kA s₀ 1) P.ekLen = ekK P s₀ s.mem :=
    ek_at (T := tVW P s₀ s.mem) (ρ := rhoK P s₀) (fun i hi => (e₁.tl.ek i hi).1) e₁.rek
  obtain hs₁ : stateAt s₁.mem (kA s₀ 3) = hstate (ekK P s₀ s.mem) (Kem16.hashedBy P (P.k * P.k / 2))
      (Hybrid.dB (Kem16.kgSrc P)) := by
    rw [VG.Proof.Sha3.AArch64.Hybrid.X3.stateAt_frame f₁ (fun r hr => by
      rw [stR_scratch]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (st_far hp (by decide) (by kl) (.inl (by decide))).symm
      · exact (st_far hp (by decide) (by kl) (.inl (by decide))).symm), H.hash, ← ek₁]
    refine hstate_prefix hle ?_
    obtain e1 : kA s₀ 1 = kA s₀ 1 + BitVec.ofNat 64 0 := (ptr_zero _).symm
    rw [e1, bytesAt_frame f₁ (fun q hq => ?_) (by have := kL_le hw 1; simp only [kL] at this; omega_using [hf, hh])]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact hp.args.rdisj (b₁ := 1) (o₁ := 0) (l₁ := 136 * Kem16.hashedBy P (P.k * P.k / 2)) (by decide) (by decide)
        (by simp only [kL]; omega_using [hle]) (by kl) (.inr (.inl (by omega_using [hh])))
    · exact hp.args.rdisj (b₁ := 1) (o₁ := 0) (by decide) (by decide) (by simp only [kL]; omega_using [hle]) (by kl)
        (.inl (by decide))
  obtain hb : Kem16.hashedBy P (P.k * P.k / 2) ≤ Hybrid.blocks (Kem16.kgSrc P) := by
    simp only [Hybrid.blocks, Kem16.kgSrc]
    have := (Nat.le_div_iff_mul_le (k := 136) (by decide)).2
      (show Kem16.hashedBy P (P.k * P.k / 2) * 136 ≤ P.ekLen by omega_using [hle])
    omega_using [hle]
  obtain r := blocks_ok v hp (Hybrid.blocks (Kem16.kgSrc P) - Kem16.hashedBy P (P.k * P.k / 2))
    (Kem16.hashedBy P (P.k * P.k / 2)) (by omega_using [hb]) (s := s₁) ⟨kb₁, e₁, hs₁⟩
  rw [Nat.add_sub_cancel' hb] at r
  exact WPs.mono r fun u hu => WPs.single (final_ok hp hu)

end VG.Proof.MlKem.AArch64.KeyGen

end

end


/-! # The key generation hashing `ek` during the matrix is correct

`using_correctP`: `G` (`a_using_ok`), the first two pairs of the matrix
computing the first PRF outputs (`first_step`), the noise, `ŝ` and the
all-zero third state (`pre_ok`), the rest of the matrix with the rows of `t̂`
between its pairs (`matrixRows_ok`), and the tail (`tail_ok`). -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.KeyGen
variable {sha3 : Bool}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Optimized
open VG.Proof.MlKem.AArch64.Hybrid (TStk)

variable {P : KemLay}

theorem matrixRows_ne_nil (P : KemLay) (hk3 : 3 ≤ P.k) : Impl.MlKem.AArch64.Kem16P.kgMatrixRows sha3 P ≠ [] := by
  intro h
  unfold Impl.MlKem.AArch64.Kem16P.kgMatrixRows Impl.MlKem.AArch64.Kem16P.pairs at h
  obtain h2 := (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp h).1).2
  obtain hp : 0 < P.k * P.k / 2 - 2 := by
    have := Nat.mul_le_mul hk3 hk3
    omega_using [this]
  exact List.cons_ne_nil _ _ (List.flatMap_eq_nil_iff.mp h2 0 (List.mem_range.mpr hp))

/-- **The key generation computing the first PRF outputs in the matrix is correct.** -/
theorem using_correctP (v : Proof.Sha3.AArch64.Permutation) (hash : FixedHash.HashFn)
    (hG : FixedHash.HashCorrect hash .x28 ST WK 72 6
      [⟨.x25,0,32⟩,⟨.x28,BK,1⟩] [⟨.x28,SB,32⟩,⟨.x28,SG,32⟩])
    {s₀ : State} (hp : Pre P s₀) (hk : Stk128K P s₀) (hr : Noise.Room P) (hk3 : 3 ≤ P.k) (tables : Tables s₀)
    (ts : TStk s₀) (depthA : (FixedHashCallers.kgAUsing hash P).aarch64Depth ≤ 1)
    (depthP : (Impl.MlKem.AArch64.Kem16P.kgPre sha3 P).aarch64Depth ≤ 1) :
    WP isa (Impl.MlKem.AArch64.Kem16P.keyGen sha3 hash v.callee P) s₀ fun t =>
      abiPreserved s₀ t ∧ (keyGenAArch64 P).post s₀ t := by
  unfold Impl.MlKem.AArch64.Kem16P.keyGen
  refine WPs.seqs (by simp) ?_
  refine WPs.cons (WP.mono_syms (WP.tablesDepth (a_using_ok hash hG hp) tables depthA) fun sA ⟨hA, ta⟩ hs => ?_)
  refine WPs.cons (WP.mono (first_step (sha3 := sha3) hp hk (p := 0) (by decide) hk3
    (FInv.zero hA ta (ts.of hs hA.kb.sp))) fun s₁ h₁ => ?_)
  refine WPs.cons (WP.mono (first_step (sha3 := sha3) hp hk (p := 1) (by decide) hk3 h₁) fun s₂ h₂ => ?_)
  refine WPs.cons (WP.mono (pre_ok (sha3 := sha3) hp hr hk3 h₂ depthP) fun s₃ h₃ => ?_)
  refine WPs.cons (WP.mono (WPs.seqs (matrixRows_ne_nil (sha3 := sha3) P hk3) (matrixRows_ok (sha3 := sha3) hp hk hr hk3 h₃))
    fun s₄ h₄ => ?_)
  exact WPs.single (WP.mono (tail_ok v hp h₄) fun t ht => ⟨ht.abi, post_ofW h₄.b ht⟩)

end VG.Proof.MlKem.AArch64.KeyGen
