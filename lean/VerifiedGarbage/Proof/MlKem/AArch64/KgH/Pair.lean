module

public import VerifiedGarbage.Proof.MlKem.AArch64.KgH.Row
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Pair
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenMatrixTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenMatrixPair
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenMatrixPost
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenMatrixLast
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TableApart
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Offset

/-! # The pairs of the matrix between the rows of `t̂`

`pair_step`: a pair of the matrix (`Hybrid.pairM` in key generation's
workspace) whose first `m` main squeezes absorb blocks `h`, …, `h + m - 1` of
`ek`, all of them already encoded (`136 (h + m) ≤ 384 r`), keeps the interleaved
invariant `IL`. `last_step`: the final entry of an odd matrix. -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt)
open VG.Proof.MlKem.AArch64.Optimized
open VG.Proof.Sha3.AArch64.Hybrid.X3 (stR)
open VG.Proof.MlKem.AArch64.Hybrid (TStk frame)

variable {P : KemLay}

/-- `ek` is a message the third state can absorb. -/
theorem srcOkK (hw : P.Wf) : Hybrid.SrcOk (Impl.MlKem.AArch64.Kem16.kgSrc P) := by
  have := hw.facts
  refine ⟨.inr (.inl rfl), ?_, rfl, ?_⟩ <;>
    simp only [Impl.MlKem.AArch64.Kem16.kgSrc, KemLay.ekLen] <;> omega

/-- What a hashing pair of key generation writes. -/
abbrev pairWritesH (s₀ : State) (e : Nat) : List Region :=
  Hybrid.pairWrites3 (kA s₀ 3+BitVec.ofNat 64 SS) (kA s₀ 3+BitVec.ofNat 64 (AH+1024*e))
    (kA s₀ 3+BitVec.ofNat 64 (AH+1024*(e+1))) (kA s₀ 3) s₀.sp

theorem pairH_far {s₀ : State} (hp : Pre P s₀) (hk : Stk128K P s₀) {e : Nat} (he : e+1<P.k*P.k)
    {b o l : Nat} (hb : b<4) (hf : o+l≤kL P b)
    (hs : b≠3 ∨ ((o+l≤SS ∨ SS+2048≤o) ∧ (o+l≤AH+1024*e ∨ AH+1024*(e+2)≤o) ∧ 200 ≤ o)) :
    ∀ r ∈ pairWritesH s₀ e, (R (kA s₀) b o l).Disjoint r := by
  have hw := hp.wf
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact pair_far hp he hb hf (by rcases hs with hs | hs; exacts [.inl hs, .inr ⟨hs.1, hs.2.1⟩]) r hr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [stR_scratch]
      exact hp.args.rdisj hb (by decide) hf (by kl) (by rcases hs with hs | hs <;> omega)
    · exact (hk.R hb hf).symm

theorem pairH_kb {s₀ s t : State} (hp : Pre P s₀) (hk : Stk128K P s₀) {e : Nat} (he : e+1<P.k*P.k)
    (h : KB P s₀ s) (ht : Keep Paired.pairRegs s t) (hf : Frame (pairWritesH s₀ e) s.mem t.mem) :
    KB P s₀ t := by
  have hw := hp.wf
  have h1 := pairH_far hp hk he (b:=3) (o:=SV P) (l:=48) (by decide) hp.sv (.inr ⟨.inr (by lom), .inr (by lom), by lom⟩)
  have h2 := pairH_far hp hk he (b:=0) (o:=0) (l:=64) (by decide) (by kl) (.inl (by decide))
  exact h.frame ht hf (by decide) fun r hr => ⟨h1 r hr, h2 r hr⟩

theorem BInvW.pairedH {s₀ s t : State} (hp : Pre P s₀) (hk : Stk128K P s₀) {e : Nat} (he : e+1<P.k*P.k)
    (h : BInvW true P s₀ e s) {S : Impl.MlKem.AArch64.Hybrid.HSrc} {ea : Addr} {E : List Byte} {j m : Nat}
    (ht : Hybrid.PairMOutcomeW true S (matSeed (rhoK P s₀) (e/P.k) (e%P.k))
      (matSeed (rhoK P s₀) ((e+1)/P.k) ((e+1)%P.k))
      (kA s₀ 3+BitVec.ofNat 64 SS) (kA s₀ 3+BitVec.ofNat 64 (AH+1024*e))
      (kA s₀ 3+BitVec.ofNat 64 (AH+1024*(e+1))) ea (kA s₀ 3) E j m s t) :
    BInvW true P s₀ (e+2) t := by
  have hw := hp.wf
  have fr : Frame (pairWritesH s₀ e) s.mem t.mem := by
    have f := ht.frame; rw [h.kb.sp] at f; exact f
  have old {i : Nat} (hi : i<e) := pairH_far hp hk he (b:=3) (o:=AH+1024*i) (l:=1024)
    (by decide) (by simp only [kL]; lom) (.inr ⟨.inr (by lom), .inl (by lom), by lom⟩)
  refine ⟨pairH_kb hp hk he h.kb ht.keep fr,?_,?_,?_,?_,?_⟩
  · rw [bytesAt_frame fr (pairH_far hp hk he (by decide) (by kl) (.inr ⟨.inl (by lom), .inl (by lom), by lom⟩))
      (by decide)]
    exact h.rho
  · rw [bytesAt_frame fr (pairH_far hp hk he (by decide) (by kl) (.inr ⟨.inl (by lom), .inl (by lom), by lom⟩))
      (by decide)]
    exact h.sig
  · have hall : allOk P s₀ (e+2) ↔ (allOk P s₀ e ∧
        (sampleNTT 280 (matSeed (rhoK P s₀) (e/P.k) (e%P.k))).isSome) ∧
        (sampleNTT 280 (matSeed (rhoK P s₀) ((e+1)/P.k) ((e+1)%P.k))).isSome := by
      rw [show e+2=(e+1)+1 by omega,allOk_succ,allOk_succ]
    rw [ht.status,h.acc]
    by_cases ha : allOk P s₀ e <;>
      by_cases hb : (sampleNTT 280 (matSeed (rhoK P s₀) (e/P.k) (e%P.k))).isSome <;>
      by_cases hc : (sampleNTT 280 (matSeed (rhoK P s₀) ((e+1)/P.k) ((e+1)%P.k))).isSome <;>
      simp [hall,ha,hb,hc]
  · intro i hi
    rcases (by omega : i<e ∨ i=e ∨ i=e+1) with hi|rfl|rfl
    · exact reducedW_frame fr (old hi) (h.red i hi)
    · exact ht.reducedLeft
    · exact ht.reducedRight
  · intro i hi
    rcases (by omega : i<e ∨ i=e ∨ i=e+1) with hi|rfl|rfl
    · rw [aAtW,polyAtW_frame fr (old hi)]; exact h.res i hi
    · exact ht.left
    · exact ht.right

theorem ekR (s₀ : State) : (⟨kA s₀ 1, P.ekLen⟩ : Region) = R (kA s₀) 1 0 (kL P 1) := by
  simp only [R, ptr_zero, kL]

/-- What a hashing pair of key generation needs of `ek`, the third state and the frame. -/
theorem hash_inputK {s₀ s : State} (hp : Pre P s₀) (hk : Stk128K P s₀) {e : Nat} (he : e+1<P.k*P.k)
    (h : KB P s₀ s) (tk : TStk s) (mt : MatrixTable P s₀ s) :
    Hybrid.HashInput (Impl.MlKem.AArch64.Kem16.kgSrc P) (kA s₀ 3+BitVec.ofNat 64 SS)
      (kA s₀ 3+BitVec.ofNat 64 (AH+1024*e)) (kA s₀ 3+BitVec.ofNat 64 (AH+1024*(e+1)))
      (s.syms "VG_MLKEM_REJ_SHUFFLE") (kA s₀ 1) (kA s₀ 3) s := by
  have hw := hp.wf
  have f1 : AH+1024*e+1024≤kL P 3 := matrixEntry_fit hw (by omega)
  have f2 : AH+1024*(e+1)+1024≤kL P 3 := matrixEntry_fit hw he
  have ek : (⟨kA s₀ 1, (Impl.MlKem.AArch64.Kem16.kgSrc P).len⟩ : Region) = R (kA s₀) 1 0 (kL P 1) := ekR s₀
  have pR : (⟨kA s₀ 3+BitVec.ofNat 64 SS, 2048⟩ : Region) = R (kA s₀) 3 SS 2048 := rfl
  have aR : polyRegion (kA s₀ 3+BitVec.ofNat 64 (AH+1024*e)) = R (kA s₀) 3 (AH+1024*e) 1024 := rfl
  have bR : polyRegion (kA s₀ 3+BitVec.ofNat 64 (AH+1024*(e+1))) = R (kA s₀) 3 (AH+1024*(e+1)) 1024 := rfl
  have fS : 0 + 200 ≤ kL P 3 := by
    show 0 + 200 ≤ P.scl; omega_using [hw.facts.2.2.2.2.2.2.2.2.1]
  have fP : KG.SS + 2048 ≤ kL P 3 := by
    show 1056 + 2048 ≤ P.scl; omega_using [hw.facts.2.2.2.2.2.2.2.2.1]
  have fE : 0 + kL P 1 ≤ kL P 1 := by omega
  refine ⟨⟨cov_w hp h (b := 3) (o := SS) (l := 2048) (by decide) fP, ?_, ?_,
    by rw [h.sp]; exact hk.sp, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, h.x28, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [stR_scratch]; exact cov_w hp h (b := 3) (o := 0) (l := 200) (by decide) fS
  · rw [ek]; exact cov_r hp h (b := 1) (o := 0) (l := kL P 1) (by decide) fE
  · rw [stR_scratch, pR]
    exact hp.args.rdisj (b₁ := 3) (o₁ := 0) (l₁ := 200) (b₂ := 3) (o₂ := SS) (l₂ := 2048)
      (by decide) (by decide) fS fP (.inr (.inl (by decide)))
  · rw [stR_scratch, ek]
    exact hp.args.rdisj (b₁ := 3) (o₁ := 0) (l₁ := 200) (b₂ := 1) (o₂ := 0) (l₂ := kL P 1)
      (by decide) (by decide) fS fE (.inl (by decide))
  · rw [ek, pR]
    exact hp.args.rdisj (b₁ := 1) (o₁ := 0) (l₁ := kL P 1) (b₂ := 3) (o₂ := SS) (l₂ := 2048)
      (by decide) (by decide) fE fP (.inl (by decide))
  · rw [h.sp, pR]; exact hk.R (b := 3) (o := SS) (l := 2048) (by decide) fP
  · rw [h.sp, stR_scratch]; exact hk.R (b := 3) (o := 0) (l := 200) (by decide) fS
  · rw [h.sp, ek]; exact hk.R (b := 1) (o := 0) (l := kL P 1) (by decide) fE
  · show s.gpr .x26 + BitVec.ofNat 64 0 = kA s₀ 1
    rw [h.x26, ptr_zero]
  · rw [stR_scratch]; exact mt.apart.sub_right (R.sub fS)
  · rw [h.sp]; have t := tk.shuffle; rw [h.sp] at t; exact t
  · rw [stR_scratch, aR]
    exact hp.args.rdisj (b₁ := 3) (o₁ := AH+1024*e) (l₁ := 1024) (b₂ := 3) (o₂ := 0) (l₂ := 200)
      (by decide) (by decide) f1 fS (.inr (.inr (by lom)))
  · rw [stR_scratch, bR]
    exact hp.args.rdisj (b₁ := 3) (o₁ := AH+1024*(e+1)) (l₁ := 1024) (b₂ := 3) (o₂ := 0) (l₂ := 200)
      (by decide) (by decide) f2 fS (.inr (.inr (by lom)))
  · rw [ek, aR]
    exact hp.args.rdisj (b₁ := 3) (o₁ := AH+1024*e) (l₁ := 1024) (b₂ := 1) (o₂ := 0) (l₂ := kL P 1)
      (by decide) (by decide) f1 fE (.inl (by decide))
  · rw [ek, bR]
    exact hp.args.rdisj (b₁ := 3) (o₁ := AH+1024*(e+1)) (l₁ := 1024) (b₂ := 1) (o₂ := 0) (l₂ := kL P 1)
      (by decide) (by decide) f2 fE (.inl (by decide))

/-- The rejection table, from the constant tables. -/
theorem matrixTable_of {s₀ s : State} (hp : Pre P s₀) (h : KB P s₀ s) (ta : Tables s) : MatrixTable P s₀ s := by
  have scratch : Covers [⟨kA s₀ 3, P.scl⟩] s.wr := by
    simpa only [R, ptr_zero] using cov_w hp h (b := 3) (o := 0) (l := P.scl) (by decide) (by kl)
  exact ⟨ta.shuffle, ta.shuffleRead, apart_of_covers ta.shuffleApart scratch⟩

/-- The writes of a hashing pair lie in `scratch` and the frame. -/
theorem pairH_wr {s₀ s : State} (hp : Pre P s₀) (hk : KB P s₀ s) {e : Nat} (he : e+1<P.k*P.k) :
    ∀ q ∈ pairWritesH s₀ e, ∃ q' ∈ s.wr ++ [frame s.sp], Region.Sub q q' := by
  have hw := hp.wf
  have f1 : AH+1024*e+1024≤kL P 3 := matrixEntry_fit hw (by omega)
  have f2 : AH+1024*(e+1)+1024≤kL P 3 := matrixEntry_fit hw he
  have fS : 0 + 200 ≤ kL P 3 := by
    show 0 + 200 ≤ P.scl; omega_using [hw.facts.2.2.2.2.2.2.2.2.1]
  have fP : KG.SS + 2048 ≤ kL P 3 := by
    show 1056 + 2048 ≤ P.scl; omega_using [hw.facts.2.2.2.2.2.2.2.2.1]
  have sc : (⟨kA s₀ 3, kL P 3⟩ : Region) ∈ s.wr ++ [frame s.sp] := by rw [hk.wr, hp.wr]; simp
  intro q hq
  simp only [pairWritesH, Hybrid.pairWrites3, Paired.stepWrites, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hq
  rcases hq with (rfl | rfl | rfl) | rfl | rfl
  · exact ⟨_, sc, R.sub (A := kA s₀) (b := 3) (o := SS) (l := 2048) fP⟩
  · exact ⟨_, sc, R.sub (A := kA s₀) (b := 3) (o := AH+1024*e) (l := 1024) f1⟩
  · exact ⟨_, sc, R.sub (A := kA s₀) (b := 3) (o := AH+1024*(e+1)) (l := 1024) f2⟩
  · exact ⟨_, sc, by rw [stR_scratch]; exact R.sub fS⟩
  · exact ⟨_, List.mem_append_right _ (by rw [hk.sp]; exact List.mem_singleton_self _), fun _ h => h⟩

/-- **A hashing pair** of the matrix, between the rows of `t̂`. -/
theorem pair_step {s₀ s : State} (hp : Pre P s₀) (hk : Stk128K P s₀) (hr : Noise.Room P) {p r h m : Nat}
    (he : 2*p+1 < P.k*P.k) (hm : m ≤ 3) (hb : ∀ k < m, 136*(h+k) < P.ekLen) (hhr : 136*(h+m) ≤ 384*r)
    (H : IL P s₀ (2*p) r h s) :
    WP isa (Impl.MlKem.AArch64.Hybrid.pairM SB SS AH P (Impl.MlKem.AArch64.Kem16.kgSrc P) (2*p) h m true) s
      (IL P s₀ (2*p+2) r (h+m)) := by
  have hw := hp.wf
  have kb := H.b.kb
  have hf := hw.facts
  have hkk : P.k * P.k ≤ 16 := hf.2.2.1
  have hoa : AH+1024*(2*p)<65536 := by simp only [KG.AH]; omega
  have hob : AH+1024*(2*p+1)<65536 := by simp only [KG.AH]; omega
  have hk1 : 0 < P.k := by omega
  have hk2 : P.k ≤ 256 := by omega
  have mt := matrixTable_of hp kb H.tables
  have pin := pair_input hp he kb mt
  have hin := hash_inputK hp hk he kb H.tstk mt
  rw [Hybrid.pairM_iff]
  refine WP.mono_syms (Hybrid.pairMCode_ok P (Impl.MlKem.AArch64.Kem16.kgSrc P) (a := 2*p) (j := h) (m := m)
    (srcOkK hw) (by decide) (by decide) (by decide) hoa hob pin hin (fun k hk _ => hb k hk) H.hash rfl
    (by rw [H.b.acc]; split; exacts [Or.inr rfl, Or.inl rfl])) fun t ht sy => ?_
  have post := ht.outcome (p := kA s₀ 3+BitVec.ofNat 64 SS) hk1 hk2
  simp only [Paired.seedBytes, H.b.rho] at post
  have fr : Frame (pairWritesH s₀ (2*p)) s.mem t.mem := by
    have f := post.frame; rw [kb.sp] at f; exact f
  have bt := BInvW.pairedH hp hk he H.b post
  have kbt := bt.kb
  have hrn := H.rn
  have hrk := H.rk
  have far {o l : Nat} (hf : o+l≤kL P 3) (hs : AH + 1024 * (P.k * P.k) ≤ o) :=
    pairH_far hp hk he (b := 3) (o := o) (l := l) (by decide) hf (.inr ⟨.inr (by lom), .inr (by omega), by lom⟩)
  refine ⟨bt, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, ?_, by omega, by omega, H.rk, ?_, hhr, ?_,
    H.tstk.of sy (by rw [kbt.sp, kb.sp])⟩
  · exact polyIsW_frame_poly (w16 := true) fr (far (by kl) (by lom)) (H.sp j hj)
  · exact polyIsW_frame_poly (w16 := true) fr (far (Noise.noise_fits hr hj)
      (by have := Noise.noise_past_kg hr j; lom))
      (H.errors j hj)
  · rw [bytesAt_frame fr (pairH_far hp hk he (by decide) (by kl) (.inl (by decide))) (by decide)]
    exact H.dk j hj
  · refine IL.rowsDone_frame H.rn H.rows fr (fun e' he' q hq => ?_) (fun i' hi' q hq =>
      ⟨pairH_far hp hk he (by decide) (by kl) (.inl (by decide)) q hq,
        pairH_far hp hk he (by decide) (by kl) (.inl (by decide)) q hq⟩)
    exact pairH_far hp hk he (b := 3) (o := AH+1024*e') (l := 1024) (by decide) (by simp only [kL]; lom)
      (.inr ⟨.inr (by lom), .inl (by lom), by lom⟩) q hq
  · rw [post.hash, ← post.ek, Nat.min_eq_right hm]; rfl
  · exact Hybrid.tables_frame128 H.tables H.tstk sy post.keep.rd post.keep.wr post.keep.sp
      (fr.sub (pairH_wr hp kb (by omega)))

end VG.Proof.MlKem.AArch64.KeyGen
