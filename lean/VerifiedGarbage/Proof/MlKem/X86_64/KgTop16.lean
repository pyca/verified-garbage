module

public import VerifiedGarbage.Proof.MlKem.X86_64.Kg16
public import VerifiedGarbage.Proof.MlKem.X86_64.KgTop
import VerifiedGarbage.Proof.MlKem.X86_64.KgCT
meta import VerifiedGarbage.Proof.MlKem.X86_64.KgCT
import Mathlib.Tactic.Conv
meta import Mathlib.Tactic.Conv
meta import VerifiedGarbage.Proof.MlKem.X86_64.YLanes

/-!
# ML-KEM on x86-64: key generation with 16-bit polynomials

The function, piece by piece: it returns 1 with `KeyGen_internal(d, z)` in
`ek` and `dk` if every `SampleNTT` succeeded within 280 iterations, and 0
otherwise (`kemKeyGen16_correct`); it leaks only the pointers and `ρ`
(`kemKeyGen16_ct`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace KeyGen16

open KeyGen VG.Impl.MlKem.X86_64.Top16

theorem KB16.zero {K : Kem16} {σ s : State} (h : KA K.L σ s) (h15 : s.gpr .r15 = 1) : KB16 K 0 σ s :=
  ⟨h, MatB16.zero _ _ _ h15⟩

theorem body_ok {K : Kem16} (hK : KpkeOk K.L) (v : Sample4Impl) (W : Kg16Wf K) {σ : State}
    (hp : (keyGenK K.L).pre σ) {s : State} (h : KB16 K (K.L.k * K.L.k) σ s) :
    WP isa (ifOk (kgRest K v.callee)) s (KEnd K.L σ) := by
  refine ifOk_ok (fun s₁ hP hne => ?_) fun s₁ hP he => ?_
  · have ho := r15_ne h.m.r15 hne
    exact WP.mono (rest_ok W hp hK v (KR0.start (h.flag W hp (Nat.le_refl _) hP) ho)) fun s' hf =>
      ⟨hf.kc, by rw [hf.r15, ifp ho], fun _ => hf⟩
  · have ho := r15_eq h.m.r15 he
    have h' := h.flag W hp (Nat.le_refl _) hP
    exact ⟨h'.a.kc, h'.m.r15, fun h => absurd h ho⟩

end KeyGen16

open KeyGen KeyGen16 in
theorem kemKeyGen16_correct {K : Kem16} (hK : KpkeOk K.L) (v : Sample4Impl) (W : Kg16Wf K) {n : String}
    {c : Prog isa} (hs : v.callee.s16 = some (n, c)) (hctl : ctlOk (kemKeyGen16 K v.callee (n, c)) = true)
    (σ : State) (hp : (keyGenK K.L).pre σ) :
    ∃ t s', Exec isa (kemKeyGen16 K v.callee (n, c)) σ t s' ∧ abiPreserved σ s' ∧ (keyGenK K.L).post σ s' := by
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (pro_ok W hp) fun s₁ ⟨h₁, h15⟩ =>
    WP.seq (WP.mono (gRho_ok W hp h₁ h15) fun s₂ ⟨h₂, h15'⟩ =>
      WP.seq (WP.mono (samples_ok W hp (v.s16 n c hs) (KB16.zero h₂ h15')) fun s₃ h₃ =>
        WP.seq (WP.mono (body_ok hK v W hp h₃) fun s₄ h₄ =>
          WP.mono (topEpi_ok h₄.kc.top (h₄.hin W hp)) fun s₅ ⟨hr, hg, hm⟩ =>
            (⟨hg, post_of W h₄ hr hm⟩ : gprPreserved σ s₅ ∧ (keyGenK K.L).post σ s₅)))))
  exact ⟨t, s', he, abiPreserved_of_ctl hctl he hF.1, hF.2⟩

/-! ## Constant time -/

namespace KeyGen16

open KeyGen VG.Impl.MlKem.X86_64.Top16

variable {K : Kem16} (W : Kg16Wf K)
include W

theorem sample_tr {e : Nat} (he : e < K.L.k * K.L.k) (he' : 4 * (K.L.k * K.L.k / 4) ≤ e) :
    RelCT isa (R K.L (KB16 K e)) (sampleIJ16 (sc (K.oA + 512 * e)) (e / K.L.k) (e % K.L.k) (sc K.oW))
      fun _ _ => True := by
  have hc := W.kb e he he'
  simp only [kbChk, Bool.and_eq_true] at hc
  have hk := W.k
  exact rel2_of (sampleIJ16_tr (kgB_bases K.L) rbx_na rbx_na (by have := div_lt_k he; omega)
      (by have := mod_lt_k he; omega) hc.1 (W.ijT e he))
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨kc_lrel W p₁ p₂ pub h₁.a.kc h₂.a.kc, by rw [h₁.a.sb, h₂.a.sb]; exact rho_pub pub⟩

theorem quad_tr {n : String} {c : Prog isa} (v : S16Ok c) {q : Nat} (hq : q < K.L.k * K.L.k / 4) :
    RelCT isa (R K.L (KB16 K (4 * q))) (quad16 (n, c) K.L.k (4 * q) (sc (K.oA + 512 * (4 * q))) (sc K.oW))
      fun _ _ => True := by
  have hc := W.kq q hq
  simp only [kqChk, Bool.and_eq_true] at hc
  have hk := W.k
  have h16 : K.L.k * K.L.k ≤ 16 := Nat.mul_le_mul hk.2 hk.2
  exact rel2_of (RelCT.exists_ fun ρ => quad16_tr (ρ := ρ) v (kgB_bases K.L) (by omega)
      (fun t ht => ⟨by have := div_lt_k (show 4 * q + t < K.L.k * K.L.k by omega); omega,
        by have := mod_lt_k (show 4 * q + t < K.L.k * K.L.k by omega); omega⟩) hc.1)
    fun σ₁ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨KPke.kgRho K.L.p (kgD σ₁), kc_lrel W p₁ p₂ pub h₁.a.kc h₂.a.kc,
      ⟨h₁.a.sb, fun _ h => absurd h (Nat.not_lt_zero _)⟩,
      ⟨h₂.a.sb.trans (rho_pub pub).symm, fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩

theorem samples_tr {n : String} {c : Prog isa} (v : S16Ok c) :
    RelCT isa (R K.L (KB16 K 0)) (mat K (n, c)) (R K.L (KB16 K (K.L.k * K.L.k))) :=
  samples16_tr' (n, c) K.L.k K.oA (sc K.oW) (R := fun e => R K.L (KB16 K e))
    (fun _ he he' => relInv (fun _ _ hp hs => sample_step W hp he he' hs) (sample_tr W he he'))
    (fun _ hq => relInv (fun _ _ hp hs => quad_step W hp v hq hs) (quad_tr W v hq))

theorem prfs_tr (v : Sample4Impl) :
    RelCT isa (R K.L (KR0 K)) (v.callee.prfs 0 (2 * K.L.k) K.oPR (K.oW / 32)) fun _ _ => True := by
  have hc := W.pr
  simp only [prChk, Bool.and_eq_true] at hc
  exact rel2_of (v.prfs_tr (kgB_bases K.L) (by have := W.k; omega) hc.1.1.1.1) fun _ _ _ _ p₁ p₂ pub h₁ h₂ =>
    kc_lrel W p₁ p₂ pub h₁.kc h₂.kc

theorem se_tr {A : Arith} (hA : ArithOk A) {N : Nat} (hN : N < 2 * K.L.k) :
    RelCT isa (R K.L (KRest16 K N)) (cbdN K A N) fun _ _ => True := by
  have hc := W.se N hN
  simp only [seChk, Bool.and_eq_true] at hc
  exact rel2_of (cbd2_16At_trL hA rbx_na hc.1) fun _ _ _ _ p₁ p₂ pub h₁ h₂ => kc_lrel W p₁ p₂ pub h₁.kc h₂.kc

theorem rest_tr (hK : KpkeOk K.L) (v : Sample4Impl) :
    RelCT isa (R K.L fun σ s => KR0 K σ s ∧ allOk K.L.k (rhoK K.L σ) (K.L.k * K.L.k)) (kgRest K v.callee)
      (R K.L fun σ s => KFin K.L σ s ∧ allOk K.L.k (rhoK K.L σ) (K.L.k * K.L.k)) := by
  unfold kgRest noise
  refine RelCT.seq (R := R K.L fun σ s => KRest16 K (2 * K.L.k) σ s ∧ allOk K.L.k (rhoK K.L σ) (K.L.k * K.L.k))
    (RelCT.seq (R := R K.L fun σ s => KRest16 K 0 σ s ∧ allOk K.L.k (rhoK K.L σ) (K.L.k * K.L.k))
      (relInvC (fun σ s hp hs => prfs_ok W hp v hs) (prfs_tr W v)) ?_) ?_
  · have := seqR_tr (R := fun k => R K.L fun σ s => KRest16 K k σ s ∧ allOk K.L.k (rhoK K.L σ) (K.L.k * K.L.k))
      (2 * K.L.k) 0 fun k _ hk => relInvC (fun σ s hp hs => se_ok W hp v.arith (by omega) hs)
        (se_tr W v.arith (by omega))
    rwa [Nat.zero_add] at this
  · exact relInvC (fun σ s hp hs => tail_ok W hp hK hs) (tail_tr hK W)

omit W in
theorem r15_pub {σ₁ σ₂ x y : State} (pub : (keyGenK K.L).pub σ₁ σ₂) (h₁ : KB16 K (K.L.k * K.L.k) σ₁ x)
    (h₂ : KB16 K (K.L.k * K.L.k) σ₂ y) : x.gpr .r15 = y.gpr .r15 := by
  rw [h₁.m.r15, h₂.m.r15]
  exact congrArg (fun ρ => if allOk K.L.k ρ (K.L.k * K.L.k) then (1 : BitVec 64) else 0) (rho_pub pub)

theorem body_tr (hK : KpkeOk K.L) (v : Sample4Impl) :
    RelCT isa (R K.L (KB16 K (K.L.k * K.L.k))) (ifOk (kgRest K v.callee)) (R K.L (KEnd K.L)) := by
  refine ifOk_tr (fun x y ⟨_, _, _, _, pub, h₁, h₂⟩ => by rw [r15_pub pub h₁ h₂]) ?_ ?_
  · refine RelCT.mono (rest_tr W hK v) (fun x y ⟨x₀, y₀, ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩, hx, hy, hne⟩ => ?_)
      fun x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ =>
        ⟨σ₁, σ₂, p₁, p₂, pub, ⟨h₁.1.kc, by rw [h₁.1.r15, ifp h₁.2], fun _ => h₁.1⟩,
          ⟨h₂.1.kc, by rw [h₂.1.r15, ifp h₂.2], fun _ => h₂.1⟩⟩
    have o₁ := r15_ne h₁.m.r15 hne
    have o₂ : allOk K.L.k (rhoK K.L σ₂) (K.L.k * K.L.k) := by rw [← rho_pub pub]; exact o₁
    exact ⟨σ₁, σ₂, p₁, p₂, pub, ⟨KR0.start (h₁.flag W p₁ (Nat.le_refl _) hx) o₁, o₁⟩,
      ⟨KR0.start (h₂.flag W p₂ (Nat.le_refl _) hy) o₂, o₂⟩⟩
  · rintro x y ⟨x₀, y₀, ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩, hx, hy, he⟩
    have o₁ := r15_eq h₁.m.r15 he
    have o₂ : ¬ allOk K.L.k (rhoK K.L σ₂) (K.L.k * K.L.k) := by rw [← rho_pub pub]; exact o₁
    have k₁ := h₁.flag W p₁ (Nat.le_refl _) hx
    have k₂ := h₂.flag W p₂ (Nat.le_refl _) hy
    exact ⟨σ₁, σ₂, p₁, p₂, pub, ⟨k₁.a.kc, k₁.m.r15, fun h => absurd h o₁⟩, ⟨k₂.a.kc, k₂.m.r15, fun h => absurd h o₂⟩⟩

end KeyGen16

open KeyGen KeyGen16 in
theorem kemKeyGen16_ct {K : Kem16} (hK : KpkeOk K.L) (v : Sample4Impl) (W : Kg16Wf K) {n : String}
    {c : Prog isa} (hs : v.callee.s16 = some (n, c)) :
    ConstantTime isa (keyGenK K.L).pre (keyGenK K.L).pub (kemKeyGen16 K v.callee (n, c)) := by
  refine relStart (Q := fun _ _ => True) ?_
  unfold kemKeyGen16
  refine RelCT.seq (relInv (I' := fun σ s => KC σ s ∧ s.gpr .r15 = 1)
    (fun σ s hp hs => by subst hs; exact pro_ok W hp) pro_tr) ?_
  refine RelCT.seq (relInv (I' := fun σ s => KA K.L σ s ∧ s.gpr .r15 = 1)
    (fun σ s hp hs => gRho_ok W hp hs.1 hs.2) (gRho_tr W)) ?_
  refine RelCT.seq (RelCT.mono (samples_tr W (v.s16 n c hs))
    (fun x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, KB16.zero h₁.1 h₁.2, KB16.zero h₂.1 h₂.2⟩)
    fun _ _ h => h) ?_
  exact RelCT.seq (body_tr W hK v) (RelCT.mono epi_tr (fun _ _ h => h) fun _ _ _ => trivial)

end VG.Proof.MlKem.X86_64
