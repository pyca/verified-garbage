module

public import VerifiedGarbage.Proof.MlKem.X86_64.Kg16Tail
public import VerifiedGarbage.Proof.MlKem.X86_64.KgA16
import VerifiedGarbage.Proof.MlKem.X86_64.KgTop

/-!
# ML-KEM on x86-64: key generation with 16-bit polynomials, the samples

After `G(d ‖ k)` (`KeyGen.KA`): the entries of `Â`, as `u16`s
(`samples_ok`), and when every `SampleNTT` succeeded, the outputs of `PRF₂`
(`prfs_ok`) and `s ‖ e` from them (`se_ok`), as `u16`s (`KRest16`), and
their constant time.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace KeyGen16

open KeyGen VG.Impl.MlKem.X86_64.Top16

/-- After the first `e` entries of `Â`. -/
structure KB16 (K : Kem16) (e : Nat) (σ s : State) : Prop where
  a : KA K.L σ s
  m : MatB16 K.L.k K.oA (KPke.kgRho K.L.p (kgD σ)) e s

/-- After the matrix, when every `SampleNTT` succeeded. -/
structure KR0 (K : Kem16) (σ s : State) : Prop where
  kc : KC σ s
  rho : bytesAt s.mem (pa s (sc oG)) 32 = rhoK K.L σ
  sig : bytesAt s.mem (pa s sigP) 32 = KPke.kgSigma K.L.p (kgD σ)
  r15 : s.gpr .r15 = 1
  mat : ∀ e < K.L.k * K.L.k, PolyIsW 16 s.mem (pa s (aP K e)) (aHat (rhoK K.L σ) (e / K.L.k) (e % K.L.k))

section
variable {K : Kem16} (W : Kg16Wf K) {σ : State} (hp : (keyGenK K.L).pre σ)
include W hp

theorem matKeep_ok {e : Nat} {s s' : State} (h : KA K.L σ s) {ws : List (Ptr × Nat)} (hP : PPostB s s' ws)
    (hc : matKeep K e ws = true) :
    KA K.L σ s' ∧ ∀ e' < e, keepB (kgB K.L) ws (sc (K.oA + 512 * e')) 512 = true := by
  simp only [matKeep, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨hkc, kG⟩, kS⟩, kB⟩, kA⟩ := hc
  exact ⟨h.keep W hp hP hkc kG kS kB, kA⟩

theorem sample_step {e : Nat} (he : e < K.L.k * K.L.k) (he' : 4 * (K.L.k * K.L.k / 4) ≤ e) {s : State}
    (h : KB16 K e σ s) : WP isa (sampleIJ16 (sc (K.oA + 512 * e)) (e / K.L.k) (e % K.L.k) (sc K.oW)) s
      (KB16 K (e + 1) σ) := by
  have hc := W.kb e he he'
  simp only [kbChk, Bool.and_eq_true] at hc
  have hk := W.k
  have L₀ := h.a.kc.lay W hp
  refine WP.mono (sampleIJ16_ok L₀ (kgB_bases K.L) rbx_na rbx_na (by have := div_lt_k he; omega)
    (by have := mod_lt_k he; omega) hc.1) fun s' ⟨hP, h15, hres⟩ => ?_
  have ⟨ka, kA⟩ := matKeep_ok W hp h.a hP hc.2
  exact ⟨ka, h.m.single h.a.sb L₀ hP kA h15 hres⟩

theorem quad_step {n : String} {c : Prog isa} (v : S16Ok c) {q : Nat} (hq : q < K.L.k * K.L.k / 4) {s : State}
    (h : KB16 K (4 * q) σ s) : WP isa (quad16 (n, c) K.L.k (4 * q) (sc (K.oA + 512 * (4 * q))) (sc K.oW)) s
      (KB16 K (4 * q + 4) σ) := by
  have hc := W.kq q hq
  simp only [kqChk, Bool.and_eq_true] at hc
  have hk := W.k
  have L₀ := h.a.kc.lay W hp
  refine WP.mono (quad16_ok v L₀ (kgB_bases K.L) (by have : K.L.k * K.L.k ≤ 16 := Nat.mul_le_mul hk.2 hk.2; omega)
    hc.1) fun s' ⟨hP, h15, hres⟩ => ?_
  have ⟨ka, kA⟩ := matKeep_ok W hp h.a hP hc.2
  exact ⟨ka, h.m.four h.a.sb L₀ hP kA h15 hres⟩

theorem samples_ok {n : String} {c : Prog isa} (v : S16Ok c) {s : State} (h : KB16 K 0 σ s) :
    WP isa (mat K (n, c)) s (KB16 K (K.L.k * K.L.k) σ) :=
  samples16_ok' (n, c) K.L.k K.oA (sc K.oW) (I := fun e => KB16 K e σ)
    (fun _ he he' _ hs => sample_step W hp he he' hs) (fun _ hq _ hs => quad_step W hp v hq hs) h

theorem KB16.flag {e : Nat} (he : e ≤ K.L.k * K.L.k) {s s' : State} (h : KB16 K e σ s) (hP : PPost s s' []) :
    KB16 K e σ s' := by
  have L₀ := h.a.kc.lay W hp
  exact ⟨h.a.keep W hp hP.b W.flag W.flagG W.flagS W.flagB, by rw [hP.cs .r15 (by decide)]; exact h.m.r15,
    fun e' he' f hf => L₀.keepPoly16 hP.b (W.flagA e' (by omega)) (h.m.mat e' he' f hf)⟩

end

theorem KR0.start {K : Kem16} {σ s : State} (h : KB16 K (K.L.k * K.L.k) σ s)
    (ho : allOk K.L.k (rhoK K.L σ) (K.L.k * K.L.k)) : KR0 K σ s :=
  ⟨h.a.kc, h.a.rho, h.a.sig, by rw [h.m.r15, ifp ho], fun e he =>
    h.m.mat e he _ (aHat_eq ho (div_lt_k he) (mod_lt_k he))⟩

section
variable {K : Kem16} (W : Kg16Wf K) {σ : State} (hp : (keyGenK K.L).pre σ)
include W hp

theorem KRest16.keep {n : Nat} {s s' : State} (h : KRest16 K n σ s) {ws : List (Ptr × Nat)} (hP : PPost s s' ws)
    (hc : restChk K n ws = true) : KRest16 K n σ s' := by
  simp only [restChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨hkc, kG⟩, kS⟩, kA⟩, kR⟩, kP⟩ := hc
  have L₀ := h.kc.lay W hp
  exact ⟨h.kc.step W hp hP.b hkc, by rw [L₀.keepBytes hP.b kG]; exact h.rho,
    by rw [L₀.keepBytes hP.b kS]; exact h.sig, by rw [hP.cs .r15 (by decide)]; exact h.r15,
    fun e he => L₀.keepPoly16 hP.b (kA e he) (h.mat e he),
    fun N hN => by rw [L₀.keepBytes hP.b (kR N hN)]; exact h.prf N hN,
    fun N hN => L₀.keepPoly16 hP.b (kP N hN) (h.se N hN)⟩

theorem prfs_ok (v : Sample4Impl) {s : State} (h : KR0 K σ s) :
    WP isa (v.callee.prfs 0 (2 * K.L.k) K.oPR (K.oW / 32)) s (KRest16 K 0 σ) := by
  have hc := W.pr
  simp only [prChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨hpc, hkc⟩, kG⟩, kS⟩, kA⟩ := hc
  have L₀ := h.kc.lay W hp
  refine WP.mono (v.prfs_ok L₀ (kgB_bases K.L) (by have := W.k; omega) hpc) fun s' ⟨hP, hb⟩ => ?_
  have hσ : bytesAt s'.mem (pa s' sigP) 32 = bytesAt s.mem (pa s sigP) 32 := L₀.keepBytes hP.b kS
  refine ⟨h.kc.step W hp hP.b hkc, by rw [L₀.keepBytes hP.b kG]; exact h.rho, hσ.trans h.sig,
    by rw [hP.cs .r15 (by decide)]; exact h.r15, fun e he => L₀.keepPoly16 hP.b (kA e he) (h.mat e he),
    fun N hN => ?_, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  rw [Top16.prfO, hP.pa rbx_cs, hb N hN, h.sig, Nat.zero_add]

theorem se_ok {A : Arith} (hA : ArithOk A) {N : Nat} (hN : N < 2 * K.L.k) {s : State} (h : KRest16 K N σ s) :
    WP isa (cbdN K A N) s (KRest16 K (N + 1) σ) := by
  have hc := W.se N hN
  simp only [seChk, Bool.and_eq_true] at hc
  have L₀ := h.kc.lay W hp
  refine WP.mono (cbd2_16At_okL hA L₀ rbx_na hc.1) fun s₁ ⟨hP₁, hp₁⟩ => ?_
  rw [h.prf N hN, ← hP₁.pa rbx_cs] at hp₁
  have hk := h.keep W hp hP₁ hc.2
  refine ⟨hk.kc, hk.rho, hk.sig, hk.r15, hk.mat, hk.prf, fun k hk' => ?_⟩
  rcases (by omega : k < N ∨ k = N) with hk' | rfl
  · exact hk.se k hk'
  · exact hp₁

/-- The samples and the keys, when every `SampleNTT` succeeded. -/
theorem rest_ok (hK : KpkeOk K.L) (v : Sample4Impl) {s : State} (h : KR0 K σ s) :
    WP isa (kgRest K v.callee) s (KFin K.L σ) := by
  unfold kgRest noise
  refine WP.seq (WP.seq (WP.mono (prfs_ok W hp v h) fun s₀ h₀ => WP.mono (seqR_ok (I := fun k => KRest16 K k σ)
    (2 * K.L.k) 0 (fun k _ hk s hs => se_ok W hp v.arith (by omega) hs) s₀ h₀) fun s₁ h₁ => ?_))
  rw [Nat.zero_add] at h₁
  exact tail_ok W hp hK h₁

end

end KeyGen16

end VG.Proof.MlKem.X86_64
