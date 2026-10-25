module

public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Mr
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.MontPrep
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrShift
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rsa.Ranges
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrMain

/-!
# An FFDH parameter candidate on AArch64: the test of a modulus

`testTail_ok`: with `N` in `aN`, the Montgomery setup, Miller–Rabin's
exponent and the witnesses (`millerRabin_ok`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.ParameterCandidate

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Ffdh.AArch64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MillerRabin.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Proof.Ffdh.ParameterCandidate (checkWitnesses)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sK sCnt)

/-- The header words `montPrep` keeps. -/
theorem mp_hdr (w : Nat) {k : Nat} (hk : k ∈ [0, 2, 3, 18, 22, 27]) :
    ∀ r ∈ mpRanges w, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  simp only [mpRanges, mpTail]
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> exact VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl

/-- The working space fits the exponent. -/
theorem PDims.eZ {p : PP} (h : PDims p) (q : Bool) :
    slot (mW (p.mb q)) aE + 8 * (mW (p.mb q) + 2) ≤ p.Z := by
  have := h.z
  have := h.b1
  obtain ⟨_, _, _, h4⟩ := h.mb q
  simp only [slot, hdrBytes, aE, mW, PP.L] at *
  omega_arith

/-- What the test of `N` (of `mb` bits) in `aN` needs, from octet `u` of the tape. -/
structure TT (p : PP) (mb N u : Nat) (s : State) : Prop where
  st : PSt p (mW mb) s
  mb1 : 511 ≤ mb
  mb2 : mb ≤ 8192
  eZ : slot (mW mb) aE + 8 * (mW mb + 2) ≤ p.Z
  len : word s.mem p.B (8 * kLen) = BitVec.ofNat 64 (mLen mb)
  top : word s.mem p.B (8 * fTop) = BitVec.ofNat 64 (2 ^ mK mb - 1)
  chk : word s.mem p.B (8 * fChecks) = BitVec.ofNat 64 (Spec.Ffdh.primeChecks mb)
  msk : word s.mem p.B (8 * Public.sMask) = mask true
  n : wv s.mem p.B (slot (mW mb) aN) (mW mb) = N
  odd : N % 2 = 1
  lo : 2 ^ (mb - 1) ≤ N
  bl : Spec.RsaKeyGen.bitLength (N - 1) = mb
  used : word s.mem p.B (8 * kUsed) = BitVec.ofNat 64 u
  ul : u ≤ p.r.length
  hL : p.L ≤ p.r.length
  mbb : mb ≤ p.bits

theorem primeChecks_lt (mb : Nat) : Spec.Ffdh.primeChecks mb < 2 ^ 62 := by
  unfold Spec.Ffdh.primeChecks; split <;> decide

theorem primeChecks_pos (mb : Nat) : 1 ≤ Spec.Ffdh.primeChecks mb := by
  unfold Spec.Ffdh.primeChecks; split <;> decide

theorem TT.dims {p : PP} {mb N u : Nat} {s : State} (h : TT p mb N u s) :
    MrDims p (mW mb) N mb (Spec.Ffdh.primeChecks mb) :=
  ⟨rfl, h.mb1, h.mb2, h.eZ, h.odd, Nat.le_trans (show 3 ≤ 2 ^ 2 by decide)
    (Nat.le_trans (Nat.pow_le_pow_right (by decide) (by have := h.mb1; omega_arith)) h.lo), h.bl, primeChecks_lt mb, h.hL, h.mbb⟩

/-- The Montgomery setup and the exponent of the test of `N`. -/
theorem testPre_ok (M : Mont) {p : PP} {mb N u : Nat} {s : State} (h₀ : TT p mb N u s) :
    WP isa (seqs (montPrep M.mm ++ expSetup)) s fun t =>
      MrFix p (mW mb) N mb (Spec.Ffdh.primeChecks mb) t ∧ word t.mem p.B (8 * kUsed) = BitVec.ofNat 64 u ∧
        InScr p.B p.Z s.mem t.mem ∧ Keep mmRegs s t := by
  obtain ⟨h, hmb1, hmb2, hEZ, hlen, htop, hchk, hmsk, hn, hodd, hlo, hbl, hU, hul, -, -⟩ := h₀
  have hws := h.ws
  have hn' := hws.scr.nowrap
  have hZ := hws.hZ
  have h256 := hws.h256
  have hw8 : 8 ≤ mW mb := by simp only [mW]; omega_arith
  have hlo' : 2 ^ (64 * (mW mb - 1)) ≤ N :=
    Nat.le_trans (Nat.pow_le_pow_right (by decide) (by simp only [mW]; omega_arith)) hlo
  have hN3 : 3 ≤ N := Nat.le_trans (show 3 ≤ 2 ^ 2 by decide)
    (Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega_arith)) hlo)
  have hle16 : ∀ r ∈ mpRanges (mW mb), r.1 + r.2 ≤ p.Z := mpRanges_le hZ
  refine wp_seqs_append (by simp [montPrep]) (by simp [expSetup]) ?_
  refine WP.mono (montPrep_ok M hws (by omega_arith) hn hodd hlo')
    fun s₁ ⟨ws₁, inv₁, n₁, r2₁, r1₁, rm1₁, f₁, k₁⟩ => ?_
  have st₁ : PSt p (mW mb) s₁ := h.step ws₁ f₁ (mpRanges_pmut _) hle16 k₁
  refine WP.mono (expSetup_ok ws₁ hEZ n₁ hodd (by omega_arith)) fun s₂ ⟨ex₂, f₂, ws₂, k₂⟩ => ?_
  have hE1 : slot (mW mb) aE + 8 * (mW mb + 1) ≤ p.Z := by omega_arith
  have st₂ : PSt p (mW mb) s₂ := st₁.step ws₂ f₂
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact PMut.ofSlot _ _ _)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact hE1) k₂
  have dE : ∀ {j : Nat}, j < 16 → ∀ r ∈ [(slot (mW mb) aE, 8 * (mW mb + 1))],
      slot (mW mb) j + 8 * (mW mb) ≤ r.1 ∨ r.1 + r.2 ≤ slot (mW mb) j := fun {j} hj r hr => by
    rw [List.mem_singleton.mp hr]
    exact .inl (Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left 8 (Nat.le_add_right _ 2)) _)
      (VG.Proof.Rsa.slot_lt (w := mW mb) (show j < aE by simp only [aE]; omega_arith)))
  have sl : ∀ {j : Nat}, j < 16 → p.B.toNat + slot (mW mb) j + 8 * mW mb ≤ 2 ^ 64 := fun {j} hj => by
    have := VG.Proof.Rsa.slot_lt (w := mW mb) hj; omega_arith
  have dH : ∀ {k : Nat}, k < 32 → ∀ r ∈ [(slot (mW mb) aE, 8 * (mW mb + 1))],
      8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k := fun {k} hk r hr => by
    rw [List.mem_singleton.mp hr]; exact .inl (by simp only [slot, hdrBytes]; omega_arith)
  have hH : ∀ {k : Nat}, k ∈ [0, 2, 3, 18, 22, 27] → word s₂.mem p.B (8 * k) = word s.mem p.B (8 * k) := fun {k} hk => by
    have hk' : k < 32 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; omega_arith
    rw [f₂.word_eq (dH hk') (by omega_arith), f₁.word_eq (mp_hdr _ hk) (by omega_arith)]
  have hWv : ∀ {j : Nat}, j < 16 → wv s₂.mem p.B (slot (mW mb) j) (mW mb) = wv s₁.mem p.B (slot (mW mb) j) (mW mb) :=
    fun {j} hj => f₂.wv_eq (dE hj) (by have := sl hj; omega_arith)
  have hWd : word s₂.mem p.B (slot (mW mb) aN) = word s₁.mem p.B (slot (mW mb) aN) :=
    f₂.word_eq (fun r hr => by have := dE (j := aN) (by decide) r hr; omega_arith) (by have := sl (j := aN) (by decide); omega_arith)
  have hMi : word s₂.mem p.B (8 * sMinv) = word s₁.mem p.B (8 * sMinv) :=
    f₂.word_eq (dH (by decide)) (by simp only [sMinv]; omega_arith)
  have fix : MrFix p (mW mb) N mb (Spec.Ffdh.primeChecks mb) s₂ :=
    ⟨st₂, ⟨_, ⟨ws₂, by rw [hWd, hMi]; exact inv₁, by rw [hWv (by decide)]; exact n₁, rfl,
        by rw [hWv (by decide)]; exact r1₁, by rw [hWv (by decide)]; exact rm1₁⟩⟩, ex₂,
      by rw [hWv (by decide)]; exact r2₁, by rw [hH (k := kLen) (by decide)]; exact hlen,
      by rw [hH (k := fTop) (by decide)]; exact htop, by rw [hH (k := fChecks) (by decide)]; exact hchk,
      by rw [hH (k := Public.sMask) (by decide)]; exact hmsk⟩
  have i12 : InScr p.B p.Z s.mem s₂.mem := (InScr.of_frm f₁ hle16).trans
    (InScr.of_frm f₂ fun r hr => by rw [List.mem_singleton.mp hr]; exact hE1)
  exact ⟨fix, by rw [hH (k := kUsed) (by decide)]; exact hU, i12, (k₁.trans k₂).mono (by decide)⟩

/-- The test of `N` in `aN`, from the Montgomery setup. -/
theorem testTail_ok (M : Mont) (R : Kernel) {p : PP} {mb N u : Nat} {s : State} (h : TT p mb N u s) :
    WP isa (seqs (montPrep M.mm ++ expSetup ++ VG.Impl.Ffdh.AArch64.ParameterCandidate.millerRabin M.mm R.run)) s
      (MrEnd p (mW mb) N mb (Spec.Ffdh.primeChecks mb) s
        (checkWitnesses N (Spec.Ffdh.primeChecks mb) (p.r.drop u))) := by
  refine wp_seqs_append (by simp [montPrep]) (by simp [VG.Impl.Ffdh.AArch64.ParameterCandidate.millerRabin]) ?_
  refine WP.mono (testPre_ok M h) fun t ⟨fix, hU, i12, k₁₂⟩ => ?_
  exact WP.mono (millerRabin_ok M R h.dims fix hU h.ul (primeChecks_pos mb)) fun t' ⟨a, b, c, d, e⟩ =>
    ⟨a, b, c, i12.trans d, (k₁₂.trans e).mono (by decide)⟩

end VG.Proof.Ffdh.AArch64.ParameterCandidate
