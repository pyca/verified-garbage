module

import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Piece
import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly
public import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Samp
meta import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Samp
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Framework.TaintSum
meta import VerifiedGarbage.Proof.Framework.TaintSum
meta import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Piece
import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
meta import VerifiedGarbage.Proof.Framework.Arm.NativeTaint
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Call
meta import VerifiedGarbage.Proof.MlDsa.KeyGen.Leak
meta import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly
meta import VerifiedGarbage.Proof.MlKem.Arm.CallsCT
meta import VerifiedGarbage.Proof.MlKem.Arm.Loops
meta import VerifiedGarbage.Proof.MlKem.Arm.NttInv
meta import VerifiedGarbage.Proof.MlKem.Arm.RowSum
meta import VerifiedGarbage.Proof.MlKem.Arm.SampleCT
meta import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Sha3.Arith
meta import VerifiedGarbage.Proof.Sha3.Arm.Stream.Absorb
meta import VerifiedGarbage.Proof.Sha3.Arm.Stream.Pad

/-! ### `MlDsa.Arm.KeyGen.RestPack`, which this module and modules that import it used -/

section

/-! ### `MlDsa.Arm.KeyGen.RestBase`, which only this module used -/

section

/-!
# ML-DSA key generation on 32-bit ARM: after the samplers

Once the samplers are done, with `Â` and `s₁ ‖ s₂` in memory as `A` and `S`
and `r11` as `R` (`Good`), the rest of the function computes the keys from
them, whatever they are (`KR`): after the copies of `ρ` and `K`
(`copies_piece`), the first `np` entries of `s₁ ‖ s₂` packed to `sk`, the
first `nj` of `s₁` in the NTT domain, and the first `nr` rows of `t` packed to
`pk` and `sk`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.KeyGen
open VG.Impl.MlKem.Arm (copy)
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt bitPack simpleBitPack)
open VG.Proof.MlDsa (polyAt coeffAt Reduced PolyIs)
open VG.Proof.MlDsa.KeyGen (t1K t0K Small Good ifp ifn)
open VG.Spec.Sha3 (bytesAt)

/-- After the samplers: the keys from `A`, `S` and `R`, so far. -/
structure KR (p : Params) (STK : Nat) (σ : State) (A : Nat → Poly) (S : Nat → IPoly) (R : BitVec 32)
    (np nj nr : Nat) (s : State) : Prop where
  kc : KC p STK σ s
  r11 : s.gpr .r11 = R
  good : Good p (xiOf σ) (p.k * p.ℓ) (p.ℓ + p.k) A S R
  small : ∀ r < p.ℓ + p.k, Small p.η (S r)
  aS : ∀ e < p.k * p.ℓ, PolyIs s.mem ((lay p STK σ).A 0 (oP e)) (A e)
  s2 : ∀ i < p.k, PolyIs s.mem ((lay p STK σ).A 0 (oP (p.k * p.ℓ + (p.ℓ + i)))) (toRq (S (p.ℓ + i)))
  s1 : ∀ j < p.ℓ, PolyIs s.mem ((lay p STK σ).A 0 (oP (p.k * p.ℓ + j)))
    (if j < nj then ntt (toRq (S j)) else toRq (S j))
  pk0 : bytesAt s.mem ((lay p STK σ).A 3 0) 32 = rhoOf p σ
  sk0 : bytesAt s.mem ((lay p STK σ).A 4 0) 32 = rhoOf p σ
  sk1 : bytesAt s.mem ((lay p STK σ).A 4 32) 32 = kOf p σ
  packs : ∀ r < np, bytesAt s.mem ((lay p STK σ).A 4 (128 + lenS p * r)) (lenS p) = bitPack (S r) p.η p.η
  rows : ∀ i < nr, bytesAt s.mem ((lay p STK σ).A 3 (32 + 320 * i)) 320 = simpleBitPack (t1K p A S i) 1023 ∧
    bytesAt s.mem ((lay p STK σ).A 4 (oT0 p + 416 * i)) 416 = bitPack (t0K p A S i) 4095 4096

/-- A part that writes `W` keeps what `KR` says. -/
structure KRChk (p : Params) (STK : Nat) (np nj nr : Nat) (W : List (Nat × Nat × Nat)) : Prop where
  kc : kcChk p STK W = true
  aS : ∀ e < p.k * p.ℓ, sepAll [scrLen p, STK, 32, p.pkLen, p.skLen] (0, oP e, 1024) W = true
  s2 : ∀ i < p.k, sepAll [scrLen p, STK, 32, p.pkLen, p.skLen] (0, oP (p.k * p.ℓ + (p.ℓ + i)), 1024) W = true
  s1 : ∀ j < p.ℓ, sepAll [scrLen p, STK, 32, p.pkLen, p.skLen] (0, oP (p.k * p.ℓ + j), 1024) W = true
  pk0 : sepAll [scrLen p, STK, 32, p.pkLen, p.skLen] (3, 0, 32) W = true
  sk0 : sepAll [scrLen p, STK, 32, p.pkLen, p.skLen] (4, 0, 32) W = true
  sk1 : sepAll [scrLen p, STK, 32, p.pkLen, p.skLen] (4, 32, 32) W = true
  packs : ∀ r < np, sepAll [scrLen p, STK, 32, p.pkLen, p.skLen] (4, 128 + lenS p * r, lenS p) W = true
  rows : ∀ i < nr, sepAll [scrLen p, STK, 32, p.pkLen, p.skLen] (3, 32 + 320 * i, 320) W = true ∧
    sepAll [scrLen p, STK, 32, p.pkLen, p.skLen] (4, oT0 p + 416 * i, 416) W = true

/-- Proves a `KRChk`, in each case of `η`. -/
tactic_template "krchk " hF:term:max : tactic => `(tactic| (
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> (try refine ⟨?_, ?_⟩) <;>
      first
        | lsep $hF [kcChk, ($hF).pk, ($hF).sk]
        | rcases ($hF).eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;> lsep $hF [kcChk, ($hF).pk, ($hF).sk, hlen]))

theorem sepAll_append {sz : List Nat} {a : Nat × Nat × Nat} {W₁ W₂ : List (Nat × Nat × Nat)}
    (h₁ : sepAll sz a W₁ = true) (h₂ : sepAll sz a W₂ = true) : sepAll sz a (W₁ ++ W₂) = true := by
  simp only [sepAll, List.all_append, Bool.and_eq_true] at *
  exact ⟨h₁, h₂⟩

theorem kcChk_append {p : Params} {STK : Nat} {W₁ W₂ : List (Nat × Nat × Nat)} (h₁ : kcChk p STK W₁ = true)
    (h₂ : kcChk p STK W₂ = true) : kcChk p STK (W₁ ++ W₂) = true := by
  simp only [kcChk, Bool.and_eq_true] at *
  exact ⟨sepAll_append h₁.1 h₂.1, sepAll_append h₁.2 h₂.2⟩

/-- The checks of two pieces of writes, for both. -/
theorem KRChk.append {p : Params} {STK np nj nr : Nat} {W₁ W₂ : List (Nat × Nat × Nat)}
    (h₁ : KRChk p STK np nj nr W₁) (h₂ : KRChk p STK np nj nr W₂) : KRChk p STK np nj nr (W₁ ++ W₂) :=
  ⟨kcChk_append h₁.kc h₂.kc, fun e he => sepAll_append (h₁.aS e he) (h₂.aS e he),
    fun i hi => sepAll_append (h₁.s2 i hi) (h₂.s2 i hi), fun j hj => sepAll_append (h₁.s1 j hj) (h₂.s1 j hj),
    sepAll_append h₁.pk0 h₂.pk0, sepAll_append h₁.sk0 h₂.sk0, sepAll_append h₁.sk1 h₂.sk1,
    fun r hr => sepAll_append (h₁.packs r hr) (h₂.packs r hr),
    fun i hi => ⟨sepAll_append (h₁.rows i hi).1 (h₂.rows i hi).1, sepAll_append (h₁.rows i hi).2 (h₂.rows i hi).2⟩⟩

/-! The checks of a write to one region, proved once for any region (`krchk` on a
literal list of writes costs seconds). -/

/-- The stack below the function's frame. -/
theorem KRChk.stk {p : Params} (hF : PFacts p) {STK np nj nr : Nat} (hnp : np ≤ p.ℓ + p.k) (hnr : nr ≤ p.k) :
    KRChk p STK np nj nr [(1, 0, STK)] := by
  krchk hF

/-- A write to `scratch` outside the saved registers and the polynomials. -/
theorem KRChk.c0 {p : Params} (hF : PFacts p) {STK np nj nr : Nat} (hnp : np ≤ p.ℓ + p.k) (hnr : nr ≤ p.k)
    {o n : Nat} (h1 : o + n ≤ 840 ∨ 876 ≤ o) (h2 : o + n ≤ oP 0 ∨ oP (p.k * p.ℓ + p.ℓ + p.k) ≤ o)
    (h3 : o + n ≤ scrLen p) : KRChk p STK np nj nr [(0, o, n)] := by
  simp only [oP] at h2
  krchk hF

/-- A write to `pk` after the rows so far. -/
theorem KRChk.c3 {p : Params} (hF : PFacts p) {STK np nj nr : Nat} (hnp : np ≤ p.ℓ + p.k) (hnr : nr ≤ p.k)
    {o n : Nat} (h1 : 32 + 320 * nr ≤ o) (h2 : o + n ≤ p.pkLen) : KRChk p STK np nj nr [(3, o, n)] := by
  rw [hF.pk] at h2
  krchk hF

/-- A write to `sk` after `ρ` and `K`, outside the entries packed and the rows so far. -/
theorem KRChk.c4 {p : Params} (hF : PFacts p) {STK np nj nr : Nat} (hnp : np ≤ p.ℓ + p.k) (hnr : nr ≤ p.k)
    {o n : Nat} (h0 : 64 ≤ o) (hp : o + n ≤ 128 ∨ 128 + lenS p * np ≤ o) (hr : o + n ≤ oT0 p ∨ oT0 p + 416 * nr ≤ o)
    (h2 : o + n ≤ p.skLen) : KRChk p STK np nj nr [(4, o, n)] := by
  rw [hF.sk] at h2
  simp only [oT0] at hr h2
  rcases hF.eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;> rw [hlen] at hp hr h2 <;>
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> (try refine ⟨?_, ?_⟩) <;>
  lsep hF [kcChk, hF.pk, hF.sk, hlen]

theorem KR.keep {p : Params} (hF : PFacts p) {STK : Nat} {σ : State} {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 32}
    {np nj nr : Nat} {s s' : State} (h : KR p STK σ A S R np nj nr s) {W : List (Nat × Nat × Nat)}
    (hk : Kept ((lay p STK σ).RL W) s s') (hc : KRChk p STK np nj nr W) : KR p STK σ A S R np nj nr s' := by
  have hL := h.kc.site.ok
  have hle : lenS p ≤ 2 ^ 64 := by rcases hF.eta with ⟨_, e⟩ | ⟨_, e⟩ <;> omega_using [e]
  have kb : ∀ {i o l : Nat}, sepAll [scrLen p, STK, 32, p.pkLen, p.skLen] (i, o, l) W = true → i ∈ kWb →
      l ≤ 2 ^ 64 → bytesAt s'.mem ((lay p STK σ).A i o) l = bytesAt s.mem ((lay p STK σ).A i o) l :=
    fun hs hi hl => bytes_keepW hL hk.frame hs hi hl
  exact ⟨h.kc.keep hk hc.kc, (hk.cs .r11 (by decide) (by decide)).trans h.r11, h.good, h.small,
    fun e he => polyIs_keepW hL hk.frame (hc.aS e he) (by decide) rfl (h.aS e he),
    fun i hi => polyIs_keepW hL hk.frame (hc.s2 i hi) (by decide) rfl (h.s2 i hi),
    fun j hj => polyIs_keepW hL hk.frame (hc.s1 j hj) (by decide) rfl (h.s1 j hj),
    by rw [kb hc.pk0 (by decide) (by decide)]; exact h.pk0,
    by rw [kb hc.sk0 (by decide) (by decide)]; exact h.sk0,
    by rw [kb hc.sk1 (by decide) (by decide)]; exact h.sk1,
    fun r hr => by
      rw [kb (hc.packs r hr) (by decide) hle]
      exact h.packs r hr,
    fun i hi => ⟨by rw [kb (hc.rows i hi).1 (by decide) (by decide)]; exact (h.rows i hi).1,
      by rw [kb (hc.rows i hi).2 (by decide) (by decide)]; exact (h.rows i hi).2⟩⟩

/-! ## `ρ` and `K` to the keys -/

/-- After the copies, for some `A`, `S` and `R`. -/
abbrev KR0 (p : Params) (STK : Nat) (σ s : State) : Prop := ∃ A S R, KR p STK σ A S R 0 0 0 s

theorem copies_ok {p : Params} (hF : PFacts p) {STK : Nat} {σ s : State}
    (h : KSamp p STK σ (p.k * p.ℓ) (p.ℓ + p.k) s) : WP isa copies s (KR0 p STK σ) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hs := h.k1.kc.site
  unfold copies
  refine WP.seq (WP.mono (copyS hs (sb := .r7) (so := oHX) (db := .r5) (dO := 0) (len := 32) ⟨rfl, by lsep hF⟩
    ⟨rfl, by lsep hF [hF.pk]⟩ (show ix Reg.r5 ∈ kWb by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by lsep hF [hF.pk])) fun s₁ ⟨k₁, b₁⟩ => ?_)
  have h₁ := h.keep k₁ (by lsep hF [k1Chk, kcChk, hF.pk]) (fun e' he' => by lsep hF [hF.pk])
    (fun r' hr' => by lsep hF [hF.pk]) (k₁.cs .r11 (by decide) (by decide))
  refine WP.seq (WP.mono (copyS h₁.k1.kc.site (sb := .r7) (so := oHX) (db := .r6) (dO := 0) (len := 32)
    ⟨rfl, by lsep hF⟩ ⟨rfl, by lsep hF [hF.sk]⟩ (show ix Reg.r6 ∈ kWb by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by lsep hF [hF.sk])) fun s₂ ⟨k₂, b₂⟩ => ?_)
  have h₂ := h₁.keep k₂ (by lsep hF [k1Chk, kcChk, hF.sk]) (fun e' he' => by lsep hF [hF.sk])
    (fun r' hr' => by lsep hF [hF.sk]) (k₂.cs .r11 (by decide) (by decide))
  refine WP.mono (copyS h₂.k1.kc.site (sb := .r7) (so := oHX + 96) (db := .r6) (dO := 32) (len := 32)
    ⟨rfl, by lsep hF⟩ ⟨rfl, by lsep hF [hF.sk]⟩ (show ix Reg.r6 ∈ kWb by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by lsep hF [hF.sk])) fun s₃ ⟨k₃, b₃⟩ => ?_
  have h₃ := h₂.keep k₃ (by lsep hF [k1Chk, kcChk, hF.sk]) (fun e' he' => by lsep hF [hF.sk])
    (fun r' hr' => by lsep hF [hF.sk]) (k₃.cs .r11 (by decide) (by decide))
  have hL := hs.ok
  obtain ⟨A, S, hA, hS, hG⟩ := h₃.ex
  have e1 : ∀ {m : Mem}, bytesAt m ((lay p STK σ).A 0 oHX) 128 = hxOf p σ →
      bytesAt m ((lay p STK σ).A 0 oHX) 32 = rhoOf p σ := fun hx => by
    rw [rho_eq, ← hx, Proof.MlKem.bytesAt_take _ _ (show 32 ≤ 128 by decide)]
  refine ⟨A, S, s₃.gpr .r11, ⟨h₃.k1.kc, rfl, hG, fun r hr => (hS r hr).2, hA,
    fun i hi => (hS (p.ℓ + i) (by omega_using [hi])).1,
    fun j hj => by rw [ifn (Nat.not_lt_zero j)]; exact (hS j (by omega_using [hj])).1, ?_, ?_, ?_,
    fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩
  · rw [bytes_keepW hL k₃.frame (i := 3) (o := 0) (l := 32) (by lsep hF [hF.pk, hF.sk]) (by decide) (by decide),
      bytes_keepW hL k₂.frame (i := 3) (o := 0) (l := 32) (by lsep hF [hF.pk, hF.sk]) (by decide) (by decide)]
    exact b₁.trans (e1 h.k1.hx)
  · rw [bytes_keepW hL k₃.frame (i := 4) (o := 0) (l := 32) (by lsep hF [hF.sk]) (by decide) (by decide)]
    exact b₂.trans (e1 h₁.k1.hx)
  · show bytesAt s₃.mem (lpa (lay p STK σ) (.r6, 32)) 32 = _
    rw [b₃, kOf_eq, ← h₂.k1.hx, Proof.MlKem.bytesAt_slice _ _ (show 96 + 32 ≤ 128 by decide), add_ofNat_add]
    rfl

/-- Two runs in every layout of key generation, from the taint analysis of
the pointers of the layout. -/
theorem ktaint4 {p : Params} {STK : Nat} {c : Prog isa} {hc : VG.Taint.Hint VG.Arm.taint.T}
    (h : (VG.Arm.taint.check (Taint.ofRegs [.r4, .r5, .r6, .r7]) c hc).isSome = true) :
    RelCT isa (KTwo p STK) c fun _ _ => True :=
  ktwo fun _ => taint4 (fun _ _ h => h) h

theorem copies_piece {p : Params} (hF : PFacts p) {STK : Nat} :
    KPiece p STK (fun σ s => KSamp p STK σ (p.k * p.ℓ) (p.ℓ + p.k) s) (KR0 p STK) copies :=
  ⟨fun _ _ _ h => copies_ok hF h,
    rel_of (ktaint4 (by native_taint_decide)) fun _ _ _ _ _ _ pub h₁ h₂ => kc_two pub h₁.k1.kc h₂.k1.kc⟩

end VG.Proof.MlDsa.Arm.KeyGen

end

end

/-!
# ML-DSA key generation on 32-bit ARM: `s₁ ‖ s₂` to `sk`, and `ŝ₁`

Each entry of `s₁ ‖ s₂`, `BitPack`ed to `sk` (`packS_piece`), then `ŝ₁[j] =
NTT(s₁[j])` in place (`nttS_piece`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt bitPack modPm q n)
open VG.Proof.MlDsa (polyAt coeffAt Reduced PolyIs)
open VG.Proof.MlDsa.KeyGen (Small ifp ifn)
open VG.Spec.Sha3 (bytesAt)

/-! ## The coefficients of a small polynomial -/

theorem coeff_val {m : Mem} {a : Addr} {f : Poly} (h : PolyIs m a f) {i : Nat} (hi : i < 256) :
    (coeffAt m a i).toNat = (f[i]'hi).val := by
  have e := congrArg (fun g : Poly => (g[i]'hi).val) h.2
  simp only [polyAt, Vector.getElem_ofFn, Fin.val_ofNat] at e
  rw [← e, Nat.mod_eq_of_lt (h.1 i hi)]

theorem small_mem {η : Nat} {x : IPoly} (h : Small η x) {i : Nat} (hi : i < 256) :
    -(η : Int) ≤ x[i] ∧ x[i] ≤ η := h _ (Vector.mem_toList_iff.mpr (Vector.getElem_mem hi))

theorem small_coeff {m : Mem} {a : Addr} {η : Nat} (hη : η ≤ 4) {x : IPoly} (h : PolyIs m a (toRq x))
    (hs : Small η x) : ∀ i < n, -(η : Int) ≤ modPm (coeffAt m a i).toNat q ∧ modPm (coeffAt m a i).toNat q ≤ η :=
  fun i hi => by
    have hx := small_mem hs hi
    rw [coeff_val h hi]
    simp only [toRq, Vector.getElem_map]
    rw [Proof.MlDsa.KeyGen.modPm_ofInt (by omega_arith) (by omega_arith)]
    exact hx

theorem small_big {η : Nat} (hη : η ≤ 4) {x : IPoly} (hs : Small η x) :
    ∀ c ∈ x.toList, -4190208 ≤ c ∧ c ≤ 4190208 := fun c hc => by
  have := hs c hc; omega_arith

theorem eta_le {p : Params} (hF : PFacts p) : p.η ≤ 4 := by rcases hF.eta with ⟨h, _⟩ | ⟨h, _⟩ <;> omega_arith

theorem eta_params {p : Params} (hF : PFacts p) : (p.η, p.η) ∈ Proof.MlDsa.bitPackParams := by
  rcases hF.eta with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> decide

theorem lenS_eq (p : Params) : lenS p = 32 * Spec.MlDsa.bitlen (p.η + p.η) := by
  rw [lenS, Nat.two_mul]

/-- The entry `r` of `s₁ ‖ s₂`, before `NTT`. -/
theorem KR.sPoly {p : Params} {STK : Nat} {σ : State} {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 32}
    {np nr : Nat} {s : State} (h : KR p STK σ A S R np 0 nr s) {r : Nat} (hr : r < p.ℓ + p.k) :
    PolyIs s.mem ((lay p STK σ).A 0 (oP (p.k * p.ℓ + r))) (toRq (S r)) := by
  by_cases hl : r < p.ℓ
  · have := h.s1 r hl; rwa [ifn (Nat.not_lt_zero r)] at this
  · have := h.s2 (r - p.ℓ) (by omega_arith); rwa [show p.ℓ + (r - p.ℓ) = r by omega_arith] at this

/-- The states after the copies, and the first `np` entries packed, `nj` in
the NTT domain and `nr` rows. -/
abbrev KRx (p : Params) (STK : Nat) (np nj nr : Nat) (σ s : State) : Prop := ∃ A S R, KR p STK σ A S R np nj nr s

section
variable {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : PFacts p) {STK : Nat} (hS : S + 8 ≤ STK)
include hP hF hS

/-! ## `BitPack` of `s₁ ‖ s₂` -/

omit hP hS in
theorem packS_m {σ : State} {r : Nat} (hr : r < p.ℓ + p.k) :
    BpOk (lay p STK σ) kWb (sP p r) p.η p.η (.r6, 128 + lenS p * r) (lenS p) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  rcases hF.eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;>
  exact ⟨⟨sc_ok _, by lsep hF⟩, ⟨rfl, by lsep hF [hF.sk, hlen]⟩, show ix Reg.r6 ∈ kWb by decide,
    by lsep hF [hF.sk, hlen], eta_params hF, lenS_eq p⟩

theorem packS_ok {r : Nat} (hr : r < p.ℓ + p.k) {σ : State} {A : Nat → Poly} {S' : Nat → IPoly} {R : BitVec 32}
    {s : State} (h : KR p STK σ A S' R r 0 0 s) : WP isa (packS P p r) s (KR p STK σ A S' R (r + 1) 0 0) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hs := h.kc.site
  have hSp := h.sPoly hr
  unfold packS bitPackAt
  refine bp_ok hP.bitPack hs (by omega_arith) (packS_m hF hr) hSp.1 (small_coeff (eta_le hF) hSp (h.small r hr))
    fun s' k' hb => ?_
  have hle : 128 + lenS p * r + lenS p ≤ oT0 p := by
    simp only [oT0]; rw [Nat.add_assoc, ← Nat.mul_succ]; exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hr) _
  have hk' := h.keep hF k' ((KRChk.c4 (o := 128 + lenS p * r) (n := lenS p) hF (Nat.le_of_lt hr) (Nat.zero_le _)
    (by omega_arith) (.inr (Nat.le_refl _)) (.inl hle) (by rw [hF.sk]; omega_arith)).append (W₁ := [_])
    (KRChk.stk hF (Nat.le_of_lt hr) (Nat.zero_le _)))
  refine ⟨hk'.kc, hk'.r11, hk'.good, hk'.small, hk'.aS, hk'.s2, hk'.s1, hk'.pk0, hk'.sk0, hk'.sk1,
    fun r' hr' => ?_, hk'.rows⟩
  rcases (by omega_arith : r' < r ∨ r' = r) with hr' | rfl
  · exact hk'.packs r' hr'
  · show bytesAt s'.mem (lpa (lay p STK σ) (.r6, 128 + lenS p * r')) (lenS p) = _
    rw [hb]
    show bitPack ((polyAt s.mem ((lay p STK σ).A 0 (oP (p.k * p.ℓ + r')))).map _) _ _ = _
    rw [hSp.2, Proof.MlDsa.KeyGen.modPm_toRq (small_big (eta_le hF) (h.small r' hr))]

theorem packS_two {r : Nat} (hr : r < p.ℓ + p.k) (σ : State) :
    RelCT isa (fun x y => Two (lay p STK σ) kWb STK x y ∧
      PolyIs x.mem ((lay p STK σ).A 0 (oP (p.k * p.ℓ + r))) (polyAt x.mem ((lay p STK σ).A 0 (oP (p.k * p.ℓ + r)))) ∧
      PolyIs y.mem ((lay p STK σ).A 0 (oP (p.k * p.ℓ + r))) (polyAt y.mem ((lay p STK σ).A 0 (oP (p.k * p.ℓ + r)))) ∧
      (∃ x' : IPoly, PolyIs x.mem ((lay p STK σ).A 0 (oP (p.k * p.ℓ + r))) (toRq x') ∧ Small p.η x') ∧
      (∃ y' : IPoly, PolyIs y.mem ((lay p STK σ).A 0 (oP (p.k * p.ℓ + r))) (toRq y') ∧ Small p.η y'))
      (packS P p r) fun _ _ => True := by
  unfold packS bitPackAt
  exact bp_tr hP.bitPack (by omega_arith) (packS_m hF hr) fun x y ⟨T, rx, ry, ⟨x', hx, sx⟩, ⟨y', hy, sy⟩⟩ =>
    ⟨T.1, T.2.1, T.2.2, rx.1, ry.1, small_coeff (eta_le hF) hx sx, small_coeff (eta_le hF) hy sy⟩

theorem packS_piece {r : Nat} (hr : r < p.ℓ + p.k) :
    KPiece p STK (KRx p STK r 0 0) (KRx p STK (r + 1) 0 0) (packS P p r) :=
  ⟨fun _ _ _ ⟨A, S', R, h⟩ => WP.mono (packS_ok hP hF hS hr h) fun _ h => ⟨A, S', R, h⟩,
    rel_of (RelCT.exists_ fun σ => packS_two hP hF hS hr σ) fun σ₁ _ _ _ _ _ pub ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ =>
      ⟨σ₁, kc_twoL pub h₁.kc h₂.kc, ⟨(h₁.sPoly hr).1, rfl⟩, by rw [lay_pub pub]; exact ⟨(h₂.sPoly hr).1, rfl⟩,
        ⟨_, h₁.sPoly hr, h₁.small r hr⟩, by rw [lay_pub pub]; exact ⟨_, h₂.sPoly hr, h₂.small r hr⟩⟩⟩

/-! ## `NTT` of `s₁` -/

omit hP hS in
theorem nttS_m {σ : State} {j : Nat} (hj : j < p.ℓ) : PtrIn (lay p STK σ) (sP p j) 1024 ∧ PtrIn (lay p STK σ) (sc oSS) 1024 ∧
    sepB (lay p STK σ).sizes (tri (sP p j) 1024) (tri (sc oSS) 1024) = true := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  exact ⟨⟨sc_ok _, by lsep hF⟩, ⟨sc_ok _, by lsep hF⟩, by lsep hF⟩

theorem nttS_ok {j : Nat} (hj : j < p.ℓ) {σ : State} {A : Nat → Poly} {S' : Nat → IPoly} {R : BitVec 32}
    {s : State} (h : KR p STK σ A S' R (p.ℓ + p.k) j 0 s) :
    WP isa (nttS P p j) s (KR p STK σ A S' R (p.ℓ + p.k) (j + 1) 0) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hs := h.kc.site
  have hSj := h.s1 j hj
  rw [ifn (Nat.lt_irrefl j)] at hSj
  obtain ⟨m1, m2, m3⟩ := nttS_m hF (STK := STK) (σ := σ) hj
  unfold nttS nttAt
  refine ip_ok (t := ntt) hP.ntt hs (by omega_arith) m1 m2 (show ix Reg.r7 ∈ kWb by decide)
    (show ix Reg.r7 ∈ kWb by decide) m3 hSj.1 fun s' k' hb => ?_
  have hL := hs.ok
  have hle : lenS p ≤ 2 ^ 64 := by rcases hF.eta with ⟨_, e⟩ | ⟨_, e⟩ <;> omega_arith
  have hpk : ∀ r < p.ℓ + p.k, sepAll [scrLen p, STK, 32, p.pkLen, p.skLen] (4, 128 + lenS p * r, lenS p)
      [tri (sP p j) 1024, tri (sc oSS) 1024, (1, 0, STK)] = true := fun r hr => by
    rcases hF.eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;> lsep hF [hF.sk, hlen]
  refine ⟨h.kc.keep k' (by lsep hF [kcChk]), (k'.cs .r11 (by decide) (by decide)).trans h.r11, h.good, h.small,
    fun e he => polyIs_keepW hL k'.frame (by lsep hF) (by decide) rfl (h.aS e he),
    fun i hi => polyIs_keepW hL k'.frame (by lsep hF) (by decide) rfl (h.s2 i hi), fun j' hj' => ?_,
    by rw [bytes_keepW hL k'.frame (i := 3) (o := 0) (l := 32) (by lsep hF [hF.pk]) (by decide) (by decide)]
       exact h.pk0,
    by rw [bytes_keepW hL k'.frame (i := 4) (o := 0) (l := 32) (by lsep hF [hF.sk]) (by decide) (by decide)]
       exact h.sk0,
    by rw [bytes_keepW hL k'.frame (i := 4) (o := 32) (l := 32) (by lsep hF [hF.sk]) (by decide) (by decide)]
       exact h.sk1,
    fun r hr => by rw [bytes_keepW hL k'.frame (hpk r hr) (by decide) hle]; exact h.packs r hr,
    fun _ h => absurd h (Nat.not_lt_zero _)⟩
  by_cases e : j' = j
  · subst e
    rw [ifp (Nat.lt_succ_self _)]
    show PolyIs s'.mem (lpa (lay p STK σ) (sP p j')) _
    rw [← hSj.2]; exact hb
  · have := polyIs_keepW hL k'.frame (by lsep hF) (by decide) rfl (h.s1 j' hj')
    by_cases hlt : j' < j
    · rwa [ifp hlt, ← ifp (show j' < j + 1 by omega_arith) (ntt (toRq (S' j'))) (toRq (S' j'))] at this
    · rwa [ifn hlt, ← ifn (show ¬ j' < j + 1 by omega_arith) (ntt (toRq (S' j'))) (toRq (S' j'))] at this

theorem nttS_two {j : Nat} (hj : j < p.ℓ) (σ : State) :
    RelCT isa (fun x y => Two (lay p STK σ) kWb STK x y ∧ Reduced x.mem ((lay p STK σ).A 0 (oP (p.k * p.ℓ + j))) ∧
      Reduced y.mem ((lay p STK σ).A 0 (oP (p.k * p.ℓ + j)))) (nttS P p j) fun _ _ => True := by
  obtain ⟨m1, m2, m3⟩ := nttS_m hF (STK := STK) (σ := σ) hj
  unfold nttS nttAt
  exact ip_tr (t := ntt) hP.ntt (by omega_arith) m1 m2 (show ix Reg.r7 ∈ kWb by decide) (show ix Reg.r7 ∈ kWb by decide)
    m3 fun x y ⟨T, rx, ry⟩ => ⟨T.1, T.2.1, T.2.2, rx, ry⟩

theorem nttS_piece {j : Nat} (hj : j < p.ℓ) :
    KPiece p STK (KRx p STK (p.ℓ + p.k) j 0) (KRx p STK (p.ℓ + p.k) (j + 1) 0) (nttS P p j) :=
  ⟨fun _ _ _ ⟨A, S', R, h⟩ => WP.mono (nttS_ok hP hF hS hj h) fun _ h => ⟨A, S', R, h⟩,
    rel_of (RelCT.exists_ fun σ => nttS_two hP hF hS hj σ) fun σ₁ _ _ _ _ _ pub ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ =>
      ⟨σ₁, kc_twoL pub h₁.kc h₂.kc, (h₁.s1 j hj).1, by rw [lay_pub pub]; exact (h₂.s1 j hj).1⟩⟩

end

end VG.Proof.MlDsa.Arm.KeyGen

end

end

/-!
# ML-DSA key generation on 32-bit ARM: the rows of `t`

Row `i` of `t`: the sum of the products `Â[i, j] ŝ₁[j]` in `t` (`rowMul_ok`,
`rowMulAdd_ok`), `NTT⁻¹` of it plus `s₂[i]` (`rowInv_ok`, `rowAdd_ok`), then
`Power2Round` (`rowP2r_ok`) and `t₁[i]` packed to `pk` and `t₀[i]` to `sk`
(`rowSbp_ok`, `rowBp_ok`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt nttInv add multiplyNTT bitPack simpleBitPack power2Round ofInt modPm q n)
open VG.Proof.MlDsa (polyAt natPolyAt coeffAt Reduced PolyIs NatPolyIs)
open VG.Proof.MlDsa.KeyGen (dotK tK t1K t0K ifp ifn idx_lt)
open VG.Spec.Sha3 (bytesAt)

/-- The polynomial `t`, `t₁` and `t₀` of the layout. -/
abbrev oT (p : Params) : Nat := oP (p.k * p.ℓ + p.ℓ + p.k)
abbrev oT1 (p : Params) : Nat := oP (p.k * p.ℓ + p.ℓ + p.k + 1)
abbrev oT0' (p : Params) : Nat := oP (p.k * p.ℓ + p.ℓ + p.k + 2)

/-- The `t` so far. -/
abbrev tIs (p : Params) (STK : Nat) (g : (Nat → Poly) → (Nat → IPoly) → Poly) (σ : State) (A : Nat → Poly)
    (S : Nat → IPoly) (s : State) : Prop := PolyIs s.mem ((lay p STK σ).A 0 (oT p)) (g A S)

/-- In row `i`, with `f` holding of the memory. -/
abbrev RowI (p : Params) (STK : Nat) (i : Nat)
    (f : State → (Nat → Poly) → (Nat → IPoly) → State → Prop) (σ s : State) : Prop :=
  ∃ A S R, KR p STK σ A S R (p.ℓ + p.k) p.ℓ i s ∧ f σ A S s

theorem KR.polyA {p : Params} {STK : Nat} {σ : State} {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 32}
    {np nj nr : Nat} {s : State} (h : KR p STK σ A S R np nj nr s) {i j : Nat} (hi : i < p.k) (hj : j < p.ℓ) :
    PolyIs s.mem ((lay p STK σ).A 0 (oP (p.ℓ * i + j))) (A (p.ℓ * i + j)) := h.aS _ (idx_lt hi hj)

theorem KR.polyS {p : Params} {STK : Nat} {σ : State} {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 32}
    {np nr : Nat} {s : State} (h : KR p STK σ A S R np p.ℓ nr s) {j : Nat} (hj : j < p.ℓ) :
    PolyIs s.mem ((lay p STK σ).A 0 (oP (p.k * p.ℓ + j))) (ntt (toRq (S j))) := by
  have := h.s1 j hj; rwa [ifp hj] at this

theorem modPm_t0 (t : Poly) :
    ((t.map fun c => ofInt (power2Round c).2).map fun c => modPm c.val q) = t.map fun c => (power2Round c).2 := by
  rw [Vector.map_map]
  refine Vector.map_congr_left fun c _ => ?_
  have := Proof.MlDsa.KeyGen.power2Round_snd c
  exact Proof.MlDsa.KeyGen.modPm_ofInt (by omega_using [this]) (by omega_using [this])

theorem t0_coeff {m : Mem} {a : Addr} {t : Poly} (h : PolyIs m a (t.map fun c => ofInt (power2Round c).2)) :
    ∀ i < n, -((4095 : Nat) : Int) ≤ modPm (coeffAt m a i).toNat q ∧ modPm (coeffAt m a i).toNat q ≤ ((4096 : Nat) : Int) :=
  fun j hj => by
    rw [coeff_val h hj]
    simp only [Vector.getElem_map]
    have := Proof.MlDsa.KeyGen.power2Round_snd (t[j]'hj)
    rw [Proof.MlDsa.KeyGen.modPm_ofInt (by omega) (by omega)]
    omega

theorem t1_bound {m : Mem} {a : Addr} {p : Params} {A : Nat → Poly} {S : Nat → IPoly} {i : Nat}
    (h1 : NatPolyIs m a (t1K p A S i)) : ∀ j < n, (coeffAt m a j).toNat ≤ 1023 := fun j hj => by
  rw [show (coeffAt m a j).toNat = (t1K p A S i)[j]'hj from by
    rw [← h1]; simp only [natPolyAt, Vector.getElem_ofFn]]
  simp only [t1K, Vector.getElem_map]
  have := Proof.MlDsa.KeyGen.power2Round_fst ((tK p A S i)[j]'hj)
  omega

/-! ## The checks of the writes of a row, once each -/

theorem chk_poly {p : Params} (hF : PFacts p) {STK i : Nat} (hi : i < p.k) {j : Nat} (hj : j < 3) :
    KRChk p STK (p.ℓ + p.k) p.ℓ i [(0, oP (p.k * p.ℓ + p.ℓ + p.k + j), 1024)] := by
  have := hF.k; have := hF.l; have := hF.kl; have := hF.scr
  exact KRChk.c0 hF (by omega_using []) (by omega_using [hi]) (.inr (by simp only [oP]; omega_using []))
    (.inr (by simp only [oP]; omega_using [])) (by simp only [oP]; omega_using [hj, this])

theorem chk_t {p : Params} (hF : PFacts p) {STK i : Nat} (hi : i < p.k) :
    KRChk p STK (p.ℓ + p.k) p.ℓ i [(0, oP (p.k * p.ℓ + p.ℓ + p.k), 1024), (1, 0, STK)] := by
  have := (chk_poly hF (STK := STK) hi (j := 0) (by decide)).append (W₂ := [_]) (KRChk.stk hF (by omega_using []) (by omega_using [hi]))
  rwa [Nat.add_zero] at this

theorem chk_inv {p : Params} (hF : PFacts p) {STK i : Nat} (hi : i < p.k) :
    KRChk p STK (p.ℓ + p.k) p.ℓ i [(0, oP (p.k * p.ℓ + p.ℓ + p.k), 1024), (0, oSS, 1024), (1, 0, STK)] := by
  have := hF.k; have := hF.l; have := hF.kl; have := hF.scr
  have := (chk_poly hF (STK := STK) hi (j := 0) (by decide)).append (W₁ := [_])
    ((KRChk.c0 (o := oSS) (n := 1024) hF (by omega_using []) (by omega_using [hi]) (.inr (by decide)) (.inl (by decide))
      (by simp only [oSS]; omega_using [this])).append (W₁ := [_]) (KRChk.stk hF (by omega_using []) (by omega_using [hi])))
  rwa [Nat.add_zero] at this

theorem chk_p2r {p : Params} (hF : PFacts p) {STK i : Nat} (hi : i < p.k) :
    KRChk p STK (p.ℓ + p.k) p.ℓ i [(0, oP (p.k * p.ℓ + p.ℓ + p.k + 1), 1024),
      (0, oP (p.k * p.ℓ + p.ℓ + p.k + 2), 1024), (1, 0, STK)] :=
  (chk_poly hF hi (j := 1) (by decide)).append (W₁ := [_])
    ((chk_poly hF hi (j := 2) (by decide)).append (W₁ := [_]) (KRChk.stk hF (by omega_using []) (by omega_using [hi])))

theorem chk_sbp {p : Params} (hF : PFacts p) {STK i : Nat} (hi : i < p.k) :
    KRChk p STK (p.ℓ + p.k) p.ℓ i [(3, 32 + 320 * i, 320), (1, 0, STK)] :=
  (KRChk.c3 hF (Nat.le_refl _) (Nat.le_of_lt hi) (Nat.le_refl _) (by rw [hF.pk]; omega_using [hi])).append (W₁ := [_])
    (KRChk.stk hF (Nat.le_refl _) (Nat.le_of_lt hi))

theorem chk_bp {p : Params} (hF : PFacts p) {STK i : Nat} (hi : i < p.k) :
    KRChk p STK (p.ℓ + p.k) p.ℓ i [(4, oT0 p + 416 * i, 416), (1, 0, STK)] := by
  have := hF.k; have := hF.l
  exact (KRChk.c4 hF (Nat.le_refl _) (Nat.le_of_lt hi) (by simp only [oT0]; omega_using []) (.inr (by simp only [oT0]; omega_using []))
    (.inr (Nat.le_refl _)) (by rw [hF.sk]; omega_using [hi])).append (W₁ := [_]) (KRChk.stk hF (Nat.le_refl _) (Nat.le_of_lt hi))

section
variable {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : PFacts p) {STK : Nat} (hS : S + 8 ≤ STK)
  {i : Nat} (hi : i < p.k)
include hP hF hS hi

/-! ## The calls, one by one -/

/-- `t = Â[i, 0] ŝ₁[0]`. -/
theorem rowMul_ok {σ : State} {A : Nat → Poly} {S' : Nat → IPoly} {R : BitVec 32} {s : State}
    (h : KR p STK σ A S' R (p.ℓ + p.k) p.ℓ i s) :
    WP isa (mulAt P (tP p) (aP (p.ℓ * i)) (sP p 0)) s fun s' =>
      KR p STK σ A S' R (p.ℓ + p.k) p.ℓ i s' ∧ tIs p STK (fun A S => dotK p A S i 1) σ A S' s' := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hx0 := idx_lt (j := 0) hi (by omega_using [hl])
  have hA := h.polyA hi (j := 0) (by omega_using [hl])
  rw [Nat.add_zero] at hx0 hA
  have hS0 := h.polyS (j := 0) (by omega_using [hl])
  rw [Nat.add_zero] at hS0
  refine mul_ok hP.mul h.kc.site (by omega_using [hS]) (h := tP p) (f := aP (p.ℓ * i)) (g := sP p 0)
    ⟨⟨sc_ok _, by lsep hF⟩, ⟨sc_ok _, by lsep hF⟩, ⟨sc_ok _, by lsep hF⟩, show ix Reg.r7 ∈ kWb by decide,
      by lsep hF, by lsep hF⟩ hA.1 hS0.1 fun s' k' hb => ⟨h.keep hF k' (chk_t hF hi), ?_⟩
  show PolyIs s'.mem (lpa (lay p STK σ) (tP p)) _
  dsimp only
  rw [Proof.MlDsa.KeyGen.dotK_one, ← hA.2, ← hS0.2]
  exact hb

/-- `t = t + Â[i, j] ŝ₁[j]`. -/
theorem rowMulAdd_ok {j : Nat} (hj : j < p.ℓ) {σ : State} {A : Nat → Poly} {S' : Nat → IPoly} {R : BitVec 32}
    {s : State} (h : KR p STK σ A S' R (p.ℓ + p.k) p.ℓ i s) (ht : tIs p STK (fun A S => dotK p A S i j) σ A S' s) :
    WP isa (mulAddAt P (tP p) (aP (p.ℓ * i + j)) (sP p j)) s fun s' =>
      KR p STK σ A S' R (p.ℓ + p.k) p.ℓ i s' ∧ tIs p STK (fun A S => dotK p A S i (j + 1)) σ A S' s' := by
  dsimp only [tIs] at ht
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hx0 := idx_lt hi hj
  have hA := h.polyA hi hj
  have hSj := h.polyS hj
  refine mulAdd_ok hP.mulAdd h.kc.site (by omega_using [hS]) (h := tP p) (f := aP (p.ℓ * i + j)) (g := sP p j)
    ⟨⟨sc_ok _, by lsep hF⟩, ⟨sc_ok _, by lsep hF⟩, ⟨sc_ok _, by lsep hF⟩, show ix Reg.r7 ∈ kWb by decide,
      by lsep hF, by lsep hF⟩ ht.1 hA.1 hSj.1 fun s' k' hb => ⟨h.keep hF k' (chk_t hF hi), ?_⟩
  show PolyIs s'.mem (lpa (lay p STK σ) (tP p)) _
  dsimp only
  rw [Proof.MlDsa.KeyGen.dotK_succ, ← hA.2, ← hSj.2, ← ht.2]
  exact hb

omit hP hS hi in
theorem tP_m {σ : State} : PtrIn (lay p STK σ) (tP p) 1024 ∧ PtrIn (lay p STK σ) (sc oSS) 1024 ∧
    sepB (lay p STK σ).sizes (tri (tP p) 1024) (tri (sc oSS) 1024) = true := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  exact ⟨⟨sc_ok _, by lsep hF⟩, ⟨sc_ok _, by lsep hF⟩, by lsep hF⟩

/-- `t = NTT⁻¹(t)`. -/
theorem rowInv_ok {σ : State} {A : Nat → Poly} {S' : Nat → IPoly} {R : BitVec 32} {s : State}
    (h : KR p STK σ A S' R (p.ℓ + p.k) p.ℓ i s) (ht : tIs p STK (fun A S => dotK p A S i p.ℓ) σ A S' s) :
    WP isa (invNttAt P (tP p)) s fun s' =>
      KR p STK σ A S' R (p.ℓ + p.k) p.ℓ i s' ∧ tIs p STK (fun A S => nttInv (dotK p A S i p.ℓ)) σ A S' s' := by
  dsimp only [tIs] at ht
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  obtain ⟨m1, m2, m3⟩ := tP_m hF (σ := σ)
  unfold invNttAt
  refine ip_ok (t := nttInv) hP.invNtt h.kc.site (by omega_using [hS]) m1 m2 (show ix Reg.r7 ∈ kWb by decide)
    (show ix Reg.r7 ∈ kWb by decide) m3 ht.1 fun s' k' hb => ⟨h.keep hF k' (chk_inv hF hi), ?_⟩
  show PolyIs s'.mem (lpa (lay p STK σ) (tP p)) _
  dsimp only
  rw [← ht.2]
  exact hb

/-- `t = t + s₂[i]`. -/
theorem rowAdd_ok {σ : State} {A : Nat → Poly} {S' : Nat → IPoly} {R : BitVec 32} {s : State}
    (h : KR p STK σ A S' R (p.ℓ + p.k) p.ℓ i s)
    (ht : tIs p STK (fun A S => nttInv (dotK p A S i p.ℓ)) σ A S' s) :
    WP isa (addAt P (tP p) (sP p (p.ℓ + i))) s fun s' =>
      KR p STK σ A S' R (p.ℓ + p.k) p.ℓ i s' ∧ tIs p STK (fun A S => tK p A S i) σ A S' s' := by
  dsimp only [tIs] at ht
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hS2 := h.s2 i hi
  refine add_ok hP.add h.kc.site (by omega_using [hS]) (f := tP p) (g := sP p (p.ℓ + i))
    ⟨⟨sc_ok _, by lsep hF⟩, ⟨sc_ok _, by lsep hF⟩, show ix Reg.r7 ∈ kWb by decide, by lsep hF⟩ ht.1 hS2.1
    fun s' k' hb => ⟨h.keep hF k' (chk_t hF hi), ?_⟩
  show PolyIs s'.mem (lpa (lay p STK σ) (tP p)) _
  dsimp only
  rw [Proof.MlDsa.KeyGen.tK, ← hS2.2, ← ht.2]
  exact hb

omit hP hS hi in
theorem p2r_m {σ : State} : P2rOk (lay p STK σ) kWb (tP p) (t1P p) (t0P p) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  exact ⟨⟨sc_ok _, by lsep hF⟩, ⟨sc_ok _, by lsep hF⟩, ⟨sc_ok _, by lsep hF⟩, show ix Reg.r7 ∈ kWb by decide,
    show ix Reg.r7 ∈ kWb by decide, by lsep hF, by lsep hF, by lsep hF⟩

/-- After `Power2Round`. -/
abbrev p2rIs (p : Params) (STK i : Nat) (σ : State) (A : Nat → Poly) (S : Nat → IPoly) (s : State) : Prop :=
  NatPolyIs s.mem ((lay p STK σ).A 0 (oT1 p)) (t1K p A S i) ∧
    PolyIs s.mem ((lay p STK σ).A 0 (oT0' p)) ((tK p A S i).map fun c => ofInt (power2Round c).2)

/-- `Power2Round` of `t`. -/
theorem rowP2r_ok {σ : State} {A : Nat → Poly} {S' : Nat → IPoly} {R : BitVec 32} {s : State}
    (h : KR p STK σ A S' R (p.ℓ + p.k) p.ℓ i s) (ht : tIs p STK (fun A S => tK p A S i) σ A S' s) :
    WP isa (power2RoundAt P (tP p) (t1P p) (t0P p)) s fun s' =>
      KR p STK σ A S' R (p.ℓ + p.k) p.ℓ i s' ∧ p2rIs p STK i σ A S' s' := by
  dsimp only [tIs] at ht
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  refine p2r_ok hP.power2Round h.kc.site (by omega_using [hS]) (p2r_m hF) ht.1 fun s' k' h1 h0 =>
    ⟨h.keep hF k' (chk_p2r hF hi), ?_, ?_⟩
  · show NatPolyIs s'.mem (lpa (lay p STK σ) (t1P p)) _
    rw [t1K, ← ht.2]; exact h1
  · show PolyIs s'.mem (lpa (lay p STK σ) (t0P p)) _
    rw [← ht.2]; exact h0

/-- After `t₁[i]` to `pk`. -/
abbrev sbpIs (p : Params) (STK i : Nat) (σ : State) (A : Nat → Poly) (S : Nat → IPoly) (s : State) : Prop :=
  PolyIs s.mem ((lay p STK σ).A 0 (oT0' p)) ((tK p A S i).map fun c => ofInt (power2Round c).2) ∧
    bytesAt s.mem ((lay p STK σ).A 3 (32 + 320 * i)) 320 = simpleBitPack (t1K p A S i) 1023

omit hP hS in
theorem sbp_m {σ : State} : SbpOk (lay p STK σ) kWb (t1P p) 1023 (.r5, 32 + 320 * i) 320 := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  exact ⟨⟨sc_ok _, by lsep hF⟩, ⟨rfl, by lsep hF [hF.pk]⟩, show ix Reg.r5 ∈ kWb by decide, by lsep hF [hF.pk],
    by decide, by decide⟩

/-- `t₁[i]` to `pk`. -/
theorem rowSbp_ok {σ : State} {A : Nat → Poly} {S' : Nat → IPoly} {R : BitVec 32} {s : State}
    (h : KR p STK σ A S' R (p.ℓ + p.k) p.ℓ i s) (h1 : p2rIs p STK i σ A S' s) :
    WP isa (simpleBitPackAt P (t1P p) 1023 (.r5, 32 + 320 * i) 320) s fun s' =>
      KR p STK σ A S' R (p.ℓ + p.k) p.ℓ i s' ∧ sbpIs p STK i σ A S' s' := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  refine sbp_ok hP.simpleBitPack h.kc.site (by omega_using [hS]) (sbp_m hF hi) (t1_bound h1.1) fun s' k' hb =>
    ⟨h.keep hF k' (chk_sbp hF hi), polyIs_keepW h.kc.site.ok k'.frame (by lsep hF [hF.pk]) (by decide) rfl h1.2, ?_⟩
  show bytesAt s'.mem (lpa (lay p STK σ) (.r5, 32 + 320 * i)) 320 = _
  rw [hb]
  exact congrArg (simpleBitPack · 1023) h1.1

omit hP hS in
theorem bp_m {σ : State} : BpOk (lay p STK σ) kWb (t0P p) 4095 4096 (.r6, oT0 p + 416 * i) 416 := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  rcases hF.eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;>
  exact ⟨⟨sc_ok _, by lsep hF⟩, ⟨rfl, by lsep hF [hF.sk, hlen]⟩, show ix Reg.r6 ∈ kWb by decide,
    by lsep hF [hF.sk, hlen], by decide, by decide⟩

/-- `t₀[i]` to `sk`. -/
theorem rowBp_ok {σ : State} {A : Nat → Poly} {S' : Nat → IPoly} {R : BitVec 32} {s : State}
    (h : KR p STK σ A S' R (p.ℓ + p.k) p.ℓ i s) (h0 : sbpIs p STK i σ A S' s) :
    WP isa (bitPackAt P (t0P p) 4095 4096 (.r6, oT0 p + 416 * i) 416) s
      (KR p STK σ A S' R (p.ℓ + p.k) p.ℓ (i + 1)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  unfold bitPackAt
  refine bp_ok hP.bitPack h.kc.site (by omega_using [hS]) (bp_m hF hi) h0.1.1 (t0_coeff h0.1) fun s' k' hb => ?_
  have hk' := h.keep hF k' (chk_bp hF hi)
  refine ⟨hk'.kc, hk'.r11, hk'.good, hk'.small, hk'.aS, hk'.s2, hk'.s1, hk'.pk0, hk'.sk0, hk'.sk1, hk'.packs,
    fun i' hi' => ?_⟩
  rcases (by omega_using [hi'] : i' < i ∨ i' = i) with hi' | rfl
  · exact hk'.rows i' hi'
  · refine ⟨?_, ?_⟩
    · rw [bytes_keepW h.kc.site.ok k'.frame (i := 3) (o := 32 + 320 * i') (l := 320)
        (by rcases hF.eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;> lsep hF [hF.pk, hF.sk, hlen]) (by decide) (by decide)]
      exact h0.2
    · show bytesAt s'.mem (lpa (lay p STK σ) (.r6, oT0 p + 416 * i')) 416 = _
      rw [hb]
      show bitPack ((polyAt s.mem ((lay p STK σ).A 0 (oT0' p))).map _) _ _ = _
      rw [h0.1.2, modPm_t0]
      rfl

/-! ## The pieces of a row -/

theorem rowMul_piece :
    KPiece p STK (KRx p STK (p.ℓ + p.k) p.ℓ i) (RowI p STK i (tIs p STK fun A S => dotK p A S i 1))
      (mulAt P (tP p) (aP (p.ℓ * i)) (sP p 0)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hx0 := idx_lt (j := 0) hi (by omega_using [hl])
  rw [Nat.add_zero] at hx0
  refine ⟨fun _ _ _ ⟨A, S', R, h⟩ => WP.mono (rowMul_ok hP hF hS hi h) fun _ h => ⟨A, S', R, h⟩,
    rel_of (Q := fun x y => ∃ σ, Two (lay p STK σ) kWb STK x y ∧
      (Reduced x.mem ((lay p STK σ).A 0 (oP (p.ℓ * i))) ∧ Reduced x.mem ((lay p STK σ).A 0 (oP (p.k * p.ℓ)))) ∧
      (Reduced y.mem ((lay p STK σ).A 0 (oP (p.ℓ * i))) ∧ Reduced y.mem ((lay p STK σ).A 0 (oP (p.k * p.ℓ)))))
      (RelCT.exists_ fun σ => mul_tr hP.mul (by omega_using [hS]) (h := tP p) (f := aP (p.ℓ * i)) (g := sP p 0)
        ⟨⟨sc_ok _, by lsep hF⟩, ⟨sc_ok _, by lsep hF⟩, ⟨sc_ok _, by lsep hF⟩, show ix Reg.r7 ∈ kWb by decide,
          by lsep hF, by lsep hF⟩ fun x y ⟨T, ⟨a, b⟩, ⟨c, d⟩⟩ => ⟨T.1, T.2.1, T.2.2, a, b, c, d⟩) ?_⟩
  intro σ₁ _ _ _ _ _ pub ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩
  have a₁ := h₁.polyA hi (j := 0) (by omega_using [hl]); have a₂ := h₂.polyA hi (j := 0) (by omega_using [hl])
  have s₁ := h₁.polyS (j := 0) (by omega_using [hl]); have s₂ := h₂.polyS (j := 0) (by omega_using [hl])
  rw [Nat.add_zero] at a₁ a₂ s₁ s₂
  rw [← lay_pub pub] at a₂ s₂
  exact ⟨σ₁, kc_twoL pub h₁.kc h₂.kc, ⟨a₁.1, s₁.1⟩, ⟨a₂.1, s₂.1⟩⟩

theorem rowMulAdd_piece {j : Nat} (hj : j < p.ℓ) :
    KPiece p STK (RowI p STK i (tIs p STK fun A S => dotK p A S i j))
      (RowI p STK i (tIs p STK fun A S => dotK p A S i (j + 1))) (mulAddAt P (tP p) (aP (p.ℓ * i + j)) (sP p j)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hx0 := idx_lt hi hj
  refine ⟨fun _ _ _ ⟨A, S', R, h, ht⟩ => WP.mono (rowMulAdd_ok hP hF hS hi hj h ht) fun _ h => ⟨A, S', R, h⟩,
    rel_of (Q := fun x y => ∃ σ, Two (lay p STK σ) kWb STK x y ∧
      (Reduced x.mem ((lay p STK σ).A 0 (oT p)) ∧ Reduced x.mem ((lay p STK σ).A 0 (oP (p.ℓ * i + j))) ∧
        Reduced x.mem ((lay p STK σ).A 0 (oP (p.k * p.ℓ + j)))) ∧
      (Reduced y.mem ((lay p STK σ).A 0 (oT p)) ∧ Reduced y.mem ((lay p STK σ).A 0 (oP (p.ℓ * i + j))) ∧
        Reduced y.mem ((lay p STK σ).A 0 (oP (p.k * p.ℓ + j)))))
      (RelCT.exists_ fun σ => mulAdd_tr hP.mulAdd (by omega_using [hS]) (h := tP p) (f := aP (p.ℓ * i + j)) (g := sP p j)
        ⟨⟨sc_ok _, by lsep hF⟩, ⟨sc_ok _, by lsep hF⟩, ⟨sc_ok _, by lsep hF⟩, show ix Reg.r7 ∈ kWb by decide,
          by lsep hF, by lsep hF⟩ fun x y ⟨T, ⟨a, b, c⟩, ⟨d, e, f⟩⟩ => ⟨T.1, T.2.1, T.2.2, a, b, c, d, e, f⟩) ?_⟩
  intro σ₁ _ _ _ _ _ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩
  have a₂ := (h₂.polyA hi hj).1; have s₂ := (h₂.polyS hj).1; have t₂' := t₂.1
  rw [← lay_pub pub] at a₂ s₂ t₂'
  exact ⟨σ₁, kc_twoL pub h₁.kc h₂.kc, ⟨t₁.1, (h₁.polyA hi hj).1, (h₁.polyS hj).1⟩, ⟨t₂', a₂, s₂⟩⟩

theorem rowInv_piece :
    KPiece p STK (RowI p STK i (tIs p STK fun A S => dotK p A S i p.ℓ))
      (RowI p STK i (tIs p STK fun A S => nttInv (dotK p A S i p.ℓ))) (invNttAt P (tP p)) := by
  refine ⟨fun _ _ _ ⟨A, S', R, h, ht⟩ => WP.mono (rowInv_ok hP hF hS hi h ht) fun _ h => ⟨A, S', R, h⟩,
    rel_of (Q := fun x y => ∃ σ, Two (lay p STK σ) kWb STK x y ∧ Reduced x.mem ((lay p STK σ).A 0 (oT p)) ∧
      Reduced y.mem ((lay p STK σ).A 0 (oT p)))
      (RelCT.exists_ fun σ => by
        obtain ⟨m1, m2, m3⟩ := tP_m hF (σ := σ)
        unfold invNttAt
        exact ip_tr (t := nttInv) hP.invNtt (by omega_using [hS]) m1 m2 (show ix Reg.r7 ∈ kWb by decide)
          (show ix Reg.r7 ∈ kWb by decide) m3 fun x y ⟨T, a, b⟩ => ⟨T.1, T.2.1, T.2.2, a, b⟩) ?_⟩
  intro σ₁ _ _ _ _ _ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩
  have t₂' := t₂.1
  rw [← lay_pub pub] at t₂'
  exact ⟨σ₁, kc_twoL pub h₁.kc h₂.kc, t₁.1, t₂'⟩

theorem rowAdd_piece :
    KPiece p STK (RowI p STK i (tIs p STK fun A S => nttInv (dotK p A S i p.ℓ)))
      (RowI p STK i (tIs p STK fun A S => tK p A S i)) (addAt P (tP p) (sP p (p.ℓ + i))) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  refine ⟨fun _ _ _ ⟨A, S', R, h, ht⟩ => WP.mono (rowAdd_ok hP hF hS hi h ht) fun _ h => ⟨A, S', R, h⟩,
    rel_of (Q := fun x y => ∃ σ, Two (lay p STK σ) kWb STK x y ∧
      (Reduced x.mem ((lay p STK σ).A 0 (oT p)) ∧ Reduced x.mem ((lay p STK σ).A 0 (oP (p.k * p.ℓ + (p.ℓ + i))))) ∧
      (Reduced y.mem ((lay p STK σ).A 0 (oT p)) ∧ Reduced y.mem ((lay p STK σ).A 0 (oP (p.k * p.ℓ + (p.ℓ + i))))))
      (RelCT.exists_ fun σ => add_tr hP.add (by omega_using [hS]) (f := tP p) (g := sP p (p.ℓ + i))
        ⟨⟨sc_ok _, by lsep hF⟩, ⟨sc_ok _, by lsep hF⟩, show ix Reg.r7 ∈ kWb by decide, by lsep hF⟩
        fun x y ⟨T, ⟨a, b⟩, ⟨c, d⟩⟩ => ⟨T.1, T.2.1, T.2.2, a, b, c, d⟩) ?_⟩
  intro σ₁ _ _ _ _ _ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩
  have t₂' := t₂.1; have s₂ := (h₂.s2 i hi).1
  rw [← lay_pub pub] at t₂' s₂
  exact ⟨σ₁, kc_twoL pub h₁.kc h₂.kc, ⟨t₁.1, (h₁.s2 i hi).1⟩, ⟨t₂', s₂⟩⟩

theorem rowP2r_piece :
    KPiece p STK (RowI p STK i (tIs p STK fun A S => tK p A S i)) (RowI p STK i (p2rIs p STK i))
      (power2RoundAt P (tP p) (t1P p) (t0P p)) := by
  refine ⟨fun _ _ _ ⟨A, S', R, h, ht⟩ => WP.mono (rowP2r_ok hP hF hS hi h ht) fun _ h => ⟨A, S', R, h⟩,
    rel_of (Q := fun x y => ∃ σ, Two (lay p STK σ) kWb STK x y ∧ Reduced x.mem ((lay p STK σ).A 0 (oT p)) ∧
      Reduced y.mem ((lay p STK σ).A 0 (oT p)))
      (RelCT.exists_ fun σ => p2r_tr hP.power2Round (by omega_using [hS]) (p2r_m hF)
        fun x y ⟨T, a, b⟩ => ⟨T.1, T.2.1, T.2.2, a, b⟩) ?_⟩
  intro σ₁ _ _ _ _ _ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩
  have t₂' := t₂.1
  rw [← lay_pub pub] at t₂'
  exact ⟨σ₁, kc_twoL pub h₁.kc h₂.kc, t₁.1, t₂'⟩

theorem rowSbp_piece :
    KPiece p STK (RowI p STK i (p2rIs p STK i)) (RowI p STK i (sbpIs p STK i))
      (simpleBitPackAt P (t1P p) 1023 (.r5, 32 + 320 * i) 320) := by
  refine ⟨fun _ _ _ ⟨A, S', R, h, h1⟩ => WP.mono (rowSbp_ok hP hF hS hi h h1) fun _ h => ⟨A, S', R, h⟩,
    rel_of (Q := fun x y => ∃ σ, Two (lay p STK σ) kWb STK x y ∧
      (∀ j < n, (coeffAt x.mem ((lay p STK σ).A 0 (oT1 p)) j).toNat ≤ 1023) ∧
      (∀ j < n, (coeffAt y.mem ((lay p STK σ).A 0 (oT1 p)) j).toNat ≤ 1023))
      (RelCT.exists_ fun σ => sbp_tr hP.simpleBitPack (by omega_using [hS]) (sbp_m hF hi)
        fun x y ⟨T, a, b⟩ => ⟨T.1, T.2.1, T.2.2, a, b⟩) ?_⟩
  intro σ₁ _ _ _ _ _ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩
  have t₂' := t1_bound t₂.1
  rw [← lay_pub pub] at t₂'
  exact ⟨σ₁, kc_twoL pub h₁.kc h₂.kc, t1_bound t₁.1, t₂'⟩

theorem rowBp_piece :
    KPiece p STK (RowI p STK i (sbpIs p STK i)) (KRx p STK (p.ℓ + p.k) p.ℓ (i + 1))
      (bitPackAt P (t0P p) 4095 4096 (.r6, oT0 p + 416 * i) 416) := by
  refine ⟨fun _ _ _ ⟨A, S', R, h, h0⟩ => WP.mono (rowBp_ok hP hF hS hi h h0) fun _ h => ⟨A, S', R, h⟩,
    rel_of (Q := fun x y => ∃ σ, Two (lay p STK σ) kWb STK x y ∧
      (Reduced x.mem ((lay p STK σ).A 0 (oT0' p)) ∧ ∀ j < n, -((4095 : Nat) : Int) ≤
        modPm (coeffAt x.mem ((lay p STK σ).A 0 (oT0' p)) j).toNat q ∧
        modPm (coeffAt x.mem ((lay p STK σ).A 0 (oT0' p)) j).toNat q ≤ ((4096 : Nat) : Int)) ∧
      (Reduced y.mem ((lay p STK σ).A 0 (oT0' p)) ∧ ∀ j < n, -((4095 : Nat) : Int) ≤
        modPm (coeffAt y.mem ((lay p STK σ).A 0 (oT0' p)) j).toNat q ∧
        modPm (coeffAt y.mem ((lay p STK σ).A 0 (oT0' p)) j).toNat q ≤ ((4096 : Nat) : Int)))
      (RelCT.exists_ fun σ => by
        unfold bitPackAt
        exact bp_tr hP.bitPack (by omega_using [hS]) (bp_m hF hi)
          fun x y ⟨T, ⟨a, b⟩, ⟨c, d⟩⟩ => ⟨T.1, T.2.1, T.2.2, a, c, b, d⟩) ?_⟩
  intro σ₁ _ _ _ _ _ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩
  have r₂ := t₂.1.1; have c₂ := t0_coeff t₂.1
  rw [← lay_pub pub] at r₂ c₂
  exact ⟨σ₁, kc_twoL pub h₁.kc h₂.kc, ⟨t₁.1.1, t0_coeff t₁.1⟩, ⟨r₂, c₂⟩⟩

end

end VG.Proof.MlDsa.Arm.KeyGen
