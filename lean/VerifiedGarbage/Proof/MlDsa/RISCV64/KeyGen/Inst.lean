module

public import VerifiedGarbage.Impl.MlDsa.RISCV64.KeyGen.Inst
public import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.Samp
import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.Ntt
import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.NttInv
import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.Mul
import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.RISCV64.Sample.RejNtt
import VerifiedGarbage.Proof.MlDsa.RISCV64.Sample.RejBounded
import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.SimpleBitPack
import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.BitPack
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlDsa.RISCV64.Round.Arith
public import VerifiedGarbage.Proof.MlDsa.Round.Mem
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.MlKem.RISCV64.Common
import VerifiedGarbage.Proof.MlKem.RISCV64.Add
import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.Common
import VerifiedGarbage.Proof.Framework.RISCV64.Run
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Round.Arith
meta import VerifiedGarbage.Proof.MlDsa.Round.Mem
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Common
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Add
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.Common
meta import VerifiedGarbage.Proof.Framework.RISCV64.Run
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.RISCV64.Isa
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.MlDsa.KeyGen.Rest
import VerifiedGarbage.Proof.MlKem.KPke
import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly
import VerifiedGarbage.Proof.MlDsa.KeyGen.Mono
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.Samp
meta import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly
meta import VerifiedGarbage.Proof.MlDsa.KeyGen.Mono
meta import VerifiedGarbage.Proof.MlKem.Mem

/-! ### `MlDsa.RISCV64.KeyGen.Top`, which only this module used -/

section

/-! ### `MlDsa.RISCV64.KeyGen.RestRow`, which only this module used -/

section

/-! ### `MlDsa.RISCV64.KeyGen.RestBase`, which only this module used -/

section

/-!
# ML-DSA key generation on RISC-V: after the samplers

As on PPC64LE (`Proof/MlDsa/PPC64LE/KeyGen/Top.lean`): once the samplers
are done, with `Â` and `s₁ ‖ s₂` in memory as `A` and `S` and `s4` as `R`
(`Good` of its low word), the rest of the function computes the keys from
them, whatever they are (`KR`): after the copies of `ρ` and `K`
(`copies_piece`), the first `np` entries of `s₁ ‖ s₂` packed to `sk`, the
first `nj` of `s₁` in the NTT domain, and the first `nr` rows of `t` packed
to `pk` and `sk`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.KeyGen

open VG VG.RISCV64 VG.Proof.MlKem.RISCV64
open VG.Impl.MlDsa.RISCV64.KeyGen
open VG.Impl.MlKem.RISCV64 (copy)
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt bitPack simpleBitPack)
open VG.Proof.MlDsa (polyAt coeffAt Reduced PolyIs)
open VG.Proof.MlDsa.KeyGen (t1K t0K Small Good ifp ifn)
open VG.Spec.Sha3 (bytesAt)

/-- After the samplers: the keys from `A`, `S` and `R`, so far. -/
structure KR (p : Params) (STK : Nat) (σ : State) (A : Nat → Poly) (S : Nat → IPoly) (R : BitVec 64)
    (np nj nr : Nat) (s : State) : Prop where
  kc : KC p STK σ s
  s4 : s.gpr .s4 = R
  good : Good p (xiOf σ) (p.k * p.ℓ) (p.ℓ + p.k) A S (R.setWidth 32)
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
    {o n : Nat} (h1 : o + n ≤ 1288 ∨ 1368 ≤ o) (h2 : o + n ≤ oP 0 ∨ oP (p.k * p.ℓ + p.ℓ + p.k) ≤ o)
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

theorem KR.keep {p : Params} (hF : PFacts p) {STK : Nat} {σ : State} {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64}
    {np nj nr : Nat} {s s' : State} (h : KR p STK σ A S R np nj nr s) {W : List (Nat × Nat × Nat)}
    (hk : Kept ((lay p STK σ).RL W) s s') (hc : KRChk p STK np nj nr W) : KR p STK σ A S R np nj nr s' := by
  have hL := h.kc.site.ok
  have hle : lenS p ≤ 2 ^ 64 := by rcases hF.eta with ⟨_, e⟩ | ⟨_, e⟩ <;> omega_using [e]
  have kb : ∀ {i o l : Nat}, sepAll [scrLen p, STK, 32, p.pkLen, p.skLen] (i, o, l) W = true → i ∈ kWb →
      l ≤ 2 ^ 64 → bytesAt s'.mem ((lay p STK σ).A i o) l = bytesAt s.mem ((lay p STK σ).A i o) l :=
    fun hs hi hl => bytes_keepW hL hk.frame hs hi hl
  exact ⟨h.kc.keep hk hc.kc, (hk.cs .s4 (by decide)).trans h.s4, h.good, h.small,
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
  refine WP.seq (WP.mono (copyS hs (sb := .s11) (so := oHX) (db := .s9) (dO := 0) (len := 32) ⟨by decide, by lsep hF⟩
    ⟨by decide, by lsep hF [hF.pk]⟩ (show ix Reg.s9 ∈ kWb by decide) (by decide) (by decide) (by decide) (by decide)
    (by lsep hF [hF.pk])) fun s₁ ⟨k₁, b₁⟩ => ?_)
  have h₁ := h.keep k₁ (by lsep hF [k1Chk, kcChk, hF.pk]) (fun e' he' => by lsep hF [hF.pk])
    (fun r' hr' => by lsep hF [hF.pk])
  refine WP.seq (WP.mono (copyS h₁.k1.kc.site (sb := .s11) (so := oHX) (db := .s8) (dO := 0) (len := 32)
    ⟨by decide, by lsep hF⟩ ⟨by decide, by lsep hF [hF.sk]⟩ (show ix Reg.s8 ∈ kWb by decide) (by decide) (by decide)
    (by decide) (by decide) (by lsep hF [hF.sk])) fun s₂ ⟨k₂, b₂⟩ => ?_)
  have h₂ := h₁.keep k₂ (by lsep hF [k1Chk, kcChk, hF.sk]) (fun e' he' => by lsep hF [hF.sk])
    (fun r' hr' => by lsep hF [hF.sk])
  refine WP.mono (copyS h₂.k1.kc.site (sb := .s11) (so := oHX + 96) (db := .s8) (dO := 32) (len := 32)
    ⟨by decide, by lsep hF⟩ ⟨by decide, by lsep hF [hF.sk]⟩ (show ix Reg.s8 ∈ kWb by decide) (by decide) (by decide)
    (by decide) (by decide) (by lsep hF [hF.sk])) fun s₃ ⟨k₃, b₃⟩ => ?_
  have h₃ := h₂.keep k₃ (by lsep hF [k1Chk, kcChk, hF.sk]) (fun e' he' => by lsep hF [hF.sk])
    (fun r' hr' => by lsep hF [hF.sk])
  have hL := hs.ok
  obtain ⟨A, S, hA, hS, hG⟩ := h₃.ex
  have e1 : ∀ {m : Mem}, bytesAt m ((lay p STK σ).A 0 oHX) 128 = hxOf p σ →
      bytesAt m ((lay p STK σ).A 0 oHX) 32 = rhoOf p σ := fun hx => by
    rw [rho_eq, ← hx, Proof.MlKem.bytesAt_take _ _ (show 32 ≤ 128 by decide)]
  refine ⟨A, S, s₃.gpr .s4, ⟨h₃.k1.kc, rfl, hG, fun r hr => (hS r hr).2, hA,
    fun i hi => (hS (p.ℓ + i) (by omega_using [hi])).1,
    fun j hj => by rw [ifn (Nat.not_lt_zero j)]; exact (hS j (by omega_using [hj])).1, ?_, ?_, ?_,
    fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩
  · rw [bytes_keepW hL k₃.frame (i := 3) (o := 0) (l := 32) (by lsep hF [hF.pk, hF.sk]) (by decide) (by decide),
      bytes_keepW hL k₂.frame (i := 3) (o := 0) (l := 32) (by lsep hF [hF.pk, hF.sk]) (by decide) (by decide)]
    exact b₁.trans (e1 h.k1.hx)
  · rw [bytes_keepW hL k₃.frame (i := 4) (o := 0) (l := 32) (by lsep hF [hF.sk]) (by decide) (by decide)]
    exact b₂.trans (e1 h₁.k1.hx)
  · show bytesAt s₃.mem (lpa (lay p STK σ) (.s8, 32)) 32 = _
    rw [b₃, kOf_eq, ← h₂.k1.hx, Proof.MlKem.bytesAt_slice _ _ (show 96 + 32 ≤ 128 by decide)]
    simp only [lpa, Lay.A, BitVec.add_assoc, ← BitVec.ofNat_add]
    rfl

/-- Two runs in every layout of key generation, from the taint analysis of
the pointers of the layout. -/
theorem ktaint4 {p : Params} {STK : Nat} {c : Prog isa} {hc : VG.Taint.Hint VG.RISCV64.taint.T}
    (h : (VG.RISCV64.taint.check (Taint.ofRegs [.s8, .s9, .s10, .s11]) c hc).isSome = true) :
    RelCT isa (KTwo p STK) c fun _ _ => True :=
  ktwo fun _ => taint4 (fun _ _ h => h) h

theorem copies_piece {p : Params} (hF : PFacts p) {STK : Nat} :
    KPiece p STK (fun σ s => KSamp p STK σ (p.k * p.ℓ) (p.ℓ + p.k) s) (KR0 p STK) copies :=
  ⟨fun _ _ _ h => copies_ok hF h,
    rel_of (ktaint4 (by taint_decide)) fun _ _ _ _ _ _ pub h₁ h₂ => kc_two pub h₁.k1.kc h₂.k1.kc⟩

end VG.Proof.MlDsa.RISCV64.KeyGen

end

end

/-! ### `MlDsa.RISCV64.KeyGen.RestPack`, which this module and modules that import it used -/

section

/-!
# ML-DSA key generation on RISC-V: `s₁ ‖ s₂` to `sk`, and `ŝ₁`

As on PPC64LE (`Proof/MlDsa/PPC64LE/KeyGen/Top.lean`): each entry of
`s₁ ‖ s₂`, `BitPack`ed to `sk` (`packS_piece`), then `ŝ₁[j] = NTT(s₁[j])` in
place (`nttS_piece`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.KeyGen

open VG VG.RISCV64 VG.Proof.MlKem.RISCV64
open VG.Impl.MlDsa.RISCV64.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt bitPack modPm q n)
open VG.Proof.MlDsa (polyAt coeffAt Reduced PolyIs)
open VG.Proof.MlDsa.KeyGen (Small ifp ifn)
open VG.Spec.Sha3 (bytesAt)

/-- A pointer, in a register of the layout, at an offset below `2³¹`. -/
theorem ptr_ok {r : Reg} (hr : baseReg r = true) {o : Nat} (h : o < 2 ^ 31 - 2048) : argOk (.ptr (r, o)) = true := by
  simp only [argOk, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hr, h⟩

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
theorem KR.sPoly {p : Params} {STK : Nat} {σ : State} {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64}
    {np nr : Nat} {s : State} (h : KR p STK σ A S R np 0 nr s) {r : Nat} (hr : r < p.ℓ + p.k) :
    PolyIs s.mem ((lay p STK σ).A 0 (oP (p.k * p.ℓ + r))) (toRq (S r)) := by
  by_cases hl : r < p.ℓ
  · have := h.s1 r hl; rwa [ifn (Nat.not_lt_zero r)] at this
  · have := h.s2 (r - p.ℓ) (by omega_arith); rwa [show p.ℓ + (r - p.ℓ) = r by omega_arith] at this

/-- The states after the copies, and the first `np` entries packed, `nj` in
the NTT domain and `nr` rows. -/
abbrev KRx (p : Params) (STK : Nat) (np nj nr : Nat) (σ s : State) : Prop := ∃ A S R, KR p STK σ A S R np nj nr s

section
variable {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : PFacts p) {STK : Nat} (hS : S ≤ STK)
include hP hF hS

/-! ## `BitPack` of `s₁ ‖ s₂` -/

omit hP hS in
theorem packS_m {σ : State} {r : Nat} (hr : r < p.ℓ + p.k) :
    BpOk (lay p STK σ) kWb (sP p r) p.η p.η (.s8, 128 + lenS p * r) (lenS p) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  rcases hF.eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;>
  exact ⟨⟨sc_ok (oP_lt (by omega_arith)), by lsep hF⟩, ⟨ptr_ok rfl (by rw [hlen]; omega_arith), by lsep hF [hF.sk, hlen]⟩,
    show ix Reg.s8 ∈ kWb by decide,
    by lsep hF [hF.sk, hlen], eta_params hF, lenS_eq p, by alsep⟩

theorem packS_ok {r : Nat} (hr : r < p.ℓ + p.k) {σ : State} {A : Nat → Poly} {S' : Nat → IPoly} {R : BitVec 64}
    {s : State} (h : KR p STK σ A S' R r 0 0 s) : WP isa (packS P p r) s (KR p STK σ A S' R (r + 1) 0 0) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hs := h.kc.site
  have hSp := h.sPoly hr
  unfold packS bitPackAt
  refine bp_ok hP.bitPack hs hS (packS_m hF hr) hSp.1 (small_coeff (eta_le hF) hSp (h.small r hr))
    fun s' k' hb => ?_
  have hle : 128 + lenS p * r + lenS p ≤ oT0 p := by
    simp only [oT0]; rw [Nat.add_assoc, ← Nat.mul_succ]; exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hr) _
  have hk' := h.keep hF k' ((KRChk.c4 (o := 128 + lenS p * r) (n := lenS p) hF (Nat.le_of_lt hr) (Nat.zero_le _)
    (by omega_arith) (.inr (Nat.le_refl _)) (.inl hle) (by rw [hF.sk]; omega_arith)).append (W₁ := [_])
    (KRChk.stk hF (Nat.le_of_lt hr) (Nat.zero_le _)))
  refine ⟨hk'.kc, hk'.s4, hk'.good, hk'.small, hk'.aS, hk'.s2, hk'.s1, hk'.pk0, hk'.sk0, hk'.sk1,
    fun r' hr' => ?_, hk'.rows⟩
  rcases (by omega_arith : r' < r ∨ r' = r) with hr' | rfl
  · exact hk'.packs r' hr'
  · show bytesAt s'.mem (lpa (lay p STK σ) (.s8, 128 + lenS p * r')) (lenS p) = _
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
  exact bp_tr hP.bitPack hS (packS_m hF hr) fun x y ⟨T, rx, ry, ⟨x', hx, sx⟩, ⟨y', hy, sy⟩⟩ =>
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
  exact ⟨⟨sc_ok (oP_lt (by omega_arith)), by lsep hF⟩, ⟨sc_ok (by decide), by lsep hF⟩, by lsep hF⟩

theorem nttS_ok {j : Nat} (hj : j < p.ℓ) {σ : State} {A : Nat → Poly} {S' : Nat → IPoly} {R : BitVec 64}
    {s : State} (h : KR p STK σ A S' R (p.ℓ + p.k) j 0 s) :
    WP isa (nttS P p j) s (KR p STK σ A S' R (p.ℓ + p.k) (j + 1) 0) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hs := h.kc.site
  have hSj := h.s1 j hj
  rw [ifn (Nat.lt_irrefl j)] at hSj
  obtain ⟨m1, m2, m3⟩ := nttS_m hF (STK := STK) (σ := σ) hj
  unfold nttS nttAt
  refine ip_ok (t := ntt) hP.ntt hs hS ⟨m1, m2, show ix Reg.s11 ∈ kWb by decide, show ix Reg.s11 ∈ kWb by decide, m3, by alsep, by alsep⟩
    hSj.1 fun s' k' hb => ?_
  have hL := hs.ok
  have hle : lenS p ≤ 2 ^ 64 := by rcases hF.eta with ⟨_, e⟩ | ⟨_, e⟩ <;> omega_arith
  have hpk : ∀ r < p.ℓ + p.k, sepAll [scrLen p, STK, 32, p.pkLen, p.skLen] (4, 128 + lenS p * r, lenS p)
      [tri (sP p j) 1024, tri (sc oSS) 1024, (1, 0, STK)] = true := fun r hr => by
    rcases hF.eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;> lsep hF [hF.sk, hlen]
  refine ⟨h.kc.keep k' (by lsep hF [kcChk]), (k'.cs .s4 (by decide)).trans h.s4, h.good, h.small,
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
  exact ip_tr (t := ntt) hP.ntt hS ⟨m1, m2, show ix Reg.s11 ∈ kWb by decide, show ix Reg.s11 ∈ kWb by decide, m3, by alsep, by alsep⟩
    fun x y ⟨T, rx, ry⟩ => ⟨T.1, T.2.1, T.2.2, rx, ry⟩

theorem nttS_piece {j : Nat} (hj : j < p.ℓ) :
    KPiece p STK (KRx p STK (p.ℓ + p.k) j 0) (KRx p STK (p.ℓ + p.k) (j + 1) 0) (nttS P p j) :=
  ⟨fun _ _ _ ⟨A, S', R, h⟩ => WP.mono (nttS_ok hP hF hS hj h) fun _ h => ⟨A, S', R, h⟩,
    rel_of (RelCT.exists_ fun σ => nttS_two hP hF hS hj σ) fun σ₁ _ _ _ _ _ pub ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ =>
      ⟨σ₁, kc_twoL pub h₁.kc h₂.kc, (h₁.s1 j hj).1, by rw [lay_pub pub]; exact (h₂.s1 j hj).1⟩⟩

end

end VG.Proof.MlDsa.RISCV64.KeyGen

end

end

/-!
# ML-DSA key generation on RISC-V: the rows of `t`

As on PPC64LE (`Proof/MlDsa/PPC64LE/KeyGen/Top.lean`): row `i` of `t`:
the sum of the products `Â[i, j] ŝ₁[j]` in `t` (`rowMul_ok`,
`rowMulAdd_ok`), `NTT⁻¹` of it plus `s₂[i]` (`rowInv_ok`, `rowAdd_ok`), then
`Power2Round` (`rowP2r_ok`) and `t₁[i]` packed to `pk` and `t₀[i]` to `sk`
(`rowSbp_ok`, `rowBp_ok`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.KeyGen

open VG VG.RISCV64 VG.Proof.MlKem.RISCV64
open VG.Impl.MlDsa.RISCV64.KeyGen
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

theorem KR.polyA {p : Params} {STK : Nat} {σ : State} {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64}
    {np nj nr : Nat} {s : State} (h : KR p STK σ A S R np nj nr s) {i j : Nat} (hi : i < p.k) (hj : j < p.ℓ) :
    PolyIs s.mem ((lay p STK σ).A 0 (oP (p.ℓ * i + j))) (A (p.ℓ * i + j)) := h.aS _ (idx_lt hi hj)

theorem KR.polyS {p : Params} {STK : Nat} {σ : State} {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64}
    {np nr : Nat} {s : State} (h : KR p STK σ A S R np p.ℓ nr s) {j : Nat} (hj : j < p.ℓ) :
    PolyIs s.mem ((lay p STK σ).A 0 (oP (p.k * p.ℓ + j))) (ntt (toRq (S j))) := by
  have := h.s1 j hj; rwa [ifp hj] at this

theorem modPm_t0 (t : Poly) :
    ((t.map fun c => ofInt (power2Round c).2).map fun c => modPm c.val q) = t.map fun c => (power2Round c).2 := by
  rw [Vector.map_map]
  refine Vector.map_congr_left fun c _ => ?_
  have := Proof.MlDsa.KeyGen.power2Round_snd c
  exact Proof.MlDsa.KeyGen.modPm_ofInt (by omega_arith) (by omega_arith)

theorem t0_coeff {m : Mem} {a : Addr} {t : Poly} (h : PolyIs m a (t.map fun c => ofInt (power2Round c).2)) :
    ∀ i < n, -((4095 : Nat) : Int) ≤ modPm (coeffAt m a i).toNat q ∧ modPm (coeffAt m a i).toNat q ≤ ((4096 : Nat) : Int) :=
  fun j hj => by
    rw [coeff_val h hj]
    simp only [Vector.getElem_map]
    have := Proof.MlDsa.KeyGen.power2Round_snd (t[j]'hj)
    rw [Proof.MlDsa.KeyGen.modPm_ofInt (by omega_arith) (by omega_arith)]
    omega_arith

theorem t1_bound {m : Mem} {a : Addr} {p : Params} {A : Nat → Poly} {S : Nat → IPoly} {i : Nat}
    (h1 : NatPolyIs m a (t1K p A S i)) : ∀ j < n, (coeffAt m a j).toNat ≤ 1023 := fun j hj => by
  rw [show (coeffAt m a j).toNat = (t1K p A S i)[j]'hj from by
    rw [← h1]; simp only [natPolyAt, Vector.getElem_ofFn]]
  simp only [t1K, Vector.getElem_map]
  have := Proof.MlDsa.KeyGen.power2Round_fst ((tK p A S i)[j]'hj)
  omega_arith

/-! ## The checks of the writes of a row, once each -/

theorem chk_poly {p : Params} (hF : PFacts p) {STK i : Nat} (hi : i < p.k) {j : Nat} (hj : j < 3) :
    KRChk p STK (p.ℓ + p.k) p.ℓ i [(0, oP (p.k * p.ℓ + p.ℓ + p.k + j), 1024)] := by
  have := hF.k; have := hF.l; have := hF.kl; have := hF.scr
  exact KRChk.c0 hF (by omega_arith) (by omega_arith) (.inr (by simp only [oP]; omega_arith))
    (.inr (by simp only [oP]; omega_arith)) (by simp only [oP]; omega_arith)

theorem chk_t {p : Params} (hF : PFacts p) {STK i : Nat} (hi : i < p.k) :
    KRChk p STK (p.ℓ + p.k) p.ℓ i [(0, oP (p.k * p.ℓ + p.ℓ + p.k), 1024), (1, 0, STK)] := by
  have := (chk_poly hF (STK := STK) hi (j := 0) (by decide)).append (W₂ := [_]) (KRChk.stk hF (by omega_arith) (by omega_arith))
  rwa [Nat.add_zero] at this

theorem chk_inv {p : Params} (hF : PFacts p) {STK i : Nat} (hi : i < p.k) :
    KRChk p STK (p.ℓ + p.k) p.ℓ i [(0, oP (p.k * p.ℓ + p.ℓ + p.k), 1024), (0, oSS, 1024), (1, 0, STK)] := by
  have := hF.k; have := hF.l; have := hF.kl; have := hF.scr
  have := (chk_poly hF (STK := STK) hi (j := 0) (by decide)).append (W₁ := [_])
    ((KRChk.c0 (o := oSS) (n := 1024) hF (by omega_arith) (by omega_arith) (.inr (by decide)) (.inl (by decide))
      (by simp only [oSS]; omega_arith)).append (W₁ := [_]) (KRChk.stk hF (by omega_arith) (by omega_arith)))
  rwa [Nat.add_zero] at this

theorem chk_p2r {p : Params} (hF : PFacts p) {STK i : Nat} (hi : i < p.k) :
    KRChk p STK (p.ℓ + p.k) p.ℓ i [(0, oP (p.k * p.ℓ + p.ℓ + p.k + 1), 1024),
      (0, oP (p.k * p.ℓ + p.ℓ + p.k + 2), 1024), (1, 0, STK)] :=
  (chk_poly hF hi (j := 1) (by decide)).append (W₁ := [_])
    ((chk_poly hF hi (j := 2) (by decide)).append (W₁ := [_]) (KRChk.stk hF (by omega_arith) (by omega_arith)))

theorem chk_sbp {p : Params} (hF : PFacts p) {STK i : Nat} (hi : i < p.k) :
    KRChk p STK (p.ℓ + p.k) p.ℓ i [(3, 32 + 320 * i, 320), (1, 0, STK)] :=
  (KRChk.c3 hF (Nat.le_refl _) (Nat.le_of_lt hi) (Nat.le_refl _) (by rw [hF.pk]; omega_arith)).append (W₁ := [_])
    (KRChk.stk hF (Nat.le_refl _) (Nat.le_of_lt hi))

theorem chk_bp {p : Params} (hF : PFacts p) {STK i : Nat} (hi : i < p.k) :
    KRChk p STK (p.ℓ + p.k) p.ℓ i [(4, oT0 p + 416 * i, 416), (1, 0, STK)] := by
  have := hF.k; have := hF.l
  exact (KRChk.c4 hF (Nat.le_refl _) (Nat.le_of_lt hi) (by simp only [oT0]; omega_arith) (.inr (by simp only [oT0]; omega_arith))
    (.inr (Nat.le_refl _)) (by rw [hF.sk]; omega_arith)).append (W₁ := [_]) (KRChk.stk hF (Nat.le_refl _) (Nat.le_of_lt hi))

section
variable {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : PFacts p) {STK : Nat} (hS : S ≤ STK)
  {i : Nat} (hi : i < p.k)
include hP hF hS hi

/-! ## The calls, one by one -/

/-- `t = Â[i, 0] ŝ₁[0]`. -/
theorem rowMul_ok {σ : State} {A : Nat → Poly} {S' : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : KR p STK σ A S' R (p.ℓ + p.k) p.ℓ i s) :
    WP isa (mulAt P (tP p) (aP (p.ℓ * i)) (sP p 0)) s fun s' =>
      KR p STK σ A S' R (p.ℓ + p.k) p.ℓ i s' ∧ tIs p STK (fun A S => dotK p A S i 1) σ A S' s' := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hx0 := idx_lt (j := 0) hi (by omega_arith)
  have hA := h.polyA hi (j := 0) (by omega_arith)
  rw [Nat.add_zero] at hx0 hA
  have hS0 := h.polyS (j := 0) (by omega_arith)
  rw [Nat.add_zero] at hS0
  refine mul_ok hP.mul h.kc.site hS (h := tP p) (f := aP (p.ℓ * i)) (g := sP p 0)
    ⟨⟨sc_ok (oP_lt (by omega_arith)), by lsep hF⟩, ⟨sc_ok (oP_lt (by omega_arith)), by lsep hF⟩, ⟨sc_ok (oP_lt (by omega_arith)), by lsep hF⟩, show ix Reg.s11 ∈ kWb by decide,
      by lsep hF, by lsep hF, by alsep, by alsep, by alsep⟩ hA.1 hS0.1 fun s' k' hb => ⟨h.keep hF k' (chk_t hF hi), ?_⟩
  show PolyIs s'.mem (lpa (lay p STK σ) (tP p)) _
  dsimp only
  rw [Proof.MlDsa.KeyGen.dotK_one, ← hA.2, ← hS0.2]
  exact hb

/-- `t = t + Â[i, j] ŝ₁[j]`. -/
theorem rowMulAdd_ok {j : Nat} (hj : j < p.ℓ) {σ : State} {A : Nat → Poly} {S' : Nat → IPoly} {R : BitVec 64}
    {s : State} (h : KR p STK σ A S' R (p.ℓ + p.k) p.ℓ i s) (ht : tIs p STK (fun A S => dotK p A S i j) σ A S' s) :
    WP isa (mulAddAt P (tP p) (aP (p.ℓ * i + j)) (sP p j)) s fun s' =>
      KR p STK σ A S' R (p.ℓ + p.k) p.ℓ i s' ∧ tIs p STK (fun A S => dotK p A S i (j + 1)) σ A S' s' := by
  dsimp only [tIs] at ht
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hx0 := idx_lt hi hj
  have hA := h.polyA hi hj
  have hSj := h.polyS hj
  refine mulAdd_ok hP.mulAdd h.kc.site hS (h := tP p) (f := aP (p.ℓ * i + j)) (g := sP p j)
    ⟨⟨sc_ok (oP_lt (by omega_arith)), by lsep hF⟩, ⟨sc_ok (oP_lt (by omega_arith)), by lsep hF⟩, ⟨sc_ok (oP_lt (by omega_arith)), by lsep hF⟩, show ix Reg.s11 ∈ kWb by decide,
      by lsep hF, by lsep hF, by alsep, by alsep, by alsep⟩ ht.1 hA.1 hSj.1 fun s' k' hb => ⟨h.keep hF k' (chk_t hF hi), ?_⟩
  show PolyIs s'.mem (lpa (lay p STK σ) (tP p)) _
  dsimp only
  rw [Proof.MlDsa.KeyGen.dotK_succ, ← hA.2, ← hSj.2, ← ht.2]
  exact hb

omit hP hS hi in
theorem tP_m {σ : State} : PtrIn (lay p STK σ) (tP p) 1024 ∧ PtrIn (lay p STK σ) (sc oSS) 1024 ∧
    sepB (lay p STK σ).sizes (tri (tP p) 1024) (tri (sc oSS) 1024) = true := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  exact ⟨⟨sc_ok (oP_lt (by omega_arith)), by lsep hF⟩, ⟨sc_ok (by decide), by lsep hF⟩, by lsep hF⟩

/-- `t = NTT⁻¹(t)`. -/
theorem rowInv_ok {σ : State} {A : Nat → Poly} {S' : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : KR p STK σ A S' R (p.ℓ + p.k) p.ℓ i s) (ht : tIs p STK (fun A S => dotK p A S i p.ℓ) σ A S' s) :
    WP isa (invNttAt P (tP p)) s fun s' =>
      KR p STK σ A S' R (p.ℓ + p.k) p.ℓ i s' ∧ tIs p STK (fun A S => nttInv (dotK p A S i p.ℓ)) σ A S' s' := by
  dsimp only [tIs] at ht
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  obtain ⟨m1, m2, m3⟩ := tP_m hF (σ := σ)
  unfold invNttAt
  refine ip_ok (t := nttInv) hP.invNtt h.kc.site hS ⟨m1, m2, show ix Reg.s11 ∈ kWb by decide,
    show ix Reg.s11 ∈ kWb by decide, m3, by alsep, by alsep⟩ ht.1 fun s' k' hb => ⟨h.keep hF k' (chk_inv hF hi), ?_⟩
  show PolyIs s'.mem (lpa (lay p STK σ) (tP p)) _
  dsimp only
  rw [← ht.2]
  exact hb

/-- `t = t + s₂[i]`. -/
theorem rowAdd_ok {σ : State} {A : Nat → Poly} {S' : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : KR p STK σ A S' R (p.ℓ + p.k) p.ℓ i s)
    (ht : tIs p STK (fun A S => nttInv (dotK p A S i p.ℓ)) σ A S' s) :
    WP isa (addAt P (tP p) (sP p (p.ℓ + i))) s fun s' =>
      KR p STK σ A S' R (p.ℓ + p.k) p.ℓ i s' ∧ tIs p STK (fun A S => tK p A S i) σ A S' s' := by
  dsimp only [tIs] at ht
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hS2 := h.s2 i hi
  refine add_ok hP.add h.kc.site hS (f := tP p) (g := sP p (p.ℓ + i))
    ⟨⟨sc_ok (oP_lt (by omega_arith)), by lsep hF⟩, ⟨sc_ok (oP_lt (by omega_arith)), by lsep hF⟩, show ix Reg.s11 ∈ kWb by decide, by lsep hF, by alsep, by alsep⟩ ht.1 hS2.1
    fun s' k' hb => ⟨h.keep hF k' (chk_t hF hi), ?_⟩
  show PolyIs s'.mem (lpa (lay p STK σ) (tP p)) _
  dsimp only
  rw [Proof.MlDsa.KeyGen.tK, ← hS2.2, ← ht.2]
  exact hb

omit hP hS hi in
theorem p2r_m {σ : State} : P2rOk (lay p STK σ) kWb (tP p) (t1P p) (t0P p) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  exact ⟨⟨sc_ok (oP_lt (by omega_arith)), by lsep hF⟩, ⟨sc_ok (oP_lt (by omega_arith)), by lsep hF⟩, ⟨sc_ok (oP_lt (by omega_arith)), by lsep hF⟩, show ix Reg.s11 ∈ kWb by decide,
    show ix Reg.s11 ∈ kWb by decide, by lsep hF, by lsep hF, by lsep hF, by alsep, by alsep, by alsep⟩

/-- After `Power2Round`. -/
abbrev p2rIs (p : Params) (STK i : Nat) (σ : State) (A : Nat → Poly) (S : Nat → IPoly) (s : State) : Prop :=
  NatPolyIs s.mem ((lay p STK σ).A 0 (oT1 p)) (t1K p A S i) ∧
    PolyIs s.mem ((lay p STK σ).A 0 (oT0' p)) ((tK p A S i).map fun c => ofInt (power2Round c).2)

/-- `Power2Round` of `t`. -/
theorem rowP2r_ok {σ : State} {A : Nat → Poly} {S' : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : KR p STK σ A S' R (p.ℓ + p.k) p.ℓ i s) (ht : tIs p STK (fun A S => tK p A S i) σ A S' s) :
    WP isa (power2RoundAt P (tP p) (t1P p) (t0P p)) s fun s' =>
      KR p STK σ A S' R (p.ℓ + p.k) p.ℓ i s' ∧ p2rIs p STK i σ A S' s' := by
  dsimp only [tIs] at ht
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  refine p2r_ok hP.power2Round h.kc.site hS (p2r_m hF) ht.1 fun s' k' h1 h0 =>
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
theorem sbp_m {σ : State} : SbpOk (lay p STK σ) kWb (t1P p) 1023 (.s9, 32 + 320 * i) 320 := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  exact ⟨⟨sc_ok (oP_lt (by omega_arith)), by lsep hF⟩, ⟨ptr_ok rfl (by omega_arith), by lsep hF [hF.pk]⟩,
    show ix Reg.s9 ∈ kWb by decide, by lsep hF [hF.pk],
    by decide, by decide, by alsep⟩

/-- `t₁[i]` to `pk`. -/
theorem rowSbp_ok {σ : State} {A : Nat → Poly} {S' : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : KR p STK σ A S' R (p.ℓ + p.k) p.ℓ i s) (h1 : p2rIs p STK i σ A S' s) :
    WP isa (simpleBitPackAt P (t1P p) 1023 (.s9, 32 + 320 * i) 320) s fun s' =>
      KR p STK σ A S' R (p.ℓ + p.k) p.ℓ i s' ∧ sbpIs p STK i σ A S' s' := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  refine sbp_ok hP.simpleBitPack h.kc.site hS (sbp_m hF hi) (t1_bound h1.1) fun s' k' hb =>
    ⟨h.keep hF k' (chk_sbp hF hi), polyIs_keepW h.kc.site.ok k'.frame (by lsep hF [hF.pk]) (by decide) rfl h1.2, ?_⟩
  show bytesAt s'.mem (lpa (lay p STK σ) (.s9, 32 + 320 * i)) 320 = _
  rw [hb]
  exact congrArg (simpleBitPack · 1023) h1.1

omit hP hS in
theorem bp_m {σ : State} : BpOk (lay p STK σ) kWb (t0P p) 4095 4096 (.s8, oT0 p + 416 * i) 416 := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  rcases hF.eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;>
  exact ⟨⟨sc_ok (oP_lt (by omega_arith)), by lsep hF⟩, ⟨ptr_ok rfl (by simp only [oT0, hlen]; omega_arith),
    by lsep hF [hF.sk, hlen]⟩, show ix Reg.s8 ∈ kWb by decide,
    by lsep hF [hF.sk, hlen], by decide, by decide, by alsep⟩

/-- `t₀[i]` to `sk`. -/
theorem rowBp_ok {σ : State} {A : Nat → Poly} {S' : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : KR p STK σ A S' R (p.ℓ + p.k) p.ℓ i s) (h0 : sbpIs p STK i σ A S' s) :
    WP isa (bitPackAt P (t0P p) 4095 4096 (.s8, oT0 p + 416 * i) 416) s
      (KR p STK σ A S' R (p.ℓ + p.k) p.ℓ (i + 1)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  unfold bitPackAt
  refine bp_ok hP.bitPack h.kc.site hS (bp_m hF hi) h0.1.1 (t0_coeff h0.1) fun s' k' hb => ?_
  have hk' := h.keep hF k' (chk_bp hF hi)
  refine ⟨hk'.kc, hk'.s4, hk'.good, hk'.small, hk'.aS, hk'.s2, hk'.s1, hk'.pk0, hk'.sk0, hk'.sk1, hk'.packs,
    fun i' hi' => ?_⟩
  rcases (by omega_arith : i' < i ∨ i' = i) with hi' | rfl
  · exact hk'.rows i' hi'
  · refine ⟨?_, ?_⟩
    · rw [bytes_keepW h.kc.site.ok k'.frame (i := 3) (o := 32 + 320 * i') (l := 320)
        (by rcases hF.eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;> lsep hF [hF.pk, hF.sk, hlen]) (by decide) (by decide)]
      exact h0.2
    · show bytesAt s'.mem (lpa (lay p STK σ) (.s8, oT0 p + 416 * i')) 416 = _
      rw [hb]
      show bitPack ((polyAt s.mem ((lay p STK σ).A 0 (oT0' p))).map _) _ _ = _
      rw [h0.1.2, modPm_t0]
      rfl

/-! ## The pieces of a row -/

theorem rowMul_piece :
    KPiece p STK (KRx p STK (p.ℓ + p.k) p.ℓ i) (RowI p STK i (tIs p STK fun A S => dotK p A S i 1))
      (mulAt P (tP p) (aP (p.ℓ * i)) (sP p 0)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hx0 := idx_lt (j := 0) hi (by omega_arith)
  rw [Nat.add_zero] at hx0
  refine ⟨fun _ _ _ ⟨A, S', R, h⟩ => WP.mono (rowMul_ok hP hF hS hi h) fun _ h => ⟨A, S', R, h⟩,
    rel_of (Q := fun x y => ∃ σ, Two (lay p STK σ) kWb STK x y ∧
      (Reduced x.mem ((lay p STK σ).A 0 (oP (p.ℓ * i))) ∧ Reduced x.mem ((lay p STK σ).A 0 (oP (p.k * p.ℓ)))) ∧
      (Reduced y.mem ((lay p STK σ).A 0 (oP (p.ℓ * i))) ∧ Reduced y.mem ((lay p STK σ).A 0 (oP (p.k * p.ℓ)))))
      (RelCT.exists_ fun σ => mul_tr hP.mul hS (h := tP p) (f := aP (p.ℓ * i)) (g := sP p 0)
        ⟨⟨sc_ok (oP_lt (by omega_arith)), by lsep hF⟩, ⟨sc_ok (oP_lt (by omega_arith)), by lsep hF⟩, ⟨sc_ok (oP_lt (by omega_arith)), by lsep hF⟩, show ix Reg.s11 ∈ kWb by decide,
          by lsep hF, by lsep hF, by alsep, by alsep, by alsep⟩ fun x y ⟨T, ⟨a, b⟩, ⟨c, d⟩⟩ => ⟨T.1, T.2.1, T.2.2, a, b, c, d⟩) ?_⟩
  intro σ₁ _ _ _ _ _ pub ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩
  have a₁ := h₁.polyA hi (j := 0) (by omega_arith); have a₂ := h₂.polyA hi (j := 0) (by omega_arith)
  have s₁ := h₁.polyS (j := 0) (by omega_arith); have s₂ := h₂.polyS (j := 0) (by omega_arith)
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
      (RelCT.exists_ fun σ => mulAdd_tr hP.mulAdd hS (h := tP p) (f := aP (p.ℓ * i + j)) (g := sP p j)
        ⟨⟨sc_ok (oP_lt (by omega_arith)), by lsep hF⟩, ⟨sc_ok (oP_lt (by omega_arith)), by lsep hF⟩, ⟨sc_ok (oP_lt (by omega_arith)), by lsep hF⟩, show ix Reg.s11 ∈ kWb by decide,
          by lsep hF, by lsep hF, by alsep, by alsep, by alsep⟩ fun x y ⟨T, ⟨a, b, c⟩, ⟨d, e, f⟩⟩ => ⟨T.1, T.2.1, T.2.2, a, b, c, d, e, f⟩) ?_⟩
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
        exact ip_tr (t := nttInv) hP.invNtt hS ⟨m1, m2, show ix Reg.s11 ∈ kWb by decide,
          show ix Reg.s11 ∈ kWb by decide, m3, by alsep, by alsep⟩ fun x y ⟨T, a, b⟩ => ⟨T.1, T.2.1, T.2.2, a, b⟩) ?_⟩
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
      (RelCT.exists_ fun σ => add_tr hP.add hS (f := tP p) (g := sP p (p.ℓ + i))
        ⟨⟨sc_ok (oP_lt (by omega_arith)), by lsep hF⟩, ⟨sc_ok (oP_lt (by omega_arith)), by lsep hF⟩, show ix Reg.s11 ∈ kWb by decide, by lsep hF, by alsep, by alsep⟩
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
      (RelCT.exists_ fun σ => p2r_tr hP.power2Round hS (p2r_m hF)
        fun x y ⟨T, a, b⟩ => ⟨T.1, T.2.1, T.2.2, a, b⟩) ?_⟩
  intro σ₁ _ _ _ _ _ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩
  have t₂' := t₂.1
  rw [← lay_pub pub] at t₂'
  exact ⟨σ₁, kc_twoL pub h₁.kc h₂.kc, t₁.1, t₂'⟩

theorem rowSbp_piece :
    KPiece p STK (RowI p STK i (p2rIs p STK i)) (RowI p STK i (sbpIs p STK i))
      (simpleBitPackAt P (t1P p) 1023 (.s9, 32 + 320 * i) 320) := by
  refine ⟨fun _ _ _ ⟨A, S', R, h, h1⟩ => WP.mono (rowSbp_ok hP hF hS hi h h1) fun _ h => ⟨A, S', R, h⟩,
    rel_of (Q := fun x y => ∃ σ, Two (lay p STK σ) kWb STK x y ∧
      (∀ j < n, (coeffAt x.mem ((lay p STK σ).A 0 (oT1 p)) j).toNat ≤ 1023) ∧
      (∀ j < n, (coeffAt y.mem ((lay p STK σ).A 0 (oT1 p)) j).toNat ≤ 1023))
      (RelCT.exists_ fun σ => sbp_tr hP.simpleBitPack hS (sbp_m hF hi)
        fun x y ⟨T, a, b⟩ => ⟨T.1, T.2.1, T.2.2, a, b⟩) ?_⟩
  intro σ₁ _ _ _ _ _ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩
  have t₂' := t1_bound t₂.1
  rw [← lay_pub pub] at t₂'
  exact ⟨σ₁, kc_twoL pub h₁.kc h₂.kc, t1_bound t₁.1, t₂'⟩

theorem rowBp_piece :
    KPiece p STK (RowI p STK i (sbpIs p STK i)) (KRx p STK (p.ℓ + p.k) p.ℓ (i + 1))
      (bitPackAt P (t0P p) 4095 4096 (.s8, oT0 p + 416 * i) 416) := by
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
        exact bp_tr hP.bitPack hS (bp_m hF hi)
          fun x y ⟨T, ⟨a, b⟩, ⟨c, d⟩⟩ => ⟨T.1, T.2.1, T.2.2, a, c, b, d⟩) ?_⟩
  intro σ₁ _ _ _ _ _ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩
  have r₂ := t₂.1.1; have c₂ := t0_coeff t₂.1
  rw [← lay_pub pub] at r₂ c₂
  exact ⟨σ₁, kc_twoL pub h₁.kc h₂.kc, ⟨t₁.1.1, t0_coeff t₁.1⟩, ⟨r₂, c₂⟩⟩

end

end VG.Proof.MlDsa.RISCV64.KeyGen

end

end

/-!
# ML-DSA key generation on RISC-V: `vg_mldsa44_keygen`, `vg_mldsa65_keygen`, `vg_mldsa87_keygen`

As on PPC64LE (`Proof/MlDsa/PPC64LE/KeyGen/Top.lean`): the rows
(`row_piece`), the keys in memory (`pk_bytes`, `sk_bytes`), `tr = H(pk, 64)`
(`trHash_piece`), and the whole function, piece by piece, for any parameter
set of Table 1 and any verified implementations of the primitives
(`keyGen_piece`, `keyGen_verified`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.KeyGen

open VG VG.RISCV64 VG.Proof.MlKem.RISCV64
open VG.Impl.MlDsa.RISCV64.KeyGen
open VG.Impl.MlKem.RISCV64 (topEnd)
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt bitPack simpleBitPack keyGenInternal)
open VG.Proof.MlDsa (polyAt Reduced PolyIs)
open VG.Proof.MlDsa.KeyGen (dotK tK t1K t0K pkK skK Good)
open VG.Spec.Sha3 (bytesAt)

/-! ## A row -/

theorem row_piece {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : PFacts p) {STK : Nat}
    (hS : S ≤ STK) {i : Nat} (hi : i < p.k) :
    KPiece p STK (KRx p STK (p.ℓ + p.k) p.ℓ i) (KRx p STK (p.ℓ + p.k) p.ℓ (i + 1)) (row P p i) := by
  have hl := hF.l
  unfold row
  refine (rowMul_piece hP hF hS hi).seq (Piece.seq ?_ ((rowInv_piece hP hF hS hi).seq ((rowAdd_piece hP hF hS hi).seq
    ((rowP2r_piece hP hF hS hi).seq ((rowSbp_piece hP hF hS hi).seq (rowBp_piece hP hF hS hi))))))
  refine Piece.mono (Piece.seqR (I := fun j => RowI p STK i (tIs p STK fun A S => dotK p A S i j)) (p.ℓ - 1) 1
    fun j h1 h2 => rowMulAdd_piece hP hF hS hi (by omega_arith)) (fun _ _ _ h => h) fun _ _ _ h => ?_
  rwa [show 1 + (p.ℓ - 1) = p.ℓ by omega_arith] at h

/-! ## The keys in memory -/

theorem flatMap_congr_mem {α β : Type} {f g : α → List β} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) →
    l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h x (List.mem_cons_self ..),
      flatMap_congr_mem fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem t1Max_eq : Spec.MlDsa.t1Max = 1023 := by decide

theorem pk_bytes {p : Params} (hF : PFacts p) {STK : Nat} {σ : State} {A : Nat → Poly} {S : Nat → IPoly}
    {R : BitVec 64} {np nj : Nat} {s : State} (h : KR p STK σ A S R np nj p.k s) :
    bytesAt s.mem ((lay p STK σ).A 3 0) p.pkLen = pkK p A S (rhoOf p σ) := by
  have hp0 := h.pk0
  have hr : ∀ i ∈ List.range p.k, bytesAt s.mem ((lay p STK σ).ptr 3 + BitVec.ofNat 64 (32 + 320 * i)) 320 =
      simpleBitPack (t1K p A S i) 1023 := fun i hi => (h.rows i (List.mem_range.mp hi)).1
  simp only [Lay.A, BitVec.add_zero] at hp0 ⊢
  rw [hF.pk, Proof.MlKem.bytesAt_add, hp0, show (lay p STK σ).ptr 3 + BitVec.ofNat 64 32 =
      (lay p STK σ).ptr 3 + BitVec.ofNat 64 32 from rfl,
    Proof.MlDsa.KeyGen.bytesAt_pieces s.mem _ 32 320 p.k, pkK, t1Max_eq, flatMap_congr_mem hr]

theorem sk_bytes {p : Params} (hF : PFacts p) {STK : Nat} {σ : State} {A : Nat → Poly} {S : Nat → IPoly}
    {R : BitVec 64} {nj : Nat} {s : State} (h : KR p STK σ A S R (p.ℓ + p.k) nj p.k s)
    (htr : bytesAt s.mem ((lay p STK σ).A 4 64) 64 = Spec.MlDsa.H (pkK p A S (rhoOf p σ)) 64) :
    bytesAt s.mem ((lay p STK σ).A 4 0) p.skLen = skK p A S (rhoOf p σ) (kOf p σ) := by
  have h0 := h.sk0
  have h1 := h.sk1
  simp only [Lay.A, BitVec.add_zero] at h0 h1 htr ⊢
  have h2 : bytesAt s.mem ((lay p STK σ).ptr 4 + BitVec.ofNat 64 (32 + 32)) 64 =
    Spec.MlDsa.H (pkK p A S (rhoOf p σ)) 64 := htr
  have hp : ∀ r ∈ List.range (p.ℓ + p.k), bytesAt s.mem ((lay p STK σ).ptr 4 +
      BitVec.ofNat 64 (32 + 32 + 64 + lenS p * r)) (lenS p) = bitPack (S r) p.η p.η := fun r hr =>
    h.packs r (List.mem_range.mp hr)
  have hr : ∀ i ∈ List.range p.k, bytesAt s.mem ((lay p STK σ).ptr 4 +
      BitVec.ofNat 64 (oT0 p + 416 * i)) 416 = bitPack (t0K p A S i) 4095 4096 := fun i hi =>
    (h.rows i (List.mem_range.mp hi)).2
  rw [hF.sk, oT0, show 128 = 32 + 32 + 64 from rfl, Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add,
    Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add, h0, h1, h2,
    Proof.MlDsa.KeyGen.bytesAt_pieces s.mem _ (32 + 32 + 64) (lenS p) (p.ℓ + p.k),
    ← oT0, Proof.MlDsa.KeyGen.bytesAt_pieces s.mem _ (oT0 p) 416 p.k, skK, flatMap_congr_mem hp,
    flatMap_congr_mem hr]
  rfl

/-! ## `tr = H(pk, 64)` -/

/-- At the end: the keys, but for the return. -/
abbrev KFin (p : Params) (STK : Nat) (σ s : State) : Prop :=
  ∃ A S R, KR p STK σ A S R (p.ℓ + p.k) p.ℓ p.k s ∧
    bytesAt s.mem ((lay p STK σ).A 4 64) 64 = Spec.MlDsa.H (pkK p A S (rhoOf p σ)) 64

theorem trPieces {p : Params} (hF : PFacts p) {STK : Nat} {σ s : State} (hs : Site (lay p STK σ) kWb STK s) :
    (∀ pc ∈ ([⟨.s9, 0, 1024⟩, ⟨.s9, 1024, p.pkLen - 1024⟩] : List Impl.MlKem.RISCV64.Piece),
      PieceOk (hashLay (lay p STK σ) s fun _ => true) ix s false pc) ∧
    PieceOk (hashLay (lay p STK σ) s fun _ => true) ix s true (⟨.s8, 64, 64⟩ : Impl.MlKem.RISCV64.Piece) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hpk := hF.lens
  refine ⟨fun pc hpc => ?_, pieceS hs rfl (by decide) (by decide) (by decide)
    (by rcases hF.eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;> lsep hF [hashLay, Lay.size, hF.sk, hlen, ite_true]) (.inr rfl)
    fun _ => by decide⟩
  have hp := hF.pk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpc
  rcases hpc with rfl | rfl
  · exact pieceS hs rfl (show (0 : Nat) < 32768 by decide) (by decide) (by decide)
      (by lsep hF [hashLay, Lay.size, hF.pk, ite_true]) (.inr rfl) fun h => absurd h (by decide)
  · exact pieceS hs rfl (show (1024 : Nat) < 32768 by decide) (by dsimp only; rw [hp]; omega_arith)
      (by dsimp only; rw [hp]; omega_arith)
      (by lsep hF [hashLay, Lay.size, hF.pk, ite_true]) (.inr rfl) fun h => absurd h (by decide)

theorem trHash_ok {p : Params} (hF : PFacts p) {STK : Nat} {σ : State} {A : Nat → Poly} {S : Nat → IPoly}
    {R : BitVec 64} {s : State} (h : KR p STK σ A S R (p.ℓ + p.k) p.ℓ p.k s) :
    WP isa (trHash p) s (KFin p STK σ) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hs := h.kc.site
  obtain ⟨hin, hq⟩ := trPieces hF hs
  unfold trHash
  refine WP.mono (hashS hs ktrue (rate := 136) (sfx := 0x1f) (by decide) (by decide) (by simp) hin hq)
    fun s' ⟨k', o'⟩ => ⟨A, S, R, h.keep hF k' ?_, ?_⟩
  · have := hF.scr
    exact (KRChk.c0 (o := 0) (n := 200) hF (Nat.le_refl _) (Nat.le_refl _) (.inl (by decide)) (.inl (by decide))
      (by omega_arith)).append (W₁ := [_]) ((KRChk.stk hF (Nat.le_refl _) (Nat.le_refl _)).append (W₁ := [_])
      (KRChk.c4 (o := 64) (n := 64) hF (Nat.le_refl _) (Nat.le_refl _) (by decide) (.inl (by decide))
        (.inl (by simp only [oT0]; omega_arith)) (by rw [hF.sk, oT0]; omega_arith)))
  have o₃ : bytesAt s'.mem ((lay p STK σ).A 4 64) 64 = _ := o'
  rw [o₃]
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, Lay.pb,
    hashLay_ptr _ _ _ (ix_ne1 _)]
  have e : bytesAt s.mem ((lay p STK σ).ptr (ix Reg.s9) + BitVec.ofNat 64 0) p.pkLen = pkK p A S (rhoOf p σ) :=
    pk_bytes hF h
  have hp := hF.pk
  have h1024 : 1024 ≤ p.pkLen := by rw [hp]; omega_arith
  have e' : bytesAt s.mem ((lay p STK σ).ptr (ix Reg.s9) + BitVec.ofNat 64 0) 1024 ++
      bytesAt s.mem ((lay p STK σ).ptr (ix Reg.s9) + BitVec.ofNat 64 1024) (p.pkLen - 1024) =
      pkK p A S (rhoOf p σ) := by
    rw [← e, show (lay p STK σ).ptr (ix Reg.s9) + BitVec.ofNat 64 1024 =
      (lay p STK σ).ptr (ix Reg.s9) + BitVec.ofNat 64 0 + BitVec.ofNat 64 1024 by rw [BitVec.add_zero],
      ← Proof.MlKem.bytesAt_add, Nat.add_sub_cancel' h1024]
  rw [e', shake31]
  exact (Proof.MlKem.shake256_eq _ _).symm

theorem trHash_piece {p : Params} (hF : PFacts p) {STK : Nat} :
    KPiece p STK (KRx p STK (p.ℓ + p.k) p.ℓ p.k) (KFin p STK) (trHash p) :=
  ⟨fun _ _ _ ⟨_, _, _, h⟩ => trHash_ok hF h,
    rel_of (ktwo fun σ => hashS_tr ktrue (rate := 136) (sfx := 0x1f) (by decide) (by decide) (by simp)
      (fun s hs => (trPieces hF hs).1) (fun s hs => (trPieces hF hs).2) fun _ _ h => h)
      fun _ _ _ _ _ _ pub ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ => kc_two pub h₁.kc h₂.kc⟩

/-! ## The return -/

theorem epi_ok {p : Params} (hF : PFacts p) {STK : Nat} {σ s : State} (h : KFin p STK σ s) :
    WP isa (.block topEnd) s fun s' =>
      RISCV64.target.abiPreserved σ s' ∧ (Spec.MlDsa.keyGenContract p RISCV64.abi STK).post σ s' := by
  obtain ⟨A, S, R, h, htr⟩ := h
  have hs := h.kc.site
  have hscr := hF.scr
  have hin : ∀ o, 1288 ≤ o → o + 8 ≤ 1368 → InRegions (s.rd ++ s.wr) (pScr σ + BitVec.ofNat 64 o) 8 :=
    fun o h₁ h₂ => mem_rd_wr' (Lay.covers (L := lay p STK σ) (o := o) (l := 8) (hs.cw 0 (by decide) (by decide))
      (by rw [lay_size0]; omega_arith) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩)
  refine WP.mono (topEnd_ok hs.s11 hs.al0 h.kc.sav hin h.kc.pres)
    fun s' ⟨pr, lr, r3, m', sp', _, _⟩ => ⟨⟨pr, sp'.trans h.kc.sp, lr⟩, ?_⟩
  sig_post [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, RISCV64.abi, RISCV64.argRegs]
  have e3 : σ.gpr .a1 = (lay p STK σ).A 3 0 := by simp only [Lay.A, BitVec.add_zero]; rfl
  have e4 : σ.gpr .a2 = (lay p STK σ).A 4 0 := by simp only [Lay.A, BitVec.add_zero]; rfl
  rw [r3, h.s4, m', e3, e4, pk_bytes hF h, sk_bytes hF h htr]
  exact Proof.MlDsa.KeyGen.outcome_keyGen (by have := hF.l; omega_arith) h.good

theorem ktaint31 {p : Params} {STK : Nat} {c : Prog isa} {hc : VG.Taint.Hint VG.RISCV64.taint.T}
    (h : (VG.RISCV64.taint.check (Taint.ofRegs [.s11]) c hc).isSome = true) : RelCT isa (KTwo p STK) c fun _ _ => True :=
  ktwo fun _ => taint31 (fun _ _ h => h) h

theorem epi_piece {p : Params} (hF : PFacts p) {STK : Nat} :
    KPiece p STK (KFin p STK)
      (fun σ s => RISCV64.target.abiPreserved σ s ∧ (Spec.MlDsa.keyGenContract p RISCV64.abi STK).post σ s)
      (.block topEnd) :=
  ⟨fun _ _ _ h => epi_ok hF h, rel_of (ktaint31 (by taint_decide))
    fun _ _ _ _ _ _ pub ⟨_, _, _, h₁, _⟩ ⟨_, _, _, h₂, _⟩ => kc_two pub h₁.kc h₂.kc⟩

/-! ## The function -/

section
variable {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : PFacts p) {STK : Nat} (hS : S ≤ STK)
include hP hF hS

theorem rest_piece :
    KPiece p STK (fun σ s => KSamp p STK σ (p.k * p.ℓ) (p.ℓ + p.k) s) (KFin p STK) (rest P p) := by
  unfold rest
  refine (copies_piece hF).seq (Piece.seq (J := KRx p STK (p.ℓ + p.k) 0 0) ?_
    (Piece.seq (J := KRx p STK (p.ℓ + p.k) p.ℓ 0) ?_ (Piece.seq (J := KRx p STK (p.ℓ + p.k) p.ℓ p.k) ?_
      (trHash_piece hF))))
  · refine Piece.mono (Piece.seqR (I := fun r => KRx p STK r 0 0) (p.ℓ + p.k) 0
      fun r _ hr => packS_piece hP hF hS (by omega_arith)) (fun _ _ _ h => h) fun _ _ _ h => ?_
    simpa using h
  · refine Piece.mono (Piece.seqR (I := fun j => KRx p STK (p.ℓ + p.k) j 0) p.ℓ 0
      fun j _ hj => nttS_piece hP hF hS (by omega_arith)) (fun _ _ _ h => h) fun _ _ _ h => ?_
    simpa using h
  · refine Piece.mono (Piece.seqR (I := fun i => KRx p STK (p.ℓ + p.k) p.ℓ i) p.k 0
      fun i _ hi => row_piece hP hF hS (by omega_arith)) (fun _ _ _ h => h) fun _ _ _ h => ?_
    simpa using h

theorem keyGen_piece (hSTK : 1168 ≤ STK) :
    KPiece p STK (fun σ s => s = σ)
      (fun σ s => RISCV64.target.abiPreserved σ s ∧ (Spec.MlDsa.keyGenContract p RISCV64.abi STK).post σ s)
      (keyGen P p) :=
  (pro_piece hF hSTK).seq ((seeds_piece hF).seq ((sampA_piece hP hF hS).seq ((sampS_piece hP hF hS).seq
    ((rest_piece hP hF hS).seq (epi_piece hF)))))

end

/-- A state satisfying `keyGenContract`'s precondition. -/
def keyGenSat (p : Params) : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x4000 | .a3 => 0x10000 | _ => 0
  sp := 0x80000
  mem _ := 0
  rd := [⟨0x1000, 32⟩]
  wr := [⟨0x2000, p.pkLen⟩, ⟨0x4000, p.skLen⟩, ⟨0x10000, scrLen p⟩]

/-- `vg_mldsa*_keygen` of the parameter set `p` meets its contract with `S`
bytes of stack, for any verified implementations `P` of the primitives it
calls with at most `S` bytes of stack, and `S` at least the 1168 bytes the
sponge needs. The contract's satisfiability (`hsat`, by `keyGenSat`) is
evaluated once `S` is known. -/
theorem keyGen_verified {P : Prims} {S : Nat} (hP : PrimsOk P S) (h48 : 1168 ≤ S)
    (p : Spec.MlDsa.Params) (hp : p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87)
    (hsat : (Spec.MlDsa.keyGenContract p RISCV64.abi S).pre (keyGenSat p)) :
    Verified RISCV64.target (keyGen P p) (Spec.MlDsa.keyGenContract p RISCV64.abi S) := by
  have hF := pfacts hp
  have hk := keyGen_piece hP hF (Nat.le_refl _) h48
  obtain ⟨n, rfl⟩ : ∃ n, S = n + 1 := ⟨S - 1, by omega_arith⟩
  refine ⟨fun s hs => hk.ok s s (pre_of hs) rfl, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_,
    ⟨keyGenSat p, hsat⟩⟩
  sig_pub [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, RISCV64.abi, RISCV64.argRegs] at hpub
  obtain ⟨hsp, hl, h3, h4, h5, h6⟩ := hpub
  exact relStart hk.tr s₁ s₂ t₁ t₂ s₁' s₂' (pre_of h₁) (pre_of h₂) ⟨hsp, h3, h4, h5, h6, hl⟩ e₁ e₂

end VG.Proof.MlDsa.RISCV64.KeyGen

end

end

/-! ### `MlDsa.RISCV64.Round.Power2Round`, which only this module used -/

section

/-!
# ML-DSA on RISCV64: `vg_mldsa_power2round`

One symbolic execution of the loop body, for any pointers (`body_ok`), which
writes `(a + 4095) >> 13` to `t1` and `((a + 4095) mod 2¹³) - 4095`, plus
`q` if negative, to `t0` (`p2r1_val`, `p2r0_val`, through
`power2Round_eq`); the loop invariant says which coefficients are done
(`Inv`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Round.Power2Round

open VG VG.RISCV64 VG.Impl.MlDsa.RISCV64.Round
open VG.Impl.MlKem.RISCV64 (fixup)
open VG.Impl.MlDsa.RISCV64.Arith (loadImm)
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Round (coeffAddr pR coeff_contains coeffAt_writeW polyAt_val polyIs_of_toNat natPolyIs_of_toNat
  map_get coeffAt_frame power2Round_eq power2Round_t0 reduced_zero)
open VG.Proof.MlDsa.RISCV64.Round
open VG.Proof.MlDsa.RISCV64.Arith (loadImm_q)
open VG.Proof.MlKem.RISCV64 (wp_loop_nz count_sub count_nz ptr_succ align4_add)

/-! ## Values -/

theorem p2r1_val {a : BitVec 64} (ha : a.toNat < q) :
    ((a + 4095) >>> 13).toNat = (a.toNat + 4095) / 8192 := by
  rw [VG.Proof.MlDsa.Round.q_eq] at ha
  bv_omega

/-- What `power2Round` leaves for `t0`, before `fixup`. -/
def p2rLow (a : BitVec 64) : BitVec 64 :=
  a + (4095 : BitVec 64) - ((a + (4095 : BitVec 64)) >>> 13) <<< 13 - (4095 : BitVec 64)

theorem p2r0_val {a : BitVec 64} (ha : a.toNat < q) :
    (fixk 8380417 (p2rLow a)).toNat =
      if (a.toNat + 4095) % 8192 < 4095 then (a.toNat + 4095) % 8192 + q - 4095
      else (a.toNat + 4095) % 8192 - 4095 := by
  rw [VG.Proof.MlDsa.Round.q_eq] at ha ⊢
  have t : (4095 : BitVec 64).toNat = 4095 := by simp
  have h1 : (a + 4095).toNat = a.toNat + 4095 := by rw [BitVec.toNat_add, t]; omega_using [ha]
  have h2 : ((a + 4095) >>> 13 <<< 13).toNat = (a.toNat + 4095) / 8192 * 8192 := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, h1, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    exact Nat.mod_eq_of_lt (by omega_using [ha])
  have hx : (a + (4095 : BitVec 64) - ((a + (4095 : BitVec 64)) >>> 13) <<< 13).toNat = (a.toNat + 4095) % 8192 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h1, h2]; omega_using []), h1, h2]; omega_using []
  have := fixk_diff (k := 8380417) (by decide)
    (a := a + (4095 : BitVec 64) - ((a + (4095 : BitVec 64)) >>> 13) <<< 13) (b := 4095)
    (by rw [hx]; omega_using []) (by rw [hx, t]; exact Nat.le_add_left _ _) (by rw [t]; decide)
  rw [hx, t] at this
  exact this

/-! ## The loop body -/

/-- What an iteration does, for the values stored. -/
def Step (s : State) (x y z c : BitVec 64) (v w : BitVec 32) (s' : State) : Prop :=
  s'.gpr .a0 = x + 4 ∧ s'.gpr .a1 = y + 4 ∧ s'.gpr .a2 = z + 4 ∧ s'.gpr .a3 = c - 1 ∧
    s'.gpr .a4 = s.gpr .a4 ∧ s'.gpr .t2 = s.gpr .t2 ∧
    s'.mem = (s.mem.writeW y v).writeW z w ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
    s'.gpr .ra = s.gpr .ra ∧
    ∀ r ∈ preserved, s'.gpr r = s.gpr r

section
variable {s : State} {x y z c : BitVec 64} (h3 : s.gpr .a0 = x) (h4 : s.gpr .a1 = y) (h5 : s.gpr .a2 = z)
  (h6 : s.gpr .a3 = c) (h7 : s.gpr .a4 = 8380417) (h12 : s.gpr .t2 = 4095)
  (ia : InRegions (s.rd ++ s.wr) x 4) (ob : InRegions s.wr y 4) (oc : InRegions s.wr z 4)
  (ax : x.toNat % 4 = 0) (ay : y.toNat % 4 = 0) (az : z.toNat % 4 = 0)
include h3 h4 h5 h6 h7 h12 ia ob oc ax ay az

theorem body_ok :
    WP isa (.block p2rBody) s (Step s x y z c
      ((((s.mem.readW x 32).setWidth 64 + 4095) >>> 13).setWidth 32)
      ((fixk 8380417 (p2rLow ((s.mem.readW x 32).setWidth 64))).setWidth 32)) := by
  crun [p2rBody, fixup, Step, fixk, p2rLow, h3, h4, h5, h6, h7, h12, ia, ob, oc, ax, ay, az, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, List.cons_append, List.nil_append]
  simp [Mem.writeW, Mem.readW, Mem.read]

end

/-! ## The loop -/

section
variable (s₀ : State)

abbrev T : Addr := s₀.gpr .a0
abbrev T1 : Addr := s₀.gpr .a1
abbrev T0 : Addr := s₀.gpr .a2

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [pR (T s₀)]
  wr : s₀.wr = [pR (T1 s₀), pR (T0 s₀)]
  dt1 : (pR (T s₀)).Disjoint (pR (T1 s₀))
  dt0 : (pR (T s₀)).Disjoint (pR (T0 s₀))
  d01 : (pR (T1 s₀)).Disjoint (pR (T0 s₀))
  fit : (T s₀).toNat + 1024 ≤ 2 ^ 64
  fit1 : (T1 s₀).toNat + 1024 ≤ 2 ^ 64
  fit0 : (T0 s₀).toNat + 1024 ≤ 2 ^ 64
  red : Reduced s₀.mem (T s₀)
  al : (T s₀).toNat % 4 = 0
  al1 : (T1 s₀).toNat % 4 = 0
  al0 : (T0 s₀).toNat % 4 = 0

/-- After `i` iterations, writing `o1 j` and `o0 j` to coefficient `j` of
`t1` and `t0`. -/
structure Inv (o1 o0 : Nat → BitVec 32) (s₀ : State) (i : Nat) (s : State) : Prop where
  r3 : s.gpr .a0 = T s₀ + BitVec.ofNat 64 (4 * i)
  r4 : s.gpr .a1 = T1 s₀ + BitVec.ofNat 64 (4 * i)
  r5 : s.gpr .a2 = T0 s₀ + BitVec.ofNat 64 (4 * i)
  r6 : s.gpr .a3 = BitVec.ofNat 64 (256 - i)
  r7 : s.gpr .a4 = 8380417
  r12 : s.gpr .t2 = 4095
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  lr : s.gpr .ra = s₀.gpr .ra
  pres : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  frame : Frame [pR (T1 s₀), pR (T0 s₀)] s₀.mem s.mem
  c1 : ∀ j < 256, j < i → coeffAt s.mem (T1 s₀) j = o1 j
  c0 : ∀ j < 256, j < i → coeffAt s.mem (T0 s₀) j = o0 j

/-- The coefficient of `t` an iteration reads is as on entry. -/
theorem read_t {o1 o0 : Nat → BitVec 32} {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 256) {s : State}
    (h : Inv o1 o0 s₀ i s) : s.mem.readW (T s₀ + BitVec.ofNat 64 (4 * i)) 32 = coeffAt s₀.mem (T s₀) i :=
  coeffAt_frame h.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.dt1
    · exact hp.dt0) hi

theorem inv_step {o1 o0 : Nat → BitVec 32} {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 256)
    {s : State} (h : Inv o1 o0 s₀ i s)
    (hv : ∀ {a : BitVec 64}, a = (coeffAt s₀.mem (T s₀) i).setWidth 64 →
      ((a + 4095) >>> 13).setWidth 32 = o1 i ∧ (fixk 8380417 (p2rLow a)).setWidth 32 = o0 i) :
    WP isa (.block p2rBody) s fun s' => Inv o1 o0 s₀ (i + 1) s' ∧ (s'.gpr .a3 != 0) = decide (i + 1 ≠ 256) := by
  have cT := coeff_contains (T s₀) (i := i) hi
  have c1 := coeff_contains (T1 s₀) (i := i) hi
  have c0 := coeff_contains (T0 s₀) (i := i) hi
  obtain ⟨v1, v0⟩ := hv (a := (s.mem.readW (T s₀ + BitVec.ofNat 64 (4 * i)) 32).setWidth 64)
    (by rw [read_t hp hi h])
  refine WP.mono (body_ok h.r3 h.r4 h.r5 h.r6 h.r7 h.r12 ?_ ?_ ?_ (align4_add hp.al i) (align4_add hp.al1 i)
    (align4_add hp.al0 i))
    fun s' ⟨r3, r4, r5, r6, r7, r12, m, rd, wr, sp, lr, pres⟩ => ⟨⟨?_, ?_, ?_, ?_,
    r7.trans h.r7, r12.trans h.r12, rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, lr.trans h.lr,
    fun r hr => (pres r hr).trans (h.pres r hr), ?_, ?_, ?_⟩, ?_⟩
  · rw [h.rd, h.wr, hp.rd, hp.wr]; exact ⟨_, by simp, cT⟩
  · rw [h.wr, hp.wr]; exact ⟨_, by simp, c1⟩
  · rw [h.wr, hp.wr]; exact ⟨pR (T0 s₀), by simp, c0⟩
  · rw [r3]; exact ptr_succ _ 4 i
  · rw [r4]; exact ptr_succ _ 4 i
  · rw [r5]; exact ptr_succ _ 4 i
  · rw [r6]; exact count_sub hi
  · rw [m]
    exact (h.frame.writeW (List.mem_cons_self ..) _ c1).writeW (by simp) _ c0
  · intro j hj hji
    have dj : (pR (T1 s₀)).Disjoint (pR (T0 s₀)) := hp.d01
    rw [m, show T1 s₀ + BitVec.ofNat 64 (4 * i) = coeffAddr (T1 s₀) i from rfl,
      show T0 s₀ + BitVec.ofNat 64 (4 * i) = coeffAddr (T0 s₀) i from rfl,
      VG.Proof.MlDsa.Round.coeffAt_writeW_disjoint _ (hp.d01) (coeff_contains _ hi) (i := j) (by omega),
      coeffAt_writeW _ _ hj hi]
    by_cases e : i = j
    · subst e; rw [ite_eq_left rfl, v1]
    · rw [ite_eq_right e]; exact h.c1 j hj (by omega_using [hji, e])
  · intro j hj hji
    rw [m, show T0 s₀ + BitVec.ofNat 64 (4 * i) = coeffAddr (T0 s₀) i from rfl,
      coeffAt_writeW _ _ hj hi]
    by_cases e : i = j
    · subst e; rw [ite_eq_left rfl, v0]
    · rw [ite_eq_right e, VG.Proof.MlDsa.Round.coeffAt_writeW_disjoint _ hp.d01.symm (coeff_contains _ hi)
        (i := j) (by omega)]
      exact h.c0 j hj (by omega_using [hji, e])
  · rw [r6, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, count_sub hi]; exact count_nz hi (by decide)

theorem loop_ok {o1 o0 : Nat → BitVec 32} {s₀ : State} (hp : Pre s₀)
    (hv : ∀ i < 256, ∀ {a : BitVec 64}, a = (coeffAt s₀.mem (T s₀) i).setWidth 64 →
      ((a + 4095) >>> 13).setWidth 32 = o1 i ∧ (fixk 8380417 (p2rLow a)).setWidth 32 = o0 i) :
    WP isa power2Round s₀ (Inv o1 o0 s₀ 256) := by
  refine WP.seq ?_
  simp only [loadQ, loadImm_q, loadImm_4095, List.cons_append, List.nil_append]
  crun []
  refine wp_loop_nz (Inv o1 o0 s₀) (N := 256) (by decide)
    (fun i hi s h => inv_step hp hi h (hv i hi)) (fun _ h => h) ?_
  refine ⟨by simp, by simp, by simp, by simp, by simp; decide, by simp; decide,
    rfl, rfl, rfl, by simp, fun r hr => ?_, Frame.refl _ _, fun j _ h => absurd h (by omega_using []),
    fun j _ h => absurd h (by omega_using [])⟩
  have : r ≠ .a3 ∧ r ≠ .a4 ∧ r ≠ .t2 := by revert r hr; decide
  simp [this.1, this.2.1, this.2.2]

/-! ## Correctness -/

/-- The values stored. -/
def o1 (s₀ : State) (j : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (((polyAt s₀.mem (T s₀)).map fun c => (power2Round c).1.toNat)[j]!)

def o0 (s₀ : State) (j : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (((polyAt s₀.mem (T s₀)).map fun c => ofInt (power2Round c).2)[j]!).val

theorem vals {s₀ : State} (hp : Pre s₀) : ∀ i < 256, ∀ {a : BitVec 64}, a = (coeffAt s₀.mem (T s₀) i).setWidth 64 →
    ((a + 4095) >>> 13).setWidth 32 = o1 s₀ i ∧ (fixk 8380417 (p2rLow a)).setWidth 32 = o0 s₀ i := by
  intro i hi a ha
  have hr := hp.red i hi
  have hat : a.toNat = (coeffAt s₀.mem (T s₀) i).toNat := by
    rw [ha, BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := (coeffAt s₀.mem (T s₀) i).isLt; omega_using [])
  have hpv := polyAt_val hp.red (i := i) hi
  have hq : a.toNat < q := by rw [hat]; exact hr
  refine ⟨?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, p2r1_val hq, o1, map_get _ _ hi, power2Round_eq, hpv, ← hat, BitVec.toNat_ofNat]
    simp only [Int.toNat_natCast]
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, p2r0_val hq, o0, map_get _ _ hi, power2Round_t0, hpv, ← hat, BitVec.toNat_ofNat]

theorem o1_toNat (s₀ : State) {j : Nat} (hj : j < 256) :
    (o1 s₀ j).toNat = ((polyAt s₀.mem (T s₀)).map fun c => (power2Round c).1.toNat)[j]! := by
  rw [o1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  rw [map_get _ _ hj, power2Round_eq]
  simp only [Int.toNat_natCast]
  have : ((polyAt s₀.mem (T s₀))[j]!).val < 8380417 := Fin.isLt _
  omega

theorem o0_toNat (s₀ : State) {j : Nat} :
    (o0 s₀ j).toNat = (((polyAt s₀.mem (T s₀)).map fun c => ofInt (power2Round c).2)[j]!).val := by
  rw [o0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  exact Nat.lt_trans (Fin.isLt _) (by decide)

theorem pre_of {s : State} (h : (Proof.MlDsa.power2RoundContract RISCV64.abi).pre s) : Pre s := by
  sig_pre [Proof.MlDsa.power2RoundContract, Proof.MlDsa.power2RoundSig, RISCV64.abi, RISCV64.argRegs] at h
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 1024⟩]

theorem verified : Verified RISCV64.target power2Round (Proof.MlDsa.power2RoundContract RISCV64.abi) := by
  refine ⟨fun s hs => ?_, VG.Proof.MlKem.RISCV64.Add.ctRegs [.a0, .a1, .a2] (fun s₁ s₂ h => ?_)
    (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · have hp := pre_of hs
    obtain ⟨t, s', he, h⟩ := loop_ok hp (vals hp)
    refine ⟨t, s', he, ⟨h.pres, h.sp, h.lr⟩, ?_⟩
    sig_post [Proof.MlDsa.power2RoundContract, Proof.MlDsa.power2RoundSig, RISCV64.abi, RISCV64.argRegs]
    refine ⟨natPolyIs_of_toNat fun j hj => ?_, polyIs_of_toNat fun j hj => ?_⟩
    · rw [h.c1 j hj hj]; exact o1_toNat s hj
    · rw [h.c0 j hj hj]; exact o0_toNat s
  · sig_pub [Proof.MlDsa.power2RoundContract, Proof.MlDsa.power2RoundSig, RISCV64.abi, RISCV64.argRegs] at h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2
  · sig_pub [Proof.MlDsa.power2RoundContract, Proof.MlDsa.power2RoundSig, RISCV64.abi, RISCV64.argRegs] at h
    exact h.1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlDsa.power2RoundContract, Proof.MlDsa.power2RoundSig, RISCV64.abi, RISCV64.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | exact reduced_zero _
        | decide +kernel

end VG.Proof.MlDsa.RISCV64.Round.Power2Round

end

end

/-!
# ML-DSA key generation on RISC-V, with this library's primitives

The RISC-V implementations of the primitives (`prims`) are verified with at
most 1168 bytes of stack (the samplers' Keccak frames; the others use none),
and their frames use no more (`prims_ok`), so key generation with them is
verified with 1168 (`keyGen44_verified`, …).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.KeyGen

open VG VG.RISCV64
open VG.Impl.MlDsa.RISCV64.KeyGen

theorem prims_ok : PrimsOk prims 1168 where
  ntt := ⟨⟨0, by decide, Arith.Ntt.verified⟩, by decide +kernel⟩
  invNtt := ⟨⟨0, by decide, Arith.NttInv.verified⟩, by decide +kernel⟩
  mul := ⟨⟨0, by decide, Arith.Mul.mul_verified⟩, by decide +kernel⟩
  mulAdd := ⟨⟨0, by decide, Arith.Mul.mulAdd_verified⟩, by decide +kernel⟩
  add := ⟨⟨0, by decide, Arith.AddSub.add_verified⟩, by decide +kernel⟩
  rejNtt := ⟨⟨1168, by decide, Sample.rejNTT_verified⟩, by decide +kernel⟩
  rejBounded := ⟨⟨1168, by decide, Sample.rejBounded_verified⟩, by decide +kernel⟩
  power2Round := ⟨⟨0, by decide, Round.Power2Round.verified⟩, by decide +kernel⟩
  simpleBitPack := ⟨⟨0, by decide, Pack.simpleBitPack_verified⟩, by decide +kernel⟩
  bitPack := ⟨⟨0, by decide, Pack.bitPack_verified⟩, by decide +kernel⟩

theorem keyGen44_sat : (Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa44 RISCV64.abi 1168).pre (keyGenSat Spec.MlDsa.mlDsa44) := by
  sig_sat_check [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, RISCV64.abi, RISCV64.argRegs, keyGenSat]

theorem keyGen44_verified :
    Verified RISCV64.target keyGen44 (Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa44 RISCV64.abi 1168) :=
  keyGen_verified prims_ok (by decide) _ (.inl rfl) keyGen44_sat

theorem keyGen65_sat : (Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa65 RISCV64.abi 1168).pre (keyGenSat Spec.MlDsa.mlDsa65) := by
  sig_sat_check [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, RISCV64.abi, RISCV64.argRegs, keyGenSat]

theorem keyGen65_verified :
    Verified RISCV64.target keyGen65 (Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa65 RISCV64.abi 1168) :=
  keyGen_verified prims_ok (by decide) _ (.inr (.inl rfl)) keyGen65_sat

theorem keyGen87_sat : (Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa87 RISCV64.abi 1168).pre (keyGenSat Spec.MlDsa.mlDsa87) := by
  sig_sat_check [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, RISCV64.abi, RISCV64.argRegs, keyGenSat]

theorem keyGen87_verified :
    Verified RISCV64.target keyGen87 (Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa87 RISCV64.abi 1168) :=
  keyGen_verified prims_ok (by decide) _ (.inr (.inr rfl)) keyGen87_sat

end VG.Proof.MlDsa.RISCV64.KeyGen
