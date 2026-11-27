module

import VerifiedGarbage.Proof.MlDsa.DecideAt
import VerifiedGarbage.Proof.MlDsa.Arith.Representation
import VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.Call
import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly
import VerifiedGarbage.Proof.MlKem.X86_64.FragC
public import VerifiedGarbage.Proof.MlDsa.KeyGen.Rest
public import VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.Samp
import VerifiedGarbage.Proof.MlKem.X86_64.Lit
meta import VerifiedGarbage.Proof.MlDsa.KeyGen.Rest
meta import VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.Samp
meta import VerifiedGarbage.Proof.MlDsa.DecideAt
meta import VerifiedGarbage.Proof.MlKem.X86_64.Lit
import VerifiedGarbage.Proof.MlKem.X86_64.SampleLoop
meta import VerifiedGarbage.Proof.MlKem.X86_64.FragC
meta import VerifiedGarbage.Proof.MlKem.X86_64.SampleLoop
meta import VerifiedGarbage.Proof.MlKem.Kpke16Contract
meta import VerifiedGarbage.Proof.MlKem.KpkeMulContract

/-! ### `MlDsa.X86_64.KeyGen.RestPack`, which this module and modules that import it used -/

section

/-! ### `MlDsa.X86_64.KeyGen.RestBase`, which only this module used -/

section

/-!
# ML-DSA key generation on x86-64: after the samplers

Once the samplers are done, with `Â` and `s₁ ‖ s₂` in memory as `A` and `S`
and `r15` as `R` (`Good`), the rest of the function computes the keys from
them, whatever they are (`KR`): after the copies of `ρ` and `K`
(`copies_piece`), the first `np` entries of `s₁ ‖ s₂` packed to `sk`, the
first `nj` of `s₁` in the NTT domain, and the first `nr` rows of `t` packed to
`pk` and `sk`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.KeyGen

open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.MlKem.X86_64 (Ptr sc copy seqR)
open VG.Impl.MlDsa.X86_64.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt bitPack simpleBitPack)
open VG.Proof.MlDsa (polyAt coeffAt Reduced PolyIs)
open VG.Proof.MlDsa.KeyGen (t1K t0K)
open VG.Spec.Sha3 (bytesAt)

/-- After the samplers: the keys from `A`, `S` and `R`, so far. -/
structure KR (p : Params) (σ : State) (A : Nat → Poly) (S : Nat → IPoly) (R : BitVec 64) (np nj nr : Nat)
    (s : State) : Prop where
  kc : KC p σ s
  r15 : s.gpr .r15 = R
  good : Good p σ (p.k * p.ℓ) (p.ℓ + p.k) A S R
  small : ∀ r < p.ℓ + p.k, Small p.η (S r)
  aS : ∀ e < p.k * p.ℓ, PolyIs s.mem (pa s (aP e)) (A e)
  s2 : ∀ i < p.k, PolyIs s.mem (pa s (sP p (p.ℓ + i))) (toRq (S (p.ℓ + i)))
  s1 : ∀ j < p.ℓ, PolyIs s.mem (pa s (sP p j)) (if j < nj then ntt (toRq (S j)) else toRq (S j))
  pk0 : bytesAt s.mem (pa s (.r12, 0)) 32 = rhoOf p σ
  sk0 : bytesAt s.mem (pa s (.r13, 0)) 32 = rhoOf p σ
  sk1 : bytesAt s.mem (pa s (.r13, 32)) 32 = kOf p σ
  packs : ∀ r < np, bytesAt s.mem (pa s (.r13, 128 + lenS p * r)) (lenS p) = bitPack (S r) p.η p.η
  rows : ∀ i < nr, bytesAt s.mem (pa s (.r12, 32 + 320 * i)) 320 = simpleBitPack (t1K p A S i) 1023 ∧
    bytesAt s.mem (pa s (.r13, oT0 p + 416 * i)) 416 = bitPack (t0K p A S i) 4095 4096

/-- A piece that writes `ws` keeps what `KR` says. -/
structure KRChk (p : Params) (np nj nr : Nat) (ws : List (Ptr × Nat)) : Prop where
  kc : kcChk p ws = true
  aS : ∀ e < p.k * p.ℓ, keepB (kgB p) ws (aP e) 1024 = true
  s2 : ∀ i < p.k, keepB (kgB p) ws (sP p (p.ℓ + i)) 1024 = true
  s1 : ∀ j < p.ℓ, keepB (kgB p) ws (sP p j) 1024 = true
  pk0 : keepB (kgB p) ws (.r12, 0) 32 = true
  sk0 : keepB (kgB p) ws (.r13, 0) 32 = true
  sk1 : keepB (kgB p) ws (.r13, 32) 32 = true
  packs : ∀ r < np, keepB (kgB p) ws (.r13, 128 + lenS p * r) (lenS p) = true
  rows : ∀ i < nr, keepB (kgB p) ws (.r12, 32 + 320 * i) 320 = true ∧ keepB (kgB p) ws (.r13, oT0 p + 416 * i) 416 = true

/-- The checks of two pieces of writes, for both. -/
theorem KRChk.append {p : Params} {np nj nr : Nat} {ws₁ ws₂ : List (Ptr × Nat)} (h₁ : KRChk p np nj nr ws₁)
    (h₂ : KRChk p np nj nr ws₂) : KRChk p np nj nr (ws₁ ++ ws₂) :=
  ⟨kcChk_append h₁.kc h₂.kc, fun e he => keepB_append (h₁.aS e he) (h₂.aS e he),
    fun i hi => keepB_append (h₁.s2 i hi) (h₂.s2 i hi), fun j hj => keepB_append (h₁.s1 j hj) (h₂.s1 j hj),
    keepB_append h₁.pk0 h₂.pk0, keepB_append h₁.sk0 h₂.sk0, keepB_append h₁.sk1 h₂.sk1,
    fun r hr => keepB_append (h₁.packs r hr) (h₂.packs r hr),
    fun i hi => ⟨keepB_append (h₁.rows i hi).1 (h₂.rows i hi).1, keepB_append (h₁.rows i hi).2 (h₂.rows i hi).2⟩⟩

/-! The checks of a write to one region, proved once for any region: each check
is about the write and one region, apart from it or in another buffer. -/

/-- A write keeps a region of another register, both in the layout, the write's register written. -/
theorem keepB_one_diff {bs : List (Reg × Nat)} {r r' : Reg} {o n o' l : Nat} (hb : r' ∈ bases) (hne : r' ≠ r)
    (hw : r ∈ wRegs) (hq : inB bs (r', o') l = true) (hi : inB bs (r, o) n = true) :
    keepB bs [((r, o), n)] (r', o') l = true := by
  simp only [keepB, List.all_cons, List.all_nil, sepB_diff bs hne (Or.inr hw), hq, hi, decide_eq_true hb,
    Bool.and_self]

/-- A write keeps a region of its register apart from it, both in the layout. -/
theorem keepB_one_same {bs : List (Reg × Nat)} {r : Reg} {o n o' l : Nat} (hb : r ∈ bases)
    (hq : inB bs (r, o') l = true) (hi : inB bs (r, o) n = true) (h : o' + l ≤ o ∨ o + n ≤ o') :
    keepB bs [((r, o), n)] (r, o') l = true := by
  simp only [keepB, List.all_cons, List.all_nil, sepB_same, hq, hi, decide_eq_true hb, Bool.and_true,
    Bool.true_and, Bool.or_eq_true, decide_eq_true_eq]
  exact h

/-- A write to `pk` or `sk` keeps what `KC` says. -/
theorem kcChk_one {p : Params} {r : Reg} {o n : Nat} (hr : r = .r12 ∨ r = .r13)
    (hi : inB (kgB p) (r, o) n = true) : kcChk p [((r, o), n)] = true := by
  have hw : r ∈ wRegs := by rcases hr with rfl | rfl <;> decide
  have hs : 840 + 48 ≤ scrLen p := by simp only [scrLen, Spec.MlDsa.scratchWords]; omega_using []
  simp only [kcChk, topChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, List.all_cons, List.all_nil,
    Bool.and_true]
  refine ⟨⟨fun k hk => keepB_one_diff (by decide) (by rcases hr with rfl | rfl <;> decide) hw
    (by rw [inB_rbx]; exact decide_eq_true (by simp only [VG.Impl.MlKem.X86_64.oSV]; omega_using [hs, hk])) hi, hi⟩,
    keepB_one_diff (by decide) (by rcases hr with rfl | rfl <;> decide) hw (by rw [inB_rbp]; rfl) hi⟩

/-- A write to `scratch` outside the saved registers and the polynomials. -/
theorem KRChk.rbx {p : Params} (hF : PFacts p) {np nj nr : Nat} (hnp : np ≤ p.ℓ + p.k) (hnr : nr ≤ p.k) {o n : Nat}
    (h1 : o + n ≤ VG.Impl.MlKem.X86_64.oSV ∨ VG.Impl.MlKem.X86_64.oSV + 48 ≤ o)
    (h2 : o + n ≤ oP 0 ∨ oP (p.k * p.ℓ + p.ℓ + p.k) ≤ o) (h3 : o + n ≤ scrLen p) :
    KRChk p np nj nr [((.rbx, o), n)] := by
  have hk := hF.k; have hl := hF.l
  have hi : inB (kgB p) (.rbx, o) n = true := by rw [inB_rbx]; exact decide_eq_true h3
  have hs : scrLen p = 1024 * (p.k * p.ℓ + 4 * p.k + 3 * p.ℓ + 32) := by
    simp only [scrLen, Spec.MlDsa.scratchWords]; omega_using []
  have hsk := hF.sk
  have hpk := hF.pk
  simp only [VG.Impl.MlKem.X86_64.oSV] at h1
  simp only [oP] at h2
  simp only [oT0] at hsk
  have bx : ∀ {o' l : Nat}, o' + l ≤ scrLen p → (o' + l ≤ o ∨ o + n ≤ o') →
      keepB (kgB p) [((.rbx, o), n)] (.rbx, o') l = true :=
    fun h => keepB_one_same (by decide) (by rw [inB_rbx]; exact decide_eq_true h) hi
  have b12 : ∀ {o' l : Nat}, o' + l ≤ p.pkLen → keepB (kgB p) [((.rbx, o), n)] (.r12, o') l = true :=
    fun h => keepB_one_diff (by decide) (by decide) (by decide) (by rw [inB_r12]; exact decide_eq_true h) hi
  have b13 : ∀ {o' l : Nat}, o' + l ≤ p.skLen → keepB (kgB p) [((.rbx, o), n)] (.r13, o') l = true :=
    fun h => keepB_one_diff (by decide) (by decide) (by decide) (by rw [inB_r13]; exact decide_eq_true h) hi
  have kc : kcChk p [((.rbx, o), n)] = true := by
    simp only [kcChk, topChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, List.all_cons, List.all_nil,
      Bool.and_true]
    exact ⟨⟨fun k hk' => bx (by rw [hs]; simp only [VG.Impl.MlKem.X86_64.oSV]; omega_using [hk'])
      (by simp only [VG.Impl.MlKem.X86_64.oSV]; omega_using [h1, hk']), hi⟩,
      keepB_one_diff (by decide) (by decide) (by decide) (by rw [inB_rbp]; rfl) hi⟩
  refine ⟨kc, fun e he => bx ?_ ?_, fun i hi' => bx ?_ ?_, fun j hj => bx ?_ ?_, b12 ?_, b13 ?_, b13 ?_,
    fun r hr' => b13 ?_, fun i hi' => ⟨b12 ?_, b13 ?_⟩⟩
  all_goals try simp only [oP, oT0]
  · rw [hs]; omega_using [he]
  · omega_using [h2, he]
  · rw [hs]; omega_using [hi']
  · omega_using [h2, hi']
  · rw [hs]; omega_using [hj]
  · omega_using [h2, hj]
  · omega_using [hpk]
  · omega_using [hsk]
  · omega_using [hsk]
  · rcases hF.eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;> simp only [hlen] at hsk ⊢ <;> omega_using [hnp, hr', hsk]
  · omega_using [hnr, hpk, hi']
  · omega_using [hnr, hsk, hi']

/-- A write to `pk` after the rows so far. -/
theorem KRChk.r12 {p : Params} (hF : PFacts p) {np nj nr : Nat} (hnp : np ≤ p.ℓ + p.k) (_hnr : nr ≤ p.k) {o n : Nat}
    (h1 : 32 + 320 * nr ≤ o) (h2 : o + n ≤ p.pkLen) : KRChk p np nj nr [((.r12, o), n)] := by
  have hk := hF.k; have hl := hF.l
  have hi : inB (kgB p) (.r12, o) n = true := by rw [inB_r12]; exact decide_eq_true h2
  have hs : scrLen p = 1024 * (p.k * p.ℓ + 4 * p.k + 3 * p.ℓ + 32) := by
    simp only [scrLen, Spec.MlDsa.scratchWords]; omega_using []
  have hsk := hF.sk
  have hpk := hF.pk
  simp only [oT0] at hsk
  have bx : ∀ {o' l : Nat}, o' + l ≤ scrLen p → keepB (kgB p) [((.r12, o), n)] (.rbx, o') l = true :=
    fun h => keepB_one_diff (by decide) (by decide) (by decide) (by rw [inB_rbx]; exact decide_eq_true h) hi
  have b12 : ∀ {o' l : Nat}, o' + l ≤ p.pkLen → (o' + l ≤ o ∨ o + n ≤ o') →
      keepB (kgB p) [((.r12, o), n)] (.r12, o') l = true :=
    fun h => keepB_one_same (by decide) (by rw [inB_r12]; exact decide_eq_true h) hi
  have b13 : ∀ {o' l : Nat}, o' + l ≤ p.skLen → keepB (kgB p) [((.r12, o), n)] (.r13, o') l = true :=
    fun h => keepB_one_diff (by decide) (by decide) (by decide) (by rw [inB_r13]; exact decide_eq_true h) hi
  refine ⟨kcChk_one (.inl rfl) hi, fun e he => bx ?_, fun i hi' => bx ?_, fun j hj => bx ?_, b12 ?_ ?_, b13 ?_,
    b13 ?_, fun r hr' => b13 ?_, fun i hi' => ⟨b12 ?_ ?_, b13 ?_⟩⟩
  all_goals try simp only [oP, oT0]
  · rw [hs]; omega_using [he]
  · rw [hs]; omega_using [hi']
  · rw [hs]; omega_using [hj]
  · omega_using [hpk]
  · omega_using [h1]
  · omega_using [hsk]
  · omega_using [hsk]
  · rcases hF.eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;> simp only [hlen] at hsk ⊢ <;> omega_using [hnp, hr', hsk]
  · omega_using [h1, h2, hi']
  · omega_using [h1, hi']
  · omega_using [h1, h2, hsk, hpk, hi']

/-- A write to `sk` after `ρ` and `K`, outside the entries packed and the rows so far. -/
theorem KRChk.r13 {p : Params} (hF : PFacts p) {np nj nr : Nat} (hnp : np ≤ p.ℓ + p.k) (hnr : nr ≤ p.k) {o n : Nat}
    (h0 : 64 ≤ o) (hp : o + n ≤ 128 ∨ 128 + lenS p * np ≤ o) (hr : o + n ≤ oT0 p ∨ oT0 p + 416 * nr ≤ o)
    (h2 : o + n ≤ p.skLen) : KRChk p np nj nr [((.r13, o), n)] := by
  have hk := hF.k; have hl := hF.l
  have hi : inB (kgB p) (.r13, o) n = true := by rw [inB_r13]; exact decide_eq_true h2
  have hs : scrLen p = 1024 * (p.k * p.ℓ + 4 * p.k + 3 * p.ℓ + 32) := by
    simp only [scrLen, Spec.MlDsa.scratchWords]; omega_using []
  have hsk := hF.sk
  have hpk := hF.pk
  have bx : ∀ {o' l : Nat}, o' + l ≤ scrLen p → keepB (kgB p) [((.r13, o), n)] (.rbx, o') l = true :=
    fun h => keepB_one_diff (by decide) (by decide) (by decide) (by rw [inB_rbx]; exact decide_eq_true h) hi
  have b12 : ∀ {o' l : Nat}, o' + l ≤ p.pkLen → keepB (kgB p) [((.r13, o), n)] (.r12, o') l = true :=
    fun h => keepB_one_diff (by decide) (by decide) (by decide) (by rw [inB_r12]; exact decide_eq_true h) hi
  have b13 : ∀ {o' l : Nat}, o' + l ≤ p.skLen → (o' + l ≤ o ∨ o + n ≤ o') →
      keepB (kgB p) [((.r13, o), n)] (.r13, o') l = true :=
    fun h => keepB_one_same (by decide) (by rw [inB_r13]; exact decide_eq_true h) hi
  refine ⟨kcChk_one (.inr rfl) hi, fun e he => bx ?_, fun i hi' => bx ?_, fun j hj => bx ?_, b12 ?_,
    b13 ?_ ?_, b13 ?_ ?_, fun r hr' => b13 ?_ ?_, fun i hi' => ⟨b12 ?_, b13 ?_ ?_⟩⟩
  all_goals try simp only [oP]
  · rw [hs]; omega_using [he]
  · rw [hs]; omega_using [hi']
  · rw [hs]; omega_using [hj]
  · omega_using [hpk]
  · omega_using [hk, hsk]
  · omega_using [h0]
  · omega_using [hk, hsk]
  · omega_using [h0]
  · rcases hF.eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;> simp only [oT0, hlen] at hsk ⊢ <;> omega_using [hnp, hr', hsk]
  · rcases hF.eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;> simp only [hlen] at hp ⊢ <;> omega_using [hr', hp]
  · omega_using [hnr, hpk, hi']
  · simp only [oT0] at hsk hr ⊢; omega_using [hnr, hsk, hi']
  · simp only [oT0] at hr ⊢; omega_using [hr, hi']

theorem KR.keep {p : Params} (hF : PFacts p) {σ : State} (hp : (kgK p).pre σ) {A : Nat → Poly} {S : Nat → IPoly}
    {R : BitVec 64} {np nj nr : Nat} {s s' : State} (h : KR p σ A S R np nj nr s) {ws : List (Ptr × Nat)}
    (hP : PPostB s s' ws) (hx : MX s' = MX s) (h15 : s'.gpr .r15 = s.gpr .r15) (hc : KRChk p np nj nr ws) :
    KR p σ A S R np nj nr s' := by
  have L := h.kc.lay hF hp
  exact ⟨h.kc.step hF hp hP hx hc.kc, h15.trans h.r15, h.good, h.small,
    fun e he => polyIs_frame' L hP (hc.aS e he) (h.aS e he), fun i hi => polyIs_frame' L hP (hc.s2 i hi) (h.s2 i hi),
    fun j hj => polyIs_frame' L hP (hc.s1 j hj) (h.s1 j hj), by rw [L.keepBytes hP hc.pk0]; exact h.pk0,
    by rw [L.keepBytes hP hc.sk0]; exact h.sk0, by rw [L.keepBytes hP hc.sk1]; exact h.sk1,
    fun r hr => by rw [L.keepBytes hP (hc.packs r hr)]; exact h.packs r hr,
    fun i hi => ⟨by rw [L.keepBytes hP (hc.rows i hi).1]; exact (h.rows i hi).1,
      by rw [L.keepBytes hP (hc.rows i hi).2]; exact (h.rows i hi).2⟩⟩

/-! ## `ρ` and `K` to the keys -/

theorem r13_bases (o n : Nat) : ∀ w ∈ [(((.r13, o) : Ptr), n)], w.1.1 ∈ bases := fun w hw => by
  rw [List.mem_singleton] at hw; subst hw; show Reg.r13 ∈ bases; decide

/-- After the copies, for some `A`, `S` and `R`. -/
abbrev KR0 (p : Params) (σ s : State) : Prop := ∃ A S R, KR p σ A S R 0 0 0 s

theorem copies_ok {p : Params} (hF : PFacts p) {σ : State} (hp : (kgK p).pre σ) {s : State}
    (h : KSamp p σ (p.k * p.ℓ) (p.ℓ + p.k) s) : WP isa copies s (KR0 p σ) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have L := h.k1.kc.lay hF hp
  unfold copies
  refine WP.seq (WP.mono (copy_okM L (dst := (.r12, 0)) (src := sc oHX) (n := 32) (by decide)
    (by layd)) fun s₁ ⟨⟨hP₁, hb₁⟩, hx₁⟩ => ?_)
  have L₁ := L.post hP₁.b (kgB_bases p)
  refine WP.seq (WP.mono (copy_okM L₁ (dst := (.r13, 0)) (src := sc oHX) (n := 32) (by decide)
    (by layd)) fun s₂ ⟨⟨hP₂, hb₂⟩, hx₂⟩ => ?_)
  have L₂ := L₁.post hP₂.b (kgB_bases p)
  refine WP.mono (copy_okM L₂ (dst := (.r13, 32)) (src := sc (oHX + 96)) (n := 32) (by decide)
    (by layd)) fun s₃ ⟨⟨hP₃, hb₃⟩, hx₃⟩ => ?_
  have hP := PPostB.app (PPostB.app hP₁.b hP₂.b (r13_bases _ _)) hP₃.b (r13_bases _ _)
  have hx : MX s₃ = MX s := hx₃.trans (hx₂.trans hx₁)
  have h15 : s₃.gpr .r15 = s.gpr .r15 := by
    rw [hP₃.cs .r15 (by decide), hP₂.cs .r15 (by decide), hP₁.cs .r15 (by decide)]
  obtain ⟨A, S, hA, hS, hG⟩ := h.ex
  have hc : kcChk p ([((.r12, 0), 32)] ++ [((.r13, 0), 32)] ++ [((.r13, 32), 32)]) = true ∧
      (∀ e < p.k * p.ℓ, keepB (kgB p) ([((.r12, 0), 32)] ++ [((.r13, 0), 32)] ++ [((.r13, 32), 32)]) (aP e) 1024 = true) ∧
      (∀ r < p.ℓ + p.k, keepB (kgB p) ([((.r12, 0), 32)] ++ [((.r13, 0), 32)] ++ [((.r13, 32), 32)]) (sP p r) 1024
        = true) := by
    exact ⟨by layd, fun _ _ => by layd, fun _ _ => by layd⟩
  -- The bytes of `HX`, and `ρ`, `K`.
  have hHX₁ : bytesAt s₁.mem (pa s₁ (sc oHX)) 128 = hxOf p σ := by rw [L.keepBytes hP₁.b (by layd)]; exact h.k1.hx
  have hHX₂ : bytesAt s₂.mem (pa s₂ (sc oHX)) 128 = hxOf p σ := by
    rw [L₁.keepBytes hP₂.b (by layd)]; exact hHX₁
  have e1 : bytesAt s.mem (pa s (sc oHX)) 32 = rhoOf p σ := by
    rw [rho_eq, ← h.k1.hx, Proof.MlKem.bytesAt_take _ _ (show 32 ≤ 128 by decide)]
  have e1' : bytesAt s₁.mem (pa s₁ (sc oHX)) 32 = rhoOf p σ := by
    rw [rho_eq, ← hHX₁, Proof.MlKem.bytesAt_take _ _ (show 32 ≤ 128 by decide)]
  have e2 : bytesAt s₂.mem (pa s₂ (sc (oHX + 96))) 32 = kOf p σ := by
    rw [kOf_eq, ← hHX₂, Proof.MlKem.bytesAt_slice _ _ (show 96 + 32 ≤ 128 by decide), pa, pa, off_add]
  refine ⟨A, S, s.gpr .r15, ⟨h.k1.kc.step hF hp hP hx hc.1, h15, hG, fun r hr => (hS r hr).2,
    fun e he => polyIs_frame' L hP (hc.2.1 e he) (hA e he),
    fun i hi => polyIs_frame' L hP (hc.2.2 _ (by omega_using [hi])) (hS (p.ℓ + i) (by omega_using [hi])).1,
    fun j hj => by rw [ifn (Nat.not_lt_zero j)]; exact polyIs_frame' L hP (hc.2.2 j (by omega_using [hj])) (hS j (by omega_using [hj])).1,
    ?_, ?_, ?_, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩
  · rw [L₂.keepBytes hP₃.b (by layd),
      L₁.keepBytes hP₂.b (by layd),
      hP₁.pa (by decide), hb₁, e1]
  · rw [L₂.keepBytes hP₃.b (by layd),
      hP₂.pa (by decide), hb₂, e1']
  · rw [hP₃.pa (by decide), hb₃, e2]

theorem copies_piece {p : Params} (hF : PFacts p) :
    Piece p (fun σ s => KSamp p σ (p.k * p.ℓ) (p.ℓ + p.k) s) (KR0 p) copies :=
  ⟨fun _ _ hp h => copies_ok hF hp h,
    rel_of (Q := Two p) (taintRel [.rbx, .r12, .r13] (fun x y h r hr => h.regs r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> decide)) (by taint_decide))
      fun _ _ _ _ p₁ p₂ pub h₁ h₂ => kc_two hF p₁ p₂ pub h₁.k1.kc h₂.k1.kc⟩

end VG.Proof.MlDsa.X86_64.KeyGen

end

end

/-!
# ML-DSA key generation on x86-64: `s₁ ‖ s₂` to `sk`, and `ŝ₁`

Each entry of `s₁ ‖ s₂`, `BitPack`ed to `sk` (`packS_piece`), then `ŝ₁[j] =
NTT(s₁[j])` in place (`nttS_piece`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.KeyGen

open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.MlKem.X86_64 (Ptr sc)
open VG.Impl.MlDsa.X86_64.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt bitPack)
open VG.Proof.MlDsa (polyAt coeffAt Reduced PolyIs)
open VG.Spec.Sha3 (bytesAt)

/-! ## The coefficients of a small polynomial -/

theorem coeff_val {m : Mem} {q : Addr} {f : Poly} (h : PolyIs m q f) {i : Nat} (hi : i < 256) :
    (coeffAt m q i).toNat = (f[i]'hi).val := by
  have e := congrArg (fun g : Poly => (g[i]'hi).val) h.2
  simp only [polyAt, Vector.getElem_ofFn, Fin.val_ofNat] at e
  rw [← e, Nat.mod_eq_of_lt (h.1 i hi)]

theorem small_mem {η : Nat} {x : IPoly} (h : Small η x) {i : Nat} (hi : i < 256) :
    -(η : Int) ≤ x[i] ∧ x[i] ≤ η := h _ (Vector.mem_toList_iff.mpr (Vector.getElem_mem hi))

theorem packIn_of {m : Mem} {q : Addr} {η : Nat} (hη : η ≤ 4) {x : IPoly} (h : PolyIs m q (toRq x))
    (hs : Small η x) : PackIn m q η η := by
  refine ⟨h.1, fun i hi => ?_⟩
  have hx := small_mem hs hi
  rw [coeff_val h hi]
  simp only [toRq, Vector.getElem_map]
  rw [Proof.MlDsa.KeyGen.modPm_ofInt (by omega) (by omega)]
  exact hx

theorem small_big {η : Nat} (hη : η ≤ 4) {x : IPoly} (hs : Small η x) :
    ∀ c ∈ x.toList, -4190208 ≤ c ∧ c ≤ 4190208 := fun c hc => by
  have := hs c hc; omega_arith

theorem eta_le {p : Params} (hF : PFacts p) : p.η ≤ 4 := by rcases hF.eta with ⟨h, _⟩ | ⟨h, _⟩ <;> omega_using [h]

theorem eta_params {p : Params} (hF : PFacts p) : (p.η, p.η) ∈ Proof.MlDsa.bitPackParams := by
  rcases hF.eta with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> decide

theorem lenS_eq (p : Params) : lenS p = 32 * Spec.MlDsa.bitlen (p.η + p.η) := by
  rw [lenS, Nat.two_mul]

/-- The entry `r` of `s₁ ‖ s₂`, before `NTT`. -/
theorem KR.sPoly {p : Params} {σ : State} {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {np nr : Nat} {s : State}
    (h : KR p σ A S R np 0 nr s) {r : Nat} (hr : r < p.ℓ + p.k) : PolyIs s.mem (pa s (sP p r)) (toRq (S r)) := by
  by_cases hl : r < p.ℓ
  · have := h.s1 r hl; rwa [ifn (Nat.not_lt_zero r)] at this
  · have := h.s2 (r - p.ℓ) (by omega_using [hr, hl]); rwa [show p.ℓ + (r - p.ℓ) = r by omega_using [hl]] at this

/-! ## `BitPack` of `s₁ ‖ s₂` -/

theorem chk_packS {p : Params} (hF : PFacts p) {r : Nat} (hr : r < p.ℓ + p.k) :
    KRChk p r 0 0 [((.r13, 128 + lenS p * r), lenS p)] := by
  have hle : 128 + lenS p * r + lenS p ≤ oT0 p := by
    simp only [oT0]; rw [Nat.add_assoc, ← Nat.mul_succ]; exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hr) _
  exact KRChk.r13 hF (Nat.le_of_lt hr) (Nat.zero_le _) (by omega_using []) (.inr (Nat.le_refl _)) (.inl hle)
    (by rw [hF.sk]; omega_using [hle])

theorem packS_ok {P : Prims} (hP : PrimsOk P) {p : Params} (hF : PFacts p) {σ : State} (hp : (kgK p).pre σ)
    {r : Nat} (hr : r < p.ℓ + p.k) {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : KR p σ A S R r 0 0 s) : WP isa (packS P p r) s (KR p σ A S R (r + 1) 0 0) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have S₀ := h.kc.site hF hp
  have hS := h.sPoly hr
  unfold packS
  rcases hF.eta with ⟨he, hlen⟩ | ⟨he, hlen⟩ <;>
  refine WP.mono (bpAt_ok (eta_params hF) (lenS_eq p) (sc_ok _ (by simp only [oP]; omega_using [hr, hkl, hl, hk]))
    ⟨by rw [hlen]; omega, show Reg.r13 ∉ MlKem.X86_64.argRegs by decide⟩ (by layd)
    (by layd) hP.bitPack S₀ (packIn_of (eta_le hF) hS (h.small r hr)))
    fun s' ⟨hP', hx, hb⟩ => ?_ <;>
  · have hP'' : PPostB s s' [((.r13, 128 + lenS p * r), lenS p)] := hP'.b
    have hk' := h.keep hF hp hP'' hx (hP'.cs .r15 (by decide)) (chk_packS hF hr)
    refine ⟨hk'.kc, hk'.r15, hk'.good, hk'.small, hk'.aS, hk'.s2, hk'.s1, hk'.pk0, hk'.sk0, hk'.sk1,
      fun r' hr' => ?_, hk'.rows⟩
    rcases (by omega_using [hr'] : r' < r ∨ r' = r) with hr' | rfl
    · exact hk'.packs r' hr'
    · rw [hP'.pa (show Reg.r13 ∈ calleeSaved by decide), hb, hS.2, Proof.MlDsa.KeyGen.modPm_toRq (small_big (eta_le hF) (h.small r' hr))]

/-- The states after the copies, and the first `np` entries packed, `nj` in the NTT domain and `nr` rows. -/
abbrev KRx (p : Params) (np nj nr : Nat) (σ s : State) : Prop := ∃ A S R, KR p σ A S R np nj nr s

theorem packS_tr {P : Prims} (hP : PrimsOk P) {p : Params} (hF : PFacts p) {r : Nat} (hr : r < p.ℓ + p.k) :
    RelCT isa (R p (KRx p r 0 0)) (packS P p r) fun _ _ => True := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  refine rel_of (Q := fun x y => Two p x y ∧ PackIn x.mem (pa x (sP p r)) p.η p.η ∧
    PackIn y.mem (pa y (sP p r)) p.η p.η) ?_ fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ =>
      ⟨kc_two hF p₁ p₂ pub h₁.kc h₂.kc, packIn_of (eta_le hF) (h₁.sPoly hr) (h₁.small r hr),
        packIn_of (eta_le hF) (h₂.sPoly hr) (h₂.small r hr)⟩
  unfold packS
  rcases hF.eta with ⟨he, hlen⟩ | ⟨he, hlen⟩ <;>
  exact bpAt_tr (eta_params hF) (lenS_eq p) (sc_ok _ (by simp only [oP]; omega_using [hr, hkl, hl, hk]))
    ⟨by rw [hlen]; omega, show Reg.r13 ∉ MlKem.X86_64.argRegs by decide⟩ (by layd)
    (by layd) hP.bitPack (show Reg.rbx ∈ kgRegs by decide) (show Reg.r13 ∈ kgRegs by decide)

theorem packS_piece {P : Prims} (hP : PrimsOk P) {p : Params} (hF : PFacts p) {r : Nat} (hr : r < p.ℓ + p.k) :
    Piece p (KRx p r 0 0) (KRx p (r + 1) 0 0) (packS P p r) :=
  ⟨fun _ _ hp ⟨A, S, R, h⟩ => WP.mono (packS_ok hP hF hp hr h) fun _ h => ⟨A, S, R, h⟩, packS_tr hP hF hr⟩

/-! ## `NTT` of `s₁` -/

theorem nttS_ok {P : Prims} (hP : PrimsOk P) {p : Params} (hF : PFacts p) {σ : State} (hp : (kgK p).pre σ)
    {j : Nat} (hj : j < p.ℓ) {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : KR p σ A S R (p.ℓ + p.k) j 0 s) : WP isa (nttS P p j) s (KR p σ A S R (p.ℓ + p.k) (j + 1) 0) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have S₀ := h.kc.site hF hp
  have hS := h.s1 j hj
  rw [ifn (Nat.lt_irrefl j)] at hS
  unfold nttS nttAt
  refine WP.mono (ipAt_ok (t := ntt) (f := sP p j) (sc_ok _ (by simp only [oP]; omega_using [hj, hkl, hl])) (by layd) (by layd) (by layd)
    hP.ntt S₀ hS.1) fun s' ⟨hP', hx, hb⟩ => ?_
  have hP'' : PPostB s s' [(sP p j, 1024), (sc VG.Impl.MlKem.X86_64.oSS, 1024)] := hP'.b
  have L := S₀.lay
  have hlen : lenS p = 96 ∨ lenS p = 128 := hF.eta.imp And.right And.right
  exact ⟨h.kc.step hF hp hP'' hx (by layd), (hP'.cs .r15 (by decide)).trans h.r15, h.good,
    h.small, fun e he => polyIs_frame' L hP'' (by layd) (h.aS e he),
    fun i hi => polyIs_frame' L hP'' (by layd) (h.s2 i hi),
    fun j' hj' => if e : j' = j then by
        subst e; rw [ifp (Nat.lt_succ_self j'), hP''.pa (p := sP p j') rbx_bases, ← hS.2]; exact hb
      else by
        have := polyIs_frame' L hP'' (by layd) (h.s1 j' hj')
        by_cases hlt : j' < j
        · rwa [ifp hlt, ← ifp (show j' < j + 1 by omega_using [hlt]) (ntt (toRq (S j'))) (toRq (S j'))] at this
        · rwa [ifn hlt, ← ifn (show ¬ j' < j + 1 by omega_using [e, hlt]) (ntt (toRq (S j'))) (toRq (S j'))] at this,
    by rw [L.keepBytes hP'' (by layd)]; exact h.pk0,
    by rw [L.keepBytes hP'' (by layd)]; exact h.sk0,
    by rw [L.keepBytes hP'' (by layd)]; exact h.sk1,
    fun r hr => by
      rw [L.keepBytes hP'' (by rcases hlen with hlen | hlen <;> layk [hF.pk, hF.sk, hlen])]; exact h.packs r hr,
    fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem nttS_tr {P : Prims} (hP : PrimsOk P) {p : Params} (hF : PFacts p) {j : Nat} (hj : j < p.ℓ) :
    RelCT isa (R p (KRx p (p.ℓ + p.k) j 0)) (nttS P p j) fun _ _ => True := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  refine rel_of (Q := fun x y => Two p x y ∧ Reduced x.mem (pa x (sP p j)) ∧ Reduced y.mem (pa y (sP p j))) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ => ⟨kc_two hF p₁ p₂ pub h₁.kc h₂.kc, (h₁.s1 j hj).1,
      (h₂.s1 j hj).1⟩
  unfold nttS nttAt
  exact ipAt_tr (t := ntt) (f := sP p j) (sc_ok _ (by simp only [oP]; omega_using [hj, hkl, hl])) (by layd) (by layd) (by layd) hP.ntt
    (show Reg.rbx ∈ kgRegs by decide)

theorem nttS_piece {P : Prims} (hP : PrimsOk P) {p : Params} (hF : PFacts p) {j : Nat} (hj : j < p.ℓ) :
    Piece p (KRx p (p.ℓ + p.k) j 0) (KRx p (p.ℓ + p.k) (j + 1) 0) (nttS P p j) :=
  ⟨fun _ _ hp ⟨A, S, R, h⟩ => WP.mono (nttS_ok hP hF hp hj h) fun _ h => ⟨A, S, R, h⟩, nttS_tr hP hF hj⟩

end VG.Proof.MlDsa.X86_64.KeyGen

end

end

/-!
# ML-DSA key generation on x86-64: the rows of `t`

Row `i` of `t`: `NTT⁻¹` of the sum of the products `Â[i, j] ŝ₁[j]` in `t`, in
one call (`dot_ok`), plus `s₂[i]` (`addS2_ok`), then
`Power2Round` (`p2r_ok`) and `t₁[i]` packed to `pk` and `t₀[i]` to `sk`
(`sbp_ok`, `bp_ok`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.KeyGen

open VG.Proof.MlDsa.Arith.Representation

open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.MlKem.X86_64 (Ptr sc seqR)
open VG.Impl.MlDsa.X86_64.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt nttInv add multiplyNTT bitPack simpleBitPack power2Round ofInt)
open VG.Proof.MlDsa (polyAt natPolyAt coeffAt Reduced PolyIs NatPolyIs)
open VG.Proof.MlDsa.KeyGen (dotK tK t1K t0K)
open VG.Spec.Sha3 (bytesAt)

theorem idx_lt {p : Params} {i j : Nat} (hi : i < p.k) (hj : j < p.ℓ) : p.ℓ * i + j < p.k * p.ℓ := by
  have := Nat.mul_le_mul_left p.ℓ (show i + 1 ≤ p.k by omega_arith)
  rw [Nat.mul_succ, Nat.mul_comm p.ℓ p.k] at this
  omega_arith

/-- The `t` so far. -/
abbrev tIs (p : Params) (g : (Nat → Poly) → (Nat → IPoly) → Poly) (A : Nat → Poly) (S : Nat → IPoly) (s : State) :
    Prop := PolyIs s.mem (pa s (tP p)) (g A S)

theorem KR.polyA {p : Params} {σ : State} {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {np nj nr : Nat}
    {s : State} (h : KR p σ A S R np nj nr s) {i j : Nat} (hi : i < p.k) (hj : j < p.ℓ) :
    PolyIs s.mem (pa s (aP (p.ℓ * i + j))) (A (p.ℓ * i + j)) := h.aS _ (idx_lt hi hj)

theorem KR.polyS {p : Params} {σ : State} {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {np nr : Nat}
    {s : State} (h : KR p σ A S R np p.ℓ nr s) {j : Nat} (hj : j < p.ℓ) :
    PolyIs s.mem (pa s (sP p j)) (ntt (toRq (S j))) := by
  have := h.s1 j hj; rwa [ifp hj] at this

theorem famP_sc (b j : Nat) : famP (sc (oP b)) j = sc (oP (b + j)) := by
  simp only [famP, sc, oP, Nat.mul_add, Nat.add_assoc]

/-- Entry `j` of row `i` of `Â`, as polynomial `j` of the row. -/
theorem KR.famA {p : Params} {σ : State} {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {np nj nr : Nat}
    {s : State} (h : KR p σ A S R np nj nr s) {i j : Nat} (hi : i < p.k) (hj : j < p.ℓ) :
    PolyIs s.mem (pa s (famP (aP (p.ℓ * i)) j)) (A (p.ℓ * i + j)) := by
  rw [famP_sc]; exact h.aS _ (idx_lt hi hj)

/-- `ŝ₁[j]`, as polynomial `j` of `ŝ₁`. -/
theorem KR.famS {p : Params} {σ : State} {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {np nr : Nat}
    {s : State} (h : KR p σ A S R np p.ℓ nr s) {j : Nat} (hj : j < p.ℓ) :
    PolyIs s.mem (pa s (famP (sP p 0) j)) (ntt (toRq (S j))) := by
  rw [famP_sc, Nat.add_zero]; exact h.polyS hj

theorem l457 {p : Params} (hF : PFacts p) : p.ℓ = 4 ∨ p.ℓ = 5 ∨ p.ℓ = 7 := by
  rcases hF.mem with rfl | rfl | rfl <;> decide

theorem tP_ok {p : Params} (hF : PFacts p) : PtrOk (tP p) :=
  sc_ok _ (by have := hF.kl; have := hF.l; have := hF.k; simp only [oP]; omega_arith)

theorem tP1_ok {p : Params} (hF : PFacts p) : PtrOk (t1P p) :=
  sc_ok _ (by have := hF.kl; have := hF.l; have := hF.k; simp only [oP]; omega_arith)

theorem tP0_ok {p : Params} (hF : PFacts p) : PtrOk (t0P p) :=
  sc_ok _ (by have := hF.kl; have := hF.l; have := hF.k; simp only [oP]; omega_arith)

theorem modPm_t0 (t : Poly) :
    ((t.map fun c => ofInt (power2Round c).2).map fun c => Spec.MlDsa.modPm c.val Spec.MlDsa.q) =
      t.map fun c => (power2Round c).2 := by
  rw [Vector.map_map]
  refine Vector.map_congr_left fun c _ => ?_
  have := Proof.MlDsa.KeyGen.power2Round_snd c
  exact Proof.MlDsa.KeyGen.modPm_ofInt (by omega_arith) (by omega_arith)

theorem packIn_t0 {m : Mem} {q : Addr} {t : Poly} (h : PolyIs m q (t.map fun c => ofInt (power2Round c).2)) :
    PackIn m q 4095 4096 := by
  refine ⟨h.1, fun j hj => ?_⟩
  rw [coeff_val h hj]
  simp only [Vector.getElem_map]
  have := Proof.MlDsa.KeyGen.power2Round_snd (t[j]'hj)
  rw [Proof.MlDsa.KeyGen.modPm_ofInt (by omega_arith) (by omega_arith)]
  omega_arith

/-! ## The checks of the writes of a row, once each -/

/-- Polynomial `j` of `scratch` after `s₁ ‖ s₂`. -/
theorem chk_poly {p : Params} (hF : PFacts p) {i : Nat} (hi : i < p.k) {j : Nat} (hj : j < 3) :
    KRChk p (p.ℓ + p.k) p.ℓ i [(sc (oP (p.k * p.ℓ + p.ℓ + p.k + j)), 1024)] := by
  have := hF.k; have := hF.l; have := hF.kl
  exact KRChk.rbx hF (by omega_arith) (by omega_arith) (.inr (by simp only [VG.Impl.MlKem.X86_64.oSV, oP]; omega_arith))
    (.inr (by simp only [oP]; omega_arith)) (by simp only [scrLen, Spec.MlDsa.scratchWords, oP]; omega_arith)

theorem chk_t {p : Params} (hF : PFacts p) {i : Nat} (hi : i < p.k) : KRChk p (p.ℓ + p.k) p.ℓ i [(tP p, 1024)] := by
  have := chk_poly hF hi (j := 0) (by decide); rwa [Nat.add_zero] at this

theorem chk_inv {p : Params} (hF : PFacts p) {i : Nat} (hi : i < p.k) :
    KRChk p (p.ℓ + p.k) p.ℓ i [(tP p, 1024), (sc VG.Impl.MlKem.X86_64.oSS, 1024)] := by
  have := hF.k; have := hF.l; have := hF.kl
  exact (chk_t hF hi).append (ws₁ := [_]) (KRChk.rbx (o := VG.Impl.MlKem.X86_64.oSS) (n := 1024) hF (by omega_arith)
    (by omega_arith) (.inr (by decide)) (.inl (by decide))
    (by simp only [scrLen, Spec.MlDsa.scratchWords, VG.Impl.MlKem.X86_64.oSS]; omega_arith))

theorem chk_p2r {p : Params} (hF : PFacts p) {i : Nat} (hi : i < p.k) :
    KRChk p (p.ℓ + p.k) p.ℓ i [(t1P p, 1024), (t0P p, 1024)] :=
  (chk_poly hF hi (j := 1) (by decide)).append (ws₁ := [_]) (chk_poly hF hi (j := 2) (by decide))

theorem chk_sbp {p : Params} (hF : PFacts p) {i : Nat} (hi : i < p.k) :
    KRChk p (p.ℓ + p.k) p.ℓ i [((.r12, 32 + 320 * i), 320)] :=
  KRChk.r12 hF (Nat.le_refl _) (Nat.le_of_lt hi) (Nat.le_refl _) (by rw [hF.pk]; omega_arith)

theorem chk_bp {p : Params} (hF : PFacts p) {i : Nat} (hi : i < p.k) :
    KRChk p (p.ℓ + p.k) p.ℓ i [((.r13, oT0 p + 416 * i), 416)] := by
  have := hF.k; have := hF.l
  refine KRChk.r13 hF (Nat.le_refl _) (Nat.le_of_lt hi) (by simp only [oT0]; omega_arith) (.inr (by simp only [oT0]; omega_arith))
    (.inr (Nat.le_refl _)) (by rw [hF.sk]; omega_arith)

section
variable {P : Prims} (hP : PrimsOk P) {p : Params} (hF : PFacts p) {σ : State} (hp : (kgK p).pre σ) {i : Nat}
  (hi : i < p.k)
include hP hF hp hi


/-- `t = NTT⁻¹(Σⱼ Â[i, j] ŝ₁[j])`. -/
theorem dot_ok {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State} (h : KR p σ A S R (p.ℓ + p.k) p.ℓ i s) :
    WP isa (dotInvAt P.asfx (P.dotInv p.ℓ) p.ℓ (tP p) (aP (p.ℓ * i)) (sP p 0)) s fun s' =>
      KR p σ A S R (p.ℓ + p.k) p.ℓ i s' ∧ tIs p (fun A S => nttInv (dotK p A S i p.ℓ)) A S s' := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hx0 := idx_lt (j := 0) hi (by omega_arith)
  rw [Nat.add_zero] at hx0
  have S₀ := h.kc.site hF hp
  refine WP.mono (dotInvAt_ok (tP_ok hF) (sc_ok _ (by simp only [oP]; omega_arith))
    (sc_ok _ (by simp only [oP]; omega_arith)) (by layd) (hP.dotInv p.ℓ (l457 hF)) S₀
    (fun j hj => (h.famA hi hj).1) (fun j hj => (h.famS hj).1)) fun s' ⟨hP', hx, hb⟩ => ?_
  have hP'' : PPostB s s' [(tP p, 1024), (sc VG.Impl.MlKem.X86_64.oSS, 1024)] := hP'.b
  refine ⟨h.keep hF hp hP'' hx (hP'.cs .r15 (by decide)) (chk_inv hF hi), ?_⟩
  rw [tIs, hP''.pa (p := tP p) rbx_bases]
  have he : Proof.MlDsa.dotNTT (fun j => polyAt s.mem (pa s (famP (aP (p.ℓ * i)) j)))
      (fun j => polyAt s.mem (pa s (famP (sP p 0) j))) p.ℓ = dotK p A S i p.ℓ := by
    unfold Proof.MlDsa.dotNTT dotK
    refine congrArg (List.foldl Spec.MlDsa.add Spec.MlDsa.zero) (List.map_congr_left fun j hj => ?_)
    rw [List.mem_range] at hj
    dsimp only
    rw [(h.famA hi hj).2, (h.famS hj).2]
  rwa [he] at hb

/-- `t = t + s₂[i]`. -/
theorem addS2_ok {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : KR p σ A S R (p.ℓ + p.k) p.ℓ i s) (ht : tIs p (fun A S => nttInv (dotK p A S i p.ℓ)) A S s) :
    WP isa (addAt P.asfx P.add (tP p) (sP p (p.ℓ + i))) s fun s' =>
      KR p σ A S R (p.ℓ + p.k) p.ℓ i s' ∧ tIs p (fun A S => tK p A S i) A S s' := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  dsimp only [tIs] at ht
  have S₀ := h.kc.site hF hp
  have hS := h.s2 i hi
  refine WP.mono (addAt_ok (tP_ok hF) (sc_ok _ (by simp only [oP]; omega_arith)) (by layd) (by layd) hP.add S₀ ht.1 hS.1)
    fun s' ⟨hP', hx, hb⟩ => ?_
  have hP'' : PPostB s s' [(tP p, 1024)] := hP'.b
  refine ⟨h.keep hF hp hP'' hx (hP'.cs .r15 (by decide)) (chk_t hF hi), ?_⟩
  rw [tIs, hP''.pa (p := tP p) rbx_bases, Proof.MlDsa.KeyGen.tK, ← hS.2, ← ht.2]
  exact hb

/-- `Power2Round` of `t`. -/
theorem p2r_ok {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : KR p σ A S R (p.ℓ + p.k) p.ℓ i s) (ht : tIs p (fun A S => tK p A S i) A S s) :
    WP isa (power2RoundAt P.power2Round (tP p) (t1P p) (t0P p)) s fun s' =>
      KR p σ A S R (p.ℓ + p.k) p.ℓ i s' ∧ NatPolyIs s'.mem (pa s' (t1P p)) (t1K p A S i) ∧
      PolyIs s'.mem (pa s' (t0P p)) ((tK p A S i).map fun c => ofInt (power2Round c).2) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  dsimp only [tIs] at ht
  have S₀ := h.kc.site hF hp
  refine WP.mono (p2rAt_ok (tP_ok hF) (tP1_ok hF) (tP0_ok hF) (by layd) (by layd) (by layd) (by layd) (by layd)
    hP.power2Round S₀ ht.1) fun s' ⟨hP', hx, h1, h0⟩ => ?_
  have hP'' : PPostB s s' [(t1P p, 1024), (t0P p, 1024)] := hP'.b
  refine ⟨h.keep hF hp hP'' hx (hP'.cs .r15 (by decide)) (chk_p2r hF hi), ?_, ?_⟩
  · rw [hP''.pa (p := t1P p) rbx_bases, Proof.MlDsa.KeyGen.t1K, ← ht.2]; exact h1
  · rw [hP''.pa (p := t0P p) rbx_bases, ← ht.2]; exact h0

/-- `t₁[i]` to `pk`. -/
theorem sbp_ok {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : KR p σ A S R (p.ℓ + p.k) p.ℓ i s) (h1 : NatPolyIs s.mem (pa s (t1P p)) (t1K p A S i))
    (h0 : PolyIs s.mem (pa s (t0P p)) ((tK p A S i).map fun c => ofInt (power2Round c).2)) :
    WP isa (simpleBitPackAt P.simpleBitPack (t1P p) 1023 (.r12, 32 + 320 * i) 320) s fun s' =>
      KR p σ A S R (p.ℓ + p.k) p.ℓ i s' ∧
      PolyIs s'.mem (pa s' (t0P p)) ((tK p A S i).map fun c => ofInt (power2Round c).2) ∧
      bytesAt s'.mem (pa s' (.r12, 32 + 320 * i)) 320 = simpleBitPack (t1K p A S i) 1023 := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have S₀ := h.kc.site hF hp
  have L := S₀.lay
  refine WP.mono (sbpAt_ok (by decide) (by decide) (tP1_ok hF)
    ⟨by omega_arith, show Reg.r12 ∉ MlKem.X86_64.argRegs by decide⟩ (by layd) (by layd) hP.simpleBitPack S₀
    fun j hj => ?_) fun s' ⟨hP', hx, hb⟩ => ?_
  · rw [show (coeffAt s.mem (pa s (t1P p)) j).toNat = (t1K p A S i)[j]'hj from by
      rw [← h1]; simp only [Proof.MlDsa.natPolyAt, Vector.getElem_ofFn]]
    simp only [Proof.MlDsa.KeyGen.t1K, Vector.getElem_map]
    have := Proof.MlDsa.KeyGen.power2Round_fst ((tK p A S i)[j]'hj)
    omega_arith
  · have hP'' : PPostB s s' [((.r12, 32 + 320 * i), 320)] := hP'.b
    refine ⟨h.keep hF hp hP'' hx (hP'.cs .r15 (by decide)) (chk_sbp hF hi),
      polyIs_frame' L hP'' (by layd) h0, ?_⟩
    rw [hP''.pa (p := (.r12, 32 + 320 * i)) (show Reg.r12 ∈ bases by decide), hb, h1]

/-- `t₀[i]` to `sk`. -/
theorem bp_ok {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : KR p σ A S R (p.ℓ + p.k) p.ℓ i s)
    (h0 : PolyIs s.mem (pa s (t0P p)) ((tK p A S i).map fun c => ofInt (power2Round c).2))
    (h1 : bytesAt s.mem (pa s (.r12, 32 + 320 * i)) 320 = simpleBitPack (t1K p A S i) 1023) :
    WP isa (bitPackAt P.bitPack (t0P p) 4095 4096 (.r13, oT0 p + 416 * i) 416) s
      (KR p σ A S R (p.ℓ + p.k) p.ℓ (i + 1)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have S₀ := h.kc.site hF hp
  have L := S₀.lay
  have hlen : lenS p = 96 ∨ lenS p = 128 := hF.eta.imp And.right And.right
  refine WP.mono (bpAt_ok (by decide) (by decide) (tP0_ok hF)
    ⟨by rcases hlen with hl | hl <;> simp only [oT0, hl] <;> omega_arith,
      show Reg.r13 ∉ MlKem.X86_64.argRegs by decide⟩ (by layd)
    (by layd) hP.bitPack S₀ (packIn_t0 h0)) fun s' ⟨hP', hx, hb⟩ => ?_
  have hP'' : PPostB s s' [((.r13, oT0 p + 416 * i), 416)] := hP'.b
  have hk' := h.keep hF hp hP'' hx (hP'.cs .r15 (by decide)) (chk_bp hF hi)
  refine ⟨hk'.kc, hk'.r15, hk'.good, hk'.small, hk'.aS, hk'.s2, hk'.s1, hk'.pk0, hk'.sk0, hk'.sk1, hk'.packs,
    fun i' hi' => ?_⟩
  rcases (by omega_arith : i' < i ∨ i' = i) with hi' | rfl
  · exact hk'.rows i' hi'
  · refine ⟨by rw [L.keepBytes hP'' (by layd)]; exact h1, ?_⟩
    rw [hP''.pa (p := (.r13, oT0 p + 416 * i')) (show Reg.r13 ∈ bases by decide), hb, h0.2, modPm_t0]
    rfl

end

theorem t1_bound {m : Mem} {q : Addr} {p : Params} {A : Nat → Poly} {S : Nat → IPoly} {i : Nat}
    (h1 : NatPolyIs m q (t1K p A S i)) : ∀ j < 256, (coeffAt m q j).toNat ≤ 1023 := fun j hj => by
  rw [show (coeffAt m q j).toNat = (t1K p A S i)[j]'hj from by
    rw [← h1]; simp only [Proof.MlDsa.natPolyAt, Vector.getElem_ofFn]]
  simp only [Proof.MlDsa.KeyGen.t1K, Vector.getElem_map]
  have := Proof.MlDsa.KeyGen.power2Round_fst ((Proof.MlDsa.KeyGen.tK p A S i)[j]'hj)
  omega_arith

/-! ## The pieces of a row -/

/-- In row `i`, with `f` holding of the memory. -/
abbrev RowI (p : Params) (i : Nat) (f : (Nat → Poly) → (Nat → IPoly) → State → Prop) (σ s : State) : Prop :=
  ∃ A S R, KR p σ A S R (p.ℓ + p.k) p.ℓ i s ∧ f A S s

section
variable {P : Prims} (hP : PrimsOk P) {p : Params} (hF : PFacts p) {i : Nat} (hi : i < p.k)
include hP hF hi

theorem dot_piece : Piece p (KRx p (p.ℓ + p.k) p.ℓ i) (RowI p i (tIs p fun A S => nttInv (dotK p A S i p.ℓ)))
    (dotInvAt P.asfx (P.dotInv p.ℓ) p.ℓ (tP p) (aP (p.ℓ * i)) (sP p 0)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hx0 := idx_lt (j := 0) hi (by omega_arith)
  rw [Nat.add_zero] at hx0
  refine ⟨fun _ _ hp ⟨A, S, R, h⟩ => WP.mono (dot_ok hP hF hp hi h) fun _ h => ⟨A, S, R, h⟩, ?_⟩
  refine rel_of (Q := fun x y => Two p x y ∧
    ((∀ j < p.ℓ, Reduced x.mem (pa x (famP (aP (p.ℓ * i)) j))) ∧ ∀ j < p.ℓ, Reduced x.mem (pa x (famP (sP p 0) j))) ∧
    ((∀ j < p.ℓ, Reduced y.mem (pa y (famP (aP (p.ℓ * i)) j))) ∧ ∀ j < p.ℓ, Reduced y.mem (pa y (famP (sP p 0) j))))
    ?_ fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ =>
      ⟨kc_two hF p₁ p₂ pub h₁.kc h₂.kc, ⟨fun j hj => (h₁.famA hi hj).1, fun j hj => (h₁.famS hj).1⟩,
        ⟨fun j hj => (h₂.famA hi hj).1, fun j hj => (h₂.famS hj).1⟩⟩
  exact dotInvAt_tr (tP_ok hF) (sc_ok _ (by simp only [oP]; omega_arith)) (sc_ok _ (by simp only [oP]; omega_arith))
    (by layd) (hP.dotInv p.ℓ (l457 hF)) (show Reg.rbx ∈ kgRegs by decide) (show Reg.rbx ∈ kgRegs by decide)
    (show Reg.rbx ∈ kgRegs by decide)

theorem addS2_piece : Piece p (RowI p i (tIs p fun A S => nttInv (dotK p A S i p.ℓ)))
    (RowI p i (tIs p fun A S => Proof.MlDsa.KeyGen.tK p A S i)) (addAt P.asfx P.add (tP p) (sP p (p.ℓ + i))) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  refine ⟨fun _ _ hp ⟨A, S, R, h, ht⟩ => WP.mono (addS2_ok hP hF hp hi h ht) fun _ h => ⟨A, S, R, h⟩, ?_⟩
  refine rel_of (Q := fun x y => Two p x y ∧ (Reduced x.mem (pa x (tP p)) ∧ Reduced x.mem (pa x (sP p (p.ℓ + i)))) ∧
    (Reduced y.mem (pa y (tP p)) ∧ Reduced y.mem (pa y (sP p (p.ℓ + i))))) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩ =>
      ⟨kc_two hF p₁ p₂ pub h₁.kc h₂.kc, ⟨t₁.1, (h₁.s2 i hi).1⟩, ⟨t₂.1, (h₂.s2 i hi).1⟩⟩
  exact addAt_tr (tP_ok hF) (sc_ok _ (by simp only [oP]; omega_arith)) (by layd) (by layd) hP.add
    (show Reg.rbx ∈ kgRegs by decide) (show Reg.rbx ∈ kgRegs by decide)

/-- After `Power2Round`. -/
abbrev p2rIs (p : Params) (i : Nat) (A : Nat → Poly) (S : Nat → IPoly) (s : State) : Prop :=
  NatPolyIs s.mem (pa s (t1P p)) (t1K p A S i) ∧
    PolyIs s.mem (pa s (t0P p)) ((Proof.MlDsa.KeyGen.tK p A S i).map fun c => ofInt (power2Round c).2)

theorem p2r_piece : Piece p (RowI p i (tIs p fun A S => Proof.MlDsa.KeyGen.tK p A S i)) (RowI p i (p2rIs p i))
    (power2RoundAt P.power2Round (tP p) (t1P p) (t0P p)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  refine ⟨fun _ _ hp ⟨A, S, R, h, ht⟩ => WP.mono (p2r_ok hP hF hp hi h ht) fun _ h => ⟨A, S, R, h.1, h.2⟩, ?_⟩
  refine rel_of (Q := fun x y => Two p x y ∧ Reduced x.mem (pa x (tP p)) ∧ Reduced y.mem (pa y (tP p))) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩ => ⟨kc_two hF p₁ p₂ pub h₁.kc h₂.kc, t₁.1, t₂.1⟩
  exact p2rAt_tr (tP_ok hF) (tP1_ok hF) (tP0_ok hF) (by layd) (by layd) (by layd) (by layd) (by layd) hP.power2Round
    (show Reg.rbx ∈ kgRegs by decide) (show Reg.rbx ∈ kgRegs by decide) (show Reg.rbx ∈ kgRegs by decide)

/-- After `t₁[i]` to `pk`. -/
abbrev sbpIs (p : Params) (i : Nat) (A : Nat → Poly) (S : Nat → IPoly) (s : State) : Prop :=
  PolyIs s.mem (pa s (t0P p)) ((Proof.MlDsa.KeyGen.tK p A S i).map fun c => ofInt (power2Round c).2) ∧
    bytesAt s.mem (pa s (.r12, 32 + 320 * i)) 320 = simpleBitPack (t1K p A S i) 1023

theorem sbp_piece : Piece p (RowI p i (p2rIs p i)) (RowI p i (sbpIs p i))
    (simpleBitPackAt P.simpleBitPack (t1P p) 1023 (.r12, 32 + 320 * i) 320) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  refine ⟨fun _ _ hp ⟨A, S, R, h, h1, h0⟩ => WP.mono (sbp_ok hP hF hp hi h h1 h0) fun _ h => ⟨A, S, R, h⟩, ?_⟩
  refine rel_of (Q := fun x y => Two p x y ∧ (∀ j < 256, (coeffAt x.mem (pa x (t1P p)) j).toNat ≤ 1023) ∧
    (∀ j < 256, (coeffAt y.mem (pa y (t1P p)) j).toNat ≤ 1023)) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩ =>
      ⟨kc_two hF p₁ p₂ pub h₁.kc h₂.kc, t1_bound t₁.1, t1_bound t₂.1⟩
  exact sbpAt_tr (by decide) (by decide) (tP1_ok hF) ⟨by omega_arith, show Reg.r12 ∉ MlKem.X86_64.argRegs by decide⟩
    (by layd) (by layd) hP.simpleBitPack (show Reg.rbx ∈ kgRegs by decide)
    (show Reg.r12 ∈ kgRegs by decide)

theorem bp_piece : Piece p (RowI p i (sbpIs p i)) (KRx p (p.ℓ + p.k) p.ℓ (i + 1))
    (bitPackAt P.bitPack (t0P p) 4095 4096 (.r13, oT0 p + 416 * i) 416) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  refine ⟨fun _ _ hp ⟨A, S, R, h, h0, h1⟩ => WP.mono (bp_ok hP hF hp hi h h0 h1) fun _ h => ⟨A, S, R, h⟩, ?_⟩
  refine rel_of (Q := fun x y => Two p x y ∧ PackIn x.mem (pa x (t0P p)) 4095 4096 ∧
    PackIn y.mem (pa y (t0P p)) 4095 4096) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩ =>
      ⟨kc_two hF p₁ p₂ pub h₁.kc h₂.kc, packIn_t0 t₁.1, packIn_t0 t₂.1⟩
  have hlen : lenS p = 96 ∨ lenS p = 128 := hF.eta.imp And.right And.right
  exact bpAt_tr (by decide) (by decide) (tP0_ok hF)
    ⟨by rcases hlen with hl | hl <;> simp only [oT0, hl] <;> omega_arith,
      show Reg.r13 ∉ MlKem.X86_64.argRegs by decide⟩ (by layd)
    (by layd) hP.bitPack (show Reg.rbx ∈ kgRegs by decide) (show Reg.r13 ∈ kgRegs by decide)

end

end VG.Proof.MlDsa.X86_64.KeyGen
