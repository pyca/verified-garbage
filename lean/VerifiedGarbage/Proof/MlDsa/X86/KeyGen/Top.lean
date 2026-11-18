module

import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.NoSp
import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Samp
public import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Seeds
import VerifiedGarbage.Proof.MlDsa.DecideAt
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.MlKem.KPke
import VerifiedGarbage.Proof.Sha256.X86.Lit
import VerifiedGarbage.Proof.Sha3.X86.Lit
meta import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.NoSp
meta import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Samp
meta import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Seeds
meta import VerifiedGarbage.Proof.MlDsa.DecideAt
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.MlKem.KPke
meta import VerifiedGarbage.Proof.Sha256.X86.Lit
meta import VerifiedGarbage.Proof.Sha3.X86.Lit
import VerifiedGarbage.Proof.MlKem.X86.TopLocal
meta import VerifiedGarbage.Proof.MlKem.X86.TopLocal
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Prim
import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly
import VerifiedGarbage.Proof.MlKem.X86.Pack
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.MlDsa.Contract
public import VerifiedGarbage.Proof.MlDsa.KeyGen.Rest
meta import VerifiedGarbage.Proof.MlDsa.KeyGen.Rest
meta import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Prim
meta import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly
meta import VerifiedGarbage.Proof.MlKem.X86.Pack
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlDsa.Contract

/-! ### `MlDsa.X86.KeyGen.RestRow`, which only this module used -/

section

/-! ### `MlDsa.X86.KeyGen.RestPack`, which this module and modules that import it used -/

section

/-! ### `MlDsa.X86.KeyGen.RestBase`, which this module and modules that import it used -/

section

/-!
# ML-DSA key generation on x86 (32-bit): after the samplers

Once the samplers are done, with `Â` and `s₁ ‖ s₂` in memory as `A` and `S`
(`Good`), the rest of the function computes the keys from them, whatever they
are (`KR`): after the copies of `ρ` and `K` (`copies_piece`), the first `np`
entries of `s₁ ‖ s₂` packed to `sk`, the first `nj` of `s₁` in the NTT domain,
and the first `nr` rows of `t` packed to `pk` and `sk`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top
open VG.Impl.MlDsa.X86.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt bitPack simpleBitPack keyGenSeeds)
open VG.Proof.MlDsa (polyAt coeffAt Reduced PolyIs)
open VG.Proof.MlDsa.KeyGen (t1K t0K)
open VG.Spec.Sha3 (bytesAt)

/-- After the samplers: the keys from `A` and `S`, so far. -/
structure KR (p : Params) (A : Nat → Poly) (S : Nat → IPoly) (np nj nr : Nat) (s₀ s : State) : Prop where
  ctx : Ctx (YK p) s₀ s
  good : Good p s₀ (p.k * p.ℓ) (p.ℓ + p.k) A S (accV s₀ s)
  small : ∀ r < p.ℓ + p.k, Small p.η (S r)
  aS : ∀ e < p.k * p.ℓ, PolyIs s.mem (Buf.addr s₀ (aB e)) (A e)
  s2 : ∀ i < p.k, PolyIs s.mem (Buf.addr s₀ (sB p (p.ℓ + i))) (toRq (S (p.ℓ + i)))
  s1 : ∀ j < p.ℓ, PolyIs s.mem (Buf.addr s₀ (sB p j)) (if j < nj then ntt (toRq (S j)) else toRq (S j))
  pk0 : bytesAt s.mem (Buf.addr s₀ ⟨1, 0, 32⟩) 32 = rhoOf p s₀
  sk0 : bytesAt s.mem (Buf.addr s₀ ⟨2, 0, 32⟩) 32 = rhoOf p s₀
  sk1 : bytesAt s.mem (Buf.addr s₀ ⟨2, 32, 32⟩) 32 = kOf p s₀
  packs : ∀ r < np, bytesAt s.mem (Buf.addr s₀ ⟨2, 128 + lenS p * r, lenS p⟩) (lenS p) = bitPack (S r) p.η p.η
  rows : ∀ i < nr, bytesAt s.mem (Buf.addr s₀ ⟨1, 32 + 320 * i, 320⟩) 320 = simpleBitPack (t1K p A S i) 1023 ∧
    bytesAt s.mem (Buf.addr s₀ ⟨2, oT0 p + 416 * i, 416⟩) 416 = bitPack (t0K p A S i) 4095 4096

/-- The buffers of `KR` but the polynomials of `s₁` apart from `bs`. -/
structure SafeR (p : Params) (np nr : Nat) (bs : List Buf) : Prop where
  acc : (YK p).apart (sb oACC 4) bs = true
  aS : ∀ e < p.k * p.ℓ, (YK p).apart (aB e) bs = true
  s2 : ∀ i < p.k, (YK p).apart (sB p (p.ℓ + i)) bs = true
  pk0 : (YK p).apart ⟨1, 0, 32⟩ bs = true
  sk0 : (YK p).apart ⟨2, 0, 32⟩ bs = true
  sk1 : (YK p).apart ⟨2, 32, 32⟩ bs = true
  packs : ∀ r < np, (YK p).apart ⟨2, 128 + lenS p * r, lenS p⟩ bs = true
  rows : ∀ i < nr, (YK p).apart ⟨1, 32 + 320 * i, 320⟩ bs = true ∧ (YK p).apart ⟨2, oT0 p + 416 * i, 416⟩ bs = true

/-- Proves a `SafeR`, with the facts of the parameter set `hF`: each check decided for each
parameter set if it can be (`layd`). -/
tactic_template "safeR " hF:term:max : tactic => `(tactic| (
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> (try refine ⟨?_, ?_⟩) <;> first | layd | layp $hF []))

theorem apart_append {Y : Lay} {b : Buf} {bs₁ bs₂ : List Buf} (h₁ : Y.apart b bs₁ = true)
    (h₂ : Y.apart b bs₂ = true) : Y.apart b (bs₁ ++ bs₂) = true := by
  simp only [Lay.apart, List.all_append, Bool.and_eq_true] at *
  exact ⟨h₁.1, h₁.2, h₂.2⟩

/-- `SafeR` of two lists of buffers, for both. -/
theorem SafeR.append {p : Params} {np nr : Nat} {bs₁ bs₂ : List Buf} (h₁ : SafeR p np nr bs₁)
    (h₂ : SafeR p np nr bs₂) : SafeR p np nr (bs₁ ++ bs₂) :=
  ⟨apart_append h₁.acc h₂.acc, fun e he => apart_append (h₁.aS e he) (h₂.aS e he),
    fun i hi => apart_append (h₁.s2 i hi) (h₂.s2 i hi), apart_append h₁.pk0 h₂.pk0, apart_append h₁.sk0 h₂.sk0,
    apart_append h₁.sk1 h₂.sk1, fun r hr => apart_append (h₁.packs r hr) (h₂.packs r hr),
    fun i hi => ⟨apart_append (h₁.rows i hi).1 (h₂.rows i hi).1, apart_append (h₁.rows i hi).2 (h₂.rows i hi).2⟩⟩

/-! `SafeR` of one buffer, proved once for any buffer: each check is about the
buffer and one other, apart from it or in another argument. -/

theorem apart_one_same {Y : Lay} {b c : Buf} (hb : Y.ok b = true) (hc : Y.ok c = true) (ha : b.arg = c.arg)
    (h : b.off + b.len ≤ c.off ∨ c.off + c.len ≤ b.off) : Y.apart b [c] = true := by
  simp only [Lay.apart, Lay.sep, List.all_cons, List.all_nil, hb, hc, ha, ↓reduceIte, Bool.true_and,
    Bool.and_true, Bool.or_eq_true, decide_eq_true_eq]
  exact h

theorem apart_one_diff {Y : Lay} {b c : Buf} (hb : Y.ok b = true) (hc : Y.ok c = true) (ha : b.arg ≠ c.arg)
    (hw : Y.awr c.arg = true) : Y.apart b [c] = true := by
  simp only [Lay.apart, Lay.sep, List.all_cons, List.all_nil, hb, hc, ha, ↓reduceIte, hw, Bool.or_true,
    Bool.and_true]

theorem ykOk {p : Params} {a o l : Nat} (ha : a < 4) (hl : 0 < l) (h : o + l ≤ (YK p).alen a) :
    (YK p).ok ⟨a, o, l⟩ = true := by
  simp only [Lay.ok, YK_n, ha, hl, h, decide_true, Bool.and_self]

/-- Closes the arithmetic of a check of one buffer, in each case of `η` if it needs it. -/
tactic_template "safe1 " hF:term:max : tactic => `(tactic| (
                   try simp only [VG.Impl.MlDsa.X86.KeyGen.oACC, VG.Impl.MlDsa.X86.KeyGen.oP, VG.Impl.MlDsa.X86.KeyGen.oT0]
                   first
                     | omega_arith
                     | rcases ($hF).eta with ⟨_, e⟩ | ⟨_, e⟩ <;> simp only [e] at * <;> omega_arith))

/-- A buffer of `scratch` apart from the accumulator, `Â` and `s₂`. -/
theorem SafeR.sc {p : Params} (hF : PFacts p) {np nr : Nat} (hnp : np ≤ p.ℓ + p.k) (hnr : nr ≤ p.k) {o l : Nat}
    (h0 : 0 < l) (h1 : o + l ≤ oACC ∨ oACC + 4 ≤ o)
    (h2 : o + l ≤ oP 0 ∨ (oP (p.k * p.ℓ) ≤ o ∧ o + l ≤ oP (p.k * p.ℓ + p.ℓ)) ∨ oP (p.k * p.ℓ + p.ℓ + p.k) ≤ o)
    (h3 : o + l ≤ scrLen p) : SafeR p np nr [sb o l] := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have hs : scrLen p = 1024 * (p.k * p.ℓ + 4 * p.k + 3 * p.ℓ + 32) := by simp only [scrLen, hF.sw]; omega_using []
  have hpk := hF.pk; have hsk := hF.sk
  simp only [oT0] at hsk
  simp only [oACC, oP] at h1 h2
  have hc : (YK p).ok (sb o l) = true := ykOk (by decide) h0 h3
  have same : ∀ {o' l' : Nat}, 0 < l' → o' + l' ≤ scrLen p → (o' + l' ≤ o ∨ o + l ≤ o') →
      (YK p).apart (sb o' l') [sb o l] = true :=
    fun hl' h hs => apart_one_same (ykOk (by decide) hl' h) hc rfl hs
  have d1 : ∀ {o' l' : Nat}, 0 < l' → o' + l' ≤ p.pkLen → (YK p).apart ⟨1, o', l'⟩ [sb o l] = true :=
    fun hl' h => apart_one_diff (ykOk (by decide) hl' h) hc (by dsimp only; decide) rfl
  have d2 : ∀ {o' l' : Nat}, 0 < l' → o' + l' ≤ p.skLen → (YK p).apart ⟨2, o', l'⟩ [sb o l] = true :=
    fun hl' h => apart_one_diff (ykOk (by decide) hl' h) hc (by dsimp only; decide) rfl
  refine ⟨same (by decide) ?_ ?_, fun e he => same (by decide) ?_ ?_, fun i hi => same (by decide) ?_ ?_,
    d1 (by decide) ?_, d2 (by decide) ?_, d2 (by decide) ?_, fun r hr => d2 ?_ ?_,
    fun i hi => ⟨d1 (by decide) ?_, d2 (by decide) ?_⟩⟩
  all_goals try rw [hs]
  all_goals safe1 hF

/-- A buffer of `pk` after the rows so far. -/
theorem SafeR.pk {p : Params} (hF : PFacts p) {np nr : Nat} (hnp : np ≤ p.ℓ + p.k) (hnr : nr ≤ p.k) {o l : Nat}
    (h0 : 0 < l) (h1 : 32 + 320 * nr ≤ o) (h2 : o + l ≤ p.pkLen) : SafeR p np nr [⟨1, o, l⟩] := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have hs : scrLen p = 1024 * (p.k * p.ℓ + 4 * p.k + 3 * p.ℓ + 32) := by simp only [scrLen, hF.sw]; omega_using []
  have hpk := hF.pk; have hsk := hF.sk
  simp only [oT0] at hsk
  have hc : (YK p).ok ⟨1, o, l⟩ = true := ykOk (by decide) h0 h2
  have sc : ∀ {o' l' : Nat}, 0 < l' → o' + l' ≤ scrLen p → (YK p).apart (sb o' l') [⟨1, o, l⟩] = true :=
    fun hl' h => apart_one_diff (ykOk (by decide) hl' h) hc (by dsimp only; decide) rfl
  have same : ∀ {o' l' : Nat}, 0 < l' → o' + l' ≤ p.pkLen → (o' + l' ≤ o ∨ o + l ≤ o') →
      (YK p).apart ⟨1, o', l'⟩ [⟨1, o, l⟩] = true :=
    fun hl' h hs => apart_one_same (ykOk (by decide) hl' h) hc rfl hs
  have d2 : ∀ {o' l' : Nat}, 0 < l' → o' + l' ≤ p.skLen → (YK p).apart ⟨2, o', l'⟩ [⟨1, o, l⟩] = true :=
    fun hl' h => apart_one_diff (ykOk (by decide) hl' h) hc (by dsimp only; decide) rfl
  refine ⟨sc (by decide) ?_, fun e he => sc (by decide) ?_, fun i hi => sc (by decide) ?_,
    same (by decide) ?_ ?_, d2 (by decide) ?_, d2 (by decide) ?_, fun r hr => d2 ?_ ?_,
    fun i hi => ⟨same (by decide) ?_ ?_, d2 (by decide) ?_⟩⟩
  all_goals try rw [hs]
  all_goals safe1 hF

/-- A buffer of `sk` after `ρ` and `K`, apart from the entries packed and the rows so far. -/
theorem SafeR.sk {p : Params} (hF : PFacts p) {np nr : Nat} (hnp : np ≤ p.ℓ + p.k) (hnr : nr ≤ p.k) {o l : Nat}
    (h0 : 0 < l) (h1 : 64 ≤ o) (hp : o + l ≤ 128 ∨ 128 + lenS p * np ≤ o) (hr : o + l ≤ oT0 p ∨ oT0 p + 416 * nr ≤ o)
    (h2 : o + l ≤ p.skLen) : SafeR p np nr [⟨2, o, l⟩] := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have hs : scrLen p = 1024 * (p.k * p.ℓ + 4 * p.k + 3 * p.ℓ + 32) := by simp only [scrLen, hF.sw]; omega_using []
  have hpk := hF.pk; have hsk := hF.sk
  have hc : (YK p).ok ⟨2, o, l⟩ = true := ykOk (by decide) h0 h2
  simp only [oT0] at hsk hr
  have sc : ∀ {o' l' : Nat}, 0 < l' → o' + l' ≤ scrLen p → (YK p).apart (sb o' l') [⟨2, o, l⟩] = true :=
    fun hl' h => apart_one_diff (ykOk (by decide) hl' h) hc (by dsimp only; decide) rfl
  have d1 : ∀ {o' l' : Nat}, 0 < l' → o' + l' ≤ p.pkLen → (YK p).apart ⟨1, o', l'⟩ [⟨2, o, l⟩] = true :=
    fun hl' h => apart_one_diff (ykOk (by decide) hl' h) hc (by dsimp only; decide) rfl
  have same : ∀ {o' l' : Nat}, 0 < l' → o' + l' ≤ p.skLen → (o' + l' ≤ o ∨ o + l ≤ o') →
      (YK p).apart ⟨2, o', l'⟩ [⟨2, o, l⟩] = true :=
    fun hl' h hs => apart_one_same (ykOk (by decide) hl' h) hc rfl hs
  refine ⟨sc (by decide) ?_, fun e he => sc (by decide) ?_, fun i hi => sc (by decide) ?_,
    d1 (by decide) ?_, same (by decide) ?_ ?_, same (by decide) ?_ ?_, fun r hr => same ?_ ?_ ?_,
    fun i hi => ⟨d1 (by decide) ?_, same (by decide) ?_ ?_⟩⟩
  all_goals try rw [hs]
  all_goals safe1 hF

theorem KR.keep {p : Params} {A : Nat → Poly} {S : Nat → IPoly} {np nj nr : Nat} {s₀ s s' : State}
    (h : KR p A S np nj nr s₀ s) (hp : TPre (YK p) s₀) {bs : List Buf} {N : Nat} (hN : N + 16 ≤ 96)
    (hs : SafeR p np nr bs) (hs1 : ∀ j < p.ℓ, (YK p).apart (sB p j) bs = true) (fr : Frame (FR s₀ bs N) s.mem s'.mem)
    (h' : Ctx (YK p) s₀ s') : KR p A S np nj nr s₀ s' where
  ctx := h'
  good := by rw [acc_keep hp hN hs.acc fr]; exact h.good
  small := h.small
  aS e he := keepPolyD hp hN (hs.aS e he) fr (h.aS e he)
  s2 i hi := keepPolyD hp hN (hs.s2 i hi) fr (h.s2 i hi)
  s1 j hj := keepPolyD hp hN (hs1 j hj) fr (h.s1 j hj)
  pk0 := by rw [keepBytes hp hN hs.pk0 fr]; exact h.pk0
  sk0 := by rw [keepBytes hp hN hs.sk0 fr]; exact h.sk0
  sk1 := by rw [keepBytes hp hN hs.sk1 fr]; exact h.sk1
  packs r hr := by rw [keepBytes hp hN (hs.packs r hr) fr]; exact h.packs r hr
  rows i hi := ⟨by rw [keepBytes hp hN (hs.rows i hi).1 fr]; exact (h.rows i hi).1,
    by rw [keepBytes hp hN (hs.rows i hi).2 fr]; exact (h.rows i hi).2⟩

/-- The states after the copies, and the first `np` entries packed, `nj` in the NTT domain and `nr` rows. -/
abbrev KRx (p : Params) (np nj nr : Nat) (s₀ s : State) : Prop := ∃ A S, KR p A S np nj nr s₀ s

/-! ## `ρ` and `K` to the keys -/

theorem KB.rho {p : Params} {s₀ s : State} (h : KB p s₀ s) :
    bytesAt s.mem (Buf.addr s₀ (sb oHX 32)) 32 = rhoOf p s₀ := by
  show _ = (keyGenSeeds p (xiOf s₀)).1
  rw [seeds_eq]
  show _ = (hxOf p s₀).take 32
  rw [← h.hx, Proof.MlKem.bytesAt_take _ _ (by decide)]

theorem KB.kk {p : Params} (hF : PFacts p) {s₀ s : State} (hp : TPre (YK p) s₀) (h : KB p s₀ s) :
    bytesAt s.mem (Buf.addr s₀ (sb (oHX + 96) 32)) 32 = kOf p s₀ := by
  show _ = (keyGenSeeds p (xiOf s₀)).2.2
  rw [seeds_eq]
  show _ = ((hxOf p s₀).drop 96).take 32
  rw [← h.hx, bytes_sub hp _ (k := 96) (c := 32) (L := 128) (by decide) (by layd) (by layd)]

theorem copies_piece {p : Params} (hF : PFacts p) :
    KP p (KSamp p (p.k * p.ℓ) (p.ℓ + p.k)) (KRx p 0 0 0) copies := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  unfold copies
  refine Piece.seq (B := fun s₀ s => KSamp p (p.k * p.ℓ) (p.ℓ + p.k) s₀ s ∧
      bytesAt s.mem (Buf.addr s₀ ⟨1, 0, 32⟩) 32 = rhoOf p s₀)
    (copyW_piece (Y := YK p) kS oHX 1 0 8 (by decide) (by decide) (by layd) (h₁ := .block []) (by kernel_rfl)
      (by native_taint_decide) (fun _ _ _ h => h.kb.ctx) fun s₀ s s' hp h h' fr cp => ⟨h.keep hp (N := 0) (by omega_using [])
        ⟨by layd, by layd, fun _ _ => by layd, fun _ _ => by layd⟩ (fr1 fr) h', ?_⟩) ?_
  · show bytesAt s'.mem _ 32 = _
    rw [cp]; exact h.kb.rho
  refine Piece.seq (B := fun s₀ s => KSamp p (p.k * p.ℓ) (p.ℓ + p.k) s₀ s ∧
      bytesAt s.mem (Buf.addr s₀ ⟨1, 0, 32⟩) 32 = rhoOf p s₀ ∧ bytesAt s.mem (Buf.addr s₀ ⟨2, 0, 32⟩) 32 = rhoOf p s₀)
    (copyW_piece (Y := YK p) kS oHX 2 0 8 (by decide) (by decide) (by layd) (h₁ := .block []) (by kernel_rfl)
      (by native_taint_decide) (fun _ _ _ h => h.1.kb.ctx) fun s₀ s s' hp h h' fr cp => ⟨h.1.keep hp (N := 0) (by omega_using [])
        ⟨by layd, by layd, fun _ _ => by layd, fun _ _ => by layd⟩ (fr1 fr) h',
        by rw [keepBytes hp (N := 0) (stkN (by omega_using [])) (b := ⟨1, 0, 32⟩) (by layd) (fr1 fr)]; exact h.2, ?_⟩) ?_
  · show bytesAt s'.mem _ 32 = _
    rw [cp]; exact h.1.kb.rho
  refine copyW_piece (Y := YK p) kS (oHX + 96) 2 32 8 (by decide) (by decide) (by layd) (h₁ := .block [])
    (by kernel_rfl) (by native_taint_decide) (fun _ _ _ h => h.1.kb.ctx) fun s₀ s s' hp h h' fr cp => ?_
  obtain ⟨⟨kb, A, S, hA, hS, hG⟩, e1, e2⟩ := h
  have k : ∀ b : Buf, (YK p).apart b [⟨2, 32, 32⟩] = true →
      bytesAt s'.mem (Buf.addr s₀ b) b.len = bytesAt s.mem (Buf.addr s₀ b) b.len :=
    fun b hb => keepBytes hp (N := 0) (stkN (by omega_using [])) hb (fr1 fr)
  refine ⟨A, S, h', ?_, fun r hr => (hS r hr).2, fun e he => keepPolyD hp (stkN (by omega_using [])) (by layd) (fr1 fr)
    (hA e he), fun i hi => keepPolyD hp (stkN (by omega_using [])) (by layd) (fr1 fr) (hS _ (by omega_using [hi])).1,
    fun j hj => ?_, by rw [k _ (by layd)]; exact e1, by rw [k _ (by layd)]; exact e2, ?_,
    fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩
  · rw [acc_keep hp (N := 0) (by omega_using []) (by layd) (fr1 fr)]; exact hG
  · rw [ifn (Nat.not_lt_zero j)]
    exact keepPolyD hp (stkN (by omega_using [])) (by layd) (fr1 fr) (hS _ (by omega_using [hj])).1
  · show bytesAt s'.mem _ 32 = _
    rw [cp]; exact kb.kk hF hp

end VG.Proof.MlDsa.X86.KeyGen

end

end

/-!
# ML-DSA key generation on x86 (32-bit): `s₁ ‖ s₂` packed, and `ŝ₁`

Each entry of `s₁ ‖ s₂`, `BitPack`ed to `sk` (`packS_piece`: its coefficients
are in `[-η, η]`), and `ŝ₁[j] = NTT(s₁[j])` (`nttS_piece`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top
open VG.Impl.MlDsa.X86.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt bitPack simpleBitPack)
open VG.Proof.MlDsa (polyAt coeffAt Reduced PolyIs)
open VG.Spec.Sha3 (bytesAt)

theorem coeff_val {m : Mem} {q : Addr} {f : Poly} (h : PolyIs m q f) {i : Nat} (hi : i < 256) :
    (coeffAt m q i).toNat = (f[i]'hi).val := by
  have e := congrArg (fun g : Poly => (g[i]'hi).val) h.2
  simp only [polyAt, Vector.getElem_ofFn, Fin.val_ofNat] at e
  rw [← e, Nat.mod_eq_of_lt (h.1 i hi)]

theorem small_mem {η : Nat} {x : IPoly} (h : Small η x) {i : Nat} (hi : i < 256) :
    -(η : Int) ≤ x[i] ∧ x[i] ≤ η := h _ (Vector.mem_toList_iff.mpr (Vector.getElem_mem hi))

theorem small_big {η : Nat} (hη : η ≤ 4) {x : IPoly} (hs : Small η x) :
    ∀ c ∈ x.toList, -4190208 ≤ c ∧ c ≤ 4190208 := fun c hc => by
  have := hs c hc; omega_arith

theorem eta_le {p : Params} (hF : PFacts p) : p.η ≤ 4 := by rcases hF.eta with ⟨h, _⟩ | ⟨h, _⟩ <;> omega_using [h]

theorem eta_params {p : Params} (hF : PFacts p) : (p.η, p.η) ∈ Proof.MlDsa.bitPackParams := by
  rcases hF.eta with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> decide

theorem lenS_eq (p : Params) : lenS p = 32 * Spec.MlDsa.bitlen (p.η + p.η) := by
  rw [lenS, Nat.two_mul]

/-- The coefficients of a small polynomial are in `[-η, η]`, as `BitPack` needs. -/
theorem packIn {m : Mem} {q : Addr} {η : Nat} (hη : η ≤ 4) {x : IPoly} (h : PolyIs m q (toRq x)) (hs : Small η x) :
    ∀ i < Spec.MlDsa.n, -(η : Int) ≤ Spec.MlDsa.modPm (coeffAt m q i).toNat Spec.MlDsa.q ∧
      Spec.MlDsa.modPm (coeffAt m q i).toNat Spec.MlDsa.q ≤ η := fun i hi => by
  have hx := small_mem hs hi
  rw [coeff_val h hi]
  simp only [toRq, Vector.getElem_map]
  rw [Proof.MlDsa.KeyGen.modPm_ofInt (by omega) (by omega)]
  exact hx

/-- The entry `r` of `s₁ ‖ s₂`, before `NTT`. -/
theorem KR.sPoly {p : Params} {A : Nat → Poly} {S : Nat → IPoly} {np nr : Nat} {s₀ s : State}
    (h : KR p A S np 0 nr s₀ s) {r : Nat} (hr : r < p.ℓ + p.k) :
    PolyIs s.mem (Buf.addr s₀ (sB p r)) (toRq (S r)) := by
  by_cases hl : r < p.ℓ
  · have := h.s1 r hl; rwa [ifn (Nat.not_lt_zero r)] at this
  · have := h.s2 (r - p.ℓ) (by omega_using [hr, hl]); rwa [show p.ℓ + (r - p.ℓ) = r by omega_using [hl]] at this

section
variable {P : Prims} (hP : PrimsOk P) {p : Params} (hF : PFacts p)
include hP hF

theorem packS_piece {r : Nat} (hr : r < p.ℓ + p.k) : KP p (KRx p r 0 0) (KRx p (r + 1) 0 0) (packS P p r) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  unfold packS
  refine Piece.mono (A := fun s₀ s => ∃ A S, KR p A S r 0 0 s₀ s ∧ PolyIs s.mem (Buf.addr s₀ (sB p r)) (toRq (S r)))
    ?_ (fun s₀ s _ ⟨A, S, h⟩ => ⟨A, S, h, h.sPoly hr⟩) fun _ _ _ h => h
  refine bp_piece (Y := YK p) hP.bitPack kS (oP (p.k * p.ℓ + r)) p.η p.η 2 (128 + lenS p * r) (lenS p)
    (eta_params hF) (lenS_eq p) (by layd) (Nat.le_of_eq (YK_stk p).symm) (ht := .block []) (by kernel_rfl)
    (fun s₀ s _ ⟨A, S, h, hs⟩ => ⟨h.ctx, hs.1, packIn (eta_le hF) hs (h.small r hr)⟩)
    fun s₀ s s' hp ⟨A, S, h, hs⟩ h' fr out => ⟨A, S, ?_⟩
  have hpos : 0 < lenS p := by rcases hF.eta with ⟨_, e⟩ | ⟨_, e⟩ <;> omega_using [e]
  have hle : 128 + lenS p * r + lenS p ≤ oT0 p := by
    simp only [oT0]; rw [Nat.add_assoc, ← Nat.mul_succ]; exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hr) _
  have hsf : SafeR p r 0 [⟨2, 128 + lenS p * r, lenS p⟩] := SafeR.sk hF (Nat.le_of_lt hr) (Nat.zero_le _) hpos
    (by omega_using []) (.inr (Nat.le_refl _)) (.inl hle) (by rw [hF.sk]; omega_using [hle])
  have k := h.keep hp (N := 80) (by omega_using []) hsf (fun _ _ => by layd) fr h'
  refine { k with packs := fun r' hr' => ?_ }
  rcases (by omega_using [hr'] : r' < r ∨ r' = r) with hr' | rfl
  · exact k.packs r' hr'
  · rw [out, hs.2, Proof.MlDsa.KeyGen.modPm_toRq (small_big (eta_le hF) (h.small r' hr))]

theorem nttS_piece {j : Nat} (hj : j < p.ℓ) :
    KP p (KRx p (p.ℓ + p.k) j 0) (KRx p (p.ℓ + p.k) (j + 1) 0) (nttS P p j) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  unfold nttS
  refine Piece.mono (A := fun s₀ s => ∃ A S, KR p A S (p.ℓ + p.k) j 0 s₀ s)
    ?_ (fun _ _ _ h => h) fun _ _ _ h => h
  refine inPlace_piece (Y := YK p) hP.ntt kS (oP (p.k * p.ℓ + j)) kS oSS (by layd) (Nat.le_of_eq (YK_stk p).symm)
    (ht := .block []) (by kernel_rfl)
    (fun s₀ s _ ⟨A, S, h⟩ => ⟨h.ctx, (h.s1 j hj).1⟩)
    fun s₀ s s' hp ⟨A, S, h⟩ h' fr out => ⟨A, S, ?_⟩
  have hS := h.s1 j hj
  rw [ifn (Nat.lt_irrefl j)] at hS
  have hs : SafeR p (p.ℓ + p.k) 0 [sB p j, ssB 1024] :=
    (SafeR.sc hF (Nat.le_refl _) (Nat.zero_le _) (by decide) (.inr (by simp only [oACC, oP]; omega_using []))
      (.inr (.inl (by simp only [oP]; omega_using [hj]))) (by simp only [scrLen, hF.sw, oP]; omega_using [hj])).append (bs₁ := [_])
    (SafeR.sc (o := oSS) (l := 1024) hF (Nat.le_refl _) (Nat.zero_le _) (by decide) (.inr (by decide))
      (.inl (by decide)) (by simp only [scrLen, hF.sw, oSS]; omega_using []))
  exact { ctx := h'
          good := by rw [acc_keep hp (N := 80) (by omega_using []) hs.acc fr]; exact h.good
          small := h.small
          aS := fun e he => keepPolyD hp (stkN (by omega_using [])) (hs.aS e he) fr (h.aS e he)
          s2 := fun i hi => keepPolyD hp (stkN (by omega_using [])) (hs.s2 i hi) fr (h.s2 i hi)
          s1 := fun j' hj' => if e : j' = j then by
              subst e; rw [ifp (Nat.lt_succ_self j'), ← hS.2]; exact out
            else by
              have := keepPolyD hp (stkN (by omega_using [])) (by layd) fr (h.s1 j' hj')
              by_cases hlt : j' < j
              · rwa [ifp hlt, ← ifp (show j' < j + 1 by omega_using [hlt]) (ntt (toRq (S j'))) (toRq (S j'))] at this
              · rwa [ifn hlt, ← ifn (show ¬ j' < j + 1 by omega_using [e, hlt]) (ntt (toRq (S j'))) (toRq (S j'))] at this
          pk0 := by rw [keepBytes hp (stkN (by omega_using [])) hs.pk0 fr]; exact h.pk0
          sk0 := by rw [keepBytes hp (stkN (by omega_using [])) hs.sk0 fr]; exact h.sk0
          sk1 := by rw [keepBytes hp (stkN (by omega_using [])) hs.sk1 fr]; exact h.sk1
          packs := fun r hr => by rw [keepBytes hp (stkN (by omega_using [])) (hs.packs r hr) fr]; exact h.packs r hr
          rows := fun _ h => absurd h (Nat.not_lt_zero _) }

end

end VG.Proof.MlDsa.X86.KeyGen

end

end

/-!
# ML-DSA key generation on x86 (32-bit): the rows of `t`

Row `i` (`row_piece`): `t = Σⱼ Â[i, j] ŝ₁[j]` (`dotK`, a product then `ℓ - 1`
products added), `NTT⁻¹`, `s₂[i]` added (`tK`), `Power2Round`, and `t₁`
`SimpleBitPack`ed to `pk` and `t₀` `BitPack`ed to `sk`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top
open VG.Impl.MlDsa.X86.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt nttInv bitPack simpleBitPack power2Round ofInt)
open VG.Proof.MlDsa (polyAt coeffAt Reduced PolyIs NatPolyIs)
open VG.Proof.MlDsa.KeyGen (dotK tK t1K t0K)
open VG.Spec.Sha3 (bytesAt)

/-- During row `i`: the keys so far, and `t` holding `v`. -/
abbrev RowT (p : Params) (i : Nat) (v : (Nat → Poly) → (Nat → IPoly) → Poly) (s₀ s : State) : Prop :=
  ∃ A S, KR p A S (p.ℓ + p.k) p.ℓ i s₀ s ∧ PolyIs s.mem (Buf.addr s₀ (tB p)) (v A S)

theorem KR.nttS {p : Params} {A : Nat → Poly} {S : Nat → IPoly} {nr : Nat} {s₀ s : State}
    (h : KR p A S (p.ℓ + p.k) p.ℓ nr s₀ s) {j : Nat} (hj : j < p.ℓ) :
    PolyIs s.mem (Buf.addr s₀ (sB p j)) (ntt (toRq (S j))) := by
  have := h.s1 j hj; rwa [ifp hj] at this

theorem t0_params : ((4095 : Nat), (4096 : Nat)) ∈ Proof.MlDsa.bitPackParams := by decide

theorem power2Round_fst' (c : Spec.MlDsa.Zq) : (power2Round c).1.toNat ≤ 1023 := by
  have := Proof.MlDsa.KeyGen.power2Round_fst c; omega_arith

/-! ## `SafeR` of the buffers a row writes, once each -/

theorem safe_poly {p : Params} (hF : PFacts p) {i : Nat} (hi : i < p.k) {j : Nat} (hj : j < 3) :
    SafeR p (p.ℓ + p.k) i [pB (p.k * p.ℓ + p.ℓ + p.k + j)] := by
  have := hF.k; have := hF.l; have := hF.kl
  exact SafeR.sc hF (by omega_arith) (by omega_arith) (by decide) (.inr (by simp only [oACC, oP]; omega_arith))
    (.inr (.inr (by simp only [oP]; omega_arith))) (by simp only [scrLen, hF.sw, oP]; omega_arith)

theorem safe_t {p : Params} (hF : PFacts p) {i : Nat} (hi : i < p.k) : SafeR p (p.ℓ + p.k) i [tB p] := by
  have := safe_poly hF hi (j := 0) (by decide); rwa [Nat.add_zero] at this

theorem safe_inv {p : Params} (hF : PFacts p) {i : Nat} (hi : i < p.k) :
    SafeR p (p.ℓ + p.k) i [tB p, ssB 1024] := by
  have := hF.k; have := hF.l; have := hF.kl
  exact (safe_t hF hi).append (bs₁ := [_]) (SafeR.sc (o := oSS) (l := 1024) hF (by omega_arith) (by omega_arith) (by decide)
    (.inr (by decide)) (.inl (by decide)) (by simp only [scrLen, hF.sw, oSS]; omega_arith))

theorem safe_p2r {p : Params} (hF : PFacts p) {i : Nat} (hi : i < p.k) :
    SafeR p (p.ℓ + p.k) i [t1B p, t0B p] :=
  (safe_poly hF hi (j := 1) (by decide)).append (bs₁ := [_]) (safe_poly hF hi (j := 2) (by decide))

theorem safe_sbp {p : Params} (hF : PFacts p) {i : Nat} (hi : i < p.k) :
    SafeR p (p.ℓ + p.k) i [⟨1, 32 + 320 * i, 320⟩] :=
  SafeR.pk hF (Nat.le_refl _) (Nat.le_of_lt hi) (by decide) (Nat.le_refl _) (by rw [hF.pk]; omega_arith)

theorem safe_bp {p : Params} (hF : PFacts p) {i : Nat} (hi : i < p.k) :
    SafeR p (p.ℓ + p.k) i [⟨2, oT0 p + 416 * i, 416⟩] := by
  have := hF.k; have := hF.l
  exact SafeR.sk hF (Nat.le_refl _) (Nat.le_of_lt hi) (by decide) (by simp only [oT0]; omega_arith)
    (.inr (by simp only [oT0]; omega_arith)) (.inr (Nat.le_refl _)) (by rw [hF.sk]; omega_arith)

section
variable {P : Prims} (hP : PrimsOk P) {p : Params} (hF : PFacts p) {i : Nat} (hi : i < p.k)
include hP hF hi

theorem mul_row : KP p (KRx p (p.ℓ + p.k) p.ℓ i) (RowT p i fun A S => dotK p A S i 1)
    (callP kS "vg_mldsa_multiply_ntt" P.mul [.buf (tB p), .buf (aB (p.ℓ * i)), .buf (sB p 0)]) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have he : p.ℓ * i < p.k * p.ℓ := by
    have : p.ℓ * (i + 1) ≤ p.ℓ * p.k := Nat.mul_le_mul_left _ (by omega_arith)
    rw [Nat.mul_comm p.k]; rw [Nat.mul_succ] at this; omega_arith
  refine mul_piece (Y := YK p) _ _ _ _ _ _ hP.mul (by layd) (Nat.le_of_eq (YK_stk p).symm)
    (ht := .block []) (by kernel_rfl)
    (fun s₀ s _ ⟨A, S, h⟩ => ⟨h.ctx, (h.aS _ he).1, (h.nttS (by omega_arith)).1⟩)
    fun s₀ s s' hp ⟨A, S, h⟩ h' fr out => ⟨A, S, h.keep hp (N := 80) (by omega_arith) (by exact safe_t hF hi)
      (fun _ _ => by layd) fr h', ?_⟩
  rw [(h.aS _ he).2, (h.nttS (by omega_arith)).2, ← Proof.MlDsa.KeyGen.dotK_one] at out
  exact out

theorem mulAdd_row {j : Nat} (_hj₁ : 1 ≤ j) (hj : j < p.ℓ) :
    KP p (RowT p i fun A S => dotK p A S i j) (RowT p i fun A S => dotK p A S i (j + 1)) (mulAddS P p i j) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have he : p.ℓ * i + j < p.k * p.ℓ := by
    have : p.ℓ * (i + 1) ≤ p.ℓ * p.k := Nat.mul_le_mul_left _ (by omega_arith)
    rw [Nat.mul_comm p.k]; rw [Nat.mul_succ] at this; omega_arith
  refine mulAdd_piece (Y := YK p) _ _ _ _ _ _ hP.mulAdd (by layd) (Nat.le_of_eq (YK_stk p).symm)
    (ht := .block []) (by kernel_rfl)
    (fun s₀ s _ ⟨A, S, h, ht⟩ => ⟨h.ctx, ht.1, (h.aS _ he).1, (h.nttS hj).1⟩)
    fun s₀ s s' hp ⟨A, S, h, ht⟩ h' fr out => ⟨A, S, h.keep hp (N := 80) (by omega_arith) (by exact safe_t hF hi)
      (fun _ _ => by layd) fr h', ?_⟩
  rw [ht.2, (h.aS _ he).2, (h.nttS hj).2, ← Proof.MlDsa.KeyGen.dotK_succ] at out
  exact out

theorem inv_row : KP p (RowT p i fun A S => dotK p A S i p.ℓ) (RowT p i fun A S => nttInv (dotK p A S i p.ℓ))
    (callP kS "vg_mldsa_inv_ntt" P.invNtt [.buf (tB p), .buf (ssB 1024)]) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  refine inPlace_piece (Y := YK p) hP.invNtt _ _ _ _ (by layd) (Nat.le_of_eq (YK_stk p).symm)
    (ht := .block []) (by kernel_rfl) (fun s₀ s _ ⟨A, S, h, ht⟩ => ⟨h.ctx, ht.1⟩)
    fun s₀ s s' hp ⟨A, S, h, ht⟩ h' fr out => ⟨A, S, h.keep hp (N := 80) (by omega_arith) (by exact safe_inv hF hi)
      (fun _ _ => by layd) fr h', ?_⟩
  rw [ht.2] at out
  exact out

theorem add_row : KP p (RowT p i fun A S => nttInv (dotK p A S i p.ℓ)) (RowT p i fun A S => tK p A S i)
    (callP kS "vg_mldsa_add" P.add [.buf (tB p), .buf (sB p (p.ℓ + i))]) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  refine acc_piece (Y := YK p) hP.add _ _ _ _ (by layd) (Nat.le_of_eq (YK_stk p).symm)
    (ht := .block []) (by kernel_rfl) (fun s₀ s _ ⟨A, S, h, ht⟩ => ⟨h.ctx, ht.1, (h.s2 i hi).1⟩)
    fun s₀ s s' hp ⟨A, S, h, ht⟩ h' fr out => ⟨A, S, h.keep hp (N := 80) (by omega_arith) (by exact safe_t hF hi)
      (fun _ _ => by layd) fr h', ?_⟩
  rw [ht.2, (h.s2 i hi).2] at out
  exact out

/-- After `Power2Round` of row `i`. -/
abbrev RowP (p : Params) (i : Nat) (s₀ s : State) : Prop :=
  ∃ A S, KR p A S (p.ℓ + p.k) p.ℓ i s₀ s ∧ NatPolyIs s.mem (Buf.addr s₀ (t1B p)) (t1K p A S i) ∧
    PolyIs s.mem (Buf.addr s₀ (t0B p)) ((tK p A S i).map fun c => ofInt (power2Round c).2)

theorem p2r_row : KP p (RowT p i fun A S => tK p A S i) (RowP p i)
    (callP kS "vg_mldsa_power2round" P.power2Round [.buf (tB p), .buf (t1B p), .buf (t0B p)]) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  refine p2r_piece (Y := YK p) _ _ _ _ _ _ hP.power2Round (by layd) (Nat.le_of_eq (YK_stk p).symm)
    (ht := .block []) (by kernel_rfl) (fun s₀ s _ ⟨A, S, h, ht⟩ => ⟨h.ctx, ht.1⟩)
    fun s₀ s s' hp ⟨A, S, h, ht⟩ h' fr o₁ o₂ => ⟨A, S, h.keep hp (N := 80) (by omega_arith) (by exact safe_p2r hF hi)
      (fun _ _ => by layd) fr h', ?_, ?_⟩
  · rw [ht.2] at o₁; exact o₁
  · rw [ht.2] at o₂; exact o₂

/-- After `t₁` is packed. -/
abbrev RowQ (p : Params) (i : Nat) (s₀ s : State) : Prop :=
  ∃ A S, KR p A S (p.ℓ + p.k) p.ℓ i s₀ s ∧
    PolyIs s.mem (Buf.addr s₀ (t0B p)) ((tK p A S i).map fun c => ofInt (power2Round c).2) ∧
    bytesAt s.mem (Buf.addr s₀ ⟨1, 32 + 320 * i, 320⟩) 320 = simpleBitPack (t1K p A S i) 1023

theorem sbp_row : KP p (RowP p i) (RowQ p i)
    (callP kS "vg_mldsa_simple_bit_pack" P.simpleBitPack
      [.buf (t1B p), .imm 1023, .buf ⟨1, 32 + 320 * i, 320⟩, .imm 320]) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  refine sbp_piece (Y := YK p) hP.simpleBitPack _ _ 1023 _ _ 320 (by decide) (by decide) (by layd)
    (Nat.le_of_eq (YK_stk p).symm) (ht := .block []) (by kernel_rfl)
    (fun s₀ s _ ⟨A, S, h, h1, _⟩ => ⟨h.ctx, fun j hj => ?_⟩)
    fun s₀ s s' hp ⟨A, S, h, h1, h0⟩ h' fr out => ⟨A, S, h.keep hp (N := 80) (by omega_arith) (by exact safe_sbp hF hi)
      (fun _ _ => by layd) fr h', keepPolyD hp (stkN (by omega_arith)) (by layd) fr h0, ?_⟩
  · have e := congrArg (fun v : Vector Nat 256 => v[j]'hj) h1
    simp only [Proof.MlDsa.natPolyAt, Vector.getElem_ofFn, t1K, Vector.getElem_map] at e
    rw [e]; exact power2Round_fst' _
  · rw [out, h1]

theorem bp_row : KP p (RowQ p i) (KRx p (p.ℓ + p.k) p.ℓ (i + 1))
    (callP kS "vg_mldsa_bit_pack" P.bitPack
      [.buf (t0B p), .imm 4095, .imm 4096, .buf ⟨2, oT0 p + 416 * i, 416⟩, .imm 416]) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  refine bp_piece (Y := YK p) hP.bitPack _ _ 4095 4096 _ _ 416 t0_params (by decide) (by layd)
    (Nat.le_of_eq (YK_stk p).symm) (ht := .block []) (by kernel_rfl)
    (fun s₀ s _ ⟨A, S, h, h0, _⟩ => ⟨h.ctx, h0.1, fun j hj => ?_⟩)
    fun s₀ s s' hp ⟨A, S, h, h0, hb⟩ h' fr out => ⟨A, S, ?_⟩
  · rw [coeff_val h0 hj]
    simp only [Vector.getElem_map]
    have := Proof.MlDsa.KeyGen.power2Round_snd ((tK p A S i)[j]'hj)
    rw [Proof.MlDsa.KeyGen.modPm_ofInt (by omega_arith) (by omega_arith)]
    omega_arith
  · have k := h.keep hp (N := 80) (by omega_arith) (by exact safe_bp hF hi) (fun _ _ => by layd) fr h'
    refine { k with rows := fun i' hi' => ?_ }
    rcases (by omega_arith : i' < i ∨ i' = i) with hi' | rfl
    · exact k.rows i' hi'
    · refine ⟨by rw [keepBytes hp (stkN (by omega_arith)) (by layd) fr]; exact hb, ?_⟩
      rw [out, h0.2, Vector.map_map]
      congr 1
      refine Vector.map_congr_left fun c _ => ?_
      have := Proof.MlDsa.KeyGen.power2Round_snd c
      exact Proof.MlDsa.KeyGen.modPm_ofInt (by omega_arith) (by omega_arith)

theorem row_piece : KP p (KRx p (p.ℓ + p.k) p.ℓ i) (KRx p (p.ℓ + p.k) p.ℓ (i + 1)) (row P p i) := by
  have hl := hF.l
  unfold row
  refine (mul_row hP hF hi).seq (Piece.seq ?_ ((inv_row hP hF hi).seq ((add_row hP hF hi).seq
    ((p2r_row hP hF hi).seq ((sbp_row hP hF hi).seq (bp_row hP hF hi))))))
  refine Piece.mono (seqR_piece (I := fun j => RowT p i fun A S => dotK p A S i j) (p.ℓ - 1) 1
    fun j h1 h2 => mulAdd_row hP hF hi h1 (by omega_arith)) (fun _ _ _ h => h) fun _ _ _ h => ?_
  rwa [show 1 + (p.ℓ - 1) = p.ℓ by omega_arith] at h

end

end VG.Proof.MlDsa.X86.KeyGen

end

end

/-!
# ML-DSA key generation on x86 (32-bit): `vg_mldsa44_keygen`, `vg_mldsa65_keygen`, `vg_mldsa87_keygen`

The body, piece by piece (`body_piece`), for any parameter set of Table 1 and
any verified implementations of the primitives: it returns 1 with
`KeyGen_internal(ξ)` in `pk` and `sk` if every sampler succeeded (for some
bounds), and 0 if key generation fails within the least bounds (`post`); it
leaks only the pointers, `ρ` and what `RejBoundedPoly` leaks; so the function
meets the shared contract (`keyGen_verified`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top
open VG.Impl.MlDsa.X86.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt bitPack simpleBitPack keyGenInternal)
open VG.Proof.MlDsa (polyAt Reduced PolyIs)
open VG.Proof.MlDsa.KeyGen (dotK tK t1K t0K pkK skK)
open VG.Spec.Sha3 (bytesAt)

/-! ## `tr = H(pk, 64)`, and the value returned -/

/-- At the end: the keys, and the value returned. -/
structure KFin (p : Params) (s₀ s : State) : Prop where
  ex : ∃ A S, KR p A S (p.ℓ + p.k) p.ℓ p.k s₀ s ∧
    bytesAt s.mem (Buf.addr s₀ ⟨2, 64, 64⟩) 64 = Spec.MlDsa.H (bytesAt s.mem (Buf.addr s₀ ⟨1, 0, p.pkLen⟩) p.pkLen) 64

theorem trHash_piece {p : Params} (hF : PFacts p) : KP p (KRx p (p.ℓ + p.k) p.ℓ p.k) (KFin p) (trHash p) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  refine hash1_piece (Y := YK p) 0 200 136 0x1f ⟨1, 0, p.pkLen⟩ ⟨2, 64, 64⟩ Proof.MlKem.rate136 (by layd)
    (by rw [YK_stk]; omega_using []) (by show p.pkLen < 2 ^ 32; rw [hF.pk]; omega_using [hk]) (by decide) (by native_taint_decide) (h₁ := .block [])
    (by kernel_rfl) (h₃ := .block []) (by kernel_rfl) (h₄ := .block []) (by kernel_rfl)
    (fun _ _ _ ⟨_, _, h⟩ => h.ctx) fun s₀ s s' hp ⟨A, S, h⟩ h' fr out => ⟨A, S, ?_, ?_⟩
  · have hs : SafeR p (p.ℓ + p.k) p.k [sb 0 200, sb 200 640, ⟨2, 64, 64⟩] :=
      (SafeR.sc hF (Nat.le_refl _) (Nat.le_refl _) (by decide) (.inl (by decide)) (.inl (by decide))
        (by simp only [scrLen, hF.sw]; omega_using [])).append (bs₁ := [_])
      ((SafeR.sc hF (Nat.le_refl _) (Nat.le_refl _) (by decide) (.inl (by decide)) (.inl (by decide))
        (by simp only [scrLen, hF.sw]; omega_using [])).append (bs₁ := [_])
      (SafeR.sk hF (Nat.le_refl _) (Nat.le_refl _) (by decide) (by decide) (.inl (by decide))
        (.inl (by simp only [oT0]; omega_using [])) (by rw [hF.sk, oT0]; omega_using [])))
    exact h.keep hp (N := 40) (by omega_using []) hs (fun _ _ => by layd) fr h'
  · rw [out, sponge_H, keepBytes hp (N := 40) (stkN (by omega_using [])) (b := ⟨1, 0, p.pkLen⟩) (by layd) fr]

/-- The body's end: the keys, and `eax` the AND of the samplers' results. -/
structure Done (p : Params) (s₀ s : State) : Prop extends KFin p s₀ s where
  eax : s.gpr .eax = accV s₀ s

theorem ret_piece {p : Params} (hF : PFacts p) :
    KP p (KFin p) (fun s₀ s => Ctx (YK p) s₀ s ∧ Done p s₀ s) (.block [.mov .eax (.mem (at_ .esi oACC))]) := by
  refine ld32_piece (Y := YK p) oACC (by layd) (ht := .block []) (by kernel_rfl)
    (fun _ _ _ h => by obtain ⟨_, _, h, _⟩ := h.ex; exact h.ctx) fun s₀ s s' hp h h' m' e => ⟨h', ?_, ?_⟩
  · obtain ⟨A, S, hk, htr⟩ := h.ex
    exact ⟨A, S, hk.keep hp (bs := []) (N := 0) (by omega_using []) (by safeR hF) (fun _ _ => by layd) (by rw [m']; exact Frame.refl _ _)
      h', by rw [m']; exact htr⟩
  · rw [e, accV, m']; rfl

/-! ## The body -/

theorem body_piece {P : Prims} (hP : PrimsOk P) {p : Params} (hF : PFacts p) :
    KP p (fun s₀ s => s = P0 s₀) (fun s₀ s => Ctx (YK p) s₀ s ∧ Done p s₀ s) (body P p) := by
  have hk := hF.k; have hl := hF.l
  unfold body
  refine (ldsc_piece (Y := YK p) (ht := .block []) (by kernel_rfl)).seq ((seeds_piece hF).seq ?_)
  refine Piece.seq (B := KSamp p (p.k * p.ℓ) 0) (Piece.mono (seqR_piece (I := fun e => KSamp p e 0)
    (p.k * p.ℓ) 0 fun e _ he => expA_piece hP hF (by omega_using [he])) (fun s₀ s _ h => ⟨h.1, fun _ => Proof.MlDsa.KeyGen.zeroI.map
      (fun _ => 0), fun _ => Proof.MlDsa.KeyGen.zeroI, fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ h => absurd h (Nat.not_lt_zero _), .inl ⟨h.2, ⟨0, 0, 0, 0⟩, fun _ h => absurd h (Nat.not_lt_zero _),
        fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩) fun _ _ _ h => by simpa using h) ?_
  refine Piece.seq (B := KSamp p (p.k * p.ℓ) (p.ℓ + p.k)) (Piece.mono (seqR_piece
    (I := fun r => KSamp p (p.k * p.ℓ) r) (p.ℓ + p.k) 0 fun r _ hr => expS_piece hP hF (by omega_using [hr]))
    (fun _ _ _ h => h) fun _ _ _ h => by simpa using h) ?_
  refine (copies_piece hF).seq ?_
  refine Piece.seq (B := KRx p (p.ℓ + p.k) 0 0) (Piece.mono (seqR_piece (I := fun r => KRx p r 0 0) (p.ℓ + p.k) 0
    fun r _ hr => packS_piece hP hF (by omega_using [hr])) (fun _ _ _ h => h) fun _ _ _ h => by simpa using h) ?_
  refine Piece.seq (B := KRx p (p.ℓ + p.k) p.ℓ 0) (Piece.mono (seqR_piece (I := fun j => KRx p (p.ℓ + p.k) j 0) p.ℓ 0
    fun j _ hj => nttS_piece hP hF (by omega_using [hj])) (fun _ _ _ h => h) fun _ _ _ h => by simpa using h) ?_
  refine Piece.seq (B := KRx p (p.ℓ + p.k) p.ℓ p.k) (Piece.mono (seqR_piece
    (I := fun i => KRx p (p.ℓ + p.k) p.ℓ i) p.k 0 fun i _ hi => row_piece hP hF (by omega_using [hi]))
    (fun _ _ _ h => h) fun _ _ _ h => by simpa using h) ?_
  exact (trHash_piece hF).seq (ret_piece hF)

theorem body_nosp {P : Prims} (hP : PrimsOk P) (p : Params) : NoSp (body P p) := by
  unfold body
  refine NoSp.seq (NoSp.of_all (by kernel_rfl)) (NoSp.seq (NoSp.of_all (by kernel_rfl)) (NoSp.seq
    (NoSp.seqR (fun e => ?_) _ _) (NoSp.seq (NoSp.seqR (fun r => ?_) _ _) (NoSp.seq (NoSp.of_all (by kernel_rfl))
    (NoSp.seq (NoSp.seqR (fun r => NoSp.callP hP.bitPack.nosp) _ _) (NoSp.seq (NoSp.seqR (fun j =>
      NoSp.callP hP.ntt.nosp) _ _) (NoSp.seq (NoSp.seqR (fun i => ?_) _ _) (NoSp.seq (NoSp.of_all (by kernel_rfl))
    (NoSp.of_all (by kernel_rfl))))))))))
  · unfold expA
    exact NoSp.seq (NoSp.of_all (by kernel_rfl)) (NoSp.seq (NoSp.of_all (by kernel_rfl))
      (NoSp.seq (NoSp.callPR hP.rejNtt.nosp) (NoSp.of_all (by kernel_rfl))))
  · unfold expS
    exact NoSp.seq (NoSp.of_all (by kernel_rfl)) (NoSp.seq (NoSp.callPR hP.rejBounded.nosp)
      (NoSp.of_all (by kernel_rfl)))
  · unfold row
    exact NoSp.seq (NoSp.callP hP.mul.nosp) (NoSp.seq (NoSp.seqR (fun j => NoSp.callP hP.mulAdd.nosp) _ _)
      (NoSp.seq (NoSp.callP hP.invNtt.nosp) (NoSp.seq (NoSp.callP hP.add.nosp) (NoSp.seq
        (NoSp.callP hP.power2Round.nosp) (NoSp.seq (NoSp.callP hP.simpleBitPack.nosp) (NoSp.callP hP.bitPack.nosp))))))

/-! ## The keys in memory -/

theorem flatMap_congr_mem {α β : Type} {f g : α → List β} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) →
    l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h x (List.mem_cons_self ..),
      flatMap_congr_mem fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem t1Max_eq : Spec.MlDsa.t1Max = 1023 := by decide

section
variable {p : Params} (hF : PFacts p) {s₀ s : State} (hp : TPre (YK p) s₀)
include hF hp

omit hF in
/-- A buffer of `pk` or `sk`, from the start of its argument. -/
theorem addr_arg {a o l : Nat} (h : (YK p).ok ⟨a, o, l⟩ = true) :
    Buf.addr s₀ ⟨a, o, l⟩ = (arg s₀ a).setWidth 64 + BitVec.ofNat 64 o := Buf.addr_eq hp h

theorem pk_bytes {A : Nat → Poly} {S : Nat → IPoly} {np nj : Nat} (h : KR p A S np nj p.k s₀ s) :
    bytesAt s.mem (Buf.addr s₀ ⟨1, 0, p.pkLen⟩) p.pkLen = pkK p A S (rhoOf p s₀) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have e0 := addr_arg hp (a := 1) (o := 0) (l := p.pkLen) (by layd)
  have e1 := addr_arg hp (a := 1) (o := 0) (l := 32) (by layd)
  rw [BitVec.add_zero] at e0 e1
  rw [hF.pk] at e0 ⊢
  rw [e0, Proof.MlKem.bytesAt_add, ← e1, h.pk0, e1, Proof.MlDsa.KeyGen.bytesAt_pieces s.mem _ 32 320 p.k, pkK,
    t1Max_eq]
  refine congrArg _ (flatMap_congr_mem fun i hi => ?_)
  have hi := List.mem_range.mp hi
  rw [← addr_arg hp (a := 1) (o := 32 + 320 * i) (l := 320) (by layd)]
  exact (h.rows i hi).1

theorem sk_bytes {A : Nat → Poly} {S : Nat → IPoly} {nj : Nat} (h : KR p A S (p.ℓ + p.k) nj p.k s₀ s)
    (htr : bytesAt s.mem (Buf.addr s₀ ⟨2, 64, 64⟩) 64 = Spec.MlDsa.H (pkK p A S (rhoOf p s₀)) 64) :
    bytesAt s.mem (Buf.addr s₀ ⟨2, 0, p.skLen⟩) p.skLen = skK p A S (rhoOf p s₀) (kOf p s₀) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have a0 := addr_arg hp (a := 2) (o := 0) (l := p.skLen) (by layd)
  have a1 := addr_arg hp (a := 2) (o := 0) (l := 32) (by layd)
  have a2 := addr_arg hp (a := 2) (o := 32) (l := 32) (by layd)
  have a3 := addr_arg hp (a := 2) (o := 64) (l := 64) (by layd)
  rw [BitVec.add_zero] at a0 a1
  have h0 : bytesAt s.mem ((arg s₀ 2).setWidth 64) 32 = rhoOf p s₀ := by rw [← a1]; exact h.sk0
  have h1 : bytesAt s.mem ((arg s₀ 2).setWidth 64 + BitVec.ofNat 64 32) 32 = kOf p s₀ := by rw [← a2]; exact h.sk1
  have h2 : bytesAt s.mem ((arg s₀ 2).setWidth 64 + BitVec.ofNat 64 (32 + 32)) 64 =
      Spec.MlDsa.H (pkK p A S (rhoOf p s₀)) 64 := by rw [← a3]; exact htr
  rw [a0, hF.sk, oT0, show 128 = 32 + 32 + 64 from rfl, Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add,
    Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add, h0, h1, h2]
  have p1 := Proof.MlDsa.KeyGen.bytesAt_pieces s.mem ((arg s₀ 2).setWidth 64) (32 + 32 + 64) (lenS p) (p.ℓ + p.k)
  have p2 := Proof.MlDsa.KeyGen.bytesAt_pieces s.mem ((arg s₀ 2).setWidth 64) (oT0 p) 416 p.k
  rw [oT0] at p2
  have q1 : (List.range (p.ℓ + p.k)).flatMap (fun i => bytesAt s.mem ((arg s₀ 2).setWidth 64 +
      BitVec.ofNat 64 (32 + 32 + 64 + lenS p * i)) (lenS p)) =
      (List.range (p.ℓ + p.k)).flatMap fun r => bitPack (S r) p.η p.η := flatMap_congr_mem fun r hr => by
    rw [← addr_arg hp (a := 2) (o := 32 + 32 + 64 + lenS p * r) (l := lenS p) (by have := List.mem_range.mp hr; layd)]
    exact h.packs r (List.mem_range.mp hr)
  have q2 : (List.range p.k).flatMap (fun i => bytesAt s.mem ((arg s₀ 2).setWidth 64 +
      BitVec.ofNat 64 (128 + lenS p * (p.ℓ + p.k) + 416 * i)) 416) =
      (List.range p.k).flatMap fun i => bitPack (t0K p A S i) 4095 4096 := flatMap_congr_mem fun i hi => by
    rw [show 128 + lenS p * (p.ℓ + p.k) = oT0 p from rfl,
      ← addr_arg hp (a := 2) (o := oT0 p + 416 * i) (l := 416) (by have := List.mem_range.mp hi; layd)]
    exact (h.rows i (List.mem_range.mp hi)).2
  rw [p1, p2, q1, q2, skK]
  rfl

end

/-! ## The return -/

theorem idx_lt {p : Params} {r s : Nat} (hr : r < p.k) (hs : s < p.ℓ) : p.ℓ * r + s < p.k * p.ℓ := by
  have : p.ℓ * (r + 1) ≤ p.ℓ * p.k := Nat.mul_le_mul_left _ (by omega_using [hr])
  rw [Nat.mul_comm p.k]; rw [Nat.mul_succ] at this; omega_using [hs, this]

theorem outcome_of {p : Params} {s₀ : State} {A : Nat → Poly} {S : Nat → IPoly} {v : BitVec 32}
    (hl : 0 < p.ℓ) (hG : Good p s₀ (p.k * p.ℓ) (p.ℓ + p.k) A S v) :
    Spec.MlDsa.Outcome (fun b => keyGenInternal p b (xiOf s₀)) v
      (pkK p A S (rhoOf p s₀), skK p A S (rhoOf p s₀) (kOf p s₀)) := by
  rcases hG with ⟨rfl, b, hbA, hbS⟩ | ⟨rfl, hn⟩
  · refine .inl ⟨rfl, b, ?_⟩
    show keyGenInternal p b (xiOf s₀) = _
    rw [Proof.MlDsa.KeyGen.keyGenInternal_eq,
      Proof.MlDsa.KeyGen.expandA_some (A := fun r s => A (p.ℓ * r + s)) fun r hr s hs => ?_,
      Option.bind_some, Proof.MlDsa.KeyGen.expandS_some (S := S) hbS, Option.map_some,
      Proof.MlDsa.KeyGen.kgRest_eq]
    have := hbA (p.ℓ * r + s) (idx_lt hr hs)
    rwa [Nat.mul_add_div hl, Nat.div_eq_of_lt hs, Nat.add_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt hs] at this
  · exact .inr ⟨rfl, hn⟩

theorem post {p : Params} (hF : PFacts p) {s₀ s : State} (hp : TPre (YK p) s₀) (h : Done p s₀ s) :
    Spec.MlDsa.Outcome (fun b => keyGenInternal p b (xiOf s₀)) (accV s₀ s)
      (bytesAt s.mem (Buf.addr s₀ ⟨1, 0, p.pkLen⟩) p.pkLen, bytesAt s.mem (Buf.addr s₀ ⟨2, 0, p.skLen⟩) p.skLen) := by
  obtain ⟨A, S, hk, htr⟩ := h.ex
  rw [pk_bytes hF hp hk] at htr
  rw [pk_bytes hF hp hk, sk_bytes hF hp hk htr]
  exact outcome_of (by have := hF.l; omega_using [this]) hk.good

end VG.Proof.MlDsa.X86.KeyGen
