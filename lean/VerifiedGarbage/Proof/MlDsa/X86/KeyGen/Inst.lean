module

public import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Seeds
import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.NoSp
import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Prim
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.MlDsa.X86.KeyGen.Inst
import VerifiedGarbage.Proof.MlDsa.X86.Arith.NttInv
public import VerifiedGarbage.Proof.MlDsa.X86.Sample.RejNtt
import VerifiedGarbage.Proof.MlDsa.X86.Pack.BitPack
import VerifiedGarbage.Proof.Sha3.X86.Lit
public import VerifiedGarbage.Proof.MlDsa.X86.Round.Bits
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlDsa.X86.Round.Bits
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
import VerifiedGarbage.Proof.MlDsa.Arith.Mem
meta import VerifiedGarbage.Proof.MlDsa.Arith.Mem
public import VerifiedGarbage.Impl.MlDsa.X86.Sample.RejBounded
import VerifiedGarbage.Proof.MlKem.X86.Common
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.MlDsa.X86.Sample.RejNtt
meta import VerifiedGarbage.Impl.MlDsa.X86.Sample.RejBounded
meta import VerifiedGarbage.Proof.MlKem.X86.Common
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.MlDsa.Sample.HalfByte
meta import VerifiedGarbage.Proof.MlDsa.Sample.HalfByte
import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Samp
import VerifiedGarbage.Proof.MlDsa.DecideAt
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.MlKem.KPke
import VerifiedGarbage.Proof.Sha256.X86.Lit
meta import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.NoSp
meta import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Samp
meta import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Seeds
meta import VerifiedGarbage.Proof.MlDsa.DecideAt
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.MlKem.KPke
meta import VerifiedGarbage.Proof.Sha256.X86.Lit
meta import VerifiedGarbage.Proof.Sha3.X86.Lit
import VerifiedGarbage.Proof.MlKem.X86.TopLocal
meta import VerifiedGarbage.Proof.MlKem.X86.TopLocal
import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly
import VerifiedGarbage.Proof.MlKem.X86.Pack
public import VerifiedGarbage.Proof.MlDsa.Contract
public import VerifiedGarbage.Proof.MlDsa.KeyGen.Rest
meta import VerifiedGarbage.Proof.MlDsa.KeyGen.Rest
meta import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Prim
meta import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly
meta import VerifiedGarbage.Proof.MlKem.X86.Pack
meta import VerifiedGarbage.Proof.MlDsa.Contract

/-! ### `MlDsa.X86.KeyGen.Top`, which only this module used -/

section

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

end

end

/-! ### `MlDsa.X86.Sample.RejBounded`, which only this module used -/

section

/-! ### `MlDsa.Sample.HalfByteVal`, which only this module used -/

section

/-!
# ML-DSA: the coefficient of a half-byte, without a branch

An implementation can compute the coefficient `rbC η b` of an accepted
half-byte (`HalfByte.lean`) modulo `q` without a branch or a table (`hbVal`):
`b mod 5` by subtracting 10 and then 5 where they are no greater (`csubV`, a
subtraction plus the subtrahend masked by its borrow), and `(η - b') mod q` as
`η - b'` plus `q` masked by the borrow (`etaV`); `hbVal_eq` checks it on the
accepted half-bytes by evaluation.
-/

@[expose] public section

namespace VG.Proof.MlDsa.Sample

open VG.Spec.MlDsa

/-- `x - s` if `s ≤ x`: `x - s` plus `s` masked by the borrow. -/
def csubV (s x : BitVec 32) : BitVec 32 :=
  x - s + (0#32 - (BitVec.ofBool (decide (x.toNat < s.toNat))).setWidth 32 &&& s)

/-- `(η - x) mod q`: `η - x` plus `q` masked by the borrow. -/
def etaV (η x : BitVec 32) : BitVec 32 :=
  η - x + (0#32 - (BitVec.ofBool (decide (η.toNat < x.toNat))).setWidth 32 &&& 8380417#32)

/-- The coefficient of the half-byte `x`, modulo `q`, computed without a
branch: `η - (x mod 5)` for `η = 2`, `η - x` for `η = 4`. -/
def hbVal : Nat → BitVec 32 → BitVec 32
  | 2, x => etaV 2 (csubV 5 (csubV 10 x))
  | _, x => etaV 4 x

theorem hbVal_eq2 : ∀ b < 15, hbVal 2 (BitVec.ofNat 32 b) = zw (ofInt (rbC 2 b)) := by decide

theorem hbVal_eq4 : ∀ b < 9, hbVal 4 (BitVec.ofNat 32 b) = zw (ofInt (rbC 4 b)) := by decide

theorem hbVal_eq {η : Nat} (hη : η = 2 ∨ η = 4) {b : Nat} (hb : b < rbB η) :
    hbVal η (BitVec.ofNat 32 b) = zw (ofInt (rbC η b)) := by
  rcases hη with rfl | rfl
  · exact hbVal_eq2 b hb
  · exact hbVal_eq4 b hb

end VG.Proof.MlDsa.Sample

end

end

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_rej_bounded_poly`

The body is the SHAKE256 output of the seed at `scratch + 840`
(`sponge_piece`), then a branch on the public `η` to its loop, iteration `t`
of which starts with the coefficients `LA s₀ t = rbFold η [] ((H(ρ, 544)).take
t)` (`Proof/MlDsa/Sample/RejBounded.lean`) stored at `a`, `edi` after them and
`ecx` counting them (`Loop`); the end returns whether there are 256. A
half-byte is tried (`try_piece`) as `hbTry` does: its coefficient, computed
without a branch (`hbVal`), is stored if it is accepted.

Constant time: two runs whose leaks (`rejBoundedLeak`) agree accept the
half-bytes of each byte alike (`oks_at`) and so have sampled as many
coefficients after each iteration (`LA_len`): the branches, the counter
and the addresses of the stores agree; the coefficient is computed and
stored by code the taint analysis proves constant time from `edi` alone.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Sample.RejBounded

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86
open VG.Proof.MlDsa.X86.Sample
open VG.Proof.MlDsa.Sample
open VG.Impl.MlDsa.X86.Sample (argOp rbVal rbTry rbLoad rbHi rbBody rbLoop rbBound retJ qImm sponge csub etaSub)
open VG.Spec.MlDsa (Zq q H n ofInt halfByteOk rejBoundedLeak)
open VG.Proof.MlDsa (coeffAt)
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.X86.Sample (cR E1)
open VG.Proof.MlDsa.X86.Sample.RejNtt (nil_piece zw_ofNat)

/-- The layout: `rejBounded(seed, eta, a, scratch)`, 66 bytes of seed, 544
bytes of SHAKE256. -/
def L : Lay := { nA := 4, iA := 2, iS := 3, rate := 136, outlen := 544, mlen := some 66 }

theorem hL : L.Ok :=
  ⟨by decide, by decide, by decide, by decide, by decide, fun k hk => by cases hk; decide,
    ⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩⟩

/-- `η`. -/
abbrev η (s₀ : State) : Nat := (arg s₀ 1).toNat

/-- The precondition. -/
def BPre (s₀ : State) : Prop := Pre L s₀ ∧ (η s₀ = 2 ∨ η s₀ = 4)

/-- The pointers and `esp` agree, and so does the leak. -/
def BPub (s₀ s₀' : State) : Prop :=
  PubP L s₀ s₀' ∧ rejBoundedLeak (η s₀) (L.Msg s₀) = rejBoundedLeak (η s₀') (L.Msg s₀')

/-! ## The XOF output and the coefficients it gives -/

/-- The XOF output. -/
abbrev X (s₀ : State) : List Byte := L.out s₀

/-- Byte `t` of it. -/
abbrev zb (s₀ : State) (t : Nat) : Byte := (X s₀).getD t 0

/-- The coefficients sampled after `t` iterations. -/
abbrev LA (s₀ : State) (t : Nat) : List Zq := rbFold (η s₀) [] ((X s₀).take t)

theorem X_eq (s₀ : State) : X s₀ = H (L.Msg s₀) 544 := (H_eq _ _).symm

theorem X_length (s₀ : State) : (X s₀).length = 544 := by rw [X_eq]; exact H_length _ _

theorem LA_zero (s₀ : State) : LA s₀ 0 = [] := by simp [LA, rbFold]

theorem LA_succ (s₀ : State) {t : Nat} (ht : t < 544) : LA s₀ (t + 1) = rbStep (η s₀) (LA s₀ t) (zb s₀ t) := by
  simp only [LA]
  rw [List.take_add_one, List.getElem?_eq_getElem (by rw [X_length]; exact ht), Option.toList_some,
    rbFold_snoc]
  show _ = rbStep _ _ ((X s₀).getD t 0)
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [X_length]; exact ht), Option.getD_some]

namespace BPub
variable {s₀ s₀' : State} (hq : BPub s₀ s₀')
include hq

theorem eη : η s₀ = η s₀' := by rw [η, η, hq.1.2 1 (by decide)]

theorem oks : (X s₀).map (hbOks (η s₀)) = (X s₀').map (hbOks (η s₀)) := by
  have h := hq.2
  rw [← hq.eη] at h
  rw [X_eq, X_eq]
  exact leak_hbOks h (B := 544) (by decide)

theorem oks_at {t : Nat} (ht : t < 544) : hbOks (η s₀) (zb s₀ t) = hbOks (η s₀) (zb s₀' t) := by
  have := congrArg (fun l => l[t]?) hq.oks
  simp only [List.getElem?_map, List.getElem?_eq_getElem (show t < (X s₀).length by rw [X_length]; exact ht),
    List.getElem?_eq_getElem (show t < (X s₀').length by rw [X_length]; exact ht), Option.map_some,
    Option.some.injEq] at this
  simp only [zb, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (show t < (X s₀).length by rw [X_length]; exact ht),
    List.getElem?_eq_getElem (show t < (X s₀').length by rw [X_length]; exact ht), Option.getD_some]
  exact this

theorem LA_len (t : Nat) : (LA s₀ t).length = (LA s₀' t).length := by
  simp only [LA]
  rw [← hq.eη]
  exact rbFold_length_congr rfl (by rw [List.map_take, List.map_take, hq.oks])

end BPub

/-! ## The state of the loop -/

/-- After `t` iterations, with the coefficients `La` stored. -/
structure Loop (s₀ : State) (t : Nat) (La : List Zq) (s : State) : Prop extends Base L s₀ s where
  out : ∀ p < 544, s.mem (L.sA s₀ + BitVec.ofNat 64 (840 + p)) = zb s₀ p
  esi : s.gpr .esi = L.sP s₀ + BitVec.ofNat 32 (840 + t)
  ebp : s.gpr .ebp = BitVec.ofNat 32 (544 - t)
  len : La.length ≤ 256
  edi : s.gpr .edi = L.aP s₀ + BitVec.ofNat 32 (4 * La.length)
  ecx : s.gpr .ecx = BitVec.ofNat 32 La.length
  stored : Stored s.mem (L.aA s₀) La

theorem Loop.flags {s₀ s s' : State} {t : Nat} {La : List Zq} (h : Loop s₀ t La s)
    (hsp : s'.gpr .esp = s.gpr .esp) (hsi : s'.gpr .esi = s.gpr .esi) (hbp : s'.gpr .ebp = s.gpr .ebp)
    (hdi : s'.gpr .edi = s.gpr .edi) (hcx : s'.gpr .ecx = s.gpr .ecx)
    (hm : s'.mem = s.mem) (hr : s'.rd = s.rd) (hw : s'.wr = s.wr) : Loop s₀ t La s' :=
  ⟨⟨by rw [hsp, h.esp], by rw [hr, h.rd], by rw [hw, h.wr], by rw [hm]; exact h.frame⟩,
    by rw [hm]; exact h.out, by rw [hsi, h.esi], by rw [hbp, h.ebp], h.len, by rw [hdi, h.edi], by rw [hcx, h.ecx],
    by rw [hm]; exact h.stored⟩

/-! ## A half-byte -/

/-- The coefficient of the half-byte in `edx`, into `ebx`. -/
theorem rbVal_run {e : Nat} (he : e = 2 ∨ e = 4) (s : State) :
    WP isa (.block (rbVal e)) s fun s' => s'.gpr .ebx = hbVal e (s.gpr .edx) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r, r ≠ .edx → r ≠ .ebx → s'.gpr r = s.gpr r := by
  have hqi : qImm = 8380417#32 := rfl
  apply WP.of_runBlock
  rcases he with rfl | rfl
  · simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, rbVal, Impl.MlDsa.X86.Sample.csub, etaSub, List.cons_append,
      List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, State.setReg,
      arithFlags, State.setFlags, Option.bind_some, Option.map_some, BitVec.sub_self, hqi, 
      Option.some.injEq, exists_eq_left']
    refine ⟨by simp [hbVal, etaV, csubV], trivial, trivial, trivial, fun r h1 h2 => by simp [h1, h2]⟩
  · simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, rbVal, etaSub, runBlock_cons, runStep_some, runBlock_nil, exec,
      execAlu, readSrc, State.setReg,
      arithFlags, State.setFlags, Option.bind_some, Option.map_some, BitVec.sub_self, hqi, 
      Option.some.injEq, exists_eq_left']
    refine ⟨by simp [hbVal, etaV], trivial, trivial, trivial, fun r h1 h2 => by simp [h1, h2]⟩

/-- The store block: `a[j] ← ebx`, `j` incremented. -/
abbrev stBlk : List Instr := [.store (at_ .edi 0) .ebx, .alu .add .edi (.imm 4), .alu .add .ecx (.imm 1)]

theorem store_ok {s₀ : State} (hp : BPre s₀) {t : Nat} {La : List Zq} (x : Zq) (hl : La.length < 256) {s : State}
    (h : Loop s₀ t La s) (hbx : s.gpr .ebx = zw x) :
    WP isa (.block stBlk) s fun s' => Loop s₀ t (La ++ [x]) s' ∧ s'.gpr .eax = s.gpr .eax := by
  have ha := hp.1.a_fit
  have ea : (L.aP s₀ + BitVec.ofNat 32 (4 * La.length) + BitVec.ofNat 32 0).setWidth 64 =
      coeffAddr (L.aA s₀) La.length := by
    rw [ea_add (by simp only [L] at ha ⊢; omega_using [hl, ha])]; rfl
  have hin : InRegions s.wr (coeffAddr (L.aA s₀) La.length) 4 := hp.1.inA h.wr hl
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, at_, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    State.ea, State.store32, State.setReg, arithFlags, State.setFlags, Option.bind_some, h.edi, ea, hin,
    hbx, Option.some.injEq, exists_eq_left']
  refine ⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame.writeW (r := L.aR s₀) (by simp) _
    (coeff_contains _ hl)⟩, fun p hp' => ?_, by simp [h.esi], by simp [h.ebp],
    (by simp only [List.length_append, List.length_singleton]; omega_using [hl]), ?_, ?_, stored_snoc h.stored hl x⟩, by simp⟩
  · refine (((Frame.refl _ _).writeW (List.mem_singleton_self (L.aR s₀)) _ (coeff_contains _ hl)) _
      fun r hr hc => ?_).trans (h.out p hp')
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.1.a_s _ hc ((hp.1.sub_s (o := 840 + p) (n := 1) (by omega_using [hp'])) _ (Region.contains_self _ _))
  · simp only [ite_true, List.length_append, List.length_singleton]
    rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, add_ofNat_add]; congr 2
  · simp only [ite_true, h.ecx, List.length_append, List.length_singleton]
    rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ofNat_add_ofNat]

/-- An accepted half-byte `b` in `edx`: its coefficient stored. -/
theorem acc_ok {e : Nat} (he : e = 2 ∨ e = 4) {s₀ : State} (hp : BPre s₀) {t : Nat} {La : List Zq} {b : Nat}
    (hb : b < rbB e) (hl : La.length < 256) {s : State} (h : Loop s₀ t La s)
    (hdx : s.gpr .edx = BitVec.ofNat 32 b) :
    WP isa (.block (rbVal e ++ stBlk)) s fun s' =>
      Loop s₀ t (La ++ [ofInt (rbC e b)]) s' ∧ s'.gpr .eax = s.gpr .eax := by
  rw [WP.block_append_iff]
  refine (rbVal_run he s).mono fun s1 ⟨hbx, hm, hr, hw, hg⟩ => ?_
  refine (store_ok hp _ hl (h.flags (hg _ (by decide) (by decide)) (hg _ (by decide) (by decide))
    (hg _ (by decide) (by decide)) (hg _ (by decide) (by decide)) (hg _ (by decide) (by decide)) hm hr hw)
    (by rw [hbx, hdx, hbVal_eq he hb])).mono fun s2 ⟨h2, e2⟩ => ⟨h2, by rw [e2, hg _ (by decide) (by decide)]⟩

/-- A half-byte `hb s₀` in `edx` tried, with `eax = E s₀` and the facts `X s₀` kept. -/
theorem try_piece {e : Nat} (he : e = 2 ∨ e = 4) (t : Nat) (La : State → List Zq) (hb E : State → Nat)
    (X : State → Prop)
    (hpub : ∀ s₀ s₀', BPre s₀ → BPre s₀' → BPub s₀ s₀' →
      (La s₀).length = (La s₀').length ∧ decide (hb s₀ < rbB (η s₀)) = decide (hb s₀' < rbB (η s₀')))
    (tc : TaintOk [] (.block [.alu .cmp .edx (.imm (rbBound e))]))
    (ts : TaintOk [.edi] (.block (rbVal e ++ stBlk))) :
    Piece BPre BPub
      (fun s₀ s => ((Loop s₀ t (La s₀) s ∧ s.gpr .edx = BitVec.ofNat 32 (hb s₀) ∧
        s.gpr .eax = BitVec.ofNat 32 (E s₀) ∧ (La s₀).length < 256 ∧ hb s₀ < 16) ∧ η s₀ = e) ∧ X s₀)
      (fun s₀ s => ((Loop s₀ t (hbTry (η s₀) (La s₀) (hb s₀)) s ∧ s.gpr .eax = BitVec.ofNat 32 (E s₀)) ∧
        η s₀ = e) ∧ X s₀)
      (rbTry e) := by
  obtain ⟨_, tc⟩ := tc
  obtain ⟨_, ts⟩ := ts
  have hbnd : (rbBound e).toNat = rbB e := by rcases he with rfl | rfl <;> rfl
  refine Piece.seq (B := fun s₀ s => (((Loop s₀ t (La s₀) s ∧ s.gpr .edx = BitVec.ofNat 32 (hb s₀) ∧
      s.gpr .eax = BitVec.ofNat 32 (E s₀) ∧ (La s₀).length < 256 ∧ hb s₀ < 16) ∧ η s₀ = e) ∧ X s₀) ∧
      eval .b s = some (decide (hb s₀ < rbB (η s₀)))) ?_
    (Piece.ite (fun s₀ => decide (hb s₀ < rbB (η s₀))) (fun _ _ _ h => h.2)
      (fun s₀ s₀' h₀ h₀' hq => (hpub s₀ s₀' h₀ h₀' hq).2) ?_ ?_)
  · refine Piece.taint [] (fun s₀ s hp ha => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp)) tc
    obtain ⟨⟨⟨h, hdx, hax, hl, h16⟩, hη⟩, hx⟩ := ha
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags,
      Option.bind_some, Option.some.injEq, exists_eq_left']
    refine ⟨⟨⟨⟨h.flags rfl rfl rfl rfl rfl rfl rfl rfl, hdx, hax, hl, h16⟩, hη⟩, hx⟩, ?_⟩
    simp only [eval, hdx, hbnd, toNat_ofNat32 (show hb s₀ < 2 ^ 32 by omega_using [h16]), hη]
  · refine Piece.taint [.edi] (fun s₀ s hp ⟨⟨⟨⟨⟨h, hdx, hax, hl, _⟩, hη⟩, hx⟩, _⟩, hb'⟩ => ?_)
      (fun s₀ s₀' s s' h₀ h₀' hq ⟨⟨⟨⟨⟨h, _⟩, _⟩, _⟩, _⟩, _⟩ ⟨⟨⟨⟨⟨h', _⟩, _⟩, _⟩, _⟩, _⟩ r hr => ?_) ts
    · have hb2 : hb s₀ < rbB e := hη ▸ of_decide_eq_true hb'
      refine (acc_ok he hp hb2 hl h hdx).mono fun s' ⟨h1, h2⟩ => ⟨⟨⟨?_, by rw [h2, hax]⟩, hη⟩, hx⟩
      rw [hη, hbTry_eq he, ifT hb2]; exact h1
    · simp only [List.mem_singleton] at hr
      subst hr
      rw [h.edi, h'.edi, hq.1.aP hL, (hpub s₀ s₀' h₀ h₀' hq).1]
  · exact nil_piece fun s₀ s _ ⟨⟨⟨⟨⟨h, _, hax, _⟩, hη⟩, hx⟩, _⟩, hb'⟩ => by
      refine ⟨⟨⟨?_, hax⟩, hη⟩, hx⟩
      rw [hη, hbTry_eq he, ifF (hη ▸ of_decide_eq_false hb')]; exact h

/-! ## An iteration -/

/-- The half-bytes of byte `t`. -/
abbrev lo (s₀ : State) (t : Nat) : Nat := (zb s₀ t).toNat % 16
abbrev hi (s₀ : State) (t : Nat) : Nat := (zb s₀ t).toNat / 16

/-- The coefficients after the low half-byte of byte `t`. -/
abbrev L1 (s₀ : State) (t : Nat) : List Zq := hbTry (η s₀) (LA s₀ t) (lo s₀ t)

theorem ok_bound {s₀ : State} (hp : BPre s₀) (b : Nat) :
    halfByteOk (η s₀) b = if b < rbB (η s₀) then 1 else 0 := halfByteOk_eq hp.2 b

theorem lo_pub {s₀ s₀' : State} (hp : BPre s₀) (hq : BPub s₀ s₀') {t : Nat} (ht : t < 544) :
    decide (lo s₀ t < rbB (η s₀)) = decide (lo s₀' t < rbB (η s₀')) := by
  have h := congrArg Prod.fst (hq.oks_at ht)
  simp only [hbOks] at h
  rw [ok_bound hp, ok_bound hp] at h
  rw [← hq.eη]
  by_cases h1 : lo s₀ t < rbB (η s₀) <;> by_cases h2 : lo s₀' t < rbB (η s₀) <;>
    simp only [h1, h2, ↓reduceIte, decide_true, decide_false] at h ⊢ <;> omega

theorem hi_pub {s₀ s₀' : State} (hp : BPre s₀) (hq : BPub s₀ s₀') {t : Nat} (ht : t < 544) :
    decide (hi s₀ t < rbB (η s₀)) = decide (hi s₀' t < rbB (η s₀')) := by
  have h := congrArg Prod.snd (hq.oks_at ht)
  simp only [hbOks] at h
  rw [ok_bound hp, ok_bound hp] at h
  rw [← hq.eη]
  by_cases h1 : hi s₀ t < rbB (η s₀) <;> by_cases h2 : hi s₀' t < rbB (η s₀) <;>
    simp only [h1, h2, ↓reduceIte, decide_true, decide_false] at h ⊢ <;> omega

theorem L1_len {s₀ s₀' : State} (hq : BPub s₀ s₀') {t : Nat} (ht : t < 544) :
    (L1 s₀ t).length = (L1 s₀' t).length := by
  have h := congrArg Prod.fst (hq.oks_at ht)
  simp only [hbOks] at h
  simp only [L1]
  rw [hbTry_length, hbTry_length, hq.LA_len t, h, hq.eη]

theorem LA_step {s₀ : State} {t : Nat} (ht : t < 544) :
    LA s₀ (t + 1) = if (LA s₀ t).length < 256 then
      (if (L1 s₀ t).length < 256 then hbTry (η s₀) (L1 s₀ t) (hi s₀ t) else L1 s₀ t) else LA s₀ t := by
  rw [LA_succ s₀ ht, rbStep]

theorem load_ok {s₀ : State} (hp : BPre s₀) {t : Nat} (ht : t < 544) {s : State} (h : Loop s₀ t (LA s₀ t) s) :
    WP isa (.block rbLoad) s fun s' => Loop s₀ t (LA s₀ t) s' ∧ s'.gpr .edx = BitVec.ofNat 32 (lo s₀ t) ∧
      s'.gpr .eax = BitVec.ofNat 32 (zb s₀ t).toNat ∧ eval .b s' = some (decide ((LA s₀ t).length < 256)) := by
  have hs := hp.1.s_fit
  have e0 : (L.sP s₀ + BitVec.ofNat 32 (840 + t) + BitVec.ofNat 32 0).setWidth 64 =
      L.sA s₀ + BitVec.ofNat 64 (840 + t) := by
    rw [ea_add (by simp only [L] at hs ⊢; omega_using [ht, hs])]; rfl
  have i0 := hp.1.inS' h.wr (o := 840 + t) (n := 1) (by omega_using [ht])
  have v0 := h.out t ht
  have hl := h.len
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, rbLoad, at_, runBlock_cons, runStep_some, runBlock_nil, exec,
    execAlu, readSrc, State.ea, State.load8, State.setReg, arithFlags, State.setFlags,
    Option.map_some, Option.bind_some, h.esi, e0, i0, v0, Option.some.injEq, exists_eq_left']
  refine ⟨h.flags (by simp) (by simp) (by simp) (by simp) (by simp) rfl rfl rfl, ?_, ?_, ?_⟩
  · refine eq_ofNat_of_toNat ?_
    rw [show (15 : BitVec 32) = BitVec.ofNat 32 (2 ^ 4 - 1) from rfl, toNat_and_mask _ _ (by decide), toNat_byte32]
  · exact eq_ofNat_of_toNat (toNat_byte32 _)
  · simp only [eval, h.ecx, toNat_ofNat32 (show (LA s₀ t).length < 2 ^ 32 by omega_using [hl])]
    rfl

theorem hi_ok {s₀ : State} {t : Nat} {La : List Zq} {s : State} (h : Loop s₀ t La s)
    (hax : s.gpr .eax = BitVec.ofNat 32 (zb s₀ t).toNat) :
    WP isa (.block rbHi) s fun s' => Loop s₀ t La s' ∧ s'.gpr .edx = BitVec.ofNat 32 (hi s₀ t) ∧
      s'.gpr .eax = BitVec.ofNat 32 (hi s₀ t) ∧ eval .b s' = some (decide (La.length < 256)) := by
  have hl := h.len
  have hz := (zb s₀ t).isLt
  have hv : s.gpr .eax >>> 4 = BitVec.ofNat 32 (hi s₀ t) := by
    rw [hax]; exact eq_ofNat_of_toNat (by rw [toNat_shr, toNat_ofNat32 (by omega_using [])])
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, Nat.reduceEqDiff, Nat.reduceSub, and_self, rbHi, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    execShift, readSrc, State.setReg, arithFlags, State.setFlags, Option.map_some, Option.bind_some, hv,
    Option.some.injEq, exists_eq_left']
  refine ⟨h.flags (by simp) (by simp) (by simp) (by simp) (by simp) rfl rfl rfl, by simp, by simp, ?_⟩
  simp only [eval, h.ecx, toNat_ofNat32 (show La.length < 2 ^ 32 by omega_using [hl])]
  rfl

theorem end_ok {s₀ : State} {t : Nat} (ht : t < 544) {La : List Zq} {s : State} (h : Loop s₀ t La s) :
    WP isa (.block [.alu .add .esi (.imm 1), .alu .sub .ebp (.imm 1)]) s
      fun s' => Loop s₀ (t + 1) La s' ∧ eval .ne s' = some (decide (t + 1 < 544)) := by
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    State.setReg, arithFlags, State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, h.out, ?_, ?_, h.len, by simp [h.edi], by simp [h.ecx],
    h.stored⟩, ?_⟩
  · simp only [ite_true, h.esi]
    rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, add_ofNat_add]; congr 2
  · simp only [ite_true, h.ebp]
    exact cnt_next ht
  · simp only [eval, h.ebp]
    exact cnt_ne ht (by omega_using [])

theorem body_piece {e : Nat} (he : e = 2 ∨ e = 4) (t : Nat) (ht : t < 544)
    (tc : TaintOk [] (.block [.alu .cmp .edx (.imm (rbBound e))]))
    (ts : TaintOk [.edi] (.block (rbVal e ++ stBlk))) :
    Piece BPre BPub (fun s₀ s => Loop s₀ t (LA s₀ t) s ∧ η s₀ = e)
      (fun s₀ s => (Loop s₀ (t + 1) (LA s₀ (t + 1)) s ∧ η s₀ = e) ∧ eval .ne s = some (decide (t + 1 < 544)))
      (rbBody e) := by
  refine Piece.seq (B := fun s₀ s => (Loop s₀ t (LA s₀ t) s ∧ s.gpr .edx = BitVec.ofNat 32 (lo s₀ t) ∧
      s.gpr .eax = BitVec.ofNat 32 (zb s₀ t).toNat ∧ eval .b s = some (decide ((LA s₀ t).length < 256))) ∧
      η s₀ = e) ?_ (Piece.seq (B := fun s₀ s => Loop s₀ t (LA s₀ (t + 1)) s ∧ η s₀ = e) ?_
        (Piece.taint [] (fun s₀ s _ ⟨h, hη⟩ => (end_ok ht h).mono fun s' ⟨h', hc⟩ => ⟨⟨h', hη⟩, hc⟩)
          (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp)) (by native_taint_decide)))
  · refine Piece.taint [.esi] (fun s₀ s hp ⟨h, hη⟩ => (load_ok hp ht h).mono fun s' h' => ⟨h', hη⟩)
      (fun s₀ s₀' s s' _ _ hq ⟨h, _⟩ ⟨h', _⟩ r hr => ?_) (by native_taint_decide)
    simp only [List.mem_singleton] at hr
    subst hr
    rw [h.esi, h'.esi, hq.1.sP hL]
  refine Piece.ite (fun s₀ => decide ((LA s₀ t).length < 256)) (fun _ _ _ h => h.1.2.2.2)
    (fun s₀ s₀' _ _ hq => by rw [hq.LA_len t]) ?_ ?_
  · -- the low half-byte, then the high one
    refine Piece.seq ((try_piece he t (fun s₀ => LA s₀ t) (fun s₀ => lo s₀ t) (fun s₀ => (zb s₀ t).toNat)
      (fun s₀ => (LA s₀ t).length < 256) (fun s₀ s₀' h₀ _ hq => ⟨hq.LA_len t, lo_pub h₀ hq ht⟩) tc ts).mono
        (fun s₀ s _ ⟨⟨⟨h, hdx, hax, _⟩, hη⟩, hb⟩ =>
          ⟨⟨⟨h, hdx, hax, of_decide_eq_true hb, Nat.mod_lt _ (by decide)⟩, hη⟩, of_decide_eq_true hb⟩)
        fun _ _ _ h => h) ?_
    refine Piece.seq (B := fun s₀ s => ((Loop s₀ t (L1 s₀ t) s ∧ s.gpr .edx = BitVec.ofNat 32 (hi s₀ t) ∧
        s.gpr .eax = BitVec.ofNat 32 (hi s₀ t) ∧ eval .b s = some (decide ((L1 s₀ t).length < 256))) ∧
        η s₀ = e) ∧ (LA s₀ t).length < 256)
      (Piece.taint [] (fun s₀ s _ ⟨⟨⟨h, hax⟩, hη⟩, hx⟩ => (hi_ok h hax).mono fun s' h' => ⟨⟨h', hη⟩, hx⟩)
        (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp)) (by native_taint_decide)) ?_
    refine Piece.ite (fun s₀ => decide ((L1 s₀ t).length < 256)) (fun _ _ _ h => h.1.1.2.2.2)
      (fun s₀ s₀' _ _ hq => by rw [L1_len hq ht]) ?_ ?_
    · refine (try_piece he t (fun s₀ => L1 s₀ t) (fun s₀ => hi s₀ t) (fun s₀ => hi s₀ t)
        (fun s₀ => (LA s₀ t).length < 256 ∧ (L1 s₀ t).length < 256)
        (fun s₀ s₀' h₀ _ hq => ⟨L1_len hq ht, hi_pub h₀ hq ht⟩) tc ts).mono
          (fun s₀ s _ ⟨⟨⟨⟨h, hdx, hax, _⟩, hη⟩, hx⟩, hb⟩ =>
            ⟨⟨⟨h, hdx, hax, of_decide_eq_true hb,
              show (zb s₀ t).toNat / 16 < 16 by have := (zb s₀ t).isLt; omega_using []⟩, hη⟩, hx, of_decide_eq_true hb⟩) ?_
      rintro s₀ s _ ⟨⟨⟨h, -⟩, hη⟩, hx, hx'⟩
      refine ⟨?_, hη⟩
      rw [LA_step ht, ifT hx, ifT hx']; exact h
    · exact nil_piece fun s₀ s _ ⟨⟨⟨⟨h, _⟩, hη⟩, hx⟩, hb⟩ => by
        refine ⟨?_, hη⟩
        rw [LA_step ht, ifT hx, ifF (of_decide_eq_false hb)]; exact h
  · exact nil_piece fun s₀ s _ ⟨⟨⟨h, _⟩, hη⟩, hb⟩ => by
      refine ⟨?_, hη⟩
      rw [LA_step ht, ifF (of_decide_eq_false hb)]; exact h

theorem loop_piece {e : Nat} (he : e = 2 ∨ e = 4)
    (tc : TaintOk [] (.block [.alu .cmp .edx (.imm (rbBound e))]))
    (ts : TaintOk [.edi] (.block (rbVal e ++ stBlk))) :
    Piece BPre BPub (fun s₀ s => Loop s₀ 0 (LA s₀ 0) s ∧ η s₀ = e)
      (fun s₀ s => Loop s₀ 544 (LA s₀ 544) s ∧ η s₀ = e) (.loop (rbBody e) .ne) :=
  Piece.loop (fun t s₀ s => Loop s₀ t (LA s₀ t) s ∧ η s₀ = e) (by decide) fun t ht => body_piece he t ht tc ts

/-- Before the branch on `η`: `edi = a`, and whether `η = 2` in ZF. -/
def Sel (s₀ s : State) : Prop :=
  Out L s₀ s ∧ s.gpr .edi = L.aP s₀ ∧ eval .e s = some (decide (η s₀ = 2))

theorem sel_piece : Piece BPre BPub (Out L) Sel
    (.block [.mov .edi (.mem (argOp 2)), .mov .eax (.mem (argOp 1)), .alu .cmp .eax (.imm 2)]) := by
  refine Piece.taint [.esp] (fun s₀ s hp h => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_)
    (by native_taint_decide)
  · have a₁ := h.argEa (i := 1)
    have i₁ := h.argIn hp.1 (i := 1) (by decide)
    have v₁ := h.args 1 (by decide)
    have a₂ := h.argEa (i := 2)
    have i₂ := h.argIn hp.1 (i := 2) (by decide)
    have v₂ := h.args 2 (by decide)
    simp only [Nat.mul_one, Nat.reduceMul, Nat.reduceAdd] at a₁ a₂
    apply WP.of_runBlock
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceAdd, Nat.reduceMul, argOp, at_, runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu, readSrc, State.ea, State.load32, State.setReg, arithFlags, State.setFlags, Option.map_some,
      Option.bind_some, a₁, i₁, v₁, a₂, i₂, v₂, Option.some.injEq, exists_eq_left']
    refine ⟨⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, h.args, by simp [h.esi]⟩, h.out⟩, by simp; rfl, ?_⟩
    simp only [eval, sub_beq_zero]
    rfl
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.esp, h'.esp, hq.1.e1]

theorem init_piece (e : Nat) (b : Bool) (hb : ∀ s₀, BPre s₀ → decide (η s₀ = 2) = b → η s₀ = e) :
    Piece BPre BPub (fun s₀ s => Sel s₀ s ∧ decide (η s₀ = 2) = b) (fun s₀ s => Loop s₀ 0 (LA s₀ 0) s ∧ η s₀ = e)
    (.block [.alu .add .esi (.imm (BitVec.ofNat 32 840)), .mov .ecx (.imm 0), .mov .ebp (.imm 544)]) := by
  refine Piece.taint [] (fun s₀ s hp ⟨⟨h, hdi, _⟩, e⟩ => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
    (by native_taint_decide)
  apply WP.of_runBlock
  simp only [Nat.reducePow, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    State.setReg, arithFlags, State.setFlags, Option.bind_some, Option.map_some, Option.some.injEq,
    exists_eq_left']
  rw [LA_zero]
  refine ⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, fun p hp' => ?_, by simp [h.esi], by simp, by simp,
    by simp [hdi], by simp, stored_nil _ _⟩, hb s₀ hp e⟩
  exact h.out p hp'

theorem branch_piece : Piece BPre BPub Sel (fun s₀ s => Loop s₀ 544 (LA s₀ 544) s)
    (.ite .e (rbLoop 2) (rbLoop 4)) := by
  refine Piece.ite (fun s₀ => decide (η s₀ = 2)) (fun _ _ _ h => h.2.2)
    (fun s₀ s₀' _ _ hq => by rw [hq.eη]) ?_ ?_
  · exact (Piece.seq (init_piece 2 true fun s₀ _ e => of_decide_eq_true e)
      (loop_piece (Or.inl rfl) ⟨_, by native_taint_decide⟩ ⟨_, by native_taint_decide⟩)).mono (fun _ _ _ h => h)
      fun _ _ _ h => h.1
  · exact (Piece.seq (init_piece 4 false fun s₀ hp e => hp.2.resolve_left (of_decide_eq_false e))
      (loop_piece (Or.inr rfl) ⟨_, by native_taint_decide⟩ ⟨_, by native_taint_decide⟩)).mono (fun _ _ _ h => h)
      fun _ _ _ h => h.1

/-- The end: 1 in `eax` if there are 256 coefficients, 0 if fewer. -/
structure Fin (s₀ s : State) : Prop extends Loop s₀ 544 (LA s₀ 544) s where
  eax : s.gpr .eax = BitVec.ofNat 32 ((LA s₀ 544).length / 256)

theorem fin_piece : Piece BPre BPub (fun s₀ s => Loop s₀ 544 (LA s₀ 544) s) Fin (.block (retJ .ecx)) := by
  refine Piece.taint [] (fun s₀ s _ h => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
    (by native_taint_decide)
  have hl := h.len
  refine wp_movr (wp_shr (by decide) (by decide) fun s' o e => WP.block_nil_iff.mpr ?_)
  have g : ∀ r, r ≠ .eax → s'.gpr r = s.gpr r := fun r hr => by
    rw [o.gpr r (by simp [hr])]; simp [State.setReg, hr]
  refine ⟨⟨⟨by rw [g _ (by decide), h.esp], by rw [o.rd]; exact h.rd, by rw [o.wr]; exact h.wr,
    by rw [o.mem]; exact h.frame⟩, by rw [o.mem]; exact h.out, by rw [g _ (by decide), h.esi],
    by rw [g _ (by decide), h.ebp], h.len, by rw [g _ (by decide), h.edi], by rw [g _ (by decide), h.ecx],
    by rw [o.mem]; exact h.stored⟩, ?_⟩
  rw [e]
  simp only [State.setReg, ite_true, h.ecx]
  exact eq_ofNat_of_toNat (by rw [toNat_shr, toNat_ofNat32 (show (LA s₀ 544).length < 2 ^ 32 by omega_using [hl])])

end VG.Proof.MlDsa.X86.Sample.RejBounded

namespace VG.Proof.MlDsa.X86.Sample.RejBounded

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86
open VG.Proof.MlDsa.X86.Sample
open VG.Proof.MlDsa.Sample
open VG.Impl.MlDsa.X86.Sample (argOp rbLoop retJ sponge)
open VG.Spec.MlDsa (Zq H)

/-! ## The whole function -/

theorem main_piece : Piece BPre BPub (fun s₀ s => s = P0 s₀) Fin
    (.seq (sponge 3 136 (.imm 66) 544)
      (.seq (.block [.mov .edi (.mem (argOp 2)), .mov .eax (.mem (argOp 1)), .alu .cmp .eax (.imm 2)])
        (.seq (.ite .e (rbLoop 2) (rbLoop 4)) (.block (retJ .ecx))))) :=
  Piece.seq ((sponge_piece hL).pre_mono (fun _ h => h.1) fun _ _ _ _ h => h.1) <|
    Piece.seq sel_piece <| Piece.seq branch_piece fin_piece

theorem piece : Piece BPre BPub (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (Fin s₀) s₀ s')
    Impl.MlDsa.X86.Sample.rejBounded :=
  Piece.leaf L.W (NoSp.of_all (by decide +kernel))
    (fun _ hp => ⟨by have := hp.1.sp; omega_using [this], by have := hp.1.sp'; omega_using [this]⟩)
    (fun _ hp => hp.1.hW) (fun _ _ _ _ hq => hq.1.1)
    (main_piece.mono (fun _ _ _ h => h) fun _ _ _ h => ⟨⟨h.frame, h.esp, h.rd, h.wr⟩, h⟩)

theorem BPre.of {s₀ : State} (h : (Proof.MlDsa.rejBoundedContract X86.abi 56).pre s₀) : BPre s₀ := by
  sig_pre [Proof.MlDsa.rejBoundedContract, Proof.MlDsa.rejBoundedSig, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    show (66 : Nat) < 136 by decide⟩, h22⟩

theorem LA_all (s₀ : State) : LA s₀ 544 = rbFold (η s₀) [] (H (L.Msg s₀) 544) := by
  simp only [LA]; rw [List.take_of_length_le (by rw [X_length]), X_eq]

/-- Memory with the arguments `0`, `2`, `0x100` and `0x1000` at `0x5004`. -/
def satMem : Mem := fun a => if a = 0x5008 then 2 else if a = 0x500d then 1 else if a = 0x5011 then 0x10 else 0

theorem verified :
    Verified X86.target Impl.MlDsa.X86.Sample.rejBounded (Proof.MlDsa.rejBoundedContract X86.abi 56) := by
  refine Piece.verified ((piece.pre_mono (fun _ h => BPre.of h) fun s s' _ _ h => ?_).mono
    (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · sig_pub [Proof.MlDsa.rejBoundedContract, Proof.MlDsa.rejBoundedSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes] at h
    obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := h
    refine ⟨⟨e₁, fun i hi => ?_⟩, e₂⟩
    match i, hi with
    | 0, _ => exact e₃
    | 1, _ => exact e₄
    | 2, _ => exact e₅
    | 3, _ => exact e₆
  · obtain ⟨habi, -, -, s, hfin, hm, hax⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [Proof.MlDsa.rejBoundedContract, Proof.MlDsa.rejBoundedSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]
    rw [setWidth_append32, hax, hfin.eax]
    have hl := hfin.len
    by_cases e : (LA s₀ 544).length = 256
    · have hp : Proof.MlDsa.PolyIs s.mem (L.aA s₀) (toPoly (LA s₀ 544)) := stored_polyIs hfin.stored e
      rw [LA_all] at e hp
      replace hp := Proof.MlDsa.Arith.polyIs_frame hm (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact ((BPre.of h₀).1.hW _ List.mem_cons_self).1.symm) hp
      rw [LA_all, e]
      refine ⟨fun _ => hp.1, .inl ⟨rfl, { Spec.MlDsa.minBounds with rejBounded := 544 }, ?_⟩⟩
      show (Spec.MlDsa.rejBoundedPoly (η s₀) 544 (L.Msg s₀)).map Spec.MlDsa.toRq =
        some (Proof.MlDsa.polyAt s'.mem (L.aA s₀))
      rw [rejBounded_some _ e, hp.2]
    · rw [Nat.div_eq_of_lt (by omega_using [hl, e])]
      rw [LA_all] at e
      refine ⟨fun h => absurd (congrArg BitVec.toNat h) (by show ¬ (0 = 1); decide),
        .inr ⟨rfl, ?_⟩⟩
      show (Spec.MlDsa.rejBoundedPoly (η s₀) Spec.MlDsa.minBounds.rejBounded (L.Msg s₀)).map Spec.MlDsa.toRq = none
      rw [rejBounded_none _ (B := 544) (by decide) e]; rfl
  · let st := satState satMem [⟨0, 66⟩] [⟨0x100, 1024⟩, ⟨0x1000, 2048⟩, ⟨0x5004, 16⟩]
    refine ⟨st, ?_⟩
    sig_sat_check [Proof.MlDsa.rejBoundedContract, Proof.MlDsa.rejBoundedSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]

end VG.Proof.MlDsa.X86.Sample.RejBounded

end

end

/-! ### `MlDsa.X86.Round.Power2Round`, which only this module used -/

section

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_power2round`

One loop over the coefficients (`p2r_step`): `x = a + 4095`, `t1 = x >> 13`
and `t0 = (x mod 2¹³) - 4095`, plus `q` if negative (`power2Round_eq`,
`power2Round_t0`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Round

open VG VG.X86 VG.X86.Wp VG.Impl.MlDsa.X86.Round
open VG.Impl.MlKem.X86 (at_ leaf)
open VG.Spec.MlDsa (q power2Round ofInt)
open VG.Proof.MlDsa (coeffAt Reduced polyAt PolyIs NatPolyIs power2RoundContract power2RoundSig)
open VG.Proof.MlDsa.Round (coeffAddr pR coeff_contains coeffAt_frame coeffAt_writeW coeffAt_writeW_disjoint
  n_eq q_eq polyAt_val natPolyIs_of_toNat polyIs_of_toNat map_get power2Round_eq power2Round_t0)
open VG.Proof.MlKem.X86 (Only E0 P0 P0_esp P0_wr frameR retR LeafPost LeafEnd Piece satState
  toNat_ofNat32 eq_ofNat_of_toNat ptr_next cnt_next cnt_ne)

structure P2Pre (s₀ : State) : Prop where
  sp : 16 ≤ (E0 s₀).toNat
  sp' : (E0 s₀).toNat + 4 + 12 ≤ 2 ^ 32
  rd : s₀.rd = [pR (pA s₀ 0)]
  wr : s₀.wr = [pR (pA s₀ 1), pR (pA s₀ 2), aR s₀ 3]
  t_1 : (pR (pA s₀ 0)).Disjoint (pR (pA s₀ 1))
  t_0 : (pR (pA s₀ 0)).Disjoint (pR (pA s₀ 2))
  t_a : (pR (pA s₀ 0)).Disjoint (aR s₀ 3)
  t1_t0 : (pR (pA s₀ 1)).Disjoint (pR (pA s₀ 2))
  t1_a : (pR (pA s₀ 1)).Disjoint (aR s₀ 3)
  t0_a : (pR (pA s₀ 2)).Disjoint (aR s₀ 3)
  ret_t : (retR s₀).Disjoint (pR (pA s₀ 0))
  ret_1 : (retR s₀).Disjoint (pR (pA s₀ 1))
  ret_0 : (retR s₀).Disjoint (pR (pA s₀ 2))
  ret_a : (retR s₀).Disjoint (aR s₀ 3)
  stk_t : (stkR s₀).Disjoint (pR (pA s₀ 0))
  stk_1 : (stkR s₀).Disjoint (pR (pA s₀ 1))
  stk_0 : (stkR s₀).Disjoint (pR (pA s₀ 2))
  stk_a : (stkR s₀).Disjoint (aR s₀ 3)
  t_fit : (arg s₀ 0).toNat + 1024 ≤ 2 ^ 32
  t1_fit : (arg s₀ 1).toNat + 1024 ≤ 2 ^ 32
  t0_fit : (arg s₀ 2).toNat + 1024 ≤ 2 ^ 32
  t_red : Reduced s₀.mem (pA s₀ 0)

theorem P2Pre.of {s₀ : State} (h : (power2RoundContract X86.abi 16).pre s₀) : P2Pre s₀ := by
  sig_pre [power2RoundContract, power2RoundSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22⟩

/-- The public data: the stack pointer and the pointers. -/
def P2Pub (s₀ s₀' : State) : Prop :=
  E0 s₀ = E0 s₀' ∧ arg s₀ 0 = arg s₀' 0 ∧ arg s₀ 1 = arg s₀' 1 ∧ arg s₀ 2 = arg s₀' 2

/-- The `r₁` of `Power2Round(a)`. -/
def p2r1 (a : Nat) : Nat := (a + 4095) / 8192

/-- The `r₀` of `Power2Round(a)`, modulo `q`. -/
def p2r0 (a : Nat) : Nat := condAddN ((a + 4095) % 8192) 4095 q

/-- After `k` coefficients. -/
structure P2Inv (s₀ : State) (k : Nat) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  esi : s.gpr .esi = arg s₀ 0 + BitVec.ofNat 32 (4 * k)
  edi : s.gpr .edi = arg s₀ 1 + BitVec.ofNat 32 (4 * k)
  ebp : s.gpr .ebp = arg s₀ 2 + BitVec.ofNat 32 (4 * k)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (256 - k)
  frame : Frame [pR (pA s₀ 1), pR (pA s₀ 2)] (P0 s₀).mem s.mem
  out1 : ∀ i < k, coeffAt s.mem (pA s₀ 1) i = BitVec.ofNat 32 (p2r1 (coeffAt s₀.mem (pA s₀ 0) i).toNat)
  out0 : ∀ i < k, coeffAt s.mem (pA s₀ 2) i = BitVec.ofNat 32 (p2r0 (coeffAt s₀.mem (pA s₀ 0) i).toNat)

theorem p2rBody_eq : p2rBody =
    .mov .eax (.mem (at_ .esi 0)) :: .alu .add .eax (.imm 4095) :: .mov .edx (.reg .eax) :: .shift .shr .edx 13 ::
      .store (at_ .edi 0) .edx :: .alu .and .eax (.imm 8191) :: (condAdd .eax (.imm 4095) .edx qImm ++
      ([.store (at_ .ebp 0) .eax, .alu .add .esi (.imm 4), .alu .add .edi (.imm 4), .alu .add .ebp (.imm 4),
        .alu .sub .ecx (.imm 1)] : List Instr)) := by
  simp only [p2rBody, List.cons_append, List.nil_append]

theorem p2r_step {s₀ : State} (hp : P2Pre s₀) {k : Nat} (hk : k < 256) {s : State} (h : P2Inv s₀ k s) :
    WP isa (.block p2rBody) s fun s' => P2Inv s₀ (k + 1) s' ∧ eval .ne s' = some (decide (k + 1 < 256)) := by
  have hk' : k < VG.Spec.MlDsa.n := by rw [n_eq]; exact hk
  have hin : InRegions (s.rd ++ s.wr) (addr (arg s₀ 0 + BitVec.ofNat 32 (4 * k)) 0) 4 := by
    rw [addr_cf hp.t_fit hk, h.rd, h.wr, pushed_rd, P0_wr, hp.rd]
    exact ⟨_, by simp, coeff_contains _ hk'⟩
  have hkeep : coeffAt s.mem (pA s₀ 0) k = coeffAt s₀.mem (pA s₀ 0) k :=
    in_keep hp.sp h.frame hp.stk_t (by simp [hp.t_1, hp.t_0]) hk
  have ha := hp.t_red k hk'
  generalize ea : (coeffAt s₀.mem (pA s₀ 0) k).toNat = a at ha
  rw [q_eq] at ha
  rw [p2rBody_eq]
  refine wp_ldm h.esi hin fun s₁ u₁ => wp_addi fun s₂ u₂ => wp_mov fun s₃ u₃ =>
    wp_shr (by decide) fun s₄ u₄ _ => ?_
  have v₁ : (s₁.gpr .eax).toNat = a := by
    rw [u₁.gpr, addr_cf hp.t_fit hk, ← VG.Proof.MlDsa.Round.coeffAt_eq, hkeep, ea]
  have v₂ : (s₂.gpr .eax).toNat = a + 4095 := by
    rw [u₂.gpr, BitVec.toNat_add, v₁]; simp; omega_arith
  have v₄ : (s₄.gpr .edx).toNat = p2r1 a := by
    rw [u₄.gpr, u₃.gpr, BitVec.toNat_ushiftRight, v₂, Nat.shiftRight_eq_div_pow]; rfl
  have edi₄ : s₄.gpr .edi = arg s₀ 1 + BitVec.ofNat 32 (4 * k) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.edi]
  have out₁ : InRegions s₄.wr (addr (arg s₀ 1 + BitVec.ofNat 32 (4 * k)) 0) 4 := by
    rw [addr_cf hp.t1_fit hk, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr, P0_wr, hp.wr]
    exact ⟨_, by simp, coeff_contains _ hk'⟩
  refine wp_stm edi₄ out₁ fun s₅ m₅ => wp_andi fun s₆ u₆ => ?_
  have v₆ : (s₆.gpr .eax).toNat = (a + 4095) % 8192 := by
    rw [u₆.gpr, m₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      show (8191 : BitVec 32) = BitVec.ofNat 32 (2 ^ 13 - 1) from rfl,
      VG.Proof.MlKem.X86.toNat_and_mask _ 13 (by decide), v₂]
  refine condAdd_spec (by decide) (X := 4095) rfl
    (by rw [v₆, show qImm.toNat = 8380417 from rfl, show (4095 : BitVec 32).toNat = 4095 from rfl]; omega_arith)
    fun s₇ o₇ v₇ => ?_
  have ebp₇ : s₇.gpr .ebp = arg s₀ 2 + BitVec.ofNat 32 (4 * k) := by
    rw [o₇.gpr _ (by decide), u₆.other _ (by decide), m₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.ebp]
  have out₀ : InRegions s₇.wr (addr (arg s₀ 2 + BitVec.ofNat 32 (4 * k)) 0) 4 := by
    rw [addr_cf hp.t0_fit hk, o₇.wr, u₆.wr, m₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr, P0_wr, hp.wr]
    exact ⟨_, by simp, coeff_contains _ hk'⟩
  have g₇ : ∀ r, r ≠ .eax → r ≠ .edx → s₇.gpr r = s.gpr r := fun r h1 h2 => by
    rw [o₇.gpr r (by simp [h1, h2]), u₆.other r h1, m₅.gpr, u₄.other r h2, u₃.other r h2, u₂.other r h1,
      u₁.other r h1]
  have m₇ : s₇.mem = (s.mem.writeW (coeffAddr (pA s₀ 1) k) (s₄.gpr .edx)) := by
    rw [o₇.mem, u₆.mem, m₅.mem, addr_cf hp.t1_fit hk, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine wp_stm ebp₇ out₀ fun s₈ m₈ => wp_addi fun s₉ u₉ => wp_addi fun s₁₀ u₁₀ => wp_addi fun s₁₁ u₁₁ =>
    wp_subi fun s₁₂ u₁₂ _ z₁₂ => WP.block_nil_iff.mpr ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_,
      fun i hi => ?_⟩, ?_⟩
  · rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide),
      m₈.gpr, g₇ _ (by decide) (by decide), h.esp]
  · rw [u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, m₈.rd, o₇.rd, u₆.rd, m₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, m₈.wr, o₇.wr, u₆.wr, m₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
  · rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr, m₈.gpr,
      g₇ _ (by decide) (by decide), h.esi]
    exact ptr_next _ _ 4
  · rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr, u₉.other _ (by decide), m₈.gpr,
      g₇ _ (by decide) (by decide), h.edi]
    exact ptr_next _ _ 4
  · rw [u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), m₈.gpr, ebp₇]
    exact ptr_next _ _ 4
  · rw [u₁₂.gpr, u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), m₈.gpr,
      g₇ _ (by decide) (by decide), h.ecx]
    exact cnt_next hk
  · rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, m₈.mem, addr_cf hp.t0_fit hk, m₇]
    exact (h.frame.writeW (by simp) _ (coeff_contains _ hk')).writeW (by simp) _ (coeff_contains _ hk')
  · rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, m₈.mem, addr_cf hp.t0_fit hk, m₇, coeffAt_writeW_disjoint _ hp.t1_t0 (coeff_contains _ hk') (by rw [n_eq]; omega_arith),
      coeffAt_writeW _ _ (by rw [n_eq]; omega_arith) hk']
    by_cases e : k = i
    · subst e; rw [ite_eq_left rfl, ea]; exact eq_ofNat_of_toNat v₄
    · rw [ite_eq_right e]; exact h.out1 i (by omega_arith)
  · rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, m₈.mem, addr_cf hp.t0_fit hk, m₇, coeffAt_writeW _ _ (by rw [n_eq]; omega_arith) hk',
      coeffAt_writeW_disjoint _ hp.t1_t0.symm (coeff_contains _ hk') (by rw [n_eq]; omega_arith)]
    by_cases e : k = i
    · subst e; rw [ite_eq_left rfl, ea]
      refine eq_ofNat_of_toNat (v₇.trans ?_)
      rw [v₆]; rfl
    · rw [ite_eq_right e]; exact h.out0 i (by omega_arith)
  · simp only [eval, z₁₂, Option.map_some]
    rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), m₈.gpr,
      g₇ _ (by decide) (by decide), h.ecx]
    exact cnt_ne hk (by decide)

/-- After `p2rInit`. -/
structure P2S (s₀ s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  mem : s.mem = (P0 s₀).mem
  esi : s.gpr .esi = arg s₀ 0
  edi : s.gpr .edi = arg s₀ 1
  ebp : s.gpr .ebp = arg s₀ 2

theorem p2rInit_piece : Piece P2Pre P2Pub (fun s₀ s => s = P0 s₀) P2S (.block p2rInit) := by
  refine Piece.taint [.esp] (fun s₀ s hp e => ?_) (fun s₀ s₀' s s' _ _ hq e e' r hr => ?_) (by native_taint_decide)
  · subst e
    have hin : aR s₀ 3 ∈ s₀.rd ++ s₀.wr := by simp [hp.wr]
    obtain ⟨a₀, i₀, v₀⟩ := arg_P0 (i := 0) (by omega_arith) hp.sp hp.sp' hin hp.stk_a
    obtain ⟨a₁, i₁, v₁⟩ := arg_P0 (i := 1) (by omega_arith) hp.sp hp.sp' hin hp.stk_a
    obtain ⟨a₂, i₂, v₂⟩ := arg_P0 (i := 2) (by omega_arith) hp.sp hp.sp' hin hp.stk_a
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceAdd, Nat.reduceMul] at a₀ a₁ a₂
    apply WP.of_runBlock
    simp only [reduceCtorEq, ↓reduceIte, p2rInit, at_, runBlock_cons, runStep_some, runBlock_nil,
      exec, readSrc, State.ea, State.load32, State.setReg, Option.map_some, a₀, a₁, a₂, i₀, i₁, i₂, v₀, v₁, v₂,
      Option.some.injEq, exists_eq_left']
    exact ⟨by simp, rfl, rfl, rfl, by simp, by simp, by simp⟩
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [e, e', P0_esp, P0_esp, hq.1]

theorem p2r_piece : Piece P2Pre P2Pub (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (P2Inv s₀ 256) s₀ s')
    power2Round := by
  refine Piece.leaf (fun s₀ => [pR (pA s₀ 1), pR (pA s₀ 2)]) (NoSp.of_all (by decide +kernel))
    (fun _ hp => ⟨hp.sp, by have := hp.sp'; omega_arith⟩) (fun _ hp r hr => ?_) (fun _ _ _ _ hq => hq.1)
    ((Piece.seq p2rInit_piece (Piece.seq (B := (P2Inv · 0)) ?_ ?_)).mono (fun _ _ _ h => h)
      fun _ _ _ h => ⟨⟨h.frame, h.esp, h.rd, h.wr⟩, h⟩)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨by rw [← stk_eq hp.sp]; exact hp.stk_1, hp.ret_1⟩
    · exact ⟨by rw [← stk_eq hp.sp]; exact hp.stk_0, hp.ret_0⟩
  · refine Piece.taint [] (fun s₀ s hp h => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
      (by native_taint_decide)
    refine wp_movi fun s₁ u₁ => WP.block_nil_iff.mpr ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => absurd hi (by omega_arith),
      fun i hi => absurd hi (by omega_arith)⟩
    · rw [u₁.other _ (by decide), h.esp]
    · rw [u₁.rd, h.rd]
    · rw [u₁.wr, h.wr]
    · rw [u₁.other _ (by decide), h.esi]; simp
    · rw [u₁.other _ (by decide), h.edi]; simp
    · rw [u₁.other _ (by decide), h.ebp]; simp
    · rw [u₁.gpr]; rfl
    · rw [u₁.mem, h.mem]; exact Frame.refl _ _
  · exact Piece.countLoop (by decide) (fun k s₀ s => P2Inv s₀ k s) [.esp, .esi, .edi, .ebp, .ecx]
      (fun k hk s₀ s hp h => p2r_step hp hk h)
      (fun k _ s₀ s₀' s s' _ _ hq h h' r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · rw [h.esp, h'.esp, P0_esp, P0_esp, hq.1]
        · rw [h.esi, h'.esi, hq.2.1]
        · rw [h.edi, h'.edi, hq.2.2.1]
        · rw [h.ebp, h'.ebp, hq.2.2.2]
        · rw [h.ecx, h'.ecx]) (by native_taint_decide)

theorem p2r0_lt {a : Nat} : p2r0 a < 2 ^ 32 := by
  have hq : q = 8380417 := rfl
  have := Nat.mod_lt (a + 4095) (show 8192 > 0 by decide)
  unfold p2r0 condAddN; split <;> omega_arith

theorem p2r_post {s₀ s : State} (hp : P2Pre s₀) (hinv : P2Inv s₀ 256 s) :
    NatPolyIs s.mem (pA s₀ 1) ((polyAt s₀.mem (pA s₀ 0)).map fun c => (power2Round c).1.toNat) ∧
      PolyIs s.mem (pA s₀ 2) ((polyAt s₀.mem (pA s₀ 0)).map fun c => ofInt (power2Round c).2) := by
  refine ⟨natPolyIs_of_toNat fun i hi => ?_, polyIs_of_toNat fun i hi => ?_⟩
  · rw [hinv.out1 i hi, map_get _ _ hi, power2Round_eq, polyAt_val hp.t_red hi,
      toNat_ofNat32 (by have := hp.t_red i hi; unfold p2r1; rw [q_eq] at this; omega_arith)]
    rfl
  · rw [hinv.out0 i hi, map_get _ _ hi, power2Round_t0, polyAt_val hp.t_red hi, toNat_ofNat32 p2r0_lt]
    rfl

/-- Memory with the arguments `0x400`, `0` and `0x800` at `0x5004`. -/
def p2rSatMem : Mem := fun a => if a = 0x5005 then 4 else if a = 0x500d then 8 else 0

theorem p2rSat_zero (a : Addr) (ha : a.toNat < 0x5000) : p2rSatMem a = 0 := by
  simp only [p2rSatMem]
  rw [ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega_arith),
    ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega_arith)]

theorem power2Round_verified : Verified X86.target power2Round (power2RoundContract X86.abi 16) := by
  refine Piece.verified ((p2r_piece.pre_mono (fun _ h => P2Pre.of h) fun s s' _ _ h => by
      sig_pub [power2RoundContract, power2RoundSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [power2RoundContract, power2RoundSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    have hp := P2Pre.of h₀
    obtain ⟨q1, q2⟩ := p2r_post hp hinv
    exact ⟨Proof.MlDsa.Arith.natPolyIs_frame hm (fun r hr => by rw [List.mem_singleton.mp hr]; rw [← stk_eq hp.sp]; exact hp.stk_1.symm) q1,
      Proof.MlDsa.Arith.polyIs_frame hm (fun r hr => by rw [List.mem_singleton.mp hr]; rw [← stk_eq hp.sp]; exact hp.stk_0.symm) q2⟩
  · let st := satState p2rSatMem [⟨0x400, 1024⟩] [⟨0, 1024⟩, ⟨0x800, 1024⟩, ⟨0x5004, 12⟩]
    have a0 : arg st 0 = 0x400 := by decide
    have a1 : arg st 1 = 0 := by decide
    have a2 : arg st 2 = 0x800 := by decide
    have e : argAddr st 0 = 0x5004 := by decide
    refine ⟨st, ?_⟩
    sig_pre [power2RoundContract, power2RoundSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [a0, a1, a2, e]
    refine ⟨by decide, by decide, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      by decide, by decide, by decide, reduced_zero p2rSat_zero 0x400 (by decide)⟩
    all_goals exact Region.disjoint_of_sep (by decide)

end VG.Proof.MlDsa.X86.Round

end

end

/-! ### `MlDsa.X86.KeyGen.Verified`, which only this module used -/

section

/-!
# ML-DSA key generation on x86 (32-bit): the contract

`vg_mldsa*_keygen` of the parameter sets of Table 1 meets `keyGenContract`
with 96 bytes of stack (`keyGen_verified`), for any verified implementations
of the primitives it calls (`PrimsOk`): the body, as a leaf (`topLeaf`), from
the contract's precondition and public data (`pre_of`, `pub_of`), to its
postcondition (`post`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top
open VG.Impl.MlDsa.X86.KeyGen
open VG.Spec.MlDsa (Params)

/-- Memory with the arguments `0`, `0x1000`, `0x3000` and `0x10000` at `0x5004`. -/
def satMem : Mem := fun a => if a = 0x5009 then 0x10 else if a = 0x500d then 0x30 else if a = 0x5012 then 1 else 0

/-- A state satisfying the precondition. -/
def keyGenSat (p : Params) : State :=
  satState satMem [⟨0, 32⟩] [⟨0x1000, p.pkLen⟩, ⟨0x3000, p.skLen⟩, ⟨0x10000, scrLen p⟩, ⟨0x5004, 16⟩]

theorem keyGen_verified {P : Prims} (hP : PrimsOk P) (p : Params)
    (hp : p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) :
    Verified X86.target (keyGen P p) (Spec.MlDsa.keyGenContract p X86.abi 96) := by
  have hF := pfacts hp
  refine Piece.verified (((topLeaf (body_nosp hP p) (body_piece hP hF)).pre_mono (fun _ h => pre_of h)
    fun _ _ _ _ h => pub_of h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hd, hm, hax⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [sw_app, hax, hd.eax,
      argKeep (pre_of h₀) hm (k := 1) (l := p.pkLen) (by rcases hp with rfl | rfl | rfl <;> decide),
      argKeep (pre_of h₀) hm (k := 2) (l := p.skLen) (by rcases hp with rfl | rfl | rfl <;> decide)]
    have r := post hF (pre_of h₀) hd
    simp only [xiOf, addr0] at r
    exact r
  · rcases hp with rfl | rfl | rfl
    · exact ⟨keyGenSat Spec.MlDsa.mlDsa44, by sig_sat_check [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, X86.abi,
        X86.argSlots, X86.argVal, X86.argBytes, keyGenSat, satState, satMem]⟩
    · exact ⟨keyGenSat Spec.MlDsa.mlDsa65, by sig_sat_check [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, X86.abi,
        X86.argSlots, X86.argVal, X86.argBytes, keyGenSat, satState, satMem]⟩
    · exact ⟨keyGenSat Spec.MlDsa.mlDsa87, by sig_sat_check [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, X86.abi,
        X86.argSlots, X86.argVal, X86.argBytes, keyGenSat, satState, satMem]⟩

end VG.Proof.MlDsa.X86.KeyGen

end

end


/-!
# ML-DSA key generation on x86 (32-bit), with this library's primitives

The x86 primitives (`Impl.MlDsa.X86.KeyGen.prims`) are verified against their
contracts, use at most 56 bytes of stack and write `esp` only by frames and
calls (`prims_ok`), so `vg_mldsa{44,65,87}_keygen` meet theirs
(`keyGen44_verified`, …).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.KeyGen

open VG VG.X86
open VG.Impl.MlDsa.X86.KeyGen (prims keyGen44 keyGen65 keyGen87)

theorem prims_ok : PrimsOk prims where
  ntt := ⟨⟨15, by decide, Arith.NttFwd.verified⟩, by lit_decide, NoSp.of_all (by lit_decide)⟩
  invNtt := ⟨⟨15, by decide, Arith.NttInvP.verified⟩, by lit_decide, NoSp.of_all (by lit_decide)⟩
  mul := ⟨⟨15, by decide, Arith.mul_verified⟩, by lit_decide, NoSp.of_all (by lit_decide)⟩
  mulAdd := ⟨⟨15, by decide, Arith.mulAdd_verified⟩, by lit_decide, NoSp.of_all (by lit_decide)⟩
  add := ⟨⟨15, by decide, Arith.add_verified⟩, by lit_decide, NoSp.of_all (by lit_decide)⟩
  rejNtt := ⟨⟨55, by decide, Sample.RejNtt.verified⟩, by lit_decide, NoSp.of_all (by lit_decide)⟩
  rejBounded := ⟨⟨55, by decide, Sample.RejBounded.verified⟩, by lit_decide, NoSp.of_all (by lit_decide)⟩
  power2Round := ⟨⟨15, by decide, Round.power2Round_verified⟩, by lit_decide, NoSp.of_all (by lit_decide)⟩
  simpleBitPack := ⟨⟨15, by decide, Pack.SimpleBitPack.verified⟩, by lit_decide,
    NoSp.of_all (by lit_decide)⟩
  bitPack := ⟨⟨15, by decide, Pack.BitPack.verified⟩, by lit_decide, NoSp.of_all (by lit_decide)⟩

/-- `vg_mldsa{44,65,87}_keygen` never write `esp`. -/
theorem keyGen_nosp (p : Spec.MlDsa.Params) : NoSp (Impl.MlDsa.X86.KeyGen.keyGen prims p) := NoSp.leaf (body_nosp prims_ok p)

theorem keyGen44_verified :
    Verified X86.target keyGen44 (Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa44 X86.abi 96) :=
  keyGen_verified prims_ok _ (.inl rfl)

theorem keyGen65_verified :
    Verified X86.target keyGen65 (Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa65 X86.abi 96) :=
  keyGen_verified prims_ok _ (.inr (.inl rfl))

theorem keyGen87_verified :
    Verified X86.target keyGen87 (Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa87 X86.abi 96) :=
  keyGen_verified prims_ok _ (.inr (.inr rfl))

end VG.Proof.MlDsa.X86.KeyGen
