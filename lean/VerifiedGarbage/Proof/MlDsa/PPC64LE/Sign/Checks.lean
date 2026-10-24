module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sign.Calls
import VerifiedGarbage.Proof.MlDsa.Sign.Iter
import VerifiedGarbage.Proof.MlDsa.Sign.Mem
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.MlDsa.Verify.Mem
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sign.Calls
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint

/-!
# ML-DSA signing on PPC64LE: the checks of an iteration

As on 32-bit ARM (`Proof/MlDsa/Arm/Sign/PhaseK.lean`), once `SampleInBall`
succeeded (`KB`): `ĉ = NTT(c)`, and each check of the iteration, their
results ANDed into `r24`: the norm of each `z[r]` (`IZ`), of each `r₀[i]`
(`IQ`) and of each `ct₀[i]`, with each hint `h[i]` and the number of its 1s
summed in `r26` (`IH`), and that sum against `ω`; so `r24` is 1 exactly when
the iteration passes (`KO`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Sign

open VG VG.PPC64LE VG.Proof.MlKem.PPC64LE
open VG.Proof.MlDsa.PPC64LE.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of polyIs_keepW bytes_keepW
  Regs2 zx copyS)
open VG.Impl.MlDsa.PPC64LE.Sign
open VG.Impl.MlDsa.PPC64LE.KeyGen (callAt and24 seqR)
open VG.Impl.MlKem.PPC64LE (copy)
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Sign (chF zF w'F r0F ct0F w''F passF)
open VG.Spec.Sha3 (bytesAt)

section
variable (p : Params)

/-- `c = SampleInBall(c̃)` of the iteration with counter `κ`, within `maxBounds`. -/
abbrev cV (σ : State) (κ : Nat) : IPoly :=
  (sampleInBall p.τ maxBounds.ball (CTv p σ κ)).getD (Vector.replicate n 0)

/-- `z[r]`, `r₀[i]`, `ct₀[i]`, `w[i] - cs₂[i]`, `w[i] - cs₂[i] + ct₀[i]` and `h[i]`. -/
abbrev Zv (σ : State) (κ r : Nat) : Poly := zF p (S1v p σ) (rppOf p σ) κ (cV p σ κ) r
abbrev R0v (σ : State) (κ i : Nat) : Poly := r0F p (Am p σ) (S2v p σ) (rppOf p σ) κ (cV p σ κ) i
abbrev CT0v (σ : State) (κ i : Nat) : Poly := ct0F (T0v p σ) (cV p σ κ) i
abbrev W'v (σ : State) (κ i : Nat) : Poly := w'F p (Am p σ) (S2v p σ) (rppOf p σ) κ (cV p σ κ) i
abbrev W''v (σ : State) (κ i : Nat) : Poly := w''F p (Am p σ) (S2v p σ) (T0v p σ) (rppOf p σ) κ (cV p σ κ) i
abbrev Hv (σ : State) (κ i : Nat) : Vector Bool n :=
  Proof.MlDsa.Sign.hF p (Am p σ) (S2v p σ) (T0v p σ) (rppOf p σ) κ (cV p σ κ) i

/-- Whether the iteration with counter `κ` passes, once `SampleInBall` succeeded. -/
abbrev PassV (σ : State) (κ : Nat) : Prop :=
  passF p (Am p σ) (S1v p σ) (S2v p σ) (T0v p σ) (rppOf p σ) κ (cV p σ κ)

/-- `z` passed. -/
abbrev ZOk (σ : State) (κ : Nat) : Prop := ∀ j < p.ℓ, normRq [Zv p σ κ j] < p.γ₁ - p.β

/-- `r₀` passed. -/
abbrev R0Ok (σ : State) (κ : Nat) : Prop := ∀ j < p.k, normRq [R0v p σ κ j] < p.γ₂ - p.β

end

/-- A family of polynomials in slots `b + j` for `a ≤ j < e`, apart from what a
part writes, is kept. -/
theorem famR_keep {L : Lay} {Wb : List Nat} (hL : OkW L Wb) (h0 : 0 ∈ Wb) {W : List (Nat × Nat × Nat)} {m m' : Mem}
    (hf : Frame (L.RL W) m m') {b a e : Nat} (h : sepAll L.sizes (0, oP (b + a), 1024 * (e - a)) W = true)
    {F : Nat → Poly} (hp : ∀ j, a ≤ j → j < e → PolyIs m (L.A 0 (oP (b + j))) (F j)) :
    ∀ j, a ≤ j → j < e → PolyIs m' (L.A 0 (oP (b + j))) (F j) :=
  fun j h1 h2 => polyIs_keepW hL hf (sepAll_sub h (by unfold oP; omega) (by unfold oP; omega)) h0 rfl (hp j h1 h2)

/-! ## The checks' state -/

/-- The checks of iteration `t`, once `SampleInBall` succeeded: `ĉ = NTT(c)`. -/
structure KB (p : Params) (STK : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  l : IL p STK σ t s
  ct : bytesAt s.mem ((slay2 p STK σ).A 0 oCT) (cLen p) = CTv p σ (p.ℓ * t)
  c : PolyIs s.mem (SL p STK σ 0) (chF (cV p σ (p.ℓ * t)))
  some : (sampleInBall p.τ maxBounds.ball (CTv p σ (p.ℓ * t))).isSome

/-- A part that writes `W` keeps `KB`. -/
def kbChk (p : Params) (STK : Nat) (W : List (Nat × Nat × Nat)) : Bool :=
  ikChk p STK W && sepAll [scrLen p, STK, p.skLen, 64, p.sigLen] (0, oCT, cLen p) W &&
    sepAll [scrLen p, STK, p.skLen, 64, p.sigLen] (0, oP 0, 1024) W

theorem KB.keep {p : Params} (hF : SFacts p) {STK : Nat} {σ : State} {t : Nat} {s s' : State} (h : KB p STK σ t s)
    {W : List (Nat × Nat × Nat)} (hk : Kept ((slay2 p STK σ).RL W) s s') (hc : kbChk p STK W = true) :
    KB p STK σ t s' := by
  simp only [kbChk, Bool.and_eq_true] at hc
  obtain ⟨⟨c1, c2⟩, c3⟩ := hc
  have hL := h.l.k.sc.site.ok
  have hct : cLen p ≤ 2 ^ 64 := by rcases hF.ct with e | e | e <;> omega
  exact ⟨⟨h.l.k.keep hk c1, (hk.cs .r27 (by decide)).trans h.l.r27, (hk.cs .r25 (by decide)).trans h.l.r25,
    h.l.t_lt, h.l.rej⟩, by rw [bytes_keepW hL hk.frame c2 (by decide) hct]; exact h.ct,
    polyIs_keepW hL hk.frame c3 (by decide) rfl h.c, h.some⟩

theorem IK.regs2 {p : Params} {STK : Nat} {σ s s' : State} (h : IK p STK σ s) (r : Regs2 s s') : IK p STK σ s' :=
  ⟨h.sc.regs2 r, h.ok, by rw [r.mem]; exact h.A, by rw [r.mem]; exact h.rpp, by rw [r.mem]; exact h.s1,
    by rw [r.mem]; exact h.s2, by rw [r.mem]; exact h.t0⟩

theorem IL.regs2 {p : Params} {STK : Nat} {σ : State} {t : Nat} {s s' : State} (h : IL p STK σ t s) (r : Regs2 s s') :
    IL p STK σ t s' :=
  ⟨h.k.regs2 r, by rw [r.gpr .r27 (by decide) (by decide)]; exact h.r27,
    by rw [r.gpr .r25 (by decide) (by decide)]; exact h.r25, h.t_lt, h.rej⟩

theorem KB.regs2 {p : Params} {STK : Nat} {σ : State} {t : Nat} {s s' : State} (h : KB p STK σ t s) (r : Regs2 s s') :
    KB p STK σ t s' :=
  ⟨h.l.regs2 r, by rw [r.mem]; exact h.ct, by rw [r.mem]; exact h.c, h.some⟩

theorem SC2.of_eq {p : Params} {STK : Nat} {σ s s' : State} (h : SC2 p STK σ s)
    (hg : ∀ r, r ≠ .r3 → r ≠ .r26 → s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) : SC2 p STK σ s' := by
  have hs := h.site
  refine ⟨⟨hs.ok, hs.len, hs.w0, hs.w1, hs.sz0, hs.sz1, by rw [hsp]; exact hs.p1, hs.s48, by rw [hsp]; exact hs.spk,
    by rw [hg .r31 (by decide) (by decide)]; exact hs.r31, by rw [hg .r30 (by decide) (by decide)]; exact hs.r30,
    by rw [hg .r29 (by decide) (by decide)]; exact hs.r29, by rw [hg .r28 (by decide) (by decide)]; exact hs.r28,
    by rw [hwr]; exact hs.cw, by rw [hwr, hrd]; exact hs.cr⟩, hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp,
    fun r hr hs' => ?_, by rw [hm]; exact h.sav, by rw [hm]; exact h.sk, by rw [hm]; exact h.mu⟩
  have : r ≠ .r3 ∧ r ≠ .r26 := ⟨fun e => by subst e; simp [preserved] at hr, fun e => by subst e; simp [savedTop] at hs'⟩
  rw [hg r this.1 this.2]; exact h.pres r hr hs'

theorem KB.of_eq {p : Params} {STK : Nat} {σ : State} {t : Nat} {s s' : State} (h : KB p STK σ t s)
    (hg : ∀ r, r ≠ .r3 → r ≠ .r26 → s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) : KB p STK σ t s' :=
  ⟨⟨⟨h.l.k.sc.of_eq hg hm hrd hwr hsp, h.l.k.ok, by rw [hm]; exact h.l.k.A, by rw [hm]; exact h.l.k.rpp,
    by rw [hm]; exact h.l.k.s1, by rw [hm]; exact h.l.k.s2, by rw [hm]; exact h.l.k.t0⟩,
    by rw [hg .r27 (by decide) (by decide)]; exact h.l.r27, by rw [hg .r25 (by decide) (by decide)]; exact h.l.r25,
    h.l.t_lt, h.l.rej⟩, by rw [hm]; exact h.ct, by rw [hm]; exact h.c, h.some⟩

/-! ## `z` -/

/-- The checks of `z[j]` for `j < nz`; `y[j]` for `ys ≤ j < ℓ`, `r26 = 0`. -/
structure IZ (p : Params) (STK : Nat) (σ : State) (t nz ys : Nat) (s : State) : Prop where
  b : KB p STK σ t s
  z : ∀ r < nz, PolyIs s.mem (SL p STK σ (yBase p + r)) (Zv p σ (p.ℓ * t) r)
  y : ∀ r, ys ≤ r → r < p.ℓ → PolyIs s.mem (SL p STK σ (yBase p + r)) (Yv p σ (p.ℓ * t) r)
  w : ∀ i < p.k, PolyIs s.mem (SL p STK σ (wBase p + i)) (Wv p σ (p.ℓ * t) i)
  r26 : s.gpr .r26 = 0
  r24 : s.gpr .r24 = bit (∀ j < nz, normRq [Zv p σ (p.ℓ * t) j] < p.γ₁ - p.β)

/-- A part that writes `W` keeps `IZ`. -/
def izChk (p : Params) (STK : Nat) (W : List (Nat × Nat × Nat)) (nz ys : Nat) : Bool :=
  kbChk p STK W && sepAll [scrLen p, STK, p.skLen, 64, p.sigLen] (0, oP (yBase p + 0), 1024 * (nz - 0)) W &&
    sepAll [scrLen p, STK, p.skLen, 64, p.sigLen] (0, oP (yBase p + ys), 1024 * (p.ℓ - ys)) W &&
    sepAll [scrLen p, STK, p.skLen, 64, p.sigLen] (0, oP (wBase p + 0), 1024 * (p.k - 0)) W

theorem IZ.keep {p : Params} (hF : SFacts p) {STK : Nat} {σ : State} {t nz ys : Nat} {s s' : State}
    (h : IZ p STK σ t nz ys s) {W : List (Nat × Nat × Nat)} (hk : Kept ((slay2 p STK σ).RL W) s s')
    (hc : izChk p STK W nz ys = true) : IZ p STK σ t nz ys s' := by
  simp only [izChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨c1, c2⟩, c3⟩, c4⟩ := hc
  have hL := h.b.l.k.sc.site.ok
  have h0 : 0 ∈ sWb2 := by decide
  exact ⟨h.b.keep hF hk c1, fun r hr => famR_keep hL h0 hk.frame c2 (fun j _ hj => h.z j hj) r (Nat.zero_le _) hr,
    famR_keep hL h0 hk.frame c3 h.y, fun i hi => famR_keep hL h0 hk.frame c4 (fun j _ hj => h.w j hj) i
      (Nat.zero_le _) hi, (hk.cs .r26 (by decide)).trans h.r26, (hk.cs .r24 (by decide)).trans h.r24⟩

theorem IZ.weak {p : Params} {STK : Nat} {σ : State} {t r : Nat} {s : State} (h : IZ p STK σ t r r s)
    (hr : r < p.ℓ) : IZ p STK σ t r (r + 1) s ∧ PolyIs s.mem (SL p STK σ (yBase p + r)) (Yv p σ (p.ℓ * t) r) :=
  ⟨⟨h.b, h.z, fun j hj hj' => h.y j (by omega) hj', h.w, h.r26, h.r24⟩, h.y r (Nat.le_refl _) hr⟩

/-! ## `r₀` -/

/-- The checks of `r₀[j]` for `j < nr` (`w[j]` is `w[j] - cs₂[j]`); `w[j]` for `ws ≤ j < k`; `z` checked, `r26 = 0`. -/
structure IQ (p : Params) (STK : Nat) (σ : State) (t nr ws : Nat) (s : State) : Prop where
  b : KB p STK σ t s
  z : ∀ r < p.ℓ, PolyIs s.mem (SL p STK σ (yBase p + r)) (Zv p σ (p.ℓ * t) r)
  w' : ∀ i < nr, PolyIs s.mem (SL p STK σ (wBase p + i)) (W'v p σ (p.ℓ * t) i)
  w : ∀ i, ws ≤ i → i < p.k → PolyIs s.mem (SL p STK σ (wBase p + i)) (Wv p σ (p.ℓ * t) i)
  r26 : s.gpr .r26 = 0
  r24 : s.gpr .r24 = bit (ZOk p σ (p.ℓ * t) ∧ ∀ j < nr, normRq [R0v p σ (p.ℓ * t) j] < p.γ₂ - p.β)

/-- A part that writes `W` keeps `IQ`. -/
def iqChk (p : Params) (STK : Nat) (W : List (Nat × Nat × Nat)) (nr ws : Nat) : Bool :=
  kbChk p STK W && sepAll [scrLen p, STK, p.skLen, 64, p.sigLen] (0, oP (yBase p + 0), 1024 * (p.ℓ - 0)) W &&
    sepAll [scrLen p, STK, p.skLen, 64, p.sigLen] (0, oP (wBase p + 0), 1024 * (nr - 0)) W &&
    sepAll [scrLen p, STK, p.skLen, 64, p.sigLen] (0, oP (wBase p + ws), 1024 * (p.k - ws)) W

theorem IQ.keep {p : Params} (hF : SFacts p) {STK : Nat} {σ : State} {t nr ws : Nat} {s s' : State}
    (h : IQ p STK σ t nr ws s) {W : List (Nat × Nat × Nat)} (hk : Kept ((slay2 p STK σ).RL W) s s')
    (hc : iqChk p STK W nr ws = true) : IQ p STK σ t nr ws s' := by
  simp only [iqChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨c1, c2⟩, c3⟩, c4⟩ := hc
  have hL := h.b.l.k.sc.site.ok
  have h0 : 0 ∈ sWb2 := by decide
  exact ⟨h.b.keep hF hk c1, fun r hr => famR_keep hL h0 hk.frame c2 (fun j _ hj => h.z j hj) r (Nat.zero_le _) hr,
    fun i hi => famR_keep hL h0 hk.frame c3 (fun j _ hj => h.w' j hj) i (Nat.zero_le _) hi,
    famR_keep hL h0 hk.frame c4 h.w, (hk.cs .r26 (by decide)).trans h.r26, (hk.cs .r24 (by decide)).trans h.r24⟩

theorem IQ.weak {p : Params} {STK : Nat} {σ : State} {t i : Nat} {s : State} (h : IQ p STK σ t i i s)
    (hi : i < p.k) : IQ p STK σ t i (i + 1) s ∧ PolyIs s.mem (SL p STK σ (wBase p + i)) (Wv p σ (p.ℓ * t) i) :=
  ⟨⟨h.b, h.z, h.w', fun j hj hj' => h.w j (by omega) hj', h.r26, h.r24⟩, h.w i (Nat.le_refl _) hi⟩

theorem IZ.iq {p : Params} {STK : Nat} {σ : State} {t : Nat} {s : State} (h : IZ p STK σ t p.ℓ p.ℓ s) :
    IQ p STK σ t 0 0 s :=
  ⟨h.b, h.z, fun _ h => absurd h (Nat.not_lt_zero _), fun i _ hi => h.w i hi, h.r26,
    by rw [h.r24]; exact bit_congr ⟨fun h => ⟨h, fun _ h => absurd h (Nat.not_lt_zero _)⟩, fun h => h.1⟩⟩

/-! ## Hints and their 1s -/

theorem zq_sub_sub (a : Zq) : a - a - a = -a := by
  apply Fin.ext
  have ha := a.isLt
  simp only [Fin.sub_def, Fin.neg_def, q] at *
  omega

theorem sub_sub_self (a : Poly) : sub (sub a a) a = neg a := by
  apply Vector.ext
  intro j hj
  simp only [sub, neg, Vector.getElem_zipWith, Vector.getElem_map, zq_sub_sub]

theorem hintOnes_le (h : Vector Bool n) : hintOnes [h] ≤ 256 := by
  rw [Proof.MlDsa.Sign.hintOnes_single]
  exact Nat.le_trans (List.length_filter_le _ _) (by simp)

/-- The sum of the 1s of the first `i` hints. -/
abbrev onesSum (f : Nat → Vector Bool n) (i : Nat) : Nat := ((List.range i).map fun j => hintOnes [f j]).sum

theorem onesSum_succ (f : Nat → Vector Bool n) (i : Nat) : onesSum f (i + 1) = onesSum f i + hintOnes [f i] := by
  simp only [onesSum, List.range_succ, List.map_append, List.map_cons, List.map_nil, List.sum_append,
    List.sum_cons, List.sum_nil, Nat.add_zero]

theorem onesSum_le (f : Nat → Vector Bool n) : ∀ i, onesSum f i ≤ 256 * i
  | 0 => by simp [onesSum]
  | i + 1 => by
    rw [onesSum_succ]
    have := onesSum_le f i; have := hintOnes_le (f i)
    omega

/-- A hint kept by a part that writes apart from it. -/
theorem hintIs_keepW {L : Lay} {Wb : List Nat} (hL : OkW L Wb) {W : List (Nat × Nat × Nat)} {m m' : Mem}
    (hf : Frame (L.RL W) m m') {i o : Nat} (h : sepAll L.sizes (i, o, 1024 * 1) W = true) (hw : i ∈ Wb)
    {hh : List (Vector Bool Spec.MlDsa.n)} (hi : HintIs m (L.A i o) 1 hh) : HintIs m' (L.A i o) 1 hh :=
  Proof.MlDsa.Verify.hintIs_frame hf (by decide) (KeyGen.keepD hL h hw) hi

/-- The checks of `ct₀[j]` for `j < nc`; for `j < nh`, `w[j]` is `w[j] - cs₂[j] + ct₀[j]` and `h[j]` is the
hint, the number of their 1s in `r26`; `w[j]` is `w[j] - cs₂[j]` for `ws ≤ j < k`. -/
structure IH (p : Params) (STK : Nat) (σ : State) (t nc nh ws : Nat) (s : State) : Prop where
  b : KB p STK σ t s
  z : ∀ r < p.ℓ, PolyIs s.mem (SL p STK σ (yBase p + r)) (Zv p σ (p.ℓ * t) r)
  w'' : ∀ i < nh, PolyIs s.mem (SL p STK σ (wBase p + i)) (W''v p σ (p.ℓ * t) i)
  w' : ∀ i, ws ≤ i → i < p.k → PolyIs s.mem (SL p STK σ (wBase p + i)) (W'v p σ (p.ℓ * t) i)
  h : ∀ i < nh, HintIs s.mem (SL p STK σ (5 + i)) 1 [Hv p σ (p.ℓ * t) i]
  r26 : s.gpr .r26 = BitVec.ofNat 64 (onesSum (Hv p σ (p.ℓ * t)) nh)
  r24 : s.gpr .r24 = bit ((ZOk p σ (p.ℓ * t) ∧ R0Ok p σ (p.ℓ * t)) ∧
    ∀ j < nc, normRq [CT0v p σ (p.ℓ * t) j] < p.γ₂)

/-- A part that writes `W` keeps `IH`. -/
def ihChk (p : Params) (STK : Nat) (W : List (Nat × Nat × Nat)) (nh ws : Nat) : Bool :=
  kbChk p STK W && sepAll [scrLen p, STK, p.skLen, 64, p.sigLen] (0, oP (yBase p + 0), 1024 * (p.ℓ - 0)) W &&
    sepAll [scrLen p, STK, p.skLen, 64, p.sigLen] (0, oP (wBase p + 0), 1024 * (nh - 0)) W &&
    sepAll [scrLen p, STK, p.skLen, 64, p.sigLen] (0, oP (wBase p + ws), 1024 * (p.k - ws)) W &&
    sepAll [scrLen p, STK, p.skLen, 64, p.sigLen] (0, oP (5 + 0), 1024 * (nh - 0)) W

theorem IH.keep {p : Params} (hF : SFacts p) {STK : Nat} {σ : State} {t nc nh ws : Nat} {s s' : State}
    (h : IH p STK σ t nc nh ws s) {W : List (Nat × Nat × Nat)} (hk : Kept ((slay2 p STK σ).RL W) s s')
    (hc : ihChk p STK W nh ws = true) : IH p STK σ t nc nh ws s' := by
  simp only [ihChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩ := hc
  have hL := h.b.l.k.sc.site.ok
  have h0 : 0 ∈ sWb2 := by decide
  exact ⟨h.b.keep hF hk c1, fun r hr => famR_keep hL h0 hk.frame c2 (fun j _ hj => h.z j hj) r (Nat.zero_le _) hr,
    fun i hi => famR_keep hL h0 hk.frame c3 (fun j _ hj => h.w'' j hj) i (Nat.zero_le _) hi,
    famR_keep hL h0 hk.frame c4 h.w',
    fun i hi => hintIs_keepW hL hk.frame (sepAll_sub c5 (by unfold oP; omega) (by unfold oP; omega)) h0 (h.h i hi),
    (hk.cs .r26 (by decide)).trans h.r26, (hk.cs .r24 (by decide)).trans h.r24⟩

theorem IH.weak {p : Params} {STK : Nat} {σ : State} {t i : Nat} {s : State} (h : IH p STK σ t i i i s)
    (hi : i < p.k) :
    IH p STK σ t i i (i + 1) s ∧ PolyIs s.mem (SL p STK σ (wBase p + i)) (W'v p σ (p.ℓ * t) i) :=
  ⟨⟨h.b, h.z, h.w'', fun j hj hj' => h.w' j (by omega) hj', h.h, h.r26, h.r24⟩, h.w' i (Nat.le_refl _) hi⟩

theorem IQ.ih {p : Params} {STK : Nat} {σ : State} {t : Nat} {s : State} (h : IQ p STK σ t p.k p.k s) :
    IH p STK σ t 0 0 0 s :=
  ⟨h.b, h.z, fun _ h => absurd h (Nat.not_lt_zero _), fun i _ hi => h.w' i hi, fun _ h => absurd h (Nat.not_lt_zero _),
    by rw [h.r26]; rfl,
    by rw [h.r24]; exact bit_congr ⟨fun h => ⟨h, fun _ h => absurd h (Nat.not_lt_zero _)⟩, fun h => h.1⟩⟩

/-- The block after `vg_mldsa_make_hint`: its result added to `r26`. -/
theorem onesAdd_ok (s : State) :
    WP isa (.block [.lsr .w .r3 .r3 0, .add .r26 .r26 .r3]) s fun s' =>
      s'.gpr .r26 = s.gpr .r26 + zx (s.gpr .r3) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      ∀ r, r ≠ .r3 → r ≠ .r26 → s'.gpr r = s.gpr r := by
  crun []
  refine ⟨by simp, fun r h3 h26 => ?_⟩
  simp [h3, h26]

/-- `ssep`, with the slots and checks of the signing loop. -/
syntax "csep " term:max : tactic
macro_rules
  | `(tactic| csep $hF) => `(tactic| ssep $hF [izChk, iqChk, ihChk, kbChk, ikChk, sc2Chk, yBase, yhBase, wBase, s1Base, s2Base,
      t0Base, aBase, nSec])

/-- `slt`, with the slots of the signing loop. -/
syntax "clt " term:max : tactic
macro_rules
  | `(tactic| clt $hF) => `(tactic| (try dsimp only [yBase, yhBase, wBase, s1Base, s2Base, t0Base, aBase]); slt $hF)

section
variable {P : Prims} {S : Nat} (hP : SPrimsOk P S) {p : Params} (hF : SFacts p) {STK : Nat} (hS : S ≤ STK)
include hP hF hS

/-- `y[r]` while `z[r]` is computed. -/
abbrev ZA (p : Params) (STK t r : Nat) (σ s : State) : Prop :=
  IZ p STK σ t r (r + 1) s ∧ PolyIs s.mem (SL p STK σ (yBase p + r)) (Yv p σ (p.ℓ * t) r)

omit hP hS in
theorem za_keep {t r : Nat} (hr : r < p.ℓ) {σ s s' : State} (h : ZA p STK t r σ s) {x : Nat} (hx : 1 ≤ x ∧ x < 5)
    (hk : Kept ((slay2 p STK σ).RL [tri (pS x) 1024, tri (sc oPS) 1024, (1, 0, STK)]) s s') :
    ZA p STK t r σ s' := by
  have hk' := hF.k; have hl := hF.l; have hkl := hF.kl
  exact ⟨h.1.keep hF hk (by csep hF),
    polyIs_keepW h.1.b.l.k.sc.site.ok hk.frame (by csep hF) (by decide) rfl h.2⟩

theorem zR_piece {t r : Nat} (hr : r < p.ℓ) :
    SPiece p STK (fun σ s => IZ p STK σ t r r s) (fun σ s => IZ p STK σ t (r + 1) (r + 1) s) (zR P p r) := by
  have hk' := hF.k; have hl := hF.l; have hkl := hF.kl
  have hza : ∀ σ s, ZA p STK t r σ s → SC2 p STK σ s := fun _ _ h => h.1.b.l.k.sc
  -- `T1 ← NTT⁻¹(ĉ ŝ₁[r])`
  have p1 := mulP_piece hP hS hza (x := 1) (a := 0) (b := s1Base p + r)
    (fun σ => ⟨⟨sptr_ok rfl (by decide), by csep hF⟩, ⟨sptr_ok rfl (by decide), by csep hF⟩,
      ⟨sptr_ok rfl (by clt hF), by csep hF⟩, show ix Reg.r31 ∈ sWb2 by decide, by csep hF, by csep hF⟩)
    (F := fun σ => chF (cV p σ (p.ℓ * t))) (G := fun σ => S1v p σ r)
    (fun _ _ h => h.1.b.c) (fun _ _ h => h.1.b.l.k.s1 r hr)
    (fun σ s s' h k => za_keep hF hr h (x := 1) (by decide) (k.monoL (by simp)))
  have p2 := ipP_piece hS hza (t := nttInv) hP.invNtt (x := 1) (name := "vg_mldsa_inv_ntt")
    (fun σ => ⟨⟨sptr_ok rfl (by decide), by csep hF⟩, ⟨sptr_ok rfl (by decide), by csep hF⟩,
      show ix Reg.r31 ∈ sWb2 by decide, show ix Reg.r31 ∈ sWb2 by decide, by csep hF⟩)
    (F := fun σ => multiplyNTT (chF (cV p σ (p.ℓ * t))) (S1v p σ r))
    (fun σ s s' h k => za_keep hF hr h (x := 1) (by decide) (k.monoL (by simp)))
  -- `y[r] ← y[r] + T1`, which is `z[r]`
  have hzb : ∀ σ s, (IZ p STK σ t r (r + 1) s ∧
      PolyIs s.mem (SL p STK σ 1) (nttInv (multiplyNTT (chF (cV p σ (p.ℓ * t))) (S1v p σ r)))) → SC2 p STK σ s :=
    fun _ _ h => h.1.b.l.k.sc
  have p3 := addP_piece hP hS hzb (f := yBase p + r) (g := 1)
    (fun σ => ⟨⟨sptr_ok rfl (by clt hF), by csep hF⟩, ⟨sptr_ok rfl (by decide), by csep hF⟩,
      show ix Reg.r31 ∈ sWb2 by decide, by csep hF⟩)
    (F := fun σ => Yv p σ (p.ℓ * t) r) (G := fun σ => nttInv (multiplyNTT (chF (cV p σ (p.ℓ * t))) (S1v p σ r)))
    (fun _ _ h => h.2)
    (fun σ s s' h k => ⟨h.1.keep hF k (by csep hF),
      polyIs_keepW h.1.b.l.k.sc.site.ok k.frame (by csep hF) (by decide) rfl h.2⟩)
  -- its norm, into `r24`
  have hzc : ∀ σ s, IZ p STK σ t r (r + 1) s → SC2 p STK σ s := fun _ _ h => h.b.l.k.sc
  have p4 := normP_piece hP hS hzc (f := yBase p + r) (B := p.γ₁ - p.β) (fun σ => ⟨sptr_ok rfl (by clt hF), by csep hF⟩)
    (fun σ => by csep hF) (by rcases hF.g1 with e | e <;> rw [e] <;> omega)
    (F := fun σ => Zv p σ (p.ℓ * t) r)
    (fun σ s s' h k => h.keep hF k (by csep hF))
  have p5 := and24_piece (p := p) (STK := STK) (J := fun σ s => (IZ p STK σ t r (r + 1) s ∧
      PolyIs s.mem (SL p STK σ (yBase p + r)) (Zv p σ (p.ℓ * t) r)) ∧
      (s.gpr .r3).setWidth 32 = (if normRq [Zv p σ (p.ℓ * t) r] < p.γ₁ - p.β then 1 else 0))
    (J' := fun σ s => IZ p STK σ t (r + 1) (r + 1) s) (fun _ _ h => h.1.1.b.l.k.sc)
    fun σ s s' ⟨⟨h, hz⟩, h3⟩ r2 e24 => ⟨h.b.regs2 r2, fun j hj => by
        rw [r2.mem]
        rcases (by omega : j < r ∨ j = r) with h' | rfl
        exacts [h.z j h', hz],
      fun j hj hj' => by rw [r2.mem]; exact h.y j hj hj', fun i hi => by rw [r2.mem]; exact h.w i hi,
      by rw [r2.gpr .r26 (by decide) (by decide)]; exact h.r26,
      by rw [e24, h.r24, bit_and h3]; exact bit_congr forall_lt_succ⟩
  unfold zR normAt
  refine Piece.mono (p1.seq (p2.seq ((Piece.mono p3 (fun σ s _ h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩)
    fun σ s _ h => ⟨h.1.1, h.2⟩).seq (p4.seq p5)))) (fun σ s _ h => h.weak hr) fun _ _ _ h => h
end

section
variable {P : Prims} {S : Nat} (hP : SPrimsOk P S) {p : Params} (hF : SFacts p) {STK : Nat} (hS : S ≤ STK)
include hP hF hS

/-- `w[i]` while `r₀[i]` is computed. -/
abbrev RA (p : Params) (STK t i : Nat) (σ s : State) : Prop :=
  IQ p STK σ t i (i + 1) s ∧ PolyIs s.mem (SL p STK σ (wBase p + i)) (Wv p σ (p.ℓ * t) i)

omit hP hS in
theorem ra_keep {t i : Nat} (hi : i < p.k) {σ s s' : State} (h : RA p STK t i σ s) {x : Nat} (hx : 1 ≤ x ∧ x < 5)
    (hk : Kept ((slay2 p STK σ).RL [tri (pS x) 1024, tri (sc oPS) 1024, (1, 0, STK)]) s s') :
    RA p STK t i σ s' := by
  have hk' := hF.k; have hl := hF.l; have hkl := hF.kl
  exact ⟨h.1.keep hF hk (by csep hF), polyIs_keepW h.1.b.l.k.sc.site.ok hk.frame (by csep hF) (by decide) rfl h.2⟩

theorem r0R_piece {t i : Nat} (hi : i < p.k) :
    SPiece p STK (fun σ s => IQ p STK σ t i i s) (fun σ s => IQ p STK σ t (i + 1) (i + 1) s) (r0R P p i) := by
  have hk' := hF.k; have hl := hF.l; have hkl := hF.kl
  have hra : ∀ σ s, RA p STK t i σ s → SC2 p STK σ s := fun _ _ h => h.1.b.l.k.sc
  -- `T1 ← NTT⁻¹(ĉ ŝ₂[i])`
  have p1 := mulP_piece hP hS hra (x := 1) (a := 0) (b := s2Base p + i)
    (fun σ => ⟨⟨sptr_ok rfl (by decide), by csep hF⟩, ⟨sptr_ok rfl (by decide), by csep hF⟩,
      ⟨sptr_ok rfl (by clt hF), by csep hF⟩, show ix Reg.r31 ∈ sWb2 by decide, by csep hF, by csep hF⟩)
    (F := fun σ => chF (cV p σ (p.ℓ * t))) (G := fun σ => S2v p σ i)
    (fun _ _ h => h.1.b.c) (fun _ _ h => h.1.b.l.k.s2 i hi)
    (fun σ s s' h k => ra_keep hF hi h (x := 1) (by decide) (k.monoL (by simp)))
  have p2 := ipP_piece hS hra (t := nttInv) hP.invNtt (x := 1) (name := "vg_mldsa_inv_ntt")
    (fun σ => ⟨⟨sptr_ok rfl (by decide), by csep hF⟩, ⟨sptr_ok rfl (by decide), by csep hF⟩,
      show ix Reg.r31 ∈ sWb2 by decide, show ix Reg.r31 ∈ sWb2 by decide, by csep hF⟩)
    (F := fun σ => multiplyNTT (chF (cV p σ (p.ℓ * t))) (S2v p σ i))
    (fun σ s s' h k => ra_keep hF hi h (x := 1) (by decide) (k.monoL (by simp)))
  -- `w[i] ← w[i] - T1`
  have hrb : ∀ σ s, (IQ p STK σ t i (i + 1) s ∧
      PolyIs s.mem (SL p STK σ 1) (nttInv (multiplyNTT (chF (cV p σ (p.ℓ * t))) (S2v p σ i)))) → SC2 p STK σ s :=
    fun _ _ h => h.1.b.l.k.sc
  have p3 := subP_piece hP hS hrb (f := wBase p + i) (g := 1)
    (fun σ => ⟨⟨sptr_ok rfl (by clt hF), by csep hF⟩, ⟨sptr_ok rfl (by decide), by csep hF⟩,
      show ix Reg.r31 ∈ sWb2 by decide, by csep hF⟩)
    (F := fun σ => Wv p σ (p.ℓ * t) i) (G := fun σ => nttInv (multiplyNTT (chF (cV p σ (p.ℓ * t))) (S2v p σ i)))
    (fun _ _ h => h.2)
    (fun σ s s' h k => ⟨h.1.keep hF k (by csep hF),
      polyIs_keepW h.1.b.l.k.sc.site.ok k.frame (by csep hF) (by decide) rfl h.2⟩)
  -- `T2 ← LowBits(w[i])`
  have hrc : ∀ σ s, (IQ p STK σ t i (i + 1) s ∧ PolyIs s.mem (SL p STK σ (wBase p + i)) (W'v p σ (p.ℓ * t) i)) →
      SC2 p STK σ s := fun _ _ h => h.1.b.l.k.sc
  have p4 := lbP_piece hP hS hrc (r := wBase p + i) (o := 2) (g2 := p.γ₂)
    (fun σ => ⟨⟨sptr_ok rfl (by clt hF), by csep hF⟩, ⟨sptr_ok rfl (by decide), by csep hF⟩,
      show ix Reg.r31 ∈ sWb2 by decide, by csep hF, hF.g2,
      by have hg := hF.g2; simp only [gamma2s, List.mem_cons, List.not_mem_nil, or_false] at hg
         rcases hg with e | e <;> rw [e] <;> decide⟩)
    (F := fun σ => W'v p σ (p.ℓ * t) i) (fun _ _ h => h.2)
    (fun σ s s' h k => ⟨h.1.keep hF k (by csep hF),
      polyIs_keepW h.1.b.l.k.sc.site.ok k.frame (by csep hF) (by decide) rfl h.2⟩)
  -- its norm, into `r24`
  have hB : p.γ₂ - p.β < 2 ^ 31 := by
    have hg := hF.g2; simp only [gamma2s, List.mem_cons, List.not_mem_nil, or_false] at hg
    have hq : q = 8380417 := rfl
    rcases hg with e | e <;> rw [e] <;> omega
  have p5 := normP_piece hP hS hrc (f := 2) (B := p.γ₂ - p.β) (fun σ => ⟨sptr_ok rfl (by decide), by csep hF⟩)
    (fun σ => by csep hF) hB (F := fun σ => R0v p σ (p.ℓ * t) i)
    (fun σ s s' h k => ⟨h.1.keep hF k (by csep hF),
      polyIs_keepW h.1.b.l.k.sc.site.ok k.frame (by csep hF) (by decide) rfl h.2⟩)
  have p6 := and24_piece (p := p) (STK := STK) (J := fun σ s => ((IQ p STK σ t i (i + 1) s ∧
      PolyIs s.mem (SL p STK σ (wBase p + i)) (W'v p σ (p.ℓ * t) i)) ∧ PolyIs s.mem (SL p STK σ 2) (R0v p σ (p.ℓ * t) i)) ∧
      (s.gpr .r3).setWidth 32 = (if normRq [R0v p σ (p.ℓ * t) i] < p.γ₂ - p.β then 1 else 0))
    (J' := fun σ s => IQ p STK σ t (i + 1) (i + 1) s) (fun _ _ h => h.1.1.1.b.l.k.sc)
    fun σ s s' ⟨⟨⟨h, hw⟩, _⟩, h3⟩ r2 e24 => ⟨h.b.regs2 r2, fun j hj => by rw [r2.mem]; exact h.z j hj,
      fun j hj => by
        rw [r2.mem]
        rcases (by omega : j < i ∨ j = i) with h' | rfl
        exacts [h.w' j h', hw],
      fun j hj hj' => by rw [r2.mem]; exact h.w j hj hj',
      by rw [r2.gpr .r26 (by decide) (by decide)]; exact h.r26,
      by
        rw [e24, h.r24, bit_and h3]
        exact bit_congr ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨a, forall_lt_succ.mp ⟨b, c⟩⟩,
          fun ⟨a, b⟩ => ⟨⟨a, (forall_lt_succ.mpr b).1⟩, (forall_lt_succ.mpr b).2⟩⟩⟩
  unfold r0R normAt
  refine Piece.mono (p1.seq (p2.seq ((Piece.mono p3 (fun σ s _ h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩)
    fun σ s _ h => ⟨h.1.1, h.2⟩).seq (p4.seq (p5.seq p6))))) (fun σ s _ h => h.weak hi) fun _ _ _ h => h

end

section
variable {P : Prims} {S : Nat} (hP : SPrimsOk P S) {p : Params} (hF : SFacts p) {STK : Nat} (hS : S ≤ STK)
include hP hF hS

/-- `w[i] - cs₂[i]` while `ct₀[i]` and `h[i]` are computed. -/
abbrev HA (p : Params) (STK t i : Nat) (σ s : State) : Prop :=
  IH p STK σ t i i (i + 1) s ∧ PolyIs s.mem (SL p STK σ (wBase p + i)) (W'v p σ (p.ℓ * t) i)

/-- After the norm of `ct₀[i]`. -/
abbrev HB (p : Params) (STK t i : Nat) (σ s : State) : Prop :=
  (IH p STK σ t (i + 1) i (i + 1) s ∧ PolyIs s.mem (SL p STK σ (wBase p + i)) (W'v p σ (p.ℓ * t) i)) ∧
    PolyIs s.mem (SL p STK σ 3) (CT0v p σ (p.ℓ * t) i)

omit hP hS in
theorem ha_keep {t i : Nat} (hi : i < p.k) {σ s s' : State} (h : HA p STK t i σ s) {x : Nat} (hx : 1 ≤ x ∧ x < 5)
    (hk : Kept ((slay2 p STK σ).RL [tri (pS x) 1024, tri (sc oPS) 1024, (1, 0, STK)]) s s') :
    HA p STK t i σ s' := by
  have hk' := hF.k; have hl := hF.l; have hkl := hF.kl
  exact ⟨h.1.keep hF hk (by csep hF), polyIs_keepW h.1.b.l.k.sc.site.ok hk.frame (by csep hF) (by decide) rfl h.2⟩

omit hP hS in
theorem g2_lt : p.γ₂ < 2 ^ 31 := by
  have hg := hF.g2; simp only [gamma2s, List.mem_cons, List.not_mem_nil, or_false] at hg
  have hq : q = 8380417 := rfl
  rcases hg with e | e <;> rw [e] <;> omega

theorem hR_piece {t i : Nat} (hi : i < p.k) :
    SPiece p STK (fun σ s => IH p STK σ t i i i s) (fun σ s => IH p STK σ t (i + 1) (i + 1) (i + 1) s) (hR P p i) := by
  have hk' := hF.k; have hl := hF.l; have hkl := hF.kl
  have hg2 := g2_lt hF
  have hha : ∀ σ s, HA p STK t i σ s → SC2 p STK σ s := fun _ _ h => h.1.b.l.k.sc
  -- `T3 ← ct₀[i] = NTT⁻¹(ĉ t̂₀[i])`
  have p1 := mulP_piece hP hS hha (x := 3) (a := 0) (b := t0Base p + i)
    (fun σ => ⟨⟨sptr_ok rfl (by decide), by csep hF⟩, ⟨sptr_ok rfl (by decide), by csep hF⟩,
      ⟨sptr_ok rfl (by clt hF), by csep hF⟩, show ix Reg.r31 ∈ sWb2 by decide, by csep hF, by csep hF⟩)
    (F := fun σ => chF (cV p σ (p.ℓ * t))) (G := fun σ => T0v p σ i)
    (fun _ _ h => h.1.b.c) (fun _ _ h => h.1.b.l.k.t0 i hi)
    (fun σ s s' h k => ha_keep hF hi h (x := 3) (by decide) (k.monoL (by simp)))
  have p2 := ipP_piece hS hha (t := nttInv) hP.invNtt (x := 3) (name := "vg_mldsa_inv_ntt")
    (fun σ => ⟨⟨sptr_ok rfl (by decide), by csep hF⟩, ⟨sptr_ok rfl (by decide), by csep hF⟩,
      show ix Reg.r31 ∈ sWb2 by decide, show ix Reg.r31 ∈ sWb2 by decide, by csep hF⟩)
    (F := fun σ => multiplyNTT (chF (cV p σ (p.ℓ * t))) (T0v p σ i))
    (fun σ s s' h k => ha_keep hF hi h (x := 3) (by decide) (k.monoL (by simp)))
  -- its norm, into `r24`
  have p3 := normP_piece hP hS hha (f := 3) (B := p.γ₂) (fun σ => ⟨sptr_ok rfl (by decide), by csep hF⟩)
    (fun σ => by csep hF) hg2 (F := fun σ => CT0v p σ (p.ℓ * t) i)
    (fun σ s s' h k => ha_keep hF hi h (x := 3) (by decide) (k.monoL (by simp)))
  have p4 := and24_piece (p := p) (STK := STK) (J := fun σ s => (HA p STK t i σ s ∧
      PolyIs s.mem (SL p STK σ 3) (CT0v p σ (p.ℓ * t) i)) ∧
      (s.gpr .r3).setWidth 32 = (if normRq [CT0v p σ (p.ℓ * t) i] < p.γ₂ then 1 else 0))
    (J' := HB p STK t i) (fun _ _ h => h.1.1.1.b.l.k.sc)
    fun σ s s' ⟨⟨⟨h, hw⟩, h3c⟩, h3⟩ r2 e24 => ⟨⟨⟨h.b.regs2 r2, fun j hj => by rw [r2.mem]; exact h.z j hj,
      fun j hj => by rw [r2.mem]; exact h.w'' j hj, fun j hj hj' => by rw [r2.mem]; exact h.w' j hj hj',
      fun j hj => by rw [r2.mem]; exact h.h j hj, by rw [r2.gpr .r26 (by decide) (by decide)]; exact h.r26,
      by
        rw [e24, h.r24, bit_and h3]
        exact bit_congr ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨a, forall_lt_succ.mp ⟨b, c⟩⟩,
          fun ⟨a, b⟩ => ⟨⟨a, (forall_lt_succ.mpr b).1⟩, (forall_lt_succ.mpr b).2⟩⟩⟩,
      by rw [r2.mem]; exact hw⟩, by rw [r2.mem]; exact h3c⟩
  -- `T4 ← ct₀[i]`, then `T4 ← (T4 - ct₀[i]) - ct₀[i]`
  have p5 : SPiece p STK (HB p STK t i) (fun σ s => HB p STK t i σ s ∧
      PolyIs s.mem (SL p STK σ 4) (CT0v p σ (p.ℓ * t) i)) (copy .r31 (oP 3) .r31 (oP 4) 1024) := by
    refine ⟨fun σ s _ h => ?_, srel2 (fun σ s h => h.1.1.b.l.k.sc) (copy_taint _ _ _)⟩
    refine WP.mono (copyS h.1.1.b.l.k.sc.site (sb := .r31) (so := oP 3) (db := .r31)
      (dO := oP 4) (len := 1024) ⟨sptr_ok rfl (by decide), by csep hF⟩ ⟨sptr_ok rfl (by decide), by csep hF⟩
      (by decide) (by decide) (by decide) (by decide) (by decide) (by csep hF)) fun s' ⟨k', b'⟩ => ?_
    have hL := h.1.1.b.l.k.sc.site.ok
    exact ⟨⟨⟨h.1.1.keep hF k' (by csep hF), polyIs_keepW hL k'.frame (by csep hF) (by decide) rfl h.1.2⟩,
      polyIs_keepW hL k'.frame (by csep hF) (by decide) rfl h.2⟩, Proof.MlDsa.Sign.polyIs_of_bytes b' h.2⟩
  have hhb : ∀ σ s, HB p STK t i σ s → SC2 p STK σ s := fun _ _ h => h.1.1.b.l.k.sc
  have m44 : ∀ σ, KeyGen.AddOk (slay2 p STK σ) sWb2 (pS 4) (pS 3) := fun σ =>
    ⟨⟨sptr_ok rfl (by decide), by csep hF⟩, ⟨sptr_ok rfl (by decide), by csep hF⟩,
      show ix Reg.r31 ∈ sWb2 by decide, by csep hF⟩
  have hbk : ∀ σ s s', HB p STK t i σ s → Kept ((slay2 p STK σ).RL [tri (pS 4) 1024, (1, 0, STK)]) s s' →
      HB p STK t i σ s' := fun σ s s' h k => by
    have hL := h.1.1.b.l.k.sc.site.ok
    exact ⟨⟨h.1.1.keep hF k (by csep hF), polyIs_keepW hL k.frame (by csep hF) (by decide) rfl h.1.2⟩,
      polyIs_keepW hL k.frame (by csep hF) (by decide) rfl h.2⟩
  have p6 := subP_piece hP hS hhb (f := 4) (g := 3) m44 (F := fun σ => CT0v p σ (p.ℓ * t) i)
    (G := fun σ => CT0v p σ (p.ℓ * t) i) (fun _ _ h => h.2) hbk
  have p7 := subP_piece hP hS hhb (f := 4) (g := 3) m44
    (F := fun σ => sub (CT0v p σ (p.ℓ * t) i) (CT0v p σ (p.ℓ * t) i))
    (G := fun σ => CT0v p σ (p.ℓ * t) i) (fun _ _ h => h.2) hbk
  -- `w[i] ← w[i] - cs₂[i] + ct₀[i]`
  have hhc : ∀ σ s, ((IH p STK σ t (i + 1) i (i + 1) s ∧ PolyIs s.mem (SL p STK σ 3) (CT0v p σ (p.ℓ * t) i)) ∧
      PolyIs s.mem (SL p STK σ 4) (neg (CT0v p σ (p.ℓ * t) i))) → SC2 p STK σ s := fun _ _ h => h.1.1.b.l.k.sc
  have p8 := addP_piece hP hS hhc (f := wBase p + i) (g := 3)
    (fun σ => ⟨⟨sptr_ok rfl (by clt hF), by csep hF⟩, ⟨sptr_ok rfl (by decide), by csep hF⟩,
      show ix Reg.r31 ∈ sWb2 by decide, by csep hF⟩)
    (F := fun σ => W'v p σ (p.ℓ * t) i) (G := fun σ => CT0v p σ (p.ℓ * t) i) (fun _ _ h => h.1.2)
    (fun σ s s' h k => by
      have hL := h.1.1.b.l.k.sc.site.ok
      exact ⟨⟨h.1.1.keep hF k (by csep hF), polyIs_keepW hL k.frame (by csep hF) (by decide) rfl h.1.2⟩,
        polyIs_keepW hL k.frame (by csep hF) (by decide) rfl h.2⟩)
  -- `h[i] ← MakeHint(T4, w[i])`
  have mm : ∀ σ, KeyGen.UhOk (slay2 p STK σ) sWb2 (pS 4) (pS (wBase p + i)) p.γ₂ (pS (5 + i)) := fun σ =>
    ⟨⟨sptr_ok rfl (by decide), by csep hF⟩, ⟨sptr_ok rfl (by clt hF), by csep hF⟩,
      ⟨sptr_ok rfl (by clt hF), by csep hF⟩, show ix Reg.r31 ∈ sWb2 by decide, by csep hF, by csep hF, hF.g2, hg2⟩
  have p9' : SPiece p STK (fun σ s => (IH p STK σ t (i + 1) i (i + 1) s ∧
        PolyIs s.mem (SL p STK σ (wBase p + i)) (W''v p σ (p.ℓ * t) i)) ∧
        PolyIs s.mem (SL p STK σ 4) (neg (CT0v p σ (p.ℓ * t) i)))
      (fun σ s => ((IH p STK σ t (i + 1) i (i + 1) s ∧
        PolyIs s.mem (SL p STK σ (wBase p + i)) (W''v p σ (p.ℓ * t) i)) ∧
        HintIs s.mem (SL p STK σ (5 + i)) 1 [Hv p σ (p.ℓ * t) i]) ∧
        ((s.gpr .r3).setWidth 32).toNat = hintOnes [Hv p σ (p.ℓ * t) i])
      (callAt "vg_mldsa_make_hint" P.makeHint [(.r3, .ptr (pS 4)), (.r4, .ptr (pS (wBase p + i))), (.r5, .imm p.γ₂),
        (.r6, .ptr (pS (5 + i)))]) := by
    refine ⟨fun σ s _ ⟨⟨h, hw⟩, h4⟩ => ?_, rel_of (RelCT.exists_ fun σ => KeyGen.mh_tr hP.makeHint hS (mm σ)
      (P := fun x y => Two (slay2 p STK σ) sWb2 STK x y ∧ Reduced x.mem (SL p STK σ 4) ∧
        Reduced x.mem (SL p STK σ (wBase p + i)) ∧ Reduced y.mem (SL p STK σ 4) ∧
        Reduced y.mem (SL p STK σ (wBase p + i))) fun _ _ h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩)
      fun σ₁ _ _ _ _ _ pub h₁ h₂ => ⟨σ₁, sc2_twoL pub h₁.1.1.b.l.k.sc h₂.1.1.b.l.k.sc, h₁.2.1, h₁.1.2.1,
        by rw [SL_pub pub]; exact h₂.2.1, by rw [SL_pub pub]; exact h₂.1.2.1⟩⟩
    refine KeyGen.mh_ok hP.makeHint h.b.l.k.sc.site hS (mm σ) h4.1 hw.1 fun s' k' hq he => ?_
    have e1 : polyAt s.mem (lpa (slay2 p STK σ) (pS 4)) = neg (CT0v p σ (p.ℓ * t) i) := h4.2
    have e2 : polyAt s.mem (lpa (slay2 p STK σ) (pS (wBase p + i))) = W''v p σ (p.ℓ * t) i := hw.2
    rw [e1, e2] at hq he
    exact ⟨⟨⟨h.keep hF k' (by csep hF), polyIs_keepW h.b.l.k.sc.site.ok k'.frame (by csep hF) (by decide) rfl hw⟩,
      hq⟩, he⟩
  -- `r26 ← r26 + |h[i]|`
  have p9 : SPiece p STK (fun σ s => ((IH p STK σ t (i + 1) i (i + 1) s ∧
        PolyIs s.mem (SL p STK σ (wBase p + i)) (W''v p σ (p.ℓ * t) i)) ∧
        HintIs s.mem (SL p STK σ (5 + i)) 1 [Hv p σ (p.ℓ * t) i]) ∧
        ((s.gpr .r3).setWidth 32).toNat = hintOnes [Hv p σ (p.ℓ * t) i])
      (fun σ s => IH p STK σ t (i + 1) (i + 1) (i + 1) s) (.block [.lsr .w .r3 .r3 0, .add .r26 .r26 .r3]) := by
    refine ⟨fun σ s _ ⟨⟨⟨h, hw⟩, hh⟩, he⟩ => WP.mono (onesAdd_ok s) fun s' ⟨e26, m, rd, wr, sp, g⟩ => ?_,
      srel2 (fun σ s h => h.1.1.1.b.l.k.sc) (by taint_decide)⟩
    have hz : zx (s.gpr .r3) = BitVec.ofNat 64 (hintOnes [Hv p σ (p.ℓ * t) i]) := by
      apply BitVec.eq_of_toNat_eq
      rw [← he]
      simp only [zx, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have hk : KB p STK σ t s' := h.b.of_eq g m rd wr sp
    refine ⟨hk, fun j hj => by rw [m]; exact h.z j hj, fun j hj => by
        rw [m]
        rcases (by omega : j < i ∨ j = i) with h' | rfl
        exacts [h.w'' j h', hw],
      fun j hj hj' => by rw [m]; exact h.w' j hj hj', fun j hj => by
        rw [m]
        rcases (by omega : j < i ∨ j = i) with h' | rfl
        exacts [h.h j h', hh], ?_, by rw [g .r24 (by decide) (by decide)]; exact h.r24⟩
    rw [e26, h.r26, hz, ← BitVec.ofNat_add, onesSum_succ]
  unfold hR normAt makeHintAt
  refine Piece.mono (p1.seq (p2.seq ((p3.seq p4).seq (p5.seq (p6.seq ((Piece.mono p7 (fun _ _ _ h => h)
    fun σ s _ h => ⟨⟨⟨h.1.1.1, h.1.2⟩, by rw [sub_sub_self] at h; exact h.2⟩, h.1.1.2⟩).seq
    ((Piece.mono p8 (fun _ _ _ h => h) fun σ s _ h => ⟨⟨h.1.1.1, h.2⟩, h.1.2⟩).seq (p9'.seq p9))))))))
    (fun σ s _ h => h.weak hi) fun _ _ _ h => h

end

end VG.Proof.MlDsa.PPC64LE.Sign
