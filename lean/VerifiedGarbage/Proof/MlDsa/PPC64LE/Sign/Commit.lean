module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sign.Decode
public import VerifiedGarbage.Proof.MlDsa.Sign.Loop
import VerifiedGarbage.Proof.MlDsa.Sign.Mem
import VerifiedGarbage.Proof.MlDsa.Sign.Iter
import VerifiedGarbage.Proof.MlDsa.KeyGen.Rest
import VerifiedGarbage.Proof.MlKem.KPke
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.MlKem.PPC64LE.Prf
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlDsa.KeyGen.Mono
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sign.Decode
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint

/-!
# ML-DSA signing on PPC64LE: the commitment of an iteration

As on 32-bit ARM (`Proof/MlDsa/Arm/Sign/PhaseC.lean`). At the head of
iteration `t` of the loop (`IL`): what decoding left (`IK`), `κ = ℓt` in
`r27`, `814 - t` in `r25`, and the `t` iterations before rejected (within
`maxBounds`). Then `y[r]` from `ExpandMask(ρ″, κ + r)` and `ŷ[r] = NTT(y[r])`,
`w[i] = NTT⁻¹(∑_j Â[i, j] ŷ[j])`, `w1Encode(HighBits(w[i]))` at `W1`, and
`c̃ = H(μ ‖ w1Encode(w₁), λ/4)` at `CT` (`commit_piece`), each with the
polynomials done so far (`IC`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Sign

open VG VG.PPC64LE VG.Proof.MlKem.PPC64LE
open VG.Proof.MlDsa.PPC64LE.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of taint31 polyIs_keepW
  bytes_keepW copyS)
open VG.Impl.MlDsa.PPC64LE.Sign
open VG.Impl.MlDsa.PPC64LE.KeyGen (seqR callAt)
open VG.Impl.MlKem.PPC64LE (copy hash)
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Sign (aF s1F s2F t0F yF yhF wF w1F ctF amat Rej)
open VG.Spec.Sha3 (bytesAt)

/-- A part of a region apart from `W` is apart from `W`. -/
theorem sepAll_sub {sz : List Nat} {i o l o' l' : Nat} {W : List (Nat × Nat × Nat)} (h : sepAll sz (i, o, l) W = true)
    (h1 : o ≤ o') (h2 : o' + l' ≤ o + l) : sepAll sz (i, o', l') W = true :=
  List.all_eq_true.mpr fun w hw => by
    have := List.all_eq_true.mp h w hw
    obtain ⟨j, q, n⟩ := w
    simp only [sepB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at this ⊢
    omega

/-- A family of polynomials in consecutive slots of `scratch`, apart from what
a part writes, is kept. -/
theorem fam_keep {L : Lay} {Wb : List Nat} (hL : OkW L Wb) (h0 : 0 ∈ Wb) {W : List (Nat × Nat × Nat)} {m m' : Mem}
    (hf : Frame (L.RL W) m m') {b n : Nat} (h : sepAll L.sizes (0, oP b, 1024 * n) W = true) {F : Nat → Poly}
    (hp : ∀ j < n, PolyIs m (L.A 0 (oP (b + j))) (F j)) : ∀ j < n, PolyIs m' (L.A 0 (oP (b + j))) (F j) :=
  fun j hj => polyIs_keepW hL hf (sepAll_sub h (by unfold oP; omega) (by unfold oP; omega)) h0 rfl (hp j hj)

/-! ## What decoding left -/

section
variable (p : Params)

/-- The slots of `h`, `y`, `ŷ` and `w`. -/
abbrev yBase : Nat := 5 + p.k
abbrev yhBase : Nat := 5 + p.k + p.ℓ
abbrev wBase : Nat := 5 + p.k + 2 * p.ℓ

/-- The number of slots from `ŝ₁` to the end of `Â`. -/
abbrev nSec : Nat := p.ℓ + 2 * p.k + p.k * p.ℓ

/-- `Â[i, j]`, within `maxBounds`. -/
abbrev Am (σ : State) (i j : Nat) : Poly := aF maxBounds.rejNTT (rhoOf p σ) i j

/-- `y[r]`, `ŷ[r]`, `w[i]` and `c̃` of the iteration with counter `κ`. -/
abbrev Yv (σ : State) (κ r : Nat) : Poly := toRq (yF p (rppOf p σ) κ r)
abbrev YHv (σ : State) (κ r : Nat) : Poly := yhF p (rppOf p σ) κ r
abbrev Wv (σ : State) (κ i : Nat) : Poly := wF p (Am p σ) (rppOf p σ) κ i
abbrev CTv (σ : State) (κ : Nat) : List Byte := ctF p (Am p σ) (muOf σ) (rppOf p σ) κ

/-- The iterations before `t` were rejected, within `maxBounds`. -/
abbrev RejT (σ : State) (t : Nat) : Prop :=
  Rej p (amat p (Am p σ)) ((List.range p.ℓ).map (S1v p σ)) ((List.range p.k).map (S2v p σ))
    ((List.range p.k).map (T0v p σ)) (muOf σ) (rppOf p σ) maxBounds 0 t

end

/-- What decoding left: `Â`, `ρ″`, `ŝ₁`, `ŝ₂` and `t̂₀`. -/
structure IK (p : Params) (STK : Nat) (σ s : State) : Prop where
  sc : SC2 p STK σ s
  ok : ∀ e < p.k * p.ℓ, (rejNTTPoly maxBounds.rejNTT (seedE p σ e)).isSome
  A : ∀ e < p.k * p.ℓ, PolyIs s.mem ((slay2 p STK σ).A 0 (oP (aBase p + e))) (aVal p σ e)
  rpp : bytesAt s.mem ((slay2 p STK σ).A 0 oMS) 64 = rppOf p σ
  s1 : ∀ r < p.ℓ, PolyIs s.mem ((slay2 p STK σ).A 0 (oP (s1Base p + r))) (S1v p σ r)
  s2 : ∀ i < p.k, PolyIs s.mem ((slay2 p STK σ).A 0 (oP (s2Base p + i))) (S2v p σ i)
  t0 : ∀ i < p.k, PolyIs s.mem ((slay2 p STK σ).A 0 (oP (t0Base p + i))) (T0v p σ i)

theorem ID.ik {p : Params} {STK : Nat} {σ s : State} (h : ID p STK σ p.ℓ p.k p.k s) : IK p STK σ s :=
  ⟨h.sc, h.ok, h.A, h.rpp, h.s1, h.s2, h.t0⟩

/-- A part that writes `W`, apart from `ŝ₁`…`Â` and `ρ″`, keeps `IK`. -/
def ikChk (p : Params) (STK : Nat) (W : List (Nat × Nat × Nat)) : Bool :=
  sc2Chk p STK W && sepAll [scrLen p, STK, p.skLen, 64, p.sigLen] (0, oP (s1Base p), 1024 * nSec p) W &&
    sepAll [scrLen p, STK, p.skLen, 64, p.sigLen] (0, oMS, 64) W

theorem IK.keep {p : Params} {STK : Nat} {σ s s' : State} (h : IK p STK σ s) {W : List (Nat × Nat × Nat)}
    (hk : Kept ((slay2 p STK σ).RL W) s s') (hc : ikChk p STK W = true) : IK p STK σ s' := by
  simp only [ikChk, Bool.and_eq_true] at hc
  obtain ⟨⟨c1, c2⟩, c3⟩ := hc
  have hL := h.sc.site.ok
  have hb : ∀ {b n : Nat}, s1Base p ≤ b → b + n ≤ s1Base p + nSec p →
      sepAll (slay2 p STK σ).sizes (0, oP b, 1024 * n) W = true := fun {b n} h1 h2 =>
    sepAll_sub c2 (by unfold oP; omega) (by unfold oP; omega)
  have h0 : 0 ∈ sWb2 := by decide
  refine ⟨h.sc.keep hk c1, h.ok, ?_, by rw [bytes_keepW hL hk.frame c3 h0 (by decide)]; exact h.rpp,
    fam_keep hL h0 hk.frame (hb (Nat.le_refl _) (by simp only [nSec]; omega)) h.s1,
    fam_keep hL h0 hk.frame (hb (by simp only [s1Base, s2Base]; omega) (by simp only [s1Base, s2Base, nSec]; omega)) h.s2,
    fam_keep hL h0 hk.frame (hb (by simp only [s1Base, t0Base]; omega) (by simp only [s1Base, t0Base, nSec]; omega)) h.t0⟩
  exact fam_keep hL h0 hk.frame (hb (by simp only [s1Base, aBase]; omega) (by simp only [aBase, s1Base, nSec]; omega)) h.A

/-! ## The head of an iteration -/

/-- The head of iteration `t`. -/
structure IL (p : Params) (STK : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  k : IK p STK σ s
  r27 : s.gpr .r27 = BitVec.ofNat 64 (p.ℓ * t)
  r25 : s.gpr .r25 = BitVec.ofNat 64 (814 - t)
  t_lt : t < 814
  rej : RejT p σ t

/-- Iteration `t`, with the first `ny` polynomials of `y`, `nyh` of `ŷ`, `nw`
of `w`, and the encodings of `nh` of `w₁` at `W1`. -/
structure IC (p : Params) (STK : Nat) (σ : State) (t ny nyh nw nh : Nat) (s : State) : Prop where
  l : IL p STK σ t s
  y : ∀ r < ny, PolyIs s.mem ((slay2 p STK σ).A 0 (oP (yBase p + r))) (Yv p σ (p.ℓ * t) r)
  yh : ∀ r < nyh, PolyIs s.mem ((slay2 p STK σ).A 0 (oP (yhBase p + r))) (YHv p σ (p.ℓ * t) r)
  w : ∀ i < nw, PolyIs s.mem ((slay2 p STK σ).A 0 (oP (wBase p + i))) (Wv p σ (p.ℓ * t) i)
  w1 : bytesAt s.mem ((slay2 p STK σ).A 0 oW1) (w1Len p * nh) =
    (List.range nh).flatMap fun j => simpleBitPack (w1F p (Am p σ) (rppOf p σ) (p.ℓ * t) j) (w1Max p)
  w1b : w1Len p * nh ≤ 1024

/-- A part that writes `W` keeps `IC`. -/
def icChk (p : Params) (STK : Nat) (W : List (Nat × Nat × Nat)) (ny nyh nw nh : Nat) : Bool :=
  ikChk p STK W && sepAll [scrLen p, STK, p.skLen, 64, p.sigLen] (0, oP (yBase p), 1024 * ny) W &&
    sepAll [scrLen p, STK, p.skLen, 64, p.sigLen] (0, oP (yhBase p), 1024 * nyh) W &&
    sepAll [scrLen p, STK, p.skLen, 64, p.sigLen] (0, oP (wBase p), 1024 * nw) W &&
    sepAll [scrLen p, STK, p.skLen, 64, p.sigLen] (0, oW1, w1Len p * nh) W

theorem IC.keep {p : Params} {STK : Nat} {σ : State} {t ny nyh nw nh : Nat} {s s' : State}
    (h : IC p STK σ t ny nyh nw nh s) {W : List (Nat × Nat × Nat)} (hk : Kept ((slay2 p STK σ).RL W) s s')
    (hc : icChk p STK W ny nyh nw nh = true) (h25 : s'.gpr .r25 = s.gpr .r25) (h27 : s'.gpr .r27 = s.gpr .r27) :
    IC p STK σ t ny nyh nw nh s' := by
  simp only [icChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨c0, c1⟩, c2⟩, c3⟩, c4⟩ := hc
  have hL := h.l.k.sc.site.ok
  have h0 : 0 ∈ sWb2 := by decide
  have hw1 : w1Len p * nh ≤ 2 ^ 64 := by have := h.w1b; omega
  exact ⟨⟨h.l.k.keep hk c0, h27.trans h.l.r27, h25.trans h.l.r25, h.l.t_lt, h.l.rej⟩,
    fam_keep hL h0 hk.frame c1 h.y, fam_keep hL h0 hk.frame c2 h.yh, fam_keep hL h0 hk.frame c3 h.w,
    by rw [bytes_keepW hL hk.frame c4 h0 hw1]; exact h.w1, h.w1b⟩

/-! ## `κ + r` -/

theorem integerToBytes_two (x : Nat) : integerToBytes x 2 = [BitVec.ofNat 8 x, BitVec.ofNat 8 (x / 256)] := by
  simp [integerToBytes, List.range_succ]

theorem kappa_bytes {x : Nat} (hx : x < 2 ^ 16) :
    [(BitVec.ofNat 64 x).setWidth 8, (BitVec.ofNat 64 x >>> 8).setWidth 8] = integerToBytes x 2 := by
  rw [integerToBytes_two]
  congr 1
  · apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  · congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
    omega

theorem add_one_ne (a : Addr) : a ≠ a + 1 := by
  intro h
  have := congrArg BitVec.toNat h
  have ha := a.isLt
  rw [BitVec.toNat_add] at this
  have e1 : (1 : BitVec 64).toNat = 1 := rfl
  rw [e1] at this
  omega

theorem bytes2_write (m : Mem) (a : Addr) (v w : Byte) :
    bytesAt ((m.writeW a v).writeW (a + 1) w) a 2 = [v, w] := by
  show [((m.writeW a v).writeW (a + 1) w) (a + BitVec.ofNat 64 0),
    ((m.writeW a v).writeW (a + 1) w) (a + BitVec.ofNat 64 1)] = _
  have e0 : a + BitVec.ofNat 64 0 = a := BitVec.add_zero a
  have e1 : a + BitVec.ofNat 64 1 = a + 1 := rfl
  rw [e0, e1, VG.WriteBytes.writeW8_apply, VG.WriteBytes.writeW8_apply, VG.Proof.MlDsa.KeyGen.ifn (add_one_ne a),
    VG.Proof.MlDsa.KeyGen.ifp rfl, VG.WriteBytes.writeW8_apply, VG.Proof.MlDsa.KeyGen.ifp rfl]

section
variable {p : Params} (hF : SFacts p) {STK : Nat}
include hF

theorem setKappa_ok {σ s : State} {t ny nyh nw nh r : Nat} (h : IC p STK σ t ny nyh nw nh s) (hr : r < p.ℓ)
    (hc : icChk p STK [tri (sc (oMS + 64)) 2] ny nyh nw nh = true) :
    WP isa (.block (setKappa r)) s fun s' => IC p STK σ t ny nyh nw nh s' ∧
      bytesAt s'.mem ((slay2 p STK σ).A 0 (oMS + 64)) 2 = integerToBytes (p.ℓ * t + r) 2 := by
  have hl := hF.l
  have ht := h.l.t_lt
  have hs := h.l.k.sc.site
  have g31 : s.gpr .r31 = sScr σ := hs.r31
  have i64 : InRegions s.wr (sScr σ + BitVec.ofNat 64 (oMS + 64)) 1 :=
    hs.cwE (q := sc (oMS + 64)) (l := 1) ⟨sptr_ok rfl (by decide), by ssep hF⟩ (by decide) _ _
      ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  have i65 : InRegions s.wr (sScr σ + BitVec.ofNat 64 (oMS + 65)) 1 :=
    hs.cwE (q := sc (oMS + 65)) (l := 1) ⟨sptr_ok rfl (by decide), by ssep hF⟩ (by decide) _ _
      ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  have hmv : WP isa (.block (setKappa r)) s fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
      s'.mem = (s.mem.writeW (sScr σ + BitVec.ofNat 64 (oMS + 64)) ((s.gpr .r27 + BitVec.ofNat 64 r).setWidth 8)).writeW
        (sScr σ + BitVec.ofNat 64 (oMS + 65)) (((s.gpr .r27 + BitVec.ofNat 64 r) >>> 8).setWidth 8) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
    have hr' : r < 2 ^ 15 := by omega
    have o64 : oMS + 64 < 2 ^ 15 := by decide
    have o65 : oMS + 65 < 2 ^ 15 := by decide
    have hn : Reg.r31 ≠ Reg.r0 := by decide
    simp only [← g31] at i64 i65 ⊢
    prun [setKappa, exec_stb, hn, hr', o64, o65, i64, i65]
    and_intros
    all_goals first
      | exact trivial
      | rfl
      | (intro r hr
         have h0 : r ≠ .r3 := by rintro rfl; simp [preserved] at hr
         simp only [RegUpd.gpr_write, h0, ite_false])
  refine WP.mono hmv fun s' ⟨cs, m, rd, wr, sp⟩ => ?_
  have e65 : sScr σ + BitVec.ofNat 64 (oMS + 65) = sScr σ + BitVec.ofNat 64 (oMS + 64) + 1 := by
    rw [BitVec.add_assoc]; rfl
  have hk : Kept ((slay2 p STK σ).RL [tri (sc (oMS + 64)) 2]) s s' := by
    refine ⟨cs, sp, rd, wr, ?_⟩
    rw [m]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (VG.Offset.contains (sScr σ) (Nat.le_refl _) (by decide) (by decide))).writeW (List.mem_singleton_self _) _
      (VG.Offset.contains (sScr σ) (by decide) (by decide) (by decide))
  refine ⟨h.keep hk hc (cs .r25 (by decide)) (cs .r27 (by decide)), ?_⟩
  have hx : p.ℓ * t + r < 2 ^ 16 := by
    have := Nat.mul_le_mul_left p.ℓ (show t ≤ 813 by omega); omega
  show bytesAt s'.mem (sScr σ + BitVec.ofNat 64 (oMS + 64)) 2 = _
  rw [m, e65, bytes2_write, h.l.r27, ← BitVec.ofNat_add, kappa_bytes hx]

end

/-! ## Taint checks for any offsets -/

/-- The taint check of a copy within `scratch` does not depend on its offsets. -/
theorem copy_taint (so dO len : Nat) : (VG.PPC64LE.taint.check (Taint.ofRegs [.r31]) (copy .r31 so .r31 dO len)
    (VG.Taint.hintOf VG.PPC64LE.taint (Taint.ofRegs [.r31]) (copy .r31 0 .r31 0 1))).isSome = true := rfl

theorem setKappa_taint (r : Nat) : (VG.PPC64LE.taint.check (Taint.ofRegs [.r31]) (.block (setKappa r))
    (VG.Taint.hintOf VG.PPC64LE.taint (Taint.ofRegs [.r31]) (.block (setKappa 0)))).isSome = true := rfl

/-! ## `y` and `ŷ` -/

section
variable {P : Prims} {S : Nat} (hP : SPrimsOk P S) {p : Params} (hF : SFacts p) {STK : Nat} (hS : S ≤ STK)
include hP hF hS

/-- `κ + r` written. -/
abbrev M1 (p : Params) (STK t r : Nat) (σ s : State) : Prop :=
  IC p STK σ t r r 0 0 s ∧ bytesAt s.mem ((slay2 p STK σ).A 0 (oMS + 64)) 2 = integerToBytes (p.ℓ * t + r) 2

/-- `y[r]` copied to `ŷ[r]`. -/
abbrev M3 (p : Params) (STK t r : Nat) (σ s : State) : Prop :=
  IC p STK σ t (r + 1) r 0 0 s ∧ PolyIs s.mem ((slay2 p STK σ).A 0 (oP (yhBase p + r))) (Yv p σ (p.ℓ * t) r)

omit hP hS in
theorem em_m {σ : State} {r : Nat} (hr : r < p.ℓ) :
    KeyGen.RbOk (slay2 p STK σ) sWb2 (sc oMS) (yP p r) (sc oPS) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  exact ⟨⟨sptr_ok rfl (by decide), by ssep hF⟩, ⟨sptr_ok rfl (by slt hF), by ssep hF⟩,
    ⟨sptr_ok rfl (by decide), by ssep hF⟩, show ix Reg.r31 ∈ sWb2 by decide, show ix Reg.r31 ∈ sWb2 by decide,
    by ssep hF, by ssep hF, by ssep hF⟩

omit hP hS in
theorem nty_m {σ : State} {r : Nat} (hr : r < p.ℓ) : KeyGen.IpOk (slay2 p STK σ) sWb2 (yhP p r) (sc oPS) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  exact ⟨⟨sptr_ok rfl (by slt hF), by ssep hF⟩, ⟨sptr_ok rfl (by decide), by ssep hF⟩,
    show ix Reg.r31 ∈ sWb2 by decide, show ix Reg.r31 ∈ sWb2 by decide, by ssep hF⟩

omit hP hS in
theorem kappa_piece {t r : Nat} (hr : r < p.ℓ) :
    SPiece p STK (fun σ s => IC p STK σ t r r 0 0 s) (M1 p STK t r) (.block (setKappa r)) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  exact ⟨fun σ s _ h => setKappa_ok hF h hr (by ssep hF [icChk, ikChk, sc2Chk, yBase, yhBase, wBase, s1Base, nSec]),
    srel2 (fun σ s h => h.l.k.sc) (setKappa_taint r)⟩

theorem mask_piece {t r : Nat} (hr : r < p.ℓ) :
    SPiece p STK (M1 p STK t r) (fun σ s => IC p STK σ t (r + 1) r 0 0 s) (maskAt P p.γ₁ (yP p r)) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  refine ⟨fun σ s _ ⟨h, hb⟩ => ?_, rel_of (RelCT.exists_ fun σ => KeyGen.em_tr hP.expandMask hS
    (em_m hF (σ := σ) hr) hF.g1 fun _ _ h => ⟨h.1, h.2.1, h.2.2⟩)
    fun σ₁ _ _ _ _ _ pub h₁ h₂ => ⟨σ₁, sc2_twoL pub h₁.1.l.k.sc h₂.1.l.k.sc⟩⟩
  unfold maskAt
  refine KeyGen.em_ok hP.expandMask h.l.k.sc.site hS (em_m hF hr) hF.g1 fun s' k' hq => ?_
  have I := h.keep k' (by ssep hF [icChk, ikChk, sc2Chk, yBase, yhBase, wBase, s1Base, nSec])
    (k'.cs .r25 (by decide)) (k'.cs .r27 (by decide))
  have hms : bytesAt s.mem (lpa (slay2 p STK σ) (sc oMS)) 66 = rppOf p σ ++ integerToBytes (p.ℓ * t + r) 2 := by
    have e2 : bytesAt s.mem ((slay2 p STK σ).A 0 oMS + BitVec.ofNat 64 64) 2 = integerToBytes (p.ℓ * t + r) 2 := by
      simp only [Lay.A, BitVec.add_assoc, ← BitVec.ofNat_add] at hb ⊢; exact hb
    show bytesAt s.mem ((slay2 p STK σ).A 0 oMS) (64 + 2) = _
    rw [Proof.MlKem.bytesAt_add, h.l.k.rpp, e2]
  rw [hms] at hq
  refine ⟨I.l, fun r' hr' => ?_, I.yh, I.w, I.w1, I.w1b⟩
  rcases (by omega : r' < r ∨ r' = r) with h' | rfl
  exacts [I.y r' h', hq]

omit hP hS in
theorem copyY_piece {t r : Nat} (hr : r < p.ℓ) :
    SPiece p STK (fun σ s => IC p STK σ t (r + 1) r 0 0 s) (M3 p STK t r)
      (copy .r31 (oP (5 + p.k + r)) .r31 (oP (5 + p.k + p.ℓ + r)) 1024) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  refine ⟨fun σ s _ h => ?_, srel2 (fun σ s h => h.l.k.sc) (copy_taint _ _ _)⟩
  refine WP.mono (copyS h.l.k.sc.site (sb := .r31) (so := oP (5 + p.k + r)) (db := .r31)
    (dO := oP (5 + p.k + p.ℓ + r)) (len := 1024) ⟨sptr_ok rfl (by slt hF), by ssep hF⟩
    ⟨sptr_ok rfl (by slt hF), by ssep hF⟩ (by decide) (by slt hF) (by slt hF) (by decide) (by decide) (by ssep hF))
    fun s' ⟨k', b'⟩ => ⟨h.keep k' (by ssep hF [icChk, ikChk, sc2Chk, yBase, yhBase, wBase, s1Base, nSec])
      (k'.cs .r25 (by decide)) (k'.cs .r27 (by decide)), ?_⟩
  exact Proof.MlDsa.Sign.polyIs_of_bytes b' (h.y r (by omega))

theorem nttY_piece {t r : Nat} (hr : r < p.ℓ) :
    SPiece p STK (M3 p STK t r) (fun σ s => IC p STK σ t (r + 1) (r + 1) 0 0 s) (nttAt P (yhP p r)) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  refine ⟨fun σ s _ ⟨h, hy⟩ => ?_, rel_of (RelCT.exists_ fun σ => KeyGen.ip_tr (t := ntt) hP.ntt hS
    (nty_m hF (σ := σ) hr) (P := fun x y => Two (slay2 p STK σ) sWb2 STK x y ∧
      Reduced x.mem ((slay2 p STK σ).A 0 (oP (yhBase p + r))) ∧
      Reduced y.mem ((slay2 p STK σ).A 0 (oP (yhBase p + r))))
      fun _ _ h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2.1, h.2.2⟩)
    fun σ₁ _ _ _ _ _ pub h₁ h₂ => ⟨σ₁, sc2_twoL pub h₁.1.l.k.sc h₂.1.l.k.sc, h₁.2.1, by
      rw [slay2_pub pub]; exact h₂.2.1⟩⟩
  unfold nttAt
  refine KeyGen.ip_ok (t := ntt) hP.ntt h.l.k.sc.site hS (nty_m hF hr) hy.1 fun s' k' hq => ?_
  have I := h.keep k' (by ssep hF [icChk, ikChk, sc2Chk, yBase, yhBase, wBase, s1Base, nSec])
    (k'.cs .r25 (by decide)) (k'.cs .r27 (by decide))
  refine ⟨I.l, I.y, fun r' hr' => ?_, I.w, I.w1, I.w1b⟩
  rcases (by omega : r' < r ∨ r' = r) with h' | rfl
  · exact I.yh r' h'
  · have e : polyAt s.mem (lpa (slay2 p STK σ) (yhP p r')) = Yv p σ (p.ℓ * t) r' := hy.2
    rw [e] at hq
    exact hq

theorem maskR_piece {t r : Nat} (hr : r < p.ℓ) :
    SPiece p STK (fun σ s => IC p STK σ t r r 0 0 s) (fun σ s => IC p STK σ t (r + 1) (r + 1) 0 0 s)
      (maskR P p r) :=
  (kappa_piece hF hr).seq ((mask_piece hP hF hS hr).seq ((copyY_piece hF hr).seq (nttY_piece hP hF hS hr)))

end

/-! ## `w` -/

theorem aVal_ij {p : Params} {σ : State} {i j : Nat} (hj : j < p.ℓ) : aVal p σ (p.ℓ * i + j) = Am p σ i j := by
  have hl : 0 < p.ℓ := by omega
  have e1 : (p.ℓ * i + j) / p.ℓ = i := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hl, Nat.div_eq_of_lt hj, Nat.zero_add]
  have e2 : (p.ℓ * i + j) % p.ℓ = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  simp only [aVal, Am, e1, e2]

theorem aP_ij (p : Params) (i j : Nat) : aP p i j = pS (aBase p + (p.ℓ * i + j)) := by
  show pS (5 + 4 * p.k + 3 * p.ℓ + p.ℓ * i + j) = _
  rw [Nat.add_assoc (5 + 4 * p.k + 3 * p.ℓ)]

theorem ij_lt {p : Params} {i j : Nat} (hi : i < p.k) (hj : j < p.ℓ) : p.ℓ * i + j < p.k * p.ℓ := by
  have := Nat.mul_le_mul_left p.ℓ (show i + 1 ≤ p.k from hi)
  rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm p.ℓ p.k] at this; omega

/-- `∑_{j < m} Â[i, j] ŷ[j]`, summed from `j = 0` with `AddNTT`. -/
abbrev wAcc (p : Params) (σ : State) (κ i m : Nat) : Poly :=
  ((List.range m).map fun j => multiplyNTT (Am p σ i j) (YHv p σ κ j)).foldl add zero

theorem add_zero_left (x : Poly) : add zero x = x := by
  apply Vector.ext
  intro j hj
  simp [add, zero]

theorem wAcc_one (p : Params) (σ : State) (κ i : Nat) :
    wAcc p σ κ i 1 = multiplyNTT (Am p σ i 0) (YHv p σ κ 0) := by
  simp only [wAcc, List.range_one, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, add_zero_left]

theorem wAcc_succ (p : Params) (σ : State) (κ i m : Nat) :
    wAcc p σ κ i (m + 1) = add (wAcc p σ κ i m) (multiplyNTT (Am p σ i m) (YHv p σ κ m)) := by
  simp only [wAcc, List.range_succ, List.map_append, List.map_cons, List.map_nil, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

/-- Row `i` of `w`, with `m` terms of its sum. -/
abbrev WA (p : Params) (STK t i m : Nat) (σ s : State) : Prop :=
  IC p STK σ t p.ℓ p.ℓ i 0 s ∧ PolyIs s.mem ((slay2 p STK σ).A 0 (oP (wBase p + i))) (wAcc p σ (p.ℓ * t) i m)

theorem IC.aij {p : Params} {STK : Nat} {σ : State} {t ny nyh nw nh : Nat} {s : State}
    (h : IC p STK σ t ny nyh nw nh s) {i j : Nat} (hi : i < p.k) (hj : j < p.ℓ) :
    PolyIs s.mem ((slay2 p STK σ).A 0 (oP (aBase p + (p.ℓ * i + j)))) (Am p σ i j) := by
  rw [← aVal_ij hj]; exact h.l.k.A _ (ij_lt hi hj)

section
variable {P : Prims} {S : Nat} (hP : SPrimsOk P S) {p : Params} (hF : SFacts p) {STK : Nat} (hS : S ≤ STK)
include hP hF hS

omit hP hS in
theorem mw_m {σ : State} {i j : Nat} (hi : i < p.k) (hj : j < p.ℓ) :
    KeyGen.MulOk (slay2 p STK σ) sWb2 (wP p i) (pS (aBase p + (p.ℓ * i + j))) (yhP p j) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have he := ij_lt hi hj
  generalize p.ℓ * i + j = e at he ⊢
  exact ⟨⟨sptr_ok rfl (by slt hF), by ssep hF⟩, ⟨sptr_ok rfl (by slt hF), by ssep hF⟩,
    ⟨sptr_ok rfl (by slt hF), by ssep hF⟩, show ix Reg.r31 ∈ sWb2 by decide, by ssep hF, by ssep hF⟩

omit hP hS in
theorem ntw_m {σ : State} {i : Nat} (hi : i < p.k) : KeyGen.IpOk (slay2 p STK σ) sWb2 (wP p i) (sc oPS) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  exact ⟨⟨sptr_ok rfl (by slt hF), by ssep hF⟩, ⟨sptr_ok rfl (by decide), by ssep hF⟩,
    show ix Reg.r31 ∈ sWb2 by decide, show ix Reg.r31 ∈ sWb2 by decide, by ssep hF⟩

theorem mulW_piece {t i : Nat} (hi : i < p.k) :
    SPiece p STK (fun σ s => IC p STK σ t p.ℓ p.ℓ i 0 s) (WA p STK t i 1) (mulAt P (wP p i) (aP p i 0) (yhP p 0)) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have h0 : 0 < p.ℓ := by omega
  rw [aP_ij]
  refine ⟨fun σ s _ h => ?_, rel_of (RelCT.exists_ fun σ => KeyGen.mul_tr hP.mul hS (mw_m hF (σ := σ) hi h0)
    (P := fun x y => Two (slay2 p STK σ) sWb2 STK x y ∧
      Reduced x.mem ((slay2 p STK σ).A 0 (oP (aBase p + (p.ℓ * i + 0)))) ∧
      Reduced x.mem ((slay2 p STK σ).A 0 (oP (yhBase p + 0))) ∧
      Reduced y.mem ((slay2 p STK σ).A 0 (oP (aBase p + (p.ℓ * i + 0)))) ∧
      Reduced y.mem ((slay2 p STK σ).A 0 (oP (yhBase p + 0))))
    fun _ _ h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩)
    fun σ₁ _ _ _ _ _ pub h₁ h₂ => ⟨σ₁, sc2_twoL pub h₁.l.k.sc h₂.l.k.sc, (h₁.aij hi h0).1, (h₁.yh 0 h0).1,
      by rw [slay2_pub pub]; exact (h₂.aij hi h0).1, by rw [slay2_pub pub]; exact (h₂.yh 0 h0).1⟩⟩
  unfold mulAt
  refine KeyGen.mul_ok hP.mul h.l.k.sc.site hS (mw_m hF hi h0) (h.aij hi h0).1 (h.yh 0 h0).1 fun s' k' hq => ?_
  refine ⟨h.keep k' (by ssep hF [icChk, ikChk, sc2Chk, yBase, yhBase, wBase, s1Base, nSec])
    (k'.cs .r25 (by decide)) (k'.cs .r27 (by decide)), ?_⟩
  have e1 : polyAt s.mem (lpa (slay2 p STK σ) (pS (aBase p + (p.ℓ * i + 0)))) = Am p σ i 0 := (h.aij hi h0).2
  have e2 : polyAt s.mem (lpa (slay2 p STK σ) (yhP p 0)) = YHv p σ (p.ℓ * t) 0 := (h.yh 0 h0).2
  rw [e1, e2, ← wAcc_one] at hq
  exact hq

theorem mulAddW_piece {t i j : Nat} (hi : i < p.k) (hj : j < p.ℓ) :
    SPiece p STK (WA p STK t i j) (WA p STK t i (j + 1)) (mulAddAt P (wP p i) (aP p i j) (yhP p j)) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  rw [aP_ij]
  refine ⟨fun σ s _ ⟨h, hw⟩ => ?_, rel_of (RelCT.exists_ fun σ => KeyGen.mulAdd_tr hP.mulAdd hS
    (mw_m hF (σ := σ) hi hj)
    (P := fun x y => Two (slay2 p STK σ) sWb2 STK x y ∧
      Reduced x.mem ((slay2 p STK σ).A 0 (oP (wBase p + i))) ∧
      Reduced x.mem ((slay2 p STK σ).A 0 (oP (aBase p + (p.ℓ * i + j)))) ∧
      Reduced x.mem ((slay2 p STK σ).A 0 (oP (yhBase p + j))) ∧
      Reduced y.mem ((slay2 p STK σ).A 0 (oP (wBase p + i))) ∧
      Reduced y.mem ((slay2 p STK σ).A 0 (oP (aBase p + (p.ℓ * i + j)))) ∧
      Reduced y.mem ((slay2 p STK σ).A 0 (oP (yhBase p + j))))
    fun _ _ h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩)
    fun σ₁ _ _ _ _ _ pub h₁ h₂ => ⟨σ₁, sc2_twoL pub h₁.1.l.k.sc h₂.1.l.k.sc, h₁.2.1, (h₁.1.aij hi hj).1,
      (h₁.1.yh j hj).1, by rw [slay2_pub pub]; exact h₂.2.1, by rw [slay2_pub pub]; exact (h₂.1.aij hi hj).1,
      by rw [slay2_pub pub]; exact (h₂.1.yh j hj).1⟩⟩
  unfold mulAddAt
  refine KeyGen.mulAdd_ok hP.mulAdd h.l.k.sc.site hS (mw_m hF hi hj) hw.1 (h.aij hi hj).1 (h.yh j hj).1
    fun s' k' hq => ?_
  refine ⟨h.keep k' (by ssep hF [icChk, ikChk, sc2Chk, yBase, yhBase, wBase, s1Base, nSec])
    (k'.cs .r25 (by decide)) (k'.cs .r27 (by decide)), ?_⟩
  have e0 : polyAt s.mem (lpa (slay2 p STK σ) (wP p i)) = wAcc p σ (p.ℓ * t) i j := hw.2
  have e1 : polyAt s.mem (lpa (slay2 p STK σ) (pS (aBase p + (p.ℓ * i + j)))) = Am p σ i j := (h.aij hi hj).2
  have e2 : polyAt s.mem (lpa (slay2 p STK σ) (yhP p j)) = YHv p σ (p.ℓ * t) j := (h.yh j hj).2
  rw [e0, e1, e2, ← wAcc_succ] at hq
  exact hq

theorem invW_piece {t i : Nat} (hi : i < p.k) :
    SPiece p STK (WA p STK t i p.ℓ) (fun σ s => IC p STK σ t p.ℓ p.ℓ (i + 1) 0 s) (invNttAt P (wP p i)) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  refine ⟨fun σ s _ ⟨h, hw⟩ => ?_, rel_of (RelCT.exists_ fun σ => KeyGen.ip_tr (t := nttInv) hP.invNtt hS
    (ntw_m hF (σ := σ) hi) (P := fun x y => Two (slay2 p STK σ) sWb2 STK x y ∧
      Reduced x.mem ((slay2 p STK σ).A 0 (oP (wBase p + i))) ∧
      Reduced y.mem ((slay2 p STK σ).A 0 (oP (wBase p + i))))
      fun _ _ h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2.1, h.2.2⟩)
    fun σ₁ _ _ _ _ _ pub h₁ h₂ => ⟨σ₁, sc2_twoL pub h₁.1.l.k.sc h₂.1.l.k.sc, h₁.2.1, by
      rw [slay2_pub pub]; exact h₂.2.1⟩⟩
  unfold invNttAt
  refine KeyGen.ip_ok (t := nttInv) hP.invNtt h.l.k.sc.site hS (ntw_m hF hi) hw.1 fun s' k' hq => ?_
  have I := h.keep k' (by ssep hF [icChk, ikChk, sc2Chk, yBase, yhBase, wBase, s1Base, nSec])
    (k'.cs .r25 (by decide)) (k'.cs .r27 (by decide))
  refine ⟨I.l, I.y, I.yh, fun i' hi' => ?_, I.w1, I.w1b⟩
  rcases (by omega : i' < i ∨ i' = i) with h' | rfl
  · exact I.w i' h'
  · have e : polyAt s.mem (lpa (slay2 p STK σ) (wP p i')) = wAcc p σ (p.ℓ * t) i' p.ℓ := hw.2
    rw [e] at hq
    exact hq

theorem rowW_piece {t i : Nat} (hi : i < p.k) :
    SPiece p STK (fun σ s => IC p STK σ t p.ℓ p.ℓ i 0 s) (fun σ s => IC p STK σ t p.ℓ p.ℓ (i + 1) 0 s)
      (rowW P p i) := by
  have hl := hF.l
  unfold rowW
  refine (mulW_piece hP hF hS hi).seq ((Piece.mono (Piece.seqR (I := fun j => WA p STK t i j) (p.ℓ - 1) 1
    fun j h1 h2 => mulAddW_piece hP hF hS hi (by omega)) (fun _ _ _ h => h) fun _ _ _ h => ?_).seq
    (invW_piece hP hF hS hi))
  rwa [show 1 + (p.ℓ - 1) = p.ℓ by omega] at h

end

end VG.Proof.MlDsa.PPC64LE.Sign

