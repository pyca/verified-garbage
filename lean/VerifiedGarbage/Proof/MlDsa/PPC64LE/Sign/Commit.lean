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

end VG.Proof.MlDsa.PPC64LE.Sign
