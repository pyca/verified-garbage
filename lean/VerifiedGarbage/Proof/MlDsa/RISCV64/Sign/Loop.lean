module

import VerifiedGarbage.Proof.Framework.RISCV64.MRun
import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
public import VerifiedGarbage.Proof.MlDsa.Sign.Iter
import VerifiedGarbage.Proof.MlDsa.KeyGen.Mono
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Run
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.MlDsa.Sign.Mem
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.MlDsa.Verify.Mem
import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.MlDsa.RISCV64.Sign.Decode
import VerifiedGarbage.Proof.MlDsa.KeyGen.Rest
import VerifiedGarbage.Proof.MlKem.KPke
import VerifiedGarbage.Proof.MlKem.RISCV64.Prf
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Sign.Decode
meta import VerifiedGarbage.Proof.MlDsa.Sign.Iter
meta import VerifiedGarbage.Proof.MlDsa.Sign.Mem
meta import VerifiedGarbage.Proof.MlDsa.KeyGen.Rest
meta import VerifiedGarbage.Proof.MlKem.KPke
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Prf
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlDsa.KeyGen.Mono
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.MRun
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.TCB.RISCV64.Target

/-! ### `MlDsa.RISCV64.Sign.Checks`, which only this module used -/

section

/-! ### `MlDsa.RISCV64.Sign.Calls`, which only this module used -/

section

/-! ### `MlDsa.RISCV64.Sign.Commit`, which only this module used -/

section

/-!
# ML-DSA signing on RISC-V: the commitment of an iteration

As on PPC64LE (`Proof/MlDsa/PPC64LE/Sign/PhaseC.lean`). At the head of
iteration `t` of the loop (`IL`): what decoding left (`IK`), `κ = ℓt` in
`s7`, `814 - t` in `s5`, and the `t` iterations before rejected (within
`maxBounds`). Then `y[r]` from `ExpandMask(ρ″, κ + r)` and `ŷ[r] = NTT(y[r])`,
`w[i] = NTT⁻¹(∑_j Â[i, j] ŷ[j])`, `w1Encode(HighBits(w[i]))` at `W1`, and
`c̃ = H(μ ‖ w1Encode(w₁), λ/4)` at `CT` (`commit_piece`), each with the
polynomials done so far (`IC`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Sign

open VG VG.RISCV64 VG.Proof.MlKem.RISCV64
open VG.Proof.MlDsa.RISCV64.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of taint31 polyIs_keepW
  bytes_keepW copyS hashLay hashLay_ptr hashS hashS_tr pieceS ix_ne1 shake31)
open VG.Impl.MlDsa.RISCV64.Sign
open VG.Impl.MlDsa.RISCV64.KeyGen (seqR callAt)
open VG.Impl.MlKem.RISCV64 (copy hash)
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
    omega_using [h1, h2, this]

/-- A family of polynomials in consecutive slots of `scratch`, apart from what
a part writes, is kept. -/
theorem fam_keep {L : Lay} {Wb : List Nat} (hL : OkW L Wb) (h0 : 0 ∈ Wb) {W : List (Nat × Nat × Nat)} {m m' : Mem}
    (hf : Frame (L.RL W) m m') {b n : Nat} (h : sepAll L.sizes (0, oP b, 1024 * n) W = true) {F : Nat → Poly}
    (hp : ∀ j < n, PolyIs m (L.A 0 (oP (b + j))) (F j)) : ∀ j < n, PolyIs m' (L.A 0 (oP (b + j))) (F j) :=
  fun j hj => polyIs_keepW hL hf (sepAll_sub h (by unfold oP; omega_using []) (by unfold oP; omega_using [hj])) h0 rfl (hp j hj)

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
    sepAll_sub c2 (by unfold oP; omega_using [h1]) (by unfold oP; omega_using [h2])
  have h0 : 0 ∈ sWb2 := by decide
  refine ⟨h.sc.keep hk c1, h.ok, ?_, by rw [bytes_keepW hL hk.frame c3 h0 (by decide)]; exact h.rpp,
    fam_keep hL h0 hk.frame (hb (Nat.le_refl _) (by simp only [nSec]; omega_using [])) h.s1,
    fam_keep hL h0 hk.frame (hb (by simp only [s1Base, s2Base]; omega_using []) (by simp only [s1Base, s2Base, nSec]; omega_using [])) h.s2,
    fam_keep hL h0 hk.frame (hb (by simp only [s1Base, t0Base]; omega_using []) (by simp only [s1Base, t0Base, nSec]; omega_using [])) h.t0⟩
  exact fam_keep hL h0 hk.frame (hb (by simp only [s1Base, aBase]; omega_using []) (by simp only [aBase, s1Base, nSec]; omega_using [])) h.A

/-! ## The head of an iteration -/

/-- The head of iteration `t`. -/
structure IL (p : Params) (STK : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  k : IK p STK σ s
  s7 : s.gpr .s7 = BitVec.ofNat 64 (p.ℓ * t)
  s5 : s.gpr .s5 = BitVec.ofNat 64 (814 - t)
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
    (hc : icChk p STK W ny nyh nw nh = true) (h25 : s'.gpr .s5 = s.gpr .s5) (h27 : s'.gpr .s7 = s.gpr .s7) :
    IC p STK σ t ny nyh nw nh s' := by
  simp only [icChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨c0, c1⟩, c2⟩, c3⟩, c4⟩ := hc
  have hL := h.l.k.sc.site.ok
  have h0 : 0 ∈ sWb2 := by decide
  have hw1 : w1Len p * nh ≤ 2 ^ 64 := by have := h.w1b; omega_using [this]
  exact ⟨⟨h.l.k.keep hk c0, h27.trans h.l.s7, h25.trans h.l.s5, h.l.t_lt, h.l.rej⟩,
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
  omega_using [this]

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
  have g31 : s.gpr .s11 = sScr σ := hs.s11
  have i64 : InRegions s.wr (sScr σ + BitVec.ofNat 64 (oMS + 64)) 1 :=
    hs.cwE (q := sc (oMS + 64)) (l := 1) ⟨sptr_ok rfl (by decide), by ssep hF⟩ (by decide) _ _
      ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  have i65 : InRegions s.wr (sScr σ + BitVec.ofNat 64 (oMS + 65)) 1 :=
    hs.cwE (q := sc (oMS + 65)) (l := 1) ⟨sptr_ok rfl (by decide), by ssep hF⟩ (by decide) _ _
      ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  have hmv : WP isa (.block (setKappa r)) s fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
      s'.mem = (s.mem.writeW (sScr σ + BitVec.ofNat 64 (oMS + 64)) ((s.gpr .s7 + BitVec.ofNat 64 r).setWidth 8)).writeW
        (sScr σ + BitVec.ofNat 64 (oMS + 65)) (((s.gpr .s7 + BitVec.ofNat 64 r) >>> 8).setWidth 8) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
    have hr' : r < 2048 := by omega_using [hr, hl]
    have o64 : oMS + 64 < 2048 := by decide
    have o65 : oMS + 65 < 2048 := by decide
    have hn : Reg.s11 ≠ Reg.t0 := by decide
    simp only [← g31] at i64 i65 ⊢
    mrun [setKappa, hn, hr', o64, o65, i64, i65]
    refine ⟨fun r hr => ?_, by simp only [Mem.writeW, BitVec.setWidth_eq]⟩
    have h0 : r ≠ .a0 := by rintro rfl; simp [preserved] at hr
    simp only [h0, ite_false]
  refine WP.mono hmv fun s' ⟨cs, m, rd, wr, sp⟩ => ?_
  have e65 : sScr σ + BitVec.ofNat 64 (oMS + 65) = sScr σ + BitVec.ofNat 64 (oMS + 64) + 1 := by
    rw [BitVec.add_assoc]; rfl
  have hk : Kept ((slay2 p STK σ).RL [tri (sc (oMS + 64)) 2]) s s' := by
    refine ⟨cs, sp, rd, wr, ?_⟩
    rw [m]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (VG.Offset.contains (sScr σ) (Nat.le_refl _) (by decide) (by decide))).writeW (List.mem_singleton_self _) _
      (VG.Offset.contains (sScr σ) (by decide) (by decide) (by decide))
  refine ⟨h.keep hk hc (cs .s5 (by decide)) (cs .s7 (by decide)), ?_⟩
  have hx : p.ℓ * t + r < 2 ^ 16 := by
    have := Nat.mul_le_mul_left p.ℓ (show t ≤ 813 by omega_using [ht]); omega_using [hr, hl, this]
  show bytesAt s'.mem (sScr σ + BitVec.ofNat 64 (oMS + 64)) 2 = _
  rw [m, e65, bytes2_write, h.l.s7, ← BitVec.ofNat_add, kappa_bytes hx]

end

/-! ## Taint checks for any offsets -/

/-- The taint check of a copy within `scratch`, between offsets past the
12-bit immediates (so moved by `lui` and `addi`, `addrOf`), does not depend on
its offsets. -/
theorem copy_taint (so dO len : Nat) (hso : 2048 ≤ so) (hdo : 2048 ≤ dO) :
    (VG.RISCV64.taint.check (Taint.ofRegs [.s11]) (copy .s11 so .s11 dO len)
      (VG.Taint.hintOf VG.RISCV64.taint (Taint.ofRegs [.s11]) (copy .s11 4096 .s11 4096 1))).isSome = true := by
  simp only [copy, VG.Impl.MlKem.RISCV64.addrOf, ite_eq_right (show ¬ so < 2048 by omega_using [hso]),
    ite_eq_right (show ¬ dO < 2048 by omega_using [hdo])]
  rfl

theorem setKappa_taint (r : Nat) : (VG.RISCV64.taint.check (Taint.ofRegs [.s11]) (.block (setKappa r))
    (VG.Taint.hintOf VG.RISCV64.taint (Taint.ofRegs [.s11]) (.block (setKappa 0)))).isSome = true := rfl

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
    ⟨sptr_ok rfl (by decide), by ssep hF⟩, show ix Reg.s11 ∈ sWb2 by decide, show ix Reg.s11 ∈ sWb2 by decide,
    by ssep hF, by ssep hF, by ssep hF, by salsep, by salsep⟩

omit hP hS in
theorem nty_m {σ : State} {r : Nat} (hr : r < p.ℓ) : KeyGen.IpOk (slay2 p STK σ) sWb2 (yhP p r) (sc oPS) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  exact ⟨⟨sptr_ok rfl (by slt hF), by ssep hF⟩, ⟨sptr_ok rfl (by decide), by ssep hF⟩,
    show ix Reg.s11 ∈ sWb2 by decide, show ix Reg.s11 ∈ sWb2 by decide, by ssep hF, by salsep, by salsep⟩

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
    (k'.cs .s5 (by decide)) (k'.cs .s7 (by decide))
  have hms : bytesAt s.mem (lpa (slay2 p STK σ) (sc oMS)) 66 = rppOf p σ ++ integerToBytes (p.ℓ * t + r) 2 := by
    have e2 : bytesAt s.mem ((slay2 p STK σ).A 0 oMS + BitVec.ofNat 64 64) 2 = integerToBytes (p.ℓ * t + r) 2 := by
      simp only [Lay.A, BitVec.add_assoc, ← BitVec.ofNat_add] at hb ⊢; exact hb
    show bytesAt s.mem ((slay2 p STK σ).A 0 oMS) (64 + 2) = _
    rw [Proof.MlKem.bytesAt_add, h.l.k.rpp, e2]
  rw [hms] at hq
  refine ⟨I.l, fun r' hr' => ?_, I.yh, I.w, I.w1, I.w1b⟩
  rcases (by omega_using [hr'] : r' < r ∨ r' = r) with h' | rfl
  exacts [I.y r' h', hq]

omit hP hS in
theorem copyY_piece {t r : Nat} (hr : r < p.ℓ) :
    SPiece p STK (fun σ s => IC p STK σ t (r + 1) r 0 0 s) (M3 p STK t r)
      (copy .s11 (oP (5 + p.k + r)) .s11 (oP (5 + p.k + p.ℓ + r)) 1024) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  refine ⟨fun σ s _ h => ?_, srel2 (fun σ s h => h.l.k.sc) (copy_taint _ _ _ (by unfold oP; omega_using []) (by unfold oP; omega_using []))⟩
  refine WP.mono (copyS h.l.k.sc.site (sb := .s11) (so := oP (5 + p.k + r)) (db := .s11)
    (dO := oP (5 + p.k + p.ℓ + r)) (len := 1024) ⟨sptr_ok rfl (by slt hF), by ssep hF⟩
    ⟨sptr_ok rfl (by slt hF), by ssep hF⟩ (by decide) (by slt hF) (by slt hF) (by decide) (by decide) (by ssep hF))
    fun s' ⟨k', b'⟩ => ⟨h.keep k' (by ssep hF [icChk, ikChk, sc2Chk, yBase, yhBase, wBase, s1Base, nSec])
      (k'.cs .s5 (by decide)) (k'.cs .s7 (by decide)), ?_⟩
  exact Proof.MlDsa.Sign.polyIs_of_bytes b' (h.y r (by omega_using []))

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
    (k'.cs .s5 (by decide)) (k'.cs .s7 (by decide))
  refine ⟨I.l, I.y, fun r' hr' => ?_, I.w, I.w1, I.w1b⟩
  rcases (by omega_using [hr'] : r' < r ∨ r' = r) with h' | rfl
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
  have hl : 0 < p.ℓ := by omega_using [hj]
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
  rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm p.ℓ p.k] at this; omega_using [hj, this]

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
    ⟨sptr_ok rfl (by slt hF), by ssep hF⟩, show ix Reg.s11 ∈ sWb2 by decide, by ssep hF, by ssep hF, by salsep, by salsep, by salsep⟩

omit hP hS in
theorem ntw_m {σ : State} {i : Nat} (hi : i < p.k) : KeyGen.IpOk (slay2 p STK σ) sWb2 (wP p i) (sc oPS) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  exact ⟨⟨sptr_ok rfl (by slt hF), by ssep hF⟩, ⟨sptr_ok rfl (by decide), by ssep hF⟩,
    show ix Reg.s11 ∈ sWb2 by decide, show ix Reg.s11 ∈ sWb2 by decide, by ssep hF, by salsep, by salsep⟩

theorem mulW_piece {t i : Nat} (hi : i < p.k) :
    SPiece p STK (fun σ s => IC p STK σ t p.ℓ p.ℓ i 0 s) (WA p STK t i 1) (mulAt P (wP p i) (aP p i 0) (yhP p 0)) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have h0 : 0 < p.ℓ := by omega_using [hl]
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
    (k'.cs .s5 (by decide)) (k'.cs .s7 (by decide)), ?_⟩
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
    (k'.cs .s5 (by decide)) (k'.cs .s7 (by decide)), ?_⟩
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
    (k'.cs .s5 (by decide)) (k'.cs .s7 (by decide))
  refine ⟨I.l, I.y, I.yh, fun i' hi' => ?_, I.w1, I.w1b⟩
  rcases (by omega_using [hi'] : i' < i ∨ i' = i) with h' | rfl
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
    fun j h1 h2 => mulAddW_piece hP hF hS hi (by omega_using [hl, h2])) (fun _ _ _ h => h) fun _ _ _ h => ?_).seq
    (invW_piece hP hF hS hi))
  rwa [show 1 + (p.ℓ - 1) = p.ℓ by omega_using [hl]] at h

end

/-! ## `w₁` and `c̃` -/

theorem natPolyIs_coeff {m : Mem} {a : Addr} {f : Vector Nat n} (h : NatPolyIs m a f) {j : Nat} (hj : j < 256) :
    (coeffAt m a j).toNat = f[j] := by
  have := congrArg (·[j]) h
  simp only [natPolyAt, Vector.getElem_ofFn] at this
  exact this

/-- `w₁[i]` in `T1`. -/
abbrev H1 (p : Params) (STK t i : Nat) (σ s : State) : Prop :=
  IC p STK σ t p.ℓ p.ℓ p.k i s ∧ NatPolyIs s.mem ((slay2 p STK σ).A 0 (oP 1)) (w1F p (Am p σ) (rppOf p σ) (p.ℓ * t) i)

/-- The commitment: `y`, `ŷ`, `w`, and `c̃` at `CT`. -/
abbrev ICd (p : Params) (STK t : Nat) (σ s : State) : Prop :=
  IC p STK σ t p.ℓ p.ℓ p.k p.k s ∧ bytesAt s.mem ((slay2 p STK σ).A 0 oCT) (cLen p) = CTv p σ (p.ℓ * t)

/-- The buffers of the sponge: `mu` and `scratch`. -/
abbrev Kmu : Nat → Bool := fun i => i == 3

theorem kmu : ∀ i < 5, ∀ j < 5, i ≠ j → 2 ≤ i → 2 ≤ j → Kmu i = true → Kmu j = true → i ∈ sWb2 ∨ j ∈ sWb2 :=
  fun i _ j _ hij _ _ hi hj => by
    simp only [Kmu, beq_iff_eq] at hi hj; omega

section
variable {P : Prims} {S : Nat} (hP : SPrimsOk P S) {p : Params} (hF : SFacts p) {STK : Nat} (hS : S ≤ STK)
include hP hF hS

omit hP hS in
theorem hb_m {σ : State} {i : Nat} (hi : i < p.k) : KeyGen.BitsOk (slay2 p STK σ) sWb2 (wP p i) p.γ₂ t1P := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have hg := hF.g2
  exact ⟨⟨sptr_ok rfl (by slt hF), by ssep hF⟩, ⟨sptr_ok rfl (by decide), by ssep hF⟩,
    show ix Reg.s11 ∈ sWb2 by decide, by ssep hF, hg,
    by simp only [gamma2s, List.mem_cons, List.not_mem_nil, or_false] at hg; rcases hg with e | e <;> rw [e] <;> decide, by salsep, by salsep⟩

omit hP hS in
theorem w1_off {i : Nat} (hi : i < p.k) : w1Len p * i + w1Len p ≤ 1024 := by
  have hw := hF.w1
  have := Nat.mul_le_mul_left (w1Len p) (show i + 1 ≤ p.k from hi)
  rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm (w1Len p) p.k] at this; omega_using [hw, this]

omit hP hS in
theorem sbpW_m {σ : State} {i : Nat} (hi : i < p.k) :
    KeyGen.SbpOk (slay2 p STK σ) sWb2 t1P (w1Max p) (sc (oW1 + w1Len p * i)) (w1Len p) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have := w1_off hF hi
  exact ⟨⟨sptr_ok rfl (by decide), by ssep hF⟩, ⟨sptr_ok rfl (by slt hF), by ssep hF⟩,
    show ix Reg.s11 ∈ sWb2 by decide, by ssep hF, hF.sbp, rfl, by salsep⟩

theorem hbW_piece {t i : Nat} (hi : i < p.k) :
    SPiece p STK (fun σ s => IC p STK σ t p.ℓ p.ℓ p.k i s) (H1 p STK t i) (highBitsAt P (wP p i) p.γ₂ t1P) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  refine ⟨fun σ s _ h => ?_, rel_of (RelCT.exists_ fun σ => KeyGen.hb_tr hP.highBits hS (hb_m hF (σ := σ) hi)
    (P := fun x y => Two (slay2 p STK σ) sWb2 STK x y ∧
      Reduced x.mem ((slay2 p STK σ).A 0 (oP (wBase p + i))) ∧
      Reduced y.mem ((slay2 p STK σ).A 0 (oP (wBase p + i))))
      fun _ _ h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2.1, h.2.2⟩)
    fun σ₁ _ _ _ _ _ pub h₁ h₂ => ⟨σ₁, sc2_twoL pub h₁.l.k.sc h₂.l.k.sc, (h₁.w i hi).1, by
      rw [slay2_pub pub]; exact (h₂.w i hi).1⟩⟩
  have := w1_off hF hi
  unfold highBitsAt
  refine KeyGen.hb_ok hP.highBits h.l.k.sc.site hS (hb_m hF hi) (h.w i hi).1 fun s' k' hq => ?_
  refine ⟨h.keep k' (by ssep hF [icChk, ikChk, sc2Chk, yBase, yhBase, wBase, s1Base, nSec])
    (k'.cs .s5 (by decide)) (k'.cs .s7 (by decide)), ?_⟩
  have e : polyAt s.mem (lpa (slay2 p STK σ) (wP p i)) = Wv p σ (p.ℓ * t) i := (h.w i hi).2
  rw [e] at hq
  exact hq

theorem sbpW_piece {t i : Nat} (hi : i < p.k) :
    SPiece p STK (H1 p STK t i) (fun σ s => IC p STK σ t p.ℓ p.ℓ p.k (i + 1) s)
      (simpleBitPackAt P t1P (w1Max p) (sc (oW1 + w1Len p * i)) (w1Len p)) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have hw := w1_off hF hi
  have hcf : ∀ {σ x : State}, H1 p STK t i σ x → ∀ j < n,
      (coeffAt x.mem ((slay2 p STK σ).A 0 (oP 1)) j).toNat ≤ w1Max p := fun h j hj => by
    rw [natPolyIs_coeff h.2 hj]
    simp only [w1F, Vector.getElem_map]
    exact Proof.MlDsa.Sign.highBits_le hF.g2 _
  refine ⟨fun σ s _ h => ?_, rel_of (RelCT.exists_ fun σ => KeyGen.sbp_tr hP.simpleBitPack hS (sbpW_m hF (σ := σ) hi)
    (P := fun x y => Two (slay2 p STK σ) sWb2 STK x y ∧
      (∀ j < n, (coeffAt x.mem ((slay2 p STK σ).A 0 (oP 1)) j).toNat ≤ w1Max p) ∧
      (∀ j < n, (coeffAt y.mem ((slay2 p STK σ).A 0 (oP 1)) j).toNat ≤ w1Max p))
      fun _ _ h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2.1, h.2.2⟩)
    fun σ₁ _ _ _ _ _ pub h₁ h₂ => ⟨σ₁, sc2_twoL pub h₁.1.l.k.sc h₂.1.l.k.sc, hcf h₁, by
      rw [slay2_pub pub]; exact hcf h₂⟩⟩
  unfold simpleBitPackAt
  refine KeyGen.sbp_ok hP.simpleBitPack h.1.l.k.sc.site hS (sbpW_m hF hi) (hcf h) fun s' k' hq => ?_
  have I := h.1.keep k' (by ssep hF [icChk, ikChk, sc2Chk, yBase, yhBase, wBase, s1Base, nSec])
    (k'.cs .s5 (by decide)) (k'.cs .s7 (by decide))
  refine ⟨I.l, I.y, I.yh, I.w, ?_, by rw [Nat.mul_succ]; exact hw⟩
  have e : natPolyAt s.mem (lpa (slay2 p STK σ) t1P) = w1F p (Am p σ) (rppOf p σ) (p.ℓ * t) i := h.2
  rw [e] at hq
  have b2 : bytesAt s'.mem ((slay2 p STK σ).A 0 oW1 + BitVec.ofNat 64 (w1Len p * i)) (w1Len p) =
      simpleBitPack (w1F p (Am p σ) (rppOf p σ) (p.ℓ * t) i) (w1Max p) := by
    simp only [lpa, Lay.A, ix, BitVec.add_assoc, ← BitVec.ofNat_add] at hq ⊢; exact hq
  rw [Nat.mul_succ, Proof.MlKem.bytesAt_add, I.w1, b2, List.range_succ, List.flatMap_append,
    List.flatMap_singleton]

omit hP hS in
theorem ctPieces {σ s : State} (hs : Site (slay2 p STK σ) sWb2 STK s) :
    (∀ pc ∈ ([⟨.s9, 0, 64⟩, ⟨.s11, oW1, p.k * w1Len p⟩] : List Impl.MlKem.RISCV64.Piece),
      PieceOk (hashLay (slay2 p STK σ) s Kmu) ix s false pc) ∧
    PieceOk (hashLay (slay2 p STK σ) s Kmu) ix s true (⟨.s11, oCT, cLen p⟩ : Impl.MlKem.RISCV64.Piece) := by
  have hk := hF.k
  obtain ⟨w1a, w1b⟩ := hF.w1
  refine ⟨fun pc hpc => ?_, pieceS hs rfl (show oCT < 32768 by decide)
    (show cLen p < 2048 by rcases hF.ct with e | e | e <;> omega_using [e])
    (show 0 < cLen p by rcases hF.ct with e | e | e <;> omega_using [e])
    (by rcases hF.ct with e | e | e <;> ssep hF [hashLay, Lay.size, e]) (.inl rfl)
    fun _ => show ix Reg.s11 ∈ sWb2 by decide⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpc
  rcases hpc with rfl | rfl
  · exact pieceS hs rfl (show (0 : Nat) < 32768 by decide) (show 64 < 2048 by decide) (by decide)
      (by ssep hF [hashLay, Lay.size]) (.inr rfl) fun h => absurd h (by decide)
  · exact pieceS hs rfl (show oW1 < 32768 by decide) (show p.k * w1Len p < 2048 by omega_using [w1a]) w1b
      (by rcases hF.w1l with e | ⟨e, _⟩ <;> ssep hF [hashLay, Lay.size, e]) (.inl rfl) fun h => absurd h (by decide)

omit hP hS in
theorem ctHash_piece {t : Nat} :
    SPiece p STK (fun σ s => IC p STK σ t p.ℓ p.ℓ p.k p.k s) (ICd p STK t)
      (hash 136 0x1f [⟨.s9, 0, 64⟩, ⟨.s11, oW1, p.k * w1Len p⟩] [⟨.s11, oCT, cLen p⟩]) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  refine ⟨fun σ s _ h => ?_, rel_of (RelCT.exists_ fun σ => hashS_tr kmu (rate := 136) (sfx := 0x1f) (by decide)
    (by decide) (by simp) (fun s hs => (ctPieces hF (σ := σ) hs).1) (fun s hs => (ctPieces hF hs).2) fun _ _ h => h)
    fun σ₁ _ _ _ _ _ pub h₁ h₂ => ⟨σ₁, sc2_twoL pub h₁.l.k.sc h₂.l.k.sc⟩⟩
  have hs := h.l.k.sc.site
  obtain ⟨hin, hq⟩ := ctPieces hF hs
  have hc : cLen p ≤ 64 := by rcases hF.ct with e | e | e <;> omega_using [e]
  have hb := h.w1b
  refine WP.mono (hashS hs kmu (rate := 136) (sfx := 0x1f) (by decide) (by decide) (by simp) hin hq)
    fun s' ⟨k', o'⟩ => ⟨h.keep k' (by ssep hF [icChk, ikChk, sc2Chk, yBase, yhBase, wBase, s1Base, nSec])
      (k'.cs .s5 (by decide)) (k'.cs .s7 (by decide)), ?_⟩
  have o₃ : bytesAt s'.mem ((slay2 p STK σ).A 0 oCT) (cLen p) = _ := o'
  rw [o₃]
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, Lay.pb,
    hashLay_ptr _ _ _ (ix_ne1 _)]
  have e1 : bytesAt s.mem ((slay2 p STK σ).ptr (ix Reg.s9) + BitVec.ofNat 64 0) 64 = muOf σ := h.l.k.sc.mu
  have e2 : bytesAt s.mem ((slay2 p STK σ).ptr (ix Reg.s11) + BitVec.ofNat 64 oW1) (p.k * w1Len p) =
      w1Encode p ((List.range p.k).map (w1F p (Am p σ) (rppOf p σ) (p.ℓ * t))) := by
    rw [Nat.mul_comm]
    exact h.w1.trans (by simp only [w1Encode, List.flatMap_map])
  rw [e1, e2, shake31]
  exact (Proof.MlKem.shake256_eq _ _).symm

theorem w1R_piece {t i : Nat} (hi : i < p.k) :
    SPiece p STK (fun σ s => IC p STK σ t p.ℓ p.ℓ p.k i s) (fun σ s => IC p STK σ t p.ℓ p.ℓ p.k (i + 1) s)
      (w1R P p i) :=
  (hbW_piece hP hF hS hi).seq (sbpW_piece hP hF hS hi)

/-- The commitment of iteration `t`. -/
theorem commit_piece {t : Nat} :
    SPiece p STK (IL p STK · t) (ICd p STK t) (commit P p) := by
  unfold commit
  refine Piece.mono ((Piece.mono (Piece.seqR (I := fun r σ s => IC p STK σ t r r 0 0 s) p.ℓ 0
    fun r _ hr => maskR_piece hP hF hS (by omega_using [hr])) (fun _ _ _ h => h) fun _ _ _ h => by simpa using h).seq
    ((Piece.mono (Piece.seqR (I := fun i σ s => IC p STK σ t p.ℓ p.ℓ i 0 s) p.k 0
      fun i _ hi => rowW_piece hP hF hS (by omega_using [hi])) (fun _ _ _ h => h) fun _ _ _ h => by simpa using h).seq
    ((Piece.mono (Piece.seqR (I := fun i σ s => IC p STK σ t p.ℓ p.ℓ p.k i s) p.k 0
      fun i _ hi => w1R_piece hP hF hS (by omega_using [hi])) (fun _ _ _ h => h) fun _ _ _ h => by simpa using h).seq
      (ctHash_piece hF)))) (fun σ s _ h => ?_) fun _ _ _ h => h
  exact ⟨h, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _),
    fun _ h => absurd h (Nat.not_lt_zero _), by simp only [Nat.mul_zero, List.range_zero, List.flatMap_nil]; rfl, by simp⟩

end

end VG.Proof.MlDsa.RISCV64.Sign

end

end

/-!
# ML-DSA signing on RISC-V: calls of the primitives, as pieces

Once `sig` is in `s8` (`slay2`), each call of a polynomial primitive on
slots of `scratch` as a piece (`SPiece`), for any invariant `I` that implies
`SC2` and that the call keeps: its correctness from the call's contract, and
its constant time from the callee's (`callV_tr`), as the checks and the
signature use them.
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Sign

open VG VG.RISCV64 VG.Proof.MlKem.RISCV64
open VG.Proof.MlDsa.RISCV64.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of polyIs_keepW Regs2
  copyS zx and24_ok Callee)
open VG.Impl.MlDsa.RISCV64.Sign
open VG.Impl.MlDsa.RISCV64.KeyGen (callAt and24)
open VG.Impl.MlKem.RISCV64 (copy)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable {P : Prims} {S : Nat} (hP : SPrimsOk P S) {p : Params} {STK : Nat} (hS : S ≤ STK)
  {I : State → State → Prop} (hI : ∀ σ s, I σ s → SC2 p STK σ s)

/-- Slot `x` of `scratch`. -/
abbrev SL (p : Params) (STK : Nat) (σ : State) (x : Nat) : Addr := (slay2 p STK σ).A 0 (oP x)

theorem SL_pub {σ₁ σ₂ : State} (pub : sPub p σ₁ σ₂) (x : Nat) : SL p STK σ₁ x = SL p STK σ₂ x := by
  simp only [SL, slay2_pub pub]

include hP hS hI

theorem mulP_piece {x a b : Nat} (m : ∀ σ, KeyGen.MulOk (slay2 p STK σ) sWb2 (pS x) (pS a) (pS b))
    {F G : State → Poly} (hf : ∀ σ s, I σ s → PolyIs s.mem (SL p STK σ a) (F σ))
    (hg : ∀ σ s, I σ s → PolyIs s.mem (SL p STK σ b) (G σ))
    (hk : ∀ σ s s', I σ s → Kept ((slay2 p STK σ).RL [tri (pS x) 1024, (1, 0, STK)]) s s' → I σ s') :
    SPiece p STK I (fun σ s => I σ s ∧ PolyIs s.mem (SL p STK σ x) (multiplyNTT (F σ) (G σ)))
      (mulAt P (pS x) (pS a) (pS b)) := by
  refine ⟨fun σ s _ h => ?_, rel_of (RelCT.exists_ fun σ => KeyGen.mul_tr hP.mul hS (m σ)
    (P := fun x y => Two (slay2 p STK σ) sWb2 STK x y ∧ Reduced x.mem (SL p STK σ a) ∧ Reduced x.mem (SL p STK σ b) ∧
      Reduced y.mem (SL p STK σ a) ∧ Reduced y.mem (SL p STK σ b)) fun _ _ h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩)
    fun σ₁ _ _ _ _ _ pub h₁ h₂ => ⟨σ₁, sc2_twoL pub (hI _ _ h₁) (hI _ _ h₂), (hf _ _ h₁).1, (hg _ _ h₁).1,
      by rw [SL_pub pub]; exact (hf _ _ h₂).1, by rw [SL_pub pub]; exact (hg _ _ h₂).1⟩⟩
  unfold mulAt
  refine KeyGen.mul_ok hP.mul (hI _ _ h).site hS (m σ) (hf _ _ h).1 (hg _ _ h).1 fun s' k' hq => ⟨hk _ _ _ h k', ?_⟩
  have e1 : polyAt s.mem (lpa (slay2 p STK σ) (pS a)) = F σ := (hf _ _ h).2
  have e2 : polyAt s.mem (lpa (slay2 p STK σ) (pS b)) = G σ := (hg _ _ h).2
  rw [e1, e2] at hq
  exact hq

omit hP in
theorem ipP_piece {name : String} {code : Prog isa} {t : Poly → Poly}
    (hc : Callee code (fun stk => inPlaceContract RISCV64.abi t stk) S) {x : Nat}
    (m : ∀ σ, KeyGen.IpOk (slay2 p STK σ) sWb2 (pS x) (sc oPS)) {F : State → Poly}
    (hk : ∀ σ s s', I σ s → Kept ((slay2 p STK σ).RL [tri (pS x) 1024, tri (sc oPS) 1024, (1, 0, STK)]) s s' →
      I σ s') :
    SPiece p STK (fun σ s => I σ s ∧ PolyIs s.mem (SL p STK σ x) (F σ))
      (fun σ s => I σ s ∧ PolyIs s.mem (SL p STK σ x) (t (F σ))) (callAt name code [(.a0, .ptr (pS x)), (.a1, .ptr (sc oPS))]) := by
  refine ⟨fun σ s _ ⟨h, hx⟩ => ?_, rel_of (RelCT.exists_ fun σ => KeyGen.ip_tr (t := t) hc hS (m σ)
    (P := fun x' y => Two (slay2 p STK σ) sWb2 STK x' y ∧ Reduced x'.mem (SL p STK σ x) ∧ Reduced y.mem (SL p STK σ x))
      fun _ _ h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2.1, h.2.2⟩)
    fun σ₁ _ _ _ _ _ pub h₁ h₂ => ⟨σ₁, sc2_twoL pub (hI _ _ h₁.1) (hI _ _ h₂.1), h₁.2.1, by
      rw [SL_pub pub]; exact h₂.2.1⟩⟩
  refine KeyGen.ip_ok (t := t) hc (hI _ _ h).site hS (m σ) hx.1 fun s' k' hq => ⟨hk _ _ _ h k', ?_⟩
  have e : polyAt s.mem (lpa (slay2 p STK σ) (pS x)) = F σ := hx.2
  rw [e] at hq
  exact hq

theorem addP_piece {f g : Nat} (m : ∀ σ, KeyGen.AddOk (slay2 p STK σ) sWb2 (pS f) (pS g)) {F G : State → Poly}
    (hg : ∀ σ s, I σ s → PolyIs s.mem (SL p STK σ g) (G σ))
    (hk : ∀ σ s s', I σ s → Kept ((slay2 p STK σ).RL [tri (pS f) 1024, (1, 0, STK)]) s s' → I σ s') :
    SPiece p STK (fun σ s => I σ s ∧ PolyIs s.mem (SL p STK σ f) (F σ))
      (fun σ s => I σ s ∧ PolyIs s.mem (SL p STK σ f) (add (F σ) (G σ))) (addAt P (pS f) (pS g)) := by
  refine ⟨fun σ s _ ⟨h, hf⟩ => ?_, rel_of (RelCT.exists_ fun σ => KeyGen.add_tr hP.add hS (m σ)
    (P := fun x y => Two (slay2 p STK σ) sWb2 STK x y ∧ Reduced x.mem (SL p STK σ f) ∧ Reduced x.mem (SL p STK σ g) ∧
      Reduced y.mem (SL p STK σ f) ∧ Reduced y.mem (SL p STK σ g)) fun _ _ h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩)
    fun σ₁ _ _ _ _ _ pub h₁ h₂ => ⟨σ₁, sc2_twoL pub (hI _ _ h₁.1) (hI _ _ h₂.1), h₁.2.1, (hg _ _ h₁.1).1,
      by rw [SL_pub pub]; exact h₂.2.1, by rw [SL_pub pub]; exact (hg _ _ h₂.1).1⟩⟩
  unfold addAt
  refine KeyGen.add_ok hP.add (hI _ _ h).site hS (m σ) hf.1 (hg _ _ h).1 fun s' k' hq => ⟨hk _ _ _ h k', ?_⟩
  have e1 : polyAt s.mem (lpa (slay2 p STK σ) (pS f)) = F σ := hf.2
  have e2 : polyAt s.mem (lpa (slay2 p STK σ) (pS g)) = G σ := (hg _ _ h).2
  rw [e1, e2] at hq
  exact hq

theorem subP_piece {f g : Nat} (m : ∀ σ, KeyGen.AddOk (slay2 p STK σ) sWb2 (pS f) (pS g)) {F G : State → Poly}
    (hg : ∀ σ s, I σ s → PolyIs s.mem (SL p STK σ g) (G σ))
    (hk : ∀ σ s s', I σ s → Kept ((slay2 p STK σ).RL [tri (pS f) 1024, (1, 0, STK)]) s s' → I σ s') :
    SPiece p STK (fun σ s => I σ s ∧ PolyIs s.mem (SL p STK σ f) (F σ))
      (fun σ s => I σ s ∧ PolyIs s.mem (SL p STK σ f) (sub (F σ) (G σ))) (subAt P (pS f) (pS g)) := by
  refine ⟨fun σ s _ ⟨h, hf⟩ => ?_, rel_of (RelCT.exists_ fun σ => KeyGen.sub_tr hP.sub hS (m σ)
    (P := fun x y => Two (slay2 p STK σ) sWb2 STK x y ∧ Reduced x.mem (SL p STK σ f) ∧ Reduced x.mem (SL p STK σ g) ∧
      Reduced y.mem (SL p STK σ f) ∧ Reduced y.mem (SL p STK σ g)) fun _ _ h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩)
    fun σ₁ _ _ _ _ _ pub h₁ h₂ => ⟨σ₁, sc2_twoL pub (hI _ _ h₁.1) (hI _ _ h₂.1), h₁.2.1, (hg _ _ h₁.1).1,
      by rw [SL_pub pub]; exact h₂.2.1, by rw [SL_pub pub]; exact (hg _ _ h₂.1).1⟩⟩
  unfold subAt
  refine KeyGen.sub_ok hP.sub (hI _ _ h).site hS (m σ) hf.1 (hg _ _ h).1 fun s' k' hq => ⟨hk _ _ _ h k', ?_⟩
  have e1 : polyAt s.mem (lpa (slay2 p STK σ) (pS f)) = F σ := hf.2
  have e2 : polyAt s.mem (lpa (slay2 p STK σ) (pS g)) = G σ := (hg _ _ h).2
  rw [e1, e2] at hq
  exact hq

/-- The call of `vg_mldsa_norm_lt`, its result in `a0`. -/
theorem normP_piece {f B : Nat} (pf : ∀ σ, PtrIn (slay2 p STK σ) (pS f) 1024) (af : KeyGen.AlS (pS f))
    (hfs : ∀ σ, sepAll (slay2 p STK σ).sizes (0, oP f, 1024) [(1, 0, STK)] = true) (hB : B < 2 ^ 31 - 2048) {F : State → Poly}
    (hk : ∀ σ s s', I σ s → Kept ((slay2 p STK σ).RL [(1, 0, STK)]) s s' → I σ s') :
    SPiece p STK (fun σ s => I σ s ∧ PolyIs s.mem (SL p STK σ f) (F σ))
      (fun σ s => (I σ s ∧ PolyIs s.mem (SL p STK σ f) (F σ)) ∧
        (s.gpr .a0).setWidth 32 = (if normRq [F σ] < B then 1 else 0))
      (callAt "vg_mldsa_norm_lt" P.normLt (KeyGen.nlArgs (pS f) B)) := by
  refine ⟨fun σ s _ ⟨h, hf⟩ => ?_, rel_of (RelCT.exists_ fun σ => KeyGen.nl_tr hP.normLt hS (pf σ) af hB
    (P := fun x y => Two (slay2 p STK σ) sWb2 STK x y ∧ Reduced x.mem (SL p STK σ f) ∧ Reduced y.mem (SL p STK σ f))
      fun _ _ h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2.1, h.2.2⟩)
    fun σ₁ _ _ _ _ _ pub h₁ h₂ => ⟨σ₁, sc2_twoL pub (hI _ _ h₁.1) (hI _ _ h₂.1), h₁.2.1, by
      rw [SL_pub pub]; exact h₂.2.1⟩⟩
  refine KeyGen.nl_ok hP.normLt (hI _ _ h).site hS (pf σ) af hB hf.1 fun s' k' hq => ⟨⟨hk _ _ _ h k', ?_⟩, ?_⟩
  · exact polyIs_keepW (hI _ _ h).site.ok k'.frame (hfs σ) (by decide) rfl hf
  · have e : polyAt s.mem (lpa (slay2 p STK σ) (pS f)) = F σ := hf.2
    rw [e] at hq
    exact hq

theorem lbP_piece {r o g2 : Nat} (m : ∀ σ, KeyGen.BitsOk (slay2 p STK σ) sWb2 (pS r) g2 (pS o)) {F : State → Poly}
    (hr : ∀ σ s, I σ s → PolyIs s.mem (SL p STK σ r) (F σ))
    (hk : ∀ σ s s', I σ s → Kept ((slay2 p STK σ).RL [tri (pS o) 1024, (1, 0, STK)]) s s' → I σ s') :
    SPiece p STK I (fun σ s => I σ s ∧ PolyIs s.mem (SL p STK σ o) ((F σ).map fun c => ofInt (lowBits g2 c)))
      (lowBitsAt P (pS r) g2 (pS o)) := by
  refine ⟨fun σ s _ h => ?_, rel_of (RelCT.exists_ fun σ => KeyGen.lb_tr hP.lowBits hS (m σ)
    (P := fun x y => Two (slay2 p STK σ) sWb2 STK x y ∧ Reduced x.mem (SL p STK σ r) ∧ Reduced y.mem (SL p STK σ r))
      fun _ _ h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2.1, h.2.2⟩)
    fun σ₁ _ _ _ _ _ pub h₁ h₂ => ⟨σ₁, sc2_twoL pub (hI _ _ h₁) (hI _ _ h₂), (hr _ _ h₁).1, by
      rw [SL_pub pub]; exact (hr _ _ h₂).1⟩⟩
  unfold lowBitsAt
  refine KeyGen.lb_ok hP.lowBits (hI _ _ h).site hS (m σ) (hr _ _ h).1 fun s' k' hq => ⟨hk _ _ _ h k', ?_⟩
  have e : polyAt s.mem (lpa (slay2 p STK σ) (pS r)) = F σ := (hr _ _ h).2
  rw [e] at hq
  exact hq

end

/-! ## `s4 ← s4 ∧ a0` -/

/-- `1` if `a`, else `0`. -/
abbrev bit (a : Prop) [Decidable a] : BitVec 64 := if a then 1 else 0

theorem bit_and {a b : Prop} [Decidable a] [Decidable b] {x : BitVec 64}
    (hx : x.setWidth 32 = if b then 1 else 0) : bit a &&& zx x = bit (a ∧ b) := by
  by_cases ha : a <;> by_cases hb : b <;> simp only [bit, zx, hx, ha, hb, ite_true, ite_false, and_true,
    and_false] <;> decide

theorem bit_congr {a b : Prop} [Decidable a] [Decidable b] (h : a ↔ b) : bit a = bit b := by
  by_cases ha : a
  · rw [show bit a = 1 from VG.Proof.MlDsa.KeyGen.ifp ha _ _, show bit b = 1 from VG.Proof.MlDsa.KeyGen.ifp (h.mp ha) _ _]
  · rw [show bit a = 0 from VG.Proof.MlDsa.KeyGen.ifn ha _ _,
      show bit b = 0 from VG.Proof.MlDsa.KeyGen.ifn (fun hb => ha (h.mpr hb)) _ _]

theorem forall_lt_succ {Q : Nat → Prop} {r : Nat} : ((∀ j < r, Q j) ∧ Q r) ↔ ∀ j < r + 1, Q j :=
  ⟨fun ⟨h1, h2⟩ j hj => by
    rcases (by omega_using [hj] : j < r ∨ j = r) with hj | rfl
    exacts [h1 j hj, h2], fun h => ⟨fun j hj => h j (by omega_using [hj]), h r (by omega_using [])⟩⟩

section
variable {p : Params} {STK : Nat} {J J' : State → State → Prop} (hJ : ∀ σ s, J σ s → SC2 p STK σ s)
include hJ

/-- `and24`, from an invariant `J` that implies `SC2`. -/
theorem and24_piece
    (h : ∀ σ s s', J σ s → Regs2 s s' → s'.gpr .s4 = s.gpr .s4 &&& zx (s.gpr .a0) → J' σ s') :
    SPiece p STK J J' (.block and24) :=
  ⟨fun σ s _ hs => WP.mono (and24_ok s) fun s' ⟨_, e24, r⟩ => h σ s s' hs r e24,
    srel2 hJ and24_taint⟩

end

end VG.Proof.MlDsa.RISCV64.Sign

end

end

/-!
# ML-DSA signing on RISC-V: the checks of an iteration

As on PPC64LE (`Proof/MlDsa/PPC64LE/Sign/PhaseK.lean`), once `SampleInBall`
succeeded (`KB`): `ĉ = NTT(c)`, and each check of the iteration, their
results ANDed into `s4`: the norm of each `z[r]` (`IZ`), of each `r₀[i]`
(`IQ`) and of each `ct₀[i]`, with each hint `h[i]` and the number of its 1s
summed in `s6` (`IH`), and that sum against `ω`; so `s4` is 1 exactly when
the iteration passes (`KO`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Sign

open VG VG.RISCV64 VG.Proof.MlKem.RISCV64
open VG.Proof.MlDsa.RISCV64.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of polyIs_keepW bytes_keepW
  Regs2 zx copyS)
open VG.Impl.MlDsa.RISCV64.Sign
open VG.Impl.MlDsa.RISCV64.KeyGen (callAt and24 seqR)
open VG.Impl.MlKem.RISCV64 (copy)
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
  fun j h1 h2 => polyIs_keepW hL hf (sepAll_sub h (by unfold oP; omega_using [h1]) (by unfold oP; omega_using [h2])) h0 rfl (hp j h1 h2)

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
  obtain hct : cLen p ≤ 2 ^ 64 := by rcases hF.ct with e | e | e <;> omega_using [e]
  exact ⟨⟨h.l.k.keep hk c1, (hk.cs .s7 (by decide)).trans h.l.s7, (hk.cs .s5 (by decide)).trans h.l.s5,
    h.l.t_lt, h.l.rej⟩, by rw [bytes_keepW hL hk.frame c2 (by decide) hct]; exact h.ct,
    polyIs_keepW hL hk.frame c3 (by decide) rfl h.c, h.some⟩

theorem IK.regs2 {p : Params} {STK : Nat} {σ s s' : State} (h : IK p STK σ s) (r : Regs2 s s') : IK p STK σ s' :=
  ⟨h.sc.regs2 r, h.ok, by rw [r.mem]; exact h.A, by rw [r.mem]; exact h.rpp, by rw [r.mem]; exact h.s1,
    by rw [r.mem]; exact h.s2, by rw [r.mem]; exact h.t0⟩

theorem IL.regs2 {p : Params} {STK : Nat} {σ : State} {t : Nat} {s s' : State} (h : IL p STK σ t s) (r : Regs2 s s') :
    IL p STK σ t s' :=
  ⟨h.k.regs2 r, by rw [r.gpr .s7 (by decide) (by decide)]; exact h.s7,
    by rw [r.gpr .s5 (by decide) (by decide)]; exact h.s5, h.t_lt, h.rej⟩

theorem KB.regs2 {p : Params} {STK : Nat} {σ : State} {t : Nat} {s s' : State} (h : KB p STK σ t s) (r : Regs2 s s') :
    KB p STK σ t s' :=
  ⟨h.l.regs2 r, by rw [r.mem]; exact h.ct, by rw [r.mem]; exact h.c, h.some⟩

theorem SC2.of_eq {p : Params} {STK : Nat} {σ s s' : State} (h : SC2 p STK σ s)
    (hg : ∀ r, r ≠ .a0 → r ≠ .s4 → r ≠ .s6 → s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) : SC2 p STK σ s' := by
  have hs := h.site
  refine ⟨⟨hs.ok, hs.len, hs.w0, hs.w1, hs.sz0, hs.sz1, by rw [hsp]; exact hs.p1, hs.s1168, by rw [hsp]; exact hs.spk, by rw [hsp]; exact hs.al, hs.al0,
    by rw [hg .s11 (by decide) (by decide) (by decide)]; exact hs.s11,
    by rw [hg .s10 (by decide) (by decide) (by decide)]; exact hs.s10,
    by rw [hg .s9 (by decide) (by decide) (by decide)]; exact hs.s9,
    by rw [hg .s8 (by decide) (by decide) (by decide)]; exact hs.s8,
    by rw [hwr]; exact hs.cw, by rw [hwr, hrd]; exact hs.cr⟩, hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp,
    fun r hr hs' => ?_, by rw [hm]; exact h.sav, by rw [hm]; exact h.sk, by rw [hm]; exact h.mu, h.pre,
    by rw [hg .s3 (by decide) (by decide) (by decide)]; exact h.s3, by rw [hm]; exact h.cache⟩
  have : r ≠ .a0 ∧ r ≠ .s4 ∧ r ≠ .s6 := ⟨fun e => by subst e; simp [preserved] at hr,
    fun e => by subst e; simp [savedTop] at hs', fun e => by subst e; simp [savedTop] at hs'⟩
  rw [hg r this.1 this.2.1 this.2.2]; exact h.pres r hr hs'

theorem KB.of_eq {p : Params} {STK : Nat} {σ : State} {t : Nat} {s s' : State} (h : KB p STK σ t s)
    (hg : ∀ r, r ≠ .a0 → r ≠ .s4 → r ≠ .s6 → s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) : KB p STK σ t s' :=
  ⟨⟨⟨h.l.k.sc.of_eq hg hm hrd hwr hsp, h.l.k.ok, by rw [hm]; exact h.l.k.A, by rw [hm]; exact h.l.k.rpp,
    by rw [hm]; exact h.l.k.s1, by rw [hm]; exact h.l.k.s2, by rw [hm]; exact h.l.k.t0⟩,
    by rw [hg .s7 (by decide) (by decide) (by decide)]; exact h.l.s7,
    by rw [hg .s5 (by decide) (by decide) (by decide)]; exact h.l.s5,
    h.l.t_lt, h.l.rej⟩, by rw [hm]; exact h.ct, by rw [hm]; exact h.c, h.some⟩

/-! ## `z` -/

/-- The checks of `z[j]` for `j < nz`; `y[j]` for `ys ≤ j < ℓ`, `s6 = 0`. -/
structure IZ (p : Params) (STK : Nat) (σ : State) (t nz ys : Nat) (s : State) : Prop where
  b : KB p STK σ t s
  z : ∀ r < nz, PolyIs s.mem (SL p STK σ (yBase p + r)) (Zv p σ (p.ℓ * t) r)
  y : ∀ r, ys ≤ r → r < p.ℓ → PolyIs s.mem (SL p STK σ (yBase p + r)) (Yv p σ (p.ℓ * t) r)
  w : ∀ i < p.k, PolyIs s.mem (SL p STK σ (wBase p + i)) (Wv p σ (p.ℓ * t) i)
  s6 : s.gpr .s6 = 0
  s4 : s.gpr .s4 = bit (∀ j < nz, normRq [Zv p σ (p.ℓ * t) j] < p.γ₁ - p.β)

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
  obtain h0 : 0 ∈ sWb2 := by decide
  exact ⟨h.b.keep hF hk c1, fun r hr => famR_keep hL h0 hk.frame c2 (fun j _ hj => h.z j hj) r (Nat.zero_le _) hr,
    famR_keep hL h0 hk.frame c3 h.y, fun i hi => famR_keep hL h0 hk.frame c4 (fun j _ hj => h.w j hj) i
      (Nat.zero_le _) hi, (hk.cs .s6 (by decide)).trans h.s6, (hk.cs .s4 (by decide)).trans h.s4⟩

theorem IZ.weak {p : Params} {STK : Nat} {σ : State} {t r : Nat} {s : State} (h : IZ p STK σ t r r s)
    (hr : r < p.ℓ) : IZ p STK σ t r (r + 1) s ∧ PolyIs s.mem (SL p STK σ (yBase p + r)) (Yv p σ (p.ℓ * t) r) :=
  ⟨⟨h.b, h.z, fun j hj hj' => h.y j (by omega_using [hj]) hj', h.w, h.s6, h.s4⟩, h.y r (Nat.le_refl _) hr⟩

/-! ## `r₀` -/

/-- The checks of `r₀[j]` for `j < nr` (`w[j]` is `w[j] - cs₂[j]`); `w[j]` for `ws ≤ j < k`; `z` checked, `s6 = 0`. -/
structure IQ (p : Params) (STK : Nat) (σ : State) (t nr ws : Nat) (s : State) : Prop where
  b : KB p STK σ t s
  z : ∀ r < p.ℓ, PolyIs s.mem (SL p STK σ (yBase p + r)) (Zv p σ (p.ℓ * t) r)
  w' : ∀ i < nr, PolyIs s.mem (SL p STK σ (wBase p + i)) (W'v p σ (p.ℓ * t) i)
  w : ∀ i, ws ≤ i → i < p.k → PolyIs s.mem (SL p STK σ (wBase p + i)) (Wv p σ (p.ℓ * t) i)
  s6 : s.gpr .s6 = 0
  s4 : s.gpr .s4 = bit (ZOk p σ (p.ℓ * t) ∧ ∀ j < nr, normRq [R0v p σ (p.ℓ * t) j] < p.γ₂ - p.β)

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
  obtain h0 : 0 ∈ sWb2 := by decide
  exact ⟨h.b.keep hF hk c1, fun r hr => famR_keep hL h0 hk.frame c2 (fun j _ hj => h.z j hj) r (Nat.zero_le _) hr,
    fun i hi => famR_keep hL h0 hk.frame c3 (fun j _ hj => h.w' j hj) i (Nat.zero_le _) hi,
    famR_keep hL h0 hk.frame c4 h.w, (hk.cs .s6 (by decide)).trans h.s6, (hk.cs .s4 (by decide)).trans h.s4⟩

theorem IQ.weak {p : Params} {STK : Nat} {σ : State} {t i : Nat} {s : State} (h : IQ p STK σ t i i s)
    (hi : i < p.k) : IQ p STK σ t i (i + 1) s ∧ PolyIs s.mem (SL p STK σ (wBase p + i)) (Wv p σ (p.ℓ * t) i) :=
  ⟨⟨h.b, h.z, h.w', fun j hj hj' => h.w j (by omega_using [hj]) hj', h.s6, h.s4⟩, h.w i (Nat.le_refl _) hi⟩

theorem IZ.iq {p : Params} {STK : Nat} {σ : State} {t : Nat} {s : State} (h : IZ p STK σ t p.ℓ p.ℓ s) :
    IQ p STK σ t 0 0 s :=
  ⟨h.b, h.z, fun _ h => absurd h (Nat.not_lt_zero _), fun i _ hi => h.w i hi, h.s6,
    by rw [h.s4]; exact bit_congr ⟨fun h => ⟨h, fun _ h => absurd h (Nat.not_lt_zero _)⟩, fun h => h.1⟩⟩

/-! ## Hints and their 1s -/

theorem zq_sub_sub (a : Zq) : a - a - a = -a := by
  apply Fin.ext
  have ha := a.isLt
  simp only [Fin.sub_def, Fin.neg_def, q] at *
  omega_using []

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
    omega_arith

/-- A hint kept by a part that writes apart from it. -/
theorem hintIs_keepW {L : Lay} {Wb : List Nat} (hL : OkW L Wb) {W : List (Nat × Nat × Nat)} {m m' : Mem}
    (hf : Frame (L.RL W) m m') {i o : Nat} (h : sepAll L.sizes (i, o, 1024 * 1) W = true) (hw : i ∈ Wb)
    {hh : List (Vector Bool Spec.MlDsa.n)} (hi : HintIs m (L.A i o) 1 hh) : HintIs m' (L.A i o) 1 hh :=
  Proof.MlDsa.Verify.hintIs_frame hf (by decide) (KeyGen.keepD hL h hw) hi

/-- The checks of `ct₀[j]` for `j < nc`; for `j < nh`, `w[j]` is `w[j] - cs₂[j] + ct₀[j]` and `h[j]` is the
hint, the number of their 1s in `s6`; `w[j]` is `w[j] - cs₂[j]` for `ws ≤ j < k`. -/
structure IH (p : Params) (STK : Nat) (σ : State) (t nc nh ws : Nat) (s : State) : Prop where
  b : KB p STK σ t s
  z : ∀ r < p.ℓ, PolyIs s.mem (SL p STK σ (yBase p + r)) (Zv p σ (p.ℓ * t) r)
  w'' : ∀ i < nh, PolyIs s.mem (SL p STK σ (wBase p + i)) (W''v p σ (p.ℓ * t) i)
  w' : ∀ i, ws ≤ i → i < p.k → PolyIs s.mem (SL p STK σ (wBase p + i)) (W'v p σ (p.ℓ * t) i)
  h : ∀ i < nh, HintIs s.mem (SL p STK σ (5 + i)) 1 [Hv p σ (p.ℓ * t) i]
  s6 : s.gpr .s6 = BitVec.ofNat 64 (onesSum (Hv p σ (p.ℓ * t)) nh)
  s4 : s.gpr .s4 = bit ((ZOk p σ (p.ℓ * t) ∧ R0Ok p σ (p.ℓ * t)) ∧
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
  obtain h0 : 0 ∈ sWb2 := by decide
  exact ⟨h.b.keep hF hk c1, fun r hr => famR_keep hL h0 hk.frame c2 (fun j _ hj => h.z j hj) r (Nat.zero_le _) hr,
    fun i hi => famR_keep hL h0 hk.frame c3 (fun j _ hj => h.w'' j hj) i (Nat.zero_le _) hi,
    famR_keep hL h0 hk.frame c4 h.w',
    fun i hi => hintIs_keepW hL hk.frame (sepAll_sub c5 (by unfold oP; omega_using []) (by unfold oP; omega_using [hi])) h0 (h.h i hi),
    (hk.cs .s6 (by decide)).trans h.s6, (hk.cs .s4 (by decide)).trans h.s4⟩

theorem IH.weak {p : Params} {STK : Nat} {σ : State} {t i : Nat} {s : State} (h : IH p STK σ t i i i s)
    (hi : i < p.k) :
    IH p STK σ t i i (i + 1) s ∧ PolyIs s.mem (SL p STK σ (wBase p + i)) (W'v p σ (p.ℓ * t) i) :=
  ⟨⟨h.b, h.z, h.w'', fun j hj hj' => h.w' j (by omega_using [hj]) hj', h.h, h.s6, h.s4⟩, h.w' i (Nat.le_refl _) hi⟩

theorem IQ.ih {p : Params} {STK : Nat} {σ : State} {t : Nat} {s : State} (h : IQ p STK σ t p.k p.k s) :
    IH p STK σ t 0 0 0 s :=
  ⟨h.b, h.z, fun _ h => absurd h (Nat.not_lt_zero _), fun i _ hi => h.w' i hi, fun _ h => absurd h (Nat.not_lt_zero _),
    by rw [h.s6]; rfl,
    by rw [h.s4]; exact bit_congr ⟨fun h => ⟨h, fun _ h => absurd h (Nat.not_lt_zero _)⟩, fun h => h.1⟩⟩

/-- The block after `vg_mldsa_make_hint`: its result added to `s6`. -/
theorem onesAdd_ok (s : State) :
    WP isa (.block [.shift .sll .d .a0 .a0 32, .shift .srl .d .a0 .a0 32, .add .s6 .s6 .a0]) s fun s' =>
      s'.gpr .s6 = s.gpr .s6 + zx (s.gpr .a0) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      ∀ r, r ≠ .a0 → r ≠ .s6 → s'.gpr r = s.gpr r := by
  mrun []
  refine ⟨by rw [KeyGen.zx_shift], fun r h3 h26 => ?_⟩
  simp only [h3, h26, ite_false]

/-- `ssep`, with the slots and checks of the signing loop. -/
syntax "csep " term:max : tactic
macro_rules
  | `(tactic| csep $hF) => `(tactic| ssep $hF [icChk, izChk, iqChk, ihChk, kbChk, ikChk, sc2Chk, yBase, yhBase, wBase, s1Base, s2Base,
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
  obtain hk' := hF.k; have hl := hF.l; have hkl := hF.kl
  exact ⟨h.1.keep hF hk (by csep hF),
    polyIs_keepW h.1.b.l.k.sc.site.ok hk.frame (by csep hF) (by decide) rfl h.2⟩

theorem zR_piece {t r : Nat} (hr : r < p.ℓ) :
    SPiece p STK (fun σ s => IZ p STK σ t r r s) (fun σ s => IZ p STK σ t (r + 1) (r + 1) s) (zR P p r) := by
  obtain hk' := hF.k; have hl := hF.l; have hkl := hF.kl
  obtain hza : ∀ σ s, ZA p STK t r σ s → SC2 p STK σ s := fun _ _ h => h.1.b.l.k.sc
  -- `T1 ← NTT⁻¹(ĉ ŝ₁[r])`
  obtain p1 := mulP_piece hP hS hza (x := 1) (a := 0) (b := s1Base p + r)
    (fun σ => ⟨⟨sptr_ok rfl (by decide), by csep hF⟩, ⟨sptr_ok rfl (by decide), by csep hF⟩,
      ⟨sptr_ok rfl (by clt hF), by csep hF⟩, show ix Reg.s11 ∈ sWb2 by decide, by csep hF, by csep hF, by salsep, by salsep, by salsep⟩)
    (F := fun σ => chF (cV p σ (p.ℓ * t))) (G := fun σ => S1v p σ r)
    (fun _ _ h => h.1.b.c) (fun _ _ h => h.1.b.l.k.s1 r hr)
    (fun σ s s' h k => za_keep hF hr h (x := 1) (by decide) (k.monoL (by simp)))
  obtain p2 := ipP_piece hS hza (t := nttInv) hP.invNtt (x := 1) (name := "vg_mldsa_inv_ntt")
    (fun σ => ⟨⟨sptr_ok rfl (by decide), by csep hF⟩, ⟨sptr_ok rfl (by decide), by csep hF⟩,
      show ix Reg.s11 ∈ sWb2 by decide, show ix Reg.s11 ∈ sWb2 by decide, by csep hF, by salsep, by salsep⟩)
    (F := fun σ => multiplyNTT (chF (cV p σ (p.ℓ * t))) (S1v p σ r))
    (fun σ s s' h k => za_keep hF hr h (x := 1) (by decide) (k.monoL (by simp)))
  -- `y[r] ← y[r] + T1`, which is `z[r]`
  obtain hzb : ∀ σ s, (IZ p STK σ t r (r + 1) s ∧
      PolyIs s.mem (SL p STK σ 1) (nttInv (multiplyNTT (chF (cV p σ (p.ℓ * t))) (S1v p σ r)))) → SC2 p STK σ s :=
    fun _ _ h => h.1.b.l.k.sc
  obtain p3 := addP_piece hP hS hzb (f := yBase p + r) (g := 1)
    (fun σ => ⟨⟨sptr_ok rfl (by clt hF), by csep hF⟩, ⟨sptr_ok rfl (by decide), by csep hF⟩,
      show ix Reg.s11 ∈ sWb2 by decide, by csep hF, by salsep, by salsep⟩)
    (F := fun σ => Yv p σ (p.ℓ * t) r) (G := fun σ => nttInv (multiplyNTT (chF (cV p σ (p.ℓ * t))) (S1v p σ r)))
    (fun _ _ h => h.2)
    (fun σ s s' h k => ⟨h.1.keep hF k (by csep hF),
      polyIs_keepW h.1.b.l.k.sc.site.ok k.frame (by csep hF) (by decide) rfl h.2⟩)
  -- its norm, into `s4`
  obtain hzc : ∀ σ s, IZ p STK σ t r (r + 1) s → SC2 p STK σ s := fun _ _ h => h.b.l.k.sc
  obtain p4 := normP_piece hP hS hzc (f := yBase p + r) (B := p.γ₁ - p.β) (fun σ => ⟨sptr_ok rfl (by clt hF), by csep hF⟩) (by salsep)
    (fun σ => by csep hF) (by rcases hF.g1 with e | e <;> rw [e] <;> omega_using [])
    (F := fun σ => Zv p σ (p.ℓ * t) r)
    (fun σ s s' h k => h.keep hF k (by csep hF))
  obtain p5 := and24_piece (p := p) (STK := STK) (J := fun σ s => (IZ p STK σ t r (r + 1) s ∧
      PolyIs s.mem (SL p STK σ (yBase p + r)) (Zv p σ (p.ℓ * t) r)) ∧
      (s.gpr .a0).setWidth 32 = (if normRq [Zv p σ (p.ℓ * t) r] < p.γ₁ - p.β then 1 else 0))
    (J' := fun σ s => IZ p STK σ t (r + 1) (r + 1) s) (fun _ _ h => h.1.1.b.l.k.sc)
    fun σ s s' ⟨⟨h, hz⟩, h3⟩ r2 e24 => ⟨h.b.regs2 r2, fun j hj => by
        rw [r2.mem]
        rcases (by omega_using [hj] : j < r ∨ j = r) with h' | rfl
        exacts [h.z j h', hz],
      fun j hj hj' => by rw [r2.mem]; exact h.y j hj hj', fun i hi => by rw [r2.mem]; exact h.w i hi,
      by rw [r2.gpr .s6 (by decide) (by decide)]; exact h.s6,
      by rw [e24, h.s4, bit_and h3]; exact bit_congr forall_lt_succ⟩
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
  obtain hk' := hF.k; have hl := hF.l; have hkl := hF.kl
  exact ⟨h.1.keep hF hk (by csep hF), polyIs_keepW h.1.b.l.k.sc.site.ok hk.frame (by csep hF) (by decide) rfl h.2⟩

theorem r0R_piece {t i : Nat} (hi : i < p.k) :
    SPiece p STK (fun σ s => IQ p STK σ t i i s) (fun σ s => IQ p STK σ t (i + 1) (i + 1) s) (r0R P p i) := by
  obtain hk' := hF.k; have hl := hF.l; have hkl := hF.kl
  obtain hra : ∀ σ s, RA p STK t i σ s → SC2 p STK σ s := fun _ _ h => h.1.b.l.k.sc
  -- `T1 ← NTT⁻¹(ĉ ŝ₂[i])`
  obtain p1 := mulP_piece hP hS hra (x := 1) (a := 0) (b := s2Base p + i)
    (fun σ => ⟨⟨sptr_ok rfl (by decide), by csep hF⟩, ⟨sptr_ok rfl (by decide), by csep hF⟩,
      ⟨sptr_ok rfl (by clt hF), by csep hF⟩, show ix Reg.s11 ∈ sWb2 by decide, by csep hF, by csep hF, by salsep, by salsep, by salsep⟩)
    (F := fun σ => chF (cV p σ (p.ℓ * t))) (G := fun σ => S2v p σ i)
    (fun _ _ h => h.1.b.c) (fun _ _ h => h.1.b.l.k.s2 i hi)
    (fun σ s s' h k => ra_keep hF hi h (x := 1) (by decide) (k.monoL (by simp)))
  obtain p2 := ipP_piece hS hra (t := nttInv) hP.invNtt (x := 1) (name := "vg_mldsa_inv_ntt")
    (fun σ => ⟨⟨sptr_ok rfl (by decide), by csep hF⟩, ⟨sptr_ok rfl (by decide), by csep hF⟩,
      show ix Reg.s11 ∈ sWb2 by decide, show ix Reg.s11 ∈ sWb2 by decide, by csep hF, by salsep, by salsep⟩)
    (F := fun σ => multiplyNTT (chF (cV p σ (p.ℓ * t))) (S2v p σ i))
    (fun σ s s' h k => ra_keep hF hi h (x := 1) (by decide) (k.monoL (by simp)))
  -- `w[i] ← w[i] - T1`
  obtain hrb : ∀ σ s, (IQ p STK σ t i (i + 1) s ∧
      PolyIs s.mem (SL p STK σ 1) (nttInv (multiplyNTT (chF (cV p σ (p.ℓ * t))) (S2v p σ i)))) → SC2 p STK σ s :=
    fun _ _ h => h.1.b.l.k.sc
  obtain p3 := subP_piece hP hS hrb (f := wBase p + i) (g := 1)
    (fun σ => ⟨⟨sptr_ok rfl (by clt hF), by csep hF⟩, ⟨sptr_ok rfl (by decide), by csep hF⟩,
      show ix Reg.s11 ∈ sWb2 by decide, by csep hF, by salsep, by salsep⟩)
    (F := fun σ => Wv p σ (p.ℓ * t) i) (G := fun σ => nttInv (multiplyNTT (chF (cV p σ (p.ℓ * t))) (S2v p σ i)))
    (fun _ _ h => h.2)
    (fun σ s s' h k => ⟨h.1.keep hF k (by csep hF),
      polyIs_keepW h.1.b.l.k.sc.site.ok k.frame (by csep hF) (by decide) rfl h.2⟩)
  -- `T2 ← LowBits(w[i])`
  obtain hrc : ∀ σ s, (IQ p STK σ t i (i + 1) s ∧ PolyIs s.mem (SL p STK σ (wBase p + i)) (W'v p σ (p.ℓ * t) i)) →
      SC2 p STK σ s := fun _ _ h => h.1.b.l.k.sc
  obtain p4 := lbP_piece hP hS hrc (r := wBase p + i) (o := 2) (g2 := p.γ₂)
    (fun σ => ⟨⟨sptr_ok rfl (by clt hF), by csep hF⟩, ⟨sptr_ok rfl (by decide), by csep hF⟩,
      show ix Reg.s11 ∈ sWb2 by decide, by csep hF, hF.g2,
      by have hg := hF.g2; simp only [gamma2s, List.mem_cons, List.not_mem_nil, or_false] at hg
         rcases hg with e | e <;> rw [e] <;> decide, by salsep, by salsep⟩)
    (F := fun σ => W'v p σ (p.ℓ * t) i) (fun _ _ h => h.2)
    (fun σ s s' h k => ⟨h.1.keep hF k (by csep hF),
      polyIs_keepW h.1.b.l.k.sc.site.ok k.frame (by csep hF) (by decide) rfl h.2⟩)
  -- its norm, into `s4`
  obtain hB : p.γ₂ - p.β < 2 ^ 31 - 2048 := by
    obtain hg := hF.g2; simp only [gamma2s, List.mem_cons, List.not_mem_nil, or_false] at hg
    have hq : q = 8380417 := rfl
    rcases hg with e | e <;> rw [e] <;> omega_using [hq]
  obtain p5 := normP_piece hP hS hrc (f := 2) (B := p.γ₂ - p.β) (fun σ => ⟨sptr_ok rfl (by decide), by csep hF⟩) (by salsep)
    (fun σ => by csep hF) hB (F := fun σ => R0v p σ (p.ℓ * t) i)
    (fun σ s s' h k => ⟨h.1.keep hF k (by csep hF),
      polyIs_keepW h.1.b.l.k.sc.site.ok k.frame (by csep hF) (by decide) rfl h.2⟩)
  obtain p6 := and24_piece (p := p) (STK := STK) (J := fun σ s => ((IQ p STK σ t i (i + 1) s ∧
      PolyIs s.mem (SL p STK σ (wBase p + i)) (W'v p σ (p.ℓ * t) i)) ∧ PolyIs s.mem (SL p STK σ 2) (R0v p σ (p.ℓ * t) i)) ∧
      (s.gpr .a0).setWidth 32 = (if normRq [R0v p σ (p.ℓ * t) i] < p.γ₂ - p.β then 1 else 0))
    (J' := fun σ s => IQ p STK σ t (i + 1) (i + 1) s) (fun _ _ h => h.1.1.1.b.l.k.sc)
    fun σ s s' ⟨⟨⟨h, hw⟩, _⟩, h3⟩ r2 e24 => ⟨h.b.regs2 r2, fun j hj => by rw [r2.mem]; exact h.z j hj,
      fun j hj => by
        rw [r2.mem]
        rcases (by omega_using [hj] : j < i ∨ j = i) with h' | rfl
        exacts [h.w' j h', hw],
      fun j hj hj' => by rw [r2.mem]; exact h.w j hj hj',
      by rw [r2.gpr .s6 (by decide) (by decide)]; exact h.s6,
      by
        rw [e24, h.s4, bit_and h3]
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
  obtain hk' := hF.k; have hl := hF.l; have hkl := hF.kl
  exact ⟨h.1.keep hF hk (by csep hF), polyIs_keepW h.1.b.l.k.sc.site.ok hk.frame (by csep hF) (by decide) rfl h.2⟩

omit hP hS in
theorem g2_lt : p.γ₂ < 2 ^ 31 - 2048 := by
  obtain hg := hF.g2; simp only [gamma2s, List.mem_cons, List.not_mem_nil, or_false] at hg
  have hq : q = 8380417 := rfl
  rcases hg with e | e <;> rw [e] <;> omega_using [hq]

theorem hR_piece {t i : Nat} (hi : i < p.k) :
    SPiece p STK (fun σ s => IH p STK σ t i i i s) (fun σ s => IH p STK σ t (i + 1) (i + 1) (i + 1) s) (hR P p i) := by
  obtain hk' := hF.k; have hl := hF.l; have hkl := hF.kl
  obtain hg2 := g2_lt hF
  obtain hha : ∀ σ s, HA p STK t i σ s → SC2 p STK σ s := fun _ _ h => h.1.b.l.k.sc
  -- `T3 ← ct₀[i] = NTT⁻¹(ĉ t̂₀[i])`
  obtain p1 := mulP_piece hP hS hha (x := 3) (a := 0) (b := t0Base p + i)
    (fun σ => ⟨⟨sptr_ok rfl (by decide), by csep hF⟩, ⟨sptr_ok rfl (by decide), by csep hF⟩,
      ⟨sptr_ok rfl (by clt hF), by csep hF⟩, show ix Reg.s11 ∈ sWb2 by decide, by csep hF, by csep hF, by salsep, by salsep, by salsep⟩)
    (F := fun σ => chF (cV p σ (p.ℓ * t))) (G := fun σ => T0v p σ i)
    (fun _ _ h => h.1.b.c) (fun _ _ h => h.1.b.l.k.t0 i hi)
    (fun σ s s' h k => ha_keep hF hi h (x := 3) (by decide) (k.monoL (by simp)))
  obtain p2 := ipP_piece hS hha (t := nttInv) hP.invNtt (x := 3) (name := "vg_mldsa_inv_ntt")
    (fun σ => ⟨⟨sptr_ok rfl (by decide), by csep hF⟩, ⟨sptr_ok rfl (by decide), by csep hF⟩,
      show ix Reg.s11 ∈ sWb2 by decide, show ix Reg.s11 ∈ sWb2 by decide, by csep hF, by salsep, by salsep⟩)
    (F := fun σ => multiplyNTT (chF (cV p σ (p.ℓ * t))) (T0v p σ i))
    (fun σ s s' h k => ha_keep hF hi h (x := 3) (by decide) (k.monoL (by simp)))
  -- its norm, into `s4`
  obtain p3 := normP_piece hP hS hha (f := 3) (B := p.γ₂) (fun σ => ⟨sptr_ok rfl (by decide), by csep hF⟩) (by salsep)
    (fun σ => by csep hF) hg2 (F := fun σ => CT0v p σ (p.ℓ * t) i)
    (fun σ s s' h k => ha_keep hF hi h (x := 3) (by decide) (k.monoL (by simp)))
  obtain p4 := and24_piece (p := p) (STK := STK) (J := fun σ s => (HA p STK t i σ s ∧
      PolyIs s.mem (SL p STK σ 3) (CT0v p σ (p.ℓ * t) i)) ∧
      (s.gpr .a0).setWidth 32 = (if normRq [CT0v p σ (p.ℓ * t) i] < p.γ₂ then 1 else 0))
    (J' := HB p STK t i) (fun _ _ h => h.1.1.1.b.l.k.sc)
    fun σ s s' ⟨⟨⟨h, hw⟩, h3c⟩, h3⟩ r2 e24 => ⟨⟨⟨h.b.regs2 r2, fun j hj => by rw [r2.mem]; exact h.z j hj,
      fun j hj => by rw [r2.mem]; exact h.w'' j hj, fun j hj hj' => by rw [r2.mem]; exact h.w' j hj hj',
      fun j hj => by rw [r2.mem]; exact h.h j hj, by rw [r2.gpr .s6 (by decide) (by decide)]; exact h.s6,
      by
        rw [e24, h.s4, bit_and h3]
        exact bit_congr ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨a, forall_lt_succ.mp ⟨b, c⟩⟩,
          fun ⟨a, b⟩ => ⟨⟨a, (forall_lt_succ.mpr b).1⟩, (forall_lt_succ.mpr b).2⟩⟩⟩,
      by rw [r2.mem]; exact hw⟩, by rw [r2.mem]; exact h3c⟩
  -- `T4 ← ct₀[i]`, then `T4 ← (T4 - ct₀[i]) - ct₀[i]`
  obtain p5 : SPiece p STK (HB p STK t i) (fun σ s => HB p STK t i σ s ∧
      PolyIs s.mem (SL p STK σ 4) (CT0v p σ (p.ℓ * t) i)) (copy .s11 (oP 3) .s11 (oP 4) 1024) := by
    refine ⟨fun σ s _ h => ?_, srel2 (fun σ s h => h.1.1.b.l.k.sc) (copy_taint _ _ _ (by unfold oP; omega_using []) (by unfold oP; omega_using []))⟩
    refine WP.mono (copyS h.1.1.b.l.k.sc.site (sb := .s11) (so := oP 3) (db := .s11)
      (dO := oP 4) (len := 1024) ⟨sptr_ok rfl (by decide), by csep hF⟩ ⟨sptr_ok rfl (by decide), by csep hF⟩
      (by decide) (by decide) (by decide) (by decide) (by decide) (by csep hF)) fun s' ⟨k', b'⟩ => ?_
    have hL := h.1.1.b.l.k.sc.site.ok
    exact ⟨⟨⟨h.1.1.keep hF k' (by csep hF), polyIs_keepW hL k'.frame (by csep hF) (by decide) rfl h.1.2⟩,
      polyIs_keepW hL k'.frame (by csep hF) (by decide) rfl h.2⟩, Proof.MlDsa.Sign.polyIs_of_bytes b' h.2⟩
  obtain hhb : ∀ σ s, HB p STK t i σ s → SC2 p STK σ s := fun _ _ h => h.1.1.b.l.k.sc
  obtain m44 : ∀ σ, KeyGen.AddOk (slay2 p STK σ) sWb2 (pS 4) (pS 3) := fun σ =>
    ⟨⟨sptr_ok rfl (by decide), by csep hF⟩, ⟨sptr_ok rfl (by decide), by csep hF⟩,
      show ix Reg.s11 ∈ sWb2 by decide, by csep hF, by salsep, by salsep⟩
  obtain hbk : ∀ σ s s', HB p STK t i σ s → Kept ((slay2 p STK σ).RL [tri (pS 4) 1024, (1, 0, STK)]) s s' →
      HB p STK t i σ s' := fun σ s s' h k => by
    have hL := h.1.1.b.l.k.sc.site.ok
    exact ⟨⟨h.1.1.keep hF k (by csep hF), polyIs_keepW hL k.frame (by csep hF) (by decide) rfl h.1.2⟩,
      polyIs_keepW hL k.frame (by csep hF) (by decide) rfl h.2⟩
  obtain p6 := subP_piece hP hS hhb (f := 4) (g := 3) m44 (F := fun σ => CT0v p σ (p.ℓ * t) i)
    (G := fun σ => CT0v p σ (p.ℓ * t) i) (fun _ _ h => h.2) hbk
  obtain p7 := subP_piece hP hS hhb (f := 4) (g := 3) m44
    (F := fun σ => sub (CT0v p σ (p.ℓ * t) i) (CT0v p σ (p.ℓ * t) i))
    (G := fun σ => CT0v p σ (p.ℓ * t) i) (fun _ _ h => h.2) hbk
  -- `w[i] ← w[i] - cs₂[i] + ct₀[i]`
  obtain hhc : ∀ σ s, ((IH p STK σ t (i + 1) i (i + 1) s ∧ PolyIs s.mem (SL p STK σ 3) (CT0v p σ (p.ℓ * t) i)) ∧
      PolyIs s.mem (SL p STK σ 4) (neg (CT0v p σ (p.ℓ * t) i))) → SC2 p STK σ s := fun _ _ h => h.1.1.b.l.k.sc
  obtain p8 := addP_piece hP hS hhc (f := wBase p + i) (g := 3)
    (fun σ => ⟨⟨sptr_ok rfl (by clt hF), by csep hF⟩, ⟨sptr_ok rfl (by decide), by csep hF⟩,
      show ix Reg.s11 ∈ sWb2 by decide, by csep hF, by salsep, by salsep⟩)
    (F := fun σ => W'v p σ (p.ℓ * t) i) (G := fun σ => CT0v p σ (p.ℓ * t) i) (fun _ _ h => h.1.2)
    (fun σ s s' h k => by
      have hL := h.1.1.b.l.k.sc.site.ok
      exact ⟨⟨h.1.1.keep hF k (by csep hF), polyIs_keepW hL k.frame (by csep hF) (by decide) rfl h.1.2⟩,
        polyIs_keepW hL k.frame (by csep hF) (by decide) rfl h.2⟩)
  -- `h[i] ← MakeHint(T4, w[i])`
  obtain mm : ∀ σ, KeyGen.UhOk (slay2 p STK σ) sWb2 (pS 4) (pS (wBase p + i)) p.γ₂ (pS (5 + i)) := fun σ =>
    ⟨⟨sptr_ok rfl (by decide), by csep hF⟩, ⟨sptr_ok rfl (by clt hF), by csep hF⟩,
      ⟨sptr_ok rfl (by clt hF), by csep hF⟩, show ix Reg.s11 ∈ sWb2 by decide, by csep hF, by csep hF, hF.g2, hg2, by salsep, by salsep, by salsep⟩
  obtain p9' : SPiece p STK (fun σ s => (IH p STK σ t (i + 1) i (i + 1) s ∧
        PolyIs s.mem (SL p STK σ (wBase p + i)) (W''v p σ (p.ℓ * t) i)) ∧
        PolyIs s.mem (SL p STK σ 4) (neg (CT0v p σ (p.ℓ * t) i)))
      (fun σ s => ((IH p STK σ t (i + 1) i (i + 1) s ∧
        PolyIs s.mem (SL p STK σ (wBase p + i)) (W''v p σ (p.ℓ * t) i)) ∧
        HintIs s.mem (SL p STK σ (5 + i)) 1 [Hv p σ (p.ℓ * t) i]) ∧
        ((s.gpr .a0).setWidth 32).toNat = hintOnes [Hv p σ (p.ℓ * t) i])
      (callAt "vg_mldsa_make_hint" P.makeHint [(.a0, .ptr (pS 4)), (.a1, .ptr (pS (wBase p + i))), (.a2, .imm p.γ₂),
        (.a3, .ptr (pS (5 + i)))]) := by
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
  -- `s6 ← s6 + |h[i]|`
  obtain p9 : SPiece p STK (fun σ s => ((IH p STK σ t (i + 1) i (i + 1) s ∧
        PolyIs s.mem (SL p STK σ (wBase p + i)) (W''v p σ (p.ℓ * t) i)) ∧
        HintIs s.mem (SL p STK σ (5 + i)) 1 [Hv p σ (p.ℓ * t) i]) ∧
        ((s.gpr .a0).setWidth 32).toNat = hintOnes [Hv p σ (p.ℓ * t) i])
      (fun σ s => IH p STK σ t (i + 1) (i + 1) (i + 1) s) (.block [.shift .sll .d .a0 .a0 32, .shift .srl .d .a0 .a0 32, .add .s6 .s6 .a0]) := by
    refine ⟨fun σ s _ ⟨⟨⟨h, hw⟩, hh⟩, he⟩ => WP.mono (onesAdd_ok s) fun s' ⟨e26, m, rd, wr, sp, g⟩ => ?_,
      srel2 (fun σ s h => h.1.1.1.b.l.k.sc) (by taint_decide)⟩
    obtain hz : zx (s.gpr .a0) = BitVec.ofNat 64 (hintOnes [Hv p σ (p.ℓ * t) i]) := by
      apply BitVec.eq_of_toNat_eq
      rw [← he]
      simp only [zx, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    obtain hk : KB p STK σ t s' := h.b.of_eq (fun r a _ b => g r a b) m rd wr sp
    refine ⟨hk, fun j hj => by rw [m]; exact h.z j hj, fun j hj => by
        rw [m]
        rcases (by omega_using [hj] : j < i ∨ j = i) with h' | rfl
        exacts [h.w'' j h', hw],
      fun j hj hj' => by rw [m]; exact h.w' j hj hj', fun j hj => by
        rw [m]
        rcases (by omega_using [hj] : j < i ∨ j = i) with h' | rfl
        exacts [h.h j h', hh], ?_, by rw [g .s4 (by decide) (by decide)]; exact h.s4⟩
    rw [e26, h.s6, hz, ← BitVec.ofNat_add, onesSum_succ]
  unfold hR normAt makeHintAt
  refine Piece.mono (p1.seq (p2.seq ((p3.seq p4).seq (p5.seq (p6.seq ((Piece.mono p7 (fun _ _ _ h => h)
    fun σ s _ h => ⟨⟨⟨h.1.1.1, h.1.2⟩, by rw [sub_sub_self] at h; exact h.2⟩, h.1.1.2⟩).seq
    ((Piece.mono p8 (fun _ _ _ h => h) fun σ s _ h => ⟨⟨h.1.1.1, h.2⟩, h.1.2⟩).seq (p9'.seq p9))))))))
    (fun σ s _ h => h.weak hi) fun _ _ _ h => h

end

/-! ## The checks, assembled -/

/-- Iteration `t` after `SampleInBall` succeeded. -/
abbrev KA (p : Params) (STK t : Nat) (σ s : State) : Prop :=
  ICd p STK t σ s ∧ PolyIs s.mem (SL p STK σ 0) (toRq (cV p σ (p.ℓ * t))) ∧
    (sampleInBall p.τ maxBounds.ball (CTv p σ (p.ℓ * t))).isSome

/-- `ĉ = NTT(c)`. -/
abbrev KN (p : Params) (STK t : Nat) (σ s : State) : Prop :=
  (ICd p STK t σ s ∧ (sampleInBall p.τ maxBounds.ball (CTv p σ (p.ℓ * t))).isSome) ∧
    PolyIs s.mem (SL p STK σ 0) (chF (cV p σ (p.ℓ * t)))

/-- What the branches of the checks need two runs to agree on: whether the
first `r` polynomials of `z` passed, for each `r` (the checks stop at the
first that fails), whether `z` and the first `i` polynomials of `r₀` passed,
for each `i`, and whether the iteration passed. -/
abbrev ChecksAgree (p : Params) (t : Nat) (σ₁ σ₂ : State) : Prop :=
  (∀ r ≤ p.ℓ, (∀ j < r, normRq [Zv p σ₁ (p.ℓ * t) j] < p.γ₁ - p.β) ↔
    (∀ j < r, normRq [Zv p σ₂ (p.ℓ * t) j] < p.γ₁ - p.β)) ∧
  (∀ i ≤ p.k, (ZOk p σ₁ (p.ℓ * t) ∧ ∀ j < i, normRq [R0v p σ₁ (p.ℓ * t) j] < p.γ₂ - p.β) ↔
    (ZOk p σ₂ (p.ℓ * t) ∧ ∀ j < i, normRq [R0v p σ₂ (p.ℓ * t) j] < p.γ₂ - p.β)) ∧
  (PassV p σ₁ (p.ℓ * t) ↔ PassV p σ₂ (p.ℓ * t))

/-- The checks done: whether the iteration passes in `s4`. -/
structure KO (p : Params) (STK : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  b : KB p STK σ t s
  z : PassV p σ (p.ℓ*t) → ∀ r < p.ℓ, PolyIs s.mem (SL p STK σ (yBase p + r)) (Zv p σ (p.ℓ * t) r)
  h : PassV p σ (p.ℓ*t) → ∀ i < p.k, HintIs s.mem (SL p STK σ (5 + i)) 1 [Hv p σ (p.ℓ * t) i]
  s4 : s.gpr .s4 = bit (PassV p σ (p.ℓ * t))

theorem bit_zero {a : Prop} [Decidable a] : bit a=0 ↔ ¬a := by
  by_cases h:a
  · rw [show bit a=1 from VG.Proof.MlDsa.KeyGen.ifp h _ _]; simp only [h,not_true_eq_false]; decide
  · rw [show bit a=0 from VG.Proof.MlDsa.KeyGen.ifn h _ _]; exact ⟨fun _=>h,fun _=>rfl⟩

theorem bit_ne {a : Prop} [Decidable a] : bit a≠0 ↔ a := by
  rw [ne_eq,bit_zero]
  exact Decidable.not_not

theorem seqOk_ok {f : Nat→Prog isa} {I : Nat→State→Prop} :
    ∀ (n a : Nat), (∀ k, a≤k → k<a+n → ∀ s, I k s → WP isa (f k) s (I (k+1))) →
      ∀ s, I a s → WP isa (seqOk f a n) s fun s'=>∃k,a≤k ∧ k≤a+n ∧ I k s' ∧ (k=a+n ∨ s'.gpr .s4=0)
  | 0,a,_,s,h=>WP.block_nil ⟨a,Nat.le_refl _,by omega_using [],h,.inl (by omega_using [])⟩
  | n+1,a,h,s,hs=>by
    rw [seqOk]
    refine WP.seq (WP.mono (h a (Nat.le_refl _) (by omega_using []) s hs) fun s₁ h₁=>?_)
    apply WP.ite _ (Steps.eval_nonzero s₁ .s4)
    · intro _
      refine WP.mono (seqOk_ok n (a+1) (fun k hk hk'=>h k (by omega_using [hk]) (by omega_using [hk'])) s₁ h₁) ?_
      rintro s' ⟨k,hk,hk',hi,hd⟩
      exact ⟨k,by omega_using [hk],by omega_using [hk'],hi,hd.imp (fun _=>by omega_arith) id⟩
    · intro hb
      exact WP.block_nil ⟨a+1,by omega_using [],by omega_using [],h₁,.inr (by simpa using hb)⟩

theorem IZ.done {p : Params} {STK : Nat} {σ : State} {t k : Nat} {s : State}
    (hk:k≤p.ℓ) (h:IZ p STK σ t k k s) (hd:k=p.ℓ ∨ s.gpr .s4=0) :
    s.gpr .s4=bit (ZOk p σ (p.ℓ*t)) := by
  rcases hd with rfl|h0
  · exact h.s4
  · rw [h.s4] at h0 ⊢
    obtain hn := bit_zero.mp h0
    rw [bit_zero.mpr hn,bit_zero.mpr (fun ha=>hn fun j hj=>ha j (by omega_using [hk, hj]))]

theorem IQ.done {p : Params} {STK : Nat} {σ : State} {t k : Nat} {s : State}
    (hk:k≤p.k) (h:IQ p STK σ t k k s) (hd:k=p.k ∨ s.gpr .s4=0) :
    s.gpr .s4=bit (ZOk p σ (p.ℓ*t) ∧ R0Ok p σ (p.ℓ*t)) := by
  rcases hd with rfl|h0
  · exact h.s4
  · rw [h.s4] at h0 ⊢
    obtain hn := bit_zero.mp h0
    rw [bit_zero.mpr hn,bit_zero.mpr (fun ha=>hn ⟨ha.1,fun j hj=>ha.2 j (by omega_using [hk, hj])⟩)]

theorem rejected_ko {p : Params} {STK : Nat} {σ : State} {t : Nat} {s : State}
    (h:KB p STK σ t s) (hn:¬PassV p σ (p.ℓ*t)) (hz:s.gpr .s4=0) : KO p STK σ t s :=
  ⟨h,fun hp=>absurd hp hn,fun hp=>absurd hp hn,by rw [hz,bit_zero.mpr hn]⟩

theorem sign_bit {S w : Nat} (hS : S < 2 ^ 62) (hw : w < 2 ^ 62) :
    (BitVec.ofNat 64 S - BitVec.ofNat 64 w) >>> 63 = if S < w then 1 else 0 := by
  by_cases h : S < w
  · rw [VG.Proof.MlDsa.KeyGen.ifp h]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    rw [Nat.shiftRight_eq_div_pow, show (1 : BitVec 64).toNat = 1 from rfl]
    omega_using [hw, h]
  · rw [VG.Proof.MlDsa.KeyGen.ifn h]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    rw [Nat.shiftRight_eq_div_pow, show (0 : BitVec 64).toNat = 0 from rfl]
    omega_using [hS, h]

theorem bit_and' {a b : Prop} [Decidable a] [Decidable b] : bit a &&& (if b then 1 else 0) = bit (a ∧ b) := by
  by_cases ha : a <;> by_cases hb : b <;> simp only [bit, ha, hb, ite_true, ite_false, and_true, and_false] <;> decide

theorem passV_iff {p : Params} {σ : State} {κ : Nat} :
    (((ZOk p σ κ ∧ R0Ok p σ κ) ∧ ∀ j < p.k, normRq [CT0v p σ κ j] < p.γ₂) ∧ onesSum (Hv p σ κ) p.k < p.ω + 1) ↔
      PassV p σ κ :=
  ⟨fun ⟨⟨⟨a, b⟩, c⟩, d⟩ => ⟨a, b, c, Nat.le_of_lt_succ d⟩, fun ⟨a, b, c, d⟩ => ⟨⟨⟨a, b⟩, c⟩, Nat.lt_succ_of_le d⟩⟩

theorem onesOk_run (p : Params) (hω : p.ω + 1 ≤ 2048) (s : State) :
    WP isa (.block (onesOk p)) s fun s' =>
      s'.gpr .s4 = s.gpr .s4 &&& ((s.gpr .s6 - BitVec.ofNat 64 (p.ω + 1)) >>> 63) ∧ Regs2 s s' := by
  unfold onesOk
  mrun [hω]
  refine ⟨fun r h3 h24 => ?_, rfl, rfl, rfl, rfl⟩
  simp only [h3, h24, ite_false]

/-- The taint check of `onesOk` does not depend on `ω`. -/
theorem onesOk_taint (p : Params) : (VG.RISCV64.taint.check (Taint.ofRegs [.s11]) (.block (onesOk p))
    (VG.Taint.hintOf VG.RISCV64.taint (Taint.ofRegs [.s11]) (.block (onesOk mlDsa44)))).isSome = true := rfl

section
variable {P : Prims} {S : Nat} (hP : SPrimsOk P S) {p : Params} (hF : SFacts p) {STK : Nat} (hS : S ≤ STK)
include hP hF hS

theorem cntt_piece {t : Nat} : SPiece p STK (KA p STK t) (KN p STK t) (nttAt P cP) := by
  obtain hk' := hF.k; have hl := hF.l; have hkl := hF.kl
  obtain hc : cLen p ≤ 64 := by rcases hF.ct with e | e | e <;> omega_using [e]
  obtain p1 := ipP_piece hS (I := fun σ s => ICd p STK t σ s ∧ (sampleInBall p.τ maxBounds.ball (CTv p σ (p.ℓ * t))).isSome)
    (fun _ _ h => h.1.1.l.k.sc) (t := ntt) hP.ntt (x := 0) (name := "vg_mldsa_ntt")
    (fun σ => ⟨⟨sptr_ok rfl (by decide), by csep hF⟩, ⟨sptr_ok rfl (by decide), by csep hF⟩,
      show ix Reg.s11 ∈ sWb2 by decide, show ix Reg.s11 ∈ sWb2 by decide, by csep hF, by salsep, by salsep⟩)
    (F := fun σ => toRq (cV p σ (p.ℓ * t)))
    (fun σ s s' h k => by
      have := h.1.1.w1b
      exact ⟨⟨h.1.1.keep k (by ssep hF [icChk, ikChk, sc2Chk, yBase, yhBase, wBase, s1Base, nSec])
        (k.cs .s5 (by decide)) (k.cs .s7 (by decide)), by
          have := h.1.2
          rw [bytes_keepW h.1.1.l.k.sc.site.ok k.frame (by csep hF) (by decide) (by omega_using [hc])]; exact this⟩, h.2⟩)
  exact Piece.mono p1 (fun σ s _ h => ⟨⟨h.1, h.2.2⟩, h.2.1⟩) fun _ _ _ h => h

omit hP hF hS in
theorem kinit_piece {t : Nat} :
    SPiece p STK (KN p STK t) (fun σ s => IZ p STK σ t 0 0 s) (.block [.li .s4 1, .li .s6 0]) := by
  refine ⟨fun σ s _ h => ?_, srel2 (fun σ s h => h.1.1.1.l.k.sc) (by taint_decide)⟩
  obtain hrun : WP isa (.block [.li .s4 1, .li .s6 0]) s fun s' => s'.gpr .s4 = 1 ∧ s'.gpr .s6 = 0 ∧
      (∀ r, r ≠ .a0 → r ≠ .s6 → r ≠ .s4 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp := by
    mrun []
    refine ⟨rfl, rfl, fun r _ h26 h24 => ?_⟩
    simp only [h26, h24, ite_false]
  refine WP.mono hrun fun s' ⟨e24, e26, g, m, rd, wr, sp⟩ => ?_
  exact ⟨KB.of_eq ⟨h.1.1.1.l, h.1.1.2, h.2, h.1.2⟩ (fun r h3 h24 h26 => g r h3 h26 h24) m rd wr sp,
    fun _ h => absurd h (Nat.not_lt_zero _), fun r _ hr => by rw [m]; exact h.1.1.1.y r hr,
    fun i hi => by rw [m]; exact h.1.1.1.w i hi, e26,
    by rw [e24]; exact (VG.Proof.MlDsa.KeyGen.ifp (fun _ h => absurd h (Nat.not_lt_zero _)) _ _).symm⟩


omit hP hS in
theorem onesOk_piece {t : Nat} : SPiece p STK (fun σ s => IH p STK σ t p.k p.k p.k s) (KO p STK · t) (.block (onesOk p)) := by
  have hk' := hF.k
  refine ⟨fun σ s _ h => WP.mono (onesOk_run p (by have := hF.om; omega_using [this]) s) fun s' ⟨e24, r2⟩ => ?_,
    srel2 (fun σ s h => h.b.l.k.sc) (onesOk_taint p)⟩
  obtain hS := onesSum_le (Hv p σ (p.ℓ * t)) p.k
  have hom := hF.om
  refine ⟨h.b.regs2 r2, (fun _ j hj => by rw [r2.mem]; exact h.z j hj), (fun _ j hj => by rw [r2.mem]; exact h.h j hj), ?_⟩
  rw [e24, h.s6, h.s4, sign_bit (by omega_using [hk', hS]) (by omega_using [hom]), bit_and']
  exact bit_congr passV_iff

theorem hs_piece {t : Nat} :
    SPiece p STK (fun σ s => IH p STK σ t 0 0 0 s) (fun σ s => IH p STK σ t p.k p.k p.k s) (seqR (hR P p) 0 p.k) :=
  Piece.mono (Piece.seqR (I := fun i σ s => IH p STK σ t i i i s) p.k 0
    fun i _ hi => hR_piece hP hF hS (by omega_using [hi])) (fun _ _ _ h => h) fun _ _ _ h => by simpa using h

end

end VG.Proof.MlDsa.RISCV64.Sign

end

end

/-!
# ML-DSA signing on RISC-V: the rejection sampling loop

As on PPC64LE (`Proof/MlDsa/PPC64LE/Sign/PhaseL.lean`). An iteration
(`iter_ok`) either continues, with the next iteration's head (`IL`), or ends
the loop (`XS`): with `s4 = 1` when it passed, as `signIteration` does
within `maxBounds` after the iterations before were rejected; with
`s4 = 0` when `signLoop` returns nothing within `minBounds` (its
`SampleInBall` did not finish, or it was the 814th rejected). So the loop
(`signLoop_ok`) ends in `XS`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Sign

open VG VG.RISCV64 VG.Proof.MlKem.RISCV64
open VG.Proof.MlDsa.RISCV64.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of polyIs_keepW bytes_keepW
  Regs2 zx)
open VG.Impl.MlDsa.RISCV64.Sign
open VG.Impl.MlDsa.RISCV64.KeyGen (callAt seqR)
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Sign (passF zF amat Rej ParamsOk signIteration_eqF signLoop_min_none signCommit_eq)
open VG.Proof.MlDsa.KeyGen (ifp ifn)
open VG.Spec.Sha3 (bytesAt)

theorem zx_set32 (x : BitVec 64) : (zx x).setWidth 32 = x.setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  simp only [zx, BitVec.toNat_setWidth]
  omega_using []

/-- The result of a call, the low word of `a0`, zero-extended. -/
theorem zxBlk_ok (s : State) :
    WP isa (.block [.shift .sll .d .a0 .a0 32, .shift .srl .d .a0 .a0 32]) s fun s' =>
      s'.gpr .a0 = zx (s.gpr .a0) ∧ (∀ r, r ≠ .a0 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
        s'.wr = s.wr ∧ s'.sp = s.sp := by
  mrun []
  exact ⟨KeyGen.zx_shift _, fun r hr => by simp only [hr, ite_false]⟩

/-! ## The loop of the specification -/

section
variable (p : Params) (σ : State)

/-- `signLoop`'s arguments for the function entered in `σ`: `Â`, `ŝ₁`, `ŝ₂`, `t̂₀`, `μ`, `ρ″`. -/
abbrev loopF (b : Bounds) (n κ : Nat) : Option (List Byte × List Poly × List (Vector Bool Spec.MlDsa.n)) :=
  signLoop p b (amat p (Am p σ)) ((List.range p.ℓ).map (S1v p σ)) ((List.range p.k).map (S2v p σ))
    ((List.range p.k).map (T0v p σ)) (muOf σ) (rppOf p σ) n κ

abbrev iterF (b : Bounds) (κ : Nat) : Option (List Byte × Option (List Poly × List (Vector Bool Spec.MlDsa.n))) :=
  signIteration p b (amat p (Am p σ)) ((List.range p.ℓ).map (S1v p σ)) ((List.range p.k).map (S2v p σ))
    ((List.range p.k).map (T0v p σ)) (muOf σ) (rppOf p σ) κ

end

section
variable {p : Params} {σ : State} {κ : Nat}

theorem iterF_eq (hp : ParamsOk p) (b : Bounds) :
    iterF p σ b κ = (sampleInBall p.τ b.ball (CTv p σ κ)).map fun c =>
      (CTv p σ κ, if passF p (Am p σ) (S1v p σ) (S2v p σ) (T0v p σ) (rppOf p σ) κ c then
        some ((List.range p.ℓ).map (zF p (S1v p σ) (rppOf p σ) κ c),
          (List.range p.k).map (Proof.MlDsa.Sign.hF p (Am p σ) (S2v p σ) (T0v p σ) (rppOf p σ) κ c)) else none) :=
  signIteration_eqF hp b _ _ _ _ _ _ κ

theorem cV_eq (h : (sampleInBall p.τ maxBounds.ball (CTv p σ κ)).isSome) :
    sampleInBall p.τ maxBounds.ball (CTv p σ κ) = some (cV p σ κ) := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp h
  simp only [cV, hc, Option.getD_some]

theorem iter_rej (hp : ParamsOk p) (h : (sampleInBall p.τ maxBounds.ball (CTv p σ κ)).isSome)
    (hf : ¬ PassV p σ κ) : iterF p σ maxBounds κ = some (CTv p σ κ, none) := by
  rw [iterF_eq hp, cV_eq h, Option.map_some, ifn hf]

theorem iter_pass (hp : ParamsOk p) (h : (sampleInBall p.τ maxBounds.ball (CTv p σ κ)).isSome)
    (hf : PassV p σ κ) : iterF p σ maxBounds κ =
      some (CTv p σ κ, some ((List.range p.ℓ).map (Zv p σ κ), (List.range p.k).map (Hv p σ κ))) := by
  rw [iterF_eq hp, cV_eq h, Option.map_some, ifp hf]

theorem iter_none (h : sampleInBall p.τ minBounds.ball (CTv p σ κ) = none) : iterF p σ minBounds κ = none := by
  rw [iterF, Proof.MlDsa.Sign.signIteration_eq, signCommit_eq, h]; rfl

end

theorem loop_none_ball {p : Params} {σ : State} {t : Nat} (h : RejT p σ t)
    (hn : sampleInBall p.τ minBounds.ball (CTv p σ (p.ℓ * t)) = none) : loopF p σ minBounds minBounds.sign 0 = none :=
  signLoop_min_none p _ _ _ _ _ _ (by decide) h (.inr (by rw [Nat.zero_add]; exact iter_none hn))

theorem loop_none_exh {p : Params} {σ : State} (h : RejT p σ 814) : loopF p σ minBounds minBounds.sign 0 = none :=
  signLoop_min_none p _ _ _ _ _ _ (by decide) h (.inl (by decide))

/-! ## `SampleInBall` -/

/-- After `SampleInBall`: the commitment, and `c` at `ĉ` if it succeeded. -/
structure IB (p : Params) (STK : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  c : ICd p STK t σ s
  r01 : (s.gpr .a0).setWidth 32 = 0 ∨ (s.gpr .a0).setWidth 32 = 1
  ok : (s.gpr .a0).setWidth 32 = 1 → PolyIs s.mem (SL p STK σ 0) (toRq (cV p σ (p.ℓ * t))) ∧
    (sampleInBall p.τ maxBounds.ball (CTv p σ (p.ℓ * t))).isSome
  bad : (s.gpr .a0).setWidth 32 = 0 → sampleInBall p.τ minBounds.ball (CTv p σ (p.ℓ * t)) = none

theorem ball_val {τ : Nat} {x : List Byte} {r : BitVec 32} {out : Poly}
    (h : Outcome (fun b => (sampleInBall τ b.ball x).map toRq) r out) (h1 : r = 1)
    (hm : (sampleInBall τ maxBounds.ball x).isSome) :
    out = toRq ((sampleInBall τ maxBounds.ball x).getD (Vector.replicate n 0)) := by
  rcases h with ⟨_, b, hb⟩ | ⟨h0, _⟩
  · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hm
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp hb
    have e1 := Proof.MlDsa.Sign.sampleInBall_mono (Nat.le_max_left b.ball maxBounds.ball) hc
    have e2 := Proof.MlDsa.Sign.sampleInBall_mono (Nat.le_max_right b.ball maxBounds.ball) hy
    rw [e1] at e2
    rw [hy, Option.some.inj e2]; rfl
  · rw [h1] at h0; cases h0

section
variable {P : Prims} {S : Nat} (hP : SPrimsOk P S) {p : Params} (hF : SFacts p) {STK : Nat} (hS : S ≤ STK)
include hP hF hS

omit hP hS in
theorem ball_m {σ : State} : KeyGen.BallOk (slay2 p STK σ) sWb2 (sc oCT) (cLen p) p.τ cP (sc oPS) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have hc : 0 < cLen p ∧ cLen p ≤ 64 := by rcases hF.ct with e | e | e <;> omega_arith
  exact ⟨⟨sptr_ok rfl (by decide), by csep hF⟩, ⟨sptr_ok rfl (by decide), by csep hF⟩,
    ⟨sptr_ok rfl (by decide), by csep hF⟩, show ix Reg.s11 ∈ sWb2 by decide, show ix Reg.s11 ∈ sWb2 by decide,
    by csep hF, by csep hF, by csep hF, hF.bp, ⟨hc.1, by omega_arith, hF.tau⟩, by salsep, by salsep⟩

theorem ball_ok {t : Nat} {σ s : State} (h : ICd p STK t σ s) :
    WP isa (ballAt P (cLen p) p.τ cP) s (IB p STK σ t) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have hc : cLen p ≤ 64 := by rcases hF.ct with e | e | e <;> omega_arith
  have hb := h.1.w1b
  unfold ballAt
  refine ball_okX hP h.1.l.k.sc.site hS (ball_m hF) fun s' k' hred hout hmax => ?_
  have hct : bytesAt s.mem (lpa (slay2 p STK σ) (sc oCT)) (cLen p) = CTv p σ (p.ℓ * t) := h.2
  rw [hct] at hout hmax
  refine ⟨⟨h.1.keep k' (by csep hF) (k'.cs .s5 (by decide)) (k'.cs .s7 (by decide)), ?_⟩, ?_,
    fun h1 => ⟨⟨hred h1, ball_val hout h1 (hmax h1)⟩, hmax h1⟩, fun h0 => ?_⟩
  · rw [bytes_keepW h.1.l.k.sc.site.ok k'.frame (by csep hF) (by decide) (by omega_arith)]; exact h.2
  · rcases hout with ⟨e, _⟩ | ⟨e, _⟩
    exacts [.inr e, .inl e]
  · rcases hout with ⟨e, _⟩ | ⟨_, hn⟩
    · rw [h0] at e; cases e
    · exact Option.map_eq_none_iff.mp hn

end

/-! ## The end of an iteration -/

theorem SC2.of_regs {p : Params} {STK : Nat} {σ s s' : State} (h : SC2 p STK σ s)
    (hg : ∀ r, r ∉ [.a0, .s4, .s5, .s6, .s7] → s'.gpr r = s.gpr r) (hm : s'.mem = s.mem)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) : SC2 p STK σ s' := by
  have hs := h.site
  refine ⟨⟨hs.ok, hs.len, hs.w0, hs.w1, hs.sz0, hs.sz1, by rw [hsp]; exact hs.p1, hs.s1168, by rw [hsp]; exact hs.spk, by rw [hsp]; exact hs.al, hs.al0,
    by rw [hg .s11 (by decide)]; exact hs.s11, by rw [hg .s10 (by decide)]; exact hs.s10,
    by rw [hg .s9 (by decide)]; exact hs.s9, by rw [hg .s8 (by decide)]; exact hs.s8,
    by rw [hwr]; exact hs.cw, by rw [hwr, hrd]; exact hs.cr⟩, hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp,
    fun r hr hs' => ?_, by rw [hm]; exact h.sav, by rw [hm]; exact h.sk, by rw [hm]; exact h.mu, h.pre,
    by rw [hg .s3 (by decide)]; exact h.s3, by rw [hm]; exact h.cache⟩
  have : r ∉ [.a0, .s4, .s5, .s6, .s7] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro (rfl | rfl | rfl | rfl | rfl)
    · simp [preserved] at hr
    all_goals simp [savedTop] at hs'
  rw [hg r this]; exact h.pres r hr hs'

theorem IK.of_regs {p : Params} {STK : Nat} {σ s s' : State} (h : IK p STK σ s)
    (hg : ∀ r, r ∉ [.a0, .s4, .s5, .s6, .s7] → s'.gpr r = s.gpr r) (hm : s'.mem = s.mem)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) : IK p STK σ s' :=
  ⟨h.sc.of_regs hg hm hrd hwr hsp, h.ok, by rw [hm]; exact h.A, by rw [hm]; exact h.rpp, by rw [hm]; exact h.s1,
    by rw [hm]; exact h.s2, by rw [hm]; exact h.t0⟩

/-- A block that writes one register `d` (one of `a0`, `s4`–`s7`) with `v`. -/
abbrev W1 (d : Reg) (v : BitVec 64) (s s' : State) : Prop :=
  s'.gpr d = v ∧ (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp

theorem W1.of_regs {d : Reg} (hd : d ∈ [.a0, .s4, .s5, .s6, .s7]) {v : BitVec 64} {s s' : State}
    (h : W1 d v s s') : ∀ r, r ∉ [.a0, .s4, .s5, .s6, .s7] → s'.gpr r = s.gpr r :=
  fun r hr => h.2.1 r fun e => hr (e ▸ hd)

theorem li_ok (d : Reg) {v : Nat} (hv : v < 2048) (s : State) :
    WP isa (.block [.li d v]) s (W1 d (BitVec.ofNat 64 v) s) := by
  mrun [hv]
  exact ⟨by simp, fun r hr => by simp [hr], rfl, rfl, rfl, rfl⟩

theorem addi_ok {d : Reg} {v : Nat} (hv : v < 2048) (s : State) :
    WP isa (.block [.addi d d v]) s (W1 d (s.gpr d + BitVec.ofNat 64 v) s) := by
  mrun [hv]
  exact ⟨by simp, fun r hr => by simp [hr], rfl, rfl, rfl, rfl⟩

theorem subi_ok {d : Reg} (s : State) :
    WP isa (.block [.addi d d (-1)]) s (W1 d (s.gpr d - BitVec.ofNat 64 1) s) := by
  mrun []
  exact ⟨by simp, fun r hr => by simp [hr], rfl, rfl, rfl, rfl⟩

theorem bit_pos {a : Prop} [Decidable a] (h : a) : bit a = 1 := ifp h _ _
theorem bit_neg {a : Prop} [Decidable a] (h : ¬ a) : bit a = 0 := ifn h _ _

theorem ofNat_sub_one {k : Nat} (h : 1 ≤ k) (hk : k < 2 ^ 64) :
    BitVec.ofNat 64 k - BitVec.ofNat 64 1 = BitVec.ofNat 64 (k - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega_arith

/-- Iteration `t` passed: `c̃`, `z` and `h`, and `s5 = 1`. -/
structure EP (p : Params) (STK : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  k : IK p STK σ s
  ct : bytesAt s.mem ((slay2 p STK σ).A 0 oCT) (cLen p) = CTv p σ (p.ℓ * t)
  z : ∀ r < p.ℓ, PolyIs s.mem (SL p STK σ (yBase p + r)) (Zv p σ (p.ℓ * t) r)
  h : ∀ i < p.k, HintIs s.mem (SL p STK σ (5 + i)) 1 [Hv p σ (p.ℓ * t) i]
  some : (sampleInBall p.τ maxBounds.ball (CTv p σ (p.ℓ * t))).isSome
  pass : PassV p σ (p.ℓ * t)
  s4 : s.gpr .s4 = 1
  s5 : s.gpr .s5 = 1
  t_lt : t < 814
  rej : RejT p σ t

/-- Iteration `t` was rejected: `κ = ℓ(t + 1)`, `s5 = 814 - t`. -/
structure EF (p : Params) (STK : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  k : IK p STK σ s
  s7 : s.gpr .s7 = BitVec.ofNat 64 (p.ℓ * (t + 1))
  s5 : s.gpr .s5 = BitVec.ofNat 64 (814 - t)
  some : (sampleInBall p.τ maxBounds.ball (CTv p σ (p.ℓ * t))).isSome
  fail : ¬ PassV p σ (p.ℓ * t)
  s4 : s.gpr .s4 = 0
  t_lt : t < 814
  rej : RejT p σ t

/-- `SampleInBall` did not finish within `minBounds`: `s4 = 0`, `s5 = 1`. -/
structure EB (p : Params) (STK : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  k : IK p STK σ s
  none : sampleInBall p.τ minBounds.ball (CTv p σ (p.ℓ * t)) = none
  s4 : s.gpr .s4 = 0
  s5 : s.gpr .s5 = 1
  t_lt : t < 814
  rej : RejT p σ t

/-- The loop ended: in `s4`, whether an iteration passed (and its signature), or `signLoop` returns
nothing within `minBounds`. -/
structure XS (p : Params) (STK : Nat) (σ : State) (s : State) : Prop where
  k : IK p STK σ s
  r01 : s.gpr .s4 = 0 ∨ s.gpr .s4 = 1
  pass : s.gpr .s4 = 1 → ∃ t < 814, RejT p σ t ∧
    (sampleInBall p.τ maxBounds.ball (CTv p σ (p.ℓ * t))).isSome ∧ PassV p σ (p.ℓ * t) ∧
    bytesAt s.mem ((slay2 p STK σ).A 0 oCT) (cLen p) = CTv p σ (p.ℓ * t) ∧
    (∀ r < p.ℓ, PolyIs s.mem (SL p STK σ (yBase p + r)) (Zv p σ (p.ℓ * t) r)) ∧
    ∀ i < p.k, HintIs s.mem (SL p STK σ (5 + i)) 1 [Hv p σ (p.ℓ * t) i]
  fail : s.gpr .s4 = 0 → loopF p σ minBounds minBounds.sign 0 = none

/-- After iteration `t`: the loop continues with iteration `t + 1`, or ends. -/
def LP (p : Params) (STK : Nat) (σ : State) (t : Nat) (s : State) : Prop :=
  (s.gpr .s5 ≠ 0 ∧ IL p STK σ (t + 1) s) ∨ (s.gpr .s5 = 0 ∧ XS p STK σ s)

theorem kthen_ok {p : Params} {STK : Nat} {σ : State} {t : Nat} {s : State} (h : KO p STK σ t s)
    (hb : s.gpr .s4 ≠ 0) : WP isa (.block [.li .s5 1]) s (EP p STK σ t) := by
  refine WP.mono (li_ok .s5 (by decide) s) fun s' w => ?_
  have hpass : PassV p σ (p.ℓ * t) := by
    by_contra hc
    rw [h.s4, bit_neg hc] at hb; exact hb rfl
  have e24 : s.gpr .s4 = 1 := by rw [h.s4, bit_pos hpass]
  exact ⟨h.b.l.k.of_regs (W1.of_regs (by decide) w) w.2.2.1 w.2.2.2.1 w.2.2.2.2.1 w.2.2.2.2.2,
    by rw [w.2.2.1]; exact h.b.ct, fun r hr => by rw [w.2.2.1]; exact h.z hpass r hr,
    fun i hi => by rw [w.2.2.1]; exact h.h hpass i hi, h.b.some, hpass,
    by rw [w.2.1 .s4 (by decide)]; exact e24, w.1, h.b.l.t_lt, h.b.l.rej⟩

theorem kelse_ok {p : Params} {STK : Nat} {σ : State} {t : Nat} {s : State} (hl : p.ℓ < 2048) (h : KO p STK σ t s)
    (hb : s.gpr .s4 = 0) : WP isa (.block [.addi .s7 .s7 p.ℓ]) s (EF p STK σ t) := by
  refine WP.mono (addi_ok hl s) fun s' w => ?_
  have hfail : ¬ PassV p σ (p.ℓ * t) := fun hp => by
    rw [h.s4, bit_pos hp] at hb; exact absurd hb (by decide)
  exact ⟨h.b.l.k.of_regs (W1.of_regs (by decide) w) w.2.2.1 w.2.2.2.1 w.2.2.2.2.1 w.2.2.2.2.2,
    by rw [w.1, h.b.l.s7, ← BitVec.ofNat_add, Nat.mul_succ], by rw [w.2.1 .s5 (by decide)]; exact h.b.l.s5,
    h.b.some, hfail, by rw [w.2.1 .s4 (by decide), h.s4, bit_neg hfail], h.b.l.t_lt, h.b.l.rej⟩

theorem kbranch_ok {p : Params} {STK : Nat} {σ : State} {t : Nat} {s : State} (hl : p.ℓ < 2048)
    (h : KO p STK σ t s) :
    WP isa (ifOkElse (.block [.li .s5 1]) (.block [.addi .s7 .s7 p.ℓ])) s fun s' => EP p STK σ t s' ∨ EF p STK σ t s' :=
  WP.ite _ (Steps.eval_nonzero s .s4) (fun hb => WP.mono (kthen_ok h (by simpa using hb)) fun _ h => .inl h)
    fun hb => WP.mono (kelse_ok hl h (by simpa using hb)) fun _ h => .inr h

/-- `IB` after the result is zero-extended. -/
theorem IB.zx {p : Params} {STK : Nat} {σ : State} {t : Nat} {s s' : State} (h : IB p STK σ t s)
    (w : s'.gpr .a0 = zx (s.gpr .a0) ∧ (∀ r, r ≠ .a0 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp) : IB p STK σ t s' := by
  obtain ⟨g3, go, m3, rd3, wr3, sp3⟩ := w
  have k3 : Kept ((slay2 p STK σ).RL []) s s' :=
    ⟨fun r hr => go r (by rintro rfl; simp [preserved] at hr), sp3, rd3, wr3, by rw [m3]; exact Frame.refl _ _⟩
  have e32 : (s'.gpr .a0).setWidth 32 = (s.gpr .a0).setWidth 32 := by rw [g3, zx_set32]
  exact ⟨⟨h.c.1.keep k3 rfl (go _ (by decide)) (go _ (by decide)), by rw [m3]; exact h.c.2⟩,
    by rw [e32]; exact h.r01, fun h1 => by rw [m3]; exact h.ok (by rw [← e32]; exact h1),
    fun h0 => h.bad (by rw [← e32]; exact h0)⟩

theorem zx_zero {x : BitVec 64} (h : x.setWidth 32 = 0) : zx x = 0 := by rw [zx, h]; rfl

theorem eb_ok {p : Params} {STK : Nat} {σ : State} {t : Nat} {s : State} (h : IB p STK σ t s)
    (h0 : (s.gpr .a0).setWidth 32 = 0) : WP isa (.block [.li .s4 0, .li .s5 1]) s (EB p STK σ t) := by
  rw [show ([.li .s4 0, .li .s5 1] : List Instr) = [.li .s4 0] ++ [.li .s5 1] from rfl, WP.block_append_iff]
  refine WP.mono (li_ok .s4 (by decide) s) fun s1 w1 => WP.mono (li_ok .s5 (by decide) s1) fun s2 w2 => ?_
  have k1 := h.c.1.l.k.of_regs (W1.of_regs (by decide) w1) w1.2.2.1 w1.2.2.2.1 w1.2.2.2.2.1 w1.2.2.2.2.2
  exact ⟨k1.of_regs (W1.of_regs (by decide) w2) w2.2.2.1 w2.2.2.2.1 w2.2.2.2.2.1 w2.2.2.2.2.2, h.bad h0,
    by rw [w2.2.1 .s4 (by decide)]; exact w1.1, w2.1, h.c.1.l.t_lt, h.c.1.l.rej⟩

theorem dec_end {p : Params} {STK : Nat} (hp : ParamsOk p) {σ : State} {t : Nat} {s : State}
    (h : EP p STK σ t s ∨ EF p STK σ t s ∨ EB p STK σ t s) :
    WP isa (.block [.addi .s5 .s5 (-1)]) s (LP p STK σ t) := by
  refine WP.mono (subi_ok s) fun s' w => ?_
  have hk : IK p STK σ s := by rcases h with h | h | h <;> exact h.k
  have K := hk.of_regs (W1.of_regs (by decide) w) w.2.2.1 w.2.2.2.1 w.2.2.2.2.1 w.2.2.2.2.2
  have e24 : s'.gpr .s4 = s.gpr .s4 := w.2.1 .s4 (by decide)
  have em : s'.mem = s.mem := w.2.2.1
  rcases h with h | h | h
  · -- passed
    have z : s'.gpr .s5 = 0 := by rw [w.1, h.s5]; decide
    refine .inr ⟨z, K, .inr (e24.trans h.s4), fun _ => ⟨t, h.t_lt, h.rej, h.some, h.pass,
      by rw [em]; exact h.ct, fun r hr => by rw [em]; exact h.z r hr, fun i hi => by rw [em]; exact h.h i hi⟩,
      fun h0 => absurd (h0.symm.trans (e24.trans h.s4)) (by decide)⟩
  · -- rejected
    have ht := h.t_lt
    have hr : RejT p σ (t + 1) := Rej.succ _ _ _ _ _ _ _ h.rej (by rw [Nat.zero_add]; exact iter_rej hp h.some h.fail)
    have e25 : s'.gpr .s5 = BitVec.ofNat 64 (814 - (t + 1)) := by
      rw [w.1, h.s5, ofNat_sub_one (by omega_arith) (by omega_arith)]; congr 1
    by_cases ht' : t = 813
    · subst ht'
      refine .inr ⟨by rw [e25]; decide, K, .inl (e24.trans h.s4),
        fun h1 => absurd (h1.symm.trans (e24.trans h.s4)) (by decide), fun _ => loop_none_exh hr⟩
    · refine .inl ⟨by rw [e25]; intro e; have := congrArg BitVec.toNat e; simp at this; omega_arith,
        ⟨K, by rw [w.2.1 .s7 (by decide)]; exact h.s7, e25, by omega_arith, hr⟩⟩
  · -- `SampleInBall` failed
    have z : s'.gpr .s5 = 0 := by rw [w.1, h.s5]; decide
    exact .inr ⟨z, K, .inl (e24.trans h.s4), fun h1 => absurd (h1.symm.trans (e24.trans h.s4)) (by decide),
      fun _ => loop_none_ball h.rej h.none⟩

/-! ## An iteration, and the loop -/

section
variable {P : Prims} {S : Nat} (hP : SPrimsOk P S) {p : Params} (hF : SFacts p) {STK : Nat} (hS : S ≤ STK)
include hP hF hS

theorem checksR0_ok {σ : State} (hpre:SPre p STK σ) {t : Nat} {s : State} (h:IQ p STK σ t 0 0 s) :
    WP isa (checksR0 P p) s (KO p STK σ t) := by
  unfold checksR0
  refine WP.seq (WP.mono (seqOk_ok (I:=fun i=>IQ p STK σ t i i) p.k 0
    (fun i _ hi s hs=>(r0R_piece hP hF hS (by omega_using [hi])).ok σ s hpre hs) s h) fun s₁ ⟨k,_,hk,hi,hd⟩=>?_)
  rw [Nat.zero_add] at hk hd
  apply WP.ite _ (Steps.eval_nonzero s₁ .s4)
  · intro hb
    have hn:s₁.gpr .s4≠0:=by simpa using hb
    have he:k=p.k:=hd.resolve_right hn
    subst he
    exact WP.seq (WP.mono ((hs_piece hP hF hS).ok σ s₁ hpre hi.ih) fun s₂ h₂=>(onesOk_piece hF).ok σ s₂ hpre h₂)
  · intro hb
    have hz:s₁.gpr .s4=0:=by simpa using hb
    have hn:¬PassV p σ (p.ℓ*t):=fun hp=>(bit_ne.mpr ⟨hp.1,hp.2.1⟩) ((IQ.done hk hi hd).symm.trans hz)
    exact WP.block_nil (rejected_ko hi.b hn hz)

theorem zchecks_ok {σ : State} (hpre:SPre p STK σ) {t : Nat} {s : State} (h:IZ p STK σ t 0 0 s) :
    WP isa (.seq (seqOk (zR P p) 0 p.ℓ) (ifOk (checksR0 P p))) s (KO p STK σ t) := by
  refine WP.seq (WP.mono (seqOk_ok (I:=fun i=>IZ p STK σ t i i) p.ℓ 0
    (fun i _ hi s hs=>(zR_piece hP hF hS (by omega_using [hi])).ok σ s hpre hs) s h) fun s₁ ⟨k,_,hk,hi,hd⟩=>?_)
  rw [Nat.zero_add] at hk hd
  apply WP.ite _ (Steps.eval_nonzero s₁ .s4)
  · intro hb
    have hn:s₁.gpr .s4≠0:=by simpa using hb
    have he:k=p.ℓ:=hd.resolve_right hn
    subst he
    exact checksR0_ok hP hF hS hpre hi.iq
  · intro hb
    have hz:s₁.gpr .s4=0:=by simpa using hb
    have hn:¬PassV p σ (p.ℓ*t):=fun hp=>(bit_ne.mpr hp.1) ((IZ.done hk hi hd).symm.trans hz)
    exact WP.block_nil (rejected_ko hi.b hn hz)

theorem checks_ok {σ : State} (hpre : SPre p STK σ) {t : Nat} {s : State} (h : KA p STK t σ s) :
    WP isa (checks P p) s fun s' => EP p STK σ t s' ∨ EF p STK σ t s' := by
  unfold checks
  refine WP.seq (WP.mono ((cntt_piece hP hF hS).ok σ s hpre h) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (kinit_piece.ok σ s1 hpre h1) fun s2 h2 => ?_)
  exact WP.seq (WP.mono (zchecks_ok hP hF hS hpre h2) fun s₃ h₃=>kbranch_ok (by have := hF.l; omega_using [this]) h₃)

theorem iter_ok (hp : ParamsOk p) {σ : State} (hpre : SPre p STK σ) {t : Nat} {s : State} (h : IL p STK σ t s) :
    WP isa (iter P p) s (LP p STK σ t) := by
  unfold iter
  refine WP.seq (WP.mono ((commit_piece hP hF hS).ok σ s hpre h) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (ball_ok hP hF hS h1) fun s2 h2 => ?_)
  refine WP.seq (WP.seq (WP.mono (zxBlk_ok s2) fun s3 ⟨g3, go, m3, rd3, wr3, sp3⟩ => ?_))
  have h3 : IB p STK σ t s3 := h2.zx ⟨g3, go, m3, rd3, wr3, sp3⟩
  refine WP.ite _ (Steps.eval_nonzero s3 .a0) (fun hb => ?_) fun hb => ?_
  · have h1' : (s3.gpr .a0).setWidth 32 = 1 := by
      rcases h3.r01 with e | e
      · have : s3.gpr .a0 = 0 := by rw [g3, zx, ← zx_set32, ← g3, e]; rfl
        rw [this] at hb; exact absurd hb (by decide)
      · exact e
    exact WP.mono (checks_ok hP hF hS hpre ⟨h3.c, (h3.ok h1').1, (h3.ok h1').2⟩) fun s' h' =>
      dec_end hp (h'.elim .inl (fun h => .inr (.inl h)))
  · have z : s3.gpr .a0 = 0 := by simpa using hb
    have z32 : (s3.gpr .a0).setWidth 32 = 0 := by rw [z]; rfl
    exact WP.mono (eb_ok h3 z32) fun s' h' => dec_end hp (.inr (.inr h'))

omit hP hF hS in
theorem loopInit_ok {σ s : State} (h : IK p STK σ s) :
    WP isa (.block [.li .s7 0, .li .s5 814]) s (IL p STK σ 0) := by
  rw [show ([.li .s7 0, .li .s5 814] : List Instr) = [.li .s7 0] ++ [.li .s5 814] from rfl, WP.block_append_iff]
  refine WP.mono (li_ok .s7 (by decide) s) fun s1 w1 => WP.mono (li_ok .s5 (by decide) s1) fun s2 w2 => ?_
  have k1 := h.of_regs (W1.of_regs (by decide) w1) w1.2.2.1 w1.2.2.2.1 w1.2.2.2.2.1 w1.2.2.2.2.2
  exact ⟨k1.of_regs (W1.of_regs (by decide) w2) w2.2.2.1 w2.2.2.2.1 w2.2.2.2.2.1 w2.2.2.2.2.2,
    by rw [w2.2.1 .s7 (by decide), w1.1, Nat.mul_zero], w2.1, by decide, fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem signLoop_ok (hp : ParamsOk p) {σ : State} (hpre : SPre p STK σ) {s : State} (h : IK p STK σ s) :
    WP isa (Impl.MlDsa.RISCV64.Sign.signLoop P p) s (XS p STK σ) := by
  unfold Impl.MlDsa.RISCV64.Sign.signLoop
  refine WP.seq (WP.mono (loopInit_ok h) fun s2 I0 => ?_)
  refine WP.loop (M := isa) (fun n s => ∃ t, n = 814 - t ∧ IL p STK σ t s) (fun n s ⟨t, hn, hs⟩ => ?_) 814 s2
    ⟨0, rfl, I0⟩
  refine WP.mono (iter_ok hP hF hS hp hpre hs) fun s' h' => ?_
  rcases h' with ⟨hz, hI⟩ | ⟨hz, hX⟩
  · exact .inr ⟨by rw [Steps.eval_nonzero]; exact congrArg some (bne_iff_ne.mpr hz), 814 - (t + 1), by have := hs.t_lt; omega_arith, t + 1, rfl, hI⟩
  · exact .inl ⟨by rw [Steps.eval_nonzero, hz]; rfl, hX⟩

end

end VG.Proof.MlDsa.RISCV64.Sign
