module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.AttemptBI
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.CTBase
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Bignum.PPC64LE.WinBase
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.AttemptBI
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.CTBase
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.WinBase
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.ExchangeCorrect
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.DomainBody
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubOut
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubCorrect
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubLoad
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.Status
import VerifiedGarbage.Proof.Rsa.FixedBaseCombTable
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# `vg_ffdh_generate_key_cached` on PPC64LE: the body in constant time

From `BI`, each piece of the body runs from a predicate that fixes the
registers it computes addresses and branches from as functions of the public
data `CG`, and states that the rest reaches the next such predicate, by
correctness (`stage1_ok`, `bad_ok`, `good_ok`); between them, the taint
checker. The values loaded from memory (the header's words, the context's)
are pinned after the block that loads them.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Cached

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain
open VG.Impl.Ffdh.PPC64LE VG.Impl.Ffdh.PPC64LE.Cached VG.Impl.Ffdh.PPC64LE.Cached.Generate
open VG.Impl.Ffdh.PPC64LE.GenerateKey (cutBody)
open VG.Proof.Ffdh.PPC64LE.Domain
open VG.Proof.Ffdh.PPC64LE.GenerateKey (GD K6 K7 KM1 KM2 pins_K6 pins_K7)
open VG.Proof.Ffdh.KeyScalar (cut)
open VG.Proof.MillerRabin.PPC64LE (Env arr)
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.PPC64LE.Win (mask)
open VG.Proof.Bignum.PPC64LE (Two Pins two_post two_taint)
open VG.Proof.Ffdh.PPC64LE.ParameterCandidate (two_ite')

section
variable {S D X O R C : Addr} {Z k L p bits : Nat} {v : Bool}

/-- The registers and header words x's range reads. -/
structure LF (S D X : Addr) (Z k L : Nat) (s : State) : Prop where
  env : Env s S Z ((k + 7) / 8)
  h23 : s.gpr .r23 = S
  h21 : s.gpr .r21 = D
  h27 : s.gpr .r27 = BitVec.ofNat 64 L
  h28 : s.gpr .r28 = BitVec.ofNat 64 k
  hX : s.mem.readW (off S 64) 64 = off X 0
  hXL : s.mem.readW (off S 72) 64 = BitVec.ofNat 64 k

/-- After x's cut and range, from `s₀`: `scalarC_ok`'s and `xRange_ok`'s
results. -/
def XI (S D X R : Addr) (k L bits : Nat) (s₀ u : State) : Prop :=
  ∃ s₃, ((Spec.Rsa.bytesAt s₃.mem X k = cut (Spec.Rsa.bytesAt s₀.mem R k) (k - (bits + 7) / 8) (tbOf bits) ∧
      Outside X 0 k s₀.mem s₃.mem) ∧ Keep scalarCRegs s₀ s₃) ∧
    ((u.gpr .r26 = mask (decide (0 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₃.mem X k) ∧
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₃.mem X k) <
          Derive.bnd s₃.mem D k L (arr s₃.mem S ((k + 7) / 8) 0))) ∧
      arr u.mem S ((k + 7) / 8) 0 = arr s₃.mem S ((k + 7) / 8) 0 ∧ Body S ((k + 7) / 8) s₃.mem u.mem ∧
      u.gpr .r10 = off S (slot ((k + 7) / 8) 0)) ∧ Keep Derive.xRangeRegs s₃ u)

/-- x's cut, by correctness, with x's range to come. -/
theorem stage1_ok {s : State} (h : BI S D X O R C Z k L p bits v s) :
    WP isa scalar s fun s₃ => LF S D X Z k L s₃ ∧ WP isa Derive.xRange s₃ (XI S D X R k L bits s) := by
  have hZ := h.env.hZ
  have e0 := Domain.slot_eq ((k + 7) / 8) 0
  have e28 := Domain.slot_eq ((k + 7) / 8) 28
  have hk := h.hk
  have hk' := h.hk'
  refine WP.mono (scalarC_ok h.env h.h23 h.h28 (by omega) h.hk' h.hb1 h.hbk h.hbw h.hyw h.hX h.hR h.hrdR h.hx
    h.hsepRX) fun s₃ ⟨⟨xb, xout⟩, k3⟩ => ?_
  have osc := GenerateKey.out_scr xout h.hsepBX
  have hw3 : ∀ d, d + 8 ≤ 256 → word s₃.mem S d = word s.mem S d := fun d hd =>
    Outside.word osc (Or.inl (by omega)) (by omega)
  have hp3 : arr s₃.mem S ((k + 7) / 8) 0 = p := by
    rw [arr, Outside.val32 osc (Or.inl (by omega)) (by omega)]; exact h.hP
  have e3 := h.env.keep k3 (by decide)
  have g23 : s₃.gpr .r23 = S := (k3.gpr .r23 (by decide)).trans h.h23
  have g21 : s₃.gpr .r21 = D := (k3.gpr .r21 (by decide)).trans h.h21
  have g27 : s₃.gpr .r27 = BitVec.ofNat 64 L := (k3.gpr .r27 (by decide)).trans h.h27
  have g28 : s₃.gpr .r28 = BitVec.ofNat 64 k := (k3.gpr .r28 (by decide)).trans h.h28
  have hX3 : s₃.mem.readW (off S 64) 64 = off X 0 := by
    show word s₃.mem S 64 = _; rw [hw3 64 (by omega)]; exact h.hX
  have hXL3 : s₃.mem.readW (off S 72) 64 = BitVec.ofNat 64 k := by
    show word s₃.mem S 72 = _; rw [hw3 72 (by omega)]; exact h.hXL
  have rdQ : L = 3 * k → ∀ i < k, InRegions (s₃.rd ++ s₃.wr) (off (off D (2 * k)) i) 1 := fun hq i hi => by
    rw [Domain.off_off', k3.rd, k3.wr]; exact h.hrdD _ (by omega)
  have sepQ : L = 3 * k → ∀ i < k, ∀ x, ofs S x < Z → off (off D (2 * k)) i ≠ x := fun hq i hi => by
    rw [Domain.off_off']; exact h.hsepD _ (by omega)
  refine ⟨⟨e3, g23, g21, g27, g28, hX3, hXL3⟩, WP.mono (Derive.xRange_ok (xl := k) e3 g23 g21 g27 g28 (by omega)
    (by omega) (by rcases h.hL with e | e <;> omega) (by omega) (by omega) (Nat.le_refl _) hX3 hXL3
    (fun i hi => (h.hx.congr k3.wr).ld (d := i) (n := 1) (by omega)) h.hsepX rdQ sepQ (by rw [hp3]; have := h.hp2; omega))
    fun u hu => ⟨s₃, ⟨⟨xb, xout⟩, k3⟩, hu⟩⟩

end

/-! ## x's cut -/

/-- The shift of the first octet's mask. -/
abbrev shiftOf (bits : Nat) : BitVec 64 := BitVec.ofNat 64 (8 * ((bits + 7) / 8) - bits)

/-- Before x's range. -/
def PX' (q : CG) (s₀ t : State) : Prop :=
  LF q.c.S q.c.D q.g.d.x.X q.c.Z q.c.k q.c.L t ∧
    WP isa Derive.xRange t (XI q.c.S q.c.D q.g.d.x.X q.g.R q.c.k q.c.L q.bits s₀)

def PX (q : CG) (t : State) : Prop := ∃ s₀, BIq q s₀ ∧ PX' q s₀ t

/-- After `maskByte`, with the rest of x's cut to come. -/
def B2' (q : CG) (s₀ t : State) : Prop :=
  (t.mem = s₀.mem ∧ Keep [.r14, .r17, .r18] s₀ t) ∧
    WP isa (.seq (.block sbBlock) (Precompute.countLoop .r6 cutBody)) t (PX' q s₀)

def B2 (q : CG) (t : State) : Prop := ∃ s₀, BIq q s₀ ∧ B2' q s₀ t

/-- After `maskByte`'s block: the shift in `r17`. -/
def B1 (q : CG) (t : State) : Prop :=
  ∃ s₀, BIq q s₀ ∧ t.gpr .r17 = shiftOf q.bits ∧ WP isa mbIte t (B2' q s₀)

/-- After `sbBlock`: `rand`'s and x's addresses, the count and the index. -/
def B3 (q : CG) (t : State) : Prop :=
  ∃ s₀, BIq q s₀ ∧ (t.gpr .r24 = off q.g.R 0 ∧ t.gpr .r25 = off q.g.d.x.X 0 ∧
    t.gpr .r6 = BitVec.ofNat 64 q.c.k ∧ t.gpr .r4 = BitVec.ofNat 64 0) ∧
    WP isa (Precompute.countLoop .r6 cutBody) t (PX' q s₀)

/-- After `xLoadPre`: `Derive.R1`'s registers. -/
def R1c (q : CG) (t : State) : Prop :=
  ∃ s₀, BIq q s₀ ∧ (t.gpr .r10 = off q.c.S (slot q.c.w 4) ∧ t.gpr .r12 = off q.g.d.x.X 0 ∧
    t.gpr .r6 = BitVec.ofNat 64 q.c.k ∧ t.gpr .r11 = BitVec.ofNat 64 (2 * q.c.w) ∧ t.gpr .r21 = q.c.D ∧
    t.gpr .r23 = q.c.S ∧ t.gpr .r27 = BitVec.ofNat 64 q.c.L ∧ t.gpr .r28 = BitVec.ofNat 64 q.c.k ∧
    t.gpr .r29 = BitVec.ofNat 64 (8 * (q.c.w + 2)) ∧ t.gpr .r31 = q.c.S) ∧
    WP isa (.seq Derive.xLoadRest Derive.xMask) t
      (XI q.c.S q.c.D q.g.d.x.X q.g.R q.c.k q.c.L q.bits s₀)

/-- After x's range. -/
def XIc (q : CG) (u : State) : Prop :=
  ∃ s₀, BIq q s₀ ∧ XI q.c.S q.c.D q.g.d.x.X q.g.R q.c.k q.c.L q.bits s₀ u

theorem pins_BI : Pins BIq [.r23] := by
  intro q s₁ s₂ h₁ h₂ r hr
  rw [List.mem_singleton] at hr; subst hr; rw [h₁.h23, h₂.h23]

theorem pins_B1 : Pins B1 [.r17] := by
  rintro q s₁ s₂ ⟨_, _, a, _⟩ ⟨_, _, b, _⟩ r hr
  rw [List.mem_singleton] at hr; subst hr; rw [a, b]

theorem pins_B2 : Pins B2 [.r23, .r28] := by
  rintro q s₁ s₂ ⟨a₀, ha, ⟨-, ka⟩, -⟩ ⟨b₀, hb, ⟨-, kb⟩, -⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [ka.gpr .r23 (by decide), kb.gpr .r23 (by decide), ha.h23, hb.h23]
  · rw [ka.gpr .r28 (by decide), kb.gpr .r28 (by decide), ha.h28, hb.h28]

theorem pins_B3 : Pins B3 [.r24, .r25, .r6, .r4] := by
  rintro q s₁ s₂ ⟨_, _, ⟨a24, a25, a6, a4⟩, _⟩ ⟨_, _, ⟨b24, b25, b6, b4⟩, _⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [a24, b24]
  · rw [a25, b25]
  · rw [a6, b6]
  · rw [a4, b4]

theorem pins_PX : Pins PX [.r23] := by
  rintro q s₁ s₂ ⟨_, _, a, _⟩ ⟨_, _, b, _⟩ r hr
  rw [List.mem_singleton] at hr; subst hr; rw [a.h23, b.h23]

theorem pins_R1c : Pins R1c [.r6, .r10, .r11, .r12, .r21, .r23, .r27, .r28, .r29, .r31] := by
  rintro q s₁ s₂ ⟨_, _, ⟨a10, a12, a6, a11, a21, a23, a27, a28, a29, a31⟩, _⟩
    ⟨_, _, ⟨b10, b12, b6, b11, b21, b23, b27, b28, b29, b31⟩, _⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a6, b6]
  · rw [a10, b10]
  · rw [a11, b11]
  · rw [a12, b12]
  · rw [a21, b21]
  · rw [a23, b23]
  · rw [a27, b27]
  · rw [a28, b28]
  · rw [a29, b29]
  · rw [a31, b31]

theorem BI_B1 {q : CG} {s : State} (h : BIq q s) : WP isa (.block mbBlock) s (B1 q) := by
  have hZ := h.env.hZ
  have hw := Domain.slot_eq ((q.c.k + 7) / 8) 28
  have hs1 := stage1_ok h
  rw [scalar_eq] at hs1
  have hm := WP.and (maskByte_ok h.env.hs (by omega) h.h23 h.hbw h.hyw (by have := h.hbk; have := h.hk'; omega))
    (WP.seq_iff.mp hs1)
  rw [maskByte_eq] at hm
  exact WP.mono (WP.and (mb_ok h.env.hs (by omega) h.h23 h.hbw h.hyw (by have := h.hbk; have := h.hk'; omega))
    (WP.seq_iff.mp hm)) fun t ⟨⟨⟨a17, _⟩, _⟩, hw⟩ => ⟨s, h, a17,
      WP.mono hw fun u ⟨⟨⟨_, um⟩, uk⟩, hu⟩ => ⟨⟨um, uk⟩, hu⟩⟩

theorem B2_B3 {q : CG} {s : State} (h : B2 q s) : WP isa (.block sbBlock) s (B3 q) := by
  obtain ⟨s₀, h₀, ⟨hm, hk⟩, hw⟩ := h
  have hZ := h₀.env.hZ
  have hw28 := Domain.slot_eq ((q.c.k + 7) / 8) 28
  refine WP.mono (WP.and (sb_ok (bits := q.bits) (X := q.g.d.x.X) (R := q.g.R) (h₀.env.hs.congr hk.wr) (by omega)
    ((hk.gpr .r23 (by decide)).trans h₀.h23) ((hk.gpr .r28 (by decide)).trans h₀.h28)
    (by have := h₀.hbk; omega) (by have := h₀.hk'; omega)
    (by rw [hm]; exact h₀.hyw) (by rw [hm]; exact h₀.hX) (by rw [hm]; exact h₀.hR)) (WP.seq_iff.mp hw))
    fun t ⟨⟨⟨_, a24, a25, a6, a4, _⟩, _⟩, hw'⟩ => ⟨s₀, h₀, ⟨a24, a25, a6, a4⟩, hw'⟩

theorem PX_R1c {q : CG} {s : State} (h : PX q s) : WP isa (.block Derive.xLoadPre) s (R1c q) := by
  obtain ⟨s₀, h₀, hl, hw⟩ := h
  unfold Derive.xRange at hw
  refine WP.mono (WP.and (Derive.xLoadPre_ok hl.env hl.h23 hl.hX hl.hXL) (WP.seq_iff.mp hw))
    fun t ⟨⟨⟨a10, a12, a6, _⟩, kt⟩, hw'⟩ => ⟨s₀, h₀, ⟨a10, a12, a6, (kt.gpr .r11 (by decide)).trans hl.env.h11,
      (kt.gpr .r21 (by decide)).trans hl.h21, (kt.gpr .r23 (by decide)).trans hl.h23,
      (kt.gpr .r27 (by decide)).trans hl.h27, (kt.gpr .r28 (by decide)).trans hl.h28,
      (kt.gpr .r29 (by decide)).trans hl.env.h29, (kt.gpr .r31 (by decide)).trans hl.env.h31⟩, hw'⟩

/-- x's cut. -/
theorem scalar_rel : RelCT isa (Two BIq) scalar (Two PX) := by
  rw [scalar_eq, maskByte_eq]
  exact RelCT.seq (R := Two B2) (RelCT.seq (R := Two B1)
    (two_post (two_taint _ pins_BI (by taint_decide)) fun _ _ h => BI_B1 h)
    (two_post (two_taint _ pins_B1 (by taint_decide)) fun _ _ ⟨s₀, h₀, _, hw⟩ =>
      WP.mono hw fun _ hu => ⟨s₀, h₀, hu⟩))
    (RelCT.seq (R := Two B3) (two_post (two_taint _ pins_B2 (by taint_decide)) fun _ _ h => B2_B3 h)
      (two_post (two_taint _ pins_B3 (by taint_decide)) fun _ _ ⟨s₀, h₀, _, hw⟩ =>
        WP.mono hw fun _ hu => ⟨s₀, h₀, hu⟩))

/-- x's range. -/
theorem xRange_rel : RelCT isa (Two PX) Derive.xRange (Two XIc) := by
  unfold Derive.xRange
  exact RelCT.seq (R := Two R1c) (two_post (two_taint _ pins_PX (by taint_decide)) fun _ _ h => PX_R1c h)
    (two_post (two_taint _ pins_R1c (by taint_decide)) fun _ _ ⟨s₀, h₀, _, hw⟩ =>
      WP.mono hw fun _ hu => ⟨s₀, h₀, hu⟩)

/-! ## After x's range -/

section
variable {S D X O R C : Addr} {Z k L p bits : Nat} {v : Bool}

/-- What holds after x's range, from `BI`. -/
structure XF (S D X R C : Addr) (Z k p bits : Nat) (v : Bool) (s₀ u : State) : Prop where
  env : Env u S Z ((k + 7) / 8)
  h23 : u.gpr .r23 = S
  h28 : u.gpr .r28 = BitVec.ofNat 64 k
  hw : ∀ d, d + 8 ≤ 256 → word u.mem S d = word s₀.mem S d
  xb : Spec.Rsa.bytesAt u.mem X k = cut (Spec.Rsa.bytesAt s₀.mem R k) (k - (bits + 7) / 8) (tbOf bits)
  hp : arr u.mem S ((k + 7) / 8) 0 = p
  keep : Keep (scalarCRegs ++ Derive.xRangeRegs) s₀ u
  cx : Outside C (8 * ctxWords ((k + 7) / 8)) (2 ^ 64) s₀.mem u.mem
  r26 : (u.gpr .r26 == 0) = !v

theorem xf_of {s₀ u : State} (h : BI S D X O R C Z k L p bits v s₀) (hx : XI S D X R k L bits s₀ u) :
    XF S D X R C Z k p bits v s₀ u := by
  obtain ⟨s₃, ⟨⟨xb, xout⟩, k3⟩, ⟨a26, p4, b4, a10⟩, k4⟩ := hx
  have hZ := h.env.hZ
  have hnw := h.env.hs.nowrap
  have hk := h.hk
  have e0 := Domain.slot_eq ((k + 7) / 8) 0
  have e28 := Domain.slot_eq ((k + 7) / 8) 28
  have osc := GenerateKey.out_scr xout h.hsepBX
  have hw3 : ∀ d, d + 8 ≤ 256 → word s₃.mem S d = word s₀.mem S d := fun d hd =>
    Outside.word osc (Or.inl (by omega)) (by omega)
  have hp3 : arr s₃.mem S ((k + 7) / 8) 0 = p := by
    rw [arr, Outside.val32 osc (Or.inl (by omega)) (by omega)]; exact h.hP
  have hbD : ∀ (Q : Addr) n, (∀ i < n, ∀ y, ofs X y < k → off Q i ≠ y) →
      Spec.Rsa.bytesAt s₃.mem Q n = Spec.Rsa.bytesAt s₀.mem Q n := fun Q n hq =>
    Domain.outside_bytesAt xout (by omega) hq
  have eb : Derive.bnd s₃.mem D k L p = Derive.bnd s₀.mem D k L p := by
    unfold Derive.bnd
    by_cases hq : L = 3 * k
    · rw [ite_eq_left hq, ite_eq_left hq, hbD _ _ fun i hi => by
        rw [Domain.off_off']; exact h.hsepDX _ (by omega)]
    · rw [ite_eq_right hq, ite_eq_right hq]
  have cx3 := ctx_of_x (n := 8 * ctxWords ((k + 7) / 8)) xout h.hsepCX
  have e3 := h.env.keep k3 (by decide)
  have k34 := k3.trans k4
  rw [xb, hp3, eb] at a26
  rw [hp3] at p4
  refine ⟨⟨h.env.hs.congr k34.wr, a10, (k34.gpr .r29 (by decide)).trans h.env.h29,
    (k34.gpr .r11 (by decide)).trans h.env.h11, (k34.gpr .r31 (by decide)).trans h.env.h31, h.env.hw, h.env.hw', hZ⟩,
    (k34.gpr .r23 (by decide)).trans h.h23, (k34.gpr .r28 (by decide)).trans h.h28,
    fun d hd => by rw [Outside.word b4 (by omega) (by omega), hw3 d hd],
    by rw [Domain.Body.bytesAt b4 hZ h.hsepX, xb], p4, k34,
    cx3.trans (outs_ctx (body_att b4) (attOut_fit e3) h.hc.sep), ?_⟩
  rw [a26, Domain.mask_beq_zero]
  congr 1
  cases hv : v
  · exact decide_eq_false fun hc => absurd (h.hv.mp hc) (by simp [hv])
  · exact decide_eq_true (h.hv.mpr hv)

end

/-! ## The two branches -/

/-- Before the output: `exOut_split`'s registers. -/
def X7p (q : CG) (t : State) : Prop :=
  t.gpr .r27 = off q.g.d.x.O 0 ∧ t.gpr .r10 = off q.c.S (slot q.c.w 0) ∧
    t.gpr .r29 = BitVec.ofNat 64 (8 * (q.c.w + 2)) ∧ t.gpr .r28 = BitVec.ofNat 64 q.c.k ∧ t.gpr .r23 = q.c.S ∧
    t.gpr .r11 = BitVec.ofNat 64 (2 * q.c.w)

/-- Before `exOutPre`: its registers. -/
def X6p (q : CG) (t : State) : Prop :=
  t.gpr .r10 = off q.c.S (slot q.c.w 0) ∧ t.gpr .r29 = BitVec.ofNat 64 (8 * (q.c.w + 2)) ∧
    t.gpr .r11 = BitVec.ofNat 64 (2 * q.c.w) ∧ t.gpr .r23 = q.c.S ∧ t.gpr .r28 = BitVec.ofNat 64 q.c.k

/-- After the comb's first block: the comb's registers. -/
def HP (q : CG) (t : State) : Prop :=
  t.gpr .r30 = q.C ∧ t.gpr .r27 = off q.g.d.x.X 0 ∧
    t.gpr .r21 = BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows q.bits) ∧ t.gpr .r3 = BitVec.ofNat 64 1 ∧ X6p q t

/-- Before the status's last block, which reaches x's mask. -/
def FinB (q : CG) (c : List Instr) (t : State) : Prop := t.gpr .r23 = q.c.S ∧ WP isa (.block c) t (K6 q.g)

def GD3 (q : CG) (t : State) : Prop := X7p q t ∧ WP isa PublicChecked.output t (FinB q Derive.status)

def GD2 (q : CG) (t : State) : Prop := X6p q t ∧ WP isa exOutPre t (GD3 q)

def GD1 (q : CG) (t : State) : Prop := HP q t ∧ WP isa combRest t (GD2 q)

def BD1 (q : CG) (t : State) : Prop := X7p q t ∧ WP isa PublicChecked.output t (FinB q [.li .r3 2])

theorem pins_X7p {Φ : CG → State → Prop} (h : ∀ q s, Φ q s → X7p q s) :
    Pins Φ [.r10, .r11, .r23, .r27, .r28, .r29] := by
  intro q s₁ s₂ h₁ h₂ r hr
  obtain ⟨a27, a10, a29, a28, a23, a11⟩ := h _ _ h₁
  obtain ⟨b27, b10, b29, b28, b23, b11⟩ := h _ _ h₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a10, b10]
  · rw [a11, b11]
  · rw [a23, b23]
  · rw [a27, b27]
  · rw [a28, b28]
  · rw [a29, b29]

theorem pins_X6p {Φ : CG → State → Prop} (h : ∀ q s, Φ q s → X6p q s) :
    Pins Φ [.r10, .r11, .r23, .r28, .r29] := by
  intro q s₁ s₂ h₁ h₂ r hr
  obtain ⟨a10, a29, a11, a23, a28⟩ := h _ _ h₁
  obtain ⟨b10, b29, b11, b23, b28⟩ := h _ _ h₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [a10, b10]
  · rw [a11, b11]
  · rw [a23, b23]
  · rw [a28, b28]
  · rw [a29, b29]

theorem pins_GD1 : Pins GD1 [.r3, .r10, .r11, .r21, .r23, .r27, .r28, .r29, .r30] := by
  rintro q s₁ s₂ ⟨⟨a30, a27, a21, a3, a10, a29, a11, a23, a28⟩, -⟩
    ⟨⟨b30, b27, b21, b3, b10, b29, b11, b23, b28⟩, -⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a3, b3]
  · rw [a10, b10]
  · rw [a11, b11]
  · rw [a21, b21]
  · rw [a23, b23]
  · rw [a27, b27]
  · rw [a28, b28]
  · rw [a29, b29]
  · rw [a30, b30]

theorem pins_FinB (c : List Instr) : Pins (fun q s => FinB q c s) [.r23] := by
  rintro q s₁ s₂ ⟨a, -⟩ ⟨b, -⟩ r hr
  rw [List.mem_singleton] at hr; subst hr; rw [a, b]

theorem pins_XIc {Φ : CG → State → Prop} (h : ∀ q s, Φ q s → XIc q s) : Pins Φ [.r23] := by
  intro q s₁ s₂ h₁ h₂ r hr
  obtain ⟨a₀, ha, hxa⟩ := h _ _ h₁
  obtain ⟨b₀, hb, hxb⟩ := h _ _ h₂
  rw [List.mem_singleton] at hr; subst hr
  rw [(xf_of ha hxa).h23, (xf_of hb hxb).h23]

/-- x's mask's predicate, at the end of either branch. -/
theorem k6_of {q : CG} {s₀ u t : State} {rs : List Reg} (h₀ : BIq q s₀) (hx : XF q.c.S q.c.D q.g.d.x.X q.g.R q.C
    q.c.Z q.c.k q.c.p q.bits q.g.d.v s₀ u) (k : Keep rs u t) (h23 : .r23 ∉ rs) (h28 : .r28 ∉ rs)
    (hw : word t.mem q.c.S 64 = word u.mem q.c.S 64) {st : Nat} (h3 : t.gpr .r3 = BitVec.ofNat 64 st)
    (hst1 : 1 ≤ st) (hst : st < 4) : K6 q.g t := by
  have hZ := h₀.env.hZ
  have e28 := Domain.slot_eq ((q.c.k + 7) / 8) 28
  have hk := h₀.hk
  have hk' := h₀.hk'
  have kk := hx.keep.trans k
  exact ⟨⟨(k.gpr _ h23).trans hx.h23, (k.gpr _ h28).trans hx.h28⟩,
    by show word t.mem _ 64 = _; rw [hw, hx.hw 64 (by omega)]; exact h₀.hX,
    by rw [kk.rd, kk.wr]; exact h₀.env.hs.ld (d := 64) (n := 8) (by omega), h₀.hx.congr kk.wr,
    ⟨show 1 ≤ q.c.k by omega, show q.c.k < 2 ^ 32 by omega⟩, st, h3, hst1, hst⟩

/-- Out of range: zeros to `y`, the status 2. -/
theorem bad_ok {q : CG} {u : State} (h : XIc q u) (hv : q.g.d.v = false) :
    WP isa (.block [.load .d .r27 .r23 80]) u (BD1 q) := by
  obtain ⟨s₀, h₀, hx⟩ := h
  have xf := xf_of h₀ hx
  have hZ := h₀.env.hZ
  have hnw := h₀.env.hs.nowrap
  have hk := h₀.hk
  have hk' := h₀.hk'
  have e8 := Domain.slot_eq ((q.c.k + 7) / 8) 8
  have e28 := Domain.slot_eq ((q.c.k + 7) / 8) 28
  have hO : u.mem.readW (off q.c.S 80) 64 = off q.g.d.x.O 0 := (xf.hw 80 (by omega)).trans h₀.hO
  refine WP.mono (WP.keep [.r27] (Q := fun t => t.gpr .r27 = off q.g.d.x.O 0 ∧ t.mem = u.mem) (by
      prun [xf.h23, xf.env.hs.ld (d := 80) (n := 8) (by omega), hO]) (by decide)) fun t ⟨⟨a27, mt⟩, kt⟩ => ?_
  have k10 := (kt.gpr .r10 (by decide)).trans xf.env.h10
  have k29 := (kt.gpr .r29 (by decide)).trans xf.env.h29
  have k28 := (kt.gpr .r28 (by decide)).trans xf.h28
  have k23 := (kt.gpr .r23 (by decide)).trans xf.h23
  have k11 := (kt.gpr .r11 (by decide)).trans xf.env.h11
  have ka := xf.keep.trans kt
  have h26 : t.gpr .r26 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if false then 1 else 0) := by
    rw [kt.gpr .r26 (by decide)]
    have e := xf.r26
    rw [hv] at e
    exact (beq_iff_eq.mp e).trans rfl
  refine ⟨⟨a27, k10, k29, k28, k23, k11⟩, WP.mono (Pub.output_ok (b := false) (xf.env.hs.congr kt.wr)
    (h₀.ho.congr ka.wr) k10 k29 k28 a27 h26 (by omega) (by omega) (by omega) h₀.hsepO)
    fun t' ⟨⟨_, ot, _⟩, kt'⟩ => ⟨(kt'.gpr .r23 (by decide)).trans k23, WP.mono (li_ok t' 2 (by decide))
      fun t'' ⟨⟨u3, um⟩, ku⟩ => k6_of h₀ xf ((kt.trans kt').trans ku) (by decide) (by decide) ?_ u3
        (by decide) (by decide)⟩⟩
  rw [um]
  refine (Pub.Outside.word_apart (d := 64) ot h₀.hsepB (by omega) (by omega) hnw).trans ?_
  show word t.mem _ 64 = word u.mem _ 64
  rw [mt]

/-- In range: the comb, then z or zeros to `y`, the status 1 or 3 (whatever x's range). -/
theorem good_ok {q : CG} {u : State} (h : XIc q u) :
    WP isa (.block headBlock) u (GD1 q) := by
  obtain ⟨s₀, h₀, hx⟩ := h
  have xf := xf_of h₀ hx
  have hZ := h₀.env.hZ
  have hnw := h₀.env.hs.nowrap
  have hk := h₀.hk
  have hk' := h₀.hk'
  have hw := h₀.env.hw; have hw' := h₀.env.hw'
  have e0 := Domain.slot_eq ((q.c.k + 7) / 8) 0
  have e28 := Domain.slot_eq ((q.c.k + 7) / 8) 28
  have hl4 : (Spec.Rsa.bytesAt u.mem q.g.d.x.X q.c.k).length = q.c.k := VG.Proof.Bignum.bytesAt_length _ _ _
  have xv : Spec.Rsa.os2ip (Spec.Rsa.bytesAt u.mem q.g.d.x.X q.c.k) < 2 ^ q.bits := by
    rw [xf.xb, scalarC_value (by simp [Spec.Rsa.bytesAt]) h₀.hb1 h₀.hbk]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have ci : CombIn u q.c.S q.C q.g.d.x.X q.c.Z ((q.c.k + 7) / 8) (Spec.Rsa.bytesAt u.mem q.g.d.x.X q.c.k) q.c.p
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₀.mem (off q.c.D q.c.k) q.c.k)) q.bits := by
    refine ⟨xf.env, xf.h23, by rw [xf.h28, hl4], by rw [show hCtx = 0 from rfl]; exact (xf.hw 0 (by omega)).trans h₀.hCw,
      h₀.hc.congr xf.keep.rd xf.keep.wr, fun a ha => ?_, ?_, xf.hp,
      by rw [show hRows = 24 from rfl]; exact (xf.hw 24 (by omega)).trans h₀.hRw,
      by rw [show u.mem.readW (off q.c.S 64) 64 = word u.mem q.c.S 64 from rfl, xf.hw 64 (by omega)]
         exact h₀.hX.trans (BitVec.add_zero _),
      fun n hn => (h₀.hx.congr xf.keep.wr).ld (d := n) (n := 1) (by omega), fun n hn => h₀.hsepX n (by omega),
      fun n hn => by simp [Spec.Rsa.bytesAt, off],
      ⟨h₀.hodd, by have := h₀.hp2; omega, (Rsa.FixedBaseComb.rows_small (show q.bits ≤ 8192 by have := h₀.hbk; omega)).1,
        by rw [hl4]; omega⟩, h₀.hb1⟩
    · rw [← h₀.hents a ha]
      exact Outside.val32 xf.cx (Or.inl (by have := row_fits (w := (q.c.k + 7) / 8) ha; omega))
        (by have := row_fits (w := (q.c.k + 7) / 8) ha; have := h₀.hc.hn; omega)
    · rw [← h₀.hr2]
      exact Outside.val32 xf.cx (Or.inl (by have := row1_fits ((q.c.k + 7) / 8); omega))
        (by have := row1_fits ((q.c.k + 7) / 8); have := h₀.hc.hn; omega)
  have hP : 0 < q.c.p := by have := h₀.hp2; omega
  have hc : WP isa comb u (GD2 q) := by
    refine WP.mono (comb_ok ci) fun t ⟨⟨z1, p1, o1, r10⟩, k1⟩ => ?_
    generalize hz : Spec.Rsa.powMod (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₀.mem (off q.c.D q.c.k) q.c.k))
      (Rsa.FixedBaseComb.high q.bits (Spec.Rsa.os2ip (Spec.Rsa.bytesAt u.mem q.g.d.x.X q.c.k)) 0) q.c.p = z at z1
    have hzP : z < q.c.p := by rw [← hz, VG.Proof.Bignum.powMod_eq]; exact Nat.mod_lt _ hP
    have t29 := (k1.gpr .r29 (by decide)).trans xf.env.h29
    have t11 := (k1.gpr .r11 (by decide)).trans xf.env.h11
    have t23 := (k1.gpr .r23 (by decide)).trans xf.h23
    have t28 := (k1.gpr .r28 (by decide)).trans xf.h28
    refine ⟨⟨r10, t29, t11, t23, t28⟩, WP.mono (Domain.exOut_split (O := q.g.d.x.O) (k := q.c.k)
      (xf.env.hs.congr k1.wr) (h₀.ho.congr (xf.keep.trans k1).wr) r10 t29 t11 t23 t28 hw hw' hZ (by omega) (by omega)
      (by rw [hdr_of_comb o1 (by decide)]; exact (xf.hw 80 (by omega)).trans h₀.hO) h₀.hsepO
      (by rw [p1]; omega) (by rw [z1, p1]; exact hzP) (by rw [p1]; exact h₀.hpk))
      fun t₃ ⟨p3, hw3⟩ => ⟨p3, WP.mono hw3 fun t₄ ⟨⟨_, o2, m, bm, om⟩, k4⟩ => ⟨(k4.gpr .r23 (by decide)).trans t23,
        WP.mono (Derive.status_ok t₄ _ o2) fun t₅ ⟨⟨t3, tm⟩, k5⟩ =>
          k6_of h₀ xf ((k1.trans k4).trans k5) (by decide) (by decide) ?_ t3
            (by split <;> decide) (by split <;> decide)⟩⟩⟩
    rw [tm]
    refine (Pub.Outside.word_apart (d := 64) om h₀.hsepB (by omega) (by omega) hnw).trans ?_
    show word m _ 64 = word u.mem _ 64
    rw [Outside.word bm (Or.inl (by omega)) (by omega)]
    exact hdr_of_comb o1 (by decide)
  rw [comb_eq] at hc
  refine WP.mono (WP.and (head_ok xf.env.hs (by omega) xf.h23 ci.hC ci.hX ci.hRw) (WP.seq_iff.mp hc))
    fun t ⟨⟨⟨a30, a27, a21, a3, _⟩, kt⟩, hw⟩ => ⟨⟨a30, a27.trans (BitVec.add_zero _).symm, a21, a3,
      (kt.gpr .r10 (by decide)).trans xf.env.h10, (kt.gpr .r29 (by decide)).trans xf.env.h29,
      (kt.gpr .r11 (by decide)).trans xf.env.h11, (kt.gpr .r23 (by decide)).trans xf.h23,
      (kt.gpr .r28 (by decide)).trans xf.h28⟩, hw⟩

/-- After x's range: out of range or in range, to x's mask. -/
theorem ite_rel : RelCT isa (Two XIc) (.ite (.zero .d .r26) Derive.dpBad good) (Two fun (q : CG) s => K6 q.g s) := by
  refine two_ite' (fun q : CG => !q.g.d.v) (fun q u ⟨s₀, h₀, hx⟩ => by rw [eval_zero, (xf_of h₀ hx).r26]) ?_ ?_
  · unfold Derive.dpBad
    exact RelCT.seq (R := Two BD1) (two_post (two_taint _ (pins_XIc fun _ _ h => h.1) (by taint_decide))
        fun _ _ ⟨h, hv⟩ => bad_ok h (by simpa using hv))
      (RelCT.seq (R := Two fun (q : CG) s => FinB q [.li .r3 2] s)
        (two_post (two_taint _ (pins_X7p fun _ _ h => h.1) (by taint_decide)) fun _ _ h => h.2)
        (two_post (two_taint _ (pins_FinB [.li .r3 2]) (by taint_decide)) fun _ _ h => h.2))
  · unfold good exOut
    rw [comb_eq]
    exact RelCT.seq (R := Two GD2) (RelCT.seq (R := Two GD1)
        (two_post (two_taint _ (pins_XIc fun _ _ h => h.1) (by taint_decide)) fun _ _ ⟨h, _⟩ =>
          good_ok h)
        (two_post (two_taint _ pins_GD1 (by taint_decide)) fun _ _ h => h.2))
      (RelCT.seq (R := Two fun (q : CG) s => FinB q Derive.status s) (RelCT.seq (R := Two GD3)
          (two_post (two_taint _ (pins_X6p fun _ _ h => h.1) (by taint_decide)) fun _ _ h => h.2)
          (two_post (two_taint _ (pins_X7p fun _ _ h => h.1) (by taint_decide)) fun _ _ h => h.2))
        (two_post (two_taint _ (pins_FinB Derive.status) (by taint_decide)) fun _ _ h => h.2))

/-- x's mask. -/
theorem maskX_rel : RelCT isa (Two fun (q : CG) s => K6 q.g s) VG.Impl.Ffdh.PPC64LE.GenerateKey.maskX
    (Two fun (q : CG) s => CF q.c s) := by
  unfold VG.Impl.Ffdh.PPC64LE.GenerateKey.maskX
  exact RelCT.seq (R := Two fun (q : CG) s => K7 q.g s)
    (two_post (two_taint _ (fun q => pins_K6 q.g) (by taint_decide)) fun _ _ h => KM1 h)
    (two_post (two_taint _ (fun q => pins_K7 q.g) (by taint_decide)) fun _ _ h => KM2 h)

/-- The body. -/
theorem body_rel : RelCT isa (Two BIq) body (Two fun (q : CG) s => CF q.c s) := by
  unfold body
  exact RelCT.seq (R := Two PX) scalar_rel (RelCT.seq (R := Two fun (q : CG) s => K6 q.g s)
    (RelCT.seq (R := Two XIc) xRange_rel ite_rel) maskX_rel)

end VG.Proof.Ffdh.PPC64LE.Cached
