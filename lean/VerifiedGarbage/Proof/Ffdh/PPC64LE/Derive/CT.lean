module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.Fn
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.Front
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.Range
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.Fn
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.Front
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.Range
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.Body
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.Status
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.ExchangeCorrect
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckPublicFn
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubCorrect
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubOut
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# `vg_ffdh_derive_public` on PPC64LE: constant time

As the exchange's (`Domain/ExchangeCT.lean`), with the public data `DD`: the
exchange's for g as the peer and `y` as `out` (`dxOf`), the bound on x and
whether x is within it, which the status reveals. Each predicate after a
piece that computes from memory states that the rest of its stage reaches
the next predicate, by correctness: p's load and check (`loadP_ok`), x's
range (`xRange_ok`); the exchange's predicates then cover the power and the
output.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Derive

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain VG.Impl.Ffdh.PPC64LE.Derive
open VG.Proof.Ffdh.PPC64LE.Domain
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.PPC64LE (Two Pins two_post two_taint)

/-- The public data of a run: the exchange's, the bound on x, and whether x
is within it. -/
structure DD where
  x : XD
  b : Nat
  v : Bool

/-- x's value in `s`. -/
abbrev xval (x : XD) (s : State) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem x.X x.xl)

def ddOf (s : State) : DD :=
  ⟨dxOf s, bnd s.mem (s.gpr .r5) (s.gpr .r7).toNat (s.gpr .r6).toNat (dxOf s).c.p,
    decide (0 < xval (dxOf s) s ∧ xval (dxOf s) s <
      bnd s.mem (s.gpr .r5) (s.gpr .r7).toNat (s.gpr .r6).toNat (dxOf s).c.p)⟩

/-- The bound, as the data has it, whatever the bytes of `m` and `m'` outside
the domain's. -/
theorem bnd_congr {m m' : Mem} {D : Addr} {k L p : Nat}
    (h : L = 3 * k → Spec.Rsa.bytesAt m' (off D (2 * k)) k = Spec.Rsa.bytesAt m (off D (2 * k)) k) :
    bnd m' D k L p = bnd m D k L p := by
  unfold bnd
  by_cases hq : L = 3 * k
  · rw [ite_eq_left hq, ite_eq_left hq, h hq]
  · rw [ite_eq_right hq, ite_eq_right hq]

/-- The bound and x's range, as the data has them. -/
def Inv (d : DD) (s : State) : Prop :=
  d.x.c.Y = off d.x.c.D d.x.c.k ∧ bnd s.mem d.x.c.D d.x.c.k d.x.c.L d.x.c.p = d.b ∧
    (0 < xval d.x s ∧ xval d.x s < d.b ↔ d.v = true)

theorem Inv.keep {d : DD} {s t : State} (h : Inv d s) (hb : Base d.x.c s) (he : ∀ i < d.x.xl, ∀ y,
    ofs d.x.c.S y < d.x.c.Z → off d.x.X i ≠ y) (hm : Body d.x.c.S d.x.c.w s.mem t.mem) : Inv d t := by
  have hZ := hb.env.hZ
  refine ⟨h.1, (bnd_congr fun hq => hm.bytesAt hZ fun i hi => by
    rw [off_off']; exact hb.sepD _ (by omega)).trans h.2.1, ?_⟩
  have ex : xval d.x t = xval d.x s := by simp only [xval]; rw [hm.bytesAt hZ he]
  rw [ex]; exact h.2.2

/-- The exchange's `Ext` but for `r9`. -/
structure ExtX (x : XD) (s : State) : Prop where
  wX : s.mem.readW (off x.c.S 64) 64 = off x.X 0
  wXL : s.mem.readW (off x.c.S 72) 64 = BitVec.ofNat 64 x.xl
  wO : s.mem.readW (off x.c.S 80) 64 = off x.O 0
  rdX : ∀ i < x.xl, InRegions (s.rd ++ s.wr) (off x.X i) 1
  sepX : ∀ i < x.xl, ∀ y, ofs x.c.S y < x.c.Z → off x.X i ≠ y
  scrO : Scr s x.O x.c.k
  sepO : ∀ y, ofs x.O y < x.c.k → x.c.Z ≤ ofs x.c.S y
  xl1 : 1 ≤ x.xl
  xlk : x.xl ≤ x.c.k

theorem ExtX.of {x : XD} {s : State} (h : Ext x s) : ExtX x s :=
  ⟨h.wX, h.wXL, h.wO, h.rdX, h.sepX, h.scrO, h.sepO, h.xl1, h.xlk⟩

theorem ExtX.ext {x : XD} {s : State} (h : ExtX x s) (h9 : s.gpr .r9 = x.c.Y) : Ext x s :=
  ⟨h9, h.wX, h.wXL, h.wO, h.rdX, h.sepX, h.scrO, h.sepO, h.xl1, h.xlk⟩

theorem ExtX.keep {x : XD} {s t : State} {rs : List Reg} (h : ExtX x s) (k : Keep rs s t)
    (hm : Body x.c.S x.c.w s.mem t.mem) : ExtX x t where
  wX := by
    have := Domain.slot_eq x.c.w 0
    show word t.mem x.c.S 64 = _
    rw [Outside.word hm (Or.inl (by omega)) (by omega)]; exact h.wX
  wXL := by
    have := Domain.slot_eq x.c.w 0
    show word t.mem x.c.S 72 = _
    rw [Outside.word hm (Or.inl (by omega)) (by omega)]; exact h.wXL
  wO := by
    have := Domain.slot_eq x.c.w 0
    show word t.mem x.c.S 80 = _
    rw [Outside.word hm (Or.inl (by omega)) (by omega)]; exact h.wO
  rdX := by rw [k.rd, k.wr]; exact h.rdX
  sepX := h.sepX
  scrO := h.scrO.congr k.wr
  sepO := h.sepO
  xl1 := h.xl1
  xlk := h.xlk

/-! ## The predicates -/

def Z0 (d : DD) (s : State) : Prop := dpContract.pre s ∧ ddOf s = d

/-- From `dpFront` on. -/
def ZB (d : DD) (s : State) : Prop := XB d.x s ∧ Inv d s

/-- After p's check. -/
def Z4 (d : DD) (s : State) : Prop := X4 d.x s ∧ Inv d s

/-- With `loadN`'s arguments, and p's load and check to come. -/
def Z1a (d : DD) (s : State) : Prop :=
  X1a d.x s ∧ WP isa (.seq Precompute.loadN Precompute.check) s (Z4 d)

/-- After `loadN`. -/
def Z2 (d : DD) (s : State) : Prop := X2 d.x s ∧ WP isa Precompute.check s (Z4 d)

/-- After `check1`. -/
def Z3 (d : DD) (s : State) : Prop := X3 d.x s ∧ WP isa Precompute.check2 s (Z4 d)

/-- After x's range: `r26` is zero exactly when x is out of range. -/
def R2 (d : DD) (s : State) : Prop :=
  Base d.x.c s ∧ ExtX d.x s ∧ arr s.mem d.x.c.S d.x.c.w 0 = d.x.c.p ∧
    Spec.Rsa.modulusValid d.x.c.p d.x.c.k = true ∧ (s.gpr .r26 = 0 ↔ d.v = false) ∧
    d.x.c.Y = off d.x.c.D d.x.c.k

/-- After x's address and length are loaded: the registers of the rest of
x's range, and that it reaches `R2`. -/
def R1 (d : DD) (s : State) : Prop :=
  (s.gpr .r10 = off d.x.c.S (slot d.x.c.w 4) ∧ s.gpr .r12 = off d.x.X 0 ∧ s.gpr .r6 = BitVec.ofNat 64 d.x.xl ∧
    s.gpr .r11 = BitVec.ofNat 64 (2 * d.x.c.w) ∧ s.gpr .r21 = d.x.c.D ∧ s.gpr .r23 = d.x.c.S ∧
    s.gpr .r27 = BitVec.ofNat 64 d.x.c.L ∧ s.gpr .r28 = BitVec.ofNat 64 d.x.c.k ∧
    s.gpr .r29 = BitVec.ofNat 64 (8 * (d.x.c.w + 2)) ∧ s.gpr .r31 = d.x.c.S) ∧
  WP isa (.seq xLoadRest xMask) s (R2 d)

/-- Before the power: g's address in `r9`, and p checked. -/
def G2 (d : DD) (s : State) : Prop :=
  XB d.x s ∧ arr s.mem d.x.c.S d.x.c.w 0 = d.x.c.p ∧ Spec.Rsa.modulusValid d.x.c.p d.x.c.k = true

/-! ## Pins -/

theorem pins_x {Φ : XD → State → Prop} {rs : List Reg} (h : Pins Φ rs) : Pins (fun (d : DD) s => Φ d.x s) rs :=
  fun d => h d.x

theorem pins_xb {Φ : DD → State → Prop} (h : ∀ d s, Φ d s → XB d.x s) :
    Pins Φ (baseRegs ++ ([.r9] : List Reg)) := fun d s₁ s₂ h₁ h₂ =>
  pins_XB (Φ := XB) (fun _ _ h => h) d.x s₁ s₂ (h _ _ h₁) (h _ _ h₂)

theorem pins_base' {Φ : DD → State → Prop} (h : ∀ d s, Φ d s → Base d.x.c s) : Pins Φ baseRegs :=
  fun _ _ _ h₁ h₂ => (h _ _ h₁).pins (h _ _ h₂)

theorem pins_Z0 : Pins Z0 [.r3, .r8, .r9, .r10] := by
  rintro d s₁ s₂ ⟨-, h₁⟩ ⟨-, h₂⟩ r hr
  have e₁ := congrArg DD.x h₁
  have e₂ := congrArg DD.x h₂
  simp only [ddOf, dxOf] at e₁ e₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (congrArg XD.O e₁).trans (congrArg XD.O e₂).symm
  · exact (congrArg XD.X e₁).trans (congrArg XD.X e₂).symm
  · exact BitVec.eq_of_toNat_eq ((congrArg XD.xl e₁).trans (congrArg XD.xl e₂).symm)
  · exact (congrArg (fun x => x.c.S) e₁).trans (congrArg (fun x => x.c.S) e₂).symm

theorem pins_R1 : Pins R1 [.r6, .r10, .r11, .r12, .r21, .r23, .r27, .r28, .r29, .r31] := by
  rintro d s₁ s₂ ⟨⟨a10, a12, a6, a11, a21, a23, a27, a28, a29, a31⟩, -⟩
    ⟨⟨b10, b12, b6, b11, b21, b23, b27, b28, b29, b31⟩, -⟩ r hr
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

theorem pins_ZCF : Pins (fun (d : DD) s => CF d.x.c s) [.r23] := pins_x pins_XCF

/-! ## The front and p's check -/

/-- `wp_and` and a decomposition of the sequence: the first part reaches `P`
and the rest. -/
theorem wp_split {c₁ c₂ : Prog isa} {s : State} {P Q : State → Prop} (h₁ : WP isa c₁ s P)
    (h₂ : WP isa (.seq c₁ c₂) s Q) : WP isa c₁ s fun t => P t ∧ WP isa c₂ t Q := by
  obtain ⟨t₁, s₁, e₁, p₁⟩ := h₁
  obtain ⟨t₂, s₂, e₂, q₂⟩ := WP.seq_iff.mp h₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ e₂
  exact ⟨t₁, s₁, e₁, p₁, q₂⟩

theorem F0 {d : DD} {s : State} (h : Z0 d s) : WP isa (.block dpFront) s (ZB d) := by
  obtain ⟨hpre, rfl⟩ := h
  refine WP.mono (dp_front hpre) fun t ⟨⟨hb, he⟩, _, hby, _⟩ => ⟨⟨hb, he⟩, rfl,
    bnd_congr fun hq => hby _ _ fun i hi => by
      rw [off_off']; exact hb.sepD _ (by simp only [ddOf, dxOf] at hq hi ⊢; omega), ?_⟩
  have ex : xval (dxOf s) t = xval (dxOf s) s := by simp only [xval]; rw [hby _ _ he.sepX]
  show 0 < xval (dxOf s) t ∧ xval (dxOf s) t < bnd s.mem (s.gpr .r5) (s.gpr .r7).toNat (s.gpr .r6).toNat
    (dxOf s).c.p ↔ decide _ = true
  rw [ex, decide_eq_true_iff]

/-- p's load and check, from `ZB`, by correctness. -/
theorem ZB_loadP {d : DD} {s : State} (h : ZB d s) : WP isa loadP s (Z4 d) := by
  obtain ⟨⟨hb, he⟩, hi⟩ := h
  have hk := hb.k64
  refine WP.mono (loadP_ok hb.env hb.r21 hb.r28 rfl hk hb.k1024 (fun i hi => hb.rdD i (by have := hb.kL; omega))
    (fun i hi => hb.sepD i (by have := hb.kL; omega))) fun t ⟨⟨pt, ct, bt⟩, kt⟩ => ?_
  have ep : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem d.x.c.D d.x.c.k) = d.x.c.p := by
    rw [← Proof.Ffdh.take_bytesAt _ _ hb.kL, hb.bD]
  rw [ep] at pt ct
  exact ⟨⟨⟨hb.keep kt bt, he.keep kt bt⟩, pt, ct⟩, hi.keep hb he.sepX bt⟩

theorem F1 {d : DD} {s : State} (h : ZB d s) :
    WP isa (.block [.addi .r12 .r21 0, .addi .r6 .r28 0]) s (Z1a d) :=
  wp_split (XA h.1) (ZB_loadP h)

theorem F2 {d : DD} {s : State} (h : Z1a d s) : WP isa Precompute.loadN s (Z2 d) :=
  wp_split (XL h.1) h.2

theorem F3 {d : DD} {s : State} (h : Z2 d s) : WP isa (.block Precompute.check1) s (Z3 d) :=
  wp_split (XC1 h.1) h.2

theorem F4 {d : DD} {s : State} (h : Z3 d s) : WP isa Precompute.check2 s (Z4 d) := h.2

theorem FK0 {d : DD} {s : State} (h : Z4 d s ∧ s.gpr .r0 ≠ 0) : WP isa (.block [.li .r3 0]) s (fun t => CF d.x.c t) :=
  TK0 (Φ := fun d s => Base d s) (fun _ _ h => h) h.1.1.1.1

/-! ## x's range -/

theorem TR1 {d : DD} {s : State} (h : Z4 d s ∧ s.gpr .r0 = 0) : WP isa (.block xLoadPre) s (R1 d) := by
  obtain ⟨⟨⟨⟨hb, he⟩, hp, h0⟩, hi⟩, hz⟩ := h
  have hv := h0.mp hz
  have hf := modulus_facts hv
  have hk := hb.k64
  have hk' := hb.k1024
  have hZ := hb.env.hZ
  have hwd : d.x.c.w = (d.x.c.k + 7) / 8 := rfl
  have e28 := Domain.slot_eq d.x.c.w 28
  have rdQ : d.x.c.L = 3 * d.x.c.k → ∀ i < d.x.c.k, InRegions (s.rd ++ s.wr) (off (off d.x.c.D (2 * d.x.c.k)) i) 1 :=
    fun hq i hi => by rw [off_off']; exact hb.rdD _ (by omega)
  have sepQ : d.x.c.L = 3 * d.x.c.k → ∀ i < d.x.c.k, ∀ y, ofs d.x.c.S y < d.x.c.Z →
      off (off d.x.c.D (2 * d.x.c.k)) i ≠ y := fun hq i hi => by rw [off_off']; exact hb.sepD _ (by omega)
  have hrange := xRange_ok hb.env hb.r23 hb.r21 hb.r27 hb.r28 (by omega) (by omega)
    (by rcases hb.hL with h | h <;> omega) (by omega) he.xl1 he.xlk he.wX he.wXL he.rdX he.sepX rdQ sepQ
    (by rw [hp]; omega)
  unfold xRange at hrange
  refine wp_split (WP.mono (xLoadPre_ok hb.env hb.r23 he.wX he.wXL) fun t ⟨⟨a10, a12, a6, _⟩, kt⟩ =>
    ⟨a10, a12, a6, (kt.gpr .r11 (by decide)).trans hb.env.h11, (kt.gpr .r21 (by decide)).trans hb.r21,
      (kt.gpr .r23 (by decide)).trans hb.r23, (kt.gpr .r27 (by decide)).trans hb.r27,
      (kt.gpr .r28 (by decide)).trans hb.r28, (kt.gpr .r29 (by decide)).trans hb.env.h29,
      (kt.gpr .r31 (by decide)).trans hb.env.h31⟩) (WP.mono hrange fun t ⟨⟨t26, tp, tb, t10⟩, kt⟩ => ?_)
  have hb' : Base d.x.c t := Base.of hb (fun r hr => by
      simp only [baseRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [t10, hb.env.h10]
      all_goals exact kt.gpr _ (by decide)) kt.rd kt.wr tb
  refine ⟨hb', (ExtX.of he).keep kt tb, by rw [tp, hp], hv, ?_, hi.1⟩
  rw [t26, hp, hi.2.1, mask_eq_zero, decide_eq_false_iff_not]
  show ¬ (0 < xval d.x s ∧ xval d.x s < d.b) ↔ _
  rw [hi.2.2]
  cases d.v <;> simp

/-! ## Out of range -/

theorem TB {d : DD} {s : State} (h : R2 d s ∧ s.gpr .r26 = 0) :
    WP isa (.block [.load .d .r27 .r23 80]) s (fun t => X7 d.x t) := by
  obtain ⟨⟨hb, he, -, -, -⟩, hz⟩ := h
  have hZ := hb.env.hZ
  have hk := hb.k64
  have hk' := hb.k1024
  have hwd : d.x.c.w = (d.x.c.k + 7) / 8 := rfl
  have e8 := Domain.slot_eq d.x.c.w 8
  have e28 := Domain.slot_eq d.x.c.w 28
  refine WP.mono (WP.keep [.r27] (Q := fun t => t.gpr .r27 = off d.x.O 0 ∧ t.mem = s.mem) (by
      prun [hb.r23, hb.env.hs.ld (d := 80) (n := 8) (by omega), he.wO]) (by decide)) fun t ⟨⟨a27, mt⟩, kt⟩ => ?_
  have k10 := (kt.gpr .r10 (by decide)).trans hb.env.h10
  have k29 := (kt.gpr .r29 (by decide)).trans hb.env.h29
  have k28 := (kt.gpr .r28 (by decide)).trans hb.r28
  have k23 := (kt.gpr .r23 (by decide)).trans hb.r23
  refine ⟨⟨a27, k10, k29, k28, k23, (kt.gpr .r11 (by decide)).trans hb.env.h11⟩, ?_⟩
  refine WP.mono (Pub.output_ok (b := false) (hb.env.hs.congr kt.wr) (he.scrO.congr kt.wr) k10 k29 k28 a27
    (by rw [kt.gpr .r26 (by decide), hz]; rfl) (by omega) (by omega) (by omega) he.sepO) fun u ⟨_, ku⟩ => ?_
  show u.gpr .r23 = d.x.c.S
  rw [ku.gpr .r23 (by decide), k23]

theorem TLi {d : DD} {s : State} (h : CF d.x.c s) (v : Nat) (hv : v < 2 ^ 15) :
    WP isa (.block [.li .r3 v]) s (fun t => CF d.x.c t) :=
  WP.mono (li_ok s v hv) fun t ⟨_, kt⟩ => by show t.gpr .r23 = _; rw [kt.gpr .r23 (by decide)]; exact h

theorem TSt {d : DD} {s : State} (h : CF d.x.c s) : WP isa (.block status) s (fun t => CF d.x.c t) := by
  refine WP.mono (WP.keep [.r0, .r3] (Q := fun _ => True) (by unfold status; prun; exact ⟨_, rfl⟩) (by decide))
    fun t ⟨_, kt⟩ => ?_
  show t.gpr .r23 = _
  rw [kt.gpr .r23 (by decide)]; exact h

/-! ## In range -/

theorem TG1 {d : DD} {s : State} (h : R2 d s ∧ s.gpr .r26 ≠ 0) :
    WP isa (.block [.add .r9 .r21 .r28]) s (G2 d) := by
  obtain ⟨⟨hb, he, hp, hv, -, hY⟩, -⟩ := h
  refine WP.mono (WP.keep [.r9] (Q := fun t => t.gpr .r9 = off d.x.c.D d.x.c.k ∧ t.mem = s.mem)
    (by prun [hb.r21, hb.r28]) (by decide)) fun t ⟨⟨a9, mt⟩, kt⟩ => ?_
  have hm : Body d.x.c.S d.x.c.w s.mem t.mem := by rw [mt]; exact Outside.refl _ _ _ _
  exact ⟨⟨hb.keep kt hm, (he.keep kt hm).ext (a9.trans hY.symm)⟩, by rw [arr, mt]; exact hp, hv⟩

theorem TG2 {d : DD} {s : State} (h : G2 d s) : WP isa exPre s (X5 d.x) := by
  obtain ⟨⟨hb, he⟩, hp, hv⟩ := h
  have hf := modulus_facts hv
  have hk := hb.k64
  have hk' := hb.k1024
  have hxk := he.xlk
  have hZ := hb.env.hZ
  have hnw := hb.env.hs.nowrap
  have hwd : d.x.c.w = (d.x.c.k + 7) / 8 := rfl
  have e0 := Domain.slot_eq d.x.c.w 0
  have e28 := Domain.slot_eq d.x.c.w 28
  have hpk : d.x.c.p < 256 ^ d.x.c.k := by
    have := VG.Proof.Bignum.os2ip_lt (d.x.c.db.take d.x.c.k)
    rwa [hb.take_len] at this
  refine WP.mono (exPower_split hb.env hb.r23 he.r9 hb.r28 (by omega) (by omega) he.xl1 (by omega) hb.rdY hb.sepY
    he.rdX he.sepX he.wX he.wXL (by rw [hp]; exact hf.1) (by rw [hp]; exact hf.2))
    fun s₆ ⟨⟨a30, a31, g10, g29, g11, g23, g28⟩, hw⟩ => ⟨⟨a30, a31, g10, g29, g11, g23, g28⟩, WP.mono hw
      fun t ⟨⟨z5, p5, b5, r10₅⟩, k5⟩ => ?_⟩
  have k29 := (k5.gpr .r29 (by decide)).trans hb.env.h29
  have k11 := (k5.gpr .r11 (by decide)).trans hb.env.h11
  have k23 := (k5.gpr .r23 (by decide)).trans hb.r23
  have k28 := (k5.gpr .r28 (by decide)).trans hb.r28
  refine ⟨⟨r10₅, k29, k11, k23, k28⟩, WP.mono (exOut_split (O := d.x.O) (hb.env.hs.congr k5.wr)
    (he.scrO.congr k5.wr) r10₅ k29 k11 k23 k28 hb.env.hw hb.env.hw' hZ (by omega) (by omega) ?_ he.sepO
    (by rw [p5, hp]; omega) (by rw [z5, p5]; exact Nat.mod_lt _ (by rw [hp]; omega)) (by rw [p5, hp]; exact hpk))
    fun s₃ ⟨⟨a27, b10, b29, b28, b23, b11⟩, hw'⟩ => ⟨⟨a27, b10, b29, b28, b23, b11⟩, WP.mono hw'
      fun u ⟨_, ku⟩ => (ku.gpr .r23 (by decide)).trans k23⟩⟩
  show word t.mem d.x.c.S 80 = _
  rw [Outside.word b5 (Or.inl (by omega)) (by omega)]; exact he.wO

/-! ## Constant time -/

/-! ## Constant time -/

theorem pins_Z1a : Pins Z1a (baseRegs ++ ([.r12, .r6] : List Reg)) := fun d s₁ s₂ h₁ h₂ =>
  pins_X1a (Φ := X1a) (fun _ _ h => h) d.x s₁ s₂ h₁.1 h₂.1

theorem pins_Z2 : Pins Z2 (baseRegs ++ ([.r12, .r6] : List Reg)) := fun d s₁ s₂ h₁ h₂ =>
  pins_X1a (Φ := X1a) (fun _ _ h => h) d.x s₁ s₂ h₁.1.1 h₂.1.1

theorem pins_Z3 : Pins Z3 (baseRegs ++ ([.r6, .r15, .r18] : List Reg)) := fun d s₁ s₂ h₁ h₂ =>
  pins_X3 d.x s₁ s₂ h₁.1 h₂.1

theorem dp_rel : RelCT isa (Two Z0) derivePublic fun _ _ => True := by
  unfold derivePublic
  refine RelCT.seq (R := Two ZB) (two_post (two_taint _ pins_Z0 (by taint_decide)) fun _ _ h => F0 h)
    (RelCT.seq (R := Two Z4) ?_
      (RelCT.seq (R := Two fun (d : DD) s => CF d.x.c s) ?_ (two_taint _ pins_ZCF (by taint_decide))))
  · unfold loadP Precompute.check
    exact RelCT.seq (two_post (two_taint _ (pins_xb (Φ := ZB) fun _ _ h => h.1) (by taint_decide)) fun _ _ h => F1 h)
      (RelCT.seq (two_post (two_taint _ pins_Z1a (by taint_decide)) fun _ _ h => F2 h)
        (RelCT.seq (two_post (two_taint _ pins_Z2 (by taint_decide)) fun _ _ h => F3 h)
          (two_post (two_taint _ pins_Z3 (by taint_decide)) fun _ _ h => F4 h)))
  · refine two_ite (Φ := Z4) (fun d s₁ s₂ h₁ h₂ => h₁.1.2.2.trans h₂.1.2.2.symm) ?_
      (two_post (two_taint _ (pins_xb (Φ := fun d s => Z4 d s ∧ s.gpr .r0 ≠ 0) fun _ _ h => h.1.1.1)
        (by taint_decide)) fun _ _ h => FK0 h)
    unfold dpBody xRange
    refine RelCT.seq (R := Two R2) (RelCT.seq
      (two_post (two_taint _ (pins_xb (Φ := fun d s => Z4 d s ∧ s.gpr .r0 = 0) fun _ _ h => h.1.1.1)
        (by taint_decide)) fun _ _ h => TR1 h)
      (two_post (two_taint _ pins_R1 (by taint_decide)) fun _ _ h => h.2)) ?_
    refine two_ite (Φ := R2) (fun d s₁ s₂ h₁ h₂ => h₁.2.2.2.2.1.trans h₂.2.2.2.2.1.symm) ?_ ?_
    · unfold dpBad
      exact RelCT.seq (two_post (two_taint _ (pins_base' (Φ := fun d s => R2 d s ∧ s.gpr .r26 = 0)
          fun _ _ h => h.1.1) (by taint_decide)) fun _ _ h => TB h)
        (RelCT.seq (two_post (two_taint _ (pins_x pins_X7) (by taint_decide)) fun _ _ h => h.2)
          (two_post (two_taint _ pins_ZCF (by taint_decide)) fun _ _ h => TLi h 2 (by decide)))
    · unfold dpGood exPower exOut
      exact RelCT.seq (two_post (two_taint _ (pins_base' (Φ := fun d s => R2 d s ∧ s.gpr .r26 ≠ 0)
          fun _ _ h => h.1.1) (by taint_decide)) fun _ _ h => TG1 h)
        (RelCT.seq (RelCT.seq (two_post (two_taint _ (pins_xb (Φ := G2) fun _ _ h => h.1) (by taint_decide))
            fun _ _ h => TG2 h)
          (two_post (two_taint _ (pins_x pins_X5) (by taint_decide)) fun _ _ h => h.2))
          (RelCT.seq (RelCT.seq (two_post (two_taint _ (pins_x pins_X6) (by taint_decide)) fun _ _ h => h.2)
              (two_post (two_taint _ (pins_x pins_X7) (by taint_decide)) fun _ _ h => h.2))
            (two_post (two_taint _ pins_ZCF (by taint_decide)) fun _ _ h => TSt h)))

/-- Bools equal when they are false together. -/
theorem bool_eq_of_false_iff {a b : Bool} (h : a = false ↔ b = false) : a = b := by
  cases a <;> cases b <;> simp_all

/-- Runs with the same public arguments and leakage have the same public
data. -/
theorem ddOf_eq {s t : State} (hs : dpContract.pre s) (h3 : s.gpr .r3 = t.gpr .r3) (h5 : s.gpr .r5 = t.gpr .r5)
    (h6 : s.gpr .r6 = t.gpr .r6) (h7 : s.gpr .r7 = t.gpr .r7) (h8 : s.gpr .r8 = t.gpr .r8)
    (h9 : s.gpr .r9 = t.gpr .r9) (h10 : s.gpr .r10 = t.gpr .r10) (a0 : stackArg s 0 = stackArg t 0)
    (hl : dpLeak s = dpLeak t) : ddOf s = ddOf t := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨hk, -⟩, hL, -⟩ := hs
  simp only [Spec.Ffdh.domainLenValid] at hL
  simp only [dpLeak] at hl
  obtain ⟨e1, e2⟩ := List.append_inj hl (by simp only [List.length_map, VG.Proof.Bignum.bytesAt_length, h6])
  have ed : Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat =
      Spec.Rsa.bytesAt t.mem (s.gpr .r5) (s.gpr .r6).toNat := by
    have := (List.map_inj_right (fun _ _ h => BitVec.eq_of_toNat_eq h)).mp e1
    rw [← h5, ← h6] at this; exact this
  have sl : ∀ o, o + (s.gpr .r7).toNat ≤ (s.gpr .r6).toNat →
      Spec.Rsa.bytesAt s.mem (s.gpr .r5 + BitVec.ofNat 64 o) (s.gpr .r7).toNat =
        Spec.Rsa.bytesAt t.mem (s.gpr .r5 + BitVec.ofNat 64 o) (s.gpr .r7).toNat := fun o ho => by
    rw [← VG.Proof.Dsa.bytesAt_slice s.mem _ ho, ← VG.Proof.Dsa.bytesAt_slice t.mem _ ho, ed]
  have hdx : dxOf s = dxOf t := by
    simp only [dxOf]
    rw [← h3, ← h5, ← h6, ← h7, ← h8, ← h9, ← h10, ← a0, ed]
    simp only [off]
    rw [sl _ (by omega)]
  have hbnd : bnd s.mem (s.gpr .r5) (s.gpr .r7).toNat (s.gpr .r6).toNat (dxOf s).c.p =
      bnd t.mem (t.gpr .r5) (t.gpr .r7).toNat (t.gpr .r6).toNat (dxOf t).c.p := by
    rw [← hdx, ← h5, ← h6, ← h7]
    exact (bnd_congr fun hq => (sl _ (by omega)).symm).symm
  have hp : ∀ m : Mem, Spec.Rsa.os2ip ((Spec.Rsa.bytesAt m (s.gpr .r5) (s.gpr .r6).toNat).take (s.gpr .r7).toNat) =
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (s.gpr .r5) (s.gpr .r7).toNat) := fun m => by
    rw [Proof.Ffdh.take_bytesAt _ _ (by omega)]
  have e3 := (Proof.Ffdh.PPC64LE.Derive.keyStatus_two _ _).symm.trans
    ((iff_of_eq (congrArg (· = 2) (List.cons.inj e2).1)).trans (Proof.Ffdh.PPC64LE.Derive.keyStatus_two _ _))
  rw [← h5, ← h6, ← h7, ← h8, ← h9] at e3
  rw [Proof.Ffdh.PPC64LE.Derive.privateValid_dom (by omega) (by omega),
    Proof.Ffdh.PPC64LE.Derive.privateValid_dom (by omega) (by omega)] at e3
  have hv := bool_eq_of_false_iff e3
  simp only [ddOf, DD.mk.injEq]
  refine ⟨hdx, hbnd, ?_⟩
  rw [← hdx, ← h5, ← h6, ← h7]
  have hpT : Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (s.gpr .r5) (s.gpr .r7).toNat) =
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r7).toNat) := by rw [← hp, ← hp, ed]
  have hbT : ∀ P, bnd t.mem (s.gpr .r5) (s.gpr .r7).toNat (s.gpr .r6).toNat P =
      bnd s.mem (s.gpr .r5) (s.gpr .r7).toNat (s.gpr .r6).toNat P := fun P =>
    bnd_congr fun hq => (sl _ (by omega)).symm
  rw [hpT, hbT] at hv
  rw [hbT, show (dxOf s).c.p = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r7).toNat) from hp s.mem]
  simp only [xval, dxOf]
  exact hv

theorem dp_ct : ConstantTime isa dpContract.pre dpContract.pub derivePublic :=
  RelCT.constantTime (dp_rel.mono (fun s _ ⟨hs, ht, hsp, h3, _, h5, h6, h7, h8, h9, h10, a0, hl⟩ =>
    ⟨ddOf s, ⟨hs, rfl⟩, ⟨ht, (ddOf_eq hs h3 h5 h6 h7 h8 h9 h10 a0 hl).symm⟩, hsp⟩) fun _ _ h => h)

end VG.Proof.Ffdh.PPC64LE.Derive
