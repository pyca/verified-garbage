module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.CheckPrivate.Fn
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.CheckPrivate.Front
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckDomainCT
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.CheckPrivate.Fn
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.CheckPrivate.Front
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckDomainCT
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Ffdh.PPC64LE.CheckPrivate.Body
import VerifiedGarbage.Proof.Ffdh.PPC64LE.CheckPrivate.Status
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.Body
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.CT
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.Status
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.ExchangeBody
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.DomainBody
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckPublicFn
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# `vg_ffdh_check_private` on PPC64LE: constant time

As `vg_ffdh_derive_public`'s (`Derive/CT.lean`), with the public data `KD`
(`kdOf`): the domain (g as `CD`'s y), x's address and length, y's address,
the bound on x and whether x is within it. p's load and check are the
domain check's pieces (`DA`, `DL`, `DC1`, `DC2`), each predicate stating that
the rest of the check reaches `K4` (`KB_loadP`); x's range as the
derivation's; the power and the comparison by `exPower_split` and
`cpCmp_split`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.CheckPrivate

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain VG.Impl.Ffdh.PPC64LE.Derive
open VG.Impl.Ffdh.PPC64LE.CheckPrivate
open VG.Proof.Ffdh.PPC64LE.Domain VG.Proof.Ffdh.PPC64LE.Derive
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.PPC64LE (Two Pins two_post two_taint)

/-- g's address, the bound and x's range, as the data has them. -/
def InvK (d : KD) (s : State) : Prop :=
  d.c.Y = off d.c.D d.c.k ∧ bnd s.mem d.c.D d.c.k d.c.L d.c.p = d.b ∧
    (0 < xvalK d s ∧ xvalK d s < d.b ↔ d.v = true)

theorem InvK.keep {d : KD} {s t : State} (h : InvK d s) (hb : Base d.c s) (he : ExtK d s)
    (hm : Body d.c.S d.c.w s.mem t.mem) : InvK d t := by
  have hZ := hb.env.hZ
  refine ⟨h.1, (bnd_congr fun hq => hm.bytesAt hZ fun i hi => by
    rw [off_off']; exact hb.sepD _ (by omega)).trans h.2.1, ?_⟩
  have ex : xvalK d t = xvalK d s := by simp only [xvalK]; rw [hm.bytesAt hZ he.sepX]
  rw [ex]; exact h.2.2

/-! ## The predicates -/

def K0 (d : KD) (s : State) : Prop := kpContract.pre s ∧ kdOf s = d

/-- From `cpFront` on. -/
def KB (d : KD) (s : State) : Prop := Base d.c s ∧ ExtK d s ∧ InvK d s

/-- After p's check. -/
def K4 (d : KD) (s : State) : Prop := E4 d.c s ∧ ExtK d s ∧ InvK d s

/-- With `loadN`'s arguments, and p's load and check to come. -/
def K1a (d : KD) (s : State) : Prop :=
  E1a d.c s ∧ WP isa (.seq Precompute.loadN Precompute.check) s (K4 d)

/-- After `loadN`. -/
def K2 (d : KD) (s : State) : Prop := E2 d.c s ∧ WP isa Precompute.check s (K4 d)

/-- After `check1`. -/
def K3 (d : KD) (s : State) : Prop := E3 d.c s ∧ WP isa Precompute.check2 s (K4 d)

/-- After x's range: `r26` is zero exactly when x is out of range. -/
def KR2 (d : KD) (s : State) : Prop :=
  Base d.c s ∧ ExtK d s ∧ arr s.mem d.c.S d.c.w 0 = d.c.p ∧ Spec.Rsa.modulusValid d.c.p d.c.k = true ∧
    (s.gpr .r26 = 0 ↔ d.v = false) ∧ d.c.Y = off d.c.D d.c.k

/-- After x's address and length are loaded. -/
def KR1 (d : KD) (s : State) : Prop :=
  (s.gpr .r10 = off d.c.S (slot d.c.w 4) ∧ s.gpr .r12 = off d.X 0 ∧ s.gpr .r6 = BitVec.ofNat 64 d.xl ∧
    s.gpr .r11 = BitVec.ofNat 64 (2 * d.c.w) ∧ s.gpr .r21 = d.c.D ∧ s.gpr .r23 = d.c.S ∧
    s.gpr .r27 = BitVec.ofNat 64 d.c.L ∧ s.gpr .r28 = BitVec.ofNat 64 d.c.k ∧
    s.gpr .r29 = BitVec.ofNat 64 (8 * (d.c.w + 2)) ∧ s.gpr .r31 = d.c.S) ∧
  WP isa (.seq xLoadRest xMask) s (KR2 d)

/-- Before the power: g's address in `r9`, and p checked. -/
def KG2 (d : KD) (s : State) : Prop :=
  Base d.c s ∧ ExtK d s ∧ arr s.mem d.c.S d.c.w 0 = d.c.p ∧ Spec.Rsa.modulusValid d.c.p d.c.k = true ∧
    s.gpr .r9 = d.c.Y

/-- Before the comparison's rest: its registers, and that it ends with the
working space in `r23`. -/
def V7 (d : KD) (s : State) : Prop :=
  (s.gpr .r12 = off d.Yv 0 ∧ s.gpr .r10 = off d.c.S (slot d.c.w 0) ∧ s.gpr .r11 = BitVec.ofNat 64 (2 * d.c.w) ∧
    s.gpr .r23 = d.c.S ∧ s.gpr .r28 = BitVec.ofNat 64 d.c.k ∧ s.gpr .r29 = BitVec.ofNat 64 (8 * (d.c.w + 2))) ∧
  WP isa cpTail s (CF d.c)

/-- After the power. -/
def V6 (d : KD) (s : State) : Prop :=
  (s.gpr .r10 = off d.c.S (slot d.c.w 0) ∧ s.gpr .r29 = BitVec.ofNat 64 (8 * (d.c.w + 2)) ∧
    s.gpr .r11 = BitVec.ofNat 64 (2 * d.c.w) ∧ s.gpr .r23 = d.c.S ∧ s.gpr .r28 = BitVec.ofNat 64 d.c.k) ∧
  WP isa (.block [.load .d .r12 .r23 80]) s (V7 d)

/-- After `exPre`. -/
def V5 (d : KD) (s : State) : Prop :=
  (s.gpr .r30 = off d.X 0 ∧ s.gpr .r31 = BitVec.ofNat 64 d.xl ∧ s.gpr .r10 = off d.c.S (slot d.c.w 0) ∧
    s.gpr .r29 = BitVec.ofNat 64 (8 * (d.c.w + 2)) ∧ s.gpr .r11 = BitVec.ofNat 64 (2 * d.c.w) ∧
    s.gpr .r23 = d.c.S ∧ s.gpr .r28 = BitVec.ofNat 64 d.c.k) ∧
  WP isa ModExp.powSecret s (V6 d)

/-! ## Pins -/

theorem pins_kbase {Φ : KD → State → Prop} (h : ∀ d s, Φ d s → Base d.c s) : Pins Φ baseRegs :=
  fun _ _ _ h₁ h₂ => (h _ _ h₁).pins (h _ _ h₂)

theorem pins_K0 : Pins K0 [.r10] := by
  rintro d s₁ s₂ ⟨-, h₁⟩ ⟨-, h₂⟩ r hr
  have e₁ := congrArg (fun d => d.c.S) h₁
  have e₂ := congrArg (fun d => d.c.S) h₂
  simp only [kdOf] at e₁ e₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  exact e₁.trans e₂.symm

theorem pins_K1a : Pins K1a (baseRegs ++ ([.r12, .r6] : List Reg)) := fun d s₁ s₂ h₁ h₂ =>
  pins_E1a (Φ := E1a) (fun _ _ h => h) d.c s₁ s₂ h₁.1 h₂.1

theorem pins_K2 : Pins K2 (baseRegs ++ ([.r12, .r6] : List Reg)) := fun d s₁ s₂ h₁ h₂ =>
  pins_E1a (Φ := E1a) (fun _ _ h => h) d.c s₁ s₂ h₁.1.1 h₂.1.1

theorem pins_K3 : Pins K3 (baseRegs ++ ([.r6, .r15, .r18] : List Reg)) := fun d s₁ s₂ h₁ h₂ =>
  pins_E3 d.c s₁ s₂ h₁.1 h₂.1

theorem pins_KR1 : Pins KR1 [.r6, .r10, .r11, .r12, .r21, .r23, .r27, .r28, .r29, .r31] := by
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

theorem pins_KG2 : Pins KG2 (baseRegs ++ ([.r9] : List Reg)) := by
  intro d s₁ s₂ h₁ h₂ r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact h₁.1.pins h₂.1 r hr
  · rw [List.mem_singleton] at hr; subst hr; rw [h₁.2.2.2.2, h₂.2.2.2.2]

theorem pins_V5 : Pins V5 [.r10, .r11, .r23, .r28, .r29, .r30, .r31] := by
  rintro d s₁ s₂ ⟨⟨a30, a31, a10, a29, a11, a23, a28⟩, -⟩ ⟨⟨b30, b31, b10, b29, b11, b23, b28⟩, -⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a10, b10]
  · rw [a11, b11]
  · rw [a23, b23]
  · rw [a28, b28]
  · rw [a29, b29]
  · rw [a30, b30]
  · rw [a31, b31]

theorem pins_V6 : Pins V6 [.r10, .r11, .r23, .r28, .r29] := by
  rintro d s₁ s₂ ⟨⟨a10, a29, a11, a23, a28⟩, -⟩ ⟨⟨b10, b29, b11, b23, b28⟩, -⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [a10, b10]
  · rw [a11, b11]
  · rw [a23, b23]
  · rw [a28, b28]
  · rw [a29, b29]

theorem pins_V7 : Pins V7 [.r10, .r11, .r12, .r23, .r28, .r29] := by
  rintro d s₁ s₂ ⟨⟨a12, a10, a11, a23, a28, a29⟩, -⟩ ⟨⟨b12, b10, b11, b23, b28, b29⟩, -⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a10, b10]
  · rw [a11, b11]
  · rw [a12, b12]
  · rw [a23, b23]
  · rw [a28, b28]
  · rw [a29, b29]

theorem pins_KCF : Pins (fun (d : KD) s => CF d.c s) [.r23] := by
  intro d s₁ s₂ h₁ h₂ r hr
  rw [List.mem_singleton] at hr; subst hr; exact h₁.trans h₂.symm

/-! ## The front and p's check -/

theorem KF0 {d : KD} {s : State} (h : K0 d s) : WP isa (.block cpFront) s (KB d) := by
  obtain ⟨hpre, rfl⟩ := h
  refine WP.mono (kp_front hpre) fun t ⟨hb, he, _, hby, _⟩ => ⟨hb, he, rfl,
    bnd_congr fun hq => hby _ _ fun i hi => by
      rw [off_off']; exact hb.sepD _ (by simp only [kdOf] at hq hi ⊢; omega), ?_⟩
  have ex : xvalK (kdOf s) t = xvalK (kdOf s) s := by simp only [xvalK]; rw [hby _ _ he.sepX]
  show 0 < xvalK (kdOf s) t ∧ xvalK (kdOf s) t < bnd s.mem (s.gpr .r3) (s.gpr .r5).toNat (s.gpr .r4).toNat
    (kdOf s).c.p ↔ decide _ = true
  rw [ex, decide_eq_true_iff]
  exact Iff.rfl

/-- p's load and check, from `KB`, by correctness. -/
theorem KB_loadP {d : KD} {s : State} (h : KB d s) : WP isa loadP s (K4 d) := by
  obtain ⟨hb, he, hi⟩ := h
  have hk := hb.k64
  refine WP.mono (loadP_ok hb.env hb.r21 hb.r28 rfl hk hb.k1024 (fun i hi => hb.rdD i (by have := hb.kL; omega))
    (fun i hi => hb.sepD i (by have := hb.kL; omega))) fun t ⟨⟨pt, ct, bt⟩, kt⟩ => ?_
  have ep : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem d.c.D d.c.k) = d.c.p := by
    rw [← Proof.Ffdh.take_bytesAt _ _ hb.kL, hb.bD]
  rw [ep] at pt ct
  exact ⟨⟨hb.keep kt bt, pt, ct⟩, he.keep kt bt, hi.keep hb he bt⟩

theorem KF1 {d : KD} {s : State} (h : KB d s) :
    WP isa (.block [.addi .r12 .r21 0, .addi .r6 .r28 0]) s (K1a d) :=
  wp_split (DA h.1) (KB_loadP h)

theorem KF2 {d : KD} {s : State} (h : K1a d s) : WP isa Precompute.loadN s (K2 d) :=
  wp_split (DL h.1) h.2

theorem KF3 {d : KD} {s : State} (h : K2 d s) : WP isa (.block Precompute.check1) s (K3 d) :=
  wp_split (DC1 h.1) h.2

theorem KF4 {d : KD} {s : State} (h : K3 d s) : WP isa Precompute.check2 s (K4 d) := h.2

theorem KLi {d : KD} {s : State} (h : Base d.c s) (v : Nat) (hv : v < 2 ^ 15) :
    WP isa (.block [.li .r3 v]) s (fun t => CF d.c t) :=
  WP.mono (li_ok s v hv) fun t ⟨_, kt⟩ => by show t.gpr .r23 = _; rw [kt.gpr .r23 (by decide)]; exact h.r23

/-! ## x's range -/

theorem KTR1 {d : KD} {s : State} (h : K4 d s ∧ s.gpr .r0 = 0) : WP isa (.block xLoadPre) s (KR1 d) := by
  obtain ⟨⟨⟨hb, hp, h0⟩, he, hi⟩, hz⟩ := h
  have hv := h0.mp hz
  have hf := modulus_facts hv
  have hk := hb.k64
  have hk' := hb.k1024
  have hZ := hb.env.hZ
  have hwd : d.c.w = (d.c.k + 7) / 8 := rfl
  have e28 := Domain.slot_eq d.c.w 28
  have rdQ : d.c.L = 3 * d.c.k → ∀ i < d.c.k, InRegions (s.rd ++ s.wr) (off (off d.c.D (2 * d.c.k)) i) 1 :=
    fun hq i hi => by rw [off_off']; exact hb.rdD _ (by omega)
  have sepQ : d.c.L = 3 * d.c.k → ∀ i < d.c.k, ∀ y, ofs d.c.S y < d.c.Z →
      off (off d.c.D (2 * d.c.k)) i ≠ y := fun hq i hi => by rw [off_off']; exact hb.sepD _ (by omega)
  have hrange := xRange_ok hb.env hb.r23 hb.r21 hb.r27 hb.r28 (by omega) (by omega)
    (by rcases hb.hL with h | h <;> omega) (by omega) he.xl1 he.xlk he.wX he.wXL he.rdX he.sepX rdQ sepQ
    (by rw [hp]; omega)
  unfold xRange at hrange
  refine wp_split (WP.mono (xLoadPre_ok hb.env hb.r23 he.wX he.wXL) fun t ⟨⟨a10, a12, a6, _⟩, kt⟩ =>
    ⟨a10, a12, a6, (kt.gpr .r11 (by decide)).trans hb.env.h11, (kt.gpr .r21 (by decide)).trans hb.r21,
      (kt.gpr .r23 (by decide)).trans hb.r23, (kt.gpr .r27 (by decide)).trans hb.r27,
      (kt.gpr .r28 (by decide)).trans hb.r28, (kt.gpr .r29 (by decide)).trans hb.env.h29,
      (kt.gpr .r31 (by decide)).trans hb.env.h31⟩) (WP.mono hrange fun t ⟨⟨t26, tp, tb, t10⟩, kt⟩ => ?_)
  have hb' : Base d.c t := Base.of hb (fun r hr => by
      simp only [baseRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [t10, hb.env.h10]
      all_goals exact kt.gpr _ (by decide)) kt.rd kt.wr tb
  refine ⟨hb', he.keep kt tb, by rw [tp, hp], hv, ?_, hi.1⟩
  rw [t26, hp, hi.2.1, mask_eq_zero, decide_eq_false_iff_not]
  show ¬ (0 < xvalK d s ∧ xvalK d s < d.b) ↔ _
  rw [hi.2.2]
  cases d.v <;> simp

/-! ## In range -/

theorem KG1 {d : KD} {s : State} (h : KR2 d s ∧ s.gpr .r26 ≠ 0) :
    WP isa (.block [.add .r9 .r21 .r28]) s (KG2 d) := by
  obtain ⟨⟨hb, he, hp, hv, -, hY⟩, -⟩ := h
  refine WP.mono (WP.keep [.r9] (Q := fun t => t.gpr .r9 = off d.c.D d.c.k ∧ t.mem = s.mem)
    (by prun [hb.r21, hb.r28]) (by decide)) fun t ⟨⟨a9, mt⟩, kt⟩ => ?_
  have hm : Body d.c.S d.c.w s.mem t.mem := by rw [mt]; exact Outside.refl _ _ _ _
  exact ⟨hb.keep kt hm, he.keep kt hm, by rw [arr, mt]; exact hp, hv, a9.trans hY.symm⟩

theorem KG3 {d : KD} {s : State} (h : KG2 d s) : WP isa exPre s (V5 d) := by
  obtain ⟨hb, he, hp, hv, h9⟩ := h
  have hf := modulus_facts hv
  have hk := hb.k64
  have hk' := hb.k1024
  have hxk := he.xlk
  have hZ := hb.env.hZ
  have hnw := hb.env.hs.nowrap
  have hwd : d.c.w = (d.c.k + 7) / 8 := rfl
  have e0 := Domain.slot_eq d.c.w 0
  have e28 := Domain.slot_eq d.c.w 28
  refine WP.mono (exPower_split hb.env hb.r23 h9 hb.r28 (by omega) (by omega) he.xl1 (by omega) hb.rdY hb.sepY
    he.rdX he.sepX he.wX he.wXL (by rw [hp]; exact hf.1) (by rw [hp]; exact hf.2))
    fun s₆ ⟨⟨a30, a31, g10, g29, g11, g23, g28⟩, hw⟩ => ⟨⟨a30, a31, g10, g29, g11, g23, g28⟩, WP.mono hw
      fun t ⟨⟨_, p5, b5, r10₅⟩, k5⟩ => ?_⟩
  have k29 := (k5.gpr .r29 (by decide)).trans hb.env.h29
  have k11 := (k5.gpr .r11 (by decide)).trans hb.env.h11
  have k23 := (k5.gpr .r23 (by decide)).trans hb.r23
  have k28 := (k5.gpr .r28 (by decide)).trans hb.r28
  refine ⟨⟨r10₅, k29, k11, k23, k28⟩, WP.mono (cpCmp_split (Yv := d.Yv) (hb.env.hs.congr k5.wr) r10₅ k29 k11 k23
    k28 ?_ hb.env.hw hb.env.hw' hZ (by omega) (by omega) (by rw [k5.rd, k5.wr]; exact he.rdY) he.sepY
    (by rw [p5, hp]; omega)) fun s₁ ⟨regs, hw'⟩ => ⟨regs, WP.mono hw' fun u ⟨⟨_, _, u23⟩, _⟩ => u23⟩⟩
  show word t.mem d.c.S 80 = _
  rw [Outside.word b5 (Or.inl (by omega)) (by omega)]; exact he.wY

/-! ## Constant time -/

theorem kp_rel : RelCT isa (Two K0) checkPrivate fun _ _ => True := by
  unfold checkPrivate
  refine RelCT.seq (R := Two KB) (two_post (two_taint _ pins_K0 (by taint_decide)) fun _ _ h => KF0 h)
    (RelCT.seq (R := Two K4) ?_
      (RelCT.seq (R := Two fun (d : KD) s => CF d.c s) ?_ (two_taint _ pins_KCF (by taint_decide))))
  · unfold loadP Precompute.check
    exact RelCT.seq (two_post (two_taint _ (pins_kbase (Φ := KB) fun _ _ h => h.1) (by taint_decide))
        fun _ _ h => KF1 h)
      (RelCT.seq (two_post (two_taint _ pins_K1a (by taint_decide)) fun _ _ h => KF2 h)
        (RelCT.seq (two_post (two_taint _ pins_K2 (by taint_decide)) fun _ _ h => KF3 h)
          (two_post (two_taint _ pins_K3 (by taint_decide)) fun _ _ h => KF4 h)))
  · refine two_ite (Φ := K4) (fun d s₁ s₂ h₁ h₂ => h₁.1.2.2.trans h₂.1.2.2.symm) ?_
      (two_post (two_taint _ (pins_kbase (Φ := fun d s => K4 d s ∧ s.gpr .r0 ≠ 0) fun _ _ h => h.1.1.1)
        (by taint_decide)) fun _ _ h => KLi h.1.1.1 0 (by decide))
    unfold cpBody xRange
    refine RelCT.seq (R := Two KR2) (RelCT.seq
      (two_post (two_taint _ (pins_kbase (Φ := fun d s => K4 d s ∧ s.gpr .r0 = 0) fun _ _ h => h.1.1.1)
        (by taint_decide)) fun _ _ h => KTR1 h)
      (two_post (two_taint _ pins_KR1 (by taint_decide)) fun _ _ h => h.2)) ?_
    refine two_ite (Φ := KR2) (fun d s₁ s₂ h₁ h₂ => h₁.2.2.2.2.1.trans h₂.2.2.2.2.1.symm) ?_ ?_
    · exact two_post (two_taint _ (pins_kbase (Φ := fun d s => KR2 d s ∧ s.gpr .r26 = 0) fun _ _ h => h.1.1)
        (by taint_decide)) fun _ _ h => KLi h.1.1 2 (by decide)
    · unfold cpGood exPower cpCmp
      exact RelCT.seq (two_post (two_taint _ (pins_kbase (Φ := fun d s => KR2 d s ∧ s.gpr .r26 ≠ 0)
          fun _ _ h => h.1.1) (by taint_decide)) fun _ _ h => KG1 h)
        (RelCT.seq (RelCT.seq (two_post (two_taint _ pins_KG2 (by taint_decide)) fun _ _ h => KG3 h)
          (two_post (two_taint _ pins_V5 (by taint_decide)) fun _ _ h => h.2))
          (RelCT.seq (two_post (two_taint _ pins_V6 (by taint_decide)) fun _ _ h => h.2)
            (two_post (two_taint _ pins_V7 (by taint_decide)) fun _ _ h => h.2)))

/-- The status is 2 exactly when x is out of range. -/
theorem privateStatus_two (a : Spec.Ffdh.Parameters) (y x : Nat) :
    Spec.Ffdh.privateStatus a y x = 2 ↔ Spec.Ffdh.privateValid a x = false := by
  unfold Spec.Ffdh.privateStatus
  cases Spec.Ffdh.privateValid a x
  · simp
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    split <;> simp

/-- Runs with the same public arguments and leakage have the same public
data. -/
theorem kdOf_eq {s t : State} (hs : kpContract.pre s) (h3 : s.gpr .r3 = t.gpr .r3) (h4 : s.gpr .r4 = t.gpr .r4)
    (h5 : s.gpr .r5 = t.gpr .r5) (h6 : s.gpr .r6 = t.gpr .r6) (h7 : s.gpr .r7 = t.gpr .r7)
    (h8 : s.gpr .r8 = t.gpr .r8) (h9 : s.gpr .r9 = t.gpr .r9) (h10 : s.gpr .r10 = t.gpr .r10)
    (a0 : stackArg s 0 = stackArg t 0) (hl : kpLeak s = kpLeak t) : kdOf s = kdOf t := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, ⟨hk, -⟩, hL, -⟩ := hs
  simp only [Spec.Ffdh.domainLenValid] at hL
  simp only [kpLeak] at hl
  obtain ⟨e12, e3⟩ := List.append_inj hl (by
    simp only [List.length_append, List.length_map, VG.Proof.Bignum.bytesAt_length, h4, h7])
  obtain ⟨e1, e2⟩ := List.append_inj e12 (by simp only [List.length_map, VG.Proof.Bignum.bytesAt_length, h4])
  have ed : Spec.Rsa.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat =
      Spec.Rsa.bytesAt t.mem (s.gpr .r3) (s.gpr .r4).toNat := by
    have := (List.map_inj_right (fun _ _ h => BitVec.eq_of_toNat_eq h)).mp e1
    rw [← h3, ← h4] at this; exact this
  have sl : ∀ o, o + (s.gpr .r5).toNat ≤ (s.gpr .r4).toNat →
      Spec.Rsa.bytesAt s.mem (s.gpr .r3 + BitVec.ofNat 64 o) (s.gpr .r5).toNat =
        Spec.Rsa.bytesAt t.mem (s.gpr .r3 + BitVec.ofNat 64 o) (s.gpr .r5).toNat := fun o ho => by
    rw [← VG.Proof.Dsa.bytesAt_slice s.mem _ ho, ← VG.Proof.Dsa.bytesAt_slice t.mem _ ho, ed]
  have hp : ∀ m : Mem, Spec.Rsa.os2ip ((Spec.Rsa.bytesAt m (s.gpr .r3) (s.gpr .r4).toNat).take (s.gpr .r5).toNat) =
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (s.gpr .r3) (s.gpr .r5).toNat) := fun m => by
    rw [Proof.Ffdh.take_bytesAt _ _ (by omega)]
  have hpT : Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (s.gpr .r3) (s.gpr .r5).toNat) =
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r3) (s.gpr .r5).toNat) := by rw [← hp, ← hp, ed]
  have hbT : ∀ P, bnd t.mem (s.gpr .r3) (s.gpr .r5).toNat (s.gpr .r4).toNat P =
      bnd s.mem (s.gpr .r3) (s.gpr .r5).toNat (s.gpr .r4).toNat P := fun P =>
    bnd_congr fun hq => (sl _ (by omega)).symm
  have e4 := (privateStatus_two _ _ _).symm.trans
    ((iff_of_eq (congrArg (· = 2) (List.cons.inj e3).1)).trans (privateStatus_two _ _ _))
  rw [← h3, ← h4, ← h5, ← h8, ← h9] at e4
  rw [Proof.Ffdh.PPC64LE.Derive.privateValid_dom (by omega) (by omega),
    Proof.Ffdh.PPC64LE.Derive.privateValid_dom (by omega) (by omega), hpT, hbT] at e4
  have hv := bool_eq_of_false_iff e4
  have ext : ∀ a b : KD, a.c = b.c → a.X = b.X → a.xl = b.xl → a.Yv = b.Yv → a.b = b.b → a.v = b.v → a = b := by
    rintro ⟨⟩ ⟨⟩; simp_all
  have hc : (kdOf s).c = (kdOf t).c := by
    simp only [kdOf]
    rw [← h3, ← h4, ← h5, ← h10, ← a0, ed]
    simp only [off]
    rw [sl _ (by omega)]
  refine ext _ _ hc (by simp only [kdOf, h8]) (by simp only [kdOf, h9]) (by simp only [kdOf, h6]) ?_ ?_
  · show bnd s.mem _ _ _ (kdOf s).c.p = bnd t.mem _ _ _ (kdOf t).c.p
    rw [← hc, ← h3, ← h4, ← h5, hbT]
  · show decide _ = decide _
    rw [← h3, ← h4, ← h5, ← h8, ← h9]
    simp only [CD.p, hp, hpT, hbT]
    exact hv

theorem kp_ct : ConstantTime isa kpContract.pre kpContract.pub checkPrivate :=
  RelCT.constantTime (kp_rel.mono (fun s _ ⟨hs, ht, hsp, h3, h4, h5, h6, h7, h8, h9, h10, a0, hl⟩ =>
    ⟨kdOf s, ⟨hs, rfl⟩, ⟨ht, (kdOf_eq hs h3 h4 h5 h6 h7 h8 h9 h10 a0 hl).symm⟩, hsp⟩) fun _ _ h => h)

end VG.Proof.Ffdh.PPC64LE.CheckPrivate
