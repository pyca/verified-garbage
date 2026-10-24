module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.Fn
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.Body
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.CT
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.Fn
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.Body
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.CT
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.Front
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.Front
import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.ScalarEq
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.Status
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.ExchangeCorrect
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckPublicFn
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubCorrect
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreWrite
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# `vg_ffdh_generate_key` on PPC64LE: constant time

The public data `GD` is `vg_ffdh_derive_public`'s (`Derive.DD`) for x's and
`y`'s buffers, the bound and whether x is within it, and `rand`'s address.
The front and p's check are as `vg_ffdh_derive_public`'s; x's cut runs
without a branch on the domain and the pointers (`scalarRest`); the rest is
`vg_ffdh_derive_public`'s body (`Derive.dpBody_rel`) and x's mask, without a
branch.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.GenerateKey

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain VG.Impl.Ffdh.PPC64LE.GenerateKey
open VG.Proof.Ffdh.PPC64LE.Domain VG.Proof.Ffdh.PPC64LE.Derive
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.PPC64LE (Two Pins two_post two_taint)

/-- The exchange's data of a run: the domain and g, x's and `y`'s buffers. -/
def gxOf (s : State) : XD := ⟨gcOf s, s.gpr .r5, s.gpr .r3, (s.gpr .r9).toNat⟩

/-- The public data of a run. -/
structure GD where
  d : DD
  R : Addr

/-- x's octets as the code cuts them from the memory `m`. -/
abbrev gOct (g : GD) (m : Mem) : List Byte := gkOct m g.d.x.c.D g.R g.d.x.c.k g.d.x.c.L

def gdOf (s : State) : GD :=
  ⟨⟨gxOf s, Derive.bnd s.mem (s.gpr .r7) (s.gpr .r9).toNat (s.gpr .r8).toNat (gcOf s).p,
    decide (0 < gkScalar s ∧ gkScalar s < Derive.bnd s.mem (s.gpr .r7) (s.gpr .r9).toNat (s.gpr .r8).toNat (gcOf s).p)⟩,
    s.gpr .r10⟩

/-- What holds of `rand`, x and `y` beyond `Ext`, kept by changes to the
working space: the header's word 11, the separations, the bound and x's range. -/
structure KE (g : GD) (s : State) : Prop where
  wR : s.mem.readW (off g.d.x.c.S 88) 64 = off g.R 0
  rdR : ∀ i < g.d.x.c.k, InRegions (s.rd ++ s.wr) (off g.R i) 1
  sepR : ∀ i < g.d.x.c.k, ∀ y, ofs g.d.x.c.S y < g.d.x.c.Z → off g.R i ≠ y
  scrX : Scr s g.d.x.X g.d.x.c.k
  sepBX : ∀ y, ofs g.d.x.c.S y < g.d.x.c.Z → g.d.x.c.k ≤ ofs g.d.x.X y
  sepRX : ∀ i < g.d.x.c.k, ∀ y, ofs g.d.x.X y < g.d.x.c.k → off g.R i ≠ y
  sepDX : ∀ i < g.d.x.c.L, ∀ y, ofs g.d.x.X y < g.d.x.c.k → off g.d.x.c.D i ≠ y
  sepXO : ∀ i < g.d.x.c.k, ∀ y, ofs g.d.x.O y < g.d.x.c.k → off g.d.x.X i ≠ y
  sepOX : ∀ i < g.d.x.c.k, ∀ y, ofs g.d.x.X y < g.d.x.c.k → off g.d.x.O i ≠ y
  sepB : ∀ y, ofs g.d.x.c.S y < g.d.x.c.Z → g.d.x.c.k ≤ ofs g.d.x.O y
  xlk : g.d.x.xl = g.d.x.c.k
  hY : g.d.x.c.Y = off g.d.x.c.D g.d.x.c.k
  bnd : Derive.bnd s.mem g.d.x.c.D g.d.x.c.k g.d.x.c.L g.d.x.c.p = g.d.b
  rng : Spec.Rsa.modulusValid g.d.x.c.p g.d.x.c.k = true →
    (0 < Spec.Rsa.os2ip (gOct g s.mem) ∧ Spec.Rsa.os2ip (gOct g s.mem) < g.d.b ↔ g.d.v = true)

/-- `KE` across a change of memory that keeps the bytes of the domain and of
`rand` and the header's word 11. -/
theorem KE.of_bytes {g : GD} {s t : State} (h : KE g s) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (hw : t.mem.readW (off g.d.x.c.S 88) 64 = s.mem.readW (off g.d.x.c.S 88) 64)
    (hD : ∀ (Q : Addr) n, (∀ i < n, ∃ j < g.d.x.c.L, off Q i = off g.d.x.c.D j) →
      Spec.Rsa.bytesAt t.mem Q n = Spec.Rsa.bytesAt s.mem Q n)
    (hR : Spec.Rsa.bytesAt t.mem g.R g.d.x.c.k = Spec.Rsa.bytesAt s.mem g.R g.d.x.c.k)
    (hL : g.d.x.c.L = 2 * g.d.x.c.k ∨ g.d.x.c.L = 3 * g.d.x.c.k) : KE g t where
  wR := hw.trans h.wR
  rdR := by rw [hrd, hwr]; exact h.rdR
  sepR := h.sepR
  scrX := h.scrX.congr hwr
  sepBX := h.sepBX
  sepRX := h.sepRX
  sepDX := h.sepDX
  sepXO := h.sepXO
  sepOX := h.sepOX
  sepB := h.sepB
  xlk := h.xlk
  hY := h.hY
  bnd := (bnd_congr fun hq => hD _ _ fun i hi => ⟨2 * g.d.x.c.k + i, by omega, by rw [off_off']⟩).trans h.bnd
  rng := by
    have e : gOct g t.mem = gOct g s.mem := by
      unfold gOct gkOct
      rw [hR, hD _ _ fun i hi => by
        unfold bptr
        split
        · exact ⟨2 * g.d.x.c.k + i, by omega, by rw [off_off']⟩
        · exact ⟨i, by omega, rfl⟩]
    intro hv; rw [e]; exact h.rng hv

/-- `KE` across a change of the working space. -/
theorem KE.keep {g : GD} {s t : State} {rs : List Reg} (h : KE g s) (hb : Base g.d.x.c s) (k : Keep rs s t)
    (hm : Body g.d.x.c.S g.d.x.c.w s.mem t.mem) : KE g t := by
  have hZ := hb.env.hZ
  have e0 := Domain.slot_eq g.d.x.c.w 0
  refine h.of_bytes k.rd k.wr (by show word t.mem _ 88 = word s.mem _ 88; rw [Outside.word hm (Or.inl (by omega))
    (by omega)]) (fun Q n hq => hm.bytesAt hZ fun i hi y hy e => ?_) (hm.bytesAt hZ h.sepR) hb.hL
  obtain ⟨j, hj, ej⟩ := hq i hi
  exact hb.sepD j hj y hy (ej ▸ e)

/-- `KE` across a change of x's octets. -/
theorem KE.outX {g : GD} {s t : State} {rs : List Reg} (h : KE g s) (hb : Base g.d.x.c s) (k : Keep rs s t)
    (ho : Outside g.d.x.X 0 g.d.x.c.k s.mem t.mem) : KE g t := by
  have hZ := hb.env.hZ
  have hnw := hb.env.hs.nowrap
  have e28 := Domain.slot_eq g.d.x.c.w 28
  refine h.of_bytes k.rd k.wr (Outside.word_sep (d := 88) ho h.sepBX (by omega) (by omega) hnw)
    (fun Q n hq => outside_bytesAt (Z := g.d.x.c.k) ho (by omega) fun i hi y hy e => ?_)
    (outside_bytesAt (Z := g.d.x.c.k) ho (by omega) h.sepRX) hb.hL
  obtain ⟨j, hj, ej⟩ := hq i hi
  exact h.sepDX j hj y hy (ej ▸ e)

/-! ## The predicates -/

def K0 (g : GD) (s : State) : Prop := gkContract.pre s ∧ gdOf s = g

/-- From the front on. -/
def KB (g : GD) (s : State) : Prop := XB g.d.x s ∧ KE g s

/-- The front after the working space's address. -/
def gkRest : List Instr :=
  save .r11 ++ ([.store .d .r3 .r23 64, .store .d .r4 .r23 72, .store .d .r5 .r23 80, .store .d .r10 .r23 88,
    .addi .r3 .r7 0, .addi .r4 .r8 0, .addi .r5 .r9 0] ++ (setup ++ [.add .r9 .r21 .r28]))

theorem gkFront_eq : gkFront = [.addSp .r11 104, .load .d .r11 .r11 0] ++ gkRest := by
  simp only [gkFront, gkRest, List.append_assoc, List.cons_append, List.nil_append]

/-- After loading the working space's address, with the rest of the front to come. -/
def KL1 (g : GD) (s : State) : Prop :=
  (∃ s₀, K0 g s₀ ∧ s.gpr .r11 = stackArg s₀ 1) ∧ WP isa (.block gkRest) s (KB g)

/-- After p's check. -/
def K4 (g : GD) (s : State) : Prop := X4 g.d.x s ∧ KE g s

/-- The front, by correctness: `KB` of the run's data. -/
theorem front_kb {s : State} (h : gkContract.pre s) : WP isa (.block gkFront) s (KB (gdOf s)) := by
  have hpre := h
  obtain ⟨-, hrd, hwr, dXY, dXD, dXR, dXS, -, dYD, -, dYS, -, dDS, dRS, -, nwX, nwY, -, nwR, nwS, ⟨hk, hk'⟩, hL,
    hxl, hyl, hrl, hsl⟩ := h
  rw [hxl] at hwr dXY dXD dXR dXS nwX
  rw [hyl] at hwr dXY dYD dYS nwY
  rw [hrl] at hrd dXR dRS nwR
  refine WP.mono (gk_front hpre) fun t ⟨hb, h9, w8, w9, w10, w11, _, hby, kt⟩ => ?_
  dsimp only [KB, gdOf, gxOf]
  have h4 : s.gpr .r4 = BitVec.ofNat 64 (s.gpr .r9).toNat := by rw [← hxl, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hLk : (s.gpr .r8).toNat = 2 * (s.gpr .r9).toNat ∨ (s.gpr .r8).toNat = 3 * (s.gpr .r9).toNat := by
    simp only [Spec.Ffdh.domainLenValid] at hL; omega
  have sepD := sep_of_disjoint dDS (by omega)
  have sXS := sep_of_disjoint (L := (s.gpr .r9).toNat) dXS (by omega)
  have sRS := sep_of_disjoint (L := (s.gpr .r9).toNat) dRS (by omega)
  have sXR := sep_of_disjoint (L := (s.gpr .r9).toNat) dXR.symm (by omega)
  have sXD := sep_of_disjoint (L := (s.gpr .r8).toNat) dXD.symm (by omega)
  have sXY := sep_of_disjoint (L := (s.gpr .r9).toNat) dXY (by omega)
  have sYX := sep_of_disjoint (L := (s.gpr .r9).toNat) dXY.symm (by omega)
  have scY : Scr t (s.gpr .r5) (s.gpr .r9).toNat := Scr.of_mem (by rw [kt.wr, hwr]; simp) nwY
  have scX : Scr t (s.gpr .r3) (s.gpr .r9).toNat := Scr.of_mem (by rw [kt.wr, hwr]; simp) nwX
  refine ⟨⟨hb, ⟨h9, ?_, ?_, ?_, fun i hi => ?_, sXS, scY, Pub.sep_of_disjoint dYS, show 1 ≤ (s.gpr .r9).toNat by omega,
    Nat.le_refl _⟩⟩, ⟨?_, fun i hi => ?_, sRS, scX, Pub.sep_of_disjoint dXS.symm, sXR, sXD, sXY, sYX,
    Pub.sep_of_disjoint dYS.symm, rfl, rfl, ?_, ?_⟩⟩
  · show word t.mem (stackArg s 1) 64 = off (s.gpr .r3) 0; rw [w8]; simp [off]
  · show word t.mem (stackArg s 1) 72 = BitVec.ofNat 64 (s.gpr .r9).toNat; rw [w9, h4]
  · show word t.mem (stackArg s 1) 80 = off (s.gpr .r5) 0; rw [w10]; simp [off]
  · exact scX.ld (d := i) (n := 1) (by show i + 1 ≤ (s.gpr .r9).toNat; exact hi)
  · show word t.mem (stackArg s 1) 88 = off (s.gpr .r10) 0; rw [w11]; simp [off]
  · rw [kt.rd, kt.wr]
    exact rd_of_mem (s := s) (D := s.gpr .r10) (L := (s.gpr .r9).toNat) (by rw [hrd]; simp) (by omega) i hi
  · show Derive.bnd t.mem (s.gpr .r7) (s.gpr .r9).toNat (s.gpr .r8).toNat (gcOf s).p = _
    exact bnd_congr fun hq => hby _ _ fun i hi => by rw [off_off']; exact sepD _ (by omega)
  · intro hv
    show 0 < Spec.Rsa.os2ip (gkOct t.mem (s.gpr .r7) (s.gpr .r10) (s.gpr .r9).toNat (s.gpr .r8).toNat) ∧
      Spec.Rsa.os2ip (gkOct t.mem (s.gpr .r7) (s.gpr .r10) (s.gpr .r9).toNat (s.gpr .r8).toNat) <
        Derive.bnd s.mem (s.gpr .r7) (s.gpr .r9).toNat (s.gpr .r8).toNat (gcOf s).p ↔ (gdOf s).d.v = true
    have e : gkOct t.mem (s.gpr .r7) (s.gpr .r10) (s.gpr .r9).toNat (s.gpr .r8).toNat =
        gkOct s.mem (s.gpr .r7) (s.gpr .r10) (s.gpr .r9).toNat (s.gpr .r8).toNat := by
      unfold gkOct
      rw [hby _ _ (sep_of_disjoint dRS (by omega)), hby _ _ fun i hi => by
        unfold bptr; split
        · rw [off_off']; exact sepD _ (by omega)
        · exact sepD _ (by omega)]
    have ep : (gcOf s).p = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r9).toNat) := by
      show Spec.Rsa.os2ip ((Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat).take (s.gpr .r9).toNat) = _
      rw [Proof.Ffdh.take_bytesAt _ _ (by omega)]
    have hf := modulus_facts hv
    rw [ep] at hf
    rw [e, gkOct_eq s.mem _ _ (by omega) hLk fun _ => ⟨hf.2, by omega⟩]
    show _ ↔ decide (0 < gkScalar s ∧ gkScalar s < _) = true
    unfold gkScalar
    rw [hrl]
    exact decide_eq_true_iff.symm

/-! ## Pins -/

theorem pins_gx {Φ : GD → State → Prop} (h : ∀ g s, Φ g s → XB g.d.x s) :
    Pins Φ (baseRegs ++ ([.r9] : List Reg)) := fun g s₁ s₂ h₁ h₂ =>
  pins_XB (Φ := XB) (fun _ _ h => h) g.d.x s₁ s₂ (h _ _ h₁) (h _ _ h₂)

theorem pins_K0 : Pins K0 ([] : List Reg) := fun _ _ _ _ _ _ hr => absurd hr List.not_mem_nil

theorem pins_KL1 : Pins KL1 [.r11] := by
  rintro g s₁ s₂ ⟨⟨a, ⟨-, ha⟩, h1⟩, -⟩ ⟨⟨b, ⟨-, hb⟩, h2⟩, -⟩ r hr
  rw [List.mem_singleton] at hr; subst hr
  rw [h1, h2]
  exact (congrArg (fun g : GD => g.d.x.c.S) ha).trans (congrArg (fun g : GD => g.d.x.c.S) hb).symm

theorem pins_gCF : Pins (fun (g : GD) s => CF g.d.x.c s) [.r23] := fun g s₁ s₂ h₁ h₂ =>
  pins_XCF g.d.x s₁ s₂ h₁ h₂

/-! ## The front and p's check -/

theorem KL1_of {g : GD} {s : State} (h : K0 g s) :
    WP isa (.block ([.addSp .r11 104, .load .d .r11 .r11 0] : List Instr)) s (KL1 g) := by
  obtain ⟨hpre, rfl⟩ := h
  have hA1 : InRegions (s.rd ++ s.wr) (stackArgAddr s 1) 8 := by
    refine ⟨gkStack s, List.mem_append_left _ (by rw [hpre.2.1]; simp), ?_⟩
    show (⟨s.sp + BitVec.ofNat 64 96, 24⟩ : Region).Contains (s.sp + BitVec.ofNat 64 104) 8
    rw [show s.sp + BitVec.ofNat 64 104 = s.sp + BitVec.ofNat 64 96 + BitVec.ofNat 64 8 by rw [Offset.add_add]]
    exact Offset.contains_base _ (by omega) (by omega)
  have hf := front_kb hpre
  rw [gkFront_eq, WP.block_append_iff] at hf
  exact WP.mono (WP.and (loadS1_ok s hA1) hf) fun t ⟨⟨⟨a11, _⟩, _⟩, hw⟩ => ⟨⟨s, ⟨hpre, rfl⟩, a11⟩, hw⟩

def K1a (g : GD) (s : State) : Prop := X1a g.d.x s ∧ WP isa (.seq Precompute.loadN Precompute.check) s (K4 g)

def K2 (g : GD) (s : State) : Prop := X2 g.d.x s ∧ WP isa Precompute.check s (K4 g)

def K3 (g : GD) (s : State) : Prop := X3 g.d.x s ∧ WP isa Precompute.check2 s (K4 g)

/-- p's load and check, from `KB`, by correctness. -/
theorem KB_loadP {g : GD} {s : State} (h : KB g s) : WP isa loadP s (K4 g) := by
  obtain ⟨⟨hb, he⟩, hi⟩ := h
  have hk := hb.k64
  refine WP.mono (loadP_ok hb.env hb.r21 hb.r28 rfl hk hb.k1024 (fun i hi => hb.rdD i (by have := hb.kL; omega))
    (fun i hi => hb.sepD i (by have := hb.kL; omega))) fun t ⟨⟨pt, ct, bt⟩, kt⟩ => ?_
  have ep : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem g.d.x.c.D g.d.x.c.k) = g.d.x.c.p := by
    rw [← Proof.Ffdh.take_bytesAt _ _ hb.kL, hb.bD]
  rw [ep] at pt ct
  exact ⟨⟨⟨hb.keep kt bt, he.keep kt bt⟩, pt, ct⟩, hi.keep hb kt bt⟩

theorem KF1 {g : GD} {s : State} (h : KB g s) :
    WP isa (.block [.addi .r12 .r21 0, .addi .r6 .r28 0]) s (K1a g) :=
  wp_split (XA h.1) (KB_loadP h)

theorem KF2 {g : GD} {s : State} (h : K1a g s) : WP isa Precompute.loadN s (K2 g) := wp_split (XL h.1) h.2

theorem KF3 {g : GD} {s : State} (h : K2 g s) : WP isa (.block Precompute.check1) s (K3 g) :=
  wp_split (XC1 h.1) h.2

theorem KF4 {g : GD} {s : State} (h : K3 g s) : WP isa Precompute.check2 s (K4 g) := h.2

theorem KK0 {g : GD} {s : State} (h : K4 g s ∧ s.gpr .r0 ≠ 0) :
    WP isa (.block [.li .r3 0]) s (fun t => CF g.d.x.c t) :=
  TK0 (Φ := fun d s => Base d s) (fun _ _ h => h) h.1.1.1.1

theorem pins_K1a : Pins K1a (baseRegs ++ ([.r12, .r6] : List Reg)) := fun g s₁ s₂ h₁ h₂ =>
  pins_X1a (Φ := X1a) (fun _ _ h => h) g.d.x s₁ s₂ h₁.1 h₂.1

theorem pins_K2 : Pins K2 (baseRegs ++ ([.r12, .r6] : List Reg)) := fun g s₁ s₂ h₁ h₂ =>
  pins_X1a (Φ := X1a) (fun _ _ h => h) g.d.x s₁ s₂ h₁.1.1 h₂.1.1

theorem pins_K3 : Pins K3 (baseRegs ++ ([.r6, .r15, .r18] : List Reg)) := fun g s₁ s₂ h₁ h₂ =>
  pins_X3 g.d.x s₁ s₂ h₁.1 h₂.1

/-! ## x's cut -/

/-- `Base` across a change of x's octets, apart from the domain. -/
theorem base_outX {d : CD} {s t : State} {rs : List Reg} {X : Addr} {n : Nat} (h : Base d s) (k : Keep rs s t)
    (hr : ∀ r ∈ baseRegs, r ∉ rs) (ho : Outside X 0 n s.mem t.mem)
    (hD : ∀ i < d.L, ∀ y, ofs X y < n → off d.D i ≠ y) (hY : ∀ i < d.k, ∀ y, ofs X y < n → off d.Y i ≠ y) :
    Base d t where
  env := ⟨h.env.hs.congr k.wr, (k.gpr _ (hr _ (by decide))).trans h.env.h10,
    (k.gpr _ (hr _ (by decide))).trans h.env.h29, (k.gpr _ (hr _ (by decide))).trans h.env.h11,
    (k.gpr _ (hr _ (by decide))).trans h.env.h31, h.env.hw, h.env.hw', h.env.hZ⟩
  r21 := (k.gpr _ (hr _ (by decide))).trans h.r21
  r23 := (k.gpr _ (hr _ (by decide))).trans h.r23
  r27 := (k.gpr _ (hr _ (by decide))).trans h.r27
  r28 := (k.gpr _ (hr _ (by decide))).trans h.r28
  k64 := h.k64
  k1024 := h.k1024
  hL := h.hL
  rdD := by rw [k.rd, k.wr]; exact h.rdD
  sepD := h.sepD
  rdY := by rw [k.rd, k.wr]; exact h.rdY
  sepY := h.sepY
  bD := by rw [outside_bytesAt (Z := n) ho (by omega) hD]; exact h.bD
  bY := by rw [outside_bytesAt (Z := n) ho (by omega) hY]; exact h.bY

/-- After the pointers: with p valid, `rand`'s and x's addresses in `r24` and `r25`. -/
def KP (g : GD) (s : State) : Prop :=
  (K4 g s ∧ s.gpr .r0 = 0) ∧ s.gpr .r24 = off g.R 0 ∧ s.gpr .r25 = off g.d.x.X 0

/-- After x's cut: `vg_ffdh_derive_public`'s predicate after p's check. -/
def K5 (g : GD) (s : State) : Prop := (Z4 g.d s ∧ s.gpr .r0 = 0) ∧ KE g s

theorem KPtrs {g : GD} {s : State} (h : K4 g s ∧ s.gpr .r0 = 0) : WP isa (.block ptrs) s (KP g) := by
  obtain ⟨⟨⟨⟨hb, he⟩, hp, hv⟩, hi⟩, hz⟩ := h
  have hZ := hb.env.hZ
  have e28 := Domain.slot_eq g.d.x.c.w 28
  refine WP.mono (ptrs_ok hb.env.hs (by omega) hb.r23 he.wX hi.wR) fun t ⟨⟨a24, a25, m⟩, k⟩ => ?_
  have hm : Body g.d.x.c.S g.d.x.c.w s.mem t.mem := by rw [m]; exact Outside.refl _ _ _ _
  exact ⟨⟨⟨⟨⟨hb.same k m, he.same k m⟩, by rw [arr, m]; exact hp, by rw [k.gpr .r0 (by decide)]; exact hv⟩,
    hi.keep hb k hm⟩, by rw [k.gpr .r0 (by decide)]; exact hz⟩, a24, a25⟩

theorem pins_KP : Pins KP (baseRegs ++ ([.r9, .r24, .r25] : List Reg)) := by
  intro g s₁ s₂ h₁ h₂ r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact h₁.1.1.1.1.1.pins h₂.1.1.1.1.1 r hr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.1.1.1.1.2.r9, h₂.1.1.1.1.2.r9]
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2, h₂.2.2]

theorem KS {g : GD} {s : State} (h : KP g s) : WP isa scalarRest s (K5 g) := by
  obtain ⟨⟨⟨⟨⟨hb, he⟩, hp, hv⟩, hi⟩, hz⟩, h24, h25⟩ := h
  have hval := hv.mp hz
  have hZ := hb.env.hZ
  have hnw := hb.env.hs.nowrap
  have e0 := Domain.slot_eq g.d.x.c.w 0
  have e28 := Domain.slot_eq g.d.x.c.w 28
  refine WP.mono (scalarRest_ok hb.r21 hb.r27 hb.r28 hb.k64 hb.k1024 hb.hL h24 h25 hb.rdD hi.rdR hi.scrX hi.sepRX)
    fun t ⟨⟨xb, xo, x0⟩, kt⟩ => ?_
  have hY : ∀ i < g.d.x.c.k, ∀ y, ofs g.d.x.X y < g.d.x.c.k → off g.d.x.c.Y i ≠ y := fun i hi' => by
    rw [hi.hY, off_off']; exact hi.sepDX _ (by rcases hb.hL with h | h <;> omega)
  have hb' : Base g.d.x.c t := base_outX hb kt (by decide) xo hi.sepDX hY
  have hw : ∀ d, d + 8 ≤ g.d.x.c.Z → word t.mem g.d.x.c.S d = word s.mem g.d.x.c.S d := fun d hd =>
    Outside.word_sep (d := d) xo hi.sepBX (by omega) hd hnw
  have he' : Ext g.d.x t :=
    ⟨(kt.gpr .r9 (by decide)).trans he.r9, (hw 64 (by omega)).trans he.wX, (hw 72 (by omega)).trans he.wXL,
      (hw 80 (by omega)).trans he.wO, by rw [kt.rd, kt.wr]; exact he.rdX, he.sepX, he.scrO.congr kt.wr, he.sepO,
      he.xl1, he.xlk⟩
  have hi' := hi.outX hb kt xo
  refine ⟨⟨⟨⟨⟨hb', he'⟩, by rw [arr, Outside.val32 (out_scr xo hi.sepBX) (Or.inl (by omega)) (by omega)]; exact hp,
    ⟨fun _ => hval, fun _ => x0⟩⟩, hi.hY, hi'.bnd, ?_⟩, x0⟩, hi'⟩
  have ex : xval g.d.x t = Spec.Rsa.os2ip (gOct g s.mem) := by
    simp only [xval]; rw [hi.xlk, xb]; rfl
  rw [ex]; exact hi.rng hval

/-! ## After x's cut -/

/-- After `vg_ffdh_derive_public`'s body: the registers and the header's word
of x's mask, and the status. -/
def K6 (g : GD) (s : State) : Prop :=
  (s.gpr .r23 = g.d.x.c.S ∧ s.gpr .r28 = BitVec.ofNat 64 g.d.x.c.k) ∧
    s.mem.readW (off g.d.x.c.S 64) 64 = off g.d.x.X 0 ∧ InRegions (s.rd ++ s.wr) (off g.d.x.c.S 64) 8 ∧
    Scr s g.d.x.X g.d.x.c.k ∧ (1 ≤ g.d.x.c.k ∧ g.d.x.c.k < 2 ^ 32) ∧
    ∃ st, s.gpr .r3 = BitVec.ofNat 64 st ∧ 1 ≤ st ∧ st < 4

/-- Before x's masked loop. -/
def K7 (g : GD) (s : State) : Prop :=
  (s.gpr .r25 = off g.d.x.X 0 ∧ s.gpr .r6 = BitVec.ofNat 64 g.d.x.c.k) ∧ s.gpr .r23 = g.d.x.c.S ∧
    Scr s g.d.x.X g.d.x.c.k ∧ (1 ≤ g.d.x.c.k ∧ g.d.x.c.k < 2 ^ 32) ∧ ∃ c, s.gpr .r17 = mask c

theorem pins_K6 : Pins K6 [.r23, .r28] := by
  intro g s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [h₁.1.1, h₂.1.1]
  · rw [h₁.1.2, h₂.1.2]

theorem pins_K7 : Pins K7 [.r25, .r6] := by
  intro g s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [h₁.1.1, h₂.1.1]
  · rw [h₁.1.2, h₂.1.2]

theorem KD {g : GD} {s : State} (h : K5 g s) : WP isa VG.Impl.Ffdh.PPC64LE.Derive.dpBody s (K6 g) := by
  obtain ⟨⟨⟨⟨⟨hb, he⟩, hp, hv⟩, hinv⟩, hz⟩, hi⟩ := h
  have hval := hv.mp hz
  have hf := modulus_facts hval
  have hpk : g.d.x.c.p < 256 ^ g.d.x.c.k := by
    have := VG.Proof.Bignum.os2ip_lt (g.d.x.c.db.take g.d.x.c.k)
    rwa [hb.take_len] at this
  have hZ := hb.env.hZ
  have e0 := Domain.slot_eq g.d.x.c.w 0
  have e28 := Domain.slot_eq g.d.x.c.w 28
  refine WP.mono (Derive.dpBody_ok hb.env hb.r23 hb.r21 hb.r27 hb.r28 rfl hb.k64 hb.k1024 hb.hL he.xl1 he.xlk he.wX
    he.wXL he.wO hb.rdD hb.sepD he.rdX he.sepX he.scrO he.sepO hi.sepB hp hf.1 hf.2 hpk rfl rfl rfl)
    fun t ⟨⟨_, t3, tw, _⟩, kt⟩ => ⟨⟨(kt.gpr .r23 (by decide)).trans hb.r23, (kt.gpr .r28 (by decide)).trans hb.r28⟩,
      by show word t.mem _ 64 = _; rw [tw 64 (by omega)]; exact he.wX,
      by rw [kt.rd, kt.wr]; exact hb.env.hs.ld (d := 64) (n := 8) (by omega), hi.scrX.congr kt.wr,
      ⟨by have := hb.k64; omega, by have := hb.k1024; omega⟩, _, t3,
      by split <;> [decide; split <;> decide], by split <;> [decide; split <;> decide]⟩

theorem KM1 {g : GD} {s : State} (h : K6 g s) :
    WP isa (.block (statusMask ++ [.load .d .r25 .r23 64, .addi .r6 .r28 0])) s (K7 g) := by
  obtain ⟨⟨h23, h28⟩, hX, hrd, hx, hk, st, h3, hst1, hst⟩ := h
  refine WP.mono (WP.keep [.r0, .r6, .r12, .r17, .r25] (Q := fun t => t.gpr .r25 = off g.d.x.X 0 ∧
      t.gpr .r17 = mask (decide (st = 1)) ∧ t.gpr .r6 = BitVec.ofNat 64 g.d.x.c.k ∧ t.mem = s.mem) (by
    unfold statusMask
    prun [h3, h23, h28, hrd, hX, BitVec.add_zero, status_mask st hst hst1]) (by decide))
    fun t ⟨⟨a25, a17, a6, _⟩, k⟩ => ⟨⟨a25, a6⟩, (k.gpr .r23 (by decide)).trans h23, hx.congr k.wr, hk, _, a17⟩

theorem KM2 {g : GD} {s : State} (h : K7 g s) :
    WP isa (countLoop .r6 [.lbz .r16 .r25 0, .logic .and .r16 .r16 .r17, .stb .r16 .r25 0, .addi .r25 .r25 1]) s
      (fun t => CF g.d.x.c t) := by
  obtain ⟨⟨h25, h6⟩, h23, hx, hk, c, h17⟩ := h
  exact WP.mono (masked_ok hk.1 hk.2 hx h25 h17 h6) fun t ⟨_, kt⟩ => (kt.gpr .r23 (by decide)).trans h23

/-! ## Constant time -/

theorem gk_rel : RelCT isa (Two K0) generateKey fun _ _ => True := by
  unfold generateKey
  rw [gkFront_eq]
  refine RelCT.seq (R := Two KB) ?_ (RelCT.seq (R := Two K4) ?_
    (RelCT.seq (R := Two fun (g : GD) s => CF g.d.x.c s) ?_ (two_taint _ pins_gCF (by taint_decide))))
  · exact RelCT.block_append (RelCT.seq (two_post (two_taint _ pins_K0 (by taint_decide)) fun _ _ h => KL1_of h)
      (two_post (two_taint _ pins_KL1 (by taint_decide)) fun _ _ h => h.2))
  · unfold loadP Precompute.check
    exact RelCT.seq (two_post (two_taint _ (pins_gx (Φ := KB) fun _ _ h => h.1) (by taint_decide)) fun _ _ h => KF1 h)
      (RelCT.seq (two_post (two_taint _ pins_K1a (by taint_decide)) fun _ _ h => KF2 h)
        (RelCT.seq (two_post (two_taint _ pins_K2 (by taint_decide)) fun _ _ h => KF3 h)
          (two_post (two_taint _ pins_K3 (by taint_decide)) fun _ _ h => KF4 h)))
  · refine two_ite (Φ := K4) (fun g s₁ s₂ h₁ h₂ => h₁.1.2.2.trans h₂.1.2.2.symm) ?_
      (two_post (two_taint _ (pins_gx (Φ := fun g s => K4 g s ∧ s.gpr .r0 ≠ 0) fun _ _ h => h.1.1.1)
        (by taint_decide)) fun _ _ h => KK0 h)
    unfold gkBody
    rw [scalar_eq]
    refine RelCT.seq (R := Two K5) (RelCT.seq
      (two_post (two_taint _ (pins_gx (Φ := fun g s => K4 g s ∧ s.gpr .r0 = 0) fun _ _ h => h.1.1.1)
        (by taint_decide)) fun _ _ h => KPtrs h)
      (two_post (two_taint _ pins_KP (by taint_decide)) fun _ _ h => KS h))
      (RelCT.seq (R := Two K6) (two_post (dpBody_rel.mono (fun _ _ ⟨g, h₁, h₂, hsp⟩ => ⟨g.d, h₁.1, h₂.1, hsp⟩)
        fun _ _ _ => trivial) fun _ _ h => KD h) ?_)
    unfold maskX
    exact RelCT.seq (two_post (two_taint _ pins_K6 (by taint_decide)) fun _ _ h => KM1 h)
      (two_post (two_taint _ pins_K7 (by taint_decide)) fun _ _ h => KM2 h)

/-- Runs with the same public arguments and leakage have the same public
data. -/
theorem gdOf_eq {s t : State} (hs : gkContract.pre s) (h3 : s.gpr .r3 = t.gpr .r3) (h5 : s.gpr .r5 = t.gpr .r5)
    (h7 : s.gpr .r7 = t.gpr .r7) (h8 : s.gpr .r8 = t.gpr .r8) (h9 : s.gpr .r9 = t.gpr .r9)
    (h10 : s.gpr .r10 = t.gpr .r10) (a0 : stackArg s 0 = stackArg t 0) (a1 : stackArg s 1 = stackArg t 1)
    (a2 : stackArg s 2 = stackArg t 2) (hl : gkLeak s = gkLeak t) : gdOf s = gdOf t := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨hk, -⟩, hL, -⟩ := hs
  simp only [Spec.Ffdh.domainLenValid] at hL
  simp only [gkLeak] at hl
  obtain ⟨e1, e2⟩ := List.append_inj hl (by simp only [List.length_map, VG.Proof.Bignum.bytesAt_length, h8])
  have ed : Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat =
      Spec.Rsa.bytesAt t.mem (s.gpr .r7) (s.gpr .r8).toNat := by
    have := (List.map_inj_right (fun _ _ h => BitVec.eq_of_toNat_eq h)).mp e1
    rw [← h7, ← h8] at this; exact this
  have sl : ∀ o, o + (s.gpr .r9).toNat ≤ (s.gpr .r8).toNat →
      Spec.Rsa.bytesAt s.mem (s.gpr .r7 + BitVec.ofNat 64 o) (s.gpr .r9).toNat =
        Spec.Rsa.bytesAt t.mem (s.gpr .r7 + BitVec.ofNat 64 o) (s.gpr .r9).toNat := fun o ho => by
    rw [← VG.Proof.Dsa.bytesAt_slice s.mem _ ho, ← VG.Proof.Dsa.bytesAt_slice t.mem _ ho, ed]
  have hgx : gxOf s = gxOf t := by
    simp only [gxOf, gcOf]
    rw [← h3, ← h5, ← h7, ← h8, ← h9, ← a1, ← a2, ed]
    simp only [off]
    rw [sl _ (by omega)]
  have hp : ∀ m : Mem, Spec.Rsa.os2ip ((Spec.Rsa.bytesAt m (s.gpr .r7) (s.gpr .r8).toNat).take (s.gpr .r9).toNat) =
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (s.gpr .r7) (s.gpr .r9).toNat) := fun m => by
    rw [Proof.Ffdh.take_bytesAt _ _ (by omega)]
  have hbT : ∀ P, Derive.bnd t.mem (s.gpr .r7) (s.gpr .r9).toNat (s.gpr .r8).toNat P =
      Derive.bnd s.mem (s.gpr .r7) (s.gpr .r9).toNat (s.gpr .r8).toNat P := fun P =>
    bnd_congr fun hq => (sl _ (by omega)).symm
  have hpT : Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (s.gpr .r7) (s.gpr .r9).toNat) =
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r9).toNat) := by rw [← hp, ← hp, ed]
  have e3 := (Derive.keyStatus_two _ _).symm.trans
    ((iff_of_eq (congrArg (· = 2) (List.cons.inj e2).1)).trans (Derive.keyStatus_two _ _))
  simp only [gkScalar] at e3
  rw [← h7, ← h8, ← h9, ← h10, ← a0] at e3
  rw [Derive.privateValid_dom (by omega) (by omega), Derive.privateValid_dom (by omega) (by omega)] at e3
  rw [hpT, hbT, ← ed] at e3
  have hv := bool_eq_of_false_iff e3
  simp only [gdOf, GD.mk.injEq, DD.mk.injEq]
  have hgp : (gcOf t).p = (gcOf s).p := congrArg (fun x : XD => x.c.p) hgx.symm
  have ep : (gcOf s).p = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r9).toNat) := hp s.mem
  refine ⟨⟨hgx, ?_, ?_⟩, h10⟩
  · rw [← h7, ← h8, ← h9, hgp, hbT]
  · rw [← h7, ← h8, ← h9, hgp, hbT, ep]
    simp only [gkScalar, ← h7, ← h8, ← h9, ← h10, ← a0, ← ed]
    exact hv

theorem gk_ct : ConstantTime isa gkContract.pre gkContract.pub generateKey :=
  RelCT.constantTime (gk_rel.mono (fun s _ ⟨hs, ht, hsp, h3, _, h5, _, h7, h8, h9, h10, a0, a1, a2, hl⟩ =>
    ⟨gdOf s, ⟨hs, rfl⟩, ⟨ht, (gdOf_eq hs h3 h5 h7 h8 h9 h10 a0 a1 a2 hl).symm⟩, hsp⟩) fun _ _ h => h)

end VG.Proof.Ffdh.PPC64LE.GenerateKey
