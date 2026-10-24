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
    decide (0 < Spec.Rsa.os2ip (gkOct s.mem (s.gpr .r7) (s.gpr .r10) (s.gpr .r9).toNat (s.gpr .r8).toNat) ∧
      Spec.Rsa.os2ip (gkOct s.mem (s.gpr .r7) (s.gpr .r10) (s.gpr .r9).toNat (s.gpr .r8).toNat) <
        Derive.bnd s.mem (s.gpr .r7) (s.gpr .r9).toNat (s.gpr .r8).toNat (gcOf s).p)⟩, s.gpr .r10⟩

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
  rng : 0 < Spec.Rsa.os2ip (gOct g s.mem) ∧ Spec.Rsa.os2ip (gOct g s.mem) < g.d.b ↔ g.d.v = true

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
    rw [e]; exact h.rng

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
  · show 0 < Spec.Rsa.os2ip (gkOct t.mem (s.gpr .r7) (s.gpr .r10) (s.gpr .r9).toNat (s.gpr .r8).toNat) ∧
      Spec.Rsa.os2ip (gkOct t.mem (s.gpr .r7) (s.gpr .r10) (s.gpr .r9).toNat (s.gpr .r8).toNat) <
        Derive.bnd s.mem (s.gpr .r7) (s.gpr .r9).toNat (s.gpr .r8).toNat (gcOf s).p ↔ (gdOf s).d.v = true
    have e : gkOct t.mem (s.gpr .r7) (s.gpr .r10) (s.gpr .r9).toNat (s.gpr .r8).toNat =
        gkOct s.mem (s.gpr .r7) (s.gpr .r10) (s.gpr .r9).toNat (s.gpr .r8).toNat := by
      unfold gkOct
      rw [hby _ _ (sep_of_disjoint dRS (by omega)), hby _ _ fun i hi => by
        unfold bptr; split
        · rw [off_off']; exact sepD _ (by omega)
        · exact sepD _ (by omega)]
    rw [e]
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

end VG.Proof.Ffdh.PPC64LE.GenerateKey
