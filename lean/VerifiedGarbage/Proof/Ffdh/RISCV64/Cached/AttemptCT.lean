module

public import VerifiedGarbage.Proof.Ffdh.RISCV64.Cached.AttemptCorrect
public import VerifiedGarbage.Proof.Ffdh.RISCV64.Cached.Front
public import VerifiedGarbage.Proof.Ffdh.RISCV64.Cached.AttemptImplies
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ffdh.RISCV64.Derive.CT
public import VerifiedGarbage.Proof.Ffdh.RISCV64.CT
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public meta import VerifiedGarbage.Proof.Ffdh.RISCV64.Cached.AttemptCorrect
public meta import VerifiedGarbage.Proof.Ffdh.RISCV64.Cached.Front
public meta import VerifiedGarbage.Proof.Ffdh.RISCV64.Derive.CT
public meta import VerifiedGarbage.Proof.Ffdh.RISCV64.CT
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
public meta import VerifiedGarbage.Proof.Framework.RelCT
public meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ffdh.RISCV64.Derive.Correct
import VerifiedGarbage.Proof.Bignum.RISCV64.PubMid
import VerifiedGarbage.Proof.Bignum.RISCV64.PubCorrect
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.ContextRows
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
-- separate module: the constant-time proof, apart from the correctness proof's chain of modules

/-!
# `vg_ffdh_generate_key_cached` on RISC-V: constant time, and verified

The public data `GData`: `vg_ffdh_derive_public`'s (`Derive.DD`), whose
range bit is that of the cut scalar (`cutC`, which the status reveals,
`cutC_eq`), `rand`'s and the context's addresses, the scalar's width and
g. The predicates carry `Derive.AR`, `rand` in `t1`, x's and `rand`'s facts
(`XR`), the range bit (`KPI`) and the context's (`CX`) to the scalar. In
range, the comb's predicates (`KG2`–`KG6`) carry what is left to run, from
its correctness, to what the mask of x needs (`KQ5`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.Cached

open VG VG.RISCV64 VG.RISCV64.Taint VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Ffdh.RISCV64 VG.Impl.Ffdh.RISCV64.Cached VG.Impl.Ffdh.RISCV64.Cached.Generate
open VG.Proof.Bignum.RISCV64
open VG.Proof.Ffdh.RISCV64
open VG.Proof.Ffdh.RISCV64.GenerateKey (XR maskPre_ok masked_ok)
open VG.Proof.Ffdh.RISCV64.Derive (AR bnd DD inRange Inv W Z4 RB)
open VG.Proof.Ffdh.KeyScalar (cut)
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Pre (Two Pins two_post two_taint)

/-- Whether the cut scalar is within its bound. -/
def cutC (x : XD) (R : Addr) (bits : Nat) (m : Mem) : Bool :=
  decide (0 < Spec.Rsa.os2ip (cut (Spec.Rsa.bytesAt m R x.k) (x.k - (bits + 7) / 8) (tbOf bits)) ∧
    Spec.Rsa.os2ip (cut (Spec.Rsa.bytesAt m R x.k) (x.k - (bits + 7) / 8) (tbOf bits)) < bnd m x.D x.k x.L x.p)

/-- The public data of a run. -/
structure GData where
  d : DD
  R : Addr
  C : Addr
  bits : Nat
  G : Nat

def cgOf (s : State) : GData :=
  ⟨⟨cgx s, cutC (cgx s) (s.gpr .a7) (cgBits s) s.mem⟩, s.gpr .a7, stackArg s 3, cgBits s, (cgA s).g⟩

/-- The range bit, as the data has it. -/
def KPI (g : GData) (s : State) : Prop := cutC g.d.x g.R g.bits s.mem = g.d.v

theorem KPI.keep {g : GData} {s t u : State} {o n : Nat} (h : KPI g s) (hc : Ctx g.d.x u) (hx : XR g.d.x g.R u)
    (hm : Outside g.d.x.S o n s.mem t.mem) (hn : o + n ≤ g.d.x.Z) : KPI g t := by
  have hL := hc.hL
  have eR := Pub.bytes_apart hm hn hx.sepRS
  have eb : bnd t.mem g.d.x.D g.d.x.k g.d.x.L g.d.x.p = bnd s.mem g.d.x.D g.d.x.k g.d.x.L g.d.x.p := by
    unfold bnd
    by_cases hq : g.d.x.L = 3 * g.d.x.k
    · rw [ite_eq_left hq, ite_eq_left hq, Pub.bytes_apart hm hn fun i hi => by
        have h' := hc.sepD (2 * g.d.x.k + i) (by omega_arith); rw [← Derive.off_off] at h'; exact h']
    · rw [ite_eq_right hq, ite_eq_right hq]
  unfold KPI cutC
  rw [eR, eb]
  exact h

/-- `Φ` of the data, with the argument registers, `rand`, its facts, the
range bit and the context's facts. -/
def KU (Φ : XD → State → Prop) (g : GData) (s : State) : Prop :=
  Φ g.d.x s ∧ AR g.d.x s ∧ s.gpr .t1 = g.R ∧ XR g.d.x g.R s ∧ KPI g s ∧ CX g.d.x g.C g.bits g.G s ∧
    g.d.x.Y = off g.d.x.D g.d.x.k

theorem KU.keep {Φ Ψ : XD → State → Prop} {g : GData} {s t : State} (h : KU Φ g s) (hc : ∀ x s, Φ x s → Ctx x s)
    (h' : Ψ g.d.x t) (ha : Arr g.d.x s.mem t.mem) (k : Keep [.a0, .s0, .t3, .t4, .t5] s t) : KU Ψ g t := by
  have hZ := (hc _ _ h.1).hZ
  unfold slot hdrBytes at hZ
  exact ⟨h', h.2.1.keep k, (k.gpr (by decide)).trans h.2.2.1, h.2.2.2.1.keep k.2.1 k.2.2,
    h.2.2.2.2.1.keep (hc _ _ h.1) h.2.2.2.1 ha (by omega_arith),
    h.2.2.2.2.2.1.keep (hc _ _ h.1) k.2.1 k.2.2 ha, h.2.2.2.2.2.2⟩

/-! ## The predicates -/

def KP0 (g : GData) (s : State) : Prop := cgContract.pre s ∧ cgOf s = g

/-- The front after its first four instructions. -/
abbrev frontRest : List Instr :=
  PublicChecked.saveRegs ++ (ctxHdr ++ (GenerateKey.gkHdr ++ PublicChecked.setup))

/-- After the working space's and the context's addresses. -/
def KF1 (g : GData) (s : State) : Prop :=
  s.gpr .t0 = g.d.x.S ∧ s.gpr .t1 = g.C ∧ WP isa (.block frontRest) s (KU Base g)

/-- Before the scalar: p valid. -/
def KS4 (g : GData) (s : State) : Prop := KU X4 g s ∧ s.gpr .s0 = 0

/-- After the scalar. -/
def KQ4 (g : GData) (s : State) : Prop := Z4 g.d s ∧ XR g.d.x g.R s ∧ CX g.d.x g.C g.bits g.G s

/-- After x's range. -/
def KRB (g : GData) (s : State) : Prop := RB g.d s ∧ XR g.d.x g.R s ∧ CX g.d.x g.C g.bits g.G s

/-- After the branches: what the mask needs. -/
def KQ5 (g : GData) (s : State) : Prop :=
  s.gpr .s6 = g.d.x.S ∧ Scr s g.d.x.S g.d.x.Z ∧ 256 ≤ g.d.x.Z ∧ 64 ≤ g.d.x.k ∧ g.d.x.k ≤ 1024 ∧
    (∃ n < 4, s.gpr .a0 = BitVec.ofNat 64 n) ∧
    word s.mem g.d.x.S 8 = off g.d.x.X 0 ∧ word s.mem g.d.x.S 16 = BitVec.ofNat 64 g.d.x.k ∧ XR g.d.x g.R s

/-- Before the mask's loop. -/
def KM (g : GData) (s : State) : Prop :=
  s.gpr .s6 = g.d.x.S ∧ s.gpr .a1 = off g.d.x.X 0 ∧ s.gpr .t5 = BitVec.ofNat 64 g.d.x.k ∧
    (∃ c : Bool, s.gpr .s4 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if c then 1 else 0)) ∧ 64 ≤ g.d.x.k ∧
    g.d.x.k ≤ 1024 ∧ XR g.d.x g.R s

/-- After the branch. -/
def KCF (g : GData) (s : State) : Prop := CF g.d.x s

/-- Before the status. -/
def KG6 (g : GData) (s : State) : Prop := CF g.d.x s ∧ WP isa (.block Derive.status) s (KQ5 g)

/-- Before the output. -/
def KG5 (g : GData) (s : State) : Prop := R8 g.d.x s ∧ WP isa PublicChecked.output s (KG6 g)

/-- Before `out`'s load. -/
def KG4 (g : GData) (s : State) : Prop := RW g.d.x s ∧ WP isa (.block [.load .d .s10 .s6 0]) s (KG5 g)

/-- After the comb. -/
def KG3 (g : GData) (s : State) : Prop := RW g.d.x s ∧ WP isa zMask s (KG4 g)

/-- After the comb's first block. -/
def KG2 (g : GData) (s : State) : Prop :=
  RW g.d.x s ∧ s.gpr .s10 = g.C ∧ s.gpr .s8 = g.d.x.X ∧
    s.gpr .s7 = BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows g.bits) ∧ s.gpr .t2 = BitVec.ofNat 64 1 ∧
    WP isa combRest s (KG3 g)

/-! ## Pins -/

theorem pins_KU {Φ : XD → State → Prop} {rs : List Reg} (h : Pins Φ rs) : Pins (KU Φ) rs :=
  fun g _ _ h₁ h₂ => h g.d.x _ _ h₁.1 h₂.1

theorem pins_KP0 : Pins KP0 ([] : List Reg) := fun _ _ _ _ _ _ hr => absurd hr List.not_mem_nil

theorem pins_KF1 : Pins KF1 [.t0, .t1] :=
  pins_of (fun g r => if r = .t0 then g.d.x.S else g.C) fun g s h r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [h.1, h.2.1]

theorem pins_KS4 : Pins KS4 (baseRegs ++ ([.a2, .a3, .a4, .a5, .a6, .t1] : List Reg)) := by
  intro g s₁ s₂ h₁ h₂ r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact pins_base (Φ := X4) (fun _ _ h => h.1) g.d.x s₁ s₂ h₁.1.1 h₂.1.1 r hr
  · refine pins_of (Φ := KS4) (fun g r => if r = .t1 then g.R else Derive.arVal g.d.x r) (fun g s h r hr => ?_)
      g s₁ s₂ h₁ h₂ r hr
    have ha := h.1.2.1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ha.a2, ha.a3, ha.a4, ha.a5, ha.a6, h.1.2.2.1]

theorem pins_KQ4 : Pins KQ4 (baseRegs ++ ([.a2, .a3, .a4, .a5, .a6] : List Reg)) :=
  fun g s₁ s₂ h₁ h₂ => Derive.pins_Z4 g.d s₁ s₂ h₁.1 h₂.1

theorem pins_KRB : Pins KRB baseRegs :=
  fun g s₁ s₂ h₁ h₂ => pins_base (Φ := X4) (fun _ _ h => h.1) g.d.x s₁ s₂ h₁.1.1 h₂.1.1

theorem pins_KRB9 : Pins (fun g s => KRB g s ∧ s.gpr .s9 = 0) baseRegs :=
  fun g s₁ s₂ h₁ h₂ => pins_KRB g s₁ s₂ h₁.1 h₂.1

/-- The registers `KG2` fixes, as functions of the data. -/
def g2Val (g : GData) (r : Reg) : BitVec 64 :=
  if r = .s10 then g.C else if r = .s8 then g.d.x.X else
    if r = .s7 then BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows g.bits) else
      if r = .t2 then BitVec.ofNat 64 1 else rwVal g.d.x r

theorem pins_KG2 : Pins KG2 [.s10, .s8, .s7, .t2, .s6, .a7, .s5, .t0, .s11] := pins_of g2Val fun g s h r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | hr
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2.1
  · exact h.2.2.2.2.1
  · have e : g2Val g r = rwVal g.d.x r := by
      unfold g2Val; rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl
    rw [e]
    exact rw_vals h.1 r (by simpa using hr)

theorem pins_KG3 : Pins KG3 [.s6, .a7, .s5, .t0, .s11] := pins_of (fun g => rwVal g.d.x) fun _ _ h => rw_vals h.1

theorem pins_KG4 : Pins KG4 [.s6, .a7, .s5, .t0, .s11] := pins_of (fun g => rwVal g.d.x) fun _ _ h => rw_vals h.1

theorem pins_KG5 : Pins KG5 [.s10, .s6, .a7, .s5, .t0, .s11] :=
  pins_of (fun g r => if r = .s10 then off g.d.x.O 0 else rwVal g.d.x r) fun g s h r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | hr
    · exact h.1.1
    · have hne : r ≠ .s10 := by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
      rw [ite_eq_right_of_eq_false _ _ (eq_false hne)]
      exact rw_vals h.1.2 r (by simpa using hr)

theorem pins_KG6 : Pins KG6 [.s6] := pins_of (fun g _ => g.d.x.S) fun g s h r hr => by
  rw [List.mem_singleton] at hr; subst hr; exact h.1

theorem pins_KQ5 : Pins KQ5 [.s6] := pins_of (fun g _ => g.d.x.S) fun g s h r hr => by
  rw [List.mem_singleton] at hr; subst hr; exact h.1

theorem pins_KM : Pins KM [.s6, .a1, .t5] :=
  pins_of (fun g r => if r = .s6 then g.d.x.S else if r = .a1 then off g.d.x.X 0 else BitVec.ofNat 64 g.d.x.k)
    fun g s h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [h.1, h.2.1, h.2.2.1]

theorem pins_KCF : Pins KCF [.s6] := fun g s₁ s₂ h₁ h₂ => pins_CF g.d.x s₁ s₂ h₁ h₂

theorem pins_KTI : Pins (fun g s => KU X4 g s ∧ s.gpr .s0 ≠ 0) baseRegs :=
  fun g s₁ s₂ h₁ h₂ => pins_base (Φ := X4) (fun _ _ h => h.1) g.d.x s₁ s₂ h₁.1.1 h₂.1.1

/-! ## The steps, by correctness -/

/-- The working space's and the context's addresses. -/
theorem front4_ok {s : State} (h : cgContract.pre s) :
    WP isa (.block ([.addSp .t0 8, .load .d .t0 .t0 0, .addSp .t1 24, .load .d .t1 .t1 0] : List Instr)) s
      fun t => t.gpr .t0 = stackArg s 1 ∧ t.gpr .t1 = stackArg s 3 := by
  obtain ⟨hrd, hwr, dXY, dXD, dXR, dXS, dXC, dXA, dYD, dYR, dYS, dYC, dYA, dDS, dRS, dSC, dSA, nwX, nwY, nwD,
    nwR, nwS, nwC, ⟨hk, hk'⟩, hL, hxl, hyl, hrl, hsl, hdv, hctx, alS, alC, alsp⟩ := h
  have hA : ∀ k < 5, InRegions (s.rd ++ s.wr) (stackArgAddr s k) 8 := fun k hk => by
    refine ⟨cgStack s, List.mem_append_left _ (by rw [hrd]; simp), ?_⟩
    show (⟨s.sp + BitVec.ofNat 64 (8 * 0), 40⟩ : Region).Contains (s.sp + BitVec.ofNat 64 (8 * k)) 8
    simp only [Nat.mul_zero, add_ofNat_zero]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  rw [show ([.addSp .t0 8, .load .d .t0 .t0 0, .addSp .t1 24, .load .d .t1 .t1 0] : List Instr) =
    ([.addSp .t0 8, .load .d .t0 .t0 0] : List Instr) ++ ([.addSp .t1 24, .load .d .t1 .t1 0] : List Instr) from rfl]
  refine WP.block_append (WP.mono (loadSk_ok s .t0 1 8 rfl (by decide) (hA 1 (by decide)) alsp)
    fun s₀ ⟨⟨a0', m0, p0⟩, k0⟩ => ?_)
  refine WP.mono (loadSk_ok s₀ .t1 3 24 rfl (by decide)
    (by rw [k0.2.1, k0.2.2, stackArgAddr, p0]; exact hA 3 (by decide)) (by rw [p0]; exact alsp))
    fun s₁ ⟨⟨a1', _, _⟩, k1⟩ => ⟨(k1.gpr (by decide)).trans a0', a1'.trans (by simp only [stackArg, stackArgAddr, p0, m0])⟩

theorem GL1 {g : GData} {s : State} (h : KP0 g s) :
    WP isa (.block ([.addSp .t0 8, .load .d .t0 .t0 0, .addSp .t1 24, .load .d .t1 .t1 0] : List Instr)) s (KF1 g) := by
  obtain ⟨hpre, rfl⟩ := h
  have hf := WP.rdwr (cgFront_ok hpre)
  unfold Generate.front at hf
  simp only [List.append_assoc] at hf
  rw [WP.block_append_iff] at hf
  refine WP.mono (WP.and (front4_ok hpre) hf) fun t ⟨⟨a0, a1⟩, w⟩ => ⟨a0, a1, ?_⟩
  refine WP.mono w fun u ⟨⟨hb, ha, h1, _, hch, _, o⟩, r, w', _⟩ => ?_
  have hZ := hb.ctx.hZ
  unfold slot hdrBytes at hZ
  have hx := cgXR hpre r w'
  have hn : 0 + 256 ≤ (cgx s).Z := by omega_arith
  have hi : KPI (cgOf s) s := rfl
  exact ⟨hb, ha, h1, hx, KPI.keep (s := s) (t := u) hi hb.ctx hx o hn,
    cx_of_pre hpre r (o.mono (Nat.le_refl _) (by change 256 ≤ (stackArg s 2).toNat * 8 at hn; omega_arith)) hch, rfl⟩

theorem TSc {g : GData} {s : State} (h : KS4 g s) : WP isa scalar s (KQ4 g) := by
  obtain ⟨⟨h4, ha, h1, hx, hpi, hcx, hYD⟩, hz⟩ := h
  refine WP.mono (WP.rdwr (scalarC_ok h4 hz ha hx h1 hcx.b1 hcx.bk hcx.hbw hcx.hyw))
    fun t ⟨⟨t4, t0, ta, tx, tb, to⟩, r, w, _⟩ => ⟨⟨⟨t4, ta, ?_⟩, t0⟩, tx, hcx.ofX h4.1.ctx hx r w to hYD⟩
  have hc := h4.1.ctx
  have hL := hc.hL
  have eb : bnd t.mem g.d.x.D g.d.x.k g.d.x.L g.d.x.p = bnd s.mem g.d.x.D g.d.x.k g.d.x.L g.d.x.p := by
    unfold bnd
    by_cases hq : g.d.x.L = 3 * g.d.x.k
    · rw [ite_eq_left hq, ite_eq_left hq, Pub.bytes_apart (Z := g.d.x.k) to (by omega_arith) fun i hi => by
        have h' := hx.sepDX (2 * g.d.x.k + i) (by omega_arith); rw [← Derive.off_off] at h'; exact h']
    · rw [ite_eq_right hq, ite_eq_right hq]
  show inRange g.d.x t.mem = g.d.v
  unfold inRange
  rw [hx.xl, tb, eb]
  exact hpi

theorem TX {g : GData} {s : State} (h : KQ4 g s) : WP isa Derive.xRange s (KRB g) := by
  obtain ⟨⟨⟨h4, ha, hi⟩, hz⟩, hx, hcx⟩ := h
  have hv := h4.2.2.mp hz
  refine WP.mono (WP.rdwr (Derive.xRange_ok h4 hv ha)) fun t ⟨⟨t4, t0, t9, am⟩, r, w, _⟩ =>
    ⟨⟨t4, t0, ?_⟩, hx.keep r w, hcx.keep h4.1.ctx r w am⟩
  rw [t9]
  have hi' : inRange g.d.x s.mem = g.d.v := hi
  unfold inRange at hi'
  rw [hi']
  cases g.d.v <;> decide

/-- `KQ5` from a run that changed only the arrays and `out`. -/
theorem q5_of {g : GData} {s t : State} (hc : Ctx g.d.x s) (hx : XR g.d.x g.R s) (hrd : t.rd = s.rd)
    (hwr : t.wr = s.wr) (h6 : t.gpr .s6 = g.d.x.S) (ha : ∃ n < 4, t.gpr .a0 = BitVec.ofNat 64 n)
    (hm : ∃ m, Arr g.d.x s.mem m ∧ Outside g.d.x.O 0 g.d.x.k m t.mem) : KQ5 g t := by
  obtain ⟨m, am, om⟩ := hm
  have hn := hc.scr.nowrap
  have hZ := hc.hZ
  unfold slot hdrBytes at hZ
  have hw : ∀ d, d + 8 ≤ 256 → word t.mem g.d.x.S d = word s.mem g.d.x.S d := fun d hd => by
    refine (Pub.Outside.word_apart om hx.sepSO (by omega_arith) (by omega_arith) hn).trans ?_
    show Mont.word m _ _ = _
    exact Outside.word am (Or.inl hd) (by omega_arith)
  exact ⟨h6, hc.scr.congr hwr, by omega_arith, hc.k64, hc.k1024, ha, by rw [hw 8 (by decide)]; exact hc.hX,
    by rw [hw 16 (by decide), hc.hXL, hx.xl], hx.keep hrd hwr⟩

theorem TBd {g : GData} {s : State} (h : KRB g s ∧ s.gpr .s9 = 0) : WP isa Derive.dpBad s (KQ5 g) :=
  WP.mono (WP.rdwr (Derive.bad_ok h.1.1.1.1 h.2)) fun _ ⟨⟨⟨_, ta⟩, t6, ot⟩, r, w, _⟩ =>
    q5_of h.1.1.1.1.ctx h.1.2.1 r w t6 ⟨2, by decide, ta⟩ ⟨s.mem, Outside.refl _ _ _ _, ot⟩

/-- In range: the comb's first block, then what is left of the branch. -/
theorem TG1 {g : GData} {s : State} (h : KRB g s) : WP isa (.block headBlock) s (KG2 g) := by
  obtain ⟨⟨h4, hz, -⟩, hx, hcx⟩ := h
  obtain ⟨hb, hp, h0⟩ := h4
  have hc := hb.ctx
  have hv := h0.mp hz
  have hf := VG.Proof.Bignum.valid_facts hv hc.k64
  have hk := hc.k64; have hk' := hc.k1024
  have hZ := hc.hZ
  have hn := hc.scr.nowrap
  have hpk : g.d.x.p < 256 ^ g.d.x.k := by
    have := VG.Proof.Bignum.os2ip_lt (g.d.x.db.take g.d.x.k)
    rwa [take_len hc.hL.1 hc] at this
  have hP : 0 < g.d.x.p := by omega_arith
  have hwd : g.d.x.w = (g.d.x.k + 7) / 8 := rfl
  have hxl : g.d.x.xl = g.d.x.k := hx.xl
  have hlen : (Spec.Rsa.bytesAt s.mem g.d.x.X g.d.x.k).length = g.d.x.k := VG.Proof.Bignum.bytesAt_length _ _ _
  have ci : CombIn s g.d.x.S g.C g.d.x.X g.d.x.Z g.d.x.w (Spec.Rsa.bytesAt s.mem g.d.x.X g.d.x.k) g.d.x.p g.G
      g.bits := by
    refine ⟨hc.scr, by omega_arith, by omega_arith, hZ, hb.a7, hb.s5, hb.t0, hb.s6, hc.hX.trans (BitVec.add_zero _),
      by rw [hlen]; exact hb.s11,
      hcx.hC, hcx.hRw, hcx.ctx, hcx.ents, hcx.r2, hp, fun n hn => hc.rdX n (by rw [hlen] at hn; omega_arith),
      fun n hn => hc.sepX n (by rw [hlen] at hn; omega_arith), fun n hn => by simp [Spec.Rsa.bytesAt, off],
      by rw [hlen]; omega_arith,
      ⟨hf.1, hf.2.1, (Rsa.FixedBaseComb.rows_small (show g.bits ≤ 8192 by have := hcx.bk; omega_arith)).1⟩,
      by have := hcx.b1; omega_arith⟩
  have hZ8 : 64 ≤ g.d.x.Z := by unfold slot hdrBytes at hZ; omega_arith
  refine WP.mono (head_ok hc.scr hZ8 hb.s6 ci.hX hcx.hC hcx.hRw) fun s₁ ⟨⟨a10, a8, a7, a2, m1⟩, k1⟩ => ?_
  have rw1 : RW g.d.x s₁ := ⟨(k1.gpr (by decide)).trans hb.s6, (k1.gpr (by decide)).trans hb.a7,
    (k1.gpr (by decide)).trans hb.s5, (k1.gpr (by decide)).trans hb.t0, (k1.gpr (by decide)).trans hb.s11⟩
  refine ⟨rw1, a10, a8, a7, a2, ?_⟩
  refine WP.mono (WP.rdwr (combRest_ok ci a10 a8 a7 a2 m1 k1)) fun s₂ ⟨⟨⟨z1, p1, o1⟩, k2⟩, r2, w2, _⟩ => ?_
  have ar1 : Arr g.d.x s.mem s₂.mem := arr_of o1 (by unfold slot hdrBytes; omega_arith) (by
    have := Win.slot24 g.d.x.w; unfold slot hdrBytes at hZ this ⊢; omega_arith)
  have hc1 := hc.keep k2.2.1 k2.2.2 ar1
  have rw2 : RW g.d.x s₂ := ⟨(k2.gpr (by decide)).trans hb.s6, (k2.gpr (by decide)).trans hb.a7,
    (k2.gpr (by decide)).trans hb.s5, (k2.gpr (by decide)).trans hb.t0, (k2.gpr (by decide)).trans hb.s11⟩
  have hzP : wordsVal s₂.mem g.d.x.S (slot g.d.x.w 4) g.d.x.w < g.d.x.p := by
    rw [show wordsVal s₂.mem g.d.x.S (slot g.d.x.w 4) g.d.x.w = _ from z1, VG.Proof.Bignum.powMod_eq]
    exact Nat.mod_lt _ hP
  refine ⟨rw2, WP.mono (WP.rdwr (exOut_split hc1 rw2 p1 hf.1 hzP hpk)) fun s₇ ⟨⟨r7, h7⟩, rr7, ww7, _⟩ =>
    ⟨r7, WP.mono (WP.rdwr h7) fun s₈ ⟨⟨r8, h8⟩, rr8, ww8, _⟩ =>
      ⟨r8, WP.mono (WP.rdwr h8) fun t ⟨op, rt, wt, _⟩ => ⟨op.s6, ?_⟩⟩⟩⟩
  obtain ⟨m, am, om⟩ := op.mem
  refine WP.mono (WP.keep [.a0, .t2] (Q := fun u => u.gpr .a0 = BitVec.ofNat 64 3 - (t.gpr .a0 <<< 1) ∧
    u.mem = t.mem) (by unfold Derive.status; brun [fin64_exec_li_lit (show 3 < 2048 by decide)]) (by rfl) (by rfl))
    fun u ⟨⟨ua, um⟩, ku⟩ => q5_of hc hx ?_ ?_ ((ku.gpr (by decide)).trans op.s6) ?_
      ⟨m, ar1.trans am, by rw [um]; exact om⟩
  · rw [ku.2.1, rt, rr8, rr7, r2, k1.2.1]
  · rw [ku.2.2, wt, ww8, ww7, w2, k1.2.2]
  · rw [ua, op.a0, status_bv]
    exact ⟨_, by split <;> decide, rfl⟩

theorem TM {g : GData} {s : State} (h : KQ5 g s) : WP isa (.block GenerateKey.maskPre) s (KM g) := by
  obtain ⟨h6, hs, hZ, k1, k2, ⟨n, hn, h0⟩, hX, hK, hx⟩ := h
  exact WP.mono (WP.rdwr (maskPre_ok hs hZ h6 h0 hn hX hK)) fun t ⟨⟨⟨t4, t1, t5, _⟩, kt⟩, r, w, _⟩ =>
    ⟨(kt.gpr (by decide)).trans h6, t1, t5, ⟨decide (n = 1), by rw [t4]; simp⟩, k1, k2, hx.keep r w⟩

theorem TL {g : GData} {s : State} (h : KM g s) : WP isa GenerateKey.maskLoop s (KCF g) := by
  obtain ⟨h6, h1, h5, ⟨c, h4⟩, k1, k2, hx⟩ := h
  exact WP.mono (masked_ok (c := c) (by omega_arith) (by omega_arith) hx.nwX hx.wX h1 h4 h5)
    fun _ ⟨_, kt⟩ => (kt.gpr (by decide)).trans h6

/-! ## Constant time -/

/-- x in range: the comb, then as `vg_ffdh_derive_public`. -/
theorem good_rel : RelCT isa (Two KRB) good (Two KQ5) := by
  unfold good comb exOut
  exact RelCT.seq
    (RelCT.seq (two_post (two_taint _ pins_KRB (by taint_decide)) fun _ _ h => TG1 h)
      (two_post (two_taint _ pins_KG2 (by taint_decide)) fun _ _ h => h.2.2.2.2.2))
    (RelCT.seq
      (RelCT.seq (two_post (two_taint _ pins_KG3 (by taint_decide)) fun _ _ h => h.2)
        (RelCT.seq (two_post (two_taint _ pins_KG4 (by taint_decide)) fun _ _ h => h.2)
          (two_post (two_taint _ pins_KG5 (by taint_decide)) fun _ _ h => h.2)))
      (two_post (two_taint _ pins_KG6 (by taint_decide)) fun _ _ h => h.2))

/-- x's range and the branches. -/
theorem range_rel : RelCT isa (Two KQ4) (.seq Derive.xRange (.ite (.zero .s9) Derive.dpBad good)) (Two KQ5) := by
  refine RelCT.seq (R := Two KRB) (two_post (two_taint _ pins_KQ4 (by taint_decide)) fun _ _ h => TX h) ?_
  refine RelCT.ite (fun s₁ s₂ ⟨g, h₁, h₂, _⟩ => ?_)
    (RelCT.mono (two_post (Φ := fun g s => KRB g s ∧ s.gpr .s9 = 0) (two_taint _ pins_KRB9 (by taint_decide))
      (Ψ := KQ5) fun _ _ h => TBd h) (fun s₁ s₂ ⟨⟨g, h₁, h₂, hsp⟩, hc⟩ => ?_) fun _ _ h => h)
    (RelCT.mono good_rel (fun s₁ s₂ ⟨⟨g, h₁, h₂, hsp⟩, _⟩ => ⟨g, h₁, h₂, hsp⟩) fun _ _ h => h)
  · rw [Steps.eval_zero, Steps.eval_zero]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, h₁.1.2.2, h₂.1.2.2]
  · rw [Steps.eval_zero] at hc
    have h9 : s₁.gpr .s9 = 0 := by simpa using hc
    exact ⟨g, ⟨h₁, h9⟩, ⟨h₂, h₂.1.2.2.mpr (h₁.1.2.2.mp h9)⟩, hsp⟩

/-- After p's check, for a valid p. -/
theorem body_rel : RelCT isa (Two KS4) body (Two KCF) := by
  unfold body GenerateKey.maskX
  exact RelCT.seq (two_post (two_taint _ pins_KS4 (by taint_decide)) fun _ _ h => TSc h)
    (RelCT.seq range_rel
      (RelCT.seq (two_post (two_taint _ pins_KQ5 (by taint_decide)) fun _ _ h => TM h)
        (two_post (two_taint _ pins_KM (by taint_decide)) fun _ _ h => TL h)))

theorem cg_rel : RelCT isa (Two KP0) Generate.code fun _ _ => True := by
  unfold Generate.code Generate.front
  simp only [List.append_assoc]
  refine RelCT.seq (R := Two (KU Base)) ?_ (RelCT.seq (R := Two (KU X4)) ?_
    (RelCT.seq (R := Two KCF) ?_ (two_taint _ pins_KCF (by taint_decide))))
  · exact RelCT.block_append (RelCT.seq (two_post (two_taint _ pins_KP0 (by taint_decide)) fun _ _ h => GL1 h)
      (two_post (two_taint _ pins_KF1 (by taint_decide)) fun _ _ h => h.2.2))
  · unfold loadP Precompute.check
    exact RelCT.seq (two_post (two_taint _ (pins_KU (pins_base fun _ _ h => h)) (by taint_decide))
        fun _ _ h => WP.mono (WP.keep [.a0, .s0, .t3, .t4, .t5] (loadN_X h.1) (by rfl)) fun _ ⟨⟨h', a⟩, k⟩ =>
          h.keep (fun _ _ h => h.ctx) h' a k)
      (RelCT.seq (two_post (two_taint _ (pins_KU (pins_base (Φ := X2) fun _ _ h => h.1)) (by taint_decide))
          fun _ _ h => WP.mono (WP.keep [.a0, .s0, .t3, .t4, .t5] (check1_X h.1) (by rfl)) fun _ ⟨⟨h', m⟩, k⟩ =>
            h.keep (fun _ _ h => h.1.ctx) h' (by rw [m]; exact Outside.refl _ _ _ _) k)
        (two_post (two_taint _ (pins_KU pins_X3) (by taint_decide)) fun _ _ h =>
          WP.mono (WP.keep [.a0, .s0, .t3, .t4, .t5] (check2_X h.1) (by rfl)) fun _ ⟨⟨h', m⟩, k⟩ =>
            h.keep (fun _ _ h => h.1.ctx) h' (by rw [m]; exact Outside.refl _ _ _ _) k))
  · refine RelCT.ite (fun s₁ s₂ ⟨g, h₁, h₂, _⟩ => ?_)
      (RelCT.mono body_rel (fun s₁ s₂ ⟨⟨g, h₁, h₂, hsp⟩, hc⟩ => ?_) fun _ _ h => h)
      (RelCT.mono (two_post (Φ := fun g s => KU X4 g s ∧ s.gpr .s0 ≠ 0)
        (two_taint _ pins_KTI (by taint_decide)) (Ψ := KCF) fun _ _ h => TI ⟨h.1.1, h.2⟩)
        (fun s₁ s₂ ⟨⟨g, h₁, h₂, hsp⟩, hc⟩ => ?_) fun _ _ h => h)
    · rw [Steps.eval_zero, Steps.eval_zero]
      congr 1
      rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, h₁.1.2.2, h₂.1.2.2]
    · rw [Steps.eval_zero] at hc
      have h0 : s₁.gpr .s0 = 0 := by simpa using hc
      exact ⟨g, ⟨h₁, h0⟩, ⟨h₂, h₂.1.2.2.mpr (h₁.1.2.2.mp h0)⟩, hsp⟩
    · rw [Steps.eval_zero] at hc
      have h0 : s₁.gpr .s0 ≠ 0 := by simpa using hc
      exact ⟨g, ⟨h₁, h0⟩, ⟨h₂, fun e => h0 (h₁.1.2.2.mpr (h₂.1.2.2.mp e))⟩, hsp⟩

/-! ## The public data -/

/-- The range bit is whether the status is not 2. -/
theorem cutC_eq {s : State} (h : cgContract.pre s) :
    cutC (cgx s) (s.gpr .a7) (cgBits s) s.mem = decide (Spec.Ffdh.keyStatus (cgA s) (cgScalar s) ≠ 2) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨hk, hk'⟩, hL, -, -, hrl, -, hdv,
    -⟩ := h
  have hLk : 2 * (s.gpr .a6).toNat ≤ (s.gpr .a5).toNat := by
    simp only [Spec.Ffdh.domainLenValid] at hL; omega_arith
  have hL' : (s.gpr .a5).toNat = 2 * (s.gpr .a6).toNat ∨ (s.gpr .a5).toNat = 3 * (s.gpr .a6).toNat := hL
  have hgb := ContextRows.genBits_facts hdv
  have hsc : Spec.Rsa.os2ip (cut (Spec.Rsa.bytesAt s.mem (s.gpr .a7) (cgx s).k)
      ((cgx s).k - (cgBits s + 7) / 8) (tbOf (cgBits s))) = cgScalar s := by
    rw [scalarC_value (k := (cgx s).k) (bits := cgBits s) (VG.Proof.Bignum.bytesAt_length _ _ _) hgb.1 hgb.2]
    show _ = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .a7) (stackArg s 0).toNat) % 2 ^ cgBits s
    rw [hrl]
    rfl
  have hpD : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a6).toNat) = (cgx s).p := by
    rw [show (cgx s).p = (cgA s).p from rfl, Proof.Ffdh.domainOf_p _ _ hLk]
  have hst := Derive.keyStatus_dom (m := s.mem) (D := s.gpr .a4) (by omega_arith) hL' hdv (cgScalar s)
  change Spec.Ffdh.keyStatus (cgA s) (cgScalar s) = _ at hst
  rw [hpD] at hst
  unfold cutC
  rw [hsc, hst]
  show decide (0 < cgScalar s ∧ cgScalar s < bnd s.mem (s.gpr .a4) (s.gpr .a6).toNat (s.gpr .a5).toNat (cgx s).p) = _
  by_cases hr : 0 < cgScalar s ∧ cgScalar s < bnd s.mem (s.gpr .a4) (s.gpr .a6).toNat (s.gpr .a5).toNat (cgx s).p
  · simp only [hr, and_self, not_true_eq_false, ↓reduceIte, decide_true]
    split <;> decide
  · simp only [hr, not_false_eq_true, ↓reduceIte, decide_false]
    decide

theorem cgOf_eq {s t : State} (hs : cgContract.pre s) (ht : cgContract.pre t) (hp : cgContract.pub s t) :
    cgOf s = cgOf t := by
  obtain ⟨_, hb, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4⟩ := hp
  simp only [cgLeak] at hb
  obtain ⟨e1, e2⟩ := List.append_inj hb (by simp only [List.length_map, VG.Proof.Bignum.bytesAt_length, h5])
  have eb : Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat = Spec.Rsa.bytesAt t.mem (t.gpr .a4) (t.gpr .a5).toNat :=
    (List.map_inj_right (fun _ _ h => BitVec.eq_of_toNat_eq h)).mp e1
  have ex : cgx s = cgx t := by
    simp only [cgx]
    rw [eb]
    simp only [h0, h2, h4, h5, h6, a1, a2]
  have eA : cgA s = cgA t := by
    show Spec.Ffdh.domainOf (s.gpr .a6).toNat (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat) = _
    rw [eb, h6]
  have ev : cutC (cgx s) (s.gpr .a7) (cgBits s) s.mem = cutC (cgx t) (t.gpr .a7) (cgBits t) t.mem := by
    rw [cutC_eq hs, cutC_eq ht, (List.cons.inj e2).1]
  have eB : cgBits s = cgBits t := congrArg Spec.Ffdh.generationScalarBits eA
  have eG : (cgA s).g = (cgA t).g := congrArg Spec.Ffdh.Parameters.g eA
  unfold cgOf
  rw [ev, ex, h7, a3, eB, eG]

theorem cg_ct : ConstantTime isa cgContract.pre cgContract.pub Generate.code :=
  RelCT.constantTime (cg_rel.mono (fun s _ ⟨hs, ht, hp⟩ =>
    ⟨cgOf s, ⟨hs, rfl⟩, ⟨ht, (cgOf_eq hs ht hp).symm⟩, hp.1⟩) fun _ _ h => h)

/-- `vg_ffdh_generate_key_cached`. -/
theorem cg_verified : Verified target Generate.code (Spec.Ffdh.cachedGenerateKeyContract abi) :=
  Verified.of_correct cg_correct cg_ct cg_implies

end VG.Proof.Ffdh.RISCV64.Cached
