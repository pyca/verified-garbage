module

public import VerifiedGarbage.Proof.Dsa.X86_64.CheckOperands
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import Batteries.Logic
public import VerifiedGarbage.Proof.Dsa.X86_64.Call
import VerifiedGarbage.Proof.Dsa.X86_64.CallHeader
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.Dsa.X86_64.Add
public import VerifiedGarbage.Impl.Dsa.X86_64.Core
import VerifiedGarbage.Proof.Dsa.X86_64.StoreSuffix
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Dsa.X86_64.Core
meta import VerifiedGarbage.Proof.Dsa.X86_64.StoreSuffix
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
public import VerifiedGarbage.Impl.Dsa.Layout
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
public import VerifiedGarbage.Impl.Dsa.X86_64.Arithmetic
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
meta import VerifiedGarbage.Impl.Dsa.Layout
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Impl.Dsa.X86_64.Arithmetic
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceInitCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceInitCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Add
import VerifiedGarbage.Proof.Dsa.X86_64.SetupCT
import VerifiedGarbage.Proof.Bignum.X86_64.CTR2
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
meta import VerifiedGarbage.Proof.Dsa.X86_64.SetupCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTR2
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
meta import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Dsa.X86_64.Load
meta import VerifiedGarbage.Proof.Dsa.X86_64.Load
public import VerifiedGarbage.Proof.Dsa.X86_64.PowerCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Frame
meta import VerifiedGarbage.Proof.Dsa.X86_64.PowerCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Frame
public import VerifiedGarbage.Proof.Dsa.X86_64.ReduceByte
import VerifiedGarbage.Proof.Bignum.X86_64.CrtArith
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTGPow
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceByte
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtArith
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTGPow
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
public import Aesop.BuiltinRules
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import Aesop.BuiltinRules
public import VerifiedGarbage.Proof.Dsa.X86_64.ProductCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ProductCT
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
public import VerifiedGarbage.Impl.Rsa.X86_64.Crt
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.ToDual
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Impl.Rsa.X86_64.Crt
meta import Mathlib.Order.RelClasses
meta import Mathlib.Tactic.Finiteness.Attr
meta import Mathlib.Tactic.Push
meta import Mathlib.Data.Nat.Basic
meta import Mathlib.Tactic.ToDual

/-! ### `Dsa.X86_64.CallHeadCT`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.CallFinishCT`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.ReduceByteCT`, which only this module used -/

section

/-! ### `Dsa.X86_64.AddCT`, which this module and modules that import it used -/

section

/-! # Constant time of DSA modular addition -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- `addMod`'s loads. -/
def addHead (a b : Nat) : List Instr :=
  [.mov .rbx (.mem (hdr (sArr a))), .mov .r9 (.mem (hdr (sArr b))), .mov .r10 (.mem (hdr (sArr Public.aN))),
    .mov .r8 (.mem (hdr (sArr Public.aAcc))), .mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr Public.aTmp))),
    .mov32 .rbp (.imm 0)]

/-- `addMod`'s sum. -/
def addLoop : Prog isa :=
  wordLoop 0 [cfFromRbp, .mov .rax (.mem (ix .rbx .r14)), .alu .adc .rax (.mem (ix .r9 .r14)),
    .store (ix .r8 .r14) .rax, cfToRbp]

/-- `addMod`'s carry and the reload of its output's base. -/
def addCarry (o : Nat) : List Instr :=
  [.mov32 .rax (.imm 0), cfFromRbp, .alu .adc .rax (.imm 0), .store (ix .r8 .r12) .rax,
    .mov .rbx (.mem (hdr (sArr o)))]

theorem addCode_eq (o a b : Nat) :
    addMod o a b = .seq (.block (addHead a b)) (.seq addLoop (.seq (.block (addCarry o)) (.seq subMod selectAcc))) := rfl

/-- The workspace of `addMod`, for some `-m⁻¹`. -/
def AddPre (L : Ws) (s : State) : Prop := GoodW L s ∧ 1 ≤ L.w ∧ L.w < 2 ^ 31

/-- After `addMod`'s loads. -/
def AddHead (a b : Nat) (L : Ws) (t : State) : Prop :=
  t.gpr .rdi = L.B ∧ t.gpr .rbx = off L.B (slot L.w a) ∧ t.gpr .r9 = off L.B (slot L.w b) ∧
    t.gpr .r10 = off L.B (slot L.w Public.aN) ∧ t.gpr .r8 = off L.B (slot L.w Public.aAcc) ∧
    t.gpr .r12 = BitVec.ofNat 64 L.w ∧ t.gpr .rsi = off L.B (slot L.w Public.aTmp) ∧ t.gpr .rbp = mask false ∧
    GoodW L t ∧ 1 ≤ L.w ∧ L.w < 2 ^ 31

/-- Before `addMod`'s subtraction and selection. -/
def AddMid (o : Nat) (L : Ws) (t : State) : Prop :=
  t.gpr .rbx = off L.B (slot L.w o) ∧ t.gpr .r10 = off L.B (slot L.w Public.aN) ∧
    t.gpr .r8 = off L.B (slot L.w Public.aAcc) ∧ t.gpr .r12 = BitVec.ofNat 64 L.w ∧
    t.gpr .rsi = off L.B (slot L.w Public.aTmp)

theorem addHead_ok {a b : Nat} (ha : a < 8) (hb : b < 8) {L : Ws} {s : State} (h : AddPre L s) : WP isa (.block (addHead a b)) s (AddHead a b L) := by
  obtain ⟨⟨minv, hg, hZ⟩, hw, hw'⟩ := h
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off L.B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot L.w 8 hi; omega_arith)
  refine WP.mono (WP.keep [.rbx, .r9, .r10, .r8, .r12, .rsi, .rbp] (Q := fun t =>
      t.gpr .rbx = off L.B (slot L.w a) ∧ t.gpr .r9 = off L.B (slot L.w b) ∧
      t.gpr .r10 = off L.B (slot L.w Public.aN) ∧ t.gpr .r8 = off L.B (slot L.w Public.aAcc) ∧
      t.gpr .r12 = BitVec.ofNat 64 L.w ∧ t.gpr .rsi = off L.B (slot L.w Public.aTmp) ∧ t.gpr .rbp = mask false ∧
      t.mem = s.mem)
    (by unfold addHead; xrun [State.ea, hdr, hg.rdi, hdrOff, hl (sArr a) (by unfold sArr; omega_arith), hl (sArr b) (by unfold sArr; omega_arith),
      hl (sArr Public.aN) (by decide), hl (sArr Public.aAcc) (by decide), hl sW (by decide),
      hl (sArr Public.aTmp) (by decide), hg.hdr.harr a ha, hg.hdr.harr b hb,
      hg.hdr.harr Public.aN (by decide), hg.hdr.harr Public.aAcc (by decide), hg.hdr.harr Public.aTmp (by decide),
      hg.hdr.hw]) rfl)
    fun t ⟨⟨h1, h2, h3, h4, h5, h6, h7, hm⟩, k⟩ => ⟨(k.gpr (by decide)).trans hg.rdi, h1, h2, h3, h4, h5, h6, h7,
      ⟨minv, ⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi, hm ▸ hg.hdr⟩, hZ⟩, hw, hw'⟩

theorem addCarry_ok {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8)
    (haAcc : a ≠ Public.aAcc) (hbAcc : b ≠ Public.aAcc) {L : Ws} {s₁ : State} (h : AddHead a b L s₁) : WP isa (.seq addLoop (.block (addCarry o))) s₁ (AddMid o L) := by
  obtain ⟨hdi, hbx, h9, h10, h8, h12, hsi, hbp, ⟨minv, hg, hZ⟩, hw, hw'⟩ := h
  have hs₁ := hg.scr
  have hn := hs₁.nowrap
  have sl : ∀ j < 8, slot L.w j + 8 * (L.w + 2) ≤ L.Z := fun j hj => (slot_le hj).trans hZ
  have sA := sl Public.aAcc (by decide)
  have sX := sl a ha
  have sT := sl b hb
  have p1 := slot_sep (w := L.w) haAcc
  have p2 := slot_sep (w := L.w) hbAcc
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s₁.mem → Keep [.r14] s₁ t → t.cf = s₁.cf →
      AddInv s₁ L.B L.Z (slot L.w Public.aAcc) (slot L.w a) (slot L.w b) 0 t := fun t h14 hm k _ =>
    ⟨hs₁.congr k.2.2, k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _,
      ⟨false, (k.gpr (by decide)).trans hbp, by rw [hm]; rfl⟩⟩
  refine WP.seq (WP.mono (wordLoop_ok (start := 0) (N := L.w) (by omega_arith) hw'
    (AddInv s₁ L.B L.Z (slot L.w Public.aAcc) (slot L.w a) (slot L.w b)) h0
    (fun j _ hj t hI => addStep_ok h8 hbx h9 h12 (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
      (by omega_arith) hj hI)) fun s₂ hI => ?_)
  obtain ⟨c, hc, -⟩ := hI.val
  have s₂8 : s₂.gpr .r8 = off L.B (slot L.w Public.aAcc) := (hI.keep.gpr (by decide)).trans h8
  have s₂12 : s₂.gpr .r12 = BitVec.ofNat 64 L.w := (hI.keep.gpr (by decide)).trans h12
  have s₂di : s₂.gpr .rdi = L.B := (hI.keep.gpr (by decide)).trans hdi
  have hl₂ : ∀ i < 32, InRegions (s₂.rd ++ s₂.wr) (off L.B (8 * i)) 8 := fun i hi =>
    hI.scr.ld (by have := hdr_lt_slot L.w 8 hi; omega_arith)
  have q1 := hdr_lt_slot L.w Public.aAcc (show sArr o < 32 by unfold sArr; omega_arith)
  have q2 := hdr_lt_slot L.w 8 (show sArr o < 32 by unfold sArr; omega_arith)
  have ho₂ : word s₂.mem L.B (8 * sArr o) = off L.B (slot L.w o) := by
    rw [hI.out.word (by omega_arith) (by omega_arith)]
    exact hg.hdr.harr o ho
  have hX : ∀ v : BitVec 64,
      (s₂.mem.writeW (off L.B (slot L.w Public.aAcc + 8 * L.w)) v).readW (off L.B (8 * sArr o)) 64 =
        off L.B (slot L.w o) := fun v =>
    ((writeW_outside s₂.mem L.B v (by omega_arith)).word (Or.inl (by omega_arith)) (by omega_arith)).trans ho₂
  refine WP.mono (WP.keep [.rax, .rbp, .rbx] (Q := fun t => t.gpr .rbx = off L.B (slot L.w o))
    (by
      unfold addCarry cfFromRbp
      xrun [State.ea, ix, hdr, s₂di, hdrOff, addr0 s₂8 s₂12, hc, cf_mask,
        hI.scr.st (show slot L.w Public.aAcc + 8 * L.w + 8 ≤ L.Z by omega_arith), sx0, hl₂ (sArr o) (by unfold sArr; omega_arith),
        hX]) rfl) fun t ⟨hbx', k⟩ => ⟨hbx', ?_, ?_, ?_, ?_⟩
  · exact (k.gpr (by decide)).trans ((hI.keep.gpr (by decide)).trans h10)
  · exact (k.gpr (by decide)).trans s₂8
  · exact (k.gpr (by decide)).trans s₂12
  · exact (k.gpr (by decide)).trans ((hI.keep.gpr (by decide)).trans hsi)

theorem pins_addHead (a b : Nat) : Pins (AddHead a b) [.rdi, .rbx, .r9, .r10, .r8, .r12, .rsi] := by
  intro L s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  obtain ⟨a₁, b₁, c₁, d₁, e₁, f₁, g₁, -⟩ := h₁
  obtain ⟨a₂, b₂, c₂, d₂, e₂, f₂, g₂, -⟩ := h₂
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a₁, a₂]
  · rw [b₁, b₂]
  · rw [c₁, c₂]
  · rw [d₁, d₂]
  · rw [e₁, e₂]
  · rw [f₁, f₂]
  · rw [g₁, g₂]

theorem pins_addMid (o : Nat) : Pins (AddMid o) [.rbx, .r10, .r8, .r12, .rsi] := by
  intro L s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  obtain ⟨a₁, b₁, c₁, d₁, e₁⟩ := h₁
  obtain ⟨a₂, b₂, c₂, d₂, e₂⟩ := h₂
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [a₁, a₂]
  · rw [b₁, b₂]
  · rw [c₁, c₂]
  · rw [d₁, d₂]
  · rw [e₁, e₂]

/-- Modular addition has a value-independent trace for either DSA schedule. -/
theorem addCode_ct {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8)
    (haAcc : a ≠ Public.aAcc) (hbAcc : b ≠ Public.aAcc)
    {h₁ h₂ h₃ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.rdi]) (.block (addHead a b)) h₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.rdi, .rbx, .r9, .r10, .r8, .r12, .rsi])
      (.seq addLoop (.block (addCarry o))) h₂).isSome = true)
    (ht₃ : (taint.check (Taint.ofRegs [.rbx, .r10, .r8, .r12, .rsi])
      (.seq subMod selectAcc) h₃).isSome = true) :
    RelCT isa (Two AddPre) (addMod o a b) fun _ _ => True := by
  rw [addCode_eq]
  exact RelCT.assoc (RelCT.assoc (RelCT.seq (two_post (Ψ := AddMid o)
    (RelCT.assoc' (RelCT.seq (two_piece (Ψ := AddHead a b) [.rdi]
      (pins_rdiB (fun L => L.B) fun _ _ ⟨⟨_, hg, _⟩, _⟩ => hg.rdi) ht₁
        fun _ _ h => addHead_ok ha hb h)
      (two_taint _ (pins_addHead a b) ht₂)))
    fun _ _ h => WP.seq (WP.seq (WP.mono (addHead_ok ha hb h)
      fun _ h₁ => WP.seq_iff.mp (addCarry_ok ho ha hb haAcc hbAcc h₁))))
    (two_taint _ (pins_addMid o) ht₃)))

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.ReduceStepCT`, which only this module used -/

section

/-! # Timing of the multiply-and-add reduction step -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.Dsa.X86_64

/-- The accumulator is reduced; its value need not agree between runs. -/
theorem reduceStep_ct (M : Mont) : RelCT isa (Two (Reduced [aY]))
    (Arithmetic.reduceStep M.mm) (fun _ _ => True) := by
  unfold Arithmetic.reduceStep
  refine RelCT.seq (mont_step_ct M (by unfold MmUse; decide) [aY] (by decide) (by decide)) ?_
  exact two_map (fun p : ProductPublic => p.layout.ws)
    (fun p _ h => ⟨⟨_, h.1.good, p.fits⟩, by change 1 ≤ p.layout.w; have := p.lower; omega_using [this], p.upper⟩)
    (addCode_ct (by decide) (by decide) (by decide) (by decide) (by decide)
      (by taint_decide) (by taint_decide) (by taint_decide))

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.ReduceReadCT`, which only this module used -/

section

/-! # Constant-time reads of secret reduction input bytes -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure ReduceReadPublic where
  layout : Lay
  pointer : Addr

def ReduceReadPre (p : ReduceReadPublic) (s : State) : Prop :=
  GoodL p.layout s ∧ word s.mem p.layout.B (8 * Crt.sSrc) = p.pointer ∧
  InRegions (s.rd ++ s.wr) p.pointer 1

def ReduceReadHead (p : ReduceReadPublic) (s : State) : Prop :=
  GoodL p.layout s ∧ s.gpr .rsi = p.pointer ∧ InRegions (s.rd ++ s.wr) p.pointer 1

def ReduceReadStore (p : ReduceReadPublic) (s : State) : Prop :=
  s.gpr .rdi = p.layout.B ∧ s.gpr .rsi = p.pointer ∧
  s.gpr .rbx = off p.layout.B (slot p.layout.w aX)

theorem reduceRead_ct : RelCT isa (Two ReduceReadPre) (.block Arithmetic.reduceRead)
    (fun _ _ => True) := by
  change RelCT isa (Two ReduceReadPre) (.block (
    ([.mov .rsi (.mem (hdr Crt.sSrc))] : List Instr) ++
    ([.movzx8 .rax (at0 .rsi), .mov .rbx (.mem (hdr (sArr aX)))] : List Instr) ++
    [.store (at0 .rbx) .rax, .alu .add .rsi (.imm 1), .store (hdr Crt.sSrc) .rsi])) _
  rw [List.append_assoc]
  apply RelCT.block_append
  refine RelCT.seq (two_piece (Ψ := ReduceReadHead) [.rdi]
    (fun p s t hs ht => pins_good p.layout s t hs.1 ht.1) (by taint_decide) ?_) ?_
  · intro p s ⟨hg, hp, hr⟩
    refine WP.mono (WP.keep [.rsi] (Q := fun t => t.gpr .rsi = p.pointer ∧ t.mem = s.mem)
      ?_ rfl) fun t ⟨⟨hsi, hm⟩, hk⟩ =>
      ⟨⟨⟨hg.1.scr.congr hk.2.2, (hk.gpr (by decide)).trans hg.1.rdi, hm ▸ hg.1.hdr⟩, hg.2⟩,
        hsi, by simpa only [hk.2.1, hk.2.2] using hr⟩
    xrun [State.ea, hdr, hg.1.rdi, hdrOff, hp,
      hg.1.scr.ld (show 8 * Crt.sSrc + 8 ≤ p.layout.Z by
        have := hdr_lt_slot p.layout.w 8 (show Crt.sSrc < 32 by decide); have := hg.2; omega_arith)]
  apply RelCT.block_append
  refine RelCT.seq (two_piece (Ψ := ReduceReadStore) [.rdi, .rsi]
    (pins_of (fun p r => if r = .rdi then p.layout.B else p.pointer) (by
      intro p s h r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.1.1.rdi
      · exact h.2.1)) (by taint_decide) ?_) ?_
  · intro p s ⟨hg, hsi, hr⟩
    refine WP.mono (WP.keep [.rax, .rbx] (Q := fun t =>
      t.gpr .rbx = off p.layout.B (slot p.layout.w aX)) ?_ rfl)
      fun t ⟨hbx, hk⟩ => ⟨(hk.gpr (by decide)).trans hg.1.rdi,
        (hk.gpr (by decide)).trans hsi, hbx⟩
    xrun [State.ea, at0, hdr, hsi, hr, hg.1.rdi, hdrOff,
      show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
      hg.1.hdr.harr aX (by decide),
      hg.1.scr.ld (show 8 * sArr aX + 8 ≤ p.layout.Z by
        have := hdr_lt_slot p.layout.w 8 (show sArr aX < 32 by decide); have := hg.2; omega_arith)]
  exact two_taint [.rdi, .rsi, .rbx]
    (pins_of (fun p r => if r = .rdi then p.layout.B else if r = .rsi then p.pointer else
      off p.layout.B (slot p.layout.w aX)) (by
        intro p s h r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact h.1
        · exact h.2.1
        · exact h.2.2)) (by taint_decide)

end VG.Proof.Dsa.X86_64

end

end

/-! # Constant time of one complete streaming reduction byte -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure ReducePublic extends PowerPublic where
  greater255 : 255 < modulus
  lengthBound : bytes.len < 2 ^ 64

/-- Source bytes and the accumulator are secret; only their address and
length appear in the public descriptor. -/
def ReduceBytePre (p : ReducePublic) (s : State) : Prop :=
  ∃ (bs : List Byte) (acc : Nat), bs.length = p.bytes.len ∧ 0 < bs.length ∧
    ReduceState s p.bytes.x.B p.bytes.x.Z p.bytes.x.o p.bytes.x.w p.bytes.x.wx
      p.modulus p.minv p.bytes.ptr bs acc

def ReduceArithmeticPre (p : ReducePublic) (s : State) : Prop :=
  SubCtx s p.bytes.x.B p.bytes.x.Z p.bytes.x.o p.bytes.x.w p.bytes.x.wx p.minv ∧
  ModCtx s (off p.bytes.x.B p.bytes.x.o) (slot p.bytes.x.wx 8) p.bytes.x.wx p.minv p.modulus ∧
  wv s.mem (off p.bytes.x.B p.bytes.x.o) (slot p.bytes.x.wx aY) p.bytes.x.wx < p.modulus ∧
  wv s.mem (off p.bytes.x.B p.bytes.x.o) (slot p.bytes.x.wx aX) p.bytes.x.wx < p.modulus

theorem reduceRead_arithmetic {p : ReducePublic} {s : State} (h : ReduceBytePre p s) :
    WP isa (.block Arithmetic.reduceRead) s (ReduceArithmeticPre p) := by
  obtain ⟨bs, acc, hlen, hpos, h⟩ := h
  have hr := h.source.rd 0 hpos
  simp only [BitVec.add_zero] at hr
  refine WP.mono (reduceRead_context h.ctx h.modulus (by have := p.lower; omega_using [this])
    h.pointer hr h.high) fun t ⟨hc, hm, hbyte, harr, _⟩ => ?_
  refine ⟨hc, hm, ?_, ?_⟩
  · rw [harr aY (by decide) (by decide), h.value]
    exact h.reduced
  · rw [hbyte]
    have := (s.mem p.bytes.ptr).isLt
    have := p.greater255
    omega_using [this]

theorem reduceArithmetic_ct (M : Mont) : RelCT isa (Two ReduceArithmeticPre)
    (Arithmetic.reduceStep M.mm) (fun _ _ => True) :=
  two_map (fun p : ReducePublic => p.toPowerPublic.product) (fun _ _ h =>
    ⟨h.2.1, fun j hj => by obtain rfl := List.mem_singleton.mp hj; exact h.2.2.1⟩) (reduceStep_ct M)

/-- Only the header address is needed for the counter block's trace.
The loop proof separately establishes that the resulting flag is public. -/
theorem reduceByte_ct (M : Mont) : RelCT isa (Two ReduceBytePre)
    (Arithmetic.reduceByte M.mm) (fun _ _ => True) := by
  unfold Arithmetic.reduceByte seqs
  refine RelCT.seq (two_post (Ψ := ReduceArithmeticPre)
    (two_map (fun p : ReducePublic =>
      (⟨p.toPowerPublic.product.layout, p.bytes.ptr⟩ : ReduceReadPublic)) ?_ reduceRead_ct)
    (fun _ _ h => reduceRead_arithmetic h)) ?_
  · intro p s ⟨bs, acc, hlen, hpos, h⟩
    refine ⟨⟨h.ctx.good, Nat.le_refl _⟩, h.pointer, ?_⟩
    simpa using h.source.rd 0 hpos
  refine RelCT.seq (two_post (Ψ := fun p s => s.gpr .rdi = off p.bytes.x.B p.bytes.x.o)
    (reduceArithmetic_ct M) ?_) ?_
  · intro p s ⟨hc, hm, hred, hb⟩
    unfold Arithmetic.reduceStep
    refine WP.seq (WP.mono (mont_step M hm (Nat.le_refl _) p.lower
      (by have := p.fits; have := p.upper; omega_arith) (by unfold MmUse; decide) hred)
      fun u ⟨hmu, hlt, _, hf, _⟩ => ?_)
    have hxu := (hf.wv_of_not_mem (show aX < 8 by decide) (by decide) hc.good.scr.nowrap)
    refine WP.mono (addMod_ok hmu.good.scr hmu.good.rdi hmu.good.hdr (Nat.le_refl _)
      p.lower (by have := p.fits; have := p.upper; omega_arith)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rw [hmu.modulus]; exact hlt)
      (by rw [hmu.modulus, hxu]; exact hb)) fun t ⟨_, _, hk⟩ =>
        (hk.gpr (by decide)).trans hmu.good.rdi
  exact two_taint [.rdi] (pins_rdiB (fun p => off p.bytes.x.B p.bytes.x.o) (fun _ _ h => h))
    (by taint_decide)

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.ProductCallCT`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.PowerCallCT`, which this module and modules that import it used -/

section

/-! # Constant time of setup, load and complete DSA exponentiation -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure PowerCallPublic extends PowerPublic where
  base : Addr
  baseLen : Nat
  width48 : bytes.x.wx ≤ 48
  basePositive : 1 ≤ baseLen
  baseFits : (baseLen + 7) / 8 ≤ bytes.x.wx
  expPositive : 1 ≤ bytes.len
  expLimit : bytes.len ≤ 1024

abbrev PowerCallPublic.x (p : PowerCallPublic) : XPub := p.bytes.x

def PowerCallBytes (p : PowerCallPublic) (s : State) : Prop := ∃ bb eb : List Byte,
  word s.mem p.x.B (8 * arg) = p.base ∧ word s.mem p.x.B (8 * argLen) = BitVec.ofNat 64 bb.length ∧
  word s.mem p.x.B (8 * arg2) = p.bytes.ptr ∧ word s.mem p.x.B (8 * arg2Len) = BitVec.ofNat 64 eb.length ∧
  bb.length = p.baseLen ∧ eb.length = p.bytes.len ∧
  Src s p.x.B p.x.Z p.base bb ∧ Src s p.x.B p.x.Z p.bytes.ptr eb

def PowerCallPre (p : PowerCallPublic) (s : State) : Prop :=
  SubCtx s p.x.B p.x.Z p.x.o p.x.w p.x.wx p.minv ∧
  ModCtx s (off p.x.B p.x.o) (slot p.x.wx 8) p.x.wx p.minv p.modulus ∧ PowerCallBytes p s

def PowerCallPrepared (p : PowerCallPublic) (s : State) : Prop := PowerCallPre p s ∧
  wv s.mem (off p.x.B p.x.o) (slot p.x.wx aOne) p.x.wx = 1 ∧
  wv s.mem (off p.x.B p.x.o) (slot p.x.wx aR2) p.x.wx = 2 ^ (128 * p.x.wx) % p.modulus

theorem PowerCallBytes.frame {p : PowerCallPublic} {s t : State} (h : PowerCallBytes p s)
    (hc : SubCtx s p.x.B p.x.Z p.x.o p.x.w p.x.wx p.minv)
    (hf : Frm (off p.x.B p.x.o) (workRanges p.x.wx) s.mem t.mem) (hk : Keep mmRegs s t) :
    PowerCallBytes p t := by
  obtain ⟨bb, eb, hp, hl, hep, hel, hbl, helen, hb, he⟩ := h
  exact ⟨bb, eb, (work_parent hc hf (by decide)).trans hp, (work_parent hc hf (by decide)).trans hl,
    (work_parent hc hf (by decide)).trans hep, (work_parent hc hf (by decide)).trans hel,
    hbl, helen, work_source hc hf hk hb, work_source hc hf hk he⟩

theorem powerCall_prepare (M : Mont) {p : PowerCallPublic} {s : State} (h : PowerCallPre p s) :
    WP isa (Arithmetic.constants M.mm) s (PowerCallPrepared p) := by
  refine WP.mono (prepare_ok M h.1 p.lower p.width48 p.greater p.odd h.2.1.modulus h.2.1.inverse)
    fun t ⟨hc, hm, hone, hr2, hf, hk⟩ => ?_
  exact ⟨⟨hc, hm, h.2.2.frame h.1 hf hk⟩, hone, hr2⟩

theorem powerCall_load {p : PowerCallPublic} {s : State} (h : PowerCallPrepared p s) :
    WP isa (Arithmetic.load aX arg argLen) s (PowerCorePre p.toPowerPublic) := by
  obtain ⟨⟨hc, hm, bb, eb, hp, hl, hep, hel, hbl, helen, hb, he⟩, hone, hr2⟩ := h
  have hb1 : 1 ≤ bb.length := hbl ▸ p.basePositive
  have hbw : (bb.length + 7) / 8 ≤ p.x.wx := hbl ▸ p.baseFits
  have hb31 : bb.length < 2 ^ 31 := by
    have hw48 : p.x.wx ≤ 48 := p.width48
    omega_using [hbw, hw48]
  refine WP.mono (load_ok hc p.lower p.fits p.upper (by decide) (by decide) (by decide) hp hl hb hb1 hb31 hbw)
    fun t ⟨hct, _, hf, hk⟩ => ?_
  have hfa : Arrays (off p.x.B p.x.o) p.x.wx [aX] s.mem t.mem :=
    Arrays.of_outside (List.mem_singleton_self aX) hf (Nat.le_refl _) (Nat.le_refl _)
  have hfw := arrays_work hfa (by decide)
  have hz := hc.good.scr.nowrap
  have hmt : ModCtx t (off p.x.B p.x.o) (slot p.x.wx 8) p.x.wx p.minv p.modulus := by
    refine ⟨hct.good, (hfa.wv_of_not_mem (by decide) (by decide) hz).trans hm.modulus, ?_⟩
    rw [hfa.word0_of_not_mem (by decide) (by decide) hz (by have := p.lower; omega_using [hb1, hbw])]
    exact hm.inverse
  refine ⟨eb, ⟨hct, hmt, (hfa.wv_of_not_mem (by decide) (by decide) hz).trans hone,
    (work_parent hc hfw (by decide)).trans hep, (work_parent hc hfw (by decide)).trans hel,
    helen, helen ▸ p.expPositive, helen ▸ p.expLimit, work_source hc hfw hk he⟩,
    (hfa.wv_of_not_mem (by decide) (by decide) hz).trans hr2⟩

theorem powerCall_ct (M : Mont) (Sq : MontS) : RelCT isa (Two PowerCallPre)
    (Arithmetic.power Sq.mm M.mm arg argLen arg2 arg2Len) (fun _ _ => True) := by
  unfold Arithmetic.power
  refine RelCT.seq (two_post (Ψ := PowerCallPrepared)
    (two_map (fun p : PowerCallPublic => p.toPowerPublic.product) (fun p s h =>
      ⟨h.2.1, p.width48, p.greater, p.odd⟩) (constants_ct M)) (fun _ _ h => powerCall_prepare M h)) ?_
  refine RelCT.seq (two_post (Ψ := fun p s => PowerCorePre p.toPowerPublic s)
    (two_map (fun p : PowerCallPublic => (⟨p.x, p.base, p.baseLen⟩ : BPub)) ?_
      (loadArr_ct (j := aX) (sp := arg) (sl := argLen) (by decide) (by taint_decide) (by taint_decide)))
    (fun _ _ h => powerCall_load h)) ?_
  · intro p s ⟨⟨hc, _, bb, _, hp, hl, _, _, hbl, _, hb, _⟩, _⟩
    refine ⟨p.minv, bb, hc, p.lower, p.fits, p.upper, by decide, by decide, by decide,
      hp, hl, hbl, hb, hbl ▸ p.basePositive, ?_, hbl ▸ p.baseFits⟩
    have hbw : (bb.length + 7) / 8 ≤ p.x.wx := hbl ▸ p.baseFits
    have hw48 : p.x.wx ≤ 48 := p.width48
    omega_using [hbw, hw48]
  · exact two_map PowerCallPublic.toPowerPublic (fun _ _ h => h) (powerCore_ct M Sq)

end VG.Proof.Dsa.X86_64

end

end

/-! # Constant time of the complete ordinary modular product -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- Both product inputs fit the workspace. The shared call description
contains public pointers and lengths, never operand values. -/
structure ProductCallPublic extends PowerCallPublic where
  secondFits : (bytes.len + 7) / 8 ≤ bytes.x.wx

/-- Loading either input leaves the public call description and prepared
Montgomery constants intact. -/
theorem productCall_load {p : ProductCallPublic} {s : State}
    {a sp sl : Nat} {ptr : Addr} {bs : List Byte}
    (ha : a < 8) (han : a ≠ aN) (hao : a ≠ aOne) (har : a ≠ aR2)
    (hsp : sp < 32) (hsl : sl < 32)
    (h : PowerCallPrepared p.toPowerCallPublic s)
    (hp : word s.mem p.x.B (8 * sp) = ptr)
    (hl : word s.mem p.x.B (8 * sl) = BitVec.ofNat 64 bs.length)
    (hs : Src s p.x.B p.x.Z ptr bs) (h1 : 1 ≤ bs.length)
    (hfit : (bs.length + 7) / 8 ≤ p.x.wx) :
    WP isa (Arithmetic.load a sp sl) s (PowerCallPrepared p.toPowerCallPublic) := by
  obtain ⟨⟨hc, hm, hb⟩, hone, hr2⟩ := h
  have hlen : bs.length < 2 ^ 31 := by
    have hw48 : p.x.wx ≤ 48 := p.width48
    omega_using [hfit, hw48]
  refine WP.mono (load_ok hc p.lower p.fits p.upper ha hsp hsl hp hl hs h1 hlen hfit)
    fun t ⟨hct, _, hf, hk⟩ => ?_
  have hfa : Arrays (off p.x.B p.x.o) p.x.wx [a] s.mem t.mem :=
    Arrays.of_outside (List.mem_singleton_self a) hf (Nat.le_refl _) (Nat.le_refl _)
  have hz := hc.good.scr.nowrap
  have hmn : aN ∉ [a] := by simpa using Ne.symm han
  have hmo : aOne ∉ [a] := by simpa using Ne.symm hao
  have hmr : aR2 ∉ [a] := by simpa using Ne.symm har
  have hmt : ModCtx t (off p.x.B p.x.o) (slot p.x.wx 8) p.x.wx p.minv p.modulus := by
    refine ⟨hct.good, (hfa.wv_of_not_mem (by decide) hmn hz).trans hm.modulus, ?_⟩
    rw [hfa.word0_of_not_mem (by decide) hmn hz (by have := p.lower; omega_using [h1, hfit])]
    exact hm.inverse
  exact ⟨⟨hct, hmt, hb.frame hc (arrays_work hfa (by intro j hj; obtain rfl := List.mem_singleton.mp hj; exact ha)) hk⟩,
    (hfa.wv_of_not_mem (by decide) hmo hz).trans hone,
    (hfa.wv_of_not_mem (by decide) hmr hz).trans hr2⟩

theorem productCall_ct (M : Mont) :
    RelCT isa (Two (fun p : ProductCallPublic => PowerCallPre p.toPowerCallPublic))
      (Arithmetic.product M.mm arg argLen arg2 arg2Len) (fun _ _ => True) := by
  unfold Arithmetic.product seqs
  refine RelCT.seq (two_post (Ψ := fun p : ProductCallPublic => PowerCallPrepared p.toPowerCallPublic)
    (two_map (fun p : ProductCallPublic => p.toPowerPublic.product)
      (fun p _ h => ⟨h.2.1, p.width48, p.greater, p.odd⟩) (constants_ct M))
    (fun _ _ h => powerCall_prepare M h)) ?_
  refine RelCT.seq (two_post (Ψ := fun p : ProductCallPublic => PowerCallPrepared p.toPowerCallPublic)
    (two_map (fun p : ProductCallPublic => (⟨p.x, p.base, p.baseLen⟩ : BPub)) ?_
      (loadArr_ct (j := aX) (sp := arg) (sl := argLen) (by decide) (by taint_decide) (by taint_decide))) ?_) ?_
  · intro p s ⟨⟨hc, _, bb, _, hp, hl, _, _, hbl, _, hb, _⟩, _⟩
    refine ⟨p.minv, bb, hc, p.lower, p.fits, p.upper, by decide, by decide, by decide,
      hp, hl, hbl, hb, hbl ▸ p.basePositive, ?_, hbl ▸ p.baseFits⟩
    have hbw : (bb.length + 7) / 8 ≤ p.x.wx := hbl ▸ p.baseFits
    have hw48 : p.x.wx ≤ 48 := p.width48
    omega_using [hbw, hw48]
  · intro p s h
    obtain ⟨bb, _, hp, hl, _, _, hbl, _, hb, _⟩ := h.1.2.2
    exact productCall_load (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      h hp hl hb (hbl ▸ p.basePositive) (hbl ▸ p.baseFits)
  refine RelCT.seq (two_post (Ψ := fun p : ProductCallPublic => PowerCallPrepared p.toPowerCallPublic)
    (two_map (fun p : ProductCallPublic => p.bytes) ?_
      (loadArr_ct (j := aXm) (sp := arg2) (sl := arg2Len) (by decide) (by taint_decide) (by taint_decide))) ?_) ?_
  · intro p s ⟨⟨hc, _, _, eb, _, _, hp, hl, _, hel, _, hb⟩, _⟩
    refine ⟨p.minv, eb, hc, p.lower, p.fits, p.upper, by decide, by decide, by decide,
      hp, hl, hel, hb, hel ▸ p.expPositive, ?_, hel ▸ p.secondFits⟩
    have hbw : (eb.length + 7) / 8 ≤ p.x.wx := hel ▸ p.secondFits
    have hw48 : p.x.wx ≤ 48 := p.width48
    omega_using [hbw, hw48]
  · intro p s h
    obtain ⟨_, eb, _, _, hp, hl, _, hel, _, hb⟩ := h.1.2.2
    exact productCall_load (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      h hp hl hb (hel ▸ p.expPositive) (hel ▸ p.secondFits)
  exact two_map (fun p : ProductCallPublic => p.toPowerPublic.product) (fun p s ⟨⟨_, hm, _⟩, hone, hr2⟩ => by
    refine ⟨hm, ?_⟩
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · dsimp only [PowerPublic.product]
      rw [hr2]
      exact Nat.mod_lt _ (by have := p.greater; omega_using [this])
    · dsimp only [PowerPublic.product]
      rw [hone]
      exact p.greater) (productCore_ct M)

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.AddCallCT`, which only this module used -/

section

/-! # Constant time of loading and adding DSA scalars -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64 VG.Impl.Rsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem callLoad_context {p : PowerCallPublic} {s : State} {a sp sl : Nat}
    {ptr : Addr} {bs : List Byte} (ha : a < 8) (han : a ≠ aN) (hsp : sp < 32) (hsl : sl < 32)
    (h : PowerCallPre p s) (hp : word s.mem p.x.B (8 * sp) = ptr)
    (hl : word s.mem p.x.B (8 * sl) = BitVec.ofNat 64 bs.length)
    (hs : Src s p.x.B p.x.Z ptr bs) (h1 : 1 ≤ bs.length)
    (hfit : (bs.length + 7) / 8 ≤ p.x.wx) :
    WP isa (Arithmetic.load a sp sl) s (PowerCallPre p) := by
  have hlen : bs.length < 2 ^ 31 := by
    have hw48 : p.x.wx ≤ 48 := p.width48
    omega_using [hfit, hw48]
  exact WP.mono (load_mod_ok h.1 h.2.1 p.lower p.fits p.upper ha han hsp hsl hp hl hs h1 hlen hfit)
    fun t ⟨hc, hm, _, _, hf, hk⟩ => ⟨hc, hm, h.2.2.frame h.1 hf hk⟩

theorem addCall_ct :
    RelCT isa (Two (fun p : ProductCallPublic => PowerCallPre p.toPowerCallPublic))
      (seqs [Arithmetic.load aX arg argLen, Arithmetic.load aXm arg2 arg2Len, Crt.addMod aY aX aXm])
      (fun _ _ => True) := by
  unfold seqs
  refine RelCT.seq (two_post (Ψ := fun p : ProductCallPublic => PowerCallPre p.toPowerCallPublic)
    (two_map (fun p : ProductCallPublic => (⟨p.x, p.base, p.baseLen⟩ : BPub)) ?_
      (loadArr_ct (j := aX) (sp := arg) (sl := argLen) (by decide) (by taint_decide) (by taint_decide))) ?_) ?_
  · intro p s ⟨hc, _, bb, _, hp, hl, _, _, hbl, _, hb, _⟩
    refine ⟨p.minv, bb, hc, p.lower, p.fits, p.upper, by decide, by decide, by decide,
      hp, hl, hbl, hb, hbl ▸ p.basePositive, ?_, hbl ▸ p.baseFits⟩
    have hbw : (bb.length + 7) / 8 ≤ p.x.wx := hbl ▸ p.baseFits
    have hw48 : p.x.wx ≤ 48 := p.width48
    omega_using [hbw, hw48]
  · intro p s h
    obtain ⟨bb, _, hp, hl, _, _, hbl, _, hb, _⟩ := h.2.2
    exact callLoad_context (by decide) (by decide) (by decide) (by decide)
      h hp hl hb (hbl ▸ p.basePositive) (hbl ▸ p.baseFits)
  refine RelCT.seq (two_post (Ψ := fun p : ProductCallPublic => PowerCallPre p.toPowerCallPublic)
    (two_map (fun p : ProductCallPublic => p.bytes) ?_
      (loadArr_ct (j := aXm) (sp := arg2) (sl := arg2Len) (by decide) (by taint_decide) (by taint_decide))) ?_) ?_
  · intro p s ⟨hc, _, _, eb, _, _, hp, hl, _, hel, _, hb⟩
    refine ⟨p.minv, eb, hc, p.lower, p.fits, p.upper, by decide, by decide, by decide,
      hp, hl, hel, hb, hel ▸ p.expPositive, ?_, hel ▸ p.secondFits⟩
    have hbw : (eb.length + 7) / 8 ≤ p.x.wx := hel ▸ p.secondFits
    have hw48 : p.x.wx ≤ 48 := p.width48
    omega_using [hbw, hw48]
  · intro p s h
    obtain ⟨_, eb, _, _, hp, hl, _, hel, _, hb⟩ := h.2.2
    exact callLoad_context (by decide) (by decide) (by decide) (by decide)
      h hp hl hb (hel ▸ p.expPositive) (hel ▸ p.secondFits)
  exact two_map (fun p : ProductCallPublic => p.x.ws)
    (fun p _ h => ⟨⟨_, h.1.good, Nat.le_refl _⟩,
      by change 1 ≤ p.x.wx; have hw : 2 ≤ p.x.wx := p.lower; omega_using [hw],
      by change p.x.wx < 2 ^ 31; have hw : p.x.wx ≤ p.x.w := p.fits; have hw' : p.x.w < 2 ^ 30 := p.upper; omega_using [hw, hw']⟩)
    (addCode_ct (by decide) (by decide) (by decide) (by decide) (by decide)
      (by taint_decide) (by taint_decide) (by taint_decide))

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.ReduceCallCT`, which only this module used -/

section

/-! ### `Dsa.X86_64.ReduceLoopCT`, which only this module used -/

section

/-! # Constant time of nonempty streaming reduction -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def ReducePublic.remaining (p : ReducePublic) (j : Nat) : ReducePublic :=
  { p with bytes := { p.bytes with ptr := p.bytes.ptr + BitVec.ofNat 64 j, len := p.bytes.len - j }
           lengthBound := Nat.lt_of_le_of_lt (Nat.sub_le _ _) p.lengthBound }

def ReduceLoopPre (p : ReducePublic) (j : Nat) (s : State) : Prop :=
  ∃ (bs : List Byte) (acc : Nat), bs.length = p.bytes.len - j ∧
    ReduceState s p.bytes.x.B p.bytes.x.Z p.bytes.x.o p.bytes.x.w p.bytes.x.wx
      p.modulus p.minv (p.bytes.ptr + BitVec.ofNat 64 j) bs acc

theorem reduceLoop_step (M : Mont) {p : ReducePublic} {j : Nat} {s : State}
    (hj : j < p.bytes.len) (h : ReduceLoopPre p j s) :
    WP isa (Arithmetic.reduceByte M.mm) s fun t =>
      isa.eval .ne t = some (decide (j + 1 < p.bytes.len)) ∧ ReduceLoopPre p (j + 1) t := by
  obtain ⟨bs, acc, hlen, h⟩ := h
  cases bs with
  | nil => simp only [List.length_nil] at hlen; omega
  | cons b bs =>
    refine WP.mono (reduceByte_ok M h p.lower (by have := p.fits; have := p.upper; omega_arith)
      p.greater255 p.odd (by have := p.lengthBound; omega_using [hlen, this]))
      fun t ⟨ht, hz, _, _⟩ => ?_
    have hpos : p.bytes.ptr + BitVec.ofNat 64 j + 1 = p.bytes.ptr + BitVec.ofNat 64 (j + 1) := by
      rw [BitVec.add_assoc, ofNat_add_one]
    refine ⟨?_, bs, _, ?_, hpos ▸ ht⟩
    · change VG.X86_64.eval .ne t = _
      simp only [VG.X86_64.eval, hz, Option.map_some]
      apply congrArg some
      apply Bool.eq_iff_iff.mpr
      by_cases he : bs.length = 0
      · simp only [he, decide_true, Bool.not_true, Bool.false_eq_true, decide_eq_true_eq, false_iff]
        simp only [List.length_cons] at hlen
        omega_using [hlen, he]
      · simp only [he, decide_false, Bool.not_false, decide_eq_true_eq, true_iff]
        simp only [List.length_cons] at hlen
        omega_using [hlen, he]
    · simp only [List.length_cons] at hlen
      omega_using [hlen]

theorem reduceLoop_ct (M : Mont) :
    RelCT isa (Two fun p s => 0 < p.bytes.len ∧ ReduceLoopPre p 0 s)
      (.loop (Arithmetic.reduceByte M.mm) .ne) (fun _ _ => True) := by
  have hct := two_map (Φ := fun (p : ReducePublic × Nat) s => p.2 < p.1.bytes.len ∧ ReduceLoopPre p.1 p.2 s)
    (fun p : ReducePublic × Nat => p.1.remaining p.2)
    (fun p s ⟨hj, bs, acc, hlen, h⟩ =>
      ⟨bs, acc, hlen, by omega_using [hj, hlen], h⟩) (reduceByte_ct M)
  refine (two_loop (Φ := ReduceLoopPre) (Ψ := fun _ _ => True) (fun p => p.bytes.len) hct ?_).mono
    (fun _ _ h => h) (fun _ _ _ => trivial)
  intro p j s hj hs
  exact WP.mono (reduceLoop_step M hj hs) fun t ⟨hz, ht⟩ => ⟨hz, fun _ => ht, fun _ => trivial⟩

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.ReduceSetupCT`, which only this module used -/

section

/-! # Constant time of streaming-reduction setup -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def ReduceContext (p : ReducePublic) (s : State) : Prop :=
  SubCtx s p.bytes.x.B p.bytes.x.Z p.bytes.x.o p.bytes.x.w p.bytes.x.wx p.minv ∧
  ModCtx s (off p.bytes.x.B p.bytes.x.o) (slot p.bytes.x.wx 8) p.bytes.x.wx p.minv p.modulus

def ReduceSetupPre (p : ReducePublic) (s : State) : Prop :=
  ReduceContext p s ∧ p.bytes.x.wx ≤ 48

def ReduceDoublePre (p : ReducePublic) (s : State) : Prop :=
  ReduceContext p s ∧ wv s.mem (off p.bytes.x.B p.bytes.x.o) (slot p.bytes.x.wx aR2) p.bytes.x.wx < p.modulus

theorem reduceSetup_ct (M : Mont) : RelCT isa (Two ReduceSetupPre)
    (Arithmetic.reduceSetup M.mm) (fun _ _ => True) := by
  unfold Arithmetic.reduceSetup seqs
  refine RelCT.seq (two_post (Ψ := fun p s => ReduceContext p s ∧
    wv s.mem (off p.bytes.x.B p.bytes.x.o) (slot p.bytes.x.wx aOne) p.bytes.x.wx = 1)
    (two_map (fun p : ReducePublic => p.toPowerPublic.product)
      (fun p s h => ⟨h.1.2, h.2, p.greater, p.odd⟩) (constants_ct M)) ?_) ?_
  · intro p s ⟨⟨hc, hm⟩, hw⟩
    exact WP.mono (prepare_ok M hc p.lower hw p.greater p.odd hm.modulus hm.inverse)
      fun t ⟨hct, hmt, hone, _⟩ => ⟨⟨hct, hmt⟩, hone⟩
  refine RelCT.seq (two_post (Ψ := ReduceDoublePre)
    (two_map (fun p : ReducePublic => p.bytes.x.ws)
      (fun _ _ h => ⟨_, h.1.1.good, Nat.le_refl _⟩) (M.ct (by unfold MmUse; decide))) ?_) ?_
  · intro p s ⟨⟨hc, hm⟩, hone⟩
    exact WP.mono (mont_step M hm (Nat.le_refl _) p.lower
      (by have := p.fits; have := p.upper; omega_arith) (by unfold MmUse; decide)
      (by rw [hone]; exact p.greater)) fun t ⟨hmt, hlt, _, hf, hk⟩ =>
        ⟨⟨arrays_context hc hf (by decide) hk, hmt⟩, hlt⟩
  refine RelCT.seq (two_piece (Ψ := fun p s => ReduceDoublePre p s ∧ s.gpr .rcx = 8) []
    (by intro p s t hs ht r hr; cases hr) (by taint_decide) ?_) ?_
  · intro p s ⟨⟨hc, hm⟩, hlt⟩
    refine WP.mono (WP.keep [.rcx] (Q := fun t => t.gpr .rcx = 8 ∧ t.mem = s.mem)
      (by xrun) rfl) fun t ⟨⟨hcx, hmem⟩, hk⟩ => ?_
    have hct := hc.of_keep hmem hk (by decide)
    exact ⟨⟨⟨hct, ⟨hct.good, hmem ▸ hm.modulus, hmem ▸ hm.inverse⟩⟩, hmem ▸ hlt⟩, hcx⟩
  refine RelCT.seq (two_post (Ψ := ReduceContext)
    (two_map (fun p : ReducePublic => (⟨p.toPowerPublic.product.layout, 8⟩ : DblPub)) ?_
      ((doubles_ct (mo := aN) (acc := aAcc) (tmp := aTmp) (o := aR2) (sl := sCnt) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by taint_decide) (by taint_decide) (by taint_decide)).mono
          (fun _ _ h => h) (fun _ _ _ => True.intro))) ?_) ?_
  · intro p s ⟨⟨⟨hc, hm⟩, hlt⟩, hcx⟩
    exact ⟨⟨hc.good, Nat.le_refl _⟩, p.lower,
      by change p.bytes.x.wx < 2 ^ 31; have := p.fits; have := p.upper; omega_arith,
      by change 1 ≤ 8; decide, by change 8 < 2 ^ 31; decide, hcx, by
        change wv s.mem (off p.bytes.x.B p.bytes.x.o) (slot p.bytes.x.wx aR2) p.bytes.x.wx <
          wv s.mem (off p.bytes.x.B p.bytes.x.o) (slot p.bytes.x.wx aN) p.bytes.x.wx
        rw [hm.modulus]; exact hlt⟩
  · intro p s ⟨⟨⟨hc, hm⟩, hlt⟩, hcx⟩
    exact WP.mono (double_mod_ok hc hm p.lower (by have := p.fits; have := p.upper; omega_arith)
      (by decide) (by decide) (c := 8) hcx hlt) fun t ⟨hct, hmt, _⟩ => ⟨hct, hmt⟩
  refine RelCT.seq (two_post (Ψ := ReduceContext)
    (two_map (fun p : ReducePublic => p.bytes.x.ws)
      (fun _ _ h => ⟨_, h.1.good, Nat.le_refl _⟩)
      (zeroArr_ct (by decide) (by taint_decide))) ?_) ?_
  · intro p s ⟨hc, hm⟩
    exact WP.mono (clear_mod_ok hc hm p.lower (by have := p.fits; have := p.upper; omega_arith)
      (by decide) (by decide)) fun t ⟨hct, hmt, _⟩ => ⟨hct, hmt⟩
  exact two_map (fun p : ReducePublic => p.bytes.x.ws)
    (fun _ _ h => ⟨_, h.1.good, Nat.le_refl _⟩)
    (zeroArr_ct (by decide) (by taint_decide))

end VG.Proof.Dsa.X86_64

end

end

/-! # Constant time of complete DSA streaming reduction, including empty inputs -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.X86_64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def ReduceCallBytes (p : ReducePublic) (s : State) : Prop := ∃ bs : List Byte,
  bs.length = p.bytes.len ∧ word s.mem p.bytes.x.B (8 * arg) = p.bytes.ptr ∧
  word s.mem p.bytes.x.B (8 * argLen) = BitVec.ofNat 64 bs.length ∧
  Src s p.bytes.x.B p.bytes.x.Z p.bytes.ptr bs

def ReduceCallPre (p : ReducePublic) (s : State) : Prop := ReduceSetupPre p s ∧ ReduceCallBytes p s

def ReduceCallPrepared (p : ReducePublic) (s : State) : Prop :=
  ReduceContext p s ∧ ReduceCallBytes p s ∧
  wv s.mem (off p.bytes.x.B p.bytes.x.o) (slot p.bytes.x.wx aR2) p.bytes.x.wx =
    256 * 2 ^ (64 * p.bytes.x.wx) % p.modulus ∧
  wv s.mem (off p.bytes.x.B p.bytes.x.o) (slot p.bytes.x.wx aY) p.bytes.x.wx = 0 ∧
  wv s.mem (off p.bytes.x.B p.bytes.x.o) (slot p.bytes.x.wx aX) p.bytes.x.wx = 0

def ReduceStart (p : ReducePublic) (s : State) : Prop :=
  ReduceLoopPre p 0 s ∧ s.zf = some (decide (p.bytes.len = 0))

theorem reduceCall_setup (M : Mont) {p : ReducePublic} {s : State} (h : ReduceCallPre p s) :
    WP isa (Arithmetic.reduceSetup M.mm) s (ReduceCallPrepared p) := by
  obtain ⟨⟨⟨hc, hm⟩, hw⟩, bs, hlen, hp, hl, hs⟩ := h
  refine WP.mono (reduceSetup_ok M hc p.lower hw p.greater p.odd hm.modulus hm.inverse)
    fun t ⟨hct, hmt, hr, hy, hx, hf, hk⟩ => ?_
  exact ⟨⟨hct, hmt⟩, ⟨bs, hlen, (work_parent hc hf (by decide)).trans hp,
    (work_parent hc hf (by decide)).trans hl, work_source hc hf hk hs⟩, hr, hy, hx⟩

theorem reduceCall_init {p : ReducePublic} {s : State} (h : ReduceCallPrepared p s) :
    WP isa (.block (Arithmetic.reduceInit arg argLen)) s (ReduceStart p) := by
  obtain ⟨⟨hc, hm⟩, ⟨bs, hlen, hp, hl, hs⟩, hr, hy, hx⟩ := h
  refine WP.mono (reduceInit_ok hc hm (by decide) (by decide) hp hl (hlen ▸ p.lengthBound))
    fun t ⟨hct, hmt, harr, hptr, hrem, hz, hf, hk⟩ => ?_
  have ht : ReduceState t p.bytes.x.B p.bytes.x.Z p.bytes.x.o p.bytes.x.w p.bytes.x.wx
      p.modulus p.minv p.bytes.ptr bs 0 :=
    ⟨hct, hmt, (harr aR2 (by decide)).trans hr,
      fun i hi _ => (wv_eq_zero_iff _ _ _ _).mp ((harr aX (by decide)).trans hx) i hi,
      (harr aY (by decide)).trans hy, by have := p.greater; omega_using [this], hptr, hrem,
      work_source hc hf hk hs⟩
  refine ⟨⟨bs, 0, ?_, ?_⟩, ?_⟩
  · simpa only [Nat.sub_zero] using hlen
  · simpa only [BitVec.add_zero] using ht
  · simpa only [hlen] using hz

theorem reduceCall_ct (M : Mont) : RelCT isa (Two ReduceCallPre)
    (Arithmetic.reduce M.mm arg argLen) (fun _ _ => True) := by
  unfold Arithmetic.reduce seqs
  refine RelCT.seq (two_post (Ψ := ReduceCallPrepared)
    (two_map (fun p : ReducePublic => p) (fun _ _ h => h.1) (reduceSetup_ct M))
    (fun _ _ h => reduceCall_setup M h)) ?_
  refine RelCT.seq (two_post (Ψ := ReduceStart)
    (two_map (fun p : ReducePublic => p.bytes.x) (fun _ _ h => ⟨_, h.1.1⟩) reduceInit_ct)
    (fun _ _ h => reduceCall_init h)) ?_
  refine two_ite (fun p s t hs ht => by simp only [eval, hs.2, ht.2]) ?_ ?_
  · exact two_taint [] (by intro p s t hs ht r hr; cases hr) (by taint_decide)
  · exact two_map (fun p : ReducePublic => p) (fun p s h => by
      refine ⟨?_, h.1.1⟩
      have hz := h.1.2
      have he := h.2
      change VG.X86_64.eval .e s = some false at he
      simp only [VG.X86_64.eval, hz, Option.some.injEq, decide_eq_false_iff_not] at he
      omega_using [he]) (reduceLoop_ct M)

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.FinishCT`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.StoreCT`, which only this module used -/

section

/-! # Constant-time encoding of an arithmetic result -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.X86_64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def StorePre (p : BPub) (s : State) : Prop := ∃ minv,
  SubCtx s p.x.B p.x.Z p.x.o p.x.w p.x.wx minv ∧
  word s.mem p.x.B (8 * result) = p.ptr ∧ word s.mem p.x.B (8 * resultLen) = BitVec.ofNat 64 p.len

def StoreRegs (p : BPub) (s : State) : Prop :=
  s.gpr .rbx = off (off p.x.B p.x.o) (slot p.x.wx aY) ∧
  s.gpr .rsi = p.ptr ∧ s.gpr .rcx = BitVec.ofNat 64 p.len

theorem store_ct : RelCT isa (Two StorePre) (Arithmetic.store aY result resultLen) (fun _ _ => True) := by
  unfold Arithmetic.store seqs
  refine RelCT.seq (RelCT.block_append (l₁ := ([.mov .rax (.mem (hdr Crt.sLink))] : List Instr))
    (RelCT.seq (two_piece (Ψ := fun p s => StorePre p s ∧ s.gpr .rax = p.x.B) [.rdi]
      (pins_of (fun p _ => off p.x.B p.x.o) (by
        intro p s ⟨_, hc, _⟩ r hr
        obtain rfl := List.mem_singleton.mp hr
        exact hc.rdi)) (by taint_decide) ?_)
      (two_piece (Ψ := StoreRegs) [.rdi, .rax]
        (pins_of (fun p r => if r = .rdi then off p.x.B p.x.o else p.x.B) (by
          intro p s ⟨⟨_, hc, _⟩, ha⟩ r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact hc.rdi
          · exact ha)) (by taint_decide) ?_))) ?_
  · intro p s ⟨minv, hc, hp, hl⟩
    refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = p.x.B ∧ t.mem = s.mem)
      ?_ rfl) fun t ⟨⟨ha, hm⟩, hk⟩ =>
      ⟨⟨minv, hc.mem hm hk (by decide), hm ▸ hp, hm ▸ hl⟩, ha⟩
    xrun [State.ea, hdr, hc.rdi, hdrOff, hc.link,
      hc.good.scr.ld (show 8 * Crt.sLink + 8 ≤ slot p.x.wx 8 by
        have := hdr_lt_slot p.x.wx 8 (show Crt.sLink < 32 by decide); omega_using [this])]
  · intro p s ⟨⟨minv, hc, hp, hl⟩, ha⟩
    have hsmall : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off p.x.B p.x.o) (8 * i)) 8 :=
      fun i hi => hc.good.scr.ld (by have := hdr_lt_slot p.x.wx 8 hi; omega_using [this])
    have hlarge : ∀ i < 32, InRegions (s.rd ++ s.wr) (off p.x.B (8 * i)) 8 :=
      fun i hi => hc.scr.ld (by
        have := hc.lo; have := hc.hi
        have : 256 ≤ slot p.x.w 8 := by unfold slot hdrBytes; omega_using []
        omega_arith)
    xrun [StoreRegs, State.ea, hdr, Crt.ws, hc.rdi, ha, hdrOff,
      hlarge result (by decide), hlarge resultLen (by decide), hp, hl,
      hsmall (sArr aY) (by decide), hc.hdr.harr aY (by decide)]
  exact two_taint [.rbx, .rsi, .rcx]
    (pins_of (fun p r => if r = .rbx then off (off p.x.B p.x.o) (slot p.x.wx aY)
      else if r = .rsi then p.ptr else BitVec.ofNat 64 p.len) (by
        intro p s h r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact h.1
        · exact h.2.1
        · exact h.2.2)) (by taint_decide)

end VG.Proof.Dsa.X86_64

end

end

/-! # Constant time of arithmetic result storage and return -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.X86_64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def FinishPre (p : BPub) (s : State) : Prop := StorePre p s ∧
  1 ≤ p.len ∧ p.len < 2 ^ 31 ∧ p.x.wx = (p.len + 7) / 8 ∧
  (∀ j < p.len, InRegions s.wr (p.ptr + BitVec.ofNat 64 j) 1) ∧
  (∀ j < p.len, p.x.Z ≤ ofs p.x.B (p.ptr + BitVec.ofNat 64 j))

theorem finish_ct : RelCT isa (Two FinishPre) (seqs Core.finish) (fun _ _ => True) := by
  unfold Core.finish seqs
  refine RelCT.seq (two_post (Ψ := fun p s => s.gpr .rdi = off p.x.B p.x.o)
    (two_map (fun p : BPub => p) (fun _ _ h => h.1) store_ct) ?_) ?_
  · intro p s ⟨⟨minv, hc, hp, hl⟩, h1, h31, hw, hout, hpre⟩
    exact WP.mono (storeSuffix_ok hc (by decide) (by decide) (by decide) hp hl h1 h31 hw hout hpre)
      fun t ⟨hct, _⟩ => hct.rdi
  exact two_taint [.rdi]
    (pins_of (fun p _ => off p.x.B p.x.o) (by
      intro p s h r hr
      obtain rfl := List.mem_singleton.mp hr
      exact h)) (by taint_decide)

end VG.Proof.Dsa.X86_64

end

end

/-! # Retaining public result bindings across arithmetic calls -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem FinishPre.work {p : BPub} {s t : State} {minv : BitVec 64}
    (h : FinishPre p s) (hc : SubCtx s p.x.B p.x.Z p.x.o p.x.w p.x.wx minv)
    (ht : SubCtx t p.x.B p.x.Z p.x.o p.x.w p.x.wx minv)
    (hf : Frm (off p.x.B p.x.o) (workRanges p.x.wx) s.mem t.mem) (hk : Keep mmRegs s t) :
    FinishPre p t := by
  obtain ⟨⟨_, _, hp, hl⟩, h1, h31, hw, hout, hpre⟩ := h
  exact ⟨⟨minv, ht, (work_parent hc hf (by decide)).trans hp,
    (work_parent hc hf (by decide)).trans hl⟩, h1, h31, hw,
    fun j hj => by rw [hk.2.2]; exact hout j hj, hpre⟩

structure PowerFinishPublic extends PowerCallPublic where
  output : Addr
  outputLen : Nat

def PowerFinishPublic.result (p : PowerFinishPublic) : BPub := ⟨p.x, p.output, p.outputLen⟩

def PowerFinishPre (p : PowerFinishPublic) (s : State) : Prop :=
  PowerCallPre p.toPowerCallPublic s ∧ FinishPre p.result s

theorem powerFinish_ct (M : Mont) (Sq : MontS) : RelCT isa (Two PowerFinishPre)
    (.seq (Arithmetic.power Sq.mm M.mm arg argLen arg2 arg2Len) (seqs Core.finish)) (fun _ _ => True) := by
  refine RelCT.seq (two_post (Ψ := fun p s => FinishPre p.result s)
    (two_map PowerFinishPublic.toPowerCallPublic (fun _ _ h => h.1) (powerCall_ct M Sq)) ?_)
    (two_map PowerFinishPublic.result (fun _ _ h => h) finish_ct)
  intro p s ⟨⟨hc, hm, bb, eb, hp, hl, hep, hel, hbl, helen, hb, he⟩, hf⟩
  exact WP.mono (power_ok M Sq hc p.lower p.width48 p.fits p.upper p.greater p.odd
    hm.modulus hm.inverse (by decide) (by decide) (by decide) (by decide)
    hp hl hb (hbl ▸ p.basePositive) (hbl ▸ p.baseFits)
    hep hel he (helen ▸ p.expPositive) (helen ▸ p.expLimit))
    fun t ⟨hct, _, _, hft, hkt⟩ => hf.work hc hct hft hkt

structure ProductFinishPublic extends ProductCallPublic where
  output : Addr
  outputLen : Nat

def ProductFinishPublic.result (p : ProductFinishPublic) : BPub := ⟨p.x, p.output, p.outputLen⟩

def ProductFinishPre (p : ProductFinishPublic) (s : State) : Prop :=
  PowerCallPre p.toPowerCallPublic s ∧ FinishPre p.result s

theorem productFinish_ct (M : Mont) : RelCT isa (Two ProductFinishPre)
    (.seq (Arithmetic.product M.mm arg argLen arg2 arg2Len) (seqs Core.finish)) (fun _ _ => True) := by
  refine RelCT.seq (two_post (Ψ := fun p s => FinishPre p.result s)
    (two_map ProductFinishPublic.toProductCallPublic (fun _ _ h => h.1) (productCall_ct M)) ?_)
    (two_map ProductFinishPublic.result (fun _ _ h => h) finish_ct)
  intro p s ⟨⟨hc, hm, bb, eb, hp, hl, hep, hel, hbl, helen, hb, he⟩, hf⟩
  exact WP.mono (product_ok M hc p.lower p.width48 p.fits p.upper p.greater p.odd
    hm.modulus hm.inverse (by decide) (by decide) (by decide) (by decide)
    hp hl hb (hbl ▸ p.basePositive) (hbl ▸ p.baseFits)
    hep hel he (helen ▸ p.expPositive) (helen ▸ p.secondFits))
    fun t ⟨hct, _, _, hft, hkt⟩ => hf.work hc hct hft hkt

structure ReduceFinishPublic extends ReducePublic where
  output : Addr
  outputLen : Nat

def ReduceFinishPublic.result (p : ReduceFinishPublic) : BPub := ⟨p.bytes.x, p.output, p.outputLen⟩

def ReduceFinishPre (p : ReduceFinishPublic) (s : State) : Prop :=
  ReduceCallPre p.toReducePublic s ∧ FinishPre p.result s

theorem reduceFinish_ct (M : Mont) : RelCT isa (Two ReduceFinishPre)
    (.seq (Arithmetic.reduce M.mm arg argLen) (seqs Core.finish)) (fun _ _ => True) := by
  refine RelCT.seq (two_post (Ψ := fun p s => FinishPre p.result s)
    (two_map ReduceFinishPublic.toReducePublic (fun _ _ h => h.1) (reduceCall_ct M)) ?_)
    (two_map ReduceFinishPublic.result (fun _ _ h => h) finish_ct)
  intro p s ⟨⟨⟨⟨hc, hm⟩, hw⟩, bs, hlen, hp, hl, hs⟩, hf⟩
  exact WP.mono (reduce_ok M hc p.lower hw p.greater255 p.odd hm.modulus hm.inverse
    (by decide) (by decide) hp hl hs (hlen ▸ p.lengthBound))
    fun t ⟨hct, _, _, hft, hkt⟩ => hf.work hc hct hft hkt

theorem sourceBytes_eq {s : State} {B ptr : Addr} {Z : Nat} {bs : List Byte}
    (h : Src s B Z ptr bs) : Spec.Rsa.bytesAt s.mem ptr bs.length = bs := by
  apply List.ext_getElem
  · simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
  · intro i hi hj
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
    exact h.val i hj

def AddFinishPre (p : ProductFinishPublic) (s : State) : Prop := ProductFinishPre p s ∧
  Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem p.base p.baseLen) < p.modulus ∧
  Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem p.bytes.ptr p.bytes.len) < p.modulus

theorem addFinish_ct : RelCT isa (Two AddFinishPre)
    (.seq (seqs [Arithmetic.load aX arg argLen, Arithmetic.load aXm arg2 arg2Len,
      VG.Impl.Rsa.X86_64.Crt.addMod aY aX aXm]) (seqs Core.finish)) (fun _ _ => True) := by
  refine RelCT.seq (two_post (Ψ := fun p s => FinishPre p.result s)
    (two_map ProductFinishPublic.toProductCallPublic (fun _ _ h => h.1.1) addCall_ct) ?_)
    (two_map ProductFinishPublic.result (fun _ _ h => h) finish_ct)
  intro p s ⟨⟨⟨hc, hm, bb, eb, hp, hl, hep, hel, hbl, helen, hb, he⟩, hf⟩, hbr, her⟩
  rw [← hbl, sourceBytes_eq hb] at hbr
  rw [← helen, sourceBytes_eq he] at her
  exact WP.mono (add_ok hc hm p.lower p.width48 p.fits p.upper
    (by decide) (by decide) (by decide) (by decide)
    hp hl hb (hbl ▸ p.basePositive) (hbl ▸ p.baseFits)
    hep hel he (helen ▸ p.expPositive) (helen ▸ p.secondFits) hbr her)
    fun t ⟨hct, _, _, hft, hkt⟩ => hf.work hc hct hft hkt

end VG.Proof.Dsa.X86_64

end

end

/-! # Public argument binding for complete arithmetic calls -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure Call3Public extends PowerFinishPublic where
  parentInverse : BitVec 64
  extent : pWorkspace ≤ bytes.x.Z
  childLow : slot bytes.x.w 8 ≤ bytes.x.o
  childHigh : bytes.x.o + slot bytes.x.wx 8 + tabBytes bytes.x.wx ≤ bytes.x.Z
  offsetBound : bytes.x.o < 2 ^ 31
  outputPositive : 1 ≤ outputLen
  outputBound : outputLen < 2 ^ 31
  outputWidth : bytes.x.wx = (outputLen + 7) / 8

def Call3Pre (a b output : Operand) (p : Call3Public) (s : State) : Prop :=
  Good s p.x.B p.x.Z p.x.w p.parentInverse ∧
  ChildReady s.mem p.x.B p.x.o p.x.wx p.modulus p.minv ∧
  (∃ ba bb : List Byte, OperandBytes s p.x.B p.x.Z a ba ∧ OperandBytes s p.x.B p.x.Z b bb ∧
    ba.length = p.baseLen ∧ bb.length = p.bytes.len) ∧
  pointerValue s.mem p.x.B a.pointer = p.base ∧ pointerValue s.mem p.x.B b.pointer = p.bytes.ptr ∧
  pointerValue s.mem p.x.B output.pointer = p.output ∧
  word s.mem p.x.B output.length.offset = BitVec.ofNat 64 p.outputLen ∧
  (∀ j < p.outputLen, InRegions s.wr (p.output + BitVec.ofNat 64 j) 1) ∧
  (∀ j < p.outputLen, p.x.Z ≤ ofs p.x.B (p.output + BitVec.ofNat 64 j))

def callHead (a b output : Operand) (o : Nat) : List Instr :=
  Core.operand arg argLen a ++ Core.operand arg2 arg2Len b ++
    Core.operand result resultLen output ++ Core.enter o

/-- The head can use any workspace offset shared by the two executions. -/
theorem callHead_run {p : Call3Public} {s : State} {a b output : Operand}
    (ha : pointerFits a.pointer) (hb : pointerFits b.pointer) (ho : pointerFits output.pointer)
    (h : Call3Pre a b output p s) :
    WP isa (.block (callHead a b output p.x.o)) s fun t =>
      PowerFinishPre p.toPowerFinishPublic t ∧ Frm p.x.B argumentRanges s.mem t.mem ∧ Keep coreRegs s t := by
  obtain ⟨hg, child, ⟨ba, bb, has, hbs, hbl, hel⟩, hp, hep, hop, hol, hout, hprefix⟩ := h
  have h256 : 256 ≤ slot p.x.w 8 := by unfold slot hdrBytes; omega_using []
  have hlo : slot p.x.w 8 ≤ p.x.o := p.childLow
  have hhi : p.x.o + slot p.x.wx 8 + tabBytes p.x.wx ≤ p.x.Z := p.childHigh
  unfold callHead
  rw [WP.block_append_iff]
  refine WP.mono (arguments_ok hg child p.extent (by omega_using [h256, hlo]) (by omega_using [hhi]) a b output ha hb ho)
    fun u ⟨hgu, hcu, hargs, _, hf, hk⟩ => ?_
  refine WP.mono (enter_ok hgu hcu.header p.childLow p.childHigh p.offsetBound)
    fun t ⟨hct, hmem, hkt⟩ => ?_
  have hft : Frm p.x.B argumentRanges s.mem t.mem := by rw [hmem]; exact hf
  have hkt' : Keep coreRegs s t := (hk.trans hkt).mono (by decide)
  have hargs' : Arguments t.mem s.mem p.x.B a b output := hmem ▸ hargs
  have childt : ChildReady t.mem p.x.B p.x.o p.x.wx p.modulus p.minv := hmem ▸ hcu
  refine ⟨⟨⟨hct, ⟨hct.good, childt.modulus, childt.inverse⟩,
    ba, bb, hargs'.1.trans hp, hargs'.2.1.trans has.length,
    hargs'.2.2.1.trans hep, hargs'.2.2.2.1.trans hbs.length, hbl, hel, ?_, ?_⟩,
    ⟨⟨p.minv, hct, hargs'.2.2.2.2.1.trans hop, hargs'.2.2.2.2.2.trans hol⟩,
      p.outputPositive, p.outputBound, p.outputWidth, ?_, hprefix⟩⟩, hft, hkt'⟩
  · rw [← hp]
    exact arguments_source hft hkt' (Nat.le_trans (by decide) p.extent) has.source
  · rw [← hep]
    exact arguments_source hft hkt' (Nat.le_trans (by decide) p.extent) hbs.source
  · intro j hj
    rw [hkt'.2.2]
    exact hout j hj

theorem callHead_ok {p : Call3Public} {s : State} {a b output : Operand}
    (ha : pointerFits a.pointer) (hb : pointerFits b.pointer) (ho : pointerFits output.pointer)
    (h : Call3Pre a b output p s) :
    WP isa (.block (callHead a b output p.x.o)) s (PowerFinishPre p.toPowerFinishPublic) :=
  WP.mono (callHead_run ha hb ho h) (fun _ h => h.1)

/-- The pointer-binding block addresses only saved fields and header slots;
operand bytes are not inspected until the arithmetic call. -/
theorem callHead_ct {a b output : Operand} {o : Nat}
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (callHead a b output o)) hc).isSome = true) :
    RelCT isa (Two (Call3Pre a b output)) (.block (callHead a b output o)) (fun _ _ => True) :=
  two_taint [.rdi] (pins_of (fun p _ => p.x.B) (by
    intro p s h r hr
    obtain rfl := List.mem_singleton.mp hr
    exact h.1.rdi)) hT

/-- Exponentiation from parent argument binding through result storage. -/
theorem corePow_ct (M : Mont) (Sq : MontS) {a b output : Operand} {o : Nat}
    (ha : pointerFits a.pointer) (hb : pointerFits b.pointer) (ho : pointerFits output.pointer)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (callHead a b output o)) hc).isSome = true) :
    RelCT isa (Two fun p s => Call3Pre a b output p s ∧ p.x.o = o)
      (Core.pow Sq.mm M.mm o a b output) (fun _ _ => True) := by
  change RelCT isa _ (.seq (.block (callHead a b output o))
    (.seq (Arithmetic.power Sq.mm M.mm arg argLen arg2 arg2Len) (seqs Core.finish))) _
  refine RelCT.seq (two_post (Ψ := fun p s => PowerFinishPre p.toPowerFinishPublic s)
    (two_map (fun p : Call3Public => p) (fun _ _ h => h.1) (callHead_ct hT)) ?_)
    (two_map Call3Public.toPowerFinishPublic (fun _ _ h => h) (powerFinish_ct M Sq))
  intro p s ⟨h, heq⟩
  rw [← heq]
  exact callHead_ok ha hb ho h

structure Call3ProductPublic extends Call3Public where
  secondFits : (bytes.len + 7) / 8 ≤ bytes.x.wx

def Call3ProductPublic.finish (p : Call3ProductPublic) : ProductFinishPublic :=
  { p.toPowerCallPublic with secondFits := p.secondFits, output := p.output, outputLen := p.outputLen }

theorem coreProduct_ct (M : Mont) {a b output : Operand} {o : Nat}
    (ha : pointerFits a.pointer) (hb : pointerFits b.pointer) (ho : pointerFits output.pointer)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (callHead a b output o)) hc).isSome = true) :
    RelCT isa (Two fun p : Call3ProductPublic => fun s => Call3Pre a b output p.toCall3Public s ∧ p.x.o = o)
      (Core.product M.mm o a b output) (fun _ _ => True) := by
  change RelCT isa _ (.seq (.block (callHead a b output o))
    (.seq (Arithmetic.product M.mm arg argLen arg2 arg2Len) (seqs Core.finish))) _
  refine RelCT.seq (two_post (Ψ := fun p s => ProductFinishPre p.finish s)
    (two_map Call3ProductPublic.toCall3Public (fun _ _ h => h.1) (callHead_ct hT)) ?_)
    (two_map Call3ProductPublic.finish (fun _ _ h => h) (productFinish_ct M))
  intro p s ⟨h, heq⟩
  rw [← heq]
  exact callHead_ok ha hb ho h

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.CallAddCT`, which only this module used -/

section

/-! # Constant time of the complete parent-to-child scalar addition -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64 VG.Impl.Rsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def CallAddPre (a b output : Operand) (p : Call3ProductPublic) (s : State) : Prop :=
  Call3Pre a b output p.toCall3Public s ∧ p.x.o = qWorkspace ∧
  Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem p.base p.baseLen) < p.modulus ∧
  Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem p.bytes.ptr p.bytes.len) < p.modulus

theorem callAddHead_ok {p : Call3ProductPublic} {s : State} {a b output : Operand}
    (ha : pointerFits a.pointer) (hb : pointerFits b.pointer) (ho : pointerFits output.pointer)
    (h : CallAddPre a b output p s) :
    WP isa (.block (callHead a b output qWorkspace)) s (AddFinishPre p.finish) := by
  obtain ⟨h, heq, hbr, her⟩ := h
  rw [← heq]
  refine WP.mono (callHead_run ha hb ho h) fun t ⟨ht, hf, hk⟩ => ?_
  obtain ⟨_, _, ⟨ba, bb, has, hbs, hbl, hel⟩, hp, hep, _⟩ := h
  have hsa : Src s p.x.B p.x.Z p.base ba := hp ▸ has.source
  have hsb : Src s p.x.B p.x.Z p.bytes.ptr bb := hep ▸ hbs.source
  have hta := arguments_source hf hk (Nat.le_trans (by decide) p.extent) hsa
  have htb := arguments_source hf hk (Nat.le_trans (by decide) p.extent) hsb
  refine ⟨ht, ?_, ?_⟩
  · change Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t.mem p.base p.baseLen) < p.modulus
    rw [← hbl, sourceBytes_eq hta]
    rw [← hbl, sourceBytes_eq hsa] at hbr
    exact hbr
  · change Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t.mem p.bytes.ptr p.bytes.len) < p.modulus
    rw [← hel, sourceBytes_eq htb]
    rw [← hel, sourceBytes_eq hsb] at her
    exact her

theorem coreAdd_ct {a b output : Operand}
    (ha : pointerFits a.pointer) (hb : pointerFits b.pointer) (ho : pointerFits output.pointer)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (callHead a b output qWorkspace)) hc).isSome = true) :
    RelCT isa (Two (CallAddPre a b output)) (Core.add a b output) (fun _ _ => True) := by
  change RelCT isa _ (.seq (.block (callHead a b output qWorkspace))
    (seqs ([Arithmetic.load aX arg argLen, Arithmetic.load aXm arg2 arg2Len,
      Crt.addMod aY aX aXm] ++ Core.finish))) _
  refine RelCT.seq (two_post (Ψ := fun p s => AddFinishPre p.finish s)
    (two_map Call3ProductPublic.toCall3Public (fun _ _ h => h.1) (callHead_ct hT))
    (fun _ _ h => callAddHead_ok ha hb ho h)) ?_
  exact RelCT.seqs_append (by simp) (by simp [Core.finish])
    (two_map Call3ProductPublic.finish (fun _ _ h => h) addFinish_ct)

end VG.Proof.Dsa.X86_64

end

end


/-! # Arithmetic timing in a persistent DSA execution workspace -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def ExecutionLayout.pointer (L : ExecutionLayout) : Pointer → Addr
  | .input f => L.fields f
  | .local d => off L.base d
  | .signatureS => L.fields .signature + L.fields .qLen

theorem Ready.publicPointer {L : ExecutionLayout} {s : State} (h : Ready L s)
    (p : Pointer) (hp : stablePointer p) : pointerValue s.mem L.base p = L.pointer p := by
  cases p with
  | input f => exact h.fields f hp
  | «local» _ => rfl
  | signatureS => exact congrArg₂ (· + ·) (h.fields .signature (by decide)) (h.fields .qLen (by decide))

structure ReadyCallPublic (side : ModulusSide) (d : Nat) where
  layout : ExecutionLayout
  baseLen : Nat
  exponentLen : Nat
  greater : 1 < side.value layout
  odd : side.value layout % 2 = 1
  basePositive : 1 ≤ baseLen
  baseFits : (baseLen + 7) / 8 ≤ side.words layout
  exponentPositive : 1 ≤ exponentLen
  exponentBound : exponentLen ≤ 1024
  outputStart : activeBytes ≤ d
  outputEnd : d + side.length layout ≤ usedBytes

def ReadyCallPublic.call {side : ModulusSide} {d : Nat} (p : ReadyCallPublic side d)
    (a b : Operand) : Call3Public where
  bytes := ⟨⟨p.layout.base, activeBytes, side.offset, outerWords, side.words p.layout⟩,
    p.layout.pointer b.pointer, p.exponentLen⟩
  minv := side.inverse p.layout
  modulus := side.value p.layout
  lower := (side.bounds p.layout).1
  fits := (side.bounds p.layout).2.1
  upper := by change outerWords < 2 ^ 30; decide
  greater := p.greater
  odd := p.odd
  base := p.layout.pointer a.pointer
  baseLen := p.baseLen
  width48 := (side.bounds p.layout).2.1
  basePositive := p.basePositive
  baseFits := p.baseFits
  expPositive := p.exponentPositive
  expLimit := p.exponentBound
  output := off p.layout.base d
  outputLen := side.length p.layout
  parentInverse := 0
  extent := by change pWorkspace ≤ activeBytes; decide
  childLow := (side.bounds p.layout).2.2.1
  childHigh := (side.bounds p.layout).2.2.2.2.1
  offsetBound := (side.bounds p.layout).2.2.2.1
  outputPositive := (side.bounds p.layout).2.2.2.2.2.1
  outputBound := (side.bounds p.layout).2.2.2.2.2.2
  outputWidth := rfl

def ReadyCallPre (side : ModulusSide) (d : Nat) (a b : Operand)
    (p : ReadyCallPublic side d) (s : State) : Prop := Ready p.layout s ∧
  ∃ ba bb : List Byte, OperandBytes s p.layout.base activeBytes a ba ∧
    OperandBytes s p.layout.base activeBytes b bb ∧ ba.length = p.baseLen ∧ bb.length = p.exponentLen

theorem readyCall_pre {side : ModulusSide} {d : Nat} {a b : Operand}
    {p : ReadyCallPublic side d} {s : State}
    (ha : stablePointer a.pointer) (hb : stablePointer b.pointer) (h : ReadyCallPre side d a b p s) :
    Call3Pre a b ⟨.local d, side.lengthField⟩ (p.call a b) s := by
  obtain ⟨hr, ba, bb, has, hbs, hbl, hel⟩ := h
  exact ⟨hr.parent, hr.child side, ⟨ba, bb, has, hbs, hbl, hel⟩,
    hr.publicPointer a.pointer ha, hr.publicPointer b.pointer hb, rfl, hr.length side,
    hr.local_write p.outputEnd, hr.local_out p.outputStart p.outputEnd⟩

theorem readyPow_ct (M : Mont) (Sq : MontS) (side : ModulusSide) (d : Nat) (a b : Operand)
    (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (hpa : stablePointer a.pointer) (hpb : stablePointer b.pointer)
    (hd : d < 2 ^ 31)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi])
      (.block (callHead a b ⟨.local d, side.lengthField⟩ side.offset)) hc).isSome = true) :
    RelCT isa (Two (ReadyCallPre side d a b))
      (Core.pow Sq.mm M.mm side.offset a b ⟨.local d, side.lengthField⟩) (fun _ _ => True) :=
  two_map (fun p : ReadyCallPublic side d => p.call a b)
    (fun _ _ h => ⟨readyCall_pre hpa hpb h, rfl⟩)
    (corePow_ct M Sq ha hb hd hT)

structure ReadyProductPublic (side : ModulusSide) (d : Nat) extends ReadyCallPublic side d where
  secondFits : (exponentLen + 7) / 8 ≤ side.words layout

def ReadyProductPublic.call {side : ModulusSide} {d : Nat} (p : ReadyProductPublic side d)
    (a b : Operand) : Call3ProductPublic :=
  { p.toReadyCallPublic.call a b with secondFits := p.secondFits }

theorem readyProduct_ct (M : Mont) (side : ModulusSide) (d : Nat) (a b : Operand)
    (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (hpa : stablePointer a.pointer) (hpb : stablePointer b.pointer)
    (hd : d < 2 ^ 31)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi])
      (.block (callHead a b ⟨.local d, side.lengthField⟩ side.offset)) hc).isSome = true) :
    RelCT isa (Two fun p : ReadyProductPublic side d => ReadyCallPre side d a b p.toReadyCallPublic)
      (Core.product M.mm side.offset a b ⟨.local d, side.lengthField⟩) (fun _ _ => True) :=
  two_map (fun p : ReadyProductPublic side d => p.call a b)
    (fun _ _ h => ⟨readyCall_pre hpa hpb h, rfl⟩)
    (coreProduct_ct M ha hb hd hT)

def ReadyAddPre (d : Nat) (a b : Operand) (p : ReadyProductPublic .q d) (s : State) : Prop :=
  ReadyCallPre .q d a b p.toReadyCallPublic s ∧
  Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (p.layout.pointer a.pointer) p.baseLen) < p.layout.subgroup ∧
  Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (p.layout.pointer b.pointer) p.exponentLen) < p.layout.subgroup

theorem readyAdd_ct (d : Nat) (a b : Operand)
    (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (hpa : stablePointer a.pointer) (hpb : stablePointer b.pointer)
    (hd : d < 2 ^ 31)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi])
      (.block (callHead a b (Core.scalar d) qWorkspace)) hc).isSome = true) :
    RelCT isa (Two (ReadyAddPre d a b)) (Core.add a b (Core.scalar d)) (fun _ _ => True) :=
  two_map (fun p : ReadyProductPublic .q d => p.call a b)
    (fun _ _ h => ⟨readyCall_pre hpa hpb h.1, rfl, h.2⟩)
    (coreAdd_ct ha hb hd hT)

end VG.Proof.Dsa.X86_64
