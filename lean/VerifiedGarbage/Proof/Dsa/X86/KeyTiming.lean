module

public import VerifiedGarbage.Impl.Dsa.X86.Validate
public import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.Proof.Dsa.X86.CallTiming
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Dsa.X86.Pointer
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
import VerifiedGarbage.Proof.Dsa.X86.PointerTiming
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Dsa.X86.StageMinus
public import VerifiedGarbage.Proof.Dsa.X86.StreamTiming
public import VerifiedGarbage.Proof.Dsa.X86.StageArithmetic
import VerifiedGarbage.Proof.Dsa.X86.CoreSetup
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Mont.X86.ContextFrame
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.TCB.X86.Isa
import VerifiedGarbage.TCB.X86.State
import VerifiedGarbage.Proof.Dsa.X86.Persistent
import VerifiedGarbage.Proof.Weierstrass.MontContract
public import VerifiedGarbage.Proof.Dsa.X86.CoreFrame
import VerifiedGarbage.Proof.Dsa.X86.ChecksTiming
import VerifiedGarbage.Proof.Dsa.X86.StageChecks
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Dsa.X86.StagePower
import VerifiedGarbage.Proof.Dsa.X86.PowJoint
import VerifiedGarbage.Proof.Dsa.X86.CorePowerLoad
public import VerifiedGarbage.Proof.Dsa.X86.StackFrame
import VerifiedGarbage.Proof.Dsa.X86.PowCallTiming
import VerifiedGarbage.Proof.Dsa.X86.PowCall
public import VerifiedGarbage.Impl.Dsa.X86.Core
import VerifiedGarbage.Proof.Dsa.X86.BytesTiming
import VerifiedGarbage.Proof.Mont.X86.PowerTiming

/-! ### `Dsa.X86.CallPowerTiming`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86.RawInputsTiming`, which this module and modules that import it used -/

section

/-! # Pairwise component loading for validation without a Montgomery context -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem rawInputs_relCT (n al bl i j : Nat) (a b : Pointer) (base : Addr) (size : Nat)
    (hz : Layout.saved ≤ size) (hn : n ≤ 48) (hi : i < 9) (ha4 : 4 ≤ al) (ha : al ≤ 8 * n) (hwa : al % 4 = 0) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧
      OperandReady s base n a al ∧ OperandReady t base n a al ∧
      pointerValue base s a = pointerValue base t a ∧ pointerValue base s b = pointerValue base t b)
      (.seq (Core.load n al (slot n i) a) (Core.load n bl (slot n j) b))
      (VG.X86.Taint.Agree (workspaceTaint true)) := by
  intro s t tr ur sf tf ⟨S, T, A₁, A₂, Pa, Pb⟩ E F
  have B := slot_bound (n := n) hi
  have C := VG.Proof.Dsa.X86.Layout.context_bound hn
  have H : 8256 ≤ size := hz
  have fit : slot n i + 8 * n ≤ size := by simp only [stride] at B; omega_using [B, C, H]
  cases E with
  | seq E₁ E₂ =>
    cases F with
    | seq F₁ F₂ =>
      obtain ⟨Trace₁, _⟩ := coreLoad_relCT n al (slot n i) a base size hz _ _ _ _ _ _ ⟨S, T, Pa⟩ E₁ F₁
      obtain ⟨_, K₁, O₁⟩ := wp_result (coreLoad_ok S hz fit ha4 ha hwa A₁.toReadableComponent (A₁.slot hi)) E₁
      obtain ⟨_, K₂, O₂⟩ := wp_result (coreLoad_ok T hz fit ha4 ha hwa A₂.toReadableComponent (A₂.slot hi)) F₁
      have Hn : contextBytes n ≤ 8192 := by omega_using [C]
      have P₁ := pointerValue_keep K₁ (by decide) (slotOutside_whole O₁ hi) Hn b
      have P₂ := pointerValue_keep K₂ (by decide) (slotOutside_whole O₂ hi) Hn b
      obtain ⟨Trace₂, Agree⟩ := coreLoad_relCT n bl (slot n j) b base size hz _ _ _ _ _ _
        ⟨S.of_keeps K₁ (by decide), T.of_keeps K₂ (by decide), P₁.trans (Pb.trans P₂.symm)⟩ E₂ F₂
      exact ⟨by rw [Trace₁, Trace₂], Agree⟩

end VG.Proof.Dsa.X86

end

end

/-! ### `Dsa.X86.CorePowerTiming`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86.CoreSetupTiming`, which this module and modules that import it used -/

section

/-! # Constant-time modulus loading and context initialization -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem contextSetup_relCT (n : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (contextSetup n)
      (VG.X86.Taint.Agree (workspaceTaint false)) :=
  checkedProgramChange (hint := contextSetupHint) (contextSetup_check n) rfl

theorem coreSetup_relCT (len : Nat) (modulus : Field) (base : Addr) (size : Nat) (hz : Layout.saved ≤ size) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧
      pointerValue base s (.input modulus) = pointerValue base t (.input modulus))
      (Core.setup len modulus) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold Core.setup
  refine RelCT.seq (coreLoad_relCT _ _ _ _ base size hz) ?_
  exact (contextSetup_relCT _).mono
    (fun _ _ h => taint.le_sound (show taint.le (workspaceTaint false) (workspaceTaint true) = true from rfl) h)
    (fun _ _ h => h)

end VG.Proof.Dsa.X86

end

end

/-! ### `Dsa.X86.CoreStoreTiming`, which this module and modules that import it used -/

section

/-! # Constant-time release of internal arithmetic results -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem coreStore_workspace_relCT (len output : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false))
      (Core.store len output) (VG.X86.Taint.Agree (workspaceTaint true)) := by
  unfold Core.store Core.pointer
  refine RelCT.seq (R := VG.X86.Taint.Agree (workspaceTaint true)) ?_
    (storeComponent_relCT len (slot ((len + 7) / 8) 6))
  apply checkedProgramChange (σ := workspaceTaint true) (τ' := { regs := .ofList [.edi, .esi, .ecx], flags := true })
    (hint := .block []) ?_ rfl
  change taint.checkBlock (workspaceTaint false)
    [.mov .esi (.reg .edi), .alu .add .esi (.imm (BitVec.ofNat 32 output)), .mov .ecx (.imm (BitVec.allOnes 32))] = _
  rw [← VG.X86.Taint.checkBlock_erase _ _ rfl]
  change taint.checkBlock (workspaceTaint false) [.mov .esi (.reg .edi), .alu .add .esi (.imm 0), .mov .ecx (.imm 0)] = _
  rfl

end VG.Proof.Dsa.X86

end

end

/-! ### `Dsa.X86.ArithmeticHeadTiming`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86.ArithmeticHead`, which this module and modules that import it used -/

section

/-! # Common context and operand preparation for powers, products, and sums -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

def arithmeticHead (len bl : Nat) (modulus : Field) (a b : Pointer) : Prog isa :=
  .seq (Core.setup len modulus)
    (.seq (Core.load ((len + 7) / 8) len (slot ((len + 7) / 8) 5) a)
      (Core.load ((len + 7) / 8) bl (slot ((len + 7) / 8) 8) b))

structure ArithmeticPre (base : Addr) (size len bl : Nat) (modulus : Field) (a b : Pointer) (s : State) : Prop where
  scr : Scr s base size
  modulusReady : OperandReady s base ((len + 7) / 8) (.input modulus) len
  leftReady : OperandReady s base ((len + 7) / 8) a len
  rightReady : OperandReady s base ((len + 7) / 8) b bl
  large : 1 < Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input modulus)).setWidth 64) len)
  odd : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input modulus)).setWidth 64) len) % 2 = 1

end VG.Proof.Dsa.X86

end

end

/-! # Constant-time preparation of a binary modular operation -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/CoreInputsTiming.lean`, which only this module imported.
section

/-! # Loading two arithmetic operands without revealing their values -/

section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem coreInputs_relCT (n al bl : Nat) (a b : Pointer) (base : Addr) (size : Nat)
    (hz : Layout.saved ≤ size) (hn : n ≤ 48) (ha4 : 4 ≤ al) (ha : al ≤ 8 * n) (hwa : al % 4 = 0) :
    RelCT isa (fun s t => ∃ m₁ m₂,
      Context n m₁ base size s ∧ Context n m₂ base size t ∧
      OperandReady s base n a al ∧ OperandReady t base n a al ∧
      pointerValue base s a = pointerValue base t a ∧ pointerValue base s b = pointerValue base t b)
      (.seq (Core.load n al (slot n 5) a) (Core.load n bl (slot n 8) b))
      (VG.X86.Taint.Agree (workspaceTaint true)) := by
  intro s t tr ur sf tf ⟨m₁, m₂, C₁, C₂, A₁, A₂, Pa, Pb⟩ E F
  cases E with
  | seq E₁ E₂ =>
    cases F with
    | seq F₁ F₂ =>
      obtain ⟨Trace₁, _⟩ := coreLoad_relCT n al (slot n 5) a base size hz _ _ _ _ _ _ ⟨C₁.scr, C₂.scr, Pa⟩ E₁ F₁
      obtain ⟨D₁, _, K₁, O₁⟩ := wp_result (coreLoadSlot_ok C₁ hz (by decide) (by decide) ha4 ha hwa
        A₁.toReadableComponent (A₁.slot (by decide))) E₁
      obtain ⟨D₂, _, K₂, O₂⟩ := wp_result (coreLoadSlot_ok C₂ hz (by decide) (by decide) ha4 ha hwa
        A₂.toReadableComponent (A₂.slot (by decide))) F₁
      have Hn : contextBytes n ≤ 8192 := Nat.le_trans (VG.Proof.Dsa.X86.Layout.context_bound hn) (by decide)
      have P₁ := pointerValue_keep K₁ (by decide) (slotOutside_whole O₁ (by decide)) Hn b
      have P₂ := pointerValue_keep K₂ (by decide) (slotOutside_whole O₂ (by decide)) Hn b
      obtain ⟨Trace₂, Agree⟩ := coreLoad_relCT n bl (slot n 8) b base size hz _ _ _ _ _ _
        ⟨D₁.scr, D₂.scr, P₁.trans (Pb.trans P₂.symm)⟩ E₂ F₂
      exact ⟨by rw [Trace₁, Trace₂], Agree⟩

end VG.Proof.Dsa.X86
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

def ArithmeticAgree (base : Addr) (size len bl : Nat) (modulus : Field) (a b : Pointer) (s t : State) : Prop :=
  ArithmeticPre base size len bl modulus a b s ∧ ArithmeticPre base size len bl modulus a b t ∧
  pointerValue base s (.input modulus) = pointerValue base t (.input modulus) ∧
  pointerValue base s a = pointerValue base t a ∧ pointerValue base s b = pointerValue base t b

theorem arithmeticHead_relCT (base : Addr) (size len bl : Nat) (modulus : Field) (a b : Pointer)
    (hz : Layout.saved ≤ size) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0) :
    RelCT isa (ArithmeticAgree base size len bl modulus a b) (arithmeticHead len bl modulus a b)
      (VG.X86.Taint.Agree (workspaceTaint true)) := by
  intro s t tr ur sf tf ⟨P, Q, Mod, Left, Right⟩ E F
  have hn : (len + 7) / 8 ≤ 48 := by omega_using [hmax]
  have Hn : contextBytes ((len + 7) / 8) ≤ 8192 :=
    Nat.le_trans (VG.Proof.Dsa.X86.Layout.context_bound hn) (by decide)
  cases E with
  | seq E₀ E₁ =>
    cases F with
    | seq F₀ F₁ =>
      obtain ⟨Trace₀, _⟩ := coreSetup_relCT len modulus base size hz _ _ _ _ _ _ ⟨P.scr, Q.scr, Mod⟩ E₀ F₀
      obtain ⟨C₁, _, _, O₁, K₁⟩ := wp_result (coreSetup_ok P.scr hz rfl h4 hmax hw4
        P.modulusReady.toReadableComponent (P.modulusReady.slot (by decide)) rfl P.large P.odd) E₀
      obtain ⟨C₂, _, _, O₂, K₂⟩ := wp_result (coreSetup_ok Q.scr hz rfl h4 hmax hw4
        Q.modulusReady.toReadableComponent (Q.modulusReady.slot (by decide)) rfl Q.large Q.odd) F₀
      have A₁ := P.leftReady.keep K₁ (by decide) O₁ hn
      have A₂ := Q.leftReady.keep K₂ (by decide) O₂ hn
      have PL := (pointerValue_keep K₁ (by decide) O₁ Hn a).trans
        (Left.trans (pointerValue_keep K₂ (by decide) O₂ Hn a).symm)
      have PR := (pointerValue_keep K₁ (by decide) O₁ Hn b).trans
        (Right.trans (pointerValue_keep K₂ (by decide) O₂ Hn b).symm)
      obtain ⟨Trace₁, Agree⟩ := coreInputs_relCT ((len + 7) / 8) len bl a b base size hz hn h4 (by omega_using []) hw4
        _ _ _ _ _ _ ⟨_, _, C₁, C₂, A₁, A₂, PL, PR⟩ E₁ F₁
      exact ⟨by rw [Trace₀, Trace₁], Agree⟩

end VG.Proof.Dsa.X86

end

end

/-! # Constant-time modular exponentiation through the shared helper -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/PowerHead.lean`, which only this module imported.
section

/-! # Loading shared exponentiation's operands without duplicating setup -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

def powerHead (len bl : Nat) (modulus : Field) (a b : Pointer) : Prog isa :=
  .seq (Core.load ((len + 7) / 8) len (slot ((len + 7) / 8) 0) (.input modulus))
    (.seq (Core.load ((len + 7) / 8) len (slot ((len + 7) / 8) 5) a)
      (Core.load ((len + 7) / 8) bl (slot ((len + 7) / 8) 8) b))

structure PowerReady (base : Addr) (size n : Nat) (s : State) : Prop where
  scr : Scr s base size
  room : Pow.Room (s.gpr .esp) base size
  large : 1 < wordsVal s.mem base (slot n 0) n
  odd : wordsVal s.mem base (slot n 0) n % 2 = 1

theorem powerHead_ok {base : Addr} {size len bl : Nat} {modulus : Field} {a b : Pointer} {s : State}
    (P : ArithmeticPre base size len bl modulus a b s) (room : Pow.Room (s.gpr .esp) base size)
    (hz : Layout.saved ≤ size) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hb4 : 4 ≤ bl) (hb : bl ≤ len)
    (hw4 : len % 4 = 0) (hwb : bl % 4 = 0) :
    WP isa (powerHead len bl modulus a b) s fun t =>
      PowerReady base size ((len + 7) / 8) t ∧ Keeps loadClob s t := by
  let n := (len + 7) / 8
  have hn : n ≤ 48 := by dsimp only [n]; omega_using [hmax]
  have cb := VG.Proof.Dsa.X86.Layout.context_bound hn
  have sz : 8256 ≤ size := hz
  have nw := P.scr.nowrap
  have bounds (j : Nat) (hj : j < 9) : slot n j + 8 * n ≤ size := by
    have H := slot_bound (n := n) hj
    simp only [stride] at H
    omega_using [cb, sz, H]
  unfold powerHead
  refine WP.seq (WP.mono (coreLoad_ok P.scr hz (bounds 0 (by decide)) h4 (by omega_using []) hw4
    P.modulusReady.toReadableComponent (P.modulusReady.slot (by decide))) fun u ⟨M, K, O⟩ => ?_)
  have O' := slotOutside_whole O (by decide)
  have A := P.leftReady.keep K (by decide) O' hn
  have B := P.rightReady.keep K (by decide) O' hn
  refine WP.seq (WP.mono (coreLoad_ok (P.scr.of_keeps K (by decide)) hz (bounds 5 (by decide)) h4
    (by omega_using []) hw4 A.toReadableComponent (A.slot (by decide))) fun v ⟨_, L, F⟩ => ?_)
  have B' := B.keep L (by decide) (slotOutside_whole F (by decide)) hn
  refine WP.mono (coreLoad_ok (P.scr.of_keeps (K.trans L) (by decide)) hz (bounds 8 (by decide)) hb4
    (by omega_using [hb]) hwb B'.toReadableComponent (B'.slot (by decide))) fun t ⟨_, N, G⟩ => ?_
  have allK := (K.trans L).trans N
  have mod : wordsVal t.mem base (slot n 0) n =
      Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input modulus)).setWidth 64) len) := by
    rw [slotOutside_val G (by decide) (by have H := bounds 0 (by decide); dsimp only [n] at H; omega_using [nw, H]),
      slotOutside_val F (by decide) (by have H := bounds 0 (by decide); dsimp only [n] at H; omega_using [nw, H]), M]
  exact ⟨⟨P.scr.of_keeps allK (by decide), by rw [allK.1 _ (by decide)]; exact room,
    mod ▸ P.large, mod ▸ P.odd⟩, allK⟩

end VG.Proof.Dsa.X86
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem powerHead_relCT (base : Addr) (size len bl : Nat) (modulus : Field) (a b : Pointer)
    (hz : Layout.saved ≤ size) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0) :
    RelCT isa (ArithmeticAgree base size len bl modulus a b) (powerHead len bl modulus a b)
      (VG.X86.Taint.Agree (workspaceTaint true)) := by
  intro s t tr ur sf tf ⟨P, Q, Mod, Left, Right⟩ E F
  have hn : (len + 7) / 8 ≤ 48 := by omega_using [hmax]
  have Hn := VG.Proof.Dsa.X86.Layout.context_bound hn
  have B := slot_bound (n := (len + 7) / 8) (i := 0) (by decide)
  have H : 8256 ≤ size := hz
  have fit : slot ((len + 7) / 8) 0 + 8 * ((len + 7) / 8) ≤ size := by
    simp only [stride] at B; omega_using [Hn, B, H]
  cases E with
  | seq E₀ E₁ => cases F with
    | seq F₀ F₁ =>
      have Trace₀ := (coreLoad_relCT _ len _ (.input modulus) base size hz
        _ _ _ _ _ _ ⟨P.scr, Q.scr, Mod⟩ E₀ F₀).1
      obtain ⟨_, K₁, O₁⟩ := wp_result (coreLoad_ok P.scr hz fit h4 (by omega_using []) hw4
        P.modulusReady.toReadableComponent (P.modulusReady.slot (by decide))) E₀
      obtain ⟨_, K₂, O₂⟩ := wp_result (coreLoad_ok Q.scr hz fit h4 (by omega_using []) hw4
        Q.modulusReady.toReadableComponent (Q.modulusReady.slot (by decide))) F₀
      have W₁ := slotOutside_whole O₁ (by decide)
      have W₂ := slotOutside_whole O₂ (by decide)
      have A₁ := P.leftReady.keep K₁ (by decide) W₁ hn
      have A₂ := Q.leftReady.keep K₂ (by decide) W₂ hn
      have PL := (pointerValue_keep K₁ (by decide) W₁ (by omega_using [Hn]) a).trans
        (Left.trans (pointerValue_keep K₂ (by decide) W₂ (by omega_using [Hn]) a).symm)
      have PR := (pointerValue_keep K₁ (by decide) W₁ (by omega_using [Hn]) b).trans
        (Right.trans (pointerValue_keep K₂ (by decide) W₂ (by omega_using [Hn]) b).symm)
      obtain ⟨Trace₁, Agree⟩ := rawInputs_relCT _ len bl 5 8 a b base size hz hn (by decide)
        h4 (by omega_using []) hw4 _ _ _ _ _ _ ⟨P.scr.of_keeps K₁ (by decide), Q.scr.of_keeps K₂ (by decide), A₁, A₂, PL, PR⟩ E₁ F₁
      exact ⟨by rw [Trace₀, Trace₁], Agree⟩

def PowerPair (base : Addr) (size n : Nat) (s t : State) : Prop :=
  PowerReady base size n s ∧ PowerReady base size n t ∧ s.gpr .esp = t.gpr .esp

theorem powerTail_relCT (base : Addr) (size n len e output : Nat)
    (hz : contextBytes n ≤ size) (hu : usedBytes ≤ size)
    (hn : 2 ≤ n) (hn48 : n ≤ 48) (he : 1 < e) (hen : e ≤ 2 * n) :
    RelCT isa (PowerPair base size n) (.seq (Pow.call n e) (Core.store len output))
      (VG.X86.Taint.Agree (workspaceTaint true)) := by
  refine RelCT.seq ?_ (coreStore_workspace_relCT len output)
  intro s t tr ur sf tf ⟨S, T, SP⟩ E F
  have DI : s.gpr .edi = t.gpr .edi := BitVec.eq_of_toNat_eq (S.scr.edi_toNat.trans T.scr.edi_toNat.symm)
  have CT := (Pow.call_relCT n e hn hn48 he hen) _ _ _ _ _ _
    ⟨SP, DI, ⟨base, size, S.scr, S.room, hz, S.large, S.odd⟩, ⟨base, size, T.scr, T.room, hz, T.large, T.odd⟩⟩ E F
  obtain ⟨_, _, K⟩ := wp_result (Pow.call_ok S.scr S.room hz hu hn hn48 he hen rfl S.large S.odd) E
  obtain ⟨_, _, L⟩ := wp_result (Pow.call_ok T.scr T.room hz hu hn hn48 he hen rfl T.large T.odd) F
  refine ⟨CT.1, agree_regs (rs := [.edi]) ?_⟩
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  rw [K.1 .edi (by decide), L.1 .edi (by decide), DI]

def PowerAgree (base : Addr) (size len bl : Nat) (modulus : Field) (a b : Pointer) (s t : State) : Prop :=
  ArithmeticAgree base size len bl modulus a b s t ∧ Pow.Room (s.gpr .esp) base size ∧
    Pow.Room (t.gpr .esp) base size ∧ s.gpr .esp = t.gpr .esp

theorem corePower_relCT (base : Addr) (size len expLen output : Nat) (modulus : Field) (a b : Pointer)
    (hz : Layout.saved ≤ size) (hu : usedBytes ≤ size) (h4 : 16 ≤ len) (hmax : len ≤ 384)
    (hw4 : len % 4 = 0) (he : 8 ≤ expLen) (hel : expLen ≤ len) (hew : expLen % 4 = 0) :
    RelCT isa (PowerAgree base size len expLen modulus a b)
      (Core.power len expLen modulus a b output) (VG.X86.Taint.Agree (workspaceTaint true)) := by
  have hn : (len + 7) / 8 ≤ 48 := by omega_using [hmax]
  have cb := VG.Proof.Dsa.X86.Layout.context_bound hn
  have sz : 8256 ≤ size := hz
  unfold Core.power
  dsimp only
  apply RelCT.assoc
  refine RelCT.seq ?_ (powerTail_relCT base size _ len _ output (by omega_using [cb, sz]) hu (by omega_using [h4]) hn (by omega_using [he]) (by omega_using [hel]))
  have H := (powerHead_relCT base size len expLen modulus a b hz (by omega_using [h4]) hmax hw4).mono
    (fun _ _ (P : PowerAgree base size len expLen modulus a b _ _) => P.1) (fun _ _ A => A)
  refine (H.wpDep (F := fun s t => PowerReady base size ((len + 7) / 8) t ∧ Keeps loadClob s t)
    (fun s t P => ⟨powerHead_ok P.1.1 P.2.1 hz (by omega_using [h4]) hmax (by omega_using [he]) hel hw4 hew,
      powerHead_ok P.1.2.1 P.2.2.1 hz (by omega_using [h4]) hmax (by omega_using [he]) hel hw4 hew⟩)).mono (fun _ _ P => P) ?_
  rintro s t ⟨_, a, b, P, ⟨S, K⟩, ⟨T, L⟩⟩
  exact ⟨S, T, (K.1 .esp (by decide)).trans (P.2.2.2.trans (L.1 .esp (by decide)).symm)⟩

/-- What two runs of the product of two powers share: `PowerAgree`, and the
second base and exponent at the same addresses. -/
def Power2Agree (base : Addr) (size len bl : Nat) (modulus : Field) (a b a2 b2 : Pointer) (s t : State) : Prop :=
  PowerAgree base size len bl modulus a b s t ∧
  OperandReady s base ((len + 7) / 8) a2 len ∧ OperandReady t base ((len + 7) / 8) a2 len ∧
  OperandReady s base ((len + 7) / 8) b2 bl ∧ OperandReady t base ((len + 7) / 8) b2 bl ∧
  pointerValue base s a2 = pointerValue base t a2 ∧ pointerValue base s b2 = pointerValue base t b2

theorem power2Head_ok {base : Addr} {size len bl : Nat} {modulus : Field} {a b a2 b2 : Pointer} {s : State}
    (P : ArithmeticPre base size len bl modulus a b s) (room : Pow.Room (s.gpr .esp) base size)
    (A2 : OperandReady s base ((len + 7) / 8) a2 len) (B2 : OperandReady s base ((len + 7) / 8) b2 bl)
    (hz : Layout.saved ≤ size) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hb4 : 8 ≤ bl) (hb : bl ≤ len)
    (hw4 : len % 4 = 0) (hwb : bl % 4 = 0) :
    WP isa (Core.loadPower2 ((len + 7) / 8) len bl modulus a b a2 b2) s fun t =>
      PowerReady base size ((len + 7) / 8) t ∧ Keeps loadClob s t := by
  have hn : (len + 7) / 8 ≤ 48 := by omega_using [hmax]
  have cb := VG.Proof.Dsa.X86.Layout.context_bound hn
  have sz : 8256 ≤ size := hz
  refine WP.mono (coreLoadPower2_ok P.scr hz rfl h4 hmax hw4 hb4 hb hwb P.modulusReady P.leftReady P.rightReady
    A2 B2 rfl (by omega_using [cb, sz])) fun t ⟨M, _, _, _, _, _, K⟩ => ?_
  exact ⟨⟨P.scr.of_keeps K (by decide), by rw [K.1 _ (by decide)]; exact room, M ▸ P.large, M ▸ P.odd⟩, K⟩

/-- The staging of the product of two powers: the same trace from the same addresses. -/
theorem power2Head_relCT (base : Addr) (size len bl : Nat) (modulus : Field) (a b a2 b2 : Pointer)
    (hz : Layout.saved ≤ size) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0)
    (hb4 : 8 ≤ bl) (hb : bl ≤ len) (hwb : bl % 4 = 0) :
    RelCT isa (Power2Agree base size len bl modulus a b a2 b2)
      (Core.loadPower2 ((len + 7) / 8) len bl modulus a b a2 b2) (fun _ _ => True) := by
  intro s t tr ur sf tf ⟨⟨⟨P, Q, Mod, Left, Right⟩, _, _, _⟩, A2s, A2t, B2s, B2t, PA2, PB2⟩ E F
  have hn : (len + 7) / 8 ≤ 48 := by omega_using [hmax]
  have Hn := VG.Proof.Dsa.X86.Layout.context_bound hn
  have H8 : contextBytes ((len + 7) / 8) ≤ 8192 := Nat.le_trans Hn (by decide)
  have H : 8256 ≤ size := hz
  have B7 := slot_bound (n := (len + 7) / 8) (i := 7) (by decide)
  have fit7 : slot ((len + 7) / 8) 7 + 8 * ((len + 7) / 8) ≤ size := by
    simp only [stride] at B7; omega_using [Hn, B7, H]
  cases E with
  | seq E₀ E₁ => cases F with
    | seq F₀ F₁ =>
      have T₀ := (powerHead_relCT base size len bl modulus a b hz h4 hmax hw4 _ _ _ _ _ _
        ⟨P, Q, Mod, Left, Right⟩ E₀ F₀).1
      obtain ⟨_, _, _, O₁, K₁⟩ := wp_result (coreLoadPower_ok P.scr hz rfl h4 hmax hw4 hb4 hb hwb P.modulusReady
        P.leftReady P.rightReady rfl (by omega_using [Hn, H])) E₀
      obtain ⟨_, _, _, O₂, K₂⟩ := wp_result (coreLoadPower_ok Q.scr hz rfl h4 hmax hw4 hb4 hb hwb Q.modulusReady
        Q.leftReady Q.rightReady rfl (by omega_using [Hn, H])) F₀
      have S₁ := P.scr.of_keeps K₁ (by decide)
      have S₂ := Q.scr.of_keeps K₂ (by decide)
      have A₁ := A2s.keep K₁ (by decide) O₁ hn
      have A₂ := A2t.keep K₂ (by decide) O₂ hn
      have PA := (pointerValue_keep K₁ (by decide) O₁ H8 a2).trans
        (PA2.trans (pointerValue_keep K₂ (by decide) O₂ H8 a2).symm)
      have PB := (pointerValue_keep K₁ (by decide) O₁ H8 b2).trans
        (PB2.trans (pointerValue_keep K₂ (by decide) O₂ H8 b2).symm)
      cases E₁ with
      | seq E₁ E₂ => cases F₁ with
        | seq F₁ F₂ =>
          have T₁ := (coreLoad_relCT _ len _ a2 base size hz _ _ _ _ _ _ ⟨S₁, S₂, PA⟩ E₁ F₁).1
          obtain ⟨_, K₁', O₁'⟩ := wp_result (coreLoad_ok S₁ hz fit7 h4 (by omega_using []) hw4
            A₁.toReadableComponent (A₁.slot (by decide))) E₁
          obtain ⟨_, K₂', O₂'⟩ := wp_result (coreLoad_ok S₂ hz fit7 h4 (by omega_using []) hw4
            A₂.toReadableComponent (A₂.slot (by decide))) F₁
          have W₁ := slotOutside_whole O₁' (by decide)
          have W₂ := slotOutside_whole O₂' (by decide)
          have PB' := (pointerValue_keep K₁' (by decide) W₁ H8 b2).trans
            (PB.trans (pointerValue_keep K₂' (by decide) W₂ H8 b2).symm)
          have T₂ := (coreLoad_relCT _ bl _ b2 base size hz _ _ _ _ _ _
            ⟨S₁.of_keeps K₁' (by decide), S₂.of_keeps K₂' (by decide), PB'⟩ E₂ F₂).1
          exact ⟨by rw [T₀, T₁, T₂], trivial⟩

/-- The product of two powers and the store of its result. -/
theorem power2Tail_relCT (base : Addr) (size n len e output : Nat)
    (hz : contextBytes n ≤ size) (hn : 6 ≤ n) (hn48 : n ≤ 48) (he : 0 < e) (hen : e ≤ 2 * n) :
    RelCT isa (PowerPair base size n) (.seq (Pow.core2 n e) (Core.store len output))
      (VG.X86.Taint.Agree (workspaceTaint true)) := by
  refine RelCT.seq ?_ (coreStore_workspace_relCT len output)
  intro s t tr ur sf tf ⟨S, T, SP⟩ E F
  have DI : s.gpr .edi = t.gpr .edi := BitVec.eq_of_toNat_eq (S.scr.edi_toNat.trans T.scr.edi_toNat.symm)
  have RS := S.room.callRoom S.scr.nowrap
  have RT := T.room.callRoom T.scr.nowrap
  have CT := (Pow.core2_relCT (base := base) (sp := s.gpr .esp) hn hn48 he hen) _ _ _ _ _ _
    ⟨⟨size, _, S.scr, RS, rfl, hz, rfl, S.large, S.odd⟩, ⟨size, _, T.scr, SP ▸ RT, SP.symm, hz, rfl, T.large, T.odd⟩⟩ E F
  obtain ⟨_, _, K⟩ := wp_result (Pow.core2_ok S.scr RS hz hn hn48 he hen rfl S.large S.odd) E
  obtain ⟨_, _, L⟩ := wp_result (Pow.core2_ok T.scr RT hz hn hn48 he hen rfl T.large T.odd) F
  refine ⟨CT.1, agree_regs (rs := [.edi]) ?_⟩
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  rw [K.1 .edi (by decide), L.1 .edi (by decide), DI]

theorem corePower2_relCT (base : Addr) (size len expLen output : Nat) (modulus : Field) (a b a2 b2 : Pointer)
    (hz : Layout.saved ≤ size) (h4 : 48 ≤ len) (hmax : len ≤ 384)
    (hw4 : len % 4 = 0) (he : 8 ≤ expLen) (hel : expLen ≤ len) (hew : expLen % 4 = 0) :
    RelCT isa (Power2Agree base size len expLen modulus a b a2 b2)
      (Core.power2 len expLen modulus a b a2 b2 output) (VG.X86.Taint.Agree (workspaceTaint true)) := by
  have hn : (len + 7) / 8 ≤ 48 := by omega_using [hmax]
  have cb := VG.Proof.Dsa.X86.Layout.context_bound hn
  have sz : 8256 ≤ size := hz
  unfold Core.power2
  dsimp only
  refine RelCT.seq ?_ (power2Tail_relCT base size _ len _ output (by omega_using [cb, sz]) (by omega_using [h4]) hn
    (by omega_using [he]) (by omega_using [hel]))
  have H := power2Head_relCT base size len expLen modulus a b a2 b2 hz (by omega_using [h4]) hmax hw4 he hel hew
  refine (H.wpDep (F := fun s t => PowerReady base size ((len + 7) / 8) t ∧ Keeps loadClob s t)
    (fun s t P => ⟨power2Head_ok P.1.1.1 P.1.2.1 P.2.1 P.2.2.2.1 hz (by omega_using [h4]) hmax he hel hw4 hew,
      power2Head_ok P.1.1.2.1 P.1.2.2.1 P.2.2.1 P.2.2.2.2.1 hz (by omega_using [h4]) hmax he hel hw4 hew⟩)).mono
    (fun _ _ P => P) ?_
  rintro s t ⟨_, a, b, P, ⟨S, K⟩, ⟨T, L⟩⟩
  exact ⟨S, T, (K.1 .esp (by decide)).trans (P.1.2.2.2.trans (L.1 .esp (by decide)).symm)⟩

end VG.Proof.Dsa.X86

end

end

/-! # Exponentiation stages preserve a public call layout -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem CallReady.arithmeticP {L : CallLayout} {s : State} {a b : Pointer} {bl : Nat}
    (R : CallReady L s) (A : CallOperand L a L.pLen) (B : CallOperand L b bl) (hb : 0 < bl) :
    ArithmeticPre L.base L.size L.pLen bl .p a b s := by
  have W := L.lengths
  refine ⟨R.moduli.scr, R.moduli.pReady, R.operand A (by omega_using [W]) (by omega_using [W]), R.operand B hb (by omega_using [W]), ?_, ?_⟩
  · change 1 < operandValue s L.base (.input .p) L.pLen
    rw [R.moduli.pValue]; exact R.moduli.pLarge
  · change operandValue s L.base (.input .p) L.pLen % 2 = 1
    rw [R.moduli.pValue]; exact R.moduli.pOdd

theorem CallReady.arithmeticQ {L : CallLayout} {s : State} {a b : Pointer}
    (R : CallReady L s) (A : CallOperand L a L.qLen) (B : CallOperand L b L.qLen) :
    ArithmeticPre L.base L.size L.qLen L.qLen .q a b s := by
  have W := L.lengths
  refine ⟨R.moduli.scr, R.moduli.qReady, R.operand A (by omega_using [W]) (by omega_using [W]), R.operand B (by omega_using [W]) (by omega_using [W]), ?_, ?_⟩
  · change 1 < operandValue s L.base (.input .q) L.qLen
    rw [R.moduli.qValue]; have := R.moduli.qLarge; omega_using [this]
  · change operandValue s L.base (.input .q) L.qLen % 2 = 1
    rw [R.moduli.qValue]; exact R.moduli.qOdd

theorem callPowerP_relCT (L : CallLayout) (a b : Pointer) (output : Nat)
    (P : CallOperand L (.input .p) L.pLen) (A : CallOperand L a L.pLen) (B : CallOperand L b L.qLen)
    (ho : r ≤ output) (hb : output + L.pLen ≤ usedBytes) :
    RelCT isa (CallPair L) (Core.power L.pLen L.qLen .p a b output) (CallPair L) := by
  have W := L.lengths
  refine call_stage (Q := VG.X86.Taint.Agree (workspaceTaint true)) ?_ ?_
  · apply (corePower_relCT L.base L.size L.pLen L.qLen output .p a b L.saved L.extent
    (by omega_using [W]) (by omega_using [W]) L.aligned.1 (by omega_using [W]) (by omega_using [W]) L.aligned.2).mono ?_ (fun _ _ h => h)
    intro s t H
    exact ⟨⟨H.1.arithmeticP A B (by omega_using [W]), H.2.arithmeticP A B (by omega_using [W]), H.pointer P, H.pointer A, H.pointer B⟩,
      H.1.moduli.room, H.2.moduli.room, H.1.sp.trans H.2.sp.symm⟩
  · intro s R
    exact WP.mono (stagePowerP_ok R.moduli (R.operand A (by omega_using [W]) (by omega_using [W]))
      (R.operand B (by omega_using [W]) (by omega_using [W])) ho hb) fun _ H => H.2.toStageFrame.execution (.inl ⟨ho, hb⟩)

theorem callPowerQ_relCT (L : CallLayout) (a b : Pointer) (output : Nat)
    (Q : CallOperand L (.input .q) L.qLen) (A : CallOperand L a L.qLen) (B : CallOperand L b L.qLen)
    (ho : r ≤ output) (hb : output + L.qLen ≤ usedBytes) :
    RelCT isa (CallPair L) (Core.power L.qLen L.qLen .q a b output) (CallPair L) := by
  have W := L.lengths
  refine call_stage (Q := VG.X86.Taint.Agree (workspaceTaint true)) ?_ ?_
  · apply (corePower_relCT L.base L.size L.qLen L.qLen output .q a b L.saved L.extent
    (by omega_using [W]) (by omega_using [W]) L.aligned.2 (by omega_using [W]) (by omega_using []) L.aligned.2).mono ?_ (fun _ _ h => h)
    intro s t H
    exact ⟨⟨H.1.arithmeticQ A B, H.2.arithmeticQ A B, H.pointer Q, H.pointer A, H.pointer B⟩,
      H.1.moduli.room, H.2.moduli.room, H.1.sp.trans H.2.sp.symm⟩
  · intro s R
    exact WP.mono (stagePowerQ_ok R.moduli (R.operand A (by omega_using [W]) (by omega_using [W]))
      (R.operand B (by omega_using [W]) (by omega_using [W])) ho hb) fun _ H => H.2.toStageFrame.execution (.inl ⟨ho, hb⟩)

end VG.Proof.Dsa.X86

end

end

/-! ### `Dsa.X86.CallValidationTiming`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86.ValidationBlocksTiming`, which this module and modules that import it used -/

section

/-! # Constant-time validation masks and fixed constants -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86 VG.Proof.Mont.X86.Dynamic

theorem setConst_relCT (k out value : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (setConstW k out value)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold setConstW
  refine RelCT.seq (erased_relCT (σ := workspaceTaint false) _ (zerosW 0 1)
    (VG.Taint.hintOf taint (workspaceTaint false) (Code.erase (zerosW 0 1))) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)) ?_
  apply blockFlatMap_relCT
  intro j
  split
  · exact RelCT.block_nil (fun _ _ h => h)
  · apply checkedBlockInvariant (τ' := zeroTaint false) ?_ rfl
    rw [← VG.X86.Taint.checkBlock_erase _ _ rfl]
    change taint.checkBlock (workspaceTaint false) [.mov .eax (.imm 0), .store (sc 0) .eax] = _
    rfl

theorem lessThanConstant_relCT (n a tmp value : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (lessThanConstant n a tmp value)
      (VG.X86.Taint.Agree (workspaceTaint false)) :=
  RelCT.seq (setConst_relCT _ tmp value) (lessThan_relCT false n a tmp)

theorem lowerTwo_relCT (n : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (Validate.lowerTwo n)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold Validate.lowerTwo
  refine RelCT.seq (lessThanConstant_relCT n (slot n 5) (slot n 7) 2) ?_
  exact erased_relCT _ (.block ([.alu .xor .eax (.imm (BitVec.allOnes 32)), .mov .edx (.reg .eax)] ++ andFlag 0))
    (.block []) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)

theorem rangeMask_relCT (n : Nat) (aboveOne : Bool) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false))
      (.seq (checkRange n (slot n 5) (slot n 0) (Layout.field .mask))
        (if aboveOne then Validate.lowerTwo n else .block [])) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  apply RelCT.seq (checkRange_relCT false _ _ _ _)
  cases aboveOne
  · exact RelCT.block_nil (fun _ _ h => h)
  · exact lowerTwo_relCT n

theorem equalMask_relCT (n a b : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false))
      (.seq (equal n a b) (.block Validate.accumulate)) (VG.X86.Taint.Agree (workspaceTaint false)) :=
  RelCT.seq (equal_relCT false n a b) (checkedBlockInvariant (andFlag_check false _) rfl)

theorem modulusMinus_relCT (n amount : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (modulusMinus n amount)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold modulusMinus
  refine RelCT.seq (setConst_relCT _ _ _) ?_
  exact erased_relCT _ (chainW .sbb 1 0 0 0)
    (VG.Taint.hintOf taint (workspaceTaint false) (Code.erase (chainW .sbb 1 0 0 0))) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)

end VG.Proof.Dsa.X86

end

end

/-! ### `Dsa.X86.ValidationTiming`, which only this module used -/

section

/-! # Component validation does not branch or address memory on secret values -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem forget_counter {s t : State} (H : VG.X86.Taint.Agree (workspaceTaint true) s t) :
    VG.X86.Taint.Agree (workspaceTaint false) s t := taint.le_sound (by rfl) H

theorem validateRange_relCT (len : Nat) (modulus : Field) (input : Pointer) (aboveOne : Bool)
    (base : Addr) (size : Nat) (hz : Layout.saved ≤ size) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧
      OperandReady s base ((len + 7) / 8) (.input modulus) len ∧
      OperandReady t base ((len + 7) / 8) (.input modulus) len ∧
      pointerValue base s (.input modulus) = pointerValue base t (.input modulus) ∧
      pointerValue base s input = pointerValue base t input)
      (Validate.range len modulus input aboveOne) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold Validate.range
  dsimp only
  apply RelCT.assoc
  apply RelCT.seq (rawInputs_relCT _ len len 0 5 (.input modulus) input base size hz (by omega_using [hmax]) (by decide) h4
    (by omega_using []) hw4)
  exact (rangeMask_relCT _ aboveOne).mono (fun _ _ h => forget_counter h) (fun _ _ h => h)

theorem validateEqual_relCT (len : Nat) (a b : Pointer) (base : Addr) (size : Nat)
    (hz : Layout.saved ≤ size) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧
      OperandReady s base ((len + 7) / 8) a len ∧ OperandReady t base ((len + 7) / 8) a len ∧
      pointerValue base s a = pointerValue base t a ∧ pointerValue base s b = pointerValue base t b)
      (Validate.equalValues len a b) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold Validate.equalValues
  dsimp only
  apply RelCT.assoc
  apply RelCT.seq (rawInputs_relCT _ len len 5 8 a b base size hz (by omega_using [hmax]) (by decide) h4 (by omega_using []) hw4)
  exact (equalMask_relCT _ _ _).mono (fun _ _ h => forget_counter h) (fun _ _ h => h)

theorem validateOne_relCT (len : Nat) (input : Pointer) (base : Addr) (size : Nat) (hz : Layout.saved ≤ size) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧ pointerValue base s input = pointerValue base t input)
      (Validate.isOne len input) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold Validate.isOne
  dsimp only
  apply RelCT.seq (coreLoad_relCT _ len _ input base size hz)
  have Tail := RelCT.seq (setConst_relCT (2 * ((len + 7) / 8)) (slot ((len + 7) / 8) 8) 1)
    (equalMask_relCT ((len + 7) / 8) (slot ((len + 7) / 8) 5) (slot ((len + 7) / 8) 8))
  exact Tail.mono (fun _ _ h => forget_counter h) (fun _ _ h => h)

theorem validateZero_relCT (len : Nat) (input : Pointer) (wantNonzero : Bool) (base : Addr) (size : Nat) (hz : Layout.saved ≤ size) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧ pointerValue base s input = pointerValue base t input)
      (Validate.zero len input wantNonzero) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold Validate.zero
  dsimp only
  apply RelCT.seq (coreLoad_relCT _ len _ input base size hz)
  exact (checkZero_relCT true _ _ _ wantNonzero).mono (fun _ _ h => h) (fun _ _ h => forget_counter h)

end VG.Proof.Dsa.X86

end

end


/-! # Validation stages retain the public call layout -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem callRange_relCT (L : CallLayout) (len : Nat) (modulus : Field) (input : Pointer) (aboveOne : Bool)
    (M : CallOperand L (.input modulus) len) (I : CallOperand L input len) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0) :
    RelCT isa (CallPair L) (Validate.range len modulus input aboveOne) (CallPair L) := by
  refine call_stage (Q := VG.X86.Taint.Agree (workspaceTaint false)) ?_ ?_
  · apply (validateRange_relCT len modulus input aboveOne L.base L.size L.saved h4 hmax hw4).mono ?_ (fun _ _ h => h)
    intro s t H
    exact ⟨H.1.moduli.scr, H.2.moduli.scr, H.1.operand M (by omega_using [h4]) (by omega_using [hmax]),
      H.2.operand M (by omega_using [h4]) (by omega_using [hmax]), H.pointer M, H.pointer I⟩
  · intro s R
    exact WP.mono (stageRange_ok R.moduli h4 hmax hw4 (R.operand M (by omega_using [h4]) (by omega_using [hmax]))
      (R.operand I (by omega_using [h4]) (by omega_using [hmax])) aboveOne) fun _ H => H.2.2.execution (.inr ⟨rfl, rfl⟩)

theorem callEqual_relCT (L : CallLayout) (len : Nat) (a b : Pointer)
    (A : CallOperand L a len) (B : CallOperand L b len) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0) :
    RelCT isa (CallPair L) (Validate.equalValues len a b) (CallPair L) := by
  refine call_stage (Q := VG.X86.Taint.Agree (workspaceTaint false)) ?_ ?_
  · apply (validateEqual_relCT len a b L.base L.size L.saved h4 hmax hw4).mono ?_ (fun _ _ h => h)
    intro s t H
    exact ⟨H.1.moduli.scr, H.2.moduli.scr, H.1.operand A (by omega_using [h4]) (by omega_using [hmax]),
      H.2.operand A (by omega_using [h4]) (by omega_using [hmax]), H.pointer A, H.pointer B⟩
  · intro s R
    exact WP.mono (stageEqual_ok R.moduli h4 hmax hw4 (R.operand A (by omega_using [h4]) (by omega_using [hmax]))
      (R.operand B (by omega_using [h4]) (by omega_using [hmax]))) fun _ H => H.2.2.execution (.inr ⟨rfl, rfl⟩)

theorem callOne_relCT (L : CallLayout) (len : Nat) (input : Pointer)
    (I : CallOperand L input len) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0) :
    RelCT isa (CallPair L) (Validate.isOne len input) (CallPair L) := by
  refine call_stage (Q := VG.X86.Taint.Agree (workspaceTaint false)) ?_ ?_
  · exact (validateOne_relCT len input L.base L.size L.saved).mono
      (fun _ _ H => ⟨H.1.moduli.scr, H.2.moduli.scr, H.pointer I⟩) (fun _ _ h => h)
  · intro s R
    exact WP.mono (stageOne_ok R.moduli h4 hmax hw4 (R.operand I (by omega_using [h4]) (by omega_using [hmax])))
      fun _ H => H.2.2.execution (.inr ⟨rfl, rfl⟩)

theorem callZero_relCT (L : CallLayout) (len : Nat) (input : Pointer) (wantNonzero : Bool)
    (I : CallOperand L input len) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0) :
    RelCT isa (CallPair L) (Validate.zero len input wantNonzero) (CallPair L) := by
  refine call_stage (Q := VG.X86.Taint.Agree (workspaceTaint false)) ?_ ?_
  · exact (validateZero_relCT len input wantNonzero L.base L.size L.saved).mono
      (fun _ _ H => ⟨H.1.moduli.scr, H.2.moduli.scr, H.pointer I⟩) (fun _ _ h => h)
  · intro s R
    exact WP.mono (stageZero_ok R.moduli h4 hmax hw4 (R.operand I (by omega_using [h4]) (by omega_using [hmax])) wantNonzero)
      fun _ H => H.2.2.execution (.inr ⟨rfl, rfl⟩)

end VG.Proof.Dsa.X86

end

end

/-! ### `Dsa.X86.CallReduceTiming`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86.CoreReduceTiming`, which only this module used -/

section

/-! # Complete streaming reduction calls have secret-independent traces -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/CoreStreamSource.lean`, which only this module imported.
section

/-! # The public byte-source pointer for scalar reduction -/

section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

end VG.Proof.Dsa.X86
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

structure ReductionPre (base : Addr) (size qLen inputLen : Nat) (input : Pointer) (src : Src) (s : State) : Prop where
  scr : Scr s base size
  modulusReady : OperandReady s base ((qLen + 7) / 8) (.input .q) qLen
  inputReady : StreamInput s base (contextBytes ((qLen + 7) / 8)) (pointerValue base s input) inputLen
  len : LenOperand base size ((qLen + 7) / 8) s src inputLen
  large : 255 < Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input .q)).setWidth 64) qLen)
  odd : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input .q)).setWidth 64) qLen) % 2 = 1
  room : Pow.Room (s.gpr .esp) base size
  stack : Region.Disjoint ⟨(pointerValue base s input).setWidth 64, inputLen⟩ (callStack (s.gpr .esp))
  lenFit : inputLen < 2 ^ 32

theorem movLen_trace {src : Src} (hf : LenForm src) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint true)) (.block [.mov .ebx src]) (fun _ _ => True) := by
  intro s t tr ur s' t' A E F
  obtain ⟨τ, H⟩ : ∃ τ, taint.checkBlock (workspaceTaint true) [.mov .ebx src] = some τ := by
    rcases hf with ⟨v, rfl⟩ | ⟨d, rfl⟩
    · exact ⟨_, rfl⟩
    · refine ⟨workspaceTaint true, ?_⟩
      rw [← VG.X86.Taint.checkBlock_erase _ _ rfl]
      change taint.checkBlock (workspaceTaint true) [.mov .ebx (.mem (sc 0))] = _
      rfl
  have C : VG.Taint.check taint (workspaceTaint true) (.block [.mov .ebx src]) (.block []) = some τ := H
  exact ⟨(VG.Taint.check_sound C A E F).1, trivial⟩

theorem coreReduce_relCT (base : Addr) (size qLen inputLen output : Nat) (input : Pointer) (src : Src)
    (hf : LenForm src) (hz : Layout.saved ≤ size) (hu : usedBytes ≤ size) (h4 : 4 ≤ qLen) (hmax : qLen ≤ 384)
    (hw4 : qLen % 4 = 0) :
    RelCT isa (fun s t => ReductionPre base size qLen inputLen input src s ∧
      ReductionPre base size qLen inputLen input src t ∧
      pointerValue base s (.input .q) = pointerValue base t (.input .q) ∧
      pointerValue base s input = pointerValue base t input ∧ s.gpr .esp = t.gpr .esp)
      (Core.reduce qLen src input output) (VG.X86.Taint.Agree (workspaceTaint true)) := by
  have hn48 : (qLen + 7) / 8 ≤ 48 := by omega_using [hmax]
  have Hn : contextBytes ((qLen + 7) / 8) ≤ 8192 :=
    Nat.le_trans (VG.Proof.Dsa.X86.Layout.context_bound hn48) (by decide)
  have sz : 8256 ≤ size := hz
  have bound : slot ((qLen + 7) / 8) 0 + 8 * ((qLen + 7) / 8) ≤ contextBytes ((qLen + 7) / 8) := by
    have H := slot_bound (n := (qLen + 7) / 8) (i := 0) (by decide)
    simp only [stride] at H
    omega_using [H]
  unfold Core.reduce
  dsimp only
  apply RelCT.assoc
  -- the modulus, then the bytes' address and length
  have loadCT := ((coreLoad_relCT ((qLen + 7) / 8) qLen (slot ((qLen + 7) / 8) 0) (.input .q) base size hz).mono
      (P' := fun (s t : State) => ReductionPre base size qLen inputLen input src s ∧
        ReductionPre base size qLen inputLen input src t ∧
        pointerValue base s (.input .q) = pointerValue base t (.input .q) ∧
        pointerValue base s input = pointerValue base t input ∧ s.gpr .esp = t.gpr .esp)
      (fun _ _ H => ⟨H.1.scr, H.2.1.scr, H.2.2.1⟩) (fun _ _ h => h)).wpDep
    (F := fun (σ u : State) => Scr u base size ∧ pointerValue base u input = pointerValue base σ input)
    fun s t ⟨P, Q, _⟩ => by
      have go : ∀ σ, ReductionPre base size qLen inputLen input src σ → WP isa
          (Core.load ((qLen + 7) / 8) qLen (slot ((qLen + 7) / 8) 0) (.input .q)) σ
          fun u => Scr u base size ∧ pointerValue base u input = pointerValue base σ input := by
        intro σ R
        refine WP.mono (coreLoad_ok R.scr hz (by omega_using [Hn, sz, bound]) h4 (by omega_using []) hw4
          R.modulusReady.toReadableComponent (R.modulusReady.slot (by decide))) fun u ⟨_, K, O⟩ => ?_
        exact ⟨R.scr.of_keeps K (by decide),
          pointerValue_keep K (by decide) (O.mono (by omega_using []) (by omega_using [bound])) Hn input⟩
      exact ⟨go s P, go t Q⟩
  have headCT := RelCT.seq loadCT (RelCT.block_append (RelCT.seq ((pointer_relCT input base size hz).mono
      (fun _ _ ⟨_, σ₁, σ₂, ⟨_, _, _, I, _⟩, ⟨S₁, E₁⟩, ⟨S₂, E₂⟩⟩ => ⟨S₁, S₂, by rw [E₁, E₂, I]⟩) (fun _ _ h => h))
    (movLen_trace hf)))
  have head := headCT.wpDep (F := fun (σ w : State) =>
      Red.CallIn ((qLen + 7) / 8)
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt σ.mem ((pointerValue base σ (.input .q)).setWidth 64) qLen))
        w base size (pointerValue base σ input) inputLen ∧ Keeps powerClob σ w)
    fun s t ⟨P, Q, _⟩ => by
      have go : ∀ σ, ReductionPre base size qLen inputLen input src σ → WP isa _ σ fun w =>
          Red.CallIn ((qLen + 7) / 8)
            (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt σ.mem ((pointerValue base σ (.input .q)).setWidth 64) qLen))
            w base size (pointerValue base σ input) inputLen ∧ Keeps powerClob σ w := fun σ R =>
        WP.mono (reduceHead_ok R.len R.scr hz R.room rfl h4 hmax hw4 R.modulusReady R.inputReady R.stack
          R.lenFit rfl R.large R.odd) fun w ⟨C, _, K⟩ => ⟨C, K⟩
      exact ⟨go s P, go t Q⟩
  have hn : 0 < (qLen + 7) / 8 := by omega_using [h4]
  refine RelCT.seq (R := Red.CallReady ((qLen + 7) / 8)) (head.mono (fun _ _ h => h) ?_) ?_
  · rintro w₁ w₂ ⟨_, σ₁, σ₂, ⟨_, _, _, I, SP⟩, ⟨C₁, K₁⟩, ⟨C₂, K₂⟩⟩
    rw [← I] at C₂
    refine ⟨by rw [K₁.1 _ (by decide), K₂.1 _ (by decide)]; exact SP, fun r hr => ?_, base, size, _, _, _, _, hu, C₁, C₂⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [C₁.ebx, C₂.ebx]
    · rw [C₁.esi, C₂.esi]
    · exact Red.edi_eq C₁.scr C₂.scr
  refine RelCT.seq (R := VG.X86.Taint.Agree (workspaceTaint false)) ?_ (coreStore_workspace_relCT qLen output)
  refine ((Red.call_relCT _ hn).wpDep (F := fun (σ x : State) => x.gpr .edi = σ.gpr .edi) fun s t H => ?_).mono
    (fun _ _ h => h) fun x₁ x₂ ⟨_, σ₁, σ₂, ⟨_, RG, _⟩, e₁, e₂⟩ => ?_
  · obtain ⟨_, _, _, _, _, _, _, _, U, C₁, C₂⟩ := H
    exact ⟨WP.mono (Red.call_ok C₁ U hn hn48) fun _ ⟨_, _, K⟩ => K.1 _ (by decide),
      WP.mono (Red.call_ok C₂ U hn hn48) fun _ ⟨_, _, K⟩ => K.1 _ (by decide)⟩
  · apply agree_regs (rs := [.edi])
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    rw [e₁, e₂]; exact RG _ (by simp)

end VG.Proof.Dsa.X86

end

end


/-! # Streaming reduction stages retain the public call layout -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem CallReady.stream {L : CallLayout} {s : State} {p : Pointer} {len n : Nat}
    (R : CallReady L s) (O : CallOperand L p len) (hl : ∀ o, p = .local o → 0 < len) (hn : n ≤ 48) :
    StreamInput s L.base (contextBytes n) (pointerValue L.base s p) len := by
  rcases O with ⟨full, member, le⟩ | ⟨offset, rfl, lo, hi⟩
  · exact ((R.buffers (p, full) member).prefix le).stream (R.moduli.context hn)
  · exact localStream R.moduli.scr (hl _ rfl) (Nat.le_trans hi R.moduli.extent)
      (Nat.le_trans (VG.Proof.Dsa.X86.Layout.context_bound hn) (Nat.le_trans (by decide : 7048 ≤ r) lo))

theorem CallReady.stack {L : CallLayout} {s : State} {p : Pointer} {len : Nat}
    (R : CallReady L s) (O : CallOperand L p len) (hl : ∀ o, p = .local o → 0 < len) :
    Region.Disjoint ⟨(pointerValue L.base s p).setWidth 64, len⟩ (callStack (s.gpr .esp)) := by
  rcases O with ⟨full, member, le⟩ | ⟨offset, rfl, lo, hi⟩
  · exact ((R.buffers (p, full) member).prefix le).stack
  · exact localStack R.moduli.scr R.moduli.room (hl _ rfl) (Nat.le_trans hi R.moduli.extent)

theorem callReduce_relCT (L : CallLayout) (input : Pointer) (src : Src) (len output : Nat) (hf : LenForm src)
    (hsrc : ∀ s, CallReady L s → LenOperand L.base L.size ((L.qLen + 7) / 8) s src len)
    (Q : CallOperand L (.input .q) L.qLen) (I : CallOperand L input len)
    (hl : ∀ o, input = .local o → 0 < len) (hlen : len < 2 ^ 32)
    (ho : r ≤ output) (hb : output + L.qLen ≤ usedBytes) :
    RelCT isa (CallPair L) (Core.reduce L.qLen src input output) (CallPair L) := by
  have W := L.lengths
  have N : (L.qLen + 7) / 8 ≤ 48 := by omega_using [W]
  have hw4 : L.qLen % 4 = 0 := by have H := L.widths; unfold Spec.Dsa.lengthsValid at H; omega_using [H]
  have pre (s : State) (R : CallReady L s) : ReductionPre L.base L.size L.qLen len input src s := by
    refine ⟨R.moduli.scr, R.moduli.qReady, R.stream I hl N, hsrc s R, ?_, ?_, R.moduli.room, R.stack I hl, hlen⟩
    · change 255 < operandValue s L.base (.input .q) L.qLen
      rw [R.moduli.qValue]; exact R.moduli.qLarge
    · change operandValue s L.base (.input .q) L.qLen % 2 = 1
      rw [R.moduli.qValue]; exact R.moduli.qOdd
  refine call_stage (Q := VG.X86.Taint.Agree (workspaceTaint true)) ?_ ?_
  · apply (coreReduce_relCT L.base L.size L.qLen len output input src hf L.saved L.extent (by omega_using [W]) (by omega_using [W])
      hw4).mono ?_ (fun _ _ h => h)
    intro s t H
    exact ⟨pre s H.1, pre t H.2, H.pointer Q, H.pointer I, H.1.sp.trans H.2.sp.symm⟩
  · intro s R
    exact WP.mono (stageReduce_ok (hsrc s R) R.moduli (R.stream I hl N) (R.stack I hl) hlen ho hb)
      fun _ H => H.2.toStageFrame.execution (.inl ⟨ho, hb⟩)

/-- The saved digest prefix, as a length operand. -/
theorem CallReady.prefixOperand {L : CallLayout} {s : State} (R : CallReady L s) :
    LenOperand L.base L.size ((L.qLen + 7) / 8) s Core.digestPrefix L.digestPrefix :=
  LenOperand.prefix L.saved (by have := L.lengths; omega_using [this]) R.prefixLen

end VG.Proof.Dsa.X86

end

end

/-! ### `Dsa.X86.CallMinusTiming`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86.MinusTiming`, which only this module used -/

section

/-! # Constant-time formation of the fixed public modulus decrements -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem validateMinus_relCT (len amount output : Nat) (modulus : Field) (base : Addr) (size : Nat) (hz : Layout.saved ≤ size) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧
      pointerValue base s (.input modulus) = pointerValue base t (.input modulus))
      (Validate.minus len modulus amount output) (VG.X86.Taint.Agree (workspaceTaint true)) := by
  unfold Validate.minus
  dsimp only
  refine RelCT.seq (coreLoad_relCT _ _ _ _ base size hz) ?_
  exact (RelCT.seq (modulusMinus_relCT _ amount) (coreStore_workspace_relCT len output)).mono
    (fun _ _ h => taint.le_sound
      (show taint.le (workspaceTaint false) (workspaceTaint true) = true from rfl) h)
    (fun _ _ h => h)

end VG.Proof.Dsa.X86

end

end


/-! # Public modulus decrements retain the call layout -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem callMinusP_relCT (L : CallLayout) (output : Nat) (P : CallOperand L (.input .p) L.pLen)
    (ho : r ≤ output) (hb : output + L.pLen ≤ usedBytes) :
    RelCT isa (CallPair L) (Validate.minus L.pLen .p 1 output) (CallPair L) := by
  refine call_stage (Q := VG.X86.Taint.Agree (workspaceTaint true)) ?_ ?_
  · exact (validateMinus_relCT L.pLen 1 output .p L.base L.size L.saved).mono
      (fun _ _ H => ⟨H.1.moduli.scr, H.2.moduli.scr, H.pointer P⟩) (fun _ _ h => h)
  · intro s R
    exact WP.mono (stageMinusP_ok R.moduli (by have := R.moduli.pLarge; omega_using [this]) ho hb)
      fun _ H => H.2.toStageFrame.execution (.inl ⟨ho, hb⟩)

theorem callMinusQ_relCT (L : CallLayout) (output : Nat) (Q : CallOperand L (.input .q) L.qLen)
    (ho : r ≤ output) (hb : output + L.qLen ≤ usedBytes) :
    RelCT isa (CallPair L) (Validate.minus L.qLen .q 2 output) (CallPair L) := by
  refine call_stage (Q := VG.X86.Taint.Agree (workspaceTaint true)) ?_ ?_
  · exact (validateMinus_relCT L.qLen 2 output .q L.base L.size L.saved).mono
      (fun _ _ H => ⟨H.1.moduli.scr, H.2.moduli.scr, H.pointer Q⟩) (fun _ _ h => h)
  · intro s R
    exact WP.mono (stageMinusQ_ok R.moduli (by have := R.moduli.qLarge; omega_using [this]) ho hb)
      fun _ H => H.2.toStageFrame.execution (.inl ⟨ho, hb⟩)

end VG.Proof.Dsa.X86

end

end

/-! # Constant-time domain and key validation -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem CallOperand.localBuffer (L : CallLayout) (offset len : Nat)
    (lo : r ≤ offset) (hi : offset + len ≤ usedBytes) : CallOperand L (.local offset) len :=
  .inr ⟨offset, rfl, lo, hi⟩

theorem callDomain_relCT (L : CallLayout)
    (P : CallOperand L (.input .p) L.pLen) (Q : CallOperand L (.input .q) L.qLen)
    (G : CallOperand L (.input .g) L.pLen) (Y : CallOperand L (.input .y) L.pLen) :
    RelCT isa (CallPair L) (Validate.domain L.pLen L.qLen) (CallPair L) := by
  have W := L.lengths
  have T := CallOperand.localBuffer L t L.pLen (by decide) (by change 14944 + L.pLen ≤ 15712; omega_using [W])
  have U := CallOperand.localBuffer L u L.qLen (by decide) (by change 14816 + L.qLen ≤ 15712; omega_using [W])
  have A := L.aligned
  exact RelCT.seq (RelCT.seq
    (callRange_relCT L L.pLen .p (.input .g) true P G (by omega_using [W]) (by omega_using [W]) A.1)
    (callRange_relCT L L.pLen .p (.input .y) true P Y (by omega_using [W]) (by omega_using [W]) A.1))
    (RelCT.seq (callMinusP_relCT L t P (by decide) (by change 14944 + L.pLen ≤ 15712; omega_using [W]))
    (RelCT.seq (callReduce_relCT (hl := fun _ _ => by have := L.lengths; omega_using [W]) L (.local t) (.imm (BitVec.ofNat 32 L.pLen)) L.pLen u (.inl ⟨_, rfl⟩)
      (fun s _ => LenOperand.imm _ _ _ s _) Q T (by omega_using [W]) (by decide)
      (by change 14816 + L.qLen ≤ 15712; omega_using [W]))
    (RelCT.seq (callZero_relCT L L.qLen (.local u) false U (by omega_using [W]) (by omega_using [W]) A.2)
    (RelCT.seq (callMinusQ_relCT L qMinusTwo Q (by decide)
      (by change 14912 + L.qLen ≤ 15712; omega_using [W])) (RelCT.block_nil (fun _ _ h => h))))))

theorem callSubgroup_relCT (L : CallLayout)
    (P : CallOperand L (.input .p) L.pLen) (Q : CallOperand L (.input .q) L.qLen)
    (G : CallOperand L (.input .g) L.pLen) (Y : CallOperand L (.input .y) L.pLen) :
    RelCT isa (CallPair L) (Validate.subgroup L.pLen L.qLen) (CallPair L) := by
  have W := L.lengths
  have bound : t + L.pLen ≤ usedBytes := by change 14944 + L.pLen ≤ 15712; omega_using [W]
  have T := CallOperand.localBuffer L t L.pLen (by decide) bound
  have A := L.aligned
  exact RelCT.seq (callPowerP_relCT L (.input .g) (.input .q) t P G Q (by decide) bound)
    (RelCT.seq (callOne_relCT L L.pLen (.local t) T (by omega_using [W]) (by omega_using [W]) A.1)
    (RelCT.seq (callPowerP_relCT L (.input .y) (.input .q) t P Y Q (by decide) bound)
    (RelCT.seq (callOne_relCT L L.pLen (.local t) T (by omega_using [W]) (by omega_using [W]) A.1)
      (RelCT.block_nil (fun _ _ h => h)))))

theorem callPublicKey_relCT (L : CallLayout)
    (P : CallOperand L (.input .p) L.pLen) (Q : CallOperand L (.input .q) L.qLen)
    (G : CallOperand L (.input .g) L.pLen) (Y : CallOperand L (.input .y) L.pLen) :
    RelCT isa (CallPair L) (Validate.publicKey L.pLen L.qLen) (CallPair L) :=
  RelCT.seq (callDomain_relCT L P Q G Y) (callSubgroup_relCT L P Q G Y)

theorem callPrivateKey_relCT (L : CallLayout)
    (P : CallOperand L (.input .p) L.pLen) (Q : CallOperand L (.input .q) L.qLen)
    (G : CallOperand L (.input .g) L.pLen) (Y : CallOperand L (.input .y) L.pLen)
    (X : CallOperand L (.input .x) L.qLen) (K : CallOperand L (.input .nonce) L.qLen) :
    RelCT isa (CallPair L) (Validate.privateKey L.pLen L.qLen) (CallPair L) := by
  have W := L.lengths
  have bound : t + L.pLen ≤ usedBytes := by change 14944 + L.pLen ≤ 15712; omega_using [W]
  have T := CallOperand.localBuffer L t L.pLen (by decide) bound
  have A := L.aligned
  exact RelCT.seq (RelCT.seq
    (callRange_relCT L L.qLen .q (.input .x) false Q X (by omega_using [W]) (by omega_using [W]) A.2)
    (callRange_relCT L L.qLen .q (.input .nonce) false Q K (by omega_using [W]) (by omega_using [W]) A.2))
    (RelCT.seq (callPowerP_relCT L (.input .g) (.input .x) t P G X (by decide) bound)
    (RelCT.seq (callEqual_relCT L L.pLen (.local t) (.input .y) T Y (by omega_using [W]) (by omega_using [W]) A.1)
      (RelCT.block_nil (fun _ _ h => h))))

end VG.Proof.Dsa.X86
