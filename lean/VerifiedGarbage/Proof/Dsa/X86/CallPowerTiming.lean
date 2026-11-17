module

public import VerifiedGarbage.Proof.Dsa.X86.CallTiming
import VerifiedGarbage.Proof.Dsa.X86.StagePower
import VerifiedGarbage.Proof.Weierstrass.MontContract
public import VerifiedGarbage.Proof.Dsa.X86.StackFrame
import VerifiedGarbage.Proof.Dsa.X86.RawInputsTiming
import VerifiedGarbage.Proof.Dsa.X86.PowCallTiming
import VerifiedGarbage.Proof.Dsa.X86.PointerTiming
import VerifiedGarbage.Proof.Dsa.X86.PowCall
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
import VerifiedGarbage.Proof.Dsa.X86.CoreSetup
public import VerifiedGarbage.Proof.Dsa.X86.CoreFrame
import VerifiedGarbage.Proof.Dsa.X86.CoreInputs
public import VerifiedGarbage.Impl.Dsa.X86.Core
import VerifiedGarbage.Proof.Dsa.X86.BytesTiming
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Dsa.X86.Pointer
import VerifiedGarbage.Proof.Mont.X86.PowerTiming

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
