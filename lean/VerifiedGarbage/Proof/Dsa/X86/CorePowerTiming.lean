module

public import VerifiedGarbage.Proof.Dsa.X86.ArithmeticHeadTiming
public import VerifiedGarbage.Proof.Dsa.X86.ArithmeticHead
public import VerifiedGarbage.Proof.Dsa.X86.StackFrame

import VerifiedGarbage.Proof.Dsa.X86.CoreStoreTiming
import VerifiedGarbage.Proof.Dsa.X86.RawInputsTiming
import VerifiedGarbage.Proof.Dsa.X86.PowCallTiming
import VerifiedGarbage.Proof.Dsa.X86.PointerTiming
import VerifiedGarbage.Proof.Dsa.X86.PowCall
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
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
  have hn : n ≤ 48 := by dsimp only [n]; omega
  have cb := VG.Proof.Dsa.X86.Layout.context_bound hn
  have sz : 8256 ≤ size := hz
  have nw := P.scr.nowrap
  have bounds (j : Nat) (hj : j < 9) : slot n j + 8 * n ≤ size := by
    have H := slot_bound (n := n) hj
    simp only [stride] at H
    omega
  unfold powerHead
  refine WP.seq (WP.mono (coreLoad_ok P.scr hz (bounds 0 (by decide)) h4 (by omega) hw4
    P.modulusReady.toReadableComponent (P.modulusReady.slot (by decide))) fun u ⟨M, K, O⟩ => ?_)
  have O' := slotOutside_whole O (by decide)
  have A := P.leftReady.keep K (by decide) O' hn
  have B := P.rightReady.keep K (by decide) O' hn
  refine WP.seq (WP.mono (coreLoad_ok (P.scr.of_keeps K (by decide)) hz (bounds 5 (by decide)) h4
    (by omega) hw4 A.toReadableComponent (A.slot (by decide))) fun v ⟨_, L, F⟩ => ?_)
  have B' := B.keep L (by decide) (slotOutside_whole F (by decide)) hn
  refine WP.mono (coreLoad_ok (P.scr.of_keeps (K.trans L) (by decide)) hz (bounds 8 (by decide)) hb4
    (by omega) hwb B'.toReadableComponent (B'.slot (by decide))) fun t ⟨_, N, G⟩ => ?_
  have allK := (K.trans L).trans N
  have mod : wordsVal t.mem base (slot n 0) n =
      Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input modulus)).setWidth 64) len) := by
    rw [slotOutside_val G (by decide) (by have H := bounds 0 (by decide); dsimp only [n] at H; omega),
      slotOutside_val F (by decide) (by have H := bounds 0 (by decide); dsimp only [n] at H; omega), M]
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
  have hn : (len + 7) / 8 ≤ 48 := by omega
  have Hn := VG.Proof.Dsa.X86.Layout.context_bound hn
  have B := slot_bound (n := (len + 7) / 8) (i := 0) (by decide)
  have H : 8256 ≤ size := hz
  have fit : slot ((len + 7) / 8) 0 + 8 * ((len + 7) / 8) ≤ size := by
    simp only [stride] at B; omega
  cases E with
  | seq E₀ E₁ => cases F with
    | seq F₀ F₁ =>
      have Trace₀ := (coreLoad_relCT _ len _ (.input modulus) base size hz
        _ _ _ _ _ _ ⟨P.scr, Q.scr, Mod⟩ E₀ F₀).1
      obtain ⟨_, K₁, O₁⟩ := wp_result (coreLoad_ok P.scr hz fit h4 (by omega) hw4
        P.modulusReady.toReadableComponent (P.modulusReady.slot (by decide))) E₀
      obtain ⟨_, K₂, O₂⟩ := wp_result (coreLoad_ok Q.scr hz fit h4 (by omega) hw4
        Q.modulusReady.toReadableComponent (Q.modulusReady.slot (by decide))) F₀
      have W₁ := slotOutside_whole O₁ (by decide)
      have W₂ := slotOutside_whole O₂ (by decide)
      have A₁ := P.leftReady.keep K₁ (by decide) W₁ hn
      have A₂ := Q.leftReady.keep K₂ (by decide) W₂ hn
      have PL := (pointerValue_keep K₁ (by decide) W₁ (by omega) a).trans
        (Left.trans (pointerValue_keep K₂ (by decide) W₂ (by omega) a).symm)
      have PR := (pointerValue_keep K₁ (by decide) W₁ (by omega) b).trans
        (Right.trans (pointerValue_keep K₂ (by decide) W₂ (by omega) b).symm)
      obtain ⟨Trace₁, Agree⟩ := rawInputs_relCT _ len bl 5 8 a b base size hz hn (by decide)
        h4 (by omega) hw4 _ _ _ _ _ _ ⟨P.scr.of_keeps K₁ (by decide), Q.scr.of_keeps K₂ (by decide), A₁, A₂, PL, PR⟩ E₁ F₁
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
  have hn : (len + 7) / 8 ≤ 48 := by omega
  have cb := VG.Proof.Dsa.X86.Layout.context_bound hn
  have sz : 8256 ≤ size := hz
  unfold Core.power
  dsimp only
  apply RelCT.assoc
  refine RelCT.seq ?_ (powerTail_relCT base size _ len _ output (by omega) hu (by omega) hn (by omega) (by omega))
  have H := (powerHead_relCT base size len expLen modulus a b hz (by omega) hmax hw4).mono
    (fun _ _ (P : PowerAgree base size len expLen modulus a b _ _) => P.1) (fun _ _ A => A)
  refine (H.wpDep (F := fun s t => PowerReady base size ((len + 7) / 8) t ∧ Keeps loadClob s t)
    (fun s t P => ⟨powerHead_ok P.1.1 P.2.1 hz (by omega) hmax (by omega) hel hw4 hew,
      powerHead_ok P.1.2.1 P.2.2.1 hz (by omega) hmax (by omega) hel hw4 hew⟩)).mono (fun _ _ P => P) ?_
  rintro s t ⟨_, a, b, P, ⟨S, K⟩, ⟨T, L⟩⟩
  exact ⟨S, T, (K.1 .esp (by decide)).trans (P.2.2.2.trans (L.1 .esp (by decide)).symm)⟩

end VG.Proof.Dsa.X86
