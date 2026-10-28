module
public import VerifiedGarbage.Proof.Dsa.X86.ArithmeticHeadTiming
public import VerifiedGarbage.Proof.Dsa.X86.CorePowerTiming

import VerifiedGarbage.Proof.Dsa.X86.ArithmeticTiming
import VerifiedGarbage.Proof.Dsa.X86.CoreStoreTiming
import VerifiedGarbage.Proof.Dsa.X86.MulCall
import VerifiedGarbage.Proof.Dsa.X86.MulTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Complete modular products have secret-independent execution traces -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem productTail_relCT (base : Addr) (size n len output : Nat)
    (hz : contextBytes n ≤ size) (hu : usedBytes ≤ size) (hn : 0 < n) (hn48 : n ≤ 48) :
    RelCT isa (PowerPair base size n) (.seq (Arith.mulCall n) (Core.store len output))
      (VG.X86.Taint.Agree (workspaceTaint true)) := by
  refine RelCT.seq ?_ (coreStore_workspace_relCT len output)
  intro s t tr ur sf tf ⟨S, T, SP⟩ E F
  have DI : s.gpr .edi = t.gpr .edi := BitVec.eq_of_toNat_eq (S.scr.edi_toNat.trans T.scr.edi_toNat.symm)
  have CT := (Mul.call_relCT n) _ _ _ _ _ _ ⟨SP, DI, by have := S.room.1; omega⟩ E F
  obtain ⟨_, _, K⟩ := wp_result (Mul.call_ok S.scr S.room hz hu hn hn48 rfl S.large S.odd) E
  obtain ⟨_, _, L⟩ := wp_result (Mul.call_ok T.scr T.room hz hu hn hn48 rfl T.large T.odd) F
  refine ⟨CT.1, agree_regs (rs := [.edi]) ?_⟩
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  rw [K.1 .edi (by decide), L.1 .edi (by decide), DI]

theorem coreProductMod_relCT (base : Addr) (size len output : Nat) (modulus : Field) (a b : Pointer)
    (hz : Layout.saved ≤ size) (hu : usedBytes ≤ size) (h4 : 4 ≤ len) (hmax : len ≤ 384)
    (hw4 : len % 4 = 0) :
    RelCT isa (PowerAgree base size len len modulus a b)
      (Core.productMod len modulus a b output) (VG.X86.Taint.Agree (workspaceTaint true)) := by
  have hn : (len + 7) / 8 ≤ 48 := by omega
  have cb := VG.Proof.Dsa.X86.Layout.context_bound hn
  have sz : 8256 ≤ size := hz
  unfold Core.productMod
  dsimp only
  refine RelCT.seq ?_ (productTail_relCT base size _ len output (by omega) hu (by omega) hn)
  have H := (powerHead_relCT base size len len modulus a b hz h4 hmax hw4).mono
    (fun _ _ (P : PowerAgree base size len len modulus a b _ _) => P.1) (fun _ _ A => A)
  refine (H.wpDep (F := fun s t => PowerReady base size ((len + 7) / 8) t ∧ Keeps loadClob s t)
    (fun s t P => ⟨powerHead_ok P.1.1 P.2.1 hz h4 hmax h4 (Nat.le_refl _) hw4 hw4,
      powerHead_ok P.1.2.1 P.2.2.1 hz h4 hmax h4 (Nat.le_refl _) hw4 hw4⟩)).mono (fun _ _ P => P) ?_
  rintro s t ⟨_, a, b, P, ⟨S, K⟩, ⟨T, L⟩⟩
  exact ⟨S, T, (K.1 .esp (by decide)).trans (P.2.2.2.trans (L.1 .esp (by decide)).symm)⟩

theorem coreSum_relCT (base : Addr) (size len output : Nat) (a b : Pointer)
    (hz : Layout.saved ≤ size) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0) :
    RelCT isa (ArithmeticAgree base size len len .q a b)
      (Core.sum len a b output) (VG.X86.Taint.Agree (workspaceTaint true)) := by
  unfold Core.sum
  dsimp only
  apply RelCT.assoc
  refine RelCT.seq (arithmeticHead_relCT base size len len .q a b hz h4 hmax hw4) ?_
  refine RelCT.seq (ordinaryAdd_relCT _) ?_
  exact (coreStore_workspace_relCT len output).mono
    (fun _ _ h => taint.le_sound (show taint.le (workspaceTaint false) (workspaceTaint true) = true from rfl) h)
    (fun _ _ h => h)

end VG.Proof.Dsa.X86
