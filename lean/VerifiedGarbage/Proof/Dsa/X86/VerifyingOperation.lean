module

public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI
public import VerifiedGarbage.Proof.Dsa.X86.OutputFrame
public import VerifiedGarbage.Impl.Dsa.X86.Entry
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Dsa.X86.InstalledInputs
import VerifiedGarbage.Proof.Dsa.X86.ABIResources
import VerifiedGarbage.Proof.Dsa.X86.EntrySave
import VerifiedGarbage.Proof.Dsa.X86.CallerBuffer
public import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Spec.Dsa.SignVerify
import VerifiedGarbage.Proof.Dsa.X86.ShapeSavedFrame
import VerifiedGarbage.Proof.Dsa.OutputBytes
import VerifiedGarbage.Proof.Dsa.X86.SavedFrame
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Dsa.X86.Installed
import VerifiedGarbage.Proof.Mont.X86.PowerStep
import VerifiedGarbage.Proof.Dsa.X86.PackedKeyBuffers
public import VerifiedGarbage.Proof.Dsa.X86.Pointer
import VerifiedGarbage.Proof.Dsa.X86.WidthMatch
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Dsa.X86.Checks
public import VerifiedGarbage.Proof.Dsa.X86.Moduli
public import VerifiedGarbage.Proof.Dsa.X86.ShapeOperands
public import VerifiedGarbage.Proof.Dsa.Accepted
import VerifiedGarbage.Proof.Dsa.X86.ShapeModuli
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.Dsa.X86.FailureLoop
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! ### `Dsa.X86.Failure`, which this module and modules that import it used -/

section

/-! # Early failure returns zero and clears the complete signing output -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86

theorem signFailure_ok {s : State} {base : Addr} {size qLen : Nat} {out : BitVec 32}
    (hs : Scr s base size) (hz : Layout.saved ≤ size) (hl : 0 < qLen) (hq : qLen ≤ 32)
    (hp : pointerValue base s (.input .out) = out)
    (hc : pointerValue base s (.input .qLen) = BitVec.ofNat 32 qLen)
    (hf : out.toNat + 2 * qLen ≤ 2 ^ 32)
    (hw : ∀ i, i < 2 * qLen → InRegions s.wr (out.setWidth 64 + BitVec.ofNat 64 i) 1) :
    WP isa (Entry.failure true) s fun t =>
      Spec.Rsa.bytesAt t.mem (out.setWidth 64) (2 * qLen) = List.replicate (2 * qLen) 0 ∧
      t.gpr .eax = 0 ∧ Outside (out.setWidth 64) 0 (2 * qLen) s.mem t.mem ∧ Keeps [.esi, .ecx, .eax] s t := by
  have bound : 8256 ≤ size := hz
  unfold Entry.failure Core.sequence
  dsimp only [List.foldr, ite_true]
  refine WP.seq (wp_movS (readSrc_sc hs (d := Layout.field .out) (by change 8228 ≤ size; omega_using [bound])) fun s1 U1 _ => ?_)
  have K1 := U1.keeps
  refine wp_movS (readSrc_sc (hs.of_keeps K1 (by decide)) (d := Layout.field .qLen) (by change 8236 ≤ size; omega_using [bound])) fun s2 U2 _ => ?_
  refine wp_addS rfl fun s3 U3 _ => ?_
  refine wp_movS rfl fun s4 U4 _ => WP.block_nil ?_
  have K4 : Keeps [.esi, .ecx, .eax] s s4 :=
    (((U1.keeps.mono (by decide)).trans (U2.keeps.mono (by decide))).trans (U3.keeps.mono (by decide))).trans (U4.keeps.mono (by decide))
  have O4 : s4.mem = s.mem := by rw [U4.mem, U3.mem, U2.mem, U1.mem]
  have P4 : s4.gpr .esi = out := by
    rw [U4.other _ (by decide), U3.other _ (by decide), U2.other _ (by decide), U1.gpr]
    exact hp
  have C4 : s4.gpr .ecx = BitVec.ofNat 32 (2 * qLen) := by
    rw [U4.other _ (by decide), U3.gpr, U2.gpr, U1.mem]
    change pointerValue base s (.input .qLen) + pointerValue base s (.input .qLen) = _
    rw [hc, ← BitVec.ofNat_add, ← Nat.two_mul]
  refine WP.seq (WP.mono (failureLoop_ok (by omega_using [hl]) (by omega_using [hq]) hf P4 C4 U4.gpr
    (by intro i hi; rw [K4.2.2]; exact hw i hi)) fun t ⟨V, Z, O, K⟩ => ?_)
  exact WP.block_nil ⟨V, Z, by simpa only [O4] using O, K4.trans (K.mono (by decide))⟩

theorem verifyFailure_ok (s : State) :
    WP isa (Entry.failure false) s fun t => t.gpr .eax = 0 ∧ Keeps [.eax] s t ∧ t.mem = s.mem := by
  exact wp_movS rfl fun t U _ => WP.block_nil ⟨U.gpr, U.keeps, U.mem⟩

end VG.Proof.Dsa.X86

end

end

/-! ### `Dsa.X86.Sized`, which this module and modules that import it used -/

section

/-! # Public shape rejection before the arithmetic body -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Proof.Ecdsa.X86
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem sized_ok (signing : Bool) {s : State} {base : Addr} {size pLen qLen p q : Nat}
    {post : State → Prop}
    (hs : Scr s base size) (extent : usedBytes ≤ size) (widths : Spec.Dsa.lengthsValid pLen qLen)
    (P : CallerBuffer s base size (.input .p) pLen) (Q : CallerBuffer s base size (.input .q) qLen)
    (hp : operandValue s base (.input .p) pLen = p) (hq : operandValue s base (.input .q) qLen = q)
    (failure : ∀ t, ¬ shapeValid p q → Keeps shapeClob s t →
      Outs base shapeRanges s.mem t.mem → WP isa (Entry.failure signing) t post)
    (body : ∀ t, shapeValid p q → Moduli base size pLen qLen p q t →
      (pointerValue base t (.input .digestPrefixLen)).toNat =
        min (pointerValue base s (.input .digestLen)).toNat (Spec.Dsa.bitLength q / 8) →
      flagW base (Layout.field .mask) t = BitVec.allOnes 32 →
      Keeps shapeClob s t → Outs base shapeRanges s.mem t.mem →
      WP isa (if signing then SignVerify.signBody pLen qLen else SignVerify.verifyBody pLen qLen) t post) :
    WP isa (Entry.sized signing pLen qLen) s post := by
  unfold Entry.sized
  refine WP.seq (WP.mono (shapeModuli_ok hs extent widths P Q hp hq) fun t ⟨F, Z, M, K, O⟩ => ?_)
  by_cases valid : shapeValid p q
  · refine WP.ite false (by simp only [eval, Z, valid, decide_true, Bool.not_true])
      (fun h => Bool.noConfusion h) (fun _ => ?_)
    obtain ⟨Mt, D⟩ := M valid
    exact body t valid Mt D (by simpa only [flagW, mask32, valid, decide_true, ite_true] using F) K O
  · refine WP.ite true (by simp only [eval, Z, valid, decide_false, Bool.not_false])
      (fun _ => failure t valid K O) (fun h => Bool.noConfusion h)

end VG.Proof.Dsa.X86

end

end

/-! ### `Dsa.X86.ReturnFrame`, which this module and modules that import it used -/

section

/-! # Restoring the cdecl registers and protecting the return address -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Spill VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86

theorem return_stack_disjoint {sp : BitVec 32} (h : 108 ≤ sp.toNat) :
    Region.Disjoint ⟨sp.setWidth 64, 4⟩ (callStack sp) := by
  rw [callStack_eq h]
  intro x hx hc
  have hs := sp.isLt
  simp only [Region.Contains] at hx hc
  bv_omega

theorem outside_return {s t : State} {base : Addr} {size : Nat}
    (O : StackOutside (s.gpr .esp) base size s.mem t.mem)
    (apart : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨base, size⟩) (hsp : 108 ≤ (s.gpr .esp).toNat) :
    t.mem.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32 := by
  apply Mem.readW_congr
  intro i hi
  have H := apart ((s.gpr .esp).setWidth 64 + BitVec.ofNat 64 i) (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi]))
  change ¬ (ofs base ((s.gpr .esp).setWidth 64 + BitVec.ofNat 64 i) + 1 ≤ size) at H
  exact O _ (by omega_using [H]) (return_stack_disjoint hsp _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])))

theorem outputFrame_return {s t : State} {base out : Addr} {size len : Nat}
    (O : StackOutputFrame (s.gpr .esp) base out size len s.mem t.mem)
    (scratchApart : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨base, size⟩)
    (outApart : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨out, len⟩) (hsp : 108 ≤ (s.gpr .esp).toNat) :
    t.mem.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32 := by
  apply Mem.readW_congr
  intro i hi
  have W := scratchApart ((s.gpr .esp).setWidth 64 + BitVec.ofNat 64 i) (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi]))
  have B := outApart ((s.gpr .esp).setWidth 64 + BitVec.ofNat 64 i) (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi]))
  change ¬ (ofs base ((s.gpr .esp).setWidth 64 + BitVec.ofNat 64 i) + 1 ≤ size) at W
  change ¬ (ofs out ((s.gpr .esp).setWidth 64 + BitVec.ofNat 64 i) + 1 ≤ len) at B
  exact O _ (by omega_using [W]) (by omega_using [B]) (return_stack_disjoint hsp _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])))

theorem restored_abi {s t u : State} (R : Restored t u s.gpr Entry.savedRegisters)
    (sp : t.gpr .esp = s.gpr .esp)
    (ret : t.mem.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32) :
    abiPreserved s u := by
  refine ⟨?_, by rw [R.mem]; exact ret⟩
  intro reg hr
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact R.regs _ (by decide)
  · exact R.regs _ (by decide)
  · exact R.regs _ (by decide)
  · exact R.regs _ (by decide)
  · exact (R.other _ (by decide)).trans sp

end VG.Proof.Dsa.X86

end

end

/-! ### `Dsa.X86.WidthDispatch`, which this module and modules that import it used -/

section

/-! # Selecting supported public component widths -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86

theorem widthDispatch_ok (signing : Bool) (widths : List (Nat × Nat))
    {s : State} {base : Addr} {size pLen qLen : Nat} {Q : State → Prop}
    (hs : Scr s base size) (hz : Layout.saved ≤ size) (member : (pLen, qLen) ∈ widths)
    (bound : ∀ w ∈ widths, w.1 < 2 ^ 32 ∧ w.2 < 2 ^ 32)
    (hp : (pointerValue base s (.input .pLen)).toNat = pLen)
    (hq : (pointerValue base s (.input .qLen)).toNat = qLen)
    (body : ∀ t, Keeps [.eax] s t → t.mem = s.mem → WP isa (Entry.sized signing pLen qLen) t Q) :
    WP isa (Entry.widthDispatch signing widths) s Q := by
  induction widths generalizing s with
  | nil => simp only [List.not_mem_nil] at member
  | cons w rest ih =>
    obtain ⟨wp, wq⟩ := w
    have B := bound (wp, wq) List.mem_cons_self
    have Brest : ∀ w ∈ rest, w.1 < 2 ^ 32 ∧ w.2 < 2 ^ 32 :=
      fun w hw => bound w (List.mem_cons_of_mem _ hw)
    unfold Entry.widthDispatch
    refine WP.seq (WP.mono (widthMatch_ok hs hz hp hq B.1 B.2) fun t ⟨Z, K, O⟩ => ?_)
    by_cases Both : pLen = wp ∧ qLen = wq
    · refine WP.ite true (by simp only [eval, Z, Both, true_and, decide_true]) (fun _ => ?_) (fun h => Bool.noConfusion h)
      rw [← Both.1, ← Both.2]
      exact body t K O
    · refine WP.ite false (by simp only [eval, Z, Both, decide_false]) (fun h => Bool.noConfusion h) (fun _ => ?_)
      apply ih (hs.of_keeps K (by decide))
        (by simpa only [List.mem_cons, Prod.mk.injEq, Both, false_or] using member) Brest
      · simpa only [pointerValue, O] using hp
      · simpa only [pointerValue, O] using hq
      · intro u Ku Ou
        exact body u (K.trans Ku) (Ou.trans O)

end VG.Proof.Dsa.X86

end

end

/-! # Complete functional and cdecl verification of the x86 verifier -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/VerifySized.lean`, which only this module imported.
section

/-! # The complete public-size verifier, including invalid domain rejection -/

section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

end VG.Proof.Dsa.X86
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/VerifyingInstalled.lean`, which only this module imported.
section

/-! # Verification of original caller bytes after cdecl argument installation -/

section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

end VG.Proof.Dsa.X86
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem supportedWidths_member {pLen qLen : Nat} (H : Spec.Dsa.lengthsValid pLen qLen) :
    (pLen, qLen) ∈ [(128, 20), (256, 28), (256, 32), (384, 32), (256, 20)] := by
  unfold Spec.Dsa.lengthsValid at H
  rcases H with ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl⟩ <;> decide

end VG.Proof.Dsa.X86
