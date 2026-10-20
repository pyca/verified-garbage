module
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.Dsa.X86.Entry
public import VerifiedGarbage.Proof.Dsa.X86.Pointer
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Spec.Weierstrass

import VerifiedGarbage.Proof.Dsa.X86.FailureLoop
import VerifiedGarbage.Proof.Mont.X86.Instr

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
  refine WP.seq (wp_movS (readSrc_sc hs (d := Layout.field .out) (by change 8228 ≤ size; omega)) fun s1 U1 _ => ?_)
  have K1 := U1.keeps
  refine wp_movS (readSrc_sc (hs.of_keeps K1 (by decide)) (d := Layout.field .qLen) (by change 8236 ≤ size; omega)) fun s2 U2 _ => ?_
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
  refine WP.seq (WP.mono (failureLoop_ok (by omega) (by omega) hf P4 C4 U4.gpr
    (by intro i hi; rw [K4.2.2]; exact hw i hi)) fun t ⟨V, Z, O, K⟩ => ?_)
  exact WP.block_nil ⟨V, Z, by simpa only [O4] using O, K4.trans (K.mono (by decide))⟩

theorem verifyFailure_ok (s : State) :
    WP isa (Entry.failure false) s fun t => t.gpr .eax = 0 ∧ Keeps [.eax] s t ∧ t.mem = s.mem := by
  exact wp_movS rfl fun t U _ => WP.block_nil ⟨U.gpr, U.keeps, U.mem⟩

end VG.Proof.Dsa.X86
