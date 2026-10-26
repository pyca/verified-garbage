module

public import VerifiedGarbage.Impl.Dsa.X86.Generate
import VerifiedGarbage.Proof.Dsa.X86.FailureLoop
import VerifiedGarbage.Proof.Mont.X86.Instr
import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.Dsa.X86.Pointer
public import VerifiedGarbage.Spec.Rsa.Contract
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs

/-! # Invalid shapes clear the complete derived key -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86

theorem deriveFailure_ok {s : State} {base : Addr} {size pLen qLen : Nat} {out : BitVec 32}
    (hs : Scr s base size) (hz : Layout.saved ≤ size)
    (hl : 0 < 3 * pLen + 2 * qLen) (hb : 3 * pLen + 2 * qLen < 2 ^ 32)
    (hp : pointerValue base s (.input .out) = out)
    (hf : out.toNat + (3 * pLen + 2 * qLen) ≤ 2 ^ 32)
    (hw : ∀ i < 3 * pLen + 2 * qLen, InRegions s.wr (out.setWidth 64 + BitVec.ofNat 64 i) 1) :
    WP isa (Generate.deriveFailure pLen qLen) s fun t =>
      Spec.Rsa.bytesAt t.mem (out.setWidth 64) (3 * pLen + 2 * qLen) = List.replicate (3 * pLen + 2 * qLen) 0 ∧
      t.gpr .eax = 0 ∧ Outside (out.setWidth 64) 0 (3 * pLen + 2 * qLen) s.mem t.mem ∧ Keeps [.esi, .ecx, .eax] s t := by
  have bound : 8256 ≤ size := hz
  unfold Generate.deriveFailure Core.sequence
  dsimp only [List.foldr]
  refine WP.seq (wp_movS (readSrc_sc hs (d := Layout.field .out) (by change 8228 ≤ size; omega)) fun s1 U1 _ => ?_)
  refine wp_movS rfl fun s2 U2 _ => ?_
  refine wp_movS rfl fun s3 U3 _ => WP.block_nil ?_
  have K3 : Keeps [.esi, .ecx, .eax] s s3 :=
    ((U1.keeps.mono (by decide)).trans (U2.keeps.mono (by decide))).trans (U3.keeps.mono (by decide))
  have O3 : s3.mem = s.mem := by rw [U3.mem, U2.mem, U1.mem]
  refine WP.seq (WP.mono (failureLoop_ok hl hb hf
    (by rw [U3.other _ (by decide), U2.other _ (by decide), U1.gpr]; exact hp)
    (by rw [U3.other _ (by decide), U2.gpr]) U3.gpr
    (by intro i hi; rw [K3.2.2]; exact hw i hi)) fun t ⟨V, Z, O, K⟩ => ?_)
  exact WP.block_nil ⟨V, Z, by simpa only [O3] using O, K3.trans (K.mono (by decide))⟩

end VG.Proof.Dsa.X86
