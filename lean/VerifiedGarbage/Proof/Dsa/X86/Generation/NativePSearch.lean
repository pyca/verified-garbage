module
public import Aesop.BuiltinRules
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass.Point
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PAttempt
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PSearchState
import VerifiedGarbage.Proof.Dsa.X86.Generation.BufferArgs
import VerifiedGarbage.Proof.Dsa.X86.Generation.PSearchStable
import VerifiedGarbage.Proof.Dsa.X86.Generation.PSearchStep

/-! # Complete bounded p generation, with exact retries and witness exhaustion -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86 VG.Impl.Dsa.X86.Generation

theorem nativePSearch_ok {H : Hash} (K : HashOK H) {P : PSearchPlan} {W : Nat → BitVec 32} {used : Nat} {s : State}
    (R : PSearchMemory P W s) (cursor : W 16 = BitVec.ofNat 32 used) (bound : used ≤ P.context.witnesses.bytes.length)
    (digest : H.D = P.context.geometry.qLen) (final : H.F = P.context.geometry.qLen)
    (hash : ∀ bs, K.SH.H.hash bs = Spec.Dsa.seedHash (8 * P.seed.bytes.length) bs)
    (hashSize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * P.seed.bytes.length) bs).length = 8 * P.seed.bytes.length) :
    WP isa (nativePSearch H P.context.geometry.pLen P.context.geometry.qLen) s
      (PSearchFinished P (P.remaining 0 used) s) := by
  have pw := P.context.geometry.width
  have parent : s.mem.readW (off P.context.geometry.frameBase 20) 32 = P.context.geometry.parent :=
    (R.context.representation 5 (by decide)).trans ((R.context.fixed 5 (by decide) (by decide)).trans P.context.parent)
  unfold nativePSearch
  change WP isa (.seq (.block (bufferPointer .edi VG.Impl.Dsa.Generation.Layout.control)) _) s _
  refine WP.seq (WP.mono (bufferPointer_ok R.context.arena.frame parent .edi _) fun a ⟨di, mem, Ka⟩ => ?_)
  have Ra : PSearchMemory P W a := ⟨R.context.congr mem Ka (by decide),
    R.seed.keep (by rw [mem]; exact Frame.refl [] s.mem) (by simp) Ka, R.source, by rw [mem]; exact R.qval, R.seedUsed⟩
  have initial : PSearchInvariant P (P.remaining 0 used) s 0 a :=
    ⟨W, used, Ra, cursor, bound, by omega, rfl, by rw [mem]; exact Frame.refl _ _, Ka.2.1, Ka.2.2⟩
  exact pSearch_ok (by omega : 32 * P.context.geometry.pLen ≤ 12288) (by omega)
    (pSearchInvariant_stable P (P.remaining 0 used) s) (pSearchFinished_stable P (P.remaining 0 used) s)
    (fun _ I _ _ => pSearch_done I)
    (fun _ _ hc I C => pSearch_step K digest final hash hashSize hc I C)
    initial (Ra.context.arena.controlScr di)
end VG.Proof.Dsa.X86.Generation
