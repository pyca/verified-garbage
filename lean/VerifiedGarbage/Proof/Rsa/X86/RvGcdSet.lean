module
public import VerifiedGarbage.Proof.Rsa.RecoverSubtract
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.RvBase

import VerifiedGarbage.Proof.Rsa.X86.RvSubWrap
import VerifiedGarbage.Proof.Rsa.X86.RvScalarOps
import VerifiedGarbage.Proof.Rsa.X86.RvOps
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Tactic.Push
import Mathlib.Algebra.NeZero
import Mathlib.Basic.IsEmpty.Defs
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Initializing the GCD computation for the recovered factor -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa (sub32)

def AG (w m y : Nat) : Nat → Nat :=
  upd (upd (upd (upd (upd (upd (upd (upd (fun _ => 0) aN m) 0 (sub32 w y 1)) 1 m) aM m)
    2 1) 3 0) aZero 0) aNM (sub32 w 0 m)
abbrev liveG : List Nat := [aNM, aZero, 3, 2, aM, 1, 0, aN]

theorem gcdSet_ok {g : Geo} {s0 s : State} {A V : Nat → Nat} {m y : Nat}
    (h : KS g s0 A [mY, aN, aZ, aOne] (fun _ => 0) [] V [sMask] s)
    (modulus : A aN = m) (value : A mY = y) (zero : A aZ = 0) (one : A aOne = 1) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.gcdSet s fun t => KS g s0 (AG g.w m y) liveG (fun _ => 0) [] V [sMask] t := by
  unfold VG.Impl.Rsa.X86.RecoverRt.gcdSet
  simp only [seqs]
  refine WP.seq (WP.mono (h.subWrap (o := 0) (a := mY) (b := aOne)
    (by decide) (by simp) (by simp) (by decide) (by decide) (by simp)) fun s1 ⟨h1, _⟩ => ?_)
  rw [value, one] at h1
  refine WP.seq (WP.mono (h1.copy_w (o := 1) (a := aN) (by decide) (by simp) (by decide) (by simp))
    fun s2 ⟨h2, _, _⟩ => ?_)
  refine WP.seq (WP.mono (h2.copy_w (o := aM) (a := aN) (by decide) (by simp) (by decide) (by simp))
    fun s3 ⟨h3, _, _⟩ => ?_)
  refine WP.seq (WP.mono (h3.copy_w (o := 2) (a := aZ) (by decide) (by simp) (by decide) (by simp))
    fun s4 ⟨h4, _, _⟩ => ?_)
  refine WP.seq (WP.mono (h4.setOne_w (j := 2) (by simp) (by simp)) fun s5 ⟨h5, _⟩ => ?_)
  refine WP.seq (WP.mono (h5.copy_w (o := 3) (a := aZ) (by decide) (by simp) (by decide) (by simp))
    fun s6 ⟨h6, _, _⟩ => ?_)
  refine WP.seq (WP.mono (h6.copy_w (o := aZero) (a := aZ) (by decide) (by simp) (by decide) (by simp))
    fun s7 ⟨h7, _, _⟩ => ?_)
  refine WP.mono (h7.subWrap (o := aNM) (a := aZero) (b := aM)
    (by decide) (by simp) (by simp) (by decide) (by decide) (by simp)) fun t ⟨hout, _⟩ => ?_
  have vN : A 32 = m := modulus
  have vZ : A 34 = 0 := zero
  refine hout.mono ?_ (by simp) (fun d hd => ⟨hd, rfl⟩)
  intro j hj
  simp only [liveG, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [AG, upd, aNM, aZero, aM, aZ, aOne, aN, mY, vN, vZ]

end VG.Proof.Rsa.X86.Recover
