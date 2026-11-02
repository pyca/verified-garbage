module

import VerifiedGarbage.Proof.Mont.X86.Compact.EntryMemory

public import VerifiedGarbage.Proof.Mont.X86.Rt.Sub

public import VerifiedGarbage.Proof.Mont.X86.Compact.Frame

import VerifiedGarbage.Proof.Mont.X86.Compact.EntryArgs
import VerifiedGarbage.Proof.Mont.X86.Compact.Core
import VerifiedGarbage.Proof.Mont.X86.Compact.EntryValues
import VerifiedGarbage.Proof.Mont.X86.Compact.Arithmetic
import VerifiedGarbage.Proof.Mont.X86.Compact.Prepared
import VerifiedGarbage.Proof.Mont.X86.Compact.Layout
public import VerifiedGarbage.Impl.Mont.X86.Compact
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Mont.X86.Compact.Entry

/-! # The public prepared contract supplies every compact arithmetic precondition -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Rsa.Mont hiding Keeps
open VG.Impl.Mont.X86

theorem Entry.core {s : State} (A : Entry s) :
    let W := wsOf s
    let w := wOf s.mem W
    let S := arrAt w 2
    let o := arrAt w (arg s 2).toNat
    WP isa Compact.core (entered s) fun t =>
      Outs W [(S, 8 * (2 * w) + 28), (o, 4 * (2 * w))] (entered s).mem t.mem ∧
      val32 t.mem W o (2 * w) < val32 s.mem W (arrAt w 0) (2 * w) ∧
      val32 t.mem W o (2 * w) * 2 ^ (32 * (2 * w)) % val32 s.mem W (arrAt w 0) (2 * w) =
        val32 s.mem W (arrAt w (arg s 3).toNat) (2 * w) *
          val32 s.mem W (arrAt w (arg s 4).toNat) (2 * w) % val32 s.mem W (arrAt w 0) (2 * w) ∧
      Keeps clob7 (entered s) t := by
  dsimp only
  let w := wOf s.mem (wsOf s)
  have fit : arrAt w 8 ≤ lenOf s := by
    simpa only [lenOf, Nat.mul_comm] using A.layout.2.2.1
  have lay := layout_bounds fit A.left A.right
  have oFit := array_fit fit A.output.1
  have mFit := array_fit fit (j := 0) (by decide)
  have aFit := array_fit fit A.left.1
  have bFit := array_fit fit A.right.1
  have apart := operand_apart (w := w) A.output
  have product := product_fits w
  have acc : Compact.accOff = 24 := rfl
  have width : 0 < w := by have := A.layout.1; dsimp only [w]; omega
  have nowrap : (wsOf s).toNat + lenOf s ≤ 2 ^ 32 := by rw [A.ws_toNat]; exact A.bound
  have n32 : 4 * (2 * w) < 2 ^ 32 := by have := lay.scr; omega
  have mValue := A.pushed_val32 (d := arrAt w 0) (n := 2 * w) (by omega)
  have aValue := A.pushed_val32 (d := arrAt w (arg s 3).toNat) (n := 2 * w) (by omega)
  have bValue := A.pushed_val32 (d := arrAt w (arg s 4).toNat) (n := 2 * w) (by omega)
  have inverse : (val32 (entered s).mem (wsOf s) (arrAt w 0) (2 * w) *
      w32 (entered s).mem (wsOf s) 56 + 1) % 2 ^ 32 = 0 := by
    rw [mValue, A.pushed_w32 (by have := A.headerFit; omega)]
    exact prepared_inverse width A.inverse
  have rightLt : val32 (entered s).mem (wsOf s) (arrAt w (arg s 4).toNat) (2 * w) <
      val32 (entered s).mem (wsOf s) (arrAt w 0) (2 * w) := by
    rw [bValue, mValue]
    have B := A.rightLt
    rw [numAt_val32, numAt_val32] at B
    exact B
  have outHeader : 128 ≤ arrAt w (arg s 2).toNat := by unfold arrAt hdrBytes; omega
  have outMod : arrAt w (arg s 2).toNat = arrAt w 0 ∨
      arrAt w (arg s 2).toNat + 4 * (2 * w) ≤ arrAt w 0 ∨
      arrAt w 0 + 4 * (2 * w) ≤ arrAt w (arg s 2).toNat := by
    by_cases zero : (arg s 2).toNat = 0
    · exact Or.inl (by rw [zero])
    · have := array_mono w (i := 0) (j := (arg s 2).toNat) (by omega)
      exact Or.inr (Or.inr (by omega))
  dsimp only [w] at *
  refine WP.mono (core_ok A.pushed_ws A.pushed_args A.ws_toNat.symm A.metadata lay
    A.output.1 A.output_ptr outHeader outMod (by omega) n32 (by omega) (by omega) inverse rightLt) ?_
  rintro t ⟨O, low, congruence, K⟩
  rw [mValue] at low congruence
  rw [aValue, bValue] at congruence
  exact ⟨O, low, congruence, K⟩

end VG.Proof.Mont.X86.Compact
