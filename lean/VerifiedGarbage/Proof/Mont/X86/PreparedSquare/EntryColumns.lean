module

public import VerifiedGarbage.Proof.Mont.X86.Compact.Entry


public import VerifiedGarbage.Proof.Mont.X86.Rt.Base

public import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.Narrow
public import VerifiedGarbage.Proof.Mont.X86.Rt.Sub
import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.FrameArgs
public import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.Layout
import VerifiedGarbage.Proof.Mont.X86.Compact.Layout
import VerifiedGarbage.Proof.Mont.X86.Compact.EntryMemory
import VerifiedGarbage.Proof.Mont.X86.Compact.EntryValues
import VerifiedGarbage.Proof.Mont.X86.Compact.Arithmetic
import VerifiedGarbage.Proof.Mont.X86.Square.FinalMath
public import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.Frame
import VerifiedGarbage.Proof.Mont.X86.Compact.Prepared
public import Init.Data.BitVec.BasicAux
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! # The public prepared contract supplies the column loop's read-only cache -/

@[expose] public section
namespace VG.Proof.Mont.X86.PreparedSquare
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Spec.Rsa.Mont hiding Keeps

theorem entry_columns {s t : State} (A : Compact.Entry s) (same : arg s 3 = arg s 4)
    (K : Keeps clob7 s t)
    (O : Outside (Compact.wsOf s) (arrAt (wOf s.mem (Compact.wsOf s)) 2) 16 s.mem t.mem)
    (eax : t.gpr .eax = arg s 0)
    (ebx : t.gpr .ebx = s.mem.readW (off (Compact.wsOf s) 48) 32)
    (esi : t.gpr .esi = arg s 0 + BitVec.ofNat 32 (arrAt (wOf s.mem (Compact.wsOf s)) (arg s 3).toNat))
    (ebp : t.gpr .ebp = arg s 0 + BitVec.ofNat 32 256)
    (edi : PtrAt t (Compact.wsOf s) .edi (arrAt (wOf s.mem (Compact.wsOf s)) 2)) :
    let W := Compact.wsOf s
    let w := wOf s.mem W
    let S := arrAt w 2
    let o := arrAt w (arg s 2).toNat
    let a := arrAt w (arg s 3).toNat
    ColumnReady (entered t) W (Compact.lenOf s) (2 * w) S o a
      (cacheValues (arg s) (s.mem.readW (off W 48) 32) S o a) := by
  dsimp only
  let W := Compact.wsOf s
  let w := wOf s.mem W
  let S := arrAt w 2
  let o := arrAt w (arg s 2).toNat
  let a := arrAt w (arg s 3).toNat
  change Outside W S 16 s.mem t.mem at O
  have fit : arrAt w 8 ≤ Compact.lenOf s := by
    simpa only [Compact.lenOf, Nat.mul_comm] using A.layout.2.2.1
  have lay := layout_bounds fit A.left
  have outFit := Compact.array_fit fit A.output.1
  have aFit := Compact.array_fit fit A.left.1
  have apart := Compact.operand_apart (w := w) A.left
  have outApart := Compact.operand_apart (w := w) A.output
  have bound : W.toNat + Compact.lenOf s ≤ 2 ^ 32 := by rw [A.ws_toNat]; exact A.bound
  have modulus : arrAt w 0 = 256 := by simp [arrAt, hdrBytes]
  have header : 128 ≤ S := by unfold S arrAt hdrBytes; omega
  have scratch : S + 8 * (2 * w) + 32 = arrAt w 4 := by unfold S arrAt hdrBytes; omega
  have width : 0 < w := by have := A.layout.1; dsimp only [w, W]; omega
  have Oall : Outs W [(0, Compact.lenOf s)] s.mem t.mem :=
    Outs.of_outside (O.mono (o' := 0) (n' := Compact.lenOf s) (by omega) (by have := lay.scr; omega)) (by simp)
  have args := original_args A K (by decide) ((raw_args A).of_keeps K (by decide) Oall)
  have hw := entered_ws ((raw_ws A).of_keeps K)
  have read (d : Nat) (h : d + 4 ≤ Compact.lenOf s) (sep : d + 4 ≤ S ∨ S + 16 ≤ d) :
      w32 (entered t).mem W d = w32 s.mem W d := by
    rw [entered_w32 A K (by decide) h]
    exact O.w32 sep (by omega)
  have val (d : Nat) (h : d + 4 * (2 * w) ≤ Compact.lenOf s)
      (sep : d + 4 * (2 * w) ≤ S ∨ S + 16 ≤ d) :
      val32 (entered t).mem W d (2 * w) = val32 s.mem W d (2 * w) := by
    rw [entered_val32 A K (by decide) h]
    exact O.val32 sep (by omega)
  have mVal := val 256 lay.mo_le (by have := lay.smo; omega)
  have aVal := val a lay.a_le (by have := lay.sa; omega)
  have metadata := Compact.layout_metadata (A := arg s) A.layout A.left.1 A.right.1
  rw [same] at metadata
  rw [← same] at metadata
  have prepared : Compact.Metadata (entered t).mem W (arg s) (2 * w) S 256 a a := by
    have M := entered_metadata A K (by decide) (metadata.keep O header)
    change Compact.Metadata (entered t).mem W (arg s) (2 * w) S (arrAt w 0) a a at M
    rwa [modulus] at M
  let C := cacheValues (arg s) (s.mem.readW (off W 48) 32) S o a
  have values : ArgVals C W (2 * w) S 256 56 o a a :=
    cacheValues_ok A.ws_toNat.symm metadata.width (by have := lay.scr; omega)
      (by omega) (by omega)
  have cached : Args (entered t) W (Compact.lenOf s) C :=
    entered_args (by rw [K.1 .esp (by decide)]; exact A.stackFit)
      (by rw [K.1 .esp (by decide)]; exact A.savedSeparate') eax ebx ebp esi rfl rfl
  have edient : PtrAt (entered t) W .edi S := by rw [PtrAt, entered, pushed_gpr _ _ (by decide)]; exact edi
  have inv : (val32 (entered t).mem W 256 (2 * w) * w32 (entered t).mem W 56 + 1) % 2 ^ 32 = 0 := by
    rw [mVal, read 56 (by have := A.headerFit; omega) (by omega)]
    have H := Compact.prepared_inverse width A.inverse
    change (val32 s.mem W (arrAt w 0) (2 * w) * w32 s.mem W 56 + 1) % 2 ^ 32 = 0 at H
    rwa [modulus] at H
  have small : val32 (entered t).mem W a (2 * w) < val32 (entered t).mem W 256 (2 * w) := by
    rw [aVal, mVal]
    have H := A.rightLt
    rw [← same, Compact.numAt_val32, Compact.numAt_val32] at H
    change val32 s.mem W a (2 * w) < val32 s.mem W (arrAt w 0) (2 * w) at H
    rwa [modulus] at H
  refine ⟨cached, hw, values, lay, ?_, edient, ?_, small, ?_, ?_, ?_⟩
  · change 0 < 2 * w
    omega
  · exact VG.Proof.Mont.X86.Square.low_inverse (entered t).mem W 256 56 (by omega) inv
  · change (entered t).wr = [cacheRegion (entered t), ⟨W, Compact.lenOf s⟩]
    rw [entered, pushed_wr, K.2.2, A.wr]
    congr 1
    exact entered_region t
  · exact entered_fit (by rw [K.1 .esp (by decide)]; exact A.stackFit)
  · change (⟨((entered t).gpr .esp).setWidth 64, 16⟩ : Region).Disjoint ⟨W, Compact.lenOf s⟩
    rw [← entered_region, K.1 .esp (by decide)]
    exact A.savedSeparate'

end VG.Proof.Mont.X86.PreparedSquare
