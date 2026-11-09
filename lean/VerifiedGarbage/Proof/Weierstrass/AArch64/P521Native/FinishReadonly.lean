module

-- separate module: table and scalar-bit preservation are memory-frame lemmas independent of point and group semantics

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowLookupPoint
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.NormalizeLayout
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishDoubles
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! Shared public table and scalar bits remain immutable through final arithmetic. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass

 theorem finish_double_frame_unch {base : Addr} {m m' : Mem} (h : WindowWorkFrame base m m') :
    Unch base [(1072,432),(4080,504)] m m' := by
  intro x hx
  exact h x (hx (1072,432) (by simp)) (hx (4080,504) (by simp))

 theorem finish_table_canonical_keep {base table : Addr} {m m' : Mem} {W : List (Nat × Nat)}
    (apart : TableWorkspaceApart base table 8192) (frame : Unch base W m m')
    (fits : ∀w∈W,w.1+w.2≤8192) (old : WindowTableCanonical m table) :
    WindowTableCanonical m' table := by
  have outside : Outside base 0 8192 m m' := frame.outside fun w hw => ⟨Nat.zero_le _,fits w hw⟩
  intro d lo hi
  rw [apart.wordsVal outside 9 (lookupEntryOffset d) (by unfold lookupEntryOffset; omega_arith),
    apart.wordsVal outside 9 (lookupEntryOffset d+72) (by unfold lookupEntryOffset; omega_arith)]
  exact old d lo hi

 theorem finish_affine_keep {base table : Addr} {m m' : Mem} {W : List (Nat × Nat)}
    (apart : TableWorkspaceApart base table 8192) (frame : Unch base W m m')
    (fits : ∀w∈W,w.1+w.2≤8192) (k j : Nat) :
    windowAffine m' table k j=windowAffine m table k j := by
  have outside : Outside base 0 8192 m m' := frame.outside fun w hw => ⟨Nat.zero_le _,fits w hw⟩
  have digit := magH_le (H:=16) (combWin_lt 5 k j)
  have xSame : windowX m' table (magH 16 (combWin 5 k j))=windowX m table (magH 16 (combWin 5 k j)) := by
    simp only [windowX]
    split
    · rfl
    · rw [apart.wordsVal outside 9 _ (by unfold lookupEntryOffset; omega_arith)]
  have ySame : windowY m' table (magH 16 (combWin 5 k j))=windowY m table (magH 16 (combWin 5 k j)) := by
    simp only [windowY]
    split
    · rfl
    · rw [apart.wordsVal outside 9 _ (by unfold lookupEntryOffset; omega_arith)]
  simp only [windowAffine,xSame,ySame]

 theorem finish_bits_keep {base : Addr} {m m' : Mem} {W : List (Nat × Nat)} {k : Nat}
    (frame : Unch base W m m') (apart : ∀w∈W,w.1+w.2≤3304 ∨ 3829≤w.1)
    (bits : ∀i<525,m (off base (3304+i))=if k.testBit i then 1 else 0) :
    ∀i<525,m' (off base (3304+i))=if k.testBit i then 1 else 0 := by
  intro i hi
  rw [frame _ (by
    intro w hw
    rw [ofs_off0 base (by omega_arith)]
    have bounds := apart w hw
    omega_arith)]
  exact bits i hi

end VG.Proof.Weierstrass.AArch64.P521Native
