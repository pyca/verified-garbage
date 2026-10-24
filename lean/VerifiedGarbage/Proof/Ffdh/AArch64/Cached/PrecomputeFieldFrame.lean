module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeField
public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Layout
import VerifiedGarbage.Proof.Framework.Omega

/-! Modulus setup preserves the cached-generation controls in the upper header. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum
open VG.Impl.Bignum.Public

theorem precomputeField_header {B : Addr} {w i : Nat} {m m' : Mem}
 (frame : Frm B (pcLoadRanges w++r2Ranges w) m m')
 (lower : 16≤i) (upper : i<32) (counter : i≠sCnt) :
 word m' B (8*i)=word m B (8*i) := by
 apply frame.word_eq _ (by omega)
 intro r hr
 have belowN := hdr_lt_slot w aN upper
 have belowAcc := hdr_lt_slot w aAcc upper
 have belowTmp := hdr_lt_slot w aTmp upper
 have belowR2 := hdr_lt_slot w aR2 upper
 simp only [List.mem_append,pcLoadRanges,r2Ranges,List.mem_cons,List.not_mem_nil,or_false] at hr
 rcases hr with (rfl|rfl|rfl|rfl) | (rfl|rfl|rfl|rfl)
 all_goals simp only [sW,sArr,sMinv] at *
 all_goals omega

theorem precomputeField_inscr {B : Addr} {w Z : Nat} {m m' : Mem}
 (frame : Frm B (pcLoadRanges w++r2Ranges w) m m') (room : slot w 8≤Z) : InScr B Z m m' := by
 intro x hx
 apply frame x
 intro r hr
 have inside : r.1+r.2≤slot w 8 := by
  rcases List.mem_append.mp hr with load | square
  · exact pcLoadRanges_le w r load
  · have two := slot_le (w:=w) (show Public.aAcc<8 by decide)
    have three := slot_le (w:=w) (show Public.aTmp<8 by decide)
    have four := slot_le (w:=w) (show Public.aR2<8 by decide)
    have count := hdr_lt_slot w 8 (show sCnt<32 by decide)
    simp only [r2Ranges,List.mem_cons,List.not_mem_nil,or_false] at square
    rcases square with rfl|rfl|rfl|rfl <;> omega
 exact Or.inr (by omega)

end VG.Proof.Ffdh.AArch64.Cached
