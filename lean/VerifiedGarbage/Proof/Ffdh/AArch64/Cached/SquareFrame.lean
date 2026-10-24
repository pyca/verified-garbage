module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeSquares
import VerifiedGarbage.Proof.Framework.Omega

/-! Squaring changes arithmetic arrays and one counter, preserving the context metadata. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum

theorem basisSquareRanges_le (w : Nat) : ∀ r∈basisSquareRanges w,r.1+r.2≤slot w 8 := by
 have s2 := slot_le (w:=w) (by decide : 2<8)
 have s3 := slot_le (w:=w) (by decide : 3<8)
 have s5 := slot_le (w:=w) (by decide : 5<8)
 have s6 := slot_le (w:=w) (by decide : 6<8)
 have counter := hdr_lt_slot w 8 (show sI<32 by decide)
 simp only [basisSquareRanges,squareRanges,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
 rintro _ ((rfl|rfl|rfl|rfl)|rfl) <;> omega

theorem squareFrame_header {B : Addr} {w i : Nat} {m m' : Mem}
 (frame : Frm B (basisSquareRanges w) m m') (inside : i<32) (different : i≠sI) :
 word m' B (8*i)=word m B (8*i) := by
 apply frame.word_eq ?_ (by omega)
 intro r hr
 have s2 := hdr_lt_slot w 2 inside
 have s3 := hdr_lt_slot w 3 inside
 have s5 := hdr_lt_slot w 5 inside
 have s6 := hdr_lt_slot w 6 inside
 simp only [basisSquareRanges,squareRanges,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr
 rcases hr with ((rfl|rfl|rfl|rfl)|rfl) <;> omega

end VG.Proof.Ffdh.AArch64.Cached
