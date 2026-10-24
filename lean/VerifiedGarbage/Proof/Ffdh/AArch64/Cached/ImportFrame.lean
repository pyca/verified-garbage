module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.ImportPrefix
import VerifiedGarbage.Proof.Framework.Omega

/-! Native context import preserves all cached API controls in the upper header. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum

theorem importRanges_le (w : Nat) : ∀ r∈importRanges w,r.1+r.2≤slot w 8 := by
 simp only [importRanges,importDataRanges,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
 rintro _ ((rfl|rfl)|(rfl|rfl|rfl))
 all_goals dsimp only [sW,sArr,sMinv,slot,hdrBytes];omega

theorem importFrame_header {B : Addr} {w i : Nat} {m m' : Mem}
 (frame : Frm B (importRanges w) m m') (lower : 16≤i) (upper : i<32) :
 word m' B (8*i)=word m B (8*i) := by
 apply frame.word_eq _ (by omega)
 simp only [importRanges,importDataRanges,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
 rintro _ ((rfl|rfl)|(rfl|rfl|rfl))
 all_goals dsimp only [sW,sArr,sMinv,slot,hdrBytes];omega

end VG.Proof.Ffdh.AArch64.Cached
