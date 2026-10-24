module

public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Comb
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Mem

/-! Each masked table word reads both operands, stores only the destination,
and advances both pointers by eight. The mask is never used as an address. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum.AArch64

theorem selectWord_ok (s : State) {src dst : Addr} {mask : BitVec 64}
 (source : s.gpr .x9=src) (output : s.gpr .x8=dst) (choose : s.gpr .x6=mask)
 (readSource : InRegions (s.rd++s.wr) src 8) (readOutput : InRegions (s.rd++s.wr) dst 8)
 (writeOutput : InRegions s.wr dst 8) :
 WP isa (.block VG.Impl.Ffdh.AArch64.Cached.Comb.selectWord) s fun t =>
 (t.mem=s.mem.writeW dst (s.mem.readW dst 64 ||| (s.mem.readW src 64 &&& mask)) ∧
 t.gpr .x9=src+8#64 ∧ t.gpr .x8=dst+8#64) ∧ Keep [.x3,.x4,.x8,.x9] s t := by
 unfold VG.Impl.Ffdh.AArch64.Cached.Comb.selectWord
 refine WP.keep [.x3,.x4,.x8,.x9] ?_ rfl rfl rfl
 brun [source,output,choose,readSource,readOutput,writeOutput]

/-- The OR accumulator either retains a prior selected row or inserts the
unique current match; at most one of the 32 rows can match. -/
theorem selectWord_value (old row : BitVec 64) (selected : Prop) [Decidable selected] :
 old ||| (row &&& (if selected then BitVec.allOnes 64 else 0#64)) =
 if selected then old ||| row else old := by
 split_ifs
 · rw [BitVec.and_allOnes]
 · rw [BitVec.and_zero,BitVec.or_zero]

end VG.Proof.Ffdh.AArch64.Cached
