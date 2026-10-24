module

public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Policy
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Header
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-! Serialize the public metadata into the immutable canonical context. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem metadataTail_ok {s : State} {B ctx : Addr} {Z N bytes rows : Nat}
 (scratch : Scr s B Z) (room : 256≤Z) (output : Scr s ctx 24)
 (base : s.gpr .x0=B) (context : word s.mem B (8*sCtx)=ctx)
 (bits : s.gpr .x10=BitVec.ofNat 64 N) (width : s.gpr .x11=BitVec.ofNat 64 bytes)
 (count : s.gpr .x13=BitVec.ofNat 64 rows) :
 WP isa (.block Policy.metadataTail) s fun t =>
 t.mem=(((s.mem.writeW (off B (8*sRows)) (BitVec.ofNat 64 rows)).writeW
  ctx (BitVec.ofNat 64 N)).writeW (off ctx 8) (BitVec.ofNat 64 bytes)).writeW
  (off ctx 16) (BitVec.ofNat 64 rows) ∧ Keep [.x8] s t := by
 have frame : Outside B (8*sRows) 8 s.mem (s.mem.writeW (off B (8*sRows)) (BitVec.ofNat 64 rows)) :=
  writeW_outside _ _ _ (by decide)
 have pointer : word (s.mem.writeW (off B (8*sRows)) (BitVec.ofNat 64 rows)) B (8*sCtx)=ctx :=
  (frame.word (Or.inl (by decide : 8*sCtx+8≤8*sRows)) (by decide)).trans context
 refine WP.keep [.x8] ?_ rfl rfl rfl
 unfold Policy.metadataTail
 brun [base,hdr_enc (show sRows<32 by decide),hdr_enc (show sCtx<32 by decide),
  scratch.ld (d:=8*sCtx) (by unfold sCtx;omega),scratch.st (d:=8*sRows) (by unfold sRows;omega),
  pointer,bits,width,count,
  (show InRegions s.wr ctx 8 by simpa [off] using output.st (d:=0) (by decide)),output.st (d:=8) (by decide),output.st (d:=16) (by decide)]

end VG.Proof.Ffdh.AArch64.Cached
