module

public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Precompute
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Header
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! Advance the public subset index and compare it with the next tooth's table index. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem productCounter_ok {s : State} {B : Addr} {Z w j d : Nat} {mi : BitVec 64}
 (good : Good s B Z w mi) (room : slot w 8≤Z)
 (index : word s.mem B (8*sJ)=BitVec.ofNat 64 j) (basis : word s.mem B (8*sD)=BitVec.ofNat 64 d) :
 WP isa (.block Precompute.productNext) s fun t =>
 Good t B Z w mi ∧ word t.mem B (8*sJ)=BitVec.ofNat 64 (j+1) ∧
 t.gpr .x3=BitVec.ofNat 64 (j+1)-BitVec.ofNat 64 d ∧
 Outside B (8*sJ) 8 s.mem t.mem ∧ Keep [.x3,.x4] s t := by
 have increment : BitVec.ofNat 64 j+1#64=BitVec.ofNat 64 (j+1) := (BitVec.ofNat_add _ _).symm
 have frame : Outside B (8*sJ) 8 s.mem (s.mem.writeW (off B (8*sJ)) (BitVec.ofNat 64 (j+1))) :=
  writeW_outside _ _ _ (by decide)
 have basisAfter : word (s.mem.writeW (off B (8*sJ)) (BitVec.ofNat 64 (j+1))) B (8*sD)=BitVec.ofNat 64 d :=
  (frame.word (Or.inl (by decide : 8*sD+8≤8*sJ)) (by decide)).trans basis
 refine WP.mono (WP.keep [.x3,.x4] (Q:=fun t =>
  t.gpr .x3=BitVec.ofNat 64 (j+1)-BitVec.ofNat 64 d ∧
  t.mem=s.mem.writeW (off B (8*sJ)) (BitVec.ofNat 64 (j+1))) ?_ rfl rfl rfl) ?_
 · unfold Precompute.productNext
   brun [good.x0,hdr_enc (show sJ<32 by decide),hdr_enc (show sD<32 by decide),
    header_read good room (show sJ<32 by decide),header_read good room (show sD<32 by decide),
    good.scr.st (d:=8*sJ) (by have := hdr_lt_slot w 8 (show sJ<32 by decide);omega),index,basisAfter,increment]
 · rintro t ⟨⟨value,mem⟩,rest⟩
   have totalFrame : Outside B (8*sJ) 8 s.mem t.mem := by rw [mem];exact frame
   refine ⟨good_after_header good (by decide) (by decide) totalFrame rest ((rest.gpr .x0 (by decide)).trans good.x0),
    ?_,value,totalFrame,rest⟩
   rw [mem,word_writeW_self]

end VG.Proof.Ffdh.AArch64.Cached
