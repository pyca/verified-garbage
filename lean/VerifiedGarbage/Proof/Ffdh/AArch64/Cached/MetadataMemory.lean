module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Metadata
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PublicFrame
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! The metadata writer produces exactly the three reviewed header words. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum

theorem threeHeaderWords (m : Mem) (a : Addr) (N bytes rows : Nat) :
 Spec.Rsa.wordsAt (((m.writeW (off a 0) (BitVec.ofNat 64 N)).writeW
  (off a 8) (BitVec.ofNat 64 bytes)).writeW (off a 16) (BitVec.ofNat 64 rows)) a 3=
 [BitVec.ofNat 64 N,BitVec.ofNat 64 bytes,BitVec.ofNat 64 rows] := by
 change [_,_,_]=_
 dsimp only
 rw [List.cons.injEq]
 constructor
 · rw [Mem.readW_writeW_sep (Offset.sep a (by decide) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_sep (Offset.sep a (by decide) (by decide) (by decide)) (by decide)]
   exact Mem.readW_writeW_self64 _ _ _
 · rw [List.cons.injEq]
   constructor
   · rw [Mem.readW_writeW_sep (Offset.sep a (by decide) (by decide) (by decide)) (by decide)]
     exact Mem.readW_writeW_self64 _ _ _
   · exact congrArg (fun x => [x]) (Mem.readW_writeW_self64 _ _ _)

theorem metadataMemory_header (m : Mem) (B ctx : Addr) (N : Nat) :
 Spec.Rsa.wordsAt (metadataMemory m B ctx N) ctx 3=
 [BitVec.ofNat 64 N,BitVec.ofNat 64 ((N+7)/8),BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows N)] := by
 simpa only [metadataMemory,off,BitVec.add_zero] using
  threeHeaderWords ((m.writeW (off B (8*sBytes)) (BitVec.ofNat 64 ((N+7)/8))).writeW
   (off B (8*sRows)) (BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows N))) ctx N ((N+7)/8) (Spec.Rsa.FixedBaseComb.rows N)

theorem metadataMemory_frame (m : Mem) (p : Parameters) (N : Nat) : PublicFrame p m (metadataMemory m p.B p.ctx N) := by
 have bytes := (Frame.refl (publicWrites p) m).writeW (r:=⟨p.B,p.Z⟩) (b:=off p.B (8*sBytes)) (by simp [publicWrites])
  (BitVec.ofNat 64 ((N+7)/8)) (Offset.contains_base _ (by have := p.room;have := VG.Proof.Bignum.hdr_lt_slot p.w 8 (show sBytes<32 by decide);omega) (by decide))
 have rows := bytes.writeW (r:=⟨p.B,p.Z⟩) (b:=off p.B (8*sRows)) (by simp [publicWrites])
  (BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows N)) (Offset.contains_base _ (by have := p.room;have := VG.Proof.Bignum.hdr_lt_slot p.w 8 (show sRows<32 by decide);omega) (by decide))
 have bitHeader := rows.writeW (r:=⟨p.ctx,8*(3+34*p.w)⟩) (b:=p.ctx) (by simp [publicWrites])
  (BitVec.ofNat 64 N) (by change (p.ctx-p.ctx).toNat+8≤8*(3+34*p.w);simp;omega)
 have byteHeader := bitHeader.writeW (r:=⟨p.ctx,8*(3+34*p.w)⟩) (b:=off p.ctx 8) (by simp [publicWrites])
  (BitVec.ofNat 64 ((N+7)/8)) (Offset.contains_base _ (by omega) (by decide))
 exact byteHeader.writeW (r:=⟨p.ctx,8*(3+34*p.w)⟩) (b:=off p.ctx 16) (by simp [publicWrites])
  (BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows N)) (Offset.contains_base _ (by omega) (by decide))

end VG.Proof.Ffdh.AArch64.Cached
