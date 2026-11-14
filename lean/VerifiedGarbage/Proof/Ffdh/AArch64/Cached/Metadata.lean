module

public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Policy
public import VerifiedGarbage.Spec.Rsa.FixedBaseComb
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.BitMath
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Layout
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.Bignum.AArch64.Run

/-! ### `Ffdh.AArch64.Cached.MetadataRows`, which only this module used -/

section

/-! The public subtraction loop computes exactly ceil(N/5). -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

theorem metadataRowStep (s : State) {L j : Nat} (positive : 5≤L) (fit : L<2^63)
 (remaining : s.gpr .x12=BitVec.ofNat 64 L) (count : s.gpr .x13=BitVec.ofNat 64 j) :
 WP isa (.block Policy.rowStep) s fun t =>
 (t.gpr .x12=BitVec.ofNat 64 (L-5) ∧ t.gpr .x13=BitVec.ofNat 64 (j+1) ∧
 t.gpr .x14=(if L-5<5 then 1#64 else 0#64) ∧ t.mem=s.mem) ∧ Keep [.x12,.x13,.x14] s t := by
 have sub : BitVec.ofNat 64 L-5#64=BitVec.ofNat 64 (L-5) :=
  BitVec.ofNat_sub_ofNat_of_le L 5 (by decide) positive
 refine WP.keep [.x12,.x13,.x14] ?_ rfl rfl rfl
 unfold Policy.rowStep
 brun [remaining,count,sub,sign_sub (a:=L-5) (b:=5) (by omega_using [fit]) (by decide)]
 constructor
 · exact (BitVec.ofNat_add _ _).symm
 · change ((BitVec.ofNat 64 (L-5)+ ~~~5#64+1#64) >>> 63)=_
   rw [BitVec.add_assoc,←BitVec.neg_eq_not_add,←BitVec.sub_eq_add_neg]
   exact sign_sub (by omega_using [fit]) (by decide)

theorem metadataRows_ok (s : State) {N : Nat} (positive : 0<N) (bound : N≤8192)
 (remaining : s.gpr .x12=BitVec.ofNat 64 (N+4)) (count : s.gpr .x13=0#64) :
 WP isa (.loop (.block Policy.rowStep) (.zero .x .x14)) s fun t =>
 t.gpr .x13=BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows N) ∧ t.mem=s.mem ∧ Keep [.x12,.x13,.x14] s t := by
 let d := (N+4)/5
 have dPositive : 0<d := by dsimp [d];omega_using [positive]
 let I := fun n t => ∃ j, n=d-j ∧ j<d ∧
  t.gpr .x12=BitVec.ofNat 64 (N+4-5*j) ∧ t.gpr .x13=BitVec.ofNat 64 j ∧
  t.mem=s.mem ∧ Keep [.x12,.x13,.x14] s t
 refine WP.loop (M:=isa) I ?_ d s ?_
 · intro n t h
   obtain ⟨j,rem,hj,left,countT,mem,keep⟩ := h
   have enough : 5≤N+4-5*j := by dsimp [d] at hj;omega_using [hj]
   refine WP.mono (metadataRowStep t enough (by omega_using [bound]) left countT) ?_
   rintro u ⟨⟨leftU,countU,flagU,memU⟩,keepU⟩
   have same : N+4-5*j-5=N+4-5*(j+1) := by omega_using []
   have flag : (N+4-5*j-5<5) ↔ ¬j+1<d := by dsimp [d];omega_using []
   by_cases more : j+1<d
   · right
     refine ⟨?_,d-(j+1),by omega_using [rem, hj],j+1,rfl,more,?_,countU,memU.trans mem,(keep.trans keepU).mono (by decide)⟩
     · rw [eval_zero,flagU,ite_eq_right (by rw [flag];exact not_not_intro more)]
       decide
     · rw [leftU,same]
   · left
     have last : j+1=d := by omega_using [hj, more]
     refine ⟨?_,?_,memU.trans mem,(keep.trans keepU).mono (by decide)⟩
     · rw [eval_zero,flagU,ite_eq_left (flag.mpr more)]
       decide
     · rw [countU,last]
       rfl
 · refine ⟨0,by omega_using [],dPositive,?_,count,rfl,Keep.refl _ _⟩
   simpa using remaining

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! Exact serialization of the reviewed sampling width and comb row count. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/MetadataHead.lean`, which only this module imported.
section

/-! Public scalar width metadata is computed without assuming initialized arithmetic arrays. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem metadataHead_ok {s : State} {B : Addr} {Z N : Nat}
 (scratch : Scr s B Z) (room : 256≤Z) (base : s.gpr .x0=B) (bound : N≤8192)
 (bits : word s.mem B (8*sBits)=BitVec.ofNat 64 N) :
 WP isa (.block Policy.metadataHead) s fun t =>
 (t.gpr .x10=BitVec.ofNat 64 N ∧ t.gpr .x11=BitVec.ofNat 64 ((N+7)/8) ∧
 t.gpr .x12=BitVec.ofNat 64 (N+4) ∧ t.gpr .x13=0#64 ∧
 t.mem=s.mem.writeW (off B (8*sBytes)) (BitVec.ofNat 64 ((N+7)/8))) ∧
 Keep [.x10,.x11,.x12,.x13] s t := by
 have shift : (BitVec.ofNat 64 N+7#64) >>> 3=BitVec.ofNat 64 ((N+7)/8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight,BitVec.toNat_add,BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow]
  omega_using [bound]
 refine WP.keep [.x10,.x11,.x12,.x13] ?_ rfl rfl rfl
 unfold Policy.metadataHead
 brun [base,hdr_enc (show sBits<32 by decide),hdr_enc (show sBytes<32 by decide),
  scratch.ld (d:=8*sBits) (by unfold sBits;omega_using [room]),scratch.st (d:=8*sBytes) (by unfold sBytes;omega_using [room]),bits,shift]
 exact (BitVec.ofNat_add _ _).symm

end VG.Proof.Ffdh.AArch64.Cached
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/MetadataTail.lean`, which only this module imported.
section

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
  scratch.ld (d:=8*sCtx) (by unfold sCtx;omega_using [room]),scratch.st (d:=8*sRows) (by unfold sRows;omega_using [room]),
  pointer,bits,width,count,
  (show InRegions s.wr ctx 8 by simpa [off] using output.st (d:=0) (by decide)),output.st (d:=8) (by decide),output.st (d:=16) (by decide)]

end VG.Proof.Ffdh.AArch64.Cached
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def metadataMemory (m : Mem) (B ctx : Addr) (N : Nat) : Mem :=
 let m1 := m.writeW (off B (8*sBytes)) (BitVec.ofNat 64 ((N+7)/8))
 let m2 := m1.writeW (off B (8*sRows)) (BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows N))
 ((m2.writeW ctx (BitVec.ofNat 64 N)).writeW (off ctx 8) (BitVec.ofNat 64 ((N+7)/8))).writeW
  (off ctx 16) (BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows N))

theorem metadata_ok {s : State} {B ctx : Addr} {Z N : Nat}
 (scratch : Scr s B Z) (room : 256≤Z) (output : Scr s ctx 24)
 (base : s.gpr .x0=B) (context : word s.mem B (8*sCtx)=ctx)
 (bits : word s.mem B (8*sBits)=BitVec.ofNat 64 N) (positive : 0<N) (bound : N≤8192) :
 WP isa Policy.metadata s fun t => t.mem=metadataMemory s.mem B ctx N ∧
 Keep [.x8,.x10,.x11,.x12,.x13,.x14] s t := by
 unfold Policy.metadata
 rw [WP.seq_iff]
 refine WP.mono (metadataHead_ok scratch room base bound bits) ?_
 rintro u ⟨⟨bitsU,widthU,leftU,countU,memU⟩,restU⟩
 rw [WP.seq_iff]
 refine WP.mono (metadataRows_ok u positive bound leftU countU) ?_
 rintro v ⟨countV,memV,restV⟩
 have rest := restU.trans restV
 have frame : Outside B (8*sBytes) 8 s.mem u.mem := by
  rw [memU];exact writeW_outside _ _ _ (by decide)
 have ctxV : word v.mem B (8*sCtx)=ctx := by
  rw [memV]
  exact (frame.word (Or.inl (by decide : 8*sCtx+8≤8*sBytes)) (by decide)).trans context
 refine WP.mono (metadataTail_ok (scratch.congr rest.wr) room (output.congr rest.wr)
  ((rest.gpr .x0 (by decide)).trans base) ctxV
  ((restV.gpr .x10 (by decide)).trans bitsU) ((restV.gpr .x11 (by decide)).trans widthU) countV) ?_
 rintro t ⟨memT,restT⟩
 refine ⟨?_,(rest.trans restT).mono (by decide)⟩
 rw [memV,memU] at memT
 exact memT

end VG.Proof.Ffdh.AArch64.Cached
