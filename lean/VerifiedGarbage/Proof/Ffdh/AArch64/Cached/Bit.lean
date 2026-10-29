module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.BitLoad
public import VerifiedGarbage.Proof.Ffdh.CombBitBytes
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-! Exact scalar bit extraction, including the public zero padding above N. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero eval_nonzero)
open VG.Proof.Bignum.AArch64

structure Source (src : Addr) (bs : List Byte) (s : State) : Prop where
 readable : ∀ i<bs.length, InRegions (s.rd++s.wr) (src+BitVec.ofNat 64 i) 1
 bytes : ∀ i<bs.length, s.mem (src+BitVec.ofNat 64 i)=bs.getD i 0

theorem Source.of_mem {src : Addr} {bs : List Byte} {s t : State} {rs : List Reg}
 (h : Source src bs s) (mem : t.mem=s.mem) (rest : Keep rs s t) : Source src bs t := by
 constructor
 · intro i hi; rw [rest.rd,rest.wr]; exact h.readable i hi
 · intro i hi; rw [mem]; exact h.bytes i hi

def bitValue (bs : List Byte) (N k : Nat) : Nat :=
 if k<N then (bs.getD (bs.length-1-k/8) 0).toNat / 2^(k%8) % 2 else 0

theorem bitValue_lt (bs : List Byte) (N k : Nat) : bitValue bs N k<2 := by
 unfold bitValue
 split <;> omega

private theorem guard_ok (s : State) {k N : Nat} (hk : k<2^63) (hN : N<2^63)
 (index : s.gpr .x9=BitVec.ofNat 64 k) (width : s.gpr .x5=BitVec.ofNat 64 N) :
 WP isa (.block [.sub .x .x8 .x9 .x5,.lsr .x .x8 .x8 63]) s fun t =>
 (t.gpr .x8=(if k<N then 1#64 else 0#64) ∧ t.mem=s.mem) ∧ Keep [.x8] s t := by
 refine WP.keep [.x8] ?_ rfl rfl rfl
 brun [index,width,sign_sub hk hN]

private theorem optionalShift_ok (s : State) {r : Nat} (bound : r<8)
 (count : s.gpr .x10=BitVec.ofNat 64 r) :
 WP isa (.ite (.zero .x .x10) (.block []) VG.Impl.Ffdh.AArch64.Cached.Comb.shift) s fun t =>
 t.gpr .x11=s.gpr .x11>>>r ∧ t.mem=s.mem ∧ Keep [.x10,.x11] s t := by
 by_cases zero : r=0
 · subst r
   refine ⟨_,s,.iteT ?_ (.block rfl),by simp,rfl,Keep.refl _ _⟩
   rw [eval_zero,count]
   decide
 · obtain ⟨tr,t,run,word,_,mem,rest⟩ := shift_ok s (by omega) (by omega) count
   refine ⟨_,t,.iteF ?_ run,word,mem,rest⟩
   rw [eval_zero,count]
   have ne : BitVec.ofNat 64 r ≠ 0#64 := by
    intro eq
    have h := congrArg BitVec.toNat eq
    change r%2^64=0 at h
    rw [Nat.mod_eq_of_lt (by omega)] at h
    omega
   simp [ne]

private theorem maskedBit (b : Byte) {r : Nat} (hr : r<8) :
 (BitVec.ofNat 64 b.toNat >>> r) &&& 1#64 = BitVec.ofNat 64 (b.toNat/2^r%2) := by
 apply BitVec.eq_of_toNat_eq
 rw [byte_bit b r hr,BitVec.toNat_ofNat]
 exact (Nat.mod_eq_of_lt (by omega : b.toNat/2^r%2<2^64)).symm

theorem bit_ok (s : State) {src : Addr} {bs : List Byte} {k N : Nat}
 (source : Source src bs s) (size : bs.length<2^31) (widthBound : N≤8*bs.length)
 (indexFit : k<2^63)
 (ptr : s.gpr .x1=src) (length : s.gpr .x2=BitVec.ofNat 64 bs.length)
 (index : s.gpr .x9=BitVec.ofNat 64 k) (width : s.gpr .x5=BitVec.ofNat 64 N) :
 WP isa VG.Impl.Ffdh.AArch64.Cached.Comb.bit s fun t =>
 t.gpr .x11=BitVec.ofNat 64 (bitValue bs N k) ∧ t.mem=s.mem ∧ Keep [.x8,.x10,.x11] s t := by
 unfold VG.Impl.Ffdh.AArch64.Cached.Comb.bit
 rw [WP.seq_iff]
 refine WP.mono (guard_ok s indexFit (by omega) index width) ?_
 rintro u ⟨⟨flag,memU⟩,restU⟩
 by_cases inside : k<N
 · apply WP.ite true (by rw [eval_nonzero,flag,ite_eq_left inside]; decide)
   · intro _
     rw [WP.seq_iff]
     have pos : bs.length-1-k/8<bs.length := by omega
     refine WP.mono (load_ok u (b:=bs.getD (bs.length-1-k/8) 0) size (by omega)
      ((restU.gpr .x1 (by decide)).trans ptr) ((restU.gpr .x2 (by decide)).trans length)
      ((restU.gpr .x9 (by decide)).trans index)
      (by rw [restU.rd,restU.wr]; exact source.readable _ pos)
      (by rw [memU]; exact source.bytes _ pos)) ?_
     rintro v ⟨⟨byte,count,memV⟩,restV⟩
     rw [WP.seq_iff]
     refine WP.mono (optionalShift_ok v (by omega) count) ?_
     rintro z ⟨shifted,memZ,restZ⟩
     refine WP.mono (WP.keep [.x10,.x11] (Q:=fun t =>
      t.gpr .x11=BitVec.ofNat 64 (bitValue bs N k) ∧ t.mem=z.mem)
      ?_ rfl rfl rfl) ?_
     · brun [shifted,byte,bitValue,inside]
       exact maskedBit _ (Nat.mod_lt k (by decide))
     · rintro t ⟨⟨word,mem⟩,rest⟩
       exact ⟨word,mem.trans (memZ.trans (memV.trans memU)),
        (((restU.trans restV).trans restZ).trans rest).mono (by decide)⟩
   · intro impossible; cases impossible
 · apply WP.ite false (by rw [eval_nonzero,flag,ite_eq_right inside]; decide)
   · intro impossible; cases impossible
   · intro _
     refine WP.mono (WP.keep [.x11] (Q:=fun t =>
      t.gpr .x11=BitVec.ofNat 64 (bitValue bs N k) ∧ t.mem=u.mem) ?_ rfl rfl rfl) ?_
     · brun [bitValue,inside]
     · rintro t ⟨⟨word,mem⟩,rest⟩
       exact ⟨word,mem.trans memU,(restU.trans rest).mono (by decide)⟩

end VG.Proof.Ffdh.AArch64.Cached
