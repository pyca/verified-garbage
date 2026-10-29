module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.BitMath
public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Comb
public import VerifiedGarbage.Proof.Bignum.AArch64.Run

import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Omega
/-! A public bit index reads a big-endian scalar byte at a bounded address. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/Shift.lean`, which only this module imported.
section

/-! The comb's public-count bit extraction shifts by at most seven positions. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum.AArch64

private theorem shift_step (s : State) {k : Nat} (positive : 0<k) (fit : k<2^64)
 (count : s.gpr .x10=BitVec.ofNat 64 k) :
 WP isa (.block [.lsr .x .x11 .x11 1,.subImm .x .x10 .x10 1]) s fun t =>
 (t.gpr .x11=s.gpr .x11 >>> 1 ∧ t.gpr .x10=BitVec.ofNat 64 (k-1) ∧ t.mem=s.mem) ∧
 Keep [.x10,.x11] s t := by
 refine WP.keep [.x10,.x11] ?_ rfl rfl rfl
 brun [count]
 exact BitVec.ofNat_sub_ofNat_of_le k 1 (by decide) (by omega)

theorem shift_ok (s : State) {n : Nat} (positive : 0<n) (fit : n<2^64)
 (count : s.gpr .x10=BitVec.ofNat 64 n) :
 WP isa VG.Impl.Ffdh.AArch64.Cached.Comb.shift s fun t =>
 t.gpr .x11=s.gpr .x11 >>> n ∧ t.gpr .x10=0#64 ∧ t.mem=s.mem ∧ Keep [.x10,.x11] s t := by
 let I := fun k t => 0<k ∧ k≤n ∧ t.gpr .x10=BitVec.ofNat 64 k ∧
  t.gpr .x11=s.gpr .x11 >>> (n-k) ∧ t.mem=s.mem ∧ Keep [.x10,.x11] s t
 unfold VG.Impl.Ffdh.AArch64.Cached.Comb.shift
 refine WP.loop (M:=isa) I ?_ n s ⟨positive,by omega,count,by simp,rfl,Keep.refl _ _⟩
 intro k t h
 obtain ⟨posK,leK,countK,word,mem,rest⟩ := h
 refine WP.mono (shift_step t posK (by omega) countK) ?_
 rintro u ⟨⟨wordU,countU,memU⟩,restU⟩
 have next : u.gpr .x11=s.gpr .x11 >>> (n-(k-1)) := by
  rw [wordU,word,←BitVec.shiftRight_add]
  congr 1
  omega
 by_cases last : k=1
 · left
   refine ⟨?_,?_,?_,memU.trans mem,(rest.trans restU).mono (by decide)⟩
   · change some (u.gpr .x10 != 0#64) = some false
     simp only [countU,last,Nat.sub_self]
     decide
   · simpa only [last,Nat.sub_self,Nat.sub_zero] using next
   · simpa only [last,Nat.sub_self] using countU
 · right
   refine ⟨?_,k-1,by omega,by omega,by omega,countU,next,memU.trans mem,(rest.trans restU).mono (by decide)⟩
   change some (u.gpr .x10 != 0#64) = some true
   rw [countU]
   have ne : BitVec.ofNat 64 (k-1) ≠ 0#64 := by
    intro eq
    have h := congrArg BitVec.toNat eq
    change (k-1)%2^64=0 at h
    rw [Nat.mod_eq_of_lt (by omega)] at h
    omega
   simp [ne]

end VG.Proof.Ffdh.AArch64.Cached
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum.AArch64

private theorem read1_eq (m : Mem) (p : Addr) : m.read p 1 = m p := by
 change (0#0 ++ m p : BitVec (0+8)) = m p
 exact BitVec.zero_width_append _ _

private theorem byte_zext (b : Byte) : (b.setWidth 32).setWidth 64=BitVec.ofNat 64 b.toNat := by
 apply BitVec.eq_of_toNat_eq
 simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat]
 have := b.isLt
 omega

theorem bit_index {n k : Nat} (hn : n<2^31) (hk : k<8*n) :
 BitVec.ofNat 64 n - (BitVec.ofNat 64 k >>> 3) - 1#64 = BitVec.ofNat 64 (n-1-k/8) := by
 have shift : BitVec.ofNat 64 k >>> 3 = BitVec.ofNat 64 (k/8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow]
  omega
 rw [shift,BitVec.ofNat_sub_ofNat_of_le n (k/8) (by omega) (by omega),
  BitVec.ofNat_sub_ofNat_of_le (n-k/8) 1 (by decide) (by omega)]
 congr 1
 omega

theorem load_ok (s : State) {src : Addr} {n k : Nat} {b : Byte}
 (hn : n<2^31) (hk : k<8*n)
 (ptr : s.gpr .x1=src) (length : s.gpr .x2=BitVec.ofNat 64 n) (index : s.gpr .x9=BitVec.ofNat 64 k)
 (readable : InRegions (s.rd++s.wr) (src+BitVec.ofNat 64 (n-1-k/8)) 1)
 (byte : s.mem (src+BitVec.ofNat 64 (n-1-k/8))=b) :
 WP isa (.block VG.Impl.Ffdh.AArch64.Cached.Comb.load) s fun t =>
 (t.gpr .x11=BitVec.ofNat 64 b.toNat ∧ t.gpr .x10=BitVec.ofNat 64 (k%8) ∧ t.mem=s.mem) ∧
 Keep [.x8,.x10,.x11] s t := by
 unfold VG.Impl.Ffdh.AArch64.Cached.Comb.load
 refine WP.keep [.x8,.x10,.x11] ?_ rfl rfl rfl
 brun [ptr,length,index,bit_index hn hk,readable,read1_eq,byte,byte_zext]
 apply BitVec.eq_of_toNat_eq
 simp only [BitVec.toNat_and,BitVec.toNat_ofNat]
 rw [Nat.mod_eq_of_lt (by omega : k<2^64)]
 change k &&& 7 = (k%8)%2^64
 rw [show (7:Nat)=2^3-1 by decide,Nat.and_two_pow_sub_one_eq_mod]
 omega

end VG.Proof.Ffdh.AArch64.Cached
