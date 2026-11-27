module

public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Comb
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ffdh.CombBitBytes
import VerifiedGarbage.Proof.Framework.PowLit
import Mathlib.Tactic.SplitIfs

/-! ### `Ffdh.AArch64.Cached.BitMath`, which this module and modules that import it used -/

section

/-! Width-guard and byte-extraction arithmetic for the public comb indices. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64

theorem sign_sub {a b : Nat} (ha : a<2^63) (hb : b<2^63) :
 ((BitVec.ofNat 64 a - BitVec.ofNat 64 b) >>> 63) =
 (if a<b then 1#64 else 0#64) := by
 apply BitVec.eq_of_toNat_eq
 simp only [BitVec.toNat_ushiftRight,BitVec.toNat_sub,BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow]
 rw [Nat.mod_eq_of_lt (by omega_using [ha] : a<2^64),Nat.mod_eq_of_lt (by omega_using [hb] : b<2^64)]
 split_ifs with h
 · change ((2^64-b+a)%2^64)/2^63=1
   rw [Nat.mod_eq_of_lt (by omega_using [ha, h])]
   omega_using [hb, h]
 · change ((2^64-b+a)%2^64)/2^63=0
   have eq : 2^64-b+a=2^64+(a-b) := by omega_using [ha, h]
   rw [eq,Nat.add_mod_left,Nat.mod_eq_of_lt (by omega_using [ha])]
   omega_using [ha]

theorem byte_bit : ∀ (b : Byte), ∀ n<8,
 ((BitVec.ofNat 64 b.toNat >>> n) &&& 1#64).toNat = b.toNat / 2^n % 2 := by
 decide +kernel

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.Cached.BitLoad`, which only this module used -/

section

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
 refine WP.loop (M:=isa) I ?_ n s ⟨positive,by omega_using [],count,by simp,rfl,Keep.refl _ _⟩
 intro k t h
 obtain ⟨posK,leK,countK,word,mem,rest⟩ := h
 refine WP.mono (shift_step t posK (by omega_using [fit, leK]) countK) ?_
 rintro u ⟨⟨wordU,countU,memU⟩,restU⟩
 have next : u.gpr .x11=s.gpr .x11 >>> (n-(k-1)) := by
  rw [wordU,word,←BitVec.shiftRight_add]
  congr 1
  omega_using [posK, leK]
 by_cases last : k=1
 · left
   refine ⟨?_,?_,?_,memU.trans mem,(rest.trans restU).mono (by decide)⟩
   · change some (u.gpr .x10 != 0#64) = some false
     simp only [countU,last,Nat.sub_self]
     decide
   · simpa only [last,Nat.sub_self,Nat.sub_zero] using next
   · simpa only [last,Nat.sub_self] using countU
 · right
   refine ⟨?_,k-1,by omega_using [posK],by omega_using [posK, last],by omega_using [leK],countU,next,memU.trans mem,(rest.trans restU).mono (by decide)⟩
   change some (u.gpr .x10 != 0#64) = some true
   rw [countU]
   have ne : BitVec.ofNat 64 (k-1) ≠ 0#64 := by
    intro eq
    have h := congrArg BitVec.toNat eq
    change (k-1)%2^64=0 at h
    rw [Nat.mod_eq_of_lt (by omega_using [fit, leK])] at h
    omega_using [positive, fit, count, posK, leK, countK, word, wordU, countU, next, last, eq, h]
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
 omega_using []

theorem bit_index {n k : Nat} (hn : n<2^31) (hk : k<8*n) :
 BitVec.ofNat 64 n - (BitVec.ofNat 64 k >>> 3) - 1#64 = BitVec.ofNat 64 (n-1-k/8) := by
 have shift : BitVec.ofNat 64 k >>> 3 = BitVec.ofNat 64 (k/8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow]
  omega_using [hn, hk]
 rw [shift,BitVec.ofNat_sub_ofNat_of_le n (k/8) (by omega_using [hn, hk]) (by omega_using [hk]),
  BitVec.ofNat_sub_ofNat_of_le (n-k/8) 1 (by decide) (by omega_using [hk])]
 congr 1
 omega_using []

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
 rw [Nat.mod_eq_of_lt (by omega_using [hn, hk] : k<2^64)]
 change k &&& 7 = (k%8)%2^64
 rw [show (7:Nat)=2^3-1 by decide,Nat.and_two_pow_sub_one_eq_mod]
 omega_using []

end VG.Proof.Ffdh.AArch64.Cached

end

end


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
 split <;> omega_using []

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
 · obtain ⟨tr,t,run,word,_,mem,rest⟩ := shift_ok s (by omega_using [zero]) (by omega_using [bound]) count
   refine ⟨_,t,.iteF ?_ run,word,mem,rest⟩
   rw [eval_zero,count]
   have ne : BitVec.ofNat 64 r ≠ 0#64 := by
    intro eq
    have h := congrArg BitVec.toNat eq
    change r%2^64=0 at h
    rw [Nat.mod_eq_of_lt (by omega_using [bound])] at h
    omega_using [zero, h]
   simp [ne]

private theorem maskedBit (b : Byte) {r : Nat} (hr : r<8) :
 (BitVec.ofNat 64 b.toNat >>> r) &&& 1#64 = BitVec.ofNat 64 (b.toNat/2^r%2) := by
 apply BitVec.eq_of_toNat_eq
 rw [byte_bit b r hr,BitVec.toNat_ofNat]
 exact (Nat.mod_eq_of_lt (by omega_using [] : b.toNat/2^r%2<2^64)).symm

theorem bit_ok (s : State) {src : Addr} {bs : List Byte} {k N : Nat}
 (source : Source src bs s) (size : bs.length<2^31) (widthBound : N≤8*bs.length)
 (indexFit : k<2^63)
 (ptr : s.gpr .x1=src) (length : s.gpr .x2=BitVec.ofNat 64 bs.length)
 (index : s.gpr .x9=BitVec.ofNat 64 k) (width : s.gpr .x5=BitVec.ofNat 64 N) :
 WP isa VG.Impl.Ffdh.AArch64.Cached.Comb.bit s fun t =>
 t.gpr .x11=BitVec.ofNat 64 (bitValue bs N k) ∧ t.mem=s.mem ∧ Keep [.x8,.x10,.x11] s t := by
 unfold VG.Impl.Ffdh.AArch64.Cached.Comb.bit
 rw [WP.seq_iff]
 refine WP.mono (guard_ok s indexFit (by omega_using [size, widthBound]) index width) ?_
 rintro u ⟨⟨flag,memU⟩,restU⟩
 by_cases inside : k<N
 · apply WP.ite true (by rw [eval_nonzero,flag,ite_eq_left inside]; decide)
   · intro _
     rw [WP.seq_iff]
     have pos : bs.length-1-k/8<bs.length := by omega_using [widthBound, inside]
     refine WP.mono (load_ok u (b:=bs.getD (bs.length-1-k/8) 0) size (by omega_using [widthBound, inside])
      ((restU.gpr .x1 (by decide)).trans ptr) ((restU.gpr .x2 (by decide)).trans length)
      ((restU.gpr .x9 (by decide)).trans index)
      (by rw [restU.rd,restU.wr]; exact source.readable _ pos)
      (by rw [memU]; exact source.bytes _ pos)) ?_
     rintro v ⟨⟨byte,count,memV⟩,restV⟩
     rw [WP.seq_iff]
     refine WP.mono (optionalShift_ok v (by omega_using []) count) ?_
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
