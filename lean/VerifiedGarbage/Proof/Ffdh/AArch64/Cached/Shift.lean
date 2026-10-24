module

public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Comb
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

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
