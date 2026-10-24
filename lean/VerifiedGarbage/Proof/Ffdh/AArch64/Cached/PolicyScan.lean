module

public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Policy
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Bit
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-! The general policy scans public bound bytes to the first nonzero byte. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

private theorem read1_eq (m : Mem) (p : Addr) : m.read p 1=m p := by
 change (0#0 ++ m p : BitVec (0+8))=m p
 exact BitVec.zero_width_append _ _

private theorem byte_zext (b : Byte) : (b.setWidth 32).setWidth 64=BitVec.ofNat 64 b.toNat := by
 apply BitVec.eq_of_toNat_eq
 simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat]
 have := b.isLt
 omega

private theorem byte_zero : ∀ b : Byte,
 (BitVec.ofNat 64 b.toNat == 0#64)=decide (b=0#8) := by decide +kernel

theorem policyScanStep {s : State} {src : Addr} {bs : List Byte} {i : Nat}
 (source : Source src bs s) (_size : bs.length<2^31) (inside : i<bs.length)
 (pointer : s.gpr .x1=off src i) (remaining : s.gpr .x2=BitVec.ofNat 64 (bs.length-i)) :
 WP isa (.block Policy.scanStep) s fun t =>
 (t.gpr .x1=off src (i+1) ∧ t.gpr .x2=BitVec.ofNat 64 (bs.length-(i+1)) ∧
 t.gpr .x3=BitVec.ofNat 64 (bs.getD i 0).toNat ∧ t.mem=s.mem) ∧ Keep [.x1,.x2,.x3] s t := by
 refine WP.keep [.x1,.x2,.x3] ?_ rfl rfl rfl
 unfold Policy.scanStep
 brun [pointer,remaining,source.readable i inside,source.bytes i inside,read1_eq,byte_zext]
 rw [BitVec.ofNat_sub_ofNat_of_le (bs.length-i) 1 (by decide) (by omega)]
 congr 1

theorem policyScan_ok (s : State) {src : Addr} {bs : List Byte} {L : Nat}
 (source : Source src bs s) (size : bs.length<2^31) (inside : L<bs.length)
 (zeros : ∀ i<L,bs.getD i 0=0#8) (nonzero : bs.getD L 0≠0#8)
 (pointer : s.gpr .x1=src) (remaining : s.gpr .x2=BitVec.ofNat 64 bs.length) :
 WP isa (.loop (.block Policy.scanStep) (.zero .x .x3)) s fun t =>
 t.gpr .x1=off src (L+1) ∧ t.gpr .x2=BitVec.ofNat 64 (bs.length-(L+1)) ∧
 t.gpr .x3=BitVec.ofNat 64 (bs.getD L 0).toNat ∧ t.mem=s.mem ∧ Keep [.x1,.x2,.x3] s t := by
 let I := fun n t => ∃ j, n=L+1-j ∧ j≤L ∧
  t.gpr .x1=off src j ∧ t.gpr .x2=BitVec.ofNat 64 (bs.length-j) ∧
  t.mem=s.mem ∧ Keep [.x1,.x2,.x3] s t
 refine WP.loop (M:=isa) I ?_ (L+1) s ?_
 · intro n t h
   obtain ⟨j,rem,hj,pointerT,leftT,memT,restT⟩ := h
   refine WP.mono (policyScanStep (source.of_mem memT restT) size (by omega) pointerT leftT) ?_
   rintro u ⟨⟨pointerU,leftU,byteU,memU⟩,restU⟩
   by_cases last : j=L
   · left
     subst j
     refine ⟨?_,pointerU,leftU,byteU,memU.trans memT,(restT.trans restU).mono (by decide)⟩
     rw [eval_zero,byteU]
     change some (BitVec.ofNat 64 (bs.getD L 0).toNat == 0#64)=some false
     rw [byte_zero,decide_eq_false nonzero]
   · right
     refine ⟨?_,L+1-(j+1),by omega,j+1,rfl,by omega,pointerU,leftU,
      memU.trans memT,(restT.trans restU).mono (by decide)⟩
     rw [eval_zero,byteU]
     change some (BitVec.ofNat 64 (bs.getD j 0).toNat == 0#64)=some true
     rw [byte_zero,zeros j (by omega)]
     decide
 · refine ⟨0,by omega,by omega,?_,?_,rfl,Keep.refl _ _⟩
   · simpa [off] using pointer
   · simpa using remaining

end VG.Proof.Ffdh.AArch64.Cached
