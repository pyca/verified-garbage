module

public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Policy
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Header
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-! Select q's public bytes when present, otherwise p's public bytes. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

private theorem exec_cselc_x (s : State) (d n m : Reg) (cond : CondCode) :
 exec (.cselc .x d n m cond) s=some (s.write .x d (if cond.holds s then s.gpr n else s.gpr m)) := rfl
private theorem zeroFlag (s : State) (d : Reg) (a b : BitVec 64) (c : Bool) :
 (s.addWithCarry .x d a b c).zf=decide (a+b+BitVec.ofNat 64 c.toNat=0#64) := rfl

private theorem publicSub (k dl : Nat) (size : k<2^31) (shape : dl=2*k ∨ dl=3*k) :
 BitVec.ofNat 64 dl+ ~~~BitVec.ofNat 64 (2*k)+1#64=BitVec.ofNat 64 (dl-2*k) := by
 rw [BitVec.add_assoc,←BitVec.neg_eq_not_add,←BitVec.sub_eq_add_neg]
 exact BitVec.ofNat_sub_ofNat_of_le dl (2*k) (by omega) (by omega)

theorem policySource_ok {s : State} {B dom : Addr} {Z k dl : Nat}
 (scratch : Scr s B Z) (room : 256≤Z) (base : s.gpr .x0=B)
 (positive : 0<k) (size : k<2^31) (shape : dl=2*k ∨ dl=3*k)
 (pointer : word s.mem B (8*sDom)=dom) (length : word s.mem B (8*sLen)=BitVec.ofNat 64 k)
 (domainLength : word s.mem B (8*sDL)=BitVec.ofNat 64 dl) :
 WP isa (.block (Policy.boundSource++[movi .x10 0])) s fun t =>
 (t.gpr .x1=(if dl=2*k then dom else off dom (2*k)) ∧
 t.gpr .x2=BitVec.ofNat 64 k ∧ t.gpr .x10=0#64 ∧ t.mem=s.mem) ∧ Keep [.x1,.x2,.x3,.x4,.x10] s t := by
 have shift : BitVec.ofNat 64 k <<< 1=BitVec.ofNat 64 (2*k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft,BitVec.toNat_ofNat,Nat.shiftLeft_eq]
  omega
 have choose : (if decide (BitVec.ofNat 64 (dl-2*k)=0#64) then dom else dom+BitVec.ofNat 64 (2*k))=
  (if dl=2*k then dom else off dom (2*k)) := by
  rcases shape with eq | eq
  · subst dl
    simp
  · subst dl
    have ne : BitVec.ofNat 64 (3*k-2*k)≠0#64 := by
     intro zero
     have := congrArg BitVec.toNat zero
     simp only [BitVec.toNat_ofNat] at this
     omega
    simp only [ne,decide_false,ite_false,show ¬3*k=2*k by omega]
    rfl
 refine WP.keep [.x1,.x2,.x3,.x4,.x10] ?_ rfl rfl rfl
 unfold Policy.boundSource
 brun [base,hdr_enc (show sDom<32 by decide),hdr_enc (show sLen<32 by decide),hdr_enc (show sDL<32 by decide),
  scratch.ld (d:=8*sDom) (by unfold sDom;omega),scratch.ld (d:=8*sLen) (by unfold sLen;omega),
  scratch.ld (d:=8*sDL) (by unfold sDL;omega),pointer,length,domainLength,shift,
  exec_cselc_x,CondCode.holds,RegUpd.zf_write,zeroFlag,Bool.toNat_true,publicSub k dl size shape,choose]

end VG.Proof.Ffdh.AArch64.Cached
