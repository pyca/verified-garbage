module
public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.P384Joint
public import VerifiedGarbage.Impl.Weierstrass.AArch64.Joint
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointLoad
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelectV
import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Mont.AArch64.Row
public import VerifiedGarbage.Proof.Mont.AArch64.Words
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
public import VerifiedGarbage.Proof.Weierstrass.CheckPointContract
public import VerifiedGarbage.Proof.Weierstrass.PointOpsContract
public import VerifiedGarbage.Proof.Weierstrass.InverseContract
@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x)
def fixedLoadBody : List Instr := P384Joint.fixedAddress ++ Joint.loadWords P384Joint.K.E.x 12 ++
 copy 6 P384Joint.K.E.z (p384.sl ONEP)
private theorem syms_write (s : State) (sz : Size) (r : Reg) (x : BitVec sz.bits) :
 (s.write sz r x).syms=s.syms := rfl
theorem fixedAddress_ok {s : State} {a : Nat} {T : Addr}
 (ha : 1≤a) (h2 : s.gpr .x2=BitVec.ofNat 64 a) (ht : s.syms "VG_P384_GTAB"=T) :
 WP isa (.block P384Joint.fixedAddress) s fun t =>
 t.gpr .x16=T+BitVec.ofNat 64 (192*(a-1)) ∧ Keeps [.x2,.x3,.x16] s t := by
 apply WP.of_runBlock
 simp only [P384Joint.fixedAddress,show P384Joint.p384v.tsym="VG_P384_GTAB" from rfl,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
 RegUpd.gpr_write,syms_write,BitVec.setWidth_eq,Size.bits,h2,ht,
 show 1<4096 by decide,show 16*0<64 by decide,
 ite_true,ite_false,reduceCtorEq,Option.some.injEq,exists_eq_left']
 refine ⟨?_,?_,rfl,rfl,rfl,rfl⟩
 · simp only [Nat.mul_zero,BitVec.shiftLeft_zero]
   change T + ((BitVec.ofNat 64 a - BitVec.ofNat 64 1) * BitVec.ofNat 64 192) = _
   rw [BitVec.ofNat_sub_ofNat_of_le a 1 (by decide) (by omega),←BitVec.ofNat_mul]
   congr 2
   omega
 · intro r hr
   simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
   simp only [RegUpd.gpr_write,hr.1,hr.2.1,hr.2.2,ite_false]
/-- Loading x and y and copying the Montgomery one initializes an affine point. -/
theorem fixedLoadBody_ok {s : State} {base T : Addr} {size a : Nat}
    (hs : Scr s base size) (ha : 1≤a) (h2 : s.gpr .x2=BitVec.ofNat 64 a)
    (ht : s.syms "VG_P384_GTAB"=T) (hy : P384Joint.K.E.y=P384Joint.K.E.x+48)
    (hd : P384Joint.K.E.x+96≤size) (hd8 : P384Joint.K.E.x%8=0)
    (hz : P384Joint.K.E.z+48≤size) (hz8 : P384Joint.K.E.z%8=0)
    (hone : (p384.sl ONEP)+48≤size) (hone8 : (p384.sl ONEP)%8=0)
    (hsep : P384Joint.K.E.x+96≤P384Joint.K.E.z ∨ P384Joint.K.E.z+48≤P384Joint.K.E.x)
    (hsep1 : P384Joint.K.E.x+96≤(p384.sl ONEP) ∨ (p384.sl ONEP)+48≤P384Joint.K.E.x)
    (hsepz : P384Joint.K.E.z≤(p384.sl ONEP) ∨ (p384.sl ONEP)+48≤P384Joint.K.E.z)
    (hr : ∀ i<12, InRegions (s.rd++s.wr)
      (T+BitVec.ofNat 64 (192*(a-1))+BitVec.ofNat 64 (8*i)) 8)
    (hout : ∀ i<12, ∀ b<8, size≤ofs base
      (T+BitVec.ofNat 64 (192*(a-1))+BitVec.ofNat 64 (8*i)+BitVec.ofNat 64 b)) :
    WP isa (.block fixedLoadBody) s fun t =>
      wordsVal t.mem base P384Joint.K.E.x 6=wordsVal s.mem (T+BitVec.ofNat 64 (192*(a-1))) 0 6 ∧
      wordsVal t.mem base P384Joint.K.E.y 6=wordsVal s.mem (T+BitVec.ofNat 64 (192*(a-1))) 48 6 ∧
      wordsVal t.mem base P384Joint.K.E.z 6=wordsVal s.mem base (p384.sl ONEP) 6 ∧
      KeepRegs [.x1,.x2,.x3,.x4,.x16] s t ∧
      Unch base [(P384Joint.K.E.x,96),(P384Joint.K.E.z,48)] s.mem t.mem := by
  rw [fixedLoadBody,List.append_assoc,WP.block_append_iff]
  refine WP.mono (fixedAddress_ok ha h2 ht) fun b ⟨b16,kb⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (jointLoadWords_ok (hs.of_keeps kb (by decide)) b16 hd hd8 (by decide)
    (by intro i hi; rw [kb.rd,kb.wr]; exact hr i hi) hout 12 (by decide)) fun d ⟨wd,kd,od⟩ => ?_
  refine WP.mono (copy_ok 6 ((hs.of_keeps kb (by decide)).of_keepRegs kd (by decide))
    hz hone hz8 hone8 hsepz) fun t ⟨zt,kt,ot⟩ => ?_
  have hn := hs.nowrap
  have wx : wordsVal d.mem base P384Joint.K.E.x 6=wordsVal s.mem (T+BitVec.ofNat 64 (192*(a-1))) 0 6 := by
    refine wordsVal_of_words₂ _ _ _ fun i hi => ?_
    simpa only [Nat.zero_add,kb.mem] using wd i (by omega_using [hi])
  have wy : wordsVal d.mem base P384Joint.K.E.y 6=wordsVal s.mem (T+BitVec.ofNat 64 (192*(a-1))) 48 6 := by
    refine wordsVal_of_words₂ _ _ _ fun i hi => ?_
    rw [hy]
    have e := wd (6+i) (by omega_using [hi])
    simpa only [Nat.mul_add,Nat.add_assoc,kb.mem] using e
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [ot.wordsVal (by omega_using [hsep]) (by omega_using [hd, hn]),wx]
  · rw [ot.wordsVal (by omega_using [hy, hsep]) (by omega_using [hy, hd, hn]),wy]
  · rw [zt,od.wordsVal (by omega_using [hsep1]) (by omega_using [hone, hn]),kb.mem]
  · exact ((Keeps.regs kb).mono (by sub_regs)).trans
      ((kd.mono (by sub_regs)).trans (kt.mono (by sub_regs)))
  · intro x hx
    have hx0 := hx (P384Joint.K.E.x,96) (by simp)
    have hx1 := hx (P384Joint.K.E.z,48) (by simp)
    rw [ot x hx1,od x hx0,kb.mem]

end VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
