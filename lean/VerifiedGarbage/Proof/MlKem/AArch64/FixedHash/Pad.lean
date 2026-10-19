module

public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.PadByte
public import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Sha3.Lanes
import VerifiedGarbage.Proof.Framework.Block

/-! # The exact fixed-length suffix and final padding byte -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64

def padCode (sc : Reg) (st rate pos sfx : Nat) : List Instr :=
 xorByteCode sc (st+pos) sfx ++ xorByteCode sc (st+rate-1) 128

theorem pad_ok {s : State} {sc : Reg} {st rate pos sfx : Nat}
    (h9 : sc≠.x9) (h10 : sc≠.x10) (hr : 0<rate) (hr200 : rate≤200)
    (hp : pos<rate) (hoff : st+rate≤4096)
    (cov : Covers [⟨s.gpr sc+BitVec.ofNat 64 st,200⟩] s.wr) :
    WP isa (.block (padCode sc st rate pos sfx)) s fun t=>
      Keep [.x9,.x10] s t ∧ Frame [⟨s.gpr sc+BitVec.ofNat 64 st,200⟩] s.mem t.mem ∧
      Spec.Sha3.stateAt t.mem (s.gpr sc+BitVec.ofNat 64 st)=
        Proof.Sha3.xorByte (Proof.Sha3.xorByte (Spec.Sha3.stateAt s.mem (s.gpr sc+BitVec.ofNat 64 st))
          pos (BitVec.ofNat 8 sfx)) (rate-1) 128 := by
  have hw : ∀j<200,InRegions s.wr (s.gpr sc+BitVec.ofNat 64 st+BitVec.ofNat 64 j) 1 := by
    intro j hj
    exact cov _ _ ⟨⟨s.gpr sc+BitVec.ofNat 64 st,200⟩,by simp,Proof.Sha3.contains_offset (by omega) (by omega)⟩
  unfold padCode
  rw [WP.block_append_iff]
  refine WP.mono (xorByte_ok (off:=st+pos) (value:=sfx) h9 h10 (by omega)
    (by rw [←ptr_add]; exact hw pos (by omega))) fun a ha=>?_
  have ka := ha.1.get sc (by simp [h9,h10])
  have off : st+rate-1=st+(rate-1) := by omega
  have ma : a.mem=s.mem.writeW (s.gpr sc+BitVec.ofNat 64 st+BitVec.ofNat 64 pos)
      (s.mem (s.gpr sc+BitVec.ofNat 64 st+BitVec.ofNat 64 pos) ^^^ BitVec.ofNat 8 sfx) := by
    simpa only [ptr_add] using ha.2
  refine WP.mono (xorByte_ok (s:=a) (off:=st+rate-1) (value:=128) h9 h10 (by omega)
    (by rw [ha.1.wr,ka,off,←ptr_add]; exact hw (rate-1) (by omega))) fun t ht=>?_
  have mt : t.mem=a.mem.writeW (s.gpr sc+BitVec.ofNat 64 st+BitVec.ofNat 64 (rate-1))
      (a.mem (s.gpr sc+BitVec.ofNat 64 st+BitVec.ofNat 64 (rate-1)) ^^^ (128:Byte)) := by
    have hh := ht.2
    rw [ka,off,←ptr_add] at hh
    exact hh
  refine ⟨(ha.1.trans ht.1).mono (by simp),?_,?_⟩
  · rw [mt,ma]
    apply Frame.writeW (r:=⟨s.gpr sc+BitVec.ofNat 64 st,200⟩)
      (Frame.writeW (r:=⟨s.gpr sc+BitVec.ofNat 64 st,200⟩) (Frame.refl _ _) (by simp) _ ?_) (by simp) _ ?_
    · exact Proof.Sha3.contains_offset (by omega) (by omega)
    · exact Proof.Sha3.contains_offset (by omega) (by omega)
  · rw [mt,stateAt_writeXor (by omega),ma,stateAt_writeXor (by omega)]

end VG.Proof.MlKem.AArch64.FixedHash
