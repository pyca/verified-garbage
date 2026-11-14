module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointLoadedProduct
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointReduction
public import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Framework.Block

/-! One memory/alias contract for every fused square site. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 (storesR)
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

def pointSquareNormalized (rn : Reg) (d : Nat) (rt : Reg) (o : Nat) : List Instr :=
  pointLoadedProduct rn d ++ (pointFoldCode++(pointCorrectCode++storesR rt pointFoldOutRegs o))

theorem point_square_normalized_ok {s : State} {rn rt : Reg} {p q : Addr} {size cap d o : Nat}
    (hp : Ptr s rn p size) (hq : PtrW s rt q cap)
    (hd : d+72≤size) (ho : o+72≤cap) (hd8 : d%8=0) (ho8 : o%8=0)
    (hrn : rn∉pointFullProductClob) (hrt : rt∉pointFullProductClob)
    (ha : wordsVal s.mem p d 9<fieldPrime) :
    WP isa (.block (pointSquareNormalized rn d rt o)) s fun t =>
      wordsVal t.mem q o 9<fieldPrime ∧
      wordsVal t.mem q o 9=(wordsVal s.mem p d 9*wordsVal s.mem p d 9)%fieldPrime ∧
      t.gpr .x1=0 ∧ t.gpr .x0=511 ∧ KeepRegs pointFullProductClob s t ∧ Outside q o 72 s.mem t.mem := by
  have fieldBound : fieldPrime≤2^521 := by
    dsimp only [fieldPrime]
    have h := Nat.sub_le ((2:Nat)^521) 1
    exact h
  have ha' : wordsVal s.mem p d 9<2^521 := Nat.lt_of_lt_of_le ha fieldBound
  rw [pointSquareNormalized,WP.block_append_iff]
  refine WP.mono (point_loaded_product_ok hp hd hd8 hrn ha') fun u ⟨prod,z6,kp⟩ => ?_
  have hu : regsVal u pointProductRegs<fieldPrime*fieldPrime := by
    rw [prod]
    exact Nat.mul_lt_mul'' ha ha
  rw [←List.append_assoc,WP.block_append_iff]
  refine WP.mono (point_reduce_ok z6 hu) fun v ⟨canon,val,z1,mask,kr⟩ => ?_
  have kv := kp.trans (kr.mono (by decide))
  have hqv := hq.of_keepRegs (Keeps.regs kv) hrt
  refine WP.mono (storesR_ok pointFoldOutRegs hqv (o:=o) (by simpa only
    [show pointFoldOutRegs.length=9 from rfl] using ho) ho8 (by decide))
    fun t ⟨stored,ks,frame⟩ => ?_
  change wordsVal t.mem q o 9=regsVal v pointFoldOutRegs at stored
  exact ⟨by rw [stored]; exact canon,by rw [stored,val,prod],
    (ks.gpr .x1 (by decide)).trans z1,(ks.gpr .x0 (by decide)).trans mask,
    (Keeps.regs kv).trans (ks.mono (by decide)),by rw [kv.mem] at frame; exact frame⟩

end VG.Proof.Mont.AArch64.P521Field
