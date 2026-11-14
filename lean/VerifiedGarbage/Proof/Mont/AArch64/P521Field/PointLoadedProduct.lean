module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointProduct
public import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.StreamValue
import VerifiedGarbage.Proof.Framework.Block

/-! Exact square product including all nine input reads. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 (loadsR)
open VG.Impl.Mont.AArch64.P521Square (aRegs)

def pointLoadedProduct (rn : Reg) (d : Nat) : List Instr :=
  loadsR rn (aRegs.take 8) d ++ pointProductCode rn (d+64)

theorem point_loaded_product_ok {s : State} {rn : Reg} {p : Addr} {size d : Nat}
    (hp : Ptr s rn p size) (hd : d+72≤size) (ha8 : d%8=0)
    (hrn : rn∉pointFullProductClob)
    (ha : wordsVal s.mem p d 9<2^521) :
    WP isa (.block (pointLoadedProduct rn d)) s fun t =>
      regsVal t pointProductRegs=wordsVal s.mem p d 9*wordsVal s.mem p d 9 ∧
      t.gpr .x6=0 ∧ VG.Proof.Ed25519.AArch64.Keeps pointFullProductClob s t := by
  have hr : rn∉aRegs.take 8 := fun h => hrn
    ((show ∀r∈aRegs.take 8,r∈pointFullProductClob from by decide) rn h)
  have hrLow : rn∉pointLowClob := fun h => hrn
    ((show ∀r∈pointLowClob,r∈pointFullProductClob from by decide) rn h)
  rw [pointLoadedProduct,WP.block_append_iff]
  refine WP.mono (loadsR_ok (aRegs.take 8) hp (by simpa only [aRegs,List.take,List.length_cons,List.length_nil] using Nat.le_trans (by omega_arith : d+64≤d+72) hd)
    ha8 (by decide) hr) fun u ⟨loaded,kl,_⟩ => ?_
  have hu := hp.of_keeps kl hr
  have hread : InRegions (u.rd++u.wr) (u.gpr rn+BitVec.ofNat 64 (d+64)) 8 := by
    rw [hu.reg]
    exact hu.ld (d+64) (by omega_arith)
  have hone : wordsVal s.mem p (d+64) 1=(word s.mem p (d+64)).toNat := by
    simp only [wordsVal,Nat.mul_zero,Nat.add_zero]
  have he := wordsVal_split s.mem p d 8 1
  simp only [Nat.reduceAdd,Nat.reduceMul,hone] at he
  have hp512 : (2:Nat)^512=13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096 := by decide +kernel
  have hp521 : (2:Nat)^521=6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057152 := by decide +kernel
  rw [hp512] at he
  have ha' := ha
  rw [hp521] at ha'
  have htop : (u.mem.readW (u.gpr rn+BitVec.ofNat 64 (d+64)) 64).toNat<512 := by
    rw [kl.mem,hu.reg]
    change (word s.mem p (d+64)).toNat<512
    omega_using [he,ha']
  refine WP.mono (point_product_ok u rn (d+64) ⟨by omega_arith,by have := hu.enc; omega_arith⟩
    hread hrLow htop) fun t ⟨prod,hz,kp⟩ => ?_
  refine ⟨?_,hz,(kl.mono (by decide)).trans kp⟩
  simp only [show (aRegs.take 8).length=8 from by decide] at loaded
  rw [prod,loaded,kl.mem,hu.reg]
  rw [←he]

end VG.Proof.Mont.AArch64.P521Field
