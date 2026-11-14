module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.CmsPairValue
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.LinearPair
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.LinearSum

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64

def cmsLoadedPair (i b : Nat) : List Instr := twoLoads .x28 (cmsIn0 i) (cmsIn1 i) b++cmsPairCode i

theorem cms_loaded_pair_value {s : State} {p : Addr} {size b : Nat} (i : Nat) (hi : i<3)
    (hp : Ptr s .x28 p size) (hb : b+16≤size) (hb8 : b%8=0) :
    WP isa (.block (cmsLoadedPair i b)) s fun t =>
      regsVal t [cmsOut0 i,cmsOut1 i]+2^128*((t.gpr (cmsIn1 i)).toNat+t.c.toNat)=
        (s.gpr (cmsHigh i)).toNat+s.c.toNat+(s.gpr .x1).toNat*wordsVal s.mem p b 2 ∧
      t.gpr .x1=s.gpr .x1 ∧ Keeps (cmsPairClob i) s t := by
  have hc : i=0 ∨ i=1 ∨ i=2 := by omega_arith
  have hf : .x28≠cmsIn0 i ∧ cmsIn0 i≠cmsIn1 i ∧
      (cmsHigh i)∉[cmsIn0 i,cmsIn1 i] ∧ Reg.x1∉[cmsIn0 i,cmsIn1 i] ∧ Reg.x1∉cmsPairClob i ∧
      (∀r∈[cmsIn0 i,cmsIn1 i],r∈cmsPairClob i) := by
    rcases hc with rfl|rfl|rfl <;> decide
  rw [cmsLoadedPair,WP.block_append_iff]
  refine WP.mono (two_loads_ok hp hb hb8 hf.1 hf.2.1) fun u ⟨b0,b1,cu,ku⟩ => ?_
  refine WP.mono (cms_pair_value u i hi) fun t ⟨ev,kt⟩ => ?_
  rw [ku.gpr (cmsHigh i) hf.2.2.1,cu,ku.gpr .x1 hf.2.2.2.1,b0,b1] at ev
  refine ⟨?_,(kt.gpr .x1 hf.2.2.2.2.1).trans (ku.gpr .x1 hf.2.2.2.1),
    (ku.mono hf.2.2.2.2.2).trans kt⟩
  simpa only [wordsVal,Nat.mul_zero,Nat.add_zero] using ev

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64

def cmsScalarRegs : List Reg := [.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11]
def cmsPrefixHigh : Nat → Reg | 2 => .x7 | 4 => .x9 | 6 => .x11 | _ => .x13

def cmsScalarInv (s : State) (p : Addr) (b k : Nat) : Prop :=
  regsVal s (cmsScalarRegs.take k)+2^(64*k)*((s.gpr (cmsPrefixHigh k)).toNat+s.c.toNat)=
    12*wordsVal s.mem p b k

theorem cms_extend {S F T A L N C : Nat}
    (hp : S+F*T=12*A) (hc : L+2^128*N=T+12*C) :
    S+F*L+(F*2^128)*N=12*(A+F*C) := by
  have he := congrArg (fun n => F*n) hc
  simp only [Nat.mul_add] at he
  rw [Nat.mul_left_comm F 12] at he
  simp only [Nat.mul_add,Nat.mul_assoc]
  omega_using [hp,he]

theorem cms_prefix_step {s : State} {p : Addr} {size b : Nat} (i : Nat) (hi : i<3)
    (hp : Ptr s .x28 p size) (hb : b+8*(2*(i+1)+2)≤size) (hb8 : b%8=0)
    (hk : s.gpr .x1=12) (hv : cmsScalarInv s p b (2*(i+1))) :
    WP isa (.block (cmsLoadedPair i (b+8*(2*(i+1))))) s fun t =>
      cmsScalarInv t p b (2*(i+1)+2) ∧ t.gpr .x1=12 ∧ Keeps (cmsPairClob i) s t := by
  have cases_i : i=0 ∨ i=1 ∨ i=2 := by omega_arith
  have hlen : (cmsScalarRegs.take (2*(i+1))).length=2*(i+1) := by
    rcases cases_i with rfl|rfl|rfl <;> decide
  have hregs : cmsScalarRegs.take (2*(i+1)+2)=
      cmsScalarRegs.take (2*(i+1))++[cmsOut0 i,cmsOut1 i] := by
    rcases cases_i with rfl|rfl|rfl <;> decide
  have high0 : cmsPrefixHigh (2*(i+1))=cmsHigh i := by
    rcases cases_i with rfl|rfl|rfl <;> rfl
  have high1 : cmsPrefixHigh (2*(i+1)+2)=cmsIn1 i := by
    rcases cases_i with rfl|rfl|rfl <;> rfl
  have hf : ∀r∈cmsScalarRegs.take (2*(i+1)),r∉cmsPairClob i := by
    rcases cases_i with rfl|rfl|rfl <;> decide
  refine WP.mono (cms_loaded_pair_value i hi hp (by omega_arith) (by omega_arith)) fun t ⟨ev,kt,kept⟩ => ?_
  have low : regsVal t (cmsScalarRegs.take (2*(i+1)))=regsVal s (cmsScalarRegs.take (2*(i+1))) :=
    regsVal_congr fun r h => kept.gpr r (hf r h)
  have hs := hv
  dsimp only [cmsScalarInv] at hs ⊢
  rw [high0] at hs
  rw [hk,show (12 : BitVec 64).toNat=12 from rfl] at ev
  have extend := cms_extend hs ev
  have pw : 2^(64*(2*(i+1)+2))=2^(64*(2*(i+1)))*2^128 := by
    rw [show 64*(2*(i+1)+2)=64*(2*(i+1))+128 by omega_arith,Nat.pow_add]
  refine ⟨?_,kt.trans hk,kept⟩
  rw [hregs,regsVal_append,hlen,low,high1,pw,kept.mem,wordsVal_split]
  exact extend

end VG.Proof.Mont.AArch64.P521Field
