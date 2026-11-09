module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.StreamTail
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.StreamBounds
import VerifiedGarbage.Proof.Framework.Block

/-! Complete streamed ordinary P-521 multiplication before reduction. -/

-- separate module: final-row bounds and the seventeen-word product interface
@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64

structure ProductInv (s₀ : State) (pa pt : Addr) (B : Nat) (s : State) : Prop where
  product : wordsVal s.mem pt 0 8+2^512*regsVal s row8In=wordsVal s₀.mem pa 0 9*B
  zero : s.gpr .x2=0
  memory : Outside pt 0 64 s₀.mem s.mem
  kept : KeepRegs streamClob s₀ s

theorem finish_product {s₀ s : State} {pa pt : Addr} {B : Nat}
    (inv : TailInv s₀ pa pt B s)
    (ha : wordsVal s₀.mem pa 0 9<2^521) (hb : B<2^521) :
    WP isa (.block (row8LowCode++row8HighCode)) s (ProductInv s₀ pa pt B) := by
  have ae := wordsVal_succ_top s₀.mem pa 0 8
  simp only [Nat.reduceAdd,Nat.reduceMul,Nat.zero_add] at ae
  have atop := top_limb_bound (L:=wordsVal s₀.mem pa 0 8)
    (A:=wordsVal s₀.mem pa 0 9) (top:=(word s₀.mem pa 64).toNat) ae ha
  have aTopReg : (s.gpr .x3).toNat<512 := by rw [inv.top]; exact atop
  have be : B=regsVal s bLowRegs+2^512*(s.gpr .x13).toNat := by
    rw [←inv.b]
    have hbr : bRegs=bLowRegs++[.x13] := rfl
    rw [hbr,regsVal_append]
    simp only [regsVal,Nat.mul_zero,Nat.add_zero,
      show bLowRegs.length=8 from rfl,Nat.reduceMul]
  have btop := top_limb_bound (L:=regsVal s bLowRegs) (A:=B)
    (top:=(s.gpr .x13).toNat) be hb
  have hpref := wordsVal_lt s₀.mem pa 0 8
  simp only [Nat.reduceMul] at hpref
  have ht := tail_acc_bound (P:=wordsVal s₀.mem pa 0 8)
    (S:=wordsVal s.mem pt 0 8) (T:=regsVal s row8In) (B:=B) hpref inv.product
  have hbound := final_row_bound (T:=regsVal s row8In) (B:=B) (s.gpr .x3) ht hb aTopReg
  have hbound' : regsVal s row8In+(s.gpr .x3).toNat*regsVal s bRegs<2^576 := by
    rw [inv.b]; exact hbound
  refine WP.mono (row8_value s (mulHi_small _ _ aTopReg btop) hbound') fun t ⟨prod,k⟩ => ?_
  refine ⟨?_,(k.gpr _ (by decide)).trans inv.zero,?_,?_⟩
  · rw [inv.b,inv.top] at prod
    have e := last_limb_identity inv.product prod
    rw [←ae] at e
    rw [k.mem]
    exact e
  · rw [k.mem]; exact inv.memory
  · exact inv.kept.trans ((VG.Proof.Mont.AArch64.Keeps.regs k).mono (by decide))

def productCode : List Instr := stream8Code++(row8LowCode++row8HighCode)

theorem product_ok {s : State} {pa pb pt : Addr}
    (ha : Ptr s .x1 pa 72) (hb : Ptr s .x2 pb 72) (ht : PtrW s .x27 pt 64)
    (stable : StableInput s pa pt)
    (ha' : wordsVal s.mem pa 0 9<2^521) (hb' : wordsVal s.mem pb 0 9<2^521) :
    WP isa (.block productCode) s (ProductInv s pa pt (wordsVal s.mem pb 0 9)) := by
  rw [productCode,WP.block_append_iff]
  refine WP.mono (stream8_ok ha hb ht stable) fun u inv => ?_
  exact finish_product inv ha' hb'

end VG.Proof.Mont.AArch64.P521Field
