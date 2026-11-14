module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeProduct
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeReduction
import VerifiedGarbage.Proof.Framework.Block

/-! The ordinary multiplication's complete arithmetic core. -/

-- separate module: product and canonical reduction before ABI stores/restores
@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

/-- Writable scratch is also readable in the model. -/
theorem _root_.VG.Proof.Mont.AArch64.PtrW.readable {s : State} {r : Reg} {p : Addr} {n : Nat}
    (h : PtrW s r p n) : Ptr s r p n := by
  refine ⟨h.reg,?_,h.enc⟩
  intro d hd
  obtain ⟨region,hr,hc⟩ := h.st d hd
  exact ⟨region,List.mem_append_right _ hr,hc⟩

def nativeArithmetic : List Instr := nativeProductCode++(nativeFold++nativeCorrect)
def arithmeticClob : List Reg := .x1::streamClob

theorem nativeArithmetic_eq : (mulFnBlocks.flatten.drop 16).take 394=nativeArithmetic := by
  have h0 := List.take_add (l:=mulFnBlocks.flatten.drop 16) (i:=354) (j:=40)
  have h1 := List.take_add (l:=mulFnBlocks.flatten.drop 370) (i:=29) (j:=11)
  simp only [List.drop_drop,Nat.reduceAdd] at h0 h1
  rw [nativeArithmetic,nativeProductCode,nativeFold,←nativeCorrect_eq,h0,h1]

theorem native_arithmetic_ok {s : State} {pa pb pt : Addr}
    (ha : Ptr s .x1 pa 72) (hb : Ptr s .x2 pb 72) (ht : PtrW s .x27 pt 64)
    (stable : StableInput s pa pt)
    (ha' : wordsVal s.mem pa 0 9<fieldPrime) (hb' : wordsVal s.mem pb 0 9<fieldPrime) :
    WP isa (.block nativeArithmetic) s fun t =>
      regsVal t bRegs<fieldPrime ∧
      regsVal t bRegs=wordsVal s.mem pa 0 9*wordsVal s.mem pb 0 9%fieldPrime ∧
      Outside pt 0 64 s.mem t.mem ∧ KeepRegs arithmeticClob s t := by
  have fieldBound : fieldPrime≤2^521 := by
    dsimp only [fieldPrime]
    have h := Nat.sub_le ((2 : Nat)^521) 1
    exact h
  have haSmall : wordsVal s.mem pa 0 9<2^521 :=
    Nat.lt_of_lt_of_le ha' fieldBound
  have hbSmall : wordsVal s.mem pb 0 9<2^521 :=
    Nat.lt_of_lt_of_le hb' fieldBound
  rw [nativeArithmetic,WP.block_append_iff]
  refine WP.mono (native_product_ok ha hb ht stable haSmall hbSmall) fun u inv => ?_
  have hp := (ht.of_keepRegs inv.kept (by decide)).readable
  have hu : streamedValue u pt<fieldPrime*fieldPrime := by
    dsimp only [streamedValue]
    rw [inv.product]
    exact Nat.mul_lt_mul'' ha' hb'
  refine WP.mono (native_reduce_ok hp inv.zero hu) fun t ⟨bound,value,k⟩ => ?_
  refine ⟨bound,?_,?_,(inv.kept.mono (by decide)).trans
    ((VG.Proof.Mont.AArch64.Keeps.regs k).mono (by decide))⟩
  · rw [value]
    dsimp only [streamedValue]
    rw [inv.product]
  · rw [k.mem]; exact inv.memory

end VG.Proof.Mont.AArch64.P521Field
