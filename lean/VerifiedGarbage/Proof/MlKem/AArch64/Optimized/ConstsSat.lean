module
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Consts
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Readonly.Words
import VerifiedGarbage.Proof.MlKem.Arith
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Optimized
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Impl.MlKem.AArch64.Ntt16 VG.Impl.MlKem.AArch64.Ntt16.Readonly

def tableSyms (name : String) : Addr :=
 if name="VG_MLKEM_REJ_SHUFFLE" then 0x200000 else
 if name="VG_MLKEM_GAMMA" then 0x210000 else
 if name="VG_MLKEM_NTT16_ZETAS" then 0x220000 else 0x230000

def tableMem : Mem := fun a =>
 if a.toNat<0x210000 then constMem 0x200000 Impl.MlKem.AArch64.Rej8.tableWords a else
 if a.toNat<0x220000 then constMem 0x210000 (words 32 gammaTable) a else
 if a.toNat<0x230000 then constMem 0x220000 (words 16 tableHalves) a else
 constMem 0x230000 (words 16 invTableHalves) a

theorem tableMem_word {n i : Nat} (hn : n<4) (hi : i<512) :
 tableMem.readW (BitVec.ofNat 64 (0x200000+65536*n)+BitVec.ofNat 64 (8*i)) 64 =
 (constMem (BitVec.ofNat 64 (0x200000+65536*n))
  ([Impl.MlKem.AArch64.Rej8.tableWords,words 32 gammaTable,words 16 tableHalves,words 16 invTableHalves].getD n [])).readW
   (BitVec.ofNat 64 (0x200000+65536*n)+BitVec.ofNat 64 (8*i)) 64 := by
 apply Mem.readW_congr
 intro j hj
 have e : (BitVec.ofNat 64 (0x200000+65536*n)+BitVec.ofNat 64 (8*i)+BitVec.ofNat 64 j).toNat =
  0x200000+65536*n+8*i+j := by
  rw [←BitVec.ofNat_add,←BitVec.ofNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
 rcases (by omega : n=0 ∨ n=1 ∨ n=2 ∨ n=3) with rfl|rfl|rfl|rfl
 · simp only [tableMem,e,ite_eq_left (by omega : 0x200000+65536*0+8*i+j<0x210000)]
   simp only [List.getD_cons_zero,Nat.reduceMul,Nat.reduceAdd]
   rfl
 · simp only [tableMem,e,ite_eq_right (by omega : ¬0x200000+65536*1+8*i+j<0x210000),
    ite_eq_left (by omega : 0x200000+65536*1+8*i+j<0x220000)]
   simp only [List.getD_cons_zero,List.getD_cons_succ,Nat.reduceMul,Nat.reduceAdd]
   rfl
 · simp only [tableMem,e,ite_eq_right (by omega : ¬0x200000+65536*2+8*i+j<0x210000),
    ite_eq_right (by omega : ¬0x200000+65536*2+8*i+j<0x220000),
    ite_eq_left (by omega : 0x200000+65536*2+8*i+j<0x230000)]
   simp only [List.getD_cons_zero,List.getD_cons_succ,Nat.reduceMul,Nat.reduceAdd]
   rfl
 · simp only [tableMem,e,ite_eq_right (by omega : ¬0x200000+65536*3+8*i+j<0x210000),
    ite_eq_right (by omega : ¬0x200000+65536*3+8*i+j<0x220000),
    ite_eq_right (by omega : ¬0x200000+65536*3+8*i+j<0x230000)]
   simp only [List.getD_cons_zero,List.getD_cons_succ,Nat.reduceMul,Nat.reduceAdd]
   rfl

theorem tableMem_held : Abi.constsHeld tableMem tableSyms constants := by
 simp only [Abi.constsHeld,constants,List.forall_mem_cons]
 refine ⟨?_,?_,?_,?_,fun _ h=>nomatch h⟩
 all_goals intro i hi
 · change i<Impl.MlKem.AArch64.Rej8.tableWords.length at hi
   rw [Rej8.tableWords_length] at hi
   rw [show tableSyms "VG_MLKEM_REJ_SHUFFLE"=0x200000 by rfl]
   have hx := tableMem_word (n:=0) (i:=i) (by decide) (by omega)
   simp only [Nat.reduceMul,Nat.reduceAdd,List.getD_cons_zero] at hx
   exact hx.trans (constMem_held _ _ (by rw [Rej8.tableWords_length]; decide) i (by rw [Rej8.tableWords_length]; exact hi))
 · change i<(words 32 gammaTable).length at hi
   rw [Ntt16.Readonly.gamma_length] at hi
   rw [show tableSyms "VG_MLKEM_GAMMA"=0x210000 by rfl]
   have hx := tableMem_word (n:=1) (i:=i) (by decide) (by omega)
   simp only [Nat.reduceMul,Nat.reduceAdd,List.getD_cons_zero,List.getD_cons_succ] at hx
   exact hx.trans (constMem_held _ _ (by rw [Ntt16.Readonly.gamma_length]; decide) i (by rw [Ntt16.Readonly.gamma_length]; exact hi))
 · change i<(words 16 tableHalves).length at hi
   rw [Ntt16.Readonly.forward_length] at hi
   rw [show tableSyms "VG_MLKEM_NTT16_ZETAS"=0x220000 by rfl]
   have hx := tableMem_word (n:=2) (i:=i) (by decide) (by omega)
   simp only [Nat.reduceMul,Nat.reduceAdd,List.getD_cons_zero,List.getD_cons_succ] at hx
   exact hx.trans (constMem_held _ _ (by rw [Ntt16.Readonly.forward_length]; decide) i (by rw [Ntt16.Readonly.forward_length]; exact hi))
 · change i<(words 16 invTableHalves).length at hi
   rw [Ntt16.Readonly.inverse_length] at hi
   rw [show tableSyms "VG_MLKEM_INTT16_ZETAS"=0x230000 by rfl]
   have hx := tableMem_word (n:=3) (i:=i) (by decide) (by omega)
   simp only [Nat.reduceMul,Nat.reduceAdd,List.getD_cons_zero,List.getD_cons_succ] at hx
   exact hx.trans (constMem_held _ _ (by rw [Ntt16.Readonly.inverse_length]; decide) i (by rw [Ntt16.Readonly.inverse_length]; exact hi))
end VG.Proof.MlKem.AArch64.Optimized
