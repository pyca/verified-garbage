module

import VerifiedGarbage.Proof.Mont.X86.CombBuild
import VerifiedGarbage.Proof.Mont.WordsCanonical
public import VerifiedGarbage.Proof.Dsa.FixedBaseCombContract
import VerifiedGarbage.Proof.Rsa.FixedBaseCombTable
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Mont.X86.CombTableState

/-! Arithmetic table invariants imply the exact shared RSA word representation. -/

@[expose] public section
namespace VG.Proof.Mont.X86.Comb
open VG VG.Proof.Mont VG.Impl.Mont.X86.Dynamic

theorem TableAt.canonical {n context m g bits : Nat} {base : Addr} {mem : Mem}
    (T : TableAt n context m g bits base (fun _ => True) mem) :
    Spec.Rsa.wordsAt mem (off base (context+16*n)) (32*n)=Spec.Rsa.FixedBaseComb.table m g bits n := by
  rw [wordsAt_blocks]
  unfold Spec.Rsa.FixedBaseComb.table
  simp only [Spec.Rsa.FixedBaseComb.entries,Spec.Rsa.FixedBaseComb.teeth]
  simp only [List.flatMap_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro j hj
  rw [wordsAt_canonical]
  have V := T j (List.mem_range.mp hj) trivial
  change wordsVal mem base (context+16*n+8*n*j) n = _ at V
  rw [V]
  rfl

theorem context_canonical {L : Impl.Dsa.FixedBaseComb.Layout} {m g : Nat} {base : Addr} {mem : Mem}
    (P : wordsVal mem base L.context L.n=m)
    (R : wordsVal mem base (L.context+8*L.n) L.n=2^(128*L.n)%m)
    (T : TableAt L.n L.context m g (32*L.e) base (fun _ => True) mem) :
    Spec.Rsa.wordsAt mem (off base L.context) (Proof.Dsa.FixedBaseComb.contextWords L)=
      Proof.Dsa.FixedBaseComb.context L m g := by
  have size : Proof.Dsa.FixedBaseComb.contextWords L=L.n+(L.n+32*L.n) := by
    unfold Proof.Dsa.FixedBaseComb.contextWords Spec.Rsa.FixedBaseComb.entries Spec.Rsa.FixedBaseComb.teeth
    omega
  rw [size,wordsAt_append,wordsAt_append,wordsAt_canonical,wordsAt_canonical,P,R]
  have addr : L.context+8*L.n+8*L.n=L.context+16*L.n := by omega
  rw [addr,T.canonical]
  simp only [Proof.Dsa.FixedBaseComb.context,List.append_assoc]

theorem table_of_context {L : Impl.Dsa.FixedBaseComb.Layout} {m g : Nat} {base : Addr} {mem : Mem}
    (mp : 0<m) (mb : m<2^(64*L.n))
    (H : Spec.Rsa.wordsAt mem (off base L.context) (Proof.Dsa.FixedBaseComb.contextWords L)=
      Proof.Dsa.FixedBaseComb.context L m g) :
    TableAt L.n L.context m g (32*L.e) base (fun _ => True) mem := by
  have size : Proof.Dsa.FixedBaseComb.contextWords L=2*L.n+32*L.n := by
    unfold Proof.Dsa.FixedBaseComb.contextWords Spec.Rsa.FixedBaseComb.entries Spec.Rsa.FixedBaseComb.teeth
    omega
  have lists := congrArg (List.drop (2*L.n)) H
  rw [size,wordsAt_append,List.drop_left' (by simp only [Spec.Rsa.wordsAt,List.length_map,List.length_range])] at lists
  unfold Proof.Dsa.FixedBaseComb.context at lists
  rw [List.drop_left' (by simp only [List.length_append,Spec.Rsa.toWords,List.length_map,List.length_range]; omega)] at lists
  have addr : L.context+8*(2*L.n)=L.context+16*L.n := by omega
  rw [addr] at lists
  intro j hj _
  have jn : j*L.n+L.n≤32*L.n := by
    have := Nat.mul_le_mul_right L.n (show j+1≤32 by omega)
    simpa only [Nat.add_mul,Nat.one_mul] using this
  have block := congrArg (fun l : List (BitVec 64) => (l.drop (j*L.n)).take L.n) lists
  rw [wordsAt_slice _ _ _ _ _ _ jn,VG.Proof.Rsa.FixedBaseComb.table_entry _ _ _ _ _ hj] at block
  have V := wordsAt_value block
  have entryAddr : L.context+16*L.n+8*(j*L.n)=entry L.n (L.context+16*L.n) j := by
    unfold entry; ac_rfl
  rw [entryAddr,Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ mp) mb)] at V
  exact V

end VG.Proof.Mont.X86.Comb
