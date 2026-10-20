module

public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeTableState
public import VerifiedGarbage.Proof.Ffdh.GenerationPrecompute
import VerifiedGarbage.Proof.Bignum.ExportEncoding
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.GetElem
import Mathlib.Tactic.Ring

/-! Native header, Montgomery prefix, and dense comb entries form the canonical context. -/
@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Mont
open VG.Proof.Bignum (wv read_eq_wv word_eq_ofNat)

private theorem wordsAt_add (m : Mem) (a : Addr) (n k : Nat) :
    Spec.Rsa.wordsAt m a (n+k)=Spec.Rsa.wordsAt m a n ++ Spec.Rsa.wordsAt m (off a (8*n)) k := by
  simp only [Spec.Rsa.wordsAt,List.range_add,List.map_append,List.map_map]
  apply congrArg (fun xs=>(List.range n).map (fun i=>m.readW (a+BitVec.ofNat 64 (8*i)) 64) ++ xs)
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply,off,Offset.add_add,Nat.mul_add]

private theorem wordsAt_read {m : Mem} {a : Addr} {w x : Nat}
    (value : (m.read a (8*w)).toNat=x) :
    Spec.Rsa.wordsAt m a w=Spec.Rsa.toWords x w := by
  have number : wv m a 0 w=x := by
    rw [←read_eq_wv]
    simpa only [off,BitVec.add_zero] using value
  apply List.ext_getElem
  · simp only [Spec.Rsa.wordsAt,Spec.Rsa.toWords,List.length_map,List.length_range]
  · intro i hi _
    have bound : i<w := by simpa only [Spec.Rsa.wordsAt,List.length_map,List.length_range] using hi
    have word := word_eq_ofNat m a 0 w bound
    rw [number] at word
    simpa only [Spec.Rsa.wordsAt,Spec.Rsa.toWords,List.getElem_map,List.getElem_range,Nat.zero_add] using word

private theorem table_words {p : Inputs} {m : Mem} (table : TablePrefix p 32 m) (n : Nat) (hn : n≤32) :
    Spec.Rsa.wordsAt m (off (State.addr p.output) (24+16*p.w)) (n*p.w)=
      (List.range n).flatMap (fun digit=>Spec.Rsa.toWords (entryValue p digit) p.w) := by
  induction n with
  | zero => simp [Spec.Rsa.wordsAt]
  | succ n ih =>
    conv_lhs => arg 3; rw [Nat.add_mul,Nat.one_mul]
    rw [wordsAt_add,ih (by omega),List.range_succ,List.flatMap_append]
    simp only [List.flatMap_singleton]
    congr 1
    have addr : off (off (State.addr p.output) (24+16*p.w)) (8*(n*p.w))=
        off (State.addr p.output) (entryOffset p n) := by
      unfold off
      rw [Offset.add_add]
      rw [show 24+16*p.w+8*(n*p.w)=entryOffset p n by unfold entryOffset;ring]
    rw [addr]
    exact wordsAt_read (table n (by omega))

theorem canonical_words {p : Inputs} {m : Mem}
    (header : Spec.Rsa.wordsAt m (State.addr p.output) 3=
      [BitVec.ofNat 64 (bits p),BitVec.ofNat 64 ((bits p+7)/8),
        BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows (bits p))])
    (montgomery : Spec.Rsa.wordsAt m (off (State.addr p.output) 24) (2*p.w)=
      Spec.Rsa.toWords p.P p.w ++ Spec.Rsa.toWords (2^(128*p.w)%p.P) p.w)
    (table : TablePrefix p 32 m) :
    Spec.Rsa.wordsAt m (State.addr p.output) (Spec.Ffdh.generationPrecomputedWords p.k)=
      VG.Proof.Ffdh.generationValues p.k p.dom := by
  have length : Spec.Ffdh.generationPrecomputedWords p.k=3+(2*p.w+32*p.w) := by
    simp only [Spec.Ffdh.generationPrecomputedWords,Spec.Rsa.FixedBaseComb.precomputedWords,
      Spec.Rsa.precomputedWords,Spec.Rsa.FixedBaseComb.entries,Spec.Rsa.FixedBaseComb.teeth,Inputs.w]
  rw [length,wordsAt_add]
  change Spec.Rsa.wordsAt m (State.addr p.output) 3 ++
    Spec.Rsa.wordsAt m (off (State.addr p.output) 24) (2*p.w+32*p.w)=_
  rw [wordsAt_add,header,montgomery]
  have addr : off (off (State.addr p.output) 24) (8*(2*p.w))=
      off (State.addr p.output) (24+16*p.w) := by
    unfold off
    rw [Offset.add_add]
    rw [show 24+8*(2*p.w)=24+16*p.w by omega]
  rw [addr,table_words table 32 (by omega)]
  simp only [VG.Proof.Ffdh.generationValues,Spec.Rsa.FixedBaseComb.table,
    Spec.Rsa.FixedBaseComb.entries,Spec.Rsa.FixedBaseComb.teeth,entryValue,bits,Inputs.P,Inputs.G,Inputs.w,
    Spec.Ffdh.domainOf,List.append_assoc]

theorem canonical_precompute {p : Inputs} {m : Mem}
    (valid : Spec.Rsa.modulusValid p.P p.k=true)
    (header : Spec.Rsa.wordsAt m (State.addr p.output) 3=
      [BitVec.ofNat 64 (bits p),BitVec.ofNat 64 ((bits p+7)/8),
        BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows (bits p))])
    (montgomery : Spec.Rsa.wordsAt m (off (State.addr p.output) 24) (2*p.w)=
      Spec.Rsa.toWords p.P p.w ++ Spec.Rsa.toWords (2^(128*p.w)%p.P) p.w)
    (table : TablePrefix p 32 m) :
    Spec.Ffdh.generationPrecompute p.k p.dom=
      some (Spec.Rsa.wordsAt m (State.addr p.output) (Spec.Ffdh.generationPrecomputedWords p.k)) := by
  rw [canonical_words header montgomery table]
  apply VG.Proof.Ffdh.generationPrecompute_eq _ valid
  rw [p.domainLength]
  split <;> omega

end VG.Proof.Ffdh.Arm.CombBuilder
