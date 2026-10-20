module

import VerifiedGarbage.Proof.Ffdh.Arm.CachedGenerationFacts
public import VerifiedGarbage.Proof.Bignum.Arm.CombTableState
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.ExportEncoding
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import Mathlib.Tactic.Ring
public import VerifiedGarbage.Proof.Ffdh.Arm.CachedGenerationEnvironment

/-! Canonical reusable context words are exactly the read-only native comb table. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum VG.Proof.Bignum.Arm

def cachedTablePtr (p : Inputs) : BitVec 32 := p.cachedContext+BitVec.ofNat 32 (24+16*p.w)

theorem CachedGenerationContext.table {p : Inputs} {s : State} (h : CachedGenerationContext p s) :
    CombTable (cachedTablePtr p) p.w p.P p.G
      (Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k p.dom)) s := by
  have wPos : 0<p.w := by have := p.width.1; omega
  have wordsCount : p.cachedWords=3+34*p.w := by
    rw [h.canonical.1]
    simp only [Spec.Ffdh.generationPrecomputedWords,Spec.Rsa.FixedBaseComb.precomputedWords,
      Spec.Rsa.precomputedWords,Spec.Rsa.FixedBaseComb.entries,Spec.Rsa.FixedBaseComb.teeth,Inputs.w]
    omega
  have size : 8*p.cachedWords=24+272*p.w := by rw [wordsCount]; omega
  have ptrAddr : State.addr (cachedTablePtr p)=VG.Proof.Mont.off (State.addr p.cachedContext) (24+16*p.w) := by
    unfold cachedTablePtr
    exact addr_add (by have := h.fit; omega)
  have ptrNat : (cachedTablePtr p).toNat=p.cachedContext.toNat+(24+16*p.w) := by
    simp only [cachedTablePtr,BitVec.toNat_add,BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by have := h.fit; omega : 24+16*p.w<2^32)]
    exact Nat.mod_eq_of_lt (by have := h.fit; omega)
  refine ⟨wPos,?_,?_,?_⟩
  · rw [ptrNat]
    have := h.fit
    omega
  · rw [ptrAddr]
    exact CallLay.inRegions_sub h.readable (by omega) (by omega)
  · intro a ha
    let E := Spec.Rsa.powMod p.G
      (Spec.Rsa.FixedBaseComb.exponent (Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k p.dom)) a) p.P *
      2^(64*p.w)%p.P
    have modValid := VG.Proof.Ffdh.domainValid_mod h.valid
    have pPos : 0<p.P := by have := (valid_facts modValid p.minLength).2.1; exact Nat.lt_trans (by decide) this
    have pBound : p.P<2^(64*p.w) := by
      have v := os2ip_lt (p.dom.take p.k)
      rw [p.pLength,pow256_eq] at v
      exact Nat.lt_of_lt_of_le v (Nat.pow_le_pow_right (by decide) (by have := p.width.2.2.2.1; omega))
    have eBound : E<2^(64*p.w) := Nat.lt_trans (Nat.mod_lt _ pPos) pBound
    have limb (i : Nat) (hi : i<p.w) :
        s.mem.readW (VG.Proof.Mont.off (State.addr p.cachedContext) (24+16*p.w+8*p.w*a+8*i)) 64 =
          BitVec.ofNat 64 (E/2^(64*i)) := by
      let index := 3+(2+a)*p.w+i
      have mulA : (2+a)*p.w≤33*p.w := Nat.mul_le_mul_right _ (by omega)
      have indexFit : index<p.cachedWords := by dsimp [index]; omega
      have entries := VG.Proof.Ffdh.generationValues_entry p.k p.dom a ha
      have entry := congrArg (fun xs : List (BitVec 64) => xs[i]?) entries
      have hik : i<Spec.Rsa.modulusWords p.k := hi
      simp only [List.getElem?_take,ite_eq_left hik,List.getElem?_drop,Spec.Rsa.toWords,
        List.getElem?_map,List.getElem?_range hik,Option.map_some] at entry
      have read := congrArg (fun xs : List (BitVec 64) => xs[index]?) h.words
      simp only [Spec.Rsa.wordsAt,List.getElem?_map,List.getElem?_range indexFit,Option.map_some] at read
      change some (s.mem.readW (VG.Proof.Mont.off (State.addr p.cachedContext) (8*index)) 64)=_ at read
      dsimp only [index,Inputs.w] at read
      rw [entry] at read
      have offset : 24+16*p.w+8*p.w*a+8*i=8*index := by dsimp [index]; ring
      rw [offset]
      exact Option.some.inj read
    have value : wv s.mem (State.addr p.cachedContext) (24+16*p.w+8*p.w*a) p.w=E := by
      rw [← Nat.mod_eq_of_lt eBound]
      apply wv_of_words
      intro i hi
      change (s.mem.readW (VG.Proof.Mont.off (State.addr p.cachedContext) (24+16*p.w+8*p.w*a+8*i)) 64).toNat=_
      rw [limb i hi,BitVec.toNat_ofNat]
    rw [← read_eq_val32,show 4*(2*p.w)=8*p.w by omega,ptrAddr]
    simp only [VG.Proof.Mont.off,Offset.add_add]
    change (s.mem.read (VG.Proof.Mont.off (State.addr p.cachedContext) (24+16*p.w+8*p.w*a)) (8*p.w)).toNat=E
    rw [read_eq_wv]
    exact value

theorem CachedGenerationContext.tableSeparate {p : Inputs} {s : State}
    (h : CachedGenerationContext p s) : ∀ r∈keyCallWrites p s,
      (⟨State.addr (cachedTablePtr p),32*(8*p.w)⟩ : Region).Disjoint r := by
  have wPos : 0<p.w := by have := p.width.1; omega
  have wordsCount : p.cachedWords=3+34*p.w := by
    rw [h.canonical.1]
    simp only [Spec.Ffdh.generationPrecomputedWords,Spec.Rsa.FixedBaseComb.precomputedWords,
      Spec.Rsa.precomputedWords,Spec.Rsa.FixedBaseComb.entries,Spec.Rsa.FixedBaseComb.teeth,Inputs.w]
    omega
  have size : 8*p.cachedWords=24+272*p.w := by rw [wordsCount]; omega
  have address : State.addr (cachedTablePtr p)=VG.Proof.Mont.off (State.addr p.cachedContext) (24+16*p.w) := by
    unfold cachedTablePtr
    exact addr_add (by have := h.fit; omega)
  have sub : (⟨State.addr (cachedTablePtr p),32*(8*p.w)⟩ : Region).Sub (cachedRegion p) := by
    rw [address]
    exact Offset.sub_base _ (by omega)
  intro r hr
  exact (h.separate r hr).sub_left sub

end VG.Proof.Ffdh.Arm
