module

public import VerifiedGarbage.Spec.Ffdh.GenerationPrecompute
import VerifiedGarbage.Proof.Rsa.FixedBaseCombTable
public import VerifiedGarbage.Spec.Rsa.FixedBaseComb

/-! Canonical words, headers, and entry slices of a reusable generation context. -/

@[expose] public section
namespace VG.Proof.Ffdh
open VG.Spec.Rsa (toWords powMod modulusWords)
open VG.Spec.Ffdh (domainOf generationScalarBits)
open VG.Proof.Rsa.FixedBaseComb (toWords_length table_length table_entry)

/-- The serialization obtained whenever the trusted precomputation succeeds. -/
def generationValues (pLen : Nat) (dom : List Byte) : List (BitVec 64) :=
  let a := domainOf pLen dom
  let bits := generationScalarBits a
  let w := modulusWords pLen
  [BitVec.ofNat 64 bits,BitVec.ofNat 64 ((bits+7)/8),
    BitVec.ofNat 64 (VG.Spec.Rsa.FixedBaseComb.rows bits)] ++
  toWords a.p w ++ toWords (2^(128*w)%a.p) w ++
    VG.Spec.Rsa.FixedBaseComb.table a.p a.g bits w

theorem generationPrecompute_eq {pLen : Nat} {dom : List Byte}
    (length : pLen≤dom.length)
    (valid : VG.Spec.Rsa.modulusValid (VG.Spec.Rsa.os2ip (dom.take pLen)) pLen = true) :
    VG.Spec.Ffdh.generationPrecompute pLen dom = some (generationValues pLen dom) := by
  have len : (dom.take pLen).length=pLen := by simp only [List.length_take]; omega
  simp only [VG.Spec.Ffdh.generationPrecompute,VG.Spec.Rsa.FixedBaseComb.precompute,
    VG.Spec.Rsa.publicPrecompute,len,valid,↓reduceIte,Option.bind_eq_bind,Option.bind_some,Option.pure_def,generationValues,
    VG.Spec.Ffdh.domainOf,List.append_assoc]

theorem generationValues_length (pLen : Nat) (dom : List Byte) :
    (generationValues pLen dom).length = VG.Spec.Ffdh.generationPrecomputedWords pLen := by
  simp only [generationValues,List.length_append,List.length_cons,List.length_nil,toWords_length,
    table_length,VG.Spec.Ffdh.generationPrecomputedWords,VG.Spec.Rsa.FixedBaseComb.precomputedWords,
    VG.Spec.Rsa.precomputedWords,VG.Spec.Rsa.FixedBaseComb.entries,VG.Spec.Rsa.FixedBaseComb.teeth]
  omega

theorem generationValues_headers (pLen : Nat) (dom : List Byte) :
    let bits := generationScalarBits (domainOf pLen dom)
    (generationValues pLen dom).take 3 = [BitVec.ofNat 64 bits,BitVec.ofNat 64 ((bits+7)/8),
      BitVec.ofNat 64 (VG.Spec.Rsa.FixedBaseComb.rows bits)] := by
  simp only [generationValues,List.cons_append,List.nil_append,List.take_succ_cons,List.take_zero]

theorem generationValues_montgomery (pLen : Nat) (dom : List Byte) :
    let a := domainOf pLen dom
    let w := modulusWords pLen
    ((generationValues pLen dom).drop 3).take (2*w) =
      toWords a.p w ++ toWords (2^(128*w)%a.p) w := by
  simp only [generationValues,List.cons_append,List.nil_append,List.drop_succ_cons,List.drop_zero]
  have len : (toWords (domainOf pLen dom).p (modulusWords pLen) ++
      toWords (2^(128*modulusWords pLen)%(domainOf pLen dom).p) (modulusWords pLen)).length =
      2*modulusWords pLen := by rw [List.length_append,toWords_length,toWords_length]; omega
  rw [← len,List.take_left]

theorem generationValues_entry (pLen : Nat) (dom : List Byte) (a : Nat) (ha : a<32) :
    let g := domainOf pLen dom
    let bits := generationScalarBits g
    let w := modulusWords pLen
    ((generationValues pLen dom).drop (3+(2+a)*w)).take w =
      toWords (powMod g.g (VG.Spec.Rsa.FixedBaseComb.exponent bits a) g.p * 2^(64*w)%g.p) w := by
  dsimp only
  let w := modulusWords pLen
  have preLength : (toWords (domainOf pLen dom).p w ++
      toWords (2^(128*w)%(domainOf pLen dom).p) w).length = 2*w := by
    rw [List.length_append,toWords_length,toWords_length]; omega
  rw [show 3+(2+a)*w = 3+(2*w+a*w) by rw [Nat.add_mul]]
  rw [← List.drop_drop (i := 2*w+a*w) (j := 3)]
  simp only [generationValues,List.cons_append,List.nil_append,List.drop_succ_cons,List.drop_zero]
  rw [List.drop_append]
  rw [List.drop_eq_nil_of_le (by rw [preLength]; omega),List.nil_append,preLength]
  rw [show 2*w+a*w-2*w=a*w by omega]
  exact table_entry _ _ _ _ _ ha

end VG.Proof.Ffdh
