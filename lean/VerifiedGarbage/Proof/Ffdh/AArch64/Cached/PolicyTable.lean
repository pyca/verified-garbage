module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyRecordEnv
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Policy
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Ffdh.VettedGroupFacts

/-! ### `Ffdh.AArch64.Cached.PolicyMath`, which this module and modules that import it used -/

section

/-! ### `Ffdh.AArch64.Cached.PolicyBytes`, which only this module used -/

section

/-! The generated constant quadwords contain the exact domain-table bytes. -/

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached.PolicyFacts
open VG VG.Impl.Ffdh.AArch64.Cached.Policy

theorem groupBytes_length (g : Group) : g.bytes.length = 8 + 3 * g.len := by
  simp only [Group.bytes, wordBytes, List.length_append, List.length_map, List.length_range,
    Group.domain, VG.Proof.Rsa.i2osp_length]
  omega_using []

theorem tableBytes_length : tableBytes.length = 17744 := by
  simp only [tableBytes, groups, List.flatMap_cons, List.flatMap_nil, List.length_append,
    groupBytes_length, List.length_nil]

theorem tableWords_length : tableWords.length = 2218 := by
  simp only [tableWords, List.length_map, List.length_range, tableBytes_length]

theorem tableWords_getD {i : Nat} (hi : i < tableWords.length) :
    tableWords.getD i 0 = tableWord i := by
  simp only [tableWords, List.length_map, List.length_range] at hi
  simp only [tableWords, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hi, Option.map_some, Option.getD_some]

theorem tableWord_byte {i : Nat} (hi : i < tableBytes.length) :
    (tableWord (i / 8)).extractLsb' (8 * (i % 8)) 8 = tableBytes.getD i 0 := by
  unfold tableWord
  change ((show Mem from fun a : Addr => tableBytes.getD a.toNat 0).read  (BitVec.ofNat 64 (8 * (i / 8))) 8).extractLsb' (8 * (i % 8)) 8 = _
  rw [Mem.extractLsb'_read _ _ (by omega_using [])]
  simp only [BitVec.ofNat_add_ofNat, Nat.div_add_mod, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by rw [tableBytes_length] at hi; omega_using [hi])]

theorem table_held_byte {m : Mem} {base : Addr}
    (held : ∀ i < tableWords.length, m.readW (base + BitVec.ofNat 64 (8 * i)) 64 = tableWords.getD i 0)
    {i : Nat} (hi : i < tableBytes.length) :
    m (base + BitVec.ofNat 64 i) = tableBytes.getD i 0 := by
  have word := held (i / 8) (by rw [tableWords_length]; rw [tableBytes_length] at hi; omega_using [hi])
  rw [tableWords_getD (by rw [tableWords_length]; rw [tableBytes_length] at hi; omega_using [hi])] at word
  have addr : base + BitVec.ofNat 64 i =
      (base + BitVec.ofNat 64 (8 * (i / 8))) + BitVec.ofNat 64 (i % 8) := by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.div_add_mod]
  rw [addr, ← Mem.extractLsb'_read m _ (n := 8) (by omega_using []), ← tableWord_byte hi, ← word]
  rfl

end VG.Proof.Ffdh.AArch64.Cached.PolicyFacts

end

end

/-! The AArch64 recognizer's data is exactly the existing reviewed policy table.
These are value-level facts; instruction correctness is proved separately. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/PolicyFacts.lean`, which only this module imported.
section

/-! Compatibility names for the AArch64 policy's shared, ISA-independent facts. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached.PolicyFacts
export VG.Proof.Ffdh.VettedGroupFacts (group_bounds group_aligned width_unique width_unique_word domain_parts domain_encoding domainOf_injective group_take_two group_take_three domainOf_two domainOf_three NumericMatch numericRecognize group_parameters group_match_iff numericRecognize_spec recognize_spec)
end VG.Proof.Ffdh.AArch64.Cached.PolicyFacts
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached.Policy
open VG VG.Impl.Ffdh.AArch64.Cached.Policy

theorem tableBytes_length : tableBytes.length=17744 :=PolicyFacts.tableBytes_length

theorem tableWords_length : tableWords.length=2218 :=PolicyFacts.tableWords_length

/-- A complete byte comparison implements the common exact-group policy. -/
theorem recognize_spec {k : Nat} {dom : List Byte} (positive : 0 < k)
 (size : dom.length = 2*k ∨ dom.length = 3*k)
 (normalized : 2^(64*((k+7)/8-1)) ≤ Spec.Rsa.os2ip (dom.take k)) :
 VG.Impl.Ffdh.AArch64.Cached.Policy.recognizeList groups k dom =
 (Spec.Ffdh.vettedExponentBits (Spec.Ffdh.domainOf k dom)).getD 0 := by
 exact VG.Proof.Ffdh.AArch64.Cached.PolicyFacts.recognize_spec positive size normalized

end VG.Proof.Ffdh.AArch64.Cached.Policy

end

end

/-! The public table traversal implements the same reviewed exact-domain rule as ARMv7. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def PolicyTableAt (B p : Addr) : List Policy.Group → State → Prop
 | [],_ => True
 | g::gs,s => PolicyRecordAt B p g s ∧ PolicyTableAt B (off p (8+3*g.len)) gs s

theorem PolicyTableAt.after_mem {B p : Addr} {gs : List Policy.Group} {s t : State} {rs : List Reg}
 (h : PolicyTableAt B p gs s) (mem : t.mem=s.mem) (rest : Keep rs s t) : PolicyTableAt B p gs t := by
 induction gs generalizing p with
 | nil => trivial
 | cons g gs ih => exact ⟨h.1.after_mem mem rest,ih h.2⟩

def policyWidth (N k : Nat) (dom : List Byte) : List Policy.Group → Nat
 | [] => N
 | g::gs => if k=g.len ∧ dom=g.domain.take dom.length then min N g.bits else policyWidth N k dom gs

theorem policyWidth_rule (N k : Nat) (dom : List Byte) (gs : List Policy.Group)
 (positive : ∀ g∈gs,0<g.bits) :
 policyWidth N k dom gs=
  let cap := VG.Impl.Ffdh.AArch64.Cached.Policy.recognizeList gs k dom
  if cap=0 then N else min N cap := by
 induction gs with
 | nil => rfl
 | cons g gs ih =>
   simp only [policyWidth,VG.Impl.Ffdh.AArch64.Cached.Policy.recognizeList]
   change (if k=g.len ∧ dom=g.domain.take dom.length then min N g.bits else policyWidth N k dom gs)=
    (if (if g.len=k ∧ dom=g.domain.take dom.length then g.bits else
     VG.Impl.Ffdh.AArch64.Cached.Policy.recognizeList gs k dom)=0 then N else
     min N (if g.len=k ∧ dom=g.domain.take dom.length then g.bits else
     VG.Impl.Ffdh.AArch64.Cached.Policy.recognizeList gs k dom))
   by_cases yes : k=g.len ∧ dom=g.domain.take dom.length
   · have reverse : g.len=k ∧ dom=g.domain.take dom.length := ⟨yes.1.symm,yes.2⟩
     rw [ite_eq_left yes,ite_eq_left reverse,ite_eq_right (by have := positive g (by simp);omega_using [this])]
   · have no : ¬(g.len=k ∧ dom=g.domain.take dom.length) := fun h => yes ⟨h.1.symm,h.2⟩
     rw [ite_eq_right yes,ite_eq_right no]
     exact ih (fun a ha => positive a (by simp [ha]))

end VG.Proof.Ffdh.AArch64.Cached
