module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyTableBytes
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyMath
public import VerifiedGarbage.Proof.Framework.AArch64.StackScratchConsts
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Omega

/-! The emitted native quadwords contain exactly the reviewed public vetted-group table. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

private theorem singletonRead {name : String} {words : List (BitVec 64)} {st : Nat} {s : State}
 (hc : ConstsOk [(name,words)] st s) : InRegions (s.rd++s.wr) (s.syms name) (8*words.length) := by
 have member : (⟨s.syms name,8*words.length⟩ : Region)∈s.rd := by
  apply List.mem_of_mem_drop
  rw [hc.1]
  exact List.mem_cons_self
 exact ⟨_,List.mem_append_left _ member,Region.contains_self _ _⟩

private theorem singletonRegion {name : String} {words : List (BitVec 64)} {st : Nat} {s : State}
 (hc : ConstsOk [(name,words)] st s) :
 (s.syms name).toNat+8*words.length≤2^64 ∧
 (∀ r∈s.wr,(⟨s.syms name,8*words.length⟩ : Region).Disjoint r) := by
 have h := hc.2.2.1 (⟨s.syms name,8*words.length⟩ : Region) List.mem_cons_self
 exact ⟨h.1,h.2.1⟩

private theorem singletonHeld {name : String} {words : List (BitVec 64)} {st : Nat} {s : State}
 (hc : ConstsOk [(name,words)] st s) :
 ∀ j<words.length,s.mem.readW (s.syms name+BitVec.ofNat 64 (8*j)) 64=words.getD j 0 :=
 fun j hj => hc.2.1 (name,words) List.mem_cons_self j hj

private theorem constRead {st : Nat} {s : State} (hc : ConstsOk Policy.tableConsts st s) :
 InRegions (s.rd++s.wr) (s.syms Policy.tableSym) Policy.tableBytes.length := by
 have read := singletonRead hc
 simpa only [Policy.tableWords_length,Policy.tableBytes_length] using read

private theorem constBytes {st : Nat} {s : State} (hc : ConstsOk Policy.tableConsts st s) :
 Spec.Rsa.bytesAt s.mem (s.syms Policy.tableSym) Policy.tableBytes.length=Policy.tableBytes := by
 apply List.ext_getElem
 · simp only [Spec.Rsa.bytesAt,List.length_map,List.length_range]
 · intro i hi hj
   simp only [Spec.Rsa.bytesAt,List.getElem_map,List.getElem_range]
   have byte :=PolicyFacts.table_held_byte (singletonHeld hc) (i:=i) hj
   rw [byte]
   exact (List.getElem_eq_getD (h:=hj) 0).symm

theorem policyConsts_table {s : State} {B : Addr} {Z st : Nat}
 (hc : ConstsOk Policy.tableConsts st s) (scratch : Scr s B Z) (room : 256≤Z) :
 PolicyTableAt B (s.syms Policy.tableSym) Policy.groups s := by
 have region := singletonRegion hc
 have readable := constRead hc
 have bytes := constBytes hc
 have length := Policy.tableBytes_length
 have wordLength := Policy.tableWords_length
 have safe : ∀ i<Policy.tableBytes.length,8*VG.Impl.Ffdh.AArch64.Cached.sBits+8≤
    ofs B (s.syms Policy.tableSym+BitVec.ofNat 64 i) := by
  intro i hi
  obtain ⟨r,hr,contains⟩ := scratch.region (d:=0) (n:=Z) (by omega) (by omega)
  have containsB : r.Contains B Z := by simpa only [off,BitVec.add_zero] using contains
  have outside : Z≤ofs B (s.syms Policy.tableSym+BitVec.ofNat 64 i) := by
   by_contra no
   have within : ofs B (s.syms Policy.tableSym+BitVec.ofNat 64 i)<Z := by omega
   exact (region.2 r hr) _ (Offset.contains_base _ (by rw [wordLength];rw [length] at hi;omega)
    (by rw [length] at hi;omega)) (containsB.byte within)
  unfold VG.Impl.Ffdh.AArch64.Cached.sBits
  omega
 refine policyTableOfBytes (by rw [←show Policy.tableBytes=Policy.groups.flatMap Policy.Group.bytes from rfl,length];decide)
  readable bytes ?_ safe
 intro g hg
 simp only [Policy.groups,List.mem_cons,List.not_mem_nil,or_false] at hg
 rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

end VG.Proof.Ffdh.AArch64.Cached
