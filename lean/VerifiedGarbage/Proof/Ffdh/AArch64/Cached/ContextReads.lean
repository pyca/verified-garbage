module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Context
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.ReadEnv
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.Ring

/-! The reviewed canonical context supplies all native comb reads and values. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Proof.Bignum

theorem context_readEnv {p : Parameters} {s : State} {count : Nat} {dom bs : List Byte}
 (words : p.w=Spec.Rsa.modulusWords p.k) (modulus : p.P=(Spec.Ffdh.domainOf p.k dom).p)
 (generator : p.G=(Spec.Ffdh.domainOf p.k dom).g) (policy : p.N=Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k dom))
 (pointer : p.table=p.ctx+BitVec.ofNat 64 (24+16*p.w))
 (length : p.k≤dom.length) (valid : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (dom.take p.k)) p.k=true)
 (canonical : Spec.Ffdh.generationContextAt s.mem p.ctx count p.k dom)
 (scalar : Source p.src bs s) (scalarLength : bs.length=p.k)
 (scalarOutside : ∀ i<bs.length,p.Z≤ofs p.B (p.src+BitVec.ofNat 64 i))
 (readable : ∀ i<count,InRegions (s.rd++s.wr) (p.ctx+BitVec.ofNat 64 (8*i)) 8)
 (outside : ∀ i<8*count,p.Z≤ofs p.B (p.ctx+BitVec.ofNat 64 i)) : ReadEnv p bs s := by
 have countEq : count=3+34*p.w := by rw [context_words_count canonical,words]
 have address (j i : Nat) : off p.table (8*p.w*j+8*i)=p.ctx+BitVec.ofNat 64 (8*(3+(2+j)*p.w+i)) := by
  rw [pointer]
  unfold off
  rw [BitVec.add_assoc,←BitVec.ofNat_add]
  congr 2
  ring
 have fit (j i : Nat) (hj : j<32) (hi : i<p.w) : 3+(2+j)*p.w+i<count := by
  have multiple := Nat.mul_le_mul_right p.w (show 2+j≤33 by omega)
  rw [countEq]
  omega
 refine ⟨scalar,scalarLength,scalarOutside,?_,?_,?_⟩
 · intro j hj i hi
   rw [address]
   exact readable _ (fit j i hj hi)
 · intro j hj i hi b hb
   rw [address,BitVec.add_assoc,←BitVec.ofNat_add]
   exact outside _ (by have := fit j i hj hi;omega)
 · intro j hj
   have entry := context_table_entry length valid canonical hj
   have equal : wv s.mem p.table (8*p.w*j) p.w=wv s.mem p.ctx (24+16*p.w+8*p.w*j) p.w := by
    apply wv_congr2
    intro i hi
    unfold word
    rw [address]
    congr 2
    ring
   rw [equal,words,modulus,generator,policy]
   exact entry

end VG.Proof.Ffdh.AArch64.Cached
