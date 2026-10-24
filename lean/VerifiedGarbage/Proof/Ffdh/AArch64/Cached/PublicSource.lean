module

public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Source
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PublicFrame
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.GeneratorSource
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Omega

/-! Checked domain bytes are immutable throughout context creation. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

structure PublicSource (p : Parameters) (ptr : Addr) (bs : List Byte) (s : State) : Prop extends Source ptr bs s where
 scratchOutside : ∀ i<bs.length,p.Z≤ofs p.B (ptr+BitVec.ofNat 64 i)
 contextOutside : ∀ i<bs.length,8*(3+34*p.w)≤ofs p.ctx (ptr+BitVec.ofNat 64 i)

theorem PublicSource.after {p : Parameters} {ptr : Addr} {bs : List Byte} {s t : State} {rs : List Reg}
 (source : PublicSource p ptr bs s) (frame : PublicFrame p s.mem t.mem) (rest : Keep rs s t) : PublicSource p ptr bs t := by
 refine ⟨⟨?_,?_⟩,source.scratchOutside,source.contextOutside⟩
 · intro i hi;rw [rest.rd,rest.wr];exact source.readable i hi
 · intro i hi
   apply Eq.trans (frame _ ?_) (source.bytes i hi)
   intro r hr
   simp only [publicWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
   rcases hr with rfl|rfl
   · have out := source.scratchOutside i hi
     change ¬ofs p.B (ptr+BitVec.ofNat 64 i)+1≤p.Z
     omega
   · have out := source.contextOutside i hi
     change ¬ofs p.ctx (ptr+BitVec.ofNat 64 i)+1≤8*(3+34*p.w)
     omega

theorem PublicSource.toSrc {p : Parameters} {ptr : Addr} {bs : List Byte} {s : State}
 (source : PublicSource p ptr bs s) : Src s p.B p.Z ptr bs := by
 refine ⟨source.readable,?_,source.scratchOutside⟩
 intro i hi
 simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some] using source.bytes i hi

theorem PublicSource.take {p : Parameters} {ptr : Addr} {bs : List Byte} {s : State}
 (source : PublicSource p ptr bs s) (n : Nat) : PublicSource p ptr (bs.take n) s := by
 refine ⟨source.toSource.take n,?_,?_⟩
 all_goals intro i hi;have bound : i<bs.length := by rw [List.length_take] at hi;omega
 · exact source.scratchOutside i bound
 · exact source.contextOutside i bound

theorem PublicSource.drop {p : Parameters} {ptr : Addr} {bs : List Byte} {s : State}
 (source : PublicSource p ptr bs s) (n : Nat) : PublicSource p (ptr+BitVec.ofNat 64 n) (bs.drop n) s := by
 refine ⟨source.toSource.drop n,?_,?_⟩
 all_goals intro i hi;have bound : n+i<bs.length := by rw [List.length_drop] at hi;omega
 · simpa only [BitVec.ofNat_add,BitVec.add_assoc] using source.scratchOutside (n+i) bound
 · simpa only [BitVec.ofNat_add,BitVec.add_assoc] using source.contextOutside (n+i) bound

theorem PublicSource.generator {p : Parameters} {ptr : Addr} {dom : List Byte} {s : State}
 (source : PublicSource p ptr dom s) (length : 2*p.k≤dom.length)
 (value : p.G=(Spec.Ffdh.domainOf p.k dom).g) :
 GeneratorSource p (ptr+BitVec.ofNat 64 p.k) ((dom.drop p.k).take p.k) s := by
 have bytes := (source.drop p.k).take p.k
 refine ⟨bytes.toSrc,?_,?_,bytes.contextOutside⟩
 · simp only [List.length_take,List.length_drop];omega
 · exact value.symm

end VG.Proof.Ffdh.AArch64.Cached
