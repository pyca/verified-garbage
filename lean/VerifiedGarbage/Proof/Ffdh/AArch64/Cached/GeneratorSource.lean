module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.ContextBuild
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.LoadArray
import VerifiedGarbage.Proof.Framework.Omega

/-! The checked generator's public bytes remain outside both working buffers. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

structure GeneratorSource (p : Parameters) (ptr : Addr) (bs : List Byte) (s : State) : Prop where
 source : Src s p.B p.Z ptr bs
 length : bs.length=p.k
 value : Spec.Rsa.os2ip bs=p.G
 separate : ∀ i<bs.length,8*(3+34*p.w)≤ofs p.ctx (ptr+BitVec.ofNat 64 i)

theorem GeneratorSource.after_inscr {p : Parameters} {ptr : Addr} {bs : List Byte} {s t : State} {rs : List Reg}
 (h : GeneratorSource p ptr bs s) (frame : InScr p.B p.Z s.mem t.mem) (rest : Keep rs s t) : GeneratorSource p ptr bs t :=
 ⟨h.source.congrK frame rest,h.length,h.value,h.separate⟩

theorem GeneratorSource.after_entry {p : Parameters} {ptr : Addr} {bs : List Byte} {s t : State} {rs : List Reg} {j : Nat}
 (h : GeneratorSource p ptr bs s) (frame : Outside p.ctx (entryOffset p.w j) (8*p.w) s.mem t.mem)
 (inside : j<32) (rest : Keep rs s t) : GeneratorSource p ptr bs t := by
 refine ⟨⟨?_,?_,h.source.out⟩,h.length,h.value,h.separate⟩
 · intro i hi;rw [rest.rd,rest.wr];exact h.source.rd i hi
 · intro i hi
   rw [frame _ (Or.inr (by have := entry_within p inside;have := h.separate i hi;omega))]
   exact h.source.val i hi

end VG.Proof.Ffdh.AArch64.Cached
