module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.GeneratorSource
import VerifiedGarbage.Proof.Framework.Omega

/-! A public generator source is disjoint from every portion of the writable context. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

theorem GeneratorSource.after_context {p : Parameters} {ptr : Addr} {bs : List Byte} {s t : State} {rs : List Reg} {d n : Nat}
 (h : GeneratorSource p ptr bs s) (frame : Outside p.ctx d n s.mem t.mem)
 (inside : d+n≤8*(3+34*p.w)) (rest : Keep rs s t) : GeneratorSource p ptr bs t := by
 refine ⟨⟨?_,?_,h.source.out⟩,h.length,h.value,h.separate⟩
 · intro i hi;rw [rest.rd,rest.wr];exact h.source.rd i hi
 · intro i hi
   rw [frame _ (Or.inr (by have :=h.separate i hi;omega))]
   exact h.source.val i hi

end VG.Proof.Ffdh.AArch64.Cached
