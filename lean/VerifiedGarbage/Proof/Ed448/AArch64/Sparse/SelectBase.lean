module

public import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Table
import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.SelectCopy
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Ed448.AArch64.Window.Select

/-! Direct public indexing of the immutable odd affine base-point table. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.Ed448.AArch64.Sparse
open VG.Proof.X448.AArch64 (Scr Keeps Outside off ofs word)
open VG.Proof.Ed448.AArch64.Window (dst)

structure BaseTableAt (s:State) (base p:Addr) : Prop where
  read : InRegions (s.rd++s.wr) p 8192
  far : ∀ i<8192,8192≤ofs base (p+BitVec.ofNat 64 i)
  val : ∀ i<1024,s.mem.readW (p+BitVec.ofNat 64 (8*i)) 64=baseWord i

private theorem address_fact : ∀ m<128,
    (BitVec.ofNat 64 m>>>1)<<<7=BitVec.ofNat 64 (128*(m/2)) := by decide +kernel

private def baseAddress : List Instr :=
  [.lsr .x .x11 .x11 1,.adrSym .x8 baseSym,.lsl .x .x9 .x11 7,.add .x .x8 .x8 .x9]

private theorem baseAddress_ok {s:State} {m:Nat} (hm:m<128)
    (h11:s.gpr .x11=BitVec.ofNat 64 m) :
    WP isa (.block baseAddress) s fun t =>
      t.gpr .x8=off (s.syms baseSym) (128*(m/2)) ∧
      Keeps [.x11,.x8,.x9] s t ∧ t.mem=s.mem := by
  apply WP.of_runBlock
  simp only [baseAddress,runBlock_cons,runStep_some,runBlock_nil,exec,State.read,Size.bits,
    Nat.reduceLT,ite_true,BitVec.setWidth_eq,h11,State.write,
    ite_false,reduceCtorEq,address_fact m hm,Option.some.injEq,exists_eq_left']
  refine ⟨by trivial,⟨fun r hr => ?_,rfl,rfl⟩,by trivial⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
  simp only [hr.1,hr.2.1,hr.2.2,ite_false]

theorem selectBase_ok {s:State} {base:Addr} (hs:Scr s base)
    (ht:BaseTableAt s base (s.syms baseSym)) {m:Nat}
    (hm:m<128) (h11:s.gpr .x11=BitVec.ofNat 64 m) :
    WP isa (.block selectBase) s fun t =>
      (∀ w<16,word t.mem base (dst w)=baseWord (16*(m/2)+w)) ∧
      Outside base 832 192 s.mem t.mem ∧ Keeps [.x11,.x8,.x9,.x4] s t := by
  have he:selectBase=baseAddress++copyWords 16 0:=rfl
  rw [he,WP.block_append_iff]
  refine WP.mono (baseAddress_ok hm h11) fun a ⟨a8,ka,am⟩ => ?_
  have ho:∀ w,off (s.syms baseSym) (128*(m/2))+BitVec.ofNat 64 (0+8*w)=
      s.syms baseSym+BitVec.ofNat 64 (8*(16*(m/2)+w)) := by
    intro w
    rw [off,Offset.add_add]
    exact congrArg (fun n => s.syms baseSym+BitVec.ofNat 64 n) (by omega)
  refine WP.mono (copyWords_ok (n:=16) (a:=0) (hs.of_keeps ka (by decide)) a8 (by decide) (by decide) (by decide)
    (fun w hw => by
      rw [ka.2.1,ka.2.2,ho w]
      exact VG.CallLay.inRegions_sub ht.read (by omega) (by decide))
    (fun w hw j hj => by
      rw [ho w,Offset.add_add]
      exact Nat.le_trans (by decide) (ht.far _ (by omega)))) fun t ⟨tv,fo,kt⟩ => ?_
  refine ⟨fun w hw => ?_,?_,(ka.mono (by decide)).trans (kt.mono (by decide))⟩
  · rw [tv w hw,ho w,am,ht.val _ (by omega)]
  · rw [am] at fo
    exact fo

end VG.Proof.Ed448.AArch64.Sparse
