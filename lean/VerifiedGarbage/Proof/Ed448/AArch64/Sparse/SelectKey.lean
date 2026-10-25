module

public import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Table
import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.SelectCopy
import VerifiedGarbage.Proof.X448.AArch64.Iter
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Ed448.AArch64.Window.Select

/-! Direct public indexing of one of eight projective odd key multiples. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.Ed448.AArch64.Sparse
open VG.Impl.Ed448.AArch64 (TAB)
open VG.Proof.X448.AArch64 (Scr Keeps Outside off ofs word ofs_off')
open VG.Proof.Ed448.AArch64.Window (dst tw)

private theorem address_fact : ∀ m<16,
    ((BitVec.ofNat 64 m>>>1)<<<7)+((BitVec.ofNat 64 m>>>1)<<<6)=
      BitVec.ofNat 64 (192*(m/2)) := by decide +kernel

private def keyAddress : List Instr :=
  [.lsr .x .x11 .x11 1,.lsl .x .x8 .x11 7,.lsl .x .x9 .x11 6,
   .add .x .x8 .x8 .x9,.add .x .x8 .x8 .x3]

private theorem keyAddress_ok {s:State} {base:Addr} (hs:Scr s base) {m:Nat}
    (hm:m<16) (h11:s.gpr .x11=BitVec.ofNat 64 m) :
    WP isa (.block keyAddress) s fun t =>
      t.gpr .x8=off base (192*(m/2)) ∧ Keeps [.x11,.x8,.x9] s t ∧ t.mem=s.mem := by
  apply WP.of_runBlock
  simp only [keyAddress,runBlock_cons,runStep_some,runBlock_nil,exec,State.read,Size.bits,
    Nat.reduceLT,ite_true,RegUpd.gpr_write,BitVec.setWidth_eq,h11,hs.x3,
    ite_false,reduceCtorEq,address_fact m hm,Option.some.injEq,exists_eq_left']
  refine ⟨BitVec.add_comm _ _,⟨fun r hr => ?_,rfl,rfl⟩,rfl⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
  simp only [RegUpd.gpr_write,hr.1,hr.2.1,hr.2.2,ite_false]

theorem selectKey_ok {s:State} {base:Addr} (hs:Scr s base) {m:Nat}
    (hm:m<16) (h11:s.gpr .x11=BitVec.ofNat 64 m) :
    WP isa (.block selectKey) s fun t =>
      (∀ w<24,word t.mem base (dst w)=tw s.mem base (m/2) w) ∧
      Outside base 832 384 s.mem t.mem ∧ Keeps [.x11,.x8,.x9,.x4] s t := by
  have he:selectKey=keyAddress++copyWords 24 TAB:=rfl
  rw [he,WP.block_append_iff]
  refine WP.mono (keyAddress_ok hs hm h11) fun a ⟨a8,ka,am⟩ => ?_
  have ha:=hs.of_keeps ka (by decide)
  have ho:∀ w<24,off base (192*(m/2))+BitVec.ofNat 64 (TAB+8*w)=
      off base (TAB+192*(m/2)+8*w) := by
    intro w _
    rw [off,off,Offset.add_add]
    exact congrArg (fun n => base+BitVec.ofNat 64 n) (by omega)
  refine WP.mono (copyWords_ok ha a8 (Nat.le_refl 24) (by decide) (by decide)
    (fun w hw => by rw [ho w hw];exact ha.read (by simp only [TAB];omega))
    (fun w hw j hj => by
      rw [ho w hw,VG.Proof.X448.AArch64.ofs_off base (by simp only [TAB];omega)]
      simp only [TAB]
      omega)) fun t ⟨tv,fo,kt⟩ => ?_
  refine ⟨fun w hw => ?_,?_,(ka.mono (by decide)).trans (kt.mono (by decide))⟩
  · rw [tv w hw,ho w hw,am]
    rfl
  · rw [am] at fo
    exact fo

end VG.Proof.Ed448.AArch64.Sparse
