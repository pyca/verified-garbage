module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MixedZero
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.Block

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64

def mixedSelectPairArith (r0 r1 : Reg) : List Instr := [
  .cselc .x r0 r0 .x20 .ne,.cselc .x r1 r1 .x21 .ne]

theorem mixed_select_pair_arith (s : State) (r0 r1 : Reg)
    (h01 : r0≠r1) (h21 : Reg.x21≠r0) :
    WP isa (.block (mixedSelectPairArith r0 r1)) s fun t =>
      t.gpr r0=(if s.zf then s.gpr .x20 else s.gpr r0) ∧
      t.gpr r1=(if s.zf then s.gpr .x21 else s.gpr r1) ∧
      t.zf=s.zf ∧ Keeps [r0,r1] s t := by
  apply WP.of_runBlock
  simp only [mixedSelectPairArith,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,
    RegUpd.gpr_write,RegUpd.zf_write,CondCode.holds,BitVec.setWidth_eq,
    h01,h01.symm,h21,ite_false,ite_true,Option.some.injEq,exists_eq_left']
  refine ⟨?_,?_,True.intro,⟨?_,?_,?_,?_,?_⟩⟩
  · cases s.zf <;> rfl
  · cases s.zf <;> rfl
  · intro r hr
    simp only [List.mem_cons,not_or] at hr
    simp only [RegUpd.gpr_write,hr.1,hr.2,ite_false]
  · simp only [RegUpd.mem_write]
  · simp only [RegUpd.rd_write]
  · simp only [RegUpd.wr_write]
  · simp only [RegUpd.sp_write]

theorem mixed_select_word_arith (s : State) (r : Reg) :
    WP isa (.block [.cselc .x r r .x20 .ne]) s fun t =>
      t.gpr r=(if s.zf then s.gpr .x20 else s.gpr r) ∧ t.zf=s.zf ∧ Keeps [r] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,
    RegUpd.gpr_write,RegUpd.zf_write,CondCode.holds,BitVec.setWidth_eq,ite_true,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,True.intro,⟨?_,?_,?_,?_,?_⟩⟩
  · cases s.zf <;> rfl
  · intro q hq
    simp only [List.mem_singleton] at hq
    simp only [RegUpd.gpr_write,hq,ite_false]
  · simp only [RegUpd.mem_write]
  · simp only [RegUpd.rd_write]
  · simp only [RegUpd.wr_write]
  · simp only [RegUpd.sp_write]

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64

theorem mixed_ldR_ok {s : State} {p : Addr} {rn : Reg} {size d : Nat}
    (hp : Ptr s rn p size) (hd : d+8≤size) (hd8 : d%8=0) (r : Reg) :
    WP isa (.block [.ldr .x r rn d]) s fun t =>
      t.gpr r=word s.mem p d ∧ Keeps [r] s t ∧ t.zf=s.zf := by
  apply WP.of_runBlock
  simp only [runBlock_cons,exec_ldR hp hd hd8,runStep_some,runBlock_nil,
    RegUpd.gpr_write_self,BitVec.setWidth_eq,Option.some.injEq,exists_eq_left']
  refine ⟨True.intro,⟨?_,rfl,rfl,rfl,rfl⟩,rfl⟩
  intro r' hr
  simp only [List.mem_singleton] at hr
  exact RegUpd.gpr_write_of_ne _ _ _ hr

theorem mixed_two_loads_ok {s : State} {p : Addr} {rn r0 r1 : Reg} {size d : Nat}
    (hp : Ptr s rn p size) (hd : d+16≤size) (hd8 : d%8=0) (hr : rn≠r0) (h01 : r0≠r1) :
    WP isa (.block (twoLoads rn r0 r1 d)) s fun t =>
      t.gpr r0=word s.mem p d ∧ t.gpr r1=word s.mem p (d+8) ∧ Keeps [r0,r1] s t ∧ t.zf=s.zf := by
  have hs : twoLoads rn r0 r1 d=([.ldr .x r0 rn d] : List Instr)++[.ldr .x r1 rn (d+8)] := rfl
  rw [hs,WP.block_append_iff]
  refine WP.mono (mixed_ldR_ok hp (by omega_arith) hd8 r0) fun u ⟨e0,k0,z0⟩ => ?_
  refine WP.mono (mixed_ldR_ok (hp.of_keeps k0 (by simpa only [List.mem_singleton] using hr))
    (by omega_arith) (by omega_arith) r1) fun t ⟨e1,k1,z1⟩ => ?_
  exact ⟨(k1.gpr r0 (by simpa only [List.mem_singleton] using h01)).trans e0,by rw [e1,k0.mem],
    (k0.mono (by simp)).trans (k1.mono (by simp)),z1.trans z0⟩

def mixedSelectPair (r0 r1 : Reg) (a b : Nat) : List Instr :=
  twoLoads .x30 r0 r1 a++(twoLoads .x28 .x20 .x21 b++mixedSelectPairArith r0 r1)

theorem mixed_select_pair_ok {s : State} {pa pb : Addr} {size cap a b : Nat} (r0 r1 : Reg)
    (hp : Ptr s .x30 pa size) (hq : Ptr s .x28 pb cap)
    (ha : a+16≤size) (hb : b+16≤cap) (ha8 : a%8=0) (hb8 : b%8=0)
    (h01 : r0≠r1) (fresh : ∀r∈[r0,r1],r∉([.x20,.x21,.x28,.x30] : List Reg)) :
    WP isa (.block (mixedSelectPair r0 r1 a b)) s fun t =>
      t.gpr r0=(if s.zf then word s.mem pb b else word s.mem pa a) ∧
      t.gpr r1=(if s.zf then word s.mem pb (b+8) else word s.mem pa (a+8)) ∧
      t.zf=s.zf ∧ Keeps [r0,r1,.x20,.x21] s t := by
  have f0 := fresh r0 (by simp)
  have f1 := fresh r1 (by simp)
  have nr0 : Reg.x30≠r0 := by intro e; subst r0; simp at f0
  have n28 : Reg.x28∉[r0,r1] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    constructor <;> intro e
    · subst r0; simp at f0
    · subst r1; simp at f1
  have out0 : r0∉([.x20,.x21] : List Reg) := fun h => f0 (by simp_all)
  have out1 : r1∉([.x20,.x21] : List Reg) := fun h => f1 (by simp_all)
  have h21 : Reg.x21≠r0 := by intro e; subst r0; simp at f0
  rw [mixedSelectPair,WP.block_append_iff]
  refine WP.mono (mixed_two_loads_ok hp ha ha8 nr0 h01) fun u ⟨a0,a1,ku,zu⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mixed_two_loads_ok (hq.of_keeps ku n28) hb hb8 (by decide) (by decide))
    fun v ⟨b0,b1,kv,zv⟩ => ?_
  refine WP.mono (mixed_select_pair_arith v r0 r1 h01 h21) fun t ⟨e0,e1,zt,kt⟩ => ?_
  rw [zv,zu,b0,ku.mem,kv.gpr r0 out0,a0] at e0
  rw [zv,zu,b1,ku.mem,kv.gpr r1 out1,a1] at e1
  exact ⟨e0,e1,zt.trans (zv.trans zu),
    (ku.mono (by simp)).trans ((kv.mono (by simp)).trans (kt.mono (by simp)))⟩

def mixedSelectWord (r : Reg) (a b : Nat) : List Instr :=
  [.ldr .x r .x30 a,.ldr .x .x20 .x28 b,.cselc .x r r .x20 .ne]

theorem mixed_select_word_ok {s : State} {pa pb : Addr} {size cap a b : Nat} (r : Reg)
    (hp : Ptr s .x30 pa size) (hq : Ptr s .x28 pb cap)
    (ha : a+8≤size) (hb : b+8≤cap) (ha8 : a%8=0) (hb8 : b%8=0)
    (fresh : r∉([.x20,.x28,.x30] : List Reg)) :
    WP isa (.block (mixedSelectWord r a b)) s fun t =>
      t.gpr r=(if s.zf then word s.mem pb b else word s.mem pa a) ∧
      t.zf=s.zf ∧ Keeps [r,.x20] s t := by
  have n28 : Reg.x28≠r := by intro e; subst r; simp at fresh
  have n20 : r≠Reg.x20 := by intro e; subst r; simp at fresh
  have hs : mixedSelectWord r a b=([.ldr .x r .x30 a] : List Instr)++
      ([.ldr .x .x20 .x28 b]++[.cselc .x r r .x20 .ne]) := rfl
  rw [hs,WP.block_append_iff]
  refine WP.mono (mixed_ldR_ok hp ha ha8 r) fun u ⟨ea,ku,zu⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mixed_ldR_ok (hq.of_keeps ku (by simpa only [List.mem_singleton] using n28)) hb hb8 .x20)
    fun v ⟨eb,kv,zv⟩ => ?_
  refine WP.mono (mixed_select_word_arith v r) fun t ⟨e,zt,kt⟩ => ?_
  rw [zv,zu,eb,ku.mem,kv.gpr r (by simpa only [List.mem_singleton] using n20),ea] at e
  exact ⟨e,zt.trans (zv.trans zu),(ku.mono (by simp)).trans ((kv.mono (by simp)).trans (kt.mono (by simp)))⟩

end VG.Proof.Mont.AArch64.P521Field
