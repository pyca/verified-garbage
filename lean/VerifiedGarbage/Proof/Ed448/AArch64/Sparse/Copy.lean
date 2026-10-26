module

import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Recode
import VerifiedGarbage.Proof.X448.AArch64.Iter
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AddrArith
import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Recode
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X448.AArch64.Mem
import VerifiedGarbage.Proof.X448.AArch64.BitWrite

/-! Preserve signature digits while the challenge reuses the bit buffer. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.Ed448.AArch64.Sparse
open VG.Impl.X448.AArch64 (BITS)
open VG.Proof.X448.AArch64 (Scr Keeps Outside off ofs read1_eq write1_eq writeW8_apply
  writeW8_outside ofs_off' off_eq_iff)

private theorem byte_rt : ∀ b : BitVec 8,
    (b.setWidth 32 |>.setWidth 64 |>.setWidth 32 |>.setWidth 8)=b := by decide +kernel

private theorem copySetup_ok {s:State} {base:Addr} (hs:Scr s base) :
    WP isa (.block [.addImm .x .x10 .x3 3400,.addImm .x .x10 .x10 3400]) s fun u =>
      u.gpr .x10=off base SDIG ∧ Keeps [.x10] s u ∧ u.mem=s.mem := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,State.read,Size.bits,Nat.reduceLT,
    ite_true,RegUpd.gpr_write,BitVec.setWidth_eq,hs.x3,Option.some.injEq,exists_eq_left']
  refine ⟨?_,⟨fun r hr => ?_,rfl,rfl⟩,rfl⟩
  · rw [Offset.add_add]
    rfl
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_write,hr,ite_false]

private theorem copyOne_ok {s:State} {base:Addr} (hs:Scr s base)
    (hp:s.gpr .x10=off base SDIG) {i:Nat} (hi:i<464) :
    WP isa (.block [.ldrb .x4 .x3 (BITS+i),.strb .x4 .x10 i]) s fun u =>
      u.mem=s.mem.writeW (off base (SDIG+i)) (s.mem (off base (BITS+i))) ∧
      Keeps [.x4] s u := by
  have hr:=hs.read (d:=BITS+i) (n:=1) (by simp only [BITS];omega)
  have hw:=hs.write (d:=SDIG+i) (n:=1) (by simp only [SDIG];omega)
  have es:BITS+i<4096 := by simp only [BITS];omega
  have ei:i<4096 := by omega
  have ha:off base SDIG+BitVec.ofNat 64 i=off base (SDIG+i) := Offset.add_add _ _ _
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,State.read,Size.bits,addr,
    Nat.mod_one,es,ei,and_self,ite_true,hs.x3,hp,ha,State.load,State.store,hr,hw,
    read1_eq,write1_eq,RegUpd.gpr_write,RegUpd.rd_write,RegUpd.wr_write,RegUpd.mem_write,
    Option.bind_some,Option.map_some,reduceCtorEq,ite_false,byte_rt,Option.some.injEq,exists_eq_left']
  refine ⟨by trivial,⟨fun r h => ?_,rfl,rfl⟩⟩
  simp only [List.mem_singleton] at h
  simp only [RegUpd.gpr_write,h,ite_false]

private theorem copyLoop_ok {s:State} {base:Addr} (hs:Scr s base)
    (hp:s.gpr .x10=off base SDIG) {n:Nat} (hn:n≤464) :
    WP isa (.block ((List.range n).flatMap fun i =>
      [.ldrb .x4 .x3 (BITS+i),.strb .x4 .x10 i])) s fun u =>
      (∀ i<n,u.mem (off base (SDIG+i))=s.mem (off base (BITS+i))) ∧
      Outside base SDIG 464 s.mem u.mem ∧ Keeps [.x4] s u := by
  induction n with
  | zero => exact WP.block_nil ⟨fun _ h => by omega,Outside.refl _ _ _ _,Keeps.refl _ _⟩
  | succ n ih =>
    rw [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨ht,fo,kt⟩ => ?_
    refine WP.mono (copyOne_ok (hs.of_keeps kt (by decide))
      ((kt.1 _ (by decide)).trans hp) (by omega)) fun u ⟨um,ku⟩ => ?_
    refine ⟨fun i hi => ?_,?_,kt.trans ku⟩
    · have hsrc:t.mem (off base (BITS+n))=s.mem (off base (BITS+n)) :=
        fo _ (Or.inl (by rw [ofs_off' base (by simp only [BITS];omega)];simp only [BITS,SDIG];omega))
      rw [um,writeW8_apply]
      simp only [off_eq_iff base (d:=SDIG+i) (e:=SDIG+n)
        (by simp only [SDIG];omega) (by simp only [SDIG];omega)]
      by_cases he:i=n
      · subst i
        rw [ite_eq_left rfl,hsrc]
      · rw [ite_eq_right (by omega)]
        exact ht i (by omega)
    · rw [um]
      refine fo.trans ?_
      intro x hx
      exact writeW8_outside _ base _ (by simp only [SDIG];omega) (by omega)

theorem copySignatureDigits_ok {s:State} {base:Addr} (hs:Scr s base) :
    WP isa (.block copySignatureDigits) s fun u =>
      (∀ i<464,u.mem (off base (SDIG+i))=s.mem (off base (BITS+i))) ∧
      Outside base SDIG 464 s.mem u.mem ∧ Keeps [.x4,.x10] s u := by
  unfold copySignatureDigits
  rw [WP.block_append_iff]
  refine WP.mono (copySetup_ok hs) fun t ⟨tp,kt,tm⟩ => ?_
  refine WP.mono (copyLoop_ok (hs.of_keeps kt (by decide)) tp (Nat.le_refl 464))
    fun u ⟨hd,fo,ku⟩ => ?_
  rw [tm] at hd fo
  exact ⟨hd,fo,(kt.mono (by decide)).trans (ku.mono (by decide))⟩

end VG.Proof.Ed448.AArch64.Sparse
