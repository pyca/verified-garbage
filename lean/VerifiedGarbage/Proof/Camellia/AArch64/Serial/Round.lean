module

public import VerifiedGarbage.Proof.Camellia.AArch64.Serial.Lookup
public import VerifiedGarbage.Proof.Camellia.AArch64.Serial.Linear
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Interleave

/-! # Scalar Feistel rounds with the register substitution table -/

@[expose] public section
namespace VG.Proof.Camellia.AArch64.Serial
open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Impl.Camellia.AArch64.Serial

theorem mixKey_run {s : State} {a : Reg} {k : Nat}
    (ha8 : a ≠ .x8) (hk : k < 34)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 (256+8*k)) 8) :
    ∃ t, runBlock isa (mixKey a k) s = some t ∧
      t.gpr .x10 = s.gpr a ^^^ rev64 (s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 (256+8*k)) 64) ∧
      (∀ r, r ≠ .x8 → r ≠ .x10 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v := by
  let u := s.write .x .x8 (s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 (256+8*k)) 64)
  let v := u.write .x .x8 (rev64 (u.gpr .x8))
  let t := v.write .x .x10 (v.read .x a ^^^ v.read .x .x8)
  refine ⟨t,?_,?_,?_,rfl,rfl,rfl,rfl,rfl⟩
  · rw [mixKey,runBlock_cons,exec_ldr_x ⟨by omega,by omega⟩ hr,runStep_some,
      runBlock_cons,exec_rev,runStep_some,runBlock_cons,exec_logic,runStep_some,runBlock_nil]
    rfl
  · simp only [t,v,u,gpr_write_self,State.read,Size.bits,BitVec.setWidth_eq,
      gpr_write_of_ne _ _ _ ha8]
  · intro r h8 h10
    simp only [t,v,u,gpr_write_of_ne _ _ _ h8,gpr_write_of_ne _ _ _ h10]

/-- One F application updates only the other Feistel half and its temporary registers. -/
theorem f_run {s : State} {a b : Reg} {k : Nat}
    (ha : a = .x6 ∨ a = .x7) (hb : b = .x6 ∨ b = .x7)
    (hk : k < 34) (hc : Constants s) (hm : Masks s) (ht : Table s)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 (256+8*k)) 8) :
    ∃ t, runBlock isa (f a b k) s = some t ∧
      t.gpr b = s.gpr b ^^^ Spec.Camellia.f (s.gpr a)
        (rev64 (s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 (256+8*k)) 64)) ∧
      Constants t ∧ Masks t ∧ Table t ∧
      (∀ r, r ≠ b → r ∉ [.x8,.x10,.x11,.x12,.x16,.x17] → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have ha8 : a ≠ .x8 := by rcases ha with rfl | rfl <;> decide
  have hb8 : b ≠ .x8 := by rcases hb with rfl | rfl <;> decide
  have hb10 : b ≠ .x10 := by rcases hb with rfl | rfl <;> decide
  have hbl : b ∉ [.x10,.x11,.x12,.x16,.x17] := by
    rcases hb with rfl | rfl <;> decide
  obtain ⟨u,ue,uv,ug,um,urd,uwr,usp,uvec⟩ := mixKey_run ha8 hk hr
  have uc : Constants u := by simpa only [Constants,uvec] using hc
  have ut : Table u := by simpa only [Table,uvec] using ht
  have umat : Masks u := by
    refine ⟨?_,?_,?_⟩
    · rw [uvec]; exact hm.1
    · rw [ug _ (by decide) (by decide)]; exact hm.2.1
    · rw [ug _ (by decide) (by decide)]; exact hm.2.2
  obtain ⟨v,ve,vv,vg,vm,vrd,vwr,vsp,vvec⟩ := substitute_run u uc umat ut
  obtain ⟨w,we,wv,wg,wm,wrd,wwr,wsp,wvec⟩ := linear_run v
  let t := w.write .x b (w.read .x b ^^^ w.read .x .x10)
  have wb : w.read .x b = s.gpr b := by
    simp only [State.read,Size.bits,BitVec.setWidth_eq,wg _ hbl,vg _ hb10,ug _ hb8 hb10]
  have val : w.read .x .x10 = Spec.Camellia.f (s.gpr a)
      (rev64 (s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 (256+8*k)) 64)) := by
    simp only [State.read,Size.bits,BitVec.setWidth_eq,wv,vv,uv]
    exact (f_eq _ _).symm
  have other : ∀ r, r ≠ b → r ∉ [.x8,.x10,.x11,.x12,.x16,.x17] → t.gpr r = s.gpr r := by
    intro r hr hn
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hn
    rw [gpr_write_of_ne _ _ _ hr,wg _ (by
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
      exact hn.2),vg _ hn.2.1,ug _ hn.1 hn.2.1]
  have tv : ∀ q, q ∉ [.v0,.v1,.v2,.v3] → t.v q = s.v q := by
    intro q hq
    rw [show t.v q = w.v q from rfl,wvec,vvec _ hq,uvec]
  have tt : Table t := by
    intro j hj
    rw [VG.AArch64.Tbl.tbyte_congr' (fun i hi => tv _ (by
      have hn := VG.AArch64.Tbl.treg_ne i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
      exact ⟨hn.1,hn.2.1,hn.2.2.1,hn.2.2.2.1⟩)) j hj]
    exact ht j hj
  refine ⟨t,?_,?_,?_,?_,tt,other,wm.trans (vm.trans um),
    wrd.trans (vrd.trans urd),wwr.trans (vwr.trans uwr),wsp.trans (vsp.trans usp)⟩
  · rw [f,VG.Interleave.runBlock_append,VG.Interleave.runBlock_append,
      VG.Interleave.runBlock_append,ue,Option.bind_some,ve,Option.bind_some,we,Option.bind_some]
    rfl
  · simp only [t,gpr_write_self,Size.bits,BitVec.setWidth_eq,wb,val]
  · exact ⟨(tv _ (by decide)).trans hc.1,(tv _ (by decide)).trans hc.2.1,
      (tv _ (by decide)).trans hc.2.2⟩
  · refine ⟨(tv _ (by decide)).trans hm.1,?_,?_⟩
    · rw [other _ (by rcases hb with rfl | rfl <;> decide) (by decide)]
      exact hm.2.1
    · rw [other _ (by rcases hb with rfl | rfl <;> decide) (by decide)]
      exact hm.2.2

end VG.Proof.Camellia.AArch64.Serial
