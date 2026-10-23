module

public import VerifiedGarbage.Proof.Sm4.AArch64.Serial.Lookup
public import VerifiedGarbage.Proof.Sm4.AArch64.Serial.Linear
public import VerifiedGarbage.Proof.Sm4.Rounds
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Interleave

/-! # Single-word SM4 rounds with register substitution -/

@[expose] public section

namespace VG.Proof.Sm4.AArch64.Serial

open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Impl.Sm4.AArch64.Serial

theorem wordReg_ne : ∀ j < 4, wordReg j ≠ .x10 ∧ wordReg j ≠ .x11 := by decide

theorem mixKey_run {s : State} {b c d : Reg} {i : Nat}
    (hb : b ≠ .x10) (hc : c ≠ .x10) (hd : d ≠ .x10) (hi : i < 32)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 (256+4*i)) 4) :
    ∃ t, runBlock isa (mixKey b c d i) s = some t ∧
      t.gpr .x10 = (((s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 (256+4*i)) 32 ^^^
        (s.gpr b).setWidth 32) ^^^ (s.gpr c).setWidth 32) ^^^ (s.gpr d).setWidth 32).setWidth 64 ∧
      (∀ r, r ≠ .x10 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v := by
  let k := s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 (256+4*i)) 32
  let a := s.write .w .x10 k
  let e := a.write .w .x10 (a.read .w .x10 ^^^ a.read .w b)
  let f := e.write .w .x10 (e.read .w .x10 ^^^ e.read .w c)
  let g := f.write .w .x10 (f.read .w .x10 ^^^ f.read .w d)
  refine ⟨g,?_,?_,?_,rfl,rfl,rfl,rfl,rfl⟩
  · rw [mixKey,runBlock_cons,exec_ldr_w ⟨by omega,by omega⟩ hr,runStep_some,
      runBlock_cons,exec_logic,runStep_some,runBlock_cons,exec_logic,runStep_some,
      runBlock_cons,exec_logic,runStep_some,runBlock_nil]
  · simp only [g,f,e,a,gpr_write_self,State.read,Size.bits,
      gpr_write_of_ne _ _ _ hb,gpr_write_of_ne _ _ _ hc,gpr_write_of_ne _ _ _ hd]
    simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),BitVec.setWidth_eq]
    rfl
  · intro r hr
    simp only [g,f,e,a,gpr_write_of_ne _ _ _ hr]

def words (s : State) (w : Nat) : BitVec 32 := (s.gpr (wordReg w)).setWidth 32

theorem wordReg_inj : ∀ a < 4, ∀ b < 4, wordReg a = wordReg b → a = b := by decide

theorem round_run {s : State} {i : Nat} (hi : i < 32) (hc : Constants s) (ht : Table s)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 (256+4*i)) 4) :
    ∃ t, runBlock isa (round i) s = some t ∧
      (∀ w < 4, words t w = VG.Proof.Sm4.sround .enc
        (s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 (256+4*i)) 32) (i%4) (words s) w) ∧
      Constants t ∧ Table t ∧
      (∀ r, r ≠ wordReg (i%4) → r ≠ .x10 → r ≠ .x11 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  let ra := wordReg (i%4)
  have ha10 : ra ≠ .x10 := (wordReg_ne _ (Nat.mod_lt _ (by decide))).1
  have ha11 : ra ≠ .x11 := (wordReg_ne _ (Nat.mod_lt _ (by decide))).2
  obtain ⟨a,ae,av,ag,am,ard,awr,asp,avec⟩ := mixKey_run (b := wordReg ((i+1)%4))
    (c := wordReg ((i+2)%4)) (d := wordReg ((i+3)%4))
    (wordReg_ne _ (Nat.mod_lt _ (by decide))).1
    (wordReg_ne _ (Nat.mod_lt _ (by decide))).1
    (wordReg_ne _ (Nat.mod_lt _ (by decide))).1 hi hr
  have ac : Constants a := by simpa only [Constants,avec] using hc
  have atab : Table a := by simpa only [Table,avec] using ht
  obtain ⟨b,be,bv,bg,bm,brd,bwr,bsp,bvec⟩ := substitute_run a ac atab
  obtain ⟨c,ce,cv,cg,cm,crd,cwr,csp,cvec⟩ := linear_run b
  let t := c.write .w ra (c.read .w ra ^^^ c.read .w .x11)
  have cra : c.read .w ra = (s.gpr ra).setWidth 32 := by
    simp only [State.read,Size.bits,cg _ ha11,bg _ ha10,ag _ ha10]
  have val : c.read .w .x11 = Spec.Sm4.t
      (words s ((i+1)%4) ^^^ words s ((i+2)%4) ^^^ words s ((i+3)%4) ^^^
        s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 (256+4*i)) 32) := by
    simp only [State.read,Size.bits,cv,bv,av,
      BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),BitVec.setWidth_eq]
    unfold Spec.Sm4.t words
    congr 2
    ac_rfl
  have other : ∀ r, r ≠ ra → r ≠ .x10 → r ≠ .x11 → t.gpr r = s.gpr r := by
    intro r hra h10 h11
    rw [gpr_write_of_ne _ _ _ hra,cg _ h11,bg _ h10,ag _ h10]
  have tv : ∀ v, v ∉ [.v0,.v1,.v2,.v3] → t.v v = s.v v := by
    intro v hv
    rw [show t.v v = c.v v from rfl,cvec,bvec _ hv,avec]
  refine ⟨t,?_,?_,hc.of_preserved tv,ht.of_preserved tv,other,?_,?_,?_,?_⟩
  · rw [round,VG.Interleave.runBlock_append,VG.Interleave.runBlock_append,
      VG.Interleave.runBlock_append,roundInput,ae,Option.bind_some,be,Option.bind_some,ce,Option.bind_some]
    simp only [roundOutput,runBlock_cons,exec_logic,runStep_some,runBlock_nil]
    rfl
  · intro w hw
    by_cases h : w = i%4
    · subst w
      change (t.gpr ra).setWidth 32 = _
      simp only [t,gpr_write_self,
        BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),BitVec.setWidth_eq]
      rw [cra,val]
      simp only [VG.Proof.Sm4.sround,ite_true,VG.Impl.Sm4.Lin.t_enc]
      rw [show (i%4+1)%4 = (i+1)%4 by omega,
        show (i%4+2)%4 = (i+2)%4 by omega,
        show (i%4+3)%4 = (i+3)%4 by omega]
      rfl
    · have hreg : wordReg w ≠ ra := fun e => h (wordReg_inj w hw _ (Nat.mod_lt _ (by decide)) e)
      rw [words,other _ hreg (wordReg_ne w hw).1 (wordReg_ne w hw).2]
      simp only [VG.Proof.Sm4.sround,h,ite_false,words]
  · exact cm.trans (bm.trans am)
  · exact crd.trans (brd.trans ard)
  · exact cwr.trans (bwr.trans awr)
  · exact csp.trans (bsp.trans asp)

end VG.Proof.Sm4.AArch64.Serial
