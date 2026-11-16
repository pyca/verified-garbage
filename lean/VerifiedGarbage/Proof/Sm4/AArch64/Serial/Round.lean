module

public import VerifiedGarbage.Proof.Sm4.AArch64.Serial.Lookup
public import VerifiedGarbage.Impl.Sm4.AArch64.Serial.Core
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Sm4.Rounds
import VerifiedGarbage.Proof.Framework.Interleave

/-! ### `Sm4.AArch64.Serial.Linear`, which only this module used -/

section

/-! # SM4's linear map with shifted-register XORs -/

@[expose] public section

namespace VG.Proof.Sm4.AArch64.Serial

open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Impl.Sm4.AArch64.Serial

theorem rotate_complement (x : BitVec 32) (r : Nat) (hr : 0 < r) (hr' : r < 32) :
    x.rotateRight (32-r) = x.rotateLeft r := by
  rw [BitVec.rotateRight_def,BitVec.rotateLeft_def,Nat.mod_eq_of_lt hr',
    Nat.mod_eq_of_lt (show 32-r < 32 by omega_using [hr]),Nat.sub_sub_self (by omega_using [hr'] : r ≤ 32)]
  exact BitVec.or_comm _ _

theorem linear_eq (x : BitVec 32) :
    x ^^^ x.rotateRight 30 ^^^ x.rotateRight 22 ^^^ x.rotateRight 14 ^^^ x.rotateRight 8 =
      Spec.Sm4.linear x := by
  rw [show 30 = 32-2 by rfl,rotate_complement x 2 (by decide) (by decide),
    show 22 = 32-10 by rfl,rotate_complement x 10 (by decide) (by decide),
    show 14 = 32-18 by rfl,rotate_complement x 18 (by decide) (by decide),
    show 8 = 32-24 by rfl,rotate_complement x 24 (by decide) (by decide)]
  rfl

theorem ror32_bit (x : BitVec 32) {r i : Nat} (hr : r < 32) (hi : i < 32) :
    (x.rotateRight r).getLsbD i = x.getLsbD ((i + r) % 32) := by
  rw [BitVec.getLsbD_rotateRight, Nat.mod_eq_of_lt hr]
  by_cases h : i < 32 - r
  · simp only [h, ↓reduceIte]; congr 1; omega_using [h, hr]
  · simp only [h, ↓reduceIte, hi, decide_true, Bool.true_and]; congr 1; omega_using [h, hr, hi]

/-- `linear`'s two halves are the chain of four XORs. -/
theorem linear_tree (x : BitVec 32) :
    (x ^^^ x.rotateRight 30) ^^^ (x.rotateRight 8 ^^^ (x ^^^ x.rotateRight 8).rotateRight 14) =
      x ^^^ x.rotateRight 30 ^^^ x.rotateRight 22 ^^^ x.rotateRight 14 ^^^ x.rotateRight 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h14 : (i + 14) % 32 < 32 := Nat.mod_lt _ (by decide)
  simp only [BitVec.getLsbD_xor, ror32_bit x (by decide : 30 < 32) hi, ror32_bit x (by decide : 22 < 32) hi,
    ror32_bit x (by decide : 14 < 32) hi, ror32_bit x (by decide : 8 < 32) hi,
    ror32_bit (x ^^^ x.rotateRight 8) (by decide : 14 < 32) hi, ror32_bit x (by decide : 8 < 32) h14,
    show ((i + 14) % 32 + 8) % 32 = (i + 22) % 32 by omega_using []]
  generalize x.getLsbD i = a
  generalize x.getLsbD ((i + 30) % 32) = b
  generalize x.getLsbD ((i + 22) % 32) = c
  generalize x.getLsbD ((i + 14) % 32) = d
  generalize x.getLsbD ((i + 8) % 32) = e
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> rfl

theorem linear_run (s : State) :
    ∃ t, runBlock isa linear s = some t ∧
      t.gpr .x11 = (Spec.Sm4.linear ((s.gpr .x10).setWidth 32)).setWidth 64 ∧
      (∀ r, r ∉ [.x11,.x12,.x13] → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v := by
  let x := (s.gpr .x10).setWidth 32
  let a := s.write .w .x11 (x ^^^ x.rotateRight 30)
  let b := a.write .w .x12 (x ^^^ x.rotateRight 8)
  let c := b.write .w .x13 (x.rotateRight 8)
  let d := c.write .w .x12 (c.read .w .x13 ^^^ (c.read .w .x12).rotateRight 14)
  let e := d.write .w .x11 (d.read .w .x11 ^^^ d.read .w .x12)
  refine ⟨e,?_,?_,?_,rfl,rfl,rfl,rfl,rfl⟩
  · rfl
  · simp only [e,d,c,b,a,gpr_write,State.read,Size.bits,↓reduceIte,reduceCtorEq]
    simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
    rw [linear_tree,linear_eq]
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [e,d,c,b,a,gpr_write_of_ne _ _ _ hr.1,gpr_write_of_ne _ _ _ hr.2.1,
      gpr_write_of_ne _ _ _ hr.2.2]

end VG.Proof.Sm4.AArch64.Serial

end

end


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
  · rw [mixKey,runBlock_cons,exec_ldr_w ⟨by omega_using [],by omega_using [hi]⟩ hr,runStep_some,
      runBlock_cons,exec_logic,runStep_some,runBlock_cons,exec_logic,runStep_some,
      runBlock_cons,exec_logic,runStep_some,runBlock_nil]
  · simp only [g,f,e,a,gpr_write_self,State.read,Size.bits,
      gpr_write_of_ne _ _ _ hb,gpr_write_of_ne _ _ _ hc,gpr_write_of_ne _ _ _ hd]
    simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),BitVec.setWidth_eq]
    rfl
  · intro r hr
    simp only [g,f,e,a,gpr_write_of_ne _ _ _ hr]

def words (s : State) (w : Nat) : BitVec 32 := (s.gpr (wordReg w)).setWidth 32

theorem wordReg_nl : ∀ j < 4, wordReg j ∉ [.x11,.x12,.x13] := by decide

theorem wordReg_inj : ∀ a < 4, ∀ b < 4, wordReg a = wordReg b → a = b := by decide

theorem rkIdx_lt (d : Spec.Sm4.Direction) {i : Nat} (hi : i < 32) : rkIdx d i < 32 := by
  cases d
  · exact hi
  · exact Nat.lt_of_le_of_lt (Nat.sub_le 31 i) (by decide)

theorem round_run (d : Spec.Sm4.Direction) {s : State} {i : Nat} (hc : Constants s) (ht : Table s)
    (hi : rkIdx d i < 32)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 (256+4*rkIdx d i)) 4) :
    ∃ t, runBlock isa (round d i) s = some t ∧
      (∀ w < 4, words t w = VG.Proof.Sm4.sround .enc
        (s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 (256+4*rkIdx d i)) 32) (i%4) (words s) w) ∧
      Constants t ∧ Table t ∧
      (∀ r, r ≠ wordReg (i%4) → r ≠ .x10 → r ∉ [.x11,.x12,.x13] → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  rw [round]
  generalize rkIdx d i = kk at hi hr ⊢
  let ra := wordReg (i%4)
  have ha10 : ra ≠ .x10 := (wordReg_ne _ (Nat.mod_lt _ (by decide))).1
  have ha11 : ra ∉ [.x11,.x12,.x13] := wordReg_nl _ (Nat.mod_lt _ (by decide))
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
        s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 (256+4*kk)) 32) := by
    simp only [State.read,Size.bits,cv,bv,av,
      BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),BitVec.setWidth_eq]
    unfold Spec.Sm4.t words
    congr 2
    ac_rfl
  have other : ∀ r, r ≠ ra → r ≠ .x10 → r ∉ [.x11,.x12,.x13] → t.gpr r = s.gpr r := by
    intro r hra h10 h11
    rw [gpr_write_of_ne _ _ _ hra,cg _ h11,bg _ h10,ag _ h10]
  have tv : ∀ v, v ∉ [.v0,.v1,.v2,.v3] → t.v v = s.v v := by
    intro v hv
    rw [show t.v v = c.v v from rfl,cvec,bvec _ hv,avec]
  refine ⟨t,?_,?_,hc.of_preserved tv,ht.of_preserved tv,other,?_,?_,?_,?_⟩
  · rw [VG.Interleave.runBlock_append,VG.Interleave.runBlock_append,
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
      rw [show (i%4+1)%4 = (i+1)%4 by omega_using [],
        show (i%4+2)%4 = (i+2)%4 by omega_using [],
        show (i%4+3)%4 = (i+3)%4 by omega_using []]
      rfl
    · have hreg : wordReg w ≠ ra := fun e => h (wordReg_inj w hw _ (Nat.mod_lt _ (by decide)) e)
      rw [words,other _ hreg (wordReg_ne w hw).1 (wordReg_nl w hw)]
      simp only [VG.Proof.Sm4.sround,h,ite_false,words]
  · exact cm.trans (bm.trans am)
  · exact crd.trans (brd.trans ard)
  · exact cwr.trans (bwr.trans awr)
  · exact csp.trans (bsp.trans asp)

end VG.Proof.Sm4.AArch64.Serial
