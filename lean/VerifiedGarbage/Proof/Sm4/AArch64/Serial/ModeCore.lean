module

public import VerifiedGarbage.Proof.Sm4.AArch64.Serial.Load
import VerifiedGarbage.Proof.Sm4.Layout
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.Framework.Interleave
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
public import VerifiedGarbage.Spec.Aes
import VerifiedGarbage.Proof.Sm4.CtrCipher
import VerifiedGarbage.Proof.Framework.CallLay
public import VerifiedGarbage.Proof.Sm4.AArch64.ModeCore
public import VerifiedGarbage.Spec.Sm4.Ctr
import VerifiedGarbage.Proof.Modes.AArch64.Fb
import VerifiedGarbage.Proof.Sm4.AArch64.Lit
public import VerifiedGarbage.Proof.Sm4.AArch64.PreparedVerified
import VerifiedGarbage.Proof.Sm4.AArch64.Ecb
public import VerifiedGarbage.Impl.Sm4.AArch64.Serial.Core
public import VerifiedGarbage.Proof.Framework.AArch64.Straight
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Sm4.SboxTable
public import VerifiedGarbage.Spec.Camellia
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Sm4.AArch64.Imm
import VerifiedGarbage.Proof.Sm4.AArch64.Prologue
public import VerifiedGarbage.Proof.Sm4.AArch64.Round
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Sm4.AArch64.Serial.Lookup
public import VerifiedGarbage.Proof.Sm4.Rounds
public import VerifiedGarbage.Proof.Modes.AArch64.Core
import VerifiedGarbage.Proof.Aes.Bitsliced
import VerifiedGarbage.Proof.Framework.GetElem

/-! ### `Sm4.AArch64.Serial.State`, which this module and modules that import it used -/

section

/-! # The memory prepared for the single-block SM4 core -/

@[expose] public section

namespace VG.Proof.Sm4.AArch64.Serial

open VG VG.AArch64 VG.Impl.Sm4.AArch64.Serial

/-- Prepared data remains entirely in the core's scratch region. -/
structure Ready (m : Mem) (B : Addr) (k : Spec.Sm4.Schedule) : Prop where
  sbox : ∀ j < 256, m (B + BitVec.ofNat 64 j) = Spec.Sm4.sbox.getD j 0
  keys : ∀ i < 32, m.readW (B + BitVec.ofNat 64 (256+4*i)) 32 = k.getD i 0

theorem schedule_readW (m : Mem) (p : Addr) (i : Nat) (hi : i < 32) :
    m.readW (p + BitVec.ofNat 64 (4*i)) 32 = (Spec.Sm4.scheduleAt m p).getD i 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [VG.Proof.Aes.getD_eq _ hi,getLsbD_readW32 m p i hj]
  have h := VG.Proof.Sm4.getLsbD_scheduleAt m p (i := i) (c := j/8) (j := j%8)
    hi (by omega_using [hj]) (by omega_using [])
  rw [show 8*(j/8)+j%8 = j by omega_using []] at h
  rw [h]
  rw [show (32*i+j)/8 = 4*i+j/8 by omega_using [],show (32*i+j)%8 = j%8 by omega_using []]

theorem copied_schedule {m m' : Mem} {p q : Addr}
    (h : ∀ j < 128, m' (q + BitVec.ofNat 64 j) = m (p + BitVec.ofNat 64 j)) :
    Spec.Sm4.scheduleAt m' q = Spec.Sm4.scheduleAt m p := by
  apply Vector.ext
  intro i hi
  simp only [Spec.Sm4.scheduleAt,Vector.getElem_ofFn,List.range,List.range.loop,List.foldl]
  rw [h (4*i+0) (by omega_using [hi]),h (4*i+1) (by omega_using [hi]),h (4*i+2) (by omega_using [hi]),h (4*i+3) (by omega_using [hi])]

theorem Ready.frame {s s' : State} {B : Addr} {k : Spec.Sm4.Schedule} {rs : List Region}
    (h : Ready s.mem B k) (hf : Frame rs s.mem s'.mem)
    (hd : ∀ r ∈ rs, Region.Disjoint (Modes.AArch64.coreRegion core B) r ∨
      Region.Sub r (Modes.AArch64.bufRegion core B)) : Ready s'.mem B k := by
  have tableDisjoint : ∀ r ∈ rs, Region.Disjoint ⟨B,256⟩ r := by
    intro r hr
    rcases hd r hr with h | h
    · exact h.sub_left (VG.Region.sub_prefix (by decide))
    · exact (VG.Offset.base_disjoint B (by decide : 256 ≤ 768)
        (by decide : 768+16 ≤ 2^64)).sub_right h
  have keysDisjoint : ∀ r ∈ rs, Region.Disjoint ⟨(B + BitVec.ofNat 64 256),128⟩ r := by
    intro r hr
    rcases hd r hr with h | h
    · exact h.sub_left (VG.Offset.sub_base B (by decide : 256+128 ≤ 3168))
    · exact (VG.Offset.disjoint B (Or.inl (by decide : 256+128 ≤ 768))
        (by decide : 256+128 ≤ 2^64) (by decide : 768+16 ≤ 2^64)).sub_right h
  refine ⟨fun j hj => ?_,fun i hi => ?_⟩
  · rw [hf.bytes tableDisjoint (by decide : 256 ≤ 2^64) hj]
    exact h.sbox j hj
  · rw [← VG.Offset.add_add B 256 (4*i)]
    rw [hf.readW (w := 32) (VG.Offset.contains_base ((B + BitVec.ofNat 64 256)) (d := 4*i) (n := 4) (k := 128)
      (by omega_using [hi]) (by omega_using [hi])) keysDisjoint (by decide)]
    rw [VG.Offset.add_add]
    exact h.keys i hi

end VG.Proof.Sm4.AArch64.Serial

end

end

/-! ### `Sm4.AArch64.Serial.Round`, which this module and modules that import it used -/

section

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

end

end

/-! ### `Sm4.AArch64.Serial.Prepared`, which only this module used -/

section

/-! ### `Sm4.AArch64.Serial.Prepare`, which only this module used -/

section

/-! # Preparing the constant S-box and raw SM4 schedule -/

@[expose] public section

namespace VG.Proof.Sm4.AArch64.Serial

open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Impl.Sm4.AArch64.Serial

theorem tableWord_byte : ∀ h < 32, ∀ j < 8,
    (tableWord h).extractLsb' (8*j) 8 = Spec.Sm4.sbox.getD (8*h+j) 0 := fun h _ j hj => by
  have r8 : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := rfl
  unfold tableWord
  rw [r8, List.foldl_cons, List.foldl_cons, List.foldl_cons, List.foldl_cons, List.foldl_cons, List.foldl_cons,
    List.foldl_cons, List.foldl_cons, List.foldl_nil]
  exact VG.Proof.Sm4.AArch64.pack8_byte (fun j => Spec.Sm4.sbox.getD (8 * h + j) 0) hj

theorem preparedTable_run {s : State} {B : Addr}
    (hb : s.gpr .x5 = B)
    (hw : (⟨B, 8*396⟩ : Region) ∈ s.wr) :
    ∃ t, runBlock isa preparedTable s = some t ∧
      (∀ j < 32, t.mem.readW (B + BitVec.ofNat 64 (8*j)) 64 = tableWord j) ∧
      (∀ r, r ≠ .x21 → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ Frame [⟨B,256⟩] s.mem t.mem := by
  have hrange : tableEntries.map (·.1) = List.range 32 := by
    simp [tableEntries,List.map_map,Function.comp_def]
  obtain ⟨t,he,hv,_,hg,hd,hw',hf⟩ := VG.Proof.Sm4.AArch64.setSlotsN_ok 32
    (by decide) tableEntries (s := s) hb hw
    (fun kv hk => by
      simp only [tableEntries,List.mem_map,List.mem_range] at hk
      obtain ⟨i,hi,rfl⟩ := hk
      exact hi)
    (by rw [hrange]; exact List.nodup_range)
  have hbt : t.gpr .x5 = B := (hg _ (by decide)).trans hb
  refine ⟨t,he,?_,hg,hd,hw',hf⟩
  intro j hj
  have hjmem : (j,tableWord j) ∈ tableEntries :=
    List.mem_map.mpr ⟨j,List.mem_range.mpr hj,rfl⟩
  have h := hv (j,tableWord j) hjmem
  simp only [VG.Proof.Sm4.AArch64.slotW,VG.AArch64.Straight.wordAddr,VG.Impl.Aes.AArch64.sb,hbt] at h
  exact h

theorem preparedTable_bytes {m : Mem} {B : Addr}
    (h : ∀ j < 32, m.readW (B + BitVec.ofNat 64 (8*j)) 64 = tableWord j) :
    ∀ j < 256, m (B + BitVec.ofNat 64 j) = Spec.Sm4.sbox.getD j 0 := by
  intro j hj
  have e := congrArg (fun v : BitVec 64 => v.extractLsb' (8*(j%8)) 8) (h (j/8) (by omega_using [hj]))
  change (m.read (B + BitVec.ofNat 64 (8*(j/8))) 8).extractLsb' (8*(j%8)) 8 = _ at e
  rw [Mem.extractLsb'_read _ _ (by omega_using []),tableWord_byte _ (by omega_using [hj]) _ (by omega_using []),
    VG.Offset.add_add,show 8*(j/8)+j%8 = j by omega_using []] at e
  exact e

/-- The same table setup under any permissions covering its scratch space. -/
theorem preparedTable_wp {s : State} {B : Addr}
    (hb : s.gpr .x5 = B) (hw : InRegions s.wr B (8*396)) :
    WP isa (.block preparedTable) s fun t =>
      (∀ j < 32, t.mem.readW (B + BitVec.ofNat 64 (8*j)) 64 = tableWord j) ∧
      (∀ r, r ≠ .x21 → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ Frame [⟨B,256⟩] s.mem t.mem := by
  let u := s.withRegions [] [⟨B,8*396⟩]
  obtain ⟨t,he,hv,hg,hd,hw',hf⟩ := preparedTable_run (s := u) hb List.mem_cons_self
  obtain ⟨tr,t',hex,heq⟩ := (WP.of_runBlock ⟨t,he,rfl⟩ :
    WP isa (.block preparedTable) u (fun t' => t' = t))
  subst t'
  have hcov : Covers u.wr s.wr := Covers.one hw
  have hread : Covers (u.rd ++ u.wr) (s.rd ++ s.wr) := Covers.right hcov
  have ew := VG.AArch64.Exec.widen (s := u) (s' := t) (rd := s.rd) (wr := s.wr) hex hread hcov
  refine ⟨tr,t.withRegions s.rd s.wr,?_,hv,hg,rfl,rfl,hf⟩
  simpa only [u,State.withRegions_withRegions,State.withRegions_self] using ew

end VG.Proof.Sm4.AArch64.Serial

end

end

/-! ### `Sm4.AArch64.Serial.Copy`, which only this module used -/

section

/-! # Copy the expanded schedule using the existing checked block copier -/

@[expose] public section

namespace VG.Proof.Sm4.AArch64.Serial

open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Impl.Sm4.AArch64.Serial
open VG.Proof.Sm4.AArch64 (CopyInv copyBlocks_wp)

theorem copySchedule_wp {s : State}
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x0) 128)
    (hw : InRegions s.wr (s.gpr .x5 + BitVec.ofNat 64 256) 128)
    (hsep : Region.Disjoint ⟨s.gpr .x0,128⟩ ⟨s.gpr .x5 + BitVec.ofNat 64 256,128⟩) :
    WP isa copySchedule s fun t =>
      (∀ j < 128, t.mem (s.gpr .x5 + BitVec.ofNat 64 256 + BitVec.ofNat 64 j) =
        s.mem (s.gpr .x0 + BitVec.ofNat 64 j)) ∧
      Frame [⟨s.gpr .x5 + BitVec.ofNat 64 256,128⟩] s.mem t.mem ∧
      (∀ r, r ≠ .x14 → r ≠ .x15 → r ≠ .x17 → r ≠ .x21 → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  let a := s.write .x .x14 (s.gpr .x0)
  let b := a.write .x .x15 (a.gpr .x5 + BitVec.ofNat 64 256)
  let c := b.write .x .x17 8
  have regs : ∀ r, r ≠ .x14 → r ≠ .x15 → r ≠ .x17 → c.gpr r = s.gpr r := by
    intro r h14 h15 h17
    simp only [c,b,a,gpr_write_of_ne _ _ _ h14,gpr_write_of_ne _ _ _ h15,gpr_write_of_ne _ _ _ h17]
  have c14 : c.gpr .x14 = s.gpr .x0 := by simp [c,b,a,State.write]
  have c15 : c.gpr .x15 = s.gpr .x5 + BitVec.ofNat 64 256 := by simp [c,b,a,State.write]
  have c17 : c.gpr .x17 = 8 := by simp [c,State.write]
  unfold copySchedule
  refine WP.seq (WP.of_runBlock ⟨c,?_,?_⟩)
  · have ea : exec (VG.Impl.Aes.AArch64.movR .x14 .x0) s = some a := by
      simp [VG.Impl.Aes.AArch64.movR,exec,State.read,a]
    have eb : exec (.addImm .x .x15 .x5 256) a = some b := by
      rw [exec_addImm_x (by decide)]
      simp [State.read,b]
    have ec : exec (.movz .x .x17 8 0) b = some c := rfl
    rw [runBlock_cons,ea,runStep_some,runBlock_cons,eb,runStep_some,
      runBlock_cons,ec,runStep_some,runBlock_nil]
  · have hA : ∀ j < 16, InRegions (c.rd ++ c.wr) (s.gpr .x0 + BitVec.ofNat 64 (8*j)) 8 := by
      intro j hj
      exact CallLay.inRegions_sub hr (by omega_using [hj]) (by decide)
    have hB : ∀ j < 16, InRegions c.wr (s.gpr .x5 + BitVec.ofNat 64 256 + BitVec.ofNat 64 (8*j)) 8 := by
      intro j hj
      exact CallLay.inRegions_sub hw (by omega_using [hj]) (by decide)
    have inv : CopyInv (s.gpr .x0) (s.gpr .x5+ BitVec.ofNat 64 256) 8 c 0 c := by
      refine ⟨?_,?_,?_,fun _ h => absurd h (by omega_using []),Frame.refl _ _,fun _ _ _ _ _ => rfl,rfl,rfl⟩
      · simpa using c14
      · simpa using c15
      · simpa using c17
    refine WP.mono (copyBlocks_wp (by decide) (by decide) hA hB hsep inv) fun t ht =>
      ⟨ht.copied,ht.frame,fun r h14 h15 h17 h21 =>
        (ht.regs r h14 h15 h17 h21).trans (regs r h14 h15 h17),ht.rd,ht.wr⟩

end VG.Proof.Sm4.AArch64.Serial

end

end


/-! # The serial SM4 core's prepared state -/

@[expose] public section

namespace VG.Proof.Sm4.AArch64.Serial

open VG VG.AArch64 VG.Impl.Sm4.AArch64.Serial
open VG.Proof.Modes.AArch64 (ScrIn coreRegion)
open VG.Proof.Sm4.AArch64 (KeyArgs)

theorem prepare_wp {s : State} {B : Addr} {rs : List Region} {k : Spec.Sm4.Schedule}
    (hB : s.gpr .x5 = B) (hs : ScrIn s B core.total)
    (hR : (⟨B,8*core.total⟩ : Region) ∈ rs) (hk : KeyArgs s rs k) :
    WP isa core.prepare s fun t => Ready t.mem B k ∧ t.gpr .x5 = B ∧
      t.gpr .x23 = s.gpr .x23 ∧ t.gpr .x24 = s.gpr .x24 ∧
      Frame [coreRegion core B] s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain ⟨p,hp,rfl,hin,hfit,hdis⟩ := hk
  have hw : InRegions s.wr B (8*396) := ⟨_,hs.wr,by change (⟨B,3264⟩ : Region).Contains B 3168; simp [Region.Contains]⟩
  have hkey : Region.Disjoint ⟨p,128⟩ ⟨B,8*core.total⟩ := hdis _ hR
  change WP isa (.seq (.block preparedTable) copySchedule) s _
  refine WP.seq (WP.mono (preparedTable_wp hB hw) fun a ⟨aw,ag,ard,awr,af⟩ => ?_)
  have ab : a.gpr .x5 = B := (ag _ (by decide)).trans hB
  have ap : a.gpr .x0 = p := (ag _ (by decide)).trans hp
  have preserved : ∀ j < 128, a.mem (p+BitVec.ofNat 64 j) = s.mem (p+BitVec.ofNat 64 j) := by
    intro j hj
    exact af.bytes (R := ⟨p,128⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst r
      exact hkey.sub_right (Region.sub_prefix (by decide))) (by show 128 ≤ 2^64; decide) hj
  have readKey : InRegions (a.rd ++ a.wr) (a.gpr .x0) 128 := by
    rw [ard,awr,ap]
    exact ⟨_,List.mem_append_left _ hin,Region.contains_self _ _⟩
  have writeKey : InRegions a.wr (a.gpr .x5 + BitVec.ofNat 64 256) 128 := by
    rw [awr,ab]
    exact ⟨_,hs.wr,VG.Offset.contains_base B (by decide : 256+128 ≤ 3264) (by decide)⟩
  have sepKey : Region.Disjoint ⟨a.gpr .x0,128⟩ ⟨a.gpr .x5+BitVec.ofNat 64 256,128⟩ := by
    rw [ap,ab]
    exact hkey.sub_right (VG.Offset.sub_base B (by decide : 256+128 ≤ 3264))
  refine WP.mono (copySchedule_wp readKey writeKey sepKey) fun t ⟨tc,tf,tg,trd,twr⟩ => ?_
  have table : ∀ j < 256, t.mem (B+BitVec.ofNat 64 j) = Spec.Sm4.sbox.getD j 0 := by
    intro j hj
    have tf' : Frame [⟨B+BitVec.ofNat 64 256,128⟩] a.mem t.mem := by simpa only [ab] using tf
    rw [tf'.bytes (R := ⟨B,256⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst r
      exact VG.Offset.base_disjoint B (by decide : 256 ≤ 256) (by decide : 256+128 ≤ 2^64)) (by show 256 ≤ 2^64; decide) hj]
    exact preparedTable_bytes aw j hj
  have copied : Spec.Sm4.scheduleAt t.mem (B+BitVec.ofNat 64 256) = Spec.Sm4.scheduleAt s.mem p := by
    apply copied_schedule
    intro j hj
    have e := tc j hj
    rw [ab,ap,preserved j hj] at e
    exact e
  have keyWords : ∀ i < 32, t.mem.readW (B+BitVec.ofNat 64 (256+4*i)) 32 =
      (Spec.Sm4.scheduleAt s.mem p).getD i 0 := by
    intro i hi
    rw [← VG.Offset.add_add B 256 (4*i),schedule_readW _ _ i hi,copied]
  refine ⟨⟨table,?_⟩,?_,?_,?_,?_,trd.trans ard,twr.trans awr⟩
  · simpa only [hp] using keyWords
  · exact (tg _ (by decide) (by decide) (by decide) (by decide)).trans ab
  · exact (tg _ (by decide) (by decide) (by decide) (by decide)).trans (ag _ (by decide))
  · exact (tg _ (by decide) (by decide) (by decide) (by decide)).trans (ag _ (by decide))
  · refine (af.sub (fun r hr => ?_)).trans (tf.sub (fun r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst r
      exact ⟨_,List.mem_cons_self,Region.sub_prefix (by decide : 256 ≤ 3168)⟩
    · simp only [List.mem_singleton] at hr; subst r
      exact ⟨_,List.mem_cons_self,by rw [ab]; exact VG.Offset.sub_base B (by decide : 256+128 ≤ 3168)⟩

end VG.Proof.Sm4.AArch64.Serial

end

end

/-! ### `Sm4.AArch64.Serial.Crypt`, which only this module used -/

section

/-! ### `Sm4.AArch64.Serial.Block`, which only this module used -/

section

/-! # Load and store a single SM4 block in big-endian word order -/

@[expose] public section

namespace VG.Proof.Sm4.AArch64.Serial

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Sm4.AArch64.Serial

theorem wordReg_ne_base : ∀ j < 4, wordReg j ≠ .x5 := by decide

theorem readBE_word (m : Mem) (p : Addr) (i : Nat) (hi : i < 4) :
    rev32 (m.readW (p + BitVec.ofNat 64 (4*i)) 32) =
      Spec.Sm4.wordAt (Spec.Sm4.blockAt m p) (4*i) := by
  rw [rev32_readW,Spec.Sm4.wordAt]
  rw [VG.Proof.Sm4.blockAt_getD _ _ (by omega_using [hi]),VG.Proof.Sm4.blockAt_getD _ _ (by omega_using [hi]),
    VG.Proof.Sm4.blockAt_getD _ _ (by omega_using [hi]),VG.Proof.Sm4.blockAt_getD _ _ (by omega_using [hi])]
  have add1 (j : Nat) : p + BitVec.ofNat 64 (j+1) = p + BitVec.ofNat 64 j + 1 := by
    rw [BitVec.ofNat_add,BitVec.add_assoc]; rfl
  simp only [show 4*i+2 = (4*i+1)+1 by omega_using [],
    show 4*i+3 = ((4*i+1)+1)+1 by omega_using [],add1]

theorem loadWord_run {s : State} {r : Reg} {i : Nat} (hi : i < 4)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 (768+4*i)) 4) :
    ∃ t, runBlock isa [.ldr .w r .x5 (768+4*i),.rev32 r r] s = some t ∧
      (t.gpr r).setWidth 32 = rev32 (s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 (768+4*i)) 32) ∧
      (∀ q, q ≠ r → t.gpr q = s.gpr q) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v := by
  let a := s.write .w r (s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 (768+4*i)) 32)
  let b := a.write .w r (rev32 (a.read .w r))
  refine ⟨b,?_,?_,?_,rfl,rfl,rfl,rfl,rfl⟩
  · rw [runBlock_cons,exec_ldr_w ⟨by omega_using [],by omega_using [hi]⟩ hread,runStep_some,
      runBlock_cons,exec_rev32,runStep_some,runBlock_nil]
  · simp only [b,a,gpr_write_self,State.read,Size.bits,
      BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),BitVec.setWidth_eq]
  · intro q hq
    simp only [b,a,gpr_write_of_ne _ _ _ hq]

theorem loads_run (s : State) (n : Nat) (hn : n ≤ 4)
    (hread : ∀ i < 4, InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 (768+4*i)) 4) :
    ∃ t, runBlock isa ((List.range n).flatMap fun i =>
        [.ldr .w (wordReg i) .x5 (768+4*i),.rev32 (wordReg i) (wordReg i)]) s = some t ∧
      (∀ j < n, words t j = rev32 (s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 (768+4*j)) 32)) ∧
      (∀ r, (∀ j < n, r ≠ wordReg j) → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v := by
  induction n with
  | zero => exact ⟨s,rfl,fun _ h => absurd h (by omega_using []),fun _ _ => rfl,rfl,rfl,rfl,rfl,rfl⟩
  | succ n ih =>
    obtain ⟨a,ae,aw,ag,am,ard,awr,asp,avec⟩ := ih (by omega_using [hn])
    have ab : a.gpr .x5 = s.gpr .x5 := ag _ (fun j hj => (wordReg_ne_base j (by omega_using [hn, hj])).symm)
    have ar : InRegions (a.rd ++ a.wr) (a.gpr .x5 + BitVec.ofNat 64 (768+4*n)) 4 := by
      rw [ard,awr,ab]
      exact hread n (by omega_using [hn])
    obtain ⟨b,be,bv,bg,bm,brd,bwr,bsp,bvec⟩ := loadWord_run (r := wordReg n) (by omega_using [hn]) ar
    refine ⟨b,?_,?_,?_,bm.trans am,brd.trans ard,bwr.trans awr,bsp.trans asp,bvec.trans avec⟩
    · rw [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
        VG.Interleave.runBlock_append,ae,Option.bind_some,be]
    · intro j hj
      by_cases h : j = n
      · subst j
        simpa only [words,am,ab] using bv
      · rw [words,bg _ (fun e => h (wordReg_inj _ (by omega_using [hn, hj]) _ (by omega_using [hn]) e))]
        exact aw j (by omega_using [hj, h])
    · intro r hr
      exact (bg r (hr n (by omega_using []))).trans (ag r (fun j hj => hr j (by omega_using [hj])))

theorem storeWord_run {s : State} {r : Reg} {i : Nat} (hr : r ≠ .x5) (hi : i < 4)
    (hwrite : InRegions s.wr (s.gpr .x5 + BitVec.ofNat 64 (768+4*i)) 4) :
    ∃ t, runBlock isa [.rev32 r r,.str .w r .x5 (768+4*i)] s = some t ∧
      t.mem = s.mem.writeW (s.gpr .x5 + BitVec.ofNat 64 (768+4*i)) (rev32 ((s.gpr r).setWidth 32)) ∧
      (∀ q, q ≠ r → t.gpr q = s.gpr q) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v := by
  let a := s.write .w r (rev32 ((s.gpr r).setWidth 32))
  let t := { a with mem := a.mem.writeW (a.gpr .x5 + BitVec.ofNat 64 (768+4*i)) ((a.gpr r).setWidth 32) }
  have base : a.gpr .x5 = s.gpr .x5 := gpr_write_of_ne _ _ _ hr.symm
  refine ⟨t,?_,?_,?_,rfl,rfl,rfl,rfl⟩
  · rw [runBlock_cons,exec_rev32,runStep_some,runBlock_cons]
    rw [exec_str_w ⟨by omega_using [],by omega_using [hi]⟩ (by
      change InRegions a.wr (a.gpr .x5 + BitVec.ofNat 64 (768+4*i)) 4
      rw [base]; exact hwrite),runStep_some,runBlock_nil]
    rfl
  · simp only [t,a,base,gpr_write_self,mem_write,
      BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),BitVec.setWidth_eq]
  · intro q hq
    exact gpr_write_of_ne _ _ _ hq

theorem frame_write_word (m : Mem) (p : Addr) (v : BitVec 32) :
    Frame [⟨p,4⟩] m (m.writeW p v) := by
  intro x hx
  simp only [Mem.writeW,Mem.write]
  exact ite_eq_right (fun h => hx _ List.mem_cons_self h)

theorem stores_run (s : State) (n : Nat) (hn : n ≤ 4)
    (hwrite : ∀ i < 4, InRegions s.wr (s.gpr .x5 + BitVec.ofNat 64 (768+4*i)) 4) :
    ∃ t, runBlock isa ((List.range n).flatMap fun i =>
        [.rev32 (wordReg (3-i)) (wordReg (3-i)),.str .w (wordReg (3-i)) .x5 (768+4*i)]) s = some t ∧
      (∀ j < n, t.mem.readW (s.gpr .x5 + BitVec.ofNat 64 (768+4*j)) 32 = rev32 (words s (3-j))) ∧
      (∀ r, (∀ j < n, r ≠ wordReg (3-j)) → t.gpr r = s.gpr r) ∧
      Frame [⟨s.gpr .x5+BitVec.ofNat 64 768,16⟩] s.mem t.mem ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v := by
  induction n with
  | zero => exact ⟨s,rfl,fun _ h => absurd h (by omega_using []),fun _ _ => rfl,Frame.refl _ _,rfl,rfl,rfl,rfl⟩
  | succ n ih =>
    obtain ⟨a,ae,aw,ag,af,ard,awr,asp,avec⟩ := ih (by omega_using [hn])
    have ab : a.gpr .x5 = s.gpr .x5 := ag _ (fun j hj => (wordReg_ne_base (3-j) (by omega_using [])).symm)
    have av : a.gpr (wordReg (3-n)) = s.gpr (wordReg (3-n)) := ag _ (fun j hj he => by
      have := wordReg_inj (3-n) (by omega_using []) (3-j) (by omega_using []) he
      omega_using [hn, hj, this])
    have ar : InRegions a.wr (a.gpr .x5 + BitVec.ofNat 64 (768+4*n)) 4 := by
      rw [awr,ab]
      exact hwrite n (by omega_using [hn])
    obtain ⟨b,be,bm,bg,brd,bwr,bsp,bvec⟩ := storeWord_run (wordReg_ne_base (3-n) (by omega_using [])) (by omega_using [hn]) ar
    have bmem : b.mem = a.mem.writeW (s.gpr .x5 + BitVec.ofNat 64 (768+4*n)) (rev32 (words s (3-n))) := by
      simpa only [ab,av,words] using bm
    have bf : Frame [⟨s.gpr .x5 + BitVec.ofNat 64 (768+4*n),4⟩] a.mem b.mem := by
      rw [bmem]
      exact frame_write_word _ _ _
    refine ⟨b,?_,?_,?_,?_,brd.trans ard,bwr.trans awr,bsp.trans asp,bvec.trans avec⟩
    · rw [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
        VG.Interleave.runBlock_append,ae,Option.bind_some,be]
    · intro j hj
      by_cases h : j = n
      · subst j
        rw [bmem,Mem.readW_writeW_self32]
      · rw [bf.readW (w := 32) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst r
          exact VG.Offset.disjoint (s.gpr .x5) (by omega_using [h]) (by omega_using [hn, hj]) (by omega_using [hn])) (by decide)]
        exact aw j (by omega_using [hj, h])
    · intro r hr
      exact (bg r (hr n (by omega_using []))).trans (ag r (fun j hj => hr j (by omega_using [hj])))
    · refine af.trans (bf.sub (fun r hr => ?_))
      simp only [List.mem_singleton] at hr; subst r
      refine ⟨_,List.mem_cons_self,?_⟩
      rw [← VG.Offset.add_add (s.gpr .x5) 768 (4*n)]
      exact VG.Offset.sub_base _ (by omega_using [hn] : 4*n+4 ≤ 16)

theorem stored_bytes {m : Mem} {p : Addr} {z : Nat → BitVec 32}
    (h : ∀ i < 4, m.readW (p + BitVec.ofNat 64 (4*i)) 32 = rev32 (z (3-i))) :
    Spec.Aes.bytesAt m p 16 = (VG.Proof.Sm4.outBlock z).toList := by
  apply List.ext_getElem (by simp [Spec.Aes.bytesAt])
  intro i hi hi'
  have hi16 : i < 16 := by simpa [Spec.Aes.bytesAt] using hi
  simp only [Spec.Aes.bytesAt,List.getElem_map,List.getElem_range,Vector.getElem_toList]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have b := Mem.readW_byte m (p+BitVec.ofNat 64 (4*(i/4))) (i := i%4) (by omega_using [])
  rw [VG.Offset.add_add,show 4*(i/4)+i%4 = i by omega_using [],h (i/4) (by omega_using [hi16])] at b
  rw [b,BitVec.getLsbD_extractLsb',VG.Proof.Sm4.getLsbD_outBlock' z hi16 hj]
  simp only [hj,decide_true,Bool.true_and]
  change (byteRev32 (z (3-i/4))).getLsbD (8*(i%4)+j) = _
  rw [byteRev32_getLsbD _ (by omega_using [hj])]
  congr 1 <;> omega_using [hj]

end VG.Proof.Sm4.AArch64.Serial

end

end

/-! ### `Sm4.AArch64.Serial.Rounds`, which only this module used -/

section

/-! # The 32 serial SM4 rounds -/

@[expose] public section

namespace VG.Proof.Sm4.AArch64.Serial

open VG VG.AArch64 VG.Impl.Sm4.AArch64.Serial
open VG.Proof.Sm4 (sround quad quads)

def written : List Reg := [.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13]

def steps (K : Nat → BitVec 32) (n : Nat) (x : Nat → BitVec 32) : Nat → BitVec 32 :=
  (List.range n).foldl (fun z i => sround .enc (K i) (i%4) z) x

theorem steps_succ (K : Nat → BitVec 32) (n : Nat) (x : Nat → BitVec 32) :
    steps K (n+1) x = sround .enc (K n) (n%4) (steps K n x) := by
  simp only [steps,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]

theorem sround_congr (k : BitVec 32) {a w : Nat} {x y : Nat → BitVec 32}
    (ha : a < 4) (h : ∀ j < 4, x j = y j) (hw : w < 4) :
    sround .enc k a x w = sround .enc k a y w := by
  unfold sround
  split
  · rw [h a ha,h _ (Nat.mod_lt _ (by decide)),h _ (Nat.mod_lt _ (by decide)),
      h _ (Nat.mod_lt _ (by decide))]
  · exact h w hw

theorem steps_congr (K L : Nat → BitVec 32) (n : Nat) (x y : Nat → BitVec 32)
    (hk : ∀ i < n, K i = L i) (hx : ∀ j < 4, x j = y j) :
    ∀ w < 4, steps K n x w = steps L n y w := by
  induction n with
  | zero => exact hx
  | succ n ih =>
    intro w hw
    rw [steps_succ,steps_succ,hk n (by omega_using [])]
    exact sround_congr _ (Nat.mod_lt _ (by decide)) (ih (fun i hi => hk i (by omega_using [hi]))) hw

theorem wordReg_mem : ∀ j < 4, wordReg j ∈ written := by decide

theorem rounds_run (d : Spec.Sm4.Direction) (s : State) (n : Nat) (hn : n ≤ 32)
    (hc : Constants s) (ht : Table s)
    (hr : ∀ i < 32, InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 (256+4*i)) 4) :
    ∃ t, runBlock isa ((List.range n).flatMap (round d)) s = some t ∧
      (∀ w < 4, words t w = steps
        (fun i => s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 (256+4*rkIdx d i)) 32) n (words s) w) ∧
      Constants t ∧ Table t ∧
      (∀ r, r ∉ written → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  induction n with
  | zero => exact ⟨s,rfl,fun _ _ => rfl,hc,ht,fun _ _ => rfl,rfl,rfl,rfl,rfl⟩
  | succ n ih =>
    obtain ⟨a,ae,aw,ac,atab,ag,am,ard,awr,asp⟩ := ih (by omega_using [hn])
    have ab : a.gpr .x5 = s.gpr .x5 := ag _ (by decide)
    have hk : rkIdx d n < 32 := rkIdx_lt d (by omega_using [hn])
    have ar : InRegions (a.rd ++ a.wr) (a.gpr .x5 + BitVec.ofNat 64 (256+4*rkIdx d n)) 4 := by
      rw [ard,awr,ab]
      exact hr _ hk
    obtain ⟨b,be,bw,bc,bt,bg,bm,brd,bwr,bsp⟩ := round_run d ac atab hk ar
    refine ⟨b,?_,?_,bc,bt,?_,bm.trans am,brd.trans ard,bwr.trans awr,bsp.trans asp⟩
    · rw [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
        VG.Interleave.runBlock_append,ae,Option.bind_some,be]
    · intro w hw
      rw [bw w hw,am,ab,steps_succ]
      exact sround_congr _ (Nat.mod_lt _ (by decide)) aw hw
    · intro r hr
      have hreg : r ≠ wordReg (n%4) := fun he => hr (he ▸ wordReg_mem _ (Nat.mod_lt _ (by decide)))
      have h10 : r ≠ .x10 := fun he => hr (by simp [written,he])
      have h11 : r ∉ [.x11,.x12,.x13] := fun he => hr (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at he
        rcases he with he | he | he <;> simp [written,he])
      exact (bg r hreg h10 h11).trans (ag r hr)

theorem steps_quads (K : Nat → BitVec 32) (x : Nat → BitVec 32) (n : Nat) :
    steps K (4*n) x = quads .enc K n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [steps,VG.Proof.Sm4.range_four,List.foldl_append,List.foldl_cons,List.foldl_nil]
    change sround .enc (K (4*n+3)) ((4*n+3)%4)
      (sround .enc (K (4*n+2)) ((4*n+2)%4)
        (sround .enc (K (4*n+1)) ((4*n+1)%4)
          (sround .enc (K (4*n)) ((4*n)%4) (steps K (4*n) x)))) = _
    rw [ih,show (4*n)%4 = 0 by omega_using [],show (4*n+1)%4 = 1 by omega_using [],
      show (4*n+2)%4 = 2 by omega_using [],show (4*n+3)%4 = 3 by omega_using []]
    rfl

end VG.Proof.Sm4.AArch64.Serial

end

end


/-! # Correctness of the single-block SM4 core -/

@[expose] public section

namespace VG.Proof.Sm4.AArch64.Serial

open VG VG.AArch64 VG.Impl.Sm4.AArch64.Serial
open VG.Proof.Modes.AArch64 (ScrIn coreRegion bufRegion)

/-- The direction's cipher on a block's bytes. -/
def dirCipher : Spec.Sm4.Direction → Spec.Sm4.Schedule → Spec.Cbc.Cipher
  | .encrypt => Spec.Sm4.cipher
  | .decrypt => Spec.Sm4.invCipher

theorem dirCipher_bytes (d : Spec.Sm4.Direction) (k : Spec.Sm4.Schedule) (m : Mem) (p : Addr) :
    dirCipher d k (Spec.Aes.bytesAt m p 16) =
      (VG.Proof.Sm4.outBlock (VG.Proof.Sm4.quads .enc (fun i => k.getD (rkIdx d i) 0) 8
        (VG.Proof.Sm4.ofBlock (Spec.Sm4.blockAt m p)))).toList := by
  cases d
  · exact VG.Proof.Sm4.cipher_bytes k m p
  · rw [dirCipher, Spec.Sm4.invCipher, VG.Proof.Sm4.bytesAt_eq_blockAt, VG.Proof.Sm4.ofFn_toList,
      Spec.Sm4.decryptBlock, VG.Proof.Sm4.crypt_eq]
    rfl

theorem crypt_wp (dir : Spec.Sm4.Direction) {s : State} {B : Addr} {k : Spec.Sm4.Schedule}
    (hB : s.gpr .x5 = B) (hs : ScrIn s B core.total) (ready : Ready s.mem B k) :
    WP isa (.block (crypt dir)) s fun t => t.gpr .x5 = B ∧
      t.gpr .x23 = s.gpr .x23 ∧ t.gpr .x24 = s.gpr .x24 ∧ Ready t.mem B k ∧
      Frame [coreRegion core B] s.mem t.mem ∧
      Spec.Aes.bytesAt t.mem (B+BitVec.ofNat 64 768) 16 =
        dirCipher dir k (Spec.Aes.bytesAt s.mem (B+BitVec.ofNat 64 768) 16) ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  have readable : InRegions (s.rd ++ s.wr) (s.gpr .x5) 256 := by
    rw [hB]
    exact ⟨_,List.mem_append_right _ hs.wr,by
      change (⟨B,3264⟩ : Region).Contains B 256
      simp [Region.Contains]⟩
  have bytes : ∀ j < 256, s.mem (s.gpr .x5+BitVec.ofNat 64 j) = Spec.Sm4.sbox.getD j 0 := by
    rw [hB]; exact ready.sbox
  change WP isa (.block (loadSbox ++ quarterConstants ++ loadBlock ++ (List.range 32).flatMap (round dir) ++ storeBlock)) s _
  rw [WP.block_append_iff,WP.block_append_iff,WP.block_append_iff,WP.block_append_iff]
  refine WP.mono (loadSbox_ok s readable bytes) fun a ⟨atab,ae⟩ => ?_
  obtain ⟨b,be,bc,bg,bm,brd,bwr,_,bvec⟩ := quarterConstants_run a
  refine WP.of_runBlock ⟨b,be,?_⟩
  have ab : a.gpr = s.gpr := by rw [ae]
  have am : a.mem = s.mem := by rw [ae]
  have ard : a.rd = s.rd := by rw [ae]
  have awr : a.wr = s.wr := by rw [ae]
  have bbase : b.gpr .x5 = B := (bg _ (by decide)).trans (by rw [ab]; exact hB)
  have bmem : b.mem = s.mem := bm.trans am
  have btab : Table b := atab.of_rows (fun j hj => by
    have hn := VG.AArch64.Tbl.treg_ne8 j hj
    exact bvec _ hn.2.2.2.2.1 hn.2.2.2.2.2.1 hn.2.2.2.2.2.2.1)
  have br : ∀ i < 4, InRegions (b.rd ++ b.wr) (b.gpr .x5+BitVec.ofNat 64 (768+4*i)) 4 := by
    intro i hi
    rw [brd,bwr,ard,awr,bbase]
    exact ⟨_,List.mem_append_right _ hs.wr,VG.Offset.contains_base B
      (by omega_using [hi] : 768+4*i+4 ≤ 3264) (by omega_using [hi])⟩
  obtain ⟨c,ce,cw,cg,cm,crd,cwr,_,cvec⟩ := loads_run b 4 (by decide) br
  refine WP.of_runBlock ⟨c,ce,?_⟩
  have ck : ∀ r, r ∉ written → c.gpr r = b.gpr r := by
    intro r hr
    exact cg r (fun j hj he => hr (he ▸ wordReg_mem j hj))
  have cbase : c.gpr .x5 = B := (ck _ (by decide)).trans bbase
  have cmem : c.mem = s.mem := cm.trans bmem
  have cc : Constants c := by simpa only [Constants,cvec] using bc
  have ct : Table c := by simpa only [Table,cvec] using btab
  have cr : ∀ i < 32, InRegions (c.rd ++ c.wr) (c.gpr .x5+BitVec.ofNat 64 (256+4*i)) 4 := by
    intro i hi
    rw [crd,cwr,brd,bwr,ard,awr,cbase]
    exact ⟨_,List.mem_append_right _ hs.wr,VG.Offset.contains_base B
      (by omega_using [hi] : 256+4*i+4 ≤ 3264) (by omega_using [hi])⟩
  obtain ⟨d,de,dw,dc,dt,dg,dm,drd,dwr,_⟩ :=
    rounds_run dir c 32 (by decide) cc ct cr
  refine WP.of_runBlock ⟨d,de,?_⟩
  have dbase : d.gpr .x5 = B := (dg _ (by decide)).trans cbase
  have dmem : d.mem = s.mem := dm.trans cmem
  let init := VG.Proof.Sm4.ofBlock (Spec.Sm4.blockAt s.mem (B+BitVec.ofNat 64 768))
  let z := VG.Proof.Sm4.quads .enc (fun i => k.getD (rkIdx dir i) 0) 8 init
  have initial : ∀ w < 4, words c w = init w := by
    intro w hw
    rw [cw w hw,bmem,bbase,← VG.Offset.add_add B 768 (4*w),readBE_word _ _ w hw]
    rfl
  have dwords : ∀ w < 4, words d w = z w := by
    intro w hw
    rw [dw w hw]
    have h := steps_congr
      (fun i => c.mem.readW (c.gpr .x5+BitVec.ofNat 64 (256+4*rkIdx dir i)) 32)
      (fun i => k.getD (rkIdx dir i) 0) 32 (words c) init
      (fun i hi => by rw [cmem,cbase]; exact ready.keys _ (rkIdx_lt dir hi)) initial w hw
    rw [h]
    change steps (fun i => k.getD (rkIdx dir i) 0) (4*8) init w = z w
    rw [steps_quads]
  have dr : ∀ i < 4, InRegions d.wr (d.gpr .x5+BitVec.ofNat 64 (768+4*i)) 4 := by
    intro i hi
    rw [dwr,cwr,bwr,awr,dbase]
    exact ⟨_,hs.wr,VG.Offset.contains_base B (by omega_using [hi] : 768+4*i+4 ≤ 3264) (by omega_using [hi])⟩
  obtain ⟨e,ee,ew,eg,ef,erd,ewr,_,_⟩ := stores_run d 4 (by decide) dr
  refine WP.of_runBlock ⟨e,ee,?_⟩
  have ek : ∀ r, r ∉ written → e.gpr r = d.gpr r := by
    intro r hr
    exact eg r (fun j hj he => hr (he ▸ wordReg_mem (3-j) (by omega_using [])))
  have output : Spec.Aes.bytesAt e.mem (B+BitVec.ofNat 64 768) 16 = (VG.Proof.Sm4.outBlock z).toList := by
    apply stored_bytes
    intro i hi
    rw [VG.Offset.add_add]
    rw [← dbase,ew i hi,dwords (3-i) (by omega_using [])]
  have frame : Frame [bufRegion core B] s.mem e.mem := by
    change Frame [⟨B+BitVec.ofNat 64 768,16⟩] s.mem e.mem
    simpa only [dbase,dmem] using ef
  have finalReady : Ready e.mem B k := ready.frame frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst r
    exact Or.inr (fun _ h => h))
  refine ⟨(ek _ (by decide)).trans dbase,?_,?_,finalReady,?_,?_,?_,?_⟩
  · rw [ek _ (by decide),dg _ (by decide),ck _ (by decide),bg _ (by decide),ab]
  · rw [ek _ (by decide),dg _ (by decide),ck _ (by decide),bg _ (by decide),ab]
  · exact frame.sub (fun r hr => by
      simp only [List.mem_singleton] at hr; subst r
      exact ⟨_,List.mem_cons_self,VG.Offset.sub_base B (by decide : 768+16 ≤ 3168)⟩)
  · rw [output,dirCipher_bytes]
  · exact erd.trans (drd.trans (crd.trans (brd.trans ard)))
  · exact ewr.trans (dwr.trans (cwr.trans (bwr.trans awr)))

end VG.Proof.Sm4.AArch64.Serial

end

end


/-! # The single-block SM4 core meets the existing mode interface -/

@[expose] public section

namespace VG.Proof.Sm4.AArch64.Serial

open VG VG.AArch64 VG.Impl.Sm4.AArch64.Serial
open VG.Proof.Modes.AArch64 (CoreSpec BlockSpec KeepsReg bufAddr)

@[simp] theorem core_bw : core.bw = 2 := rfl

def coreSpec : CoreSpec core where
  Key := Spec.Sm4.Schedule
  cipher := Spec.Sm4.cipher
  KeyArgs := VG.Proof.Sm4.AArch64.KeyArgs
  Ready s B k := Ready s.mem B k
  cipher_len _ _ := by simp [Spec.Sm4.cipher]
  layout := ⟨by decide,by decide,by decide,by decide,by decide⟩
  keyRegs_ok := by decide
  regs_ok := by decide
  keyArgs_congr h hr hrd hwr _ hf := VG.Proof.Sm4.AArch64.keyArgs_congr h hr hrd hwr hf
  ready_frame h hf hd _ _ := h.frame hf hd
  prepare_wp := prepare_wp
  crypt_wp := by
    intro s B k hb hs hr
    refine WP.mono (crypt_wp .encrypt hb hs hr) fun t ⟨tb,td,tl,tr,tf,to,rd,wr⟩ =>
      ⟨tb,td,tl,tr,tf,?_,rd,wr⟩
    intro j hj
    have hj' : j < 1 := hj
    have hj0 : j = 0 := by omega_using [hj']
    subst j
    change Spec.Aes.bytesAt t.mem (B+BitVec.ofNat 64 (768+16*0)) 16 =
      Spec.Sm4.cipher k (Spec.Aes.bytesAt s.mem (B+BitVec.ofNat 64 (768+16*0)) 16)
    exact to

abbrev blockSpec : BlockSpec core := coreSpec.toBlock rfl

@[simp] theorem decCore_bw : decCore.bw = 2 := rfl

/-- The decrypting core meets the mode interface. -/
def decCoreSpec : CoreSpec decCore where
  Key := Spec.Sm4.Schedule
  cipher := Spec.Sm4.invCipher
  KeyArgs := VG.Proof.Sm4.AArch64.KeyArgs
  Ready s B k := Ready s.mem B k
  cipher_len _ _ := by simp [Spec.Sm4.invCipher]
  layout := ⟨by decide,by decide,by decide,by decide,by decide⟩
  keyRegs_ok := by decide
  regs_ok := by decide
  keyArgs_congr h hr hrd hwr _ hf := VG.Proof.Sm4.AArch64.keyArgs_congr h hr hrd hwr hf
  ready_frame h hf hd _ _ := h.frame hf hd
  prepare_wp := prepare_wp
  crypt_wp := by
    intro s B k hb hs hr
    refine WP.mono (crypt_wp .decrypt hb hs hr) fun t ⟨tb,td,tl,tr,tf,to,rd,wr⟩ =>
      ⟨tb,td,tl,tr,tf,?_,rd,wr⟩
    intro j hj
    have hj' : j < 1 := hj
    have hj0 : j = 0 := by omega_using [hj']
    subst j
    change Spec.Aes.bytesAt t.mem (B+BitVec.ofNat 64 (768+16*0)) 16 =
      Spec.Sm4.invCipher k (Spec.Aes.bytesAt s.mem (B+BitVec.ofNat 64 (768+16*0)) 16)
    exact to

abbrev decBlockSpec : BlockSpec decCore := decCoreSpec.toBlock rfl

attribute [local irreducible] Spec.Sm4.invCipher in
theorem invCipher_eq (k : Spec.Sm4.Schedule) : decBlockSpec.cipher k = Spec.Sm4.invCipher k := rfl

theorem prepare_regSafe_x19 : VG.Proof.Modes.AArch64.regSafe .x19 core.prepare = true := by
  show VG.Proof.Modes.AArch64.regSafe .x19 (.seq (.block preparedTable) copySchedule) = true
  rw [VG.Proof.Sm4.AArch64.serialTable.lit_eq]
  decide +kernel

theorem crypt_regSafe_x19 : VG.Proof.Modes.AArch64.regSafe .x19 core.crypt = true := by decide +kernel

theorem keeps_x19 : KeepsReg .x19 core.prepare ∧ KeepsReg .x19 core.crypt :=
  ⟨VG.Proof.Modes.AArch64.keepsReg_of_regSafe prepare_regSafe_x19,
    VG.Proof.Modes.AArch64.keepsReg_of_regSafe crypt_regSafe_x19⟩

attribute [local irreducible] Spec.Sm4.cipher in
theorem cipher_eq (k : Spec.Sm4.Schedule) : blockSpec.cipher k = Spec.Sm4.cipher k := rfl

end VG.Proof.Sm4.AArch64.Serial
