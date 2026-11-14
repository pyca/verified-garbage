module

public import VerifiedGarbage.Impl.Camellia.AArch64.Serial.Core
public import VerifiedGarbage.Proof.Camellia.SerialPure
public import VerifiedGarbage.Proof.Framework.AArch64.Tbl
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.Interleave
import Mathlib.Tactic.IntervalCases

/-! ### `Camellia.AArch64.Serial.ByteOps`, which only this module used -/

section

/-! # Byte-lane identities for Camellia's register substitution -/

@[expose] public section
namespace VG.Proof.Camellia.AArch64.Serial
open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Tbl
open VG.Impl.Camellia.AArch64.Serial
open VG.Proof.Camellia.Serial

theorem vbyte_map2 (f : (w : Nat) → BitVec w → BitVec w → BitVec w)
    (x y : BitVec 128) (e : Nat) (he : e < 16) :
    vbyte (VArr.b16.map2 f x y) e = f 8 (vbyte x e) (vbyte y e) :=
by
  unfold VArr.map2
  exact vbyte_ofVBytes (fun i => f 8 (vbyte x i) (vbyte y i)) he

theorem vbyte_and (x y : BitVec 128) (e : Nat) :
    vbyte (x &&& y) e = vbyte x e &&& vbyte y e := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [vbyte, hi]

theorem dup_byte (x : BitVec 64) (e : Nat) (he : e < 16) :
    vbyte (ofVDwords x x) e = byte x (e % 8) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [vbyte, ofVDwords, byte, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_append, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
    hi, decide_true, Bool.true_and]
  by_cases h : e < 8
  · simp only [show 8*e+i < 64 by omega_using [hi, h], ite_true, Nat.mod_eq_of_lt h]
  · simp only [show ¬8*e+i < 64 by omega_using [h], ite_false]
    congr 1
    omega_using [he, h]

/-- SHL followed by SRI implements a byte rotation, including the inserted bit. -/
theorem shift_insert_rotate : ∀ sh ∈ [1,7], ∀ x : Byte,
    ((x <<< sh) &&& ~~~(BitVec.allOnes 8 >>> (8-sh))) ||| (x >>> (8-sh)) =
      x.rotateLeft sh := by
  decide +kernel

theorem byte_select_zero (x y : Byte) : x ^^^ ((x ^^^ y) &&& 0) = x := by simp

theorem byte_select_all (x y : Byte) : x ^^^ ((x ^^^ y) &&& 255) = y := by
  change x ^^^ ((x ^^^ y) &&& BitVec.allOnes 8) = y
  rw [BitVec.and_allOnes]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor]
  cases x.getLsbD i <;> cases y.getLsbD i <;> rfl

/-- Rotate selected byte lanes while preserving all scalar state and the table. -/
theorem rotateSelected_run (s : State) (mask : VReg) (sh : Nat)
    (hm1 : mask ≠ .v1) (hsh : sh ∈ [1,7]) :
    ∃ t, runBlock isa (rotateSelected mask sh) s = some t ∧
      (∀ e < 16, vbyte (t.v .v0) e =
        vbyte (s.v .v0) e ^^^
          ((vbyte (s.v .v0) e ^^^ (vbyte (s.v .v0) e).rotateLeft sh) &&&
            vbyte (s.v mask) e)) ∧
      VOnly [.v0,.v1] s t := by
  let a := s.setV .v1 (VArr.b16.map2
    (fun w x y => VShiftOp.shl.eval sh w x y) (s.v .v1) (s.v .v0))
  let b := a.setV .v1 (VArr.b16.map2
    (fun w x y => VShiftOp.sri.eval (8-sh) w x y) (a.v .v1) (a.v .v0))
  let c := b.setV .v0 (VSelOp.bit.eval (b.v .v0) (b.v .v1) (b.v mask))
  have hs : VShiftOp.shl.ok 8 sh = true := by
    rcases (show sh = 1 ∨ sh = 7 by simpa using hsh) with rfl | rfl <;> rfl
  have ht : VShiftOp.sri.ok 8 (8-sh) = true := by
    rcases (show sh = 1 ∨ sh = 7 by simpa using hsh) with rfl | rfl <;> rfl
  refine ⟨c,?_,?_,?_⟩
  · simp only [rotateSelected,runBlock_cons]
    rw [show exec (.vop (.shift .shl .b16 .v1 .v0 sh)) s = some a by
      simp [exec_vop',VOp.eval,VArr.esize,hs,a]]
    simp only [runStep_some,runBlock_cons]
    rw [show exec (.vop (.shift .sri .b16 .v1 .v0 (8-sh))) a = some b by
      simp [exec_vop',VOp.eval,VArr.esize,ht,b]]
    simp only [runStep_some,runBlock_cons]
    rfl
  · intro e he
    simp only [c,b,a,State.setV,ite_true,show (.v0 : VReg) ≠ .v1 by decide,
      hm1,ite_false,VSelOp.eval,
      vbyte_xor,vbyte_and,vbyte_map2 _ _ _ e he,VShiftOp.eval]
    rw [shift_insert_rotate sh hsh]
  · exact ((VOnly.setV s (by simp) _).trans
      (VOnly.setV a (by simp) _)).trans (VOnly.setV b (by simp) _)

theorem low64_eq_packed (v : BitVec 128) (t : Nat → Byte)
    (h : ∀ j < 8, vbyte v j = t j) : v.extractLsb' 0 64 = packed t := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h₁ := congrArg (fun b : Byte => b.getLsbD (i%8)) (h (i/8) (by omega_using [hi]))
  have h₂ := congrArg (fun b : Byte => b.getLsbD (i%8))
    (byte_packed t (i/8) (by omega_using [hi]))
  simp only [vbyte, BitVec.getLsbD_extractLsb', show i%8 < 8 by omega_using [],
    decide_true, Bool.true_and, show 8*(i/8)+i%8=i by omega_using []] at h₁
  simp only [byte, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
    show i%8 < 8 by omega_using [], decide_true, Bool.true_and,
    show 8*(i/8)+i%8=i by omega_using []] at h₂
  simp only [BitVec.getLsbD_extractLsb',hi,decide_true,Bool.true_and,Nat.zero_add]
  exact h₁.trans h₂.symm

end VG.Proof.Camellia.AArch64.Serial

end

end


/-! # Camellia's four S-box variants through one register table -/

@[expose] public section
namespace VG.Proof.Camellia.AArch64.Serial
open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Tbl
open VG.Impl.Camellia.AArch64.Serial
open VG.Proof.Camellia.Serial

def Constants (s : State) : Prop :=
  s.v .v4 = bc 64 ∧ s.v .v5 = bc 128 ∧ s.v .v6 = bc 192

def Masks (s : State) : Prop :=
  s.v .v7 = ofVDwords 0x000000ff0000ff00 0x000000ff0000ff00 ∧
  s.gpr .x13 = 0x00ff0000ff000000 ∧ s.gpr .x14 = 0x0000ff0000ff0000

def Table (s : State) : Prop :=
  ∀ k < 256, tbyte s.v k = Spec.Camellia.sbox1Table.getD k 0

def preChosen (e : Nat) : Bool := e%8 = 1 ∨ e%8 = 4
def leftChosen (e : Nat) : Bool := e%8 = 3 ∨ e%8 = 6
def rightChosen (e : Nat) : Bool := e%8 = 2 ∨ e%8 = 5

theorem pre_mask : ∀ e < 16,
    vbyte (ofVDwords 0x000000ff0000ff00 0x000000ff0000ff00) e =
      if preChosen e then 255 else 0 := by decide +kernel

theorem left_mask : ∀ e < 16,
    vbyte (ofVDwords 0x00ff0000ff000000 0x00ff0000ff000000) e =
      if leftChosen e then 255 else 0 := by decide +kernel

theorem right_mask : ∀ e < 16,
    vbyte (ofVDwords 0x0000ff0000ff0000 0x0000ff0000ff0000) e =
      if rightChosen e then 255 else 0 := by decide +kernel

theorem widen {s t : State} (h : VOnly [.v0,.v1] s t) :
    VOnly [.v0,.v1,.v2,.v3] s t := by
  refine ⟨h.1,fun r hr => h.2 r ?_⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr ⊢
  exact ⟨hr.1,hr.2.1⟩

theorem Constants.preserved {s t : State} (hc : Constants s)
    (hv : VOnly [.v0,.v1,.v2,.v3] s t) : Constants t :=
  ⟨(hv.2 _ (by decide)).trans hc.1,(hv.2 _ (by decide)).trans hc.2.1,
    (hv.2 _ (by decide)).trans hc.2.2⟩

theorem Masks.preserved {s t : State} (hm : Masks s)
    (hv : VOnly [.v0,.v1,.v2,.v3] s t) : Masks t := by
  exact ⟨(hv.2 _ (by decide)).trans hm.1,
    congrFun hv.gpr _ |>.trans hm.2.1, congrFun hv.gpr _ |>.trans hm.2.2⟩

theorem Table.preserved {s t : State} (ht : Table s)
    (hv : VOnly [.v0,.v1,.v2,.v3] s t) : Table t := by
  intro k hk
  rw [tbyte_congr' (fun j hj => hv.2 _ (by
    have hn := treg_ne j hj
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨hn.1,hn.2.1,hn.2.2.1,hn.2.2.2.1⟩)) k hk]
  exact ht k hk

theorem rotateChosen_run (s : State) (mask : VReg) (sh : Nat)
    (hm : mask ≠ .v1) (hs : sh ∈ [1,7]) (chosen : Nat → Bool)
    (hc : ∀ e < 16, vbyte (s.v mask) e = if chosen e then 255 else 0) :
    ∃ t, runBlock isa (rotateSelected mask sh) s = some t ∧
      (∀ e < 16, vbyte (t.v .v0) e =
        if chosen e then (vbyte (s.v .v0) e).rotateLeft sh else vbyte (s.v .v0) e) ∧
      VOnly [.v0,.v1,.v2,.v3] s t := by
  obtain ⟨t,ht,hb,hv⟩ := rotateSelected_run s mask sh hm hs
  refine ⟨t,ht,?_,widen hv⟩
  intro e he
  rw [hb e he,hc e he]
  cases chosen e
  · exact byte_select_zero _ _
  · exact byte_select_all _ _

theorem indices_run (s : State) (hc : Constants s) :
    ∃ t, runBlock isa indices s = some t ∧
      t.v .v0 = s.v .v0 ∧
      (∀ e < 16, vbyte (t.v .v1) e = vbyte (s.v .v0) e ^^^ 64) ∧
      (∀ e < 16, vbyte (t.v .v2) e = vbyte (s.v .v0) e ^^^ 128) ∧
      (∀ e < 16, vbyte (t.v .v3) e = vbyte (s.v .v0) e ^^^ 192) ∧
      VOnly [.v0,.v1,.v2,.v3] s t := by
  let a := s.setV .v1 (s.v .v0 ^^^ s.v .v4)
  let b := a.setV .v2 (a.v .v0 ^^^ a.v .v5)
  let c := b.setV .v3 (b.v .v0 ^^^ b.v .v6)
  have h0 : c.v .v0 = s.v .v0 := by simp [c,b,a,State.setV]
  have h1 : c.v .v1 = s.v .v0 ^^^ bc 64 := by simp [c,b,a,State.setV,hc.1]
  have h2 : c.v .v2 = s.v .v0 ^^^ bc 128 := by simp [c,b,a,State.setV,hc.2.1]
  have h3 : c.v .v3 = s.v .v0 ^^^ bc 192 := by simp [c,b,a,State.setV,hc.2.2]
  refine ⟨c,?_,h0,?_,?_,?_,?_⟩
  · simp only [indices,runBlock_cons,exec_eorv,runStep_some,runBlock_nil]
    rfl
  · intro e he; rw [h1,vbyte_xor,vbyte_bc _ he]
  · intro e he; rw [h2,vbyte_xor,vbyte_bc _ he]
  · intro e he; rw [h3,vbyte_xor,vbyte_bc _ he]
  · exact ((VOnly.setV s (by simp) _).trans
      (VOnly.setV a (by simp) _)).trans (VOnly.setV b (by simp) _)

/-- Lookup in the single SBOX1 table, retaining every prepared constant. -/
theorem lookup_run (s : State) (hc : Constants s) (ht : Table s) :
    ∃ t, runBlock isa (indices ++ VG.Impl.Tbl.AArch64.select true) s = some t ∧
      (∀ e < 16, vbyte (t.v .v0) e = Spec.Camellia.sbox1 (vbyte (s.v .v0) e)) ∧
      VOnly [.v0,.v1,.v2,.v3] s t := by
  obtain ⟨a,ha,h0,h1,h2,h3,hv⟩ := indices_run s hc
  let I := fun e => vbyte (s.v .v0) e
  obtain ⟨b,hb,bo,bv⟩ := select_full_run (s := a) I
    (fun e _ => by rw [h0]) h1 h2 h3
  refine ⟨b,?_,?_,hv.trans bv⟩
  · rw [VG.Interleave.runBlock_append,ha,Option.bind_some,hb]
  · intro e he
    rw [bo e he,ht.preserved hv _ (I e).isLt]
    rfl

/-- The rotations surrounding SBOX1 are exactly SBOX1, SBOX2, SBOX3 and SBOX4. -/
theorem substituted_byte (x : BitVec 64) (j : Nat) (hj : j < 8) :
    (let a := if preChosen j then (byte x j).rotateLeft 1 else byte x j
     let b := Spec.Camellia.sbox1 a
     let c := if leftChosen j then b.rotateLeft 1 else b
     if rightChosen j then c.rotateLeft 7 else c) = substitutedByte x j := by
  interval_cases j <;> rfl

/-- The complete constant-time substitution preserves the register-resident table. -/
theorem substitute_run (s : State) (hc : Constants s) (hm : Masks s) (ht : Table s) :
    ∃ t, runBlock isa substitute s = some t ∧
      t.gpr .x10 = substituted (s.gpr .x10) ∧
      (∀ r, r ≠ .x10 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      (∀ v, v ∉ [.v0,.v1,.v2,.v3] → t.v v = s.v v) := by
  let a := s.setV .v0 (ofVDwords (s.gpr .x10) (s.gpr .x10))
  have av : VOnly [.v0,.v1,.v2,.v3] s a := VOnly.setV s (by simp) _
  obtain ⟨b,hb,bb,bv⟩ := rotateChosen_run a .v7 1 (by decide) (by simp)
    preChosen (fun j hj => by
      rw [(hm.preserved av).1]
      exact pre_mask j hj)
  have ab := av.trans bv
  obtain ⟨c,hc',cb,cv⟩ := lookup_run b (hc.preserved ab) (ht.preserved ab)
  have ac := ab.trans cv
  let d := c.setV .v3 (ofVDwords (c.gpr .x13) (c.gpr .x13))
  have dv : VOnly [.v0,.v1,.v2,.v3] c d := VOnly.setV c (by simp) _
  have dc : d.v .v0 = c.v .v0 := by simp [d,State.setV]
  obtain ⟨e,he,eb,ev⟩ := rotateChosen_run d .v3 1 (by decide) (by simp)
    leftChosen (fun j hj => by
      change vbyte (ofVDwords (c.gpr .x13) (c.gpr .x13)) j = _
      rw [(hm.preserved ac).2.1]
      exact left_mask j hj)
  have ae := (ac.trans dv).trans ev
  let f := e.setV .v3 (ofVDwords (e.gpr .x14) (e.gpr .x14))
  have fv : VOnly [.v0,.v1,.v2,.v3] e f := VOnly.setV e (by simp) _
  have fe : f.v .v0 = e.v .v0 := by simp [f,State.setV]
  obtain ⟨g,hg,gb,gv⟩ := rotateChosen_run f .v3 7 (by decide) (by simp)
    rightChosen (fun j hj => by
      change vbyte (ofVDwords (e.gpr .x14) (e.gpr .x14)) j = _
      rw [(hm.preserved ae).2.2]
      exact right_mask j hj)
  have ag := (ae.trans fv).trans gv
  have word : (g.v .v0).extractLsb' 0 64 = substituted (s.gpr .x10) := by
    apply low64_eq_packed
    intro j hj
    rw [gb j (by omega_using [hj]),fe,eb j (by omega_using [hj]),dc,cb j (by omega_using [hj]),bb j (by omega_using [hj])]
    have aj : vbyte (a.v .v0) j = byte (s.gpr .x10) j := by
      rw [show a.v .v0 = ofVDwords (s.gpr .x10) (s.gpr .x10) from rfl,
        dup_byte _ j (by omega_using [hj]),Nat.mod_eq_of_lt hj]
    rw [aj]
    exact substituted_byte _ j hj
  let t := g.write .x .x10 ((g.v .v0).extractLsb' 0 64)
  refine ⟨t,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have hdup0 : runBlock isa [.vop (.dup .d2 .v0 .x10)] s = some a := rfl
    have hdup13 : runBlock isa [.vop (.dup .d2 .v3 .x13)] c = some d := rfl
    have hdup14 : runBlock isa [.vop (.dup .d2 .v3 .x14)] e = some f := rfl
    have eq : substitute = [.vop (.dup .d2 .v0 .x10)] ++
        (rotateSelected .v7 1 ++ ((indices ++ VG.Impl.Tbl.AArch64.select true) ++
        ([.vop (.dup .d2 .v3 .x13)] ++ (rotateSelected .v3 1 ++
        ([.vop (.dup .d2 .v3 .x14)] ++ (rotateSelected .v3 7 ++
        [.umov .x .x10 .v0 0])))))) := by
      simp only [substitute,List.append_assoc]
    rw [eq,VG.Interleave.runBlock_append,hdup0,Option.bind_some,
      VG.Interleave.runBlock_append,hb,Option.bind_some,
      VG.Interleave.runBlock_append,hc',Option.bind_some,
      VG.Interleave.runBlock_append,hdup13,Option.bind_some,
      VG.Interleave.runBlock_append,he,Option.bind_some,
      VG.Interleave.runBlock_append,hdup14,Option.bind_some,
      VG.Interleave.runBlock_append,hg,Option.bind_some,runBlock_cons]
    rw [show exec (.umov .x .x10 .v0 0) g = some t by
      simp [exec,Size.bits,t]]
    rw [runStep_some,runBlock_nil]
  · simpa only [t,gpr_write_self,Size.bits,BitVec.setWidth_eq] using word
  · intro r hr
    rw [show t.gpr r = g.gpr r from gpr_write_of_ne _ _ _ hr,ag.gpr]
  · exact ag.mem
  · exact ag.rd
  · exact ag.wr
  · change g.sp = s.sp
    rw [ag.1]
  · exact ag.2

end VG.Proof.Camellia.AArch64.Serial
