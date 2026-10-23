module

public import VerifiedGarbage.Impl.Sm4.AArch64.Serial.Core
public import VerifiedGarbage.Proof.Framework.AArch64.Tbl
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.Interleave

/-! # SM4 substitution through the existing constant-time register lookup -/

@[expose] public section

namespace VG.Proof.Sm4.AArch64.Serial

open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Tbl
open VG.Impl.Sm4.AArch64.Serial

/-- The three public byte constants used to select a quarter. -/
def Constants (s : State) : Prop :=
  s.v .v4 = bc 64 ∧ s.v .v5 = bc 128 ∧ s.v .v6 = bc 192

/-- All 256 S-box bytes reside in registers, independent of the index. -/
def Table (s : State) : Prop :=
  ∀ k < 256, tbyte s.v k = Spec.Sm4.sbox.getD k 0

def indices : List Instr :=
  [.vop (.dup .s4 .v0 .x10), .vop (.logic .eor .v1 .v0 .v4),
   .vop (.logic .eor .v2 .v0 .v5), .vop (.logic .eor .v3 .v0 .v6)]

theorem substitute_eq : substitute = indices ++ (VG.Impl.Tbl.AArch64.select true ++ ([.umov .w .x10 .v0 0] : List Instr)) := by
  simp only [substitute, indices, List.append_assoc]

theorem indices_run (s : State) (hc : Constants s) :
    ∃ t, runBlock isa indices s = some t ∧
      (∀ e < 16, vbyte (t.v .v0) e = vbyte (ofVWords
        ((s.gpr .x10).setWidth 32) ((s.gpr .x10).setWidth 32)
        ((s.gpr .x10).setWidth 32) ((s.gpr .x10).setWidth 32)) e) ∧
      (∀ e < 16, vbyte (t.v .v1) e = vbyte (t.v .v0) e ^^^ 64) ∧
      (∀ e < 16, vbyte (t.v .v2) e = vbyte (t.v .v0) e ^^^ 128) ∧
      (∀ e < 16, vbyte (t.v .v3) e = vbyte (t.v .v0) e ^^^ 192) ∧
      VOnly [.v0,.v1,.v2,.v3] s t := by
  let x := (s.gpr .x10).setWidth 32
  let a := s.setV .v0 (ofVWords x x x x)
  let b := a.setV .v1 (a.v .v0 ^^^ a.v .v4)
  let c := b.setV .v2 (b.v .v0 ^^^ b.v .v5)
  let d := c.setV .v3 (c.v .v0 ^^^ c.v .v6)
  have h0 : d.v .v0 = ofVWords x x x x := by simp [d,c,b,a,State.setV]
  have h1 : d.v .v1 = ofVWords x x x x ^^^ bc 64 := by simp [d,c,b,a,State.setV,hc.1]
  have h2 : d.v .v2 = ofVWords x x x x ^^^ bc 128 := by simp [d,c,b,a,State.setV,hc.2.1]
  have h3 : d.v .v3 = ofVWords x x x x ^^^ bc 192 := by simp [d,c,b,a,State.setV,hc.2.2]
  refine ⟨d, ?_, fun e _ => by rw [h0], ?_, ?_, ?_, ?_⟩
  · simp only [indices, runBlock_cons]
    change (exec (.vop (.dup .s4 .v0 .x10)) s).bind _ = _
    rw [show exec (.vop (.dup .s4 .v0 .x10)) s = some a from rfl]
    simp only [Option.bind_some, exec_eorv, runStep_some, runBlock_cons, runBlock_nil]
    rfl
  · intro e he; rw [h1,h0,vbyte_xor,vbyte_bc _ he]
  · intro e he; rw [h2,h0,vbyte_xor,vbyte_bc _ he]
  · intro e he; rw [h3,h0,vbyte_xor,vbyte_bc _ he]
  · exact ((VOnly.setV s (by simp) _).trans
      (VOnly.setV a (by simp) _)).trans
      ((VOnly.setV b (by simp) _).trans (VOnly.setV c (by simp) _))

theorem low_word_bytes (v : BitVec 128) :
    v.extractLsb' 0 32 = vbyte v 3 ++ vbyte v 2 ++ vbyte v 1 ++ vbyte v 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  simp only [hi, decide_true, Bool.true_and]
  by_cases h0 : i < 8
  · simp [h0]
  have h08 : 8 ≤ i := by omega
  by_cases h1 : i - 8 < 8
  · simp [h0,h1,show 8 + (i-8) = i by omega]
  by_cases h2 : i - 8 - 8 < 8
  · simp [h0,h1,h2,show 16 + (i-8-8) = i by omega]
  · have h3 : i - 8 - 8 - 8 < 8 := by omega
    simp [h0,h1,h2,h3,show 24 + (i-8-8-8) = i by omega]

theorem dup_low_byte (x : BitVec 32) (j : Nat) (hj : j < 4) :
    vbyte (ofVWords x x x x) j = (x >>> (8*j)).setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [vbyte, ofVWords, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  have h : 8*j+i < 32 := by omega
  simp only [hi,h,decide_true,Bool.true_and,ite_true]

theorem substituted_word (v : BitVec 128) (x : BitVec 32)
    (h : ∀ j < 4, vbyte v j = Spec.Sm4.sbox.getD ((x >>> (8*j)).setWidth 8).toNat 0) :
    v.extractLsb' 0 32 = Spec.Sm4.tau x := by
  rw [low_word_bytes, h 3 (by decide), h 2 (by decide), h 1 (by decide), h 0 (by decide)]
  rfl

theorem Table.of_rows {s t : State} (ht : Table s)
    (hv : ∀ j < 16, t.v (VG.Impl.Tbl.AArch64.treg j) = s.v (VG.Impl.Tbl.AArch64.treg j)) : Table t := by
  intro k hk
  rw [tbyte_congr' hv k hk]
  exact ht k hk

theorem Constants.of_preserved {s t : State} (hc : Constants s)
    (hv : ∀ v, v ∉ [.v0,.v1,.v2,.v3] → t.v v = s.v v) : Constants t := by
  exact ⟨(hv _ (by decide)).trans hc.1,(hv _ (by decide)).trans hc.2.1,
    (hv _ (by decide)).trans hc.2.2⟩

theorem Table.of_preserved {s t : State} (ht : Table s)
    (hv : ∀ v, v ∉ [.v0,.v1,.v2,.v3] → t.v v = s.v v) : Table t := by
  intro k hk
  rw [tbyte_congr' (fun j hj => hv _ (by
    have hn := treg_ne j hj
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨hn.1,hn.2.1,hn.2.2.1,hn.2.2.2.1⟩)) k hk]
  exact ht k hk

/-- Set the public quarter constants without touching the register table. -/
theorem quarterConstants_run (s : State) :
    ∃ t, runBlock isa quarterConstants s = some t ∧ Constants t ∧
      (∀ r, r ≠ .x15 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      (∀ v, v ≠ .v4 → v ≠ .v5 → v ≠ .v6 → t.v v = s.v v) := by
  let a := s.write .w .x15 64
  let b := a.setV .v4 (bc 64)
  let c := b.write .w .x15 128
  let d := c.setV .v5 (bc 128)
  let e := d.write .w .x15 192
  let f := e.setV .v6 (bc 192)
  refine ⟨f,?_,?_,?_,rfl,rfl,rfl,rfl,?_⟩
  · rfl
  · simp [Constants,f,e,d,c,b,a,State.setV,State.write]
  · intro r hr
    simp only [f,e,d,c,b,a,gpr_setV,gpr_write_of_ne _ _ _ hr]
  · intro v h4 h5 h6
    simp only [f,e,d,c,b,a,v_write,v_setV_of_ne _ _ h4,v_setV_of_ne _ _ h5,v_setV_of_ne _ _ h6]

/-- Substitution of all four bytes, preserving the table and public constants. -/
theorem substitute_run (s : State) (hc : Constants s) (ht : Table s) :
    ∃ t, runBlock isa substitute s = some t ∧
      t.gpr .x10 = (Spec.Sm4.tau ((s.gpr .x10).setWidth 32)).setWidth 64 ∧
      (∀ r, r ≠ .x10 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp ∧
      (∀ v, v ∉ [.v0,.v1,.v2,.v3] → t.v v = s.v v) := by
  let x := (s.gpr .x10).setWidth 32
  let I := fun e => vbyte (ofVWords x x x x) e
  obtain ⟨a,ha,h0,h1,h2,h3,hv⟩ := indices_run s hc
  obtain ⟨b,hb,bo,bv⟩ := select_full_run (s := a) I h0
    (fun e he => by rw [h1 e he,h0 e he])
    (fun e he => by rw [h2 e he,h0 e he])
    (fun e he => by rw [h3 e he,h0 e he])
  have tab : ∀ k < 256, tbyte a.v k = Spec.Sm4.sbox.getD k 0 := by
    intro k hk
    rw [tbyte_congr' (fun j hj => hv.2 _ (by
      have := treg_ne j hj
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
      exact ⟨this.1,this.2.1,this.2.2.1,this.2.2.2.1⟩)) k hk]
    exact ht k hk
  have bytes : ∀ j < 4, vbyte (b.v .v0) j = Spec.Sm4.sbox.getD ((x >>> (8*j)).setWidth 8).toNat 0 := by
    intro j hj
    rw [bo j (by omega),tab _ (I j).isLt]
    unfold I
    rw [dup_low_byte x j hj]
  have word : (b.v .v0).extractLsb' 0 32 = Spec.Sm4.tau x := substituted_word _ _ bytes
  let t := b.write .w .x10 ((b.v .v0).extractLsb' 0 32)
  have ku : VOnly [.v0,.v1,.v2,.v3] s b := hv.trans bv
  refine ⟨t,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [substitute_eq,VG.Interleave.runBlock_append,ha,Option.bind_some,VG.Interleave.runBlock_append,hb,Option.bind_some,
      runBlock_cons]
    rw [show exec (.umov .w .x10 .v0 0) b = some t by simp [exec,Size.bits,t]]
    rw [runStep_some,runBlock_nil]
  · simp only [t,gpr_write_self,word,x]
  · intro r hr
    rw [gpr_write_of_ne _ _ _ hr,ku.gpr]
  · simp only [t,mem_write]; exact ku.mem
  · simp only [t,rd_write]; exact ku.rd
  · simp only [t,wr_write]; exact ku.wr
  · change b.sp = s.sp
    rw [ku.1]
  · intro v hv
    exact ku.2 v hv

end VG.Proof.Sm4.AArch64.Serial
