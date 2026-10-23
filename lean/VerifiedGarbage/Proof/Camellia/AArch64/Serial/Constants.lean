module

public import VerifiedGarbage.Proof.Camellia.AArch64.Serial.Lookup
import VerifiedGarbage.Proof.Sm4.AArch64.Serial.Lookup
import VerifiedGarbage.Proof.Sm4.AArch64.Serial.Load
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Loading the public substitution table and rotation masks -/

@[expose] public section
namespace VG.Proof.Camellia.AArch64.Serial
open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Tbl
open VG.Impl.Camellia.AArch64.Serial

theorem quarterConstants_run (s : State) :
    ∃ t, runBlock isa quarterConstants s = some t ∧ Constants t ∧
      (∀ r, r ≠ .x15 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      (∀ v, v ≠ .v4 → v ≠ .v5 → v ≠ .v6 → t.v v = s.v v) :=
  VG.Proof.Sm4.AArch64.Serial.quarterConstants_run s

theorem loadSbox_ok (s : State)
    (readable : InRegions (s.rd ++ s.wr) (s.gpr .x5) 256)
    (bytes : ∀ k < 256, s.mem (s.gpr .x5 + BitVec.ofNat 64 k) =
      Spec.Camellia.sbox1Table.getD k 0) :
    WP isa (.block loadSbox) s fun t => Table t ∧ t = { s with v := t.v } := by
  refine WP.mono (VG.Proof.Sm4.AArch64.Serial.loads_ok s readable 16 (by decide))
    fun t ⟨ht,_,he⟩ => ⟨?_,he⟩
  intro k hk
  rw [tbyte,ht _ (by omega)]
  change (s.mem.read _ 16).extractLsb' (8*(k%16)) 8 = _
  rw [Mem.extractLsb'_read s.mem _ (by omega),VG.Offset.add_add,
    show 16*(k/16)+k%16 = k by omega]
  exact bytes k hk

theorem maskConstants_run (s : State) :
    ∃ t, runBlock isa maskConstants s = some t ∧ Masks t ∧
      (∀ r, r ≠ .x13 → r ≠ .x14 → r ≠ .x15 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      (∀ v, v ≠ .v7 → t.v v = s.v v) := by
  let a := s.write .x .x15 0xff00
  let b := a.write .x .x15
    ((a.read .x .x15 &&& ~~~((0xffff : BitVec 64) <<< 32)) ||| (0xff : BitVec 64) <<< 32)
  let c := b.setV .v7 (ofVDwords (b.gpr .x15) (b.gpr .x15))
  let d := c.write .x .x13 0
  let e := d.write .x .x13
    ((d.read .x .x13 &&& ~~~((0xffff : BitVec 64) <<< 16)) ||| (0xff00 : BitVec 64) <<< 16)
  let f := e.write .x .x13
    ((e.read .x .x13 &&& ~~~((0xffff : BitVec 64) <<< 48)) ||| (0xff : BitVec 64) <<< 48)
  let g := f.write .x .x14 0
  let h := g.write .x .x14
    ((g.read .x .x14 &&& ~~~((0xffff : BitVec 64) <<< 16)) ||| (0xff : BitVec 64) <<< 16)
  let t := h.write .x .x14
    ((h.read .x .x14 &&& ~~~((0xffff : BitVec 64) <<< 32)) ||| (0xff00 : BitVec 64) <<< 32)
  refine ⟨t,?_,?_,?_,rfl,rfl,rfl,rfl,?_⟩
  · have eq : maskConstants = [
        .movz .x .x15 0xff00 0, .movk .x .x15 0xff 2,
        .vop (.dup .d2 .v7 .x15), .movz .x .x13 0 0,
        .movk .x .x13 0xff00 1, .movk .x .x13 0xff 3,
        .movz .x .x14 0 0, .movk .x .x14 0xff 1, .movk .x .x14 0xff00 2] := by
      decide +kernel
    rw [eq]
    rfl
  · simp only [Masks,t,h,g,f,e,d,c,b,a,gpr_write,State.read,Size.bits,
      BitVec.setWidth_eq,↓reduceIte,reduceCtorEq,v_write,v_setV_self]
    constructor
    · congr 1 <;> decide +kernel
    constructor <;> decide +kernel
  · intro r h13 h14 h15
    simp only [t,h,g,f,e,d,c,b,a,gpr_write_of_ne _ _ _ h13,
      gpr_write_of_ne _ _ _ h14,gpr_write_of_ne _ _ _ h15,gpr_setV]
  · intro v hv
    simp only [t,h,g,f,e,d,c,b,a,v_write,v_setV_of_ne _ _ hv]

theorem constants_wp (s : State)
    (readable : InRegions (s.rd ++ s.wr) (s.gpr .x5) 256)
    (bytes : ∀ k < 256, s.mem (s.gpr .x5+BitVec.ofNat 64 k) = Spec.Camellia.sbox1Table.getD k 0) :
    WP isa (.block constants) s fun t => Constants t ∧ Masks t ∧ Table t ∧
      (∀ r, r ∉ [.x13,.x14,.x15] → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  rw [constants,WP.block_append_iff,WP.block_append_iff]
  refine WP.mono (loadSbox_ok s readable bytes) fun a ⟨atab,ae⟩ => ?_
  obtain ⟨b,be,bc,bg,bm,brd,bwr,bsp,bvec⟩ := quarterConstants_run a
  refine WP.of_runBlock ⟨b,be,?_⟩
  obtain ⟨c,ce,cmask,cg,cm,crd,cwr,csp,cvec⟩ := maskConstants_run b
  refine WP.of_runBlock ⟨c,ce,?_,cmask,?_,?_,?_,?_,?_,?_⟩
  · exact ⟨(cvec _ (by decide)).trans bc.1,(cvec _ (by decide)).trans bc.2.1,
      (cvec _ (by decide)).trans bc.2.2⟩
  · intro j hj
    rw [tbyte_congr' (fun i hi => by
      have hn := VG.AArch64.Tbl.treg_ne8 i hi
      exact (cvec _ hn.2.2.2.2.2.2.2).trans
        (bvec _ hn.2.2.2.2.1 hn.2.2.2.2.2.1 hn.2.2.2.2.2.2.1)) j hj]
    exact atab j hj
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    rw [cg _ hr.1 hr.2.1 hr.2.2,bg _ hr.2.2,ae]
  · rw [cm,bm,ae]
  · rw [crd,brd,ae]
  · rw [cwr,bwr,ae]
  · rw [csp,bsp,ae]

end VG.Proof.Camellia.AArch64.Serial
