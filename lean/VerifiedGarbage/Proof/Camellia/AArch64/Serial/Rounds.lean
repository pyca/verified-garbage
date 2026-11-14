module

public import VerifiedGarbage.Proof.Camellia.AArch64.Serial.Lookup
public import VerifiedGarbage.Impl.Camellia.AArch64.Serial.Core
public import VerifiedGarbage.Proof.Camellia.SerialPure
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Interleave
public import VerifiedGarbage.Proof.Camellia.Words

/-! ### `Camellia.AArch64.Serial.Round`, which only this module used -/

section

/-! ### `Camellia.AArch64.Serial.Linear`, which only this module used -/

section

/-! # Scalar execution of Camellia's byte diffusion -/

@[expose] public section
namespace VG.Proof.Camellia.AArch64.Serial
open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Impl.Camellia.AArch64.Serial
open VG.Proof.Camellia.Serial

theorem linear_run (s : State) :
    ∃ t, runBlock isa linear s = some t ∧
      t.gpr .x10 = linearWord (s.gpr .x10) ∧
      (∀ r, r ∉ [.x10,.x11,.x12,.x16,.x17] → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v := by
  let a := s.write .x .x11 (s.read .x .x10 >>> 32)
  let b := a.write .w .x12 (a.read .w .x10 + (0 : BitVec 32))
  let c := b.write .w .x16 (b.read .w .x11 ^^^ (b.read .w .x11).rotateRight 8)
  let d := c.write .w .x16 (c.read .w .x16 ^^^ (c.read .w .x11).rotateRight 16)
  let e := d.write .w .x17 ((d.read .w .x12 ++ d.read .w .x12).extractLsb' 8 32)
  let f := e.write .w .x17 (e.read .w .x17 ^^^ (e.read .w .x12).rotateRight 16)
  let g := f.write .w .x17 (f.read .w .x17 ^^^ (f.read .w .x12).rotateRight 24)
  let h := g.write .w .x16 (g.read .w .x16 ^^^ g.read .w .x17)
  let i := h.write .w .x12 (h.read .w .x11 ^^^ (h.read .w .x11).rotateRight 24)
  let j := i.write .w .x12 (i.read .w .x12 ^^^ i.read .w .x17)
  let k := j.write .x .x10 (j.read .x .x16 <<< 32)
  let t := k.write .x .x10 (k.read .x .x10 ||| k.read .x .x12)
  refine ⟨t,?_,?_,?_,rfl,rfl,rfl,rfl,rfl⟩
  · rfl
  · simp only [t,k,j,i,h,g,f,e,d,c,b,a,State.read,Size.bits,gpr_write,
      BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),BitVec.setWidth_eq,
      ↓reduceIte,reduceCtorEq]
    simp only [extract_self _ 8 (by decide)]
    rw [← BitVec.setWidth_append_eq_shiftLeft_setWidth_or]
    simp only [BitVec.setWidth_eq]
    simp only [show ∀ x : BitVec 32, x + (0 : BitVec 32) = x from
      fun x => BitVec.add_zero x,linearWord]
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [t,k,j,i,h,g,f,e,d,c,b,a,gpr_write_of_ne _ _ _ hr.1,
      gpr_write_of_ne _ _ _ hr.2.1,gpr_write_of_ne _ _ _ hr.2.2.1,
      gpr_write_of_ne _ _ _ hr.2.2.2.1,gpr_write_of_ne _ _ _ hr.2.2.2.2]

end VG.Proof.Camellia.AArch64.Serial

end

end


/-! # Scalar Feistel rounds with the register substitution table -/

@[expose] public section
namespace VG.Proof.Camellia.AArch64.Serial
open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Impl.Camellia.AArch64.Serial
open VG.Proof.Camellia.Serial

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
  · rw [mixKey,runBlock_cons,exec_ldr_x ⟨by omega_using [],by omega_using [hk]⟩ hr,runStep_some,
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

end

end

/-! ### `Camellia.AArch64.Serial.Fl`, which only this module used -/

section

/-! # The scalar FL and inverse-FL half-word transformations -/

@[expose] public section
namespace VG.Proof.Camellia.AArch64.Serial
open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Impl.Camellia.AArch64.Serial
open VG.Proof.Camellia.Serial

theorem rotate31 (x : BitVec 32) : x.rotateRight 31 = x.rotateLeft 1 := by
  simp only [BitVec.rotateRight_def,BitVec.rotateLeft_def,Nat.reduceMod,Nat.reduceSub]
  exact BitVec.or_comm _ _

theorem flLow_run (s : State) :
    ∃ t, runBlock isa flLow s = some t ∧
      (t.gpr .x12).setWidth 32 = (s.gpr .x12).setWidth 32 ^^^
        ((s.gpr .x10).setWidth 32 &&& (s.gpr .x16).setWidth 32).rotateLeft 1 ∧
      t.gpr .x12 = ((t.gpr .x12).setWidth 32).setWidth 64 ∧
      (∀ r, r ≠ .x11 → r ≠ .x12 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v := by
  let a := s.write .w .x11 (s.read .w .x10 &&& s.read .w .x16)
  let b := a.write .w .x11 ((a.read .w .x11 ++ a.read .w .x11).extractLsb' 31 32)
  let t := b.write .w .x12 (b.read .w .x12 ^^^ b.read .w .x11)
  refine ⟨t,rfl,?_,?_,?_,rfl,rfl,rfl,rfl,rfl⟩
  · simp only [t,b,a,State.read,Size.bits,gpr_write,
      BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),BitVec.setWidth_eq,
      ↓reduceIte,reduceCtorEq,extract_self _ 31 (by decide),rotate31]
  · simp only [t,gpr_write_self,Size.bits,
      BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),BitVec.setWidth_eq]
  · intro r h11 h12
    simp only [t,b,a,gpr_write_of_ne _ _ _ h11,gpr_write_of_ne _ _ _ h12]

theorem flHigh_run (s : State) :
    ∃ t, runBlock isa flHigh s = some t ∧
      (t.gpr .x10).setWidth 32 = (s.gpr .x10).setWidth 32 ^^^
        ((s.gpr .x12).setWidth 32 ||| (s.gpr .x8).setWidth 32) ∧
      t.gpr .x10 = ((t.gpr .x10).setWidth 32).setWidth 64 ∧
      (∀ r, r ≠ .x10 → r ≠ .x11 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v := by
  let a := s.write .w .x11 (s.read .w .x12 ||| s.read .w .x8)
  let t := a.write .w .x10 (a.read .w .x10 ^^^ a.read .w .x11)
  refine ⟨t,rfl,?_,?_,?_,rfl,rfl,rfl,rfl,rfl⟩
  · simp only [t,a,State.read,Size.bits,gpr_write,
      BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),BitVec.setWidth_eq,
      ↓reduceIte,reduceCtorEq]
  · simp only [t,gpr_write_self,Size.bits,
      BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),BitVec.setWidth_eq]
  · intro r h10 h11
    simp only [t,a,gpr_write_of_ne _ _ _ h10,gpr_write_of_ne _ _ _ h11]

theorem flInput_run {s : State} {r : Reg} {k : Nat}
    (hr : r = .x6 ∨ r = .x7) (hk : k < 34)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 (256+8*k)) 8) :
    ∃ t, runBlock isa (flInput r k) s = some t ∧
      t.gpr .x8 = rev64 (s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 (256+8*k)) 64) ∧
      (t.gpr .x10).setWidth 32 = (s.gpr r >>> 32).setWidth 32 ∧
      (t.gpr .x12).setWidth 32 = (s.gpr r).setWidth 32 ∧
      (t.gpr .x16).setWidth 32 = (t.gpr .x8 >>> 32).setWidth 32 ∧
      (∀ q, q ∉ [.x8,.x10,.x12,.x16] → t.gpr q = s.gpr q) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v := by
  let a := s.write .x .x8 (s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 (256+8*k)) 64)
  let b := a.write .x .x8 (rev64 (a.read .x .x8))
  let c := b.write .x .x10 (b.read .x r >>> 32)
  let d := c.write .w .x12 (c.read .w r + (0 : BitVec 32))
  let t := d.write .x .x16 (d.read .x .x8 >>> 32)
  refine ⟨t,?_,?_,?_,?_,?_,?_,rfl,rfl,rfl,rfl,rfl⟩
  · rw [flInput,runBlock_cons,exec_ldr_x ⟨by omega_using [],by omega_using [hk]⟩ hread,runStep_some]
    rfl
  · simp only [t,d,c,b,a,gpr_write,State.read,Size.bits,BitVec.setWidth_eq,
      ↓reduceIte,reduceCtorEq]
  · rcases hr with rfl | rfl <;>
      simp only [t,d,c,b,a,gpr_write,State.read,Size.bits,BitVec.setWidth_eq,
        ↓reduceIte,reduceCtorEq]
  · rcases hr with rfl | rfl <;>
      simp only [t,d,c,b,a,gpr_write,State.read,Size.bits,BitVec.setWidth_eq,
        BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),
        show ∀ x : BitVec 32, x + (0 : BitVec 32) = x from fun x => BitVec.add_zero x,
        ↓reduceIte,reduceCtorEq]
  · simp only [t,d,c,b,a,gpr_write,State.read,Size.bits,BitVec.setWidth_eq,
      ↓reduceIte,reduceCtorEq]
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hq
    simp only [t,d,c,b,a,gpr_write_of_ne _ _ _ hq.1,
      gpr_write_of_ne _ _ _ hq.2.1,gpr_write_of_ne _ _ _ hq.2.2.1,
      gpr_write_of_ne _ _ _ hq.2.2.2]

theorem joinHalves_run {s : State} {r : Reg} (hr : r ≠ .x12)
    (hi : s.gpr .x10 = ((s.gpr .x10).setWidth 32).setWidth 64)
    (hl : s.gpr .x12 = ((s.gpr .x12).setWidth 32).setWidth 64) :
    ∃ t, runBlock isa (joinHalves r) s = some t ∧
      t.gpr r = (s.gpr .x10).setWidth 32 ++ (s.gpr .x12).setWidth 32 ∧
      (∀ q, q ≠ r → t.gpr q = s.gpr q) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v := by
  let a := s.write .x r (s.read .x .x10 <<< 32)
  let t := a.write .x r (a.read .x r ||| a.read .x .x12)
  refine ⟨t,rfl,?_,?_,rfl,rfl,rfl,rfl,rfl⟩
  · simp only [t,a,gpr_write_self,State.read,Size.bits,BitVec.setWidth_eq,
      gpr_write_of_ne _ _ _ hr.symm]
    rw [hi,hl,← BitVec.setWidth_append_eq_shiftLeft_setWidth_or]
    simp only [BitVec.setWidth_eq,
      BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)]
  · intro q hq
    simp only [t,a,gpr_write_of_ne _ _ _ hq]

theorem fl_run {s : State} {r : Reg} {k : Nat} (inv : Bool)
    (hr : r = .x6 ∨ r = .x7) (hk : k < 34)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 (256+8*k)) 8) :
    ∃ t, runBlock isa (fl r k inv) s = some t ∧
      t.gpr r = (if inv then Spec.Camellia.flinv else Spec.Camellia.fl) (s.gpr r)
        (rev64 (s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 (256+8*k)) 64)) ∧
      (∀ q, q ≠ r → q ∉ [.x8,.x10,.x11,.x12,.x16] → t.gpr q = s.gpr q) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v := by
  obtain ⟨u,ue,u8,u10,u12,u16,ug,um,urd,uwr,usp,uvec⟩ := flInput_run hr hk hread
  have hr12 : r ≠ .x12 := by rcases hr with rfl | rfl <;> decide
  cases inv
  case false =>
    obtain ⟨v,ve,vl,vzero,vg,vm,vrd,vwr,vsp,vvec⟩ := flLow_run u
    obtain ⟨w,we,wh,wzero,wg,wm,wrd,wwr,wsp,wvec⟩ := flHigh_run v
    have wlow : w.gpr .x12 = ((w.gpr .x12).setWidth 32).setWidth 64 := by
      rw [wg _ (by decide) (by decide)]
      exact vzero
    obtain ⟨t,te,tr,tg,tm,trd,twr,tsp,tvec⟩ := joinHalves_run hr12 wzero wlow
    have vl' : (v.gpr .x12).setWidth 32 = (s.gpr r).setWidth 32 ^^^
        ((s.gpr r >>> 32).setWidth 32 &&&
          (rev64 (s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 (256+8*k)) 64) >>> 32).setWidth 32).rotateLeft 1 := by
      rw [vl,u12,u10,u16,u8]
    have wh' : (w.gpr .x10).setWidth 32 = (s.gpr r >>> 32).setWidth 32 ^^^
        ((v.gpr .x12).setWidth 32 |||
          (rev64 (s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 (256+8*k)) 64)).setWidth 32) := by
      rw [wh,vg .x10 (by decide) (by decide),vg .x8 (by decide) (by decide),u10,u8]
    refine ⟨t,?_,?_,?_,tm.trans (wm.trans (vm.trans um)),
      trd.trans (wrd.trans (vrd.trans urd)),twr.trans (wwr.trans (vwr.trans uwr)),
      tsp.trans (wsp.trans (vsp.trans usp)),tvec.trans (wvec.trans (vvec.trans uvec))⟩
    · change runBlock isa (flInput r k ++ (flLow ++ flHigh) ++ joinHalves r) s = some t
      rw [VG.Interleave.runBlock_append,VG.Interleave.runBlock_append,ue,Option.bind_some,
        VG.Interleave.runBlock_append,ve,Option.bind_some,we,Option.bind_some,te]
    · rw [tr,wh',wg _ (by decide) (by decide),vl']
      rfl
    · intro q hqr hn
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hn
      rw [tg _ hqr,wg _ hn.2.1 hn.2.2.1,vg _ hn.2.2.1 hn.2.2.2.1,
        ug _ (by
          simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
          exact ⟨hn.1,hn.2.1,hn.2.2.2⟩)]
  case true =>
    obtain ⟨v,ve,vh,vzero,vg,vm,vrd,vwr,vsp,vvec⟩ := flHigh_run u
    obtain ⟨w,we,wl,wzero,wg,wm,wrd,wwr,wsp,wvec⟩ := flLow_run v
    have whigh : w.gpr .x10 = ((w.gpr .x10).setWidth 32).setWidth 64 := by
      rw [wg _ (by decide) (by decide)]
      exact vzero
    obtain ⟨t,te,tr,tg,tm,trd,twr,tsp,tvec⟩ := joinHalves_run hr12 whigh wzero
    have vh' : (v.gpr .x10).setWidth 32 = (s.gpr r >>> 32).setWidth 32 ^^^
        ((s.gpr r).setWidth 32 |||
          (rev64 (s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 (256+8*k)) 64)).setWidth 32) := by
      rw [vh,u10,u12,u8]
    have wl' : (w.gpr .x12).setWidth 32 = (s.gpr r).setWidth 32 ^^^
        ((v.gpr .x10).setWidth 32 &&&
          (rev64 (s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 (256+8*k)) 64) >>> 32).setWidth 32).rotateLeft 1 := by
      rw [wl,vg .x12 (by decide) (by decide),vg .x16 (by decide) (by decide),u12,u16,u8]
    refine ⟨t,?_,?_,?_,tm.trans (wm.trans (vm.trans um)),
      trd.trans (wrd.trans (vrd.trans urd)),twr.trans (wwr.trans (vwr.trans uwr)),
      tsp.trans (wsp.trans (vsp.trans usp)),tvec.trans (wvec.trans (vvec.trans uvec))⟩
    · change runBlock isa (flInput r k ++ (flHigh ++ flLow) ++ joinHalves r) s = some t
      rw [VG.Interleave.runBlock_append,VG.Interleave.runBlock_append,ue,Option.bind_some,
        VG.Interleave.runBlock_append,ve,Option.bind_some,we,Option.bind_some,te]
    · rw [tr,wl',wg _ (by decide) (by decide),vh']
      rfl
    · intro q hqr hn
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hn
      rw [tg _ hqr,wg _ hn.2.2.1 hn.2.2.2.1,vg _ hn.2.1 hn.2.2.1,
        ug _ (by
          simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
          exact ⟨hn.1,hn.2.1,hn.2.2.2⟩)]

end VG.Proof.Camellia.AArch64.Serial

end

end


/-! # Six-round groups using the existing word-oriented Camellia model -/

@[expose] public section
namespace VG.Proof.Camellia.AArch64.Serial
open VG VG.AArch64
open VG.Impl.Camellia.AArch64.Serial

def written : List Reg := [.x6,.x7,.x8,.x10,.x11,.x12,.x16,.x17]

def halves (s : State) : BitVec 64 × BitVec 64 := (s.gpr .x6,s.gpr .x7)

def keyWord (s : State) (j : Nat) : BitVec 64 :=
  rev64 (s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 (256+8*j)) 64)

theorem pair_run (s : State) (k : Nat) (hk : k+1 < 34)
    (hc : Constants s) (hm : Masks s) (ht : Table s)
    (hr : ∀ j < 34, InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 (256+8*j)) 8) :
    ∃ t, runBlock isa (roundPair k) s = some t ∧
      halves t = VG.Proof.Camellia.pair (keyWord s k) (keyWord s (k+1)) (halves s) ∧
      Constants t ∧ Masks t ∧ Table t ∧
      (∀ r, r ∉ written → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  obtain ⟨u,ue,uv,uc,um,ut,ug,umem,urd,uwr,usp⟩ :=
    f_run (a := .x6) (b := .x7) (Or.inl rfl) (Or.inr rfl) (by omega_using [hk]) hc hm ht (hr k (by omega_using [hk]))
  have ur : InRegions (u.rd ++ u.wr) (u.gpr .x5 + BitVec.ofNat 64 (256+8*(k+1))) 8 := by
    rw [urd,uwr,ug .x5 (by decide) (by decide)]
    exact hr (k+1) hk
  obtain ⟨v,ve,vv,vc,vm,vt,vg,vmem,vrd,vwr,vsp⟩ :=
    f_run (a := .x7) (b := .x6) (Or.inr rfl) (Or.inl rfl) hk uc um ut ur
  refine ⟨v,?_,?_,vc,vm,vt,?_,vmem.trans umem,vrd.trans urd,vwr.trans uwr,vsp.trans usp⟩
  · rw [roundPair,VG.Interleave.runBlock_append,ue,Option.bind_some,ve]
  · simp only [halves,VG.Proof.Camellia.pair,keyWord]
    rw [vv,vg .x7 (by decide) (by decide),uv,ug .x6 (by decide) (by decide),
      umem,ug .x5 (by decide) (by decide)]
  · intro r hr
    have h6 : r ≠ .x6 := fun h => hr (h ▸ (by decide : Reg.x6 ∈ written))
    have h7 : r ≠ .x7 := fun h => hr (h ▸ (by decide : Reg.x7 ∈ written))
    have hrest : r ∉ [.x8,.x10,.x11,.x12,.x16,.x17] := by
      intro h
      apply hr
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
    exact (vg r h6 hrest).trans (ug r h7 hrest)

def pairs (K : Nat → BitVec 64) (k n : Nat) (d : BitVec 64 × BitVec 64) :
    BitVec 64 × BitVec 64 :=
  (List.range n).foldl (fun d i => VG.Proof.Camellia.pair (K (k+2*i)) (K (k+2*i+1)) d) d

theorem pairs_succ (K : Nat → BitVec 64) (k n : Nat) (d : BitVec 64 × BitVec 64) :
    pairs K k (n+1) d = VG.Proof.Camellia.pair (K (k+2*n)) (K (k+2*n+1)) (pairs K k n d) := by
  simp only [pairs,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]

theorem pairs_run (s : State) (k n : Nat) (hk : k+2*n ≤ 34)
    (hc : Constants s) (hm : Masks s) (ht : Table s)
    (hr : ∀ j < 34, InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 (256+8*j)) 8) :
    ∃ t, runBlock isa ((List.range n).flatMap fun j => roundPair (k+2*j)) s = some t ∧
      halves t = pairs (keyWord s) k n (halves s) ∧
      Constants t ∧ Masks t ∧ Table t ∧
      (∀ r, r ∉ written → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  induction n with
  | zero => exact ⟨s,rfl,rfl,hc,hm,ht,fun _ _ => rfl,rfl,rfl,rfl,rfl⟩
  | succ n ih =>
    obtain ⟨u,ue,uv,uc,um,ut,ug,umem,urd,uwr,usp⟩ := ih (by omega_using [hk])
    have ur : ∀ j < 34, InRegions (u.rd ++ u.wr) (u.gpr .x5 + BitVec.ofNat 64 (256+8*j)) 8 := by
      intro j hj
      rw [urd,uwr,ug .x5 (by decide)]
      exact hr j hj
    obtain ⟨v,ve,vv,vc,vm,vt,vg,vmem,vrd,vwr,vsp⟩ := pair_run u (k+2*n) (by omega_using [hk]) uc um ut ur
    refine ⟨v,?_,?_,vc,vm,vt,fun r h => (vg r h).trans (ug r h),
      vmem.trans umem,vrd.trans urd,vwr.trans uwr,vsp.trans usp⟩
    · rw [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
        VG.Interleave.runBlock_append,ue,Option.bind_some,ve]
    · rw [vv,pairs_succ,uv]
      simp only [keyWord,umem,ug .x5 (by decide),Nat.add_assoc]

theorem six_run (s : State) (k : Nat) (hk : k+6 ≤ 34)
    (hc : Constants s) (hm : Masks s) (ht : Table s)
    (hr : ∀ j < 34, InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 (256+8*j)) 8) :
    ∃ t, runBlock isa (six k) s = some t ∧
      halves t = pairs (keyWord s) k 3 (halves s) ∧
      Constants t ∧ Masks t ∧ Table t ∧
      (∀ r, r ∉ written → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp :=
  pairs_run s k 3 hk hc hm ht hr

theorem flPair_run (s : State) (k : Nat) (hk : k+1 < 34)
    (hc : Constants s) (hm : Masks s) (ht : Table s)
    (hr : ∀ j < 34, InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 (256+8*j)) 8) :
    ∃ t, runBlock isa (flPair k) s = some t ∧
      halves t = (Spec.Camellia.fl (s.gpr .x6) (keyWord s k),
        Spec.Camellia.flinv (s.gpr .x7) (keyWord s (k+1))) ∧
      Constants t ∧ Masks t ∧ Table t ∧
      (∀ r, r ∉ written → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  obtain ⟨u,ue,uv,ug,umem,urd,uwr,usp,uvec⟩ :=
    fl_run false (r := .x6) (Or.inl rfl) (by omega_using [hk]) (hr k (by omega_using [hk]))
  have ur : InRegions (u.rd ++ u.wr) (u.gpr .x5 + BitVec.ofNat 64 (256+8*(k+1))) 8 := by
    rw [urd,uwr,ug .x5 (by decide) (by decide)]
    exact hr (k+1) hk
  obtain ⟨v,ve,vv,vg,vmem,vrd,vwr,vsp,vvec⟩ :=
    fl_run true (r := .x7) (Or.inr rfl) hk ur
  have other : ∀ r, r ∉ written → v.gpr r = s.gpr r := by
    intro r hr
    have h6 : r ≠ .x6 := fun h => hr (h ▸ (by decide : Reg.x6 ∈ written))
    have h7 : r ≠ .x7 := fun h => hr (h ▸ (by decide : Reg.x7 ∈ written))
    have hrest : r ∉ [.x8,.x10,.x11,.x12,.x16] := by
      simp only [written,List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
      exact ⟨hr.2.2.1,hr.2.2.2.1,hr.2.2.2.2.1,hr.2.2.2.2.2.1,hr.2.2.2.2.2.2.1⟩
    exact (vg r h7 hrest).trans (ug r h6 hrest)
  have tv : v.v = s.v := vvec.trans uvec
  refine ⟨v,?_,?_,?_,?_,?_,other,vmem.trans umem,vrd.trans urd,vwr.trans uwr,vsp.trans usp⟩
  · rw [flPair,VG.Interleave.runBlock_append,ue,Option.bind_some,ve]
  · simp only [halves]
    rw [vg .x6 (by decide) (by decide),uv,vv,ug .x7 (by decide) (by decide),
      umem,ug .x5 (by decide) (by decide)]
    rfl
  · simpa only [Constants,tv] using hc
  · refine ⟨by rw [tv]; exact hm.1,?_,?_⟩
    · rw [other .x13 (by decide)]; exact hm.2.1
    · rw [other .x14 (by decide)]; exact hm.2.2
  · simpa only [Table,tv] using ht

def partialRounds (E : Nat → BitVec 64) (d : BitVec 64 × BitVec 64) : BitVec 64 × BitVec 64 :=
  let d := pairs E 2 3 d
  let d := (Spec.Camellia.fl d.1 (E 8),Spec.Camellia.flinv d.2 (E 9))
  let d := pairs E 10 3 d
  let d := (Spec.Camellia.fl d.1 (E 16),Spec.Camellia.flinv d.2 (E 17))
  pairs E 18 3 d

def lastRounds (E : Nat → BitVec 64) (d : BitVec 64 × BitVec 64) : BitVec 64 × BitVec 64 :=
  pairs E 26 3 (Spec.Camellia.fl d.1 (E 24),Spec.Camellia.flinv d.2 (E 25))

theorem partialRounds_eq (E : Nat → BitVec 64) (d : BitVec 64 × BitVec 64) :
    partialRounds E d = VG.Proof.Camellia.groups 3 E d := by
  simp only [partialRounds,pairs,VG.Proof.Camellia.groups,VG.Proof.Camellia.group,
    List.range_succ,List.range_zero,List.foldl_append,List.foldl_cons,List.foldl_nil,
    List.nil_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceLT,ite_true,ite_false]

theorem lastRounds_eq (E : Nat → BitVec 64) (d : BitVec 64 × BitVec 64) :
    lastRounds E (partialRounds E d) = VG.Proof.Camellia.groups 4 E d := by
  simp only [lastRounds,partialRounds,pairs,VG.Proof.Camellia.groups,VG.Proof.Camellia.group,
    List.range_succ,List.range_zero,List.foldl_append,List.foldl_cons,List.foldl_nil,
    List.nil_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceLT,ite_true,ite_false]

end VG.Proof.Camellia.AArch64.Serial
