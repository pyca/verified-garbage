module

public import VerifiedGarbage.Impl.Camellia.AArch64.Serial.Core
public import VerifiedGarbage.Proof.Camellia.AArch64.Serial.Pure
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Interleave

/-! # The scalar FL and inverse-FL half-word transformations -/

@[expose] public section
namespace VG.Proof.Camellia.AArch64.Serial
open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Impl.Camellia.AArch64.Serial

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
  · rw [flInput,runBlock_cons,exec_ldr_x ⟨by omega,by omega⟩ hread,runStep_some]
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
