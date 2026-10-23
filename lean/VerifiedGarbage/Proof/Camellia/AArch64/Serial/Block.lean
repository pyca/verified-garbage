module

public import VerifiedGarbage.Proof.Camellia.AArch64.Serial.State
public import VerifiedGarbage.Proof.Camellia.AArch64.Serial.Rounds
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Interleave
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Camellia.Layout
import VerifiedGarbage.Proof.Camellia.KeySched
import VerifiedGarbage.Proof.Camellia.Common
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Loading and whitening the serial core's two 64-bit halves -/

@[expose] public section
namespace VG.Proof.Camellia.AArch64.Serial
open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Impl.Camellia.AArch64.Serial

theorem loadBE_run {s : State} {r : Reg} {off : Nat}
    (hoff : off % 8 = 0 ∧ off < 32768)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x5+BitVec.ofNat 64 off) 8) :
    ∃ t, runBlock isa (loadBE r off) s = some t ∧
      t.gpr r = rev64 (s.mem.readW (s.gpr .x5+BitVec.ofNat 64 off) 64) ∧
      (∀ q, q ≠ r → t.gpr q = s.gpr q) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v := by
  let a := s.write .x r (s.mem.readW (s.gpr .x5+BitVec.ofNat 64 off) 64)
  let t := a.write .x r (rev64 (a.read .x r))
  refine ⟨t,?_,?_,fun q hq => ?_,rfl,rfl,rfl,rfl,rfl⟩
  · rw [loadBE,runBlock_cons,exec_ldr_x hoff hr,runStep_some,runBlock_cons,
      exec_rev,runStep_some,runBlock_nil]
  · simp only [t,a,gpr_write_self,State.read,Size.bits,BitVec.setWidth_eq]
  · simp only [t,a,gpr_write_of_ne _ _ _ hq]

theorem xorKey_run {s : State} {r : Reg} {k : Nat}
    (hr : r ≠ .x10) (hk : k < 34)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .x5+BitVec.ofNat 64 (256+8*k)) 8) :
    ∃ t, runBlock isa (xorKey r k) s = some t ∧
      t.gpr r = s.gpr r ^^^ keyWord s k ∧
      (∀ q, q ≠ r → q ≠ .x10 → t.gpr q = s.gpr q) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v := by
  obtain ⟨a,ae,av,ag,am,ard,awr,asp,avec⟩ := loadBE_run (r := .x10) ⟨by omega,by omega⟩ hread
  let t := a.write .x r (a.read .x r ^^^ a.read .x .x10)
  refine ⟨t,?_,?_,?_,am,ard,awr,asp,avec⟩
  · rw [xorKey,VG.Interleave.runBlock_append,ae,Option.bind_some]
    rfl
  · simp only [t,gpr_write_self,State.read,Size.bits,BitVec.setWidth_eq,ag _ hr,av,keyWord]
  · intro q hqr hq10
    rw [gpr_write_of_ne _ _ _ hqr,ag _ hq10]

theorem loadBlock_run (s : State)
    (hr : ∀ off ∈ [256,264,768,776],
      InRegions (s.rd ++ s.wr) (s.gpr .x5+BitVec.ofNat 64 off) 8) :
    ∃ t, runBlock isa loadBlock s = some t ∧
      halves t = (rev64 (s.mem.readW (s.gpr .x5+BitVec.ofNat 64 768) 64) ^^^ keyWord s 0,
        rev64 (s.mem.readW (s.gpr .x5+BitVec.ofNat 64 776) 64) ^^^ keyWord s 1) ∧
      (∀ r, r ∉ [.x6,.x7,.x10] → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v := by
  obtain ⟨a,ae,av,ag,am,ard,awr,asp,avec⟩ :=
    loadBE_run (r := .x6) ⟨by decide,by decide⟩ (hr 768 (by decide))
  have ar : InRegions (a.rd ++ a.wr) (a.gpr .x5+BitVec.ofNat 64 776) 8 := by
    rw [ard,awr,ag _ (by decide)]
    exact hr 776 (by decide)
  obtain ⟨b,be,bv,bg,bm,brd,bwr,bsp,bvec⟩ := loadBE_run (r := .x7) ⟨by decide,by decide⟩ ar
  have br : InRegions (b.rd ++ b.wr) (b.gpr .x5+BitVec.ofNat 64 (256+8*0)) 8 := by
    rw [brd,bwr,ard,awr,bg _ (by decide),ag _ (by decide)]
    exact hr 256 (by decide)
  obtain ⟨c,ce,cv,cg,cm,crd,cwr,csp,cvec⟩ := xorKey_run (r := .x6) (by decide) (by decide) br
  have cr : InRegions (c.rd ++ c.wr) (c.gpr .x5+BitVec.ofNat 64 (256+8*1)) 8 := by
    rw [crd,cwr,brd,bwr,ard,awr,cg _ (by decide) (by decide),bg _ (by decide),ag _ (by decide)]
    exact hr 264 (by decide)
  obtain ⟨d,de,dv,dg,dm,drd,dwr,dsp,dvec⟩ := xorKey_run (r := .x7) (by decide) (by decide) cr
  refine ⟨d,?_,?_,?_,dm.trans (cm.trans (bm.trans am)),
    drd.trans (crd.trans (brd.trans ard)),dwr.trans (cwr.trans (bwr.trans awr)),
    dsp.trans (csp.trans (bsp.trans asp)),dvec.trans (cvec.trans (bvec.trans avec))⟩
  · rw [loadBlock,VG.Interleave.runBlock_append,VG.Interleave.runBlock_append,
      VG.Interleave.runBlock_append,ae,Option.bind_some,be,Option.bind_some,ce,Option.bind_some,de]
  · simp only [halves]
    rw [dg .x6 (by decide) (by decide),dv,cv,bg .x6 (by decide),av,
      cg .x7 (by decide) (by decide),bv]
    simp only [keyWord,cm,bm,am,cg .x5 (by decide) (by decide),bg .x5 (by decide),ag .x5 (by decide)]
  · intro r hn
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hn
    rw [dg _ hn.2.1 hn.2.2,cg _ hn.1 hn.2.2,bg _ hn.2.1,ag _ hn.1]

/-- The two big-endian words in the block buffer are exactly the decoded block. -/
theorem decoded_halves (m : Mem) (p : Addr) :
    (Spec.Camellia.decodeBlock (Spec.Camellia.blockAt m p) >>> 64).setWidth 64 =
      rev64 (m.readW p 64) ∧
    (Spec.Camellia.decodeBlock (Spec.Camellia.blockAt m p)).setWidth 64 =
      rev64 (m.readW (p+BitVec.ofNat 64 8) 64) := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · rw [readBE,VG.Proof.Camellia.getLsbD_wordAt _ _ hi]
    have h := congrArg (fun b : Byte => b.getLsbD (i%8))
      (VG.Proof.Camellia.byteOf_hi (Spec.Camellia.blockAt m p) (i := 7-i/8) (by omega))
    simp only [VG.Proof.Camellia.byteOf,BitVec.getLsbD_setWidth,BitVec.getLsbD_ushiftRight,
      show i%8 < 8 by omega,decide_true,Bool.true_and,
      show 56-8*(7-i/8)+i%8=i by omega,Spec.Camellia.blockAt,Vector.getElem_ofFn] at h
    simpa only [BitVec.getLsbD_setWidth,BitVec.getLsbD_ushiftRight,
      hi,decide_true,Bool.true_and,Spec.Camellia.blockAt] using h
  · rw [readBE,VG.Proof.Camellia.getLsbD_wordAt _ _ hi]
    have h := congrArg (fun b : Byte => b.getLsbD (i%8))
      (VG.Proof.Camellia.byteOf_lo (Spec.Camellia.blockAt m p) (i := 7-i/8) (by omega))
    simp only [VG.Proof.Camellia.byteOf,BitVec.getLsbD_setWidth,BitVec.getLsbD_ushiftRight,
      show i%8 < 8 by omega,decide_true,Bool.true_and,
      show 56-8*(7-i/8)+i%8=i by omega,Spec.Camellia.blockAt,Vector.getElem_ofFn] at h
    rw [VG.Offset.add_add]
    simpa only [show 8+(7-i/8)=8+7-i/8 by omega,
      BitVec.getLsbD_setWidth,hi,decide_true,Bool.true_and,Spec.Camellia.blockAt] using h

theorem storeBlock_run (s : State)
    (hw0 : InRegions s.wr (s.gpr .x5+BitVec.ofNat 64 768) 8)
    (hw1 : InRegions s.wr (s.gpr .x5+BitVec.ofNat 64 776) 8) :
    ∃ t, runBlock isa storeBlock s = some t ∧
      t.mem.readW (s.gpr .x5+BitVec.ofNat 64 768) 64 = rev64 (s.gpr .x7) ∧
      t.mem.readW (s.gpr .x5+BitVec.ofNat 64 776) 64 = rev64 (s.gpr .x6) ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → t.gpr r = s.gpr r) ∧
      Frame [⟨s.gpr .x5+BitVec.ofNat 64 768,16⟩] s.mem t.mem ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v := by
  let a := s.write .x .x7 (rev64 (s.read .x .x7))
  let b := a.write .x .x6 (rev64 (a.read .x .x6))
  let c := { b with mem := b.mem.writeW (b.gpr .x5+BitVec.ofNat 64 768) (b.gpr .x7) }
  let t := { c with mem := c.mem.writeW (c.gpr .x5+BitVec.ofNat 64 776) (c.gpr .x6) }
  have base : b.gpr .x5 = s.gpr .x5 := by
    simp only [b,a,gpr_write,↓reduceIte,reduceCtorEq]
  have mem : t.mem = (s.mem.writeW (s.gpr .x5+BitVec.ofNat 64 768) (rev64 (s.gpr .x7))).writeW
      (s.gpr .x5+BitVec.ofNat 64 776) (rev64 (s.gpr .x6)) := by
    simp only [t,c,b,a,State.read,Size.bits,gpr_write,BitVec.setWidth_eq,
      mem_write,↓reduceIte,reduceCtorEq]
  refine ⟨t,?_,?_,?_,?_,?_,rfl,rfl,rfl,rfl⟩
  · rw [storeBlock,runBlock_cons,exec_rev,runStep_some,runBlock_cons,exec_rev,runStep_some,
      runBlock_cons,exec_str_x ⟨by decide,by decide⟩ (by rw [base]; exact hw0),runStep_some,
      runBlock_cons,exec_str_x ⟨by decide,by decide⟩ (by change InRegions c.wr _ _; rw [show c.gpr .x5 = s.gpr .x5 from base]; exact hw1),
      runStep_some,runBlock_nil]
  · rw [mem,Mem.readW_writeW_sep (VG.Offset.disjoint (s.gpr .x5)
      (Or.inl (by decide : 768+8 ≤ 776)) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self64]
  · rw [mem,Mem.readW_writeW_self64]
  · intro r h6 h7
    simp only [t,c,b,a,gpr_write_of_ne _ _ _ h6,gpr_write_of_ne _ _ _ h7]
  · rw [mem]
    apply Frame.trans
      (VG.Proof.Camellia.frame_writeW _ (Region.sub_prefix (by decide : 8 ≤ 16)))
    apply VG.Proof.Camellia.frame_writeW
    rw [← VG.Offset.add_add (s.gpr .x5) 768 8]
    exact VG.Offset.sub_base _ (by decide : 8+8 ≤ 16)

/-- Two stored little-endian words represent the standard big-endian output block. -/
theorem stored_bytes {m : Mem} {p : Addr} {hi lo : BitVec 64}
    (h0 : m.readW p 64 = rev64 hi)
    (h1 : m.readW (p+BitVec.ofNat 64 8) 64 = rev64 lo) :
    Spec.Aes.bytesAt m p 16 = (Spec.Camellia.encodeBlock (hi ++ lo)).toList := by
  apply List.ext_getElem (by simp [Spec.Aes.bytesAt])
  intro i hi16 hi'
  have hn : i < 16 := by simpa [Spec.Aes.bytesAt] using hi16
  simp only [Spec.Aes.bytesAt,List.getElem_map,List.getElem_range,Vector.getElem_toList]
  rw [VG.Proof.Camellia.encodeBlock_getElem _ _ hn]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  by_cases h : i < 8
  · simp only [h,ite_true]
    have b : m (p+BitVec.ofNat 64 i) = (m.readW p 64).extractLsb' (8*i) 8 := by
      change m (p+BitVec.ofNat 64 i) = (m.read p 8).extractLsb' (8*i) 8
      exact (Mem.extractLsb'_read m p h).symm
    rw [h0] at b
    rw [b]
    simp only [BitVec.getLsbD_extractLsb',hj,decide_true,Bool.true_and]
    change (byteRev64 hi).getLsbD (8*i+j) = _
    rw [byteRev64_getLsbD _ (by omega),VG.Proof.Camellia.getLsbD_byteOf _ h hj]
    congr 1 <;> omega
  · simp only [h,ite_false]
    have b : m (p+BitVec.ofNat 64 8+BitVec.ofNat 64 (i-8)) =
        (m.readW (p+BitVec.ofNat 64 8) 64).extractLsb' (8*(i-8)) 8 := by
      change m _ = (m.read (p+BitVec.ofNat 64 8) 8).extractLsb' (8*(i-8)) 8
      exact (Mem.extractLsb'_read m _ (by omega : i-8 < 8)).symm
    rw [h1,VG.Offset.add_add,show 8+(i-8)=i by omega] at b
    rw [b]
    simp only [BitVec.getLsbD_extractLsb',hj,decide_true,Bool.true_and]
    change (byteRev64 lo).getLsbD (8*(i-8)+j) = _
    rw [byteRev64_getLsbD _ (by omega),VG.Proof.Camellia.getLsbD_byteOf _ (by omega) hj]
    congr 1 <;> omega

theorem whitening_run (s : State) (k : Nat) (hk : k+1 < 34)
    (hr : ∀ j < 34, InRegions (s.rd ++ s.wr) (s.gpr .x5+BitVec.ofNat 64 (256+8*j)) 8)
    (hw0 : InRegions s.wr (s.gpr .x5+BitVec.ofNat 64 768) 8)
    (hw1 : InRegions s.wr (s.gpr .x5+BitVec.ofNat 64 776) 8) :
    ∃ t, runBlock isa (whitening k) s = some t ∧
      Spec.Aes.bytesAt t.mem (s.gpr .x5+BitVec.ofNat 64 768) 16 =
        (Spec.Camellia.encodeBlock ((s.gpr .x7 ^^^ keyWord s k) ++
          (s.gpr .x6 ^^^ keyWord s (k+1)))).toList ∧
      (∀ r, r ∉ written → t.gpr r = s.gpr r) ∧
      Frame [⟨s.gpr .x5+BitVec.ofNat 64 768,16⟩] s.mem t.mem ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  obtain ⟨a,ae,av,ag,am,ard,awr,asp,_⟩ := xorKey_run (r := .x7) (by decide) (by omega) (hr k (by omega))
  have ar : InRegions (a.rd ++ a.wr) (a.gpr .x5+BitVec.ofNat 64 (256+8*(k+1))) 8 := by
    rw [ard,awr,ag _ (by decide) (by decide)]
    exact hr (k+1) hk
  obtain ⟨b,be,bv,bg,bm,brd,bwr,bsp,_⟩ := xorKey_run (r := .x6) (by decide) hk ar
  have bbase : b.gpr .x5 = s.gpr .x5 := (bg _ (by decide) (by decide)).trans (ag _ (by decide) (by decide))
  obtain ⟨t,te,t0,t1,tg,tf,trd,twr,tsp,_⟩ := storeBlock_run b
    (by rw [bwr,awr,bbase]; exact hw0) (by rw [bwr,awr,bbase]; exact hw1)
  have out := stored_bytes (p := b.gpr .x5+BitVec.ofNat 64 768) t0
    (by rw [VG.Offset.add_add]; exact t1)
  refine ⟨t,?_,?_,?_,?_,trd.trans (brd.trans ard),twr.trans (bwr.trans awr),tsp.trans (bsp.trans asp)⟩
  · rw [whitening,VG.Interleave.runBlock_append,VG.Interleave.runBlock_append,
      ae,Option.bind_some,be,Option.bind_some,te]
  · rw [bbase,bg .x7 (by decide) (by decide),av,bv,ag .x6 (by decide) (by decide)] at out
    simpa only [keyWord,am,ag .x5 (by decide) (by decide)] using out
  · intro r hn
    simp only [written,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn
    rw [tg _ hn.1 hn.2.1,bg _ hn.1 hn.2.2.2.1,ag _ hn.2.1 hn.2.2.2.1]
  · simpa only [bbase,bm,am] using tf

end VG.Proof.Camellia.AArch64.Serial
