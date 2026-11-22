module

public import VerifiedGarbage.Impl.AesGcm.AArch64.DirectGather.Medium

public import VerifiedGarbage.Impl.AesGcm.AArch64.DirectGather
public import VerifiedGarbage.Proof.AesGcm.AArch64.Save
public import VerifiedGarbage.Proof.AesGcm.AArch64.Env
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.ShortSeal
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Groups
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! Initialize the compact gather frame while preserving the caller's arguments. -/

public section

namespace VG.Proof.AesGcm.AArch64.DirectGather.Mid

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64.DirectGather

theorem setup_ok (s : State) {n : Nat} (hn : n ≤ 224)
    (hw : Covers [⟨s.sp, Medium.work⟩] s.wr)
    (hr : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (Medium.work + 8)) 8)
    (hlen : s.mem.readW (s.sp + BitVec.ofNat 64 (Medium.work + 8)) 64 = BitVec.ofNat 64 n) :
    WP isa (.block Medium.setup) s fun t =>
      t.gpr .x19 = s.sp ∧ t.gpr .x21 = s.gpr .x0 ∧ t.gpr .x22 = s.gpr .x1 ∧
      t.gpr .x23 = s.gpr .x2 ∧ t.gpr .x24 = s.gpr .x5 ∧ t.gpr .x26 = BitVec.ofNat 64 n ∧
      t.gpr .x25 = BitVec.ofNat 64 (16 * ((n + 15) / 16)) ∧
      (∀ r, r ∉ [.x9, .x19, .x21, .x22, .x23, .x24, .x25, .x26] → t.gpr r = s.gpr r) ∧
      SavedAt t.mem s.sp s ∧ Frame [savedR s.sp] s.mem t.mem ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  unfold Medium.setup
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.of_runBlock ⟨_, by arun [], ?_⟩
  let u := s.write .x .x9 s.sp
  have hx : u.gpr .x9 = s.sp := by simp [u, gpr_write]
  obtain ⟨v,run,hg,hsp,hrd,hwr,hm⟩ := save_ok u .x9 hx (Wn := Medium.work) hw (by decide)
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨v, ?_, ?_⟩
  · simpa [u, State.write] using run
  have hframe : Frame [savedR s.sp] s.mem v.mem := hm ▸ savedMem_frame _ _ _
  have hread : v.mem.readW (s.sp + BitVec.ofNat 64 (Medium.work+8)) 64 = BitVec.ofNat 64 n := by
    rw [← hlen]
    apply hframe.readW (r := ⟨_, 8⟩) (Region.contains_self _ _)
    · intro q hq
      simp only [List.mem_singleton] at hq
      subst q
      exact Offset.disjoint s.sp (.inr (by decide)) (by decide) (by decide)
    · decide
  have hs : v.sp = s.sp := hsp
  have hrs : InRegions (v.rd ++ v.wr) (v.sp + BitVec.ofNat 64 (Medium.work+8)) 8 := by
    simpa only [hs, hrd, hwr, u, rd_write, wr_write] using hr
  refine WP.of_runBlock ⟨_, by arun [hrs], ?_⟩
  change v.mem.read _ 8 = _ at hread
  simp only [State.read, BitVec.add_zero, gpr_write, reduceCtorEq, ite_false, ite_true, sp_write, rd_write, wr_write,
    mem_write, BitVec.setWidth_eq, Size.bits, hs, hread, hg, hx]
  refine ⟨trivial, rfl, rfl, rfl, rfl, trivial, Stitch.ceil16_bv (by omega), ?_, ?_, hframe, trivial, hrd, hwr⟩
  · intro r h
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    simp [u, gpr_write, h]
  · rw [hm]
    intro p hp
    rw [savedAt_save _ _ u p hp]
    have hne : p.1 ≠ .x9 := (by decide : ∀ p ∈ VG.Impl.AesGcm.AArch64.saved, p.1 ≠ .x9) p hp
    simp [u, gpr_write, hne]


theorem zero_ok {W : Addr} (s : State) (hb : s.gpr .x19 = W)
    (hw : Covers [⟨W, Medium.work⟩] s.wr) :
    WP isa (.block Medium.zero) s fun t =>
      t.mem = WriteBytes.writeBytes s.mem (W + BitVec.ofNat 64 Medium.keyO) (List.replicate 528 0) ∧
      t.gpr = s.gpr ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  unfold Medium.zero
  rw [WP.block_cons_iff]
  refine ⟨_, Proof.Gcm.AArch64.Pmull.exec_movi0 .v0 s, ?_⟩
  refine WP.mono (Stitch.zstores_range (off := Medium.keyO) 33 _ (by rfl) hb hw
    (by decide) (by decide) (by decide)) fun _ ⟨hm,hg,_,hs,hr,hw⟩ => ⟨hm,hg,hs,hr,hw⟩

theorem aad_ok {W : Addr} {c al : Nat} (hc : c ≤ 14) (s : State)
    (hb : s.gpr .x19 = W) (h25 : s.gpr .x25 = BitVec.ofNat 64 (16*c))
    (h24 : s.gpr .x24 = BitVec.ofNat 64 al)
    (h : LoopPre s (s.gpr .x4) (W + BitVec.ofNat 64 (Medium.authO+224-16*c)) al) :
    WP isa Medium.aad s fun t =>
      t.mem = WriteBytes.writeBytes s.mem (W + BitVec.ofNat 64 (Medium.authO+224-16*c))
        (Spec.Aes.bytesAt s.mem (s.gpr .x4) al) ∧
      (∀ r, r ∉ loopRegs → t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  unfold Medium.aad
  refine WP.seq ?_
  rw [WP.block_append_iff]
  obtain ⟨u,run,hd,g,hm,_,hs,hr,hw⟩ := Stitch.atP_ok (c := c) .x11 (Medium.authO+128) 0 (by decide)
    (by unfold Medium.authO; omega) s hb h25 (by decide)
  refine WP.of_runBlock ⟨u,run,?_⟩
  refine WP.of_runBlock ⟨_,by arun [],?_⟩
  refine WP.mono (copy_ok _ (S := s.gpr .x4) (D := W + BitVec.ofNat 64 (Medium.authO+224-16*c)) (n := al)
    (by simp [gpr_write, g .x4 (by decide)]) (by simpa [gpr_write] using hd)
    (by simp [gpr_write, g .x24 (by decide), h24])
    ⟨h.lt, by simpa only [rd_write, wr_write, hr, hw] using h.rd,
      by simpa only [wr_write, hw] using h.wr, h.disj⟩) fun _ ⟨m',g',s',r',w'⟩ => ?_
  refine ⟨by simpa only [mem_write, hm] using m', fun r hh => ?_,
    s'.trans hs,r'.trans hr,w'.trans hw⟩
  rw [g' r hh]
  simp only [loopRegs,List.mem_cons,List.not_mem_nil,or_false,not_or] at hh
  simp [gpr_write,hh.2.1,hh.2.2.1,g r hh.1]

theorem cursors_ok {W : Addr} {c : Nat} (hc : c ≤ 14) (s : State)
    (hb : s.gpr .x19 = W) (h25 : s.gpr .x25 = BitVec.ofNat 64 (16*c))
    (hr : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 Medium.work) 8) :
    WP isa (.block Medium.cursors) s fun t =>
      t.gpr .x1 = W + 240 ∧ t.gpr .x2 = s.mem.readW (s.sp + BitVec.ofNat 64 Medium.work) 64 ∧
      t.gpr .x3 = W + BitVec.ofNat 64 (Medium.authO+240-16*c) ∧
      t.gpr .x6 = s.gpr .x27 ∧ t.gpr .x7 = s.gpr .x28 ∧
      (∀ r, r ∉ [.x1,.x2,.x3,.x6,.x7] → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  unfold Medium.cursors
  rw [WP.block_append_iff]
  let t := ((((s.write .x .x6 (s.gpr .x27)).write .x .x7 (s.gpr .x28)).write .x .x1 (s.gpr .x19 + 240))).write .x .x2 (s.mem.read (s.sp + BitVec.ofNat 64 Medium.work) 8)
  refine WP.of_runBlock ⟨t,by arun [hr,Medium.keyO,t] <;> simp only [Medium.work, Nat.reduceMod, Nat.reduceLT, and_self, ↓reduceIte,runStep_some,runBlock_nil,BitVec.add_zero,show (240:Addr)=240#64 by decide],?_⟩
  obtain ⟨u,run,out,g,m,_,sp,rd,wr⟩ := Stitch.atP_ok (c := c) .x3 (Medium.authO+128) 1 (by decide)
    (by unfold Medium.authO; omega) t (by simpa [t,gpr_write] using hb) (by simpa [t,gpr_write] using h25) (by decide)
  refine WP.of_runBlock ⟨u,run,?_,?_,out,?_,?_,fun r h => ?_,m,sp,rd,wr⟩
  · simp [g .x1 (by decide),t,gpr_write,hb]
  · simp [g .x2 (by decide),t,gpr_write,Mem.readW]
  · simp [g .x6 (by decide),t,gpr_write]
  · simp [g .x7 (by decide),t,gpr_write]
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at h
    simp [g r h.2.2.1,t,gpr_write,h.1,h.2.1,h.2.2.2.1,h.2.2.2.2]

end VG.Proof.AesGcm.AArch64.DirectGather.Mid
