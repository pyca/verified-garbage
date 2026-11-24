module

public import VerifiedGarbage.Proof.AesGcm.RISCV64.GatherBs
public import VerifiedGarbage.Proof.Framework.RISCV64.StackScratchArgs
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.AesGcm.RISCV64.DirectGather
public import VerifiedGarbage.Proof.AesGcm.RISCV64.OneEntry
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Seal
public import VerifiedGarbage.Proof.AesGcm.RISCV64.OneBs
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamCrypt
import VerifiedGarbage.Proof.AesGcm.RISCV64.Flush

/-! # Direct gather private frame and its argument slots

The scratch frame copies four stack arguments. Only those four words and
the workspace pointer have been written when nonce processing starts.
-/

public section
namespace VG.Proof.AesGcm.RISCV64.DirectGather

open VG VG.RISCV64 VG.Impl.StackScratch.RISCV64 VG.Proof.AesGcm.RISCV64.GatherBs


abbrev allocated (s : State) := allocd 2608 s
abbrev prepared (s : State) := setArgsState 2608 4 (allocated s)
abbrev frameSp (s : State) := (allocated s).sp
abbrev work (s : State) := frameSp s + 40

theorem frameSp_eq {s : State} (h : GatherBs.Lay s) : frameSp s = Bs s + 2064 := by
  change s.sp - BitVec.ofNat 64 2608 = _
  rw [h.hB, Offset.add_ofNat_sub _ (by decide : 2608 ≤ 4672)]
  rfl

theorem arg_addr (s : State) (i : Nat) : frameSp s + BitVec.ofNat 64 (2608 + 8 * i) = stackArgAddr s i := by
  change (s.sp - BitVec.ofNat 64 2608) + BitVec.ofNat 64 (2608 + 8*i) = _
  rw [← Offset.add_add, BitVec.sub_add_cancel]; rfl

structure Prepared (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = (allocated s).wr
  sp : t.sp = frameSp s
  regs : ∀ q, q ≠ .t0 → q ≠ .t1 → t.gpr q = s.gpr q
  frame : Frame [⟨frameSp s, 40⟩] s.mem t.mem
  args : ∀ i < 4, t.mem.readW (frameSp s + BitVec.ofNat 64 (8 * i)) 64 = stackArg s i
  workArg : t.mem.readW (frameSp s + 32) 64 = work s

theorem prepared_run {s : State} (h : GatherBs.Lay s) :
    execBlock isa (setArgs 2608 4) (allocated s) =
        some (prepared s, setArgsTrace 2608 (frameSp s) 4) ∧ Prepared s (prepared s) := by
  have ha : (frameSp s).toNat % 8 = 0 := by rw [frameSp_eq h]; exact h.al8 (by decide) (by decide)
  have hr (j : Nat) (hj : j < 4) : InRegions ((allocated s).rd ++ (allocated s).wr)
      (frameSp s + BitVec.ofNat 64 (2608 + 8*j)) 8 := by
    rw [arg_addr]
    refine ⟨_, List.mem_append_left _ h.argIn, ?_⟩
    change (⟨s.sp + BitVec.ofNat 64 0, 32⟩ : Region).Contains (s.sp + BitVec.ofNat 64 (8*j)) 8
    exact Offset.contains _ (Nat.zero_le _) (by omega_using [hj]) (by decide)
  have hw (j : Nat) (hj : j ≤ 4) : InRegions (allocated s).wr (frameSp s + BitVec.ofNat 64 (8*j)) 8 :=
    ⟨_, List.mem_cons_self .., Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])⟩
  obtain ⟨run, rd, wr, sp, regs, frame, args, buf⟩ :=
    setArgs_run (bytes := 2608) (m := 4) (u := allocated s) ha (by decide) (by decide) (by decide) (by decide) hr hw
  constructor
  · exact run
  constructor
  · exact rd
  · exact wr
  · exact sp
  · intro q h0 h1
    unfold prepared
    apply Eq.trans (regs q h0 h1)
    rfl
  · exact frame
  swap
  · exact buf
  intro i hi
  exact (args i hi).trans (congrArg (fun p => s.mem.readW p 64) (arg_addr s i))

end VG.Proof.AesGcm.RISCV64.DirectGather

end

public section
namespace VG.Proof.AesGcm.RISCV64.DirectGather

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.AesGcm.RISCV64
open VG.Impl.AesGcm.RISCV64.DirectGather (setup)

/-- The three private scratch writes before nonce and AAD processing. -/
@[expose] def setupMem (m : Mem) (W count dst : Addr) : Mem :=
  ((m.writeW (W + 256) count).writeW (W + 240) dst).writeW (W + 248) (0#64)

/-- Read the gather-only arguments before the GCM subroutines use volatile
registers. The caller's stack arguments are disjoint from this workspace. -/
theorem setup_wp {s : State} {W sp dst len : Addr}
    (h0 : s.gpr .s0 = W) (ht : s.gpr .t1 = sp)
    (wa : W.toNat % 8 = 0) (sa : sp.toNat % 8 = 0)
    (work : Covers [⟨W, 2560⟩] s.wr)
    (args : Covers [⟨sp, 32⟩] (s.rd ++ s.wr))
    (apart : (⟨sp, 32⟩ : Region).Disjoint ⟨W, 2560⟩)
    (dest : s.mem.readW sp 64 = dst) (length : s.mem.readW (sp + 8) 64 = len) :
    WP isa (.block setup) s fun z =>
      z.gpr .s8 = s.gpr .a6 ∧ z.gpr .s11 = len ∧
      (∀ r, r ∉ [Reg.s8, .s11, .t0] → z.gpr r = s.gpr r) ∧
      z.mem = setupMem s.mem W (s.gpr .a7) dst ∧ z.rd = s.rd ∧ z.wr = s.wr ∧ z.sp = s.sp := by
  have disj (i j : Nat) (hi : i + 8 ≤ 32) (hj : j + 8 ≤ 2560) :
      Mem.Sep (sp + BitVec.ofNat 64 i) 8 (W + BitVec.ofNat 64 j) 8 :=
    (apart.sub_left (Offset.sub_base sp hi)).sub_right (Offset.sub_base W hj) |>.sep (Region.contains_self _ _) (Region.contains_self _ _)
  unfold setup
  refine wp_mv fun a ua => ?_
  refine wp_sd (off := rO) (a := W + 256) (by decide) (by rw [ua.other _ (by decide), h0]; rfl)
    (Spill.al8 (d := 256) wa (by decide)) (by rw [ua.wr]; exact in_off work (by decide) (by decide)) fun b ub => ?_
  refine wp_ld (off := 0) (a := sp) (by decide) (by rw [ub.gpr, ua.other _ (by decide), ht, BitVec.add_zero])
    sa (by rw [ub.rd, ub.wr, ua.rd, ua.wr]; simpa using (in_off (d := 0) (n := 8) args (by decide) (by decide))) fun c uc => ?_
  have destC : c.gpr .t0 = dst := by
    rw [uc.gpr, ub.mem, ua.mem, Mem.readW_writeW_sep (a := sp) (by simpa using disj 0 256 (by decide) (by decide)) (by decide), dest]
  refine wp_sd (off := dataO) (a := W + 240) (by decide)
    (by rw [uc.other _ (by decide), ub.gpr, ua.other _ (by decide), h0]; rfl)
    (Spill.al8 (d := 240) wa (by decide)) (by rw [uc.wr, ub.wr, ua.wr]; exact in_off work (by decide) (by decide))
    fun d ud => ?_
  refine wp_ld (off := 8) (a := sp + 8) (by decide)
    (by rw [ud.gpr, uc.other _ (by decide), ub.gpr, ua.other _ (by decide), ht]; rfl)
    (Spill.al8 (d := 8) sa (by decide))
    (by rw [ud.rd, ud.wr, uc.rd, uc.wr, ub.rd, ub.wr, ua.rd, ua.wr]; exact in_off args (by decide) (by decide))
    fun e ue => ?_
  have lenE : e.gpr .s11 = len := by
    rw [ue.gpr, ud.mem, Mem.readW_writeW_sep (disj 8 240 (by decide) (by decide)) (by decide), uc.mem, ub.mem,
      Mem.readW_writeW_sep (disj 8 256 (by decide) (by decide)) (by decide), ua.mem, length]
  refine wp_li (imm := 0) (by decide) fun f uf => ?_
  refine wp_sd (off := dstO) (a := W + 248) (by decide)
    (by rw [uf.other _ (by decide), ue.other _ (by decide), ud.gpr, uc.other _ (by decide), ub.gpr,
      ua.other _ (by decide), h0]; rfl)
    (Spill.al8 (d := 248) wa (by decide))
    (by rw [uf.wr, ue.wr, ud.wr, uc.wr, ub.wr, ua.wr]; exact in_off work (by decide) (by decide))
    fun z uz => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [uz.gpr, uf.other _ (by decide), ue.other _ (by decide), ud.gpr, uc.other _ (by decide), ub.gpr, ua.gpr]
  · rw [uz.gpr, uf.other _ (by decide), lenE]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [uz.gpr, uf.other _ hr.2.2, ue.other _ hr.2.1, ud.gpr, uc.other _ hr.2.2, ub.gpr, ua.other _ hr.1]
  · rw [uz.mem, uf.gpr, uf.mem, ue.mem, ud.mem, destC, uc.mem, ub.mem, ua.other _ (by decide), ua.mem]; rfl
  · rw [uz.rd, uf.rd, ue.rd, ud.rd, uc.rd, ub.rd, ua.rd]
  · rw [uz.wr, uf.wr, ue.wr, ud.wr, uc.wr, ub.wr, ua.wr]
  · rw [uz.sp, uf.sp, ue.sp, ud.sp, uc.sp, ub.sp, ua.sp]

end VG.Proof.AesGcm.RISCV64.DirectGather

end

public section
namespace VG.Proof.AesGcm.RISCV64.DirectGather

open VG VG.RISCV64 VG.Spec.Gcm
open VG.Impl.AesGcm.RISCV64
open VG.Impl.AesGcm.RISCV64.DirectGather (entry)
open VG.Proof.AesGcm.RISCV64.GatherBs (Src Dst Cnt Tg Bk Bs)

theorem work_eq {s : State} (h : GatherBs.Lay s) : work s = Bs s + BitVec.ofNat 64 2104 := by
  unfold work
  rw [frameSp_eq h]
  exact Offset.add_add (Bs s) 2064 40

theorem workCover {s t : State} (ht : Prepared s t) : Covers [⟨work s, 2560⟩] t.wr := by
  rw [ht.wr]
  apply Covers.of_sub
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨_, List.mem_cons_self .., 40, rfl, by change 40+2560 ≤ 2608; decide⟩

theorem areaCover {s t : State} (ht : Prepared s t) : Covers [⟨frameSp s, 40⟩] (t.rd ++ t.wr) := by
  apply covers_left
  rw [ht.wr]
  apply Covers.of_sub
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨_, List.mem_cons_self .., 0, (BitVec.add_zero _).symm, by change 0+40 ≤ 2608; decide⟩

theorem setupMem_frame (m : Mem) (W cnt dst : Addr) :
    Frame [⟨W + 240,24⟩] m (setupMem m W cnt dst) := by
  exact (((Frame.refl [⟨W + 240,24⟩] m).writeW (List.mem_singleton_self _) cnt
    (Offset.contains W (d := 256) (n := 8) (e := 240) (k := 24) (by decide) (by decide) (by decide))).writeW (List.mem_singleton_self _) dst
    (Offset.contains W (d := 240) (n := 8) (e := 240) (k := 24) (by decide) (by decide) (by decide))).writeW (List.mem_singleton_self _) (0#64)
    (Offset.contains W (d := 248) (n := 8) (e := 240) (k := 24) (by decide) (by decide) (by decide))

/-- The original four stack arguments and the saved caller registers still
hold after adapting the one-shot entry to gather seal. -/
structure Started (s z : State) : Prop where
  rd : z.rd = s.rd
  wr : z.wr = (allocated s).wr
  sp : z.sp = frameSp s
  saved : SavedAt z.mem (work s) s
  frame : Frame [⟨frameSp s,40⟩, ⟨work s + 128,136⟩] s.mem z.mem
  s0 : z.gpr .s0 = work s
  s1 : z.gpr .s1 = work s + 16
  s2 : z.gpr .s2 = s.gpr .a0
  s3 : z.gpr .s3 = s.gpr .a1
  s4 : z.gpr .s4 = s.gpr .a2
  s5 : z.gpr .s5 = s.gpr .a3
  s7 : z.gpr .s7 = s.gpr .a3
  s8 : z.gpr .s8 = Src s
  s10 : z.gpr .s10 = s.gpr .a5
  s11 : z.gpr .s11 = stackArg s 1
  s9 : z.gpr .s9 = Tg s
  aad : z.mem.readW (work s + 232) 64 = s.gpr .a4
  dst : z.mem.readW (work s + 240) 64 = Dst s
  offset : z.mem.readW (work s + 248) 64 = 0
  count : z.mem.readW (work s + 256) 64 = s.gpr .a7
  args : ∀ i < 4, z.mem.readW (frameSp s + BitVec.ofNat 64 (8*i)) 64 = stackArg s i

theorem start_wp {s t : State} (h : GatherBs.Lay s) (ht : Prepared s t) :
    WP isa (.block entry) t (Started s) := by
  let w := work s
  let p := frameSp s
  have wa : w.toNat % 8 = 0 := by unfold w; rw [work_eq h]; exact h.al8 (by decide) (by decide)
  have sa : p.toNat % 16 = 0 := by
    unfold p; rw [frameSp_eq h]; change (Bs s + BitVec.ofNat 64 2064).toNat % 16 = 0; rw [h.off_toNat (by decide),h.bs_toNat]
    have := h.al; have := h.w₁; omega_arith
  have WC := workCover ht
  have AC := areaCover ht
  have dis : (⟨p,40⟩ : Region).Disjoint ⟨w,2560⟩ := by
    change (⟨frameSp s, 40⟩ : Region).Disjoint ⟨frameSp s + BitVec.ofNat 64 40,2560⟩
    simpa only [BitVec.add_zero] using (Offset.disjoint (frameSp s) (d := 0) (n := 40) (e := 40) (k := 2560)
      (.inl (by decide)) (by decide) (by decide))
  have slots (i : Nat) (hi : i ≤ 4) : InRegions (t.rd ++ t.wr) (p + BitVec.ofNat 64 (8*i)) 8 :=
    in_off AC (by omega_using [hi]) (by decide)
  unfold entry
  rw [WP.block_append_iff]
  refine WP.mono (one1At_args_wp (off := 32) (tagO := 16) (W := w) (T := Tg s) (by decide)
    (.inr rfl) WC wa (ht.sp ▸ sa) (ht.sp ▸ slots 4 (by decide)) (ht.sp ▸ ht.workArg)
    (ht.sp ▸ slots 2 (by decide)) (ht.sp ▸ ht.args 2 (by decide)) ?_) fun u ⟨hu, a6, a7⟩ => ?_
  · rw [ht.sp]
    exact (dis.sub_left (Offset.sub_base p (by decide : 16+8 ≤ 40))).sub_right
      (Offset.sub_base w (by decide : 128+120 ≤ 2560))
  have U (i : Nat) (hi : i < 4) :
      u.mem.readW (p + BitVec.ofNat 64 (8*i)) 64 = stackArg s i := by
    refine (hu.frame.readW (Region.contains_self _ _) ?_ (by decide)).trans (ht.args i hi)
    intro r hr; obtain rfl := List.mem_singleton.mp hr
    exact (dis.sub_left (Offset.sub_base p (by omega_using [hi] : 8*i+8 ≤ 40))).sub_right
      (Offset.sub_base w (by decide : 128+120 ≤ 2560))
  refine WP.mono (setup_wp (sp := p) (dst := Dst s) (len := stackArg s 1) hu.s0 (hu.t1.trans ht.sp) wa (by omega_using [sa])
    (hu.keeps.wr ▸ WC) ?_ (dis.sub_left (Region.sub_prefix (by decide))) (by simpa using U 0 (by decide))
    (U 1 (by decide))) fun z ⟨s8,s11,regs,mem,rd,wr,sp⟩ => ?_
  · rw [hu.keeps.rd, hu.keeps.wr]; exact covers_prefix AC (by decide)
  have count : u.gpr .a7 = s.gpr .a7 := a7.trans (ht.regs _ (by decide) (by decide))
  have F := setupMem_frame u.mem w (u.gpr .a7) (Dst s)
  rw [← mem] at F
  refine ⟨rd.trans (hu.keeps.rd.trans ht.rd), wr.trans (hu.keeps.wr.trans ht.wr),
    sp.trans (hu.keeps.sp.trans ht.sp), ?_, ?_, (regs _ (by decide)).trans hu.s0,
    (regs _ (by decide)).trans hu.s1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, s11, (regs _ (by decide)).trans hu.s9,
    ?_, ?_, ?_, ?_, ?_⟩
  · apply (hu.saved.congr (fun x hx => (ht.regs x.1 (by revert hx; revert x; decide)
      (by revert hx; revert x; decide)).symm)).frame F
    intro r hr; obtain rfl := List.mem_singleton.mp hr
    exact Offset.disjoint w (.inl (by decide)) (by decide) (by decide)
  · refine (ht.frame.mono (fun r hr => ?_)).trans ((hu.frame.sub fun r hr => ?_).trans (F.sub fun r hr => ?_))
    · obtain rfl := List.mem_singleton.mp hr; exact List.mem_cons_self ..
    · obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Region.sub_prefix (by decide)⟩
    · obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Offset.sub w (by decide) (by decide)⟩
  · exact (regs _ (by decide)).trans (hu.s2.trans (ht.regs _ (by decide) (by decide)))
  · exact (regs _ (by decide)).trans (hu.s3.trans (ht.regs _ (by decide) (by decide)))
  · exact (regs _ (by decide)).trans (hu.s4.trans (ht.regs _ (by decide) (by decide)))
  · exact (regs _ (by decide)).trans (hu.s5.trans (ht.regs _ (by decide) (by decide)))
  · exact (regs _ (by decide)).trans (hu.s7.trans (ht.regs _ (by decide) (by decide)))
  · exact s8.trans (a6.trans (ht.regs _ (by decide) (by decide)))
  · exact (regs _ (by decide)).trans (hu.s10.trans (ht.regs _ (by decide) (by decide)))
  · refine (F.readW (Region.contains_self _ _) ?_ (by decide)).trans (hu.aad.trans (ht.regs _ (by decide) (by decide)))
    intro r hr; obtain rfl := List.mem_singleton.mp hr
    exact Offset.disjoint w (d := 232) (e := 240) (.inl (by decide)) (by decide) (by decide)
  · rw [mem]; unfold setupMem
    rw [Mem.readW_writeW_sep, Mem.readW_writeW_self64]
    · exact Offset.sep w (d := 240) (n := 8) (e := 248) (k := 8) (by decide) (by decide) (by decide)
    · decide
  · rw [mem]; exact Mem.readW_writeW_self64 ..
  · rw [mem]; unfold setupMem
    rw [Mem.readW_writeW_sep, Mem.readW_writeW_sep, Mem.readW_writeW_self64, count]
    · exact Offset.sep w (d := 256) (n := 8) (e := 240) (k := 8) (by decide) (by decide) (by decide)
    · decide
    · exact Offset.sep w (d := 256) (n := 8) (e := 248) (k := 8) (by decide) (by decide) (by decide)
    · decide
  · intro i hi
    refine (slot_keep F (fun r hr => ?_)).trans (U i hi)
    obtain rfl := List.mem_singleton.mp hr
    exact (dis.sub_left (Offset.sub_base p (by omega_using [hi] : 8*i+8 ≤ 40))).sub_right
      (Offset.sub_base w (by decide : 240+24 ≤ 2560))

end VG.Proof.AesGcm.RISCV64.DirectGather

end

public section
namespace VG.Proof.AesGcm.RISCV64.DirectGather

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64
open GatherBs (C Dst Bk Tg cR nR aR bkR dsR lsR dR tgR stkR Bs)

abbrev inputs (s : State) := [cR s, nR s, aR s, bkR s, dsR s] ++ lsR s

structure Caller (s : State) : Prop where
  layout : GatherBs.Lay s
  fit : ∀ r ∈ inputs s ++ [dR s,tgR s], r.base.toNat + r.len ≤ 2^64
  apart : ∀ r ∈ inputs s ++ [dR s,tgR s], (stkR s).Disjoint r
  inputsApart : ∀ r ∈ inputs s, r.Disjoint (dR s) ∧ r.Disjoint (tgR s)
  outputsApart : (dR s).Disjoint (tgR s)
  ctxAlign : (C s).toNat % 8 = 0
  bkAlign : (Bk s).toNat % 8 = 0
  keys : Spec.Gcm.CtxSlicedRepr s.mem (Bk s) (C s)

theorem caller {s : State} (pre : GatherBs.gatherPre s) : Caller s := by
  have h := GatherBs.lay pre
  obtain ⟨_, _, cd, ct, nd, nt, ad, at_, dsd, dst, bkd, bkt, listed, dt, _, _, _, _, _, _, _, _, _, _, _,
    oc, on, oa, ods, ol, od, ot, ob, _, _, _, _, _, ca, ba, bk⟩ := pre
  refine ⟨h, ?_, ?_, ?_, dt, ca, ba, bk⟩
  all_goals intro r hr; simp only [inputs,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr
  · rcases hr with ((rfl|rfl|rfl|rfl|rfl)|hl)|(rfl|rfl)
    exacts [oc,on,oa,ob,ods,ol _ hl,od,ot]
  · rcases hr with ((rfl|rfl|rfl|rfl|rfl)|hl)|(rfl|rfl)
    exacts [h.bc,h.bn,h.ba,h.bbk,h.bds,h.bl _ hl,h.bd,h.bt]
  · rcases hr with (rfl|rfl|rfl|rfl|rfl)|hl
    exacts [⟨cd,ct⟩,⟨nd,nt⟩,⟨ad,at_⟩,⟨bkd,bkt⟩,⟨dsd,dst⟩,listed _ hl]

abbrev statePtr (s : State) := work s + BitVec.ofNat 64 16

theorem scratch_sub {s : State} (h : Caller s) : (⟨work s, 2560⟩ : Region).Sub (stkR s) := by
  rw [work_eq h.layout]; exact Offset.sub_base _ (by decide)

theorem below_eq {s : State} (h : Caller s) :
    below (frameSp s) 2048 = ⟨Bs s + BitVec.ofNat 64 16, 2048⟩ := by
  unfold below
  rw [frameSp_eq h.layout]
  change Region.mk ((Bs s + BitVec.ofNat 64 2064) - BitVec.ofNat 64 2048) 2048 = _
  rw [Offset.add_ofNat_sub _ (by decide)]

theorem below_sub {s : State} (h : Caller s) : (below (frameSp s) 2048).Sub (stkR s) := by
  rw [below_eq h]; exact Offset.sub_base _ (by decide)

theorem layoutOf {s : State} (h : Caller s) : Lay (C s) (statePtr s) (work s) := by
  apply oneLay
  · exact h.fit (cR s) (by simp [inputs])
  · rw [work_eq h.layout, h.layout.off_toNat (by decide)]
    have := h.layout.hBn; omega_arith
  · exact h.layout.bc.symm.sub_right (scratch_sub h)
  · exact h.ctxAlign
  · rw [work_eq h.layout]; exact h.layout.al8 (by decide) (by decide)

theorem stackOf {s : State} (h : Caller s) : StkOk (C s) (statePtr s) (work s) (frameSp s) := by
  have wd : (⟨work s,2560⟩ : Region).Disjoint (below (frameSp s) 2048) := by
    rw [work_eq h.layout,below_eq h]
    exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)
  refine ⟨h.layout.bc.symm.sub_right (below_sub h), wd.sub_left (Offset.sub_base _ (by decide)), wd, ?_, ?_⟩
  all_goals rw [frameSp_eq h.layout]; have e : (Bs s + 2064).toNat = (Bs s).toNat + 2064 := h.layout.off_toNat (k := 2064) (by decide); rw [e]
  · have ha := h.layout.al; have hb := h.layout.w₁; rw [h.layout.bs_toNat]; omega_arith
  · omega_arith

theorem coversWork {s t : State} (hw : t.wr = (allocated s).wr) :
    Covers [⟨work s,2560⟩] t.wr := by
  rw [hw]; apply Covers.of_sub; intro r hr; obtain rfl := List.mem_singleton.mp hr
  exact ⟨_, List.mem_cons_self .., 40, rfl, by change 40 + 2560 ≤ 2608; decide⟩

theorem inputCover {s t : State} (h : Caller s) (hrd : t.rd = s.rd) (r : Region) (hr : r ∈ inputs s) :
    Covers [r] (t.rd ++ t.wr) := by
  apply covers_mem
  exact List.mem_append_left _ (hrd ▸ (h.layout.pre.1 ▸ List.mem_append_left _ hr))

theorem dataOf {s t : State} (h : Caller s) (hsp : t.sp = frameSp s)
    {r : Region} (hr : r ∈ inputs s ++ [dR s, tgR s]) (small : r.len < 2^64)
    (read : Covers [r] (t.rd ++ t.wr)) : DataOk (statePtr s) (work s) t r.base r.len := by
  have dis := (h.apart _ hr).symm
  have w := dis.sub_right (scratch_sub h)
  exact ⟨read,small,h.fit _ hr,w.sub_right (Offset.sub_base _ (by decide)),w,hsp ▸ dis.sub_right (below_sub h)⟩

theorem Started.environment {s z : State} (h : Caller s) (hz : Started s z) :
    Env z.gpr (frameSp s) z := by
  have Wcov := coversWork hz.wr
  have statePerm : Covers [⟨statePtr s,80⟩] z.wr := covers_off Wcov (by decide) (by decide)
  refine ⟨fun _ _ => rfl, hz.sp, ?_, ?_⟩
  · rw [hz.s2,hz.s1,hz.s0]
    exact ⟨inputCover h hz.rd _ (by simp [inputs]),statePerm,Wcov⟩
  · rw [hz.s2,hz.s1,hz.s0,hz.sp]; exact stackOf h

end VG.Proof.AesGcm.RISCV64.DirectGather

end

public section
namespace VG.Proof.AesGcm.RISCV64.DirectGather

open VG VG.RISCV64 VG.Spec.Gcm VG.Impl.AesGcm.RISCV64
open VG.Spec.Aes (bytesAt)
open GatherBs (Bs C Nn NL Ad AL Bk Rn cR nR aR stkR)

abbrev nonce (s : State) := bytesAt s.mem (Nn s) (NL s)
abbrev aadBytes (s : State) := bytesAt s.mem (Ad s) (AL s)
abbrev H (s : State) := ctxH s.mem (C s)
abbrev J (s : State) := Spec.Gcm.j0 (H s) (nonce s)

theorem Started.stackFrame {s z : State} (h : Caller s) (hz : Started s z) : Frame [stkR s] s.mem z.mem := by
  apply hz.frame.sub
  intro r hr; rcases List.mem_cons.mp hr with rfl | hr
  · exact ⟨_,List.mem_singleton_self _,frameSp_eq h.layout ▸ Offset.sub_base _ (by decide : 2064+40≤4672)⟩
  · obtain rfl := List.mem_singleton.mp hr
    exact ⟨_,List.mem_singleton_self _,(fun a ha => scratch_sub h a (Offset.sub_base (work s) (by decide : 128+136≤2560) a ha))⟩

theorem j0_sub {s : State} (h : Caller s) (r : Region) (hr : r ∈ j0Frame (statePtr s) (work s) (frameSp s)) :
    r.Sub (stkR s) := by
  simp only [j0Frame, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl
  exacts [(fun a ha => scratch_sub h a (Offset.sub_base (work s) (by decide : 16+80≤2560) a ha)),
    (fun a ha => scratch_sub h a (Offset.sub_base (work s) (by decide : 96+16≤2560) a ha)),
    (fun a ha => scratch_sub h a (Offset.sub_base (work s) (by decide : 512+256≤2560) a ha)),below_sub h]

theorem args_safe_j0 {s : State} (h : Caller s) (i : Nat) (hi : i < 4) :
    ∀ r ∈ j0Frame (statePtr s) (work s) (frameSp s),
    (⟨frameSp s + BitVec.ofNat 64 (8*i),8⟩ : Region).Disjoint r := by
  have base : (⟨frameSp s,40⟩ : Region).Disjoint ⟨work s,2560⟩ := by
    change (⟨frameSp s,40⟩ : Region).Disjoint ⟨frameSp s + BitVec.ofNat 64 40, 2560⟩
    simpa only [BitVec.add_zero] using
      Offset.disjoint (frameSp s) (d := 0) (n := 40) (e := 40) (k := 2560) (.inl (by decide)) (by decide) (by decide)
  have slot := Offset.sub_base (frameSp s) (by omega_using [hi] : 8*i+8 ≤ 40)
  intro r hr; simp only [j0Frame,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl
  · exact (base.sub_left slot).sub_right (Offset.sub_base _ (by decide))
  · exact (base.sub_left slot).sub_right (Offset.sub_base _ (by decide))
  · exact (base.sub_left slot).sub_right (Offset.sub_base _ (by decide))
  · apply Region.Disjoint.sub_left _ slot
    rw [below_eq h,frameSp_eq h.layout]
    exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)

theorem externalBytes {s z : State} (h : Caller s) (f : Frame [stkR s] s.mem z.mem)
    (r : Region) (hr : r ∈ inputs s) :
    bytesAt z.mem r.base r.len = bytesAt s.mem r.base r.len := by
  have fit := h.fit _ (List.mem_append_left _ hr)
  exact bytesAt_frame f (fun x hx => (List.mem_singleton.mp hx) ▸ (h.apart _ (List.mem_append_left _ hr)).symm)
    (by omega_using [fit])

theorem aad_wp [VG.Proof.Gcm.RISCV64.GhashLaw] {s z : State} (h : Caller s) (hz : Started s z) :
    WP isa oneAad z (OA z.gpr (frameSp s) (H s) (nonce s) (aadBytes s) z.mem) := by
  have f := hz.stackFrame h
  have he := hz.environment h
  have L := (layoutOf h).v hz.s2 hz.s1 hz.s0
  have nn : nR s ∈ inputs s := by simp [inputs]
  have aa : aR s ∈ inputs s := by simp [inputs]
  have hn := dataOf h hz.sp (List.mem_append_left _ nn) (s.gpr .a3).isLt (inputCover h hz.rd _ nn)
  have ha := dataOf h hz.sp (List.mem_append_left _ aa) (s.gpr .a5).isLt (inputCover h hz.rd _ aa)
  have hh : blockAt z.mem (z.gpr .s2 + 240) = H s := by
    rw [hz.s2]; exact ctxH_keep f fun r hr => (List.mem_singleton.mp hr) ▸ h.layout.bc.symm
  have raw := oneAad_ok L he hh hz.s4 (by rw [hz.s5]; exact (show s.gpr .a3 = BitVec.ofNat 64 (NL s) by simp [GatherBs.NL]))
    (by rw [hz.s7]; simp [GatherBs.NL])
    (by rw [hz.s1,hz.s0]; exact hn)
    (by rw [hz.s1,hz.s0,hz.s10]; exact ha) (by rw [hz.s0]; exact hz.aad)
  have nv := externalBytes h f _ nn
  have av := externalBytes h f _ aa
  change bytesAt z.mem (Nn s) (NL s) = nonce s at nv
  change bytesAt z.mem (Ad s) (AL s) = aadBytes s at av
  simpa only [hz.s10,nv,av] using raw

end VG.Proof.AesGcm.RISCV64.DirectGather

end
