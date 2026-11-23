module

public import VerifiedGarbage.Proof.AesGcm.RISCV64.DirectGather.Aad
import VerifiedGarbage.Proof.AesGcm.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.AesGcm.RISCV64.DirectGather.Loop
import VerifiedGarbage.Proof.Gather.RISCV64.Loop
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Gcm.Ctr

public section
namespace VG.Proof.AesGcm.RISCV64.DirectGather

open VG VG.RISCV64 VG.Spec.Gcm VG.Proof.Gcm VG.Impl.AesGcm.RISCV64
open GatherBs (C Src Dst Bk Tg stkR)

structure Ready (s e : State) : Prop where
  rd : e.rd = s.rd
  wr : e.wr = (allocated s).wr
  sp : e.sp = frameSp s
  saved : SavedAt e.mem (work s) s
  frame : Frame [stkR s] s.mem e.mem
  s0 : e.gpr .s0 = work s
  s1 : e.gpr .s1 = statePtr s
  s2 : e.gpr .s2 = C s
  s3 : e.gpr .s3 = s.gpr .a1
  s7 : e.gpr .s7 = Bk s
  s8 : e.gpr .s8 = Src s
  s10 : e.gpr .s10 = s.gpr .a5
  s11 : e.gpr .s11 = stackArg s 1
  dest : e.mem.readW (work s + 240) 64 = Dst s
  offset : e.mem.readW (work s + 248) 64 = 0
  count : e.mem.readW (work s + 256) 64 = s.gpr .a7
  aad : e.mem.readW (work s + 232) 64 = s.gpr .a4
  tagPtr : e.mem.readW (frameSp s + 16) 64 = Tg s
  hashKey : blockAt e.mem (C s + 240) = H s
  j : blockAt e.mem (statePtr s) = J s
  counter : blockAt e.mem (statePtr s + 48) = inc32 (J s)
  abs : Absorbed e.mem (statePtr s + 16) (statePtr s + 32) (H s)
    (aadBytes s ++ zeros (padLen (aadBytes s).length))

/-- All gather cursor slots lie between the temporary hash block and the
callee workspace. -/
theorem slot_safe_j0 {s : State} (h : Caller s) {d : Nat} (lo : 232 ≤ d) (hi : d+8 ≤ 264) :
    ∀ r ∈ j0Frame (statePtr s) (work s) (frameSp s),
      (⟨work s + BitVec.ofNat 64 d,8⟩ : Region).Disjoint r := by
  intro r hr; simp only [j0Frame,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl
  · exact Offset.disjoint (work s) (.inr (by omega_using [lo])) (by omega_using [hi]) (by decide)
  · exact Offset.disjoint (work s) (.inr (by omega_using [lo])) (by omega_using [hi]) (by decide)
  · exact Offset.disjoint (work s) (.inl (by omega_using [hi])) (by omega_using [hi]) (by decide)
  · exact (stackOf h).w.sub_left (Offset.sub_base _ (by omega_using [hi]))

theorem ready_wp {s z u : State} (h : Caller s) (hz : Started s z)
    (oa : OA z.gpr (frameSp s) (H s) (nonce s) (aadBytes s) z.mem u)
    (rd : u.rd = z.rd) (wr : u.wr = z.wr) :
    WP isa (.block (bkLoad 24)) u (Ready s) := by
  have jf := oa.frame
  rw [hz.s1,hz.s0] at jf
  have arg (i : Nat) (hi : i < 4) :
      u.mem.readW (frameSp s + BitVec.ofNat 64 (8*i)) 64 = stackArg s i :=
    (slot_keep jf (args_safe_j0 h i hi)).trans (hz.args i hi)
  have usp := oa.env.sp
  have sa := (stackOf h).al
  have load : InRegions (u.rd ++ u.wr) (u.sp + BitVec.ofNat 64 24) 8 := by
    rw [usp,wr,hz.wr]
    apply in_left
    exact ⟨_,List.mem_cons_self ..,Offset.contains_base _ (by decide : 24+8 ≤ 2608) (by decide)⟩
  refine WP.mono (bkLoad_ok (off := 24) (by decide) (by rw [usp]; exact sa) (by decide) load)
    fun e ⟨key,g,k⟩ => ?_
  have eqr (r : Reg) (hr : r ∈ frozen) (h7 : r ≠ .s7) : e.gpr r = z.gpr r :=
    (g r (fun a => absurd (a ▸ hr) (by decide)) h7).trans (oa.env.fr r hr)
  have slot (d : Nat) (lo : 232 ≤ d) (hi : d+8 ≤ 264) :
      e.mem.readW (work s + BitVec.ofNat 64 d) 64 = z.mem.readW (work s + BitVec.ofNat 64 d) 64 := by
    rw [k.mem]; exact slot_keep jf (slot_safe_j0 h lo hi)
  refine ⟨k.rd.trans (rd.trans hz.rd),k.wr.trans (wr.trans hz.wr),k.sp.trans usp,?_,?_,
    (eqr _ (by decide) (by decide)).trans hz.s0,(eqr _ (by decide) (by decide)).trans hz.s1,
    (eqr _ (by decide) (by decide)).trans hz.s2,(eqr _ (by decide) (by decide)).trans hz.s3,?_,
    (eqr _ (by decide) (by decide)).trans hz.s8,(eqr _ (by decide) (by decide)).trans hz.s10,
    (eqr _ (by decide) (by decide)).trans hz.s11,(slot 240 (by decide) (by decide)).trans hz.dst,
    (slot 248 (by decide) (by decide)).trans hz.offset,(slot 256 (by decide) (by decide)).trans hz.count,
    (slot 232 (by decide) (by decide)).trans hz.aad,?_,?_,?_,?_,?_⟩
  · rw [k.mem]; exact hz.saved.frame jf (saved_j0Frame (layoutOf h) (stackOf h))
  · rw [k.mem]; exact (hz.stackFrame h).trans (jf.sub fun r hr => ⟨_,List.mem_singleton_self _,j0_sub h r hr⟩)
  · rw [key,usp]; exact arg 3 (by decide)
  · rw [k.mem]; exact arg 2 (by decide)
  · rw [k.mem]; have q := oa.hH; rw [hz.s2] at q; exact q
  · rw [k.mem]; have q := oa.j; rw [hz.s1] at q; exact q
  · rw [k.mem]; have q := oa.cb; rw [hz.s1] at q; exact q
  · rw [k.mem]; have q := oa.abs; rw [hz.s1] at q; exact q

end VG.Proof.AesGcm.RISCV64.DirectGather

end

public section
namespace VG.Proof.AesGcm.RISCV64.DirectGather

open VG VG.RISCV64 VG.Spec.Gcm VG.Proof.Gcm
open VG.Proof.Gather.RISCV64 (sb sl slice_mem)
open VG.Spec.Aes (bytesAt)
open GatherBs (Bs C Rn Src Dst Bk Cnt L dsR lsR dR bkR stkR cR)

abbrev loopArgs (s e : State) : LoopArgs :=
  ⟨s.mem,Src s,Dst s,Cnt s,Rn s,inc32 (J s),e.gpr,frameSp s⟩

theorem dataWrite {s e : State} (h : Caller s) (he : Ready s e) :
    DataW (C s) (statePtr s) (work s) e (Dst s) (L s) := by
  have wr : Covers [dR s] e.wr := by rw [he.wr]; apply covers_mem; exact List.mem_cons_of_mem _ (h.layout.pre.2.1 ▸ List.mem_cons_self ..)
  exact ⟨dataOf h he.sp (by simp) (stackArg s 1).isLt (covers_left wr),wr,
    (h.inputsApart (cR s) (by simp [inputs])).1⟩

theorem keyInput {s e : State} (h : Caller s) (he : Ready s e) :
    BkIn (Bk s) (C s) (statePtr s) (work s) (frameSp s) (Rn s) e.mem (Dst s) (Dst s) (L s) e := by
  have br := inputCover h he.rd (bkR s) (by simp [inputs])
  have dis := h.layout.bbk.symm.sub_left (Region.sub_prefix (by decide : 960 ≤ 1248))
  have wd := dis.sub_right (scratch_sub h)
  have rr := h.layout.hR
  refine ⟨covers_prefix br (by decide),h.bkAlign,wd.sub_right (Offset.sub_base _ (by decide)),wd,
    dis.sub_right (below_sub h),((h.inputsApart (bkR s) (by simp [inputs])).1).sub_left (Region.sub_prefix (by decide)),?_⟩
  exact keysAt_ctx_frame rr he.frame (fun r hr => (List.mem_singleton.mp hr) ▸ dis)
    (fun r hr => (List.mem_singleton.mp hr) ▸ h.layout.bc.symm) (keysAt_of_sliced (by omega_using [rr]) h.keys)

theorem loopFrame {s e : State} (h : Caller s) (he : Ready s e) {r : Region}
    (hr : r ∈ (loopArgs s e).frame) : r = dR s ∨ r.Sub (stkR s) := by
  change r ∈ [⟨Dst s,GatherBs.gl s (Cnt s)⟩,⟨e.gpr .s1 + 48,32⟩,⟨e.gpr .s0 + 512,2048⟩,
    ⟨e.gpr .s0 + 248,8⟩,⟨e.gpr .s0 + 256,8⟩] at hr
  rw [he.s1,he.s0,h.layout.hgl] at hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl
  · exact .inl rfl
  · exact .inr (fun a ha => scratch_sub h a (Offset.sub_base _ (by decide : 16+80 ≤ 2560) a
      (Offset.sub_base (statePtr s) (by decide : 48+32 ≤ 80) a ha)))
  all_goals exact .inr (fun a ha => scratch_sub h a (Offset.sub_base (work s) (by decide) a ha))

theorem inputLoopApart {s e : State} (h : Caller s) (he : Ready s e) {r : Region} (hr : r ∈ inputs s) :
    ∀ t ∈ (loopArgs s e).frame, r.Disjoint t := by
  intro t ht
  rcases loopFrame h he ht with rfl|sub
  · exact (h.inputsApart r hr).1
  · exact ((h.apart _ (List.mem_append_left _ hr)).symm).sub_right sub

theorem loopInput {s e : State} (h : Caller s) (he : Ready s e) : LoopInput (loopArgs s e) e := by
  have R : Rn s = 10 ∨ Rn s = 12 ∨ Rn s = 14 := h.layout.hR
  have de : dsR s ∈ inputs s := by simp [inputs]
  have piece {i : Nat} (hi : i < Cnt s) :
      (⟨sb s.mem (Src s) i,sl s.mem (Src s) i⟩ : Region) ∈ inputs s :=
    List.mem_append_right _ (slice_mem _ _ hi)
  have ds : (dsR s).Disjoint (stkR s) := h.layout.bds.symm
  refine ⟨(layoutOf h).v he.s2 he.s1 he.s0,R,?_,(s.gpr .a7).isLt,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change e.gpr .s3 = _; rw [he.s3]; simp [Rn]
  · simpa only [Nat.mul_comm] using h.layout.ods
  · simpa only [dsR,Nat.mul_comm] using inputCover h he.rd _ de
  · simpa only [dsR,Nat.mul_comm] using inputLoopApart h he de
  · intro i hi
    have keep (d : Nat) (hd : d+8 ≤ 16) :
        e.mem.readW (Src s + BitVec.ofNat 64 (16*i) + BitVec.ofNat 64 d) 64 =
        s.mem.readW (Src s + BitVec.ofNat 64 (16*i) + BitVec.ofNat 64 d) 64 := by
      apply slot_keep he.frame
      intro r hr; obtain rfl := List.mem_singleton.mp hr
      rw [Offset.add_add]
      exact ds.sub_left (Offset.sub_base _ (by change 16*i+d+8 ≤ Cnt s*16; change i < Cnt s at hi; omega))
    constructor
    · simpa [LoopArgs.cursor,LoopArgs.S,sb] using keep 0 (by decide)
    · have k := keep 8 (by decide)
      simpa [LoopArgs.cursor,LoopArgs.n,sl] using k
  · intro i hi
    have mem := piece hi
    have result := dataOf h he.sp (List.mem_append_left _ mem) (by apply BitVec.isLt) (inputCover h he.rd _ mem)
    change DataOk (e.gpr .s1) (e.gpr .s0) _ _ _
    rw [he.s1,he.s0]; exact result
  · intro i hi; exact inputLoopApart h he (piece hi)
  · intro i hi; exact externalBytes h he.frame _ (piece hi)
  · change DataW (e.gpr .s2) (e.gpr .s1) (e.gpr .s0) e (Dst s) (GatherBs.gl s (Cnt s))
    rw [he.s2,he.s1,he.s0,h.layout.hgl]; exact dataWrite h he
  · change BkIn (e.gpr .s7) (e.gpr .s2) (e.gpr .s1) (e.gpr .s0) _ _ _ _ _ (GatherBs.gl s (Cnt s)) _
    rw [he.s7,he.s2,he.s1,he.s0,h.layout.hgl]; exact keyInput h he

theorem loopAt0 {s e : State} (h : Caller s) (he : Ready s e) : LoopAt (loopArgs s e) e 0 e := by
  let a := loopArgs s e
  have V : a.regs 0 (e.gpr .s9) = e.gpr := by
    funext r; by_cases hr : r = .s8
    · subst r; simp [LoopArgs.regs,LoopArgs.cursor,a,he.s8]
    · by_cases h9 : r = .s9
      · subst r; rfl
      · simp [LoopArgs.regs,hr,h9,a]
  have en : Env e.gpr (frameSp s) e := by
    refine ⟨fun _ _ => rfl, he.sp, ?_, ?_⟩
    · rw [he.s0,he.s1,he.s2]; have wc := coversWork he.wr
      exact ⟨inputCover h he.rd (cR s) (by simp [inputs]),covers_off wc (by decide : 16+80 ≤ 2560) (by decide),wc⟩
    · rw [he.s0,he.s1,he.s2,he.sp]; exact stackOf h
  refine ⟨⟨_,V ▸ en⟩,rfl,rfl,rfl,?_,?_,?_,?_,?_,Frame.refl _ _⟩
  · change e.mem.readW (e.gpr .s0 + 240) 64 = _; rw [he.s0]; exact he.dest
  · change e.mem.readW (e.gpr .s0 + 248) 64 = 0; rw [he.s0]; exact he.offset
  · change e.mem.readW (e.gpr .s0 + 256) 64 = BitVec.ofNat 64 (Cnt s - 0); rw [he.s0,he.count]; simp [Cnt]
  · apply ctr_zero; change blockAt e.mem (e.gpr .s1 + 48) = _; rw [he.s1]; exact he.counter
  · rfl

end VG.Proof.AesGcm.RISCV64.DirectGather

end
