module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillABI
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Context
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Entry
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.FrameStore
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.EntryState
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Memory
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextSlice
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextFrame
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeometryWork
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.AArch64.StackStore
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd -- shake: keep (brun's simp set reads its lemmas)
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

-- separate module: the entry's symbolic execution, which a change to the loop's proofs does not re-elaborate

/-! # The refillable-tape search's entry on AArch64

The entry stores the arguments in the attempts' frame and the controller's
words (`entry_ok`), and each width's header the subgroup's width
(`widthHeader_ok`). -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64.Generation.Refill

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 (Lay Rep Geo upd nW cF)
open VG.Impl.RsaOaep.AArch64 (frameBytes oRsa)
open VG.Proof.Dsa.AArch64.Generation

/-- The memory after the entry's header. -/
def headerMem (m : Mem) (F : Addr) (g : Reg → BitVec 64) (a0 a1 : BitVec 64) : Mem :=
  (((((((((((((m.writeW (off F 48) (g .x0)).writeW (off F 56) (g .x1)).writeW (off F 64) (g .x3)).writeW
    (off F 72) (g .x4)).writeW (off F 88) (g .x3)).writeW (off F 112) (g .x3)).writeW (off F 120) (g .x4)).writeW
    (off F 40) (g .x5)).writeW (off F 136) a1).writeW (off F 80) (0 : BitVec 64)).writeW (off F 104) (0 : BitVec 64)).writeW
    (off F 448) (g .x2)).writeW (off F 456) (g .x7)).writeW (off F 464) a0

theorem movz_zero : (BitVec.ofNat 16 0).setWidth 64 = (0 : BitVec 64) := by decide

theorem header_run {s : State} {F : Addr} (hsp : s.sp = F) (hw : (⟨F, 480⟩ : Region) ∈ s.wr)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr .x7) 8)
    (h8 : InRegions (s.rd ++ s.wr) (s.gpr .x7 + BitVec.ofNat 64 8) 8) :
    WP isa (.block Impl.Dsa.AArch64.Generation.entryHeader) s fun t =>
      t.mem = headerMem s.mem F s.gpr (s.mem.readW (s.gpr .x7) 64)
        (s.mem.readW (s.gpr .x7 + BitVec.ofNat 64 8) 64) ∧ Keep [.x3, .x8, .x9] s t := by
  have st : ∀ d, d + 8 ≤ 480 → InRegions s.wr (s.sp + BitVec.ofNat 64 d) 8 := fun d hd =>
    ⟨_, hw, by rw [hsp]; exact Offset.contains_base F hd (by omega)⟩
  refine WP.keep [.x3, .x8, .x9] ?_ (by decide)
  simp only [Impl.Dsa.AArch64.Generation.entryHeader, Impl.Dsa.AArch64.Generation.Refill.ctl, Nat.reduceMul,
    Nat.reduceAdd]
  brun [State.write, exec_ldr_x (off := 0) (by decide), exec_ldr_x (off := 8) (by decide),
    exec_storeSp (off := 48) (by decide), exec_storeSp (off := 56) (by decide),
    exec_storeSp (off := 64) (by decide), exec_storeSp (off := 72) (by decide),
    exec_storeSp (off := 88) (by decide), exec_storeSp (off := 112) (by decide),
    exec_storeSp (off := 120) (by decide), exec_storeSp (off := 40) (by decide),
    exec_storeSp (off := 136) (by decide), exec_storeSp (off := 80) (by decide),
    exec_storeSp (off := 104) (by decide), exec_storeSp (off := 448) (by decide),
    exec_storeSp (off := 456) (by decide), exec_storeSp (off := 464) (by decide), h0, h8,
    st 48 (by decide), st 56 (by decide), st 64 (by decide), st 72 (by decide), st 88 (by decide),
    st 112 (by decide), st 120 (by decide), st 40 (by decide), st 136 (by decide), st 80 (by decide),
    st 104 (by decide), st 448 (by decide), st 456 (by decide), st 464 (by decide), movz_zero]
  rw [hsp]
  rfl

/-! ## The controller's words -/

theorem ctl_contains (F : Addr) {k : Nat} (hk : k < 4) :
    (ctlRegion F).Contains (off F (448 + 8 * k)) 8 :=
  Offset.contains F (e := 448) (by omega) (by omega) (by omega)

theorem ctl_frame (F : Addr) : (ctlRegion F).Disjoint ⟨F, frameBytes⟩ :=
  (Offset.base_disjoint F (e := 448) (n := 32) (k := frameBytes) (by decide) (by omega)).symm

theorem ctl_below (F : Addr) {n : Nat} (hn : n ≤ 288) : (ctlRegion F).Disjoint (below F n) :=
  Offset.disjoint_below F (n := n) (d := 448) (k := 32) (by omega)

theorem ctl_write (m : Mem) (F : Addr) {k : Nat} (hk : k < 4) (v : BitVec 64) :
    Frame [ctlRegion F] m (m.writeW (off F (448 + 8 * k)) v) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) v (ctl_contains F hk)

theorem ctlWord_frame {rs : List Region} {m m' : Mem} {F : Addr} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (ctlRegion F).Disjoint r) {k : Nat} (hk : k < 4) :
    ctlWord m' F k = ctlWord m F k :=
  hf.readW (ctl_contains F hk) hd (by decide)

theorem ctlWord_write_self (m : Mem) (F : Addr) (k : Nat) (v : BitVec 64) :
    ctlWord (m.writeW (off F (448 + 8 * k)) v) F k = v := Mem.readW_writeW_self64 ..

theorem ctlWord_write_other (m : Mem) (F : Addr) {j k : Nat} (hj : j < 4)
    (hk : k < 4) (hne : j ≠ k) (v : BitVec 64) :
    ctlWord (m.writeW (off F (448 + 8 * k)) v) F j = ctlWord m F j := by
  unfold ctlWord
  rw [Mem.readW_writeW_sep (Offset.sep F (d := 448 + 8 * j) (n := 8) (e := 448 + 8 * k) (k := 8) (by omega)
    (by omega) (by omega)) (by decide)]

theorem rep_ctl {m : Mem} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep m F S V W)
    (hS : (ctlRegion F).Disjoint ⟨S, oRsa⟩) {k : Nat} (hk : k < 4) (v : BitVec 64) :
    Rep (m.writeW (off F (448 + 8 * k)) v) F S V W :=
  rep_of_disjoint_frame R (ctl_write m F hk v)
    (fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact (ctl_frame F).symm)
    (fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact hS.symm)

/-! ## The entry -/

/-- The state the entry starts from: the frame allocated and the
callee-saved registers saved (`linkState`). -/
structure RefillAllocated {pBytes : Nat} {s₀ : State} (h : RefillABI pBytes s₀) (u : State) : Prop where
  sp : u.sp = refillBase s₀
  wr : u.wr = ⟨refillBase s₀, 480⟩ :: s₀.wr
  rd : u.rd = s₀.rd
  regs : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x7], u.gpr r = s₀.gpr r
  mem : Frame [⟨off (refillBase s₀) 296, 152⟩] s₀.mem u.mem

theorem refillBase_bound {pBytes : Nat} {s : State} (h : RefillABI pBytes s) :
    (refillBase s).toNat + 480 ≤ 2 ^ 64 := by
  rw [refillBase_toNat h]; have := s.sp.isLt; have : 768 ≤ s.sp.toNat := h.stackLower; omega

/-- The regions the entry and the search write in the frame, and the saved
registers', are disjoint from each buffer. -/
theorem RefillABI.frame_disjoint {pBytes : Nat} {s : State} (h : RefillABI pBytes s) {r : Region}
    (hr : r = inOut s ∨ r = inUsed s ∨ r = inRand s ∨ r = inScr s ∨ r = inState s) {d n : Nat}
    (hd : d + n ≤ 480) : r.Disjoint ⟨off (refillBase s) d, n⟩ := by
  rw [refillBase_low, off_off]
  exact (h.stack_disjoint (by unfold refillStack; omega) hr).symm

theorem RefillABI.geo {pBytes : Nat} {s : State} (h : RefillABI pBytes s) :
    Geo (refillBase s) (refillGeometry h).hash := by
  have hh := (refillGeometry h).small_bound (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa)
    (by decide) (by decide)
  exact ⟨by
      show 16 ≤ (refillBase s).toNat
      rw [refillBase_toNat h]; have : 768 ≤ s.sp.toNat := h.stackLower; omega,
    (refillGeometry h).frameBound,
    (refillGeometry h).part_bound hh, (refillGeometry h).frame_part hh,
    ((refillGeometry h).stack_part hh).sub_left (below_sub (a := 16) (by decide) (by decide)),
    ((refillGeometry h).frame_below.sub_right (below_sub (a := 16) (by decide) (by decide))).symm⟩

theorem RefillABI.ctl_arena {pBytes : Nat} {s : State} (h : RefillABI pBytes s) :
    (ctlRegion (refillBase s)).Disjoint ⟨s.gpr .x5, VG.Impl.Dsa.Generation.Layout.usedBytes pBytes⟩ := by
  rw [ctlRegion_eq]
  exact h.stack_arena (by decide)

theorem RefillABI.ctl_hash {pBytes : Nat} {s : State} (h : RefillABI pBytes s) :
    (ctlRegion (refillBase s)).Disjoint ⟨(refillGeometry h).hash, oRsa⟩ :=
  h.ctl_arena.sub_right ((refillGeometry h).part_sub
    ((refillGeometry h).small_bound (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide)))

/-- The tape's memory across writes to the frame and the saved registers. -/
theorem RefillAllocated.randMemory {pBytes : Nat} {s₀ u v : State} {h : RefillABI pBytes s₀}
    (a : RefillAllocated h u) (hf : Frame [⟨refillBase s₀, 480⟩] u.mem v.mem)
    (hr : v.rd = u.rd) : GenerationTapeMemory (randTape h) v where
  cover := by
    intro x n hx
    simp only [randTape, bytesAt_length, InRegions, List.mem_singleton] at hx
    obtain ⟨r, rfl, hx⟩ := hx
    refine ⟨_, List.mem_append_left _ ?_, hx⟩
    rw [hr, a.rd, h.rd]; exact List.mem_cons_self ..
  bytes := by
    change Spec.Rsa.bytesAt v.mem (s₀.gpr .x3) (Spec.Rsa.bytesAt s₀.mem (s₀.gpr .x3) (s₀.gpr .x4).toNat).length = _
    rw [bytesAt_length]
    have hall : Frame [⟨off (refillBase s₀) 296, 152⟩, ⟨refillBase s₀, 480⟩] s₀.mem v.mem :=
      (a.mem.mono (fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact List.mem_cons_self ..)).trans
      (hf.mono fun r hr => by rcases List.mem_singleton.mp hr with rfl; simp)
    refine VG.Proof.Dsa.Generation.frame_bytesAt hall (fun r hr => ?_) (Nat.le_of_lt (s₀.gpr .x4).isLt)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.frame_disjoint (r := inRand s₀) (by simp) (by decide)
    · have := h.frame_disjoint (r := inRand s₀) (d := 0) (n := 480) (by simp) (by decide)
      simp only [off, BitVec.add_zero] at this
      exact this

/-- The frame words after the header. -/
def headerWords (W : Nat → BitVec 64) (g : Reg → BitVec 64) (a1 : BitVec 64) : Nat → BitVec 64 :=
  upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd W 6 (g .x0)) 7 (g .x1)) 8 (g .x3)) 9 (g .x4))
    11 (g .x3)) 14 (g .x3)) 15 (g .x4)) 5 (g .x5)) 17 a1) 10 0) 13 0

theorem headerMem_rep {m : Mem} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64} (G : Geo F S)
    (R : Rep m F S V W) (hS : (ctlRegion F).Disjoint ⟨S, oRsa⟩) (g : Reg → BitVec 64) (a0 a1 : BitVec 64) :
    Rep (headerMem m F g a0 a1) F S V (headerWords W g a1) := by
  have R1 := ((((((((((R.wf G (k := 6) (by decide) (g .x0)).wf G (k := 7) (by decide) (g .x1)).wf
    G (k := 8) (by decide) (g .x3)).wf G (k := 9) (by decide) (g .x4)).wf G (k := 11) (by decide) (g .x3)).wf
    G (k := 14) (by decide) (g .x3)).wf G (k := 15) (by decide) (g .x4)).wf G (k := 5) (by decide) (g .x5)).wf
    G (k := 17) (by decide) a1).wf G (k := 10) (by decide) 0).wf G (k := 13) (by decide) 0
  exact rep_ctl (rep_ctl (rep_ctl R1 hS (k := 0) (by decide) _) hS (k := 1) (by decide) _) hS (k := 2) (by decide) _

theorem headerMem_frame (m : Mem) (F : Addr) (g : Reg → BitVec 64) (a0 a1 : BitVec 64) :
    Frame [⟨F, frameBytes⟩, ctlRegion F] m (headerMem m F g a0 a1) := by
  have fc : ∀ d, d + 8 ≤ frameBytes → (⟨F, frameBytes⟩ : Region).Contains (off F d) 8 := fun d hd =>
    Offset.contains_base F hd (by unfold frameBytes at hd; omega)
  have c : ∀ k < 4, (ctlRegion F).Contains (off F (448 + 8 * k)) 8 := fun _ hk => ctl_contains F hk
  unfold headerMem
  refine Frame.writeW (Frame.writeW (Frame.writeW (Frame.writeW (Frame.writeW (Frame.writeW (Frame.writeW
    (Frame.writeW (Frame.writeW (Frame.writeW (Frame.writeW (Frame.writeW (Frame.writeW (Frame.writeW (Frame.refl _ _)
    (List.mem_cons_self ..) _ (fc 48 (by decide))) (List.mem_cons_self ..) _ (fc 56 (by decide)))
    (List.mem_cons_self ..) _ (fc 64 (by decide))) (List.mem_cons_self ..) _ (fc 72 (by decide)))
    (List.mem_cons_self ..) _ (fc 88 (by decide))) (List.mem_cons_self ..) _ (fc 112 (by decide)))
    (List.mem_cons_self ..) _ (fc 120 (by decide))) (List.mem_cons_self ..) _ (fc 40 (by decide)))
    (List.mem_cons_self ..) _ (fc 136 (by decide))) (List.mem_cons_self ..) _ (fc 80 (by decide)))
    (List.mem_cons_self ..) _ (fc 104 (by decide))) (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (c 0 (by decide)))
    (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (c 1 (by decide)))
    (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (c 2 (by decide))

theorem headerMem_ctl (m : Mem) (F : Addr) (g : Reg → BitVec 64) (a0 a1 : BitVec 64) :
    ctlWord (headerMem m F g a0 a1) F 0 = g .x2 ∧ ctlWord (headerMem m F g a0 a1) F 1 = g .x7 ∧
      ctlWord (headerMem m F g a0 a1) F 2 = a0 := by
  unfold headerMem
  refine ⟨?_, ?_, ctlWord_write_self _ F 2 _⟩
  · rw [ctlWord_write_other _ F (j := 0) (k := 2) (by decide) (by decide) (by decide),
      ctlWord_write_other _ F (j := 0) (k := 1) (by decide) (by decide) (by decide)]
    exact ctlWord_write_self _ F 0 _
  · rw [ctlWord_write_other _ F (j := 1) (k := 2) (by decide) (by decide) (by decide)]
    exact ctlWord_write_self _ F 1 _

/-- The entry's end: the frame words but the subgroup's width, which each
width's header sets. -/
structure EntryDone {pBytes : Nat} {s₀ : State} (h : RefillABI pBytes s₀) (W : Nat → BitVec 64) (v : State) :
    Prop where
  layout : Lay v (refillBase s₀) (refillGeometry h).hash
  rep : ∃ V, Rep v.mem (refillBase s₀) (refillGeometry h).hash V W
  slots : ∀ k ∈ generationSlots, k ≠ 18 → k ≠ 26 → W k = refillWords pBytes s₀ k
  w16 : W 16 = 0
  w10 : W 10 = 0
  scratch : Scr v (s₀.gpr .x5) (VG.Impl.Dsa.Generation.Layout.usedBytes pBytes)
  rand : GenerationTapeMemory (randTape h) v
  wr : v.wr = ⟨refillBase s₀, 480⟩ :: s₀.wr
  rd : v.rd = s₀.rd
  c0 : ctlWord v.mem (refillBase s₀) 0 = s₀.gpr .x2
  c1 : ctlWord v.mem (refillBase s₀) 1 = s₀.gpr .x7
  c2 : ctlWord v.mem (refillBase s₀) 2 = s₀.mem.readW (s₀.gpr .x7) 64

theorem entry_ok {pBytes : Nat} {s₀ u : State} (h : RefillABI pBytes s₀) (a : RefillAllocated h u) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.entryHeader ++ Impl.Dsa.AArch64.Generation.entryDerived)) u
      fun v => ∃ W, EntryDone h W v ∧
        Frame [⟨refillBase s₀, frameBytes⟩, ctlRegion (refillBase s₀)] u.mem v.mem ∧ Keep [.x3, .x4, .x8, .x9] u v := by
  have G := h.geo
  have hS := h.ctl_hash
  have hw480 : (⟨refillBase s₀, 480⟩ : Region) ∈ u.wr := by rw [a.wr]; exact List.mem_cons_self ..
  -- `state`'s words, as the entry reads them
  have stateSep : (inState s₀).Disjoint ⟨off (refillBase s₀) 296, 152⟩ :=
    h.frame_disjoint (r := inState s₀) (by simp) (by decide)
  have c0 : (inState s₀).Contains (s₀.gpr .x7) 8 := by
    have := Offset.contains_base (s₀.gpr .x7) (d := 0) (n := 8) (k := 32) (by decide) (by decide)
    simpa only [inState, BitVec.add_zero] using this
  have c8 : (inState s₀).Contains (s₀.gpr .x7 + BitVec.ofNat 64 8) 8 :=
    Offset.contains_base (s₀.gpr .x7) (d := 8) (n := 8) (k := 32) (by decide) (by decide)
  have st0 : u.mem.readW (u.gpr .x7) 64 = s₀.mem.readW (s₀.gpr .x7) 64 := by
    rw [a.regs .x7 (by simp)]
    exact a.mem.readW (r := inState s₀) c0
      (fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact stateSep) (by decide)
  have st1 : u.mem.readW (u.gpr .x7 + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 pBytes := by
    rw [a.regs .x7 (by simp)]
    rw [a.mem.readW (r := inState s₀) c8
      (fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact stateSep) (by decide)]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, ← h.width, Nat.mod_eq_of_lt (BitVec.isLt _)]
    rfl
  have rd0 : InRegions (u.rd ++ u.wr) (u.gpr .x7) 8 := by
    rw [a.regs .x7 (by simp), a.wr]
    exact ⟨inState s₀, List.mem_append_right _ (List.mem_cons_of_mem _ (by rw [h.wr]; simp)), c0⟩
  have rd8 : InRegions (u.rd ++ u.wr) (u.gpr .x7 + BitVec.ofNat 64 8) 8 := by
    rw [a.regs .x7 (by simp), a.wr]
    exact ⟨inState s₀, List.mem_append_right _ (List.mem_cons_of_mem _ (by rw [h.wr]; simp)), c8⟩
  apply WP.block_append
  refine WP.mono (header_run a.sp hw480 rd0 rd8) fun t ⟨hm, kt⟩ => ?_
  rw [st0, st1] at hm
  have RA := headerMem_rep G (initialRep u.mem (refillBase s₀) (refillGeometry h).hash) hS u.gpr
    (s₀.mem.readW (s₀.gpr .x7) 64) (BitVec.ofNat 64 pBytes)
  rw [← hm] at RA
  have fA : Frame [⟨refillBase s₀, frameBytes⟩, ctlRegion (refillBase s₀)] u.mem t.mem := by
    rw [hm]; exact headerMem_frame _ _ _ _ _
  have cA := headerMem_ctl u.mem (refillBase s₀) u.gpr (s₀.mem.readW (s₀.gpr .x7) 64) (BitVec.ofNat 64 pBytes)
  rw [← hm] at cA
  have spt : t.sp = refillBase s₀ := kt.sp.trans a.sp
  have wrt : t.wr = ⟨refillBase s₀, 480⟩ :: s₀.wr := kt.wr.trans a.wr
  have frt : Covers [⟨refillBase s₀, frameBytes⟩] t.wr := by
    rw [wrt]
    have := Offset.contains_base (refillBase s₀) (d := 0) (n := frameBytes) (k := 480) (by decide) (by decide)
    simp only [BitVec.add_zero] at this
    exact Covers.one ⟨_, List.mem_cons_self .., this⟩
  refine WP.mono (entryDerived_ok G RA spt frt (B := u.gpr .x5) rfl) fun v ⟨Rv, fv, kv⟩ => ?_
  have fV : Frame [⟨refillBase s₀, frameBytes⟩, ctlRegion (refillBase s₀)] u.mem v.mem :=
    fA.trans (fv.mono fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact List.mem_cons_self ..)
  have kV : Keep [.x3, .x4, .x8, .x9] u v := (kt.trans kv).mono (by decide)
  have r5 : u.gpr .x5 = s₀.gpr .x5 := a.regs _ (by simp)
  have spv : v.sp = refillBase s₀ := kV.sp.trans a.sp
  have wrv : v.wr = ⟨refillBase s₀, 480⟩ :: s₀.wr := kV.wr.trans a.wr
  have scr : Scr v (s₀.gpr .x5) (VG.Impl.Dsa.Generation.Layout.usedBytes pBytes) :=
    ⟨⟨s₀.gpr .x5, 0, (s₀.gpr .x6).toNat * 8, by rw [wrv]; exact List.mem_cons_of_mem _ (by rw [h.wr]; simp [inScr]),
      by simp [off], by have := h.scratchSize; omega, by have := h.scrBound; omega⟩,
      by have := h.scrBound; have := h.scratchSize; omega⟩
  have hh := (refillGeometry h).small_bound (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide)
  have ctlV : ∀ k < 4, ctlWord v.mem (refillBase s₀) k = ctlWord t.mem (refillBase s₀) k := fun k hk =>
    ctlWord_frame fv (fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact ctl_frame _) hk
  have fV480 : Frame [⟨refillBase s₀, 480⟩] u.mem v.mem := fV.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    rcases hr with rfl | rfl
    · have := Offset.sub_base (refillBase s₀) (d := 0) (n := frameBytes) (k := 480) (by decide)
      simpa only [BitVec.add_zero] using this
    · exact Offset.sub_base (refillBase s₀) (d := 448) (n := 32) (k := 480) (by decide)
  refine ⟨_, ⟨?_, ⟨_, Rv⟩, ?_, ?_, by simp [workspaceWords, derivedWords, workspaceSlots, headerWords, upd], scr, a.randMemory fV480 kV.rd, wrv, kV.rd.trans a.rd, ?_, ?_, ?_⟩, fV, kV⟩
  · exact { sp := spv
            fr := by rw [kv.wr]; exact frt
            sc := Covers.one (scr.region hh (by decide))
            slot := by
              show VG.Proof.RsaOaep.AArch64.word v.mem (refillBase s₀) (8 * 12) = (refillGeometry h).hash
              rw [Rv.fr 12 (by decide)]
              simp only [workspaceWords, derivedWords, workspaceSlots, List.foldl, upd, r5]
              rfl
            geo := G }
  · intro k hk h18 h26
    simp only [generationSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact absurd rfl h18 | exact absurd rfl h26 | skip
    all_goals simp only [workspaceWords, derivedWords, workspaceSlots, List.foldl, headerWords, upd, refillWords,
      r5, a.regs .x0 (by simp), a.regs .x1 (by simp), a.regs .x3 (by simp), a.regs .x4 (by simp)]
    all_goals first | rfl | simp [off]
  · simp [workspaceWords, upd]
  · rw [ctlV 0 (by decide), cA.1, a.regs .x2 (by simp)]
  · rw [ctlV 1 (by decide), cA.2.1, a.regs .x7 (by simp)]
  · rw [ctlV 2 (by decide), cA.2.2]

/-- The subgroup's width in `W 18` and `W 26`: the search's memory. -/
theorem widthHeader_ok {pBytes qBytes : Nat} {s₀ v : State} {h : RefillABI pBytes s₀} {W : Nat → BitVec 64}
    (E : EntryDone h W v) (hq : qBytes = Spec.Dsa.generationQLen pBytes) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.Refill.widthHeader qBytes)) v fun w =>
      GenerationMemory (refillContext h) (upd (upd W 18 (BitVec.ofNat 64 qBytes)) 26 (BitVec.ofNat 64 qBytes)) w ∧
      W 16 = 0 ∧ W 10 = 0 ∧ ctlWord w.mem (refillBase s₀) 0 = s₀.gpr .x2 ∧ ctlWord w.mem (refillBase s₀) 1 = s₀.gpr .x7 ∧
      ctlWord w.mem (refillBase s₀) 2 = s₀.mem.readW (s₀.gpr .x7) 64 ∧
      Frame [⟨refillBase s₀, frameBytes⟩] v.mem w.mem ∧ Keep [.x3] v w := by
  have L := E.layout
  obtain ⟨V, R⟩ := E.rep
  have hq32 : qBytes < 2 ^ 16 := by subst hq; unfold Spec.Dsa.generationQLen; split <;> decide
  have hmv : (BitVec.ofNat 16 qBytes).setWidth 64 = BitVec.ofNat 64 qBytes := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  have hq2 : qBytes = 20 ∨ qBytes = 32 := by subst hq; unfold Spec.Dsa.generationQLen; split <;> simp
  have s144 : InRegions v.wr (v.sp + BitVec.ofNat 64 144) 8 := by rw [L.sp]; exact L.st (d := 144) (by decide)
  have s208 : InRegions v.wr (v.sp + BitVec.ofNat 64 208) 8 := by rw [L.sp]; exact L.st (d := 208) (by decide)
  refine WP.mono (WP.keep [.x3] (Q := fun w => w.mem = (v.mem.writeW (off (refillBase s₀) 144) (BitVec.ofNat 64 qBytes)).writeW
      (off (refillBase s₀) 208) (BitVec.ofNat 64 qBytes)) (by
    unfold Impl.Dsa.AArch64.Generation.Refill.widthHeader
    brun [State.write, exec_storeSp (off := 144) (by decide), exec_storeSp (off := 208) (by decide), s144, s208, hmv]
    rw [L.sp]) (by rcases hq2 with rfl | rfl <;> decide) rfl
    (by rcases hq2 with rfl | rfl <;> decide +kernel)) fun w ⟨hm, kw⟩ => ?_
  have Rw : Rep w.mem (refillBase s₀) (refillGeometry h).hash V
      (upd (upd W 18 (BitVec.ofNat 64 qBytes)) 26 (BitVec.ofNat 64 qBytes)) := by
    rw [hm]; exact (R.wf L.geo (k := 18) (by decide) _).wf L.geo (k := 26) (by decide) _
  have fw : Frame [⟨refillBase s₀, frameBytes⟩] v.mem w.mem := by
    rw [hm]
    exact ((Frame.refl _ _).writeW List.mem_cons_self _ (cF _ (d := 144) (by decide))).writeW
      List.mem_cons_self _ (cF _ (d := 208) (by decide))
  have cw : ∀ k < 4, ctlWord w.mem (refillBase s₀) k = ctlWord v.mem (refillBase s₀) k := fun k hk =>
    ctlWord_frame fw (fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact ctl_frame _) hk
  have fc : Frame (refillContext h).changed v.mem w.mem := GenerationContext.frame_single fw
  have randW : GenerationTapeMemory (randTape h) w :=
    E.rand.frame (p := refillContext h) fc kw.rd kw.wr
  refine ⟨⟨lay_of_rep L R Rw (by simp [upd]) kw.sp kw.wr, ⟨V, Rw⟩, ?_, E.scratch.congr kw.wr, randW,
    randW.slice (Nat.zero_le _), randW⟩, E.w16, E.w10, by rw [cw 0 (by decide)]; exact E.c0,
    by rw [cw 1 (by decide)]; exact E.c1, by rw [cw 2 (by decide)]; exact E.c2, fw, kw⟩
  intro k hk
  by_cases h18 : k = 18
  · subst h18; simp [upd, refillContext, refillWords, hq]
  by_cases h26 : k = 26
  · subst h26; simp [upd, refillContext, refillWords, hq]
  simp only [upd, h18, h26, ite_false]
  exact E.slots k hk h18 h26

end VG.Proof.Dsa.AArch64.Generation.Refill
