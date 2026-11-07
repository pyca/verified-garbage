module
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Loop

import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.SaveGP
import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Save
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Scalar
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.Spill
import VerifiedGarbage.Proof.ChaCha20.Keystream

@[expose] public section

namespace VG.Proof.ChaCha20.AArch64.Mixed8
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed8
open VG.Proof.ChaCha20.AArch64.Xor (XPre st dp L bp stR dR bR)

abbrev saveV : List Instr := [.strq .v8 .x3 128,.strq .v9 .x3 144]
abbrev restoreV : List Instr := [.ldrq .v8 .x3 128,.ldrq .v9 .x3 144]
abbrev savedVR (s : State) : Region := ⟨s.gpr .x3 + BitVec.ofNat 64 128,32⟩

theorem saveV_ok (s : State)
    (ho0 : InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 128) 16)
    (ho1 : InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 144) 16) :
    WP isa (.block saveV) s fun u =>
      u.gpr = s.gpr ∧ u.v = s.v ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp ∧
      Frame [savedVR s] s.mem u.mem ∧
      u.mem.read (s.gpr .x3 + BitVec.ofNat 64 128) 16 = s.v .v8 ∧
      u.mem.read (s.gpr .x3 + BitVec.ofNat 64 144) 16 = s.v .v9 := by
  apply WP.of_runBlock
  simp only [↓reduceIte, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self, saveV,runBlock_cons,runBlock_nil,exec,addr,
    State.store,ho0,ho1,Option.bind_some,Option.some.injEq,exists_eq_left',isa,runStep_some]
  refine ⟨trivial,trivial,trivial,trivial,trivial,?_,?_,?_⟩
  · have h0 : (savedVR s).Contains (s.gpr .x3 + BitVec.ofNat 64 128) 16 := by
      simp only [Region.Contains,BitVec.sub_self]; decide
    have h1 : (savedVR s).Contains (s.gpr .x3 + BitVec.ofNat 64 144) 16 := by
      exact Offset.contains (s.gpr .x3) (by decide : 128 ≤ 144)
        (by decide : 144 + 16 ≤ 128 + 32) (by decide)
    exact ((Frame.refl _ _).write (List.mem_cons_self ..) _ h0).write
      (List.mem_cons_self ..) _ h1
  · rw [Mem.read_write_sep (Offset.sep (s.gpr .x3) (d := 128) (n := 16) (e := 144) (k := 16)
      (by decide) (by decide) (by decide)) (by decide),VG.Proof.ChaCha20.AArch64.Rows6.read_write_self]
  · exact VG.Proof.ChaCha20.AArch64.Rows6.read_write_self _ _ _

theorem restoreV_ok {s : State} (v8 v9 : BitVec 128)
    (hi0 : InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 128) 16)
    (hi1 : InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 144) 16)
    (hm0 : s.mem.read (s.gpr .x3 + BitVec.ofNat 64 128) 16 = v8)
    (hm1 : s.mem.read (s.gpr .x3 + BitVec.ofNat 64 144) 16 = v9) :
    WP isa (.block restoreV) s fun u =>
      u.v .v8 = v8 ∧ u.v .v9 = v9 ∧ u.gpr = s.gpr ∧ u.mem = s.mem ∧
      u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [restoreV,runBlock_cons,runBlock_nil,exec,addr,
    ite_true,State.load,hi0,hi1,State.setV,hm0,hm1,Option.bind_some,Option.map_some,
    Option.some.injEq,exists_eq_left',isa,runStep_some]
  trivial

theorem gp_same {s₀ s u : State} {t : Nat} (h : GPInv s₀ t s)
    (hg : u.gpr = s.gpr) (hm : u.mem = s.mem) (hr : u.rd = s.rd)
    (hw : u.wr = s.wr) (hsp : u.sp = s.sp) : GPInv s₀ t u := by
  refine ⟨⟨?_,?_,?_,?_,h.le,?_,hr.trans h.rd,hw.trans h.wr,hsp.trans h.sp,?_,?_,?_⟩,?_,?_⟩
  · rw [hg]; exact h.x0
  · rw [hg]; exact h.x1
  · rw [hg]; exact h.x2
  · rw [hg]; exact h.x3
  · intro r hr n20 n19 n26; rw [hg]; exact h.cs r hr n20 n19 n26
  · rw [hm]; exact h.cnt
  · rw [hm]; exact h.data
  · rw [hm]; exact h.frame
  · rw [hg]; exact h.x20
  · rw [hm]; exact h.saved

theorem enterV_ok {s₀ s : State} (hp : XPre s₀) (h : GPInv s₀ 0 s)
    (hv : s.v = s₀.v) : WP isa (.block saveV) s (BulkInv s₀ 0) := by
  have ho (d : Nat) (hd : d + 16 ≤ 320) : InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 d) 16 := by
    rw [h.wr,hp.wr,h.x3]
    exact ⟨bR s₀,by simp,Offset.contains_base _ hd (by omega)⟩
  refine (saveV_ok s (ho 128 (by decide)) (ho 144 (by decide))).mono fun u
    ⟨hg,_,hr,hw,hsp,hf,hm0,hm1⟩ => ?_
  have hsub : (savedVR s).Sub (bR s₀) := by
    rw [show savedVR s = ⟨bp s₀ + BitVec.ofNat 64 128,32⟩ by rw [savedVR,h.x3]]
    exact Offset.sub_base _ (by decide)
  have hfb : Frame [bR s₀] s.mem u.mem := hf.sub (by
    intro r hr; have he := List.mem_singleton.mp hr; subst r
    exact ⟨bR s₀,by simp,hsub⟩)
  refine ⟨⟨⟨?_,?_,?_,?_,h.le,?_,hr.trans h.rd,hw.trans h.wr,hsp.trans h.sp,?_,?_,
    h.frame.trans (hfb.mono (by simp))⟩,?_,?_⟩,?_⟩
  · rw [hg]; exact h.x0
  · rw [hg]; exact h.x1
  · rw [hg]; exact h.x2
  · rw [hg]; exact h.x3
  · intro r hr n20 n19 n26; rw [hg]; exact h.cs r hr n20 n19 n26
  · rw [VG.Proof.ChaCha20.AArch64.Xor.stateAt_frame hfb (by simpa using hp.st_b)]; exact h.cnt
  · intro k hk
    rw [hfb.bytes (R := dR s₀) (by simpa using hp.d_b)
      (by have hL := VG.Proof.ChaCha20.AArch64.Xor.L_lt s₀; change L s₀ ≤ 2 ^ 64; omega) hk]
    exact h.data k hk
  · rw [hg]; exact h.x20
  · intro j
    rw [hf.readW (r := guardR s₀ j) (by simp only [Region.Contains,BitVec.sub_self]; decide)
      (by intro r hr; have he := List.mem_singleton.mp hr; subst r
          change (guardR s₀ j).Disjoint ⟨s.gpr .x3 + BitVec.ofNat 64 128,32⟩
          rw [h.x3]
          exact Offset.disjoint _ (by have hj := j.isLt; omega)
            (by have hj := j.isLt; omega) (by decide)) (by decide),h.saved j]
  · intro j
    have hj : j = 0 ∨ j = 1 := by simp only [Fin.ext_iff]; omega
    rcases hj with rfl | rfl
    · change u.mem.read (bp s₀ + BitVec.ofNat 64 128) 16 = s₀.v .v8
      simpa only [h.x3,hv] using hm0
    · change u.mem.read (bp s₀ + BitVec.ofNat 64 144) 16 = s₀.v .v9
      simpa only [h.x3,hv] using hm1

theorem enter_ok {s₀ s : State} (hp : XPre s₀) (h : LInv s₀ 0 s)
    (hold : ∀ r ∈ preserved, s.gpr r = s₀.gpr r) (hv : s.v = s₀.v) :
    WP isa (.block enter) s (BulkInv s₀ 0) := by
  unfold enter
  apply WP.block_append_iff.mpr
  refine (VG.Proof.ChaCha20.AArch64.Mixed5.keeps_vectors (by
    intro i hi; simp only [VG.Impl.ChaCha20.AArch64.Mixed5.enter,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> rfl) (enterGP_ok hp h hold)).mono fun u ⟨hu,huv,_,_,_⟩ => ?_
  exact enterV_ok hp hu (huv.trans hv)

theorem leaveV_ok {s₀ s : State} {t : Nat} (hp : XPre s₀) (h : BulkInv s₀ t s) :
    WP isa (.block restoreV) s fun u =>
      GPInv s₀ t u ∧ u.v .v8 = s₀.v .v8 ∧ u.v .v9 = s₀.v .v9 := by
  have hi (d : Nat) (hd : d + 16 ≤ 320) : InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 d) 16 := by
    rw [h.rd,hp.rd,h.wr,hp.wr,h.x3]
    exact ⟨bR s₀,by simp,Offset.contains_base _ hd (by omega)⟩
  have hm0 : s.mem.read (s.gpr .x3 + BitVec.ofNat 64 128) 16 = s₀.v .v8 := by
    rw [h.x3]; exact h.savedV 0
  have hm1 : s.mem.read (s.gpr .x3 + BitVec.ofNat 64 144) 16 = s₀.v .v9 := by
    rw [h.x3]; exact h.savedV 1
  refine (restoreV_ok _ _ (hi 128 (by decide)) (hi 144 (by decide)) hm0 hm1).mono fun u
    ⟨hv8,hv9,hg,hm,hr,hw,hsp⟩ => ⟨gp_same h.toGPInv hg hm hr hw hsp,hv8,hv9⟩

theorem leave_ok {s₀ s : State} {t : Nat} (hp : XPre s₀) (h : BulkInv s₀ t s) :
    WP isa (.block leave) s fun u => LInv s₀ t u ∧
      (∀ r ∈ preserved, u.gpr r = s₀.gpr r) ∧ u.v .v8 = s₀.v .v8 ∧ u.v .v9 = s₀.v .v9 := by
  unfold leave
  apply WP.block_append_iff.mpr
  refine (leaveV_ok hp h).mono fun u ⟨hu,hv8,hv9⟩ => ?_
  refine (VG.Proof.ChaCha20.AArch64.Mixed5.keeps_vectors (by
    intro i hi; simp only [VG.Impl.ChaCha20.AArch64.Mixed5.leave,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl <;> rfl) (leaveGP_ok hp hu)).mono fun v ⟨⟨hl,hcs⟩,hv,_,_,_⟩ => ?_
  exact ⟨hl,hcs,by rw [hv]; exact hv8,by rw [hv]; exact hv9⟩
/-! ## `vg_chacha20_xor`'s entry to and exit from the chunks -/

open VG.Proof.ChaCha20.AArch64.Xor (TPre tp tR T0 Dst Src wp_movS S0)
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.ChaCha20 (stateAt)

/-- `enterFrom`, from a state with the entry state's registers but `x5`. -/
theorem tenter_ok {s₀ a : State} (hp : TPre s₀) (hg : ∀ r, r ≠ .x5 → a.gpr r = s₀.gpr r)
    (hm : a.mem = s₀.mem) (hrd : a.rd = s₀.rd) (hwr : a.wr = s₀.wr) (hsp : a.sp = s₀.sp)
    (hv : a.v = s₀.v) : WP isa (.block enterFrom) a (TInv s₀ 0) := by
  have hL := VG.Proof.ChaCha20.AArch64.Xor.L_lt s₀
  have hb : a.gpr .x3 = bp s₀ := hg _ (by decide)
  have hw : a.wr = [stR s₀,tR s₀,bR s₀] := hwr.trans hp.wr
  have ho (d : Nat) (n : Nat) (hd : d + n ≤ 320) : InRegions a.wr (a.gpr .x3 + BitVec.ofNat 64 d) n := by
    rw [hw,hb]; exact ⟨bR s₀,by simp,Offset.contains_base _ hd (by omega)⟩
  rw [show enterFrom = Spill.saveCode .x3 savedFrom ++
    ([.addImm .x .x20 .x3 0] ++ (saveV ++ [.addImm .x .x27 .x1 0, .addImm .x .x1 .x4 0])) from rfl]
  refine Spill.save_ok (by decide) (fun p hp' => ho p.2 8 (by revert p; decide)) ?_
  refine WP.block_append_iff.mpr (wp_movS fun b ub hbsp hbv => WP.block_nil ?_)
  have hb3 : b.gpr .x3 = bp s₀ := by rw [ub.other _ (by decide)]; exact hb
  have hbw : b.wr = a.wr := ub.wr
  refine WP.block_append_iff.mpr ((saveV_ok b (by rw [hbw,hb3,← hb]; exact ho 128 16 (by decide))
    (by rw [hbw,hb3,← hb]; exact ho 144 16 (by decide))).mono fun c ⟨hcg,hcv,hcr,hcw,hcsp,hcf,hm0,hm1⟩ => ?_)
  refine wp_movS fun d ud hdsp _ => wp_movS fun e ue hesp _ => WP.block_nil ?_
  have ga : ∀ r, r ≠ .x20 → r ≠ .x27 → r ≠ .x1 → e.gpr r = a.gpr r := fun r h20 h21 h1 => by
    rw [ue.other r h1,ud.other r h21,hcg,ub.other r h20]
  have hbm : b.mem = Spill.saveMem a.mem (a.gpr .x3) a.gpr savedFrom := ub.mem
  have hem : e.mem = c.mem := by rw [ue.mem,ud.mem]
  have hsub : Region.Sub (savedVR b) (bR s₀) := by
    rw [savedVR,hb3]; exact Offset.sub_base _ (by decide)
  have f₁ : Frame [bR s₀] s₀.mem b.mem := by
    rw [hbm,hm,hb]; exact Spill.saveMem_frame_base (by decide) (by decide) _ _ _
  have f₂ : Frame [bR s₀] b.mem c.mem := hcf.sub (by
    intro r hr; simp only [List.mem_singleton] at hr; subst r
    exact ⟨bR s₀,by simp,hsub⟩)
  have hfb : Frame [bR s₀] s₀.mem e.mem := by rw [hem]; exact f₁.trans f₂
  have hnb : ∀ r ∈ [bR s₀], (tR s₀).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hp.t_b
  have hnd : ∀ r ∈ [bR s₀], (dR s₀).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hp.d_b
  refine ⟨?_,?_,?_,?_,?_,?_,by omega,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [ga _ (by decide) (by decide) (by decide),hg _ (by decide)]
  · rw [ue.gpr,ud.other _ (by decide),hcg,ub.other _ (by decide),hg _ (by decide)]; simp
  · rw [ga _ (by decide) (by decide) (by decide),hg _ (by decide)]
    simp only [Nat.mul_zero,Nat.sub_zero]
    simpa only [BitVec.setWidth_eq] using (BitVec.ofNat_toNat 64 (s₀.gpr .x2)).symm
  · rw [ga _ (by decide) (by decide) (by decide),hb]
  · rw [ue.other _ (by decide),ud.other _ (by decide),hcg,ub.gpr,hb]
  · rw [ue.other _ (by decide),ud.gpr,hcg,ub.other _ (by decide),hg _ (by decide)]; simp
  · intro r hr _ h20 h21 _
    have n1 : r ≠ .x1 := by intro he; subst r; simp [preserved] at hr
    have n5 : r ≠ .x5 := by intro he; subst r; simp [preserved] at hr
    rw [ga r h20 h21 n1,hg r n5]
  · rw [ue.rd,ud.rd,hcr,ub.rd,hrd]
  · rw [ue.wr,ud.wr,hcw,ub.wr,hwr]
  · rw [hesp,hdsp,hcsp,hbsp,hsp]
  · rw [VG.Proof.ChaCha20.AArch64.Xor.stateAt_frame hfb (by simpa using hp.st_b),
      VG.Proof.ChaCha20.ctr_zero]
  · intro k hk
    simp only [Nat.mul_zero,Nat.not_lt_zero,ite_false]
    exact hfb.bytes (R := tR s₀) hnb (Nat.le_of_lt hL) hk
  · intro k hk _
    exact hfb.bytes (R := dR s₀) hnd (Nat.le_of_lt hL) hk
  · have hsv : TSaved s₀ b.mem := by
      intro p hp'
      rw [hbm,← hb,Spill.saveMem_saved (by decide) a.mem (a.gpr .x3) a.gpr p hp',
        hg _ (by revert p; decide)]
    rw [hem]
    exact Spill.Saved.frame_in hsv (lo := 256) (n := 32) (by decide) hcf (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      rw [savedVR,hb3]
      exact Offset.disjoint _ (by decide) (by decide) (by decide))
  · intro j
    have hj : j = 0 ∨ j = 1 := by simp only [Fin.ext_iff]; omega
    rw [hem]
    rcases hj with rfl | rfl
    · change c.mem.read (bp s₀ + BitVec.ofNat 64 128) 16 = s₀.v .v8
      rw [← hb3,hm0,hbv,hv]
    · change c.mem.read (bp s₀ + BitVec.ofNat 64 144) 16 = s₀.v .v9
      rw [← hb3,hm1,hbv,hv]

/-- After the chunks of `vg_chacha20_xor` (or none): the source (`x1`) and
the destination (`x4`) advanced past `t` chunks, our caller's registers
restored. -/
structure TRest (s₀ : State) (t : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = st s₀
  x1 : s.gpr .x1 = dp s₀ + BitVec.ofNat 64 (512 * t)
  x2 : s.gpr .x2 = BitVec.ofNat 64 (L s₀ - 512 * t)
  x3 : s.gpr .x3 = bp s₀
  x4 : s.gpr .x4 = tp s₀ + BitVec.ofNat 64 (512 * t)
  le : 512 * t ≤ L s₀
  cs : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  cnt : stateAt s.mem (st s₀) = ctr (S0 s₀) (8 * t)
  data : Dst s₀ (512 * t) s.mem
  src : Src s₀ (512 * t) s.mem
  v8 : s.v .v8 = s₀.v .v8
  v9 : s.v .v9 = s₀.v .v9

/-- `leaveFrom`. -/
theorem tleave_ok {s₀ s : State} (hp : TPre s₀) {t : Nat} (h : TInv s₀ t s) :
    WP isa (.block leaveFrom) s (TRest s₀ t) := by
  have hw : s.wr = [stR s₀,tR s₀,bR s₀] := h.wr.trans hp.wr
  have hi (d n : Nat) (hd : d + n ≤ 320) : InRegions (s.rd ++ s.wr) (bp s₀ + BitVec.ofNat 64 d) n := by
    rw [hw]; exact ⟨bR s₀,by simp,Offset.contains_base _ hd (by omega)⟩
  rw [show leaveFrom = [VG.Impl.ChaCha20.AArch64.Xor.mov .x4 .x1, VG.Impl.ChaCha20.AArch64.Xor.mov .x1 .x27] ++
    (restoreV ++ Spill.restoreCode .x3 savedFrom) from rfl]
  refine WP.block_append_iff.mpr (wp_movS fun a ua hasp hav => wp_movS fun b ub hbsp hbv =>
    WP.block_nil ?_)
  have hb3 : b.gpr .x3 = bp s₀ := by rw [ub.other _ (by decide),ua.other _ (by decide)]; exact h.x3
  have hbm : b.mem = s.mem := by rw [ub.mem,ua.mem]
  have hbrw : b.rd ++ b.wr = s.rd ++ s.wr := by rw [ub.rd,ub.wr,ua.rd,ua.wr]
  refine WP.block_append_iff.mpr ((restoreV_ok (s₀.v .v8) (s₀.v .v9)
    (by rw [hbrw,hb3]; exact hi 128 16 (by decide)) (by rw [hbrw,hb3]; exact hi 144 16 (by decide))
    (by rw [hbm,hb3]; exact h.savedV 0) (by rw [hbm,hb3]; exact h.savedV 1)).mono
    fun c ⟨hv8,hv9,hcg,hcm,hcr,hcw,hcsp⟩ => ?_)
  have hc3 : c.gpr .x3 = bp s₀ := by rw [hcg]; exact hb3
  refine (Spill.restore_wp hc3 (by decide) (by decide) (fun p hp' => by
      rw [hcr,hcw,hbrw]; exact hi p.2 8 (by revert p; decide))
    (by rw [hcm,hbm]; exact h.saved)).mono fun d hd => ?_
  have gb : ∀ r, r ∉ savedFrom.map Prod.fst → d.gpr r = b.gpr r := fun r hr => by
    rw [hd.other r hr,hcg]
  have hdm : d.mem = s.mem := by rw [hd.mem,hcm,hbm]
  refine ⟨?_,?_,?_,?_,?_,h.le,?_,?_,?_,?_,by rw [hdm]; exact h.cnt,by rw [hdm]; exact h.data,
    by rw [hdm]; exact h.src,by rw [hd.v]; exact hv8,by rw [hd.v]; exact hv9⟩
  · rw [gb _ (by decide),ub.other _ (by decide),ua.other _ (by decide),h.x0]
  · rw [gb _ (by decide),ub.gpr,ua.other _ (by decide),h.x27]
  · rw [gb _ (by decide),ub.other _ (by decide),ua.other _ (by decide),h.x2]
  · rw [gb _ (by decide),hb3]
  · rw [gb _ (by decide),ub.other _ (by decide),ua.gpr,h.x1]
  · intro r hr
    by_cases hm : r ∈ savedFrom.map Prod.fst
    · exact hd.gpr_of (.inl hm)
    · have n1 : r ≠ .x1 := by intro he; subst r; simp [preserved] at hr
      have n4 : r ≠ .x4 := by intro he; subst r; simp [preserved] at hr
      rw [gb r hm,ub.other r n1,ua.other r n4]
      refine h.cs r hr ?_ ?_ ?_ ?_ <;> intro he <;> subst r <;> simp [savedFrom] at hm
  · rw [hd.rd,hcr,ub.rd,ua.rd,h.rd]
  · rw [hd.wr,hcw,ub.wr,ua.wr,h.wr]
  · rw [hd.sp,hcsp,hbsp,hasp,h.sp]

end VG.Proof.ChaCha20.AArch64.Mixed8
