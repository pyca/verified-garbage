module

public import VerifiedGarbage.Proof.Gcm.RISCV64.Prepared.Head

/-! # Store the GHASH result and wipe the frame -/

@[expose] public section
namespace VG.Proof.Gcm.RISCV64
open VG.Impl.Gcm.RISCV64.Prepared
open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Gcm.RISCV64
open VG.WriteBytes
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom)

theorem wipe14_ok (u : State) {B : Addr} (hR : (⟨B, 112⟩ : Region) ∈ u.wr) (hsp : u.sp = B)
    (hal : B.toNat % 16 = 0) :
    WP isa (.block (Impl.StackScratch.RISCV64.wipe 14)) u fun u' => Frame [⟨B, 112⟩] u.mem u'.mem ∧
      (∀ r, r ≠ .t5 → r ≠ .t6 → u'.gpr r = u.gpr r) ∧ u'.sp = u.sp := by
  obtain ⟨u', he, hf, ho, hs, -, -⟩ := wipe_run ⟨B, 112⟩ u 14 hR (by rw [hsp]; omega_using [hal])
    (fun k hk => by rw [hsp]; exact Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk]))
  exact ⟨_, _, Exec.block_iff.mpr he, hf, ho, hs⟩

theorem cached_tail_ok {H : Block} (s : State) (hp : CachedPre H s) (u : State) {Y : Block} (hy : w2 (u.gpr Y0) (u.gpr Y1) = Y)
    (hyp : u.gpr YP = s.gpr .a1) (hwrU : u.wr = (allocd 112 s).wr) (hsp : u.sp = (allocd 112 s).sp)
    (hslot : ∀ p ∈ compactSaved, u.mem.readW ((allocd 112 s).sp + BitVec.ofNat 64 p.2) 64 = s.gpr p.1) :
    WP isa (.block (storeY ++ (.addSp .t0 0 :: compactRestore) ++ Impl.StackScratch.RISCV64.wipe 14)) u
      fun t => blockAt t.mem (s.gpr .a1) = Y ∧ (∀ r ∈ savedRegs, t.gpr r = s.gpr r) ∧ t.sp = u.sp := by
  obtain ⟨hrd, hwr, _, hsh, hsy, hsd, hfd, hF, _⟩ := hp
  set a := allocd 112 s with ha
  have awr : a.wr = ⟨a.sp, 112⟩ :: s.wr := rfl
  obtain hwy : ∀ off, off ≤ 8 → ∀ j < 8, InRegions u.wr (s.gpr .a1 + BitVec.ofNat 64 (off + j)) 1 :=
    fun off ho j hj => ⟨⟨s.gpr .a1, 16⟩, by rw [hwrU, awr, hwr]; simp,
      Offset.contains_base _ (by omega_using [ho, hj]) (by omega_using [ho, hj])⟩
  rw [WP.block_append_iff, WP.block_append_iff, storeY, WP.block_append_iff]
  refine WP.mono (ByteLoad.storeBE_ok (s := u) (v := Y0) (tmp := .t2) (n := YP) (off := 0) (w := 8)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by rw [hyp]; exact hwy 0 (by decide)))
    fun s₁ e₁ => ?_
  subst e₁
  refine WP.mono (ByteLoad.storeBE_ok (v := Y1) (tmp := .t2) (n := YP) (off := 8) (w := 8)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [RegUpd.gpr_write_of_ne _ _ (by decide)]; show ∀ j < 8, InRegions u.wr _ 1
        rw [hyp]; exact hwy 8 (by decide)))
    fun s₂ e₂ => ?_
  subst e₂
  simp only [RegUpd.gpr_write_of_ne _ _ (show YP ≠ .t2 by decide), RegUpd.gpr_write_of_ne _ _ (show Y1 ≠ .t2 by decide),
    hyp]
  obtain Fy : Frame [⟨s.gpr .a1, 16⟩] u.mem
      (writeBytes (writeBytes u.mem (s.gpr .a1 + BitVec.ofNat 64 0) (ByteLoad.beBytes 8 (u.gpr Y0)))
        (s.gpr .a1 + BitVec.ofNat 64 8) (ByteLoad.beBytes 8 (u.gpr Y1))) :=
    (writeBytes_frame _ _ _ (Offset.contains_base _ (by simp [ByteLoad.beBytes_length]) (by decide))).trans
      (writeBytes_frame _ _ _ (Offset.contains_base _ (by simp [ByteLoad.beBytes_length]) (by decide)))
  obtain hm : ∀ p ∈ compactSaved, (writeBytes (writeBytes u.mem (s.gpr .a1 + BitVec.ofNat 64 0)
      (ByteLoad.beBytes 8 (u.gpr Y0))) (s.gpr .a1 + BitVec.ofNat 64 8)
        (ByteLoad.beBytes 8 (u.gpr Y1))).readW (a.sp + BitVec.ofNat 64 p.2) 64 = s.gpr p.1 := by
    intro p hp
    obtain hd : 32 ≤ p.2 ∧ p.2 + 8 ≤ 112 := by
      simp only [compactSaved, saved, slot, List.map, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    obtain c : (⟨a.sp + BitVec.ofNat 64 p.2, 8⟩ : Region).Contains (a.sp + BitVec.ofNat 64 p.2) 8 :=
      Region.contains_self _ _
    simp only [Mem.readW]
    rw [Frame.read Fy c (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
          exact sub_disj (Offset.sub_base _ (by omega_using [hd])) hsy) (by decide)]
    have := hslot p hp
    simp only [Mem.readW] at this
    exact this
  refine WP.mono (compact_restore_ok _ ?_ s.gpr ?_) fun s₃ ⟨r3, k4, m4, p4⟩ => ?_
  · simp only [RegUpd.sp_write, RegUpd.wr_write]; rw [hsp]; exact hF.of_wr hwrU
  · simp only [RegUpd.sp_write, RegUpd.mem_write]; rw [hsp]; exact hm
  obtain sp3 : s₃.sp = a.sp := by rw [p4]; simp only [RegUpd.sp_write]; exact hsp
  obtain hRw : (⟨a.sp, 112⟩ : Region) ∈ s₃.wr := by
    rw [k4.2.2]; simp only [RegUpd.wr_write]; rw [hwrU, awr]; exact List.mem_cons_self
  refine WP.mono (wipe14_ok s₃ hRw sp3 hF.al) fun t ⟨ft, gt, pt⟩ => ?_
  refine ⟨?_, fun r hr => ?_, ?_⟩
  · have hyb : blockAt t.mem (s.gpr .a1) = blockAt s₃.mem (s.gpr .a1) :=
      Proof.Gcm.blockAt_congr fun i hi => ft _ fun r hr hc => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
        exact hsy _ hc (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi]))
    rw [hyb, m4]
    simp only [RegUpd.mem_write]
    rw [blockAt_store, hy]
  · have h56 : r ≠ .t5 ∧ r ≠ .t6 := by
      simp only [savedRegs, saved, List.map, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [gt r h56.1 h56.2, r3 r hr]
  · rw [pt, p4]; simp only [RegUpd.sp_write]


end VG.Proof.Gcm.RISCV64
