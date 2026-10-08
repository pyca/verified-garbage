import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.FinishOps
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Env
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Counter

/-! # Writing the final counter and hash and restoring the entry registers -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Impl.Gcm.X86_64.StitchAvx8 (finish)
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame)
open VG.Spec.Gcm (Block blockAt inc32)

structure FinishPost (s₀ start : State) (n : Nat) (y : Block) (s : State) : Prop where
  counter : blockAt s.mem (cp s₀) = Nat.repeat inc32 n (cb s₀)
  hash : blockAt s.mem (yp s₀) = y
  frame : Frame [cR s₀, yR s₀] start.mem s.mem
  regs : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem finish_ok {s₀ s : State} {P : Nat → Block} (hp : SPre s₀) (hE : Env s₀ P s)
    (n : Nat) (hv : (s.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32 + BitVec.ofNat 32 (n + 8)) :
    WP isa (.block finish) s (FinishPost s₀ s n (s.lane .xmm2 0)) := by
  have hcode : finish = finishHead ++
      ([.vop (.vbin .vpshufb .l128 .xmm2 .xmm2 .xmm0),
        .vmovdquStore .l128 (at_ .rcx 0) .xmm2] : List Instr) ++
      [.vop .vzeroupper] ++ restoreEntry := rfl
  rw [hcode, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (finishHead_ok s (by
    rw [hE.wr, hE.rsi]; exact in_sub hp.c_in (off := 12) (by decide)) (by
    rw [hE.rd, hE.wr, hE.r11]; exact in_rdwr (in_sub hp.p_in (off := 768) (by decide))) (by
    rw [hE.r11, hE.rsi]
    exact (hp.p_c.sub_left (Offset.sub_base (pp s₀) (d := 768) (n := 16) (k := 1024) (by decide))).sub_right
      (Offset.sub_base (cp s₀) (d := 12) (n := 4) (k := 16) (by decide))))
    fun t ⟨htM, ht0, htG, htX, htR, htW⟩ => ?_
  have hnum : (s.gpr .r8).setWidth 32 - 8 = (cb s₀).extractLsb' 0 32 + BitVec.ofNat 32 n := by
    rw [hv, BitVec.ofNat_add]
    change ((cb s₀).extractLsb' 0 32 + (BitVec.ofNat 32 n + 8)) - 8 = _
    rw [← BitVec.add_assoc, BitVec.add_sub_cancel]
  rw [hE.rsi, hnum] at htM
  have fct : Frame [cR s₀] s.mem t.mem := by
    rw [htM]
    exact (Frame.refl _ _).writeW List.mem_cons_self _
      (Offset.contains_base (cp s₀) (d := 12) (n := 4) (k := 16) (by decide) (by decide))
  have hcb : blockAt s.mem (cp s₀) = cb s₀ := blockAt_frame hE.frame (by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.d_c.symm
    · exact hp.p_c.symm)
  have ct : blockAt t.mem (cp s₀) = Nat.repeat inc32 n (cb s₀) := by
    rw [htM]
    have hc := refreshCounter_ok s.mem (cp s₀) (cb s₀) 0 n hcb
    simpa only [Nat.zero_add] using hc
  rw [WP.block_append_iff]
  refine WP.mono (store16_ok .xmm2 .xmm2 .rcx t (by
    rw [ht0, hE.r11]; exact hE.mask) (by
    rw [htW, hE.wr, htG _ (by decide) (by decide), hE.rcx]; exact hp.y_in))
    fun u ⟨huM, huG, huR, huW, _⟩ => ?_
  rw [htG _ (by decide) (by decide), hE.rcx, htX _ (by decide) 0 (by decide)] at huM
  have fyu : Frame [yR s₀] t.mem u.mem := by
    rw [huM]
    exact (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
  have fu : Frame [cR s₀, yR s₀] s.mem u.mem :=
    (fct.mono (by simp)).trans (fyu.mono (by simp))
  have py : ∀ r ∈ [cR s₀, yR s₀], (pR s₀).Disjoint r := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.p_c
    · exact hp.p_y
  have saved : ∀ d, d + 8 ≤ 1024 → u.mem.readW (pp s₀ + BitVec.ofNat 64 d) 64 =
      s.mem.readW (pp s₀ + BitVec.ofNat 64 d) 64 := fun d hd =>
    fu.readW (r := pR s₀) (Offset.contains_base _ hd (by omega)) py (by decide)
  have ur11 : u.gpr .r11 = pp s₀ := by rw [huG, htG _ (by decide) (by decide), hE.r11]
  rw [WP.block_append_iff, WP.block_cons_iff]
  refine ⟨VOp.exec .vzeroupper u, rfl, ?_⟩
  rw [WP.block_nil_iff]
  refine WP.mono (restoreEntry_ok (VOp.exec .vzeroupper u)
    (by change InRegions (u.rd ++ u.wr) (u.gpr .r11 + BitVec.ofNat 64 808) 8
        rw [huR, huW, htR, htW, hE.rd, hE.wr, ur11]
        exact in_rdwr (in_sub hp.p_in (off := 808) (by decide)))
    (by change InRegions (u.rd ++ u.wr) (u.gpr .r11 + BitVec.ofNat 64 800) 8
        rw [huR, huW, htR, htW, hE.rd, hE.wr, ur11]
        exact in_rdwr (in_sub hp.p_in (off := 800) (by decide))))
    fun v ⟨hv8, hvi, hvG, hvM, hvR, hvW⟩ => ?_
  change v.gpr .r8 = u.mem.readW (u.gpr .r11 + BitVec.ofNat 64 808) 64 at hv8
  change v.gpr .rsi = u.mem.readW (u.gpr .r11 + BitVec.ofNat 64 800) 64 at hvi
  change v.mem = u.mem at hvM
  refine ⟨?_, ?_, hvM ▸ fu, ?_, ?_, ?_⟩
  · rw [hvM]
    exact (blockAt_frame fyu (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hp.c_y)).trans ct
  · rw [hvM, huM, VG.Proof.Gcm.X86_64.blockAt_store]
  · intro r hax hdx h9 h10
    by_cases h8 : r = .r8
    · subst r
      rw [hv8, ur11, saved 808 (by decide)]; exact hE.data
    by_cases hi : r = .rsi
    · subst r
      rw [hvi, ur11, saved 800 (by decide)]; exact hE.rounds
    · rw [hvG r h8 hi]
      change u.gpr r = s₀.gpr r
      rw [huG, htG r hax h8]
      exact hE.other r hax hdx h8 h9 h10 hi
  · exact hvR.trans (huR.trans (htR.trans hE.rd))
  · exact hvW.trans (huW.trans (htW.trans hE.wr))

end VG.Proof.Gcm.X86_64.StitchAvx8
