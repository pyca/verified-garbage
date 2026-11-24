module

public import VerifiedGarbage.Proof.Gcm.RISCV64.Prepared.Finish
public import VerifiedGarbage.Proof.Gcm.RISCV64.Lit
public import VerifiedGarbage.Proof.Framework.RISCV64.Lit

/-! # The RISC-V prepared GHASH update meets its arithmetic and ABI obligations -/

@[expose] public section
namespace VG.Proof.Gcm.RISCV64
open VG.Impl.Gcm.RISCV64.Prepared
open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Gcm.RISCV64
open VG.WriteBytes
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom)


def hashDone (H : Block) (s t : State) : Prop := blockAt t.mem (s.gpr .a1) =
    ghashFrom H (blockAt s.mem (s.gpr .a1)) (blocksAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
theorem preparedHash_ok {H : Block} (s : State) (hp : CachedPre H s) (hsp : 112 ≤ s.sp.toNat) :
    WP isa cachedHash s fun s' => hashDone H s s' ∧ ∀ r ∈ savedRegs, s'.gpr r = s.gpr r := by

  refine WP.ite _ (eval_zero s N) (fun h0 => WP.block_nil ⟨?_, fun _ _ => rfl⟩) (fun h0 => ?_)
  · have hn : (s.gpr .a3).toNat = 0 := by
      have := beq_iff_eq.mp h0; simp [N] at this; simp [this]
    show blockAt s.mem (s.gpr .a1) = _
    rw [hn]; rfl
  obtain hpos : 0 < (s.gpr .a3).toNat := by
    have := beq_eq_false_iff_ne.mp h0
    refine Nat.pos_of_ne_zero fun h => this ?_
    exact BitVec.eq_of_toNat_eq (by simpa [N] using h)
  refine WP.allocLe ⟨by decide, by decide, by decide⟩ hsp ?_
  unfold cachedBody
  refine WP.seq (WP.mono (cached_head_ok s hp) fun sY hH => ?_)
  refine WP.seq (WP.mono (split_loop hH.loop (s.gpr .a3).isLt hpos hH.inv) fun sL hBL => ?_)
  have hfp := hH.spill
  obtain hslot : ∀ p ∈ compactSaved, sL.mem.readW ((allocd 112 s).sp + BitVec.ofNat 64 p.2) 64 = s.gpr p.1 := by
    intro p hp
    obtain hd : 32 ≤ p.2 ∧ p.2 + 8 ≤ 112 := by
      simp only [compactSaved, saved, slot, List.map, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    obtain c : (⟨(allocd 112 s).sp + BitVec.ofNat 64 p.2, 8⟩ : Region).Contains
        ((allocd 112 s).sp + BitVec.ofNat 64 p.2) 8 := Region.contains_self _ _
    have := hH.slots p hp
    simp only [Mem.readW] at this ⊢
    rw [Frame.read hBL.frame c (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      rw [hfp]; simpa using slot_disj (allocd 112 s).sp (d:=p.2) (e:=0) (n:=32) (by omega_using [hd]) (by omega_using [hd])) (by decide)]
    exact this
  obtain hyp : sL.gpr YP = s.gpr .a1 := by rw [Keep.gpr hBL.keep (by decide), hH.yp]
  obtain hwrL : sL.wr = (allocd 112 s).wr := by rw [hBL.keep.2.2, hH.wr]
  obtain hspL : sL.sp = (allocd 112 s).sp := by rw [hBL.sp, hH.sp]
  obtain T := cached_tail_ok s hp sL hBL.y hyp hwrL hspL hslot
  refine WP.mono T fun t h mL _ fl => ?_
  refine ⟨?_, fun r hr => h.2.1 r hr⟩
  have h1 := h.1
  simp only [hashDone] at h1 ⊢
  -- The `free` loses the frame's bytes, which lie apart from `Y`.
  exact Eq.trans (Proof.Gcm.blockAt_congr fun i hi =>
    lost_byte fl (R := ⟨s.gpr .a1, 16⟩) hp.stackY.symm hi) h1


theorem preparedHash_law {H : Block} (s : State) (hp : CachedPre H s) (hsp : 112 ≤ s.sp.toNat) :
    ∃ tr t, Exec isa cachedHash s tr t ∧ abiPreserved s t ∧ hashDone H s t := by
  obtain ⟨tr,t,hx,⟨post,hsv⟩,hkeep⟩ := WP.keep (.a0 :: written) (preparedHash_ok s hp hsp) (by lit_decide) (by lit_decide)
  refine ⟨tr,t,hx,⟨fun r hr => ?_,Exec.sp hx,hkeep.gpr (by decide)⟩,post⟩
  by_cases h : r ∈ saved.map Prod.fst
  · exact hsv r h
  · exact hkeep.gpr (by revert hr h; revert r; decide)
end VG.Proof.Gcm.RISCV64
