module
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Finish

import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Last
import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Finish
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.LoopRounds
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.AddrArith

@[expose] public section

namespace VG.Proof.ChaCha20.AArch64.Mixed8
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed8
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.ChaCha20 (serialize block)

variable {sve : Bool}

abbrev lastR (s : State) : Region := ⟨s.gpr .x1 + BitVec.ofNat 64 384,128⟩

/-- After a chunk: its 512 bytes of the source (at `r` on entry) XORed with
the keystream of its eight blocks into the destination (at `x1`). -/
structure ChunkedFrom (r : Reg) (s₀ s : State) : Prop where
  x0 : s.gpr .x0 = s₀.gpr .x0
  x1 : s.gpr .x1 = s₀.gpr .x1
  x2 : s.gpr .x2 = s₀.gpr .x2
  x3 : s.gpr .x3 = s₀.gpr .x3
  cs : ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x26 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  cnt : source s = source s₀
  data : ∀ k < 512, s.mem (s₀.gpr .x1 + BitVec.ofNat 64 k) =
    s₀.mem (s₀.gpr r + BitVec.ofNat 64 k) ^^^
      (serialize (block (ctr (source s₀) (k / 64)))).getD (k % 64) 0
  frame : Frame [sr s₀,scalarBuf s₀,dr s₀] s₀.mem s.mem

theorem lastFrom_ok (r : Reg) {s₀ s : State} (hp : CP s₀) (hsr : SrcOK r s₀) (h : FinishedFrom r s₀ s) :
    WP isa (.block ((List.finRange 8).flatMap (xorScalarRowFrom r))) s (ChunkedFrom r s₀) := by
  have hr : s.gpr r = s₀.gpr r := by
    rcases hsr.reg with rfl | rfl
    · exact h.x1
    · exact h.cs _ (by simp [preserved]) (by decide) (by decide)
  have hi : ∀ k : Fin 8, InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 (16 * k.val)) 16 := by
    intro k
    rw [h.rd,h.wr,h.x3]
    obtain ⟨r,hr,hc⟩ := hp.buffer (16 * k.val) 16 (by omega)
    exact ⟨r,List.mem_append_right _ hr,hc⟩
  have hs : ∀ k : Fin 8, InRegions (s.rd ++ s.wr) (s.gpr r + BitVec.ofNat 64 (384 + 16 * k.val)) 16 := by
    intro k; rw [h.rd,h.wr,hr]; exact hsr.src _ _ (by omega)
  have ho : ∀ k : Fin 8, InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 (384 + 16 * k.val)) 16 := by
    intro k; rw [h.wr,h.x1]; exact hp.data _ _ (by omega)
  have hdis : (scalarBuf s₀).Disjoint (lastR s₀) :=
    (hp.d_b.symm.sub_left (Region.sub_prefix (by decide : 128 ≤ 320))).sub_right
      (Offset.sub_base _ (by decide : 384 + 128 ≤ 512))
  have hsl : Region.Sub ⟨s₀.gpr r + BitVec.ofNat 64 384,128⟩ ⟨s₀.gpr r,512⟩ :=
    Offset.sub_base _ (by decide : 384 + 128 ≤ 512)
  have halias : s₀.gpr r + BitVec.ofNat 64 384 = (lastR s₀).base ∨
      (⟨s₀.gpr r + BitVec.ofNat 64 384,128⟩ : Region).Disjoint ⟨(lastR s₀).base,128⟩ := by
    rcases hsr.alias with he | hd
    · exact .inl (by rw [he])
    · exact .inr ((hd.sub_left hsl).sub_right (Offset.sub_base _ (by decide : 384 + 128 ≤ 512)))
  refine (xorScalarListFrom_ok r (List.finRange 8) (List.nodup_finRange 8)
    (VG.Proof.ChaCha20.AArch64.Neon4.DataTo.nil s.mem (s₀.gpr r + BitVec.ofNat 64 384)
      (lastR s₀).base 128 _)
    (by rw [hr]) (by rw [h.x1]) h.x3 hdis halias
    (fun _ _ => List.not_mem_nil) hi hs ho).mono fun u ⟨hu,hs⟩ => ?_
  have hf : Frame [lastR s₀] s.mem u.mem := data_frame128 hu
  have hst : (sr s₀).Disjoint (lastR s₀) :=
    hp.st_d.sub_right (Offset.sub_base _ (by decide : 384 + 128 ≤ 512))
  refine ⟨(congrFun hs.gpr _).trans h.x0,(congrFun hs.gpr _).trans h.x1,
    (congrFun hs.gpr _).trans h.x2,(congrFun hs.gpr _).trans h.x3,?_,
    hs.rd.trans h.rd,hs.wr.trans h.wr,hs.sp.trans h.sp,?_,?_,?_⟩
  · intro r hr h19 h26; rw [hs.gpr]; exact h.cs r hr h19 h26
  · rw [source,hs.gpr,h.x0,VG.Proof.ChaCha20.AArch64.Xor.stateAt_frame hf (by
      intro r hr; have he := List.mem_singleton.mp hr; subst r; exact hst)]
    rw [← h.x0]; exact h.cnt
  · intro k hk
    by_cases hk' : k < 384
    · rw [hf.bytes (R := firstR s₀) (by
        intro r hr; have he := List.mem_singleton.mp hr; subst r
        exact Offset.base_disjoint _ (by decide : 384 ≤ 384) (by decide : 384 + 128 ≤ 2 ^ 64))
        (by decide : 384 ≤ 2 ^ 64) hk',h.data k hk']
    · have htail : k - 384 < 128 := by omega
      have he : (lastR s₀).base + BitVec.ofNat 64 (k - 384) = s₀.gpr .x1 + BitVec.ofNat 64 k := by
        dsimp [lastR]; rw [BitVec.add_assoc,← BitVec.ofNat_add,show 384 + (k - 384) = k by omega]
      have hes : s₀.gpr r + BitVec.ofNat 64 384 + BitVec.ofNat 64 (k - 384) =
          s₀.gpr r + BitVec.ofNat 64 k := by
        rw [BitVec.add_assoc,← BitVec.ofNat_add,show 384 + (k - 384) = k by omega]
      have hm := hu ((lastR s₀).base + BitVec.ofNat 64 (k - 384))
      rw [VG.Offset.add_sub_cancel_left,BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : k - 384 < 2 ^ 64)] at hm
      have hslot : (k - 384) / 16 ∈ (List.finRange 8).map Fin.val ++ [] := by
        apply List.mem_append_left
        exact List.mem_map_of_mem (f := Fin.val)
          (List.mem_finRange (⟨(k - 384) / 16,by omega⟩ : Fin 8))
      rw [ite_eq_left ⟨hslot,by omega⟩,he,hes] at hm
      dsimp only at hm
      have hbuf := h.buf (⟨(k - 384) / 16,by omega⟩ : Fin 8)
      rw [hbuf,
        VG.Proof.ChaCha20.AArch64.Rows6.output_byte] at hm
      have hplain : s.mem (s₀.gpr r + BitVec.ofNat 64 k) = s₀.mem (s₀.gpr r + BitVec.ofNat 64 k) := by
        have hp' := h.frame.bytes (R := ⟨s₀.gpr r + BitVec.ofNat 64 384,128⟩) (by
          intro q hq
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
          rcases hq with rfl | rfl | rfl
          · exact (hsr.st_s.sub_right hsl).symm
          · exact (hsr.s_b.sub_left hsl).sub_right (Region.sub_prefix (by decide : 128 ≤ 320))
          · rcases hsr.alias with he' | hd
            · rw [he']; exact Offset.disjoint_base _ (by decide : 384 ≤ 384) (by decide : 384 + 128 ≤ 2 ^ 64)
            · exact (hd.sub_left hsl).sub_right (Region.sub_prefix (by decide : 384 ≤ 512)))
          (by decide : 128 ≤ 2 ^ 64) htail
        rwa [hes] at hp'
      rw [hplain,show 6 + (k - 384) / 64 = k / 64 by omega,
        show (k - 384) % 64 = k % 64 by omega] at hm
      exact hm
  · have hpre : Frame [sr s₀,scalarBuf s₀,dr s₀] s₀.mem s.mem := h.frame.sub (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨sr s₀,by simp,fun _ h => h⟩
      · exact ⟨scalarBuf s₀,by simp,fun _ h => h⟩
      · exact ⟨dr s₀,by simp,Region.sub_prefix (by decide : 384 ≤ 512)⟩)
    exact hpre.trans (hf.sub (by
      intro r hr; have he := List.mem_singleton.mp hr; subst r
      exact ⟨dr s₀,by simp,Offset.sub_base _ (by decide : 384 + 128 ≤ 512)⟩))

theorem chunkFrom_ok (r : Reg) (s : State) (hp : CP s) (hs : SrcOK r s) :
    WP isa (chunkFrom sve r) s (ChunkedFrom r s) := by
  apply WP.seq
  refine (prepare_ok s hp).mono fun a ha => ?_
  apply WP.seq
  have first : WP isa (phase sve .x26) a fun b => Prepared s b 5 := by
    refine (counted_phase_ok ha.vec ha.scalar ha.table
      (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide)) (by decide)
      ((ha.keep _ VG.Proof.ChaCha20.AArch64.not_words_x1 (by decide) (by decide)).trans ha.saved.data.symm)).mono fun b ⟨hv,hc,hsp,ht⟩ => ?_
    refine ⟨hv,ht,hc.holds,?_,?_,?_,hc.rd.trans ha.rd,hc.wr.trans ha.wr,hsp.trans ha.sp,?_⟩
    · rw [source,hc.mem,hc.keep _ VG.Proof.ChaCha20.AArch64.not_words_x0]; exact ha.cnt
    · exact ⟨by rw [hc.keep _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide))]; exact ha.saved.len,
        by rw [hc.keep _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide))]; exact ha.saved.data⟩
    · intro r hr h19 h26; rw [hc.keep r hr]; exact ha.keep r hr h19 h26
    · rw [hc.mem]; exact ha.frame
  refine first.mono fun b hb => ?_
  apply WP.seq
  refine (second_ok hp hb).mono fun c hc => ?_
  apply WP.seq
  refine (compute_second_ok hp hc).mono fun d hd => ?_
  apply WP.seq
  refine (spill2_ok hp hd).mono fun e he => ?_
  apply WP.seq
  exact (finishFrom_ok r hp hs he).mono fun f hf => lastFrom_ok r hp hs hf

end VG.Proof.ChaCha20.AArch64.Mixed8
