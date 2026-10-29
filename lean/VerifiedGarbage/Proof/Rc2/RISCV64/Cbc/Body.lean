module

public import VerifiedGarbage.Proof.Rc2.RISCV64.Cbc.Step
import VerifiedGarbage.Proof.Rc2.RISCV64.Run
import VerifiedGarbage.Proof.Rc2.Memory
import VerifiedGarbage.Proof.Rc2.CbcMemory
import VerifiedGarbage.Proof.Rc2.CbcList
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Rc2.RISCV64.Cbc.Call
import VerifiedGarbage.Proof.Rc2.RISCV64.Cipher
import VerifiedGarbage.Proof.Rc2.RISCV64.Cbc.Io
import VerifiedGarbage.Proof.Framework.RISCV64.Loops
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep

/-! # RC2-CBC on RISCV64: an iteration of the loop -/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64.Cbc

open VG VG.RISCV64 VG.Impl.Rc2.RISCV64 VG.Impl.Rc2.RISCV64.Cbc

theorem count_sub {n j : Nat} (hj : j < n) :
    BitVec.ofNat 64 (n - j) - 1#64 = BitVec.ofNat 64 (n - (j + 1)) := by
  rw [Offset.ofNat_sub_ofNat (by omega)]; congr 1

theorem preserved_not : ∀ r ∈ preserved, r ∉ saved.map Prod.fst →
    r ∉ [Reg.t0, .a7, .t1, .t2, .a0, .a1, .a2, .s3, .s4, .s6] := by decide

theorem enc_spec (k : Spec.Rc2.Schedule) (iv b : Spec.Rc2.Block) :
    Spec.Rc2.cbc k .encrypt iv [b] =
      ([Spec.Rc2.encryptBlock k (Spec.Rc2.xorBlock b iv)], Spec.Rc2.encryptBlock k (Spec.Rc2.xorBlock b iv)) := rfl

theorem dec_spec (k : Spec.Rc2.Schedule) (iv b : Spec.Rc2.Block) :
    Spec.Rc2.cbc k .decrypt iv [b] = ([Spec.Rc2.xorBlock (Spec.Rc2.decryptBlock k b) iv], b) := rfl

theorem body_run (d : Spec.Rc2.Direction) {T I D W : Addr} {n : Nat} {g : Reg → BitVec 64} {m₀ : Mem} {s₀ : State}
    (R : Regions T I D W n) {j : Nat} (hj : j < n) (t : State) (H : Inv d T I D W n g m₀ s₀ j t) :
    WP isa (body d) t fun t' => Inv d T I D W n g m₀ s₀ (j + 1) t' ∧
      (t'.gpr .s4 != (0 : BitVec 64)) = !decide (j + 1 = n) := by
  have hf := R.fit
  let p := D + BitVec.ofNat 64 (8 * j)
  have pIn : InRegions t.wr p 8 := by
    rw [H.wr]; exact ⟨⟨D, 8 * n⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have pIn' : InRegions (t.rd ++ t.wr) p 8 := by
    obtain ⟨r, hr, hc⟩ := pIn; exact ⟨r, List.mem_append_right _ hr, hc⟩
  have iIn : InRegions t.wr I 8 := by rw [H.wr]; exact ⟨⟨I, 8⟩, by simp, Region.contains_self _ _⟩
  have iIn' : InRegions (t.rd ++ t.wr) I 8 := by
    obtain ⟨r, hr, hc⟩ := iIn; exact ⟨r, List.mem_append_right _ hr, hc⟩
  have bj : Region.Sub ⟨p, 8⟩ ⟨D, 8 * n⟩ := Offset.sub_base D (by omega)
  have pI : (⟨p, 8⟩ : Region).Disjoint ⟨I, 8⟩ := (R.ID.sub_right bj).symm
  have r28 : t.gpr .s3 = p := H.s3
  have b₀ : Spec.Rc2.blockAt t.mem p = Spec.Rc2.blockAt m₀ p := H.rest j (Nat.le_refl _) hj
  have hpt : p.toNat = D.toNat + 8 * j := by
    simp only [p, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show 8 * j < 2 ^ 64 by omega), Nat.mod_eq_of_lt (by omega)]
  have W256 : Region.Sub ⟨W, 256⟩ ⟨W, 512⟩ := Region.sub_prefix (by decide)
  have hfw := R.fitW
  have spec := Proof.Rc2.cbc_append (Spec.Rc2.scheduleAt m₀ T) d (Spec.Rc2.blockAt m₀ I)
    (Spec.Rc2.blocksAt m₀ D j) [Spec.Rc2.blockAt m₀ p]
  unfold body
  cases d with
  | encrypt =>
    apply WP.seq
    refine WP.mono (beforeEnc_run t H.s1 H.s2 r28 H.s5 pIn' pIn iIn')
      fun t₁ ⟨a3, a4, a5, m₁, k₁⟩ => ?_
    apply WP.seq
    refine WP.mono (call_run .encrypt t₁ a3 a4 a5 R.al (by omega) (by omega) (R.TW.sub_right W256)
      ((R.DW.sub_left bj).sub_right W256) (by rw [k₁.2.1, k₁.2.2, H.rd, H.wr]; exact covers hj)
      (by rw [k₁.2.2, H.wr]; exact covers_wr hj)) fun t₂ ⟨rd₂, wr₂, F₂, P₂, c₂⟩ => ?_
    have g2 : ∀ r, r ∈ preserved → r ∉ [Reg.t0, .a7, .t1, .t2, .a0, .a1, .a2] → t₂.gpr r = t.gpr r := fun r hr hn => by
      rw [P₂ r hr, k₁.gpr hn]
    have h27 : t₂.gpr .s2 = I := by rw [g2 _ (by decide) (by decide), H.s2]
    have h28 : t₂.gpr .s3 = p := by rw [g2 _ (by decide) (by decide), H.s3]
    have h29 : t₂.gpr .s4 = BitVec.ofNat 64 (n - j) := by rw [g2 _ (by decide) (by decide), H.s4]
    have pIn₂ : InRegions (t₂.rd ++ t₂.wr) p 8 := by rw [rd₂, wr₂, k₁.2.1, k₁.2.2]; exact pIn'
    have iIn₂ : InRegions t₂.wr I 8 := by rw [wr₂, k₁.2.2]; exact iIn
    refine WP.mono (afterEnc_run t₂ h27 h28 h29 pIn₂ iIn₂) fun t₃ ⟨a28, a29, m₃, k₃⟩ => ?_
    -- the frame of the whole step
    have F : Frame [⟨p, 8⟩, ⟨I, 8⟩, ⟨W, 256⟩] t.mem t₃.mem := by
      refine Frame.trans (Frame.trans ?_ (F₂.mono (by simp))) ?_
      · rw [m₁]; exact (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
      · rw [m₃]; exact (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)
    obtain ⟨fS, fV, fB, fD⟩ := step_frame R hj F
    -- the new block and chaining value
    have out : Spec.Rc2.blockAt t₂.mem p =
        Spec.Rc2.encryptBlock (Spec.Rc2.scheduleAt m₀ T) (Spec.Rc2.xorBlock (Spec.Rc2.blockAt m₀ p)
          (Spec.Rc2.blockAt t.mem I)) := by
      have hs₁ : Spec.Rc2.scheduleAt t₁.mem T = Spec.Rc2.scheduleAt m₀ T := by
        rw [m₁, Proof.Rc2.scheduleAt_frame (Proof.Rc2.frame_store64 _ _ _) T (by simpa using R.TD.sub_right bj),
          H.sched]
      rw [c₂, hs₁, m₁, Proof.Rc2.blockAt_xor, b₀]; rfl
    have b₃ : Spec.Rc2.blockAt t₃.mem p = Spec.Rc2.blockAt t₂.mem p := by
      rw [m₃]; exact Proof.Rc2.blockAt_frame (Proof.Rc2.frame_store64 _ _ _) _ (by simpa using pI)
    have i₃ : Spec.Rc2.blockAt t₃.mem I = Spec.Rc2.blockAt t₂.mem p := by rw [m₃, Proof.Rc2.blockAt_copy]
    refine ⟨⟨by rw [k₃.2.1, rd₂, k₁.2.1, H.rd], by rw [k₃.2.2, wr₂, k₁.2.2, H.wr],
      by rw [k₃.gpr (by decide), g2 _ (by decide) (by decide), H.s1], by rw [k₃.gpr (by decide), h27],
      by rw [a28, Offset.add_add]; congr 2,
      by rw [a29, count_sub hj], by rw [k₃.gpr (by decide), g2 _ (by decide) (by decide), H.s5],
      fun r hr hn => ?_, fV g H.saved, by rw [fS, H.sched], ?_, ?_, fun i hi hn => ?_⟩, ?_⟩
    · have hn' := preserved_not r hr hn
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn'
      rw [k₃.gpr (by simp [hn']), g2 r hr (by simp [hn']), H.pres r hr hn]
    · rw [done_succ, done_succ, fD, H.done, spec, enc_spec, ← H.iv, b₃, out]
    · rw [done_succ, spec, enc_spec, ← H.iv, i₃, out]
    · rw [fB i hn (by omega), H.rest i (by omega) hn]
    · rw [a29, count_sub hj, ofNat_bne_zero' (by omega)]
      congr 1
      exact decide_eq_decide.mpr (by omega)
  | decrypt =>
    apply WP.seq
    refine WP.mono (beforeDec_run t H.s1 r28 H.s5 pIn') fun t₁ ⟨a3, a4, a5, a31, m₁, k₁⟩ => ?_
    apply WP.seq
    refine WP.mono (call_run .decrypt t₁ a3 a4 a5 R.al (by omega) (by omega) (R.TW.sub_right W256)
      ((R.DW.sub_left bj).sub_right W256) (by rw [k₁.2.1, k₁.2.2, H.rd, H.wr]; exact covers hj)
      (by rw [k₁.2.2, H.wr]; exact covers_wr hj)) fun t₂ ⟨rd₂, wr₂, F₂, P₂, c₂⟩ => ?_
    have g2 : ∀ r, r ∈ preserved → r ∉ [Reg.s6, .a7, .t1, .a0, .a1, .a2] → t₂.gpr r = t.gpr r := fun r hr hn => by
      rw [P₂ r hr, k₁.gpr hn]
    have h27 : t₂.gpr .s2 = I := by rw [g2 _ (by decide) (by decide), H.s2]
    have h28 : t₂.gpr .s3 = p := by rw [g2 _ (by decide) (by decide), H.s3]
    have h29 : t₂.gpr .s4 = BitVec.ofNat 64 (n - j) := by rw [g2 _ (by decide) (by decide), H.s4]
    have h31 : t₂.gpr .s6 = t.mem.readW p 64 := by rw [P₂ _ (by decide), a31]
    have pIn₂ : InRegions (t₂.rd ++ t₂.wr) p 8 := by rw [rd₂, wr₂, k₁.2.1, k₁.2.2]; exact pIn'
    have pW₂ : InRegions t₂.wr p 8 := by rw [wr₂, k₁.2.2]; exact pIn
    have iIn₂ : InRegions t₂.wr I 8 := by rw [wr₂, k₁.2.2]; exact iIn
    have iIn₂' : InRegions (t₂.rd ++ t₂.wr) I 8 := by rw [rd₂, wr₂, k₁.2.1, k₁.2.2]; exact iIn'
    refine WP.mono (afterDec_run t₂ h27 h28 h29 h31 pIn₂ pW₂ iIn₂' iIn₂) fun t₃ ⟨a28, a29, m₃, k₃⟩ => ?_
    have F : Frame [⟨p, 8⟩, ⟨I, 8⟩, ⟨W, 256⟩] t.mem t₃.mem := by
      rw [← m₁]
      refine Frame.trans (F₂.mono (by simp)) ?_
      rw [m₃]
      have f₁ : Frame [⟨p, 8⟩, ⟨I, 8⟩, ⟨W, 256⟩] t₂.mem
          (t₂.mem.writeW p (t₂.mem.readW p 64 ^^^ t₂.mem.readW I 64)) :=
        (Frame.refl _ _).writeW (r := ⟨p, 8⟩) (by simp) _ (Region.contains_self _ _)
      exact f₁.writeW (r := ⟨I, 8⟩) (by simp) _ (Region.contains_self _ _)
    obtain ⟨fS, fV, fB, fD⟩ := step_frame R hj F
    have i₂ : Spec.Rc2.blockAt t₂.mem I = Spec.Rc2.blockAt t.mem I := by
      rw [Proof.Rc2.blockAt_frame F₂ I (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl)
        · exact pI.symm
        · exact R.IW.sub_right (Region.sub_prefix (by decide))), m₁]
    have hs₁ : Spec.Rc2.scheduleAt t₁.mem T = Spec.Rc2.scheduleAt m₀ T := by rw [m₁, H.sched]
    have b₃ : Spec.Rc2.blockAt t₃.mem p =
        Spec.Rc2.xorBlock (Spec.Rc2.decryptBlock (Spec.Rc2.scheduleAt m₀ T) (Spec.Rc2.blockAt m₀ p))
          (Spec.Rc2.blockAt t.mem I) := by
      rw [m₃, Proof.Rc2.blockAt_frame (Proof.Rc2.frame_store64 _ _ _) _ (by simpa using pI),
        Proof.Rc2.blockAt_xor, i₂, c₂, hs₁, m₁, b₀]; rfl
    have i₃ : Spec.Rc2.blockAt t₃.mem I = Spec.Rc2.blockAt m₀ p := by
      rw [m₃, Proof.Rc2.blockAt_store64, ← Proof.Rc2.blockAt_read64, b₀]
    refine ⟨⟨by rw [k₃.2.1, rd₂, k₁.2.1, H.rd], by rw [k₃.2.2, wr₂, k₁.2.2, H.wr],
      by rw [k₃.gpr (by decide), g2 _ (by decide) (by decide), H.s1], by rw [k₃.gpr (by decide), h27],
      by rw [a28, Offset.add_add]; congr 2,
      by rw [a29, count_sub hj], by rw [k₃.gpr (by decide), g2 _ (by decide) (by decide), H.s5],
      fun r hr hn => ?_, fV g H.saved, by rw [fS, H.sched], ?_, ?_, fun i hi hn => ?_⟩, ?_⟩
    · have hn' := preserved_not r hr hn
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn'
      rw [k₃.gpr (by simp [hn']), g2 r hr (by simp [hn']), H.pres r hr hn]
    · rw [done_succ, done_succ, fD, H.done, spec, dec_spec, ← H.iv, b₃]
    · rw [done_succ, spec, dec_spec, i₃]
    · rw [fB i hn (by omega), H.rest i (by omega) hn]
    · rw [a29, count_sub hj, ofNat_bne_zero' (by omega)]
      congr 1
      exact decide_eq_decide.mpr (by omega)

end VG.Proof.Rc2.RISCV64.Cbc
