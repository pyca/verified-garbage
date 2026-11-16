module

public import VerifiedGarbage.Proof.Rc2.Contract
import VerifiedGarbage.Proof.Rc2.RISCV64.Cbc.Call
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.Rc2.RISCV64.Run
import VerifiedGarbage.Proof.Rc2.Memory
import VerifiedGarbage.Proof.Rc2.CbcMemory
import VerifiedGarbage.Proof.Rc2.CbcList
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Rc2.RISCV64.Cbc
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Framework.RISCV64.Inline
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Rc2.RISCV64.Cipher
import VerifiedGarbage.Proof.Rc2.RISCV64.Cbc.Io
import VerifiedGarbage.Proof.Framework.RISCV64.Loops

/-! ### `Rc2.RISCV64.Cbc.Step`, which only this module used -/

section

/-!
# RC2-CBC on RISCV64: one block

`body_run`: an iteration of the loop takes the invariant `Inv` from `j` blocks
done to `j + 1`.
-/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64.Cbc

open VG VG.RISCV64 VG.Impl.Rc2.RISCV64 VG.Impl.Rc2.RISCV64.Cbc

/-- The buffers: the schedule at `T`, the chaining value at `I`, `n` blocks
at `D` and the working space at `W`, apart, not wrapping around, the working
space aligned. -/
structure Regions (T I D W : Addr) (n : Nat) : Prop where
  TI : (⟨T, 128⟩ : Region).Disjoint ⟨I, 8⟩
  TD : (⟨T, 128⟩ : Region).Disjoint ⟨D, 8 * n⟩
  TW : (⟨T, 128⟩ : Region).Disjoint ⟨W, 512⟩
  ID : (⟨I, 8⟩ : Region).Disjoint ⟨D, 8 * n⟩
  IW : (⟨I, 8⟩ : Region).Disjoint ⟨W, 512⟩
  DW : (⟨D, 8 * n⟩ : Region).Disjoint ⟨W, 512⟩
  fit : D.toNat + 8 * n ≤ 2 ^ 64
  fitW : W.toNat + 512 ≤ 2 ^ 64
  al : W.toNat % 8 = 0

/-- After `j` of the `n` blocks, from memory `m₀` and with our caller's
registers `g`. -/
structure Inv (d : Spec.Rc2.Direction) (T I D W : Addr) (n : Nat) (g : Reg → BitVec 64) (m₀ : Mem)
    (s₀ : State) (j : Nat) (t : State) : Prop where
  rd : t.rd = [⟨T, 128⟩]
  wr : t.wr = [⟨I, 8⟩, ⟨D, 8 * n⟩, ⟨W, 512⟩]
  s1 : t.gpr .s1 = T
  s2 : t.gpr .s2 = I
  s3 : t.gpr .s3 = D + BitVec.ofNat 64 (8 * j)
  s4 : t.gpr .s4 = BitVec.ofNat 64 (n - j)
  s5 : t.gpr .s5 = W
  pres : ∀ r ∈ preserved, r ∉ saved.map Prod.fst → t.gpr r = s₀.gpr r
  saved : Spill.Saved W g saved t.mem
  sched : Spec.Rc2.scheduleAt t.mem T = Spec.Rc2.scheduleAt m₀ T
  done : Spec.Rc2.blocksAt t.mem D j =
    (Proof.Rc2.cbcBlocks (Spec.Rc2.scheduleAt m₀ T) d (Spec.Rc2.blockAt m₀ I) (Spec.Rc2.blocksAt m₀ D j)).1
  iv : Spec.Rc2.blockAt t.mem I =
    (Proof.Rc2.cbcBlocks (Spec.Rc2.scheduleAt m₀ T) d (Spec.Rc2.blockAt m₀ I) (Spec.Rc2.blocksAt m₀ D j)).2
  rest : ∀ i, j ≤ i → i < n → Spec.Rc2.blockAt t.mem (D + BitVec.ofNat 64 (8 * i)) =
    Spec.Rc2.blockAt m₀ (D + BitVec.ofNat 64 (8 * i))

theorem saved_fits : ∀ p ∈ saved, p.2 % 8 = 0 ∧ p.2 < 2048 := by decide
theorem saved_in : ∀ p ∈ saved, 256 ≤ p.2 ∧ p.2 + 8 ≤ 312 := by decide

/-- What a step leaves alone: anything apart from the block, the chaining
value and the block function's working space. -/
theorem step_frame {T I D W : Addr} {n j : Nat} (R : Regions T I D W n) (hj : j < n) {m m' : Mem}
    (F : Frame [⟨D + BitVec.ofNat 64 (8 * j), 8⟩, ⟨I, 8⟩, ⟨W, 256⟩] m m') :
    Spec.Rc2.scheduleAt m' T = Spec.Rc2.scheduleAt m T ∧
    (∀ g, Spill.Saved W g saved m → Spill.Saved W g saved m') ∧
    (∀ i, i < n → i ≠ j → Spec.Rc2.blockAt m' (D + BitVec.ofNat 64 (8 * i)) =
      Spec.Rc2.blockAt m (D + BitVec.ofNat 64 (8 * i))) ∧
    Spec.Rc2.blocksAt m' D j = Spec.Rc2.blocksAt m D j := by
  have hf := R.fit
  obtain bj : Region.Sub ⟨D + BitVec.ofNat 64 (8 * j), 8⟩ ⟨D, 8 * n⟩ := Offset.sub_base D (by omega_using [hj])
  obtain W256 : Region.Sub ⟨W, 256⟩ ⟨W, 512⟩ := Region.sub_prefix (by decide)
  refine ⟨Proof.Rc2.scheduleAt_frame F T ?_, fun g sv => sv.frame F ?_, fun i hi hne => Proof.Rc2.blockAt_frame F _ ?_,
    Proof.Rc2.blocksAt_frame F D j ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact R.TD.sub_right bj
    · exact R.TI
    · exact R.TW.sub_right W256
  · intro p hp r hr
    obtain hb := saved_in p hp
    obtain slot : Region.Sub ⟨W + BitVec.ofNat 64 p.2, 8⟩ ⟨W, 512⟩ := Offset.sub_base W (by omega_using [hb])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (R.DW.sub_left bj).symm.sub_left slot
    · exact (R.IW.symm.sub_left slot)
    · exact Offset.disjoint_base W (by omega_using [hb]) (by omega_using [hb])
  · have bi : Region.Sub ⟨D + BitVec.ofNat 64 (8 * i), 8⟩ ⟨D, 8 * n⟩ := Offset.sub_base D (by omega_using [hi])
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact Offset.disjoint D (by omega_using [hne]) (by omega_using [hf, hi]) (by omega_using [hj, hf])
    · exact (R.ID.sub_right bi).symm
    · exact (R.DW.sub_left bi).sub_right W256
  · have bp : Region.Sub ⟨D, 8 * j⟩ ⟨D, 8 * n⟩ := Region.sub_prefix (by omega_using [hj])
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact Offset.base_disjoint D (by omega_using []) (by omega_using [hj, hf])
    · exact (R.ID.sub_right bp).symm
    · exact (R.DW.sub_left bp).sub_right W256

theorem blocksAt_one (m : Mem) (p : Addr) : Spec.Rc2.blocksAt m p 1 = [Spec.Rc2.blockAt m p] := by
  simp [Spec.Rc2.blocksAt]

/-- The done blocks, one more. -/
theorem done_succ (m : Mem) (D : Addr) (j : Nat) :
    Spec.Rc2.blocksAt m D (j + 1) = Spec.Rc2.blocksAt m D j ++ [Spec.Rc2.blockAt m (D + BitVec.ofNat 64 (8 * j))] := by
  rw [Proof.Rc2.blocksAt_add, blocksAt_one]

theorem covers {T I D W : Addr} {n j : Nat} (hj : j < n) :
    Covers ([⟨T, 128⟩] ++ [⟨D + BitVec.ofNat 64 (8 * j), 8⟩, ⟨W, 256⟩])
      ([⟨T, 128⟩] ++ [⟨I, 8⟩, ⟨D, 8 * n⟩, ⟨W, 512⟩]) := by
  refine Covers.of_sub fun r hr => ?_
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  · exact ⟨⟨D, 8 * n⟩, by simp, 8 * j, rfl, by simp; omega_using [hj]⟩
  · exact ⟨⟨W, 512⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩

theorem covers_wr {I D W : Addr} {n j : Nat} (hj : j < n) :
    Covers [⟨D + BitVec.ofNat 64 (8 * j), 8⟩, ⟨W, 256⟩] [⟨I, 8⟩, ⟨D, 8 * n⟩, ⟨W, 512⟩] := by
  refine Covers.of_sub fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨⟨D, 8 * n⟩, by simp, 8 * j, rfl, by simp; omega_using [hj]⟩
  · exact ⟨⟨W, 512⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩

end VG.Proof.Rc2.RISCV64.Cbc

end

end


/-! # RC2-CBC on RISCV64: an iteration of the loop -/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64.Cbc

open VG VG.RISCV64 VG.Impl.Rc2.RISCV64 VG.Impl.Rc2.RISCV64.Cbc

theorem count_sub {n j : Nat} (hj : j < n) :
    BitVec.ofNat 64 (n - j) - 1#64 = BitVec.ofNat 64 (n - (j + 1)) := by
  rw [Offset.ofNat_sub_ofNat (by omega_using [hj])]; congr 1

theorem preserved_not : ∀ r ∈ preserved, r ∉ saved.map Prod.fst →
    r ∉ [Reg.t0, .a7, .t1, .t2, .a0, .a1, .a2, .s3, .s4, .s6] := by decide

theorem enc_spec (k : Spec.Rc2.Schedule) (iv b : Spec.Rc2.Block) :
    Proof.Rc2.cbcBlocks k .encrypt iv [b] =
      ([Spec.Rc2.encryptBlock k (Proof.Rc2.xorBlock b iv)], Spec.Rc2.encryptBlock k (Proof.Rc2.xorBlock b iv)) := rfl

theorem dec_spec (k : Spec.Rc2.Schedule) (iv b : Spec.Rc2.Block) :
    Proof.Rc2.cbcBlocks k .decrypt iv [b] = ([Proof.Rc2.xorBlock (Spec.Rc2.decryptBlock k b) iv], b) := rfl

theorem body_run (d : Spec.Rc2.Direction) {T I D W : Addr} {n : Nat} {g : Reg → BitVec 64} {m₀ : Mem} {s₀ : State}
    (R : Regions T I D W n) {j : Nat} (hj : j < n) (t : State) (H : Inv d T I D W n g m₀ s₀ j t) :
    WP isa (body d) t fun t' => Inv d T I D W n g m₀ s₀ (j + 1) t' ∧
      (t'.gpr .s4 != (0 : BitVec 64)) = !decide (j + 1 = n) := by
  have hf := R.fit
  let p := D + BitVec.ofNat 64 (8 * j)
  obtain pIn : InRegions t.wr p 8 := by
    rw [H.wr]; exact ⟨⟨D, 8 * n⟩, by simp, Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj, hf])⟩
  obtain pIn' : InRegions (t.rd ++ t.wr) p 8 := by
    obtain ⟨r, hr, hc⟩ := pIn; exact ⟨r, List.mem_append_right _ hr, hc⟩
  obtain iIn : InRegions t.wr I 8 := by rw [H.wr]; exact ⟨⟨I, 8⟩, by simp, Region.contains_self _ _⟩
  obtain iIn' : InRegions (t.rd ++ t.wr) I 8 := by
    obtain ⟨r, hr, hc⟩ := iIn; exact ⟨r, List.mem_append_right _ hr, hc⟩
  obtain bj : Region.Sub ⟨p, 8⟩ ⟨D, 8 * n⟩ := Offset.sub_base D (by omega_using [hj])
  obtain pI : (⟨p, 8⟩ : Region).Disjoint ⟨I, 8⟩ := (R.ID.sub_right bj).symm
  have r28 : t.gpr .s3 = p := H.s3
  obtain b₀ : Spec.Rc2.blockAt t.mem p = Spec.Rc2.blockAt m₀ p := H.rest j (Nat.le_refl _) hj
  obtain hpt : p.toNat = D.toNat + 8 * j := by
    simp only [p, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show 8 * j < 2 ^ 64 by omega_using [hj, hf]), Nat.mod_eq_of_lt (by omega_using [hj, hf])]
  obtain W256 : Region.Sub ⟨W, 256⟩ ⟨W, 512⟩ := Region.sub_prefix (by decide)
  have hfw := R.fitW
  obtain spec := Proof.Rc2.cbc_append (Spec.Rc2.scheduleAt m₀ T) d (Spec.Rc2.blockAt m₀ I)
    (Spec.Rc2.blocksAt m₀ D j) [Spec.Rc2.blockAt m₀ p]
  unfold body
  cases d with
  | encrypt =>
    apply WP.seq
    refine WP.mono (beforeEnc_run t H.s1 H.s2 r28 H.s5 pIn' pIn iIn')
      fun t₁ ⟨a3, a4, a5, m₁, k₁⟩ => ?_
    apply WP.seq
    refine WP.mono (call_run .encrypt t₁ a3 a4 a5 R.al (by omega_using [hj, hf, hpt]) (by omega_using [hfw]) (R.TW.sub_right W256)
      ((R.DW.sub_left bj).sub_right W256) (by rw [k₁.2.1, k₁.2.2, H.rd, H.wr]; exact covers hj)
      (by rw [k₁.2.2, H.wr]; exact covers_wr hj)) fun t₂ ⟨rd₂, wr₂, F₂, P₂, c₂⟩ => ?_
    obtain g2 : ∀ r, r ∈ preserved → r ∉ [Reg.t0, .a7, .t1, .t2, .a0, .a1, .a2] → t₂.gpr r = t.gpr r := fun r hr hn => by
      rw [P₂ r hr, k₁.gpr hn]
    obtain h27 : t₂.gpr .s2 = I := by rw [g2 _ (by decide) (by decide), H.s2]
    obtain h28 : t₂.gpr .s3 = p := by rw [g2 _ (by decide) (by decide), H.s3]
    obtain h29 : t₂.gpr .s4 = BitVec.ofNat 64 (n - j) := by rw [g2 _ (by decide) (by decide), H.s4]
    obtain pIn₂ : InRegions (t₂.rd ++ t₂.wr) p 8 := by rw [rd₂, wr₂, k₁.2.1, k₁.2.2]; exact pIn'
    obtain iIn₂ : InRegions t₂.wr I 8 := by rw [wr₂, k₁.2.2]; exact iIn
    refine WP.mono (afterEnc_run t₂ h27 h28 h29 pIn₂ iIn₂) fun t₃ ⟨a28, a29, m₃, k₃⟩ => ?_
    -- the frame of the whole step
    obtain F : Frame [⟨p, 8⟩, ⟨I, 8⟩, ⟨W, 256⟩] t.mem t₃.mem := by
      refine Frame.trans (Frame.trans ?_ (F₂.mono (by simp))) ?_
      · rw [m₁]; exact (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
      · rw [m₃]; exact (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)
    obtain ⟨fS, fV, fB, fD⟩ := step_frame R hj F
    -- the new block and chaining value
    obtain out : Spec.Rc2.blockAt t₂.mem p =
        Spec.Rc2.encryptBlock (Spec.Rc2.scheduleAt m₀ T) (Proof.Rc2.xorBlock (Spec.Rc2.blockAt m₀ p)
          (Spec.Rc2.blockAt t.mem I)) := by
      obtain hs₁ : Spec.Rc2.scheduleAt t₁.mem T = Spec.Rc2.scheduleAt m₀ T := by
        rw [m₁, Proof.Rc2.scheduleAt_frame (Proof.Rc2.frame_store64 _ _ _) T (by simpa using R.TD.sub_right bj),
          H.sched]
      rw [c₂, hs₁, m₁, Proof.Rc2.blockAt_xor, b₀]; rfl
    obtain b₃ : Spec.Rc2.blockAt t₃.mem p = Spec.Rc2.blockAt t₂.mem p := by
      rw [m₃]; exact Proof.Rc2.blockAt_frame (Proof.Rc2.frame_store64 _ _ _) _ (by simpa using pI)
    obtain i₃ : Spec.Rc2.blockAt t₃.mem I = Spec.Rc2.blockAt t₂.mem p := by rw [m₃, Proof.Rc2.blockAt_copy]
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
    · rw [fB i hn (by omega_using [hi]), H.rest i (by omega_using [hi]) hn]
    · rw [a29, count_sub hj, ofNat_bne_zero' (by omega_using [hf])]
      congr 1
      exact decide_eq_decide.mpr (by omega_using [hj])
  | decrypt =>
    apply WP.seq
    refine WP.mono (beforeDec_run t H.s1 r28 H.s5 pIn') fun t₁ ⟨a3, a4, a5, a31, m₁, k₁⟩ => ?_
    apply WP.seq
    refine WP.mono (call_run .decrypt t₁ a3 a4 a5 R.al (by omega_using [hj, hf, hpt]) (by omega_using [hfw]) (R.TW.sub_right W256)
      ((R.DW.sub_left bj).sub_right W256) (by rw [k₁.2.1, k₁.2.2, H.rd, H.wr]; exact covers hj)
      (by rw [k₁.2.2, H.wr]; exact covers_wr hj)) fun t₂ ⟨rd₂, wr₂, F₂, P₂, c₂⟩ => ?_
    obtain g2 : ∀ r, r ∈ preserved → r ∉ [Reg.s6, .a7, .t1, .a0, .a1, .a2] → t₂.gpr r = t.gpr r := fun r hr hn => by
      rw [P₂ r hr, k₁.gpr hn]
    obtain h27 : t₂.gpr .s2 = I := by rw [g2 _ (by decide) (by decide), H.s2]
    obtain h28 : t₂.gpr .s3 = p := by rw [g2 _ (by decide) (by decide), H.s3]
    obtain h29 : t₂.gpr .s4 = BitVec.ofNat 64 (n - j) := by rw [g2 _ (by decide) (by decide), H.s4]
    obtain h31 : t₂.gpr .s6 = t.mem.readW p 64 := by rw [P₂ _ (by decide), a31]
    obtain pIn₂ : InRegions (t₂.rd ++ t₂.wr) p 8 := by rw [rd₂, wr₂, k₁.2.1, k₁.2.2]; exact pIn'
    obtain pW₂ : InRegions t₂.wr p 8 := by rw [wr₂, k₁.2.2]; exact pIn
    obtain iIn₂ : InRegions t₂.wr I 8 := by rw [wr₂, k₁.2.2]; exact iIn
    obtain iIn₂' : InRegions (t₂.rd ++ t₂.wr) I 8 := by rw [rd₂, wr₂, k₁.2.1, k₁.2.2]; exact iIn'
    refine WP.mono (afterDec_run t₂ h27 h28 h29 h31 pIn₂ pW₂ iIn₂' iIn₂) fun t₃ ⟨a28, a29, m₃, k₃⟩ => ?_
    obtain F : Frame [⟨p, 8⟩, ⟨I, 8⟩, ⟨W, 256⟩] t.mem t₃.mem := by
      rw [← m₁]
      refine Frame.trans (F₂.mono (by simp)) ?_
      rw [m₃]
      obtain f₁ : Frame [⟨p, 8⟩, ⟨I, 8⟩, ⟨W, 256⟩] t₂.mem
          (t₂.mem.writeW p (t₂.mem.readW p 64 ^^^ t₂.mem.readW I 64)) :=
        (Frame.refl _ _).writeW (r := ⟨p, 8⟩) (by simp) _ (Region.contains_self _ _)
      exact f₁.writeW (r := ⟨I, 8⟩) (by simp) _ (Region.contains_self _ _)
    obtain ⟨fS, fV, fB, fD⟩ := step_frame R hj F
    obtain i₂ : Spec.Rc2.blockAt t₂.mem I = Spec.Rc2.blockAt t.mem I := by
      rw [Proof.Rc2.blockAt_frame F₂ I (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl)
        · exact pI.symm
        · exact R.IW.sub_right (Region.sub_prefix (by decide))), m₁]
    obtain hs₁ : Spec.Rc2.scheduleAt t₁.mem T = Spec.Rc2.scheduleAt m₀ T := by rw [m₁, H.sched]
    obtain b₃ : Spec.Rc2.blockAt t₃.mem p =
        Proof.Rc2.xorBlock (Spec.Rc2.decryptBlock (Spec.Rc2.scheduleAt m₀ T) (Spec.Rc2.blockAt m₀ p))
          (Spec.Rc2.blockAt t.mem I) := by
      rw [m₃, Proof.Rc2.blockAt_frame (Proof.Rc2.frame_store64 _ _ _) _ (by simpa using pI),
        Proof.Rc2.blockAt_xor, i₂, c₂, hs₁, m₁, b₀]; rfl
    obtain i₃ : Spec.Rc2.blockAt t₃.mem I = Spec.Rc2.blockAt m₀ p := by
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
    · rw [fB i hn (by omega_using [hi]), H.rest i (by omega_using [hi]) hn]
    · rw [a29, count_sub hj, ofNat_bne_zero' (by omega_using [hf])]
      congr 1
      exact decide_eq_decide.mpr (by omega_using [hj])

end VG.Proof.Rc2.RISCV64.Cbc
