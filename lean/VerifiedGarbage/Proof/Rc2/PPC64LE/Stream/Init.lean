module

public import VerifiedGarbage.Proof.Rc2.PPC64LE.Stream.Checks
public import VerifiedGarbage.Proof.Rc2.PPC64LE.KeyVerified
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import VerifiedGarbage.Proof.Rc2.Stream
import VerifiedGarbage.Proof.Rc2.Memory
import VerifiedGarbage.Proof.Rc2.CbcMemory
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Streaming RC2-CBC on PPC64LE: `init` -/

@[expose] public section

namespace VG.Proof.Rc2.PPC64LE.Stream

open VG VG.PPC64LE VG.Impl.Rc2.PPC64LE VG.Impl.Rc2.PPC64LE.Stream
open VG.Impl.Rc2.PPC64LE.Cbc (mov)

/-- `init`'s buffers: the key at `K` (`L` bytes), the IV at `V` (`N` bytes),
the context at `C` and the working space at `W`. -/
structure InitPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .r3, (s.gpr .r4).toNat⟩, ⟨s.gpr .r6, (s.gpr .r7).toNat⟩]
  wr : s.wr = [⟨s.gpr .r8, 144⟩, ⟨s.gpr .r9, 576⟩]
  kC : (⟨s.gpr .r3, (s.gpr .r4).toNat⟩ : Region).Disjoint ⟨s.gpr .r8, 144⟩
  kW : (⟨s.gpr .r3, (s.gpr .r4).toNat⟩ : Region).Disjoint ⟨s.gpr .r9, 576⟩
  vC : (⟨s.gpr .r6, (s.gpr .r7).toNat⟩ : Region).Disjoint ⟨s.gpr .r8, 144⟩
  vW : (⟨s.gpr .r6, (s.gpr .r7).toNat⟩ : Region).Disjoint ⟨s.gpr .r9, 576⟩
  CW : (⟨s.gpr .r8, 144⟩ : Region).Disjoint ⟨s.gpr .r9, 576⟩

theorem expandKey_noFrames : expandKey.noFrames = true := by decide +kernel

theorem initBody_wp (s : State) (h : InitPre s)
    (hv : valid (s.gpr .r4).toNat (s.gpr .r5).toNat (s.gpr .r7).toNat) :
    WP isa initBody s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.lr = s.lr ∧ s'.gpr .r3 = 0#64 ∧
      Spec.Rc2.scheduleAt s'.mem (s.gpr .r8) =
        Spec.Rc2.expandKey (Spec.Rc2.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat) (s.gpr .r5).toNat ∧
      Spec.Rc2.blockAt s'.mem (s.gpr .r8 + 128) = Spec.Rc2.blockAt s.mem (s.gpr .r6) := by
  obtain ⟨hk, hb, hi⟩ := hv
  obtain ⟨K, hK⟩ : ∃ K, s.gpr .r3 = K := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V, s.gpr .r6 = V := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, s.gpr .r8 = C := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, s.gpr .r9 = W := ⟨_, rfl⟩
  have hrd := h.rd; have hwr := h.wr; have kC := h.kC; have kW := h.kW; have vC := h.vC; have vW := h.vW
  have CW := h.CW
  simp only [hK, hV, hC, hW] at hrd hwr kC kW vC vW CW
  rw [hK, hC, hV]
  have inW : ∀ d, d + 8 ≤ 576 → InRegions s.wr (W + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [hwr]; exact ⟨⟨W, 576⟩, by simp, Offset.contains_base _ hd (by omega)⟩
  have inC : InRegions s.wr (C + 128) 8 := by
    rw [hwr]; exact ⟨⟨C, 144⟩, by simp, Offset.contains_base C (d := 128) (by omega) (by omega)⟩
  have inV : InRegions (s.rd ++ s.wr) V 8 := by
    rw [hrd]; exact ⟨⟨V, (s.gpr .r7).toNat⟩, by simp, by rw [hi]; exact Region.contains_self _ _⟩
  have cW : ∀ d, d + 8 ≤ 576 → (⟨W, 576⟩ : Region).Contains (W + BitVec.ofNat 64 d) 8 := fun d hd =>
    Offset.contains_base W hd (by omega)
  have W512 := inW 512 (by decide)
  have W520 := inW 520 (by decide)
  -- frames
  have slot512 : Region.Sub ⟨W + BitVec.ofNat 64 512, 8⟩ ⟨W, 576⟩ := Offset.sub_base W (by omega)
  have slot520 : Region.Sub ⟨W + BitVec.ofNat 64 520, 8⟩ ⟨W, 576⟩ := Offset.sub_base W (by omega)
  have ivC : Region.Sub ⟨C + 128, 8⟩ ⟨C, 144⟩ := Offset.sub_base C (d := 128) (by omega)
  unfold initBody withLr
  apply WP.seq
  refine WP.mono (WP.keep [.r0, .r25] (c := .block [.mflr .r0, .store .d .r0 .r9 512, .store .d .r25 .r9 520,
      mov .r25 .r9]) (Q := fun t => t.gpr .r25 = W ∧
      t.mem = (s.mem.writeW (W + BitVec.ofNat 64 512) s.lr).writeW (W + BitVec.ofNat 64 520) (s.gpr .r25))
    (by rrun [mov, hW, W512, W520]) (by simp [writesOnly, Code.allInstrs_eq, instrs, mov, dstOf]) rfl)
    fun t₁ ⟨⟨a₁, m₁⟩, k₁⟩ => ?_
  have F₁ : Frame [⟨W, 576⟩] s.mem t₁.mem := by
    rw [m₁]
    exact ((Frame.refl _ _).writeW (r := ⟨W, 576⟩) (by simp) _ (cW 512 (by decide))).writeW
      (r := ⟨W, 576⟩) (by simp) _ (cW 520 (by decide))
  have h6 : t₁.gpr .r6 = V := by rw [k₁.gpr (by decide), hV]
  have h8 : t₁.gpr .r8 = C := by rw [k₁.gpr (by decide), hC]
  have h9 : t₁.gpr .r9 = W := by rw [k₁.gpr (by decide), hW]
  have inV₁ : InRegions (t₁.rd ++ t₁.wr) V 8 := by rw [k₁.2.1, k₁.2.2]; exact inV
  have inC₁ : InRegions t₁.wr (C + 128#64) 8 := by rw [k₁.2.2]; exact inC
  apply WP.seq
  apply WP.seq
  refine WP.mono (WP.keep [.r6, .r7, .r10] (c := .block initArgs) (Q := fun t =>
      t.gpr .r6 = C ∧ t.gpr .r7 = W ∧ t.mem = t₁.mem.writeW (C + 128#64) (t₁.mem.readW V 64))
    (by unfold initArgs; rrun [mov, h6, h8, h9, inV₁, inC₁])
    (by simp [writesOnly, Code.allInstrs_eq, instrs, initArgs, mov, dstOf]) rfl) fun t₂ ⟨⟨a6, a7, m₂⟩, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  have h3 : t₂.gpr .r3 = K := by rw [k12.gpr (by decide), hK]
  have h4 : t₂.gpr .r4 = s.gpr .r4 := k12.gpr (by decide)
  have h5 : t₂.gpr .r5 = s.gpr .r5 := k12.gpr (by decide)
  have C128 : Region.Sub ⟨C, 128⟩ ⟨C, 144⟩ := Region.sub_prefix (by decide)
  have W512r : Region.Sub ⟨W, 512⟩ ⟨W, 576⟩ := Region.sub_prefix (by decide)
  apply WP.seq
  refine WP.call (k := keyC) expandKey_ok (rd := [⟨K, (s.gpr .r4).toNat⟩]) (wr := [⟨C, 128⟩, ⟨W, 512⟩]) ?_ ?_ ?_
    (fun t₃ rd₃ wr₃ _ F₃ P₃ _ post₃ => ?_) expandKey_noFrames
  · simp only [keyC, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr]
    rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide),
      State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), h3, h4, h5, a6, a7]
    exact ⟨rfl, rfl, kC.sub_right C128, kW.sub_right W512r, (CW.sub_left C128).sub_right W512r, hk.1, hk.2, hb.1, hb.2⟩
  · rw [k12.2.1, k12.2.2, hrd, hwr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨⟨C, 144⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨⟨W, 576⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  · rw [k12.2.2, hwr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨C, 144⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨⟨W, 576⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  -- after the call
  refine WP.mono (WP.keep [.r3] (c := .block [.li .r3 0]) (Q := fun t => t.gpr .r3 = 0#64 ∧ t.mem = t₃.mem)
    (by rrun) (by simp [writesOnly, Code.allInstrs_eq, instrs, dstOf]) rfl) fun t₄ ⟨⟨a3, m₄⟩, k₄⟩ => ?_
  have h31 : t₄.gpr .r25 = W := by rw [k₄.gpr (by decide), P₃ _ (by decide), k₂.gpr (by decide), a₁]
  have F₂ : Frame [⟨C, 144⟩, ⟨W, 576⟩] s.mem t₂.mem := by
    rw [m₂]
    exact (F₁.mono (by simp)).writeW (r := ⟨C, 144⟩) (by simp) _ (Offset.contains_base C (d := 128) (by omega) (by omega))
  -- the slots, apart from the context and the called function's working space
  have slot : ∀ d, 512 ≤ d → d + 8 ≤ 576 → t₄.mem.readW (W + BitVec.ofNat 64 d) 64 = t₁.mem.readW (W + BitVec.ofNat 64 d) 64 := by
    intro d hd hd'
    have sd : Region.Sub ⟨W + BitVec.ofNat 64 d, 8⟩ ⟨W, 576⟩ := Offset.sub_base W (by omega)
    rw [m₄, F₃.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact (CW.sub_left C128).symm.sub_left sd
      · exact Offset.disjoint_base W (by omega) (by omega)) (by decide), m₂,
      Mem.readW_writeW_sep (((CW.sub_left ivC).symm.sub_left sd).sep (Region.contains_self _ _)
        (Region.contains_self _ _)) (by decide)]
  have e512 : t₄.mem.readW (W + 512#64) 64 = s.lr := by
    rw [slot 512 (by decide) (by decide), m₁, Mem.readW_writeW_sep (Offset.sep W (by omega) (by omega) (by omega))
      (by decide), Mem.readW_writeW_self64]
  have e520 : t₄.mem.readW (W + 520#64) 64 = s.gpr .r25 := by
    rw [slot 520 (by decide) (by decide), m₁, Mem.readW_writeW_self64]
  have rw₄ : t₄.rd = s.rd ∧ t₄.wr = s.wr := ⟨by rw [k₄.2.1, rd₃, k12.2.1], by rw [k₄.2.2, wr₃, k12.2.2]⟩
  have in512 : InRegions (t₄.rd ++ t₄.wr) (W + 512#64) 8 := by
    rw [rw₄.1, rw₄.2]; obtain ⟨r, hr, hc⟩ := W512; exact ⟨r, List.mem_append_right _ hr, hc⟩
  have in520 : InRegions (t₄.rd ++ t₄.wr) (W + 520#64) 8 := by
    rw [rw₄.1, rw₄.2]; obtain ⟨r, hr, hc⟩ := W520; exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (WP.keep [.r0, .r25] (c := .block [.load .d .r0 .r25 512, .mtlr .r0, .load .d .r25 .r25 520])
      (Q := fun t => t.gpr .r25 = s.gpr .r25 ∧ t.lr = s.lr ∧ t.mem = t₄.mem)
    (by rrun [h31, e512, e520, in512, in520]) (by simp [writesOnly, Code.allInstrs_eq, instrs, dstOf]) rfl)
    fun t₅ ⟨⟨a31, lr₅, m₅⟩, k₅⟩ => ⟨fun r hr => ?_, lr₅, by rw [k₅.gpr (by decide), a3], ?_, ?_⟩
  · by_cases h31' : r = .r25
    · subst h31'; exact a31
    · have hn : r ∉ [Reg.r0, .r25, .r6, .r7, .r10] := by revert hr h31'; revert r; decide
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
      rw [k₅.gpr (by simp [hn]), k₄.gpr (by simp; intro e; subst e; revert hr; decide), P₃ r hr,
        k12.gpr (by simp [hn])]
  · have hB : Spec.Rc2.bytesAt t₂.mem K (s.gpr .r4).toNat = Spec.Rc2.bytesAt s.mem K (s.gpr .r4).toNat :=
      Proof.Rc2.bytesAt_frame F₂ K _ (by omega) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl)
        · exact kC
        · exact kW)
    have := post₃
    simp only [keyC, State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem] at this
    rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide),
      State.callEntry_gpr _ (by decide), a6, h3, h4, h5, hB] at this
    rw [m₅, m₄]; exact this
  · have hiv : Spec.Rc2.blockAt t₃.mem (C + 128#64) = Spec.Rc2.blockAt t₂.mem (C + 128#64) :=
      Proof.Rc2.blockAt_frame F₃ _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl)
        · exact Offset.disjoint_base C (d := 128) (by omega) (by omega)
        · exact (CW.sub_left ivC).sub_right W512r)
    have hV₁ : Spec.Rc2.blockAt t₁.mem V = Spec.Rc2.blockAt s.mem V :=
      Proof.Rc2.blockAt_frame F₁ V (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r rfl
        rw [← hi]; exact vW)
    show Spec.Rc2.blockAt t₅.mem (C + 128#64) = _
    rw [m₅, m₄, hiv, m₂, Proof.Rc2.blockAt_store64, ← Proof.Rc2.blockAt_read64, hV₁]

/-- `init`'s postcondition. -/
def initPost (s s' : State) : Prop :=
  ∀ direction, match Spec.Rc2.initWithEffectiveBits
      (Spec.Rc2.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat)
      (Spec.Rc2.bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat) direction (s.gpr .r5).toNat with
    | .ok c => BitVec.setWidth 32 (s'.gpr .r3) = 0 ∧ Spec.Rc2.contextAt s'.mem (s.gpr .r8) direction 0 = c
    | .error e => (BitVec.setWidth 32 (s'.gpr .r3)).toNat = e.code

theorem init_wp (s : State) (h : InitPre s) :
    WP isa init s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.lr = s.lr ∧ initPost s s' := by
  unfold init
  apply WP.seq
  refine WP.mono (WP.keepLr (checks_run s) (by decide) (by rw [← Code.allInstrs_eq]; decide))
    fun t₁ ⟨⟨m₁, k₁, c₁, e₁, v₁⟩, l₁⟩ => ?_
  have g : ∀ r, r ∉ [Reg.r3, .r10] → t₁.gpr r = s.gpr r := fun r hr => k₁.gpr hr
  have g4 := g .r4 (by decide); have g5 := g .r5 (by decide); have g6 := g .r6 (by decide)
  have g7 := g .r7 (by decide); have g8 := g .r8 (by decide); have g9 := g .r9 (by decide)
  refine WP.ite _ (by rw [eval_nonzero, c₁]) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hv : ¬valid (s.gpr .r4).toNat (s.gpr .r5).toNat (s.gpr .r7).toNat := by simpa using hb
    refine ⟨fun r hr => k₁.gpr (by revert hr; revert r; decide), l₁, ?_⟩
    refine Proof.Rc2.init_post_error ?_ hv
    rw [e₁ hv]
    unfold errCode
    split
    · rfl
    · split <;> rfl
  · have hv : valid (s.gpr .r4).toNat (s.gpr .r5).toNat (s.gpr .r7).toNat := by simpa using hb
    have g3 := v₁ hv
    have h' : InitPre t₁ := by
      obtain ⟨rd, wr, kC, kW, vC, vW, CW⟩ := h
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [k₁.2.1, k₁.2.2, g3, g4, g6, g7, g8, g9] <;> with_reducible assumption
    refine WP.mono (initBody_wp t₁ h' (by rw [g4, g5, g7]; exact hv)) fun s' ⟨P, L, r3, S, V⟩ =>
      ⟨fun r hr => by rw [P r hr, k₁.gpr (by revert hr; revert r; decide)], L.trans l₁, ?_⟩
    rw [g3, g4, g5, g8, m₁] at S
    rw [g6, g8, m₁] at V
    exact Proof.Rc2.init_post hv.1 hv.2.1 hv.2.2 (by rw [r3]; rfl) S V

end VG.Proof.Rc2.PPC64LE.Stream
