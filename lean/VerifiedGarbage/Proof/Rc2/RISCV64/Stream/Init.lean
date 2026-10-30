module

public import VerifiedGarbage.Proof.Rc2.RISCV64.Stream.Checks
public import VerifiedGarbage.Proof.Rc2.RISCV64.KeyVerified
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
import VerifiedGarbage.Proof.Rc2.Stream
import VerifiedGarbage.Proof.Rc2.Memory
import VerifiedGarbage.Proof.Rc2.CbcMemory
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Rc2.RISCV64.Cbc.Io
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Rc2.RISCV64.Lit

/-! # Streaming RC2-CBC on RISCV64: `init` -/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64.Stream

open VG VG.RISCV64 VG.Impl.Rc2.RISCV64 VG.Impl.Rc2.RISCV64.Stream
open VG.Impl.Rc2.RISCV64.Cbc (mov)

/-- `init`'s buffers: the key at `K` (`L` bytes), the IV at `V` (`N` bytes),
the context at `C` and the working space at `W`. -/
structure InitPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .a0, (s.gpr .a1).toNat⟩, ⟨s.gpr .a3, (s.gpr .a4).toNat⟩]
  wr : s.wr = [⟨s.gpr .a5, 144⟩, ⟨s.gpr .a6, 576⟩]
  al : (s.gpr .a6).toNat % 8 = 0
  kC : (⟨s.gpr .a0, (s.gpr .a1).toNat⟩ : Region).Disjoint ⟨s.gpr .a5, 144⟩
  kW : (⟨s.gpr .a0, (s.gpr .a1).toNat⟩ : Region).Disjoint ⟨s.gpr .a6, 576⟩
  vC : (⟨s.gpr .a3, (s.gpr .a4).toNat⟩ : Region).Disjoint ⟨s.gpr .a5, 144⟩
  vW : (⟨s.gpr .a3, (s.gpr .a4).toNat⟩ : Region).Disjoint ⟨s.gpr .a6, 576⟩
  CW : (⟨s.gpr .a5, 144⟩ : Region).Disjoint ⟨s.gpr .a6, 576⟩

theorem expandKey_noFrames : expandKey.noFrames = true := by lit_decide

theorem initArgs_run (t₁ : State) {V C W : Addr} (h6 : t₁.gpr .a3 = V) (h8 : t₁.gpr .a5 = C)
    (h9 : t₁.gpr .a6 = W) (inV₁ : InRegions (t₁.rd ++ t₁.wr) V 8) (inC₁ : InRegions t₁.wr (C + 128#64) 8) :
    WP isa (.block initArgs) t₁ fun t => t.gpr .a3 = C ∧ t.gpr .a4 = W ∧
      t.mem = t₁.mem.writeW (C + 128#64) (t₁.mem.readW V 64) ∧ Keep [.t0, .a7, .t1, .t2, .a3, .a4] t₁ t := by
  unfold initArgs
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (Cbc.load64_run (d := .t0) (n := .a3) (p := V) (by decide) (by decide) (by decide) (by decide)
    (by decide) t₁ h6 inV₁) fun u₁ ⟨v₁, mu₁, ku₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.t2] (c := .block [.addi .t2 .a5 128]) (Q := fun u => u.gpr .t2 = C + 128#64 ∧
      u.mem = u₁.mem) (by rrun [ku₁.gpr (show Reg.a5 ∉ [Reg.t0, .a7, .t1] by decide), h8]) (by rfl) rfl)
    fun u₂ ⟨⟨v₂, mu₂⟩, ku₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (Cbc.store64_run (v := .t0) (n := .t2) (p := C + 128#64) (by decide) (by decide) (by decide) u₂ v₂
    (by rw [ku₂.2.2, ku₁.2.2]; exact inC₁)) fun u₃ ⟨mu₃, ku₃⟩ => ?_
  have k₃ := (ku₁.trans ku₂).trans ku₃
  have g5 : u₃.gpr .a5 = C := by rw [k₃.gpr (by decide), h8]
  have g6 : u₃.gpr .a6 = W := by rw [k₃.gpr (by decide), h9]
  refine WP.mono (WP.keep [.a3, .a4] (c := .block [mov .a3 .a5, mov .a4 .a6]) (Q := fun t => t.gpr .a3 = C ∧
      t.gpr .a4 = W ∧ t.mem = u₃.mem) (by rrun [mov, g5, g6]) (by rfl) rfl) fun t ⟨⟨a, b, m⟩, k⟩ =>
      ⟨a, b, ?_, (k₃.trans k).mono (by simp)⟩
  rw [m, mu₃, ku₂.gpr (by decide), v₁, mu₂, mu₁]

theorem initBody_wp (s : State) (h : InitPre s)
    (hv : valid (s.gpr .a1).toNat (s.gpr .a2).toNat (s.gpr .a4).toNat) :
    WP isa initBody s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.gpr .ra = s.gpr .ra ∧
      s'.gpr .a0 = 0#64 ∧
      Spec.Rc2.scheduleAt s'.mem (s.gpr .a5) =
        Spec.Rc2.expandKey (Spec.Rc2.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) (s.gpr .a2).toNat ∧
      Spec.Rc2.blockAt s'.mem (s.gpr .a5 + 128) = Spec.Rc2.blockAt s.mem (s.gpr .a3) := by
  obtain ⟨hk, hb, hi⟩ := hv
  obtain ⟨K, hK⟩ : ∃ K, s.gpr .a0 = K := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V, s.gpr .a3 = V := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, s.gpr .a5 = C := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, s.gpr .a6 = W := ⟨_, rfl⟩
  have hrd := h.rd; have hwr := h.wr; have kC := h.kC; have kW := h.kW; have vC := h.vC; have vW := h.vW
  have CW := h.CW; have hal := h.al
  simp only [hK, hV, hC, hW] at hrd hwr kC kW vC vW CW hal
  rw [hK, hC, hV]
  have inW : ∀ d, d + 8 ≤ 576 → InRegions s.wr (W + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [hwr]; exact ⟨⟨W, 576⟩, by simp, Offset.contains_base _ hd (by omega_arith)⟩
  have inC : InRegions s.wr (C + 128) 8 := by
    rw [hwr]; exact ⟨⟨C, 144⟩, by simp, Offset.contains_base C (d := 128) (by omega_arith) (by omega_arith)⟩
  have inV : InRegions (s.rd ++ s.wr) V 8 := by
    rw [hrd]; exact ⟨⟨V, (s.gpr .a4).toNat⟩, by simp, by rw [hi]; exact Region.contains_self _ _⟩
  have cW : ∀ d, d + 8 ≤ 576 → (⟨W, 576⟩ : Region).Contains (W + BitVec.ofNat 64 d) 8 := fun d hd =>
    Offset.contains_base W hd (by omega_arith)
  have W512 := inW 512 (by decide)
  have W520 := inW 520 (by decide)
  -- frames
  have slot512 : Region.Sub ⟨W + BitVec.ofNat 64 512, 8⟩ ⟨W, 576⟩ := Offset.sub_base W (by omega_arith)
  have slot520 : Region.Sub ⟨W + BitVec.ofNat 64 520, 8⟩ ⟨W, 576⟩ := Offset.sub_base W (by omega_arith)
  have ivC : Region.Sub ⟨C + 128, 8⟩ ⟨C, 144⟩ := Offset.sub_base C (d := 128) (by omega_arith)
  have al512 := Spill.al8 hal (d := 512) (by decide)
  have al520 := Spill.al8 hal (d := 520) (by decide)
  unfold initBody withRa
  apply WP.seq
  refine WP.mono (WP.keep [.s7] (c := .block [.store .d .ra .a6 512, .store .d .s7 .a6 520, mov .s7 .a6])
      (Q := fun t => t.gpr .s7 = W ∧
      t.mem = (s.mem.writeW (W + BitVec.ofNat 64 512) (s.gpr .ra)).writeW (W + BitVec.ofNat 64 520) (s.gpr .s7))
    (by rrun [mov, hW, W512, W520, al512, al520]) (by rfl) rfl)
    fun t₁ ⟨⟨a₁, m₁⟩, k₁⟩ => ?_
  have F₁ : Frame [⟨W, 576⟩] s.mem t₁.mem := by
    rw [m₁]
    exact ((Frame.refl _ _).writeW (r := ⟨W, 576⟩) (by simp) _ (cW 512 (by decide))).writeW
      (r := ⟨W, 576⟩) (by simp) _ (cW 520 (by decide))
  have h6 : t₁.gpr .a3 = V := by rw [k₁.gpr (by decide), hV]
  have h8 : t₁.gpr .a5 = C := by rw [k₁.gpr (by decide), hC]
  have h9 : t₁.gpr .a6 = W := by rw [k₁.gpr (by decide), hW]
  have inV₁ : InRegions (t₁.rd ++ t₁.wr) V 8 := by rw [k₁.2.1, k₁.2.2]; exact inV
  have inC₁ : InRegions t₁.wr (C + 128#64) 8 := by rw [k₁.2.2]; exact inC
  apply WP.seq
  apply WP.seq
  refine WP.mono (initArgs_run t₁ h6 h8 h9 inV₁ inC₁) fun t₂ ⟨a6, a7, m₂, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  have h3 : t₂.gpr .a0 = K := by rw [k12.gpr (by decide), hK]
  have h4 : t₂.gpr .a1 = s.gpr .a1 := k12.gpr (by decide)
  have h5 : t₂.gpr .a2 = s.gpr .a2 := k12.gpr (by decide)
  have C128 : Region.Sub ⟨C, 128⟩ ⟨C, 144⟩ := Region.sub_prefix (by decide)
  have W512r : Region.Sub ⟨W, 512⟩ ⟨W, 576⟩ := Region.sub_prefix (by decide)
  apply WP.seq
  refine WP.call (k := keyC) (expandKey_ok (by lit_decide) (by lit_decide)) (rd := [⟨K, (s.gpr .a1).toNat⟩]) (wr := [⟨C, 128⟩, ⟨W, 512⟩]) ?_ ?_ ?_
    (fun t₃ rd₃ wr₃ _ F₃ P₃ _ post₃ => ?_) expandKey_noFrames
  · simp only [keyC, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr]
    rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide),
      State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), h3, h4, h5, a6, a7]
    exact ⟨rfl, rfl, hal, kC.sub_right C128, kW.sub_right W512r, (CW.sub_left C128).sub_right W512r, hk.1, hk.2,
      hb.1, hb.2⟩
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
  refine WP.mono (WP.keep [.a0] (c := .block [.li .a0 0]) (Q := fun t => t.gpr .a0 = 0#64 ∧ t.mem = t₃.mem)
    (by rrun) (by rfl) rfl) fun t₄ ⟨⟨a3, m₄⟩, k₄⟩ => ?_
  have h31 : t₄.gpr .s7 = W := by rw [k₄.gpr (by decide), P₃ _ (by decide), k₂.gpr (by decide), a₁]
  have F₂ : Frame [⟨C, 144⟩, ⟨W, 576⟩] s.mem t₂.mem := by
    rw [m₂]
    exact (F₁.mono (by simp)).writeW (r := ⟨C, 144⟩) (by simp) _ (Offset.contains_base C (d := 128) (by omega_arith) (by omega_arith))
  -- the slots, apart from the context and the called function's working space
  have slot : ∀ d, 512 ≤ d → d + 8 ≤ 576 → t₄.mem.readW (W + BitVec.ofNat 64 d) 64 = t₁.mem.readW (W + BitVec.ofNat 64 d) 64 := by
    intro d hd hd'
    have sd : Region.Sub ⟨W + BitVec.ofNat 64 d, 8⟩ ⟨W, 576⟩ := Offset.sub_base W (by omega_arith)
    rw [m₄, F₃.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact (CW.sub_left C128).symm.sub_left sd
      · exact Offset.disjoint_base W (by omega_arith) (by omega_arith)) (by decide), m₂,
      Mem.readW_writeW_sep (((CW.sub_left ivC).symm.sub_left sd).sep (Region.contains_self _ _)
        (Region.contains_self _ _)) (by decide)]
  have e512 : t₄.mem.readW (W + 512#64) 64 = s.gpr .ra := by
    rw [slot 512 (by decide) (by decide), m₁, Mem.readW_writeW_sep (Offset.sep W (by omega_arith) (by omega_arith) (by omega_arith))
      (by decide), Mem.readW_writeW_self64]
  have e520 : t₄.mem.readW (W + 520#64) 64 = s.gpr .s7 := by
    rw [slot 520 (by decide) (by decide), m₁, Mem.readW_writeW_self64]
  have rw₄ : t₄.rd = s.rd ∧ t₄.wr = s.wr := ⟨by rw [k₄.2.1, rd₃, k12.2.1], by rw [k₄.2.2, wr₃, k12.2.2]⟩
  have in512 : InRegions (t₄.rd ++ t₄.wr) (W + 512#64) 8 := by
    rw [rw₄.1, rw₄.2]; obtain ⟨r, hr, hc⟩ := W512; exact ⟨r, List.mem_append_right _ hr, hc⟩
  have in520 : InRegions (t₄.rd ++ t₄.wr) (W + 520#64) 8 := by
    rw [rw₄.1, rw₄.2]; obtain ⟨r, hr, hc⟩ := W520; exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (WP.keep [.ra, .s7] (c := .block [.load .d .ra .s7 512, .load .d .s7 .s7 520])
      (Q := fun t => t.gpr .s7 = s.gpr .s7 ∧ t.gpr .ra = s.gpr .ra ∧ t.mem = t₄.mem)
    (by rrun [h31, e512, e520, in512, in520, al512, al520]) (by rfl) rfl)
    fun t₅ ⟨⟨a31, lr₅, m₅⟩, k₅⟩ => ⟨fun r hr => ?_, lr₅, by rw [k₅.gpr (by decide), a3], ?_, ?_⟩
  · by_cases h31' : r = .s7
    · subst h31'; exact a31
    · have hn : r ∉ [Reg.ra, .s7, .t0, .a7, .t1, .t2, .a3, .a4] := by revert hr h31'; revert r; decide
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
      rw [k₅.gpr (by simp [hn]), k₄.gpr (by simp; intro e; subst e; revert hr; decide), P₃ r hr,
        k12.gpr (by simp [hn])]
  · have hB : Spec.Rc2.bytesAt t₂.mem K (s.gpr .a1).toNat = Spec.Rc2.bytesAt s.mem K (s.gpr .a1).toNat :=
      Proof.Rc2.bytesAt_frame F₂ K _ (by omega_arith) (by
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
        · exact Offset.disjoint_base C (d := 128) (by omega_arith) (by omega_arith)
        · exact (CW.sub_left ivC).sub_right W512r)
    have hV₁ : Spec.Rc2.blockAt t₁.mem V = Spec.Rc2.blockAt s.mem V :=
      Proof.Rc2.blockAt_frame F₁ V (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r rfl
        rw [← hi]; exact vW)
    show Spec.Rc2.blockAt t₅.mem (C + 128#64) = _
    rw [m₅, m₄, hiv, m₂, Proof.Rc2.blockAt_store64, ← Proof.Rc2.blockAt_read64, hV₁]

/-- `init`'s postcondition. -/
noncomputable def initPost (s s' : State) : Prop :=
  ∀ direction, match Spec.Rc2.initWithEffectiveBits
      (Spec.Rc2.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat)
      (Spec.Rc2.bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat) direction (s.gpr .a2).toNat with
    | .ok c => BitVec.setWidth 32 (s'.gpr .a0) = 0 ∧ Spec.Rc2.contextAt s'.mem (s.gpr .a5) direction 0 = c
    | .error e => (BitVec.setWidth 32 (s'.gpr .a0)).toNat = e.code

theorem init_wp (s : State) (h : InitPre s) :
    WP isa init s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.gpr .ra = s.gpr .ra ∧
      initPost s s' := by
  unfold init
  apply WP.seq
  refine WP.mono (checks_run s) fun t₁ ⟨m₁, k₁, c₁, e₁, v₁⟩ => ?_
  have g : ∀ r, r ∉ [Reg.a0, .t0] → t₁.gpr r = s.gpr r := fun r hr => k₁.gpr hr
  have g4 := g .a1 (by decide); have g5 := g .a2 (by decide); have g6 := g .a3 (by decide)
  have g7 := g .a4 (by decide); have g8 := g .a5 (by decide); have g9 := g .a6 (by decide)
  refine WP.ite _ (by rw [Steps.eval_nonzero, c₁]) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hv : ¬valid (s.gpr .a1).toNat (s.gpr .a2).toNat (s.gpr .a4).toNat := by simpa using hb
    refine ⟨fun r hr => k₁.gpr (by revert hr; revert r; decide), k₁.gpr (by decide), ?_⟩
    refine Proof.Rc2.init_post_error ?_ hv
    rw [e₁ hv]
    unfold errCode
    split
    · rfl
    · split <;> rfl
  · have hv : valid (s.gpr .a1).toNat (s.gpr .a2).toNat (s.gpr .a4).toNat := by simpa using hb
    have g3 := v₁ hv
    have h' : InitPre t₁ := by
      obtain ⟨rd, wr, al, kC, kW, vC, vW, CW⟩ := h
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [k₁.2.1, k₁.2.2, g3, g4, g6, g7, g8, g9] <;>
        with_reducible assumption
    refine WP.mono (initBody_wp t₁ h' (by rw [g4, g5, g7]; exact hv)) fun s' ⟨P, L, r3, S, V⟩ =>
      ⟨fun r hr => by rw [P r hr, k₁.gpr (by revert hr; revert r; decide)], by rw [L, k₁.gpr (by decide)], ?_⟩
    rw [g3, g4, g5, g8, m₁] at S
    rw [g6, g8, m₁] at V
    exact Proof.Rc2.init_post hv.1 hv.2.1 hv.2.2 (by rw [r3]; rfl) S V

end VG.Proof.Rc2.RISCV64.Stream
