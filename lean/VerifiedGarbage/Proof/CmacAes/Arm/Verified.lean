import VerifiedGarbage.Proof.CmacAes.Arm.UpdateCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Cmac.Contract
import VerifiedGarbage.Proof.CmacAes.Arm.Finalize
import VerifiedGarbage.Proof.CmacAes.Arm.Subkeys

section

/-!
# AES-CMAC on ARMv7: `vg_cmac_aes_subkeys` is constant time

The code before the call and after it is checked by the taint analysis, from
the registers the correctness proof pins (the arguments, then `r5` and `r6`);
the call of `vg_aes_ctr32`, in its frame, is constant time by its own proof
(`ctr_rel`).
-/

namespace VG.Proof.CmacAes.Arm

open VG VG.Arm VG.Impl.CmacAes.Arm

/-- What is known after the call. -/
structure SPost (s₀ : State) (s : State) : Prop where
  r5 : s.gpr .r5 = Sc s₀
  r6 : s.gpr .r6 = Kb s₀

theorem spost_wp {s₀ s : State} (h : SAfter s₀ s) : WP isa (ctrCall .r4 .r5) s (SPost s₀) :=
  WP.mono (ctr_call h.pre) fun _ hc =>
    ⟨by rw [hc.saved .r5 (by simp [preserved]) (by decide), h.r5],
      by rw [hc.saved .r6 (by simp [preserved]) (by decide), h.r6]⟩

theorem subkeys_rel {s₀ s₀' : State} (h0 : subkeysArm.pre s₀) (h0' : subkeysArm.pre s₀')
    (hq : subkeysArm.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') subkeys fun _ _ => True := by
  obtain ⟨q₀, q₁, q₂, q₃, q₄⟩ := hq
  have hp := SPre.of h0
  have hp' := SPre.of h0'
  have eW : W s₀' = W s₀ := q₁.symm
  have eR : R s₀' = R s₀ := by rw [R, R, q₂]
  have eK : Kb s₀' = Kb s₀ := q₃.symm
  have eS : Sc s₀' = Sc s₀ := q₄.symm
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.r0, .r1, .r2, .r3]) (.block subkeysPre) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r5, .r6]) (.block subkeysPost) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := SAfter s₀) (G' := SAfter s₀')
    (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun s s' e e' => by
      subst e e'
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption) ⟨_, hA⟩
    (fun s e => by rw [e]; exact pre_wp hp) (fun s e => by rw [e]; exact pre_wp hp')
  have c := rel_wp (F := SAfter s₀) (F' := SAfter s₀') (G := SPost s₀) (G' := SPost s₀')
    (ctr_rel (sp₀ := s₀.sp) fun s₁ s₂ h =>
      ⟨h.1.pre, by have := h.2.pre; rwa [eW, eS, eK, eR] at this, h.1.sp, h.2.sp.trans q₀.symm⟩)
    (fun _ h => spost_wp h) (fun _ h => spost_wp h)
  have b := RelCT.taint (A := taint) (P := fun s₁ s₂ => SPost s₀ s₁ ∧ SPost s₀' s₂) (Taint.ofRegs [.r5, .r6])
    (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.r5, h.2.r5, eS]
      · rw [h.1.r6, h.2.r6, eK]) hB
  exact a.seq (c.seq b)

theorem subkeys_ct : ConstantTime isa subkeysArm.pre subkeysArm.pub subkeys :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (subkeys_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.Arm

end

section

section

/-!
# AES-CMAC on ARMv7: `vg_cmac_aes_finalize` is correct

Before the call, the counter block holds `Mₙ ⊕ C`, for the last block `Mₙ` of
§6.2 step 4 and the chaining value `C` at `state`, and the state is zeroed;
the call leaves `CIPH_K(C ⊕ Mₙ)` there (`finalize_raw_wp`, whatever the
32 bytes after the key schedule hold, as AES-SIV's key context needs), and
that is the MAC when they are the subkeys of its cipher (`finalize_wp`,
`Cmac.macFull_split`).
-/

namespace VG.Proof.CmacAes.Arm

open VG VG.Arm VG.Impl.CmacAes.Arm
open VG.Proof.MdStream.Arm (Upd Mupd op2_imm op2_reg wp_mov wp_add wp_ldr eval_eq)

/-! ## Up to the call -/

/-- What the code before the call leaves. -/
structure FMid (s₀ s : State) : Prop where
  pre : CallPre s (W s₀) (S s₀ + BitVec.ofNat 32 2048) (St s₀) (S s₀) (R s₀) .r4 .r5
  blk : Spec.Aes.bytesAt s.mem (Ca s₀) 16 =
    Spec.Cmac.xor (mn s₀) (Spec.Aes.bytesAt s₀.mem (State.addr (St s₀)) 16)
  frame : Frame [⟨Ca s₀, 16⟩, stR s₀] (fsMem s₀) s.mem
  r5 : s.gpr .r5 = S s₀
  keep : ∀ r ∈ preserved, r ≠ .r4 → r ≠ .r5 → r ≠ .lr → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem finArgs_eq : finArgs = xorBlk .r12 .lr .r5 .r2 .r5 2048 0 2048 ++
    (.mov .r12 (.imm 0) :: (zeroBlk .r12 .r2 0 ++
      ([.mov .r3 (.reg .r2), .dp .add .r2 .r5 (.imm (BitVec.ofNat 32 2048)), .mov .r4 (.imm 1)] :
        List Instr))) := rfl

theorem preserved_ne {r : Reg} (hr : r ∈ preserved) : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem finArgs_wp {s₀ : State} (hp : FPre s₀) {s : State} (h : BPost s₀ s) :
    WP isa (.block finArgs) s (FMid s₀) := by
  have sf := hp.scr_fit
  have tf := hp.st_fit
  have hR := hp.rounds
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have r2 : s.gpr .r2 = St s₀ := h.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have cA : State.addr (S s₀ + BitVec.ofNat 32 2048) = Ca s₀ := addr_add (by omega)
  have cSt : (⟨Ca s₀, 16⟩ : Region).Disjoint (stR s₀) := hp.st_scr.symm.sub_left (Offset.sub_base _ (by decide))
  have wSt : Covers [stR s₀] s₀.wr := by
    rw [hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
  rw [finArgs_eq]
  refine xorBlk_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [h.r5]; omega) (by rw [r2]; omega) (by rw [h.r5]; omega)
    (by
      rw [h.r5, hrw]
      exact fun a n hi => (hp.cS (d := 2048) (n := 16) (by decide)) a n hi |>
        fun ⟨r, hr, hc⟩ => ⟨r, List.mem_append_right _ hr, hc⟩)
    (by
      rw [r2, add0, hrw]
      exact fun a n hi => wSt a n hi |> fun ⟨r, hr, hc⟩ => ⟨r, List.mem_append_right _ hr, hc⟩)
    (by rw [h.r5, h.wr]; exact hp.cS (by decide)) fun s₁ g₁ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₂ u₂ => ?_
  have r2₂ : s₂.gpr .r2 = St s₀ := by rw [u₂.other _ (by decide), g₁.gpr _ (by decide) (by decide), r2]
  refine Proof.CmacAes.Arm.zeroBlk_ok u₂.gpr (by decide) (by rw [r2₂]; omega)
    (by rw [r2₂, add0, u₂.wr, g₁.wr, h.wr]; exact wSt) fun s₃ G₃ m₃ rd₃ wr₃ sp₃ => ?_
  refine wp_mov (op2_reg _ _) fun s₄ u₄ => wp_add (op2_imm (by decide)) fun s₅ u₅ =>
    wp_mov (op2_imm (by decide)) fun s₆ u₆ => WP.block_nil ?_
  have keep : ∀ r, r ≠ .r2 → r ≠ .r3 → r ≠ .r4 → r ≠ .r12 → r ≠ .lr → s₆.gpr r = s.gpr r :=
    fun r h2 h3 h4 h12 hlr => by
      rw [u₆.other _ h4, u₅.other _ h2, u₄.other _ h3, G₃, u₂.other _ h12, g₁.gpr _ h12 hlr]
  have r5₆ : s₆.gpr .r5 = S s₀ := by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), h.r5]
  have sp₆ : s₆.sp = s₀.sp := by rw [u₆.sp, u₅.sp, u₄.sp, sp₃, u₂.sp, g₁.sp, h.sp]
  have rd₆ : s₆.rd = s₀.rd := by rw [u₆.rd, u₅.rd, u₄.rd, rd₃, u₂.rd, g₁.rd, h.rd]
  have wr₆ : s₆.wr = s₀.wr := by rw [u₆.wr, u₅.wr, u₄.wr, wr₃, u₂.wr, g₁.wr, h.wr]
  have mem₆ : s₆.mem = Proof.Cmac.zero4 (Proof.Cmac.xor4Mem s.mem (Ca s₀) (Ca s₀) (State.addr (St s₀)))
      (State.addr (St s₀)) := by
    rw [u₆.mem, u₅.mem, u₄.mem, m₃, r2₂, add0, u₂.mem, g₁.mem, h.r5, r2, add0]
  have hb : below s₆ = belowR s₀ := by rw [below, sp₆]; rfl
  have stS : Spec.Aes.bytesAt s.mem (State.addr (St s₀)) 16 = Spec.Aes.bytesAt s₀.mem (State.addr (St s₀)) 16 :=
    Proof.Cmac.bytesAt_frame16 ((fsMem_frame s₀).trans (h.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, List.mem_singleton_self _, Offset.sub_base _ (by decide)⟩)) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.st_scr
  refine ⟨?_, ?_, ?_, r5₆, fun r hr h4 h5 hlr => ?_, sp₆, rd₆, wr₆⟩
  · exact
    { r0 := by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide),
          h.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)]
      r1 := by
        rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide),
          h.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [R]
      r2 := by rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), G₃, u₂.other _ (by decide),
          g₁.gpr _ (by decide) (by decide), h.r5]
      r3 := by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, G₃, r2₂]
      hra := u₆.gpr
      hrb := r5₆
      regs := by decide
      rounds := hR
      hsp := by rw [sp₆]; exact hp.sp8
      wc := by rw [cA]; exact (hp.ca_key (d := 0) (n := 240) (by decide)).symm |> fun d => by simpa using d
      wd := hp.key_st.sub_left (Region.sub_prefix (by decide))
      ws := (hp.key_scr.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
      cd := by rw [cA]; exact cSt
      cs := by rw [cA]; exact Offset.disjoint_base _ (by decide) (by omega)
      ds := hp.st_scr.sub_right (Region.sub_prefix (by decide))
      bw := by rw [hb]; exact hp.b_key.sub_right (Region.sub_prefix (by decide))
      bc := by rw [hb, cA]; exact hp.b_scr.sub_right (Offset.sub_base _ (by decide))
      bd := by rw [hb]; exact hp.b_st
      bs := by rw [hb]; exact hp.b_scr.sub_right (Region.sub_prefix (by decide))
      hW := by have := hp.key_fit; omega
      hC := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 2048) (by decide),
          Nat.mod_eq_of_lt (by omega)]; omega
      hD := tf
      hS := by omega
      reads := by
        rw [rd₆, wr₆, hp.rd]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact ⟨keyR s₀, by simp, 0, by simp, by simp⟩
      writes := by
        rw [wr₆, hp.wr, cA]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨scrR s₀, by simp, 2048, rfl, by simp⟩
        · exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
        · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩
      zero := by rw [mem₆]; exact Proof.Cmac.zero4_bytes _ _ }
  · rw [mem₆, Proof.Cmac.zero4, Proof.Cmac.bytesAt_frame16 (Proof.Cmac.frame_store4 _ _ _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact cSt),
      Proof.Cmac.xor4Mem_bytes _ (Proof.Cmac.Sep4.self _) (Proof.Cmac.Sep4.of_disjoint cSt), h.blk, stS]
  · rw [mem₆]
    refine ((h.frame.trans (Proof.Cmac.xor4Mem_frame _ _ _ _)).mono (by simp)).trans
      ((Proof.Cmac.frame_store4 _ _ _ _ _).mono (by simp))
  · have hne := preserved_ne hr
    rw [keep r hne.2.2.1 hne.2.2.2.1 h4 hne.2.2.2.2 hlr, h.keep r hne.2.2.2.1 h4 h5 hne.2.2.2.2 hlr]

theorem finPre_wp {s₀ : State} (hp : FPre s₀) : WP isa finPre s₀ (FMid s₀) := by
  refine WP.seq (WP.mono (finSave_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (Q := BPost s₀) ?_ fun _ h => finArgs_wp hp h)
  have ev : isa.eval .eq s₁ = some (decide (N s₀ = 16)) := by
    show VG.Arm.eval .eq s₁ = _; rw [eval_eq, h₁.z]
  by_cases hL : N s₀ = 16
  · exact WP.ite true (by rw [ev]; simp [hL]) (fun _ => full_wp hp hL h₁) (fun h => by cases h)
  · exact WP.ite false (by rw [ev]; simp [hL]) (fun h => by cases h)
      (fun _ => partial_wp hp (by have := hp.len; omega) h₁)

/-! ## The whole function -/

/-- What `vg_cmac_aes_finalize` leaves in the state, from the subkeys after
the key schedule, whatever they are. -/
def finalizeRaw (s₀ s' : State) : Prop :=
  Spec.Aes.bytesAt s'.mem (State.addr (St s₀)) 16 =
    ciph s₀ (Spec.Cmac.xor (mn s₀) (Spec.Aes.bytesAt s₀.mem (State.addr (St s₀)) 16))

/-- `finalizeArm` with `finalizeRaw` as its postcondition. -/
def finalizeRawArm : Contract isa := { finalizeArm with post := finalizeRaw }

theorem finalize_raw_wp {s₀ : State} (h0 : finalizeArm.pre s₀) :
    WP isa finalize s₀ fun s' => abiPreserved s₀ s' ∧ finalizeRaw s₀ s' := by
  have hp := FPre.of h0
  have hR := hp.rounds
  have hRb : 16 * (R s₀ + 1) ≤ 240 := by rcases hR with h | h | h <;> omega
  have sf := hp.scr_fit
  have cA : State.addr (S s₀ + BitVec.ofNat 32 2048) = Ca s₀ := addr_add (by omega)
  refine WP.seq (WP.mono (finPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (ctr_call h₁.pre) fun s₂ h₂ => ?_)
  have r5₂ : s₂.gpr .r5 = S s₀ := by rw [h₂.saved .r5 (by simp [preserved]) (by decide), h₁.r5]
  have rdwr₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr]
  have inS : ∀ d, d + 4 ≤ 2176 → InRegions (s₂.rd ++ s₂.wr) (State.addr (S s₀) + BitVec.ofNat 64 d) 4 :=
    fun d hd => by
      rw [rdwr₂]
      obtain ⟨r, hr, hc⟩ := in_of_cov (hp.cS (d := d) (n := 4) hd)
      exact ⟨r, List.mem_append_right _ hr, hc⟩
  rw [show ([.ldr .r4 .r5 2064, .ldr .lr .r5 2072, .ldr .r5 .r5 2068] : List Instr) =
    [(.r4, 2064), (.lr, 2072)].map (fun (p : Reg × Nat) => Instr.ldr p.1 .r5 p.2) ++ [.ldr .r5 .r5 2068] from rfl]
  refine Spill.restoreList_ok [(.r4, 2064), (.lr, 2072)] s₂ _ (by decide) (fun p hp' => ?_)
    fun s₃ ld₃ ho₃ m₃ rd₃ wr₃ sp₃ => ?_
  · have hb : 2064 ≤ p.2 ∧ p.2 + 4 ≤ 2076 ∧ p.1 ≠ .r5 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl <;> decide
    exact ⟨hb.2.2, by omega, by rw [r5₂]; omega, by rw [r5₂]; exact inS _ (by omega)⟩
  refine wp_ldr (a := State.addr (S s₀) + BitVec.ofNat 64 2068) (by decide)
    (by rw [ho₃ _ (by decide), r5₂]; exact addr_add (by omega))
    (by rw [rd₃, wr₃]; exact inS _ (by decide)) fun s₄ u₄ => WP.block_nil ?_
  -- The slots, which nothing after the save writes.
  have slot : ∀ r d, (r, d) ∈ fsaved → s₂.mem.readW (State.addr (S s₀) + BitVec.ofNat 64 d) 32 = s₀.gpr r := by
    intro r d hrd
    have hd : 2064 ≤ d ∧ d + 4 ≤ 2076 := by
      simp only [fsaved, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hrd
      omega
    rw [h₂.frame.readW (r := ⟨State.addr (S s₀) + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · rw [cA]; exact Offset.disjoint _ (by omega) (by omega) (by omega)
        · exact hp.st_scr.symm.sub_left (Offset.sub_base _ (by omega))
        · exact Offset.disjoint_base _ (by omega) (by omega)
        · rw [below, h₁.sp]; exact hp.b_scr.symm.sub_left (Offset.sub_base _ (by omega))) (by decide),
      h₁.frame.readW (r := ⟨State.addr (S s₀) + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Offset.disjoint _ (by omega) (by omega) (by omega)
        · exact hp.st_scr.symm.sub_left (Offset.sub_base _ (by omega))) (by decide),
      fsMem_slot s₀ hrd]
  have sch : Spec.Aes.bytesAt s₁.mem (State.addr (W s₀)) (16 * (R s₀ + 1)) =
      Spec.Aes.bytesAt s₀.mem (State.addr (W s₀)) (16 * (R s₀ + 1)) := by
    have f : Frame [scrR s₀, stR s₀] s₀.mem s₁.mem :=
      (((fsMem_frame s₀).mono (by simp)).trans (h₁.frame.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨scrR s₀, by simp, Offset.sub_base _ (by decide)⟩
        · exact ⟨stR s₀, by simp, fun _ h => h⟩))
    exact Proof.Cmac.bytesAt_frame f (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.key_scr.sub_left (Region.sub_prefix (by omega))
      · exact hp.key_st.sub_left (Region.sub_prefix (by omega))) (by omega)
  refine ⟨⟨fun r hr => ?_, by rw [u₄.sp, sp₃, h₂.sp, h₁.sp]⟩, ?_⟩
  · by_cases h4 : r = .r4
    · subst h4; rw [u₄.other _ (by decide), ld₃ (.r4, 2064) (by simp), r5₂, slot .r4 2064 (by decide)]
    by_cases h5 : r = .r5
    · subst h5; rw [u₄.gpr, m₃, slot .r5 2068 (by decide)]
    by_cases hlr : r = .lr
    · subst hlr; rw [u₄.other _ (by decide), ld₃ (.lr, 2072) (by simp), r5₂, slot .lr 2072 (by decide)]
    rw [u₄.other _ h5, ho₃ _ (by simp [h4, hlr]), h₂.saved r hr hlr, h₁.keep r hr h4 h5 hlr]
  · show Spec.Aes.bytesAt s₄.mem (State.addr (St s₀)) 16 = _
    rw [u₄.mem, m₃, h₂.out, sch, cA, h₁.blk]

theorem finalize_wp {s₀ : State} (h0 : finalizeArm.pre s₀) :
    WP isa finalize s₀ fun s' => abiPreserved s₀ s' ∧ finalizeArm.post s₀ s' := by
  have hp := FPre.of h0
  refine WP.mono (finalize_raw_wp h0) fun s' ⟨ab, raw⟩ => ⟨ab, fun hk msg hm hne hst => ?_⟩
  have hk' : Spec.Aes.bytesAt s₀.mem (State.addr (W s₀) + BitVec.ofNat 64 240) 32 =
      (Spec.Cmac.subkeys (ciph s₀) 16).1 ++ (Spec.Cmac.subkeys (ciph s₀) 16).2 := hk
  obtain ⟨e1, e2⟩ := Proof.Cmac.k1k2 (Proof.Cmac.subkeys_aes_length _ _) hk'
  show Spec.Aes.bytesAt s'.mem (State.addr (St s₀)) 16 = _
  rw [raw, mn, e1, e2, hst,
    Proof.Cmac.macFull_split _ hm (by rw [Proof.Cmac.bytesAt_length]; exact hp.len)
      (by rw [Proof.Cmac.bytesAt_length]; exact hne), Proof.Cmac.xor_comm]

end VG.Proof.CmacAes.Arm

end

/-!
# AES-CMAC on ARMv7: `vg_cmac_aes_finalize` is constant time

The code before the call is checked by the taint analysis, from the public
arguments (its branches and the copy loop depend only on `last_len`), the call
of `vg_aes_ctr32`, in its frame, is constant time by its own proof
(`ctr_rel`), its arguments pinned by the correctness proof (`FMid`), and the
restore after it by the taint analysis again, from `r5` (the scratch buffer).
-/

namespace VG.Proof.CmacAes.Arm

open VG VG.Arm VG.Impl.CmacAes.Arm

/-- The restore after the call. -/
abbrev finEnd : List Instr := [.ldr .r4 .r5 2064, .ldr .lr .r5 2072, .ldr .r5 .r5 2068]

theorem finalize_rel {s₀ s₀' : State} (h0 : finalizeArm.pre s₀) (h0' : finalizeArm.pre s₀')
    (hq : finalizeArm.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') finalize fun _ _ => True := by
  obtain ⟨q₀, q₁, q₂, q₃, q₄, q₅, q₆⟩ := hq
  have hp := FPre.of h0
  have hp' := FPre.of h0'
  have eW : W s₀' = W s₀ := q₁.symm
  have eR : R s₀' = R s₀ := by rw [R, R, q₂]
  have eSt : St s₀' = St s₀ := q₃.symm
  have eS : S s₀' = S s₀ := q₆.symm
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (argTaint [.r0, .r1, .r2, .r3] 8) finPre h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r5]) (.block finEnd) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have wfA : ∀ {s : State}, FPre s →
      s.sp.toNat + 8 ≤ 2 ^ 32 ∧ ∀ r ∈ s.wr, Region.Disjoint ⟨State.addr s.sp, 8⟩ r := fun {s} h => by
    have e : (⟨State.addr s.sp, 8⟩ : Region) = argsR s := by simp [stackArgAddr]
    refine ⟨h.sp_fit, ?_⟩
    rw [e, h.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact h.st_args.symm
    · exact h.scr_args.symm
  have a := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := FMid s₀) (G' := FMid s₀')
    (argTaint [.r0, .r1, .r2, .r3] 8)
    (fun s s' e e' => by
      subst e e'
      refine agree_argTaint (fun r hr => ?_) q₀ (wfA hp) (wfA hp')
        (argMem_of (j := 2) q₀ hp.sp_fit fun i hi => ?_)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
      · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
        · exact q₅
        · exact q₆) ⟨_, hA⟩
    (fun s e => by rw [e]; exact finPre_wp hp) (fun s e => by rw [e]; exact finPre_wp hp')
  have c := rel_wp (F := FMid s₀) (F' := FMid s₀') (G := fun s => s.gpr .r5 = S s₀)
    (G' := fun s => s.gpr .r5 = S s₀')
    (ctr_rel (sp₀ := s₀.sp) fun s₁ s₂ h =>
      ⟨h.1.pre, by have := h.2.pre; rwa [eW, eS, eSt, eR] at this, h.1.sp, h.2.sp.trans q₀.symm⟩)
    (fun _ h => WP.mono (ctr_call h.pre) fun _ hc => by rw [hc.saved .r5 (by simp [preserved]) (by decide), h.r5])
    (fun _ h => WP.mono (ctr_call h.pre) fun _ hc => by rw [hc.saved .r5 (by simp [preserved]) (by decide), h.r5])
  have b := RelCT.taint (A := taint) (P := fun s₁ s₂ => s₁.gpr .r5 = S s₀ ∧ s₂.gpr .r5 = S s₀')
    (Taint.ofRegs [.r5]) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1, h.2, eS]) hB
  exact a.seq (c.seq b)

theorem finalize_ct : ConstantTime isa finalizeArm.pre finalizeArm.pub finalize :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (finalize_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.Arm

end

/-!
# AES-CMAC on ARMv7: `Verified`

Correctness and constant time, a state satisfying each precondition, and the
shared contracts of `Spec/Cmac/Contract.lean`, with 8 bytes of stack: each
call of `vg_aes_ctr32` pushes its two stack arguments.
-/

namespace VG.Proof.CmacAes.Arm

open VG VG.Arm VG.Impl.CmacAes.Arm

/-- A state satisfying `vg_cmac_aes_update`'s precondition (with no blocks,
and the scratch buffer at 0, which the zero stack arguments point at). -/
def updSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 240⟩, ⟨0x3000, 0⟩, ⟨0x8000, 8⟩]
  wr := [⟨0x2000, 16⟩, ⟨0, 2176⟩]

theorem update_verified : Verified Arm.target update (Spec.Cmac.aesUpdateContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => update_wp hs) update_ct (by
    sig_implies [Spec.Cmac.aesUpdateContract, Spec.Cmac.aesUpdateSig, updateArm, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [updSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using updSat)

/-- A state satisfying `vg_cmac_aes_subkeys`'s precondition. -/
def subSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 240⟩]
  wr := [⟨0x2000, 32⟩, ⟨0x3000, 2176⟩]

theorem subkeys_verified : Verified Arm.target subkeys (Spec.Cmac.aesSubkeysContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => subkeys_wp hs) subkeys_ct (by
    sig_implies [Spec.Cmac.aesSubkeysContract, Spec.Cmac.aesSubkeysSig, subkeysArm, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [subSat] using subSat)

/-- A state satisfying `vg_cmac_aes_finalize`'s precondition (with no last
bytes, and the scratch buffer at 0). -/
def finSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 272⟩, ⟨0x3000, 0⟩, ⟨0x8000, 8⟩]
  wr := [⟨0x2000, 16⟩, ⟨0, 2176⟩]

theorem finalize_verified : Verified Arm.target finalize (Spec.Cmac.aesFinalizeContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => finalize_wp hs) finalize_ct (by
    sig_implies [Spec.Cmac.aesFinalizeContract, Spec.Cmac.aesFinalizeSig, finalizeArm, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [finSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using finSat)

end VG.Proof.CmacAes.Arm
