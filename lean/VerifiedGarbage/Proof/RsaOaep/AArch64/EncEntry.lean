import VerifiedGarbage.Proof.RsaOaep.AArch64.EncLay

/-!
# RSAES-OAEP encryption on AArch64: entering the frames

The layout of a call (`lay`), what the shared contract says of it
(`lay_ok`), and the prologue (`prologue_ok`): our register arguments saved
to their slots, our stack arguments moved to theirs, establishing `Ctx`.
-/

namespace VG.Proof.RsaOaep.AArch64.Enc

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Proof.RsaPkcs1Enc.AArch64.Enc (q_add add_add read8 write8 toNat_sub_k preserved_ne)
open VG.Proof.RsaOaep.AArch64.Dec (moveMem MoveOk moveMem_frame moveMem_read moveMem_moved moves_ok sub_trans
  entered entered_rd entered_gpr entered_v)

/-- The shared contract, with `P + 288` bytes of stack. -/
abbrev encSpec (H G : Spec.Mgf1.Hash) (P : Nat) : Contract isa :=
  Spec.RsaOaep.encryptContract H G AArch64.abi (P + 288)

/-- The layout of a call from `s`, with `D` bytes of seed and `P` bytes of
stack for the calls. -/
def lay (D P : Nat) (s : State) : ELay :=
  ⟨s.gpr .x0, s.gpr .x1, s.gpr .x2, s.gpr .x3, s.gpr .x4, s.gpr .x5, s.gpr .x6, s.gpr .x7,
    stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4, D, s.sp - BitVec.ofNat 64 288, P⟩

theorem lay_Q (D P : Nat) (s : State) : (lay D P s).Q + BitVec.ofNat 64 288 = s.sp := BitVec.sub_add_cancel _ _

theorem lay_args (D P : Nat) (s : State) : (lay D P s).Q + BitVec.ofNat 64 288 = stackArgAddr s 0 := by
  rw [lay_Q, stackArgAddr]; exact (BitVec.add_zero _).symm

theorem lay_stk (D P : Nat) (s : State) :
    (lay D P s).Q - BitVec.ofNat 64 P = s.sp - BitVec.ofNat 64 (P + 287 + 1) := by
  simp only [lay]
  rw [BitVec.sub_sub, BitVec.ofNat_add_ofNat, show 288 + P = P + 287 + 1 by omega]

theorem forall_ro {L : ELay} {F : Region → Prop} (h : F L.N ∧ F L.E ∧ F L.LAB ∧ F L.MSG ∧ F L.SD) :
    ∀ R ∈ L.ro, F R := by
  intro R hR
  simp only [ELay.ro, List.mem_cons, List.not_mem_nil, or_false] at hR
  obtain ⟨a, b, c, d, e⟩ := h
  rcases hR with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem lay_ok {H G : Spec.Mgf1.Hash} {P : Nat} {s : State} (h : (encSpec H G P).pre s) :
    (lay H.len P s).Ok := by
  sig_pre [Spec.RsaOaep.encryptContract, Spec.RsaOaep.encryptSig, AArch64.abi, AArch64.argRegs,
    _root_.List.range, _root_.List.range.loop, List.append_eq] at h
  obtain ⟨hsp, hsp2, -, -,
    oN, oE, oL, oM, oSd, oS, oA,
    nS, eS, lS, mS, sdS, sA,
    kO, kN, kE, kL, kM, kSd, kS, -,
    bO, bN, bE, bL, bM, bSd, bS,
    kv, hk1, el1, elk, slk⟩ := h
  simp only [hk1] at oA oN oE oL oM oSd oS kO bO
  have eA : (lay H.len P s).ARGS = ⟨stackArgAddr s 0, 40⟩ := by simp only [ELay.ARGS, lay_args]
  have eK : (lay H.len P s).STK = ⟨s.sp - BitVec.ofNat 64 (P + 287 + 1), P + 287 + 1⟩ := by
    show (⟨(lay H.len P s).Q - BitVec.ofNat 64 P, P + 288⟩ : Region) = _
    rw [lay_stk]
  have hQ : (lay H.len P s).Q.toNat = s.sp.toNat - 288 := toNat_sub_k (by omega)
  refine ⟨oS, forall_ro ⟨oN, oE, oL, oM, oSd⟩, forall_ro ⟨nS.symm, eS.symm, lS.symm, mS.symm, sdS.symm⟩, eA ▸ oA,
    eA ▸ sA, eK ▸ kO, eK ▸ kS, forall_ro ⟨eK ▸ kN, eK ▸ kE, eK ▸ kL, eK ▸ kM, eK ▸ kSd⟩, bO, bS,
    forall_ro ⟨bN, bE, bL, bM, bSd⟩, by omega, by simp only [lay] at hQ ⊢; omega, kv, hk1, el1, elk, slk⟩

/-! ## The prologue -/

theorem entered_sp (D P : Nat) (s : State) : (entered s).sp = (lay D P s).Q := by
  show s.sp - 16 - BitVec.ofNat 64 272 = s.sp - BitVec.ofNat 64 288
  rw [BitVec.sub_sub]; rfl

theorem lr_slot (D P : Nat) (s : State) : s.sp - 16 = (lay D P s).Q + BitVec.ofNat 64 272 := by
  show s.sp - 16 = s.sp - BitVec.ofNat 64 288 + BitVec.ofNat 64 272
  bv_omega

theorem entered_wr (D P : Nat) (s : State) :
    (entered s).wr = (lay D P s).FR :: (lay D P s).LR :: s.wr := by
  show (⟨s.sp - 16 - BitVec.ofNat 64 272, 272⟩ : Region) :: ⟨s.sp - 16, 16⟩ :: s.wr = _
  rw [show s.sp - 16 - BitVec.ofNat 64 272 = (lay D P s).Q from entered_sp D P s, lr_slot D P]
  rfl

theorem entered_mem (D P : Nat) (s : State) :
    (entered s).mem = s.mem.writeW ((lay D P s).Q + BitVec.ofNat 64 272) (s.gpr .x30) := by
  show s.mem.write (s.sp - 16) 8 (s.gpr .x30) = _
  rw [lr_slot D P, write8]

theorem ourArg_lay (D P : Nat) (s : State) : ∀ j, j < 5 → ourArg (lay D P s) j = stackArg s j
  | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl

/-- The register arguments' slots. -/
abbrev saveList : List (Reg × Nat) :=
  [(.x0, sOut), (.x2, sN), (.x3, sK), (.x4, sE), (.x5, sEl), (.x6, sLab), (.x7, sLabLen)]

/-- The stack arguments' moves to their slots. -/
def argMoves : List (Nat × Nat) := [(0, sMsg), (1, sMsgLen), (2, sSeed), (3, sScr), (4, sScrLen)]

theorem encPrologue_eq : encPrologue = ([.addSp .x9 0] : List Instr) ++ Spill.saveCode .x9 saveList ++
    argMoves.flatMap (fun p => mvArg p.1 p.2) := rfl

theorem argMoves_ok : MoveOk argMoves := by decide

theorem argMoves_nodup : (argMoves.map Prod.snd).Nodup := by decide

theorem argMoves_lt : ∀ p ∈ argMoves, p.1 < 5 := by decide

theorem argMoves_apart {a : Nat} (ha : a ∈ saveList.map Prod.snd) :
    ∀ p ∈ argMoves, p.2 + 8 ≤ a ∨ a + 8 ≤ p.2 := by
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem spec_rdwr {H G : Spec.Mgf1.Hash} {P : Nat} {s : State} (h : (encSpec H G P).pre s) :
    s.rd = [(lay H.len P s).N, (lay H.len P s).E, (lay H.len P s).LAB, (lay H.len P s).MSG, (lay H.len P s).SD,
      (lay H.len P s).ARGS] ∧ s.wr = [(lay H.len P s).OUT, (lay H.len P s).SCR] := by
  have hL := lay_ok h
  sig_pre [Spec.RsaOaep.encryptContract, Spec.RsaOaep.encryptSig, AArch64.abi, AArch64.argRegs,
    _root_.List.range, _root_.List.range.loop, List.append_eq] at h
  obtain ⟨-, -, hrd, hwr, -⟩ := h
  have hk1 : (s.gpr .x1).toNat = (s.gpr .x3).toNat := hL.olk
  have e40 : (lay H.len P s).ARGS = ⟨stackArgAddr s 0, 40⟩ := by simp only [ELay.ARGS, lay_args]
  rw [hrd, hwr, hk1, e40]
  exact ⟨rfl, rfl⟩

/-- The frame's words as the prologue leaves them. -/
abbrev Prologued (L : ELay) (W : Nat → BitVec 64) : Prop := Slots L W

theorem prologue_ok {H G : Spec.Mgf1.Hash} {P : Nat} {s : State} (h : (encSpec H G P).pre s) :
    WP isa (.block encPrologue) (entered s) fun t => Ctx (lay H.len P s) s.gpr s.v s.mem t ∧
      t.gpr .x9 = (lay H.len P s).Q ∧ Slots (lay H.len P s) (fun j => word t.mem (lay H.len P s).Q (8 * j)) := by
  have hL := lay_ok h
  have hnQ := hL.nQ
  have hpQ : P ≤ (lay H.len P s).Q.toNat := hL.pQ
  obtain ⟨hrd, hwr⟩ := spec_rdwr h
  have hfr : ∀ (u : State) d n, u.wr = (entered s).wr → d + n ≤ frameBytes →
      InRegions u.wr ((lay H.len P s).Q + BitVec.ofNat 64 d) n :=
    fun u d n hu hd => ⟨(lay H.len P s).FR, by rw [hu, entered_wr H.len P]; simp,
      Offset.contains_base _ hd (by unfold frameBytes at hd; omega)⟩
  have harg : ∀ (u : State) d, u.rd = s.rd → 288 ≤ d → d + 8 ≤ 328 →
      InRegions (u.rd ++ u.wr) ((lay H.len P s).Q + BitVec.ofNat 64 d) 8 :=
    fun u d hu h₁ h₂ => ⟨(lay H.len P s).ARGS, by rw [hu, hrd]; simp, Offset.contains _ h₁ (by omega) (by omega)⟩
  have eLr : (entered s).mem.readW ((lay H.len P s).Q + BitVec.ofNat 64 272) 64 = s.gpr .x30 := by
    rw [entered_mem H.len P, Mem.readW_writeW_self64]
  have eArg : ∀ j, j < 5 → (entered s).mem.readW ((lay H.len P s).Q + BitVec.ofNat 64 (288 + 8 * j)) 64 =
      stackArg s j := by
    intro j hj
    rw [entered_mem H.len P, Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide),
      stackArg, stackArgAddr, ← lay_Q H.len P s, add_add]
  have eFr : Frame [(lay H.len P s).STK] s.mem (entered s).mem := by
    rw [entered_mem H.len P]
    refine (Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_
    show (⟨(lay H.len P s).Q - BitVec.ofNat 64 P, P + 288⟩ : Region).Contains
      ((lay H.len P s).Q + BitVec.ofNat 64 272) (64 / 8)
    rw [q_add (lay H.len P s).Q P 272]
    exact Offset.contains_base _ (by omega) (by omega)
  rw [encPrologue_eq, List.append_assoc, WP.block_append_iff]
  have h0 : WP isa (.block [.addSp .x9 0]) (entered s) fun t₀ =>
      t₀ = (entered s).write .x .x9 (lay H.len P s).Q := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Nat.reduceLT, ite_true, entered_sp H.len P,
      BitVec.add_zero, Option.some.injEq, exists_eq_left']
  refine WP.mono h0 fun t₀ ht₀ => ?_
  subst ht₀
  have h9 : ((entered s).write .x .x9 (lay H.len P s).Q).gpr .x9 = (lay H.len P s).Q := by
    simp only [RegUpd.gpr_write, ite_true, Size.bits, BitVec.setWidth_eq]
  rw [WP.block_append_iff]
  refine WP.mono (Spill.save_wp (by decide) (fun p hp => ?_)) fun t₂ hs => ?_
  · rw [h9]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact hfr _ _ _ (RegUpd.wr_write ..) (by decide)
  have hsp₂ : t₂.sp = (lay H.len P s).Q := hs.sp.trans ((RegUpd.sp_write ..).trans (entered_sp H.len P s))
  have hrd₂ : t₂.rd = s.rd := hs.rd.trans (RegUpd.rd_write ..)
  have hwr₂ : t₂.wr = (entered s).wr := hs.wr.trans (RegUpd.wr_write ..)
  refine WP.mono (moves_ok argMoves_ok (t := t₂) (by rw [hs.gpr, h9, hsp₂])
    (fun p hp => by rw [hsp₂]; exact hfr _ _ _ hwr₂ (argMoves_ok p hp).2.1)
    (fun p hp => by
      have := argMoves_lt p hp
      rw [hsp₂]; exact harg _ _ hrd₂ (by unfold arg frameBytes; omega) (by unfold arg frameBytes; omega)))
    fun u hm => ?_
  have M2 : t₂.mem = Spill.saveMem (entered s).mem (lay H.len P s).Q
      ((entered s).write .x .x9 (lay H.len P s).Q).gpr saveList := by
    rw [hs.mem, h9, RegUpd.mem_write]
  have F2 : Frame [⟨(lay H.len P s).Q, 216⟩] (entered s).mem t₂.mem := by
    rw [M2]
    exact Spill.saveMem_frame_base (fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) (by decide) _ _ _
  have S2 : Spill.Saved (lay H.len P s).Q ((entered s).write .x .x9 (lay H.len P s).Q).gpr saveList t₂.mem := by
    rw [M2]; exact Spill.saveMem_saved (by decide) _ _ _
  have U : u.mem = moveMem t₂.mem (lay H.len P s).Q t₂.mem argMoves := by rw [hm.mem, hsp₂]
  have hi₂ : ∀ d, 216 ≤ d → d + 8 ≤ 408 → t₂.mem.readW ((lay H.len P s).Q + BitVec.ofNat 64 d) 64 =
      (entered s).mem.readW ((lay H.len P s).Q + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ =>
    F2.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base _ (by omega) (by omega)) (by decide)
  have uArg : ∀ j, j < 5 → u.mem.readW ((lay H.len P s).Q + BitVec.ofNat 64 (288 + 8 * j)) 64 = stackArg s j := by
    intro j hj
    rw [U, moveMem_read argMoves_ok _ _ (fun p hp => by
      have := (argMoves_ok p hp).2.1; unfold frameBytes at this; omega) (by omega),
      hi₂ _ (by omega) (by omega), eArg j hj]
  have uMv : ∀ p ∈ argMoves, u.mem.readW ((lay H.len P s).Q + BitVec.ofNat 64 p.2) 64 = stackArg s p.1 := by
    intro p hp
    have := argMoves_lt p hp
    rw [U, moveMem_moved argMoves_ok argMoves_nodup _ _ p hp, show arg p.1 = 288 + 8 * p.1 from rfl,
      hi₂ _ (by omega) (by omega), eArg _ this]
  have uSv : ∀ r d, (r, d) ∈ saveList → u.mem.readW ((lay H.len P s).Q + BitVec.ofNat 64 d) 64 = s.gpr r := by
    intro r d hrd
    rw [U, moveMem_read argMoves_ok _ _ (argMoves_apart (List.mem_map_of_mem (f := Prod.snd) hrd))
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hrd
          rcases hrd with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> (dsimp only; decide)),
      S2 (r, d) hrd]
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hrd
    rcases hrd with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
      exact RegUpd.gpr_write_of_ne _ _ _ (by dsimp only; decide)
  have F : Frame [⟨(lay H.len P s).Q, 272⟩] (entered s).mem u.mem := by
    rw [U]
    refine Frame.trans (F2.sub fun r hr => ?_) ((moveMem_frame argMoves_ok _ _).sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by unfold frameBytes; omega)⟩
  have go : ∀ r, r ≠ .x9 → r ≠ .x10 → u.gpr r = s.gpr r := fun r h₁ h₂ => by
    rw [hm.other r h₂, hs.gpr]; exact RegUpd.gpr_write_of_ne _ _ _ h₁
  have w8 : ∀ d, word u.mem (lay H.len P s).Q d = u.mem.readW ((lay H.len P s).Q + BitVec.ofNat 64 d) 64 :=
    fun _ => rfl
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hm.rd, hrd₂, hrd]
  · rw [hm.wr, hwr₂, entered_wr H.len P, hwr]
  · rw [hm.sp, hsp₂]
  · intro r hr _
    exact go r (preserved_ne hr (by decide)) (preserved_ne hr (by decide))
  · intro r _
    rw [hm.v, hs.v, RegUpd.v_write, entered_v]
  · rw [U, moveMem_read argMoves_ok _ _ (by decide) (by omega), hi₂ 272 (by omega) (by omega), eLr]
  · intro j hj
    rw [uArg j hj, ourArg_lay H.len P s j hj]
  · have hk : (lay H.len P s).STK ∈ [(lay H.len P s).OUT, (lay H.len P s).SCR, (lay H.len P s).STK] := by simp
    refine Frame.trans (eFr.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact hk) (F.sub fun r hr => ?_)
    rw [List.mem_singleton.mp hr]
    have h272 := ELay.Ok.sub_stk (L := lay H.len P s) (d := 0) (n := 272) (by omega)
    rw [show (lay H.len P s).Q + BitVec.ofNat 64 0 = (lay H.len P s).Q from BitVec.add_zero _] at h272
    exact ⟨(lay H.len P s).STK, hk, h272⟩
  · rw [hm.other .x9 (by decide), hs.gpr, h9]
  · rw [w8]; exact uMv (3, sScr) (by decide)
  · rw [w8]; exact uSv .x0 sOut (by simp)
  · rw [w8]; exact uSv .x2 sN (by simp)
  · rw [w8]; exact uSv .x3 sK (by simp)
  · rw [w8]; exact uSv .x4 sE (by simp)
  · rw [w8]; exact uSv .x5 sEl (by simp)
  · rw [w8]; exact uMv (4, sScrLen) (by decide)
  · rw [w8]; exact uSv .x6 sLab (by simp)
  · rw [w8]; exact uSv .x7 sLabLen (by simp)
  · rw [w8]; exact uMv (0, sMsg) (by decide)
  · rw [w8]; exact uMv (1, sMsgLen) (by decide)
  · rw [w8]; exact uMv (2, sSeed) (by decide)

end VG.Proof.RsaOaep.AArch64.Enc
