import VerifiedGarbage.Proof.RsaOaep.AArch64.DecLay
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncEntry

/-!
# RSAES-OAEP decryption on AArch64: entering the frames

As for RSAES-PKCS1-v1_5 (`Proof/RsaPkcs1Enc/AArch64/DecEntry.lean`): the
layout of a call (`lay`), what the shared contract says of it (`lay_ok`),
and the prologue (`prologue_ok`), run from the state in which the inner
frame's body starts (`entered`): it saves our register arguments to their
slots (`Spill.save_wp`) and moves our stack arguments to theirs and to the
private-key operation's (`moves_ok`), establishing `Ctx`.
-/

namespace VG.Proof.RsaOaep.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Proof.RsaPkcs1Enc.AArch64.Enc (q_add add_add read8 write8 toNat_sub_k preserved_ne)

/-- The shared contract, with `P + 288` bytes of stack. -/
abbrev decSpec (H G : Spec.Mgf1.Hash) (P : Nat) : Contract isa :=
  Spec.RsaOaep.decryptContract H G AArch64.abi (P + 288)

/-- The layout of a call from `s`, with `P` bytes of stack for the calls. -/
def lay (P : Nat) (s : State) : DLay :=
  ⟨s.gpr .x0, s.gpr .x1, s.gpr .x2, s.gpr .x3, s.gpr .x4, s.gpr .x5, s.gpr .x6, s.gpr .x7,
    stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4, stackArg s 5, stackArg s 6,
    stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10, stackArg s 11, stackArg s 12, stackArg s 13,
    stackArg s 14, s.sp - BitVec.ofNat 64 288, P⟩

theorem lay_Q (P : Nat) (s : State) : (lay P s).Q + BitVec.ofNat 64 288 = s.sp := BitVec.sub_add_cancel _ _

theorem lay_args (P : Nat) (s : State) : (lay P s).Q + BitVec.ofNat 64 288 = stackArgAddr s 0 := by
  rw [lay_Q, stackArgAddr]; exact (BitVec.add_zero _).symm

theorem lay_stk (P : Nat) (s : State) :
    (lay P s).Q - BitVec.ofNat 64 P = s.sp - BitVec.ofNat 64 (P + 288) := by
  simp only [lay]
  rw [BitVec.sub_sub, BitVec.ofNat_add_ofNat, Nat.add_comm 288 P]

theorem forall_ro {L : DLay} {F : Region → Prop}
    (h : F L.N ∧ F L.E ∧ F L.PP ∧ F L.QQ ∧ F L.DP ∧ F L.DQ ∧ F L.QI ∧ F L.LAB ∧ F L.CT) : ∀ R ∈ L.ro, F R := by
  intro R hR
  simp only [DLay.ro, List.mem_cons, List.not_mem_nil, or_false] at hR
  obtain ⟨a, b, c, d, e, f, g, i, j⟩ := h
  rcases hR with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem lay_ok {H G : Spec.Mgf1.Hash} {P : Nat} {s : State} (h : (decSpec H G P).pre s) : (lay P s).Ok := by
  sig_pre [Spec.RsaOaep.decryptContract, Spec.RsaOaep.decryptSig, AArch64.abi, AArch64.argRegs,
    _root_.List.range, _root_.List.range.loop, List.append_eq] at h
  sig_split h
  rename_i hsp hsp2 hdrop1 hdrop2 oM oN oE oP oQ oDP oDQ oQI oL oC oS oA mN mE mP mQ mDP mDQ mQI mL mC mS mA
    nS eS pS qS dpS dqS qiS lS cS sA kO kM kN kE kP kQ kDP kDQ kQI kL kC kS hdrop3 bO bM bN bE bP bQ bDP bDQ
    bQI bL bC bS kv hk1 hk2 el1 elk pl1 plk ql1 qlk hdp hqi hdq
  clear hdrop1 hdrop2 hdrop3
  have slk := h
  clear h
  simp only [hk1, hk2, hdp, hqi, hdq] at oA oN oE oP oQ oDP oDQ oQI oL oC oS oM mC mDP mDQ mQI cS dpS dqS qiS
  simp only [hk1, hk2, hdp, hqi, hdq] at kO kC kDP kDQ kQI bO bC bDP bDQ bQI
  have eA : (lay P s).ARGS = ⟨stackArgAddr s 0, 120⟩ := by simp only [DLay.ARGS, lay_args]
  have eK : (lay P s).STK = ⟨s.sp - BitVec.ofNat 64 (P + 288), P + 288⟩ := by
    show (⟨(lay P s).Q - BitVec.ofNat 64 P, P + 288⟩ : Region) = _
    rw [lay_stk]
  have hQ : (lay P s).Q.toNat = s.sp.toNat - 288 := toNat_sub_k (by omega)
  refine ⟨oM, oS, mS, forall_ro ⟨oN, oE, oP, oQ, oDP, oDQ, oQI, oL, oC⟩,
    forall_ro ⟨mN, mE, mP, mQ, mDP, mDQ, mQI, mL, mC⟩,
    forall_ro ⟨nS.symm, eS.symm, pS.symm, qS.symm, dpS.symm, dqS.symm, qiS.symm, lS.symm, cS.symm⟩, eA ▸ oA,
    eA ▸ mA, eA ▸ sA, eK ▸ kO, eK ▸ kM, eK ▸ kS, forall_ro ⟨eK ▸ kN, eK ▸ kE, eK ▸ kP, eK ▸ kQ, eK ▸ kDP,
    eK ▸ kDQ, eK ▸ kQI, eK ▸ kL, eK ▸ kC⟩, bO, bM, bS, forall_ro ⟨bN, bE, bP, bQ, bDP, bDQ, bQI, bL, bC⟩,
    by omega, by simp only [lay] at hQ ⊢; omega, kv, hk1, hk2, el1, elk, pl1, plk, ql1, qlk, hdp, hqi, hdq, slk⟩

/-! ## Moving the stack arguments -/

/-- The memory after moving the word at `B + arg j` (as in `m₀`) to `B + d`
for each `(j, d)`, in order. -/
def moveMem (m : Mem) (B : Addr) (m₀ : Mem) : List (Nat × Nat) → Mem
  | [] => m
  | (j, d) :: l => moveMem (m.writeW (B + BitVec.ofNat 64 d) (m₀.readW (B + BitVec.ofNat 64 (arg j)) 64)) B m₀ l

/-- The moves' destinations are words of the frame, and their sources our
stack arguments. -/
def MoveOk (l : List (Nat × Nat)) : Prop := ∀ p ∈ l, p.2 % 8 = 0 ∧ p.2 + 8 ≤ frameBytes ∧ p.1 < 15

instance (l : List (Nat × Nat)) : Decidable (MoveOk l) := by unfold MoveOk; infer_instance

theorem moveMem_frame {l : List (Nat × Nat)} (hl : MoveOk l) {B : Addr} (m m₀ : Mem) :
    Frame [⟨B, frameBytes⟩] m (moveMem m B m₀ l) := by
  suffices h : ∀ m', Frame [⟨B, frameBytes⟩] m m' → Frame [⟨B, frameBytes⟩] m (moveMem m' B m₀ l) from
    h m (Frame.refl _ _)
  induction l with
  | nil => exact fun _ h => h
  | cons p l ih =>
    obtain ⟨j, d⟩ := p
    intro m' h
    have hd := hl (j, d) List.mem_cons_self
    have hd2 : d + 8 ≤ 272 := hd.2.1
    exact ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)) _
      (h.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by unfold frameBytes; omega) (by omega)))

theorem moveMem_read {l : List (Nat × Nat)} (hl : MoveOk l) {B : Addr} (m m₀ : Mem) {a : Nat}
    (ha : ∀ p ∈ l, p.2 + 8 ≤ a ∨ a + 8 ≤ p.2) (ha' : a + 8 ≤ 408) :
    (moveMem m B m₀ l).readW (B + BitVec.ofNat 64 a) 64 = m.readW (B + BitVec.ofNat 64 a) 64 := by
  induction l generalizing m with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨j, d⟩ := p
    have hd := hl (j, d) List.mem_cons_self
    rw [moveMem, ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)) _ (fun q hq => ha q (List.mem_cons_of_mem _ hq)),
      Mem.readW_writeW_sep (Offset.sep _ (by have := ha (j, d) List.mem_cons_self; dsimp only at this; omega)
        (by omega) (by unfold frameBytes at hd; omega)) (by decide)]

theorem moveMem_moved {l : List (Nat × Nat)} (hl : MoveOk l) (hn : (l.map Prod.snd).Nodup) {B : Addr}
    (m m₀ : Mem) :
    ∀ p ∈ l, (moveMem m B m₀ l).readW (B + BitVec.ofNat 64 p.2) 64 = m₀.readW (B + BitVec.ofNat 64 (arg p.1)) 64 := by
  induction l generalizing m with
  | nil => exact fun _ h => absurd h List.not_mem_nil
  | cons p l ih =>
    obtain ⟨j, d⟩ := p
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · have hd := hl (j, d) List.mem_cons_self
      have hne : ∀ q ∈ l, q.2 ≠ d := fun q hq e =>
        (List.nodup_cons.mp hn).1 (List.mem_map.mpr ⟨q, hq, e⟩)
      rw [moveMem, moveMem_read (fun q hq => hl q (List.mem_cons_of_mem _ hq)) _ _ (fun q hq => by
        have := hl q (List.mem_cons_of_mem _ hq); have := hne q hq
        have h8 : q.2 % 8 = 0 := (hl q (List.mem_cons_of_mem _ hq)).1
        have h8' : d % 8 = 0 := hd.1
        omega) (by unfold frameBytes at hd; dsimp only; omega), Mem.readW_writeW_self64]
    · exact ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)) (List.nodup_cons.mp hn).2 _ q hq

/-- After the moves, from `t`. -/
structure Moved (t u : State) (l : List (Nat × Nat)) : Prop where
  rd : u.rd = t.rd
  wr : u.wr = t.wr
  sp : u.sp = t.sp
  v : u.v = t.v
  mem : u.mem = moveMem t.mem t.sp t.mem l
  other : ∀ r, r ≠ .x10 → u.gpr r = t.gpr r

/-- One move. -/
theorem mv_step {u : State} {j d : Nat} (ho : arg j % 8 = 0 ∧ arg j < 32768) (hd : d % 8 = 0 ∧ d < 32768)
    (hr : InRegions (u.rd ++ u.wr) (u.sp + BitVec.ofNat 64 (arg j)) 8)
    (hw : InRegions u.wr (u.gpr .x9 + BitVec.ofNat 64 d) 8) :
    WP isa (.block (mvArg j d)) u fun u₁ => u₁.rd = u.rd ∧ u₁.wr = u.wr ∧ u₁.sp = u.sp ∧ u₁.v = u.v ∧
      u₁.mem = u.mem.writeW (u.gpr .x9 + BitVec.ofNat 64 d) (u.mem.readW (u.sp + BitVec.ofNat 64 (arg j)) 64) ∧
      ∀ r, r ≠ .x10 → u₁.gpr r = u.gpr r := by
  apply WP.of_runBlock
  rw [mvArg, runBlock_cons, Bytes.exec_ldrSp ho hr, runStep_some, runBlock_cons,
    exec_str_x hd (by rw [RegUpd.wr_write, RegUpd.gpr_write_of_ne _ _ _ (by decide)]; exact hw),
    runStep_some, runBlock_nil]
  refine ⟨_, rfl, rfl, rfl, rfl, rfl, ?_, fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr⟩
  show (u.mem.writeW _ _) = _
  rw [RegUpd.gpr_write_of_ne _ _ _ (by decide), RegUpd.gpr_write_self, BitVec.setWidth_eq]

theorem moves_ok {l : List (Nat × Nat)} (hl : MoveOk l) {t : State} (h9 : t.gpr .x9 = t.sp)
    (hw : ∀ p ∈ l, InRegions t.wr (t.sp + BitVec.ofNat 64 p.2) 8)
    (hr : ∀ p ∈ l, InRegions (t.rd ++ t.wr) (t.sp + BitVec.ofNat 64 (arg p.1)) 8) :
    WP isa (.block (l.flatMap fun p => mvArg p.1 p.2)) t fun u => Moved t u l := by
  suffices h : ∀ (l : List (Nat × Nat)), MoveOk l → ∀ (u : State), u.gpr .x9 = t.sp → u.sp = t.sp →
      u.rd = t.rd → u.wr = t.wr →
      (∀ p ∈ l, u.mem.readW (t.sp + BitVec.ofNat 64 (arg p.1)) 64 = t.mem.readW (t.sp + BitVec.ofNat 64 (arg p.1)) 64) →
      (∀ p ∈ l, InRegions u.wr (t.sp + BitVec.ofNat 64 p.2) 8) →
      (∀ p ∈ l, InRegions (u.rd ++ u.wr) (t.sp + BitVec.ofNat 64 (arg p.1)) 8) →
      WP isa (.block (l.flatMap fun p => mvArg p.1 p.2)) u fun u' => u'.rd = u.rd ∧ u'.wr = u.wr ∧
        u'.sp = u.sp ∧ u'.v = u.v ∧ u'.mem = moveMem u.mem t.sp t.mem l ∧ ∀ r, r ≠ .x10 → u'.gpr r = u.gpr r by
    exact WP.mono (h l hl t h9 rfl rfl rfl (fun _ _ => rfl) hw hr) fun u ⟨a, b, c, d, e, f⟩ => ⟨a, b, c, d, e, f⟩
  intro l
  induction l with
  | nil => exact fun _ u _ _ _ _ _ _ _ => WP.block_nil ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  | cons p l ih =>
    obtain ⟨j, d⟩ := p
    intro hl u h9 hsp hrd hwr hsrc hw hr
    have hd := hl (j, d) List.mem_cons_self
    have hw₀ := hw (j, d) List.mem_cons_self
    have hr₀ := hr (j, d) List.mem_cons_self
    have hs₀ := hsrc (j, d) List.mem_cons_self
    dsimp only at hd hw₀ hr₀ hs₀
    rw [List.flatMap_cons, WP.block_append_iff]
    have ho : arg j % 8 = 0 ∧ arg j < 32768 := by unfold arg frameBytes; omega
    have hd' : d % 8 = 0 ∧ d < 32768 := ⟨hd.1, by unfold frameBytes at hd; omega⟩
    refine WP.mono (mv_step ho hd' (by rw [hsp]; exact hr₀) (by rw [h9]; exact hw₀))
      fun u₁ ⟨r₁, w₁, s₁, v₁, m₁, g₁⟩ => ?_
    have e₁ : ∀ a, a < 15 → u₁.mem.readW (t.sp + BitVec.ofNat 64 (arg a)) 64 =
        u.mem.readW (t.sp + BitVec.ofNat 64 (arg a)) 64 := fun a ha => by
      rw [m₁, h9]
      exact Mem.readW_writeW_sep (Offset.sep _ (by unfold arg frameBytes at *; omega)
        (by unfold arg frameBytes; omega) (by unfold frameBytes at hd; omega)) (by decide)
    refine WP.mono (ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)) u₁
      (by rw [g₁ .x9 (by decide), h9]) (s₁.trans hsp) (r₁.trans hrd) (w₁.trans hwr)
      (fun q hq => (e₁ q.1 (hl q (List.mem_cons_of_mem _ hq)).2.2).trans (hsrc q (List.mem_cons_of_mem _ hq)))
      (fun q hq => by rw [w₁]; exact hw q (List.mem_cons_of_mem _ hq))
      (fun q hq => by rw [r₁, w₁]; exact hr q (List.mem_cons_of_mem _ hq)))
      fun u' ⟨a, b, c, e, f, g⟩ => ⟨a.trans r₁, b.trans w₁, c.trans s₁, e.trans v₁, ?_, fun r hr =>
        (g r hr).trans (g₁ r hr)⟩
    rw [f, m₁, moveMem, h9, hsp, hs₀]

/-! ## The prologue -/

/-- The state in which the inner frame's body starts. -/
def entered (s : State) : State := allocated frameBytes (pushed .x30 s)

@[simp] theorem entered_rd (s : State) : (entered s).rd = s.rd := rfl
@[simp] theorem entered_gpr (s : State) : (entered s).gpr = s.gpr := rfl
@[simp] theorem entered_v (s : State) : (entered s).v = s.v := rfl

theorem entered_sp (P : Nat) (s : State) : (entered s).sp = (lay P s).Q := by
  show s.sp - 16 - BitVec.ofNat 64 272 = s.sp - BitVec.ofNat 64 288
  rw [BitVec.sub_sub]; rfl

theorem lr_slot (P : Nat) (s : State) : s.sp - 16 = (lay P s).Q + BitVec.ofNat 64 272 := by
  show s.sp - 16 = s.sp - BitVec.ofNat 64 288 + BitVec.ofNat 64 272
  bv_omega

theorem entered_wr (P : Nat) (s : State) :
    (entered s).wr = (lay P s).FR :: (lay P s).LR :: s.wr := by
  show (⟨s.sp - 16 - BitVec.ofNat 64 272, 272⟩ : Region) :: ⟨s.sp - 16, 16⟩ :: s.wr = _
  rw [show s.sp - 16 - BitVec.ofNat 64 272 = (lay P s).Q from entered_sp P s, lr_slot P]
  rfl

theorem entered_mem (P : Nat) (s : State) :
    (entered s).mem = s.mem.writeW ((lay P s).Q + BitVec.ofNat 64 272) (s.gpr .x30) := by
  show s.mem.write (s.sp - 16) 8 (s.gpr .x30) = _
  rw [lr_slot P, write8]

theorem ourArg_lay (P : Nat) (s : State) : ∀ j, j < 15 → ourArg (lay P s) j = stackArg s j
  | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl | 5, _ => rfl | 6, _ => rfl
  | 7, _ => rfl | 8, _ => rfl | 9, _ => rfl | 10, _ => rfl | 11, _ => rfl | 12, _ => rfl | 13, _ => rfl
  | 14, _ => rfl

/-- The register arguments' slots. -/
abbrev saveList : List (Reg × Nat) := [(.x0, sOut), (.x2, sMl), (.x3, sN), (.x4, sK), (.x5, sE), (.x6, sEl), (.x7, 0)]

/-- The stack arguments' moves: the label, its length and `scratch` to
their slots, and ours from `p_len` to `qinv_len` to the frame's words 1 to
9. -/
def argMoves : List (Nat × Nat) :=
  [(9, sLab), (10, sLabLen), (13, sScr), (14, sScrLen)] ++ (List.range 9).map fun j => (j, 8 * (j + 1))

theorem decPrologue_eq : decPrologue = ([.addSp .x9 0] : List Instr) ++ Spill.saveCode .x9 saveList ++
    argMoves.flatMap (fun p => mvArg p.1 p.2) := rfl

theorem argMoves_ok : MoveOk argMoves := by decide

theorem argMoves_nodup : (argMoves.map Prod.snd).Nodup := by decide

theorem mem_argMoves {j : Nat} (hj : j < 9) : (j, 8 * (j + 1)) ∈ argMoves :=
  List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)

/-- The saves' slots are not the moves'. -/
theorem argMoves_apart {a : Nat} (ha : a ∈ saveList.map Prod.snd) :
    ∀ p ∈ argMoves, p.2 + 8 ≤ a ∨ a + 8 ≤ p.2 := by
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The regions the contract grants. -/
theorem spec_rdwr {H G : Spec.Mgf1.Hash} {P : Nat} {s : State} (h : (decSpec H G P).pre s) :
    s.rd = [(lay P s).N, (lay P s).E, (lay P s).PP, (lay P s).QQ, (lay P s).DP, (lay P s).DQ, (lay P s).QI,
      (lay P s).LAB, (lay P s).CT, (lay P s).ARGS] ∧ s.wr = [(lay P s).OUT, (lay P s).ML, (lay P s).SCR] := by
  have hL := lay_ok h
  sig_pre [Spec.RsaOaep.decryptContract, Spec.RsaOaep.decryptSig, AArch64.abi, AArch64.argRegs,
    _root_.List.range, _root_.List.range.loop, List.append_eq] at h
  obtain ⟨-, -, hrd, hwr, -⟩ := h
  have hk1 : (s.gpr .x1).toNat = (s.gpr .x4).toNat := hL.olk
  have hk2 : (stackArg s 12).toNat = (s.gpr .x4).toNat := hL.clk
  have hdp : (stackArg s 4).toNat = (stackArg s 0).toNat := hL.dpl
  have hqi : (stackArg s 8).toNat = (stackArg s 0).toNat := hL.qil
  have hdq : (stackArg s 6).toNat = (stackArg s 2).toNat := hL.dql
  rw [hrd, hwr, hk1, hk2, hdp, hqi, hdq, ← lay_args P]
  exact ⟨rfl, rfl⟩

/-- The frame's words as the prologue leaves them. -/
structure Prologued (L : DLay) (W : Nat → BitVec 64) : Prop where
  slots : Slots L W
  p : W 0 = L.p
  args : ∀ j < 9, W (j + 1) = ourArg L j

theorem prologue_ok {H G : Spec.Mgf1.Hash} {P : Nat} {s : State} (h : (decSpec H G P).pre s) :
    WP isa (.block decPrologue) (entered s) fun t => Ctx (lay P s) s.gpr s.v s.mem t ∧
      t.gpr .x9 = (lay P s).Q ∧ Prologued (lay P s) (fun j => word t.mem (lay P s).Q (8 * j)) := by
  have hL := lay_ok h
  have hnQ := hL.nQ
  have hpQ : P ≤ (lay P s).Q.toNat := hL.pQ
  obtain ⟨hrd, hwr⟩ := spec_rdwr h
  have hfr : ∀ (u : State) d n, u.wr = (entered s).wr → d + n ≤ frameBytes →
      InRegions u.wr ((lay P s).Q + BitVec.ofNat 64 d) n :=
    fun u d n hu hd => ⟨(lay P s).FR, by rw [hu, entered_wr P]; simp,
      Offset.contains_base _ hd (by unfold frameBytes at hd; omega)⟩
  have harg : ∀ (u : State) d, u.rd = s.rd → 288 ≤ d → d + 8 ≤ 408 →
      InRegions (u.rd ++ u.wr) ((lay P s).Q + BitVec.ofNat 64 d) 8 :=
    fun u d hu h₁ h₂ => ⟨(lay P s).ARGS, by rw [hu, hrd]; simp, Offset.contains _ h₁ (by omega) (by omega)⟩
  have eLr : (entered s).mem.readW ((lay P s).Q + BitVec.ofNat 64 272) 64 = s.gpr .x30 := by
    rw [entered_mem P, Mem.readW_writeW_self64]
  have eArg : ∀ j, j < 15 → (entered s).mem.readW ((lay P s).Q + BitVec.ofNat 64 (288 + 8 * j)) 64 =
      stackArg s j := by
    intro j hj
    rw [entered_mem P, Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide),
      stackArg, stackArgAddr, ← lay_Q P s, add_add]
  have eFr : Frame [(lay P s).STK] s.mem (entered s).mem := by
    rw [entered_mem P]
    refine (Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_
    show (⟨(lay P s).Q - BitVec.ofNat 64 P, P + 288⟩ : Region).Contains
      ((lay P s).Q + BitVec.ofNat 64 272) (64 / 8)
    rw [q_add (lay P s).Q P 272]
    exact Offset.contains_base _ (by omega) (by omega)
  rw [decPrologue_eq, List.append_assoc, WP.block_append_iff]
  -- `x9 = sp`.
  have h0 : WP isa (.block [.addSp .x9 0]) (entered s) fun t₀ => t₀ = (entered s).write .x .x9 (lay P s).Q := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Nat.reduceLT, ite_true, entered_sp P,
      BitVec.add_zero, Option.some.injEq, exists_eq_left']
  refine WP.mono h0 fun t₀ ht₀ => ?_
  subst ht₀
  have h9 : ((entered s).write .x .x9 (lay P s).Q).gpr .x9 = (lay P s).Q := by
    simp only [RegUpd.gpr_write, ite_true, Size.bits, BitVec.setWidth_eq]
  rw [WP.block_append_iff]
  refine WP.mono (Spill.save_wp (by decide) (fun p hp => ?_)) fun t₂ hs => ?_
  · rw [h9]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact hfr _ _ _ (RegUpd.wr_write ..) (by decide)
  have hsp₂ : t₂.sp = (lay P s).Q := hs.sp.trans ((RegUpd.sp_write ..).trans (entered_sp P s))
  have hrd₂ : t₂.rd = s.rd := hs.rd.trans (RegUpd.rd_write ..)
  have hwr₂ : t₂.wr = (entered s).wr := hs.wr.trans (RegUpd.wr_write ..)
  refine WP.mono (moves_ok argMoves_ok (t := t₂) (by rw [hs.gpr, h9, hsp₂])
    (fun p hp => by rw [hsp₂]; exact hfr _ _ _ hwr₂ (argMoves_ok p hp).2.1)
    (fun p hp => by
      have := (argMoves_ok p hp).2.2
      rw [hsp₂]; exact harg _ _ hrd₂ (by unfold arg frameBytes; omega) (by unfold arg frameBytes; omega)))
    fun u hm => ?_
  -- The memory.
  have M2 : t₂.mem = Spill.saveMem (entered s).mem (lay P s).Q ((entered s).write .x .x9 (lay P s).Q).gpr
      saveList := by
    rw [hs.mem, h9, RegUpd.mem_write]
  have F2 : Frame [⟨(lay P s).Q, 224⟩] (entered s).mem t₂.mem := by
    rw [M2]
    exact Spill.saveMem_frame_base (fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) (by decide) _ _ _
  have S2 : Spill.Saved (lay P s).Q ((entered s).write .x .x9 (lay P s).Q).gpr saveList t₂.mem := by
    rw [M2]; exact Spill.saveMem_saved (by decide) _ _ _
  have U : u.mem = moveMem t₂.mem (lay P s).Q t₂.mem argMoves := by rw [hm.mem, hsp₂]
  have hi₂ : ∀ d, 224 ≤ d → d + 8 ≤ 408 → t₂.mem.readW ((lay P s).Q + BitVec.ofNat 64 d) 64 =
      (entered s).mem.readW ((lay P s).Q + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ =>
    F2.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base _ (by omega) (by omega)) (by decide)
  -- Our stack arguments, unchanged.
  have uArg : ∀ j, j < 15 → u.mem.readW ((lay P s).Q + BitVec.ofNat 64 (288 + 8 * j)) 64 = stackArg s j := by
    intro j hj
    rw [U, moveMem_read argMoves_ok _ _ (fun p hp => by
      have := (argMoves_ok p hp).2.1; unfold frameBytes at this; omega) (by omega),
      hi₂ _ (by omega) (by omega), eArg j hj]
  have uMv : ∀ p ∈ argMoves, u.mem.readW ((lay P s).Q + BitVec.ofNat 64 p.2) 64 = stackArg s p.1 := by
    intro p hp
    have := (argMoves_ok p hp).2.2
    rw [U, moveMem_moved argMoves_ok argMoves_nodup _ _ p hp, show arg p.1 = 288 + 8 * p.1 from rfl,
      hi₂ _ (by omega) (by omega), eArg _ this]
  have uSv : ∀ r d, (r, d) ∈ saveList → u.mem.readW ((lay P s).Q + BitVec.ofNat 64 d) 64 = s.gpr r := by
    intro r d hrd
    rw [U, moveMem_read argMoves_ok _ _ (argMoves_apart (List.mem_map_of_mem (f := Prod.snd) hrd))
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hrd
          rcases hrd with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> (dsimp only; decide)),
      S2 (r, d) hrd]
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hrd
    rcases hrd with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
      exact RegUpd.gpr_write_of_ne _ _ _ (by dsimp only; decide)
  have F : Frame [⟨(lay P s).Q, 272⟩] (entered s).mem u.mem := by
    rw [U]
    refine Frame.trans (F2.sub fun r hr => ?_) ((moveMem_frame argMoves_ok _ _).sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by unfold frameBytes; omega)⟩
  have go : ∀ r, r ≠ .x9 → r ≠ .x10 → u.gpr r = s.gpr r := fun r h₁ h₂ => by
    rw [hm.other r h₂, hs.gpr]; exact RegUpd.gpr_write_of_ne _ _ _ h₁
  have w8 : ∀ d, word u.mem (lay P s).Q d = u.mem.readW ((lay P s).Q + BitVec.ofNat 64 d) 64 := fun _ => rfl
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩⟩
  · rw [hm.rd, hrd₂, hrd]
  · rw [hm.wr, hwr₂, entered_wr P, hwr]
  · rw [hm.sp, hsp₂]
  · intro r hr _
    exact go r (preserved_ne hr (by decide)) (preserved_ne hr (by decide))
  · intro r _
    rw [hm.v, hs.v, RegUpd.v_write, entered_v]
  · rw [U, moveMem_read argMoves_ok _ _ (by decide) (by omega), hi₂ 272 (by omega) (by omega), eLr]
  · intro j hj
    rw [uArg j hj, ourArg_lay P s j hj]
  · have hk : (lay P s).STK ∈ [(lay P s).OUT, (lay P s).ML, (lay P s).SCR, (lay P s).STK] := by simp
    refine Frame.trans (eFr.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact hk) (F.sub fun r hr => ?_)
    rw [List.mem_singleton.mp hr]
    have h272 := DLay.Ok.sub_stk (L := lay P s) (d := 0) (n := 272) (by omega)
    rw [show (lay P s).Q + BitVec.ofNat 64 0 = (lay P s).Q from BitVec.add_zero _] at h272
    exact ⟨(lay P s).STK, hk, h272⟩
  · rw [hm.other .x9 (by decide), hs.gpr, h9]
  · rw [w8]; exact uMv (13, sScr) (by decide)
  · rw [w8]; exact uSv .x0 sOut (by simp)
  · rw [w8]; exact uSv .x3 sN (by simp)
  · rw [w8]; exact uSv .x4 sK (by simp)
  · rw [w8]; exact uSv .x5 sE (by simp)
  · rw [w8]; exact uSv .x6 sEl (by simp)
  · rw [w8]; exact uMv (14, sScrLen) (by decide)
  · rw [w8]; exact uMv (9, sLab) (by decide)
  · rw [w8]; exact uMv (10, sLabLen) (by decide)
  · rw [w8]; exact uSv .x2 sMl (by simp)
  · rw [w8]; exact uSv .x7 0 (by simp)
  · intro j hj
    rw [w8, uMv _ (mem_argMoves hj), ourArg_lay P s j (by omega)]

end VG.Proof.RsaOaep.AArch64.Dec
