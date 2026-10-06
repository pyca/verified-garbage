import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecLay
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncEntry

/-!
# RSAES-PKCS1-v1_5 decryption on AArch64: entering the frames

The layout of a call (`lay`), what the shared contract says of it
(`lay_ok`), and the first block (`setup`), run from the state in which the
inner frame's body starts (`entered`): it saves our register arguments to
their slots (`Spill.save_wp`), moves our stack arguments to theirs and to the
private-key operation's (`moves_ok`), and sets the call's registers,
establishing `Ctx` (`entry_ok`).
-/

namespace VG.Proof.RsaPkcs1Enc.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Decrypt
open VG.Proof.RsaPkcs1Enc.AArch64.Enc (add_add read8 write8 toNat_sub_k)

/-- The shared contract, with `P + 224` bytes of stack. -/
abbrev decSpec (P : Nat) : Contract isa := Spec.RsaPkcs1Enc.decryptContract AArch64.abi (P + 224)

/-- The layout of a call from `s`, with `P` bytes of stack for the calls. -/
def lay (P : Nat) (s : State) : Lay :=
  ⟨s.gpr .x0, s.gpr .x1, s.gpr .x2, s.gpr .x3, s.gpr .x4, s.gpr .x5, s.gpr .x6, s.gpr .x7,
    stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4, stackArg s 5, stackArg s 6,
    stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10, stackArg s 11, stackArg s 12, stackArg s 13,
    stackArg s 14, s.sp - BitVec.ofNat 64 224, P⟩

theorem lay_Q (P : Nat) (s : State) : (lay P s).Q + BitVec.ofNat 64 224 = s.sp := BitVec.sub_add_cancel _ _

theorem lay_args (P : Nat) (s : State) : (lay P s).Q + BitVec.ofNat 64 224 = stackArgAddr s 0 := by
  rw [lay_Q, stackArgAddr]; exact (BitVec.add_zero _).symm

theorem lay_stk (P : Nat) (s : State) :
    (lay P s).Q - BitVec.ofNat 64 P = s.sp - BitVec.ofNat 64 (P + 224) := by
  simp only [lay]
  rw [BitVec.sub_sub, BitVec.ofNat_add_ofNat, Nat.add_comm 224 P]

theorem forall_ro {L : Lay} {F : Region → Prop}
    (h : F L.N ∧ F L.E ∧ F L.D ∧ F L.INP ∧ F L.PP ∧ F L.QQ ∧ F L.DP ∧ F L.DQ ∧ F L.QI) : ∀ R ∈ L.ro, F R := by
  intro R hR
  simp only [Lay.ro, List.mem_cons, List.not_mem_nil, or_false] at hR
  obtain ⟨a, b, c, d, e, f, g, i, j⟩ := h
  rcases hR with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

theorem lay_ok {P : Nat} {s : State} (h : (decSpec P).pre s) : (lay P s).Ok := by
  sig_pre [Spec.RsaPkcs1Enc.decryptContract, Spec.RsaPkcs1Enc.decryptSig, AArch64.abi, AArch64.argRegs,
    _root_.List.range, _root_.List.range.loop, List.append_eq] at h
  obtain ⟨hsp, hsp2, -, -,
    oM, oN, oE, oD, oI, oP, oQ, oDP, oDQ, oQI, oS, oA,
    mN, mE, mD, mI, mP, mQ, mDP, mDQ, mQI, mS, mA,
    nS, eS, dS, iS, pS, qS, dpS, dqS, qiS, sA,
    kO, kM, kN, kE, kD, kI, kP, kQ, kDP, kDQ, kQI, kS, -,
    bO, bM, bN, bE, bD, bI, bP, bQ, bDP, bDQ, bQI, bS,
    kv, hk1, hk2, el1, elk, dl1, dlk, pl1, plk, ql1, qlk, hdp, hqi, hdq, slk⟩ := h
  simp only [hk1, hk2, hdp, hqi, hdq] at oA oN oE oD oI oP oQ oDP oDQ oQI oS oM mI mDP mDQ mQI iS dpS dqS qiS
  simp only [hk1, hk2, hdp, hqi, hdq] at kO kI kDP kDQ kQI bO bI bDP bDQ bQI
  have eA : (lay P s).ARGS = ⟨stackArgAddr s 0, 120⟩ := by simp only [Lay.ARGS, lay_args]
  have eK : (lay P s).STK = ⟨s.sp - BitVec.ofNat 64 (P + 224), P + 224⟩ := by
    show (⟨(lay P s).Q - BitVec.ofNat 64 P, P + 224⟩ : Region) = _
    rw [lay_stk]
  have hQ : (lay P s).Q.toNat = s.sp.toNat - 224 := toNat_sub_k (by omega)
  refine ⟨oM, oS, mS, forall_ro ⟨oN, oE, oD, oI, oP, oQ, oDP, oDQ, oQI⟩,
    forall_ro ⟨mN, mE, mD, mI, mP, mQ, mDP, mDQ, mQI⟩,
    forall_ro ⟨nS.symm, eS.symm, dS.symm, iS.symm, pS.symm, qS.symm, dpS.symm, dqS.symm, qiS.symm⟩, eA ▸ oA, eA ▸ mA,
    eA ▸ sA, eK ▸ kO, eK ▸ kM, eK ▸ kS, forall_ro ⟨eK ▸ kN, eK ▸ kE, eK ▸ kD, eK ▸ kI, eK ▸ kP, eK ▸ kQ, eK ▸ kDP,
    eK ▸ kDQ, eK ▸ kQI⟩, bO, bM, bS, forall_ro ⟨bN, bE, bD, bI, bP, bQ, bDP, bDQ, bQI⟩, by omega,
    by simp only [lay] at hQ ⊢; omega, kv, hk1, hk2, el1, elk, dl1, dlk, pl1, plk, ql1, qlk, hdp, hqi, hdq, slk⟩

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

theorem moveMem_frame {l : List (Nat × Nat)} (hl : MoveOk l) {B : Addr} (m m₀ : Mem) : Frame [⟨B, frameBytes⟩] m (moveMem m B m₀ l) := by
  suffices h : ∀ m', Frame [⟨B, frameBytes⟩] m m' → Frame [⟨B, frameBytes⟩] m (moveMem m' B m₀ l) from
    h m (Frame.refl _ _)
  induction l with
  | nil => exact fun _ h => h
  | cons p l ih =>
    obtain ⟨j, d⟩ := p
    intro m' h
    have hd := hl (j, d) List.mem_cons_self
    have hd2 : d + 8 ≤ 208 := hd.2.1
    exact ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)) _
      (h.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by unfold frameBytes; omega) (by omega)))

theorem moveMem_read {l : List (Nat × Nat)} (hl : MoveOk l) {B : Addr} (m m₀ : Mem) {a : Nat} (ha : ∀ p ∈ l, p.2 + 8 ≤ a ∨ a + 8 ≤ p.2) (ha' : a + 8 ≤ 344) :
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

/-! ## The setup -/

/-- The state in which the inner frame's body starts. -/
def entered (s : State) : State := allocated frameBytes (pushed .x30 s)

@[simp] theorem entered_rd (s : State) : (entered s).rd = s.rd := rfl
@[simp] theorem entered_gpr (s : State) : (entered s).gpr = s.gpr := rfl
@[simp] theorem entered_v (s : State) : (entered s).v = s.v := rfl

theorem entered_sp (P : Nat) (s : State) : (entered s).sp = (lay P s).Q := by
  show s.sp - 16 - BitVec.ofNat 64 208 = s.sp - BitVec.ofNat 64 224
  rw [BitVec.sub_sub]; rfl

theorem lr_slot (P : Nat) (s : State) : s.sp - 16 = (lay P s).Q + BitVec.ofNat 64 208 := by
  show s.sp - 16 = s.sp - BitVec.ofNat 64 224 + BitVec.ofNat 64 208
  bv_omega

theorem entered_wr (P : Nat) (s : State) :
    (entered s).wr = (lay P s).FR :: (lay P s).LR :: s.wr := by
  show (⟨s.sp - 16 - BitVec.ofNat 64 208, 208⟩ : Region) :: ⟨s.sp - 16, 16⟩ :: s.wr = _
  rw [show s.sp - 16 - BitVec.ofNat 64 208 = (lay P s).Q from entered_sp P s, lr_slot P]
  rfl

theorem entered_mem (P : Nat) (s : State) :
    (entered s).mem = s.mem.writeW ((lay P s).Q + BitVec.ofNat 64 208) (s.gpr .x30) := by
  show s.mem.write (s.sp - 16) 8 (s.gpr .x30) = _
  rw [lr_slot P, write8]

theorem ourArg_lay (P : Nat) (s : State) : ∀ j, j < 15 → ourArg (lay P s) j = stackArg s j
  | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl | 5, _ => rfl | 6, _ => rfl
  | 7, _ => rfl | 8, _ => rfl | 9, _ => rfl | 10, _ => rfl | 11, _ => rfl | 12, _ => rfl | 13, _ => rfl
  | 14, _ => rfl

theorem saves_eq : saves = [.addSp .x9 0] ++ Spill.saveCode .x9
    [(.x0, oOut), (.x2, oML), (.x3, oN), (.x4, oK), (.x5, oE), (.x6, oEl), (.x7, oD)] := rfl

/-- The call's registers once the slots are written. -/
structure Ready (L : Lay) (t : State) : Prop where
  x0 : t.gpr .x0 = L.out
  x1 : t.gpr .x1 = L.k
  x2 : t.gpr .x2 = L.n
  x3 : t.gpr .x3 = L.k
  x4 : t.gpr .x4 = L.e
  x5 : t.gpr .x5 = L.el
  x6 : t.gpr .x6 = L.inp
  x7 : t.gpr .x7 = L.k

theorem privRegs_ok {t : State} (ha : InRegions (t.rd ++ t.wr) (t.sp + BitVec.ofNat 64 (arg 1)) 8) :
    WP isa (.block privRegs) t fun u => u.rd = t.rd ∧ u.wr = t.wr ∧ u.sp = t.sp ∧ u.v = t.v ∧ u.mem = t.mem ∧
      u.gpr .x0 = t.gpr .x0 ∧ u.gpr .x1 = t.gpr .x4 ∧ u.gpr .x2 = t.gpr .x3 ∧ u.gpr .x3 = t.gpr .x4 ∧
      u.gpr .x4 = t.gpr .x5 ∧ u.gpr .x5 = t.gpr .x6 ∧ u.gpr .x6 = t.mem.readW (t.sp + BitVec.ofNat 64 (arg 1)) 64 ∧
      u.gpr .x7 = t.gpr .x4 ∧ ∀ r ∈ preserved, u.gpr r = t.gpr r := by
  have ha' : InRegions (t.rd ++ t.wr) (t.sp + BitVec.ofNat 64 232) 8 := ha
  show WP isa (.block privRegs) t fun u => u.rd = t.rd ∧ u.wr = t.wr ∧ u.sp = t.sp ∧ u.v = t.v ∧ u.mem = t.mem ∧
      u.gpr .x0 = t.gpr .x0 ∧ u.gpr .x1 = t.gpr .x4 ∧ u.gpr .x2 = t.gpr .x3 ∧ u.gpr .x3 = t.gpr .x4 ∧
      u.gpr .x4 = t.gpr .x5 ∧ u.gpr .x5 = t.gpr .x6 ∧ u.gpr .x6 = t.mem.readW (t.sp + BitVec.ofNat 64 232) 64 ∧
      u.gpr .x7 = t.gpr .x4 ∧ ∀ r ∈ preserved, u.gpr r = t.gpr r
  apply WP.of_runBlock
  simp only [privRegs, mov, arg, frameBytes, runBlock_cons, runStep_some, runBlock_nil, exec, State.read, State.load,
    Size.bits, BitVec.setWidth_eq, BitVec.or_self, Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT,
    and_self, ite_true, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, RegUpd.v_write, ha',
    read8, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (intro r hr
       simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
         simp only [RegUpd.gpr_write, reduceCtorEq, ite_false])
    | simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]

/-- The regions the contract grants. -/
theorem spec_rdwr {P : Nat} {s : State} (h : (decSpec P).pre s) :
    s.rd = [(lay P s).N, (lay P s).E, (lay P s).D, (lay P s).INP, (lay P s).PP, (lay P s).QQ, (lay P s).DP,
      (lay P s).DQ, (lay P s).QI, (lay P s).ARGS] ∧ s.wr = [(lay P s).OUT, (lay P s).ML, (lay P s).SCR] := by
  have hL := lay_ok h
  sig_pre [Spec.RsaPkcs1Enc.decryptContract, Spec.RsaPkcs1Enc.decryptSig, AArch64.abi, AArch64.argRegs,
    _root_.List.range, _root_.List.range.loop, List.append_eq] at h
  obtain ⟨-, -, hrd, hwr, -⟩ := h
  have hk1 : (s.gpr .x1).toNat = (s.gpr .x4).toNat := hL.olk
  have hk2 : (stackArg s 2).toNat = (s.gpr .x4).toNat := hL.ilk
  have hdp : (stackArg s 8).toNat = (stackArg s 4).toNat := hL.dpl
  have hqi : (stackArg s 12).toNat = (stackArg s 4).toNat := hL.qil
  have hdq : (stackArg s 10).toNat = (stackArg s 6).toNat := hL.dql
  rw [hrd, hwr, hk1, hk2, hdp, hqi, hdq, ← lay_args P]
  exact ⟨rfl, rfl⟩

theorem argMoves_ok : MoveOk argMoves := by decide

theorem argMoves_nodup : (argMoves.map Prod.snd).Nodup := by decide

theorem mem_argMoves {j : Nat} (hj : j < 12) : (j + 3, 8 * j) ∈ argMoves :=
  List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)

/-- The saves' slots are not the moves'. -/
theorem argMoves_apart {a : Nat} (ha : a ∈ [oOut, oML, oN, oK, oE, oEl, oD]) :
    ∀ p ∈ argMoves, p.2 + 8 ≤ a ∨ a + 8 ≤ p.2 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem entry_ok {P : Nat} {s : State} (h : (decSpec P).pre s) :
    WP isa (.block setup) (entered s) fun t => Ctx (lay P s) s.gpr s.v s.mem t ∧ Ready (lay P s) t := by
  have hL := lay_ok h
  have hnQ := hL.nQ
  have hpQ : P ≤ (lay P s).Q.toNat := hL.pQ
  obtain ⟨hrd, hwr⟩ := spec_rdwr h
  have hfr : ∀ (u : State) d n, u.wr = (entered s).wr → d + n ≤ frameBytes →
      InRegions u.wr ((lay P s).Q + BitVec.ofNat 64 d) n :=
    fun u d n hu hd => ⟨(lay P s).FR, by rw [hu, entered_wr P]; simp,
      Offset.contains_base _ hd (by unfold frameBytes at hd; omega)⟩
  have harg : ∀ (u : State) d, u.rd = s.rd → 224 ≤ d → d + 8 ≤ 344 →
      InRegions (u.rd ++ u.wr) ((lay P s).Q + BitVec.ofNat 64 d) 8 :=
    fun u d hu h₁ h₂ => ⟨(lay P s).ARGS, by rw [hu, hrd]; simp, Offset.contains _ h₁ (by omega) (by omega)⟩
  have eLr : (entered s).mem.readW ((lay P s).Q + BitVec.ofNat 64 208) 64 = s.gpr .x30 := by
    rw [entered_mem P, Mem.readW_writeW_self64]
  have eArg : ∀ j, j < 15 → (entered s).mem.readW ((lay P s).Q + BitVec.ofNat 64 (224 + 8 * j)) 64 =
      stackArg s j := by
    intro j hj
    rw [entered_mem P, Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide),
      stackArg, stackArgAddr, ← lay_Q P s, add_add]
  have eFr : Frame [(lay P s).STK] s.mem (entered s).mem := by
    rw [entered_mem P]
    refine (Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_
    show (⟨(lay P s).Q - BitVec.ofNat 64 P, P + 224⟩ : Region).Contains
      ((lay P s).Q + BitVec.ofNat 64 208) (64 / 8)
    rw [Enc.q_add (lay P s).Q P 208]
    exact Offset.contains_base _ (by omega) (by omega)
  rw [setup, saves_eq, List.append_assoc, WP.block_append_iff]
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
  rw [WP.block_append_iff]
  refine WP.mono (moves_ok argMoves_ok (t := t₂) (by rw [hs.gpr, h9, hsp₂])
    (fun p hp => by rw [hsp₂]; exact hfr _ _ _ hwr₂ (argMoves_ok p hp).2.1)
    (fun p hp => by
      have := (argMoves_ok p hp).2.2
      rw [hsp₂]; exact harg _ _ hrd₂ (by unfold arg frameBytes; omega) (by unfold arg frameBytes; omega)))
    fun t₃ hm => ?_
  have hsp₃ : t₃.sp = (lay P s).Q := hm.sp.trans hsp₂
  refine WP.mono (privRegs_ok (t := t₃) (by
    rw [hsp₃, hm.rd, hm.wr]; exact harg _ _ hrd₂ (by unfold arg frameBytes; omega)
      (by unfold arg frameBytes; omega))) fun u hu => ?_
  obtain ⟨urd, uwr, usp, uv, um, u0, u1, u2, u3, u4, u5, u6, u7, upr⟩ := hu
  -- The memory.
  have M2 : t₂.mem = Spill.saveMem (entered s).mem (lay P s).Q ((entered s).write .x .x9 (lay P s).Q).gpr
      [(.x0, oOut), (.x2, oML), (.x3, oN), (.x4, oK), (.x5, oE), (.x6, oEl), (.x7, oD)] := by
    rw [hs.mem, h9, RegUpd.mem_write]
  have F2 : Frame [⟨(lay P s).Q, 152⟩] (entered s).mem t₂.mem := by
    rw [M2]
    exact Spill.saveMem_frame_base (fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) (by decide) _ _ _
  have S2 : Spill.Saved (lay P s).Q ((entered s).write .x .x9 (lay P s).Q).gpr
      [(.x0, oOut), (.x2, oML), (.x3, oN), (.x4, oK), (.x5, oE), (.x6, oEl), (.x7, oD)] t₂.mem := by
    rw [M2]; exact Spill.saveMem_saved (by decide) _ _ _
  have U : u.mem = moveMem t₂.mem (lay P s).Q t₂.mem argMoves := by rw [um, hm.mem, hsp₂]
  have hi₂ : ∀ d, 152 ≤ d → d + 8 ≤ 344 → t₂.mem.readW ((lay P s).Q + BitVec.ofNat 64 d) 64 =
      (entered s).mem.readW ((lay P s).Q + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ =>
    F2.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base _ (by omega) (by omega)) (by decide)
  -- Our stack arguments, unchanged.
  have uArg : ∀ j, j < 15 → u.mem.readW ((lay P s).Q + BitVec.ofNat 64 (224 + 8 * j)) 64 = stackArg s j := by
    intro j hj
    rw [U, moveMem_read argMoves_ok _ _ (fun p hp => by
      have := (argMoves_ok p hp).2.1; unfold frameBytes at this; omega) (by omega),
      hi₂ _ (by omega) (by omega), eArg j hj]
  have uMv : ∀ p ∈ argMoves, u.mem.readW ((lay P s).Q + BitVec.ofNat 64 p.2) 64 = stackArg s p.1 := by
    intro p hp
    have := (argMoves_ok p hp).2.2
    rw [U, moveMem_moved argMoves_ok argMoves_nodup _ _ p hp, show arg p.1 = 224 + 8 * p.1 from rfl,
      hi₂ _ (by omega) (by omega), eArg _ this]
  have uSv : ∀ r d, (r, d) ∈ [(Reg.x0, oOut), (.x2, oML), (.x3, oN), (.x4, oK), (.x5, oE), (.x6, oEl), (.x7, oD)] →
      u.mem.readW ((lay P s).Q + BitVec.ofNat 64 d) 64 = s.gpr r := by
    intro r d hrd
    rw [U, moveMem_read argMoves_ok _ _ (argMoves_apart (List.mem_map_of_mem (f := Prod.snd) hrd))
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hrd
          rcases hrd with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> (dsimp only; decide)),
      S2 (r, d) hrd]
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hrd
    rcases hrd with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
      exact RegUpd.gpr_write_of_ne _ _ _ (by dsimp only; decide)
  have F : Frame [⟨(lay P s).Q, 208⟩] (entered s).mem u.mem := by
    rw [U]
    refine Frame.trans (F2.sub fun r hr => ?_) ((moveMem_frame argMoves_ok _ _).sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by unfold frameBytes; omega)⟩
  have go : ∀ r, r ≠ .x9 → r ≠ .x10 → t₃.gpr r = s.gpr r := fun r h₁ h₂ => by
    rw [hm.other r h₂, hs.gpr]; exact RegUpd.gpr_write_of_ne _ _ _ h₁
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [urd, hm.rd, hrd₂, hrd]
  · rw [uwr, hm.wr, hwr₂, entered_wr P, hwr]
  · rw [usp, hsp₃]
  · intro r hr _
    rw [upr r hr, go r (Enc.preserved_ne hr (by decide)) (Enc.preserved_ne hr (by decide))]
  · intro r _
    rw [uv, hm.v, hs.v, RegUpd.v_write, entered_v]
  · intro j hj
    rw [uMv _ (mem_argMoves hj), ourArg_lay P s (j + 3) (by omega)]
  · exact uSv .x0 oOut (by simp)
  · exact uSv .x2 oML (by simp)
  · exact uSv .x3 oN (by simp)
  · exact uSv .x4 oK (by simp)
  · exact uSv .x5 oE (by simp)
  · exact uSv .x6 oEl (by simp)
  · exact uSv .x7 oD (by simp)
  · exact uMv (0, oDl) (by decide)
  · exact uMv (1, oIn) (by decide)
  · exact uMv (13, oScr) (by decide)
  · rw [U, moveMem_read argMoves_ok _ _ (by decide) (by omega), hi₂ 208 (by omega) (by omega), eLr]
  · intro j hj
    rw [uArg j hj, ourArg_lay P s j hj]
  · have hk : (lay P s).STK ∈ [(lay P s).OUT, (lay P s).ML, (lay P s).SCR, (lay P s).STK] := by simp
    refine Frame.trans (eFr.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact hk) (F.sub fun r hr => ?_)
    rw [List.mem_singleton.mp hr]
    have h208 := Lay.Ok.sub_stk (L := lay P s) (d := 0) (n := 208) (by omega)
    rw [show (lay P s).Q + BitVec.ofNat 64 0 = (lay P s).Q from BitVec.add_zero _] at h208
    exact ⟨(lay P s).STK, hk, h208⟩
  · rw [u0]; exact go .x0 (by decide) (by decide)
  · rw [u1]; exact go .x4 (by decide) (by decide)
  · rw [u2]; exact go .x3 (by decide) (by decide)
  · rw [u3]; exact go .x4 (by decide) (by decide)
  · rw [u4]; exact go .x5 (by decide) (by decide)
  · rw [u5]; exact go .x6 (by decide) (by decide)
  · rw [u6, ← um, hsp₃]; exact uArg 1 (by decide)
  · rw [u7]; exact go .x4 (by decide) (by decide)

end VG.Proof.RsaPkcs1Enc.AArch64.Dec