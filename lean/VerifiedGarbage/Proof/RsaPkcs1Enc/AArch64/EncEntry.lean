import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncLay
import VerifiedGarbage.Proof.Framework.AArch64.Spill

/-!
# RSAES-PKCS1-v1_5 encryption on AArch64: entering the frames

The layout of a call (`lay`), what its precondition says of it (`lay_ok`),
and the first block (`setup`), run from the state in which the inner frame's
body starts (`entered`): it writes the slots, the call's stack arguments and
the first two bytes of `EM`, establishing `Ctx` (`entry_ok`).
-/

namespace VG.Proof.RsaPkcs1Enc.AArch64.Enc

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Encrypt

/-- The layout of a call from `s`, with `P` bytes of stack for the call. -/
def lay (P : Nat) (s : State) : Lay :=
  ⟨s.gpr .x0, s.gpr .x1, s.gpr .x2, s.gpr .x3, s.gpr .x4, s.gpr .x5, s.gpr .x6, s.gpr .x7,
    stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, s.sp - BitVec.ofNat 64 1088, P⟩

theorem lay_Q (P : Nat) (s : State) : (lay P s).Q + BitVec.ofNat 64 1088 = s.sp := BitVec.sub_add_cancel _ _

theorem lay_args (P : Nat) (s : State) : (lay P s).Q + BitVec.ofNat 64 1088 = stackArgAddr s 0 := by
  rw [lay_Q, stackArgAddr]; exact (BitVec.add_zero _).symm

theorem lay_stk (P : Nat) (s : State) :
    (lay P s).Q - BitVec.ofNat 64 P = s.sp - BitVec.ofNat 64 (P + 1088) := by
  simp only [lay]
  rw [BitVec.sub_sub, BitVec.ofNat_add_ofNat, Nat.add_comm 1088 P]

theorem toNat_sub_k {a : Addr} {k : Nat} (h : k ≤ a.toNat) : (a - BitVec.ofNat 64 k).toNat = a.toNat - k := by
  have := a.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega),
    show 2 ^ 64 - k + a.toNat = a.toNat - k + 2 ^ 64 by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

theorem lay_ok {P : Nat} {s : State} (h : (encK P).pre s) : (lay P s).Ok := by
  obtain ⟨hsp, hsp2, -, -, oN, oE, oM, oP, oS, oA, nS, eS, mS, pS, sA, kO, kN, kE, kM, kP, kS, -,
    bO, bN, bE, bM, bP, bS, kv, olk, el1, elk, mlk, plk, slk⟩ := h
  have eO : (lay P s).OUT = ⟨s.gpr .x0, (s.gpr .x1).toNat⟩ := by simp only [Lay.OUT, lay, olk]
  have eA : (lay P s).ARGS = ⟨stackArgAddr s 0, 32⟩ := by simp only [Lay.ARGS, lay_args]
  have eK : (lay P s).STK = ⟨s.sp - BitVec.ofNat 64 (P + 1088), P + 1088⟩ := by
    show (⟨(lay P s).Q - BitVec.ofNat 64 P, P + 1088⟩ : Region) = _
    rw [lay_stk]
  have hQ : (lay P s).Q.toNat = s.sp.toNat - 1088 := toNat_sub_k (by omega)
  exact ⟨eO ▸ oN, eO ▸ oE, eO ▸ oM, eO ▸ oP, eO ▸ oS, by rw [eA, eO]; exact oA, nS, eS, mS, pS,
    by rw [eA]; exact sA, by rw [eK, eO]; exact kO, eK ▸ kN, eK ▸ kE, eK ▸ kM, eK ▸ kP, eK ▸ kS,
    by simp only [lay]; omega, bN, bE, bM, bP, bS, by omega, by simp only [lay] at hQ ⊢; omega, kv, olk, el1,
    elk, mlk, plk, slk⟩

/-- The state in which the inner frame's body starts. -/
def entered (s : State) : State := allocated frameBytes (pushed .x30 s)

@[simp] theorem entered_rd (s : State) : (entered s).rd = s.rd := rfl
@[simp] theorem entered_gpr (s : State) : (entered s).gpr = s.gpr := rfl
@[simp] theorem entered_v (s : State) : (entered s).v = s.v := rfl

theorem entered_sp (P : Nat) (s : State) : (entered s).sp = (lay P s).Q := by
  show s.sp - 16 - BitVec.ofNat 64 1072 = s.sp - BitVec.ofNat 64 1088
  rw [BitVec.sub_sub]; rfl

theorem lr_slot (P : Nat) (s : State) : s.sp - 16 = (lay P s).Q + BitVec.ofNat 64 1072 := by
  show s.sp - 16 = s.sp - BitVec.ofNat 64 1088 + BitVec.ofNat 64 1072
  bv_omega

theorem entered_wr (P : Nat) (s : State) :
    (entered s).wr = (lay P s).FR :: (lay P s).LR :: s.wr := by
  show (⟨s.sp - 16 - BitVec.ofNat 64 1072, 1072⟩ : Region) :: ⟨s.sp - 16, 16⟩ :: s.wr = _
  rw [show s.sp - 16 - BitVec.ofNat 64 1072 = (lay P s).Q from entered_sp P s, lr_slot P]
  rfl

theorem write8 (m : Mem) (a : Addr) (v : BitVec 64) : m.write a 8 v = m.writeW a v := by
  simp only [Mem.writeW, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq]

theorem read8 (m : Mem) (a : Addr) : m.read a 8 = m.readW a 64 := by
  simp only [Mem.readW, Nat.reduceDiv, BitVec.setWidth_eq]

theorem entered_mem (P : Nat) (s : State) :
    (entered s).mem = s.mem.writeW ((lay P s).Q + BitVec.ofNat 64 1072) (s.gpr .x30) := by
  show s.mem.write (s.sp - 16) 8 (s.gpr .x30) = _
  rw [lr_slot P, write8]

/-- The registers once the slots are written, and the first two bytes of `EM`. -/
structure Setup (L : Lay) (g : Reg → BitVec 64) (t : State) : Prop where
  x0 : t.gpr .x0 = g .x0
  x1 : t.gpr .x1 = g .x1
  x2 : t.gpr .x2 = g .x2
  x3 : t.gpr .x3 = g .x3
  x4 : t.gpr .x4 = g .x4
  x5 : t.gpr .x5 = g .x5
  x6 : t.gpr .x6 = g .x6
  x7 : t.gpr .x7 = g .x7
  x11 : t.gpr .x11 = L.ps
  x12 : t.gpr .x12 = L.pl
  x13 : t.gpr .x13 = L.Q + BitVec.ofNat 64 (oEM + 2)
  x14 : t.gpr .x14 = 0
  x15 : t.gpr .x15 = 1
  b0 : t.mem (L.Q + BitVec.ofNat 64 oEM) = 0
  b1 : t.mem (L.Q + BitVec.ofNat 64 (oEM + 1)) = 2

theorem saves_eq : saves = Spill.saveCode .x9 [(.x10, 0), (.x11, 8), (.x0, oOut), (.x3, oK)] := rfl

/-- The stack arguments on entry, in the frames. -/
theorem arg_mem {P : Nat} {s : State} {j : Nat} :
    s.mem.readW ((lay P s).Q + BitVec.ofNat 64 (1088 + 8 * j)) 64 = stackArg s j := by
  rw [stackArg, stackArgAddr, ← lay_Q P s, add_add]

/-- After `loadArgs`. -/
structure Loaded (s t : State) : Prop where
  rd : t.rd = (entered s).rd
  wr : t.wr = (entered s).wr
  sp : t.sp = (entered s).sp
  v : t.v = s.v
  mem : t.mem = (entered s).mem
  x9 : t.gpr .x9 = (entered s).sp
  x10 : t.gpr .x10 = stackArg s 2
  x11 : t.gpr .x11 = stackArg s 3
  other : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → t.gpr r = s.gpr r

theorem loadArgs_ok {P : Nat} {s : State} (h : (encK P).pre s) :
    WP isa (.block loadArgs) (entered s) (Loaded s) := by
  have hL := lay_ok h
  have hnQ := hL.nQ
  have ha : ∀ j, j < 4 → InRegions ((entered s).rd ++ (entered s).wr)
      ((lay P s).Q + BitVec.ofNat 64 (1088 + 8 * j)) 8 :=
    fun j hj => ⟨(lay P s).ARGS, by rw [entered_rd, h.2.2.1, ← lay_args P]; simp,
      Offset.contains _ (by omega) (by omega) (by omega)⟩
  have a2 : InRegions ((entered s).rd ++ (entered s).wr) ((lay P s).Q + BitVec.ofNat 64 1104) 8 := ha 2 (by decide)
  have a3 : InRegions ((entered s).rd ++ (entered s).wr) ((lay P s).Q + BitVec.ofNat 64 1112) 8 := ha 3 (by decide)
  have m2 : (entered s).mem.readW ((lay P s).Q + BitVec.ofNat 64 1104) 64 = stackArg s 2 := by
    rw [entered_mem P, Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
    exact arg_mem (j := 2)
  have m3 : (entered s).mem.readW ((lay P s).Q + BitVec.ofNat 64 1112) 64 = stackArg s 3 := by
    rw [entered_mem P, Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
    exact arg_mem (j := 3)
  apply WP.of_runBlock
  simp only [loadArgs, arg, frameBytes, runBlock_cons, runStep_some, runBlock_nil, exec, State.load,
    BitVec.setWidth_eq, Option.map_some, Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod,
    Nat.reduceLT, and_self, ite_true, entered_sp P, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write,
    RegUpd.mem_write, a2, a3, read8, m2, m3, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, rfl, by simp only [RegUpd.sp_write, entered_sp P], rfl, rfl,
    by simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, entered_sp P, BitVec.add_zero],
    by simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq],
    by simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq],
    fun r h9 h10 h11 => by simp only [RegUpd.gpr_write, h9, h10, h11, ite_false, entered_gpr]⟩

/-- The four saves. -/
abbrev saveList : List (Reg × Nat) := [(.x10, 0), (.x11, 8), (.x0, oOut), (.x3, oK)]

/-- After `emStart`, from the state `t` after the saves. -/
structure Started (s t u : State) : Prop where
  rd : u.rd = t.rd
  wr : u.wr = t.wr
  sp : u.sp = t.sp
  v : u.v = t.v
  mem : u.mem = (t.mem.write (t.sp + BitVec.ofNat 64 oEM) 1 0#8).write (t.sp + BitVec.ofNat 64 (oEM + 1)) 1 2#8
  x11 : u.gpr .x11 = stackArg s 0
  x12 : u.gpr .x12 = stackArg s 1
  x13 : u.gpr .x13 = t.sp + BitVec.ofNat 64 (oEM + 2)
  x14 : u.gpr .x14 = 0
  x15 : u.gpr .x15 = 1
  other : ∀ r, r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → r ≠ .x14 → r ≠ .x15 → u.gpr r = t.gpr r

theorem emStart_ok {s t : State} (h9 : t.gpr .x9 = t.sp)
    (w40 : InRegions t.wr (t.sp + BitVec.ofNat 64 40) 1) (w41 : InRegions t.wr (t.sp + BitVec.ofNat 64 41) 1)
    (a0 : InRegions (t.rd ++ t.wr) (t.sp + BitVec.ofNat 64 1088) 8)
    (a1 : InRegions (t.rd ++ t.wr) (t.sp + BitVec.ofNat 64 1096) 8)
    (m0 : t.mem.readW (t.sp + BitVec.ofNat 64 1088) 64 = stackArg s 0)
    (m1 : t.mem.readW (t.sp + BitVec.ofNat 64 1096) 64 = stackArg s 1) :
    WP isa (.block emStart) t (Started s t) := by
  apply WP.of_runBlock
  simp (disch := enc_disch) only [emStart, oEM, arg, frameBytes, runBlock_cons, runStep_some, runBlock_nil, exec,
    Size.bits, BitVec.shiftLeft_zero, addr, State.load, State.store, State.read, BitVec.setWidth_eq, Option.map_some,
    Option.bind_some, Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self, ite_true,
    RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, RegUpd.gpr_write, reduceCtorEq,
    ite_false, h9, w40, w41, a0, a1, read8, Bytes.readW_write_sep, m0, m1, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, fun r h10 h11 h12 h13 h14 h15 => ?_⟩
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]; rfl
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]; rfl
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]; rfl
  · simp only [RegUpd.gpr_write, h10, h11, h12, h13, h14, h15, ite_false]

theorem preserved_ne {r : Reg} (hr : r ∈ preserved) {d : Reg} (hd : d ∉ preserved) : r ≠ d :=
  fun e => hd (e ▸ hr)

theorem entry_ok {P : Nat} {s : State} (h : (encK P).pre s) :
    WP isa (.block setup) (entered s) fun t => Ctx (lay P s) s.gpr s.v s.mem t ∧ Setup (lay P s) s.gpr t := by
  have hL := lay_ok h
  have hnQ := hL.nQ
  have olk := hL.olk
  have hfr : ∀ (u : State) d n, u.wr = (entered s).wr → d + n ≤ frameBytes → InRegions u.wr ((lay P s).Q + BitVec.ofNat 64 d) n :=
    fun u d n hu hd => ⟨(lay P s).FR, by rw [hu, entered_wr P]; simp, Offset.contains_base _ hd (by unfold frameBytes at hd; omega)⟩
  have harg : ∀ (u : State) d, u.rd = s.rd → 1088 ≤ d → d + 8 ≤ 1120 → InRegions (u.rd ++ u.wr) ((lay P s).Q + BitVec.ofNat 64 d) 8 :=
    fun u d hu h₁ h₂ => ⟨(lay P s).ARGS, by rw [hu, h.2.2.1, ← lay_args P]; simp, Offset.contains _ h₁ (by omega) (by omega)⟩
  -- The memory on entry to the frames' body.
  have eLr : (entered s).mem.readW ((lay P s).Q + BitVec.ofNat 64 1072) 64 = s.gpr .x30 := by
    rw [entered_mem P, Mem.readW_writeW_self64]
  have eArg : ∀ j, j < 4 → (entered s).mem.readW ((lay P s).Q + BitVec.ofNat 64 (1088 + 8 * j)) 64 = stackArg s j := by
    intro j hj
    rw [entered_mem P, Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
    exact arg_mem
  have hpQ : P ≤ (lay P s).Q.toNat := hL.pQ
  have eFr : Frame [(lay P s).STK] s.mem (entered s).mem := by
    rw [entered_mem P]
    refine (Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_
    show (⟨(lay P s).Q - BitVec.ofNat 64 P, P + 1088⟩ : Region).Contains
      ((lay P s).Q + BitVec.ofNat 64 1072) (64 / 8)
    rw [q_add (lay P s).Q P 1072]
    exact Offset.contains_base _ (by omega) (by omega)
  rw [setup, WP.block_append_iff]
  refine WP.mono (loadArgs_ok h) fun t ht => ?_
  rw [WP.block_append_iff, saves_eq]
  have h9 : t.gpr .x9 = (lay P s).Q := ht.x9.trans (entered_sp P s)
  refine WP.mono (Spill.save_wp (by decide) (fun p hp => ?_)) fun t₂ hs => ?_
  · rw [h9]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> exact hfr t _ _ ht.wr (by decide)
  have hsp₂ : t₂.sp = (lay P s).Q := hs.sp.trans (ht.sp.trans (entered_sp P s))
  have M2 : t₂.mem = Spill.saveMem t.mem (lay P s).Q t.gpr [(.x10, 0), (.x11, 8), (.x0, oOut), (.x3, oK)] := by
    rw [hs.mem, h9]
  have F2 : Frame [⟨(lay P s).Q, 32⟩] t.mem t₂.mem := by
    rw [M2]
    exact Spill.saveMem_frame_base (fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> decide) (by decide) _ _ _
  have S2 : Spill.Saved (lay P s).Q t.gpr [(.x10, 0), (.x11, 8), (.x0, oOut), (.x3, oK)] t₂.mem := by
    rw [M2]; exact Spill.saveMem_saved (by decide) _ _ _
  have keepHigh : ∀ d, 32 ≤ d → d + 8 ≤ 1120 → t₂.mem.readW ((lay P s).Q + BitVec.ofNat 64 d) 64 =
      (entered s).mem.readW ((lay P s).Q + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ => by
    rw [F2.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base _ (by omega) (by omega)) (by decide), ht.mem]
  have m0 : t₂.mem.readW (t₂.sp + BitVec.ofNat 64 1088) 64 = stackArg s 0 := by
    rw [hsp₂, keepHigh 1088 (by omega) (by omega)]; exact eArg 0 (by decide)
  have m1 : t₂.mem.readW (t₂.sp + BitVec.ofNat 64 1096) 64 = stackArg s 1 := by
    rw [hsp₂, keepHigh 1096 (by omega) (by omega)]; exact eArg 1 (by decide)
  have hrd₂ : t₂.rd = s.rd := hs.rd.trans ht.rd
  have hwr₂ : t₂.wr = (entered s).wr := hs.wr.trans ht.wr
  refine WP.mono (emStart_ok (s := s) (by rw [hs.gpr, h9, hsp₂]) (by rw [hsp₂]; exact hfr t₂ _ _ hwr₂ (by decide))
    (by rw [hsp₂]; exact hfr t₂ _ _ hwr₂ (by decide)) (by rw [hsp₂]; exact harg t₂ _ hrd₂ (by omega) (by omega))
    (by rw [hsp₂]; exact harg t₂ _ hrd₂ (by omega) (by omega)) m0 m1) fun u hu => ?_
  have hx40 : (lay P s).Q + BitVec.ofNat 64 oEM ≠ (lay P s).Q + BitVec.ofNat 64 (oEM + 1) :=
    Offset.add_ofNat_ne _ (by decide) (by decide) (by decide)
  have F3 : Frame [⟨(lay P s).Q + BitVec.ofNat 64 oEM, 2⟩] t₂.mem u.mem := by
    rw [hu.mem, hsp₂]
    refine ((Frame.refl _ _).write (List.mem_singleton_self _) _ ?_).write (List.mem_singleton_self _) _ ?_
    · exact Offset.contains _ (by decide) (by decide) (by unfold oEM; omega)
    · exact Offset.contains _ (by decide) (by decide) (by unfold oEM; omega)
  -- Everything the body has written so far is in `⟨Q, 42⟩`.
  have F : Frame [⟨(lay P s).Q, 42⟩] (entered s).mem u.mem := by
    refine Frame.trans (F2.sub fun r hr => ?_) (F3.sub fun r hr => ?_) |> fun f => ht.mem ▸ f
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by decide)⟩
  have hi : ∀ d, 42 ≤ d → d + 8 ≤ 1120 → u.mem.readW ((lay P s).Q + BitVec.ofNat 64 d) 64 =
      (entered s).mem.readW ((lay P s).Q + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ =>
    F.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base _ (by omega) (by omega)) (by decide)
  have S3 := S2.frame F3 fun p hp r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hr
    subst hr
    rcases hp with rfl | rfl | rfl | rfl <;>
      exact Offset.disjoint _ (by decide) (by decide) (by decide)
  have sv : ∀ r d, (r, d) ∈ [(Reg.x10, 0), (Reg.x11, 8), (Reg.x0, oOut), (Reg.x3, oK)] →
      u.mem.readW ((lay P s).Q + BitVec.ofNat 64 d) 64 = t.gpr r := fun r d hrd => S3 (r, d) hrd
  have g₂ : t₂.gpr = t.gpr := hs.gpr
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hu.rd, hrd₂, h.2.2.1, ← lay_args P]; rfl
  · rw [hu.wr, hwr₂, entered_wr P, h.2.2.2.1]
    simp only [Lay.OUT, Lay.SCR, lay]
    rw [show (s.gpr .x1).toNat = (s.gpr .x3).toNat from olk]
  · rw [hu.sp, hsp₂]
  · intro r hr h30
    rw [hu.other r (preserved_ne hr (by decide)) (preserved_ne hr (by decide)) (preserved_ne hr (by decide))
      (preserved_ne hr (by decide)) (preserved_ne hr (by decide)) (preserved_ne hr (by decide)), g₂,
      ht.other r (preserved_ne hr (by decide)) (preserved_ne hr (by decide)) (preserved_ne hr (by decide))]
  · intro r _
    rw [hu.v, hs.v, ht.v]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [sv .x10 0 (by simp), ht.x10]; rfl
    · rw [sv .x11 8 (by simp), ht.x11]; rfl
    · rw [sv .x0 oOut (by simp), ht.other .x0 (by decide) (by decide) (by decide)]; rfl
    · rw [sv .x3 oK (by simp), ht.other .x3 (by decide) (by decide) (by decide)]; rfl
    · rw [hi 1072 (by omega) (by omega), eLr]
    · rw [show arg 0 = 1088 + 8 * 0 from rfl, hi (1088 + 8 * 0) (by omega) (by omega)]; exact eArg 0 (by decide)
    · rw [show arg 1 = 1088 + 8 * 1 from rfl, hi (1088 + 8 * 1) (by omega) (by omega)]; exact eArg 1 (by decide)
    · rw [show arg 2 = 1088 + 8 * 2 from rfl, hi (1088 + 8 * 2) (by omega) (by omega)]; exact eArg 2 (by decide)
    · rw [show arg 3 = 1088 + 8 * 3 from rfl, hi (1088 + 8 * 3) (by omega) (by omega)]; exact eArg 3 (by decide)
  · have hk : (lay P s).STK ∈ [(lay P s).OUT, (lay P s).SCR, (lay P s).STK] :=
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    refine Frame.trans (eFr.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact hk) (F.sub fun r hr => ?_)
    rw [List.mem_singleton.mp hr]
    have h42 := Lay.Ok.sub_stk (L := lay P s) (d := 0) (n := 42) (by omega)
    rw [show (lay P s).Q + BitVec.ofNat 64 0 = (lay P s).Q from BitVec.add_zero _] at h42
    exact ⟨(lay P s).STK, hk, h42⟩
  · have go : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → r ≠ .x14 → r ≠ .x15 →
        u.gpr r = s.gpr r := fun r a b c d e f g' => by
      rw [hu.other r b c d e f g', g₂, ht.other r a b c]
    refine ⟨go .x0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      go .x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      go .x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      go .x3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      go .x4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      go .x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      go .x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      go .x7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hu.x11, hu.x12, by rw [hu.x13, hsp₂], hu.x14, hu.x15, ?_, ?_⟩
    · rw [hu.mem, hsp₂, Bytes.write1_ne _ _ hx40, Bytes.write1_self]; rfl
    · rw [hu.mem, hsp₂, Bytes.write1_self]; rfl

end VG.Proof.RsaPkcs1Enc.AArch64.Enc
