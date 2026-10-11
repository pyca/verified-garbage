import VerifiedGarbage.Proof.Sm4.X86.KeyLoop

/-!
# The SM4 key schedule on x86 (32-bit): the whole function

As on ARMv7 (`Proof/Sm4/Arm/KeyEk.lean`): `expandKey_wp`, with the working
space as an argument (`expandKeyX86`): `expandKey` saves the callee-saved
registers, keeps the schedule's pointer in its slot, stores the table of
`CK`'s planes, bitslices eight copies of `MK ⊕ FK`, runs the loop
(`ekIter_ok`) and restores the registers; the schedule is the
specification's `expandKey`.
-/

namespace VG.Proof.Sm4

open VG VG.X86 VG.Impl.Sm4.X86

/-- The key schedule on x86 with its working space as the third argument. -/
def expandKeyX86 : Contract X86.isa where
  pre s :=
    let key : Region := ⟨(arg s 0).setWidth 64, 16⟩
    let sched : Region := ⟨(arg s 1).setWidth 64, 128⟩
    let scratch : Region := ⟨(arg s 2).setWidth 64, 4 * slots⟩
    let args : Region := ⟨argAddr s 0, 12⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [key, args] ∧ s.wr = [sched, scratch] ∧
    key.Disjoint sched ∧ key.Disjoint scratch ∧ sched.Disjoint scratch ∧
    args.Disjoint sched ∧ args.Disjoint scratch ∧ ret.Disjoint sched ∧ ret.Disjoint scratch ∧
    (arg s 0).toNat + 16 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 128 ≤ 2 ^ 32 ∧
    (arg s 2).toNat + 4 * slots ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 16 ≤ 2 ^ 32
  post s s' :=
    Spec.Sm4.scheduleAt s'.mem ((arg s 1).setWidth 64) =
      Spec.Sm4.expandKey (Spec.Sm4.blockAt s.mem ((arg s 0).setWidth 64))
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 3, arg s₁ i = arg s₂ i

end VG.Proof.Sm4

namespace VG.Proof.Sm4.X86

open VG VG.X86 VG.X86.Straight VG.Impl.Sm4.X86
open VG.Impl.Aes.X86 (sb slotAt st movS movR addI at_ argOp)
open VG.Proof.Sm4 (quads ofBlock outBlock keyInit rkOf getLsbD_outBlock expandKeyX86 expandKey_eq)
open VG.Impl.Sm4 (planeOf32 fkLE)

/-! ## The loop -/

/-- What the loop keeps, after `m` of its eight iterations: the state holds
the key schedule's words after `4 m` rounds, and the schedule its first
`4 m` round keys. -/
structure EkInv (s₀ : State) (b S : BitVec 32) (key : Spec.Sm4.Block) (m : Nat) (s : State) : Prop where
  base : s.gpr sb = b
  esp : s.gpr .esp = s₀.gpr .esp
  ptr : s.mem.readW (wordAddr b nSlot) 32 = S + BitVec.ofNat 32 (16 * m)
  kp : AtEntry s b (4 * m)
  keys : KeyCtx s Spec.Sm4.ck
  st : StRel s (fun _ => quads .key Spec.Sm4.ck m (keyInit key))
  sched : ∀ i < 4 * m, ∀ c < 4, ∀ j < 8,
    (s.mem (S.setWidth 64 + BitVec.ofNat 64 (4 * i + c))).getLsbD j = (rkOf key i).getLsbD (8 * c + j)
  saved : Saved s₀ b s.mem
  frame : Frame [⟨b.setWidth 64, 4 * slots⟩, ⟨S.setWidth 64, 128⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The scratch buffer and the schedule, writable and apart. -/
structure EkPre (s₀ : State) (b S : BitVec 32) : Prop where
  scr : ScrIn s₀.wr b
  sch : (⟨S.setWidth 64, 128⟩ : Region) ∈ s₀.wr
  sep : Region.Disjoint ⟨S.setWidth 64, 128⟩ ⟨b.setWidth 64, 4 * slots⟩
  fitS : S.toNat + 128 ≤ 2 ^ 32

theorem ekIter_ok {s₀ : State} {b S : BitVec 32} {key : Spec.Sm4.Block} (hp : EkPre s₀ b S) {m : Nat} (hm : m < 8)
    {s : State} (hi : EkInv s₀ b S key m s) :
    ∃ s', runBlock isa keyBody s = some s' ∧ EkInv s₀ b S key (m + 1) s' ∧
      s'.zf = some (decide (m + 1 = 8)) := by
  have hfit' := hp.scr.fit
  have hfit : b.toNat + 4 * 358 ≤ 2 ^ 32 := hfit'
  have l₁ := tableSlot_eq
  have l₂ := dSlot_eq
  have l₃ := nSlot_eq
  have l₄ := slots_eq
  have l₅ := savedSlot_eq
  have l₆ := tableEnd_eq
  have hfitS := hp.fitS
  have hSn := setWidth_toNat S
  have hbn := setWidth_toNat b
  have hc0 : Ctx s s := Ctx.refl s
  have hwS : ScrIn s.wr b := by rw [hi.wr]; exact hp.scr
  -- Four rounds.
  obtain ⟨s₁, e₁, c₁, k₁, X₁⟩ := rounds4_ok .key hi.keys hc0 (by rw [hi.base]; exact hi.kp) hm hi.st
  obtain ⟨s₂, e₂, kp₂, -, o₂, m₂, rd₂, wr₂⟩ := addI_ok s₁ kp 128
  have c₂ : Ctx s s₂ := c₁.kp o₂ m₂ rd₂ wr₂
  have X₂ : StRel s₂ (fun _ => quads .key Spec.Sm4.ck (m + 1) (keyInit key)) :=
    X₁.congr fun k => by simp only [slotW, m₂, o₂ sb (by decide)]
  -- The words to the tail buffer.
  obtain ⟨s₃, e₃, c₃, kp₃, X₃, T₃⟩ := fromBs_step hi.keys c₂ X₂
  have base₃ : s₃.gpr sb = b := by rw [c₃.base, hi.base]
  have hwS₃ : ScrIn s₃.wr b := by rw [c₃.wr]; exact hwS
  -- To the schedule.
  obtain ⟨s₄, e₄, B₄, n₄, f₄, o₄, rd₄, wr₄⟩ := extract_ok hm base₃ hwS₃ hfitS
    (by rw [c₃.wr, hi.wr]; exact hp.sch) hp.sep
    (by rw [slot_keep (lo := tableSlot) (hi := slots) hfit' (Nat.le_refl _) c₃.frame (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; rw [hi.base]
          exact VG.Offset.disjoint_base _ (Nat.le_refl _) (by omega))
        (show tableSlot ≤ nSlot by decide) (by decide), hi.ptr])
  obtain ⟨s₅, e₅, z₅, g₅, m₅, rd₅, wr₅⟩ := endTest_ok s₄ (BitVec.ofNat 32 (4 * tableEnd))
  have mem₅ : s₅.mem = s₄.mem := m₅
  have g₅' : ∀ r, r ≠ .eax → r ≠ .ecx → s₅.gpr r = s₃.gpr r := fun r h0 h7 => by rw [g₅ r h0, o₄ r h0 h7]
  have base₅ : s₅.gpr sb = b := by rw [g₅' _ (by decide) (by decide), base₃]
  have kp₄ : s₄.gpr kp = b + BitVec.ofNat 32 (4 * tableSlot + 32 * (4 * (m + 1))) := by
    rw [o₄ _ (by decide) (by decide), kp₃, kp₂, k₁, show s.gpr kp = _ from hi.kp,
      show (128 : BitVec 32) = BitVec.ofNat 32 128 from rfl, VG.Offset.add_add,
      show 4 * tableSlot + 32 * (4 * m) + 128 = 4 * tableSlot + 32 * (4 * (m + 1)) by omega]
  have kp₅ : AtEntry s₅ b (4 * (m + 1)) := by
    rw [AtEntry, g₅ _ (by decide), kp₄]
  -- What the extraction keeps: everything outside the schedule's new bytes and the pointer's slot.
  have dHi : ∀ r ∈ [(⟨S.setWidth 64 + BitVec.ofNat 64 (16 * m), 16⟩ : Region), ⟨wordAddr b nSlot, 4⟩],
      (slotsRegion b 0 dSlot).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hp.sep.sub_left (VG.Offset.sub_base _ (by omega))).sub_right
        (VG.Offset.sub_base _ (by omega)) |>.symm
    · rw [slot_addr (by omega)]
      exact VG.Offset.disjoint _ (by omega) (by omega) (by omega)
  have keep₄ : ∀ k < dSlot, s₄.mem.readW (wordAddr b k) 32 = s₃.mem.readW (wordAddr b k) 32 := fun k hk =>
    slot_keep (lo := 0) (hi := dSlot) hfit' (by decide) f₄ dHi (Nat.zero_le _) hk
  have keepT : ∀ k, tableSlot ≤ k → k < dSlot → s₃.mem.readW (wordAddr b k) 32 = s.mem.readW (wordAddr b k) 32 :=
    fun k h1 h2 => slot_keep (lo := tableSlot) (hi := dSlot) hfit' (by decide) c₃.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [hi.base]
      exact VG.Offset.disjoint_base _ (Nat.le_refl _) (by omega)) h1 h2
  have hent : ∀ e < 32, ∀ j < 8, entryW s₅.mem b e j = entryW s.mem b e j := fun e he j hj => by
    simp only [entryW]
    rw [mem₅, keep₄ _ (by rw [tableSlot_eq, dSlot_eq]; omega), keepT _ (by omega) (by rw [tableSlot_eq, dSlot_eq]; omega)]
  refine ⟨s₅, ?_, ⟨base₅, ?_, by rw [mem₅]; exact n₄, kp₅,
    ⟨by rw [base₅, wr₅, wr₄, c₃.wr, hi.wr]; exact hp.scr,
      fun e he => by rw [base₅]; exact (hi.keys.keys e he).congr fun j hj => by rw [hi.base] at *; exact hent e he j hj⟩,
    fun w hw => (X₃ w hw).congr fun j hj => ?_, fun i hi' c hc j hj => ?_, fun i hi' => ?_, ?_,
    by rw [rd₅, rd₄, c₃.rd, hi.rd], by rw [wr₅, wr₄, c₃.wr, hi.wr]⟩, ?_⟩
  · rw [keyBody, runBlock_app, runBlock_app, runBlock_app, runBlock_app, e₁, Option.bind_some,
      e₂, Option.bind_some, e₃, Option.bind_some, e₄, Option.bind_some, e₅]
  · rw [g₅' _ (by decide) (by decide), c₃.keep _ (by decide) (by decide), hi.esp]
  · show slotW s₅ (stateSlot w j) = slotW s₃ (stateSlot w j)
    rw [slotW, slotW, base₅, base₃, mem₅, keep₄ _ (by simp only [stateSlot, dSlot_eq]; omega)]
  · by_cases hnew : 4 * m ≤ i
    · have ht : 4 * (i - 4 * m) + c < 16 := by omega
      have hB := B₄ _ ht j hj
      rw [show 16 * m + (4 * (i - 4 * m) + c) = 4 * i + c by omega] at hB
      rw [mem₅, hB, T₃ 0 (by decide), getLsbD_outBlock _ (by omega) hj]
      simp only [rkOf]
      rw [show i / 4 + 1 = m + 1 by omega, show 3 - (15 - (4 * (i - 4 * m) + c)) / 4 = i % 4 by omega,
        show 8 * (3 - (15 - (4 * (i - 4 * m) + c)) % 4) + j = 8 * c + j by omega]
    · have hx : (⟨S.setWidth 64, 128⟩ : Region).Contains (S.setWidth 64 + BitVec.ofNat 64 (4 * i + c)) 1 :=
        VG.Offset.contains_base _ (by omega) (by omega)
      rw [mem₅, f₄ _ (fun r hr => ?_), c₃.frame _ (fun r hr => ?_)]
      · exact hi.sched i (by omega) c hc j hj
      · simp only [List.mem_singleton] at hr; subst hr; rw [hi.base]
        exact fun h => hp.sep _ hx (Region.sub_prefix (show 4 * tableSlot ≤ 4 * slots by
          rw [tableSlot_eq, slots_eq]; omega) _ h)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact VG.Proof.Sm4.not_contains_off _ (Or.inl (by omega)) (by omega) (by decide) (by omega)
        · exact fun h => hp.sep _ hx (slot_sub hfit' (by decide) _ h)
  · have hk : savedSlot + i < dSlot := by rw [savedSlot_eq, dSlot_eq]; omega
    show s₅.mem.readW _ 32 = _
    rw [mem₅, keep₄ _ hk, keepT _ (by rw [savedSlot_eq, tableSlot_eq]; omega) hk]
    exact hi.saved i hi'
  · rw [mem₅]
    refine hi.frame.trans ((c₃.frame.sub fun r hr => ⟨⟨b.setWidth 64, 4 * slots⟩, List.mem_cons_self, ?_⟩).trans
      (f₄.sub fun r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst hr; rw [hi.base]
      exact Region.sub_prefix (by rw [tableSlot_eq, slots_eq]; omega)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨S.setWidth 64, 128⟩, List.mem_cons_of_mem _ List.mem_cons_self, VG.Offset.sub_base _ (by omega)⟩
      · exact ⟨⟨b.setWidth 64, 4 * slots⟩, List.mem_cons_self, slot_sub hfit' (by decide)⟩
  · rw [z₅, kp₄, o₄ _ (by decide) (by decide), show s₃.gpr .edi = b from base₃, VG.Offset.add_sub_cancel_left,
      ofNat32_sub_beq (by rw [tableSlot_eq]; omega) (by rw [tableEnd_eq]; omega), tableSlot_eq, tableEnd_eq]
    simp only [Option.some.injEq, decide_eq_decide]; omega

theorem ekLoop_wp {s₀ s : State} {b S : BitVec 32} {key : Spec.Sm4.Block} (hp : EkPre s₀ b S)
    (hi : EkInv s₀ b S key 0 s) :
    WP isa (.loop (.block keyBody) .ne) s (EkInv s₀ b S key 8) := by
  refine WP.loop (M := isa) (fun n s => ∃ m, n = 8 - m ∧ m < 8 ∧ EkInv s₀ b S key m s)
    (fun n s hs => ?_) 8 s ⟨0, rfl, by omega, hi⟩
  obtain ⟨m, rfl, hm, hi⟩ := hs
  obtain ⟨s', e', hi', z'⟩ := ekIter_ok hp hm hi
  refine WP.of_runBlock ⟨s', e', ?_⟩
  by_cases h8 : m + 1 = 8
  · exact .inl ⟨by rw [eval_ne, z', h8]; rfl, by rw [h8] at hi'; exact hi'⟩
  · exact .inr ⟨by rw [eval_ne, z']; simp [h8], 8 - (m + 1), by omega, m + 1, rfl, by omega, hi'⟩

/-! ## The start -/

theorem ckEntries_mem {e j : Nat} (he : e < 32) (hj : j < 8) :
    (tableSlot + 8 * e + j, planeOf32 (Spec.Sm4.ck e) j) ∈ ckEntries := by
  simp only [ckEntries, List.mem_flatMap, List.mem_range, List.mem_map]
  exact ⟨e, he, j, hj, rfl⟩

theorem ckEntries_lt : ∀ kv ∈ ckEntries, kv.1 < tableEnd := by decide +kernel

theorem ckEntries_nodup : (ckEntries.map (·.1)).Nodup := by
  -- The slots are consecutive: a linear check, not the quadratic `Nodup` search.
  rw [show ckEntries.map (·.1) = List.range' tableSlot 256 by decide +kernel]
  exact List.nodup_range'

/-- Argument `i` of three is in the arguments' region. -/
theorem arg3_contains (s : State) (hfit : (s.gpr .esp).toNat + 16 ≤ 2 ^ 32) {i : Nat} (hi : i < 3) :
    (⟨argAddr s 0, 12⟩ : Region).Contains (argAddr s i) 4 := by
  have hs := setWidth_toNat (s.gpr .esp)
  rw [show argAddr s i = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) from addr_eq (by omega),
    show argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 from addr_eq (by omega)]
  exact VG.Offset.contains _ (by omega) (by omega) (by omega)

/-- The code before the loop. -/
def ekHead : List Instr :=
  saveRegs 2 ++ [.mov .eax (.mem (argOp 1)), st nSlot .eax] ++ ckTable ++ loadKey ++ toBs ++ kpAt tableSlot

theorem ekHead_ok {s₀ : State} (hp : expandKeyX86.pre s₀) :
    ∃ s, runBlock isa ekHead s₀ = some s ∧
      EkInv s₀ (arg s₀ 2) (arg s₀ 1) (Spec.Sm4.blockAt s₀.mem ((arg s₀ 0).setWidth 64)) 0 s := by
  obtain ⟨hrd, hwr, dKS, dKB, dSB, dAS, dAB, -, -, fitK, fitS, fitB, fitE⟩ := hp
  let b := arg s₀ 2
  let S := arg s₀ 1
  let Kp := arg s₀ 0
  have hwS : ScrIn s₀.wr b := .exact (by rw [hwr]; simp [b]) fitB
  have hfit : b.toNat + 4 * 358 ≤ 2 ^ 32 := fitB
  have hbn := setWidth_toNat b
  have hKn := setWidth_toNat Kp
  have hfK : Kp.toNat + 16 ≤ 2 ^ 32 := fitK
  have l₁ := tableSlot_eq
  have l₂ := dSlot_eq
  have l₃ := nSlot_eq
  have l₄ := slots_eq
  have l₅ := savedSlot_eq
  have l₆ := tableEnd_eq
  have l₇ := tailSlot_eq
  have hrA : (⟨argAddr s₀ 0, 12⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp
  -- The arguments, through writes of the scratch buffer.
  have argR : ∀ {m : Mem}, Frame [⟨b.setWidth 64, 4 * slots⟩] s₀.mem m → ∀ i < 3,
      m.readW (argAddr s₀ i) 32 = arg s₀ i := fun hf i hi =>
    hf.readW (arg3_contains s₀ fitE hi) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dAB) (by decide)
  have argIn : ∀ {s : State}, s.rd = s₀.rd → s.wr = s₀.wr → s.gpr .esp = s₀.gpr .esp → ∀ i < 3,
      InRegions (s.rd ++ s.wr) (s.ea (argOp i)) 4 := fun h1 h2 h3 i hi => by
    rw [h1, h2, ea_arg h3]; exact ⟨_, List.mem_append_left _ hrA, arg3_contains s₀ fitE hi⟩
  -- Saving, the schedule's pointer, the table of `CK`.
  obtain ⟨s₁, e₁, b₁, g₁, sv₁, rd₁, wr₁, f₁, -⟩ := save_ok (k := 2) hwS (argIn rfl rfl rfl 2 (by decide))
    (by rw [ea_arg rfl]; rfl)
  have esp₁ : s₁.gpr .esp = s₀.gpr .esp := g₁ _ (by decide) (by decide)
  obtain ⟨s₂, e₂, a₂, o₂, m₂, rd₂, wr₂, f₂⟩ := argSlot_ok s₁ (i := 1) (k := nSlot) b₁ (by decide)
    (by rw [wr₁]; exact hwS) (argIn rd₁ wr₁ esp₁ 1 (by decide))
  have b₂ : s₂.gpr sb = b := (o₂ _ (by decide)).trans b₁
  have hw₂ : ScrIn s₂.wr b := by rw [wr₂, wr₁]; exact hwS
  obtain ⟨s₃, e₃, v₃, k₃, g₃, rd₃, wr₃, f₃⟩ := constStores_ok ckEntries b₂ hw₂ ckEntries_nodup
    (fun kv hkv => by have := ckEntries_lt kv hkv; omega)
  have b₃ : s₃.gpr sb = b := (g₃ _ (by decide)).trans b₂
  have esp₃ : s₃.gpr .esp = s₀.gpr .esp := by rw [g₃ _ (by decide), o₂ _ (by decide), esp₁]
  have f₀₃ : Frame [⟨b.setWidth 64, 4 * slots⟩] s₀.mem s₃.mem :=
    f₁.trans ((f₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact slot_sub fitB (by decide)⟩).trans f₃)
  have rd₃' : s₃.rd = s₀.rd := by rw [rd₃, rd₂, rd₁]
  have wr₃' : s₃.wr = s₀.wr := by rw [wr₃, wr₂, wr₁]
  -- The key's pointer.
  obtain ⟨s₄, e₄, c₄, o₄, m₄, rd₄, wr₄⟩ := ldArg_ok s₃ .ecx 0 (argIn rd₃' wr₃' esp₃ 0 (by decide))
  have ecx₄ : s₄.gpr .ecx = Kp := by rw [c₄, ea_arg esp₃]; exact argR f₀₃ 0 (by decide)
  have b₄ : s₄.gpr sb = b := (o₄ _ (by decide)).trans b₃
  have hw₄ : ScrIn s₄.wr b := by rw [wr₄, wr₃']; exact hwS
  have f₀₄ : Frame [⟨b.setWidth 64, 4 * slots⟩] s₀.mem s₄.mem := by rw [m₄]; exact f₀₃
  -- The key's words, as on entry.
  have inK : ∀ w < 4, InRegions (s₀.rd ++ s₀.wr) (wordAddr Kp w) 4 := fun w hw =>
    ⟨_, List.mem_append_left _ (by rw [hrd]; exact List.mem_cons_self), by
      rw [slot_addr (by omega)]; exact VG.Offset.contains_base _ (by omega) (by omega)⟩
  have hKw : ∀ (m : Mem), Frame [⟨b.setWidth 64, 4 * slots⟩] s₀.mem m → ∀ w < 4,
      m.readW (wordAddr Kp w) 32 = s₀.mem.readW (wordAddr Kp w) 32 := fun m hf w hw => by
    rw [slot_addr (by omega)]
    exact hf.readW (r := ⟨Kp.setWidth 64, 16⟩) (VG.Offset.contains_base _ (by omega) (by omega))
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dKB) (by decide)
  -- `MK ⊕ FK` to the tail buffer.
  have rdwr : ∀ (st : State), st.rd = s₀.rd → st.wr = s₀.wr → ∀ w < 4,
      InRegions (st.rd ++ st.wr) (wordAddr Kp w) 4 := fun st h1 h2 w hw => by rw [h1, h2]; exact inK w hw
  obtain ⟨s₅, e₅, v₅, k₅, g₅, rd₅, wr₅, f₅⟩ := loadKeyWord_ok (s := s₄) 0 (by decide) b₄ hw₄ ecx₄
    (rdwr s₄ (by rw [rd₄, rd₃']) (by rw [wr₄, wr₃']) 0 (by decide))
  obtain ⟨s₆, e₆, v₆, k₆, g₆, rd₆, wr₆, f₆⟩ := loadKeyWord_ok (s := s₅) 1 (by decide)
    (by rw [g₅ _ (by decide), b₄]) (by rw [wr₅]; exact hw₄) (by rw [g₅ _ (by decide), ecx₄])
    (rdwr s₅ (by rw [rd₅, rd₄, rd₃']) (by rw [wr₅, wr₄, wr₃']) 1 (by decide))
  obtain ⟨s₇, e₇, v₇, k₇, g₇, rd₇, wr₇, f₇⟩ := loadKeyWord_ok (s := s₆) 2 (by decide)
    (by rw [g₆ _ (by decide), g₅ _ (by decide), b₄]) (by rw [wr₆, wr₅]; exact hw₄)
    (by rw [g₆ _ (by decide), g₅ _ (by decide), ecx₄])
    (rdwr s₆ (by rw [rd₆, rd₅, rd₄, rd₃']) (by rw [wr₆, wr₅, wr₄, wr₃']) 2 (by decide))
  obtain ⟨s₈, e₈, v₈, k₈, g₈, rd₈, wr₈, f₈⟩ := loadKeyWord_ok (s := s₇) 3 (by decide)
    (by rw [g₇ _ (by decide), g₆ _ (by decide), g₅ _ (by decide), b₄]) (by rw [wr₇, wr₆, wr₅]; exact hw₄)
    (by rw [g₇ _ (by decide), g₆ _ (by decide), g₅ _ (by decide), ecx₄])
    (rdwr s₇ (by rw [rd₇, rd₆, rd₅, rd₄, rd₃']) (by rw [wr₇, wr₆, wr₅, wr₄, wr₃']) 3 (by decide))
  have g₈' : ∀ r, r ≠ .eax → s₈.gpr r = s₄.gpr r := fun r h0 => by
    rw [g₈ r h0, g₇ r h0, g₆ r h0, g₅ r h0]
  have b₈ : s₈.gpr sb = b := by rw [g₈' _ (by decide), b₄]
  have f₀₈ : Frame [⟨b.setWidth 64, 4 * slots⟩] s₀.mem s₈.mem := f₀₄.trans (f₅.trans (f₆.trans (f₇.trans f₈)))
  -- The slots outside the tail buffer after `s₃`.
  have notTail : ∀ k, tableSlot ≤ k → ∀ c < 8, ∀ w < 4, k ≠ tailAt c w := fun k hk c hc w hw => by
    simp only [tailAt]; omega
  have kk₈ : ∀ k < slots, tableSlot ≤ k →
      s₈.mem.readW (wordAddr b k) 32 = s₃.mem.readW (wordAddr b k) 32 := fun k hk ht => by
    rw [k₈ k hk (fun c hc => notTail k ht c hc 3 (by decide)), k₇ k hk (fun c hc => notTail k ht c hc 2 (by decide)),
      k₆ k hk (fun c hc => notTail k ht c hc 1 (by decide)), k₅ k hk (fun c hc => notTail k ht c hc 0 (by decide)),
      m₄]
  have notCk : ∀ k, tableEnd ≤ k → k ∉ ckEntries.map (·.1) := fun k hk hm => by
    simp only [List.mem_map] at hm
    obtain ⟨kv, hkv, rfl⟩ := hm
    have := ckEntries_lt kv hkv; omega
  -- The table of `CK`.
  have hkey₈ : KeyCtx s₈ Spec.Sm4.ck :=
    { scr := by rw [b₈, wr₈, wr₇, wr₆, wr₅, wr₄, wr₃']; exact hwS
      keys := fun e he => (planeOf32_rel (Spec.Sm4.ck e)).congr fun j hj => by
        rw [b₈, entryW, kk₈ _ (by omega) (by omega), v₃ _ (ckEntries_mem he hj)] }
  -- The key, bitsliced.
  obtain ⟨s₉, e₉, c₉, X₉⟩ := toBs_step hkey₈ (Ctx.refl s₈)
  obtain ⟨s₁₀a, e₁₀a, k₁₀a, o₁₀a, m₁₀a, rd₁₀a, wr₁₀a, -, -⟩ := movR_ok s₉ kp .edi
  obtain ⟨s₁₀, e₁₀, k₁₀, -, o₁₀, m₁₀, rd₁₀, wr₁₀⟩ := addI_ok s₁₀a kp (BitVec.ofNat 32 (4 * tableSlot))
  have b₉ : s₉.gpr sb = b := by rw [c₉.base, b₈]
  have b₁₀ : s₁₀.gpr sb = b := by rw [o₁₀ _ (by decide), o₁₀a _ (by decide), b₉]
  have mem₁₀ : s₁₀.mem = s₉.mem := by rw [m₁₀, m₁₀a]
  have keep₉ : ∀ k, tableSlot ≤ k → k < slots →
      s₁₀.mem.readW (wordAddr b k) 32 = s₈.mem.readW (wordAddr b k) 32 := fun k h1 h2 => by
    rw [mem₁₀]
    exact slot_keep (lo := tableSlot) (hi := slots) fitB (Nat.le_refl _) c₉.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [b₈]
      exact VG.Offset.disjoint_base _ (Nat.le_refl _) (by omega)) h1 h2
  have hK : ∀ w < 4, ∀ t < 4, ∀ j < 8, (s₀.mem.readW (wordAddr Kp w) 32).getLsbD (8 * t + j) =
      ((Spec.Sm4.blockAt s₀.mem (Kp.setWidth 64)).getD (4 * w + t) 0).getLsbD j := fun w hw t ht j hj => by
    rw [readW32_bit _ _ ht hj, VG.Proof.Sm4.blockAt_getD _ _ (by omega), byte_addr _ rfl (by omega)]
  have hT : ∀ c < 8, ∀ w < 4, s₈.mem.readW (wordAddr b (tailAt c w)) 32 =
      s₀.mem.readW (wordAddr Kp w) 32 ^^^ fkLE w := by
    intro c hc w hw
    have hne : ∀ w', w' < 4 → w' ≠ w → ∀ c' < 8, tailAt c w ≠ tailAt c' w' := fun w' _ h c' _ h' => by
      simp only [tailAt] at h'; omega
    have hl := tailAt_lt hc hw
    rcases (show w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 by omega) with rfl | rfl | rfl | rfl
    · rw [k₈ _ hl (hne 3 (by decide) (by decide)), k₇ _ hl (hne 2 (by decide) (by decide)),
        k₆ _ hl (hne 1 (by decide) (by decide)), v₅ c hc, hKw _ f₀₄ 0 (by decide)]
    · rw [k₈ _ hl (hne 3 (by decide) (by decide)), k₇ _ hl (hne 2 (by decide) (by decide)), v₆ c hc,
        hKw _ (f₀₄.trans f₅) 1 (by decide)]
    · rw [k₈ _ hl (hne 3 (by decide) (by decide)), v₇ c hc, hKw _ (f₀₄.trans (f₅.trans f₆)) 2 (by decide)]
    · rw [v₈ c hc, hKw _ (f₀₄.trans (f₅.trans (f₆.trans f₇))) 3 (by decide)]
  have hst : StRel s₁₀ (fun _ => quads .key Spec.Sm4.ck 0
      (keyInit (Spec.Sm4.blockAt s₀.mem (Kp.setWidth 64)))) := fun w hw =>
    ((X₉ w hw).congr fun j _ => by simp only [planes, slotW, mem₁₀, b₁₀, b₉]).congr_right fun c hc =>
      (keyInit_rel b₈ fitB hK hT c hc w hw).symm
  have g₁₀ : ∀ r, r ≠ kp → s₁₀.gpr r = s₉.gpr r := fun r hr => by rw [o₁₀ r hr, o₁₀a r hr]
  refine ⟨s₁₀, ?_, ⟨b₁₀, ?_, ?_, ?_, ?_, hst, fun i hi => by omega, fun i hi => ?_, ?_,
    by rw [rd₁₀, rd₁₀a, c₉.rd, rd₈, rd₇, rd₆, rd₅, rd₄, rd₃'],
    by rw [wr₁₀, wr₁₀a, c₉.wr, wr₈, wr₇, wr₆, wr₅, wr₄, wr₃']⟩⟩
  · rw [ekHead, runBlock_app, runBlock_app, runBlock_app, runBlock_app, runBlock_app, e₁,
      Option.bind_some,
      show ([.mov .eax (.mem (argOp 1)), st nSlot .eax] : List Instr) =
        [.mov .eax (.mem (argOp 1)), .store (slotAt .edi nSlot) .eax] from rfl,
      e₂, Option.bind_some, ckTable, e₃, Option.bind_some,
      show loadKey = [.mov .ecx (.mem (argOp 0))] ++
        (loadKeyWord 0 ++ (loadKeyWord 1 ++ (loadKeyWord 2 ++ loadKeyWord 3))) from rfl,
      runBlock_app, e₄, Option.bind_some,
      runBlock_app, e₅, Option.bind_some, runBlock_app, e₆, Option.bind_some, runBlock_app, e₇, Option.bind_some,
      e₈, Option.bind_some, e₉, Option.bind_some, kpAt,
      show ([movR kp .edi, addI kp (BitVec.ofNat 32 (4 * tableSlot))] : List Instr) =
        [movR kp .edi] ++ [addI kp (BitVec.ofNat 32 (4 * tableSlot))] from rfl, runBlock_app, e₁₀a,
      Option.bind_some, e₁₀]
  · rw [g₁₀ _ (by decide), c₉.keep _ (by decide) (by decide), g₈' _ (by decide), o₄ _ (by decide), esp₃]
  · rw [keep₉ _ (by decide) (by decide), kk₈ _ (by decide) (by decide), k₃ _ (by decide) (notCk _ (by decide)),
      m₂, readW_slot_write fitB _ (by decide) (by decide), ite_eq_left rfl, ea_arg esp₁]
    rw [argR f₁ 1 (by decide)]
    simp
  · rw [AtEntry, k₁₀, k₁₀a, c₉.keep _ (by decide) (by decide), g₈' _ (by decide), show s₄.gpr .edi = b from b₄]
    simp [b]
  · exact (hkey₈.of_ctx c₉) |> fun h => ⟨by rw [wr₁₀, wr₁₀a, b₁₀, ← b₉]; exact h.scr,
      fun e he => by rw [b₁₀, ← b₉, mem₁₀]; exact h.keys e he⟩
  · have hk : savedSlot + i < slots := by omega
    show s₁₀.mem.readW _ 32 = _
    rw [keep₉ _ (by omega) hk, kk₈ _ hk (by omega), k₃ _ hk (notCk _ (by omega)), m₂,
      readW_slot_write fitB _ hk (by decide), ite_eq_right (by omega)]
    exact sv₁ i hi
  · rw [mem₁₀]
    refine (f₀₈.trans (c₉.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)).sub
      fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self, fun _ h => h⟩
    simp only [List.mem_singleton] at hr; subst hr
    rw [b₈]; exact Region.sub_prefix (by omega)

theorem expandKey_wp {s₀ : State} (hp : expandKeyX86.pre s₀) :
    WP isa expandKey s₀ fun s' => abiPreserved s₀ s' ∧ expandKeyX86.post s₀ s' := by
  obtain ⟨s₁, e₁, h₁⟩ := ekHead_ok hp
  obtain ⟨hrd, hwr, dKS, dKB, dSB, dAS, dAB, dRS, dRB, fitK, fitS, fitB, fitE⟩ := hp
  let b := arg s₀ 2
  let S := arg s₀ 1
  have hwB : ScrIn s₀.wr b := .exact (by rw [hwr]; simp [b]) fitB
  have hwS : (⟨S.setWidth 64, 128⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [S]
  have pre : EkPre s₀ b S := ⟨hwB, hwS, dSB, fitS⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  refine WP.seq (WP.mono (ekLoop_wp pre h₁) fun s₂ h₂ => ?_)
  obtain ⟨s₃, e₃, rg₃, o₃, m₃, -, -⟩ := restore_ok (s₀ := s₀) (b := b) (by rw [h₂.wr]; exact hwB) h₂.base
    h₂.saved
  refine WP.of_runBlock ⟨s₃, e₃, ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact rg₃ 0 (by decide)
    · exact rg₃ 1 (by decide)
    · exact rg₃ 2 (by decide)
    · exact rg₃ 3 (by decide)
    · rw [o₃ _ (fun i hi => by revert i; decide), h₂.esp]
  · rw [m₃]
    exact h₂.frame.readW (r := ⟨(s₀.gpr .esp).setWidth 64, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dRB
      · exact dRS) (by decide)
  · show Spec.Sm4.scheduleAt s₃.mem (S.setWidth 64) = _
    rw [expandKey_eq]
    apply Vector.ext
    intro i hi
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    rw [show k = 8 * (k / 8) + k % 8 by omega, VG.Proof.Sm4.getLsbD_scheduleAt _ _ hi (by omega) (by omega),
      Vector.getElem_ofFn, m₃]
    exact h₂.sched i (by omega) _ (by omega) _ (by omega)

end VG.Proof.Sm4.X86
