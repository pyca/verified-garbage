import VerifiedGarbage.Proof.Seed.X86.Group
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.TCB.X86.Target

/-!
# SEED ECB on x86 (32-bit): the whole function

`ecb_wp`: with the working space as an argument (`ecbX86`), `ecb d` saves
the callee-saved registers, copies the round keys to the table in the order
the rounds of `d` use them (`keyTable_ok`), keeps the data pointer and the
count in their slots, transforms the blocks a group at a time
(`dataLoop_wp`) and restores the registers.
-/

namespace VG.Proof.Seed

open VG VG.X86 VG.Impl.Seed.X86

/-- ECB on x86 with its working space as the fourth argument. -/
def ecbX86 (d : Spec.Seed.Direction) : Contract X86.isa where
  pre s :=
    let sched : Region := ⟨(arg s 0).setWidth 64, 128⟩
    let data : Region := ⟨(arg s 1).setWidth 64, 16 * (arg s 2).toNat⟩
    let scratch : Region := ⟨(arg s 3).setWidth 64, 4 * slots⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [sched, args] ∧ s.wr = [data, scratch] ∧
    sched.Disjoint data ∧ sched.Disjoint scratch ∧ data.Disjoint scratch ∧
    args.Disjoint data ∧ args.Disjoint scratch ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
    (arg s 0).toNat + 128 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 16 * (arg s 2).toNat ≤ 2 ^ 32 ∧
    (arg s 3).toNat + 4 * slots ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32
  post s s' :=
    Spec.Seed.blocksAt s'.mem ((arg s 1).setWidth 64) (arg s 2).toNat =
      Spec.Seed.ecb (Spec.Seed.scheduleAt s.mem ((arg s 0).setWidth 64)) d
        (Spec.Seed.blocksAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 4, arg s₁ i = arg s₂ i

end VG.Proof.Seed

namespace VG.Proof.Seed.X86

open VG VG.X86 VG.X86.Straight VG.Impl.Seed.X86
open VG.Impl.Aes.X86 (sb slotAt st argOp at_ movS)
open VG.Proof.Seed (ecbX86 crypt_congr)

/-! ## The arguments -/

theorem ea_arg {s₀ s : State} (h : s.gpr .esp = s₀.gpr .esp) (i : Nat) : s.ea (argOp i) = argAddr s₀ i := by
  show (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 = _
  rw [h]; rfl

/-- Argument `i` is in the arguments' region. -/
theorem arg_contains (s : State) (hfit : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32) {i : Nat} (hi : i < 4) :
    (⟨argAddr s 0, 16⟩ : Region).Contains (argAddr s i) 4 := by
  have hs := toNat_addr (s.gpr .esp)
  rw [show argAddr s i = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) from addr_eq (by omega),
    show argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 from addr_eq (by omega)]
  exact Offset.contains _ (by omega) (by omega) (by omega)

/-- `mov eax, [esp + 4 + 4 i]; mov [edi + 4 k], eax`. -/
theorem argSlot_ok (s : State) {b : BitVec 32} {i k : Nat} (hb : s.gpr .edi = b) (hk : k < slots)
    (hw : ScrIn s.wr b) (ha : InRegions (s.rd ++ s.wr) (s.ea (argOp i)) 4) :
    ∃ s', runBlock isa [.mov .eax (.mem (argOp i)), .store (slotAt .edi k) .eax] s = some s' ∧
      s'.gpr .eax = s.mem.readW (s.ea (argOp i)) 32 ∧ (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem.writeW (wordAddr b k) (s.mem.readW (s.ea (argOp i)) 32) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨wordAddr b k, 4⟩] s.mem s'.mem := by
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := ldArg_ok s .eax i ha
  obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂, -, -, f₂⟩ := stSlot_ok s₁ .eax .edi (k := k) (by rw [o₁ _ (by decide), hb]) hk
    (by rw [wr₁]; exact hw)
  refine ⟨s₂, ?_, by rw [g₂, v₁], fun r hr => by rw [g₂, o₁ r hr], by rw [m₂, v₁, m₁], by rw [rd₂, rd₁],
    by rw [wr₂, wr₁], by rw [← m₁]; exact f₂⟩
  rw [show ([.mov .eax (.mem (argOp i)), .store (slotAt .edi k) .eax] : List Instr) =
    [.mov .eax (.mem (argOp i))] ++ [.store (slotAt .edi k) .eax] from rfl, runBlock_append, e₁, Option.bind_some, e₂]

/-! ## The table of round keys -/

/-- `mov eax, [ecx + 4 a]; mov [edi + 4 d], eax` for each `(a, d)`. -/
def loadsCode (L : List (Nat × Nat)) : List Instr :=
  L.flatMap fun p => [.mov .eax (.mem (at_ .ecx (4 * p.1))), st p.2 .eax]

/-- The schedule at `sched` and the scratch buffer at `b`. -/
structure SchedPre (s : State) (b sched : BitVec 32) : Prop where
  base : s.gpr sb = b
  scr : ScrIn s.wr b
  ecx : s.gpr .ecx = sched
  sch : (⟨sched.setWidth 64, 128⟩ : Region) ∈ s.rd ++ s.wr
  schFit : sched.toNat + 128 ≤ 2 ^ 32
  sep : Region.Disjoint ⟨sched.setWidth 64, 128⟩ ⟨b.setWidth 64, 4 * slots⟩

/-- Word `i` of the schedule. -/
def schW (m : Mem) (sched : BitVec 32) (i : Nat) : BitVec 32 := m.readW (wordAddr sched i) 32

theorem loads_ok {b sched : BitVec 32} :
    ∀ (L : List (Nat × Nat)) (s : State), SchedPre s b sched → (∀ p ∈ L, p.1 < 32 ∧ p.2 < slots) →
      (L.map (·.2)).Nodup →
      ∃ s', runBlock isa (loadsCode L) s = some s' ∧
        (∀ p ∈ L, s'.mem.readW (wordAddr b p.2) 32 = schW s.mem sched p.1) ∧
        (∀ j < slots, j ∉ L.map (·.2) → s'.mem.readW (wordAddr b j) 32 = s.mem.readW (wordAddr b j) 32) ∧
        (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        Frame [⟨b.setWidth 64, 4 * slots⟩] s.mem s'.mem
  | [], s, _, _, _ => ⟨s, runBlock_nil, fun _ h => absurd h List.not_mem_nil, fun _ _ _ => rfl,
      fun _ _ => rfl, rfl, rfl, Frame.refl _ _⟩
  | p :: L, s, hs, hL, hnd => by
    have hp := hL p List.mem_cons_self
    have hfK := hs.schFit
    have hea : s.ea (at_ .ecx (4 * p.1)) = wordAddr sched p.1 := by
      show addr (s.gpr .ecx) (4 * p.1) = _; rw [hs.ecx]
    have hin : InRegions (s.rd ++ s.wr) (wordAddr sched p.1) 4 :=
      ⟨_, hs.sch, by
        rw [slot_addr (by omega)]
        exact Offset.contains_base _ (by omega) (by omega)⟩
    let v := schW s.mem sched p.1
    let s₁ := s.setReg .eax v
    have e₀ : exec (.mov .eax (.mem (at_ .ecx (4 * p.1)))) s = some s₁ := by
      simp only [exec, readSrc, hea, State.load32, hin, ↓reduceIte, Option.map_some]; rfl
    obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂, -, -, f₂⟩ := stSlot_ok s₁ .eax sb (k := p.2)
      (by rw [show s₁.gpr sb = s.gpr sb from RegUpd.gpr_setReg_of_ne _ _ (by decide), hs.base]) hp.2
      (by rw [show s₁.wr = s.wr from rfl]; exact hs.scr)
    have e₁ : runBlock isa [.mov .eax (.mem (at_ .ecx (4 * p.1))), st p.2 .eax] s = some s₂ := by
      rw [runBlock_cons, e₀, runStep_some]; exact e₂
    have hs₂ : SchedPre s₂ b sched :=
      ⟨by rw [g₂, show s₁.gpr sb = s.gpr sb from RegUpd.gpr_setReg_of_ne _ _ (by decide), hs.base],
        by rw [wr₂]; exact hs.scr,
        by rw [g₂, show s₁.gpr .ecx = s.gpr .ecx from RegUpd.gpr_setReg_of_ne _ _ (by decide), hs.ecx],
        by rw [rd₂, wr₂]; exact hs.sch, hfK, hs.sep⟩
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨s', e', v', o', g', rd', wr', f'⟩ := loads_ok L s₂ hs₂
      (fun q hq => hL q (List.mem_cons_of_mem _ hq)) hnd.2
    have hfit := hs.scr.fit
    have hsch : ∀ i < 32, schW s₂.mem sched i = schW s.mem sched i := by
      intro i hi
      simp only [schW]
      rw [slot_addr (by omega)]
      refine f₂.readW (r := ⟨sched.setWidth 64, 128⟩) (Offset.contains_base _ (by omega) (by omega))
        (fun r hr => ?_) (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      exact hs.sep.sub_right (slot_sub hfit hp.2)
    have m₂' : s₂.mem = s.mem.writeW (wordAddr b p.2) v := by
      rw [m₂, show s₁.mem = s.mem from rfl, show s₁.gpr .eax = v from RegUpd.gpr_setReg_self _ _ _]
    refine ⟨s', ?_, fun q hq => ?_, fun j hj hjL => ?_, fun r hr => ?_, by rw [rd', rd₂]; rfl,
      by rw [wr', wr₂]; rfl, ?_⟩
    · rw [loadsCode, List.flatMap_cons, runBlock_append, e₁, Option.bind_some]; exact e'
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [o' _ hp.2 hnd.1, m₂', readW_slot_write hfit _ hp.2 hp.2, ite_eq_left rfl]
      · rw [v' q hq, hsch _ (hL q (List.mem_cons_of_mem _ hq)).1]
    · simp only [List.map_cons, List.mem_cons, not_or] at hjL
      rw [o' j hj hjL.2, m₂', readW_slot_write hfit _ hj hp.2, ite_eq_right hjL.1]
    · rw [g' r hr, g₂, RegUpd.gpr_setReg_of_ne _ _ hr]
    · exact (f₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact slot_sub hfit hp.2⟩).trans f'

def tableMoves (d : Spec.Seed.Direction) : List (Nat × Nat) := (List.range 32).map fun i => (keySrc d i, tableSlot + i)

theorem keyTable_eq (d : Spec.Seed.Direction) :
    keyTable d = .mov .ecx (.mem (argOp 0)) :: loadsCode (tableMoves d) := by
  cases d <;> decide +kernel

theorem keySrc_lt (d : Spec.Seed.Direction) {i : Nat} (hi : i < 32) : keySrc d i < 32 := by
  cases d <;> simp [keySrc] <;> omega

/-- The table, after `ecx` is loaded: word `i` is the schedule's word `keySrc d i`. -/
theorem table_ok (d : Spec.Seed.Direction) {s : State} {b sched : BitVec 32} (hs : SchedPre s b sched) :
    ∃ s', runBlock isa (loadsCode (tableMoves d)) s = some s' ∧
      (∀ i < 32, s'.mem.readW (wordAddr b (tableSlot + i)) 32 = schW s.mem sched (keySrc d i)) ∧
      (∀ j < slots, (j < tableSlot ∨ tableEnd ≤ j) →
        s'.mem.readW (wordAddr b j) 32 = s.mem.readW (wordAddr b j) 32) ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨b.setWidth 64, 4 * slots⟩] s.mem s'.mem := by
  obtain ⟨s', e', v', o', g', rd', wr', f'⟩ := loads_ok (tableMoves d) s hs
    (by intro p hp
        simp only [tableMoves, List.mem_map, List.mem_range] at hp
        obtain ⟨i, hi, rfl⟩ := hp
        exact ⟨keySrc_lt d hi, by rw [slots_eq, tableSlot_eq]; omega⟩)
    (by cases d <;> decide +kernel)
  refine ⟨s', e', fun i hi => v' (keySrc d i, tableSlot + i) ?_,
    fun j hj hj' => o' j hj ?_, g', rd', wr', f'⟩
  · simp only [tableMoves, List.mem_map, List.mem_range]; exact ⟨i, hi, rfl⟩
  · simp only [tableMoves, List.map_map, List.mem_map, List.mem_range, Function.comp, not_exists, not_and]
    intro i hi he; rw [tableSlot_eq, tableEnd_eq] at *; omega

/-! ## The block function -/

/-- The block function of each direction. -/
def blockFn (sch : Spec.Seed.Schedule) : Spec.Seed.Direction → Spec.Seed.Block → Spec.Seed.Block
  | .encrypt => Spec.Seed.encryptBlock sch
  | .decrypt => Spec.Seed.decryptBlock sch

theorem ecb_eq (sch : Spec.Seed.Schedule) (d : Spec.Seed.Direction) (l : List Spec.Seed.Block) :
    Spec.Seed.ecb sch d l = l.map (blockFn sch d) := by
  cases d <;> rfl

/-- The table's round keys are the schedule's, in the order of `d`. -/
theorem keyPairs_eq (d : Spec.Seed.Direction) (m : Mem) {sched : BitVec 32} (hfit : sched.toNat + 128 ≤ 2 ^ 32)
    {j : Nat} (hj : j < 16) :
    keyPairs (fun i => schW m sched (keySrc d i)) j =
      Spec.Seed.roundKey (Spec.Seed.scheduleAt m (sched.setWidth 64))
        (match d with | .encrypt => j | .decrypt => 15 - j) := by
  have hw : ∀ i < 32, schW m sched i = m.readW (sched.setWidth 64 + BitVec.ofNat 64 (4 * i)) 32 := fun i hi => by
    simp only [schW]; rw [slot_addr (by omega)]
  cases d
  · rw [Proof.Seed.roundKey_readW _ _ hj]
    simp only [keyPairs, keySrc]
    rw [hw _ (by omega), hw _ (by omega), show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, Offset.add_add,
      show 4 * (2 * j) = 8 * j by omega, show 4 * (2 * j + 1) = 8 * j + 4 by omega]
  · show keyPairs _ j = Spec.Seed.roundKey _ (15 - j)
    rw [Proof.Seed.roundKey_readW _ _ (by omega)]
    simp only [keyPairs, keySrc]
    rw [hw _ (by omega), hw _ (by omega), show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, Offset.add_add,
      show 4 * (2 * (15 - 2 * j / 2) + 2 * j % 2) = 8 * (15 - j) by omega,
      show 4 * (2 * (15 - (2 * j + 1) / 2) + (2 * j + 1) % 2) = 8 * (15 - j) + 4 by omega]

theorem outF_spec (d : Spec.Seed.Direction) (m : Mem) {sched : BitVec 32} (hfit : sched.toNat + 128 ≤ 2 ^ 32)
    (D : Addr) (j : Nat) :
    outF m D (fun i => schW m sched (keySrc d i)) j =
      blockFn (Spec.Seed.scheduleAt m (sched.setWidth 64)) d
        (Spec.Seed.blockAt m (D + BitVec.ofNat 64 (16 * j))) := by
  simp only [outF]
  cases d
  · exact crypt_congr (fun i hi => keyPairs_eq .encrypt m hfit hi) _
  · exact crypt_congr (fun i hi => keyPairs_eq .decrypt m hfit hi) _

/-! ## The function -/

theorem ecb_wp (dir : Spec.Seed.Direction) {s₀ : State} (hp : (ecbX86 dir).pre s₀) :
    WP isa (ecb dir) s₀ fun s' => abiPreserved s₀ s' ∧ (ecbX86 dir).post s₀ s' := by
  obtain ⟨hrd, hwr, dKD, dKS, dDS, dAD, dAS, dRD, dRS, fitK, fitD, fitB, fitE⟩ := hp
  let sched := arg s₀ 0
  let D := arg s₀ 1
  let n := (arg s₀ 2).toNat
  let b := arg s₀ 3
  have hfit' : b.toNat + 4 * slots ≤ 2 ^ 32 := fitB
  have hwS : ScrIn s₀.wr b := ⟨by rw [hwr]; simp [b], fitB⟩
  have hwD : (⟨D.setWidth 64, 16 * n⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [D, n]
  have hrK : (⟨sched.setWidth 64, 128⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp [sched]
  have hrA : (⟨argAddr s₀ 0, 16⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp
  -- The arguments, through writes of the scratch buffer.
  have argR : ∀ {m : Mem}, Frame [⟨b.setWidth 64, 4 * slots⟩] s₀.mem m → ∀ i < 4,
      m.readW (argAddr s₀ i) 32 = arg s₀ i := fun hf i hi =>
    hf.readW (arg_contains s₀ fitE hi) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dAS) (by decide)
  have argIn : ∀ {s : State}, s.rd = s₀.rd → s.wr = s₀.wr → s.gpr .esp = s₀.gpr .esp → ∀ i < 4,
      InRegions (s.rd ++ s.wr) (s.ea (argOp i)) 4 := fun h1 h2 h3 i hi => by
    rw [h1, h2, ea_arg h3]; exact ⟨_, List.mem_append_left _ hrA, arg_contains s₀ fitE hi⟩
  have subS : ∀ k < slots, Region.Sub ⟨wordAddr b k, 4⟩ ⟨b.setWidth 64, 4 * slots⟩ :=
    fun k hk => slot_sub hfit' hk
  unfold ecb
  -- The prologue and the table.
  obtain ⟨s₁, e₁, b₁, g₁, sv₁, rd₁, wr₁, f₁, -⟩ := save_ok (k := 3) hwS (argIn rfl rfl rfl 3 (by decide))
    (by rw [ea_arg rfl]; rfl)
  have esp₁ : s₁.gpr .esp = s₀.gpr .esp := g₁ _ (by decide) (by decide)
  obtain ⟨s₁', e₁', c₁', o₁', m₁', rd₁', wr₁'⟩ := ldArg_ok s₁ .ecx 0 (argIn rd₁ wr₁ esp₁ 0 (by decide))
  have ecx₁ : s₁'.gpr .ecx = sched := by rw [c₁', ea_arg esp₁]; exact argR f₁ 0 (by decide)
  have hk₁ : SchedPre s₁' b sched :=
    ⟨by rw [o₁' _ (by decide)]; exact b₁, by rw [wr₁', wr₁]; exact hwS, ecx₁,
      List.mem_append_left _ (by rw [rd₁', rd₁]; exact hrK), fitK, dKS⟩
  obtain ⟨s₂, e₂, t₂, k₂, g₂, rd₂', wr₂', f₂⟩ := table_ok dir hk₁
  have e₁₂ : runBlock isa (saveRegs 3 ++ keyTable dir) s₀ = some s₂ := by
    rw [keyTable_eq, show Instr.mov .ecx (.mem (argOp 0)) :: loadsCode (tableMoves dir) =
        [.mov .ecx (.mem (argOp 0))] ++ loadsCode (tableMoves dir) from rfl,
      runBlock_append, e₁, Option.bind_some, runBlock_append, e₁', Option.bind_some, e₂]
  refine WP.seq (WP.of_runBlock ⟨s₂, e₁₂, ?_⟩)
  let E : Nat → Spec.Seed.Word := fun i => schW s₀.mem sched (keySrc dir i)
  have hfK : sched.toNat + 128 ≤ 2 ^ 32 := fitK
  have hsch : ∀ i < 32, schW s₁'.mem sched i = schW s₀.mem sched i := by
    intro i hi
    simp only [schW]
    rw [m₁', slot_addr (by omega)]
    refine f₁.readW (r := ⟨sched.setWidth 64, 128⟩) (Offset.contains_base _ (by omega) (by omega))
      (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact dKS
  have f₀₂ : Frame [⟨b.setWidth 64, 4 * slots⟩] s₀.mem s₂.mem := f₁.trans (by rw [← m₁']; exact f₂)
  have g₁₂ : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edi → s₂.gpr r = s₀.gpr r := fun r h1 h2 h3 => by
    rw [g₂ r h1, o₁' r h2, g₁ r h1 h3]
  have base₂ : s₂.gpr sb = b := by rw [g₂ _ (by decide), o₁' _ (by decide)]; exact b₁
  have esp₂ : s₂.gpr .esp = s₀.gpr .esp := g₁₂ _ (by decide) (by decide) (by decide)
  have sc₂ : ScrOk s₀ b E s₂.mem := by
    refine ⟨fun e he => ?_, fun i hi => ?_⟩
    · rw [t₂ e he, hsch _ (keySrc_lt dir he)]
    · rw [← sv₁ i hi, ← m₁']
      exact k₂ _ (by rw [savedSlot_eq, slots_eq]; omega) (.inr (by rw [savedSlot_eq, tableEnd_eq]; omega))
  have rd₂ : s₂.rd = s₀.rd := by rw [rd₂', rd₁', rd₁]
  have wr₂ : s₂.wr = s₀.wr := by rw [wr₂', wr₁', wr₁]
  -- The data pointer and the count to their slots.
  obtain ⟨s₃a, e₃a, a₃a, o₃a, m₃a, rd₃a, wr₃a, f₃a⟩ := argSlot_ok s₂ (i := 1) (k := ptrSlot) base₂ (by decide)
    (by rw [wr₂]; exact hwS) (argIn rd₂ wr₂ esp₂ 1 (by decide))
  have f₀₃a : Frame [⟨b.setWidth 64, 4 * slots⟩] s₀.mem s₃a.mem :=
    f₀₂.trans (f₃a.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact subS _ (by decide)⟩)
  have esp₃a : s₃a.gpr .esp = s₀.gpr .esp := by rw [o₃a _ (by decide), esp₂]
  obtain ⟨s₃b, e₃b, a₃b, o₃b, m₃b, rd₃b, wr₃b, f₃b⟩ := argSlot_ok s₃a (i := 2) (k := cntSlot)
    ((o₃a _ (by decide)).trans base₂) (by decide) (by rw [wr₃a, wr₂]; exact hwS)
    (argIn (by rw [rd₃a, rd₂]) (by rw [wr₃a, wr₂]) esp₃a 2 (by decide))
  let s₃ := arithFlags s₃b (s₃b.gpr .eax &&& s₃b.gpr .eax) false false
  have e₃ : runBlock isa [.mov .eax (.mem (argOp 1)), st ptrSlot .eax, .mov .eax (.mem (argOp 2)), st cntSlot .eax,
      .alu .test .eax (.reg .eax)] s₂ = some s₃ := by
    rw [show ([.mov .eax (.mem (argOp 1)), st ptrSlot .eax, .mov .eax (.mem (argOp 2)), st cntSlot .eax,
        .alu .test .eax (.reg .eax)] : List Instr) =
      [.mov .eax (.mem (argOp 1)), .store (slotAt .edi ptrSlot) .eax] ++
        ([.mov .eax (.mem (argOp 2)), .store (slotAt .edi cntSlot) .eax] ++ [.alu .test .eax (.reg .eax)]) from rfl,
      runBlock_append, e₃a, Option.bind_some, runBlock_append, e₃b, Option.bind_some]
    rfl
  refine WP.seq (WP.of_runBlock ⟨s₃, e₃, ?_⟩)
  have eax₃ : s₃b.gpr .eax = arg s₀ 2 := by
    rw [a₃b, ea_arg esp₃a]; exact argR f₀₃a 2 (by decide)
  have dp₃ : s₃.mem.readW (wordAddr b ptrSlot) 32 = D := by
    show s₃b.mem.readW _ 32 = _
    rw [m₃b, readW_slot_write hfit' (j := ptrSlot) (k := cntSlot) _ (by decide) (by decide), ite_eq_right (by decide),
      m₃a, readW_slot_write hfit' (j := ptrSlot) (k := ptrSlot) _ (by decide) (by decide), ite_eq_left rfl,
      ea_arg esp₂]
    exact argR f₀₂ 1 (by decide)
  have np₃ : s₃.mem.readW (wordAddr b cntSlot) 32 = BitVec.ofNat 32 n := by
    show s₃b.mem.readW _ 32 = _
    rw [m₃b, readW_slot_write hfit' (j := cntSlot) (k := cntSlot) _ (by decide) (by decide), ite_eq_left rfl,
      ← a₃b, eax₃]
    simp only [n, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have f₃ : Frame [(⟨wordAddr b ptrSlot, 4⟩ : Region), ⟨wordAddr b cntSlot, 4⟩] s₂.mem s₃.mem :=
    (f₃a.sub fun r hr => ⟨r, by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self, fun _ h => h⟩).trans
      (f₃b.sub fun r hr => ⟨r, by
        rw [List.mem_singleton.mp hr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩)
  have sc₃ : ScrOk s₀ b E s₃.mem := sc₂.frame hfit' f₃ (dn_disj hfit')
  have f₀₃ : Frame [⟨b.setWidth 64, 4 * slots⟩] s₀.mem s₃.mem :=
    f₀₂.trans (f₃.sub fun r hr => ⟨_, List.mem_singleton_self _, dn_sub hfit' r hr⟩)
  have data₃ : ∀ i < 16 * n, s₃.mem (D.setWidth 64 + BitVec.ofNat 64 i) = s₀.mem (D.setWidth 64 + BitVec.ofNat 64 i) :=
    fun i hi => f₀₃.bytes (R := ⟨D.setWidth 64, 16 * n⟩)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dDS) (by simp only; omega) hi
  have fr₃ : Frame [⟨b.setWidth 64, 4 * slots⟩, ⟨D.setWidth 64, 16 * n⟩] s₀.mem s₃.mem :=
    f₀₃.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  have g₃ : ∀ r, r ≠ .eax → s₃.gpr r = s₂.gpr r := fun r hr => by
    show s₃b.gpr r = _; rw [o₃b r hr, o₃a r hr]
  have base₃ : s₃.gpr .edi = b := by rw [g₃ _ (by decide)]; exact base₂
  have esp₃ : s₃.gpr .esp = s₀.gpr .esp := by rw [g₃ _ (by decide), esp₂]
  have rd₃ : s₃.rd = s₀.rd := by show s₃b.rd = _; rw [rd₃b, rd₃a, rd₂]
  have wr₃ : s₃.wr = s₀.wr := by show s₃b.wr = _; rw [wr₃b, wr₃a, wr₂]
  have hz₃ : s₃.zf = some (decide (n = 0)) := by
    rw [RegUpd.zf_arithFlags, eax₃, BitVec.and_self]
    refine congrArg some (Bool.eq_iff_iff.mpr ?_)
    rw [beq_iff_eq, decide_eq_true_iff]
    exact ⟨fun h => by simp only [n, h]; rfl, fun h => BitVec.eq_of_toNat_eq h⟩
  -- The groups.
  refine WP.seq (WP.mono (M := isa) (Q := GDone s₀ b D n E)
    (WP.ite (decide (n = 0)) ((eval_e s₃).trans hz₃) (fun h0 => ?_) (fun h0 => ?_)) fun s₅ d₅ => ?_)
  · have hn0 : n = 0 := by simpa using h0
    exact WP.block_nil ⟨base₃, esp₃, sc₃, fun i hi => by omega, fr₃, rd₃, wr₃⟩
  · have hn0 : n ≠ 0 := by simpa using h0
    refine dataLoop_wp ⟨hwS, hwD, dDS, fitD⟩ ⟨base₃, esp₃, by rw [dp₃]; simp,
      by rw [np₃, Nat.mul_zero, Nat.sub_zero], by omega, sc₃, fun i hi => ?_, fr₃, rd₃, wr₃⟩
    rw [data₃ i hi, ite_eq_right (by omega)]
  -- The epilogue.
  obtain ⟨s₆, e₆, rg₆, o₆, m₆, -, -⟩ := restore_ok (s₀ := s₀) (b := b) (by rw [d₅.wr]; exact hwS) d₅.base
    d₅.scr.saved
  refine WP.of_runBlock ⟨s₆, e₆, ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact rg₆ 0 (by decide)
    · exact rg₆ 1 (by decide)
    · exact rg₆ 2 (by decide)
    · exact rg₆ 3 (by decide)
    · rw [o₆ _ (fun i hi => by revert i; decide), d₅.esp]
  · rw [m₆]
    exact d₅.frame.readW (r := ⟨(s₀.gpr .esp).setWidth 64, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dRS
      · exact dRD) (by decide)
  · have hd₆ : DInv s₀.mem s₆.mem (D.setWidth 64) n n (outF s₀.mem (D.setWidth 64) E) := fun i hi => by
      rw [m₆]; exact d₅.data i hi
    show Spec.Seed.blocksAt s₆.mem (D.setWidth 64) n = _
    rw [blocksAt_of_dinv hd₆, ecb_eq]
    simp only [Spec.Seed.blocksAt, List.map_map]
    refine List.map_congr_left fun j _ => ?_
    exact outF_spec dir s₀.mem hfK _ j

end VG.Proof.Seed.X86
