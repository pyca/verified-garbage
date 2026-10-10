import VerifiedGarbage.Proof.TripleDes.X86.Head
import VerifiedGarbage.Proof.TripleDes.X86.RestoredOutput
import VerifiedGarbage.Proof.Rc2.X86.BlockArgs
import VerifiedGarbage.Spec.TripleDes.Contract
import VerifiedGarbage.Proof.TripleDes.X86.Body
import VerifiedGarbage.Proof.TripleDes.X86.WordStore
import VerifiedGarbage.Proof.TripleDes.Schedule

/-! ## `RestoredTail` -/

section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (addr32)

structure RestoredTailPost (original origin : State) (x : BitVec 64) (s : State) : Prop where
  result : Spec.TripleDes.blockAt s.mem (addr32 (dataArg origin)) =
    Spec.TripleDes.encodeBlock (Spec.TripleDes.permute Spec.TripleDes.fp x)
  saved : ∀ r ∈ savedRegs, s.gpr r = original.gpr r
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  sp : s.gpr .esp = origin.gpr .esp
  frame : Frame [⟨addr32 (dataArg origin), 8⟩, workRegion origin] origin.mem s.mem

theorem blockTailRestored_ok (original s : State) (x : BitVec 64) (hword : WordState x s)
    (hsaved : Saved original s) (hok : Ok sboxCfg s)
    (dataFit : (dataArg s).toNat + 8 ≤ 2 ^ 32)
    (harg : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) 2) 4)
    (hargSep : (⟨wordAddr (s.gpr .esp) 2, 4⟩ : Region).Disjoint (workRegion s))
    (hw : ∀ i < 2, InRegions s.wr (wordAddr (dataArg s) i) 4)
    (hread : ∀ i < 4, InRegions (s.rd ++ s.wr) (addr32 (s.gpr .ebp) + BitVec.ofNat 64 (4 * i)) 4) :
    WP isa (.block (finalSave ++ blockRestore ++ restoredOutput)) s (RestoredTailPost original s x) := by
  rw [WP.block_append_iff, WP.block_append_iff]
  apply WP.mono (finalSave_ok s hok)
  intro s₁ h₁
  have saved₁ := hsaved.congr h₁.bp h₁.frame
  have reads₁ : ∀ i < 4, InRegions (s₁.rd ++ s₁.wr) (addr32 (s₁.gpr .ebp) + BitVec.ofNat 64 (4 * i)) 4 := by
    rw [h₁.rd, h₁.wr, h₁.bp]; exact hread
  apply WP.mono (blockRestore_ok original s₁ saved₁ (by rw [h₁.bp]; exact hok.fit) reads₁)
  intro s₂ h₂
  have sp₂ : s₂.gpr .esp = s.gpr .esp := h₂.sp.trans h₁.sp
  have ptr₂ : s₂.gpr .eax = s.gpr .ebp := h₂.ptr.trans h₁.bp
  have rd₂ : s₂.rd = s.rd := h₂.rd.trans h₁.rd
  have wr₂ : s₂.wr = s.wr := h₂.wr.trans h₁.wr
  have data₂ : dataArg s₂ = dataArg s := by
    unfold dataArg
    rw [sp₂, h₂.mem]
    exact h₁.frame.readW (r := ⟨wordAddr (s.gpr .esp) 2, 4⟩) (Region.contains_self _ _)
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hargSep) (by decide)
  have input₂ : finalWord s₂ = Spec.TripleDes.permute Spec.TripleDes.fp x := by
    unfold finalWord
    rw [ptr₂, h₂.mem]
    change (s₁.mem.readW (wordAddr (s.gpr .ebp) 7) 32 ++
      s₁.mem.readW (wordAddr (s.gpr .ebp) 6) 32 : BitVec 64) =
        Spec.TripleDes.permute Spec.TripleDes.fp x
    rw [h₁.hi, h₁.lo, VG.Proof.TripleDes.halves_append, hword.left, hword.right,
      VG.Proof.TripleDes.halves_append]
  have reads₂ : ∀ k ∈ [24, 28], InRegions (s₂.rd ++ s₂.wr) (addr (s₂.gpr .eax) k) 4 := by
    intro k hk
    rw [rd₂, wr₂, ptr₂]
    have hwk : InRegions s.wr (addr (s.gpr .ebp) k) 4 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl
      · exact hok.slotIn 6 (by decide)
      · exact hok.slotIn 7 (by decide)
    obtain ⟨r, hr, hc⟩ := hwk
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have arg₂ : InRegions (s₂.rd ++ s₂.wr) (wordAddr (s₂.gpr .esp) 2) 4 := by
    rw [rd₂, wr₂, sp₂]; exact harg
  have writes₂ : ∀ i < 2, InRegions s₂.wr (wordAddr (dataArg s₂) i) 4 := by
    rw [wr₂, data₂]; exact hw
  obtain ⟨s₃, run₃, mem₃, rd₃, wr₃, regs₃⟩ := restoredOutput_ok s₂
    (by rw [data₂]; exact dataFit) arg₂ reads₂ writes₂
  have hm : s₃.mem = s₁.mem.writeW (addr32 (dataArg s))
      (byteRev64 (Spec.TripleDes.permute Spec.TripleDes.fp x)) := by
    rw [mem₃, data₂, input₂, h₂.mem]
  refine WP.of_runBlock ⟨s₃, run₃, ⟨?_, ?_, rd₃.trans rd₂, wr₃.trans wr₂,
    (regs₃ .esp (by decide) (by decide) (by decide)).trans sp₂, ?_⟩⟩
  · rw [hm]
    exact blockAt_writeW _ _ _
  · intro r hr
    have neq : ∀ r ∈ savedRegs, r ≠ .eax ∧ r ≠ .ecx ∧ r ≠ .edx := by decide
    exact (regs₃ r (neq r hr).1 (neq r hr).2.1 (neq r hr).2.2).trans (h₂.saved r hr)
  · rw [hm]
    exact (h₁.frame.mono (by intro r hr; obtain rfl := List.mem_singleton.mp hr; simp)).writeW
      (List.mem_cons_self) _ (Region.contains_self _ _)

end VG.Proof.TripleDes.X86

end

/-! ## `Block` -/

section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Spec.TripleDes (Direction Schedule)
open VG.Proof.Rc2.X86 (addr32)

def blockResult (keys : Schedule) (d : Direction) (b : Spec.TripleDes.Block) : Spec.TripleDes.Block :=
  match d with
  | .encrypt => Spec.TripleDes.encryptBlock keys b
  | .decrypt => Spec.TripleDes.decryptBlock keys b

theorem blockResult_core (keys : Schedule) (d : Direction) (b : Spec.TripleDes.Block) :
    Spec.TripleDes.encodeBlock (Spec.TripleDes.permute Spec.TripleDes.fp
      (blockCore (Spec.TripleDes.componentSchedule keys) d
        (Spec.TripleDes.permute Spec.TripleDes.ip (Spec.TripleDes.decodeBlock b)))) = blockResult keys d b := by
  cases d
  · exact (VG.Proof.TripleDes.encryptBlock_eq_cores keys b).symm
  · exact (VG.Proof.TripleDes.decryptBlock_eq_cores keys b).symm

def blockRegions (s : State) : List Region :=
  [⟨addr32 (dataArg s), 8⟩, ⟨addr32 (scratchArg s 3), 512⟩]

structure BlockPost (keys : Schedule) (d : Direction) (original s : State) : Prop where
  result : Spec.TripleDes.blockAt s.mem (addr32 (dataArg original)) =
    blockResult keys d (Spec.TripleDes.blockAt original.mem (addr32 (dataArg original)))
  saved : ∀ r ∈ savedRegs, s.gpr r = original.gpr r
  rd : s.rd = original.rd
  wr : s.wr = original.wr
  sp : s.gpr .esp = original.gpr .esp
  frame : Frame (blockRegions original) original.mem s.mem

theorem block_ok (keys : Schedule) (base : BitVec 32) (d : Direction) (s : State)
    (hp : HeadPre (Spec.TripleDes.componentSchedule keys) base s)
    (hread : ∀ i < 4, InRegions (s.rd ++ s.wr) (addr32 (scratchArg s 3) + BitVec.ofNat 64 (4 * i)) 4)
    (hwrite : ∀ i < 2, InRegions s.wr (wordAddr (dataArg s) i) 4)
    (hargSep : (⟨wordAddr (s.gpr .esp) 2, 4⟩ : Region).Disjoint (workRegion (prepared s))) :
    WP isa (block d) s (BlockPost keys d s) := by
  rw [block]
  apply WP.seq
  apply WP.mono (blockHead_ok (Spec.TripleDes.componentSchedule keys) base s hp)
  intro s₁ h₁
  apply WP.seq
  apply WP.mono (blockBody_ok (Spec.TripleDes.componentSchedule keys) base s₁ _ d h₁.ready h₁.word)
  intro s₂ h₂
  have stable := h₂.2.2
  have bp₂ : s₂.gpr .ebp = scratchArg s 3 := stable.bp.trans h₁.bp
  have sp₂ : s₂.gpr .esp = s.gpr .esp := stable.sp.trans h₁.sp
  have work₁ : workRegion s₁ = workRegion (prepared s) := by
    unfold workRegion prepared
    rw [h₁.bp, VG.X86.RegUpd.gpr_setReg_self]
  have data₂ : dataArg s₂ = dataArg s := by
    unfold dataArg
    rw [stable.sp]
    have sep : (⟨wordAddr (s₁.gpr .esp) 2, 4⟩ : Region).Disjoint (workRegion s₁) := by
      rw [h₁.sp, work₁]
      exact hargSep
    have hm := stable.frame.readW (a := wordAddr (s₁.gpr .esp) 2) (w := 32)
      (r := ⟨wordAddr (s₁.gpr .esp) 2, 4⟩) (Region.contains_self _ _)
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact sep) (by decide)
    exact hm.trans h₁.data
  have saved₂ := h₁.saved.congr stable.bp stable.frame
  have reads₂ : ∀ i < 4, InRegions (s₂.rd ++ s₂.wr) (addr32 (s₂.gpr .ebp) + BitVec.ofNat 64 (4 * i)) 4 := by
    rw [stable.rd, stable.wr, h₁.rd, h₁.wr, bp₂]; exact hread
  have writes₂ : ∀ i < 2, InRegions s₂.wr (wordAddr (dataArg s₂) i) 4 := by
    rw [stable.wr, h₁.wr, data₂]; exact hwrite
  have arg₂ : InRegions (s₂.rd ++ s₂.wr) (wordAddr (s₂.gpr .esp) 2) 4 := by
    rw [stable.rd, stable.wr, h₁.rd, h₁.wr, sp₂]; exact hp.argRead 2 (by decide)
  have work₂ : workRegion s₂ = workRegion (prepared s) := by
    unfold workRegion prepared
    rw [bp₂, VG.X86.RegUpd.gpr_setReg_self]
  apply WP.mono (blockTailRestored_ok s s₂ _ h₂.1 saved₂ h₂.2.1.spills
    (by rw [data₂]; exact hp.dataFit) arg₂
    (by rw [sp₂, work₂]; exact hargSep) writes₂ reads₂)
  intro s₃ h₃
  refine ⟨?_, h₃.saved, h₃.rd.trans (stable.rd.trans h₁.rd), h₃.wr.trans (stable.wr.trans h₁.wr),
    h₃.sp.trans sp₂, ?_⟩
  · have hr := h₃.result
    rw [data₂] at hr
    exact hr.trans (blockResult_core keys d _)
  · have hf₁ : Frame (blockRegions s) s.mem s₁.mem := h₁.frame.sub (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨⟨addr32 (scratchArg s 3), 512⟩, by simp [blockRegions], Region.sub_prefix (by decide)⟩)
    have hf₂ : Frame (blockRegions s) s₁.mem s₂.mem := stable.frame.sub (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      refine ⟨⟨addr32 (scratchArg s 3), 512⟩, by simp [blockRegions], ?_⟩
      unfold workRegion
      rw [h₁.bp]
      exact Offset.sub_base _ (by decide))
    have hf₃ : Frame (blockRegions s) s₂.mem s₃.mem := h₃.frame.sub (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [data₂]
        exact ⟨⟨addr32 (dataArg s), 8⟩, by simp [blockRegions], fun _ h => h⟩
      · refine ⟨⟨addr32 (scratchArg s 3), 512⟩, by simp [blockRegions], ?_⟩
        unfold workRegion
        rw [bp₂]
        exact Offset.sub_base _ (by decide))
    exact hf₁.trans (hf₂.trans hf₃)

end VG.Proof.TripleDes.X86

end

/-! ## `Contract` -/

section

namespace VG.Proof.TripleDes.X86
open VG VG.X86
open VG.Proof.Rc2.X86 (addr32)
open VG.Spec.TripleDes (Direction)

/-- The IA-32 calling convention and memory layout used by the block proof. -/
def blockContract (d : Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨addr32 (arg s 0), 384⟩
    let data : Region := ⟨addr32 (arg s 1), 8⟩
    let scratch : Region := ⟨addr32 (arg s 2), 512⟩
    let args : Region := ⟨argAddr s 0, 12⟩
    let ret : Region := ⟨addr32 (s.gpr .esp), 4⟩
    s.rd = [key, args] ∧ s.wr = [data, scratch] ∧ key.Disjoint scratch ∧ data.Disjoint scratch ∧
      args.Disjoint data ∧ args.Disjoint scratch ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
      (arg s 0).toNat + 384 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 8 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 512 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 16 ≤ 2 ^ 32
  post s s' := Spec.TripleDes.blockAt s'.mem (addr32 (arg s 1)) =
    blockResult (Spec.TripleDes.scheduleAt s.mem (addr32 (arg s 0))) d
      (Spec.TripleDes.blockAt s.mem (addr32 (arg s 1)))
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 3, arg s₁ i = arg s₂ i

end VG.Proof.TripleDes.X86

end

/-! ## `ScheduleMemory` -/

section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Straight
open VG.Spec.TripleDes (Direction)
open VG.Proof.Rc2.X86 (addr32)
def selectedRound (d : Direction) (j : Nat) : Nat := if d = .encrypt then j else 15 - j

theorem selectedRound_bound (d : Direction) (j : Nat) (hj : j < 16) : selectedRound d j < 16 := by
  cases d <;> simp only [selectedRound, reduceCtorEq, ite_true, ite_false] <;> omega

theorem keyAddr_component (base : BitVec 32) (c : Nat) (d : Direction) (j : Nat) :
    keyAddr (componentBase base c) d j = base + BitVec.ofNat 32 (8 * (16 * c + selectedRound d j)) := by
  unfold keyAddr componentBase selectedRound
  rw [Offset.add_ofNat_add_ofNat]
  exact congrArg (fun n => base + BitVec.ofNat 32 n) (by omega)

theorem keyWordAddress (base : BitVec 32) (fit : base.toNat + 384 ≤ 2 ^ 32)
    (c j t : Nat) (hc : c < 3) (hj : j < 16) (ht : t < 2) (d : Direction) :
    wordAddr (keyAddr (componentBase base c) d j) t =
      addr32 base + BitVec.ofNat 64 (8 * (16 * c + selectedRound d j) + 4 * t) := by
  have bound := selectedRound_bound d j hj
  rw [wordAddr, keyAddr_component]
  unfold addr
  rw [Offset.add_ofNat_add_ofNat]
  exact VG.Proof.Rc2.X86.addr_add (by omega)

theorem readKey_component (m : Mem) (base : BitVec 32)
    (fit : base.toNat + 384 ≤ 2 ^ 32) (c j : Nat) (hc : c < 3) (hj : j < 16) (d : Direction) :
    readKey m (keyAddr (componentBase base c) d j) =
      m.readW (addr32 base + BitVec.ofNat 64 (8 * (16 * c + selectedRound d j))) 64 := by
  rw [readKey, keyWordAddress base fit c j 1 hc hj (by decide) d,
    keyWordAddress base fit c j 0 hc hj (by decide) d]
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one]
  rw [← Offset.add_ofNat_add_ofNat]
  exact readW_pair m _

theorem ready_of_regions (s : State) (base : BitVec 32) (hok : Ok sboxCfg s)
    (hb : scheduleArg s = base) (fit : base.toNat + 384 ≤ 2 ^ 32)
    (hread : ∀ p, (⟨addr32 base, 384⟩ : Region).Contains p 4 → InRegions (s.rd ++ s.wr) p 4)
    (hdis : (⟨addr32 base, 384⟩ : Region).Disjoint ⟨addr32 (s.gpr .ebp), 512⟩)
    (harg : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) 1) 4)
    (hargSep : (⟨wordAddr (s.gpr .esp) 1, 4⟩ : Region).Disjoint (workRegion s)) :
    Ready (Spec.TripleDes.componentSchedule (Spec.TripleDes.scheduleAt s.mem (addr32 base))) base s := by
  have workSub : Region.Sub (workRegion s) ⟨addr32 (s.gpr .ebp), 512⟩ :=
    Offset.sub_base _ (by decide)
  have keySub : ∀ c < 3, ∀ d : Direction, ∀ j < 16, ∀ t < 2,
      Region.Sub ⟨wordAddr (keyAddr (componentBase base c) d j) t, 4⟩ ⟨addr32 base, 384⟩ := by
    intro c hc d j hj t ht
    rw [keyWordAddress base fit c j t hc hj ht d]
    have bound := selectedRound_bound d j hj
    exact Offset.sub_base _ (by omega)
  refine ⟨hok, hb, harg, hargSep, ?_, ?_, ?_, ?_⟩
  · intro c hc d j hj t ht
    apply hread
    rw [keyWordAddress base fit c j t hc hj ht d]
    have bound := selectedRound_bound d j hj
    exact Offset.contains_base _ (by omega) (by omega)
  · intro c hc d j hj t ht
    exact (hdis.sub_left (keySub c hc d j hj t ht)).sub_right workSub
  · intro c hc d j hj k hk t ht
    have scratchFit : (s.gpr .ebp).toNat + 512 ≤ 2 ^ 32 := hok.fit
    apply hdis.symm.sep
    · rw [wordAddr, addr_eq (by omega)]
      exact Offset.contains_base _ (by omega) (by omega)
    · rw [keyWordAddress base fit c j t hc hj ht d]
      have bound := selectedRound_bound d j hj
      exact Offset.contains_base _ (by omega) (by omega)
  · intro c hc d j hj
    rw [readKey_component s.mem base fit c j hc hj d]
    exact (VG.Proof.TripleDes.componentSchedule_readW s.mem (addr32 base) c
      (selectedRound d j) hc (selectedRound_bound d j hj)).symm

end VG.Proof.TripleDes.X86

end

/-! ## `Pre` -/

section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.RegUpd VG.X86.Straight
open VG.Proof.Rc2.X86 (addr32 argContainsCount)
open VG.Spec.TripleDes (Direction)

theorem argument_word (s : State) (i : Nat) : arg s i = s.mem.readW (wordAddr (s.gpr .esp) (i + 1)) 32 := by
  unfold arg argAddr
  apply congrArg (fun p => s.mem.readW p 32)
  change addr (s.gpr .esp) (4 + 4 * i) = addr (s.gpr .esp) (4 * (i + 1))
  exact congrArg (addr (s.gpr .esp)) (by omega)

theorem data_argument (s : State) : dataArg s = arg s 1 := (argument_word s 1).symm

theorem scratch_argument (s : State) : scratchArg s 3 = arg s 2 := (argument_word s 2).symm

theorem schedule_argument (s : State) : scheduleArg s = arg s 0 := (argument_word s 0).symm

theorem headPre_of_contract (d : Direction) (s : State) (hs : (blockContract d).pre s) :
    HeadPre (Spec.TripleDes.componentSchedule (Spec.TripleDes.scheduleAt s.mem (addr32 (arg s 0))))
      (arg s 0) s := by
  obtain ⟨hrd, hwr, keySep, dataSep, argsData, argsScratch, _, _, keyFit, dataFit, scratchFit, spFit⟩ := hs
  have bp : (prepared s).gpr .ebp = arg s 2 := by rw [prepared, gpr_setReg_self, scratch_argument]
  have sp : (prepared s).gpr .esp = s.gpr .esp := gpr_setReg_of_ne s _ (by decide)
  have saveSub : Region.Sub (saveRegion s) ⟨addr32 (arg s 2), 512⟩ := by
    rw [saveRegion, scratch_argument]
    exact Region.sub_prefix (by decide)
  have workSub : Region.Sub (workRegion (prepared s)) ⟨addr32 (arg s 2), 512⟩ := by
    rw [workRegion, bp]
    exact Offset.sub_base _ (by decide)
  have argContains : ∀ i ∈ [1, 2, 3], (⟨argAddr s 0, 12⟩ : Region).Contains
      (wordAddr (s.gpr .esp) i) 4 := by
    intro i hi
    have hb : 1 ≤ i ∧ i ≤ 3 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> decide
    rw [wordAddr, addr_eq (by omega)]
    have h := argContainsCount s 3 spFit (i - 1) (by omega)
    rw [show 4 + 4 * (i - 1) = 4 * i by omega] at h
    exact h
  have argSub : ∀ i ∈ [1, 2, 3], Region.Sub ⟨wordAddr (s.gpr .esp) i, 4⟩ ⟨argAddr s 0, 12⟩ := by
    intro i hi a ha
    exact (argContains i hi).byte (by change (a - wordAddr (s.gpr .esp) i).toNat + 1 ≤ 4 at ha; omega)
  have argRead : ∀ i ∈ [1, 2, 3], InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) i) 4 := by
    intro i hi
    rw [hrd, hwr]
    exact ⟨⟨argAddr s 0, 12⟩, by simp, argContains i hi⟩
  have slots : ∀ i < 128, InRegions (prepared s).wr (wordAddr ((prepared s).gpr .ebp) i) 4 := by
    intro i hi
    rw [bp, wordAddr, addr_eq (by omega)]
    change InRegions s.wr _ 4
    rw [hwr]
    exact ⟨⟨addr32 (arg s 2), 512⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hok : Ok sboxCfg (prepared s) := by
    refine ⟨slots, ?_, ?_, ?_⟩
    · intro k hk; change k < 0 at hk; omega
    · change ((prepared s).gpr .ebp).toNat + 512 ≤ 2 ^ 32
      rw [bp]; exact scratchFit
    · intro k hk j hj; change j < 0 at hj; omega
  have hb : scheduleArg (prepared s) = arg s 0 := by
    unfold scheduleArg
    rw [sp]
    exact (argument_word s 0).symm
  have ready := ready_of_regions (prepared s) (arg s 0) hok hb keyFit
    (by intro p hp
        change InRegions (s.rd ++ s.wr) p 4
        rw [hrd, hwr]
        exact ⟨⟨addr32 (arg s 0), 384⟩, by simp, hp⟩)
    (by rw [bp]; exact keySep)
    (by change InRegions (s.rd ++ s.wr) (wordAddr ((prepared s).gpr .esp) 1) 4
        rw [sp]; exact argRead 1 (by decide))
    (by rw [sp]; exact (argsScratch.sub_left (argSub 1 (by decide))).sub_right workSub)
  refine ⟨ready, ?_, ?_, ?_, argRead, ?_, ?_, dataSep.sub_right saveSub, ?_⟩
  · rw [scratch_argument]; exact scratchFit
  · rw [data_argument]; exact dataFit
  · intro i hi
    rw [scratch_argument, hwr]
    exact ⟨⟨addr32 (arg s 2), 512⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  · intro i hi
    exact (argsScratch.sub_left (argSub i hi)).sub_right saveSub
  · intro i hi
    rw [data_argument, wordAddr, addr_eq (by omega), hrd, hwr]
    exact ⟨⟨addr32 (arg s 1), 8⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  · intro c hc direction j hj t ht
    have keySub : Region.Sub ⟨wordAddr (keyAddr (componentBase (arg s 0) c) direction j) t, 4⟩
        ⟨addr32 (arg s 0), 384⟩ := by
      rw [keyWordAddress _ keyFit c j t hc hj ht direction]
      have bound := selectedRound_bound direction j hj
      exact Offset.sub_base _ (by omega)
    exact (keySep.sub_left keySub).sub_right saveSub

end VG.Proof.TripleDes.X86

end

/-! ## `CorrectBlock` -/

section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (addr32 argContainsCount)
open VG.Spec.TripleDes (Direction)

theorem block_correct (d : Direction) (s : State) (hs : (blockContract d).pre s) :
    WP isa (block d) s (fun s' => abiPreserved s s' ∧ (blockContract d).post s s') := by
  have hp := headPre_of_contract d s hs
  obtain ⟨_, hwr, _, _, _, argsScratch, retData, retScratch, _, dataFit, _, spFit⟩ := hs
  have hwrite : ∀ i < 2, InRegions s.wr (wordAddr (dataArg s) i) 4 := by
    intro i hi
    rw [data_argument, wordAddr, addr_eq (by omega), hwr]
    exact ⟨⟨addr32 (arg s 1), 8⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hread : ∀ i < 4, InRegions (s.rd ++ s.wr) (addr32 (scratchArg s 3) + BitVec.ofNat 64 (4 * i)) 4 := by
    intro i hi
    obtain ⟨r, hr, hc⟩ := hp.saveWrite i hi
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have hargSep : (⟨wordAddr (s.gpr .esp) 2, 4⟩ : Region).Disjoint (workRegion (prepared s)) := by
    have sub : Region.Sub ⟨wordAddr (s.gpr .esp) 2, 4⟩ ⟨argAddr s 0, 12⟩ := by
      rw [wordAddr, addr_eq (by omega), VG.Proof.Rc2.X86.argAddr_eq s 0 (by omega)]
      exact Offset.sub _ (by decide) (by decide)
    have workSub : Region.Sub (workRegion (prepared s)) ⟨addr32 (arg s 2), 512⟩ := by
      unfold workRegion prepared
      rw [VG.X86.RegUpd.gpr_setReg_self, scratch_argument]
      exact Offset.sub_base _ (by decide)
    exact (argsScratch.sub_left sub).sub_right workSub
  apply WP.mono (block_ok (Spec.TripleDes.scheduleAt s.mem (addr32 (arg s 0)))
    (arg s 0) d s hp hread hwrite hargSep)
  intro s' hpost
  refine ⟨⟨?_, ?_⟩, hpost.result⟩
  · intro r hr
    have hregs : ∀ r ∈ calleeSaved, r ∈ savedRegs ∨ r = .esp := by decide
    rcases hregs r hr with h | rfl
    · exact hpost.saved r h
    · exact hpost.sp
  · apply hpost.frame.readW (r := ⟨addr32 (s.gpr .esp), 4⟩) (Region.contains_self _ _) _ (by decide)
    intro r hr
    simp only [blockRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact retData
    · exact retScratch

end VG.Proof.TripleDes.X86

end
