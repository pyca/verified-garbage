module

public import VerifiedGarbage.Proof.Rc2.X86.Key
public import VerifiedGarbage.Impl.Rc2.X86.Ssse3
public import VerifiedGarbage.Proof.Rc2.Expansion
import VerifiedGarbage.Proof.Rc2.X86.Ssse3Lookup
import VerifiedGarbage.Proof.Rc2.X86.Ssse3Lit
import VerifiedGarbage.Proof.Rc2.X86.KeyIO
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.X86.SymFrame
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.Reduce
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Rc2.X86.Key
meta import VerifiedGarbage.Impl.Rc2.X86.Ssse3
meta import VerifiedGarbage.Proof.Rc2.Expansion
meta import VerifiedGarbage.Proof.Rc2.X86.Ssse3Lookup
meta import VerifiedGarbage.Proof.Rc2.X86.Ssse3Lit
meta import VerifiedGarbage.Proof.Rc2.X86.KeyIO
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Framework.X86.SymFrame
meta import VerifiedGarbage.Proof.Framework.X86.Syms
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86.Reduce
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# Verified RC2 key expansion on x86 with PITABLE read by `pshufb`

`Impl.Rc2.X86.Ssse3.expandKey` meets the baseline's contract
(`keyContract`) with four bytes of stack (`keyContractS 4`), in constant
time: `key`, the key expansion `init` calls. The loops are the baseline's,
proven for any look-up (`LookOk`, `Proof/Rc2/X86/KeyIO.lean`); the look-up
is `Ssse3.piLookup_ok`, with the table's address in EBP, which the function
takes in a frame of its own after the copy of the key (`symFrame_ok`).
-/

@[expose] public section

namespace VG.Proof.Rc2.X86.Ssse3

open VG VG.X86 VG.X86.RegUpd VG.Impl.Rc2.X86 VG.Impl.Rc2.X86.Ssse3
open VG.Impl.Rc2 (piSym)

/-- What the look-up needs: the 16 bytes at EDI writable, and the table's address in EBP. -/
def LookPre (s : State) : Prop := InRegions s.wr (addr32 (s.gpr .edi)) 16 ∧ s.gpr .ebp = s.syms piSym

theorem lookOk : LookOk Ssse3.piLookup LookPre where
  run s h := by
    have hw : InRegions s.wr (addr (s.gpr .edi) 0) 16 := by
      rw [show addr (s.gpr .edi) 0 = (s.gpr .edi).setWidth 64 by simp only [addr, BitVec.add_zero]]
      exact h.1
    refine WP.mono (piLookup_ok s hw h.2) fun t ⟨h1, hg, hm, hrd, hwr⟩ => ⟨h1, ⟨fun r hr => ?_, hm, hrd, hwr⟩⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    exact hg r hr.1 hr.2.1 hr.2.2
  keep s s' h wr edi ebp sy := by
    refine ⟨?_, ?_⟩
    · rw [wr, edi]; exact h.1
    · rw [ebp, sy]; exact h.2

/-- The table's address from EAX into EBP, and the count of the copy back into ECX. -/
theorem takeBase_ok (s : State) :
    ∃ s', runBlock isa [rr .ebp .eax, rr .ecx .esi] s = some s' ∧
      s'.gpr .ebp = s.gpr .eax ∧ s'.gpr .ecx = s.gpr .esi ∧ Keep [.ebp, .ecx] s s' := by
  refine ⟨(s.setReg .ebp (s.gpr .eax)).setReg .ecx (s.gpr .esi), by
    simp only [runBlock_cons, reduceExec, rr, readSrc, Option.map_some, runStep_some, runBlock_nil,
      gpr_setReg, reduceCtorEq, ↓reduceIte], ?_, ?_, ?_⟩
  · simp only [gpr_setReg, reduceCtorEq, ↓reduceIte]
  · simp only [gpr_setReg, ↓reduceIte]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, hr.1, hr.2, ite_false]
    · simp only [mem_setReg]
    · simp only [rd_setReg]
    · simp only [wr_setReg]

theorem prefix_frame {m m' : Mem} {p : Addr} {l : Proof.Rc2.KeyBytes} {n : Nat} {rs : List Region}
    (h : Proof.Rc2.BytesPrefix m p l n) (hn : n ≤ 128) (frame : Frame rs m m')
    (sep : ∀ r ∈ rs, (Region.mk p 128).Disjoint r) : Proof.Rc2.BytesPrefix m' p l n := by
  intro i hi
  rw [← h i hi]
  exact frame.bytes (R := ⟨p, 128⟩) sep (show (128 : Nat) ≤ 2 ^ 64 by decide) (show i < 128 by omega_using [hi, hn])

theorem key_body_correct (s : State) (hs : (keyContractS 4).pre s) :
    WP isa Ssse3.expandKey s (fun s' => abiPreserved s s' ∧ keyContract.post s s') := by
  obtain ⟨⟨hrd, hwr, keyOut, keyScratch, outScratch, argsOut, argsScratch, retOut, retScratch, keyFit, outFit,
    scratchFit, spFit, ht, ht', hb, hb'⟩, spLo, stkOut, stkScratch⟩ := hs
  obtain writes : ∀ i < 4, InRegions s.wr (addr32 (arg s 4) + BitVec.ofNat 64 (4 * i)) 4 := by
    intro i hi
    rw [hwr]
    exact ⟨⟨addr32 (arg s 4), 512⟩, by simp, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  have argRead (st : State) (rd : st.rd = s.rd) (wr : st.wr = s.wr)
      (sp : st.gpr .esp = s.gpr .esp) : ∀ i < 5, InRegions (st.rd ++ st.wr) (argAddr st i) 4 := by
    intro i hi
    obtain fit : (st.gpr .esp).toNat + 24 ≤ 2 ^ 32 := by rw [sp]; exact spFit
    rw [argAddr_eq st i (by omega_using [hi, fit]), sp, rd, wr, hrd, hwr]
    exact ⟨⟨argAddr s 0, 20⟩, by simp, argContains s spFit i hi⟩
  -- The stack the function uses is apart from the arguments and the return address.
  obtain stkEq : below (s.gpr .esp) 4 = ⟨addr32 (s.gpr .esp) - BitVec.ofNat 64 4, 4⟩ := by
    show (⟨(s.gpr .esp - BitVec.ofNat 32 4).setWidth 64, 4⟩ : Region) = _
    rw [Taint.sub_setWidth spLo]; rfl
  obtain argsStk : (Region.mk (argAddr s 0) 20).Disjoint (below (s.gpr .esp) 4) := by
    rw [stkEq, argAddr_eq s 0 (by omega_using [spFit])]
    exact Offset.disjoint_below _ (by decide)
  obtain retStk : (Region.mk (addr32 (s.gpr .esp)) 4).Disjoint (below (s.gpr .esp) 4) := by
    rw [stkEq]; exact Offset.base_disjoint_below _ (by decide)
  rw [Ssse3.expandKey]
  apply WP.seq
  obtain ⟨s₀, run₀, scratch₀, keep₀⟩ := loadArg_ok s .eax 4 (argRead s rfl rfl rfl 4 (by decide))
  refine WP.of_runBlock ⟨s₀, run₀, ?_⟩
  have gpr₀ (r : Reg) (hr : r ≠ .eax) : s₀.gpr r = s.gpr r := keep₀.reg r (by simpa using hr)
  apply WP.seq
  rw [WP.block_append_iff, keySave_eq]
  apply WP.mono (saveCode_ok s₀ .eax savedReg 4 (by decide)
    (by rw [scratch₀]; omega_using [scratchFit]) (by rw [keep₀.wr, scratch₀]; exact writes))
  intro s₁ h₁
  obtain sp₁ : s₁.gpr .esp = s.gpr .esp := by rw [h₁.1]; exact gpr₀ .esp (by decide)
  obtain savedFrame : Frame [⟨addr32 (arg s 4), 512⟩] s.mem s₁.mem := by
    rw [h₁.2.2.2, keep₀.mem, scratch₀]
    apply (saveMem_frame_le _ _ _ 4 64 (by decide) (by decide)).sub
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact ⟨⟨addr32 (arg s 4), 512⟩, List.mem_cons_self, Region.sub_prefix (by decide)⟩
  obtain args₁ : ∀ i < 5, arg s₁ i = arg s i :=
    args_frame savedFrame sp₁ spFit (by simpa using argsScratch)
  apply WP.mono (pinKey_ok s₁ (argRead s₁ (h₁.2.1.trans keep₀.rd) (h₁.2.2.1.trans keep₀.wr) sp₁))
  intro s₂ ⟨key₂, len₂, ptr₂, zero₂, keep₂⟩
  rw [args₁ 0 (by decide)] at key₂
  rw [args₁ 1 (by decide)] at len₂
  rw [args₁ 3 (by decide)] at ptr₂
  obtain scratchFrame : Frame [⟨addr32 (arg s 4), 512⟩] s.mem s₂.mem := by
    rw [keep₂.mem]; exact savedFrame
  obtain sp₂ : s₂.gpr .esp = s.gpr .esp := (keep₂.reg .esp (by decide)).trans sp₁
  obtain rd₂ : s₂.rd = s.rd := keep₂.rd.trans (h₁.2.1.trans keep₀.rd)
  obtain wr₂ : s₂.wr = s.wr := keep₂.wr.trans (h₁.2.2.1.trans keep₀.wr)
  obtain source₂ : Spec.Rc2.bytesAt s₂.mem (addr32 (s₂.gpr .ebp)) (arg s 1).toNat =
      Spec.Rc2.bytesAt s.mem (addr32 (arg s 0)) (arg s 1).toNat := by
    rw [key₂]
    exact bytesAt_frame scratchFrame (by simpa using keyScratch) (by omega_using [])
  obtain read₂ : ∀ i < (arg s 1).toNat,
      InRegions (s₂.rd ++ s₂.wr) (addr32 (s₂.gpr .ebp) + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [rd₂, wr₂, key₂, hrd, hwr]
    exact ⟨⟨addr32 (arg s 0), (arg s 1).toNat⟩, by simp,
      Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  obtain write₂ : ∀ i < 128, InRegions s₂.wr (addr32 (s₂.gpr .edi) + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [wr₂, ptr₂, hwr]
    exact ⟨⟨addr32 (arg s 3), 128⟩, by simp, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  obtain lanes₂ : InRegions s₂.wr (addr32 (s₂.gpr .edi)) 16 := by
    rw [wr₂, ptr₂, hwr]
    exact ⟨⟨addr32 (arg s 3), 128⟩, by simp, by simp [Region.Contains]⟩
  obtain length : (Spec.Rc2.bytesAt s.mem (addr32 (arg s 0)) (arg s 1).toNat).length = (arg s 1).toNat := by
    simp [Spec.Rc2.bytesAt]
  -- The copy of the key.
  apply WP.seq
  apply WP.mono (copyLoop_ok s₂ (arg s 1).toNat ht ht' (by rw [key₂]; exact keyFit) (by rw [ptr₂]; exact outFit)
    (by simpa using len₂) zero₂ read₂ write₂ (by rw [key₂, ptr₂]; exact keyOut))
  intro s₃ ⟨_, frame₃, prefix₃⟩
  rw [source₂, ptr₂] at prefix₃
  obtain sp₃ : s₃.gpr .esp = s.gpr .esp := (frame₃.reg .esp (by decide)).trans sp₂
  obtain outFrame₃ : Frame [⟨addr32 (arg s 3), 128⟩] s₂.mem s₃.mem := by
    have h := frame₃.mem
    rw [ptr₂] at h; exact h
  -- The table's address.
  apply WP.seq
  rw [tableBase]
  apply WP.mono (symFrame_ok piSym s₃ (by rw [sp₃]; exact spLo))
  intro s₄ h₄
  obtain stkFrame₄ : Frame [below (s.gpr .esp) 4] s₃.mem s₄.mem := by
    have h := h₄.frame
    rw [sp₃] at h; exact h
  apply WP.seq
  obtain ⟨s₅, run₅, base₅, count₅, keep₅⟩ := takeBase_ok s₄
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  have gpr₅ (r : Reg) (h₁ : r ≠ .eax) (h₂ : r ≠ .ecx) (h₃ : r ≠ .ebp) : s₅.gpr r = s₃.gpr r :=
    (keep₅.reg r (by simp [h₂, h₃])).trans (h₄.gpr r (by simp [h₁, h₂]))
  obtain ptr₅ : s₅.gpr .edi = arg s 3 :=
    (gpr₅ .edi (by decide) (by decide) (by decide)).trans ((frame₃.reg .edi (by decide)).trans ptr₂)
  obtain len₅ : s₅.gpr .esi = arg s 1 :=
    (gpr₅ .esi (by decide) (by decide) (by decide)).trans ((frame₃.reg .esi (by decide)).trans len₂)
  obtain sp₅ : s₅.gpr .esp = s.gpr .esp := (gpr₅ .esp (by decide) (by decide) (by decide)).trans sp₃
  obtain rd₅ : s₅.rd = s.rd := keep₅.rd.trans (h₄.rd.trans (frame₃.rd.trans rd₂))
  obtain wr₅ : s₅.wr = s.wr := keep₅.wr.trans (h₄.wr.trans (frame₃.wr.trans wr₂))
  obtain look₅ : LookPre s₅ := by
    refine ⟨?_, ?_⟩
    · rw [wr₅, ptr₅, hwr]
      exact ⟨⟨addr32 (arg s 3), 128⟩, by simp, by simp [Region.Contains]⟩
    · rw [base₅, h₄.addr, runBlock_syms run₅, h₄.syms]
  obtain write₅ : ∀ i < 128, InRegions s₅.wr (addr32 (s₅.gpr .edi) + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [wr₅, ptr₅, hwr]
    exact ⟨⟨addr32 (arg s 3), 128⟩, by simp, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  obtain prefix₅ : Proof.Rc2.BytesPrefix s₅.mem (addr32 (arg s 3))
      (Proof.Rc2.fill (Spec.Rc2.bytesAt s.mem (addr32 (arg s 0)) (arg s 1).toNat) 0) (arg s 1).toNat := by
    rw [keep₅.mem]
    exact prefix_frame prefix₃ ht' stkFrame₄ (by simpa using stkOut.symm)
  -- The fill, and the reduction.
  apply WP.seq
  apply VG.X86.WP.mono_syms (maybeFill_ok lookOk s₅ (Spec.Rc2.bytesAt s.mem (addr32 (arg s 0)) (arg s 1).toNat)
    (by rw [length]; exact ht) (by rw [length]; exact ht') (by rw [ptr₅]; exact outFit)
    (by rw [length, len₅]; simp) (by rw [length, count₅, h₄.gpr .esi (by decide), frame₃.reg .esi (by decide), len₂]; simp)
    write₅ look₅ (by rw [ptr₅, length]; exact prefix₅))
  intro s₆ ⟨_, frame₆, prefix₆⟩ sy₆
  rw [ptr₅, length] at prefix₆
  obtain ptr₆ : s₆.gpr .edi = arg s 3 := (frame₆.reg .edi (by decide)).trans ptr₅
  obtain sp₆ : s₆.gpr .esp = s.gpr .esp := (frame₆.reg .esp (by decide)).trans sp₅
  obtain outFrame₆ : Frame [⟨addr32 (arg s 3), 128⟩] s₅.mem s₆.mem := by
    have h := frame₆.mem
    rw [ptr₅] at h; exact h
  -- Memory from the entry: the saved registers, the schedule and the stack.
  obtain frame₆' : Frame [⟨addr32 (arg s 4), 512⟩, ⟨addr32 (arg s 3), 128⟩, below (s.gpr .esp) 4] s.mem s₆.mem := by
    refine (scratchFrame.mono (by simp)).trans ((outFrame₃.mono (by simp)).trans ((stkFrame₄.mono (by simp)).trans ?_))
    rw [← keep₅.mem]
    exact outFrame₆.mono (by simp)
  obtain args₆ := args_frame frame₆' sp₆ spFit (by simpa using ⟨argsScratch, argsOut, argsStk⟩)
  apply WP.seq
  apply WP.mono (expandReduce_ok lookOk s₆ _ (arg s 2).toNat hb hb' (by rw [ptr₆]; exact outFit)
    (argRead s₆ (frame₆.rd.trans rd₅) (frame₆.wr.trans wr₅) sp₆ 2 (by decide))
    (by simpa only [arg, argAddr, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_toNat, BitVec.setWidth_eq, addr32,
      BitVec.ofNat_eq_ofNat] using args₆ 2 (by decide))
    (by rw [frame₆.wr, frame₆.reg .edi (by decide)]; exact write₅)
    (lookOk.keep s₅ s₆ look₅ frame₆.wr (frame₆.reg .edi (by decide)) (frame₆.reg .ebp (by decide)) sy₆)
    (by rw [ptr₆]; exact prefix₆))
  intro s₇ h₇
  obtain core := h₇.1
  obtain outFrame₇ : Frame [⟨addr32 (arg s 3), 128⟩] s₆.mem s₇.mem := by
    have h := core.mem
    rw [ptr₆] at h; exact h
  obtain sp₇ : s₇.gpr .esp = s.gpr .esp := (core.reg .esp (by decide)).trans sp₆
  obtain rd₇ := core.rd.trans (frame₆.rd.trans rd₅)
  obtain wr₇ := core.wr.trans (frame₆.wr.trans wr₅)
  obtain expanded : Proof.Rc2.BytesPrefix s₇.mem (addr32 (arg s 3))
      (Spec.Rc2.expandBytes (Spec.Rc2.bytesAt s.mem (addr32 (arg s 0)) (arg s 1).toNat) (arg s 2).toNat) 128 := by
    have h := h₇.2
    rw [ptr₆] at h
    rw [Proof.Rc2.expandBytes_eq, length]; exact h
  rw [WP.block_append_iff]
  obtain frame₇ : Frame [⟨addr32 (arg s 4), 512⟩, ⟨addr32 (arg s 3), 128⟩, below (s.gpr .esp) 4] s.mem s₇.mem :=
    frame₆'.trans (outFrame₇.mono (by simp))
  obtain args₇ := args_frame frame₇ sp₇ spFit (by simpa using ⟨argsScratch, argsOut, argsStk⟩)
  obtain ⟨s₈, run₈, base₈, keep₈⟩ := loadArg_ok s₇ .eax 4 (argRead s₇ rd₇ wr₇ sp₇ 4 (by decide))
  refine WP.of_runBlock ⟨s₈, run₈, ?_⟩
  rw [args₇ 4 (by decide)] at base₈
  obtain rd₈ := keep₈.rd.trans rd₇
  obtain wr₈ := keep₈.wr.trans wr₇
  obtain scratchRead : ∀ i ∈ List.range 4,
      InRegions (s₈.rd ++ s₈.wr) (addr32 (s₈.gpr .eax) + BitVec.ofNat 64 (4 * i)) 4 := by
    intro i hi
    rw [rd₈, wr₈, base₈, hrd, hwr]
    obtain bound := List.mem_range.mp hi
    exact ⟨⟨addr32 (arg s 4), 512⟩, by simp, Offset.contains_base _ (by omega_using [bound]) (by omega_using [bound])⟩
  -- After the saves, only the schedule and the stack change.
  obtain later : Frame [⟨addr32 (arg s 3), 128⟩, below (s.gpr .esp) 4] s₂.mem s₇.mem := by
    refine (outFrame₃.mono (by simp)).trans ((stkFrame₄.mono (by simp)).trans ?_)
    rw [← keep₅.mem]
    exact (outFrame₆.mono (by simp)).trans (outFrame₇.mono (by simp))
  obtain stored : ∀ i ∈ List.range 4,
      s₈.mem.readW (addr32 (s₈.gpr .eax) + BitVec.ofNat 64 (4 * i)) 32 = s.gpr (savedReg i) := by
    intro i hi
    obtain bound := List.mem_range.mp hi
    rw [keep₈.mem, base₈, later.readW (r := ⟨addr32 (arg s 4), 512⟩)
      (Offset.contains_base _ (by omega_using [bound]) (by omega_using [bound]))
      (by simpa using ⟨outScratch.symm, stkScratch.symm⟩) (by decide),
      keep₂.mem, h₁.2.2.2, scratch₀]
    rw [saveMem_read _ _ _ 4 (by decide) i bound]
    exact gpr₀ _ (by
      obtain sep : ∀ i ∈ List.range 4, savedReg i ≠ .eax := by decide
      exact sep i hi)
  rw [keyRestore_eq]
  apply WP.mono (restoreCode_ok s₈ .eax savedReg (List.range 4) s.gpr (by rw [base₈]; omega_using [scratchFit])
    (by decide) (by decide) scratchRead stored)
  intro s₉ h₉
  constructor
  · constructor
    · intro r hr
      by_cases he : r = .esp
      · subst r
        exact (h₉.2.reg .esp (by decide)).trans ((keep₈.reg .esp (by decide)).trans sp₇)
      · exact h₉.1 r (by
          obtain covered : ∀ r ∈ calleeSaved, r ≠ .esp → r ∈ (List.range 4).map savedReg := by decide
          exact covered r hr he)
    · rw [h₉.2.mem, keep₈.mem]
      exact frame₇.readW (Region.contains_self _ _) (by simpa [addr32] using ⟨retScratch, retOut, retStk⟩) (by decide)
  · change Spec.Rc2.scheduleAt s₉.mem (addr32 (arg s 3)) = _
    rw [h₉.2.mem, keep₈.mem]
    exact Proof.Rc2.scheduleAt_expanded expanded

/-! ## Constant time -/

/-- Only `esp` and the arguments are public; the frame in which the function takes the table's address
is within the four bytes of stack it may use. -/
def keyTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [128, 512], argLen := 24, room := 4 }

theorem keyTaint_wf {s : State} (h : (keyContractS 4).pre s) : VG.X86.Taint.Wf keyTaint s := by
  obtain ⟨⟨_, wr, _, _, osc, ao, asc, ro, rsc, _, ofit, sfit, spfit, _⟩, spLo, so, ssc⟩ := h
  refine Taint.Wf.entryRoom rfl ⟨fun _ => ⟨?_, ?_, ?_⟩, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨spfit, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim⟩ fun _ => ⟨spLo, ?_⟩
  · rw [wr]
    exact .cons (Nat.le_refl _) (.cons (Nat.le_refl _) .nil)
  · simp only [wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq, List.Pairwise.nil,
      and_true]
    exact ⟨osc, fun _ h => h.elim⟩
  · simp only [wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · have := (arg s 3).isLt
      simp only [addr32, BitVec.toNat_setWidth]; omega_using [ofit, this]
    · have := (arg s 4).isLt
      simp only [addr32, BitVec.toNat_setWidth]; omega_using [sfit, this]
  · simp only [keyTaint, wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact Taint.frame_disjoint (n := 20) (by omega_using [spfit]) ro ao
    · exact Taint.frame_disjoint (n := 20) (by omega_using [spfit]) rsc asc
  · show ∀ r ∈ s.wr, Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 4, 4⟩ r
    rw [← Taint.sub_setWidth spLo, wr]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact so
    · exact ssc

theorem keyTaint_agree {s₁ s₂ : State} (h₁ : (keyContractS 4).pre s₁) (h₂ : (keyContractS 4).pre s₂)
    (hp : keyContract.pub s₁ s₂) : VG.X86.Taint.Agree keyTaint s₁ s₂ := by
  obtain ⟨sp, args⟩ := hp
  have fit : ∀ s, (keyContractS 4).pre s → (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 := by
    intro s hs; exact hs.1.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_,
    keyTaint_wf h₁, keyTaint_wf h₂, VG.X86.Taint.slotsOk_empty,
    VG.X86.Taint.slotsAgree_empty, fun _ => sp, fun k h4 hk => ?_⟩
  · simp only [keyTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r; exact sp
  · rw [h₁.1.2.1, h₂.1.2.1, args 3 (by decide), args 4 (by decide)]
  · simp only [keyTaint] at hk
    rw [show Taint.depth keyTaint.stk = 0 from rfl, Nat.zero_add]
    rw [Taint.argByte_eq (fit _ h₁) h4 hk, Taint.argByte_eq (fit _ h₂) h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)),
      Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (args ((k - 4) / 4) (by omega_using [hk]))

theorem expandKey_constantTime : ConstantTime isa (keyContractS 4).pre keyContract.pub Ssse3.expandKey := by
  exact VG.Taint.constantTime (A := VG.X86.sseTaint) keyTaint (fun _ _ h₁ h₂ hp => keyTaint_agree h₁ h₂ hp)
    (by taint_decide)

/-! ## The key expansion `init` calls -/

theorem key_nosp : NoSp Ssse3.expandKey := NoSp.of_all (by lit_decide)

theorem key_stack : stackUse Ssse3.expandKey = 4 := by lit_decide

/-- `vg_rc2_expand_key_ssse3`. -/
def key : KeyFn 4 where
  name := keyName
  code := Ssse3.expandKey
  correct := key_body_correct
  ct := expandKey_constantTime
  nosp := key_nosp
  stack := key_stack

end VG.Proof.Rc2.X86.Ssse3
