module

import VerifiedGarbage.Proof.Rc2.CbcMemory
import VerifiedGarbage.Proof.Rc2.X86.KeyIO
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Rc2.X86.Lit
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Proof.Rc2.X86.KeyIO
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.Rc2.X86.Lit
import VerifiedGarbage.Proof.Rc2.X86.RoundSteps
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Rc2.PairMem
public import VerifiedGarbage.Impl.Rc2.X86.Cbc
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Rc2.X86.Cbc.CallFrame
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.X86.SseTaint
public import VerifiedGarbage.Proof.Rc2.X86.BlockArgs
public import VerifiedGarbage.Spec.Rc2.Contract
public import VerifiedGarbage.Proof.Rc2.Contract
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Rc2.X86.BlockArgs
meta import VerifiedGarbage.Spec.Rc2.Contract
meta import VerifiedGarbage.Proof.Rc2.Contract
meta import VerifiedGarbage.Proof.Rc2.X86.RoundSteps
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Rc2.CbcMemory
meta import VerifiedGarbage.Proof.Rc2.PairMem
meta import VerifiedGarbage.Impl.Rc2.X86.Cbc
meta import VerifiedGarbage.Proof.Framework.X86.Call
meta import VerifiedGarbage.Proof.Rc2.X86.Cbc.CallFrame
meta import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Rc2.X86.Cbc.Contract`, which this module and modules that import it used -/

section

/-! ### `Rc2.X86.Cbc.Body`, which this module and modules that import it used -/

section

/-! ### `Rc2.X86.Block`, which only this module used -/

section

@[expose] public section

section

/-! # RC2 block correctness and the x86 calling convention -/

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.Impl.Rc2.X86

def blockSavedReg (i : Nat) : Reg := blockSaved.getD i .eax

theorem blockSave_eq : blockSave = saveCode .eax blockSavedReg 5 := rfl

theorem blockRestore_eq : blockRestore = restoreCode .eax blockSavedReg (List.range 5) := rfl

def cipher (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (b : Spec.Rc2.Block) : Spec.Rc2.Block :=
  match d with
  | .encrypt => Spec.Rc2.encryptBlock k b
  | .decrypt => Spec.Rc2.decryptBlock k b

def blockContract (d : Spec.Rc2.Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨addr32 (arg s 0), 128⟩
    let data : Region := ⟨addr32 (arg s 1), 8⟩
    let scratch : Region := ⟨addr32 (arg s 2), 256⟩
    let args : Region := ⟨argAddr s 0, 12⟩
    let ret : Region := ⟨addr32 (s.gpr .esp), 4⟩
    s.rd = [key, args] ∧ s.wr = [data, scratch] ∧ key.Disjoint scratch ∧ data.Disjoint scratch ∧
      args.Disjoint data ∧ args.Disjoint scratch ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
      (arg s 0).toNat + 128 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 8 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 256 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 16 ≤ 2 ^ 32
  post s s' := s'.gpr .ecx = s.gpr .ecx ∧ Spec.Rc2.blockAt s'.mem (addr32 (arg s 1)) =
    cipher d (Spec.Rc2.scheduleAt s.mem (addr32 (arg s 0))) (Spec.Rc2.blockAt s.mem (addr32 (arg s 1)))
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 3, arg s₁ i = arg s₂ i

theorem cipher_rounds (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (b : Spec.Rc2.Block) :
    cipher d k b = Spec.Rc2.encodeBlock
      ((List.range 16).foldl (fun v j => roundSpec d k j v) (Spec.Rc2.decodeBlock b)) := by
  cases d <;> rfl

theorem block_correct (d : Spec.Rc2.Direction) (s : State) (hs : (blockContract d).pre s) :
    WP isa (.block (blockCode d)) s (fun s' => abiPreserved s s' ∧ (blockContract d).post s s') := by
  obtain ⟨hrd, hwr, keySep, dataSep, argsData, argsScratch, retData, retScratch, keyFit, dataFit, scratchFit, spFit⟩ := hs
  have argRead (st : State) (rd : st.rd = s.rd) (wr : st.wr = s.wr)
      (sp : st.gpr .esp = s.gpr .esp) : ∀ i < 3, InRegions (st.rd ++ st.wr) (argAddr st i) 4 := by
    intro i hi
    obtain fit : (st.gpr .esp).toNat + 16 ≤ 2 ^ 32 := by rw [sp]; exact spFit
    rw [argAddr_eq st i (by omega_arith), sp, rd, wr, hrd, hwr]
    exact ⟨⟨argAddr s 0, 12⟩, by simp, argContainsCount s 3 spFit i hi⟩
  obtain writes : ∀ i < 5, InRegions s.wr (addr32 (arg s 2) + BitVec.ofNat 64 (4 * i)) 4 := by
    intro i hi
    rw [hwr]
    exact ⟨⟨addr32 (arg s 2), 256⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  simp only [blockCode, List.append_assoc]
  rw [WP.block_append_iff]
  obtain ⟨s₀, run₀, scratch₀, keep₀⟩ := loadArg_ok s .eax 2 (argRead s rfl rfl rfl 2 (by decide))
  refine WP.of_runBlock ⟨s₀, run₀, ?_⟩
  rw [WP.block_append_iff, blockSave_eq]
  apply WP.mono (saveCode_ok s₀ .eax blockSavedReg 5 (by decide)
    (by rw [scratch₀]; exact scratchFit) (by rw [keep₀.wr, scratch₀]; exact writes))
  intro s₁ h₁
  have gpr₀ (r : Reg) (hr : r ≠ .eax) : s₀.gpr r = s.gpr r := keep₀.reg r (by simpa using hr)
  obtain sp₁ : s₁.gpr .esp = s.gpr .esp := by rw [h₁.1]; exact gpr₀ .esp (by decide)
  obtain savedFrame : Frame [⟨addr32 (arg s 2), 256⟩] s.mem s₁.mem := by
    rw [h₁.2.2.2, keep₀.mem, scratch₀]
    exact saveMem_frame_le s.mem (addr32 (arg s 2)) (fun i => s₀.gpr (blockSavedReg i)) 5 64 (by decide) (by decide)
  obtain args₁ := arguments_frame 3 savedFrame sp₁ spFit (by simpa using argsScratch)
  rw [WP.block_append_iff]
  obtain ⟨s₂, run₂, scratch₂, data₂, keep₂⟩ := pinBlock_ok s₁
    (argRead s₁ (h₁.2.1.trans keep₀.rd) (h₁.2.2.1.trans keep₀.wr) sp₁ 1 (by decide))
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  rw [h₁.1, scratch₀] at scratch₂
  rw [args₁ 1 (by decide)] at data₂
  obtain sp₂ : s₂.gpr .esp = s.gpr .esp := (keep₂.reg .esp (by decide)).trans sp₁
  obtain rd₂ := keep₂.rd.trans (h₁.2.1.trans keep₀.rd)
  obtain wr₂ := keep₂.wr.trans (h₁.2.2.1.trans keep₀.wr)
  obtain frame₂ : Frame [⟨addr32 (arg s 2), 256⟩] s.mem s₂.mem := by rw [keep₂.mem]; exact savedFrame
  obtain args₂ := arguments_frame 3 frame₂ sp₂ spFit (by simpa using argsScratch)
  obtain base₂ : wordBase s₂ = addr32 (arg s 2) + 64 := by unfold wordBase; rw [scratch₂]
  obtain wordsSub : Region.Sub ⟨wordBase s₂, 16⟩ ⟨addr32 (arg s 2), 256⟩ := by
    rw [base₂]; exact Offset.sub_base (addr32 (arg s 2)) (d := 64) (n := 16) (k := 256) (by decide)
  obtain area₂ : areaBase s₂ = addr32 (arg s 2) + BitVec.ofNat 64 48 := by unfold areaBase; rw [scratch₂]
  obtain areaSub : Region.Sub ⟨areaBase s₂, 32⟩ ⟨addr32 (arg s 2), 256⟩ := by
    rw [area₂]; exact Offset.sub_base (addr32 (arg s 2)) (d := 48) (n := 32) (k := 256) (by decide)
  obtain dataWords : (Region.mk (addr32 (arg s 1)) 8).Disjoint ⟨wordBase s₂, 16⟩ := by
    intro a ha hb; exact dataSep a ha (wordsSub a hb)
  obtain env₂ : RoundEnv s₂ := by
    constructor
    · rw [scratch₂]; exact scratchFit
    · rw [args₂ 0 (by decide)]; exact keyFit
    · exact argRead s₂ rd₂ wr₂ sp₂ 0 (by decide)
    · intro i hi
      rw [args₂ 0 (by decide), rd₂, wr₂, hrd, hwr]
      exact ⟨⟨addr32 (arg s 0), 128⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    · rw [args₂ 0 (by decide), rd₂, wr₂, hrd, hwr]
      exact ⟨⟨addr32 (arg s 0), 128⟩, by simp, Region.contains_self _ _⟩
    · intro i hi
      rw [wr₂, hwr, base₂, BitVec.add_assoc, show (64 : Addr) = BitVec.ofNat 64 64 from rfl, ← BitVec.ofNat_add]
      exact ⟨⟨addr32 (arg s 2), 256⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    · rw [wr₂, hwr, area₂]
      exact ⟨⟨addr32 (arg s 2), 256⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    · rw [args₂ 0 (by decide)]
      intro a ha hb; exact keySep a ha (areaSub a hb)
    · have ae : argAddr s₂ 0 = argAddr s 0 := by unfold argAddr; rw [sp₂]
      rw [ae]
      intro a ha hb
      exact argsScratch a (Region.sub_prefix (by decide : 4 ≤ 12) a ha) (areaSub a hb)
  obtain input₂ : Spec.Rc2.blockAt s₂.mem (addr32 (s₂.gpr .edi)) = Spec.Rc2.blockAt s.mem (addr32 (arg s 1)) := by
    rw [data₂]; exact blockAt_frame frame₂ _ (by simpa using dataSep)
  obtain schedule₂ : Spec.Rc2.scheduleAt s₂.mem (addr32 (arg s₂ 0)) = Spec.Rc2.scheduleAt s.mem (addr32 (arg s 0)) := by
    rw [args₂ 0 (by decide)]; exact scheduleAt_frame frame₂ _ (by simpa using keySep)
  obtain dataRead₂ : ∀ i < 8, InRegions (s₂.rd ++ s₂.wr) (addr32 (s₂.gpr .edi) + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [rd₂, wr₂, data₂, hrd, hwr]
    exact ⟨⟨addr32 (arg s 1), 8⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  rw [WP.block_append_iff]
  apply WP.mono (blockLoad_ok s₂ (by rw [data₂]; exact dataFit) env₂.scratchFit dataRead₂ env₂.wordWrite
    (by rw [data₂]; exact dataWords))
  intro s₃ h₃
  rw [WP.block_append_iff]
  apply WP.mono (rounds_ok d s₃ _ h₃.1 (h₃.2.env env₂))
  intro s₄ h₄
  obtain core := h₃.2.trans h₄.2
  obtain env₄ := core.env env₂
  obtain sp₄ : s₄.gpr .esp = s.gpr .esp := (core.reg .esp (by decide)).trans sp₂
  obtain scratch₄ : s₄.gpr .ebp = arg s 2 := (core.reg .ebp (by decide)).trans scratch₂
  obtain rd₄ := core.rd.trans rd₂
  obtain wr₄ := core.wr.trans wr₂
  obtain frame₄ : Frame [⟨addr32 (arg s 2), 256⟩] s.mem s₄.mem :=
    frame₂.trans (core.mem.sub (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      exact ⟨_, List.mem_cons_self, areaSub⟩))
  obtain args₄ := arguments_frame 3 frame₄ sp₄ spFit (by simpa using argsScratch)
  let v := (List.range 16).foldl (fun v j => roundSpec d
    (Spec.Rc2.scheduleAt s.mem (addr32 (arg s 0))) j v) (Spec.Rc2.decodeBlock (Spec.Rc2.blockAt s.mem (addr32 (arg s 1))))
  obtain words₄ : MemWords s₄.mem (wordBase s₄) v := by
    have h := h₄.1
    rw [h₃.2.schedule env₂, schedule₂, input₂] at h
    exact h
  rw [WP.block_append_iff]
  obtain ⟨s₅, run₅, data₅, keep₅⟩ := loadArg_ok s₄ .edi 1 (argRead s₄ rd₄ wr₄ sp₄ 1 (by decide))
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  rw [args₄ 1 (by decide)] at data₅
  obtain base₅ : wordBase s₅ = wordBase s₄ := by unfold wordBase; rw [keep₅.reg .ebp (by decide)]
  obtain writable₅ : ∀ i < 8, InRegions s₅.wr (addr32 (s₅.gpr .edi) + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [keep₅.wr, wr₄, data₅, hwr]
    exact ⟨⟨addr32 (arg s 1), 8⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  rw [WP.block_append_iff]
  apply WP.mono (blockStore_ok s₅ v (by rw [keep₅.mem, base₅]; exact words₄)
    (by rw [data₅]; exact dataFit) (by rw [keep₅.reg .ebp (by decide)]; exact env₄.scratchFit)
    (by rw [keep₅.rd, keep₅.wr, base₅]; exact env₄.wordRead)
    (by rw [base₅, core.base, data₅]; exact dataWords.symm) writable₅)
  intro s₆ h₆
  obtain mem₆ : s₆.mem = s₄.mem.writeW (addr32 (arg s 1)) (pack v) := by rw [h₆.mem, keep₅.mem, data₅]
  obtain scratch₆ : s₆.gpr .ebp = arg s 2 := (h₆.reg .ebp (by decide)).trans ((keep₅.reg .ebp (by decide)).trans scratch₄)
  obtain sp₆ : s₆.gpr .esp = s.gpr .esp := (h₆.reg .esp (by decide)).trans ((keep₅.reg .esp (by decide)).trans sp₄)
  obtain rd₆ := h₆.rd.trans (keep₅.rd.trans rd₄)
  obtain wr₆ := h₆.wr.trans (keep₅.wr.trans wr₄)
  rw [WP.block_append_iff]
  obtain ⟨s₇, run₇, base₇, keep₇⟩ := blockScratchBase_ok s₆
  refine WP.of_runBlock ⟨s₇, run₇, ?_⟩
  rw [scratch₆] at base₇
  obtain reads₇ : ∀ i ∈ List.range 5, InRegions (s₇.rd ++ s₇.wr) (addr32 (s₇.gpr .eax) + BitVec.ofNat 64 (4 * i)) 4 := by
    intro i hi
    rw [keep₇.rd, keep₇.wr, rd₆, wr₆, base₇, hrd, hwr]
    obtain bound := List.mem_range.mp hi
    exact ⟨⟨addr32 (arg s 2), 256⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  obtain stored₇ : ∀ i ∈ List.range 5, s₇.mem.readW (addr32 (s₇.gpr .eax) + BitVec.ofNat 64 (4 * i)) 32 = s.gpr (blockSavedReg i) := by
    intro i hi
    obtain bound := List.mem_range.mp hi
    rw [keep₇.mem, mem₆, base₇, Mem.readW_writeW_sep
      (dataSep.symm.sep (Offset.contains_base _ (by omega_arith) (by omega_arith)) (Region.contains_self _ _)) (by decide)]
    obtain sep : (Region.mk (addr32 (arg s 2)) 20).Disjoint ⟨areaBase s₂, 32⟩ := by
      rw [area₂]; exact (Offset.disjoint_base (addr32 (arg s 2)) (d := 48) (n := 32) (k := 20) (by decide) (by decide)).symm
    rw [core.mem.readW (r := ⟨addr32 (arg s 2), 20⟩)
      (Offset.contains_base _ (by omega_arith) (by omega_arith)) (by simpa using sep) (by decide),
      keep₂.mem, h₁.2.2.2, scratch₀, saveMem_read _ _ _ 5 (by decide) i bound]
    exact gpr₀ _ (by
      obtain fact : ∀ i ∈ List.range 5, blockSavedReg i ≠ .eax := by decide
      exact fact i hi)
  rw [blockRestore_eq]
  apply WP.mono (restoreCode_ok s₇ .eax blockSavedReg (List.range 5) s.gpr
    (by rw [base₇]; exact scratchFit) (by decide) (by decide) reads₇ stored₇)
  intro s₈ h₈
  constructor
  · constructor
    · intro r hr
      by_cases he : r = .esp
      · subst r
        exact (h₈.2.reg .esp (by decide)).trans ((keep₇.reg .esp (by decide)).trans sp₆)
      · exact h₈.1 r (by
          obtain fact : ∀ r ∈ calleeSaved, r ≠ .esp → r ∈ (List.range 5).map blockSavedReg := by decide
          exact fact r hr he)
    · rw [h₈.2.mem, keep₇.mem, mem₆, Mem.readW_writeW_sep
        (retData.sep (Region.contains_self _ _) (Region.contains_self _ _)) (by decide)]
      exact frame₄.readW (Region.contains_self _ _) (by simpa [addr32] using retScratch) (by decide)
  · refine ⟨h₈.1 .ecx (by decide), ?_⟩
    change Spec.Rc2.blockAt s₈.mem (addr32 (arg s 1)) = _
    rw [h₈.2.mem, keep₇.mem, mem₆, blockAt_write64, cipher_rounds]

end VG.Proof.Rc2.X86

end

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.Impl.Rc2.X86

def blockTaint : VG.X86.Taint.T := { regs := .ofList [.esp], flags := false, argLen := 16 }

theorem blockTaint_wf {d : Spec.Rc2.Direction} {s : State} (h : (blockContract d).pre s) : VG.X86.Taint.Wf blockTaint s := by
  obtain ⟨_, wr, _, _, ao, asc, ro, rsc, _, _, _, spfit⟩ := h
  refine Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨spfit, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim⟩
  simp only [blockTaint, wr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact Taint.frame_disjoint (n := 12) (by omega_arith) ro ao
  · exact Taint.frame_disjoint (n := 12) (by omega_arith) rsc asc

theorem blockTaint_agree {d : Spec.Rc2.Direction} {s₁ s₂ : State} (h₁ : (blockContract d).pre s₁) (h₂ : (blockContract d).pre s₂)
    (hp : (blockContract d).pub s₁ s₂) : VG.X86.Taint.Agree blockTaint s₁ s₂ := by
  obtain ⟨sp, args⟩ := hp
  obtain fit : ∀ s, (blockContract d).pre s → (s.gpr .esp).toNat + 16 ≤ 2 ^ 32 := by
    intro s hs; exact hs.2.2.2.2.2.2.2.2.2.2.2
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h,
    blockTaint_wf h₁, blockTaint_wf h₂, VG.X86.Taint.slotsOk_empty,
    VG.X86.Taint.slotsAgree_empty, fun _ => sp, fun k h4 hk => ?_⟩
  · simp only [blockTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r; exact sp
  · simp only [blockTaint] at hk
    rw [show Taint.depth blockTaint.stk = 0 from rfl, Nat.zero_add]
    rw [Taint.argByte_eq (fit _ h₁) h4 hk, Taint.argByte_eq (fit _ h₂) h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)),
      Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (args ((k - 4) / 4) (by omega_arith))

theorem encryptBlock_constantTime : ConstantTime isa (blockContract .encrypt).pre (blockContract .encrypt).pub encryptBlock := by
  exact VG.Taint.constantTime (A := VG.X86.sseTaint) blockTaint (fun _ _ h₁ h₂ hp => blockTaint_agree h₁ h₂ hp)
    (by taint_decide)

theorem decryptBlock_constantTime : ConstantTime isa (blockContract .decrypt).pre (blockContract .decrypt).pub decryptBlock := by
  exact VG.Taint.constantTime (A := VG.X86.sseTaint) blockTaint (fun _ _ h₁ h₂ hp => blockTaint_agree h₁ h₂ hp)
    (by taint_decide)

end VG.Proof.Rc2.X86

end

end

@[expose] public section

section

section

namespace VG.Proof.Rc2.X86.Cbc

open VG VG.X86 VG.Impl.Rc2.X86

def kept : List Reg := [.ebx, .ecx, .esi, .edi, .ebp, .esp]

theorem block_nosp (d : Spec.Rc2.Direction) : NoSp (.block (blockCode d)) := by
  apply NoSp.of_all
  cases d
  · change encryptBlock.allInstrs _ = true
    lit_decide
  · change decryptBlock.allInstrs _ = true
    lit_decide

theorem blockCall_eq (d : Spec.Rc2.Direction) : Impl.Rc2.X86.Cbc.blockCall d =
    .frame (.push [.ebp, .esi, .ebx])
      (.call (match d with | .encrypt => "vg_rc2_encrypt_block" | .decrypt => "vg_rc2_decrypt_block")
        (.block (blockCode d))) (.pop .eax 3) := by cases d <;> rfl

structure CallPre (s : State) : Prop where
  reads : Covers [⟨addr32 (s.gpr .ebx), 128⟩, ⟨addr32 (s.gpr .esi), 8⟩, ⟨addr32 (s.gpr .ebp), 256⟩] (s.rd ++ s.wr)
  writes : Covers [⟨addr32 (s.gpr .esi), 8⟩, ⟨addr32 (s.gpr .ebp), 256⟩] s.wr
  keyScratch : (Region.mk (addr32 (s.gpr .ebx)) 128).Disjoint ⟨addr32 (s.gpr .ebp), 256⟩
  dataScratch : (Region.mk (addr32 (s.gpr .esi)) 8).Disjoint ⟨addr32 (s.gpr .ebp), 256⟩
  keyFit : (s.gpr .ebx).toNat + 128 ≤ 2 ^ 32
  dataFit : (s.gpr .esi).toNat + 8 ≤ 2 ^ 32
  bufFit : (s.gpr .ebp).toNat + 256 ≤ 2 ^ 32
  stackLo : 16 ≤ (s.gpr .esp).toNat
  stackKey : (below (s.gpr .esp) 16).Disjoint ⟨addr32 (s.gpr .ebx), 128⟩
  stackData : (below (s.gpr .esp) 16).Disjoint ⟨addr32 (s.gpr .esi), 8⟩
  stackBuf : (below (s.gpr .esp) 16).Disjoint ⟨addr32 (s.gpr .ebp), 256⟩

structure CallPost (d : Spec.Rc2.Direction) (s s' : State) : Prop where
  reg : ∀ r ∈ kept, s'.gpr r = s.gpr r
  callee : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame [⟨addr32 (s.gpr .esi), 8⟩, ⟨addr32 (s.gpr .ebp), 256⟩, below (s.gpr .esp) 16] s.mem s'.mem
  output : Spec.Rc2.blockAt s'.mem (addr32 (s.gpr .esi)) =
    cipher d (Spec.Rc2.scheduleAt s.mem (addr32 (s.gpr .ebx))) (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .esi)))

theorem call_ok (d : Spec.Rc2.Direction) (s : State) (hp : CallPre s) :
    WP isa (Impl.Rc2.X86.Cbc.blockCall d) s (CallPost d s) := by
  rw [blockCall_eq]
  let rs : List Reg := [.ebp, .esi, .ebx]
  obtain hrs : .esp ∉ rs := by decide
  have fit : 4 * rs.length + 4 ≤ (s.gpr .esp).toNat := hp.stackLo
  let sE := (pushed rs s).callEntry
  obtain a0 : arg sE 0 = s.gpr .ebx := by rw [callEntry_arg fit hrs (by decide)]; rfl
  obtain a1 : arg sE 1 = s.gpr .esi := by rw [callEntry_arg fit hrs (by decide)]; rfl
  obtain a2 : arg sE 2 = s.gpr .ebp := by rw [callEntry_arg fit hrs (by decide)]; rfl
  obtain eA : argAddr sE 0 = ((s.gpr .esp) - BitVec.ofNat 32 12).setWidth 64 := by rw [callEntry_argAddr0]; rfl
  obtain eSp : sE.gpr .esp = s.gpr .esp - BitVec.ofNat 32 16 := by rw [callEntry_esp']; rfl
  obtain b12 : Region.Sub (below (s.gpr .esp) 12) (below (s.gpr .esp) 16) := below_sub (by decide) hp.stackLo
  obtain r4 : Region.Sub ⟨((s.gpr .esp) - BitVec.ofNat 32 16).setWidth 64, 4⟩ (below (s.gpr .esp) 16) :=
    Region.sub_prefix (by decide)
  refine callWithGpr (k := blockContract d) (block_correct d) (block_nosp d) (by decide) hrs
    hp.stackLo (rd := [⟨addr32 (s.gpr .ebx), 128⟩, ⟨argAddr sE 0, 12⟩])
    (wr := [⟨addr32 (s.gpr .esi), 8⟩, ⟨addr32 (s.gpr .ebp), 256⟩]) ⟨?_, ?_, ?_⟩ ?_
  · change (blockContract d).pre (sE.withRegions _ _)
    simp only [blockContract, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, eA, eSp]
    refine ⟨trivial, trivial, hp.keyScratch, hp.dataScratch, hp.stackData.sub_left b12,
      hp.stackBuf.sub_left b12, hp.stackData.sub_left r4, hp.stackBuf.sub_left r4,
      hp.keyFit, hp.dataFit, hp.bufFit, ?_⟩
    rw [sub_toNat hp.stackLo]
    have := (s.gpr .esp).isLt
    omega_using []
  · intro a n ⟨r, hr, hc⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact InRegions_append_cons.mpr (.inr (hp.reads a n ⟨_, by simp, hc⟩))
    · apply InRegions_append_cons.mpr
      left
      rw [eA] at hc
      exact hc
    · exact InRegions_append_cons.mpr (.inr (hp.reads a n ⟨_, by simp, hc⟩))
    · exact InRegions_append_cons.mpr (.inr (hp.reads a n ⟨_, by simp, hc⟩))
  · intro a n h
    obtain ⟨r, hr, hc⟩ := hp.writes a n h
    exact ⟨r, List.mem_cons_of_mem _ hr, hc⟩
  · intro s' rd wr cs frame ⟨s₂, mem₂, gpr₂, post⟩
    change (blockContract d).post (sE.withRegions _ _) s₂ at post
    simp only [blockContract, State.withRegions_gpr, State.withRegions_mem, arg_withRegions,
      a0, a1] at post
    obtain stackFrame := callEntry_frame fit hrs
    change Frame [below (s.gpr .esp) 16] s.mem sE.mem at stackFrame
    obtain m16 : Frame [below (s.gpr .esp) 16] s₂.mem s'.mem :=
      Frame.below_mono (wr := []) mem₂ (by decide) hp.stackLo
    refine ⟨?_, cs, rd, wr, frame, ?_⟩
    · intro r hr
      by_cases he : r = .ecx
      · subst r
        obtain memGpr : s₂.gpr .ecx = s'.gpr .ecx := gpr₂ .ecx (by decide) (by decide)
        rw [← memGpr, post.1]
        exact (State.callEntry_gpr _ (by decide)).trans (pushed_gpr rs s (by decide))
      · have fact : ∀ r ∈ kept, r ≠ .ecx → r ∈ calleeSaved := by decide
        exact cs r (fact r hr he)
    · rw [blockAt_frame m16 _ (by simpa using hp.stackData.symm), post.2,
        scheduleAt_frame stackFrame _ (by simpa using hp.stackKey.symm),
        blockAt_frame stackFrame _ (by simpa using hp.stackData.symm)]

end VG.Proof.Rc2.X86.Cbc

end

section

section

/-! # Pair loads and stores for 64-bit CBC blocks -/

namespace VG.Proof.Rc2.X86.Cbc

open VG VG.X86 VG.X86.RegUpd VG.Impl.Rc2.X86 VG.Proof.Rc2.Word32

theorem halves {rs : List Region} {p : Addr} (h : InRegions rs p 8) :
    InRegions rs p 4 ∧ InRegions rs (p + BitVec.ofNat 64 4) 4 := by
  obtain ⟨r, hr, hc⟩ := h
  constructor
  · exact ⟨r, hr, by unfold Region.Contains at hc ⊢; omega_using [hc]⟩
  · refine ⟨r, hr, ?_⟩
    unfold Region.Contains at hc ⊢
    rw [BitVec.add_sub_comm, BitVec.toNat_add]
    obtain bound := Nat.mod_le ((p - r.base).toNat + (BitVec.ofNat 64 4).toNat) (2 ^ 64)
    change ((p - r.base).toNat + 4) % 2 ^ 64 + 4 ≤ r.len
    change ((p - r.base).toNat + 4) % 2 ^ 64 ≤ (p - r.base).toNat + 4 at bound
    omega_using [hc]

theorem loadPair_ok (s : State) (lo hi src : Reg) (a : Nat)
    (different : lo ≠ hi) (sep : src ≠ lo)
    (fit : (s.gpr src).toNat + a + 8 ≤ 2 ^ 32)
    (readable : InRegions (s.rd ++ s.wr) (addr32 (s.gpr src) + BitVec.ofNat 64 a) 8) :
    ∃ s', runBlock isa [.mov lo (.mem (memOp src a)), .mov hi (.mem (memOp src (a + 4)))] s = some s' ∧
      s'.gpr lo = s.mem.readW (addr32 (s.gpr src) + BitVec.ofNat 64 a) 32 ∧
      s'.gpr hi = s.mem.readW (addr32 (s.gpr src) + BitVec.ofNat 64 (a + 4)) 32 ∧
      Keep [lo, hi] s s' := by
  obtain ⟨rd0, rd4⟩ := halves readable
  rw [BitVec.add_assoc, ← BitVec.ofNat_add] at rd4
  rw [runBlock_cons, exec_load s lo src a (by omega_using [fit]) rd0, runStep_some]
  obtain rd4' : InRegions ((s.setReg lo (s.mem.readW (addr32 (s.gpr src) + BitVec.ofNat 64 a) 32)).rd ++
      (s.setReg lo (s.mem.readW (addr32 (s.gpr src) + BitVec.ofNat 64 a) 32)).wr)
      (addr32 ((s.setReg lo (s.mem.readW (addr32 (s.gpr src) + BitVec.ofNat 64 a) 32)).gpr src) +
        BitVec.ofNat 64 (a + 4)) 4 := by
    simpa only [rd_setReg, wr_setReg, gpr_setReg_of_ne _ _ sep] using rd4
  rw [runBlock_cons, exec_load _ hi src (a + 4)
    (by rw [gpr_setReg_of_ne _ _ sep]; omega_using [fit]) rd4', runStep_some, runBlock_nil]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · rw [gpr_setReg_of_ne _ _ different, gpr_setReg_self]
  · rw [gpr_setReg_self, gpr_setReg_of_ne _ _ sep, mem_setReg]
  · refine ⟨?_, rfl, rfl, rfl⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [gpr_setReg_of_ne _ _ hr.2, gpr_setReg_of_ne _ _ hr.1]

theorem storePair_ok (s : State) (lo hi dst : Reg) (b : Nat)
    (fit : (s.gpr dst).toNat + b + 8 ≤ 2 ^ 32)
    (writable : InRegions s.wr (addr32 (s.gpr dst) + BitVec.ofNat 64 b) 8) :
    ∃ s', runBlock isa [.store (memOp dst b) lo, .store (memOp dst (b + 4)) hi] s = some s' ∧
      Keep [] {s with
        mem := s.mem.writeW (addr32 (s.gpr dst) + BitVec.ofNat 64 b)
          (s.gpr hi ++ s.gpr lo)} s' := by
  obtain ⟨wr0, wr4⟩ := halves writable
  rw [BitVec.add_assoc, ← BitVec.ofNat_add] at wr4
  rw [runBlock_cons, exec_store s lo dst b (by omega_using [fit]) wr0, runStep_some,
    runBlock_cons, exec_store {s with mem := s.mem.writeW (addr32 (s.gpr dst) + BitVec.ofNat 64 b) (s.gpr lo)} hi dst (b + 4) (by change (s.gpr dst).toNat + (b + 4) < 2 ^ 32; omega_using [fit]) wr4,
    runStep_some, runBlock_nil]
  refine ⟨_, rfl, fun _ _ => rfl, ?_, rfl, rfl⟩
  rw [write64_pair, BitVec.add_assoc, ← BitVec.ofNat_add]

end VG.Proof.Rc2.X86.Cbc

end

/-! # CBC loads, XORs, stores, and public loop counters -/

namespace VG.Proof.Rc2.X86.Cbc

open VG VG.X86 VG.X86.RegUpd VG.Impl.Rc2.X86 VG.Proof.Rc2.Word32

def temps : List Reg := [.eax, .edx]

theorem copy64_ok (s : State) (src dst : Reg) (a b : Nat)
    (srcSep : src ≠ .eax) (dstSep : dst ≠ .eax ∧ dst ≠ .edx)
    (srcFit : (s.gpr src).toNat + a + 8 ≤ 2 ^ 32)
    (dstFit : (s.gpr dst).toNat + b + 8 ≤ 2 ^ 32)
    (readable : InRegions (s.rd ++ s.wr) (addr32 (s.gpr src) + BitVec.ofNat 64 a) 8)
    (writable : InRegions s.wr (addr32 (s.gpr dst) + BitVec.ofNat 64 b) 8) :
    WP isa (.block (Impl.Rc2.X86.Cbc.copy64 src dst a b)) s (fun s' =>
      Keep temps {s with
        mem := s.mem.writeW (addr32 (s.gpr dst) + BitVec.ofNat 64 b)
          (s.mem.readW (addr32 (s.gpr src) + BitVec.ofNat 64 a) 64)} s') := by
  change WP isa (.block (([.mov .eax (.mem (memOp src a)), .mov .edx (.mem (memOp src (a + 4)))] : List Instr) ++
    [.store (memOp dst b) .eax, .store (memOp dst (b + 4)) .edx])) s _
  rw [WP.block_append_iff]
  obtain ⟨s₁, run₁, lo₁, hi₁, keep₁⟩ := loadPair_ok s .eax .edx src a (by decide) srcSep srcFit readable
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ptr := keep₁.reg dst (by simpa only [List.mem_cons, List.not_mem_nil, or_false, not_or] using dstSep)
  obtain ⟨s₂, run₂, keep₂⟩ := storePair_ok s₁ .eax .edx dst b
    (by rw [ptr]; exact dstFit) (by rw [keep₁.wr, ptr]; exact writable)
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  constructor
  · intro r hr
    exact (keep₂.reg r (by simp)).trans (keep₁.reg r hr)
  · rw [keep₂.mem, ptr, hi₁, lo₁, keep₁.mem, ← Offset.add_ofNat_add_ofNat, ← read64_pair]
  · exact keep₂.rd.trans keep₁.rd
  · exact keep₂.wr.trans keep₁.wr

theorem exec_xorMem (s : State) (t n : Reg) (off : Nat)
    (fit : (s.gpr n).toNat + off < 2 ^ 32)
    (h : InRegions (s.rd ++ s.wr) (addr32 (s.gpr n) + BitVec.ofNat 64 off) 4) :
    exec (.alu .xor t (.mem (memOp n off))) s =
      some ((arithFlags s (s.gpr t ^^^ s.mem.readW (addr32 (s.gpr n) + BitVec.ofNat 64 off) 32) false false).setReg t
          (s.gpr t ^^^ s.mem.readW (addr32 (s.gpr n) + BitVec.ofNat 64 off) 32)) := by
  simp only [exec, execAlu, readSrc, memOp, State.ea]
  rw [← addr32, addr_add fit]
  simp only [State.load32, h, ite_true, Option.bind_some]

theorem xorPair_ok (s : State) (iv : Reg) (ivSep : iv ≠ .eax ∧ iv ≠ .edx)
    (fit : (s.gpr iv).toNat + 8 ≤ 2 ^ 32)
    (rd : InRegions (s.rd ++ s.wr) (addr32 (s.gpr iv)) 8) :
    ∃ s', runBlock isa [.alu .xor .eax (.mem (memOp iv 0)), .alu .xor .edx (.mem (memOp iv 4))] s = some s' ∧
      s'.gpr .eax = s.gpr .eax ^^^ s.mem.readW (addr32 (s.gpr iv)) 32 ∧
      s'.gpr .edx = s.gpr .edx ^^^ s.mem.readW (addr32 (s.gpr iv) + BitVec.ofNat 64 4) 32 ∧
      Keep temps s s' := by
  obtain ⟨rd0, rd4⟩ := halves rd
  rw [runBlock_cons, exec_xorMem s .eax iv 0 (by omega_using []) (by simpa only [BitVec.add_zero] using rd0), runStep_some]
  rw [runBlock_cons, exec_xorMem _ .edx iv 4
    (by simp only [gpr_setReg, gpr_arithFlags, ivSep.1, ite_false]; omega_using [fit])
    (by simpa only [rd_setReg, wr_setReg, rd_arithFlags, wr_arithFlags, gpr_setReg, gpr_arithFlags, ivSep.1, ite_false] using rd4),
    runStep_some, runBlock_nil]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true, BitVec.add_zero]
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true, ivSep.1, mem_setReg, mem_arithFlags]
  · refine ⟨?_, rfl, rfl, rfl⟩
    intro r hr
    simp only [temps, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, gpr_arithFlags, hr.1, hr.2, ite_false]

theorem xor64_ok (s : State) (dst iv : Reg)
    (dstSep : dst ∉ temps) (ivSep : iv ∉ temps)
    (dstFit : (s.gpr dst).toNat + 8 ≤ 2 ^ 32) (ivFit : (s.gpr iv).toNat + 8 ≤ 2 ^ 32)
    (readDst : InRegions (s.rd ++ s.wr) (addr32 (s.gpr dst)) 8)
    (readIv : InRegions (s.rd ++ s.wr) (addr32 (s.gpr iv)) 8)
    (writable : InRegions s.wr (addr32 (s.gpr dst)) 8) :
    WP isa (.block (Impl.Rc2.X86.Cbc.xor64 dst iv)) s (fun s' =>
      Keep temps {s with mem := (s.mem.writeW (addr32 (s.gpr dst))
        (s.mem.readW (addr32 (s.gpr dst)) 64 ^^^ s.mem.readW (addr32 (s.gpr iv)) 64))} s') := by
  obtain ds : dst ≠ .eax ∧ dst ≠ .edx := by simpa only [temps, List.mem_cons, List.not_mem_nil, or_false, not_or] using dstSep
  obtain vs : iv ≠ .eax ∧ iv ≠ .edx := by simpa only [temps, List.mem_cons, List.not_mem_nil, or_false, not_or] using ivSep
  change WP isa (.block (([.mov .eax (.mem (memOp dst 0)), .mov .edx (.mem (memOp dst 4))] : List Instr) ++
    (([.alu .xor .eax (.mem (memOp iv 0)), .alu .xor .edx (.mem (memOp iv 4))] : List Instr) ++
      [.store (memOp dst 0) .eax, .store (memOp dst 4) .edx]))) s _
  rw [WP.block_append_iff]
  obtain ⟨s₁, run₁, lo₁, hi₁, keep₁⟩ := loadPair_ok s .eax .edx dst 0 (by decide) ds.1
    (by simpa using dstFit) (by simpa using readDst)
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain iv₁ := keep₁.reg iv ivSep
  rw [WP.block_append_iff]
  obtain ⟨s₂, run₂, lo₂, hi₂, keep₂⟩ := xorPair_ok s₁ iv vs
    (by rw [iv₁]; exact ivFit) (by rw [keep₁.rd, keep₁.wr, iv₁]; exact readIv)
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  obtain keep : Keep temps s s₂ := keep₁.trans keep₂
  obtain ptr := keep.reg dst dstSep
  obtain ⟨s₃, run₃, keep₃⟩ := storePair_ok s₂ .eax .edx dst 0
    (by rw [ptr]; simpa using dstFit) (by rw [keep.wr, ptr]; simpa using writable)
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  refine ⟨fun r hr => (keep₃.reg r (by simp)).trans (keep.reg r hr), ?_, keep₃.rd.trans keep.rd, keep₃.wr.trans keep.wr⟩
  rw [keep₃.mem, keep.mem, ptr, BitVec.add_zero, hi₂, lo₂, hi₁, lo₁, keep₁.mem, iv₁]
  simp only [Nat.zero_add, BitVec.add_zero]
  rw [pair_xor, ← read64_pair, ← read64_pair]

def zeroCount (s : State) : Option Bool := s.zf

theorem eval_zeroCount (s : State) : eval .e s = zeroCount s := rfl

theorem eval_nonzeroCount (s : State) : eval .ne s = (zeroCount s).map (! ·) := rfl

theorem advance_ok (s : State) :
    ∃ s', runBlock isa Impl.Rc2.X86.Cbc.advance s = some s' ∧
      s'.gpr .esi = s.gpr .esi + 8 ∧ s'.gpr .edi = s.gpr .edi - 1 ∧
      s'.zf = some ((s.gpr .edi - 1) == 0) ∧ Keep [.esi, .edi] s s' := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, Impl.Rc2.X86.Cbc.advance,
      runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
      Option.bind_some, gpr_setReg, gpr_arithFlags]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true]
  · exact gpr_setReg_self _ _ _
  · rw [zf_setReg, zf_arithFlags]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, gpr_arithFlags, hr.1, hr.2, ite_false]
    · simp only [mem_setReg, mem_arithFlags]
    · simp only [rd_setReg, rd_arithFlags]
    · simp only [wr_setReg, wr_arithFlags]

end VG.Proof.Rc2.X86.Cbc

end

section

/-! # Permissions and separation for one CBC step -/

namespace VG.Proof.Rc2.X86.Cbc

open VG VG.X86

abbrev keyR (s : State) : Region := ⟨addr32 (s.gpr .ebx), 128⟩
abbrev ivR (s : State) : Region := ⟨addr32 (s.gpr .ecx), 8⟩
abbrev dataR (s : State) (n : Nat := 1) : Region := ⟨addr32 (s.gpr .esi), 8 * n⟩
abbrev bufR (s : State) : Region := ⟨addr32 (s.gpr .ebp), 512⟩

abbrev stackR (s : State) : Region := below (s.gpr .esp) 16

structure StepPre (s : State) (n : Nat := 1) : Prop where
  keyFit : (s.gpr .ebx).toNat + 128 ≤ 2 ^ 32
  ivFit : (s.gpr .ecx).toNat + 8 ≤ 2 ^ 32
  dataFit : (s.gpr .esi).toNat + 8 * n ≤ 2 ^ 32
  bufFit : (s.gpr .ebp).toNat + 512 ≤ 2 ^ 32
  reads : Covers [keyR s, ivR s, dataR s n, bufR s] (s.rd ++ s.wr)
  writes : Covers [ivR s, dataR s n, bufR s] s.wr
  keyIv : (keyR s).Disjoint (ivR s)
  keyData : (keyR s).Disjoint (dataR s n)
  keyBuf : (keyR s).Disjoint (bufR s)
  ivData : (ivR s).Disjoint (dataR s n)
  ivBuf : (ivR s).Disjoint (bufR s)
  dataBuf : (dataR s n).Disjoint (bufR s)

  stackLo : 16 ≤ (s.gpr .esp).toNat
  stackKey : (stackR s).Disjoint (keyR s)
  stackIv : (stackR s).Disjoint (ivR s)
  stackData : (stackR s).Disjoint (dataR s n)
  stackBuf : (stackR s).Disjoint (bufR s)

theorem StepPre.transport {s s' : State} {n : Nat} (hp : StepPre s n)
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) (regs : ∀ r ∈ kept, s'.gpr r = s.gpr r) : StepPre s' n := by
  obtain a := regs .ebx (by decide)
  obtain b := regs .ecx (by decide)
  obtain c := regs .esi (by decide)
  obtain d := regs .ebp (by decide)
  obtain e := regs .esp (by decide)
  constructor
  · simpa only [a] using hp.keyFit
  · simpa only [b] using hp.ivFit
  · simpa only [c] using hp.dataFit
  · simpa only [d] using hp.bufFit
  · simpa only [keyR, ivR, dataR, bufR, rd, wr, a, b, c, d] using hp.reads
  · simpa only [keyR, ivR, dataR, bufR, rd, wr, a, b, c, d] using hp.writes
  · simpa only [keyR, ivR, dataR, bufR, rd, wr, a, b, c, d] using hp.keyIv
  · simpa only [keyR, ivR, dataR, bufR, rd, wr, a, b, c, d] using hp.keyData
  · simpa only [keyR, ivR, dataR, bufR, rd, wr, a, b, c, d] using hp.keyBuf
  · simpa only [keyR, ivR, dataR, bufR, rd, wr, a, b, c, d] using hp.ivData
  · simpa only [keyR, ivR, dataR, bufR, rd, wr, a, b, c, d] using hp.ivBuf
  · simpa only [keyR, ivR, dataR, bufR, rd, wr, a, b, c, d] using hp.dataBuf

  · simpa only [e] using hp.stackLo
  · simpa only [stackR, keyR, ivR, dataR, bufR, a, b, c, d, e] using hp.stackKey
  · simpa only [stackR, keyR, ivR, dataR, bufR, a, b, c, d, e] using hp.stackIv
  · simpa only [stackR, keyR, ivR, dataR, bufR, a, b, c, d, e] using hp.stackData
  · simpa only [stackR, keyR, ivR, dataR, bufR, a, b, c, d, e] using hp.stackBuf

theorem StepPre.keep {s s' : State} {m : Mem} {n : Nat} (hp : StepPre s n) (h : Keep [.eax, .edx] {s with mem := m} s') : StepPre s' n :=
  hp.transport h.rd h.wr fun r hr => h.reg r (by
    obtain sep : ∀ r ∈ kept, r ∉ [.eax, .edx] := by decide
    exact sep r hr)

theorem StepPre.call {s : State} (hp : StepPre s) : CallPre s := by
  constructor
  · have hc : Covers [⟨addr32 (s.gpr .ebx), 128⟩, ⟨addr32 (s.gpr .esi), 8⟩, ⟨addr32 (s.gpr .ebp), 256⟩]
        [keyR s, ivR s, dataR s, bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨keyR s, by simp, 0, by simp, by simp⟩
      · exact ⟨dataR s, by simp, 0, by simp, by simp⟩
      · exact ⟨bufR s, by simp, 0, by simp, by simp⟩
    exact fun a n h => hp.reads a n (hc a n h)
  · have hc : Covers [⟨addr32 (s.gpr .esi), 8⟩, ⟨addr32 (s.gpr .ebp), 256⟩] [ivR s, dataR s, bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨dataR s, by simp, 0, by simp, by simp⟩
      · exact ⟨bufR s, by simp, 0, by simp, by simp⟩
    exact fun a n h => hp.writes a n (hc a n h)
  · exact hp.keyBuf.sub_right (Region.sub_prefix (by decide))
  · exact hp.dataBuf.sub_right (Region.sub_prefix (by decide))
  · exact hp.keyFit
  · simpa only [Nat.mul_one] using hp.dataFit
  · have := hp.bufFit; omega_using [this]
  · exact hp.stackLo
  · exact hp.stackKey
  · exact hp.stackData
  · exact hp.stackBuf.sub_right (Region.sub_prefix (by decide))

theorem StepPre.readData {s : State} (hp : StepPre s) : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .esi)) 8 :=
  hp.reads _ _ ⟨dataR s, by simp, Region.contains_self _ _⟩

theorem StepPre.readIv {s : State} (hp : StepPre s) : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .ecx)) 8 :=
  hp.reads _ _ ⟨ivR s, by simp, Region.contains_self _ _⟩

theorem StepPre.writeData {s : State} (hp : StepPre s) : InRegions s.wr (addr32 (s.gpr .esi)) 8 :=
  hp.writes _ _ ⟨dataR s, by simp, Region.contains_self _ _⟩

theorem StepPre.writeIv {s : State} (hp : StepPre s) : InRegions s.wr (addr32 (s.gpr .ecx)) 8 :=
  hp.writes _ _ ⟨ivR s, by simp, Region.contains_self _ _⟩

theorem StepPre.readBuf {s : State} (hp : StepPre s) (i : Nat) (hi : i + 8 ≤ 512) :
    InRegions (s.rd ++ s.wr) (addr32 (s.gpr .ebp) + BitVec.ofNat 64 i) 8 :=
  hp.reads _ _ ⟨bufR s, by simp, Offset.contains_base _ hi (by omega_using [hi])⟩

theorem StepPre.writeBuf {s : State} (hp : StepPre s) (i : Nat) (hi : i + 8 ≤ 512) :
    InRegions s.wr (addr32 (s.gpr .ebp) + BitVec.ofNat 64 i) 8 :=
  hp.writes _ _ ⟨bufR s, by simp, Offset.contains_base _ hi (by omega_using [hi])⟩

end VG.Proof.Rc2.X86.Cbc

end

/-! # The frame preserved by a CBC step -/

namespace VG.Proof.Rc2.X86.Cbc

open VG VG.X86

def stepWrites (s : State) : List Region := [ivR s, dataR s, ⟨addr32 (s.gpr .ebp), 264⟩, stackR s]

structure Pinned (s s' : State) : Prop where
  reg : ∀ r ∈ kept, s'.gpr r = s.gpr r
  callee : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame (stepWrites s) s.mem s'.mem

theorem Pinned.of_keep {s s' : State} {m : Mem} (h : Keep [.eax, .edx] {s with mem := m} s')
    (frame : Frame (stepWrites s) s.mem m) : Pinned s s' := by
  obtain k : ∀ r ∈ kept, r ∉ [.eax, .edx] := by decide
  obtain c : ∀ r ∈ calleeSaved, r ∉ [.eax, .edx] := by decide
  exact ⟨fun r hr => h.reg r (k r hr), fun r hr => h.reg r (c r hr), h.rd, h.wr, by rw [h.mem]; exact frame⟩

theorem Pinned.of_call {d : Spec.Rc2.Direction} {s s' : State} (h : CallPost d s s') : Pinned s s' := by
  refine ⟨h.reg, h.callee, h.rd, h.wr, h.mem.sub ?_⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨dataR s, by simp [stepWrites], fun _ h => h⟩
  · exact ⟨⟨addr32 (s.gpr .ebp), 264⟩, by simp [stepWrites], Region.sub_prefix (by decide)⟩
  · exact ⟨stackR s, by simp [stepWrites], fun _ h => h⟩

theorem Pinned.writes_eq {s s' : State} (h : Pinned s s') : stepWrites s' = stepWrites s := by
  simp only [stepWrites, ivR, dataR, stackR, h.reg .ecx (by decide), h.reg .esi (by decide),
    h.reg .ebp (by decide), h.reg .esp (by decide)]

theorem Pinned.trans {s s' s'' : State} (h : Pinned s s') (h' : Pinned s' s'') : Pinned s s'' := by
  refine ⟨fun r hr => (h'.reg r hr).trans (h.reg r hr), fun r hr => (h'.callee r hr).trans (h.callee r hr),
    h'.rd.trans h.rd, h'.wr.trans h.wr, ?_⟩
  have f := h'.mem
  rw [h.writes_eq] at f
  exact h.mem.trans f

theorem Pinned.pre {s s' : State} {n : Nat} (h : Pinned s s') (hp : StepPre s n) : StepPre s' n :=
  hp.transport h.rd h.wr h.reg

theorem Pinned.schedule {s s' : State} (h : Pinned s s') (hp : StepPre s) :
    Spec.Rc2.scheduleAt s'.mem (addr32 (s.gpr .ebx)) = Spec.Rc2.scheduleAt s.mem (addr32 (s.gpr .ebx)) := by
  apply scheduleAt_frame h.mem
  simpa only [stepWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro hp.keyIv (And.intro hp.keyData (And.intro
      (hp.keyBuf.sub_right (Region.sub_prefix (by decide : 264 ≤ 512))) hp.stackKey.symm))

theorem CallPost.iv {d : Spec.Rc2.Direction} {s s' : State} (h : CallPost d s s') (hp : StepPre s) :
    Spec.Rc2.blockAt s'.mem (addr32 (s.gpr .ecx)) = Spec.Rc2.blockAt s.mem (addr32 (s.gpr .ecx)) := by
  apply blockAt_frame h.mem
  simpa only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro hp.ivData (And.intro
      (hp.ivBuf.sub_right (Region.sub_prefix (by decide : 256 ≤ 512))) hp.stackIv.symm)

structure StepPost (d : Spec.Rc2.Direction) (s s' : State) : Prop extends Pinned s s' where
  data : Spec.Rc2.blockAt s'.mem (addr32 (s.gpr .esi)) =
    (Proof.Rc2.cbcStep (Spec.Rc2.scheduleAt s.mem (addr32 (s.gpr .ebx))) d
      (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .ecx))) (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .esi)))).1
  iv : Spec.Rc2.blockAt s'.mem (addr32 (s.gpr .ecx)) =
    (Proof.Rc2.cbcStep (Spec.Rc2.scheduleAt s.mem (addr32 (s.gpr .ebx))) d
      (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .ecx))) (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .esi)))).2

end VG.Proof.Rc2.X86.Cbc

end

section

/-! # One CBC decryption step, retaining the original ciphertext -/

namespace VG.Proof.Rc2.X86.Cbc

open VG VG.X86 VG.Impl.Rc2.X86

abbrev stashR (s : State) : Region := ⟨addr32 (s.gpr .ebp) + BitVec.ofNat 64 256, 8⟩

theorem stash_sub (s : State) : Region.Sub (stashR s) (bufR s) :=
  Offset.sub_base _ (by decide)

theorem call_stash {d : Spec.Rc2.Direction} {s s' : State} (hp : StepPre s) (h : CallPost d s s') :
    Spec.Rc2.blockAt s'.mem (stashR s).base = Spec.Rc2.blockAt s.mem (stashR s).base := by
  apply blockAt_frame h.mem
  obtain sep : (stashR s).Disjoint ⟨addr32 (s.gpr .ebp), 256⟩ := by
    obtain h := Offset.disjoint (addr32 (s.gpr .ebp)) (d := 256) (n := 8) (e := 0) (k := 256)
      (by omega_using []) (by decide) (by decide)
    simpa using h
  simpa only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro ((hp.dataBuf.sub_right (stash_sub s)).symm) (And.intro sep
      (hp.stackBuf.sub_right (stash_sub s)).symm)

theorem decryptStep_ok (s : State) (hp : StepPre s) :
    WP isa (Impl.Rc2.X86.Cbc.step .decrypt) s (StepPost .decrypt s) := by
  rw [Impl.Rc2.X86.Cbc.step]
  apply WP.seq
  apply WP.mono (copy64_ok s .esi .ebp 0 256 (by decide) (by decide)
    (by simpa using hp.dataFit) (by have := hp.bufFit; omega_using [this]) (by simpa using hp.readData) (hp.writeBuf 256 (by decide)))
  intro s₁ keep₁
  simp only [BitVec.add_zero] at keep₁
  obtain frame₁ : Frame [stashR s] s.mem s₁.mem := by
    rw [keep₁.mem]; exact frame_store64 _ _ _
  obtain pin₁ : Pinned s s₁ := by
    apply Pinned.of_keep keep₁
    apply (frame_store64 _ _ _).sub
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact ⟨⟨addr32 (s.gpr .ebp), 264⟩, by simp [stepWrites], Offset.sub_base _ (by decide)⟩
  obtain hp₁ := pin₁.pre hp
  obtain key₁ := pin₁.schedule hp
  obtain data₁ := blockAt_frame frame₁ (addr32 (s.gpr .esi)) (by simpa using hp.dataBuf.sub_right (stash_sub s))
  obtain iv₁ := blockAt_frame frame₁ (addr32 (s.gpr .ecx)) (by simpa using hp.ivBuf.sub_right (stash_sub s))
  obtain stash₁ : Spec.Rc2.blockAt s₁.mem (stashR s).base = Spec.Rc2.blockAt s.mem (addr32 (s.gpr .esi)) := by
    rw [keep₁.mem]; exact blockAt_copy _ _ _
  apply WP.seq
  apply WP.mono (call_ok .decrypt s₁ hp₁.call)
  intro s₂ h₂
  obtain pin₂ := pin₁.trans (Pinned.of_call h₂)
  obtain hp₂ := pin₂.pre hp
  have output₂ := h₂.output
  rw [pin₁.reg .esi (by decide), pin₁.reg .ebx (by decide), key₁, data₁] at output₂
  obtain iv₂ := h₂.iv hp₁
  rw [pin₁.reg .ecx (by decide), iv₁] at iv₂
  obtain stash₂ := call_stash hp₁ h₂
  simp only [pin₁.reg .ebp (by decide)] at stash₂
  obtain stash₂' := stash₂.trans stash₁
  change WP isa (.block (Impl.Rc2.X86.Cbc.xor64 .esi .ecx ++
    Impl.Rc2.X86.Cbc.copy64 .ebp .ecx 256 0)) s₂ _
  rw [WP.block_append_iff]
  apply WP.mono (xor64_ok s₂ .esi .ecx (by decide) (by decide)
    (by simpa using hp₂.dataFit) hp₂.ivFit hp₂.readData hp₂.readIv hp₂.writeData)
  intro s₃ keep₃
  obtain frame₃ : Frame [dataR s₂] s₂.mem s₃.mem := by
    rw [keep₃.mem]; exact frame_store64 _ _ _
  obtain pin₃ := Pinned.of_keep keep₃ ((frame_store64 _ _ _).mono (by simp [stepWrites]))
  obtain pin₀₃ := pin₂.trans pin₃
  obtain hp₃ := pin₀₃.pre hp
  obtain data₃ : Spec.Rc2.blockAt s₃.mem (addr32 (s.gpr .esi)) =
      Proof.Rc2.xorBlock (Spec.Rc2.decryptBlock (Spec.Rc2.scheduleAt s.mem (addr32 (s.gpr .ebx)))
        (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .esi)))) (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .ecx))) := by
    obtain h : Spec.Rc2.blockAt s₃.mem (addr32 (s₂.gpr .esi)) =
        Proof.Rc2.xorBlock (Spec.Rc2.blockAt s₂.mem (addr32 (s₂.gpr .esi))) (Spec.Rc2.blockAt s₂.mem (addr32 (s₂.gpr .ecx))) := by
      rw [keep₃.mem]; exact blockAt_xor _ _ _
    rw [pin₂.reg .esi (by decide), pin₂.reg .ecx (by decide), output₂, iv₂] at h
    exact h
  obtain stash₃ := blockAt_frame frame₃ (stashR s₂).base
    (by simpa using (hp₂.dataBuf.sub_right (stash_sub s₂)).symm)
  simp only [pin₂.reg .ebp (by decide)] at stash₃
  obtain stash₃' := stash₃.trans stash₂'
  apply WP.mono (copy64_ok s₃ .ebp .ecx 256 0 (by decide) (by decide)
    (by have := hp₃.bufFit; omega_using [this]) (by simpa using hp₃.ivFit) (hp₃.readBuf 256 (by decide)) (by simpa using hp₃.writeIv))
  intro s₄ keep₄
  simp only [BitVec.add_zero] at keep₄
  obtain frame₄ : Frame [ivR s₃] s₃.mem s₄.mem := by
    rw [keep₄.mem]; exact frame_store64 _ _ _
  obtain pin₄ := Pinned.of_keep keep₄ ((frame_store64 _ _ _).mono (by simp [stepWrites]))
  refine ⟨pin₀₃.trans pin₄, ?_, ?_⟩
  · have same := blockAt_frame frame₄ (addr32 (s₃.gpr .esi)) (by simpa using hp₃.ivData.symm)
    rw [pin₀₃.reg .esi (by decide)] at same
    exact same.trans data₃
  · have out : Spec.Rc2.blockAt s₄.mem (addr32 (s₃.gpr .ecx)) = Spec.Rc2.blockAt s₃.mem (stashR s₃).base := by
      rw [keep₄.mem]; exact blockAt_copy _ _ _
    simp only [pin₀₃.reg .ecx (by decide), pin₀₃.reg .ebp (by decide)] at out
    exact out.trans stash₃'

end VG.Proof.Rc2.X86.Cbc

end

section

/-! # Restricting CBC permissions to a consecutive subrange -/

namespace VG.Proof.Rc2.X86.Cbc

open VG VG.X86

theorem StepPre.slice {s s' : State} {n m i : Nat} (hp : StepPre s n) (bound : i + m ≤ n)
    (startFit : (s.gpr .esi).toNat + 8 * i < 2 ^ 32)
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr)
    (key : s'.gpr .ebx = s.gpr .ebx) (iv : s'.gpr .ecx = s.gpr .ecx)
    (buf : s'.gpr .ebp = s.gpr .ebp) (sp : s'.gpr .esp = s.gpr .esp)
    (ptr : s'.gpr .esi = s.gpr .esi + BitVec.ofNat 32 (8 * i)) : StepPre s' m := by
  obtain ptrAddr : addr32 (s'.gpr .esi) = addr32 (s.gpr .esi) + BitVec.ofNat 64 (8 * i) := by
    rw [ptr]; exact addr_add startFit
  obtain fit : (s'.gpr .esi).toNat + 8 * m ≤ 2 ^ 32 := by
    rw [ptr, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * i) (by omega_using [startFit]),
      Nat.mod_eq_of_lt startFit]
    have := hp.dataFit
    omega_using [bound, this]
  obtain sub : Region.Sub (dataR s' m) (dataR s n) := by
    change Region.Sub ⟨addr32 (s'.gpr .esi), 8 * m⟩ ⟨addr32 (s.gpr .esi), 8 * n⟩
    rw [ptrAddr]
    exact Offset.sub_base _ (by omega_using [bound])
  constructor
  · rw [key]; exact hp.keyFit
  · rw [iv]; exact hp.ivFit
  · exact fit
  · rw [buf]; exact hp.bufFit
  · have hc : Covers [keyR s', ivR s', dataR s' m, bufR s'] [keyR s, ivR s, dataR s n, bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨keyR s, by simp, 0, by simp [key], by simp⟩
      · exact ⟨ivR s, by simp, 0, by simp [iv], by simp⟩
      · exact ⟨dataR s n, by simp, 8 * i, ptrAddr, by change 8 * i + 8 * m ≤ 8 * n; omega_using [bound]⟩
      · exact ⟨bufR s, by simp, 0, by simp [buf], by simp⟩
    rw [rd, wr]
    exact fun a k h => hp.reads a k (hc a k h)
  · have hc : Covers [ivR s', dataR s' m, bufR s'] [ivR s, dataR s n, bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨ivR s, by simp, 0, by simp [iv], by simp⟩
      · exact ⟨dataR s n, by simp, 8 * i, ptrAddr, by change 8 * i + 8 * m ≤ 8 * n; omega_using [bound]⟩
      · exact ⟨bufR s, by simp, 0, by simp [buf], by simp⟩
    rw [wr]
    exact fun a k h => hp.writes a k (hc a k h)
  · simpa only [keyR, ivR, key, iv] using hp.keyIv
  · simpa only [keyR, key] using hp.keyData.sub_right sub
  · simpa only [keyR, bufR, key, buf] using hp.keyBuf
  · simpa only [ivR, iv] using hp.ivData.sub_right sub
  · simpa only [ivR, bufR, iv, buf] using hp.ivBuf
  · simpa only [bufR, buf] using hp.dataBuf.sub_left sub

  · rw [sp]; exact hp.stackLo
  · simpa only [stackR, keyR, sp, key] using hp.stackKey
  · simpa only [stackR, ivR, sp, iv] using hp.stackIv
  · simpa only [stackR, sp] using hp.stackData.sub_right sub
  · simpa only [stackR, bufR, sp, buf] using hp.stackBuf

theorem StepPre.head {s : State} {n : Nat} (hp : StepPre s n) (hn : 1 ≤ n) : StepPre s :=
  hp.slice (i := 0) hn (by simpa using (s.gpr .esi).isLt) rfl rfl rfl rfl rfl rfl (by simp)

end VG.Proof.Rc2.X86.Cbc

end

section

/-! # One CBC encryption step -/

namespace VG.Proof.Rc2.X86.Cbc

open VG VG.X86 VG.Impl.Rc2.X86

theorem encryptStep_ok (s : State) (hp : StepPre s) :
    WP isa (Impl.Rc2.X86.Cbc.step .encrypt) s (StepPost .encrypt s) := by
  rw [Impl.Rc2.X86.Cbc.step]
  apply WP.seq
  apply WP.mono (xor64_ok s .esi .ecx (by decide) (by decide)
    (by simpa using hp.dataFit) hp.ivFit hp.readData hp.readIv hp.writeData)
  intro s₁ keep₁
  obtain pin₁ := Pinned.of_keep keep₁ ((frame_store64 _ _ _).mono (by simp [stepWrites]))
  obtain hp₁ := pin₁.pre hp
  obtain key₁ := pin₁.schedule hp
  obtain data₁ : Spec.Rc2.blockAt s₁.mem (addr32 (s.gpr .esi)) =
      Proof.Rc2.xorBlock (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .esi))) (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .ecx))) := by
    rw [keep₁.mem]; exact blockAt_xor _ _ _
  apply WP.seq
  apply WP.mono (call_ok .encrypt s₁ hp₁.call)
  intro s₂ h₂
  obtain pin₂ := pin₁.trans (Pinned.of_call h₂)
  obtain hp₂ := pin₂.pre hp
  have output₂ := h₂.output
  rw [pin₁.reg .esi (by decide), pin₁.reg .ebx (by decide), key₁, data₁] at output₂
  apply WP.mono (copy64_ok s₂ .esi .ecx 0 0 (by decide) (by decide)
    (by simpa using hp₂.dataFit) (by simpa using hp₂.ivFit) (by simpa using hp₂.readData) (by simpa using hp₂.writeIv))
  intro s₃ keep₃
  simp only [BitVec.add_zero] at keep₃
  obtain frame₃ : Frame [ivR s₂] s₂.mem s₃.mem := by
    rw [keep₃.mem]; exact frame_store64 _ _ _
  obtain pin₃ := Pinned.of_keep keep₃ ((frame_store64 _ _ _).mono (by simp [stepWrites]))
  refine ⟨pin₂.trans pin₃, ?_, ?_⟩
  · have same := blockAt_frame frame₃ (addr32 (s₂.gpr .esi)) (by simpa using hp₂.ivData.symm)
    rw [pin₂.reg .esi (by decide)] at same
    exact same.trans output₂
  · have out : Spec.Rc2.blockAt s₃.mem (addr32 (s₂.gpr .ecx)) = Spec.Rc2.blockAt s₂.mem (addr32 (s₂.gpr .esi)) := by
      rw [keep₃.mem]; exact blockAt_copy _ _ _
    rw [pin₂.reg .ecx (by decide), pin₂.reg .esi (by decide)] at out
    exact out.trans output₂

end VG.Proof.Rc2.X86.Cbc

end

/-! # A CBC loop iteration and its public counter -/

namespace VG.Proof.Rc2.X86.Cbc

open VG VG.X86 VG.Impl.Rc2.X86

theorem step_ok (d : Spec.Rc2.Direction) (s : State) (hp : StepPre s) :
    WP isa (Impl.Rc2.X86.Cbc.step d) s (StepPost d s) := by
  cases d
  · exact encryptStep_ok s hp
  · exact decryptStep_ok s hp

structure BodyPost (d : Spec.Rc2.Direction) (s : State) (n : Nat) (s' : State) : Prop where
  ptr : s'.gpr .esi = s.gpr .esi + 8
  count : s'.gpr .edi = BitVec.ofNat 32 (n - 1)
  flag : zeroCount s' = some (decide (n = 1))
  reg : ∀ r ∈ kept, r ≠ .esi → r ≠ .edi → s'.gpr r = s.gpr r
  callee : ∀ r ∈ calleeSaved, r ≠ .esi → r ≠ .edi → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame (stepWrites s) s.mem s'.mem
  data : Spec.Rc2.blockAt s'.mem (addr32 (s.gpr .esi)) =
    (Proof.Rc2.cbcStep (Spec.Rc2.scheduleAt s.mem (addr32 (s.gpr .ebx))) d
      (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .ecx))) (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .esi)))).1
  iv : Spec.Rc2.blockAt s'.mem (addr32 (s.gpr .ecx)) =
    (Proof.Rc2.cbcStep (Spec.Rc2.scheduleAt s.mem (addr32 (s.gpr .ebx))) d
      (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .ecx))) (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .esi)))).2

theorem body_ok (d : Spec.Rc2.Direction) (s : State) (n : Nat) (hn : 1 ≤ n) (bound : n < 2 ^ 32)
    (count : s.gpr .edi = BitVec.ofNat 32 n) (hp : StepPre s) :
    WP isa (Impl.Rc2.X86.Cbc.body d) s (BodyPost d s n) := by
  rw [Impl.Rc2.X86.Cbc.body]
  apply WP.seq
  apply WP.mono (step_ok d s hp)
  intro s₁ h₁
  obtain ⟨s₂, run₂, ptr₂, count₂, flag₂, keep₂⟩ := advance_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  obtain count' : s₁.gpr .edi - 1 = BitVec.ofNat 32 (n - 1) := by
    rw [h₁.reg .edi (by decide), count]
    exact Offset.ofNat_sub_ofNat hn
  refine ⟨by rw [ptr₂, h₁.reg .esi (by decide)], count₂.trans count', ?_, ?_, ?_,
    keep₂.rd.trans h₁.rd, keep₂.wr.trans h₁.wr, ?_, ?_, ?_⟩
  · rw [zeroCount, flag₂, count']
    obtain eqZero := counter_eq (n - 1) 0 (by omega_using [bound]) (by decide)
    simp only [BitVec.sub_zero] at eqZero
    change some (BitVec.ofNat 32 (n - 1) == 0#32) = _
    rw [eqZero]
    obtain he : n - 1 = 0 ↔ n = 1 := by omega_using [hn]
    simp only [he]
  · intro r hr hs hb
    exact (keep₂.reg r (by simp [hs, hb])).trans (h₁.reg r hr)
  · intro r hr hs hb
    exact (keep₂.reg r (by simp [hs, hb])).trans (h₁.callee r hr)
  · rw [keep₂.mem]; exact h₁.mem
  · rw [keep₂.mem]; exact h₁.data
  · rw [keep₂.mem]; exact h₁.iv

theorem BodyPost.tail {d : Spec.Rc2.Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s (n + 1) s') (hp : StepPre s (n + 1)) (hn : 1 ≤ n) : StepPre s' n :=
  hp.slice (i := 1) (by omega_using []) (by have := hp.dataFit; omega_using [hn, this]) h.rd h.wr
    (h.reg .ebx (by decide) (by decide) (by decide))
    (h.reg .ecx (by decide) (by decide) (by decide))
    (h.reg .ebp (by decide) (by decide) (by decide))
    (h.reg .esp (by decide) (by decide) (by decide))
    h.ptr

end VG.Proof.Rc2.X86.Cbc

end

end

@[expose] public section

section

/-! CBC register saves, stack arguments, and restoration. -/
namespace VG.Proof.Rc2.X86.Cbc
open VG VG.X86 VG.X86.RegUpd VG.Impl.Rc2.X86

def callerSaved : List Reg := [.ebp, .ebx, .esi, .edi]

def savedMem (s : State) : Mem :=
  ((((s.mem.writeW (addr32 (s.gpr .eax) + BitVec.ofNat 64 264) (s.gpr .ebp)).writeW (addr32 (s.gpr .eax) + BitVec.ofNat 64 268) (s.gpr .ebx)).writeW (addr32 (s.gpr .eax) + BitVec.ofNat 64 272) (s.gpr .esi)).writeW (addr32 (s.gpr .eax) + BitVec.ofNat 64 276) (s.gpr .edi))

theorem save_ok (s : State)
    (fit : (s.gpr .eax).toNat + 512 ≤ 2 ^ 32)
    (w0 : InRegions s.wr (addr32 (s.gpr .eax) + BitVec.ofNat 64 264) 4)
    (w1 : InRegions s.wr (addr32 (s.gpr .eax) + BitVec.ofNat 64 268) 4)
    (w2 : InRegions s.wr (addr32 (s.gpr .eax) + BitVec.ofNat 64 272) 4)
    (w3 : InRegions s.wr (addr32 (s.gpr .eax) + BitVec.ofNat 64 276) 4)
    : ∃ s', runBlock isa Impl.Rc2.X86.Cbc.save s = some s' ∧ Keep [] {s with mem := savedMem s} s' := by
  have a264 : addr32 (s.gpr .eax + BitVec.ofNat 32 264) = addr32 (s.gpr .eax) + BitVec.ofNat 64 264 := addr_add (by omega_using [fit])
  have a268 : addr32 (s.gpr .eax + BitVec.ofNat 32 268) = addr32 (s.gpr .eax) + BitVec.ofNat 64 268 := addr_add (by omega_using [fit])
  have a272 : addr32 (s.gpr .eax + BitVec.ofNat 32 272) = addr32 (s.gpr .eax) + BitVec.ofNat 64 272 := addr_add (by omega_using [fit])
  have a276 : addr32 (s.gpr .eax + BitVec.ofNat 32 276) = addr32 (s.gpr .eax) + BitVec.ofNat 64 276 := addr_add (by omega_using [fit])
  refine ⟨_, by
    simp only [Impl.Rc2.X86.Cbc.save, runBlock_cons, runStep_some, runBlock_nil,
      exec, memOp, State.ea, State.store32, ← addr_eq_def,
      a264, a268, a272, a276, w0, w1, w2, w3, ite_true]
    rfl, ?_⟩
  exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem savedMem_frame (s : State) : Frame [⟨addr32 (s.gpr .eax), 512⟩] s.mem (savedMem s) := by
  unfold savedMem
  apply Frame.writeW (r := ⟨addr32 (s.gpr .eax), 512⟩) (hr := List.mem_cons_self) (hb := Offset.contains_base _ (by decide : 276 + 4 ≤ 512) (by decide))
  apply Frame.writeW (r := ⟨addr32 (s.gpr .eax), 512⟩) (hr := List.mem_cons_self) (hb := Offset.contains_base _ (by decide : 272 + 4 ≤ 512) (by decide))
  apply Frame.writeW (r := ⟨addr32 (s.gpr .eax), 512⟩) (hr := List.mem_cons_self) (hb := Offset.contains_base _ (by decide : 268 + 4 ≤ 512) (by decide))
  apply Frame.writeW (r := ⟨addr32 (s.gpr .eax), 512⟩) (hr := List.mem_cons_self) (hb := Offset.contains_base _ (by decide : 264 + 4 ≤ 512) (by decide))
  exact Frame.refl _ _

theorem savedMem_ebp (s : State) : (savedMem s).readW (addr32 (s.gpr .eax) + BitVec.ofNat 64 264) 32 = s.gpr .ebp := by
  rw [savedMem, Mem.readW_writeW_sep (Offset.sep _ (by decide : 264 + 4 ≤ 276 ∨ 276 + 4 ≤ 264) (by decide) (by decide)) (by decide), Mem.readW_writeW_sep (Offset.sep _ (by decide : 264 + 4 ≤ 272 ∨ 272 + 4 ≤ 264) (by decide) (by decide)) (by decide), Mem.readW_writeW_sep (Offset.sep _ (by decide : 264 + 4 ≤ 268 ∨ 268 + 4 ≤ 264) (by decide) (by decide)) (by decide), Mem.readW_writeW_self32]

theorem savedMem_ebx (s : State) : (savedMem s).readW (addr32 (s.gpr .eax) + BitVec.ofNat 64 268) 32 = s.gpr .ebx := by
  rw [savedMem, Mem.readW_writeW_sep (Offset.sep _ (by decide : 268 + 4 ≤ 276 ∨ 276 + 4 ≤ 268) (by decide) (by decide)) (by decide), Mem.readW_writeW_sep (Offset.sep _ (by decide : 268 + 4 ≤ 272 ∨ 272 + 4 ≤ 268) (by decide) (by decide)) (by decide), Mem.readW_writeW_self32]

theorem savedMem_esi (s : State) : (savedMem s).readW (addr32 (s.gpr .eax) + BitVec.ofNat 64 272) 32 = s.gpr .esi := by
  rw [savedMem, Mem.readW_writeW_sep (Offset.sep _ (by decide : 272 + 4 ≤ 276 ∨ 276 + 4 ≤ 272) (by decide) (by decide)) (by decide), Mem.readW_writeW_self32]

theorem savedMem_edi (s : State) : (savedMem s).readW (addr32 (s.gpr .eax) + BitVec.ofNat 64 276) 32 = s.gpr .edi := by
  rw [savedMem, Mem.readW_writeW_self32]

theorem setup_ok (s : State)
    (readable : ∀ i < 4, InRegions (s.rd ++ s.wr) (argAddr s i) 4) :
    ∃ s', runBlock isa Impl.Rc2.X86.Cbc.setup s = some s' ∧
      s'.gpr .ebx = arg s 0 ∧ s'.gpr .ecx = arg s 1 ∧ s'.gpr .esi = arg s 2 ∧
      s'.gpr .edi = arg s 3 ∧ s'.gpr .ebp = s.gpr .eax ∧
      zeroCount s' = some (arg s 3 == 0) ∧ Keep [.ebp, .ebx, .ecx, .esi, .edi] s s' := by
  have r0 := readable 0 (by decide)
  have r1 := readable 1 (by decide)
  have r2 := readable 2 (by decide)
  have r3 := readable 3 (by decide)
  simp only [argAddr, Nat.mul_zero, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd] at r0 r1 r2 r3
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Impl.Rc2.X86.Cbc.setup, rr, runBlock_cons, runStep_some,
      runBlock_nil, exec, execAlu, readSrc, memOp, State.ea, State.load32, gpr_setReg,
      mem_setReg, rd_setReg, wr_setReg, r0, r1, r2, r3, Option.map_some, Option.bind_some]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_arithFlags, gpr_setReg, reduceCtorEq, ite_true, ite_false]; rfl
  · simp only [gpr_arithFlags, gpr_setReg, reduceCtorEq, ite_true, ite_false]; rfl
  · simp only [gpr_arithFlags, gpr_setReg, reduceCtorEq, ite_true, ite_false]; rfl
  · simp only [gpr_arithFlags, gpr_setReg, reduceCtorEq, ite_true, ite_false]; rfl
  · simp only [gpr_arithFlags, gpr_setReg, reduceCtorEq, ite_true, ite_false]
  · change some ((arg s 3 - 0) == 0) = _
    exact congrArg (fun x : BitVec 32 => some (x == 0)) (by bv_omega)
  · refine ⟨?_, rfl, rfl, rfl⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_arithFlags, gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

theorem restore_ok (s : State) (values : Reg → BitVec 32)
    (fit : (s.gpr .ebp).toNat + 512 ≤ 2 ^ 32)
    (r0 : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .ebp) + BitVec.ofNat 64 264) 4)
    (v0 : s.mem.readW (addr32 (s.gpr .ebp) + BitVec.ofNat 64 264) 32 = values .ebp)
    (r1 : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .ebp) + BitVec.ofNat 64 268) 4)
    (v1 : s.mem.readW (addr32 (s.gpr .ebp) + BitVec.ofNat 64 268) 32 = values .ebx)
    (r2 : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .ebp) + BitVec.ofNat 64 272) 4)
    (v2 : s.mem.readW (addr32 (s.gpr .ebp) + BitVec.ofNat 64 272) 32 = values .esi)
    (r3 : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .ebp) + BitVec.ofNat 64 276) 4)
    (v3 : s.mem.readW (addr32 (s.gpr .ebp) + BitVec.ofNat 64 276) 32 = values .edi)
    : ∃ s', runBlock isa Impl.Rc2.X86.Cbc.restore s = some s' ∧
      (∀ r ∈ callerSaved, s'.gpr r = values r) ∧ Keep (.eax :: callerSaved) s s' := by
  have a264 : addr32 (s.gpr .ebp + BitVec.ofNat 32 264) = addr32 (s.gpr .ebp) + BitVec.ofNat 64 264 := addr_add (by omega_using [fit])
  have a268 : addr32 (s.gpr .ebp + BitVec.ofNat 32 268) = addr32 (s.gpr .ebp) + BitVec.ofNat 64 268 := addr_add (by omega_using [fit])
  have a272 : addr32 (s.gpr .ebp + BitVec.ofNat 32 272) = addr32 (s.gpr .ebp) + BitVec.ofNat 64 272 := addr_add (by omega_using [fit])
  have a276 : addr32 (s.gpr .ebp + BitVec.ofNat 32 276) = addr32 (s.gpr .ebp) + BitVec.ofNat 64 276 := addr_add (by omega_using [fit])
  refine ⟨_, by
    simp only [Impl.Rc2.X86.Cbc.restore, rr, runBlock_cons, runStep_some, runBlock_nil,
      exec, readSrc, memOp, State.ea, State.load32, gpr_setReg, reduceCtorEq, ite_false, ite_true,
      mem_setReg, rd_setReg, wr_setReg, Option.map_some, ← addr_eq_def,
      a264, a268, a272, a276, r0, r1, r2, r3, v0, v1, v2, v3]
    rfl, ?_⟩
  constructor
  · intro r hr
    simp only [callerSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false]
  · refine ⟨?_, rfl, rfl, rfl⟩
    intro r hr
    simp only [callerSaved, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

end VG.Proof.Rc2.X86.Cbc

end

namespace VG.Proof.Rc2.X86.Cbc
open VG VG.X86

def contract (d : Spec.Rc2.Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨addr32 (arg s 0), 128⟩
    let iv : Region := ⟨addr32 (arg s 1), 8⟩
    let data : Region := ⟨addr32 (arg s 2), 8 * (arg s 3).toNat⟩
    let buf : Region := ⟨addr32 (arg s 4), 512⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨addr32 (s.gpr .esp), 4⟩
    let stack := below (s.gpr .esp) 16
    s.rd = [key, args] ∧ s.wr = [iv, data, buf] ∧ key.Disjoint iv ∧ key.Disjoint data ∧ key.Disjoint buf ∧
      iv.Disjoint data ∧ iv.Disjoint buf ∧ data.Disjoint buf ∧
      args.Disjoint iv ∧ args.Disjoint data ∧ args.Disjoint buf ∧
      ret.Disjoint iv ∧ ret.Disjoint data ∧ ret.Disjoint buf ∧
      stack.Disjoint key ∧ stack.Disjoint iv ∧ stack.Disjoint data ∧ stack.Disjoint buf ∧
      (arg s 0).toNat + 128 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 8 ≤ 2 ^ 32 ∧
      (arg s 4).toNat + 512 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 ∧
      16 ≤ (s.gpr .esp).toNat ∧ (arg s 2).toNat + 8 * (arg s 3).toNat ≤ 2 ^ 32
  post s s' :=
    let out := Proof.Rc2.cbcBlocks (Spec.Rc2.scheduleAt s.mem (addr32 (arg s 0))) d
      (Spec.Rc2.blockAt s.mem (addr32 (arg s 1))) (Spec.Rc2.blocksAt s.mem (addr32 (arg s 2)) (arg s 3).toNat)
    Spec.Rc2.blocksAt s'.mem (addr32 (arg s 2)) (arg s 3).toNat = out.1 ∧
      Spec.Rc2.blockAt s'.mem (addr32 (arg s 1)) = out.2
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

end VG.Proof.Rc2.X86.Cbc

end

end

/-! ### `Rc2.X86.Cbc.Loop`, which this module and modules that import it used -/

section

@[expose] public section

section

/-! # Frames for successive CBC blocks -/

namespace VG.Proof.Rc2.X86.Cbc

open VG VG.X86

def loopWrites (s : State) (n : Nat) : List Region := [ivR s, dataR s n, ⟨addr32 (s.gpr .ebp), 264⟩, stackR s]

theorem loopFrame_slice {s s' : State} {n m i : Nat} {a b : Mem}
    (h : Frame (loopWrites s' m) a b) (bound : i + m ≤ n)
    (iv : s'.gpr .ecx = s.gpr .ecx) (buf : s'.gpr .ebp = s.gpr .ebp) (sp : s'.gpr .esp = s.gpr .esp)
    (ptr : addr32 (s'.gpr .esi) = addr32 (s.gpr .esi) + BitVec.ofNat 64 (8 * i)) :
    Frame (loopWrites s n) a b := by
  apply h.sub
  intro r hr
  simp only [loopWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · refine ⟨ivR s, by simp [loopWrites], ?_⟩
    change Region.Sub ⟨addr32 (s'.gpr .ecx), 8⟩ ⟨addr32 (s.gpr .ecx), 8⟩
    rw [iv]; exact fun _ h => h
  · refine ⟨dataR s n, by simp [loopWrites], ?_⟩
    change Region.Sub ⟨addr32 (s'.gpr .esi), 8 * m⟩ ⟨addr32 (s.gpr .esi), 8 * n⟩
    rw [ptr]
    exact Offset.sub_base _ (by omega_using [bound])
  · refine ⟨⟨addr32 (s.gpr .ebp), 264⟩, by simp [loopWrites], ?_⟩
    rw [buf]; exact fun _ h => h
  · refine ⟨stackR s, by simp [loopWrites], ?_⟩
    change Region.Sub (below (s'.gpr .esp) 16) (below (s.gpr .esp) 16)
    rw [sp]; exact fun _ h => h

theorem BodyPost.frame {d : Spec.Rc2.Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s n s') (hn : 1 ≤ n) : Frame (loopWrites s n) s.mem s'.mem :=
  loopFrame_slice (m := 1) (i := 0) h.mem hn rfl rfl rfl (by simp)

theorem BodyPost.schedule {d : Spec.Rc2.Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s n s') (hp : StepPre s) :
    Spec.Rc2.scheduleAt s'.mem (addr32 (s.gpr .ebx)) = Spec.Rc2.scheduleAt s.mem (addr32 (s.gpr .ebx)) := by
  apply scheduleAt_frame h.mem
  simpa only [stepWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro hp.keyIv (And.intro hp.keyData (And.intro
      (hp.keyBuf.sub_right (Region.sub_prefix (by decide : 264 ≤ 512))) hp.stackKey.symm))

theorem BodyPost.tailData {d : Spec.Rc2.Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s (n + 1) s') (hp : StepPre s (n + 1)) (bound : 8 * (n + 1) ≤ 2 ^ 64) :
    Spec.Rc2.blocksAt s'.mem (addr32 (s.gpr .esi) + 8) n = Spec.Rc2.blocksAt s.mem (addr32 (s.gpr .esi) + 8) n := by
  have sub : Region.Sub ⟨addr32 (s.gpr .esi) + 8, 8 * n⟩ (dataR s (n + 1)) :=
    Offset.sub_base _ (by change 8 + 8 * n ≤ 8 * (n + 1); omega_using [])
  have sep : (Region.mk (addr32 (s.gpr .esi) + 8) (8 * n)).Disjoint (dataR s) :=
    Offset.disjoint_base _ (d := 8) (n := 8 * n) (k := 8) (by decide) (by omega_using [bound])
  apply blocksAt_frame h.mem
  simpa only [stepWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro ((hp.ivData.sub_right sub).symm) (And.intro sep (And.intro
      ((hp.dataBuf.sub_left sub).sub_right (Region.sub_prefix (by decide : 264 ≤ 512))) (hp.stackData.sub_right sub).symm))

theorem firstBlock_frame {d : Spec.Rc2.Direction} {s s' : State} {n : Nat} {m : Mem}
    (h : BodyPost d s (n + 1) s') (hp : StepPre s (n + 1)) (bound : 8 * (n + 1) ≤ 2 ^ 64)
    (hn : 1 ≤ n)
    (frame : Frame (loopWrites s' n) s'.mem m) :
    Spec.Rc2.blockAt m (addr32 (s.gpr .esi)) = Spec.Rc2.blockAt s'.mem (addr32 (s.gpr .esi)) := by
  have first : Region.Sub (dataR s) (dataR s (n + 1)) := Region.sub_prefix (by change 8 ≤ 8 * (n + 1); omega_using [])
  have sep : (dataR s).Disjoint ⟨addr32 (s.gpr .esi) + 8, 8 * n⟩ :=
    Offset.base_disjoint _ (e := 8) (n := 8 * n) (k := 8) (by decide) (by omega_using [bound])
  have ptr : addr32 (s'.gpr .esi) = addr32 (s.gpr .esi) + 8 := by
    rw [h.ptr]
    exact addr_add (k := 8) (by have := hp.dataFit; omega_using [hn, this])
  apply blockAt_frame frame
  have iv := h.reg .ecx (by decide) (by decide) (by decide)
  have buf := h.reg .ebp (by decide) (by decide) (by decide)
  have sp := h.reg .esp (by decide) (by decide) (by decide)
  simpa only [loopWrites, ivR, dataR, stackR, iv, buf, ptr, sp,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro ((hp.ivData.sub_right first).symm) (And.intro sep (And.intro
      ((hp.dataBuf.sub_left first).sub_right (Region.sub_prefix (by decide : 264 ≤ 512))) (hp.stackData.sub_right first).symm))

end VG.Proof.Rc2.X86.Cbc

end

/-! # Correctness of the CBC loop on complete blocks -/

namespace VG.Proof.Rc2.X86.Cbc

open VG VG.X86

structure LoopPost (d : Spec.Rc2.Direction) (s : State) (n : Nat) (s' : State) : Prop where
  ptr : s'.gpr .esi = s.gpr .esi + BitVec.ofNat 32 (8 * n)
  count : s'.gpr .edi = 0
  reg : ∀ r ∈ kept, r ≠ .esi → r ≠ .edi → s'.gpr r = s.gpr r
  callee : ∀ r ∈ calleeSaved, r ≠ .esi → r ≠ .edi → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame (loopWrites s n) s.mem s'.mem
  data : Spec.Rc2.blocksAt s'.mem (addr32 (s.gpr .esi)) n =
    (Proof.Rc2.cbcBlocks (Spec.Rc2.scheduleAt s.mem (addr32 (s.gpr .ebx))) d
      (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .ecx))) (Spec.Rc2.blocksAt s.mem (addr32 (s.gpr .esi)) n)).1
  iv : Spec.Rc2.blockAt s'.mem (addr32 (s.gpr .ecx)) =
    (Proof.Rc2.cbcBlocks (Spec.Rc2.scheduleAt s.mem (addr32 (s.gpr .ebx))) d
      (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .ecx))) (Spec.Rc2.blocksAt s.mem (addr32 (s.gpr .esi)) n)).2

theorem loop_ok (d : Spec.Rc2.Direction) (n : Nat) :
    ∀ s : State, 1 ≤ n → 8 * n ≤ 2 ^ 32 → StepPre s n → s.gpr .edi = BitVec.ofNat 32 n →
      WP isa (.loop (Impl.Rc2.X86.Cbc.body d) .ne) s (LoopPost d s n) := by
  induction n with
  | zero => intro s hn; omega
  | succ n ih =>
    intro s hn bound hp count
    obtain ⟨t₁, s₁, exec₁, h₁⟩ := body_ok d s (n + 1) hn (by omega_using [bound]) count (hp.head hn)
    by_cases hz : n = 0
    · subst n
      refine ⟨_, s₁, Exec.loopExit exec₁ ?_, ?_⟩
      · simp only [eval_nonzeroCount, h₁.flag, decide_true, Option.map_some, Bool.not_true]
      · refine ⟨h₁.ptr, h₁.count, h₁.reg, h₁.callee, h₁.rd, h₁.wr, h₁.frame (by decide), ?_, ?_⟩
        · rw [blocksAt_cons, blocksAt_cons]
          simp only [Spec.Rc2.blocksAt, List.range_zero, List.map_nil, Proof.Rc2.cbcBlocks]
          exact congrArg (· :: []) h₁.data
        · rw [blocksAt_cons]
          simp only [Spec.Rc2.blocksAt, List.range_zero, List.map_nil, Proof.Rc2.cbcBlocks]
          exact h₁.iv
    · have hp₁ := h₁.tail hp (by omega_using [hz])
      obtain ⟨t₂, s₂, exec₂, h₂⟩ := ih s₁ (by omega_using [hz]) (by omega_using [bound]) hp₁ (by simpa using h₁.count)
      refine ⟨_, s₂, Exec.loopNext exec₁ ?_ exec₂, ?_⟩
      · have he : n + 1 ≠ 1 := by omega_using [hz]
        simp only [eval_nonzeroCount, h₁.flag, he, decide_false, Option.map_some, Bool.not_false]
      · have key := h₁.schedule (hp.head hn)
        have tail := h₁.tailData hp (by omega_using [bound])
        have data := h₂.data
        have iv := h₂.iv
        have ki := h₁.reg .ebx (by decide) (by decide) (by decide)
        have vi := h₁.reg .ecx (by decide) (by decide) (by decide)
        have bi := h₁.reg .ebp (by decide) (by decide) (by decide)
        have ptr : addr32 (s₁.gpr .esi) = addr32 (s.gpr .esi) + 8 := by
          rw [h₁.ptr]; exact addr_add (k := 8) (by have := hp.dataFit; omega_using [hz, this])
        rw [ki, vi, ptr, key, tail, h₁.iv] at data
        rw [ki, vi, ptr, key, tail, h₁.iv] at iv
        refine ⟨?_, h₂.count, ?_, ?_, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, ?_, ?_, ?_⟩
        · rw [h₂.ptr, h₁.ptr, BitVec.add_assoc]
          exact congrArg (s.gpr .esi + ·) (by
            change BitVec.ofNat 32 8 + BitVec.ofNat 32 (8 * n) = _
            rw [← BitVec.ofNat_add]
            exact congrArg (BitVec.ofNat 32) (by omega_using []))
        · intro r hr hs hb
          exact (h₂.reg r hr hs hb).trans (h₁.reg r hr hs hb)
        · intro r hr hs hb
          exact (h₂.callee r hr hs hb).trans (h₁.callee r hr hs hb)
        · exact (h₁.frame hn).trans (loopFrame_slice (i := 1) h₂.mem (by omega_using []) vi bi (h₁.reg .esp (by decide) (by decide) (by decide)) ptr)
        · have first := firstBlock_frame h₁ hp (by omega_using [bound]) (by omega_using [hz]) h₂.mem
          rw [blocksAt_cons, first, h₁.data, data, blocksAt_cons]
          rfl
        · rw [blocksAt_cons]
          exact iv

theorem maybeLoop_ok (d : Spec.Rc2.Direction) (s : State) (n : Nat) (bound : 8 * n ≤ 2 ^ 32)
    (hp : StepPre s n) (count : s.gpr .edi = BitVec.ofNat 32 n)
    (flag : zeroCount s = some (s.gpr .edi == 0)) :
    WP isa (.ite .e (.block []) (.loop (Impl.Rc2.X86.Cbc.body d) .ne)) s (LoopPost d s n) := by
  have eqZero := counter_eq n 0 (by omega_using [bound]) (by decide)
  simp only [BitVec.sub_zero] at eqZero
  have flag' : zeroCount s = some (decide (n = 0)) := by
    rw [flag, count]
    exact congrArg some eqZero
  by_cases hz : n = 0
  · subst n
    apply WP.ite true (by simp only [eval_zeroCount, flag', decide_true])
    · intro _
      apply WP.block_nil
      refine ⟨by simp, count, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, rfl, rfl, Frame.refl _ _, ?_, ?_⟩
      · rfl
      · rfl
    · simp
  · apply WP.ite false (by simp only [eval_zeroCount, flag', hz, decide_false])
    · simp
    · intro _
      exact loop_ok d n s (by omega_using [hz]) bound hp count

theorem LoopPost.scratchRead {d : Spec.Rc2.Direction} {s s' : State} {n : Nat}
    (h : LoopPost d s n s') (hp : StepPre s n) (i : Nat) (lo : 264 ≤ i) (hi : i + 4 ≤ 512) :
    s'.mem.readW (addr32 (s.gpr .ebp) + BitVec.ofNat 64 i) 32 = s.mem.readW (addr32 (s.gpr .ebp) + BitVec.ofNat 64 i) 32 := by
  have sub : Region.Sub ⟨addr32 (s.gpr .ebp) + BitVec.ofNat 64 i, 4⟩ (bufR s) := Offset.sub_base _ hi
  have sep : (Region.mk (addr32 (s.gpr .ebp) + BitVec.ofNat 64 i) 4).Disjoint ⟨addr32 (s.gpr .ebp), 264⟩ :=
    Offset.disjoint_base _ lo (by omega_using [hi])
  apply h.mem.readW (r := ⟨addr32 (s.gpr .ebp) + BitVec.ofNat 64 i, 4⟩) (Region.contains_self _ _)
    (hn := by decide)
  simpa only [loopWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro ((hp.ivBuf.sub_right sub).symm) (And.intro ((hp.dataBuf.sub_right sub).symm)
      (And.intro sep (hp.stackBuf.sub_right sub).symm))

end VG.Proof.Rc2.X86.Cbc

end

end

/-! ### `Rc2.X86.Cbc.ConstantTime`, which the modules that import this one used -/

section

@[expose] public section

section

section

/-! # Constant-time CBC steps with public registers restored by the block call -/

namespace VG.Proof.Rc2.X86.Cbc

open VG VG.X86 VG.Impl.Rc2.X86

def EqKept (s₁ s₂ : State) : Prop := ∀ r ∈ kept, s₁.gpr r = s₂.gpr r

def StepRel (s₁ s₂ : State) : Prop := StepPre s₁ ∧ StepPre s₂ ∧ EqKept s₁ s₂

theorem agreeKept {s₁ s₂ : State} (h : EqKept s₁ s₂) :
    VG.X86.Taint.Agree (τr kept) s₁ s₂ := agree_regs h

theorem before_ok (d : Spec.Rc2.Direction) (s : State) (hp : StepPre s) :
    WP isa (.block (Impl.Rc2.X86.Cbc.before d)) s (fun s' => StepPre s' ∧ ∀ r ∈ kept, s'.gpr r = s.gpr r) := by
  have sep : ∀ r ∈ kept, r ∉ temps := by decide
  cases d
  · apply WP.mono (xor64_ok s .esi .ecx (by decide) (by decide)
      (by simpa using hp.dataFit) hp.ivFit hp.readData hp.readIv hp.writeData)
    intro s' h
    exact ⟨hp.keep h, fun r hr => h.reg r (sep r hr)⟩
  · apply WP.mono (copy64_ok s .esi .ebp 0 256 (by decide) (by decide)
      (by simpa using hp.dataFit) (by have := hp.bufFit; omega_using [this])
      (by simpa using hp.readData) (hp.writeBuf 256 (by decide)))
    intro s' h
    exact ⟨hp.keep h, fun r hr => h.reg r (sep r hr)⟩

theorem kept_ct {c : Prog isa} (h : RelCT isa StepRel c (fun _ _ => True))
    (correct : ∀ s, StepPre s → WP isa c s (fun s' => StepPre s' ∧ ∀ r ∈ kept, s'.gpr r = s.gpr r)) :
    RelCT isa StepRel c StepRel := by
  apply (h.wpDep (fun s₁ s₂ hp => ⟨correct s₁ hp.1, correct s₂ hp.2.1⟩)).mono
    (fun _ _ h => h)
  rintro s₁' s₂' ⟨_, s₁, s₂, hp, h₁, h₂⟩
  refine ⟨h₁.1, h₂.1, fun r hr => ?_⟩
  rw [h₁.2 r hr, h₂.2 r hr]
  exact hp.2.2 r hr

theorem before_ct (d : Spec.Rc2.Direction) :
    RelCT isa StepRel (.block (Impl.Rc2.X86.Cbc.before d)) StepRel := by
  apply kept_ct _ (before_ok d)
  cases d <;> apply RelCT.taint (A := taint) (τr kept) (fun _ _ h => agreeKept h.2.2)
  all_goals taint_decide

def callRd (s : State) : List Region :=
  [⟨addr32 (s.gpr .ebx), 128⟩, ⟨argAddr (pushed [.ebp, .esi, .ebx] s).callEntry 0, 12⟩]
def callWr (s : State) : List Region := [⟨addr32 (s.gpr .esi), 8⟩, ⟨addr32 (s.gpr .ebp), 256⟩]

theorem callPre_ok (d : Spec.Rc2.Direction) (s : State) (hp : CallPre s) :
    VG.X86.CallPre (blockContract d) [.ebp, .esi, .ebx] (callRd s) (callWr s) s := by
  let rs : List Reg := [.ebp, .esi, .ebx]
  have hrs : .esp ∉ rs := by decide
  have fit : 4 * rs.length + 4 ≤ (s.gpr .esp).toNat := hp.stackLo
  let sE := (pushed rs s).callEntry
  have a0 : arg sE 0 = s.gpr .ebx := by rw [callEntry_arg fit hrs (by decide)]; rfl
  have a1 : arg sE 1 = s.gpr .esi := by rw [callEntry_arg fit hrs (by decide)]; rfl
  have a2 : arg sE 2 = s.gpr .ebp := by rw [callEntry_arg fit hrs (by decide)]; rfl
  have eA : argAddr sE 0 = ((s.gpr .esp) - BitVec.ofNat 32 12).setWidth 64 := by rw [callEntry_argAddr0]; rfl
  have eSp : sE.gpr .esp = s.gpr .esp - BitVec.ofNat 32 16 := by rw [callEntry_esp']; rfl
  have b12 : Region.Sub (below (s.gpr .esp) 12) (below (s.gpr .esp) 16) := below_sub (by decide) hp.stackLo
  have r4 : Region.Sub ⟨((s.gpr .esp) - BitVec.ofNat 32 16).setWidth 64, 4⟩ (below (s.gpr .esp) 16) :=
    Region.sub_prefix (by decide)
  unfold callRd callWr
  refine ⟨?_, ?_, ?_⟩
  · change (blockContract d).pre (sE.withRegions _ _)
    simp only [blockContract, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, eA, eSp]
    refine ⟨?_, trivial, hp.keyScratch, hp.dataScratch, hp.stackData.sub_left b12,
      hp.stackBuf.sub_left b12, hp.stackData.sub_left r4, hp.stackBuf.sub_left r4,
      hp.keyFit, hp.dataFit, hp.bufFit, ?_⟩
    · rw [callEntry_argAddr0]; rfl
    rw [sub_toNat hp.stackLo]
    have := (s.gpr .esp).isLt
    omega_using []
  · intro a n ⟨r, hr, hc⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact InRegions_append_cons.mpr (.inr (hp.reads a n ⟨_, by simp, hc⟩))
    · apply InRegions_append_cons.mpr
      left
      rw [eA] at hc
      exact hc
    · exact InRegions_append_cons.mpr (.inr (hp.reads a n ⟨_, by simp, hc⟩))
    · exact InRegions_append_cons.mpr (.inr (hp.reads a n ⟨_, by simp, hc⟩))
  · intro a n h
    obtain ⟨r, hr, hc⟩ := hp.writes a n h
    exact ⟨r, List.mem_cons_of_mem _ hr, hc⟩

theorem call_ct (d : Spec.Rc2.Direction) : RelCT isa StepRel (Impl.Rc2.X86.Cbc.blockCall d) StepRel := by
  apply kept_ct
  · intro s₁ s₂ t₁ t₂ u₁ u₂ hp e₁ e₂
    have sp := hp.2.2 .esp (by decide)
    have key := hp.2.2 .ebx (by decide)
    have data := hp.2.2 .esi (by decide)
    have buf := hp.2.2 .ebp (by decide)
    have rd : callRd s₂ = callRd s₁ := by
      simp only [callRd, callEntry_argAddr0, key, sp]
    have wr : callWr s₂ = callWr s₁ := by simp only [callWr, data, buf]
    have hc : ConstantTime isa (blockContract d).pre (blockContract d).pub (.block (blockCode d)) := by
      cases d
      · exact encryptBlock_constantTime
      · exact decryptBlock_constantTime
    have ct : RelCT isa (fun a b => a = s₁ ∧ b = s₂) (Impl.Rc2.X86.Cbc.blockCall d) (fun _ _ => True) := by
      rw [blockCall_eq]
      apply RelCT.callWith (block_correct d) hc (callRd s₁) (callWr s₁)
      rintro a b ⟨ha, hb⟩
      subst a b
      refine ⟨callPre_ok d s₁ hp.1.call, ?_, sp, ?_⟩
      · rw [← rd, ← wr]; exact callPre_ok d s₂ hp.2.1.call
      · constructor
        · simp only [State.withRegions_gpr, callEntry_esp', sp]
        · intro i hi
          simp only [arg_withRegions]
          rw [callEntry_arg (by exact hp.1.stackLo) (by decide) (by simpa using hi),
            callEntry_arg (by exact hp.2.1.stackLo) (by decide) (by simpa using hi)]
          have cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega_using [hi]
          rcases cases with rfl | rfl | rfl
          · exact key
          · exact data
          · exact buf
    exact ct _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂
  · intro s hp
    apply WP.mono (call_ok d s hp.call)
    intro s' h
    exact ⟨hp.transport h.rd h.wr h.reg, h.reg⟩

theorem after_ct (d : Spec.Rc2.Direction) :
    RelCT isa StepRel (.block (Impl.Rc2.X86.Cbc.after d)) (fun _ _ => True) := by
  cases d <;> apply RelCT.taint (A := taint) (τr kept) (fun _ _ h => agreeKept h.2.2)
  all_goals taint_decide

theorem step_ct (d : Spec.Rc2.Direction) :
    RelCT isa StepRel (Impl.Rc2.X86.Cbc.step d) StepRel := by
  apply kept_ct ((before_ct d).seq ((call_ct d).seq (after_ct d)))
  intro s hp
  apply WP.mono (step_ok d s hp)
  intro s' h
  exact ⟨h.toPinned.pre hp, h.reg⟩

theorem body_ct (d : Spec.Rc2.Direction) :
    RelCT isa StepRel (Impl.Rc2.X86.Cbc.body d) (fun _ _ => True) := by
  apply (step_ct d).seq
  apply RelCT.taint (A := taint) (τr kept) (fun _ _ h => agreeKept h.2.2)
  taint_decide

end VG.Proof.Rc2.X86.Cbc

end

section

/-! # Constant-time CBC loops -/

namespace VG.Proof.Rc2.X86.Cbc

open VG VG.X86 VG.Impl.Rc2.X86

def LoopRel (n : Nat) (s₁ s₂ : State) : Prop :=
  StepPre s₁ n ∧ StepPre s₂ n ∧ EqKept s₁ s₂ ∧
    s₁.gpr .edi = BitVec.ofNat 32 n ∧ s₂.gpr .edi = BitVec.ofNat 32 n ∧ 1 ≤ n

theorem bodyRel (d : Spec.Rc2.Direction) (n : Nat) :
    RelCT isa (LoopRel n) (Impl.Rc2.X86.Cbc.body d) (fun s₁ s₂ =>
      EqKept s₁ s₂ ∧ eval .ne s₁ = eval .ne s₂ ∧
        (eval .ne s₁ = some true → ∃ m < n, LoopRel m s₁ s₂)) := by
  have ct : RelCT isa (LoopRel n) (Impl.Rc2.X86.Cbc.body d) (fun _ _ => True) :=
    (body_ct d).mono (fun _ _ h => ⟨h.1.head h.2.2.2.2.2, h.2.1.head h.2.2.2.2.2, h.2.2.1⟩)
      (fun _ _ _ => trivial)
  have correct (s₁ s₂ : State) (h : LoopRel n s₁ s₂) :=
    And.intro (body_ok d s₁ n h.2.2.2.2.2 (by have := h.1.dataFit; omega_using [this]) h.2.2.2.1 (h.1.head h.2.2.2.2.2))
      (body_ok d s₂ n h.2.2.2.2.2 (by have := h.2.1.dataFit; omega_using [this]) h.2.2.2.2.1 (h.2.1.head h.2.2.2.2.2))
  apply (ct.wpDep correct).mono (fun _ _ h => h)
  rintro s₁' s₂' ⟨_, s₁, s₂, hp, h₁, h₂⟩
  have eq : EqKept s₁' s₂' := by
    intro r hr
    by_cases hptr : r = .esi
    · subst r; rw [h₁.ptr, h₂.ptr, hp.2.2.1 .esi (by decide)]
    · by_cases hcount : r = .edi
      · subst r; rw [h₁.count, h₂.count]
      · rw [h₁.reg r hr hptr hcount, h₂.reg r hr hptr hcount]
        exact hp.2.2.1 r hr
  refine ⟨eq, by rw [eval_nonzeroCount, eval_nonzeroCount, h₁.flag, h₂.flag], ?_⟩
  intro hcontinue
  have hn : 1 ≤ n := hp.2.2.2.2.2
  have hm : 1 ≤ n - 1 := by
    rw [eval_nonzeroCount, h₁.flag] at hcontinue
    by_contra h
    have e : n = 1 := by omega_using [hn, h]
    simp only [e, decide_true, Option.map_some, Bool.not_true, Option.some.injEq, Bool.false_eq_true] at hcontinue
  refine ⟨n - 1, by omega_using [hn], ?_, ?_, eq, h₁.count, h₂.count, hm⟩
  · have e : n = (n - 1) + 1 := by omega_using [hn]
    rw [e] at h₁ hp
    exact h₁.tail hp.1 hm
  · have e : n = (n - 1) + 1 := by omega_using [hn]
    rw [e] at h₂ hp
    exact h₂.tail hp.2.1 hm

theorem loop_ct (d : Spec.Rc2.Direction) (n : Nat) :
    RelCT isa (LoopRel n) (.loop (Impl.Rc2.X86.Cbc.body d) .ne) EqKept := by
  refine RelCT.loop (M := isa) (body := Impl.Rc2.X86.Cbc.body d) (c := .ne) (Q := EqKept) LoopRel ?_ n
  intro m
  exact (bodyRel d m).mono (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, fun _ => h.1, h.2.2⟩)

def MaybeRel (s₁ s₂ : State) : Prop :=
  ∃ n, StepPre s₁ n ∧ StepPre s₂ n ∧ EqKept s₁ s₂ ∧
    s₁.gpr .edi = BitVec.ofNat 32 n ∧ s₂.gpr .edi = BitVec.ofNat 32 n ∧
    zeroCount s₁ = some (decide (n = 0)) ∧ zeroCount s₂ = some (decide (n = 0))

theorem maybeLoop_ct (d : Spec.Rc2.Direction) :
    RelCT isa MaybeRel (.ite .e (.block []) (.loop (Impl.Rc2.X86.Cbc.body d) .ne)) EqKept := by
  apply RelCT.ite
  · rintro s₁ s₂ ⟨n, _, _, _, _, _, h₁, h₂⟩
    change zeroCount s₁ = zeroCount s₂
    rw [h₁, h₂]
  · apply RelCT.nil
    rintro s₁ s₂ ⟨⟨n, _, _, eq, _⟩, _⟩
    exact eq
  · apply RelCT.exists_ (fun n => loop_ct d n) |>.mono
    · rintro s₁ s₂ ⟨⟨n, h₁, h₂, eq, c₁, c₂, z₁, _⟩, branch⟩
      refine ⟨n, h₁, h₂, eq, c₁, c₂, ?_⟩
      change zeroCount s₁ = some false at branch
      rw [z₁] at branch
      have hn : n ≠ 0 := by intro hz; simp [hz] at branch
      omega_using [hn]
    · exact fun _ _ h => h

end VG.Proof.Rc2.X86.Cbc

end

namespace VG.Proof.Rc2.X86.Cbc
open VG VG.X86 VG.Impl.Rc2.X86

def startCode : Prog isa := .seq (.block [.mov .eax (.mem (memOp .esp 20))])
  (.block (Impl.Rc2.X86.Cbc.save ++ Impl.Rc2.X86.Cbc.setup))

structure StartPost (s s' : State) : Prop where
  pre : StepPre s' (arg s 3).toNat
  key : s'.gpr .ebx = arg s 0
  iv : s'.gpr .ecx = arg s 1
  data : s'.gpr .esi = arg s 2
  buf : s'.gpr .ebp = arg s 4
  count : s'.gpr .edi = arg s 3
  flag : zeroCount s' = some (arg s 3 == 0)
  sp : s'.gpr .esp = s.gpr .esp

theorem start_ok (d : Spec.Rc2.Direction) (s : State) (hs : (contract d).pre s) :
    WP isa startCode s (StartPost s) := by
  obtain ⟨hrd, hwr, keyIv, keyData, keyBuf, ivData, ivBuf, dataBuf,
    ivArgs, dataArgs, bufArgs, retIv, retData, retBuf, stackKey, stackIv, stackData, stackBuf, keyFit, ivFit, bufFit, spFit, stackLo, fit⟩ := hs
  have writes (i : Nat) (hi : i + 4 ≤ 512) : InRegions s.wr (addr32 (arg s 4) + BitVec.ofNat 64 i) 4 := by
    rw [hwr]
    exact ⟨⟨addr32 (arg s 4), 512⟩, by simp, Offset.contains_base _ hi (by omega_using [hi])⟩
  rw [startCode]
  apply WP.seq
  obtain ⟨s₀, run₀, buf₀, keep₀⟩ := loadArg_ok s .eax 4 (by
    rw [hrd, hwr, argAddr_eq s 4 (by omega_using [spFit])]
    exact ⟨⟨argAddr s 0, 20⟩, by simp, argContains s spFit 4 (by decide)⟩)
  refine WP.of_runBlock ⟨s₀, run₀, ?_⟩
  have g₀ (r : Reg) (hr : r ≠ .eax) := keep₀.reg r (by simpa using hr)
  have writes₀ (i : Nat) (hi : i + 4 ≤ 512) :
      InRegions s₀.wr (addr32 (s₀.gpr .eax) + BitVec.ofNat 64 i) 4 := by
    rw [keep₀.wr, buf₀]; exact writes i hi
  rw [WP.block_append_iff]
  obtain ⟨s₁, run₁, keep₁⟩ := save_ok s₀ (by rw [buf₀]; exact bufFit)
    (writes₀ 264 (by decide)) (writes₀ 268 (by decide)) (writes₀ 272 (by decide))
    (writes₀ 276 (by decide))
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have g₁ (r : Reg) : s₁.gpr r = s₀.gpr r := keep₁.reg r (by simp)
  have sp₁ : s₁.gpr .esp = s.gpr .esp := (g₁ .esp).trans (g₀ .esp (by decide))
  have saveFrame : Frame [⟨addr32 (arg s 4), 512⟩] s.mem s₁.mem := by
    rw [keep₁.mem, ← keep₀.mem, ← buf₀]; exact savedMem_frame s₀
  have args₁ := args_frame saveFrame sp₁ spFit (by simpa using bufArgs)
  have readArgs₁ (i : Nat) (hi : i < 4) : InRegions (s₁.rd ++ s₁.wr) (argAddr s₁ i) 4 := by
    have ptr : argAddr s₁ i = argAddr s i := by unfold argAddr; rw [sp₁]
    rw [keep₁.rd, keep₁.wr, keep₀.rd, keep₀.wr, hrd, hwr, ptr, argAddr_eq s i (by omega_using [spFit, hi])]
    exact ⟨⟨argAddr s 0, 20⟩, by simp, argContains s spFit i (by omega_using [hi])⟩
  obtain ⟨s₂, run₂, key₂, iv₂, data₂, count₂, buf₂, flag₂, keep₂⟩ := setup_ok s₁ readArgs₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  rw [args₁ 0 (by decide)] at key₂
  rw [args₁ 1 (by decide)] at iv₂
  rw [args₁ 2 (by decide)] at data₂
  rw [args₁ 3 (by decide)] at count₂ flag₂
  rw [g₁, buf₀] at buf₂
  have sp₂ := (keep₂.reg .esp (by decide)).trans sp₁
  have rd₂ := keep₂.rd.trans (keep₁.rd.trans keep₀.rd)
  have wr₂ := keep₂.wr.trans (keep₁.wr.trans keep₀.wr)
  have hp₂ : StepPre s₂ (arg s 3).toNat := by
    constructor
    · rw [key₂]; exact keyFit
    · rw [iv₂]; exact ivFit
    · rw [data₂]; exact fit
    · rw [buf₂]; exact bufFit
    · simp only [Covers, keyR, ivR, dataR, bufR, key₂, iv₂, data₂, buf₂, rd₂, wr₂, hrd, hwr]
      intro a n ⟨r, hr, hc⟩
      exact ⟨r, by simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h | h <;> simp_all only [or_true, true_or], hc⟩
    · simp only [Covers, ivR, dataR, bufR, iv₂, data₂, buf₂, wr₂, hwr]
      intro a n ⟨r, hr, hc⟩
      exact ⟨r, hr, hc⟩
    · simpa only [keyR, ivR, key₂, iv₂] using keyIv
    · simpa only [keyR, dataR, key₂, data₂] using keyData
    · simpa only [keyR, bufR, key₂, buf₂] using keyBuf
    · simpa only [ivR, dataR, iv₂, data₂] using ivData
    · simpa only [ivR, bufR, iv₂, buf₂] using ivBuf
    · simpa only [dataR, bufR, data₂, buf₂] using dataBuf
    · rw [sp₂]; exact stackLo
    · simpa only [stackR, keyR, sp₂, key₂] using stackKey
    · simpa only [stackR, ivR, sp₂, iv₂] using stackIv
    · simpa only [stackR, dataR, sp₂, data₂] using stackData
    · simpa only [stackR, bufR, sp₂, buf₂] using stackBuf
  exact ⟨hp₂, key₂, iv₂, data₂, buf₂, count₂, flag₂, sp₂⟩

def InitialRel (d : Spec.Rc2.Direction) (s₁ s₂ : State) : Prop :=
  (contract d).pre s₁ ∧ (contract d).pre s₂ ∧ (contract d).pub s₁ s₂

def startTaint : VG.X86.Taint.T := { regs := .ofList [.esp], flags := false, argLen := 24 }

theorem startTaint_wf {d : Spec.Rc2.Direction} {s : State} (h : (contract d).pre s) : VG.X86.Taint.Wf startTaint s := by
  obtain ⟨_, wr, _, _, _, _, _, _, ai, ad, ab, ri, rd, rb, _, _, _, _, _, _, _, spfit, _⟩ := h
  refine Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨spfit, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim⟩
  simp only [startTaint, wr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact Taint.frame_disjoint (n := 20) (by omega_using [spfit]) ri ai
  · exact Taint.frame_disjoint (n := 20) (by omega_using [spfit]) rd ad
  · exact Taint.frame_disjoint (n := 20) (by omega_using [spfit]) rb ab

theorem startTaint_agree {d : Spec.Rc2.Direction} {s₁ s₂ : State} (h : InitialRel d s₁ s₂) :
    VG.X86.Taint.Agree startTaint s₁ s₂ := by
  obtain ⟨h₁, h₂, sp, args⟩ := h
  have fit : ∀ s, (contract d).pre s → (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 := by
    intro s hs
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h, _⟩ := hs
    exact h
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h,
    startTaint_wf h₁, startTaint_wf h₂, VG.X86.Taint.slotsOk_empty,
    VG.X86.Taint.slotsAgree_empty, fun _ => sp, fun k h4 hk => ?_⟩
  · simp only [startTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r; exact sp
  · simp only [startTaint] at hk
    rw [show Taint.depth startTaint.stk = 0 from rfl, Nat.zero_add]
    rw [Taint.argByte_eq (fit _ h₁) h4 hk, Taint.argByte_eq (fit _ h₂) h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)),
      Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (args ((k - 4) / 4) (by omega_using [hk]))

theorem start_ct (d : Spec.Rc2.Direction) : RelCT isa (InitialRel d) startCode MaybeRel := by
  have ct : RelCT isa (InitialRel d) startCode (fun _ _ => True) := by
    apply RelCT.taint (A := taint) startTaint (fun _ _ h => startTaint_agree h)
    taint_decide
  apply (ct.wpDep (fun s₁ s₂ h => ⟨start_ok d s₁ h.1, start_ok d s₂ h.2.1⟩)).mono (fun _ _ h => h)
  rintro s₁' s₂' ⟨_, s₁, s₂, hp, h₁, h₂⟩
  obtain ⟨sp, args⟩ := hp.2.2
  have p0 := args 0 (by decide)
  have p1 := args 1 (by decide)
  have p2 := args 2 (by decide)
  have p3 := args 3 (by decide)
  have bp := args 4 (by decide)
  refine ⟨(arg s₁ 3).toNat, h₁.pre, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [p3]; exact h₂.pre
  · intro r hr
    simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h₁.key, h₂.key, p0]
    · rw [h₁.iv, h₂.iv, p1]
    · rw [h₁.data, h₂.data, p2]
    · rw [h₁.count, h₂.count, p3]
    · rw [h₁.buf, h₂.buf, bp]
    · rw [h₁.sp, h₂.sp, sp]
  · simpa using h₁.count
  · rw [p3]; simpa using h₂.count
  · rw [h₁.flag]
    apply congrArg some
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    constructor
    · intro h; rw [h]; rfl
    · intro h; exact BitVec.eq_of_toNat_eq h
  · rw [h₂.flag, p3]
    apply congrArg some
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    constructor
    · intro h; rw [h]; rfl
    · intro h; exact BitVec.eq_of_toNat_eq h

end VG.Proof.Rc2.X86.Cbc

end

/-! # Constant-time CBC callers -/

namespace VG.Proof.Rc2.X86.Cbc

open VG VG.X86

theorem cbc_constantTime (d : Spec.Rc2.Direction) :
    ConstantTime isa (contract d).pre (contract d).pub (Impl.Rc2.X86.Cbc.cbc d) := by
  apply RelCT.constantTime
  apply RelCT.assoc
  apply (start_ct d).seq
  apply (maybeLoop_ct d).seq
  apply RelCT.taint (A := taint) (τr [.ebp])
    (fun _ _ h => agree_regs (fun r hr => h r (by have e := List.mem_singleton.mp hr; rw [e]; decide)))
  taint_decide

end VG.Proof.Rc2.X86.Cbc

end

end

/-! # Verified RC2-CBC encryption and decryption -/

@[expose] public section

namespace VG.Proof.Rc2.X86.Cbc

open VG VG.X86 VG.Impl.Rc2.X86

theorem cbc_body_correct (d : Spec.Rc2.Direction) (s : State) (hs : (contract d).pre s) :
    WP isa (Impl.Rc2.X86.Cbc.cbc d) s (fun s' => abiPreserved s s' ∧ (contract d).post s s') := by
  obtain ⟨hrd, hwr, keyIv, keyData, keyBuf, ivData, ivBuf, dataBuf,
    ivArgs, dataArgs, bufArgs, retIv, retData, retBuf, stackKey, stackIv, stackData, stackBuf, keyFit, ivFit, bufFit, spFit, stackLo, fit⟩ := hs
  have writes (i : Nat) (hi : i + 4 ≤ 512) : InRegions s.wr (addr32 (arg s 4) + BitVec.ofNat 64 i) 4 := by
    rw [hwr]
    exact ⟨⟨addr32 (arg s 4), 512⟩, by simp, Offset.contains_base _ hi (by omega_arith)⟩
  rw [Impl.Rc2.X86.Cbc.cbc]
  apply WP.seq
  obtain ⟨s₀, run₀, buf₀, keep₀⟩ := loadArg_ok s .eax 4 (by
    rw [hrd, hwr, argAddr_eq s 4 (by omega_arith)]
    exact ⟨⟨argAddr s 0, 20⟩, by simp, argContains s spFit 4 (by decide)⟩)
  refine WP.of_runBlock ⟨s₀, run₀, ?_⟩
  have g₀ (r : Reg) (hr : r ≠ .eax) := keep₀.reg r (by simpa using hr)
  have writes₀ (i : Nat) (hi : i + 4 ≤ 512) :
      InRegions s₀.wr (addr32 (s₀.gpr .eax) + BitVec.ofNat 64 i) 4 := by
    rw [keep₀.wr, buf₀]; exact writes i hi
  apply WP.seq
  rw [WP.block_append_iff]
  obtain ⟨s₁, run₁, keep₁⟩ := save_ok s₀ (by rw [buf₀]; exact bufFit)
    (writes₀ 264 (by decide)) (writes₀ 268 (by decide)) (writes₀ 272 (by decide))
    (writes₀ 276 (by decide))
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have g₁ (r : Reg) : s₁.gpr r = s₀.gpr r := keep₁.reg r (by simp)
  obtain sp₁ : s₁.gpr .esp = s.gpr .esp := (g₁ .esp).trans (g₀ .esp (by decide))
  obtain saveFrame : Frame [⟨addr32 (arg s 4), 512⟩] s.mem s₁.mem := by
    rw [keep₁.mem, ← keep₀.mem, ← buf₀]; exact savedMem_frame s₀
  obtain args₁ := args_frame saveFrame sp₁ spFit (by simpa using bufArgs)
  have readArgs₁ (i : Nat) (hi : i < 4) : InRegions (s₁.rd ++ s₁.wr) (argAddr s₁ i) 4 := by
    obtain ptr : argAddr s₁ i = argAddr s i := by unfold argAddr; rw [sp₁]
    rw [keep₁.rd, keep₁.wr, keep₀.rd, keep₀.wr, hrd, hwr, ptr, argAddr_eq s i (by omega_arith)]
    exact ⟨⟨argAddr s 0, 20⟩, by simp, argContains s spFit i (by omega_arith)⟩
  obtain ⟨s₂, run₂, key₂, iv₂, data₂, count₂, buf₂, flag₂, keep₂⟩ := setup_ok s₁ readArgs₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  rw [args₁ 0 (by decide)] at key₂
  rw [args₁ 1 (by decide)] at iv₂
  rw [args₁ 2 (by decide)] at data₂
  rw [args₁ 3 (by decide)] at count₂ flag₂
  rw [g₁, buf₀] at buf₂
  obtain sp₂ := (keep₂.reg .esp (by decide)).trans sp₁
  obtain rd₂ := keep₂.rd.trans (keep₁.rd.trans keep₀.rd)
  obtain wr₂ := keep₂.wr.trans (keep₁.wr.trans keep₀.wr)
  obtain mem₂ : s₂.mem = savedMem s₀ := keep₂.mem.trans keep₁.mem
  obtain scratchFrame : Frame [⟨addr32 (arg s 4), 512⟩] s.mem s₂.mem := by
    rw [mem₂, ← keep₀.mem, ← buf₀]; exact savedMem_frame s₀
  obtain initialKey := scheduleAt_frame scratchFrame (addr32 (arg s 0)) (by simpa using keyBuf)
  obtain initialIv := blockAt_frame scratchFrame (addr32 (arg s 1)) (by simpa using ivBuf)
  obtain initialData := blocksAt_frame scratchFrame (addr32 (arg s 2)) (arg s 3).toNat (by simpa using dataBuf)
  obtain hp₂ : StepPre s₂ (arg s 3).toNat := by
    constructor
    · rw [key₂]; exact keyFit
    · rw [iv₂]; exact ivFit
    · rw [data₂]; exact fit
    · rw [buf₂]; exact bufFit
    · simp only [Covers, keyR, ivR, dataR, bufR, key₂, iv₂, data₂, buf₂, rd₂, wr₂, hrd, hwr]
      intro a n ⟨r, hr, hc⟩
      exact ⟨r, by simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h | h <;> simp_all only [or_true, true_or], hc⟩
    · simp only [Covers, ivR, dataR, bufR, iv₂, data₂, buf₂, wr₂, hwr]
      intro a n ⟨r, hr, hc⟩
      exact ⟨r, hr, hc⟩
    · simpa only [keyR, ivR, key₂, iv₂] using keyIv
    · simpa only [keyR, dataR, key₂, data₂] using keyData
    · simpa only [keyR, bufR, key₂, buf₂] using keyBuf
    · simpa only [ivR, dataR, iv₂, data₂] using ivData
    · simpa only [ivR, bufR, iv₂, buf₂] using ivBuf
    · simpa only [dataR, bufR, data₂, buf₂] using dataBuf
    · rw [sp₂]; exact stackLo
    · simpa only [stackR, keyR, sp₂, key₂] using stackKey
    · simpa only [stackR, ivR, sp₂, iv₂] using stackIv
    · simpa only [stackR, dataR, sp₂, data₂] using stackData
    · simpa only [stackR, bufR, sp₂, buf₂] using stackBuf
  apply WP.seq
  apply WP.mono (maybeLoop_ok d s₂ (arg s 3).toNat (by omega_arith) hp₂
    (by simpa using count₂) (by rw [count₂]; exact flag₂))
  intro s₃ h₃
  obtain rd₃ := h₃.rd.trans rd₂
  obtain wr₃ := h₃.wr.trans wr₂
  obtain buf₃ := (h₃.reg .ebp (by decide) (by decide) (by decide)).trans buf₂
  have reads (i : Nat) (hi : i + 4 ≤ 512) :
      InRegions (s₃.rd ++ s₃.wr) (addr32 (s₃.gpr .ebp) + BitVec.ofNat 64 i) 4 := by
    rw [rd₃, wr₃, buf₃]
    obtain ⟨r, hr, hc⟩ := writes i hi
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  obtain v0 : s₃.mem.readW (addr32 (s₃.gpr .ebp) + BitVec.ofNat 64 264) 32 = s.gpr .ebp := by
    obtain h := h₃.scratchRead hp₂ 264 (by decide) (by decide)
    rw [buf₂, mem₂, ← buf₀, savedMem_ebp, g₀ .ebp (by decide)] at h
    rw [buf₀] at h
    rw [buf₃]; exact h
  obtain v1 : s₃.mem.readW (addr32 (s₃.gpr .ebp) + BitVec.ofNat 64 268) 32 = s.gpr .ebx := by
    obtain h := h₃.scratchRead hp₂ 268 (by decide) (by decide)
    rw [buf₂, mem₂, ← buf₀, savedMem_ebx, g₀ .ebx (by decide)] at h
    rw [buf₀] at h
    rw [buf₃]; exact h
  obtain v2 : s₃.mem.readW (addr32 (s₃.gpr .ebp) + BitVec.ofNat 64 272) 32 = s.gpr .esi := by
    obtain h := h₃.scratchRead hp₂ 272 (by decide) (by decide)
    rw [buf₂, mem₂, ← buf₀, savedMem_esi, g₀ .esi (by decide)] at h
    rw [buf₀] at h
    rw [buf₃]; exact h
  obtain v3 : s₃.mem.readW (addr32 (s₃.gpr .ebp) + BitVec.ofNat 64 276) 32 = s.gpr .edi := by
    obtain h := h₃.scratchRead hp₂ 276 (by decide) (by decide)
    rw [buf₂, mem₂, ← buf₀, savedMem_edi, g₀ .edi (by decide)] at h
    rw [buf₀] at h
    rw [buf₃]; exact h
  obtain ⟨s₄, run₄, saved₄, keep₄⟩ := restore_ok s₃ s.gpr (by rw [buf₃]; exact bufFit)
    (reads 264 (by decide)) v0    (reads 268 (by decide)) v1    (reads 272 (by decide)) v2    (reads 276 (by decide)) v3
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  constructor
  · constructor
    · intro r hr
      by_cases saved : r ∈ callerSaved
      · exact saved₄ r saved
      · have eqSp : r = .esp := by cases r <;> simp_all [calleeSaved, callerSaved]
        subst r
        rw [keep₄.reg .esp (by decide), h₃.reg .esp (by decide) (by decide) (by decide), sp₂]
    · have stackRet : (Region.mk (addr32 (s.gpr .esp)) 4).Disjoint (below (s.gpr .esp) 16) := by
        change (Region.mk (addr32 (s.gpr .esp)) 4).Disjoint ⟨_, 16⟩
        rw [Taint.sub_setWidth stackLo]
        exact Offset.base_disjoint_below _ (by decide)
      have frameLoop := h₃.mem
      obtain retSep : ∀ r ∈ loopWrites s₂ (arg s 3).toNat, (Region.mk (addr32 (s.gpr .esp)) 4).Disjoint r := by
        simpa only [loopWrites, ivR, dataR, stackR, iv₂, data₂, buf₂, sp₂,
          List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
          And.intro retIv (And.intro retData (And.intro (retBuf.sub_right (Region.sub_prefix (by decide : 264 ≤ 512))) stackRet))
      change s₄.mem.readW (addr32 (s.gpr .esp)) 32 = s.mem.readW (addr32 (s.gpr .esp)) 32
      rw [keep₄.mem, frameLoop.readW (Region.contains_self _ _) retSep (by decide),
        scratchFrame.readW (Region.contains_self _ _) (by simpa using retBuf) (by decide)]
  · have out := h₃.data
    have iv := h₃.iv
    rw [key₂, iv₂, data₂, initialKey, initialIv, initialData] at out iv
    constructor
    · rw [keep₄.mem]; exact out
    · rw [keep₄.mem]; exact iv

end VG.Proof.Rc2.X86.Cbc
