module

public import VerifiedGarbage.Proof.Rc2.X86_64.Save
public import VerifiedGarbage.Proof.Rc2.X86_64.ConstantTime
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Spec.Rc2.Contract
public import VerifiedGarbage.Proof.Rc2.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Rc2.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
public import VerifiedGarbage.Impl.Rc2.X86_64.Cbc
public import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-! ### `Rc2.X86_64.Block`, which only this module used -/

section

/-! # Verified RC2 block encryption and decryption -/

@[expose] public section

namespace VG.Proof.Rc2.X86_64

open VG VG.X86_64 VG.Impl.Rc2.X86_64

def cipher (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (b : Spec.Rc2.Block) : Spec.Rc2.Block :=
  match d with
  | .encrypt => Spec.Rc2.encryptBlock k b
  | .decrypt => Spec.Rc2.decryptBlock k b

def blockContract (d : Spec.Rc2.Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, 128⟩
    let data : Region := ⟨s.gpr .rsi, 8⟩
    let scratch : Region := ⟨s.gpr .rdx, 256⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [key] ∧ s.wr = [data, scratch] ∧ key.Disjoint scratch ∧ data.Disjoint scratch ∧
      ret.Disjoint data ∧ ret.Disjoint scratch
  post s s' := Spec.Rc2.blockAt s'.mem (s.gpr .rsi) =
    cipher d (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)) (Spec.Rc2.blockAt s.mem (s.gpr .rsi))
  pub := PublicRegs [.rdi, .rsi, .rdx]

theorem cipher_rounds (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (b : Spec.Rc2.Block) :
    cipher d k b = Spec.Rc2.encodeBlock
      ((List.range 16).foldl (fun v j => roundSpec d k j v) (Spec.Rc2.decodeBlock b)) := by
  cases d <;> rfl

theorem block_correct (d : Spec.Rc2.Direction) (s : State) (hs : (blockContract d).pre s) :
    WP isa (.block (blockCode d)) s (fun s' => gprPreserved s s' ∧ (blockContract d).post s s') := by
  obtain ⟨hrd, hwr, keySep, dataSep, retData, retScratch⟩ := hs
  have writes : ∀ i < 4, InRegions s.wr (s.gpr .rdx + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi
    rw [hwr]
    exact ⟨⟨s.gpr .rdx, 256⟩, by simp, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  simp only [blockCode, List.append_assoc]
  rw [WP.block_append_iff]
  apply WP.mono (saveCode_ok s .rdx wordReg 4 writes)
  intro s₁ h₁
  have scratchFrame : Frame [⟨s.gpr .rdx, 256⟩] s.mem s₁.mem := by
    rw [h₁.2.2.2]
    exact saveMem_frame_le _ _ _ 4 32 (by decide) (by decide)
  have input₁ : Spec.Rc2.blockAt s₁.mem (s₁.gpr .rsi) = Spec.Rc2.blockAt s.mem (s.gpr .rsi) := by
    rw [h₁.1]
    exact blockAt_frame scratchFrame _ (by simpa using dataSep)
  have schedule₁ : Spec.Rc2.scheduleAt s₁.mem (s₁.gpr .rdi) =
      Spec.Rc2.scheduleAt s.mem (s.gpr .rdi) := by
    rw [h₁.1]
    exact scheduleAt_frame scratchFrame _ (by simpa using keySep)
  have dataRead₁ : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rsi) 8 := by
    rw [h₁.1, h₁.2.1, h₁.2.2.1, hrd, hwr]
    exact ⟨⟨s.gpr .rsi, 8⟩, by simp, Region.contains_self _ _⟩
  rw [WP.block_append_iff]
  apply WP.mono (blockLoad_ok s₁ dataRead₁)
  intro s₂ h₂
  have read₂ : ∀ i < 128, InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .rdi + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [h₂.2.rd, h₂.2.wr, h₂.2.reg .rdi (by decide), h₁.1, h₁.2.1, h₁.2.2.1, hrd, hwr]
    exact ⟨⟨s.gpr .rdi, 128⟩, by simp, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  have scans₂ : ScanMemory s₂ := by
    refine ⟨read₂, ?_, ?_⟩
    · intro i hi
      rw [h₂.2.rd, h₂.2.wr, h₂.2.reg .rdi (by decide), h₁.1, h₁.2.1, h₁.2.2.1, hrd, hwr]
      exact ⟨⟨s.gpr .rdi, 128⟩, by simp, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
    · rw [h₂.2.wr, h₂.2.reg .rdx (by decide), h₁.1, h₁.2.2.1, hwr]
      exact ⟨⟨s.gpr .rdx, 256⟩, by simp, Offset.contains_base _ (by decide) (by decide)⟩
  rw [WP.block_append_iff]
  apply WP.mono (rounds_ok d s₂ _ h₂.1 scans₂)
  intro s₃ h₃
  have keep₂₃ := h₂.2.trans h₃.2
  have ptr₃ : s₃.gpr .rsi = s.gpr .rsi := (keep₂₃.reg .rsi (by decide)).trans (congrFun h₁.1 .rsi)
  have writable₃ : InRegions s₃.wr (s₃.gpr .rsi) 8 := by
    rw [keep₂₃.wr, h₁.2.2.1, hwr, ptr₃]
    exact ⟨⟨s.gpr .rsi, 8⟩, by simp, Region.contains_self _ _⟩
  let v := (List.range 16).foldl (fun v j => roundSpec d
    (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)) j v) (Spec.Rc2.decodeBlock (Spec.Rc2.blockAt s.mem (s.gpr .rsi)))
  have words₃ : Words s₃ v := by
    rw [h₂.2.mem, h₂.2.reg .rdi (by decide), schedule₁, input₁] at h₃
    exact h₃.1
  rw [WP.block_append_iff]
  apply WP.mono (blockStore_ok s₃ v words₃ writable₃)
  intro s₄ h₄
  have mem₄ : s₄.mem = s₁.mem.writeW (s.gpr .rsi) (pack v) := by rw [h₄.1, keep₂₃.mem, ptr₃]
  have rd₄ : s₄.rd = s.rd := h₄.2.2.1.trans (keep₂₃.rd.trans h₁.2.1)
  have wr₄ : s₄.wr = s.wr := h₄.2.2.2.trans (keep₂₃.wr.trans h₁.2.2.1)
  have regs₄ (r : Reg) (hr : r ∉ roundWrites) : s₄.gpr r = s.gpr r := by
    rw [h₄.2.1 r (by
      intro hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with he | he <;> subst r <;> exact hr (by decide)), keep₂₃.reg r hr, h₁.1]
  have scratchRead₄ : ∀ i ∈ List.range 4,
      InRegions (s₄.rd ++ s₄.wr) (s₄.gpr .rdx + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi
    rw [rd₄, wr₄, regs₄ .rdx (by decide), hrd, hwr]
    have bound := List.mem_range.mp hi
    exact ⟨⟨s.gpr .rdx, 256⟩, by simp, Offset.contains_base _ (by omega_using [bound]) (by omega_using [bound])⟩
  have saved₄ : ∀ i ∈ List.range 4,
      s₄.mem.readW (s₄.gpr .rdx + BitVec.ofNat 64 (8 * i)) 64 = s.gpr (wordReg i) := by
    intro i hi
    have bound := List.mem_range.mp hi
    rw [mem₄, regs₄ .rdx (by decide), Mem.readW_writeW_sep
      (dataSep.symm.sep (Offset.contains_base _ (by omega_using [bound]) (by omega_using [bound])) (Region.contains_self _ _))
      (by decide), h₁.2.2.2]
    exact saveMem_read _ _ _ 4 (by decide) i bound
  apply WP.mono (restoreCode_ok s₄ .rdx wordReg (List.range 4) s.gpr
    (fun i _ => (wordReg_separate i).2.2.1) scratchRead₄ saved₄)
  intro s₅ h₅
  have finalMem : s₅.mem = s₁.mem.writeW (s.gpr .rsi) (pack v) := h₅.2.mem.trans mem₄
  constructor
  · constructor
    · intro r hr
      by_cases hm : r ∈ (List.range 4).map wordReg
      · exact h₅.1 r hm
      · rw [h₅.2.reg _ hm]
        have covered : ∀ r ∈ calleeSaved,
            r ∈ (List.range 4).map wordReg ∨ r ∉ roundWrites := by decide
        exact regs₄ r ((covered r hr).resolve_left hm)
    · have frame₄ : Frame [⟨s.gpr .rsi, 8⟩, ⟨s.gpr .rdx, 256⟩] s.mem s₅.mem := by
        rw [finalMem]
        exact (scratchFrame.mono (fun _ hr => List.mem_cons_of_mem _ hr)).writeW
          List.mem_cons_self _ (Region.contains_self _ _)
      exact frame₄.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _)
        (by
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with h | h
          · subst r; exact retData
          · subst r; exact retScratch)
        (by decide)
  · change Spec.Rc2.blockAt s₅.mem (s.gpr .rsi) = _
    rw [finalMem, blockAt_write64, cipher_rounds]

theorem encrypt_correct (s : State) (hs : (blockContract .encrypt).pre s) :
    ∃ t s', Exec isa encryptBlock s t s' ∧ abiPreserved s s' ∧
      (blockContract .encrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := block_correct .encrypt s hs
  change Exec isa encryptBlock s t s' at he
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he ha, hp⟩

theorem decrypt_correct (s : State) (hs : (blockContract .decrypt).pre s) :
    ∃ t s', Exec isa decryptBlock s t s' ∧ abiPreserved s s' ∧
      (blockContract .decrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := block_correct .decrypt s hs
  change Exec isa decryptBlock s t s' at he
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he ha, hp⟩

end VG.Proof.Rc2.X86_64

end

end


@[expose] public section

section

/-! # Calling the verified block primitive from CBC -/

namespace VG.Proof.Rc2.X86_64.Cbc

open VG VG.X86_64 VG.Impl.Rc2.X86_64

def kept : List Reg := [.rdi, .rsi, .rdx, .rbx, .rbp, .rsp]

theorem block_keeps (d : Spec.Rc2.Direction) :
    ((instrs (.block (blockCode d) : Prog isa)).all fun i => kept.all fun r => !Taint.clobbers i r) = true := by
  cases d
  · change ((instrs encryptBlock).all _) = true
    rw [← Code.allInstrs_eq]; lit_decide
  · change ((instrs decryptBlock).all _) = true
    rw [← Code.allInstrs_eq]; lit_decide

theorem block_keeps_reg (d : Spec.Rc2.Direction) {r : Reg} (hr : r ∈ kept) :
    ∀ i ∈ instrs (.block (blockCode d) : Prog isa), Taint.clobbers i r = false := by
  intro i hi
  have h := List.all_eq_true.mp (List.all_eq_true.mp (block_keeps d) i hi) r hr
  simpa using h

theorem block_correct' (d : Spec.Rc2.Direction) (s : State) (hs : (blockContract d).pre s) :
    ∃ t s', Exec isa (.block (blockCode d)) s t s' ∧ abiPreserved s s' ∧ (blockContract d).post s s' := by
  cases d
  · exact encrypt_correct s hs
  · exact decrypt_correct s hs

theorem blockCall_eq (d : Spec.Rc2.Direction) : Impl.Rc2.X86_64.Cbc.blockCall d =
    .call (match d with | .encrypt => "vg_rc2_encrypt_block" | .decrypt => "vg_rc2_decrypt_block")
      (.block (blockCode d)) := by cases d <;> rfl

structure CallPre (s : State) : Prop where
  reads : Covers [⟨s.gpr .rdi, 128⟩, ⟨s.gpr .rsi, 8⟩, ⟨s.gpr .rdx, 256⟩] (s.rd ++ s.wr)
  writes : Covers [⟨s.gpr .rsi, 8⟩, ⟨s.gpr .rdx, 256⟩] s.wr
  keyScratch : (Region.mk (s.gpr .rdi) 128).Disjoint ⟨s.gpr .rdx, 256⟩
  dataScratch : (Region.mk (s.gpr .rsi) 8).Disjoint ⟨s.gpr .rdx, 256⟩
  stackKey : (below (s.gpr .rsp) 8).Disjoint ⟨s.gpr .rdi, 128⟩
  stackData : (below (s.gpr .rsp) 8).Disjoint ⟨s.gpr .rsi, 8⟩
  stackScratch : (below (s.gpr .rsp) 8).Disjoint ⟨s.gpr .rdx, 256⟩

structure CallPost (d : Spec.Rc2.Direction) (s s' : State) : Prop where
  reg : ∀ r ∈ kept, s'.gpr r = s.gpr r
  callee : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame [⟨s.gpr .rsi, 8⟩, ⟨s.gpr .rdx, 256⟩, below (s.gpr .rsp) 8] s.mem s'.mem
  output : Spec.Rc2.blockAt s'.mem (s.gpr .rsi) =
    cipher d (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)) (Spec.Rc2.blockAt s.mem (s.gpr .rsi))

theorem call_ok (d : Spec.Rc2.Direction) (s : State) (hp : CallPre s) :
    WP isa (Impl.Rc2.X86_64.Cbc.blockCall d) s (CallPost d s) := by
  rw [blockCall_eq]
  refine WP.call (k := blockContract d) (block_correct' d)
    (block_keeps_reg d (by decide)) (by change 16 < 2 ^ 64; decide)
    (rd := [⟨s.gpr .rdi, 128⟩]) (wr := [⟨s.gpr .rsi, 8⟩, ⟨s.gpr .rdx, 256⟩]) ?_ hp.reads hp.writes ?_
  · simp only [blockContract, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.callEntry_rsp, State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp)]
    exact ⟨trivial, trivial, hp.keyScratch, hp.dataScratch, hp.stackData, hp.stackScratch⟩
  · intro s' rd wr callee frame regs ⟨s₂, mem₂, _, out₂⟩
    refine ⟨fun r hr => regs r (block_keeps_reg d hr), callee, rd, wr, frame, ?_⟩
    have stackFrame : Frame [below (s.gpr .rsp) 8] s.mem s.callEntry.mem := by
      exact (Frame.refl _ _).writeW List.mem_cons_self _ (below_call _ (by decide) (by decide))
    have key := scheduleAt_frame stackFrame (s.gpr .rdi) (by simpa using hp.stackKey.symm)
    have input := blockAt_frame stackFrame (s.gpr .rsi) (by simpa using hp.stackData.symm)
    change Spec.Rc2.blockAt s₂.mem _ = cipher d _ _ at out₂
    simp only [State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
      key, input, mem₂] at out₂
    exact out₂

end VG.Proof.Rc2.X86_64.Cbc

end

/-! # CBC loads, XORs, stores, and public loop counters -/

namespace VG.Proof.Rc2.X86_64.Cbc

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Rc2.X86_64

theorem copy64_ok (s : State) (src dst : Reg) (a b : Nat) (hne : dst ≠ .rax)
    (readable : InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 a) 8)
    (writable : InRegions s.wr (s.gpr dst + BitVec.ofNat 64 b) 8) :
    ∃ s', runBlock isa [.mov .rax (.mem (memOp src a)), .store (memOp dst b) .rax] s = some s' ∧
      Keep [.rax] {s with
        mem := s.mem.writeW (s.gpr dst + BitVec.ofNat 64 b) (s.mem.readW (s.gpr src + BitVec.ofNat 64 a) 64)} s' := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, memOp, reduceExec, readSrc,
      State.load64, State.store64, State.ea, offset_nat, readable, ite_true,
      Option.map_some, gpr_setReg, hne, ite_false,
      wr_setReg, writable]
    rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_singleton] at hr
    exact gpr_setReg_of_ne _ _ hr
  · rfl
  · rfl
  · rfl

theorem xor64_ok (s : State) (dst iv : Reg) (hd : dst ≠ .rax) (hi : iv ≠ .rax)
    (readDst : InRegions (s.rd ++ s.wr) (s.gpr dst) 8)
    (readIv : InRegions (s.rd ++ s.wr) (s.gpr iv) 8)
    (writable : InRegions s.wr (s.gpr dst) 8) :
    ∃ s', runBlock isa [.mov .rax (.mem (memOp dst 0)), .alu .xor .rax (.mem (memOp iv 0)),
      .store (memOp dst 0) .rax] s = some s' ∧
      Keep [.rax] {s with mem := s.mem.writeW (s.gpr dst) (s.mem.readW (s.gpr dst) 64 ^^^ s.mem.readW (s.gpr iv) 64)} s' := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, memOp, reduceExec, execAlu, readSrc,
      State.load64, State.store64, State.ea, offset_nat,
      BitVec.add_zero, readDst, readIv, ite_true, Option.map_some, Option.bind_some,
      gpr_setReg, gpr_arithFlags, mem_setReg, rd_setReg, wr_setReg, wr_arithFlags,
      hd, hi, ite_false, writable]
    rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_singleton] at hr
    simp only [gpr_setReg, gpr_arithFlags, hr, ite_false]
  · rfl
  · rfl
  · rfl

theorem advance_ok (s : State) :
    ∃ s', runBlock isa Impl.Rc2.X86_64.Cbc.advance s = some s' ∧
      s'.gpr .rsi = s.gpr .rsi + 8 ∧ s'.gpr .rbp = s.gpr .rbp - 1 ∧
      s'.zf = some ((s.gpr .rbp - 1) == 0) ∧ Keep [.rsi, .rbp] s s' := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, BitVec.reduceSignExtend, Impl.Rc2.X86_64.Cbc.advance,
      runBlock_cons, runStep_some, runBlock_nil, reduceExec, execAlu, readSrc,
      Option.bind_some, gpr_setReg, gpr_arithFlags]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true]
    rfl
  · exact gpr_setReg_self _ _ _
  · rw [zf_setReg, zf_arithFlags]
    rfl
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, gpr_arithFlags, hr.1, hr.2, ite_false]
    · simp only [mem_setReg, mem_arithFlags]
    · simp only [rd_setReg, rd_arithFlags]
    · simp only [wr_setReg, wr_arithFlags]

end VG.Proof.Rc2.X86_64.Cbc
