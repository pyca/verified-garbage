import VerifiedGarbage.Proof.Rc2.CbcMemory
import VerifiedGarbage.Proof.Rc2.X86_64.Block
import VerifiedGarbage.Impl.Rc2.X86_64.Cbc
import VerifiedGarbage.Proof.Framework.X86_64.Call

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
    simp only [runBlock_cons, runStep_some, runBlock_nil, memOp, exec, readSrc,
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
    simp only [runBlock_cons, runStep_some, runBlock_nil, memOp, exec, execAlu, readSrc,
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
      runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
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
