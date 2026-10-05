import VerifiedGarbage.Proof.Rc2.AArch64.Block
import VerifiedGarbage.Impl.Rc2.AArch64.Cbc
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Rc2.Stream
import VerifiedGarbage.Proof.Rc2.AArch64.Key
import VerifiedGarbage.Proof.Framework.AArch64.Spill
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Rc2.Contract
import VerifiedGarbage.Proof.Rc2.AArch64.Vec.Loop
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Call`. -/
section

/-! # Calling the verified block primitive from CBC -/

namespace VG.Proof.Rc2.AArch64.Cbc

open VG VG.AArch64 VG.Impl.Rc2.AArch64

def savedAcrossCall : List Reg := [.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28]

def kept : List Reg := [.x0, .x1, .x2, .x23, .x24]

theorem block_keeps (d : Spec.Rc2.Direction) :
    ((instrs (.block (blockCode d) : Prog isa)).all fun i => kept.all fun r => decide (dstOf i ≠ some r)) = true := by
  cases d
  · change ((instrs encryptBlock).all _) = true
    rw [← Code.allInstrs_eq]; lit_decide
  · change ((instrs decryptBlock).all _) = true
    rw [← Code.allInstrs_eq]; lit_decide

theorem block_keeps_reg (d : Spec.Rc2.Direction) {r : Reg} (hr : r ∈ VG.Proof.Rc2.AArch64.Cbc.kept) :
    ∀ i ∈ instrs (.block (blockCode d) : Prog isa), dstOf i ≠ some r := by
  intro i hi
  have h := List.all_eq_true.mp (List.all_eq_true.mp (VG.Proof.Rc2.AArch64.Cbc.block_keeps d) i hi) r hr
  simpa using h

theorem block_correct' (d : Spec.Rc2.Direction) (s : State) (hs : (blockContract d).pre s) :
    ∃ t s', Exec isa (.block (blockCode d)) s t s' ∧ abiPreserved s s' ∧ (blockContract d).post s s' := by
  cases d
  · exact VG.Proof.Rc2.AArch64.encrypt_correct s hs
  · exact VG.Proof.Rc2.AArch64.decrypt_correct s hs

theorem blockCall_eq (d : Spec.Rc2.Direction) : Impl.Rc2.AArch64.Cbc.blockCall d =
    .call (match d with | .encrypt => "vg_rc2_encrypt_block" | .decrypt => "vg_rc2_decrypt_block")
      (.block (blockCode d)) := by cases d <;> rfl

structure CallPre (s : State) : Prop where
  reads : Covers [⟨s.gpr .x0, 128⟩, ⟨s.gpr .x1, 8⟩, ⟨s.gpr .x2, 256⟩] (s.rd ++ s.wr)
  writes : Covers [⟨s.gpr .x1, 8⟩, ⟨s.gpr .x2, 256⟩] s.wr
  keyScratch : (Region.mk (s.gpr .x0) 128).Disjoint ⟨s.gpr .x2, 256⟩
  dataScratch : (Region.mk (s.gpr .x1) 8).Disjoint ⟨s.gpr .x2, 256⟩

structure CallPost (d : Spec.Rc2.Direction) (s s' : State) : Prop where
  reg : ∀ r ∈ VG.Proof.Rc2.AArch64.Cbc.kept, s'.gpr r = s.gpr r
  callee : ∀ r ∈ VG.Proof.Rc2.AArch64.Cbc.savedAcrossCall, s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame [⟨s.gpr .x1, 8⟩, ⟨s.gpr .x2, 256⟩] s.mem s'.mem
  output : Spec.Rc2.blockAt s'.mem (s.gpr .x1) =
    cipher d (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) (Spec.Rc2.blockAt s.mem (s.gpr .x1))

theorem call_ok (d : Spec.Rc2.Direction) (s : State) (hp : VG.Proof.Rc2.AArch64.Cbc.CallPre s) :
    WP isa (Impl.Rc2.AArch64.Cbc.blockCall d) s (VG.Proof.Rc2.AArch64.Cbc.CallPost d s) := by
  rw [VG.Proof.Rc2.AArch64.Cbc.blockCall_eq]
  refine WP.call (k := blockContract d) (VG.Proof.Rc2.AArch64.Cbc.block_correct' d)
    (rd := [⟨s.gpr .x0, 128⟩]) (wr := [⟨s.gpr .x1, 8⟩, ⟨s.gpr .x2, 256⟩]) ?_ hp.reads hp.writes ?_ (by rfl)
  · simp only [blockContract, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs)]
    exact ⟨trivial, trivial, hp.keyScratch, hp.dataScratch⟩
  · intro s' rd wr sp frame callee regs out
    have sep : ∀ r ∈ VG.Proof.Rc2.AArch64.Cbc.kept, r ∉ linkRegs := by decide
    have saved : ∀ r ∈ VG.Proof.Rc2.AArch64.Cbc.savedAcrossCall, r ∈ preserved ∧ r ≠ .x30 := by decide
    refine ⟨fun r hr => regs r (sep r hr) (VG.Proof.Rc2.AArch64.Cbc.block_keeps_reg d hr),
      fun r hr => callee r (saved r hr).1 (saved r hr).2, rd, wr, frame, ?_⟩
    change Spec.Rc2.blockAt s'.mem _ = cipher d _ _ at out
    simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
      State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs)] at out
    exact out

end VG.Proof.Rc2.AArch64.Cbc

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Steps`. -/
section

/-! # CBC loads, XORs, stores, and public loop counters -/

namespace VG.Proof.Rc2.AArch64.Cbc

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc2.AArch64

theorem copy64_ok (s : State) (src dst : Reg) (a b : Nat) (hne : dst ≠ .x8)
    (readable : InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 a) 8)
    (writable : InRegions s.wr (s.gpr dst + BitVec.ofNat 64 b) 8)
    (ha : a % 8 = 0 ∧ a < 32768 := by decide)
    (hb : b % 8 = 0 ∧ b < 32768 := by decide) :
    ∃ s', runBlock isa [.ldr .x .x8 src a, .str .x .x8 dst b] s = some s' ∧
      Keep [.x8, .x9] {s with
        mem := s.mem.writeW (s.gpr dst + BitVec.ofNat 64 b) (s.mem.readW (s.gpr src + BitVec.ofNat 64 a) 64)} s' := by
  have hw : InRegions (s.write .x .x8 (s.mem.readW (s.gpr src + BitVec.ofNat 64 a) 64)).wr
      ((s.write .x .x8 (s.mem.readW (s.gpr src + BitVec.ofNat 64 a) 64)).gpr dst + BitVec.ofNat 64 b) 8 := by
    simpa only [wr_write, gpr_write, hne, ite_false] using writable
  refine ⟨_, by
    rw [runBlock_cons, exec_ldr_x s _ _ a ha readable, runStep_some,
      runBlock_cons, exec_str_x _ _ _ b hb hw, runStep_some, runBlock_nil], ?_⟩
  constructor
  · intro r hr
    have hn : r ≠ .x8 := by intro h; subst r; exact hr (by simp)
    exact gpr_write_of_ne _ _ _ hn
  · simp only [gpr_write, hne, ite_false, ite_true, BitVec.setWidth_eq, mem_write]
  · rfl
  · rfl

theorem xor64_ok (s : State) (dst iv : Reg) (hd : dst ≠ .x8) (hi : iv ≠ .x8)
    (readDst : InRegions (s.rd ++ s.wr) (s.gpr dst) 8)
    (readIv : InRegions (s.rd ++ s.wr) (s.gpr iv) 8)
    (writable : InRegions s.wr (s.gpr dst) 8)
    (hd9 : dst ≠ .x9 := by decide) :
    ∃ s', runBlock isa [.ldr .x .x8 dst 0, .ldr .x .x9 iv 0,
      .logic .eor .x .x8 .x8 .x9, .str .x .x8 dst 0] s = some s' ∧
      Keep [.x8, .x9] {s with
        mem := s.mem.writeW (s.gpr dst) (s.mem.readW (s.gpr dst) 64 ^^^ s.mem.readW (s.gpr iv) 64)} s' := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
      Nat.zero_mod, Nat.reduceMul, Nat.reduceLT, and_self, ite_true, Option.bind_some, State.load,
      State.store, State.read, BitVec.setWidth_eq, BitVec.add_zero,
      readDst, readIv, writable, Option.map_some, gpr_write, mem_write, rd_write, wr_write,
      hd, hi, hd9, reduceCtorEq, ite_false]
    rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, hr.1, hr.2, ite_false]
  · rfl
  · rfl
  · rfl

def zeroCount (s : State) : Option Bool := some (s.gpr .x24 == 0)

theorem eval_zeroCount (s : State) : eval (.zero .x .x24) s = VG.Proof.Rc2.AArch64.Cbc.zeroCount s := rfl

theorem eval_nonzeroCount (s : State) : eval (.nonzero .x .x24) s = (VG.Proof.Rc2.AArch64.Cbc.zeroCount s).map (! ·) := rfl

theorem advance_ok (s : State) :
    ∃ s', runBlock isa Impl.Rc2.AArch64.Cbc.advance s = some s' ∧
      s'.gpr .x1 = s.gpr .x1 + 8 ∧ s'.gpr .x24 = s.gpr .x24 - 1 ∧
      VG.Proof.Rc2.AArch64.Cbc.zeroCount s' = some ((s.gpr .x24 - 1) == 0) ∧ Keep [.x1, .x24] s s' := by
  refine ⟨_, by
    simp only [Impl.Rc2.AArch64.Cbc.advance, runBlock_cons, runStep_some, runBlock_nil,
      exec, State.read, BitVec.setWidth_eq, Nat.reduceLT, ite_true,
      gpr_write, reduceCtorEq, ite_false]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [gpr_write, reduceCtorEq, ite_false, ite_true, BitVec.setWidth_eq]
    rfl
  · exact gpr_write_self _ _ _ _
  · rfl
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_write, hr.1, hr.2, ite_false]
    · simp only [mem_write]
    · simp only [rd_write]
    · simp only [wr_write]

end VG.Proof.Rc2.AArch64.Cbc

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Pre`. -/
section

/-! # Permissions and separation for one CBC step -/

namespace VG.Proof.Rc2.AArch64.Cbc

open VG VG.AArch64

abbrev keyR (s : State) : Region := ⟨s.gpr .x0, 128⟩
abbrev ivR (s : State) : Region := ⟨s.gpr .x23, 8⟩
abbrev dataR (s : State) (n : Nat := 1) : Region := ⟨s.gpr .x1, 8 * n⟩
abbrev bufR (s : State) : Region := ⟨s.gpr .x2, 512⟩

structure StepPre (s : State) (n : Nat := 1) : Prop where
  reads : Covers [VG.Proof.Rc2.AArch64.Cbc.keyR s, VG.Proof.Rc2.AArch64.Cbc.ivR s, VG.Proof.Rc2.AArch64.Cbc.dataR s n, VG.Proof.Rc2.AArch64.Cbc.bufR s] (s.rd ++ s.wr)
  writes : Covers [VG.Proof.Rc2.AArch64.Cbc.ivR s, VG.Proof.Rc2.AArch64.Cbc.dataR s n, VG.Proof.Rc2.AArch64.Cbc.bufR s] s.wr
  keyIv : (VG.Proof.Rc2.AArch64.Cbc.keyR s).Disjoint (VG.Proof.Rc2.AArch64.Cbc.ivR s)
  keyData : (VG.Proof.Rc2.AArch64.Cbc.keyR s).Disjoint (VG.Proof.Rc2.AArch64.Cbc.dataR s n)
  keyBuf : (VG.Proof.Rc2.AArch64.Cbc.keyR s).Disjoint (VG.Proof.Rc2.AArch64.Cbc.bufR s)
  ivData : (VG.Proof.Rc2.AArch64.Cbc.ivR s).Disjoint (VG.Proof.Rc2.AArch64.Cbc.dataR s n)
  ivBuf : (VG.Proof.Rc2.AArch64.Cbc.ivR s).Disjoint (VG.Proof.Rc2.AArch64.Cbc.bufR s)
  dataBuf : (VG.Proof.Rc2.AArch64.Cbc.dataR s n).Disjoint (VG.Proof.Rc2.AArch64.Cbc.bufR s)

theorem StepPre.transport {s s' : State} {n : Nat} (hp : VG.Proof.Rc2.AArch64.Cbc.StepPre s n)
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) (regs : ∀ r ∈ VG.Proof.Rc2.AArch64.Cbc.kept, s'.gpr r = s.gpr r) : VG.Proof.Rc2.AArch64.Cbc.StepPre s' n := by
  have a := regs .x0 (by decide)
  have b := regs .x23 (by decide)
  have c := regs .x1 (by decide)
  have d := regs .x2 (by decide)
  constructor
  · simpa only [VG.Proof.Rc2.AArch64.Cbc.keyR, VG.Proof.Rc2.AArch64.Cbc.ivR, VG.Proof.Rc2.AArch64.Cbc.dataR, VG.Proof.Rc2.AArch64.Cbc.bufR, rd, wr, a, b, c, d] using hp.reads
  · simpa only [VG.Proof.Rc2.AArch64.Cbc.keyR, VG.Proof.Rc2.AArch64.Cbc.ivR, VG.Proof.Rc2.AArch64.Cbc.dataR, VG.Proof.Rc2.AArch64.Cbc.bufR, rd, wr, a, b, c, d] using hp.writes
  · simpa only [VG.Proof.Rc2.AArch64.Cbc.keyR, VG.Proof.Rc2.AArch64.Cbc.ivR, VG.Proof.Rc2.AArch64.Cbc.dataR, VG.Proof.Rc2.AArch64.Cbc.bufR, rd, wr, a, b, c, d] using hp.keyIv
  · simpa only [VG.Proof.Rc2.AArch64.Cbc.keyR, VG.Proof.Rc2.AArch64.Cbc.ivR, VG.Proof.Rc2.AArch64.Cbc.dataR, VG.Proof.Rc2.AArch64.Cbc.bufR, rd, wr, a, b, c, d] using hp.keyData
  · simpa only [VG.Proof.Rc2.AArch64.Cbc.keyR, VG.Proof.Rc2.AArch64.Cbc.ivR, VG.Proof.Rc2.AArch64.Cbc.dataR, VG.Proof.Rc2.AArch64.Cbc.bufR, rd, wr, a, b, c, d] using hp.keyBuf
  · simpa only [VG.Proof.Rc2.AArch64.Cbc.keyR, VG.Proof.Rc2.AArch64.Cbc.ivR, VG.Proof.Rc2.AArch64.Cbc.dataR, VG.Proof.Rc2.AArch64.Cbc.bufR, rd, wr, a, b, c, d] using hp.ivData
  · simpa only [VG.Proof.Rc2.AArch64.Cbc.keyR, VG.Proof.Rc2.AArch64.Cbc.ivR, VG.Proof.Rc2.AArch64.Cbc.dataR, VG.Proof.Rc2.AArch64.Cbc.bufR, rd, wr, a, b, c, d] using hp.ivBuf
  · simpa only [VG.Proof.Rc2.AArch64.Cbc.keyR, VG.Proof.Rc2.AArch64.Cbc.ivR, VG.Proof.Rc2.AArch64.Cbc.dataR, VG.Proof.Rc2.AArch64.Cbc.bufR, rd, wr, a, b, c, d] using hp.dataBuf

theorem StepPre.keep {s s' : State} {m : Mem} {n : Nat} (hp : VG.Proof.Rc2.AArch64.Cbc.StepPre s n) (h : Keep [.x8, .x9] {s with mem := m} s') : VG.Proof.Rc2.AArch64.Cbc.StepPre s' n :=
  hp.transport h.rd h.wr fun r hr => h.reg r (by
    have sep : ∀ r ∈ VG.Proof.Rc2.AArch64.Cbc.kept, r ∉ [.x8, .x9] := by decide
    exact sep r hr)

theorem StepPre.call {s : State} (hp : VG.Proof.Rc2.AArch64.Cbc.StepPre s) : VG.Proof.Rc2.AArch64.Cbc.CallPre s := by
  constructor
  · have hc : Covers [⟨s.gpr .x0, 128⟩, ⟨s.gpr .x1, 8⟩, ⟨s.gpr .x2, 256⟩]
        [VG.Proof.Rc2.AArch64.Cbc.keyR s, VG.Proof.Rc2.AArch64.Cbc.ivR s, VG.Proof.Rc2.AArch64.Cbc.dataR s, VG.Proof.Rc2.AArch64.Cbc.bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨VG.Proof.Rc2.AArch64.Cbc.keyR s, by simp, 0, by simp, by simp⟩
      · exact ⟨VG.Proof.Rc2.AArch64.Cbc.dataR s, by simp, 0, by simp, by simp⟩
      · exact ⟨VG.Proof.Rc2.AArch64.Cbc.bufR s, by simp, 0, by simp, by simp⟩
    exact fun a n h => hp.reads a n (hc a n h)
  · have hc : Covers [⟨s.gpr .x1, 8⟩, ⟨s.gpr .x2, 256⟩] [VG.Proof.Rc2.AArch64.Cbc.ivR s, VG.Proof.Rc2.AArch64.Cbc.dataR s, VG.Proof.Rc2.AArch64.Cbc.bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨VG.Proof.Rc2.AArch64.Cbc.dataR s, by simp, 0, by simp, by simp⟩
      · exact ⟨VG.Proof.Rc2.AArch64.Cbc.bufR s, by simp, 0, by simp, by simp⟩
    exact fun a n h => hp.writes a n (hc a n h)
  · exact hp.keyBuf.sub_right (Region.sub_prefix (by decide))
  · exact hp.dataBuf.sub_right (Region.sub_prefix (by decide))

theorem StepPre.readData {s : State} (hp : VG.Proof.Rc2.AArch64.Cbc.StepPre s) : InRegions (s.rd ++ s.wr) (s.gpr .x1) 8 :=
  hp.reads _ _ ⟨VG.Proof.Rc2.AArch64.Cbc.dataR s, by simp, Region.contains_self _ _⟩

theorem StepPre.readIv {s : State} (hp : VG.Proof.Rc2.AArch64.Cbc.StepPre s) : InRegions (s.rd ++ s.wr) (s.gpr .x23) 8 :=
  hp.reads _ _ ⟨VG.Proof.Rc2.AArch64.Cbc.ivR s, by simp, Region.contains_self _ _⟩

theorem StepPre.writeData {s : State} (hp : VG.Proof.Rc2.AArch64.Cbc.StepPre s) : InRegions s.wr (s.gpr .x1) 8 :=
  hp.writes _ _ ⟨VG.Proof.Rc2.AArch64.Cbc.dataR s, by simp, Region.contains_self _ _⟩

theorem StepPre.writeIv {s : State} (hp : VG.Proof.Rc2.AArch64.Cbc.StepPre s) : InRegions s.wr (s.gpr .x23) 8 :=
  hp.writes _ _ ⟨VG.Proof.Rc2.AArch64.Cbc.ivR s, by simp, Region.contains_self _ _⟩

theorem StepPre.readBuf {s : State} (hp : VG.Proof.Rc2.AArch64.Cbc.StepPre s) (i : Nat) (hi : i + 8 ≤ 512) :
    InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 i) 8 :=
  hp.reads _ _ ⟨VG.Proof.Rc2.AArch64.Cbc.bufR s, by simp, Offset.contains_base _ hi (by omega)⟩

theorem StepPre.writeBuf {s : State} (hp : VG.Proof.Rc2.AArch64.Cbc.StepPre s) (i : Nat) (hi : i + 8 ≤ 512) :
    InRegions s.wr (s.gpr .x2 + BitVec.ofNat 64 i) 8 :=
  hp.writes _ _ ⟨VG.Proof.Rc2.AArch64.Cbc.bufR s, by simp, Offset.contains_base _ hi (by omega)⟩

end VG.Proof.Rc2.AArch64.Cbc

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Frame`. -/
section

/-! # The frame preserved by a CBC step -/

namespace VG.Proof.Rc2.AArch64.Cbc

open VG VG.AArch64

def stepWrites (s : State) : List Region := [VG.Proof.Rc2.AArch64.Cbc.ivR s, VG.Proof.Rc2.AArch64.Cbc.dataR s, ⟨s.gpr .x2, 264⟩]

structure Pinned (s s' : State) : Prop where
  reg : ∀ r ∈ VG.Proof.Rc2.AArch64.Cbc.kept, s'.gpr r = s.gpr r
  callee : ∀ r ∈ VG.Proof.Rc2.AArch64.Cbc.savedAcrossCall, s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame (VG.Proof.Rc2.AArch64.Cbc.stepWrites s) s.mem s'.mem

theorem Pinned.of_keep {s s' : State} {m : Mem} (h : Keep [.x8, .x9] {s with mem := m} s')
    (frame : Frame (VG.Proof.Rc2.AArch64.Cbc.stepWrites s) s.mem m) : VG.Proof.Rc2.AArch64.Cbc.Pinned s s' := by
  have k : ∀ r ∈ VG.Proof.Rc2.AArch64.Cbc.kept, r ∉ [.x8, .x9] := by decide
  have c : ∀ r ∈ VG.Proof.Rc2.AArch64.Cbc.savedAcrossCall, r ∉ [.x8, .x9] := by decide
  exact ⟨fun r hr => h.reg r (k r hr), fun r hr => h.reg r (c r hr), h.rd, h.wr, by rw [h.mem]; exact frame⟩

theorem Pinned.of_call {d : Spec.Rc2.Direction} {s s' : State} (h : VG.Proof.Rc2.AArch64.Cbc.CallPost d s s') : VG.Proof.Rc2.AArch64.Cbc.Pinned s s' := by
  refine ⟨h.reg, h.callee, h.rd, h.wr, h.mem.sub ?_⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨VG.Proof.Rc2.AArch64.Cbc.dataR s, by simp [VG.Proof.Rc2.AArch64.Cbc.stepWrites], fun _ h => h⟩
  · exact ⟨⟨s.gpr .x2, 264⟩, by simp [VG.Proof.Rc2.AArch64.Cbc.stepWrites], Region.sub_prefix (by decide)⟩

theorem Pinned.writes_eq {s s' : State} (h : VG.Proof.Rc2.AArch64.Cbc.Pinned s s') : VG.Proof.Rc2.AArch64.Cbc.stepWrites s' = VG.Proof.Rc2.AArch64.Cbc.stepWrites s := by
  simp only [VG.Proof.Rc2.AArch64.Cbc.stepWrites, VG.Proof.Rc2.AArch64.Cbc.ivR, VG.Proof.Rc2.AArch64.Cbc.dataR, h.reg .x23 (by decide), h.reg .x1 (by decide), h.reg .x2 (by decide)]

theorem Pinned.trans {s s' s'' : State} (h : VG.Proof.Rc2.AArch64.Cbc.Pinned s s') (h' : VG.Proof.Rc2.AArch64.Cbc.Pinned s' s'') : VG.Proof.Rc2.AArch64.Cbc.Pinned s s'' := by
  refine ⟨fun r hr => (h'.reg r hr).trans (h.reg r hr), fun r hr => (h'.callee r hr).trans (h.callee r hr),
    h'.rd.trans h.rd, h'.wr.trans h.wr, ?_⟩
  have f := h'.mem
  rw [h.writes_eq] at f
  exact h.mem.trans f

theorem Pinned.pre {s s' : State} {n : Nat} (h : VG.Proof.Rc2.AArch64.Cbc.Pinned s s') (hp : VG.Proof.Rc2.AArch64.Cbc.StepPre s n) : VG.Proof.Rc2.AArch64.Cbc.StepPre s' n :=
  hp.transport h.rd h.wr h.reg

theorem Pinned.schedule {s s' : State} (h : VG.Proof.Rc2.AArch64.Cbc.Pinned s s') (hp : VG.Proof.Rc2.AArch64.Cbc.StepPre s) :
    Spec.Rc2.scheduleAt s'.mem (s.gpr .x0) = Spec.Rc2.scheduleAt s.mem (s.gpr .x0) := by
  apply scheduleAt_frame h.mem
  simpa only [VG.Proof.Rc2.AArch64.Cbc.stepWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro hp.keyIv (And.intro hp.keyData
      (hp.keyBuf.sub_right (Region.sub_prefix (by decide : 264 ≤ 512))))

theorem CallPost.iv {d : Spec.Rc2.Direction} {s s' : State} (h : VG.Proof.Rc2.AArch64.Cbc.CallPost d s s') (hp : VG.Proof.Rc2.AArch64.Cbc.StepPre s) :
    Spec.Rc2.blockAt s'.mem (s.gpr .x23) = Spec.Rc2.blockAt s.mem (s.gpr .x23) := by
  apply blockAt_frame h.mem
  simpa only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro hp.ivData
      (hp.ivBuf.sub_right (Region.sub_prefix (by decide : 256 ≤ 512)))

structure StepPost (d : Spec.Rc2.Direction) (s s' : State) : Prop extends VG.Proof.Rc2.AArch64.Cbc.Pinned s s' where
  data : Spec.Rc2.blockAt s'.mem (s.gpr .x1) =
    (Spec.Rc2.cbcStep (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) d
      (Spec.Rc2.blockAt s.mem (s.gpr .x23)) (Spec.Rc2.blockAt s.mem (s.gpr .x1))).1
  iv : Spec.Rc2.blockAt s'.mem (s.gpr .x23) =
    (Spec.Rc2.cbcStep (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) d
      (Spec.Rc2.blockAt s.mem (s.gpr .x23)) (Spec.Rc2.blockAt s.mem (s.gpr .x1))).2

end VG.Proof.Rc2.AArch64.Cbc

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Encrypt`. -/
section

/-! # One CBC encryption step -/

namespace VG.Proof.Rc2.AArch64.Cbc

open VG VG.AArch64 VG.Impl.Rc2.AArch64

theorem encryptStep_ok (s : State) (hp : VG.Proof.Rc2.AArch64.Cbc.StepPre s) :
    WP isa (Impl.Rc2.AArch64.Cbc.step .encrypt) s (VG.Proof.Rc2.AArch64.Cbc.StepPost .encrypt s) := by
  rw [Impl.Rc2.AArch64.Cbc.step]
  apply WP.seq
  obtain ⟨s₁, run₁, keep₁⟩ := VG.Proof.Rc2.AArch64.Cbc.xor64_ok s .x1 .x23 (by decide) (by decide)
    hp.readData hp.readIv hp.writeData
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have pin₁ := Pinned.of_keep keep₁ ((frame_store64 _ _ _).mono (by simp [VG.Proof.Rc2.AArch64.Cbc.stepWrites]))
  have hp₁ := pin₁.pre hp
  have key₁ := pin₁.schedule hp
  have data₁ : Spec.Rc2.blockAt s₁.mem (s.gpr .x1) =
      Spec.Rc2.xorBlock (Spec.Rc2.blockAt s.mem (s.gpr .x1)) (Spec.Rc2.blockAt s.mem (s.gpr .x23)) := by
    rw [keep₁.mem]; exact blockAt_xor _ _ _
  apply WP.seq
  apply WP.mono (VG.Proof.Rc2.AArch64.Cbc.call_ok .encrypt s₁ hp₁.call)
  intro s₂ h₂
  have pin₂ := pin₁.trans (Pinned.of_call h₂)
  have hp₂ := pin₂.pre hp
  have output₂ := h₂.output
  rw [pin₁.reg .x1 (by decide), pin₁.reg .x0 (by decide), key₁, data₁] at output₂
  obtain ⟨s₃, run₃, keep₃⟩ := VG.Proof.Rc2.AArch64.Cbc.copy64_ok s₂ .x1 .x23 0 0 (by decide)
    (by simpa using hp₂.readData) (by simpa using hp₂.writeIv)
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  simp only [BitVec.add_zero] at keep₃
  have frame₃ : Frame [VG.Proof.Rc2.AArch64.Cbc.ivR s₂] s₂.mem s₃.mem := by
    rw [keep₃.mem]; exact frame_store64 _ _ _
  have pin₃ := Pinned.of_keep keep₃ ((frame_store64 _ _ _).mono (by simp [VG.Proof.Rc2.AArch64.Cbc.stepWrites]))
  refine ⟨pin₂.trans pin₃, ?_, ?_⟩
  · have same := blockAt_frame frame₃ (s₂.gpr .x1) (by simpa using hp₂.ivData.symm)
    rw [pin₂.reg .x1 (by decide)] at same
    exact same.trans output₂
  · have out : Spec.Rc2.blockAt s₃.mem (s₂.gpr .x23) = Spec.Rc2.blockAt s₂.mem (s₂.gpr .x1) := by
      rw [keep₃.mem]; exact blockAt_copy _ _ _
    rw [pin₂.reg .x23 (by decide), pin₂.reg .x1 (by decide)] at out
    exact out.trans output₂

end VG.Proof.Rc2.AArch64.Cbc

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Decrypt`. -/
section

/-! # One CBC decryption step, retaining the original ciphertext -/

namespace VG.Proof.Rc2.AArch64.Cbc

open VG VG.AArch64 VG.Impl.Rc2.AArch64

abbrev stashR (s : State) : Region := ⟨s.gpr .x2 + BitVec.ofNat 64 256, 8⟩

theorem stash_sub (s : State) : Region.Sub (VG.Proof.Rc2.AArch64.Cbc.stashR s) (VG.Proof.Rc2.AArch64.Cbc.bufR s) :=
  Offset.sub_base _ (by decide)

theorem call_stash {d : Spec.Rc2.Direction} {s s' : State} (hp : VG.Proof.Rc2.AArch64.Cbc.StepPre s) (h : VG.Proof.Rc2.AArch64.Cbc.CallPost d s s') :
    Spec.Rc2.blockAt s'.mem (VG.Proof.Rc2.AArch64.Cbc.stashR s).base = Spec.Rc2.blockAt s.mem (VG.Proof.Rc2.AArch64.Cbc.stashR s).base := by
  apply blockAt_frame h.mem
  have sep : (VG.Proof.Rc2.AArch64.Cbc.stashR s).Disjoint ⟨s.gpr .x2, 256⟩ := by
    have h := Offset.disjoint (s.gpr .x2) (d := 256) (n := 8) (e := 0) (k := 256)
      (by omega) (by decide) (by decide)
    simpa using h
  simpa only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro ((hp.dataBuf.sub_right (VG.Proof.Rc2.AArch64.Cbc.stash_sub s)).symm) sep

theorem decryptStep_ok (s : State) (hp : VG.Proof.Rc2.AArch64.Cbc.StepPre s) :
    WP isa (Impl.Rc2.AArch64.Cbc.step .decrypt) s (VG.Proof.Rc2.AArch64.Cbc.StepPost .decrypt s) := by
  rw [Impl.Rc2.AArch64.Cbc.step]
  apply WP.seq
  obtain ⟨s₁, run₁, keep₁⟩ := VG.Proof.Rc2.AArch64.Cbc.copy64_ok s .x1 .x2 0 256 (by decide)
    (by simpa using hp.readData) (hp.writeBuf 256 (by decide))
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  simp only [BitVec.add_zero] at keep₁
  have frame₁ : Frame [VG.Proof.Rc2.AArch64.Cbc.stashR s] s.mem s₁.mem := by
    rw [keep₁.mem]; exact frame_store64 _ _ _
  have pin₁ : VG.Proof.Rc2.AArch64.Cbc.Pinned s s₁ := by
    apply Pinned.of_keep keep₁
    apply (frame_store64 _ _ _).sub
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact ⟨⟨s.gpr .x2, 264⟩, by simp [VG.Proof.Rc2.AArch64.Cbc.stepWrites], Offset.sub_base _ (by decide)⟩
  have hp₁ := pin₁.pre hp
  have key₁ := pin₁.schedule hp
  have data₁ := blockAt_frame frame₁ (s.gpr .x1) (by simpa using hp.dataBuf.sub_right (VG.Proof.Rc2.AArch64.Cbc.stash_sub s))
  have iv₁ := blockAt_frame frame₁ (s.gpr .x23) (by simpa using hp.ivBuf.sub_right (VG.Proof.Rc2.AArch64.Cbc.stash_sub s))
  have stash₁ : Spec.Rc2.blockAt s₁.mem (VG.Proof.Rc2.AArch64.Cbc.stashR s).base = Spec.Rc2.blockAt s.mem (s.gpr .x1) := by
    rw [keep₁.mem]; exact blockAt_copy _ _ _
  apply WP.seq
  apply WP.mono (VG.Proof.Rc2.AArch64.Cbc.call_ok .decrypt s₁ hp₁.call)
  intro s₂ h₂
  have pin₂ := pin₁.trans (Pinned.of_call h₂)
  have hp₂ := pin₂.pre hp
  have output₂ := h₂.output
  rw [pin₁.reg .x1 (by decide), pin₁.reg .x0 (by decide), key₁, data₁] at output₂
  have iv₂ := h₂.iv hp₁
  rw [pin₁.reg .x23 (by decide), iv₁] at iv₂
  have stash₂ := VG.Proof.Rc2.AArch64.Cbc.call_stash hp₁ h₂
  simp only [pin₁.reg .x2 (by decide)] at stash₂
  have stash₂' := stash₂.trans stash₁
  change WP isa (.block (([.ldr .x .x8 .x1 0, .ldr .x .x9 .x23 0,
    .logic .eor .x .x8 .x8 .x9, .str .x .x8 .x1 0] : List Instr) ++
    ([.ldr .x .x8 .x2 256, .str .x .x8 .x23 0] : List Instr))) s₂ _
  rw [WP.block_append_iff]
  obtain ⟨s₃, run₃, keep₃⟩ := VG.Proof.Rc2.AArch64.Cbc.xor64_ok s₂ .x1 .x23 (by decide) (by decide)
    hp₂.readData hp₂.readIv hp₂.writeData
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have frame₃ : Frame [VG.Proof.Rc2.AArch64.Cbc.dataR s₂] s₂.mem s₃.mem := by
    rw [keep₃.mem]; exact frame_store64 _ _ _
  have pin₃ := Pinned.of_keep keep₃ ((frame_store64 _ _ _).mono (by simp [VG.Proof.Rc2.AArch64.Cbc.stepWrites]))
  have pin₀₃ := pin₂.trans pin₃
  have hp₃ := pin₀₃.pre hp
  have data₃ : Spec.Rc2.blockAt s₃.mem (s.gpr .x1) =
      Spec.Rc2.xorBlock (Spec.Rc2.decryptBlock (Spec.Rc2.scheduleAt s.mem (s.gpr .x0))
        (Spec.Rc2.blockAt s.mem (s.gpr .x1))) (Spec.Rc2.blockAt s.mem (s.gpr .x23)) := by
    have h : Spec.Rc2.blockAt s₃.mem (s₂.gpr .x1) =
        Spec.Rc2.xorBlock (Spec.Rc2.blockAt s₂.mem (s₂.gpr .x1)) (Spec.Rc2.blockAt s₂.mem (s₂.gpr .x23)) := by
      rw [keep₃.mem]; exact blockAt_xor _ _ _
    rw [pin₂.reg .x1 (by decide), pin₂.reg .x23 (by decide), output₂, iv₂] at h
    exact h
  have stash₃ := blockAt_frame frame₃ (VG.Proof.Rc2.AArch64.Cbc.stashR s₂).base
    (by simpa using (hp₂.dataBuf.sub_right (VG.Proof.Rc2.AArch64.Cbc.stash_sub s₂)).symm)
  simp only [pin₂.reg .x2 (by decide)] at stash₃
  have stash₃' := stash₃.trans stash₂'
  obtain ⟨s₄, run₄, keep₄⟩ := VG.Proof.Rc2.AArch64.Cbc.copy64_ok s₃ .x2 .x23 256 0 (by decide)
    (hp₃.readBuf 256 (by decide)) (by simpa using hp₃.writeIv)
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  simp only [BitVec.add_zero] at keep₄
  have frame₄ : Frame [VG.Proof.Rc2.AArch64.Cbc.ivR s₃] s₃.mem s₄.mem := by
    rw [keep₄.mem]; exact frame_store64 _ _ _
  have pin₄ := Pinned.of_keep keep₄ ((frame_store64 _ _ _).mono (by simp [VG.Proof.Rc2.AArch64.Cbc.stepWrites]))
  refine ⟨pin₀₃.trans pin₄, ?_, ?_⟩
  · have same := blockAt_frame frame₄ (s₃.gpr .x1) (by simpa using hp₃.ivData.symm)
    rw [pin₀₃.reg .x1 (by decide)] at same
    exact same.trans data₃
  · have out : Spec.Rc2.blockAt s₄.mem (s₃.gpr .x23) = Spec.Rc2.blockAt s₃.mem (VG.Proof.Rc2.AArch64.Cbc.stashR s₃).base := by
      rw [keep₄.mem]; exact blockAt_copy _ _ _
    simp only [pin₀₃.reg .x23 (by decide), pin₀₃.reg .x2 (by decide)] at out
    exact out.trans stash₃'

end VG.Proof.Rc2.AArch64.Cbc

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Slice`. -/
section

/-! # Restricting CBC permissions to a consecutive subrange -/

namespace VG.Proof.Rc2.AArch64.Cbc

open VG VG.AArch64

theorem StepPre.slice {s s' : State} {n m i : Nat} (hp : VG.Proof.Rc2.AArch64.Cbc.StepPre s n) (bound : i + m ≤ n)
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr)
    (key : s'.gpr .x0 = s.gpr .x0) (iv : s'.gpr .x23 = s.gpr .x23)
    (buf : s'.gpr .x2 = s.gpr .x2)
    (ptr : s'.gpr .x1 = s.gpr .x1 + BitVec.ofNat 64 (8 * i)) : VG.Proof.Rc2.AArch64.Cbc.StepPre s' m := by
  have sub : Region.Sub (VG.Proof.Rc2.AArch64.Cbc.dataR s' m) (VG.Proof.Rc2.AArch64.Cbc.dataR s n) := by
    change Region.Sub ⟨s'.gpr .x1, 8 * m⟩ ⟨s.gpr .x1, 8 * n⟩
    rw [ptr]
    exact Offset.sub_base _ (by omega)
  constructor
  · have hc : Covers [VG.Proof.Rc2.AArch64.Cbc.keyR s', VG.Proof.Rc2.AArch64.Cbc.ivR s', VG.Proof.Rc2.AArch64.Cbc.dataR s' m, VG.Proof.Rc2.AArch64.Cbc.bufR s'] [VG.Proof.Rc2.AArch64.Cbc.keyR s, VG.Proof.Rc2.AArch64.Cbc.ivR s, VG.Proof.Rc2.AArch64.Cbc.dataR s n, VG.Proof.Rc2.AArch64.Cbc.bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨VG.Proof.Rc2.AArch64.Cbc.keyR s, by simp, 0, by simp [key], by simp⟩
      · exact ⟨VG.Proof.Rc2.AArch64.Cbc.ivR s, by simp, 0, by simp [iv], by simp⟩
      · exact ⟨VG.Proof.Rc2.AArch64.Cbc.dataR s n, by simp, 8 * i, ptr, by change 8 * i + 8 * m ≤ 8 * n; omega⟩
      · exact ⟨VG.Proof.Rc2.AArch64.Cbc.bufR s, by simp, 0, by simp [buf], by simp⟩
    rw [rd, wr]
    exact fun a k h => hp.reads a k (hc a k h)
  · have hc : Covers [VG.Proof.Rc2.AArch64.Cbc.ivR s', VG.Proof.Rc2.AArch64.Cbc.dataR s' m, VG.Proof.Rc2.AArch64.Cbc.bufR s'] [VG.Proof.Rc2.AArch64.Cbc.ivR s, VG.Proof.Rc2.AArch64.Cbc.dataR s n, VG.Proof.Rc2.AArch64.Cbc.bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨VG.Proof.Rc2.AArch64.Cbc.ivR s, by simp, 0, by simp [iv], by simp⟩
      · exact ⟨VG.Proof.Rc2.AArch64.Cbc.dataR s n, by simp, 8 * i, ptr, by change 8 * i + 8 * m ≤ 8 * n; omega⟩
      · exact ⟨VG.Proof.Rc2.AArch64.Cbc.bufR s, by simp, 0, by simp [buf], by simp⟩
    rw [wr]
    exact fun a k h => hp.writes a k (hc a k h)
  · simpa only [VG.Proof.Rc2.AArch64.Cbc.keyR, VG.Proof.Rc2.AArch64.Cbc.ivR, key, iv] using hp.keyIv
  · simpa only [VG.Proof.Rc2.AArch64.Cbc.keyR, key] using hp.keyData.sub_right sub
  · simpa only [VG.Proof.Rc2.AArch64.Cbc.keyR, VG.Proof.Rc2.AArch64.Cbc.bufR, key, buf] using hp.keyBuf
  · simpa only [VG.Proof.Rc2.AArch64.Cbc.ivR, iv] using hp.ivData.sub_right sub
  · simpa only [VG.Proof.Rc2.AArch64.Cbc.ivR, VG.Proof.Rc2.AArch64.Cbc.bufR, iv, buf] using hp.ivBuf
  · simpa only [VG.Proof.Rc2.AArch64.Cbc.bufR, buf] using hp.dataBuf.sub_left sub

theorem StepPre.head {s : State} {n : Nat} (hp : VG.Proof.Rc2.AArch64.Cbc.StepPre s n) (hn : 1 ≤ n) : VG.Proof.Rc2.AArch64.Cbc.StepPre s :=
  hp.slice (i := 0) hn rfl rfl rfl rfl rfl (by simp)

end VG.Proof.Rc2.AArch64.Cbc

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Body`. -/
section

/-! # A CBC loop iteration and its public counter -/

namespace VG.Proof.Rc2.AArch64.Cbc

open VG VG.AArch64 VG.Impl.Rc2.AArch64

theorem step_ok (d : Spec.Rc2.Direction) (s : State) (hp : VG.Proof.Rc2.AArch64.Cbc.StepPre s) :
    WP isa (Impl.Rc2.AArch64.Cbc.step d) s (VG.Proof.Rc2.AArch64.Cbc.StepPost d s) := by
  cases d
  · exact VG.Proof.Rc2.AArch64.Cbc.encryptStep_ok s hp
  · exact VG.Proof.Rc2.AArch64.Cbc.decryptStep_ok s hp

structure BodyPost (d : Spec.Rc2.Direction) (s : State) (n : Nat) (s' : State) : Prop where
  ptr : s'.gpr .x1 = s.gpr .x1 + 8
  count : s'.gpr .x24 = BitVec.ofNat 64 (n - 1)
  flag : VG.Proof.Rc2.AArch64.Cbc.zeroCount s' = some (decide (n = 1))
  reg : ∀ r ∈ VG.Proof.Rc2.AArch64.Cbc.kept, r ≠ .x1 → r ≠ .x24 → s'.gpr r = s.gpr r
  callee : ∀ r ∈ VG.Proof.Rc2.AArch64.Cbc.savedAcrossCall, r ≠ .x24 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame (VG.Proof.Rc2.AArch64.Cbc.stepWrites s) s.mem s'.mem
  data : Spec.Rc2.blockAt s'.mem (s.gpr .x1) =
    (Spec.Rc2.cbcStep (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) d
      (Spec.Rc2.blockAt s.mem (s.gpr .x23)) (Spec.Rc2.blockAt s.mem (s.gpr .x1))).1
  iv : Spec.Rc2.blockAt s'.mem (s.gpr .x23) =
    (Spec.Rc2.cbcStep (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) d
      (Spec.Rc2.blockAt s.mem (s.gpr .x23)) (Spec.Rc2.blockAt s.mem (s.gpr .x1))).2

theorem body_ok (d : Spec.Rc2.Direction) (s : State) (n : Nat) (hn : 1 ≤ n) (bound : n < 2 ^ 64)
    (count : s.gpr .x24 = BitVec.ofNat 64 n) (hp : VG.Proof.Rc2.AArch64.Cbc.StepPre s) :
    WP isa (Impl.Rc2.AArch64.Cbc.body d) s (VG.Proof.Rc2.AArch64.Cbc.BodyPost d s n) := by
  rw [Impl.Rc2.AArch64.Cbc.body]
  apply WP.seq
  apply WP.mono (VG.Proof.Rc2.AArch64.Cbc.step_ok d s hp)
  intro s₁ h₁
  obtain ⟨s₂, run₂, ptr₂, count₂, flag₂, keep₂⟩ := VG.Proof.Rc2.AArch64.Cbc.advance_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have count' : s₁.gpr .x24 - 1 = BitVec.ofNat 64 (n - 1) := by
    rw [h₁.reg .x24 (by decide), count]
    exact Offset.ofNat_sub_ofNat hn
  refine ⟨by rw [ptr₂, h₁.reg .x1 (by decide)], count₂.trans count', ?_, ?_, ?_,
    keep₂.rd.trans h₁.rd, keep₂.wr.trans h₁.wr, ?_, ?_, ?_⟩
  · rw [flag₂, count']
    have eqZero := counter_eq (n - 1) 0 (by omega) (by decide)
    simp only [BitVec.sub_zero] at eqZero
    change some (BitVec.ofNat 64 (n - 1) == 0#64) = _
    rw [eqZero]
    have he : n - 1 = 0 ↔ n = 1 := by omega
    simp only [he]
  · intro r hr hs hb
    exact (keep₂.reg r (by simp [hs, hb])).trans (h₁.reg r hr)
  · intro r hr hb
    have hs : r ≠ .x1 := by
      have fact : ∀ r ∈ VG.Proof.Rc2.AArch64.Cbc.savedAcrossCall, r ≠ .x1 := by decide
      exact fact r hr
    exact (keep₂.reg r (by simp [hs, hb])).trans (h₁.callee r hr)
  · rw [keep₂.mem]; exact h₁.mem
  · rw [keep₂.mem]; exact h₁.data
  · rw [keep₂.mem]; exact h₁.iv

theorem BodyPost.tail {d : Spec.Rc2.Direction} {s s' : State} {n : Nat}
    (h : VG.Proof.Rc2.AArch64.Cbc.BodyPost d s (n + 1) s') (hp : VG.Proof.Rc2.AArch64.Cbc.StepPre s (n + 1)) : VG.Proof.Rc2.AArch64.Cbc.StepPre s' n :=
  hp.slice (i := 1) (by omega) h.rd h.wr
    (h.reg .x0 (by decide) (by decide) (by decide))
    (h.reg .x23 (by decide) (by decide) (by decide))
    (h.reg .x2 (by decide) (by decide) (by decide))
    h.ptr

end VG.Proof.Rc2.AArch64.Cbc

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Lit`. -/
section

/-! # Literal CBC callers -/

namespace VG

materialize_code Impl.Rc2.AArch64.Cbc.encrypt
materialize_code Impl.Rc2.AArch64.Cbc.decrypt

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.Cbc.ConstantTime`. -/
section

/-! # Constant-time CBC callers -/

namespace VG.Proof.Rc2.AArch64.Cbc

open VG VG.AArch64 VG.Impl.Rc2.AArch64.Cbc

theorem encrypt_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs [.x0, .x1, .x2, .x3, .x4]) encrypt := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact ⟨hp.1, fun r hr => hp.2 r (Taint.mem_ofRegs.mp hr)⟩

theorem decrypt_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs [.x0, .x1, .x2, .x3, .x4]) decrypt := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact ⟨hp.1, fun r hr => hp.2 r (Taint.mem_ofRegs.mp hr)⟩

end VG.Proof.Rc2.AArch64.Cbc

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.Cbc.LoopFrame`. -/
section

/-! # Frames for successive CBC blocks -/

namespace VG.Proof.Rc2.AArch64.Cbc

open VG VG.AArch64

def loopWrites (s : State) (n : Nat) : List Region := [VG.Proof.Rc2.AArch64.Cbc.ivR s, VG.Proof.Rc2.AArch64.Cbc.dataR s n, ⟨s.gpr .x2, 264⟩]

theorem loopFrame_slice {s s' : State} {n m i : Nat} {a b : Mem}
    (h : Frame (VG.Proof.Rc2.AArch64.Cbc.loopWrites s' m) a b) (bound : i + m ≤ n)
    (iv : s'.gpr .x23 = s.gpr .x23) (buf : s'.gpr .x2 = s.gpr .x2)
    (ptr : s'.gpr .x1 = s.gpr .x1 + BitVec.ofNat 64 (8 * i)) :
    Frame (VG.Proof.Rc2.AArch64.Cbc.loopWrites s n) a b := by
  apply h.sub
  intro r hr
  simp only [VG.Proof.Rc2.AArch64.Cbc.loopWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · refine ⟨VG.Proof.Rc2.AArch64.Cbc.ivR s, by simp [VG.Proof.Rc2.AArch64.Cbc.loopWrites], ?_⟩
    change Region.Sub ⟨s'.gpr .x23, 8⟩ ⟨s.gpr .x23, 8⟩
    rw [iv]; exact fun _ h => h
  · refine ⟨VG.Proof.Rc2.AArch64.Cbc.dataR s n, by simp [VG.Proof.Rc2.AArch64.Cbc.loopWrites], ?_⟩
    change Region.Sub ⟨s'.gpr .x1, 8 * m⟩ ⟨s.gpr .x1, 8 * n⟩
    rw [ptr]
    exact Offset.sub_base _ (by omega)
  · refine ⟨⟨s.gpr .x2, 264⟩, by simp [VG.Proof.Rc2.AArch64.Cbc.loopWrites], ?_⟩
    rw [buf]; exact fun _ h => h

theorem BodyPost.frame {d : Spec.Rc2.Direction} {s s' : State} {n : Nat}
    (h : VG.Proof.Rc2.AArch64.Cbc.BodyPost d s n s') (hn : 1 ≤ n) : Frame (VG.Proof.Rc2.AArch64.Cbc.loopWrites s n) s.mem s'.mem :=
  VG.Proof.Rc2.AArch64.Cbc.loopFrame_slice (m := 1) (i := 0) h.mem hn rfl rfl (by simp)

theorem BodyPost.schedule {d : Spec.Rc2.Direction} {s s' : State} {n : Nat}
    (h : VG.Proof.Rc2.AArch64.Cbc.BodyPost d s n s') (hp : VG.Proof.Rc2.AArch64.Cbc.StepPre s) :
    Spec.Rc2.scheduleAt s'.mem (s.gpr .x0) = Spec.Rc2.scheduleAt s.mem (s.gpr .x0) := by
  apply scheduleAt_frame h.mem
  simpa only [VG.Proof.Rc2.AArch64.Cbc.stepWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro hp.keyIv (And.intro hp.keyData
      (hp.keyBuf.sub_right (Region.sub_prefix (by decide : 264 ≤ 512))))

theorem BodyPost.tailData {d : Spec.Rc2.Direction} {s s' : State} {n : Nat}
    (h : VG.Proof.Rc2.AArch64.Cbc.BodyPost d s (n + 1) s') (hp : VG.Proof.Rc2.AArch64.Cbc.StepPre s (n + 1)) (bound : 8 * (n + 1) ≤ 2 ^ 64) :
    Spec.Rc2.blocksAt s'.mem (s.gpr .x1 + 8) n = Spec.Rc2.blocksAt s.mem (s.gpr .x1 + 8) n := by
  have sub : Region.Sub ⟨s.gpr .x1 + 8, 8 * n⟩ (VG.Proof.Rc2.AArch64.Cbc.dataR s (n + 1)) :=
    Offset.sub_base _ (by change 8 + 8 * n ≤ 8 * (n + 1); omega)
  have sep : (Region.mk (s.gpr .x1 + 8) (8 * n)).Disjoint (VG.Proof.Rc2.AArch64.Cbc.dataR s) :=
    Offset.disjoint_base _ (d := 8) (n := 8 * n) (k := 8) (by decide) (by omega)
  apply blocksAt_frame h.mem
  simpa only [VG.Proof.Rc2.AArch64.Cbc.stepWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro ((hp.ivData.sub_right sub).symm) (And.intro sep
      ((hp.dataBuf.sub_left sub).sub_right (Region.sub_prefix (by decide : 264 ≤ 512))))

theorem firstBlock_frame {d : Spec.Rc2.Direction} {s s' : State} {n : Nat} {m : Mem}
    (h : VG.Proof.Rc2.AArch64.Cbc.BodyPost d s (n + 1) s') (hp : VG.Proof.Rc2.AArch64.Cbc.StepPre s (n + 1)) (bound : 8 * (n + 1) ≤ 2 ^ 64)
    (frame : Frame (VG.Proof.Rc2.AArch64.Cbc.loopWrites s' n) s'.mem m) :
    Spec.Rc2.blockAt m (s.gpr .x1) = Spec.Rc2.blockAt s'.mem (s.gpr .x1) := by
  have first : Region.Sub (VG.Proof.Rc2.AArch64.Cbc.dataR s) (VG.Proof.Rc2.AArch64.Cbc.dataR s (n + 1)) := Region.sub_prefix (by change 8 ≤ 8 * (n + 1); omega)
  have sep : (VG.Proof.Rc2.AArch64.Cbc.dataR s).Disjoint ⟨s.gpr .x1 + 8, 8 * n⟩ :=
    Offset.base_disjoint _ (e := 8) (n := 8 * n) (k := 8) (by decide) (by omega)
  apply blockAt_frame frame
  have iv := h.reg .x23 (by decide) (by decide) (by decide)
  have buf := h.reg .x2 (by decide) (by decide) (by decide)
  simpa only [VG.Proof.Rc2.AArch64.Cbc.loopWrites, VG.Proof.Rc2.AArch64.Cbc.ivR, VG.Proof.Rc2.AArch64.Cbc.dataR, iv, buf, h.ptr,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro ((hp.ivData.sub_right first).symm) (And.intro sep
      ((hp.dataBuf.sub_left first).sub_right (Region.sub_prefix (by decide : 264 ≤ 512))))

end VG.Proof.Rc2.AArch64.Cbc

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Loop`. -/
section

/-! # Correctness of the CBC loop on complete blocks -/

namespace VG.Proof.Rc2.AArch64.Cbc

open VG VG.AArch64

structure LoopPost (d : Spec.Rc2.Direction) (s : State) (n : Nat) (s' : State) : Prop where
  ptr : s'.gpr .x1 = s.gpr .x1 + BitVec.ofNat 64 (8 * n)
  count : s'.gpr .x24 = 0
  reg : ∀ r ∈ VG.Proof.Rc2.AArch64.Cbc.kept, r ≠ .x1 → r ≠ .x24 → s'.gpr r = s.gpr r
  callee : ∀ r ∈ VG.Proof.Rc2.AArch64.Cbc.savedAcrossCall, r ≠ .x24 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame (VG.Proof.Rc2.AArch64.Cbc.loopWrites s n) s.mem s'.mem
  data : Spec.Rc2.blocksAt s'.mem (s.gpr .x1) n =
    (Spec.Rc2.cbc (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) d
      (Spec.Rc2.blockAt s.mem (s.gpr .x23)) (Spec.Rc2.blocksAt s.mem (s.gpr .x1) n)).1
  iv : Spec.Rc2.blockAt s'.mem (s.gpr .x23) =
    (Spec.Rc2.cbc (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) d
      (Spec.Rc2.blockAt s.mem (s.gpr .x23)) (Spec.Rc2.blocksAt s.mem (s.gpr .x1) n)).2

theorem loop_ok (d : Spec.Rc2.Direction) (n : Nat) :
    ∀ s : State, 1 ≤ n → 8 * n ≤ 2 ^ 64 → VG.Proof.Rc2.AArch64.Cbc.StepPre s n → s.gpr .x24 = BitVec.ofNat 64 n →
      WP isa (.loop (Impl.Rc2.AArch64.Cbc.body d) (.nonzero .x .x24)) s (VG.Proof.Rc2.AArch64.Cbc.LoopPost d s n) := by
  induction n with
  | zero => intro s hn; omega
  | succ n ih =>
    intro s hn bound hp count
    obtain ⟨t₁, s₁, exec₁, h₁⟩ := VG.Proof.Rc2.AArch64.Cbc.body_ok d s (n + 1) hn (by omega) count (hp.head hn)
    by_cases hz : n = 0
    · subst n
      refine ⟨_, s₁, Exec.loopExit exec₁ ?_, ?_⟩
      · simp only [VG.Proof.Rc2.AArch64.Cbc.eval_nonzeroCount, h₁.flag, decide_true, Option.map_some, Bool.not_true]
      · refine ⟨h₁.ptr, h₁.count, h₁.reg, h₁.callee, h₁.rd, h₁.wr, h₁.frame (by decide), ?_, ?_⟩
        · rw [blocksAt_cons, blocksAt_cons]
          simp only [Spec.Rc2.blocksAt, List.range_zero, List.map_nil, Spec.Rc2.cbc]
          exact congrArg (· :: []) h₁.data
        · rw [blocksAt_cons]
          simp only [Spec.Rc2.blocksAt, List.range_zero, List.map_nil, Spec.Rc2.cbc]
          exact h₁.iv
    · have hp₁ := h₁.tail hp
      obtain ⟨t₂, s₂, exec₂, h₂⟩ := ih s₁ (by omega) (by omega) hp₁ (by simpa using h₁.count)
      refine ⟨_, s₂, Exec.loopNext exec₁ ?_ exec₂, ?_⟩
      · have he : n + 1 ≠ 1 := by omega
        simp only [VG.Proof.Rc2.AArch64.Cbc.eval_nonzeroCount, h₁.flag, he, decide_false, Option.map_some, Bool.not_false]
      · have key := h₁.schedule (hp.head hn)
        have tail := h₁.tailData hp bound
        have data := h₂.data
        have iv := h₂.iv
        have ki := h₁.reg .x0 (by decide) (by decide) (by decide)
        have vi := h₁.reg .x23 (by decide) (by decide) (by decide)
        have bi := h₁.reg .x2 (by decide) (by decide) (by decide)
        rw [ki, vi, h₁.ptr, key, tail, h₁.iv] at data
        rw [ki, vi, h₁.ptr, key, tail, h₁.iv] at iv
        refine ⟨?_, h₂.count, ?_, ?_, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, ?_, ?_, ?_⟩
        · rw [h₂.ptr, h₁.ptr, BitVec.add_assoc]
          exact congrArg (s.gpr .x1 + ·) (by
            change BitVec.ofNat 64 8 + BitVec.ofNat 64 (8 * n) = _
            rw [← BitVec.ofNat_add]
            exact congrArg (BitVec.ofNat 64) (by omega))
        · intro r hr hs hb
          exact (h₂.reg r hr hs hb).trans (h₁.reg r hr hs hb)
        · intro r hr hb
          exact (h₂.callee r hr hb).trans (h₁.callee r hr hb)
        · exact (h₁.frame hn).trans (VG.Proof.Rc2.AArch64.Cbc.loopFrame_slice (i := 1) h₂.mem (by omega) vi bi h₁.ptr)
        · have first := VG.Proof.Rc2.AArch64.Cbc.firstBlock_frame h₁ hp bound h₂.mem
          rw [blocksAt_cons, first, h₁.data, data, blocksAt_cons]
          rfl
        · rw [blocksAt_cons]
          exact iv

theorem maybeLoop_ok (d : Spec.Rc2.Direction) (s : State) (n : Nat) (bound : 8 * n ≤ 2 ^ 64)
    (hp : VG.Proof.Rc2.AArch64.Cbc.StepPre s n) (count : s.gpr .x24 = BitVec.ofNat 64 n)
    (flag : VG.Proof.Rc2.AArch64.Cbc.zeroCount s = some (s.gpr .x24 == 0) := rfl) :
    WP isa (.ite (.zero .x .x24) (.block []) (.loop (Impl.Rc2.AArch64.Cbc.body d) (.nonzero .x .x24))) s (VG.Proof.Rc2.AArch64.Cbc.LoopPost d s n) := by
  have eqZero := counter_eq n 0 (by omega) (by decide)
  simp only [BitVec.sub_zero] at eqZero
  have flag' : VG.Proof.Rc2.AArch64.Cbc.zeroCount s = some (decide (n = 0)) := by
    rw [flag, count]
    exact congrArg some eqZero
  by_cases hz : n = 0
  · subst n
    apply WP.ite true (by simp only [VG.Proof.Rc2.AArch64.Cbc.eval_zeroCount, flag', decide_true])
    · intro _
      apply WP.block_nil
      refine ⟨by simp, count, fun _ _ _ _ => rfl, fun _ _ _ => rfl, rfl, rfl, Frame.refl _ _, ?_, ?_⟩
      · rfl
      · rfl
    · simp
  · apply WP.ite false (by simp only [VG.Proof.Rc2.AArch64.Cbc.eval_zeroCount, flag', hz, decide_false])
    · simp
    · intro _
      exact VG.Proof.Rc2.AArch64.Cbc.loop_ok d n s (by omega) bound hp count

theorem LoopPost.scratchRead {d : Spec.Rc2.Direction} {s s' : State} {n : Nat}
    (h : VG.Proof.Rc2.AArch64.Cbc.LoopPost d s n s') (hp : VG.Proof.Rc2.AArch64.Cbc.StepPre s n) (i : Nat) (lo : 264 ≤ i) (hi : i + 8 ≤ 512) :
    s'.mem.readW (s.gpr .x2 + BitVec.ofNat 64 i) 64 = s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 i) 64 := by
  have sub : Region.Sub ⟨s.gpr .x2 + BitVec.ofNat 64 i, 8⟩ (VG.Proof.Rc2.AArch64.Cbc.bufR s) := Offset.sub_base _ hi
  have sep : (Region.mk (s.gpr .x2 + BitVec.ofNat 64 i) 8).Disjoint ⟨s.gpr .x2, 264⟩ :=
    Offset.disjoint_base _ lo (by omega)
  apply h.mem.readW (r := ⟨s.gpr .x2 + BitVec.ofNat 64 i, 8⟩) (Region.contains_self _ _)
    (hn := by decide)
  simpa only [VG.Proof.Rc2.AArch64.Cbc.loopWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro ((hp.ivBuf.sub_right sub).symm) (And.intro ((hp.dataBuf.sub_right sub).symm)
      sep)

end VG.Proof.Rc2.AArch64.Cbc

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.Cbc.IO`. -/
section

/-! # CBC register saves, setup, and restoration -/

namespace VG.Proof.Rc2.AArch64.Cbc

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc2.AArch64

/-- The registers the code saves in `buf`, and where. -/
abbrev saved : List (Reg × Nat) := [(.x23, 264), (.x24, 272), (.x30, 280)]

/-- The memory after the saves. -/
abbrev savedMem (s : State) : Mem := Spill.saveMem s.mem (s.gpr .x4) s.gpr VG.Proof.Rc2.AArch64.Cbc.saved

theorem save_eq : Impl.Rc2.AArch64.Cbc.save = Spill.saveCode .x4 VG.Proof.Rc2.AArch64.Cbc.saved := rfl

theorem restore_eq : Impl.Rc2.AArch64.Cbc.restore = Spill.restoreCode .x2 VG.Proof.Rc2.AArch64.Cbc.saved := rfl

theorem savedMem_frame (s : State) : Frame [⟨s.gpr .x4, 512⟩] s.mem (VG.Proof.Rc2.AArch64.Cbc.savedMem s) :=
  Spill.saveMem_frame_base (by decide) (by decide) _ _ _

theorem setup_ok (s : State) :
    ∃ s', runBlock isa Impl.Rc2.AArch64.Cbc.setup s = some s' ∧
      s'.gpr .x23 = s.gpr .x1 ∧ s'.gpr .x24 = s.gpr .x3 ∧
      s'.gpr .x1 = s.gpr .x2 ∧ s'.gpr .x2 = s.gpr .x4 ∧
      VG.Proof.Rc2.AArch64.Cbc.zeroCount s' = some (s.gpr .x3 == 0) ∧ Keep [.x23, .x24, .x1, .x2] s s' := by
  refine ⟨_, by
    simp only [Impl.Rc2.AArch64.Cbc.setup, rr, runBlock_cons, exec]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_write, State.read, BitVec.add_zero, BitVec.setWidth_eq]
  · simp [gpr_write, State.read, BitVec.add_zero, BitVec.setWidth_eq]
  · simp [gpr_write, State.read, BitVec.add_zero, BitVec.setWidth_eq]
  · simp [gpr_write, State.read, BitVec.add_zero, BitVec.setWidth_eq]
  · unfold VG.Proof.Rc2.AArch64.Cbc.zeroCount
    simp [gpr_write, State.read, BitVec.add_zero, BitVec.setWidth_eq]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_write, BitVec.setWidth_eq, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
    · simp only [mem_write]
    · simp only [rd_write]
    · simp only [wr_write]

end VG.Proof.Rc2.AArch64.Cbc

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Contract`. -/
section

/-! # CBC's function-level contract -/

namespace VG.Proof.Rc2.AArch64.Cbc

open VG VG.AArch64

def contract (d : Spec.Rc2.Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, 128⟩
    let iv : Region := ⟨s.gpr .x1, 8⟩
    let data : Region := ⟨s.gpr .x2, 8 * (s.gpr .x3).toNat⟩
    let buf : Region := ⟨s.gpr .x4, 512⟩
    s.rd = [key] ∧ s.wr = [iv, data, buf] ∧ key.Disjoint iv ∧ key.Disjoint data ∧ key.Disjoint buf ∧
      iv.Disjoint data ∧ iv.Disjoint buf ∧ data.Disjoint buf ∧
      (s.gpr .x2).toNat + 8 * (s.gpr .x3).toNat ≤ 2 ^ 64
  post s s' :=
    let out := Spec.Rc2.cbc (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) d
      (Spec.Rc2.blockAt s.mem (s.gpr .x1)) (Spec.Rc2.blocksAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
    Spec.Rc2.blocksAt s'.mem (s.gpr .x2) (s.gpr .x3).toNat = out.1 ∧
      Spec.Rc2.blockAt s'.mem (s.gpr .x1) = out.2
  pub := PublicRegs [.x0, .x1, .x2, .x3, .x4]

end VG.Proof.Rc2.AArch64.Cbc

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Phase`. -/
section

/-!
# Decryption's groups of eight blocks

`phase_ok`: the vector phase decrypts the first `8 ⌊n / 8⌋` of the `n`
blocks, leaves the chaining value updated and `x24` the blocks left.
`phaseLoop_ok`: it and the loop over the blocks left, as the loop alone.
-/

namespace VG.Proof.Rc2.AArch64.Cbc

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc2.AArch64 VG.Proof.Rc2 VG.Proof.Rc2.AArch64.Vec

theorem contains_prefix {a : Addr} {n k : Nat} (h : n ≤ k) : (⟨a, k⟩ : Region).Contains a n := by
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega

/-- A region disjoint from a 128-byte one is shorter than the address space. -/
theorem Region.len_lt_of_disjoint {r r' : Region} (h : r.Disjoint r') (hr : 0 < r.len) :
    r'.len < 2 ^ 64 := by
  apply Nat.lt_of_not_le
  intro hl
  apply h r.base (VG.Proof.Rc2.AArch64.Cbc.contains_prefix hr)
  simp only [Region.Contains]
  have := (r.base - r'.base).isLt
  omega

structure PhasePost (s : State) (n : Nat) (s' : State) : Prop where
  ptr : s'.gpr .x1 = s.gpr .x1 + BitVec.ofNat 64 (8 * (8 * (n / 8)))
  count : s'.gpr .x24 = BitVec.ofNat 64 (n % 8)
  reg : ∀ r ∈ VG.Proof.Rc2.AArch64.Cbc.kept, r ≠ .x1 → r ≠ .x24 → s'.gpr r = s.gpr r
  callee : ∀ r ∈ VG.Proof.Rc2.AArch64.Cbc.savedAcrossCall, r ≠ .x24 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame [VG.Proof.Rc2.AArch64.Cbc.ivR s, VG.Proof.Rc2.AArch64.Cbc.dataR s (8 * (n / 8))] s.mem s'.mem
  data : Spec.Rc2.blocksAt s'.mem (s.gpr .x1) (8 * (n / 8)) =
    (Spec.Rc2.cbc (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) .decrypt
      (Spec.Rc2.blockAt s.mem (s.gpr .x23)) (Spec.Rc2.blocksAt s.mem (s.gpr .x1) (8 * (n / 8)))).1
  iv : Spec.Rc2.blockAt s'.mem (s.gpr .x23) =
    (Spec.Rc2.cbc (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) .decrypt
      (Spec.Rc2.blockAt s.mem (s.gpr .x23)) (Spec.Rc2.blocksAt s.mem (s.gpr .x1) (8 * (n / 8)))).2

theorem exec_lsr (s : State) (d n : Reg) {sh : Nat} (h : sh < 64) :
    exec (.lsr .x d n sh) s = some (s.write .x d (s.gpr n >>> sh)) := by
  simp [exec, Size.bits, h, State.read]

theorem ofNat_shift3 {n : Nat} (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n >>> 3 = BitVec.ofNat 64 (n / 8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt hn]
  rw [Nat.mod_eq_of_lt (by omega)]

theorem ofNat_mask3 {n : Nat} (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n <<< (64 - 3) >>> (64 - 3) = BitVec.ofNat 64 (n % 8) := by
  rw [maskBits _ 3 (by decide)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

/-- The groups, when there are any. -/
theorem groups_ok (s s₁ : State) {n : Nat} (hp : VG.Proof.Rc2.AArch64.Cbc.StepPre s n) (bound : 8 * n < 2 ^ 64)
    (hg : 0 < n / 8) (e₁ : s₁ = s.write .x .x10 (BitVec.ofNat 64 (n / 8))) :
    WP isa (.seq (.block Vec.setup) (.seq (.loop (.block Vec.group) (.nonzero .x .x10))
      (.block [.str .x .x11 .x23 0]))) s₁ fun s' =>
        s'.gpr .x1 = s.gpr .x1 + BitVec.ofNat 64 (8 * (8 * (n / 8))) ∧
        (∀ g, g ≠ .x1 → g ≠ .x6 → g ≠ .x7 → g ≠ .x9 → g ≠ .x10 → g ≠ .x11 → g ≠ .x12 →
          s'.gpr g = s.gpr g) ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
        Frame [VG.Proof.Rc2.AArch64.Cbc.ivR s, VG.Proof.Rc2.AArch64.Cbc.dataR s (8 * (n / 8))] s.mem s'.mem ∧
        Spec.Rc2.blocksAt s'.mem (s.gpr .x1) (8 * (n / 8)) =
          (Spec.Rc2.cbc (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) .decrypt
            (Spec.Rc2.blockAt s.mem (s.gpr .x23)) (Spec.Rc2.blocksAt s.mem (s.gpr .x1) (8 * (n / 8)))).1 ∧
        Spec.Rc2.blockAt s'.mem (s.gpr .x23) =
          (Spec.Rc2.cbc (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) .decrypt
            (Spec.Rc2.blockAt s.mem (s.gpr .x23)) (Spec.Rc2.blocksAt s.mem (s.gpr .x1) (8 * (n / 8)))).2 := by
  subst e₁
  let g := n / 8
  have z : ∀ a : Addr, a + BitVec.ofNat 64 0 = a := fun a => BitVec.add_zero a
  apply WP.seq
  rw [Vec.setup, WP.block_append_iff]
  have rk : InRegions ((s.write .x .x10 (BitVec.ofNat 64 g)).rd ++ (s.write .x .x10 (BitVec.ofNat 64 g)).wr)
      ((s.write .x .x10 (BitVec.ofNat 64 g)).gpr .x0) 128 :=
    hp.reads _ _ ⟨VG.Proof.Rc2.AArch64.Cbc.keyR s, by simp, Region.contains_self _ _⟩
  refine WP.mono (loads_ok _ rk 8 (by decide)) fun a ⟨arow, av, ae⟩ => ?_
  let s₁ := s.write .x .x10 (BitVec.ofNat 64 g)
  have ag : a.gpr = s₁.gpr := by rw [ae]
  have am : a.mem = s.mem := by rw [ae]; rfl
  have ard : a.rd = s.rd := by rw [ae]; rfl
  have awr : a.wr = s.wr := by rw [ae]; rfl
  have asp : a.sp = s.sp := by rw [ae]; rfl
  have s₁g : ∀ r, r ≠ .x10 → s₁.gpr r = s.gpr r := fun r h => gpr_write_of_ne _ _ _ h
  let b₁ := a.write .x .x9 (BitVec.ofNat 64 65535)
  let b₂ := b₁.setV Vec.m16 (ofVWords ((b₁.gpr .x9).setWidth 32) ((b₁.gpr .x9).setWidth 32)
    ((b₁.gpr .x9).setWidth 32) ((b₁.gpr .x9).setWidth 32))
  let b₃ := b₂.write .x .x11 (b₂.mem.readW (b₂.gpr .x23 + BitVec.ofNat 64 0) 64)
  have x23 : b₂.gpr .x23 = s.gpr .x23 := by
    simp only [b₂, b₁, gpr_setV, gpr_write_of_ne _ _ _ (by decide : ¬Reg.x23 = .x9), ag]
    exact s₁g _ (by decide)
  have e₃ : exec (.ldr .x .x11 .x23 0) b₂ = some b₃ := exec_ldr_x b₂ .x11 .x23 0 ⟨by decide, by decide⟩ (by
    rw [x23, z]
    rw [show b₂.rd = s.rd from ard, show b₂.wr = s.wr from awr]
    exact hp.reads _ _ ⟨VG.Proof.Rc2.AArch64.Cbc.ivR s, by simp, Region.contains_self _ _⟩)
  refine WP.of_runBlock ⟨b₃, by
    rw [runBlock_cons, exec_imm _ _ _ (by decide), runStep_some, runBlock_cons, exec_dups,
      runStep_some, runBlock_cons, e₃, runStep_some, runBlock_nil], ?_⟩
  have b3g : ∀ r, r ≠ .x9 → r ≠ .x11 → b₃.gpr r = s₁.gpr r := fun r h9 h11 => by
    simp only [b₃, b₂, b₁, gpr_write_of_ne _ _ _ h11, gpr_setV, gpr_write_of_ne _ _ _ h9, ag]
  have x1 : b₃.gpr .x1 = s.gpr .x1 := (b3g _ (by decide) (by decide)).trans (s₁g _ (by decide))
  have hdata : (VG.Proof.Rc2.AArch64.Cbc.dataR s n).Contains (s.gpr .x1) (64 * g) := VG.Proof.Rc2.AArch64.Cbc.contains_prefix (by omega)
  have big : 64 * g < 2 ^ 64 := by omega
  apply WP.seq
  refine WP.mono (loopV_ok s.mem (s.gpr .x0) g b₃ (by omega) big ?_ ?_ ?_ ?_ ?_) fun c hc => ?_
  · intro r hr
    have hne := (treg_ne_kb r hr).2
    simp only [b₃, b₂, b₁, v_write, v_setV_of_ne _ _ hne]
    rw [arow r hr]
    rw [show s₁.mem = s.mem from rfl, show s₁.gpr .x0 = s.gpr .x0 from s₁g _ (by decide)]
  · simp only [b₃, b₂, v_write, v_setV_self, b₁, gpr_write_self, BitVec.setWidth_eq]; rfl
  · rw [b3g _ (by decide) (by decide)]; exact gpr_write_self _ _ _ _
  · rw [x1, show b₃.rd = s.rd from ard, show b₃.wr = s.wr from awr]
    exact hp.reads _ _ ⟨VG.Proof.Rc2.AArch64.Cbc.dataR s n, by simp, hdata⟩
  · rw [x1, show b₃.wr = s.wr from awr]
    exact hp.writes _ _ ⟨VG.Proof.Rc2.AArch64.Cbc.dataR s n, by simp, hdata⟩
  -- The chaining value: the IV, then the last ciphertext block, stored.
  have cx23 : c.gpr .x23 = s.gpr .x23 := by
    rw [hc.reg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      b3g _ (by decide) (by decide), s₁g _ (by decide)]
  have b11 : wordBlock (b₃.gpr .x11) = Spec.Rc2.blockAt s.mem (s.gpr .x23) := by
    simp only [b₃, gpr_write_self, BitVec.setWidth_eq]
    rw [x23, z, ← blockAt_read64, show b₂.mem = s.mem from am]
  have data := hc.data
  have chain := hc.chain
  rw [b11, x1, show b₃.mem = s.mem from am] at data chain
  have ivw : InRegions c.wr (c.gpr .x23 + BitVec.ofNat 64 0) 8 := by
    rw [cx23, z, hc.wr, show b₃.wr = s.wr from awr]
    exact hp.writes _ _ ⟨VG.Proof.Rc2.AArch64.Cbc.ivR s, by simp, Region.contains_self _ _⟩
  refine WP.of_runBlock ⟨_, by
    rw [runBlock_cons, exec_str_x c .x11 .x23 0 ⟨by decide, by decide⟩ ivw, runStep_some, runBlock_nil], ?_⟩
  simp only [cx23, z]
  have ivFrame := frame_store64 c.mem (s.gpr .x23) (c.gpr .x11)
  have sub : Region.Sub (VG.Proof.Rc2.AArch64.Cbc.dataR s (8 * g)) (VG.Proof.Rc2.AArch64.Cbc.dataR s n) := Region.sub_prefix (by omega)
  refine ⟨?_, fun r h1 h6 h7 h9 h10 h11 h12 => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hc.ptr, x1, show 64 * g = 8 * (8 * g) by omega]
  · rw [hc.reg r h1 h6 h7 h9 h10 h11 h12, b3g r h9 h11, s₁g r h10]
  · rw [hc.rd]; exact ard
  · rw [hc.wr]; exact awr
  · rw [hc.sp]; exact asp
  · have f₁ : Frame [VG.Proof.Rc2.AArch64.Cbc.ivR s, VG.Proof.Rc2.AArch64.Cbc.dataR s (8 * g)] s.mem c.mem := by
      have := hc.frame
      rw [x1, show b₃.mem = s.mem from am] at this
      exact this.sub fun r hr => by
        simp only [List.mem_singleton] at hr
        subst hr
        exact ⟨VG.Proof.Rc2.AArch64.Cbc.dataR s (8 * g), by simp, Region.sub_prefix (by omega)⟩
    exact f₁.writeW (r := VG.Proof.Rc2.AArch64.Cbc.ivR s) (by simp) _ (Region.contains_self _ _)
  · rw [blocksAt_frame ivFrame _ _ (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst hr
      exact (hp.ivData.sub_right sub).symm)]
    rw [show 8 * g = 8 * g from rfl] at data
    exact data
  · rw [blockAt_store64, chain]

theorem mask24_ok (s : State) :
    ∃ s', runBlock isa (mask .x24 3) s = some s' ∧
      s'.gpr .x24 = s.gpr .x24 <<< (64 - 3) >>> (64 - 3) ∧
      (∀ r, r ≠ .x24 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let s₁ := s.write .x .x24 (s.gpr .x24 <<< (64 - 3))
  let s₂ := s₁.write .x .x24 (s₁.gpr .x24 >>> (64 - 3))
  refine ⟨s₂, by rw [mask, runBlock_cons, exec_lslx _ _ _ (by decide), runStep_some, runBlock_cons,
      exec_lsrx _ _ _ (by decide), runStep_some, runBlock_nil], ?_, fun r h => ?_, rfl, rfl, rfl⟩
  · simp only [s₂, s₁, gpr_write_self, BitVec.setWidth_eq]
  · simp only [s₂, s₁, gpr_write_of_ne _ _ _ h]

theorem phase_ok (s : State) {n : Nat} (hp : VG.Proof.Rc2.AArch64.Cbc.StepPre s n) (bound : 8 * n < 2 ^ 64)
    (count : s.gpr .x24 = BitVec.ofNat 64 n) :
    WP isa Vec.phase s (VG.Proof.Rc2.AArch64.Cbc.PhasePost s n) := by
  rw [Vec.phase]
  apply WP.seq
  let s₁ := s.write .x .x10 (s.gpr .x24 >>> 3)
  refine WP.of_runBlock ⟨s₁, by rw [runBlock_cons, VG.Proof.Rc2.AArch64.Cbc.exec_lsr _ _ _ (by decide), runStep_some,
    runBlock_nil], ?_⟩
  have x10 : s.gpr .x24 >>> 3 = BitVec.ofNat 64 (n / 8) := by rw [count, VG.Proof.Rc2.AArch64.Cbc.ofNat_shift3 (by omega)]
  have s₁g : ∀ r, r ≠ .x10 → s₁.gpr r = s.gpr r := fun r h => gpr_write_of_ne _ _ _ h
  apply WP.seq
  -- What the masking leaves, from a state with the blocks done.
  have finish : ∀ s₂ : State, s₂.gpr .x1 = s.gpr .x1 + BitVec.ofNat 64 (8 * (8 * (n / 8))) →
      (∀ g, g ≠ .x1 → g ≠ .x6 → g ≠ .x7 → g ≠ .x9 → g ≠ .x10 → g ≠ .x11 → g ≠ .x12 →
        s₂.gpr g = s.gpr g) → s₂.rd = s.rd → s₂.wr = s.wr →
      Frame [VG.Proof.Rc2.AArch64.Cbc.ivR s, VG.Proof.Rc2.AArch64.Cbc.dataR s (8 * (n / 8))] s.mem s₂.mem →
      Spec.Rc2.blocksAt s₂.mem (s.gpr .x1) (8 * (n / 8)) =
        (Spec.Rc2.cbc (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) .decrypt
          (Spec.Rc2.blockAt s.mem (s.gpr .x23)) (Spec.Rc2.blocksAt s.mem (s.gpr .x1) (8 * (n / 8)))).1 →
      Spec.Rc2.blockAt s₂.mem (s.gpr .x23) =
        (Spec.Rc2.cbc (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) .decrypt
          (Spec.Rc2.blockAt s.mem (s.gpr .x23)) (Spec.Rc2.blocksAt s.mem (s.gpr .x1) (8 * (n / 8)))).2 →
      WP isa (.block (mask .x24 3)) s₂ (VG.Proof.Rc2.AArch64.Cbc.PhasePost s n) := by
    intro s₂ ptr reg rd wr fr data iv
    obtain ⟨s₃, run, c₃, g₃, m₃, rd₃, wr₃⟩ := VG.Proof.Rc2.AArch64.Cbc.mask24_ok s₂
    refine WP.of_runBlock ⟨s₃, run, ?_⟩
    have keep : ∀ r, r ≠ .x1 → r ≠ .x6 → r ≠ .x7 → r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 →
        r ≠ .x24 → s₃.gpr r = s.gpr r := fun r a b c d e f i j => (g₃ r j).trans (reg r a b c d e f i)
    refine ⟨by rw [g₃ _ (by decide), ptr], ?_, fun r hr h1 h24 => ?_, fun r hr h24 => ?_,
      rd₃.trans rd, wr₃.trans wr, by rw [m₃]; exact fr, by rw [m₃]; exact data, by rw [m₃]; exact iv⟩
    · rw [c₃, reg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        count, VG.Proof.Rc2.AArch64.Cbc.ofNat_mask3 (by omega)]
    · have : ∀ r ∈ VG.Proof.Rc2.AArch64.Cbc.kept, r ≠ .x1 → r ≠ .x24 → r ≠ .x6 ∧ r ≠ .x7 ∧ r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x11 ∧
          r ≠ .x12 := by decide
      obtain ⟨a, b, c, d, e, f⟩ := this r hr h1 h24
      exact keep r h1 a b c d e f h24
    · have : ∀ r ∈ VG.Proof.Rc2.AArch64.Cbc.savedAcrossCall, r ≠ .x24 → r ≠ .x1 ∧ r ≠ .x6 ∧ r ≠ .x7 ∧ r ≠ .x9 ∧ r ≠ .x10 ∧
          r ≠ .x11 ∧ r ≠ .x12 := by decide
      obtain ⟨a, b, c, d, e, f, i⟩ := this r hr h24
      exact keep r a b c d e f i h24
  by_cases hg : n / 8 = 0
  · apply WP.ite true (by simp [eval, State.read, s₁, gpr_write_self, x10, hg])
    · intro _
      apply WP.block_nil
      apply finish s₁ (by rw [s₁g _ (by decide), hg]; exact (BitVec.add_zero _).symm) (fun g _ _ _ _ h _ _ => s₁g g h) rfl rfl
        (by rw [hg]; exact Frame.refl _ _)
      · rw [hg]; rfl
      · rw [hg]; rfl
    · intro h; cases h
  · apply WP.ite false (by
      simp [eval, State.read, s₁, gpr_write_self, x10]
      exact ofNat_ne_zero (by omega) (by omega))
    · intro h; cases h
    · intro _
      refine WP.mono (VG.Proof.Rc2.AArch64.Cbc.groups_ok s s₁ hp bound (by omega) (by rw [← x10])) fun s₂ h => ?_
      obtain ⟨ptr, reg, rd, wr, _, fr, data, iv⟩ := h
      exact finish s₂ ptr reg rd wr fr data iv

/-- The groups, then the blocks left one at a time: CBC on all `n`. -/
theorem phaseLoop_ok (s : State) (n : Nat) (bound : 8 * n ≤ 2 ^ 64) (hp : VG.Proof.Rc2.AArch64.Cbc.StepPre s n)
    (count : s.gpr .x24 = BitVec.ofNat 64 n) :
    WP isa (.seq Vec.phase (.ite (.zero .x .x24) (.block [])
      (.loop (Impl.Rc2.AArch64.Cbc.body .decrypt) (.nonzero .x .x24)))) s (VG.Proof.Rc2.AArch64.Cbc.LoopPost .decrypt s n) := by
  have strict : 8 * n < 2 ^ 64 := Region.len_lt_of_disjoint hp.keyData (show 0 < 128 by decide)
  apply WP.seq
  refine WP.mono (VG.Proof.Rc2.AArch64.Cbc.phase_ok s hp strict count) fun s' h' => ?_
  let g := n / 8
  have key' := h'.reg .x0 (by decide) (by decide) (by decide)
  have iv' := h'.reg .x23 (by decide) (by decide) (by decide)
  have buf' := h'.reg .x2 (by decide) (by decide) (by decide)
  have hp' : VG.Proof.Rc2.AArch64.Cbc.StepPre s' (n % 8) :=
    hp.slice (i := 8 * g) (by omega) h'.rd h'.wr key' iv' buf' h'.ptr
  refine WP.mono (VG.Proof.Rc2.AArch64.Cbc.maybeLoop_ok .decrypt s' (n % 8) (by omega) hp' h'.count) fun s'' h'' => ?_
  have subG : Region.Sub (VG.Proof.Rc2.AArch64.Cbc.dataR s (8 * g)) (VG.Proof.Rc2.AArch64.Cbc.dataR s n) := Region.sub_prefix (by omega)
  have restSub : Region.Sub ⟨s.gpr .x1 + BitVec.ofNat 64 (8 * (8 * g)), 8 * (n % 8)⟩ (VG.Proof.Rc2.AArch64.Cbc.dataR s n) :=
    Offset.sub_base _ (by omega)
  have keyFrame : Spec.Rc2.scheduleAt s'.mem (s.gpr .x0) = Spec.Rc2.scheduleAt s.mem (s.gpr .x0) :=
    scheduleAt_frame h'.mem _ (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.keyIv
      · exact hp.keyData.sub_right subG)
  have restKeep : Spec.Rc2.blocksAt s'.mem (s.gpr .x1 + BitVec.ofNat 64 (8 * (8 * g))) (n % 8) =
      Spec.Rc2.blocksAt s.mem (s.gpr .x1 + BitVec.ofNat 64 (8 * (8 * g))) (n % 8) :=
    blocksAt_frame h'.mem _ _ (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hp.ivData.sub_right restSub).symm
      · exact Offset.disjoint_base _ (by omega) (by omega))
  have firstKeep : Spec.Rc2.blocksAt s''.mem (s.gpr .x1) (8 * g) =
      Spec.Rc2.blocksAt s'.mem (s.gpr .x1) (8 * g) :=
    blocksAt_frame h''.mem _ _ (by
      intro r hr
      simp only [VG.Proof.Rc2.AArch64.Cbc.loopWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · simp only [VG.Proof.Rc2.AArch64.Cbc.ivR, iv']; exact (hp.ivData.sub_right subG).symm
      · simp only [VG.Proof.Rc2.AArch64.Cbc.dataR, h'.ptr]; exact Offset.base_disjoint _ (by omega) (by omega)
      · simp only [buf']
        exact (hp.dataBuf.sub_left subG).sub_right (Region.sub_prefix (by decide : 264 ≤ 512)))
  have split : ∀ (mm : Mem) (q : Addr), Spec.Rc2.blocksAt mm q n =
      Spec.Rc2.blocksAt mm q (8 * g) ++ Spec.Rc2.blocksAt mm (q + BitVec.ofNat 64 (8 * (8 * g))) (n % 8) :=
    fun mm q => by rw [← blocksAt_add]; exact congrArg _ (by omega)
  have data'' := h''.data
  have ivOut := h''.iv
  rw [h'.ptr, key', iv', keyFrame, h'.iv, restKeep] at data'' ivOut
  refine ⟨?_, h''.count, fun r hr h1 h24 => (h''.reg r hr h1 h24).trans (h'.reg r hr h1 h24),
    fun r hr h24 => (h''.callee r hr h24).trans (h'.callee r hr h24), h''.rd.trans h'.rd,
    h''.wr.trans h'.wr, ?_, ?_, ?_⟩
  · rw [h''.ptr, h'.ptr, Offset.add_add]
    exact congrArg _ (congrArg _ (by omega))
  · refine (h'.mem.sub fun r hr => ?_).trans (VG.Proof.Rc2.AArch64.Cbc.loopFrame_slice (i := 8 * g) h''.mem (by omega) iv' buf' h'.ptr)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨VG.Proof.Rc2.AArch64.Cbc.ivR s, by simp [VG.Proof.Rc2.AArch64.Cbc.loopWrites], fun _ h => h⟩
    · exact ⟨VG.Proof.Rc2.AArch64.Cbc.dataR s n, by simp [VG.Proof.Rc2.AArch64.Cbc.loopWrites], subG⟩
  · rw [split, split, firstKeep, h'.data, cbc_append, data'']
  · rw [ivOut, split, cbc_append]

end VG.Proof.Rc2.AArch64.Cbc

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Verified`. -/
section

/-! # Verified RC2-CBC encryption and decryption -/

namespace VG.Proof.Rc2.AArch64.Cbc

open VG VG.AArch64 VG.Impl.Rc2.AArch64

/-- The save, the setup, the blocks (`mid`, as the loop over them), and the restore. -/
theorem cbc_body_correct (d : Spec.Rc2.Direction) (mid : Prog isa)
    (hmid : ∀ s n, 8 * n ≤ 2 ^ 64 → VG.Proof.Rc2.AArch64.Cbc.StepPre s n → s.gpr .x24 = BitVec.ofNat 64 n →
      WP isa mid s (VG.Proof.Rc2.AArch64.Cbc.LoopPost d s n))
    (s : State) (hs : (VG.Proof.Rc2.AArch64.Cbc.contract d).pre s) :
    WP isa (.seq (.block (Impl.Rc2.AArch64.Cbc.save ++ Impl.Rc2.AArch64.Cbc.setup))
      (.seq mid (.block Impl.Rc2.AArch64.Cbc.restore))) s
      (fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ (VG.Proof.Rc2.AArch64.Cbc.contract d).post s s') := by
  obtain ⟨hrd, hwr, keyIv, keyData, keyBuf, ivData, ivBuf, dataBuf,
    fit⟩ := hs
  have writes (i : Nat) (hi : i + 8 ≤ 512) : InRegions s.wr (s.gpr .x4 + BitVec.ofNat 64 i) 8 := by
    rw [hwr]
    exact ⟨⟨s.gpr .x4, 512⟩, by simp, Offset.contains_base _ hi (by omega)⟩
  apply WP.seq
  rw [VG.Proof.Rc2.AArch64.Cbc.save_eq]
  refine Spill.save_ok (by decide) (fun p hp => writes p.2 (by revert p; decide)) ?_
  obtain ⟨s₂, run₂, iv₂, count₂, data₂, buf₂, -, keep₂⟩ := VG.Proof.Rc2.AArch64.Cbc.setup_ok { s with
                                                                             mem := VG.Proof.Rc2.AArch64.Cbc.savedMem s }
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have key₂ : s₂.gpr .x0 = s.gpr .x0 := keep₂.reg .x0 (by decide)
  have rd₂ : s₂.rd = s.rd := keep₂.rd
  have wr₂ : s₂.wr = s.wr := keep₂.wr
  have mem₂ : s₂.mem = VG.Proof.Rc2.AArch64.Cbc.savedMem s := keep₂.mem
  have scratchFrame : Frame [⟨s.gpr .x4, 512⟩] s.mem s₂.mem := by
    rw [mem₂]; exact VG.Proof.Rc2.AArch64.Cbc.savedMem_frame s
  have initialKey := scheduleAt_frame scratchFrame (s.gpr .x0) (by simpa using keyBuf)
  have initialIv := blockAt_frame scratchFrame (s.gpr .x1) (by simpa using ivBuf)
  have initialData := blocksAt_frame scratchFrame (s.gpr .x2) (s.gpr .x3).toNat (by simpa using dataBuf)
  have hp₂ : VG.Proof.Rc2.AArch64.Cbc.StepPre s₂ (s.gpr .x3).toNat := by
    constructor
    · simp only [VG.Proof.Rc2.AArch64.Cbc.keyR, VG.Proof.Rc2.AArch64.Cbc.ivR, VG.Proof.Rc2.AArch64.Cbc.dataR, VG.Proof.Rc2.AArch64.Cbc.bufR, key₂, iv₂, data₂, buf₂, rd₂, wr₂, hrd, hwr]
      exact fun _ _ h => h
    · simp only [VG.Proof.Rc2.AArch64.Cbc.ivR, VG.Proof.Rc2.AArch64.Cbc.dataR, VG.Proof.Rc2.AArch64.Cbc.bufR, iv₂, data₂, buf₂, wr₂, hwr]
      exact fun _ _ h => h
    · simpa only [VG.Proof.Rc2.AArch64.Cbc.keyR, VG.Proof.Rc2.AArch64.Cbc.ivR, key₂, iv₂] using keyIv
    · simpa only [VG.Proof.Rc2.AArch64.Cbc.keyR, VG.Proof.Rc2.AArch64.Cbc.dataR, key₂, data₂] using keyData
    · simpa only [VG.Proof.Rc2.AArch64.Cbc.keyR, VG.Proof.Rc2.AArch64.Cbc.bufR, key₂, buf₂] using keyBuf
    · simpa only [VG.Proof.Rc2.AArch64.Cbc.ivR, VG.Proof.Rc2.AArch64.Cbc.dataR, iv₂, data₂] using ivData
    · simpa only [VG.Proof.Rc2.AArch64.Cbc.ivR, VG.Proof.Rc2.AArch64.Cbc.bufR, iv₂, buf₂] using ivBuf
    · simpa only [VG.Proof.Rc2.AArch64.Cbc.dataR, VG.Proof.Rc2.AArch64.Cbc.bufR, data₂, buf₂] using dataBuf
  apply WP.seq
  apply WP.mono (hmid s₂ (s.gpr .x3).toNat (by omega) hp₂ (by simpa using count₂))
  intro s₃ h₃
  have rd₃ := h₃.rd.trans rd₂
  have wr₃ := h₃.wr.trans wr₂
  have buf₃ := (h₃.reg .x2 (by decide) (by decide) (by decide)).trans buf₂
  have reads (i : Nat) (hi : i + 8 ≤ 512) :
      InRegions (s₃.rd ++ s₃.wr) (s₃.gpr .x2 + BitVec.ofNat 64 i) 8 := by
    rw [rd₃, wr₃, buf₃]
    obtain ⟨r, hr, hc⟩ := writes i hi
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have hsv : Spill.Saved (s₃.gpr .x2) s.gpr VG.Proof.Rc2.AArch64.Cbc.saved s₃.mem := fun p hp => by
    have hb : 264 ≤ p.2 ∧ p.2 + 8 ≤ 512 := by revert p; decide
    have h := h₃.scratchRead hp₂ p.2 hb.1 hb.2
    rw [buf₂, mem₂] at h
    rw [buf₃, h]
    exact Spill.saveMem_saved (by decide) _ _ _ p hp
  rw [VG.Proof.Rc2.AArch64.Cbc.restore_eq]
  refine WP.mono (Spill.restore_wp rfl (by decide) (by decide)
    (fun p hp => reads p.2 (by revert p; decide)) hsv) fun s₄ h₄ => ?_
  constructor
  · intro r hr
    by_cases hs : r ∈ saved.map Prod.fst
    · exact h₄.gpr_of (.inl hs)
    have hb : r ≠ .x23 ∧ r ≠ .x24 ∧ r ≠ .x30 := by
      simpa only [VG.Proof.Rc2.AArch64.Cbc.saved, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
        not_or] using hs
    have hsa : ∀ r ∈ preserved, r ≠ .x30 → r ∈ VG.Proof.Rc2.AArch64.Cbc.savedAcrossCall := by decide
    have sep : ∀ r ∈ preserved, r ≠ .x23 → r ≠ .x24 → r ∉ [.x23, .x24, .x1, .x2] := by decide
    rw [h₄.other r hs, h₃.callee r (hsa r hr hb.2.2) hb.2.1]
    exact keep₂.reg r (sep r hr hb.1 hb.2.1)
  · have out := h₃.data
    have iv := h₃.iv
    rw [key₂, iv₂, data₂, initialKey, initialIv, initialData] at out iv
    constructor
    · rw [h₄.mem]; exact out
    · rw [h₄.mem]; exact iv

def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x4 => 0x4000 | _ => 0
  sp := 0x6000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0x4000, 512⟩]

theorem encrypt_correct (s : State) (hs : (VG.Proof.Rc2.AArch64.Cbc.contract .encrypt).pre s) :
    ∃ t s', Exec isa Impl.Rc2.AArch64.Cbc.encrypt s t s' ∧ abiPreserved s s' ∧
      (VG.Proof.Rc2.AArch64.Cbc.contract .encrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := VG.Proof.Rc2.AArch64.Cbc.cbc_body_correct .encrypt _
    (fun s n bound hp count => VG.Proof.Rc2.AArch64.Cbc.maybeLoop_ok .encrypt s n bound hp count) s hs
  change Exec isa Impl.Rc2.AArch64.Cbc.encrypt s t s' at he
  exact ⟨t, s', he, ⟨ha, (VG.AArch64.Exec.regions he rfl).2.2.1, VG.AArch64.Exec.preservedV he (by lit_decide)⟩, hp⟩

theorem decrypt_correct (s : State) (hs : (VG.Proof.Rc2.AArch64.Cbc.contract .decrypt).pre s) :
    ∃ t s', Exec isa Impl.Rc2.AArch64.Cbc.decrypt s t s' ∧ abiPreserved s s' ∧
      (VG.Proof.Rc2.AArch64.Cbc.contract .decrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := VG.Proof.Rc2.AArch64.Cbc.cbc_body_correct .decrypt _
    (fun s n bound hp count => VG.Proof.Rc2.AArch64.Cbc.phaseLoop_ok s n bound hp count) s hs
  change Exec isa Impl.Rc2.AArch64.Cbc.decrypt s t s' at he
  exact ⟨t, s', he, ⟨ha, (VG.AArch64.Exec.regions he rfl).2.2.1, VG.AArch64.Exec.preservedV he (by lit_decide)⟩, hp⟩

theorem publicRegs_five (s₁ s₂ : State) : PublicRegs [.x0, .x1, .x2, .x3, .x4] s₁ s₂ ↔
    s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 := by
  simp [PublicRegs]

theorem encrypt_verified : Verified target Impl.Rc2.AArch64.Cbc.encrypt (Spec.Rc2.cbcEncryptContract abi 0) := by
  refine Verified.of_correct VG.Proof.Rc2.AArch64.Cbc.encrypt_correct (VG.Proof.Rc2.AArch64.Cbc.encrypt_constantTime _) ?_
  sig_implies [Spec.Rc2.cbcEncryptContract, Spec.Rc2.cbcContract, Spec.Rc2.cbcSig, abi, argRegs,
    VG.Proof.Rc2.AArch64.Cbc.contract, VG.Proof.Rc2.AArch64.Cbc.publicRegs_five] [satState] using VG.Proof.Rc2.AArch64.Cbc.satState

theorem decrypt_verified : Verified target Impl.Rc2.AArch64.Cbc.decrypt (Spec.Rc2.cbcDecryptContract abi 0) := by
  refine Verified.of_correct VG.Proof.Rc2.AArch64.Cbc.decrypt_correct (VG.Proof.Rc2.AArch64.Cbc.decrypt_constantTime _) ?_
  sig_implies [Spec.Rc2.cbcDecryptContract, Spec.Rc2.cbcContract, Spec.Rc2.cbcSig, abi, argRegs,
    VG.Proof.Rc2.AArch64.Cbc.contract, VG.Proof.Rc2.AArch64.Cbc.publicRegs_five] [satState] using VG.Proof.Rc2.AArch64.Cbc.satState

end VG.Proof.Rc2.AArch64.Cbc

end
