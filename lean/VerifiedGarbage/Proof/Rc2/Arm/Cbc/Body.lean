import VerifiedGarbage.Proof.Rc2.Arm.KeyLoop
import VerifiedGarbage.Proof.Rc2.CbcMemory
import VerifiedGarbage.Proof.Rc2.Arm.KeySteps
import VerifiedGarbage.Proof.Rc2.PairMem
import VerifiedGarbage.Proof.Rc2.Arm.Block
import VerifiedGarbage.Impl.Rc2.Arm.Cbc
import VerifiedGarbage.Proof.Framework.Arm.Call

section

section

/-! # Calling the verified block primitive from CBC -/

namespace VG.Proof.Rc2.Arm.Cbc

open VG VG.Arm VG.Impl.Rc2.Arm

def savedAcrossCall : List Reg := [.r8, .r9, .r10, .r11]

def args : List Reg := [.r0, .r1, .r2]

def kept : List Reg := [.r0, .r1, .r2, .r4, .r5]

theorem block_keeps (d : Spec.Rc2.Direction) :
    ((instrs (.block (blockCode d) : Prog isa)).all fun i => args.all fun r => decide (dstOf i ≠ some r)) = true := by
  cases d
  · change ((instrs encryptBlock).all _) = true
    rw [← Code.allInstrs_eq]; lit_decide
  · change ((instrs decryptBlock).all _) = true
    rw [← Code.allInstrs_eq]; lit_decide

theorem block_keeps_reg (d : Spec.Rc2.Direction) {r : Reg} (hr : r ∈ args) :
    ∀ i ∈ instrs (.block (blockCode d) : Prog isa), dstOf i ≠ some r := by
  intro i hi
  have h := List.all_eq_true.mp (List.all_eq_true.mp (block_keeps d) i hi) r hr
  simpa using h

theorem block_correct' (d : Spec.Rc2.Direction) (s : State) (hs : (blockContract d).pre s) :
    ∃ t s', Exec isa (.block (blockCode d)) s t s' ∧ abiPreserved s s' ∧ (blockContract d).post s s' := by
  cases d
  · exact encrypt_correct s hs
  · exact decrypt_correct s hs

theorem blockCall_eq (d : Spec.Rc2.Direction) : Impl.Rc2.Arm.Cbc.blockCall d =
    .call (match d with | .encrypt => "vg_rc2_encrypt_block" | .decrypt => "vg_rc2_decrypt_block")
      (.block (blockCode d)) := by cases d <;> rfl

structure CallPre (s : State) : Prop where
  reads : Covers [⟨State.addr (s.gpr .r0), 128⟩, ⟨State.addr (s.gpr .r1), 8⟩, ⟨State.addr (s.gpr .r2), 256⟩] (s.rd ++ s.wr)
  writes : Covers [⟨State.addr (s.gpr .r1), 8⟩, ⟨State.addr (s.gpr .r2), 256⟩] s.wr
  keyScratch : (Region.mk (State.addr (s.gpr .r0)) 128).Disjoint ⟨State.addr (s.gpr .r2), 256⟩
  keyFit : (s.gpr .r0).toNat + 128 ≤ 2 ^ 32
  dataFit : (s.gpr .r1).toNat + 8 ≤ 2 ^ 32
  bufFit : (s.gpr .r2).toNat + 256 ≤ 2 ^ 32
  dataScratch : (Region.mk (State.addr (s.gpr .r1)) 8).Disjoint ⟨State.addr (s.gpr .r2), 256⟩

structure CallPost (d : Spec.Rc2.Direction) (s s' : State) : Prop where
  reg : ∀ r ∈ kept, s'.gpr r = s.gpr r
  callee : ∀ r ∈ savedAcrossCall, s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame [⟨State.addr (s.gpr .r1), 8⟩, ⟨State.addr (s.gpr .r2), 256⟩] s.mem s'.mem
  output : Spec.Rc2.blockAt s'.mem (State.addr (s.gpr .r1)) =
    cipher d (Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))) (Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r1)))

theorem call_ok (d : Spec.Rc2.Direction) (s : State) (hp : CallPre s) :
    WP isa (Impl.Rc2.Arm.Cbc.blockCall d) s (CallPost d s) := by
  rw [blockCall_eq]
  refine WP.call (k := blockContract d) (block_correct' d)
    (rd := [⟨State.addr (s.gpr .r0), 128⟩]) (wr := [⟨State.addr (s.gpr .r1), 8⟩, ⟨State.addr (s.gpr .r2), 256⟩]) ?_ hp.reads hp.writes ?_ (by rfl)
  · simp only [blockContract, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs)]
    exact ⟨trivial, trivial, hp.keyScratch, hp.dataScratch, hp.keyFit, hp.dataFit, hp.bufFit⟩
  · intro s' rd wr sp frame callee regs out
    have sep : ∀ r ∈ kept, r ∉ linkRegs := by decide
    have saved : ∀ r ∈ savedAcrossCall, r ∈ preserved ∧ r ≠ .lr := by decide
    refine ⟨fun r hr => ?_,
      fun r hr => callee r (saved r hr).1 (saved r hr).2, rd, wr, frame, ?_⟩
    · by_cases ha : r ∈ args
      · exact regs r (block_keeps_reg d ha) (sep r hr)
      · have saved : ∀ r ∈ kept, r ∉ args → r ∈ preserved ∧ r ≠ .lr := by decide
        exact callee r (saved r hr ha).1 (saved r hr ha).2
    · change Spec.Rc2.blockAt s'.mem _ = cipher d _ _ at out
      simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
      State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs)] at out
      exact out

end VG.Proof.Rc2.Arm.Cbc

end

section

section

/-! # Pair loads and stores for 64-bit CBC blocks -/

namespace VG.Proof.Rc2.Arm.Cbc

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc2.Arm VG.Proof.Rc2.Word32

theorem halves {rs : List Region} {p : Addr} (h : InRegions rs p 8) :
    InRegions rs p 4 ∧ InRegions rs (p + BitVec.ofNat 64 4) 4 := by
  obtain ⟨r, hr, hc⟩ := h
  constructor
  · exact ⟨r, hr, by unfold Region.Contains at hc ⊢; omega⟩
  · refine ⟨r, hr, ?_⟩
    unfold Region.Contains at hc ⊢
    rw [BitVec.add_sub_comm, BitVec.toNat_add]
    have bound := Nat.mod_le ((p - r.base).toNat + (BitVec.ofNat 64 4).toNat) (2 ^ 64)
    change ((p - r.base).toNat + 4) % 2 ^ 64 + 4 ≤ r.len
    change ((p - r.base).toNat + 4) % 2 ^ 64 ≤ (p - r.base).toNat + 4 at bound
    omega

theorem loadPair_ok (s : State) (lo hi src : Reg) (a : Nat)
    (different : lo ≠ hi) (sep : src ≠ lo) (bound : a + 4 < 4096)
    (fit : (s.gpr src).toNat + a + 8 ≤ 2 ^ 32)
    (readable : InRegions (s.rd ++ s.wr) (State.addr (s.gpr src) + BitVec.ofNat 64 a) 8) :
    ∃ s', runBlock isa [.ldr lo src a, .ldr hi src (a + 4)] s = some s' ∧
      s'.gpr lo = s.mem.readW (State.addr (s.gpr src) + BitVec.ofNat 64 a) 32 ∧
      s'.gpr hi = s.mem.readW (State.addr (s.gpr src) + BitVec.ofNat 64 (a + 4)) 32 ∧
      Keep [lo, hi] s s' := by
  obtain ⟨rd0, rd4⟩ := halves readable
  rw [BitVec.add_assoc, ← BitVec.ofNat_add] at rd4
  rw [runBlock_cons, exec_ldr s lo src a (by omega) (by omega) rd0, runStep_some]
  have rd4' : InRegions ((s.setReg lo (s.mem.readW (State.addr (s.gpr src) + BitVec.ofNat 64 a) 32)).rd ++
      (s.setReg lo (s.mem.readW (State.addr (s.gpr src) + BitVec.ofNat 64 a) 32)).wr)
      (State.addr ((s.setReg lo (s.mem.readW (State.addr (s.gpr src) + BitVec.ofNat 64 a) 32)).gpr src) +
        BitVec.ofNat 64 (a + 4)) 4 := by
    simpa only [rd_setReg, wr_setReg, gpr_setReg_of_ne _ _ sep] using rd4
  rw [runBlock_cons, exec_ldr _ hi src (a + 4) bound
    (by rw [gpr_setReg_of_ne _ _ sep]; omega) rd4', runStep_some, runBlock_nil]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · rw [gpr_setReg_of_ne _ _ different, gpr_setReg_self]
  · rw [gpr_setReg_self, gpr_setReg_of_ne _ _ sep, mem_setReg]
  · refine ⟨?_, rfl, rfl, rfl⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [gpr_setReg_of_ne _ _ hr.2, gpr_setReg_of_ne _ _ hr.1]

theorem storePair_ok (s : State) (lo hi dst : Reg) (b : Nat) (bound : b + 4 < 4096)
    (fit : (s.gpr dst).toNat + b + 8 ≤ 2 ^ 32)
    (writable : InRegions s.wr (State.addr (s.gpr dst) + BitVec.ofNat 64 b) 8) :
    ∃ s', runBlock isa [.str lo dst b, .str hi dst (b + 4)] s = some s' ∧
      Keep [] {s with
        mem := s.mem.writeW (State.addr (s.gpr dst) + BitVec.ofNat 64 b)
          (s.gpr hi ++ s.gpr lo)} s' := by
  obtain ⟨wr0, wr4⟩ := halves writable
  rw [BitVec.add_assoc, ← BitVec.ofNat_add] at wr4
  rw [runBlock_cons, exec_str s lo dst b (by omega) (by omega) wr0, runStep_some,
    runBlock_cons, exec_str {s with mem := s.mem.writeW (State.addr (s.gpr dst) + BitVec.ofNat 64 b) (s.gpr lo)} hi dst (b + 4) bound (by change (s.gpr dst).toNat + (b + 4) < 2 ^ 32; omega) wr4,
    runStep_some, runBlock_nil]
  refine ⟨_, rfl, fun _ _ => rfl, ?_, rfl, rfl⟩
  rw [write64_pair, BitVec.add_assoc, ← BitVec.ofNat_add]

end VG.Proof.Rc2.Arm.Cbc

end

/-! # CBC loads, XORs, stores, and public loop counters -/

namespace VG.Proof.Rc2.Arm.Cbc

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc2.Arm VG.Proof.Rc2.Word32

def temps : List Reg := [.r12, .r3, .r6, .r7]

theorem copy64_ok (s : State) (src dst : Reg) (a b : Nat)
    (srcSep : src ≠ .r12) (dstSep : dst ≠ .r12 ∧ dst ≠ .r3)
    (srcFit : (s.gpr src).toNat + a + 8 ≤ 2 ^ 32)
    (dstFit : (s.gpr dst).toNat + b + 8 ≤ 2 ^ 32)
    (readable : InRegions (s.rd ++ s.wr) (State.addr (s.gpr src) + BitVec.ofNat 64 a) 8)
    (writable : InRegions s.wr (State.addr (s.gpr dst) + BitVec.ofNat 64 b) 8)
    (ha : a + 4 < 4096 := by decide) (hb : b + 4 < 4096 := by decide) :
    WP isa (.block (Impl.Rc2.Arm.Cbc.copy64 src dst a b)) s (fun s' =>
      Keep temps {s with
        mem := s.mem.writeW (State.addr (s.gpr dst) + BitVec.ofNat 64 b)
          (s.mem.readW (State.addr (s.gpr src) + BitVec.ofNat 64 a) 64)} s') := by
  change WP isa (.block (([.ldr .r12 src a, .ldr .r3 src (a + 4)] : List Instr) ++
    [.str .r12 dst b, .str .r3 dst (b + 4)])) s _
  rw [WP.block_append_iff]
  obtain ⟨s₁, run₁, lo₁, hi₁, keep₁⟩ := loadPair_ok s .r12 .r3 src a (by decide) srcSep ha srcFit readable
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have ptr := keep₁.reg dst (by simpa only [List.mem_cons, List.not_mem_nil, or_false, not_or] using dstSep)
  obtain ⟨s₂, run₂, keep₂⟩ := storePair_ok s₁ .r12 .r3 dst b hb
    (by rw [ptr]; exact dstFit) (by rw [keep₁.wr, ptr]; exact writable)
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  constructor
  · intro r hr
    exact (keep₂.reg r (by simp)).trans (keep₁.reg r (by
      intro h; exact hr (by simp only [temps, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; grind)))
  · rw [keep₂.mem, ptr, hi₁, lo₁, keep₁.mem, ← Offset.add_ofNat_add_ofNat, ← read64_pair]
  · exact keep₂.rd.trans keep₁.rd
  · exact keep₂.wr.trans keep₁.wr

theorem xorPair_ok (s : State) :
    ∃ s', runBlock isa [.dp .eor .r12 .r12 (.reg .r6), .dp .eor .r3 .r3 (.reg .r7)] s = some s' ∧
      s'.gpr .r12 = s.gpr .r12 ^^^ s.gpr .r6 ∧ s'.gpr .r3 = s.gpr .r3 ^^^ s.gpr .r7 ∧
      Keep [.r12, .r3] s s' := by
  refine ⟨_, by
    simp only [runBlock_cons, exec, Op2.eval, Option.map_some, runStep_some, runBlock_nil, gpr_setReg]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_setReg, reduceCtorEq, ite_false, ite_true]
  · simp only [gpr_setReg, reduceCtorEq, ite_false, ite_true]
  · refine ⟨?_, rfl, rfl, rfl⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [gpr_setReg_of_ne _ _ hr.2, gpr_setReg_of_ne _ _ hr.1]

theorem xor64_ok (s : State) (dst iv : Reg)
    (dstSep : dst ∉ temps) (ivSep : iv ∉ temps)
    (dstFit : (s.gpr dst).toNat + 8 ≤ 2 ^ 32) (ivFit : (s.gpr iv).toNat + 8 ≤ 2 ^ 32)
    (readDst : InRegions (s.rd ++ s.wr) (State.addr (s.gpr dst)) 8)
    (readIv : InRegions (s.rd ++ s.wr) (State.addr (s.gpr iv)) 8)
    (writable : InRegions s.wr (State.addr (s.gpr dst)) 8) :
    WP isa (.block (Impl.Rc2.Arm.Cbc.xor64 dst iv)) s (fun s' =>
      Keep temps {s with
        mem := s.mem.writeW (State.addr (s.gpr dst))
          (s.mem.readW (State.addr (s.gpr dst)) 64 ^^^ s.mem.readW (State.addr (s.gpr iv)) 64)} s') := by
  have ds : dst ≠ .r12 ∧ dst ≠ .r3 ∧ dst ≠ .r6 ∧ dst ≠ .r7 := by simpa [temps] using dstSep
  have vs : iv ≠ .r12 ∧ iv ≠ .r3 ∧ iv ≠ .r6 ∧ iv ≠ .r7 := by simpa [temps] using ivSep
  change WP isa (.block (([.ldr .r12 dst 0, .ldr .r3 dst 4] : List Instr) ++
    (([.ldr .r6 iv 0, .ldr .r7 iv 4] : List Instr) ++
      (([.dp .eor .r12 .r12 (.reg .r6), .dp .eor .r3 .r3 (.reg .r7)] : List Instr) ++
        [.str .r12 dst 0, .str .r3 dst 4])))) s _
  rw [WP.block_append_iff]
  obtain ⟨s₁, run₁, lo₁, hi₁, keep₁⟩ := loadPair_ok s .r12 .r3 dst 0 (by decide) ds.1 (by decide)
    (by simpa using dstFit) (by simpa using readDst)
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have iv₁ := keep₁.reg iv (by simp [vs.1, vs.2.1])
  rw [WP.block_append_iff]
  obtain ⟨s₂, run₂, lo₂, hi₂, keep₂⟩ := loadPair_ok s₁ .r6 .r7 iv 0 (by decide) vs.2.2.1 (by decide)
    (by rw [iv₁]; simpa using ivFit) (by rw [keep₁.rd, keep₁.wr, iv₁]; simpa using readIv)
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  rw [WP.block_append_iff]
  obtain ⟨s₃, run₃, lo₃, hi₃, keep₃⟩ := xorPair_ok s₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have keep : Keep temps s s₃ :=
    ((keep₁.weaken (by simp [temps])).trans (keep₂.weaken (by simp [temps]))).trans
      (keep₃.weaken (by simp [temps]))
  have ptr := keep.reg dst dstSep
  obtain ⟨s₄, run₄, keep₄⟩ := storePair_ok s₃ .r12 .r3 dst 0 (by decide)
    (by rw [ptr]; simpa using dstFit) (by rw [keep.wr, ptr]; simpa using writable)
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  refine ⟨fun r hr => (keep₄.reg r (by simp)).trans (keep.reg r hr), ?_,
    keep₄.rd.trans keep.rd, keep₄.wr.trans keep.wr⟩
  rw [keep₄.mem, keep.mem, ptr, BitVec.add_zero, hi₃, lo₃, lo₂, hi₂,
    keep₂.reg .r12 (by decide), keep₂.reg .r3 (by decide), lo₁, hi₁, keep₁.mem, iv₁]
  simp only [Nat.zero_add, BitVec.add_zero]
  rw [pair_xor, ← read64_pair, ← read64_pair]

def zeroCount (s : State) : Option Bool := some s.z

theorem eval_zeroCount (s : State) : eval .eq s = zeroCount s := rfl

theorem eval_nonzeroCount (s : State) : eval .ne s = (zeroCount s).map (! ·) := rfl

theorem advance_ok (s : State) :
    ∃ s', runBlock isa Impl.Rc2.Arm.Cbc.advance s = some s' ∧
      s'.gpr .r1 = s.gpr .r1 + 8 ∧ s'.gpr .r5 = s.gpr .r5 - 1 ∧
      zeroCount s' = some ((s.gpr .r5 - 1) == 0) ∧ Keep [.r1, .r5] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [Impl.Rc2.Arm.Cbc.advance, runBlock_cons, runStep_some,
      runBlock_nil, exec, Op2.eval, Option.map_some, ite_true, gpr_setReg, ite_false]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [gpr_subFlags, gpr_setReg, reduceCtorEq, ite_false, ite_true]
  · simp only [gpr_subFlags, gpr_setReg_self]
  · change some ((s.gpr .r5 - 1 - 0) == 0) = _
    exact congrArg (fun x : BitVec 32 => some (x == 0)) (by bv_omega)
  · refine ⟨?_, rfl, rfl, rfl⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [gpr_subFlags, gpr_setReg_of_ne _ _ hr.2, gpr_setReg_of_ne _ _ hr.1]

end VG.Proof.Rc2.Arm.Cbc

end

section

/-! # Permissions and separation for one CBC step -/

namespace VG.Proof.Rc2.Arm.Cbc

open VG VG.Arm

abbrev keyR (s : State) : Region := ⟨State.addr (s.gpr .r0), 128⟩
abbrev ivR (s : State) : Region := ⟨State.addr (s.gpr .r4), 8⟩
abbrev dataR (s : State) (n : Nat := 1) : Region := ⟨State.addr (s.gpr .r1), 8 * n⟩
abbrev bufR (s : State) : Region := ⟨State.addr (s.gpr .r2), 512⟩

structure StepPre (s : State) (n : Nat := 1) : Prop where
  keyFit : (s.gpr .r0).toNat + 128 ≤ 2 ^ 32
  ivFit : (s.gpr .r4).toNat + 8 ≤ 2 ^ 32
  dataFit : (s.gpr .r1).toNat + 8 * n ≤ 2 ^ 32
  bufFit : (s.gpr .r2).toNat + 512 ≤ 2 ^ 32
  reads : Covers [keyR s, ivR s, dataR s n, bufR s] (s.rd ++ s.wr)
  writes : Covers [ivR s, dataR s n, bufR s] s.wr
  keyIv : (keyR s).Disjoint (ivR s)
  keyData : (keyR s).Disjoint (dataR s n)
  keyBuf : (keyR s).Disjoint (bufR s)
  ivData : (ivR s).Disjoint (dataR s n)
  ivBuf : (ivR s).Disjoint (bufR s)
  dataBuf : (dataR s n).Disjoint (bufR s)

theorem StepPre.transport {s s' : State} {n : Nat} (hp : StepPre s n)
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) (regs : ∀ r ∈ kept, s'.gpr r = s.gpr r) : StepPre s' n := by
  have a := regs .r0 (by decide)
  have b := regs .r4 (by decide)
  have c := regs .r1 (by decide)
  have d := regs .r2 (by decide)
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

theorem StepPre.keep {s s' : State} {m : Mem} {n : Nat} (hp : StepPre s n) (h : Keep [.r12, .r3, .r6, .r7] {s with mem := m} s') : StepPre s' n :=
  hp.transport h.rd h.wr fun r hr => h.reg r (by
    have sep : ∀ r ∈ kept, r ∉ [.r12, .r3, .r6, .r7] := by decide
    exact sep r hr)

theorem StepPre.call {s : State} (hp : StepPre s) : CallPre s := by
  constructor
  · have hc : Covers [⟨State.addr (s.gpr .r0), 128⟩, ⟨State.addr (s.gpr .r1), 8⟩, ⟨State.addr (s.gpr .r2), 256⟩]
        [keyR s, ivR s, dataR s, bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨keyR s, by simp, 0, by simp, by simp⟩
      · exact ⟨dataR s, by simp, 0, by simp, by simp⟩
      · exact ⟨bufR s, by simp, 0, by simp, by simp⟩
    exact fun a n h => hp.reads a n (hc a n h)
  · have hc : Covers [⟨State.addr (s.gpr .r1), 8⟩, ⟨State.addr (s.gpr .r2), 256⟩] [ivR s, dataR s, bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨dataR s, by simp, 0, by simp, by simp⟩
      · exact ⟨bufR s, by simp, 0, by simp, by simp⟩
    exact fun a n h => hp.writes a n (hc a n h)
  · exact hp.keyBuf.sub_right (Region.sub_prefix (by decide))
  · exact hp.keyFit
  · simpa only [Nat.mul_one] using hp.dataFit
  · have := hp.bufFit; omega
  · exact hp.dataBuf.sub_right (Region.sub_prefix (by decide))

theorem StepPre.readData {s : State} (hp : StepPre s) : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r1)) 8 :=
  hp.reads _ _ ⟨dataR s, by simp, Region.contains_self _ _⟩

theorem StepPre.readIv {s : State} (hp : StepPre s) : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r4)) 8 :=
  hp.reads _ _ ⟨ivR s, by simp, Region.contains_self _ _⟩

theorem StepPre.writeData {s : State} (hp : StepPre s) : InRegions s.wr (State.addr (s.gpr .r1)) 8 :=
  hp.writes _ _ ⟨dataR s, by simp, Region.contains_self _ _⟩

theorem StepPre.writeIv {s : State} (hp : StepPre s) : InRegions s.wr (State.addr (s.gpr .r4)) 8 :=
  hp.writes _ _ ⟨ivR s, by simp, Region.contains_self _ _⟩

theorem StepPre.readBuf {s : State} (hp : StepPre s) (i : Nat) (hi : i + 8 ≤ 512) :
    InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r2) + BitVec.ofNat 64 i) 8 :=
  hp.reads _ _ ⟨bufR s, by simp, Offset.contains_base _ hi (by omega)⟩

theorem StepPre.writeBuf {s : State} (hp : StepPre s) (i : Nat) (hi : i + 8 ≤ 512) :
    InRegions s.wr (State.addr (s.gpr .r2) + BitVec.ofNat 64 i) 8 :=
  hp.writes _ _ ⟨bufR s, by simp, Offset.contains_base _ hi (by omega)⟩

end VG.Proof.Rc2.Arm.Cbc

end

/-! # The frame preserved by a CBC step -/

namespace VG.Proof.Rc2.Arm.Cbc

open VG VG.Arm

def stepWrites (s : State) : List Region := [ivR s, dataR s, ⟨State.addr (s.gpr .r2), 264⟩]

structure Pinned (s s' : State) : Prop where
  reg : ∀ r ∈ kept, s'.gpr r = s.gpr r
  callee : ∀ r ∈ savedAcrossCall, s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame (stepWrites s) s.mem s'.mem

theorem Pinned.of_keep {s s' : State} {m : Mem} (h : Keep [.r12, .r3, .r6, .r7] {s with mem := m} s')
    (frame : Frame (stepWrites s) s.mem m) : Pinned s s' := by
  have k : ∀ r ∈ kept, r ∉ [.r12, .r3, .r6, .r7] := by decide
  have c : ∀ r ∈ savedAcrossCall, r ∉ [.r12, .r3, .r6, .r7] := by decide
  exact ⟨fun r hr => h.reg r (k r hr), fun r hr => h.reg r (c r hr), h.rd, h.wr, by rw [h.mem]; exact frame⟩

theorem Pinned.of_call {d : Spec.Rc2.Direction} {s s' : State} (h : CallPost d s s') : Pinned s s' := by
  refine ⟨h.reg, h.callee, h.rd, h.wr, h.mem.sub ?_⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨dataR s, by simp [stepWrites], fun _ h => h⟩
  · exact ⟨⟨State.addr (s.gpr .r2), 264⟩, by simp [stepWrites], Region.sub_prefix (by decide)⟩

theorem Pinned.writes_eq {s s' : State} (h : Pinned s s') : stepWrites s' = stepWrites s := by
  simp only [stepWrites, ivR, dataR, h.reg .r4 (by decide), h.reg .r1 (by decide), h.reg .r2 (by decide)]

theorem Pinned.trans {s s' s'' : State} (h : Pinned s s') (h' : Pinned s' s'') : Pinned s s'' := by
  refine ⟨fun r hr => (h'.reg r hr).trans (h.reg r hr), fun r hr => (h'.callee r hr).trans (h.callee r hr),
    h'.rd.trans h.rd, h'.wr.trans h.wr, ?_⟩
  have f := h'.mem
  rw [h.writes_eq] at f
  exact h.mem.trans f

theorem Pinned.pre {s s' : State} {n : Nat} (h : Pinned s s') (hp : StepPre s n) : StepPre s' n :=
  hp.transport h.rd h.wr h.reg

theorem Pinned.schedule {s s' : State} (h : Pinned s s') (hp : StepPre s) :
    Spec.Rc2.scheduleAt s'.mem (State.addr (s.gpr .r0)) = Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0)) := by
  apply scheduleAt_frame h.mem
  simpa only [stepWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro hp.keyIv (And.intro hp.keyData
      (hp.keyBuf.sub_right (Region.sub_prefix (by decide : 264 ≤ 512))))

theorem CallPost.iv {d : Spec.Rc2.Direction} {s s' : State} (h : CallPost d s s') (hp : StepPre s) :
    Spec.Rc2.blockAt s'.mem (State.addr (s.gpr .r4)) = Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r4)) := by
  apply blockAt_frame h.mem
  simpa only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro hp.ivData
      (hp.ivBuf.sub_right (Region.sub_prefix (by decide : 256 ≤ 512)))

structure StepPost (d : Spec.Rc2.Direction) (s s' : State) : Prop extends Pinned s s' where
  data : Spec.Rc2.blockAt s'.mem (State.addr (s.gpr .r1)) =
    (Spec.Rc2.cbcStep (Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))) d
      (Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r4))) (Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r1)))).1
  iv : Spec.Rc2.blockAt s'.mem (State.addr (s.gpr .r4)) =
    (Spec.Rc2.cbcStep (Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))) d
      (Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r4))) (Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r1)))).2

end VG.Proof.Rc2.Arm.Cbc

end

section

/-! # One CBC decryption step, retaining the original ciphertext -/

namespace VG.Proof.Rc2.Arm.Cbc

open VG VG.Arm VG.Impl.Rc2.Arm

abbrev stashR (s : State) : Region := ⟨State.addr (s.gpr .r2) + BitVec.ofNat 64 256, 8⟩

theorem stash_sub (s : State) : Region.Sub (stashR s) (bufR s) :=
  Offset.sub_base _ (by decide)

theorem call_stash {d : Spec.Rc2.Direction} {s s' : State} (hp : StepPre s) (h : CallPost d s s') :
    Spec.Rc2.blockAt s'.mem (stashR s).base = Spec.Rc2.blockAt s.mem (stashR s).base := by
  apply blockAt_frame h.mem
  have sep : (stashR s).Disjoint ⟨State.addr (s.gpr .r2), 256⟩ := by
    have h := Offset.disjoint (State.addr (s.gpr .r2)) (d := 256) (n := 8) (e := 0) (k := 256)
      (by omega) (by decide) (by decide)
    simpa using h
  simpa only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro ((hp.dataBuf.sub_right (stash_sub s)).symm) sep

theorem decryptStep_ok (s : State) (hp : StepPre s) :
    WP isa (Impl.Rc2.Arm.Cbc.step .decrypt) s (StepPost .decrypt s) := by
  rw [Impl.Rc2.Arm.Cbc.step]
  apply WP.seq
  apply WP.mono (copy64_ok s .r1 .r2 0 256 (by decide) (by decide)
    (by simpa using hp.dataFit) (by have := hp.bufFit; omega) (by simpa using hp.readData) (hp.writeBuf 256 (by decide)))
  intro s₁ keep₁
  simp only [BitVec.add_zero] at keep₁
  have frame₁ : Frame [stashR s] s.mem s₁.mem := by
    rw [keep₁.mem]; exact frame_store64 _ _ _
  have pin₁ : Pinned s s₁ := by
    apply Pinned.of_keep keep₁
    apply (frame_store64 _ _ _).sub
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact ⟨⟨State.addr (s.gpr .r2), 264⟩, by simp [stepWrites], Offset.sub_base _ (by decide)⟩
  have hp₁ := pin₁.pre hp
  have key₁ := pin₁.schedule hp
  have data₁ := blockAt_frame frame₁ (State.addr (s.gpr .r1)) (by simpa using hp.dataBuf.sub_right (stash_sub s))
  have iv₁ := blockAt_frame frame₁ (State.addr (s.gpr .r4)) (by simpa using hp.ivBuf.sub_right (stash_sub s))
  have stash₁ : Spec.Rc2.blockAt s₁.mem (stashR s).base = Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r1)) := by
    rw [keep₁.mem]; exact blockAt_copy _ _ _
  apply WP.seq
  apply WP.mono (call_ok .decrypt s₁ hp₁.call)
  intro s₂ h₂
  have pin₂ := pin₁.trans (Pinned.of_call h₂)
  have hp₂ := pin₂.pre hp
  have output₂ := h₂.output
  rw [pin₁.reg .r1 (by decide), pin₁.reg .r0 (by decide), key₁, data₁] at output₂
  have iv₂ := h₂.iv hp₁
  rw [pin₁.reg .r4 (by decide), iv₁] at iv₂
  have stash₂ := call_stash hp₁ h₂
  simp only [pin₁.reg .r2 (by decide)] at stash₂
  have stash₂' := stash₂.trans stash₁
  change WP isa (.block (Impl.Rc2.Arm.Cbc.xor64 .r1 .r4 ++
    Impl.Rc2.Arm.Cbc.copy64 .r2 .r4 256 0)) s₂ _
  rw [WP.block_append_iff]
  apply WP.mono (xor64_ok s₂ .r1 .r4 (by decide) (by decide)
    (by simpa using hp₂.dataFit) hp₂.ivFit hp₂.readData hp₂.readIv hp₂.writeData)
  intro s₃ keep₃
  have frame₃ : Frame [dataR s₂] s₂.mem s₃.mem := by
    rw [keep₃.mem]; exact frame_store64 _ _ _
  have pin₃ := Pinned.of_keep keep₃ ((frame_store64 _ _ _).mono (by simp [stepWrites]))
  have pin₀₃ := pin₂.trans pin₃
  have hp₃ := pin₀₃.pre hp
  have data₃ : Spec.Rc2.blockAt s₃.mem (State.addr (s.gpr .r1)) =
      Spec.Rc2.xorBlock (Spec.Rc2.decryptBlock (Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0)))
        (Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r1)))) (Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r4))) := by
    have h : Spec.Rc2.blockAt s₃.mem (State.addr (s₂.gpr .r1)) =
        Spec.Rc2.xorBlock (Spec.Rc2.blockAt s₂.mem (State.addr (s₂.gpr .r1))) (Spec.Rc2.blockAt s₂.mem (State.addr (s₂.gpr .r4))) := by
      rw [keep₃.mem]; exact blockAt_xor _ _ _
    rw [pin₂.reg .r1 (by decide), pin₂.reg .r4 (by decide), output₂, iv₂] at h
    exact h
  have stash₃ := blockAt_frame frame₃ (stashR s₂).base
    (by simpa using (hp₂.dataBuf.sub_right (stash_sub s₂)).symm)
  simp only [pin₂.reg .r2 (by decide)] at stash₃
  have stash₃' := stash₃.trans stash₂'
  apply WP.mono (copy64_ok s₃ .r2 .r4 256 0 (by decide) (by decide)
    (by have := hp₃.bufFit; omega) (by simpa using hp₃.ivFit) (hp₃.readBuf 256 (by decide)) (by simpa using hp₃.writeIv))
  intro s₄ keep₄
  simp only [BitVec.add_zero] at keep₄
  have frame₄ : Frame [ivR s₃] s₃.mem s₄.mem := by
    rw [keep₄.mem]; exact frame_store64 _ _ _
  have pin₄ := Pinned.of_keep keep₄ ((frame_store64 _ _ _).mono (by simp [stepWrites]))
  refine ⟨pin₀₃.trans pin₄, ?_, ?_⟩
  · have same := blockAt_frame frame₄ (State.addr (s₃.gpr .r1)) (by simpa using hp₃.ivData.symm)
    rw [pin₀₃.reg .r1 (by decide)] at same
    exact same.trans data₃
  · have out : Spec.Rc2.blockAt s₄.mem (State.addr (s₃.gpr .r4)) = Spec.Rc2.blockAt s₃.mem (stashR s₃).base := by
      rw [keep₄.mem]; exact blockAt_copy _ _ _
    simp only [pin₀₃.reg .r4 (by decide), pin₀₃.reg .r2 (by decide)] at out
    exact out.trans stash₃'

end VG.Proof.Rc2.Arm.Cbc

end

section

/-! # Restricting CBC permissions to a consecutive subrange -/

namespace VG.Proof.Rc2.Arm.Cbc

open VG VG.Arm

theorem StepPre.slice {s s' : State} {n m i : Nat} (hp : StepPre s n) (bound : i + m ≤ n)
    (startFit : (s.gpr .r1).toNat + 8 * i < 2 ^ 32)
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr)
    (key : s'.gpr .r0 = s.gpr .r0) (iv : s'.gpr .r4 = s.gpr .r4)
    (buf : s'.gpr .r2 = s.gpr .r2)
    (ptr : s'.gpr .r1 = s.gpr .r1 + BitVec.ofNat 32 (8 * i)) : StepPre s' m := by
  have ptrAddr : State.addr (s'.gpr .r1) = State.addr (s.gpr .r1) + BitVec.ofNat 64 (8 * i) := by
    rw [ptr]; exact addr_add startFit
  have fit : (s'.gpr .r1).toNat + 8 * m ≤ 2 ^ 32 := by
    rw [ptr, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * i) (by omega),
      Nat.mod_eq_of_lt startFit]
    have := hp.dataFit
    omega
  have sub : Region.Sub (dataR s' m) (dataR s n) := by
    change Region.Sub ⟨State.addr (s'.gpr .r1), 8 * m⟩ ⟨State.addr (s.gpr .r1), 8 * n⟩
    rw [ptrAddr]
    exact Offset.sub_base _ (by omega)
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
      · exact ⟨dataR s n, by simp, 8 * i, ptrAddr, by change 8 * i + 8 * m ≤ 8 * n; omega⟩
      · exact ⟨bufR s, by simp, 0, by simp [buf], by simp⟩
    rw [rd, wr]
    exact fun a k h => hp.reads a k (hc a k h)
  · have hc : Covers [ivR s', dataR s' m, bufR s'] [ivR s, dataR s n, bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨ivR s, by simp, 0, by simp [iv], by simp⟩
      · exact ⟨dataR s n, by simp, 8 * i, ptrAddr, by change 8 * i + 8 * m ≤ 8 * n; omega⟩
      · exact ⟨bufR s, by simp, 0, by simp [buf], by simp⟩
    rw [wr]
    exact fun a k h => hp.writes a k (hc a k h)
  · simpa only [keyR, ivR, key, iv] using hp.keyIv
  · simpa only [keyR, key] using hp.keyData.sub_right sub
  · simpa only [keyR, bufR, key, buf] using hp.keyBuf
  · simpa only [ivR, iv] using hp.ivData.sub_right sub
  · simpa only [ivR, bufR, iv, buf] using hp.ivBuf
  · simpa only [bufR, buf] using hp.dataBuf.sub_left sub

theorem StepPre.head {s : State} {n : Nat} (hp : StepPre s n) (hn : 1 ≤ n) : StepPre s :=
  hp.slice (i := 0) hn (by simpa using (s.gpr .r1).isLt) rfl rfl rfl rfl rfl (by simp)

end VG.Proof.Rc2.Arm.Cbc

end

section

/-! # One CBC encryption step -/

namespace VG.Proof.Rc2.Arm.Cbc

open VG VG.Arm VG.Impl.Rc2.Arm

theorem encryptStep_ok (s : State) (hp : StepPre s) :
    WP isa (Impl.Rc2.Arm.Cbc.step .encrypt) s (StepPost .encrypt s) := by
  rw [Impl.Rc2.Arm.Cbc.step]
  apply WP.seq
  apply WP.mono (xor64_ok s .r1 .r4 (by decide) (by decide)
    (by simpa using hp.dataFit) hp.ivFit hp.readData hp.readIv hp.writeData)
  intro s₁ keep₁
  have pin₁ := Pinned.of_keep keep₁ ((frame_store64 _ _ _).mono (by simp [stepWrites]))
  have hp₁ := pin₁.pre hp
  have key₁ := pin₁.schedule hp
  have data₁ : Spec.Rc2.blockAt s₁.mem (State.addr (s.gpr .r1)) =
      Spec.Rc2.xorBlock (Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r1))) (Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r4))) := by
    rw [keep₁.mem]; exact blockAt_xor _ _ _
  apply WP.seq
  apply WP.mono (call_ok .encrypt s₁ hp₁.call)
  intro s₂ h₂
  have pin₂ := pin₁.trans (Pinned.of_call h₂)
  have hp₂ := pin₂.pre hp
  have output₂ := h₂.output
  rw [pin₁.reg .r1 (by decide), pin₁.reg .r0 (by decide), key₁, data₁] at output₂
  apply WP.mono (copy64_ok s₂ .r1 .r4 0 0 (by decide) (by decide)
    (by simpa using hp₂.dataFit) (by simpa using hp₂.ivFit) (by simpa using hp₂.readData) (by simpa using hp₂.writeIv))
  intro s₃ keep₃
  simp only [BitVec.add_zero] at keep₃
  have frame₃ : Frame [ivR s₂] s₂.mem s₃.mem := by
    rw [keep₃.mem]; exact frame_store64 _ _ _
  have pin₃ := Pinned.of_keep keep₃ ((frame_store64 _ _ _).mono (by simp [stepWrites]))
  refine ⟨pin₂.trans pin₃, ?_, ?_⟩
  · have same := blockAt_frame frame₃ (State.addr (s₂.gpr .r1)) (by simpa using hp₂.ivData.symm)
    rw [pin₂.reg .r1 (by decide)] at same
    exact same.trans output₂
  · have out : Spec.Rc2.blockAt s₃.mem (State.addr (s₂.gpr .r4)) = Spec.Rc2.blockAt s₂.mem (State.addr (s₂.gpr .r1)) := by
      rw [keep₃.mem]; exact blockAt_copy _ _ _
    rw [pin₂.reg .r4 (by decide), pin₂.reg .r1 (by decide)] at out
    exact out.trans output₂

end VG.Proof.Rc2.Arm.Cbc

end

/-! # A CBC loop iteration and its public counter -/

namespace VG.Proof.Rc2.Arm.Cbc

open VG VG.Arm VG.Impl.Rc2.Arm

theorem step_ok (d : Spec.Rc2.Direction) (s : State) (hp : StepPre s) :
    WP isa (Impl.Rc2.Arm.Cbc.step d) s (StepPost d s) := by
  cases d
  · exact encryptStep_ok s hp
  · exact decryptStep_ok s hp

structure BodyPost (d : Spec.Rc2.Direction) (s : State) (n : Nat) (s' : State) : Prop where
  ptr : s'.gpr .r1 = s.gpr .r1 + 8
  count : s'.gpr .r5 = BitVec.ofNat 32 (n - 1)
  flag : zeroCount s' = some (decide (n = 1))
  reg : ∀ r ∈ kept, r ≠ .r1 → r ≠ .r5 → s'.gpr r = s.gpr r
  callee : ∀ r ∈ savedAcrossCall, r ≠ .r5 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame (stepWrites s) s.mem s'.mem
  data : Spec.Rc2.blockAt s'.mem (State.addr (s.gpr .r1)) =
    (Spec.Rc2.cbcStep (Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))) d
      (Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r4))) (Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r1)))).1
  iv : Spec.Rc2.blockAt s'.mem (State.addr (s.gpr .r4)) =
    (Spec.Rc2.cbcStep (Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))) d
      (Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r4))) (Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r1)))).2

theorem body_ok (d : Spec.Rc2.Direction) (s : State) (n : Nat) (hn : 1 ≤ n) (bound : n < 2 ^ 32)
    (count : s.gpr .r5 = BitVec.ofNat 32 n) (hp : StepPre s) :
    WP isa (Impl.Rc2.Arm.Cbc.body d) s (BodyPost d s n) := by
  rw [Impl.Rc2.Arm.Cbc.body]
  apply WP.seq
  apply WP.mono (step_ok d s hp)
  intro s₁ h₁
  obtain ⟨s₂, run₂, ptr₂, count₂, flag₂, keep₂⟩ := advance_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have count' : s₁.gpr .r5 - 1 = BitVec.ofNat 32 (n - 1) := by
    rw [h₁.reg .r5 (by decide), count]
    exact Offset.ofNat_sub_ofNat hn
  refine ⟨by rw [ptr₂, h₁.reg .r1 (by decide)], count₂.trans count', ?_, ?_, ?_,
    keep₂.rd.trans h₁.rd, keep₂.wr.trans h₁.wr, ?_, ?_, ?_⟩
  · rw [flag₂, count']
    have eqZero := counter_eq (n - 1) 0 (by omega) (by decide)
    simp only [BitVec.sub_zero] at eqZero
    change some (BitVec.ofNat 32 (n - 1) == 0#32) = _
    rw [eqZero]
    have he : n - 1 = 0 ↔ n = 1 := by omega
    simp only [he]
  · intro r hr hs hb
    exact (keep₂.reg r (by simp [hs, hb])).trans (h₁.reg r hr)
  · intro r hr hb
    have hs : r ≠ .r1 := by
      have fact : ∀ r ∈ savedAcrossCall, r ≠ .r1 := by decide
      exact fact r hr
    exact (keep₂.reg r (by simp [hs, hb])).trans (h₁.callee r hr)
  · rw [keep₂.mem]; exact h₁.mem
  · rw [keep₂.mem]; exact h₁.data
  · rw [keep₂.mem]; exact h₁.iv

theorem BodyPost.tail {d : Spec.Rc2.Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s (n + 1) s') (hp : StepPre s (n + 1)) (hn : 1 ≤ n) : StepPre s' n :=
  hp.slice (i := 1) (by omega) (by have := hp.dataFit; omega) h.rd h.wr
    (h.reg .r0 (by decide) (by decide) (by decide))
    (h.reg .r4 (by decide) (by decide) (by decide))
    (h.reg .r2 (by decide) (by decide) (by decide))
    h.ptr

end VG.Proof.Rc2.Arm.Cbc
