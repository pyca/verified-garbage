import VerifiedGarbage.Proof.Rc2.Arm.Key
import VerifiedGarbage.Proof.Rc2.Stream
import VerifiedGarbage.Proof.Rc2.Arm.Block
import VerifiedGarbage.Impl.Rc2.Arm.Cbc
import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Rc2.Contract
import VerifiedGarbage.Proof.Rc2.Arm.Key

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.Arm.Cbc.Body`. -/
section

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

theorem block_keeps_reg (d : Spec.Rc2.Direction) {r : Reg} (hr : r ∈ VG.Proof.Rc2.Arm.Cbc.args) :
    ∀ i ∈ instrs (.block (blockCode d) : Prog isa), dstOf i ≠ some r := by
  intro i hi
  have h := List.all_eq_true.mp (List.all_eq_true.mp (VG.Proof.Rc2.Arm.Cbc.block_keeps d) i hi) r hr
  simpa using h

theorem block_correct' (d : Spec.Rc2.Direction) (s : State) (hs : (blockContract d).pre s) :
    ∃ t s', Exec isa (.block (blockCode d)) s t s' ∧ abiPreserved s s' ∧ (blockContract d).post s s' := by
  cases d
  · exact VG.Proof.Rc2.Arm.encrypt_correct s hs
  · exact VG.Proof.Rc2.Arm.decrypt_correct s hs

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
  reg : ∀ r ∈ VG.Proof.Rc2.Arm.Cbc.kept, s'.gpr r = s.gpr r
  callee : ∀ r ∈ VG.Proof.Rc2.Arm.Cbc.savedAcrossCall, s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame [⟨State.addr (s.gpr .r1), 8⟩, ⟨State.addr (s.gpr .r2), 256⟩] s.mem s'.mem
  output : Spec.Rc2.blockAt s'.mem (State.addr (s.gpr .r1)) =
    cipher d (Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))) (Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r1)))

theorem call_ok (d : Spec.Rc2.Direction) (s : State) (hp : VG.Proof.Rc2.Arm.Cbc.CallPre s) :
    WP isa (Impl.Rc2.Arm.Cbc.blockCall d) s (VG.Proof.Rc2.Arm.Cbc.CallPost d s) := by
  rw [VG.Proof.Rc2.Arm.Cbc.blockCall_eq]
  refine WP.call (k := blockContract d) (VG.Proof.Rc2.Arm.Cbc.block_correct' d)
    (rd := [⟨State.addr (s.gpr .r0), 128⟩]) (wr := [⟨State.addr (s.gpr .r1), 8⟩, ⟨State.addr (s.gpr .r2), 256⟩]) ?_ hp.reads hp.writes ?_ (by rfl)
  · simp only [blockContract, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs)]
    exact ⟨trivial, trivial, hp.keyScratch, hp.dataScratch, hp.keyFit, hp.dataFit, hp.bufFit⟩
  · intro s' rd wr sp frame callee regs out
    have sep : ∀ r ∈ VG.Proof.Rc2.Arm.Cbc.kept, r ∉ linkRegs := by decide
    have saved : ∀ r ∈ VG.Proof.Rc2.Arm.Cbc.savedAcrossCall, r ∈ preserved ∧ r ≠ .lr := by decide
    refine ⟨fun r hr => ?_,
      fun r hr => callee r (saved r hr).1 (saved r hr).2, rd, wr, frame, ?_⟩
    · by_cases ha : r ∈ VG.Proof.Rc2.Arm.Cbc.args
      · exact regs r (VG.Proof.Rc2.Arm.Cbc.block_keeps_reg d ha) (sep r hr)
      · have saved : ∀ r ∈ VG.Proof.Rc2.Arm.Cbc.kept, r ∉ VG.Proof.Rc2.Arm.Cbc.args → r ∈ preserved ∧ r ≠ .lr := by decide
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
  obtain ⟨rd0, rd4⟩ := VG.Proof.Rc2.Arm.Cbc.halves readable
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
  obtain ⟨wr0, wr4⟩ := VG.Proof.Rc2.Arm.Cbc.halves writable
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
      Keep VG.Proof.Rc2.Arm.Cbc.temps {s with
        mem := s.mem.writeW (State.addr (s.gpr dst) + BitVec.ofNat 64 b)
          (s.mem.readW (State.addr (s.gpr src) + BitVec.ofNat 64 a) 64)} s') := by
  change WP isa (.block (([.ldr .r12 src a, .ldr .r3 src (a + 4)] : List Instr) ++
    [.str .r12 dst b, .str .r3 dst (b + 4)])) s _
  rw [WP.block_append_iff]
  obtain ⟨s₁, run₁, lo₁, hi₁, keep₁⟩ := VG.Proof.Rc2.Arm.Cbc.loadPair_ok s .r12 .r3 src a (by decide) srcSep ha srcFit readable
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have ptr := keep₁.reg dst (by simpa only [List.mem_cons, List.not_mem_nil, or_false, not_or] using dstSep)
  obtain ⟨s₂, run₂, keep₂⟩ := VG.Proof.Rc2.Arm.Cbc.storePair_ok s₁ .r12 .r3 dst b hb
    (by rw [ptr]; exact dstFit) (by rw [keep₁.wr, ptr]; exact writable)
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  constructor
  · intro r hr
    exact (keep₂.reg r (by simp)).trans (keep₁.reg r (by
      intro h; exact hr (by simp only [VG.Proof.Rc2.Arm.Cbc.temps, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; grind)))
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
    (dstSep : dst ∉ VG.Proof.Rc2.Arm.Cbc.temps) (ivSep : iv ∉ VG.Proof.Rc2.Arm.Cbc.temps)
    (dstFit : (s.gpr dst).toNat + 8 ≤ 2 ^ 32) (ivFit : (s.gpr iv).toNat + 8 ≤ 2 ^ 32)
    (readDst : InRegions (s.rd ++ s.wr) (State.addr (s.gpr dst)) 8)
    (readIv : InRegions (s.rd ++ s.wr) (State.addr (s.gpr iv)) 8)
    (writable : InRegions s.wr (State.addr (s.gpr dst)) 8) :
    WP isa (.block (Impl.Rc2.Arm.Cbc.xor64 dst iv)) s (fun s' =>
      Keep VG.Proof.Rc2.Arm.Cbc.temps {s with
        mem := s.mem.writeW (State.addr (s.gpr dst))
          (s.mem.readW (State.addr (s.gpr dst)) 64 ^^^ s.mem.readW (State.addr (s.gpr iv)) 64)} s') := by
  have ds : dst ≠ .r12 ∧ dst ≠ .r3 ∧ dst ≠ .r6 ∧ dst ≠ .r7 := by simpa [VG.Proof.Rc2.Arm.Cbc.temps] using dstSep
  have vs : iv ≠ .r12 ∧ iv ≠ .r3 ∧ iv ≠ .r6 ∧ iv ≠ .r7 := by simpa [VG.Proof.Rc2.Arm.Cbc.temps] using ivSep
  change WP isa (.block (([.ldr .r12 dst 0, .ldr .r3 dst 4] : List Instr) ++
    (([.ldr .r6 iv 0, .ldr .r7 iv 4] : List Instr) ++
      (([.dp .eor .r12 .r12 (.reg .r6), .dp .eor .r3 .r3 (.reg .r7)] : List Instr) ++
        [.str .r12 dst 0, .str .r3 dst 4])))) s _
  rw [WP.block_append_iff]
  obtain ⟨s₁, run₁, lo₁, hi₁, keep₁⟩ := VG.Proof.Rc2.Arm.Cbc.loadPair_ok s .r12 .r3 dst 0 (by decide) ds.1 (by decide)
    (by simpa using dstFit) (by simpa using readDst)
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have iv₁ := keep₁.reg iv (by simp [vs.1, vs.2.1])
  rw [WP.block_append_iff]
  obtain ⟨s₂, run₂, lo₂, hi₂, keep₂⟩ := VG.Proof.Rc2.Arm.Cbc.loadPair_ok s₁ .r6 .r7 iv 0 (by decide) vs.2.2.1 (by decide)
    (by rw [iv₁]; simpa using ivFit) (by rw [keep₁.rd, keep₁.wr, iv₁]; simpa using readIv)
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  rw [WP.block_append_iff]
  obtain ⟨s₃, run₃, lo₃, hi₃, keep₃⟩ := VG.Proof.Rc2.Arm.Cbc.xorPair_ok s₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have keep : Keep VG.Proof.Rc2.Arm.Cbc.temps s s₃ :=
    ((keep₁.weaken (by simp [VG.Proof.Rc2.Arm.Cbc.temps])).trans (keep₂.weaken (by simp [VG.Proof.Rc2.Arm.Cbc.temps]))).trans
      (keep₃.weaken (by simp [VG.Proof.Rc2.Arm.Cbc.temps]))
  have ptr := keep.reg dst dstSep
  obtain ⟨s₄, run₄, keep₄⟩ := VG.Proof.Rc2.Arm.Cbc.storePair_ok s₃ .r12 .r3 dst 0 (by decide)
    (by rw [ptr]; simpa using dstFit) (by rw [keep.wr, ptr]; simpa using writable)
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  refine ⟨fun r hr => (keep₄.reg r (by simp)).trans (keep.reg r hr), ?_,
    keep₄.rd.trans keep.rd, keep₄.wr.trans keep.wr⟩
  rw [keep₄.mem, keep.mem, ptr, BitVec.add_zero, hi₃, lo₃, lo₂, hi₂,
    keep₂.reg .r12 (by decide), keep₂.reg .r3 (by decide), lo₁, hi₁, keep₁.mem, iv₁]
  simp only [Nat.zero_add, BitVec.add_zero]
  rw [pair_xor, ← read64_pair, ← read64_pair]

def zeroCount (s : State) : Option Bool := some s.z

theorem eval_zeroCount (s : State) : eval .eq s = VG.Proof.Rc2.Arm.Cbc.zeroCount s := rfl

theorem eval_nonzeroCount (s : State) : eval .ne s = (VG.Proof.Rc2.Arm.Cbc.zeroCount s).map (! ·) := rfl

theorem advance_ok (s : State) :
    ∃ s', runBlock isa Impl.Rc2.Arm.Cbc.advance s = some s' ∧
      s'.gpr .r1 = s.gpr .r1 + 8 ∧ s'.gpr .r5 = s.gpr .r5 - 1 ∧
      VG.Proof.Rc2.Arm.Cbc.zeroCount s' = some ((s.gpr .r5 - 1) == 0) ∧ Keep [.r1, .r5] s s' := by
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
  reads : Covers [VG.Proof.Rc2.Arm.Cbc.keyR s, VG.Proof.Rc2.Arm.Cbc.ivR s, VG.Proof.Rc2.Arm.Cbc.dataR s n, VG.Proof.Rc2.Arm.Cbc.bufR s] (s.rd ++ s.wr)
  writes : Covers [VG.Proof.Rc2.Arm.Cbc.ivR s, VG.Proof.Rc2.Arm.Cbc.dataR s n, VG.Proof.Rc2.Arm.Cbc.bufR s] s.wr
  keyIv : (VG.Proof.Rc2.Arm.Cbc.keyR s).Disjoint (VG.Proof.Rc2.Arm.Cbc.ivR s)
  keyData : (VG.Proof.Rc2.Arm.Cbc.keyR s).Disjoint (VG.Proof.Rc2.Arm.Cbc.dataR s n)
  keyBuf : (VG.Proof.Rc2.Arm.Cbc.keyR s).Disjoint (VG.Proof.Rc2.Arm.Cbc.bufR s)
  ivData : (VG.Proof.Rc2.Arm.Cbc.ivR s).Disjoint (VG.Proof.Rc2.Arm.Cbc.dataR s n)
  ivBuf : (VG.Proof.Rc2.Arm.Cbc.ivR s).Disjoint (VG.Proof.Rc2.Arm.Cbc.bufR s)
  dataBuf : (VG.Proof.Rc2.Arm.Cbc.dataR s n).Disjoint (VG.Proof.Rc2.Arm.Cbc.bufR s)

theorem StepPre.transport {s s' : State} {n : Nat} (hp : VG.Proof.Rc2.Arm.Cbc.StepPre s n)
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) (regs : ∀ r ∈ VG.Proof.Rc2.Arm.Cbc.kept, s'.gpr r = s.gpr r) : VG.Proof.Rc2.Arm.Cbc.StepPre s' n := by
  have a := regs .r0 (by decide)
  have b := regs .r4 (by decide)
  have c := regs .r1 (by decide)
  have d := regs .r2 (by decide)
  constructor
  · simpa only [a] using hp.keyFit
  · simpa only [b] using hp.ivFit
  · simpa only [c] using hp.dataFit
  · simpa only [d] using hp.bufFit
  · simpa only [VG.Proof.Rc2.Arm.Cbc.keyR, VG.Proof.Rc2.Arm.Cbc.ivR, VG.Proof.Rc2.Arm.Cbc.dataR, VG.Proof.Rc2.Arm.Cbc.bufR, rd, wr, a, b, c, d] using hp.reads
  · simpa only [VG.Proof.Rc2.Arm.Cbc.keyR, VG.Proof.Rc2.Arm.Cbc.ivR, VG.Proof.Rc2.Arm.Cbc.dataR, VG.Proof.Rc2.Arm.Cbc.bufR, rd, wr, a, b, c, d] using hp.writes
  · simpa only [VG.Proof.Rc2.Arm.Cbc.keyR, VG.Proof.Rc2.Arm.Cbc.ivR, VG.Proof.Rc2.Arm.Cbc.dataR, VG.Proof.Rc2.Arm.Cbc.bufR, rd, wr, a, b, c, d] using hp.keyIv
  · simpa only [VG.Proof.Rc2.Arm.Cbc.keyR, VG.Proof.Rc2.Arm.Cbc.ivR, VG.Proof.Rc2.Arm.Cbc.dataR, VG.Proof.Rc2.Arm.Cbc.bufR, rd, wr, a, b, c, d] using hp.keyData
  · simpa only [VG.Proof.Rc2.Arm.Cbc.keyR, VG.Proof.Rc2.Arm.Cbc.ivR, VG.Proof.Rc2.Arm.Cbc.dataR, VG.Proof.Rc2.Arm.Cbc.bufR, rd, wr, a, b, c, d] using hp.keyBuf
  · simpa only [VG.Proof.Rc2.Arm.Cbc.keyR, VG.Proof.Rc2.Arm.Cbc.ivR, VG.Proof.Rc2.Arm.Cbc.dataR, VG.Proof.Rc2.Arm.Cbc.bufR, rd, wr, a, b, c, d] using hp.ivData
  · simpa only [VG.Proof.Rc2.Arm.Cbc.keyR, VG.Proof.Rc2.Arm.Cbc.ivR, VG.Proof.Rc2.Arm.Cbc.dataR, VG.Proof.Rc2.Arm.Cbc.bufR, rd, wr, a, b, c, d] using hp.ivBuf
  · simpa only [VG.Proof.Rc2.Arm.Cbc.keyR, VG.Proof.Rc2.Arm.Cbc.ivR, VG.Proof.Rc2.Arm.Cbc.dataR, VG.Proof.Rc2.Arm.Cbc.bufR, rd, wr, a, b, c, d] using hp.dataBuf

theorem StepPre.keep {s s' : State} {m : Mem} {n : Nat} (hp : VG.Proof.Rc2.Arm.Cbc.StepPre s n) (h : Keep [.r12, .r3, .r6, .r7] {s with mem := m} s') : VG.Proof.Rc2.Arm.Cbc.StepPre s' n :=
  hp.transport h.rd h.wr fun r hr => h.reg r (by
    have sep : ∀ r ∈ VG.Proof.Rc2.Arm.Cbc.kept, r ∉ [.r12, .r3, .r6, .r7] := by decide
    exact sep r hr)

theorem StepPre.call {s : State} (hp : VG.Proof.Rc2.Arm.Cbc.StepPre s) : VG.Proof.Rc2.Arm.Cbc.CallPre s := by
  constructor
  · have hc : Covers [⟨State.addr (s.gpr .r0), 128⟩, ⟨State.addr (s.gpr .r1), 8⟩, ⟨State.addr (s.gpr .r2), 256⟩]
        [VG.Proof.Rc2.Arm.Cbc.keyR s, VG.Proof.Rc2.Arm.Cbc.ivR s, VG.Proof.Rc2.Arm.Cbc.dataR s, VG.Proof.Rc2.Arm.Cbc.bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨VG.Proof.Rc2.Arm.Cbc.keyR s, by simp, 0, by simp, by simp⟩
      · exact ⟨VG.Proof.Rc2.Arm.Cbc.dataR s, by simp, 0, by simp, by simp⟩
      · exact ⟨VG.Proof.Rc2.Arm.Cbc.bufR s, by simp, 0, by simp, by simp⟩
    exact fun a n h => hp.reads a n (hc a n h)
  · have hc : Covers [⟨State.addr (s.gpr .r1), 8⟩, ⟨State.addr (s.gpr .r2), 256⟩] [VG.Proof.Rc2.Arm.Cbc.ivR s, VG.Proof.Rc2.Arm.Cbc.dataR s, VG.Proof.Rc2.Arm.Cbc.bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨VG.Proof.Rc2.Arm.Cbc.dataR s, by simp, 0, by simp, by simp⟩
      · exact ⟨VG.Proof.Rc2.Arm.Cbc.bufR s, by simp, 0, by simp, by simp⟩
    exact fun a n h => hp.writes a n (hc a n h)
  · exact hp.keyBuf.sub_right (Region.sub_prefix (by decide))
  · exact hp.keyFit
  · simpa only [Nat.mul_one] using hp.dataFit
  · have := hp.bufFit; omega
  · exact hp.dataBuf.sub_right (Region.sub_prefix (by decide))

theorem StepPre.readData {s : State} (hp : VG.Proof.Rc2.Arm.Cbc.StepPre s) : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r1)) 8 :=
  hp.reads _ _ ⟨VG.Proof.Rc2.Arm.Cbc.dataR s, by simp, Region.contains_self _ _⟩

theorem StepPre.readIv {s : State} (hp : VG.Proof.Rc2.Arm.Cbc.StepPre s) : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r4)) 8 :=
  hp.reads _ _ ⟨VG.Proof.Rc2.Arm.Cbc.ivR s, by simp, Region.contains_self _ _⟩

theorem StepPre.writeData {s : State} (hp : VG.Proof.Rc2.Arm.Cbc.StepPre s) : InRegions s.wr (State.addr (s.gpr .r1)) 8 :=
  hp.writes _ _ ⟨VG.Proof.Rc2.Arm.Cbc.dataR s, by simp, Region.contains_self _ _⟩

theorem StepPre.writeIv {s : State} (hp : VG.Proof.Rc2.Arm.Cbc.StepPre s) : InRegions s.wr (State.addr (s.gpr .r4)) 8 :=
  hp.writes _ _ ⟨VG.Proof.Rc2.Arm.Cbc.ivR s, by simp, Region.contains_self _ _⟩

theorem StepPre.readBuf {s : State} (hp : VG.Proof.Rc2.Arm.Cbc.StepPre s) (i : Nat) (hi : i + 8 ≤ 512) :
    InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r2) + BitVec.ofNat 64 i) 8 :=
  hp.reads _ _ ⟨VG.Proof.Rc2.Arm.Cbc.bufR s, by simp, Offset.contains_base _ hi (by omega)⟩

theorem StepPre.writeBuf {s : State} (hp : VG.Proof.Rc2.Arm.Cbc.StepPre s) (i : Nat) (hi : i + 8 ≤ 512) :
    InRegions s.wr (State.addr (s.gpr .r2) + BitVec.ofNat 64 i) 8 :=
  hp.writes _ _ ⟨VG.Proof.Rc2.Arm.Cbc.bufR s, by simp, Offset.contains_base _ hi (by omega)⟩

end VG.Proof.Rc2.Arm.Cbc

end

/-! # The frame preserved by a CBC step -/

namespace VG.Proof.Rc2.Arm.Cbc

open VG VG.Arm

def stepWrites (s : State) : List Region := [VG.Proof.Rc2.Arm.Cbc.ivR s, VG.Proof.Rc2.Arm.Cbc.dataR s, ⟨State.addr (s.gpr .r2), 264⟩]

structure Pinned (s s' : State) : Prop where
  reg : ∀ r ∈ VG.Proof.Rc2.Arm.Cbc.kept, s'.gpr r = s.gpr r
  callee : ∀ r ∈ VG.Proof.Rc2.Arm.Cbc.savedAcrossCall, s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame (VG.Proof.Rc2.Arm.Cbc.stepWrites s) s.mem s'.mem

theorem Pinned.of_keep {s s' : State} {m : Mem} (h : Keep [.r12, .r3, .r6, .r7] {s with mem := m} s')
    (frame : Frame (VG.Proof.Rc2.Arm.Cbc.stepWrites s) s.mem m) : VG.Proof.Rc2.Arm.Cbc.Pinned s s' := by
  have k : ∀ r ∈ VG.Proof.Rc2.Arm.Cbc.kept, r ∉ [.r12, .r3, .r6, .r7] := by decide
  have c : ∀ r ∈ VG.Proof.Rc2.Arm.Cbc.savedAcrossCall, r ∉ [.r12, .r3, .r6, .r7] := by decide
  exact ⟨fun r hr => h.reg r (k r hr), fun r hr => h.reg r (c r hr), h.rd, h.wr, by rw [h.mem]; exact frame⟩

theorem Pinned.of_call {d : Spec.Rc2.Direction} {s s' : State} (h : VG.Proof.Rc2.Arm.Cbc.CallPost d s s') : VG.Proof.Rc2.Arm.Cbc.Pinned s s' := by
  refine ⟨h.reg, h.callee, h.rd, h.wr, h.mem.sub ?_⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨VG.Proof.Rc2.Arm.Cbc.dataR s, by simp [VG.Proof.Rc2.Arm.Cbc.stepWrites], fun _ h => h⟩
  · exact ⟨⟨State.addr (s.gpr .r2), 264⟩, by simp [VG.Proof.Rc2.Arm.Cbc.stepWrites], Region.sub_prefix (by decide)⟩

theorem Pinned.writes_eq {s s' : State} (h : VG.Proof.Rc2.Arm.Cbc.Pinned s s') : VG.Proof.Rc2.Arm.Cbc.stepWrites s' = VG.Proof.Rc2.Arm.Cbc.stepWrites s := by
  simp only [VG.Proof.Rc2.Arm.Cbc.stepWrites, VG.Proof.Rc2.Arm.Cbc.ivR, VG.Proof.Rc2.Arm.Cbc.dataR, h.reg .r4 (by decide), h.reg .r1 (by decide), h.reg .r2 (by decide)]

theorem Pinned.trans {s s' s'' : State} (h : VG.Proof.Rc2.Arm.Cbc.Pinned s s') (h' : VG.Proof.Rc2.Arm.Cbc.Pinned s' s'') : VG.Proof.Rc2.Arm.Cbc.Pinned s s'' := by
  refine ⟨fun r hr => (h'.reg r hr).trans (h.reg r hr), fun r hr => (h'.callee r hr).trans (h.callee r hr),
    h'.rd.trans h.rd, h'.wr.trans h.wr, ?_⟩
  have f := h'.mem
  rw [h.writes_eq] at f
  exact h.mem.trans f

theorem Pinned.pre {s s' : State} {n : Nat} (h : VG.Proof.Rc2.Arm.Cbc.Pinned s s') (hp : VG.Proof.Rc2.Arm.Cbc.StepPre s n) : VG.Proof.Rc2.Arm.Cbc.StepPre s' n :=
  hp.transport h.rd h.wr h.reg

theorem Pinned.schedule {s s' : State} (h : VG.Proof.Rc2.Arm.Cbc.Pinned s s') (hp : VG.Proof.Rc2.Arm.Cbc.StepPre s) :
    Spec.Rc2.scheduleAt s'.mem (State.addr (s.gpr .r0)) = Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0)) := by
  apply scheduleAt_frame h.mem
  simpa only [VG.Proof.Rc2.Arm.Cbc.stepWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro hp.keyIv (And.intro hp.keyData
      (hp.keyBuf.sub_right (Region.sub_prefix (by decide : 264 ≤ 512))))

theorem CallPost.iv {d : Spec.Rc2.Direction} {s s' : State} (h : VG.Proof.Rc2.Arm.Cbc.CallPost d s s') (hp : VG.Proof.Rc2.Arm.Cbc.StepPre s) :
    Spec.Rc2.blockAt s'.mem (State.addr (s.gpr .r4)) = Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r4)) := by
  apply blockAt_frame h.mem
  simpa only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro hp.ivData
      (hp.ivBuf.sub_right (Region.sub_prefix (by decide : 256 ≤ 512)))

structure StepPost (d : Spec.Rc2.Direction) (s s' : State) : Prop extends VG.Proof.Rc2.Arm.Cbc.Pinned s s' where
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

theorem stash_sub (s : State) : Region.Sub (VG.Proof.Rc2.Arm.Cbc.stashR s) (VG.Proof.Rc2.Arm.Cbc.bufR s) :=
  Offset.sub_base _ (by decide)

theorem call_stash {d : Spec.Rc2.Direction} {s s' : State} (hp : VG.Proof.Rc2.Arm.Cbc.StepPre s) (h : VG.Proof.Rc2.Arm.Cbc.CallPost d s s') :
    Spec.Rc2.blockAt s'.mem (VG.Proof.Rc2.Arm.Cbc.stashR s).base = Spec.Rc2.blockAt s.mem (VG.Proof.Rc2.Arm.Cbc.stashR s).base := by
  apply blockAt_frame h.mem
  have sep : (VG.Proof.Rc2.Arm.Cbc.stashR s).Disjoint ⟨State.addr (s.gpr .r2), 256⟩ := by
    have h := Offset.disjoint (State.addr (s.gpr .r2)) (d := 256) (n := 8) (e := 0) (k := 256)
      (by omega) (by decide) (by decide)
    simpa using h
  simpa only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro ((hp.dataBuf.sub_right (VG.Proof.Rc2.Arm.Cbc.stash_sub s)).symm) sep

theorem decryptStep_ok (s : State) (hp : VG.Proof.Rc2.Arm.Cbc.StepPre s) :
    WP isa (Impl.Rc2.Arm.Cbc.step .decrypt) s (VG.Proof.Rc2.Arm.Cbc.StepPost .decrypt s) := by
  rw [Impl.Rc2.Arm.Cbc.step]
  apply WP.seq
  apply WP.mono (VG.Proof.Rc2.Arm.Cbc.copy64_ok s .r1 .r2 0 256 (by decide) (by decide)
    (by simpa using hp.dataFit) (by have := hp.bufFit; omega) (by simpa using hp.readData) (hp.writeBuf 256 (by decide)))
  intro s₁ keep₁
  simp only [BitVec.add_zero] at keep₁
  have frame₁ : Frame [VG.Proof.Rc2.Arm.Cbc.stashR s] s.mem s₁.mem := by
    rw [keep₁.mem]; exact frame_store64 _ _ _
  have pin₁ : VG.Proof.Rc2.Arm.Cbc.Pinned s s₁ := by
    apply Pinned.of_keep keep₁
    apply (frame_store64 _ _ _).sub
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact ⟨⟨State.addr (s.gpr .r2), 264⟩, by simp [VG.Proof.Rc2.Arm.Cbc.stepWrites], Offset.sub_base _ (by decide)⟩
  have hp₁ := pin₁.pre hp
  have key₁ := pin₁.schedule hp
  have data₁ := blockAt_frame frame₁ (State.addr (s.gpr .r1)) (by simpa using hp.dataBuf.sub_right (VG.Proof.Rc2.Arm.Cbc.stash_sub s))
  have iv₁ := blockAt_frame frame₁ (State.addr (s.gpr .r4)) (by simpa using hp.ivBuf.sub_right (VG.Proof.Rc2.Arm.Cbc.stash_sub s))
  have stash₁ : Spec.Rc2.blockAt s₁.mem (VG.Proof.Rc2.Arm.Cbc.stashR s).base = Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r1)) := by
    rw [keep₁.mem]; exact blockAt_copy _ _ _
  apply WP.seq
  apply WP.mono (VG.Proof.Rc2.Arm.Cbc.call_ok .decrypt s₁ hp₁.call)
  intro s₂ h₂
  have pin₂ := pin₁.trans (Pinned.of_call h₂)
  have hp₂ := pin₂.pre hp
  have output₂ := h₂.output
  rw [pin₁.reg .r1 (by decide), pin₁.reg .r0 (by decide), key₁, data₁] at output₂
  have iv₂ := h₂.iv hp₁
  rw [pin₁.reg .r4 (by decide), iv₁] at iv₂
  have stash₂ := VG.Proof.Rc2.Arm.Cbc.call_stash hp₁ h₂
  simp only [pin₁.reg .r2 (by decide)] at stash₂
  have stash₂' := stash₂.trans stash₁
  change WP isa (.block (Impl.Rc2.Arm.Cbc.xor64 .r1 .r4 ++
    Impl.Rc2.Arm.Cbc.copy64 .r2 .r4 256 0)) s₂ _
  rw [WP.block_append_iff]
  apply WP.mono (VG.Proof.Rc2.Arm.Cbc.xor64_ok s₂ .r1 .r4 (by decide) (by decide)
    (by simpa using hp₂.dataFit) hp₂.ivFit hp₂.readData hp₂.readIv hp₂.writeData)
  intro s₃ keep₃
  have frame₃ : Frame [VG.Proof.Rc2.Arm.Cbc.dataR s₂] s₂.mem s₃.mem := by
    rw [keep₃.mem]; exact frame_store64 _ _ _
  have pin₃ := Pinned.of_keep keep₃ ((frame_store64 _ _ _).mono (by simp [VG.Proof.Rc2.Arm.Cbc.stepWrites]))
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
  have stash₃ := blockAt_frame frame₃ (VG.Proof.Rc2.Arm.Cbc.stashR s₂).base
    (by simpa using (hp₂.dataBuf.sub_right (VG.Proof.Rc2.Arm.Cbc.stash_sub s₂)).symm)
  simp only [pin₂.reg .r2 (by decide)] at stash₃
  have stash₃' := stash₃.trans stash₂'
  apply WP.mono (VG.Proof.Rc2.Arm.Cbc.copy64_ok s₃ .r2 .r4 256 0 (by decide) (by decide)
    (by have := hp₃.bufFit; omega) (by simpa using hp₃.ivFit) (hp₃.readBuf 256 (by decide)) (by simpa using hp₃.writeIv))
  intro s₄ keep₄
  simp only [BitVec.add_zero] at keep₄
  have frame₄ : Frame [VG.Proof.Rc2.Arm.Cbc.ivR s₃] s₃.mem s₄.mem := by
    rw [keep₄.mem]; exact frame_store64 _ _ _
  have pin₄ := Pinned.of_keep keep₄ ((frame_store64 _ _ _).mono (by simp [VG.Proof.Rc2.Arm.Cbc.stepWrites]))
  refine ⟨pin₀₃.trans pin₄, ?_, ?_⟩
  · have same := blockAt_frame frame₄ (State.addr (s₃.gpr .r1)) (by simpa using hp₃.ivData.symm)
    rw [pin₀₃.reg .r1 (by decide)] at same
    exact same.trans data₃
  · have out : Spec.Rc2.blockAt s₄.mem (State.addr (s₃.gpr .r4)) = Spec.Rc2.blockAt s₃.mem (VG.Proof.Rc2.Arm.Cbc.stashR s₃).base := by
      rw [keep₄.mem]; exact blockAt_copy _ _ _
    simp only [pin₀₃.reg .r4 (by decide), pin₀₃.reg .r2 (by decide)] at out
    exact out.trans stash₃'

end VG.Proof.Rc2.Arm.Cbc

end

section

/-! # Restricting CBC permissions to a consecutive subrange -/

namespace VG.Proof.Rc2.Arm.Cbc

open VG VG.Arm

theorem StepPre.slice {s s' : State} {n m i : Nat} (hp : VG.Proof.Rc2.Arm.Cbc.StepPre s n) (bound : i + m ≤ n)
    (startFit : (s.gpr .r1).toNat + 8 * i < 2 ^ 32)
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr)
    (key : s'.gpr .r0 = s.gpr .r0) (iv : s'.gpr .r4 = s.gpr .r4)
    (buf : s'.gpr .r2 = s.gpr .r2)
    (ptr : s'.gpr .r1 = s.gpr .r1 + BitVec.ofNat 32 (8 * i)) : VG.Proof.Rc2.Arm.Cbc.StepPre s' m := by
  have ptrAddr : State.addr (s'.gpr .r1) = State.addr (s.gpr .r1) + BitVec.ofNat 64 (8 * i) := by
    rw [ptr]; exact addr_add startFit
  have fit : (s'.gpr .r1).toNat + 8 * m ≤ 2 ^ 32 := by
    rw [ptr, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * i) (by omega),
      Nat.mod_eq_of_lt startFit]
    have := hp.dataFit
    omega
  have sub : Region.Sub (VG.Proof.Rc2.Arm.Cbc.dataR s' m) (VG.Proof.Rc2.Arm.Cbc.dataR s n) := by
    change Region.Sub ⟨State.addr (s'.gpr .r1), 8 * m⟩ ⟨State.addr (s.gpr .r1), 8 * n⟩
    rw [ptrAddr]
    exact Offset.sub_base _ (by omega)
  constructor
  · rw [key]; exact hp.keyFit
  · rw [iv]; exact hp.ivFit
  · exact fit
  · rw [buf]; exact hp.bufFit
  · have hc : Covers [VG.Proof.Rc2.Arm.Cbc.keyR s', VG.Proof.Rc2.Arm.Cbc.ivR s', VG.Proof.Rc2.Arm.Cbc.dataR s' m, VG.Proof.Rc2.Arm.Cbc.bufR s'] [VG.Proof.Rc2.Arm.Cbc.keyR s, VG.Proof.Rc2.Arm.Cbc.ivR s, VG.Proof.Rc2.Arm.Cbc.dataR s n, VG.Proof.Rc2.Arm.Cbc.bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨VG.Proof.Rc2.Arm.Cbc.keyR s, by simp, 0, by simp [key], by simp⟩
      · exact ⟨VG.Proof.Rc2.Arm.Cbc.ivR s, by simp, 0, by simp [iv], by simp⟩
      · exact ⟨VG.Proof.Rc2.Arm.Cbc.dataR s n, by simp, 8 * i, ptrAddr, by change 8 * i + 8 * m ≤ 8 * n; omega⟩
      · exact ⟨VG.Proof.Rc2.Arm.Cbc.bufR s, by simp, 0, by simp [buf], by simp⟩
    rw [rd, wr]
    exact fun a k h => hp.reads a k (hc a k h)
  · have hc : Covers [VG.Proof.Rc2.Arm.Cbc.ivR s', VG.Proof.Rc2.Arm.Cbc.dataR s' m, VG.Proof.Rc2.Arm.Cbc.bufR s'] [VG.Proof.Rc2.Arm.Cbc.ivR s, VG.Proof.Rc2.Arm.Cbc.dataR s n, VG.Proof.Rc2.Arm.Cbc.bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨VG.Proof.Rc2.Arm.Cbc.ivR s, by simp, 0, by simp [iv], by simp⟩
      · exact ⟨VG.Proof.Rc2.Arm.Cbc.dataR s n, by simp, 8 * i, ptrAddr, by change 8 * i + 8 * m ≤ 8 * n; omega⟩
      · exact ⟨VG.Proof.Rc2.Arm.Cbc.bufR s, by simp, 0, by simp [buf], by simp⟩
    rw [wr]
    exact fun a k h => hp.writes a k (hc a k h)
  · simpa only [VG.Proof.Rc2.Arm.Cbc.keyR, VG.Proof.Rc2.Arm.Cbc.ivR, key, iv] using hp.keyIv
  · simpa only [VG.Proof.Rc2.Arm.Cbc.keyR, key] using hp.keyData.sub_right sub
  · simpa only [VG.Proof.Rc2.Arm.Cbc.keyR, VG.Proof.Rc2.Arm.Cbc.bufR, key, buf] using hp.keyBuf
  · simpa only [VG.Proof.Rc2.Arm.Cbc.ivR, iv] using hp.ivData.sub_right sub
  · simpa only [VG.Proof.Rc2.Arm.Cbc.ivR, VG.Proof.Rc2.Arm.Cbc.bufR, iv, buf] using hp.ivBuf
  · simpa only [VG.Proof.Rc2.Arm.Cbc.bufR, buf] using hp.dataBuf.sub_left sub

theorem StepPre.head {s : State} {n : Nat} (hp : VG.Proof.Rc2.Arm.Cbc.StepPre s n) (hn : 1 ≤ n) : VG.Proof.Rc2.Arm.Cbc.StepPre s :=
  hp.slice (i := 0) hn (by simpa using (s.gpr .r1).isLt) rfl rfl rfl rfl rfl (by simp)

end VG.Proof.Rc2.Arm.Cbc

end

section

/-! # One CBC encryption step -/

namespace VG.Proof.Rc2.Arm.Cbc

open VG VG.Arm VG.Impl.Rc2.Arm

theorem encryptStep_ok (s : State) (hp : VG.Proof.Rc2.Arm.Cbc.StepPre s) :
    WP isa (Impl.Rc2.Arm.Cbc.step .encrypt) s (VG.Proof.Rc2.Arm.Cbc.StepPost .encrypt s) := by
  rw [Impl.Rc2.Arm.Cbc.step]
  apply WP.seq
  apply WP.mono (VG.Proof.Rc2.Arm.Cbc.xor64_ok s .r1 .r4 (by decide) (by decide)
    (by simpa using hp.dataFit) hp.ivFit hp.readData hp.readIv hp.writeData)
  intro s₁ keep₁
  have pin₁ := Pinned.of_keep keep₁ ((frame_store64 _ _ _).mono (by simp [VG.Proof.Rc2.Arm.Cbc.stepWrites]))
  have hp₁ := pin₁.pre hp
  have key₁ := pin₁.schedule hp
  have data₁ : Spec.Rc2.blockAt s₁.mem (State.addr (s.gpr .r1)) =
      Spec.Rc2.xorBlock (Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r1))) (Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r4))) := by
    rw [keep₁.mem]; exact blockAt_xor _ _ _
  apply WP.seq
  apply WP.mono (VG.Proof.Rc2.Arm.Cbc.call_ok .encrypt s₁ hp₁.call)
  intro s₂ h₂
  have pin₂ := pin₁.trans (Pinned.of_call h₂)
  have hp₂ := pin₂.pre hp
  have output₂ := h₂.output
  rw [pin₁.reg .r1 (by decide), pin₁.reg .r0 (by decide), key₁, data₁] at output₂
  apply WP.mono (VG.Proof.Rc2.Arm.Cbc.copy64_ok s₂ .r1 .r4 0 0 (by decide) (by decide)
    (by simpa using hp₂.dataFit) (by simpa using hp₂.ivFit) (by simpa using hp₂.readData) (by simpa using hp₂.writeIv))
  intro s₃ keep₃
  simp only [BitVec.add_zero] at keep₃
  have frame₃ : Frame [VG.Proof.Rc2.Arm.Cbc.ivR s₂] s₂.mem s₃.mem := by
    rw [keep₃.mem]; exact frame_store64 _ _ _
  have pin₃ := Pinned.of_keep keep₃ ((frame_store64 _ _ _).mono (by simp [VG.Proof.Rc2.Arm.Cbc.stepWrites]))
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

theorem step_ok (d : Spec.Rc2.Direction) (s : State) (hp : VG.Proof.Rc2.Arm.Cbc.StepPre s) :
    WP isa (Impl.Rc2.Arm.Cbc.step d) s (VG.Proof.Rc2.Arm.Cbc.StepPost d s) := by
  cases d
  · exact VG.Proof.Rc2.Arm.Cbc.encryptStep_ok s hp
  · exact VG.Proof.Rc2.Arm.Cbc.decryptStep_ok s hp

structure BodyPost (d : Spec.Rc2.Direction) (s : State) (n : Nat) (s' : State) : Prop where
  ptr : s'.gpr .r1 = s.gpr .r1 + 8
  count : s'.gpr .r5 = BitVec.ofNat 32 (n - 1)
  flag : VG.Proof.Rc2.Arm.Cbc.zeroCount s' = some (decide (n = 1))
  reg : ∀ r ∈ VG.Proof.Rc2.Arm.Cbc.kept, r ≠ .r1 → r ≠ .r5 → s'.gpr r = s.gpr r
  callee : ∀ r ∈ VG.Proof.Rc2.Arm.Cbc.savedAcrossCall, r ≠ .r5 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame (VG.Proof.Rc2.Arm.Cbc.stepWrites s) s.mem s'.mem
  data : Spec.Rc2.blockAt s'.mem (State.addr (s.gpr .r1)) =
    (Spec.Rc2.cbcStep (Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))) d
      (Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r4))) (Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r1)))).1
  iv : Spec.Rc2.blockAt s'.mem (State.addr (s.gpr .r4)) =
    (Spec.Rc2.cbcStep (Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))) d
      (Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r4))) (Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r1)))).2

theorem body_ok (d : Spec.Rc2.Direction) (s : State) (n : Nat) (hn : 1 ≤ n) (bound : n < 2 ^ 32)
    (count : s.gpr .r5 = BitVec.ofNat 32 n) (hp : VG.Proof.Rc2.Arm.Cbc.StepPre s) :
    WP isa (Impl.Rc2.Arm.Cbc.body d) s (VG.Proof.Rc2.Arm.Cbc.BodyPost d s n) := by
  rw [Impl.Rc2.Arm.Cbc.body]
  apply WP.seq
  apply WP.mono (VG.Proof.Rc2.Arm.Cbc.step_ok d s hp)
  intro s₁ h₁
  obtain ⟨s₂, run₂, ptr₂, count₂, flag₂, keep₂⟩ := VG.Proof.Rc2.Arm.Cbc.advance_ok s₁
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
      have fact : ∀ r ∈ VG.Proof.Rc2.Arm.Cbc.savedAcrossCall, r ≠ .r1 := by decide
      exact fact r hr
    exact (keep₂.reg r (by simp [hs, hb])).trans (h₁.callee r hr)
  · rw [keep₂.mem]; exact h₁.mem
  · rw [keep₂.mem]; exact h₁.data
  · rw [keep₂.mem]; exact h₁.iv

theorem BodyPost.tail {d : Spec.Rc2.Direction} {s s' : State} {n : Nat}
    (h : VG.Proof.Rc2.Arm.Cbc.BodyPost d s (n + 1) s') (hp : VG.Proof.Rc2.Arm.Cbc.StepPre s (n + 1)) (hn : 1 ≤ n) : VG.Proof.Rc2.Arm.Cbc.StepPre s' n :=
  hp.slice (i := 1) (by omega) (by have := hp.dataFit; omega) h.rd h.wr
    (h.reg .r0 (by decide) (by decide) (by decide))
    (h.reg .r4 (by decide) (by decide) (by decide))
    (h.reg .r2 (by decide) (by decide) (by decide))
    h.ptr

end VG.Proof.Rc2.Arm.Cbc

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.Arm.Cbc.StepCT`. -/
section

/-! # Constant-time CBC steps with public registers restored by the block call -/

namespace VG.Proof.Rc2.Arm.Cbc

open VG VG.Arm VG.Impl.Rc2.Arm

def EqKept (s₁ s₂ : State) : Prop := ∀ r ∈ VG.Proof.Rc2.Arm.Cbc.kept, s₁.gpr r = s₂.gpr r

def StepRel (s₁ s₂ : State) : Prop := VG.Proof.Rc2.Arm.Cbc.StepPre s₁ ∧ VG.Proof.Rc2.Arm.Cbc.StepPre s₂ ∧ VG.Proof.Rc2.Arm.Cbc.EqKept s₁ s₂

theorem agreeKept {s₁ s₂ : State} (h : VG.Proof.Rc2.Arm.Cbc.EqKept s₁ s₂) :
    VG.Arm.Taint.Agree (Taint.ofRegs VG.Proof.Rc2.Arm.Cbc.kept) s₁ s₂ := Taint.agree_ofRegs h

theorem before_ok (d : Spec.Rc2.Direction) (s : State) (hp : VG.Proof.Rc2.Arm.Cbc.StepPre s) :
    WP isa (.block (Impl.Rc2.Arm.Cbc.before d)) s (fun s' => VG.Proof.Rc2.Arm.Cbc.StepPre s' ∧ ∀ r ∈ VG.Proof.Rc2.Arm.Cbc.kept, s'.gpr r = s.gpr r) := by
  have sep : ∀ r ∈ VG.Proof.Rc2.Arm.Cbc.kept, r ∉ VG.Proof.Rc2.Arm.Cbc.temps := by decide
  cases d
  · apply WP.mono (VG.Proof.Rc2.Arm.Cbc.xor64_ok s .r1 .r4 (by decide) (by decide)
      (by simpa using hp.dataFit) hp.ivFit hp.readData hp.readIv hp.writeData)
    intro s' h
    exact ⟨hp.keep h, fun r hr => h.reg r (sep r hr)⟩
  · apply WP.mono (VG.Proof.Rc2.Arm.Cbc.copy64_ok s .r1 .r2 0 256 (by decide) (by decide)
      (by simpa using hp.dataFit) (by have := hp.bufFit; omega)
      (by simpa using hp.readData) (hp.writeBuf 256 (by decide)))
    intro s' h
    exact ⟨hp.keep h, fun r hr => h.reg r (sep r hr)⟩

theorem kept_ct {c : Prog isa} (h : RelCT isa VG.Proof.Rc2.Arm.Cbc.StepRel c (fun _ _ => True))
    (correct : ∀ s, VG.Proof.Rc2.Arm.Cbc.StepPre s → WP isa c s (fun s' => VG.Proof.Rc2.Arm.Cbc.StepPre s' ∧ ∀ r ∈ VG.Proof.Rc2.Arm.Cbc.kept, s'.gpr r = s.gpr r)) :
    RelCT isa VG.Proof.Rc2.Arm.Cbc.StepRel c VG.Proof.Rc2.Arm.Cbc.StepRel := by
  apply (h.wpDep (fun s₁ s₂ hp => ⟨correct s₁ hp.1, correct s₂ hp.2.1⟩)).mono
    (fun _ _ h => h)
  rintro s₁' s₂' ⟨_, s₁, s₂, hp, h₁, h₂⟩
  refine ⟨h₁.1, h₂.1, fun r hr => ?_⟩
  rw [h₁.2 r hr, h₂.2 r hr]
  exact hp.2.2 r hr

theorem before_ct (d : Spec.Rc2.Direction) :
    RelCT isa VG.Proof.Rc2.Arm.Cbc.StepRel (.block (Impl.Rc2.Arm.Cbc.before d)) VG.Proof.Rc2.Arm.Cbc.StepRel := by
  apply VG.Proof.Rc2.Arm.Cbc.kept_ct _ (VG.Proof.Rc2.Arm.Cbc.before_ok d)
  cases d <;> apply RelCT.taint (A := taint) (Taint.ofRegs VG.Proof.Rc2.Arm.Cbc.kept) (fun _ _ h => VG.Proof.Rc2.Arm.Cbc.agreeKept h.2.2)
  all_goals taint_decide

theorem call_ct (d : Spec.Rc2.Direction) : RelCT isa VG.Proof.Rc2.Arm.Cbc.StepRel (Impl.Rc2.Arm.Cbc.blockCall d) VG.Proof.Rc2.Arm.Cbc.StepRel := by
  apply VG.Proof.Rc2.Arm.Cbc.kept_ct
  · cases d <;> apply RelCT.taint (A := taint) (Taint.ofRegs VG.Proof.Rc2.Arm.Cbc.kept) (fun _ _ h => VG.Proof.Rc2.Arm.Cbc.agreeKept h.2.2)
    all_goals taint_decide
  · intro s hp
    apply WP.mono (VG.Proof.Rc2.Arm.Cbc.call_ok d s hp.call)
    intro s' h
    exact ⟨hp.transport h.rd h.wr h.reg, h.reg⟩

theorem after_ct (d : Spec.Rc2.Direction) :
    RelCT isa VG.Proof.Rc2.Arm.Cbc.StepRel (.block (Impl.Rc2.Arm.Cbc.after d)) (fun _ _ => True) := by
  cases d <;> apply RelCT.taint (A := taint) (Taint.ofRegs VG.Proof.Rc2.Arm.Cbc.kept) (fun _ _ h => VG.Proof.Rc2.Arm.Cbc.agreeKept h.2.2)
  all_goals taint_decide

theorem step_ct (d : Spec.Rc2.Direction) :
    RelCT isa VG.Proof.Rc2.Arm.Cbc.StepRel (Impl.Rc2.Arm.Cbc.step d) VG.Proof.Rc2.Arm.Cbc.StepRel := by
  apply VG.Proof.Rc2.Arm.Cbc.kept_ct ((VG.Proof.Rc2.Arm.Cbc.before_ct d).seq ((VG.Proof.Rc2.Arm.Cbc.call_ct d).seq (VG.Proof.Rc2.Arm.Cbc.after_ct d)))
  intro s hp
  apply WP.mono (VG.Proof.Rc2.Arm.Cbc.step_ok d s hp)
  intro s' h
  exact ⟨h.toPinned.pre hp, h.reg⟩

theorem body_ct (d : Spec.Rc2.Direction) :
    RelCT isa VG.Proof.Rc2.Arm.Cbc.StepRel (Impl.Rc2.Arm.Cbc.body d) (fun _ _ => True) := by
  apply (VG.Proof.Rc2.Arm.Cbc.step_ct d).seq
  apply RelCT.taint (A := taint) (Taint.ofRegs VG.Proof.Rc2.Arm.Cbc.kept) (fun _ _ h => VG.Proof.Rc2.Arm.Cbc.agreeKept h.2.2)
  taint_decide

end VG.Proof.Rc2.Arm.Cbc

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.Arm.Cbc.Verified`. -/
section

section

section

/-! # Frames for successive CBC blocks -/

namespace VG.Proof.Rc2.Arm.Cbc

open VG VG.Arm

def loopWrites (s : State) (n : Nat) : List Region := [VG.Proof.Rc2.Arm.Cbc.ivR s, VG.Proof.Rc2.Arm.Cbc.dataR s n, ⟨State.addr (s.gpr .r2), 264⟩]

theorem loopFrame_slice {s s' : State} {n m i : Nat} {a b : Mem}
    (h : Frame (VG.Proof.Rc2.Arm.Cbc.loopWrites s' m) a b) (bound : i + m ≤ n)
    (iv : s'.gpr .r4 = s.gpr .r4) (buf : s'.gpr .r2 = s.gpr .r2)
    (ptr : State.addr (s'.gpr .r1) = State.addr (s.gpr .r1) + BitVec.ofNat 64 (8 * i)) :
    Frame (VG.Proof.Rc2.Arm.Cbc.loopWrites s n) a b := by
  apply h.sub
  intro r hr
  simp only [VG.Proof.Rc2.Arm.Cbc.loopWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · refine ⟨VG.Proof.Rc2.Arm.Cbc.ivR s, by simp [VG.Proof.Rc2.Arm.Cbc.loopWrites], ?_⟩
    change Region.Sub ⟨State.addr (s'.gpr .r4), 8⟩ ⟨State.addr (s.gpr .r4), 8⟩
    rw [iv]; exact fun _ h => h
  · refine ⟨VG.Proof.Rc2.Arm.Cbc.dataR s n, by simp [VG.Proof.Rc2.Arm.Cbc.loopWrites], ?_⟩
    change Region.Sub ⟨State.addr (s'.gpr .r1), 8 * m⟩ ⟨State.addr (s.gpr .r1), 8 * n⟩
    rw [ptr]
    exact Offset.sub_base _ (by omega)
  · refine ⟨⟨State.addr (s.gpr .r2), 264⟩, by simp [VG.Proof.Rc2.Arm.Cbc.loopWrites], ?_⟩
    rw [buf]; exact fun _ h => h

theorem BodyPost.frame {d : Spec.Rc2.Direction} {s s' : State} {n : Nat}
    (h : VG.Proof.Rc2.Arm.Cbc.BodyPost d s n s') (hn : 1 ≤ n) : Frame (VG.Proof.Rc2.Arm.Cbc.loopWrites s n) s.mem s'.mem :=
  VG.Proof.Rc2.Arm.Cbc.loopFrame_slice (m := 1) (i := 0) h.mem hn rfl rfl (by simp)

theorem BodyPost.schedule {d : Spec.Rc2.Direction} {s s' : State} {n : Nat}
    (h : VG.Proof.Rc2.Arm.Cbc.BodyPost d s n s') (hp : VG.Proof.Rc2.Arm.Cbc.StepPre s) :
    Spec.Rc2.scheduleAt s'.mem (State.addr (s.gpr .r0)) = Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0)) := by
  apply scheduleAt_frame h.mem
  simpa only [VG.Proof.Rc2.Arm.Cbc.stepWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro hp.keyIv (And.intro hp.keyData
      (hp.keyBuf.sub_right (Region.sub_prefix (by decide : 264 ≤ 512))))

theorem BodyPost.tailData {d : Spec.Rc2.Direction} {s s' : State} {n : Nat}
    (h : VG.Proof.Rc2.Arm.Cbc.BodyPost d s (n + 1) s') (hp : VG.Proof.Rc2.Arm.Cbc.StepPre s (n + 1)) (bound : 8 * (n + 1) ≤ 2 ^ 64) :
    Spec.Rc2.blocksAt s'.mem (State.addr (s.gpr .r1) + 8) n = Spec.Rc2.blocksAt s.mem (State.addr (s.gpr .r1) + 8) n := by
  have sub : Region.Sub ⟨State.addr (s.gpr .r1) + 8, 8 * n⟩ (VG.Proof.Rc2.Arm.Cbc.dataR s (n + 1)) :=
    Offset.sub_base _ (by change 8 + 8 * n ≤ 8 * (n + 1); omega)
  have sep : (Region.mk (State.addr (s.gpr .r1) + 8) (8 * n)).Disjoint (VG.Proof.Rc2.Arm.Cbc.dataR s) :=
    Offset.disjoint_base _ (d := 8) (n := 8 * n) (k := 8) (by decide) (by omega)
  apply blocksAt_frame h.mem
  simpa only [VG.Proof.Rc2.Arm.Cbc.stepWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro ((hp.ivData.sub_right sub).symm) (And.intro sep
      ((hp.dataBuf.sub_left sub).sub_right (Region.sub_prefix (by decide : 264 ≤ 512))))

theorem firstBlock_frame {d : Spec.Rc2.Direction} {s s' : State} {n : Nat} {m : Mem}
    (h : VG.Proof.Rc2.Arm.Cbc.BodyPost d s (n + 1) s') (hp : VG.Proof.Rc2.Arm.Cbc.StepPre s (n + 1)) (bound : 8 * (n + 1) ≤ 2 ^ 64)
    (hn : 1 ≤ n)
    (frame : Frame (VG.Proof.Rc2.Arm.Cbc.loopWrites s' n) s'.mem m) :
    Spec.Rc2.blockAt m (State.addr (s.gpr .r1)) = Spec.Rc2.blockAt s'.mem (State.addr (s.gpr .r1)) := by
  have first : Region.Sub (VG.Proof.Rc2.Arm.Cbc.dataR s) (VG.Proof.Rc2.Arm.Cbc.dataR s (n + 1)) := Region.sub_prefix (by change 8 ≤ 8 * (n + 1); omega)
  have sep : (VG.Proof.Rc2.Arm.Cbc.dataR s).Disjoint ⟨State.addr (s.gpr .r1) + 8, 8 * n⟩ :=
    Offset.base_disjoint _ (e := 8) (n := 8 * n) (k := 8) (by decide) (by omega)
  have ptr : State.addr (s'.gpr .r1) = State.addr (s.gpr .r1) + 8 := by
    rw [h.ptr]
    exact addr_add (k := 8) (by have := hp.dataFit; omega)
  apply blockAt_frame frame
  have iv := h.reg .r4 (by decide) (by decide) (by decide)
  have buf := h.reg .r2 (by decide) (by decide) (by decide)
  simpa only [VG.Proof.Rc2.Arm.Cbc.loopWrites, VG.Proof.Rc2.Arm.Cbc.ivR, VG.Proof.Rc2.Arm.Cbc.dataR, iv, buf, ptr,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro ((hp.ivData.sub_right first).symm) (And.intro sep
      ((hp.dataBuf.sub_left first).sub_right (Region.sub_prefix (by decide : 264 ≤ 512))))

end VG.Proof.Rc2.Arm.Cbc

end

/-! # Correctness of the CBC loop on complete blocks -/

namespace VG.Proof.Rc2.Arm.Cbc

open VG VG.Arm

structure LoopPost (d : Spec.Rc2.Direction) (s : State) (n : Nat) (s' : State) : Prop where
  ptr : s'.gpr .r1 = s.gpr .r1 + BitVec.ofNat 32 (8 * n)
  count : s'.gpr .r5 = 0
  reg : ∀ r ∈ VG.Proof.Rc2.Arm.Cbc.kept, r ≠ .r1 → r ≠ .r5 → s'.gpr r = s.gpr r
  callee : ∀ r ∈ VG.Proof.Rc2.Arm.Cbc.savedAcrossCall, r ≠ .r5 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame (VG.Proof.Rc2.Arm.Cbc.loopWrites s n) s.mem s'.mem
  data : Spec.Rc2.blocksAt s'.mem (State.addr (s.gpr .r1)) n =
    (Spec.Rc2.cbc (Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))) d
      (Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r4))) (Spec.Rc2.blocksAt s.mem (State.addr (s.gpr .r1)) n)).1
  iv : Spec.Rc2.blockAt s'.mem (State.addr (s.gpr .r4)) =
    (Spec.Rc2.cbc (Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))) d
      (Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r4))) (Spec.Rc2.blocksAt s.mem (State.addr (s.gpr .r1)) n)).2

theorem loop_ok (d : Spec.Rc2.Direction) (n : Nat) :
    ∀ s : State, 1 ≤ n → 8 * n ≤ 2 ^ 32 → VG.Proof.Rc2.Arm.Cbc.StepPre s n → s.gpr .r5 = BitVec.ofNat 32 n →
      WP isa (.loop (Impl.Rc2.Arm.Cbc.body d) .ne) s (VG.Proof.Rc2.Arm.Cbc.LoopPost d s n) := by
  induction n with
  | zero => intro s hn; omega
  | succ n ih =>
    intro s hn bound hp count
    obtain ⟨t₁, s₁, exec₁, h₁⟩ := VG.Proof.Rc2.Arm.Cbc.body_ok d s (n + 1) hn (by omega) count (hp.head hn)
    by_cases hz : n = 0
    · subst n
      refine ⟨_, s₁, Exec.loopExit exec₁ ?_, ?_⟩
      · simp only [VG.Proof.Rc2.Arm.Cbc.eval_nonzeroCount, h₁.flag, decide_true, Option.map_some, Bool.not_true]
      · refine ⟨h₁.ptr, h₁.count, h₁.reg, h₁.callee, h₁.rd, h₁.wr, h₁.frame (by decide), ?_, ?_⟩
        · rw [blocksAt_cons, blocksAt_cons]
          simp only [Spec.Rc2.blocksAt, List.range_zero, List.map_nil, Spec.Rc2.cbc]
          exact congrArg (· :: []) h₁.data
        · rw [blocksAt_cons]
          simp only [Spec.Rc2.blocksAt, List.range_zero, List.map_nil, Spec.Rc2.cbc]
          exact h₁.iv
    · have hp₁ := h₁.tail hp (by omega)
      obtain ⟨t₂, s₂, exec₂, h₂⟩ := ih s₁ (by omega) (by omega) hp₁ (by simpa using h₁.count)
      refine ⟨_, s₂, Exec.loopNext exec₁ ?_ exec₂, ?_⟩
      · have he : n + 1 ≠ 1 := by omega
        simp only [VG.Proof.Rc2.Arm.Cbc.eval_nonzeroCount, h₁.flag, he, decide_false, Option.map_some, Bool.not_false]
      · have key := h₁.schedule (hp.head hn)
        have tail := h₁.tailData hp (by omega)
        have data := h₂.data
        have iv := h₂.iv
        have ki := h₁.reg .r0 (by decide) (by decide) (by decide)
        have vi := h₁.reg .r4 (by decide) (by decide) (by decide)
        have bi := h₁.reg .r2 (by decide) (by decide) (by decide)
        have ptr : State.addr (s₁.gpr .r1) = State.addr (s.gpr .r1) + 8 := by
          rw [h₁.ptr]; exact addr_add (k := 8) (by have := hp.dataFit; omega)
        rw [ki, vi, ptr, key, tail, h₁.iv] at data
        rw [ki, vi, ptr, key, tail, h₁.iv] at iv
        refine ⟨?_, h₂.count, ?_, ?_, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, ?_, ?_, ?_⟩
        · rw [h₂.ptr, h₁.ptr, BitVec.add_assoc]
          exact congrArg (s.gpr .r1 + ·) (by
            change BitVec.ofNat 32 8 + BitVec.ofNat 32 (8 * n) = _
            rw [← BitVec.ofNat_add]
            exact congrArg (BitVec.ofNat 32) (by omega))
        · intro r hr hs hb
          exact (h₂.reg r hr hs hb).trans (h₁.reg r hr hs hb)
        · intro r hr hb
          exact (h₂.callee r hr hb).trans (h₁.callee r hr hb)
        · exact (h₁.frame hn).trans (VG.Proof.Rc2.Arm.Cbc.loopFrame_slice (i := 1) h₂.mem (by omega) vi bi ptr)
        · have first := VG.Proof.Rc2.Arm.Cbc.firstBlock_frame h₁ hp (by omega) (by omega) h₂.mem
          rw [blocksAt_cons, first, h₁.data, data, blocksAt_cons]
          rfl
        · rw [blocksAt_cons]
          exact iv

theorem maybeLoop_ok (d : Spec.Rc2.Direction) (s : State) (n : Nat) (bound : 8 * n ≤ 2 ^ 32)
    (hp : VG.Proof.Rc2.Arm.Cbc.StepPre s n) (count : s.gpr .r5 = BitVec.ofNat 32 n)
    (flag : VG.Proof.Rc2.Arm.Cbc.zeroCount s = some (s.gpr .r5 == 0)) :
    WP isa (.ite .eq (.block []) (.loop (Impl.Rc2.Arm.Cbc.body d) .ne)) s (VG.Proof.Rc2.Arm.Cbc.LoopPost d s n) := by
  have eqZero := counter_eq n 0 (by omega) (by decide)
  simp only [BitVec.sub_zero] at eqZero
  have flag' : VG.Proof.Rc2.Arm.Cbc.zeroCount s = some (decide (n = 0)) := by
    rw [flag, count]
    exact congrArg some eqZero
  by_cases hz : n = 0
  · subst n
    apply WP.ite true (by simp only [VG.Proof.Rc2.Arm.Cbc.eval_zeroCount, flag', decide_true])
    · intro _
      apply WP.block_nil
      refine ⟨by simp, count, fun _ _ _ _ => rfl, fun _ _ _ => rfl, rfl, rfl, Frame.refl _ _, ?_, ?_⟩
      · rfl
      · rfl
    · simp
  · apply WP.ite false (by simp only [VG.Proof.Rc2.Arm.Cbc.eval_zeroCount, flag', hz, decide_false])
    · simp
    · intro _
      exact VG.Proof.Rc2.Arm.Cbc.loop_ok d n s (by omega) bound hp count

theorem LoopPost.scratchRead {d : Spec.Rc2.Direction} {s s' : State} {n : Nat}
    (h : VG.Proof.Rc2.Arm.Cbc.LoopPost d s n s') (hp : VG.Proof.Rc2.Arm.Cbc.StepPre s n) (i : Nat) (lo : 264 ≤ i) (hi : i + 4 ≤ 512) :
    s'.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 i) 32 = s.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 i) 32 := by
  have sub : Region.Sub ⟨State.addr (s.gpr .r2) + BitVec.ofNat 64 i, 4⟩ (VG.Proof.Rc2.Arm.Cbc.bufR s) := Offset.sub_base _ hi
  have sep : (Region.mk (State.addr (s.gpr .r2) + BitVec.ofNat 64 i) 4).Disjoint ⟨State.addr (s.gpr .r2), 264⟩ :=
    Offset.disjoint_base _ lo (by omega)
  apply h.mem.readW (r := ⟨State.addr (s.gpr .r2) + BitVec.ofNat 64 i, 4⟩) (Region.contains_self _ _)
    (hn := by decide)
  simpa only [VG.Proof.Rc2.Arm.Cbc.loopWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro ((hp.ivBuf.sub_right sub).symm) (And.intro ((hp.dataBuf.sub_right sub).symm)
      sep)

end VG.Proof.Rc2.Arm.Cbc

end

section

/-! # CBC register saves, setup, and restoration -/

namespace VG.Proof.Rc2.Arm.Cbc

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc2.Arm

def callerSaved : List Reg := [.r4, .r5, .r6, .r7, .lr]

def savedMem (s : State) : Mem :=
  (((((s.mem.writeW (State.addr (s.gpr .r12) + BitVec.ofNat 64 264) (s.gpr .r4)).writeW (State.addr (s.gpr .r12) + BitVec.ofNat 64 268) (s.gpr .r5)).writeW (State.addr (s.gpr .r12) + BitVec.ofNat 64 272) (s.gpr .r6)).writeW (State.addr (s.gpr .r12) + BitVec.ofNat 64 276) (s.gpr .r7)).writeW (State.addr (s.gpr .r12) + BitVec.ofNat 64 280) (s.gpr .lr))

theorem save_ok (s : State)
    (fit : (s.gpr .r12).toNat + 512 ≤ 2 ^ 32)
    (w0 : InRegions s.wr (State.addr (s.gpr .r12) + BitVec.ofNat 64 264) 4)
    (w1 : InRegions s.wr (State.addr (s.gpr .r12) + BitVec.ofNat 64 268) 4)
    (w2 : InRegions s.wr (State.addr (s.gpr .r12) + BitVec.ofNat 64 272) 4)
    (w3 : InRegions s.wr (State.addr (s.gpr .r12) + BitVec.ofNat 64 276) 4)
    (w4 : InRegions s.wr (State.addr (s.gpr .r12) + BitVec.ofNat 64 280) 4)
    : ∃ s', runBlock isa Impl.Rc2.Arm.Cbc.save s = some s' ∧ Keep [] {s with mem := VG.Proof.Rc2.Arm.Cbc.savedMem s} s' := by
  have a264 : State.addr (s.gpr .r12 + BitVec.ofNat 32 264) = State.addr (s.gpr .r12) + BitVec.ofNat 64 264 := addr_add (by omega)
  have a268 : State.addr (s.gpr .r12 + BitVec.ofNat 32 268) = State.addr (s.gpr .r12) + BitVec.ofNat 64 268 := addr_add (by omega)
  have a272 : State.addr (s.gpr .r12 + BitVec.ofNat 32 272) = State.addr (s.gpr .r12) + BitVec.ofNat 64 272 := addr_add (by omega)
  have a276 : State.addr (s.gpr .r12 + BitVec.ofNat 32 276) = State.addr (s.gpr .r12) + BitVec.ofNat 64 276 := addr_add (by omega)
  have a280 : State.addr (s.gpr .r12 + BitVec.ofNat 32 280) = State.addr (s.gpr .r12) + BitVec.ofNat 64 280 := addr_add (by omega)
  refine ⟨_, by
    simp only [Impl.Rc2.Arm.Cbc.save, runBlock_cons, runStep_some, runBlock_nil,
      exec, Nat.reduceLT, ite_true, State.store32,
      a264, a268, a272, a276, a280, w0, w1, w2, w3, w4]
    rfl, ?_⟩
  exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem savedMem_frame (s : State) : Frame [⟨State.addr (s.gpr .r12), 512⟩] s.mem (VG.Proof.Rc2.Arm.Cbc.savedMem s) := by
  unfold VG.Proof.Rc2.Arm.Cbc.savedMem
  apply Frame.writeW (r := ⟨State.addr (s.gpr .r12), 512⟩) (hr := List.mem_cons_self) (hb := Offset.contains_base _ (by decide : 280 + 4 ≤ 512) (by decide))
  apply Frame.writeW (r := ⟨State.addr (s.gpr .r12), 512⟩) (hr := List.mem_cons_self) (hb := Offset.contains_base _ (by decide : 276 + 4 ≤ 512) (by decide))
  apply Frame.writeW (r := ⟨State.addr (s.gpr .r12), 512⟩) (hr := List.mem_cons_self) (hb := Offset.contains_base _ (by decide : 272 + 4 ≤ 512) (by decide))
  apply Frame.writeW (r := ⟨State.addr (s.gpr .r12), 512⟩) (hr := List.mem_cons_self) (hb := Offset.contains_base _ (by decide : 268 + 4 ≤ 512) (by decide))
  apply Frame.writeW (r := ⟨State.addr (s.gpr .r12), 512⟩) (hr := List.mem_cons_self) (hb := Offset.contains_base _ (by decide : 264 + 4 ≤ 512) (by decide))
  exact Frame.refl _ _

theorem savedMem_r4 (s : State) : (VG.Proof.Rc2.Arm.Cbc.savedMem s).readW (State.addr (s.gpr .r12) + BitVec.ofNat 64 264) 32 = s.gpr .r4 := by
  rw [VG.Proof.Rc2.Arm.Cbc.savedMem, Mem.readW_writeW_sep (Offset.sep _ (by decide : 264 + 4 ≤ 280 ∨ 280 + 4 ≤ 264) (by decide) (by decide)) (by decide), Mem.readW_writeW_sep (Offset.sep _ (by decide : 264 + 4 ≤ 276 ∨ 276 + 4 ≤ 264) (by decide) (by decide)) (by decide), Mem.readW_writeW_sep (Offset.sep _ (by decide : 264 + 4 ≤ 272 ∨ 272 + 4 ≤ 264) (by decide) (by decide)) (by decide), Mem.readW_writeW_sep (Offset.sep _ (by decide : 264 + 4 ≤ 268 ∨ 268 + 4 ≤ 264) (by decide) (by decide)) (by decide), Mem.readW_writeW_self32]

theorem savedMem_r5 (s : State) : (VG.Proof.Rc2.Arm.Cbc.savedMem s).readW (State.addr (s.gpr .r12) + BitVec.ofNat 64 268) 32 = s.gpr .r5 := by
  rw [VG.Proof.Rc2.Arm.Cbc.savedMem, Mem.readW_writeW_sep (Offset.sep _ (by decide : 268 + 4 ≤ 280 ∨ 280 + 4 ≤ 268) (by decide) (by decide)) (by decide), Mem.readW_writeW_sep (Offset.sep _ (by decide : 268 + 4 ≤ 276 ∨ 276 + 4 ≤ 268) (by decide) (by decide)) (by decide), Mem.readW_writeW_sep (Offset.sep _ (by decide : 268 + 4 ≤ 272 ∨ 272 + 4 ≤ 268) (by decide) (by decide)) (by decide), Mem.readW_writeW_self32]

theorem savedMem_r6 (s : State) : (VG.Proof.Rc2.Arm.Cbc.savedMem s).readW (State.addr (s.gpr .r12) + BitVec.ofNat 64 272) 32 = s.gpr .r6 := by
  rw [VG.Proof.Rc2.Arm.Cbc.savedMem, Mem.readW_writeW_sep (Offset.sep _ (by decide : 272 + 4 ≤ 280 ∨ 280 + 4 ≤ 272) (by decide) (by decide)) (by decide), Mem.readW_writeW_sep (Offset.sep _ (by decide : 272 + 4 ≤ 276 ∨ 276 + 4 ≤ 272) (by decide) (by decide)) (by decide), Mem.readW_writeW_self32]

theorem savedMem_r7 (s : State) : (VG.Proof.Rc2.Arm.Cbc.savedMem s).readW (State.addr (s.gpr .r12) + BitVec.ofNat 64 276) 32 = s.gpr .r7 := by
  rw [VG.Proof.Rc2.Arm.Cbc.savedMem, Mem.readW_writeW_sep (Offset.sep _ (by decide : 276 + 4 ≤ 280 ∨ 280 + 4 ≤ 276) (by decide) (by decide)) (by decide), Mem.readW_writeW_self32]

theorem savedMem_lr (s : State) : (VG.Proof.Rc2.Arm.Cbc.savedMem s).readW (State.addr (s.gpr .r12) + BitVec.ofNat 64 280) 32 = s.gpr .lr := by
  rw [VG.Proof.Rc2.Arm.Cbc.savedMem, Mem.readW_writeW_self32]

theorem setup_ok (s : State) :
    ∃ s', runBlock isa Impl.Rc2.Arm.Cbc.setup s = some s' ∧
      s'.gpr .r4 = s.gpr .r1 ∧ s'.gpr .r5 = s.gpr .r3 ∧
      s'.gpr .r1 = s.gpr .r2 ∧ s'.gpr .r2 = s.gpr .r12 ∧
      VG.Proof.Rc2.Arm.Cbc.zeroCount s' = some (s.gpr .r3 == 0) ∧ Keep [.r4, .r5, .r1, .r2] s s' := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Impl.Rc2.Arm.Cbc.setup, rr, runBlock_cons,
      runStep_some, exec, Op2.eval, Option.map_some, gpr_setReg]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_subFlags, gpr_setReg, reduceCtorEq, ite_true, ite_false]
  · simp only [gpr_subFlags, gpr_setReg, reduceCtorEq, ite_true, ite_false]
  · simp only [gpr_subFlags, gpr_setReg, reduceCtorEq, ite_true, ite_false]
  · simp only [gpr_subFlags, gpr_setReg_self]
  · change some ((s.gpr .r3 - 0) == 0) = _
    exact congrArg (fun x : BitVec 32 => some (x == 0)) (by bv_omega)
  · refine ⟨?_, rfl, rfl, rfl⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_subFlags, gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem restore_ok (s : State) (values : Reg → BitVec 32)
    (fit : (s.gpr .r2).toNat + 512 ≤ 2 ^ 32)
    (r0 : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r2) + BitVec.ofNat 64 264) 4)
    (v0 : s.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 264) 32 = values .r4)
    (r1 : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r2) + BitVec.ofNat 64 268) 4)
    (v1 : s.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 268) 32 = values .r5)
    (r2 : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r2) + BitVec.ofNat 64 272) 4)
    (v2 : s.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 272) 32 = values .r6)
    (r3 : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r2) + BitVec.ofNat 64 276) 4)
    (v3 : s.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 276) 32 = values .r7)
    (r4 : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r2) + BitVec.ofNat 64 280) 4)
    (v4 : s.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 280) 32 = values .lr)
    : ∃ s', runBlock isa Impl.Rc2.Arm.Cbc.restore s = some s' ∧
      (∀ r ∈ VG.Proof.Rc2.Arm.Cbc.callerSaved, s'.gpr r = values r) ∧ Keep VG.Proof.Rc2.Arm.Cbc.callerSaved s s' := by
  have a264 : State.addr (s.gpr .r2 + BitVec.ofNat 32 264) = State.addr (s.gpr .r2) + BitVec.ofNat 64 264 := addr_add (by omega)
  have a268 : State.addr (s.gpr .r2 + BitVec.ofNat 32 268) = State.addr (s.gpr .r2) + BitVec.ofNat 64 268 := addr_add (by omega)
  have a272 : State.addr (s.gpr .r2 + BitVec.ofNat 32 272) = State.addr (s.gpr .r2) + BitVec.ofNat 64 272 := addr_add (by omega)
  have a276 : State.addr (s.gpr .r2 + BitVec.ofNat 32 276) = State.addr (s.gpr .r2) + BitVec.ofNat 64 276 := addr_add (by omega)
  have a280 : State.addr (s.gpr .r2 + BitVec.ofNat 32 280) = State.addr (s.gpr .r2) + BitVec.ofNat 64 280 := addr_add (by omega)
  refine ⟨_, by
    simp only [Impl.Rc2.Arm.Cbc.restore, runBlock_cons, runStep_some, runBlock_nil,
      exec, Nat.reduceLT, ite_true, State.load32, gpr_setReg, reduceCtorEq, ite_false,
      mem_setReg, rd_setReg, wr_setReg, Option.map_some,
      a264, a268, a272, a276, a280, r0, r1, r2, r3, r4, v0, v1, v2, v3, v4]
    rfl, ?_⟩
  constructor
  · intro r hr
    simp only [VG.Proof.Rc2.Arm.Cbc.callerSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false]
  · refine ⟨?_, rfl, rfl, rfl⟩
    intro r hr
    simp only [VG.Proof.Rc2.Arm.Cbc.callerSaved, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

end VG.Proof.Rc2.Arm.Cbc

end

section

section

/-! # Constant-time CBC loops -/

namespace VG.Proof.Rc2.Arm.Cbc

open VG VG.Arm VG.Impl.Rc2.Arm

def LoopRel (n : Nat) (s₁ s₂ : State) : Prop :=
  VG.Proof.Rc2.Arm.Cbc.StepPre s₁ n ∧ VG.Proof.Rc2.Arm.Cbc.StepPre s₂ n ∧ VG.Proof.Rc2.Arm.Cbc.EqKept s₁ s₂ ∧
    s₁.gpr .r5 = BitVec.ofNat 32 n ∧ s₂.gpr .r5 = BitVec.ofNat 32 n ∧ 1 ≤ n

theorem bodyRel (d : Spec.Rc2.Direction) (n : Nat) :
    RelCT isa (VG.Proof.Rc2.Arm.Cbc.LoopRel n) (Impl.Rc2.Arm.Cbc.body d) (fun s₁ s₂ =>
      VG.Proof.Rc2.Arm.Cbc.EqKept s₁ s₂ ∧ eval .ne s₁ = eval .ne s₂ ∧
        (eval .ne s₁ = some true → ∃ m < n, VG.Proof.Rc2.Arm.Cbc.LoopRel m s₁ s₂)) := by
  have ct : RelCT isa (VG.Proof.Rc2.Arm.Cbc.LoopRel n) (Impl.Rc2.Arm.Cbc.body d) (fun _ _ => True) :=
    (VG.Proof.Rc2.Arm.Cbc.body_ct d).mono (fun _ _ h => ⟨h.1.head h.2.2.2.2.2, h.2.1.head h.2.2.2.2.2, h.2.2.1⟩)
      (fun _ _ _ => trivial)
  have correct (s₁ s₂ : State) (h : VG.Proof.Rc2.Arm.Cbc.LoopRel n s₁ s₂) :=
    And.intro (VG.Proof.Rc2.Arm.Cbc.body_ok d s₁ n h.2.2.2.2.2 (by have := h.1.dataFit; omega) h.2.2.2.1 (h.1.head h.2.2.2.2.2))
      (VG.Proof.Rc2.Arm.Cbc.body_ok d s₂ n h.2.2.2.2.2 (by have := h.2.1.dataFit; omega) h.2.2.2.2.1 (h.2.1.head h.2.2.2.2.2))
  apply (ct.wpDep correct).mono (fun _ _ h => h)
  rintro s₁' s₂' ⟨_, s₁, s₂, hp, h₁, h₂⟩
  have eq : VG.Proof.Rc2.Arm.Cbc.EqKept s₁' s₂' := by
    intro r hr
    by_cases hptr : r = .r1
    · subst r; rw [h₁.ptr, h₂.ptr, hp.2.2.1 .r1 (by decide)]
    · by_cases hcount : r = .r5
      · subst r; rw [h₁.count, h₂.count]
      · rw [h₁.reg r hr hptr hcount, h₂.reg r hr hptr hcount]
        exact hp.2.2.1 r hr
  refine ⟨eq, by rw [VG.Proof.Rc2.Arm.Cbc.eval_nonzeroCount, VG.Proof.Rc2.Arm.Cbc.eval_nonzeroCount, h₁.flag, h₂.flag], ?_⟩
  intro hcontinue
  have hn : 1 ≤ n := hp.2.2.2.2.2
  have hm : 1 ≤ n - 1 := by
    rw [VG.Proof.Rc2.Arm.Cbc.eval_nonzeroCount, h₁.flag] at hcontinue
    by_contra h
    have e : n = 1 := by omega
    simp only [e, decide_true, Option.map_some, Bool.not_true, Option.some.injEq, Bool.false_eq_true] at hcontinue
  refine ⟨n - 1, by omega, ?_, ?_, eq, h₁.count, h₂.count, hm⟩
  · have e : n = (n - 1) + 1 := by omega
    rw [e] at h₁ hp
    exact h₁.tail hp.1 hm
  · have e : n = (n - 1) + 1 := by omega
    rw [e] at h₂ hp
    exact h₂.tail hp.2.1 hm

theorem loop_ct (d : Spec.Rc2.Direction) (n : Nat) :
    RelCT isa (VG.Proof.Rc2.Arm.Cbc.LoopRel n) (.loop (Impl.Rc2.Arm.Cbc.body d) .ne) VG.Proof.Rc2.Arm.Cbc.EqKept := by
  refine RelCT.loop (M := isa) (body := Impl.Rc2.Arm.Cbc.body d) (c := .ne) (Q := VG.Proof.Rc2.Arm.Cbc.EqKept) VG.Proof.Rc2.Arm.Cbc.LoopRel ?_ n
  intro m
  exact (VG.Proof.Rc2.Arm.Cbc.bodyRel d m).mono (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, fun _ => h.1, h.2.2⟩)

def MaybeRel (s₁ s₂ : State) : Prop :=
  ∃ n, VG.Proof.Rc2.Arm.Cbc.StepPre s₁ n ∧ VG.Proof.Rc2.Arm.Cbc.StepPre s₂ n ∧ VG.Proof.Rc2.Arm.Cbc.EqKept s₁ s₂ ∧
    s₁.gpr .r5 = BitVec.ofNat 32 n ∧ s₂.gpr .r5 = BitVec.ofNat 32 n ∧
    VG.Proof.Rc2.Arm.Cbc.zeroCount s₁ = some (decide (n = 0)) ∧ VG.Proof.Rc2.Arm.Cbc.zeroCount s₂ = some (decide (n = 0))

theorem maybeLoop_ct (d : Spec.Rc2.Direction) :
    RelCT isa VG.Proof.Rc2.Arm.Cbc.MaybeRel (.ite .eq (.block []) (.loop (Impl.Rc2.Arm.Cbc.body d) .ne)) VG.Proof.Rc2.Arm.Cbc.EqKept := by
  apply RelCT.ite
  · rintro s₁ s₂ ⟨n, _, _, _, _, _, h₁, h₂⟩
    change VG.Proof.Rc2.Arm.Cbc.zeroCount s₁ = VG.Proof.Rc2.Arm.Cbc.zeroCount s₂
    rw [h₁, h₂]
  · apply RelCT.block_nil
    rintro s₁ s₂ ⟨⟨n, _, _, eq, _⟩, _⟩
    exact eq
  · apply RelCT.exists_ (fun n => VG.Proof.Rc2.Arm.Cbc.loop_ct d n) |>.mono
    · rintro s₁ s₂ ⟨⟨n, h₁, h₂, eq, c₁, c₂, z₁, _⟩, branch⟩
      refine ⟨n, h₁, h₂, eq, c₁, c₂, ?_⟩
      change VG.Proof.Rc2.Arm.Cbc.zeroCount s₁ = some false at branch
      rw [z₁] at branch
      have hn : n ≠ 0 := by intro hz; simp [hz] at branch
      omega
    · exact fun _ _ h => h

end VG.Proof.Rc2.Arm.Cbc

end

section

/-! # CBC's function-level contract -/

namespace VG.Proof.Rc2.Arm.Cbc

open VG VG.Arm

def contract (d : Spec.Rc2.Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), 128⟩
    let iv : Region := ⟨State.addr (s.gpr .r1), 8⟩
    let data : Region := ⟨State.addr (s.gpr .r2), 8 * (s.gpr .r3).toNat⟩
    let buf : Region := ⟨State.addr (stackArg s 0), 512⟩
    let args : Region := ⟨stackArgAddr s 0, 4⟩
    s.rd = [key, args] ∧ s.wr = [iv, data, buf] ∧ key.Disjoint iv ∧ key.Disjoint data ∧ key.Disjoint buf ∧
      iv.Disjoint data ∧ iv.Disjoint buf ∧ data.Disjoint buf ∧ iv.Disjoint args ∧ data.Disjoint args ∧ buf.Disjoint args ∧
      (s.gpr .r0).toNat + 128 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 8 ≤ 2 ^ 32 ∧
      (stackArg s 0).toNat + 512 ≤ 2 ^ 32 ∧ s.sp.toNat + 4 ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + 8 * (s.gpr .r3).toNat ≤ 2 ^ 32
  post s s' :=
    let out := Spec.Rc2.cbc (Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))) d
      (Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r1))) (Spec.Rc2.blocksAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
    Spec.Rc2.blocksAt s'.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat = out.1 ∧
      Spec.Rc2.blockAt s'.mem (State.addr (s.gpr .r1)) = out.2
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0

end VG.Proof.Rc2.Arm.Cbc

end

/-! # CBC's public prologue and stack argument -/

namespace VG.Proof.Rc2.Arm.Cbc

open VG VG.Arm VG.Impl.Rc2.Arm

def startCode : Prog isa := .seq (.block [.ldrSp .r12 0])
  (.block (Impl.Rc2.Arm.Cbc.save ++ Impl.Rc2.Arm.Cbc.setup))

structure StartPost (s s' : State) : Prop where
  pre : VG.Proof.Rc2.Arm.Cbc.StepPre s' (s.gpr .r3).toNat
  key : s'.gpr .r0 = s.gpr .r0
  iv : s'.gpr .r4 = s.gpr .r1
  data : s'.gpr .r1 = s.gpr .r2
  buf : s'.gpr .r2 = stackArg s 0
  count : s'.gpr .r5 = s.gpr .r3
  flag : VG.Proof.Rc2.Arm.Cbc.zeroCount s' = some (s.gpr .r3 == 0)

theorem start_ok (d : Spec.Rc2.Direction) (s : State) (hs : (VG.Proof.Rc2.Arm.Cbc.contract d).pre s) :
    WP isa VG.Proof.Rc2.Arm.Cbc.startCode s (VG.Proof.Rc2.Arm.Cbc.StartPost s) := by
  obtain ⟨hrd, hwr, keyIv, keyData, keyBuf, ivData, ivBuf, dataBuf,
    _ivArgs, _dataArgs, _bufArgs, keyFit, ivFit, bufFit, _spFit, fit⟩ := hs
  have writes (i : Nat) (hi : i + 4 ≤ 512) : InRegions s.wr (State.addr (stackArg s 0) + BitVec.ofNat 64 i) 4 := by
    rw [hwr]
    exact ⟨⟨State.addr (stackArg s 0), 512⟩, by simp, Offset.contains_base _ hi (by omega)⟩
  rw [VG.Proof.Rc2.Arm.Cbc.startCode]
  apply WP.seq
  obtain ⟨s₀, run₀, buf₀, keep₀⟩ := loadScratch_ok s (by
    rw [hrd, hwr]
    exact ⟨⟨stackArgAddr s 0, 4⟩, by simp, Region.contains_self _ _⟩)
  refine WP.of_runBlock ⟨s₀, run₀, ?_⟩
  have g₀ (r : Reg) (hr : r ≠ .r12) := keep₀.reg r (by simpa using hr)
  have writes₀ (i : Nat) (hi : i + 4 ≤ 512) :
      InRegions s₀.wr (State.addr (s₀.gpr .r12) + BitVec.ofNat 64 i) 4 := by
    rw [keep₀.wr, buf₀]; exact writes i hi
  rw [WP.block_append_iff]
  obtain ⟨s₁, run₁, keep₁⟩ := VG.Proof.Rc2.Arm.Cbc.save_ok s₀ (by rw [buf₀]; exact bufFit)
    (writes₀ 264 (by decide)) (writes₀ 268 (by decide)) (writes₀ 272 (by decide))
    (writes₀ 276 (by decide)) (writes₀ 280 (by decide))
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, iv₂, count₂, data₂, buf₂, flag₂, keep₂⟩ := VG.Proof.Rc2.Arm.Cbc.setup_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have g₁ (r : Reg) : s₁.gpr r = s₀.gpr r := keep₁.reg r (by simp)
  rw [g₁, g₀ .r1 (by decide)] at iv₂
  rw [g₁, g₀ .r3 (by decide)] at count₂ flag₂
  rw [g₁, g₀ .r2 (by decide)] at data₂
  rw [g₁, buf₀] at buf₂
  have key₂ := (keep₂.reg .r0 (by decide)).trans ((g₁ .r0).trans (g₀ .r0 (by decide)))
  have rd₂ := keep₂.rd.trans (keep₁.rd.trans keep₀.rd)
  have wr₂ := keep₂.wr.trans (keep₁.wr.trans keep₀.wr)
  have hp₂ : VG.Proof.Rc2.Arm.Cbc.StepPre s₂ (s.gpr .r3).toNat := by
    constructor
    · rw [key₂]; exact keyFit
    · rw [iv₂]; exact ivFit
    · rw [data₂]; exact fit
    · rw [buf₂]; exact bufFit
    · simp only [Covers, VG.Proof.Rc2.Arm.Cbc.keyR, VG.Proof.Rc2.Arm.Cbc.ivR, VG.Proof.Rc2.Arm.Cbc.dataR, VG.Proof.Rc2.Arm.Cbc.bufR, key₂, iv₂, data₂, buf₂, rd₂, wr₂, hrd, hwr]
      intro a n ⟨r, hr, hc⟩
      exact ⟨r, by simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; grind, hc⟩
    · simp only [Covers, VG.Proof.Rc2.Arm.Cbc.ivR, VG.Proof.Rc2.Arm.Cbc.dataR, VG.Proof.Rc2.Arm.Cbc.bufR, iv₂, data₂, buf₂, wr₂, hwr]
      intro a n ⟨r, hr, hc⟩
      exact ⟨r, by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; grind, hc⟩
    · simpa only [VG.Proof.Rc2.Arm.Cbc.keyR, VG.Proof.Rc2.Arm.Cbc.ivR, key₂, iv₂] using keyIv
    · simpa only [VG.Proof.Rc2.Arm.Cbc.keyR, VG.Proof.Rc2.Arm.Cbc.dataR, key₂, data₂] using keyData
    · simpa only [VG.Proof.Rc2.Arm.Cbc.keyR, VG.Proof.Rc2.Arm.Cbc.bufR, key₂, buf₂] using keyBuf
    · simpa only [VG.Proof.Rc2.Arm.Cbc.ivR, VG.Proof.Rc2.Arm.Cbc.dataR, iv₂, data₂] using ivData
    · simpa only [VG.Proof.Rc2.Arm.Cbc.ivR, VG.Proof.Rc2.Arm.Cbc.bufR, iv₂, buf₂] using ivBuf
    · simpa only [VG.Proof.Rc2.Arm.Cbc.dataR, VG.Proof.Rc2.Arm.Cbc.bufR, data₂, buf₂] using dataBuf
  exact ⟨hp₂, key₂, iv₂, data₂, buf₂, count₂, flag₂⟩

def InitialRel (d : Spec.Rc2.Direction) (s₁ s₂ : State) : Prop :=
  (VG.Proof.Rc2.Arm.Cbc.contract d).pre s₁ ∧ (VG.Proof.Rc2.Arm.Cbc.contract d).pre s₂ ∧ (VG.Proof.Rc2.Arm.Cbc.contract d).pub s₁ s₂

def EqArgs (s₁ s₂ : State) : Prop := ∀ r ∈ ([.r0, .r1, .r2, .r3, .r12] : List Reg), s₁.gpr r = s₂.gpr r

theorem load_trace {s s' : State} {t : List Leak} (h : Exec isa (.block [.ldrSp .r12 0]) s t s') :
    t = [.addr (State.addr s.sp)] := by
  cases h with
  | block h =>
    simp only [execBlock, isa] at h
    cases he : exec (.ldrSp .r12 0) s with
    | none => simp only [he] at h; cases h
    | some u =>
      simp only [he, Option.map_some, List.append_nil, Option.some.injEq, Prod.mk.injEq] at h
      simpa only [addrs, BitVec.add_zero, List.map_cons, List.map_nil] using h.2.symm

theorem load_ct (d : Spec.Rc2.Direction) :
    RelCT isa (VG.Proof.Rc2.Arm.Cbc.InitialRel d) (.block [.ldrSp .r12 0]) VG.Proof.Rc2.Arm.Cbc.EqArgs := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  have read₁ : InRegions (s₁.rd ++ s₁.wr) (stackArgAddr s₁ 0) 4 := by
    rw [hp.1.1, hp.1.2.1]
    exact ⟨⟨stackArgAddr s₁ 0, 4⟩, by simp, Region.contains_self _ _⟩
  have read₂ : InRegions (s₂.rd ++ s₂.wr) (stackArgAddr s₂ 0) 4 := by
    rw [hp.2.1.1, hp.2.1.2.1]
    exact ⟨⟨stackArgAddr s₂ 0, 4⟩, by simp, Region.contains_self _ _⟩
  obtain ⟨u₁, run₁, buf₁, keep₁⟩ := loadScratch_ok s₁ read₁
  obtain ⟨u₂, run₂, buf₂, keep₂⟩ := loadScratch_ok s₂ read₂
  obtain ⟨_, v₁, ev₁, hv₁⟩ := WP.of_runBlock (Q := fun s => s = u₁) ⟨u₁, run₁, rfl⟩
  obtain ⟨_, v₂, ev₂, hv₂⟩ := WP.of_runBlock (Q := fun s => s = u₂) ⟨u₂, run₂, rfl⟩
  have eu₁ : s₁' = u₁ := (Exec.det e₁ ev₁).2.trans hv₁
  have eu₂ : s₂' = u₂ := (Exec.det e₂ ev₂).2.trans hv₂
  obtain ⟨sp, p0, p1, p2, p3, bp⟩ := hp.2.2
  constructor
  · rw [VG.Proof.Rc2.Arm.Cbc.load_trace e₁, VG.Proof.Rc2.Arm.Cbc.load_trace e₂, sp]
  · rw [eu₁, eu₂]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [keep₁.reg .r0 (by decide), keep₂.reg .r0 (by decide)]; exact p0
    · rw [keep₁.reg .r1 (by decide), keep₂.reg .r1 (by decide)]; exact p1
    · rw [keep₁.reg .r2 (by decide), keep₂.reg .r2 (by decide)]; exact p2
    · rw [keep₁.reg .r3 (by decide), keep₂.reg .r3 (by decide)]; exact p3
    · rw [buf₁, buf₂]; exact bp

theorem start_ct (d : Spec.Rc2.Direction) : RelCT isa (VG.Proof.Rc2.Arm.Cbc.InitialRel d) VG.Proof.Rc2.Arm.Cbc.startCode VG.Proof.Rc2.Arm.Cbc.MaybeRel := by
  have ct : RelCT isa (VG.Proof.Rc2.Arm.Cbc.InitialRel d) VG.Proof.Rc2.Arm.Cbc.startCode (fun _ _ => True) := by
    apply (VG.Proof.Rc2.Arm.Cbc.load_ct d).seq
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3, .r12])
      (fun _ _ h => Taint.agree_ofRegs h)
    taint_decide
  apply (ct.wpDep (fun s₁ s₂ h => ⟨VG.Proof.Rc2.Arm.Cbc.start_ok d s₁ h.1, VG.Proof.Rc2.Arm.Cbc.start_ok d s₂ h.2.1⟩)).mono (fun _ _ h => h)
  rintro s₁' s₂' ⟨_, s₁, s₂, hp, h₁, h₂⟩
  obtain ⟨_, p0, p1, p2, p3, bp⟩ := hp.2.2
  refine ⟨(s₁.gpr .r3).toNat, h₁.pre, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [p3]; exact h₂.pre
  · intro r hr
    simp only [VG.Proof.Rc2.Arm.Cbc.kept, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [h₁.key, h₂.key, p0]
    · rw [h₁.data, h₂.data, p2]
    · rw [h₁.buf, h₂.buf, bp]
    · rw [h₁.iv, h₂.iv, p1]
    · rw [h₁.count, h₂.count, p3]
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

end VG.Proof.Rc2.Arm.Cbc

end

section

/-! # Constant-time CBC callers -/

namespace VG.Proof.Rc2.Arm.Cbc

open VG VG.Arm

theorem cbc_constantTime (d : Spec.Rc2.Direction) :
    ConstantTime isa (VG.Proof.Rc2.Arm.Cbc.contract d).pre (VG.Proof.Rc2.Arm.Cbc.contract d).pub (Impl.Rc2.Arm.Cbc.cbc d) := by
  apply RelCT.constantTime
  apply RelCT.assoc
  apply (VG.Proof.Rc2.Arm.Cbc.start_ct d).seq
  apply (VG.Proof.Rc2.Arm.Cbc.maybeLoop_ct d).seq
  apply RelCT.taint (A := taint) (Taint.ofRegs [.r2])
    (fun _ _ h => Taint.agree_ofRegs (fun r hr => h r (by have e := List.mem_singleton.mp hr; rw [e]; decide)))
  taint_decide

end VG.Proof.Rc2.Arm.Cbc

end

/-! # Verified RC2-CBC encryption and decryption -/

namespace VG.Proof.Rc2.Arm.Cbc

open VG VG.Arm VG.Impl.Rc2.Arm

theorem cbc_body_correct (d : Spec.Rc2.Direction) (s : State) (hs : (VG.Proof.Rc2.Arm.Cbc.contract d).pre s) :
    WP isa (Impl.Rc2.Arm.Cbc.cbc d) s (fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ (VG.Proof.Rc2.Arm.Cbc.contract d).post s s') := by
  obtain ⟨hrd, hwr, keyIv, keyData, keyBuf, ivData, ivBuf, dataBuf,
    _ivArgs, _dataArgs, _bufArgs, keyFit, ivFit, bufFit, _spFit, fit⟩ := hs
  have writes (i : Nat) (hi : i + 4 ≤ 512) : InRegions s.wr (State.addr (stackArg s 0) + BitVec.ofNat 64 i) 4 := by
    rw [hwr]
    exact ⟨⟨State.addr (stackArg s 0), 512⟩, by simp, Offset.contains_base _ hi (by omega)⟩
  rw [Impl.Rc2.Arm.Cbc.cbc]
  apply WP.seq
  obtain ⟨s₀, run₀, buf₀, keep₀⟩ := loadScratch_ok s (by
    rw [hrd, hwr]
    exact ⟨⟨stackArgAddr s 0, 4⟩, by simp, Region.contains_self _ _⟩)
  refine WP.of_runBlock ⟨s₀, run₀, ?_⟩
  have g₀ (r : Reg) (hr : r ≠ .r12) := keep₀.reg r (by simpa using hr)
  have writes₀ (i : Nat) (hi : i + 4 ≤ 512) :
      InRegions s₀.wr (State.addr (s₀.gpr .r12) + BitVec.ofNat 64 i) 4 := by
    rw [keep₀.wr, buf₀]; exact writes i hi
  apply WP.seq
  rw [WP.block_append_iff]
  obtain ⟨s₁, run₁, keep₁⟩ := VG.Proof.Rc2.Arm.Cbc.save_ok s₀ (by rw [buf₀]; exact bufFit)
    (writes₀ 264 (by decide)) (writes₀ 268 (by decide)) (writes₀ 272 (by decide))
    (writes₀ 276 (by decide)) (writes₀ 280 (by decide))
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, iv₂, count₂, data₂, buf₂, flag₂, keep₂⟩ := VG.Proof.Rc2.Arm.Cbc.setup_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have g₁ (r : Reg) : s₁.gpr r = s₀.gpr r := keep₁.reg r (by simp)
  rw [g₁, g₀ .r1 (by decide)] at iv₂
  rw [g₁, g₀ .r3 (by decide)] at count₂ flag₂
  rw [g₁, g₀ .r2 (by decide)] at data₂
  rw [g₁, buf₀] at buf₂
  have key₂ := (keep₂.reg .r0 (by decide)).trans ((g₁ .r0).trans (g₀ .r0 (by decide)))
  have rd₂ := keep₂.rd.trans (keep₁.rd.trans keep₀.rd)
  have wr₂ := keep₂.wr.trans (keep₁.wr.trans keep₀.wr)
  have mem₂ : s₂.mem = VG.Proof.Rc2.Arm.Cbc.savedMem s₀ := keep₂.mem.trans keep₁.mem
  have scratchFrame : Frame [⟨State.addr (stackArg s 0), 512⟩] s.mem s₂.mem := by
    rw [mem₂, ← keep₀.mem, ← buf₀]; exact VG.Proof.Rc2.Arm.Cbc.savedMem_frame s₀
  have initialKey := scheduleAt_frame scratchFrame (State.addr (s.gpr .r0)) (by simpa using keyBuf)
  have initialIv := blockAt_frame scratchFrame (State.addr (s.gpr .r1)) (by simpa using ivBuf)
  have initialData := blocksAt_frame scratchFrame (State.addr (s.gpr .r2)) (s.gpr .r3).toNat (by simpa using dataBuf)
  have hp₂ : VG.Proof.Rc2.Arm.Cbc.StepPre s₂ (s.gpr .r3).toNat := by
    constructor
    · rw [key₂]; exact keyFit
    · rw [iv₂]; exact ivFit
    · rw [data₂]; exact fit
    · rw [buf₂]; exact bufFit
    · simp only [Covers, VG.Proof.Rc2.Arm.Cbc.keyR, VG.Proof.Rc2.Arm.Cbc.ivR, VG.Proof.Rc2.Arm.Cbc.dataR, VG.Proof.Rc2.Arm.Cbc.bufR, key₂, iv₂, data₂, buf₂, rd₂, wr₂, hrd, hwr]
      intro a n ⟨r, hr, hc⟩
      exact ⟨r, by simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; grind, hc⟩
    · simp only [Covers, VG.Proof.Rc2.Arm.Cbc.ivR, VG.Proof.Rc2.Arm.Cbc.dataR, VG.Proof.Rc2.Arm.Cbc.bufR, iv₂, data₂, buf₂, wr₂, hwr]
      intro a n ⟨r, hr, hc⟩
      exact ⟨r, by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; grind, hc⟩
    · simpa only [VG.Proof.Rc2.Arm.Cbc.keyR, VG.Proof.Rc2.Arm.Cbc.ivR, key₂, iv₂] using keyIv
    · simpa only [VG.Proof.Rc2.Arm.Cbc.keyR, VG.Proof.Rc2.Arm.Cbc.dataR, key₂, data₂] using keyData
    · simpa only [VG.Proof.Rc2.Arm.Cbc.keyR, VG.Proof.Rc2.Arm.Cbc.bufR, key₂, buf₂] using keyBuf
    · simpa only [VG.Proof.Rc2.Arm.Cbc.ivR, VG.Proof.Rc2.Arm.Cbc.dataR, iv₂, data₂] using ivData
    · simpa only [VG.Proof.Rc2.Arm.Cbc.ivR, VG.Proof.Rc2.Arm.Cbc.bufR, iv₂, buf₂] using ivBuf
    · simpa only [VG.Proof.Rc2.Arm.Cbc.dataR, VG.Proof.Rc2.Arm.Cbc.bufR, data₂, buf₂] using dataBuf
  apply WP.seq
  apply WP.mono (VG.Proof.Rc2.Arm.Cbc.maybeLoop_ok d s₂ (s.gpr .r3).toNat (by omega) hp₂
    (by simpa using count₂) (by rw [count₂]; exact flag₂))
  intro s₃ h₃
  have rd₃ := h₃.rd.trans rd₂
  have wr₃ := h₃.wr.trans wr₂
  have buf₃ := (h₃.reg .r2 (by decide) (by decide) (by decide)).trans buf₂
  have reads (i : Nat) (hi : i + 4 ≤ 512) :
      InRegions (s₃.rd ++ s₃.wr) (State.addr (s₃.gpr .r2) + BitVec.ofNat 64 i) 4 := by
    rw [rd₃, wr₃, buf₃]
    obtain ⟨r, hr, hc⟩ := writes i hi
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have v0 : s₃.mem.readW (State.addr (s₃.gpr .r2) + BitVec.ofNat 64 264) 32 = s.gpr .r4 := by
    have h := h₃.scratchRead hp₂ 264 (by decide) (by decide)
    rw [buf₂, mem₂, ← buf₀, VG.Proof.Rc2.Arm.Cbc.savedMem_r4, g₀ .r4 (by decide)] at h
    rw [buf₀] at h
    rw [buf₃]; exact h
  have v1 : s₃.mem.readW (State.addr (s₃.gpr .r2) + BitVec.ofNat 64 268) 32 = s.gpr .r5 := by
    have h := h₃.scratchRead hp₂ 268 (by decide) (by decide)
    rw [buf₂, mem₂, ← buf₀, VG.Proof.Rc2.Arm.Cbc.savedMem_r5, g₀ .r5 (by decide)] at h
    rw [buf₀] at h
    rw [buf₃]; exact h
  have v2 : s₃.mem.readW (State.addr (s₃.gpr .r2) + BitVec.ofNat 64 272) 32 = s.gpr .r6 := by
    have h := h₃.scratchRead hp₂ 272 (by decide) (by decide)
    rw [buf₂, mem₂, ← buf₀, VG.Proof.Rc2.Arm.Cbc.savedMem_r6, g₀ .r6 (by decide)] at h
    rw [buf₀] at h
    rw [buf₃]; exact h
  have v3 : s₃.mem.readW (State.addr (s₃.gpr .r2) + BitVec.ofNat 64 276) 32 = s.gpr .r7 := by
    have h := h₃.scratchRead hp₂ 276 (by decide) (by decide)
    rw [buf₂, mem₂, ← buf₀, VG.Proof.Rc2.Arm.Cbc.savedMem_r7, g₀ .r7 (by decide)] at h
    rw [buf₀] at h
    rw [buf₃]; exact h
  have v4 : s₃.mem.readW (State.addr (s₃.gpr .r2) + BitVec.ofNat 64 280) 32 = s.gpr .lr := by
    have h := h₃.scratchRead hp₂ 280 (by decide) (by decide)
    rw [buf₂, mem₂, ← buf₀, VG.Proof.Rc2.Arm.Cbc.savedMem_lr, g₀ .lr (by decide)] at h
    rw [buf₀] at h
    rw [buf₃]; exact h
  obtain ⟨s₄, run₄, saved₄, keep₄⟩ := VG.Proof.Rc2.Arm.Cbc.restore_ok s₃ s.gpr (by rw [buf₃]; exact bufFit)
    (reads 264 (by decide)) v0    (reads 268 (by decide)) v1    (reads 272 (by decide)) v2    (reads 276 (by decide)) v3    (reads 280 (by decide)) v4
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  constructor
  · intro r hr
    by_cases hs : r ∈ VG.Proof.Rc2.Arm.Cbc.callerSaved
    · exact saved₄ r hs
    · have kept : ∀ r ∈ preserved, r ∉ VG.Proof.Rc2.Arm.Cbc.callerSaved →
          r ∈ VG.Proof.Rc2.Arm.Cbc.savedAcrossCall ∧ r ≠ .r5 ∧ r ∉ [.r4, .r5, .r1, .r2] ∧ r ≠ .r12 := by decide
      obtain ⟨hc, hn, ht, h12⟩ := kept r hr hs
      rw [keep₄.reg r hs, h₃.callee r hc hn, keep₂.reg r ht, g₁ r]
      exact g₀ r h12
  · have out := h₃.data
    have iv := h₃.iv
    rw [key₂, iv₂, data₂, initialKey, initialIv, initialData] at out iv
    constructor
    · rw [keep₄.mem]; exact out
    · rw [keep₄.mem]; exact iv

def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | _ => 0
  sp := 0x6000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x6001 then 0x40 else 0
  rd := [⟨0x1000, 128⟩, ⟨0x6000, 4⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0x4000, 512⟩]

theorem encrypt_correct (s : State) (hs : (VG.Proof.Rc2.Arm.Cbc.contract .encrypt).pre s) :
    ∃ t s', Exec isa Impl.Rc2.Arm.Cbc.encrypt s t s' ∧ abiPreserved s s' ∧
      (VG.Proof.Rc2.Arm.Cbc.contract .encrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := VG.Proof.Rc2.Arm.Cbc.cbc_body_correct .encrypt s hs
  change Exec isa Impl.Rc2.Arm.Cbc.encrypt s t s' at he
  exact ⟨t, s', he, ⟨ha, VG.Arm.Exec.sp he⟩, hp⟩

theorem decrypt_correct (s : State) (hs : (VG.Proof.Rc2.Arm.Cbc.contract .decrypt).pre s) :
    ∃ t s', Exec isa Impl.Rc2.Arm.Cbc.decrypt s t s' ∧ abiPreserved s s' ∧
      (VG.Proof.Rc2.Arm.Cbc.contract .decrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := VG.Proof.Rc2.Arm.Cbc.cbc_body_correct .decrypt s hs
  change Exec isa Impl.Rc2.Arm.Cbc.decrypt s t s' at he
  exact ⟨t, s', he, ⟨ha, VG.Arm.Exec.sp he⟩, hp⟩

theorem encrypt_verified : Verified target Impl.Rc2.Arm.Cbc.encrypt (Spec.Rc2.cbcEncryptContract abi 0) := by
  refine Verified.of_correct VG.Proof.Rc2.Arm.Cbc.encrypt_correct (VG.Proof.Rc2.Arm.Cbc.cbc_constantTime .encrypt) ?_
  sig_implies [Spec.Rc2.cbcEncryptContract, Spec.Rc2.cbcContract, Spec.Rc2.cbcSig, abi, argRegs,
    Arm.reduceClassify, Arm.Loc.val, State.addr, VG.Proof.Rc2.Arm.Cbc.contract]
    [satState, stackArg, stackArgAddr, Mem.readW, Mem.read] using VG.Proof.Rc2.Arm.Cbc.satState

theorem decrypt_verified : Verified target Impl.Rc2.Arm.Cbc.decrypt (Spec.Rc2.cbcDecryptContract abi 0) := by
  refine Verified.of_correct VG.Proof.Rc2.Arm.Cbc.decrypt_correct (VG.Proof.Rc2.Arm.Cbc.cbc_constantTime .decrypt) ?_
  sig_implies [Spec.Rc2.cbcDecryptContract, Spec.Rc2.cbcContract, Spec.Rc2.cbcSig, abi, argRegs,
    Arm.reduceClassify, Arm.Loc.val, State.addr, VG.Proof.Rc2.Arm.Cbc.contract]
    [satState, stackArg, stackArgAddr, Mem.readW, Mem.read] using VG.Proof.Rc2.Arm.Cbc.satState

end VG.Proof.Rc2.Arm.Cbc

end
