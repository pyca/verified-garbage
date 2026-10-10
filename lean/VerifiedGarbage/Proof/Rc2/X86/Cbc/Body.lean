import VerifiedGarbage.Proof.Rc2.X86.KeyLoop
import VerifiedGarbage.Proof.Rc2.CbcMemory
import VerifiedGarbage.Proof.Rc2.X86.KeySteps
import VerifiedGarbage.Proof.Rc2.PairMem
import VerifiedGarbage.Proof.Rc2.X86.Block
import VerifiedGarbage.Impl.Rc2.X86.Cbc
import VerifiedGarbage.Proof.Rc2.X86.Cbc.CallFrame

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
    omega_arith
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
      a0, a1, mem₂] at post
    have stackFrame := callEntry_frame fit hrs
    change Frame [below (s.gpr .esp) 16] s.mem sE.mem at stackFrame
    refine ⟨?_, cs, rd, wr, frame, ?_⟩
    · intro r hr
      by_cases he : r = .ecx
      · subst r
        have memGpr : s₂.gpr .ecx = s'.gpr .ecx := gpr₂ .ecx (by decide) (by decide)
        rw [← memGpr, post.1]
        exact (State.callEntry_gpr _ (by decide)).trans (pushed_gpr rs s (by decide))
      · have fact : ∀ r ∈ kept, r ≠ .ecx → r ∈ calleeSaved := by decide
        exact cs r (fact r hr he)
    · rw [post.2, scheduleAt_frame stackFrame _ (by simpa using hp.stackKey.symm),
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
  · exact ⟨r, hr, by unfold Region.Contains at hc ⊢; omega_arith⟩
  · refine ⟨r, hr, ?_⟩
    unfold Region.Contains at hc ⊢
    rw [BitVec.add_sub_comm, BitVec.toNat_add]
    have bound := Nat.mod_le ((p - r.base).toNat + (BitVec.ofNat 64 4).toNat) (2 ^ 64)
    change ((p - r.base).toNat + 4) % 2 ^ 64 + 4 ≤ r.len
    change ((p - r.base).toNat + 4) % 2 ^ 64 ≤ (p - r.base).toNat + 4 at bound
    omega_arith

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
  rw [runBlock_cons, exec_load s lo src a (by omega_arith) rd0, runStep_some]
  have rd4' : InRegions ((s.setReg lo (s.mem.readW (addr32 (s.gpr src) + BitVec.ofNat 64 a) 32)).rd ++
      (s.setReg lo (s.mem.readW (addr32 (s.gpr src) + BitVec.ofNat 64 a) 32)).wr)
      (addr32 ((s.setReg lo (s.mem.readW (addr32 (s.gpr src) + BitVec.ofNat 64 a) 32)).gpr src) +
        BitVec.ofNat 64 (a + 4)) 4 := by
    simpa only [rd_setReg, wr_setReg, gpr_setReg_of_ne _ _ sep] using rd4
  rw [runBlock_cons, exec_load _ hi src (a + 4)
    (by rw [gpr_setReg_of_ne _ _ sep]; omega_arith) rd4', runStep_some, runBlock_nil]
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
  rw [runBlock_cons, exec_store s lo dst b (by omega_arith) wr0, runStep_some,
    runBlock_cons, exec_store {s with mem := s.mem.writeW (addr32 (s.gpr dst) + BitVec.ofNat 64 b) (s.gpr lo)} hi dst (b + 4) (by change (s.gpr dst).toNat + (b + 4) < 2 ^ 32; omega_arith) wr4,
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
  have ptr := keep₁.reg dst (by simpa only [List.mem_cons, List.not_mem_nil, or_false, not_or] using dstSep)
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
  rw [runBlock_cons, exec_xorMem s .eax iv 0 (by omega_arith) (by simpa only [BitVec.add_zero] using rd0), runStep_some]
  rw [runBlock_cons, exec_xorMem _ .edx iv 4
    (by simp only [gpr_setReg, gpr_arithFlags, ivSep.1, ite_false]; omega_arith)
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
  have ds : dst ≠ .eax ∧ dst ≠ .edx := by simpa only [temps, List.mem_cons, List.not_mem_nil, or_false, not_or] using dstSep
  have vs : iv ≠ .eax ∧ iv ≠ .edx := by simpa only [temps, List.mem_cons, List.not_mem_nil, or_false, not_or] using ivSep
  change WP isa (.block (([.mov .eax (.mem (memOp dst 0)), .mov .edx (.mem (memOp dst 4))] : List Instr) ++
    (([.alu .xor .eax (.mem (memOp iv 0)), .alu .xor .edx (.mem (memOp iv 4))] : List Instr) ++
      [.store (memOp dst 0) .eax, .store (memOp dst 4) .edx]))) s _
  rw [WP.block_append_iff]
  obtain ⟨s₁, run₁, lo₁, hi₁, keep₁⟩ := loadPair_ok s .eax .edx dst 0 (by decide) ds.1
    (by simpa using dstFit) (by simpa using readDst)
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have iv₁ := keep₁.reg iv ivSep
  rw [WP.block_append_iff]
  obtain ⟨s₂, run₂, lo₂, hi₂, keep₂⟩ := xorPair_ok s₁ iv vs
    (by rw [iv₁]; exact ivFit) (by rw [keep₁.rd, keep₁.wr, iv₁]; exact readIv)
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have keep : Keep temps s s₂ := keep₁.trans keep₂
  have ptr := keep.reg dst dstSep
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
  have a := regs .ebx (by decide)
  have b := regs .ecx (by decide)
  have c := regs .esi (by decide)
  have d := regs .ebp (by decide)
  have e := regs .esp (by decide)
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
    have sep : ∀ r ∈ kept, r ∉ [.eax, .edx] := by decide
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
  · have := hp.bufFit; omega_arith
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
  hp.reads _ _ ⟨bufR s, by simp, Offset.contains_base _ hi (by omega_arith)⟩

theorem StepPre.writeBuf {s : State} (hp : StepPre s) (i : Nat) (hi : i + 8 ≤ 512) :
    InRegions s.wr (addr32 (s.gpr .ebp) + BitVec.ofNat 64 i) 8 :=
  hp.writes _ _ ⟨bufR s, by simp, Offset.contains_base _ hi (by omega_arith)⟩

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
  have k : ∀ r ∈ kept, r ∉ [.eax, .edx] := by decide
  have c : ∀ r ∈ calleeSaved, r ∉ [.eax, .edx] := by decide
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
    (Spec.Rc2.cbcStep (Spec.Rc2.scheduleAt s.mem (addr32 (s.gpr .ebx))) d
      (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .ecx))) (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .esi)))).1
  iv : Spec.Rc2.blockAt s'.mem (addr32 (s.gpr .ecx)) =
    (Spec.Rc2.cbcStep (Spec.Rc2.scheduleAt s.mem (addr32 (s.gpr .ebx))) d
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
  have sep : (stashR s).Disjoint ⟨addr32 (s.gpr .ebp), 256⟩ := by
    have h := Offset.disjoint (addr32 (s.gpr .ebp)) (d := 256) (n := 8) (e := 0) (k := 256)
      (by omega_arith) (by decide) (by decide)
    simpa using h
  simpa only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro ((hp.dataBuf.sub_right (stash_sub s)).symm) (And.intro sep
      (hp.stackBuf.sub_right (stash_sub s)).symm)

theorem decryptStep_ok (s : State) (hp : StepPre s) :
    WP isa (Impl.Rc2.X86.Cbc.step .decrypt) s (StepPost .decrypt s) := by
  rw [Impl.Rc2.X86.Cbc.step]
  apply WP.seq
  apply WP.mono (copy64_ok s .esi .ebp 0 256 (by decide) (by decide)
    (by simpa using hp.dataFit) (by have := hp.bufFit; omega_arith) (by simpa using hp.readData) (hp.writeBuf 256 (by decide)))
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
    exact ⟨⟨addr32 (s.gpr .ebp), 264⟩, by simp [stepWrites], Offset.sub_base _ (by decide)⟩
  have hp₁ := pin₁.pre hp
  have key₁ := pin₁.schedule hp
  have data₁ := blockAt_frame frame₁ (addr32 (s.gpr .esi)) (by simpa using hp.dataBuf.sub_right (stash_sub s))
  have iv₁ := blockAt_frame frame₁ (addr32 (s.gpr .ecx)) (by simpa using hp.ivBuf.sub_right (stash_sub s))
  have stash₁ : Spec.Rc2.blockAt s₁.mem (stashR s).base = Spec.Rc2.blockAt s.mem (addr32 (s.gpr .esi)) := by
    rw [keep₁.mem]; exact blockAt_copy _ _ _
  apply WP.seq
  apply WP.mono (call_ok .decrypt s₁ hp₁.call)
  intro s₂ h₂
  have pin₂ := pin₁.trans (Pinned.of_call h₂)
  have hp₂ := pin₂.pre hp
  have output₂ := h₂.output
  rw [pin₁.reg .esi (by decide), pin₁.reg .ebx (by decide), key₁, data₁] at output₂
  have iv₂ := h₂.iv hp₁
  rw [pin₁.reg .ecx (by decide), iv₁] at iv₂
  have stash₂ := call_stash hp₁ h₂
  simp only [pin₁.reg .ebp (by decide)] at stash₂
  have stash₂' := stash₂.trans stash₁
  change WP isa (.block (Impl.Rc2.X86.Cbc.xor64 .esi .ecx ++
    Impl.Rc2.X86.Cbc.copy64 .ebp .ecx 256 0)) s₂ _
  rw [WP.block_append_iff]
  apply WP.mono (xor64_ok s₂ .esi .ecx (by decide) (by decide)
    (by simpa using hp₂.dataFit) hp₂.ivFit hp₂.readData hp₂.readIv hp₂.writeData)
  intro s₃ keep₃
  have frame₃ : Frame [dataR s₂] s₂.mem s₃.mem := by
    rw [keep₃.mem]; exact frame_store64 _ _ _
  have pin₃ := Pinned.of_keep keep₃ ((frame_store64 _ _ _).mono (by simp [stepWrites]))
  have pin₀₃ := pin₂.trans pin₃
  have hp₃ := pin₀₃.pre hp
  have data₃ : Spec.Rc2.blockAt s₃.mem (addr32 (s.gpr .esi)) =
      Spec.Rc2.xorBlock (Spec.Rc2.decryptBlock (Spec.Rc2.scheduleAt s.mem (addr32 (s.gpr .ebx)))
        (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .esi)))) (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .ecx))) := by
    have h : Spec.Rc2.blockAt s₃.mem (addr32 (s₂.gpr .esi)) =
        Spec.Rc2.xorBlock (Spec.Rc2.blockAt s₂.mem (addr32 (s₂.gpr .esi))) (Spec.Rc2.blockAt s₂.mem (addr32 (s₂.gpr .ecx))) := by
      rw [keep₃.mem]; exact blockAt_xor _ _ _
    rw [pin₂.reg .esi (by decide), pin₂.reg .ecx (by decide), output₂, iv₂] at h
    exact h
  have stash₃ := blockAt_frame frame₃ (stashR s₂).base
    (by simpa using (hp₂.dataBuf.sub_right (stash_sub s₂)).symm)
  simp only [pin₂.reg .ebp (by decide)] at stash₃
  have stash₃' := stash₃.trans stash₂'
  apply WP.mono (copy64_ok s₃ .ebp .ecx 256 0 (by decide) (by decide)
    (by have := hp₃.bufFit; omega_arith) (by simpa using hp₃.ivFit) (hp₃.readBuf 256 (by decide)) (by simpa using hp₃.writeIv))
  intro s₄ keep₄
  simp only [BitVec.add_zero] at keep₄
  have frame₄ : Frame [ivR s₃] s₃.mem s₄.mem := by
    rw [keep₄.mem]; exact frame_store64 _ _ _
  have pin₄ := Pinned.of_keep keep₄ ((frame_store64 _ _ _).mono (by simp [stepWrites]))
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
  have ptrAddr : addr32 (s'.gpr .esi) = addr32 (s.gpr .esi) + BitVec.ofNat 64 (8 * i) := by
    rw [ptr]; exact addr_add startFit
  have fit : (s'.gpr .esi).toNat + 8 * m ≤ 2 ^ 32 := by
    rw [ptr, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * i) (by omega_arith),
      Nat.mod_eq_of_lt startFit]
    have := hp.dataFit
    omega_arith
  have sub : Region.Sub (dataR s' m) (dataR s n) := by
    change Region.Sub ⟨addr32 (s'.gpr .esi), 8 * m⟩ ⟨addr32 (s.gpr .esi), 8 * n⟩
    rw [ptrAddr]
    exact Offset.sub_base _ (by omega_arith)
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
      · exact ⟨dataR s n, by simp, 8 * i, ptrAddr, by change 8 * i + 8 * m ≤ 8 * n; omega_arith⟩
      · exact ⟨bufR s, by simp, 0, by simp [buf], by simp⟩
    rw [rd, wr]
    exact fun a k h => hp.reads a k (hc a k h)
  · have hc : Covers [ivR s', dataR s' m, bufR s'] [ivR s, dataR s n, bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨ivR s, by simp, 0, by simp [iv], by simp⟩
      · exact ⟨dataR s n, by simp, 8 * i, ptrAddr, by change 8 * i + 8 * m ≤ 8 * n; omega_arith⟩
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
  have pin₁ := Pinned.of_keep keep₁ ((frame_store64 _ _ _).mono (by simp [stepWrites]))
  have hp₁ := pin₁.pre hp
  have key₁ := pin₁.schedule hp
  have data₁ : Spec.Rc2.blockAt s₁.mem (addr32 (s.gpr .esi)) =
      Spec.Rc2.xorBlock (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .esi))) (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .ecx))) := by
    rw [keep₁.mem]; exact blockAt_xor _ _ _
  apply WP.seq
  apply WP.mono (call_ok .encrypt s₁ hp₁.call)
  intro s₂ h₂
  have pin₂ := pin₁.trans (Pinned.of_call h₂)
  have hp₂ := pin₂.pre hp
  have output₂ := h₂.output
  rw [pin₁.reg .esi (by decide), pin₁.reg .ebx (by decide), key₁, data₁] at output₂
  apply WP.mono (copy64_ok s₂ .esi .ecx 0 0 (by decide) (by decide)
    (by simpa using hp₂.dataFit) (by simpa using hp₂.ivFit) (by simpa using hp₂.readData) (by simpa using hp₂.writeIv))
  intro s₃ keep₃
  simp only [BitVec.add_zero] at keep₃
  have frame₃ : Frame [ivR s₂] s₂.mem s₃.mem := by
    rw [keep₃.mem]; exact frame_store64 _ _ _
  have pin₃ := Pinned.of_keep keep₃ ((frame_store64 _ _ _).mono (by simp [stepWrites]))
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
    (Spec.Rc2.cbcStep (Spec.Rc2.scheduleAt s.mem (addr32 (s.gpr .ebx))) d
      (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .ecx))) (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .esi)))).1
  iv : Spec.Rc2.blockAt s'.mem (addr32 (s.gpr .ecx)) =
    (Spec.Rc2.cbcStep (Spec.Rc2.scheduleAt s.mem (addr32 (s.gpr .ebx))) d
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
  have count' : s₁.gpr .edi - 1 = BitVec.ofNat 32 (n - 1) := by
    rw [h₁.reg .edi (by decide), count]
    exact Offset.ofNat_sub_ofNat hn
  refine ⟨by rw [ptr₂, h₁.reg .esi (by decide)], count₂.trans count', ?_, ?_, ?_,
    keep₂.rd.trans h₁.rd, keep₂.wr.trans h₁.wr, ?_, ?_, ?_⟩
  · rw [zeroCount, flag₂, count']
    have eqZero := counter_eq (n - 1) 0 (by omega_arith) (by decide)
    simp only [BitVec.sub_zero] at eqZero
    change some (BitVec.ofNat 32 (n - 1) == 0#32) = _
    rw [eqZero]
    have he : n - 1 = 0 ↔ n = 1 := by omega_arith
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
  hp.slice (i := 1) (by omega_arith) (by have := hp.dataFit; omega_arith) h.rd h.wr
    (h.reg .ebx (by decide) (by decide) (by decide))
    (h.reg .ecx (by decide) (by decide) (by decide))
    (h.reg .ebp (by decide) (by decide) (by decide))
    (h.reg .esp (by decide) (by decide) (by decide))
    h.ptr

end VG.Proof.Rc2.X86.Cbc
