import VerifiedGarbage.Proof.Rc2.X86.Key
import VerifiedGarbage.Proof.Rc2.Stream
import VerifiedGarbage.Proof.Rc2.X86.Block
import VerifiedGarbage.Impl.Rc2.X86.Cbc
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Rc2.Contract
import VerifiedGarbage.Proof.Rc2.X86.Key
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86.RelCT

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.X86.Cbc.CallFrame`. -/
section

/-! A framed call also exposes unchanged non-result registers of its witness. -/

namespace VG.Proof.Rc2.X86.Cbc

open VG VG.X86

theorem callWithGpr {rs : List Reg} {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsp : NoSp c) (hne : rs ≠ []) (hrs : Reg.esp ∉ rs) {s : VG.X86.State}
    (hd : 4 * rs.length + stackUse c + 4 ≤ (s.gpr .esp).toNat) {rd wr : List Region}
    (hk : VG.X86.CallPre k rs rd wr s) {Q : VG.X86.State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame (wr ++ [below (s.gpr .esp) (4 * rs.length + stackUse c + 4)]) s.mem s'.mem →
      (∃ s₂ : VG.X86.State, s₂.mem = s'.mem ∧ (∀ r, r ≠ .esp → r ≠ .eax → s₂.gpr r = s'.gpr r) ∧ k.post ((pushed rs s).callEntry.withRegions rd wr) s₂) → Q s') :
    WP isa (.frame (.push rs) (.call n c) (.pop .eax rs.length)) s Q := by
  have hn : 4 * rs.length ≤ (s.gpr .esp).toNat := by omega
  have e : ((pushed rs s).gpr .esp).toNat = (s.gpr .esp).toNat - 4 * rs.length := by
    rw [pushed_esp, VG.X86.sub_toNat hn]
  refine WP.frame hne hrs (by decide) hn (fun i hi => hsp i hi) ?_
  refine WP.call hv hsp (by rw [e]; omega) hk.pre (by rw [pushed_rd, pushed_wr]; exact hk.cov)
    (by rw [pushed_wr]; exact hk.covw) fun s₂ rd₂ wr₂ cs₂ f₂ _ ⟨s₃, m₃, g₃, post₃⟩ => ?_
  refine hQ _ (by rw [popped_rd, rd₂, pushed_rd]) (by rw [popped_wr, wr₂, pushed_wr]; rfl) (fun r hr => ?_) ?_
    ⟨s₃, by rw [m₃, popped_mem], fun r hsp hr => (g₃ r hsp).trans (popped_gpr _ _ _ hsp hr).symm, post₃⟩
  · by_cases h : r = .esp
    · subst h
      rw [popped_esp, cs₂ .esp hr, pushed_esp]; exact BitVec.sub_add_cancel _ _
    · have hne' : r ≠ .eax := by
        rintro rfl; simp [calleeSaved] at hr
      rw [popped_gpr _ _ _ h hne', cs₂ r hr, pushed_gpr _ _ h]
  · rw [popped_mem]
    refine ((pushed_frame hrs hn).sub fun r hr => ?_).trans (f₂.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), below_sub (by omega) hd⟩
    · rcases List.mem_append.mp hr with hr | hr
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · simp only [List.mem_singleton] at hr; subst hr
        refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
        rw [pushed_esp]
        exact below_inner (by omega) hd

end VG.Proof.Rc2.X86.Cbc

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.X86.Cbc.Body`. -/
section

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
  reg : ∀ r ∈ VG.Proof.Rc2.X86.Cbc.kept, s'.gpr r = s.gpr r
  callee : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame [⟨addr32 (s.gpr .esi), 8⟩, ⟨addr32 (s.gpr .ebp), 256⟩, below (s.gpr .esp) 16] s.mem s'.mem
  output : Spec.Rc2.blockAt s'.mem (addr32 (s.gpr .esi)) =
    cipher d (Spec.Rc2.scheduleAt s.mem (addr32 (s.gpr .ebx))) (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .esi)))

theorem call_ok (d : Spec.Rc2.Direction) (s : State) (hp : VG.Proof.Rc2.X86.Cbc.CallPre s) :
    WP isa (Impl.Rc2.X86.Cbc.blockCall d) s (VG.Proof.Rc2.X86.Cbc.CallPost d s) := by
  rw [VG.Proof.Rc2.X86.Cbc.blockCall_eq]
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
  refine VG.Proof.Rc2.X86.Cbc.callWithGpr (k := blockContract d) (block_correct d) (VG.Proof.Rc2.X86.Cbc.block_nosp d) (by decide) hrs
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
    omega
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
      · have fact : ∀ r ∈ VG.Proof.Rc2.X86.Cbc.kept, r ≠ .ecx → r ∈ calleeSaved := by decide
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
  · exact ⟨r, hr, by unfold Region.Contains at hc ⊢; omega⟩
  · refine ⟨r, hr, ?_⟩
    unfold Region.Contains at hc ⊢
    rw [BitVec.add_sub_comm, BitVec.toNat_add]
    have bound := Nat.mod_le ((p - r.base).toNat + (BitVec.ofNat 64 4).toNat) (2 ^ 64)
    change ((p - r.base).toNat + 4) % 2 ^ 64 + 4 ≤ r.len
    change ((p - r.base).toNat + 4) % 2 ^ 64 ≤ (p - r.base).toNat + 4 at bound
    omega

theorem loadPair_ok (s : State) (lo hi src : Reg) (a : Nat)
    (different : lo ≠ hi) (sep : src ≠ lo)
    (fit : (s.gpr src).toNat + a + 8 ≤ 2 ^ 32)
    (readable : InRegions (s.rd ++ s.wr) (addr32 (s.gpr src) + BitVec.ofNat 64 a) 8) :
    ∃ s', runBlock isa [.mov lo (.mem (memOp src a)), .mov hi (.mem (memOp src (a + 4)))] s = some s' ∧
      s'.gpr lo = s.mem.readW (addr32 (s.gpr src) + BitVec.ofNat 64 a) 32 ∧
      s'.gpr hi = s.mem.readW (addr32 (s.gpr src) + BitVec.ofNat 64 (a + 4)) 32 ∧
      Keep [lo, hi] s s' := by
  obtain ⟨rd0, rd4⟩ := VG.Proof.Rc2.X86.Cbc.halves readable
  rw [BitVec.add_assoc, ← BitVec.ofNat_add] at rd4
  rw [runBlock_cons, exec_load s lo src a (by omega) rd0, runStep_some]
  have rd4' : InRegions ((s.setReg lo (s.mem.readW (addr32 (s.gpr src) + BitVec.ofNat 64 a) 32)).rd ++
      (s.setReg lo (s.mem.readW (addr32 (s.gpr src) + BitVec.ofNat 64 a) 32)).wr)
      (addr32 ((s.setReg lo (s.mem.readW (addr32 (s.gpr src) + BitVec.ofNat 64 a) 32)).gpr src) +
        BitVec.ofNat 64 (a + 4)) 4 := by
    simpa only [rd_setReg, wr_setReg, gpr_setReg_of_ne _ _ sep] using rd4
  rw [runBlock_cons, exec_load _ hi src (a + 4)
    (by rw [gpr_setReg_of_ne _ _ sep]; omega) rd4', runStep_some, runBlock_nil]
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
  obtain ⟨wr0, wr4⟩ := VG.Proof.Rc2.X86.Cbc.halves writable
  rw [BitVec.add_assoc, ← BitVec.ofNat_add] at wr4
  rw [runBlock_cons, exec_store s lo dst b (by omega) wr0, runStep_some,
    runBlock_cons, exec_store {s with mem := s.mem.writeW (addr32 (s.gpr dst) + BitVec.ofNat 64 b) (s.gpr lo)} hi dst (b + 4) (by change (s.gpr dst).toNat + (b + 4) < 2 ^ 32; omega) wr4,
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
      Keep VG.Proof.Rc2.X86.Cbc.temps {s with
        mem := s.mem.writeW (addr32 (s.gpr dst) + BitVec.ofNat 64 b)
          (s.mem.readW (addr32 (s.gpr src) + BitVec.ofNat 64 a) 64)} s') := by
  change WP isa (.block (([.mov .eax (.mem (memOp src a)), .mov .edx (.mem (memOp src (a + 4)))] : List Instr) ++
    [.store (memOp dst b) .eax, .store (memOp dst (b + 4)) .edx])) s _
  rw [WP.block_append_iff]
  obtain ⟨s₁, run₁, lo₁, hi₁, keep₁⟩ := VG.Proof.Rc2.X86.Cbc.loadPair_ok s .eax .edx src a (by decide) srcSep srcFit readable
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have ptr := keep₁.reg dst (by simpa only [List.mem_cons, List.not_mem_nil, or_false, not_or] using dstSep)
  obtain ⟨s₂, run₂, keep₂⟩ := VG.Proof.Rc2.X86.Cbc.storePair_ok s₁ .eax .edx dst b
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
      Keep VG.Proof.Rc2.X86.Cbc.temps s s' := by
  obtain ⟨rd0, rd4⟩ := VG.Proof.Rc2.X86.Cbc.halves rd
  rw [runBlock_cons, VG.Proof.Rc2.X86.Cbc.exec_xorMem s .eax iv 0 (by omega) (by simpa only [BitVec.add_zero] using rd0), runStep_some]
  rw [runBlock_cons, VG.Proof.Rc2.X86.Cbc.exec_xorMem _ .edx iv 4
    (by simp only [gpr_setReg, gpr_arithFlags, ivSep.1, ite_false]; omega)
    (by simpa only [rd_setReg, wr_setReg, rd_arithFlags, wr_arithFlags, gpr_setReg, gpr_arithFlags, ivSep.1, ite_false] using rd4),
    runStep_some, runBlock_nil]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true, BitVec.add_zero]
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true, ivSep.1, mem_setReg, mem_arithFlags]
  · refine ⟨?_, rfl, rfl, rfl⟩
    intro r hr
    simp only [VG.Proof.Rc2.X86.Cbc.temps, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, gpr_arithFlags, hr.1, hr.2, ite_false]

theorem xor64_ok (s : State) (dst iv : Reg)
    (dstSep : dst ∉ VG.Proof.Rc2.X86.Cbc.temps) (ivSep : iv ∉ VG.Proof.Rc2.X86.Cbc.temps)
    (dstFit : (s.gpr dst).toNat + 8 ≤ 2 ^ 32) (ivFit : (s.gpr iv).toNat + 8 ≤ 2 ^ 32)
    (readDst : InRegions (s.rd ++ s.wr) (addr32 (s.gpr dst)) 8)
    (readIv : InRegions (s.rd ++ s.wr) (addr32 (s.gpr iv)) 8)
    (writable : InRegions s.wr (addr32 (s.gpr dst)) 8) :
    WP isa (.block (Impl.Rc2.X86.Cbc.xor64 dst iv)) s (fun s' =>
      Keep VG.Proof.Rc2.X86.Cbc.temps {s with mem := (s.mem.writeW (addr32 (s.gpr dst))
        (s.mem.readW (addr32 (s.gpr dst)) 64 ^^^ s.mem.readW (addr32 (s.gpr iv)) 64))} s') := by
  have ds : dst ≠ .eax ∧ dst ≠ .edx := by simpa only [VG.Proof.Rc2.X86.Cbc.temps, List.mem_cons, List.not_mem_nil, or_false, not_or] using dstSep
  have vs : iv ≠ .eax ∧ iv ≠ .edx := by simpa only [VG.Proof.Rc2.X86.Cbc.temps, List.mem_cons, List.not_mem_nil, or_false, not_or] using ivSep
  change WP isa (.block (([.mov .eax (.mem (memOp dst 0)), .mov .edx (.mem (memOp dst 4))] : List Instr) ++
    (([.alu .xor .eax (.mem (memOp iv 0)), .alu .xor .edx (.mem (memOp iv 4))] : List Instr) ++
      [.store (memOp dst 0) .eax, .store (memOp dst 4) .edx]))) s _
  rw [WP.block_append_iff]
  obtain ⟨s₁, run₁, lo₁, hi₁, keep₁⟩ := VG.Proof.Rc2.X86.Cbc.loadPair_ok s .eax .edx dst 0 (by decide) ds.1
    (by simpa using dstFit) (by simpa using readDst)
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have iv₁ := keep₁.reg iv ivSep
  rw [WP.block_append_iff]
  obtain ⟨s₂, run₂, lo₂, hi₂, keep₂⟩ := VG.Proof.Rc2.X86.Cbc.xorPair_ok s₁ iv vs
    (by rw [iv₁]; exact ivFit) (by rw [keep₁.rd, keep₁.wr, iv₁]; exact readIv)
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have keep : Keep VG.Proof.Rc2.X86.Cbc.temps s s₂ := keep₁.trans keep₂
  have ptr := keep.reg dst dstSep
  obtain ⟨s₃, run₃, keep₃⟩ := VG.Proof.Rc2.X86.Cbc.storePair_ok s₂ .eax .edx dst 0
    (by rw [ptr]; simpa using dstFit) (by rw [keep.wr, ptr]; simpa using writable)
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  refine ⟨fun r hr => (keep₃.reg r (by simp)).trans (keep.reg r hr), ?_, keep₃.rd.trans keep.rd, keep₃.wr.trans keep.wr⟩
  rw [keep₃.mem, keep.mem, ptr, BitVec.add_zero, hi₂, lo₂, hi₁, lo₁, keep₁.mem, iv₁]
  simp only [Nat.zero_add, BitVec.add_zero]
  rw [pair_xor, ← read64_pair, ← read64_pair]

def zeroCount (s : State) : Option Bool := s.zf

theorem eval_zeroCount (s : State) : eval .e s = VG.Proof.Rc2.X86.Cbc.zeroCount s := rfl

theorem eval_nonzeroCount (s : State) : eval .ne s = (VG.Proof.Rc2.X86.Cbc.zeroCount s).map (! ·) := rfl

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
  reads : Covers [VG.Proof.Rc2.X86.Cbc.keyR s, VG.Proof.Rc2.X86.Cbc.ivR s, VG.Proof.Rc2.X86.Cbc.dataR s n, VG.Proof.Rc2.X86.Cbc.bufR s] (s.rd ++ s.wr)
  writes : Covers [VG.Proof.Rc2.X86.Cbc.ivR s, VG.Proof.Rc2.X86.Cbc.dataR s n, VG.Proof.Rc2.X86.Cbc.bufR s] s.wr
  keyIv : (VG.Proof.Rc2.X86.Cbc.keyR s).Disjoint (VG.Proof.Rc2.X86.Cbc.ivR s)
  keyData : (VG.Proof.Rc2.X86.Cbc.keyR s).Disjoint (VG.Proof.Rc2.X86.Cbc.dataR s n)
  keyBuf : (VG.Proof.Rc2.X86.Cbc.keyR s).Disjoint (VG.Proof.Rc2.X86.Cbc.bufR s)
  ivData : (VG.Proof.Rc2.X86.Cbc.ivR s).Disjoint (VG.Proof.Rc2.X86.Cbc.dataR s n)
  ivBuf : (VG.Proof.Rc2.X86.Cbc.ivR s).Disjoint (VG.Proof.Rc2.X86.Cbc.bufR s)
  dataBuf : (VG.Proof.Rc2.X86.Cbc.dataR s n).Disjoint (VG.Proof.Rc2.X86.Cbc.bufR s)

  stackLo : 16 ≤ (s.gpr .esp).toNat
  stackKey : (VG.Proof.Rc2.X86.Cbc.stackR s).Disjoint (VG.Proof.Rc2.X86.Cbc.keyR s)
  stackIv : (VG.Proof.Rc2.X86.Cbc.stackR s).Disjoint (VG.Proof.Rc2.X86.Cbc.ivR s)
  stackData : (VG.Proof.Rc2.X86.Cbc.stackR s).Disjoint (VG.Proof.Rc2.X86.Cbc.dataR s n)
  stackBuf : (VG.Proof.Rc2.X86.Cbc.stackR s).Disjoint (VG.Proof.Rc2.X86.Cbc.bufR s)

theorem StepPre.transport {s s' : State} {n : Nat} (hp : VG.Proof.Rc2.X86.Cbc.StepPre s n)
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) (regs : ∀ r ∈ VG.Proof.Rc2.X86.Cbc.kept, s'.gpr r = s.gpr r) : VG.Proof.Rc2.X86.Cbc.StepPre s' n := by
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
  · simpa only [VG.Proof.Rc2.X86.Cbc.keyR, VG.Proof.Rc2.X86.Cbc.ivR, VG.Proof.Rc2.X86.Cbc.dataR, VG.Proof.Rc2.X86.Cbc.bufR, rd, wr, a, b, c, d] using hp.reads
  · simpa only [VG.Proof.Rc2.X86.Cbc.keyR, VG.Proof.Rc2.X86.Cbc.ivR, VG.Proof.Rc2.X86.Cbc.dataR, VG.Proof.Rc2.X86.Cbc.bufR, rd, wr, a, b, c, d] using hp.writes
  · simpa only [VG.Proof.Rc2.X86.Cbc.keyR, VG.Proof.Rc2.X86.Cbc.ivR, VG.Proof.Rc2.X86.Cbc.dataR, VG.Proof.Rc2.X86.Cbc.bufR, rd, wr, a, b, c, d] using hp.keyIv
  · simpa only [VG.Proof.Rc2.X86.Cbc.keyR, VG.Proof.Rc2.X86.Cbc.ivR, VG.Proof.Rc2.X86.Cbc.dataR, VG.Proof.Rc2.X86.Cbc.bufR, rd, wr, a, b, c, d] using hp.keyData
  · simpa only [VG.Proof.Rc2.X86.Cbc.keyR, VG.Proof.Rc2.X86.Cbc.ivR, VG.Proof.Rc2.X86.Cbc.dataR, VG.Proof.Rc2.X86.Cbc.bufR, rd, wr, a, b, c, d] using hp.keyBuf
  · simpa only [VG.Proof.Rc2.X86.Cbc.keyR, VG.Proof.Rc2.X86.Cbc.ivR, VG.Proof.Rc2.X86.Cbc.dataR, VG.Proof.Rc2.X86.Cbc.bufR, rd, wr, a, b, c, d] using hp.ivData
  · simpa only [VG.Proof.Rc2.X86.Cbc.keyR, VG.Proof.Rc2.X86.Cbc.ivR, VG.Proof.Rc2.X86.Cbc.dataR, VG.Proof.Rc2.X86.Cbc.bufR, rd, wr, a, b, c, d] using hp.ivBuf
  · simpa only [VG.Proof.Rc2.X86.Cbc.keyR, VG.Proof.Rc2.X86.Cbc.ivR, VG.Proof.Rc2.X86.Cbc.dataR, VG.Proof.Rc2.X86.Cbc.bufR, rd, wr, a, b, c, d] using hp.dataBuf

  · simpa only [e] using hp.stackLo
  · simpa only [VG.Proof.Rc2.X86.Cbc.stackR, VG.Proof.Rc2.X86.Cbc.keyR, VG.Proof.Rc2.X86.Cbc.ivR, VG.Proof.Rc2.X86.Cbc.dataR, VG.Proof.Rc2.X86.Cbc.bufR, a, b, c, d, e] using hp.stackKey
  · simpa only [VG.Proof.Rc2.X86.Cbc.stackR, VG.Proof.Rc2.X86.Cbc.keyR, VG.Proof.Rc2.X86.Cbc.ivR, VG.Proof.Rc2.X86.Cbc.dataR, VG.Proof.Rc2.X86.Cbc.bufR, a, b, c, d, e] using hp.stackIv
  · simpa only [VG.Proof.Rc2.X86.Cbc.stackR, VG.Proof.Rc2.X86.Cbc.keyR, VG.Proof.Rc2.X86.Cbc.ivR, VG.Proof.Rc2.X86.Cbc.dataR, VG.Proof.Rc2.X86.Cbc.bufR, a, b, c, d, e] using hp.stackData
  · simpa only [VG.Proof.Rc2.X86.Cbc.stackR, VG.Proof.Rc2.X86.Cbc.keyR, VG.Proof.Rc2.X86.Cbc.ivR, VG.Proof.Rc2.X86.Cbc.dataR, VG.Proof.Rc2.X86.Cbc.bufR, a, b, c, d, e] using hp.stackBuf

theorem StepPre.keep {s s' : State} {m : Mem} {n : Nat} (hp : VG.Proof.Rc2.X86.Cbc.StepPre s n) (h : Keep [.eax, .edx] {s with mem := m} s') : VG.Proof.Rc2.X86.Cbc.StepPre s' n :=
  hp.transport h.rd h.wr fun r hr => h.reg r (by
    have sep : ∀ r ∈ VG.Proof.Rc2.X86.Cbc.kept, r ∉ [.eax, .edx] := by decide
    exact sep r hr)

theorem StepPre.call {s : State} (hp : VG.Proof.Rc2.X86.Cbc.StepPre s) : VG.Proof.Rc2.X86.Cbc.CallPre s := by
  constructor
  · have hc : Covers [⟨addr32 (s.gpr .ebx), 128⟩, ⟨addr32 (s.gpr .esi), 8⟩, ⟨addr32 (s.gpr .ebp), 256⟩]
        [VG.Proof.Rc2.X86.Cbc.keyR s, VG.Proof.Rc2.X86.Cbc.ivR s, VG.Proof.Rc2.X86.Cbc.dataR s, VG.Proof.Rc2.X86.Cbc.bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨VG.Proof.Rc2.X86.Cbc.keyR s, by simp, 0, by simp, by simp⟩
      · exact ⟨VG.Proof.Rc2.X86.Cbc.dataR s, by simp, 0, by simp, by simp⟩
      · exact ⟨VG.Proof.Rc2.X86.Cbc.bufR s, by simp, 0, by simp, by simp⟩
    exact fun a n h => hp.reads a n (hc a n h)
  · have hc : Covers [⟨addr32 (s.gpr .esi), 8⟩, ⟨addr32 (s.gpr .ebp), 256⟩] [VG.Proof.Rc2.X86.Cbc.ivR s, VG.Proof.Rc2.X86.Cbc.dataR s, VG.Proof.Rc2.X86.Cbc.bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨VG.Proof.Rc2.X86.Cbc.dataR s, by simp, 0, by simp, by simp⟩
      · exact ⟨VG.Proof.Rc2.X86.Cbc.bufR s, by simp, 0, by simp, by simp⟩
    exact fun a n h => hp.writes a n (hc a n h)
  · exact hp.keyBuf.sub_right (Region.sub_prefix (by decide))
  · exact hp.dataBuf.sub_right (Region.sub_prefix (by decide))
  · exact hp.keyFit
  · simpa only [Nat.mul_one] using hp.dataFit
  · have := hp.bufFit; omega
  · exact hp.stackLo
  · exact hp.stackKey
  · exact hp.stackData
  · exact hp.stackBuf.sub_right (Region.sub_prefix (by decide))

theorem StepPre.readData {s : State} (hp : VG.Proof.Rc2.X86.Cbc.StepPre s) : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .esi)) 8 :=
  hp.reads _ _ ⟨VG.Proof.Rc2.X86.Cbc.dataR s, by simp, Region.contains_self _ _⟩

theorem StepPre.readIv {s : State} (hp : VG.Proof.Rc2.X86.Cbc.StepPre s) : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .ecx)) 8 :=
  hp.reads _ _ ⟨VG.Proof.Rc2.X86.Cbc.ivR s, by simp, Region.contains_self _ _⟩

theorem StepPre.writeData {s : State} (hp : VG.Proof.Rc2.X86.Cbc.StepPre s) : InRegions s.wr (addr32 (s.gpr .esi)) 8 :=
  hp.writes _ _ ⟨VG.Proof.Rc2.X86.Cbc.dataR s, by simp, Region.contains_self _ _⟩

theorem StepPre.writeIv {s : State} (hp : VG.Proof.Rc2.X86.Cbc.StepPre s) : InRegions s.wr (addr32 (s.gpr .ecx)) 8 :=
  hp.writes _ _ ⟨VG.Proof.Rc2.X86.Cbc.ivR s, by simp, Region.contains_self _ _⟩

theorem StepPre.readBuf {s : State} (hp : VG.Proof.Rc2.X86.Cbc.StepPre s) (i : Nat) (hi : i + 8 ≤ 512) :
    InRegions (s.rd ++ s.wr) (addr32 (s.gpr .ebp) + BitVec.ofNat 64 i) 8 :=
  hp.reads _ _ ⟨VG.Proof.Rc2.X86.Cbc.bufR s, by simp, Offset.contains_base _ hi (by omega)⟩

theorem StepPre.writeBuf {s : State} (hp : VG.Proof.Rc2.X86.Cbc.StepPre s) (i : Nat) (hi : i + 8 ≤ 512) :
    InRegions s.wr (addr32 (s.gpr .ebp) + BitVec.ofNat 64 i) 8 :=
  hp.writes _ _ ⟨VG.Proof.Rc2.X86.Cbc.bufR s, by simp, Offset.contains_base _ hi (by omega)⟩

end VG.Proof.Rc2.X86.Cbc

end

/-! # The frame preserved by a CBC step -/

namespace VG.Proof.Rc2.X86.Cbc

open VG VG.X86

def stepWrites (s : State) : List Region := [VG.Proof.Rc2.X86.Cbc.ivR s, VG.Proof.Rc2.X86.Cbc.dataR s, ⟨addr32 (s.gpr .ebp), 264⟩, VG.Proof.Rc2.X86.Cbc.stackR s]

structure Pinned (s s' : State) : Prop where
  reg : ∀ r ∈ VG.Proof.Rc2.X86.Cbc.kept, s'.gpr r = s.gpr r
  callee : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame (VG.Proof.Rc2.X86.Cbc.stepWrites s) s.mem s'.mem

theorem Pinned.of_keep {s s' : State} {m : Mem} (h : Keep [.eax, .edx] {s with mem := m} s')
    (frame : Frame (VG.Proof.Rc2.X86.Cbc.stepWrites s) s.mem m) : VG.Proof.Rc2.X86.Cbc.Pinned s s' := by
  have k : ∀ r ∈ VG.Proof.Rc2.X86.Cbc.kept, r ∉ [.eax, .edx] := by decide
  have c : ∀ r ∈ calleeSaved, r ∉ [.eax, .edx] := by decide
  exact ⟨fun r hr => h.reg r (k r hr), fun r hr => h.reg r (c r hr), h.rd, h.wr, by rw [h.mem]; exact frame⟩

theorem Pinned.of_call {d : Spec.Rc2.Direction} {s s' : State} (h : VG.Proof.Rc2.X86.Cbc.CallPost d s s') : VG.Proof.Rc2.X86.Cbc.Pinned s s' := by
  refine ⟨h.reg, h.callee, h.rd, h.wr, h.mem.sub ?_⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨VG.Proof.Rc2.X86.Cbc.dataR s, by simp [VG.Proof.Rc2.X86.Cbc.stepWrites], fun _ h => h⟩
  · exact ⟨⟨addr32 (s.gpr .ebp), 264⟩, by simp [VG.Proof.Rc2.X86.Cbc.stepWrites], Region.sub_prefix (by decide)⟩
  · exact ⟨VG.Proof.Rc2.X86.Cbc.stackR s, by simp [VG.Proof.Rc2.X86.Cbc.stepWrites], fun _ h => h⟩

theorem Pinned.writes_eq {s s' : State} (h : VG.Proof.Rc2.X86.Cbc.Pinned s s') : VG.Proof.Rc2.X86.Cbc.stepWrites s' = VG.Proof.Rc2.X86.Cbc.stepWrites s := by
  simp only [VG.Proof.Rc2.X86.Cbc.stepWrites, VG.Proof.Rc2.X86.Cbc.ivR, VG.Proof.Rc2.X86.Cbc.dataR, VG.Proof.Rc2.X86.Cbc.stackR, h.reg .ecx (by decide), h.reg .esi (by decide),
    h.reg .ebp (by decide), h.reg .esp (by decide)]

theorem Pinned.trans {s s' s'' : State} (h : VG.Proof.Rc2.X86.Cbc.Pinned s s') (h' : VG.Proof.Rc2.X86.Cbc.Pinned s' s'') : VG.Proof.Rc2.X86.Cbc.Pinned s s'' := by
  refine ⟨fun r hr => (h'.reg r hr).trans (h.reg r hr), fun r hr => (h'.callee r hr).trans (h.callee r hr),
    h'.rd.trans h.rd, h'.wr.trans h.wr, ?_⟩
  have f := h'.mem
  rw [h.writes_eq] at f
  exact h.mem.trans f

theorem Pinned.pre {s s' : State} {n : Nat} (h : VG.Proof.Rc2.X86.Cbc.Pinned s s') (hp : VG.Proof.Rc2.X86.Cbc.StepPre s n) : VG.Proof.Rc2.X86.Cbc.StepPre s' n :=
  hp.transport h.rd h.wr h.reg

theorem Pinned.schedule {s s' : State} (h : VG.Proof.Rc2.X86.Cbc.Pinned s s') (hp : VG.Proof.Rc2.X86.Cbc.StepPre s) :
    Spec.Rc2.scheduleAt s'.mem (addr32 (s.gpr .ebx)) = Spec.Rc2.scheduleAt s.mem (addr32 (s.gpr .ebx)) := by
  apply scheduleAt_frame h.mem
  simpa only [VG.Proof.Rc2.X86.Cbc.stepWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro hp.keyIv (And.intro hp.keyData (And.intro
      (hp.keyBuf.sub_right (Region.sub_prefix (by decide : 264 ≤ 512))) hp.stackKey.symm))

theorem CallPost.iv {d : Spec.Rc2.Direction} {s s' : State} (h : VG.Proof.Rc2.X86.Cbc.CallPost d s s') (hp : VG.Proof.Rc2.X86.Cbc.StepPre s) :
    Spec.Rc2.blockAt s'.mem (addr32 (s.gpr .ecx)) = Spec.Rc2.blockAt s.mem (addr32 (s.gpr .ecx)) := by
  apply blockAt_frame h.mem
  simpa only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro hp.ivData (And.intro
      (hp.ivBuf.sub_right (Region.sub_prefix (by decide : 256 ≤ 512))) hp.stackIv.symm)

structure StepPost (d : Spec.Rc2.Direction) (s s' : State) : Prop extends VG.Proof.Rc2.X86.Cbc.Pinned s s' where
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

theorem stash_sub (s : State) : Region.Sub (VG.Proof.Rc2.X86.Cbc.stashR s) (VG.Proof.Rc2.X86.Cbc.bufR s) :=
  Offset.sub_base _ (by decide)

theorem call_stash {d : Spec.Rc2.Direction} {s s' : State} (hp : VG.Proof.Rc2.X86.Cbc.StepPre s) (h : VG.Proof.Rc2.X86.Cbc.CallPost d s s') :
    Spec.Rc2.blockAt s'.mem (VG.Proof.Rc2.X86.Cbc.stashR s).base = Spec.Rc2.blockAt s.mem (VG.Proof.Rc2.X86.Cbc.stashR s).base := by
  apply blockAt_frame h.mem
  have sep : (VG.Proof.Rc2.X86.Cbc.stashR s).Disjoint ⟨addr32 (s.gpr .ebp), 256⟩ := by
    have h := Offset.disjoint (addr32 (s.gpr .ebp)) (d := 256) (n := 8) (e := 0) (k := 256)
      (by omega) (by decide) (by decide)
    simpa using h
  simpa only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro ((hp.dataBuf.sub_right (VG.Proof.Rc2.X86.Cbc.stash_sub s)).symm) (And.intro sep
      (hp.stackBuf.sub_right (VG.Proof.Rc2.X86.Cbc.stash_sub s)).symm)

theorem decryptStep_ok (s : State) (hp : VG.Proof.Rc2.X86.Cbc.StepPre s) :
    WP isa (Impl.Rc2.X86.Cbc.step .decrypt) s (VG.Proof.Rc2.X86.Cbc.StepPost .decrypt s) := by
  rw [Impl.Rc2.X86.Cbc.step]
  apply WP.seq
  apply WP.mono (VG.Proof.Rc2.X86.Cbc.copy64_ok s .esi .ebp 0 256 (by decide) (by decide)
    (by simpa using hp.dataFit) (by have := hp.bufFit; omega) (by simpa using hp.readData) (hp.writeBuf 256 (by decide)))
  intro s₁ keep₁
  simp only [BitVec.add_zero] at keep₁
  have frame₁ : Frame [VG.Proof.Rc2.X86.Cbc.stashR s] s.mem s₁.mem := by
    rw [keep₁.mem]; exact frame_store64 _ _ _
  have pin₁ : VG.Proof.Rc2.X86.Cbc.Pinned s s₁ := by
    apply Pinned.of_keep keep₁
    apply (frame_store64 _ _ _).sub
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact ⟨⟨addr32 (s.gpr .ebp), 264⟩, by simp [VG.Proof.Rc2.X86.Cbc.stepWrites], Offset.sub_base _ (by decide)⟩
  have hp₁ := pin₁.pre hp
  have key₁ := pin₁.schedule hp
  have data₁ := blockAt_frame frame₁ (addr32 (s.gpr .esi)) (by simpa using hp.dataBuf.sub_right (VG.Proof.Rc2.X86.Cbc.stash_sub s))
  have iv₁ := blockAt_frame frame₁ (addr32 (s.gpr .ecx)) (by simpa using hp.ivBuf.sub_right (VG.Proof.Rc2.X86.Cbc.stash_sub s))
  have stash₁ : Spec.Rc2.blockAt s₁.mem (VG.Proof.Rc2.X86.Cbc.stashR s).base = Spec.Rc2.blockAt s.mem (addr32 (s.gpr .esi)) := by
    rw [keep₁.mem]; exact blockAt_copy _ _ _
  apply WP.seq
  apply WP.mono (VG.Proof.Rc2.X86.Cbc.call_ok .decrypt s₁ hp₁.call)
  intro s₂ h₂
  have pin₂ := pin₁.trans (Pinned.of_call h₂)
  have hp₂ := pin₂.pre hp
  have output₂ := h₂.output
  rw [pin₁.reg .esi (by decide), pin₁.reg .ebx (by decide), key₁, data₁] at output₂
  have iv₂ := h₂.iv hp₁
  rw [pin₁.reg .ecx (by decide), iv₁] at iv₂
  have stash₂ := VG.Proof.Rc2.X86.Cbc.call_stash hp₁ h₂
  simp only [pin₁.reg .ebp (by decide)] at stash₂
  have stash₂' := stash₂.trans stash₁
  change WP isa (.block (Impl.Rc2.X86.Cbc.xor64 .esi .ecx ++
    Impl.Rc2.X86.Cbc.copy64 .ebp .ecx 256 0)) s₂ _
  rw [WP.block_append_iff]
  apply WP.mono (VG.Proof.Rc2.X86.Cbc.xor64_ok s₂ .esi .ecx (by decide) (by decide)
    (by simpa using hp₂.dataFit) hp₂.ivFit hp₂.readData hp₂.readIv hp₂.writeData)
  intro s₃ keep₃
  have frame₃ : Frame [VG.Proof.Rc2.X86.Cbc.dataR s₂] s₂.mem s₃.mem := by
    rw [keep₃.mem]; exact frame_store64 _ _ _
  have pin₃ := Pinned.of_keep keep₃ ((frame_store64 _ _ _).mono (by simp [VG.Proof.Rc2.X86.Cbc.stepWrites]))
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
  have stash₃ := blockAt_frame frame₃ (VG.Proof.Rc2.X86.Cbc.stashR s₂).base
    (by simpa using (hp₂.dataBuf.sub_right (VG.Proof.Rc2.X86.Cbc.stash_sub s₂)).symm)
  simp only [pin₂.reg .ebp (by decide)] at stash₃
  have stash₃' := stash₃.trans stash₂'
  apply WP.mono (VG.Proof.Rc2.X86.Cbc.copy64_ok s₃ .ebp .ecx 256 0 (by decide) (by decide)
    (by have := hp₃.bufFit; omega) (by simpa using hp₃.ivFit) (hp₃.readBuf 256 (by decide)) (by simpa using hp₃.writeIv))
  intro s₄ keep₄
  simp only [BitVec.add_zero] at keep₄
  have frame₄ : Frame [VG.Proof.Rc2.X86.Cbc.ivR s₃] s₃.mem s₄.mem := by
    rw [keep₄.mem]; exact frame_store64 _ _ _
  have pin₄ := Pinned.of_keep keep₄ ((frame_store64 _ _ _).mono (by simp [VG.Proof.Rc2.X86.Cbc.stepWrites]))
  refine ⟨pin₀₃.trans pin₄, ?_, ?_⟩
  · have same := blockAt_frame frame₄ (addr32 (s₃.gpr .esi)) (by simpa using hp₃.ivData.symm)
    rw [pin₀₃.reg .esi (by decide)] at same
    exact same.trans data₃
  · have out : Spec.Rc2.blockAt s₄.mem (addr32 (s₃.gpr .ecx)) = Spec.Rc2.blockAt s₃.mem (VG.Proof.Rc2.X86.Cbc.stashR s₃).base := by
      rw [keep₄.mem]; exact blockAt_copy _ _ _
    simp only [pin₀₃.reg .ecx (by decide), pin₀₃.reg .ebp (by decide)] at out
    exact out.trans stash₃'

end VG.Proof.Rc2.X86.Cbc

end

section

/-! # Restricting CBC permissions to a consecutive subrange -/

namespace VG.Proof.Rc2.X86.Cbc

open VG VG.X86

theorem StepPre.slice {s s' : State} {n m i : Nat} (hp : VG.Proof.Rc2.X86.Cbc.StepPre s n) (bound : i + m ≤ n)
    (startFit : (s.gpr .esi).toNat + 8 * i < 2 ^ 32)
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr)
    (key : s'.gpr .ebx = s.gpr .ebx) (iv : s'.gpr .ecx = s.gpr .ecx)
    (buf : s'.gpr .ebp = s.gpr .ebp) (sp : s'.gpr .esp = s.gpr .esp)
    (ptr : s'.gpr .esi = s.gpr .esi + BitVec.ofNat 32 (8 * i)) : VG.Proof.Rc2.X86.Cbc.StepPre s' m := by
  have ptrAddr : addr32 (s'.gpr .esi) = addr32 (s.gpr .esi) + BitVec.ofNat 64 (8 * i) := by
    rw [ptr]; exact addr_add startFit
  have fit : (s'.gpr .esi).toNat + 8 * m ≤ 2 ^ 32 := by
    rw [ptr, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * i) (by omega),
      Nat.mod_eq_of_lt startFit]
    have := hp.dataFit
    omega
  have sub : Region.Sub (VG.Proof.Rc2.X86.Cbc.dataR s' m) (VG.Proof.Rc2.X86.Cbc.dataR s n) := by
    change Region.Sub ⟨addr32 (s'.gpr .esi), 8 * m⟩ ⟨addr32 (s.gpr .esi), 8 * n⟩
    rw [ptrAddr]
    exact Offset.sub_base _ (by omega)
  constructor
  · rw [key]; exact hp.keyFit
  · rw [iv]; exact hp.ivFit
  · exact fit
  · rw [buf]; exact hp.bufFit
  · have hc : Covers [VG.Proof.Rc2.X86.Cbc.keyR s', VG.Proof.Rc2.X86.Cbc.ivR s', VG.Proof.Rc2.X86.Cbc.dataR s' m, VG.Proof.Rc2.X86.Cbc.bufR s'] [VG.Proof.Rc2.X86.Cbc.keyR s, VG.Proof.Rc2.X86.Cbc.ivR s, VG.Proof.Rc2.X86.Cbc.dataR s n, VG.Proof.Rc2.X86.Cbc.bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨VG.Proof.Rc2.X86.Cbc.keyR s, by simp, 0, by simp [key], by simp⟩
      · exact ⟨VG.Proof.Rc2.X86.Cbc.ivR s, by simp, 0, by simp [iv], by simp⟩
      · exact ⟨VG.Proof.Rc2.X86.Cbc.dataR s n, by simp, 8 * i, ptrAddr, by change 8 * i + 8 * m ≤ 8 * n; omega⟩
      · exact ⟨VG.Proof.Rc2.X86.Cbc.bufR s, by simp, 0, by simp [buf], by simp⟩
    rw [rd, wr]
    exact fun a k h => hp.reads a k (hc a k h)
  · have hc : Covers [VG.Proof.Rc2.X86.Cbc.ivR s', VG.Proof.Rc2.X86.Cbc.dataR s' m, VG.Proof.Rc2.X86.Cbc.bufR s'] [VG.Proof.Rc2.X86.Cbc.ivR s, VG.Proof.Rc2.X86.Cbc.dataR s n, VG.Proof.Rc2.X86.Cbc.bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨VG.Proof.Rc2.X86.Cbc.ivR s, by simp, 0, by simp [iv], by simp⟩
      · exact ⟨VG.Proof.Rc2.X86.Cbc.dataR s n, by simp, 8 * i, ptrAddr, by change 8 * i + 8 * m ≤ 8 * n; omega⟩
      · exact ⟨VG.Proof.Rc2.X86.Cbc.bufR s, by simp, 0, by simp [buf], by simp⟩
    rw [wr]
    exact fun a k h => hp.writes a k (hc a k h)
  · simpa only [VG.Proof.Rc2.X86.Cbc.keyR, VG.Proof.Rc2.X86.Cbc.ivR, key, iv] using hp.keyIv
  · simpa only [VG.Proof.Rc2.X86.Cbc.keyR, key] using hp.keyData.sub_right sub
  · simpa only [VG.Proof.Rc2.X86.Cbc.keyR, VG.Proof.Rc2.X86.Cbc.bufR, key, buf] using hp.keyBuf
  · simpa only [VG.Proof.Rc2.X86.Cbc.ivR, iv] using hp.ivData.sub_right sub
  · simpa only [VG.Proof.Rc2.X86.Cbc.ivR, VG.Proof.Rc2.X86.Cbc.bufR, iv, buf] using hp.ivBuf
  · simpa only [VG.Proof.Rc2.X86.Cbc.bufR, buf] using hp.dataBuf.sub_left sub

  · rw [sp]; exact hp.stackLo
  · simpa only [VG.Proof.Rc2.X86.Cbc.stackR, VG.Proof.Rc2.X86.Cbc.keyR, sp, key] using hp.stackKey
  · simpa only [VG.Proof.Rc2.X86.Cbc.stackR, VG.Proof.Rc2.X86.Cbc.ivR, sp, iv] using hp.stackIv
  · simpa only [VG.Proof.Rc2.X86.Cbc.stackR, sp] using hp.stackData.sub_right sub
  · simpa only [VG.Proof.Rc2.X86.Cbc.stackR, VG.Proof.Rc2.X86.Cbc.bufR, sp, buf] using hp.stackBuf

theorem StepPre.head {s : State} {n : Nat} (hp : VG.Proof.Rc2.X86.Cbc.StepPre s n) (hn : 1 ≤ n) : VG.Proof.Rc2.X86.Cbc.StepPre s :=
  hp.slice (i := 0) hn (by simpa using (s.gpr .esi).isLt) rfl rfl rfl rfl rfl rfl (by simp)

end VG.Proof.Rc2.X86.Cbc

end

section

/-! # One CBC encryption step -/

namespace VG.Proof.Rc2.X86.Cbc

open VG VG.X86 VG.Impl.Rc2.X86

theorem encryptStep_ok (s : State) (hp : VG.Proof.Rc2.X86.Cbc.StepPre s) :
    WP isa (Impl.Rc2.X86.Cbc.step .encrypt) s (VG.Proof.Rc2.X86.Cbc.StepPost .encrypt s) := by
  rw [Impl.Rc2.X86.Cbc.step]
  apply WP.seq
  apply WP.mono (VG.Proof.Rc2.X86.Cbc.xor64_ok s .esi .ecx (by decide) (by decide)
    (by simpa using hp.dataFit) hp.ivFit hp.readData hp.readIv hp.writeData)
  intro s₁ keep₁
  have pin₁ := Pinned.of_keep keep₁ ((frame_store64 _ _ _).mono (by simp [VG.Proof.Rc2.X86.Cbc.stepWrites]))
  have hp₁ := pin₁.pre hp
  have key₁ := pin₁.schedule hp
  have data₁ : Spec.Rc2.blockAt s₁.mem (addr32 (s.gpr .esi)) =
      Spec.Rc2.xorBlock (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .esi))) (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .ecx))) := by
    rw [keep₁.mem]; exact blockAt_xor _ _ _
  apply WP.seq
  apply WP.mono (VG.Proof.Rc2.X86.Cbc.call_ok .encrypt s₁ hp₁.call)
  intro s₂ h₂
  have pin₂ := pin₁.trans (Pinned.of_call h₂)
  have hp₂ := pin₂.pre hp
  have output₂ := h₂.output
  rw [pin₁.reg .esi (by decide), pin₁.reg .ebx (by decide), key₁, data₁] at output₂
  apply WP.mono (VG.Proof.Rc2.X86.Cbc.copy64_ok s₂ .esi .ecx 0 0 (by decide) (by decide)
    (by simpa using hp₂.dataFit) (by simpa using hp₂.ivFit) (by simpa using hp₂.readData) (by simpa using hp₂.writeIv))
  intro s₃ keep₃
  simp only [BitVec.add_zero] at keep₃
  have frame₃ : Frame [VG.Proof.Rc2.X86.Cbc.ivR s₂] s₂.mem s₃.mem := by
    rw [keep₃.mem]; exact frame_store64 _ _ _
  have pin₃ := Pinned.of_keep keep₃ ((frame_store64 _ _ _).mono (by simp [VG.Proof.Rc2.X86.Cbc.stepWrites]))
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

theorem step_ok (d : Spec.Rc2.Direction) (s : State) (hp : VG.Proof.Rc2.X86.Cbc.StepPre s) :
    WP isa (Impl.Rc2.X86.Cbc.step d) s (VG.Proof.Rc2.X86.Cbc.StepPost d s) := by
  cases d
  · exact VG.Proof.Rc2.X86.Cbc.encryptStep_ok s hp
  · exact VG.Proof.Rc2.X86.Cbc.decryptStep_ok s hp

structure BodyPost (d : Spec.Rc2.Direction) (s : State) (n : Nat) (s' : State) : Prop where
  ptr : s'.gpr .esi = s.gpr .esi + 8
  count : s'.gpr .edi = BitVec.ofNat 32 (n - 1)
  flag : VG.Proof.Rc2.X86.Cbc.zeroCount s' = some (decide (n = 1))
  reg : ∀ r ∈ VG.Proof.Rc2.X86.Cbc.kept, r ≠ .esi → r ≠ .edi → s'.gpr r = s.gpr r
  callee : ∀ r ∈ calleeSaved, r ≠ .esi → r ≠ .edi → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame (VG.Proof.Rc2.X86.Cbc.stepWrites s) s.mem s'.mem
  data : Spec.Rc2.blockAt s'.mem (addr32 (s.gpr .esi)) =
    (Spec.Rc2.cbcStep (Spec.Rc2.scheduleAt s.mem (addr32 (s.gpr .ebx))) d
      (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .ecx))) (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .esi)))).1
  iv : Spec.Rc2.blockAt s'.mem (addr32 (s.gpr .ecx)) =
    (Spec.Rc2.cbcStep (Spec.Rc2.scheduleAt s.mem (addr32 (s.gpr .ebx))) d
      (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .ecx))) (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .esi)))).2

theorem body_ok (d : Spec.Rc2.Direction) (s : State) (n : Nat) (hn : 1 ≤ n) (bound : n < 2 ^ 32)
    (count : s.gpr .edi = BitVec.ofNat 32 n) (hp : VG.Proof.Rc2.X86.Cbc.StepPre s) :
    WP isa (Impl.Rc2.X86.Cbc.body d) s (VG.Proof.Rc2.X86.Cbc.BodyPost d s n) := by
  rw [Impl.Rc2.X86.Cbc.body]
  apply WP.seq
  apply WP.mono (VG.Proof.Rc2.X86.Cbc.step_ok d s hp)
  intro s₁ h₁
  obtain ⟨s₂, run₂, ptr₂, count₂, flag₂, keep₂⟩ := VG.Proof.Rc2.X86.Cbc.advance_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have count' : s₁.gpr .edi - 1 = BitVec.ofNat 32 (n - 1) := by
    rw [h₁.reg .edi (by decide), count]
    exact Offset.ofNat_sub_ofNat hn
  refine ⟨by rw [ptr₂, h₁.reg .esi (by decide)], count₂.trans count', ?_, ?_, ?_,
    keep₂.rd.trans h₁.rd, keep₂.wr.trans h₁.wr, ?_, ?_, ?_⟩
  · rw [VG.Proof.Rc2.X86.Cbc.zeroCount, flag₂, count']
    have eqZero := counter_eq (n - 1) 0 (by omega) (by decide)
    simp only [BitVec.sub_zero] at eqZero
    change some (BitVec.ofNat 32 (n - 1) == 0#32) = _
    rw [eqZero]
    have he : n - 1 = 0 ↔ n = 1 := by omega
    simp only [he]
  · intro r hr hs hb
    exact (keep₂.reg r (by simp [hs, hb])).trans (h₁.reg r hr)
  · intro r hr hs hb
    exact (keep₂.reg r (by simp [hs, hb])).trans (h₁.callee r hr)
  · rw [keep₂.mem]; exact h₁.mem
  · rw [keep₂.mem]; exact h₁.data
  · rw [keep₂.mem]; exact h₁.iv

theorem BodyPost.tail {d : Spec.Rc2.Direction} {s s' : State} {n : Nat}
    (h : VG.Proof.Rc2.X86.Cbc.BodyPost d s (n + 1) s') (hp : VG.Proof.Rc2.X86.Cbc.StepPre s (n + 1)) (hn : 1 ≤ n) : VG.Proof.Rc2.X86.Cbc.StepPre s' n :=
  hp.slice (i := 1) (by omega) (by have := hp.dataFit; omega) h.rd h.wr
    (h.reg .ebx (by decide) (by decide) (by decide))
    (h.reg .ecx (by decide) (by decide) (by decide))
    (h.reg .ebp (by decide) (by decide) (by decide))
    (h.reg .esp (by decide) (by decide) (by decide))
    h.ptr

end VG.Proof.Rc2.X86.Cbc

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.X86.Cbc.Loop`. -/
section

section

/-! # Frames for successive CBC blocks -/

namespace VG.Proof.Rc2.X86.Cbc

open VG VG.X86

def loopWrites (s : State) (n : Nat) : List Region := [VG.Proof.Rc2.X86.Cbc.ivR s, VG.Proof.Rc2.X86.Cbc.dataR s n, ⟨addr32 (s.gpr .ebp), 264⟩, VG.Proof.Rc2.X86.Cbc.stackR s]

theorem loopFrame_slice {s s' : State} {n m i : Nat} {a b : Mem}
    (h : Frame (VG.Proof.Rc2.X86.Cbc.loopWrites s' m) a b) (bound : i + m ≤ n)
    (iv : s'.gpr .ecx = s.gpr .ecx) (buf : s'.gpr .ebp = s.gpr .ebp) (sp : s'.gpr .esp = s.gpr .esp)
    (ptr : addr32 (s'.gpr .esi) = addr32 (s.gpr .esi) + BitVec.ofNat 64 (8 * i)) :
    Frame (VG.Proof.Rc2.X86.Cbc.loopWrites s n) a b := by
  apply h.sub
  intro r hr
  simp only [VG.Proof.Rc2.X86.Cbc.loopWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · refine ⟨VG.Proof.Rc2.X86.Cbc.ivR s, by simp [VG.Proof.Rc2.X86.Cbc.loopWrites], ?_⟩
    change Region.Sub ⟨addr32 (s'.gpr .ecx), 8⟩ ⟨addr32 (s.gpr .ecx), 8⟩
    rw [iv]; exact fun _ h => h
  · refine ⟨VG.Proof.Rc2.X86.Cbc.dataR s n, by simp [VG.Proof.Rc2.X86.Cbc.loopWrites], ?_⟩
    change Region.Sub ⟨addr32 (s'.gpr .esi), 8 * m⟩ ⟨addr32 (s.gpr .esi), 8 * n⟩
    rw [ptr]
    exact Offset.sub_base _ (by omega)
  · refine ⟨⟨addr32 (s.gpr .ebp), 264⟩, by simp [VG.Proof.Rc2.X86.Cbc.loopWrites], ?_⟩
    rw [buf]; exact fun _ h => h
  · refine ⟨VG.Proof.Rc2.X86.Cbc.stackR s, by simp [VG.Proof.Rc2.X86.Cbc.loopWrites], ?_⟩
    change Region.Sub (below (s'.gpr .esp) 16) (below (s.gpr .esp) 16)
    rw [sp]; exact fun _ h => h

theorem BodyPost.frame {d : Spec.Rc2.Direction} {s s' : State} {n : Nat}
    (h : VG.Proof.Rc2.X86.Cbc.BodyPost d s n s') (hn : 1 ≤ n) : Frame (VG.Proof.Rc2.X86.Cbc.loopWrites s n) s.mem s'.mem :=
  VG.Proof.Rc2.X86.Cbc.loopFrame_slice (m := 1) (i := 0) h.mem hn rfl rfl rfl (by simp)

theorem BodyPost.schedule {d : Spec.Rc2.Direction} {s s' : State} {n : Nat}
    (h : VG.Proof.Rc2.X86.Cbc.BodyPost d s n s') (hp : VG.Proof.Rc2.X86.Cbc.StepPre s) :
    Spec.Rc2.scheduleAt s'.mem (addr32 (s.gpr .ebx)) = Spec.Rc2.scheduleAt s.mem (addr32 (s.gpr .ebx)) := by
  apply scheduleAt_frame h.mem
  simpa only [VG.Proof.Rc2.X86.Cbc.stepWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro hp.keyIv (And.intro hp.keyData (And.intro
      (hp.keyBuf.sub_right (Region.sub_prefix (by decide : 264 ≤ 512))) hp.stackKey.symm))

theorem BodyPost.tailData {d : Spec.Rc2.Direction} {s s' : State} {n : Nat}
    (h : VG.Proof.Rc2.X86.Cbc.BodyPost d s (n + 1) s') (hp : VG.Proof.Rc2.X86.Cbc.StepPre s (n + 1)) (bound : 8 * (n + 1) ≤ 2 ^ 64) :
    Spec.Rc2.blocksAt s'.mem (addr32 (s.gpr .esi) + 8) n = Spec.Rc2.blocksAt s.mem (addr32 (s.gpr .esi) + 8) n := by
  have sub : Region.Sub ⟨addr32 (s.gpr .esi) + 8, 8 * n⟩ (VG.Proof.Rc2.X86.Cbc.dataR s (n + 1)) :=
    Offset.sub_base _ (by change 8 + 8 * n ≤ 8 * (n + 1); omega)
  have sep : (Region.mk (addr32 (s.gpr .esi) + 8) (8 * n)).Disjoint (VG.Proof.Rc2.X86.Cbc.dataR s) :=
    Offset.disjoint_base _ (d := 8) (n := 8 * n) (k := 8) (by decide) (by omega)
  apply blocksAt_frame h.mem
  simpa only [VG.Proof.Rc2.X86.Cbc.stepWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro ((hp.ivData.sub_right sub).symm) (And.intro sep (And.intro
      ((hp.dataBuf.sub_left sub).sub_right (Region.sub_prefix (by decide : 264 ≤ 512))) (hp.stackData.sub_right sub).symm))

theorem firstBlock_frame {d : Spec.Rc2.Direction} {s s' : State} {n : Nat} {m : Mem}
    (h : VG.Proof.Rc2.X86.Cbc.BodyPost d s (n + 1) s') (hp : VG.Proof.Rc2.X86.Cbc.StepPre s (n + 1)) (bound : 8 * (n + 1) ≤ 2 ^ 64)
    (hn : 1 ≤ n)
    (frame : Frame (VG.Proof.Rc2.X86.Cbc.loopWrites s' n) s'.mem m) :
    Spec.Rc2.blockAt m (addr32 (s.gpr .esi)) = Spec.Rc2.blockAt s'.mem (addr32 (s.gpr .esi)) := by
  have first : Region.Sub (VG.Proof.Rc2.X86.Cbc.dataR s) (VG.Proof.Rc2.X86.Cbc.dataR s (n + 1)) := Region.sub_prefix (by change 8 ≤ 8 * (n + 1); omega)
  have sep : (VG.Proof.Rc2.X86.Cbc.dataR s).Disjoint ⟨addr32 (s.gpr .esi) + 8, 8 * n⟩ :=
    Offset.base_disjoint _ (e := 8) (n := 8 * n) (k := 8) (by decide) (by omega)
  have ptr : addr32 (s'.gpr .esi) = addr32 (s.gpr .esi) + 8 := by
    rw [h.ptr]
    exact addr_add (k := 8) (by have := hp.dataFit; omega)
  apply blockAt_frame frame
  have iv := h.reg .ecx (by decide) (by decide) (by decide)
  have buf := h.reg .ebp (by decide) (by decide) (by decide)
  have sp := h.reg .esp (by decide) (by decide) (by decide)
  simpa only [VG.Proof.Rc2.X86.Cbc.loopWrites, VG.Proof.Rc2.X86.Cbc.ivR, VG.Proof.Rc2.X86.Cbc.dataR, VG.Proof.Rc2.X86.Cbc.stackR, iv, buf, ptr, sp,
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
  reg : ∀ r ∈ VG.Proof.Rc2.X86.Cbc.kept, r ≠ .esi → r ≠ .edi → s'.gpr r = s.gpr r
  callee : ∀ r ∈ calleeSaved, r ≠ .esi → r ≠ .edi → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame (VG.Proof.Rc2.X86.Cbc.loopWrites s n) s.mem s'.mem
  data : Spec.Rc2.blocksAt s'.mem (addr32 (s.gpr .esi)) n =
    (Spec.Rc2.cbc (Spec.Rc2.scheduleAt s.mem (addr32 (s.gpr .ebx))) d
      (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .ecx))) (Spec.Rc2.blocksAt s.mem (addr32 (s.gpr .esi)) n)).1
  iv : Spec.Rc2.blockAt s'.mem (addr32 (s.gpr .ecx)) =
    (Spec.Rc2.cbc (Spec.Rc2.scheduleAt s.mem (addr32 (s.gpr .ebx))) d
      (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .ecx))) (Spec.Rc2.blocksAt s.mem (addr32 (s.gpr .esi)) n)).2

theorem loop_ok (d : Spec.Rc2.Direction) (n : Nat) :
    ∀ s : State, 1 ≤ n → 8 * n ≤ 2 ^ 32 → VG.Proof.Rc2.X86.Cbc.StepPre s n → s.gpr .edi = BitVec.ofNat 32 n →
      WP isa (.loop (Impl.Rc2.X86.Cbc.body d) .ne) s (VG.Proof.Rc2.X86.Cbc.LoopPost d s n) := by
  induction n with
  | zero => intro s hn; omega
  | succ n ih =>
    intro s hn bound hp count
    obtain ⟨t₁, s₁, exec₁, h₁⟩ := VG.Proof.Rc2.X86.Cbc.body_ok d s (n + 1) hn (by omega) count (hp.head hn)
    by_cases hz : n = 0
    · subst n
      refine ⟨_, s₁, Exec.loopExit exec₁ ?_, ?_⟩
      · simp only [VG.Proof.Rc2.X86.Cbc.eval_nonzeroCount, h₁.flag, decide_true, Option.map_some, Bool.not_true]
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
        simp only [VG.Proof.Rc2.X86.Cbc.eval_nonzeroCount, h₁.flag, he, decide_false, Option.map_some, Bool.not_false]
      · have key := h₁.schedule (hp.head hn)
        have tail := h₁.tailData hp (by omega)
        have data := h₂.data
        have iv := h₂.iv
        have ki := h₁.reg .ebx (by decide) (by decide) (by decide)
        have vi := h₁.reg .ecx (by decide) (by decide) (by decide)
        have bi := h₁.reg .ebp (by decide) (by decide) (by decide)
        have ptr : addr32 (s₁.gpr .esi) = addr32 (s.gpr .esi) + 8 := by
          rw [h₁.ptr]; exact addr_add (k := 8) (by have := hp.dataFit; omega)
        rw [ki, vi, ptr, key, tail, h₁.iv] at data
        rw [ki, vi, ptr, key, tail, h₁.iv] at iv
        refine ⟨?_, h₂.count, ?_, ?_, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, ?_, ?_, ?_⟩
        · rw [h₂.ptr, h₁.ptr, BitVec.add_assoc]
          exact congrArg (s.gpr .esi + ·) (by
            change BitVec.ofNat 32 8 + BitVec.ofNat 32 (8 * n) = _
            rw [← BitVec.ofNat_add]
            exact congrArg (BitVec.ofNat 32) (by omega))
        · intro r hr hs hb
          exact (h₂.reg r hr hs hb).trans (h₁.reg r hr hs hb)
        · intro r hr hs hb
          exact (h₂.callee r hr hs hb).trans (h₁.callee r hr hs hb)
        · exact (h₁.frame hn).trans (VG.Proof.Rc2.X86.Cbc.loopFrame_slice (i := 1) h₂.mem (by omega) vi bi (h₁.reg .esp (by decide) (by decide) (by decide)) ptr)
        · have first := VG.Proof.Rc2.X86.Cbc.firstBlock_frame h₁ hp (by omega) (by omega) h₂.mem
          rw [blocksAt_cons, first, h₁.data, data, blocksAt_cons]
          rfl
        · rw [blocksAt_cons]
          exact iv

theorem maybeLoop_ok (d : Spec.Rc2.Direction) (s : State) (n : Nat) (bound : 8 * n ≤ 2 ^ 32)
    (hp : VG.Proof.Rc2.X86.Cbc.StepPre s n) (count : s.gpr .edi = BitVec.ofNat 32 n)
    (flag : VG.Proof.Rc2.X86.Cbc.zeroCount s = some (s.gpr .edi == 0)) :
    WP isa (.ite .e (.block []) (.loop (Impl.Rc2.X86.Cbc.body d) .ne)) s (VG.Proof.Rc2.X86.Cbc.LoopPost d s n) := by
  have eqZero := counter_eq n 0 (by omega) (by decide)
  simp only [BitVec.sub_zero] at eqZero
  have flag' : VG.Proof.Rc2.X86.Cbc.zeroCount s = some (decide (n = 0)) := by
    rw [flag, count]
    exact congrArg some eqZero
  by_cases hz : n = 0
  · subst n
    apply WP.ite true (by simp only [VG.Proof.Rc2.X86.Cbc.eval_zeroCount, flag', decide_true])
    · intro _
      apply WP.block_nil
      refine ⟨by simp, count, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, rfl, rfl, Frame.refl _ _, ?_, ?_⟩
      · rfl
      · rfl
    · simp
  · apply WP.ite false (by simp only [VG.Proof.Rc2.X86.Cbc.eval_zeroCount, flag', hz, decide_false])
    · simp
    · intro _
      exact VG.Proof.Rc2.X86.Cbc.loop_ok d n s (by omega) bound hp count

theorem LoopPost.scratchRead {d : Spec.Rc2.Direction} {s s' : State} {n : Nat}
    (h : VG.Proof.Rc2.X86.Cbc.LoopPost d s n s') (hp : VG.Proof.Rc2.X86.Cbc.StepPre s n) (i : Nat) (lo : 264 ≤ i) (hi : i + 4 ≤ 512) :
    s'.mem.readW (addr32 (s.gpr .ebp) + BitVec.ofNat 64 i) 32 = s.mem.readW (addr32 (s.gpr .ebp) + BitVec.ofNat 64 i) 32 := by
  have sub : Region.Sub ⟨addr32 (s.gpr .ebp) + BitVec.ofNat 64 i, 4⟩ (VG.Proof.Rc2.X86.Cbc.bufR s) := Offset.sub_base _ hi
  have sep : (Region.mk (addr32 (s.gpr .ebp) + BitVec.ofNat 64 i) 4).Disjoint ⟨addr32 (s.gpr .ebp), 264⟩ :=
    Offset.disjoint_base _ lo (by omega)
  apply h.mem.readW (r := ⟨addr32 (s.gpr .ebp) + BitVec.ofNat 64 i, 4⟩) (Region.contains_self _ _)
    (hn := by decide)
  simpa only [VG.Proof.Rc2.X86.Cbc.loopWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro ((hp.ivBuf.sub_right sub).symm) (And.intro ((hp.dataBuf.sub_right sub).symm)
      (And.intro sep (hp.stackBuf.sub_right sub).symm))

end VG.Proof.Rc2.X86.Cbc

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.X86.Cbc.Contract`. -/
section

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
    : ∃ s', runBlock isa Impl.Rc2.X86.Cbc.save s = some s' ∧ Keep [] {s with mem := VG.Proof.Rc2.X86.Cbc.savedMem s} s' := by
  have a264 : addr32 (s.gpr .eax + BitVec.ofNat 32 264) = addr32 (s.gpr .eax) + BitVec.ofNat 64 264 := addr_add (by omega)
  have a268 : addr32 (s.gpr .eax + BitVec.ofNat 32 268) = addr32 (s.gpr .eax) + BitVec.ofNat 64 268 := addr_add (by omega)
  have a272 : addr32 (s.gpr .eax + BitVec.ofNat 32 272) = addr32 (s.gpr .eax) + BitVec.ofNat 64 272 := addr_add (by omega)
  have a276 : addr32 (s.gpr .eax + BitVec.ofNat 32 276) = addr32 (s.gpr .eax) + BitVec.ofNat 64 276 := addr_add (by omega)
  refine ⟨_, by
    simp only [Impl.Rc2.X86.Cbc.save, runBlock_cons, runStep_some, runBlock_nil,
      exec, memOp, State.ea, State.store32, ← addr_eq_def,
      a264, a268, a272, a276, w0, w1, w2, w3, ite_true]
    rfl, ?_⟩
  exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem savedMem_frame (s : State) : Frame [⟨addr32 (s.gpr .eax), 512⟩] s.mem (VG.Proof.Rc2.X86.Cbc.savedMem s) := by
  unfold VG.Proof.Rc2.X86.Cbc.savedMem
  apply Frame.writeW (r := ⟨addr32 (s.gpr .eax), 512⟩) (hr := List.mem_cons_self) (hb := Offset.contains_base _ (by decide : 276 + 4 ≤ 512) (by decide))
  apply Frame.writeW (r := ⟨addr32 (s.gpr .eax), 512⟩) (hr := List.mem_cons_self) (hb := Offset.contains_base _ (by decide : 272 + 4 ≤ 512) (by decide))
  apply Frame.writeW (r := ⟨addr32 (s.gpr .eax), 512⟩) (hr := List.mem_cons_self) (hb := Offset.contains_base _ (by decide : 268 + 4 ≤ 512) (by decide))
  apply Frame.writeW (r := ⟨addr32 (s.gpr .eax), 512⟩) (hr := List.mem_cons_self) (hb := Offset.contains_base _ (by decide : 264 + 4 ≤ 512) (by decide))
  exact Frame.refl _ _

theorem savedMem_ebp (s : State) : (VG.Proof.Rc2.X86.Cbc.savedMem s).readW (addr32 (s.gpr .eax) + BitVec.ofNat 64 264) 32 = s.gpr .ebp := by
  rw [VG.Proof.Rc2.X86.Cbc.savedMem, Mem.readW_writeW_sep (Offset.sep _ (by decide : 264 + 4 ≤ 276 ∨ 276 + 4 ≤ 264) (by decide) (by decide)) (by decide), Mem.readW_writeW_sep (Offset.sep _ (by decide : 264 + 4 ≤ 272 ∨ 272 + 4 ≤ 264) (by decide) (by decide)) (by decide), Mem.readW_writeW_sep (Offset.sep _ (by decide : 264 + 4 ≤ 268 ∨ 268 + 4 ≤ 264) (by decide) (by decide)) (by decide), Mem.readW_writeW_self32]

theorem savedMem_ebx (s : State) : (VG.Proof.Rc2.X86.Cbc.savedMem s).readW (addr32 (s.gpr .eax) + BitVec.ofNat 64 268) 32 = s.gpr .ebx := by
  rw [VG.Proof.Rc2.X86.Cbc.savedMem, Mem.readW_writeW_sep (Offset.sep _ (by decide : 268 + 4 ≤ 276 ∨ 276 + 4 ≤ 268) (by decide) (by decide)) (by decide), Mem.readW_writeW_sep (Offset.sep _ (by decide : 268 + 4 ≤ 272 ∨ 272 + 4 ≤ 268) (by decide) (by decide)) (by decide), Mem.readW_writeW_self32]

theorem savedMem_esi (s : State) : (VG.Proof.Rc2.X86.Cbc.savedMem s).readW (addr32 (s.gpr .eax) + BitVec.ofNat 64 272) 32 = s.gpr .esi := by
  rw [VG.Proof.Rc2.X86.Cbc.savedMem, Mem.readW_writeW_sep (Offset.sep _ (by decide : 272 + 4 ≤ 276 ∨ 276 + 4 ≤ 272) (by decide) (by decide)) (by decide), Mem.readW_writeW_self32]

theorem savedMem_edi (s : State) : (VG.Proof.Rc2.X86.Cbc.savedMem s).readW (addr32 (s.gpr .eax) + BitVec.ofNat 64 276) 32 = s.gpr .edi := by
  rw [VG.Proof.Rc2.X86.Cbc.savedMem, Mem.readW_writeW_self32]

theorem setup_ok (s : State)
    (readable : ∀ i < 4, InRegions (s.rd ++ s.wr) (argAddr s i) 4) :
    ∃ s', runBlock isa Impl.Rc2.X86.Cbc.setup s = some s' ∧
      s'.gpr .ebx = arg s 0 ∧ s'.gpr .ecx = arg s 1 ∧ s'.gpr .esi = arg s 2 ∧
      s'.gpr .edi = arg s 3 ∧ s'.gpr .ebp = s.gpr .eax ∧
      VG.Proof.Rc2.X86.Cbc.zeroCount s' = some (arg s 3 == 0) ∧ Keep [.ebp, .ebx, .ecx, .esi, .edi] s s' := by
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
      (∀ r ∈ VG.Proof.Rc2.X86.Cbc.callerSaved, s'.gpr r = values r) ∧ Keep (.eax :: VG.Proof.Rc2.X86.Cbc.callerSaved) s s' := by
  have a264 : addr32 (s.gpr .ebp + BitVec.ofNat 32 264) = addr32 (s.gpr .ebp) + BitVec.ofNat 64 264 := addr_add (by omega)
  have a268 : addr32 (s.gpr .ebp + BitVec.ofNat 32 268) = addr32 (s.gpr .ebp) + BitVec.ofNat 64 268 := addr_add (by omega)
  have a272 : addr32 (s.gpr .ebp + BitVec.ofNat 32 272) = addr32 (s.gpr .ebp) + BitVec.ofNat 64 272 := addr_add (by omega)
  have a276 : addr32 (s.gpr .ebp + BitVec.ofNat 32 276) = addr32 (s.gpr .ebp) + BitVec.ofNat 64 276 := addr_add (by omega)
  refine ⟨_, by
    simp only [Impl.Rc2.X86.Cbc.restore, rr, runBlock_cons, runStep_some, runBlock_nil,
      exec, readSrc, memOp, State.ea, State.load32, gpr_setReg, reduceCtorEq, ite_false, ite_true,
      mem_setReg, rd_setReg, wr_setReg, Option.map_some, ← addr_eq_def,
      a264, a268, a272, a276, r0, r1, r2, r3, v0, v1, v2, v3]
    rfl, ?_⟩
  constructor
  · intro r hr
    simp only [VG.Proof.Rc2.X86.Cbc.callerSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false]
  · refine ⟨?_, rfl, rfl, rfl⟩
    intro r hr
    simp only [VG.Proof.Rc2.X86.Cbc.callerSaved, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
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
    let out := Spec.Rc2.cbc (Spec.Rc2.scheduleAt s.mem (addr32 (arg s 0))) d
      (Spec.Rc2.blockAt s.mem (addr32 (arg s 1))) (Spec.Rc2.blocksAt s.mem (addr32 (arg s 2)) (arg s 3).toNat)
    Spec.Rc2.blocksAt s'.mem (addr32 (arg s 2)) (arg s 3).toNat = out.1 ∧
      Spec.Rc2.blockAt s'.mem (addr32 (arg s 1)) = out.2
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

end VG.Proof.Rc2.X86.Cbc

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.X86.Cbc.ConstantTime`. -/
section

section

section

/-! # Constant-time CBC steps with public registers restored by the block call -/

namespace VG.Proof.Rc2.X86.Cbc

open VG VG.X86 VG.Impl.Rc2.X86

def EqKept (s₁ s₂ : State) : Prop := ∀ r ∈ VG.Proof.Rc2.X86.Cbc.kept, s₁.gpr r = s₂.gpr r

def StepRel (s₁ s₂ : State) : Prop := VG.Proof.Rc2.X86.Cbc.StepPre s₁ ∧ VG.Proof.Rc2.X86.Cbc.StepPre s₂ ∧ VG.Proof.Rc2.X86.Cbc.EqKept s₁ s₂

theorem agreeKept {s₁ s₂ : State} (h : VG.Proof.Rc2.X86.Cbc.EqKept s₁ s₂) :
    VG.X86.Taint.Agree (τr VG.Proof.Rc2.X86.Cbc.kept) s₁ s₂ := agree_regs h

theorem before_ok (d : Spec.Rc2.Direction) (s : State) (hp : VG.Proof.Rc2.X86.Cbc.StepPre s) :
    WP isa (.block (Impl.Rc2.X86.Cbc.before d)) s (fun s' => VG.Proof.Rc2.X86.Cbc.StepPre s' ∧ ∀ r ∈ VG.Proof.Rc2.X86.Cbc.kept, s'.gpr r = s.gpr r) := by
  have sep : ∀ r ∈ VG.Proof.Rc2.X86.Cbc.kept, r ∉ VG.Proof.Rc2.X86.Cbc.temps := by decide
  cases d
  · apply WP.mono (VG.Proof.Rc2.X86.Cbc.xor64_ok s .esi .ecx (by decide) (by decide)
      (by simpa using hp.dataFit) hp.ivFit hp.readData hp.readIv hp.writeData)
    intro s' h
    exact ⟨hp.keep h, fun r hr => h.reg r (sep r hr)⟩
  · apply WP.mono (VG.Proof.Rc2.X86.Cbc.copy64_ok s .esi .ebp 0 256 (by decide) (by decide)
      (by simpa using hp.dataFit) (by have := hp.bufFit; omega)
      (by simpa using hp.readData) (hp.writeBuf 256 (by decide)))
    intro s' h
    exact ⟨hp.keep h, fun r hr => h.reg r (sep r hr)⟩

theorem kept_ct {c : Prog isa} (h : RelCT isa VG.Proof.Rc2.X86.Cbc.StepRel c (fun _ _ => True))
    (correct : ∀ s, VG.Proof.Rc2.X86.Cbc.StepPre s → WP isa c s (fun s' => VG.Proof.Rc2.X86.Cbc.StepPre s' ∧ ∀ r ∈ VG.Proof.Rc2.X86.Cbc.kept, s'.gpr r = s.gpr r)) :
    RelCT isa VG.Proof.Rc2.X86.Cbc.StepRel c VG.Proof.Rc2.X86.Cbc.StepRel := by
  apply (h.wpDep (fun s₁ s₂ hp => ⟨correct s₁ hp.1, correct s₂ hp.2.1⟩)).mono
    (fun _ _ h => h)
  rintro s₁' s₂' ⟨_, s₁, s₂, hp, h₁, h₂⟩
  refine ⟨h₁.1, h₂.1, fun r hr => ?_⟩
  rw [h₁.2 r hr, h₂.2 r hr]
  exact hp.2.2 r hr

theorem before_ct (d : Spec.Rc2.Direction) :
    RelCT isa VG.Proof.Rc2.X86.Cbc.StepRel (.block (Impl.Rc2.X86.Cbc.before d)) VG.Proof.Rc2.X86.Cbc.StepRel := by
  apply VG.Proof.Rc2.X86.Cbc.kept_ct _ (VG.Proof.Rc2.X86.Cbc.before_ok d)
  cases d <;> apply RelCT.taint (A := taint) (τr VG.Proof.Rc2.X86.Cbc.kept) (fun _ _ h => VG.Proof.Rc2.X86.Cbc.agreeKept h.2.2)
  all_goals taint_decide

def callRd (s : State) : List Region :=
  [⟨addr32 (s.gpr .ebx), 128⟩, ⟨argAddr (pushed [.ebp, .esi, .ebx] s).callEntry 0, 12⟩]
def callWr (s : State) : List Region := [⟨addr32 (s.gpr .esi), 8⟩, ⟨addr32 (s.gpr .ebp), 256⟩]

theorem callPre_ok (d : Spec.Rc2.Direction) (s : State) (hp : VG.Proof.Rc2.X86.Cbc.CallPre s) :
    VG.X86.CallPre (blockContract d) [.ebp, .esi, .ebx] (VG.Proof.Rc2.X86.Cbc.callRd s) (VG.Proof.Rc2.X86.Cbc.callWr s) s := by
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
  unfold VG.Proof.Rc2.X86.Cbc.callRd VG.Proof.Rc2.X86.Cbc.callWr
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
    omega
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

theorem call_ct (d : Spec.Rc2.Direction) : RelCT isa VG.Proof.Rc2.X86.Cbc.StepRel (Impl.Rc2.X86.Cbc.blockCall d) VG.Proof.Rc2.X86.Cbc.StepRel := by
  apply VG.Proof.Rc2.X86.Cbc.kept_ct
  · intro s₁ s₂ t₁ t₂ u₁ u₂ hp e₁ e₂
    have sp := hp.2.2 .esp (by decide)
    have key := hp.2.2 .ebx (by decide)
    have data := hp.2.2 .esi (by decide)
    have buf := hp.2.2 .ebp (by decide)
    have rd : VG.Proof.Rc2.X86.Cbc.callRd s₂ = VG.Proof.Rc2.X86.Cbc.callRd s₁ := by
      simp only [VG.Proof.Rc2.X86.Cbc.callRd, callEntry_argAddr0, key, sp]
    have wr : VG.Proof.Rc2.X86.Cbc.callWr s₂ = VG.Proof.Rc2.X86.Cbc.callWr s₁ := by simp only [VG.Proof.Rc2.X86.Cbc.callWr, data, buf]
    have hc : ConstantTime isa (blockContract d).pre (blockContract d).pub (.block (blockCode d)) := by
      cases d
      · exact encryptBlock_constantTime
      · exact decryptBlock_constantTime
    have ct : RelCT isa (fun a b => a = s₁ ∧ b = s₂) (Impl.Rc2.X86.Cbc.blockCall d) (fun _ _ => True) := by
      rw [VG.Proof.Rc2.X86.Cbc.blockCall_eq]
      apply RelCT.callWith (block_correct d) hc (VG.Proof.Rc2.X86.Cbc.callRd s₁) (VG.Proof.Rc2.X86.Cbc.callWr s₁)
      rintro a b ⟨ha, hb⟩
      subst a b
      refine ⟨VG.Proof.Rc2.X86.Cbc.callPre_ok d s₁ hp.1.call, ?_, sp, ?_⟩
      · rw [← rd, ← wr]; exact VG.Proof.Rc2.X86.Cbc.callPre_ok d s₂ hp.2.1.call
      · constructor
        · simp only [State.withRegions_gpr, callEntry_esp', sp]
        · intro i hi
          simp only [arg_withRegions]
          rw [callEntry_arg (by exact hp.1.stackLo) (by decide) (by simpa using hi),
            callEntry_arg (by exact hp.2.1.stackLo) (by decide) (by simpa using hi)]
          have cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
          rcases cases with rfl | rfl | rfl
          · exact key
          · exact data
          · exact buf
    exact ct _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂
  · intro s hp
    apply WP.mono (VG.Proof.Rc2.X86.Cbc.call_ok d s hp.call)
    intro s' h
    exact ⟨hp.transport h.rd h.wr h.reg, h.reg⟩

theorem after_ct (d : Spec.Rc2.Direction) :
    RelCT isa VG.Proof.Rc2.X86.Cbc.StepRel (.block (Impl.Rc2.X86.Cbc.after d)) (fun _ _ => True) := by
  cases d <;> apply RelCT.taint (A := taint) (τr VG.Proof.Rc2.X86.Cbc.kept) (fun _ _ h => VG.Proof.Rc2.X86.Cbc.agreeKept h.2.2)
  all_goals taint_decide

theorem step_ct (d : Spec.Rc2.Direction) :
    RelCT isa VG.Proof.Rc2.X86.Cbc.StepRel (Impl.Rc2.X86.Cbc.step d) VG.Proof.Rc2.X86.Cbc.StepRel := by
  apply VG.Proof.Rc2.X86.Cbc.kept_ct ((VG.Proof.Rc2.X86.Cbc.before_ct d).seq ((VG.Proof.Rc2.X86.Cbc.call_ct d).seq (VG.Proof.Rc2.X86.Cbc.after_ct d)))
  intro s hp
  apply WP.mono (VG.Proof.Rc2.X86.Cbc.step_ok d s hp)
  intro s' h
  exact ⟨h.toPinned.pre hp, h.reg⟩

theorem body_ct (d : Spec.Rc2.Direction) :
    RelCT isa VG.Proof.Rc2.X86.Cbc.StepRel (Impl.Rc2.X86.Cbc.body d) (fun _ _ => True) := by
  apply (VG.Proof.Rc2.X86.Cbc.step_ct d).seq
  apply RelCT.taint (A := taint) (τr VG.Proof.Rc2.X86.Cbc.kept) (fun _ _ h => VG.Proof.Rc2.X86.Cbc.agreeKept h.2.2)
  taint_decide

end VG.Proof.Rc2.X86.Cbc

end

section

/-! # Constant-time CBC loops -/

namespace VG.Proof.Rc2.X86.Cbc

open VG VG.X86 VG.Impl.Rc2.X86

def LoopRel (n : Nat) (s₁ s₂ : State) : Prop :=
  VG.Proof.Rc2.X86.Cbc.StepPre s₁ n ∧ VG.Proof.Rc2.X86.Cbc.StepPre s₂ n ∧ VG.Proof.Rc2.X86.Cbc.EqKept s₁ s₂ ∧
    s₁.gpr .edi = BitVec.ofNat 32 n ∧ s₂.gpr .edi = BitVec.ofNat 32 n ∧ 1 ≤ n

theorem bodyRel (d : Spec.Rc2.Direction) (n : Nat) :
    RelCT isa (VG.Proof.Rc2.X86.Cbc.LoopRel n) (Impl.Rc2.X86.Cbc.body d) (fun s₁ s₂ =>
      VG.Proof.Rc2.X86.Cbc.EqKept s₁ s₂ ∧ eval .ne s₁ = eval .ne s₂ ∧
        (eval .ne s₁ = some true → ∃ m < n, VG.Proof.Rc2.X86.Cbc.LoopRel m s₁ s₂)) := by
  have ct : RelCT isa (VG.Proof.Rc2.X86.Cbc.LoopRel n) (Impl.Rc2.X86.Cbc.body d) (fun _ _ => True) :=
    (VG.Proof.Rc2.X86.Cbc.body_ct d).mono (fun _ _ h => ⟨h.1.head h.2.2.2.2.2, h.2.1.head h.2.2.2.2.2, h.2.2.1⟩)
      (fun _ _ _ => trivial)
  have correct (s₁ s₂ : State) (h : VG.Proof.Rc2.X86.Cbc.LoopRel n s₁ s₂) :=
    And.intro (VG.Proof.Rc2.X86.Cbc.body_ok d s₁ n h.2.2.2.2.2 (by have := h.1.dataFit; omega) h.2.2.2.1 (h.1.head h.2.2.2.2.2))
      (VG.Proof.Rc2.X86.Cbc.body_ok d s₂ n h.2.2.2.2.2 (by have := h.2.1.dataFit; omega) h.2.2.2.2.1 (h.2.1.head h.2.2.2.2.2))
  apply (ct.wpDep correct).mono (fun _ _ h => h)
  rintro s₁' s₂' ⟨_, s₁, s₂, hp, h₁, h₂⟩
  have eq : VG.Proof.Rc2.X86.Cbc.EqKept s₁' s₂' := by
    intro r hr
    by_cases hptr : r = .esi
    · subst r; rw [h₁.ptr, h₂.ptr, hp.2.2.1 .esi (by decide)]
    · by_cases hcount : r = .edi
      · subst r; rw [h₁.count, h₂.count]
      · rw [h₁.reg r hr hptr hcount, h₂.reg r hr hptr hcount]
        exact hp.2.2.1 r hr
  refine ⟨eq, by rw [VG.Proof.Rc2.X86.Cbc.eval_nonzeroCount, VG.Proof.Rc2.X86.Cbc.eval_nonzeroCount, h₁.flag, h₂.flag], ?_⟩
  intro hcontinue
  have hn : 1 ≤ n := hp.2.2.2.2.2
  have hm : 1 ≤ n - 1 := by
    rw [VG.Proof.Rc2.X86.Cbc.eval_nonzeroCount, h₁.flag] at hcontinue
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
    RelCT isa (VG.Proof.Rc2.X86.Cbc.LoopRel n) (.loop (Impl.Rc2.X86.Cbc.body d) .ne) VG.Proof.Rc2.X86.Cbc.EqKept := by
  refine RelCT.loop (M := isa) (body := Impl.Rc2.X86.Cbc.body d) (c := .ne) (Q := VG.Proof.Rc2.X86.Cbc.EqKept) VG.Proof.Rc2.X86.Cbc.LoopRel ?_ n
  intro m
  exact (VG.Proof.Rc2.X86.Cbc.bodyRel d m).mono (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, fun _ => h.1, h.2.2⟩)

def MaybeRel (s₁ s₂ : State) : Prop :=
  ∃ n, VG.Proof.Rc2.X86.Cbc.StepPre s₁ n ∧ VG.Proof.Rc2.X86.Cbc.StepPre s₂ n ∧ VG.Proof.Rc2.X86.Cbc.EqKept s₁ s₂ ∧
    s₁.gpr .edi = BitVec.ofNat 32 n ∧ s₂.gpr .edi = BitVec.ofNat 32 n ∧
    VG.Proof.Rc2.X86.Cbc.zeroCount s₁ = some (decide (n = 0)) ∧ VG.Proof.Rc2.X86.Cbc.zeroCount s₂ = some (decide (n = 0))

theorem maybeLoop_ct (d : Spec.Rc2.Direction) :
    RelCT isa VG.Proof.Rc2.X86.Cbc.MaybeRel (.ite .e (.block []) (.loop (Impl.Rc2.X86.Cbc.body d) .ne)) VG.Proof.Rc2.X86.Cbc.EqKept := by
  apply RelCT.ite
  · rintro s₁ s₂ ⟨n, _, _, _, _, _, h₁, h₂⟩
    change VG.Proof.Rc2.X86.Cbc.zeroCount s₁ = VG.Proof.Rc2.X86.Cbc.zeroCount s₂
    rw [h₁, h₂]
  · apply RelCT.nil
    rintro s₁ s₂ ⟨⟨n, _, _, eq, _⟩, _⟩
    exact eq
  · apply RelCT.exists_ (fun n => VG.Proof.Rc2.X86.Cbc.loop_ct d n) |>.mono
    · rintro s₁ s₂ ⟨⟨n, h₁, h₂, eq, c₁, c₂, z₁, _⟩, branch⟩
      refine ⟨n, h₁, h₂, eq, c₁, c₂, ?_⟩
      change VG.Proof.Rc2.X86.Cbc.zeroCount s₁ = some false at branch
      rw [z₁] at branch
      have hn : n ≠ 0 := by intro hz; simp [hz] at branch
      omega
    · exact fun _ _ h => h

end VG.Proof.Rc2.X86.Cbc

end

namespace VG.Proof.Rc2.X86.Cbc
open VG VG.X86 VG.Impl.Rc2.X86

def startCode : Prog isa := .seq (.block [.mov .eax (.mem (memOp .esp 20))])
  (.block (Impl.Rc2.X86.Cbc.save ++ Impl.Rc2.X86.Cbc.setup))

structure StartPost (s s' : State) : Prop where
  pre : VG.Proof.Rc2.X86.Cbc.StepPre s' (arg s 3).toNat
  key : s'.gpr .ebx = arg s 0
  iv : s'.gpr .ecx = arg s 1
  data : s'.gpr .esi = arg s 2
  buf : s'.gpr .ebp = arg s 4
  count : s'.gpr .edi = arg s 3
  flag : VG.Proof.Rc2.X86.Cbc.zeroCount s' = some (arg s 3 == 0)
  sp : s'.gpr .esp = s.gpr .esp

theorem start_ok (d : Spec.Rc2.Direction) (s : State) (hs : (VG.Proof.Rc2.X86.Cbc.contract d).pre s) :
    WP isa VG.Proof.Rc2.X86.Cbc.startCode s (VG.Proof.Rc2.X86.Cbc.StartPost s) := by
  obtain ⟨hrd, hwr, keyIv, keyData, keyBuf, ivData, ivBuf, dataBuf,
    ivArgs, dataArgs, bufArgs, retIv, retData, retBuf, stackKey, stackIv, stackData, stackBuf, keyFit, ivFit, bufFit, spFit, stackLo, fit⟩ := hs
  have writes (i : Nat) (hi : i + 4 ≤ 512) : InRegions s.wr (addr32 (arg s 4) + BitVec.ofNat 64 i) 4 := by
    rw [hwr]
    exact ⟨⟨addr32 (arg s 4), 512⟩, by simp, Offset.contains_base _ hi (by omega)⟩
  rw [VG.Proof.Rc2.X86.Cbc.startCode]
  apply WP.seq
  obtain ⟨s₀, run₀, buf₀, keep₀⟩ := loadArg_ok s .eax 4 (by
    rw [hrd, hwr, argAddr_eq s 4 (by omega)]
    exact ⟨⟨argAddr s 0, 20⟩, by simp, argContains s spFit 4 (by decide)⟩)
  refine WP.of_runBlock ⟨s₀, run₀, ?_⟩
  have g₀ (r : Reg) (hr : r ≠ .eax) := keep₀.reg r (by simpa using hr)
  have writes₀ (i : Nat) (hi : i + 4 ≤ 512) :
      InRegions s₀.wr (addr32 (s₀.gpr .eax) + BitVec.ofNat 64 i) 4 := by
    rw [keep₀.wr, buf₀]; exact writes i hi
  rw [WP.block_append_iff]
  obtain ⟨s₁, run₁, keep₁⟩ := VG.Proof.Rc2.X86.Cbc.save_ok s₀ (by rw [buf₀]; exact bufFit)
    (writes₀ 264 (by decide)) (writes₀ 268 (by decide)) (writes₀ 272 (by decide))
    (writes₀ 276 (by decide))
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have g₁ (r : Reg) : s₁.gpr r = s₀.gpr r := keep₁.reg r (by simp)
  have sp₁ : s₁.gpr .esp = s.gpr .esp := (g₁ .esp).trans (g₀ .esp (by decide))
  have saveFrame : Frame [⟨addr32 (arg s 4), 512⟩] s.mem s₁.mem := by
    rw [keep₁.mem, ← keep₀.mem, ← buf₀]; exact VG.Proof.Rc2.X86.Cbc.savedMem_frame s₀
  have args₁ := args_frame saveFrame sp₁ spFit (by simpa using bufArgs)
  have readArgs₁ (i : Nat) (hi : i < 4) : InRegions (s₁.rd ++ s₁.wr) (argAddr s₁ i) 4 := by
    have ptr : argAddr s₁ i = argAddr s i := by unfold argAddr; rw [sp₁]
    rw [keep₁.rd, keep₁.wr, keep₀.rd, keep₀.wr, hrd, hwr, ptr, argAddr_eq s i (by omega)]
    exact ⟨⟨argAddr s 0, 20⟩, by simp, argContains s spFit i (by omega)⟩
  obtain ⟨s₂, run₂, key₂, iv₂, data₂, count₂, buf₂, flag₂, keep₂⟩ := VG.Proof.Rc2.X86.Cbc.setup_ok s₁ readArgs₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  rw [args₁ 0 (by decide)] at key₂
  rw [args₁ 1 (by decide)] at iv₂
  rw [args₁ 2 (by decide)] at data₂
  rw [args₁ 3 (by decide)] at count₂ flag₂
  rw [g₁, buf₀] at buf₂
  have sp₂ := (keep₂.reg .esp (by decide)).trans sp₁
  have rd₂ := keep₂.rd.trans (keep₁.rd.trans keep₀.rd)
  have wr₂ := keep₂.wr.trans (keep₁.wr.trans keep₀.wr)
  have hp₂ : VG.Proof.Rc2.X86.Cbc.StepPre s₂ (arg s 3).toNat := by
    constructor
    · rw [key₂]; exact keyFit
    · rw [iv₂]; exact ivFit
    · rw [data₂]; exact fit
    · rw [buf₂]; exact bufFit
    · simp only [Covers, VG.Proof.Rc2.X86.Cbc.keyR, VG.Proof.Rc2.X86.Cbc.ivR, VG.Proof.Rc2.X86.Cbc.dataR, VG.Proof.Rc2.X86.Cbc.bufR, key₂, iv₂, data₂, buf₂, rd₂, wr₂, hrd, hwr]
      intro a n ⟨r, hr, hc⟩
      exact ⟨r, by simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h | h <;> simp_all only [or_true, true_or], hc⟩
    · simp only [Covers, VG.Proof.Rc2.X86.Cbc.ivR, VG.Proof.Rc2.X86.Cbc.dataR, VG.Proof.Rc2.X86.Cbc.bufR, iv₂, data₂, buf₂, wr₂, hwr]
      intro a n ⟨r, hr, hc⟩
      exact ⟨r, hr, hc⟩
    · simpa only [VG.Proof.Rc2.X86.Cbc.keyR, VG.Proof.Rc2.X86.Cbc.ivR, key₂, iv₂] using keyIv
    · simpa only [VG.Proof.Rc2.X86.Cbc.keyR, VG.Proof.Rc2.X86.Cbc.dataR, key₂, data₂] using keyData
    · simpa only [VG.Proof.Rc2.X86.Cbc.keyR, VG.Proof.Rc2.X86.Cbc.bufR, key₂, buf₂] using keyBuf
    · simpa only [VG.Proof.Rc2.X86.Cbc.ivR, VG.Proof.Rc2.X86.Cbc.dataR, iv₂, data₂] using ivData
    · simpa only [VG.Proof.Rc2.X86.Cbc.ivR, VG.Proof.Rc2.X86.Cbc.bufR, iv₂, buf₂] using ivBuf
    · simpa only [VG.Proof.Rc2.X86.Cbc.dataR, VG.Proof.Rc2.X86.Cbc.bufR, data₂, buf₂] using dataBuf
    · rw [sp₂]; exact stackLo
    · simpa only [VG.Proof.Rc2.X86.Cbc.stackR, VG.Proof.Rc2.X86.Cbc.keyR, sp₂, key₂] using stackKey
    · simpa only [VG.Proof.Rc2.X86.Cbc.stackR, VG.Proof.Rc2.X86.Cbc.ivR, sp₂, iv₂] using stackIv
    · simpa only [VG.Proof.Rc2.X86.Cbc.stackR, VG.Proof.Rc2.X86.Cbc.dataR, sp₂, data₂] using stackData
    · simpa only [VG.Proof.Rc2.X86.Cbc.stackR, VG.Proof.Rc2.X86.Cbc.bufR, sp₂, buf₂] using stackBuf
  exact ⟨hp₂, key₂, iv₂, data₂, buf₂, count₂, flag₂, sp₂⟩

def InitialRel (d : Spec.Rc2.Direction) (s₁ s₂ : State) : Prop :=
  (VG.Proof.Rc2.X86.Cbc.contract d).pre s₁ ∧ (VG.Proof.Rc2.X86.Cbc.contract d).pre s₂ ∧ (VG.Proof.Rc2.X86.Cbc.contract d).pub s₁ s₂

def startTaint : VG.X86.Taint.T := { regs := .ofList [.esp], flags := false, argLen := 24 }

theorem startTaint_wf {d : Spec.Rc2.Direction} {s : State} (h : (VG.Proof.Rc2.X86.Cbc.contract d).pre s) : VG.X86.Taint.Wf VG.Proof.Rc2.X86.Cbc.startTaint s := by
  obtain ⟨_, wr, _, _, _, _, _, _, ai, ad, ab, ri, rd, rb, _, _, _, _, _, _, _, spfit, _⟩ := h
  refine Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨spfit, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim⟩
  simp only [VG.Proof.Rc2.X86.Cbc.startTaint, wr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact Taint.frame_disjoint (n := 20) (by omega) ri ai
  · exact Taint.frame_disjoint (n := 20) (by omega) rd ad
  · exact Taint.frame_disjoint (n := 20) (by omega) rb ab

theorem startTaint_agree {d : Spec.Rc2.Direction} {s₁ s₂ : State} (h : VG.Proof.Rc2.X86.Cbc.InitialRel d s₁ s₂) :
    VG.X86.Taint.Agree VG.Proof.Rc2.X86.Cbc.startTaint s₁ s₂ := by
  obtain ⟨h₁, h₂, sp, args⟩ := h
  have fit : ∀ s, (VG.Proof.Rc2.X86.Cbc.contract d).pre s → (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 := by
    intro s hs
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h, _⟩ := hs
    exact h
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h,
    VG.Proof.Rc2.X86.Cbc.startTaint_wf h₁, VG.Proof.Rc2.X86.Cbc.startTaint_wf h₂, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => sp, fun k h4 hk => ?_⟩
  · simp only [VG.Proof.Rc2.X86.Cbc.startTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r; exact sp
  · simp only [VG.Proof.Rc2.X86.Cbc.startTaint] at hk
    rw [show Taint.depth startTaint.stk = 0 from rfl, Nat.zero_add]
    rw [Taint.argByte_eq (fit _ h₁) h4 hk, Taint.argByte_eq (fit _ h₂) h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)),
      Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (args ((k - 4) / 4) (by omega))

theorem start_ct (d : Spec.Rc2.Direction) : RelCT isa (VG.Proof.Rc2.X86.Cbc.InitialRel d) VG.Proof.Rc2.X86.Cbc.startCode VG.Proof.Rc2.X86.Cbc.MaybeRel := by
  have ct : RelCT isa (VG.Proof.Rc2.X86.Cbc.InitialRel d) VG.Proof.Rc2.X86.Cbc.startCode (fun _ _ => True) := by
    apply RelCT.taint (A := taint) VG.Proof.Rc2.X86.Cbc.startTaint (fun _ _ h => VG.Proof.Rc2.X86.Cbc.startTaint_agree h)
    taint_decide
  apply (ct.wpDep (fun s₁ s₂ h => ⟨VG.Proof.Rc2.X86.Cbc.start_ok d s₁ h.1, VG.Proof.Rc2.X86.Cbc.start_ok d s₂ h.2.1⟩)).mono (fun _ _ h => h)
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
    simp only [VG.Proof.Rc2.X86.Cbc.kept, List.mem_cons, List.not_mem_nil, or_false] at hr
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
    ConstantTime isa (VG.Proof.Rc2.X86.Cbc.contract d).pre (VG.Proof.Rc2.X86.Cbc.contract d).pub (Impl.Rc2.X86.Cbc.cbc d) := by
  apply RelCT.constantTime
  apply RelCT.assoc
  apply (VG.Proof.Rc2.X86.Cbc.start_ct d).seq
  apply (VG.Proof.Rc2.X86.Cbc.maybeLoop_ct d).seq
  apply RelCT.taint (A := taint) (τr [.ebp])
    (fun _ _ h => agree_regs (fun r hr => h r (by have e := List.mem_singleton.mp hr; rw [e]; decide)))
  taint_decide

end VG.Proof.Rc2.X86.Cbc

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.X86.Cbc.Correct`. -/
section

/-! # Verified RC2-CBC encryption and decryption -/

namespace VG.Proof.Rc2.X86.Cbc

open VG VG.X86 VG.Impl.Rc2.X86

theorem cbc_body_correct (d : Spec.Rc2.Direction) (s : State) (hs : (VG.Proof.Rc2.X86.Cbc.contract d).pre s) :
    WP isa (Impl.Rc2.X86.Cbc.cbc d) s (fun s' => abiPreserved s s' ∧ (VG.Proof.Rc2.X86.Cbc.contract d).post s s') := by
  obtain ⟨hrd, hwr, keyIv, keyData, keyBuf, ivData, ivBuf, dataBuf,
    ivArgs, dataArgs, bufArgs, retIv, retData, retBuf, stackKey, stackIv, stackData, stackBuf, keyFit, ivFit, bufFit, spFit, stackLo, fit⟩ := hs
  have writes (i : Nat) (hi : i + 4 ≤ 512) : InRegions s.wr (addr32 (arg s 4) + BitVec.ofNat 64 i) 4 := by
    rw [hwr]
    exact ⟨⟨addr32 (arg s 4), 512⟩, by simp, Offset.contains_base _ hi (by omega)⟩
  rw [Impl.Rc2.X86.Cbc.cbc]
  apply WP.seq
  obtain ⟨s₀, run₀, buf₀, keep₀⟩ := loadArg_ok s .eax 4 (by
    rw [hrd, hwr, argAddr_eq s 4 (by omega)]
    exact ⟨⟨argAddr s 0, 20⟩, by simp, argContains s spFit 4 (by decide)⟩)
  refine WP.of_runBlock ⟨s₀, run₀, ?_⟩
  have g₀ (r : Reg) (hr : r ≠ .eax) := keep₀.reg r (by simpa using hr)
  have writes₀ (i : Nat) (hi : i + 4 ≤ 512) :
      InRegions s₀.wr (addr32 (s₀.gpr .eax) + BitVec.ofNat 64 i) 4 := by
    rw [keep₀.wr, buf₀]; exact writes i hi
  apply WP.seq
  rw [WP.block_append_iff]
  obtain ⟨s₁, run₁, keep₁⟩ := VG.Proof.Rc2.X86.Cbc.save_ok s₀ (by rw [buf₀]; exact bufFit)
    (writes₀ 264 (by decide)) (writes₀ 268 (by decide)) (writes₀ 272 (by decide))
    (writes₀ 276 (by decide))
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have g₁ (r : Reg) : s₁.gpr r = s₀.gpr r := keep₁.reg r (by simp)
  have sp₁ : s₁.gpr .esp = s.gpr .esp := (g₁ .esp).trans (g₀ .esp (by decide))
  have saveFrame : Frame [⟨addr32 (arg s 4), 512⟩] s.mem s₁.mem := by
    rw [keep₁.mem, ← keep₀.mem, ← buf₀]; exact VG.Proof.Rc2.X86.Cbc.savedMem_frame s₀
  have args₁ := args_frame saveFrame sp₁ spFit (by simpa using bufArgs)
  have readArgs₁ (i : Nat) (hi : i < 4) : InRegions (s₁.rd ++ s₁.wr) (argAddr s₁ i) 4 := by
    have ptr : argAddr s₁ i = argAddr s i := by unfold argAddr; rw [sp₁]
    rw [keep₁.rd, keep₁.wr, keep₀.rd, keep₀.wr, hrd, hwr, ptr, argAddr_eq s i (by omega)]
    exact ⟨⟨argAddr s 0, 20⟩, by simp, argContains s spFit i (by omega)⟩
  obtain ⟨s₂, run₂, key₂, iv₂, data₂, count₂, buf₂, flag₂, keep₂⟩ := VG.Proof.Rc2.X86.Cbc.setup_ok s₁ readArgs₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  rw [args₁ 0 (by decide)] at key₂
  rw [args₁ 1 (by decide)] at iv₂
  rw [args₁ 2 (by decide)] at data₂
  rw [args₁ 3 (by decide)] at count₂ flag₂
  rw [g₁, buf₀] at buf₂
  have sp₂ := (keep₂.reg .esp (by decide)).trans sp₁
  have rd₂ := keep₂.rd.trans (keep₁.rd.trans keep₀.rd)
  have wr₂ := keep₂.wr.trans (keep₁.wr.trans keep₀.wr)
  have mem₂ : s₂.mem = VG.Proof.Rc2.X86.Cbc.savedMem s₀ := keep₂.mem.trans keep₁.mem
  have scratchFrame : Frame [⟨addr32 (arg s 4), 512⟩] s.mem s₂.mem := by
    rw [mem₂, ← keep₀.mem, ← buf₀]; exact VG.Proof.Rc2.X86.Cbc.savedMem_frame s₀
  have initialKey := scheduleAt_frame scratchFrame (addr32 (arg s 0)) (by simpa using keyBuf)
  have initialIv := blockAt_frame scratchFrame (addr32 (arg s 1)) (by simpa using ivBuf)
  have initialData := blocksAt_frame scratchFrame (addr32 (arg s 2)) (arg s 3).toNat (by simpa using dataBuf)
  have hp₂ : VG.Proof.Rc2.X86.Cbc.StepPre s₂ (arg s 3).toNat := by
    constructor
    · rw [key₂]; exact keyFit
    · rw [iv₂]; exact ivFit
    · rw [data₂]; exact fit
    · rw [buf₂]; exact bufFit
    · simp only [Covers, VG.Proof.Rc2.X86.Cbc.keyR, VG.Proof.Rc2.X86.Cbc.ivR, VG.Proof.Rc2.X86.Cbc.dataR, VG.Proof.Rc2.X86.Cbc.bufR, key₂, iv₂, data₂, buf₂, rd₂, wr₂, hrd, hwr]
      intro a n ⟨r, hr, hc⟩
      exact ⟨r, by simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h | h <;> simp_all only [or_true, true_or], hc⟩
    · simp only [Covers, VG.Proof.Rc2.X86.Cbc.ivR, VG.Proof.Rc2.X86.Cbc.dataR, VG.Proof.Rc2.X86.Cbc.bufR, iv₂, data₂, buf₂, wr₂, hwr]
      intro a n ⟨r, hr, hc⟩
      exact ⟨r, hr, hc⟩
    · simpa only [VG.Proof.Rc2.X86.Cbc.keyR, VG.Proof.Rc2.X86.Cbc.ivR, key₂, iv₂] using keyIv
    · simpa only [VG.Proof.Rc2.X86.Cbc.keyR, VG.Proof.Rc2.X86.Cbc.dataR, key₂, data₂] using keyData
    · simpa only [VG.Proof.Rc2.X86.Cbc.keyR, VG.Proof.Rc2.X86.Cbc.bufR, key₂, buf₂] using keyBuf
    · simpa only [VG.Proof.Rc2.X86.Cbc.ivR, VG.Proof.Rc2.X86.Cbc.dataR, iv₂, data₂] using ivData
    · simpa only [VG.Proof.Rc2.X86.Cbc.ivR, VG.Proof.Rc2.X86.Cbc.bufR, iv₂, buf₂] using ivBuf
    · simpa only [VG.Proof.Rc2.X86.Cbc.dataR, VG.Proof.Rc2.X86.Cbc.bufR, data₂, buf₂] using dataBuf
    · rw [sp₂]; exact stackLo
    · simpa only [VG.Proof.Rc2.X86.Cbc.stackR, VG.Proof.Rc2.X86.Cbc.keyR, sp₂, key₂] using stackKey
    · simpa only [VG.Proof.Rc2.X86.Cbc.stackR, VG.Proof.Rc2.X86.Cbc.ivR, sp₂, iv₂] using stackIv
    · simpa only [VG.Proof.Rc2.X86.Cbc.stackR, VG.Proof.Rc2.X86.Cbc.dataR, sp₂, data₂] using stackData
    · simpa only [VG.Proof.Rc2.X86.Cbc.stackR, VG.Proof.Rc2.X86.Cbc.bufR, sp₂, buf₂] using stackBuf
  apply WP.seq
  apply WP.mono (VG.Proof.Rc2.X86.Cbc.maybeLoop_ok d s₂ (arg s 3).toNat (by omega) hp₂
    (by simpa using count₂) (by rw [count₂]; exact flag₂))
  intro s₃ h₃
  have rd₃ := h₃.rd.trans rd₂
  have wr₃ := h₃.wr.trans wr₂
  have buf₃ := (h₃.reg .ebp (by decide) (by decide) (by decide)).trans buf₂
  have reads (i : Nat) (hi : i + 4 ≤ 512) :
      InRegions (s₃.rd ++ s₃.wr) (addr32 (s₃.gpr .ebp) + BitVec.ofNat 64 i) 4 := by
    rw [rd₃, wr₃, buf₃]
    obtain ⟨r, hr, hc⟩ := writes i hi
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have v0 : s₃.mem.readW (addr32 (s₃.gpr .ebp) + BitVec.ofNat 64 264) 32 = s.gpr .ebp := by
    have h := h₃.scratchRead hp₂ 264 (by decide) (by decide)
    rw [buf₂, mem₂, ← buf₀, VG.Proof.Rc2.X86.Cbc.savedMem_ebp, g₀ .ebp (by decide)] at h
    rw [buf₀] at h
    rw [buf₃]; exact h
  have v1 : s₃.mem.readW (addr32 (s₃.gpr .ebp) + BitVec.ofNat 64 268) 32 = s.gpr .ebx := by
    have h := h₃.scratchRead hp₂ 268 (by decide) (by decide)
    rw [buf₂, mem₂, ← buf₀, VG.Proof.Rc2.X86.Cbc.savedMem_ebx, g₀ .ebx (by decide)] at h
    rw [buf₀] at h
    rw [buf₃]; exact h
  have v2 : s₃.mem.readW (addr32 (s₃.gpr .ebp) + BitVec.ofNat 64 272) 32 = s.gpr .esi := by
    have h := h₃.scratchRead hp₂ 272 (by decide) (by decide)
    rw [buf₂, mem₂, ← buf₀, VG.Proof.Rc2.X86.Cbc.savedMem_esi, g₀ .esi (by decide)] at h
    rw [buf₀] at h
    rw [buf₃]; exact h
  have v3 : s₃.mem.readW (addr32 (s₃.gpr .ebp) + BitVec.ofNat 64 276) 32 = s.gpr .edi := by
    have h := h₃.scratchRead hp₂ 276 (by decide) (by decide)
    rw [buf₂, mem₂, ← buf₀, VG.Proof.Rc2.X86.Cbc.savedMem_edi, g₀ .edi (by decide)] at h
    rw [buf₀] at h
    rw [buf₃]; exact h
  obtain ⟨s₄, run₄, saved₄, keep₄⟩ := VG.Proof.Rc2.X86.Cbc.restore_ok s₃ s.gpr (by rw [buf₃]; exact bufFit)
    (reads 264 (by decide)) v0    (reads 268 (by decide)) v1    (reads 272 (by decide)) v2    (reads 276 (by decide)) v3
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  constructor
  · constructor
    · intro r hr
      by_cases saved : r ∈ VG.Proof.Rc2.X86.Cbc.callerSaved
      · exact saved₄ r saved
      · have eqSp : r = .esp := by cases r <;> simp_all [calleeSaved, VG.Proof.Rc2.X86.Cbc.callerSaved]
        subst r
        rw [keep₄.reg .esp (by decide), h₃.reg .esp (by decide) (by decide) (by decide), sp₂]
    · have stackRet : (Region.mk (addr32 (s.gpr .esp)) 4).Disjoint (below (s.gpr .esp) 16) := by
        change (Region.mk (addr32 (s.gpr .esp)) 4).Disjoint ⟨_, 16⟩
        rw [Taint.sub_setWidth stackLo]
        exact Offset.base_disjoint_below _ (by decide)
      have frameLoop := h₃.mem
      have retSep : ∀ r ∈ VG.Proof.Rc2.X86.Cbc.loopWrites s₂ (arg s 3).toNat, (Region.mk (addr32 (s.gpr .esp)) 4).Disjoint r := by
        simpa only [VG.Proof.Rc2.X86.Cbc.loopWrites, VG.Proof.Rc2.X86.Cbc.ivR, VG.Proof.Rc2.X86.Cbc.dataR, VG.Proof.Rc2.X86.Cbc.stackR, iv₂, data₂, buf₂, sp₂,
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

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.X86.Cbc.Verified`. -/
section

namespace VG.Proof.Rc2.X86.Cbc
open VG VG.X86

def wideContract (d : Spec.Rc2.Direction) : Contract isa :=
  { VG.Proof.Rc2.X86.Cbc.contract d with
    pre := fun s =>
    let key : Region := ⟨addr32 (arg s 0), 128⟩
    let iv : Region := ⟨addr32 (arg s 1), 8⟩
    let data : Region := ⟨addr32 (arg s 2), 8 * (arg s 3).toNat⟩
    let buf : Region := ⟨addr32 (arg s 4), 512⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨addr32 (s.gpr .esp), 4⟩
    let stack := below (s.gpr .esp) 16
    s.rd = [key] ∧ s.wr = [iv, data, buf, args] ∧ key.Disjoint iv ∧ key.Disjoint data ∧ key.Disjoint buf ∧
      iv.Disjoint data ∧ iv.Disjoint buf ∧ data.Disjoint buf ∧
      args.Disjoint iv ∧ args.Disjoint data ∧ args.Disjoint buf ∧
      ret.Disjoint iv ∧ ret.Disjoint data ∧ ret.Disjoint buf ∧
      stack.Disjoint key ∧ stack.Disjoint iv ∧ stack.Disjoint data ∧ stack.Disjoint buf ∧
      (arg s 0).toNat + 128 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 8 ≤ 2 ^ 32 ∧
      (arg s 4).toNat + 512 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 ∧
      16 ≤ (s.gpr .esp).toNat ∧ (arg s 2).toNat + 8 * (arg s 3).toNat ≤ 2 ^ 32 }

def narrowRd (s : State) : List Region :=
  [⟨addr32 (arg s 0), 128⟩, ⟨argAddr s 0, 20⟩]
def narrowWr (s : State) : List Region :=
  [⟨addr32 (arg s 1), 8⟩, ⟨addr32 (arg s 2), 8 * (arg s 3).toNat⟩, ⟨addr32 (arg s 4), 512⟩]

local macro "narrow" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [VG.Proof.Rc2.X86.Cbc.contract, VG.Proof.Rc2.X86.Cbc.wideContract,
    VG.Proof.Rc2.X86.Cbc.narrowRd, VG.Proof.Rc2.X86.Cbc.narrowWr, VG.X86.arg_withRegions,
    VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem,
    VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr] $(loc)?)

theorem wide_pre (d : Spec.Rc2.Direction) (s : State) (h : (VG.Proof.Rc2.X86.Cbc.wideContract d).pre s) :
    (VG.Proof.Rc2.X86.Cbc.contract d).pre (s.withRegions (VG.Proof.Rc2.X86.Cbc.narrowRd s) (VG.Proof.Rc2.X86.Cbc.narrowWr s)) := by
  obtain ⟨_, _, h⟩ := h
  narrow
  exact ⟨trivial, trivial, h⟩

def satState : State where
  gpr r := if r = .esp then 0x6000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x6005 then 0x10 else if a = 0x6009 then 0x20 else if a = 0x600d then 0x30 else if a = 0x6015 then 0x40 else 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0x4000, 512⟩, ⟨0x6004, 20⟩]

theorem wide_implies (d : Spec.Rc2.Direction) :
    (VG.Proof.Rc2.X86.Cbc.wideContract d).Implies (Spec.Rc2.cbcContract abi d 16) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Spec.Rc2.cbcContract, Spec.Rc2.cbcSig, abi, argSlots, argVal, argBytes, addr32, VG.Proof.Rc2.X86.Cbc.wideContract, VG.Proof.Rc2.X86.Cbc.contract, below] at h
    sig_split h
    sig_reduce [Spec.Rc2.cbcContract, Spec.Rc2.cbcSig, abi, argSlots, argVal, argBytes, addr32, VG.Proof.Rc2.X86.Cbc.wideContract, VG.Proof.Rc2.X86.Cbc.contract, below]
    sig_simp [Spec.Rc2.cbcContract, Spec.Rc2.cbcSig, abi, argSlots, argVal, argBytes, addr32, VG.Proof.Rc2.X86.Cbc.wideContract, VG.Proof.Rc2.X86.Cbc.contract, below] []
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
      | (rw [Taint.sub_setWidth (by omega)]; simp only [Nat.mul_comm] at *; with_reducible assumption)
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Spec.Rc2.cbcContract, Spec.Rc2.cbcSig, abi, argSlots, argVal, argBytes, addr32, VG.Proof.Rc2.X86.Cbc.wideContract, VG.Proof.Rc2.X86.Cbc.contract, below]
  · sig_implies_pub [Spec.Rc2.cbcContract, Spec.Rc2.cbcSig, abi, argSlots, argVal, argBytes, addr32, VG.Proof.Rc2.X86.Cbc.wideContract, VG.Proof.Rc2.X86.Cbc.contract, below]
  · sig_implies_sat [Spec.Rc2.cbcContract, Spec.Rc2.cbcSig, abi, argSlots, argVal, argBytes, addr32, VG.Proof.Rc2.X86.Cbc.wideContract, VG.Proof.Rc2.X86.Cbc.contract, below]
      [satState, arg, argAddr, Mem.readW, Mem.read] using VG.Proof.Rc2.X86.Cbc.satState

theorem cbc_verified (d : Spec.Rc2.Direction) :
    Verified target (Impl.Rc2.X86.Cbc.cbc d) (Spec.Rc2.cbcContract abi d 16) := by
  have hsat := (VG.Proof.Rc2.X86.Cbc.wide_implies d).sat_left
  have narrowSat : ∃ s, (VG.Proof.Rc2.X86.Cbc.contract d).pre s := by
    obtain ⟨s, hs⟩ := hsat
    exact ⟨_, VG.Proof.Rc2.X86.Cbc.wide_pre d s hs⟩
  apply Verified.of_implies _ (VG.Proof.Rc2.X86.Cbc.wide_implies d)
  refine Verified.narrowTo
    (Verified.of_correct (VG.Proof.Rc2.X86.Cbc.cbc_body_correct d) (VG.Proof.Rc2.X86.Cbc.cbc_constantTime d) (.refl narrowSat))
    VG.Proof.Rc2.X86.Cbc.narrowRd VG.Proof.Rc2.X86.Cbc.narrowWr (VG.Proof.Rc2.X86.Cbc.wide_pre d) ?_ ?_ ?_ ?_ hsat
  · intro s h
    obtain ⟨rd, wr, _⟩ := h
    rw [rd, wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [VG.Proof.Rc2.X86.Cbc.narrowRd, VG.Proof.Rc2.X86.Cbc.narrowWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h | h | h <;> simp_all only [or_true, true_or]
  · intro s h
    obtain ⟨_, wr, _⟩ := h
    rw [wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [VG.Proof.Rc2.X86.Cbc.narrowWr, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h <;> simp_all only [or_true, true_or]
  · intro s s' _ h
    narrow at h ⊢
    exact h
  · intro s₁ s₂ _ _ h
    narrow
    exact h

theorem encrypt_verified : Verified target Impl.Rc2.X86.Cbc.encrypt (Spec.Rc2.cbcEncryptContract abi 16) := VG.Proof.Rc2.X86.Cbc.cbc_verified .encrypt
theorem decrypt_verified : Verified target Impl.Rc2.X86.Cbc.decrypt (Spec.Rc2.cbcDecryptContract abi 16) := VG.Proof.Rc2.X86.Cbc.cbc_verified .decrypt

end VG.Proof.Rc2.X86.Cbc

end
