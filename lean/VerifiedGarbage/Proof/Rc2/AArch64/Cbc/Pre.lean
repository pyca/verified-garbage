module
import VerifiedGarbage.Proof.Rc2.AArch64.BlockIO
public import VerifiedGarbage.Proof.Framework.AArch64.Spill
public import VerifiedGarbage.Proof.Rc2.AArch64.ConstantTime
public import VerifiedGarbage.Proof.Framework.AArch64.Inline
public import VerifiedGarbage.Spec.Rc2.Contract
public import VerifiedGarbage.Proof.Rc2.Contract
public import VerifiedGarbage.Proof.Rc2.AArch64.Cipher
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Rc2.AArch64.Lit
public import VerifiedGarbage.Impl.Rc2.AArch64.Cbc
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! ### `Rc2.AArch64.Cbc.Call`, which only this module used -/

section

/-! ### `Rc2.AArch64.Block`, which only this module used -/

section

/-! # Verified RC2 block encryption and decryption -/

@[expose] public section

namespace VG.Proof.Rc2.AArch64

open VG VG.AArch64 VG.Impl.Rc2.AArch64

def cipher (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (b : Spec.Rc2.Block) : Spec.Rc2.Block :=
  match d with
  | .encrypt => Spec.Rc2.encryptBlock k b
  | .decrypt => Spec.Rc2.decryptBlock k b

def blockContract (d : Spec.Rc2.Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, 128⟩
    let data : Region := ⟨s.gpr .x1, 8⟩
    let scratch : Region := ⟨s.gpr .x2, 256⟩
    s.rd = [key] ∧ s.wr = [data, scratch] ∧ key.Disjoint scratch ∧ data.Disjoint scratch
  post s s' := Spec.Rc2.blockAt s'.mem (s.gpr .x1) =
    cipher d (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) (Spec.Rc2.blockAt s.mem (s.gpr .x1))
  pub := PublicRegs [.x0, .x1, .x2]

theorem cipher_rounds (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (b : Spec.Rc2.Block) :
    cipher d k b = Spec.Rc2.encodeBlock
      ((List.range 16).foldl (fun v j => roundSpec d k j v) (Spec.Rc2.decodeBlock b)) := by
  cases d <;> rfl

theorem save_eq : blockSave = Spill.saveCode .x2 (Spill.slots wordReg 4) := by decide +kernel

theorem restore_eq : blockRestore = Spill.restoreCode .x2 (Spill.slots wordReg 4) := by decide +kernel

theorem block_correct (d : Spec.Rc2.Direction) (s : State) (hs : (blockContract d).pre s) :
    WP isa (.block (blockCode d)) s (fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ (blockContract d).post s s') := by
  obtain ⟨hrd, hwr, keySep, dataSep⟩ := hs
  have writes : ∀ i < 4, InRegions s.wr (s.gpr .x2 + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi
    rw [hwr]
    exact ⟨⟨s.gpr .x2, 256⟩, by simp, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  simp only [blockCode, List.append_assoc]
  rw [WP.block_append_iff, save_eq]
  apply WP.mono (Spill.save_wp (by decide) (Spill.forall_slots writes))
  intro s₁ h₁
  have scratchFrame : Frame [⟨s.gpr .x2, 256⟩] s.mem s₁.mem := by
    rw [h₁.mem]
    exact Spill.saveMem_frame_base (by decide) (by decide) _ _ _
  have input₁ : Spec.Rc2.blockAt s₁.mem (s₁.gpr .x1) = Spec.Rc2.blockAt s.mem (s.gpr .x1) := by
    rw [h₁.gpr]
    exact blockAt_frame scratchFrame _ (by simpa using dataSep)
  have schedule₁ : Spec.Rc2.scheduleAt s₁.mem (s₁.gpr .x0) =
      Spec.Rc2.scheduleAt s.mem (s.gpr .x0) := by
    rw [h₁.gpr]
    exact scheduleAt_frame scratchFrame _ (by simpa using keySep)
  have dataRead₁ : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .x1) 8 := by
    rw [h₁.gpr, h₁.rd, h₁.wr, hrd, hwr]
    exact ⟨⟨s.gpr .x1, 8⟩, by simp, Region.contains_self _ _⟩
  rw [WP.block_append_iff]
  apply WP.mono (blockLoad_ok s₁ dataRead₁)
  intro s₂ h₂
  have read₂ : InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .x0) 128 := by
    rw [h₂.2.rd, h₂.2.wr, h₂.2.reg .x0 (by decide), h₁.gpr, h₁.rd, h₁.wr, hrd, hwr]
    exact ⟨⟨s.gpr .x0, 128⟩, by simp, Region.contains_self _ _⟩
  rw [WP.block_append_iff]
  apply WP.mono (rounds_ok d s₂ _ h₂.1 read₂)
  intro s₃ h₃
  have keep₂₃ := h₂.2.trans (h₃.2.weaken (fun _ hr => List.mem_cons_of_mem _ hr))
  have ptr₃ : s₃.gpr .x1 = s.gpr .x1 := (keep₂₃.reg .x1 (by decide)).trans (congrFun h₁.gpr .x1)
  have writable₃ : InRegions s₃.wr (s₃.gpr .x1) 8 := by
    rw [keep₂₃.wr, h₁.wr, hwr, ptr₃]
    exact ⟨⟨s.gpr .x1, 8⟩, by simp, Region.contains_self _ _⟩
  let v := (List.range 16).foldl (fun v j => roundSpec d
    (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) j v) (Spec.Rc2.decodeBlock (Spec.Rc2.blockAt s.mem (s.gpr .x1)))
  have words₃ : Words s₃ v := by
    rw [h₂.2.mem, h₂.2.reg .x0 (by decide), schedule₁, input₁] at h₃
    exact h₃.1
  rw [WP.block_append_iff]
  apply WP.mono (blockStore_ok s₃ v words₃ writable₃)
  intro s₄ h₄
  have mem₄ : s₄.mem = s₁.mem.writeW (s.gpr .x1) (pack v) := by rw [h₄.1, keep₂₃.mem, ptr₃]
  have rd₄ : s₄.rd = s.rd := h₄.2.2.1.trans (keep₂₃.rd.trans h₁.rd)
  have wr₄ : s₄.wr = s.wr := h₄.2.2.2.trans (keep₂₃.wr.trans h₁.wr)
  have regs₄ (r : Reg) (hr : r ∉ .x9 :: roundWrites) : s₄.gpr r = s.gpr r := by
    rw [h₄.2.1 r (by
      intro hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with he | he <;> subst r <;> exact hr (by decide)), keep₂₃.reg r hr, h₁.gpr]
  have scratchRead₄ : ∀ i ∈ List.range 4,
      InRegions (s₄.rd ++ s₄.wr) (s₄.gpr .x2 + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi
    rw [rd₄, wr₄, regs₄ .x2 (by decide), hrd, hwr]
    have bound := List.mem_range.mp hi
    exact ⟨⟨s.gpr .x2, 256⟩, by simp, Offset.contains_base _ (by omega_using [bound]) (by omega_using [bound])⟩
  have saved₄ : ∀ i ∈ List.range 4,
      s₄.mem.readW (s₄.gpr .x2 + BitVec.ofNat 64 (8 * i)) 64 = s.gpr (wordReg i) := by
    intro i hi
    have bound := List.mem_range.mp hi
    rw [mem₄, regs₄ .x2 (by decide), Mem.readW_writeW_sep
      (dataSep.symm.sep (Offset.contains_base _ (by omega_using [bound]) (by omega_using [bound])) (Region.contains_self _ _))
      (by decide), h₁.mem]
    exact Spill.saveMem_saved (l := Spill.slots wordReg 4) (by decide) s.mem (s.gpr .x2) s.gpr
      (wordReg i, 8 * i) (Spill.mem_slots bound)
  rw [restore_eq]
  apply WP.mono (Spill.restore_wp rfl (by decide) (by decide)
    (Spill.forall_slots fun i hi => scratchRead₄ i (List.mem_range.mpr hi))
    (Spill.forall_slots fun i hi => saved₄ i (List.mem_range.mpr hi)))
  intro s₅ h₅
  have finalMem : s₅.mem = s₁.mem.writeW (s.gpr .x1) (pack v) := h₅.mem.trans mem₄
  constructor
  · intro r hr
    by_cases hm : r ∈ (List.range 4).map wordReg
    · exact h₅.gpr_of (.inl (by rwa [Spill.slots_fst]))
    · rw [h₅.other _ (by rwa [Spill.slots_fst])]
      have covered : ∀ r ∈ preserved,
          r ∈ (List.range 4).map wordReg ∨ r ∉ .x9 :: roundWrites := by decide
      exact regs₄ r ((covered r hr).resolve_left hm)
  · change Spec.Rc2.blockAt s₅.mem (s.gpr .x1) = _
    rw [finalMem, blockAt_write64, cipher_rounds]

theorem encrypt_correct (s : State) (hs : (blockContract .encrypt).pre s) :
    ∃ t s', Exec isa encryptBlock s t s' ∧ abiPreserved s s' ∧
      (blockContract .encrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := block_correct .encrypt s hs
  change Exec isa encryptBlock s t s' at he
  exact ⟨t, s', he, ⟨ha, (VG.AArch64.Exec.regions he rfl).2.2.1, VG.AArch64.Exec.preservedV he (by lit_decide)⟩, hp⟩

theorem decrypt_correct (s : State) (hs : (blockContract .decrypt).pre s) :
    ∃ t s', Exec isa decryptBlock s t s' ∧ abiPreserved s s' ∧
      (blockContract .decrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := block_correct .decrypt s hs
  change Exec isa decryptBlock s t s' at he
  exact ⟨t, s', he, ⟨ha, (VG.AArch64.Exec.regions he rfl).2.2.1, VG.AArch64.Exec.preservedV he (by lit_decide)⟩, hp⟩

end VG.Proof.Rc2.AArch64

end

end


/-! # Calling the verified block primitive from CBC -/

@[expose] public section

namespace VG.Proof.Rc2.AArch64.Cbc

open VG VG.AArch64 VG.Impl.Rc2.AArch64

def savedAcrossCall : List Reg := [.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28]

def kept : List Reg := [.x0, .x1, .x2, .x23, .x24]

theorem block_keeps (d : Spec.Rc2.Direction) :
    ((instrs (.block (blockCode d) : Prog isa)).all fun i => kept.all fun r => decide (clobbers i r = false)) = true := by
  cases d
  · change ((instrs encryptBlock).all _) = true
    rw [← Code.allInstrs_eq]; lit_decide
  · change ((instrs decryptBlock).all _) = true
    rw [← Code.allInstrs_eq]; lit_decide

theorem block_keeps_reg (d : Spec.Rc2.Direction) {r : Reg} (hr : r ∈ kept) :
    ∀ i ∈ instrs (.block (blockCode d) : Prog isa), clobbers i r = false := by
  intro i hi
  have h := List.all_eq_true.mp (List.all_eq_true.mp (block_keeps d) i hi) r hr
  simpa using h

theorem block_correct' (d : Spec.Rc2.Direction) (s : State) (hs : (blockContract d).pre s) :
    ∃ t s', Exec isa (.block (blockCode d)) s t s' ∧ abiPreserved s s' ∧ (blockContract d).post s s' := by
  cases d
  · exact encrypt_correct s hs
  · exact decrypt_correct s hs

theorem blockCall_eq (d : Spec.Rc2.Direction) : Impl.Rc2.AArch64.Cbc.blockCall d =
    .call (match d with | .encrypt => "vg_rc2_encrypt_block" | .decrypt => "vg_rc2_decrypt_block")
      (.block (blockCode d)) := by cases d <;> rfl

structure CallPre (s : State) : Prop where
  reads : Covers [⟨s.gpr .x0, 128⟩, ⟨s.gpr .x1, 8⟩, ⟨s.gpr .x2, 256⟩] (s.rd ++ s.wr)
  writes : Covers [⟨s.gpr .x1, 8⟩, ⟨s.gpr .x2, 256⟩] s.wr
  keyScratch : (Region.mk (s.gpr .x0) 128).Disjoint ⟨s.gpr .x2, 256⟩
  dataScratch : (Region.mk (s.gpr .x1) 8).Disjoint ⟨s.gpr .x2, 256⟩

structure CallPost (d : Spec.Rc2.Direction) (s s' : State) : Prop where
  reg : ∀ r ∈ kept, s'.gpr r = s.gpr r
  callee : ∀ r ∈ savedAcrossCall, s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame [⟨s.gpr .x1, 8⟩, ⟨s.gpr .x2, 256⟩] s.mem s'.mem
  output : Spec.Rc2.blockAt s'.mem (s.gpr .x1) =
    cipher d (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) (Spec.Rc2.blockAt s.mem (s.gpr .x1))

theorem call_ok (d : Spec.Rc2.Direction) (s : State) (hp : CallPre s) :
    WP isa (Impl.Rc2.AArch64.Cbc.blockCall d) s (CallPost d s) := by
  rw [blockCall_eq]
  refine WP.call (k := blockContract d) (block_correct' d)
    (rd := [⟨s.gpr .x0, 128⟩]) (wr := [⟨s.gpr .x1, 8⟩, ⟨s.gpr .x2, 256⟩]) ?_ hp.reads hp.writes ?_ (by rfl)
  · simp only [blockContract, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs)]
    exact ⟨trivial, trivial, hp.keyScratch, hp.dataScratch⟩
  · intro s' rd wr sp frame callee regs out
    have sep : ∀ r ∈ kept, r ∉ linkRegs := by decide
    have saved : ∀ r ∈ savedAcrossCall, r ∈ preserved ∧ r ≠ .x30 := by decide
    refine ⟨fun r hr => regs r (sep r hr) (block_keeps_reg d hr),
      fun r hr => callee r (saved r hr).1 (saved r hr).2, rd, wr, frame, ?_⟩
    change Spec.Rc2.blockAt s'.mem _ = cipher d _ _ at out
    simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
      State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs)] at out
    exact out

end VG.Proof.Rc2.AArch64.Cbc

end

end


/-! # Permissions and separation for one CBC step -/

@[expose] public section

namespace VG.Proof.Rc2.AArch64.Cbc

open VG VG.AArch64

abbrev keyR (s : State) : Region := ⟨s.gpr .x0, 128⟩
abbrev ivR (s : State) : Region := ⟨s.gpr .x23, 8⟩
abbrev dataR (s : State) (n : Nat := 1) : Region := ⟨s.gpr .x1, 8 * n⟩
abbrev bufR (s : State) : Region := ⟨s.gpr .x2, 512⟩

structure StepPre (s : State) (n : Nat := 1) : Prop where
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
  have a := regs .x0 (by decide)
  have b := regs .x23 (by decide)
  have c := regs .x1 (by decide)
  have d := regs .x2 (by decide)
  constructor
  · simpa only [keyR, ivR, dataR, bufR, rd, wr, a, b, c, d] using hp.reads
  · simpa only [keyR, ivR, dataR, bufR, rd, wr, a, b, c, d] using hp.writes
  · simpa only [keyR, ivR, dataR, bufR, rd, wr, a, b, c, d] using hp.keyIv
  · simpa only [keyR, ivR, dataR, bufR, rd, wr, a, b, c, d] using hp.keyData
  · simpa only [keyR, ivR, dataR, bufR, rd, wr, a, b, c, d] using hp.keyBuf
  · simpa only [keyR, ivR, dataR, bufR, rd, wr, a, b, c, d] using hp.ivData
  · simpa only [keyR, ivR, dataR, bufR, rd, wr, a, b, c, d] using hp.ivBuf
  · simpa only [keyR, ivR, dataR, bufR, rd, wr, a, b, c, d] using hp.dataBuf

theorem StepPre.call {s : State} (hp : StepPre s) : CallPre s := by
  constructor
  · have hc : Covers [⟨s.gpr .x0, 128⟩, ⟨s.gpr .x1, 8⟩, ⟨s.gpr .x2, 256⟩]
        [keyR s, ivR s, dataR s, bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨keyR s, by simp, 0, by simp, by simp⟩
      · exact ⟨dataR s, by simp, 0, by simp, by simp⟩
      · exact ⟨bufR s, by simp, 0, by simp, by simp⟩
    exact fun a n h => hp.reads a n (hc a n h)
  · have hc : Covers [⟨s.gpr .x1, 8⟩, ⟨s.gpr .x2, 256⟩] [ivR s, dataR s, bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨dataR s, by simp, 0, by simp, by simp⟩
      · exact ⟨bufR s, by simp, 0, by simp, by simp⟩
    exact fun a n h => hp.writes a n (hc a n h)
  · exact hp.keyBuf.sub_right (Region.sub_prefix (by decide))
  · exact hp.dataBuf.sub_right (Region.sub_prefix (by decide))

theorem StepPre.readData {s : State} (hp : StepPre s) : InRegions (s.rd ++ s.wr) (s.gpr .x1) 8 :=
  hp.reads _ _ ⟨dataR s, by simp, Region.contains_self _ _⟩

theorem StepPre.readIv {s : State} (hp : StepPre s) : InRegions (s.rd ++ s.wr) (s.gpr .x23) 8 :=
  hp.reads _ _ ⟨ivR s, by simp, Region.contains_self _ _⟩

theorem StepPre.writeData {s : State} (hp : StepPre s) : InRegions s.wr (s.gpr .x1) 8 :=
  hp.writes _ _ ⟨dataR s, by simp, Region.contains_self _ _⟩

theorem StepPre.writeIv {s : State} (hp : StepPre s) : InRegions s.wr (s.gpr .x23) 8 :=
  hp.writes _ _ ⟨ivR s, by simp, Region.contains_self _ _⟩

theorem StepPre.readBuf {s : State} (hp : StepPre s) (i : Nat) (hi : i + 8 ≤ 512) :
    InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 i) 8 :=
  hp.reads _ _ ⟨bufR s, by simp, Offset.contains_base _ hi (by omega_using [hi])⟩

theorem StepPre.writeBuf {s : State} (hp : StepPre s) (i : Nat) (hi : i + 8 ≤ 512) :
    InRegions s.wr (s.gpr .x2 + BitVec.ofNat 64 i) 8 :=
  hp.writes _ _ ⟨bufR s, by simp, Offset.contains_base _ hi (by omega_using [hi])⟩

end VG.Proof.Rc2.AArch64.Cbc
