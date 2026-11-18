module

import VerifiedGarbage.Proof.Framework.AArch64.Inline
public import VerifiedGarbage.Proof.Rc2.AArch64.ConstantTime
public import VerifiedGarbage.Spec.Rc2.Contract
public import VerifiedGarbage.Proof.Rc2.Contract
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Rc2.AArch64.Lit
public import VerifiedGarbage.Proof.Framework.AArch64.Spill
public import VerifiedGarbage.Impl.Rc2.AArch64.ExpandKey
public import VerifiedGarbage.Proof.Rc2.AArch64.Lookup
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Rc2.AArch64.KeyLoop
public import VerifiedGarbage.Proof.Rc2.Expansion
import VerifiedGarbage.Proof.Rc2.AArch64.KeySetup
import VerifiedGarbage.Proof.Rc2.AArch64.Mask
import VerifiedGarbage.Proof.Rc2.AArch64.DescendKey
import VerifiedGarbage.Proof.Framework.Omega

/-! ### `Rc2.AArch64.KeyBody`, which only this module used -/

section

/-! ### `Rc2.AArch64.CopyKey`, which only this module used -/

section

/-! # The key-copy loop -/

@[expose] public section

namespace VG.Proof.Rc2.AArch64

open VG VG.AArch64 VG.Impl.Rc2.AArch64

theorem copyLoop_ok (s : State) (t : Nat) (ht : 1 ≤ t) (ht' : t ≤ 128)
    (len : s.gpr .x20 = BitVec.ofNat 64 t) (zero : s.gpr .x23 = 0)
    (readable : ∀ i < t, InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 i) 1)
    (writable : ∀ i < 128, InRegions s.wr (s.gpr .x21 + BitVec.ofNat 64 i) 1)
    (sep : (Region.mk (s.gpr .x19) t).Disjoint ⟨s.gpr .x21, 128⟩) :
    WP isa (.loop (.block copyKey) (.nonzero .x .x10)) s (fun s' =>
      s'.gpr .x23 = BitVec.ofNat 64 t ∧ KeyFrame s s' ∧
      BytesPrefix s'.mem (s.gpr .x21) (fill (Spec.Rc2.bytesAt s.mem (s.gpr .x19) t) 0) t) := by
  let key := Spec.Rc2.bytesAt s.mem (s.gpr .x19) t
  let I (i : Nat) (s' : State) := s'.gpr .x23 = BitVec.ofNat 64 i ∧ KeyFrame s s' ∧
    BytesPrefix s'.mem (s.gpr .x21) (fill key 0) i
  apply forwardLoop (.block copyKey) I t _ 0 (by omega_using [ht]) s
    ⟨zero, KeyFrame.refl s, fun i hi => by omega⟩
  intro i hi s₁ ⟨index₁, frame₁, prefix₁⟩
  have keyPtr := frame₁.reg .x19 (by decide)
  have outPtr := frame₁.reg .x21 (by decide)
  have len₁ := (frame₁.reg .x20 (by decide)).trans len
  have read₁ : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .x19 + s₁.gpr .x23) 1 := by
    rw [frame₁.rd, frame₁.wr, keyPtr, index₁]
    exact readable i hi
  have write₁ : InRegions s₁.wr (s₁.gpr .x21 + s₁.gpr .x23) 1 := by
    rw [frame₁.wr, outPtr, index₁]
    exact writable i (by omega_using [ht', hi])
  have byte₁ : s₁.mem (s₁.gpr .x19 + s₁.gpr .x23) = key.getD i 0 := by
    rw [keyPtr, index₁, bytesAt_getD _ _ _ _ hi]
    exact frame₁.mem.bytes (by simpa using sep) (by change t ≤ 2 ^ 64; omega_using [ht']) hi
  obtain ⟨s₂, run₂, index₂, flag₂, keep₂⟩ := copyKey_ok s₁ read₁ write₁
  have keep₂' : Keep keyTemps
      {s₁ with mem := s₁.mem.writeW (s.gpr .x21 + BitVec.ofNat 64 i) (key.getD i 0)} s₂ := by
    rw [byte₁] at keep₂
    simpa only [outPtr, index₁] using keep₂
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  constructor
  · refine ⟨?_, frame₁.step i (by omega_using [ht', hi]) _ keep₂', ?_⟩
    · rw [index₂, index₁, counter_add]
    · rw [keep₂'.mem]
      have prefix₂ := prefix₁.extend (show i < 128 by omega_using [ht', hi]) (key.getD i 0)
      rw [initial_set key i] at prefix₂
      exact prefix₂
  · rw [flag₂, index₁, len₁, counter_add]
    exact congrArg some (counter_eq (i + 1) t (by omega_using [ht', hi]) (by omega_using [ht']))

end VG.Proof.Rc2.AArch64

end

end

/-! # Composing the RC2 key-expansion stages -/

@[expose] public section

namespace VG.Proof.Rc2.AArch64

open VG VG.AArch64 VG.Impl.Rc2.AArch64

def coreRegs : List Reg := [.x4, .x21, .x25, .x26, .x27, .x28, .x30]

structure CoreFrame (s₀ s : State) : Prop where
  reg : ∀ r ∈ coreRegs, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Frame [⟨s₀.gpr .x21, 128⟩] s₀.mem s.mem

theorem CoreFrame.of_keep {s s' : State} {rs : List Reg} (keep : Keep rs s s')
    (sep : ∀ r ∈ coreRegs, r ∉ rs) : CoreFrame s s' := by
  refine ⟨fun r hr => keep.reg r (sep r hr), keep.rd, keep.wr, ?_⟩
  rw [keep.mem]; exact Frame.refl _ _

theorem CoreFrame.of_key {s s' : State} (h : KeyFrame s s') : CoreFrame s s' := by
  have sep : ∀ r ∈ coreRegs, r ∉ keyTemps := by decide
  exact ⟨fun r hr => h.reg r (sep r hr), h.rd, h.wr, h.mem⟩

theorem CoreFrame.trans {s₀ s₁ s₂ : State} (h₁ : CoreFrame s₀ s₁) (h₂ : CoreFrame s₁ s₂) :
    CoreFrame s₀ s₂ := by
  refine ⟨fun r hr => (h₂.reg r hr).trans (h₁.reg r hr), h₂.rd.trans h₁.rd,
    h₂.wr.trans h₁.wr, ?_⟩
  have frame₂ := h₂.mem
  rw [h₁.reg .x21 (by decide)] at frame₂
  exact h₁.mem.trans frame₂

theorem expandCopyFill_ok (s : State) (t : Nat) (ht : 1 ≤ t) (ht' : t ≤ 128)
    (len : s.gpr .x20 = BitVec.ofNat 64 t) (zero : s.gpr .x23 = 0)
    (readable : ∀ i < t, InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 i) 1)
    (writable : ∀ i < 128, InRegions s.wr (s.gpr .x21 + BitVec.ofNat 64 i) 1)
    (sep : (Region.mk (s.gpr .x19) t).Disjoint ⟨s.gpr .x21, 128⟩) :
    WP isa expandCopyFill s (fun s' => KeyFrame s s' ∧
      BytesPrefix s'.mem (s.gpr .x21) (fill (Spec.Rc2.bytesAt s.mem (s.gpr .x19) t) (128 - t)) 128) := by
  rw [expandCopyFill]
  apply WP.seq
  apply WP.mono (copyLoop_ok s t ht ht' len zero readable writable sep)
  intro s₁ h₁
  have length : (Spec.Rc2.bytesAt s.mem (s.gpr .x19) t).length = t := by
    simp [Spec.Rc2.bytesAt]
  have ptr₁ := h₁.2.1.reg .x21 (by decide)
  have writes : ∀ i < 128, InRegions s₁.wr (s₁.gpr .x21 + BitVec.ofNat 64 i) 1 := by
    rw [h₁.2.1.wr, ptr₁]; exact writable
  apply WP.mono (maybeFill_ok s₁ (Spec.Rc2.bytesAt s.mem (s.gpr .x19) t)
    (by rw [length]; exact ht) (by rw [length]; exact ht')
    (by rw [length]; exact (h₁.2.1.reg .x20 (by decide)).trans len)
    (by rw [length]; exact h₁.1) writes (by rw [ptr₁, length]; exact h₁.2.2))
  intro s₂ h₂
  exact ⟨h₁.2.1.trans h₂.2.1, by rw [length, ptr₁] at h₂; exact h₂.2.2⟩

theorem reduceDescend_ok (s : State) (l : KeyBytes) (bits : Nat) (hb : 1 ≤ bits) (hb' : bits ≤ 1024)
    (len : s.gpr .x24 = BitVec.ofNat 64 ((bits + 7) / 8))
    (index : s.gpr .x23 = BitVec.ofNat 64 (128 - (bits + 7) / 8))
    (mask : (s.gpr .x2).setWidth 8 = BitVec.ofNat 8 (255 % 2 ^ (8 + bits - 8 * ((bits + 7) / 8))))
    (writable : ∀ i < 128, InRegions s.wr (s.gpr .x21 + BitVec.ofNat 64 i) 1)
    (initialPrefix : BytesPrefix s.mem (s.gpr .x21) l 128) :
    WP isa (.seq (.block reduceKey) (.seq (.block [rr .x10 .x23])
      (.ite (.nonzero .x .x10) (.loop (.block descendKey) (.nonzero .x .x10)) (.block [])))) s (fun s' =>
        KeyFrame s s' ∧ BytesPrefix s'.mem (s.gpr .x21)
          (descend (reduce l bits) ((bits + 7) / 8) (128 - (bits + 7) / 8)) 128) := by
  have bound : 1 ≤ (bits + 7) / 8 ∧ (bits + 7) / 8 ≤ 128 := by omega_using [hb, hb']
  have writes : InRegions s.wr (s.gpr .x21 + s.gpr .x23) 1 := by
    rw [index]; exact writable _ (by omega_using [hb])
  have reads : InRegions (s.rd ++ s.wr) (s.gpr .x21 + s.gpr .x23) 1 := by
    obtain ⟨r, hr, hc⟩ := writes
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  apply WP.seq
  apply WP.mono (reduceKey_ok s reads writes)
  intro s₁ h₁
  have keep₁ := h₁.2
  rw [index, initialPrefix _ (by omega_using [hb]), mask] at keep₁
  have frame₁ := (KeyFrame.refl s).step _ (by omega_using [hb]) _ keep₁
  have ptr₁ := keep₁.reg .x21 (by decide)
  have prefix₁ : BytesPrefix s₁.mem (s.gpr .x21) (reduce l bits) 128 := by
    rw [keep₁.mem]
    exact initialPrefix.write (by decide) (by omega_using [hb]) _
  have write₁ : ∀ i < 128, InRegions s₁.wr (s₁.gpr .x21 + BitVec.ofNat 64 i) 1 := by
    rw [keep₁.wr, ptr₁]; exact writable
  apply WP.mono (maybeDescend_ok s₁ (reduce l bits) ((bits + 7) / 8) bound.1 bound.2
    ((keep₁.reg .x24 (by decide)).trans len) (h₁.1.trans index) write₁
    (by rw [ptr₁]; exact prefix₁))
  intro s₂ h₂
  exact ⟨frame₁.trans h₂.1, by rw [ptr₁] at h₂; exact h₂.2⟩

theorem expandReduce_ok (s : State) (l : KeyBytes) (bits : Nat) (hb : 1 ≤ bits) (hb' : bits ≤ 1024)
    (input : s.gpr .x22 = BitVec.ofNat 64 bits)
    (writable : ∀ i < 128, InRegions s.wr (s.gpr .x21 + BitVec.ofNat 64 i) 1)
    (initialPrefix : BytesPrefix s.mem (s.gpr .x21) l 128) :
    WP isa expandReduce s (fun s' => CoreFrame s s' ∧ BytesPrefix s'.mem (s.gpr .x21)
      (descend (reduce l bits) ((bits + 7) / 8) (128 - (bits + 7) / 8)) 128) := by
  rw [expandReduce]
  apply WP.seq
  obtain ⟨s₁, run₁, len₁, index₁, keep₁⟩ := setReduction_ok s bits hb hb' input
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  apply WP.seq
  apply WP.mono (maskCode_ok s₁ bits hb hb' ((keep₁.reg .x22 (by decide)).trans input))
  intro s₂ h₂
  have frame := (CoreFrame.of_keep keep₁ (by decide)).trans (CoreFrame.of_keep h₂.2 (by decide))
  have ptr₂ := frame.reg .x21 (by decide)
  have writes : ∀ i < 128, InRegions s₂.wr (s₂.gpr .x21 + BitVec.ofNat 64 i) 1 := by
    rw [frame.wr, ptr₂]; exact writable
  apply WP.mono (reduceDescend_ok s₂ l bits hb hb'
    ((h₂.2.reg .x24 (by decide)).trans len₁) ((h₂.2.reg .x23 (by decide)).trans index₁) h₂.1 writes
    (by rw [ptr₂, h₂.2.mem, keep₁.mem]; exact initialPrefix))
  intro s₃ h₃
  exact ⟨frame.trans (CoreFrame.of_key h₃.1), by rw [ptr₂] at h₃; exact h₃.2⟩

end VG.Proof.Rc2.AArch64

end

end

/-! ### `Rc2.AArch64.KeyIO`, which only this module used -/

section

/-! # Register setup and scratch saves for key expansion -/

@[expose] public section

namespace VG.Proof.Rc2.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc2.AArch64

def savedReg (i : Nat) : Reg := saved.getD i .x23

theorem keySave_eq : save .x4 0 = Spill.saveCode .x4 (Spill.slots savedReg 6) := by rfl

theorem keyRestore_eq : restore .x4 0 = Spill.restoreCode .x4 (Spill.slots savedReg 6) := by rfl

theorem pinKey_ok (s : State) :
    ∃ s', runBlock isa [rr .x19 .x0, rr .x20 .x1, rr .x21 .x3, rr .x22 .x2, imm .x23 0] s = some s' ∧
      s'.gpr .x19 = s.gpr .x0 ∧ s'.gpr .x20 = s.gpr .x1 ∧
      s'.gpr .x21 = s.gpr .x3 ∧ s'.gpr .x22 = s.gpr .x2 ∧ s'.gpr .x23 = 0 ∧ Keep saved s s' := by
  refine ⟨_, by
    simp only [rr, imm, runBlock_cons, exec]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_write, State.read, BitVec.add_zero, BitVec.setWidth_eq]
  · simp [gpr_write, State.read, BitVec.add_zero, BitVec.setWidth_eq]
  · simp [gpr_write, State.read, BitVec.add_zero, BitVec.setWidth_eq]
  · simp [gpr_write, State.read, BitVec.add_zero, BitVec.setWidth_eq]
  · exact gpr_write_self _ _ _ _
  · constructor
    · intro r hr
      simp only [saved, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_write, BitVec.setWidth_eq, State.read, BitVec.add_zero, hr.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]
    · simp only [mem_write]
    · simp only [rd_write]
    · simp only [wr_write]

theorem bytesAt_frame {m m' : Mem} {p : Addr} {n : Nat} {rs : List Region}
    (frame : Frame rs m m') (sep : ∀ r ∈ rs, (Region.mk p n).Disjoint r) (bound : n ≤ 2 ^ 64) :
    Spec.Rc2.bytesAt m' p n = Spec.Rc2.bytesAt m p n := by
  unfold Spec.Rc2.bytesAt
  apply List.map_congr_left
  intro i hi
  exact frame.bytes sep bound (List.mem_range.mp hi)

end VG.Proof.Rc2.AArch64

end

end

/-! # Verified RC2 key expansion -/

@[expose] public section

namespace VG.Proof.Rc2.AArch64

open VG VG.AArch64 VG.Impl.Rc2.AArch64

def keyContract : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
    let out : Region := ⟨s.gpr .x3, 128⟩
    let scratch : Region := ⟨s.gpr .x4, 512⟩
    s.rd = [key] ∧ s.wr = [out, scratch] ∧ key.Disjoint out ∧ key.Disjoint scratch ∧
      out.Disjoint scratch ∧
      Spec.Rc2.validKey (s.gpr .x1).toNat (s.gpr .x2).toNat
  post s s' := Spec.Rc2.scheduleAt s'.mem (s.gpr .x3) =
    Spec.Rc2.expandKey (Spec.Rc2.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) (s.gpr .x2).toNat
  pub := PublicRegs [.x0, .x1, .x2, .x3, .x4]

theorem key_body_correct (s : State) (hs : keyContract.pre s) :
    WP isa expandKey s (fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ keyContract.post s s') := by
  obtain ⟨hrd, hwr, keyOut, keyScratch, outScratch, ht, ht', hb, hb'⟩ := hs
  have writes : ∀ i < 6, InRegions s.wr (s.gpr .x4 + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi
    rw [hwr]
    exact ⟨⟨s.gpr .x4, 512⟩, by simp, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  rw [expandKey]
  apply WP.seq
  rw [WP.block_append_iff, keySave_eq]
  apply WP.mono (Spill.save_wp (by decide) (Spill.forall_slots writes))
  intro s₁ h₁
  obtain ⟨s₂, run₂, key₂, len₂, ptr₂, bits₂, zero₂, keep₂⟩ := pinKey_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have scratchFrame : Frame [⟨s.gpr .x4, 512⟩] s.mem s₂.mem := by
    rw [keep₂.mem, h₁.mem]
    exact Spill.saveMem_frame_base (by decide) (by decide) _ _ _
  rw [h₁.gpr] at key₂ len₂ ptr₂ bits₂
  have rd₂ : s₂.rd = s.rd := keep₂.rd.trans h₁.rd
  have wr₂ : s₂.wr = s.wr := keep₂.wr.trans h₁.wr
  have r8₂ : s₂.gpr .x4 = s.gpr .x4 := (keep₂.reg .x4 (by decide)).trans (congrFun h₁.gpr .x4)
  have other₂ : ∀ r ∈ coreRegs, r ≠ .x21 → s₂.gpr r = s.gpr r := by
    intro r hr hn
    have sep : ∀ r ∈ coreRegs, r ≠ .x21 → r ∉ saved := by decide
    exact (keep₂.reg r (sep r hr hn)).trans (congrFun h₁.gpr r)
  have source₂ : Spec.Rc2.bytesAt s₂.mem (s₂.gpr .x19) (s.gpr .x1).toNat =
      Spec.Rc2.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat := by
    rw [key₂]
    exact bytesAt_frame scratchFrame (by simpa using keyScratch) (by omega_using [])
  have read₂ : ∀ i < (s.gpr .x1).toNat,
      InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .x19 + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [rd₂, wr₂, key₂, hrd, hwr]
    exact ⟨⟨s.gpr .x0, (s.gpr .x1).toNat⟩, by simp,
      Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  have write₂ : ∀ i < 128, InRegions s₂.wr (s₂.gpr .x21 + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [wr₂, ptr₂, hwr]
    exact ⟨⟨s.gpr .x3, 128⟩, by simp, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  apply WP.seq
  apply WP.mono (expandCopyFill_ok s₂ (s.gpr .x1).toNat ht ht'
    (by simpa using len₂) zero₂ read₂ write₂ (by rw [key₂, ptr₂]; exact keyOut))
  intro s₃ h₃
  apply WP.seq
  have write₃ : ∀ i < 128, InRegions s₃.wr (s₃.gpr .x21 + BitVec.ofNat 64 i) 1 := by
    rw [h₃.1.wr, h₃.1.reg .x21 (by decide)]; exact write₂
  apply WP.mono (expandReduce_ok s₃ _ (s.gpr .x2).toNat hb hb'
    (by simpa using (h₃.1.reg .x22 (by decide)).trans bits₂) write₃
    (by rw [h₃.1.reg .x21 (by decide)]; exact h₃.2))
  intro s₄ h₄
  have core := (CoreFrame.of_key h₃.1).trans h₄.1
  have outFrame : Frame [⟨s.gpr .x3, 128⟩] s₂.mem s₄.mem := by
    have h := core.mem
    rw [ptr₂] at h; exact h
  have r8₄ : s₄.gpr .x4 = s.gpr .x4 := (core.reg .x4 (by decide)).trans r8₂
  have other₄ : ∀ r ∈ coreRegs, r ≠ .x21 → s₄.gpr r = s.gpr r := by
    intro r hr hn
    exact (core.reg r hr).trans (other₂ r hr hn)
  have rd₄ := core.rd.trans rd₂
  have wr₄ := core.wr.trans wr₂
  have expanded : BytesPrefix s₄.mem (s.gpr .x3)
      (Spec.Rc2.expandBytes (Spec.Rc2.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) (s.gpr .x2).toNat) 128 := by
    have h := h₄.2
    rw [h₃.1.reg .x21 (by decide), ptr₂, source₂] at h
    rw [expandBytes_eq]
    have length : (Spec.Rc2.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat).length = (s.gpr .x1).toNat := by
      simp [Spec.Rc2.bytesAt]
    rw [length]; exact h
  have scratchRead : ∀ i ∈ List.range 6,
      InRegions (s₄.rd ++ s₄.wr) (s₄.gpr .x4 + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi
    rw [rd₄, wr₄, r8₄, hrd, hwr]
    have bound := List.mem_range.mp hi
    exact ⟨⟨s.gpr .x4, 512⟩, by simp, Offset.contains_base _ (by omega_using [bound]) (by omega_using [bound])⟩
  have stored : ∀ i ∈ List.range 6,
      s₄.mem.readW (s₄.gpr .x4 + BitVec.ofNat 64 (8 * i)) 64 = s.gpr (savedReg i) := by
    intro i hi
    have bound := List.mem_range.mp hi
    rw [r8₄, outFrame.readW (r := ⟨s.gpr .x4, 512⟩)
      (Offset.contains_base _ (by omega_using [bound]) (by omega_using [bound])) (by simpa using outScratch.symm) (by decide),
      keep₂.mem, h₁.mem]
    exact Spill.saveMem_saved (l := Spill.slots savedReg 6) (by decide) s.mem (s.gpr .x4) s.gpr
      (savedReg i, 8 * i) (Spill.mem_slots bound)
  rw [keyRestore_eq]
  apply WP.mono (Spill.restore_wp rfl (by decide) (by decide)
    (Spill.forall_slots fun i hi => scratchRead i (List.mem_range.mpr hi))
    (Spill.forall_slots fun i hi => stored i (List.mem_range.mpr hi)))
  intro s₅ h₅
  constructor
  · intro r hr
    by_cases hm : r ∈ (List.range 6).map savedReg
    · exact h₅.gpr_of (.inl (by rwa [Spill.slots_fst]))
    · have covered : ∀ r ∈ preserved, r ∉ (List.range 6).map savedReg →
          r ∈ coreRegs ∧ r ≠ .x21 := by decide
      obtain ⟨hc, hn⟩ := covered r hr hm
      exact (h₅.other r (by rwa [Spill.slots_fst])).trans (other₄ r hc hn)
  · change Spec.Rc2.scheduleAt s₅.mem (s.gpr .x3) = _
    rw [h₅.mem]
    exact scheduleAt_expanded expanded

theorem key_correct (s : State) (hs : keyContract.pre s) :
    ∃ t s', Exec isa expandKey s t s' ∧ abiPreserved s s' ∧ keyContract.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := key_body_correct s hs
  exact ⟨t, s', he, ⟨ha, (VG.AArch64.Exec.regions he rfl).2.2.1, VG.AArch64.Exec.preservedV he (by lit_decide)⟩, hp⟩

end VG.Proof.Rc2.AArch64
