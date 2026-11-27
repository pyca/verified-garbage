module

public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.Rc2.X86_64.Lookup
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Rc2.X86_64.Save
public import VerifiedGarbage.Impl.TripleDes.X86_64.ExpandKey
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.TripleDes.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.TripleDes.X86_64.FunctionsLit
public import VerifiedGarbage.Proof.TripleDes.X86_64.ConstantTime
import VerifiedGarbage.Proof.TripleDes.X86_64.Key.Copy
public import VerifiedGarbage.Proof.TripleDes.KeyMemory
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.TripleDes.X86_64.Key.Component
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Mem

/-! ### `TripleDes.X86_64.Key.Composition`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.X86_64.Key

open VG VG.X86_64
open VG.Proof.TripleDes (componentKeys componentOffset)

abbrev keyR (s : State) : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
abbrev outputR (s : State) : Region := ⟨s.gpr .rdx, 384⟩

def slot (base : Addr) (c j : Nat) : Addr := base + BitVec.ofNat 64 (128 * c + 8 * j)

structure Components (origin s : State) (done : Nat) : Prop where
  keys : ∀ c < done, ∀ j < 16, s.mem.readW (slot (origin.gpr .rdx) c j) 64 =
    ((componentKeys origin.mem (origin.gpr .rdi) (origin.gpr .rsi).toNat c).getD j 0).setWidth 64
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  reg : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .rsp], s.gpr r = origin.gpr r
  frame : Frame [outputR origin] origin.mem s.mem

structure Permissions (s : State) : Prop where
  reads : ∀ offset, offset + 8 ≤ (s.gpr .rsi).toNat →
    InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 offset) 8
  writes : ∀ offset, offset + 8 ≤ 384 → InRegions s.wr (s.gpr .rdx + BitVec.ofNat 64 offset) 8
  keyOutput : (keyR s).Disjoint (outputR s)
  valid : Spec.TripleDes.validKey (s.gpr .rsi).toNat

theorem componentStep_ok (origin s : State) (c : Nat) (hc : c < 3)
    (hp : Permissions origin) (hs : Components origin s c)
    (hoff : componentOffset (origin.gpr .rsi).toNat c = 8 * c) :
    WP isa (Impl.TripleDes.X86_64.Key.component (8 * c) c) s
      (Components origin · (c + 1)) := by
  have offsetBound := VG.Proof.TripleDes.componentOffset_bound _ c hp.valid hc
  rw [hoff] at offsetBound
  have read : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (8 * c)) 8 := by
    rw [hs.rd, hs.wr, hs.reg .rdi (by decide)]
    exact hp.reads _ offsetBound
  have write : ∀ j < 16, InRegions s.wr
      (s.gpr .rdx + BitVec.ofNat 64 (128 * c) + BitVec.ofNat 64 (8 * j)) 8 := by
    intro j hj
    rw [hs.wr, hs.reg .rdx (by decide), Offset.add_ofNat_add_ofNat]
    exact hp.writes _ (by omega_using [hc, hj])
  apply WP.mono (component_ok s (8 * c) c hc read write)
  intro t ht
  have frame : Frame [⟨origin.gpr .rdx + BitVec.ofNat 64 (128 * c), 128⟩] s.mem t.mem := by
    have hf := ht.frame
    rw [hs.reg .rdx (by decide)] at hf
    exact hf
  have key : Spec.TripleDes.blockAt s.mem (s.gpr .rdi + BitVec.ofNat 64 (8 * c)) =
      Spec.TripleDes.blockAt origin.mem (origin.gpr .rdi + BitVec.ofNat 64 (8 * c)) := by
    rw [hs.reg .rdi (by decide)]
    apply VG.Proof.TripleDes.blockAt_eq_of_frame _ hs.frame
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact hp.keyOutput.sub_left (Offset.sub_base _ offsetBound)
  refine ⟨?_, ht.rd.trans hs.rd, ht.wr.trans hs.wr,
    fun r hr => (ht.reg r hr).trans (hs.reg r hr), hs.frame.trans (frame.sub ?_)⟩
  · intro k hk j hj
    by_cases he : k = c
    · subst k
      have h := ht.keys j hj
      rw [key, hs.reg .rdx (by decide), Offset.add_ofNat_add_ofNat] at h
      unfold componentKeys
      rw [hoff]
      exact h
    · have before : k < c := by omega_using [hk, he]
      have sep : (Region.mk (slot (origin.gpr .rdx) k j) 8).Disjoint
          ⟨origin.gpr .rdx + BitVec.ofNat 64 (128 * c), 128⟩ :=
        Offset.disjoint _ (by omega_using [before, hj])
          (by omega_using [hk, hc, hj]) (by omega_using [hc])
      have hmem := frame.readW (a := slot (origin.gpr .rdx) k j) (w := 64) (r := ⟨slot (origin.gpr .rdx) k j, 8⟩)
        (Region.contains_self _ _) (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact sep)
        (by decide)
      exact hmem.trans (hs.keys k before j hj)
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨outputR origin, by simp, Offset.sub_base _ (by omega_using [hc])⟩

theorem copyThird_ok (origin s : State) (hp : Permissions origin)
    (hs : Components origin s 2) (hn : (origin.gpr .rsi).toNat = 16) :
    WP isa (.block Impl.TripleDes.X86_64.Key.copyThird) s (Components origin · 3) := by
  have reads : ∀ i < 16, InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi
    rw [hs.rd, hs.wr, hs.reg .rdx (by decide)]
    obtain ⟨r, hr, hc⟩ := hp.writes (8 * i) (by omega_using [hi])
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have writes : ∀ i < 16, InRegions s.wr (s.gpr .rdx + BitVec.ofNat 64 (256 + 8 * i)) 8 := by
    intro i hi
    rw [hs.wr, hs.reg .rdx (by decide)]
    exact hp.writes _ (by omega_using [hi])
  apply WP.mono (copy_ok s 16 (by decide) reads writes)
  intro t ht
  have frame : Frame [⟨origin.gpr .rdx + BitVec.ofNat 64 256, 128⟩] s.mem t.mem := by
    have h := ht.frame
    rw [hs.reg .rdx (by decide)] at h
    exact h
  refine ⟨?_, ht.rd.trans hs.rd, ht.wr.trans hs.wr, ?_, hs.frame.trans (frame.sub ?_)⟩
  · intro c hc j hj
    by_cases he : c = 2
    · subst c
      have hRepeat : componentKeys origin.mem (origin.gpr .rdi) (origin.gpr .rsi).toNat 2 =
          componentKeys origin.mem (origin.gpr .rdi) (origin.gpr .rsi).toNat 0 := by
        rw [hn]; rfl
      have h := ht.keys j hj
      rw [hs.reg .rdx (by decide)] at h
      change t.mem.readW (origin.gpr .rdx + BitVec.ofNat 64 (256 + 8 * j)) 64 = _
      rw [hRepeat]
      have first := hs.keys 0 (by decide) j hj
      simp only [slot, Nat.mul_zero, Nat.zero_add] at first
      exact h.trans first
    · have before : c < 2 := by omega_using [hc, he]
      have sep : (Region.mk (slot (origin.gpr .rdx) c j) 8).Disjoint
          ⟨origin.gpr .rdx + BitVec.ofNat 64 256, 128⟩ :=
        Offset.disjoint _ (by omega_using [before, hj])
          (by omega_using [before, hj]) (by decide)
      have hmem := frame.readW (a := slot (origin.gpr .rdx) c j) (w := 64) (r := ⟨slot (origin.gpr .rdx) c j, 8⟩)
        (Region.contains_self _ _) (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact sep)
        (by decide)
      exact hmem.trans (hs.keys c before j hj)
  · intro r hr
    have unused : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .rsp], r ≠ .rax := by decide
    exact (ht.reg r (unused r hr)).trans (hs.reg r hr)
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨outputR origin, by simp, Offset.sub_base _ (by decide)⟩

def componentIndex (i : Nat) : Nat := if i < 16 then 0 else if i < 32 then 1 else 2

theorem index_partition : ∀ i < 48, componentIndex i < 3 ∧ i % 16 < 16 ∧
    8 * i = 128 * componentIndex i + 8 * (i % 16) := by decide

theorem Components.schedule {origin s : State} (h : Components origin s 3) :
    Spec.TripleDes.scheduleAt s.mem (origin.gpr .rdx) =
      VG.Proof.TripleDes.expandedMemory origin.mem (origin.gpr .rdi) (origin.gpr .rsi).toNat := by
  apply Vector.ext
  intro i hi
  have fact := index_partition i hi
  have keys := h.keys (componentIndex i) fact.1 (i % 16) fact.2.1
  rw [slot, ← fact.2.2] at keys
  rw [VG.Proof.TripleDes.scheduleAt_readW s.mem (origin.gpr .rdx) i hi]
  simp only [VG.Proof.TripleDes.expandedMemory, Vector.getElem_ofFn]
  by_cases h16 : i < 16
  · simpa only [componentIndex, h16, ite_true] using keys
  · by_cases h32 : i < 32
    · simpa only [componentIndex, h16, h32, ite_false, ite_true] using keys
    · simpa only [componentIndex, h16, h32, ite_false] using keys


end VG.Proof.TripleDes.X86_64.Key

end

end

/-! ### `TripleDes.X86_64.Key.Contract`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.X86_64.Key

open VG VG.X86_64

def contract : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let output : Region := ⟨s.gpr .rdx, 384⟩
    let scratch : Region := ⟨s.gpr .rcx, 512⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [key] ∧ s.wr = [output, scratch] ∧ key.Disjoint output ∧ key.Disjoint scratch ∧
      output.Disjoint scratch ∧ ret.Disjoint output ∧ ret.Disjoint scratch ∧
      Spec.TripleDes.validKey (s.gpr .rsi).toNat
  post s s' := Spec.TripleDes.scheduleAt s'.mem (s.gpr .rdx) =
    Spec.TripleDes.expandKey (Spec.TripleDes.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
  pub := PublicRegs [.rdi, .rsi, .rdx, .rcx]

end VG.Proof.TripleDes.X86_64.Key

end

end

/-! ### `TripleDes.X86_64.Key.Body`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.X86_64.Key

open VG VG.X86_64 VG.X86_64.RegUpd
open VG.Proof.Rc2.X86_64 (Keep)

theorem cmpLength_ok (s : State) :
    ∃ s', runBlock isa [.alu .cmp .rsi (.imm 16)] s = some s' ∧
      s'.zf = some (s.gpr .rsi == 16) ∧ Keep [] s s' := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some]
    rfl, ?_, ?_⟩
  · rw [zf_arithFlags]
    exact congrArg some (by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq]
      change (s.gpr .rsi - (16 : BitVec 64) = (0 : BitVec 64)) ↔ s.gpr .rsi = (16 : BitVec 64)
      bv_omega)
  · exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Components.keep {origin s t : State} {n : Nat} (hs : Components origin s n)
    (ht : Keep [] s t) : Components origin t n :=
  ⟨fun c hc j hj => by rw [ht.mem]; exact hs.keys c hc j hj,
    ht.rd.trans hs.rd, ht.wr.trans hs.wr,
    fun r hr => (ht.reg r (by simp)).trans (hs.reg r hr), by rw [ht.mem]; exact hs.frame⟩

theorem beq16_toNat (x : BitVec 64) : (x == 16) = decide (x.toNat = 16) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h; rw [h]; rfl
  · intro h
    apply BitVec.eq_of_toNat_eq
    exact h

theorem body_ok (origin s : State) (hp : Permissions origin) (hs : Components origin s 0)
    (Q : State → Prop)
    (finish : ∀ t, Components origin t 3 → WP isa (.block Impl.TripleDes.X86_64.Key.restore) t Q) :
    WP isa (.seq (Impl.TripleDes.X86_64.Key.component 0 0)
      (.seq (Impl.TripleDes.X86_64.Key.component 8 1)
        (.seq (.block [.alu .cmp .rsi (.imm 16)])
          (.seq (.ite .e (.block Impl.TripleDes.X86_64.Key.copyThird)
            (Impl.TripleDes.X86_64.Key.component 16 2)) (.block Impl.TripleDes.X86_64.Key.restore))))) s Q := by
  apply WP.seq
  apply WP.mono (componentStep_ok origin s 0 (by decide) hp hs (by rfl))
  intro s₁ hs₁
  apply WP.seq
  apply WP.mono (componentStep_ok origin s₁ 1 (by decide) hp hs₁ (by rfl))
  intro s₂ hs₂
  apply WP.seq
  obtain ⟨s₃, run₃, flag₃, keep₃⟩ := cmpLength_ok s₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have hs₃ := hs₂.keep keep₃
  apply WP.seq
  apply WP.mono (Q := (Components origin · 3)) ?_
  · intro t ht
    exact finish t ht
  have flag : s₃.zf = some (decide ((origin.gpr .rsi).toNat = 16)) := by
    rw [flag₃, hs₂.reg .rsi (by decide), beq16_toNat]
  by_cases h16 : (origin.gpr .rsi).toNat = 16
  · apply WP.ite true (by simp only [eval, flag, h16, decide_true])
    · intro _; exact copyThird_ok origin s₃ hp hs₃ h16
    · simp
  · apply WP.ite false (by simp only [eval, flag, h16, decide_false])
    · simp
    · intro _
      exact componentStep_ok origin s₃ 2 (by decide) hp hs₃
        (by simp only [VG.Proof.TripleDes.componentOffset, h16, and_false, ite_false])

end VG.Proof.TripleDes.X86_64.Key

end

end

/-! ### `TripleDes.X86_64.Key.Save`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.X86_64.Key

open VG VG.X86_64 VG.Impl.TripleDes.X86_64

/-- The six callee-saved registers, in slot order. -/
def savedReg (i : Nat) : Reg := (Impl.TripleDes.X86_64.Key.savedRegs).getD i .rdi

theorem save_eq : Impl.TripleDes.X86_64.Key.save = VG.Proof.Rc2.X86_64.saveCode .rcx savedReg 6 := by
  decide +kernel

theorem restore_eq : Impl.TripleDes.X86_64.Key.restore = VG.Proof.Rc2.X86_64.restoreCode .rcx savedReg (List.range 6) := by
  decide +kernel

def Saved (original current : State) : Prop :=
  ∀ i < 6, current.mem.readW (current.gpr .rcx + BitVec.ofNat 64 (8 * i)) 64 =
    original.gpr (savedReg i)

theorem save_ok (s : State)
    (hw : ∀ i < 6, InRegions s.wr (s.gpr .rcx + BitVec.ofNat 64 (8 * i)) 8) :
    WP isa (.block Impl.TripleDes.X86_64.Key.save) s (fun s' =>
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Saved s s' ∧
      Frame [⟨s.gpr .rcx, 48⟩] s.mem s'.mem) := by
  rw [save_eq]
  apply WP.mono (VG.Proof.Rc2.X86_64.saveCode_ok s .rcx savedReg 6 hw)
  intro s' hs
  refine ⟨hs.1, hs.2.1, hs.2.2.1, ?_, ?_⟩
  · intro i hi
    rw [hs.1, hs.2.2.2]
    exact VG.Proof.Rc2.X86_64.saveMem_read _ _ _ 6 (by decide) i hi
  · rw [hs.2.2.2]
    exact VG.Proof.Rc2.X86_64.saveMem_frame _ _ _ 6 (by decide)

theorem savedReg_separate : ∀ i < 6, savedReg i ≠ .rcx := by decide +kernel

theorem restore_ok (original s : State) (hsaved : Saved original s)
    (hread : ∀ i < 6, InRegions (s.rd ++ s.wr) (s.gpr .rcx + BitVec.ofNat 64 (8 * i)) 8) :
    WP isa (.block Impl.TripleDes.X86_64.Key.restore) s (fun s' =>
      (∀ r ∈ Impl.TripleDes.X86_64.Key.savedRegs, s'.gpr r = original.gpr r) ∧
      VG.Proof.Rc2.X86_64.Keep (Impl.TripleDes.X86_64.Key.savedRegs) s s') := by
  rw [restore_eq]
  have hregs : (List.range 6).map savedReg = Impl.TripleDes.X86_64.Key.savedRegs := by decide +kernel
  have h := VG.Proof.Rc2.X86_64.restoreCode_ok s .rcx savedReg (List.range 6) original.gpr
    (fun i hi => savedReg_separate i (List.mem_range.mp hi))
    (fun i hi => hread i (List.mem_range.mp hi))
    (fun i hi => hsaved i (List.mem_range.mp hi))
  rw [hregs] at h
  exact h



end VG.Proof.TripleDes.X86_64.Key

end

end


@[expose] public section

namespace VG.Proof.TripleDes.X86_64.Key

open VG VG.X86_64

 theorem expand_correct (s : State) (hs : contract.pre s) :
    WP isa Impl.TripleDes.X86_64.Key.expandKey s (fun s' => gprPreserved s s' ∧ contract.post s s') := by
  obtain ⟨hrd, hwr, keyOutput, keyScratch, outputScratch, retOutput, retScratch, valid⟩ := hs
  have scratchWrites : ∀ i < 6, InRegions s.wr (s.gpr .rcx + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi
    rw [hwr]
    exact ⟨⟨s.gpr .rcx, 512⟩, by simp, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  rw [Impl.TripleDes.X86_64.Key.expandKey]
  apply WP.seq
  apply WP.mono (save_ok s scratchWrites)
  intro s₁ h₁
  have g₁ (r : Reg) : s₁.gpr r = s.gpr r := congrFun h₁.1 r
  have hp : Permissions s₁ := by
    constructor
    · intro offset hoff
      rw [h₁.2.1, h₁.2.2.1, g₁, hrd, hwr]
      exact ⟨⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, by simp,
        Offset.contains_base _ (by simpa only [g₁] using hoff) (by
          have bound := BitVec.isLt (s.gpr .rsi)
          rw [g₁] at hoff
          omega_using [hoff, bound])⟩
    · intro offset hoff
      rw [h₁.2.2.1, g₁, hwr]
      exact ⟨⟨s.gpr .rdx, 384⟩, by simp, Offset.contains_base _ hoff (by omega_using [hoff])⟩
    · simpa only [keyR, outputR, g₁] using keyOutput
    · simpa only [g₁] using valid
  apply body_ok s₁ s₁ hp ⟨fun _ h => by omega, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  intro s₂ h₂
  have g₂ (r : Reg) (hr : r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .rsp]) : s₂.gpr r = s.gpr r :=
    (h₂.reg r hr).trans (g₁ r)
  have frame₂ : Frame [⟨s.gpr .rdx, 384⟩] s₁.mem s₂.mem := by
    have h := h₂.frame
    rw [outputR, g₁] at h
    exact h
  have saved₂ : Saved s s₂ := by
    intro i hi
    have sub : Region.Sub ⟨s.gpr .rcx + BitVec.ofNat 64 (8 * i), 8⟩ ⟨s.gpr .rcx, 512⟩ :=
      Offset.sub_base _ (by omega_using [hi])
    have mem := frame₂.readW (a := s.gpr .rcx + BitVec.ofNat 64 (8 * i)) (w := 64)
      (r := ⟨s.gpr .rcx + BitVec.ofNat 64 (8 * i), 8⟩) (Region.contains_self _ _)
      (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact (outputScratch.sub_right sub).symm)
      (by decide)
    rw [g₂ .rcx (by decide)]
    have saved₁ := h₁.2.2.2.1 i hi
    rw [g₁] at saved₁
    exact mem.trans saved₁
  have scratchReads : ∀ i < 6, InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .rcx + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi
    rw [h₂.rd, h₂.wr, h₁.2.1, h₁.2.2.1, g₂ .rcx (by decide)]
    obtain ⟨r, hr, hc⟩ := scratchWrites i hi
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  apply WP.mono (restore_ok s s₂ saved₂ scratchReads)
  intro s₃ h₃
  have scratchFrame : Frame [⟨s.gpr .rcx, 512⟩] s.mem s₁.mem := h₁.2.2.2.2.sub (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨⟨s.gpr .rcx, 512⟩, by simp, Region.sub_prefix (by decide)⟩)
  have initialBytes := VG.Proof.TripleDes.bytesAt_eq_of_frame (s.gpr .rdi) (s.gpr .rsi).toNat
    scratchFrame (Nat.le_of_lt (BitVec.isLt _)) (by simpa using keyScratch)
  constructor
  · constructor
    · intro r hr
      by_cases hrsp : r = .rsp
      · subst r
        exact (h₃.2.reg .rsp (by decide)).trans (g₂ .rsp (by decide))
      · have saved : ∀ r ∈ calleeSaved, r ≠ .rsp → r ∈ Impl.TripleDes.X86_64.Key.savedRegs := by decide
        exact h₃.1 r (saved r hr hrsp)
    · have frame : Frame [⟨s.gpr .rdx, 384⟩, ⟨s.gpr .rcx, 512⟩] s.mem s₃.mem := by
        rw [h₃.2.mem]
        exact (scratchFrame.mono (by simp)).trans (frame₂.mono (by simp))
      apply frame.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) _ (by decide)
      simpa only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
        And.intro retOutput retScratch
  · have result := h₂.schedule
    simp only [g₁] at result
    rw [← VG.Proof.TripleDes.expandKey_memory s₁.mem (s.gpr .rdi) (s.gpr .rsi).toNat valid,
      initialBytes] at result
    change Spec.TripleDes.scheduleAt s₃.mem (s.gpr .rdx) = _
    rw [h₃.2.mem]
    exact result

end VG.Proof.TripleDes.X86_64.Key
