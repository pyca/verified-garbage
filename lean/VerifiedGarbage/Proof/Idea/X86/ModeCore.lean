module

import VerifiedGarbage.Proof.Idea.X86.Block
import VerifiedGarbage.Proof.Idea.X86.Ecb
import VerifiedGarbage.Proof.Idea.ModeBytes
public import VerifiedGarbage.Proof.Modes.X86.Core
public import VerifiedGarbage.Impl.Idea.X86.Modes
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Nat.Prime.Defs
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Idea.X86.Lit
public import VerifiedGarbage.Proof.Framework.X86.Exec
public import VerifiedGarbage.Spec.Idea.Cbc
import VerifiedGarbage.Proof.Idea.Memory
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Idea.X86.Invert

/-!
# IDEA's core for the modes on x86 (32-bit)

`modeCoreSpec`: IDEA's core (`Impl.Idea.X86.modeCore`) meets what the modes
need of a core (`Proof.Modes.X86.CoreSpec`), with the key a schedule, read
through the first stack argument, its cipher `Spec.Idea.cipher`, and the key
ready when the subkeys are copied to the scratch buffer. `crypt` is ECB's
block (`load_run`, `rounds_run`, `output_run`) between the core's own setup
and stores (`modeBlock_run`).
-/

@[expose] public section

namespace VG.Proof.Idea.X86

open VG VG.X86 VG.Impl.Idea.X86
open VG.Proof.Modes.X86 (coreRegion blkRegion blkAddr stkRegion slotA CoreSpec Layout)
open VG.Proof.Idea (cipher_bytes bytesAt_eq scheduleAt_frame)

/-- The schedule, at the address in the first stack argument, outside the
regions `rs`, as is that argument. -/
def KeyArgs (s : State) (rs : List Region) (k : Spec.Idea.Schedule) : Prop :=
  ∃ p : BitVec 32, InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 4) 4 ∧
    s.mem.readW (addr (s.gpr .esp) 4) 32 = p ∧ k = Spec.Idea.scheduleAt s.mem (p.setWidth 64) ∧
    (⟨p.setWidth 64, 104⟩ : Region) ∈ s.rd ++ s.wr ∧ p.toNat + 104 ≤ 2 ^ 32 ∧
    (∀ r ∈ rs, Region.Disjoint ⟨p.setWidth 64, 104⟩ r) ∧ ∀ r ∈ rs, Region.Disjoint ⟨addr (s.gpr .esp) 4, 4⟩ r

theorem modeCore_slots : modeCore.slots = 35 := rfl
theorem modeCore_total : modeCore.total = 46 := rfl
theorem modeCore_ka : modeCore.ka = 1 := rfl
@[simp] theorem modeCore_bw : modeCore.bw = 2 := rfl

/-- The schedule's bytes, outside the regions apart from the core or within
its buffer. -/
theorem sched_keep {B : BitVec 32} {m m' : Mem} {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint (coreRegion modeCore B) r ∨ Region.Sub r (blkRegion modeCore B)) :
    Spec.Idea.scheduleAt m' (B.setWidth 64) = Spec.Idea.scheduleAt m (B.setWidth 64) := by
  refine scheduleAt_frame hf fun r hr => ?_
  rcases hd r hr with h | h
  · exact h.sub_left (Region.sub_prefix (by simp only [modeCore, coreSlots]; decide))
  · refine Region.Disjoint.sub_right ?_ h
    exact Offset.base_disjoint _ (by simp only [modeCore, bufSlot, slots]; decide)
      (by simp only [modeCore, bufSlot, slots]; omega)

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Spec.Idea.Schedule} (h : KeyArgs s rs k)
    (hesp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame rs s.mem s'.mem) :
    KeyArgs s' rs k := by
  obtain ⟨p, hin, hp, rfl, hsch, hfit, hdis, hadis⟩ := h
  refine ⟨p, by rw [hrd, hwr, hesp]; exact hin, ?_, ?_, by rw [hrd, hwr]; exact hsch, hfit, hdis,
    by rw [hesp]; exact hadis⟩
  · rw [hesp, hf.readW (Region.contains_self _ _) hadis (by decide), hp]
  · exact (scheduleAt_frame hf hdis).symm

theorem prepare_wp {s : State} {B : BitVec 32} {rs : List Region} {k : Spec.Idea.Schedule}
    (hB : s.gpr VG.Impl.Modes.X86.sb = B) (hs : VG.Proof.Modes.X86.ScrIn s B modeCore.total)
    (hR : (⟨B.setWidth 64, 4 * modeCore.total⟩ : Region) ∈ rs) (hk : KeyArgs s rs k) :
    WP isa modeCore.prepare s fun s' => Spec.Idea.scheduleAt s'.mem (B.setWidth 64) = k ∧
      s'.gpr VG.Impl.Modes.X86.sb = B ∧ s'.gpr .esp = s.gpr .esp ∧
      Frame [coreRegion modeCore B, stkRegion (s.gpr .esp) modeCore.stack] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨p, hin, hp, rfl, hsch, hfit, hdis, -⟩ := hk
  have hB' : s.gpr .edi = B := hB
  have hfB := hs.fit
  rw [modeCore_total] at hfB
  obtain ⟨s₁, h₁, v₁, e₁⟩ := mov_run .esi (.reg .edi) _ s rfl
  obtain ⟨s₂, h₂, v₂, e₂⟩ := mov_run .edx (.mem (argOp 0)) _ s₁
    (load_src (by rw [e₁.reg .esp (by decide), e₁.rd, e₁.wr]; exact hin))
  have e₁₂ : Keep [.esi, .edx] s s₂ := (e₁.weaken (by decide)).trans (e₂.weaken (by decide))
  have esi₂ : s₂.gpr .esi = B := by rw [e₂.reg .esi (by decide), v₁, hB']
  have edx₂ : s₂.gpr .edx = p := by rw [v₂, e₁.mem, e₁.reg .esp (by decide)]; exact hp
  have hcp : CopyPre (4 * modeCore.total) s₂ :=
    ⟨by rw [edx₂, e₁₂.rd, e₁₂.wr]; exact hsch, by rw [esi₂, e₁₂.wr]; exact hs.wr,
      by rw [modeCore_total]; decide, by rw [edx₂, esi₂]; exact hdis _ hR, by rw [edx₂]; exact hfit,
      by rw [esi₂]; exact hs.fit⟩
  obtain ⟨t, ht, ci⟩ := copy_run s₂ hcp 26 (Nat.le_refl _)
  have he : runBlock isa modePrepare s = some t := by
    rw [modePrepare, show ([.mov .esi (.reg .edi), .mov .edx (.mem (argOp 0))] : List Instr) =
      [.mov .esi (.reg .edi)] ++ [.mov .edx (.mem (argOp 0))] from rfl, List.append_assoc]
    exact run_append h₁ (run_append h₂ ht)
  have treg : ∀ r, r ≠ .eax → t.gpr r = s₂.gpr r := fun r hr => ci.keep.reg r (by simpa using hr)
  refine WP.of_runBlock ⟨t, he, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show B.setWidth 64 = (s₂.gpr .esi).setWidth 64 by rw [esi₂],
      scheduleAt_of_words (S := (s₂.gpr .edx).setWidth 64) fun i hi => ci.words i hi, edx₂, e₁₂.mem]
  · show t.gpr .edi = B
    rw [treg _ (by decide), e₁₂.reg .edi (by decide), hB']
  · rw [treg _ (by decide), e₁₂.reg .esp (by decide)]
  · have f := ci.frame
    rw [esi₂, e₁₂.mem] at f
    exact f.sub fun r hr => ⟨_, List.mem_cons_self, by
      simp only [List.mem_singleton] at hr; subst hr
      exact Region.sub_prefix (by simp only [modeCore, coreSlots, bufSlot, slots]; decide)⟩
  · rw [ci.keep.rd, e₁₂.rd]
  · rw [ci.keep.wr, e₁₂.wr]

/-- The buffer's block, at `addr B (4 * bufSlot)`. -/
abbrev bufA (B : BitVec 32) : Addr := addr B (4 * bufSlot)

theorem bufA_eq {B : BitVec 32} (hfit : B.toNat + 184 ≤ 2 ^ 32) :
    bufA B = B.setWidth 64 + BitVec.ofNat 64 132 := addr_eq (by simp only [bufSlot, slots]; omega)

/-- `modeCrypt`: the buffer's block becomes `Spec.Idea.cryptBlock` of it, and
nothing but `dataSlot`, `t₀`'s slot and the buffer is written. -/
theorem modeCrypt_run {k : Spec.Idea.Schedule} {B : BitVec 32} (s : State) (hB : s.gpr .edi = B)
    (hwr : (⟨B.setWidth 64, 184⟩ : Region) ∈ s.wr) (hfit : B.toNat + 184 ≤ 2 ^ 32)
    (hk : Spec.Idea.scheduleAt s.mem (B.setWidth 64) = k) :
    ∃ s', runBlock isa modeCrypt s = some s' ∧
      Spec.Idea.blockAt s'.mem (bufA B) = Spec.Idea.cryptBlock k (Spec.Idea.blockAt s.mem (bufA B)) ∧
      Frame [⟨addr B dataSlot, 4⟩, ⟨addr B t0Slot, 4⟩, ⟨bufA B, 8⟩] s.mem s'.mem ∧
      s'.gpr .edi = B ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hA := bufA_eq hfit
  have hds : dataSlot = 108 := rfl
  have inB : ∀ d, d + 4 ≤ 184 → InRegions s.wr (B.setWidth 64 + BitVec.ofNat 64 d) 4 := fun d hd =>
    ⟨_, hwr, Offset.contains_base _ hd (by omega)⟩
  -- The setup.
  obtain ⟨s₁, h₁, v₁, e₁⟩ := mov_run .esi (.reg .edi) _ s rfl
  obtain ⟨s₂, h₂, v₂, e₂⟩ := mov_run .eax (.reg .edi) _ s₁ rfl
  obtain ⟨s₃, h₃, v₃, e₃⟩ := alu_run .add (by simp) .eax (.imm (BitVec.ofNat 32 (4 * bufSlot))) _ s₂ rfl
  have e₀₃ : Keep [.esi, .eax] s s₃ :=
    ((e₁.weaken (by decide)).trans (e₂.weaken (by decide))).trans (e₃.weaken (by decide))
  have esi₃ : s₃.gpr .esi = B := by rw [e₃.reg .esi (by decide), e₂.reg .esi (by decide), v₁, hB]
  have eax₃ : s₃.gpr .eax = B + BitVec.ofNat 32 (4 * bufSlot) := by
    rw [v₃, v₂, e₁.reg .edi (by decide), hB]; rfl
  obtain ⟨s₄, h₄, m₄, g₄, rd₄, wr₄⟩ := store_run .esi .eax dataSlot s₃ (by
    rw [esi₃, e₀₃.wr, addr_eq (by rw [show dataSlot = 108 from rfl]; omega)]; exact inB _ (by decide))
  rw [esi₃, eax₃, e₀₃.mem] at m₄
  have f₄ : Frame [⟨addr B dataSlot, 4⟩] s.mem s₄.mem := by
    rw [m₄]; exact (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
  have sched₄ : Spec.Idea.scheduleAt s₄.mem (B.setWidth 64) = k := by
    rw [scheduleAt_frame f₄ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [addr_eq (by rw [show dataSlot = 108 from rfl]; omega)]
      exact Offset.base_disjoint _ (by decide) (by omega), hk]
  have blk₄ : Spec.Idea.blockAt s₄.mem (bufA B) = Spec.Idea.blockAt s.mem (bufA B) :=
    blockAt_congr (frame_bytes f₄ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [hA, addr_eq (by rw [show dataSlot = 108 from rfl]; omega)]
      exact (Offset.disjoint _ (by decide) (by omega) (by omega))) (by decide))
  have esi₄ : s₄.gpr .esi = B := by rw [g₄, esi₃]
  have hb : BlockAt k (B + BitVec.ofNat 32 (4 * bufSlot)) (bufA B) s₄ :=
    { key := ⟨⟨46, by decide, by rw [esi₄]; omega, by rw [esi₄, wr₄, e₀₃.wr]; exact hwr⟩,
        by rw [esi₄]; simp only [slots]; omega, by rw [esi₄]; exact sched₄⟩
      slot := by rw [esi₄, m₄, Mem.readW_writeW_self32]
      addr := rfl
      fit := by simp only [BitVec.toNat_add, BitVec.toNat_ofNat, bufSlot, slots]; omega
      rd0 := by
        rw [wr₄, e₀₃.wr, hA]
        exact let ⟨r, hr, hc⟩ := inB 132 (by decide); ⟨r, List.mem_append_right _ hr, hc⟩
      rd4 := by
        rw [wr₄, e₀₃.wr, hA, Offset.add_add]
        exact let ⟨r, hr, hc⟩ := inB 136 (by decide); ⟨r, List.mem_append_right _ hr, hc⟩ }
  -- ECB's block, but its stores.
  obtain ⟨s₅, h₅, x₅, e₅⟩ := load_run s₄ hb
  obtain ⟨s₆, h₆, x₆, e₆⟩ := rounds_run k _ 8 (by decide) s₅ x₅ (hb.key.keep e₅ (by decide))
  have e₄₆ : KeepT roundWrites s₄ s₆ := ((e₅.weaken (by decide)).toT).trans (by decide) e₆
  obtain ⟨s₇, h₇, x₇, e₇⟩ := output_run k _ s₆ x₆ (hb.key.keepT e₄₆ (by decide))
  have e₄₇ : KeepT roundWrites s₄ s₇ := e₄₆.trans (by decide) e₇.toT
  have esi₇ : s₇.gpr .esi = B := (e₄₇.reg .esi (by decide)).trans esi₄
  -- The stores, through `esi`.
  obtain ⟨s₈, h₈, v₈, e₈⟩ := join_run .ebx .edi (by decide) _ _ s₇ x₇.ebx x₇.edi
  obtain ⟨s₉, h₉, m₉, g₉, rd₉, wr₉⟩ := store_run .esi .ebx (4 * bufSlot) s₈ (by
    rw [e₈.reg .esi (by decide), esi₇, e₈.wr, e₄₇.wr, wr₄, e₀₃.wr]
    exact let ⟨r, hr, hc⟩ := inB 132 (by decide); ⟨r, hr, by rw [← hA] at hc; exact hc⟩)
  obtain ⟨s₁₀, h₁₀, v₁₀, e₁₀⟩ := join_run .ecx .ebp (by decide) _ _ s₉
    (by rw [g₉, e₈.reg .ecx (by decide), x₇.ecx]) (by rw [g₉, e₈.reg .ebp (by decide), x₇.ebp])
  have esi₁₀ : s₁₀.gpr .esi = B := by rw [e₁₀.reg .esi (by decide), g₉, e₈.reg .esi (by decide), esi₇]
  obtain ⟨s₁₁, h₁₁, m₁₁, g₁₁, rd₁₁, wr₁₁⟩ := store_run .esi .ecx (4 * bufSlot + 4) s₁₀ (by
    rw [esi₁₀, e₁₀.wr, wr₉, e₈.wr, e₄₇.wr, wr₄, e₀₃.wr, addr_eq (by simp only [bufSlot, slots]; omega)]
    exact inB 136 (by decide))
  obtain ⟨s₁₂, h₁₂, v₁₂, e₁₂⟩ := mov_run .edi (.reg .esi) _ s₁₁ rfl
  have a4 : addr B (4 * bufSlot + 4) = bufA B + BitVec.ofNat 64 4 := by
    rw [hA, addr_eq (by simp only [bufSlot, slots]; omega), Offset.add_add]; rfl
  have hm : s₁₂.mem = (s₇.mem.writeW (bufA B + BitVec.ofNat 64 0) (s₈.gpr .ebx)).writeW
      (bufA B + BitVec.ofNat 64 4) (s₁₀.gpr .ecx) := by
    rw [e₁₂.mem, m₁₁, esi₁₀, e₁₀.mem, m₉, e₈.reg .esi (by decide), esi₇, e₈.mem, a4, BitVec.add_zero]
  refine ⟨s₁₂, ?_, ?_, ?_, by rw [v₁₂, g₁₁, esi₁₀], ?_, ?_, ?_⟩
  · simp only [modeCrypt, modeSetup, modeStore]
    exact run_append (a := [_, _, _, _]) (run_append h₁ (run_append h₂ (run_append h₃ h₄)))
      (run_append (run_append (run_append h₅ h₆) h₇) (run_append (a := [_, _, _]) h₈ (run_append (a := [_]) h₉
        (run_append (a := [_, _, _]) h₁₀ (run_append (a := [_]) h₁₁ h₁₂)))))
  · rw [hm, v₁₀, v₈, store_block, Spec.Idea.cryptBlock, crypt_eq, blk₄]
  · have f₄₇ : Frame [⟨addr B t0Slot, 4⟩] s₄.mem s₇.mem := by
      have := e₄₇.frame; rw [esi₄] at this; exact this
    rw [hm]
    refine (((f₄.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩).trans
      (f₄₇.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩)).writeW
      (r := ⟨bufA B, 8⟩) (by simp) _ (Offset.contains_base _ (by decide) (by decide))).writeW
      (r := ⟨bufA B, 8⟩) (by simp) _ (Offset.contains_base _ (by decide) (by decide))
  · rw [e₁₂.reg .esp (by decide), g₁₁, e₁₀.reg .esp (by decide), g₉, e₈.reg .esp (by decide),
      e₄₇.reg .esp (by decide), g₄, e₀₃.reg .esp (by decide)]
  · rw [e₁₂.rd, rd₁₁, e₁₀.rd, rd₉, e₈.rd, e₄₇.rd, rd₄, e₀₃.rd]
  · rw [e₁₂.wr, wr₁₁, e₁₀.wr, wr₉, e₈.wr, e₄₇.wr, wr₄, e₀₃.wr]

theorem crypt_wp {s : State} {B : BitVec 32} {k : Spec.Idea.Schedule}
    (hB : s.gpr VG.Impl.Modes.X86.sb = B) (hs : VG.Proof.Modes.X86.ScrIn s B modeCore.total)
    (hr : Spec.Idea.scheduleAt s.mem (B.setWidth 64) = k) :
    WP isa modeCore.crypt s fun s' => s'.gpr VG.Impl.Modes.X86.sb = B ∧ s'.gpr .esp = s.gpr .esp ∧
      Spec.Idea.scheduleAt s'.mem (B.setWidth 64) = k ∧
      Frame [coreRegion modeCore B, stkRegion (s.gpr .esp) modeCore.stack] s.mem s'.mem ∧
      (∀ j < modeCore.G, Spec.Aes.bytesAt s'.mem (blkAddr modeCore B j) (4 * modeCore.bw) =
        Spec.Idea.cipher k (Spec.Aes.bytesAt s.mem (blkAddr modeCore B j) (4 * modeCore.bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hfit : B.toNat + 184 ≤ 2 ^ 32 := hs.fit
  have hA := bufA_eq hfit
  obtain ⟨s', e, hb, f, edi', esp', rd', wr'⟩ := modeCrypt_run s hB hs.wr hfit hr
  have hsub : ∀ r ∈ [(⟨addr B dataSlot, 4⟩ : Region), ⟨addr B t0Slot, 4⟩, ⟨bufA B, 8⟩],
      ∃ d n, r = ⟨B.setWidth 64 + BitVec.ofNat 64 d, n⟩ ∧ 104 ≤ d ∧ d + n ≤ 140 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨108, 4, by rw [show dataSlot = 108 from rfl, addr_eq (by omega)], by decide, by decide⟩
    · exact ⟨104, 4, by rw [show t0Slot = 104 from rfl, addr_eq (by omega)], by decide, by decide⟩
    · exact ⟨132, 8, by rw [hA], by decide, by decide⟩
  refine WP.of_runBlock ⟨s', e, edi', esp', ?_, ?_, fun j hj => ?_, rd', wr'⟩
  · rw [scheduleAt_frame f fun r hr => by
      obtain ⟨d, n, rfl, h1, h2⟩ := hsub r hr
      exact Offset.base_disjoint _ h1 (by omega), hr]
  · exact f.sub fun r hr => ⟨_, List.mem_cons_self, by
      obtain ⟨d, n, rfl, h1, h2⟩ := hsub r hr
      exact Offset.sub_base _ (by simp only [modeCore, coreSlots, bufSlot, slots]; omega)⟩
  · have hj0 : j = 0 := by simp only [modeCore] at hj; omega
    subst hj0
    have ha : blkAddr modeCore B 0 = bufA B := by
      rw [hA]; simp only [blkAddr, slotA, modeCore, bufSlot, slots, Nat.mul_zero, BitVec.add_zero]
    rw [ha, modeCore_bw, show 4 * 2 = 8 from rfl, bytesAt_eq, hb, cipher_bytes]

/-- IDEA's core meets what the modes need. -/
def modeCoreSpec : CoreSpec modeCore where
  Key := Spec.Idea.Schedule
  cipher := Spec.Idea.cipher
  KeyArgs := KeyArgs
  Ready s B k := Spec.Idea.scheduleAt s.mem (B.setWidth 64) = k ∧ B.toNat + 4 * modeCore.total ≤ 2 ^ 32
  cipher_len _ _ := by simp [Spec.Idea.cipher, modeCore]
  layout := ⟨by simp only [modeCore]; decide, .inl rfl,
    by simp only [modeCore, coreSlots, bufSlot]; omega, by simp only [modeCore]; omega⟩
  keyArgs_congr h e r w _ f := keyArgs_congr h e r w f
  ready_frame h _ _ _ _ hf _ hd := ⟨by rw [sched_keep hf hd]; exact h.1, h.2⟩
  prepare_wp hB hs hR hk _ := WP.mono (prepare_wp hB hs hR hk) fun _ ⟨r, h⟩ => ⟨⟨r, hs.fit⟩, h⟩
  crypt_wp hB hs hr _ := WP.mono (crypt_wp hB hs hr.1) fun _ ⟨b, e, r, h⟩ => ⟨b, e, ⟨r, hr.2⟩, h⟩

end VG.Proof.Idea.X86
