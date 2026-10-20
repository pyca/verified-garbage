module

public import VerifiedGarbage.Proof.Idea.AArch64.Ecb
public import VerifiedGarbage.Proof.Idea.ModeBytes
public import VerifiedGarbage.Proof.Modes.AArch64.Core
public import VerifiedGarbage.Proof.Modes.AArch64.Words
public import VerifiedGarbage.Impl.Idea.AArch64.Modes
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Idea.AArch64.Lit
public import Mathlib.Data.List.Induction
public import VerifiedGarbage.Spec.Idea.Cbc
import VerifiedGarbage.Proof.Idea.AArch64.Block
import VerifiedGarbage.Proof.Modes.AArch64.Steps
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Aes.Blocks
public import VerifiedGarbage.Proof.AesCtr.Ctr32
public import VerifiedGarbage.Proof.AesCtr.Spec
public import VerifiedGarbage.Proof.Cmac.Frame
public import VerifiedGarbage.Proof.Cmac.Mem
public import VerifiedGarbage.Proof.Cmac.Spec
public import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Bswap
public import VerifiedGarbage.Proof.Framework.CallLay
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Idea.AArch64.Block
public import VerifiedGarbage.Proof.Idea.KeyBits
public import VerifiedGarbage.Proof.Idea.Memory
public import VerifiedGarbage.Proof.Modes.AArch64.Steps
public import VerifiedGarbage.Proof.Modes.Addr
public import VerifiedGarbage.Spec.Ctr.Contract
import VerifiedGarbage.Proof.Aes.Blocks
import VerifiedGarbage.Proof.AesCtr.Ctr32
import VerifiedGarbage.Proof.AesCtr.Spec
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Idea.KeyBits
import VerifiedGarbage.Proof.Idea.Memory
import VerifiedGarbage.Proof.Modes.Addr
import VerifiedGarbage.Spec.Ctr.Contract

/-!
# IDEA's core for the modes on AArch64

`modeCoreSpec`: IDEA's core (`Impl.Idea.AArch64.modeCore`) meets what the
modes need of a core of one-word blocks (`Proof.Modes.AArch64.BlockSpec`),
with the key a schedule (of encryption or decryption subkeys), its cipher
`Spec.Idea.cipher`, and the key ready when its copy in the core's slots is
the schedule. As on x86-64 (`Proof/Idea/X86_64/ModeCore.lean`): `crypt` is
`vg_idea_ecb`'s block code (`cryptBlock_run`) on the buffer.
-/

@[expose] public section

namespace VG.Proof.Idea.AArch64

open VG VG.AArch64 VG.Impl.Idea.AArch64
open VG.Impl.Aes.AArch64 (sb)
open VG.Proof.Modes (over over_at over_frame)
open VG.Proof.Modes.AArch64 (ScrIn coreRegion blkRegion blkAddr BlockSpec copyN_wp addImm_ok runBlock_app addr_add)

/-- The schedule's copy, with the scratch buffer at `B`. -/
abbrev schedAddr (B : Addr) : Addr := B + BitVec.ofNat 64 (8 * schedSlot)

/-- The schedule at `x0`, outside the regions `rs`. -/
def ModeKeyArgs (s : State) (rs : List Region) (k : Spec.Idea.Schedule) : Prop :=
  ∃ p : Addr, s.gpr .x0 = p ∧ k = Spec.Idea.scheduleAt s.mem p ∧ (⟨p, 104⟩ : Region) ∈ s.rd ∧
    p.toNat + 104 ≤ 2 ^ 64 ∧ ∀ r ∈ rs, Region.Disjoint ⟨p, 104⟩ r

/-- The schedule's copy is `k`. -/
def ReadyAt (m : Mem) (B : Addr) (k : Spec.Idea.Schedule) : Prop :=
  Spec.Idea.scheduleAt m (schedAddr B) = k

/-- The core's blocks are one word. -/
@[simp] theorem modeCore_bw : modeCore.bw = 1 := rfl

/-- The core's slots, its buffer and the schedule's copy. -/
theorem core_eq (B : Addr) : coreRegion modeCore B = ⟨B, 112⟩ := rfl
theorem blk_eq (B : Addr) : blkRegion modeCore B = ⟨B + BitVec.ofNat 64 0, 8⟩ := rfl
theorem total_eq : modeCore.total = 26 := rfl

theorem sched_sub (B : Addr) : Region.Sub ⟨schedAddr B, 104⟩ ⟨B, 112⟩ := Offset.sub_base B (by decide)

theorem sched_buf (B : Addr) : Region.Disjoint ⟨schedAddr B, 104⟩ ⟨B + BitVec.ofNat 64 0, 8⟩ :=
  Offset.disjoint B (.inr (by decide)) (by decide) (by decide)

theorem readyAt_frame {m m' : Mem} {B : Addr} {k : Spec.Idea.Schedule} {rs : List Region}
    (h : ReadyAt m B k) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint (coreRegion modeCore B) r ∨ Region.Sub r (blkRegion modeCore B)) :
    ReadyAt m' B k := by
  rw [ReadyAt, scheduleAt_frame hf fun r hr => ?_]
  · exact h
  rcases hd r hr with h' | h'
  · rw [core_eq] at h'; exact h'.sub_left (sched_sub B)
  · rw [blk_eq] at h'; exact (sched_buf B).sub_right h'

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Spec.Idea.Schedule} (h : ModeKeyArgs s rs k)
    (hr : ∀ r ∈ [Reg.x0], s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (_ : s'.wr = s.wr)
    (hf : Frame rs s.mem s'.mem) : ModeKeyArgs s' rs k := by
  obtain ⟨p, hp, hk, hin, hfit, hdis⟩ := h
  refine ⟨p, by rw [hr .x0 List.mem_cons_self, hp], ?_, by rw [hrd]; exact hin, hfit, hdis⟩
  rw [hk]
  exact (scheduleAt_frame hf hdis).symm

theorem prepare_wp {s : State} {B : Addr} {rs : List Region} {k : Spec.Idea.Schedule}
    (hB : s.gpr sb = B) (hs : ScrIn s B modeCore.total) (hR : (⟨B, 8 * modeCore.total⟩ : Region) ∈ rs)
    (hk : ModeKeyArgs s rs k) :
    WP isa modeCore.prepare s fun s' => ReadyAt s'.mem B k ∧ s'.gpr sb = B ∧
      s'.gpr .x23 = s.gpr .x23 ∧ s'.gpr .x24 = s.gpr .x24 ∧
      Frame [coreRegion modeCore B] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨p, hp, rfl, hin, hfit, hdis⟩ := hk
  have hfB := hs.fit
  rw [total_eq] at hfB
  have hsep : Region.Disjoint ⟨p, 104⟩ ⟨B, 112⟩ :=
    (hdis _ hR).sub_right (Region.sub_prefix (by rw [total_eq]; decide))
  refine WP.mono (copyN_wp (k := 13) (t := .x6) (u := .x6) (P := schedAddr B) (Q := p)
    ⟨by rw [hB], by rw [hp]; simp, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, fun w hw => ⟨_, hs.wr, by
        rw [addr_add, total_eq]
        exact Offset.contains_base B (by simp only [schedSlot]; omega) (by simp only [schedSlot]; omega)⟩,
      fun w hw => ⟨_, List.mem_append_left _ hin, Offset.contains_base p (by omega) (by omega)⟩,
      (hsep.sub_right (sched_sub B)).symm, by omega⟩) fun s' h => ?_
  refine ⟨scheduleAt_congr_at fun i hi => by rw [h.mem, over_at hi (by omega)],
    by rw [h.regs _ (by decide) (by decide), hB], h.regs _ (by decide) (by decide), h.regs _ (by decide) (by decide),
    ?_, h.rd, h.wr⟩
  rw [h.mem, core_eq]
  exact (over_frame _ _ _ _).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, sched_sub B⟩

theorem crypt_wp {s : State} {B : Addr} {k : Spec.Idea.Schedule} (hB : s.gpr sb = B)
    (hs : ScrIn s B modeCore.total) (hr : ReadyAt s.mem B k) :
    WP isa modeCore.crypt s fun s' => s'.gpr sb = B ∧
      s'.gpr .x23 = s.gpr .x23 ∧ s'.gpr .x24 = s.gpr .x24 ∧ ReadyAt s'.mem B k ∧
      Frame [coreRegion modeCore B] s.mem s'.mem ∧
      (∀ j < modeCore.G, Spec.Aes.bytesAt s'.mem (blkAddr modeCore B j) (8 * modeCore.bw) =
        Spec.Idea.cipher k (Spec.Aes.bytesAt s.mem (blkAddr modeCore B j) (8 * modeCore.bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hw := hs.wr
  rw [total_eq] at hw
  have hfB := hs.fit
  rw [total_eq] at hfB
  -- `x2` keeps `sb`; `x0` and `x1` to the schedule's copy and the buffer; the mask.
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := addImm_ok s .x2 sb (v := 0) (by decide)
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := addImm_ok s₁ .x0 sb (v := 8 * schedSlot) (by decide)
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := addImm_ok s₂ .x1 sb (v := 0) (by decide)
  obtain ⟨s₄, e₄, mk₄, k₄⟩ := setMask_run s₃
  have g₄ : ∀ x, x ≠ .x2 → x ≠ .x0 → x ≠ .x1 → x ≠ .x15 → s₄.gpr x = s.gpr x := fun x h1 h2 h3 h4 => by
    rw [k₄.reg x (by simp [h4]), o₃ x h3, o₂ x h2, o₁ x h1]
  have x2₄ : s₄.gpr .x2 = B := by
    rw [k₄.reg _ (by decide), o₃ _ (by decide), o₂ _ (by decide), r₁, hB]; simp
  have x0₄ : s₄.gpr .x0 = schedAddr B := by
    rw [k₄.reg _ (by decide), o₃ _ (by decide), r₂, o₁ _ (by decide), hB]
  have x1₄ : s₄.gpr .x1 = B := by
    rw [k₄.reg _ (by decide), r₃, o₂ _ (by decide), o₁ _ (by decide), hB]; simp
  have mem₄ : s₄.mem = s.mem := by rw [k₄.mem, m₃, m₂, m₁]
  have rd₄' : s₄.rd = s.rd := by rw [k₄.rd, rd₃, rd₂, rd₁]
  have wr₄' : s₄.wr = s.wr := by rw [k₄.wr, wr₃, wr₂, wr₁]
  have inS : ∀ {t n}, t + n ≤ 208 → 0 < n → InRegions s₄.wr (B + BitVec.ofNat 64 t) n := fun ht hn =>
    ⟨_, by rw [wr₄']; exact hw, Offset.contains_base B (by omega) (by omega)⟩
  -- The block.
  have hk : KeyOk k s₄ := ⟨by
      rw [x0₄]
      obtain ⟨r, h1, h2⟩ := inS (t := 8 * schedSlot) (n := 104) (by decide) (by decide)
      exact ⟨r, List.mem_append_right _ h1, h2⟩,
    by rw [x0₄, mem₄]; exact hr⟩
  obtain ⟨s₅, e₅, b₅, f₅, g₅, rd₅, wr₅, -⟩ := cryptBlock_run k s₄ x1₄
    (fun i hi => by
      obtain ⟨r, h1, h2⟩ := inS (t := i) (n := 1) (by omega) (by decide)
      exact ⟨r, List.mem_append_right _ h1, by simpa using h2⟩)
    (fun i hi => by simpa using inS (t := i) (n := 1) (by omega) (by decide)) hk mk₄
  obtain ⟨s₆, e₆, r₆, o₆, m₆, rd₆, wr₆⟩ := addImm_ok s₅ sb .x2 (v := 0) (by decide)
  refine WP.of_runBlock ⟨s₆, ?_, ?_⟩
  · show runBlock isa (([.addImm .x .x2 sb 0] ++ ([.addImm .x .x0 sb (8 * schedSlot)] ++
      ([.addImm .x .x1 sb 0] ++ ([setMask] : List Instr)))) ++ cryptBlock ++ [.addImm .x sb .x2 0]) s = some s₆
    rw [runBlock_app, runBlock_app, runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some,
      runBlock_app, e₃, Option.bind_some, e₄, Option.bind_some, e₅, Option.bind_some, e₆]
  have kp : ∀ x, x ∉ roundWrites → x ≠ .x2 → x ≠ .x0 → x ≠ .x1 → x ≠ .x15 → x ≠ sb → s₆.gpr x = s.gpr x :=
    fun x h0 h1 h2 h3 h4 h5 => by rw [o₆ _ h5, g₅ _ h0, g₄ _ h1 h2 h3 h4]
  have fB : Frame [⟨B, 8⟩] s.mem s₆.mem := by rw [m₆, ← mem₄]; exact f₅
  refine ⟨by rw [r₆, g₅ _ (by decide), x2₄]; simp,
    kp _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    kp _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ?_, ?_, fun j hj => ?_,
    by rw [rd₆, rd₅, rd₄'], by rw [wr₆, wr₅, wr₄']⟩
  · rw [ReadyAt, scheduleAt_frame fB fun r hr => ?_]
    · exact hr
    · simp only [List.mem_singleton] at hr; subst hr
      have := sched_buf B; rwa [BitVec.add_zero] at this
  · rw [core_eq]
    exact fB.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
  · have hj0 : j = 0 := by simp only [modeCore, Impl.Modes.AArch64.Core.G] at hj; omega
    subst hj0
    have ea : blkAddr modeCore B 0 = B := by simp [modeCore]
    rw [modeCore_bw, ea, cipher_bytes, bytesAt_eq, m₆, b₅, mem₄]

/-- IDEA's core meets what the modes need. -/
def modeCoreSpec : BlockSpec modeCore where
  Key := Spec.Idea.Schedule
  cipher := Spec.Idea.cipher
  KeyArgs := ModeKeyArgs
  Ready s B k := ReadyAt s.mem B k
  cipher_len _ _ := by simp [Spec.Idea.cipher]
  layout := ⟨by simp only [modeCore]; decide, by simp only [modeCore]; decide, by simp only [modeCore]; decide,
    by simp only [modeCore]; decide, by simp only [modeCore]; decide, by simp only [modeCore]; decide,
    by simp only [modeCore]; decide⟩
  keyRegs_ok := by simp only [modeCore]; decide
  regs_ok := by simp only [modeCore, Modes.AArch64.regsOk]; decide
  keyArgs_congr h hr hrd hwr _ hf := keyArgs_congr h hr hrd hwr hf
  ready_frame h hf hd _ _ := readyAt_frame h hf hd
  prepare_wp := prepare_wp
  crypt_wp := crypt_wp

end VG.Proof.Idea.AArch64
