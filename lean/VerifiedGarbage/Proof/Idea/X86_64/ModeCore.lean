module

public import VerifiedGarbage.Proof.Modes.X86_64.Core
public import VerifiedGarbage.Proof.Modes.X86_64.Words
public import VerifiedGarbage.Impl.Idea.X86_64.Modes
public import VerifiedGarbage.Spec.Idea.Cbc
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Idea.X86_64.Lit
public import VerifiedGarbage.Proof.Idea.X86_64.Round
public import Mathlib.Data.List.Induction
public import VerifiedGarbage.Proof.Idea.ModeBytes
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Idea.X86_64.Block
import VerifiedGarbage.Proof.Idea.Memory
import VerifiedGarbage.Proof.Modes.X86_64.Steps
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Idea.X86_64.Ecb
public import VerifiedGarbage.Proof.Aes.Blocks
public import VerifiedGarbage.Proof.AesCtr.Ctr32
public import VerifiedGarbage.Proof.AesCtr.Spec
public import VerifiedGarbage.Proof.Cmac.Frame
public import VerifiedGarbage.Proof.Cmac.Mem
public import VerifiedGarbage.Proof.Cmac.Spec
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Proof.Framework.X86_64.Syms
public import VerifiedGarbage.Proof.Idea.KeyBits
public import VerifiedGarbage.Proof.Idea.Memory
public import VerifiedGarbage.Proof.Idea.X86_64.Block
public import VerifiedGarbage.Proof.Modes.Addr
public import VerifiedGarbage.Proof.Modes.X86_64.Counter
public import VerifiedGarbage.Proof.Modes.X86_64.Setup
public import VerifiedGarbage.Proof.Modes.X86_64.Steps
public import VerifiedGarbage.Spec.Ctr.Contract
public import VerifiedGarbage.Spec.Idea.Contract
import VerifiedGarbage.Proof.Aes.Blocks
import VerifiedGarbage.Proof.AesCtr.Ctr32
import VerifiedGarbage.Proof.AesCtr.Spec
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Idea.KeyBits
import VerifiedGarbage.Proof.Idea.X86_64.Ecb
import VerifiedGarbage.Proof.Modes.Addr
import VerifiedGarbage.Proof.Modes.X86_64.Counter
import VerifiedGarbage.Proof.Modes.X86_64.Setup
import VerifiedGarbage.Spec.Ctr.Contract
import VerifiedGarbage.Spec.Idea.Contract

/-!
# IDEA's core for the modes on x86-64

`modeCoreSpec`: IDEA's core (`Impl.Idea.X86_64.modeCore`) meets what the
modes need of a core of one-word blocks (`Proof.Modes.X86_64.BlockSpec`),
with the key a schedule (of encryption or decryption subkeys), its cipher
`Spec.Idea.cipher`, and the key ready when its copy in the core's slots is
the schedule. `crypt` is `vg_idea_ecb`'s block code (`cryptBlock_run`) on the
buffer.
-/

@[expose] public section

namespace VG.Proof.Idea.X86_64

open VG VG.X86_64 VG.Impl.Idea.X86_64
open VG.Impl.Aes.X86_64 (sb)
open VG.Proof.Modes (over over_at over_frame)
open VG.Proof.Modes.X86_64 (ScrIn coreRegion blkRegion blkAddr BlockSpec copyN_wp movR_ok addImm_ok
  signExtend_small runBlock_app addr_add)

/-- The schedule's copy, with the scratch buffer at `B`. -/
abbrev schedAddr (B : Addr) : Addr := B + BitVec.ofNat 64 (8 * schedSlot)

/-- The schedule at `rdi`, outside the regions `rs`. -/
def ModeKeyArgs (s : State) (rs : List Region) (k : Spec.Idea.Schedule) : Prop :=
  ∃ p : Addr, s.gpr .rdi = p ∧ k = Spec.Idea.scheduleAt s.mem p ∧ (⟨p, 104⟩ : Region) ∈ s.rd ∧
    p.toNat + 104 ≤ 2 ^ 64 ∧ ∀ r ∈ rs, Region.Disjoint ⟨p, 104⟩ r

/-- The schedule's copy is `k`. -/
def ReadyAt (m : Mem) (B : Addr) (k : Spec.Idea.Schedule) : Prop :=
  Spec.Idea.scheduleAt m (schedAddr B) = k

/-- The core's blocks are one word. -/
@[simp] theorem modeCore_bw : modeCore.bw = 1 := rfl

/-- The core's slots, its buffer and the schedule's copy. -/
theorem core_eq (B : Addr) : coreRegion modeCore B = ⟨B, 112⟩ := rfl
theorem blk_eq (B : Addr) : blkRegion modeCore B = ⟨B + BitVec.ofNat 64 0, 8⟩ := rfl
theorem total_eq : modeCore.total = 22 := rfl

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
    (hr : ∀ r ∈ [Reg.rdi], s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (_ : s'.wr = s.wr)
    (hf : Frame rs s.mem s'.mem) : ModeKeyArgs s' rs k := by
  obtain ⟨p, hp, hk, hin, hfit, hdis⟩ := h
  refine ⟨p, by rw [hr .rdi List.mem_cons_self, hp], ?_, by rw [hrd]; exact hin, hfit, hdis⟩
  rw [hk]
  exact (scheduleAt_frame hf hdis).symm

theorem prepare_wp {s : State} {B : Addr} {rs : List Region} {k : Spec.Idea.Schedule}
    (hB : s.gpr sb = B) (hs : ScrIn s B modeCore.total) (hR : (⟨B, 8 * modeCore.total⟩ : Region) ∈ rs)
    (hk : ModeKeyArgs s rs k) :
    WP isa modeCore.prepare s fun s' => ReadyAt s'.mem B k ∧ s'.gpr sb = B ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.gpr .r12 = s.gpr .r12 ∧ s'.gpr .r13 = s.gpr .r13 ∧
      Frame [coreRegion modeCore B] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨p, hp, rfl, hin, hfit, hdis⟩ := hk
  have hfB := hs.fit
  rw [total_eq] at hfB
  have hsep : Region.Disjoint ⟨p, 104⟩ ⟨B, 112⟩ := (hdis _ hR).sub_right (Region.sub_prefix (by rw [total_eq]; decide))
  refine WP.mono (copyN_wp (k := 13) (P := schedAddr B) (Q := p) ⟨by rw [hB], by rw [hp]; simp, by decide,
    by decide, fun w hw => ⟨_, hs.wr, by
      rw [addr_add, total_eq]; exact Offset.contains_base B (by simp only [schedSlot]; omega) (by simp only [schedSlot]; omega)⟩,
    fun w hw => ⟨_, List.mem_append_left _ hin, Offset.contains_base p (by omega) (by omega)⟩,
    (hsep.sub_right (sched_sub B)).symm, by omega⟩) fun s' h => ?_
  refine ⟨scheduleAt_congr_at fun i hi => by rw [h.mem, over_at hi (by omega)], by rw [h.regs _ (by decide), hB],
    h.regs _ (by decide), h.regs _ (by decide), h.regs _ (by decide), ?_, h.rd, h.wr⟩
  rw [h.mem, core_eq]
  exact (over_frame _ _ _ _).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, sched_sub B⟩

/-- `KeyOk` of a schedule at `rdi` within the writable regions. -/
theorem keyOk_at (s : State) {p : Addr} (hp : s.gpr .rdi = p)
    (hin : ∀ d, d + 8 ≤ 104 → InRegions s.wr (p + BitVec.ofNat 64 d) 8) :
    KeyOk (Spec.Idea.scheduleAt s.mem p) s := by
  have hin' : ∀ d, d + 8 ≤ 104 → InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 d) 8 := fun d hd => by
    obtain ⟨r, h1, h2⟩ := hin d hd; exact ⟨r, List.mem_append_right _ h1, h2⟩
  refine ⟨fun k hk => ⟨?_, ?_⟩, fun j hj => ?_⟩
  · rw [ea_at, hp]; exact hin' _ (by omega)
  · rw [ea_at, hp]; exact subkey_read _ _ (by omega)
  · rw [ea_at, hp]; exact subkey_read96 _ _ hj

theorem crypt_wp {s : State} {B : Addr} {k : Spec.Idea.Schedule} (hB : s.gpr sb = B)
    (hs : ScrIn s B modeCore.total) (hr : ReadyAt s.mem B k) :
    WP isa modeCore.crypt s fun s' => s'.gpr sb = B ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.gpr .r12 = s.gpr .r12 ∧ s'.gpr .r13 = s.gpr .r13 ∧ ReadyAt s'.mem B k ∧
      Frame [coreRegion modeCore B] s.mem s'.mem ∧
      (∀ j < modeCore.G, Spec.Aes.bytesAt s'.mem (blkAddr modeCore B j) (8 * modeCore.bw) =
        Spec.Idea.cipher k (Spec.Aes.bytesAt s.mem (blkAddr modeCore B j) (8 * modeCore.bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hw := hs.wr
  rw [total_eq] at hw
  have hfB := hs.fit
  rw [total_eq] at hfB
  -- `rcx` keeps `sb`; `rdi` and `rsi` to the schedule's copy and the buffer.
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s .rcx sb
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := movR_ok s₁ .rdi sb
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := addImm_ok s₂ .rdi (BitVec.ofNat 32 (8 * schedSlot))
  obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄⟩ := movR_ok s₃ .rsi sb
  have g₄ : ∀ x, x ≠ .rcx → x ≠ .rdi → x ≠ .rsi → s₄.gpr x = s.gpr x := fun x h1 h2 h3 => by
    rw [o₄ x h3, o₃ x h2, o₂ x h2, o₁ x h1]
  have rcx₄ : s₄.gpr .rcx = B := by
    rw [o₄ _ (by decide), o₃ _ (by decide), o₂ _ (by decide), r₁, hB]
  have rdi₄ : s₄.gpr .rdi = schedAddr B := by
    rw [o₄ _ (by decide), r₃, r₂, o₁ _ (by decide), hB, signExtend_small (by decide)]
  have rsi₄ : s₄.gpr .rsi = B := by
    rw [r₄, o₃ _ (by decide), o₂ _ (by decide), o₁ _ (by decide), hB]
  have mem₄ : s₄.mem = s.mem := by rw [m₄, m₃, m₂, m₁]
  have rd₄' : s₄.rd = s.rd := by rw [rd₄, rd₃, rd₂, rd₁]
  have wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₃, wr₂, wr₁]
  have inS : ∀ {t n}, t + n ≤ 176 → 0 < n → InRegions s₄.wr (B + BitVec.ofNat 64 t) n := fun ht hn =>
    ⟨_, by rw [wr₄']; exact hw, Offset.contains_base B (by omega) (by omega)⟩
  -- The block.
  have hk := keyOk_at s₄ rdi₄ fun d hd => by
    rw [addr_add]; exact inS (by simp only [schedSlot]; omega) (by decide)
  rw [mem₄, hr] at hk
  obtain ⟨s₅, e₅, b₅, f₅, g₅, rd₅, wr₅⟩ := cryptBlock_run k s₄ rsi₄
    (fun i hi => by
      obtain ⟨r, h1, h2⟩ := inS (t := i) (n := 1) (by omega) (by decide)
      exact ⟨r, List.mem_append_right _ h1, h2⟩)
    (fun i hi => inS (by omega) (by decide)) hk
  obtain ⟨s₆, e₆, r₆, o₆, m₆, rd₆, wr₆⟩ := movR_ok s₅ sb .rcx
  refine WP.of_runBlock ⟨s₆, ?_, ?_⟩
  · show runBlock isa (([Impl.Aes.X86_64.movR .rcx sb] ++ ([Impl.Aes.X86_64.movR .rdi sb] ++
      ([.alu .add .rdi (.imm (BitVec.ofNat 32 (8 * schedSlot)))] ++ ([Impl.Aes.X86_64.movR .rsi sb] : List Instr)))) ++
      cryptBlock ++ [Impl.Aes.X86_64.movR sb .rcx]) s = some s₆
    rw [runBlock_app, runBlock_app, runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some,
      runBlock_app, e₃, Option.bind_some, e₄, Option.bind_some, e₅, Option.bind_some, e₆]
  have kp : ∀ x, x ∉ roundWrites → x ≠ .rcx → x ≠ .rdi → x ≠ .rsi → x ≠ sb → s₆.gpr x = s.gpr x :=
    fun x h0 h1 h2 h3 h4 => by rw [o₆ _ h4, g₅ _ h0, g₄ _ h1 h2 h3]
  have fB : Frame [⟨B, 8⟩] s.mem s₆.mem := by rw [m₆, ← mem₄]; exact f₅
  refine ⟨by rw [r₆, g₅ _ (by decide), rcx₄], kp _ (by decide) (by decide) (by decide) (by decide) (by decide),
    kp _ (by decide) (by decide) (by decide) (by decide) (by decide),
    kp _ (by decide) (by decide) (by decide) (by decide) (by decide), ?_, ?_, fun j hj => ?_,
    by rw [rd₆, rd₅, rd₄'], by rw [wr₆, wr₅, wr₄']⟩
  · rw [ReadyAt, scheduleAt_frame fB fun r hr => ?_]
    · exact hr
    · simp only [List.mem_singleton] at hr; subst hr
      have := sched_buf B; rwa [BitVec.add_zero] at this
  · rw [core_eq]
    exact fB.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
  · have hj0 : j = 0 := by simp only [modeCore] at hj; omega
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
    by simp only [modeCore]; decide, by simp only [modeCore]; decide, by simp only [modeCore]; decide⟩
  keyRegs_ok := by simp only [modeCore]; decide
  regs_ok := by simp only [modeCore, Modes.X86_64.regsOk]; decide
  keyArgs_congr h hr hrd hwr _ hf := keyArgs_congr h hr hrd hwr hf
  ready_frame h hf hd _ _ := readyAt_frame h hf hd
  prepare_wp := prepare_wp
  crypt_wp := crypt_wp

end VG.Proof.Idea.X86_64
