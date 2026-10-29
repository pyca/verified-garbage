module

public import VerifiedGarbage.Proof.Modes.RISCV64.Core
public import VerifiedGarbage.Impl.Idea.RISCV64.Modes
public import VerifiedGarbage.Spec.Idea.Cbc
public import VerifiedGarbage.Proof.Idea.RISCV64.Round
import VerifiedGarbage.Proof.Idea.ModeBytes
import VerifiedGarbage.Proof.Idea.RISCV64.Ecb
import VerifiedGarbage.Proof.Idea.RISCV64.Block
import VerifiedGarbage.Proof.Idea.RISCV64.Mul
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# IDEA's core for the modes on RISC-V

`coreSpec`: IDEA's core (`Impl.Idea.RISCV64.core`) meets what the modes need
of a core (`Proof.Modes.RISCV64.CoreSpec`), with the key a schedule of
subkeys, read in place through `a0`, its cipher `Spec.Idea.cipher`, as on
PPC64LE. The schedule is readable and apart from the regions the mode
writes (`KeyArgs`), and from the frame (`Ready`), so nothing the mode or
the core writes changes it. The core runs ECB's block code on its buffer
(`cryptBlock_ok`).
-/

@[expose] public section

namespace VG.Proof.Idea.RISCV64.Mode

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Idea.RISCV64
open VG.Impl.Modes.RISCV64 (sb)
open VG.Proof.Modes.RISCV64 (coreRegion blkRegion blkAddr slotA CoreSpec Layout ScrIn kept KeptBut)

/-- The schedule. -/
abbrev keyR (s : State) : Region := ⟨s.gpr .a0, 104⟩

/-- The schedule at `a0` is `k`, readable, and apart from the regions `rs`. -/
def KeyArgs (s : State) (rs : List Region) (k : Spec.Idea.Schedule) : Prop :=
  Spec.Idea.scheduleAt s.mem (s.gpr .a0) = k ∧ keyR s ∈ s.rd ++ s.wr ∧ ∀ r ∈ rs, (keyR s).Disjoint r

/-- The key's arguments, apart from the frame at `B` too. -/
def Ready (s : State) (B : Addr) (ws : List Region) (k : Spec.Idea.Schedule) : Prop :=
  KeyArgs s ws k ∧ (keyR s).Disjoint ⟨B, 8 * 8⟩

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Spec.Idea.Schedule} (h : KeyArgs s rs k)
    (e : s'.gpr .a0 = s.gpr .a0) (hrd : s'.rd = s.rd) (hwr : ∃ ws, s'.wr = ws ++ s.wr)
    (hf : Frame rs s.mem s'.mem) : KeyArgs s' rs k := by
  obtain ⟨hk, hin, hd⟩ := h
  obtain ⟨ws, hw⟩ := hwr
  refine ⟨?_, ?_, by rw [keyR, e]; exact hd⟩
  · rw [e, Proof.Idea.scheduleAt_frame hf hd, hk]
  · rw [hrd, hw, keyR, e]
    rcases List.mem_append.mp hin with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_append_right _ h)

theorem ready_frame {s s' : State} {B : Addr} {ws : List Region} {k : Spec.Idea.Schedule}
    {rs : List Region} (h : Ready s B ws k) (e : s'.gpr .a0 = s.gpr .a0) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hf : Frame rs s.mem s'.mem) (hs : ∀ r ∈ rs, ∃ r' ∈ ws, Region.Sub r r') :
    Ready s' B ws k := by
  obtain ⟨⟨hk, hin, hd⟩, hB⟩ := h
  have hd' : ∀ r ∈ rs, (keyR s).Disjoint r := fun r hr => by
    obtain ⟨r', hr', hsub⟩ := hs r hr
    exact (hd r' hr').sub_right hsub
  refine ⟨⟨?_, by rw [hrd, hwr, keyR, e]; exact hin, by rw [keyR, e]; exact hd⟩, by rw [keyR, e]; exact hB⟩
  rw [e, Proof.Idea.scheduleAt_frame hf hd', hk]

theorem layout : Layout core :=
  ⟨by decide, .inl rfl, by decide, by decide, by decide, by decide, by decide⟩

theorem prepare_wp {s : State} {B : Addr} {rs : List Region} {k : Spec.Idea.Schedule}
    (hB : s.gpr sb = B) (_hS : ScrIn s B core.total) (hm : (⟨B, 8 * core.total⟩ : Region) ∈ rs)
    (hk : KeyArgs s rs k) :
    WP isa core.prepare s fun s' => Ready s' B rs k ∧ s'.gpr sb = B ∧
      (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ Frame [coreRegion core B] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr :=
  WP.block_nil ⟨⟨hk, hk.2.2 _ hm⟩, hB, fun _ _ => rfl, Frame.refl _ _, rfl, rfl⟩

/-- The registers the core writes. -/
abbrev coreWrites : List Reg := [.t2, .a1] ++ roundWrites

/-- The kept registers are none the core writes. -/
theorem kept_apart : ∀ r ∈ kept, r ∉ coreWrites := by decide

theorem crypt_wp {s : State} {B : Addr} {ws : List Region} {k : Spec.Idea.Schedule}
    (hB : s.gpr sb = B) (hS : ScrIn s B core.total) (hR : Ready s B ws k) :
    WP isa core.crypt s fun s' => s'.gpr sb = B ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      Ready s' B ws k ∧ Frame [coreRegion core B] s.mem s'.mem ∧
      (∀ j < core.G, Spec.Aes.bytesAt s'.mem (blkAddr core B j) (4 * core.bw) =
        Spec.Idea.cipher k (Spec.Aes.bytesAt s.mem (blkAddr core B j) (4 * core.bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hfit : B.toNat + 8 * 8 ≤ 2 ^ 64 := hS.fit
  have hW : (⟨B, 8 * 8⟩ : Region) ∈ s.wr := hS.whole (by decide)
  obtain ⟨⟨hk, hin, hd⟩, hkB⟩ := hR
  simp only [core]
  -- The mask.
  refine WP.seq (WP.mono (WP.keep [.t2] (Q := fun t => t.gpr .t2 = 65535 ∧ t.mem = s.mem)
    (setMask_ok s) (by decide) rfl) fun s₁ ⟨⟨h2₁, m₁⟩, k₁⟩ => ?_)
  -- The buffer's address.
  refine WP.seq (wp_addi (by decide) fun s₂ u₂ => WP.block_nil ?_)
  have a₂ : s₂.gpr .a1 = B + BitVec.ofNat 64 48 := by
    rw [u₂.gpr, k₁.gpr (show sb ∉ [Reg.t2] by decide), hB]; rfl
  have K₂ : Keep [.t2, .a1] s s₂ := ⟨fun r hr => by
      rw [u₂.other r fun e => hr (by rw [e]; decide), k₁.gpr fun h => hr (by
        simp only [List.mem_singleton] at h; rw [h]; decide)],
    by rw [u₂.rd, k₁.2.1], by rw [u₂.wr, k₁.2.2]⟩
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, m₁]
  have a0₂ : s₂.gpr .a0 = s.gpr .a0 := K₂.gpr (by decide)
  have hk₂ : KeyOk k s₂ := by
    have h := keyOk_of s₂ (by rw [a0₂, K₂.2.1, K₂.2.2]; exact hin)
      (by rw [u₂.other _ (by decide)]; exact h2₁)
    rwa [m₂, a0₂, hk] at h
  have hc (i : Nat) (hi : i < 8) : (⟨B, 8 * 8⟩ : Region).Contains
      (B + BitVec.ofNat 64 48 + BitVec.ofNat 64 i) 1 := by
    rw [Offset.add_add]; exact Offset.contains_base _ (by omega) (by omega)
  have hread : BlockRead s₂ (B + BitVec.ofNat 64 48) := fun i hi => by
    rw [K₂.2.1, K₂.2.2]
    exact ⟨_, List.mem_append_right _ hW, hc i hi⟩
  have hwrite : BlockWrite s₂ (B + BitVec.ofNat 64 48) := fun i hi => by
    rw [K₂.2.2]
    exact ⟨_, hW, hc i hi⟩
  -- The block.
  refine WP.mono (cryptBlock_ok k s₂ a₂ hread hwrite hk₂) fun t ⟨b, f, e⟩ => ?_
  have Kt : Keep coreWrites s t := (K₂.trans e).mono (by decide)
  have a0t : t.gpr .a0 = s.gpr .a0 := Kt.gpr (by decide)
  have ft : Frame [⟨B + BitVec.ofNat 64 48, 8⟩] s.mem t.mem := by rw [← m₂]; exact f
  have hbuf : (keyR s).Disjoint ⟨B + BitVec.ofNat 64 48, 8⟩ :=
    hkB.sub_right (Offset.sub_base B (by omega))
  have hB0 : blkAddr core B 0 = B + BitVec.ofNat 64 48 := by simp [blkAddr, slotA, core, bufSlot]
  refine ⟨(Kt.gpr (by decide)).trans hB, fun r hr => Kt.gpr (kept_apart r hr),
    ⟨⟨?_, by rw [Kt.2.1, Kt.2.2, keyR, a0t]; exact hin, by rw [keyR, a0t]; exact hd⟩,
      by rw [keyR, a0t]; exact hkB⟩,
    ft.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩, fun j hj => ?_, Kt.2.1, Kt.2.2⟩
  · rw [a0t, Proof.Idea.scheduleAt_frame ft fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hbuf, hk]
  · simp only [List.mem_singleton] at hr; subst hr
    exact Region.sub_prefix (by decide)
  · obtain rfl : j = 0 := by simpa [core] using hj
    simp only [core] at hB0
    rw [show 4 * 2 = 8 from rfl, hB0, Proof.Idea.bytesAt_eq, b, ← m₂, Proof.Idea.cipher_bytes]

/-- IDEA's core meets what the modes need. -/
def coreSpec : CoreSpec core where
  Key := Spec.Idea.Schedule
  cipher := Spec.Idea.cipher
  KeyArgs := KeyArgs
  Ready := Ready
  cipher_len _ _ := by simp [Spec.Idea.cipher, core]
  layout := layout
  keyArgs_congr h e r w _ f := keyArgs_congr h e.a0 r w f
  ready_frame h e r w _ f hs _ := ready_frame h e.a0 r w f hs
  prepare_wp := prepare_wp
  crypt_wp := crypt_wp

end VG.Proof.Idea.RISCV64.Mode
