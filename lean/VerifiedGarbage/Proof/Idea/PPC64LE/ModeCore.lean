module

public import VerifiedGarbage.Proof.Modes.PPC64LE.Core
public import VerifiedGarbage.Impl.Idea.PPC64LE.Modes
import VerifiedGarbage.Proof.Idea.ModeBytes
import VerifiedGarbage.Proof.Idea.PPC64LE.Ecb
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Idea.PPC64LE
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Idea.PPC64LE.Round
public import VerifiedGarbage.Spec.Idea
public import VerifiedGarbage.Spec.Idea.Cbc

/-!
# IDEA's core for the modes on PPC64LE

`coreSpec`: IDEA's core (`Impl.Idea.PPC64LE.core`) meets what the modes need
of a core (`Proof.Modes.PPC64LE.CoreSpec`), with the key a schedule of
subkeys, read in place through `r3`, its cipher `Spec.Idea.cipher`. The
schedule is readable and apart from the regions the mode writes
(`KeyArgs`), and from the scratch buffer (`Ready`), so nothing the mode or
the core writes changes it. The core runs ECB's block code on its buffer
(`cryptBlock_ok`).
-/

@[expose] public section

namespace VG.Proof.Idea.PPC64LE.Mode

open VG VG.PPC64LE VG.Impl.Idea.PPC64LE
open VG.Impl.Modes.PPC64LE (sb)
open VG.Proof.Modes.PPC64LE (coreRegion blkRegion blkAddr slotA CoreSpec Layout ScrIn kept)

/-- The schedule. -/
abbrev keyR (s : State) : Region := ⟨s.gpr .r3, 104⟩

/-- The schedule at `r3` is `k`, readable, and apart from the regions `rs`. -/
def KeyArgs (s : State) (rs : List Region) (k : Spec.Idea.Schedule) : Prop :=
  Spec.Idea.scheduleAt s.mem (s.gpr .r3) = k ∧ keyR s ∈ s.rd ++ s.wr ∧ ∀ r ∈ rs, (keyR s).Disjoint r

/-- The key's arguments, apart from the scratch buffer at `B` too. -/
def Ready (s : State) (B : Addr) (ws : List Region) (k : Spec.Idea.Schedule) : Prop :=
  KeyArgs s ws k ∧ (keyR s).Disjoint ⟨B, 8 * 8⟩

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Spec.Idea.Schedule} (h : KeyArgs s rs k)
    (e : s'.gpr .r3 = s.gpr .r3) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame rs s.mem s'.mem) :
    KeyArgs s' rs k := by
  obtain ⟨hk, hin, hd⟩ := h
  refine ⟨?_, by rw [hrd, hwr, keyR, e]; exact hin, by rw [keyR, e]; exact hd⟩
  rw [e, Proof.Idea.scheduleAt_frame hf hd, hk]

theorem ready_frame {s s' : State} {B : Addr} {ws : List Region} {k : Spec.Idea.Schedule}
    {rs : List Region} (h : Ready s B ws k) (e : s'.gpr .r3 = s.gpr .r3) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hf : Frame rs s.mem s'.mem) (hs : ∀ r ∈ rs, ∃ r' ∈ ws, Region.Sub r r') :
    Ready s' B ws k := by
  obtain ⟨⟨hk, hin, hd⟩, hB⟩ := h
  have hd' : ∀ r ∈ rs, (keyR s).Disjoint r := fun r hr => by
    obtain ⟨r', hr', hsub⟩ := hs r hr
    exact (hd r' hr').sub_right hsub
  refine ⟨⟨?_, by rw [hrd, hwr, keyR, e]; exact hin, by rw [keyR, e]; exact hd⟩, by rw [keyR, e]; exact hB⟩
  rw [e, Proof.Idea.scheduleAt_frame hf hd', hk]

theorem layout : Layout core := ⟨by decide, .inl rfl, by decide, by decide, by decide⟩

theorem prepare_wp {s : State} {B : Addr} {rs : List Region} {k : Spec.Idea.Schedule}
    (hB : s.gpr sb = B) (_hS : ScrIn s B core.total) (hm : (⟨B, 8 * core.total⟩ : Region) ∈ rs)
    (hk : KeyArgs s rs k) :
    WP isa core.prepare s fun s' => Ready s' B rs k ∧ s'.gpr sb = B ∧
      (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ Frame [coreRegion core B] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr :=
  wp_nil ⟨⟨hk, hk.2.2 _ hm⟩, hB, fun _ _ => rfl, Frame.refl _ _, rfl, rfl⟩

/-- The kept registers are none the core writes. -/
theorem kept_apart : ∀ r ∈ kept, r ∉ [Reg.r0, .r4, .r6, .r7, .r8, .r9, .r10, .r11, .r12] := by decide

theorem crypt_wp {s : State} {B : Addr} {ws : List Region} {k : Spec.Idea.Schedule}
    (hB : s.gpr sb = B) (hS : ScrIn s B core.total) (hR : Ready s B ws k) :
    WP isa core.crypt s fun s' => s'.gpr sb = B ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      Ready s' B ws k ∧ Frame [coreRegion core B] s.mem s'.mem ∧
      (∀ j < core.G, Spec.Aes.bytesAt s'.mem (blkAddr core B j) (4 * core.bw) =
        Spec.Idea.cipher k (Spec.Aes.bytesAt s.mem (blkAddr core B j) (4 * core.bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hfit : B.toNat + 8 * 8 ≤ 2 ^ 64 := hS.fit
  have hW : (⟨B, 8 * 8⟩ : Region) ∈ s.wr := hS.wr
  obtain ⟨⟨hk, hin, hd⟩, hkB⟩ := hR
  simp only [core]
  -- The mask.
  refine WP.seq (WP.mono (WP.keep [.r0] (Q := fun t => t.gpr .r0 = 65535 ∧ t.mem = s.mem)
    (by unfold setMask; irun; rfl) (by decide) rfl) fun s₁ ⟨⟨h0₁, m₁⟩, k₁⟩ => ?_)
  -- The buffer's address.
  refine WP.seq (wp_addi (n := sb) (by decide) (by decide) fun s₂ u₂ => wp_nil ?_)
  have a₂ : s₂.gpr .r4 = B := by
    refine u₂.gpr.trans ?_
    show s₁.gpr .r5 + _ = B
    rw [k₁.gpr (show Reg.r5 ∉ [Reg.r0] by decide), show s.gpr .r5 = B from hB]
    simp [bufSlot]
  have K₂ : Keep [.r0, .r4] s s₂ := ⟨fun r hr => by
      rw [u₂.other r fun e => hr (by rw [e]; decide), k₁.gpr fun h => hr (by
        simp only [List.mem_singleton] at h; rw [h]; decide)],
    by rw [u₂.rd, k₁.2.1], by rw [u₂.wr, k₁.2.2]⟩
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, m₁]
  have r3₂ : s₂.gpr .r3 = s.gpr .r3 := K₂.gpr (by decide)
  have hk₂ : KeyOk k s₂ := by
    have h := keyOk_of s₂ (by rw [r3₂, K₂.2.1, K₂.2.2]; exact hin)
      (by rw [u₂.other _ (by decide)]; exact h0₁)
    rwa [m₂, r3₂, hk] at h
  have hread : BlockRead s₂ B := fun i hi => by
    rw [K₂.2.1, K₂.2.2]
    exact ⟨_, List.mem_append_right _ hW, Offset.contains_base _ (show i + 1 ≤ 8 * 8 by omega) (by omega)⟩
  have hwrite : BlockWrite s₂ B := fun i hi => by
    rw [K₂.2.2]
    exact ⟨_, hW, Offset.contains_base _ (show i + 1 ≤ 8 * 8 by omega) (by omega)⟩
  -- The block.
  refine WP.mono (cryptBlock_ok k s₂ a₂ hread hwrite hk₂) fun t ⟨b, f, e⟩ => ?_
  have Kt : Keep ([.r0, .r4] ++ roundWrites) s t := K₂.trans e
  have r3t : t.gpr .r3 = s.gpr .r3 := Kt.gpr (by decide)
  have ft : Frame [⟨B, 8⟩] s.mem t.mem := by rw [← m₂]; exact f
  have hB0 : blkAddr core B 0 = B := by simp [blkAddr, slotA, core, bufSlot]
  refine ⟨Kt.gpr (by decide) |>.trans hB, fun r hr => Kt.gpr (by
      have := kept_apart r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at this ⊢; simp only [List.cons_append,
        List.nil_append, List.mem_cons, List.not_mem_nil, or_false]; omega),
    ⟨⟨?_, by rw [Kt.2.1, Kt.2.2, keyR, r3t]; exact hin, by rw [keyR, r3t]; exact hd⟩, by rw [keyR, r3t]; exact hkB⟩,
    by simp only [coreRegion, bufSlot]; exact ft, fun j hj => ?_, Kt.2.1, Kt.2.2⟩
  · rw [r3t, Proof.Idea.scheduleAt_frame ft fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hkB.sub_right (Region.sub_prefix (by decide)), hk]
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
  keyArgs_congr h e r w f := keyArgs_congr h e r w f
  ready_frame h e r w f hs _ := ready_frame h e r w f hs
  prepare_wp := prepare_wp
  crypt_wp := crypt_wp

end VG.Proof.Idea.PPC64LE.Mode
