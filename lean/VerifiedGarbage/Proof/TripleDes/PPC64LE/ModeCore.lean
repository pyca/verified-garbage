module

public import VerifiedGarbage.Proof.Modes.PPC64LE.Core
public import VerifiedGarbage.Impl.TripleDes.PPC64LE.Modes
public import VerifiedGarbage.Proof.TripleDes.CbcBlocks
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Ecb.Call
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Block
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Covers

/-!
# Triple DES's core for the modes on PPC64LE

`dirCoreSpec d`: Triple DES's core for the direction `d`
(`Impl.TripleDes.PPC64LE.dirCore d`) meets what the modes need of a core
(`Proof.Modes.PPC64LE.CoreSpec`), with the key a schedule, read in place
through `r3`, its cipher `Spec.TripleDes.cipher` for encryption and
`Spec.TripleDes.invCipher` for decryption. The schedule is readable and
apart from the regions the mode writes (`KeyArgs`), and from the scratch
buffer (`Ready`), so nothing the mode or the core writes changes it. The
block function's call is ECB's (`Ecb.call_ok`).
-/

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE.Mode

open VG VG.PPC64LE VG.Impl.TripleDes.PPC64LE
open VG.Impl.Modes.PPC64LE (sb)
open VG.Proof.Modes.PPC64LE (coreRegion blkRegion blkAddr slotA CoreSpec Layout ScrIn kept)
open VG.Spec.Aes (bytesAt)
open VG.Spec.TripleDes (Direction)
open VG.Proof.TripleDes (dirCipher bytesAt_eq ofFn_bytesAt scheduleAt_eq_of_frame)

/-- The schedule. -/
abbrev keyR (s : State) : Region := ⟨s.gpr .r3, 384⟩

/-- The schedule at `r3` is `k`, readable, and apart from the regions `rs`. -/
def KeyArgs (s : State) (rs : List Region) (k : Spec.TripleDes.Schedule) : Prop :=
  Spec.TripleDes.scheduleAt s.mem (s.gpr .r3) = k ∧ InRegions (s.rd ++ s.wr) (s.gpr .r3) 384 ∧
    ∀ r ∈ rs, (keyR s).Disjoint r

/-- The key's arguments, apart from the scratch buffer at `B` too. -/
def Ready (s : State) (B : Addr) (ws : List Region) (k : Spec.TripleDes.Schedule) : Prop :=
  KeyArgs s ws k ∧ (keyR s).Disjoint ⟨B, 8 * 72⟩

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Spec.TripleDes.Schedule} (h : KeyArgs s rs k)
    (e : s'.gpr .r3 = s.gpr .r3) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame rs s.mem s'.mem) :
    KeyArgs s' rs k := by
  obtain ⟨hk, hin, hd⟩ := h
  refine ⟨?_, by rw [hrd, hwr, e]; exact hin, by rw [keyR, e]; exact hd⟩
  rw [e, scheduleAt_eq_of_frame _ hf hd, hk]

theorem ready_frame {s s' : State} {B : Addr} {ws : List Region} {k : Spec.TripleDes.Schedule}
    {rs : List Region} (h : Ready s B ws k) (e : s'.gpr .r3 = s.gpr .r3) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hf : Frame rs s.mem s'.mem) (hs : ∀ r ∈ rs, ∃ r' ∈ ws, Region.Sub r r') :
    Ready s' B ws k := by
  obtain ⟨⟨hk, hin, hd⟩, hB⟩ := h
  have hd' : ∀ r ∈ rs, (keyR s).Disjoint r := fun r hr => by
    obtain ⟨r', hr', hsub⟩ := hs r hr
    exact (hd r' hr').sub_right hsub
  refine ⟨⟨?_, by rw [hrd, hwr, e]; exact hin, by rw [keyR, e]; exact hd⟩, by rw [keyR, e]; exact hB⟩
  rw [e, scheduleAt_eq_of_frame _ hf hd', hk]

theorem layout (d : Direction) : Layout (dirCore d) :=
  ⟨by cases d <;> decide, .inl rfl, by cases d <;> decide, by cases d <;> decide, by cases d <;> decide⟩

theorem prepare_wp (d : Direction) {s : State} {B : Addr} {rs : List Region} {k : Spec.TripleDes.Schedule}
    (_hB : s.gpr sb = B) (_hS : ScrIn s B (dirCore d).total) (hm : (⟨B, 8 * (dirCore d).total⟩ : Region) ∈ rs)
    (hk : KeyArgs s rs k) :
    WP isa (dirCore d).prepare s fun s' => Ready s' B rs k ∧ s'.gpr sb = B ∧
      (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ Frame [coreRegion (dirCore d) B] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr :=
  wp_nil ⟨⟨hk, hk.2.2 _ hm⟩, _hB, fun _ _ => rfl, Frame.refl _ _, rfl, rfl⟩

theorem dirCipher_bytes (d : Direction) (k : Spec.TripleDes.Schedule) (m : Mem) (p : Addr) :
    dirCipher d k (Spec.Aes.bytesAt m p 8) = (blockResult k d (Spec.TripleDes.blockAt m p)).toList := by
  cases d <;> simp only [dirCipher, Spec.TripleDes.cipher, Spec.TripleDes.invCipher, blockResult, ofFn_bytesAt]

/-- Ecb's kept registers and the callee-saved ones are the modes'. -/
theorem kept_sub : ∀ r ∈ kept, r ∈ Ecb.kept ∨ r ∈ preserved := by decide

theorem crypt_wp (d : Direction) {s : State} {B : Addr} {ws : List Region} {k : Spec.TripleDes.Schedule}
    (hB : s.gpr sb = B) (hS : ScrIn s B (dirCore d).total) (hR : Ready s B ws k) :
    WP isa (dirCore d).crypt s fun s' => s'.gpr sb = B ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      Ready s' B ws k ∧ Frame [coreRegion (dirCore d) B] s.mem s'.mem ∧
      (∀ j < (dirCore d).G, bytesAt s'.mem (blkAddr (dirCore d) B j) (4 * (dirCore d).bw) =
        dirCipher d k (bytesAt s.mem (blkAddr (dirCore d) B j) (4 * (dirCore d).bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hfit : B.toNat + 8 * 72 ≤ 2 ^ 64 := hS.fit
  have hW : (⟨B, 8 * 72⟩ : Region) ∈ s.wr := hS.wr
  obtain ⟨⟨hk, hin, hd⟩, hkB⟩ := hR
  simp only [dirCore]
  refine WP.seq (wp_addi (n := sb) (by decide) (by decide) fun s₁ u₁ => wp_nil ?_)
  have r4₁ : s₁.gpr .r4 = B + BitVec.ofNat 64 512 := by rw [u₁.gpr, hB]; rfl
  have g₁ : ∀ r, r ≠ .r4 → s₁.gpr r = s.gpr r := u₁.other
  have m₁ : s₁.mem = s.mem := u₁.mem
  have rd₁ : s₁.rd = s.rd := u₁.rd
  have wr₁ : s₁.wr = s.wr := u₁.wr
  have r3₁ : s₁.gpr .r3 = s.gpr .r3 := g₁ _ (by decide)
  have r5₁ : s₁.gpr .r5 = B := by rw [g₁ _ (by decide)]; exact hB
  have cw : VG.Covers [⟨s₁.gpr .r4, 8⟩, ⟨s₁.gpr .r5, 512⟩] s₁.wr := VG.Covers.of_sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨B, 8 * 72⟩, by rw [wr₁]; exact hW, 512, r4₁, by show 512 + 8 ≤ 8 * 72; omega⟩
    · exact ⟨⟨B, 8 * 72⟩, by rw [wr₁]; exact hW, 0, by simp [r5₁], by show 0 + 512 ≤ 8 * 72; omega⟩
  have hp : Ecb.CallPre s₁ :=
    ⟨VG.Covers.cons (by rw [r3₁, rd₁, wr₁]; exact VG.Covers.one hin) (VG.Covers.right cw), cw,
      by rw [r3₁, r5₁]; exact hkB.sub_right (Region.sub_prefix (by decide)),
      by rw [r4₁, r5₁]; exact VG.Offset.disjoint_base _ (by decide) (by omega_using [hfit])⟩
  refine WP.mono (Ecb.call_ok d s₁ hp) fun s₂ h₂ => ?_
  have g₂ : ∀ r ∈ kept, s₂.gpr r = s.gpr r := fun r hr => by
    have h4 : r ≠ .r4 := by revert hr; decide +revert
    rcases kept_sub r hr with h | h
    · rw [h₂.reg r h, g₁ r h4]
    · rw [h₂.callee r h, g₁ r h4]
  have r3₂ : s₂.gpr .r3 = s.gpr .r3 := g₂ _ (by decide)
  have sub₂ : ∀ r ∈ [(⟨s₁.gpr .r4, 8⟩ : Region), ⟨s₁.gpr .r5, 512⟩], Region.Sub r ⟨B, 8 * 72⟩ := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [r4₁]; exact VG.Offset.sub_base _ (by decide)
    · rw [r5₁]; exact Region.sub_prefix (by decide)
  have f₂ : Frame [⟨s₁.gpr .r4, 8⟩, ⟨s₁.gpr .r5, 512⟩] s.mem s₂.mem := by rw [← m₁]; exact h₂.mem
  have sched : Spec.TripleDes.scheduleAt s₂.mem (s₂.gpr .r3) = k := by
    rw [r3₂, scheduleAt_eq_of_frame _ f₂ fun r hr => hkB.sub_right (sub₂ r hr), hk]
  refine ⟨by rw [show sb = .r5 from rfl, h₂.reg _ (by decide), r5₁], g₂,
    ⟨⟨sched, by rw [h₂.rd, h₂.wr, rd₁, wr₁, r3₂]; exact hin, by rw [keyR, r3₂]; exact hd⟩,
      by rw [keyR, r3₂]; exact hkB⟩, f₂.sub fun r hr => ?_, fun j hj => ?_,
    by rw [h₂.rd, rd₁], by rw [h₂.wr, wr₁]⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_singleton_self _, by
        rw [r4₁]; exact VG.Offset.sub_base _ (by show 512 + 8 ≤ 8 * (bufSlot + 1); decide)⟩
    · exact ⟨_, List.mem_singleton_self _, by
        rw [r5₁]; exact Region.sub_prefix (by show 512 ≤ 8 * (bufSlot + 1); decide)⟩
  · obtain rfl : j = 0 := by omega
    have e : blkAddr (dirCore d) B 0 = s₁.gpr .r4 := by
      rw [r4₁]; simp [blkAddr, slotA, dirCore, bufSlot]
    simp only [dirCore] at e
    rw [e, bytesAt_eq, h₂.output, dirCipher_bytes, m₁, r3₁, hk]

/-- Triple DES's core for the direction `d` meets what the modes need. -/
def dirCoreSpec (d : Direction) : CoreSpec (dirCore d) where
  Key := Spec.TripleDes.Schedule
  cipher := dirCipher d
  KeyArgs := KeyArgs
  Ready := Ready
  cipher_len _ _ := by cases d <;> simp [dirCipher, Spec.TripleDes.cipher, Spec.TripleDes.invCipher, dirCore]
  layout := layout d
  keyArgs_congr h e r w f := keyArgs_congr h e r w f
  ready_frame h e r w f hs _ := ready_frame h e r w f hs
  prepare_wp := prepare_wp d
  crypt_wp := crypt_wp d

end VG.Proof.TripleDes.PPC64LE.Mode
