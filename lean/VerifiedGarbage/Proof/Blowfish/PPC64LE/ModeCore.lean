module

public import VerifiedGarbage.Proof.Modes.PPC64LE.Core
public import VerifiedGarbage.Impl.Blowfish.PPC64LE.Modes
public import VerifiedGarbage.Proof.Blowfish.ModeBytes
import VerifiedGarbage.Proof.Blowfish.PPC64LE.Ecb
import VerifiedGarbage.Proof.Blowfish.Schedule
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Blowfish.PPC64LE
public import VerifiedGarbage.Proof.Blowfish.PPC64LE.Run
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.Proof.Framework.Semantics

/-!
# Blowfish's core for the modes on PPC64LE

`dirCoreSpec up`: Blowfish's core (`Impl.Blowfish.PPC64LE.dirCore up`) meets
what the modes need of a core (`Proof.Modes.PPC64LE.CoreSpec`), with the key
a schedule, read in place through `r3`, its cipher `Proof.Blowfish.dirCipher
up`. The schedule is readable and apart from the regions the mode writes
(`KeyArgs`), and from the scratch buffer (`Ready`), so nothing the mode or
the core writes changes it. The core runs ECB's block function on its
buffer (`loadBlock_run`, `cipher_run`, `storeBlock_run`), with our caller's
`r14`–`r17` saved in its first four slots through `r6`.
-/

@[expose] public section

namespace VG.Proof.Blowfish.PPC64LE.Mode

open VG VG.PPC64LE VG.Impl.Blowfish.PPC64LE VG.Spec.Blowfish VG.Proof.Blowfish
open VG.Impl.Modes.PPC64LE (sb)
open VG.Proof.Modes.PPC64LE (coreRegion blkRegion blkAddr slotA CoreSpec Layout ScrIn kept)

/-- The schedule. -/
abbrev keyR (s : State) : Region := ⟨s.gpr .r3, 4168⟩

/-- The schedule at `r3` is `k`, readable, and apart from the regions `rs`. -/
def KeyArgs (s : State) (rs : List Region) (k : Schedule) : Prop :=
  scheduleAt s.mem (s.gpr .r3) = k ∧ keyR s ∈ s.rd ++ s.wr ∧ ∀ r ∈ rs, (keyR s).Disjoint r

/-- The key's arguments, apart from the scratch buffer at `B` too. -/
def Ready (s : State) (B : Addr) (ws : List Region) (k : Schedule) : Prop :=
  KeyArgs s ws k ∧ (keyR s).Disjoint ⟨B, 8 * 12⟩

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Schedule} (h : KeyArgs s rs k)
    (e : s'.gpr .r3 = s.gpr .r3) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame rs s.mem s'.mem) :
    KeyArgs s' rs k := by
  obtain ⟨hk, hin, hd⟩ := h
  refine ⟨?_, by rw [hrd, hwr, keyR, e]; exact hin, by rw [keyR, e]; exact hd⟩
  rw [e, scheduleAt_eq_of_frame _ hf hd, hk]

theorem ready_frame {s s' : State} {B : Addr} {ws : List Region} {k : Schedule}
    {rs : List Region} (h : Ready s B ws k) (e : s'.gpr .r3 = s.gpr .r3) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hf : Frame rs s.mem s'.mem) (hs : ∀ r ∈ rs, ∃ r' ∈ ws, Region.Sub r r') :
    Ready s' B ws k := by
  obtain ⟨⟨hk, hin, hd⟩, hB⟩ := h
  have hd' : ∀ r ∈ rs, (keyR s).Disjoint r := fun r hr => by
    obtain ⟨r', hr', hsub⟩ := hs r hr
    exact (hd r' hr').sub_right hsub
  refine ⟨⟨?_, by rw [hrd, hwr, keyR, e]; exact hin, by rw [keyR, e]; exact hd⟩, by rw [keyR, e]; exact hB⟩
  rw [e, scheduleAt_eq_of_frame _ hf hd', hk]

theorem layout (up : Bool) : Layout (dirCore up) :=
  ⟨by cases up <;> decide, .inl rfl, by cases up <;> decide, by cases up <;> decide, by cases up <;> decide⟩

theorem prepare_wp (up : Bool) {s : State} {B : Addr} {rs : List Region} {k : Schedule}
    (hB : s.gpr sb = B) (_hS : ScrIn s B (dirCore up).total) (hm : (⟨B, 8 * (dirCore up).total⟩ : Region) ∈ rs)
    (hk : KeyArgs s rs k) :
    WP isa (dirCore up).prepare s fun s' => Ready s' B rs k ∧ s'.gpr sb = B ∧
      (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ Frame [coreRegion (dirCore up) B] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr :=
  wp_nil ⟨⟨hk, hk.2.2 _ hm⟩, hB, fun _ _ => rfl, Frame.refl _ _, rfl, rfl⟩

theorem saved_fst : saved.map Prod.fst = [.r14, .r15, .r16, .r17] := rfl

/-- The registers the core writes, but `r14`–`r17`, which it restores. -/
def cryptRegs : List Reg := [.r0, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17]

theorem crypt_wp (up : Bool) {s : State} {B : Addr} {ws : List Region} {k : Schedule}
    (hB : s.gpr sb = B) (hS : ScrIn s B (dirCore up).total) (hR : Ready s B ws k) :
    WP isa (dirCore up).crypt s fun s' => s'.gpr sb = B ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      Ready s' B ws k ∧ Frame [coreRegion (dirCore up) B] s.mem s'.mem ∧
      (∀ j < (dirCore up).G, Spec.Aes.bytesAt s'.mem (blkAddr (dirCore up) B j) (4 * (dirCore up).bw) =
        dirCipher up k (Spec.Aes.bytesAt s.mem (blkAddr (dirCore up) B j) (4 * (dirCore up).bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hfit : B.toNat + 8 * 12 ≤ 2 ^ 64 := hS.fit
  have hW : (⟨B, 8 * 12⟩ : Region) ∈ s.wr := hS.wr
  obtain ⟨⟨hk, hin, hd⟩, hkB⟩ := hR
  have slotIn : ∀ (u : State), u.wr = s.wr → ∀ o, o + 8 ≤ 96 → InRegions u.wr (B + BitVec.ofNat 64 o) 8 :=
    fun u hu o ho => ⟨_, by rw [hu]; exact hW, Offset.contains_base _ (by omega) (by omega)⟩
  have slotRd : ∀ (u : State), u.rd = s.rd → u.wr = s.wr → ∀ o n, o + n ≤ 96 →
      InRegions (u.rd ++ u.wr) (B + BitVec.ofNat 64 o) n := fun u hr hu o n ho =>
    ⟨_, by rw [hr, hu]; exact List.mem_append_right _ hW, Offset.contains_base _ (by omega) (by omega)⟩
  simp only [dirCore, modeCrypt]
  -- Our caller's `r14`–`r17`, through `r6`.
  refine WP.seq (wp_mr fun s₁ u₁ => ?_)
  have r6₁ : s₁.gpr .r6 = B := by rw [u₁.gpr]; exact hB
  rw [save_eq, ← List.append_nil (Spill.saveCode .r6 saved)]
  refine Spill.save_ok (by decide) saved_fits (fun p hp => by
    rw [r6₁, u₁.wr]; exact slotIn s rfl _ (by have := saved_lt p hp; omega)) (wp_nil ?_)
  let M₀ := Spill.saveMem s₁.mem (s₁.gpr .r6) s₁.gpr saved
  let s₂ : State := { s₁ with mem := M₀ }
  have F₀ : Frame [⟨B, 32⟩] s.mem M₀ := by
    rw [← u₁.mem, ← r6₁]; exact Spill.saveMem_frame_base (fun p hp => saved_lt p hp) (by decide) _ _ _
  have hsv : Spill.Saved B s₁.gpr saved M₀ := by
    rw [← r6₁]; exact Spill.saveMem_saved (by decide) _ _ _
  -- The block's pointer, and `r0 = 0`.
  refine WP.seq (wp_li (by decide) fun s₃ u₃ => wp_addi (by decide) (by decide) fun s₄ u₄ => wp_nil ?_)
  have g₄ : ∀ r, r ≠ .r0 → r ≠ .r16 → s₄.gpr r = s₁.gpr r := fun r h0 h16 => by
    rw [u₄.other r h16, u₃.other r h0]
  have z₄ : s₄.gpr .r0 = 0#64 := by rw [u₄.other _ (by decide)]; exact u₃.gpr
  have p₄ : s₄.gpr .r16 = B + BitVec.ofNat 64 32 := by
    refine u₄.gpr.trans ?_
    rw [u₃.other _ (by decide)]; show s₁.gpr .r6 + _ = _; rw [r6₁]; rfl
  have rd₄ : s₄.rd = s.rd := by rw [u₄.rd, u₃.rd]; exact u₁.rd
  have wr₄ : s₄.wr = s.wr := by rw [u₄.wr, u₃.wr]; exact u₁.wr
  have m₄ : s₄.mem = M₀ := by rw [u₄.mem, u₃.mem]
  -- The block into the halves.
  have q4 : InRegions (s₄.rd ++ s₄.wr) (B + BitVec.ofNat 64 32 + BitVec.ofNat 64 4) 4 := by
    rw [Offset.add_add]; exact slotRd _ rd₄ wr₄ 36 4 (by decide)
  refine WP.seq (WP.mono (WP.keep [.r4, .r5, .r12] (loadBlock_run s₄ p₄ z₄ (slotRd _ rd₄ wr₄ 32 4 (by decide)) q4)
    (by decide) rfl) fun s₅ ⟨⟨l₅, h₅, m₅⟩, k₅⟩ => ?_)
  have r3₅ : s₅.gpr .r3 = s.gpr .r3 := by
    rw [k₅.gpr (by decide), g₄ _ (by decide) (by decide), u₁.other _ (by decide)]
  have E : LookEnv s₅ := by
    refine ⟨fun o ho => ?_, by rw [k₅.gpr (by decide)]; exact z₄⟩
    rw [r3₅, k₅.2.1, k₅.2.2, rd₄, wr₄]
    exact ⟨_, hin, Offset.contains_base _ ho (by omega)⟩
  -- The block function.
  refine WP.seq (WP.mono (cipher_run E up) fun s₆ ⟨c₆, k₆, m₆⟩ => ?_)
  have rd₆ : s₆.rd = s.rd := by rw [k₆.2.1, k₅.2.1, rd₄]
  have wr₆ : s₆.wr = s.wr := by rw [k₆.2.2, k₅.2.2, wr₄]
  have p₆ : s₆.gpr .r16 = B + BitVec.ofNat 64 32 := by rw [k₆.gpr (by decide), k₅.gpr (by decide), p₄]
  have z₆ : s₆.gpr .r0 = 0#64 := by rw [k₆.gpr (by decide), k₅.gpr (by decide), z₄]
  have q4' : InRegions s₆.wr (B + BitVec.ofNat 64 32 + BitVec.ofNat 64 4) 4 := by
    rw [Offset.add_add]
    exact ⟨_, by rw [wr₆]; exact hW, Offset.contains_base _ (show 36 + 4 ≤ 96 by decide) (by omega)⟩
  -- The halves back to the block.
  refine WP.seq (WP.mono (storeBlock_run s₆ p₆ z₆
    ⟨_, by rw [wr₆]; exact hW, Offset.contains_base _ (show 32 + 4 ≤ 96 by decide) (by omega)⟩ q4')
    fun s₇ ⟨m₇, _, _, k₇⟩ => ?_)
  have r6₇ : s₇.gpr .r6 = B := by
    rw [k₇.gpr (by decide), k₆.gpr (by decide), k₅.gpr (by decide), g₄ _ (by decide) (by decide), r6₁]
  have rd₇ : s₇.rd = s.rd := by rw [k₇.2.1, rd₆]
  have wr₇ : s₇.wr = s.wr := by rw [k₇.2.2, wr₆]
  -- The memory: the saves and the block.
  have Fblk : Frame [⟨B + BitVec.ofNat 64 32, 8⟩] s₆.mem s₇.mem := by rw [m₇]; exact stored_frame _ _ _ _
  have F₇ : Frame [⟨B, 40⟩] s.mem s₇.mem := by
    have a : Frame [⟨B, 40⟩] s.mem s₆.mem := by
      rw [m₆, m₅, m₄]; exact F₀.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
    exact a.trans (Fblk.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by decide)⟩)
  have hsv₇ : Spill.Saved B s₁.gpr saved s₇.mem := by
    refine (hsv.frame (by rw [← m₄, ← m₅, ← m₆]; exact Fblk)) fun p hp r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (.inl (by have := saved_lt p hp; omega)) (by have := saved_lt p hp; omega) (by omega)
  -- `sb` and our caller's registers back.
  refine wp_mr fun s₈ u₈ => ?_
  rw [restore_eq]
  refine WP.mono (Spill.restore_wp (by decide) (by rw [u₈.other _ (by decide), r6₇]) saved_fits (by decide)
    (fun p hp => by
      rw [u₈.rd, u₈.wr]; exact slotRd _ rd₇ wr₇ _ 8 (by have := saved_lt p hp; omega))
    (by rw [u₈.mem]; exact hsv₇)) fun s' R => ?_
  have K₇ : Keep cryptRegs s s₇ := by
    have Kb : Keep cryptRegs s₄ s₇ := ((k₅.trans k₆).trans k₇).mono (by decide)
    refine ⟨fun r hr => ?_, rd₇, wr₇⟩
    have h0 : r ≠ .r0 := by rintro rfl; exact hr (by decide)
    have h6 : r ≠ .r6 := by rintro rfl; exact hr (by decide)
    have h16 : r ≠ .r16 := by rintro rfl; exact hr (by decide)
    rw [Kb.gpr hr, g₄ r h0 h16, u₁.other r h6]
  have sched : scheduleAt s'.mem (s'.gpr .r3) = k := by
    rw [R.mem, u₈.mem, R.other _ (by decide), u₈.other _ (by decide), K₇.gpr (by decide),
      scheduleAt_eq_of_frame _ F₇ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hkB.sub_right (Region.sub_prefix (by decide)), hk]
  have r3' : s'.gpr .r3 = s.gpr .r3 := by rw [R.other _ (by decide), u₈.other _ (by decide), K₇.gpr (by decide)]
  refine ⟨?_, fun r hr => ?_, ⟨⟨sched, ?_, by rw [keyR, r3']; exact hd⟩, by rw [keyR, r3']; exact hkB⟩,
    by rw [R.mem, u₈.mem]; exact F₇, fun j hj => ?_, by rw [R.rd, u₈.rd, rd₇], by rw [R.wr, u₈.wr, wr₇]⟩
  · exact (R.other _ (by decide)).trans (u₈.gpr.trans r6₇)
  · by_cases hs : r ∈ saved.map Prod.fst
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hs
      have h6 : p.1 ≠ .r6 := by
        simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl <;> decide
      rw [R.gpr p hp, u₁.other _ h6]
    · rw [saved_fst] at hs
      have h5 : r ≠ .r5 := by rintro rfl; exact absurd hr (by decide)
      have hc : r ∉ cryptRegs := by
        intro hc
        simp only [cryptRegs, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          first | exact absurd hr (by decide) | exact hs (by decide)
      rw [R.other r (by rw [saved_fst]; exact hs), u₈.other r h5, K₇.gpr hc]
  · rw [R.rd, R.wr, u₈.rd, u₈.wr, rd₇, wr₇, keyR, r3']; exact hin
  · obtain rfl : j = 0 := by simpa [dirCore] using hj
    have e : blkAddr (dirCore up) B 0 = B + BitVec.ofNat 64 32 := by simp [blkAddr, slotA, dirCore, bufSlot]
    simp only [dirCore] at e
    have e1 := congrArg Prod.fst c₆
    have e2 := congrArg Prod.snd c₆
    simp only at e1 e2
    have hb : blockAt s₄.mem (B + BitVec.ofNat 64 32) = blockAt s.mem (B + BitVec.ofNat 64 32) := by
      rw [m₄]; exact blockAt_frame F₀ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint_base _ (by decide) (by omega)
    have hk₄ : scheduleAt s₄.mem (s.gpr .r3) = k := by
      rw [m₄, scheduleAt_eq_of_frame _ F₀ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hkB.sub_right (Region.sub_prefix (by decide)), hk]
    rw [e, show 4 * 2 = 8 from rfl, R.mem, u₈.mem, bytesAt_eq, m₇, stored_block, e1, e2, l₅, h₅, m₅, r3₅, hb, hk₄,
      ← blockOut_eq, dirCipher_bytes]
    cases up <;> rfl

/-- Blowfish's core in the direction `up` meets what the modes need. -/
def dirCoreSpec (up : Bool) : CoreSpec (dirCore up) where
  Key := Schedule
  cipher := dirCipher up
  KeyArgs := KeyArgs
  Ready := Ready
  cipher_len k b := dirCipher_len up k b
  layout := layout up
  keyArgs_congr h e r w _ f := keyArgs_congr h e.r3 r w f
  ready_frame h e r w _ f hs _ := ready_frame h e.r3 r w f hs
  prepare_wp := prepare_wp up
  crypt_wp := crypt_wp up

end VG.Proof.Blowfish.PPC64LE.Mode
