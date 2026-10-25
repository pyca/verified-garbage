module

public import VerifiedGarbage.Proof.Modes.PPC64LE.Core
public import VerifiedGarbage.Impl.Seed.PPC64LE.Modes
public import VerifiedGarbage.Proof.Seed.ModeBytes
import VerifiedGarbage.Proof.Seed.PPC64LE.Ecb
import VerifiedGarbage.Proof.Seed.PPC64LE.Setup
import VerifiedGarbage.Proof.Seed.Rounds
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# SEED's core for the modes on PPC64LE

`dirCoreSpec d`: SEED's core for the direction `d`
(`Impl.Seed.PPC64LE.dirCore d`) meets what the modes need of a core
(`Proof.Modes.PPC64LE.CoreSpec`), with the key a schedule, read in place
through `r3`, its cipher `Proof.Seed.dirCipher d`. The schedule is
readable and apart from the regions the mode writes (`KeyArgs`), and from
the scratch buffer (`Ready`), so nothing the mode or the core writes changes
it.

The core (`crypt_ok`) is ECB's batch taken apart (`Batch.lean`): the copy in
of one block (`copyIn_loop`), the rounds (`rounds_ok`) and the copy out
(`copyOut_loop`), around which it saves and restores the caller's
`r14`–`r28` (`stores_ok`, `loads_ok`) and keeps the modes' `r29`–`r31` in
`r4`–`r6`.
-/

@[expose] public section

namespace VG.Proof.Seed.PPC64LE.Mode

open VG VG.PPC64LE VG.Impl.Seed.PPC64LE VG.Proof.Seed.PPC64LE VG.PPC64LE.RegUpd
open VG.Proof.Modes.PPC64LE (coreRegion blkRegion blkAddr slotA CoreSpec Layout ScrIn kept)
open VG.Spec.Seed (Direction)
open VG.Spec.Aes (bytesAt)

/-- The schedule. -/
abbrev keyR (s : State) : Region := ⟨s.gpr .r3, 128⟩

/-- The schedule at `r3` is `k`, readable, and apart from the regions `rs`. -/
def KeyArgs (s : State) (rs : List Region) (k : Spec.Seed.Schedule) : Prop :=
  Spec.Seed.scheduleAt s.mem (s.gpr .r3) = k ∧ keyR s ∈ s.rd ∧ ∀ r ∈ rs, (keyR s).Disjoint r

/-- The key's arguments, apart from the scratch buffer at `B` too. -/
def Ready (s : State) (B : Addr) (ws : List Region) (k : Spec.Seed.Schedule) : Prop :=
  KeyArgs s ws k ∧ (keyR s).Disjoint ⟨B, 8 * (bufSlot + 8)⟩

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Spec.Seed.Schedule} (h : KeyArgs s rs k)
    (e : s'.gpr .r3 = s.gpr .r3) (hrd : s'.rd = s.rd) (hf : Frame rs s.mem s'.mem) :
    KeyArgs s' rs k := by
  obtain ⟨hk, hin, hd⟩ := h
  refine ⟨?_, by rw [hrd, keyR, e]; exact hin, by rw [keyR, e]; exact hd⟩
  rw [e, Proof.Seed.scheduleAt_frame hf hd, hk]

theorem ready_frame {s s' : State} {B : Addr} {ws : List Region} {k : Spec.Seed.Schedule}
    {rs : List Region} (h : Ready s B ws k) (e : s'.gpr .r3 = s.gpr .r3) (hrd : s'.rd = s.rd)
    (hf : Frame rs s.mem s'.mem) (hs : ∀ r ∈ rs, ∃ r' ∈ ws, Region.Sub r r') :
    Ready s' B ws k := by
  obtain ⟨⟨hk, hin, hd⟩, hB⟩ := h
  have hd' : ∀ r ∈ rs, (keyR s).Disjoint r := fun r hr => by
    obtain ⟨r', hr', hsub⟩ := hs r hr
    exact (hd r' hr').sub_right hsub
  refine ⟨⟨?_, by rw [hrd, keyR, e]; exact hin, by rw [keyR, e]; exact hd⟩, by rw [keyR, e]; exact hB⟩
  rw [e, Proof.Seed.scheduleAt_frame hf hd', hk]

/-- The key stays ready through what the core writes, its slots. -/
theorem ready_core {s s' : State} {B : Addr} {ws : List Region} {k : Spec.Seed.Schedule}
    (h : Ready s B ws k) (e : s'.gpr .r3 = s.gpr .r3) (hrd : s'.rd = s.rd)
    (hf : Frame [⟨B, 8 * (bufSlot + 2)⟩] s.mem s'.mem) : Ready s' B ws k := by
  obtain ⟨⟨hk, hin, hd⟩, hB⟩ := h
  refine ⟨⟨?_, by rw [hrd, keyR, e]; exact hin, by rw [keyR, e]; exact hd⟩, by rw [keyR, e]; exact hB⟩
  rw [e, Proof.Seed.scheduleAt_frame hf fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hB.sub_right (Region.sub_prefix (by omega_arith)), hk]

theorem layout (d : Direction) : Layout (dirCore d) :=
  ⟨by cases d <;> decide, .inr rfl, by cases d <;> decide, by cases d <;> decide, by cases d <;> decide⟩

theorem prepare_wp (d : Direction) {s : State} {B : Addr} {rs : List Region} {k : Spec.Seed.Schedule}
    (hB : s.gpr .r5 = B) (_hS : ScrIn s B (dirCore d).total)
    (hm : (⟨B, 8 * (dirCore d).total⟩ : Region) ∈ rs) (hk : KeyArgs s rs k) :
    WP isa (dirCore d).prepare s fun s' => Ready s' B rs k ∧ s'.gpr .r5 = B ∧
      (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ Frame [coreRegion (dirCore d) B] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr :=
  wp_nil ⟨⟨hk, hk.2.2 _ hm⟩, hB, fun _ _ => rfl, Frame.refl _ _, rfl, rfl⟩

/-! ## The block -/

/-- The buffer's address. -/
abbrev bufA (B : Addr) : Addr := B + BitVec.ofNat 64 (8 * bufSlot)

/-- The block function in the direction `d`, on the modes' blocks. -/
private theorem dirCipher_bytes (d : Direction) (k : Spec.Seed.Schedule) (m : Mem) (p : Addr) :
    Proof.Seed.dirCipher d k (bytesAt m p 16) = (cipher d k (Spec.Seed.blockAt m p)).toList := by
  have e : (Vector.ofFn fun i : Fin 16 => (Spec.Seed.blockAt m p).toList.getD i.val 0) =
      Spec.Seed.blockAt m p := by
    apply Vector.ext; intro i hi; simp
  cases d <;> simp only [Proof.Seed.dirCipher, Spec.Seed.cipher, Spec.Seed.invCipher, cipher,
    Proof.Seed.bytesAt_eq, e]

theorem coreIn_eq (d : Direction) : coreIn d =
    [Impl.Aes.PPC64LE.movR .r8 .r5] ++
      (callerRegs.map fun p => (p.2, p.1)).map (fun p => Impl.Aes.PPC64LE.stS p.1 p.2) ++
      ([.addi .r3 .r3 (keyStart d), .li .r10 1, .addi .r6 .r8 (8 * bufSlot),
        Impl.Aes.PPC64LE.movR .r7 .r8] : List Instr) := rfl

theorem coreOut_eq (d : Direction) : coreOut d =
    ([.subi .r3 .r3 (keyStart d), Impl.Aes.PPC64LE.movR .r5 .r8] : List Instr) ++
      callerRegs.map (fun p => Impl.Aes.PPC64LE.ldS p.1 p.2) := rfl

theorem callerRegs_ok : ∀ p ∈ callerRegs, p.2 < scratchSlots ∧ p.1 ≠ .r8 ∧ 112 ≤ p.2 := by decide

/-- The caller's registers the core saves: those `preserved` but the modes'. -/
theorem callerRegs_kept : ∀ r ∈ kept, r ≠ .r29 → r ≠ .r30 → r ≠ .r31 → r ≠ .r3 → r ≠ .r2 →
    ∃ p ∈ callerRegs, p.1 = r := by decide

theorem not_callerRegs : ∀ r ∈ [Reg.r2, .r3, .r5, .r29, .r30, .r31], ∀ p ∈ callerRegs, p.1 ≠ r := by
  decide

/-- What the core does to its block, and keeps. -/
theorem crypt_ok (d : Direction) {s : State} {B : Addr} (hB : s.gpr .r5 = B)
    (hS : ScrIn s B (bufSlot + 8)) (hk : (keyR s).Disjoint ⟨B, 8 * (bufSlot + 8)⟩)
    (hkin : keyR s ∈ s.rd) :
    WP isa (coreCrypt d) s fun s' => s'.gpr .r5 = B ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      Frame [⟨B, 8 * (bufSlot + 2)⟩] s.mem s'.mem ∧
      bytesAt s'.mem (bufA B) 16 =
        Proof.Seed.dirCipher d (Spec.Seed.scheduleAt s.mem (s.gpr .r3)) (bytesAt s.mem (bufA B) 16) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  let P := bufA B
  have hbs : bufSlot = 130 := rfl
  have hsc : scratchSlots = 130 := rfl
  have hfit : B.toNat + 8 * (bufSlot + 8) ≤ 2 ^ 64 := hS.fit
  have hW : (⟨B, 8 * (bufSlot + 8)⟩ : Region) ∈ s.wr := hS.wr
  -- The setup: the bases, the caller's registers saved, the key pointer.
  let s₁ := s.write .r8 (s.gpr .r5)
  have r8₁ : s₁.gpr .r8 = B := by simp [s₁, gpr_write, hB]
  have g₁ : ∀ r, r ≠ .r8 → s₁.gpr r = s.gpr r := fun r hr => gpr_write_of_ne _ _ hr
  have room₁ : Room s₁ := ⟨8 * (bufSlot + 8), by omega_arith, by rw [r8₁]; exact hW⟩
  have scr₁ : scratchR s₁ = ⟨B, 8 * scratchSlots⟩ := by simp only [scratchR, r8₁]
  obtain ⟨s₂, e₂, g₂, rd₂, wr₂, sp₂, f₂, set₂, -⟩ := stores_ok room₁
    (callerRegs.map fun p => (p.2, p.1)) (by decide) (by decide)
  let s₃ := (((s₂.write .r3 (s₂.gpr .r3 + BitVec.ofNat 64 (keyStart d))).write .r10 (BitVec.ofNat 64 1)).write
    .r6 (B + BitVec.ofNat 64 (8 * bufSlot))).write .r7 B
  have e₃ : runBlock isa (coreIn d) s = some s₃ := by
    rw [coreIn_eq]
    refine runBlock_trans (runBlock_trans (by rw [runBlock_cons, exec_movR, runStep_some, runBlock_nil]) e₂) ?_
    rw [runBlock_cons, exec_addi' (keyStart_lt d), runStep_some, runBlock_cons, exec_li (by decide),
      runStep_some, runBlock_cons, exec_addi' (by decide), runStep_some, runBlock_cons, exec_movR,
      runStep_some, runBlock_nil]
    simp only [s₃, gpr_write_of_ne _ _ (show Reg.r8 ≠ .r10 by decide),
      gpr_write_of_ne _ _ (show Reg.r8 ≠ .r3 by decide), gpr_write_of_ne _ _ (show Reg.r8 ≠ .r6 by decide),
      g₂, r8₁]
  have G₃ : ∀ r, r ≠ .r3 → r ≠ .r6 → r ≠ .r7 → r ≠ .r8 → r ≠ .r10 → s₃.gpr r = s.gpr r := by
    intro r a b c e f
    simp only [s₃, gpr_write_of_ne _ _ c, gpr_write_of_ne _ _ b, gpr_write_of_ne _ _ f,
      gpr_write_of_ne _ _ a, g₂, g₁ r e]
  have r8₃ : s₃.gpr .r8 = B := by
    simp only [s₃, gpr_write_of_ne _ _ (show Reg.r8 ≠ .r7 by decide),
      gpr_write_of_ne _ _ (show Reg.r8 ≠ .r6 by decide), gpr_write_of_ne _ _ (show Reg.r8 ≠ .r10 by decide),
      gpr_write_of_ne _ _ (show Reg.r8 ≠ .r3 by decide), g₂, r8₁]
  have r3₃ : s₃.gpr .r3 = s.gpr .r3 + BitVec.ofNat 64 (keyStart d) := by
    simp only [s₃, gpr_write_of_ne _ _ (show Reg.r3 ≠ .r7 by decide),
      gpr_write_of_ne _ _ (show Reg.r3 ≠ .r6 by decide), gpr_write_of_ne _ _ (show Reg.r3 ≠ .r10 by decide),
      gpr_write_self, g₂, g₁ _ (show Reg.r3 ≠ .r8 by decide)]
  have r6₃ : s₃.gpr .r6 = P := by
    simp only [s₃, gpr_write_of_ne _ _ (show Reg.r6 ≠ .r7 by decide), gpr_write_self]; rfl
  have r7₃ : s₃.gpr .r7 = B := gpr_write_self _ _ _
  have r10₃ : s₃.gpr .r10 = BitVec.ofNat 64 1 := by
    simp only [s₃, gpr_write_of_ne _ _ (show Reg.r10 ≠ .r7 by decide),
      gpr_write_of_ne _ _ (show Reg.r10 ≠ .r6 by decide), gpr_write_self]
  have mem₃ : s₃.mem = s₂.mem := rfl
  have rd₃ : s₃.rd = s.rd := rd₂
  have wr₃ : s₃.wr = s.wr := wr₂
  have sp₃ : s₃.sp = s.sp := sp₂
  have slot₃ : ∀ j, slotW s₃ j = slotW s₂ j := fun j => by
    show s₃.mem.readW (StraightK.wordAddr (s₃.gpr .r8) j) 64 = s₂.mem.readW (StraightK.wordAddr (s₂.gpr .r8) j) 64
    rw [mem₃, r8₃, g₂, r8₁]
  have saved₃ : ∀ p ∈ callerRegs, slotW s₃ p.2 = s.gpr p.1 := by
    intro p hp
    rw [slot₃, set₂ (p.2, p.1) (List.mem_map_of_mem hp), g₁ _ (callerRegs_ok p hp).2.1]
  have f₃ : Frame [⟨B, 8 * scratchSlots⟩] s.mem s₃.mem := by rw [mem₃, ← scr₁]; exact f₂
  have room₃ : Room s₃ := room_congr room₁ (by rw [r8₃, r8₁]) (by rw [wr₃]; rfl)
  -- The block, outside the scratch buffer of the batch.
  have Psep : Region.Disjoint ⟨P, 16⟩ ⟨B, 8 * scratchSlots⟩ :=
    Offset.disjoint_base B (by omega_arith) (by omega_arith)
  have Parr : ∀ t : State, t.gpr .r8 = B → Region.Disjoint ⟨P, 16⟩ (arraysR t) := fun t ht => by
    rw [show arraysR t = ⟨B + BitVec.ofNat 64 (8 * 48), 8 * 64⟩ by simp only [arraysR, ht]]
    exact Offset.disjoint B (by omega_arith) (by omega_arith) (by omega_arith)
  have Pwr : (⟨P, 16⟩ : Region) ∈ s.wr ∨ True := .inr trivial
  have Pin : ∀ w < 4, InRegions s.wr (P + BitVec.ofNat 64 (16 * 0 + 4 * w)) 4 := fun w hw =>
    ⟨_, hW, by
      rw [Offset.add_add]
      exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  -- The copy in.
  have pre₃ : CopyPre s₃ P 1 := by
    refine ⟨room₃, by omega_arith, fun b hb w hw => ?_, ?_⟩
    · obtain rfl : b = 0 := by omega_arith
      obtain ⟨r, hr, hc⟩ := Pin w hw
      exact ⟨r, by rw [rd₃, wr₃]; exact List.mem_append_right _ hr, hc⟩
    · exact Parr s₃ r8₃
  have inv₃ : CopyInInv s₃ P 1 (1 - 1) s₃ := by
    refine ⟨by omega_arith, by rw [r6₃]; simp, by rw [r7₃, r8₃]; simp, by rw [r10₃], fun w _ b hb => by omega_arith,
      Frame.refl _ _, fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₃, e₃, ?_⟩)
  refine WP.seq (WP.mono (copyIn_loop pre₃ 1 s₃ inv₃ (by omega_arith) (by omega_arith)) fun s₄ i₄ => ?_)
  have G₄ : ∀ r, r ≠ .r3 → r ≠ .r6 → r ≠ .r7 → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → s₄.gpr r = s.gpr r :=
    fun r a b c e f g => (i₄.regs r f c g b).trans (G₃ r a b c e g)
  have r8₄ : s₄.gpr .r8 = B := (i₄.regs _ (by decide) (by decide) (by decide) (by decide)).trans r8₃
  have r3₄ : s₄.gpr .r3 = s.gpr .r3 + BitVec.ofNat 64 (keyStart d) :=
    (i₄.regs _ (by decide) (by decide) (by decide) (by decide)).trans r3₃
  have f₄ : Frame [⟨B, 8 * scratchSlots⟩] s.mem s₄.mem := by
    refine f₃.trans (i₄.frame.sub fun r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr
    refine ⟨_, List.mem_cons_self, ?_⟩
    rw [show arraysR s₃ = ⟨B + BitVec.ofNat 64 (8 * 48), 8 * 64⟩ by simp only [arraysR, r8₃]]
    exact Offset.sub_base _ (by omega_arith)
  have slot₄ : ∀ p ∈ callerRegs, slotW s₄ p.2 = s.gpr p.1 := by
    intro p hp
    have hp' := callerRegs_ok p hp
    rw [← saved₃ p hp]
    show s₄.mem.readW (StraightK.wordAddr (s₄.gpr .r8) p.2) 64 = s₃.mem.readW (StraightK.wordAddr (s₃.gpr .r8) p.2) 64
    rw [r8₄, r8₃]
    refine i₄.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    rw [show arraysR s₃ = ⟨B + BitVec.ofNat 64 (8 * 48), 8 * 64⟩ by simp only [arraysR, r8₃]]
    exact Offset.disjoint B (by omega)
      (by omega) (by omega)
  have hq₄ : quad s₄ 0 = decodeQ (Spec.Seed.blockAt s.mem P) := by
    rw [quad_of_lanes (m := s₃.mem) (p := P) fun w hw => i₄.lanes w hw 0 (by omega_arith)]
    rw [show P + BitVec.ofNat 64 (16 * 0) = P by simp, blockAt_frame f₃ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Psep]
  -- The modes' state to `r4`–`r6`.
  let s₅ := ((s₄.write .r4 (s₄.gpr .r29)).write .r5 ((s₄.write .r4 (s₄.gpr .r29)).gpr .r30)).write .r6
    (((s₄.write .r4 (s₄.gpr .r29)).write .r5 ((s₄.write .r4 (s₄.gpr .r29)).gpr .r30)).gpr .r31)
  refine WP.seq (WP.of_runBlock ⟨s₅, by
    rw [park, runBlock_cons, exec_movR, runStep_some, runBlock_cons, exec_movR, runStep_some,
      runBlock_cons, exec_movR, runStep_some, runBlock_nil], ?_⟩)
  have G₅ : ∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → s₅.gpr r = s₄.gpr r := fun r a b c => by
    simp only [s₅, gpr_write_of_ne _ _ c, gpr_write_of_ne _ _ b, gpr_write_of_ne _ _ a]
  have st₅ : s₅.gpr .r4 = s.gpr .r29 ∧ s₅.gpr .r5 = s.gpr .r30 ∧ s₅.gpr .r6 = s.gpr .r31 := by
    refine ⟨?_, ?_, ?_⟩ <;> simp [s₅, gpr_write] <;>
      exact G₄ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have r8₅ : s₅.gpr .r8 = B := (G₅ _ (by decide) (by decide) (by decide)).trans r8₄
  have room₅ : Room s₅ := room_congr room₃ (by rw [r8₅, r8₃]) (by simp only [s₅, wr_write]; exact i₄.wr)
  have scr₅ : scratchR s₅ = ⟨B, 8 * scratchSlots⟩ := by simp only [scratchR, r8₅]
  have r3₅ : s₅.gpr .r3 = s.gpr .r3 + BitVec.ofNat 64 (keyStart d) := (G₅ _ (by decide) (by decide) (by decide)).trans r3₄
  have hkB : ∀ j < 16, Region.Disjoint ⟨kp d (s.gpr .r3 + BitVec.ofNat 64 (keyStart d)) j, 8⟩ ⟨B, 8 * scratchSlots⟩ :=
    fun j hj => by
      rw [kp_start _ _ hj]
      exact (hk.sub_left (Offset.sub_base _ (keyOff_le d hj))).sub_right
        (Region.sub_prefix (by omega_arith))
  have keys₅ : KeysOk d s₅ (s₅.gpr .r3) := by
    intro j hj
    have hle := keyOff_le d hj
    have hin : keyR s ∈ s₅.rd ++ s₅.wr := by
      rw [show s₅.rd = s.rd by simp only [s₅, rd_write]; rw [i₄.rd, rd₃]]; exact List.mem_append_left _ hkin
    rw [r3₅, scr₅]
    refine ⟨?_, ?_, hkB j hj⟩
    · rw [kp_start _ _ hj]; exact ⟨_, hin, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    · rw [kp_start _ _ hj, show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, Offset.add_ofNat_add_ofNat]
      exact ⟨_, hin, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have hkeys : ∀ j < 16, keysAt d s₅.mem (s₅.gpr .r3) j = keysAt d s.mem (s.gpr .r3 + BitVec.ofNat 64 (keyStart d)) j := by
    intro j hj
    rw [r3₅]
    refine keysAt_frame (show Frame [⟨B, 8 * scratchSlots⟩] s.mem s₅.mem from f₄) fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr; exact hkB j hj
  -- The rounds.
  refine WP.seq (WP.mono (rounds_ok d room₅ keys₅) fun s₆ ⟨q₆, room₆, rd₆, wr₆, sp₆, g₆, f₆⟩ => ?_)
  have hq₆ : quad s₆ 0 = roundsN (keysAt d s.mem (s.gpr .r3 + BitVec.ofNat 64 (keyStart d))) 16
      (decodeQ (Spec.Seed.blockAt s.mem P)) := by
    rw [q₆ 0 (by omega_arith), roundsN_congr 16 _ hkeys,
      show quad s₅ 0 = quad s₄ 0 by simp only [quad, lv, laneA, r8₅, r8₄]; rfl, hq₄]
  have r8₆ : s₆.gpr .r8 = B := (g₆ _ (by simp)).trans r8₅
  -- The modes' state back, and the copy out.
  let s₇ := (((((s₆.write .r29 (s₆.gpr .r4)).write .r30 (s₆.gpr .r5)).write .r31 (s₆.gpr .r6)).write .r10
    (BitVec.ofNat 64 1)).write .r6 (B + BitVec.ofNat 64 (8 * bufSlot))).write .r7 B
  refine WP.seq (WP.of_runBlock ⟨s₇, by
    rw [unpark, runBlock_cons, exec_movR, runStep_some, runBlock_cons, exec_movR, runStep_some,
      runBlock_cons, exec_movR, runStep_some, runBlock_cons, exec_li (by decide), runStep_some,
      runBlock_cons, exec_addi' (by decide), runStep_some, runBlock_cons, exec_movR, runStep_some,
      runBlock_nil]
    simp [s₇, gpr_write, r8₆], ?_⟩)
  have G₇ : ∀ r, r ≠ .r6 → r ≠ .r7 → r ≠ .r10 → r ≠ .r29 → r ≠ .r30 → r ≠ .r31 → s₇.gpr r = s₆.gpr r := by
    intro r a b c e f g
    simp only [s₇, gpr_write_of_ne _ _ b, gpr_write_of_ne _ _ a, gpr_write_of_ne _ _ c,
      gpr_write_of_ne _ _ g, gpr_write_of_ne _ _ f, gpr_write_of_ne _ _ e]
  have st₇ : s₇.gpr .r29 = s.gpr .r29 ∧ s₇.gpr .r30 = s.gpr .r30 ∧ s₇.gpr .r31 = s.gpr .r31 := by
    refine ⟨?_, ?_, ?_⟩ <;> simp only [s₇, gpr_write, reduceCtorEq, ite_false, ite_true]
    · rw [g₆ .r4 (by simp)]; exact st₅.1
    · rw [g₆ .r5 (by simp)]; exact st₅.2.1
    · rw [g₆ .r6 (by simp)]; exact st₅.2.2
  have r8₇ : s₇.gpr .r8 = B := (G₇ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans r8₆
  have r6₇ : s₇.gpr .r6 = P := by
    simp only [s₇, gpr_write_of_ne _ _ (show Reg.r6 ≠ .r7 by decide), gpr_write_self]; rfl
  have r7₇ : s₇.gpr .r7 = B := gpr_write_self _ _ _
  have r10₇ : s₇.gpr .r10 = BitVec.ofNat 64 1 := by
    simp only [s₇, gpr_write_of_ne _ _ (show Reg.r10 ≠ .r7 by decide),
      gpr_write_of_ne _ _ (show Reg.r10 ≠ .r6 by decide), gpr_write_self]
  have wr₇ : s₇.wr = s.wr := by simp only [s₇, wr_write]; rw [wr₆, show s₅.wr = s.wr by
    simp only [s₅, wr_write]; rw [i₄.wr, wr₃]]
  have rd₇ : s₇.rd = s.rd := by simp only [s₇, rd_write]; rw [rd₆, show s₅.rd = s.rd by
    simp only [s₅, rd_write]; rw [i₄.rd, rd₃]]
  have quad₇ : quad s₇ 0 = quad s₆ 0 := by simp only [quad, lv, laneA, r8₇, r8₆]; rfl
  have pre₇ : CopyOutPre s₇ P 1 := by
    refine ⟨room_congr room₃ (by rw [r8₇, r8₃]) (by rw [wr₇, wr₃]), by omega_arith, fun b hb w hw => ?_, Parr s₇ r8₇⟩
    obtain rfl : b = 0 := by omega_arith
    rw [wr₇]; exact Pin w hw
  have inv₇ : CopyOutInv s₇ P 1 (1 - 1) s₇ := by
    refine ⟨by omega_arith, by rw [r6₇]; simp, by rw [r7₇, r8₇]; simp, by rw [r10₇], fun b hb => by omega_arith,
      Frame.refl _ _, fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.mono (copyOut_loop pre₇ 1 s₇ inv₇ (by omega_arith) (by omega_arith)) fun s₈ i₈ => ?_)
  have G₈ : ∀ r, r ≠ .r6 → r ≠ .r7 → r ≠ .r9 → r ≠ .r10 → s₈.gpr r = s₇.gpr r :=
    fun r a b c e => i₈.regs r c b e a
  have r8₈ : s₈.gpr .r8 = B := (G₈ _ (by decide) (by decide) (by decide) (by decide)).trans r8₇
  have room₈ : Room s₈ := room_congr room₃ (by rw [r8₈, r8₃]) (by rw [i₈.wr, wr₇, wr₃])
  -- The key pointer and `sb` back, the caller's registers restored.
  let s₉ := (s₈.write .r3 (s₈.gpr .r3 - BitVec.ofNat 64 (keyStart d))).write .r5 B
  have room₉ : Room s₉ := room_congr room₈ (by simp [s₉, gpr_write, r8₈]) rfl
  obtain ⟨s', run', m', sp', set', keep', rd', wr'⟩ := loads_ok room₉ callerRegs
    (fun q hq => ⟨(callerRegs_ok q hq).1, (callerRegs_ok q hq).2.1⟩) (by decide)
  refine WP.of_runBlock ⟨s', by
    rw [coreOut_eq]
    refine runBlock_trans ?_ run'
    rw [runBlock_cons, exec_subi' (keyStart_lt d), runStep_some, runBlock_cons, exec_movR, runStep_some,
      runBlock_nil]
    simp [s₉, gpr_write, r8₈], ?_⟩
  have r3₈ : s₈.gpr .r3 = s.gpr .r3 + BitVec.ofNat 64 (keyStart d) := by
    rw [G₈ _ (by decide) (by decide) (by decide) (by decide),
      G₇ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g₆ _ (by simp), r3₅]
  have g' : ∀ r, (∀ p ∈ callerRegs, p.1 ≠ r) → r ≠ .r3 → r ≠ .r5 → s'.gpr r = s₈.gpr r := fun r h a b => by
    rw [keep' r h]; simp only [s₉, gpr_write_of_ne _ _ b, gpr_write_of_ne _ _ a]
  have r8₉ : s₉.gpr .r8 = B := by
    simp only [s₉, gpr_write_of_ne _ _ (show Reg.r8 ≠ .r5 by decide),
      gpr_write_of_ne _ _ (show Reg.r8 ≠ .r3 by decide), r8₈]
  have f48 : Frame [workR s₅, ⟨P, 16⟩] s₄.mem s₈.mem := by
    have a : Frame [workR s₅, ⟨P, 16⟩] s₄.mem s₆.mem :=
      (show s₅.mem = s₄.mem by simp only [s₅, mem_write]) ▸ f₆.mono (by simp)
    have b : Frame [workR s₅, ⟨P, 16⟩] s₆.mem s₈.mem := by
      rw [show s₆.mem = s₇.mem by simp only [s₇, mem_write]]
      exact i₈.frame.mono (by simp)
    exact a.trans b
  -- Memory: within the core's slots.
  have fwork : Frame [⟨B, 8 * (bufSlot + 2)⟩] s.mem s'.mem := by
    rw [m']
    show Frame _ s.mem s₈.mem
    refine ((f₄.trans (f₆.sub fun r hr => ?_)).sub fun r hr => ?_).trans (i₈.frame.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_cons_self, ?_⟩
      simp only [workR, r8₅]; exact Region.sub_prefix (by omega_arith)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, Region.sub_prefix (by omega_arith)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, Offset.sub_base _ (by omega_arith)⟩
  refine ⟨?_, fun r hr => ?_, fwork, ?_, ?_, ?_⟩
  · rw [keep' _ (not_callerRegs .r5 (by simp))]; simp only [s₉, gpr_write_self]
  · by_cases h29 : r = .r29
    · subst h29; rw [g' _ (not_callerRegs _ (by simp)) (by decide) (by decide), G₈ _ (by decide) (by decide)
        (by decide) (by decide)]; exact st₇.1
    by_cases h30 : r = .r30
    · subst h30; rw [g' _ (not_callerRegs _ (by simp)) (by decide) (by decide), G₈ _ (by decide) (by decide)
        (by decide) (by decide)]; exact st₇.2.1
    by_cases h31 : r = .r31
    · subst h31; rw [g' _ (not_callerRegs _ (by simp)) (by decide) (by decide), G₈ _ (by decide) (by decide)
        (by decide) (by decide)]; exact st₇.2.2
    by_cases h3 : r = .r3
    · subst h3
      rw [keep' _ (not_callerRegs _ (by simp))]
      simp only [s₉, gpr_write_of_ne _ _ (show Reg.r3 ≠ .r5 by decide), gpr_write_self, r3₈,
        BitVec.add_sub_cancel]
    by_cases h2 : r = .r2
    · subst h2
      rw [g' _ (not_callerRegs _ (by simp)) (by decide) (by decide), G₈ _ (by decide) (by decide)
        (by decide) (by decide), G₇ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        g₆ .r2 (by simp)]
      exact G₄ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    obtain ⟨p, hp, rfl⟩ := callerRegs_kept r hr h29 h30 h31 h3 h2
    have hp' := callerRegs_ok p hp
    rw [set' p hp, ← slot₄ p hp]
    have m₉ : s₉.mem = s₈.mem := by simp only [s₉, mem_write]
    simp only [slotW, Impl.Aes.PPC64LE.sb, r8₉, r8₄, m₉]
    refine f48.readW (r := ⟨StraightK.wordAddr B p.2, 8⟩) (Region.contains_self _ _) (fun r hr => ?_)
      (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simp only [workR, r8₅]; exact Offset.disjoint_base _ (by omega) (by omega)
    · exact Offset.disjoint B (by omega) (by omega) (by omega)
  · -- The block.
    rw [show s'.mem = s₈.mem by rw [m']; simp only [s₉, mem_write], dirCipher_bytes, Proof.Seed.bytesAt_eq]
    refine congrArg Vector.toList ?_
    rw [← crypt_keysAt, crypt_eq, ← hq₆, ← quad₇]
    refine blockAt_of_bytes fun i hi => ?_
    have e := i₈.done 0 (by omega_arith) i hi
    rw [show P + BitVec.ofNat 64 (16 * 0 + i) = P + BitVec.ofNat 64 i by simp] at e
    rw [e, encodeSwapped_get _ _ hi]
  · rw [rd', show s₉.rd = s₈.rd by simp only [s₉, rd_write], i₈.rd, rd₇]
  · rw [wr', show s₉.wr = s₈.wr by simp only [s₉, wr_write], i₈.wr, wr₇]

/-- SEED's core meets what the modes need. -/
def dirCoreSpec (d : Direction) : CoreSpec (dirCore d) where
  Key := Spec.Seed.Schedule
  cipher := Proof.Seed.dirCipher d
  KeyArgs := KeyArgs
  Ready := Ready
  cipher_len _ _ := by cases d <;> simp [Proof.Seed.dirCipher, Spec.Seed.cipher, Spec.Seed.invCipher, dirCore]
  layout := layout d
  keyArgs_congr h e r _ _ f := keyArgs_congr h e.r3 r f
  ready_frame h e r _ _ f hs _ := ready_frame h e.r3 r f hs
  prepare_wp := prepare_wp d
  crypt_wp {s B ws k} hB hS hR := by
    refine WP.mono (crypt_ok d hB hS hR.2 hR.1.2.1) fun s' ⟨h5, hk, hf, hb, hrd, hwr⟩ => ?_
    refine ⟨h5, hk, ready_core hR (hk .r3 (by decide)) hrd hf, hf, fun j hj => ?_, hrd, hwr⟩
    obtain rfl : j = 0 := by simpa [dirCore] using hj
    have e : blkAddr (dirCore d) B 0 = bufA B := by simp [blkAddr, slotA, dirCore]
    rw [show 4 * (dirCore d).bw = 16 from rfl, e, hb, hR.1.1]

end VG.Proof.Seed.PPC64LE.Mode
