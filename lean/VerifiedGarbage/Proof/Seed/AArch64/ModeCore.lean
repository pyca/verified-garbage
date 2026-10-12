module

public import VerifiedGarbage.Proof.Seed.AArch64.Ecb
public import VerifiedGarbage.Proof.Seed.AArch64.Batch
public import VerifiedGarbage.Proof.Seed.AArch64.Lit
public import VerifiedGarbage.Proof.Seed.ModeBytes
public import VerifiedGarbage.Proof.Modes.AArch64.Core
public import VerifiedGarbage.Proof.Modes.AArch64.Words
public import VerifiedGarbage.Proof.Modes.AArch64.ViaV
public import VerifiedGarbage.Impl.Seed.AArch64.Modes
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# SEED's core for the modes on AArch64

`dirCoreSpec d`: SEED's core for the direction `d`
(`Impl.Seed.AArch64.dirCore d`) meets what the modes need of a core of
16-byte blocks (`Proof.Modes.AArch64.BlockSpec`, with `bw = 2`), with the
key a schedule, its cipher `Spec.Seed.cipher` for encryption and
`Spec.Seed.invCipher` for decryption, and the key ready when its copy in the
core's slots is the schedule. As on x86-64 (`Proof/Seed/X86_64/ModeCore.lean`):
`crypt` is a batch (`batch_ok`) on the buffer's sixteen blocks, around
which `v29` and `v30` keep the data's address and the blocks left, since the
batch writes no vector register (`vSafe`).
-/

@[expose] public section

namespace VG.Proof.Seed.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Seed.AArch64
open VG.Impl.Aes.AArch64 (sb)
open VG.Proof.Modes (over over_at over_frame)
open VG.Proof.Modes.AArch64 (ScrIn coreRegion blkRegion blkAddr BlockSpec copyN_wp addImm_ok movz_ok
  runBlock_app addr_add vSafe keepsV_of_vSafe dup_ok umov_ok extract_ofVDwords)
open VG.Spec.Seed (Direction)

/-- The schedule's copy and the buffer, with the scratch buffer at `B`. -/
abbrev schedAddr (B : Addr) : Addr := B + BitVec.ofNat 64 (8 * schedSlot)
abbrev bufAt (B : Addr) : Addr := B + BitVec.ofNat 64 (8 * bufSlot)

/-- The schedule at `x0`, outside the regions `rs`. -/
def ModeKeyArgs (s : State) (rs : List Region) (k : Spec.Seed.Schedule) : Prop :=
  ∃ p : Addr, s.gpr .x0 = p ∧ k = Spec.Seed.scheduleAt s.mem p ∧ (⟨p, 128⟩ : Region) ∈ s.rd ∧
    p.toNat + 128 ≤ 2 ^ 64 ∧ ∀ r ∈ rs, Region.Disjoint ⟨p, 128⟩ r

/-- The schedule's copy is `k`. -/
def ReadyAt (m : Mem) (B : Addr) (k : Spec.Seed.Schedule) : Prop :=
  Spec.Seed.scheduleAt m (schedAddr B) = k

/-- The core's blocks are two words. -/
@[simp] theorem dirCore_bw (d : Direction) : (dirCore d).bw = 2 := rfl

theorem dirCipher_bytes (d : Direction) (k : Spec.Seed.Schedule) (m : Mem) (p : Addr) :
    dirCipher d k (Spec.Aes.bytesAt m p 16) = (cipher d k (Spec.Seed.blockAt m p)).toList := by
  have h : (Vector.ofFn fun i : Fin 16 => (Spec.Aes.bytesAt m p 16).getD i.val 0) = Spec.Seed.blockAt m p := by
    ext i hi; simp [Spec.Aes.bytesAt, Spec.Seed.blockAt]
  cases d <;> simp only [dirCipher, Spec.Seed.cipher, Spec.Seed.invCipher, cipher, h]

/-- The core's slots, its buffer and the schedule's copy. -/
theorem core_eq (d : Direction) (B : Addr) : coreRegion (dirCore d) B = ⟨B, 1360⟩ := by
  simp only [coreRegion, dirCore, schedSlot, bufSlot, scratchSlots]
theorem blk_eq (d : Direction) (B : Addr) : blkRegion (dirCore d) B = ⟨B + BitVec.ofNat 64 976, 256⟩ := by
  simp only [blkRegion, dirCore, bufSlot, scratchSlots, Impl.Modes.AArch64.Core.G]
theorem total_eq (d : Direction) : (dirCore d).total = 182 := by
  simp only [dirCore, schedSlot, bufSlot, scratchSlots]

theorem sched_sub (B : Addr) : Region.Sub ⟨schedAddr B, 128⟩ ⟨B, 1360⟩ := Offset.sub_base B (by decide)
theorem sched_buf (B : Addr) : Region.Disjoint ⟨schedAddr B, 128⟩ ⟨B + BitVec.ofNat 64 976, 256⟩ :=
  Offset.disjoint B (.inr (by decide)) (by decide) (by decide)

theorem readyAt_frame {d : Direction} {m m' : Mem} {B : Addr} {k : Spec.Seed.Schedule} {rs : List Region}
    (h : ReadyAt m B k) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint (coreRegion (dirCore d) B) r ∨ Region.Sub r (blkRegion (dirCore d) B)) :
    ReadyAt m' B k := by
  rw [ReadyAt, scheduleAt_frame hf fun r hr => ?_]
  · exact h
  rcases hd r hr with h' | h'
  · rw [core_eq] at h'; exact h'.sub_left (sched_sub B)
  · rw [blk_eq] at h'; exact (sched_buf B).sub_right h'

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Spec.Seed.Schedule} (h : ModeKeyArgs s rs k)
    (hr : ∀ r ∈ [Reg.x0], s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (_ : s'.wr = s.wr)
    (hf : Frame rs s.mem s'.mem) : ModeKeyArgs s' rs k := by
  obtain ⟨p, hp, hk, hin, hfit, hdis⟩ := h
  refine ⟨p, by rw [hr .x0 List.mem_cons_self, hp], ?_, by rw [hrd]; exact hin, hfit, hdis⟩
  rw [hk]
  exact (scheduleAt_frame hf hdis).symm

theorem prepare_wp (d : Direction) {s : State} {B : Addr} {rs : List Region} {k : Spec.Seed.Schedule}
    (hB : s.gpr sb = B) (hs : ScrIn s B (dirCore d).total) (hR : (⟨B, 8 * (dirCore d).total⟩ : Region) ∈ rs)
    (hk : ModeKeyArgs s rs k) :
    WP isa (dirCore d).prepare s fun s' => ReadyAt s'.mem B k ∧ s'.gpr sb = B ∧
      s'.gpr .x23 = s.gpr .x23 ∧ s'.gpr .x24 = s.gpr .x24 ∧
      Frame [coreRegion (dirCore d) B] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨p, hp, rfl, hin, hfit, hdis⟩ := hk
  have hfB := hs.fit
  rw [total_eq] at hfB
  have hsep : Region.Disjoint ⟨p, 128⟩ ⟨B, 1456⟩ := (hdis _ hR).sub_right (Region.sub_prefix (by rw [total_eq]))
  refine WP.mono (copyN_wp (k := 16) (t := .x6) (u := .x6) (P := schedAddr B) (Q := p)
    ⟨by rw [hB], by rw [hp]; simp, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, fun w hw => ⟨_, hs.wr, by
        rw [addr_add, total_eq]; exact Offset.contains_base B (by simp only [schedSlot, bufSlot, scratchSlots]; omega)
          (by simp only [schedSlot, bufSlot, scratchSlots]; omega)⟩,
      fun w hw => ⟨_, List.mem_append_left _ hin, Offset.contains_base p (by omega) (by omega)⟩,
      (hsep.sub_right (Offset.sub_base B (by decide))).symm, by omega⟩) fun s' h => ?_
  refine ⟨scheduleAt_congr_at fun i hi => by rw [h.mem, over_at hi (by omega)],
    by rw [h.regs _ (by decide) (by decide), hB], h.regs _ (by decide) (by decide), h.regs _ (by decide) (by decide),
    ?_, h.rd, h.wr⟩
  rw [h.mem, core_eq]
  exact (over_frame _ _ _ _).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, sched_sub B⟩

/-- One instruction that writes no vector register keeps them. -/
private theorem single_v {i : Instr} {s s' : State} (h : vdstOf i = none) (hr : runBlock isa [i] s = some s') :
    s'.v = s.v := by
  cases he : exec i s with
  | none => rw [runBlock_cons, he] at hr; cases hr
  | some u =>
    rw [runBlock_cons, he, runStep_some, runBlock_nil] at hr
    cases hr
    funext r
    exact exec_vec (by rw [h]; simp) he

private theorem inRd {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n :=
  let ⟨r, hr, hc⟩ := h; ⟨r, List.mem_append_right _ hr, hc⟩

/-- The batch keeps the vector registers `v29` and `v30`. -/
theorem batch_vsafe (d : Direction) : vSafe .v29 (batch d) = true ∧ vSafe .v30 (batch d) = true := by
  cases d <;> exact ⟨by lit_decide, by lit_decide⟩

theorem crypt_wp (d : Direction) {s : State} {B : Addr} {k : Spec.Seed.Schedule} (hB : s.gpr sb = B)
    (hs : ScrIn s B (dirCore d).total) (hr : ReadyAt s.mem B k) :
    WP isa (dirCore d).crypt s fun s' => s'.gpr sb = B ∧
      s'.gpr .x23 = s.gpr .x23 ∧ s'.gpr .x24 = s.gpr .x24 ∧ ReadyAt s'.mem B k ∧
      Frame [coreRegion (dirCore d) B] s.mem s'.mem ∧
      (∀ j < (dirCore d).G, Spec.Aes.bytesAt s'.mem (blkAddr (dirCore d) B j) (8 * (dirCore d).bw) =
        dirCipher d k (Spec.Aes.bytesAt s.mem (blkAddr (dirCore d) B j) (8 * (dirCore d).bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hfB := hs.fit
  rw [total_eq] at hfB
  have hw := hs.wr
  rw [total_eq] at hw
  -- The data's address and the blocks left to `v29` and `v30`.
  have e₁ := dup_ok s .v29 .x23
  let s₂ := (s.setV .v29 (ofVDwords (s.gpr .x23) (s.gpr .x23))).setV .v30
    (ofVDwords (s.gpr .x24) (s.gpr .x24))
  have e₂ : runBlock isa [.vop (.dup .d2 .v30 .x24)] (s.setV .v29 (ofVDwords (s.gpr .x23) (s.gpr .x23))) =
      some s₂ := dup_ok _ _ _
  have v29₂ : s₂.v .v29 = ofVDwords (s.gpr .x23) (s.gpr .x23) := by
    simp only [s₂, RegUpd.v_setV_of_ne _ _ (show VReg.v29 ≠ .v30 by decide), RegUpd.v_setV_self]
  have v30₂ : s₂.v .v30 = ofVDwords (s.gpr .x24) (s.gpr .x24) := RegUpd.v_setV_self _ _ _
  -- `x1`, `x2` and `x0` to the buffer, its sixteen blocks and the first round key.
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := addImm_ok s₂ .x1 sb (v := 8 * bufSlot) (by decide)
  obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄⟩ := movz_ok s₃ .x2 (v := 16) (by decide)
  obtain ⟨s₅, e₅, r₅, o₅, m₅, rd₅, wr₅⟩ := addImm_ok s₄ .x0 sb (v := 8 * schedSlot + keyStart d)
    (by cases d <;> decide)
  have g₅ : ∀ x, x ≠ .x1 → x ≠ .x2 → x ≠ .x0 → s₅.gpr x = s.gpr x := fun x h1 h2 h3 => by
    rw [o₅ x h3, o₄ x h2, o₃ x h1]; rfl
  have x5₅ : s₅.gpr .x5 = B := by rw [g₅ _ (by decide) (by decide) (by decide)]; exact hB
  have x1₅ : s₅.gpr .x1 = bufAt B := by
    rw [o₅ _ (by decide), o₄ _ (by decide), r₃]; show s.gpr sb + _ = _; rw [hB]
  have x2₅ : s₅.gpr .x2 = 16 := by rw [o₅ _ (by decide), r₄]; rfl
  have x0₅ : s₅.gpr .x0 = schedAddr B + BitVec.ofNat 64 (keyStart d) := by
    rw [r₅, o₄ _ (by decide), o₃ _ (by decide)]
    show s.gpr sb + _ = _
    rw [hB, BitVec.add_assoc, BitVec.ofNat_add]
  have mem₅ : s₅.mem = s.mem := by rw [m₅, m₄, m₃]; rfl
  have rd₅' : s₅.rd = s.rd := by rw [rd₅, rd₄, rd₃]; rfl
  have wr₅' : s₅.wr = s.wr := by rw [wr₅, wr₄, wr₃]; rfl
  have v₅ : ∀ v, s₅.v v = s₂.v v := fun v => by
    rw [single_v rfl e₅, single_v rfl e₄, single_v rfl e₃]
  have room₅ : Room s₅ := ⟨8 * 182, by decide, by rw [x5₅, wr₅']; exact hw⟩
  have hx2 : (s₅.gpr .x2).toNat = 16 := by rw [x2₅]; rfl
  have scr₅ : scratchR s₅ = ⟨B, 8 * scratchSlots⟩ := by simp only [scratchR, x5₅]
  have inScr : ∀ t n, t + n ≤ 1456 → InRegions s₅.wr (B + BitVec.ofNat 64 t) n := fun t n h =>
    ⟨_, by rw [wr₅']; exact hw, Offset.contains_base B (by omega) (by omega)⟩
  have hbuf : 8 * bufSlot = 976 := rfl
  have hsch : 8 * schedSlot = 1232 := rfl
  have hpre : BatchPre d s₅ := by
    refine ⟨room₅, by rw [hx2]; decide, fun b hb w hw' => ?_, ?_, fun j hj => ?_, fun j hj => ?_⟩
    · rw [hx2] at hb
      rw [x1₅, bufAt, Offset.add_add, hbuf]
      exact inScr _ _ (by omega)
    · rw [x1₅, hx2, scr₅, bufAt, hbuf]; exact Offset.disjoint_base B (by decide) (by decide)
    · rw [x0₅, kp_start _ _ hj, schedAddr, Offset.add_add, scr₅, hsch]
      have := keyOff_le d hj
      refine ⟨inRd (inScr (1232 + keyOff d j) 4 (by omega)), ?_,
        Offset.disjoint_base B (by unfold scratchSlots; omega) (by omega)⟩
      rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, Offset.add_add]
      exact inRd (inScr (1232 + keyOff d j + 4) 4 (by omega))
    · rw [x0₅, kp_start _ _ hj, schedAddr, Offset.add_add, x1₅, hx2, bufAt, hbuf, hsch]
      have := keyOff_le d hj
      exact Offset.disjoint B (.inr (by omega)) (by omega) (by omega)
  refine WP.seq (WP.of_runBlock ⟨s₅, ?_, ?_⟩)
  · show runBlock isa ([.vop (.dup .d2 .v29 .x23)] ++ ([.vop (.dup .d2 .v30 .x24)] ++
      ([.addImm .x .x1 sb (8 * bufSlot)] ++ ([.movz .x .x2 (BitVec.ofNat 16 16) 0] ++
      ([.addImm .x .x0 sb (8 * schedSlot + keyStart d)] : List Instr))))) s = some s₅
    rw [runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃, Option.bind_some,
      runBlock_app, e₄, Option.bind_some, e₅]
  obtain ⟨hv29, hv30⟩ := batch_vsafe d
  refine WP.seq (WP.mono (show WP isa (batch d) s₅ fun s₈ => BatchPost d s₅ s₈ ∧ s₈.v .v29 = s₅.v .v29 ∧
      s₈.v .v30 = s₅.v .v30 from
    let ⟨t, s₈, e, q⟩ := batch_ok d hpre
    ⟨t, s₈, e, q, keepsV_of_vSafe hv29 _ _ _ e, keepsV_of_vSafe hv30 _ _ _ e⟩) fun s₈ ⟨q, q29, q30⟩ => ?_)
  obtain ⟨qdone, _, _, qregs, _, qrd, qwr, qframe⟩ := q
  rw [hx2, x1₅] at qdone qframe
  have x5₈ : s₈.gpr .x5 = B := by rw [qregs .x5 (by simp), x5₅]
  have e₆ := umov_ok s₈ .x23 .v29
  have e₇ := umov_ok (s₈.write .x .x23 ((s₈.v .v29).extractLsb' 0 64)) .x24 .v30
  refine WP.of_runBlock ⟨_, by
    show runBlock isa ([.umov .x .x23 .v29 0] ++ [.umov .x .x24 .v30 0]) s₈ = some _
    rw [runBlock_app, e₆, Option.bind_some, e₇], ?_⟩
  have workR₅ : workR s₅ = ⟨B, 8 * 112⟩ := by simp only [workR, x5₅]
  rw [workR₅] at qframe
  have fsched₈ : ∀ r ∈ [(⟨B, 8 * 112⟩ : Region), ⟨bufAt B, 16 * 16⟩], Region.Disjoint ⟨schedAddr B, 128⟩ r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint_base B (by decide) (by decide)
    · exact sched_buf B
  have fcore : Frame [⟨B, 1360⟩] s.mem s₈.mem := by
    rw [← mem₅]
    refine qframe.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
    · exact ⟨_, List.mem_singleton_self _, Offset.sub_base B (by decide)⟩
  refine ⟨by rw [(Modes.AArch64.write_ok _ .x24 _).2.1 sb (by decide), (Modes.AArch64.write_ok _ .x23 _).2.1 sb (by decide)]; exact x5₈,
    by rw [(Modes.AArch64.write_ok _ .x24 _).2.1 .x23 (by decide), (Modes.AArch64.write_ok _ .x23 _).1, q29, v₅, v29₂, extract_ofVDwords],
    by rw [(Modes.AArch64.write_ok _ .x24 _).1, RegUpd.v_write, q30, v₅, v30₂, extract_ofVDwords],
    ?_, by rw [core_eq, RegUpd.mem_write, RegUpd.mem_write]; exact fcore, fun j hj => ?_, by rw [RegUpd.rd_write, RegUpd.rd_write, qrd, rd₅'], by rw [RegUpd.wr_write, RegUpd.wr_write, qwr, wr₅']⟩
  · rw [RegUpd.mem_write, RegUpd.mem_write, ReadyAt, scheduleAt_frame qframe fsched₈, mem₅]; exact hr
  · have hj16 : j < 16 := by simp only [dirCore, Impl.Modes.AArch64.Core.G] at hj; exact hj
    have ea : blkAddr (dirCore d) B j = bufAt B + BitVec.ofNat 64 (16 * j) := by
      rw [blkAddr, bufAt, Offset.add_add]; simp only [dirCore, bufSlot, scratchSlots]
    rw [dirCore_bw, show 8 * 2 = 16 from rfl, ea, dirCipher_bytes, bytesAt_eq, RegUpd.mem_write, RegUpd.mem_write,
      qdone j (by omega), x0₅, crypt_keysAt, mem₅, hr]

/-- SEED's core for the direction `d` meets what the modes need. -/
def dirCoreSpec (d : Direction) : BlockSpec (dirCore d) where
  Key := Spec.Seed.Schedule
  cipher := dirCipher d
  KeyArgs := ModeKeyArgs
  Ready s B k := ReadyAt s.mem B k
  cipher_len _ _ := by cases d <;> simp [dirCipher, Spec.Seed.cipher, Spec.Seed.invCipher]
  layout := ⟨by simp only [dirCore]; decide, by simp only [dirCore]; decide, by simp only [dirCore]; decide,
    by simp only [dirCore, schedSlot, bufSlot, scratchSlots, Impl.Modes.AArch64.Core.G]; decide,
    by simp only [dirCore, schedSlot, bufSlot, scratchSlots]; decide,
    by simp only [dirCore, schedSlot, bufSlot, scratchSlots]; decide,
    by simp only [dirCore, bufSlot, scratchSlots]; decide⟩
  keyRegs_ok := by simp only [dirCore]; decide
  regs_ok := by simp only [dirCore, Modes.AArch64.regsOk]; decide
  keyArgs_congr h hr hrd hwr _ hf := keyArgs_congr h hr hrd hwr hf
  ready_frame h hf hd _ _ := readyAt_frame h hf hd
  prepare_wp := prepare_wp d
  crypt_wp := crypt_wp d

end VG.Proof.Seed.AArch64
