module

public import VerifiedGarbage.Proof.Seed.X86_64.Ecb
public import VerifiedGarbage.Proof.Modes.X86_64.Core
public import VerifiedGarbage.Impl.Seed.X86_64.Modes
public import VerifiedGarbage.Proof.Seed.ModeBytes
import VerifiedGarbage.Proof.Seed.X86_64.Setup
import VerifiedGarbage.Proof.Modes.X86_64.Steps
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Seed.X86_64.Lit
import VerifiedGarbage.Proof.Modes.X86_64.Fb
import VerifiedGarbage.Proof.Modes.X86_64.Words
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint

/-!
# SEED's core for the modes on x86-64

`dirCoreSpec d`: SEED's core for the direction `d`
(`Impl.Seed.X86_64.dirCore d`) meets what the modes need of a core of
16-byte blocks (`Proof.Modes.X86_64.BlockSpec`, with `bw = 2`), with the key
a schedule, its cipher `Spec.Seed.cipher` for encryption and
`Spec.Seed.invCipher` for decryption, and the key ready when its copy in the
core's slots is the schedule and the batch's masks are in their slots.
`crypt` is a batch (`batch_ok`) on the buffer's sixteen blocks.
-/

@[expose] public section

namespace VG.Proof.Seed.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Seed.X86_64
open VG.Impl.Aes.X86_64 (sb)
open VG.Proof.Modes (over over_at over_frame)
open VG.Proof.Modes.X86_64 (ScrIn coreRegion blkRegion blkAddr BlockSpec copyN_wp movR_ok addImm_ok movImm_ok
  signExtend_small runBlock_app addr_add)
open VG.Spec.Seed (Direction)

/-- The schedule's copy and the buffer, with the scratch buffer at `B`. -/
abbrev schedAddr (B : Addr) : Addr := B + BitVec.ofNat 64 (8 * schedSlot)
abbrev bufAt (B : Addr) : Addr := B + BitVec.ofNat 64 (8 * bufSlot)

/-- The schedule at `rdi`, outside the regions `rs`. -/
def ModeKeyArgs (s : State) (rs : List Region) (k : Spec.Seed.Schedule) : Prop :=
  ∃ p : Addr, s.gpr .rdi = p ∧ k = Spec.Seed.scheduleAt s.mem p ∧ (⟨p, 128⟩ : Region) ∈ s.rd ∧
    p.toNat + 128 ≤ 2 ^ 64 ∧ ∀ r ∈ rs, Region.Disjoint ⟨p, 128⟩ r

/-- The batch's masks, with the scratch buffer at `B`. -/
def MasksAt (m : Mem) (B : Addr) : Prop := ∀ kv ∈ maskSlots, m.readW (wordAddr B kv.1) 64 = kv.2

/-- The schedule's copy is `k`, and the masks are in their slots. -/
def ReadyAt (m : Mem) (B : Addr) (k : Spec.Seed.Schedule) : Prop :=
  Spec.Seed.scheduleAt m (schedAddr B) = k ∧ MasksAt m B

/-- The core's blocks are two words. -/
@[simp] theorem dirCore_bw (d : Direction) : (dirCore d).bw = 2 := rfl

theorem dirCipher_bytes (d : Direction) (k : Spec.Seed.Schedule) (m : Mem) (p : Addr) :
    dirCipher d k (Spec.Aes.bytesAt m p 16) = (cipher d k (Spec.Seed.blockAt m p)).toList := by
  have h : (Vector.ofFn fun i : Fin 16 => (Spec.Aes.bytesAt m p 16).getD i.val 0) = Spec.Seed.blockAt m p := by
    ext i hi; simp [Spec.Aes.bytesAt, Spec.Seed.blockAt]
  cases d <;> simp only [dirCipher, Spec.Seed.cipher, Spec.Seed.invCipher, cipher, h]

/-- The masks' slots, 48 to 60. -/
abbrev masksR (B : Addr) : Region := ⟨B, 8 * 61⟩

theorem masksAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {B : Addr} (h : MasksAt m B)
    (hd : ∀ r ∈ rs, (masksR B).Disjoint r) : MasksAt m' B := by
  intro kv hkv
  rw [← h kv hkv]
  exact hf.readW (Offset.contains_base B (by have := (maskSlots_lt kv hkv).1; omega) (by
    have := (maskSlots_lt kv hkv).1; omega)) hd (by decide)

/-- The core's slots, its buffer, the schedule's copy and the masks. -/
theorem core_eq (d : Direction) (B : Addr) : coreRegion (dirCore d) B = ⟨B, 1440⟩ := by
  simp only [coreRegion, dirCore, schedSlot, bufSlot, scratchSlots]
theorem blk_eq (d : Direction) (B : Addr) : blkRegion (dirCore d) B = ⟨B + BitVec.ofNat 64 1056, 256⟩ := by
  simp only [blkRegion, dirCore, bufSlot, scratchSlots]
theorem total_eq (d : Direction) : (dirCore d).total = 188 := by
  simp only [dirCore, schedSlot, bufSlot, scratchSlots]

theorem sched_sub (B : Addr) : Region.Sub ⟨schedAddr B, 128⟩ ⟨B, 1440⟩ := Offset.sub_base B (by decide)
theorem masks_sub (B : Addr) : Region.Sub (masksR B) ⟨B, 1440⟩ := Region.sub_prefix (by decide)
theorem sched_buf (B : Addr) : Region.Disjoint ⟨schedAddr B, 128⟩ ⟨B + BitVec.ofNat 64 1056, 256⟩ :=
  Offset.disjoint B (.inr (by decide)) (by decide) (by decide)
theorem masks_buf (B : Addr) : Region.Disjoint (masksR B) ⟨B + BitVec.ofNat 64 1056, 256⟩ :=
  (Offset.disjoint_base B (by decide) (by decide)).symm

theorem readyAt_frame {d : Direction} {m m' : Mem} {B : Addr} {k : Spec.Seed.Schedule} {rs : List Region}
    (h : ReadyAt m B k) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint (coreRegion (dirCore d) B) r ∨ Region.Sub r (blkRegion (dirCore d) B)) :
    ReadyAt m' B k := by
  refine ⟨?_, masksAt_frame hf h.2 fun r hr => ?_⟩
  · rw [scheduleAt_frame hf fun r hr => ?_]
    · exact h.1
    rcases hd r hr with h' | h'
    · rw [core_eq] at h'; exact h'.sub_left (sched_sub B)
    · rw [blk_eq] at h'; exact (sched_buf B).sub_right h'
  · rcases hd r hr with h' | h'
    · rw [core_eq] at h'; exact h'.sub_left (masks_sub B)
    · rw [blk_eq] at h'; exact (masks_buf B).sub_right h'

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Spec.Seed.Schedule} (h : ModeKeyArgs s rs k)
    (hr : ∀ r ∈ [Reg.rdi], s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (_ : s'.wr = s.wr)
    (hf : Frame rs s.mem s'.mem) : ModeKeyArgs s' rs k := by
  obtain ⟨p, hp, hk, hin, hfit, hdis⟩ := h
  refine ⟨p, by rw [hr .rdi List.mem_cons_self, hp], ?_, by rw [hrd]; exact hin, hfit, hdis⟩
  rw [hk]
  exact (scheduleAt_frame hf hdis).symm

/-- The batch's scratch buffer is the start of the core's. -/
theorem room_of {d : Direction} {s : State} {B : Addr} (hB : s.gpr sb = B) (hs : ScrIn s B (dirCore d).total) :
    Room s := ⟨8 * (dirCore d).total, by rw [total_eq]; decide, by rw [show s.gpr .r9 = B from hB]; exact hs.wr⟩

theorem prepare_wp (d : Direction) {s : State} {B : Addr} {rs : List Region} {k : Spec.Seed.Schedule}
    (hB : s.gpr sb = B) (hs : ScrIn s B (dirCore d).total) (hR : (⟨B, 8 * (dirCore d).total⟩ : Region) ∈ rs)
    (hk : ModeKeyArgs s rs k) :
    WP isa (dirCore d).prepare s fun s' => ReadyAt s'.mem B k ∧ s'.gpr sb = B ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.gpr .r12 = s.gpr .r12 ∧ s'.gpr .r13 = s.gpr .r13 ∧
      Frame [coreRegion (dirCore d) B] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨p, hp, rfl, hin, hfit, hdis⟩ := hk
  have hfB := hs.fit
  rw [total_eq] at hfB
  have hsep : Region.Disjoint ⟨p, 128⟩ ⟨B, 1504⟩ := (hdis _ hR).sub_right (Region.sub_prefix (by rw [total_eq]))
  show WP isa (.block (_ ++ _)) s _
  rw [WP.block_append_iff]
  refine WP.mono (copyN_wp (k := 16) (P := schedAddr B) (Q := p) ⟨by rw [hB], by rw [hp]; simp, by decide,
    by decide, fun w hw => ⟨_, hs.wr, by
      rw [addr_add, total_eq]; exact Offset.contains_base B (by simp only [schedSlot, bufSlot, scratchSlots]; omega)
        (by simp only [schedSlot, bufSlot, scratchSlots]; omega)⟩,
    fun w hw => ⟨_, List.mem_append_left _ hin, Offset.contains_base p (by omega) (by omega)⟩,
    (hsep.sub_right (Offset.sub_base B (by decide))).symm, by omega⟩) fun s₁ h₁ => ?_
  have r9₁ : s₁.gpr .r9 = B := by rw [h₁.regs .r9 (by decide)]; exact hB
  have room₁ : Room s₁ := ⟨8 * (dirCore d).total, by rw [total_eq]; decide, by rw [r9₁, h₁.wr]; exact hs.wr⟩
  obtain ⟨s₂, e₂, g₂, rd₂, wr₂, f₂, set₂, _⟩ := masks_ok room₁ maskSlots
    (fun p hp => by have := (maskSlots_lt p hp).1; unfold scratchSlots; omega) (by decide)
  refine WP.of_runBlock ⟨s₂, e₂, ?_⟩
  have scr : scratchR s₁ = ⟨B, 8 * scratchSlots⟩ := by simp only [scratchR, r9₁]
  rw [scr] at f₂
  have fcopy : Frame [⟨B, 1440⟩] s.mem s₁.mem := by
    rw [h₁.mem]
    exact (over_frame _ _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, sched_sub B⟩
  have fmask : Frame [⟨B, 1440⟩] s₁.mem s₂.mem := f₂.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
  have hreg : ∀ r, r ≠ .rax → r ≠ Impl.Aes.X86_64.t0 → s₂.gpr r = s.gpr r := fun r h1 h2 => by
    rw [g₂ r h2, h₁.regs r h1]
  refine ⟨⟨?_, fun kv hkv => ?_⟩, by rw [hreg _ (by decide) (by decide), hB], hreg _ (by decide) (by decide),
    hreg _ (by decide) (by decide), hreg _ (by decide) (by decide), by rw [core_eq]; exact fcopy.trans fmask,
    by rw [rd₂, h₁.rd], by rw [wr₂, h₁.wr]⟩
  · rw [scheduleAt_frame f₂ fun r hr => ?_, h₁.mem]
    · exact scheduleAt_congr_at fun i hi => over_at hi (by omega)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base B (by decide) (by decide)
  · have := set₂ kv hkv
    simp only [slotW, show s₂.gpr sb = B by rw [hreg _ (by decide) (by decide), hB]] at this
    exact this

theorem crypt_wp (d : Direction) {s : State} {B : Addr} {k : Spec.Seed.Schedule} (hB : s.gpr sb = B)
    (hs : ScrIn s B (dirCore d).total) (hr : ReadyAt s.mem B k) :
    WP isa (dirCore d).crypt s fun s' => s'.gpr sb = B ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.gpr .r12 = s.gpr .r12 ∧ s'.gpr .r13 = s.gpr .r13 ∧ ReadyAt s'.mem B k ∧
      Frame [coreRegion (dirCore d) B] s.mem s'.mem ∧
      (∀ j < (dirCore d).G, Spec.Aes.bytesAt s'.mem (blkAddr (dirCore d) B j) (8 * (dirCore d).bw) =
        dirCipher d k (Spec.Aes.bytesAt s.mem (blkAddr (dirCore d) B j) (8 * (dirCore d).bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hfB := hs.fit
  rw [total_eq] at hfB
  have hw := hs.wr
  rw [total_eq] at hw
  -- The data's address and the blocks left to `xmm13` and `xmm14`.
  obtain ⟨s₁, e₁, x₁, g₁, m₁, rd₁, wr₁⟩ := Modes.X86_64.movqX_ok s .xmm13 .r12
  obtain ⟨s₂, e₂, x₂, g₂, m₂, rd₂, wr₂⟩ := Modes.X86_64.movqX_ok s₁ .xmm14 .r13
  have x₂' : s₂.xmm .xmm13 = (0 : BitVec 64) ++ s.gpr .r12 := by
    have hs₂ : some (s₁.setXmm .xmm14 ((0 : BitVec 64) ++ s₁.gpr .r13)) = some s₂ := e₂
    rw [← Option.some.inj hs₂, RegUpd.xmm_setXmm_of_ne _ _ (by decide), x₁]
  rw [g₁] at x₂
  -- `rsi`, `rdx` and `rdi` to the buffer, its sixteen blocks and the first round key.
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := movR_ok s₂ .rsi sb
  obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄⟩ := addImm_ok s₃ .rsi (BitVec.ofNat 32 (8 * bufSlot))
  obtain ⟨s₅, e₅, r₅, o₅, m₅, rd₅, wr₅⟩ := movImm_ok s₄ .rdx 16
  obtain ⟨s₆, e₆, r₆, o₆, m₆, rd₆, wr₆⟩ := movR_ok s₅ .rdi sb
  obtain ⟨s₇, e₇, r₇, o₇, m₇, rd₇, wr₇⟩ := addImm_ok s₆ .rdi (BitVec.ofNat 32 (8 * schedSlot + keyStart d))
  have g₇ : ∀ x, x ≠ .rsi → x ≠ .rdx → x ≠ .rdi → s₇.gpr x = s.gpr x := fun x h1 h2 h3 => by
    rw [o₇ x h3, o₆ x h3, o₅ x h2, o₄ x h1, o₃ x h1, g₂, g₁]
  have r9₇ : s₇.gpr .r9 = B := by rw [g₇ _ (by decide) (by decide) (by decide)]; exact hB
  have rsi₇ : s₇.gpr .rsi = bufAt B := by
    rw [o₇ _ (by decide), o₆ _ (by decide), o₅ _ (by decide), r₄, r₃, g₂, g₁, hB, signExtend_small (by decide)]
  have rdx₇ : s₇.gpr .rdx = 16 := by rw [o₇ _ (by decide), o₆ _ (by decide), r₅]
  have rdi₇ : s₇.gpr .rdi = schedAddr B + BitVec.ofNat 64 (keyStart d) := by
    rw [r₇, r₆, o₅ _ (by decide), o₄ _ (by decide), o₃ _ (by decide), g₂, g₁, hB, signExtend_small (by
      cases d <;> decide), BitVec.add_assoc, BitVec.ofNat_add]
  have mem₇ : s₇.mem = s.mem := by rw [m₇, m₆, m₅, m₄, m₃, m₂, m₁]
  have rd₇' : s₇.rd = s.rd := by rw [rd₇, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁]
  have wr₇' : s₇.wr = s.wr := by rw [wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]
  have xmm₇ : s₇.xmm = s₂.xmm := by
    rw [Modes.X86_64.runBlock_vec (by cases d <;> decide) e₇, Modes.X86_64.runBlock_vec (by decide) e₆,
      Modes.X86_64.runBlock_vec (by decide) e₅, Modes.X86_64.runBlock_vec (by decide) e₄,
      Modes.X86_64.runBlock_vec (by decide) e₃]
  have room₇ : Room s₇ := ⟨8 * 188, by decide, by rw [r9₇, wr₇']; exact hw⟩
  have masks₇ : MasksIn s₇ := fun kv hkv => by
    simp only [slotW, show s₇.gpr sb = B from r9₇, mem₇]; exact hr.2 kv hkv
  have hrdx : (s₇.gpr .rdx).toNat = 16 := by rw [rdx₇]; rfl
  have scr₇ : scratchR s₇ = ⟨B, 8 * scratchSlots⟩ := by simp only [scratchR, r9₇]
  have inScr : ∀ t n, t + n ≤ 1504 → InRegions s₇.wr (B + BitVec.ofNat 64 t) n := fun t n h =>
    ⟨_, by rw [wr₇']; exact hw, Offset.contains_base B (by omega) (by omega)⟩
  have hbuf : 8 * bufSlot = 1056 := rfl
  have hsch : 8 * schedSlot = 1312 := rfl
  have hpre : BatchPre d s₇ := by
    refine ⟨room₇, masks₇, by rw [hrdx]; decide, fun b hb w hw' => ?_, ?_, fun j hj => ?_, fun j hj => ?_⟩
    · rw [hrdx] at hb
      rw [rsi₇, bufAt, Offset.add_add, hbuf]
      exact inScr _ _ (by omega)
    · rw [rsi₇, hrdx, scr₇, bufAt, hbuf]; exact Offset.disjoint_base B (by decide) (by decide)
    · rw [rdi₇, kp_start _ _ hj, schedAddr, Offset.add_add, scr₇, hsch]
      have := keyOff_le d hj
      refine ⟨Modes.X86_64.inRd (inScr (1312 + keyOff d j) 4 (by omega)), ?_,
        Offset.disjoint_base B (by unfold scratchSlots; omega) (by omega)⟩
      rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, Offset.add_add]
      exact Modes.X86_64.inRd (inScr (1312 + keyOff d j + 4) 4 (by omega))
    · rw [rdi₇, kp_start _ _ hj, schedAddr, Offset.add_add, rsi₇, hrdx, bufAt, hbuf, hsch]
      have := keyOff_le d hj
      exact Offset.disjoint B (.inr (by omega)) (by omega) (by omega)
  refine WP.seq (WP.of_runBlock ⟨s₇, ?_, ?_⟩)
  · show runBlock isa ([.xop (.movq .xmm13 .r12)] ++ ([.xop (.movq .xmm14 .r13)] ++
      ([Impl.Aes.X86_64.movR .rsi sb] ++ ([.alu .add .rsi (.imm (BitVec.ofNat 32 (8 * bufSlot)))] ++
      ([.movImm64 .rdx 16] ++ ([Impl.Aes.X86_64.movR .rdi sb] ++
      ([.alu .add .rdi (.imm (BitVec.ofNat 32 (8 * schedSlot + keyStart d)))] : List Instr))))))) s = some s₇
    rw [runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃, Option.bind_some,
      runBlock_app, e₄, Option.bind_some, runBlock_app, e₅, Option.bind_some, runBlock_app, e₆, Option.bind_some, e₇]
  refine WP.seq (WP.mono (WP.vecKeep (by cases d <;> lit_decide) (batch_ok d hpre)) fun s₈ ⟨q, qx, _⟩ => ?_)
  obtain ⟨qdone, _, _, _, qregs, qmasks, qrd, qwr, qframe⟩ := q
  rw [hrdx, rsi₇] at qdone qframe
  have r9₈ : s₈.gpr .r9 = B := by rw [qregs .r9 (by simp), r9₇]
  have sb₈ : s₈.gpr sb = B := r9₈
  obtain ⟨t₁, f₁, v₁, o₁, mt₁, rdt₁, wrt₁, xt₁⟩ := Modes.X86_64.movqR_ok s₈ .r12 .xmm13
  obtain ⟨s₉, f₉, v₉, o₉, mt₉, rdt₉, wrt₉, _⟩ := Modes.X86_64.movqR_ok t₁ .r13 .xmm14
  refine WP.of_runBlock ⟨s₉, ?_, ?_⟩
  · show runBlock isa ([.movqR .r12 .xmm13] ++ [.movqR .r13 .xmm14]) s₈ = some s₉
    rw [runBlock_app, f₁, Option.bind_some, f₉]
  have m₉ : s₉.mem = s₈.mem := by rw [mt₉, mt₁]
  have hsv : ∀ x, x ≠ .r12 → x ≠ .r13 → s₉.gpr x = s₈.gpr x := fun x h1 h2 => by rw [o₉ x h2, o₁ x h1]
  have workR₇ : workR s₇ = ⟨B, 8 * 125⟩ := by simp only [workR, r9₇]
  rw [workR₇] at qframe
  have fsched₈ : ∀ r ∈ [(⟨B, 8 * 125⟩ : Region), ⟨bufAt B, 16 * 16⟩], Region.Disjoint ⟨schedAddr B, 128⟩ r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint_base B (by decide) (by decide)
    · exact sched_buf B
  have fcore : Frame [⟨B, 1440⟩] s.mem s₉.mem := by
    rw [m₉, ← mem₇]
    refine qframe.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
    · exact ⟨_, List.mem_singleton_self _, Offset.sub_base B (by decide)⟩
  refine ⟨by rw [hsv _ (by decide) (by decide)]; exact sb₈, by
      rw [hsv _ (by decide) (by decide), qregs .rsp (by simp), g₇ _ (by decide) (by decide) (by decide)],
    by rw [o₉ _ (by decide), v₁, qx, xmm₇, x₂', Modes.X86_64.extract_zero_append],
    by rw [v₉, xt₁, qx, xmm₇, x₂, Modes.X86_64.extract_zero_append],
    ⟨?_, ?_⟩, by rw [core_eq]; exact fcore, fun j hj => ?_,
    by rw [rdt₉, rdt₁, qrd, rd₇'], by rw [wrt₉, wrt₁, qwr, wr₇']⟩
  · rw [m₉, scheduleAt_frame qframe fsched₈, mem₇]; exact hr.1
  · intro kv hkv
    have := qmasks kv hkv
    simp only [slotW, show s₈.gpr sb = B from r9₈] at this
    rw [m₉]; exact this
  · have hj16 : j < 16 := by simp only [dirCore] at hj; exact hj
    have ea : blkAddr (dirCore d) B j = bufAt B + BitVec.ofNat 64 (16 * j) := by
      rw [blkAddr, bufAt, Offset.add_add]; simp only [dirCore, bufSlot, scratchSlots]
    rw [dirCore_bw, show 8 * 2 = 16 from rfl, ea, dirCipher_bytes, bytesAt_eq, m₉,
      qdone j (by omega), rdi₇, crypt_keysAt, mem₇, hr.1]

/-- SEED's core for the direction `d` meets what the modes need. -/
def dirCoreSpec (d : Direction) : BlockSpec (dirCore d) where
  Key := Spec.Seed.Schedule
  cipher := dirCipher d
  KeyArgs := ModeKeyArgs
  Ready s B k := ReadyAt s.mem B k
  cipher_len _ _ := by cases d <;> simp [dirCipher, Spec.Seed.cipher, Spec.Seed.invCipher]
  layout := ⟨by simp only [dirCore]; decide, by simp only [dirCore]; decide, by simp only [dirCore]; decide,
    by simp only [dirCore, schedSlot, bufSlot, scratchSlots]; decide, by simp only [dirCore]; decide,
    by simp only [dirCore, schedSlot, bufSlot, scratchSlots]; decide⟩
  keyRegs_ok := by simp only [dirCore]; decide
  regs_ok := by simp only [dirCore, Modes.X86_64.regsOk]; decide
  keyArgs_congr h hr hrd hwr _ hf := keyArgs_congr h hr hrd hwr hf
  ready_frame h hf hd _ _ := readyAt_frame h hf hd
  prepare_wp := prepare_wp d
  crypt_wp := crypt_wp d

end VG.Proof.Seed.X86_64
