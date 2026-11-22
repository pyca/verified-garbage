module

-- separate module: the core on 64 blocks, as `ModeCore.lean` is the core on one; it alone imports the bitsliced ECB
public import VerifiedGarbage.Proof.TripleDes.RISCV64.ModeCore
public import VerifiedGarbage.Proof.TripleDes.RISCV64.Bitsliced.Ecb
public import VerifiedGarbage.Proof.Modes.RISCV64.Wide
public import VerifiedGarbage.Proof.Modes.RISCV64.Shared
public import VerifiedGarbage.Impl.TripleDes.RISCV64.Modes
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.TripleDes.CbcBlocks

/-!
# Triple DES's core on 64 blocks for the modes on RISC-V
-/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64.Mode

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.TripleDes.RISCV64
open VG.Impl.TripleDes.RISCV64.Bitslice (transpose transposeCall passes)
open VG.Proof.Modes.RISCV64 (coreRegion blkRegion blkAddr slotA CoreSpec Layout ScrIn kept KeptBut OneOk)
open VG.Spec.TripleDes (Direction Schedule scheduleAt blockAt)
open VG.Proof.TripleDes (dirCipher bytesAt_eq scheduleAt_eq_of_frame)
open VG.Proof.TripleDes.Bitslice (blockOut wAt)
open VG.Proof.TripleDes.RISCV64.Bitsliced

/-- The buffer's 64 words transposed, through the passes, and back: each is
its block's encryption or decryption, and `rest` runs after. -/
theorem words_wp (d : Direction) {s : State} (h : Room s) (hm : MasksAt s) {rest : Prog isa}
    {Q : State → Prop}
    (k : ∀ s', (∀ b < 64, blockAt s'.mem (wAt (s.gpr .s0) b) =
        blockOut (scheduleAt s.mem (schedA s)) d (blockAt s.mem (wAt (s.gpr .s0) b))) →
      (∀ r ∈ Bitsliced.passKept, s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      Frame [stR s] s.mem s'.mem → WP isa rest s' Q) :
    WP isa (.seq transposeCall (.seq (passes d) (.seq transposeCall rest))) s Q := by
  apply WP.seq
  refine WP.mono (transposeCall_ok h hm) fun s₃ ⟨w₃, rd₃, wr₃, _, s0₃, a1₃, a2₃, s11₃, f₃⟩ => ?_
  obtain h₃ : Room s₃ := h.congr s0₃ wr₃
  apply WP.seq
  refine WP.mono (passes_ok d h₃) fun s₄ ⟨w₄, k₄, rd₄, wr₄, _, f₄⟩ => ?_
  obtain s0₄ : s₄.gpr .s0 = s.gpr .s0 := (k₄ _ (by decide)).trans s0₃
  obtain h₄ : Room s₄ := h.congr s0₄ (wr₄.trans wr₃)
  obtain fs₄ : Frame [stR s] s.mem s₄.mem := f₃.trans (by rw [← stR_congr s0₃]; exact f₄)
  obtain K₃ : scheduleAt s₃.mem (schedA s₃) = scheduleAt s.mem (schedA s) := by
    rw [show schedA s₃ = schedA s by simp only [schedA, s0₃]]; exact sched_frame h f₃
  apply WP.seq
  refine WP.mono (transposeCall_ok h₄ (masksAt_frame s0₄ h fs₄ hm))
    fun s₅ ⟨w₅, rd₅, wr₅, _, s0₅, a1₅, a2₅, s11₅, f₅⟩ => ?_
  obtain fs₅ : Frame [stR s] s.mem s₅.mem := fs₄.trans (by rw [← stR_congr s0₄]; exact f₅)
  refine k s₅ (fun b hb => ?_) (fun r hr => ?_) (rd₅.trans (rd₄.trans rd₃)) (wr₅.trans (wr₄.trans wr₃)) fs₅
  · have lane₃ : VG.Proof.TripleDes.Bitslice.ipLane (words s₃) b =
        Spec.TripleDes.permute Spec.TripleDes.ip (Spec.TripleDes.decodeBlock (blockAt s.mem (wAt (s.gpr .s0) b))) := by
      rw [VG.Proof.TripleDes.Bitslice.ipLane_congr w₃ b]
      refine VG.Proof.TripleDes.Bitslice.ipLane_transpose _ _ hb fun j hj => ?_
      exact readW_bit s.mem (wAt (s.gpr .s0) b) hj
    obtain word₅ : s₅.mem.readW (wAt (s.gpr .s0) b) 64 = VG.Proof.TripleDes.Bitslice.transposeW (words s₄) b := by
      rw [← w₅ b hb]
      simp only [words, sl, Straight.wordAddr, s0₅, s0₄, wAt]
    rw [VG.Proof.TripleDes.Bitslice.blockOut_cores]
    apply blockAt_of_readW
    intro j hj
    rw [word₅, VG.Proof.TripleDes.Bitslice.transpose_out _ _ j hj,
      VG.Proof.TripleDes.Bitslice.ipLane_congr w₄ b, VG.Proof.TripleDes.Bitslice.tdeaW_lane _ _ _ hb,
      lane₃, K₃]
  · simp only [Bitsliced.passKept, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [s0₅, s0₄]
    · rw [a1₅, k₄ _ (by decide), a1₃]
    · rw [a2₅, k₄ _ (by decide), a2₃]
    · rw [s11₅, k₄ _ (by decide), s11₃]

/-! ## The core -/

/-- ECB's base in the frame at `B`. -/
abbrev wideA (B : Addr) : Addr := B + BitVec.ofNat 64 wideOff

/-- The key is ready for the wide core: the schedules' copy in the frame at
`B` is `k`, and ECB's masks are stored. -/
def ReadyW (s : State) (B : Addr) (_ws : List Region) (k : Schedule) : Prop :=
  scheduleAt s.mem (B + BitVec.ofNat 64 keyOff) = k ∧
    (∀ j < 6, s.mem.readW (Straight.wordAddr (wideA B) (112 + j)) 64 =
      Bitslice.swapMask (Bitslice.maskShifts.getD j 1)) ∧
    B.toNat + 8 * 138 ≤ 2 ^ 64

theorem layoutW (d : Direction) : Layout (wideInline d) :=
  ⟨by cases d <;> decide, .inl rfl, by cases d <;> decide, by cases d <;> decide,
    by cases d <;> decide, by cases d <;> decide, by cases d <;> decide⟩

theorem wideSaved_fits : Spill.Fits wideSaved := by decide
theorem wideSaved_in : ∀ p ∈ wideSaved, 968 ≤ p.2 ∧ p.2 + 8 ≤ 968 + 80 := by decide
theorem wideSaved_ne : ∀ p ∈ wideSaved, p.1 ≠ .t0 := by decide

/-- The registers the core keeps that it does not save. -/
theorem kept_cases : ∀ r ∈ kept, r ∈ wideSaved.map Prod.fst ∨ r = .s1 ∨ r = .s2 ∨ r = .s3 ∨ r = .s4 := by
  decide

theorem kept_not_tmp : ∀ r ∈ kept, r ≠ .t0 ∧ r ≠ .t1 ∧ r ≠ .t2 ∧ r ≠ .t4 ∧ r ≠ .t5 := by decide

theorem blockOut_eq (K : Schedule) (d : Direction) (b : Spec.TripleDes.Block) :
    blockOut K d b = blockResult K d b := by cases d <;> rfl

theorem crypt_wpW (d : Direction) {s : State} {B : Addr} {ws : List Region} {k : Schedule}
    (hB : s.gpr sb = B) (hS : ScrIn s B (wideInline d).total) (hR : ReadyW s B ws k) :
    WP isa (wideInline d).crypt s fun s' => s'.gpr sb = B ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      ReadyW s' B ws k ∧ Frame [coreRegion (wideInline d) B] s.mem s'.mem ∧
      (∀ j < (wideInline d).G, Spec.Aes.bytesAt s'.mem (blkAddr (wideInline d) B j) (4 * (wideInline d).bw) =
        dirCipher d k (Spec.Aes.bytesAt s.mem (blkAddr (wideInline d) B j) (4 * (wideInline d).bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨hk, hmask, -⟩ := hR
  obtain hfit : B.toNat + 8 * 138 ≤ 2 ^ 64 := hS.fit
  obtain hal : B.toNat % 16 = 0 := hS.al
  obtain hwhole : (⟨B, 8 * 138⟩ : Region) ∈ s.wr := hS.whole (by cases d <;> decide)
  obtain hwo : wideOff = 48 := rfl
  let W := wideA B
  obtain inW : ∀ o n, o + n ≤ 1056 → InRegions s.wr (W + BitVec.ofNat 64 o) n := fun o n h => by
    show InRegions s.wr (B + BitVec.ofNat 64 wideOff + BitVec.ofNat 64 o) n
    rw [Offset.add_add]
    exact ⟨_, hwhole, Offset.contains_base _ (by omega_using [h, hwo]) (by omega_using [h, hwo])⟩
  obtain WN : W.toNat = B.toNat + 48 := by
    show (B + BitVec.ofNat 64 wideOff).toNat = _
    rw [Offset.toNat_add_ofNat]; omega_using [hfit, hwo]
  obtain alW : W.toNat % 8 = 0 := by omega_using [WN, hal]
  show WP isa (wideCrypt d) s _
  unfold wideCrypt
  apply WP.seq
  -- the registers saved, ECB's base, the modes' state parked
  show WP isa (.block (.addi .t0 sb (wideOff : Nat) :: (Spill.saveCode .t0 wideSaved ++
    ([movR .s0 .t0, movR .a1 .s1, movR .a2 .s2, movR .s11 .s3] : List Instr)))) s _
  refine wp_addi (by decide) fun u₁ h₁ => ?_
  obtain t0₁ : u₁.gpr .t0 = W := by rw [h₁.gpr, hB]
  refine Spill.save_ok (by rw [t0₁]; exact alW) wideSaved_fits.1
    (fun p hp => by
      rw [t0₁, h₁.wr]; exact inW p.2 8 (by have := wideSaved_in p hp; omega_using [this])) ?_
  refine wp_mv fun u₂ h₂ => wp_mv fun u₃ h₃ => wp_mv fun u₄ h₄ => wp_mv fun u₅ h₅ => WP.block_nil ?_
  obtain g₅ : ∀ r, r ≠ .s0 → r ≠ .a1 → r ≠ .a2 → r ≠ .s11 → u₅.gpr r = u₁.gpr r := fun r a b c e => by
    rw [h₅.other r e, h₄.other r c, h₃.other r b, h₂.other r a]
  obtain s0₅ : u₅.gpr .s0 = W := by
    rw [h₅.other _ (by decide), h₄.other _ (by decide), h₃.other _ (by decide), h₂.gpr]; exact t0₁
  obtain a1₅ : u₅.gpr .a1 = s.gpr .s1 := by
    rw [h₅.other _ (by decide), h₄.other _ (by decide), h₃.gpr, h₂.other _ (by decide)]
    exact h₁.other _ (by decide)
  obtain a2₅ : u₅.gpr .a2 = s.gpr .s2 := by
    rw [h₅.other _ (by decide), h₄.gpr, h₃.other _ (by decide), h₂.other _ (by decide)]
    exact h₁.other _ (by decide)
  obtain s11₅ : u₅.gpr .s11 = s.gpr .s3 := by
    rw [h₅.gpr, h₄.other _ (by decide), h₃.other _ (by decide), h₂.other _ (by decide)]
    exact h₁.other _ (by decide)
  obtain ra₅ : u₅.gpr .ra = s.gpr .ra := by
    rw [g₅ _ (by decide) (by decide) (by decide) (by decide)]; exact h₁.other _ (by decide)
  obtain m₅ : u₅.mem = Spill.saveMem s.mem W u₁.gpr wideSaved := by
    rw [h₅.mem, h₄.mem, h₃.mem, h₂.mem]
    show Spill.saveMem u₁.mem (u₁.gpr .t0) u₁.gpr wideSaved = _
    rw [t0₁, h₁.mem]
  obtain wr₅ : u₅.wr = s.wr := by rw [h₅.wr, h₄.wr, h₃.wr, h₂.wr]; exact h₁.wr
  obtain rd₅ : u₅.rd = s.rd := by rw [h₅.rd, h₄.rd, h₃.rd, h₂.rd]; exact h₁.rd
  obtain fsave : Frame [⟨W + BitVec.ofNat 64 968, 80⟩] s.mem u₅.mem := by
    rw [m₅]; exact Spill.saveMem_frame wideSaved_in (by decide) _ _ _
  obtain sv₅ : Spill.Saved W u₁.gpr wideSaved u₅.mem := by
    rw [m₅]; exact Spill.saveMem_saved wideSaved_fits _ _ _
  obtain hroom : Room u₅ :=
    ⟨fun o n h => by rw [s0₅, wr₅]; exact inW o n h, by rw [s0₅]; exact alW,
      by rw [s0₅]; unfold Bitslice.frameBytes; omega_using [WN, hfit]⟩
  obtain hmasks : MasksAt u₅ := fun j hj => by
    rw [s0₅, ← hmask j hj]
    refine fsave.readW (Region.contains_self _ 8) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (.inl (by omega_using [hj])) (by omega_using [hj]) (by decide)
  obtain hsched : scheduleAt u₅.mem (schedA u₅) = k := by
    obtain e : schedA u₅ = B + BitVec.ofNat 64 keyOff := by
      show u₅.gpr .s0 + BitVec.ofNat 64 Bitslice.schedOff = _
      rw [s0₅]; show B + BitVec.ofNat 64 wideOff + BitVec.ofNat 64 Bitslice.schedOff = _
      rw [Offset.add_add]; rfl
    rw [e, scheduleAt_eq_of_frame _ fsave fun r hr => ?_, hk]
    simp only [List.mem_singleton] at hr; subst hr
    show Region.Disjoint ⟨B + BitVec.ofNat 64 keyOff, 384⟩ ⟨B + BitVec.ofNat 64 wideOff + BitVec.ofNat 64 968, 80⟩
    rw [Offset.add_add]
    exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
  -- the buffer through ECB
  refine words_wp d hroom hmasks fun s₆ blk₆ k₆ rd₆ wr₆ f₆ => ?_
  obtain s0₆ : s₆.gpr .s0 = W := (k₆ _ (by decide)).trans s0₅
  show WP isa (.block (movR .s1 .a1 :: movR .s2 .a2 :: movR .s3 .s11 ::
    .addi sb .s0 (-((wideOff : Nat) : Int)) :: Spill.restoreCode .s0 wideSaved)) s₆ _
  refine wp_mv fun v₁ g₁ => wp_mv fun v₂ g₂ => wp_mv fun v₃ g₃ => wp_subi (by decide) fun v₄ g₄ => ?_
  obtain mem₄ : v₄.mem = s₆.mem := by rw [g₄.mem, g₃.mem, g₂.mem, g₁.mem]
  obtain wr₄ : v₄.wr = s.wr := by rw [g₄.wr, g₃.wr, g₂.wr, g₁.wr, wr₆, wr₅]
  obtain rd₄ : v₄.rd = s.rd := by rw [g₄.rd, g₃.rd, g₂.rd, g₁.rd, rd₆, rd₅]
  obtain s0₄ : v₄.gpr .s0 = W := by
    rw [g₄.other _ (by decide), g₃.other _ (by decide), g₂.other _ (by decide), g₁.other _ (by decide)]
    exact s0₆
  obtain sb₄ : v₄.gpr sb = B := by
    rw [g₄.gpr, g₃.other _ (by decide), g₂.other _ (by decide), g₁.other _ (by decide), s0₆]
    exact BitVec.add_sub_cancel B _
  obtain s1₄ : v₄.gpr .s1 = s.gpr .s1 := by
    rw [g₄.other _ (by decide), g₃.other _ (by decide), g₂.other _ (by decide), g₁.gpr, k₆ _ (by decide), a1₅]
  obtain s2₄ : v₄.gpr .s2 = s.gpr .s2 := by
    rw [g₄.other _ (by decide), g₃.other _ (by decide), g₂.gpr, g₁.other _ (by decide), k₆ _ (by decide), a2₅]
  obtain s3₄ : v₄.gpr .s3 = s.gpr .s3 := by
    rw [g₄.other _ (by decide), g₃.gpr, g₂.other _ (by decide), g₁.other _ (by decide), k₆ _ (by decide), s11₅]
  obtain stW : stR u₅ = ⟨W, 512⟩ := by simp only [stR, s0₅]
  obtain sv₄ : Spill.Saved W u₁.gpr wideSaved v₄.mem := by
    rw [mem₄]
    refine sv₅.frame_in wideSaved_in f₆ fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr; rw [stW]
    exact Offset.disjoint_base _ (by decide) (by decide)
  refine WP.mono (Spill.restore_wp alW s0₄ wideSaved_fits.1 (by decide)
    (fun p hp => by
      obtain ⟨r, hr, hc⟩ := inW p.2 8 (by have := wideSaved_in p hp; omega_using [this])
      exact ⟨r, List.mem_append_right _ (wr₄ ▸ hr), hc⟩) sv₄) fun s' hres => ?_
  obtain mem' : s'.mem = s₆.mem := hres.mem.trans mem₄
  obtain fall : Frame [(⟨W, 512⟩ : Region), ⟨W + BitVec.ofNat 64 968, 80⟩] s.mem s'.mem := by
    rw [mem']
    exact (fsave.mono fun r hr => List.mem_cons_of_mem _ hr).trans
      ((stW ▸ f₆).mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self)
  refine ⟨by rw [hres.other _ (by decide)]; exact sb₄, fun r hr => ?_, ⟨?_, fun j hj => ?_, hfit⟩, ?_,
    fun j hj => ?_, hres.rd.trans rd₄, hres.wr.trans wr₄⟩
  · rcases kept_cases r hr with hm | rfl | rfl | rfl | rfl
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
      rw [hres.gpr p hp]; exact h₁.other _ (wideSaved_ne p hp)
    · rw [hres.other _ (by decide)]; exact s1₄
    · rw [hres.other _ (by decide)]; exact s2₄
    · rw [hres.other _ (by decide)]; exact s3₄
    · rw [hres.other _ (by decide)]; exact sb₄.trans hB.symm
  · rw [scheduleAt_eq_of_frame _ fall fun r hr => ?_, hk]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · show Region.Disjoint ⟨B + BitVec.ofNat 64 keyOff, 384⟩ ⟨B + BitVec.ofNat 64 wideOff, 512⟩
      exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)
    · show Region.Disjoint ⟨B + BitVec.ofNat 64 keyOff, 384⟩ ⟨B + BitVec.ofNat 64 wideOff + BitVec.ofNat 64 968, 80⟩
      rw [Offset.add_add]
      exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
  · rw [← hmask j hj]
    refine fall.readW (Region.contains_self _ 8) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint_base _ (by omega_using [hj]) (by omega_using [hj])
    · exact Offset.disjoint _ (.inl (by omega_using [hj])) (by omega_using [hj]) (by decide)
  · refine fall.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Region.sub_prefix (by cases d <;> decide)
    · exact Offset.sub_base _ (by cases d <;> decide)
  · have hj64 : j < 64 := hj
    obtain e : blkAddr (wideInline d) B j = wAt W j := by
      show B + BitVec.ofNat 64 (8 * bufSlot) + BitVec.ofNat 64 (4 * 2 * j) = B + BitVec.ofNat 64 wideOff + BitVec.ofNat 64 (8 * j)
      rfl
    obtain b₅ : blockAt u₅.mem (wAt W j) = blockAt s.mem (wAt W j) :=
      VG.Proof.TripleDes.Bitslice.blockAt_frame fsave fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inl (by omega_using [hj64])) (by omega_using [hj64]) (by decide)
    obtain b₆ := blk₆ j hj64
    rw [s0₅, hsched, b₅, blockOut_eq] at b₆
    rw [show 4 * (wideInline d).bw = 8 from rfl, e, bytesAt_eq, mem', b₆, dirCipher_bytes]

/-- The key stays ready through what the mode writes: the schedules' copy
and the masks are in the core's slots, apart from its buffer. -/
theorem ready_frameW (d : Direction) {s s' : State} {B : Addr} {ws : List Region} {k : Schedule}
    {rs : List Region} (h : ReadyW s B ws k) (hf : Frame rs s.mem s'.mem)
    (hc : ∀ r ∈ rs, Region.Disjoint (coreRegion (wideInline d) B) r ∨
      Region.Sub r (blkRegion (wideInline d) B)) :
    ReadyW s' B ws k := by
  obtain ⟨hk, hmask, hfit⟩ := h
  refine ⟨?_, fun j hj => ?_, hfit⟩
  · rw [scheduleAt_eq_of_frame _ hf fun r hr => ?_, hk]
    rcases hc r hr with h | h
    · exact h.sub_left (Offset.sub _ (by cases d <;> decide) (by cases d <;> decide))
    · exact Region.Disjoint.sub_right
        (Offset.disjoint _ (.inr (by cases d <;> decide)) (by decide) (by cases d <;> decide)) h
  · rw [← hmask j hj]
    refine hf.readW (Region.contains_self _ 8) (fun r hr => ?_) (by decide)
    rcases hc r hr with h | h
    · refine h.sub_left ?_
      show Region.Sub ⟨B + BitVec.ofNat 64 wideOff + BitVec.ofNat 64 (8 * (112 + j)), 8⟩ _
      exact Offset.sub_base _ (by cases d <;> (dsimp only [wideInline, Impl.Modes.RISCV64.coreSlot]; omega_using [hj]))
    · refine Region.Disjoint.sub_right ?_ h
      show Region.Disjoint ⟨B + BitVec.ofNat 64 wideOff + BitVec.ofNat 64 (8 * (112 + j)), 8⟩
        ⟨B + BitVec.ofNat 64 wideOff, 512⟩
      exact Offset.disjoint_base _ (by omega_using [hj]) (by omega_using [hj])

theorem prepare_wpW (d : Direction) {s : State} {B : Addr} {rs : List Region} {k : Schedule}
    (hB : s.gpr sb = B) (hS : ScrIn s B (wideInline d).total)
    (hm : (⟨B, 8 * (wideInline d).total⟩ : Region) ∈ rs) (hk : KeyArgs s rs k) :
    WP isa (wideInline d).prepare s fun s' => ReadyW s' B rs k ∧ s'.gpr sb = B ∧
      (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ Frame [coreRegion (wideInline d) B] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain hfit : B.toNat + 8 * 138 ≤ 2 ^ 64 := hS.fit
  obtain hal : B.toNat % 16 = 0 := hS.al
  obtain hwhole : (⟨B, 8 * 138⟩ : Region) ∈ s.wr := hS.whole (by cases d <;> decide)
  obtain hwo : wideOff = 48 := rfl
  obtain ⟨hkk, hin, hd⟩ := hk
  obtain dK : (keyR s).Disjoint ⟨B, 8 * 138⟩ := hd _ hm
  obtain hmin : min (8 * (wideInline d).total) 2032 = 1104 := by cases d <;> rfl
  let W := wideA B
  obtain WN : W.toNat = B.toNat + 48 := by
    show (B + BitVec.ofNat 64 wideOff).toNat = _
    rw [Offset.toNat_add_ofNat]; omega_using [hfit, hwo]
  show WP isa widePrepare s _
  unfold widePrepare
  apply WP.seq
  refine WP.mono (copy_wp hB (fun o w h => hS.low o w (by rw [hmin]; omega_using [h])) hkk hin
    (Region.Disjoint.sub_left (Region.Disjoint.symm dK) (Offset.sub_base _ (by decide))))
    fun a ⟨ka, ga, fa, rda, wra⟩ => ?_
  show WP isa (.block (movR .t5 .s0 :: .addi .s0 sb (wideOff : Nat) ::
    (Bitslice.storeMasks ++ ([movR .s0 .t5] : List Instr)))) a _
  refine wp_mv fun u₁ h₁ => wp_addi (by decide) fun u₂ h₂ => ?_
  rw [WP.block_append_iff, storeMasks_eq]
  obtain s0₂ : u₂.gpr .s0 = W := by
    rw [h₂.gpr, h₁.other _ (by decide), ga _ (by decide) (by decide) (by decide) (by decide), hB]
  obtain t5₂ : u₂.gpr .t5 = s.gpr .s0 := by
    rw [h₂.other _ (by decide), h₁.gpr, ga _ (by decide) (by decide) (by decide) (by decide)]
  obtain g₂ : ∀ r, r ≠ .s0 → r ≠ .t5 → u₂.gpr r = a.gpr r := fun r h0 h5 => by
    rw [h₂.other _ h0, h₁.other _ h5]
  obtain wr₂ : u₂.wr = s.wr := by rw [h₂.wr, h₁.wr, wra]
  obtain rd₂ : u₂.rd = s.rd := by rw [h₂.rd, h₁.rd, rda]
  obtain mem₂ : u₂.mem = a.mem := by rw [h₂.mem, h₁.mem]
  obtain hroom : Room u₂ :=
    ⟨fun o n h => by
        rw [s0₂, wr₂]
        show InRegions s.wr (B + BitVec.ofNat 64 wideOff + BitVec.ofNat 64 o) n
        rw [Offset.add_add]
        exact ⟨_, hwhole, Offset.contains_base _ (by unfold Bitslice.frameBytes at h; omega_using [h, hwo])
          (by unfold Bitslice.frameBytes at h; omega_using [h, hwo])⟩,
      by rw [s0₂]; omega_using [WN, hal],
      by rw [s0₂]; unfold Bitslice.frameBytes; omega_using [WN, hfit]⟩
  refine WP.mono (masks_ok hroom 6 (Nat.le_refl _)) fun v ⟨m, g, w, f, rdv⟩ => ?_
  refine wp_mv fun u₃ h₃ => WP.block_nil ?_
  obtain hmr : maskR u₂ = ⟨W + BitVec.ofNat 64 896, 48⟩ := by simp only [maskR, s0₂]
  rw [hmr, mem₂] at f
  obtain g₃ : ∀ r, r ≠ .s0 → r ≠ .t0 → r ≠ .t1 → r ≠ .t2 → r ≠ .t4 → r ≠ .t5 → u₃.gpr r = s.gpr r :=
    fun r h0 a0 a1 a2 a4 a5 => by
      rw [h₃.other _ h0, g r a0 a1, g₂ r h0 a5, ga r a0 a1 a2 a4]
  obtain s0₃ : u₃.gpr .s0 = s.gpr .s0 := by rw [h₃.gpr, g _ (by decide) (by decide), t5₂]
  obtain fall : Frame [coreRegion (wideInline d) B] s.mem u₃.mem := by
    rw [h₃.mem]
    refine (fa.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      (f.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by cases d <;> decide) (by cases d <;> decide)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub_base _ (by cases d <;> decide)
  refine ⟨⟨?_, fun j hj => ?_, hfit⟩,
    by rw [g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hB,
    fun r hr => ?_, fall, by rw [h₃.rd, rdv, rd₂], by rw [h₃.wr, w, wr₂]⟩
  · rw [h₃.mem, scheduleAt_eq_of_frame _ f fun r hr => ?_, ka]
    simp only [List.mem_singleton] at hr; subst hr
    show Region.Disjoint ⟨B + BitVec.ofNat 64 keyOff, 384⟩ ⟨B + BitVec.ofNat 64 wideOff + BitVec.ofNat 64 896, 48⟩
    rw [Offset.add_add]
    exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
  · rw [h₃.mem]; have e := m j hj; rw [s0₂] at e; exact e
  · by_cases e : r = .s0
    · subst e; exact s0₃
    · obtain ⟨a0, a1, a2, a4, a5⟩ := kept_not_tmp r hr
      exact g₃ r e a0 a1 a2 a4 a5

/-- Triple DES's core on 64 blocks for the direction `d` meets what the
modes need. -/
def wideInlineSpec (d : Direction) : CoreSpec (wideInline d) where
  Key := Schedule
  cipher := dirCipher d
  KeyArgs := KeyArgs
  Ready := ReadyW
  cipher_len _ _ := by
    cases d <;> simp [dirCipher, Spec.TripleDes.cipher, Spec.TripleDes.invCipher, wideInline]
  layout := layoutW d
  keyArgs_congr h e r w _ f := keyArgs_congr h e.a0 r w f
  ready_frame h _ _ _ _ f _ hc := ready_frameW d h f hc
  prepare_wp := prepare_wpW d
  crypt_wp := crypt_wpW d

open VG.Proof.Modes.RISCV64 (KeyMove ReadyMove SharedReady originalState)

theorem shared_keyW (d : Direction) : KeyMove (wideInlineSpec d) := by
  intro s t rs ts k hk ha rd wr hf hs
  obtain ⟨hk, hin, hd⟩ := keyArgs_congr hk ha rd wr hf
  exact ⟨hk, hin, fun r hr => by
    obtain ⟨r', hr', sub⟩ := hs r hr
    exact (hd r' hr').sub_right sub⟩

theorem shared_readyW (d : Direction) : ReadyMove (wideInlineSpec d) := by
  intro s t B ws k rs hr ha rd wr hf hs hd
  exact ready_frameW d (ws := ws) hr hf hd

/-- The core as the modes call it: its code in two functions they share. -/
def wideCoreSpec (d : Direction) : CoreSpec (wideCore d) :=
  (wideInlineSpec d).shared (by cases d <;> decide) (by left; cases d <;> decide)
    (shared_keyW d) (shared_readyW d) (by cases d <;> rfl) (by cases d <;> rfl) _ _

theorem layoutS (d : Direction) : Layout (wideCore d) := (wideCoreSpec d).layout

/-- The block function on the buffer's first block is the core on one
block: it writes that block and the 63 after it, its working space. -/
theorem wideOne_wp (d : Direction) {s : State} {B : Addr} {ws : List Region} {k : Schedule}
    (hB : s.gpr sb = B) (hS : ScrIn s B (wideCore d).total) (hR : SharedReady (wideInlineSpec d) s B ws k) :
    WP isa (wideOne d) s fun s' => s'.gpr sb = B ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      SharedReady (wideInlineSpec d) s' B ws k ∧ Frame [coreRegion (wideCore d) B] s.mem s'.mem ∧
      Spec.Aes.bytesAt s'.mem (blkAddr (wideCore d) B 0) (4 * (wideCore d).bw) =
        dirCipher d k (Spec.Aes.bytesAt s.mem (blkAddr (wideCore d) B 0) (4 * (wideCore d).bw)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨rs, hrs, hR⟩ := hR
  obtain hR : ReadyW (originalState (wideInline d) s B) B rs k := hR
  obtain hfit : B.toNat + 8 * 140 ≤ 2 ^ 64 := hS.fit
  obtain hal : B.toNat % 16 = 0 := hS.al
  obtain hbo : bufOff = 48 := rfl
  obtain hk : scheduleAt s.mem (B + BitVec.ofNat 64 keyOff) = k := hR.1
  obtain hlow : (⟨B, 1120⟩ : Region) ∈ s.wr := hS.whole (by cases d <;> decide)
  obtain hpre : BlockPre k sb bufOff s := by
    refine ⟨by decide, by decide, by rw [hB]; omega_using [hal], fun o ho => ?_, by rw [hB]; exact hk,
      ⟨_, hlow, ?_⟩, ?_⟩
    · rw [hB]; exact ⟨_, hlow, Offset.contains_base _ (by omega_using [ho]) (by omega_using [ho])⟩
    · rw [hB]; exact Offset.contains_base _ (by decide) (by omega_using [hbo])
    · simp only [workRegion, hB, bufOff, bufSlot]
      exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
  show WP isa (block d sb bufOff) s _
  refine WP.mono (block_ok k d sb bufOff s hpre) fun t ht => ?_
  obtain hBt : t.gpr sb = B := (ht.regs sb (by decide)).trans hB
  obtain hblk : ∀ r ∈ [(⟨s.gpr sb + BitVec.ofNat 64 bufOff, 8⟩ : Region), workRegion s],
      Region.Sub r (blkRegion (wideInline d) B) := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [hB]; exact Region.sub_prefix (by cases d <;> decide)
    · simp only [workRegion, hB]
      show Region.Sub ⟨B + BitVec.ofNat 64 56, 504⟩ ⟨B + BitVec.ofNat 64 48, 4 * 2 * 64⟩
      rw [show (56 : Nat) = 48 + 8 from rfl, ← Offset.add_add]
      exact Offset.sub_base _ (by decide)
  obtain hcore : Region.Sub (blkRegion (wideInline d) B) (coreRegion (wideCore d) B) :=
    Region.sub_prefix (by cases d <;> decide)
  refine ⟨hBt, fun r hr => ht.regs r (kept_sub r hr),
    ⟨rs, hrs, (ready_frameW d hR (s' := originalState (wideInline d) t B) (ht.frame : Frame _ s.mem t.mem)
      fun r hr => .inr (hblk r hr) :)⟩,
    ht.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, fun x hx => hcore x (hblk r hr x hx)⟩,
    ?_, ht.rd, ht.wr⟩
  obtain e : blkAddr (wideCore d) B 0 = s.gpr sb + BitVec.ofNat 64 bufOff := by
    rw [hB]; show B + BitVec.ofNat 64 (8 * bufSlot) + BitVec.ofNat 64 (4 * 2 * 0) = _
    exact BitVec.add_zero _
  rw [show 4 * (wideCore d).bw = 8 from rfl, e, bytesAt_eq, ht.result]
  exact (dirCipher_bytes d k s.mem _).symm

theorem wideOne_ok (d : Direction) : OneOk (wideCoreSpec d) (wideOne d) := fun hB hS hR =>
  wideOne_wp d hB hS hR

end VG.Proof.TripleDes.RISCV64.Mode
