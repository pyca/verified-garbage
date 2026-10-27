module

public import VerifiedGarbage.Proof.Modes.RISCV64.Core
public import VerifiedGarbage.Impl.TripleDes.RISCV64.Ecb
public import VerifiedGarbage.Proof.TripleDes.CbcBlocks
import VerifiedGarbage.Proof.TripleDes.RISCV64.BlockOk
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.Framework.RISCV64.Loops
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.TripleDes.RISCV64.Block

/-!
# Triple DES's core for the modes on RISC-V

`dirCoreSpec d`: Triple DES's core for the direction `d`
(`Impl.TripleDes.RISCV64.dirCore d`) meets what the modes need of a core
(`Proof.Modes.RISCV64.CoreSpec`), with the key a schedule, its cipher
`Proof.TripleDes.dirCipher d`. The schedule at `a0` is readable and apart
from the regions the mode writes (`KeyArgs`); `prepare` copies it into the
frame (`copyLoop_ok`), and the key is ready when the copy is the schedule
(`Ready`), which nothing the mode writes changes: the copy is in the core's
slots, apart from its buffer. The core runs the block function on its
buffer (`block_ok`).
-/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64.Mode

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.TripleDes.RISCV64
open VG.Proof.Modes.RISCV64 (coreRegion blkRegion blkAddr slotA CoreSpec Layout ScrIn kept KeptBut)
open VG.Spec.TripleDes (Direction Schedule)
open VG.Proof.TripleDes (dirCipher bytesAt_eq ofFn_bytesAt scheduleAt_eq_of_frame scheduleAt_copy)

/-- The schedule. -/
abbrev keyR (s : State) : Region := ⟨s.gpr .a0, 384⟩

/-- The schedule at `a0` is `k`, readable, and apart from the regions `rs`. -/
def KeyArgs (s : State) (rs : List Region) (k : Schedule) : Prop :=
  Spec.TripleDes.scheduleAt s.mem (s.gpr .a0) = k ∧ keyR s ∈ s.rd ++ s.wr ∧
    ∀ r ∈ rs, (keyR s).Disjoint r

/-- The schedule's copy in the frame at `B` is `k`. -/
def Ready (s : State) (B : Addr) (_ws : List Region) (k : Schedule) : Prop :=
  Spec.TripleDes.scheduleAt s.mem (B + BitVec.ofNat 64 keyOff) = k ∧ B.toNat + 8 * 118 ≤ 2 ^ 64

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Schedule} (h : KeyArgs s rs k)
    (e : s'.gpr .a0 = s.gpr .a0) (hrd : s'.rd = s.rd) (hwr : ∃ ws, s'.wr = ws ++ s.wr)
    (hf : Frame rs s.mem s'.mem) : KeyArgs s' rs k := by
  obtain ⟨hk, hin, hd⟩ := h
  obtain ⟨ws, hw⟩ := hwr
  refine ⟨?_, ?_, by rw [keyR, e]; exact hd⟩
  · rw [e, scheduleAt_eq_of_frame _ hf hd, hk]
  · rw [hrd, hw, keyR, e]
    rcases List.mem_append.mp hin with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_append_right _ h)

/-- The copy is in the core's slots, apart from its buffer. -/
theorem copy_sub (d : Direction) (B : Addr) :
    Region.Sub ⟨B + BitVec.ofNat 64 keyOff, 384⟩ (coreRegion (dirCore d) B) :=
  Offset.sub _ (by cases d <;> decide) (by cases d <;> decide)

theorem copy_blk (d : Direction) (B : Addr) :
    Region.Disjoint ⟨B + BitVec.ofNat 64 keyOff, 384⟩ (blkRegion (dirCore d) B) :=
  Offset.disjoint _ (.inr (by cases d <;> decide)) (by decide) (by cases d <;> decide)

theorem ready_frame (d : Direction) {s s' : State} {B : Addr} {ws : List Region} {k : Schedule}
    {rs : List Region} (h : Ready s B ws k) (hf : Frame rs s.mem s'.mem)
    (hc : ∀ r ∈ rs, Region.Disjoint (coreRegion (dirCore d) B) r ∨
      Region.Sub r (blkRegion (dirCore d) B)) :
    Ready s' B ws k := by
  obtain ⟨hk, hfit⟩ := h
  refine ⟨?_, hfit⟩
  rw [scheduleAt_eq_of_frame _ hf fun r hr => ?_, hk]
  rcases hc r hr with h | h
  · exact h.sub_left (copy_sub d B)
  · exact (copy_blk d B).sub_right h

theorem layout (d : Direction) : Layout (dirCore d) :=
  ⟨by cases d <;> decide, .inl rfl, by cases d <;> decide, by cases d <;> decide,
    by cases d <;> decide, by cases d <;> decide, by cases d <;> decide⟩

theorem prepare_wp (d : Direction) {s : State} {B : Addr} {rs : List Region} {k : Schedule}
    (hB : s.gpr sb = B) (hS : ScrIn s B (dirCore d).total)
    (hm : (⟨B, 8 * (dirCore d).total⟩ : Region) ∈ rs) (hk : KeyArgs s rs k) :
    WP isa (dirCore d).prepare s fun s' => Ready s' B rs k ∧ s'.gpr sb = B ∧
      (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ Frame [coreRegion (dirCore d) B] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hfit : B.toNat + 8 * 118 ≤ 2 ^ 64 := hS.fit
  have hko : keyOff = 560 := rfl
  obtain ⟨hkk, hin, hd⟩ := hk
  have dK : (keyR s).Disjoint ⟨B, 8 * 118⟩ := hd _ hm
  show WP isa modePrepare s _
  unfold modePrepare
  apply WP.seq
  refine wp_addi (by decide) fun u₁ h₁ => wp_mv fun u₂ h₂ => wp_li (imm := 384) (by decide)
    fun a h₃ => WP.block_nil ?_
  have a0 : a.gpr .t0 = B + BitVec.ofNat 64 keyOff := by
    rw [h₃.other _ (by decide), h₂.other _ (by decide), h₁.gpr, hB]
  have a2 : a.gpr .t2 = s.gpr .a0 := by
    rw [h₃.other _ (by decide), h₂.gpr, h₁.other _ (by decide)]
  have ak : ∀ r, r ≠ .t0 → r ≠ .t2 → r ≠ .t4 → a.gpr r = s.gpr r := fun r h0 h2 h4 => by
    rw [h₃.other _ h4, h₂.other _ h2, h₁.other _ h0]
  have am : a.mem = s.mem := by rw [h₃.mem, h₂.mem, h₁.mem]
  have ard : a.rd = s.rd := by rw [h₃.rd, h₂.rd, h₁.rd]
  have awr : a.wr = s.wr := by rw [h₃.wr, h₂.wr, h₁.wr]
  refine WP.mono (copyLoop_ok (tmp := .t1) (src := .t2) (dst := .t0) (cnt := .t4) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) a (N := 384) (by decide) (by decide)
    h₃.gpr
    (fun i hi => by
      rw [a2, ard, awr]
      exact ⟨_, hin, Offset.contains_base _ (by omega) (by omega)⟩)
    (fun i hi => by
      rw [a0, awr, Offset.add_add]
      exact ⟨_, hS.low, Offset.contains_base _ (by simp only [dirCore, keyOff]; omega) (by omega)⟩)
    (by
      rw [a0, a2]
      have hs : Region.Sub ⟨B + BitVec.ofNat 64 keyOff, 384⟩ ⟨B, 8 * 118⟩ :=
        Offset.sub_base _ (by simp only [keyOff]; omega)
      have h : Region.Disjoint ⟨B + BitVec.ofNat 64 keyOff, 384⟩ ⟨s.gpr .a0, 384⟩ :=
        Region.Disjoint.sub_left (Region.Disjoint.symm dK) hs
      intro x hx hy
      exact h x (by simp only [Region.Contains]; omega) (by simp only [Region.Contains]; omega)))
    fun t ⟨tc, tf, tk⟩ => ?_
  rw [a0, a2, am] at tc
  rw [a0, am] at tf
  have gt : ∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .t2 → r ≠ .t4 → t.gpr r = s.gpr r := fun r h0 h1 h2 h4 => by
    rw [tk.gpr (by simp [h0, h1, h2, h4]), ak r h0 h2 h4]
  refine ⟨⟨by rw [scheduleAt_copy tc, hkk], hfit⟩,
    by rw [gt _ (by decide) (by decide) (by decide) (by decide)]; exact hB,
    fun r hr => gt r (by revert hr; decide +revert) (by revert hr; decide +revert)
      (by revert hr; decide +revert) (by revert hr; decide +revert),
    tf.sub fun r hr => ?_, by rw [tk.2.1, ard], by rw [tk.2.2, awr]⟩
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, List.mem_singleton_self _, copy_sub d B⟩

theorem dirCipher_bytes (d : Direction) (k : Schedule) (m : Mem) (p : Addr) :
    dirCipher d k (Spec.Aes.bytesAt m p 8) = (blockResult k d (Spec.TripleDes.blockAt m p)).toList := by
  cases d <;> simp only [dirCipher, Spec.TripleDes.cipher, Spec.TripleDes.invCipher, blockResult,
    ofFn_bytesAt]

theorem kept_sub : ∀ r ∈ kept, r ∈ blockKept := by decide

theorem crypt_wp (d : Direction) {s : State} {B : Addr} {ws : List Region} {k : Schedule}
    (hB : s.gpr sb = B) (hS : ScrIn s B (dirCore d).total) (hR : Ready s B ws k) :
    WP isa (dirCore d).crypt s fun s' => s'.gpr sb = B ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      Ready s' B ws k ∧ Frame [coreRegion (dirCore d) B] s.mem s'.mem ∧
      (∀ j < (dirCore d).G, Spec.Aes.bytesAt s'.mem (blkAddr (dirCore d) B j) (4 * (dirCore d).bw) =
        dirCipher d k (Spec.Aes.bytesAt s.mem (blkAddr (dirCore d) B j) (4 * (dirCore d).bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hfit : B.toNat + 8 * 118 ≤ 2 ^ 64 := hS.fit
  have hal : B.toNat % 16 = 0 := hS.al
  have hbo : bufOff = 48 := rfl
  obtain ⟨hk, _⟩ := hR
  have hlow : (⟨B, 944⟩ : Region) ∈ s.wr := hS.low
  have hpre : BlockPre k sb bufOff s := by
    refine ⟨by decide, by decide, by rw [hB]; omega, fun o ho => ?_, by rw [hB]; exact hk,
      ⟨_, hlow, ?_⟩, ?_⟩
    · rw [hB]; exact ⟨_, hlow, Offset.contains_base _ (by omega) (by omega)⟩
    · rw [hB]; exact Offset.contains_base _ (by decide) (by omega)
    · simp only [workRegion, hB, bufOff, bufSlot]
      exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
  show WP isa (block d sb bufOff) s _
  refine WP.mono (block_ok k d sb bufOff s hpre) fun t ht => ?_
  have hBt : t.gpr sb = B := (ht.regs sb (by decide)).trans hB
  have hsub : ∀ r ∈ [(⟨s.gpr sb + BitVec.ofNat 64 bufOff, 8⟩ : Region), workRegion s],
      Region.Sub r (coreRegion (dirCore d) B) := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [hB]; exact Offset.sub _ (by cases d <;> decide) (by cases d <;> decide)
    · simp only [workRegion, hB]; exact Offset.sub _ (by cases d <;> decide) (by cases d <;> decide)
  refine ⟨hBt, fun r hr => ht.regs r (kept_sub r hr), ⟨?_, hfit⟩,
    ht.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, hsub r hr⟩, fun j hj => ?_, ht.rd, ht.wr⟩
  · rw [scheduleAt_eq_of_frame _ ht.frame fun r hr => (copy_sub d B |> fun _ => ?_), hk]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [hB]; exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)
    · simp only [workRegion, hB]; exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)
  · obtain rfl : j = 0 := by simpa [dirCore] using hj
    have e : blkAddr (dirCore d) B 0 = s.gpr sb + BitVec.ofNat 64 bufOff := by
      rw [hB]; simp [blkAddr, slotA, dirCore, bufOff, bufSlot]
    rw [show 4 * (dirCore d).bw = 8 from rfl, e, bytesAt_eq, ht.result, dirCipher_bytes]

/-- Triple DES's core for the direction `d` meets what the modes need. -/
def dirCoreSpec (d : Direction) : CoreSpec (dirCore d) where
  Key := Schedule
  cipher := dirCipher d
  KeyArgs := KeyArgs
  Ready := Ready
  cipher_len _ _ := by cases d <;> simp [dirCipher, Spec.TripleDes.cipher, Spec.TripleDes.invCipher, dirCore]
  layout := layout d
  keyArgs_congr h e r w _ f := keyArgs_congr h e.a0 r w f
  ready_frame h _ _ _ _ f _ hc := ready_frame d h f hc
  prepare_wp := prepare_wp d
  crypt_wp := crypt_wp d

end VG.Proof.TripleDes.RISCV64.Mode
