module

public import VerifiedGarbage.Proof.Modes.RISCV64.Core
public import VerifiedGarbage.Impl.Blowfish.RISCV64.Modes
public import VerifiedGarbage.Proof.Blowfish.ModeBytes
import VerifiedGarbage.Proof.Blowfish.RISCV64.Ecb
import VerifiedGarbage.Proof.Blowfish.RISCV64.Cipher
import VerifiedGarbage.Proof.Blowfish.RISCV64.Run
import VerifiedGarbage.Proof.Blowfish.Schedule
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.RISCV64.Loops
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RISCV64.MRun
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill

/-!
# Blowfish's core for the modes on RISC-V

`dirCoreSpec up`: Blowfish's core (`Impl.Blowfish.RISCV64.dirCore up`) meets
what the modes need of a core (`Proof.Modes.RISCV64.CoreSpec`), with the key
a schedule, its cipher `Proof.Blowfish.dirCipher up`. The schedule at `a0`
is readable and apart from the regions the mode writes (`KeyArgs`);
`prepare` copies it into the frame after the buffer (`copyLoop_ok`), and the
key is ready when the copy is the schedule (`Ready`), which nothing the mode
writes changes: the copy is in the core's slots, apart from its buffer. The
core runs ECB's block function on its buffer under the copy
(`loadBlock_run`, `cipher_run`, `storeBlock_run`).
-/

@[expose] public section

namespace VG.Proof.Blowfish.RISCV64.Mode

open VG VG.RISCV64 VG.Impl.Blowfish.RISCV64 VG.Spec.Blowfish VG.Proof.Blowfish
open VG.Impl.Modes.RISCV64 (sb coreSlot mov)
open VG.WriteBytes (writeBytes)
open VG.RISCV64.ByteLoad (beBytes)
open VG.Proof.Modes.RISCV64 (coreRegion blkRegion blkAddr slotA CoreSpec Layout ScrIn kept KeptBut)

/-- The schedule. -/
abbrev keyR (s : State) : Region := ⟨s.gpr .a0, 4168⟩

/-- The schedule at `a0` is `k`, readable, and apart from the regions `rs`. -/
def KeyArgs (s : State) (rs : List Region) (k : Schedule) : Prop :=
  scheduleAt s.mem (s.gpr .a0) = k ∧ keyR s ∈ s.rd ++ s.wr ∧ ∀ r ∈ rs, (keyR s).Disjoint r

/-- The schedule's copy in the frame at `B` is `k`. -/
def Ready (s : State) (B : Addr) (_ws : List Region) (k : Schedule) : Prop :=
  scheduleAt s.mem (B + BitVec.ofNat 64 schOff) = k ∧ B.toNat + 8 * 528 ≤ 2 ^ 64

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
theorem copy_sub (up : Bool) (B : Addr) :
    Region.Sub ⟨B + BitVec.ofNat 64 schOff, 4168⟩ (coreRegion (dirCore up) B) :=
  Offset.sub _ (by cases up <;> decide) (by cases up <;> decide)

theorem copy_blk (up : Bool) (B : Addr) :
    Region.Disjoint ⟨B + BitVec.ofNat 64 schOff, 4168⟩ (blkRegion (dirCore up) B) :=
  Offset.disjoint _ (.inr (by cases up <;> decide)) (by simp only [schOff, bufOff, bufSlot]; omega)
    (by cases up <;> simp only [dirCore, bufSlot] <;> omega)

theorem ready_frame (up : Bool) {s s' : State} {B : Addr} {ws : List Region} {k : Schedule}
    {rs : List Region} (h : Ready s B ws k) (hf : Frame rs s.mem s'.mem)
    (hc : ∀ r ∈ rs, Region.Disjoint (coreRegion (dirCore up) B) r ∨ Region.Sub r (blkRegion (dirCore up) B)) :
    Ready s' B ws k := by
  obtain ⟨hk, hfit⟩ := h
  refine ⟨?_, hfit⟩
  rw [scheduleAt_eq_of_frame _ hf fun r hr => ?_, hk]
  rcases hc r hr with h | h
  · exact h.sub_left (copy_sub up B)
  · exact (copy_blk up B).sub_right h

theorem layout (up : Bool) : Layout (dirCore up) :=
  ⟨by cases up <;> decide, .inl rfl, by cases up <;> decide, by cases up <;> decide, by cases up <;> decide,
    by cases up <;> decide, by cases up <;> decide⟩

theorem prepare_wp (up : Bool) {s : State} {B : Addr} {rs : List Region} {k : Schedule}
    (hB : s.gpr sb = B) (hS : ScrIn s B (dirCore up).total) (hm : (⟨B, 8 * (dirCore up).total⟩ : Region) ∈ rs)
    (hk : KeyArgs s rs k) :
    WP isa (dirCore up).prepare s fun s' => Ready s' B rs k ∧ s'.gpr sb = B ∧
      (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ Frame [coreRegion (dirCore up) B] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hfit : B.toNat + 8 * 528 ≤ 2 ^ 64 := hS.fit
  have hB' : s.gpr .s4 = B := hB
  obtain ⟨hkk, hin, hd⟩ := hk
  have dK : (keyR s).Disjoint ⟨B, 8 * 528⟩ := hd _ hm
  show WP isa modePrepare s _
  unfold modePrepare
  apply WP.seq
  refine WP.mono (WP.keep [.t0, .t2, .t4] (Q := fun t => t.gpr .t0 = B + BitVec.ofNat 64 schOff ∧
      t.gpr .t2 = s.gpr .a0 ∧ t.gpr .t4 = BitVec.ofNat 64 4168 ∧ t.mem = s.mem) (by
    unfold li4168
    brun [hB', shl_4168, schOff, bufOff, bufSlot, sb]
    all_goals rfl) (by decide) rfl) fun a ⟨⟨a0, a2, a4, am⟩, ak⟩ => ?_
  refine WP.mono (copyLoop_ok (tmp := .t1) (src := .t2) (dst := .t0) (cnt := .t4) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) a (N := 4168) (by decide) (by decide) a4
    (fun i hi => by
      rw [a2, ak.2.1, ak.2.2]
      exact ⟨_, hin, Offset.contains_base _ (by omega) (by omega)⟩)
    (fun i hi => by
      rw [a0, ak.2.2, Offset.add_add]
      exact hS.wr _ _ (by decide) (by cases up <;> simp only [dirCore, schOff, bufOff, bufSlot] <;> omega)
        (by simp only [schOff, bufOff, bufSlot]; omega)) (by
      rw [a0, a2]
      have hs : Region.Sub ⟨B + BitVec.ofNat 64 schOff, 4168⟩ ⟨B, 8 * 528⟩ :=
        Offset.sub_base _ (by simp only [schOff, bufOff, bufSlot]; omega)
      have h : Region.Disjoint ⟨B + BitVec.ofNat 64 schOff, 4168⟩ ⟨s.gpr .a0, 4168⟩ :=
        Region.Disjoint.sub_left (Region.Disjoint.symm dK) hs
      intro x hx hy
      exact h x (by simp only [Region.Contains]; omega) (by simp only [Region.Contains]; omega))) fun t ⟨tc, tf, tk⟩ => ?_
  rw [a0, a2, am] at tc
  rw [a0, am] at tf
  have K : Keep [.t0, .t2, .t4, .t1, .t2, .t0, .t4] s t := ak.trans tk
  have nk : ∀ r ∈ kept, r ∉ [Reg.t0, .t2, .t4, .t1, .t2, .t0, .t4] := by decide
  refine ⟨⟨by rw [scheduleAt_copy tc, hkk], hfit⟩, by rw [show sb = .s4 from rfl, K.gpr (by decide)]; exact hB',
    fun r hr => K.gpr (nk r hr), tf.sub fun r hr => ?_, K.2.1, K.2.2⟩
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, List.mem_singleton_self _, copy_sub up B⟩

/-- The registers the core writes. -/
def cryptRegs : List Reg := [.a1, .a2, .a3, .a4, .a5, .a6, .a7, .t0, .t1, .t2, .t3, .t4, .t5, .t6]

theorem blkAddr_eq (up : Bool) (B : Addr) : blkAddr (dirCore up) B 0 = B + BitVec.ofNat 64 48 := by
  simp only [blkAddr, slotA, dirCore, bufSlot, Nat.mul_zero, BitVec.add_zero]

theorem crypt_wp (up : Bool) {s : State} {B : Addr} {ws : List Region} {k : Schedule}
    (hB : s.gpr sb = B) (hS : ScrIn s B (dirCore up).total) (hR : Ready s B ws k) :
    WP isa (dirCore up).crypt s fun s' => s'.gpr sb = B ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      Ready s' B ws k ∧ Frame [coreRegion (dirCore up) B] s.mem s'.mem ∧
      (∀ j < (dirCore up).G, Spec.Aes.bytesAt s'.mem (blkAddr (dirCore up) B j) (4 * (dirCore up).bw) =
        dirCipher up k (Spec.Aes.bytesAt s.mem (blkAddr (dirCore up) B j) (4 * (dirCore up).bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hfit : B.toNat + 8 * 528 ≤ 2 ^ 64 := hS.fit
  have hal : B.toNat % 16 = 0 := hS.al
  have hB' : s.gpr .s4 = B := hB
  obtain ⟨hk, _⟩ := hR
  have blkW : InRegions s.wr (B + BitVec.ofNat 64 48) 8 :=
    hS.low _ _ (by cases up <;> decide)
  have blkR : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 48) 8 :=
    let ⟨r, hr, hc⟩ := blkW; ⟨r, List.mem_append_right _ hr, hc⟩
  show WP isa (modeCrypt up) s _
  unfold modeCrypt
  apply WP.seq
  refine WP.mono (WP.keep [.a7, .a1] (Q := fun t => t.gpr .a7 = B + BitVec.ofNat 64 schOff ∧
      t.gpr .a1 = B + BitVec.ofNat 64 48 ∧ t.mem = s.mem) (by
    brun [hB', schOff, bufOff, bufSlot, sb]
    all_goals rfl) (by decide) rfl) fun a ⟨⟨a7, a1, am⟩, ak⟩ => ?_
  apply WP.seq
  refine WP.mono (loadBlock_run a a1 (by rw [ak.2.1, ak.2.2]; exact blkR)) fun u₁ ⟨l₁, h₁, k₁, m₁⟩ => ?_
  have K₁ : Keep [.a7, .a1, .a3, .a4, .t4] s u₁ := ak.trans k₁
  have E : LookEnv u₁ := by
    refine ⟨fun o ho ho' => ?_, fun o ho ho' => ?_, ?_, ?_⟩
    · rw [k₁.gpr (by decide), a7, K₁.2.1, K₁.2.2, Offset.add_add]
      obtain ⟨r, hr, hc⟩ := hS.wr (schOff + o) 4 (by decide) (by cases up <;> simp only [dirCore, schOff, bufOff, bufSlot] <;> omega)
        (by simp only [schOff, bufOff, bufSlot]; omega)
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    · rw [k₁.gpr (by decide), a7, K₁.2.1, K₁.2.2, Offset.add_add]
      obtain ⟨r, hr, hc⟩ := hS.wr (schOff + o) 8 (by decide) (by cases up <;> simp only [dirCore, schOff, bufOff, bufSlot] <;> omega)
        (by simp only [schOff, bufOff, bufSlot]; omega)
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    · rw [k₁.gpr (by decide), a7, BitVec.toNat_add, BitVec.toNat_ofNat]
      simp only [schOff, bufOff, bufSlot]
      omega
    · rw [k₁.gpr (by decide), a7, BitVec.toNat_add, BitVec.toNat_ofNat]
      simp only [schOff, bufOff, bufSlot]
      omega
  apply WP.seq
  refine WP.mono (cipher_run E up) fun u₂ ⟨c₂, k₂, m₂⟩ => ?_
  have K₂ : Keep cryptRegs s u₂ := (K₁.trans k₂).mono (by decide)
  have p₂ : u₂.gpr .a1 = B + BitVec.ofNat 64 48 := by rw [k₂.gpr (by decide), k₁.gpr (by decide), a1]
  refine WP.mono (storeBlock_run u₂ p₂ (by rw [K₂.2.2]; exact blkW)) fun u₃ ⟨m₃, _, _, k₃⟩ => ?_
  have K₃ : Keep cryptRegs s u₃ := (K₂.trans k₃).mono (by decide)
  have nk : ∀ r ∈ kept, r ∉ cryptRegs := by decide
  have F₃ : Frame [⟨B + BitVec.ofNat 64 48, 8⟩] s.mem u₃.mem := by
    rw [m₃, m₂, m₁, am]; exact stored_frame _ _ _ _
  have dB : Region.Disjoint ⟨B + BitVec.ofNat 64 schOff, 4168⟩ ⟨B + BitVec.ofNat 64 48, 8⟩ := by
    have := copy_blk up B
    simpa [blkRegion, slotA, dirCore, bufSlot] using this
  have hK : scheduleAt u₃.mem (B + BitVec.ofNat 64 schOff) = k := by
    rw [scheduleAt_eq_of_frame _ F₃ fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dB, hk]
  refine ⟨by rw [show sb = .s4 from rfl, K₃.gpr (by decide)]; exact hB', fun r hr => K₃.gpr (nk r hr),
    ⟨hK, hfit⟩, F₃.sub fun r hr => ?_, fun j hj => ?_, K₃.2.1, K₃.2.2⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by cases up <;> decide)⟩
  · obtain rfl : j = 0 := by simpa [dirCore] using hj
    have e1 := congrArg Prod.fst c₂
    have e2 := congrArg Prod.snd c₂
    simp only at e1 e2
    rw [blkAddr_eq, show 4 * (dirCore up).bw = 8 from rfl, bytesAt_eq, m₃, stored_block, e1, e2, l₁, h₁, m₁, am,
      k₁.gpr (show Reg.a7 ∉ [Reg.a3, .a4, .t4] by decide), a7, hk, ← blockOut_eq, dirCipher_bytes]
    cases up <;> rfl

/-- Blowfish's core in the direction `up` meets what the modes need. -/
def dirCoreSpec (up : Bool) : CoreSpec (dirCore up) where
  Key := Schedule
  cipher := dirCipher up
  KeyArgs := KeyArgs
  Ready := Ready
  cipher_len k b := dirCipher_len up k b
  layout := layout up
  keyArgs_congr h e r w _ f := keyArgs_congr h e.a0 r w f
  ready_frame h _ _ _ _ f _ hc := ready_frame up h f hc
  prepare_wp := prepare_wp up
  crypt_wp := crypt_wp up

/-! ## Two blocks a step -/

/-- The schedule's copy for two blocks in the frame at `B` is `k`. -/
def Ready2 (s : State) (B : Addr) (_ws : List Region) (k : Schedule) : Prop :=
  scheduleAt s.mem (B + BitVec.ofNat 64 schOff2) = k ∧ B.toNat + 8 * 540 ≤ 2 ^ 64

theorem copy2_sub (up : Bool) (B : Addr) :
    Region.Sub ⟨B + BitVec.ofNat 64 schOff2, 4168⟩ (coreRegion (dirCore2 up) B) :=
  Offset.sub _ (by cases up <;> decide) (by cases up <;> decide)

theorem copy2_blk (up : Bool) (B : Addr) :
    Region.Disjoint ⟨B + BitVec.ofNat 64 schOff2, 4168⟩ (blkRegion (dirCore2 up) B) :=
  Offset.disjoint _ (.inr (by cases up <;> decide)) (by simp only [schOff2, bufOff, bufSlot]; omega)
    (by cases up <;> simp only [dirCore2, bufSlot] <;> omega)

theorem ready2_frame (up : Bool) {s s' : State} {B : Addr} {ws : List Region} {k : Schedule}
    {rs : List Region} (h : Ready2 s B ws k) (hf : Frame rs s.mem s'.mem)
    (hc : ∀ r ∈ rs, Region.Disjoint (coreRegion (dirCore2 up) B) r ∨ Region.Sub r (blkRegion (dirCore2 up) B)) :
    Ready2 s' B ws k := by
  obtain ⟨hk, hfit⟩ := h
  refine ⟨?_, hfit⟩
  rw [scheduleAt_eq_of_frame _ hf fun r hr => ?_, hk]
  rcases hc r hr with h | h
  · exact h.sub_left (copy2_sub up B)
  · exact (copy2_blk up B).sub_right h

theorem layout2 (up : Bool) : Layout (dirCore2 up) :=
  ⟨by cases up <;> decide, .inl rfl, by cases up <;> decide, by cases up <;> decide, by cases up <;> decide,
    by cases up <;> decide, by cases up <;> decide⟩

theorem prepare2_wp (up : Bool) {s : State} {B : Addr} {rs : List Region} {k : Schedule}
    (hB : s.gpr sb = B) (hS : ScrIn s B (dirCore2 up).total) (hm : (⟨B, 8 * (dirCore2 up).total⟩ : Region) ∈ rs)
    (hk : KeyArgs s rs k) :
    WP isa (dirCore2 up).prepare s fun s' => Ready2 s' B rs k ∧ s'.gpr sb = B ∧
      (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ Frame [coreRegion (dirCore2 up) B] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hfit : B.toNat + 8 * 540 ≤ 2 ^ 64 := hS.fit
  have hB' : s.gpr .s4 = B := hB
  obtain ⟨hkk, hin, hd⟩ := hk
  have dK : (keyR s).Disjoint ⟨B, 8 * 540⟩ := hd _ hm
  show WP isa modePrepare2 s _
  unfold modePrepare2
  apply WP.seq
  refine WP.mono (WP.keep [.t0, .t2, .t4] (Q := fun t => t.gpr .t0 = B + BitVec.ofNat 64 schOff2 ∧
      t.gpr .t2 = s.gpr .a0 ∧ t.gpr .t4 = BitVec.ofNat 64 4168 ∧ t.mem = s.mem) (by
    unfold li4168
    brun [hB', shl_4168, schOff2, bufOff, bufSlot, sb]
    all_goals rfl) (by decide) rfl) fun a ⟨⟨a0, a2, a4, am⟩, ak⟩ => ?_
  refine WP.mono (copyLoop_ok (tmp := .t1) (src := .t2) (dst := .t0) (cnt := .t4) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) a (N := 4168) (by decide) (by decide) a4
    (fun i hi => by
      rw [a2, ak.2.1, ak.2.2]
      exact ⟨_, hin, Offset.contains_base _ (by omega) (by omega)⟩)
    (fun i hi => by
      rw [a0, ak.2.2, Offset.add_add]
      exact hS.wr _ _ (by decide) (by cases up <;> simp only [dirCore2, schOff2, bufOff, bufSlot] <;> omega)
        (by simp only [schOff2, bufOff, bufSlot]; omega)) (by
      rw [a0, a2]
      have hs : Region.Sub ⟨B + BitVec.ofNat 64 schOff2, 4168⟩ ⟨B, 8 * 540⟩ :=
        Offset.sub_base _ (by simp only [schOff2, bufOff, bufSlot]; omega)
      have h : Region.Disjoint ⟨B + BitVec.ofNat 64 schOff2, 4168⟩ ⟨s.gpr .a0, 4168⟩ :=
        Region.Disjoint.sub_left (Region.Disjoint.symm dK) hs
      intro x hx hy
      exact h x (by simp only [Region.Contains]; omega) (by simp only [Region.Contains]; omega))) fun t ⟨tc, tf, tk⟩ => ?_
  rw [a0, a2, am] at tc
  rw [a0, am] at tf
  have K : Keep [.t0, .t2, .t4, .t1, .t2, .t0, .t4] s t := ak.trans tk
  have nk : ∀ r ∈ kept, r ∉ [Reg.t0, .t2, .t4, .t1, .t2, .t0, .t4] := by decide
  refine ⟨⟨by rw [scheduleAt_copy tc, hkk], hfit⟩, by rw [show sb = .s4 from rfl, K.gpr (by decide)]; exact hB',
    fun r hr => K.gpr (nk r hr), tf.sub fun r hr => ?_, K.2.1, K.2.2⟩
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, List.mem_singleton_self _, copy2_sub up B⟩

theorem crypt2_save_eq : (([.addi sch sb schOff2, .addi ptr sb bufOff] : List Instr) ++ slotBase ++
    saved2.map (fun (r, d) => Instr.store .d r rowPtr d) ++ park2) =
    (([.addi sch sb schOff2, .addi ptr sb bufOff] : List Instr) ++ slotBase) ++
      (Spill.saveCode .t0 saved2 ++ park2) := by
  simp only [List.append_assoc]; rfl

theorem crypt2_restore_eq :
    (storeBlock2 ++ unpark2 ++ slotBase ++ saved2.map fun (r, d) => Instr.load .d r rowPtr d) =
    storeBlock2 ++ (unpark2 ++ (slotBase ++ Spill.restoreCode .t0 saved2)) := by
  simp only [List.append_assoc]; rfl

theorem saved_ok' : ∀ p ∈ saved2, p.2 % 8 = 0 ∧ p.2 < 2048 := by decide
theorem saved_in' : ∀ p ∈ saved2, 0 ≤ p.2 ∧ p.2 + 8 ≤ 0 + 80 := by decide

/-- What the two-block core writes, but what it restores or parks. -/
def crypt2Regs : List Reg := [.a1, .a2, .a3, .a4, .a5, .a6, .a7, .t0, .t1, .t2, .t3, .t4, .t5, .t6,
  .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .t4, .a1, .a2, .s0, .s11, .ra, .t0]

/-- The kept registers neither saved nor parked: `a0`. -/
theorem kept_out : ∀ r ∈ kept, r ∉ saved2.map Prod.fst → r ∉ [Reg.s1, .s2, .s3, .s4] → r ∉ crypt2Regs := by
  decide

theorem saved_out : ∀ p ∈ saved2, p.1 ∉ [Reg.a7, .a1, .t0] := by decide
theorem blkAddr2_eq (up : Bool) (B : Addr) (j : Nat) :
    blkAddr (dirCore2 up) B j = B + BitVec.ofNat 64 (48 + 8 * j) := by
  simp only [blkAddr, slotA, dirCore2, bufSlot]
  rw [Offset.add_add]

theorem crypt2_wp (up : Bool) {s : State} {B : Addr} {ws : List Region} {k : Schedule}
    (hB : s.gpr sb = B) (hS : ScrIn s B (dirCore2 up).total) (hR : Ready2 s B ws k) :
    WP isa (dirCore2 up).crypt s fun s' => s'.gpr sb = B ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      Ready2 s' B ws k ∧ Frame [coreRegion (dirCore2 up) B] s.mem s'.mem ∧
      (∀ j < (dirCore2 up).G, Spec.Aes.bytesAt s'.mem (blkAddr (dirCore2 up) B j) (4 * (dirCore2 up).bw) =
        dirCipher up k (Spec.Aes.bytesAt s.mem (blkAddr (dirCore2 up) B j) (4 * (dirCore2 up).bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hfit : B.toNat + 8 * 540 ≤ 2 ^ 64 := hS.fit
  have hal : B.toNat % 16 = 0 := hS.al
  have hB' : s.gpr .s4 = B := hB
  obtain ⟨hk, _⟩ := hR
  let q := B + BitVec.ofNat 64 48
  let SA := B + BitVec.ofNat 64 4232
  have e64 : schOff2 = 64 := rfl
  have blkW : InRegions s.wr q 16 := hS.low _ _ (by cases up <;> decide)
  have hSA : SA.toNat % 8 = 0 := Spill.al8 (by omega) (by decide)
  -- The save slots, the copy and the buffer, in the frame.
  have dSC : ∀ r ∈ [(⟨B + BitVec.ofNat 64 schOff2, 4168⟩ : Region)],
      Region.Disjoint ⟨SA + BitVec.ofNat 64 0, 80⟩ r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [BitVec.add_zero, e64]
    exact Offset.disjoint _ (.inr (by decide)) (by omega) (by omega)
  have dSq : (⟨SA + BitVec.ofNat 64 0, 80⟩ : Region).Disjoint ⟨q, 16⟩ := by
    rw [BitVec.add_zero]
    exact Offset.disjoint _ (.inr (by decide)) (by omega) (by omega)
  have e8 : q + 8#64 = B + BitVec.ofNat 64 56 := by
    rw [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, Offset.add_add]
  have dSq₁ : (⟨SA + BitVec.ofNat 64 0, 80⟩ : Region).Disjoint ⟨q, 8⟩ := by
    rw [BitVec.add_zero]
    exact Offset.disjoint _ (.inr (by decide)) (by omega) (by omega)
  have dSq₂ : (⟨SA + BitVec.ofNat 64 0, 80⟩ : Region).Disjoint ⟨q + 8#64, 8⟩ := by
    rw [e8, BitVec.add_zero]
    exact Offset.disjoint _ (.inr (by decide)) (by omega) (by omega)
  have dCq : (⟨B + BitVec.ofNat 64 schOff2, 4168⟩ : Region).Disjoint ⟨q, 16⟩ := by
    rw [e64]; exact Offset.disjoint _ (.inr (by decide)) (by omega) (by omega)
  show WP isa (modeCrypt2 up) s _
  unfold modeCrypt2
  apply WP.seq
  rw [crypt2_save_eq, WP.block_append_iff]
  refine WP.mono (WP.keep [.a7, .a1, .t0] (Q := fun t => t.gpr .a7 = B + BitVec.ofNat 64 schOff2 ∧
      t.gpr .a1 = q ∧ t.gpr .t0 = SA ∧ t.mem = s.mem) (by
    unfold slotBase
    brun [hB', schOff2, bufOff, bufSlot, sb]
    refine ⟨rfl, ?_⟩
    rw [Offset.add_add, Offset.add_add, Offset.add_add]) (by decide) rfl) fun a ⟨⟨a7, a1, a0, am⟩, ak⟩ => ?_
  -- The registers saved.
  refine Spill.save_ok (b := .t0) (by rw [a0]; exact hSA) saved_ok' (fun p hp => ?_) ?_
  · have := saved_in' p hp
    have h8 := (saved_ok' p hp).1
    rw [ak.2.2, a0, Offset.add_add]
    exact hS.wr _ _ (by decide) (by cases up <;> simp only [dirCore2] <;> omega) (by omega)
  rw [a0]
  let Ms := Spill.saveMem a.mem SA a.gpr saved2
  have fs : Frame [⟨SA, 80⟩] s.mem Ms := by
    rw [← am]
    exact Spill.saveMem_frame_base (fun p hp => (saved_in' p hp).2) (by decide) _ _ _
  let b : State := { a with mem := Ms }
  have bg : b.gpr = a.gpr := rfl
  -- The modes' state parked.
  refine WP.mono (WP.keep [.s0, .s11, .ra] (Q := fun t => t.gpr .s0 = s.gpr .s1 ∧ t.gpr .s11 = s.gpr .s2 ∧
      t.gpr .ra = s.gpr .s3 ∧ t.mem = Ms) (by
    have g1 : a.gpr .s1 = s.gpr .s1 := ak.gpr (by decide)
    have g2 : a.gpr .s2 = s.gpr .s2 := ak.gpr (by decide)
    have g3 : a.gpr .s3 = s.gpr .s3 := ak.gpr (by decide)
    unfold park2
    brun [mov, g1, g2, g3]
    all_goals rfl) (by decide) rfl) fun pk ⟨⟨p0, p11, pra, pm⟩, pkk⟩ => ?_
  have pg : ∀ r, r ∉ [Reg.s0, .s11, .ra] → pk.gpr r = a.gpr r := fun r hr => pkk.gpr hr
  have dSq0 : (⟨SA, 80⟩ : Region).Disjoint ⟨q, 16⟩ := by have := dSq; rwa [BitVec.add_zero] at this
  have hbq : ∀ o, o ≤ 8 → blockAt Ms (q + BitVec.ofNat 64 o) = blockAt s.mem (q + BitVec.ofNat 64 o) :=
    fun o ho => blockAt_frame fs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (dSq0.sub_right (r₂' := ⟨q + BitVec.ofNat 64 o, 8⟩) (Offset.sub_base _ (by omega))).symm
  have hbk : scheduleAt Ms (B + BitVec.ofNat 64 schOff2) = k := by
    rw [scheduleAt_eq_of_frame _ fs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      have := dSC _ (List.mem_singleton_self _); rw [BitVec.add_zero] at this; exact this.symm, hk]
  -- The two blocks.
  apply WP.seq
  refine WP.mono (loadBlock2_run pk (q := q) (by rw [pg _ (by decide), a1]) (by
    rw [pkk.2.1, pkk.2.2, ak.2.1, ak.2.2]
    let ⟨r, hr, hc⟩ := blkW; exact ⟨r, List.mem_append_right _ hr, hc⟩)) fun u₁ ⟨l₁, h₁, l₁', h₁', k₁, m₁⟩ => ?_
  have K₁ : Keep [.a7, .a1, .t0, .s0, .s11, .ra, .a3, .a4, .s1, .s2, .t4] s u₁ := (ak.trans pkk).trans k₁
  have u7 : u₁.gpr .a7 = B + BitVec.ofNat 64 schOff2 := by rw [k₁.gpr (by decide), pg _ (by decide), a7]
  have E : LookEnv u₁ := by
    refine ⟨fun o ho ho' => ?_, fun o ho ho' => ?_, ?_, ?_⟩
    · rw [u7, K₁.2.1, K₁.2.2, Offset.add_add]
      obtain ⟨r, hr, hc⟩ := hS.wr (schOff2 + o) 4 (by decide) (by cases up <;> simp only [dirCore2, schOff2, bufOff, bufSlot] <;> omega)
        (by simp only [schOff2, bufOff, bufSlot]; omega)
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    · rw [u7, K₁.2.1, K₁.2.2, Offset.add_add]
      obtain ⟨r, hr, hc⟩ := hS.wr (schOff2 + o) 8 (by decide) (by cases up <;> simp only [dirCore2, schOff2, bufOff, bufSlot] <;> omega)
        (by simp only [schOff2, bufOff, bufSlot]; omega)
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    · rw [u7, BitVec.toNat_add, BitVec.toNat_ofNat]
      simp only [schOff2, bufOff, bufSlot]
      omega
    · rw [u7, BitVec.toNat_add, BitVec.toNat_ofNat]
      simp only [schOff2, bufOff, bufSlot]
      omega
  apply WP.seq
  refine WP.mono (cipher2_run E up) fun u₂ ⟨c₂, c₂', k₂, m₂⟩ => ?_
  have K₂ : Keep crypt2Regs s u₂ := (K₁.trans k₂).mono (by decide)
  have p₂ : u₂.gpr .a1 = q := by rw [k₂.gpr (by decide), k₁.gpr (by decide), pg _ (by decide), a1]
  rw [crypt2_restore_eq, WP.block_append_iff]
  refine WP.mono (storeBlock2_run u₂ p₂ (by rw [K₂.2.2]; exact blkW)) fun u₃ ⟨m₃, _, _, k₃⟩ => ?_
  rw [WP.block_append_iff]
  have u₃7 : u₃.gpr .a7 = B + BitVec.ofNat 64 schOff2 := by
    rw [k₃.gpr (by decide), k₂.gpr (by decide), u7]
  have u₃p : ∀ r ∈ [Reg.s0, .s11, .ra], u₃.gpr r = pk.gpr r := fun r hr => by
    rw [k₃.gpr (by revert hr; revert r; decide), k₂.gpr (by revert hr; revert r; decide),
      k₁.gpr (by revert hr; revert r; decide)]
  -- The modes' state back.
  refine WP.mono (WP.keep [.s1, .s2, .s3, .s4] (Q := fun t => t.gpr .s1 = s.gpr .s1 ∧ t.gpr .s2 = s.gpr .s2 ∧
      t.gpr .s3 = s.gpr .s3 ∧ t.gpr .s4 = B ∧ t.gpr .a7 = B + BitVec.ofNat 64 schOff2 ∧ t.mem = u₃.mem) (by
    have h0 : u₃.gpr .s0 = s.gpr .s1 := by rw [u₃p _ (by decide), p0]
    have h11 : u₃.gpr .s11 = s.gpr .s2 := by rw [u₃p _ (by decide), p11]
    have hra : u₃.gpr .ra = s.gpr .s3 := by rw [u₃p _ (by decide), pra]
    unfold unpark2
    brun [mov, h0, h11, hra, u₃7, schOff2, bufOff, bufSlot, sb]
    exact BitVec.add_sub_cancel _ _) (by decide) rfl) fun v ⟨⟨v1, v2, v3, v4, v7, vm⟩, kv⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.t0] (Q := fun t => t.gpr .t0 = SA ∧ t.mem = v.mem) (by
    unfold slotBase
    brun [v7, schOff2, bufOff, bufSlot]
    rw [Offset.add_add, Offset.add_add, Offset.add_add]) (by decide) rfl) fun u₄ ⟨⟨u₄0, u₄m'⟩, k₄⟩ => ?_
  have u₄m : u₄.mem = u₃.mem := u₄m'.trans vm
  -- The memory after the stores.
  have m₂' : u₂.mem = Ms := by rw [m₂, m₁, pm]
  let M₁ := writeBytes Ms q (beBytes 4 (u₂.gpr .a3) ++ beBytes 4 (u₂.gpr .a4))
  have f₁ := stored_frame Ms q (u₂.gpr .a3) (u₂.gpr .a4)
  have f₂ := stored_frame M₁ (q + 8#64) (u₂.gpr .s1) (u₂.gpr .s2)
  have mem₄ : u₄.mem = writeBytes M₁ (q + 8#64) (beBytes 4 (u₂.gpr .s1) ++ beBytes 4 (u₂.gpr .s2)) := by
    rw [u₄m, m₃, m₂']
  have hsv : Spill.Saved SA a.gpr saved2 u₄.mem := by
    rw [mem₄]
    refine ((Spill.saveMem_saved (by decide) a.mem SA a.gpr).frame_in saved_in' f₁ fun r hr => ?_).frame_in
      saved_in' f₂ fun r hr => ?_
    · simp only [List.mem_singleton] at hr; subst hr; exact dSq₁
    · simp only [List.mem_singleton] at hr; subst hr; exact dSq₂
  refine WP.mono (Spill.restore_wp (B := SA) hSA u₄0 saved_ok' (by decide) (fun p hp => ?_) hsv)
    fun t R => ?_
  · have := saved_in' p hp
    have h8 := (saved_ok' p hp).1
    rw [k₄.2.1, k₄.2.2, kv.2.1, kv.2.2, k₃.2.1, k₃.2.2, K₂.2.1, K₂.2.2, Offset.add_add]
    obtain ⟨r, hr, hc⟩ := hS.wr (4232 + p.2) 8 (by decide) (by cases up <;> simp only [dirCore2] <;> omega) (by omega)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have Kt : Keep crypt2Regs s u₄ := (((K₂.trans k₃).trans kv).trans k₄).mono (by decide)
  have tg : ∀ r ∈ kept, t.gpr r = s.gpr r := fun r hr => by
    by_cases hm : r ∈ saved2.map Prod.fst
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
      rw [R.gpr p hp, ak.gpr (saved_out p hp)]
    · rw [R.other r hm]
      by_cases hq : r ∈ [Reg.s1, .s2, .s3, .s4]
      · rw [k₄.gpr (by revert hq; revert r; decide)]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl
        · exact v1
        · exact v2
        · exact v3
        · exact v4.trans hB'.symm
      · exact Kt.gpr (kept_out r hr hm hq)
  have hK4 : scheduleAt u₄.mem (B + BitVec.ofNat 64 schOff2) = k := by
    rw [mem₄, scheduleAt_eq_of_frame _ f₂ fun r hr => ?_, scheduleAt_eq_of_frame _ f₁ fun r hr => ?_, hbk]
    · simp only [List.mem_singleton] at hr; subst hr
      exact dCq.sub_right (Region.sub_prefix (by decide))
    · simp only [List.mem_singleton] at hr; subst hr
      rw [e8, e64]; exact Offset.disjoint _ (.inr (by decide)) (by omega) (by omega)
  refine ⟨by rw [show sb = .s4 from rfl]; exact (tg .s4 (by decide)).trans hB', tg, ⟨by rw [R.mem]; exact hK4, hfit⟩,
    ?_, fun j hj => ?_, by rw [R.rd]; exact Kt.2.1, by rw [R.wr]; exact Kt.2.2⟩
  · rw [R.mem, mem₄]
    have eC : coreRegion (dirCore2 up) B = ⟨B + BitVec.ofNat 64 48, 4272⟩ := by cases up <;> rfl
    rw [eC]
    refine ((fs.sub fun r hr => ?_).trans (f₁.sub fun r hr => ?_)).trans (f₂.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, by rw [e8]; exact Offset.sub _ (by decide) (by decide)⟩
  · have hj' : j < 2 := hj
    rw [R.mem, show 4 * (dirCore2 up).bw = 8 from rfl]
    have u17 : u₁.gpr .a7 = B + BitVec.ofNat 64 schOff2 := u7
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · have e1 := congrArg Prod.fst c₂
      have e2 := congrArg Prod.snd c₂
      simp only at e1 e2
      have ea : blkAddr (dirCore2 up) B 0 = q := by rw [blkAddr2_eq]
      have h0 := hbq 0 (by decide); rw [BitVec.add_zero] at h0
      rw [ea, bytesAt_eq, mem₄, blockAt_frame f₂ fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          rw [e8]; exact Offset.disjoint _ (.inl (by decide)) (by omega) (by omega),
        stored_block, e1, e2, l₁, h₁, m₁, pm, u17, hbk, ← blockOut_eq, h0, dirCipher_bytes]
      cases up <;> rfl
    · have e1 := congrArg Prod.fst c₂'
      have e2 := congrArg Prod.snd c₂'
      simp only at e1 e2
      have ea : blkAddr (dirCore2 up) B 1 = q + 8#64 := by rw [blkAddr2_eq, e8]
      have h8 := hbq 8 (by decide)
      rw [show q + BitVec.ofNat 64 8 = q + 8#64 from rfl] at h8
      rw [ea, bytesAt_eq, mem₄, stored_block, e1, e2, l₁', h₁', m₁, pm, u17, hbk, ← blockOut_eq, h8,
        dirCipher_bytes]
      cases up <;> rfl

/-- Blowfish's two-block core in the direction `up` meets what the modes need. -/
def dirCoreSpec2 (up : Bool) : CoreSpec (dirCore2 up) where
  Key := Schedule
  cipher := dirCipher up
  KeyArgs := KeyArgs
  Ready := Ready2
  cipher_len k b := dirCipher_len up k b
  layout := layout2 up
  keyArgs_congr h e r w _ f := keyArgs_congr h e.a0 r w f
  ready_frame h _ _ _ _ f _ hc := ready2_frame up h f hc
  prepare_wp := prepare2_wp up
  crypt_wp := crypt2_wp up

end VG.Proof.Blowfish.RISCV64.Mode
