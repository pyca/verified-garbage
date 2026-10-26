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
open VG.Impl.Modes.RISCV64 (sb coreSlot)
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
    ⟨_, hS.low, Offset.contains_base _ (by cases up <;> decide) (by omega)⟩
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

end VG.Proof.Blowfish.RISCV64.Mode
