module

public import VerifiedGarbage.Proof.Modes.RISCV64.SeqFinal
public import VerifiedGarbage.Impl.Blowfish.RISCV64.FbFinal
public import VerifiedGarbage.Spec.Blowfish.CfbFinal
public import VerifiedGarbage.Spec.Blowfish.OfbFinal
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Blowfish.RISCV64.FbFinalLit
meta import VerifiedGarbage.Proof.Modes.RISCV64.SeqFinal
meta import VerifiedGarbage.Impl.Blowfish.RISCV64.FbFinal
meta import VerifiedGarbage.Spec.Blowfish.CfbFinal
meta import VerifiedGarbage.Spec.Blowfish.OfbFinal
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Blowfish.RISCV64.FbFinalLit
public import VerifiedGarbage.Spec.Blowfish.Cbc
public import VerifiedGarbage.Spec.Blowfish.Cfb
public import VerifiedGarbage.Spec.Blowfish.Ofb
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Modes.RISCV64.Modes
import VerifiedGarbage.Proof.Modes.RISCV64.Wide
public import VerifiedGarbage.Proof.Modes.RISCV64.Seq
public import VerifiedGarbage.Proof.Modes.Steps
import VerifiedGarbage.Proof.Blowfish.RISCV64.ModesLit
meta import VerifiedGarbage.Proof.Blowfish.RISCV64.ModesLit
meta import VerifiedGarbage.Spec.Blowfish.Cbc
meta import VerifiedGarbage.Spec.Blowfish.Cfb
meta import VerifiedGarbage.Spec.Blowfish.Ofb
meta import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Impl.Blowfish.RISCV64.Modes
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Impl.Blowfish.RISCV64.Modes
public import VerifiedGarbage.Proof.Modes.RISCV64.Shared
public import VerifiedGarbage.Proof.Blowfish.ModeBytes
import VerifiedGarbage.Proof.Blowfish.RISCV64.Ecb
import VerifiedGarbage.Proof.Blowfish.RISCV64.Cipher
import VerifiedGarbage.Proof.Blowfish.Schedule
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.RISCV64.Loops
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RISCV64.MRun
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
meta import VerifiedGarbage.Proof.Modes.RISCV64.Shared
meta import VerifiedGarbage.Proof.Blowfish.ModeBytes
meta import VerifiedGarbage.Proof.Blowfish.RISCV64.Ecb
meta import VerifiedGarbage.Proof.Blowfish.RISCV64.Cipher
meta import VerifiedGarbage.Proof.Blowfish.Schedule
meta import VerifiedGarbage.Proof.Framework.RISCV64.Keep
meta import VerifiedGarbage.Proof.Framework.RISCV64.Loops
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RISCV64.MRun
meta import VerifiedGarbage.Proof.Framework.RISCV64.Spill
meta import VerifiedGarbage.Proof.Modes.RISCV64.Modes
meta import VerifiedGarbage.Proof.Modes.RISCV64.Wide
meta import VerifiedGarbage.Proof.Modes.RISCV64.Seq
meta import VerifiedGarbage.Proof.Modes.Steps

/-! ### `Blowfish.RISCV64.ModesVerified`, which this module and modules that import it used -/

section

/-! ### `Blowfish.RISCV64.ModeCore`, which only this module used -/

section

/-!
# Blowfish's core for the modes on RISC-V

`inlineCoreSpec up`: Blowfish's core (`Impl.Blowfish.RISCV64.inlineCore up`) meets
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
    Region.Sub ⟨B + BitVec.ofNat 64 schOff, 4168⟩ (coreRegion (inlineCore up) B) :=
  Offset.sub _ (by cases up <;> decide) (by cases up <;> decide)

theorem copy_blk (up : Bool) (B : Addr) :
    Region.Disjoint ⟨B + BitVec.ofNat 64 schOff, 4168⟩ (blkRegion (inlineCore up) B) :=
  Offset.disjoint _ (.inr (by cases up <;> decide)) (by simp only [schOff, bufOff, bufSlot]; omega_using [])
    (by cases up <;> simp only [inlineCore, bufSlot] <;> omega_using [])

theorem ready_frame (up : Bool) {s s' : State} {B : Addr} {ws : List Region} {k : Schedule}
    {rs : List Region} (h : Ready s B ws k) (hf : Frame rs s.mem s'.mem)
    (hc : ∀ r ∈ rs, Region.Disjoint (coreRegion (inlineCore up) B) r ∨ Region.Sub r (blkRegion (inlineCore up) B)) :
    Ready s' B ws k := by
  obtain ⟨hk, hfit⟩ := h
  refine ⟨?_, hfit⟩
  rw [scheduleAt_eq_of_frame _ hf fun r hr => ?_, hk]
  rcases hc r hr with h | h
  · exact h.sub_left (copy_sub up B)
  · exact (copy_blk up B).sub_right h

theorem inlineLayout (up : Bool) : Layout (inlineCore up) :=
  ⟨by cases up <;> decide, .inl rfl, by cases up <;> decide, by cases up <;> decide, by cases up <;> decide,
    by cases up <;> decide, by cases up <;> decide⟩

theorem prepare_wp (up : Bool) {s : State} {B : Addr} {rs : List Region} {k : Schedule}
    (hB : s.gpr sb = B) (hS : ScrIn s B (inlineCore up).total) (hm : (⟨B, 8 * (inlineCore up).total⟩ : Region) ∈ rs)
    (hk : KeyArgs s rs k) :
    WP isa (inlineCore up).prepare s fun s' => Ready s' B rs k ∧ s'.gpr sb = B ∧
      (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ Frame [coreRegion (inlineCore up) B] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hfit : B.toNat + 8 * 528 ≤ 2 ^ 64 := hS.fit
  have hB' : s.gpr .s4 = B := hB
  obtain ⟨hkk, hin, hd⟩ := hk
  obtain dK : (keyR s).Disjoint ⟨B, 8 * 528⟩ := hd _ hm
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
      exact ⟨_, hin, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩)
    (fun i hi => by
      rw [a0, ak.2.2, Offset.add_add]
      exact hS.wr _ _ (by decide) (by cases up <;> simp only [inlineCore, schOff, bufOff, bufSlot] <;> omega_using [hi])
        (by simp only [schOff, bufOff, bufSlot]; omega_using [])) (by
      rw [a0, a2]
      obtain hs : Region.Sub ⟨B + BitVec.ofNat 64 schOff, 4168⟩ ⟨B, 8 * 528⟩ :=
        Offset.sub_base _ (by simp only [schOff, bufOff, bufSlot]; omega_using [])
      obtain h : Region.Disjoint ⟨B + BitVec.ofNat 64 schOff, 4168⟩ ⟨s.gpr .a0, 4168⟩ :=
        Region.Disjoint.sub_left (Region.Disjoint.symm dK) hs
      intro x hx hy
      exact h x (by simp only [Region.Contains]; omega_using [hx]) (by simp only [Region.Contains]; omega_using [hy]))) fun t ⟨tc, tf, tk⟩ => ?_
  rw [a0, a2, am] at tc
  rw [a0, am] at tf
  obtain K : Keep [.t0, .t2, .t4, .t1, .t2, .t0, .t4] s t := ak.trans tk
  obtain nk : ∀ r ∈ kept, r ∉ [Reg.t0, .t2, .t4, .t1, .t2, .t0, .t4] := by decide
  refine ⟨⟨by rw [scheduleAt_copy tc, hkk], hfit⟩, by rw [show sb = .s4 from rfl, K.gpr (by decide)]; exact hB',
    fun r hr => K.gpr (nk r hr), tf.sub fun r hr => ?_, K.2.1, K.2.2⟩
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, List.mem_singleton_self _, copy_sub up B⟩

/-- The registers the core writes. -/
def cryptRegs : List Reg := [.a1, .a2, .a3, .a4, .a5, .a6, .a7, .t0, .t1, .t2, .t3, .t4, .t5, .t6]

theorem blkAddr_eq (up : Bool) (B : Addr) : blkAddr (inlineCore up) B 0 = B + BitVec.ofNat 64 48 := by
  simp only [blkAddr, slotA, inlineCore, bufSlot, Nat.mul_zero, BitVec.add_zero]

theorem crypt_wp (up : Bool) {s : State} {B : Addr} {ws : List Region} {k : Schedule}
    (hB : s.gpr sb = B) (hS : ScrIn s B (inlineCore up).total) (hR : Ready s B ws k) :
    WP isa (inlineCore up).crypt s fun s' => s'.gpr sb = B ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      Ready s' B ws k ∧ Frame [coreRegion (inlineCore up) B] s.mem s'.mem ∧
      (∀ j < (inlineCore up).G, Spec.Aes.bytesAt s'.mem (blkAddr (inlineCore up) B j) (4 * (inlineCore up).bw) =
        dirCipher up k (Spec.Aes.bytesAt s.mem (blkAddr (inlineCore up) B j) (4 * (inlineCore up).bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hfit : B.toNat + 8 * 528 ≤ 2 ^ 64 := hS.fit
  have hal : B.toNat % 16 = 0 := hS.al
  have hB' : s.gpr .s4 = B := hB
  obtain ⟨hk, _⟩ := hR
  obtain blkW : InRegions s.wr (B + BitVec.ofNat 64 48) 8 :=
    hS.low _ _ (by cases up <;> decide)
  obtain blkR : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 48) 8 :=
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
  obtain K₁ : Keep [.a7, .a1, .a3, .a4, .t4] s u₁ := ak.trans k₁
  obtain E : LookEnv u₁ := by
    refine ⟨fun o ho ho' => ?_, fun o ho ho' => ?_, ?_, ?_⟩
    · rw [k₁.gpr (by decide), a7, K₁.2.1, K₁.2.2, Offset.add_add]
      obtain ⟨r, hr, hc⟩ := hS.wr (schOff + o) 4 (by decide) (by cases up <;> simp only [inlineCore, schOff, bufOff, bufSlot] <;> omega_using [ho'])
        (by simp only [schOff, bufOff, bufSlot]; omega_using [ho])
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    · rw [k₁.gpr (by decide), a7, K₁.2.1, K₁.2.2, Offset.add_add]
      obtain ⟨r, hr, hc⟩ := hS.wr (schOff + o) 8 (by decide) (by cases up <;> simp only [inlineCore, schOff, bufOff, bufSlot] <;> omega_using [ho'])
        (by simp only [schOff, bufOff, bufSlot]; omega_using [ho])
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    · rw [k₁.gpr (by decide), a7, BitVec.toNat_add, BitVec.toNat_ofNat]
      simp only [schOff, bufOff, bufSlot]
      omega_using [hal]
    · rw [k₁.gpr (by decide), a7, BitVec.toNat_add, BitVec.toNat_ofNat]
      simp only [schOff, bufOff, bufSlot]
      omega_using [hal]
  apply WP.seq
  refine WP.mono (cipher_run E up) fun u₂ ⟨c₂, k₂, m₂⟩ => ?_
  obtain K₂ : Keep cryptRegs s u₂ := (K₁.trans k₂).mono (by decide)
  obtain p₂ : u₂.gpr .a1 = B + BitVec.ofNat 64 48 := by rw [k₂.gpr (by decide), k₁.gpr (by decide), a1]
  refine WP.mono (storeBlock_run u₂ p₂ (by rw [K₂.2.2]; exact blkW)) fun u₃ ⟨m₃, _, _, k₃⟩ => ?_
  obtain K₃ : Keep cryptRegs s u₃ := (K₂.trans k₃).mono (by decide)
  obtain nk : ∀ r ∈ kept, r ∉ cryptRegs := by decide
  obtain F₃ : Frame [⟨B + BitVec.ofNat 64 48, 8⟩] s.mem u₃.mem := by
    rw [m₃, m₂, m₁, am]; exact stored_frame _ _ _ _
  obtain dB : Region.Disjoint ⟨B + BitVec.ofNat 64 schOff, 4168⟩ ⟨B + BitVec.ofNat 64 48, 8⟩ := by
    have := copy_blk up B
    simpa [blkRegion, slotA, inlineCore, bufSlot] using this
  obtain hK : scheduleAt u₃.mem (B + BitVec.ofNat 64 schOff) = k := by
    rw [scheduleAt_eq_of_frame _ F₃ fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dB, hk]
  refine ⟨by rw [show sb = .s4 from rfl, K₃.gpr (by decide)]; exact hB', fun r hr => K₃.gpr (nk r hr),
    ⟨hK, hfit⟩, F₃.sub fun r hr => ?_, fun j hj => ?_, K₃.2.1, K₃.2.2⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by cases up <;> decide)⟩
  · obtain rfl : j = 0 := by simpa [inlineCore] using hj
    obtain e1 := congrArg Prod.fst c₂
    obtain e2 := congrArg Prod.snd c₂
    simp only at e1 e2
    rw [blkAddr_eq, show 4 * (inlineCore up).bw = 8 from rfl, bytesAt_eq, m₃, stored_block, e1, e2, l₁, h₁, m₁, am,
      k₁.gpr (show Reg.a7 ∉ [Reg.a3, .a4, .t4] by decide), a7, hk, ← blockOut_eq, dirCipher_bytes]
    cases up <;> rfl

/-- Blowfish's core in the direction `up` meets what the modes need. -/
def inlineCoreSpec (up : Bool) : CoreSpec (inlineCore up) where
  Key := Schedule
  cipher := dirCipher up
  KeyArgs := KeyArgs
  Ready := Ready
  cipher_len k b := dirCipher_len up k b
  layout := inlineLayout up
  keyArgs_congr h e r w _ f := keyArgs_congr h e.a0 r w f
  ready_frame h _ _ _ _ f _ hc := ready_frame up h f hc
  prepare_wp := prepare_wp up
  crypt_wp := crypt_wp up

/-! ## Two blocks a step -/

/-- The schedule's copy for two blocks in the frame at `B` is `k`. -/
def Ready2 (s : State) (B : Addr) (_ws : List Region) (k : Schedule) : Prop :=
  scheduleAt s.mem (B + BitVec.ofNat 64 schOff2) = k ∧ B.toNat + 8 * 540 ≤ 2 ^ 64

theorem copy2_sub (up : Bool) (B : Addr) :
    Region.Sub ⟨B + BitVec.ofNat 64 schOff2, 4168⟩ (coreRegion (inlineCore2 up) B) :=
  Offset.sub _ (by cases up <;> decide) (by cases up <;> decide)

theorem copy2_blk (up : Bool) (B : Addr) :
    Region.Disjoint ⟨B + BitVec.ofNat 64 schOff2, 4168⟩ (blkRegion (inlineCore2 up) B) :=
  Offset.disjoint _ (.inr (by cases up <;> decide)) (by simp only [schOff2, bufOff, bufSlot]; omega_using [])
    (by cases up <;> simp only [inlineCore2, bufSlot] <;> omega_using [])

theorem ready2_frame (up : Bool) {s s' : State} {B : Addr} {ws : List Region} {k : Schedule}
    {rs : List Region} (h : Ready2 s B ws k) (hf : Frame rs s.mem s'.mem)
    (hc : ∀ r ∈ rs, Region.Disjoint (coreRegion (inlineCore2 up) B) r ∨ Region.Sub r (blkRegion (inlineCore2 up) B)) :
    Ready2 s' B ws k := by
  obtain ⟨hk, hfit⟩ := h
  refine ⟨?_, hfit⟩
  rw [scheduleAt_eq_of_frame _ hf fun r hr => ?_, hk]
  rcases hc r hr with h | h
  · exact h.sub_left (copy2_sub up B)
  · exact (copy2_blk up B).sub_right h

theorem inlineLayout2 (up : Bool) : Layout (inlineCore2 up) :=
  ⟨by cases up <;> decide, .inl rfl, by cases up <;> decide, by cases up <;> decide, by cases up <;> decide,
    by cases up <;> decide, by cases up <;> decide⟩

theorem prepare2_wp (up : Bool) {s : State} {B : Addr} {rs : List Region} {k : Schedule}
    (hB : s.gpr sb = B) (hS : ScrIn s B (inlineCore2 up).total) (hm : (⟨B, 8 * (inlineCore2 up).total⟩ : Region) ∈ rs)
    (hk : KeyArgs s rs k) :
    WP isa (inlineCore2 up).prepare s fun s' => Ready2 s' B rs k ∧ s'.gpr sb = B ∧
      (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ Frame [coreRegion (inlineCore2 up) B] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hfit : B.toNat + 8 * 540 ≤ 2 ^ 64 := hS.fit
  have hB' : s.gpr .s4 = B := hB
  obtain ⟨hkk, hin, hd⟩ := hk
  obtain dK : (keyR s).Disjoint ⟨B, 8 * 540⟩ := hd _ hm
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
      exact ⟨_, hin, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩)
    (fun i hi => by
      rw [a0, ak.2.2, Offset.add_add]
      exact hS.wr _ _ (by decide) (by cases up <;> simp only [inlineCore2, schOff2, bufOff, bufSlot] <;> omega_using [hi])
        (by simp only [schOff2, bufOff, bufSlot]; omega_using [])) (by
      rw [a0, a2]
      obtain hs : Region.Sub ⟨B + BitVec.ofNat 64 schOff2, 4168⟩ ⟨B, 8 * 540⟩ :=
        Offset.sub_base _ (by simp only [schOff2, bufOff, bufSlot]; omega_using [])
      obtain h : Region.Disjoint ⟨B + BitVec.ofNat 64 schOff2, 4168⟩ ⟨s.gpr .a0, 4168⟩ :=
        Region.Disjoint.sub_left (Region.Disjoint.symm dK) hs
      intro x hx hy
      exact h x (by simp only [Region.Contains]; omega_using [hx]) (by simp only [Region.Contains]; omega_using [hy]))) fun t ⟨tc, tf, tk⟩ => ?_
  rw [a0, a2, am] at tc
  rw [a0, am] at tf
  obtain K : Keep [.t0, .t2, .t4, .t1, .t2, .t0, .t4] s t := ak.trans tk
  obtain nk : ∀ r ∈ kept, r ∉ [Reg.t0, .t2, .t4, .t1, .t2, .t0, .t4] := by decide
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
    blkAddr (inlineCore2 up) B j = B + BitVec.ofNat 64 (48 + 8 * j) := by
  simp only [blkAddr, slotA, inlineCore2, bufSlot]
  rw [Offset.add_add]

theorem crypt2_wp (up : Bool) {s : State} {B : Addr} {ws : List Region} {k : Schedule}
    (hB : s.gpr sb = B) (hS : ScrIn s B (inlineCore2 up).total) (hR : Ready2 s B ws k) :
    WP isa (inlineCore2 up).crypt s fun s' => s'.gpr sb = B ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      Ready2 s' B ws k ∧ Frame [coreRegion (inlineCore2 up) B] s.mem s'.mem ∧
      (∀ j < (inlineCore2 up).G, Spec.Aes.bytesAt s'.mem (blkAddr (inlineCore2 up) B j) (4 * (inlineCore2 up).bw) =
        dirCipher up k (Spec.Aes.bytesAt s.mem (blkAddr (inlineCore2 up) B j) (4 * (inlineCore2 up).bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hfit : B.toNat + 8 * 540 ≤ 2 ^ 64 := hS.fit
  have hal : B.toNat % 16 = 0 := hS.al
  have hB' : s.gpr .s4 = B := hB
  obtain ⟨hk, _⟩ := hR
  let q := B + BitVec.ofNat 64 48
  let SA := B + BitVec.ofNat 64 4232
  have e64 : schOff2 = 64 := rfl
  obtain blkW : InRegions s.wr q 16 := hS.low _ _ (by cases up <;> decide)
  obtain hSA : SA.toNat % 8 = 0 := Spill.al8 (by omega_using [hal]) (by decide)
  -- The save slots, the copy and the buffer, in the frame.
  obtain dSC : ∀ r ∈ [(⟨B + BitVec.ofNat 64 schOff2, 4168⟩ : Region)],
      Region.Disjoint ⟨SA + BitVec.ofNat 64 0, 80⟩ r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [BitVec.add_zero, e64]
    exact Offset.disjoint _ (.inr (by decide)) (by omega_using []) (by omega_using [])
  obtain dSq : (⟨SA + BitVec.ofNat 64 0, 80⟩ : Region).Disjoint ⟨q, 16⟩ := by
    rw [BitVec.add_zero]
    exact Offset.disjoint _ (.inr (by decide)) (by omega_using []) (by omega_using [])
  obtain e8 : q + 8#64 = B + BitVec.ofNat 64 56 := by
    rw [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, Offset.add_add]
  obtain dSq₁ : (⟨SA + BitVec.ofNat 64 0, 80⟩ : Region).Disjoint ⟨q, 8⟩ := by
    rw [BitVec.add_zero]
    exact Offset.disjoint _ (.inr (by decide)) (by omega_using []) (by omega_using [])
  obtain dSq₂ : (⟨SA + BitVec.ofNat 64 0, 80⟩ : Region).Disjoint ⟨q + 8#64, 8⟩ := by
    rw [e8, BitVec.add_zero]
    exact Offset.disjoint _ (.inr (by decide)) (by omega_using []) (by omega_using [])
  obtain dCq : (⟨B + BitVec.ofNat 64 schOff2, 4168⟩ : Region).Disjoint ⟨q, 16⟩ := by
    rw [e64]; exact Offset.disjoint _ (.inr (by decide)) (by omega_using []) (by omega_using [])
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
    obtain h8 := (saved_ok' p hp).1
    rw [ak.2.2, a0, Offset.add_add]
    exact hS.wr _ _ (by decide) (by cases up <;> simp only [inlineCore2] <;> omega_using [this]) (by omega_using [h8])
  rw [a0]
  let Ms := Spill.saveMem a.mem SA a.gpr saved2
  obtain fs : Frame [⟨SA, 80⟩] s.mem Ms := by
    rw [← am]
    exact Spill.saveMem_frame_base (fun p hp => (saved_in' p hp).2) (by decide) _ _ _
  let b : State := { a with mem := Ms }
  have bg : b.gpr = a.gpr := rfl
  -- The modes' state parked.
  refine WP.mono (WP.keep [.s0, .s11, .ra] (Q := fun t => t.gpr .s0 = s.gpr .s1 ∧ t.gpr .s11 = s.gpr .s2 ∧
      t.gpr .ra = s.gpr .s3 ∧ t.mem = Ms) (by
    obtain g1 : a.gpr .s1 = s.gpr .s1 := ak.gpr (by decide)
    obtain g2 : a.gpr .s2 = s.gpr .s2 := ak.gpr (by decide)
    obtain g3 : a.gpr .s3 = s.gpr .s3 := ak.gpr (by decide)
    unfold park2
    brun [mov, g1, g2, g3]
    all_goals rfl) (by decide) rfl) fun pk ⟨⟨p0, p11, pra, pm⟩, pkk⟩ => ?_
  obtain pg : ∀ r, r ∉ [Reg.s0, .s11, .ra] → pk.gpr r = a.gpr r := fun r hr => pkk.gpr hr
  obtain dSq0 : (⟨SA, 80⟩ : Region).Disjoint ⟨q, 16⟩ := by have := dSq; rwa [BitVec.add_zero] at this
  obtain hbq : ∀ o, o ≤ 8 → blockAt Ms (q + BitVec.ofNat 64 o) = blockAt s.mem (q + BitVec.ofNat 64 o) :=
    fun o ho => blockAt_frame fs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (dSq0.sub_right (r₂' := ⟨q + BitVec.ofNat 64 o, 8⟩) (Offset.sub_base _ (by omega_using [ho]))).symm
  obtain hbk : scheduleAt Ms (B + BitVec.ofNat 64 schOff2) = k := by
    rw [scheduleAt_eq_of_frame _ fs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      have := dSC _ (List.mem_singleton_self _); rw [BitVec.add_zero] at this; exact this.symm, hk]
  -- The two blocks.
  apply WP.seq
  refine WP.mono (loadBlock2_run pk (q := q) (by rw [pg _ (by decide), a1]) (by
    rw [pkk.2.1, pkk.2.2, ak.2.1, ak.2.2]
    let ⟨r, hr, hc⟩ := blkW; exact ⟨r, List.mem_append_right _ hr, hc⟩)) fun u₁ ⟨l₁, h₁, l₁', h₁', k₁, m₁⟩ => ?_
  obtain K₁ : Keep [.a7, .a1, .t0, .s0, .s11, .ra, .a3, .a4, .s1, .s2, .t4] s u₁ := (ak.trans pkk).trans k₁
  obtain u7 : u₁.gpr .a7 = B + BitVec.ofNat 64 schOff2 := by rw [k₁.gpr (by decide), pg _ (by decide), a7]
  obtain E : LookEnv u₁ := by
    refine ⟨fun o ho ho' => ?_, fun o ho ho' => ?_, ?_, ?_⟩
    · rw [u7, K₁.2.1, K₁.2.2, Offset.add_add]
      obtain ⟨r, hr, hc⟩ := hS.wr (schOff2 + o) 4 (by decide) (by cases up <;> simp only [inlineCore2, schOff2, bufOff, bufSlot] <;> omega_using [ho'])
        (by simp only [schOff2, bufOff, bufSlot]; omega_using [ho])
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    · rw [u7, K₁.2.1, K₁.2.2, Offset.add_add]
      obtain ⟨r, hr, hc⟩ := hS.wr (schOff2 + o) 8 (by decide) (by cases up <;> simp only [inlineCore2, schOff2, bufOff, bufSlot] <;> omega_using [ho'])
        (by simp only [schOff2, bufOff, bufSlot]; omega_using [ho])
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    · rw [u7, BitVec.toNat_add, BitVec.toNat_ofNat]
      simp only [schOff2, bufOff, bufSlot]
      omega_using [hal]
    · rw [u7, BitVec.toNat_add, BitVec.toNat_ofNat]
      simp only [schOff2, bufOff, bufSlot]
      omega_using [hal]
  apply WP.seq
  refine WP.mono (cipher2_run E up) fun u₂ ⟨c₂, c₂', k₂, m₂⟩ => ?_
  obtain K₂ : Keep crypt2Regs s u₂ := (K₁.trans k₂).mono (by decide)
  obtain p₂ : u₂.gpr .a1 = q := by rw [k₂.gpr (by decide), k₁.gpr (by decide), pg _ (by decide), a1]
  rw [crypt2_restore_eq, WP.block_append_iff]
  refine WP.mono (storeBlock2_run u₂ p₂ (by rw [K₂.2.2]; exact blkW)) fun u₃ ⟨m₃, _, _, k₃⟩ => ?_
  rw [WP.block_append_iff]
  obtain u₃7 : u₃.gpr .a7 = B + BitVec.ofNat 64 schOff2 := by
    rw [k₃.gpr (by decide), k₂.gpr (by decide), u7]
  obtain u₃p : ∀ r ∈ [Reg.s0, .s11, .ra], u₃.gpr r = pk.gpr r := fun r hr => by
    rw [k₃.gpr (by revert hr; revert r; decide), k₂.gpr (by revert hr; revert r; decide),
      k₁.gpr (by revert hr; revert r; decide)]
  -- The modes' state back.
  refine WP.mono (WP.keep [.s1, .s2, .s3, .s4] (Q := fun t => t.gpr .s1 = s.gpr .s1 ∧ t.gpr .s2 = s.gpr .s2 ∧
      t.gpr .s3 = s.gpr .s3 ∧ t.gpr .s4 = B ∧ t.gpr .a7 = B + BitVec.ofNat 64 schOff2 ∧ t.mem = u₃.mem) (by
    obtain h0 : u₃.gpr .s0 = s.gpr .s1 := by rw [u₃p _ (by decide), p0]
    obtain h11 : u₃.gpr .s11 = s.gpr .s2 := by rw [u₃p _ (by decide), p11]
    obtain hra : u₃.gpr .ra = s.gpr .s3 := by rw [u₃p _ (by decide), pra]
    unfold unpark2
    brun [mov, h0, h11, hra, u₃7, schOff2, bufOff, bufSlot, sb]
    exact BitVec.add_sub_cancel _ _) (by decide) rfl) fun v ⟨⟨v1, v2, v3, v4, v7, vm⟩, kv⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.t0] (Q := fun t => t.gpr .t0 = SA ∧ t.mem = v.mem) (by
    unfold slotBase
    brun [v7, schOff2, bufOff, bufSlot]
    rw [Offset.add_add, Offset.add_add, Offset.add_add]) (by decide) rfl) fun u₄ ⟨⟨u₄0, u₄m'⟩, k₄⟩ => ?_
  obtain u₄m : u₄.mem = u₃.mem := u₄m'.trans vm
  -- The memory after the stores.
  obtain m₂' : u₂.mem = Ms := by rw [m₂, m₁, pm]
  let M₁ := writeBytes Ms q (beBytes 4 (u₂.gpr .a3) ++ beBytes 4 (u₂.gpr .a4))
  obtain f₁ := stored_frame Ms q (u₂.gpr .a3) (u₂.gpr .a4)
  obtain f₂ := stored_frame M₁ (q + 8#64) (u₂.gpr .s1) (u₂.gpr .s2)
  obtain mem₄ : u₄.mem = writeBytes M₁ (q + 8#64) (beBytes 4 (u₂.gpr .s1) ++ beBytes 4 (u₂.gpr .s2)) := by
    rw [u₄m, m₃, m₂']
  obtain hsv : Spill.Saved SA a.gpr saved2 u₄.mem := by
    rw [mem₄]
    refine ((Spill.saveMem_saved (by decide) a.mem SA a.gpr).frame_in saved_in' f₁ fun r hr => ?_).frame_in
      saved_in' f₂ fun r hr => ?_
    · simp only [List.mem_singleton] at hr; subst hr; exact dSq₁
    · simp only [List.mem_singleton] at hr; subst hr; exact dSq₂
  refine WP.mono (Spill.restore_wp (B := SA) hSA u₄0 saved_ok' (by decide) (fun p hp => ?_) hsv)
    fun t R => ?_
  · have := saved_in' p hp
    obtain h8 := (saved_ok' p hp).1
    rw [k₄.2.1, k₄.2.2, kv.2.1, kv.2.2, k₃.2.1, k₃.2.2, K₂.2.1, K₂.2.2, Offset.add_add]
    obtain ⟨r, hr, hc⟩ := hS.wr (4232 + p.2) 8 (by decide) (by cases up <;> simp only [inlineCore2] <;> omega_using [this]) (by omega_using [h8])
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  obtain Kt : Keep crypt2Regs s u₄ := (((K₂.trans k₃).trans kv).trans k₄).mono (by decide)
  obtain tg : ∀ r ∈ kept, t.gpr r = s.gpr r := fun r hr => by
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
  obtain hK4 : scheduleAt u₄.mem (B + BitVec.ofNat 64 schOff2) = k := by
    rw [mem₄, scheduleAt_eq_of_frame _ f₂ fun r hr => ?_, scheduleAt_eq_of_frame _ f₁ fun r hr => ?_, hbk]
    · simp only [List.mem_singleton] at hr; subst hr
      exact dCq.sub_right (Region.sub_prefix (by decide))
    · simp only [List.mem_singleton] at hr; subst hr
      rw [e8, e64]; exact Offset.disjoint _ (.inr (by decide)) (by omega_using []) (by omega_using [])
  refine ⟨by rw [show sb = .s4 from rfl]; exact (tg .s4 (by decide)).trans hB', tg, ⟨by rw [R.mem]; exact hK4, hfit⟩,
    ?_, fun j hj => ?_, by rw [R.rd]; exact Kt.2.1, by rw [R.wr]; exact Kt.2.2⟩
  · rw [R.mem, mem₄]
    obtain eC : coreRegion (inlineCore2 up) B = ⟨B + BitVec.ofNat 64 48, 4272⟩ := by cases up <;> rfl
    rw [eC]
    refine ((fs.sub fun r hr => ?_).trans (f₁.sub fun r hr => ?_)).trans (f₂.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, by rw [e8]; exact Offset.sub _ (by decide) (by decide)⟩
  · have hj' : j < 2 := hj
    rw [R.mem, show 4 * (inlineCore2 up).bw = 8 from rfl]
    have u17 : u₁.gpr .a7 = B + BitVec.ofNat 64 schOff2 := u7
    rcases (by omega_using [hj'] : j = 0 ∨ j = 1) with rfl | rfl
    · have e1 := congrArg Prod.fst c₂
      obtain e2 := congrArg Prod.snd c₂
      simp only at e1 e2
      obtain ea : blkAddr (inlineCore2 up) B 0 = q := by rw [blkAddr2_eq]
      obtain h0 := hbq 0 (by decide); rw [BitVec.add_zero] at h0
      rw [ea, bytesAt_eq, mem₄, blockAt_frame f₂ fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          rw [e8]; exact Offset.disjoint _ (.inl (by decide)) (by omega_using []) (by omega_using []),
        stored_block, e1, e2, l₁, h₁, m₁, pm, u17, hbk, ← blockOut_eq, h0, dirCipher_bytes]
      cases up <;> rfl
    · have e1 := congrArg Prod.fst c₂'
      obtain e2 := congrArg Prod.snd c₂'
      simp only at e1 e2
      obtain ea : blkAddr (inlineCore2 up) B 1 = q + 8#64 := by rw [blkAddr2_eq, e8]
      obtain h8 := hbq 8 (by decide)
      rw [show q + BitVec.ofNat 64 8 = q + 8#64 from rfl] at h8
      rw [ea, bytesAt_eq, mem₄, stored_block, e1, e2, l₁', h₁', m₁, pm, u17, hbk, ← blockOut_eq, h8,
        dirCipher_bytes]
      cases up <;> rfl

/-- Blowfish's two-block core in the direction `up` meets what the modes need. -/
def inlineCoreSpec2 (up : Bool) : CoreSpec (inlineCore2 up) where
  Key := Schedule
  cipher := dirCipher up
  KeyArgs := KeyArgs
  Ready := Ready2
  cipher_len k b := dirCipher_len up k b
  layout := inlineLayout2 up
  keyArgs_congr h e r w _ f := keyArgs_congr h e.a0 r w f
  ready_frame h _ _ _ _ f _ hc := ready2_frame up h f hc
  prepare_wp := prepare2_wp up
  crypt_wp := crypt2_wp up

open VG.Proof.Modes.RISCV64 (KeyMove ReadyMove)

theorem shared_key (up : Bool) : KeyMove (inlineCoreSpec up) := by
  intro s t rs ts k hk ha rd wr hf hs
  obtain ⟨hk, hin, hd⟩ := keyArgs_congr hk ha rd wr hf
  exact ⟨hk, hin, fun r hr => by
    obtain ⟨r', hr', sub⟩ := hs r hr
    exact (hd r' hr').sub_right sub⟩

theorem shared_ready (up : Bool) : ReadyMove (inlineCoreSpec up) := by
  intro s t B ws k rs hr ha rd wr hf hs hd
  exact ready_frame (ws := ws) up hr hf hd

def dirCoreSpec (up : Bool) : CoreSpec (dirCore up) :=
  (inlineCoreSpec up).shared (by dsimp only [inlineCore, inlineCore2]; decide) (by dsimp only [inlineCore, inlineCore2]; decide) (shared_key up) (shared_ready up) (by cases up <;> rfl) (by cases up <;> rfl) _ _

theorem shared_key2 (up : Bool) : KeyMove (inlineCoreSpec2 up) := by
  intro s t rs ts k hk ha rd wr hf hs
  obtain ⟨hk, hin, hd⟩ := keyArgs_congr hk ha rd wr hf
  exact ⟨hk, hin, fun r hr => by
    obtain ⟨r', hr', sub⟩ := hs r hr
    exact (hd r' hr').sub_right sub⟩

theorem shared_ready2 (up : Bool) : ReadyMove (inlineCoreSpec2 up) := by
  intro s t B ws k rs hr ha rd wr hf hs hd
  exact ready2_frame (ws := ws) up hr hf hd

def dirCoreSpec2 (up : Bool) : CoreSpec (dirCore2 up) :=
  (inlineCoreSpec2 up).shared (by dsimp only [inlineCore, inlineCore2]; decide) (by dsimp only [inlineCore, inlineCore2]; decide) (shared_key2 up) (shared_ready2 up) (by cases up <;> rfl) (by cases up <;> rfl) _ _

theorem layout (up : Bool) : Layout (dirCore up) :=
  VG.Proof.Modes.RISCV64.shared_layout (inlineLayout up) (by dsimp only [inlineCore, inlineCore2]; decide) _ _

theorem layout2 (up : Bool) : Layout (dirCore2 up) :=
  VG.Proof.Modes.RISCV64.shared_layout (inlineLayout2 up) (by dsimp only [inlineCore, inlineCore2]; decide) _ _

end VG.Proof.Blowfish.RISCV64.Mode

end

end

/-! ### `Blowfish.RISCV64.ModesConstantTime`, which only this module used -/

section

/-!
# Constant-time Blowfish modes on RISC-V

Only the pointers and the count (`a0`–`a3`) and the stack pointer are
public. The modes keep their state in `s1`–`s4`, which the one-block
function never writes and the two-block core parks in registers and
recomputes (`park2`, `unpark2`), never in memory, and zero the frame through
`t3`, a copy of its base made before the caller's `s1`–`s4` come back from
memory.
-/

@[expose] public section

namespace VG.Proof.Blowfish.RISCV64

open VG VG.RISCV64 VG.Impl.Blowfish.RISCV64

/-- The modes' public arguments: the stack pointer and `a0`–`a3`. -/
def modePub (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ ∀ r ∈ [Reg.a0, .a1, .a2, .a3], s₁.gpr r = s₂.gpr r

theorem modes_ofRegs (s₁ s₂ : State) (h : modePub s₁ s₂) :
    taint.Agree (Taint.ofRegs [.a0, .a1, .a2, .a3]) s₁ s₂ :=
  ⟨h.1, fun r hr => h.2 r (Taint.mem_ofRegs.mp hr)⟩

theorem cbcEncryptChained_constantTime (pre : State → Prop) :
    ConstantTime isa pre modePub cbcEncryptChained :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

theorem cbcDecryptChained_constantTime (pre : State → Prop) :
    ConstantTime isa pre modePub cbcDecryptChained :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

theorem ofb_constantTime (pre : State → Prop) : ConstantTime isa pre modePub ofb :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

theorem cfbEncrypt_constantTime (pre : State → Prop) : ConstantTime isa pre modePub cfbEncrypt :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

theorem cfbDecrypt_constantTime (pre : State → Prop) : ConstantTime isa pre modePub cfbDecrypt :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

end VG.Proof.Blowfish.RISCV64

end

end

/-!
# Blowfish's modes on RISC-V meet their contracts

`cbcEncryptChained_verified`, `ofb_verified`, … : the modes of
`Proof/Modes/RISCV64/` over Blowfish's core (`Mode.dirCoreSpec`) meet the
shared contracts, with `stack := 4240`: the mode's frame of 530 slots below
the stack pointer, which it zeroes before returning (`seq_changes_wp`); CBC
and CFB decryption, two blocks a step over `Mode.dirCoreSpec2`, with
`stack := 4336` (542 slots).
The proofs are written against `modeContract`, which states the frame.
-/

@[expose] public section

namespace VG.Proof.Blowfish.RISCV64.Modes

open VG VG.RISCV64 VG.Impl.Blowfish.RISCV64 VG.Impl.Modes
open VG.Proof.Modes.RISCV64 (SeqPre ivR scrRegion Fb)
open VG.Proof.Blowfish.RISCV64.Mode (dirCoreSpec dirCoreSpec2 KeyArgs layout layout2)
open VG.Proof.Blowfish.RISCV64 (modePub)

/-- The frame's bytes: 530 slots, and 542 for the modes over the two-block
core (`dirCore2`). -/
abbrev frameBytes : Nat := 4240
abbrev frameBytes2 : Nat := 4336

/-- Blowfish under the schedule at `a0`, and its inverse. -/
abbrev ciph (s : State) : Spec.Cbc.Cipher := Spec.Blowfish.cipher (Spec.Blowfish.scheduleAt s.mem (s.gpr .a0))
abbrev invCiph (s : State) : Spec.Cbc.Cipher :=
  Spec.Blowfish.invCipher (Spec.Blowfish.scheduleAt s.mem (s.gpr .a0))
/-- The chaining value. -/
abbrev ivAt (m : Mem) (s : State) : List Byte := Spec.Aes.bytesAt m (s.gpr .a1) 8
/-- The data, in blocks. -/
abbrev dataAt (m : Mem) (s : State) : List (List Byte) := Spec.Blowfish.cbcBlocksAt m (s.gpr .a2) (s.gpr .a3).toNat

/-- The functions' postconditions. -/
def cbcEncPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cbc.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (Spec.Cbc.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s))
def cbcDecPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cbc.decrypt (invCiph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (dataAt s.mem s)
def ofbPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Ofb.crypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Ofb.next (ciph s) (ivAt s.mem s) (s.gpr .a3).toNat
def cfbEncPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cfb.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (Spec.Cfb.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s))
def cfbDecPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cfb.decrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (dataAt s.mem s)

/-- A mode's function on RISC-V, with its frame of `frameBytes` below the
stack pointer, and the postcondition `post`. -/
def modeContract (frameBytes : Nat) (post : State → State → Prop) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .a0, 4168⟩
    let iv : Region := ⟨s.gpr .a1, 8⟩
    let data : Region := ⟨s.gpr .a2, 8 * (s.gpr .a3).toNat⟩
    let stack : Region := ⟨s.sp - frameBytes, frameBytes⟩
    s.rd = [key] ∧ s.wr = [iv, data] ∧
      key.Disjoint iv ∧ key.Disjoint data ∧ iv.Disjoint data ∧
      (s.gpr .a1).toNat + 8 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 8 * (s.gpr .a3).toNat ≤ 2 ^ 64 ∧
      s.sp.toNat % 16 = 0 ∧ frameBytes ≤ s.sp.toNat ∧ stack.Disjoint key ∧ stack.Disjoint iv ∧
      stack.Disjoint data
  post := post
  pub := modePub

/-- `modeContract`'s precondition gives the modes'. -/
theorem seqPre_of {post : State → State → Prop} {M : Mode} (up : Bool) (hstep : M.step = 8) {s : State}
    (h : (modeContract frameBytes post).pre s) : SeqPre (dirCore up) M s := by
  obtain ⟨-, hwr, -, -, dVD, fV, fD, al, sp, -, dSV, dSD⟩ := h
  have e8 : 4 * (dirCore up).bw = 8 := rfl
  have eS : scrRegion (dirCore up) (Fb s (dirCore up)) = ⟨s.sp - frameBytes, frameBytes⟩ := rfl
  have eV : ivR s (dirCore up) = ⟨s.gpr .a1, 8⟩ := rfl
  refine ⟨al, sp, by rw [eV, hwr]; simp, fun _ => by rw [eV, hwr]; simp, by rw [e8]; exact fV,
    by rw [hwr, hstep]; simp, by rw [hstep]; exact fD, by rw [hstep, eS]; exact dSD.symm,
    by rw [eV, eS]; exact dSV.symm, fun _ => by rw [eV, hstep]; exact dVD, ⟨by omega_using [hstep], by rw [e8]; omega_using [hstep]⟩,
    layout up⟩

theorem keyArgs_of {post : State → State → Prop} {M : Mode} (up : Bool) (hstep : M.step = 8) {s : State}
    (h : (modeContract frameBytes post).pre s) :
    KeyArgs s (Proof.Modes.RISCV64.wrs0 (dirCore up) M s) (Spec.Blowfish.scheduleAt s.mem (s.gpr .a0)) := by
  obtain ⟨hrd, -, -, dKD, -, -, -, -, -, dSK, -, -⟩ := h
  refine ⟨rfl, by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _), fun r hr => ?_⟩
  simp only [Proof.Modes.RISCV64.wrs0, Proof.Modes.RISCV64.wrs, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl
  · show (Region.mk (s.gpr .a0) 4168).Disjoint ⟨s.gpr .a2, M.step * (s.gpr .a3).toNat⟩
    rw [hstep]; exact dKD
  · exact dSK.symm

/-- `seqPre_of` for the two-block core. -/
theorem seqPre2_of {post : State → State → Prop} {M : Mode} (up : Bool) (hstep : M.step = 8) {s : State}
    (h : (modeContract frameBytes2 post).pre s) : SeqPre (dirCore2 up) M s := by
  obtain ⟨-, hwr, -, -, dVD, fV, fD, al, sp, -, dSV, dSD⟩ := h
  have e8 : 4 * (dirCore2 up).bw = 8 := rfl
  have eS : scrRegion (dirCore2 up) (Fb s (dirCore2 up)) = ⟨s.sp - frameBytes2, frameBytes2⟩ := rfl
  have eV : ivR s (dirCore2 up) = ⟨s.gpr .a1, 8⟩ := rfl
  refine ⟨al, sp, by rw [eV, hwr]; simp, fun _ => by rw [eV, hwr]; simp, by rw [e8]; exact fV,
    by rw [hwr, hstep]; simp, by rw [hstep]; exact fD, by rw [hstep, eS]; exact dSD.symm,
    by rw [eV, eS]; exact dSV.symm, fun _ => by rw [eV, hstep]; exact dVD, ⟨by omega_using [hstep], by rw [e8]; omega_using [hstep]⟩,
    layout2 up⟩

theorem keyArgs2_of {post : State → State → Prop} {M : Mode} (up : Bool) (hstep : M.step = 8) {s : State}
    (h : (modeContract frameBytes2 post).pre s) :
    KeyArgs s (Proof.Modes.RISCV64.wrs0 (dirCore2 up) M s) (Spec.Blowfish.scheduleAt s.mem (s.gpr .a0)) := by
  obtain ⟨hrd, -, -, dKD, -, -, -, -, -, dSK, -, -⟩ := h
  refine ⟨rfl, by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _), fun r hr => ?_⟩
  simp only [Proof.Modes.RISCV64.wrs0, Proof.Modes.RISCV64.wrs, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl
  · show (Region.mk (s.gpr .a0) 4168).Disjoint ⟨s.gpr .a2, M.step * (s.gpr .a3).toNat⟩
    rw [hstep]; exact dKD
  · exact dSK.symm

/-- The data in blocks, as the modes' steps. -/
theorem cbcBlocksAt_eq (m : Mem) (p : Addr) (n : Nat) :
    Spec.Blowfish.cbcBlocksAt m p n = Proof.Modes.chunksAt 8 m p n :=
  Proof.Blowfish.cbcBlocksAt_eq m p n

/-! ## Correctness -/

theorem cbcEncryptChained_correct (s : State) (hs : (modeContract frameBytes cbcEncPost).pre s) :
    ∃ t s', Exec isa cbcEncryptChained s t s' ∧ abiPreserved s s' ∧ (modeContract frameBytes cbcEncPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.cbcEncChained_wp (dirCoreSpec true)
    (seqPre_of true (M := Mode.cbcEncChained 2) rfl hs) (keyArgs_of true (M := Mode.cbcEncChained 2) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => ⟨h1, by rw [dataAt, dataAt, cbcBlocksAt_eq, cbcBlocksAt_eq]; exact h2,
      by rw [dataAt, cbcBlocksAt_eq]; exact h3⟩

theorem cbcDecryptChained_correct (s : State) (hs : (modeContract frameBytes2 cbcDecPost).pre s) :
    ∃ t s', Exec isa cbcDecryptChained s t s' ∧ abiPreserved s s' ∧ (modeContract frameBytes2 cbcDecPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.cbcDecWide_wp (lg := 1) (dirCoreSpec2 false) (by decide) (by decide)
    (by decide) (seqPre2_of false (M := Mode.cbcDecChained 2) rfl hs)
    (keyArgs2_of false (M := Mode.cbcDecChained 2) rfl hs))
    fun _ ⟨h1, h2, h3, _⟩ => ⟨h1, by rw [dataAt, dataAt, cbcBlocksAt_eq, cbcBlocksAt_eq]; exact h2,
      by rw [dataAt, cbcBlocksAt_eq]; exact h3⟩

theorem ofb_correct (s : State) (hs : (modeContract frameBytes ofbPost).pre s) :
    ∃ t s', Exec isa ofb s t s' ∧ abiPreserved s s' ∧ (modeContract frameBytes ofbPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.ofb_wp (dirCoreSpec true)
    (seqPre_of true (M := Mode.ofb 2) rfl hs) (keyArgs_of true (M := Mode.ofb 2) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => ⟨h1, by rw [dataAt, dataAt, cbcBlocksAt_eq, cbcBlocksAt_eq]; exact h2, h3⟩

theorem cfbEncrypt_correct (s : State) (hs : (modeContract frameBytes cfbEncPost).pre s) :
    ∃ t s', Exec isa cfbEncrypt s t s' ∧ abiPreserved s s' ∧ (modeContract frameBytes cfbEncPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.cfbEnc_wp (dirCoreSpec true)
    (seqPre_of true (M := Mode.cfbEnc 2) rfl hs) (keyArgs_of true (M := Mode.cfbEnc 2) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => ⟨h1, by rw [dataAt, dataAt, cbcBlocksAt_eq, cbcBlocksAt_eq]; exact h2,
      by rw [dataAt, cbcBlocksAt_eq]; exact h3⟩

theorem cfbDecrypt_correct (s : State) (hs : (modeContract frameBytes2 cfbDecPost).pre s) :
    ∃ t s', Exec isa cfbDecrypt s t s' ∧ abiPreserved s s' ∧ (modeContract frameBytes2 cfbDecPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.cfbDecWide_wp (lg := 1) (dirCoreSpec2 true) (by decide) (by decide)
    (by decide) (seqPre2_of true (M := Mode.cfbDecEarly 2) rfl hs)
    (keyArgs2_of true (M := Mode.cfbDecEarly 2) rfl hs))
    fun _ ⟨h1, h2, h3, _⟩ => ⟨h1, by rw [dataAt, dataAt, cbcBlocksAt_eq, cbcBlocksAt_eq]; exact h2,
      by rw [dataAt, cbcBlocksAt_eq]; exact h3⟩

/-! ## The contracts -/

/-- A state satisfying the modes' precondition: the schedule at `0x1000`,
the IV at `0x3000`, no data at `0x4000`, and the stack below `0x8000`. -/
def modeSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x3000 | .a2 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 4168⟩]
  wr := [⟨0x3000, 8⟩, ⟨0x4000, 0⟩]

theorem modePub_iff (s₁ s₂ : State) : modePub s₁ s₂ ↔
    s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 := by
  simp [modePub]

theorem cbcEncryptChained_verified :
    Verified RISCV64.target cbcEncryptChained (Spec.Blowfish.cbcEncryptChainedContract RISCV64.abi frameBytes) := by
  refine Verified.of_correct cbcEncryptChained_correct (cbcEncryptChained_constantTime _) ?_
  contract_implies [Spec.Blowfish.cbcEncryptChainedContract, Spec.Blowfish.cbcChainedSig, RISCV64.abi,
    RISCV64.argRegs, modeContract, cbcEncPost, modePub_iff] [modeSat] using modeSat

theorem cbcDecryptChained_verified :
    Verified RISCV64.target cbcDecryptChained (Spec.Blowfish.cbcDecryptChainedContract RISCV64.abi frameBytes2) := by
  refine Verified.of_correct cbcDecryptChained_correct (cbcDecryptChained_constantTime _) ?_
  contract_implies [Spec.Blowfish.cbcDecryptChainedContract, Spec.Blowfish.cbcChainedSig, RISCV64.abi,
    RISCV64.argRegs, modeContract, cbcDecPost, modePub_iff] [modeSat] using modeSat

theorem ofb_verified : Verified RISCV64.target ofb (Spec.Blowfish.ofbContract RISCV64.abi frameBytes) := by
  refine Verified.of_correct ofb_correct (ofb_constantTime _) ?_
  contract_implies [Spec.Blowfish.ofbContract, Spec.Blowfish.ofbSig, RISCV64.abi, RISCV64.argRegs,
    modeContract, ofbPost, modePub_iff] [modeSat] using modeSat

theorem cfbEncrypt_verified :
    Verified RISCV64.target cfbEncrypt (Spec.Blowfish.cfbEncryptContract RISCV64.abi frameBytes) := by
  refine Verified.of_correct cfbEncrypt_correct (cfbEncrypt_constantTime _) ?_
  contract_implies [Spec.Blowfish.cfbEncryptContract, Spec.Blowfish.cfbSig, RISCV64.abi, RISCV64.argRegs,
    modeContract, cfbEncPost, modePub_iff] [modeSat] using modeSat

theorem cfbDecrypt_verified :
    Verified RISCV64.target cfbDecrypt (Spec.Blowfish.cfbDecryptContract RISCV64.abi frameBytes2) := by
  refine Verified.of_correct cfbDecrypt_correct (cfbDecrypt_constantTime _) ?_
  contract_implies [Spec.Blowfish.cfbDecryptContract, Spec.Blowfish.cfbSig, RISCV64.abi, RISCV64.argRegs,
    modeContract, cfbDecPost, modePub_iff] [modeSat] using modeSat

end VG.Proof.Blowfish.RISCV64.Modes

end

end

/-!
# Blowfish-CFB64 and Blowfish-OFB of a message's last piece on RISC-V meet their contracts

The modes' CFB and OFB over a message's last piece (`Proof.Modes.RISCV64.cfbEncFinal_wp`,
`cfbDecFinal_wp`, `ofbFinal_wp`) over Blowfish's one-block encryption core meet the contracts,
with `stack := 4240`, that core's frame (`ModesVerified.lean`), whose
precondition, with the data `len` bytes, is `seq`'s for the data a byte at a
time (`byteMode`). Constant time as the whole-block functions.
-/

@[expose] public section

namespace VG.Proof.Blowfish.RISCV64.Modes

open VG VG.RISCV64 VG.Impl.Blowfish.RISCV64 VG.Impl.Modes
open VG.Proof.Modes.RISCV64 (SeqPre ivR scrRegion Fb byteMode)
open VG.Proof.Blowfish.RISCV64.Mode (dirCoreSpec KeyArgs layout)
open VG.Proof.Blowfish.RISCV64 (modePub modes_ofRegs)

/-- The final functions' postconditions. -/
def encFinalPost (s s' : State) : Prop :=
  Spec.Cfb.EncryptFinal (ciph s) 8 s.mem s'.mem (s.gpr .a1) (s.gpr .a2) (s.gpr .a3).toNat
def decFinalPost (s s' : State) : Prop :=
  Spec.Cfb.DecryptFinal (ciph s) 8 s.mem s'.mem (s.gpr .a1) (s.gpr .a2) (s.gpr .a3).toNat
def ofbFinalPost (s s' : State) : Prop :=
  Spec.Ofb.CryptFinal (ciph s) 8 s.mem s'.mem (s.gpr .a1) (s.gpr .a2) (s.gpr .a3).toNat

/-- A final function on RISC-V, with its frame below the stack pointer, the
data `len` bytes, and the postcondition `post`. -/
def finalContract (post : State → State → Prop) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .a0, 4168⟩
    let iv : Region := ⟨s.gpr .a1, 8⟩
    let data : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
    let stack : Region := ⟨s.sp - frameBytes, frameBytes⟩
    s.rd = [key] ∧ s.wr = [iv, data] ∧
      key.Disjoint iv ∧ key.Disjoint data ∧ iv.Disjoint data ∧
      (s.gpr .a1).toNat + 8 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64 ∧
      s.sp.toNat % 16 = 0 ∧ frameBytes ≤ s.sp.toNat ∧ stack.Disjoint key ∧ stack.Disjoint iv ∧
      stack.Disjoint data
  post := post
  pub := modePub

theorem seqPreF_of {post : State → State → Prop} {s : State} (h : (finalContract post).pre s) :
    SeqPre (dirCore true) byteMode s := by
  obtain ⟨-, hwr, -, -, dVD, fV, fD, al, sp, -, dSV, dSD⟩ := h
  have eb : 4 * (dirCore true).bw = 8 := rfl
  have eS := (show scrRegion (dirCore true) (Fb s (dirCore true)) = ⟨s.sp - frameBytes, frameBytes⟩ from rfl)
  have eV : ivR s (dirCore true) = ⟨s.gpr .a1, 8⟩ := rfl
  have eD : Proof.Modes.RISCV64.dataRegion (s.gpr .a2) byteMode.step (s.gpr .a3).toNat =
      ⟨s.gpr .a2, (s.gpr .a3).toNat⟩ := by
    simp only [Proof.Modes.RISCV64.dataRegion, byteMode, Nat.one_mul]
  refine ⟨al, sp, by rw [eV, hwr]; simp, fun _ => by rw [eV, hwr]; simp, by rw [eb]; exact fV,
    by rw [eD, hwr]; simp, by simp only [byteMode, Nat.one_mul]; exact fD, by rw [eD, eS]; exact dSD.symm,
    by rw [eV, eS]; exact dSV.symm, fun _ => by rw [eV, eD]; exact dVD, ⟨by decide, by rw [eb]; decide⟩,
    layout true⟩

theorem keyArgsF_of {post : State → State → Prop} {s : State} (h : (finalContract post).pre s) :
    KeyArgs s (Proof.Modes.RISCV64.wrs0 (dirCore true) byteMode s) (Spec.Blowfish.scheduleAt s.mem (s.gpr .a0)) := by
  obtain ⟨hrd, -, -, dKD, -, -, -, -, -, dSK, -, -⟩ := h
  refine ⟨rfl, by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _), fun r hr => ?_⟩
  simp only [Proof.Modes.RISCV64.wrs0, Proof.Modes.RISCV64.wrs, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl
  · show (Region.mk (s.gpr .a0) 4168).Disjoint ⟨s.gpr .a2, 1 * (s.gpr .a3).toNat⟩
    rw [Nat.one_mul]; exact dKD
  · exact dSK.symm

theorem cfbEncryptFinal_correct (s : State) (hs : (finalContract encFinalPost).pre s) :
    ∃ t s', Exec isa cfbEncryptFinal s t s' ∧ abiPreserved s s' ∧ (finalContract encFinalPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.cfbEncFinal_wp (dirCoreSpec true) (seqPreF_of hs) (keyArgsF_of hs))
    fun _ ⟨h1, h2, _⟩ => ⟨h1, h2⟩

theorem cfbDecryptFinal_correct (s : State) (hs : (finalContract decFinalPost).pre s) :
    ∃ t s', Exec isa cfbDecryptFinal s t s' ∧ abiPreserved s s' ∧ (finalContract decFinalPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.cfbDecFinal_wp (dirCoreSpec true) (seqPreF_of hs) (keyArgsF_of hs))
    fun _ ⟨h1, h2, _⟩ => ⟨h1, h2⟩

theorem ofbFinal_correct (s : State) (hs : (finalContract ofbFinalPost).pre s) :
    ∃ t s', Exec isa ofbFinal s t s' ∧ abiPreserved s s' ∧ (finalContract ofbFinalPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.ofbFinal_wp (dirCoreSpec true) (seqPreF_of hs) (keyArgsF_of hs))
    fun _ ⟨h1, h2, _⟩ => ⟨h1, h2⟩

/-! ## Constant time -/

theorem cfbEncryptFinal_constantTime (pre : State → Prop) : ConstantTime isa pre modePub cfbEncryptFinal :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

theorem cfbDecryptFinal_constantTime (pre : State → Prop) : ConstantTime isa pre modePub cfbDecryptFinal :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

theorem ofbFinal_constantTime (pre : State → Prop) : ConstantTime isa pre modePub ofbFinal :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

/-! ## The contracts -/

theorem cfbEncryptFinal_verified :
    Verified RISCV64.target cfbEncryptFinal (Spec.Blowfish.cfbEncryptFinalContract RISCV64.abi (frameBytes)) := by
  refine Verified.of_correct cfbEncryptFinal_correct (cfbEncryptFinal_constantTime _) ?_
  contract_implies [Spec.Blowfish.cfbEncryptFinalContract, Spec.Blowfish.cfbFinalSig, RISCV64.abi,
    RISCV64.argRegs, finalContract, encFinalPost, modePub_iff] [modeSat] using modeSat

theorem cfbDecryptFinal_verified :
    Verified RISCV64.target cfbDecryptFinal (Spec.Blowfish.cfbDecryptFinalContract RISCV64.abi (frameBytes)) := by
  refine Verified.of_correct cfbDecryptFinal_correct (cfbDecryptFinal_constantTime _) ?_
  contract_implies [Spec.Blowfish.cfbDecryptFinalContract, Spec.Blowfish.cfbFinalSig, RISCV64.abi,
    RISCV64.argRegs, finalContract, decFinalPost, modePub_iff] [modeSat] using modeSat

theorem ofbFinal_verified :
    Verified RISCV64.target ofbFinal (Spec.Blowfish.ofbFinalContract RISCV64.abi (frameBytes)) := by
  refine Verified.of_correct ofbFinal_correct (ofbFinal_constantTime _) ?_
  contract_implies [Spec.Blowfish.ofbFinalContract, Spec.Blowfish.ofbFinalSig, RISCV64.abi,
    RISCV64.argRegs, finalContract, ofbFinalPost, modePub_iff] [modeSat] using modeSat

end VG.Proof.Blowfish.RISCV64.Modes
