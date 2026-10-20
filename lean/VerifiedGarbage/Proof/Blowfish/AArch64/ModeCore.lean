module

public import VerifiedGarbage.Proof.Blowfish.AArch64.KeepV
public import VerifiedGarbage.Proof.Blowfish.ModeBytes
public import VerifiedGarbage.Proof.Modes.AArch64.FbLoop
public import VerifiedGarbage.Impl.Blowfish.AArch64.Modes
public import VerifiedGarbage.Proof.Blowfish.AArch64.Sbox
import VerifiedGarbage.Proof.Modes.AArch64.Steps
import VerifiedGarbage.Proof.Blowfish.AArch64.ModesLit
import VerifiedGarbage.Proof.Blowfish.AArch64.EcbMain
import VerifiedGarbage.Impl.Blowfish.AArch64
import VerifiedGarbage.Proof.Blowfish.Schedule
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Spec.Blowfish
import VerifiedGarbage.TCB.AArch64.Isa
import VerifiedGarbage.TCB.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Blowfish's core for the modes on AArch64

`dirCoreSpec up`: Blowfish's core (`Impl.Blowfish.AArch64.dirCore up`)
meets what the modes need of a core of one-word blocks
(`Proof.Modes.AArch64.BlockSpec`), with the key a schedule, its cipher
encryption (`up`) or decryption (`dirCipher`), and the key ready when the
schedule is at `x0`, readable and outside every writable region (`SchedAt`),
where nothing the modes or the core write can reach it. `crypt` is the ECB
functions' batch (`batch_ok`) on the buffer's sixteen blocks.

`crypt_vKeep`: every run of `crypt` keeps the low halves of `v8`–`v15`,
which it keeps in `x8`–`x15` across the batch, which does not write them;
`crypt_keeps`: it keeps `x25`, where the feedback modes keep the IV's
address.
-/

@[expose] public section

namespace VG.Proof.Blowfish.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Blowfish.AArch64 VG.Spec.Blowfish VG.Proof.Blowfish
open VG.Impl.Aes.AArch64 (sb movR)
open VG.Proof.Modes.AArch64 (ScrIn WrIn coreRegion blkRegion blkAddr BlockSpec movR_ok runBlock_app
  KeepsReg regSafe keepsReg_of_regSafe)

/-- The schedule at `p`: readable, within the address space, and outside
every writable region. -/
structure SchedAt (s : State) (p : Addr) : Prop where
  rd : (⟨p, 4168⟩ : Region) ∈ s.rd
  fit : p.toNat + 4168 ≤ 2 ^ 64
  sep : ∀ w ∈ s.wr, Region.Disjoint ⟨p, 4168⟩ w

theorem SchedAt.congr {s s' : State} {p : Addr} (h : SchedAt s p) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    SchedAt s' p :=
  ⟨by rw [hrd]; exact h.rd, h.fit, by rw [hwr]; exact h.sep⟩

/-- The schedule at `x0`, outside the regions `rs` and every writable one. -/
def ModeKeyArgs (s : State) (rs : List Region) (k : Schedule) : Prop :=
  ∃ p : Addr, s.gpr .x0 = p ∧ k = scheduleAt s.mem p ∧ SchedAt s p ∧ ∀ r ∈ rs, Region.Disjoint ⟨p, 4168⟩ r

/-- The schedule at `x0` is `k`. -/
def ReadyAt (s : State) (k : Schedule) : Prop :=
  ∃ p : Addr, s.gpr .x0 = p ∧ scheduleAt s.mem p = k ∧ SchedAt s p

@[simp] theorem dirCore_bw (up : Bool) : (dirCore up).bw = 1 := rfl

theorem core_eq (up : Bool) (B : Addr) : coreRegion (dirCore up) B = ⟨B, 128⟩ := rfl
theorem total_eq (up : Bool) : (dirCore up).total = 28 := rfl

theorem x0_not_mode (up : Bool) : Reg.x0 ∉ Modes.AArch64.modeRegs (dirCore up) := by
  simp only [Modes.AArch64.modeRegs, dirCore]; decide

theorem ready_frame {up : Bool} {s s' : State} {k : Schedule} {rs : List Region} (h : ReadyAt s k)
    (hf : Frame rs s.mem s'.mem) (hw : WrIn rs s s')
    (hg : ∀ r, r ∉ Modes.AArch64.modeRegs (dirCore up) → s'.gpr r = s.gpr r) : ReadyAt s' k := by
  obtain ⟨p, hp, hk, hS⟩ := h
  refine ⟨p, by rw [hg _ (x0_not_mode up), hp], ?_, hS.congr hw.rd hw.wr⟩
  rw [scheduleAt_eq_of_frame _ hf fun r hr => ?_, hk]
  obtain ⟨w, hw', hsub⟩ := hw.sub r hr
  exact (hS.sep w hw').sub_right hsub

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Schedule} (h : ModeKeyArgs s rs k)
    (hr : ∀ r ∈ [Reg.x0], s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hf : Frame rs s.mem s'.mem) : ModeKeyArgs s' rs k := by
  obtain ⟨p, hp, hk, hS, hdis⟩ := h
  refine ⟨p, by rw [hr .x0 List.mem_cons_self, hp], ?_, hS.congr hrd hwr, hdis⟩
  rw [hk]
  exact (scheduleAt_eq_of_frame _ hf hdis).symm

theorem prepare_wp {up : Bool} {s : State} {B : Addr} {rs : List Region} {k : Schedule}
    (hB : s.gpr sb = B) (_ : ScrIn s B (dirCore up).total) (_ : (⟨B, 8 * (dirCore up).total⟩ : Region) ∈ rs)
    (hk : ModeKeyArgs s rs k) :
    WP isa (dirCore up).prepare s fun s' => ReadyAt s' k ∧ s'.gpr sb = B ∧
      s'.gpr .x23 = s.gpr .x23 ∧ s'.gpr .x24 = s.gpr .x24 ∧
      Frame [coreRegion (dirCore up) B] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨p, hp, hk, hS, -⟩ := hk
  exact WP.block_nil ⟨⟨p, hp, hk.symm, hS⟩, hB, rfl, rfl, Frame.refl _ _, rfl, rfl⟩

/-! ## The steps around the batch -/

/-- The registers `modeSave` writes. -/
def keepList : List Reg := [.x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15]

theorem modeSave_eq : modeSave = [.umov .x .x8 .v8 0, .umov .x .x9 .v9 0, .umov .x .x10 .v10 0,
    .umov .x .x11 .v11 0, .umov .x .x12 .v12 0, .umov .x .x13 .v13 0, .umov .x .x14 .v14 0,
    .umov .x .x15 .v15 0] := rfl

theorem modeRestore_eq : modeRestore = ([.vop (.dup .d2 .v8 .x8), .vop (.dup .d2 .v9 .x9),
    .vop (.dup .d2 .v10 .x10), .vop (.dup .d2 .v11 .x11), .vop (.dup .d2 .v12 .x12),
    .vop (.dup .d2 .v13 .x13), .vop (.dup .d2 .v14 .x14), .vop (.dup .d2 .v15 .x15)] : List Instr) ++
    ([movR sb .x16] : List Instr) := rfl

theorem exec_umov_x (s : State) (d : Reg) (n : VReg) :
    exec (.umov .x d n 0) s = some (s.write .x d ((s.v n).extractLsb' 0 64)) := rfl

theorem exec_dup_x (s : State) (d : VReg) (n : Reg) :
    exec (.vop (.dup .d2 d n)) s = some (s.setV d (ofVDwords (s.gpr n) (s.gpr n))) := rfl

theorem extract_dup (x : BitVec 64) : (ofVDwords x x).extractLsb' 0 64 = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [ofVDwords, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and,
    Nat.zero_add, ite_true]

theorem lt8 {k : Nat} (hk : k < 8) :
    k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega

theorem modeSave_run (s : State) :
    ∃ s', runBlock isa modeSave s = some s' ∧
      (∀ k < 8, s'.gpr (modeKeep k) = (s.v (modeV k)).extractLsb' 0 64) ∧
      (∀ r, r ∉ keepList → s'.gpr r = s.gpr r) ∧ s' = { s with gpr := s'.gpr } := by
  let t₁ := s.write .x .x8 ((s.v .v8).extractLsb' 0 64)
  let t₂ := t₁.write .x .x9 ((t₁.v .v9).extractLsb' 0 64)
  let t₃ := t₂.write .x .x10 ((t₂.v .v10).extractLsb' 0 64)
  let t₄ := t₃.write .x .x11 ((t₃.v .v11).extractLsb' 0 64)
  let t₅ := t₄.write .x .x12 ((t₄.v .v12).extractLsb' 0 64)
  let t₆ := t₅.write .x .x13 ((t₅.v .v13).extractLsb' 0 64)
  let t₇ := t₆.write .x .x14 ((t₆.v .v14).extractLsb' 0 64)
  let t₈ := t₇.write .x .x15 ((t₇.v .v15).extractLsb' 0 64)
  refine ⟨t₈, ?_, fun k hk => ?_, fun r hr => ?_, rfl⟩
  · rw [modeSave_eq, runBlock_cons, exec_umov_x, runStep_some, runBlock_cons, exec_umov_x, runStep_some,
      runBlock_cons, exec_umov_x, runStep_some, runBlock_cons, exec_umov_x, runStep_some,
      runBlock_cons, exec_umov_x, runStep_some, runBlock_cons, exec_umov_x, runStep_some,
      runBlock_cons, exec_umov_x, runStep_some, runBlock_cons, exec_umov_x, runStep_some, runBlock_nil]
  · rcases lt8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [modeKeep, modeV, List.getD_cons_succ, List.getD_cons_zero, t₈, t₇, t₆, t₅, t₄, t₃, t₂, t₁,
        gpr_write, v_write, BitVec.setWidth_eq, reduceCtorEq, ↓reduceIte]
  · simp only [keepList, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [t₈, t₇, t₆, t₅, t₄, t₃, t₂, t₁, gpr_write, hr, ↓reduceIte]

theorem modeRestore_run (s : State) :
    ∃ s', runBlock isa modeRestore s = some s' ∧
      (∀ k < 8, (s'.v (modeV k)).extractLsb' 0 64 = s.gpr (modeKeep k)) ∧
      s'.gpr sb = s.gpr .x16 ∧ (∀ r, r ≠ sb → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let t₁ := s.setV .v8 (ofVDwords (s.gpr .x8) (s.gpr .x8))
  let t₂ := t₁.setV .v9 (ofVDwords (t₁.gpr .x9) (t₁.gpr .x9))
  let t₃ := t₂.setV .v10 (ofVDwords (t₂.gpr .x10) (t₂.gpr .x10))
  let t₄ := t₃.setV .v11 (ofVDwords (t₃.gpr .x11) (t₃.gpr .x11))
  let t₅ := t₄.setV .v12 (ofVDwords (t₄.gpr .x12) (t₄.gpr .x12))
  let t₆ := t₅.setV .v13 (ofVDwords (t₅.gpr .x13) (t₅.gpr .x13))
  let t₇ := t₆.setV .v14 (ofVDwords (t₆.gpr .x14) (t₆.gpr .x14))
  let t₈ := t₇.setV .v15 (ofVDwords (t₇.gpr .x15) (t₇.gpr .x15))
  have e₈ : runBlock isa [.vop (.dup .d2 .v8 .x8), .vop (.dup .d2 .v9 .x9),
      .vop (.dup .d2 .v10 .x10), .vop (.dup .d2 .v11 .x11), .vop (.dup .d2 .v12 .x12),
      .vop (.dup .d2 .v13 .x13), .vop (.dup .d2 .v14 .x14), .vop (.dup .d2 .v15 .x15)] s = some t₈ := by
    rw [runBlock_cons, exec_dup_x, runStep_some, runBlock_cons, exec_dup_x, runStep_some,
      runBlock_cons, exec_dup_x, runStep_some, runBlock_cons, exec_dup_x, runStep_some,
      runBlock_cons, exec_dup_x, runStep_some, runBlock_cons, exec_dup_x, runStep_some,
      runBlock_cons, exec_dup_x, runStep_some, runBlock_cons, exec_dup_x, runStep_some, runBlock_nil]
  have g₈ : t₈.gpr = s.gpr := by simp only [t₈, t₇, t₆, t₅, t₄, t₃, t₂, t₁, gpr_setV]
  have mem₈ : t₈.mem = s.mem := by simp only [t₈, t₇, t₆, t₅, t₄, t₃, t₂, t₁, mem_setV]
  have rd₈ : t₈.rd = s.rd := by simp only [t₈, t₇, t₆, t₅, t₄, t₃, t₂, t₁, rd_setV]
  have wr₈ : t₈.wr = s.wr := by simp only [t₈, t₇, t₆, t₅, t₄, t₃, t₂, t₁, wr_setV]
  let t₉ := t₈.write .x sb (t₈.gpr .x16 + BitVec.ofNat 64 0)
  have e₉ : runBlock isa [movR sb .x16] t₈ = some t₉ := by
    simp only [movR, runBlock_cons, runStep_some, runBlock_nil, exec_addImm_x (show 0 < 4096 by decide),
      Modes.AArch64.read_x, t₉]
  obtain ⟨r₉, o₉, m₉, rd₉, wr₉⟩ := Modes.AArch64.write_ok t₈ sb (t₈.gpr .x16 + BitVec.ofNat 64 0)
  refine ⟨t₉, by rw [modeRestore_eq, runBlock_app, e₈, Option.bind_some, e₉], fun k hk => ?_,
    by rw [r₉, BitVec.add_zero, g₈], fun r hr => by rw [o₉ r hr, g₈], by rw [m₉, mem₈], by rw [rd₉, rd₈],
    by rw [wr₉, wr₈]⟩
  rcases lt8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [modeKeep, modeV, List.getD_cons_succ, List.getD_cons_zero, t₉, t₈, t₇, t₆, t₅, t₄, t₃, t₂, t₁,
      v_write, v_setV, gpr_setV, extract_dup, reduceCtorEq, ↓reduceIte]

theorem modeSetup_run (s : State) :
    ∃ s', runBlock isa modeSetup s = some s' ∧ s'.gpr .x16 = s.gpr sb ∧ s'.gpr .x4 = s.gpr sb ∧
      (∀ r, r ≠ .x16 → r ≠ .x4 → r ≠ .x6 → s'.gpr r = s.gpr r) ∧ Consts s' ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s .x16 sb
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := movR_ok s₁ .x4 sb
  obtain ⟨s₃, e₃, c₃, o₃, m₃, rd₃, wr₃, -⟩ := constants_run s₂
  refine ⟨s₃, ?_, by rw [o₃ _ (by decide), o₂ _ (by decide), r₁],
    by rw [o₃ _ (by decide), r₂, o₁ _ (by decide)], fun r h1 h2 h3 => by rw [o₃ r h3, o₂ r h2, o₁ r h1], c₃,
    by rw [m₃, m₂, m₁], by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁]⟩
  show runBlock isa ([movR .x16 sb] ++ ([movR .x4 sb] ++ constants)) s = some s₃
  rw [runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, e₃]

theorem batchOf_eq (up : Bool) : batchOf up = batch up := by cases up <;> rfl

/-! ## `crypt` -/

theorem crypt_wp {up : Bool} {s : State} {B : Addr} {k : Schedule} (hB : s.gpr sb = B)
    (hs : ScrIn s B (dirCore up).total) (hr : ReadyAt s k) :
    WP isa (dirCore up).crypt s fun s' => s'.gpr sb = B ∧
      s'.gpr .x23 = s.gpr .x23 ∧ s'.gpr .x24 = s.gpr .x24 ∧ ReadyAt s' k ∧
      Frame [coreRegion (dirCore up) B] s.mem s'.mem ∧
      (∀ j < (dirCore up).G, Spec.Aes.bytesAt s'.mem (blkAddr (dirCore up) B j) (8 * (dirCore up).bw) =
        dirCipher up k (Spec.Aes.bytesAt s.mem (blkAddr (dirCore up) B j) (8 * (dirCore up).bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨p, hp, hK, hS⟩ := hr
  have hw := hs.wr
  have hfit := hs.fit
  rw [total_eq] at hw hfit
  -- The low halves of `v8`–`v15` to `x8`–`x15`.
  obtain ⟨s₁, e₁, -, g₁, eq₁⟩ := modeSave_run s
  have mem₁ : s₁.mem = s.mem := by rw [eq₁]
  have rd₁ : s₁.rd = s.rd := by rw [eq₁]
  have wr₁ : s₁.wr = s.wr := by rw [eq₁]
  -- The setup.
  obtain ⟨s₂, e₂, x16₂, x4₂, g₂, c₂, mem₂, rd₂, wr₂⟩ := modeSetup_run s₁
  have g₂' : ∀ r, r ∉ keepList → r ≠ .x16 → r ≠ .x4 → r ≠ .x6 → s₂.gpr r = s.gpr r :=
    fun r h0 h1 h2 h3 => by rw [g₂ r h1 h2 h3, g₁ r h0]
  have sb₁ : s₁.gpr sb = B := by rw [g₁ _ (by decide), hB]
  have x0₂ : s₂.gpr .x0 = p := by
    rw [g₂' _ (by decide) (by decide) (by decide) (by decide), hp]
  have x4B : s₂.gpr .x4 = B := by rw [x4₂, sb₁]
  rw [mem₁] at mem₂; rw [rd₁] at rd₂; rw [wr₁] at wr₂
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, WP.seq (WP.of_runBlock ⟨s₂, e₂, ?_⟩)⟩)
  -- The batch.
  have hS₂ : SchedIn s₂ .x0 := fun off n h => by
    rw [x0₂, rd₂]
    exact ⟨_, List.mem_append_left _ hS.rd, Offset.contains_base p h (by omega)⟩
  have hW₂ : ∀ j < 8, InRegions s₂.wr (s₂.gpr .x4 + BitVec.ofNat 64 (16 * j)) 16 := fun j hj => by
    rw [x4B, wr₂]
    exact ⟨_, hw, Offset.contains_base B (by omega) (by omega)⟩
  rw [batchOf_eq]
  refine WP.seq (WP.mono (batch_ok up hS₂ c₂ hW₂) fun s₃ P => ?_)
  -- `v8`–`v15` and `sb` back.
  obtain ⟨s₄, e₄, -, sb₄, g₄, mem₄, rd₄, wr₄⟩ := modeRestore_run s₃
  refine WP.of_runBlock ⟨s₄, e₄, ?_⟩
  have g₃ : ∀ r, r ∉ keepList → r ≠ .x16 → r ≠ .x4 → r ≠ .x6 → r ≠ .x5 → r ≠ .x7 → s₄.gpr r = s.gpr r :=
    fun r h0 h1 h2 h3 h5 h7 => by rw [g₄ r h5, P.gpr r h5 h3 h7, g₂' r h0 h1 h2 h3]
  have rdE : s₄.rd = s.rd := by rw [rd₄, P.rd, rd₂]
  have wrE : s₄.wr = s.wr := by rw [wr₄, P.wr, wr₂]
  have sch : ∀ r ∈ [(⟨s₂.gpr .x4, 128⟩ : Region)], Region.Disjoint ⟨p, 4168⟩ r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [x4B]; exact (hS.sep _ hw).sub_right (Region.sub_prefix (by decide))
  have fr : Frame [⟨B, 128⟩] s.mem s₄.mem := by rw [mem₄, ← mem₂, ← x4B]; exact P.frame
  refine ⟨by rw [sb₄, P.gpr _ (by decide) (by decide) (by decide), x16₂, sb₁],
    g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    ⟨p, by rw [g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hp], ?_,
      hS.congr rdE wrE⟩, by rw [core_eq]; exact fr, fun j hj => ?_, rdE, wrE⟩
  · rw [mem₄, scheduleAt_eq_of_frame _ P.frame sch, mem₂]; exact hK
  · have hj16 : j < 16 := by simp only [dirCore, Impl.Modes.AArch64.Core.G] at hj; exact hj
    have ea : blkAddr (dirCore up) B j = s₂.gpr .x4 + BitVec.ofNat 64 (8 * j) := by
      rw [x4B]; simp only [blkAddr, dirCore, Nat.mul_zero, Nat.zero_add, Nat.mul_one]
    rw [dirCore_bw, Nat.mul_one, ea, dirCipher_bytes, bytesAt_eq, mem₄, P.out j hj16, x0₂, mem₂, hK]
    rfl

/-- Blowfish's core meets what the modes need. -/
def dirCoreSpec (up : Bool) : BlockSpec (dirCore up) where
  Key := Schedule
  cipher := dirCipher up
  KeyArgs := ModeKeyArgs
  Ready s _ k := ReadyAt s k
  cipher_len := dirCipher_len up
  layout := ⟨by simp only [dirCore]; decide, by simp only [dirCore]; decide, by simp only [dirCore]; decide,
    by simp only [dirCore, Impl.Modes.AArch64.Core.G]; decide, by simp only [dirCore]; decide,
    by simp only [dirCore]; decide, by simp only [dirCore]; decide⟩
  keyRegs_ok := by simp only [dirCore]; decide
  regs_ok := by simp only [dirCore, Modes.AArch64.regsOk]; decide
  keyArgs_congr h hr hrd hwr _ hf := keyArgs_congr h hr hrd hwr hf
  ready_frame h hf _ hw hg := ready_frame h hf hw hg
  prepare_wp := prepare_wp
  crypt_wp := crypt_wp

/-! ## What every run of `crypt` keeps -/

/-- The batch writes neither `x8`–`x15` nor `x25`. -/
theorem batch_regSafe (up : Bool) :
    (∀ k < 8, regSafe (modeKeep k) (batchOf up) = true) ∧ regSafe .x25 (batchOf up) = true := by
  cases up
  · exact ⟨by show ∀ k < 8, regSafe (modeKeep k) batchDec = true; lit_decide,
      by show regSafe .x25 batchDec = true; lit_decide⟩
  · exact ⟨by show ∀ k < 8, regSafe (modeKeep k) batchEnc = true; lit_decide,
      by show regSafe .x25 batchEnc = true; lit_decide⟩

theorem setup_regSafe : ∀ k < 8, regSafe (modeKeep k) (.block modeSetup) = true := by decide

/-- Every run of `crypt` keeps the low halves of `v8`–`v15`. -/
theorem crypt_vKeep (up : Bool) : ∀ s t s', Exec isa (dirCore up).crypt s t s' → VKeep s s' := by
  intro s t s' he
  cases he with
  | seq e₁ e₂ =>
    cases e₂ with
    | seq e₃ e₄ =>
      cases e₄ with
      | seq e₅ e₆ =>
        rename_i s₁ _ s₂ _ s₃ _ _
        obtain ⟨u₁, r₁, h₁, -, -⟩ := modeSave_run s
        have q₁ := block_final e₁ r₁
        obtain ⟨u₄, r₄, h₄, -⟩ := modeRestore_run s₃
        have q₄ := block_final e₆ r₄
        subst q₁ q₄
        have hk : ∀ k < 8, (s'.v (modeV k)).extractLsb' 0 64 = (s.v (modeV k)).extractLsb' 0 64 :=
          fun k hk => by
            rw [h₄ k hk, keepsReg_of_regSafe ((batch_regSafe up).1 k hk) _ _ _ e₅,
              keepsReg_of_regSafe (setup_regSafe k hk) _ _ _ e₃, h₁ k hk]
        intro r hr
        simp only [preservedV, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        exacts [hk 0 (by decide), hk 1 (by decide), hk 2 (by decide), hk 3 (by decide), hk 4 (by decide),
          hk 5 (by decide), hk 6 (by decide), hk 7 (by decide)]

/-- The core keeps `x25`, where the feedback modes keep the IV's address. -/
theorem crypt_keeps : KeepsReg .x25 (dirCore true).prepare ∧ KeepsReg .x25 (dirCore true).crypt := by
  refine ⟨keepsReg_of_regSafe (by decide), keepsReg_of_regSafe ?_⟩
  show regSafe .x25 (modeCrypt true) = true
  simp only [modeCrypt, regSafe, (batch_regSafe true).2]
  decide

end VG.Proof.Blowfish.AArch64
