module

public import VerifiedGarbage.Proof.Cast5.AArch64.TblBatch
public import VerifiedGarbage.Proof.Cast5.AArch64.FbVerified
public import VerifiedGarbage.Proof.Blowfish.AArch64.ModeCore
public import VerifiedGarbage.Proof.Cast5.ModeScratch
public import VerifiedGarbage.Proof.Cast5.Rounds
public import VerifiedGarbage.Impl.Cast5.AArch64.TblModes
public import VerifiedGarbage.Impl.StackScratch.AArch64
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Cast5.Contract
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Blowfish.AArch64.EcbMain
import VerifiedGarbage.Proof.Blowfish.AArch64.ConstantTime
import VerifiedGarbage.Proof.Modes.AArch64.Steps
import VerifiedGarbage.Proof.Modes.AArch64.CbcDecChained
import VerifiedGarbage.Proof.Modes.AArch64.CfbDec.Whole
import VerifiedGarbage.Proof.Cast5.Memory
import VerifiedGarbage.Proof.Cast5.AArch64.TblLit
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Cast5.AArch64.TblBatch
meta import VerifiedGarbage.Proof.Cast5.AArch64.FbVerified
meta import VerifiedGarbage.Proof.Blowfish.AArch64.ModeCore
meta import VerifiedGarbage.Proof.Cast5.ModeScratch
meta import VerifiedGarbage.Proof.Cast5.Rounds
meta import VerifiedGarbage.Impl.Cast5.AArch64.TblModes
meta import VerifiedGarbage.Impl.StackScratch.AArch64
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Cast5.Contract
meta import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Proof.Blowfish.AArch64.EcbMain
meta import VerifiedGarbage.Proof.Blowfish.AArch64.ConstantTime
meta import VerifiedGarbage.Proof.Modes.AArch64.Steps
meta import VerifiedGarbage.Proof.Modes.AArch64.CbcDecChained
meta import VerifiedGarbage.Proof.Modes.AArch64.CfbDec.Whole
meta import VerifiedGarbage.Proof.Cast5.Memory
meta import VerifiedGarbage.Proof.Cast5.AArch64.TblLit
meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# CAST5-CBC and -CFB64 decryption on AArch64, sixteen blocks at a time

`batchCoreSpec up`: the core of sixteen blocks
(`Impl.Cast5.AArch64.Tbl.batchCore up`) meets what the modes need of a core
of one-word blocks (`Proof.Modes.AArch64.BlockSpec`), with the key the
subkeys and the number of rounds, its cipher encryption (`up`) or
decryption, and the key ready when the subkeys are at `x0`, readable and
outside every writable region, and `x1` holds the number of rounds. `crypt`
is the ECB functions' batch (`batch_ok`) on the buffer's sixteen blocks.
`crypt_vKeep`: every run of `crypt` keeps the low halves of `v8`–`v15`,
which it keeps in general-purpose registers the batch does not write.

`cbcDecryptChained_framed`, `cfbDecrypt_framed`: the modes' CBC decryption
that updates the chaining value and batched CFB decryption over that core,
with their working space on the stack, zeroed on return (224 bytes, the 28
words of the scratch buffer), meet the shared contracts. Each is constant
time by the taint analysis: the pointers, `rounds`, `n` and the stack
pointer are public, and so is everything the code computes from them.
-/

@[expose] public section

namespace VG.Proof.Cast5.AArch64.Tbl

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Cast5.AArch64.Tbl
open VG.Impl.Cast5.AArch64 (modeRegs)
open VG.Impl.Blowfish.AArch64 (constants)
open VG.Impl.Aes.AArch64 (sb movR)
open VG.Proof.Cast5 (dirCipher dirCipher_length bytesAt_eq)
open VG.Proof.Cast5.AArch64.Mode (SchedAt scheduleAt_frame dirCipher_bytes)
open VG.Proof.Modes.AArch64 (ScrIn WrIn coreRegion blkRegion blkAddr BlockSpec movR_ok runBlock_app
  runBlock_syms KeepsReg regSafe keepsReg_of_regSafe)
open VG.Proof.Blowfish.AArch64 (Consts constants_run cat_run exec_umov_x exec_dup_x extract_dup lt8 VKeep
  VSafeBut vKeep_of_vSafeBut block_final)

/-! ## The key -/

/-- The subkeys at `x0`, outside the regions `rs` and every writable one, and
the number of rounds in `x1`. -/
def ModeKeyArgs (s : State) (rs : List Region) (kn : Spec.Cast5.Schedule × Nat) : Prop :=
  (∃ p : Addr, s.gpr .x0 = p ∧ kn.1 = Spec.Cast5.scheduleAt s.mem p ∧ SchedAt s p ∧
    ∀ r ∈ rs, Region.Disjoint ⟨p, 128⟩ r) ∧
  s.gpr .x1 = BitVec.ofNat 64 kn.2 ∧ (kn.2 = 12 ∨ kn.2 = 16)

/-- The key `kn` is ready: its subkeys at `x0` and its number of rounds in `x1`. -/
def ReadyAt (s : State) (kn : Spec.Cast5.Schedule × Nat) : Prop :=
  (∃ p : Addr, s.gpr .x0 = p ∧ Spec.Cast5.scheduleAt s.mem p = kn.1 ∧ SchedAt s p) ∧
    s.gpr .x1 = BitVec.ofNat 64 kn.2 ∧ (kn.2 = 12 ∨ kn.2 = 16)

@[simp] theorem batchCore_bw (up : Bool) : (batchCore up).bw = 1 := rfl

theorem core_eq (up : Bool) (B : Addr) : coreRegion (batchCore up) B = ⟨B, 128⟩ := rfl
theorem total_eq (up : Bool) : (batchCore up).total = 28 := rfl

theorem x0_not_mode (up : Bool) : Reg.x0 ∉ Modes.AArch64.modeRegs (batchCore up) := by
  simp only [Modes.AArch64.modeRegs, batchCore]; decide

theorem x1_not_mode (up : Bool) : Reg.x1 ∉ Modes.AArch64.modeRegs (batchCore up) := by
  simp only [Modes.AArch64.modeRegs, batchCore]; decide

theorem ready_frame {up : Bool} {s s' : State} {kn : Spec.Cast5.Schedule × Nat} {rs : List Region}
    (h : ReadyAt s kn) (hf : Frame rs s.mem s'.mem) (hw : WrIn rs s s')
    (hg : ∀ r, r ∉ Modes.AArch64.modeRegs (batchCore up) → s'.gpr r = s.gpr r) : ReadyAt s' kn := by
  obtain ⟨⟨p, hp, hk, hS⟩, h1, hn⟩ := h
  refine ⟨⟨p, by rw [hg _ (x0_not_mode up), hp], ?_, hS.congr hw.rd hw.wr⟩, by rw [hg _ (x1_not_mode up), h1], hn⟩
  rw [scheduleAt_frame hf fun r hr => ?_, hk]
  obtain ⟨w, hw', hsub⟩ := hw.sub r hr
  exact (hS.sep w hw').sub_right hsub

theorem keyArgs_congr {s s' : State} {rs : List Region} {kn : Spec.Cast5.Schedule × Nat}
    (h : ModeKeyArgs s rs kn) (hr : ∀ r ∈ [Reg.x0, .x1], s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hf : Frame rs s.mem s'.mem) : ModeKeyArgs s' rs kn := by
  obtain ⟨⟨p, hp, hk, hS, hdis⟩, h1, hn⟩ := h
  refine ⟨⟨p, by rw [hr .x0 (by simp), hp], ?_, hS.congr hrd hwr, hdis⟩, by rw [hr .x1 (by simp), h1], hn⟩
  rw [hk]
  exact (scheduleAt_frame hf hdis).symm

theorem prepare_wp {up : Bool} {s : State} {B : Addr} {rs : List Region} {kn : Spec.Cast5.Schedule × Nat}
    (hB : s.gpr sb = B) (_ : ScrIn s B (batchCore up).total) (_ : (⟨B, 8 * (batchCore up).total⟩ : Region) ∈ rs)
    (hk : ModeKeyArgs s rs kn) :
    WP isa (batchCore up).prepare s fun s' => ReadyAt s' kn ∧ s'.gpr sb = B ∧
      s'.gpr .x23 = s.gpr .x23 ∧ s'.gpr .x24 = s.gpr .x24 ∧
      Frame [coreRegion (batchCore up) B] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨⟨p, hp, hk, hS, -⟩, h1, hn⟩ := hk
  exact WP.block_nil ⟨⟨⟨p, hp, hk.symm, hS⟩, h1, hn⟩, hB, rfl, rfl, Frame.refl _ _, rfl, rfl⟩

/-! ## The steps around the batch -/

/-- The registers `modeSave` writes. -/
def keepList : List Reg := [.x11, .x12, .x19, .x20, .x21, .x26, .x27, .x28]

theorem modeSave_eq : modeSave = [.umov .x .x11 .v8 0, .umov .x .x12 .v9 0, .umov .x .x19 .v10 0,
    .umov .x .x20 .v11 0, .umov .x .x21 .v12 0, .umov .x .x26 .v13 0, .umov .x .x27 .v14 0,
    .umov .x .x28 .v15 0] := rfl

theorem modeRestore_eq : modeRestore = ([.vop (.dup .d2 .v8 .x11), .vop (.dup .d2 .v9 .x12),
    .vop (.dup .d2 .v10 .x19), .vop (.dup .d2 .v11 .x20), .vop (.dup .d2 .v12 .x21),
    .vop (.dup .d2 .v13 .x26), .vop (.dup .d2 .v14 .x27), .vop (.dup .d2 .v15 .x28)] : List Instr) ++
    ([movR sb .x22] : List Instr) := rfl

theorem modeSave_run (s : State) :
    ∃ s', runBlock isa modeSave s = some s' ∧
      (∀ k < 8, s'.gpr (modeKeep k) = (s.v (modeV k)).extractLsb' 0 64) ∧
      (∀ r, r ∉ keepList → s'.gpr r = s.gpr r) ∧ s' = { s with gpr := s'.gpr } := by
  let t₁ := s.write .x .x11 ((s.v .v8).extractLsb' 0 64)
  let t₂ := t₁.write .x .x12 ((t₁.v .v9).extractLsb' 0 64)
  let t₃ := t₂.write .x .x19 ((t₂.v .v10).extractLsb' 0 64)
  let t₄ := t₃.write .x .x20 ((t₃.v .v11).extractLsb' 0 64)
  let t₅ := t₄.write .x .x21 ((t₄.v .v12).extractLsb' 0 64)
  let t₆ := t₅.write .x .x26 ((t₅.v .v13).extractLsb' 0 64)
  let t₇ := t₆.write .x .x27 ((t₆.v .v14).extractLsb' 0 64)
  let t₈ := t₇.write .x .x28 ((t₇.v .v15).extractLsb' 0 64)
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
      s'.gpr sb = s.gpr .x22 ∧ (∀ r, r ≠ sb → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let t₁ := s.setV .v8 (ofVDwords (s.gpr .x11) (s.gpr .x11))
  let t₂ := t₁.setV .v9 (ofVDwords (t₁.gpr .x12) (t₁.gpr .x12))
  let t₃ := t₂.setV .v10 (ofVDwords (t₂.gpr .x19) (t₂.gpr .x19))
  let t₄ := t₃.setV .v11 (ofVDwords (t₃.gpr .x20) (t₃.gpr .x20))
  let t₅ := t₄.setV .v12 (ofVDwords (t₄.gpr .x21) (t₄.gpr .x21))
  let t₆ := t₅.setV .v13 (ofVDwords (t₅.gpr .x26) (t₅.gpr .x26))
  let t₇ := t₆.setV .v14 (ofVDwords (t₆.gpr .x27) (t₆.gpr .x27))
  let t₈ := t₇.setV .v15 (ofVDwords (t₇.gpr .x28) (t₇.gpr .x28))
  have e₈ : runBlock isa [.vop (.dup .d2 .v8 .x11), .vop (.dup .d2 .v9 .x12),
      .vop (.dup .d2 .v10 .x19), .vop (.dup .d2 .v11 .x20), .vop (.dup .d2 .v12 .x21),
      .vop (.dup .d2 .v13 .x26), .vop (.dup .d2 .v14 .x27), .vop (.dup .d2 .v15 .x28)] s = some t₈ := by
    rw [runBlock_cons, exec_dup_x, runStep_some, runBlock_cons, exec_dup_x, runStep_some,
      runBlock_cons, exec_dup_x, runStep_some, runBlock_cons, exec_dup_x, runStep_some,
      runBlock_cons, exec_dup_x, runStep_some, runBlock_cons, exec_dup_x, runStep_some,
      runBlock_cons, exec_dup_x, runStep_some, runBlock_cons, exec_dup_x, runStep_some, runBlock_nil]
  have g₈ : t₈.gpr = s.gpr := by simp only [t₈, t₇, t₆, t₅, t₄, t₃, t₂, t₁, gpr_setV]
  have mem₈ : t₈.mem = s.mem := by simp only [t₈, t₇, t₆, t₅, t₄, t₃, t₂, t₁, mem_setV]
  have rd₈ : t₈.rd = s.rd := by simp only [t₈, t₇, t₆, t₅, t₄, t₃, t₂, t₁, rd_setV]
  have wr₈ : t₈.wr = s.wr := by simp only [t₈, t₇, t₆, t₅, t₄, t₃, t₂, t₁, wr_setV]
  obtain ⟨t₉, e₉, r₉, o₉, m₉, rd₉, wr₉⟩ := movR_ok t₈ sb .x22
  have v₉ : t₉.v = t₈.v := by
    have h := Option.some.inj (e₉.symm.trans (by
      simp only [movR, runBlock_cons, runStep_some, runBlock_nil, exec_addImm_x (show 0 < 4096 by decide)] :
      runBlock isa [movR sb .x22] t₈ = some (t₈.write .x sb (t₈.read .x .x22 + BitVec.ofNat 64 0))))
    rw [h]; rfl
  refine ⟨t₉, by rw [modeRestore_eq, runBlock_app, e₈, Option.bind_some, e₉], fun k hk => ?_,
    by rw [r₉, g₈], fun r hr => by rw [o₉ r hr, g₈], by rw [m₉, mem₈], by rw [rd₉, rd₈],
    by rw [wr₉, wr₈]⟩
  rw [v₉]
  rcases lt8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [modeKeep, modeV, List.getD_cons_succ, List.getD_cons_zero, t₈, t₇, t₆, t₅, t₄, t₃, t₂, t₁,
      v_setV, gpr_setV, extract_dup, reduceCtorEq, ↓reduceIte]

theorem modeSetup_run (s : State) :
    ∃ s', runBlock isa modeSetup s = some s' ∧ s'.gpr .x22 = s.gpr sb ∧ s'.gpr .x4 = s.gpr sb ∧
      s'.gpr .x16 = s.gpr .x1 ∧ s'.gpr .x9 = s'.syms planesSym ∧
      (∀ r, r ≠ .x22 → r ≠ .x4 → r ≠ .x16 → r ≠ .x6 → r ≠ .x9 → s'.gpr r = s.gpr r) ∧ Consts s' ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s .x22 sb
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := movR_ok s₁ .x4 sb
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := movR_ok s₂ .x16 .x1
  obtain ⟨s₄, e₄, c₄, o₄, m₄, rd₄, wr₄, -, -⟩ := constants_run s₃
  let s₅ := s₄.write .x .x9 (s₄.syms planesSym)
  have e₅ : runBlock isa ([.adrSym .x9 planesSym] : List Instr) s₄ = some s₅ := by
    rw [runBlock_cons, exec_adrSym, runStep_some, runBlock_nil]
  have o₅ : ∀ r, r ≠ .x9 → s₅.gpr r = s₄.gpr r := fun r hr => gpr_write_of_ne _ _ _ hr
  refine ⟨s₅, ?_, by rw [o₅ _ (by decide), o₄ _ (by decide), o₃ _ (by decide), o₂ _ (by decide), r₁],
    by rw [o₅ _ (by decide), o₄ _ (by decide), o₃ _ (by decide), r₂, o₁ _ (by decide)],
    by rw [o₅ _ (by decide), o₄ _ (by decide), r₃, o₂ _ (by decide), o₁ _ (by decide)], ?_,
    fun r h22 h4 h16 h6 h9 => by rw [o₅ r h9, o₄ r h6, o₃ r h16, o₂ r h4, o₁ r h22], c₄,
    m₄.trans (m₃.trans (m₂.trans m₁)), rd₄.trans (rd₃.trans (rd₂.trans rd₁)),
    wr₄.trans (wr₃.trans (wr₂.trans wr₁))⟩
  · show runBlock isa ([movR .x22 sb] ++ ([movR .x4 sb] ++ ([movR .x16 .x1] ++
      (constants ++ ([.adrSym .x9 planesSym] : List Instr))))) s = some s₅
    exact cat_run e₁ (cat_run e₂ (cat_run e₃ (cat_run e₄ e₅)))
  · show (s₄.write .x .x9 _).gpr .x9 = s₄.syms planesSym
    rw [gpr_write_self]; exact BitVec.setWidth_eq _

theorem batchOf_eq (up : Bool) : batchOf up = batch up := by cases up <;> rfl

/-! ## `crypt` -/

theorem crypt_wp {up : Bool} {s : State} {B : Addr} {kn : Spec.Cast5.Schedule × Nat} (hB : s.gpr sb = B)
    (hs : ScrIn s B (batchCore up).total) (hr : ReadyAt s kn) :
    WP isa (batchCore up).crypt s fun s' => s'.gpr sb = B ∧
      s'.gpr .x23 = s.gpr .x23 ∧ s'.gpr .x24 = s.gpr .x24 ∧ ReadyAt s' kn ∧
      Frame [coreRegion (batchCore up) B] s.mem s'.mem ∧
      (∀ j < (batchCore up).G, Spec.Aes.bytesAt s'.mem (blkAddr (batchCore up) B j) (8 * (batchCore up).bw) =
        dirCipher up kn.1 kn.2 (Spec.Aes.bytesAt s.mem (blkAddr (batchCore up) B j) (8 * (batchCore up).bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨k, n⟩ := kn
  obtain ⟨⟨p, hp, hK, hS⟩, h1, hn⟩ := hr
  have hw := hs.wr
  have hfit := hs.fit
  rw [total_eq] at hw hfit
  -- The low halves of `v8`–`v15` to their registers.
  obtain ⟨s₁, e₁, -, g₁, eq₁⟩ := modeSave_run s
  have mem₁ : s₁.mem = s.mem := by rw [eq₁]
  have rd₁ : s₁.rd = s.rd := by rw [eq₁]
  have wr₁ : s₁.wr = s.wr := by rw [eq₁]
  -- The setup.
  obtain ⟨s₂, e₂, x22₂, x4₂, x16₂, x9₂, g₂, c₂, mem₂, rd₂, wr₂⟩ := modeSetup_run s₁
  have g₂' : ∀ r, r ∉ keepList → r ≠ .x22 → r ≠ .x4 → r ≠ .x16 → r ≠ .x6 → r ≠ .x9 → s₂.gpr r = s.gpr r :=
    fun r h0 h22 h4 h16 h6 h9 => by rw [g₂ r h22 h4 h16 h6 h9, g₁ r h0]
  have sb₁ : s₁.gpr sb = B := by rw [g₁ _ (by decide), hB]
  have x0₂ : s₂.gpr .x0 = p := by
    rw [g₂' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hp]
  have x4B : s₂.gpr .x4 = B := by rw [x4₂, sb₁]
  rw [mem₁] at mem₂; rw [rd₁] at rd₂; rw [wr₁] at wr₂
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, WP.seq (WP.of_runBlock ⟨s₂, e₂, ?_⟩)⟩)
  -- The batch.
  have P₂ : CPre s₂ k := ⟨x9₂, c₂, by
    rw [x0₂, rd₂]
    exact ⟨_, List.mem_append_left _ hS.rd, Region.contains_self _ _⟩, fun j hj => by
    rw [x0₂, mem₂, ← Proof.Cast5.scheduleAt_getD _ _ hj, hK]⟩
  have hW₂ : ∀ j < 8, InRegions s₂.wr (s₂.gpr .x4 + BitVec.ofNat 64 (16 * j)) 16 := fun j hj => by
    rw [x4B, wr₂]
    exact ⟨_, hw, Offset.contains_base B (by omega_using [hj]) (by omega_using [hj])⟩
  have h16 : s₂.gpr .x16 = BitVec.ofNat 64 n := by rw [x16₂, g₁ _ (by decide), h1]
  rw [batchOf_eq]
  refine WP.seq (WP.mono (batch_ok up P₂ hn h16 hW₂) fun s₃ P => ?_)
  -- `v8`–`v15` and `sb` back.
  obtain ⟨s₄, e₄, -, sb₄, g₄, mem₄, rd₄, wr₄⟩ := modeRestore_run s₃
  refine WP.of_runBlock ⟨s₄, e₄, ?_⟩
  have g₃ : ∀ r, r ∉ keepList → r ≠ .x22 → r ≠ .x4 → r ≠ .x16 → r ≠ .x6 → r ≠ .x9 → r ∉ batchG →
      s₄.gpr r = s.gpr r :=
    fun r h0 h22 h4 h16 h6 h9 hb => by
      rw [g₄ r (fun h => hb (by rw [h]; decide)), P.gpr r hb, g₂' r h0 h22 h4 h16 h6 h9]
  have rdE : s₄.rd = s.rd := by rw [rd₄, P.rd, rd₂]
  have wrE : s₄.wr = s.wr := by rw [wr₄, P.wr, wr₂]
  have dKB : Region.Disjoint ⟨p, 128⟩ ⟨B, 128⟩ := (hS.sep _ hw).sub_right (Region.sub_prefix (by decide))
  have fr : Frame [⟨B, 128⟩] s.mem s₄.mem := by rw [mem₄, ← mem₂, ← x4B]; exact P.frame
  refine ⟨by rw [sb₄, P.gpr _ (by decide), x22₂, sb₁],
    g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    ⟨⟨p, by rw [g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hp],
        ?_, hS.congr rdE wrE⟩,
      by rw [g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h1], hn⟩,
    by rw [core_eq]; exact fr, fun j hj => ?_, rdE, wrE⟩
  · rw [scheduleAt_frame fr fun r hr => ?_]
    · exact hK
    simp only [List.mem_singleton] at hr; subst hr; exact dKB
  · have hj16 : j < 16 := by simp only [batchCore, Impl.Modes.AArch64.Core.G] at hj; exact hj
    have ea : blkAddr (batchCore up) B j = s₂.gpr .x4 + BitVec.ofNat 64 (8 * j) := by
      rw [x4B]; simp only [blkAddr, batchCore, Nat.mul_zero, Nat.zero_add, Nat.mul_one]
    rw [batchCore_bw, Nat.mul_one, ea, dirCipher_bytes, bytesAt_eq, mem₄, P.out j hj16, mem₂]
    rfl

/-- CAST5's core of sixteen blocks meets what the modes need. -/
def batchCoreSpec (up : Bool) : BlockSpec (batchCore up) where
  Key := Spec.Cast5.Schedule × Nat
  cipher kn := dirCipher up kn.1 kn.2
  KeyArgs := ModeKeyArgs
  Ready s _ kn := ReadyAt s kn
  cipher_len kn b := by rw [batchCore_bw]; exact dirCipher_length up kn.1 kn.2 b
  layout := ⟨by simp only [batchCore]; decide, by simp only [batchCore]; decide, by simp only [batchCore]; decide,
    by simp only [batchCore, Impl.Modes.AArch64.Core.G]; decide, by simp only [batchCore]; decide,
    by simp only [batchCore]; decide, by simp only [batchCore]; decide⟩
  keyRegs_ok := by simp only [batchCore]; decide
  regs_ok := by simp only [batchCore, Modes.AArch64.regsOk]; decide
  keyArgs_congr h hr hrd hwr _ hf := keyArgs_congr h hr hrd hwr hf
  ready_frame h hf _ hw hg := ready_frame h hf hw hg
  prepare_wp := prepare_wp
  crypt_wp := crypt_wp

/-! ## What every run of `crypt` keeps -/

/-- The batch writes none of the registers that keep `v8`–`v15`. -/
theorem batch_regSafe (up : Bool) : ∀ k < 8, regSafe (modeKeep k) (batchOf up) = true := by
  cases up
  · show ∀ k < 8, regSafe (modeKeep k) batchDec = true; lit_decide
  · show ∀ k < 8, regSafe (modeKeep k) batchEnc = true; lit_decide

theorem setup_regSafe : ∀ k < 8, regSafe (modeKeep k) (.block modeSetup) = true := by decide

/-- Every run of `crypt` keeps the low halves of `v8`–`v15`. -/
theorem crypt_vKeep (up : Bool) : ∀ s t s', Exec isa (batchCore up).crypt s t s' → VKeep s s' := by
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
            rw [h₄ k hk, keepsReg_of_regSafe (batch_regSafe up k hk) _ _ _ e₅,
              keepsReg_of_regSafe (setup_regSafe k hk) _ _ _ e₃, h₁ k hk]
        intro r hr
        simp only [preservedV, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        exacts [hk 0 (by decide), hk 1 (by decide), hk 2 (by decide), hk 3 (by decide), hk 4 (by decide),
          hk 5 (by decide), hk 6 (by decide), hk 7 (by decide)]

end VG.Proof.Cast5.AArch64.Tbl

/-!
## The modes
-/

namespace VG.Proof.Cast5.AArch64.Tbl

open VG VG.AArch64 VG.Impl.Cast5.AArch64.Tbl
open VG.Impl.Cast5.AArch64 (modeRegs)
open VG.Proof.Cast5.AArch64 (dataOf ivOf keyOf blkLen blocksOf_eq ciphOf)
open VG.Proof.Blowfish.AArch64 (VSafeBut vKeep_of_vSafeBut)

/-- The modes' precondition, with the working space at `x5`. -/
def modePre (s : State) : Prop :=
  let sched : Region := ⟨s.gpr .x0, 128⟩
  let iv : Region := ⟨s.gpr .x2, 8⟩
  let data : Region := ⟨s.gpr .x3, blkLen s⟩
  let scratch : Region := ⟨s.gpr .x5, 8 * 28⟩
  s.rd = [sched] ∧ s.wr = [iv, data, scratch] ∧ sched.Disjoint iv ∧ sched.Disjoint data ∧
    sched.Disjoint scratch ∧ iv.Disjoint data ∧ iv.Disjoint scratch ∧ data.Disjoint scratch ∧
    (s.gpr .x0).toNat + 128 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + 8 ≤ 2 ^ 64 ∧
    (s.gpr .x3).toNat + blkLen s ≤ 2 ^ 64 ∧ (s.gpr .x5).toNat + 8 * 28 ≤ 2 ^ 64 ∧
    ((s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 16)

/-- The public arguments. -/
def modePub (s₁ s₂ : State) : Prop :=
  s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧ s₁.sp = s₂.sp

/-- CBC decryption that updates the chaining value. -/
def cbcDecX : Contract isa where
  pre := modePre
  post s s' :=
    dataOf s s'.mem = Spec.Cbc.decrypt (Spec.Cast5.invCipher (keyOf s) (s.gpr .x1).toNat) (ivOf s)
        (dataOf s s.mem) ∧
      Spec.Aes.bytesAt s'.mem (s.gpr .x2) 8 = Spec.Cbc.next (ivOf s) (dataOf s s.mem)
  pub := modePub

/-- CFB64 decryption. -/
def cfbDecX : Contract isa where
  pre := modePre
  post s s' := dataOf s s'.mem = Spec.Cfb.decrypt (ciphOf s) (ivOf s) (dataOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .x2) 8 = Spec.Cbc.next (ivOf s) (dataOf s s.mem)
  pub := modePub

/-- The key's arguments, from the precondition. -/
theorem keyArgs_of {s₀ : State} (hp : modePre s₀) :
    ModeKeyArgs s₀ [⟨s₀.gpr .x5, 8 * 28⟩, ⟨s₀.gpr .x2, 8⟩] (keyOf s₀, (s₀.gpr .x1).toNat) := by
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, fitK, fitV, fitD, fitB, hr⟩ := hp
  exact ⟨⟨s₀.gpr .x0, rfl, rfl, ⟨by rw [hrd]; simp, fitK, fun w hw => by
      rw [hwr] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact dKV
      · exact dKD
      · exact dKS⟩, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dKS
      · exact dKV⟩, by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], hr⟩

theorem cbcDecryptChained_wp {s₀ : State} (hp : cbcDecX.pre s₀) :
    WP isa cbcDecryptChained s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cbcDecX.post s₀ s' := by
  have hk := keyArgs_of hp
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, fitK, fitV, fitD, fitB, hr⟩ := hp
  have hwS : (⟨s₀.gpr .x5, 8 * 28⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  have e : 8 * (batchCore false).bw * (s₀.gpr .x4).toNat = (s₀.gpr .x4).toNat * 8 := by
    rw [batchCore_bw, Nat.mul_one, Nat.mul_comm]
  refine WP.mono (Proof.Modes.AArch64.cbcDecryptChained_wp (batchCoreSpec false) (r := modeRegs)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .x5) (P := s₀.gpr .x2) (D := s₀.gpr .x3) (n := (s₀.gpr .x4).toNat)
    (k := (keyOf s₀, (s₀.gpr .x1).toNat)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [e, hwr]; simp) dVS (by rw [e]; exact dDS) (by rw [e]; exact dVD)
    (by rw [e]; exact fitD) hk)
    fun s' ⟨hcs, hdata, hiv, _, _, _⟩ => ⟨hcs, ?_⟩
  rw [batchCore_bw, Nat.mul_one, blocksOf_eq, blocksOf_eq] at hdata
  rw [batchCore_bw, Nat.mul_one, blocksOf_eq] at hiv
  exact ⟨hdata, hiv⟩

theorem cfbDecrypt_wp {s₀ : State} (hp : cfbDecX.pre s₀) :
    WP isa cfbDecrypt s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cfbDecX.post s₀ s' := by
  have hk := keyArgs_of hp
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, fitK, fitV, fitD, fitB, hr⟩ := hp
  have hwS : (⟨s₀.gpr .x5, 8 * 28⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  have e : 8 * (batchCore true).bw * (s₀.gpr .x4).toNat = (s₀.gpr .x4).toNat * 8 := by
    rw [batchCore_bw, Nat.mul_one, Nat.mul_comm]
  refine WP.mono (Proof.Modes.AArch64.CfbDec.batched_wp (batchCoreSpec true) (r := modeRegs)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .x5) (P := s₀.gpr .x2) (D := s₀.gpr .x3) (n := (s₀.gpr .x4).toNat)
    (k := (keyOf s₀, (s₀.gpr .x1).toNat)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [e, hwr]; simp) dVS (by rw [e]; exact dDS) (by rw [e]; exact dVD)
    (by rw [e]; exact fitD) hk)
    fun s' ⟨hcs, hdata, hiv, _, _, _⟩ => ⟨hcs, ?_⟩
  rw [batchCore_bw, Nat.mul_one, blocksOf_eq, blocksOf_eq] at hdata
  rw [batchCore_bw, Nat.mul_one, blocksOf_eq] at hiv
  exact ⟨hdata, hiv⟩

/-! ## Constant time, and the contracts -/

theorem taint_agree (s₁ s₂ : State) (_ : modePre s₁) (_ : modePre s₂) (hp : modePub s₁ s₂) :
    VG.AArch64.Taint.Agree (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5]) s₁ s₂ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, hsp⟩ := hp
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- A state satisfying the precondition (one block, 16 rounds). -/
def modeSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 16 | .x2 => 0x2000 | .x3 => 0x3000 | .x4 => 1 | .x5 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 8⟩, ⟨0x4000, 8 * 28⟩]

/-- A state satisfying the functions' precondition, with 224 bytes of stack. -/
def modeFrameSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 16 | .x2 => 0x2000 | .x3 => 0x3000 | .x4 => 1 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 8⟩]

/-- Every instruction keeps `v8`–`v15`, but in `crypt`. -/
theorem cbcDecryptChained_vSafe : VSafeBut (batchCore false).crypt cbcDecryptChained := by
  unfold cbcDecryptChained; vsafe_but

theorem cfbDecrypt_vSafe : VSafeBut (batchCore true).crypt cfbDecrypt := by
  unfold cfbDecrypt; vsafe_but

theorem cbcDecryptChained_verified :
    Verified AArch64.target cbcDecryptChained
      (Proof.Cast5.modeScratchContract AArch64.abi Spec.Cast5.cbcChainedSig 28
        (Proof.Cast5.cbcChainedPre AArch64.abi.ptrBits) (Proof.Cast5.cbcDecChainedPost AArch64.abi.ptrBits)) :=
  Verified.of_correct (k := cbcDecX) (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs (rs := [.x30]) (cbcDecryptChained_wp hs) (by lit_decide)
        (by lit_decide)
      exact ⟨t, s', he, ⟨Proof.Modes.AArch64.preserved_of h₁ h₃, Exec.sp he,
        vKeep_of_vSafeBut cbcDecryptChained_vSafe (crypt_vKeep false) _ _ _ he⟩, h₂⟩)
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5]) taint_agree
      (by taint_decide)) (by
    sig_implies [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Spec.Cast5.cbcChainedSig,
      Proof.Cast5.cbcChainedPre, Proof.Cast5.cbcDecChainedPost, cbcDecX, modePre, modePub, AArch64.abi,
      AArch64.argRegs, Curry.withScratch, Curry.app] [modeSat] using modeSat)

theorem cfbDecrypt_verified :
    Verified AArch64.target cfbDecrypt
      (Proof.Cast5.modeScratchContract AArch64.abi Spec.Cast5.cfbSig 28
        (Spec.Cast5.cfbPre AArch64.abi.ptrBits) (Proof.Cast5.cfbDecPost AArch64.abi.ptrBits)) :=
  Verified.of_correct (k := cfbDecX) (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs (rs := [.x30]) (cfbDecrypt_wp hs) (by lit_decide)
        (by lit_decide)
      exact ⟨t, s', he, ⟨Proof.Modes.AArch64.preserved_of h₁ h₃, Exec.sp he,
        vKeep_of_vSafeBut cfbDecrypt_vSafe (crypt_vKeep true) _ _ _ he⟩, h₂⟩)
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5]) taint_agree
      (by taint_decide)) (by
    sig_implies [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Spec.Cast5.cfbSig,
      Spec.Cast5.ofbSig, Spec.Cast5.cfbPre, Spec.Cast5.ofbPre, Proof.Cast5.cfbDecPost, cfbDecX, modePre, modePub,
      AArch64.abi, AArch64.argRegs, Curry.withScratch, Curry.app] [modeSat] using modeSat)

/-! ## The functions with their working space on the stack -/

theorem cbcDecFrameSat_pre : ∃ s, (Proof.Cast5.cbcDecryptChainedRoundsContract AArch64.abi 224).pre s := by
  implies_sat [Proof.Cast5.cbcDecryptChainedRoundsContract, Spec.Cast5.cbcChainedSig, AArch64.abi,
    AArch64.argRegs] [modeFrameSat] using modeFrameSat

theorem cfbDecFrameSat_pre : ∃ s, (Proof.Cast5.cfbDecryptRoundsContract AArch64.abi 224).pre s := by
  implies_sat [Proof.Cast5.cfbDecryptRoundsContract, Spec.Cast5.cfbSig, Spec.Cast5.ofbSig, Spec.Cast5.cfbPre,
    Spec.Cast5.ofbPre, AArch64.abi, AArch64.argRegs] [modeFrameSat] using modeFrameSat

/-- CBC decryption with its working space on the stack. -/
theorem cbcDecryptChained_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 224 .x5 28 cbcDecryptChained)
      (Proof.Cast5.cbcDecryptChainedRoundsContract AArch64.abi 224) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Cast5.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 28) (pre := Proof.Cast5.cbcChainedPre AArch64.abi.ptrBits)
    (post := Proof.Cast5.cbcDecChainedPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 224) cbcDecryptChained_verified
    (by decide) (by decide) (by decide) (Proof.Cast5.cbcDecChainedPostOut_local _) cbcDecFrameSat_pre

/-- CFB64 decryption with its working space on the stack. -/
theorem cfbDecrypt_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 224 .x5 28 cfbDecrypt)
      (Proof.Cast5.cfbDecryptRoundsContract AArch64.abi 224) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Cast5.cfbSig) (nm := "scratch") (e := .u64)
    (n := 28) (pre := Spec.Cast5.cfbPre AArch64.abi.ptrBits)
    (post := Proof.Cast5.cfbDecPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 224) cfbDecrypt_verified
    (by decide) (by decide) (by decide) (Proof.Cast5.cfbDecPostOut_local _) cfbDecFrameSat_pre

end VG.Proof.Cast5.AArch64.Tbl
