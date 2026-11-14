module

public import VerifiedGarbage.Proof.Cast5.Rounds
public import VerifiedGarbage.Proof.Cast5.RISCV64.ModesConstantTime
public import VerifiedGarbage.Proof.Modes.RISCV64.Core
public import VerifiedGarbage.Impl.Cast5.RISCV64.Modes
public import VerifiedGarbage.Proof.Cast5.ModeCipher
public import VerifiedGarbage.Proof.Cast5.RISCV64.Block
import VerifiedGarbage.Proof.Cast5.ModeMem
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Cast5.RISCV64.EcbVerified
public import VerifiedGarbage.Spec.Cast5.Cbc
public import VerifiedGarbage.Spec.Cast5.Cfb
public import VerifiedGarbage.Spec.Cast5.Ofb
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Modes.RISCV64.Seq
public import VerifiedGarbage.Proof.Modes.Steps
public import VerifiedGarbage.Proof.Framework.RISCV64.Consts
public import VerifiedGarbage.Spec.Cast5
public import VerifiedGarbage.Spec.Cfb
public import VerifiedGarbage.Spec.Ofb
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Modes.RISCV64.Modes
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Cast5.RISCV64.ModesLit

/-! ### `Cast5.RISCV64.ModeCore`, which only this module used -/

section

/-!
# CAST5's core for the modes on RISC-V

`dirCoreSpec up n hn`: CAST5's core (`Impl.Cast5.RISCV64.dirCore up n`)
meets what the modes need of a core (`Proof.Modes.RISCV64.CoreSpec`), with
the key the subkeys, read in place through `a0`, and its cipher encryption
(`up`) or decryption with `n` rounds (`Proof.Cast5.dirCipher`), as on
PPC64LE (`Proof/Cast5/PPC64LE/ModeCore.lean`). The subkeys and the table of
S-boxes (where the static `VG_CAST5_S1234` puts it, holding the S-boxes)
are readable and apart from the regions the mode writes (`KeyArgs`), and
from the mode's frame (`Ready`), so nothing the mode or the core writes
changes them. The core runs ECB's block function on its buffer, slot 6
(`crypt_wp`), with the mode's `s1`–`s4` in `a3`, `a4`, `s11` and `ra`, our
caller's `s0`, `s5`–`s11` and `ra` in slots 7 to 15, and the buffer's and
the table's addresses and `n` in the registers the block function reads.
-/

@[expose] public section

namespace VG.Proof.Cast5.RISCV64.Mode

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Cast5.RISCV64
open VG.Impl.Cast5 (s1234Sym s1234)
open VG.Impl.Modes.RISCV64 (sb coreSlot)
open VG.Proof.Cast5 (Held dirCipher dirCipher_length ofFn_bytesAt scheduleAt_frame held_frame)
open VG.Proof.Modes.RISCV64 (coreRegion blkRegion blkAddr slotA CoreSpec Layout ScrIn kept KeptBut)

/-- The subkeys. -/
abbrev keyR (s : State) : Region := ⟨s.gpr .a0, 128⟩

/-- The table of S-boxes. -/
abbrev tblR (s : State) : Region := ⟨s.syms s1234Sym, 4096⟩

/-- The subkeys at `a0` are `k`, and they and the table are readable, within
the address space and apart from the regions `rs`; the table is 64-byte
aligned and holds the S-boxes. -/
structure KeyArgs (s : State) (rs : List Region) (k : Spec.Cast5.Schedule) : Prop where
  sched : Spec.Cast5.scheduleAt s.mem (s.gpr .a0) = k
  key : keyR s ∈ s.rd ++ s.wr
  kfit : (s.gpr .a0).toNat + 128 ≤ 2 ^ 64
  keyOut : ∀ r ∈ rs, (keyR s).Disjoint r
  tbl : tblR s ∈ s.rd ++ s.wr
  tal : (s.syms s1234Sym).toNat % 64 = 0
  held : Held s.mem (s.syms s1234Sym) s1234
  tblOut : ∀ r ∈ rs, (tblR s).Disjoint r

/-- The key's arguments, apart from the mode's frame at `B` too. -/
structure Ready (s : State) (B : Addr) (ws : List Region) (k : Spec.Cast5.Schedule) : Prop where
  args : KeyArgs s ws k
  keyScr : (keyR s).Disjoint ⟨B, 8 * 16⟩
  tblScr : (tblR s).Disjoint ⟨B, 8 * 16⟩

theorem mem_extend {rs ws xs : List Region} {r : Region} (h : r ∈ rs ++ xs) : r ∈ rs ++ (ws ++ xs) := by
  rcases List.mem_append.mp h with h | h
  · exact List.mem_append_left _ h
  · exact List.mem_append_right _ (List.mem_append_right _ h)

/-- `KeyArgs` survives what keeps `a0`, the readable regions and the
statics, extends the writable ones, and writes memory apart from the subkeys
and the table. -/
theorem KeyArgs.congr {s s' : State} {rs : List Region} {k : Spec.Cast5.Schedule} (h : KeyArgs s rs k)
    (e : s'.gpr .a0 = s.gpr .a0) (hrd : s'.rd = s.rd) (hwr : ∃ ws, s'.wr = ws ++ s.wr)
    (hsy : s'.syms = s.syms) {fs : List Region} (hf : Frame fs s.mem s'.mem)
    (hk : ∀ r ∈ fs, (keyR s).Disjoint r) (ht : ∀ r ∈ fs, (tblR s).Disjoint r) : KeyArgs s' rs k := by
  obtain ⟨ws, hw⟩ := hwr
  exact
    { sched := by rw [e, scheduleAt_frame hf hk, h.sched]
      key := by rw [hrd, hw, keyR, e]; exact mem_extend h.key
      kfit := by rw [e]; exact h.kfit
      keyOut := by rw [keyR, e]; exact h.keyOut
      tbl := by rw [hrd, hw, tblR, hsy]; exact mem_extend h.tbl
      tal := by rw [hsy]; exact h.tal
      held := by rw [hsy]; exact Proof.Cast5.held_frame h.held hf ht
      tblOut := by rw [tblR, hsy]; exact h.tblOut }

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Spec.Cast5.Schedule} (h : KeyArgs s rs k)
    (e : KeptBut s s') (hrd : s'.rd = s.rd) (hwr : ∃ ws, s'.wr = ws ++ s.wr) (hsy : s'.syms = s.syms)
    (hf : Frame rs s.mem s'.mem) : KeyArgs s' rs k :=
  h.congr e.a0 hrd hwr hsy hf h.keyOut h.tblOut

theorem ready_frame {s s' : State} {B : Addr} {ws : List Region} {k : Spec.Cast5.Schedule}
    {rs : List Region} (h : Ready s B ws k) (e : KeptBut s s') (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsy : s'.syms = s.syms) (hf : Frame rs s.mem s'.mem) (hs : ∀ r ∈ rs, ∃ r' ∈ ws, Region.Sub r r') :
    Ready s' B ws k := by
  have hk : ∀ r ∈ rs, (keyR s).Disjoint r := fun r hr => by
    obtain ⟨r', hr', hsub⟩ := hs r hr
    exact (h.args.keyOut r' hr').sub_right hsub
  have ht : ∀ r ∈ rs, (tblR s).Disjoint r := fun r hr => by
    obtain ⟨r', hr', hsub⟩ := hs r hr
    exact (h.args.tblOut r' hr').sub_right hsub
  refine ⟨h.args.congr e.a0 hrd ⟨[], by rw [hwr]; rfl⟩ hsy hf hk ht, by rw [keyR, e.a0]; exact h.keyScr,
    by rw [tblR, hsy]; exact h.tblScr⟩

theorem layout (up : Bool) (n : Nat) : Layout (dirCore up n) :=
  ⟨Nat.one_pos, .inl rfl, show 6 ≤ 6 by decide, show 8 * 6 + 4 * 2 * 1 ≤ 8 * 16 by decide,
    show 8 * 6 + 4 * 2 * 1 ≤ 2032 by decide, show 16 % 2 = 0 by decide, show 16 < 2048 by decide⟩

theorem prepare_wp (up : Bool) (n : Nat) {s : State} {B : Addr} {rs : List Region} {k : Spec.Cast5.Schedule}
    (hB : s.gpr sb = B) (_hS : ScrIn s B (dirCore up n).total)
    (hm : (⟨B, 8 * (dirCore up n).total⟩ : Region) ∈ rs) (hk : KeyArgs s rs k) :
    WP isa (dirCore up n).prepare s fun s' => Ready s' B rs k ∧ s'.gpr sb = B ∧
      (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ Frame [coreRegion (dirCore up n) B] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr :=
  WP.block_nil ⟨⟨hk, hk.keyOut _ hm, hk.tblOut _ hm⟩, hB, fun _ _ => rfl, Frame.refl _ _, rfl, rfl⟩

/-! ## The core's code -/

theorem modeSaved_fits : Spill.Fits modeSaved := by decide
theorem modeSaved_ok : ∀ p ∈ modeSaved, p.2 % 8 = 0 ∧ p.2 < 2048 := modeSaved_fits.1
theorem modeSaved_lt : ∀ p ∈ modeSaved, 56 ≤ p.2 ∧ p.2 + 8 ≤ 56 + 72 := by decide
theorem modeSaved_restorable : Spill.Restorable sb modeSaved := by decide

/-- The registers the core writes before the block function. -/
def setRegs : List Reg := [dat, .a3, .a4, .s11, .ra, tbl, rnd]

/-- Of the registers the caller expects kept, those the core neither saves
nor parks the mode's in are none it writes. -/
theorem kept_rest : ∀ r ∈ kept, r ∉ modeSaved.map Prod.fst → r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → r ≠ .s4 →
    r ∉ roundRegs ∧ r ∉ setRegs := by decide

theorem modeCrypt_eq (up : Bool) (n : Nat) : modeCrypt up n =
    .seq (.block (Spill.saveCode sb modeSaved ++
      ([.addi dat sb 48, mov .a3 .s1, mov .a4 .s2, mov .s11 .s3, mov .ra .s4, .lla tbl s1234Sym, .li rnd n] :
        List Instr)))
      (.seq (crypt up dat)
        (.block (([mov .s1 .a3, mov .s2 .a4, mov .s3 .s11, mov .s4 .ra] : List Instr) ++
          Spill.restoreCode sb modeSaved))) := rfl

/-- The block cipher as the modes see it: the cipher of the block's bytes. -/
theorem dirCipher_bytes (up : Bool) (k : Spec.Cast5.Schedule) (n : Nat) (m : Mem) (p : Addr) :
    dirCipher up k n (Spec.Aes.bytesAt m p 8) = (cipher up k n (Spec.Cast5.blockAt m p)).toList := by
  cases up <;> simp only [dirCipher, cipher, Spec.Cast5.cipher, Spec.Cast5.invCipher, ofFn_bytesAt,
    Bool.false_eq_true, ite_true, ite_false]

/-- The bytes at `p`, apart from what a frame writes, are unchanged. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 8⟩ r) : Spec.Aes.bytesAt m' p 8 = Spec.Aes.bytesAt m p 8 := by
  simp only [Spec.Aes.bytesAt]
  exact List.map_congr_left fun i hi =>
    hf.bytes (R := ⟨p, 8⟩) hd (by show (8 : Nat) ≤ 2 ^ 64; decide) (List.mem_range.mp hi)

theorem crypt_wp (up : Bool) {n : Nat} (hn : n = 12 ∨ n = 16) {s : State} {B : Addr} {ws : List Region}
    {k : Spec.Cast5.Schedule} (hB : s.gpr sb = B) (hS : ScrIn s B (dirCore up n).total)
    (hR : Ready s B ws k) :
    WP isa (dirCore up n).crypt s fun s' => s'.gpr sb = B ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      Ready s' B ws k ∧ Frame [coreRegion (dirCore up n) B] s.mem s'.mem ∧
      (∀ j < (dirCore up n).G, Spec.Aes.bytesAt s'.mem (blkAddr (dirCore up n) B j) (4 * (dirCore up n).bw) =
        dirCipher up k n (Spec.Aes.bytesAt s.mem (blkAddr (dirCore up n) B j) (4 * (dirCore up n).bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hfit : B.toNat + 128 ≤ 2 ^ 64 := hS.fit
  have hW : (⟨B, 128⟩ : Region) ∈ s.wr := hS.whole (by show 8 * 16 ≤ 4064; decide)
  have hal : B.toNat % 8 = 0 := by have := hS.al; omega_arith
  obtain ⟨hk, hkB, htB⟩ := hR
  have hn11 : n < 2048 := by rcases hn with rfl | rfl <;> decide
  refine WP.of_syms ?_
  show WP isa (modeCrypt up n) s _
  rw [modeCrypt_eq]
  -- Our caller's registers to their slots.
  refine WP.seq (Spill.save_ok (b := sb) (by rw [hB]; exact hal) modeSaved_ok (fun p hp => by
    have := modeSaved_lt p hp
    exact ⟨_, hW, by rw [hB]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩) ?_)
  rw [hB]
  generalize hM : Spill.saveMem s.mem B s.gpr modeSaved = M
  have sv : Spill.Saved B s.gpr modeSaved M := by rw [← hM]; exact Spill.saveMem_saved modeSaved_fits _ _ _
  have fM : Frame [⟨B + BitVec.ofNat 64 56, 72⟩] s.mem M := by
    rw [← hM]; exact Spill.saveMem_frame modeSaved_lt (by decide) _ _ _
  -- The buffer's address, the mode's registers parked, the table's address and the rounds.
  refine WP.cons (exec_addi (by decide)) (WP.cons (exec_addi (by decide)) (WP.cons (exec_addi (by decide))
    (WP.cons (exec_addi (by decide)) (WP.cons (exec_addi (by decide)) (WP.cons exec_lla
    (WP.cons (exec_li (by unfold imm12; omega_arith)) (WP.block_nil ?_)))))))
  generalize hs₇ : State.write _ rnd _ = s₇
  have g₇ : ∀ r, r ∉ setRegs → s₇.gpr r = s.gpr r := fun r hr => by
    simp only [setRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [← hs₇]; simp [State.write, hr]
  have m₇ : s₇.mem = M := by rw [← hs₇]; rfl
  have rd₇ : s₇.rd = s.rd := by rw [← hs₇]; rfl
  have wr₇ : s₇.wr = s.wr := by rw [← hs₇]; rfl
  have sy₇ : s₇.syms = s.syms := by rw [← hs₇]; rfl
  have b₇ : s₇.gpr sb = B := by rw [g₇ _ (by decide), hB]
  have a2₇ : s₇.gpr dat = B + BitVec.ofNat 64 48 := by
    have hB' : s.gpr .s4 = B := hB
    rw [← hs₇]; simp [State.write, sb, hB']
  have t₇ : s₇.gpr tbl = s.syms s1234Sym := by rw [← hs₇]; simp [State.write]
  have n₇ : s₇.gpr rnd = BitVec.ofNat 64 n := by rw [← hs₇]; simp [State.write]
  have pk₇ : s₇.gpr .a3 = s.gpr .s1 ∧ s₇.gpr .a4 = s.gpr .s2 ∧ s₇.gpr .s11 = s.gpr .s3 ∧
      s₇.gpr .ra = s.gpr .s4 := by
    rw [← hs₇]; simp [State.write]
  clear hs₇
  have a0₇ : s₇.gpr .a0 = s.gpr .a0 := g₇ _ (by decide)
  -- Nothing the saves wrote is the subkeys, the table or the block.
  have hkM : ∀ r ∈ [(⟨B + BitVec.ofNat 64 56, 72⟩ : Region)], (keyR s).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hkB.sub_right (Offset.sub_base _ (by decide))
  have htM : ∀ r ∈ [(⟨B + BitVec.ofNat 64 56, 72⟩ : Region)], (tblR s).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact htB.sub_right (Offset.sub_base _ (by decide))
  have pre : BPre s₇ dat (B + BitVec.ofNat 64 48) (s.gpr .a0) n :=
    { ptr := a2₇
      prOk := by decide
      sched := a0₇
      rounds := n₇
      nv := hn
      trd := by rw [t₇, rd₇, wr₇]; exact hk.tbl
      tal := by rw [t₇]; exact hk.tal
      held := by rw [t₇, m₇]; exact Proof.Cast5.held_frame hk.held fM htM
      inP := ⟨_, by rw [wr₇]; exact hW, Offset.contains_base _ (by decide) (by omega_arith)⟩
      inK := by rw [rd₇, wr₇]; exact hk.key
      kfit := hk.kfit }
  -- The block function.
  refine WP.seq (WP.mono (crypt_ok pre up) fun v hv => ?_)
  have gv : ∀ r, r ∉ roundRegs → v.gpr r = s₇.gpr r := fun r hr => hv.keep.gpr hr
  have svv : Spill.Saved B s.gpr modeSaved v.mem := by
    rw [← m₇] at sv
    exact sv.frame hv.frame fun p hp r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inr (by have := modeSaved_lt p hp; omega_arith))
        (by have := modeSaved_lt p hp; omega_arith) (by omega_arith)
  -- The mode's registers back, then our caller's.
  refine wp_mv fun x₁ e₁ => wp_mv fun x₂ e₂ => wp_mv fun x₃ e₃ => wp_mv fun x₄ e₄ => ?_
  have gx : ∀ r, r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → r ≠ .s4 → x₄.gpr r = v.gpr r := fun r h1 h2 h3 h4 => by
    rw [e₄.other r h4, e₃.other r h3, e₂.other r h2, e₁.other r h1]
  have px : x₄.gpr .s1 = s.gpr .s1 ∧ x₄.gpr .s2 = s.gpr .s2 ∧ x₄.gpr .s3 = s.gpr .s3 ∧
      x₄.gpr .s4 = s.gpr .s4 := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [e₄.other _ (by decide), e₃.other _ (by decide), e₂.other _ (by decide), e₁.gpr, gv _ (by decide),
        pk₇.1]
    · rw [e₄.other _ (by decide), e₃.other _ (by decide), e₂.gpr, e₁.other _ (by decide), gv _ (by decide),
        pk₇.2.1]
    · rw [e₄.other _ (by decide), e₃.gpr, e₂.other _ (by decide), e₁.other _ (by decide), gv _ (by decide),
        pk₇.2.2.1]
    · rw [e₄.gpr, e₃.other _ (by decide), e₂.other _ (by decide), e₁.other _ (by decide), gv _ (by decide),
        pk₇.2.2.2]
  have bx : x₄.gpr sb = B := px.2.2.2.trans hB
  have mx : x₄.mem = v.mem := by rw [e₄.mem, e₃.mem, e₂.mem, e₁.mem]
  have rdx : x₄.rd = s.rd := by rw [e₄.rd, e₃.rd, e₂.rd, e₁.rd, hv.keep.2.1, rd₇]
  have wrx : x₄.wr = s.wr := by rw [e₄.wr, e₃.wr, e₂.wr, e₁.wr, hv.keep.2.2, wr₇]
  rw [← List.append_nil (Spill.restoreCode sb modeSaved)]
  refine Spill.restore_ok (b := sb) hal bx modeSaved_ok modeSaved_restorable (fun p hp => by
    have := modeSaved_lt p hp
    exact ⟨_, by rw [rdx, wrx]; exact List.mem_append_right _ hW,
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩) (by rw [mx]; exact svv) fun w R => ?_
  refine WP.block_nil fun syF => ?_
  -- The memory: the saves and the block.
  have memF : w.mem = v.mem := by rw [R.mem, mx]
  have fF : Frame [⟨B + BitVec.ofNat 64 48, 80⟩] s.mem w.mem := by
    rw [memF]
    refine (fM.sub fun r hr => ?_).trans ((m₇ ▸ hv.frame).sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
  have rdF : w.rd = s.rd := by rw [R.rd, rdx]
  have wrF : w.wr = s.wr := by rw [R.wr, wrx]
  have a0F : w.gpr .a0 = s.gpr .a0 := by
    rw [R.other _ (by decide), gx _ (by decide) (by decide) (by decide) (by decide), gv _ (by decide), a0₇]
  have hkF : ∀ r ∈ [(⟨B + BitVec.ofNat 64 48, 80⟩ : Region)], (keyR s).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hkB.sub_right (Offset.sub_base _ (by decide))
  have htF : ∀ r ∈ [(⟨B + BitVec.ofNat 64 48, 80⟩ : Region)], (tblR s).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact htB.sub_right (Offset.sub_base _ (by decide))
  refine ⟨?_, fun r hr => ?_, ⟨hk.congr a0F rdF ⟨[], by rw [wrF]; rfl⟩ syF fF hkF htF,
    by rw [keyR, a0F]; exact hkB, by rw [tblR, syF]; exact htB⟩, fF, fun j hj => ?_, rdF, wrF⟩
  · rw [R.other _ (by decide), bx]
  · -- The registers the caller expects kept.
    by_cases hs : r ∈ modeSaved.map Prod.fst
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hs
      exact R.gpr p hp
    rw [R.other r hs]
    by_cases h1 : r = .s1
    · subst h1; exact px.1
    by_cases h2 : r = .s2
    · subst h2; exact px.2.1
    by_cases h3 : r = .s3
    · subst h3; exact px.2.2.1
    by_cases h4 : r = .s4
    · subst h4; exact px.2.2.2
    obtain ⟨hr1, hr2⟩ := kept_rest r hr hs h1 h2 h3 h4
    rw [gx r h1 h2 h3 h4, gv r hr1, g₇ r hr2]
  · -- The block.
    obtain rfl : j = 0 := by have : j < 1 := hj; omega_using [this]
    have ea : blkAddr (dirCore up n) B 0 = B + BitVec.ofNat 64 48 := by
      simp [blkAddr, slotA, dirCore, bufSlot]
    have hb : Spec.Aes.bytesAt M (B + BitVec.ofNat 64 48) 8 = Spec.Aes.bytesAt s.mem (B + BitVec.ofNat 64 48) 8 :=
      bytesAt_frame fM fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inl (by decide)) (by decide) (by omega_arith)
    have hkk : Spec.Cast5.scheduleAt M (s.gpr .a0) = k := by rw [scheduleAt_frame fM hkM, hk.sched]
    rw [ea, show 4 * (dirCore up n).bw = 8 from rfl, memF, Proof.Cast5.bytesAt_eq, hv.blk, m₇, dirCipher_bytes, hkk,
      ← ofFn_bytesAt M (B + BitVec.ofNat 64 48), hb, ofFn_bytesAt]

/-- CAST5's core with `n` rounds, in the direction `up`, meets what the modes need. -/
def dirCoreSpec (up : Bool) (n : Nat) (hn : n = 12 ∨ n = 16) : CoreSpec (dirCore up n) where
  Key := Spec.Cast5.Schedule
  cipher k := dirCipher up k n
  KeyArgs := KeyArgs
  Ready := Ready
  cipher_len k b := dirCipher_length up k n b
  layout := layout up n
  keyArgs_congr h e r w y f := keyArgs_congr h e r w y f
  ready_frame h e r w y f hs _ := ready_frame h e r w y f hs
  prepare_wp := prepare_wp up n
  crypt_wp := crypt_wp up hn

end VG.Proof.Cast5.RISCV64.Mode

end

end


/-!
# CAST5's modes on RISC-V meet their contracts

`modeFn m` moves the arguments to the modes' registers and runs `m n` for
the count of rounds `n` (`modeFn_wp`), and each `m n` is a mode of
`Proof/Modes/RISCV64/` over CAST5's core with `n` rounds
(`Mode.dirCoreSpec`), as on PPC64LE (`Proof/Cast5/PPC64LE/ModesVerified.lean`).
`cbcEncryptChained_verified`, `ofb_verified`, …: each meets the shared
contract with `stack := 128` (the mode's frame of 16 slots below the stack
pointer, which it zeroes before returning), under the calling convention
with the table (`abi.withConsts ecbConsts`). The proof's contract (`modePC`)
is `modeP` for the state without the table's region, with what the contract
says of the table (`ConstsOk`).
-/

@[expose] public section

namespace VG.Proof.Cast5.RISCV64.Modes

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Cast5.RISCV64 VG.Impl.Modes
open VG.Impl.Cast5 (s1234Sym s1234 ecbConsts)
open VG.Proof.Modes.RISCV64 (SeqPre)
open VG.Proof.Cast5.RISCV64.Mode (dirCoreSpec KeyArgs layout)
open VG.Proof.Cast5.RISCV64 (modePub s1234_len ecbSatMem ecbSatMem_held ecbConsts_eq)

/-- The frame's bytes. -/
abbrev frameBytes : Nat := 128

/-! ## The arguments -/

/-- The subkeys on entry. -/
abbrev keyOf (s : State) : Spec.Cast5.Schedule := Spec.Cast5.scheduleAt s.mem (s.gpr .a0)
/-- The count of rounds. -/
abbrev rounds (s : State) : Nat := (s.gpr .a1).toNat
/-- The chaining value. -/
abbrev ivAt (m : Mem) (s : State) : List Byte := Spec.Aes.bytesAt m (s.gpr .a2) 8
/-- The data, in blocks. -/
abbrev dataAt (m : Mem) (s : State) : List (List Byte) := Spec.Cast5.cbcBlocksAt m (s.gpr .a3) (s.gpr .a4).toNat

/-- The state after `modeFn`'s moves, from `s`: the arguments in the modes'
registers, and nothing else the caller sees changed. -/
structure Shifted (s s₁ : State) : Prop where
  a0 : s₁.gpr .a0 = s.gpr .a0
  a1 : s₁.gpr .a1 = s.gpr .a2
  a2 : s₁.gpr .a2 = s.gpr .a3
  a3 : s₁.gpr .a3 = s.gpr .a4
  other : ∀ r ∈ preserved, s₁.gpr r = s.gpr r
  ra : s₁.gpr .ra = s.gpr .ra
  mem : s₁.mem = s.mem
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr
  sp : s₁.sp = s.sp
  syms : s₁.syms = s.syms

theorem Shifted.abi {s s₁ s' : State} (h : Shifted s s₁) (ha : abiPreserved s₁ s') : abiPreserved s s' :=
  ⟨fun r hr => (ha.1 r hr).trans (h.other r hr), ha.2.1.trans h.sp, ha.2.2.trans h.ra⟩

/-- `modeFn m` runs `m` with the count of rounds, from the state with the
arguments moved. -/
theorem modeFn_wp {m : Nat → Prog isa} {s : State} {Q : State → Prop} (hn : rounds s = 12 ∨ rounds s = 16)
    (h : ∀ s₁, Shifted s s₁ → WP isa (m (rounds s)) s₁ Q) : WP isa (modeFn m) s Q := by
  unfold modeFn
  refine WP.seq (WP.cons (exec_addi (by decide)) (WP.cons (exec_addi (by decide)) (WP.cons (exec_addi (by decide))
    (WP.cons (exec_addi (by decide)) (WP.cons (exec_addi (by decide)) (WP.block_nil ?_))))))
  generalize hs₁ : State.write _ _ _ = s₁
  have sh : Shifted s s₁ := by
    subst hs₁
    refine ⟨?_, ?_, ?_, ?_, fun r hr => ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
    · simp [State.write]
    · simp [State.write]
    · simp [State.write]
    · simp [State.write]
    · have h1 : r ≠ .a1 := by rintro rfl; simp [preserved] at hr
      have h2 : r ≠ .a2 := by rintro rfl; simp [preserved] at hr
      have h3 : r ≠ .a3 := by rintro rfl; simp [preserved] at hr
      have h0 : r ≠ .t0 := by rintro rfl; simp [preserved] at hr
      simp [State.write, h1, h2, h3, h0]
    · simp [State.write]
  have t0 : s₁.gpr .t0 = s.gpr .a1 + BitVec.ofInt 64 0 + BitVec.ofInt 64 (-12) := by
    subst hs₁; simp only [State.write]; simp
  have e1 : s.gpr .a1 = BitVec.ofNat 64 (rounds s) := by simp only [rounds, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rcases hn with hn | hn
  · refine WP.ite true (by rw [eval_zero, t0, e1, hn]; decide) (fun _ => ?_) (fun h => absurd h (by decide))
    exact hn ▸ h s₁ sh
  · refine WP.ite false (by rw [eval_zero, t0, e1, hn]; decide) (fun h => absurd h (by decide)) (fun _ => ?_)
    exact hn ▸ h s₁ sh

/-! ## The modes' contract, as the proof states it -/

/-- The modes' public arguments, without the table's address. -/
def argPub (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4

/-- A mode's function on RISC-V, with its frame below the stack pointer,
and the postcondition `post`. -/
def modeP (post : State → State → Prop) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .a0, 128⟩
    let iv : Region := ⟨s.gpr .a2, 8⟩
    let data : Region := ⟨s.gpr .a3, 8 * (s.gpr .a4).toNat⟩
    let stack : Region := ⟨s.sp - frameBytes, frameBytes⟩
    s.rd = [key] ∧ s.wr = [iv, data] ∧
      key.Disjoint iv ∧ key.Disjoint data ∧ iv.Disjoint data ∧
      (s.gpr .a0).toNat + 128 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 8 ≤ 2 ^ 64 ∧
      (s.gpr .a3).toNat + 8 * (s.gpr .a4).toNat ≤ 2 ^ 64 ∧
      s.sp.toNat % 16 = 0 ∧ frameBytes ≤ s.sp.toNat ∧ stack.Disjoint key ∧ stack.Disjoint iv ∧
      stack.Disjoint data ∧ ((s.gpr .a1).toNat = 12 ∨ (s.gpr .a1).toNat = 16)
  post := post
  pub := argPub

/-- `modeP`, with the table. -/
def modePC (post : State → State → Prop) : Contract isa where
  pre s := (modeP post).pre (stripConsts ecbConsts s) ∧ ConstsOk ecbConsts frameBytes s
  post := post
  pub := modePub

/-- The functions' postconditions. -/
def cbcEncPost (s s' : State) : Prop :=
  let cs := Spec.Cbc.encrypt (Spec.Cast5.cipher (keyOf s) (rounds s)) (ivAt s.mem s) (dataAt s.mem s)
  dataAt s'.mem s = cs ∧ ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) cs
def cbcDecPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cbc.decrypt (Spec.Cast5.invCipher (keyOf s) (rounds s)) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (dataAt s.mem s)
def ofbPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Ofb.crypt (Spec.Cast5.cipher (keyOf s) (rounds s)) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Ofb.next (Spec.Cast5.cipher (keyOf s) (rounds s)) (ivAt s.mem s) (s.gpr .a4).toNat
def cfbEncPost (s s' : State) : Prop :=
  let cs := Spec.Cfb.encrypt (Spec.Cast5.cipher (keyOf s) (rounds s)) (ivAt s.mem s) (dataAt s.mem s)
  dataAt s'.mem s = cs ∧ ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) cs
def cfbDecPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cfb.decrypt (Spec.Cast5.cipher (keyOf s) (rounds s)) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (dataAt s.mem s)

section
variable {post : State → State → Prop} {s s₁ : State} (hs : (modePC post).pre s) (h₁ : Shifted s s₁)
include hs

theorem rounds_of : rounds s = 12 ∨ rounds s = 16 := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hn⟩, -⟩ := hs
  exact hn

include h₁

/-- `modePC`'s precondition gives the modes'. -/
theorem seqPre_of (up : Bool) {n : Nat} {M : Mode} (hstep : M.step = 8) :
    SeqPre (dirCore up n) M s₁ := by
  obtain ⟨⟨-, hwr, -, -, dVD, -, fV, fD, al, sp, -, dSV, dSD, -⟩, -⟩ := hs
  simp only [stripConsts_gpr, stripConsts_wr, stripConsts_sp] at hwr dVD fV fD al sp dSV dSD
  have eS : Proof.Modes.RISCV64.scrRegion (dirCore up n) (Proof.Modes.RISCV64.Fb s₁ (dirCore up n)) =
      ⟨s.sp - frameBytes, frameBytes⟩ := by
    simp only [Proof.Modes.RISCV64.scrRegion, Proof.Modes.RISCV64.Fb, h₁.sp]; rfl
  have eV : Proof.Modes.RISCV64.ivR s₁ (dirCore up n) = ⟨s.gpr .a2, 8⟩ := by
    simp only [Proof.Modes.RISCV64.ivR, Proof.Modes.RISCV64.P, h₁.a1]; rfl
  have eD : Proof.Modes.RISCV64.dataRegion (Proof.Modes.RISCV64.Dp s₁) M.step (Proof.Modes.RISCV64.N s₁) =
      ⟨s.gpr .a3, 8 * (s.gpr .a4).toNat⟩ := by
    simp only [Proof.Modes.RISCV64.dataRegion, Proof.Modes.RISCV64.Dp, Proof.Modes.RISCV64.N, h₁.a2, h₁.a3, hstep]
  have hwr₁ : s₁.wr = [⟨s.gpr .a2, 8⟩, ⟨s.gpr .a3, 8 * (s.gpr .a4).toNat⟩] := by rw [h₁.wr, hwr]
  refine ⟨by rw [h₁.sp]; exact al, by rw [h₁.sp]; exact sp, by rw [eV, hwr₁]; simp,
    fun _ => by rw [eV, hwr₁]; simp,
    by simp only [Proof.Modes.RISCV64.P, h₁.a1]; exact fV, by rw [eD, hwr₁]; simp,
    by simp only [Proof.Modes.RISCV64.Dp, Proof.Modes.RISCV64.N, h₁.a2, h₁.a3, hstep]; exact fD,
    by rw [eD, eS]; exact dSD.symm, by rw [eV, eS]; exact dSV.symm, fun _ => by rw [eV, eD]; exact dVD,
    ⟨by omega_using [hstep], by rw [hstep]; rfl⟩, layout up n⟩

/-- `modePC`'s precondition gives the key's arguments. -/
theorem keyArgs_of (up : Bool) {n : Nat} {M : Mode} (hstep : M.step = 8) :
    KeyArgs s₁ (Proof.Modes.RISCV64.wrs0 (dirCore up n) M s₁) (keyOf s) := by
  obtain ⟨⟨hrd, hwr, -, dKD, -, fK, -, -, -, -, dSK, -, -, -⟩, hk⟩ := hs
  simp only [stripConsts_gpr, stripConsts_wr, stripConsts_sp] at hrd hwr dKD fK dSK
  have trd : (⟨s.syms s1234Sym, 4096⟩ : Region) ∈ s.rd := s1234_len ▸ ConstsOk.rd1 hk
  have twr : ∀ r ∈ s.wr, Region.Disjoint ⟨s.syms s1234Sym, 4096⟩ r := s1234_len ▸ ConstsOk.wr1 hk
  have tst : Region.Disjoint ⟨s.syms s1234Sym, 4096⟩ ⟨s.sp - frameBytes, frameBytes⟩ := by
    have := (hk.2.2.1 _ List.mem_cons_self).2.2 ⟨s.sp - BitVec.ofNat 64 frameBytes, frameBytes⟩ (by
      simp [abi, stackBelow])
    simp only [s1234_len] at this; exact this
  have ews : Proof.Modes.RISCV64.wrs0 (dirCore up n) M s₁ =
      [⟨s.gpr .a3, 8 * (s.gpr .a4).toNat⟩, ⟨s.sp - frameBytes, frameBytes⟩] := by
    simp only [Proof.Modes.RISCV64.wrs0, Proof.Modes.RISCV64.wrs, Proof.Modes.RISCV64.dataRegion,
      Proof.Modes.RISCV64.scrRegion, Proof.Modes.RISCV64.Dp, Proof.Modes.RISCV64.N, Proof.Modes.RISCV64.Fb,
      h₁.a2, h₁.a3, h₁.sp, hstep]
    rfl
  refine ⟨by rw [h₁.mem, h₁.a0], ?_, by rw [h₁.a0]; exact fK, fun r hr => ?_, ?_, ?_, ?_, fun r hr => ?_⟩
  · rw [h₁.rd, h₁.wr, Mode.keyR, h₁.a0]
    exact List.mem_append_left _ (stripConsts_rd_mem (by rw [hrd]; simp))
  · rw [ews] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [Mode.keyR, h₁.a0]; exact dKD
    · rw [Mode.keyR, h₁.a0]; exact dSK.symm
  · rw [h₁.rd, h₁.wr, Mode.tblR, h₁.syms]; exact List.mem_append_left _ trd
  · rw [h₁.syms]; exact ConstsOk.aligned hk List.mem_cons_self
  · rw [h₁.mem, h₁.syms]; exact ConstsOk.held1 hk
  · rw [ews] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [Mode.tblR, h₁.syms]; exact twr _ (by rw [hwr]; simp)
    · rw [Mode.tblR, h₁.syms]; exact tst

end

/-- A mode's result from the modes' proof, in the functions' terms. -/
theorem post_eq {s s₁ : State} (h₁ : Shifted s s₁) {m : Mem} :
    Proof.Modes.chunksAt 8 m (Proof.Modes.RISCV64.Dp s₁) (Proof.Modes.RISCV64.N s₁) = dataAt m s ∧
      Spec.Aes.bytesAt m (Proof.Modes.RISCV64.P s₁) 8 = ivAt m s ∧
      Proof.Modes.RISCV64.N s₁ = (s.gpr .a4).toNat := by
  refine ⟨?_, by simp only [Proof.Modes.RISCV64.P, h₁.a1, ivAt], by simp only [Proof.Modes.RISCV64.N, h₁.a3]⟩
  rw [dataAt, Proof.Cast5.cbcBlocksAt_eq]
  simp only [Proof.Modes.RISCV64.Dp, Proof.Modes.RISCV64.N, h₁.a2, h₁.a3]

/-! ## Correctness -/

theorem cbcEncryptChained_correct (s : State) (hs : (modePC cbcEncPost).pre s) :
    ∃ t s', Exec isa cbcEncryptChained s t s' ∧ abiPreserved s s' ∧ cbcEncPost s s' := by
  refine modeFn_wp (rounds_of hs) fun s₁ h₁ => WP.mono (Proof.Modes.RISCV64.cbcEncChained_wp
    (dirCoreSpec true _ (rounds_of hs)) (seqPre_of hs h₁ true (M := Mode.cbcEncChained 2) rfl)
    (keyArgs_of hs h₁ true (M := Mode.cbcEncChained 2) rfl)) fun s' ⟨h1, h2, h3⟩ => ⟨h₁.abi h1, ?_⟩
  obtain ⟨d0, i0, -⟩ := post_eq h₁ (m := s₁.mem)
  obtain ⟨d', i', -⟩ := post_eq h₁ (m := s'.mem)
  simp only [dirCore, dirCoreSpec, Proof.Cast5.dirCipher, Proof.Modes.RISCV64.iv0, Proof.Modes.RISCV64.blocks0,
    ↓reduceIte] at h2 h3
  rw [d', d0, i0, h₁.mem] at h2
  rw [i', d0, i0, h₁.mem] at h3
  exact ⟨h2, h3⟩

theorem cbcDecryptChained_correct (s : State) (hs : (modePC cbcDecPost).pre s) :
    ∃ t s', Exec isa cbcDecryptChained s t s' ∧ abiPreserved s s' ∧ cbcDecPost s s' := by
  refine modeFn_wp (rounds_of hs) fun s₁ h₁ => WP.mono (Proof.Modes.RISCV64.cbcDecChained_wp
    (dirCoreSpec false _ (rounds_of hs)) (seqPre_of hs h₁ false (M := Mode.cbcDecChained 2) rfl)
    (keyArgs_of hs h₁ false (M := Mode.cbcDecChained 2) rfl)) fun s' ⟨h1, h2, h3⟩ => ⟨h₁.abi h1, ?_⟩
  obtain ⟨d0, i0, -⟩ := post_eq h₁ (m := s₁.mem)
  obtain ⟨d', i', -⟩ := post_eq h₁ (m := s'.mem)
  simp only [dirCore, dirCoreSpec, Proof.Cast5.dirCipher, Proof.Modes.RISCV64.iv0, Proof.Modes.RISCV64.blocks0,
    Bool.false_eq_true, ↓reduceIte] at h2 h3
  rw [d', d0, i0, h₁.mem] at h2
  rw [i', d0, i0, h₁.mem] at h3
  exact ⟨h2, h3⟩

theorem ofb_correct (s : State) (hs : (modePC ofbPost).pre s) :
    ∃ t s', Exec isa ofb s t s' ∧ abiPreserved s s' ∧ ofbPost s s' := by
  refine modeFn_wp (rounds_of hs) fun s₁ h₁ => WP.mono (Proof.Modes.RISCV64.ofb_wp
    (dirCoreSpec true _ (rounds_of hs)) (seqPre_of hs h₁ true (M := Mode.ofb 2) rfl)
    (keyArgs_of hs h₁ true (M := Mode.ofb 2) rfl)) fun s' ⟨h1, h2, h3⟩ => ⟨h₁.abi h1, ?_⟩
  obtain ⟨d0, i0, n0⟩ := post_eq h₁ (m := s₁.mem)
  obtain ⟨d', i', -⟩ := post_eq h₁ (m := s'.mem)
  simp only [dirCore, dirCoreSpec, Proof.Cast5.dirCipher, Proof.Modes.RISCV64.iv0, Proof.Modes.RISCV64.blocks0,
    ↓reduceIte] at h2 h3
  rw [d', d0, i0, h₁.mem] at h2
  rw [i', i0, n0, h₁.mem] at h3
  exact ⟨h2, h3⟩

theorem cfbEncrypt_correct (s : State) (hs : (modePC cfbEncPost).pre s) :
    ∃ t s', Exec isa cfbEncrypt s t s' ∧ abiPreserved s s' ∧ cfbEncPost s s' := by
  refine modeFn_wp (rounds_of hs) fun s₁ h₁ => WP.mono (Proof.Modes.RISCV64.cfbEnc_wp
    (dirCoreSpec true _ (rounds_of hs)) (seqPre_of hs h₁ true (M := Mode.cfbEnc 2) rfl)
    (keyArgs_of hs h₁ true (M := Mode.cfbEnc 2) rfl)) fun s' ⟨h1, h2, h3⟩ => ⟨h₁.abi h1, ?_⟩
  obtain ⟨d0, i0, -⟩ := post_eq h₁ (m := s₁.mem)
  obtain ⟨d', i', -⟩ := post_eq h₁ (m := s'.mem)
  simp only [dirCore, dirCoreSpec, Proof.Cast5.dirCipher, Proof.Modes.RISCV64.iv0, Proof.Modes.RISCV64.blocks0,
    ↓reduceIte] at h2 h3
  rw [d', d0, i0, h₁.mem] at h2
  rw [i', d0, i0, h₁.mem] at h3
  exact ⟨h2, h3⟩

theorem cfbDecrypt_correct (s : State) (hs : (modePC cfbDecPost).pre s) :
    ∃ t s', Exec isa cfbDecrypt s t s' ∧ abiPreserved s s' ∧ cfbDecPost s s' := by
  refine modeFn_wp (rounds_of hs) fun s₁ h₁ => WP.mono (Proof.Modes.RISCV64.cfbDec_wp
    (dirCoreSpec true _ (rounds_of hs)) (seqPre_of hs h₁ true (M := Mode.cfbDec 2) rfl)
    (keyArgs_of hs h₁ true (M := Mode.cfbDec 2) rfl)) fun s' ⟨h1, h2, h3⟩ => ⟨h₁.abi h1, ?_⟩
  obtain ⟨d0, i0, -⟩ := post_eq h₁ (m := s₁.mem)
  obtain ⟨d', i', -⟩ := post_eq h₁ (m := s'.mem)
  simp only [dirCore, dirCoreSpec, Proof.Cast5.dirCipher, Proof.Modes.RISCV64.iv0, Proof.Modes.RISCV64.blocks0,
    ↓reduceIte] at h2 h3
  rw [d', d0, i0, h₁.mem] at h2
  rw [i', d0, i0, h₁.mem] at h3
  exact ⟨h2, h3⟩

/-! ## The contracts -/

/-- A state satisfying `modeP`'s precondition: the subkeys at `0x1000`, 16
rounds, the IV at `0x2000`, no data at `0x3000`, and the stack below
`0x8000`. -/
def modeSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 16 | .a2 => 0x2000 | .a3 => 0x3000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 0⟩]

/-- `modeSat` with the table, at `0x100000`. -/
def modeSatC : State :=
  { modeSat with mem := ecbSatMem, rd := [⟨0x1000, 128⟩, ⟨0x100000, 4096⟩], syms := fun _ => 0x100000 }

section
variable {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post' : sig.Post abi.ptrBits}
  {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {post : State → State → Prop}

/-- A mode's contract with the table, from `modeP`'s implying it without. -/
theorem implies_consts (h : (modeP post).Implies (sig.contract abi pre post' true frameBytes leak))
    (hpost : ∀ s s', post s s' → post (stripConsts ecbConsts s) s')
    (hsat : ∃ s, (sig.contract (abi.withConsts ecbConsts) pre post' true frameBytes leak).pre s) :
    (modePC post).Implies (sig.contract (abi.withConsts ecbConsts) pre post' true frameBytes leak) where
  pre s hs := ⟨h.pre _ (pre_consts.mp hs).1, (pre_consts.mp hs).2⟩
  post s s' hs hp := post_consts.mpr (post_stripConsts.mp (h.post (stripConsts ecbConsts s) s'
    (pre_consts.mp hs).1 (hpost s s' hp)))
  pub s₁ s₂ h₁ h₂ hp := by
    have a := h.pub (stripConsts ecbConsts s₁) (stripConsts ecbConsts s₂) (pre_consts.mp h₁).1
      (pre_consts.mp h₂).1 (pub_stripConsts.mpr (pub_consts.mp hp).1)
    obtain ⟨hsp, e0, e1, e2, e3, e4⟩ := a
    exact ⟨hsp, by simp only [stripConsts_gpr] at e0 e1 e2 e3 e4; simp [e0, e1, e2, e3, e4],
      (pub_consts.mp hp).2 _ List.mem_cons_self⟩
  sat := hsat

end

/-- `modeP`'s precondition and public data follow from the contract's, and
the contract's postcondition from `modeP`'s, with the table. `ls` unfolds
the contract and its signature. -/
local macro "mode_implies " "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  refine implies_consts
    { pre := by
        intro s h
        sig_pre [$ls,*, abi, argRegs, stackBelow] at h
        obtain ⟨al, sp, hrd, hwr, dKV, dKD, dVD, dSK, dSV, dSD, fK, fV, fD, hn⟩ := h
        simp only [Nat.mul_comm _ 8] at hwr dKD dVD dSD fD
        exact ⟨hrd, hwr, dKV, dKD, dVD, fK, fV, fD, al, sp, dSK, dSV, dSD, hn⟩
      post := fun s s' _ h => by sig_post [$ls,*, abi, argRegs]; exact h
      pub := by sig_implies_pub [$ls,*, abi, argRegs, argPub]
      sat := by sig_implies_sat [$ls,*, abi, argRegs, stackBelow] [modeSat] using modeSat }
    (fun _ _ h => h) ⟨modeSatC, ?_⟩
  have hl : s1234.length = 512 := by rw [Impl.Cast5.s1234, table_length]
  have held := ecbSatMem_held
  rw [ecbConsts_eq]
  generalize s1234 = W at hl held ⊢
  generalize e : modeSatC = s
  sig_pre [$ls,*, abi, argRegs, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst e
  rw [hl]
  repeat' apply And.intro
  all_goals first
    | exact fun i hi => held i (by rw [hl]; exact hi)
    | rfl
    | decide
    | exact Or.inr rfl
    | exact Region.disjoint_of_sep (by decide)
    | (intro r hr
       change r ∈ [(⟨0x2000, 8⟩ : Region), ⟨0x3000, 0⟩] at hr
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
       -- (A `rfl` pattern in a macro names a new variable, by hygiene.)
       rcases hr with hr | hr <;> (subst hr; exact Region.disjoint_of_sep (by decide)))))

theorem cbcEnc_implies :
    (modePC cbcEncPost).Implies (Proof.Cast5.cbcEncryptChainedRoundsContract (abi.withConsts ecbConsts) frameBytes) := by
  mode_implies [Proof.Cast5.cbcEncryptChainedRoundsContract, Spec.Cast5.cbcChainedSig]

theorem cbcDec_implies :
    (modePC cbcDecPost).Implies (Proof.Cast5.cbcDecryptChainedRoundsContract (abi.withConsts ecbConsts) frameBytes) := by
  mode_implies [Proof.Cast5.cbcDecryptChainedRoundsContract, Spec.Cast5.cbcChainedSig]

theorem ofb_implies : (modePC ofbPost).Implies (Proof.Cast5.ofbRoundsContract (abi.withConsts ecbConsts) frameBytes) := by
  mode_implies [Proof.Cast5.ofbRoundsContract, Spec.Cast5.ofbSig, Spec.Cast5.ofbPre]

theorem cfbEnc_implies :
    (modePC cfbEncPost).Implies (Proof.Cast5.cfbEncryptRoundsContract (abi.withConsts ecbConsts) frameBytes) := by
  mode_implies [Proof.Cast5.cfbEncryptRoundsContract, Spec.Cast5.cfbSig, Spec.Cast5.cfbPre]

theorem cfbDec_implies :
    (modePC cfbDecPost).Implies (Proof.Cast5.cfbDecryptRoundsContract (abi.withConsts ecbConsts) frameBytes) := by
  mode_implies [Proof.Cast5.cfbDecryptRoundsContract, Spec.Cast5.cfbSig, Spec.Cast5.cfbPre]

/-! ## Verified -/

theorem cbcEncryptChained_verified : Verified target cbcEncryptChained
    (Proof.Cast5.cbcEncryptChainedRoundsContract (abi.withConsts ecbConsts) frameBytes) :=
  Verified.of_correct cbcEncryptChained_correct (cbcEncryptChained_constantTime _) cbcEnc_implies

theorem cbcDecryptChained_verified : Verified target cbcDecryptChained
    (Proof.Cast5.cbcDecryptChainedRoundsContract (abi.withConsts ecbConsts) frameBytes) :=
  Verified.of_correct cbcDecryptChained_correct (cbcDecryptChained_constantTime _) cbcDec_implies

theorem ofb_verified : Verified target ofb (Proof.Cast5.ofbRoundsContract (abi.withConsts ecbConsts) frameBytes) :=
  Verified.of_correct ofb_correct (ofb_constantTime _) ofb_implies

theorem cfbEncrypt_verified : Verified target cfbEncrypt
    (Proof.Cast5.cfbEncryptRoundsContract (abi.withConsts ecbConsts) frameBytes) :=
  Verified.of_correct cfbEncrypt_correct (cfbEncrypt_constantTime _) cfbEnc_implies

theorem cfbDecrypt_verified : Verified target cfbDecrypt
    (Proof.Cast5.cfbDecryptRoundsContract (abi.withConsts ecbConsts) frameBytes) :=
  Verified.of_correct cfbDecrypt_correct (cfbDecrypt_constantTime _) cfbDec_implies

end VG.Proof.Cast5.RISCV64.Modes
