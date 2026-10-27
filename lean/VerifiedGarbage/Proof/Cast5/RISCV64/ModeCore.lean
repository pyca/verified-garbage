module

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
the address space and apart from the regions `rs`; the table holds the
S-boxes. -/
structure KeyArgs (s : State) (rs : List Region) (k : Spec.Cast5.Schedule) : Prop where
  sched : Spec.Cast5.scheduleAt s.mem (s.gpr .a0) = k
  key : keyR s ∈ s.rd ++ s.wr
  kfit : (s.gpr .a0).toNat + 128 ≤ 2 ^ 64
  keyOut : ∀ r ∈ rs, (keyR s).Disjoint r
  tbl : tblR s ∈ s.rd ++ s.wr
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

/-- The registers the core keeps the mode's `s1`–`s4` in. -/
def parked : List Reg := [.a3, .a4, .s11, .ra]

/-- The registers the core writes before the block function. -/
def setRegs : List Reg := [dat, .a3, .a4, .s11, .ra, tbl, rnd]

/-- Of the registers the caller expects kept, those the core neither saves
nor parks the mode's in are none it writes. -/
theorem kept_rest : ∀ r ∈ kept, r ∉ modeSaved.map Prod.fst → r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → r ≠ .s4 →
    r ∉ roundRegs ∧ r ∉ setRegs := by decide

/-- The mode's `s1`–`s4` and the registers the core parks them in are none the
block function writes. -/
theorem parked_ok : ∀ r ∈ parked, r ∉ roundRegs := by decide

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
  have hW : (⟨B, 128⟩ : Region) ∈ s.wr := hS.low
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
    obtain rfl : j = 0 := by have : j < 1 := hj; omega
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
