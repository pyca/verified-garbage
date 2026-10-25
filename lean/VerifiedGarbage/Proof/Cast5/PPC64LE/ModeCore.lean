module

public import VerifiedGarbage.Proof.Modes.PPC64LE.Core
public import VerifiedGarbage.Impl.Cast5.PPC64LE.Modes
public import VerifiedGarbage.Proof.Cast5.ModeCipher
public import VerifiedGarbage.Proof.Cast5.PPC64LE.Block
import VerifiedGarbage.Proof.Cast5.ModeMem
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# CAST5's core for the modes on PPC64LE

`dirCoreSpec up n hn`: CAST5's core (`Impl.Cast5.PPC64LE.dirCore up n`)
meets what the modes need of a core (`Proof.Modes.PPC64LE.CoreSpec`), with
the key the subkeys, read in place through `r3`, and its cipher encryption
(`up`) or decryption with `n` rounds (`Proof.Cast5.dirCipher`). The subkeys
and the table of S-boxes (where the static `VG_CAST5_S1234` puts it, holding
the S-boxes) are readable and apart from the regions the mode writes
(`KeyArgs`), and from the scratch buffer (`Ready`), so nothing the mode or
the core writes changes them. The core runs ECB's block function on its
buffer, slot 0 (`crypt_ok`), with the modes' `r29` and `r30` in `r6` and
`r7`, our caller's `r14`–`r28` in slots 1 to 15, and the table's address,
255, zero and `n` in the registers the block function reads.
-/

@[expose] public section

namespace VG.Proof.Cast5.PPC64LE.Mode

open VG VG.PPC64LE VG.Impl.Cast5.PPC64LE
open VG.Impl.Cast5 (s1234Sym s1234)
open VG.Impl.Modes.PPC64LE (sb)
open VG.Proof.Cast5 (Held dirCipher dirCipher_length ofFn_bytesAt scheduleAt_frame held_frame)
open VG.Proof.Modes.PPC64LE (coreRegion blkRegion blkAddr slotA CoreSpec Layout ScrIn kept KeptBut)

/-- The subkeys. -/
abbrev keyR (s : State) : Region := ⟨s.gpr .r3, 128⟩

/-- The table of S-boxes. -/
abbrev tblR (s : State) : Region := ⟨s.syms s1234Sym, 4096⟩

/-- The subkeys at `r3` are `k`, and they and the table are readable, within
the address space and apart from the regions `rs`; the table holds the
S-boxes. -/
structure KeyArgs (s : State) (rs : List Region) (k : Spec.Cast5.Schedule) : Prop where
  sched : Spec.Cast5.scheduleAt s.mem (s.gpr .r3) = k
  key : keyR s ∈ s.rd ++ s.wr
  kfit : (s.gpr .r3).toNat + 128 ≤ 2 ^ 64
  keyOut : ∀ r ∈ rs, (keyR s).Disjoint r
  tbl : tblR s ∈ s.rd ++ s.wr
  held : Held s.mem (s.syms s1234Sym) s1234
  tblOut : ∀ r ∈ rs, (tblR s).Disjoint r

/-- The key's arguments, apart from the scratch buffer at `B` too. -/
structure Ready (s : State) (B : Addr) (ws : List Region) (k : Spec.Cast5.Schedule) : Prop where
  args : KeyArgs s ws k
  keyScr : (keyR s).Disjoint ⟨B, 8 * 22⟩
  tblScr : (tblR s).Disjoint ⟨B, 8 * 22⟩

/-- `KeyArgs` survives what keeps `r3`, the regions and the statics, and
writes memory apart from the subkeys and the table. -/
theorem KeyArgs.congr {s s' : State} {rs : List Region} {k : Spec.Cast5.Schedule} (h : KeyArgs s rs k)
    (e : s'.gpr .r3 = s.gpr .r3) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsy : s'.syms = s.syms)
    {fs : List Region} (hf : Frame fs s.mem s'.mem) (hk : ∀ r ∈ fs, (keyR s).Disjoint r)
    (ht : ∀ r ∈ fs, (tblR s).Disjoint r) : KeyArgs s' rs k where
  sched := by rw [e, scheduleAt_frame hf hk, h.sched]
  key := by rw [hrd, hwr, keyR, e]; exact h.key
  kfit := by rw [e]; exact h.kfit
  keyOut := by rw [keyR, e]; exact h.keyOut
  tbl := by rw [hrd, hwr, tblR, hsy]; exact h.tbl
  held := by rw [hsy]; exact held_frame h.held hf ht
  tblOut := by rw [tblR, hsy]; exact h.tblOut

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Spec.Cast5.Schedule} (h : KeyArgs s rs k)
    (e : KeptBut s s') (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsy : s'.syms = s.syms)
    (hf : Frame rs s.mem s'.mem) : KeyArgs s' rs k :=
  h.congr e.r3 hrd hwr hsy hf h.keyOut h.tblOut

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
  refine ⟨?_, by rw [keyR, e.r3]; exact h.keyScr, by rw [tblR, hsy]; exact h.tblScr⟩
  have a := h.args.congr e.r3 hrd hwr hsy hf hk ht
  exact ⟨a.sched, a.key, a.kfit, by rw [keyR, e.r3]; exact h.args.keyOut, a.tbl, a.held,
    by rw [tblR, hsy]; exact h.args.tblOut⟩

theorem layout (up : Bool) (n : Nat) : Layout (dirCore up n) :=
  ⟨Nat.one_pos, .inl rfl, by show 8 * 0 + 4 * 2 * 1 ≤ 8 * 16; decide, by show 16 + 6 ≤ 22; decide,
    by show 8 * 22 < 2 ^ 15; decide⟩

theorem prepare_wp (up : Bool) (n : Nat) {s : State} {B : Addr} {rs : List Region} {k : Spec.Cast5.Schedule}
    (hB : s.gpr sb = B) (_hS : ScrIn s B (dirCore up n).total)
    (hm : (⟨B, 8 * (dirCore up n).total⟩ : Region) ∈ rs) (hk : KeyArgs s rs k) :
    WP isa (dirCore up n).prepare s fun s' => Ready s' B rs k ∧ s'.gpr sb = B ∧
      (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ Frame [coreRegion (dirCore up n) B] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr :=
  wp_nil ⟨⟨hk, hk.keyOut _ hm, hk.tblOut _ hm⟩, hB, fun _ _ => rfl, Frame.refl _ _, rfl, rfl⟩

/-! ## The core's code -/

theorem modeSaved_fits : Spill.Fits modeSaved := by decide
theorem modeSaved_ok : ∀ p ∈ modeSaved, p.2 % 8 = 0 ∧ p.2 < 32768 := modeSaved_fits.1
theorem modeSaved_lt : ∀ p ∈ modeSaved, 8 ≤ p.2 ∧ p.2 + 8 ≤ 8 + 120 := by decide
theorem modeSaved_restorable : Spill.Restorable sb modeSaved := by decide

/-- Of the registers the caller expects kept, those the core saves are none
of the registers it uses to keep `r29` and `r30`. -/
theorem saved_ne : ∀ p ∈ modeSaved, p.1 ≠ .r6 ∧ p.1 ≠ .r7 := by decide

/-- The others are none of the registers the core writes. -/
theorem kept_rest : ∀ r ∈ kept, r ∉ modeSaved.map Prod.fst → r ≠ .r29 → r ≠ .r30 →
    r ∉ roundRegs ∧ r ≠ tbl ∧ r ≠ c255 ∧ r ≠ .r0 ∧ r ≠ rnd ∧ r ≠ .r6 ∧ r ≠ .r7 := by decide

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
  have hfit : B.toNat + 176 ≤ 2 ^ 64 := hS.fit
  have hW : (⟨B, 176⟩ : Region) ∈ s.wr := hS.wr
  obtain ⟨hk, hkB, htB⟩ := hR
  have hn15 : n < 2 ^ 15 := by rcases hn with rfl | rfl <;> decide
  refine VG.PPC64LE.WP.of_syms ?_
  simp only [dirCore, modeCrypt, List.cons_append, List.nil_append]
  -- `r29`, `r30` to `r6`, `r7`.
  refine WP.seq (WP.cons exec_logic (WP.cons exec_logic ?_))
  generalize hs₂ : ((s.write .r6 (s.gpr .r29 ||| s.gpr .r29)).write .r7
    ((s.write .r6 (s.gpr .r29 ||| s.gpr .r29)).gpr .r30 ||| (s.write .r6 (s.gpr .r29 ||| s.gpr .r29)).gpr .r30)) = s₂
  have g₂ : ∀ r, r ≠ .r6 → r ≠ .r7 → s₂.gpr r = s.gpr r := fun r h6 h7 => by
    rw [← hs₂]; simp [State.write, h6, h7]
  have r6₂ : s₂.gpr .r6 = s.gpr .r29 := by rw [← hs₂]; simp [State.write]
  have r7₂ : s₂.gpr .r7 = s.gpr .r30 := by rw [← hs₂]; simp [State.write]
  have mem₂ : s₂.mem = s.mem := by rw [← hs₂]; rfl
  have rd₂ : s₂.rd = s.rd := by rw [← hs₂]; rfl
  have wr₂ : s₂.wr = s.wr := by rw [← hs₂]; rfl
  have sy₂ : s₂.syms = s.syms := by rw [← hs₂]; rfl
  have b₂ : s₂.gpr sb = B := by rw [g₂ _ (by decide) (by decide), hB]
  -- Our caller's registers to their slots.
  refine Spill.save_ok (b := sb) (by decide) modeSaved_ok (fun p hp => by
    have := modeSaved_lt p hp
    exact ⟨_, by rw [wr₂]; exact hW, by rw [b₂]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩) ?_
  rw [b₂]
  generalize hM : Spill.saveMem s₂.mem B s₂.gpr modeSaved = M
  have sv : Spill.Saved B s₂.gpr modeSaved M := by rw [← hM]; exact Spill.saveMem_saved modeSaved_fits _ _ _
  have fM : Frame [⟨B + BitVec.ofNat 64 8, 120⟩] s.mem M := by
    rw [← hM, mem₂]; exact Spill.saveMem_frame modeSaved_lt (by decide) _ _ _
  -- The table's address, 255, zero and the rounds.
  refine WP.cons (exec_adrSym (by decide)) ?_
  refine wp_li (by decide) fun s₅ u₅ => wp_li (by decide) fun s₆ u₆ => wp_li hn15 fun s₇ u₇ => wp_nil ?_
  have g₇ : ∀ r, r ≠ tbl → r ≠ c255 → r ≠ .r0 → r ≠ rnd → s₇.gpr r = s₂.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₇.other r h4, u₆.other r h3, u₅.other r h2]; simp [State.write, h1]
  have t₇ : s₇.gpr tbl = s.syms s1234Sym := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), ← sy₂]; simp [State.write]
  have c₇ : s₇.gpr c255 = 255#64 := by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr]
  have z₇ : s₇.gpr .r0 = 0 := by rw [u₇.other _ (by decide), u₆.gpr]; rfl
  have n₇ : s₇.gpr rnd = BitVec.ofNat 64 n := u₇.gpr
  have m₇ : s₇.mem = M := by rw [u₇.mem, u₆.mem, u₅.mem]; rfl
  have rd₇ : s₇.rd = s.rd := by rw [u₇.rd, u₆.rd, u₅.rd]; exact rd₂
  have wr₇ : s₇.wr = s.wr := by rw [u₇.wr, u₆.wr, u₅.wr]; exact wr₂
  have b₇ : s₇.gpr sb = B := by rw [g₇ _ (by decide) (by decide) (by decide) (by decide), b₂]
  have r3₇ : s₇.gpr .r3 = s.gpr .r3 := by
    rw [g₇ _ (by decide) (by decide) (by decide) (by decide), g₂ _ (by decide) (by decide)]
  -- Nothing the saves wrote is the subkeys, the table or the block.
  have hkM : ∀ r ∈ [(⟨B + BitVec.ofNat 64 8, 120⟩ : Region)], (keyR s).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hkB.sub_right (Offset.sub_base _ (by decide))
  have htM : ∀ r ∈ [(⟨B + BitVec.ofNat 64 8, 120⟩ : Region)], (tblR s).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact htB.sub_right (Offset.sub_base _ (by decide))
  have pre : BPre s₇ .r5 B (s.gpr .r3) n :=
    { ptr := b₇
      prOk := by decide
      sched := r3₇
      rounds := n₇
      nv := hn
      zero := z₇
      c255 := c₇
      trd := by rw [t₇, rd₇, wr₇]; exact hk.tbl
      held := by rw [t₇, m₇]; exact held_frame hk.held fM htM
      inP := ⟨_, by rw [wr₇]; exact hW, fun off ho => Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
      inK := by rw [rd₇, wr₇]; exact hk.key
      kfit := hk.kfit }
  -- The block function.
  refine WP.seq (WP.mono (crypt_ok pre up) fun v hv => ?_)
  have gv : ∀ r, r ∉ roundRegs → v.gpr r = s₇.gpr r := fun r hr => hv.keep.gpr hr
  have bv : v.gpr sb = B := by rw [gv _ (by decide), b₇]
  have svv : Spill.Saved B s₂.gpr modeSaved v.mem := by
    rw [← m₇] at sv
    exact sv.frame hv.frame fun p hp r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base _ (by have := modeSaved_lt p hp; omega_arith) (by have := modeSaved_lt p hp; omega_arith)
  -- Our caller's registers back, and `r29`, `r30`.
  refine Spill.restore_ok (b := sb) (by decide) bv modeSaved_ok modeSaved_restorable (fun p hp => by
    have := modeSaved_lt p hp
    exact ⟨_, by rw [hv.keep.2.1, hv.keep.2.2, rd₇, wr₇]; exact List.mem_append_right _ hW,
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩) svv fun w R => ?_
  refine wp_mr fun x₁ e₁ => wp_mr fun x₂ e₂ => wp_nil fun syF => ?_
  have gw : ∀ r, r ≠ .r29 → r ≠ .r30 → x₂.gpr r = w.gpr r := fun r h29 h30 => by
    rw [e₂.other r h30, e₁.other r h29]
  -- The memory: the saves and the block.
  have memF : x₂.mem = v.mem := by rw [e₂.mem, e₁.mem, R.mem]
  have fF : Frame [⟨B, 8 * 16⟩] s.mem x₂.mem := by
    rw [memF]
    refine (fM.sub fun r hr => ?_).trans ((m₇ ▸ hv.frame).sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by decide)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
  have rdF : x₂.rd = s.rd := by rw [e₂.rd, e₁.rd, R.rd, hv.keep.2.1, rd₇]
  have wrF : x₂.wr = s.wr := by rw [e₂.wr, e₁.wr, R.wr, hv.keep.2.2, wr₇]
  have r3F : x₂.gpr .r3 = s.gpr .r3 := by
    rw [gw _ (by decide) (by decide), R.other _ (by decide), gv _ (by decide), r3₇]
  have hkF : ∀ r ∈ [(⟨B, 8 * 16⟩ : Region)], (keyR s).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hkB.sub_right (Region.sub_prefix (by decide))
  have htF : ∀ r ∈ [(⟨B, 8 * 16⟩ : Region)], (tblR s).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact htB.sub_right (Region.sub_prefix (by decide))
  refine ⟨?_, fun r hr => ?_, ⟨hk.congr r3F rdF wrF syF fF hkF htF, by rw [keyR, r3F]; exact hkB,
    by rw [tblR, syF]; exact htB⟩, fF, fun j hj => ?_, rdF, wrF⟩
  · rw [gw _ (by decide) (by decide), R.other _ (by decide), bv]
  · -- The registers the caller expects kept.
    by_cases h29 : r = .r29
    · subst h29
      rw [e₂.other _ (by decide), e₁.gpr, R.other _ (by decide), gv _ (by decide),
        g₇ _ (by decide) (by decide) (by decide) (by decide), r6₂]
    by_cases h30 : r = .r30
    · subst h30
      rw [e₂.gpr, e₁.other _ (by decide), R.other _ (by decide), gv _ (by decide),
        g₇ _ (by decide) (by decide) (by decide) (by decide), r7₂]
    rw [gw r h29 h30]
    by_cases hs : r ∈ modeSaved.map Prod.fst
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hs
      rw [R.gpr p hp, g₂ _ (saved_ne p hp).1 (saved_ne p hp).2]
    · obtain ⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7⟩ := kept_rest r hr hs h29 h30
      rw [R.other r hs, gv r hr1, g₇ r hr2 hr3 hr4 hr5, g₂ r hr6 hr7]
  · -- The block.
    obtain rfl : j = 0 := by simpa using hj
    have ea : blkAddr (dirCore up n) B 0 = B := by simp [blkAddr, slotA, dirCore]
    simp only [dirCore] at ea
    have hb : Spec.Aes.bytesAt M B 8 = Spec.Aes.bytesAt s.mem B 8 :=
      bytesAt_frame fM fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.base_disjoint _ (by decide) (by omega_arith)
    have hkk : Spec.Cast5.scheduleAt M (s.gpr .r3) = k := by rw [scheduleAt_frame fM hkM, hk.sched]
    rw [ea, show 4 * 2 = 8 from rfl, memF, Proof.Cast5.bytesAt_eq, hv.blk, m₇, dirCipher_bytes, hkk,
      ← ofFn_bytesAt M B, hb, ofFn_bytesAt]

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

end VG.Proof.Cast5.PPC64LE.Mode
