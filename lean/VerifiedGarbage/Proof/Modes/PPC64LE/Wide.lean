module
-- separate module: every PPC64LE core's batched modes, as `Modes.lean` has the one-block ones

public import VerifiedGarbage.Proof.Modes.PPC64LE.Seq
public import VerifiedGarbage.Proof.Modes.Wide
public import VerifiedGarbage.Proof.Modes.WideCtr
public import VerifiedGarbage.Proof.Modes.PPC64LE.Modes
public import VerifiedGarbage.Spec.Gcm
public import VerifiedGarbage.Proof.Modes.Ctr32
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Modes.StepsChained
import VerifiedGarbage.Proof.Modes.CtrStep
import VerifiedGarbage.Proof.Modes.Ctr32Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.Block

/-!
# Block cipher modes on PPC64LE, a group of blocks at a time

`wideSteps_ok`: the loops of `Core.seq2` (`Impl/Modes/PPC64LE/Wide.lean`)
take all the steps of the mode `Mn`, one block of `st` bytes each, as
`Core.steps Mn` does (`LoopsOk`): the steps of `Mw`, each of a group of
`g = 2 ^ lg` blocks, which compute `group st g F` (`loopWide_wp`), while
a group is left, then those of `Mn` (`loop_wp`) for the rest. The data
splits at the first `g q` blocks (`q = n / g`): running `group st g F` on
the groups is running `F` on their blocks (`run_group_blocks`), and `F`
goes on from where the groups left the chaining value (`run_append`). As
on RISC-V (`Proof/Modes/RISCV64/Wide.lean`).

`wideStepsWith_ok`: the same, with the steps of `Mn` on the core
`c.withOne one`, whose code `one` enciphers the buffer's first block
(`OneOk`), and is a core of its own (`CoreSpec.withOne`): `seq2With`'s
loops. `seq2`'s are those of `one = c.crypt` (`OneOk.self`), whose core
takes the same steps as `c` (`withOne_steps`).

`levels_ok`: the loops of `Core.levels`, a wide loop for each level in
turn, each on the blocks the ones before it left, then `rest`: each wide
loop (`wideThen_ok`, whose level `WideOk` states what it needs) leaves the
blocks after its groups to the code after it, which takes all the steps
from wherever it starts (`StepsOk`), as the narrow steps on `c.withOne one`
do (`stepsOne_ok`). `wideStepsWith_ok` is the case of one level.

`cbcDecWide_wp`, `cfbDecWide_wp`, `ctrWide_wp` and `ctr32Wide_wp`: the
function (`seq2_changes_wp`, as `seq_changes_wp`) over CBC and CFB
decryption and the two counter modes, with the conclusions of
`cbcDecChained_wp`, `cfbDec_wp`, `ctr_wp` and `ctr32_wp`;
`cbcDecWideWith_wp` and `cfbDecWideWith_wp` the same of `seq2With`, and
`cbcDecLevelsWith_wp` and `cfbDecLevelsWith_wp` of `seqLevelsWith`, whose
levels fit the core (`LevelsFit`); `cfbDecSeq_wp`, `ctrSeq_wp` and
`ctr32Seq_wp` those of CFB decryption and the counter modes, one block a
step (`seq`), for the short messages of `pick`.

`pick_wp`: `pick lg short long` (`Impl/Modes/PPC64LE/Wide.lean`) runs
`short` or `long` from the state with `r8` written, which keeps the modes'
arguments (`r3`–`r7`), regions and memory, so their preconditions hold of it
as of the entry state; `abiPreserved_r8` brings their conclusion back.
-/

@[expose] public section

namespace VG.Proof.Modes.PPC64LE

open VG VG.PPC64LE VG.Impl.Modes VG.Impl.Modes.PPC64LE
open VG.Spec.Aes (bytesAt)

variable {c : Core}

theorem dataW_mono {wr : List Region} {D : Addr} {len len' : Nat}
    (h : ∀ o w, 0 < w → o + w ≤ len' → InRegions wr (D + BitVec.ofNat 64 o) w) (hl : len ≤ len') :
    ∀ o w, 0 < w → o + w ≤ len → InRegions wr (D + BitVec.ofNat 64 o) w :=
  fun o w hw ho => h o w hw (Nat.le_trans ho hl)

theorem dataW_shift {wr : List Region} {D : Addr} {d len len' : Nat}
    (h : ∀ o w, 0 < w → o + w ≤ len' → InRegions wr (D + BitVec.ofNat 64 o) w) (hl : d + len ≤ len') :
    ∀ o w, 0 < w → o + w ≤ len → InRegions wr (D + BitVec.ofNat 64 d + BitVec.ofNat 64 o) w :=
  fun o w hw ho => by rw [VG.Offset.add_add]; exact h (d + o) w hw (by omega_using [ho, hl])

/-- The code `one` enciphers the first block of `c`'s buffer, as `c`'s
code does its `G` (`CoreSpec.crypt_wp`). -/
def OneOk (cs : CoreSpec c) (one : Prog isa) : Prop :=
  ∀ {s : State} {B : Addr} {ws : List Region} {k : cs.Key}, s.gpr sb = B → ScrIn s B c.total →
    cs.Ready s B ws k →
    WP isa one s fun s' => s'.gpr sb = B ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ cs.Ready s' B ws k ∧
      Frame [coreRegion c B] s.mem s'.mem ∧
      bytesAt s'.mem (blkAddr c B 0) (4 * c.bw) = cs.cipher k (bytesAt s.mem (blkAddr c B 0) (4 * c.bw)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr

/-- `c`'s own code enciphers its buffer's first block. -/
theorem OneOk.self (cs : CoreSpec c) : OneOk cs c.crypt := fun hB hS hR =>
  WP.mono (cs.crypt_wp hB hS hR) fun _ ⟨h1, h2, h3, h4, h5, h6, h7⟩ =>
    ⟨h1, h2, h3, h4, h5 0 cs.layout.G_pos, h6, h7⟩

/-- `c` with the code `one`, a core on one block, with `c`'s key. -/
def CoreSpec.withOne (cs : CoreSpec c) {one : Prog isa} (h : OneOk cs one) : CoreSpec (c.withOne one) where
  Key := cs.Key
  cipher := cs.cipher
  KeyArgs := cs.KeyArgs
  Ready := cs.Ready
  cipher_len := cs.cipher_len
  layout := by
    have hL := cs.layout
    have hb : 4 * c.bw * 1 ≤ 4 * c.bw * c.G := Nat.mul_le_mul_left _ hL.G_pos
    exact ⟨Nat.one_pos, hL.bw, by have := hL.buf_le; simp only [Core.withOne]; omega_using [this, hb],
      hL.room, hL.disp⟩
  keyArgs_congr := cs.keyArgs_congr
  ready_frame h1 h2 h3 h4 h5 h6 h7 h8 := cs.ready_frame h1 h2 h3 h4 h5 h6 h7 fun r hr =>
    (h8 r hr).imp id fun hs a ha => Region.sub_prefix (Nat.mul_le_mul_left _ cs.layout.G_pos) a (hs a ha)
  prepare_wp := cs.prepare_wp
  crypt_wp hB hS hR := WP.mono (h hB hS hR) fun _ ⟨h1, h2, h3, h4, h5, h6, h7⟩ =>
    ⟨h1, h2, h3, h4, fun j hj => by
      obtain rfl : j = 0 := Nat.lt_one_iff.mp hj
      exact h5, h6, h7⟩

/-- `c` with its own code on one block takes `c`'s steps. -/
theorem withOne_steps (M : Mode) : (c.withOne c.crypt).steps M = c.steps M := rfl

section
variable (cs : CoreSpec c) {Mw Mn : Mode} {F : StepFn} {s₀ : State} {k : cs.Key} {lg : Nat}
  {ciphB : Spec.Cbc.Cipher} {one : Prog isa}

/-- The code `P` takes all the steps of `Mn` from any state with `n` blocks
left at `D` (as `LoopsOk`, for any data and regions `W`). -/
def StepsOk (Mn : Mode) (F : StepFn) (k : cs.Key) (P : Prog isa) : Prop :=
  ∀ {s : State} {B D : Addr} {n : Nat} {W : List Region} {c0 : List Byte} {xs : List (List Byte)},
    Fixed c s B D n Mn.step (4 * c.bw) W n 1 → Inv cs s B D n Mn.step W n 1 k F c0 xs 0 s →
    WP isa P s (Done (c := c) s B D n Mn.step F c0 xs)

/-- What a wide loop of the mode `Mw`, on groups of `2 ^ lg` blocks of the
mode `Mn`, needs. -/
structure WideOk (Mn : Mode) (F : StepFn) (k : cs.Key) (Mw : Mode) (lg : Nat) : Prop where
  lg15 : lg ≤ 15
  G : 2 ^ lg ≤ c.G
  step : Mw.step = 2 ^ lg * Mn.step
  stepLt : 2 ^ lg * Mn.step < 2 ^ 15
  pre : ∀ o ∈ Mw.pre, o.InBounds (lens c Mw.step (4 * c.bw * 2 ^ lg))
  post : ∀ o ∈ Mw.post, o.InBounds (lens c Mw.step (4 * c.bw * 2 ^ lg))
  ciph : ∃ ciphB, ComputesB Mw (4 * c.bw) (4 * c.bw * 2 ^ lg) ciphB (group Mn.step (2 ^ lg) F) ∧
    BufCipher c (cs.cipher k) ciphB (4 * c.bw * 2 ^ lg)

/-- The steps of `Mn` on `c.withOne one`. -/
theorem stepsOne_ok (hone : OneOk cs one)
    (hpre : ∀ o ∈ Mn.pre, o.InBounds (lens c Mn.step (4 * c.bw)))
    (hpost : ∀ o ∈ Mn.post, o.InBounds (lens c Mn.step (4 * c.bw)))
    (hcomp : Computes Mn (4 * c.bw) (cs.cipher k) F) :
    StepsOk cs Mn F k ((c.withOne one).steps Mn) := by
  intro s B D n W c0 xs hFx hI
  let cs₁ := cs.withOne hone
  have hL := hFx.layout
  have hFn : Fixed (c.withOne one) s B D n Mn.step (4 * c.bw) W n 1 :=
    ⟨hFx.scr, hFx.dataW, hFx.dataFit, hFx.dataScr, hFx.nFit, hFx.cnt, hFx.dec, hFx.step,
      ⟨by have := hFx.buf.1; omega_using [this], Nat.le_of_eq (Nat.mul_one _).symm⟩, hFx.dataIn, hFx.scrIn,
      cs₁.layout⟩
  have hIn : Inv cs₁ s B D n Mn.step W n 1 k F c0 xs 0 s :=
    ⟨hI.b, hI.keep, hI.rd, hI.wr, hI.dp, hI.np, hI.ready, hI.data, hI.chn, Frame.refl _ _⟩
  have hxs : xs.length = n := by
    have e := hI.data
    simp only [List.take_zero, run, List.nil_append, List.drop_zero] at e
    rw [← e, chunksAt_length]
  refine WP.mono (loop_wp cs₁ hFn rfl hpre hpost hcomp hxs hIn) fun s' h' => ?_
  have d := h'.done hxs
  exact ⟨d.b, d.keep, d.rd, d.wr, d.data, d.chn, d.frame⟩

/-- A wide loop of `Mw`, then `rest` on the blocks it leaves. -/
theorem wideThen_ok {rest : Prog isa} (hw : WideOk cs Mn F k Mw lg) (hFb : Blockwise F Mn.step (4 * c.bw))
    (hrest : StepsOk cs Mn F k rest) :
    StepsOk cs Mn F k (.seq (c.loopWide Mw lg) rest) := by
  intro s₂ B D n W iv xs hFx hI
  obtain ⟨hlg, hG, hstw, hstle, hpreW, hpostW, ciphB, hcompW, hB⟩ := hw
  have hL := hFx.layout
  have hg : 0 < 2 ^ lg := Nat.two_pow_pos lg
  have hg15 : 2 ^ lg ≤ 2 ^ 15 := Nat.pow_le_pow_right (by decide) hlg
  have hbw : 0 < c.bw := by rcases hL.bw with h | h <;> omega_using [h]
  have hivl : iv.length = 4 * c.bw := by
    have e : bytesAt s₂.mem (slotA B c.chnSlot) (4 * c.bw) = iv := hI.chn
    rw [← e]; simp [bytesAt]
  generalize hsd : Mn.step = st at hFx hI hstw hstle hcompW hFb ⊢
  have hst := hFx.step
  have hN := hFx.nFit
  have hDf := hFx.dataFit
  -- The groups and the blocks left.
  let g := 2 ^ lg
  let q := n / g
  let r := n - g * q
  have hq : g * q ≤ n := Nat.mul_div_le _ _
  have hnr : n = g * q + r := by omega_using [hq]
  have hwq' : Mw.step * q = st * (g * q) := by rw [hstw, Nat.mul_assoc, Nat.mul_left_comm]
  have hwq : Mw.step * q + st * r = st * n := by rw [hwq', ← Nat.mul_add, ← hnr]
  obtain ⟨RW, hRW, hDW⟩ := hFx.dataIn
  have coreScr : Region.Sub (coreRegion c B) (scrRegion c B) := Region.sub_prefix (by
    have := hL.room; omega_using [this])
  have chnScr : Region.Sub (chnRegion c B) (scrRegion c B) := VG.Offset.sub_base _ (by
    have h1 := hL.room; have h2 := bw_le hL; simp only [Core.chnSlot]; omega_using [h1, h2])
  -- The groups.
  have hFw : Fixed c s₂ B D q Mw.step (4 * c.bw * 2 ^ lg) W n (2 ^ lg) :=
    ⟨hFx.scr, dataW_mono hFx.dataW (by omega_using [hwq]), by omega_using [hDf, hwq],
      hFx.dataScr.sub_left (Region.sub_prefix (by omega_using [hwq])), hN, Nat.mul_div_le _ _, hg15,
      ⟨by rw [hstw]; exact Nat.mul_pos hg hst.1, by rw [hstw]; exact hstle⟩,
      ⟨Nat.mul_pos (by omega_using [hbw]) hg, Nat.mul_le_mul_left _ hG⟩,
      ⟨RW, hRW, fun a ha => hDW a (Region.sub_prefix (by omega_using [hwq]) a ha)⟩, hFx.scrIn, hL⟩
  generalize hxw : chunksAt Mw.step s₂.mem D q = xw
  have hIw : Inv cs s₂ B D q Mw.step W n (2 ^ lg) k (group st (2 ^ lg) F) iv xw 0 s₂ := by
    refine ⟨hI.b, hI.keep, hI.rd, hI.wr, ?_, ?_, hI.ready, ?_, ?_, Frame.refl _ _⟩
    · rw [hI.dp, Nat.mul_zero, Nat.mul_zero]
    · rw [hI.np, Nat.mul_zero, Nat.mul_zero]
    · simp only [hxw, List.take_zero, run, List.nil_append, List.drop_zero]
    · rw [hI.chn]; rfl
  have hxwl : xw.length = q := by rw [← hxw, chunksAt_length]
  refine WP.seq (WP.mono (loopWide_wp cs (by omega_using [hlg]) hFw rfl rfl hB hpreW hpostW hcompW hxwl hIw)
    fun s₃ h₃ => ?_)
  -- The blocks left.
  let D' := D + BitVec.ofNat 64 (Mw.step * q)
  have hD'fit : D'.toNat + st * r ≤ 2 ^ 64 := by
    show (D + BitVec.ofNat 64 (Mw.step * q)).toNat + st * r ≤ 2 ^ 64
    have := D.isLt
    rw [VG.Offset.toNat_add_ofNat]; omega_using [hDf, hwq, this]
  have hsubN : Region.Sub (dataRegion D' st r) (dataRegion D st n) := VG.Offset.sub_base _ (by omega_using [hwq])
  have hFn : Fixed c s₃ B D' r st (4 * c.bw) W r 1 :=
    ⟨⟨by rw [h₃.wr]; exact hFx.scr.wr, hFx.scr.fit⟩, by rw [h₃.wr]; exact dataW_shift hFx.dataW (by omega_using [hwq]),
      hD'fit, hFx.dataScr.sub_left hsubN, by omega_using [hN], by omega_using [], by decide, hst,
      ⟨by omega_using [hbw], Nat.le_trans (Nat.le_of_eq (Nat.mul_one _).symm) (Nat.mul_le_mul_left _ hL.G_pos)⟩,
      ⟨RW, hRW, fun a ha => hDW a (hsubN a ha)⟩, hFx.scrIn, hL⟩
  generalize hxn : chunksAt st s₃.mem D' r = xn
  have hIn : Inv cs s₃ B D' r st W r 1 k F (run (group st (2 ^ lg) F) iv xw).2 xn 0 s₃ := by
    refine ⟨h₃.b, fun _ _ _ _ => rfl, rfl, rfl, ?_, ?_, h₃.ready, ?_, ?_, Frame.refl _ _⟩
    · rw [h₃.dp, Nat.mul_zero, BitVec.add_zero]
    · rw [h₃.np, Nat.mul_zero, Nat.sub_zero]
    · simp only [hxn, List.take_zero, run, List.nil_append, List.drop_zero]
    · show bytesAt s₃.mem (slotA B c.chnSlot) (4 * c.bw) = _
      rw [h₃.chn, List.take_of_length_le (by omega_using [hxwl])]; rfl
  have hxnl : xn.length = r := by rw [← hxn, chunksAt_length]
  subst hsd
  refine WP.mono (hrest hFn hIn) fun s₄ d₄ => ?_
  have d₃ := h₃.done hxwl
  -- How the data split.
  have hdis₃ : ∀ R ∈ big c B D q Mw.step, Region.Disjoint (dataRegion D' Mn.step r) R := by
    intro R hR
    simp only [big, List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl
    · exact (hFx.dataScr.sub_left hsubN).sub_right coreScr
    · exact (hFx.dataScr.sub_left hsubN).sub_right chnScr
    · exact (VG.Offset.disjoint_base _ (Nat.le_refl _) (by omega_using [hDf, hwq]))
  have hdis₄ : ∀ R ∈ big c B D' r Mn.step, Region.Disjoint (dataRegion D Mn.step (g * q)) R := by
    intro R hR
    simp only [big, List.mem_cons, List.not_mem_nil, or_false] at hR
    have hpre' : Region.Sub (dataRegion D Mn.step (g * q)) (dataRegion D Mn.step n) :=
      Region.sub_prefix (by omega_using [hwq, hwq'])
    rcases hR with rfl | rfl | rfl
    · exact (hFx.dataScr.sub_left hpre').sub_right coreScr
    · exact (hFx.dataScr.sub_left hpre').sub_right chnScr
    · show Region.Disjoint ⟨D, Mn.step * (g * q)⟩ ⟨D + BitVec.ofNat 64 (Mw.step * q), Mn.step * r⟩
      rw [hwq']
      exact VG.Offset.base_disjoint _ (Nat.le_refl _) (by omega_using [hDf, hwq, hwq'])
  have hsplit : ∀ m : Mem, chunksAt Mn.step m D n = chunksAt Mn.step m D (g * q) ++ chunksAt Mn.step m D' r :=
    fun m => by
      show _ = _ ++ chunksAt Mn.step m (D + BitVec.ofNat 64 (Mw.step * q)) r
      rw [hnr, chunksAt_add, hwq']
  have hgroup : ∀ m : Mem, chunksAt Mn.step m D (g * q) = (chunksAt Mw.step m D q).flatMap (split Mn.step g) :=
    fun m => by rw [chunksAt_group, hstw]
  have hlen : ∀ x ∈ xw, x.length = g * Mn.step := fun x hx => by
    rw [← hxw] at hx
    simp only [chunksAt, List.mem_map, List.mem_range] at hx
    obtain ⟨_, _, rfl⟩ := hx
    simp only [bytesAt, List.length_map, List.length_range, hstw]; rfl
  obtain ⟨rg1, rg2⟩ := run_group_blocks hFb iv xw hivl hlen
  -- The inputs: the groups' blocks, then the blocks left.
  have hxs' : xs = xw.flatMap (split Mn.step g) ++ xn := by
    have e := hI.data
    simp only [List.take_zero, run, List.nil_append, List.drop_zero] at e
    rw [← e, hsplit, hgroup, hxw, ← hxn,
      chunksAt_frame h₃.frame hdis₃ (by omega_using [hD'fit])]
  have hrun := run_append F iv (xw.flatMap (split Mn.step g)) xn
  rw [← rg2] at hrun
  refine ⟨d₄.b, fun r' hr h3 h2 => by rw [d₄.keep r' hr h3 h2, d₃.keep r' hr h3 h2], by rw [d₄.rd, d₃.rd],
    by rw [d₄.wr, d₃.wr], ?_, ?_, ?_⟩
  · rw [hxs', hrun, hsplit, d₄.data, chunksAt_frame d₄.frame hdis₄ (by omega_using [hDf, hwq, hwq']), hgroup,
      d₃.data, rg1]
  · have e₄ : bytesAt s₄.mem (slotA B c.chnSlot) (4 * c.bw) = _ := d₄.chn
    rw [hxs', hrun, e₄]
  · refine (d₃.frame.sub fun R hR => ?_).trans (d₄.frame.sub fun R hR => ?_)
    · simp only [big, List.mem_cons, List.not_mem_nil, or_false] at hR
      rcases hR with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
          Region.sub_prefix (by omega_using [hwq])⟩
    · simp only [big, List.mem_cons, List.not_mem_nil, or_false] at hR
      rcases hR with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), hsubN⟩

/-- The wide loops of `levels`, then `rest`. -/
theorem levels_ok {wide : Nat → Mode} {lgs : List Nat} {rest : Prog isa}
    (hw : ∀ lg ∈ lgs, WideOk cs Mn F k (wide (2 ^ lg)) lg) (hFb : Blockwise F Mn.step (4 * c.bw))
    (hrest : StepsOk cs Mn F k rest) : StepsOk cs Mn F k (c.levels wide lgs rest) := by
  induction lgs with
  | nil => exact hrest
  | cons lg lgs ih =>
    exact wideThen_ok cs (hw lg List.mem_cons_self) hFb (ih fun l hl => hw l (List.mem_cons_of_mem _ hl))

/-- The loops of `seqLevelsWith`: the levels' groups, then the blocks left on
`c.withOne one`. -/
theorem levelsWith_loops {wide : Nat → Mode} {lgs : List Nat} (hone : OneOk cs one)
    (hw : ∀ lg ∈ lgs, WideOk cs Mn F k (wide (2 ^ lg)) lg) (hFb : Blockwise F Mn.step (4 * c.bw))
    (hpre : ∀ o ∈ Mn.pre, o.InBounds (lens c Mn.step (4 * c.bw)))
    (hpost : ∀ o ∈ Mn.post, o.InBounds (lens c Mn.step (4 * c.bw)))
    (hcomp : Computes Mn (4 * c.bw) (cs.cipher k) F) :
    LoopsOk cs Mn F s₀ k (c.levels wide lgs ((c.withOne one).steps Mn)) := fun _ hFx hI =>
  levels_ok cs hw hFb (stepsOne_ok cs hone hpre hpost hcomp) hFx hI

/-- The loops of `seq2With`: the groups, then the blocks left on `c.withOne one`. -/
theorem wideStepsWith_ok (hone : OneOk cs one) (hlg : lg ≤ 15) (hG : 2 ^ lg ≤ c.G) (hstw : Mw.step = 2 ^ lg * Mn.step)
    (hstle : 2 ^ lg * Mn.step < 2 ^ 15)
    (hpreW : ∀ o ∈ Mw.pre, o.InBounds (lens c Mw.step (4 * c.bw * 2 ^ lg)))
    (hpostW : ∀ o ∈ Mw.post, o.InBounds (lens c Mw.step (4 * c.bw * 2 ^ lg)))
    (hcompW : ComputesB Mw (4 * c.bw) (4 * c.bw * 2 ^ lg) ciphB (group Mn.step (2 ^ lg) F))
    (hB : BufCipher c (cs.cipher k) ciphB (4 * c.bw * 2 ^ lg))
    (hFb : Blockwise F Mn.step (4 * c.bw))
    (hpre : ∀ o ∈ Mn.pre, o.InBounds (lens c Mn.step (4 * c.bw)))
    (hpost : ∀ o ∈ Mn.post, o.InBounds (lens c Mn.step (4 * c.bw)))
    (hcomp : Computes Mn (4 * c.bw) (cs.cipher k) F) :
    LoopsOk cs Mn F s₀ k (.seq (c.loopWide Mw lg) ((c.withOne one).steps Mn)) :=
  levelsWith_loops cs (wide := fun _ => Mw) (lgs := [lg]) hone
    (fun l hl => by
      obtain rfl : l = lg := List.mem_singleton.mp hl
      exact ⟨hlg, hG, hstw, hstle, hpreW, hpostW, ⟨ciphB, hcompW, hB⟩⟩)
    hFb hpre hpost hcomp

/-- The loops of `seq2`: the groups, then the blocks left. -/
theorem wideSteps_ok (hlg : lg ≤ 15) (hG : 2 ^ lg ≤ c.G) (hstw : Mw.step = 2 ^ lg * Mn.step)
    (hstle : 2 ^ lg * Mn.step < 2 ^ 15)
    (hpreW : ∀ o ∈ Mw.pre, o.InBounds (lens c Mw.step (4 * c.bw * 2 ^ lg)))
    (hpostW : ∀ o ∈ Mw.post, o.InBounds (lens c Mw.step (4 * c.bw * 2 ^ lg)))
    (hcompW : ComputesB Mw (4 * c.bw) (4 * c.bw * 2 ^ lg) ciphB (group Mn.step (2 ^ lg) F))
    (hB : BufCipher c (cs.cipher k) ciphB (4 * c.bw * 2 ^ lg))
    (hFb : Blockwise F Mn.step (4 * c.bw))
    (hpre : ∀ o ∈ Mn.pre, o.InBounds (lens c Mn.step (4 * c.bw)))
    (hpost : ∀ o ∈ Mn.post, o.InBounds (lens c Mn.step (4 * c.bw)))
    (hcomp : Computes Mn (4 * c.bw) (cs.cipher k) F) :
    LoopsOk cs Mn F s₀ k (.seq (c.loopWide Mw lg) (c.steps Mn)) := by
  rw [← withOne_steps]
  exact wideStepsWith_ok cs (OneOk.self cs) hlg hG hstw hstle hpreW hpostW hcompW hB hFb hpre hpost hcomp

end

/-- The core's block cipher on `g` blocks of its buffer. -/
theorem bufCipher_blocks {ciph : Spec.Cbc.Cipher} {g : Nat} (hg : g ≤ c.G) :
    BufCipher c ciph (blocksCipher (4 * c.bw) g ciph) (4 * c.bw * g) := fun B m m' h => by
  rw [Nat.mul_comm (4 * c.bw) g, blocksCipher, bytesAt_split, bytesAt_flatten]
  congr 1
  simp only [chunksAt, List.map_map]
  exact List.map_congr_left fun j hj => h j (Nat.lt_of_lt_of_le (List.mem_range.mp hj) hg)

section
variable (cs : CoreSpec c) {s₀ : State} {k : cs.Key} {lg : Nat}

/-- The function of `seq2`, as `seq_changes_wp`. -/
theorem seq2_changes_wp {Mw Mn : Mode} {F : StepFn} (hp : SeqPre c Mn s₀)
    (hloops : LoopsOk cs Mn F s₀ k (.seq (c.loopWide Mw lg) (c.steps Mn)))
    (hk : cs.KeyArgs s₀ (wrs0 c Mn s₀) k) :
    WP isa (c.seq2 Mw Mn lg) s₀ fun s' => abiPreserved s₀ s' ∧
      chunksAt Mn.step s'.mem (Dp s₀) (N s₀) = (run F (iv0 c s₀) (xs0 Mn s₀)).1 ∧
      (Mn.ivOut = true → bytesAt s'.mem (P s₀) (4 * c.bw) = (run F (iv0 c s₀) (xs0 Mn s₀)).2) ∧
      Changes c Mn s₀ s' :=
  seqWith_changes_wp cs hp hloops hk

theorem lens_wide (G : Nat) (l : Loc) (hl : l ≠ .chn) :
    4 * c.bw * G ≤ lens c (G * (4 * c.bw)) (4 * c.bw * G) l := by
  cases l <;> simp [lens, Nat.mul_comm] at hl ⊢

theorem cbcDecWide_ok (hlg : lg ≤ 15) (hG : 2 ^ lg ≤ c.G) (hstle : 2 ^ lg * (4 * c.bw) < 2 ^ 15) :
    WideOk cs (Mode.cbcDecChained c.bw) (cbcDecF (cs.cipher k)) k (Mode.cbcDecWide c.bw (2 ^ lg)) lg := by
  obtain ⟨hw1, hw2⟩ := cbcDecWide_inBounds (bw := c.bw) (len := lens c (2 ^ lg * (4 * c.bw)) (4 * c.bw * 2 ^ lg))
    (2 ^ lg) (lens_wide _ _ (by decide)) (lens_wide _ _ (by decide)) (by simp [lens])
  exact ⟨hlg, hG, rfl, hstle, hw1, hw2, ⟨_, cbcDecWide_computes (cs.cipher_len k) _, bufCipher_blocks hG⟩⟩

theorem cfbDecWide_ok (hlg : lg ≤ 15) (hG : 2 ^ lg ≤ c.G) (hstle : 2 ^ lg * (4 * c.bw) < 2 ^ 15) :
    WideOk cs (Mode.cfbDecEarly c.bw) (cfbDecF (cs.cipher k)) k (Mode.cfbDecWide c.bw (2 ^ lg)) lg := by
  obtain ⟨hw1, hw2⟩ := cfbDecWide_inBounds (bw := c.bw) (len := lens c (2 ^ lg * (4 * c.bw)) (4 * c.bw * 2 ^ lg))
    (2 ^ lg) (lens_wide _ _ (by decide)) (lens_wide _ _ (by decide)) (by simp [lens])
  exact ⟨hlg, hG, rfl, hstle, hw1, hw2, ⟨_, cfbDecWide_computes (cs.cipher_len k) _, bufCipher_blocks hG⟩⟩

/-- What a level of `lgs` needs: groups of at most `G` blocks, of at most
`2 ^ 15` bytes. -/
abbrev LevelsFit (c : Core) (lgs : List Nat) : Prop :=
  ∀ lg ∈ lgs, lg ≤ 15 ∧ 2 ^ lg ≤ c.G ∧ 2 ^ lg * (4 * c.bw) < 2 ^ 15

theorem cbcDecLevelsWith_loops {one : Prog isa} {lgs : List Nat} (hone : OneOk cs one) (hfit : LevelsFit c lgs) :
    LoopsOk cs (Mode.cbcDecChained c.bw) (cbcDecF (cs.cipher k)) s₀ k
      (c.levels (Mode.cbcDecWide c.bw) lgs ((c.withOne one).steps (Mode.cbcDecChained c.bw))) := by
  have b := blk_bounds (c := c) (st := (Mode.cbcDecChained c.bw).step) rfl
  exact levelsWith_loops cs hone (fun lg hl => cbcDecWide_ok cs (hfit lg hl).1 (hfit lg hl).2.1 (hfit lg hl).2.2)
    (cbcDecF_blockwise (cs.cipher_len k)) (copyBlk_inBounds (b _) (b _))
    (append_ok (append_ok (xorBlk_inBounds (b _) (b _) (b _)) (copyBlk_inBounds (b _) (b _)))
      (copyBlk_inBounds (b _) (b _)))
    (cbcDecChained_computes (cs.cipher_len k))

theorem cfbDecLevelsWith_loops {one : Prog isa} {lgs : List Nat} (hone : OneOk cs one) (hfit : LevelsFit c lgs) :
    LoopsOk cs (Mode.cfbDecEarly c.bw) (cfbDecF (cs.cipher k)) s₀ k
      (c.levels (Mode.cfbDecWide c.bw) lgs ((c.withOne one).steps (Mode.cfbDecEarly c.bw))) := by
  have b := blk_bounds (c := c) (st := (Mode.cfbDecEarly c.bw).step) rfl
  exact levelsWith_loops cs hone (fun lg hl => cfbDecWide_ok cs (hfit lg hl).1 (hfit lg hl).2.1 (hfit lg hl).2.2)
    (cfbDecF_blockwise (cs.cipher_len k))
    (append_ok (copyBlk_inBounds (b _) (b _)) (copyBlk_inBounds (b _) (b _))) (xorBlk_inBounds (b _) (b _) (b _))
    (cfbDecEarly_computes (cs.cipher_len k))

theorem cbcDecWideWith_loops {one : Prog isa} (hone : OneOk cs one) (hlg : lg ≤ 15) (hG : 2 ^ lg ≤ c.G)
    (hstle : 2 ^ lg * (4 * c.bw) < 2 ^ 15) :
    LoopsOk cs (Mode.cbcDecChained c.bw) (cbcDecF (cs.cipher k)) s₀ k
      (.seq (c.loopWide (Mode.cbcDecWide c.bw (2 ^ lg)) lg) ((c.withOne one).steps (Mode.cbcDecChained c.bw))) :=
  cbcDecLevelsWith_loops cs (lgs := [lg]) hone fun _ h => by
    obtain rfl := List.mem_singleton.mp h; exact ⟨hlg, hG, hstle⟩

theorem cfbDecWideWith_loops {one : Prog isa} (hone : OneOk cs one) (hlg : lg ≤ 15) (hG : 2 ^ lg ≤ c.G)
    (hstle : 2 ^ lg * (4 * c.bw) < 2 ^ 15) :
    LoopsOk cs (Mode.cfbDecEarly c.bw) (cfbDecF (cs.cipher k)) s₀ k
      (.seq (c.loopWide (Mode.cfbDecWide c.bw (2 ^ lg)) lg) ((c.withOne one).steps (Mode.cfbDecEarly c.bw))) :=
  cfbDecLevelsWith_loops cs (lgs := [lg]) hone fun _ h => by
    obtain rfl := List.mem_singleton.mp h; exact ⟨hlg, hG, hstle⟩

/-- CBC decryption, `2 ^ lg` blocks at a time. -/
theorem cbcDecWide_wp (hlg : lg ≤ 15) (hG : 2 ^ lg ≤ c.G) (hstle : 2 ^ lg * (4 * c.bw) < 2 ^ 15)
    (hp : SeqPre c (Mode.cbcDecChained c.bw) s₀) (hk : cs.KeyArgs s₀ (wrs0 c (Mode.cbcDecChained c.bw) s₀) k) :
    WP isa (c.seq2 (Mode.cbcDecWide c.bw (2 ^ lg)) (Mode.cbcDecChained c.bw) lg) s₀ fun s' => abiPreserved s₀ s' ∧
      chunksAt (4 * c.bw) s'.mem (Dp s₀) (N s₀) = Spec.Cbc.decrypt (cs.cipher k) (iv0 c s₀) (blocks0 (c := c) s₀) ∧
      bytesAt s'.mem (P s₀) (4 * c.bw) = Spec.Cbc.next (iv0 c s₀) (blocks0 (c := c) s₀) ∧
      Changes c (Mode.cbcDecChained c.bw) s₀ s' :=
  WP.mono (seq2_changes_wp cs hp (cbcDecWideWith_loops cs (OneOk.self cs) hlg hG hstle) hk)
    fun s' ⟨h1, h2, h3, h4⟩ =>
    ⟨h1, h2.trans (by rw [decrypt_run]; rfl), by rw [h3 rfl, decrypt_run_next]; rfl, h4⟩

/-- CBC decryption, `2 ^ lg` blocks at a time, and the blocks left by `one`. -/
theorem cbcDecWideWith_wp {one : Prog isa} (hone : OneOk cs one) (hlg : lg ≤ 15) (hG : 2 ^ lg ≤ c.G)
    (hstle : 2 ^ lg * (4 * c.bw) < 2 ^ 15)
    (hp : SeqPre c (Mode.cbcDecChained c.bw) s₀) (hk : cs.KeyArgs s₀ (wrs0 c (Mode.cbcDecChained c.bw) s₀) k) :
    WP isa (c.seq2With one (Mode.cbcDecWide c.bw (2 ^ lg)) (Mode.cbcDecChained c.bw) lg) s₀ fun s' =>
      abiPreserved s₀ s' ∧
      chunksAt (4 * c.bw) s'.mem (Dp s₀) (N s₀) = Spec.Cbc.decrypt (cs.cipher k) (iv0 c s₀) (blocks0 (c := c) s₀) ∧
      bytesAt s'.mem (P s₀) (4 * c.bw) = Spec.Cbc.next (iv0 c s₀) (blocks0 (c := c) s₀) ∧
      Changes c (Mode.cbcDecChained c.bw) s₀ s' :=
  WP.mono (seqWith_changes_wp cs hp (cbcDecWideWith_loops cs hone hlg hG hstle) hk) fun s' ⟨h1, h2, h3, h4⟩ =>
    ⟨h1, h2.trans (by rw [decrypt_run]; rfl), by rw [h3 rfl, decrypt_run_next]; rfl, h4⟩

/-- CFB decryption, `2 ^ lg` blocks at a time. -/
theorem cfbDecWide_wp (hlg : lg ≤ 15) (hG : 2 ^ lg ≤ c.G) (hstle : 2 ^ lg * (4 * c.bw) < 2 ^ 15)
    (hp : SeqPre c (Mode.cfbDecEarly c.bw) s₀) (hk : cs.KeyArgs s₀ (wrs0 c (Mode.cfbDecEarly c.bw) s₀) k) :
    WP isa (c.seq2 (Mode.cfbDecWide c.bw (2 ^ lg)) (Mode.cfbDecEarly c.bw) lg) s₀ fun s' => abiPreserved s₀ s' ∧
      chunksAt (4 * c.bw) s'.mem (Dp s₀) (N s₀) = Spec.Cfb.decrypt (cs.cipher k) (iv0 c s₀) (blocks0 (c := c) s₀) ∧
      bytesAt s'.mem (P s₀) (4 * c.bw) = Spec.Cbc.next (iv0 c s₀) (blocks0 (c := c) s₀) ∧
      Changes c (Mode.cfbDecEarly c.bw) s₀ s' :=
  WP.mono (seq2_changes_wp cs hp (cfbDecWideWith_loops cs (OneOk.self cs) hlg hG hstle) hk)
    fun s' ⟨h1, h2, h3, h4⟩ =>
    ⟨h1, h2.trans (by rw [(cfbDec_run _ _ _).1]; rfl), by rw [h3 rfl, (cfbDec_run _ _ _).2]; rfl, h4⟩

/-- CFB decryption, `2 ^ lg` blocks at a time, and the blocks left by `one`. -/
theorem cfbDecWideWith_wp {one : Prog isa} (hone : OneOk cs one) (hlg : lg ≤ 15) (hG : 2 ^ lg ≤ c.G)
    (hstle : 2 ^ lg * (4 * c.bw) < 2 ^ 15)
    (hp : SeqPre c (Mode.cfbDecEarly c.bw) s₀) (hk : cs.KeyArgs s₀ (wrs0 c (Mode.cfbDecEarly c.bw) s₀) k) :
    WP isa (c.seq2With one (Mode.cfbDecWide c.bw (2 ^ lg)) (Mode.cfbDecEarly c.bw) lg) s₀ fun s' =>
      abiPreserved s₀ s' ∧
      chunksAt (4 * c.bw) s'.mem (Dp s₀) (N s₀) = Spec.Cfb.decrypt (cs.cipher k) (iv0 c s₀) (blocks0 (c := c) s₀) ∧
      bytesAt s'.mem (P s₀) (4 * c.bw) = Spec.Cbc.next (iv0 c s₀) (blocks0 (c := c) s₀) ∧
      Changes c (Mode.cfbDecEarly c.bw) s₀ s' :=
  WP.mono (seqWith_changes_wp cs hp (cfbDecWideWith_loops cs hone hlg hG hstle) hk) fun s' ⟨h1, h2, h3, h4⟩ =>
    ⟨h1, h2.trans (by rw [(cfbDec_run _ _ _).1]; rfl), by rw [h3 rfl, (cfbDec_run _ _ _).2]; rfl, h4⟩

/-- CBC decryption, by groups of `2 ^ lg` blocks for each `lg` of `lgs` in
turn, then the blocks left by `one`. -/
theorem cbcDecLevelsWith_wp {one : Prog isa} {lgs : List Nat} (hone : OneOk cs one) (hfit : LevelsFit c lgs)
    (hp : SeqPre c (Mode.cbcDecChained c.bw) s₀) (hk : cs.KeyArgs s₀ (wrs0 c (Mode.cbcDecChained c.bw) s₀) k) :
    WP isa (c.seqLevelsWith one (Mode.cbcDecWide c.bw) lgs (Mode.cbcDecChained c.bw)) s₀ fun s' =>
      abiPreserved s₀ s' ∧
      chunksAt (4 * c.bw) s'.mem (Dp s₀) (N s₀) = Spec.Cbc.decrypt (cs.cipher k) (iv0 c s₀) (blocks0 (c := c) s₀) ∧
      bytesAt s'.mem (P s₀) (4 * c.bw) = Spec.Cbc.next (iv0 c s₀) (blocks0 (c := c) s₀) ∧
      Changes c (Mode.cbcDecChained c.bw) s₀ s' :=
  WP.mono (seqWith_changes_wp cs hp (cbcDecLevelsWith_loops cs hone hfit) hk) fun s' ⟨h1, h2, h3, h4⟩ =>
    ⟨h1, h2.trans (by rw [decrypt_run]; rfl), by rw [h3 rfl, decrypt_run_next]; rfl, h4⟩

/-- CFB decryption, by groups of `2 ^ lg` blocks for each `lg` of `lgs` in
turn, then the blocks left by `one`. -/
theorem cfbDecLevelsWith_wp {one : Prog isa} {lgs : List Nat} (hone : OneOk cs one) (hfit : LevelsFit c lgs)
    (hp : SeqPre c (Mode.cfbDecEarly c.bw) s₀) (hk : cs.KeyArgs s₀ (wrs0 c (Mode.cfbDecEarly c.bw) s₀) k) :
    WP isa (c.seqLevelsWith one (Mode.cfbDecWide c.bw) lgs (Mode.cfbDecEarly c.bw)) s₀ fun s' =>
      abiPreserved s₀ s' ∧
      chunksAt (4 * c.bw) s'.mem (Dp s₀) (N s₀) = Spec.Cfb.decrypt (cs.cipher k) (iv0 c s₀) (blocks0 (c := c) s₀) ∧
      bytesAt s'.mem (P s₀) (4 * c.bw) = Spec.Cbc.next (iv0 c s₀) (blocks0 (c := c) s₀) ∧
      Changes c (Mode.cfbDecEarly c.bw) s₀ s' :=
  WP.mono (seqWith_changes_wp cs hp (cfbDecLevelsWith_loops cs hone hfit) hk) fun s' ⟨h1, h2, h3, h4⟩ =>
    ⟨h1, h2.trans (by rw [(cfbDec_run _ _ _).1]; rfl), by rw [h3 rfl, (cfbDec_run _ _ _).2]; rfl, h4⟩

/-! ## Counter mode -/

/-- The loops of `seq2` over counter mode with the counter block stepped by
`o` before the block cipher. -/
theorem ctrEarlyWide_loops {o : Op} {g : List Byte → List Byte} (hbw : c.bw = 4) (hg : IncOp o g)
    (hsh : ∀ L st j, Op.shift L st j o = o) (hgl : ∀ c, c.length = 16 → (g c).length = 16)
    (ho : ∀ len : Loc → Nat, 16 ≤ len .chn → o.InBounds len)
    (hlg : lg ≤ 15) (hG : 2 ^ lg ≤ c.G) (hstle : 2 ^ lg * 16 < 2 ^ 15) :
    LoopsOk cs (Mode.ctrEarlyWith o) (ctrStep (cs.cipher k) g) s₀ k
      (.seq (c.loopWide (Mode.widen (2 ^ lg) 16 (Mode.ctrEarlyWith o)) lg) (c.steps (Mode.ctrEarlyWith o))) := by
  have e4 : 4 * c.bw = 16 := by rw [hbw]
  have hc : ∀ x, (cs.cipher k x).length = 16 := fun x => by rw [cs.cipher_len, e4]
  obtain ⟨hw1, hw2⟩ := ctrWide_inBounds (len := lens c (2 ^ lg * 16) (4 * c.bw * 2 ^ lg)) hsh
    (ho _ (by simp [lens, e4])) (2 ^ lg) (by simp [lens, Nat.mul_comm]) (by simp [lens, e4])
    (by simp [lens, e4])
  obtain ⟨hn1, hn2⟩ := ctrEarly_inBounds (len := lens c 16 (4 * c.bw)) (ho _ (by simp [lens, e4]))
    (by simp [lens]) (by simp [lens, e4]) (by simp [lens, e4])
  have hcw := ctrWide_computes hc hg hsh hgl (2 ^ lg)
  have hB := bufCipher_blocks (c := c) (ciph := cs.cipher k) hG
  rw [e4] at hB
  exact wideSteps_ok cs hlg hG rfl hstle hw1 hw2 (by rw [e4]; exact hcw) (by rw [e4]; exact hB)
    (by rw [e4]; exact ctrStep_blockwise hc hgl) hn1 hn2 (by rw [e4]; exact ctrEarly_computes hc hg hgl)

/-- Counter mode, `2 ^ lg` blocks at a time. -/
theorem ctrWide_wp (hbw : c.bw = 4) (hlg : lg ≤ 15) (hG : 2 ^ lg ≤ c.G) (hstle : 2 ^ lg * 16 < 2 ^ 15)
    (hp : SeqPre c Mode.ctrEarly s₀) (hk : cs.KeyArgs s₀ (wrs0 c Mode.ctrEarly s₀) k) :
    WP isa (c.seq2 (Mode.ctrWide (2 ^ lg)) Mode.ctrEarly lg) s₀ fun s' => abiPreserved s₀ s' ∧
      chunksAt (4 * c.bw) s'.mem (Dp s₀) (N s₀) =
        Spec.Ctr.crypt (cs.cipher k) (iv0 c s₀) (blocks0 (c := c) s₀) ∧
      bytesAt s'.mem (P s₀) (4 * c.bw) = Spec.Ctr.next (iv0 c s₀) (N s₀) ∧
      Changes c Mode.ctrEarly s₀ s' :=
  WP.mono (seq2_changes_wp cs hp (ctrEarlyWide_loops cs hbw incOp_ctr (fun _ _ _ => rfl) inc_length
    (fun len h => ⟨by simpa [Op.width, Mode.ctrInc] using h, by simpa [Op.width, Mode.ctrInc] using h,
      fun _ _ h => by cases h⟩) hlg hG hstle) hk) fun s' ⟨h1, h2, h3, h4⟩ =>
    ⟨h1, by simpa [hbw, Mode.ctrEarly, Mode.ctrEarlyWith, xs0, blocks0, ← ctrF_eq] using
        h2.trans (ctr_run _ _ _).1.symm,
      by rw [h3 rfl, ← ctrF_eq, ← (ctr_run _ _ _).2, xs0, chunksAt_length], h4⟩

/-- Counter mode with GCM's `inc₃₂`, `2 ^ lg` blocks at a time. -/
theorem ctr32Wide_wp (hbw : c.bw = 4) (hlg : lg ≤ 15) (hG : 2 ^ lg ≤ c.G) (hstle : 2 ^ lg * 16 < 2 ^ 15)
    (hp : SeqPre c Mode.ctr32Early s₀) (hk : cs.KeyArgs s₀ (wrs0 c Mode.ctr32Early s₀) k) :
    WP isa (c.seq2 (Mode.ctr32Wide (2 ^ lg)) Mode.ctr32Early lg) s₀ fun s' => abiPreserved s₀ s' ∧
      (chunksAt (4 * c.bw) s'.mem (Dp s₀) (N s₀)).map Spec.Gcm.ofBytes =
        Spec.Gcm.ctr32 (onBlocks (cs.cipher k)) (Spec.Gcm.ofBytes (iv0 c s₀))
          ((blocks0 (c := c) s₀).map Spec.Gcm.ofBytes) ∧
      Spec.Gcm.ofBytes (bytesAt s'.mem (P s₀) (4 * c.bw)) =
        Nat.repeat Spec.Gcm.inc32 (N s₀) (Spec.Gcm.ofBytes (iv0 c s₀)) ∧
      Changes c Mode.ctr32Early s₀ s' := by
  have hc : ∀ x, (cs.cipher k x).length = 16 := by simpa [hbw] using cs.cipher_len k
  have ht : (iv0 c s₀).length = 16 := by simp [iv0, bytesAt, hbw]
  have hx : ∀ x ∈ blocks0 (c := c) s₀, x.length = 16 := by
    intro x hx
    simp only [blocks0, chunksAt, List.mem_map, List.mem_range] at hx
    obtain ⟨j, -, rfl⟩ := hx
    simp [bytesAt, hbw]
  obtain ⟨g1, g2⟩ := ctr32_gcm hc ht hx
  have e : xs0 Mode.ctr32Early s₀ = blocks0 (c := c) s₀ := by
    simp [xs0, blocks0, Mode.ctr32Early, Mode.ctrEarlyWith, hbw]
  have es : Mode.ctr32Early.step = 4 * c.bw := by simp [Mode.ctr32Early, Mode.ctrEarlyWith, hbw]
  refine WP.mono (seq2_changes_wp cs hp (ctrEarlyWide_loops cs hbw incOp_ctr32 (fun _ _ _ => rfl) inc32B_length
    (fun len h => ⟨by simp [Op.width, Mode.ctr32Inc]; omega_using [h], by simp [Op.width, Mode.ctr32Inc]; omega_using [h],
      fun _ _ h => by cases h⟩) hlg hG hstle) hk)
    fun s' ⟨h1, h2, h3, h4⟩ => ⟨h1, ?_, ?_, h4⟩
  · rw [← es, h2, e, ← ctr32F_eq]; exact g1
  · rw [h3 rfl, e, ← ctr32F_eq, g2, blocks0, chunksAt_length]

/-- CFB decryption, one block a step: `cfbDec_wp`, and what it changes. -/
theorem cfbDecSeq_wp (hp : SeqPre c (Mode.cfbDec c.bw) s₀) (hk : cs.KeyArgs s₀ (wrs0 c (Mode.cfbDec c.bw) s₀) k) :
    WP isa (c.seq (Mode.cfbDec c.bw)) s₀ fun s' => abiPreserved s₀ s' ∧
      chunksAt (4 * c.bw) s'.mem (Dp s₀) (N s₀) = Spec.Cfb.decrypt (cs.cipher k) (iv0 c s₀) (blocks0 (c := c) s₀) ∧
      bytesAt s'.mem (P s₀) (4 * c.bw) = Spec.Cbc.next (iv0 c s₀) (blocks0 (c := c) s₀) ∧
      Changes c (Mode.cfbDec c.bw) s₀ s' := by
  have b := blk_bounds (c := c) (st := (Mode.cfbDec c.bw).step) rfl
  refine WP.mono (seq_changes_wp cs hp ((copyBlk_inBounds (b _) (b _)))
    ((append_ok (copyBlk_inBounds (b _) (b _)) (xorBlk_inBounds (b _) (b _) (b _))))
    (cfbDec_computes (cs.cipher_len k)) hk) fun s' ⟨h1, h2, h3, h4⟩ => ⟨h1, ?_, ?_, h4⟩
  · exact h2.trans (by rw [(cfbDec_run _ _ _).1]; rfl)
  · rw [h3 rfl, (cfbDec_run _ _ _).2]; rfl

/-- CBC decryption, one block a step: `cbcDecChained_wp`'s conclusions and
what it changes. -/
theorem cbcDecSeq_wp (hp : SeqPre c (Mode.cbcDecChained c.bw) s₀)
    (hk : cs.KeyArgs s₀ (wrs0 c (Mode.cbcDecChained c.bw) s₀) k) :
    WP isa (c.seq (Mode.cbcDecChained c.bw)) s₀ fun s' => abiPreserved s₀ s' ∧
      chunksAt (4 * c.bw) s'.mem (Dp s₀) (N s₀) = Spec.Cbc.decrypt (cs.cipher k) (iv0 c s₀) (blocks0 (c := c) s₀) ∧
      bytesAt s'.mem (P s₀) (4 * c.bw) = Spec.Cbc.next (iv0 c s₀) (blocks0 (c := c) s₀) ∧
      Changes c (Mode.cbcDecChained c.bw) s₀ s' := by
  have b := blk_bounds (c := c) (st := (Mode.cbcDecChained c.bw).step) rfl
  refine WP.mono (seq_changes_wp cs hp ((copyBlk_inBounds (b _) (b _)))
    ((append_ok (append_ok (xorBlk_inBounds (b _) (b _) (b _)) (copyBlk_inBounds (b _) (b _)))
        (copyBlk_inBounds (b _) (b _))))
    (cbcDecChained_computes (cs.cipher_len k)) hk) fun s' ⟨h1, h2, h3, h4⟩ => ⟨h1, ?_, ?_, h4⟩
  · exact h2.trans (by rw [decrypt_run]; rfl)
  · rw [h3 rfl, decrypt_run_next]; rfl

/-- The loop of `seq` over counter mode, one block a step. -/
theorem ctrEarly_loops {o : Op} {g : List Byte → List Byte} (hbw : c.bw = 4) (hg : IncOp o g)
    (hgl : ∀ c, c.length = 16 → (g c).length = 16) (ho : ∀ len : Loc → Nat, 16 ≤ len .chn → o.InBounds len) :
    LoopsOk cs (Mode.ctrEarlyWith o) (ctrStep (cs.cipher k) g) s₀ k (c.steps (Mode.ctrEarlyWith o)) := by
  have e4 : 4 * c.bw = 16 := by rw [hbw]
  have hc : ∀ x, (cs.cipher k x).length = 16 := fun x => by rw [cs.cipher_len, e4]
  obtain ⟨hn1, hn2⟩ := ctrEarly_inBounds (len := lens c 16 (4 * c.bw)) (ho _ (by simp [lens, e4]))
    (by simp [lens]) (by simp [lens, e4]) (by simp [lens, e4])
  exact steps_ok cs hn1 hn2 (by rw [e4]; exact ctrEarly_computes hc hg hgl)

/-- Counter mode, one block a step: `ctrWide_wp`'s conclusions, of `seq`. -/
theorem ctrSeq_wp (hbw : c.bw = 4) (hp : SeqPre c Mode.ctrEarly s₀)
    (hk : cs.KeyArgs s₀ (wrs0 c Mode.ctrEarly s₀) k) :
    WP isa (c.seq Mode.ctrEarly) s₀ fun s' => abiPreserved s₀ s' ∧
      chunksAt (4 * c.bw) s'.mem (Dp s₀) (N s₀) =
        Spec.Ctr.crypt (cs.cipher k) (iv0 c s₀) (blocks0 (c := c) s₀) ∧
      bytesAt s'.mem (P s₀) (4 * c.bw) = Spec.Ctr.next (iv0 c s₀) (N s₀) ∧
      Changes c Mode.ctrEarly s₀ s' :=
  WP.mono (seqWith_changes_wp cs hp (ctrEarly_loops cs hbw incOp_ctr inc_length
    (fun len h => ⟨by simpa [Op.width, Mode.ctrInc] using h, by simpa [Op.width, Mode.ctrInc] using h,
      fun _ _ h => by cases h⟩)) hk) fun s' ⟨h1, h2, h3, h4⟩ =>
    ⟨h1, by simpa [hbw, Mode.ctrEarly, Mode.ctrEarlyWith, xs0, blocks0, ← ctrF_eq] using
        h2.trans (ctr_run _ _ _).1.symm,
      by rw [h3 rfl, ← ctrF_eq, ← (ctr_run _ _ _).2, xs0, chunksAt_length], h4⟩

/-- Counter mode with GCM's `inc₃₂`, one block a step: `ctr32Wide_wp`'s
conclusions, of `seq`. -/
theorem ctr32Seq_wp (hbw : c.bw = 4) (hp : SeqPre c Mode.ctr32Early s₀)
    (hk : cs.KeyArgs s₀ (wrs0 c Mode.ctr32Early s₀) k) :
    WP isa (c.seq Mode.ctr32Early) s₀ fun s' => abiPreserved s₀ s' ∧
      (chunksAt (4 * c.bw) s'.mem (Dp s₀) (N s₀)).map Spec.Gcm.ofBytes =
        Spec.Gcm.ctr32 (onBlocks (cs.cipher k)) (Spec.Gcm.ofBytes (iv0 c s₀))
          ((blocks0 (c := c) s₀).map Spec.Gcm.ofBytes) ∧
      Spec.Gcm.ofBytes (bytesAt s'.mem (P s₀) (4 * c.bw)) =
        Nat.repeat Spec.Gcm.inc32 (N s₀) (Spec.Gcm.ofBytes (iv0 c s₀)) ∧
      Changes c Mode.ctr32Early s₀ s' := by
  have hc : ∀ x, (cs.cipher k x).length = 16 := by simpa [hbw] using cs.cipher_len k
  have ht : (iv0 c s₀).length = 16 := by simp [iv0, bytesAt, hbw]
  have hx : ∀ x ∈ blocks0 (c := c) s₀, x.length = 16 := by
    intro x hx
    simp only [blocks0, chunksAt, List.mem_map, List.mem_range] at hx
    obtain ⟨j, -, rfl⟩ := hx
    simp [bytesAt, hbw]
  obtain ⟨g1, g2⟩ := ctr32_gcm hc ht hx
  have e : xs0 Mode.ctr32Early s₀ = blocks0 (c := c) s₀ := by
    simp [xs0, blocks0, Mode.ctr32Early, Mode.ctrEarlyWith, hbw]
  have es : Mode.ctr32Early.step = 4 * c.bw := by simp [Mode.ctr32Early, Mode.ctrEarlyWith, hbw]
  refine WP.mono (seqWith_changes_wp cs hp (ctrEarly_loops cs hbw incOp_ctr32 inc32B_length
    (fun len h => ⟨by simp [Op.width, Mode.ctr32Inc]; omega_using [h], by simp [Op.width, Mode.ctr32Inc]; omega_using [h],
      fun _ _ h => by cases h⟩)) hk)
    fun s' ⟨h1, h2, h3, h4⟩ => ⟨h1, ?_, ?_, h4⟩
  · rw [← es, h2, e, ← ctr32F_eq]; exact g1
  · rw [h3 rfl, e, ← ctr32F_eq, g2, blocks0, chunksAt_length]

end

/-! ## Short messages -/

/-- `r8` is not callee-saved. -/
theorem abiPreserved_r8 {s s' : State} {v : BitVec 64} (h : abiPreserved (s.write .r8 v) s') :
    abiPreserved s s' := by
  have ne : ∀ r ∈ preserved, r ≠ .r8 := by decide
  exact ⟨fun r hr => (h.1 r hr).trans (by simp only [State.write, ne r hr, ↓reduceIte]), h.2.1, h.2.2⟩

/-- The modes' arguments are not `r8`. -/
theorem args_write_r8 (s : State) (v : BitVec 64) :
    S (s.write .r8 v) = S s ∧ P (s.write .r8 v) = P s ∧ Dp (s.write .r8 v) = Dp s ∧ N (s.write .r8 v) = N s ∧
      (s.write .r8 v).mem = s.mem ∧ (s.write .r8 v).rd = s.rd ∧ (s.write .r8 v).wr = s.wr :=
  ⟨RegUpd.gpr_write_of_ne _ _ (by decide), RegUpd.gpr_write_of_ne _ _ (by decide),
    RegUpd.gpr_write_of_ne _ _ (by decide), by simp only [N, RegUpd.gpr_write_of_ne _ _ (show ¬ Reg.r6 = .r8 by decide)],
    rfl, rfl, rfl⟩

theorem SeqPre.write_r8 {M : Mode} {s : State} (hp : SeqPre c M s) (v : BitVec 64) :
    SeqPre c M (s.write .r8 v) := by
  obtain ⟨eS, eP, eD, eN, -, erd, ewr⟩ := args_write_r8 s v
  obtain ⟨⟨h1, h1'⟩, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hp
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h10, h11⟩ <;>
    simp only [ivR, scrRegion, dataRegion, eS, eP, eD, eN, erd, ewr] <;> with_reducible assumption

theorem Changes.write_r8 {M : Mode} {s s' : State} {v : BitVec 64} (h : Changes c M (s.write .r8 v) s') :
    Changes c M s s' := by
  obtain ⟨eS, eP, eD, eN, em, -, -⟩ := args_write_r8 s v
  obtain ⟨h1, h2⟩ := h
  refine ⟨by rw [h1, eS], ?_⟩
  simpa only [ivR, dataRegion, eS, eP, eD, eN, em] using h2

/-- What a function changes depends on its core only through its slots and
block, and on its mode through its step. -/
theorem Changes.congr {c₂ : Core} {M₁ M₂ : Mode} {s s' : State} (h : Changes c M₁ s s')
    (hsl : c.slots = c₂.slots) (hbw : c.bw = c₂.bw) (hst : M₁.step = M₂.step) : Changes c₂ M₂ s s' := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨h1, by simpa only [coreRegion, modeR, ivR, dataRegion, hsl, hbw, hst] using h2⟩

theorem pick_wp {lg : Nat} (hlg : lg < 64) {short long : Prog isa} {s : State} {Q : State → Prop}
    (hs : s.gpr .r6 >>> lg = 0 → WP isa short (s.write .r8 (s.gpr .r6 >>> lg)) Q)
    (hl : s.gpr .r6 >>> lg ≠ 0 → WP isa long (s.write .r8 (s.gpr .r6 >>> lg)) Q) :
    WP isa (pick lg short long) s Q := by
  unfold pick
  refine WP.seq (WP.of_runBlock ⟨_, by rw [runBlock_cons, exec_lsr_d hlg, runStep_some, runBlock_nil], ?_⟩)
  have e : (s.write .r8 (s.gpr .r6 >>> lg)).read .d .r8 = s.gpr .r6 >>> lg := by
    simp only [State.read, State.write, ↓reduceIte, Size.bits, BitVec.setWidth_eq]
  refine WP.ite _ rfl (fun h => hs ?_) (fun h => hl ?_)
  · rw [← e]; simpa using h
  · rw [← e]; simpa using h

end VG.Proof.Modes.PPC64LE
