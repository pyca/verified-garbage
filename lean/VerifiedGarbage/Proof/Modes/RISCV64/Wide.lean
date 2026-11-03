module
-- separate module: every RISC-V core's batched modes, as `Modes.lean` has the one-block ones

public import VerifiedGarbage.Proof.Modes.RISCV64.Seq
public import VerifiedGarbage.Proof.Modes.Wide
public import VerifiedGarbage.Proof.Modes.RISCV64.Modes
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Modes.StepsChained
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Block cipher modes on RISC-V, a group of blocks at a time

`wideSteps_ok`: the loops of `Core.seq2` (`Impl/Modes/RISCV64/Wide.lean`)
take all the steps of the mode `Mn`, one block of `st` bytes each, as
`Core.steps Mn` does (`LoopsOk`): the steps of `Mw`, each of a group of
`g = 2 ^ lg` blocks, which compute `group st g F` (`loopWide_wp`), while
a group is left, then those of `Mn` (`loop_wp`) for the rest. The data
splits at the first `g q` blocks (`q = n / g`): running `group st g F` on
the groups is running `F` on their blocks (`run_group_blocks`), and `F`
goes on from where the groups left the chaining value (`run_append`).
`seq2_changes_wp`: the function, as `seq_changes_wp`.
-/

@[expose] public section

namespace VG.Proof.Modes.RISCV64

open VG VG.RISCV64 VG.Impl.Modes VG.Impl.Modes.RISCV64
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

/-- A widened mode's words, at multiples of 4 if its blocks' are. -/
theorem widen_wordAl {os : List Op} {L st G : Nat} (h : ∀ o ∈ os, WordAl o) (hL : L % 4 = 0) (hst : st % 4 = 0) :
    ∀ o ∈ (List.range G).flatMap (fun j => os.map (Op.shift L st j)), WordAl o := by
  intro o ho hw
  simp only [List.mem_flatMap, List.mem_range, List.mem_map] at ho
  obtain ⟨j, -, o', ho', rfl⟩ := ho
  obtain ⟨hd, hs, hx⟩ := h o' ho' hw
  have sh : ∀ l, shOff L st j l % 4 = 0 := fun l => by
    cases l <;> simp only [shOff, Nat.mul_mod, hL, hst, Nat.zero_mul, Nat.zero_mod]
  refine ⟨by simp only [Op.shift]; omega_using [hd, sh o'.dst],
    by simp only [Op.shift]; omega_using [hs, sh o'.src], fun l off e => ?_⟩
  simp only [Op.shift, Option.map_eq_some_iff] at e
  obtain ⟨⟨l', off'⟩, e', he⟩ := e
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have := hx l' off' e'
  omega_using [this, sh l']

section
variable (cs : CoreSpec c) {Mw Mn : Mode} {F : StepFn} {s₀ : State} {k : cs.Key} {lg : Nat}
  {ciphB : Spec.Cbc.Cipher}

/-- The loops of `seq2`: the groups, then the blocks left. -/
theorem wideSteps_ok (hlg : lg ≤ 11) (hG : 2 ^ lg ≤ c.G) (hstw : Mw.step = 2 ^ lg * Mn.step)
    (hstle : 2 ^ lg * Mn.step ≤ 2032)
    (hpreW : ∀ o ∈ Mw.pre, o.InBounds (lens c Mw.step (4 * c.bw * 2 ^ lg)))
    (hpostW : ∀ o ∈ Mw.post, o.InBounds (lens c Mw.step (4 * c.bw * 2 ^ lg)))
    (hcompW : ComputesB Mw (4 * c.bw) (4 * c.bw * 2 ^ lg) ciphB (group Mn.step (2 ^ lg) F))
    (hB : BufCipher c (cs.cipher k) ciphB (4 * c.bw * 2 ^ lg))
    (hFb : Blockwise F Mn.step (4 * c.bw))
    (hpre : ∀ o ∈ Mn.pre, o.InBounds (lens c Mn.step (4 * c.bw)))
    (hpost : ∀ o ∈ Mn.post, o.InBounds (lens c Mn.step (4 * c.bw)))
    (hcomp : Computes Mn (4 * c.bw) (cs.cipher k) F) {w : Bool}
    (hpreWA : ∀ o ∈ Mw.pre, WordAl o) (hpostWA : ∀ o ∈ Mw.post, WordAl o)
    (hpreA : ∀ o ∈ Mn.pre, WordAl o) (hpostA : ∀ o ∈ Mn.post, WordAl o)
    (hD : w = true → (Dp s₀).toNat % 4 = 0 ∧ Mn.step % 4 = 0) :
    LoopsOk cs Mn F s₀ k (.seq (c.loopWide w Mw lg) (c.steps w Mn)) := by
  intro s₂ hFx hI
  have hL := hFx.layout
  have hg : 0 < 2 ^ lg := Nat.two_pow_pos lg
  have hg11 : 2 ^ lg ≤ 2048 := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hlg; simpa using this
  have hbw : 0 < c.bw := by rcases hL.bw with h | h <;> omega_using [h]
  simp only [wrs0] at hFx hI
  generalize hBd : Fb s₀ c = B at hFx hI ⊢
  generalize hDd : Dp s₀ = D at hFx hI hD ⊢
  generalize hNd : N s₀ = n at hFx hI ⊢
  have hivl : (iv0 c s₀).length = 4 * c.bw := by simp [iv0, bytesAt]
  generalize hsd : Mn.step = st at hFx hI hstw hstle hcompW hFb hpre hpost hD ⊢
  have hst := hFx.step
  have hN := hFx.nFit
  have hDf := hFx.dataFit
  generalize hxs : xs0 Mn s₀ = xs at hI ⊢
  generalize hivd : iv0 c s₀ = iv at hI hivl ⊢
  -- The groups and the blocks left.
  let g := 2 ^ lg
  let q := n / g
  let r := n - g * q
  have hq : g * q ≤ n := Nat.mul_div_le _ _
  have hnr : n = g * q + r := by omega_using [hq]
  have hwq' : Mw.step * q = st * (g * q) := by rw [hstw, Nat.mul_assoc, Nat.mul_left_comm]
  have hwq : Mw.step * q + st * r = st * n := by rw [hwq', ← Nat.mul_add, ← hnr]
  have hWdat : dataRegion D st n ∈ wrs c B D n st := List.mem_cons_self
  have coreScr : Region.Sub (coreRegion c B) (scrRegion c B) := VG.Offset.sub_base _ (by
    have h1 := total_ge hL; simp only [coreSlot] at h1 ⊢; omega)
  have chnScr : Region.Sub (chnRegion c B) (scrRegion c B) := VG.Offset.sub_base _ (by
    have h1 := total_ge hL; have h2 := bw_le hL; simp only [Core.chnSlot, coreSlot] at h1 ⊢; omega)
  -- The groups.
  have hFw : Fixed c s₂ B D q Mw.step (4 * c.bw * 2 ^ lg) (wrs c B D n st) n (2 ^ lg) :=
    ⟨hFx.scr, dataW_mono hFx.dataW (by omega_using [hwq]), by omega_using [hDf, hwq],
      hFx.dataScr.sub_left (Region.sub_prefix (by omega_using [hwq])), hN, Nat.mul_div_le _ _, hg11,
      ⟨by rw [hstw]; exact Nat.mul_pos hg hst.1, by rw [hstw]; exact hstle⟩,
      ⟨Nat.mul_pos (by omega_using [hbw]) hg, Nat.mul_le_mul_left _ hG⟩,
      ⟨_, hWdat, Region.sub_prefix (by omega_using [hwq])⟩, hFx.scrIn, hL⟩
  generalize hxw : chunksAt Mw.step s₂.mem D q = xw
  have hIw : Inv cs s₂ B D q Mw.step (wrs c B D n st) n (2 ^ lg) k (group st (2 ^ lg) F) iv xw 0 s₂ := by
    refine ⟨hI.b, hI.keep, hI.rd, hI.wr, ?_, ?_, hI.ready, ?_, ?_, Frame.refl _ _⟩
    · rw [hI.dp, Nat.mul_zero, Nat.mul_zero]
    · rw [hI.np, Nat.mul_zero, Nat.mul_zero]
    · simp only [hxw, List.take_zero, run, List.nil_append, List.drop_zero]
    · rw [hI.chn]; rfl
  have hxwl : xw.length = q := by rw [← hxw, chunksAt_length]
  have hBal : B.toNat % 4 = 0 := by have := hFx.scr.al; omega
  have hww : WordOk c w Mw B D Mw.step := ⟨hpreWA, hpostWA, hBal, fun hw =>
    ⟨(hD hw).1, by rw [hstw, Nat.mul_mod, (hD hw).2, Nat.mul_zero, Nat.zero_mod]⟩⟩
  refine WP.seq (WP.mono (loopWide_wp cs (by omega_using [hlg]) hFw hww rfl rfl hB hpreW hpostW hcompW hxwl hIw)
    fun s₃ h₃ => ?_)
  -- The blocks left.
  let D' := D + BitVec.ofNat 64 (Mw.step * q)
  have hD'fit : D'.toNat + st * r ≤ 2 ^ 64 := by
    show (D + BitVec.ofNat 64 (Mw.step * q)).toNat + st * r ≤ 2 ^ 64
    have := D.isLt
    rw [VG.Offset.toNat_add_ofNat]; omega_using [hDf, hwq, this]
  have hsubN : Region.Sub (dataRegion D' st r) (dataRegion D st n) := VG.Offset.sub_base _ (by omega_using [hwq])
  have hFn : Fixed c s₃ B D' r st (4 * c.bw) (wrs c B D n st) r 1 :=
    ⟨hFx.scr.congr h₃.wr, by rw [h₃.wr]; exact dataW_shift hFx.dataW (by omega_using [hwq]), hD'fit,
      hFx.dataScr.sub_left hsubN, by omega_using [hN], by omega_using [], by decide, hst, hFx.buf,
      ⟨_, hWdat, hsubN⟩, hFx.scrIn, hL⟩
  generalize hxn : chunksAt st s₃.mem D' r = xn
  have hIn : Inv cs s₃ B D' r st (wrs c B D n st) r 1 k F (run (group st (2 ^ lg) F) iv xw).2 xn 0 s₃ := by
    refine ⟨h₃.b, fun _ _ _ _ => rfl, rfl, rfl, ?_, ?_, h₃.ready, ?_, ?_, Frame.refl _ _⟩
    · rw [h₃.dp, Nat.mul_zero, BitVec.add_zero]
    · rw [h₃.np, Nat.mul_zero, Nat.sub_zero]
    · simp only [hxn, List.take_zero, run, List.nil_append, List.drop_zero]
    · rw [h₃.chn, List.take_of_length_le (by omega_using [hxwl])]; rfl
  have hxnl : xn.length = r := by rw [← hxn, chunksAt_length]
  have hwn : WordOk c w Mn B D' st := ⟨hpreA, hpostA, hBal, fun hw =>
    ⟨al4 (hD hw).1 (by rw [hstw, Nat.mul_assoc, Nat.mul_mod, Nat.mul_mod st, (hD hw).2]; simp),
      (hD hw).2⟩⟩
  refine WP.mono (loop_wp cs hFn hwn hsd hpre hpost hcomp hxnl hIn) fun s₄ h₄ => ?_
  have d₃ := h₃.done hxwl
  have d₄ := h₄.done hxnl
  -- How the data split.
  have hdis₃ : ∀ R ∈ big c B D q Mw.step, Region.Disjoint (dataRegion D' st r) R := by
    intro R hR
    simp only [big, List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl
    · exact (hFx.dataScr.sub_left hsubN).sub_right coreScr
    · exact (hFx.dataScr.sub_left hsubN).sub_right chnScr
    · exact (VG.Offset.disjoint_base _ (Nat.le_refl _) (by omega_using [hDf, hwq]))
  have hdis₄ : ∀ R ∈ big c B D' r st, Region.Disjoint (dataRegion D st (g * q)) R := by
    intro R hR
    simp only [big, List.mem_cons, List.not_mem_nil, or_false] at hR
    have hpre' : Region.Sub (dataRegion D st (g * q)) (dataRegion D st n) := Region.sub_prefix (by omega_using [hwq, hwq'])
    rcases hR with rfl | rfl | rfl
    · exact (hFx.dataScr.sub_left hpre').sub_right coreScr
    · exact (hFx.dataScr.sub_left hpre').sub_right chnScr
    · show Region.Disjoint ⟨D, st * (g * q)⟩ ⟨D + BitVec.ofNat 64 (Mw.step * q), st * r⟩
      rw [hwq']
      exact VG.Offset.base_disjoint _ (Nat.le_refl _) (by omega_using [hDf, hwq, hwq'])
  have hsplit : ∀ m : Mem, chunksAt st m D n = chunksAt st m D (g * q) ++ chunksAt st m D' r := fun m => by
    show _ = _ ++ chunksAt st m (D + BitVec.ofNat 64 (Mw.step * q)) r
    rw [hnr, chunksAt_add, hwq']
  have hgroup : ∀ m : Mem, chunksAt st m D (g * q) = (chunksAt Mw.step m D q).flatMap (split st g) := fun m => by
    rw [chunksAt_group, hstw]
  have hlen : ∀ x ∈ xw, x.length = g * st := fun x hx => by
    rw [← hxw] at hx
    simp only [chunksAt, List.mem_map, List.mem_range] at hx
    obtain ⟨_, _, rfl⟩ := hx
    simp only [bytesAt, List.length_map, List.length_range, hstw]; rfl
  obtain ⟨rg1, rg2⟩ := run_group_blocks hFb iv xw hivl hlen
  -- The inputs: the groups' blocks, then the blocks left.
  have hxs' : xs = xw.flatMap (split st g) ++ xn := by
    have e := hI.data
    simp only [List.take_zero, run, List.nil_append, List.drop_zero] at e
    rw [← e, hsplit, hgroup, hxw, ← hxn,
      chunksAt_frame h₃.frame hdis₃ (by omega_using [hD'fit])]
  have hrun := run_append F iv (xw.flatMap (split st g)) xn
  rw [← rg2] at hrun
  refine ⟨d₄.b, fun r' hr h3 h2 => by rw [d₄.keep r' hr h3 h2, d₃.keep r' hr h3 h2], by rw [d₄.rd, d₃.rd],
    by rw [d₄.wr, d₃.wr], ?_, ?_, ?_⟩
  · rw [hxs', hrun, hsplit, d₄.data, chunksAt_frame d₄.frame hdis₄ (by omega_using [hDf, hwq, hwq']), hgroup,
      d₃.data, rg1]
  · rw [hxs', hrun, d₄.chn]
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
    (hloops : LoopsOk cs Mn F s₀ k (Core.aligned Mn.step fun w => .seq (c.loopWide w Mw lg) (c.steps w Mn)))
    (hk : cs.KeyArgs s₀ (wrs0 c Mn s₀) k) :
    WP isa (c.seq2 Mw Mn lg) s₀ fun s' => abiPreserved s₀ s' ∧
      chunksAt Mn.step s'.mem (Dp s₀) (N s₀) = (run F (iv0 c s₀) (xs0 Mn s₀)).1 ∧
      (Mn.ivOut = true → bytesAt s'.mem (P s₀) (4 * c.bw) = (run F (iv0 c s₀) (xs0 Mn s₀)).2) ∧
      Changes c Mn s₀ s' :=
  seqWith_changes_wp cs hp hloops hk

theorem lens_wide (G : Nat) (l : Loc) (hl : l ≠ .chn) :
    4 * c.bw * G ≤ lens c (G * (4 * c.bw)) (4 * c.bw * G) l := by
  cases l <;> simp [lens, Nat.mul_comm] at hl ⊢

theorem cbcDecWide_loops (hlg : lg ≤ 11) (hG : 2 ^ lg ≤ c.G) (hstle : 2 ^ lg * (4 * c.bw) ≤ 2032) :
    LoopsOk cs (Mode.cbcDecChained c.bw) (cbcDecF (cs.cipher k)) s₀ k
      (Core.aligned (Mode.cbcDecChained c.bw).step fun w =>
        .seq (c.loopWide w (Mode.cbcDecWide c.bw (2 ^ lg)) lg) (c.steps w (Mode.cbcDecChained c.bw))) := by
  have b := blk_bounds (c := c) (st := (Mode.cbcDecChained c.bw).step) rfl
  obtain ⟨hw1, hw2⟩ := cbcDecWide_inBounds (bw := c.bw) (len := lens c (2 ^ lg * (4 * c.bw)) (4 * c.bw * 2 ^ lg))
    (2 ^ lg) (lens_wide _ _ (by decide)) (lens_wide _ _ (by decide)) (by simp [lens])
  have hpA : ∀ o ∈ (Mode.cbcDecChained c.bw).pre, WordAl o := copyBlk_wordAl _ _ _
  have hqA : ∀ o ∈ (Mode.cbcDecChained c.bw).post, WordAl o :=
    append_ok (append_ok (xorBlk_wordAl _ _ _ _) (copyBlk_wordAl _ _ _)) (copyBlk_wordAl _ _ _)
  have h4 : (4 * c.bw) % 4 = 0 := Nat.mul_mod_right 4 _
  exact aligned_ok cs fun w hD => wideSteps_ok cs hlg hG rfl hstle hw1 hw2 (cbcDecWide_computes (cs.cipher_len k) _)
    (bufCipher_blocks hG) (cbcDecF_blockwise (cs.cipher_len k)) (copyBlk_inBounds (b _) (b _))
    (append_ok (append_ok (xorBlk_inBounds (b _) (b _) (b _)) (copyBlk_inBounds (b _) (b _)))
      (copyBlk_inBounds (b _) (b _)))
    (cbcDecChained_computes (cs.cipher_len k)) (widen_wordAl hpA h4 h4) (widen_wordAl hqA h4 h4) hpA hqA hD

theorem cfbDecWide_loops (hlg : lg ≤ 11) (hG : 2 ^ lg ≤ c.G) (hstle : 2 ^ lg * (4 * c.bw) ≤ 2032) :
    LoopsOk cs (Mode.cfbDecEarly c.bw) (cfbDecF (cs.cipher k)) s₀ k
      (Core.aligned (Mode.cfbDecEarly c.bw).step fun w =>
        .seq (c.loopWide w (Mode.cfbDecWide c.bw (2 ^ lg)) lg) (c.steps w (Mode.cfbDecEarly c.bw))) := by
  have b := blk_bounds (c := c) (st := (Mode.cfbDecEarly c.bw).step) rfl
  obtain ⟨hw1, hw2⟩ := cfbDecWide_inBounds (bw := c.bw) (len := lens c (2 ^ lg * (4 * c.bw)) (4 * c.bw * 2 ^ lg))
    (2 ^ lg) (lens_wide _ _ (by decide)) (lens_wide _ _ (by decide)) (by simp [lens])
  have hpA : ∀ o ∈ (Mode.cfbDecEarly c.bw).pre, WordAl o := append_ok (copyBlk_wordAl _ _ _) (copyBlk_wordAl _ _ _)
  have hqA : ∀ o ∈ (Mode.cfbDecEarly c.bw).post, WordAl o := xorBlk_wordAl _ _ _ _
  have h4 : (4 * c.bw) % 4 = 0 := Nat.mul_mod_right 4 _
  exact aligned_ok cs fun w hD => wideSteps_ok cs hlg hG rfl hstle hw1 hw2 (cfbDecWide_computes (cs.cipher_len k) _)
    (bufCipher_blocks hG) (cfbDecF_blockwise (cs.cipher_len k))
    (append_ok (copyBlk_inBounds (b _) (b _)) (copyBlk_inBounds (b _) (b _))) (xorBlk_inBounds (b _) (b _) (b _))
    (cfbDecEarly_computes (cs.cipher_len k)) (widen_wordAl hpA h4 h4) (widen_wordAl hqA h4 h4) hpA hqA hD

/-- CBC decryption, `2 ^ lg` blocks at a time. -/
theorem cbcDecWide_wp (hlg : lg ≤ 11) (hG : 2 ^ lg ≤ c.G) (hstle : 2 ^ lg * (4 * c.bw) ≤ 2032)
    (hp : SeqPre c (Mode.cbcDecChained c.bw) s₀) (hk : cs.KeyArgs s₀ (wrs0 c (Mode.cbcDecChained c.bw) s₀) k) :
    WP isa (c.seq2 (Mode.cbcDecWide c.bw (2 ^ lg)) (Mode.cbcDecChained c.bw) lg) s₀ fun s' => abiPreserved s₀ s' ∧
      chunksAt (4 * c.bw) s'.mem (Dp s₀) (N s₀) = Spec.Cbc.decrypt (cs.cipher k) (iv0 c s₀) (blocks0 (c := c) s₀) ∧
      bytesAt s'.mem (P s₀) (4 * c.bw) = Spec.Cbc.next (iv0 c s₀) (blocks0 (c := c) s₀) ∧
      Changes c (Mode.cbcDecChained c.bw) s₀ s' :=
  WP.mono (seq2_changes_wp cs hp
    (cbcDecWide_loops cs hlg hG hstle) hk) fun s' ⟨h1, h2, h3, h4⟩ =>
    ⟨h1, h2.trans (by rw [decrypt_run]; rfl), by rw [h3 rfl, decrypt_run_next]; rfl, h4⟩

/-- CFB decryption, `2 ^ lg` blocks at a time. -/
theorem cfbDecWide_wp (hlg : lg ≤ 11) (hG : 2 ^ lg ≤ c.G) (hstle : 2 ^ lg * (4 * c.bw) ≤ 2032)
    (hp : SeqPre c (Mode.cfbDecEarly c.bw) s₀) (hk : cs.KeyArgs s₀ (wrs0 c (Mode.cfbDecEarly c.bw) s₀) k) :
    WP isa (c.seq2 (Mode.cfbDecWide c.bw (2 ^ lg)) (Mode.cfbDecEarly c.bw) lg) s₀ fun s' => abiPreserved s₀ s' ∧
      chunksAt (4 * c.bw) s'.mem (Dp s₀) (N s₀) = Spec.Cfb.decrypt (cs.cipher k) (iv0 c s₀) (blocks0 (c := c) s₀) ∧
      bytesAt s'.mem (P s₀) (4 * c.bw) = Spec.Cbc.next (iv0 c s₀) (blocks0 (c := c) s₀) ∧
      Changes c (Mode.cfbDecEarly c.bw) s₀ s' :=
  WP.mono (seq2_changes_wp cs hp
    (cfbDecWide_loops cs hlg hG hstle) hk) fun s' ⟨h1, h2, h3, h4⟩ =>
    ⟨h1, h2.trans (by rw [(cfbDec_run _ _ _).1]; rfl), by rw [h3 rfl, (cfbDec_run _ _ _).2]; rfl, h4⟩

end

end VG.Proof.Modes.RISCV64
