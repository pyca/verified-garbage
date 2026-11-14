module

public import VerifiedGarbage.Proof.Blowfish.X86_64.Reduce
public import VerifiedGarbage.Proof.Blowfish.X86_64.Row
import VerifiedGarbage.Proof.Framework.X86_64.Words
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Blowfish.Schedule
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Impl.Rc2.X86_64.Sse2Lookup
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
public import VerifiedGarbage.Proof.Blowfish.F
import VerifiedGarbage.Proof.Framework.Mem

/-! ### `Blowfish.X86_64.Lookup`, which only this module used -/

section

/-! ### `Blowfish.X86_64.Combine`, which only this module used -/

section

/-! # An S-box entry from its byte planes; the index in every lane -/

@[expose] public section

namespace VG.Proof.Blowfish.X86_64

open VG VG.X86_64 VG.Impl.Blowfish.X86_64 VG.Spec.Blowfish

/-- The entry's bytes, shifted into place and ORed. -/
theorem combine_entry (m : Mem) (S : Addr) {j : Nat} (hj : j < 4) (x : Byte) :
    (pl S j 0 m x.toNat).setWidth 32 ||| (pl S j 1 m x.toNat).setWidth 32 <<< 8 |||
        (pl S j 2 m x.toNat).setWidth 32 <<< 16 ||| (pl S j 3 m x.toNat).setWidth 32 <<< 24 =
      sEntry (scheduleAt m S) j x := by
  refine word_ext fun b hb => ?_
  rw [byte_of_le4 _ _ _ _ hb, sEntry_byte _ _ hj hb]
  rcases (by omega_using [hb] : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;> rfl

/-- `punpcklwd` of a value with itself, then `pshufd 0`: its low word in every word. -/
theorem bcast_low (v : BitVec 128) (b : Byte) (h : dword v 0 = b.setWidth 32) :
    shufDwords (XBinOp.eval .punpcklwd v v) 0 = bcast b := by
  refine ext_word fun i hi => ?_
  rw [word_eq_dword _ hi, show shufDwords (XBinOp.eval .punpcklwd v v) 0 =
      ofDwords (dword (XBinOp.eval .punpcklwd v v) 0) (dword (XBinOp.eval .punpcklwd v v) 0)
        (dword (XBinOp.eval .punpcklwd v v) 0) (dword (XBinOp.eval .punpcklwd v v) 0) from rfl]
  have d0 : dword (XBinOp.eval .punpcklwd v v) 0 = word v 0 ++ word v 0 := by
    rw [dword_words]
    simp only [XBinOp.eval, word_ofWords _ (show 2 * 0 + 1 < 8 by decide), word_ofWords _ (show 2 * 0 < 8 by decide)]
    rfl
  have w0 : word v 0 = b.setWidth 16 := by
    rw [word_eq_dword _ (by decide), show 0 / 2 = 0 from rfl, h]
    apply BitVec.eq_of_getLsbD_eq; intro j hj; simp [hj]; omega_using [hj]
  have hd : ∀ k < 4, dword (ofDwords (word v 0 ++ word v 0) (word v 0 ++ word v 0) (word v 0 ++ word v 0)
      (word v 0 ++ word v 0)) k = word v 0 ++ word v 0 := by
    intro k hk
    rcases (by omega_using [hk] : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> simp
  rw [d0, hd _ (by omega_using [hi]), bcast, word_ofWords _ hi, w0]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hj, decide_true, Bool.true_and]
  split <;> rename_i h <;> rcases (by omega_using [] : i % 2 = 0 ∨ i % 2 = 1) with e | e <;> simp [e] at h ⊢ <;>
    omega

end VG.Proof.Blowfish.X86_64

end

end


/-!
# An S-box lookup

`lookup_run`: `lookup sch j` leaves S-box `j` at byte `3 - j` of xL (S₁ at
its most significant byte) in the low doubleword of `accReg 0`, writing only
`r8`, `r9`, `r11`, the flags and the scan's vector registers.
-/

@[expose] public section

namespace VG.Proof.Blowfish.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Blowfish.X86_64 VG.Spec.Blowfish

theorem exec_movImm64 (s : State) (d : Reg) (v : BitVec 64) : exec (.movImm64 d v) s = some (s.setReg d v) := rfl

theorem loadConst_run (t : State) {dst : XReg} (hd : dst ≠ tmp) (v : BitVec 128) :
    ∃ t', runBlock isa (loadConst dst v) t = some t' ∧ t'.xmm dst = v ∧
      (∀ d, d ≠ dst → d ≠ tmp → t'.xmm d = t.xmm d) ∧ (∀ g, g ≠ .r11 → t'.gpr g = t.gpr g) ∧
      t' = { t with gpr := t'.gpr, xmm := t'.xmm } := by
  let t₁ := t.setReg .r11 (v.extractLsb' 0 64)
  let t₂ := (XOp.movq dst .r11).exec t₁
  let t₃ := t₂.setReg .r11 (v.extractLsb' 64 64)
  let t₄ := (XOp.movq tmp .r11).exec t₃
  let t₅ := (XOp.bin .punpcklqdq dst tmp).exec t₄
  refine ⟨t₅, ?_, ?_, fun d h1 h2 => ?_, fun g hg => ?_, ?_⟩
  · simp only [loadConst, bin, runBlock_cons, exec_movImm64, exec_xop, runStep_some, runBlock_nil]
    rfl
  · simp (disch := decide) only [t₅, t₄, t₃, t₂, t₁, XOp.exec, xmm_setXmm_self, xmm_setXmm_of_ne _ _ hd,
      xmm_setReg, gpr_setReg_self]
    exact movq_const v
  · simp only [t₅, t₄, t₃, t₂, t₁, XOp.exec, xmm_setXmm_of_ne _ _ h1, xmm_setXmm_of_ne _ _ h2, xmm_setReg]
  · simp only [t₅, t₄, t₃, t₂, t₁, XOp.exec, gpr_setXmm, gpr_setReg_of_ne _ _ hg]
  · simp only [t₅, t₄, t₃, t₂, t₁, XOp.exec, State.setXmm, State.setReg]

/-- Byte `k` of a word, by shifts. -/
theorem shifts_byte (L : BitVec 32) {k : Nat} (hk : k < 4) :
    (L <<< (24 - 8 * k)) >>> 24 = (L.extractLsb' (8 * k) 8).setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_extractLsb']
  by_cases h : i < 8
  · simp [h, show 24 + i < 32 by omega_using [h], show ¬ 24 + i < 24 - 8 * k by omega_using []]
    rw [decide_eq_true hi, Bool.true_and]
    exact congrArg _ (by omega_using [hk])
  · simp [h, show ¬ 24 + i < 32 by omega_using [h]]

theorem exec_mov32_imm (s : State) (d : Reg) (v : BitVec 32) :
    exec (.mov32 d (.imm v)) s = some (s.setReg32 d v) := rfl

theorem pslld_dword0 (v : BitVec 128) (c : BitVec 8) (hc : c.toNat < 32) :
    dword (XShiftOp.eval .pslld v c) 0 = dword v 0 <<< c.toNat := by
  rw [pslld_dwords _ _ hc, dword_ofDwords_0]

theorem psrld_dword0 (v : BitVec 128) (c : BitVec 8) (hc : c.toNat < 32) :
    dword (XShiftOp.eval .psrld v c) 0 = dword v 0 >>> c.toNat := by
  rw [psrld_dwords _ _ hc, dword_ofDwords_0]

theorem state_eta (t : State) :
    t = { t with gpr := t.gpr, xmm := t.xmm, cf := t.cf, zf := t.zf, sf := t.sf, of := t.of } := rfl

theorem reduce_run (t : State) {b : Nat} (hb : b < 4) :
    ∃ t', runBlock isa (reduce b) t = some t' ∧ t'.xmm (accReg b) = reduceV (t.xmm (accReg b)) ∧
      (∀ d, d ≠ tmp → d ≠ accReg b → t'.xmm d = t.xmm d) ∧ t' = { t with xmm := t'.xmm } := by
  have ne := (accReg_ne b hb).1
  let ops : List XOp := [.pshufd tmp (accReg b) 0x4E, .bin .por (accReg b) tmp, .pshufd tmp (accReg b) 0xB1,
    .bin .por (accReg b) tmp, .bin .movdqa tmp (accReg b), .shift .psrld tmp (BitVec.ofNat 8 16),
    .bin .por (accReg b) tmp, .bin .movdqa tmp (accReg b), .shift .psrld tmp (BitVec.ofNat 8 8),
    .bin .por (accReg b) tmp, .shift .pslld (accReg b) (BitVec.ofNat 8 24), .shift .psrld (accReg b) (BitVec.ofNat 8 24)]
  refine ⟨ops.foldl (fun t op => op.exec t) t, by rw [show reduce b = ops.map .xop from rfl]; exact runXops ops t,
    ?_, fun d h1 h2 => ?_, ?_⟩
  · simp only [ops, List.foldl, XOp.exec, xmm_setXmm_self, xmm_setXmm_of_ne _ _ ne, xmm_setXmm_of_ne _ _ ne.symm,
      eval_movdqa]
    rfl
  · simp only [ops, List.foldl, XOp.exec, xmm_setXmm_of_ne _ _ h1, xmm_setXmm_of_ne _ _ h2]
  · simp only [ops, List.foldl, XOp.exec, State.setXmm]

/-- What a lookup needs. -/
structure LookEnv (sch : Reg) (S : Addr) (s : State) : Prop where
  hsch : s.gpr sch = S
  ne8 : sch ≠ Reg.r8
  ne9 : sch ≠ Reg.r9
  ne11 : sch ≠ Reg.r11
  rd : Readable s S
  ones : s.xmm onesReg = wordsOf 1
  sixteen : s.xmm sixteenReg = wordsOf 16
  low : s.xmm lowReg = wordsOf 0xFF

/-- The vector registers a lookup writes. -/
def lookXRegs : List XReg := [idxReg, kReg, tmp, tmp2, mEven, mOdd, .xmm8, .xmm9, .xmm10, .xmm11]

/-- Only the lookup's registers and the flags change. -/
structure LookOnly (s s' : State) : Prop where
  xmm : ∀ d, d ∉ lookXRegs → s'.xmm d = s.xmm d
  gpr : ∀ g, g ≠ .r8 → g ≠ .r9 → g ≠ .r11 → s'.gpr g = s.gpr g
  eq : s' = { s with gpr := s'.gpr, xmm := s'.xmm, cf := s'.cf, zf := s'.zf, sf := s'.sf, of := s'.of }

theorem index_eq (k : Nat) : index k = ([.bin .movdqa idxReg xL, .shift .pslld idxReg (BitVec.ofNat 8 (24 - 8 * k)),
    .shift .psrld idxReg (BitVec.ofNat 8 24), .bin .punpcklwd idxReg idxReg, .pshufd idxReg idxReg 0] : List XOp).map .xop := rfl

theorem lookup_run {sch : Reg} {S : Addr} {s : State} (E : LookEnv sch S s) {j : Nat} (hj : j < 4) :
    WP isa (lookup sch j) s (fun s' => dword (s'.xmm (accReg 0)) 0 =
      sEntry (scheduleAt s.mem S) j ((dword (s.xmm xL) 0).extractLsb' (8 * (3 - j)) 8) ∧ LookOnly s s') := by
  let x : Byte := (dword (s.xmm xL) 0).extractLsb' (8 * (3 - j)) 8
  rw [lookup]
  apply WP.seq
  -- the index, the row's numbers, the accumulators and the counters
  let iops : List XOp := [.bin .movdqa idxReg xL, .shift .pslld idxReg (BitVec.ofNat 8 (24 - 8 * (3 - j))),
    .shift .psrld idxReg (BitVec.ofNat 8 24), .bin .punpcklwd idxReg idxReg, .pshufd idxReg idxReg 0]
  let t₁ := iops.foldl (fun t op => op.exec t) s
  have hidx : t₁.xmm idxReg = bcast x := by
    simp (disch := decide) only [t₁, iops, List.foldl, XOp.exec, xmm_setXmm_self, eval_movdqa]
    refine bcast_low _ _ ?_
    rw [psrld_dword0 _ _ (by decide), pslld_dword0 _ _ (by simp; omega_using [])]
    simp only [BitVec.toNat_ofNat, show (24 - 8 * (3 - j)) % 2 ^ 8 = 24 - 8 * (3 - j) by omega_using [],
      show 24 % 2 ^ 8 = 24 from rfl]
    exact shifts_byte _ (by omega_using [])
  obtain ⟨t₂, r₂, k₂, x₂, g₂, e₂⟩ := loadConst_run t₁ (dst := kReg) (by decide) evenStart
  let pops : List XOp := (List.range 4).map fun b => .bin .pxor (accReg b) (accReg b)
  let t₃ := pops.foldl (fun t op => op.exec t) t₂
  let t₄ := (t₃.setReg32 .r8 0).setReg32 .r9 16
  have run₄ : runBlock isa (index (3 - j) ++ loadConst kReg evenStart ++
      (List.range 4).map (fun b => bin .pxor (accReg b) (accReg b)) ++
      [.mov32 .r8 (.imm 0), .mov32 .r9 (.imm 16)]) s = some t₄ := by
    refine cat_run (cat_run (cat_run (by rw [index_eq]; exact runXops iops s) r₂) (runXops pops t₂)) ?_
    rw [runBlock_cons, exec_mov32_imm, runStep_some, runBlock_cons, exec_mov32_imm, runStep_some, runBlock_nil]
  -- what the init leaves
  have g₁ : t₁.gpr = s.gpr := by simp only [t₁, iops, List.foldl, XOp.exec, gpr_setXmm]
  have x₁ : ∀ d, d ≠ idxReg → t₁.xmm d = s.xmm d := fun d h => by
    simp only [t₁, iops, List.foldl, XOp.exec, xmm_setXmm_of_ne _ _ h]
  have pops_eq : pops = [.bin .pxor .xmm8 .xmm8, .bin .pxor .xmm9 .xmm9, .bin .pxor .xmm10 .xmm10,
      .bin .pxor .xmm11 .xmm11] := rfl
  have x₄ : ∀ d, d ∉ lookXRegs → t₄.xmm d = s.xmm d := fun d hd => by
    have h1 : d ≠ idxReg := fun e => hd (by rw [e]; decide)
    have h2 : d ≠ kReg := fun e => hd (by rw [e]; decide)
    have h3 : d ≠ tmp := fun e => hd (by rw [e]; decide)
    have h8 : d ≠ .xmm8 := fun e => hd (by rw [e]; decide)
    have h9 : d ≠ .xmm9 := fun e => hd (by rw [e]; decide)
    have h10 : d ≠ .xmm10 := fun e => hd (by rw [e]; decide)
    have h11 : d ≠ .xmm11 := fun e => hd (by rw [e]; decide)
    simp only [t₄, t₃, pops_eq, List.foldl, XOp.exec, State.setReg32, xmm_setReg, xmm_setXmm_of_ne _ _ h8,
      xmm_setXmm_of_ne _ _ h9, xmm_setXmm_of_ne _ _ h10, xmm_setXmm_of_ne _ _ h11]
    rw [x₂ _ h2 h3, x₁ _ h1]
  have a₄ : ∀ b < 4, t₄.xmm (accReg b) = 0 := fun b hb => by
    rcases (by omega_using [hb] : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;>
      simp (disch := decide) only [t₄, t₃, pops_eq, List.foldl, XOp.exec, State.setReg32, xmm_setReg,
        xmm_setXmm_of_ne, xmm_setXmm_self, accReg, List.getD_cons_zero, List.getD_cons_succ, reduceXBinOpEval,
        BitVec.xor_self] <;> rfl
  have xs₄ : ∀ d, d ≠ .xmm8 → d ≠ .xmm9 → d ≠ .xmm10 → d ≠ .xmm11 → t₄.xmm d = t₂.xmm d :=
    fun d h8 h9 h10 h11 => by
      simp only [t₄, t₃, pops_eq, List.foldl, XOp.exec, State.setReg32, xmm_setReg, xmm_setXmm_of_ne _ _ h8,
        xmm_setXmm_of_ne _ _ h9, xmm_setXmm_of_ne _ _ h10, xmm_setXmm_of_ne _ _ h11]
  have i₄ : t₄.xmm idxReg = bcast x := by
    rw [xs₄ _ (by decide) (by decide) (by decide) (by decide), x₂ _ (by decide) (by decide), hidx]
  have k₄ : t₄.xmm kReg = rowK 0 := by
    rw [xs₄ _ (by decide) (by decide) (by decide) (by decide), k₂]
    refine ext_word fun w hw => ?_
    rw [evenStart, rowK, word_ofWords _ hw, word_ofWords _ hw, Nat.mul_zero, Nat.zero_add]
  have g₄ : ∀ g, g ≠ .r8 → g ≠ .r9 → g ≠ .r11 → t₄.gpr g = s.gpr g := fun g h8 h9 h11 => by
    simp only [t₄, State.setReg32, gpr_setReg_of_ne _ _ h9, gpr_setReg_of_ne _ _ h8, t₃, pops_eq, List.foldl,
      XOp.exec, gpr_setXmm]
    rw [g₂ _ h11, g₁]
  have r8₄ : t₄.gpr .r8 = BitVec.ofNat 64 (16 * 0) := by
    simp only [t₄, State.setReg32, gpr_setReg_of_ne _ _ (show Reg.r8 ≠ Reg.r9 by decide), gpr_setReg_self]; rfl
  have r9₄ : t₄.gpr .r9 = BitVec.ofNat 64 (16 - 0) := by
    simp only [t₄, State.setReg32, gpr_setReg_self]; rfl
  have e₄ : t₄ = { s with gpr := t₄.gpr, xmm := t₄.xmm } := by
    simp only [t₄, t₃, pops_eq, List.foldl, XOp.exec, State.setReg32, State.setReg, State.setXmm]
    rw [e₂]; simp only [t₁, iops, List.foldl, XOp.exec, State.setXmm]
  have hrd₄ : t₄.rd = s.rd := by rw [e₄]
  have hwr₄ : t₄.wr = s.wr := by rw [e₄]
  have hm₄ : t₄.mem = s.mem := by rw [e₄]
  refine WP.of_runBlock ⟨t₄, run₄, ?_⟩
  have SE : ScanEnv sch S x j t₄ := by
    refine ⟨hj, by rw [g₄ _ E.ne8 E.ne9 E.ne11, E.hsch], E.ne8, E.ne9, fun off h => ?_, i₄,
      by rw [x₄ _ (by decide), E.ones], by rw [x₄ _ (by decide), E.sixteen], by rw [x₄ _ (by decide), E.low]⟩
    rw [hrd₄, hwr₄]; exact E.rd off h
  have I0 : RowInv sch S x j t₄ 0 t₄ :=
    ⟨by omega_using [], r8₄, r9₄, k₄, fun b hb => by rw [a₄ b hb, scanAcc_zero], fun _ _ => rfl, fun _ _ _ => rfl,
      state_eta t₄⟩
  apply WP.seq
  refine WP.mono (WP.loop (M := isa) (Q := RowInv sch S x j t₄ 16)
    (fun m u => ∃ r, r < 16 ∧ m = 16 - r ∧ RowInv sch S x j t₄ r u) ?_ 16 t₄ ⟨0, by omega_using [], rfl, I0⟩)
    fun v Iv => ?_
  · intro m u ⟨r, hr, hm, I⟩
    obtain ⟨u', ru, I', zu⟩ := row_run SE hr I
    refine WP.of_runBlock ⟨u', ru, ?_⟩
    have ev : isa.eval .ne u' = some (!(BitVec.ofNat 64 (16 - (r + 1)) == 0)) := by
      show u'.zf.map (!·) = _; rw [zu]; rfl
    by_cases h : r + 1 = 16
    · left; exact ⟨by rw [ev, h]; rfl, h ▸ I'⟩
    · right
      have nz : BitVec.ofNat 64 (16 - (r + 1)) ≠ 0 := by
        intro h'; have := congrArg BitVec.toNat h'; simp at this; omega_using [hr, h, this]
      exact ⟨by rw [ev, show (BitVec.ofNat 64 (16 - (r + 1)) == 0) = false from beq_false_of_ne nz]; rfl,
        16 - (r + 1), by omega_using [hr, hm], r + 1,
        by omega_using [hr, h], rfl, I'⟩
  -- the entry from the planes' accumulators
  obtain ⟨w0, rw0, a0, k0, e0⟩ := reduce_run v (b := 0) (by decide)
  obtain ⟨w1, rw1, a1, k1, e1⟩ := reduce_run w0 (b := 1) (by decide)
  obtain ⟨w2, rw2, a2, k2, e2⟩ := reduce_run w1 (b := 2) (by decide)
  obtain ⟨w3, rw3, a3, k3, e3⟩ := reduce_run w2 (b := 3) (by decide)
  let cops : List XOp := [.shift .pslld (accReg 1) (BitVec.ofNat 8 8), .shift .pslld (accReg 2) (BitVec.ofNat 8 16),
    .shift .pslld (accReg 3) (BitVec.ofNat 8 24), .bin .por (accReg 0) (accReg 1), .bin .por (accReg 0) (accReg 2),
    .bin .por (accReg 0) (accReg 3)]
  let w := cops.foldl (fun t op => op.exec t) w3
  have red : ∀ b < 4, dword (reduceV (v.xmm (accReg b))) 0 = (pl S j b t₄.mem x.toNat).setWidth 32 :=
    fun b hb => by rw [Iv.acc b hb]; exact reduce_scan _ x.isLt
  refine WP.of_runBlock ⟨w, ?_, ?_, ?_⟩
  · refine cat_run (a := (List.range 4).flatMap reduce) ?_ (runXops cops w3)
    show runBlock isa (reduce 0 ++ (reduce 1 ++ (reduce 2 ++ (reduce 3 ++ [])))) v = _
    exact cat_run rw0 (cat_run rw1 (cat_run rw2 (cat_run rw3 runBlock_nil)))
  · have r3 : ∀ b < 4, w3.xmm (accReg b) = reduceV (v.xmm (accReg b)) := by
      intro b hb
      rcases (by omega_using [hb] : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl
      · rw [k3 _ (by decide) (by decide), k2 _ (by decide) (by decide), k1 _ (by decide) (by decide), a0]
      · rw [k3 _ (by decide) (by decide), k2 _ (by decide) (by decide), a1, k0 _ (by decide) (by decide)]
      · rw [k3 _ (by decide) (by decide), a2, k1 _ (by decide) (by decide), k0 _ (by decide) (by decide)]
      · rw [a3, k2 _ (by decide) (by decide), k1 _ (by decide) (by decide), k0 _ (by decide) (by decide)]
    simp (disch := decide) only [w, cops, List.foldl, XOp.exec, xmm_setXmm_self, xmm_setXmm_of_ne, reduceXBinOpEval]
    rw [dword_or, dword_or, dword_or, pslld_dword0 _ _ (by decide), pslld_dword0 _ _ (by decide),
      pslld_dword0 _ _ (by decide), r3 0 (by decide), r3 1 (by decide), r3 2 (by decide), r3 3 (by decide),
      red 0 (by decide), red 1 (by decide), red 2 (by decide), red 3 (by decide), hm₄]
    exact combine_entry _ _ hj x
  · have gw : w.gpr = v.gpr := by
      simp only [w, cops, List.foldl, XOp.exec, gpr_setXmm]; rw [e3, e2, e1, e0]
    refine ⟨fun d hd => ?_, fun g h8 h9 h11 => ?_, ?_⟩
    · have n0 : d ≠ accReg 0 := fun e => hd (by rw [e]; decide)
      have n1 : d ≠ accReg 1 := fun e => hd (by rw [e]; decide)
      have n2 : d ≠ accReg 2 := fun e => hd (by rw [e]; decide)
      have n3 : d ≠ accReg 3 := fun e => hd (by rw [e]; decide)
      have nt : d ≠ tmp := fun e => hd (by rw [e]; decide)
      have sub : ∀ e ∈ rowXRegs, e ∈ lookXRegs := by decide
      have hr : d ∉ rowXRegs := fun h => hd (sub d h)
      simp only [w, cops, List.foldl, XOp.exec, xmm_setXmm_of_ne _ _ n0, xmm_setXmm_of_ne _ _ n1,
        xmm_setXmm_of_ne _ _ n2, xmm_setXmm_of_ne _ _ n3]
      rw [k3 _ nt n3, k2 _ nt n2, k1 _ nt n1, k0 _ nt n0, Iv.xmm _ hr, x₄ _ hd]
    · rw [gw, Iv.gpr g h8 h9, g₄ g h8 h9 h11]
    · have : w = { v with xmm := w.xmm } := by
        simp only [w, cops, List.foldl, XOp.exec, State.setXmm]; rw [e3, e2, e1, e0]
      rw [this, Iv.eq, e₄]

end VG.Proof.Blowfish.X86_64

end

end


/-! # F: four lookups, combined in the low doubleword of `fReg` -/

@[expose] public section

namespace VG.Proof.Blowfish.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Blowfish.X86_64 VG.Spec.Blowfish VG.Proof.Blowfish

/-- The vector registers F writes. -/
def fXRegs : List XReg := fReg :: lookXRegs

/-- Only F's registers and the flags change. -/
structure FOnly (s s' : State) : Prop where
  xmm : ∀ d, d ∉ fXRegs → s'.xmm d = s.xmm d
  gpr : ∀ g, g ≠ .r8 → g ≠ .r9 → g ≠ .r11 → s'.gpr g = s.gpr g
  eq : s' = { s with gpr := s'.gpr, xmm := s'.xmm, cf := s'.cf, zf := s'.zf, sf := s'.sf, of := s'.of }

/-- `a` is `c` with other registers and flags. -/
def Upd (c a : State) : Prop :=
  a = { c with gpr := a.gpr, xmm := a.xmm, cf := a.cf, zf := a.zf, sf := a.sf, of := a.of }

theorem Upd.trans {a b c : State} (h1 : Upd b a) (h2 : Upd c b) : Upd c a := by
  unfold Upd at *; rw [h1]; rw [h2]

theorem Upd.setXmm {a c : State} (h : Upd c a) (d : XReg) (v : BitVec 128) : Upd c (a.setXmm d v) := by
  unfold Upd at *; rw [h]; rfl

theorem FOnly.refl (s : State) : FOnly s s := ⟨fun _ _ => rfl, fun _ _ _ _ => rfl, state_eta s⟩

theorem FOnly.env {sch : Reg} {S : Addr} {s t : State} (E : LookEnv sch S s) (h : FOnly s t) : LookEnv sch S t := by
  have hrd : t.rd = s.rd := by rw [h.eq]
  have hwr : t.wr = s.wr := by rw [h.eq]
  refine ⟨by rw [h.gpr _ E.ne8 E.ne9 E.ne11, E.hsch], E.ne8, E.ne9, E.ne11, fun off ho => ?_,
    by rw [h.xmm _ (by decide), E.ones], by rw [h.xmm _ (by decide), E.sixteen], by rw [h.xmm _ (by decide), E.low]⟩
  rw [hrd, hwr]; exact E.rd off ho

theorem combineX_0 : combineX 0 = .bin .movdqa fReg (accReg 0) := rfl
theorem combineX_1 : combineX 1 = .bin .paddd fReg (accReg 0) := rfl
theorem combineX_2 : combineX 2 = .bin .pxor fReg (accReg 0) := rfl
theorem combineX_3 : combineX 3 = .bin .paddd fReg (accReg 0) := rfl

theorem dword_xor (a b : BitVec 128) : dword (a ^^^ b) 0 = dword a 0 ^^^ dword b 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [getLsbD_dword, BitVec.getLsbD_xor, decide_eq_true hi, Bool.true_and]

/-- A lookup, then its combination, from a state that F's registers alone
separate from `s`. -/
theorem fstep {sch : Reg} {S : Addr} {s : State} (E : LookEnv sch S s) {j : Nat} (hj : j < 4) {t : State}
    (O : FOnly s t) (hf : 0 < j → dword (t.xmm fReg) 0 = fAcc (scheduleAt s.mem S) (dword (s.xmm xL) 0) (j - 1)) :
    WP isa (.seq (lookup sch j) (.block [combine j])) t (fun t' =>
      dword (t'.xmm fReg) 0 = fAcc (scheduleAt s.mem S) (dword (s.xmm xL) 0) j ∧ FOnly s t') := by
  have hm : t.mem = s.mem := by rw [O.eq]
  have hx : t.xmm xL = s.xmm xL := O.xmm _ (by decide)
  apply WP.seq
  refine WP.mono (lookup_run (O.env E) hj) fun u ⟨hu, L⟩ => ?_
  rw [hm, hx] at hu
  refine WP.of_runBlock ⟨(combineX j).exec u, runXops [combineX j] u, ?_, ?_⟩
  · have hf' : 0 < j → dword (u.xmm fReg) 0 = fAcc (scheduleAt s.mem S) (dword (s.xmm xL) 0) (j - 1) :=
      fun h => by rw [L.xmm _ (by decide)]; exact hf h
    rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
    · simp only [combineX_0, XOp.exec, xmm_setXmm_self, eval_movdqa]; exact hu
    · simp only [combineX_1, XOp.exec, xmm_setXmm_self, XBinOp.eval, dword_ofDwords_0]
      rw [hf' (by decide), hu]; rfl
    · simp only [combineX_2, XOp.exec, xmm_setXmm_self, XBinOp.eval]
      rw [dword_xor, hf' (by decide), hu]; rfl
    · simp only [combineX_3, XOp.exec, xmm_setXmm_self, XBinOp.eval, dword_ofDwords_0]
      rw [hf' (by decide), hu]; rfl
  · have hx : ((combineX j).exec u) = u.setXmm fReg (((combineX j).exec u).xmm fReg) := by
      rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
        simp only [combineX_0, combineX_1, combineX_2, combineX_3, XOp.exec, xmm_setXmm_self] <;> rfl
    refine ⟨fun d hd => ?_, fun g h8 h9 h11 => ?_, ?_⟩
    · have n : d ≠ fReg := fun e => hd (by rw [e]; decide)
      have hl : d ∉ lookXRegs := fun h => hd (List.mem_cons_of_mem _ h)
      rw [hx, xmm_setXmm_of_ne _ _ n, L.xmm _ hl, O.xmm _ hd]
    · rw [hx, gpr_setXmm, L.gpr _ h8 h9 h11, O.gpr _ h8 h9 h11]
    · rw [hx]; exact Upd.setXmm (Upd.trans L.eq O.eq) _ _

theorem f_run {sch : Reg} {S : Addr} {s : State} (E : LookEnv sch S s) :
    WP isa (f sch) s (fun s' =>
      dword (s'.xmm fReg) 0 = Spec.Blowfish.f (scheduleAt s.mem S) (dword (s.xmm xL) 0) ∧ FOnly s s') := by
  rw [Impl.Blowfish.X86_64.f]
  have st := fun (j : Nat) (hj : j < 4) (t : State) (O : FOnly s t) hf => WP.seq_iff.mp (fstep E hj O hf)
  apply WP.seq
  refine WP.mono (st 0 (by decide) s (FOnly.refl s) (fun h => absurd h (by decide))) fun t0 h0 => ?_
  apply WP.seq
  refine WP.mono h0 fun u0 ⟨v0, O0⟩ => ?_
  apply WP.seq
  refine WP.mono (st 1 (by decide) u0 O0 (fun _ => v0)) fun t1 h1 => ?_
  apply WP.seq
  refine WP.mono h1 fun u1 ⟨v1, O1⟩ => ?_
  apply WP.seq
  refine WP.mono (st 2 (by decide) u1 O1 (fun _ => v1)) fun t2 h2 => ?_
  apply WP.seq
  refine WP.mono h2 fun u2 ⟨v2, O2⟩ => ?_
  apply WP.seq
  refine WP.mono (st 3 (by decide) u2 O2 (fun _ => v2)) fun t3 h3 => ?_
  refine WP.mono h3 fun u3 ⟨v3, O3⟩ => ⟨by rw [v3, fAcc_three], O3⟩

end VG.Proof.Blowfish.X86_64
