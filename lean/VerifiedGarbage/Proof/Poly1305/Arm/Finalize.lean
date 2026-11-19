module

public import VerifiedGarbage.Proof.Poly1305.Contract
import VerifiedGarbage.Proof.Poly1305.Arm.Lit
import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
import VerifiedGarbage.Proof.Poly1305.Stream
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Poly1305.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
meta import VerifiedGarbage.Proof.Poly1305.Stream
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Poly1305.Arm.Umaal
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Proof.Poly1305.Arm.Bytes
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Spec.Poly1305.Contract
meta import VerifiedGarbage.Proof.Poly1305.Contract
public import VerifiedGarbage.Proof.Poly1305.Spec
meta import VerifiedGarbage.Proof.Poly1305.Arm.Bytes
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Spec.Poly1305.Contract
meta import VerifiedGarbage.Proof.Poly1305.Spec
meta import VerifiedGarbage.Proof.Poly1305.Arm.Umaal
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Framework.Range

/-! ### `Poly1305.Arm.Steps`, which this module and modules that import it used -/

section

/-! ### `Poly1305.Arm.Blocks`, which only this module used -/

section

@[expose] public section

section

/-!
# Poly1305 on 32-bit ARM: which parts of the state the code writes

Lists of ranges of the state (`offR`), the frames of writes into them, and
what they leave unchanged: the key, the saved registers, the limbs of `r` and
the stored accumulator.
-/

namespace VG.Proof.Poly1305.Arm

open VG VG.Arm VG.Impl.Poly1305.Arm
open VG.Spec.Poly1305 (P clamp leNum bytesAt)

/-- The ranges `[a, a + len)` of the state at `B`, for `(a, len)` in `l`. -/
def offR (B : Addr) (l : List (Nat × Nat)) : List Region := l.map fun p => ⟨B + BitVec.ofNat 64 p.1, p.2⟩

/-- A range disjoint from each of the ranges `l`. -/
theorem dj_offR (B : Addr) {d n : Nat} {l : List (Nat × Nat)}
    (h : (l.all fun p => d + n ≤ p.1 ∨ p.1 + p.2 ≤ d) = true)
    (hb : d + n < 2 ^ 32) (hl : (l.all fun p => p.1 + p.2 < 2 ^ 32) = true) :
    ∀ r ∈ offR B l, (⟨B + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r := by
  intro r hr
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
  obtain h1 := List.all_eq_true.mp h p hp
  obtain h2 := List.all_eq_true.mp hl p hp
  simp only [decide_eq_true_eq] at h1 h2
  exact disjoint_sub B h1 hb h2

/-- Each of the ranges `l` is inside one of the ranges `l'`. -/
theorem sub_offR (B : Addr) {l l' : List (Nat × Nat)}
    (h : (l.all fun p => l'.any fun q => q.1 ≤ p.1 ∧ p.1 + p.2 ≤ q.1 + q.2) = true)
    (hl : (l'.all fun q => q.1 + q.2 < 2 ^ 32) = true) :
    ∀ r ∈ offR B l, ∃ r' ∈ offR B l', Region.Sub r r' := by
  intro r hr
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
  obtain ⟨q, hq, h1⟩ := List.any_eq_true.mp (List.all_eq_true.mp h p hp)
  obtain h2 := List.all_eq_true.mp hl q hq
  simp only [decide_eq_true_eq] at h1 h2
  exact ⟨_, List.mem_map.mpr ⟨q, hq, rfl⟩, sub_sub B h1.1 h1.2 h2⟩

theorem _root_.VG.Frame.offR_sub {B : Addr} {l l' : List (Nat × Nat)} {m m' : Mem} (hf : Frame (offR B l) m m')
    (h : (l.all fun p => l'.any fun q => q.1 ≤ p.1 ∧ p.1 + p.2 ≤ q.1 + q.2) = true)
    (hl : (l'.all fun q => q.1 + q.2 < 2 ^ 32) = true) : Frame (offR B l') m m' :=
  hf.sub (sub_offR B h hl)

/-- A write inside one of the ranges. -/
theorem _root_.VG.Frame.writeOff {B : Addr} {l : List (Nat × Nat)} {m m' : Mem} (hf : Frame (offR B l) m m')
    {a len d n : Nat} (hm : (a, len) ∈ l) (h1 : a ≤ d) (h2 : d + n ≤ a + len) (h3 : a + len < 2 ^ 32)
    {w : Nat} (v : BitVec w) (hw : w / 8 = n) :
    Frame (offR B l) m (m'.writeW (B + BitVec.ofNat 64 d) v) :=
  hf.writeW (List.mem_map.mpr ⟨_, hm, rfl⟩) v (hw ▸ contains_sub B h1 h2 h3)

theorem accR_offR (B : Addr) : [accR B] = offR B [(0, 20)] := by simp [offR]

theorem _root_.VG.Frame.word {B : Addr} {l : List (Nat × Nat)} {m m' : Mem} (hf : Frame (offR B l) m m') {d : Nat}
    (h : (l.all fun p => d + 4 ≤ p.1 ∨ p.1 + p.2 ≤ d) = true) (hb : d + 4 < 2 ^ 32)
    (hl : (l.all fun p => p.1 + p.2 < 2 ^ 32) = true) :
    m'.readW (B + BitVec.ofNat 64 d) 32 = m.readW (B + BitVec.ofNat 64 d) 32 :=
  hf.readW (Region.contains_self _ _) (dj_offR B h hb hl) (by decide)

/-! ## What the writes leave -/

theorem Saved.frame {B : Addr} {g : Reg → BitVec 32} {m m' : Mem} (hs : Saved B g m) {l : List (Nat × Nat)}
    (hf : Frame (offR B l) m m') (h : (l.all fun p => 88 ≤ p.1 ∨ p.1 + p.2 ≤ 56) = true)
    (hl : (l.all fun p => p.1 + p.2 < 2 ^ 32) = true) : Saved B g m' := fun i hi => by
  rw [hf.readW (Region.contains_self _ _) (fun r hr => (dj_offR B (d := 56) (n := 32) h (by decide) hl r hr).sub_left
    (sub_sub B (by omega_using [hi]) (by omega_using [hi]) (by decide))) (by decide)]
  exact hs i hi

theorem rval_frame' {B : Addr} {m m' : Mem} {l : List (Nat × Nat)} (hf : Frame (offR B l) m m')
    (h : (l.all fun p => 124 ≤ p.1 ∨ p.1 + p.2 ≤ 88) = true) (hl : (l.all fun p => p.1 + p.2 < 2 ^ 32) = true)
    {i : Nat} (hi : i < 10) : rval m' B i = rval m B i := by
  obtain hro := rOff_lt i hi
  obtain h88 : 88 ≤ rOff i := by
    have : ∀ i < 10, 88 ≤ rOff i := by decide +kernel
    exact this i hi
  obtain hd : ∀ n, rOff i + n ≤ 124 → ∀ r ∈ offR B l, (⟨B + BitVec.ofNat 64 (rOff i), n⟩ : Region).Disjoint r :=
    fun n hn r hr => (dj_offR B (d := 88) (n := 36) h (by decide) hl r hr).sub_left
      (sub_sub B (by omega_using [h88]) (by omega_using [hn]) (by decide))
  obtain hb : ∀ i < 10, rOff i + 1 ≤ 124 := by decide +kernel
  obtain hw : ∀ i < 10, ¬(i = 4 ∨ i = 9) → rOff i + 4 ≤ 124 := by decide +kernel
  simp only [rval]
  split
  · rename_i h49
    congr 1
    exact hf _ fun r hr hc => hd 1 (hb i hi) r hr _ ((Region.contains_self _ _).byte (by simp)) hc
  · rename_i h49
    rw [hf.readW (Region.contains_self _ _) (hd 4 (hw i hi h49)) (by decide)]

theorem rlimb_frame' {B : Addr} {m m' : Mem} {l : List (Nat × Nat)} (hf : Frame (offR B l) m m')
    (h : (l.all fun p => 40 ≤ p.1 ∨ p.1 + p.2 ≤ 24) = true) (hl : (l.all fun p => p.1 + p.2 < 2 ^ 32) = true) :
    rlimb m' B = rlimb m B :=
  rlimb_frame fun i hi => hf.readW (Region.contains_self _ _) (fun r hr =>
    (dj_offR B (d := 24) (n := 16) h (by decide) hl r hr).sub_left (sub_sub B (by omega_using [hi]) (by omega_using [hi]) (by decide)))
    (by decide)

theorem accD_frame {B : Addr} {m m' : Mem} {l : List (Nat × Nat)} (hf : Frame (offR B l) m m')
    (h : (l.all fun p => 20 ≤ p.1) = true) (hl : (l.all fun p => p.1 + p.2 < 2 ^ 32) = true) :
    accD m' B = accD m B := by
  obtain hw : ∀ i < 5, hwd m' B i = hwd m B i := fun i hi => by
    simp only [hwd]
    rw [hf.readW (Region.contains_self _ _) (fun r hr =>
      (dj_offR B (d := 0) (n := 20) (by
        rw [List.all_eq_true] at h ⊢
        intro p hp; have := h p hp; simp only [decide_eq_true_eq] at this ⊢; omega_using [this]) (by decide) hl r hr).sub_left
      (sub_sub B (by omega_using [hi]) (by omega_using [hi]) (by decide))) (by decide)]
  funext k
  simp only [accD, hw 0 (by decide), hw 1 (by decide), hw 2 (by decide), hw 3 (by decide), hw 4 (by decide)]

/-- The key's bytes. -/
theorem key_frame {B : Addr} {m m' : Mem} {l : List (Nat × Nat)} (hf : Frame (offR B l) m m')
    (h : (l.all fun p => 56 ≤ p.1 ∨ p.1 + p.2 ≤ 24) = true) (hl : (l.all fun p => p.1 + p.2 < 2 ^ 32) = true) :
    bytesAt m' (B + 24) 32 = bytesAt m (B + 24) 32 := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  obtain hd := dj_offR B (d := 24) (n := 32) h (by decide) hl
  rw [show (24 : Addr) = BitVec.ofNat 64 24 from rfl] at *
  exact hf.bytes (R := ⟨B + BitVec.ofNat 64 24, 32⟩) hd (by simp) (List.mem_range.mp hi)

/-! ## The stored accumulator -/

/-- The accumulator's limbs, if it is below `p`. -/
theorem val_accD_eq {m : Mem} {B : Addr} (h : leNum (bytesAt m B 24) < P) :
    val (accD m B) = leNum (bytesAt m B 24) := by
  rw [val_accD, leNum_bytesAt_24] at *
  simp only [hwd, Nat.mul_zero, Nat.reduceMul] at *
  simp only [P] at h
  omega_using [h]

end VG.Proof.Poly1305.Arm

end

/-!
# Poly1305 on 32-bit ARM: `blocks`' precondition, and the baseline's setup and reduction

What `blocks` is given (`BPre`), and, for the arithmetic in radix `2¹³`, the
limbs of `r` and the accumulator's columns from the state (`setupB_ok`) and
the columns reduced fully (`reduce_ok`).
-/

namespace VG.Proof.Poly1305.Arm

open VG VG.Arm VG.Impl.Poly1305.Arm
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr)

section
variable (s₀ : State)
/-- The state's address. -/
abbrev stB : Addr := State.addr (s₀.gpr .r0)
/-- The limbs of the clamped `r`, and its value. -/
abbrev Rl : Nat → Nat := rlimb s₀.mem (stB s₀)
abbrev Rn : Nat := val (Rl s₀)
/-- The accumulator on entry (if it is below `p`). -/
abbrev A0 : Nat := val (accD s₀.mem (stB s₀))
/-- The number of blocks, their region, and the first `i` of them. -/
abbrev nb : Nat := (s₀.gpr .r2).toNat
abbrev blR : Region := ⟨State.addr (s₀.gpr .r1), 16 * nb s₀⟩
abbrev blks (i : Nat) : List Byte := bytesAt s₀.mem (State.addr (s₀.gpr .r1)) (16 * i)
end

/-- The ranges of the state written once the registers are saved: `[0, 24)`
and `[56, 128)`. -/
abbrev wkL : List (Nat × Nat) := [(0, 24), (56, 72)]

theorem mod_step {h X M R : Nat} (hv : h % P = X % P) :
    ((h + M) * R) % P = (R * (X + M)) % P % P := by
  rw [Nat.mod_mod, Nat.mul_comm R, Nat.mul_mod, Nat.add_mod, hv, ← Nat.add_mod, ← Nat.mul_mod]

theorem eval_ne (s : State) : isa.eval .ne s = some !s.z := rfl
theorem eval_eq (s : State) : isa.eval .eq s = some s.z := rfl

theorem ofNat_beq_zero {k : Nat} (h : k < 2 ^ 32) : (BitVec.ofNat 32 k == 0) = decide (k = 0) := by
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
    exact hk this

theorem KeepsF.sub {ws : List Reg} {F F' : List Region} {s s' : State} (h : KeepsF ws F s s')
    (hs : ∀ r ∈ F, ∃ r' ∈ F', Region.Sub r r') : KeepsF ws F' s s' :=
  ⟨h.gpr, h.frame.sub hs, h.rd, h.wr, h.sp⟩

/-- The precondition of `blocks`, by field. -/
structure BPre (s₀ : State) : Prop where
  rd : s₀.rd = [blR s₀]
  wr : s₀.wr = [stR (s₀.gpr .r0)]
  st_bl : (stR (s₀.gpr .r0)).Disjoint (blR s₀)
  st_fit : (s₀.gpr .r0).toNat + 128 ≤ 2 ^ 32
  bl_fit : (s₀.gpr .r1).toNat + 16 * nb s₀ ≤ 2 ^ 32

theorem BPre.of (s : State) (h : Proof.Poly1305.blocksArm.pre s) : BPre s := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

/-! ## A block -/

theorem blks_succ (s₀ : State) (i : Nat) :
    blks s₀ (i + 1) = blks s₀ i ++ bytesAt s₀.mem (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 (16 * i)) 16 := by
  simp only [blks]
  rw [show 16 * (i + 1) = 16 * i + 16 by omega_using [], Poly1305.bytesAt_add]

/-- The block's value with the `0x01` byte appended. -/
theorem leNum_pad (b : List Byte) (h : b.length = 16) : leNum (b ++ [0x01]) = leNum b + 2 ^ 128 := by
  rw [Poly1305.leNum_append, h]; rfl

/-! ## Setup -/

section
variable {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32)
include hfit

/-- The limbs of `r` and the accumulator's columns, from the state's key and accumulator. -/
theorem setupB_ok {s : State} (h0 : s.gpr .r0 = st) (hw : stR st ∈ s.wr) :
    WP isa (.block (setupR ++ loadAcc)) s fun s' =>
      (∀ k < 10, rval s'.mem (State.addr st) k = rlimb s.mem (State.addr st) k) ∧
      ColsD (accD s.mem (State.addr st)) (State.addr st) s' ∧
      KeepsF (.r1 :: .r2 :: .r12 :: yregs) (offR (State.addr st) [(0, 20), (88, 36)]) s s' := by
  refine WP.append (setupR_ok hfit h0 hw) fun s₁ ⟨hr₁, k₁⟩ => ?_
  have f₁ : Frame (offR (State.addr st) [(88, 36)]) s.mem s₁.mem := k₁.frame
  refine WP.mono (loadAcc_ok hfit (by rw [k₁.gpr _ (by decide), h0]) (by rw [k₁.wr]; exact hw))
    fun s₂ ⟨hc₂, k₂⟩ => ⟨fun k hk => ?_, ?_, ?_⟩
  · rw [rval_frame k₂.frame hk]; exact hr₁ k hk
  · rw [← accD_frame f₁ (by decide) (by decide)]; exact hc₂
  · have k₁' : KeepsF (.r1 :: .r2 :: .r12 :: yregs) (offR (State.addr st) [(88, 36)]) s s₁ := k₁
    refine (k₁'.sub (sub_offR _ (l' := [(0, 20), (88, 36)]) (by decide) (by decide))).trans ?_
    have := k₂.sub (F' := offR (State.addr st) [(0, 20), (88, 36)]) (by
      rw [accR_offR]; exact sub_offR _ (by decide) (by decide))
    exact this

/-- Reducing the columns fully (see `reduceRegs`). -/
theorem reduce_ok {D : Nat → Nat} (hD : ∀ k < 10, D k ≤ 3564723200) {s : State} (h0 : s.gpr .r0 = st)
    (hw : stR st ∈ s.wr) (hc : ColsD D (State.addr st) s) :
    WP isa (.block reduce) s fun s' => Cols (redL D) s' ∧ Keeps (.r2 :: .r12 :: cregs) s s' := by
  rw [reduce]
  refine wp_ldr (a := State.addr st + BitVec.ofNat 64 16) (by decide) (by rw [h0]; exact ea hfit (off := 16) (by decide))
    (inSt hw (off := 16) (n := 4) (by decide)) fun s₁ u₁ => ?_
  obtain hc₁ : Cols D s₁ := fun j hj => by
    rcases Nat.lt_or_ge j 9 with h | h
    · rw [u₁.other _ (yr_ne j h).2.1]; exact hc.1 j h
    · rw [show j = 9 by omega_using [hj, h], yr9, u₁.gpr]; exact hc.2
  refine WP.mono (reduceRegs_ok (fun j hj => by have := hD j hj; omega_using [this]) hc₁) fun s₂ ⟨hc₂, _, k₂⟩ =>
    ⟨hc₂, (u₁.keeps (by simp [cregs])).trans k₂⟩

end

theorem blks_zero (s₀ : State) : blks s₀ 0 = [] := by simp [blks, bytesAt]

/-! ## The accumulator's words -/

/-- The stores of the accumulator's first five words. -/
def accList : List (Reg × Nat × Bool) :=
  [(.r3, 0, false), (.r5, 4, false), (.r7, 8, false), (.r10, 12, false), (.r1, 16, false)]

theorem accList_frame (B : Addr) : accList.map (sregion B) = offR B [(0, 4), (4, 4), (8, 4), (12, 4), (16, 4)] :=
  rfl

theorem preserved_cases : ∀ r ∈ preserved, r = .lr ∨ ∃ i < 8, savedReg i = r := by decide

/-- The accumulator's words as a number. -/
theorem val_words {L : Nat → Nat} (hL : ∀ j < 9, L j < 2 ^ 13) :
    tw0 L + 2 ^ 32 * tw1 L + 2 ^ 64 * tw2 L + 2 ^ 96 * tw3 L + 2 ^ 128 * (L 9 / 2 ^ 11) + 2 ^ 160 * 0 =
      val L := by
  rw [val_toWords hL, tw0, tw1, tw2, tw3]; omega_using []

end VG.Proof.Poly1305.Arm

end

end

/-!
# Poly1305 on 32-bit ARM: the steps of `blocks`, `update` and `finalize`

The code takes a flag, `umaal`, for its arithmetic: the baseline's, in radix
`2¹³` (`Bytes.lean`, `Blocks.lean`), or that of CPUs with `umaal`, in radix
`2³²` (`Umaal.lean`). What the functions need of either is the same
(`AccI`): at a block boundary (`Acc`), the accumulator is congruent modulo
`p` to an accumulator followed by some blocks; the setup (`setupAcc_ok`),
absorbing a block (`absorbI_ok`, `absorbAcc_ok`), the loop body of `blocks`
over any blocks (`body_gen`), and reducing and storing the accumulator
(`reduceI_ok`, `storeAcc_ok`) keep track of them, each proven for both by
cases. The callee-saved registers are saved in and restored from `scratch`
(`saveScr_ok`, `restoreScr_ok`), and bytes are copied into the buffer, bytes
56–71 of the state (`copy_ok`). `blocks` itself is the last section.
-/

@[expose] public section

namespace VG.Proof.Poly1305.Arm

open VG VG.Arm VG.Impl.Poly1305.Arm
open VG.Spec.Poly1305 (P leNum bytesAt accumulate Repr)

/-! ## At a block boundary, for either arithmetic -/

/-- What holds at a block boundary of the state at `B` and the registers,
with the accumulator congruent to `v` modulo `p`: for the baseline, the limbs
`R` of `r` are stored and the columns (`ColsD`) are below the bound that
keeps the next ones in a word; with `umaal`, `WAcc`. -/
def AccI : Bool → Addr → (Nat → Nat) → Nat → State → Prop
  | false, B, R, v, s => (∀ k < 10, rval s.mem B k = R k) ∧
      ∃ D, ColsD D B s ∧ (∀ k < 10, D k ≤ 3564723200) ∧ val D % P = v % P
  | true, B, R, v, s => WAcc B (val R) v s

theorem AccI.congr {umaal : Bool} {B : Addr} {R : Nat → Nat} {v v' : Nat} {s : State}
    (h : AccI umaal B R v s) (hv : v % P = v' % P) : AccI umaal B R v' s := by
  cases umaal
  · obtain ⟨hr, D, hc, hb, hd⟩ := h
    exact ⟨hr, D, hc, hb, hd.trans hv⟩
  · exact WAcc.congr h hv

theorem wregs_yregs : ∀ q ∈ wregs, q ∈ yregs := by decide

/-- `AccI` holds while the registers `r3`–`r11` and the state's words at
`[16, 20)` and `[88, 124)` stay. -/
theorem AccI.keep {umaal : Bool} {B : Addr} {R : Nat → Nat} {v : Nat} {s s' : State} (h : AccI umaal B R v s)
    {ws : List Reg} {l : List (Nat × Nat)} (hk : KeepsF ws (offR B l) s s')
    (hn : ∀ r ∈ ws, r ∉ yregs)
    (hl : (l.all fun p => (20 ≤ p.1 ∨ p.1 + p.2 ≤ 16) ∧ (124 ≤ p.1 ∨ p.1 + p.2 ≤ 88)) = true)
    (hl' : (l.all fun p => p.1 + p.2 < 2 ^ 32) = true) : AccI umaal B R v s' := by
  cases umaal
  · obtain ⟨hr, D, hcD, hDb, hDv⟩ := h
    refine ⟨fun k hk' => ?_, D, ⟨fun k hk' => ?_, ?_⟩, hDb, hDv⟩
    · rw [rval_frame' hk.frame (by
        rw [List.all_eq_true] at hl ⊢
        intro p hp; have := hl p hp; simp only [decide_eq_true_eq] at this ⊢; exact this.2) hl' hk']
      exact hr k hk'
    · rw [hk.gpr _ fun h' => hn _ h' (yr_yregs k hk')]; exact hcD.1 k hk'
    · rw [hk.frame.word (by
        rw [List.all_eq_true] at hl ⊢
        intro p hp; have := hl p hp; simp only [decide_eq_true_eq] at this ⊢; omega_using [this]) (by decide) hl']
      exact hcD.2
  · refine WAcc.keep h (fun q hq => hk.gpr _ fun h' => hn _ h' (wregs_yregs q hq)) fun i hi => ?_
    exact hk.frame.word (by
      rw [List.all_eq_true] at hl ⊢
      intro p hp; have := hl p hp; simp only [decide_eq_true_eq] at this ⊢; omega_using [this, hi])
      (by omega_using [hi]) hl'

/-- `r0` points at the state `st`, and (`AccI`) the accumulator is congruent
modulo `p` to the accumulator `A` followed by the blocks `X`, with `R` the
limbs of `r`. -/
structure Acc (umaal : Bool) (st : BitVec 32) (R : Nat → Nat) (A : Nat) (X : List Byte) (s : State) :
    Prop where
  r0 : s.gpr .r0 = st
  wr : stR st ∈ s.wr
  inv : AccI umaal (State.addr st) R (Poly1305.absorbAll (val R) A X) s

/-- `Acc` holds while the registers `r0` and `r3`–`r11`, the writable regions
and the state's words at `[16, 20)` and `[88, 124)` stay. -/
theorem Acc.keep {umaal : Bool} {st : BitVec 32} {R : Nat → Nat} {A : Nat} {X : List Byte} {s s' : State}
    (h : Acc umaal st R A X s) {ws : List Reg} {l : List (Nat × Nat)}
    (hk : KeepsF ws (offR (State.addr st) l) s s')
    (hws : (ws.all fun r => r != .r0 && !yregs.contains r) = true)
    (hl : (l.all fun p => (20 ≤ p.1 ∨ p.1 + p.2 ≤ 16) ∧ (124 ≤ p.1 ∨ p.1 + p.2 ≤ 88)) = true)
    (hl' : (l.all fun p => p.1 + p.2 < 2 ^ 32) = true) : Acc umaal st R A X s' := by
  obtain hn : ∀ r ∈ ws, r ≠ .r0 ∧ r ∉ yregs := fun r hr => by
    have := List.all_eq_true.mp hws r hr
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not] at this
    exact this
  exact ⟨by rw [hk.gpr _ fun h' => (hn _ h').1 rfl, h.r0], by rw [hk.wr]; exact h.wr,
    h.inv.keep hk (fun r hr => (hn r hr).2) hl hl'⟩

/-! ## The code of either arithmetic -/

theorem setup_false : setup false = setupR ++ loadAcc := rfl
theorem setup_true : setup true = setupU ++ loadAccU := rfl
theorem absorbV_false (pad : Bool) : absorbV false pad = absorb pad := rfl
theorem absorbV_true (pad : Bool) : absorbV true pad = absorbU pad := rfl
theorem reduceV_false : reduceV false = reduce ++ toWords := rfl
theorem reduceV_true : reduceV true = reduceU := rfl

section
variable {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32)
include hfit

/-- The multipliers and the accumulator, from the state's key and accumulator. -/
theorem setupAcc_ok {umaal : Bool} {s : State} (h0 : s.gpr .r0 = st) (hw : stR st ∈ s.wr) :
    WP isa (.block (setup umaal)) s fun s' =>
      AccI umaal (State.addr st) (rlimb s.mem (State.addr st)) (val (accD s.mem (State.addr st))) s' ∧
      KeepsF (.r1 :: .r2 :: .r12 :: yregs) (offR (State.addr st) [(0, 20), (88, 36)]) s s' := by
  cases umaal
  · rw [setup_false]
    exact WP.mono (setupB_ok hfit h0 hw) fun s' ⟨hr, hc, k⟩ =>
      ⟨⟨hr, _, hc, fun k _ => by have := accD_lt s.mem (State.addr st) k; omega_using [this], rfl⟩, k⟩
  · rw [setup_true]
    refine WP.mono (setupU_wacc hfit h0 hw) fun s' ⟨ha, k⟩ => ⟨ha, (k.mono ?_).sub ?_⟩
    · decide
    · intro r hr
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_map.mpr ⟨(88, 36), by decide, rfl⟩, fun _ h => h⟩

/-- Absorbing the block at `r1`, plus `2¹²⁸` if `pad`. -/
theorem absorbI_ok {umaal : Bool} (pad : Bool) {R : Nat → Nat} (hR : ∀ i < 10, R i < 2 ^ 13) {v : Nat}
    {s : State} (h0 : s.gpr .r0 = st) (hw : stR st ∈ s.wr) (h : AccI umaal (State.addr st) R v s)
    (hin : ∀ i < 4, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * i))) 4) :
    WP isa (.block (absorbV umaal pad)) s fun s' =>
      AccI umaal (State.addr st) R ((v + msgVal s + if pad then 2 ^ 128 else 0) * val R) s' ∧
      KeepsF work [accR (State.addr st)] s s' := by
  cases umaal
  · obtain ⟨hr, D, hcD, hDb, hDv⟩ := h
    rw [absorbV_false]
    refine WP.mono (absorb_ok hfit pad hR hDb h0 hw hr hcD hin) fun s' ⟨D', hc', hb', hv', k'⟩ =>
      ⟨⟨fun k hk => ?_, D', hc', hb', ?_⟩, k'⟩
    · rw [rval_frame k'.frame hk]; exact hr k hk
    · rw [hv', Nat.mul_mod, Nat.add_mod (val D + msgVal s), Nat.add_mod (val D), hDv, ← Nat.add_mod v,
        ← Nat.add_mod, ← Nat.mul_mod]
  · rw [absorbV_true]
    exact WP.mono (absorbU_wacc hfit pad h0 hw h hin) fun s' ⟨ha, k⟩ => ⟨ha, k.keepsF _⟩

/-- Absorbing the block at `a`, at `r1`. -/
theorem absorbAcc_ok {umaal : Bool} {R : Nat → Nat} (hR : ∀ i < 10, R i < 2 ^ 13) {A : Nat} {X : List Byte}
    (hX : X.length % 16 = 0) {s : State} (h : Acc umaal st R A X s) {a : Addr}
    (ha : ∀ j < 4, State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * j)) = a + BitVec.ofNat 64 (4 * j))
    (hin : ∀ j < 4, InRegions (s.rd ++ s.wr) (a + BitVec.ofNat 64 (4 * j)) 4) :
    WP isa (.block (absorbV umaal true)) s fun s' =>
      Acc umaal st R A (X ++ bytesAt s.mem a 16) s' ∧ KeepsF work [accR (State.addr st)] s s' := by
  refine WP.mono (absorbI_ok hfit true hR h.r0 h.wr h.inv fun j hj => by rw [ha j hj]; exact hin j hj)
    fun s' ⟨hi', k'⟩ => ⟨⟨by rw [k'.gpr _ (by decide), h.r0], by rw [k'.wr]; exact h.wr, hi'.congr ?_⟩, k'⟩
  have hmsg : msgVal s = leNum (bytesAt s.mem a 16) := by
    rw [leNum_bytesAt_16, msgVal]
    simp only [word]
    rw [ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide)]
  obtain hl := Poly1305.length_bytesAt s.mem a 16
  rw [Poly1305.absorbAll_append hX,
    Poly1305.absorbAll_block (b := bytesAt s.mem a 16) (by omega_using [hl]) (by omega_using [hl]), hmsg,
    leNum_pad _ hl, iteT rfl, Nat.mod_mod, Nat.mul_comm (val R), Nat.add_assoc]

omit hfit in
theorem body_eq (umaal : Bool) :
    body umaal = .block (([.ldr .r1 .r0 ptrOff, .dp .add .r2 .r1 (.imm 16), .str .r2 .r0 ptrOff] : List Instr) ++
      (absorbV umaal true ++ ([.ldr .r1 .r0 cntOff, .subs .r1 .r1 (.imm 1), .str .r1 .r0 cntOff] : List Instr))) := by
  simp only [body, List.append_assoc]

/-- The loop body of `blocks`, with the block pointer `p` and the count `c`
stored in the state. -/
theorem body_gen {umaal : Bool} {R : Nat → Nat} (hR : ∀ i < 10, R i < 2 ^ 13) {A : Nat} {X : List Byte}
    (hX : X.length % 16 = 0) {s : State} (h : Acc umaal st R A X s) {p : BitVec 32} {c : Nat}
    (hptr : s.mem.readW (State.addr st + BitVec.ofNat 64 124) 32 = p)
    (hcnt : s.mem.readW (State.addr st + BitVec.ofNat 64 20) 32 = BitVec.ofNat 32 c) (hc : 0 < c)
    (hc32 : c < 2 ^ 32) (hpf : p.toNat + 16 ≤ 2 ^ 32)
    (hin : ∀ j < 4, InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 (4 * j)) 4)
    (hd : (⟨State.addr p, 16⟩ : Region).Disjoint ⟨State.addr st + BitVec.ofNat 64 124, 4⟩) :
    WP isa (body umaal) s fun s' => Acc umaal st R A (X ++ bytesAt s.mem (State.addr p) 16) s' ∧
      KeepsF work (offR (State.addr st) [(0, 24), (124, 4)]) s s' ∧
      s'.mem.readW (State.addr st + BitVec.ofNat 64 124) 32 = p + 16 ∧
      s'.mem.readW (State.addr st + BitVec.ofNat 64 20) 32 = BitVec.ofNat 32 (c - 1) ∧
      s'.z = decide (c - 1 = 0) := by
  have hs0 := h.r0
  have hw := h.wr
  rw [body_eq, List.cons_append, List.cons_append, List.cons_append, List.nil_append]
  refine wp_ldr (a := State.addr st + BitVec.ofNat 64 124) (by decide)
    (by rw [hs0]; exact ea hfit (off := 124) (by decide)) (inSt hw (off := 124) (n := 4) (by decide))
    fun s₁ u₁ => ?_
  refine wp_add (op2_imm (by decide)) fun s₂ u₂ => ?_
  refine wp_str (a := State.addr st + BitVec.ofNat 64 124) (by decide)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hs0]; exact ea hfit (off := 124) (by decide))
    (by rw [u₂.wr, u₁.wr]; exact outSt hw (off := 124) (n := 4) (by decide)) fun s₃ u₃ => ?_
  obtain hp₃ : s₃.gpr .r1 = p := by rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, hptr]
  obtain m₃ : s₃.mem = s.mem.writeW (State.addr st + BitVec.ofNat 64 124) (p + 16) := by
    rw [u₃.mem, u₂.gpr, u₁.gpr, u₂.mem, u₁.mem, hptr]
  obtain f₃ : Frame (offR (State.addr st) [(124, 4)]) s.mem s₃.mem := by
    rw [m₃]
    exact Frame.writeOff (Frame.refl _ _) (a := 124) (len := 4) (List.mem_singleton_self _) (Nat.le_refl _) (Nat.le_refl _)
      (by decide) _ rfl
  obtain k₃ : KeepsF [.r1, .r2] (offR (State.addr st) [(124, 4)]) s s₃ :=
    ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [u₃.gpr, u₂.other _ hr.2, u₁.other _ hr.1],
      f₃, by rw [u₃.rd, u₂.rd, u₁.rd], by rw [u₃.wr, u₂.wr, u₁.wr], by rw [u₃.sp, u₂.sp, u₁.sp]⟩
  obtain hA₃ : Acc umaal st R A X s₃ := h.keep k₃ (by decide) (by decide) (by decide)
  obtain hblk : bytesAt s₃.mem (State.addr p) 16 = bytesAt s.mem (State.addr p) 16 :=
    bytesAt_frame f₃ (fun r hr => by
      simp only [offR, List.map_cons, List.map_nil, List.mem_singleton] at hr; subst hr; exact hd)
      (by decide)
  rw [← List.append_nil [Instr.ldr .r1 .r0 cntOff, .subs .r1 .r1 (.imm 1), .str .r1 .r0 cntOff]]
  refine WP.append (absorbAcc_ok hfit hR hX hA₃ (a := State.addr p)
    (fun j hj => by rw [hp₃]; exact addr_add (by omega_using [hpf, hj]))
    (fun j hj => by rw [k₃.rd, k₃.wr]; exact hin j hj)) fun s₄ ⟨hA₄, k₄⟩ => ?_
  rw [hblk] at hA₄
  have hs40 : s₄.gpr .r0 = st := hA₄.r0
  have hw₄ : stR st ∈ s₄.wr := hA₄.wr
  obtain f₄ : Frame (offR (State.addr st) [(0, 20)]) s₃.mem s₄.mem := by rw [← accR_offR]; exact k₄.frame
  refine wp_ldr (a := State.addr st + BitVec.ofNat 64 20) (by decide)
    (by rw [hs40]; exact ea hfit (off := 20) (by decide)) (inSt hw₄ (off := 20) (n := 4) (by decide))
    fun s₅ u₅ => ?_
  refine wp_subs (op2_imm (by decide)) fun s₆ u₆ hz₆ => ?_
  refine wp_str (a := State.addr st + BitVec.ofNat 64 20) (by decide)
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), hs40]; exact ea hfit (off := 20) (by decide))
    (by rw [u₆.wr, u₅.wr]; exact outSt hw₄ (off := 20) (n := 4) (by decide)) fun s₇ u₇ => WP.block_nil ?_
  obtain hc₅ : s₅.gpr .r1 = BitVec.ofNat 32 c := by
    rw [u₅.gpr, f₄.word (by decide) (by decide) (by decide), f₃.word (by decide) (by decide) (by decide), hcnt]
  obtain hc₆ : s₆.gpr .r1 = BitVec.ofNat 32 (c - 1) := by
    rw [u₆.gpr, hc₅, show c = (c - 1) + 1 by omega_using [hc, hc32], BitVec.ofNat_add, Nat.add_sub_cancel]
    exact BitVec.add_sub_cancel _ _
  obtain m₇ : s₇.mem = s₄.mem.writeW (State.addr st + BitVec.ofNat 64 20) (BitVec.ofNat 32 (c - 1)) := by
    rw [u₇.mem, hc₆, u₆.mem, u₅.mem]
  obtain k₄₇ : KeepsF [.r1] (offR (State.addr st) [(20, 4)]) s₄ s₇ := by
    refine ⟨fun r hr => ?_, ?_, by rw [u₇.rd, u₆.rd, u₅.rd], by rw [u₇.wr, u₆.wr, u₅.wr],
      by rw [u₇.sp, u₆.sp, u₅.sp]⟩
    · have h1 : r ≠ .r1 := by rintro rfl; exact hr (by decide)
      rw [u₇.gpr, u₆.other _ h1, u₅.other _ h1]
    · rw [m₇]
      exact Frame.writeOff (Frame.refl _ _) (a := 20) (len := 4) (List.mem_singleton_self _) (Nat.le_refl _) (Nat.le_refl _)
        (by decide) _ rfl
  refine ⟨hA₄.keep k₄₇ (by decide) (by decide) (by decide), ?_, ?_, by rw [m₇, Mem.readW_writeW_self32], ?_⟩
  · refine ((k₃.mono (by simp [work])).sub (sub_offR _ (by decide) (by decide))).trans
      (((k₄.sub (by rw [accR_offR]; exact sub_offR _ (by decide) (by decide))).trans
        ((k₄₇.mono (by simp [work])).sub (sub_offR _ (by decide) (by decide)))))
  · rw [m₇, readW_writeW_off _ _ _ (by decide) (by decide) (by decide),
      f₄.word (by decide) (by decide) (by decide), m₃, Mem.readW_writeW_self32]
  · rw [u₇.z, hz₆, ← u₆.gpr, hc₆, ofNat_beq_zero (by omega_using [hc, hc32])]

/-- The accumulator reduced fully: its words, of `v mod p`. -/
theorem reduceI_ok {umaal : Bool} {R : Nat → Nat} {v : Nat} {s : State} (h0 : s.gpr .r0 = st)
    (hw : stR st ∈ s.wr) (h : AccI umaal (State.addr st) R v s) :
    WP isa (.block (reduceV umaal)) s fun s' => ∃ w0 w1 w2 w3 w4, OutW w0 w1 w2 w3 w4 s' ∧
      Limbs32.val5 w0 w1 w2 w3 w4 = v % P ∧ Keeps work s s' := by
  cases umaal
  · obtain ⟨-, D, hcD, hDb, hDv⟩ := h
    obtain hE : ∀ j < 10, D j < 2 ^ 32 - 2 ^ 19 := fun j hj => by have := hDb j hj; omega_using [this]
    obtain ⟨-, -, -, hvL, hlL⟩ := red_facts D hE
    rw [reduceV_false]
    refine WP.append (reduce_ok hfit hDb h0 hw hcD) fun s₁ ⟨hc₁, k₁⟩ => ?_
    refine WP.mono (toWords_ok hc₁ fun j hj => hlL j (by omega_using [hj])) fun s₂ ⟨e3, e5, e7, e10, e1, k₂⟩ =>
      ⟨_, _, _, _, _, ⟨e3, e5, e7, e10, e1⟩, ?_, ?_⟩
    · rw [← hDv, ← hvL, val_toWords fun j hj => hlL j (by omega_using [hj])]
      rfl
    · exact (k₁.mono (by decide)).trans (k₂.mono (by decide))
  · rw [reduceV_true]
    exact reduceU_wacc h

/-- Reducing the accumulator fully and storing it. -/
theorem storeAcc_ok {umaal : Bool} {R : Nat → Nat} {A : Nat} {X : List Byte} {s : State}
    (h : Acc umaal st R A X s) :
    WP isa (.block (reduceV umaal ++ storeAcc)) s fun s' =>
      leNum (bytesAt s'.mem (State.addr st) 24) = Poly1305.absorbAll (val R) A X % P ∧
      KeepsF work (offR (State.addr st) [(0, 24)]) s s' := by
  refine WP.append (reduceI_ok hfit h.r0 h.wr h.inv) fun s₂ ⟨w0, w1, w2, w3, w4, ⟨o3, o5, o7, o10, o1⟩, hv, k₂⟩ => ?_
  obtain hs₂0 : s₂.gpr .r0 = st := by rw [k₂.gpr _ (by decide), h.r0]
  obtain hw₂ : stR st ∈ s₂.wr := by rw [k₂.wr]; exact h.wr
  rw [show storeAcc = accList.map (storeI .r0) ++ [.mov .r2 (.imm 0), .str .r2 .r0 20] from rfl]
  refine WP.append (stores_ok .r0 hfit rfl accList s₂ hs₂0 hw₂ (by decide) (by decide))
    fun s₃ ⟨hs₃, hf₃, hg₃, hrd₃, hwr₃, hsp₃⟩ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₄ u₄ => ?_
  refine wp_str (a := State.addr st + BitVec.ofNat 64 20) (by decide)
    (by rw [u₄.other _ (by decide), hg₃, hs₂0]; exact ea hfit (off := 20) (by decide))
    (by rw [u₄.wr, hwr₃]; exact outSt hw₂ (off := 20) (n := 4) (by decide)) fun s₅ u₅ => WP.block_nil ?_
  obtain m₅ : s₅.mem = s₃.mem.writeW (State.addr st + BitVec.ofNat 64 20) (0 : BitVec 32) := by
    rw [u₅.mem, u₄.gpr, u₄.mem]
  obtain f₅ : Frame (offR (State.addr st) [(0, 24)]) s.mem s₅.mem := by
    rw [m₅, ← k₂.mem]
    rw [accList_frame] at hf₃
    exact Frame.writeOff (hf₃.offR_sub (by decide) (by decide)) (a := 0) (len := 24) (by decide) (by decide)
      (by decide) (by decide) _ rfl
  -- The words stored.
  obtain w : ∀ x ∈ accList, ∀ d, x.2.1 = d → x.2.2 = false →
      s₅.mem.readW (State.addr st + BitVec.ofNat 64 d) 32 = s₂.gpr x.1 := by
    intro x hx d hd hb
    have := hs₃ x hx
    obtain ⟨r, o, b⟩ := x
    simp only at hd hb; subst hd hb
    obtain hl : o + 4 ≤ 20 := by
      have : ∀ x ∈ accList, x.2.1 + 4 ≤ 20 := by decide
      exact this _ hx
    rw [m₅, readW_writeW_off _ _ _ (by omega_using [hl]) (by decide) (by omega_using [hl])]
    exact this
  refine ⟨?_, ⟨fun r hr => ?_, f₅, ?_, ?_, ?_⟩⟩
  · have e0 := w _ (by decide : (Reg.r3, 0, false) ∈ accList) 0 rfl rfl
    obtain e4 := w _ (by decide : (Reg.r5, 4, false) ∈ accList) 4 rfl rfl
    obtain e8 := w _ (by decide : (Reg.r7, 8, false) ∈ accList) 8 rfl rfl
    obtain e12 := w _ (by decide : (Reg.r10, 12, false) ∈ accList) 12 rfl rfl
    obtain e16 := w _ (by decide : (Reg.r1, 16, false) ∈ accList) 16 rfl rfl
    obtain e20 : s₅.mem.readW (State.addr st + BitVec.ofNat 64 20) 32 = 0 := by rw [m₅, Mem.readW_writeW_self32]
    simp only at e0 e4 e8 e12 e16
    rw [leNum_bytesAt_24, e0, e4, e8, e12, e16, e20, o3, o5, o7, o10, o1, ← hv]
    rfl
  · obtain h2 : r ≠ .r2 := by rintro rfl; exact hr (by decide)
    rw [u₅.gpr, u₄.other _ h2, hg₃]
    exact k₂.gpr r hr
  · rw [u₅.rd, u₄.rd, hrd₃, k₂.rd]
  · rw [u₅.wr, u₄.wr, hwr₃, k₂.wr]
  · rw [u₅.sp, u₄.sp, hsp₃, k₂.sp]

end

theorem accD_of_words {m m' : Mem} {B : Addr}
    (h : ∀ i < 5, m'.readW (B + BitVec.ofNat 64 (4 * i)) 32 = m.readW (B + BitVec.ofNat 64 (4 * i)) 32) :
    accD m' B = accD m B := by
  obtain hw : ∀ i < 5, hwd m' B i = hwd m B i := fun i hi => by simp only [hwd, h i hi]
  funext k
  simp only [accD, hw 0 (by decide), hw 1 (by decide), hw 2 (by decide), hw 3 (by decide), hw 4 (by decide)]

/-! ## Arguments on the stack -/

theorem wp_sub {is : List Instr} {s : State} {Q : State → Prop} {d n : Reg} {o : Op2} {y : BitVec 32}
    (ho : o.eval s = some y) (k : ∀ s', Upd s s' d (s.gpr n - y) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .sub d n o :: is)) s Q :=
  WP.cons (s' := s.setReg d (s.gpr n - y)) (by simp [exec, ho]) (k _ (Upd.setReg _ _ _))

theorem Fupd.keeps {s s' : State} (h : Fupd s s') (ws : List Reg) : Keeps ws s s' :=
  ⟨fun r _ => by rw [h.gpr], h.mem, h.rd, h.wr, h.sp⟩

theorem wp_ldrSp {is : List Instr} {s : State} {Q : State → Prop} {t : Reg} {off : Nat} {a : Addr}
    (ho : off < 4096) (ha : State.addr (s.sp + BitVec.ofNat 32 off) = a) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', Upd s s' t (s.mem.readW a 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldrSp t off :: is)) s Q := by
  subst ha
  exact WP.cons (s' := s.setReg t (s.mem.readW _ 32)) (by simp [exec, ho, State.load32, hin])
    (k _ (Upd.setReg _ _ _))

/-! ## The registers saved in `scratch` -/

/-- The registers `g` saved at `[0, 32)` of the scratch space at `C`. -/
def SavedS (C : Addr) (g : Reg → BitVec 32) (m : Mem) : Prop :=
  ∀ i < 8, m.readW (C + BitVec.ofNat 64 (4 * i)) 32 = g (savedReg i)

def saveSList : List (Reg × Nat × Bool) := (List.range 8).map fun i => (savedReg i, 4 * i, false)

theorem saveScr_eq : saveScr = saveSList.map (storeI .r12) := rfl

/-- The scratch space's region. -/
abbrev scrR (sc : BitVec 32) : Region := ⟨State.addr sc, 128⟩

section
variable {sc : BitVec 32} (hsc : sc.toNat + 128 ≤ 2 ^ 32)
include hsc

theorem saveScr_ok {s : State} (h12 : s.gpr .r12 = sc) (hw : scrR sc ∈ s.wr) :
    WP isa (.block saveScr) s fun s' => SavedS (State.addr sc) s.gpr s'.mem ∧
      Frame [⟨State.addr sc, 32⟩] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp := by
  rw [saveScr_eq]
  refine WP.mono (stores_ok .r12 hsc rfl saveSList s h12 hw (by decide) (by decide))
    fun s' ⟨hs, hf, hg, hrd, hwr, hsp⟩ => ⟨fun i hi => ?_, hf.sub fun r hr => ?_, hg, hrd, hwr, hsp⟩
  · exact hs (savedReg i, 4 * i, false) (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have := List.mem_range.mp hi
    exact ⟨_, List.mem_singleton_self _, sub_base _ (by simp only [ssize]; omega_using [this]) (by decide)⟩

theorem restoreScr_ok {s : State} {g : Reg → BitVec 32} (h12 : s.gpr .r12 = sc) (hw : scrR sc ∈ s.wr)
    (hs : SavedS (State.addr sc) g s.mem) :
    WP isa (.block restoreScr) s fun s' => (∀ i < 8, s'.gpr (savedReg i) = g (savedReg i)) ∧
      Keeps [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] s s' := by
  obtain hsr : ∀ i < 8, savedReg i ∈ [Reg.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] := by decide +kernel
  obtain hinj : ∀ i < 8, ∀ j < 8, savedReg i = savedReg j → i = j := by decide +kernel
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n s' => (∀ i < n, s'.gpr (savedReg i) = g (savedReg i)) ∧
      Keeps [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] s s')
    (fun n s' hn ⟨hl, hk⟩ => ?_) 8 (Nat.le_refl _) s ⟨fun _ h => absurd h (by omega_using [h]), Keeps.refl _ _⟩)
    fun s' h => h
  refine wp_ldr (a := State.addr sc + BitVec.ofNat 64 (4 * n)) (by omega_using [hn])
    (by rw [hk.gpr _ (by decide), h12]; exact addr_add (by omega_using [hsc, hn]))
    (by rw [hk.rd, hk.wr]; exact ⟨_, List.mem_append_right _ hw, contains_off (by omega_using [hn]) (by omega_using [hn])⟩)
    fun s1 u1 => WP.block_nil ⟨fun i hi => ?_, hk.trans (u1.keeps (hsr n hn))⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | rfl
  · rw [u1.other _ (fun e => absurd (hinj _ (by omega_using [hn, h']) _ hn e) (by omega_using [h']))]; exact hl i h'
  · rw [u1.gpr, hk.mem]; exact hs i hn

end

/-! ## Copying bytes into the buffer -/

theorem add_ofNat_one (x : BitVec 32) (j : Nat) : x + BitVec.ofNat 32 j + 1 = x + BitVec.ofNat 32 (j + 1) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]; rfl

/-- The buffer of the state at `B`. -/
abbrev bufR (B : Addr) : Region := ⟨B + BitVec.ofNat 64 56, 16⟩

/-- What copying the bytes `xs` from `src` needs, in the state `sI`: they are
readable, not in the buffer, and in memory. -/
def SrcOk (sI : State) (B : Addr) (src : BitVec 32) (xs : List Byte) : Prop :=
  ∀ i < xs.length, InRegions (sI.rd ++ sI.wr) (State.addr src + BitVec.ofNat 64 i) 1 ∧
    ¬ (bufR B).Contains (State.addr src + BitVec.ofNat 64 i) 1 ∧
    sI.mem (State.addr src + BitVec.ofNat 64 i) = xs.getD i 0

/-- While copying the bytes `xs` from `src` to the buffer of the state at `st`
from its byte `j0` on, from the state `sI`: after `j` bytes. -/
structure CopyInv (sI : State) (st src : BitVec 32) (j0 : Nat) (xs : List Byte) (j : Nat) (s : State) :
    Prop where
  j_le : j ≤ xs.length
  r5 : s.gpr .r5 = src + BitVec.ofNat 32 j
  r1 : s.gpr .r1 = st + BitVec.ofNat 32 (j0 + j)
  r8 : s.gpr .r8 = BitVec.ofNat 32 (xs.length - j)
  keep : ∀ r, r ∉ [Reg.r1, .r5, .r8, .r12] → s.gpr r = sI.gpr r
  rd : s.rd = sI.rd
  wr : s.wr = sI.wr
  sp : s.sp = sI.sp
  mem : s.mem = writeBytes sI.mem (State.addr st + BitVec.ofNat 64 (56 + j0)) (xs.take j)

section
variable {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32)
include hfit

theorem copy_step {sI : State} {src : BitVec 32} {j0 : Nat} {xs : List Byte} (hj0 : j0 + xs.length ≤ 16)
    (hsrc : src.toNat + xs.length ≤ 2 ^ 32) (hw : stR st ∈ sI.wr) (hS : SrcOk sI (State.addr st) src xs)
    {j : Nat} (hj : j < xs.length) {s : State} (h : CopyInv sI st src j0 xs j s) :
    WP isa (.block copyBody) s fun s' =>
      CopyInv sI st src j0 xs (j + 1) s' ∧ s'.z = decide (xs.length - (j + 1) = 0) := by
  obtain ⟨hin, hnb, hm₀⟩ := hS j hj
  obtain hq : (bufR (State.addr st)).Contains (State.addr st + BitVec.ofNat 64 (56 + j0)) (xs.take j).length := by
    rw [List.length_take]
    exact contains_sub _ (by omega_using []) (by omega_using [hj0, hj]) (by decide)
  obtain hbyte : s.mem (State.addr src + BitVec.ofNat 64 j) = xs.getD j 0 := by
    rw [h.mem, ← hm₀]
    exact writeBytes_frame _ _ _ hq _ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hnb
  refine wp_ldrb (t := .r12) (a := State.addr src + BitVec.ofNat 64 j) (by decide)
    (by rw [h.r5, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_zero]; exact addr_add (by omega_using [hsrc, hj]))
    (by rw [h.rd, h.wr]; exact hin) fun s₁ u₁ => ?_
  refine wp_strb (t := .r12) (a := State.addr st + BitVec.ofNat 64 (56 + j0 + j)) (by decide)
    (by rw [u₁.other _ (by decide), h.r1, BitVec.add_assoc, ← BitVec.ofNat_add,
      show j0 + j + 56 = 56 + j0 + j by omega_using []]; exact ea hfit (by omega_using [hj0, hj]))
    (by rw [u₁.wr, h.wr]; exact outSt hw (by omega_using [hj0, hj])) fun s₂ m₂ => ?_
  refine wp_add (op2_imm (by decide)) fun s₃ u₃ => wp_add (op2_imm (by decide)) fun s₄ u₄ => ?_
  refine wp_subs (op2_imm (by decide)) fun s₅ u₅ hz => WP.block_nil ?_
  obtain hr8 : s₅.gpr .r8 = BitVec.ofNat 32 (xs.length - (j + 1)) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), m₂.gpr, u₁.other _ (by decide), h.r8,
      show xs.length - j = (xs.length - (j + 1)) + 1 by omega_using [hj], BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ _
  refine ⟨⟨by omega_using [hj], ?_, ?_, hr8, fun r hr => ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, m₂.gpr, u₁.other _ (by decide), h.r5,
      add_ofNat_one]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), m₂.gpr, u₁.other _ (by decide), h.r1,
      ← Nat.add_assoc, add_ofNat_one]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₅.other _ hr.2.2.1, u₄.other _ hr.1, u₃.other _ hr.2.1, m₂.gpr, u₁.other _ hr.2.2.2]
    exact h.keep r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2])
  · rw [u₅.rd, u₄.rd, u₃.rd, m₂.rd, u₁.rd, h.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, m₂.wr, u₁.wr, h.wr]
  · rw [u₅.sp, u₄.sp, u₃.sp, m₂.sp, u₁.sp, h.sp]
  · have hl : (xs.take j).length = j := by rw [List.length_take, Nat.min_eq_left (by omega_using [hj])]
    obtain hv : (s₁.gpr .r12).setWidth 8 = xs[j] := by
      rw [u₁.gpr, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq, hbyte]
      simp [List.getD_eq_getElem?_getD, hj]
    rw [u₅.mem, u₄.mem, u₃.mem, m₂.mem, hv, u₁.mem, h.mem, List.take_add_one,
      List.getElem?_eq_getElem hj, Option.toList_some, writeBytes_snoc _ _ _ _ (by omega_using [hsrc, hj, hl]), hl, off_add]
  · rw [hz, ← u₅.gpr, hr8, ofNat_beq_zero (by omega_using [hj0, hj])]

theorem copy_ok {sI : State} {src : BitVec 32} {j0 : Nat} {xs : List Byte} (hj0 : j0 + xs.length ≤ 16)
    (hsrc : src.toNat + xs.length ≤ 2 ^ 32) (hn : 0 < xs.length) (hw : stR st ∈ sI.wr)
    (hS : SrcOk sI (State.addr st) src xs) (h5 : sI.gpr .r5 = src)
    (h1 : sI.gpr .r1 = st + BitVec.ofNat 32 j0) (h8 : sI.gpr .r8 = BitVec.ofNat 32 xs.length) :
    WP isa copyIn sI (CopyInv sI st src j0 xs xs.length) := by
  obtain h₀ : CopyInv sI st src j0 xs 0 sI :=
    ⟨by omega_using [hn], by rw [h5]; simp, by rw [h1, Nat.add_zero], by rw [h8, Nat.sub_zero], fun _ _ => rfl, rfl, rfl,
      rfl, by rw [List.take_zero, writeBytes_nil]⟩
  refine WP.loop (M := isa) (fun k s => ∃ j, k = xs.length - j ∧ j < xs.length ∧ CopyInv sI st src j0 xs j s)
    ?_ xs.length sI ⟨0, by omega_using [hn], hn, h₀⟩
  rintro k s ⟨j, rfl, hj, hc⟩
  refine WP.mono (copy_step hfit hj0 hsrc hw hS hj hc) fun s' ⟨hc', hz⟩ => ?_
  by_cases hl : xs.length - (j + 1) = 0
  · refine .inl ⟨by rw [eval_ne, hz]; simp [hl], ?_⟩
    rwa [show j + 1 = xs.length by omega_using [hj, hl]] at hc'
  · exact .inr ⟨by rw [eval_ne, hz]; simp [hl], _, by omega_using [hj], j + 1, rfl, by omega_using [hj, hl], hc'⟩

omit hfit in
/-- After copying: the buffer's first `j0` bytes and the bytes copied. -/
theorem CopyInv.buf {sI : State} {src : BitVec 32} {j0 : Nat} {xs : List Byte} (hj0 : j0 + xs.length ≤ 16)
    {s : State} (h : CopyInv sI st src j0 xs xs.length s) :
    bytesAt s.mem (State.addr st + 56) (j0 + xs.length) = bytesAt sI.mem (State.addr st + 56) j0 ++ xs := by
  rw [h.mem, List.take_of_length_le (Nat.le_refl _), ← off_add]
  exact bytesAt_writeBytes sI.mem (State.addr st + 56) j0 xs (by omega_using [hj0])

omit hfit in
theorem CopyInv.frame {sI : State} {src : BitVec 32} {j0 : Nat} {xs : List Byte} (hj0 : j0 + xs.length ≤ 16)
    {s : State} (h : CopyInv sI st src j0 xs xs.length s) : Frame [bufR (State.addr st)] sI.mem s.mem := by
  rw [h.mem, List.take_of_length_le (Nat.le_refl _)]
  exact writeBytes_frame _ _ _ (contains_sub _ (by omega_using []) (by omega_using [hj0]) (by decide))

end

/-! ## `blocks`

After saving the registers, storing the block pointer and count in the state,
computing the multipliers and loading the accumulator (`prologue_ok`), each
block is absorbed (`blocksBody_ok`); then the accumulator is reduced and
stored (`epilogue_ok`). Between blocks (`Common`) it is congruent modulo `p`
to the accumulator of the blocks so far. -/

/-- Between blocks, after `i` of them. -/
structure Common (umaal : Bool) (s₀ : State) (i : Nat) (s : State) : Prop where
  keeps : KeepsF work (offR (stB s₀) wkL) s₀ s
  saved : Saved (stB s₀) s₀.gpr s.mem
  acc : Acc umaal (s₀.gpr .r0) (Rl s₀) (A0 s₀) (blks s₀ i) s

/-- The loop invariant, before block `i`. -/
structure LInv (umaal : Bool) (s₀ : State) (i : Nat) (s : State) : Prop extends Common umaal s₀ i s where
  ptr : s.mem.readW (stB s₀ + BitVec.ofNat 64 124) 32 = s₀.gpr .r1 + BitVec.ofNat 32 (16 * i)
  cnt : s.mem.readW (stB s₀ + BitVec.ofNat 64 20) 32 = BitVec.ofNat 32 (nb s₀ - i)

variable {umaal : Bool}

theorem blocksBody_ok {s₀ : State} (hp : BPre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv umaal s₀ i s) :
    WP isa (body umaal) s fun s' =>
      (isa.eval .ne s' = some false ∧ Common umaal s₀ (nb s₀) s') ∨
      (isa.eval .ne s' = some true ∧ i + 1 < nb s₀ ∧ LInv umaal s₀ (i + 1) s') := by
  have hfit := hp.st_fit
  have hbf := hp.bl_fit
  obtain hn32 : nb s₀ < 2 ^ 32 := (s₀.gpr .r2).isLt
  have hk := hL.keeps
  obtain hpA : State.addr (s₀.gpr .r1 + BitVec.ofNat 32 (16 * i)) =
      State.addr (s₀.gpr .r1) + BitVec.ofNat 64 (16 * i) := addr_add (by omega_using [hi, hbf])
  obtain hsub : Region.Sub ⟨State.addr (s₀.gpr .r1) + BitVec.ofNat 64 (16 * i), 16⟩ (blR s₀) :=
    sub_base _ (by omega_using [hi]) (by omega_using [hn32])
  obtain hfr : Frame [stR (s₀.gpr .r0)] s₀.mem s.mem :=
    hk.frame.sub fun r hr => by
      obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hr
      simp only [wkL, List.mem_cons, List.not_mem_nil, or_false] at hp'
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      rcases hp' with rfl | rfl
      · exact sub_base _ (by decide) (by decide)
      · exact sub_base _ (by decide) (by decide)
  obtain hblk : bytesAt s.mem (State.addr (s₀.gpr .r1 + BitVec.ofNat 32 (16 * i))) 16 =
      bytesAt s₀.mem (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 (16 * i)) 16 := by
    rw [hpA]
    exact Poly1305.bytesAt_frame hfr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.st_bl.sub_right hsub).symm) (by decide)
  refine WP.mono (body_gen hfit (fun i _ => rlimb_lt _ _ i)
      (by simp only [blks, Poly1305.length_bytesAt]; omega_using []) hL.acc hL.ptr hL.cnt
      (by omega_using [hi]) (by omega_using [hi, hn32])
      (by rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * i) (by omega_using [hi, hbf]),
            Nat.mod_eq_of_lt (by omega_using [hi, hbf])]
          omega_using [hi, hbf])
      (fun j hj => by
        rw [hpA, off_add, hk.rd, hp.rd]
        exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _),
          contains_off (off := 16 * i + 4 * j) (n := 4) (len := 16 * nb s₀) (by omega_using [hi, hj])
            (by omega_using [hi, hn32, hj])⟩)
      (by rw [hpA]
          exact ((hp.st_bl.sub_right hsub).sub_left (sub_base _ (a := 124) (len := 4) (len' := 128) (by decide)
            (by decide))).symm))
    fun s' ⟨hA', k', hptr, hcnt, hz⟩ => ?_
  obtain hC : Common umaal s₀ (i + 1) s' := by
    refine ⟨hk.trans (k'.sub (sub_offR _ (by decide) (by decide))), hL.saved.frame k'.frame (by decide) (by decide), ?_⟩
    rw [hblk, ← blks_succ] at hA'
    exact hA'
  by_cases hlast : i + 1 = nb s₀
  · exact .inl ⟨by rw [eval_ne, hz]; simp; omega_using [hlast], hlast ▸ hC⟩
  · refine .inr ⟨by rw [eval_ne, hz]; simp; omega_using [hi, hlast], by omega_using [hi, hlast],
      { hC with ptr := ?_, cnt := ?_ }⟩
    · rw [hptr, BitVec.add_assoc, show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, ← BitVec.ofNat_add]
      rfl
    · rw [hcnt, Nat.sub_sub]

theorem prologue_ok {s₀ : State} (hp : BPre s₀) :
    WP isa (.block (saveRegs ++ ([.str .r1 .r0 ptrOff, .str .r2 .r0 cntOff] : List Instr) ++ setup umaal ++
      ([.ldr .r1 .r0 cntOff, .cmp .r1 (.imm 0)] : List Instr))) s₀ fun s =>
      LInv umaal s₀ 0 s ∧ s.z = (s₀.gpr .r2 == 0) := by
  have hfit := hp.st_fit
  obtain hw : stR (s₀.gpr .r0) ∈ s₀.wr := by rw [hp.wr]; exact List.mem_singleton_self _
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine WP.append (saveRegs_ok hfit rfl hw) fun s₁ ⟨hsv, hf₁, hg₁, hrd₁, hwr₁, hsp₁⟩ => ?_
  obtain hw₁ : stR (s₀.gpr .r0) ∈ s₁.wr := by rw [hwr₁]; exact hw
  refine wp_str (a := stB s₀ + BitVec.ofNat 64 124) (by decide)
    (by rw [hg₁]; exact ea hfit (off := 124) (by decide)) (outSt hw₁ (off := 124) (n := 4) (by decide))
    fun s₂ u₂ => ?_
  refine wp_str (a := stB s₀ + BitVec.ofNat 64 20) (by decide)
    (by rw [u₂.gpr, hg₁]; exact ea hfit (off := 20) (by decide))
    (by rw [u₂.wr]; exact outSt hw₁ (off := 20) (n := 4) (by decide)) fun s₃ u₃ => ?_
  obtain m₃ : s₃.mem = (s₁.mem.writeW (stB s₀ + BitVec.ofNat 64 124) (s₀.gpr .r1)).writeW
      (stB s₀ + BitVec.ofNat 64 20) (s₀.gpr .r2) := by rw [u₃.mem, u₂.mem, u₂.gpr, hg₁]
  obtain f₁₃ : Frame (offR (stB s₀) [(20, 4), (124, 4)]) s₁.mem s₃.mem := by
    rw [m₃]
    exact Frame.writeOff (Frame.writeOff (Frame.refl _ _) (a := 124) (len := 4) (by decide) (Nat.le_refl _) (Nat.le_refl _)
      (by decide) _ rfl) (a := 20) (len := 4) (by decide) (Nat.le_refl _) (Nat.le_refl _) (by decide) _ rfl
  obtain hs₃0 : s₃.gpr .r0 = s₀.gpr .r0 := by rw [u₃.gpr, u₂.gpr, hg₁]
  obtain hw₃ : stR (s₀.gpr .r0) ∈ s₃.wr := by rw [u₃.wr, u₂.wr]; exact hw₁
  refine WP.append (setupAcc_ok hfit hs₃0 hw₃) fun s₄ ⟨ha₄, k₄⟩ => ?_
  obtain hs₄0 : s₄.gpr .r0 = s₀.gpr .r0 := by rw [k₄.gpr _ (by decide), hs₃0]
  obtain hw₄ : stR (s₀.gpr .r0) ∈ s₄.wr := by rw [k₄.wr]; exact hw₃
  refine wp_ldr (a := stB s₀ + BitVec.ofNat 64 20) (by decide)
    (by rw [hs₄0]; exact ea hfit (off := 20) (by decide)) (inSt hw₄ (off := 20) (n := 4) (by decide))
    fun s₅ u₅ => wp_cmp (op2_imm (by decide)) fun s₆ u₆ hz => WP.block_nil ?_
  have f₀₁ : Frame (offR (stB s₀) [(56, 32)]) s₀.mem s₁.mem := hf₁
  obtain f₁₄ : Frame (offR (stB s₀) [(0, 20), (20, 4), (88, 36), (124, 4)]) s₁.mem s₄.mem :=
    (f₁₃.offR_sub (by decide) (by decide)).trans (k₄.frame.offR_sub (by decide) (by decide))
  obtain m₆ : s₆.mem = s₄.mem := by rw [u₆.mem, u₅.mem]
  -- The key and the stored accumulator on entry.
  obtain f₀₃ : Frame (offR (stB s₀) [(20, 4), (56, 32), (124, 4)]) s₀.mem s₃.mem :=
    (f₀₁.offR_sub (by decide) (by decide)).trans (f₁₃.offR_sub (by decide) (by decide))
  obtain hRl : rlimb s₃.mem (stB s₀) = Rl s₀ := rlimb_frame' f₀₃ (by decide) (by decide)
  obtain hA : accD s₃.mem (stB s₀) = accD s₀.mem (stB s₀) := accD_frame f₀₃ (by decide) (by decide)
  rw [hRl, hA] at ha₄
  obtain hptr : s₄.mem.readW (stB s₀ + BitVec.ofNat 64 124) 32 = s₀.gpr .r1 := by
    rw [k₄.frame.word (by decide) (by decide) (by decide), m₃,
      readW_writeW_off _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  obtain hcnt : s₄.mem.readW (stB s₀ + BitVec.ofNat 64 20) 32 = s₀.gpr .r2 := by
    rw [k₄.frame.word (by decide) (by decide) (by decide), m₃, Mem.readW_writeW_self32]
  obtain k₄₆ : KeepsF [.r1] (offR (stB s₀) []) s₄ s₆ :=
    ((u₅.keeps (ws := [.r1]) (by simp)).trans ⟨fun r _ => by rw [u₆.gpr], u₆.mem, u₆.rd, u₆.wr, u₆.sp⟩).keepsF _
  refine ⟨⟨⟨⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · have h1 : r ≠ .r1 := by rintro rfl; exact hr (by decide)
    rw [u₆.gpr, u₅.other _ h1, k₄.gpr _ (by
      simp only [yregs, List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨h1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> exact hr (by decide)),
      u₃.gpr, u₂.gpr, hg₁]
  · rw [m₆]
    exact (f₀₁.offR_sub (by decide) (by decide)).trans (f₁₄.offR_sub (by decide) (by decide))
  · rw [u₆.rd, u₅.rd, k₄.rd, u₃.rd, u₂.rd, hrd₁]
  · rw [u₆.wr, u₅.wr, k₄.wr, u₃.wr, u₂.wr, hwr₁]
  · rw [u₆.sp, u₅.sp, k₄.sp, u₃.sp, u₂.sp, hsp₁]
  · rw [m₆]; exact hsv.frame f₁₄ (by decide) (by decide)
  · exact (Acc.mk hs₄0 hw₄ (by rw [blks_zero, Poly1305.absorbAll_nil]; exact ha₄)).keep k₄₆ (by decide)
      (by decide) (by decide)
  · rw [m₆, hptr]; simp
  · rw [m₆, hcnt]; simp [nb]
  · rw [hz, u₅.gpr, hcnt]; simp

theorem epilogue_ok {s₀ : State} (hp : BPre s₀) {s : State} (hc : Common umaal s₀ (nb s₀) s) :
    WP isa (.block (reduceV umaal ++ storeAcc ++ restoreRegs)) s fun s' =>
      abiPreserved s₀ s' ∧ Proof.Poly1305.blocksArm.post s₀ s' := by
  have hfit := hp.st_fit
  refine WP.append (storeAcc_ok hfit hc.acc) fun s₅ ⟨hv₅, k₅⟩ => ?_
  obtain hs₅0 : s₅.gpr .r0 = s₀.gpr .r0 := by rw [k₅.gpr _ (by decide), hc.acc.r0]
  obtain hw₅ : stR (s₀.gpr .r0) ∈ s₅.wr := by rw [k₅.wr]; exact hc.acc.wr
  refine WP.mono (restoreRegs_ok hfit hs₅0 hw₅ (hc.saved.frame k₅.frame (by decide) (by decide)))
    fun s' ⟨hr', k'⟩ => ?_
  obtain f' : Frame (offR (stB s₀) wkL) s₀.mem s'.mem := by
    rw [k'.mem]; exact hc.keeps.frame.trans (k₅.frame.offR_sub (by decide) (by decide))
  refine ⟨⟨fun r hr => ?_, ?_⟩, fun key msg hrep => ?_⟩
  · rcases preserved_cases r hr with rfl | ⟨i, hi, rfl⟩
    · rw [k'.gpr _ (by decide), k₅.gpr _ (by decide), hc.keeps.gpr _ (by decide)]
    · exact hr' i hi
  · rw [k'.sp, k₅.sp, hc.keeps.sp]
  · obtain ⟨hlen, hkey, hacc⟩ := hrep
    have hkey' := hkey
    rw [← key_frame f' (by decide) (by decide)] at hkey'
    refine ⟨?_, hkey', ?_⟩
    · rw [List.length_append, Poly1305.length_bytesAt]; omega_using [hlen]
    · rw [← hkey, take_bytesAt _ _ (by decide), ← val_rlimb, Poly1305.accumulate_append hlen]
      rw [← hkey, take_bytesAt _ _ (by decide), ← val_rlimb] at hacc
      obtain hlt : leNum (bytesAt s₀.mem (stB s₀) 24) < P := by
        rw [hacc]; exact Poly1305.accumulate_lt _ _
      obtain hA : accumulate (Rn s₀) msg = A0 s₀ := by
        rw [A0, val_accD_eq hlt]; exact hacc.symm
      obtain hlt' := Poly1305.absorbAll_lt (r := Rn s₀) (a := A0 s₀) (by rw [← hA]; exact Poly1305.accumulate_lt _ _)
        (blks s₀ (nb s₀))
      rw [hA, k'.mem, hv₅, Nat.mod_eq_of_lt hlt']

theorem blocks_correct {s₀ : State} (hp : BPre s₀) :
    WP isa (blocks umaal) s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Poly1305.blocksArm.post s₀ s' := by
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨hL, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := Common umaal s₀ (nb s₀)) ?_ fun s₂ hc => epilogue_ok hp hc)
  refine WP.ite s₁.z (eval_eq _) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by rw [h] at hz; simp only [nb]; rw [eq_of_beq hz.symm]; rfl
    exact WP.block_nil (M := isa) (h0 ▸ hL.toCommon)
  · have hpos : 0 < nb s₀ := by
      rw [h] at hz
      refine Nat.pos_of_ne_zero fun h' => ?_
      have : s₀.gpr .r2 = 0 := BitVec.eq_of_toNat_eq (by simpa [nb] using h')
      simp [this] at hz
    refine WP.loop (M := isa) (fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv umaal s₀ i s) ?_ (nb s₀) s₁
      ⟨0, rfl, hpos, hL⟩
    rintro m s ⟨i, rfl, hi, hLi⟩
    refine WP.mono (blocksBody_ok hp hi hLi) fun s' h' => ?_
    rcases h' with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
    · exact .inl ⟨he, hc⟩
    · exact .inr ⟨he, nb s₀ - (i + 1), by omega_using [hi'], i + 1, rfl, hi', hL'⟩

theorem blocks_ok (s : State) (hs : Proof.Poly1305.blocksArm.pre s) :
    ∃ t s', Exec isa (Impl.Poly1305.Arm.blocks umaal) s t s' ∧ abiPreserved s s' ∧
      Proof.Poly1305.blocksArm.post s s' :=
  blocks_correct (BPre.of s hs)

end VG.Proof.Poly1305.Arm

end

end

/-!
# Poly1305 on 32-bit ARM: `finalize`

After saving the registers in `scratch` (`prologue_ok`), a non-empty buffer is
padded in place with `0x01` and zeros (`pad_ok`); its length is stored, the
limbs of `r` computed and the accumulator loaded (`mid_ok`); the padded buffer
is absorbed (`last_ok`); then the accumulator is reduced fully and `s` is
added, modulo `2¹²⁸` (`tagI_ok`: the baseline's columns by `tagB_ok`, and
`umaal`'s words by `tagU_wacc`), and the sum is stored in `out` (`tag_ok`).
Until then (`FC`), only the state's working space, the buffer, the
accumulator and `scratch` change.
-/

@[expose] public section

namespace VG.Proof.Poly1305.Arm.Fin

open VG VG.Arm VG.Impl.Poly1305.Arm VG.Proof.Poly1305.Arm
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr Buffered leBytes mac)

variable {umaal : Bool}

/-! ## The precondition -/

section
variable (s₀ : State)
/-- `out` and `scratch`. -/
abbrev oP : BitVec 32 := stackArg s₀ 0
abbrev oA : Addr := State.addr (oP s₀)
abbrev oR : Region := ⟨oA s₀, 16⟩
abbrev sc : BitVec 32 := stackArg s₀ 1
/-- The stack arguments. -/
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 8⟩
/-- The number of bytes buffered, and the bytes. -/
abbrev kb : Nat := (s₀.gpr .r2).toNat % 16
abbrev Bf : List Byte := bytesAt s₀.mem (stB s₀ + 56) (kb s₀)
end

structure FPre (s₀ : State) : Prop where
  rd : s₀.rd = [argR s₀]
  wr : s₀.wr = [stR (s₀.gpr .r0), oR s₀, scrR (sc s₀)]
  st_o : (stR (s₀.gpr .r0)).Disjoint (oR s₀)
  st_scr : (stR (s₀.gpr .r0)).Disjoint (scrR (sc s₀))
  o_scr : (oR s₀).Disjoint (scrR (sc s₀))
  a_st : (argR s₀).Disjoint (stR (s₀.gpr .r0))
  a_o : (argR s₀).Disjoint (oR s₀)
  a_scr : (argR s₀).Disjoint (scrR (sc s₀))
  st_fit : (s₀.gpr .r0).toNat + 128 ≤ 2 ^ 32
  o_fit : (oP s₀).toNat + 16 ≤ 2 ^ 32
  sc_fit : (sc s₀).toNat + 128 ≤ 2 ^ 32
  sp_fit : s₀.sp.toNat + 8 ≤ 2 ^ 32

theorem FPre.of (s : State) (h : Proof.Poly1305.finalizeArm.pre s) : FPre s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

theorem kb_lt (s₀ : State) : kb s₀ < 16 := Nat.mod_lt _ (by decide)

theorem FPre.stW {s₀ : State} (hp : FPre s₀) {s : State} (h : s.wr = s₀.wr) : stR (s₀.gpr .r0) ∈ s.wr := by
  rw [h, hp.wr]; exact List.mem_cons_self

theorem FPre.oW {s₀ : State} (hp : FPre s₀) {s : State} (h : s.wr = s₀.wr) : oR s₀ ∈ s.wr := by
  rw [h, hp.wr]; exact List.mem_cons_of_mem _ List.mem_cons_self

theorem FPre.scW {s₀ : State} (hp : FPre s₀) {s : State} (h : s.wr = s₀.wr) : scrR (sc s₀) ∈ s.wr := by
  rw [h, hp.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))

/-- A range of the state is disjoint from `scratch`. -/
theorem FPre.st_scr' {s₀ : State} (hp : FPre s₀) {a n : Nat} (h : a + n ≤ 128) :
    (⟨stB s₀ + BitVec.ofNat 64 a, n⟩ : Region).Disjoint (scrR (sc s₀)) :=
  hp.st_scr.sub_left (sub_base _ h (by decide))

/-! ## What holds until the tag is stored -/

/-- The state's working space and buffer (`wkL`) and `scratch`. -/
abbrev fF (s₀ : State) : List Region := offR (stB s₀) wkL ++ [scrR (sc s₀)]

structure FC (s₀ s : State) : Prop where
  r0 : s.gpr .r0 = s₀.gpr .r0
  lr : s.gpr .lr = s₀.gpr .lr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame (fF s₀) s₀.mem s.mem
  saved : SavedS (State.addr (sc s₀)) s₀.gpr s.mem

theorem FC.keepsF {s₀ : State} (hp : FPre s₀) {s s' : State} (h : FC s₀ s) {ws : List Reg}
    {l : List (Nat × Nat)} (hk : KeepsF ws (offR (stB s₀) l) s s') (hws : Reg.r0 ∉ ws ∧ Reg.lr ∉ ws)
    (hl : (l.all fun p => wkL.any fun q => q.1 ≤ p.1 ∧ p.1 + p.2 ≤ q.1 + q.2) = true)
    (hl' : (l.all fun p => p.1 + p.2 ≤ 128) = true) : FC s₀ s' where
  r0 := by rw [hk.gpr _ hws.1, h.r0]
  lr := by rw [hk.gpr _ hws.2, h.lr]
  rd := hk.rd.trans h.rd
  wr := hk.wr.trans h.wr
  sp := hk.sp.trans h.sp
  frame := h.frame.trans ((hk.frame.offR_sub hl (by decide)).mono fun _ hr => List.mem_append_left _ hr)
  saved := fun i hi => by
    rw [hk.frame.readW (Region.contains_self _ _) (fun r hr => by
      obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hr
      have := List.all_eq_true.mp hl' p hp'
      simp only [decide_eq_true_eq] at this
      exact ((hp.st_scr' this).symm.sub_left (sub_base _ (by omega_using [hi]) (by decide)))) (by decide)]
    exact h.saved i hi

theorem FC.upd {s₀ s s' : State} (h : FC s₀ s) {d : Reg} {v : BitVec 32} (u : Upd s s' d v)
    (hd : d ≠ .r0 ∧ d ≠ .lr) : FC s₀ s' :=
  ⟨by rw [u.other _ (Ne.symm hd.1), h.r0], by rw [u.other _ (Ne.symm hd.2), h.lr], u.rd.trans h.rd,
    u.wr.trans h.wr, u.sp.trans h.sp, by rw [u.mem]; exact h.frame, by rw [u.mem]; exact h.saved⟩

theorem FC.flags {s₀ s s' : State} (h : FC s₀ s) (u : Fupd s s') : FC s₀ s' :=
  ⟨by rw [u.gpr, h.r0], by rw [u.gpr, h.lr], u.rd.trans h.rd, u.wr.trans h.wr, u.sp.trans h.sp,
    by rw [u.mem]; exact h.frame, by rw [u.mem]; exact h.saved⟩

/-- The address of stack argument `i`. -/
theorem argAddr {s₀ : State} (hp : FPre s₀) {i : Nat} (hi : i < 2) :
    stackArgAddr s₀ i = stackArgAddr s₀ 0 + BitVec.ofNat 64 (4 * i) := by
  have := hp.sp_fit
  simp only [stackArgAddr]
  rw [addr_add (by omega_using [hi, this]), addr_add (by omega_using [this])]
  simp

/-- Loading stack argument `i`, whose memory is as on entry. -/
theorem wp_arg {s₀ : State} (hp : FPre s₀) {s : State} (hsp : s.sp = s₀.sp) (hrd : s.rd = s₀.rd) {i : Nat}
    (hi : i < 2) (hm : s.mem.readW (stackArgAddr s₀ i) 32 = stackArg s₀ i) {t : Reg}
    {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' t (stackArg s₀ i) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldrSp t (4 * i) :: is)) s Q := by
  have := hp.sp_fit
  refine wp_ldrSp (a := stackArgAddr s₀ i) (by omega_using [hi]) (by rw [hsp]; rfl)
    (by rw [hrd, hp.rd, argAddr hp hi]
        exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _), contains_off (by omega_using [hi]) (by omega_using [hi])⟩)
    fun s' u => ?_
  rw [hm] at u
  exact k s' u

/-- The stack arguments are unchanged by writes to the state, `out` and `scratch`. -/
theorem FPre.arg {s₀ : State} (hp : FPre s₀) {m : Mem}
    (hf : Frame (offR (stB s₀) wkL ++ [oR s₀, scrR (sc s₀)]) s₀.mem m) {i : Nat} (hi : i < 2) :
    m.readW (stackArgAddr s₀ i) 32 = stackArg s₀ i := by
  rw [stackArg, hf.readW (r := argR s₀) (by rw [argAddr hp hi]; exact contains_off (by omega_using [hi]) (by omega_using [hi]))
    (fun r hr => ?_) (by decide)]
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hr
    simp only [wkL, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> exact hp.a_st.sub_right (sub_base _ (by decide) (by decide))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.a_o
    · exact hp.a_scr

/-! ## Prologue -/

theorem sub0 (x : BitVec 32) : x - 0 = x := by simp

theorem and15 (x : BitVec 32) : x &&& (15 : BitVec 32) = BitVec.ofNat 32 (x.toNat % 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (15 : BitVec 32).toNat = 2 ^ 4 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := x.toNat % 16) (by omega_using [])]

/-- After the prologue. -/
structure P1 (s₀ s : State) : Prop extends FC s₀ s where
  sfr : Frame [scrR (sc s₀)] s₀.mem s.mem
  r4 : s.gpr .r4 = BitVec.ofNat 32 (kb s₀)
  z : s.z = decide (kb s₀ = 0)

theorem prologue_ok {s₀ : State} (hp : FPre s₀) :
    WP isa (.block (([.ldrSp .r12 4] : List Instr) ++ saveScr ++ ([.dp .and .r4 .r2 (.imm 15), .cmp .r4 (.imm 0)] : List Instr))) s₀
      (P1 s₀) := by
  have hsc := hp.sc_fit
  refine wp_arg (i := 1) hp rfl rfl (by decide) rfl fun s₁ u₁ => ?_
  refine WP.append (saveScr_ok hsc u₁.gpr (by rw [u₁.wr]; exact hp.scW rfl))
    fun s₂ ⟨hsv, hf₂, hg₂, hrd₂, hwr₂, hsp₂⟩ => ?_
  obtain hf₂' : Frame [scrR (sc s₀)] s₀.mem s₂.mem := by
    rw [← u₁.mem]; exact hf₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
  obtain fc₂ : FC s₀ s₂ :=
    ⟨by rw [hg₂, u₁.other _ (by decide)], by rw [hg₂, u₁.other _ (by decide)], by rw [hrd₂, u₁.rd],
      by rw [hwr₂, u₁.wr], by rw [hsp₂, u₁.sp], hf₂'.mono fun _ hr => List.mem_append_right _ hr,
      fun i hi => by rw [hsv i hi, u₁.other _ (by revert i; decide)]⟩
  refine wp_and (op2_imm (by decide)) fun s₃ u₃ => ?_
  refine wp_cmp (op2_imm (by decide)) fun s₄ u₄ hz => WP.block_nil ?_
  obtain hr4 : s₃.gpr .r4 = BitVec.ofNat 32 (kb s₀) := by
    rw [u₃.gpr, hg₂, u₁.other _ (by decide)]
    exact and15 _
  refine ⟨(fc₂.upd u₃ (by decide)).flags u₄, by rw [u₄.mem, u₃.mem]; exact hf₂', by rw [u₄.gpr, hr4], ?_⟩
  rw [hz, hr4, sub0, ofNat_beq_zero (by have := kb_lt s₀; omega_using [this])]

/-! ## Padding the buffer in place -/

/-- Bytes `0`–`15` of the buffer of the state at `B` are `f 0`, …, `f 15`. -/
def BufHas (m : Mem) (B : Addr) (f : Nat → Byte) : Prop := ∀ k < 16, m (B + BitVec.ofNat 64 (56 + k)) = f k

/-- The padded block: the buffered bytes, `0x01`, zeros. -/
def padded (s₀ : State) (k : Nat) : Byte :=
  if k < kb s₀ then (Bf s₀).getD k 0 else if k = kb s₀ then 1 else 0

theorem buf_ne (B : Addr) {j k : Nat} (hj : j < 16) (hk : k < 16) (h : k ≠ j) :
    B + BitVec.ofNat 64 (56 + k) ≠ B + BitVec.ofNat 64 (56 + j) := by
  intro he
  obtain h2 : BitVec.ofNat 64 (56 + k) = BitVec.ofNat 64 (56 + j) := by simpa using he
  have := congrArg BitVec.toNat h2
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hk]), Nat.mod_eq_of_lt (by omega_using [hj, this])] at this
  exact h (by omega_using [this])

/-- The zero loop's invariant, before byte `j`, from the state `s₁` after the prologue. -/
structure ZInv (s₀ s₁ : State) (j : Nat) (s : State) : Prop where
  j_le : kb s₀ ≤ j ∧ j ≤ 16
  r1 : s.gpr .r1 = s₀.gpr .r0 + BitVec.ofNat 32 j
  r5 : s.gpr .r5 = BitVec.ofNat 32 (16 - j)
  r12 : s.gpr .r12 = 0
  keeps : KeepsF [.r1, .r5, .r12] (offR (stB s₀) [(56, 16)]) s₁ s
  buf : BufHas s.mem (stB s₀) fun k => if k < j then (if k < kb s₀ then s₁.mem (stB s₀ + BitVec.ofNat 64 (56 + k))
    else 0) else s₁.mem (stB s₀ + BitVec.ofNat 64 (56 + k))

theorem zinit_ok {s₀ s₁ : State} (h₁ : P1 s₀ s₁) :
    WP isa (.block [.mov .r12 (.imm 0), .dp .add .r1 .r0 (.reg .r4), .mov .r5 (.imm 16),
      .dp .sub .r5 .r5 (.reg .r4)]) s₁ (ZInv s₀ s₁ (kb s₀)) := by
  obtain hk := kb_lt s₀
  refine wp_mov (op2_imm (by decide)) fun s₂ u₂ => wp_add (op2_reg _ _) fun s₃ u₃ =>
    wp_mov (op2_imm (by decide)) fun s₄ u₄ => wp_sub (op2_reg _ _) fun s₅ u₅ => WP.block_nil ?_
  refine ⟨⟨(Nat.le_refl _), Nat.le_of_lt hk⟩, ?_, ?_, ?_, ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩, fun k hk' => ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other .r0 (by decide),
      u₂.other .r4 (by decide), h₁.r0, h₁.r4]
  · rw [u₅.gpr, u₄.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), h₁.r4,
      show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl]
    rw [show BitVec.ofNat 32 16 = BitVec.ofNat 32 (16 - kb s₀) + BitVec.ofNat 32 (kb s₀) by
      rw [← BitVec.ofNat_add, Nat.sub_add_cancel (by omega_using [hk])], BitVec.add_sub_cancel]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₅.other _ hr.2.1, u₄.other _ hr.2.1, u₃.other _ hr.1, u₂.other _ hr.2.2]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem]; exact Frame.refl _ _
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr]
  · rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem]
    by_cases h : k < kb s₀ <;> simp [h]

theorem zero_step {s₀ : State} (hp : FPre s₀) {s₁ : State} (h₁ : P1 s₀ s₁) {j : Nat} (hj : j < 16) {s : State}
    (h : ZInv s₀ s₁ j s) :
    WP isa (.block [.strb .r12 .r1 56, .dp .add .r1 .r1 (.imm 1), .subs .r5 .r5 (.imm 1)]) s fun s' =>
      ZInv s₀ s₁ (j + 1) s' ∧ s'.z = decide (16 - (j + 1) = 0) := by
  have hfit := hp.st_fit
  refine wp_strb (t := .r12) (a := stB s₀ + BitVec.ofNat 64 (56 + j)) (by decide)
    (by rw [h.r1, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm j]; exact ea hfit (by omega_using [hj]))
    (by rw [h.keeps.wr]; exact outSt (hp.stW h₁.wr) (by omega_using [hj])) fun s₂ m₂ => ?_
  refine wp_add (op2_imm (by decide)) fun s₃ u₃ => wp_subs (op2_imm (by decide)) fun s₄ u₄ hz => WP.block_nil ?_
  obtain hr5 : s₄.gpr .r5 = BitVec.ofNat 32 (16 - (j + 1)) := by
    rw [u₄.gpr, u₃.other _ (by decide), m₂.gpr, h.r5, show 16 - j = (16 - (j + 1)) + 1 by omega_using [hj],
      BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ _
  refine ⟨⟨⟨Nat.le_trans h.j_le.1 (Nat.le_succ _), by omega_using [hj]⟩, ?_, hr5, ?_, ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩,
    fun k hk => ?_⟩, ?_⟩
  · rw [u₄.other _ (by decide), u₃.gpr, m₂.gpr, h.r1, add_ofNat_one]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), m₂.gpr, h.r12]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₄.other _ hr.2.1, u₃.other _ hr.1, m₂.gpr, h.keeps.gpr r (by simp [hr.1, hr.2.1, hr.2.2])]
  · rw [u₄.mem, u₃.mem, m₂.mem]
    exact Frame.writeOff h.keeps.frame (a := 56) (len := 16) (List.mem_singleton_self _) (by omega_using [hj]) (by omega_using [hj])
      (by decide) _ rfl
  · rw [u₄.rd, u₃.rd, m₂.rd, h.keeps.rd]
  · rw [u₄.wr, u₃.wr, m₂.wr, h.keeps.wr]
  · rw [u₄.sp, u₃.sp, m₂.sp, h.keeps.sp]
  · rw [u₄.mem, u₃.mem, m₂.mem, writeW8_apply]
    by_cases hkj : k = j
    · subst hkj
      rw [iteT rfl, h.r12]
      simp only [show k < k + 1 by omega_using [], ite_true, show ¬ k < kb s₀ by have := h.j_le.1; omega_using [this], ite_false]
      rfl
    · rw [iteF (buf_ne _ hj hk hkj), h.buf k hk]
      by_cases h1 : k < j
      · simp only [h1, ite_true, show k < j + 1 by omega_using [h1]]
      · simp only [h1, ite_false, show ¬ k < j + 1 by omega_using [hkj, h1]]
  · rw [hz, ← u₄.gpr, hr5, ofNat_beq_zero (by omega_using [hj])]

theorem pad1_ok {s₀ : State} (hp : FPre s₀) {s₁ : State} (h₁ : P1 s₀ s₁) {s : State} (h : ZInv s₀ s₁ 16 s) :
    WP isa (.block [.mov .r12 (.imm 1), .dp .add .r1 .r0 (.reg .r4), .strb .r12 .r1 56]) s fun s' =>
      KeepsF [.r1, .r5, .r12] (offR (stB s₀) [(56, 16)]) s₁ s' ∧ BufHas s'.mem (stB s₀) (padded s₀) := by
  have hfit := hp.st_fit
  obtain hk := kb_lt s₀
  refine wp_mov (op2_imm (by decide)) fun s₂ u₂ => wp_add (op2_reg _ _) fun s₃ u₃ => ?_
  obtain hr1 : s₃.gpr .r1 = s₀.gpr .r0 + BitVec.ofNat 32 (kb s₀) := by
    rw [u₃.gpr, u₂.other .r0 (by decide), u₂.other .r4 (by decide), h.keeps.gpr .r0 (by decide),
      h.keeps.gpr .r4 (by decide), h₁.r0, h₁.r4]
  refine wp_strb (t := .r12) (a := stB s₀ + BitVec.ofNat 64 (56 + kb s₀)) (by decide)
    (by rw [hr1, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm (kb s₀)]; exact ea hfit (by omega_using [hk]))
    (by rw [u₃.wr, u₂.wr, h.keeps.wr]; exact outSt (hp.stW h₁.wr) (by omega_using [hk])) fun s₄ m₄ =>
      WP.block_nil ⟨⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩, fun k hk' => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [m₄.gpr, u₃.other _ hr.1, u₂.other _ hr.2.2, h.keeps.gpr r (by simp [hr.1, hr.2.1, hr.2.2])]
  · rw [m₄.mem, u₃.mem, u₂.mem]
    exact Frame.writeOff h.keeps.frame (a := 56) (len := 16) (List.mem_singleton_self _) (by omega_using [hk]) (by omega_using [hk])
      (by decide) _ rfl
  · rw [m₄.rd, u₃.rd, u₂.rd, h.keeps.rd]
  · rw [m₄.wr, u₃.wr, u₂.wr, h.keeps.wr]
  · rw [m₄.sp, u₃.sp, u₂.sp, h.keeps.sp]
  · have hB : ∀ k < kb s₀, s₁.mem (stB s₀ + BitVec.ofNat 64 (56 + k)) = (Bf s₀).getD k 0 := fun k hk'' => by
      simp only [Bf, bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk'',
        Option.map_some, Option.getD_some]
      rw [show (56 : Addr) = BitVec.ofNat 64 56 from rfl, off_add]
      refine h₁.sfr _ fun r hr hc => ?_
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_scr' (a := 56 + k) (n := 1) (by omega_using [hk, hk'']) _ (Region.contains_self _ _) hc
    rw [m₄.mem, u₃.mem, u₂.mem, writeW8_apply, u₃.other _ (by decide), u₂.gpr]
    by_cases hkj : k = kb s₀
    · subst hkj
      rw [iteT rfl]
      simp only [padded, Nat.lt_irrefl, ite_false, ite_true]
      rfl
    · rw [iteF (buf_ne _ hk hk' hkj), h.buf k hk']
      simp only [hk', ite_true]
      by_cases h1 : k < kb s₀
      · simp only [h1, ite_true, padded, hB k h1]
      · simp only [h1, ite_false, padded, hkj]

theorem padBuf_ok {s₀ : State} (hp : FPre s₀) {s₁ : State} (h₁ : P1 s₀ s₁) :
    WP isa padBuf s₁ fun s =>
      KeepsF [.r1, .r5, .r12] (offR (stB s₀) [(56, 16)]) s₁ s ∧ BufHas s.mem (stB s₀) (padded s₀) := by
  obtain hkl := kb_lt s₀
  refine WP.seq (WP.mono (zinit_ok h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (Q := ZInv s₀ s₁ 16) ?_ fun s₃ h₃ => pad1_ok hp h₁ h₃)
  refine WP.loop (M := isa) (fun n s => ∃ j, n = 16 - j ∧ j < 16 ∧ ZInv s₀ s₁ j s) ?_ _ s₂
    ⟨kb s₀, rfl, hkl, h₂⟩
  rintro n s ⟨j, rfl, hj, hz⟩
  refine WP.mono (zero_step hp h₁ hj hz) fun s' ⟨h', hz'⟩ => ?_
  by_cases hl : j + 1 = 16
  · exact .inl ⟨by rw [eval_ne, hz']; simp [hl], hl ▸ h'⟩
  · exact .inr ⟨by rw [eval_ne, hz']; simp; omega_using [hj, hl], _, by omega_using [hj], j + 1, rfl, by omega_using [hj, hl], h'⟩

/-- The padded block as a number: the buffered bytes with `0x01` appended. -/
theorem padded_value {s₀ : State} {m : Mem} (h : BufHas m (stB s₀) (padded s₀)) :
    leNum (bytesAt m (stB s₀ + BitVec.ofNat 64 56) 16) = leNum (Bf s₀ ++ [0x01]) := by
  obtain hk := kb_lt s₀
  obtain hlen : (Bf s₀).length = kb s₀ := Poly1305.length_bytesAt _ _ _
  obtain hl : bytesAt m (stB s₀ + BitVec.ofNat 64 56) 16 = (Bf s₀ ++ [0x01]) ++ List.replicate (15 - kb s₀) 0 := by
    apply List.ext_getElem
    · simp [hlen, Poly1305.length_bytesAt]; omega_using [hk, hlen]
    · intro k h₁ h₂
      rw [Poly1305.length_bytesAt] at h₁
      obtain e : (bytesAt m (stB s₀ + BitVec.ofNat 64 56) 16)[k] = padded s₀ k := by
        simp only [bytesAt, List.getElem_map, List.getElem_range]
        rw [off_add]; exact h k h₁
      refine e.trans ?_
      rcases Nat.lt_trichotomy k (kb s₀) with hk' | rfl | hk'
      · rw [List.getElem_append_left (by simp [hlen]; omega_using [hlen, hk']), List.getElem_append_left (by omega_using [hlen, hk'])]
        simp only [padded, hk', ite_true]
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show k < (Bf s₀).length by omega_using [hlen, hk'])]
      · rw [List.getElem_append_left (by simp [hlen]), List.getElem_append_right (by omega_using [hlen])]
        simp [padded, hlen]
      · rw [List.getElem_append_right (by simp [hlen]; omega_using [hlen, hk'])]
        simp [padded, show ¬ k < kb s₀ by omega_using [hlen, hk'], show k ≠ kb s₀ by omega_using [hlen, hk']]
  rw [hl, Poly1305.leNum_append _ (List.replicate _ _), Poly1305.leNum_replicate_zero, Nat.mul_zero, Nat.add_zero]

/-- After padding the buffer. -/
structure F2 (s₀ s : State) : Prop extends FC s₀ s where
  sfr : Frame (offR (stB s₀) [(56, 16)] ++ [scrR (sc s₀)]) s₀.mem s.mem
  r4 : s.gpr .r4 = BitVec.ofNat 32 (kb s₀)
  buf : 0 < kb s₀ → BufHas s.mem (stB s₀) (padded s₀)

theorem pad_ok {s₀ : State} (hp : FPre s₀) {s : State} (h : P1 s₀ s) :
    WP isa (.ite .eq (.block []) padBuf) s (F2 s₀) := by
  refine WP.ite s.z (eval_eq _) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hk : kb s₀ = 0 := by rw [h.z] at hb; simpa using hb
    exact ⟨h.toFC, h.sfr.mono fun _ hr => List.mem_append_right _ hr, h.r4, fun hk' => absurd hk (by omega_using [hk, hk'])⟩
  · refine WP.mono (padBuf_ok hp h) fun s' ⟨k', hb'⟩ => ⟨h.toFC.keepsF hp k' (by decide) (by decide)
      (by decide), ?_, by rw [k'.gpr _ (by decide), h.r4], fun _ => hb'⟩
    exact (h.sfr.mono fun _ hr => List.mem_append_right _ hr).trans
      (k'.frame.mono fun _ hr => List.mem_append_left _ hr)

/-! ## The limbs of `r` and the accumulator -/

/-- A word of the state outside the buffer, after padding it. -/
theorem sfr_word {s₀ : State} (hp : FPre s₀) {m : Mem}
    (hf : Frame (offR (stB s₀) [(56, 16)] ++ [scrR (sc s₀)]) s₀.mem m) {d : Nat}
    (hd : d + 4 ≤ 56 ∨ 72 ≤ d ∧ d + 4 ≤ 128) :
    m.readW (stB s₀ + BitVec.ofNat 64 d) 32 = s₀.mem.readW (stB s₀ + BitVec.ofNat 64 d) 32 :=
  hf.readW (Region.contains_self _ _) (fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · simp only [offR, List.map_cons, List.map_nil, List.mem_singleton] at hr; subst hr
      exact disjoint_sub _ (by omega_using [hd]) (by omega_using [hd]) (by decide)
    · simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_scr' (by omega_using [hd])) (by decide)

/-- After computing the limbs of `r` and loading the accumulator. -/
structure F3 (umaal : Bool) (s₀ s : State) : Prop extends FC s₀ s where
  acc : Acc umaal (s₀.gpr .r0) (Rl s₀) (A0 s₀) [] s
  buf : 0 < kb s₀ → BufHas s.mem (stB s₀) (padded s₀)
  z : s.z = decide (kb s₀ = 0)

theorem BufHas.frame {s₀ : State} {m m' : Mem} (h : BufHas m (stB s₀) (padded s₀)) {l : List (Nat × Nat)}
    (hf : Frame (offR (stB s₀) l) m m') (hl : (l.all fun p => 72 ≤ p.1 ∨ p.1 + p.2 ≤ 56) = true)
    (hl' : (l.all fun p => p.1 + p.2 < 2 ^ 32) = true) : BufHas m' (stB s₀) (padded s₀) := fun k hk => by
  rw [← h k hk]
  refine hf _ fun r hr hc => ?_
  exact (dj_offR _ (d := 56) (n := 16) (by
    rw [List.all_eq_true] at hl ⊢
    intro p hp; have := hl p hp; simp only [decide_eq_true_eq] at this ⊢; omega_using [this]) (by decide) hl' r hr) _
    (by rw [← off_add]; exact contains_off (by omega_using [hk]) (by omega_using [hk])) hc

theorem mid_ok {s₀ : State} (hp : FPre s₀) {s : State} (h : F2 s₀ s) :
    WP isa (.block (.str .r4 .r0 ptrOff :: setup umaal ++ ([.ldr .r1 .r0 ptrOff, .cmp .r1 (.imm 0)] : List Instr))) s
      (F3 umaal s₀) := by
  have hfit := hp.st_fit
  obtain hk := kb_lt s₀
  obtain hw := hp.stW h.wr
  refine wp_str (a := stB s₀ + BitVec.ofNat 64 124) (by decide)
    (by rw [h.r0]; exact ea hfit (off := 124) (by decide)) (outSt hw (off := 124) (n := 4) (by decide))
    fun s₁ u₁ => ?_
  obtain f₁ : Frame (offR (stB s₀) [(124, 4)]) s.mem s₁.mem := by
    rw [u₁.mem]
    exact Frame.writeOff (Frame.refl _ _) (a := 124) (len := 4) (List.mem_singleton_self _) (Nat.le_refl _) (Nat.le_refl _)
      (by decide) _ rfl
  obtain fc₁ : FC s₀ s₁ := h.toFC.keepsF hp (ws := []) ⟨fun r _ => by rw [u₁.gpr], f₁, u₁.rd, u₁.wr, u₁.sp⟩
    (by decide) (by decide) (by decide)
  refine WP.append (setupAcc_ok hfit fc₁.r0 (hp.stW fc₁.wr)) fun s₂ ⟨ha₂, k₂⟩ => ?_
  obtain fc₂ : FC s₀ s₂ := fc₁.keepsF hp k₂ (by decide) (by decide) (by decide)
  refine wp_ldr (a := stB s₀ + BitVec.ofNat 64 124) (by decide)
    (by rw [fc₂.r0]; exact ea hfit (off := 124) (by decide)) (inSt (hp.stW fc₂.wr) (off := 124) (n := 4) (by decide))
    fun s₃ u₃ => wp_cmp (op2_imm (by decide)) fun s₄ u₄ hz => WP.block_nil ?_
  obtain m₄ : s₄.mem = s₂.mem := by rw [u₄.mem, u₃.mem]
  obtain hw₁ : ∀ d, (d + 4 ≤ 56 ∨ 72 ≤ d ∧ d + 4 ≤ 124) →
      s₁.mem.readW (stB s₀ + BitVec.ofNat 64 d) 32 = s₀.mem.readW (stB s₀ + BitVec.ofNat 64 d) 32 := fun d hd => by
    rw [f₁.word (by simp only [List.all_cons, List.all_nil, Bool.and_true, decide_eq_true_eq]; omega_using [hd]) (by omega_using [hd])
      (by decide)]
    exact sfr_word hp h.sfr (by omega_using [hd])
  obtain hRl : rlimb s₁.mem (stB s₀) = Rl s₀ := rlimb_frame fun i hi => hw₁ _ (by omega_using [hi])
  obtain hA : accD s₁.mem (stB s₀) = accD s₀.mem (stB s₀) := accD_of_words fun i hi => hw₁ _ (by omega_using [hi])
  rw [hRl, hA] at ha₂
  obtain k₂₄ : KeepsF [.r1] (offR (stB s₀) []) s₂ s₄ :=
    ((u₃.keeps (ws := [.r1]) (by simp)).trans ⟨fun r _ => by rw [u₄.gpr], u₄.mem, u₄.rd, u₄.wr, u₄.sp⟩).keepsF _
  refine ⟨(fc₂.upd u₃ (by decide)).flags u₄,
    (Acc.mk fc₂.r0 (hp.stW fc₂.wr) (by rw [Poly1305.absorbAll_nil]; exact ha₂)).keep k₂₄ (by decide) (by decide)
      (by decide), fun hpos => ?_, ?_⟩
  · rw [m₄]
    exact ((h.buf hpos).frame f₁ (by decide) (by decide)).frame k₂.frame (by decide) (by decide)
  · rw [hz, u₃.gpr, k₂.frame.word (by decide) (by decide) (by decide), u₁.mem, Mem.readW_writeW_self32, h.r4,
      sub0, ofNat_beq_zero (by omega_using [hk])]

/-! ## The last block -/

/-- After absorbing the padded buffer, if any. -/
structure F4 (umaal : Bool) (s₀ s : State) : Prop extends FC s₀ s where
  acc : Acc umaal (s₀.gpr .r0) (Rl s₀) (A0 s₀) (Bf s₀) s

theorem last_ok {s₀ : State} (hp : FPre s₀) {s : State} (h : F3 umaal s₀ s) :
    WP isa (.ite .eq (.block []) (.block (.dp .add .r1 .r0 (.imm 56) :: absorbV umaal false))) s (F4 umaal s₀) := by
  have hfit := hp.st_fit
  obtain hk := kb_lt s₀
  refine WP.ite s.z (eval_eq _) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have h0 : kb s₀ = 0 := by rw [h.z] at hb; simpa using hb
    refine ⟨h.toFC, ?_⟩
    have : Bf s₀ = [] := by simp [Bf, h0, bytesAt]
    rw [this]; exact h.acc
  · have hpos : 0 < kb s₀ := by rw [h.z] at hb; simp only [decide_eq_false_iff_not] at hb; omega_using [hk, hb]
    refine wp_add (op2_imm (by decide)) fun s₁ u₁ => ?_
    obtain hr1 : s₁.gpr .r1 = s₀.gpr .r0 + 56 := by rw [u₁.gpr, h.r0]
    obtain ha : ∀ j < 4, State.addr (s₁.gpr .r1 + BitVec.ofNat 32 (4 * j)) =
        stB s₀ + BitVec.ofNat 64 56 + BitVec.ofNat 64 (4 * j) := fun j hj => by
      rw [hr1, BitVec.add_assoc, show (56 : BitVec 32) = BitVec.ofNat 32 56 from rfl, ← BitVec.ofNat_add,
        ea hfit (by omega_using [hj]), off_add]
    obtain hA₁ : Acc umaal (s₀.gpr .r0) (Rl s₀) (A0 s₀) [] s₁ :=
      h.acc.keep ((u₁.keeps (ws := [.r1]) (by simp)).keepsF (offR (stB s₀) [])) (by decide) (by decide)
        (by decide)
    refine WP.mono (absorbI_ok hfit false (R := Rl s₀) (fun i _ => rlimb_lt _ _ i) hA₁.r0 hA₁.wr hA₁.inv
      (fun j hj => by rw [ha j hj, off_add, u₁.rd, u₁.wr]; exact inSt (hp.stW h.wr) (by omega_using [hj])))
      fun s₂ ⟨hi₂, k₂⟩ => ?_
    obtain f₂ : Frame (offR (stB s₀) [(0, 20)]) s₁.mem s₂.mem := by rw [← accR_offR]; exact k₂.frame
    obtain k₂' : KeepsF work (offR (stB s₀) [(0, 20)]) s₁ s₂ := ⟨k₂.gpr, f₂, k₂.rd, k₂.wr, k₂.sp⟩
    obtain fc₂ := (h.toFC.upd u₁ (by decide)).keepsF hp k₂' (by decide) (by decide) (by decide)
    obtain hmsg : msgVal s₁ = leNum (Bf s₀ ++ [0x01]) := by
      rw [← padded_value (m := s₁.mem) (by rw [u₁.mem]; exact h.buf hpos), leNum_bytesAt_16]
      simp only [msgVal, word]
      rw [ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide)]
    obtain hl : (Bf s₀).length = kb s₀ := Poly1305.length_bytesAt _ _ _
    refine ⟨fc₂, fc₂.r0, hp.stW fc₂.wr, hi₂.congr ?_⟩
    rw [hmsg, Poly1305.absorbAll_nil,
      Poly1305.absorbAll_block (b := Bf s₀) (by omega_using [hk, hpos, hl]) (by omega_using [hk, hpos, hl]),
      iteF (show ¬(false = true) by simp), Nat.add_zero, Nat.mod_mod, Nat.mul_comm (val (Rl s₀))]

/-! ## The tag -/

/-- The tag's stores. -/
def tagList : List (Reg × Nat × Bool) := [(.r3, 0, false), (.r5, 4, false), (.r7, 8, false), (.r10, 12, false)]

/-- The sum of `h mod p` and `s`, carried. -/
def sumL (D : Nat → Nat) (w : Nat → Nat) : Nat → Nat := fun k => redL D k + mlimb (w 0) (w 1) (w 2) (w 3) k

theorem cnt_mod (s₀ : State) : (Proof.Poly1305.countArm s₀).toNat % 16 = kb s₀ := by
  simp only [kb, Proof.Poly1305.countArm]
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (s₀.gpr .r2).isLt, Nat.shiftLeft_eq]
  omega_using []

/-- The key's second half, `s`, in the state at `B`, as a number. -/
abbrev sKey (m : Mem) (B : Addr) : Nat :=
  (m.readW (B + BitVec.ofNat 64 40) 32).toNat + 2 ^ 32 * (m.readW (B + BitVec.ofNat 64 44) 32).toNat +
    2 ^ 64 * (m.readW (B + BitVec.ofNat 64 48) 32).toNat + 2 ^ 96 * (m.readW (B + BitVec.ofNat 64 52) 32).toNat

section
variable {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32)
include hfit

/-- The baseline's tag: the columns reduced fully, `s` added, and the sum
carried, as words. -/
theorem tagB_ok {D : Nat → Nat} {s : State} (hs0 : s.gpr .r0 = st) (hw : stR st ∈ s.wr)
    (hDb : ∀ k < 10, D k ≤ 3564723200) (hcD : ColsD D (State.addr st) s) :
    WP isa (.block (reduce ++ ([.str .r1 .r0 d9Off, .dp .add .r1 .r0 (.imm 40)] : List Instr) ++ addWords ++
      addTop false ++ mask :: (List.range 9).flatMap carryStep ++ toWords)) s fun s' => ∃ t0 t1 t2 t3,
      ((s'.gpr .r3).toNat = t0 ∧ (s'.gpr .r5).toNat = t1 ∧ (s'.gpr .r7).toNat = t2 ∧ (s'.gpr .r10).toNat = t3) ∧
      t0 + 2 ^ 32 * t1 + 2 ^ 64 * t2 + 2 ^ 96 * t3 = (val D % P + sKey s.mem (State.addr st)) % 2 ^ 128 ∧
      KeepsF work (offR (State.addr st) [(16, 4)]) s s' := by
  obtain hE : ∀ j < 10, D j < 2 ^ 32 - 2 ^ 19 := fun j hj => by have := hDb j hj; omega_using [this]
  obtain ⟨-, -, -, hvL, hlL⟩ := red_facts D hE
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine WP.append (reduce_ok hfit hDb hs0 hw hcD) fun s₁ ⟨hc₁, k₁⟩ => ?_
  obtain hs₁0 : s₁.gpr .r0 = st := by rw [k₁.gpr _ (by decide), hs0]
  obtain hw₁ : stR st ∈ s₁.wr := by rw [k₁.wr]; exact hw
  refine wp_str (a := State.addr st + BitVec.ofNat 64 16) (by decide) (by rw [hs₁0]; exact ea hfit (off := 16) (by decide))
    (outSt hw₁ (off := 16) (n := 4) (by decide)) fun s₂ u₂ => ?_
  refine wp_add (op2_imm (by decide)) fun s₃ u₃ => ?_
  obtain hr1 : s₃.gpr .r1 = st + 40 := by rw [u₃.gpr, u₂.gpr, hs₁0]
  obtain hw₃ : stR st ∈ s₃.wr := by rw [u₃.wr, u₂.wr]; exact hw₁
  obtain hsA : ∀ i < 4, State.addr (s₃.gpr .r1 + BitVec.ofNat 32 (4 * i)) =
      State.addr st + BitVec.ofNat 64 (40 + 4 * i) := fun i hi => by
    rw [hr1, BitVec.add_assoc, show (40 : BitVec 32) = BitVec.ofNat 32 40 from rfl, ← BitVec.ofNat_add]
    exact ea hfit (by omega_using [hi])
  refine WP.append (addWords_ok fun i hi => by rw [hsA i hi]; exact inSt hw₃ (by omega_using [hi])) fun s₄ ⟨hc₄, hr₄, k₄⟩ => ?_
  -- The words of `s`.
  let w : Nat → Nat := fun i => (s.mem.readW (State.addr st + BitVec.ofNat 64 (40 + 4 * i)) 32).toNat
  obtain m₃ : s₃.mem = s.mem.writeW (State.addr st + BitVec.ofNat 64 16) (s₁.gpr .r1) := by
    rw [u₃.mem, u₂.mem, k₁.mem]
  obtain hword : ∀ i < 4, (word s₃ i).toNat = w i := fun i hi => by
    simp only [word, w]
    rw [hsA i hi, m₃, readW_writeW_off _ _ _ (by omega_using [hi]) (by decide) (by omega_using [hi])]
  obtain hw4 : ∀ i, w i < 2 ^ 32 := fun i => BitVec.isLt _
  obtain hml := fun k => mlimb_lt (hw4 0) (hw4 1) (hw4 2) (hw4 3) k
  -- `addTop false`: the top column.
  simp only [addTop, Bool.false_eq_true, ite_false, List.append_nil, List.cons_append, List.nil_append]
  obtain hs₄0 : s₄.gpr .r0 = st := by rw [k₄.gpr _ (by decide), u₃.other _ (by decide), u₂.gpr, hs₁0]
  obtain hw₄ : stR st ∈ s₄.wr := by rw [k₄.wr]; exact hw₃
  refine wp_ldr (a := State.addr st + BitVec.ofNat 64 16) (by decide) (by rw [hs₄0]; exact ea hfit (off := 16) (by decide))
    (inSt hw₄ (off := 16) (n := 4) (by decide)) fun s₅ u₅ => wp_add (op2_lsr (by decide)) fun s₆ u₆ => ?_
  refine wp_movw fun s₇ u₇ => ?_
  obtain hL9 := hlL 9 (by decide)
  obtain hcols : Cols (sumL D w) s₇ := fun j hj => by
    rcases Nat.lt_or_ge j 9 with hj9 | hj9
    · have hne := yr_ne j hj9
      obtain e₁ := hc₁ j hj
      have := hlL j hj; have := hml j
      rw [u₇.other _ hne.2.2.1, u₆.other _ hne.2.1, u₅.other _ hne.2.1, hc₄ j hj9,
        u₃.other _ hne.2.1, u₂.gpr, toNat_add_lt (by rw [e₁, wsum_toNat _ hj9, hword 0 (by decide),
          hword 1 (by decide), hword 2 (by decide), hword 3 (by decide)]; omega_arith), e₁, wsum_toNat _ hj9,
        hword 0 (by decide), hword 1 (by decide), hword 2 (by decide), hword 3 (by decide)]
      rfl
    · have e9 : (s₅.gpr .r1).toNat = redL D 9 := by
        rw [u₅.gpr, k₄.mem, m₃, Mem.readW_writeW_self32]; exact hc₁ 9 (by decide)
      obtain e2 : (s₅.gpr .r2).toNat = w 3 := by
        rw [u₅.other _ (by decide), hr₄, hword 3 (by decide)]
      have := hml 9
      rw [show j = 9 by omega_using [hj, hj9], yr9, u₇.other _ (by decide), u₆.gpr, toNat_add_lt (by rw [e9, toNat_shr, e2]; omega_using [hL9, e9, e2]),
        e9, toNat_shr, e2]
      rfl
  obtain hfb : ∀ j < 10, sumL D w j < 2 ^ 32 - 2 ^ 19 := fun j hj => by
    have := hlL j hj; have := hml j; simp only [sumL]; omega_arith
  refine WP.append (carries_ok 0 9 (by decide) hfb hcols u₇.gpr) fun s₈ ⟨hc₈, k₈⟩ => ?_
  obtain hL : ∀ j < 9, carryN (sumL D w) 0 9 j < 2 ^ 13 := fun j hj => carryN_lt _ 0 9 j (by omega_using [hj]) (by omega_using [hj])
  refine WP.mono (toWords_ok hc₈ hL) fun s₉ ⟨e3, e5, e7, e10, _, k₉⟩ => ?_
  obtain m₉ : s₉.mem = s₃.mem := by
    rw [k₉.mem, k₈.mem, u₇.mem, u₆.mem, u₅.mem, k₄.mem]
  refine ⟨_, _, _, _, ⟨e3, e5, e7, e10⟩, ?_, ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩⟩
  · obtain hv : val (carryN (sumL D w) 0 9) = tw0 (carryN (sumL D w) 0 9) + 2 ^ 32 * tw1 (carryN (sumL D w) 0 9) +
        2 ^ 64 * tw2 (carryN (sumL D w) 0 9) + 2 ^ 96 * tw3 (carryN (sumL D w) 0 9) +
        2 ^ 128 * (carryN (sumL D w) 0 9 9 / 2 ^ 11) := by
      rw [val_toWords hL]; rfl
    obtain hvs : val (carryN (sumL D w) 0 9) = val (redL D) + (w 0 + 2 ^ 32 * w 1 + 2 ^ 64 * w 2 + 2 ^ 96 * w 3) := by
      rw [val_carryN _ 0 9 (by decide), ← val_mlimb (hw4 0) (hw4 1) (hw4 2) (hw4 3)]
      unfold sumL; rw [val_add]
    rw [hvL] at hvs
    obtain b0 := (s₉.gpr .r3).isLt; have b1 := (s₉.gpr .r5).isLt; have b2 := (s₉.gpr .r7).isLt
    obtain b3 := (s₉.gpr .r10).isLt
    rw [e3] at b0; rw [e5] at b1; rw [e7] at b2; rw [e10] at b3
    show _ = (val D % P + (w 0 + 2 ^ 32 * w 1 + 2 ^ 64 * w 2 + 2 ^ 96 * w 3)) % 2 ^ 128
    omega_using [hv, hvs, b0, b1, b2, b3]
  · have hr' : r ∉ [Reg.r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12] := hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hr'
    rw [k₉.gpr _ (by simp [h1, h3, h5, h7, h10]), k₈.gpr _ (by simp [cregs, yregs, h1, h3, h4, h5, h6, h7, h8, h9,
      h10, h11]), u₇.other _ h2, u₆.other _ h1, u₅.other _ h1, k₄.gpr _ (by simp [yregs, h2, h12, h3, h4, h5, h6,
      h7, h8, h9, h10, h11]), u₃.other _ h1, u₂.gpr, k₁.gpr _ (by simp [cregs, yregs, h1, h2, h12, h3, h4, h5, h6,
      h7, h8, h9, h10, h11])]
  · rw [m₉, m₃]
    exact Frame.writeOff (Frame.refl _ _) (a := 16) (len := 4) (List.mem_singleton_self _) (Nat.le_refl _)
      (Nat.le_refl _) (by decide) _ rfl
  · rw [k₉.rd, k₈.rd, u₇.rd, u₆.rd, u₅.rd, k₄.rd, u₃.rd, u₂.rd, k₁.rd]
  · rw [k₉.wr, k₈.wr, u₇.wr, u₆.wr, u₅.wr, k₄.wr, u₃.wr, u₂.wr, k₁.wr]
  · rw [k₉.sp, k₈.sp, u₇.sp, u₆.sp, u₅.sp, k₄.sp, u₃.sp, u₂.sp, k₁.sp]

/-- The tag's words, for either arithmetic: the accumulator reduced fully
plus `s`, modulo `2¹²⁸`. -/
theorem tagI_ok {R : Nat → Nat} {v : Nat} {s : State} (hs0 : s.gpr .r0 = st) (hw : stR st ∈ s.wr)
    (h : AccI umaal (State.addr st) R v s) :
    WP isa (.block (tagV umaal)) s fun s' => ∃ t0 t1 t2 t3,
      ((s'.gpr .r3).toNat = t0 ∧ (s'.gpr .r5).toNat = t1 ∧ (s'.gpr .r7).toNat = t2 ∧ (s'.gpr .r10).toNat = t3) ∧
      t0 + 2 ^ 32 * t1 + 2 ^ 64 * t2 + 2 ^ 96 * t3 = (v % P + sKey s.mem (State.addr st)) % 2 ^ 128 ∧
      KeepsF work (offR (State.addr st) [(16, 4)]) s s' := by
  cases umaal
  · obtain ⟨-, D, hcD, hDb, hDv⟩ := h
    rw [show tagV false = reduce ++ ([.str .r1 .r0 d9Off, .dp .add .r1 .r0 (.imm 40)] : List Instr) ++ addWords ++
      addTop false ++ mask :: (List.range 9).flatMap carryStep ++ toWords from rfl, ← hDv]
    exact tagB_ok hfit hs0 hw hDb hcD
  · rw [show tagV true = reduceU ++ addKey from rfl]
    exact WP.mono (tagU_wacc hfit hs0 hw h) fun s' ⟨t0, t1, t2, t3, hT, ht, k⟩ =>
      ⟨t0, t1, t2, t3, hT, ht, k.keepsF _⟩

end

theorem tag_ok {s₀ : State} (hp : FPre s₀) {s : State} (h : F4 umaal s₀ s) :
    WP isa (.block (tagV umaal ++
      ([.ldrSp .r2 0, .str .r3 .r2 0, .str .r5 .r2 4, .str .r7 .r2 8, .str .r10 .r2 12, .ldrSp .r12 4] : List Instr) ++
      restoreScr)) s fun s' => abiPreserved s₀ s' ∧ Proof.Poly1305.finalizeArm.post s₀ s' := by
  have hfit := hp.st_fit
  rw [List.append_assoc]
  refine WP.append (tagI_ok hfit h.acc.r0 h.acc.wr h.acc.inv) fun s₉ ⟨t0, t1, t2, t3, ⟨e3, e5, e7, e10⟩, hT, k₉⟩ => ?_
  simp only [List.cons_append, List.nil_append]
  obtain fc₉ : FC s₀ s₉ := h.toFC.keepsF hp k₉ (by decide) (by decide) (by decide)
  -- The stores into `out`.
  obtain F₃ : Frame (offR (stB s₀) wkL ++ [oR s₀, scrR (sc s₀)]) s₀.mem s₉.mem :=
    fc₉.frame.mono fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact List.mem_append_left _ hr
      · simp only [List.mem_singleton] at hr; subst hr
        exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  refine wp_arg hp (i := 0) fc₉.sp fc₉.rd (by decide) (hp.arg F₃ (by decide)) fun t₁ v₁ => ?_
  obtain hoW : oR s₀ ∈ t₁.wr := hp.oW (by rw [v₁.wr, fc₉.wr])
  refine WP.append (stores_ok .r2 hp.o_fit rfl tagList t₁ v₁.gpr hoW (by decide) (by decide))
    fun t₂ ⟨hs₂, hf₂, hg₂, hrd₂, hwr₂, hsp₂⟩ => ?_
  obtain hfo : Frame [oR s₀] t₁.mem t₂.mem := hf₂.sub fun r hr => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    obtain hb : ∀ x ∈ tagList, x.2.1 + ssize x.2.2 ≤ 16 := by decide
    exact ⟨_, List.mem_singleton_self _, sub_base _ (hb x hx) (by decide)⟩
  obtain F₂ : Frame (offR (stB s₀) wkL ++ [oR s₀, scrR (sc s₀)]) s₀.mem t₂.mem := by
    refine F₃.trans ?_
    rw [← v₁.mem]
    exact hfo.mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact List.mem_append_right _ List.mem_cons_self
  refine wp_arg hp (i := 1) (by rw [hsp₂, v₁.sp, fc₉.sp]) (by rw [hrd₂, v₁.rd, fc₉.rd]) (by decide) (hp.arg F₂ (by decide))
    fun t₃ v₃ => ?_
  obtain hsv : SavedS (State.addr (sc s₀)) s₀.gpr t₃.mem := by
    intro i hi
    rw [v₃.mem, hfo.readW (Region.contains_self _ _) (by
      simp only [List.mem_singleton, forall_eq]
      exact hp.o_scr.symm.sub_left (sub_base _ (by omega_using [hi]) (by decide))) (by decide), v₁.mem]
    exact fc₉.saved i hi
  refine WP.mono (restoreScr_ok (g := s₀.gpr) hp.sc_fit v₃.gpr (hp.scW (by rw [v₃.wr, hwr₂, v₁.wr, fc₉.wr])) hsv)
    fun s' ⟨hr', k'⟩ => ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · rcases preserved_cases r hr with rfl | ⟨i, hi, rfl⟩
    · rw [k'.gpr _ (by decide), v₃.other _ (by decide), hg₂, v₁.other _ (by decide), fc₉.lr]
    · exact hr' i hi
  · rw [k'.sp, v₃.sp, hsp₂, v₁.sp, fc₉.sp]
  · intro key msg hbuf hcnt
    obtain ⟨msg, b, rfl, hrep, hbl, hbb⟩ := Proof.Poly1305.Buffered.split hbuf
    obtain hkb : (msg ++ b).length % 16 = kb s₀ := by
      rw [← cnt_mod, hcnt, BitVec.toNat_ofNat]; omega_using [hbl]
    obtain hb : b = Bf s₀ := by rw [← hbb, hkb]
    subst hb
    obtain ⟨hlen, hkey, hacc⟩ := hrep
    -- The tag's words.
    obtain wd : ∀ x ∈ tagList, ∀ d, x.2.1 = d → x.2.2 = false →
        (s'.mem.readW (oA s₀ + BitVec.ofNat 64 d) 32).toNat = (s₉.gpr x.1).toNat := by
      intro x hx d hd hb
      have := hs₂ x hx
      obtain ⟨r, o, b⟩ := x
      simp only at hd hb; subst hd hb
      obtain hr2 : r ≠ .r2 := by
        have : ∀ x ∈ tagList, x.1 ≠ .r2 := by decide
        exact this _ hx
      rw [k'.mem, v₃.mem]; simp only [Stored] at this; rw [this, v₁.other _ hr2]
    obtain e0 := wd _ (by decide : (Reg.r3, 0, false) ∈ tagList) 0 rfl rfl
    obtain e4 := wd _ (by decide : (Reg.r5, 4, false) ∈ tagList) 4 rfl rfl
    obtain e8 := wd _ (by decide : (Reg.r7, 8, false) ∈ tagList) 8 rfl rfl
    obtain e12 := wd _ (by decide : (Reg.r10, 12, false) ∈ tagList) 12 rfl rfl
    simp only at e0 e4 e8 e12
    rw [e3] at e0; rw [e5] at e4; rw [e7] at e8; rw [e10] at e12
    -- The key.
    rw [← hkey, take_bytesAt _ _ (by decide), ← val_rlimb] at hacc
    obtain hlt : leNum (bytesAt s₀.mem (stB s₀) 24) < P := by rw [hacc]; exact Poly1305.accumulate_lt _ _
    obtain hA : accumulate (Rn s₀) msg = A0 s₀ := by rw [A0, val_accD_eq hlt]; exact hacc.symm
    obtain hlt' := Poly1305.absorbAll_lt (r := Rn s₀) (a := A0 s₀) (by rw [← hA]; exact Poly1305.accumulate_lt _ _)
      (Bf s₀)
    obtain hkw : ∀ d, 24 ≤ d → d + 4 ≤ 56 →
        s.mem.readW (stB s₀ + BitVec.ofNat 64 d) 32 = s₀.mem.readW (stB s₀ + BitVec.ofNat 64 d) 32 := fun d h1 h2 =>
      h.frame.readW (Region.contains_self _ _) (fun r hr => by
        rcases List.mem_append.mp hr with hr | hr
        · exact (dj_offR _ (d := 24) (n := 32) (by decide) (by decide) (by decide) r hr).sub_left
            (sub_sub _ h1 (by omega_using [h2]) (by decide))
        · simp only [List.mem_singleton] at hr; subst hr
          exact hp.st_scr' (by omega_using [h2])) (by decide)
    obtain hS : leNum (((bytesAt s₀.mem (stB s₀ + 24) 32).drop 16).take 16) = sKey s.mem (stB s₀) := by
      rw [(drop_bytesAt s₀.mem (stB s₀ + 24) 16 16 : (bytesAt s₀.mem (stB s₀ + 24) 32).drop 16 = _),
        take_bytesAt _ _ (Nat.le_refl _), leNum_bytesAt_16, show (24 : Addr) = BitVec.ofNat 64 24 from rfl, off_add, off_add,
        off_add, off_add, off_add]
      simp only [sKey]
      rw [hkw 40 (by decide) (by decide), hkw 44 (by decide) (by decide), hkw 48 (by decide) (by decide),
        hkw 52 (by decide) (by decide)]
    simp only [Spec.Poly1305.mac]
    rw [← hkey, take_bytesAt _ _ (by decide), ← val_rlimb, Poly1305.accumulate_append hlen, hA, hS,
      Poly1305.bytesAt_leBytes, ← Poly1305.leNum_bytesAt_read, leNum_bytesAt_16]
    rw [e0, e4, e8, e12, hT, Nat.mod_eq_of_lt hlt', show (2 : Nat) ^ 128 = 256 ^ 16 from rfl, Poly1305.leBytes_mod]

/-! ## The whole function -/

theorem finalize_correct {s₀ : State} (hp : FPre s₀) :
    WP isa (finalize umaal) s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Poly1305.finalizeArm.post s₀ s' := by
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (pad_ok hp h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (mid_ok hp h₂) fun s₃ h₃ => ?_)
  exact WP.seq (WP.mono (last_ok hp h₃) fun s₄ h₄ => tag_ok hp h₄)

/-! ## Constant time -/

/-- The initial taint: `r0` (`state`) and `r2:r3` (`count`) are public, `r0`
points at the state, and the 8 bytes of stack arguments are public, the
second one pointing at `scratch`. The analysis tracks the public slots of
the state (the buffer's length). -/
def τf : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r2, .r3], flags := false, lens := [128, 16, 128], bases := [(.r0, 0)], argLen := 8,
    argBases := [(4, 2)] }

theorem argByte_eq {s : State} (hsp : s.sp.toNat + 8 ≤ 2 ^ 32) {k : Nat} (hk : k < 8) :
    VG.Arm.Taint.argByte s k = stackArgAddr s (k / 4) + BitVec.ofNat 64 (k % 4) := by
  simp only [VG.Arm.Taint.argByte, stackArgAddr]
  rw [addr_add (by omega_using [hsp, hk]), BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 2; omega_using []

theorem wff {s : State} (h : Proof.Poly1305.finalizeArm.pre s) : VG.Arm.Taint.Wf τf s := by
  obtain hp := FPre.of s h
  obtain hst := hp.st_fit; have ho := hp.o_fit; have hsc := hp.sc_fit; have hs := hp.sp_fit
  refine ⟨fun _ => ⟨by simp [hp.wr, τf], ?_, ?_⟩, ?_, fun _ => ⟨hs, ?_⟩, ?_⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨⟨hp.st_o, hp.st_scr⟩, hp.o_scr, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> simp only [addr_toNat] <;> omega_using [hst, ho, hsc]
  · intro p hp'; simp only [τf, List.mem_singleton] at hp'; subst hp'; simp [VG.Arm.Taint.region, hp.wr]
  · have e : (⟨State.addr s.sp, 8⟩ : Region) = argR s := by simp [stackArgAddr]
    simp only [τf, e, hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.a_st
    · exact hp.a_o
    · exact hp.a_scr
  · intro p hp'; simp only [τf, List.mem_singleton] at hp'; subst hp'
    refine ⟨by decide, ?_⟩
    simp only [VG.Arm.Taint.region, hp.wr]
    rfl

theorem agreef {s₁ s₂ : State} (h₁ : Proof.Poly1305.finalizeArm.pre s₁) (h₂ : Proof.Poly1305.finalizeArm.pre s₂)
    (hpub : Proof.Poly1305.finalizeArm.pub s₁ s₂) : VG.Arm.Taint.Agree τf s₁ s₂ := by
  obtain ⟨psp, p0, p2, p3, a0, a1⟩ := hpub
  obtain hp₁ := FPre.of s₁ h₁; have hp₂ := FPre.of s₂ h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wff h₁, wff h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => psp, fun k hk => ?_⟩
  · simp only [τf, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> with_reducible assumption
  · rw [hp₁.wr, hp₂.wr]; simp only [stR, oR, oA, oP, scrR, sc, p0, a0, a1]
  · simp only [τf] at hk
    rw [argByte_eq hp₁.sp_fit hk, argByte_eq hp₂.sp_fit hk, Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)),
      Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    have : k / 4 = 0 ∨ k / 4 = 1 := by omega_using [hk]
    rcases this with h | h <;> rw [h]
    · exact congrArg _ a0
    · exact congrArg _ a1

/-- A state satisfying the precondition: `out` at `0x2000` and `scratch` at
`0x3000`, passed on the stack at `0x5000`. -/
def finalizeSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | _ => 0
  sp := 0x5000
  n := false
  z := false
  c := false
  v := false
  mem a := bif Nat.beq a.toNat 0x5001 then 0x20 else bif Nat.beq a.toNat 0x5005 then 0x30 else 0
  rd := [⟨0x5000, 8⟩]
  wr := [⟨0x1000, 128⟩, ⟨0x2000, 16⟩, ⟨0x3000, 128⟩]

theorem finalize_ok (s : State) (hs : Proof.Poly1305.finalizeArm.pre s) :
    ∃ t s', Exec isa (finalize umaal) s t s' ∧ abiPreserved s s' ∧ Proof.Poly1305.finalizeArm.post s s' :=
  finalize_correct (FPre.of s hs)

theorem finalize_ct : ConstantTime isa Proof.Poly1305.finalizeArm.pre Proof.Poly1305.finalizeArm.pub
    (finalize umaal) := by
  cases umaal
  · exact VG.Taint.constantTime (A := taint) τf (fun _ _ h₁ h₂ hp => agreef h₁ h₂ hp) (by
      taint_decide)
  · exact VG.Taint.constantTime (A := taintU) τf (fun _ _ h₁ h₂ hp => agreef h₁ h₂ hp) (by
      taint_decide)

theorem finalize_verified :
    Verified Arm.target (Impl.Poly1305.Arm.finalize umaal) (Proof.Poly1305.finalizeScratchContract Arm.abi) :=
  Verified.of_correct finalize_ok finalize_ct (by
    sig_implies [Proof.Poly1305.finalizeScratchContract, Proof.Poly1305.finalizeScratchSig, Spec.Poly1305.finalizePost,
      Proof.Poly1305.finalizeArm, Proof.Poly1305.countArm, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val, Arm.State.addr] [Proof.Poly1305.Arm.Fin.finalizeSat, Arm.stackArg,
      Arm.stackArgAddr, Mem.readW, Mem.read] using Proof.Poly1305.Arm.Fin.finalizeSat)

end VG.Proof.Poly1305.Arm.Fin
