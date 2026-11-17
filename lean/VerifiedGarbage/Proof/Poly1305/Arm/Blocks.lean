module

public import VerifiedGarbage.Proof.Poly1305.Arm.Bytes
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Spec.Poly1305.Contract
public import VerifiedGarbage.Proof.Poly1305.Contract
meta import VerifiedGarbage.Proof.Poly1305.Contract
public import VerifiedGarbage.Proof.Poly1305.Spec
import VerifiedGarbage.Proof.Poly1305.Arm.Lit
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Poly1305.Arm.Bytes
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Spec.Poly1305.Contract
meta import VerifiedGarbage.Proof.Poly1305.Spec
meta import VerifiedGarbage.Proof.Poly1305.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

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
