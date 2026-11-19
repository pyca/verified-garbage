module

public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.FillCall
public import VerifiedGarbage.Proof.Argon2.FillStep
import VerifiedGarbage.Proof.Argon2.FillPositions
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.ReadHalves
import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Initial
public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Scratch
public import VerifiedGarbage.Proof.Argon2.Contract
public import VerifiedGarbage.Proof.Argon2.AddressInput
public import VerifiedGarbage.Proof.Argon2.Matrix
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Argon2.RISCV64.Ops
import VerifiedGarbage.Proof.Argon2.Dimensions
import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.HCall
public import VerifiedGarbage.Proof.Argon2.MemoryInit
import VerifiedGarbage.Proof.Blake2.Stream
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Argon2.RISCV64.Derive.FillDep`, which this module and modules that import it used -/

section

/-! ### `Argon2.RISCV64.Derive.MemoryInit`, which this module and modules that import it used -/

section

/-!
# Argon2 on RISC-V: the memory's initialization

`memoryInit_ok`: after `memoryInit`, the memory matrix represents
`initMemory` (`Proof.Argon2.Represents`). The matrix is cleared
(`clear_ok`), then each lane's first two blocks are H′ of the 72 bytes of
H′'s input in the frame (`initBlock_ok`), H₀ followed by the column and the
lane, written there just before the call. `LI s₀ h0 l` is the state after
`l` lanes (`initCell`).
-/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.Derive

open VG VG.RISCV64
open VG.Proof.Argon2.RISCV64 (wp_sll wp_srl wp_srlw wp_mul wp_mulhu wp_or wp_and wp_lwu wp_sw)
open VG.RISCV64.Wp (Upd Mupd wp_add wp_sub wp_addi wp_subi wp_li wp_mv wp_sd)
open VG.Spec.Blake2 (bytesAt)
open VG.Spec.Argon2 (Block zeroBlock parseBlock)
open VG.Proof.Argon2 (matrixCell Represents initialBytes)
open VG.Impl.Argon2.RISCV64.Derive (ld st lda ldw)

/-! ## Blocks in memory -/

/-- A block outside a frame's regions is kept. -/
theorem blockAt_keep {rs : List Region} {m m' : Mem} (f : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 1024⟩ r) : blockAt m' p = blockAt m p := by
  unfold blockAt
  exact congrArg Vector.ofFn (funext fun j => f.read (r := ⟨p, 1024⟩)
    (Offset.contains_base p (by have := j.isLt; omega_arith) (by have := j.isLt; omega_arith)) hd (by decide))

theorem read_zero {m : Mem} {a : Addr} {n : Nat} (h : ∀ i < n, m (a + BitVec.ofNat 64 i) = 0) :
    m.read a n = 0 := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    obtain h0 : m a = 0 := by simpa using h 0 (by omega_arith)
    obtain h1 : m.read (a + 1) n = 0 := ih fun i hi => by
      rw [BitVec.add_assoc, show (1 : Addr) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat]
      exact h (1 + i) (by omega_arith)
    simp only [Mem.read, h0, h1]
    exact BitVec.zero_append_zero

/-- A block of zero bytes. -/
theorem blockAt_zero {m : Mem} {p : Addr} (h : ∀ i < 1024, m (p + BitVec.ofNat 64 i) = 0) :
    blockAt m p = zeroBlock := by
  unfold blockAt zeroBlock
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_ofFn, Vector.getElem_replicate]
  exact read_zero fun i hi => by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]; exact h _ (by omega_arith)

/-! ## The initialized cells -/

/-- Cell `k` after the first two blocks of the first `l` lanes are initialized. -/
def initCell (p : Spec.Argon2.Params) (h0 : List Byte) (l k : Nat) : Block :=
  if k / p.laneLen < l ∧ k % p.laneLen < 2 then
    parseBlock (initialBytes h0 (k / p.laneLen) (k % p.laneLen))
  else zeroBlock

theorem initCell_zero (p : Spec.Argon2.Params) (h0 : List Byte) (k : Nat) :
    initCell p h0 0 k = zeroBlock := by
  unfold initCell
  exact ite_eq_right fun h => Nat.not_lt_zero _ h.1

theorem cell_div {L l c : Nat} (hc : c < L) : (l * L + c) / L = l := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega_arith), Nat.div_eq_of_lt hc, Nat.zero_add]

theorem cell_mod {L l c : Nat} (hc : c < L) : (l * L + c) % L = c := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]

theorem initCell_new (p : Spec.Argon2.Params) (h0 : List Byte) {l c : Nat} (hL : 2 ≤ p.laneLen)
    (hc : c < 2) :
    initCell p h0 (l + 1) (l * p.laneLen + c) = parseBlock (initialBytes h0 l c) := by
  unfold initCell
  rw [cell_div (by omega_arith), cell_mod (by omega_arith)]
  exact ite_eq_left ⟨by omega_arith, hc⟩

theorem initCell_old (p : Spec.Argon2.Params) (h0 : List Byte) {l k : Nat}
    (h₀ : k ≠ l * p.laneLen) (h₁ : k ≠ l * p.laneLen + 1) :
    initCell p h0 (l + 1) k = initCell p h0 l k := by
  unfold initCell
  obtain hdm := Nat.div_add_mod k p.laneLen
  by_cases hq : k / p.laneLen = l
  · rw [hq, Nat.mul_comm] at hdm
    rw [ite_eq_right (by omega_arith), ite_eq_right (by omega_arith)]
  · by_cases hc : k / p.laneLen < l ∧ k % p.laneLen < 2
    · rw [ite_eq_left (by omega_arith), ite_eq_left hc]
    · rw [ite_eq_right (by omega_arith), ite_eq_right hc]

/-- `a - b` is zero exactly when `a = b`, for numbers below 2⁶⁴. -/
theorem ofNat_sub_beq {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b != 0) = !decide (a = b) := by
  by_cases h : a = b
  · subst h; simp
  · have hne : BitVec.ofNat 64 a - BitVec.ofNat 64 b ≠ 0 := by
      intro e
      obtain e' := congrArg BitVec.toNat e
      have z : (0 : BitVec 64).toNat = 0 := rfl
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, z] at e'
      omega_arith
    rw [bne_iff_ne.mpr hne]; simp [h]

/-! ## Clearing the matrix -/

/-- The loop's state after `j` doublewords. -/
structure CI (s₀ s₁ : State) (j : Nat) (s : State) : Prop where
  inv : Inv s₀ s
  a2 : s.gpr .a2 = memP s₀ + BitVec.ofNat 64 (8 * j)
  a3 : s.gpr .a3 = BitVec.ofNat 64 (blocksN s₀ * 128 - j)
  a4 : s.gpr .a4 = 0
  zero : ∀ i < 8 * j, s.mem (memP s₀ + BitVec.ofNat 64 i) = 0
  frame : Frame [memR s₀] s₁.mem s.mem

/-- A byte after a zero doubleword is stored at `a`. -/
theorem writeW_zero (m : Mem) (a x : Addr) :
    (m.writeW a (0 : BitVec 64)) x = if (x - a).toNat < 8 then 0 else m x := by
  simp only [Mem.writeW, Mem.write]
  split <;> simp

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem blocks_pos : 1 ≤ blocksN s₀ := by
  rw [hp.blocks_eq, hp.laneLen_eq]
  have := Nat.mul_le_mul hp.lanes_pos (show 1 ≤ 4 * (prm s₀).segmentLen by have := hp.segLen_two; omega_arith)
  omega_arith

theorem blocks_lt : blocksN s₀ < 2 ^ 32 := Nat.lt_of_le_of_lt hp.blocks_le (mcost_lt s₀)

theorem clearLoop_ok {s₁ : State} (h : CI s₀ s₁ 0 s₁) :
    WP isa (.loop (.block Impl.Argon2.RISCV64.Derive.clearWord) (.nonzero .a3)) s₁
      (CI s₀ s₁ (blocksN s₀ * 128)) := by
  have hm := hp.mem_fits
  obtain hb := blocks_lt hp
  obtain b1 := blocks_pos hp
  refine WP.loop (M := isa)
    (fun n s => ∃ j, n = blocksN s₀ * 128 - j ∧ j < blocksN s₀ * 128 ∧ CI s₀ s₁ j s)
    ?_ (blocksN s₀ * 128) s₁ ⟨0, by omega_arith, by omega_arith, h⟩
  rintro n s ⟨j, rfl, hj, c⟩
  obtain hc : (memR s₀).Contains (memP s₀ + BitVec.ofNat 64 (8 * j)) 8 :=
    Offset.contains_base _ (by omega_arith) (by omega_arith)
  simp only [Impl.Argon2.RISCV64.Derive.clearWord]
  refine wp_sd (a := memP s₀ + BitVec.ofNat 64 (8 * j)) (by decide) (by rw [c.a2]; simp)
    (al_add (by decide) (.inr hp.mem_al) (by omega_arith))
    (by rw [c.inv.wr]; exact ⟨_, mem_mem hp, hc⟩) fun t₁ u₁ => ?_
  obtain i₁ := c.inv.mupd u₁ ((Frame.refl _ _).writeW (r := memR s₀) (by simp) _ hc)
  refine wp_addi (by decide) fun t₂ u₂ => wp_subi (by decide) fun t u => WP.block_nil ?_
  obtain i₃ := (i₁.upd u₂).upd u
  obtain e₁ : t.gpr .a3 = BitVec.ofNat 64 (blocksN s₀ * 128 - (j + 1)) := by
    rw [u.gpr, u₂.other _ (by decide), u₁.gpr, c.a3,
      Offset.ofNat_sub_ofNat (by omega_arith : 1 ≤ blocksN s₀ * 128 - j)]
    congr 1
  obtain next : CI s₀ s₁ (j + 1) t := by
    refine ⟨i₃, ?_, e₁, ?_, fun i hi => ?_, ?_⟩
    · rw [u.other _ (by decide), u₂.gpr, u₁.gpr, c.a2, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
        Nat.mul_succ]
    · rw [u.other _ (by decide), u₂.other _ (by decide), u₁.gpr, c.a4]
    · rw [u.mem, u₂.mem, u₁.mem, c.a4, writeW_zero]
      by_cases hi' : i < 8 * j
      · split
        · rfl
        · exact c.zero i hi'
      · rw [show memP s₀ + BitVec.ofNat 64 i = memP s₀ + BitVec.ofNat 64 (8 * j) +
            BitVec.ofNat 64 (i - 8 * j) by
          rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_sub_cancel' (by omega_arith)],
          Offset.add_sub_cancel_left]
        split
        · rfl
        · rename_i hn; rw [BitVec.toNat_ofNat] at hn; omega_arith
    · rw [u.mem, u₂.mem, u₁.mem]
      exact c.frame.writeW (List.mem_singleton_self _) _ hc
  obtain z : VG.RISCV64.eval (.nonzero .a3) t = some (!decide (blocksN s₀ * 128 - (j + 1) = 0)) := by
    rw [VG.RISCV64.Wp.eval_nonzero, e₁, ← VG.RISCV64.Steps.ofNat_beq_zero (by omega_arith)]
    rfl
  by_cases done : j + 1 = blocksN s₀ * 128
  · exact .inl ⟨by rw [z]; simp; omega_arith, done ▸ next⟩
  · exact .inr ⟨by rw [z]; simp; omega_arith, blocksN s₀ * 128 - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, next⟩

theorem clear_ok {s : State} (h : Inv s₀ s) :
    WP isa Impl.Argon2.RISCV64.Derive.clear s fun t => Inv s₀ t ∧ Frame [memR s₀] s.mem t.mem ∧
      ∀ i < blocksN s₀ * 1024, t.mem (memP s₀ + BitVec.ofNat 64 i) = 0 := by
  obtain hb := blocks_lt hp
  unfold Impl.Argon2.RISCV64.Derive.clear Impl.Argon2.RISCV64.Derive.clearSetup
  refine WP.seq (wp_lda hp h (i := 13) (by decide) fun s₁ u₁ =>
    wp_lda hp (h.upd u₁) (i := 14) (by decide) fun s₂ u₂ => ?_)
  obtain i₂ := (h.upd u₁).upd u₂
  refine wp_sll (by decide) fun s₃ u₃ => wp_li (by decide) fun s₄ u₄ => WP.block_nil ?_
  obtain i₄ := (i₂.upd u₃).upd u₄
  refine (clearLoop_ok hp ⟨i₄, ?_, ?_, u₄.gpr, fun i hi => absurd hi (by omega_arith), Frame.refl _ _⟩).mono
    fun t c => ⟨c.inv, ?_, fun i hi => c.zero i (by omega_arith)⟩
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
    simp
  · rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr]
    apply BitVec.eq_of_toNat_eq
    rw [shl_nat (by show (arg s₀ 14).toNat * 2 ^ 7 < _; have : (arg s₀ 14).toNat < 2 ^ 32 := hb; omega_arith),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have : (arg s₀ 14).toNat < 2 ^ 32 := hb; omega_arith)]
    show blocksN s₀ * 2 ^ 7 = _
    omega_arith
  · rw [show s.mem = s₄.mem by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]]
    exact c.frame

end

theorem setWidth_ofNat (n : Nat) : (BitVec.ofNat 64 n).setWidth 32 = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_mod_of_dvd _ (by decide)]

/-- The 72 bytes of H′'s input: H₀, then two words. -/
theorem bytes72 (m : Mem) (p : Addr) :
    bytesAt m p 72 = bytesAt m p 64 ++ Spec.Blake2.wordBytes (m.readW (p + BitVec.ofNat 64 64) 32) ++
      Spec.Blake2.wordBytes (m.readW (p + BitVec.ofNat 64 68) 32) := by
  rw [show (72 : Nat) = 64 + (4 + (4 + 0)) from rfl, Proof.Blake2.bytesAt_add, bytes_word, bytes_word,
    BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  simp [bytesAt]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

omit hp in
/-- `sw r, d(s3)`, to LE32(column) or LE32(lane) in H′'s input. -/
theorem wp_stlocw {s : State} (h : Inv s₀ s) {d : Nat} (hd : 64 ≤ d ∧ d + 4 ≤ 72 ∧ d % 4 = 0) {r : Reg}
    {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → t.mem = s.mem.writeW (E s₀ + BitVec.ofNat 64 d) ((s.gpr r).setWidth 32) →
      t.gpr = s.gpr → WP isa (.block is) t Q) :
    WP isa (.block (.store .w r .s3 d :: is)) s Q := by
  obtain hc : (inR s₀).Contains (E s₀ + BitVec.ofNat 64 d) 4 :=
    Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)
  refine wp_sw (a := E s₀ + BitVec.ofNat 64 d) (by omega_arith) (by rw [h.s3])
    (h.loc_al (by decide) hd.2.2) (loc_in h (by omega_arith)) fun t u =>
      k t (h.mupd u ((Frame.refl _ _).writeW (r := inR s₀) (by simp) _ hc)) u.mem u.gpr

omit hp in
/-- The writes of `initBlock` before its call: two words of H′'s input. -/
theorem frame_words {m : Mem} (v w : BitVec 32) :
    Frame [⟨E s₀ + BitVec.ofNat 64 64, 8⟩] m
      ((m.writeW (E s₀ + BitVec.ofNat 64 64) v).writeW (E s₀ + BitVec.ofNat 64 68) w) :=
  ((Frame.refl _ m).writeW (w := 32) (List.mem_singleton_self _) v
    (Offset.contains _ (by decide) (by decide) (by decide))).writeW (w := 32)
    (List.mem_singleton_self _) w (Offset.contains _ (by decide) (by decide) (by decide))

omit hp in
/-- A doubleword of the frame outside `initBlock`'s two words is kept by them. -/
theorem readW_words {m : Mem} (v w : BitVec 32) {d : Nat} (h : d + 8 ≤ 64 ∨ 72 ≤ d)
    (hd : d + 8 ≤ 320) :
    ((m.writeW (E s₀ + BitVec.ofNat 64 64) v).writeW (E s₀ + BitVec.ofNat 64 68) w).readW
      (E s₀ + BitVec.ofNat 64 d) 64 = m.readW (E s₀ + BitVec.ofNat 64 d) 64 := by
  refine (frame_words v w).readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)

/-- The words of `initBlock` are outside the matrix, the frame's variables,
H₀ and `scratch`. -/
theorem words_disj :
    (∀ R ∈ [memR s₀, scrR s₀, outR s₀], Region.Disjoint ⟨E s₀ + BitVec.ofNat 64 64, 8⟩ R) ∧
    Region.Disjoint ⟨E s₀ + BitVec.ofNat 64 64, 8⟩ ⟨E s₀ + BitVec.ofNat 64 0, 64⟩ := by
  refine ⟨fun R hR => ?_, ?_⟩
  · exact stk_disj hp (by decide) R hR
  · exact Offset.disjoint _ (by decide) (by decide) (by decide)

/-- A cell of the memory matrix is outside `scratch`. -/
theorem cell_disj {k : Nat} (hk : k < blocksN s₀) :
    ∀ r ∈ [scrR s₀], Region.Disjoint ⟨matrixCell (memP s₀) k, 1024⟩ r := by
  obtain sub : Region.Sub ⟨matrixCell (memP s₀) k, 1024⟩ (memR s₀) := Proof.Argon2.matrixCell_sub _ _ _ hk
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  exact hp.mem_scr.sub_left sub

/-- Cells other than `k` are outside its region. -/
theorem cell_other {j k : Nat} (hj : j < blocksN s₀) (hk : k < blocksN s₀) (ne : j ≠ k) :
    Region.Disjoint ⟨matrixCell (memP s₀) j, 1024⟩ ⟨matrixCell (memP s₀) k, 1024⟩ :=
  Proof.Argon2.matrixCell_disjoint _ _ _ _ (by have := blocks_lt hp; omega_arith) hj hk ne

/-- H₀ in the frame is outside a call's writes. -/
theorem h0_call {O : Region} (hO : Region.Sub O (memR s₀) ∨ Region.Sub O (outR s₀)) :
    ∀ r ∈ [O, scrR s₀], Region.Disjoint ⟨E s₀ + BitVec.ofNat 64 0, 64⟩ r := by
  obtain sub : Region.Sub ⟨E s₀ + BitVec.ofNat 64 0, 64⟩ (inR s₀) := Offset.sub _ (by decide) (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rcases hO with h | h
    · exact ((in_disj hp (R := memR s₀) (by simp)).sub_left sub).sub_right h
    · exact ((in_disj hp (R := outR s₀) (by simp)).sub_left sub).sub_right h
  · exact (in_disj hp (R := scrR s₀) (by simp)).sub_left sub

omit hp in
/-- The frame's variables are outside a call's writes. -/
theorem lw_call {O : Region} (hO : Region.Sub O (memR s₀) ∨ Region.Sub O (outR s₀)) :
    ∀ r ∈ [O, scrR s₀], ∃ r' ∈ [memR s₀, scrR s₀, outR s₀], Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rcases hO with h | h
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

/-- Block `c < 2` of lane `l`: H′ of H₀, `c` and `l`. -/
theorem initBlock_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) {h0 : List Byte}
    (b0 : bytesAt s.mem (E s₀ + BitVec.ofNat 64 0) 64 = h0) {l c : Nat} (hl : l < lanesN s₀)
    (hc : c < 2) (r28 : s.gpr .s1 = BitVec.ofNat 64 l)
    (r29 : s.gpr .s2 = memP s₀ + BitVec.ofNat 64 ((l * (prm s₀).laneLen + c) * 1024)) :
    WP isa (Impl.Argon2.RISCV64.Derive.initBlock c) s fun t => Inv s₀ t ∧ Prm s₀ t ∧
      bytesAt t.mem (E s₀ + BitVec.ofNat 64 0) 64 = h0 ∧ t.gpr .s1 = s.gpr .s1 ∧
      t.gpr .s2 = s.gpr .s2 ∧
      blockAt t.mem (matrixCell (memP s₀) (l * (prm s₀).laneLen + c)) =
        parseBlock (initialBytes h0 l c) ∧
      ∀ k < blocksN s₀, k ≠ l * (prm s₀).laneLen + c →
        blockAt t.mem (matrixCell (memP s₀) k) = blockAt s.mem (matrixCell (memP s₀) k) := by
  have hm := hp.mem_fits
  have hlt := hp.lanes_lt
  obtain L2 : 2 ≤ (prm s₀).laneLen := by rw [hp.laneLen_eq]; have := hp.segLen_two; omega_arith
  obtain hcell : l * (prm s₀).laneLen + c < blocksN s₀ := by
    rw [hp.blocks_eq]
    have := Nat.mul_le_mul_right (prm s₀).laneLen (show l + 1 ≤ lanesN s₀ by omega_arith)
    rw [Nat.succ_mul] at this
    omega_arith
  obtain sO : Region.Sub ⟨matrixCell (memP s₀) (l * (prm s₀).laneLen + c), 1024⟩ (memR s₀) :=
    Proof.Argon2.matrixCell_sub _ _ _ hcell
  unfold Impl.Argon2.RISCV64.Derive.initBlock
  refine WP.seq (wp_li (by omega_arith) fun s₁ u₁ => ?_)
  obtain i₁ := h.upd u₁
  refine wp_stlocw i₁ (d := 64) (by decide) fun s₂ i₂ m₂ g₂ => ?_
  refine wp_stlocw i₂ (d := 68) (by decide) fun s₃ i₃ m₃ g₃ => ?_
  refine wp_addi (by decide) fun s₄ u₄ => wp_li (by decide) fun s₅ u₅ =>
    wp_mv fun s₆ u₆ => wp_li (by decide) fun s₇ u₇ => wp_mv fun s₈ u₈ => WP.block_nil ?_
  obtain i₈ := ((((i₃.upd u₄).upd u₅).upd u₆).upd u₇).upd u₈
  obtain m₈ : s₈.mem = s₃.mem := by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  obtain g₈ : ∀ r, r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → r ≠ .a3 → r ≠ .a4 → s₈.gpr r = s.gpr r :=
    fun r a b d e f => by
      rw [u₈.other _ f, u₇.other _ e, u₆.other _ d, u₅.other _ b, u₄.other _ a, g₃, g₂, u₁.other _ a]
  obtain r3₈ : s₈.gpr .a0 = E s₀ + BitVec.ofNat 64 0 := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.gpr, g₃, g₂, i₁.s3]; rfl
  obtain r4₈ : (s₈.gpr .a1).toNat = 72 := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr]; rfl
  obtain r6₈ : (s₈.gpr .a3).toNat = 1024 := by rw [u₈.other _ (by decide), u₇.gpr]; rfl
  obtain r5₈ : s₈.gpr .a2 = matrixCell (memP s₀) (l * (prm s₀).laneLen + c) := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide),
      u₄.other _ (by decide), g₃, g₂, u₁.other _ (by decide), r29]; rfl
  obtain r7₈ : s₈.gpr .a4 = scrP s₀ := by
    rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), g₃, g₂, i₁.s4]
  obtain hcell' : (l * (prm s₀).laneLen + c) * 1024 + 1024 ≤ blocksN s₀ * 1024 := by omega_arith
  refine hcall_ok hp i₈ r7₈
    ⟨inR s₀, by simp, 0, by rw [r3₈]; simp, by rw [r4₈]⟩
    ⟨memR s₀, by simp, (l * (prm s₀).laneLen + c) * 1024, by rw [r5₈]; rfl, by rw [r6₈]; exact hcell'⟩
    (by rw [r4₈]; decide) (by rw [r6₈]; decide)
    fun t it cs fr post => ⟨it, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have sO' : Region.Sub ⟨s₈.gpr .a2, (s₈.gpr .a3).toNat⟩ (memR s₀) := by rw [r5₈, r6₈]; exact sO
    exact Prm.of_lw pr fun d h₁ h₂ => by
      rw [lw_keep hp fr (lw_call (.inl sO')) (by omega_arith), lw_mem m₈]
      show s₃.mem.readW _ 64 = _
      rw [m₃, m₂, readW_words _ _ (.inr (by omega_arith)) (by omega_arith), u₁.mem]
  · rw [bytes_keep fr (h0_call hp (.inl (by rw [r5₈, r6₈]; exact sO))) (by decide), m₈, m₃, m₂,
      bytes_keep (frame_words _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (words_disj hp).2.symm) (by decide),
      u₁.mem, b0]
  · rw [cs .s1 (by decide), g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  · rw [cs .s2 (by decide), g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  · refine Proof.Argon2.blockAt_of_initialBytes _ _ _ _ _ ?_
    rw [← r5₈, show (1024 : Nat) = (s₈.gpr .a3).toNat from r6₈.symm, post, r6₈, r3₈, r4₈, bytes72, m₈]
    obtain w96 : s₃.mem.readW (E s₀ + BitVec.ofNat 64 0 + BitVec.ofNat 64 64) 32 =
        BitVec.ofNat 32 c := by
      rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, m₃, Mem.readW_writeW_sep
        (Offset.sep _ (by decide) (by decide) (by decide)) (by decide), m₂, Mem.readW_writeW_self32,
        u₁.gpr, setWidth_ofNat]
    obtain w100 : s₃.mem.readW (E s₀ + BitVec.ofNat 64 0 + BitVec.ofNat 64 68) 32 =
        BitVec.ofNat 32 l := by
      rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, m₃, Mem.readW_writeW_self32, g₂,
        u₁.other _ (by decide), r28, setWidth_ofNat]
    rw [w96, w100, m₃, m₂, bytes_keep (frame_words _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (words_disj hp).2.symm) (by decide),
      u₁.mem, b0]
    rfl
  · intro k hk ne
    obtain sk := Proof.Argon2.matrixCell_sub (memP s₀) _ _ hk
    rw [blockAt_keep fr (fun r hr => ?_), m₈, m₃, m₂, blockAt_keep (frame_words _ _) (fun r hr => ?_),
      u₁.mem]
    · simp only [List.mem_singleton] at hr; subst hr
      exact ((words_disj hp).1 (memR s₀) (by simp)).symm.sub_left sk
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [r5₈, r6₈]; exact cell_other hp hk hcell ne
      · exact cell_disj hp hk _ (by simp)

end

theorem r29_next (x : Addr) (a b : Nat) :
    x + BitVec.ofNat 64 a + BitVec.ofNat 64 1024 + BitVec.ofNat 64 b - BitVec.ofNat 64 1024 =
      x + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc (x + _) (BitVec.ofNat 64 1024), BitVec.add_comm (BitVec.ofNat 64 1024),
    ← BitVec.add_assoc, BitVec.add_sub_cancel, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- The state after the first two blocks of `l` lanes. -/
structure LI (s₀ : State) (h0 : List Byte) (l : Nat) (s : State) : Prop where
  inv : Inv s₀ s
  pr : Prm s₀ s
  b0 : bytesAt s.mem (E s₀ + BitVec.ofNat 64 0) 64 = h0
  s1 : s.gpr .s1 = BitVec.ofNat 64 l
  s2 : s.gpr .s2 = memP s₀ + BitVec.ofNat 64 (l * (prm s₀).laneLen * 1024)
  cells : ∀ k < blocksN s₀, blockAt s.mem (matrixCell (memP s₀) k) = initCell (prm s₀) h0 l k

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem lane_ok {h0 : List Byte} {l : Nat} {s : State} (hl : l < lanesN s₀) (h : LI s₀ h0 l s) :
    WP isa Impl.Argon2.RISCV64.Derive.initLane s fun t =>
      LI s₀ h0 (l + 1) t ∧ VG.RISCV64.eval (.nonzero .a0) t = some (!decide (l + 1 = lanesN s₀)) := by
  obtain L2 : 2 ≤ (prm s₀).laneLen := by rw [hp.laneLen_eq]; have := hp.segLen_two; omega_arith
  have hlt := hp.lanes_lt
  obtain hll : (prm s₀).laneLen ≤ mcostN s₀ :=
    Nat.le_trans (Nat.le_trans (Nat.le_mul_of_pos_left _ hp.lanes_pos) (Nat.le_of_eq hp.blocks_eq.symm))
      hp.blocks_le
  obtain hm := mcost_lt s₀
  unfold Impl.Argon2.RISCV64.Derive.initLane
  refine WP.seq ((initBlock_ok hp h.inv h.pr h.b0 hl (c := 0) (by decide) h.s1
    (by rw [h.s2, Nat.add_zero])).mono fun s₁ ⟨i₁, p₁, b₁, e₁, d₁, w₁, o₁⟩ => ?_)
  refine WP.seq (wp_addi (by decide) fun s₂ u₂ => WP.block_nil ?_)
  obtain i₂ := i₁.upd u₂
  refine WP.seq ((initBlock_ok hp i₂ (p₁.of_mem u₂.mem) (h0 := h0) (by rw [u₂.mem]; exact b₁) hl (c := 1)
    (by decide) (by rw [u₂.other _ (by decide), e₁, h.s1])
    (by rw [u₂.gpr, d₁, h.s2, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_mul])).mono
    fun s₃ ⟨i₃, p₃, b₃, e₃, d₃, w₃, o₃⟩ => ?_)
  simp only [Impl.Argon2.RISCV64.Derive.nextLane]
  refine wp_ldloc i₃ (d := Impl.Argon2.RISCV64.Derive.strideOff) (by decide) fun s₄ u₄ =>
    wp_add fun s₅ u₅ => wp_subi (by decide) fun s₆ u₆ => wp_addi (by decide) fun s₇ u₇ => ?_
  obtain i₇ := (((i₃.upd u₄).upd u₅).upd u₆).upd u₇
  refine wp_ldw hp i₇ (i := 7) (by decide) fun s₈ u₈ => wp_sub fun t u => WP.block_nil ?_
  obtain i₈ := (i₇.upd u₈).upd u
  obtain mt : t.mem = s₃.mem := by rw [u.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  obtain r28t : t.gpr .s1 = BitVec.ofNat 64 (l + 1) := by
    rw [u.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), e₃, u₂.other _ (by decide), e₁, h.s1,
      BitVec.ofNat_add]
  refine ⟨⟨i₈, p₃.of_mem mt, by rw [mt, b₃], r28t, ?_, fun k hk => ?_⟩, ?_⟩
  · rw [u.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.gpr,
      u₄.gpr, u₄.other _ (by decide), d₃, u₂.gpr, d₁, h.s2, p₃.stride, r29_next,
      show l * (prm s₀).laneLen * 1024 + (prm s₀).laneLen * 1024 = (l + 1) * (prm s₀).laneLen * 1024 by
        rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]]
  · rw [mt]
    by_cases k1 : k = l * (prm s₀).laneLen + 1
    · rw [k1, w₃]; exact (initCell_new _ _ L2 (by decide)).symm
    rw [o₃ k hk k1]
    by_cases k0 : k = l * (prm s₀).laneLen
    · rw [u₂.mem, k0, show l * (prm s₀).laneLen = l * (prm s₀).laneLen + 0 from rfl, w₁]
      exact (initCell_new _ _ L2 (by decide)).symm
    rw [u₂.mem, o₁ k hk (by omega_arith), h.cells k hk, initCell_old _ _ k0 k1]
  · have r28₈ : s₈.gpr .s1 = BitVec.ofNat 64 (l + 1) := by
      rw [← r28t, u.other _ (by decide)]
    obtain lanes : (arg32 s₀ 7).setWidth 64 = BitVec.ofNat 64 (lanesN s₀) := ofNat_toNat (toNat_ext32 _)
    rw [VG.RISCV64.Wp.eval_nonzero, u.gpr, r28₈, u₈.gpr, lanes, ofNat_sub_beq (by omega_arith) (by omega_arith)]

end

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `clear`, from the body with H₀ in the frame. -/
theorem clearW_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) {h0 : List Byte}
    (b0 : bytesAt s.mem (E s₀ + BitVec.ofNat 64 0) 64 = h0) :
    WP isa Impl.Argon2.RISCV64.Derive.clear s fun t => Inv s₀ t ∧ Prm s₀ t ∧
      bytesAt t.mem (E s₀ + BitVec.ofNat 64 0) 64 = h0 ∧ ∀ i < blocksN s₀ * 1024,
        t.mem (memP s₀ + BitVec.ofNat 64 i) = 0 := by
  refine (clear_ok hp h).mono fun s₁ ⟨i₁, f₁, z₁⟩ => ⟨i₁, ?_, ?_, z₁⟩
  · have fsub : ∀ r ∈ [memR s₀], ∃ r' ∈ [memR s₀, scrR s₀, outR s₀], Region.Sub r r' :=
      fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; simp, fun _ h => h⟩
    exact Prm.of_lw pr fun d h₁ h₂ => lw_keep hp f₁ fsub (by omega_arith)
  · rw [bytes_keep f₁ (fun r hr => ?_) (by omega_arith), b0]
    simp only [List.mem_singleton] at hr; subst hr
    obtain sub : Region.Sub ⟨E s₀ + BitVec.ofNat 64 0, 64⟩ (inR s₀) := Offset.sub _ (by decide) (by decide)
    exact (in_disj hp (R := memR s₀) (by simp)).sub_left sub

/-- The first lane's first block, after `clear`. -/
theorem laneStart_ok {s : State} {h0 : List Byte} (h : Inv s₀ s ∧ Prm s₀ s ∧
      bytesAt s.mem (E s₀ + BitVec.ofNat 64 0) 64 = h0 ∧ ∀ i < blocksN s₀ * 1024,
        s.mem (memP s₀ + BitVec.ofNat 64 i) = 0) :
    WP isa (.block [lda .s2 Impl.Argon2.RISCV64.Derive.memoryArg, .li .s1 0]) s (LI s₀ h0 0) := by
  obtain ⟨i₁, p₁, b₁, z₁⟩ := h
  refine wp_lda hp i₁ (i := 13) (by decide) fun s₂ u₂ => wp_li (by decide) fun s₃ u₃ =>
    WP.block_nil ?_
  obtain i₃ := (i₁.upd u₂).upd u₃
  obtain m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem]
  refine ⟨i₃, p₁.of_mem m₃, by rw [m₃]; exact b₁, u₃.gpr, ?_, fun k hk => ?_⟩
  · rw [u₃.other _ (by decide), u₂.gpr]; simp
  · rw [initCell_zero, m₃]
    refine blockAt_zero fun i hi => ?_
    rw [matrixCell, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact z₁ _ (by omega_arith)

theorem memoryInit_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) {h0 : List Byte}
    (b0 : bytesAt s.mem (E s₀ + BitVec.ofNat 64 0) 64 = h0) :
    WP isa Impl.Argon2.RISCV64.Derive.memoryInit s fun t => Inv s₀ t ∧ Prm s₀ t ∧
      Represents t.mem (memP s₀) (prm s₀).blocks (Spec.Argon2.initMemory (prm s₀) h0).memory := by
  have hlt := hp.lanes_lt
  have hl1 := hp.lanes_pos
  unfold Impl.Argon2.RISCV64.Derive.memoryInit
  refine WP.seq ((clearW_ok hp h pr b0).mono fun s₁ h₁ =>
    WP.seq ((laneStart_ok hp h₁).mono fun s₃ start => ?_))
  refine WP.loop (M := isa) (fun n t => ∃ l, n = lanesN s₀ - l ∧ l < lanesN s₀ ∧ LI s₀ h0 l t) ?_
    (lanesN s₀) s₃ ⟨0, by omega_arith, by omega_arith, start⟩
  rintro n t ⟨l, rfl, hl, ht⟩
  refine (lane_ok hp hl ht).mono fun u ⟨hu, cu⟩ => ?_
  by_cases done : l + 1 = lanesN s₀
  · refine .inl ⟨cu.trans (by simp [done]), hu.inv, hu.pr, ?_⟩
    refine ⟨Proof.Argon2.initMemory_size _ _, fun k hk => ?_⟩
    obtain hk' : k < blocksN s₀ := by rw [hp.blocks]; exact hk
    rw [hu.cells k hk', Array.getElem?_eq_getElem (by rw [Proof.Argon2.initMemory_size]; exact hk),
      Option.getD_some, Proof.Argon2.initMemory_cell _ _ _ hk, initCell, done]
    have : k / (prm s₀).laneLen < lanesN s₀ := by
      rw [hp.blocks_eq] at hk'
      exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hk')
    by_cases c2 : k % (prm s₀).laneLen < 2
    · rw [ite_eq_left ⟨this, c2⟩, ite_eq_left c2]
    · rw [ite_eq_right (fun h => c2 h.2), ite_eq_right c2]
  · refine .inr ⟨cu.trans (by rw [decide_eq_false done]; rfl), lanesN s₀ - (l + 1), by omega_arith,
      l + 1, rfl, by omega_arith, hu⟩

end

end VG.Proof.Argon2.RISCV64.Derive

end

end

/-! ### `Argon2.RISCV64.Derive.FillState`, which this module and modules that import it used -/

section

/-! ### `Argon2.RISCV64.Derive.FillSteps`, which this module and modules that import it used -/

section

/-!
# Argon2 on RISC-V: the steps of the filling loops

The address computations the filling loops share: `column_ok` (the current
column), `blockAddr_ok` (a block's address from its lane and column) and
`prevPointer_ok` (the previous block's). Register-only steps are described
by `Only` (the registers they may write), which keeps the body's invariant
when the invariant names none of them (`Inv.only`).
-/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.Derive

open VG VG.RISCV64
open VG.Proof.Argon2.RISCV64 (wp_sll wp_srl wp_srlw wp_mul wp_mulhu wp_or wp_and wp_lwu wp_sw)
open VG.RISCV64.Wp (Upd Mupd wp_add wp_sub wp_subi)
open VG.Impl.Argon2.RISCV64.Derive (sliceOff segLenOff indexOff laneOff laneLenOff passOff ld)

theorem Inv.only {s₀ s t : State} (h : Inv s₀ s) {ds : List Reg} (o : Only ds s t)
    (hd : ∀ r ∈ ds, Free r := by decide) : Inv s₀ t :=
  h.step o.sp (o.gpr _ fun m => (hd _ m).1 rfl) (o.gpr _ fun m => (hd _ m).2.1 rfl)
    (o.gpr _ fun m => (hd _ m).2.2.1 rfl) (fun r hr => o.gpr _ fun m => (hd _ m).2.2.2 hr) o.rd o.wr (by rw [o.mem]; exact Frame.refl _ _)

theorem Divide.KeepD.only {s t : State} (k : Divide.KeepD s t) : Only [.a1, .a3, .a4, .a5, .a6] s t :=
  ⟨fun r hr => k.other r (fun h => hr (by simp [h])) (fun h => hr (by simp [h]))
    (fun h => hr (by simp [h])) (fun h => hr (by simp [h])) (fun h => hr (by simp [h])),
    k.mem, k.rd, k.wr, k.sp⟩

theorem ofNat_mul_ofNat {a b : Nat} : BitVec.ofNat 64 a * BitVec.ofNat 64 b = BitVec.ofNat 64 (a * b) :=
  (BitVec.ofNat_mul ..).symm

/-- `ofNat x << n`, without overflow. -/
theorem ofNat_shl' {x n : Nat} (h : x * 2 ^ n < 2 ^ 64) :
    BitVec.ofNat 64 x <<< n = BitVec.ofNat 64 (x * 2 ^ n) := by
  have hx : x < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right x (Nat.two_pow_pos n)) h
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hx]

/-! ## Addresses -/

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem laneLen_ge : 8 ≤ (prm s₀).laneLen := by rw [hp.laneLen_eq]; have := hp.segLen_two; omega_using [this]

theorem laneLen_le : (prm s₀).laneLen ≤ blocksN s₀ := by
  rw [hp.blocks_eq]; exact Nat.le_mul_of_pos_left _ hp.lanes_pos

theorem blocks_lt' : blocksN s₀ < 2 ^ 32 := Nat.lt_of_le_of_lt hp.blocks_le (mcost_lt s₀)

/-- A cell of the matrix, and its bytes, fit in the matrix. -/
theorem cell_fits {lane col : Nat} (hl : lane < lanesN s₀) (hc : col < (prm s₀).laneLen) :
    lane * (prm s₀).laneLen + col < blocksN s₀ ∧
      (lane * (prm s₀).laneLen + col) * 1024 + 1024 ≤ blocksN s₀ * 1024 := by
  have : lane * (prm s₀).laneLen + col < blocksN s₀ := by
    have e := hp.blocks_eq
    have := Nat.mul_le_mul_right (prm s₀).laneLen (show lane + 1 ≤ lanesN s₀ by omega_using [hl])
    rw [Nat.succ_mul] at this
    omega_using [hc, e, this]
  have h2 : (lane * (prm s₀).laneLen + col + 1) * 1024 ≤ blocksN s₀ * 1024 :=
    Nat.mul_le_mul_right 1024 this
  rw [Nat.succ_mul] at h2
  exact ⟨this, h2⟩

/-- `blockAddr`: `r3 :=` the address of block `col` of lane `lane`. -/
theorem blockAddr_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) {lane col : Nat}
    (hl : lane < lanesN s₀) (hc : col < (prm s₀).laneLen) (ha : s.gpr .a0 = BitVec.ofNat 64 lane)
    (hcx : s.gpr .a1 = BitVec.ofNat 64 col) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, t.gpr .a0 = memP s₀ + BitVec.ofNat 64 ((lane * (prm s₀).laneLen + col) * 1024) →
      Only [.a0, .a2] s t → WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.RISCV64.Derive.blockAddr ++ is)) s Q := by
  obtain ⟨cl, cf⟩ := cell_fits hp hl hc
  have hb := blocks_lt' hp
  unfold Impl.Argon2.RISCV64.Derive.blockAddr
  simp only [List.cons_append, List.nil_append]
  refine wp_ldloc h (d := laneLenOff) (by decide) fun s₁ u₁ => wp_mul fun s₂ u₂ =>
    wp_add fun s₃ u₃ => wp_sll (by decide) fun s₄ u₄ => ?_
  have i₄ := (((h.upd u₁).upd u₂).upd u₃).upd u₄
  have e₄ : s₄.gpr .a0 = BitVec.ofNat 64 ((lane * (prm s₀).laneLen + col) * 1024) := by
    rw [u₄.gpr, u₃.gpr, u₂.gpr, u₂.other .a1 (by decide), u₁.gpr, u₁.other .a0 (by decide),
      u₁.other .a1 (by decide), ha, hcx, pr.laneLen, ofNat_mul_ofNat, BitVec.ofNat_add_ofNat,
      ofNat_shl' (by omega_using [cl, hb])]
  refine wp_lda hp i₄ (i := 13) (by decide) fun s₅ u₅ => wp_add fun s₆ u₆ => k s₆ ?_ ?_
  · rw [u₆.gpr, u₅.gpr, u₅.other _ (by decide), e₄]
  · exact (((((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)).trans
      (Only.of_upd u₄)).trans (Only.of_upd u₅)).trans (Only.of_upd u₆) |>.mono (by simp)

end

/-- The loop position in the frame. -/
structure Pos (s₀ s : State) (pass slice lane index : Nat) : Prop where
  pass : lw s₀ s passOff = BitVec.ofNat 64 pass
  slice : lw s₀ s sliceOff = BitVec.ofNat 64 slice
  lane : lw s₀ s laneOff = BitVec.ofNat 64 lane
  index : lw s₀ s indexOff = BitVec.ofNat 64 index

theorem Pos.of_mem {s₀ s t : State} {pass slice lane index : Nat} (h : Pos s₀ s pass slice lane index)
    (hm : t.mem = s.mem) : Pos s₀ t pass slice lane index :=
  ⟨by rw [lw_mem hm]; exact h.pass, by rw [lw_mem hm]; exact h.slice, by rw [lw_mem hm]; exact h.lane,
    by rw [lw_mem hm]; exact h.index⟩

theorem Pos.of_lw {s₀ s t : State} {pass slice lane index : Nat} (h : Pos s₀ s pass slice lane index)
    (hl : ∀ d, 184 ≤ d → d + 8 ≤ 216 → lw s₀ t d = lw s₀ s d) :
    Pos s₀ t pass slice lane index :=
  ⟨by rw [hl _ (by decide) (by decide)]; exact h.pass, by rw [hl _ (by decide) (by decide)]; exact h.slice,
    by rw [hl _ (by decide) (by decide)]; exact h.lane, by rw [hl _ (by decide) (by decide)]; exact h.index⟩

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem segLen_lt : (prm s₀).segmentLen < 2 ^ 30 := by
  have := laneLen_ge hp
  have := laneLen_le hp
  have := blocks_lt' hp
  have l := hp.laneLen_eq
  omega

omit hp in
/-- `column`: `r4 :=` the current column, `slice · segLen + index`. -/
theorem column_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) {pass slice lane index : Nat}
    (ps : Pos s₀ s pass slice lane index)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ t, t.gpr .a1 = BitVec.ofNat 64 (slice * (prm s₀).segmentLen + index) →
      Only [.a0, .a1, .a2] s t → WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.RISCV64.Derive.column ++ is)) s Q := by
  unfold Impl.Argon2.RISCV64.Derive.column
  simp only [List.cons_append, List.nil_append]
  refine wp_ldloc h (d := sliceOff) (by decide) fun s₁ u₁ => ?_
  have i₁ := h.upd u₁
  refine wp_ldloc i₁ (d := segLenOff) (by decide) fun s₂ u₂ => wp_mul fun s₃ u₃ => ?_
  have i₃ := (i₁.upd u₂).upd u₃
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  refine wp_ldloc i₃ (d := indexOff) (by decide) fun s₄ u₄ => wp_add fun t u => k t ?_ ?_
  · rw [u.gpr, u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, lw_mem u₁.mem,
      ps.slice, pr.segLen, u₄.gpr, lw_mem m₃, ps.index, ofNat_mul_ofNat, BitVec.ofNat_add_ofNat]
  · exact ((((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)).trans
      (Only.of_upd u₄)).trans (Only.of_upd u) |>.mono (by simp)

/-- `prevColumn`: `r4 :=` the column before `a1`, cyclically. -/
theorem prevColumn_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) {col : Nat}
    (hc : col < (prm s₀).laneLen) (hx : s.gpr .a1 = BitVec.ofNat 64 col) :
    WP isa Impl.Argon2.RISCV64.Derive.prevColumn s fun t =>
      t.gpr .a1 = BitVec.ofNat 64 ((col + (prm s₀).laneLen - 1) % (prm s₀).laneLen) ∧
        Only [.a1] s t := by
  have := laneLen_ge hp
  have := laneLen_le hp
  have := blocks_lt' hp
  unfold Impl.Argon2.RISCV64.Derive.prevColumn
  refine WP.seq (WP.ite (decide (col = 0)) ?_ ?_ ?_)
  · rw [show isa.eval _ s = VG.RISCV64.eval _ s from rfl, VG.RISCV64.Wp.eval_zero, hx,
      VG.RISCV64.Steps.ofNat_beq_zero (by omega_arith)]
  · intro hz
    refine wp_ldloc h (d := laneLenOff) (by decide) fun s₂ u₂ => WP.block_nil ?_
    refine wp_subi (by decide) fun t u => WP.block_nil ⟨?_, ?_⟩
    · have c0 : col = 0 := of_decide_eq_true hz
      rw [u.gpr, u₂.gpr, pr.laneLen, c0, sub_ofNat (b := 1) (by omega_using [hc]), Nat.zero_add,
        Nat.mod_eq_of_lt (by omega_using [hc])]
    · exact ((Only.of_upd u₂).trans (Only.of_upd u)).mono (by simp)
  · intro hz
    refine WP.block_nil (wp_subi (by decide) fun t u => WP.block_nil ⟨?_, ?_⟩)
    · have c0 : col ≠ 0 := of_decide_eq_false hz
      rw [u.gpr, hx, sub_ofNat (b := 1) (by omega_using [c0])]
      congr 1
      rw [show col + (prm s₀).laneLen - 1 = col - 1 + (prm s₀).laneLen by omega_using [c0], Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega_using [hc])]
    · exact (Only.of_upd u).mono (by simp)

/-- `prevPointer`: `r3 :=` the address of the previous block. -/
theorem prevPointer_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) {pass slice lane index : Nat}
    (ps : Pos s₀ s pass slice lane index) (hl : lane < lanesN s₀) (hs : slice < 4)
    (hi : index < (prm s₀).segmentLen) :
    WP isa Impl.Argon2.RISCV64.Derive.prevPointer s fun t =>
      t.gpr .a0 = memP s₀ + BitVec.ofNat 64 ((lane * (prm s₀).laneLen +
        (slice * (prm s₀).segmentLen + index + (prm s₀).laneLen - 1) % (prm s₀).laneLen) * 1024) ∧
      Only [.a0, .a1, .a2] s t := by
  have hc := Proof.Argon2.column_lt (prm s₀) hp.lanes_pos hs hi
  have := laneLen_ge hp
  unfold Impl.Argon2.RISCV64.Derive.prevPointer
  refine WP.seq ?_
  rw [← List.append_nil Impl.Argon2.RISCV64.Derive.column]
  refine column_ok h pr ps fun s₁ c₁ k₁ => WP.block_nil ?_
  have i₁ := h.only k₁
  refine WP.seq ((prevColumn_ok hp i₁ (pr.of_mem k₁.mem) hc c₁).mono fun s₂ ⟨c₂, k₂⟩ => ?_)
  have i₂ := i₁.only k₂
  have m₂ : s₂.mem = s.mem := by rw [k₂.mem, k₁.mem]
  refine wp_ldloc i₂ (d := laneOff) (by decide) fun s₃ u₃ => ?_
  have i₃ := i₂.upd u₃
  rw [← List.append_nil Impl.Argon2.RISCV64.Derive.blockAddr]
  refine blockAddr_ok hp i₃ (pr.of_mem (by rw [u₃.mem, m₂])) hl (Nat.mod_lt _ (by omega_using [hc]))
    (by rw [u₃.gpr, lw_mem m₂, ps.lane]) (by rw [u₃.other _ (by decide), c₂])
    fun t a k => WP.block_nil ⟨a, ?_⟩
  exact (((k₁.trans k₂).trans (Only.of_upd u₃)).trans k).mono (by simp)

end

end VG.Proof.Argon2.RISCV64.Derive

end

end

/-!
# Argon2 on RISC-V: the state of the filling loops

`FS s₀ pass slice lane index ctr st`: the body at a position of the filling
loops (`Pos`), the memory matrix representing `st`'s, and the address block
cached in `scratch[2048, 3072)` that of the counter in the frame, if it is
not zero (`CacheOk`). `addressMode_ok`: `addressMode` leaves `a5` nonzero
for data-dependent addressing.
-/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.Derive

open VG VG.RISCV64
open VG.RISCV64.Wp (Upd Mupd wp_add wp_sub wp_addi wp_subi wp_li wp_mv wp_ld wp_sd wp_xor)
open VG.Proof.Argon2.RISCV64 (wp_sll wp_srl wp_srlw wp_mul wp_mulhu wp_or wp_and wp_lwu wp_sw)
open VG.RISCV64.Wp (Upd Mupd wp_li wp_sub)
open VG.Spec.Argon2 (Block zeroBlock FillState addressBlock independent)
open VG.Proof.Argon2 (matrixCell Represents)
open VG.Impl.Argon2.RISCV64.Derive (sliceOff segLenOff indexOff laneOff laneLenOff passOff counterOff)

/-- The address block cached at `scratch + 2048`, for the counter in the frame. -/
def CacheOk (s₀ : State) (pass lane slice ctr : Nat) (s : State) : Prop :=
  ctr < 2 ^ 32 ∧ lw s₀ s counterOff = BitVec.ofNat 64 ctr ∧
    (ctr = 0 ∨ 1 ≤ ctr ∧
      blockAt s.mem (scrP s₀ + BitVec.ofNat 64 2048) = addressBlock (prm s₀) pass lane slice ctr)

/-- The counter after a block: the index's group, for data-independent addressing. -/
def ctrNext (p : Spec.Argon2.Params) (pass slice index ctr : Nat) : Nat :=
  if independent p pass slice then index / 128 + 1 else ctr

/-- The filling loops' state at a position, the memory matrix holding `st`'s. -/
structure FS (s₀ : State) (pass slice lane index ctr : Nat) (st : FillState) (s : State) : Prop where
  inv : Inv s₀ s
  pr : Prm s₀ s
  pos : Pos s₀ s pass slice lane index
  cache : CacheOk s₀ pass lane slice ctr s
  mem : Represents s.mem (memP s₀) (prm s₀).blocks st.memory

theorem Represents.keep {m m' : Mem} {base : Addr} {n : Nat} {b : Array Block}
    (h : Represents m base n b)
    (hk : ∀ k < n, blockAt m' (matrixCell base k) = blockAt m (matrixCell base k)) :
    Represents m' base n b :=
  ⟨h.size, fun k hk' => (hk k hk').trans (h.block k hk')⟩

/-! ## The addressing mode -/

theorem independent_eq {s₀ : State} (hk : (kindV s₀).toNat ≤ 2) (pass slice : Nat) :
    independent (prm s₀) pass slice = (decide ((kindV s₀).toNat = 1) ||
      (decide ((kindV s₀).toNat = 2) && decide (pass = 0) && decide (slice < 2))) := by
  have hv : (prm s₀).variant =
      (if (kindV s₀).toNat = 0 then .d else if (kindV s₀).toNat = 1 then .i else .id) := rfl
  have e1 : (Spec.Argon2.Variant.d == .i) = false := rfl
  have e2 : (Spec.Argon2.Variant.d == .id) = false := rfl
  have e3 : (Spec.Argon2.Variant.i == .i) = true := rfl
  have e3' : (Spec.Argon2.Variant.i == .id) = false := rfl
  have e4 : (Spec.Argon2.Variant.id == .i) = false := rfl
  have e5 : (Spec.Argon2.Variant.id == .id) = true := rfl
  rcases (by omega_using [hk] : (kindV s₀).toNat = 0 ∨ (kindV s₀).toNat = 1 ∨ (kindV s₀).toNat = 2) with
    h | h | h
  · rw [independent, hv, ite_eq_left h, e1, e2, h]; simp
  · rw [independent, hv, ite_eq_right (by omega_using [h]), ite_eq_left h, e3, e3', h]; simp
  · rw [independent, hv, ite_eq_right (by omega_using [h]), ite_eq_right (by omega_using [h]), e4, e5, h]; simp
    cases pass <;> rfl

/-- `((0 - x) | x) >> 63` is whether `x` is not zero. -/
theorem nz (x : BitVec 64) : ((0 - x) ||| x) >>> 63 = if x = 0 then 0 else 1 := by
  by_cases hx : x = 0
  · subst hx; decide
  · simp only [hx, ite_false]
    have hn : x.toNat ≠ 0 := fun h => hx (BitVec.eq_of_toNat_eq h)
    have hm : ∀ y : BitVec 64, y.msb = decide (2 ^ 63 ≤ y.toNat) := fun y => by
      rw [BitVec.msb_eq_decide]
    have hb : 2 ^ 63 ≤ ((0 - x) ||| x).toNat := by
      have : ((0 - x) ||| x).msb = true := by
        rw [BitVec.msb_or, hm, hm, BitVec.toNat_sub, show (0 : BitVec 64).toNat = 0 from rfl]
        have := x.isLt
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        omega_using [hn]
      rw [hm] at this; exact of_decide_eq_true this
    have hl := ((0 - x) ||| x).isLt
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    show _ = 1
    omega_using [hb]

/-- The second test of `addressMode`: Argon2id in the first two slices of the first pass. -/
theorem id_zero {k : Nat} (hk : k ≤ 2) {pass slice : Nat} (hp : pass < 2 ^ 64) (hs : slice < 4) :
    ((BitVec.ofNat 64 k ^^^ BitVec.ofNat 64 2) ||| BitVec.ofNat 64 pass ||| (BitVec.ofNat 64 slice >>> 1) = 0) ↔
      (k = 2 ∧ pass = 0 ∧ slice < 2) := by
  have e : BitVec.ofNat 64 slice >>> 1 = 0 ↔ slice < 2 := by
    constructor
    · intro h
      have := congrArg BitVec.toNat h
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega_using [hs])] at this
      rw [show (0 : BitVec 64).toNat = 0 from rfl] at this
      omega_using [this]
    · intro h
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega_using [hs])]
      rw [show (0 : BitVec 64).toNat = 0 from rfl]
      omega_using [h]
  have f : BitVec.ofNat 64 k ^^^ BitVec.ofNat 64 2 = 0 ↔ k = 2 := by
    rcases (by omega_using [hk] : k = 0 ∨ k = 1 ∨ k = 2) with h | h | h <;> subst h <;> decide
  have pp : BitVec.ofNat 64 pass = 0 ↔ pass = 0 := by
    constructor
    · intro e; have := congrArg BitVec.toNat e
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp] at this; exact this
    · intro e; rw [e]; rfl
  have orz : ∀ x y : BitVec 64, x ||| y = 0 ↔ x = 0 ∧ y = 0 := fun _ _ => BitVec.or_eq_zero_iff
  rw [orz, orz, f, e, pp, and_assoc]

theorem mode_bits (a b : Prop) [Decidable a] [Decidable b] :
    (((if a then (0 : BitVec 64) else 1) &&& (if b then 0 else 1)) != 0) = !(decide a || decide b) := by
  by_cases ha : a <;> by_cases hb : b <;> simp [ha, hb]

/-- `nonzero d n t`: `d :=` whether `n` is not zero. -/
theorem nonzero_ok {s : State} {d n t : Reg} (hnt : n ≠ t) {is : List Instr} {Q : State → Prop}
    (k : ∀ u, u.gpr d = (if s.gpr n = 0 then 0 else 1) → Only [t, d] s u → WP isa (.block is) u Q) :
    WP isa (.block (Impl.Argon2.RISCV64.Derive.nonzero d n t ++ is)) s Q := by
  simp only [Impl.Argon2.RISCV64.Derive.nonzero, List.cons_append, List.nil_append]
  refine wp_li (by decide) fun s₁ u₁ => wp_sub fun s₂ u₂ => wp_or fun s₃ u₃ =>
    wp_srl (by decide) fun u u₄ => k u ?_ ?_
  · rw [u₄.gpr, u₃.gpr, u₂.gpr, u₂.other n hnt, u₁.gpr, u₁.other n hnt,
      show BitVec.ofNat 64 0 = 0 from rfl, nz]
  · exact (((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)).trans (Only.of_upd u₄)
      |>.mono (by simp)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `addressMode`: `a5` is nonzero for data-dependent addressing. -/
theorem addressMode_ok {s : State} (h : Inv s₀ s) {pass slice lane index : Nat}
    (ps : Pos s₀ s pass slice lane index) (hpass : pass < 2 ^ 32) (hs : slice < 4) :
    WP isa (.block Impl.Argon2.RISCV64.Derive.addressMode) s fun t =>
      VG.RISCV64.eval (.nonzero .a5) t = some (!independent (prm s₀) pass slice) ∧
        Only [.a0, .a1, .a2, .a3, .a4, .a5] s t := by
  have hk := hp.kind_le
  have K : (arg32 s₀ 0).setWidth 64 = BitVec.ofNat 64 (kindV s₀).toNat := ofNat_toNat (toNat_ext32 _)
  unfold Impl.Argon2.RISCV64.Derive.addressMode
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine wp_ldw hp h (i := 0) (by decide) fun s₁ u₁ => wp_li (by decide) fun s₂ u₂ =>
    wp_xor fun s₃ u₃ => wp_li (by decide) fun s₄ u₄ => wp_xor fun s₅ u₅ => ?_
  have o₅ := ((((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)).trans
    (Only.of_upd u₄)).trans (Only.of_upd u₅)
  have i₅ := h.only o₅
  refine wp_ldloc i₅ (d := passOff) (by decide) fun s₆ u₆ => wp_or fun s₇ u₇ => ?_
  have o₇ := (o₅.trans (Only.of_upd u₆)).trans (Only.of_upd u₇)
  have i₇ := h.only o₇
  refine wp_ldloc i₇ (d := sliceOff) (by decide) fun s₈ u₈ => wp_srl (by decide) fun s₉ u₉ =>
    wp_or fun s₁₀ u₁₀ => ?_
  have o₁₀ := ((o₇.trans (Only.of_upd u₈)).trans (Only.of_upd u₉)).trans (Only.of_upd u₁₀)
  have v4 : s₁₀.gpr .a1 = BitVec.ofNat 64 (kindV s₀).toNat ^^^ BitVec.ofNat 64 1 := by
    rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.gpr, K]
  have v5 : s₁₀.gpr .a2 = (BitVec.ofNat 64 (kindV s₀).toNat ^^^ BitVec.ofNat 64 2) |||
      BitVec.ofNat 64 pass ||| (BitVec.ofNat 64 slice >>> 1) := by
    rw [u₁₀.gpr, u₉.gpr, u₉.other _ (by decide), u₈.gpr, u₈.other _ (by decide), u₇.gpr,
      u₆.gpr, u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, K, lw_mem o₇.mem, ps.slice,
      lw_mem o₅.mem, ps.pass]
  refine nonzero_ok (by decide) fun s₁₁ v₁₁ o₁₁ => nonzero_ok (by decide) fun s₁₂ v₁₂ o₁₂ =>
    wp_and fun t ut => WP.block_nil ⟨?_, ?_⟩
  · have r8 : t.gpr .a5 = (if BitVec.ofNat 64 (kindV s₀).toNat ^^^ BitVec.ofNat 64 1 = 0 then 0 else 1) &&&
        (if (BitVec.ofNat 64 (kindV s₀).toNat ^^^ BitVec.ofNat 64 2) ||| BitVec.ofNat 64 pass |||
          (BitVec.ofNat 64 slice >>> 1) = 0 then 0 else 1) := by
      rw [ut.gpr, o₁₂.gpr _ (by decide), v₁₁, v4, v₁₂, o₁₁.gpr _ (by decide), v5]
    have k1 : (BitVec.ofNat 64 (kindV s₀).toNat ^^^ BitVec.ofNat 64 1 = 0) ↔ (kindV s₀).toNat = 1 := by
      rcases (by omega_using [hk] : (kindV s₀).toNat = 0 ∨ (kindV s₀).toNat = 1 ∨ (kindV s₀).toNat = 2) with
        e | e | e <;> rw [e] <;> decide
    rw [VG.RISCV64.Wp.eval_nonzero, r8, mode_bits, independent_eq hk]
    simp only [k1, id_zero hk (by omega_using [hpass] : pass < 2 ^ 64) hs, Bool.decide_and, Bool.and_assoc]
  · exact (((o₁₀.trans o₁₁).trans o₁₂).trans (Only.of_upd ut)).mono (by simp)

end

end VG.Proof.Argon2.RISCV64.Derive

end

end

/-!
# Argon2 on RISC-V: the filling state, and data-dependent addressing

`FS.keep`: what keeps the filling state (`FS.of_only`, `FS.store`,
`FS.frame`). `dependentWord_ok`: J₁ and J₂, the halves of the previous
block's first doubleword, to the frame (`Rand`).
-/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.Derive

open VG VG.RISCV64
open VG.RISCV64.Wp (Upd Mupd wp_add wp_sub wp_addi wp_subi wp_li wp_mv wp_ld wp_sd wp_xor)
open VG.Proof.Argon2.RISCV64 (wp_sll wp_srl wp_srlw wp_mul wp_mulhu wp_or wp_and wp_lwu wp_sw)
open VG.RISCV64.Wp (Upd Mupd)
open VG.Spec.Argon2 (Block zeroBlock FillState)
open VG.Proof.Argon2 (matrixCell Represents)
open VG.Impl.Argon2.RISCV64.Derive (j1Off j2Off)

/-- Doubleword `j` of a block. -/
theorem blockAt_get (m : Mem) (p : Addr) {j : Nat} (hj : j < 128) :
    (blockAt m p)[j] = m.readW (p + BitVec.ofNat 64 (8 * j)) 64 := by
  simp only [blockAt, Vector.getElem_ofFn, Mem.readW, BitVec.setWidth_eq]

/-- J₁ and J₂, the halves of the random word `w`, in the frame. -/
def Rand (s₀ s : State) (w : BitVec 64) : Prop :=
  lw s₀ s j1Off = w &&& 0xffffffff ∧ lw s₀ s j2Off = w >>> 32

theorem lo_ext (w : BitVec 64) : (w.setWidth 32).setWidth 64 = w &&& 0xffffffff := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and]
  rw [show (0xffffffff : BitVec 64).toNat = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have := Nat.mod_lt w.toNat (show 0 < 2 ^ 32 by decide)
  omega_using []

theorem hi_ext (w : BitVec 64) : (w.extractLsb' 32 32).setWidth 64 = w >>> 32 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  have := w.isLt
  have h32 : w.toNat / 2 ^ 32 < 2 ^ 32 := by omega_using []
  rw [Nat.mod_eq_of_lt h32, Nat.mod_eq_of_lt (by omega_using [])]

theorem FS.keep {s₀ s t : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (it : Inv s₀ t)
    (hl : ∀ d, 184 ≤ d → d + 8 ≤ 248 → lw s₀ t d = lw s₀ s d)
    (hc : blockAt t.mem (scrP s₀ + BitVec.ofNat 64 2048) = blockAt s.mem (scrP s₀ + BitVec.ofNat 64 2048))
    (hm : ∀ k < (prm s₀).blocks,
      blockAt t.mem (matrixCell (memP s₀) k) = blockAt s.mem (matrixCell (memP s₀) k)) :
    FS s₀ pass slice lane index ctr st t := by
  refine ⟨it, Prm.of_lw h.pr fun d h₁ h₂ => hl d (by omega_using [h₁]) (by omega_using [h₂]),
    h.pos.of_lw fun d h₁ h₂ => hl d (by omega_using [h₁]) (by omega_using [h₂]), ?_, Represents.keep h.mem hm⟩
  obtain ⟨c0, c1, c2 | ⟨c3, c4⟩⟩ := h.cache
  · exact ⟨c0, by rw [hl _ (by decide) (by decide)]; exact c1, .inl c2⟩
  · exact ⟨c0, by rw [hl _ (by decide) (by decide)]; exact c1, .inr ⟨c3, by rw [hc]; exact c4⟩⟩

/-- A step that writes only registers the invariant does not name keeps the
filling state. -/
theorem FS.of_only {s₀ s t : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) {ds : List Reg} (o : Only ds s t)
    (hd : ∀ r ∈ ds, Free r := by decide) : FS s₀ pass slice lane index ctr st t :=
  h.keep (h.inv.only o hd) (fun d _ _ => lw_mem o.mem d) (by rw [o.mem]) fun _ _ => by rw [o.mem]

/-- Regions a step of the filling loops may write without changing the filling state. -/
def Outside (s₀ : State) (r : Region) : Prop :=
  r.Disjoint ⟨at' s₀ 184, 64⟩ ∧ r.Disjoint ⟨scrP s₀ + BitVec.ofNat 64 2048, 1024⟩ ∧ r.Disjoint (memR s₀)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem FS.frame {s t : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (it : Inv s₀ t) {rs : List Region}
    (f : Frame rs s.mem t.mem) (ho : ∀ r ∈ rs, Outside s₀ r) : FS s₀ pass slice lane index ctr st t := by
  refine h.keep it (fun d h₁ h₂ => ?_) ?_ fun k hk => ?_
  · refine f.readW (r := ⟨E s₀ + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
      (fun r hr => (ho r hr).1.symm.sub_left ?_) (by decide)
    exact Offset.sub _ (by omega_using [h₁]) (by omega_using [h₂])
  · exact blockAt_keep f fun r hr => (ho r hr).2.1.symm
  · have hk' : k < blocksN s₀ := by rw [hp.blocks]; exact hk
    exact blockAt_keep f fun r hr => (ho r hr).2.2.symm.sub_left (Proof.Argon2.matrixCell_sub _ _ _ hk')

/-- A store to the frame outside the filling state's variables keeps the
filling state. -/
theorem FS.store {s t : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (it : Inv s₀ t) {d : Nat} (hd : 248 ≤ d)
    (hd' : d + 8 ≤ 320) {v : BitVec 64} (hm : t.mem = s.mem.writeW (E s₀ + BitVec.ofNat 64 d) v) :
    FS s₀ pass slice lane index ctr st t := by
  refine h.frame hp it (rs := [⟨E s₀ + BitVec.ofNat 64 d, 8⟩]) (by rw [hm]; exact frame_loc v)
    fun r hr => ?_
  simp only [List.mem_singleton] at hr; subst hr
  refine ⟨Offset.disjoint _ (by omega_using [hd]) (by omega_using [hd']) (by omega_using []), ?_, ?_⟩
  · exact (stk_disj hp (by omega_using [hd']) (scrR s₀) (by simp)).sub_right (scr_sub (by decide))
  · exact stk_disj hp (by omega_using [hd']) (memR s₀) (by simp)

theorem cell_al (c : Nat) {o : Nat} (ho : o % 4 = 0) :
    (matrixCell (memP s₀) c + BitVec.ofNat 64 o).toNat % 4 = 0 := by
  rw [matrixCell, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  exact al_add (by decide) (.inr (by have := hp.mem_al; omega_using [this])) (by omega_using [ho])

theorem outside_scr {o n : Nat} (h : o + n ≤ 2048 ∨ (3072 ≤ o ∧ o + n ≤ 16384)) :
    Outside s₀ ⟨scrP s₀ + BitVec.ofNat 64 o, n⟩ := by
  have sub : Region.Sub ⟨scrP s₀ + BitVec.ofNat 64 o, n⟩ (scrR s₀) := Offset.sub_base _ (by omega_using [h])
  refine ⟨((stk_disj hp (d := 184) (n := 64) (by decide) (scrR s₀) (by simp)).symm.sub_left sub),
    Offset.disjoint _ (by omega_using [h]) (by omega_using [h]) (by omega_using []), hp.mem_scr.symm.sub_left sub⟩

/-- `dependentWord`: J₁ and J₂ are the halves of the previous block's first doubleword. -/
theorem dependentWord_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (hl : lane < lanesN s₀) (hs : slice < 4)
    (hi : index < (prm s₀).segmentLen) :
    WP isa Impl.Argon2.RISCV64.Derive.dependentWord s fun t => FS s₀ pass slice lane index ctr st t ∧
      Rand s₀ t (blockAt s.mem (matrixCell (memP s₀) (lane * (prm s₀).laneLen +
        (slice * (prm s₀).segmentLen + index + (prm s₀).laneLen - 1) % (prm s₀).laneLen)))[0] := by
  have L8 := laneLen_ge hp
  obtain ⟨cl, cf⟩ := cell_fits hp hl
    (col := (slice * (prm s₀).segmentLen + index + (prm s₀).laneLen - 1) % (prm s₀).laneLen)
    (Nat.mod_lt _ (by omega_using [L8]))
  unfold Impl.Argon2.RISCV64.Derive.dependentWord
  refine WP.seq ((prevPointer_ok hp h.inv h.pr h.pos hl hs hi).mono fun s₁ ⟨a₁, k₁⟩ => ?_)
  generalize (lane * (prm s₀).laneLen + (slice * (prm s₀).segmentLen + index + (prm s₀).laneLen - 1) %
    (prm s₀).laneLen) = c at cl cf a₁ ⊢
  have h₁ := h.of_only k₁
  have hb := blocks_lt' hp
  have inP : ∀ o, o + 4 ≤ 1024 → (memR s₀).Contains (matrixCell (memP s₀) c + BitVec.ofNat 64 o) 4 :=
    fun o ho => by
      rw [matrixCell, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      exact Offset.contains_base _ (by omega_using [cl, ho]) (by omega_using [cl, hb, ho])
  have mW : ∀ t, Inv s₀ t → memR s₀ ∈ t.wr := fun t it => by rw [it.wr]; exact mem_mem hp
  have hb := blocks_lt' hp
  have c0 : (memR s₀).Contains (matrixCell (memP s₀) c) 4 :=
    Offset.contains_base (memP s₀) (d := c * 1024) (n := 4) (k := blocksN s₀ * 1024)
      (Nat.le_trans (Nat.add_le_add_left (by decide) _) cf) (by omega_arith)
  refine wp_lwu (a := matrixCell (memP s₀) c) (by decide) (by rw [a₁]; simp [matrixCell])
    (cell_al hp c (o := 0) (by decide) |> fun h => by simpa using h)
    ⟨_, List.mem_append_right _ (mW _ h₁.inv), c0⟩ fun s₂ u₂ => ?_
  have h₂ := h₁.of_only (Only.of_upd u₂)
  refine wp_stloc h₂.inv (d := j1Off) (by decide) fun s₃ i₃ v₃ o₃ g₃ m₃ => ?_
  have h₃ := h₂.store hp i₃ (d := j1Off) (by decide) (by decide) m₃
  refine wp_lwu (a := matrixCell (memP s₀) c + BitVec.ofNat 64 4) (by decide)
    (by rw [g₃, u₂.other _ (by decide), a₁]; rfl) (cell_al hp c (by decide))
    ⟨_, List.mem_append_right _ (mW _ h₃.inv), inP 4 (by decide)⟩ fun s₄ u₄ => ?_
  have h₄ := h₃.of_only (Only.of_upd u₄)
  refine wp_stloc h₄.inv (d := j2Off) (by decide) fun t it vt ot gt mt => WP.block_nil ⟨?_, ?_, ?_⟩
  · exact h₄.store hp it (d := j2Off) (by decide) (by decide) mt
  · have w0 : s.mem.readW (matrixCell (memP s₀) c) 64 = (blockAt s.mem (matrixCell (memP s₀) c))[0] := by
      rw [blockAt_get _ _ (by decide)]; simp
    rw [ot j1Off (by decide) (by decide), lw_mem u₄.mem, v₃, u₂.gpr, k₁.mem, Mem.readW_lo32 w0, lo_ext]
  · have sub : Region.Sub ⟨matrixCell (memP s₀) c, 8⟩ (memR s₀) :=
      Offset.sub_base (memP s₀) (d := c * 1024) (n := 8) (k := blocksN s₀ * 1024)
        (Nat.le_trans (Nat.add_le_add_left (by decide) _) cf)
    have w0 : s₃.mem.readW (matrixCell (memP s₀) c) 64 = (blockAt s.mem (matrixCell (memP s₀) c))[0] := by
      rw [m₃, (frame_loc _).readW (r := ⟨matrixCell (memP s₀) c, 8⟩) (Region.contains_self _ _)
        (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (loc_disj hp (d := j1Off) (by decide) (memR s₀) (by simp)).symm.sub_left sub)
        (by decide), u₂.mem, k₁.mem, blockAt_get _ _ (by decide)]
      simp
    rw [vt, u₄.gpr]
    exact (congrArg (BitVec.setWidth 64) (Mem.readW_hi32 w0)).trans (hi_ext _)

end

end VG.Proof.Argon2.RISCV64.Derive

end

end

/-! ### `Argon2.RISCV64.Derive.FillInput`, which this module and modules that import it used -/

section

/-!
# Argon2 on RISC-V: the address-generation input block

`input_ok`: `clearAt s4 1024`, `clearAt s0 1024` and `addressHeader` leave
the input block of §3.4.1.2 (`Proof.Argon2.addressInput`) at
`scratch + 1024` and a zero block at `scratch + 3072`, writing only those two
blocks.
-/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.Derive

open VG VG.RISCV64
open VG.RISCV64.Wp (Upd Mupd wp_add wp_sub wp_addi wp_subi wp_li wp_mv wp_ld wp_sd wp_xor)
open VG.Proof.Argon2.RISCV64 (wp_sll wp_srl wp_srlw wp_mul wp_mulhu wp_or wp_and wp_lwu wp_sw)
open VG.RISCV64.Wp (Upd Mupd wp_li)
open VG.Spec.Argon2 (Block zeroBlock)
open VG.Impl.Argon2.RISCV64.Derive (passOff laneOff sliceOff counterOff ld lda ldw)

/-- Doublewords of `scratch`. -/
abbrev sd (s₀ : State) (m : Mem) (o : Nat) : BitVec 64 := m.readW (scrP s₀ + BitVec.ofNat 64 o) 64

/-- A doubleword of `scratch` after a store to another, or the same. -/
theorem sd_store {s₀ : State} (m : Mem) {a b : Nat} (ha : a + 8 ≤ 16384) (hb : b + 8 ≤ 16384)
    (h : a = b ∨ a + 8 ≤ b ∨ b + 8 ≤ a) (v : BitVec 64) :
    sd s₀ (m.writeW (scrP s₀ + BitVec.ofNat 64 a) v) b = if a = b then v else sd s₀ m b := by
  by_cases e : a = b
  · subst e; rw [ite_eq_left rfl]; exact Mem.readW_writeW_self64 _ _ _
  · rw [ite_eq_right e]
    exact Mem.readW_writeW_sep (Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)

/-- A block of `scratch`, from its doublewords. -/
theorem blockAt_of_sd {s₀ : State} {m : Mem} {o : Nat} {f : Nat → BitVec 64}
    (h : ∀ i < 128, sd s₀ m (o + 8 * i) = f i) :
    blockAt m (scrP s₀ + BitVec.ofNat 64 o) = Vector.ofFn fun j : Fin 128 => f j.val := by
  apply Vector.ext
  intro j hj
  rw [blockAt_get _ _ hj, Vector.getElem_ofFn, ← h j hj, sd, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `n` stores of `a0 = 0` to `b + d + 8k`, with `b` pointing `B` bytes into
`scratch`. -/
theorem zeros_ok {s : State} (h : Inv s₀ s) {b : Reg} {B : Nat}
    (hb : s.gpr b = scrP s₀ + BitVec.ofNat 64 B) {d : Nat} (hd : B + d + 1024 ≤ 4096)
    (hd' : d + 1024 ≤ 2048) (hd8 : (B + d) % 8 = 0) (ha : s.gpr .a0 = 0) :
    ∀ n ≤ 128, WP isa (.block ((List.range n).map fun k => Instr.store .d .a0 b (d + 8 * k))) s
      fun t => Inv s₀ t ∧ t.gpr = s.gpr ∧ Frame [⟨scrP s₀ + BitVec.ofNat 64 (B + d), 1024⟩] s.mem t.mem ∧
        ∀ i < n, sd s₀ t.mem (B + d + 8 * i) = 0
  | 0, _ => WP.block_nil ⟨h, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hn => by
    rw [List.range_succ, List.map_append, List.map_singleton]
    refine WP.block_append ((zeros_ok h hb hd hd' hd8 ha n (by omega_arith)).mono fun t ⟨it, gt, ft, wt⟩ => ?_)
    have hc' : (⟨scrP s₀ + BitVec.ofNat 64 (B + d), 1024⟩ : Region).Contains
        (scrP s₀ + BitVec.ofNat 64 (B + (d + 8 * n))) 8 :=
      Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)
    refine wp_stscrb hp it (b := b) (B := B) (by rw [gt, hb]) (o := d + 8 * n) (by omega_arith)
      (by omega_arith) (by omega_arith) fun t₁ i₁ m₁ g₁ _ _ => WP.block_nil ⟨i₁, by rw [g₁, gt], ?_, fun i hi => ?_⟩
    · rw [m₁]
      exact ft.writeW (List.mem_singleton_self _) _ hc'
    · rw [m₁, gt, ha, sd_store _ (by omega_arith) (by omega_arith) (by omega_arith)]
      by_cases e : B + (d + 8 * n) = B + d + 8 * i
      · rw [ite_eq_left e]
      · rw [ite_eq_right e]; exact wt i (by omega_arith)

/-- `clearAt b d`: zero `scratch[B + d, B + d + 1024)`. -/
theorem clearAt_ok {s : State} (h : Inv s₀ s) {b : Reg} (hba : b ≠ .a0) {B : Nat}
    (hb : s.gpr b = scrP s₀ + BitVec.ofNat 64 B) {d : Nat} (hd : B + d + 1024 ≤ 4096)
    (hd' : d + 1024 ≤ 2048) (hd8 : (B + d) % 8 = 0) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → (∀ r, r ≠ .a0 → t.gpr r = s.gpr r) →
      Frame [⟨scrP s₀ + BitVec.ofNat 64 (B + d), 1024⟩] s.mem t.mem →
      (∀ i < 128, sd s₀ t.mem (B + d + 8 * i) = 0) → WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.RISCV64.Derive.clearAt b d ++ is)) s Q := by
  unfold Impl.Argon2.RISCV64.Derive.clearAt
  simp only [List.cons_append]
  refine wp_li (by decide) fun s₁ u₁ => ?_
  have i₁ := h.upd u₁
  refine WP.block_append ((zeros_ok hp i₁ (by rw [u₁.other _ hba, hb]) hd hd' hd8 u₁.gpr 128
    (Nat.le_refl _)).mono fun t ⟨it, gt, ft, wt⟩ => k t it (fun r a => ?_) ?_ wt)
  · rw [gt, u₁.other _ a]
  · rw [show s.mem = s₁.mem by rw [u₁.mem]]; exact ft

end

/-- The seven doublewords of the address-generation input block. -/
def hdr (s₀ : State) (pass lane slice c : Nat) : Nat → BitVec 64
  | 0 => BitVec.ofNat 64 pass
  | 1 => BitVec.ofNat 64 lane
  | 2 => BitVec.ofNat 64 slice
  | 3 => arg s₀ 14
  | 4 => (arg32 s₀ 5).setWidth 64
  | 5 => (arg32 s₀ 0).setWidth 64
  | _ => BitVec.ofNat 64 c

/-- The doublewords of the input block after its first `n` are written over `m`'s. -/
def HW (s₀ : State) (m : Mem) (pass lane slice c n : Nat) (m' : Mem) : Prop :=
  ∀ i < 128, sd s₀ m' (1024 + 8 * i) = if i < n then hdr s₀ pass lane slice c i else sd s₀ m (1024 + 8 * i)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- One doubleword of the header. -/
theorem hdr_step {m : Mem} {pass lane slice c n : Nat} (hn : n < 7) {u : State} (h : Inv s₀ u)
    (ha : u.gpr .a0 = hdr s₀ pass lane slice c n) (hw : HW s₀ m pass lane slice c n u.mem)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → t.gpr = u.gpr → Frame [⟨scrP s₀ + BitVec.ofNat 64 1024, 1024⟩] u.mem t.mem →
      HW s₀ m pass lane slice c (n + 1) t.mem → WP isa (.block is) t Q) :
    WP isa (.block (.store .d .a0 .s4 (1024 + 8 * n) :: is)) u Q := by
  have hc' : (⟨scrP s₀ + BitVec.ofNat 64 1024, 1024⟩ : Region).Contains
      (scrP s₀ + BitVec.ofNat 64 (1024 + 8 * n)) 8 :=
    Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)
  refine wp_stscrd hp h (o := 1024 + 8 * n) (by omega_arith) (by omega_arith) (by omega_arith)
    fun t it mt gt _ _ => k t it gt ?_ fun i hi => ?_
  · rw [mt]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ hc'
  · rw [mt, sd_store _ (by omega_arith) (by omega_arith) (by omega_arith), ha, hw i hi]
    by_cases e : 1024 + 8 * n = 1024 + 8 * i
    · rw [ite_eq_left e, ite_eq_left (by omega_arith), show i = n by omega_arith]
    · rw [ite_eq_right e]
      by_cases c₁ : i < n
      · rw [ite_eq_left c₁, ite_eq_left (by omega_arith)]
      · rw [ite_eq_right c₁, ite_eq_right (by omega_arith)]

omit hp in
theorem addressHeader_eq : Impl.Argon2.RISCV64.Derive.addressHeader =
    [ld .a0 passOff, .store .d .a0 .s4 (1024 + 8 * 0), ld .a0 laneOff, .store .d .a0 .s4 (1024 + 8 * 1),
      ld .a0 sliceOff, .store .d .a0 .s4 (1024 + 8 * 2), lda .a0 14, .store .d .a0 .s4 (1024 + 8 * 3),
      ldw .a0 5, .store .d .a0 .s4 (1024 + 8 * 4), ldw .a0 0, .store .d .a0 .s4 (1024 + 8 * 5),
      ld .a0 counterOff, .store .d .a0 .s4 (1024 + 8 * 6)] := rfl

theorem aheader_ok {s : State} (h : Inv s₀ s) {pass slice lane index c : Nat}
    (ps : Pos s₀ s pass slice lane index) (hc : lw s₀ s counterOff = BitVec.ofNat 64 c) :
    WP isa (.block Impl.Argon2.RISCV64.Derive.addressHeader) s fun t => Inv s₀ t ∧
      (∀ r, r ≠ .a0 → t.gpr r = s.gpr r) ∧
      Frame [⟨scrP s₀ + BitVec.ofNat 64 1024, 1024⟩] s.mem t.mem ∧ HW s₀ s.mem pass lane slice c 7 t.mem := by
  have fsub : ∀ r ∈ [(⟨scrP s₀ + BitVec.ofNat 64 1024, 1024⟩ : Region)],
      ∃ r' ∈ [memR s₀, scrR s₀, outR s₀], Region.Sub r r' := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨scrR s₀, by simp, Offset.sub_base _ (by decide)⟩
  have w₀ : HW s₀ s.mem pass lane slice c 0 s.mem := fun i _ => (ite_eq_right (Nat.not_lt_zero i)).symm
  rw [addressHeader_eq]
  refine wp_ldloc h (d := passOff) (by decide) fun s₁ u₁ => ?_
  refine hdr_step hp (n := 0) (by decide) (h.upd u₁) (by rw [u₁.gpr, ps.pass]; rfl)
    (by rw [u₁.mem]; exact w₀) fun t₁ i₁ g₁ f₁ w₁ => ?_
  refine wp_ldloc i₁ (d := laneOff) (by decide) fun s₂ u₂ => ?_
  have F₁ : Frame [⟨scrP s₀ + BitVec.ofNat 64 1024, 1024⟩] s.mem t₁.mem := by rw [← u₁.mem]; exact f₁
  refine hdr_step hp (n := 1) (by decide) (i₁.upd u₂)
    (by rw [u₂.gpr, lw_keep hp F₁ fsub (by decide), ps.lane]; rfl)
    (by rw [u₂.mem]; exact w₁) fun t₂ i₂ g₂ f₂ w₂ => ?_
  have F₂ := F₁.trans (by rw [← u₂.mem]; exact f₂)
  refine wp_ldloc i₂ (d := sliceOff) (by decide) fun s₃ u₃ => ?_
  refine hdr_step hp (n := 2) (by decide) (i₂.upd u₃)
    (by rw [u₃.gpr, lw_keep hp F₂ fsub (by decide), ps.slice]; rfl)
    (by rw [u₃.mem]; exact w₂) fun t₃ i₃ g₃ f₃ w₃ => ?_
  have F₃ := F₂.trans (by rw [← u₃.mem]; exact f₃)
  refine wp_lda hp i₃ (i := 14) (by decide) fun s₄ u₄ => ?_
  refine hdr_step hp (n := 3) (by decide) (i₃.upd u₄) (by rw [u₄.gpr]; rfl)
    (by rw [u₄.mem]; exact w₃) fun t₄ i₄ g₄ f₄ w₄ => ?_
  have F₄ := F₃.trans (by rw [← u₄.mem]; exact f₄)
  refine wp_ldw hp i₄ (i := 5) (by decide) fun s₅ u₅ => ?_
  refine hdr_step hp (n := 4) (by decide) (i₄.upd u₅) (by rw [u₅.gpr]; rfl)
    (by rw [u₅.mem]; exact w₄) fun t₅ i₅ g₅ f₅ w₅ => ?_
  have F₅ := F₄.trans (by rw [← u₅.mem]; exact f₅)
  refine wp_ldw hp i₅ (i := 0) (by decide) fun s₆ u₆ => ?_
  refine hdr_step hp (n := 5) (by decide) (i₅.upd u₆) (by rw [u₆.gpr]; rfl)
    (by rw [u₆.mem]; exact w₅) fun t₆ i₆ g₆ f₆ w₆ => ?_
  have F₆ := F₅.trans (by rw [← u₆.mem]; exact f₆)
  refine wp_ldloc i₆ (d := counterOff) (by decide) fun s₇ u₇ => ?_
  refine hdr_step hp (n := 6) (by decide) (i₆.upd u₇)
    (by rw [u₇.gpr, lw_keep hp F₆ fsub (by decide), hc]; rfl)
    (by rw [u₇.mem]; exact w₆) fun t i g f w => WP.block_nil ⟨i, fun r a => ?_,
      F₆.trans (by rw [← u₇.mem]; exact f), w⟩
  rw [g, u₇.other _ a, g₆, u₆.other _ a, g₅, u₅.other _ a, g₄, u₄.other _ a, g₃, u₃.other _ a, g₂,
    u₂.other _ a, g₁, u₁.other _ a]

omit hp in
/-- A doubleword of `scratch` outside a frame's region of `scratch`. -/
theorem sd_frame {m m' : Mem} {a n : Nat} (f : Frame [⟨scrP s₀ + BitVec.ofNat 64 a, n⟩] m m') {o : Nat}
    (h : o + 8 ≤ a ∨ a + n ≤ o) (ho : o + 8 ≤ 16384) (hn : a + n ≤ 16384) : sd s₀ m' o = sd s₀ m o := by
  refine f.readW (r := ⟨scrP s₀ + BitVec.ofNat 64 o, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  exact Offset.disjoint _ h (by omega_arith) (by omega_arith)

theorem input_words {pass lane slice c : Nat} :
    (Vector.ofFn fun j : Fin 128 => if j.val < 7 then hdr s₀ pass lane slice c j.val else 0) =
      Proof.Argon2.addressInput (prm s₀) pass lane slice c := by
  have eb : arg s₀ 14 = BitVec.ofNat 64 (prm s₀).blocks := by rw [← hp.blocks]; simp
  have ep : (arg32 s₀ 5).setWidth 64 = BitVec.ofNat 64 (prm s₀).passes := ofNat_toNat (toNat_ext32 _)
  have ek : (arg32 s₀ 0).setWidth 64 = BitVec.ofNat 64 (prm s₀).variant.code := by
    rw [variant_code hp.kind_le]; exact ofNat_toNat (toNat_ext32 _)
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_ofFn, Proof.Argon2.addressInput, Vector.getElem_set, zeroBlock,
    Vector.getElem_replicate]
  rcases (by omega_arith : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ 7 ≤ j) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | hj7
  · simp [hdr]
  · simp [hdr]
  · simp [hdr]
  · simp [hdr, eb]
  · simp [hdr, ep]
  · simp [hdr, ek]
  · simp [hdr]
  · rw [ite_eq_right (by omega_arith)]
    simp (disch := omega_arith) only [ite_eq_right]

/-- The address-generation input block at `scratch + 1024`, and a zero block at `scratch + 3072`. -/
theorem input_ok {s : State} (h : Inv s₀ s) {pass slice lane index c : Nat}
    (ps : Pos s₀ s pass slice lane index) (hc : lw s₀ s counterOff = BitVec.ofNat 64 c) :
    WP isa (.block (Impl.Argon2.RISCV64.Derive.clearAt .s4 1024 ++ Impl.Argon2.RISCV64.Derive.clearAt .s0 1024 ++
      Impl.Argon2.RISCV64.Derive.addressHeader)) s fun t => Inv s₀ t ∧
      (∀ r, r ≠ .a0 → t.gpr r = s.gpr r) ∧
      Frame [⟨scrP s₀ + BitVec.ofNat 64 1024, 1024⟩, ⟨scrP s₀ + BitVec.ofNat 64 3072, 1024⟩] s.mem t.mem ∧
      blockAt t.mem (scrP s₀ + BitVec.ofNat 64 1024) = Proof.Argon2.addressInput (prm s₀) pass lane slice c ∧
      blockAt t.mem (scrP s₀ + BitVec.ofNat 64 3072) = zeroBlock := by
  have fsub : ∀ d, d + 1024 ≤ 16384 → ∀ r ∈ [(⟨scrP s₀ + BitVec.ofNat 64 d, 1024⟩ : Region)],
      ∃ r' ∈ [memR s₀, scrR s₀, outR s₀], Region.Sub r r' := fun d hd r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨scrR s₀, by simp, Offset.sub_base _ hd⟩
  rw [List.append_assoc]
  refine clearAt_ok hp h (b := .s4) (by decide) (B := 0) (by rw [h.s4]; simp) (d := 1024) (by decide)
    (by decide) (by decide) fun t₁ i₁ g₁ f₁ z₁ => ?_
  refine clearAt_ok hp i₁ (b := .s0) (by decide) (B := 2048) i₁.s0 (d := 1024) (by decide)
    (by decide) (by decide) fun t₂ i₂ g₂ f₂ z₂ => ?_
  simp only [Nat.zero_add, show 2048 + 1024 = 3072 from rfl] at f₁ z₁ f₂ z₂
  have L : ∀ d, d + 8 ≤ 320 → lw s₀ t₂ d = lw s₀ s d := fun d h₂ => by
    rw [lw_keep hp f₂ (fsub _ (by decide)) h₂, lw_keep hp f₁ (fsub _ (by decide)) h₂]
  refine (aheader_ok hp i₂ (pass := pass) (slice := slice) (lane := lane) (index := index) (c := c)
    (ps.of_lw fun d h₁ h₂ => L d (by omega_arith)) (by rw [L _ (by decide)]; exact hc)).mono
    fun t ⟨it, gt, ft, wt⟩ => ⟨it, fun r a => by rw [gt r a, g₂ r a, g₁ r a], ?_, ?_, ?_⟩
  · refine (Frame.trans (f₁.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inl hr, fun _ h => h⟩)
      (f₂.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inr hr, fun _ h => h⟩)).trans
      (ft.sub fun r hr => ⟨⟨scrP s₀ + BitVec.ofNat 64 1024, 1024⟩, by simp, by
        simp only [List.mem_singleton] at hr; subst hr; exact fun _ h => h⟩)
  · rw [blockAt_of_sd (f := fun i => if i < 7 then hdr s₀ pass lane slice c i else 0) fun i hi => ?_,
      input_words hp]
    rw [wt i hi]
    by_cases e : i < 7
    · rw [ite_eq_left e, ite_eq_left e]
    · rw [ite_eq_right e, ite_eq_right e, sd_frame f₂ (by omega_arith) (by omega_arith) (by decide)]
      exact z₁ i hi
  · rw [blockAt_of_sd (f := fun _ => 0) fun i hi => ?_]
    · apply Vector.ext; intro j hj; simp [zeroBlock]
    rw [sd_frame ft (by omega_arith) (by omega_arith) (by decide)]
    exact z₂ i hi

end

end VG.Proof.Argon2.RISCV64.Derive

end

end

/-!
# Argon2 on RISC-V: the address block

`addressCalls_ok`: the address block, G(0, G(0, input)), at `scratch + 2048`.
`addressCache_ok`: J₁, J₂ from the cached address block, regenerated when
the index enters a new group of 128. `randomSource_ok`: J₁, J₂ are the
random word of `FillStep.random`.
-/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.Derive

open VG VG.RISCV64
open VG.RISCV64.Wp (Upd Mupd wp_add wp_sub wp_addi wp_subi wp_li wp_mv wp_ld wp_sd wp_xor)
open VG.Proof.Argon2.RISCV64 (wp_sll wp_srl wp_srlw wp_mul wp_mulhu wp_or wp_and wp_lwu wp_sw)
open VG.RISCV64.Wp (Upd Mupd wp_add wp_addi wp_sub wp_li wp_mv)
open VG.Spec.Argon2 (Block zeroBlock FillState compress addressBlock)
open VG.Proof.Argon2 (matrixCell Represents)
open VG.Impl.Argon2.RISCV64.Derive (indexOff counterOff j1Off j2Off)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- A register pointing `B` bytes into `scratch`: `s4` or `s0`. -/
def Base (s₀ : State) (s : State) (b : Reg) (B : Nat) : Prop :=
  (b = .s4 ∨ b = .s0) ∧ s.gpr b = scrP s₀ + BitVec.ofNat 64 B

/-- `stage (bx, x) (by, y) (bo, o)`: G of the blocks at `bx + x` and `by + y`
to `bo + o`, at `scratch + X`, `scratch + Y` and `scratch + O`. -/
theorem stage_ok {s : State} (h : Inv s₀ s) {bx by' bo : Reg} {Bx By Bo x y o : Nat}
    (hx : Base s₀ s bx Bx) (hy : Base s₀ s by' By) (hob : Base s₀ s bo Bo)
    (hxi : x < 2048) (hyi : y < 2048) (hoi : o < 2048)
    (ho' : Bo + o + 1024 ≤ 4096) (ho8 : (Bo + o) % 8 = 0)
    (hx' : Bx + x + 1024 ≤ 4096) (hx8 : (Bx + x) % 8 = 0)
    (hxo : Bx + x + 1024 ≤ Bo + o ∨ Bo + o + 1024 ≤ Bx + x)
    (hy' : By + y + 1024 ≤ 4096) (hy8 : (By + y) % 8 = 0)
    (hyo : By + y + 1024 ≤ Bo + o ∨ Bo + o + 1024 ≤ By + y) :
    WP isa (Impl.Argon2.RISCV64.Derive.stage (bx, x) (by', y) (bo, o)) s fun t => Inv s₀ t ∧
      (∀ q ∈ preserved, t.gpr q = s.gpr q) ∧
      Frame [⟨scrP s₀ + BitVec.ofNat 64 (Bo + o), 1024⟩, ⟨gwP s₀, 4096⟩] s.mem t.mem ∧
      blockAt t.mem (scrP s₀ + BitVec.ofNat 64 (Bo + o)) =
        compress (blockAt s.mem (scrP s₀ + BitVec.ofNat 64 (Bx + x)))
          (blockAt s.mem (scrP s₀ + BitVec.ofNat 64 (By + y))) := by
  unfold Impl.Argon2.RISCV64.Derive.stage Impl.Argon2.RISCV64.Derive.gScratch
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_addi hxi fun s₁ u₁ => wp_addi hyi fun s₂ u₂ =>
    wp_addi hoi fun s₃ u₃ => wp_addi (imm := 1024) (by decide) fun s₄ u₄ =>
    wp_addi (imm := 1024) (by decide) fun s₅ u₅ => WP.block_nil ?_)
  have o₅ := ((((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)).trans
    (Only.of_upd u₄)).trans (Only.of_upd u₅)
  have i₅ := h.only o₅
  have nb : ∀ b : Reg, (b = .s4 ∨ b = .s0) → b ≠ .a0 ∧ b ≠ .a1 ∧ b ≠ .a2 ∧ b ≠ .a3 := by
    intro b hb; rcases hb with rfl | rfl <;> decide
  obtain ⟨x1, x2, x3, -⟩ := nb bx hx.1
  obtain ⟨y1, y2, y3, -⟩ := nb by' hy.1
  obtain ⟨o1, o2, o3, -⟩ := nb bo hob.1
  have off : ∀ (B d : Nat), scrP s₀ + BitVec.ofNat 64 B + BitVec.ofNat 64 d =
      scrP s₀ + BitVec.ofNat 64 (B + d) := fun B d => by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  have dx : s₅.gpr .a3 = gwP s₀ := by
    rw [u₅.gpr, u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      h.s0, off, off]
  have ax : s₅.gpr .a0 = scrP s₀ + BitVec.ofNat 64 (Bx + x) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.gpr, hx.2, off]
  have sx : s₅.gpr .a1 = scrP s₀ + BitVec.ofNat 64 (By + y) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      u₁.other _ y1, hy.2, off]
  have cx : s₅.gpr .a2 = scrP s₀ + BitVec.ofNat 64 (Bo + o) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ o2,
      u₁.other _ o1, hob.2, off]
  refine ccall_ok hp i₅ dx ho' ho8 cx (by rw [ax]; exact .inr ⟨Bx + x, hx', hx8, hxo, rfl⟩)
    (by rw [sx]; exact .inr ⟨By + y, hy', hy8, hyo, rfl⟩) fun t it cs f post =>
      ⟨it, fun q hq => ?_, by rw [← o₅.mem]; exact f, by rw [post, ax, sx, o₅.mem]⟩
  rw [cs q hq]
  exact o₅.gpr q fun hm => by revert hq; revert hm; revert q; decide

omit hp in
/-- A block of `scratch` at `d`, outside the regions G's call at `o` writes. -/
theorem stage_keep {m m' : Mem} {o : Nat} (ho' : o + 1024 ≤ 4096)
    (f : Frame [⟨scrP s₀ + BitVec.ofNat 64 o, 1024⟩, ⟨gwP s₀, 4096⟩] m m') {d : Nat}
    (hd' : d + 1024 ≤ 4096) (hdo : d + 1024 ≤ o ∨ o + 1024 ≤ d) :
    blockAt m' (scrP s₀ + BitVec.ofNat 64 d) = blockAt m (scrP s₀ + BitVec.ofNat 64 d) := by
  refine blockAt_keep f fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint _ hdo (by omega_arith) (by omega_arith)
  · exact Offset.disjoint (scrP s₀) (d := d) (n := 1024) (e := 4096) (k := 4096) (.inl hd')
      (by omega_arith) (by decide)

omit hp in
theorem stage_frame {m m' : Mem} {o : Nat} (ho' : o + 1024 ≤ 4096)
    (f : Frame [⟨scrP s₀ + BitVec.ofNat 64 o, 1024⟩, ⟨gwP s₀, 4096⟩] m m') :
    Frame [scrR s₀] m m' :=
  f.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨scrR s₀, by simp, Offset.sub_base _ (by omega_arith)⟩
    · exact ⟨scrR s₀, by simp, Offset.sub_base (scrP s₀) (d := 4096) (n := 4096) (k := 16384) (by decide)⟩

/-- `addressCalls`: the address block for the counter `c` at `scratch + 2048`. -/
theorem addressCalls_ok {s : State} (h : Inv s₀ s) {pass slice lane index c : Nat}
    (ps : Pos s₀ s pass slice lane index) (hc : lw s₀ s counterOff = BitVec.ofNat 64 c) :
    WP isa Impl.Argon2.RISCV64.Derive.addressCalls s fun t => Inv s₀ t ∧
      (∀ q ∈ preserved, t.gpr q = s.gpr q) ∧ Frame [scrR s₀] s.mem t.mem ∧
      blockAt t.mem (scrP s₀ + BitVec.ofNat 64 2048) = addressBlock (prm s₀) pass lane slice c := by
  have b4 : ∀ t : State, Inv s₀ t → Base s₀ t .s4 0 := fun t it => ⟨.inl rfl, by rw [it.s4]; simp⟩
  have b0 : ∀ t : State, Inv s₀ t → Base s₀ t .s0 2048 := fun t it => ⟨.inr rfl, it.s0⟩
  unfold Impl.Argon2.RISCV64.Derive.addressCalls
  refine WP.seq ((input_ok hp h ps hc).mono fun t₁ ⟨i₁, g₁, f₁, b₁, z₁⟩ => ?_)
  refine WP.seq ((stage_ok hp i₁ (b0 _ i₁) (b4 _ i₁) (b4 _ i₁) (x := 1024) (y := 1024) (o := 0)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)).mono fun t₂ ⟨i₂, g₂, f₂, b₂⟩ => ?_)
  refine (stage_ok hp i₂ (b0 _ i₂) (b4 _ i₂) (b0 _ i₂) (x := 1024) (y := 0) (o := 0)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)).mono
    fun t ⟨it, gt, ft, bt⟩ => ⟨it, fun q hq => ?_, ?_, ?_⟩
  · rw [gt q hq, g₂ q hq]
    exact g₁ q fun e => by subst e; exact absurd hq (by decide)
  · refine Frame.trans (f₁.sub fun r hr => ?_) ((stage_frame (by decide) f₂).trans (stage_frame (by decide) ft))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨scrR s₀, by simp, Offset.sub_base _ (by decide)⟩
    · exact ⟨scrR s₀, by simp, Offset.sub_base _ (by decide)⟩
  · simp only [Nat.zero_add, Nat.add_zero, show 2048 + 1024 = 3072 from rfl] at bt b₂ f₂
    rw [bt, stage_keep (by decide) f₂ (d := 3072) (by decide) (by decide), b₂, z₁, b₁]
    rfl

end

theorem and127 {n : Nat} (h : n < 2 ^ 64) :
    BitVec.ofNat 64 n &&& BitVec.ofNat 64 127 = BitVec.ofNat 64 (n % 128) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (a := 127) (by decide), Nat.mod_eq_of_lt (a := n % 128) (by omega_arith),
    show 127 = 2 ^ 7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem shr7 {n : Nat} (h : n < 2 ^ 64) : BitVec.ofNat 64 n >>> 7 = BitVec.ofNat 64 (n / 128) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    Nat.mod_eq_of_lt (by omega_arith), Nat.shiftRight_eq_div_pow]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `cacheWord`: J₁ and J₂ are doubleword `index mod 128` of the cached address block. -/
theorem cacheWord_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (hi : index < 2 ^ 30) :
    WP isa (.block Impl.Argon2.RISCV64.Derive.cacheWord) s fun t => FS s₀ pass slice lane index ctr st t ∧
      Rand s₀ t ((blockAt s.mem (scrP s₀ + BitVec.ofNat 64 2048))[index % 128]'(Nat.mod_lt _ (by decide))) := by
  have e8 : 8 * (index % 128) < 1024 := by omega_arith
  unfold Impl.Argon2.RISCV64.Derive.cacheWord
  refine wp_ldloc h.inv (d := indexOff) (by decide) fun s₁ u₁ => wp_li (by decide) fun s₂ u₂ =>
    wp_and fun s₃ u₃ => wp_sll (by decide) fun s₄ u₄ => wp_add fun s₅ u₅ => ?_
  have o₅ := (((((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)).trans
    (Only.of_upd u₄)).trans (Only.of_upd u₅))
  have h₅ := h.of_only o₅
  have a₅ : s₅.gpr .a0 = scrP s₀ + BitVec.ofNat 64 (2048 + 8 * (index % 128)) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h.inv.s0, u₄.gpr, u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.gpr,
      h.pos.index, and127 (by omega_arith), ofNat_shl' (by omega_arith), BitVec.add_assoc,
      BitVec.ofNat_add_ofNat]
    congr 2; omega_arith
  have m₅ : s₅.mem = s.mem := o₅.mem
  have inS : ∀ t : State, Inv s₀ t → ∀ o, o + 4 ≤ 1024 →
      InRegions (t.rd ++ t.wr) (scrP s₀ + BitVec.ofNat 64 (2048 + 8 * (index % 128) + o)) 4 :=
    fun t it o ho => by
      rw [it.wr]
      exact ⟨scrR s₀, List.mem_append_right _ (scr_mem hp), Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have ad : ∀ o, s₅.gpr .a0 + BitVec.ofNat 64 o =
      scrP s₀ + BitVec.ofNat 64 (2048 + 8 * (index % 128) + o) := fun o => by
    rw [a₅, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  have al : ∀ o, o % 4 = 0 → (scrP s₀ + BitVec.ofNat 64 (2048 + 8 * (index % 128) + o)).toNat % 4 = 0 :=
    fun o ho => h.inv.scr_al (by decide) (by omega_arith)
  refine wp_lwu (a := scrP s₀ + BitVec.ofNat 64 (2048 + 8 * (index % 128) + 0)) (by decide) (ad 0)
    (al 0 (by decide)) (inS _ h₅.inv 0 (by decide)) fun s₆ u₆ => ?_
  have h₆ := h₅.of_only (Only.of_upd u₆)
  refine wp_stloc h₆.inv (d := j1Off) (by decide) fun s₇ i₇ v₇ o₇ g₇ m₇ => ?_
  have h₇ := h₆.store hp i₇ (d := j1Off) (by decide) (by decide) m₇
  refine wp_lwu (a := scrP s₀ + BitVec.ofNat 64 (2048 + 8 * (index % 128) + 4)) (by decide)
    (by rw [g₇, u₆.other _ (by decide)]; exact ad 4) (al 4 (by decide)) (inS _ h₇.inv 4 (by decide))
    fun s₈ u₈ => ?_
  have h₈ := h₇.of_only (Only.of_upd u₈)
  refine wp_stloc h₈.inv (d := j2Off) (by decide) fun t it vt ot gt mt => WP.block_nil ⟨?_, ?_, ?_⟩
  · exact h₈.store hp it (d := j2Off) (by decide) (by decide) mt
  · have w0 : s.mem.readW (scrP s₀ + BitVec.ofNat 64 (2048 + 8 * (index % 128) + 0)) 64 =
        (blockAt s.mem (scrP s₀ + BitVec.ofNat 64 2048))[index % 128] := by
      rw [Nat.add_zero, blockAt_get _ _ (Nat.mod_lt _ (by decide)), BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    rw [ot j1Off (by decide) (by decide), lw_mem u₈.mem, v₇, u₆.gpr, m₅, Mem.readW_lo32 w0, lo_ext]
  · have w0 : s₇.mem.readW (scrP s₀ + BitVec.ofNat 64 (2048 + 8 * (index % 128) + 0)) 64 =
        (blockAt s.mem (scrP s₀ + BitVec.ofNat 64 2048))[index % 128] := by
      rw [m₇, (frame_loc _).readW (r := ⟨scrP s₀ + BitVec.ofNat 64 (2048 + 8 * (index % 128) + 0), 8⟩)
        (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (loc_scr hp (by decide) (by omega_arith)).symm) (by decide),
        u₆.mem, m₅, Nat.add_zero, blockAt_get _ _ (Nat.mod_lt _ (by decide)), BitVec.add_assoc,
        BitVec.ofNat_add_ofNat]
    have e4 : scrP s₀ + BitVec.ofNat 64 (2048 + 8 * (index % 128) + 4) =
        scrP s₀ + BitVec.ofNat 64 (2048 + 8 * (index % 128) + 0) + BitVec.ofNat 64 4 := by
      rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    rw [vt, u₈.gpr, e4]
    exact (congrArg (BitVec.setWidth 64) (Mem.readW_hi32 w0)).trans (hi_ext _)

omit hp in
/-- The cached address block is that of `c`. -/
theorem cached {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) {c : Nat} (hc : 1 ≤ c) (hc' : c < 2 ^ 32)
    (he : lw s₀ s counterOff = BitVec.ofNat 64 c) :
    blockAt s.mem (scrP s₀ + BitVec.ofNat 64 2048) = addressBlock (prm s₀) pass lane slice c := by
  obtain ⟨c0, c1, c2 | ⟨_, c4⟩⟩ := h.cache
  · rw [he, c2] at c1
    have := congrArg BitVec.toNat c1
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at this
    exact absurd this (by simp; omega_arith)
  · rw [c4]
    rw [he] at c1
    have := congrArg BitVec.toNat c1
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith),
      Nat.mod_eq_of_lt (by omega_arith)] at this
    rw [this]

/-- `cacheCheck`: `r3 :=` the counter of the index's group; `a1` is zero if it is cached. -/
theorem cacheCheck_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (hi : index < (prm s₀).segmentLen) :
    WP isa (.block Impl.Argon2.RISCV64.Derive.cacheCheck) s fun t => FS s₀ pass slice lane index ctr st t ∧
      t.gpr .a0 = BitVec.ofNat 64 (index / 128 + 1) ∧
      VG.RISCV64.eval (.zero .a1) t =
        some (BitVec.ofNat 64 (index / 128 + 1) - lw s₀ t counterOff == 0) := by
  have sl := segLen_lt hp
  unfold Impl.Argon2.RISCV64.Derive.cacheCheck
  refine wp_ldloc h.inv (d := indexOff) (by decide) fun s₁ u₁ => wp_srl (by decide) fun s₂ u₂ =>
    wp_addi (by decide) fun s₃ u₃ => ?_
  have o₃ := ((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)
  have h₃ := h.of_only o₃
  have a₃ : s₃.gpr .a0 = BitVec.ofNat 64 (index / 128 + 1) := by
    rw [u₃.gpr, u₂.gpr, u₁.gpr, h.pos.index, shr7 (by omega_arith), BitVec.ofNat_add_ofNat]
  refine wp_ldloc h₃.inv (d := counterOff) (by decide) fun s₄ u₄ => wp_sub fun t u => WP.block_nil ?_
  have o₄ := (Only.of_upd u₄).trans (Only.of_upd u)
  refine ⟨h₃.of_only o₄, by rw [u.other _ (by decide), u₄.other _ (by decide), a₃], ?_⟩
  rw [VG.RISCV64.Wp.eval_zero, u.gpr, u₄.other _ (by decide), a₃, u₄.gpr, lw_mem u.mem,
    lw_mem u₄.mem]

/-- The address block of the index's group, regenerated unless it is cached. -/
theorem cacheFill_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h₄ : FS s₀ pass slice lane index ctr st s) (hi : index < (prm s₀).segmentLen)
    (a₃ : s.gpr .a0 = BitVec.ofNat 64 (index / 128 + 1))
    (z₄ : VG.RISCV64.eval (.zero .a1) s =
      some (BitVec.ofNat 64 (index / 128 + 1) - lw s₀ s counterOff == 0)) :
    WP isa (.ite (.zero .a1) (.block []) (.seq (.block [Impl.Argon2.RISCV64.Derive.st counterOff .a0])
      Impl.Argon2.RISCV64.Derive.addressCalls)) s fun t =>
      FS s₀ pass slice lane index (index / 128 + 1) st t ∧
      blockAt t.mem (scrP s₀ + BitVec.ofNat 64 2048) = addressBlock (prm s₀) pass lane slice (index / 128 + 1) := by
  have sl := segLen_lt hp
  refine WP.ite (BitVec.ofNat 64 (index / 128 + 1) - lw s₀ s counterOff == 0) z₄
    (fun hb => ?_) fun hb => ?_
  · have ce : lw s₀ s counterOff = BitVec.ofNat 64 (index / 128 + 1) := by
      have e := beq_iff_eq.mp hb
      exact ((BitVec.sub_eq_iff_eq_add.mp e).trans (by simp)).symm
    have cb := cached h₄ (c := index / 128 + 1) (by omega_arith) (by omega_arith) ce
    exact WP.block_nil ⟨⟨h₄.inv, h₄.pr, h₄.pos, ⟨by omega_arith, ce, .inr ⟨by omega_arith, cb⟩⟩, h₄.mem⟩, cb⟩
  · refine WP.seq (wp_stloc h₄.inv (d := counterOff) (by decide) fun s₅ i₅ v₅ o₅ g₅ m₅ => WP.block_nil ?_)
    have L₅ : ∀ d, 184 ≤ d → d + 8 ≤ 248 → (d + 8 ≤ counterOff ∨ counterOff + 8 ≤ d) →
        lw s₀ s₅ d = lw s₀ s d := fun d h₁ h₂ h₃ => o₅ d (by omega_arith) (by
          simp only [counterOff] at h₃ ⊢; omega_arith)
    have P₅ : Pos s₀ s₅ pass slice lane index :=
      ⟨by rw [L₅ _ (by decide) (by decide) (by decide)]; exact h₄.pos.pass,
        by rw [L₅ _ (by decide) (by decide) (by decide)]; exact h₄.pos.slice,
        by rw [L₅ _ (by decide) (by decide) (by decide)]; exact h₄.pos.lane,
        by rw [L₅ _ (by decide) (by decide) (by decide)]; exact h₄.pos.index⟩
    refine (addressCalls_ok hp i₅ (index := index) (c := index / 128 + 1) P₅ (by rw [v₅, a₃])).mono
      fun t ⟨it, _, ft, bt⟩ => ⟨?_, bt⟩
    have fsub : ∀ r ∈ [scrR s₀], ∃ r' ∈ [memR s₀, scrR s₀, outR s₀], Region.Sub r r' :=
      fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; simp, fun _ h => h⟩
    have Lt : ∀ d, d + 8 ≤ 320 → lw s₀ t d = lw s₀ s₅ d := fun d h₁ =>
      lw_keep hp ft fsub h₁
    refine ⟨it, Prm.of_lw h₄.pr fun d h₁ h₂ => ?_, ⟨?_, ?_, ?_, ?_⟩, ⟨by omega_arith,
      by rw [Lt _ (by decide), v₅, a₃], .inr ⟨by omega_arith, bt⟩⟩, Represents.keep h₄.mem fun k hk => ?_⟩
    · rw [Lt d (by omega_arith), L₅ d (by omega_arith) (by omega_arith) (by simp only [counterOff]; omega_arith)]
    · rw [Lt _ (by decide)]; exact P₅.pass
    · rw [Lt _ (by decide)]; exact P₅.slice
    · rw [Lt _ (by decide)]; exact P₅.lane
    · rw [Lt _ (by decide)]; exact P₅.index
    · have hk' : k < blocksN s₀ := by rw [hp.blocks]; exact hk
      have sk := Proof.Argon2.matrixCell_sub (memP s₀) _ _ hk'
      rw [blockAt_keep ft fun r hr => ?_, m₅, blockAt_keep (frame_loc _) fun r hr => ?_]
      · simp only [List.mem_singleton] at hr; subst hr
        exact (loc_disj hp (d := counterOff) (by decide) (memR s₀) (by simp)).symm.sub_left sk
      · simp only [List.mem_singleton] at hr; subst hr
        exact hp.mem_scr.sub_left sk

/-- `addressCache`: J₁ and J₂ from the address block of the index's group of 128. -/
theorem addressCache_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (hi : index < (prm s₀).segmentLen) :
    WP isa Impl.Argon2.RISCV64.Derive.addressCache s fun t =>
      FS s₀ pass slice lane index (index / 128 + 1) st t ∧
      Rand s₀ t ((addressBlock (prm s₀) pass lane slice (index / 128 + 1))[index % 128]'(Nat.mod_lt _ (by decide))) := by
  have sl := segLen_lt hp
  unfold Impl.Argon2.RISCV64.Derive.addressCache
  refine WP.seq ((cacheCheck_ok hp h hi).mono fun s₄ ⟨h₄, a₄, z₄⟩ => ?_)
  refine WP.seq ((cacheFill_ok hp h₄ hi a₄ z₄).mono fun t ⟨ht, bt⟩ =>
    (cacheWord_ok hp ht (by omega_arith)).mono fun u ⟨hu, wu⟩ => ⟨hu, ?_⟩)
  rw [bt] at wu
  exact wu

/-- `randomSource`: J₁ and J₂ are the step's random word. -/
theorem randomSource_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (hpass : pass < 2 ^ 32) (hl : lane < lanesN s₀)
    (hs : slice < 4) (hi : index < (prm s₀).segmentLen) :
    WP isa Impl.Argon2.RISCV64.Derive.randomSource s fun t =>
      FS s₀ pass slice lane index (ctrNext (prm s₀) pass slice index ctr) st t ∧
      Rand s₀ t (Proof.Argon2.FillStep.random (prm s₀) pass lane slice index st.memory) := by
  unfold Impl.Argon2.RISCV64.Derive.randomSource
  refine WP.seq ((addressMode_ok hp h.inv h.pos hpass hs).mono fun s₁ ⟨z₁, k₁⟩ => ?_)
  have h₁ := h.of_only k₁
  refine WP.ite (!Spec.Argon2.independent (prm s₀) pass slice) z₁ (fun hb => ?_) fun hb => ?_
  · have hind : Spec.Argon2.independent (prm s₀) pass slice = false := by simpa using hb
    refine (dependentWord_ok hp h₁ hl hs hi).mono fun t ⟨ht, wt⟩ => ⟨by rw [ctrNext, hind]; exact ht, ?_⟩
    have cl := Proof.Argon2.previous_cell_lt (prm s₀) hp.lanes_pos hp.memory_ge
      (column := slice * (prm s₀).segmentLen + index) hl
    rw [k₁.mem, h.mem.block _ cl] at wt
    rw [Proof.Argon2.FillStep.random, hind]
    simpa only [Bool.false_eq_true, ite_false] using wt
  · have hind : Spec.Argon2.independent (prm s₀) pass slice = true := by simpa using hb
    refine (addressCache_ok hp h₁ hi).mono fun t ⟨ht, wt⟩ => ⟨by rw [ctrNext, hind]; exact ht, ?_⟩
    rw [Proof.Argon2.FillStep.random, hind]
    simpa only [ite_true] using wt

end

end VG.Proof.Argon2.RISCV64.Derive
