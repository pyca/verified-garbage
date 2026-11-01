module

import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.HCall
public import VerifiedGarbage.Proof.Argon2.MemoryInit
public import VerifiedGarbage.Proof.Argon2.Matrix
import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.Initial
import VerifiedGarbage.Proof.Blake2.Stream
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.Locals
public import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.Parameters
public import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.Body
import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.Scratch
public import VerifiedGarbage.Proof.Argon2.Contract

/-!
# Argon2 on PPC64LE: the memory's initialization

`memoryInit_ok`: after `memoryInit`, the memory matrix represents
`initMemory` (`Proof.Argon2.Represents`). The matrix is cleared
(`clear_ok`), then each lane's first two blocks are H′ of the 72 bytes of
H′'s input in the frame (`initBlock_ok`), H₀ followed by the column and the
lane, written there just before the call. `LI s₀ h0 l` is the state after
`l` lanes (`initCell`).
-/

@[expose] public section

namespace VG.Proof.Argon2.PPC64LE.Derive

open VG VG.PPC64LE
open VG.Proof.MdStream.PPC64LE (Upd Mupd wp_add wp_sub wp_addi wp_subi wp_li wp_lsl wp_mov wp_std wp_stw)
open VG.Spec.Blake2 (bytesAt)
open VG.Spec.Argon2 (Block zeroBlock parseBlock)
open VG.Proof.Argon2 (matrixCell Represents initialBytes)
open VG.Impl.Argon2.PPC64LE.Derive (ld st lda ldw)

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
    have h0 : m a = 0 := by simpa using h 0 (by omega_arith)
    have h1 : m.read (a + 1) n = 0 := ih fun i hi => by
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
  have hdm := Nat.div_add_mod k p.laneLen
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
      have e' := congrArg BitVec.toNat e
      have z : (0 : BitVec 64).toNat = 0 := rfl
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, z] at e'
      omega_arith
    rw [bne_iff_ne.mpr hne]; simp [h]

/-! ## Clearing the matrix -/

/-- The loop's state after `j` doublewords. -/
structure CI (s₀ s₁ : State) (j : Nat) (s : State) : Prop where
  inv : Inv s₀ s
  r5 : s.gpr .r5 = memP s₀ + BitVec.ofNat 64 (8 * j)
  r6 : s.gpr .r6 = BitVec.ofNat 64 (blocksN s₀ * 128 - j)
  r7 : s.gpr .r7 = 0
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
    WP isa (.loop (.block Impl.Argon2.PPC64LE.Derive.clearWord) (.nonzero .d .r6)) s₁
      (CI s₀ s₁ (blocksN s₀ * 128)) := by
  have hm := hp.mem_fits
  have hb := blocks_lt hp
  have b1 := blocks_pos hp
  refine WP.loop (M := isa)
    (fun n s => ∃ j, n = blocksN s₀ * 128 - j ∧ j < blocksN s₀ * 128 ∧ CI s₀ s₁ j s)
    ?_ (blocksN s₀ * 128) s₁ ⟨0, by omega_arith, by omega_arith, h⟩
  rintro n s ⟨j, rfl, hj, c⟩
  have hc : (memR s₀).Contains (memP s₀ + BitVec.ofNat 64 (8 * j)) 8 :=
    Offset.contains_base _ (by omega_arith) (by omega_arith)
  simp only [Impl.Argon2.PPC64LE.Derive.clearWord]
  refine wp_std (a := memP s₀ + BitVec.ofNat 64 (8 * j)) (by decide) (by rw [c.r5]; simp)
    (by rw [c.inv.wr]; exact ⟨_, mem_mem hp, hc⟩) fun t₁ u₁ => ?_
  have i₁ := c.inv.mupd u₁ ((Frame.refl _ _).writeW (r := memR s₀) (by simp) _ hc)
  refine wp_addi (by decide) fun t₂ u₂ => wp_subi (by decide) fun t u => WP.block_nil ?_
  have i₃ := (i₁.upd u₂).upd u
  have e₁ : t.gpr .r6 = BitVec.ofNat 64 (blocksN s₀ * 128 - (j + 1)) := by
    rw [u.gpr, u₂.other _ (by decide), u₁.gpr, c.r6]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := blocksN s₀ * 128 - j) (by omega_arith)]
    omega_arith
  have next : CI s₀ s₁ (j + 1) t := by
    refine ⟨i₃, ?_, e₁, ?_, fun i hi => ?_, ?_⟩
    · rw [u.other _ (by decide), u₂.gpr, u₁.gpr, c.r5, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
        Nat.mul_succ]
    · rw [u.other _ (by decide), u₂.other _ (by decide), u₁.gpr, c.r7]
    · rw [u.mem, u₂.mem, u₁.mem, c.r7, writeW_zero]
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
  have z : VG.PPC64LE.eval (.nonzero .d .r6) t = some (!decide (blocksN s₀ * 128 - (j + 1) = 0)) := by
    rw [MdStream.PPC64LE.eval_nonzero, e₁, ← MdStream.PPC64LE.ofNat_beq_zero (by omega_arith)]
    rfl
  by_cases done : j + 1 = blocksN s₀ * 128
  · exact .inl ⟨by rw [z]; simp; omega_arith, done ▸ next⟩
  · exact .inr ⟨by rw [z]; simp; omega_arith, blocksN s₀ * 128 - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, next⟩

theorem clear_ok {s : State} (h : Inv s₀ s) :
    WP isa Impl.Argon2.PPC64LE.Derive.clear s fun t => Inv s₀ t ∧ Frame [memR s₀] s.mem t.mem ∧
      ∀ i < blocksN s₀ * 1024, t.mem (memP s₀ + BitVec.ofNat 64 i) = 0 := by
  have hb := blocks_lt hp
  unfold Impl.Argon2.PPC64LE.Derive.clear Impl.Argon2.PPC64LE.Derive.clearSetup
  refine WP.seq (wp_lda hp h (i := 13) (by decide) fun s₁ u₁ =>
    wp_lda hp (h.upd u₁) (i := 14) (by decide) fun s₂ u₂ => ?_)
  have i₂ := (h.upd u₁).upd u₂
  refine wp_lsl (by decide) fun s₃ u₃ => wp_li (by decide) fun s₄ u₄ => WP.block_nil ?_
  have i₄ := (i₂.upd u₃).upd u₄
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
/-- `stw r, d(r30)`, to LE32(column) or LE32(lane) in H′'s input. -/
theorem wp_stlocw {s : State} (h : Inv s₀ s) {d : Nat} (hd : 96 ≤ d ∧ d + 4 ≤ 104) {r : Reg}
    {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → t.mem = s.mem.writeW (E s₀ + BitVec.ofNat 64 d) ((s.gpr r).setWidth 32) →
      t.gpr = s.gpr → WP isa (.block is) t Q) :
    WP isa (.block (.store .w r .r30 d :: is)) s Q := by
  have hc : (inR s₀).Contains (E s₀ + BitVec.ofNat 64 d) 4 := by
    rw [E_add]; exact Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)
  refine wp_stw (a := E s₀ + BitVec.ofNat 64 d) (by omega_arith) (by rw [h.r30])
    (loc_in h (by omega_arith) (by omega_arith)) fun t u =>
      k t (h.mupd u ((Frame.refl _ _).writeW (r := inR s₀) (by simp) _ hc)) u.mem u.gpr

omit hp in
/-- The writes of `initBlock` before its call: two words of H′'s input. -/
theorem frame_words {m : Mem} (v w : BitVec 32) :
    Frame [⟨E s₀ + BitVec.ofNat 64 96, 8⟩] m
      ((m.writeW (E s₀ + BitVec.ofNat 64 96) v).writeW (E s₀ + BitVec.ofNat 64 100) w) :=
  ((Frame.refl _ m).writeW (w := 32) (List.mem_singleton_self _) v
    (Offset.contains _ (by decide) (by decide) (by decide))).writeW (w := 32)
    (List.mem_singleton_self _) w (Offset.contains _ (by decide) (by decide) (by decide))

omit hp in
/-- A doubleword of the frame outside `initBlock`'s two words is kept by them. -/
theorem readW_words {m : Mem} (v w : BitVec 32) {d : Nat} (h : d + 8 ≤ 96 ∨ 104 ≤ d)
    (hd : d + 8 ≤ 336) :
    ((m.writeW (E s₀ + BitVec.ofNat 64 96) v).writeW (E s₀ + BitVec.ofNat 64 100) w).readW
      (E s₀ + BitVec.ofNat 64 d) 64 = m.readW (E s₀ + BitVec.ofNat 64 d) 64 := by
  refine (frame_words v w).readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)

/-- The words of `initBlock` are outside the matrix, the frame's variables,
H₀ and `scratch`. -/
theorem words_disj :
    (∀ R ∈ [memR s₀, scrR s₀, outR s₀], Region.Disjoint ⟨E s₀ + BitVec.ofNat 64 96, 8⟩ R) ∧
    Region.Disjoint ⟨E s₀ + BitVec.ofNat 64 96, 8⟩ ⟨E s₀ + BitVec.ofNat 64 32, 64⟩ := by
  refine ⟨fun R hR => ?_, ?_⟩
  · rw [E_add]; exact stk_disj hp (by decide) R hR
  · exact Offset.disjoint _ (by decide) (by decide) (by decide)

/-- A cell of the memory matrix is outside `scratch` and the calls' frames. -/
theorem cell_disj {k : Nat} (hk : k < blocksN s₀) :
    ∀ r ∈ [scrR s₀, callR s₀], Region.Disjoint ⟨matrixCell (memP s₀) k, 1024⟩ r := by
  have sub : Region.Sub ⟨matrixCell (memP s₀) k, 1024⟩ (memR s₀) := Proof.Argon2.matrixCell_sub _ _ _ hk
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.mem_scr.sub_left sub
  · exact (call_disj hp (R := memR s₀) (by simp)).symm.sub_left sub

/-- Cells other than `k` are outside its region. -/
theorem cell_other {j k : Nat} (hj : j < blocksN s₀) (hk : k < blocksN s₀) (ne : j ≠ k) :
    Region.Disjoint ⟨matrixCell (memP s₀) j, 1024⟩ ⟨matrixCell (memP s₀) k, 1024⟩ :=
  Proof.Argon2.matrixCell_disjoint _ _ _ _ (by have := blocks_lt hp; omega_arith) hj hk ne

/-- H₀ in the frame is outside a call's writes. -/
theorem h0_call {O : Region} (hO : Region.Sub O (memR s₀) ∨ Region.Sub O (outR s₀)) :
    ∀ r ∈ [O, scrR s₀, callR s₀], Region.Disjoint ⟨E s₀ + BitVec.ofNat 64 32, 64⟩ r := by
  have sub : Region.Sub ⟨E s₀ + BitVec.ofNat 64 32, 64⟩ (inR s₀) := by
    rw [E_add]; exact Offset.sub _ (by decide) (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rcases hO with h | h
    · exact ((in_disj hp (R := memR s₀) (by simp)).sub_left sub).sub_right h
    · exact ((in_disj hp (R := outR s₀) (by simp)).sub_left sub).sub_right h
  · exact (in_disj hp (R := scrR s₀) (by simp)).sub_left sub
  · exact in_call.sub_left sub

omit hp in
/-- The frame's variables are outside a call's writes. -/
theorem lw_call {O : Region} (hO : Region.Sub O (memR s₀) ∨ Region.Sub O (outR s₀)) :
    ∀ r ∈ [O, scrR s₀, callR s₀], ∃ r' ∈ [memR s₀, scrR s₀, outR s₀, callR s₀], Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rcases hO with h | h
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

/-- Block `c < 2` of lane `l`: H′ of H₀, `c` and `l`. -/
theorem initBlock_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) {h0 : List Byte}
    (b0 : bytesAt s.mem (E s₀ + BitVec.ofNat 64 32) 64 = h0) {l c : Nat} (hl : l < lanesN s₀)
    (hc : c < 2) (r28 : s.gpr .r28 = BitVec.ofNat 64 l)
    (r29 : s.gpr .r29 = memP s₀ + BitVec.ofNat 64 ((l * (prm s₀).laneLen + c) * 1024)) :
    WP isa (Impl.Argon2.PPC64LE.Derive.initBlock c) s fun t => Inv s₀ t ∧ Prm s₀ t ∧
      bytesAt t.mem (E s₀ + BitVec.ofNat 64 32) 64 = h0 ∧ t.gpr .r28 = s.gpr .r28 ∧
      t.gpr .r29 = s.gpr .r29 ∧
      blockAt t.mem (matrixCell (memP s₀) (l * (prm s₀).laneLen + c)) =
        parseBlock (initialBytes h0 l c) ∧
      ∀ k < blocksN s₀, k ≠ l * (prm s₀).laneLen + c →
        blockAt t.mem (matrixCell (memP s₀) k) = blockAt s.mem (matrixCell (memP s₀) k) := by
  have hm := hp.mem_fits
  have hlt := hp.lanes_lt
  have L2 : 2 ≤ (prm s₀).laneLen := by rw [hp.laneLen_eq]; have := hp.segLen_two; omega_arith
  have hcell : l * (prm s₀).laneLen + c < blocksN s₀ := by
    rw [hp.blocks_eq]
    have := Nat.mul_le_mul_right (prm s₀).laneLen (show l + 1 ≤ lanesN s₀ by omega_arith)
    rw [Nat.succ_mul] at this
    omega_arith
  have sO : Region.Sub ⟨matrixCell (memP s₀) (l * (prm s₀).laneLen + c), 1024⟩ (memR s₀) :=
    Proof.Argon2.matrixCell_sub _ _ _ hcell
  unfold Impl.Argon2.PPC64LE.Derive.initBlock
  refine WP.seq (wp_li (by omega_arith) fun s₁ u₁ => ?_)
  have i₁ := h.upd u₁
  refine wp_stlocw i₁ (d := 96) (by decide) fun s₂ i₂ m₂ g₂ => ?_
  refine wp_stlocw i₂ (d := 100) (by decide) fun s₃ i₃ m₃ g₃ => ?_
  refine wp_addi (by decide) fun s₄ u₄ => wp_li (by decide) fun s₅ u₅ =>
    wp_mov fun s₆ u₆ => wp_li (by decide) fun s₇ u₇ => wp_mov fun s₈ u₈ => WP.block_nil ?_
  have i₈ := ((((i₃.upd u₄).upd u₅).upd u₆).upd u₇).upd u₈
  have m₈ : s₈.mem = s₃.mem := by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  have g₈ : ∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → s₈.gpr r = s.gpr r :=
    fun r a b d e f => by
      rw [u₈.other _ f, u₇.other _ e, u₆.other _ d, u₅.other _ b, u₄.other _ a, g₃, g₂, u₁.other _ a]
  have r3₈ : s₈.gpr .r3 = E s₀ + BitVec.ofNat 64 32 := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.gpr, g₃, g₂, i₁.r30]; rfl
  have r4₈ : (s₈.gpr .r4).toNat = 72 := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr]; rfl
  have r6₈ : (s₈.gpr .r6).toNat = 1024 := by rw [u₈.other _ (by decide), u₇.gpr]; rfl
  have r5₈ : s₈.gpr .r5 = matrixCell (memP s₀) (l * (prm s₀).laneLen + c) := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide),
      u₄.other _ (by decide), g₃, g₂, u₁.other _ (by decide), r29]; rfl
  have r7₈ : s₈.gpr .r7 = scrP s₀ := by
    rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), g₃, g₂, i₁.r31]
  have hcell' : (l * (prm s₀).laneLen + c) * 1024 + 1024 ≤ blocksN s₀ * 1024 := by omega_arith
  refine hcall_ok hp i₈ r7₈
    ⟨inR s₀, by simp, 0, by rw [r3₈, E_add]; simp, by rw [r4₈]⟩
    ⟨memR s₀, by simp, (l * (prm s₀).laneLen + c) * 1024, by rw [r5₈]; rfl, by rw [r6₈]; exact hcell'⟩
    (by rw [r4₈]; decide) (by rw [r6₈]; decide)
    fun t it cs fr post => ⟨it, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have sO' : Region.Sub ⟨s₈.gpr .r5, (s₈.gpr .r6).toNat⟩ (memR s₀) := by rw [r5₈, r6₈]; exact sO
    exact Prm.of_lw pr fun d h₁ h₂ => by
      rw [lw_keep hp fr (lw_call (.inl sO')) (by omega_arith) (by omega_arith), lw_mem m₈]
      show s₃.mem.readW _ 64 = _
      rw [m₃, m₂, readW_words _ _ (.inr (by omega_arith)) (by omega_arith), u₁.mem]
  · rw [bytes_keep fr (h0_call hp (.inl (by rw [r5₈, r6₈]; exact sO))) (by decide), m₈, m₃, m₂,
      bytes_keep (frame_words _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (words_disj hp).2.symm) (by decide),
      u₁.mem, b0]
  · rw [cs .r28 (by decide), g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  · rw [cs .r29 (by decide), g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  · refine Proof.Argon2.blockAt_of_initialBytes _ _ _ _ _ ?_
    rw [← r5₈, show (1024 : Nat) = (s₈.gpr .r6).toNat from r6₈.symm, post, r6₈, r3₈, r4₈, bytes72, m₈]
    have w96 : s₃.mem.readW (E s₀ + BitVec.ofNat 64 32 + BitVec.ofNat 64 64) 32 =
        BitVec.ofNat 32 c := by
      rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, m₃, Mem.readW_writeW_sep
        (Offset.sep _ (by decide) (by decide) (by decide)) (by decide), m₂, Mem.readW_writeW_self32,
        u₁.gpr, setWidth_ofNat]
    have w100 : s₃.mem.readW (E s₀ + BitVec.ofNat 64 32 + BitVec.ofNat 64 68) 32 =
        BitVec.ofNat 32 l := by
      rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, m₃, Mem.readW_writeW_self32, g₂,
        u₁.other _ (by decide), r28, setWidth_ofNat]
    rw [w96, w100, m₃, m₂, bytes_keep (frame_words _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (words_disj hp).2.symm) (by decide),
      u₁.mem, b0]
    rfl
  · intro k hk ne
    have sk := Proof.Argon2.matrixCell_sub (memP s₀) _ _ hk
    rw [blockAt_keep fr (fun r hr => ?_), m₈, m₃, m₂, blockAt_keep (frame_words _ _) (fun r hr => ?_),
      u₁.mem]
    · simp only [List.mem_singleton] at hr; subst hr
      exact ((words_disj hp).1 (memR s₀) (by simp)).symm.sub_left sk
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [r5₈, r6₈]; exact cell_other hp hk hcell ne
      · exact cell_disj hp hk _ (by simp)
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
  b0 : bytesAt s.mem (E s₀ + BitVec.ofNat 64 32) 64 = h0
  r28 : s.gpr .r28 = BitVec.ofNat 64 l
  r29 : s.gpr .r29 = memP s₀ + BitVec.ofNat 64 (l * (prm s₀).laneLen * 1024)
  cells : ∀ k < blocksN s₀, blockAt s.mem (matrixCell (memP s₀) k) = initCell (prm s₀) h0 l k

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem lane_ok {h0 : List Byte} {l : Nat} {s : State} (hl : l < lanesN s₀) (h : LI s₀ h0 l s) :
    WP isa Impl.Argon2.PPC64LE.Derive.initLane s fun t =>
      LI s₀ h0 (l + 1) t ∧ VG.PPC64LE.eval (.nonzero .d .r3) t = some (!decide (l + 1 = lanesN s₀)) := by
  have L2 : 2 ≤ (prm s₀).laneLen := by rw [hp.laneLen_eq]; have := hp.segLen_two; omega_arith
  have hlt := hp.lanes_lt
  have hll : (prm s₀).laneLen ≤ mcostN s₀ :=
    Nat.le_trans (Nat.le_trans (Nat.le_mul_of_pos_left _ hp.lanes_pos) (Nat.le_of_eq hp.blocks_eq.symm))
      hp.blocks_le
  have hm := mcost_lt s₀
  unfold Impl.Argon2.PPC64LE.Derive.initLane
  refine WP.seq ((initBlock_ok hp h.inv h.pr h.b0 hl (c := 0) (by decide) h.r28
    (by rw [h.r29, Nat.add_zero])).mono fun s₁ ⟨i₁, p₁, b₁, e₁, d₁, w₁, o₁⟩ => ?_)
  refine WP.seq (wp_addi (by decide) fun s₂ u₂ => WP.block_nil ?_)
  have i₂ := i₁.upd u₂
  refine WP.seq ((initBlock_ok hp i₂ (p₁.of_mem u₂.mem) (h0 := h0) (by rw [u₂.mem]; exact b₁) hl (c := 1)
    (by decide) (by rw [u₂.other _ (by decide), e₁, h.r28])
    (by rw [u₂.gpr, d₁, h.r29, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_mul])).mono
    fun s₃ ⟨i₃, p₃, b₃, e₃, d₃, w₃, o₃⟩ => ?_)
  simp only [Impl.Argon2.PPC64LE.Derive.nextLane]
  refine wp_ldloc i₃ (d := Impl.Argon2.PPC64LE.Derive.strideOff) (by decide) fun s₄ u₄ =>
    wp_add fun s₅ u₅ => wp_subi (by decide) fun s₆ u₆ => wp_addi (by decide) fun s₇ u₇ => ?_
  have i₇ := (((i₃.upd u₄).upd u₅).upd u₆).upd u₇
  refine wp_ldw hp i₇ (i := 7) (by decide) fun s₈ u₈ => wp_sub fun t u => WP.block_nil ?_
  have i₈ := (i₇.upd u₈).upd u
  have mt : t.mem = s₃.mem := by rw [u.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  have r28t : t.gpr .r28 = BitVec.ofNat 64 (l + 1) := by
    rw [u.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), e₃, u₂.other _ (by decide), e₁, h.r28,
      BitVec.ofNat_add]
  refine ⟨⟨i₈, p₃.of_mem mt, by rw [mt, b₃], r28t, ?_, fun k hk => ?_⟩, ?_⟩
  · rw [u.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.gpr,
      u₄.gpr, u₄.other _ (by decide), d₃, u₂.gpr, d₁, h.r29, p₃.stride, r29_next,
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
  · have r28₈ : s₈.gpr .r28 = BitVec.ofNat 64 (l + 1) := by
      rw [← r28t, u.other _ (by decide)]
    have lanes : (arg32 s₀ 7).setWidth 64 = BitVec.ofNat 64 (lanesN s₀) := ofNat_toNat (toNat_ext32 _)
    rw [MdStream.PPC64LE.eval_nonzero, u.gpr, r28₈, u₈.gpr, lanes, ofNat_sub_beq (by omega_arith) (by omega_arith)]

end

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `clear`, from the body with H₀ in the frame. -/
theorem clearW_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) {h0 : List Byte}
    (b0 : bytesAt s.mem (E s₀ + BitVec.ofNat 64 32) 64 = h0) :
    WP isa Impl.Argon2.PPC64LE.Derive.clear s fun t => Inv s₀ t ∧ Prm s₀ t ∧
      bytesAt t.mem (E s₀ + BitVec.ofNat 64 32) 64 = h0 ∧ ∀ i < blocksN s₀ * 1024,
        t.mem (memP s₀ + BitVec.ofNat 64 i) = 0 := by
  refine (clear_ok hp h).mono fun s₁ ⟨i₁, f₁, z₁⟩ => ⟨i₁, ?_, ?_, z₁⟩
  · have fsub : ∀ r ∈ [memR s₀], ∃ r' ∈ [memR s₀, scrR s₀, outR s₀, callR s₀], Region.Sub r r' :=
      fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; simp, fun _ h => h⟩
    exact Prm.of_lw pr fun d h₁ h₂ => lw_keep hp f₁ fsub (by omega_arith) (by omega_arith)
  · rw [bytes_keep f₁ (fun r hr => ?_) (by omega_arith), b0]
    simp only [List.mem_singleton] at hr; subst hr
    have sub : Region.Sub ⟨E s₀ + BitVec.ofNat 64 32, 64⟩ (inR s₀) := by
      rw [E_add]; exact Offset.sub _ (by decide) (by decide)
    exact (in_disj hp (R := memR s₀) (by simp)).sub_left sub

/-- The first lane's first block, after `clear`. -/
theorem laneStart_ok {s : State} {h0 : List Byte} (h : Inv s₀ s ∧ Prm s₀ s ∧
      bytesAt s.mem (E s₀ + BitVec.ofNat 64 32) 64 = h0 ∧ ∀ i < blocksN s₀ * 1024,
        s.mem (memP s₀ + BitVec.ofNat 64 i) = 0) :
    WP isa (.block [lda .r29 Impl.Argon2.PPC64LE.Derive.memoryArg, .li .r28 0]) s (LI s₀ h0 0) := by
  obtain ⟨i₁, p₁, b₁, z₁⟩ := h
  refine wp_lda hp i₁ (i := 13) (by decide) fun s₂ u₂ => wp_li (by decide) fun s₃ u₃ =>
    WP.block_nil ?_
  have i₃ := (i₁.upd u₂).upd u₃
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem]
  refine ⟨i₃, p₁.of_mem m₃, by rw [m₃]; exact b₁, u₃.gpr, ?_, fun k hk => ?_⟩
  · rw [u₃.other _ (by decide), u₂.gpr]; simp
  · rw [initCell_zero, m₃]
    refine blockAt_zero fun i hi => ?_
    rw [matrixCell, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact z₁ _ (by omega_arith)

theorem memoryInit_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) {h0 : List Byte}
    (b0 : bytesAt s.mem (E s₀ + BitVec.ofNat 64 32) 64 = h0) :
    WP isa Impl.Argon2.PPC64LE.Derive.memoryInit s fun t => Inv s₀ t ∧ Prm s₀ t ∧
      Represents t.mem (memP s₀) (prm s₀).blocks (Spec.Argon2.initMemory (prm s₀) h0).memory := by
  have hlt := hp.lanes_lt
  have hl1 := hp.lanes_pos
  unfold Impl.Argon2.PPC64LE.Derive.memoryInit
  refine WP.seq ((clearW_ok hp h pr b0).mono fun s₁ h₁ =>
    WP.seq ((laneStart_ok hp h₁).mono fun s₃ start => ?_))
  refine WP.loop (M := isa) (fun n t => ∃ l, n = lanesN s₀ - l ∧ l < lanesN s₀ ∧ LI s₀ h0 l t) ?_
    (lanesN s₀) s₃ ⟨0, by omega_arith, by omega_arith, start⟩
  rintro n t ⟨l, rfl, hl, ht⟩
  refine (lane_ok hp hl ht).mono fun u ⟨hu, cu⟩ => ?_
  by_cases done : l + 1 = lanesN s₀
  · refine .inl ⟨cu.trans (by simp [done]), hu.inv, hu.pr, ?_⟩
    refine ⟨Proof.Argon2.initMemory_size _ _, fun k hk => ?_⟩
    have hk' : k < blocksN s₀ := by rw [hp.blocks]; exact hk
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

end VG.Proof.Argon2.PPC64LE.Derive
