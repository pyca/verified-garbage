module

public import VerifiedGarbage.Proof.Sha1.RISCV64.Rounds
public meta import VerifiedGarbage.Proof.Sha1.RISCV64.Rounds
public import VerifiedGarbage.Proof.Sha1.RISCV64.Contract
public meta import VerifiedGarbage.Proof.Sha1.RISCV64.Contract
public import VerifiedGarbage.Proof.Sha1.StateMem
public meta import VerifiedGarbage.Proof.Sha1.StateMem
public import VerifiedGarbage.Proof.Framework.RISCV64.Align
public meta import VerifiedGarbage.Proof.Framework.RISCV64.Align
import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.Range
import all Init.Data.Nat.Bitwise.Basic
public import VerifiedGarbage.Proof.Framework.Contract
public meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RISCV64.Inline
public meta import VerifiedGarbage.Proof.Framework.RISCV64.Inline
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Semantics
public meta import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.RISCV64.Target
public meta import VerifiedGarbage.TCB.RISCV64.Target

/-!
# SHA-1 compression function on RISC-V: the whole function

Untrusted: everything here is checked by Lean. The structure of the SHA-256
proof (`Proof/Sha256/RISCV64/Compress.lean`), with the hash value read and
written a byte at a time (`Proof/Framework/RISCV64/ByteLoad.lean`), the
scratch space rounded up to a multiple of 8 first
(`Proof/Framework/RISCV64/Align.lean`), and no saved register.
-/

@[expose] public section

namespace VG.Proof.Sha1.RISCV64

open VG VG.RISCV64 VG.RISCV64.ByteLoad VG.RISCV64.Align VG.Impl.Sha1.RISCV64 VG.Impl.Words.RISCV64
open VG.Spec.Sha1 (HashValue Word Block W stateAt blockAt compressBlocks compress parseBlock)
open VG.Proof.Sha1.StateMem (readW_writeW_word stateAt_eq stateAt_get)
open VG.Proof.Sha1 (W_lt)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .a0
abbrev bp : Addr := s₀.gpr .a1
abbrev nb : Nat := (s₀.gpr .a2).toNat
abbrev scr₀ : Addr := s₀.gpr .a3
/-- The scratch space, rounded up to a multiple of 8. -/
abbrev scr : Addr := scr₀ s₀ + BitVec.ofNat 64 (pad (scr₀ s₀))
abbrev stR : Region := ⟨st s₀, 20⟩
abbrev blR : Region := ⟨bp s₀, 64 * nb s₀⟩
abbrev scrR : Region := ⟨scr₀ s₀, 80⟩
abbrev H₀ : HashValue := stateAt s₀.mem (st s₀)

/-- Block `i`, and where it starts. -/
abbrev blkAddr (i : Nat) : Addr := bp s₀ + BitVec.ofNat 64 (64 * i)
abbrev blk (i : Nat) : Block := blockAt s₀.mem (blkAddr s₀ i)

end

/-- An offset of the rounded scratch space, as one of `scratch`. -/
theorem scr_add (s₀ : State) (d : Nat) :
    scr s₀ + BitVec.ofNat 64 d = scr₀ s₀ + BitVec.ofNat 64 (pad (scr₀ s₀) + d) := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]

theorem scr_contains (s₀ : State) {d n : Nat} (h : d + n ≤ 72) :
    (scrR s₀).Contains (scr s₀ + BitVec.ofNat 64 d) n := by
  rw [scr_add]
  have := pad_lt (scr₀ s₀)
  exact Offset.contains_base _ (by omega) (by omega)

theorem scr_sub (s₀ : State) {d n : Nat} (h : d + n ≤ 72) :
    Region.Sub ⟨scr s₀ + BitVec.ofNat 64 d, n⟩ (scrR s₀) := by
  rw [scr_add]
  have := pad_lt (scr₀ s₀)
  exact Offset.sub_base _ (by omega)

theorem win_sub (s₀ : State) : Region.Sub (winRegion (scr s₀)) (scrR s₀) := by
  have := scr_sub s₀ (d := 0) (n := 64) (by omega)
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [blR s₀]
  wr : s₀.wr = [stR s₀, scrR s₀]
  st_scr : (stR s₀).Disjoint (scrR s₀)
  blk_st : (blR s₀).Disjoint (stR s₀)
  blk_scr : (blR s₀).Disjoint (scrR s₀)

theorem pre_of (s₀ : State) (h : Proof.Sha1.compressRISCV64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

theorem nb_lt : 64 * nb s₀ < 2 ^ 64 := by
  by_contra hn
  refine h.blk_st (st s₀) ?_ (by simp [Region.Contains])
  simp only [Region.Contains]
  have := (st s₀ - bp s₀).isLt
  omega

theorem in_state {k : Nat} (hk : k < 5) :
    InRegions (s₀.rd ++ s₀.wr) (st s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨stR s₀, by simp [h.wr], Offset.contains_base _ (by omega) (by omega)⟩

theorem out_state {k : Nat} (hk : k < 5) :
    InRegions s₀.wr (st s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨stR s₀, by simp [h.wr], Offset.contains_base _ (by omega) (by omega)⟩

theorem in_slot (j : Nat) : InRegions (s₀.rd ++ s₀.wr) (slotAddr (scr s₀) j) 4 :=
  ⟨scrR s₀, by simp [h.wr], scr_contains s₀ (by simp only [slot]; omega)⟩

theorem out_slot (j : Nat) : InRegions s₀.wr (slotAddr (scr s₀) j) 4 :=
  ⟨scrR s₀, by simp [h.wr], scr_contains s₀ (by simp only [slot]; omega)⟩

theorem blk_contains {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    (blR s₀).Contains (blkAddr s₀ i + BitVec.ofNat 64 (4 * t)) 4 := by
  have := h.nb_lt
  rw [show blkAddr s₀ i + BitVec.ofNat 64 (4 * t) =
    bp s₀ + BitVec.ofNat 64 (64 * i + 4 * t) by rw [BitVec.ofNat_add, BitVec.add_assoc]]
  exact Offset.contains_base _ (by omega) (by omega)

theorem in_blk {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr s₀ i + BitVec.ofNat 64 (4 * t)) 4 :=
  ⟨blR s₀, by simp [h.rd], h.blk_contains hi ht⟩

end Pre

/-! ## The loop invariant -/

theorem preserved_pub : ∀ r ∈ preserved, r ∈ pubRegs := by decide

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  a0 : s.gpr .a0 = st s₀
  a3 : s.gpr .a3 = scr s₀
  kept : ∀ r ∈ pubRegs, r ≠ .a1 → r ≠ .a2 → r ≠ .a3 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR s₀, scrR s₀] s₀.mem s.mem
  state : stateAt s.mem (st s₀) = compressBlocks (H₀ s₀) s₀.mem (bp s₀) i

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  a1 : s.gpr .a1 = blkAddr s₀ i
  a2 : s.gpr .a2 = BitVec.ofNat 64 (nb s₀ - i)

/-! ## Loading the MD buffer -/

theorem var0_inj {j k : Nat} (hj : j < 5) (hk : k < 5) (h : var 0 j = var 0 k) : j = k := by
  have key : ∀ j < 5, ∀ k < 5, var 0 j = var 0 k → j = k := by decide
  exact key j hj k hk h

theorem var0_ne {k : Nat} (hk : k < 5) : var 0 k ≠ .a0 ∧ var 0 k ≠ T0 ∧ var 0 k ≠ T1 := by
  have key : ∀ k < 5, var 0 k ≠ .a0 ∧ var 0 k ≠ T0 ∧ var 0 k ≠ T1 := by decide
  exact key k hk

theorem var0_pub {k : Nat} (hk : k < 5) : ∀ r ∈ pubRegs, r ≠ var 0 k := by
  have key : ∀ k < 5, ∀ r ∈ pubRegs, r ≠ var 0 k := by decide
  exact key k hk

/-- The first `k` words of the MD buffer are loaded. -/
structure LdI (s₁ : State) (k : Nat) (s : State) : Prop where
  vars : ∀ j < k, (s.gpr (var 0 j)).setWidth 32 = (stateAt s₁.mem (s₁.gpr .a0))[j]!
  pub : ∀ r ∈ pubRegs, s.gpr r = s₁.gpr r
  mem : s.mem = s₁.mem
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr

theorem load_step {s₀ s₁ : State} (hp : Pre s₀) (hr0 : s₁.gpr .a0 = st s₀) (hrd : s₁.rd = s₀.rd)
    (hwr : s₁.wr = s₀.wr) {k : Nat} (hk : k < 5) {s : State} (h : LdI s₁ k s) :
    WP isa (.block (loadLE32 (var 0 k) T0 .a0 (4 * k))) s (LdI s₁ (k + 1)) := by
  have ne := var0_ne hk
  have h0 : s.gpr .a0 = st s₀ := (h.pub .a0 (by decide)).trans hr0
  refine WP.mono (loadLE32_ok ne.1 (by decide) ne.2.1 (by omega)
    (by rw [h.rd, h.wr, hrd, hwr, h0]; exact hp.in_state hk)) fun s' e => ?_
  subst e
  refine ⟨fun j hj => ?_, fun r hr => ?_, h.mem, h.rd, h.wr⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [RegUpd.gpr_write_of_ne _ _ (fun e => absurd (var0_inj (by omega) hk e) (by omega)),
        RegUpd.gpr_write_of_ne _ _ (var0_ne (by omega : j < 5)).2.1]
      exact h.vars j hj
    · rw [RegUpd.gpr_write_self, lo32_ext, h.mem, h0, ← hr0, getElem!_pos _ j hk,
        stateAt_get _ _ hk]
  · rw [RegUpd.gpr_write_of_ne _ _ (var0_pub hk r hr),
      RegUpd.gpr_write_of_ne _ _ fun e => (pubRegs_ne' r hr).1 e]
    exact h.pub r hr

theorem load_ok {s₀ : State} (hp : Pre s₀) {s : State} (hr0 : s.gpr .a0 = st s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block load) s fun s₁ =>
      Vars 0 s₁ (stateAt s.mem (st s₀)) ∧ (∀ r ∈ pubRegs, s₁.gpr r = s.gpr r) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.mem = s.mem := by
  refine WP.mono (wp_range_flatMap (M := isa) (LdI s) (fun k s' hk h => load_step hp hr0 hrd hwr hk h)
    5 (Nat.le_refl _) s ⟨fun _ h => absurd h (by omega), fun _ _ => rfl, rfl, rfl, rfl⟩)
    fun s₁ h => ⟨?_, h.pub, h.rd, h.wr, h.mem⟩
  have v := h.vars
  rw [hr0] at v
  exact ⟨v 0 (by decide), v 1 (by decide), v 2 (by decide), v 3 (by decide), v 4 (by decide)⟩

/-! ## Adding the MD buffer into the words -/

/-- The first `k` of five words `f` written at `p`. -/
def writeUpTo (m : Mem) (p : Addr) (f : HashValue) (k : Nat) : Mem :=
  (List.range k).foldl (fun m j => m.writeW (p + BitVec.ofNat 64 (4 * j)) f[j]!) m

theorem writeUpTo_succ (m : Mem) (p : Addr) (f : HashValue) (k : Nat) :
    writeUpTo m p f (k + 1) = (writeUpTo m p f k).writeW (p + BitVec.ofNat 64 (4 * k)) f[k]! := by
  simp [writeUpTo, List.range_succ, List.foldl_append]

theorem readW_writeUpTo (m : Mem) (p : Addr) (f : HashValue) {k j : Nat} (hk : k ≤ 5) (hj : j < 5) :
    (writeUpTo m p f k).readW (p + BitVec.ofNat 64 (4 * j)) 32 =
      if j < k then f[j]! else m.readW (p + BitVec.ofNat 64 (4 * j)) 32 := by
  induction k with
  | zero => simp [writeUpTo]
  | succ k ih =>
    rw [writeUpTo_succ]
    by_cases hjk : j = k
    · subst hjk; rw [Mem.readW_writeW_self32]; simp
    · rw [readW_writeW_word _ _ _ hj (by omega) hjk, ih (by omega)]
      by_cases h : j < k
      · simp [h, show j < k + 1 by omega]
      · simp [h, show ¬ j < k + 1 by omega]

theorem frame_writeUpTo {r : Region} {m : Mem} {p : Addr} (f : HashValue) {k : Nat} (hk : k ≤ 5)
    (hc : ∀ j < 5, r.Contains (p + BitVec.ofNat 64 (4 * j)) 4) :
    Frame [r] m (writeUpTo m p f k) := by
  induction k with
  | zero => exact Frame.refl _ _
  | succ k ih =>
    rw [writeUpTo_succ]
    exact (ih (by omega)).writeW (List.mem_singleton_self _) _ (hc k (by omega))

/-- The first `k` words are updated, from the state `s₂` after the
operations, whose words are `V`, and the MD buffer `H` it holds. -/
structure UInv (s₀ s₂ : State) (V H : HashValue) (k : Nat) (s : State) : Prop where
  vars : ∀ j, k ≤ j → j < 5 → (s.gpr (var 0 j)).setWidth 32 = V[j]!
  pub : ∀ r ∈ pubRegs, s.gpr r = s₂.gpr r
  mem : s.mem = writeUpTo s₂.mem (st s₀) (Vector.zipWith (· + ·) V H) k
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr

theorem update_step {s₀ s₂ : State} (hp : Pre s₀) (V H : HashValue) (hr0 : s₂.gpr .a0 = st s₀)
    (hrd : s₂.rd = s₀.rd) (hwr : s₂.wr = s₀.wr)
    (hH : ∀ j < 5, s₂.mem.readW (st s₀ + BitVec.ofNat 64 (4 * j)) 32 = H[j]!)
    {k : Nat} (hk : k < 5) {s : State} (h : UInv s₀ s₂ V H k s) :
    WP isa (.block (updateW k)) s (UInv s₀ s₂ V H (k + 1)) := by
  have ne := var0_ne hk
  have h0 : s.gpr .a0 = st s₀ := (h.pub .a0 (by decide)).trans hr0
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .a0 + BitVec.ofNat 64 (4 * k)) 4 := by
    rw [h.rd, h.wr, hrd, hwr, h0]; exact hp.in_state hk
  unfold updateW
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (loadLE32_ok (by decide) (by decide) (by decide) (by omega) hin) fun s₁ e₁ => ?_
  subst e₁
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_add, Option.some.injEq,
    exists_eq_left']
  -- The state after the addition.
  generalize hs₂' : State.write _ _ _ = s₃
  have g0 : s₃.gpr .a0 = st s₀ := by
    rw [← hs₂', RegUpd.gpr_write_of_ne _ _ (Ne.symm ne.1), RegUpd.gpr_write_of_ne _ _ (by decide),
      RegUpd.gpr_write_of_ne _ _ (by decide), h0]
  have gv : (s₃.gpr (var 0 k)).setWidth 32 = V[k]! + H[k]! := by
    rw [← hs₂', RegUpd.gpr_write_self, lo32_add, RegUpd.gpr_write_of_ne _ _ ne.2.1,
      RegUpd.gpr_write_of_ne _ _ ne.2.2, h.vars k (Nat.le_refl _) hk, RegUpd.gpr_write_self, lo32_ext,
      h0, h.mem, readW_writeUpTo _ _ _ (by omega) hk]
    simp only [Nat.lt_irrefl, ite_false]
    rw [hH k hk]
  have gm : s₃.mem = s.mem := by rw [← hs₂']; rfl
  have gwr : s₃.wr = s.wr := by rw [← hs₂']; rfl
  have grd : s₃.rd = s.rd := by rw [← hs₂']; rfl
  have gr : ∀ r, r ≠ var 0 k → r ≠ T0 → r ≠ T1 → s₃.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [← hs₂', RegUpd.gpr_write_of_ne _ _ h1, RegUpd.gpr_write_of_ne _ _ h2,
      RegUpd.gpr_write_of_ne _ _ h3]
  refine WP.mono (storeLE32_ok (Ne.symm ne.2.1) (by decide) (by omega)
    (by rw [gwr, h.wr, hwr, g0]; exact hp.out_state hk)) fun s₄ e₄ => ?_
  subst e₄
  refine ⟨fun j hj hj' => ?_, fun r hr => ?_, ?_, grd.trans h.rd, gwr.trans h.wr⟩
  · have hne : var 0 j ≠ var 0 k := fun e => absurd (var0_inj hj' hk e) (by omega)
    rw [RegUpd.gpr_write_of_ne _ _ (var0_ne hj').2.1]
    show (s₃.gpr (var 0 j)).setWidth 32 = _
    rw [gr _ hne (var0_ne hj').2.1 (var0_ne hj').2.2]
    exact h.vars j (by omega) hj'
  · rw [RegUpd.gpr_write_of_ne _ _ fun e => (pubRegs_ne' r hr).1 e]
    show s₃.gpr r = _
    rw [gr r (var0_pub hk r hr) (fun e => (pubRegs_ne' r hr).1 e) (fun e => (pubRegs_ne' r hr).2.1 e)]
    exact h.pub r hr
  · rw [RegUpd.mem_write]
    show s₃.mem.writeW _ _ = _
    rw [gm, h.mem, writeUpTo_succ, g0, gv]
    congr 1
    rw [getElem!_pos (Vector.zipWith _ V H) k hk, Vector.getElem_zipWith, getElem!_pos V k hk,
      getElem!_pos H k hk]

theorem vars_get {s : State} {V : HashValue} (h : Vars 0 s V) :
    ∀ j, j < 5 → (s.gpr (var 0 j)).setWidth 32 = V[j]! := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  intro j hj
  rw [getElem!_pos V j hj]
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 by omega) with rfl | rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3, h4]

theorem update_ok {s₀ s₂ : State} (hp : Pre s₀) (V H : HashValue) (hv : Vars 0 s₂ V)
    (hr0 : s₂.gpr .a0 = st s₀) (hrd : s₂.rd = s₀.rd) (hwr : s₂.wr = s₀.wr)
    (hH : ∀ j < 5, s₂.mem.readW (st s₀ + BitVec.ofNat 64 (4 * j)) 32 = H[j]!) :
    WP isa (.block ((List.range 5).flatMap updateW)) s₂ (UInv s₀ s₂ V H 5) :=
  wp_range_flatMap (M := isa) (UInv s₀ s₂ V H) (fun _ _ hk h => update_step hp V H hr0 hrd hwr hH hk h)
    5 (Nat.le_refl _) s₂ ⟨fun j _ hj => vars_get hv j hj, fun _ _ => rfl, rfl, rfl, rfl⟩

/-! ## One block -/

theorem compressBlocks_succ (H : HashValue) (m : Mem) (p : Addr) (i : Nat) :
    compressBlocks H m p (i + 1) =
      compress (compressBlocks H m p i) (blockAt m (p + BitVec.ofNat 64 (64 * i))) := by
  simp [compressBlocks, List.range_succ, List.foldl_append]

theorem blk_word {s₀ : State} (i t : Nat) (ht : t < 16) :
    beWord s₀.mem (blkAddr s₀ i) (4 * t) = W (blk s₀ i) t := by
  rw [W_lt _ ht]; rfl

theorem frame_byte {rs : List Region} {m m' : Mem} {R : Region} {x : Addr} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, R.Disjoint r) (hx : R.Contains x 1) : m' x = m x :=
  hf x fun r hr hc => hd r hr x hx hc

theorem frame_beWord {rs : List Region} {m m' : Mem} {R : Region} {p : Addr} {off : Nat}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, R.Disjoint r) (hc : R.Contains (p + BitVec.ofNat 64 off) 4) :
    beWord m' p off = beWord m p off := by
  have h0 := contains_byte hc (k := 0) (by decide)
  rw [Nat.add_zero] at h0
  simp only [beWord, frame_byte hf hd h0, frame_byte hf hd (contains_byte hc (k := 1) (by decide)),
    frame_byte hf hd (contains_byte hc (k := 2) (by decide)),
    frame_byte hf hd (contains_byte hc (k := 3) (by decide))]

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval (.nonzero .a2) s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval (.nonzero .a2) s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  refine WP.seq (WP.mono (load_ok hp hL.a0 hL.rd hL.wr) fun s₁ ⟨hv₁, hpub₁, hrd₁, hwr₁, hm₁⟩ => ?_)
  have hwin : ∀ r' ∈ [winRegion (scr s₀)], (blR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.blk_scr (win_sub _)
  have hblk : ∀ m, Frame [winRegion (scr s₀)] s₁.mem m → ∀ t : Nat, t < 16 →
      beWord m (blkAddr s₀ i) (4 * t) = W (blk s₀ i) t := by
    intro m hm t ht
    rw [frame_beWord hm hwin (hp.blk_contains hi ht), hm₁,
      frame_beWord hL.frame (by simpa using ⟨hp.blk_st, hp.blk_scr⟩) (hp.blk_contains hi ht)]
    exact blk_word i t ht
  have hr1₁ : s₁.gpr .a1 = blkAddr s₀ i := (hpub₁ .a1 (by decide)).trans hL.a1
  have hr3₁ : s₁.gpr .a3 = scr s₀ := (hpub₁ .a3 (by decide)).trans hL.a3
  refine WP.seq (WP.mono (rounds_ok _ (blk s₀ i) _ (scr s₀) s₁ hr1₁ hr3₁ (align_al _)
    (by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_slot)
    (by rw [hwr₁, hL.wr]; exact hp.out_slot)
    (fun t ht => by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_blk hi ht) hblk hv₁ 80 (Nat.le_refl _))
    fun s₂ hR => ?_)
  have hst : ∀ r' ∈ [winRegion (scr s₀)], (stR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.st_scr (win_sub _)
  have pub₂ : ∀ r ∈ pubRegs, s₂.gpr r = s.gpr r := fun r hr => by
    rw [hR.pub r hr, hpub₁ r hr]
  have hr0₂ : s₂.gpr .a0 = st s₀ := by rw [pub₂ .a0 (by decide), hL.a0]
  have hrd₂ : s₂.rd = s₀.rd := by rw [hR.rd, hrd₁, hL.rd]
  have hwr₂ : s₂.wr = s₀.wr := by rw [hR.wr, hwr₁, hL.wr]
  rw [WP.block_append_iff]
  refine WP.mono (update_ok hp _ (stateAt s.mem (st s₀)) hR.vars hr0₂ hrd₂ hwr₂ fun k hk => ?_)
    fun s₃ h₃ => ?_
  · rw [hR.frame.readW (Offset.contains_base _ (by omega) (by omega)) hst (by decide), hm₁,
      getElem!_pos _ k hk, stateAt_get _ _ hk]
  have hr1₃ : s₃.gpr .a1 = blkAddr s₀ i := by rw [h₃.pub .a1 (by decide), pub₂ .a1 (by decide), hL.a1]
  have hr2₃ : s₃.gpr .a2 = BitVec.ofNat 64 (nb s₀ - i) := by
    rw [h₃.pub .a2 (by decide), pub₂ .a2 (by decide), hL.a2]
  have hframe : Frame [stR s₀, scrR s₀] s₀.mem s₃.mem := by
    refine hL.frame.trans ?_
    rw [← hm₁]
    refine Frame.trans (hR.frame.sub fun r hr => ⟨scrR s₀, by simp, by simp at hr; subst hr; exact win_sub _⟩) ?_
    rw [h₃.mem]
    exact (frame_writeUpTo (r := stR s₀) _ (Nat.le_refl _) fun j hj =>
      Offset.contains_base _ (by omega) (by omega)).mono fun r hr => by simp at hr; simp [hr]
  have hstate : stateAt s₃.mem (st s₀) = compressBlocks (H₀ s₀) s₀.mem (bp s₀) (i + 1) := by
    rw [compressBlocks_succ, ← hL.state]
    apply stateAt_eq
    intro k hk
    rw [h₃.mem, readW_writeUpTo _ _ _ (Nat.le_refl _) hk]
    simp only [hk, ↓reduceIte]
    rw [getElem!_pos _ k hk]
    rfl
  apply WP.of_runBlock
  simp only [advance, runBlock_cons, runStep_some, runBlock_nil, exec_addi (show imm12 64 by decide),
    exec_addi (show imm12 (-1) by decide), Option.some.injEq, exists_eq_left']
  -- The state after advancing.
  generalize hs₄ : State.write _ _ _ = s₄
  have g1 : s₄.gpr .a1 = blkAddr s₀ (i + 1) := by
    rw [← hs₄, RegUpd.gpr_write_of_ne _ _ (by decide), RegUpd.gpr_write_self, hr1₃]
    simp only [blkAddr]
    rw [show BitVec.ofInt 64 64 = BitVec.ofNat 64 64 from rfl, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
      Nat.mul_succ]
  have hnb := hp.nb_lt
  have g2 : s₄.gpr .a2 = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [← hs₄, RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne _ _ (by decide), hr2₃]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show (BitVec.ofInt 64 (-1)).toNat = 2 ^ 64 - 1 from rfl]
    omega
  have gr : ∀ r, r ≠ .a1 → r ≠ .a2 → s₄.gpr r = s₃.gpr r := fun r h1 h2 => by
    rw [← hs₄, RegUpd.gpr_write_of_ne _ _ h2, RegUpd.gpr_write_of_ne _ _ h1]
  have gm : s₄.mem = s₃.mem := by rw [← hs₄]; rfl
  have grd : s₄.rd = s₃.rd := by rw [← hs₄]; rfl
  have gwr : s₄.wr = s₃.wr := by rw [← hs₄]; rfl
  have hcommon : Common s₀ (i + 1) s₄ := by
    refine ⟨by rw [gr _ (by decide) (by decide), h₃.pub .a0 (by decide), hr0₂],
      by rw [gr _ (by decide) (by decide), h₃.pub .a3 (by decide), pub₂ .a3 (by decide), hL.a3],
      fun r hr h1 h2 h3 => ?_, by rw [grd, h₃.rd, hrd₂], by rw [gwr, h₃.wr, hwr₂],
      by rw [gm]; exact hframe, by rw [gm]; exact hstate⟩
    rw [gr r h1 h2, h₃.pub r hr, pub₂ r hr, hL.kept r hr h1 h2 h3]
  have hev : eval (.nonzero .a2) s₄ = some (BitVec.ofNat 64 (nb s₀ - (i + 1)) != 0) := by
    simp only [eval, g2]
  by_cases hlast : i + 1 = nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp, hlast ▸ hcommon⟩
  · right
    have hne : nb s₀ - (i + 1) ≠ 0 := by omega
    have h0 : BitVec.ofNat 64 (nb s₀ - (i + 1)) ≠ 0 := by
      intro h
      have h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'
      exact hne h'
    exact ⟨by rw [hev]; simpa using h0, by omega, { hcommon with a1 := g1, a2 := g2 }⟩

/-! ## The whole function -/

theorem blocks_ok {s₀ : State} (hp : Pre s₀) {s₁ : State} (hc₀ : Common s₀ 0 s₁)
    (hr1 : s₁.gpr .a1 = bp s₀) (hr2 : s₁.gpr .a2 = s₀.gpr .a2) :
    WP isa blocks s₁ (Common s₀ (nb s₀)) := by
  refine WP.ite (s₁.gpr .a2 == 0) (by simp [eval]) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by simp [hr2] at h; simp [nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < nb s₀ := by
      simp only [beq_eq_false_iff_ne, ne_eq, hr2] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv s₀ i s
    have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval (.nonzero .a2) s' = some false ∧ Common s₀ (nb s₀) s') ∨
        (eval (.nonzero .a2) s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (body_ok hp hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - (i + 1), by omega, i + 1, rfl, hi', hL'⟩
    have hL₀ : LInv s₀ 0 s₁ :=
      { hc₀ with
        a1 := by simp [blkAddr, hr1]
        a2 := by simp [nb, hr2] }
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₁ ⟨0, rfl, hpos, hL₀⟩

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa compress s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
      Proof.Sha1.compressRISCV64.post s₀ s' := by
  refine WP.seq (WP.mono (Q := fun (s₁ : State) => s₁.gpr .a3 = scr s₀ ∧ (∀ r, r ≠ .a3 → s₁.gpr r = s₀.gpr r) ∧
      s₁.mem = s₀.mem ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr) ?_ fun s₁ ⟨h3, hg, hm, hrd, hwr⟩ => ?_)
  · apply WP.of_runBlock
    simp only [align, runBlock_cons, runStep_some, runBlock_nil, exec_addi (show imm12 7 by decide),
      exec_logicImm (show imm12 (-8) by decide), RegUpd.gpr_write_self, align_eq, RegUpd.write_write,
      Option.some.injEq, exists_eq_left']
    exact ⟨trivial, fun r hr => RegUpd.gpr_write_of_ne _ _ hr, rfl, rfl, rfl⟩
  have hc₀ : Common s₀ 0 s₁ := ⟨by rw [hg _ (by decide)], h3, fun r _ _ _ h => hg r h, hrd, hwr,
    by rw [hm]; exact Frame.refl _ _, by rw [hm]; rfl⟩
  refine WP.mono (blocks_ok hp hc₀ (hg _ (by decide)) (hg _ (by decide))) fun s' hc =>
    ⟨fun r hr => hc.kept r (preserved_pub r hr) (by revert r; decide) (by revert r; decide)
      (by revert r; decide), hc.kept _ (by decide) (by decide) (by decide) (by decide), hc.state⟩

/-- A state satisfying the precondition (with no blocks). -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a3 => 0x3000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 20⟩, ⟨0x3000, 80⟩]

theorem compress_verified :
    Verified RISCV64.target Impl.Sha1.RISCV64.compress Proof.Sha1.compressRISCV64 := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h₁, hra, h₂⟩ := correct (pre_of s hs)
    exact ⟨t, s', he, ⟨h₁, Exec.sp he, hra⟩, h₂⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3]) ?_ (by taint_decide)
    intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, hsp⟩
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [h1, h2, h3, h4]
  · refine ⟨satState, rfl, rfl, ?_, ?_, ?_⟩ <;>
    exact Region.disjoint_of_sep (by decide)

end VG.Proof.Sha1.RISCV64
