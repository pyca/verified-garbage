module

public import VerifiedGarbage.Proof.Sha512.RISCV64.Rounds
public meta import VerifiedGarbage.Proof.Sha512.RISCV64.Rounds
public import VerifiedGarbage.Proof.Sha512.RISCV64.Contract
public meta import VerifiedGarbage.Proof.Sha512.RISCV64.Contract
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RISCV64.Words64
meta import VerifiedGarbage.Proof.Framework.RISCV64.Words64
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
# SHA-512 compression function on RISC-V: the whole function

Untrusted: everything here is checked by Lean. The structure of the PPC64LE
proof (`Proof/Sha512/PPC64LE/Compress.lean`) and of SHA-256's on RISC-V
(`Proof/Sha256/RISCV64/Compress.lean`), with the hash value read and written
a byte at a time (`Proof/Framework/RISCV64/ByteLoad64.lean`) and the scratch
space rounded up to a multiple of 8 first.
-/

@[expose] public section

namespace VG.Proof.Sha512.RISCV64

open VG VG.RISCV64 VG.RISCV64.ByteLoad VG.Impl.Sha512.RISCV64 VG.Impl.Words.RISCV64
open VG.Spec.Sha512 (HashValue Word Block K W stateAt blockAt compressBlocks compress parseBlock)

/-! ## Rounding the scratch space up -/

/-- How far `x` is below the next multiple of 8. -/
def pad (x : Addr) : Nat := (8 - x.toNat % 8) % 8

theorem pad_lt (x : Addr) : pad x < 8 := Nat.mod_lt _ (by decide)

theorem and_neg8 (y : BitVec 64) : y &&& BitVec.ofInt 64 (-8) = (y >>> 3) <<< 3 := by
  have : BitVec.ofInt 64 (-8) = BitVec.allOnes 64 <<< 3 := by decide
  rw [this]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_allOnes, hi, decide_true, Bool.true_and]
  by_cases h3 : i < 3
  · simp [h3]
  · simp [h3, show 3 + (i - 3) = i by omega, show i - 3 < 64 by omega]

/-- `addi 7` then `andi -8`. -/
theorem align_eq (x : Addr) :
    (x + BitVec.ofInt 64 7) &&& BitVec.ofInt 64 (-8) = x + BitVec.ofNat 64 (pad x) := by
  rw [and_neg8]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, pad]
  have := x.isLt
  rw [show BitVec.toNat (BitVec.ofInt 64 7) = 7 from rfl]
  omega

theorem align_al (x : Addr) : (x + BitVec.ofNat 64 (pad x)).toNat % 8 = 0 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  unfold pad
  have := x.isLt
  omega

/-! ## Addresses and regions -/

theorem readW_writeW_word (m : Mem) (p : Addr) (v : Word) {j k : Nat} (hj : j < 8) (hk : k < 8)
    (h : j ≠ k) :
    (m.writeW (p + BitVec.ofNat 64 (8 * k)) v).readW (p + BitVec.ofNat 64 (8 * j)) 64 =
    m.readW (p + BitVec.ofNat 64 (8 * j)) 64 :=
  Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide)

theorem stateAt_eq {m : Mem} {p : Addr} {v : HashValue}
    (h : ∀ k : Nat, (hk : k < 8) → m.readW (p + BitVec.ofNat 64 (8 * k)) 64 = v[k]) :
    stateAt m p = v := by
  apply Vector.ext
  intro k hk
  simp only [stateAt, Vector.getElem_ofFn]
  exact h k hk

theorem stateAt_get (m : Mem) (p : Addr) {k : Nat} (hk : k < 8) :
    (stateAt m p)[k] = m.readW (p + BitVec.ofNat 64 (8 * k)) 64 := by
  simp only [stateAt, Vector.getElem_ofFn]

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .a0
abbrev bp : Addr := s₀.gpr .a1
abbrev nb : Nat := (s₀.gpr .a2).toNat
abbrev scr₀ : Addr := s₀.gpr .a3
/-- The scratch space, rounded up to a multiple of 8. -/
abbrev scr : Addr := scr₀ s₀ + BitVec.ofNat 64 (pad (scr₀ s₀))
abbrev stR : Region := ⟨st s₀, 64⟩
abbrev blR : Region := ⟨bp s₀, 128 * nb s₀⟩
abbrev scrR : Region := ⟨scr₀ s₀, 144⟩
abbrev H₀ : HashValue := stateAt s₀.mem (st s₀)
/-- Where `s0` is saved. -/
abbrev savAddr : Addr := scr s₀ + BitVec.ofNat 64 128
abbrev savR : Region := ⟨savAddr s₀, 8⟩

/-- Block `i`, and where it starts. -/
abbrev blkAddr (i : Nat) : Addr := bp s₀ + BitVec.ofNat 64 (128 * i)
abbrev blk (i : Nat) : Block := blockAt s₀.mem (blkAddr s₀ i)

end

/-- An offset of the rounded scratch space, as one of `scratch`. -/
theorem scr_add (s₀ : State) (d : Nat) :
    scr s₀ + BitVec.ofNat 64 d = scr₀ s₀ + BitVec.ofNat 64 (pad (scr₀ s₀) + d) := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]

theorem scr_contains (s₀ : State) {d n : Nat} (h : d + n ≤ 136) :
    (scrR s₀).Contains (scr s₀ + BitVec.ofNat 64 d) n := by
  rw [scr_add]
  have := pad_lt (scr₀ s₀)
  exact Offset.contains_base _ (by omega) (by omega)

theorem scr_sub (s₀ : State) {d n : Nat} (h : d + n ≤ 136) :
    Region.Sub ⟨scr s₀ + BitVec.ofNat 64 d, n⟩ (scrR s₀) := by
  rw [scr_add]
  have := pad_lt (scr₀ s₀)
  exact Offset.sub_base _ (by omega)

theorem win_sub (s₀ : State) : Region.Sub (winRegion (scr s₀)) (scrR s₀) := by
  have := scr_sub s₀ (d := 0) (n := 128) (by omega)
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this

theorem savR_sub (s₀ : State) : Region.Sub (savR s₀) (scrR s₀) := scr_sub s₀ (by omega)

theorem win_sav (s₀ : State) : (winRegion (scr s₀)).Disjoint (savR s₀) := by
  have := Offset.disjoint (scr s₀) (d := 0) (n := 128) (e := 128) (k := 8) (by omega) (by omega)
    (by omega)
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [blR s₀]
  wr : s₀.wr = [stR s₀, scrR s₀]
  st_scr : (stR s₀).Disjoint (scrR s₀)
  blk_st : (blR s₀).Disjoint (stR s₀)
  blk_scr : (blR s₀).Disjoint (scrR s₀)

theorem pre_of (s₀ : State) (h : Proof.Sha512.compressRISCV64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

theorem nb_lt : 128 * nb s₀ < 2 ^ 64 := by
  by_contra hn
  refine h.blk_st (st s₀) ?_ (by simp [Region.Contains])
  simp only [Region.Contains]
  have := (st s₀ - bp s₀).isLt
  omega

theorem in_state {k : Nat} (hk : k < 8) :
    InRegions (s₀.rd ++ s₀.wr) (st s₀ + BitVec.ofNat 64 (8 * k)) 8 :=
  ⟨stR s₀, by simp [h.wr], Offset.contains_base _ (by omega) (by omega)⟩

theorem out_state {k : Nat} (hk : k < 8) :
    InRegions s₀.wr (st s₀ + BitVec.ofNat 64 (8 * k)) 8 :=
  ⟨stR s₀, by simp [h.wr], Offset.contains_base _ (by omega) (by omega)⟩

theorem in_slot (j : Nat) : InRegions (s₀.rd ++ s₀.wr) (slotAddr (scr s₀) j) 8 :=
  ⟨scrR s₀, by simp [h.wr], scr_contains s₀ (by simp only [slot]; omega)⟩

theorem out_slot (j : Nat) : InRegions s₀.wr (slotAddr (scr s₀) j) 8 :=
  ⟨scrR s₀, by simp [h.wr], scr_contains s₀ (by simp only [slot]; omega)⟩

theorem in_sav (rs : List Region) : InRegions (rs ++ s₀.wr) (savAddr s₀) 8 :=
  ⟨scrR s₀, by simp [h.wr], scr_contains s₀ (by omega)⟩

theorem out_sav : InRegions s₀.wr (savAddr s₀) 8 :=
  ⟨scrR s₀, by simp [h.wr], scr_contains s₀ (by omega)⟩

theorem blk_contains {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    (blR s₀).Contains (blkAddr s₀ i + BitVec.ofNat 64 (8 * t)) 8 := by
  have := h.nb_lt
  rw [show blkAddr s₀ i + BitVec.ofNat 64 (8 * t) =
    bp s₀ + BitVec.ofNat 64 (128 * i + 8 * t) by rw [BitVec.ofNat_add, BitVec.add_assoc]]
  exact Offset.contains_base _ (by omega) (by omega)

theorem in_blk {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr s₀ i + BitVec.ofNat 64 (8 * t)) 8 :=
  ⟨blR s₀, by simp [h.rd], h.blk_contains hi ht⟩

end Pre

/-! ## Saving and restoring `s0` -/

/-- The callee-saved registers (and the return address) the code does not
use: never written. -/
def keepRegs : List Reg := [.ra, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11]

theorem keepRegs_pub : ∀ r ∈ keepRegs, r ∈ pubRegs := by decide

theorem keepRegs_ne : ∀ r ∈ keepRegs, r ≠ .a3 ∧ r ≠ .s0 := by decide

/-- A preserved register is `s0`, or kept. -/
theorem preserved_cases : ∀ r ∈ preserved, r = .s0 ∨ r ∈ keepRegs := by decide

/-- After `save`. -/
structure Saved (s₀ : State) (s : State) : Prop where
  a3 : s.gpr .a3 = scr s₀
  gpr : ∀ r, r ≠ .a3 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [savR s₀] s₀.mem s.mem
  sav : s.mem.readW (savAddr s₀) 64 = s₀.gpr .s0

theorem save_ok {s₀ : State} (hp : Pre s₀) : WP isa (.block save) s₀ (Saved s₀) := by
  have hal : (scr s₀ + BitVec.ofNat 64 128).toNat % 8 = 0 := by
    have := align_al (scr₀ s₀)
    change (scr₀ s₀ + BitVec.ofNat 64 (pad (scr₀ s₀)) + BitVec.ofNat 64 128).toNat % 8 = 0
    rw [BitVec.toNat_add (scr₀ s₀ + _), BitVec.toNat_ofNat 128 64]
    omega
  apply WP.of_runBlock
  simp only [save, runBlock_cons, runStep_some, exec_addi (show imm12 7 by decide),
    exec_logicImm (show imm12 (-8) by decide), RegUpd.gpr_write_self, align_eq,
    RegUpd.write_write]
  rw [exec_store_d (show 128 < 2048 by decide) (by rw [RegUpd.gpr_write_self]; exact hal)
      (by rw [RegUpd.gpr_write_self, RegUpd.wr_write]; exact hp.out_sav), runStep_some,
    runBlock_nil]
  refine ⟨_, rfl, RegUpd.gpr_write_self s₀ .a3 _, fun r hr => RegUpd.gpr_write_of_ne s₀ _ hr, rfl,
    rfl, ?_, ?_⟩
  · simp only [RegUpd.gpr_write_self, RegUpd.mem_write]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  · simp only [RegUpd.gpr_write_self, RegUpd.mem_write,
      RegUpd.gpr_write_of_ne _ _ (show Reg.s0 ≠ Reg.a3 by decide)]
    exact Mem.readW_writeW_self64 _ _ _

/-! ## The loop invariant -/

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  a0 : s.gpr .a0 = st s₀
  a3 : s.gpr .a3 = scr s₀
  kept : ∀ r ∈ keepRegs, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR s₀, scrR s₀] s₀.mem s.mem
  sav : s.mem.readW (savAddr s₀) 64 = s₀.gpr .s0
  state : stateAt s.mem (st s₀) = compressBlocks (H₀ s₀) s₀.mem (bp s₀) i

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  a1 : s.gpr .a1 = blkAddr s₀ i
  a2 : s.gpr .a2 = BitVec.ofNat 64 (nb s₀ - i)

/-! ## Loading the hash value -/

theorem var0 {k : Nat} (hk : k < 8) : var 0 k = work.getD k .t0 := by
  simp only [var, Nat.zero_mod, Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt hk]

theorem var0_inj {j k : Nat} (hj : j < 8) (hk : k < 8) (h : var 0 j = var 0 k) : j = k := by
  have key : ∀ j < 8, ∀ k < 8, var 0 j = var 0 k → j = k := by decide
  exact key j hj k hk h

theorem var0_ne {k : Nat} (hk : k < 8) :
    var 0 k ≠ .a0 ∧ var 0 k ≠ T0 ∧ var 0 k ≠ T1 ∧ var 0 k ≠ T2 := by
  have key : ∀ k < 8, var 0 k ≠ .a0 ∧ var 0 k ≠ T0 ∧ var 0 k ≠ T1 ∧ var 0 k ≠ T2 := by decide
  exact key k hk

theorem var0_pub {k : Nat} (hk : k < 8) : ∀ r ∈ pubRegs, r ≠ var 0 k := by
  have key : ∀ k < 8, ∀ r ∈ pubRegs, r ≠ var 0 k := by decide
  exact key k hk

/-- The first `k` words of the hash value are loaded. -/
structure LdI (s₁ : State) (k : Nat) (s : State) : Prop where
  vars : ∀ j < k, s.gpr (var 0 j) = (stateAt s₁.mem (s₁.gpr .a0))[j]!
  pub : ∀ r ∈ pubRegs, s.gpr r = s₁.gpr r
  mem : s.mem = s₁.mem
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr

theorem load_step {s₀ s₁ : State} (hp : Pre s₀) (hr0 : s₁.gpr .a0 = st s₀) (hrd : s₁.rd = s₀.rd)
    (hwr : s₁.wr = s₀.wr) {k : Nat} (hk : k < 8) {s : State} (h : LdI s₁ k s) :
    WP isa (.block (Impl.Words64.RISCV64.loadLE64 (var 0 k) T0 T1 .a0 (8 * k))) s (LdI s₁ (k + 1)) := by
  have ne := var0_ne hk
  have h0 : s.gpr .a0 = st s₀ := (h.pub .a0 (by decide)).trans hr0
  refine WP.mono (Words64.loadLE64_ok ne.1 (by decide) ne.2.1 (by decide) (by decide) ne.2.2.1
    (by omega) (by rw [h.rd, h.wr, hrd, hwr, h0]; exact hp.in_state hk)) fun s' u => ?_
  refine ⟨fun j hj => ?_, fun r hr => ?_, u.mem.trans h.mem, u.rd.trans h.rd, u.wr.trans h.wr⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · have nj := var0_ne (by omega : j < 8)
      rw [u.other _ (fun e => absurd (var0_inj (by omega) hk e) (by omega)) nj.2.1 nj.2.2.1]
      exact h.vars j hj
    · rw [u.gpr, h.mem, h0, ← hr0, getElem!_pos _ j hk, stateAt_get _ _ hk]
  · rw [u.other _ (var0_pub hk r hr) (fun e => (pubRegs_ne hr).1 e) (fun e => (pubRegs_ne hr).2.1 e)]
    exact h.pub r hr

theorem load_ok {s₀ : State} (hp : Pre s₀) {s : State} (hr0 : s.gpr .a0 = st s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block load) s fun s₁ =>
      Vars 0 s₁ (stateAt s.mem (st s₀)) ∧ (∀ r ∈ pubRegs, s₁.gpr r = s.gpr r) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.mem = s.mem := by
  refine WP.mono (wp_range_flatMap (M := isa) (LdI s) (fun k s' hk h => load_step hp hr0 hrd hwr hk h)
    8 (Nat.le_refl _) s ⟨fun _ h => absurd h (by omega), fun _ _ => rfl, rfl, rfl, rfl⟩)
    fun s₁ h => ⟨?_, h.pub, h.rd, h.wr, h.mem⟩
  have v := h.vars
  rw [hr0] at v
  exact ⟨v 0 (by decide), v 1 (by decide), v 2 (by decide), v 3 (by decide), v 4 (by decide),
    v 5 (by decide), v 6 (by decide), v 7 (by decide)⟩

/-! ## Adding the hash value into the working variables -/

/-- The first `k` of eight words `f` written at `p`. -/
def writeUpTo (m : Mem) (p : Addr) (f : HashValue) (k : Nat) : Mem :=
  (List.range k).foldl (fun m j => m.writeW (p + BitVec.ofNat 64 (8 * j)) f[j]!) m

theorem writeUpTo_succ (m : Mem) (p : Addr) (f : HashValue) (k : Nat) :
    writeUpTo m p f (k + 1) = (writeUpTo m p f k).writeW (p + BitVec.ofNat 64 (8 * k)) f[k]! := by
  simp [writeUpTo, List.range_succ, List.foldl_append]

theorem readW_writeUpTo (m : Mem) (p : Addr) (f : HashValue) {k j : Nat} (hk : k ≤ 8) (hj : j < 8) :
    (writeUpTo m p f k).readW (p + BitVec.ofNat 64 (8 * j)) 64 =
      if j < k then f[j]! else m.readW (p + BitVec.ofNat 64 (8 * j)) 64 := by
  induction k with
  | zero => simp [writeUpTo]
  | succ k ih =>
    rw [writeUpTo_succ]
    by_cases hjk : j = k
    · subst hjk; rw [Mem.readW_writeW_self64]; simp
    · rw [readW_writeW_word _ _ _ hj (by omega) hjk, ih (by omega)]
      by_cases h : j < k
      · simp [h, show j < k + 1 by omega]
      · simp [h, show ¬ j < k + 1 by omega]

theorem frame_writeUpTo {r : Region} {m : Mem} {p : Addr} (f : HashValue) {k : Nat} (hk : k ≤ 8)
    (hc : ∀ j < 8, r.Contains (p + BitVec.ofNat 64 (8 * j)) 8) :
    Frame [r] m (writeUpTo m p f k) := by
  induction k with
  | zero => exact Frame.refl _ _
  | succ k ih =>
    rw [writeUpTo_succ]
    exact (ih (by omega)).writeW (List.mem_singleton_self _) _ (hc k (by omega))

/-- The first `k` words are updated, from the state `s₂` after the rounds,
whose working variables are `V`, and the hash value `H` it holds. -/
structure UInv (s₀ s₂ : State) (V H : HashValue) (k : Nat) (s : State) : Prop where
  vars : ∀ j, k ≤ j → j < 8 → s.gpr (var 0 j) = V[j]!
  pub : ∀ r ∈ pubRegs, s.gpr r = s₂.gpr r
  mem : s.mem = writeUpTo s₂.mem (st s₀) (Vector.zipWith (· + ·) V H) k
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr

theorem update_step {s₀ s₂ : State} (hp : Pre s₀) (V H : HashValue) (hr0 : s₂.gpr .a0 = st s₀)
    (hrd : s₂.rd = s₀.rd) (hwr : s₂.wr = s₀.wr)
    (hH : ∀ j < 8, s₂.mem.readW (st s₀ + BitVec.ofNat 64 (8 * j)) 64 = H[j]!)
    {k : Nat} (hk : k < 8) {s : State} (h : UInv s₀ s₂ V H k s) :
    WP isa (.block (updateW k)) s (UInv s₀ s₂ V H (k + 1)) := by
  have ne := var0_ne hk
  have h0 : s.gpr .a0 = st s₀ := (h.pub .a0 (by decide)).trans hr0
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .a0 + BitVec.ofNat 64 (8 * k)) 8 := by
    rw [h.rd, h.wr, hrd, hwr, h0]; exact hp.in_state hk
  unfold updateW
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (Words64.loadLE64_ok (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by omega) hin) fun s₁ u₁ => ?_
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_add, Option.some.injEq,
    exists_eq_left']
  -- The state after the addition.
  generalize hs₂' : State.write _ _ _ = s₃
  have g1 : ∀ r, r ≠ T0 → r ≠ T1 → r ≠ T2 → s₁.gpr r = s.gpr r := u₁.other
  have g0 : s₃.gpr .a0 = st s₀ := by
    rw [← hs₂', RegUpd.gpr_write_of_ne _ _ (Ne.symm ne.1), g1 _ (by decide) (by decide) (by decide), h0]
  have gv : s₃.gpr (var 0 k) = V[k]! + H[k]! := by
    rw [← hs₂', RegUpd.gpr_write_self, g1 _ ne.2.1 ne.2.2.1 ne.2.2.2, h.vars k (Nat.le_refl _) hk,
      u₁.gpr, h0, h.mem, readW_writeUpTo _ _ _ (by omega) hk]
    simp only [Nat.lt_irrefl, ite_false]
    rw [hH k hk]
  have gm : s₃.mem = s.mem := by rw [← hs₂', RegUpd.mem_write]; exact u₁.mem
  have gwr : s₃.wr = s.wr := by rw [← hs₂', RegUpd.wr_write]; exact u₁.wr
  have grd : s₃.rd = s.rd := by rw [← hs₂', RegUpd.rd_write]; exact u₁.rd
  have gr : ∀ r, r ≠ var 0 k → r ≠ T0 → r ≠ T1 → r ≠ T2 → s₃.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 => by rw [← hs₂', RegUpd.gpr_write_of_ne _ _ h1, g1 r h2 h3 h4]
  refine WP.mono (Words64.storeLE64_ok (Ne.symm ne.2.1) (by decide) (by decide) (by decide) (by omega)
    (by rw [gwr, h.wr, hwr, g0]; exact hp.out_state hk)) fun s₄ ⟨g₄, m₄, rd₄, wr₄, _⟩ => ?_
  refine ⟨fun j hj hj' => ?_, fun r hr => ?_, ?_, rd₄.trans (grd.trans h.rd), wr₄.trans (gwr.trans h.wr)⟩
  · have hne : var 0 j ≠ var 0 k := fun e => absurd (var0_inj hj' hk e) (by omega)
    have nj := var0_ne hj'
    rw [g₄ _ nj.2.1 nj.2.2.1, gr _ hne nj.2.1 nj.2.2.1 nj.2.2.2]
    exact h.vars j (by omega) hj'
  · have np := pubRegs_ne hr
    rw [g₄ _ (fun e => np.1 e) (fun e => np.2.1 e),
      gr r (var0_pub hk r hr) (fun e => np.1 e) (fun e => np.2.1 e) (fun e => np.2.2.1 e)]
    exact h.pub r hr
  · rw [m₄, gm, h.mem, writeUpTo_succ, g0, gv]
    congr 1
    rw [getElem!_pos (Vector.zipWith _ V H) k hk, Vector.getElem_zipWith, getElem!_pos V k hk,
      getElem!_pos H k hk]

theorem vars_get {s : State} {V : HashValue} (h : Vars 0 s V) :
    ∀ j, j < 8 → s.gpr (var 0 j) = V[j]! := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  intro j hj
  rw [getElem!_pos V j hj]
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3, h4, h5, h6, h7]

theorem update_ok {s₀ s₂ : State} (hp : Pre s₀) (V H : HashValue) (hv : Vars 0 s₂ V)
    (hr0 : s₂.gpr .a0 = st s₀) (hrd : s₂.rd = s₀.rd) (hwr : s₂.wr = s₀.wr)
    (hH : ∀ j < 8, s₂.mem.readW (st s₀ + BitVec.ofNat 64 (8 * j)) 64 = H[j]!) :
    WP isa (.block ((List.range 8).flatMap updateW)) s₂ (UInv s₀ s₂ V H 8) :=
  wp_range_flatMap (M := isa) (UInv s₀ s₂ V H) (fun _ _ hk h => update_step hp V H hr0 hrd hwr hH hk h)
    8 (Nat.le_refl _) s₂ ⟨fun j _ hj => vars_get hv j hj, fun _ _ => rfl, rfl, rfl, rfl⟩

theorem compressBlocks_succ (H : HashValue) (m : Mem) (p : Addr) (i : Nat) :
    compressBlocks H m p (i + 1) =
      compress (compressBlocks H m p i) (blockAt m (p + BitVec.ofNat 64 (128 * i))) := by
  simp [compressBlocks, List.range_succ, List.foldl_append]

theorem blk_word {s₀ : State} (i t : Nat) (ht : t < 16) :
    be64 s₀.mem (blkAddr s₀ i) (8 * t) = W (blk s₀ i) t := by
  rw [W_lt _ ht]; rfl

theorem frame_byte {rs : List Region} {m m' : Mem} {R : Region} {x : Addr} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, R.Disjoint r) (hx : R.Contains x 1) : m' x = m x :=
  hf x fun r hr hc => hd r hr x hx hc

theorem frame_be64 {rs : List Region} {m m' : Mem} {R : Region} {p : Addr} {off : Nat}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, R.Disjoint r) (hc : R.Contains (p + BitVec.ofNat 64 off) 8) :
    be64 m' p off = be64 m p off := by
  have h0 := contains_byte' hc (k := 0) (by decide)
  rw [Nat.add_zero] at h0
  simp only [be64, frame_byte hf hd h0,
    frame_byte hf hd (contains_byte' hc (k := 1) (by decide)),
    frame_byte hf hd (contains_byte' hc (k := 2) (by decide)),
    frame_byte hf hd (contains_byte' hc (k := 3) (by decide)),
    frame_byte hf hd (contains_byte' hc (k := 4) (by decide)),
    frame_byte hf hd (contains_byte' hc (k := 5) (by decide)),
    frame_byte hf hd (contains_byte' hc (k := 6) (by decide)),
    frame_byte hf hd (contains_byte' hc (k := 7) (by decide))]

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval (.nonzero .a2) s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval (.nonzero .a2) s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  refine WP.seq (WP.mono (load_ok hp hL.a0 hL.rd hL.wr) fun s₁ ⟨hv₁, hpub₁, hrd₁, hwr₁, hm₁⟩ => ?_)
  have hwin : ∀ r' ∈ [winRegion (scr s₀)], (blR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.blk_scr (win_sub _)
  have hblk : ∀ m, Frame [winRegion (scr s₀)] s₁.mem m → ∀ t : Nat, t < 16 →
      be64 m (blkAddr s₀ i) (8 * t) = W (blk s₀ i) t := by
    intro m hm t ht
    rw [frame_be64 hm hwin (hp.blk_contains hi ht), hm₁,
      frame_be64 hL.frame (by simpa using ⟨hp.blk_st, hp.blk_scr⟩) (hp.blk_contains hi ht)]
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
  have hsav : s₃.mem.readW (savAddr s₀) 64 = s₀.gpr .s0 := by
    have hd : (savR s₀).Disjoint (stR s₀) :=
      Region.Disjoint.sub_left hp.st_scr.symm (savR_sub s₀)
    rw [h₃.mem, (frame_writeUpTo (r := stR s₀) _ (Nat.le_refl _) fun j hj =>
        Offset.contains_base _ (by omega) (by omega)).readW (r := savR s₀)
        (Region.contains_self _ _) (by simpa using hd) (by decide),
      hR.frame.readW (r := savR s₀) (Region.contains_self _ _) (by simpa using (win_sav s₀).symm)
        (by decide), hm₁]
    exact hL.sav
  have hstate : stateAt s₃.mem (st s₀) = compressBlocks (H₀ s₀) s₀.mem (bp s₀) (i + 1) := by
    rw [compressBlocks_succ, ← hL.state]
    apply stateAt_eq
    intro k hk
    rw [h₃.mem, readW_writeUpTo _ _ _ (Nat.le_refl _) hk]
    simp only [hk, ↓reduceIte]
    rw [getElem!_pos _ k hk]
    rfl
  apply WP.of_runBlock
  simp only [advance, runBlock_cons, runStep_some, runBlock_nil, exec_addi (show imm12 128 by decide),
    exec_addi (show imm12 (-1) by decide), Option.some.injEq, exists_eq_left']
  -- The state after advancing.
  generalize hs₄ : State.write _ _ _ = s₄
  have g1 : s₄.gpr .a1 = blkAddr s₀ (i + 1) := by
    rw [← hs₄, RegUpd.gpr_write_of_ne _ _ (by decide), RegUpd.gpr_write_self, hr1₃]
    simp only [blkAddr]
    rw [show BitVec.ofInt 64 128 = BitVec.ofNat 64 128 from rfl, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
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
      fun r hr => ?_, by rw [grd, h₃.rd, hrd₂], by rw [gwr, h₃.wr, hwr₂], by rw [gm]; exact hframe,
      by rw [gm]; exact hsav, by rw [gm]; exact hstate⟩
    have hp' := keepRegs_pub r hr
    rw [gr r (fun e => by subst e; simp [keepRegs] at hr) (fun e => by subst e; simp [keepRegs] at hr),
      h₃.pub r hp', pub₂ r hp', hL.kept r hr]
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
      Proof.Sha512.compressRISCV64.post s₀ s' := by
  refine WP.seq (WP.mono (save_ok hp) fun s₁ h₁ => ?_)
  have hc₀ : Common s₀ 0 s₁ := by
    refine ⟨h₁.gpr _ (by decide), h₁.a3, fun r hr => h₁.gpr _ (keepRegs_ne r hr).1, h₁.rd, h₁.wr,
      h₁.frame.sub fun r hr => ?_, h₁.sav, ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, savR_sub s₀⟩
    · show stateAt s₁.mem (st s₀) = H₀ s₀
      apply stateAt_eq
      intro k hk
      rw [h₁.frame.readW (r := stR s₀) (Offset.contains_base _ (by omega) (by omega))
        (by simpa using Region.Disjoint.sub_right hp.st_scr (savR_sub s₀)) (by decide),
        ← stateAt_get _ _ hk]
  refine WP.seq (WP.mono (blocks_ok hp hc₀ (h₁.gpr _ (by decide)) (h₁.gpr _ (by decide)))
    fun s₂ h₂ => ?_)
  have hal : (s₂.gpr .a3 + BitVec.ofNat 64 128).toNat % 8 = 0 := by
    have := align_al (scr₀ s₀)
    rw [h₂.a3]
    change (scr₀ s₀ + BitVec.ofNat 64 (pad (scr₀ s₀)) + BitVec.ofNat 64 128).toNat % 8 = 0
    rw [BitVec.toNat_add (scr₀ s₀ + _), BitVec.toNat_ofNat 128 64]
    omega
  apply WP.of_runBlock
  rw [restore, runBlock_cons, exec_load_d (show 128 < 2048 by decide) hal
    (by rw [h₂.a3, h₂.rd, h₂.wr]; exact hp.in_sav _), runStep_some, runBlock_nil]
  refine ⟨_, rfl, fun r hr => ?_, ?_, ?_⟩
  · rcases preserved_cases r hr with rfl | hk
    · rw [RegUpd.gpr_write_self, h₂.a3, h₂.sav]
    · rw [RegUpd.gpr_write_of_ne _ _ fun e => by subst e; simp [keepRegs] at hk, h₂.kept r hk]
  · rw [RegUpd.gpr_write_of_ne _ _ (by decide), h₂.kept _ (by decide)]
  · show stateAt s₂.mem (s₀.gpr .a0) = _
    exact h₂.state

/-- A state satisfying the precondition (with no blocks). -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a3 => 0x3000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x3000, 144⟩]

theorem compress_verified :
    Verified RISCV64.target Impl.Sha512.RISCV64.compress Proof.Sha512.compressRISCV64 := by
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

end VG.Proof.Sha512.RISCV64
