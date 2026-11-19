module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Idea.X86.Key
import VerifiedGarbage.Proof.Idea.Memory
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Algebra.Group.Nat.Defs
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Idea.X86.Lit
public import VerifiedGarbage.Proof.Idea.Inverse
public import VerifiedGarbage.Proof.Idea.Scratch32
public import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Idea.Memory32
import VerifiedGarbage.Proof.Idea.Arith32
import VerifiedGarbage.Proof.Idea.KeyBits
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import Batteries.Data.List.Lemmas
import Mathlib.Order.RelClasses
meta import VerifiedGarbage.Proof.Idea.X86.Key
meta import VerifiedGarbage.Proof.Idea.Inverse
meta import VerifiedGarbage.Proof.Idea.Scratch32
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Idea.Memory32
meta import VerifiedGarbage.Proof.Idea.Arith32
meta import VerifiedGarbage.Proof.Idea.KeyBits
meta import VerifiedGarbage.Proof.Idea.Memory
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Idea.X86.Lit
meta import Mathlib.Data.Finset.Attr
meta import Mathlib.Tactic.SetLike
meta import Batteries.Data.List.Lemmas
meta import Mathlib.Order.RelClasses
meta import Mathlib.Tactic.Finiteness.Attr
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Idea.Arith
import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Idea.Arith
meta import VerifiedGarbage.Proof.Framework.Bswap

/-! ### `Idea.X86.Invert`, which this module and modules that import it used -/

section

/-! ### `Idea.X86.Block`, which this module and modules that import it used -/

section

/-!
# IDEA on x86 (32-bit): a block

`cryptBlockWith_run`: `Impl.Idea.X86.cryptBlockWith pre` replaces the block
at the address in the scratch buffer's `dataSlot` with `Spec.Idea.cryptBlock`
of it under the subkeys at `esi`, writing no memory but the block and
`t₀`'s slot, keeping `esi` and `esp`, and leaves the block's address in
`eax` and what `pre` reads in `edx`: the interface a mode reuses it
through.
-/

@[expose] public section

namespace VG.Proof.Idea.X86

open VG VG.X86 VG.Impl.Idea.X86

/-! ## Words of bytes -/

theorem cat4 (b0 b1 b2 b3 : BitVec 8) (i : Nat) :
    (b0 ++ b1 ++ b2 ++ b3 : BitVec 32).getLsbD i =
      if i < 8 then b3.getLsbD i else if i < 16 then b2.getLsbD (i - 8)
      else if i < 24 then b1.getLsbD (i - 16) else b0.getLsbD (i - 24) := getLsbD_cat4 b0 b1 b2 b3 i
theorem cat2 (b0 b1 : BitVec 8) (i : Nat) :
    (b0 ++ b1 : BitVec 16).getLsbD i = if i < 8 then b1.getLsbD i else b0.getLsbD (i - 8) :=
  BitVec.getLsbD_append
theorem hi16 (b0 b1 b2 b3 : BitVec 8) :
    (b0 ++ b1 ++ b2 ++ b3 : BitVec 32) >>> 16 = (b0 ++ b1).setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_ushiftRight, cat4, BitVec.getLsbD_setWidth, cat2, decide_eq_true hi, Bool.true_and]
  by_cases h : i < 8
  · simp only [show ¬16 + i < 8 by omega_using [], show ¬16 + i < 16 by omega_using [], show 16 + i < 24 by omega_using [h], h,
      ite_true, ite_false, show 16 + i - 16 = i by omega_using []]
  · simp only [show ¬16 + i < 8 by omega_using [], show ¬16 + i < 16 by omega_using [], show ¬16 + i < 24 by omega_using [h], h,
      ite_false, show 16 + i - 24 = i - 8 by omega_using []]
theorem lo16 (b0 b1 b2 b3 : BitVec 8) :
    (b0 ++ b1 ++ b2 ++ b3 : BitVec 32) &&& 65535 = (b2 ++ b3).setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain hm : (65535 : BitVec 32).getLsbD i = decide (i < 16) := by
    rw [show (65535 : BitVec 32) = BitVec.ofNat 32 (2 ^ 16 - 1) from rfl, BitVec.getLsbD_ofNat]
    simp only [Nat.testBit_two_pow_sub_one, hi, decide_true, Bool.true_and]
  rw [BitVec.getLsbD_and, hm, cat4, BitVec.getLsbD_setWidth, cat2, decide_eq_true hi, Bool.true_and]
  by_cases h : i < 8
  · simp only [h, ite_true, show i < 16 by omega_using [h], decide_true, Bool.and_true]
  · by_cases h' : i < 16
    · simp only [h, h', ite_true, ite_false, decide_true, Bool.and_true]
    · simp only [h, h', ite_false, decide_false, Bool.and_false]
      exact (BitVec.getLsbD_of_ge _ _ (by omega_using [h'])).symm
theorem join16 (y₁ y₂ : BitVec 16) :
    (y₁.setWidth 32).rotateRight 16 ||| y₂.setWidth 32 = (y₁ ++ y₂ : BitVec 32) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_or, BitVec.getLsbD_rotateRight, BitVec.getLsbD_append, BitVec.getLsbD_setWidth]
  by_cases h : i < 16
  · simp only [h, ite_true, BitVec.getLsbD_setWidth, show 16 % 32 + i < 32 by omega_using [h],
      decide_true, Bool.true_and, hi]
    rw [BitVec.getLsbD_of_ge _ _ (by omega_using []), Bool.false_or]
  · simp only [h, ite_false, BitVec.getLsbD_setWidth, decide_eq_true hi, decide_true,
      Bool.true_and, show i - (32 - 16 % 32) < 32 by omega_using [hi], show i - (32 - 16 % 32) = i - 16 by omega_using []]
    rw [BitVec.getLsbD_of_ge y₂ _ (by omega_using [h]), Bool.or_false]

theorem bswap_readW' (m : Mem) (A : Addr) (k : Nat) :
    bswap (m.readW (A + BitVec.ofNat 64 k) 32) =
      (m (A + BitVec.ofNat 64 k) ++ m (A + BitVec.ofNat 64 (k + 1)) ++ m (A + BitVec.ofNat 64 (k + 2)) ++
        m (A + BitVec.ofNat 64 (k + 3)) : BitVec 32) := by
  rw [bswap_readW]
  simp only [show (1 : Addr) = BitVec.ofNat 64 1 from rfl, Offset.add_ofNat_add_ofNat]

/-- Byte `i` of a byte-reversed word is byte `3 - i` of the word. -/
theorem bswap_byte (w : BitVec 32) {i : Nat} (hi : i < 4) :
    (bswap w).extractLsb' (8 * i) 8 = w.extractLsb' (24 - 8 * i) 8 := by
  obtain h := byteRev32_extract w
  obtain e : ∀ j, j < 4 → (byteRev32 w).extractLsb' (8 * j) 8 =
      [w.extractLsb' 24 8, w.extractLsb' 16 8, w.extractLsb' 8 8, w.extractLsb' 0 8][j]! := by
    intro j hj
    rw [← h]
    simp [hj]
  rw [show bswap w = byteRev32 w from rfl, e i hi]
  obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega_using [hi]
  all_goals rfl

/-- The bytes of two words, high first. -/
theorem join_byte (y₁ y₂ : BitVec 16) {i : Nat} (hi : i < 4) :
    (y₁ ++ y₂ : BitVec 32).extractLsb' (24 - 8 * i) 8 =
      ((if i < 2 then y₁ else y₂) >>> (8 * (1 - i % 2))).setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_append, decide_eq_true ht, Bool.true_and]
  obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega_using [hi]
  · simp only [show ¬24 - 8 * 0 + t < 16 by omega_using [], show (0 : Nat) < 2 by omega_using [], ite_true, ite_false]
    congr 1; omega_using []
  · simp only [show ¬24 - 8 * 1 + t < 16 by omega_using [], show (1 : Nat) < 2 by omega_using [], ite_true, ite_false]
    congr 1; omega_using []
  · simp only [show 24 - 8 * 2 + t < 16 by omega_using [ht], show ¬(2 : Nat) < 2 by omega_using [], ite_true, ite_false,
      Bool.true_and]
  · simp only [show 24 - 8 * 3 + t < 16 by omega_using [ht], show ¬(3 : Nat) < 2 by omega_using [], ite_true, ite_false,
      Bool.true_and]

/-! ## Single instructions -/

theorem bswap_run (d : Reg) (s : State) :
    ∃ s', runBlock isa [.bswap d] s = some s' ∧ s'.gpr d = bswap (s.gpr d) ∧ Keep [d] s s' := by
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, Option.some.injEq, exists_eq_left',
    RegUpd.gpr_setReg_self, true_and]
  keep_tac

theorem shift_run (op : ShiftOp) (d : Reg) (n : Nat) (hn : 1 ≤ n ∧ n ≤ 31) (s : State) :
    ∃ s', runBlock isa [.shift op d n] s = some s' ∧
      s'.gpr d = (match op with | .ror => (s.gpr d).rotateRight n | .shr => s.gpr d >>> n) ∧
      Keep [d] s s' := by
  cases op <;>
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, execShift, hn, and_self, ↓reduceIte,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self, true_and] <;>
  keep_tac

/-- A 32-bit load at `[b + d]`. -/
theorem load_src {s : State} {b : Reg} {d : Nat} (h : InRegions (s.rd ++ s.wr) (addr (s.gpr b) d) 4) :
    readSrc s (.mem (at_ b d)) = some (s.mem.readW (addr (s.gpr b) d) 32) := by
  simp only [readSrc, State.load32]
  exact ite_eq_left h

theorem store_run (b r : Reg) (d : Nat) (s : State) (h : InRegions s.wr (addr (s.gpr b) d) 4) :
    ∃ s', runBlock isa [.store (at_ b d) r] s = some s' ∧
      s'.mem = s.mem.writeW (addr (s.gpr b) d) (s.gpr r) ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hin : InRegions s.wr (s.ea (at_ b d)) 4 := h
  simp only [runBlock_cons, isa, exec, State.store32, hin, ite_true, runStep_some, runBlock_nil]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Loading -/

/-- The block's address `P` is in `dataSlot` of the scratch buffer at `esi`;
the block (64-bit address `A`) does not wrap around and can be read. -/
structure BlockAt (z : Spec.Idea.Schedule) (P : BitVec 32) (A : Addr) (s : State) : Prop where
  key : KeyOk z s
  slot : s.mem.readW (addr (s.gpr .esi) dataSlot) 32 = P
  addr : P.setWidth 64 = A
  fit : P.toNat + 8 ≤ 2 ^ 32
  rd0 : InRegions (s.rd ++ s.wr) A 4
  rd4 : InRegions (s.rd ++ s.wr) (A + BitVec.ofNat 64 4) 4

theorem slot_src {z : Spec.Idea.Schedule} {s : State} (h : KeyOk z s) {d : Nat} (hd : d + 4 ≤ 4 * slots) :
    readSrc s (.mem (at_ .esi d)) = some (s.mem.readW (addr (s.gpr .esi) d) 32) :=
  load_src (by obtain ⟨R, hR, hc⟩ := h.slot hd; exact ⟨R, List.mem_append_right _ hR, hc⟩)

theorem addrP {P : BitVec 32} {A : Addr} (hA : P.setWidth 64 = A) (hf : P.toNat + 8 ≤ 2 ^ 32) {d : Nat}
    (hd : d < 8) : addr P d = A + BitVec.ofNat 64 d := by
  rw [addr_eq (by omega_using [hf, hd]), hA]

theorem load_run {z : Spec.Idea.Schedule} {P : BitVec 32} {A : Addr} (s : State) (h : BlockAt z P A s) :
    ∃ s', runBlock isa load s = some s' ∧
      Holds (Spec.Idea.decodeBlock (Spec.Idea.blockAt s.mem A)) .ecx .edi s' ∧
      Keep [.eax, .ebx, .ecx, .edi, .ebp] s s' := by
  have w (k : Nat) (hk : k < 4) := decodeBlock_blockAt s.mem A hk
  obtain ⟨s₁, h₁, v₁, e₁⟩ := mov_run .eax _ _ s (slot_src h.key (d := dataSlot) (by decide))
  rw [h.slot] at v₁
  obtain rd₀ : InRegions (s₁.rd ++ s₁.wr) (addr (s₁.gpr .eax) 0) 4 := by
    rw [e₁.rd, e₁.wr, v₁, addrP h.addr h.fit (by decide)]
    simpa using h.rd0
  obtain rd₄ : InRegions (s₁.rd ++ s₁.wr) (addr (s₁.gpr .eax) 4) 4 := by
    rw [e₁.rd, e₁.wr, v₁, addrP h.addr h.fit (by decide)]; exact h.rd4
  obtain ⟨s₂, h₂, v₂, e₂⟩ := mov_run .ebx _ _ s₁ (load_src rd₀)
  obtain ⟨s₃, h₃, v₃, e₃⟩ := bswap_run .ebx s₂
  obtain ⟨s₄, h₄, v₄, e₄⟩ := mov_run .ecx (.reg .ebx) _ s₃ rfl
  obtain ⟨s₅, h₅, v₅, e₅⟩ := shift_run .shr .ebx 16 (by decide) s₄
  obtain ⟨s₆, h₆, v₆, e₆⟩ := alu_run .and (by simp) .ecx (.imm 0xffff) 0xffff s₅ rfl
  obtain e₂₆ : Keep [.ebx, .ecx] s₂ s₆ :=
    (((e₃.weaken (by decide)).trans (e₄.weaken (by decide))).trans (e₅.weaken (by decide))).trans
      (e₆.weaken (by decide))
  obtain rd₄' : InRegions (s₆.rd ++ s₆.wr) (addr (s₆.gpr .eax) 4) 4 := by
    rw [e₂₆.rd, e₂₆.wr, e₂.rd, e₂.wr, e₂₆.reg .eax (by decide), e₂.reg .eax (by decide)]; exact rd₄
  obtain ⟨s₇, h₇, v₇, e₇⟩ := mov_run .edi _ _ s₆ (load_src rd₄')
  obtain ⟨s₈, h₈, v₈, e₈⟩ := bswap_run .edi s₇
  obtain ⟨s₉, h₉, v₉, e₉⟩ := mov_run .ebp (.reg .edi) _ s₈ rfl
  obtain ⟨s₁₀, h₁₀, v₁₀, e₁₀⟩ := shift_run .shr .edi 16 (by decide) s₉
  obtain ⟨s₁₁, h₁₁, v₁₁, e₁₁⟩ := alu_run .and (by simp) .ebp (.imm 0xffff) 0xffff s₁₀ rfl
  simp only [aluF] at v₆ v₁₁
  simp only at v₅ v₁₀
  obtain mem₆ : s₆.mem = s.mem := by rw [e₂₆.mem, e₂.mem, e₁.mem]
  obtain eax₆ : s₆.gpr .eax = P := by rw [e₂₆.reg .eax (by decide), e₂.reg .eax (by decide), v₁]
  obtain word0 : bswap (s₂.gpr .ebx) = (s.mem (A + BitVec.ofNat 64 0) ++ s.mem (A + BitVec.ofNat 64 1) ++
      s.mem (A + BitVec.ofNat 64 2) ++ s.mem (A + BitVec.ofNat 64 3) : BitVec 32) := by
    rw [v₂, e₁.mem, v₁, addrP h.addr h.fit (by decide), bswap_readW']
  obtain word1 : bswap (s₇.gpr .edi) = (s.mem (A + BitVec.ofNat 64 4) ++ s.mem (A + BitVec.ofNat 64 5) ++
      s.mem (A + BitVec.ofNat 64 6) ++ s.mem (A + BitVec.ofNat 64 7) : BitVec 32) := by
    rw [v₇, mem₆, eax₆, addrP h.addr h.fit (by decide), bswap_readW']
  refine ⟨s₁₁, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact run_append (run_append (run_append (run_append (run_append (run_append (run_append
      (run_append (run_append (run_append h₁ h₂) h₃) h₄) h₅) h₆) h₇) h₈) h₉) h₁₀) h₁₁
  · rw [e₁₁.reg .ebx (by decide), e₁₀.reg .ebx (by decide), e₉.reg .ebx (by decide), e₈.reg .ebx (by decide),
      e₇.reg .ebx (by decide), e₆.reg .ebx (by decide), v₅, e₄.reg .ebx (by decide), v₃, word0, hi16,
      w 0 (by decide)]
  · rw [e₁₁.reg .ecx (by decide), e₁₀.reg .ecx (by decide), e₉.reg .ecx (by decide), e₈.reg .ecx (by decide),
      e₇.reg .ecx (by decide), v₆, e₅.reg .ecx (by decide), v₄, v₃, word0, lo16, w 1 (by decide)]
  · rw [e₁₁.reg .edi (by decide), v₁₀, e₉.reg .edi (by decide), v₈, word1, hi16, w 2 (by decide)]
  · rw [v₁₁, e₁₀.reg .ebp (by decide), v₉, v₈, word1, lo16, w 3 (by decide)]
  · exact ((((e₁.weaken (by decide)).trans (e₂.weaken (by decide))).trans (e₂₆.weaken (by decide))).trans
      ((((((e₇.weaken (by decide)).trans (e₈.weaken (by decide))).trans (e₉.weaken (by decide))).trans
      (e₁₀.weaken (by decide))).trans (e₁₁.weaken (by decide)))))

/-! ## The rounds -/

theorem regB_succ (n : Nat) : regB (n + 1) = regC n := by
  unfold regB regC; by_cases h : n % 2 = 0 <;> simp [h, show (n + 1) % 2 = 0 ↔ ¬ n % 2 = 0 by omega_using []]

theorem regC_succ (n : Nat) : regC (n + 1) = regB n := by
  unfold regB regC; by_cases h : n % 2 = 0 <;> simp [h, show (n + 1) % 2 = 0 ↔ ¬ n % 2 = 0 by omega_using []]

theorem regBC_ok (n : Nat) : (regB n == .ecx && regC n == .edi || regB n == .edi && regC n == .ecx) = true := by
  unfold regB regC; by_cases h : n % 2 = 0 <;> simp [h]

theorem rounds_run (z : Spec.Idea.Schedule) (x : Spec.Idea.State) :
    ∀ n ≤ 8, ∀ s : State, Holds x .ecx .edi s → KeyOk z s →
      ∃ s', runBlock isa ((List.range n).flatMap round) s = some s' ∧
        Holds (roundsSpec z n x) (regB n) (regC n) s' ∧ KeepT roundWrites s s'
  | 0, _, s, hx, _ => ⟨s, by simp [runBlock_nil], hx, (Keep.refl _ _).toT⟩
  | n + 1, hn, s, hx, hk => by
    obtain ⟨s₁, h₁, x₁, e₁⟩ := rounds_run z x n (by omega_using [hn]) s hx hk
    obtain ⟨s₂, h₂, x₂, e₂⟩ := round_run n (by omega_using [hn]) (regB n) (regC n) (regBC_ok n) z _ s₁ x₁
      (hk.keepT e₁ (by decide))
    refine ⟨s₂, ?_, ?_, e₁.trans (by decide) e₂⟩
    · rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      exact run_append h₁ h₂
    · simp only [roundsSpec, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        regB_succ, regC_succ]
      exact x₂

/-! ## The output transformation -/

/-- The output words: `Y₁` in `ebx`, `Y₂` in `edi`, `Y₃` in `ecx`, `Y₄` in `ebp`. -/
structure OutHolds (y : Spec.Idea.State) (s : State) : Prop where
  ebx : s.gpr .ebx = (y.getD 0 0).setWidth 32
  edi : s.gpr .edi = (y.getD 1 0).setWidth 32
  ecx : s.gpr .ecx = (y.getD 2 0).setWidth 32
  ebp : s.gpr .ebp = (y.getD 3 0).setWidth 32

theorem output_run (z : Spec.Idea.Schedule) (x : Spec.Idea.State) (s : State) (hx : Holds x .ecx .edi s)
    (hk : KeyOk z s) :
    ∃ s', runBlock isa output s = some s' ∧
      OutHolds (Spec.Idea.output (z.getD 48 0) (z.getD 49 0) (z.getD 50 0) (z.getD 51 0) x) s' ∧
      Keep roundWrites s s' := by
  obtain ⟨s₁, h₁, v₁, e₁⟩ := mov_run .eax (.reg .ebx) _ s rfl
  obtain ⟨s₂, h₂, v₂, e₂⟩ := mulKey_run z 48 (by decide) s₁ (hk.keep e₁ (by decide))
  obtain ⟨s₃, h₃, v₃, e₃⟩ := mov_run .ebx (.reg .edx) _ s₂ rfl
  obtain e₀₃ : Keep [.eax, .ebx, .edx] s s₃ :=
    ((e₁.weaken (by decide)).trans (e₂.weaken (by decide))).trans (e₃.weaken (by decide))
  obtain ⟨s₄, h₄, v₄, e₄⟩ := mov_run .eax (.reg .ebp) _ s₃ rfl
  obtain ⟨s₅, h₅, v₅, e₅⟩ := mulKey_run z 51 (by decide) s₄ ((hk.keep e₀₃ (by decide)).keep e₄ (by decide))
  obtain ⟨s₆, h₆, v₆, e₆⟩ := mov_run .ebp (.reg .edx) _ s₅ rfl
  obtain e₀₆ : Keep [.eax, .ebx, .edx, .ebp] s s₆ :=
    (((e₀₃.weaken (by decide)).trans (e₄.weaken (by decide))).trans (e₅.weaken (by decide))).trans
      (e₆.weaken (by decide))
  obtain ⟨s₇, h₇, v₇, e₇⟩ := addKey_run z .edi 49 (by decide) s₆ (hk.keep e₀₆ (by decide))
  obtain ⟨s₈, h₈, v₈, e₈⟩ := addKey_run z .ecx 50 (by decide) s₇ ((hk.keep e₀₆ (by decide)).keep e₇ (by decide))
  refine ⟨s₈, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [output, mulKey]
    exact run_append (run_append (run_append (run_append (run_append (run_append
      (run_append h₁ h₂) h₃) h₄) h₅) h₆) h₇) h₈
  · rw [e₈.reg .ebx (by decide), e₇.reg .ebx (by decide), e₆.reg .ebx (by decide), e₅.reg .ebx (by decide),
      e₄.reg .ebx (by decide), v₃, v₂, v₁, hx.ebx, setWidth_setWidth16_32]
    rfl
  · rw [e₈.reg .edi (by decide), v₇, e₀₆.reg .edi (by decide), hx.c, setWidth_setWidth16_32]
    rfl
  · rw [v₈, e₇.reg .ecx (by decide), e₀₆.reg .ecx (by decide), hx.b, setWidth_setWidth16_32]
    rfl
  · rw [e₈.reg .ebp (by decide), e₇.reg .ebp (by decide), v₆, v₅, v₄, e₀₃.reg .ebp (by decide), hx.ebp,
      setWidth_setWidth16_32]
    rfl
  · exact ((e₀₆.weaken (by decide)).trans (e₇.weaken (by decide))).trans (e₈.weaken (by decide))

/-! ## Storing -/

/-- A 32-bit write at `A + 4` leaves the bytes `A … A + 3`. -/
theorem writeW4_other (m : Mem) (A : Addr) (v : BitVec 32) {i : Nat} (hi : i < 4) :
    (m.writeW (A + BitVec.ofNat 64 4) v) (A + BitVec.ofNat 64 i) = m (A + BitVec.ofNat 64 i) := by
  refine Mem.write_apply ?_
  rw [Offset.add_sub_add_left, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega_using [hi]

/-- Byte `i` of a 32-bit word written at `a`. -/
theorem writeW4_byte (m : Mem) (a : Addr) (v : BitVec 32) {i : Nat} (hi : i < 4) :
    (m.writeW a v) (a + BitVec.ofNat 64 i) = v.extractLsb' (8 * i) 8 := by
  rw [Mem.readW_byte (m.writeW a v) a hi, Mem.readW_writeW_self32]

theorem store_block (m : Mem) (A : Addr) (y : Spec.Idea.State) :
    Spec.Idea.blockAt ((m.writeW (A + BitVec.ofNat 64 0)
        (bswap ((y.getD 0 0 ++ y.getD 1 0 : BitVec 32)))).writeW (A + BitVec.ofNat 64 4)
        (bswap ((y.getD 2 0 ++ y.getD 3 0 : BitVec 32)))) A = Spec.Idea.encodeBlock y := by
  apply Vector.ext
  intro i hi
  simp only [Spec.Idea.blockAt, Vector.getElem_ofFn, encodeBlock_get _ hi]
  by_cases h4 : i < 4
  · rw [writeW4_other _ _ _ h4, show A + BitVec.ofNat 64 i = A + BitVec.ofNat 64 0 + BitVec.ofNat 64 i by
      rw [Offset.add_ofNat_add_ofNat, Nat.zero_add], writeW4_byte _ _ _ h4, bswap_byte _ h4, join_byte _ _ h4]
    obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega_using [h4]
    all_goals rfl
  · rw [show A + BitVec.ofNat 64 i = A + BitVec.ofNat 64 4 + BitVec.ofNat 64 (i - 4) by
      rw [Offset.add_ofNat_add_ofNat, show 4 + (i - 4) = i by omega_using [h4]], writeW4_byte _ _ _ (by omega_using [hi]),
      bswap_byte _ (by omega_using [hi]), join_byte _ _ (by omega_using [hi])]
    obtain rfl | rfl | rfl | rfl : i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega_using [hi, h4]
    all_goals rfl

/-! ## A block -/

/-- `ror r, 16; or r, s; bswap r`: two words, high first, byte-swapped. -/
theorem join_run (r q : Reg) (hrq : r ≠ q) (y₁ y₂ : Spec.Idea.Word) (s : State)
    (hr : s.gpr r = y₁.setWidth 32) (hq : s.gpr q = y₂.setWidth 32) :
    ∃ s', runBlock isa [.shift .ror r 16, .alu .or r (.reg q), .bswap r] s = some s' ∧
      s'.gpr r = bswap (y₁ ++ y₂ : BitVec 32) ∧ Keep [r] s s' := by
  obtain ⟨s₁, h₁, v₁, e₁⟩ := shift_run .ror r 16 (by decide) s
  obtain ⟨s₂, h₂, v₂, e₂⟩ := alu_run .or (by simp) r (.reg q) _ s₁ rfl
  obtain ⟨s₃, h₃, v₃, e₃⟩ := bswap_run r s₂
  refine ⟨s₃, run_append h₁ (run_append h₂ h₃), ?_, (e₁.trans e₂).trans e₃⟩
  simp only [aluF] at v₂
  simp only at v₁
  rw [v₃, v₂, v₁, e₁.reg q (by simpa using Ne.symm hrq), hr, hq, join16]

theorem cryptBlockWith_run (z : Spec.Idea.Schedule) (pre : List Instr) (R : BitVec 32 → Prop)
    {P : BitVec 32} {A : Addr} (s : State) (h : BlockAt z P A s)
    (hw0 : InRegions s.wr A 4) (hw4 : InRegions s.wr (A + BitVec.ofNat 64 4) 4)
    (hpre : ∀ t : State, t.gpr .esi = s.gpr .esi → t.rd = s.rd → t.wr = s.wr →
      Frame [⟨addr (s.gpr .esi) t0Slot, 4⟩] s.mem t.mem →
      ∃ t', runBlock isa pre t = some t' ∧ Keep [.edx] t t' ∧ R (t'.gpr .edx)) :
    ∃ s', runBlock isa (cryptBlockWith pre) s = some s' ∧
      Spec.Idea.blockAt s'.mem A = Spec.Idea.cryptBlock z (Spec.Idea.blockAt s.mem A) ∧
      Frame [⟨A, 8⟩, ⟨addr (s.gpr .esi) t0Slot, 4⟩] s.mem s'.mem ∧ s'.gpr .eax = P ∧
      s'.gpr .esi = s.gpr .esi ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      R (s'.gpr .edx) := by
  obtain ⟨s₁, h₁, x₁, e₁⟩ := load_run s h
  obtain ⟨s₂, h₂, x₂, e₂⟩ := rounds_run z _ 8 (by decide) s₁ x₁ (h.key.keep e₁ (by decide))
  obtain e₀₂ : KeepT roundWrites s s₂ := ((e₁.weaken (by decide)).toT).trans (by decide) e₂
  obtain ⟨s₃, h₃, x₃, e₃⟩ := output_run z _ s₂ x₂ (h.key.keepT e₀₂ (by decide))
  obtain e₀₃ : KeepT roundWrites s s₃ := e₀₂.trans (by decide) e₃.toT
  obtain esi₃ : s₃.gpr .esi = s.gpr .esi := e₀₃.reg .esi (by decide)
  obtain k₃ : KeyOk z s₃ := h.key.keepT e₀₃ (by decide)
  obtain slot₃ : s₃.mem.readW (addr (s₃.gpr .esi) dataSlot) 32 = P := by
    rw [esi₃, ← h.slot]
    refine e₀₃.frame.readW (r := ⟨addr (s.gpr .esi) dataSlot, 4⟩) (Region.contains_self _ _) (fun r hr => ?_)
      (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    have := h.key.fit
    rw [addr_eq (by simp only [dataSlot, slots] at *; omega_using [this]), addr_eq (by simp only [t0Slot, slots] at *; omega_using [this])]
    exact Offset.disjoint _ (by decide) (by decide) (by decide)
  obtain ⟨s₄, h₄, v₄, e₄⟩ := mov_run .eax _ _ s₃ (slot_src k₃ (d := dataSlot) (by decide))
  rw [slot₃] at v₄
  obtain ⟨s₅, h₅, e₅, r₅⟩ := hpre s₄ ((e₄.reg .esi (by decide)).trans esi₃) (e₄.rd.trans e₀₃.rd)
    (e₄.wr.trans e₀₃.wr) (by rw [e₄.mem]; exact e₀₃.frame)
  -- The stores.
  obtain y₀ : s₅.gpr .ebx = _ := (e₅.reg .ebx (by decide)).trans ((e₄.reg .ebx (by decide)).trans x₃.ebx)
  obtain y₁ : s₅.gpr .edi = _ := (e₅.reg .edi (by decide)).trans ((e₄.reg .edi (by decide)).trans x₃.edi)
  obtain y₂ : s₅.gpr .ecx = _ := (e₅.reg .ecx (by decide)).trans ((e₄.reg .ecx (by decide)).trans x₃.ecx)
  obtain y₃ : s₅.gpr .ebp = _ := (e₅.reg .ebp (by decide)).trans ((e₄.reg .ebp (by decide)).trans x₃.ebp)
  obtain eax₅ : s₅.gpr .eax = P := (e₅.reg .eax (by decide)).trans v₄
  obtain ⟨s₆, h₆, v₆, e₆⟩ := join_run .ebx .edi (by decide) _ _ s₅ y₀ y₁
  obtain wr₆ : s₆.wr = s.wr := by rw [e₆.wr, e₅.wr, e₄.wr, e₀₃.wr]
  obtain eax₆ : s₆.gpr .eax = P := (e₆.reg .eax (by decide)).trans eax₅
  obtain ⟨s₇, h₇, m₇, g₇, rd₇, wr₇⟩ := store_run .eax .ebx 0 s₆
    (by rw [eax₆, addrP h.addr h.fit (by decide), wr₆]; simpa using hw0)
  obtain ⟨s₈, h₈, v₈, e₈⟩ := join_run .ecx .ebp (by decide) _ _ s₇
    (by rw [g₇, e₆.reg .ecx (by decide), y₂]) (by rw [g₇, e₆.reg .ebp (by decide), y₃])
  obtain eax₈ : s₈.gpr .eax = P := by rw [e₈.reg .eax (by decide), g₇, eax₆]
  obtain ⟨s₉, h₉, m₉, g₉, rd₉, wr₉⟩ := store_run .eax .ecx 4 s₈
    (by rw [eax₈, addrP h.addr h.fit (by decide), e₈.wr, wr₇, wr₆]; exact hw4)
  obtain mem₅ : s₅.mem = s₃.mem := by rw [e₅.mem, e₄.mem]
  obtain hm : s₉.mem = (s₃.mem.writeW (A + BitVec.ofNat 64 0)
      (bswap (((Spec.Idea.output (z.getD 48 0) (z.getD 49 0) (z.getD 50 0) (z.getD 51 0)
        (roundsSpec z 8 (Spec.Idea.decodeBlock (Spec.Idea.blockAt s.mem A)))).getD 0 0 ++
        (Spec.Idea.output (z.getD 48 0) (z.getD 49 0) (z.getD 50 0) (z.getD 51 0)
        (roundsSpec z 8 (Spec.Idea.decodeBlock (Spec.Idea.blockAt s.mem A)))).getD 1 0 : BitVec 32)))).writeW
      (A + BitVec.ofNat 64 4)
      (bswap (((Spec.Idea.output (z.getD 48 0) (z.getD 49 0) (z.getD 50 0) (z.getD 51 0)
        (roundsSpec z 8 (Spec.Idea.decodeBlock (Spec.Idea.blockAt s.mem A)))).getD 2 0 ++
        (Spec.Idea.output (z.getD 48 0) (z.getD 49 0) (z.getD 50 0) (z.getD 51 0)
        (roundsSpec z 8 (Spec.Idea.decodeBlock (Spec.Idea.blockAt s.mem A)))).getD 3 0 : BitVec 32))) := by
    rw [m₉, e₈.mem, m₇, e₆.mem, mem₅, eax₈, eax₆, addrP h.addr h.fit (by decide),
      addrP h.addr h.fit (by decide), v₈, v₆]
  refine ⟨s₉, ?_, ?_, ?_, by rw [g₉, eax₈], ?_, ?_, by rw [rd₉, e₈.rd, rd₇, e₆.rd, e₅.rd, e₄.rd, e₀₃.rd],
    by rw [wr₉, e₈.wr, wr₇, wr₆], ?_⟩
  · have hs : runBlock isa store s₅ = some s₉ :=
      run_append (a := [_, _, _]) h₆ (run_append (a := [_]) h₇ (run_append (a := [_, _, _]) h₈ h₉))
    exact run_append (run_append (run_append (run_append (run_append h₁ h₂) h₃) h₄) h₅) hs
  · rw [hm, store_block, Spec.Idea.cryptBlock, crypt_eq]
  · rw [hm]
    obtain hf : Frame [⟨A, 8⟩, ⟨addr (s.gpr .esi) t0Slot, 4⟩] s.mem s₃.mem :=
      e₀₃.frame.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
    refine (hf.writeW (List.mem_cons_self) _ (Offset.contains_base A (by decide) (by decide))).writeW
      (List.mem_cons_self) _ (Offset.contains_base A (by decide) (by decide))
  · rw [g₉, e₈.reg .esi (by decide), g₇, e₆.reg .esi (by decide), e₅.reg .esi (by decide),
      e₄.reg .esi (by decide), esi₃]
  · rw [g₉, e₈.reg .esp (by decide), g₇, e₆.reg .esp (by decide), e₅.reg .esp (by decide),
      e₄.reg .esp (by decide), e₀₃.reg .esp (by decide)]
  · rw [g₉, e₈.reg .edx (by decide), g₇, e₆.reg .edx (by decide)]; exact r₅

end VG.Proof.Idea.X86

end

end

/-!
# IDEA decryption subkeys on x86 (32-bit)

With the scratch buffer as an argument (four words), `invertKey` saves
`ebx`, `esi`, `edi`, `ebp` in it and restores them at the end. Each
decryption subkey is a copy, the negation or the inverse of an encryption
subkey (at `esi`; `invertKey_getD`, `Impl.Idea.invOp`), computed into `ecx`
(`invWord_ok`; the inverse by a loop of fifteen steps of `t := (t ⊙ t) ⊙ a`,
`invLoop_ok`) and stored a byte at a time at `edi` (`invStore_run`).
-/

@[expose] public section

namespace VG.Proof.Idea.X86

open VG VG.X86 VG.Impl.Idea.X86 VG.Impl.Idea

/-! ## Reading the subkeys -/

/-- The encryption subkeys `z` at `esi`, readable, not wrapping around. -/
structure SchedOk (z : Spec.Idea.Schedule) (s : State) : Prop where
  read : ⟨(s.gpr .esi).setWidth 64, 104⟩ ∈ s.rd ++ s.wr
  fit : (s.gpr .esi).toNat + 104 ≤ 2 ^ 32
  sched : Spec.Idea.scheduleAt s.mem ((s.gpr .esi).setWidth 64) = z

theorem SchedOk.word {z : Spec.Idea.Schedule} {s : State} (h : SchedOk z s) {d : Nat} (hd : d + 4 ≤ 104) :
    readSrc s (.mem (at_ .esi d)) = some (s.mem.readW ((s.gpr .esi).setWidth 64 + BitVec.ofNat 64 d) 32) := by
  obtain ha := addr_eq (x := s.gpr .esi) (k := d) (by have := h.fit; omega_arith)
  rw [load_src (by rw [ha]; exact ⟨_, h.read, Offset.contains_base _ hd (by omega_arith)⟩), ha]

/-- `loadKey r k`: subkey `k` in the low 16 bits of `r`. -/
theorem loadKey_run (z : Spec.Idea.Schedule) (r : Reg) (k : Nat) (hk52 : k < 52) (s : State)
    (h : SchedOk z s) :
    ∃ s', runBlock isa (loadKey r k) s = some s' ∧ (s'.gpr r).setWidth 16 = z.getD k 0 ∧
      Keep [r] s s' := by
  unfold loadKey
  split
  · rename_i hk; subst hk
    obtain ⟨s₁, h₁, v₁, e₁⟩ := mov_run r _ _ s (h.word (d := 100) (by decide))
    obtain ⟨s₂, h₂, v₂, e₂⟩ := shift_run .shr r 16 (by decide) s₁
    refine ⟨s₂, run_append h₁ h₂, ?_, e₁.trans e₂⟩
    simp only at v₂
    rw [v₂, v₁, subkey_hi32, h.sched]
  · obtain ⟨s₁, h₁, v₁, e₁⟩ := mov_run r _ _ s (h.word (d := 2 * k) (by omega_arith))
    exact ⟨s₁, h₁, by rw [v₁, subkey_lo32 _ _ hk52, h.sched], e₁⟩

/-! ## The inverse -/

theorem sub1_run (r : Reg) (s : State) :
    ∃ s', runBlock isa [.alu .sub r (.imm 1)] s = some s' ∧ s'.gpr r = s.gpr r - 1 ∧
      s'.zf = some (s.gpr r - 1 == 0) ∧ Keep [r] s s' := by
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, execAlu, readSrc, Option.bind_some,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self, true_and]
  exact ⟨rfl, by keep_tac⟩

theorem invStep_run (t : State) :
    ∃ t', runBlock isa invStep t = some t' ∧
      t'.gpr .ecx = (Spec.Idea.mul (Spec.Idea.mul ((t.gpr .ecx).setWidth 16) ((t.gpr .ecx).setWidth 16))
        ((t.gpr .ebx).setWidth 16)).setWidth 32 ∧
      t'.gpr .ebp = t.gpr .ebp - 1 ∧ t'.zf = some (t.gpr .ebp - 1 == 0) ∧
      Keep [.eax, .ecx, .edx, .ebp] t t' := by
  obtain ⟨t₁, h₁, v₁, e₁⟩ := mov_run .eax (.reg .ecx) _ t rfl
  obtain ⟨t₂, h₂, v₂, e₂⟩ := mul_run (.reg .ecx) (t₁.gpr .ecx) t₁
    (fun u _ _ _ hg => by simp only [readSrc, hg .ecx (by decide)])
  obtain ⟨t₃, h₃, v₃, e₃⟩ := mov_run .eax (.reg .edx) _ t₂ rfl
  obtain ⟨t₄, h₄, v₄, e₄⟩ := mul_run (.reg .ebx) (t₃.gpr .ebx) t₃
    (fun u _ _ _ hg => by simp only [readSrc, hg .ebx (by decide)])
  obtain ⟨t₅, h₅, v₅, e₅⟩ := mov_run .ecx (.reg .edx) _ t₄ rfl
  obtain ⟨t₆, h₆, v₆, z₆, e₆⟩ := sub1_run .ebp t₅
  obtain e₀₄ : Keep [.eax, .edx] t t₄ := (((e₁.weaken (by decide)).trans e₂).trans (e₃.weaken (by decide))).trans e₄
  obtain ebp₅ : t₅.gpr .ebp = t.gpr .ebp := (e₅.reg .ebp (by decide)).trans (e₀₄.reg .ebp (by decide))
  refine ⟨t₆, ?_, ?_, by rw [v₆, ebp₅], by rw [z₆, ebp₅], ?_⟩
  · unfold invStep
    exact run_append (run_append (run_append (run_append h₁ h₂) h₃) h₄) (run_append (a := [_]) h₅ h₆)
  · rw [e₆.reg .ecx (by decide), v₅, v₄, v₃, v₂, v₁, e₃.reg .ebx (by decide), e₂.reg .ebx (by decide),
      e₁.reg .ebx (by decide), e₁.reg .ecx (by decide), setWidth_setWidth16_32]
  · exact ((e₀₄.weaken (by decide)).trans (e₅.weaken (by decide))).trans (e₆.weaken (by decide))

/-- `c` steps remain: `ecx` holds `chain a (15 - c)` in its low word. -/
structure InvLoop (a : Spec.Idea.Word) (t₀ : State) (c : Nat) (t : State) : Prop where
  pos : 1 ≤ c
  le : c ≤ 15
  ebp : t.gpr .ebp = BitVec.ofNat 32 c
  ebx : (t.gpr .ebx).setWidth 16 = a
  ecx : (t.gpr .ecx).setWidth 16 = chain a (15 - c)
  keep : Keep [.eax, .ecx, .edx, .ebp] t₀ t

theorem invLoop_ok (a : Spec.Idea.Word) (t₀ : State) (c : Nat) (t : State) (hi : InvLoop a t₀ c t) :
    WP isa (.loop (.block invStep) .ne) t (fun t' =>
      t'.gpr .ecx = (Spec.Idea.inv a).setWidth 32 ∧ Keep [.eax, .ecx, .edx, .ebp] t₀ t') := by
  refine WP.loop (M := isa) (InvLoop a t₀) (fun c t hi => ?_) c t hi
  obtain ⟨t', h', ecx', ebp', z', e'⟩ := invStep_run t
  refine WP.of_runBlock ⟨t', h', ?_⟩
  obtain hv : t'.gpr .ecx = (chain a (15 - c + 1)).setWidth 32 := by
    rw [ecx', hi.ecx, hi.ebx]; rfl
  obtain hc : t'.gpr .ebp = BitVec.ofNat 32 (c - 1) := by
    rw [ebp', hi.ebp]
    apply BitVec.eq_of_toNat_eq
    have := hi.pos; have := hi.le
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl]
    omega_arith
  obtain hev : isa.eval .ne t' = some (decide (c - 1 ≠ 0)) := by
    show t'.zf.map (!·) = _
    rw [z', ← ebp', hc, Option.map_some]
    congr 1
    have := hi.le
    by_cases h0 : c - 1 = 0
    · simp only [h0]; rfl
    · have hne : BitVec.ofNat 32 (c - 1) ≠ 0 := fun h => h0 (by
        have := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at this
        exact this)
      rw [show (BitVec.ofNat 32 (c - 1) == 0) = false from by simpa using hne]
      simp [h0]
  obtain keep' : Keep [.eax, .ecx, .edx, .ebp] t₀ t' := hi.keep.trans e'
  by_cases hlast : c = 1
  · subst hlast
    left
    refine ⟨hev, ?_, keep'⟩
    rw [hv, show 15 - 1 + 1 = 15 from rfl, chain_inv]
  · right
    have := hi.pos; have := hi.le
    refine ⟨by rw [hev]; simp only [ne_eq, Option.some.injEq, decide_eq_true_eq]; omega_arith,
      c - 1, by omega_arith, by omega_arith, by omega_arith, hc, ?_, ?_, keep'⟩
    · rw [e'.reg .ebx (by decide)]; exact hi.ebx
    · rw [hv, setWidth_setWidth16_32, show 15 - c + 1 = 15 - (c - 1) by omega_arith]

/-- The registers computing a decryption subkey writes. -/
abbrev invWrites : List Reg := [.eax, .ebx, .ecx, .edx, .ebp]

theorem invWord_ok (z : Spec.Idea.Schedule) {n : Nat} (hn : n < 52) (t : State) (hz : SchedOk z t) :
    WP isa (invWord n) t (fun t' =>
      t'.gpr .ecx = ((Spec.Idea.invertKey z).getD n 0).setWidth 32 ∧ Keep invWrites t t') := by
  rw [invertKey_getD z hn]
  obtain hk := invOp_lt hn
  unfold invWord
  rcases hop : invOp n with ⟨op, k⟩
  rw [hop] at hk
  cases op with
  | copy =>
    obtain ⟨t₁, h₁, v₁, e₁⟩ := loadKey_run z .ecx k hk t hz
    obtain ⟨t₂, h₂, v₂, e₂⟩ := alu_run .and (by simp) .ecx (.imm 0xffff) 0xffff t₁ rfl
    refine WP.of_runBlock ⟨t₂, run_append h₁ h₂, ?_, (e₁.weaken (by decide)).trans (e₂.weaken (by decide))⟩
    simp only [aluF] at v₂
    rw [v₂, mask32_setWidth, v₁]; rfl
  | neg =>
    obtain ⟨t₁, h₁, v₁, e₁⟩ := loadKey_run z .edx k hk t hz
    obtain ⟨t₂, h₂, v₂, e₂⟩ := mov_run .ecx (.imm 0) 0 t₁ rfl
    obtain ⟨t₃, h₃, v₃, e₃⟩ := alu_run .sub (by simp) .ecx (.reg .edx) _ t₂ rfl
    obtain ⟨t₄, h₄, v₄, e₄⟩ := alu_run .and (by simp) .ecx (.imm 0xffff) 0xffff t₃ rfl
    refine WP.of_runBlock ⟨t₄, run_append h₁ (run_append h₂ (run_append h₃ h₄)), ?_, ?_⟩
    · simp only [aluF] at v₃ v₄
      rw [v₄, v₃, v₂, e₂.reg .edx (by decide), neg_mask32, v₁]; rfl
    · exact (((e₁.weaken (by decide)).trans (e₂.weaken (by decide))).trans (e₃.weaken (by decide))).trans
        (e₄.weaken (by decide))
  | inv =>
    apply WP.seq
    obtain ⟨t₁, h₁, v₁, e₁⟩ := loadKey_run z .ebx k hk t hz
    obtain ⟨t₂, h₂, v₂, e₂⟩ := mov_run .ecx (.reg .ebx) _ t₁ rfl
    obtain ⟨t₃, h₃, v₃, e₃⟩ := mov_run .ebp (.imm 15) 15 t₂ rfl
    refine WP.of_runBlock ⟨t₃, run_append h₁ (run_append h₂ h₃), ?_⟩
    obtain ebx₃ : t₃.gpr .ebx = t₁.gpr .ebx := by rw [e₃.reg .ebx (by decide), e₂.reg .ebx (by decide)]
    refine WP.mono (invLoop_ok (z.getD k 0) t₃ 15 t₃ ⟨by decide, by decide, v₃, by rw [ebx₃, v₁],
      by rw [e₃.reg .ecx (by decide), v₂, v₁]; rfl, Keep.refl _ _⟩) fun t₄ h₄ => ?_
    obtain ⟨ecx₄, e₄⟩ := h₄
    refine ⟨ecx₄, ?_⟩
    exact (((e₁.weaken (by decide)).trans (e₂.weaken (by decide))).trans (e₃.weaken (by decide))).trans
      (e₄.weaken (by decide))

/-! ## Storing a subkey -/

theorem writeW8_self (m : Mem) (a : Addr) (v : BitVec 8) : (m.writeW a v) a = v := by
  simp only [Mem.writeW, Mem.write, BitVec.sub_self, BitVec.toNat_zero, Nat.reduceDiv,
    Nat.zero_lt_one, ite_true, Nat.mul_zero]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi]

theorem writeW8_ne (m : Mem) (O : Addr) (v : BitVec 8) {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64)
    (h : i ≠ j) : (m.writeW (O + BitVec.ofNat 64 j) v) (O + BitVec.ofNat 64 i) = m (O + BitVec.ofNat 64 i) := by
  refine Mem.write_apply ?_
  rw [Offset.add_sub_add_left, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega_arith

theorem split16 (x : BitVec 16) : ((x >>> 8).setWidth 8 ++ x.setWidth 8 : BitVec 16) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_append]
  by_cases h : i < 8
  · simp [h]
  · simp only [h, ite_false, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
      show i - 8 < 8 by omega_arith, decide_true, Bool.true_and]
    congr 1; omega_arith

theorem store8_run (b : Reg) (d : Nat) (r : Reg8) (s : State) (h : InRegions s.wr (addr (s.gpr b) d) 1) :
    ∃ s', runBlock isa [.store8 (at_ b d) r] s = some s' ∧
      s'.mem = s.mem.writeW (addr (s.gpr b) d) ((s.gpr r.reg).setWidth 8) ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hin : InRegions s.wr (s.ea (at_ b d)) 1 := h
  simp only [runBlock_cons, isa, exec, State.store8, hin, ite_true, runStep_some, runBlock_nil]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

/-- Decryption subkey `n` of `z`. -/
abbrev dk (z : Spec.Idea.Schedule) (n : Nat) : Spec.Idea.Word := (Spec.Idea.invertKey z).getD n 0

/-- The output (104 bytes at `edi`, address `O`) writable, not wrapping around. -/
structure OutOk (O : Addr) (s : State) : Prop where
  wr : ⟨O, 104⟩ ∈ s.wr
  addr : (s.gpr .edi).setWidth 64 = O
  fit : (s.gpr .edi).toNat + 104 ≤ 2 ^ 32

theorem invStore_run {O : Addr} (n : Nat) (hn : n < 52) (v : Spec.Idea.Word) (s : State) (ho : OutOk O s)
    (hv : s.gpr .ecx = v.setWidth 32) :
    ∃ s', runBlock isa (invStore n) s = some s' ∧
      s'.mem = (s.mem.writeW (O + BitVec.ofNat 64 (2 * n)) (v.setWidth 8)).writeW
        (O + BitVec.ofNat 64 (2 * n + 1)) ((v >>> 8).setWidth 8) ∧ Keep [.ecx] { s with mem := s'.mem } s' := by
  obtain ha : ∀ d, d < 104 → addr (s.gpr .edi) d = O + BitVec.ofNat 64 d := fun d hd => by
    rw [addr_eq (by have := ho.fit; omega_arith), ho.addr]
  obtain ⟨s₁, h₁, m₁, g₁, rd₁, wr₁⟩ := store8_run .edi (2 * n) .cl s
    (by rw [ha _ (by omega_arith)]; exact ⟨_, ho.wr, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
  obtain ⟨s₂, h₂, v₂, e₂⟩ := shift_run .shr .ecx 8 (by decide) s₁
  obtain edi₂ : s₂.gpr .edi = s.gpr .edi := by rw [e₂.reg .edi (by decide), g₁]
  obtain ⟨s₃, h₃, m₃, g₃, rd₃, wr₃⟩ := store8_run .edi (2 * n + 1) .cl s₂
    (by rw [edi₂, ha _ (by omega_arith), e₂.wr, wr₁]; exact ⟨_, ho.wr, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
  refine ⟨s₃, run_append h₁ (run_append h₂ h₃), ?_, ⟨fun q hq => ?_, rfl, ?_, ?_⟩⟩
  · simp only at v₂
    rw [m₃, e₂.mem, m₁, edi₂, ha _ (by omega_arith), ha _ (by omega_arith)]
    simp only [Reg8.reg]
    rw [v₂, g₁, hv, lo8_32, hi8_32]
  · simp only [List.mem_singleton] at hq
    rw [g₃, e₂.reg q (by simpa using hq), g₁]
  · show s₃.rd = s.rd; rw [rd₃, e₂.rd, rd₁]
  · show s₃.wr = s.wr; rw [wr₃, e₂.wr, wr₁]

/-! ## All the subkeys -/

/-- After `n` decryption subkeys, from `s₀` (subkeys at `esi`, output at `O`). -/
structure SInv (z : Spec.Idea.Schedule) (O : Addr) (s₀ : State) (n : Nat) (t : State) : Prop where
  keep : Keep invWrites s₀ { t with mem := s₀.mem }
  frame : Frame [⟨O, 2 * n⟩] s₀.mem t.mem
  words : ∀ i < n, t.mem (O + BitVec.ofNat 64 (2 * i + 1)) ++ t.mem (O + BitVec.ofNat 64 (2 * i)) = dk z i

theorem SInv.ok {z : Spec.Idea.Schedule} {O : Addr} {s₀ t : State} {n : Nat} (hi : SInv z O s₀ n t)
    (hz : SchedOk z s₀) (ho : OutOk O s₀) (hsep : Region.Disjoint ⟨(s₀.gpr .esi).setWidth 64, 104⟩ ⟨O, 104⟩)
    (hn : n ≤ 52) : SchedOk z t ∧ OutOk O t := by
  obtain esi : t.gpr .esi = s₀.gpr .esi := hi.keep.reg .esi (by decide)
  obtain edi : t.gpr .edi = s₀.gpr .edi := hi.keep.reg .edi (by decide)
  refine ⟨⟨by rw [esi, hi.keep.rd, hi.keep.wr]; exact hz.read, by rw [esi]; exact hz.fit, ?_⟩,
    ⟨by rw [hi.keep.wr]; exact ho.wr, by rw [edi]; exact ho.addr, by rw [edi]; exact ho.fit⟩⟩
  rw [esi, ← hz.sched]
  exact scheduleAt_congr (frame_bytes hi.frame (by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact hsep.sub_right (Region.sub_prefix (by omega_arith))) (by decide))

theorem subkey_ok (z : Spec.Idea.Schedule) {O : Addr} (s₀ : State) (hz : SchedOk z s₀) (ho : OutOk O s₀)
    (hsep : Region.Disjoint ⟨(s₀.gpr .esi).setWidth 64, 104⟩ ⟨O, 104⟩) (n : Nat) (hn : n < 52) (t : State)
    (hi : SInv z O s₀ n t) {rest : Prog isa} {Q : State → Prop}
    (hrest : ∀ t', SInv z O s₀ (n + 1) t' → WP isa rest t' Q) :
    WP isa (.seq (invWord n) (.seq (.block (invStore n)) rest)) t Q := by
  obtain ⟨hz', ho'⟩ := hi.ok hz ho hsep (by omega_arith)
  apply WP.seq
  refine WP.mono (invWord_ok z hn t hz') fun t₁ h₁ => ?_
  obtain ⟨v₁, e₁⟩ := h₁
  apply WP.seq
  obtain ho₁ : OutOk O t₁ := ⟨by rw [e₁.wr]; exact ho'.wr, by rw [e₁.reg .edi (by decide)]; exact ho'.addr,
    by rw [e₁.reg .edi (by decide)]; exact ho'.fit⟩
  obtain ⟨t₂, h₂, m₂, e₂⟩ := invStore_run n hn _ t₁ ho₁ v₁
  refine WP.of_runBlock ⟨t₂, h₂, hrest t₂ ⟨?_, ?_, fun i hin => ?_⟩⟩
  · refine ⟨fun q hq => ?_, rfl, ?_, ?_⟩
    · show t₂.gpr q = s₀.gpr q
      rw [e₂.reg q (fun h => hq (by simp at h; simp [h])), e₁.reg q hq]
      exact hi.keep.reg q hq
    · show t₂.rd = s₀.rd; rw [e₂.rd, e₁.rd]; exact hi.keep.rd
    · show t₂.wr = s₀.wr; rw [e₂.wr, e₁.wr]; exact hi.keep.wr
  · rw [m₂, e₁.mem]
    refine ((hi.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega_arith) (by omega_arith))).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega_arith) (by omega_arith))
    simp only [List.mem_singleton] at hr; subst hr
    exact Region.sub_prefix (by omega_arith)
  · rw [m₂, e₁.mem]
    by_cases he : i = n
    · subst he
      rw [writeW8_self, writeW8_ne _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), writeW8_self, split16]
    · rw [writeW8_ne _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), writeW8_ne _ _ _ (by omega_arith) (by omega_arith) (by omega_arith),
        writeW8_ne _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), writeW8_ne _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
      exact hi.words i (by omega_arith)

/-- Subkeys `q … q + n - 1`. -/
def subkeys (q n : Nat) : Prog isa :=
  (List.range' q n).foldr (fun n rest => .seq (invWord n) (.seq (.block (invStore n)) rest)) (.block [])

theorem subkeys_ok (z : Spec.Idea.Schedule) {O : Addr} (s₀ : State) (hz : SchedOk z s₀) (ho : OutOk O s₀)
    (hsep : Region.Disjoint ⟨(s₀.gpr .esi).setWidth 64, 104⟩ ⟨O, 104⟩) :
    ∀ n q, q + n = 52 → ∀ t, SInv z O s₀ q t → WP isa (subkeys q n) t (SInv z O s₀ 52)
  | 0, q, h, t, hi => by
    rw [Nat.add_zero] at h; subst h
    exact WP.block_nil hi
  | n + 1, q, h, t, hi => by
    simp only [subkeys, List.range'_succ, List.foldr_cons]
    exact subkey_ok z s₀ hz ho hsep q (by omega_arith) t hi fun t₁ h₁ =>
      subkeys_ok z s₀ hz ho hsep n (q + 1) (by omega_arith) t₁ h₁

theorem invertKey_eq : invertKey =
    .seq (.block (([.mov .eax (.mem (argOp 2))] : List Instr) ++ saveAt .eax 0 ++
      ([.mov .esi (.mem (argOp 0)), .mov .edi (.mem (argOp 1))] : List Instr)))
    (.seq (subkeys 0 52) (.block (([.mov .eax (.mem (argOp 2))] : List Instr) ++ restoreAt .eax 0))) :=
  rfl

/-! ## The function -/

/-- `vg_idea_invert_key` on x86, with the scratch buffer (16 bytes) as its
third argument. -/
def invertContract : Contract isa where
  pre s :=
    let sched : Region := ⟨(arg s 0).setWidth 64, 104⟩
    let out : Region := ⟨(arg s 1).setWidth 64, 104⟩
    let scratch : Region := ⟨(arg s 2).setWidth 64, 16⟩
    let args : Region := ⟨argAddr s 0, 12⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [sched, args] ∧ s.wr = [out, scratch] ∧ sched.Disjoint out ∧ sched.Disjoint scratch ∧
      out.Disjoint scratch ∧ args.Disjoint out ∧ args.Disjoint scratch ∧ ret.Disjoint out ∧
      ret.Disjoint scratch ∧ (arg s 0).toNat + 104 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 104 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 16 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 16 ≤ 2 ^ 32
  post s s' := Spec.Idea.scheduleAt s'.mem ((arg s 1).setWidth 64) =
    Spec.Idea.invertKey (Spec.Idea.scheduleAt s.mem ((arg s 0).setWidth 64))
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 3, arg s₁ i = arg s₂ i

/-- The arguments read the same after writes outside them. -/
theorem arg_frame {s t : State} {rs : List Region} {n : Nat} (hf : Frame rs s.mem t.mem)
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨argAddr s 0, n⟩ r) (hesp : t.gpr .esp = s.gpr .esp)
    (hfit : (s.gpr .esp).toNat + 4 + n ≤ 2 ^ 32) {i : Nat} (hi : 4 * i + 4 ≤ n) : arg t i = arg s i := by
  obtain ha : argAddr s i = argAddr s 0 + BitVec.ofNat 64 (4 * i) := by
    simp only [argAddr]
    rw [show (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 = addr (s.gpr .esp) (4 + 4 * i) from rfl,
      show (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (s.gpr .esp) 4 from rfl,
      addr_eq (by omega_arith), addr_eq (by omega_arith), Offset.add_ofNat_add_ofNat]
  simp only [arg, show argAddr t i = argAddr s i by simp only [argAddr, hesp]]
  rw [ha]
  exact hf.readW (Offset.contains_base _ (by omega_arith) (by omega_arith)) hd (by decide)

theorem invert_wp (s : State) (hs : invertContract.pre s) :
    WP isa invertKey s (fun s' => abiPreserved s s' ∧ invertContract.post s s') := by
  obtain ⟨hrd, hwr, dSO, dSB, dOB, dAO, dAB, dRO, dRB, fitS, fitO, fitB, fitSp⟩ := hs
  obtain hargs : ⟨argAddr s 0, 12⟩ ∈ s.rd := by rw [hrd]; simp
  rw [invertKey_eq]
  -- The prologue.
  obtain ⟨s₁, h₁, v₁, e₁⟩ := mov_run .eax _ _ s (arg_src (i := 2) (by decide) hargs (by omega_arith))
  obtain hB : ∀ d, d + 4 ≤ 16 → addr (s₁.gpr .eax) d = (arg s 2).setWidth 64 + BitVec.ofNat 64 d :=
    fun d hd => by rw [v₁, addr_eq (by omega_arith)]
  obtain inB : ∀ d, d + 4 ≤ 16 → ∀ t : State, t.wr = s.wr → InRegions t.wr (addr (s₁.gpr .eax) d) 4 :=
    fun d hd t ht => by
      rw [hB d hd, ht, hwr]
      exact ⟨_, by simp, Offset.contains_base _ hd (by omega_arith)⟩
  obtain ⟨s₂, h₂, m₂, g₂, rd₂, wr₂⟩ := store_run .eax .ebx 0 s₁ (inB 0 (by decide) _ e₁.wr)
  obtain ⟨s₃, h₃, m₃, g₃, rd₃, wr₃⟩ := store_run .eax .esi 4 s₂
    (by rw [g₂]; exact inB 4 (by decide) _ (by rw [wr₂, e₁.wr]))
  obtain ⟨s₄, h₄, m₄, g₄, rd₄, wr₄⟩ := store_run .eax .edi 8 s₃
    (by rw [g₃, g₂]; exact inB 8 (by decide) _ (by rw [wr₃, wr₂, e₁.wr]))
  obtain ⟨s₅, h₅, m₅, g₅, rd₅, wr₅⟩ := store_run .eax .ebp 12 s₄
    (by rw [g₄, g₃, g₂]; exact inB 12 (by decide) _ (by rw [wr₄, wr₃, wr₂, e₁.wr]))
  obtain g₁₅ : s₅.gpr = s₁.gpr := by rw [g₅, g₄, g₃, g₂]
  obtain rd₁₅ : s₅.rd = s.rd := by rw [rd₅, rd₄, rd₃, rd₂, e₁.rd]
  obtain wr₁₅ : s₅.wr = s.wr := by rw [wr₅, wr₄, wr₃, wr₂, e₁.wr]
  obtain esp₅ : s₅.gpr .esp = s.gpr .esp := by rw [g₁₅, e₁.reg .esp (by decide)]
  -- The saved registers, in the scratch buffer.
  obtain fB : Frame [⟨(arg s 2).setWidth 64, 16⟩] s.mem s₅.mem := by
    rw [m₅, m₄, m₃, m₂, e₁.mem, g₄, g₃, g₂, hB 0 (by decide), hB 4 (by decide), hB 8 (by decide),
      hB 12 (by decide)]
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide)
      (by decide))).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  obtain saved : ∀ r d, (r, d) ∈ [(Reg.ebx, 0), (.esi, 4), (.edi, 8), (.ebp, 12)] →
      s₅.mem.readW ((arg s 2).setWidth 64 + BitVec.ofNat 64 d) 32 = s.gpr r := by
    intro r d hrd'
    obtain g1 : ∀ q, q ≠ .eax → s₁.gpr q = s.gpr q := fun q hq => e₁.reg q (by simpa using hq)
    rw [m₅, m₄, m₃, m₂, e₁.mem, g₄, g₃, g₂, hB 0 (by decide), hB 4 (by decide), hB 8 (by decide),
      hB 12 (by decide)]
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hrd'
    obtain sep : ∀ a b, a + 4 ≤ b ∨ b + 4 ≤ a → b + 4 ≤ 16 → a + 4 ≤ 16 →
        Mem.Sep ((arg s 2).setWidth 64 + BitVec.ofNat 64 a) (32 / 8) ((arg s 2).setWidth 64 + BitVec.ofNat 64 b) (32 / 8) :=
      fun a b h hb ha => Offset.sep _ h (by omega_arith) (by omega_arith)
    rcases hrd' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [Mem.readW_writeW_sep (sep 0 12 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
        Mem.readW_writeW_sep (sep 0 8 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
        Mem.readW_writeW_sep (sep 0 4 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
        Mem.readW_writeW_self32, g1 _ (by decide)]
    · rw [Mem.readW_writeW_sep (sep 4 12 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
        Mem.readW_writeW_sep (sep 4 8 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
        Mem.readW_writeW_self32, g1 _ (by decide)]
    · rw [Mem.readW_writeW_sep (sep 8 12 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
        Mem.readW_writeW_self32, g1 _ (by decide)]
    · rw [Mem.readW_writeW_self32, g1 _ (by decide)]
  -- The pointers.
  obtain hargs₅ : ⟨argAddr s₅ 0, 12⟩ ∈ s₅.rd := by
    rw [rd₁₅]; simp only [argAddr, esp₅]; exact hargs
  obtain argE : ∀ i, i < 3 → arg s₅ i = arg s i := fun i hi =>
    arg_frame fB (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dAB) esp₅ (by omega_arith)
      (by omega_arith)
  obtain ⟨s₆, h₆, v₆, e₆⟩ := mov_run .esi _ _ s₅ (arg_src (i := 0) (by decide) hargs₅ (by rw [esp₅]; omega_arith))
  obtain hargs₆ : ⟨argAddr s₆ 0, 12⟩ ∈ s₆.rd := by
    rw [e₆.rd]; simp only [argAddr, e₆.reg .esp (by decide)]; exact hargs₅
  obtain ⟨s₇, h₇, v₇, e₇⟩ := mov_run .edi _ _ s₆ (arg_src (i := 1) (by decide) hargs₆
    (by rw [e₆.reg .esp (by decide), esp₅]; omega_arith))
  obtain a₆ : arg s₆ 1 = arg s 1 := by
    simp only [arg, argAddr, e₆.mem, e₆.reg .esp (by decide)]; exact argE 1 (by decide)
  obtain e₅₇ : Keep [.esi, .edi] s₅ s₇ := (e₆.weaken (by decide)).trans (e₇.weaken (by decide))
  obtain esi₇ : s₇.gpr .esi = arg s 0 := by rw [e₇.reg .esi (by decide), v₆, argE 0 (by decide)]
  obtain edi₇ : s₇.gpr .edi = arg s 1 := by rw [v₇, a₆]
  let z := Spec.Idea.scheduleAt s.mem ((arg s 0).setWidth 64)
  obtain hz : SchedOk z s₇ := by
    refine ⟨by rw [esi₇, e₅₇.rd, e₅₇.wr, rd₁₅, wr₁₅, hrd]; simp, by rw [esi₇]; exact fitS, ?_⟩
    rw [esi₇, e₅₇.mem]
    exact scheduleAt_congr (frame_bytes fB (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact dSB) (by decide))
  obtain ho : OutOk ((arg s 1).setWidth 64) s₇ :=
    ⟨by rw [e₅₇.wr, wr₁₅, hwr]; simp, by rw [edi₇], by rw [edi₇]; exact fitO⟩
  refine WP.seq (WP.of_runBlock ⟨s₇, ?_, ?_⟩)
  · exact run_append (a := [_] ++ _) (run_append h₁ (run_append h₂ (run_append h₃ (run_append h₄ h₅))))
      (run_append h₆ h₇)
  refine WP.seq (WP.mono (subkeys_ok z s₇ hz ho (by rw [esi₇]; exact dSO) 52 0 rfl s₇
    ⟨Keep.refl _ _, Frame.refl _ _, fun i hi => absurd hi (by omega_arith)⟩) fun t ht => ?_)
  -- The epilogue.
  obtain esp_t : t.gpr .esp = s.gpr .esp := by
    rw [ht.keep.reg .esp (by decide), e₅₇.reg .esp (by decide), esp₅]
  obtain ft : Frame [⟨(arg s 2).setWidth 64, 16⟩, ⟨(arg s 1).setWidth 64, 104⟩] s.mem t.mem :=
    (fB.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩).trans
      ((by rw [← e₅₇.mem]; exact ht.frame : Frame [⟨(arg s 1).setWidth 64, 2 * 52⟩] s₅.mem t.mem).sub
        fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩)
  obtain hargsT : ⟨argAddr t 0, 12⟩ ∈ t.rd := by
    rw [ht.keep.rd, e₅₇.rd, rd₁₅]; simp only [argAddr, esp_t]; exact hargs
  obtain ⟨u₁, k₁, w₁, f₁⟩ := mov_run .eax _ _ t (arg_src (i := 2) (by decide) hargsT (by rw [esp_t]; omega_arith))
  obtain eaxU : u₁.gpr .eax = arg s 2 := by
    rw [w₁]
    exact arg_frame ft (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dAB
      · exact dAO) esp_t (by omega_arith) (by omega_arith)
  obtain savedT : ∀ r d, (r, d) ∈ [(Reg.ebx, 0), (.esi, 4), (.edi, 8), (.ebp, 12)] →
      u₁.mem.readW ((arg s 2).setWidth 64 + BitVec.ofNat 64 d) 32 = s.gpr r := by
    intro r d hm
    obtain hd : d + 4 ≤ 16 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
      omega
    rw [f₁.mem, ← saved r d hm, ← e₅₇.mem]
    exact ht.frame.readW (Offset.contains_base _ hd (by omega_arith)) (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact dOB.symm) (by decide)
  obtain rdAny : ∀ u : State, u.gpr .eax = arg s 2 → u.mem = u₁.mem → u.rd = u₁.rd → u.wr = u₁.wr →
      ∀ r d, (r, d) ∈ [(Reg.ebx, 0), (.esi, 4), (.edi, 8), (.ebp, 12)] →
        readSrc u (.mem (at_ .eax d)) = some (s.gpr r) := fun u he hm hr hw r d hm' => by
    obtain hd : d + 4 ≤ 16 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm'
      omega
    rw [load_src, he, addr_eq (by omega_arith), hm, savedT r d hm']
    rw [he, addr_eq (by omega_arith), hr, hw, f₁.rd, f₁.wr, ht.keep.rd, ht.keep.wr, e₅₇.rd, e₅₇.wr, rd₁₅, wr₁₅, hwr]
    exact ⟨_, by simp, Offset.contains_base _ hd (by omega_arith)⟩
  obtain ⟨u₂, k₂, w₂, f₂⟩ := mov_run .ebx _ _ u₁ (rdAny u₁ eaxU rfl rfl rfl .ebx 0 (by simp))
  obtain ⟨u₃, k₃, w₃, f₃⟩ := mov_run .edi _ _ u₂ (rdAny u₂ (by rw [f₂.reg .eax (by decide), eaxU])
    f₂.mem f₂.rd f₂.wr .edi 8 (by simp))
  obtain e₁₃ : Keep [.ebx, .edi] u₁ u₃ := (f₂.weaken (by decide)).trans (f₃.weaken (by decide))
  obtain ⟨u₄, k₄, w₄, f₄⟩ := mov_run .ebp _ _ u₃ (rdAny u₃ (by rw [e₁₃.reg .eax (by decide), eaxU])
    e₁₃.mem e₁₃.rd e₁₃.wr .ebp 12 (by simp))
  obtain e₁₄ : Keep [.ebx, .edi, .ebp] u₁ u₄ := (e₁₃.weaken (by decide)).trans (f₄.weaken (by decide))
  obtain ⟨u₅, k₅, w₅, f₅⟩ := mov_run .esi _ _ u₄ (rdAny u₄ (by rw [e₁₄.reg .eax (by decide), eaxU])
    e₁₄.mem e₁₄.rd e₁₄.wr .esi 4 (by simp))
  obtain e₁₅ : Keep [.ebx, .edi, .ebp, .esi] u₁ u₅ := (e₁₄.weaken (by decide)).trans (f₅.weaken (by decide))
  obtain memU : u₅.mem = t.mem := by rw [e₁₅.mem, f₁.mem]
  refine WP.of_runBlock ⟨u₅, ?_, ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · exact run_append (a := [_]) k₁ (run_append (a := [_]) k₂ (run_append (a := [_]) k₃
      (run_append (a := [_]) k₄ k₅)))
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [f₅.reg .ebx (by decide), f₄.reg .ebx (by decide), f₃.reg .ebx (by decide), w₂]
    · exact w₅
    · rw [f₅.reg .edi (by decide), f₄.reg .edi (by decide), w₃]
    · rw [f₅.reg .ebp (by decide), w₄]
    · rw [e₁₅.reg .esp (by decide), f₁.reg .esp (by decide), esp_t]
  · rw [memU]
    exact ft.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dRB
      · exact dRO) (by decide)
  · show Spec.Idea.scheduleAt u₅.mem _ = _
    rw [memU]
    apply Vector.ext
    intro n hn
    rw [← getD_lt _ 0 hn, ← getD_lt _ 0 hn, scheduleAt_getD _ _ hn]
    exact ht.words n hn

end VG.Proof.Idea.X86

namespace VG.Proof.Idea.X86

open VG VG.X86 VG.Impl.Idea.X86

def invTaint : VG.X86.Taint.T := { regs := .ofList [.esp], flags := false, argLen := 16 }

theorem invTaint_wf {s : State} (h : invertContract.pre s) : VG.X86.Taint.Wf invTaint s := by
  obtain ⟨_, wr, _, _, _, ao, ab, ro, rb, _, _, _, spfit⟩ := h
  refine Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨spfit, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim⟩
  simp only [invTaint, wr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact Taint.frame_disjoint (n := 12) (by omega_arith) ro ao
  · exact Taint.frame_disjoint (n := 12) (by omega_arith) rb ab

theorem invTaint_agree {s₁ s₂ : State} (h₁ : invertContract.pre s₁) (h₂ : invertContract.pre s₂)
    (hp : invertContract.pub s₁ s₂) : VG.X86.Taint.Agree invTaint s₁ s₂ := by
  obtain ⟨sp, args⟩ := hp
  obtain fit : ∀ s, invertContract.pre s → (s.gpr .esp).toNat + 16 ≤ 2 ^ 32 := by
    intro s hs; exact hs.2.2.2.2.2.2.2.2.2.2.2.2
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h,
    invTaint_wf h₁, invTaint_wf h₂, VG.X86.Taint.slotsOk_empty,
    VG.X86.Taint.slotsAgree_empty, fun _ => sp, fun k h4 hk => ?_⟩
  · simp only [invTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r; exact sp
  · simp only [invTaint] at hk
    rw [show Taint.depth invTaint.stk = 0 from rfl, Nat.zero_add]
    rw [Taint.argByte_eq (fit _ h₁) h4 hk, Taint.argByte_eq (fit _ h₂) h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)),
      Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (args ((k - 4) / 4) (by omega_arith))

theorem invertKey_constantTime : ConstantTime isa invertContract.pre invertContract.pub invertKey :=
  VG.Taint.constantTime (A := taint) invTaint (fun _ _ h₁ h₂ hp => invTaint_agree h₁ h₂ hp)
    (by taint_decide)

/-- Memory holding the arguments `0x1000, 0x2000, 0x3000` at `0x4004`. -/
def invSatState : State where
  gpr r := if r = .esp then 0x4000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x4005 then 0x10 else if a = 0x4009 then 0x20 else if a = 0x400d then 0x30 else 0
  rd := [⟨0x1000, 104⟩, ⟨0x4004, 12⟩]
  wr := [⟨0x2000, 104⟩, ⟨0x3000, 16⟩]

theorem invertKey_verified : Verified target invertKey (Proof.Idea.invertKeyScratchContract32 abi 4) := by
  refine Verified.of_correct invert_wp invertKey_constantTime ?_
  sig_implies [Proof.Idea.invertKeyScratchContract32, Proof.Idea.invertKeyScratchSig32,
    Spec.Idea.invertKeyPost, abi, argSlots, argVal, argBytes, invertContract]
    [invSatState, arg, argAddr, Mem.readW, Mem.read] using invSatState

end VG.Proof.Idea.X86

end

end

/-!
# IDEA ECB on x86 (32-bit)

`ecb_wp`: with the scratch buffer as an argument (33 words, at `B`), the
code saves `ebx`, `esi`, `edi`, `ebp` in it (`savedSlot`), copies the
subkeys to it (`copy_run`), puts the data pointer and `n` in their slots,
transforms the blocks in a loop (`loop_ok`) whose invariant (`LoopInv`)
says how many remain, that the ones before are transformed and the ones
after not yet (each iteration is `cryptBlockWith_run`), and restores the
registers.
-/

@[expose] public section

namespace VG.Proof.Idea.X86

open VG VG.X86 VG.Impl.Idea.X86

/-! ## Copying the subkeys -/

/-- The bytes of two areas agree if their 32-bit words do. -/
theorem scheduleAt_of_words {m m' : Mem} {S B : Addr}
    (h : ∀ i < 26, m'.readW (B + BitVec.ofNat 64 (4 * i)) 32 = m.readW (S + BitVec.ofNat 64 (4 * i)) 32) :
    Spec.Idea.scheduleAt m' B = Spec.Idea.scheduleAt m S := by
  obtain hb : ∀ j < 104, m' (B + BitVec.ofNat 64 j) = m (S + BitVec.ofNat 64 j) := by
    intro j hj
    obtain e : ∀ p : Addr, p + BitVec.ofNat 64 j = p + BitVec.ofNat 64 (4 * (j / 4)) + BitVec.ofNat 64 (j % 4) :=
      fun p => by rw [Offset.add_ofNat_add_ofNat]; congr 2; omega_arith
    rw [e B, e S, Mem.readW_byte m' _ (Nat.mod_lt j (by decide)), Mem.readW_byte m _ (Nat.mod_lt j (by decide)),
      h _ (by omega_arith)]
  apply Vector.ext
  intro i hi
  simp only [Spec.Idea.scheduleAt, Vector.getElem_ofFn]
  rw [hb _ (by omega_arith), hb _ (by omega_arith)]

/-- After `k` words of the copy from `edx` to `esi`. -/
structure CopyInv (s₀ : State) (k : Nat) (t : State) : Prop where
  keep : Keep [.eax] { s₀ with mem := t.mem } t
  frame : Frame [⟨(s₀.gpr .esi).setWidth 64, 4 * k⟩] s₀.mem t.mem
  words : ∀ i < k, t.mem.readW ((s₀.gpr .esi).setWidth 64 + BitVec.ofNat 64 (4 * i)) 32 =
    s₀.mem.readW ((s₀.gpr .edx).setWidth 64 + BitVec.ofNat 64 (4 * i)) 32

/-- What the copy needs: the subkeys (104 bytes at `edx`) readable, the
copy (at `esi`, in a region of `n` bytes) writable, apart, neither wrapping
around. -/
structure CopyPre (n : Nat) (s : State) : Prop where
  src : ⟨(s.gpr .edx).setWidth 64, 104⟩ ∈ s.rd ++ s.wr
  dst : ⟨(s.gpr .esi).setWidth 64, n⟩ ∈ s.wr
  len : 104 ≤ n
  sep : Region.Disjoint ⟨(s.gpr .edx).setWidth 64, 104⟩ ⟨(s.gpr .esi).setWidth 64, n⟩
  fitS : (s.gpr .edx).toNat + 104 ≤ 2 ^ 32
  fitB : (s.gpr .esi).toNat + n ≤ 2 ^ 32

theorem copy_run {n : Nat} (s₀ : State) (hp : CopyPre n s₀) : ∀ k ≤ 26, ∃ t,
    runBlock isa ((List.range k).flatMap copyWord) s₀ = some t ∧ CopyInv s₀ k t
  | 0, _ => ⟨s₀, by simp [runBlock_nil], ⟨Keep.refl _ _, Frame.refl _ _, fun i hi => absurd hi (by omega_arith)⟩⟩
  | k + 1, hk => by
    obtain ⟨t, ht, hi⟩ := copy_run s₀ hp k (by omega_arith)
    have := hp.len; have := hp.fitS; have := hp.fitB
    obtain edx : t.gpr .edx = s₀.gpr .edx := hi.keep.reg .edx (by decide)
    obtain esi : t.gpr .esi = s₀.gpr .esi := hi.keep.reg .esi (by decide)
    obtain hsrc : InRegions (t.rd ++ t.wr) (addr (t.gpr .edx) (4 * k)) 4 := by
      rw [edx, hi.keep.rd, hi.keep.wr, addr_eq (by omega_arith)]
      exact ⟨_, hp.src, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    obtain ⟨t₁, h₁, v₁, e₁⟩ := mov_run .eax _ _ t (load_src hsrc)
    obtain hdst : InRegions t₁.wr (addr (t₁.gpr .esi) (4 * k)) 4 := by
      rw [e₁.reg .esi (by decide), esi, e₁.wr, hi.keep.wr, addr_eq (by omega_arith)]
      exact ⟨_, hp.dst, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    obtain ⟨t₂, h₂, m₂, g₂, rd₂, wr₂⟩ := store_run .esi .eax (4 * k) t₁ hdst
    obtain esi₁ : t₁.gpr .esi = s₀.gpr .esi := (e₁.reg .esi (by decide)).trans esi
    obtain aB : addr (s₀.gpr .esi) (4 * k) = (s₀.gpr .esi).setWidth 64 + BitVec.ofNat 64 (4 * k) :=
      addr_eq (by omega_arith)
    refine ⟨t₂, ?_, ⟨⟨fun r hr => ?_, rfl, ?_, ?_⟩, ?_, fun i hik => ?_⟩⟩
    · rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      exact run_append ht (run_append (a := [_]) h₁ h₂)
    · rw [g₂, e₁.reg r hr]; exact hi.keep.reg r hr
    · rw [rd₂, e₁.rd]; exact hi.keep.rd
    · rw [wr₂, e₁.wr]; exact hi.keep.wr
    · rw [m₂, e₁.mem, esi₁, aB]
      refine (hi.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).writeW
        (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
      simp only [List.mem_singleton] at hr; subst hr
      exact Region.sub_prefix (by omega_arith)
    · rw [m₂, e₁.mem, esi₁, aB]
      by_cases he : i = k
      · subst he
        rw [Mem.readW_writeW_self32, v₁, edx, addr_eq (by omega_arith)]
        refine hi.frame.readW (r := ⟨(s₀.gpr .edx).setWidth 64, 104⟩)
          (Offset.contains_base _ (d := 4 * i) (by omega_arith) (by omega_arith)) (fun r hr => ?_) (by decide)
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.sep.sub_right (Region.sub_prefix (by omega_arith))
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
        exact hi.words i (by omega_arith)

/-! ## The contract -/

/-- ECB on x86 with its scratch buffer (`4 * slots` bytes) as the fourth argument. -/
def ecbContract : Contract isa where
  pre s :=
    let sched : Region := ⟨(arg s 0).setWidth 64, 104⟩
    let data : Region := ⟨(arg s 1).setWidth 64, 8 * (arg s 2).toNat⟩
    let scratch : Region := ⟨(arg s 3).setWidth 64, 4 * slots⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [sched, args] ∧ s.wr = [data, scratch] ∧
    sched.Disjoint data ∧ sched.Disjoint scratch ∧ data.Disjoint scratch ∧
    args.Disjoint data ∧ args.Disjoint scratch ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
    (arg s 0).toNat + 104 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 8 * (arg s 2).toNat ≤ 2 ^ 32 ∧
    (arg s 3).toNat + 4 * slots ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32
  post s s' :=
    Spec.Idea.blocksAt s'.mem ((arg s 1).setWidth 64) (arg s 2).toNat =
      Spec.Idea.ecb (Spec.Idea.scheduleAt s.mem ((arg s 0).setWidth 64))
        (Spec.Idea.blocksAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 4, arg s₁ i = arg s₂ i

/-- `ecbContract.pre`, by name. -/
structure EPre (s : State) : Prop where
  rd : s.rd = [⟨(arg s 0).setWidth 64, 104⟩, ⟨argAddr s 0, 16⟩]
  wr : s.wr = [⟨(arg s 1).setWidth 64, 8 * (arg s 2).toNat⟩, ⟨(arg s 3).setWidth 64, 4 * slots⟩]
  dSD : Region.Disjoint ⟨(arg s 0).setWidth 64, 104⟩ ⟨(arg s 1).setWidth 64, 8 * (arg s 2).toNat⟩
  dSB : Region.Disjoint ⟨(arg s 0).setWidth 64, 104⟩ ⟨(arg s 3).setWidth 64, 4 * slots⟩
  dDB : Region.Disjoint ⟨(arg s 1).setWidth 64, 8 * (arg s 2).toNat⟩ ⟨(arg s 3).setWidth 64, 4 * slots⟩
  aD : Region.Disjoint ⟨argAddr s 0, 16⟩ ⟨(arg s 1).setWidth 64, 8 * (arg s 2).toNat⟩
  aB : Region.Disjoint ⟨argAddr s 0, 16⟩ ⟨(arg s 3).setWidth 64, 4 * slots⟩
  rD : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 1).setWidth 64, 8 * (arg s 2).toNat⟩
  rB : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 3).setWidth 64, 4 * slots⟩
  fS : (arg s 0).toNat + 104 ≤ 2 ^ 32
  fD : (arg s 1).toNat + 8 * (arg s 2).toNat ≤ 2 ^ 32
  fB : (arg s 3).toNat + 4 * slots ≤ 2 ^ 32
  fSp : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32

theorem EPre.of {s : State} (h : ecbContract.pre s) : EPre s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

/-- The callee-saved register saved at word `j` of `savedSlot`. -/
def sreg (j : Nat) : Reg := [Reg.ebx, .esi, .edi, .ebp].getD j .ebx

/-! ## The prologue -/

/-- What the prologue leaves (the scratch buffer at `B`). -/
structure PInv (s p : State) : Prop where
  esi : p.gpr .esi = arg s 3
  esp : p.gpr .esp = s.gpr .esp
  rd : p.rd = s.rd
  wr : p.wr = s.wr
  frame : Frame [⟨(arg s 3).setWidth 64, 4 * slots⟩] s.mem p.mem
  sched : Spec.Idea.scheduleAt p.mem ((arg s 3).setWidth 64) =
    Spec.Idea.scheduleAt s.mem ((arg s 0).setWidth 64)
  data : p.mem.readW ((arg s 3).setWidth 64 + BitVec.ofNat 64 dataSlot) 32 = arg s 1
  left : p.mem.readW ((arg s 3).setWidth 64 + BitVec.ofNat 64 leftSlot) 32 = arg s 2
  saved : ∀ j < 4, p.mem.readW ((arg s 3).setWidth 64 + BitVec.ofNat 64 (savedSlot + 4 * j)) 32 = s.gpr (sreg j)
  zf : p.zf = some (arg s 2 - 0 == 0)

theorem cmp0_run (r : Reg) (s : State) :
    ∃ s', runBlock isa [.alu .cmp r (.imm 0)] s = some s' ∧ s'.zf = some (s.gpr r - 0 == 0) ∧
      Keep [] s s' := by
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, execAlu, readSrc, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  exact ⟨rfl, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩

/-- A word of the scratch buffer, after writes to other words. -/
theorem scr_sep {m : Mem} {B : Addr} {a d : Nat} {v : BitVec 32} (h : a + 4 ≤ d ∨ d + 4 ≤ a)
    (ha : a + 4 ≤ 4 * slots) (hd : d + 4 ≤ 4 * slots) :
    (m.writeW (B + BitVec.ofNat 64 d) v).readW (B + BitVec.ofNat 64 a) 32 = m.readW (B + BitVec.ofNat 64 a) 32 :=
  Mem.readW_writeW_sep (Offset.sep _ h (by simp only [slots] at ha; omega_arith)
    (by simp only [slots] at hd; omega_arith)) (by decide)

theorem prologue_run (s : State) (hp : EPre s) : ∃ p, runBlock isa prologue s = some p ∧ PInv s p := by
  obtain fB := hp.fB; have fSp := hp.fSp
  simp only [slots] at fB
  obtain hargs : ⟨argAddr s 0, 16⟩ ∈ s.rd := by rw [hp.rd]; simp
  let B : Addr := (arg s 3).setWidth 64
  obtain hBin : ∀ t : State, t.wr = s.wr → ∀ d, d + 4 ≤ 4 * slots → InRegions t.wr (B + BitVec.ofNat 64 d) 4 :=
    fun t ht d hd => by
      rw [ht, hp.wr]
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Offset.contains_base _ hd
        (by simp only [slots] at hd; omega_arith)⟩
  obtain hBa : ∀ x : BitVec 32, x = arg s 3 → ∀ d, d + 4 ≤ 4 * slots → addr x d = B + BitVec.ofNat 64 d :=
    fun x hx d hd => by rw [hx, addr_eq (by simp only [slots] at hd; omega_arith)]
  -- Saving the registers.
  obtain ⟨s₁, h₁, v₁, e₁⟩ := mov_run .eax _ _ s (arg_src (i := 3) (by decide) hargs (by omega_arith))
  obtain ⟨s₂, h₂, m₂, g₂, rd₂, wr₂⟩ := store_run .eax .ebx (savedSlot + 0) s₁
    (by rw [hBa _ v₁ _ (by decide)]; exact hBin _ e₁.wr _ (by decide))
  obtain ⟨s₃, h₃, m₃, g₃, rd₃, wr₃⟩ := store_run .eax .esi (savedSlot + 4) s₂
    (by rw [g₂, hBa _ v₁ _ (by decide)]; exact hBin _ (by rw [wr₂, e₁.wr]) _ (by decide))
  obtain ⟨s₄, h₄, m₄, g₄, rd₄, wr₄⟩ := store_run .eax .edi (savedSlot + 8) s₃
    (by rw [g₃, g₂, hBa _ v₁ _ (by decide)]; exact hBin _ (by rw [wr₃, wr₂, e₁.wr]) _ (by decide))
  obtain ⟨s₅, h₅, m₅, g₅, rd₅, wr₅⟩ := store_run .eax .ebp (savedSlot + 12) s₄
    (by rw [g₄, g₃, g₂, hBa _ v₁ _ (by decide)]; exact hBin _ (by rw [wr₄, wr₃, wr₂, e₁.wr]) _ (by decide))
  obtain g₁₅ : s₅.gpr = s₁.gpr := by rw [g₅, g₄, g₃, g₂]
  obtain g1 : ∀ q, q ≠ .eax → s₁.gpr q = s.gpr q := fun q hq => e₁.reg q (by simpa using hq)
  obtain m₁₅ : s₅.mem = (((s.mem.writeW (B + BitVec.ofNat 64 (savedSlot + 0)) (s.gpr .ebx)).writeW
      (B + BitVec.ofNat 64 (savedSlot + 4)) (s.gpr .esi)).writeW (B + BitVec.ofNat 64 (savedSlot + 8))
      (s.gpr .edi)).writeW (B + BitVec.ofNat 64 (savedSlot + 12)) (s.gpr .ebp) := by
    rw [m₅, m₄, m₃, m₂, e₁.mem, g₄, g₃, g₂, hBa _ v₁ _ (by decide), hBa _ v₁ _ (by decide),
      hBa _ v₁ _ (by decide), hBa _ v₁ _ (by decide), g1 _ (by decide), g1 _ (by decide), g1 _ (by decide),
      g1 _ (by decide)]
  obtain f₅ : Frame [⟨B, 4 * slots⟩] s.mem s₅.mem := by
    rw [m₁₅]
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide)
      (by decide))).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  obtain saved₅ : ∀ j < 4, s₅.mem.readW (B + BitVec.ofNat 64 (savedSlot + 4 * j)) 32 = s.gpr (sreg j) := by
    intro j hj
    rw [m₁₅]
    obtain rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega_arith
    · rw [scr_sep (by simp only [savedSlot]; omega_arith) (by decide) (by decide),
        scr_sep (by simp only [savedSlot]; omega_arith) (by decide) (by decide),
        scr_sep (by simp only [savedSlot]; omega_arith) (by decide) (by decide), Mem.readW_writeW_self32]; rfl
    · rw [scr_sep (by simp only [savedSlot]; omega_arith) (by decide) (by decide),
        scr_sep (by simp only [savedSlot]; omega_arith) (by decide) (by decide), Mem.readW_writeW_self32]; rfl
    · rw [scr_sep (by simp only [savedSlot]; omega_arith) (by decide) (by decide), Mem.readW_writeW_self32]; rfl
    · rw [Mem.readW_writeW_self32]; rfl
  obtain esp₅ : s₅.gpr .esp = s.gpr .esp := by rw [g₁₅, g1 _ (by decide)]
  obtain rd₁₅ : s₅.rd = s.rd := by rw [rd₅, rd₄, rd₃, rd₂, e₁.rd]
  obtain wr₁₅ : s₅.wr = s.wr := by rw [wr₅, wr₄, wr₃, wr₂, e₁.wr]
  obtain argE : ∀ (t : State) (rs : List Region), Frame rs s.mem t.mem →
      (∀ r ∈ rs, Region.Disjoint ⟨argAddr s 0, 16⟩ r) → t.gpr .esp = s.gpr .esp → ∀ i, i < 4 →
      arg t i = arg s i := fun t rs hf hd he i hi => arg_frame hf hd he (by omega_arith) (by omega_arith)
  obtain dAB : ∀ r ∈ [(⟨B, 4 * slots⟩ : Region)], Region.Disjoint ⟨argAddr s 0, 16⟩ r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.aB
  obtain hargsT : ∀ t : State, t.rd = s.rd → t.gpr .esp = s.gpr .esp → ⟨argAddr t 0, 16⟩ ∈ t.rd :=
    fun t hr he => by rw [hr]; simp only [argAddr, he]; exact hargs
  -- The subkeys.
  obtain ⟨s₆, h₆, v₆, e₆⟩ := mov_run .esi (.reg .eax) _ s₅ rfl
  obtain ⟨s₇, h₇, v₇, e₇⟩ := mov_run .edx _ _ s₆ (arg_src (i := 0) (by decide)
    (hargsT s₆ (by rw [e₆.rd, rd₁₅]) (by rw [e₆.reg .esp (by decide), esp₅])) (by rw [e₆.reg .esp (by decide), esp₅]; omega_arith))
  obtain mem₇ : s₇.mem = s₅.mem := by rw [e₇.mem, e₆.mem]
  obtain esi₇ : s₇.gpr .esi = arg s 3 := by rw [e₇.reg .esi (by decide), v₆, g₁₅, v₁]
  obtain edx₇ : s₇.gpr .edx = arg s 0 := by
    rw [v₇, show arg s₆ 0 = arg s₅ 0 by simp only [arg, argAddr, e₆.mem, e₆.reg .esp (by decide)]]
    exact argE s₅ _ f₅ dAB esp₅ 0 (by decide)
  obtain esp₇ : s₇.gpr .esp = s.gpr .esp := by rw [e₇.reg .esp (by decide), e₆.reg .esp (by decide), esp₅]
  obtain rd₇ : s₇.rd = s.rd := by rw [e₇.rd, e₆.rd, rd₁₅]
  obtain wr₇ : s₇.wr = s.wr := by rw [e₇.wr, e₆.wr, wr₁₅]
  obtain cp : CopyPre (4 * slots) s₇ := by
    refine ⟨by rw [edx₇, rd₇, hp.rd]; simp, by rw [esi₇, wr₇, hp.wr]; simp, by decide,
      by rw [edx₇, esi₇]; exact hp.dSB, by rw [edx₇]; exact hp.fS, by rw [esi₇]; simp only [slots]; omega_arith⟩
  obtain ⟨s₈, h₈, ci⟩ := copy_run s₇ cp 26 (by decide)
  obtain esp₈ : s₈.gpr .esp = s.gpr .esp := (ci.keep.reg .esp (by decide)).trans esp₇
  obtain esi₈ : s₈.gpr .esi = arg s 3 := (ci.keep.reg .esi (by decide)).trans esi₇
  obtain rd₈ : s₈.rd = s.rd := ci.keep.rd.trans rd₇
  obtain wr₈ : s₈.wr = s.wr := ci.keep.wr.trans wr₇
  obtain f₈ : Frame [⟨B, 4 * slots⟩] s.mem s₈.mem := by
    refine f₅.trans ?_
    rw [← mem₇]
    refine ci.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
    simp only [List.mem_singleton] at hr; subst hr
    rw [esi₇]; exact Region.sub_prefix (by decide)
  -- The slots.
  obtain ⟨s₉, h₉, v₉, e₉⟩ := mov_run .eax _ _ s₈ (arg_src (i := 1) (by decide) (hargsT s₈ rd₈ esp₈)
    (by rw [esp₈]; omega_arith))
  obtain ⟨s₁₀, h₁₀, m₁₀, g₁₀, rd₁₀, wr₁₀⟩ := store_run .esi .eax dataSlot s₉
    (by rw [e₉.reg .esi (by decide), hBa _ esi₈ _ (by decide)]; exact hBin _ (by rw [e₉.wr, wr₈]) _ (by decide))
  obtain esp₁₀ : s₁₀.gpr .esp = s.gpr .esp := by rw [g₁₀, e₉.reg .esp (by decide), esp₈]
  obtain ⟨s₁₁, h₁₁, v₁₁, e₁₁⟩ := mov_run .eax _ _ s₁₀ (arg_src (i := 2) (by decide)
    (hargsT s₁₀ (by rw [rd₁₀, e₉.rd, rd₈]) esp₁₀) (by rw [esp₁₀]; omega_arith))
  obtain ⟨s₁₂, h₁₂, m₁₂, g₁₂, rd₁₂, wr₁₂⟩ := store_run .esi .eax leftSlot s₁₁
    (by rw [e₁₁.reg .esi (by decide), g₁₀, e₉.reg .esi (by decide), hBa _ esi₈ _ (by decide)]
        exact hBin _ (by rw [e₁₁.wr, wr₁₀, e₉.wr, wr₈]) _ (by decide))
  obtain ⟨s₁₃, h₁₃, z₁₃, e₁₃⟩ := cmp0_run .eax s₁₂
  obtain a1 : s₉.gpr .eax = arg s 1 := by
    rw [v₉]; exact argE s₈ _ f₈ dAB esp₈ 1 (by decide)
  obtain mem₁₀ : s₁₀.mem = s₈.mem.writeW (B + BitVec.ofNat 64 dataSlot) (arg s 1) := by
    rw [m₁₀, e₉.mem, e₉.reg .esi (by decide), esi₈, a1, hBa _ rfl _ (by decide)]
  obtain f₁₀ : Frame [⟨B, 4 * slots⟩] s.mem s₁₀.mem := by
    rw [mem₁₀]; exact f₈.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  obtain a2 : s₁₁.gpr .eax = arg s 2 := by
    rw [v₁₁]; exact argE s₁₀ _ f₁₀ dAB esp₁₀ 2 (by decide)
  obtain mem₁₂ : s₁₂.mem = s₁₀.mem.writeW (B + BitVec.ofNat 64 leftSlot) (arg s 2) := by
    rw [m₁₂, e₁₁.mem, e₁₁.reg .esi (by decide), g₁₀, e₉.reg .esi (by decide), esi₈, a2,
      hBa _ rfl _ (by decide)]
  refine ⟨s₁₃, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · unfold prologue
    exact run_append (run_append (run_append (run_append h₁ (run_append (a := [_]) h₂ (run_append (a := [_]) h₃
      (run_append (a := [_]) h₄ h₅)))) (run_append (a := [_]) h₆ h₇)) h₈)
      (run_append (a := [_]) h₉ (run_append (a := [_]) h₁₀ (run_append (a := [_]) h₁₁
        (run_append (a := [_]) h₁₂ h₁₃))))
  · rw [e₁₃.reg .esi (by decide), g₁₂, e₁₁.reg .esi (by decide), g₁₀, e₉.reg .esi (by decide), esi₈]
  · rw [e₁₃.reg .esp (by decide), g₁₂, e₁₁.reg .esp (by decide), esp₁₀]
  · rw [e₁₃.rd, rd₁₂, e₁₁.rd, rd₁₀, e₉.rd, rd₈]
  · rw [e₁₃.wr, wr₁₂, e₁₁.wr, wr₁₀, e₉.wr, wr₈]
  · rw [e₁₃.mem, mem₁₂]; exact f₁₀.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  · rw [e₁₃.mem, mem₁₂, mem₁₀]
    refine scheduleAt_of_words fun i hi => ?_
    rw [scr_sep (by simp only [leftSlot]; omega_arith) (by simp only [slots]; omega_arith) (by decide),
      scr_sep (by simp only [dataSlot]; omega_arith) (by simp only [slots]; omega_arith) (by decide)]
    obtain w := ci.words i hi
    rw [esi₇, edx₇, mem₇] at w
    rw [w]
    refine f₅.readW (r := ⟨(arg s 0).setWidth 64, 104⟩) (Offset.contains_base _ (d := 4 * i) (by omega_arith)
      (by omega_arith)) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.dSB
  · rw [e₁₃.mem, mem₁₂, scr_sep (by simp only [leftSlot, dataSlot]; omega_arith) (by decide) (by decide), mem₁₀,
      Mem.readW_writeW_self32]
  · rw [e₁₃.mem, mem₁₂, Mem.readW_writeW_self32]
  · intro j hj
    rw [e₁₃.mem, mem₁₂, scr_sep (by simp only [leftSlot, savedSlot]; omega_arith)
      (by simp only [slots, savedSlot]; omega_arith) (by decide), mem₁₀,
      scr_sep (by simp only [dataSlot, savedSlot]; omega_arith) (by simp only [slots, savedSlot]; omega_arith) (by decide)]
    rw [← saved₅ j hj, ← mem₇]
    refine ci.frame.readW (r := ⟨B + BitVec.ofNat 64 (savedSlot + 4 * j), 4⟩) (Region.contains_self _ _)
      (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    rw [esi₇]
    exact Offset.disjoint_base _ (by simp only [savedSlot]; omega_arith) (by simp only [savedSlot]; omega_arith)
  · rw [z₁₃, g₁₂, a2]

/-! ## The loop -/

theorem store_zf (b r : Reg) (d : Nat) (s s' : State) (h : runBlock isa [.store (at_ b d) r] s = some s') :
    s'.zf = s.zf := by
  simp only [runBlock_cons, isa, exec, State.store32] at h
  split at h
  · rw [runStep_some, runBlock_nil, Option.some.injEq] at h; subst h; rfl
  · cases h

/-- The facts about the state `o` before the loop that the loop relies on. -/
structure LCtx (z : Spec.Idea.Schedule) (P₀ : BitVec 32) (n : Nat) (o : State) : Prop where
  key : KeyOk z o
  data : ⟨P₀.setWidth 64, 8 * n⟩ ∈ o.wr
  sep : Region.Disjoint ⟨P₀.setWidth 64, 8 * n⟩ ⟨(o.gpr .esi).setWidth 64, 4 * slots⟩
  fit : P₀.toNat + 8 * n ≤ 2 ^ 32

/-- The slots that the loop writes: `t₀`'s, the data pointer's and the count's. -/
abbrev slotsR (o : State) : Region := ⟨(o.gpr .esi).setWidth 64 + BitVec.ofNat 64 t0Slot, 12⟩

/-- `r` blocks remain, from block `n - r` on: the ones before are transformed. -/
structure LoopInv (z : Spec.Idea.Schedule) (P₀ : BitVec 32) (n : Nat) (m₀ : Mem) (o : State) (r : Nat)
    (t : State) : Prop where
  pos : 1 ≤ r
  le : r ≤ n
  esi : t.gpr .esi = o.gpr .esi
  esp : t.gpr .esp = o.gpr .esp
  rd : t.rd = o.rd
  wr : t.wr = o.wr
  frame : Frame [⟨P₀.setWidth 64, 8 * n⟩, slotsR o] o.mem t.mem
  data : t.mem.readW ((o.gpr .esi).setWidth 64 + BitVec.ofNat 64 dataSlot) 32 = P₀ + BitVec.ofNat 32 (8 * (n - r))
  left : t.mem.readW ((o.gpr .esi).setWidth 64 + BitVec.ofNat 64 leftSlot) 32 = BitVec.ofNat 32 r
  done : ∀ j < n - r, Spec.Idea.blockAt t.mem (P₀.setWidth 64 + BitVec.ofNat 64 (8 * j)) =
    Spec.Idea.cryptBlock z (Spec.Idea.blockAt m₀ (P₀.setWidth 64 + BitVec.ofNat 64 (8 * j)))
  todo : ∀ j, n - r ≤ j → j < n → Spec.Idea.blockAt t.mem (P₀.setWidth 64 + BitVec.ofNat 64 (8 * j)) =
    Spec.Idea.blockAt m₀ (P₀.setWidth 64 + BitVec.ofNat 64 (8 * j))

/-- After the loop (or none): every block transformed. -/
structure LoopPost (z : Spec.Idea.Schedule) (P₀ : BitVec 32) (n : Nat) (m₀ : Mem) (o : State)
    (t : State) : Prop where
  esi : t.gpr .esi = o.gpr .esi
  esp : t.gpr .esp = o.gpr .esp
  rd : t.rd = o.rd
  wr : t.wr = o.wr
  frame : Frame [⟨P₀.setWidth 64, 8 * n⟩, slotsR o] o.mem t.mem
  done : ∀ j < n, Spec.Idea.blockAt t.mem (P₀.setWidth 64 + BitVec.ofNat 64 (8 * j)) =
    Spec.Idea.cryptBlock z (Spec.Idea.blockAt m₀ (P₀.setWidth 64 + BitVec.ofNat 64 (8 * j)))

theorem step_ok {z : Spec.Idea.Schedule} {P₀ : BitVec 32} {n : Nat} {m₀ : Mem} {o : State}
    (hc : LCtx z P₀ n o) (r : Nat) (t : State) (hi : LoopInv z P₀ n m₀ o r t) :
    WP isa (.block ecbBody) t
      (fun t' => (isa.eval .ne t' = some false ∧ LoopPost z P₀ n m₀ o t') ∨
        (isa.eval .ne t' = some true ∧ ∃ r' < r, LoopInv z P₀ n m₀ o r' t')) := by
  have hfB := hc.key.fit
  simp only [slots] at hfB
  have hfD := hc.fit
  obtain hj : n - r < n := by have := hi.pos; have := hi.le; omega_arith
  obtain hb64 : 8 * n ≤ 2 ^ 64 := by omega_arith
  let Bs : Addr := (o.gpr .esi).setWidth 64
  let A : Addr := P₀.setWidth 64
  obtain hBs : ∀ d, d + 4 ≤ 4 * slots → addr (t.gpr .esi) d = Bs + BitVec.ofNat 64 d := fun d hd => by
    rw [hi.esi, addr_eq (by simp only [slots] at hd; omega_arith)]
  -- The subkeys and the slots, outside what the loop writes.
  obtain dS : ∀ q ∈ [(⟨A, 8 * n⟩ : Region), slotsR o], Region.Disjoint ⟨Bs, 104⟩ q := fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact (hc.sep.symm).sub_left (Region.sub_prefix (by decide))
    · exact Offset.base_disjoint _ (by decide) (by simp only [t0Slot]; omega_arith)
  obtain hk : KeyOk z t := by
    refine ⟨by rw [hi.esi, hi.wr]; exact hc.key.wr, by rw [hi.esi]; exact hc.key.fit, ?_⟩
    rw [hi.esi, ← hc.key.sched]
    exact scheduleAt_congr (frame_bytes hi.frame dS (by decide))
  -- The block.
  obtain hP : (P₀ + BitVec.ofNat 32 (8 * (n - r))).setWidth 64 = A + BitVec.ofNat 64 (8 * (n - r)) := by
    rw [← addr_eq (by omega_arith)]; rfl
  obtain hPfit : (P₀ + BitVec.ofNat 32 (8 * (n - r))).toNat + 8 ≤ 2 ^ 32 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * (n - r)) (by omega_arith),
      Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith
  obtain hin : ∀ i, i + 4 ≤ 8 → InRegions t.wr (A + BitVec.ofNat 64 (8 * (n - r)) + BitVec.ofNat 64 i) 4 :=
    fun i hi' => ⟨_, by rw [hi.wr]; exact hc.data, block_contains hj hi' (by decide) hb64⟩
  obtain hat : BlockAt z (P₀ + BitVec.ofNat 32 (8 * (n - r))) (A + BitVec.ofNat 64 (8 * (n - r))) t := by
    refine ⟨hk, ?_, hP, hPfit, ?_, ?_⟩
    · rw [hBs _ (by decide)]; exact hi.data
    · have := hin 0 (by decide); rw [BitVec.add_zero] at this
      obtain ⟨R, hR, hc'⟩ := this; exact ⟨R, List.mem_append_right _ hR, hc'⟩
    · obtain ⟨R, hR, hc'⟩ := hin 4 (by decide); exact ⟨R, List.mem_append_right _ hR, hc'⟩
  obtain hw0 : InRegions t.wr (A + BitVec.ofNat 64 (8 * (n - r))) 4 := by
    have := hin 0 (by decide); rwa [BitVec.add_zero] at this
  obtain hpre : ∀ u : State, u.gpr .esi = t.gpr .esi → u.rd = t.rd → u.wr = t.wr →
      Frame [⟨addr (t.gpr .esi) t0Slot, 4⟩] t.mem u.mem →
      ∃ u', runBlock isa [.mov .edx (.mem (at_ .esi leftSlot))] u = some u' ∧ Keep [.edx] u u' ∧
        u'.gpr .edx = BitVec.ofNat 32 r := fun u he hr hw hf => by
    obtain hku : KeyOk z u := ⟨by rw [he, hw]; exact hk.wr, by rw [he]; exact hk.fit, by
      rw [he, ← hk.sched]
      refine scheduleAt_congr (frame_bytes hf (fun q hq => ?_) (by decide))
      simp only [List.mem_singleton] at hq; subst hq
      rw [hBs _ (by decide), hi.esi]
      exact Offset.base_disjoint _ (by decide) (by simp only [t0Slot]; omega_arith)⟩
    obtain ⟨u', h', v', e'⟩ := mov_run .edx _ _ u (slot_src hku (d := leftSlot) (by decide))
    refine ⟨u', h', e', ?_⟩
    rw [v', he, hBs _ (by decide), ← hi.left]
    refine hf.readW (r := ⟨Bs + BitVec.ofNat 64 leftSlot, 4⟩) (Region.contains_self _ _) (fun q hq => ?_)
      (by decide)
    simp only [List.mem_singleton] at hq; subst hq
    rw [hBs _ (by decide)]
    exact Offset.disjoint _ (by simp only [leftSlot, t0Slot]; omega_arith) (by simp only [leftSlot]; omega_arith)
      (by simp only [t0Slot]; omega_arith)
  obtain ⟨t₁, h₁, b₁, f₁, eax₁, esi₁, esp₁, rd₁, wr₁, edx₁⟩ :=
    cryptBlockWith_run z _ (fun v => v = BitVec.ofNat 32 r) t hat hw0 (hin 4 (by decide)) hpre
  -- The next block's address and the count, to their slots.
  obtain hk₁ : KeyOk z t₁ := ⟨by rw [esi₁, wr₁]; exact hk.wr, by rw [esi₁]; exact hk.fit, by
    rw [esi₁, ← hk.sched]
    refine scheduleAt_congr (frame_bytes f₁ (fun q hq => ?_) (by decide))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · rw [hi.esi]; exact (hc.sep.symm).sub_left (Region.sub_prefix (by decide)) |>.sub_right
        (Offset.sub_base _ (by omega_arith))
    · rw [hBs _ (by decide), hi.esi]
      exact Offset.base_disjoint _ (by decide) (by simp only [t0Slot]; omega_arith)⟩
  obtain ⟨t₂, h₂, v₂, e₂⟩ := alu_run .add (by simp) .eax (.imm 8) 8 t₁ rfl
  obtain ⟨t₃, h₃, m₃, g₃, rd₃, wr₃⟩ := store_run .esi .eax dataSlot t₂
    (by rw [e₂.reg .esi (by decide), e₂.wr]; exact hk₁.slot (by decide))
  obtain ⟨t₄, h₄, v₄, z₄, e₄⟩ := sub1_run .edx t₃
  obtain ⟨t₅, h₅, m₅, g₅, rd₅, wr₅⟩ := store_run .esi .edx leftSlot t₄
    (by rw [e₄.reg .esi (by decide), g₃, e₂.reg .esi (by decide), e₄.wr, wr₃, e₂.wr]; exact hk₁.slot (by decide))
  obtain zf₅ : t₅.zf = some (BitVec.ofNat 32 r - 1 == 0) := by
    rw [store_zf _ _ _ _ _ h₅, z₄, g₃, e₂.reg .edx (by decide), edx₁]
  refine WP.of_runBlock ⟨t₅, ?_, ?_⟩
  · exact run_append h₁ (run_append (a := [_]) h₂ (run_append (a := [_]) h₃ (run_append (a := [_]) h₄ h₅)))
  obtain esi₅ : t₅.gpr .esi = o.gpr .esi := by
    rw [g₅, e₄.reg .esi (by decide), g₃, e₂.reg .esi (by decide), esi₁, hi.esi]
  obtain esp₅ : t₅.gpr .esp = o.gpr .esp := by
    rw [g₅, e₄.reg .esp (by decide), g₃, e₂.reg .esp (by decide), esp₁, hi.esp]
  obtain rd₅ : t₅.rd = o.rd := by rw [rd₅, e₄.rd, rd₃, e₂.rd, rd₁, hi.rd]
  obtain wr₅ : t₅.wr = o.wr := by rw [wr₅, e₄.wr, wr₃, e₂.wr, wr₁, hi.wr]
  obtain esiB : ∀ d, d + 4 ≤ 4 * slots → addr (t₄.gpr .esi) d = Bs + BitVec.ofNat 64 d := fun d hd => by
    rw [e₄.reg .esi (by decide), g₃, e₂.reg .esi (by decide), esi₁]; exact hBs d hd
  obtain mem₅ : t₅.mem = (t₁.mem.writeW (Bs + BitVec.ofNat 64 dataSlot)
      (P₀ + BitVec.ofNat 32 (8 * (n - r)) + 8)).writeW (Bs + BitVec.ofNat 64 leftSlot)
      (BitVec.ofNat 32 r - 1) := by
    rw [m₅, e₄.mem, m₃, e₂.mem, v₄, g₃, e₂.reg .edx (by decide), edx₁, esiB _ (by decide)]
    rw [show addr (t₂.gpr .esi) dataSlot = addr (t₄.gpr .esi) dataSlot by
      rw [e₄.reg .esi (by decide), g₃], esiB _ (by decide), v₂, eax₁]
    rfl
  obtain sl : ∀ d, t0Slot ≤ d → d + 4 ≤ t0Slot + 12 → (slotsR o).Contains (Bs + BitVec.ofNat 64 d) 4 :=
    fun d h₁ h₂ => Offset.contains _ h₁ h₂ (by simp only [t0Slot]; omega_arith)
  obtain dataSep : ∀ d, t0Slot ≤ d → d + 4 ≤ t0Slot + 12 → ∀ j < n,
      Region.Disjoint ⟨A + BitVec.ofNat 64 (8 * j), 8⟩ ⟨Bs + BitVec.ofNat 64 d, 4⟩ := fun d h₁ h₂ j hj =>
    (hc.sep.sub_left (Offset.sub_base _ (by omega_arith))).sub_right
      (Offset.sub_base _ (by simp only [t0Slot, slots] at *; omega_arith))
  obtain F₅ : Frame [⟨A + BitVec.ofNat 64 (8 * (n - r)), 8⟩, slotsR o] t.mem t₅.mem := by
    rw [mem₅]
    refine ((f₁.sub fun q hq => ?_).writeW (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _
      (sl _ (by decide) (by decide))).writeW
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (sl _ (by decide) (by decide))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · refine ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩
      rw [hBs _ (by decide)]
      exact Offset.sub _ (Nat.le_refl _) (by decide)
  obtain frame₅ : Frame [⟨A, 8 * n⟩, slotsR o] o.mem t₅.mem :=
    hi.frame.trans (F₅.sub fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact ⟨_, List.mem_cons_self, Offset.sub_base _ (by omega_arith)⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩)
  have other (j : Nat) (hjn : j < n) (hne : j ≠ n - r) :
      Spec.Idea.blockAt t₅.mem (A + BitVec.ofNat 64 (8 * j)) =
        Spec.Idea.blockAt t.mem (A + BitVec.ofNat 64 (8 * j)) := by
    refine blockAt_congr (frame_bytes F₅ (fun q hq => ?_) (by decide))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact blocks_disjoint hj hjn (Ne.symm hne) hb64
    · exact (hc.sep.sub_left (r₁' := ⟨A + BitVec.ofNat 64 (8 * j), 8⟩) (Offset.sub_base _ (by omega_arith))).sub_right
        (r₂' := slotsR o) (Offset.sub_base _ (by decide))
  obtain done₅ : ∀ j < n - (r - 1), Spec.Idea.blockAt t₅.mem (A + BitVec.ofNat 64 (8 * j)) =
      Spec.Idea.cryptBlock z (Spec.Idea.blockAt m₀ (A + BitVec.ofNat 64 (8 * j))) := by
    intro j hjr
    by_cases he : j = n - r
    · subst he
      obtain hb₅ : Spec.Idea.blockAt t₅.mem (A + BitVec.ofNat 64 (8 * (n - r))) =
          Spec.Idea.blockAt t₁.mem (A + BitVec.ofNat 64 (8 * (n - r))) := by
        obtain F : Frame [slotsR o] t₁.mem t₅.mem := by
          rw [mem₅]
          exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (sl _ (by decide) (by decide))).writeW
            (List.mem_singleton_self _) _ (sl _ (by decide) (by decide))
        refine blockAt_congr (frame_bytes F (fun q hq => ?_) (by decide))
        simp only [List.mem_singleton] at hq; subst hq
        exact (hc.sep.sub_left (r₁' := ⟨A + BitVec.ofNat 64 (8 * (n - r)), 8⟩)
          (Offset.sub_base _ (by omega_arith))).sub_right (r₂' := slotsR o) (Offset.sub_base _ (by decide))
      rw [hb₅, b₁, hi.todo _ (Nat.le_refl _) hj]
    · rw [other j (by omega_arith) he]
      exact hi.done j (by have := hi.pos; omega_arith)
  obtain hn32 : n < 2 ^ 32 := by omega_arith
  obtain hev : isa.eval .ne t₅ = some (decide (r - 1 ≠ 0)) := by
    show t₅.zf.map (!·) = _
    rw [zf₅, Option.map_some]
    congr 1
    have := hi.le; have := hi.pos
    by_cases h0 : r - 1 = 0
    · rw [show r = 1 by omega_arith]; rfl
    · have hne : BitVec.ofNat 32 r - 1 ≠ 0 := fun h => h0 (by
        have := congrArg BitVec.toNat h
        rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := r) (by omega_arith)] at this
        simp only [show (1 : BitVec 32).toNat = 1 from rfl, show (0 : BitVec 32).toNat = 0 from rfl] at this
        omega_arith)
      rw [show (BitVec.ofNat 32 r - 1 == 0) = false from by simpa using hne]
      simp [h0]
  obtain data₅ : t₅.mem.readW (Bs + BitVec.ofNat 64 dataSlot) 32 = P₀ + BitVec.ofNat 32 (8 * (n - (r - 1))) := by
    rw [mem₅, scr_sep (by simp only [dataSlot, leftSlot]; omega_arith) (by decide) (by decide), Mem.readW_writeW_self32]
    have := hi.pos; have := hi.le
    rw [show 8 * (n - (r - 1)) = 8 * (n - r) + 8 by omega_arith, BitVec.ofNat_add, BitVec.add_assoc]
    rfl
  obtain left₅ : t₅.mem.readW (Bs + BitVec.ofNat 64 leftSlot) 32 = BitVec.ofNat 32 (r - 1) := by
    rw [mem₅, Mem.readW_writeW_self32]
    apply BitVec.eq_of_toNat_eq
    have := hi.pos; have := hi.le
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl]
    omega_arith
  by_cases hlast : r = 1
  · subst hlast
    left
    exact ⟨hev, esi₅, esp₅, rd₅, wr₅, frame₅, fun j hjn => done₅ j (by omega_arith)⟩
  · right
    refine ⟨by rw [hev]; simp only [ne_eq, Option.some.injEq, decide_eq_true_eq]; omega_arith,
      r - 1, by have := hi.pos; omega_arith, ?_⟩
    refine ⟨by have := hi.pos; omega_arith, by have := hi.le; omega_arith, esi₅, esp₅, rd₅, wr₅, frame₅, data₅, left₅,
      done₅, ?_⟩
    intro j hj₁ hj₂
    have := hi.pos
    have := hi.le
    obtain hne : j ≠ n - r := by omega_arith
    rw [other j hj₂ hne]
    exact hi.todo j (by omega_arith) hj₂

end VG.Proof.Idea.X86

namespace VG.Proof.Idea.X86

open VG VG.X86 VG.Impl.Idea.X86

theorem loop_ok {z : Spec.Idea.Schedule} {P₀ : BitVec 32} {n : Nat} {m₀ : Mem} {o : State}
    (hc : LCtx z P₀ n o) (hn : 1 ≤ n)
    (hdata : o.mem.readW ((o.gpr .esi).setWidth 64 + BitVec.ofNat 64 dataSlot) 32 = P₀)
    (hleft : o.mem.readW ((o.gpr .esi).setWidth 64 + BitVec.ofNat 64 leftSlot) 32 = BitVec.ofNat 32 n)
    (htodo : ∀ j < n, Spec.Idea.blockAt o.mem (P₀.setWidth 64 + BitVec.ofNat 64 (8 * j)) =
      Spec.Idea.blockAt m₀ (P₀.setWidth 64 + BitVec.ofNat 64 (8 * j))) :
    WP isa (.loop (.block ecbBody) .ne) o (LoopPost z P₀ n m₀ o) := by
  refine WP.loop (M := isa) (LoopInv z P₀ n m₀ o) (fun r t hi => step_ok hc r t hi) n o
    ⟨hn, Nat.le_refl _, rfl, rfl, rfl, rfl, Frame.refl _ _, ?_, hleft, fun j hj => by omega_arith,
      fun j _ hj => htodo j hj⟩
  rw [Nat.sub_self, Nat.mul_zero, hdata]; exact (BitVec.add_zero _).symm

theorem ecb_wp (s : State) (hs : ecbContract.pre s) :
    WP isa ecb s (fun s' => abiPreserved s s' ∧ ecbContract.post s s') := by
  obtain hp := EPre.of hs
  obtain fB := hp.fB; have fSp := hp.fSp; have fD := hp.fD
  simp only [slots] at fB
  obtain ⟨o, ho, pi⟩ := prologue_run s hp
  let z := Spec.Idea.scheduleAt s.mem ((arg s 0).setWidth 64)
  let n := (arg s 2).toNat
  let B : Addr := (arg s 3).setWidth 64
  unfold ecb
  refine WP.seq (WP.of_runBlock ⟨o, ho, ?_⟩)
  obtain hc : LCtx z (arg s 1) n o := by
    refine ⟨.exact (by rw [pi.esi, pi.wr, hp.wr]; simp) (by rw [pi.esi]; simp only [slots]; omega_arith)
      (by rw [pi.esi, pi.sched]), by rw [pi.wr, hp.wr]; simp [n], by rw [pi.esi]; exact hp.dDB, fD⟩
  obtain blocks₀ : ∀ j < n, Spec.Idea.blockAt o.mem ((arg s 1).setWidth 64 + BitVec.ofNat 64 (8 * j)) =
      Spec.Idea.blockAt s.mem ((arg s 1).setWidth 64 + BitVec.ofNat 64 (8 * j)) := fun j hj =>
    blockAt_congr (frame_bytes pi.frame (by
      intro q hq; simp only [List.mem_singleton] at hq; subst hq
      exact hp.dDB.sub_left (Offset.sub_base _ (by omega_arith))) (by decide))
  refine WP.seq (WP.mono (Q := LoopPost z (arg s 1) n s.mem o) ?_ fun t ht => ?_)
  · have hz : isa.eval .e o = some (decide (n = 0)) := by
      show o.zf = _
      rw [pi.zf, show arg s 2 - 0 = arg s 2 from BitVec.sub_zero _]
      congr 1
    refine WP.ite _ hz (fun h0 => ?_) (fun h0 => ?_)
    · have h0 : n = 0 := by simpa using h0
      exact WP.block_nil ⟨rfl, rfl, rfl, rfl, Frame.refl _ _, fun j hj => by omega_arith⟩
    · have h0 : n ≠ 0 := by simpa using h0
      refine loop_ok hc (Nat.pos_of_ne_zero h0) (by rw [pi.esi]; exact pi.data)
        (by rw [pi.esi, pi.left]; simp [n]) blocks₀
  · -- Restoring the registers.
    obtain esiT : t.gpr .esi = arg s 3 := ht.esi.trans pi.esi
    obtain savedT : ∀ j < 4, t.mem.readW (B + BitVec.ofNat 64 (savedSlot + 4 * j)) 32 = s.gpr (sreg j) := by
      intro j hj
      rw [← pi.saved j hj]
      refine ht.frame.readW (r := ⟨B + BitVec.ofNat 64 (savedSlot + 4 * j), 4⟩) (Region.contains_self _ _)
        (fun q hq => ?_) (by decide)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact (hp.dDB.sub_right (r₂' := ⟨B + BitVec.ofNat 64 (savedSlot + 4 * j), 4⟩)
          (Offset.sub_base _ (by simp only [savedSlot, slots]; omega_arith))).symm
      · simp only [slotsR, pi.esi]
        exact Offset.disjoint _ (by simp only [savedSlot, t0Slot]; omega_arith)
          (by simp only [savedSlot]; omega_arith) (by simp only [t0Slot]; omega_arith)
    obtain rdT : ∀ u : State, u.gpr .esi = arg s 3 → u.mem = t.mem → u.rd = t.rd → u.wr = t.wr →
        ∀ j, j < 4 → readSrc u (.mem (at_ .esi (savedSlot + 4 * j))) = some (s.gpr (sreg j)) :=
      fun u he hm hr hw j hj => by
        rw [load_src, he, addr_eq (by simp only [savedSlot]; omega_arith), hm, savedT j hj]
        rw [he, addr_eq (by simp only [savedSlot]; omega_arith), hr, hw, ht.rd, ht.wr, pi.rd, pi.wr, hp.wr]
        exact ⟨⟨(arg s 3).setWidth 64, 4 * slots⟩, by simp,
          Offset.contains_base _ (by simp only [savedSlot, slots]; omega_arith) (by simp only [savedSlot]; omega_arith)⟩
    obtain ⟨u₁, k₁, w₁, f₁⟩ := mov_run .ebx _ _ t (rdT t esiT rfl rfl rfl 0 (by decide))
    obtain ⟨u₂, k₂, w₂, f₂⟩ := mov_run .edi _ _ u₁ (rdT u₁ (by rw [f₁.reg .esi (by decide), esiT]) f₁.mem
      f₁.rd f₁.wr 2 (by decide))
    obtain e₂ : Keep [.ebx, .edi] t u₂ := (f₁.weaken (by decide)).trans (f₂.weaken (by decide))
    obtain ⟨u₃, k₃, w₃, f₃⟩ := mov_run .ebp _ _ u₂ (rdT u₂ (by rw [e₂.reg .esi (by decide), esiT]) e₂.mem
      e₂.rd e₂.wr 3 (by decide))
    obtain e₃ : Keep [.ebx, .edi, .ebp] t u₃ := (e₂.weaken (by decide)).trans (f₃.weaken (by decide))
    obtain ⟨u₄, k₄, w₄, f₄⟩ := mov_run .esi _ _ u₃ (rdT u₃ (by rw [e₃.reg .esi (by decide), esiT]) e₃.mem
      e₃.rd e₃.wr 1 (by decide))
    obtain e₄ : Keep [.ebx, .edi, .ebp, .esi] t u₄ := (e₃.weaken (by decide)).trans (f₄.weaken (by decide))
    refine WP.of_runBlock ⟨u₄, ?_, ⟨fun r hr => ?_, ?_⟩, ?_⟩
    · exact run_append (a := [_]) k₁ (run_append (a := [_]) k₂ (run_append (a := [_]) k₃ k₄))
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [f₄.reg .ebx (by decide), f₃.reg .ebx (by decide), f₂.reg .ebx (by decide), w₁]; rfl
      · exact w₄
      · rw [f₄.reg .edi (by decide), f₃.reg .edi (by decide), w₂]; rfl
      · rw [f₄.reg .ebp (by decide), w₃]; rfl
      · rw [e₄.reg .esp (by decide), ht.esp, pi.esp]
    · rw [e₄.mem]
      obtain hr₀ : ∀ q ∈ [(⟨(arg s 3).setWidth 64, 4 * slots⟩ : Region)],
          Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ q := fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact hp.rB
      obtain h₁ := pi.frame.readW (r := ⟨(s.gpr .esp).setWidth 64, 4⟩) (w := 32) (Region.contains_self _ _) hr₀
        (by decide)
      obtain hr₁ : ∀ q ∈ [(⟨(arg s 1).setWidth 64, 8 * n⟩ : Region), slotsR o],
          Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ q := fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact hp.rD
        · simp only [slotsR, pi.esi]
          exact hp.rB.sub_right (r₂' := ⟨(arg s 3).setWidth 64 + BitVec.ofNat 64 t0Slot, 12⟩)
            (Offset.sub_base _ (by decide))
      obtain h₂ := ht.frame.readW (r := ⟨(s.gpr .esp).setWidth 64, 4⟩) (w := 32) (Region.contains_self _ _) hr₁
        (by decide)
      rw [h₂, h₁]
    · show Spec.Idea.blocksAt u₄.mem _ _ = _
      rw [e₄.mem]
      exact blocksAt_eq _ _ _ _ _ ht.done

end VG.Proof.Idea.X86
