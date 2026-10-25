module

public import VerifiedGarbage.Impl.MdStream.RISCV64
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.RISCV64.Inline
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import all Init.Data.Nat.Bitwise.Basic

/-!
# Streaming Merkle–Damgård hash functions on RISC-V: `init`

Untrusted: everything here is checked by Lean. `initWords iv` stores the
words `iv` at `a0`, little-endian (`initK`); each hash function's proofs
read its initial hash value from them.
-/

@[expose] public section

namespace VG.Proof.MdStream.RISCV64

open VG VG.RISCV64 VG.RISCV64.ByteLoad VG.Impl.MdStream.RISCV64 VG.Impl.Words.RISCV64

/-- The contract of `initWords iv` writing an `n`-byte state: the words of
`iv` are at `a0`. -/
def initK (n : Nat) (iv : List (BitVec 32)) : Contract isa where
  pre s := s.rd = [] ∧ s.wr = [⟨s.gpr .a0, n⟩]
  post s s' := ∀ k < iv.length, s'.mem.readW (s.gpr .a0 + BitVec.ofNat 64 (4 * k)) 32 = iv[k]!
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.sp = s₂.sp

/-- The first `k` words of `iv` are stored. -/
structure InitI (iv : List (BitVec 32)) (s₀ : State) (k : Nat) (s : State) : Prop where
  a0 : s.gpr .a0 = s₀.gpr .a0
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  words : ∀ j < k, s.mem.readW (s₀.gpr .a0 + BitVec.ofNat 64 (4 * j)) 32 = iv[j]!

theorem readW_writeW_word (m : Mem) (p : Addr) (v : BitVec 32) {j k : Nat} (hj : j < 512)
    (hk : k < 512) (h : j ≠ k) :
    (m.writeW (p + BitVec.ofNat 64 (4 * k)) v).readW (p + BitVec.ofNat 64 (4 * j)) 32 =
    m.readW (p + BitVec.ofNat 64 (4 * j)) 32 :=
  Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide)

theorem init_step {n : Nat} (iv : List (BitVec 32)) (hn : 4 * iv.length ≤ n) (hl : iv.length ≤ 16)
    {s₀ : State} (hp : (initK n iv).pre s₀) {k : Nat} (hk : k < iv.length) {s : State}
    (h : InitI iv s₀ k s) :
    WP isa (.block (li32 .t0 iv[k]! ++ storeLE32 .t0 .t1 .a0 (4 * k))) s (InitI iv s₀ (k + 1)) := by
  rw [WP.block_append_iff]
  refine WP.mono (li32_ok _) fun s₁ e₁ => ?_
  subst e₁
  refine WP.mono (storeLE32_ok (by decide) (by decide) (by omega) ?_) fun s₂ e₂ => ?_
  · rw [RegUpd.wr_write, RegUpd.gpr_write_of_ne _ _ (by decide), h.wr, h.a0, hp.2]
    exact ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩
  subst e₂
  refine ⟨?_, h.rd, h.wr, fun j hj => ?_⟩
  · simp only [RegUpd.gpr_write, reduceCtorEq, ↓reduceIte, h.a0]
  · simp only [RegUpd.mem_write, RegUpd.gpr_write, reduceCtorEq, ↓reduceIte, h.a0, lo32_sext]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [readW_writeW_word _ _ _ (by omega) (by omega) (by omega)]
      exact h.words j hj
    · exact Mem.readW_writeW_self32 _ _ _

theorem init_correct {n : Nat} (iv : List (BitVec 32)) (hn : 4 * iv.length ≤ n) (hl : iv.length ≤ 16)
    {s₀ : State} (hp : (initK n iv).pre s₀) :
    WP isa (initWords iv) s₀ fun s' => (initK n iv).post s₀ s' :=
  WP.mono (wp_range_flatMap (M := isa) (InitI iv s₀) (fun k s hk h => init_step iv hn hl hp hk h)
    iv.length (Nat.le_refl _) s₀ ⟨rfl, rfl, rfl, fun _ h => absurd h (by omega)⟩) fun _ h => h.words

/-- No instruction of `init` writes a register other than `t0` and `t1`. -/
def initDst : Option Reg → Bool
  | some .t0 | some .t1 | none => true
  | _ => false

theorem init_dst (iv : List (BitVec 32)) (r : Reg) (hr : r ≠ .t0 ∧ r ≠ .t1) :
    ∀ i ∈ instrs (initWords iv), dstOf i ≠ some r := by
  intro i hi e
  have hc : ((instrs (initWords iv)).all fun i => initDst (dstOf i)) = true := by
    simp only [initWords, instrs, List.all_flatMap, List.all_eq_true, List.mem_range]
    intro k _
    simp [li32, storeLE32, dstOf, initDst]
  have := List.all_eq_true.mp hc i hi
  rw [e] at this
  revert this hr; cases r <;> decide

theorem noCalls_init (iv : List (BitVec 32)) : (initWords iv).noCalls = true := rfl

/-- A state satisfying the precondition. -/
def initSat (n : Nat) : State where
  gpr r := match r with | .a0 => 0x1000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, n⟩]

theorem initAgree {n : Nat} {iv : List (BitVec 32)} {s₁ s₂ : State} (hpub : (initK n iv).pub s₁ s₂) :
    VG.RISCV64.Taint.Agree (VG.RISCV64.Taint.ofRegs [.a0]) s₁ s₂ := by
  obtain ⟨h1, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; exact h1

/-- `initWords iv`, given that the taint analysis accepts its code. -/
theorem init_verified {n : Nat} (iv : List (BitVec 32)) (hn : 4 * iv.length ≤ n) (hl : iv.length ≤ 16)
    (hct : ConstantTime RISCV64.isa (initK n iv).pre (initK n iv).pub (initWords iv)) :
    Verified RISCV64.target (initWords iv) (initK n iv) := by
  refine ⟨fun s hs => ?_, hct, ⟨initSat n, rfl, rfl⟩⟩
  obtain ⟨t, s', he, h⟩ := init_correct iv hn hl hs
  refine ⟨t, s', he, ⟨fun r hr => Exec.gpr (init_dst iv r ?_) he (.inl (noCalls_init iv)),
    Exec.sp he, Exec.gpr (init_dst iv .ra (by decide)) he (.inl (noCalls_init iv))⟩, h⟩
  revert hr; revert r; decide

end VG.Proof.MdStream.RISCV64
