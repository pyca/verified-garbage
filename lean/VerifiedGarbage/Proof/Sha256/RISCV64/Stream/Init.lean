module

public import VerifiedGarbage.Impl.Sha256.RISCV64.Stream
meta import VerifiedGarbage.Impl.Sha256.RISCV64.Stream
public import VerifiedGarbage.Proof.Sha256.RISCV64.Contract
meta import VerifiedGarbage.Proof.Sha256.RISCV64.Contract
public import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RISCV64.Inline
meta import VerifiedGarbage.Proof.Framework.RISCV64.Inline
public import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Sha256.RISCV64.Compress
meta import VerifiedGarbage.Proof.Sha256.RISCV64.Compress
import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
meta import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
import all Init.Data.Nat.Bitwise.Basic

/-!
# Streaming SHA-256 on RISC-V: `init`

Untrusted: everything here is checked by Lean.
-/

@[expose] public section

namespace VG.Proof.Sha256.RISCV64.Stream

open VG VG.RISCV64 VG.RISCV64.ByteLoad VG.Impl.Sha256.RISCV64.Stream VG.Impl.Words.RISCV64
open VG.Proof.Sha256.RISCV64 (stateAt_eq readW_writeW_word)
open VG.Spec.Sha256 (stateAt H0 H0_224 HashValue)

/-- The first `k` words of `iv` are stored. -/
structure InitI (iv : HashValue) (s₀ : State) (k : Nat) (s : State) : Prop where
  a0 : s.gpr .a0 = s₀.gpr .a0
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  words : ∀ j < k, s.mem.readW (s₀.gpr .a0 + BitVec.ofNat 64 (4 * j)) 32 = iv[j]!

theorem init_step (iv : HashValue) {s₀ : State} (hp : (Proof.Sha256.initFromRISCV64 iv).pre s₀)
    {k : Nat} (hk : k < 8) {s : State} (h : InitI iv s₀ k s) :
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
    · rw [readW_writeW_word _ _ _ (by omega) hk (by omega)]
      exact h.words j hj
    · exact Mem.readW_writeW_self32 _ _ _

/-- No instruction of `init` writes a register other than `t0` and `t1`. -/
def initDst : Option Reg → Bool
  | some .t0 | some .t1 | none => true
  | _ => false

theorem init_correct (iv : HashValue) {s₀ : State} (hp : (Proof.Sha256.initFromRISCV64 iv).pre s₀) :
    WP isa (initWith iv) s₀ fun s' => (Proof.Sha256.initFromRISCV64 iv).post s₀ s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (InitI iv s₀) (fun k s hk h => init_step iv hp hk h) 8
    (Nat.le_refl _) s₀ ⟨rfl, rfl, rfl, fun _ h => absurd h (by omega)⟩) fun s' h => ?_
  refine Proof.Sha256.Stream.reprFrom_nil (stateAt_eq fun k hk => ?_)
  rw [h.words k hk, getElem!_pos iv k hk]

theorem init_dst (iv : HashValue) (r : Reg) (hr : r ≠ .t0 ∧ r ≠ .t1) :
    ∀ i ∈ instrs (initWith iv), dstOf i ≠ some r := by
  intro i hi e
  have hc : ((instrs (initWith iv)).all fun i => initDst (dstOf i)) = true := by
    simp only [initWith, instrs, List.all_flatMap, List.all_eq_true, List.mem_range]
    intro k _
    simp [li32, storeLE32, dstOf, initDst]
  have := List.all_eq_true.mp hc i hi
  rw [e] at this
  revert this hr; cases r <;> decide

/-- A state satisfying the precondition. -/
def initSat : State where
  gpr r := match r with | .a0 => 0x1000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 96⟩]

theorem noCalls_init (iv : HashValue) : (initWith iv).noCalls = true := rfl

/-- `init`'s functional correctness and calling-convention obligations. -/
theorem initFrom_ok (iv : HashValue) :
    ∀ s, (Proof.Sha256.initFromRISCV64 iv).pre s → ∃ t s', Exec isa (initWith iv) s t s' ∧
      abiPreserved s s' ∧ (Proof.Sha256.initFromRISCV64 iv).post s s' := by
  intro s hs
  obtain ⟨t, s', he, h⟩ := init_correct iv hs
  refine ⟨t, s', he, ⟨fun r hr => Exec.gpr (init_dst iv r ?_) he (.inl (noCalls_init iv)),
    Exec.sp he, Exec.gpr (init_dst iv .ra (by decide)) he (.inl (noCalls_init iv))⟩, h⟩
  revert hr; revert r; decide

theorem agree₀ {s₁ s₂ : State} (iv : HashValue) (hpub : (Proof.Sha256.initFromRISCV64 iv).pub s₁ s₂) :
    VG.RISCV64.Taint.Agree (VG.RISCV64.Taint.ofRegs [.a0]) s₁ s₂ := by
  obtain ⟨h1, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; exact h1

theorem init_verified : Verified RISCV64.target init (Proof.Sha256.initFromRISCV64 H0) :=
  ⟨initFrom_ok H0, VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0])
    (fun _ _ _ _ h => agree₀ H0 h) (by taint_decide), ⟨initSat, rfl, rfl⟩⟩

theorem init224_verified : Verified RISCV64.target init224 (Proof.Sha256.initFromRISCV64 H0_224) :=
  ⟨initFrom_ok H0_224, VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0])
    (fun _ _ _ _ h => agree₀ H0_224 h) (by taint_decide), ⟨initSat, rfl, rfl⟩⟩

end VG.Proof.Sha256.RISCV64.Stream
