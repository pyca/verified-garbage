module

public import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Aes.Arm.Sbox
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit

/-!
# A block that stores only at given offsets of `sb` (ARMv7)

`runBlock_storesIn`: a block whose every instruction stores nothing but a
word at `sb + d`, for `lo ≤ d` and `d + 4 ≤ hi`, and never writes `sb`
(`storesIn lo hi`, checked of every instruction by evaluation), keeps `sb`
and the memory outside `[sb + lo, sb + hi)`. The tail of Camellia's eight
blocks stores the blocks through `sb`, whose slots the analysis of constant
time tracks, and this gives its frame, which the linear checker's (every
slot below `hi`) does not.
-/

@[expose] public section

namespace VG.Proof.Camellia.Arm

open VG VG.Arm
open VG.Impl.Aes.Arm (sb)

/-- `i` stores nothing but the word at `sb + d`, for `lo ≤ d` and `d + 4 ≤ hi`,
and does not write `sb`. -/
def storesIn (lo hi : Nat) : Instr → Bool
  | .str _ n d => n == sb && decide (lo ≤ d) && decide (d + 4 ≤ hi)
  | .strb .. | .push _ | .pop .. | .alloc _ | .free _ => false
  | i => !clobbers i sb

/-- The bytes `[sb + lo, sb + hi)`. -/
abbrev storeRegion (b : BitVec 32) (lo hi : Nat) : Region := ⟨State.addr b + BitVec.ofNat 64 lo, hi - lo⟩

theorem exec_mem_of_noStore {i : Instr} {s s' : State} (h : exec i s = some s')
    (hi : ∀ t n off, i ≠ .str t n off) (hb : ∀ t n off, i ≠ .strb t n off) : s'.mem = s.mem := by
  cases i with
  | str t n off => exact absurd rfl (hi t n off)
  | strb t n off => exact absurd rfl (hb t n off)
  | _ =>
    simp only [exec, State.load32, State.load8, Option.map_eq_some_iff] at h
    (repeat' split at h) <;>
    (try simp only [Option.some.injEq, reduceCtorEq] at h) <;>
    first
    | (subst h; rfl)
    | (obtain ⟨_, _, rfl⟩ := h; rfl)
    | (cases h)

theorem exec_storesIn {lo hi : Nat} {i : Instr} {s s' : State} (hs : storesIn lo hi i = true)
    (hfit : (s.gpr sb).toNat + hi ≤ 2 ^ 32) (h : exec i s = some s') :
    s'.gpr sb = s.gpr sb ∧ Frame [storeRegion (s.gpr sb) lo hi] s.mem s'.mem := by
  cases i with
  | str t n d =>
    simp only [storesIn, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hs
    obtain ⟨⟨rfl, h1⟩, h2⟩ := hs
    simp only [exec, State.store32] at h
    split at h <;> [skip; cases h]
    split at h <;> [skip; cases h]
    simp only [Option.some.injEq] at h; subst h
    refine ⟨rfl, (Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_⟩
    rw [VG.Arm.addr_add (by omega)]
    exact VG.Offset.contains _ h1 (by omega) (by have := (s.gpr sb).isLt; omega)
  | _ =>
    first
    | (simp [storesIn] at hs; done)
    | (refine ⟨exec_gpr (by simp_all [storesIn]) h, ?_⟩
       rw [exec_mem_of_noStore h (fun _ _ _ e => nomatch e) (fun _ _ _ e => nomatch e)]
       exact Frame.refl _ _)

theorem runBlock_storesIn {lo hi : Nat} : ∀ (is : List Instr) {s s' : State},
    is.all (storesIn lo hi) = true → (s.gpr sb).toNat + hi ≤ 2 ^ 32 → runBlock isa is s = some s' →
      s'.gpr sb = s.gpr sb ∧ Frame [storeRegion (s.gpr sb) lo hi] s.mem s'.mem
  | [], s, s', _, _, h => by
    rw [runBlock_nil, Option.some.injEq] at h; subst h; exact ⟨rfl, Frame.refl _ _⟩
  | i :: is, s, s', ha, hfit, h => by
    simp only [List.all_cons, Bool.and_eq_true] at ha
    rw [runBlock_cons] at h
    cases he : exec i s with
    | none => rw [he] at h; cases h
    | some s₁ =>
      rw [he, runStep_some] at h
      obtain ⟨b₁, f₁⟩ := exec_storesIn ha.1 hfit he
      obtain ⟨b₂, f₂⟩ := runBlock_storesIn is ha.2 (by rw [b₁]; exact hfit) h
      rw [b₁] at b₂ f₂
      exact ⟨b₂, f₁.trans f₂⟩

end VG.Proof.Camellia.Arm
