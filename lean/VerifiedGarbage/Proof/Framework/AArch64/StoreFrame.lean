import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.Mem

/-!
# Code that stores only at given offsets of a base register (AArch64)

`Exec.storeFrame`: code whose every instruction stores nothing but the eight
bytes at `x3 + d`, for offsets `d` that `ok` accepts (sixteen bytes at
`x3 + d`, for `strq`, if it accepts `d` and `d + 8`), and never writes `x3`
(`storesAt ok`, checked of every instruction by evaluation), keeps `x3` and
every byte that no such store covers (`Unstored`), whatever its loops and
calls.
-/

namespace VG.AArch64

/-- Whether `i` stores nothing but the eight bytes at `x3 + d`, for `ok d` (the sixteen bytes at
`x3 + d`, for `ok d` and `ok (d + 8)`), and does not write `x3`. -/
def storesAt (ok : Nat → Bool) : Instr → Bool
  | .str .x _ .x3 d => ok d
  | .strq _ .x3 d => ok d && ok (d + 8)
  | .str .. | .strb .. | .strq .. | .push _ | .pop _ | .alloc _ | .free _ => false
  | i => dstOf i != some .x3

/-- The byte at `a` is in no store at `base + d`, for `ok d`. -/
def Unstored (ok : Nat → Bool) (base a : Addr) : Prop :=
  ∀ d, ok d = true → ¬ (a - (base + BitVec.ofNat 64 d)).toNat < 8

theorem exec_mem_of_noStore {i : Instr} {s s' : State} (h : exec i s = some s')
    (hi : ∀ sz t n off, i ≠ .str sz t n off) (hb : ∀ t n off, i ≠ .strb t n off)
    (hq : ∀ t n off, i ≠ .strq t n off) : s'.mem = s.mem := by
  cases i with
  | str sz t n off => exact absurd rfl (hi sz t n off)
  | strb t n off => exact absurd rfl (hb t n off)
  | strq t n off => exact absurd rfl (hq t n off)
  | ldr sz t n off =>
    simp only [exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, -, v, -, rfl⟩ := h
    rfl
  | ldrb t n off =>
    simp only [exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, -, v, -, rfl⟩ := h
    rfl
  | ldrq t n off =>
    simp only [exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, -, v, -, rfl⟩ := h
    rfl
  | vop op =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨⟨_, _⟩, -, rfl⟩ := h
    rfl
  | ldrSp t off =>
    simp only [exec] at h
    split at h <;> [skip; cases h]
    obtain ⟨v, -, rfl⟩ := Option.map_eq_some_iff.mp h
    rfl
  | ccmp sz n imm nzcv cond =>
    simp only [exec] at h
    split at h <;> [skip; cases h]
    simp only [Option.some.injEq] at h; subst h
    split <;> rfl
  | push _ | pop _ | alloc _ | free _ => simp only [exec, reduceCtorEq] at h
  | _ =>
    simp only [exec] at h
    first
    | (simp only [Option.some.injEq] at h; subst h; rfl)
    | (split at h <;> [skip; cases h]
       simp only [Option.some.injEq] at h; subst h; rfl)

open Classical in
/-- What `Exec.storeFrame` keeps: `x3`, and the bytes no store covers. -/
noncomputable def storeGet (ok : Nat → Bool) (s : State) : Addr × (Addr → BitVec 8) :=
  (s.gpr .x3, fun a => if Unstored ok (s.gpr .x3) a then s.mem a else 0)

theorem exec_storeGet {ok : Nat → Bool} {i : Instr} {s s' : State} (hi : storesAt ok i = true)
    (h : exec i s = some s') : storeGet ok s' = storeGet ok s := by
  have h3 : s'.gpr .x3 = s.gpr .x3 := by
    refine exec_gpr (fun hd => ?_) h
    unfold storesAt at hi
    split at hi <;> simp_all [dstOf]
  have hm : ∀ a, Unstored ok (s.gpr .x3) a → s'.mem a = s.mem a := by
    intro a ha
    unfold storesAt at hi
    split at hi
    · rename_i t d
      simp only [exec, Option.bind_eq_some_iff, State.store, addr] at h
      obtain ⟨a₀, ha₀, h⟩ := h
      split at ha₀ <;> [skip; cases ha₀]
      simp only [Option.some.injEq] at ha₀; subst ha₀
      split at h <;> cases h
      exact Mem.write_apply (ha d hi)
    · rename_i t d
      simp only [exec, Option.bind_eq_some_iff, State.store, addr] at h
      obtain ⟨a₀, ha₀, h⟩ := h
      split at ha₀ <;> [rename_i hd; cases ha₀]
      simp only [Option.some.injEq] at ha₀; subst ha₀
      split at h <;> cases h
      simp only [Bool.and_eq_true] at hi
      refine Mem.write_apply fun hlt => ?_
      have h1 := ha d hi.1
      have h2 := ha (d + 8) hi.2
      rw [Offset.sub_add_eq] at h1 h2 hlt
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat] at h1 h2 hlt
      have := (a - s.gpr .x3).isLt
      omega
    all_goals first
      | exact absurd hi (by decide)
      | exact congrFun (exec_mem_of_noStore h (by intros; simp_all) (by intros; simp_all)
          (by intros; simp_all)) a
  unfold storeGet
  rw [h3]
  refine Prod.ext rfl (funext fun a => ?_)
  dsimp only
  by_cases ha : Unstored ok (s.gpr .x3) a
  · simp only [ha, ↓reduceIte, hm a ha]
  · simp only [ha, ↓reduceIte]

/-- **Code that stores only at `x3 + d`, for `ok d`,** and never writes `x3`, keeps `x3` and
every byte that no such store covers. -/
theorem Exec.storeFrame {ok : Nat → Bool} {c : Prog isa} (hc : ∀ i ∈ instrs c, storesAt ok i = true)
    {s s' : State} {t : List Leak} (h : Exec isa c s t s') :
    s'.gpr .x3 = s.gpr .x3 ∧ ∀ a, Unstored ok (s.gpr .x3) a → s'.mem a = s.mem a := by
  have e := Exec.keep (storeGet ok) (ok := fun i => storesAt ok i = true)
    (fun hi he => exec_storeGet hi he) (fun {_ j _ _ _ _} hj _ hq _ => by
      change pop j _ _ = some _ at hq
      cases j <;> simp [storesAt, pop] at hj hq) hc
    (.inr fun s s₁ s₂ s' hcall hr hb => by
      rw [ret_eq hr, hb]
      obtain ⟨-, -, -, hm, hg⟩ := call_eq hcall
      unfold storeGet
      rw [hm, hg _ (by decide)]) h
  have e1 := congrArg Prod.fst e
  simp only [storeGet] at e1
  refine ⟨e1, fun a ha => ?_⟩
  have e2 := congrFun (congrArg Prod.snd e) a
  simp only [storeGet] at e2
  rw [e1] at e2
  simp only [ha, ↓reduceIte] at e2
  exact e2

/-- `Exec.storeFrame` beside any postcondition. -/
theorem WP.storeFrame {ok : Nat → Bool} {c : Prog isa} (hc : ∀ i ∈ instrs c, storesAt ok i = true)
    {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun t => Q t ∧ t.gpr .x3 = s.gpr .x3 ∧ ∀ a, Unstored ok (s.gpr .x3) a → t.mem a = s.mem a := by
  obtain ⟨tr, t, he, hq⟩ := h
  exact ⟨tr, t, he, hq, Exec.storeFrame hc he⟩

end VG.AArch64
