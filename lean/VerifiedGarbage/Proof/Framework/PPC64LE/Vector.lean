module

public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.PPC64LE.Reduce
public meta import VerifiedGarbage.Proof.Framework.UnfoldStep

/-! # PPC64LE vector execution and constant-time analysis

Vector contents are secret. Only GPRs and the stack pointer can contribute
to addresses or branch conditions. Vector loads/stores require public
address operands; extracting a doubleword produces a secret GPR value.
-/

@[expose] public section
namespace VG.PPC64LE

theorem vpr_writeV (s : State) (d : VReg) (x : BitVec 128) (r : VReg) :
    (s.writeV d x).vpr r = if r = d then x else s.vpr r := rfl

theorem gpr_writeV (s : State) (d : VReg) (x : BitVec 128) : (s.writeV d x).gpr = s.gpr := rfl
theorem mem_writeV (s : State) (d : VReg) (x : BitVec 128) : (s.writeV d x).mem = s.mem := rfl
theorem rd_writeV (s : State) (d : VReg) (x : BitVec 128) : (s.writeV d x).rd = s.rd := rfl
theorem wr_writeV (s : State) (d : VReg) (x : BitVec 128) : (s.writeV d x).wr = s.wr := rfl
theorem sp_writeV (s : State) (d : VReg) (x : BitVec 128) : (s.writeV d x).sp = s.sp := rfl
theorem lr_writeV (s : State) (d : VReg) (x : BitVec 128) : (s.writeV d x).lr = s.lr := rfl


theorem vpr_write (s : State) (d : Reg) (x : BitVec 64) :
    (s.write d x).vpr = s.vpr := rfl

theorem write_overwrite (s : State) (d : Reg) (x y : BitVec 64) :
    (s.write d x).write d y = s.write d y := by
  simp only [State.write]
  congr 1
  funext r
  split <;> rfl

/-- A vector-only computation preserves the scalar state and memory. -/
structure VOnly (rs : List VReg) (s s' : State) : Prop where
  v : ∀ r, r ∉ rs → s'.vpr r = s.vpr r
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  lr : s'.lr = s.lr

theorem VOnly.refl (rs : List VReg) (s : State) : VOnly rs s s :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem VOnly.trans {rs ts : List VReg} {s u v : State}
    (h : VOnly rs s u) (h' : VOnly ts u v) : VOnly (rs ++ ts) s v :=
  ⟨fun r hr => by
    rw [List.mem_append, not_or] at hr
    exact (h'.v r hr.2).trans (h.v r hr.1),
   h'.gpr.trans h.gpr, h'.mem.trans h.mem, h'.rd.trans h.rd,
   h'.wr.trans h.wr, h'.sp.trans h.sp, h'.lr.trans h.lr⟩

theorem VOnly.weaken {rs ts : List VReg} {s u : State} (h : VOnly rs s u)
    (hs : ∀ r ∈ rs, r ∈ ts) : VOnly ts s u :=
  ⟨fun r hr => h.v r (fun h' => hr (hs r h')), h.gpr, h.mem, h.rd, h.wr, h.sp, h.lr⟩

theorem sldoi8_eq (n m : BitVec 128) :
    ((n ++ m) <<< 64).extractLsb' 128 128 = n.extractLsb' 0 64 ++ m.extractLsb' 64 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append,
    hi, decide_true, Bool.true_and]
  simp only [show 128 + i < 128 + 128 by omega, show ¬ 128 + i < 64 by omega,
    decide_true, decide_false, Bool.not_false, Bool.true_and]
  by_cases h : i < 64
  · simp only [h, show 128 + i - 64 < 128 by omega, decide_true, ite_true, Bool.true_and]
    exact congrArg m.getLsbD (by omega)
  · simp only [h, show ¬ 128 + i - 64 < 128 by omega, show i - 64 < 64 by omega,
      decide_true, ite_false, Bool.true_and, Nat.zero_add]
    exact congrArg n.getLsbD (by omega)

theorem ofVBytes_congr (f g : Nat → BitVec 8) (h : ∀ i < 16, f i = g i) :
    ofVBytes f = ofVBytes g := by
  have e : (List.range 16).map (fun i => (f i).setWidth 128 <<< (8 * (15 - i))) =
      (List.range 16).map (fun i => (g i).setWidth 128 <<< (8 * (15 - i))) := by
    apply List.map_congr_left
    intro i hi
    rw [h i (List.mem_range.mp hi)]
  simpa only [ofVBytes, List.foldl_map] using
    congrArg (fun xs : List (BitVec 128) => xs.foldl (fun a b => a ||| b) 0) e

theorem byteTerm_bit (f : Nat → BitVec 8) {k j r : Nat}
    (hk : k < 16) (hj : j < 16) (hr : r < 8) :
    ((f k).setWidth 128 <<< (8 * (15-k))).getLsbD (8*j+r) =
      if j = 15-k then (f k).getLsbD r else false := by
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  by_cases h : j = 15-k
  · subst j
    simp only [show ¬8*(15-k)+r < 8*(15-k) by omega, decide_false,
      Bool.not_false, Nat.add_sub_cancel_left, show 8*(15-k)+r < 128 by omega,
      show r < 128 by omega, decide_true, Bool.true_and, ite_true]
  · have h' : 8*j+r < 8*(15-k) ∨ 8 ≤ 8*j+r-8*(15-k) := by omega
    rcases h' with h' | h' <;> simp [h, h']

theorem packed_bit (f : Nat → BitVec 8) {j r : Nat} (hj : j < 16) (hr : r < 8) :
    ∀ k, k ≤ 16 →
    ((List.range k).foldl (fun x i => x ||| ((f i).setWidth 128 <<< (8*(15-i)))) (0#128)).getLsbD (8*j+r) =
      if 15-j < k then (f (15-j)).getLsbD r else false
  | 0, _ => by simp
  | k+1, hk => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      BitVec.getLsbD_or, packed_bit f hj hr k (by omega), byteTerm_bit f (by omega) hj hr]
    by_cases h : 15-j < k
    · simp [h, show 15-j < k+1 by omega, show j ≠ 15-k by omega]
    · by_cases e : j = 15-k
      · rw [ite_eq_right h, ite_eq_left e, ite_eq_left (show 15-j < k+1 by omega), Bool.false_or]
        exact congrArg (fun i => (f i).getLsbD r) (by omega)
      · simp [h, e, show ¬15-j < k+1 by omega]

theorem getLsbD_packed (f : Nat → BitVec 8) {j r : Nat} (hj : j < 16) (hr : r < 8) :
    (VG.PPC64LE.ofVBytes f).getLsbD (8*j+r) = (f (15-j)).getLsbD r := by
  simpa only [VG.PPC64LE.ofVBytes, BitVec.ofNat_eq_ofNat, show 15-j < 16 by omega, ite_true] using
    packed_bit f hj hr 16 (by decide)


theorem getLsbD_rev128 (x : BitVec 128) {i : Nat} (hi : i < 128) :
    (rev128 x).getLsbD i = x.getLsbD (8*(15-i/8)+i%8) := by
  have he : i = 8*(i/8)+i%8 := by omega
  calc
    _ = (rev128 x).getLsbD (8*(i/8)+i%8) := congrArg (rev128 x).getLsbD he
    _ = _ := by
      rw [rev128, getLsbD_packed _ (by omega) (by omega)]
      simp only [vbyte, BitVec.getLsbD_extractLsb', show i % 8 < 8 by omega,
        decide_true, Bool.true_and]
      exact congrArg x.getLsbD (by omega)

theorem rev128_rev128 (x : BitVec 128) : rev128 (rev128 x) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_rev128 _ hi, getLsbD_rev128 _ (by omega)]
  exact congrArg x.getLsbD (by omega)

namespace VectorTaint
open VG.PPC64LE.Taint (T pub set Agree)

def step (τ : T) : Instr → Option T
  | .vop _ | .mtvsrd .. => some τ
  | .lxvd2x _ a b | .stxvd2x _ a b => if pub τ a && pub τ b then some τ else none
  | .mfvsrd d _ => some (set τ d false)
  | i => Taint.step τ i

theorem step_sound {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State}
    (ha : Agree τ s₁ s₂) (hs : step τ i = some τ')
    (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    addrs i s₁ = addrs i s₂ ∧ Agree τ' s₁' s₂' := by
  cases i with
  | vop op =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [reduceExec, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨⟨_, _⟩, -, rfl⟩ := e₁
    obtain ⟨⟨_, _⟩, -, rfl⟩ := e₂
    exact ⟨rfl, ha⟩
  | mtvsrd d n =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [reduceExec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    exact ⟨rfl, ha⟩
  | mfvsrd d n =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [reduceExec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    exact ⟨rfl, ha.write d fun h => by cases h⟩
  | lxvd2x d a b =>
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    rename_i hp; cases hs
    simp only [Bool.and_eq_true] at hp
    refine ⟨by simp only [addrs, ha.reg hp.1, ha.reg hp.2], ?_⟩
    simp only [reduceExec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨_, -, _, -, rfl⟩ := e₁
    obtain ⟨_, -, _, -, rfl⟩ := e₂
    exact ha
  | stxvd2x n a b =>
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    rename_i hp; cases hs
    simp only [Bool.and_eq_true] at hp
    refine ⟨by simp only [addrs, ha.reg hp.1, ha.reg hp.2], ?_⟩
    simp only [reduceExec, Option.bind_eq_some_iff, State.store] at e₁ e₂
    obtain ⟨_, -, e₁⟩ := e₁; obtain ⟨_, -, e₂⟩ := e₂
    split at e₁ <;> [cases e₁; cases e₁]
    split at e₂ <;> [cases e₂; cases e₂]
    exact ha
  | _ => exact Taint.step_sound ha hs e₁ e₂

end VectorTaint

def vectorTaint : VG.Taint isa := { taint with
  step := VectorTaint.step
  step_sound := VectorTaint.step_sound }

end VG.PPC64LE

public meta section
namespace VG.PPC64LE

dsimproc reduceVOpEval (VOp.eval _ _) := fun e => do
  let some e' ← unfoldStep? e | return .continue
  return .visit e'

end VG.PPC64LE
