module

public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Inline
public import VerifiedGarbage.Proof.Framework.Taint

/-!
# Constant time of code that leaks memory both runs agree on (RISC-V)

The RISC-V counterpart of PPC64LE's `memTaint`
(`Proof/MlDsa/PPC64LE/Pack/HintCT.lean`), for `vg_mldsa_hint_bit_pack` and
`vg_mldsa_hint_bit_unpack`, which branch and index memory on their input,
which they load from memory.

The taint analysis (`Proof/Framework/RISCV64/Taint.lean`) treats memory as
secret. `memTaint` is one for code that runs with permissions only on memory
whose bytes two runs agree on (`MemEq`): every load it makes is then public,
and a store keeps the agreement if it stores a public value at a public
address. Neither function has a frame or calls.
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Pack.Hint

open VG VG.RISCV64
open VG.RISCV64.Taint (T pub set)

/-- `m₁` and `m₂` agree on every byte of the regions `rs`. -/
def MemEq (rs : List Region) (m₁ m₂ : Mem) : Prop := ∀ x, InRegions rs x 1 → m₁ x = m₂ x

/-- The registers `τ` agree, and the permissions and the memory they permit. -/
def MAgree (τ : T) (s₁ s₂ : State) : Prop :=
  VG.RISCV64.Taint.Agree τ s₁ s₂ ∧ s₁.rd = s₂.rd ∧ s₁.wr = s₂.wr ∧ MemEq (s₁.rd ++ s₁.wr) s₁.mem s₂.mem

/-- Instructions that only write a general-purpose register. -/
def regOp : Instr → Bool
  | .add .. | .sub .. | .addw .. | .subw .. | .sltu .. | .mul .. | .mulhu .. | .logic .. | .addi ..
  | .addiw .. | .logicImm .. | .li .. | .lui .. | .shift .. | .shiftReg .. => true
  | _ => false

/-- Loads are public, stores must store public values; the other memory
instructions and frames are not analysed. -/
def mstep (τ : T) : Instr → Option T
  | .load _ t n _ => if pub τ n then some (set τ t true) else none
  | .store _ t n _ => if pub τ n && pub τ t then some τ else none
  | i => if regOp i then VG.RISCV64.Taint.step τ i else none

theorem exec_regOp {i : Instr} (hi : regOp i = true) {s s' : State} (h : exec i s = some s') :
    s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  cases i <;> simp [regOp] at hi
  case shift op sz d n sh =>
    cases sz <;> simp only [exec] at h <;> split at h <;>
      first | (simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl, rfl⟩) | (simp at h)
  case shiftReg op sz d n m =>
    cases sz <;> simp only [exec] at h <;>
      first | (simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl, rfl⟩) | (simp at h)
  all_goals simp only [exec] at h
  all_goals first
    | (simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl, rfl⟩)
    | (split at h <;> (try split at h) <;>
        first | (simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl, rfl⟩) | (simp at h))

theorem MemEq.read {rs : List Region} {m₁ m₂ : Mem} (h : MemEq rs m₁ m₂) {a : Addr} {n : Nat}
    (hi : InRegions rs a n) (hn : n < 2 ^ 64) : m₁.read a n = m₂.read a n := by
  obtain ⟨r, hr, hc⟩ := hi
  exact Mem.read_congr fun i hi' =>
    h _ ⟨r, hr, hc.byte (by rw [Mem.sub_ofNat_toNat a (by omega)]; exact hi')⟩

theorem MemEq.write {rs : List Region} {m₁ m₂ : Mem} (h : MemEq rs m₁ m₂) (a : Addr) (n : Nat)
    (v : BitVec (8 * n)) : MemEq rs (m₁.write a n v) (m₂.write a n v) := fun x hx => by
  simp only [Mem.write]
  split
  · rfl
  · exact h x hx

theorem regOp_sound {τ τ' : T} {i : Instr} (hr : regOp i = true) {s₁ s₂ s₁' s₂' : State}
    (ha : MAgree τ s₁ s₂) (hs : VG.RISCV64.Taint.step τ i = some τ') (e₁ : exec i s₁ = some s₁')
    (e₂ : exec i s₂ = some s₂') : addrs i s₁ = addrs i s₂ ∧ MAgree τ' s₁' s₂' := by
  obtain ⟨hadd, ht⟩ := VG.RISCV64.Taint.step_sound ha.1 hs e₁ e₂
  obtain ⟨m₁, r₁, w₁⟩ := exec_regOp hr e₁
  obtain ⟨m₂, r₂, w₂⟩ := exec_regOp hr e₂
  exact ⟨hadd, ht, by rw [r₁, r₂, ha.2.1], by rw [w₁, w₂, ha.2.2.1], by
    rw [m₁, m₂, r₁, w₁]; exact ha.2.2.2⟩

theorem addr_agree {τ : T} {s₁ s₂ : State} (ha : MAgree τ s₁ s₂) {n : Reg} (hn : pub τ n = true)
    (bytes off : Nat) {a₁ a₂ : Addr} (h₁ : addr s₁ bytes n off = some a₁)
    (h₂ : addr s₂ bytes n off = some a₂) : a₁ = a₂ := by
  simp only [addr] at h₁ h₂
  rw [ha.1.reg hn] at h₁
  split at h₁ <;> [rename_i hc; cases h₁]
  rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at h₂
  exact (Option.some.inj h₁).symm.trans (Option.some.inj h₂)

theorem load_sound {τ : T} {s₁ s₂ : State} (ha : MAgree τ s₁ s₂) {n : Reg} (hn : pub τ n = true)
    (bytes off : Nat) {a₁ a₂ : Addr} (h₁ : addr s₁ bytes n off = some a₁)
    (h₂ : addr s₂ bytes n off = some a₂) {v₁ v₂ : BitVec (8 * bytes)}
    (l₁ : s₁.load a₁ bytes = some v₁) (l₂ : s₂.load a₂ bytes = some v₂) (hb : bytes < 2 ^ 64) :
    v₁ = v₂ := by
  have ea := addr_agree ha hn bytes off h₁ h₂
  subst ea
  simp only [State.load] at l₁ l₂
  split at l₁ <;> [rename_i hi; cases l₁]
  split at l₂ <;> [skip; cases l₂]
  cases l₁; cases l₂
  exact ha.2.2.2.read hi hb

theorem store_sound {τ : T} {s₁ s₂ : State} (ha : MAgree τ s₁ s₂) {n : Reg} (hn : pub τ n = true)
    (bytes off : Nat) {a₁ a₂ : Addr} (h₁ : addr s₁ bytes n off = some a₁)
    (h₂ : addr s₂ bytes n off = some a₂) {v : BitVec (8 * bytes)} {s₁' s₂' : State}
    (e₁ : s₁.store a₁ bytes v = some s₁') (e₂ : s₂.store a₂ bytes v = some s₂') :
    MAgree τ s₁' s₂' := by
  have ea := addr_agree ha hn bytes off h₁ h₂
  subst ea
  simp only [State.store] at e₁ e₂
  split at e₁ <;> [skip; cases e₁]
  split at e₂ <;> [skip; cases e₂]
  cases e₁; cases e₂
  exact ⟨ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.write _ _ _⟩

theorem mstep_sound {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State} (ha : MAgree τ s₁ s₂)
    (hs : mstep τ i = some τ') (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    addrs i s₁ = addrs i s₂ ∧ MAgree τ' s₁' s₂' := by
  cases i with
  | load sz t n off =>
    simp only [mstep] at hs
    split at hs <;> [rename_i hn; cases hs]
    cases hs
    refine ⟨by simp [addrs, ha.1.reg hn], ?_⟩
    simp only [exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨a₁, h₁, v₁, l₁, rfl⟩ := e₁; obtain ⟨a₂, h₂, v₂, l₂, rfl⟩ := e₂
    have hv := load_sound ha hn _ off h₁ h₂ l₁ l₂ (by cases sz <;> decide)
    subst hv
    exact ⟨ha.1.write t fun _ => rfl, ha.2⟩
  | store sz t n off =>
    simp only [mstep] at hs
    split at hs <;> [rename_i hn; cases hs]
    cases hs
    simp only [Bool.and_eq_true] at hn
    refine ⟨by simp [addrs, ha.1.reg hn.1], ?_⟩
    simp only [exec, Option.bind_eq_some_iff] at e₁ e₂
    obtain ⟨a₁, h₁, e₁⟩ := e₁; obtain ⟨a₂, h₂, e₂⟩ := e₂
    rw [ha.1.reg hn.2] at e₁
    exact store_sound ha hn.1 _ off h₁ h₂ e₁ e₂
  | _ =>
    simp only [mstep] at hs
    split at hs <;> [rename_i hr; cases hs]
    exact regOp_sound hr ha hs e₁ e₂

/-- Taint tracking over memory both runs agree on, for RISC-V code without
calls or frames. -/
def memTaint : VG.Taint isa where
  T := VG.RISCV64.Taint.T
  Agree := MAgree
  step := mstep
  step_sound := mstep_sound
  condPub := VG.RISCV64.Taint.condPub
  cond_sound h hc := VG.RISCV64.Taint.cond_sound h.1 hc
  meet τ₁ τ₂ := τ₁.inter τ₂
  meet_left h := ⟨taint.meet_left h.1, h.2⟩
  meet_right h := ⟨taint.meet_right h.1, h.2⟩
  le τ σ := τ.subset σ
  le_sound hle h := ⟨taint.le_sound hle h.1, h.2⟩
  call _ := none
  call_sound _ hs _ _ := by cases hs
  ret _ := none
  ret_sound _ hs _ _ := by cases hs
  push _ _ := none
  push_sound _ hs _ _ := by cases hs
  pop _ _ := none
  pop_sound _ hs _ _ := by cases hs

end VG.Proof.MlDsa.RISCV64.Pack.Hint
