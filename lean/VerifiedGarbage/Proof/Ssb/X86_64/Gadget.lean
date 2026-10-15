import VerifiedGarbage.Proof.Framework.X86_64.Ssb

/-!
# Prototype: a store-bypass gadget and safe variants

`gadget` stores a secret (`rax`) to a slot, overwrites it with a public
pointer (`rsi`), loads the slot back and dereferences it. It is constant time
(`gadget_ct`), but not under speculative store bypass (`gadget_not_specCT`):
the load may see the secret. The analysis rejects it for every window from 1
(`gadget_rejected`), and accepts the same code with an `lfence` before the
load (`fenced_specCT`) or with enough instructions between the store and the
load (`padded_specCT`, `padded_rejected`).
-/

namespace VG.Proof.Ssb.X86_64

open VG.X86_64 VG.X86_64.Ssb

def at_ (b : Reg) : MemOp := { base := b }

def store : List Instr := [.store (at_ .rdi) .rax, .store (at_ .rdi) .rsi]
def use : List Instr := [.mov .rbx (.mem (at_ .rdi)), .mov .rcx (.mem (at_ .rbx))]
/-- `n` instructions that touch neither the slot nor the registers used. -/
def pad (n : Nat) : List Instr := List.replicate n (.alu .add .rdx (.imm 1))

def gadget : Prog X86_64.isa := .block (store ++ use)
def fenced : Prog X86_64.isa := .block (store ++ .lfence :: use)
def padded (n : Nat) : Prog X86_64.isa := .block (store ++ pad n ++ use)

/-- `rdi` points at a 16-byte writable region; `rdi` and `rsi` are public. -/
def Pre (s : State) : Prop := s.wr = [⟨s.gpr .rdi, 16⟩] ∧ (s.gpr .rdi).toNat + 16 ≤ 2 ^ 64
def Pub (s₁ s₂ : State) : Prop := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi

def τ₀ : X86_64.Taint.T := { regs := .ofList [.rdi, .rsi], flags := false, lens := [16], bases := [(.rdi, 0, 0)] }

theorem agree₀ (s₁ s₂ : State) (h₁ : Pre s₁) (h₂ : Pre s₂) (hp : Pub s₁ s₂) : X86_64.Taint.Agree τ₀ s₁ s₂ := by
  have wf : ∀ s, Pre s → X86_64.Taint.Wf τ₀ s := by
    intro s hs
    refine ⟨fun _ => ⟨by simp [hs.1, τ₀], by simp [hs.1], ?_⟩, fun p hp => ?_⟩
    · simp only [hs.1, List.mem_cons, List.not_mem_nil, or_false]
      rintro r rfl; dsimp only; omega
    · simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp; simp [X86_64.Taint.region, hs.1]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ h₁, wf _ h₂, ?_, ?_, X86_64.Taint.noLo⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.1
    · exact hp.2
  · rw [h₁.1, h₂.1, hp.1]
  · intro sl h; simp [τ₀] at h
  · intro sl h; simp [τ₀] at h

/-! ## The gadget -/

theorem gadget_ct : ConstantTime X86_64.isa Pre Pub gadget :=
  VG.Taint.constantTime (A := taint) τ₀ agree₀ (by taint_decide)

theorem gadget_rejected :
    VG.Taint.checkBlock (Ssb.taint 1) (T.init τ₀) (store ++ use) = none ∧
    VG.Taint.checkBlock (Ssb.taint 64) (T.init τ₀) (store ++ use) = none := by
  decide +kernel

/-- Two runs that differ only in the secret `rax`, where the third
instruction's load sees the memory before the second (one instruction old). -/
def run (rax : BitVec 64) : SState where
  arch :=
    { gpr := fun r => match r with | .rdi => 0x1000 | .rsi => 0x2000 | .rax => rax | _ => 0
      cf := none, zf := none, sf := none, of := none
      mem := fun _ => 0
      rd := [⟨0x2000, 0x100⟩]
      wr := [⟨0x1000, 16⟩] }
  hist := [fun _ => 0]
  dirs := fun n _ => if n = 2 then 1 else 0
  n := 0

theorem gadget_not_specCT : ¬ SpecCT 1 Pre Pub gadget := by
  intro h
  have r₁ : (execBlock (Ssb.isa 1) (store ++ use) (run 0x2000)).isSome = true := by decide +kernel
  have r₂ : (execBlock (Ssb.isa 1) (store ++ use) (run 0x2008)).isSome = true := by decide +kernel
  have pre : ∀ x, Pre (run x).arch ∧ (run x).hist.length = 1 :=
    fun _ => ⟨⟨rfl, show (0x1000 : BitVec 64).toNat + 16 ≤ 2 ^ 64 by decide +kernel⟩, rfl⟩
  have := h (run 0x2000) (run 0x2008) _ _ _ _ (pre _) (pre _) ⟨⟨rfl, rfl⟩, rfl, rfl⟩
    (.block (Option.some_get r₁).symm) (.block (Option.some_get r₂).symm)
  revert this
  decide +kernel

/-! ## Safe variants -/

theorem fenced_specCT : SpecCT 64 Pre Pub fenced := specCT τ₀ agree₀ rfl (by taint_decide)

/-- A store more than `W` instructions before the load cannot be bypassed. -/
theorem padded_specCT : SpecCT 4 Pre Pub (padded 4) := specCT τ₀ agree₀ rfl (by taint_decide)

theorem padded_rejected : VG.Taint.checkBlock (Ssb.taint 4) (T.init τ₀) (store ++ pad 3 ++ use) = none := by
  decide +kernel

end VG.Proof.Ssb.X86_64
