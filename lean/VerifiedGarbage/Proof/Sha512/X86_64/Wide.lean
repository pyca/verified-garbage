module

public import VerifiedGarbage.Proof.Sha512.Contract
import VerifiedGarbage.Proof.Framework.X86_64.Inline
public import VerifiedGarbage.Proof.Sha512.X86_64.Compress
import VerifiedGarbage.Proof.Framework.Contract

/-!
# SHA-512 compression on x86-64 with the shared contract's scratch space

`compressWideX86_64` is `compressX86_64` with the 1328 bytes of scratch space
that the streaming functions pass the compression function
(`Impl.Sha512.X86_64.Stream.params`).
-/

@[expose] public section

namespace VG.Proof.Sha512

open VG.X86_64 in
/-- `compressX86_64` with 1328 bytes of scratch. -/
def compressWideX86_64 : Contract X86_64.isa :=
  { compressX86_64 with
    pre := fun s =>
      let state : Region := ⟨s.gpr .rdi, 64⟩
      let blocks : Region := ⟨s.gpr .rsi, 128 * (s.gpr .rdx).toNat⟩
      let scratch : Region := ⟨s.gpr .rcx, 1328⟩
      let ret : Region := ⟨s.gpr .rsp, 8⟩
      s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
      state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch ∧
      ret.Disjoint state ∧ ret.Disjoint scratch }

open VG.X86_64 in
/-- `compressWideX86_64` with `n` bytes of scratch space: the contract of an
implementation that uses no more (`compressWideX86_64` is
`compressWideX86_64S 1328`, for AVX2's, which uses the most). -/
def compressWideX86_64S (n : Nat) : Contract X86_64.isa :=
  { compressX86_64 with
    pre := fun s =>
      let state : Region := ⟨s.gpr .rdi, 64⟩
      let blocks : Region := ⟨s.gpr .rsi, 128 * (s.gpr .rdx).toNat⟩
      let scratch : Region := ⟨s.gpr .rcx, n⟩
      let ret : Region := ⟨s.gpr .rsp, 8⟩
      s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
      state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch ∧
      ret.Disjoint state ∧ ret.Disjoint scratch }

theorem compressWideX86_64_eq : compressWideX86_64 = compressWideX86_64S 1328 := rfl

end VG.Proof.Sha512

namespace VG.Proof.Sha512.X86_64

open _root_.VG.X86_64

theorem pfx {a : Addr} {m n : Nat} (h : Nat.ble m n = true) : Region.Prefix ⟨a, m⟩ ⟨a, n⟩ :=
  ⟨rfl, Nat.le_of_ble_eq_true h⟩
theorem sub176 (a : Addr) : Region.Sub ⟨a, 176⟩ ⟨a, 1328⟩ := Region.sub_prefix (by decide)

/-- A state satisfying `compressWideX86_64.pre`. -/
def wideSat : State := { satState with wr := [⟨0x1000, 64⟩, ⟨0x3000, 1328⟩] }

/-- A compression function verified with `a` bytes of scratch space is with
any `b ≥ a` (`Verified.widen`: it runs as it does with `a`). -/
theorem compressWideS_widen {c : Prog isa} {a b : Nat}
    (h : Verified X86_64.target c (Proof.Sha512.compressWideX86_64S a)) (hab : a ≤ b)
    (hsat : ∃ s, (Proof.Sha512.compressWideX86_64S b).pre s) :
    Verified X86_64.target c (Proof.Sha512.compressWideX86_64S b) :=
  Verified.widen h (fun s => [⟨s.gpr .rdi, 64⟩, ⟨s.gpr .rcx, a⟩])
    (fun _ ⟨h₁, _, h₃, h₄, h₅, h₆, h₇⟩ => ⟨h₁, rfl, h₃.sub_right (Region.sub_prefix hab), h₄,
      h₅.sub_right (Region.sub_prefix hab), h₆, h₇.sub_right (Region.sub_prefix hab)⟩)
    (fun _ ⟨_, h₂, _⟩ => h₂ ▸ .cons ⟨rfl, Nat.le_refl _⟩ (.cons ⟨rfl, hab⟩ .nil))
    (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat

/-- A state satisfying `compressWideX86_64S n`'s precondition, for the sizes
of the implementations. -/
theorem wideSatS (n : Nat) (h : n = 0 ∨ n = 192 ∨ n = 1328) : ∃ s, (Proof.Sha512.compressWideX86_64S n).pre s := by
  rcases h with rfl | rfl | rfl <;>
  exact ⟨{ satState with wr := [⟨0x1000, 64⟩, ⟨0x3000, _⟩] }, rfl, rfl, Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide)⟩

end VG.Proof.Sha512.X86_64
