module

public import VerifiedGarbage.Proof.Sha512.Contract
import VerifiedGarbage.Proof.Framework.X86_64.Inline
public import VerifiedGarbage.Proof.Sha512.X86_64.Compress
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Proof.Sha512.Spec
public import VerifiedGarbage.Impl.Sha512.X86_64.Avx2
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Reduce

/-! ### `Sha512.X86_64.Avx2.Rounds`, which the modules that import this one used -/

section

/-!
# SHA-512 with AVX2 on x86-64: one round

`round j t` computes `roundKW`, with `Σ₀` and `Σ₁` as three `rorx`, `Ch` as a
sum of two disjoint masks and `Maj` from the previous round's `a ⊕ b`.
-/

@[expose] public section

namespace VG.Proof.Sha512.X86_64.Avx2

open VG VG.X86_64 VG.Impl.Sha512.X86_64.Avx2
open VG.Spec.Sha512 (HashValue Word Block K W bsig0 bsig1 ch maj)
open VG.Proof.Sha512 (roundKW rounds_succ round_eq)

/-- The working variables `v` are in the registers of round `t`, and
`b ⊕ c` is in `carry t`. -/
def Vars (t : Nat) (s : State) (v : HashValue) : Prop :=
  s.gpr (var t 0) = v[0] ∧ s.gpr (var t 1) = v[1] ∧ s.gpr (var t 2) = v[2] ∧
  s.gpr (var t 3) = v[3] ∧ s.gpr (var t 4) = v[4] ∧ s.gpr (var t 5) = v[5] ∧
  s.gpr (var t 6) = v[6] ∧ s.gpr (var t 7) = v[7] ∧ s.gpr (carry t) = v[1] ^^^ v[2]

/-- The registers that hold pointers and the count, and `rsp`: never written
by the rounds. -/
def pubRegs : List Reg := [.rdi, .rsi, .rdx, .rcx, .rsp]

theorem var_succ (t k : Nat) (hk : k < 7) : var (t + 1) (k + 1) = var t k := by
  simp only [var]; congr 1; omega

theorem var_succ_zero (t : Nat) : var (t + 1) 0 = var t 7 := by
  simp only [var]; congr 1; omega_using []

/-- The registers of a round are all different. -/
theorem round_nodup (t : Nat) :
    [var t 0, var t 1, var t 2, var t 3, var t 4, var t 5, var t 6, var t 7, carry t, carry (t + 1), T,
      .rdi, .rsi, .rdx, .rcx, .rsp].Nodup := by
  have e : carry (t + 1) = if t % 2 = 0 then .r14 else .r13 := by
    simp only [carry]; split <;> split <;> first | rfl | omega
  rw [e]
  simp only [var, carry]
  have h8 := Nat.mod_lt t (show 8 > 0 by omega_using [])
  rw [show t % 2 = t % 8 % 2 by omega_using []]
  generalize t % 8 = c at *
  revert h8; revert c; decide +kernel

theorem ch_add (e f g : Word) : ch e f g = (e &&& f) + (~~~e &&& g) := by
  rw [BitVec.add_eq_or_of_and_eq_zero]
  · ext i hi
    simp only [ch, BitVec.getElem_xor, BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not]
    cases e[i] <;> cases f[i] <;> cases g[i] <;> rfl
  · ext i hi
    simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_zero]
    cases e[i] <;> cases f[i] <;> cases g[i] <;> rfl

theorem maj_carry (a b c : Word) : maj a b c = (b ^^^ c) &&& (a ^^^ b) ^^^ b := by
  ext i hi
  simp only [maj, BitVec.getElem_xor, BitVec.getElem_and]
  cases a[i] <;> cases b[i] <;> cases c[i] <;> rfl

theorem bsig0_rorx (x : Word) : bsig0 x = x.rotateRight 28 ^^^ x.rotateRight 34 ^^^ x.rotateRight 39 := rfl
theorem bsig1_rorx (x : Word) : bsig1 x = x.rotateRight 14 ^^^ x.rotateRight 18 ^^^ x.rotateRight 41 := rfl

/-- `T₁` in the order the round adds it up. -/
theorem t1_order (h e f g k w : Word) :
    h + k + w + ((e &&& f) + (~~~e &&& g)) +
        (e.rotateRight 14 ^^^ e.rotateRight 18 ^^^ e.rotateRight 41) =
      h + bsig1 e + ch e f g + k + w := by
  rw [ch_add, bsig1_rorx]; ac_rfl

/-! ## Rounds of a block -/

/-- What the rounds leave alone. -/
def Keeps (s s' : State) : Prop :=
  s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r ∈ pubRegs, s'.gpr r = s.gpr r) ∧
    s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi

theorem Keeps.refl (s : State) : Keeps s s := ⟨rfl, rfl, rfl, fun _ _ => rfl, rfl, rfl⟩

theorem Keeps.trans {s₁ s₂ s₃ : State} (h₁ : Keeps s₁ s₂) (h₂ : Keeps s₂ s₃) : Keeps s₁ s₃ :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1,
    fun r hr => (h₂.2.2.2.1 r hr).trans (h₁.2.2.2.1 r hr), h₂.2.2.2.2.1.trans h₁.2.2.2.2.1,
    h₂.2.2.2.2.2.trans h₁.2.2.2.2.2⟩

/-- Round `t` of block `j` can read `Wₜ` of `M`. -/
def WOk (j : Nat) (M : Block) (s : State) (t : Nat) : Prop :=
  InRegions (s.rd ++ s.wr) (s.ea (wSlot j t)) 8 ∧ s.mem.readW (s.ea (wSlot j t)) 64 = W M t

theorem WOk.keeps {j : Nat} {M : Block} {s s' : State} {t : Nat} (h : WOk j M s t) (hk : Keeps s s') :
    WOk j M s' t := by
  have e : s'.ea (wSlot j t) = s.ea (wSlot j t) := by
    simp only [State.ea, wSlot, at_, hk.2.2.2.1 .rcx (by decide)]
  rw [WOk, e, hk.1, hk.2.1, hk.2.2.1]; exact h

end VG.Proof.Sha512.X86_64.Avx2

end

end

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
