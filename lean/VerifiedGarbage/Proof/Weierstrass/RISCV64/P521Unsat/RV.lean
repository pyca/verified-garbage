module

public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P521Unsat.Mul
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P521Unsat.Add
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P521Unsat.Unpack
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P521Unsat.Pack

/-!
# Arithmetic modulo P-521's prime in 58-bit limbs, on RISC-V: the contracts by register

The five functions of `Impl/Weierstrass/RISCV64/P521Unsat.lean`, with
GenWide's entry and copies (`GenWide.fnP_rv`), meet contracts by register
as GenWide's do (`ws` in `a0`, the offsets in `a1`–`a3`, nine words each,
their own working space the top 576 bytes of `ws`):

* `umulRV`: tight operands to a tight result, the product modulo `p`;
* `uaddRV`, `usubRV`: the sum, and `[a] + 4p - [b]`, likewise;
* `unpackRV`: a number below `2⁵²²` to tight limbs of the same number;
* `packRV`: tight limbs to the nine words of their residue modulo `p`.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64.P521Unsat

open VG VG.RISCV64 VG.Impl.Weierstrass.RISCV64.P521Unsat
open VG.Impl.Weierstrass.Mont (p521p Keeps)
open VG.Proof.Weierstrass.RISCV64 (rvPre rvPub arg res offArg rvOwn rvOwnEnd)
open VG.Proof.Weierstrass.RISCV64.GenWide (fnP_rv)

/-- What the five contracts keep. -/
abbrev ukeeps (s s' : State) : Prop :=
  Keeps 9 (s.gpr .a0) (offArg s .a1) s.mem s'.mem (rvOwn 9) (rvOwnEnd 9)

/-- The product. -/
def umulRV : Contract isa where
  pre s := rvPre p521p s ∧ Tight (arg p521p s .a2) ∧ Tight (arg p521p s .a3)
  post s s' := Tight (res p521p s s') ∧ uv (res p521p s s') % p = uv (arg p521p s .a2) * uv (arg p521p s .a3) % p ∧
    ukeeps s s'
  pub := rvPub

/-- The sum. -/
def uaddRV : Contract isa where
  pre s := rvPre p521p s ∧ Tight (arg p521p s .a2) ∧ Tight (arg p521p s .a3)
  post s s' := Tight (res p521p s s') ∧ uv (res p521p s s') % p = (uv (arg p521p s .a2) + uv (arg p521p s .a3)) % p ∧
    ukeeps s s'
  pub := rvPub

/-- The difference, with `4p` added. -/
def usubRV : Contract isa where
  pre s := rvPre p521p s ∧ Tight (arg p521p s .a2) ∧ Tight (arg p521p s .a3)
  post s s' := Tight (res p521p s s') ∧
    uv (res p521p s s') % p = (uv (arg p521p s .a2) + 4 * p - uv (arg p521p s .a3)) % p ∧ ukeeps s s'
  pub := rvPub

/-- Words to limbs. -/
def unpackRV : Contract isa where
  pre s := rvPre p521p s ∧ arg p521p s .a2 < 2 ^ 522
  post s s' := Tight (res p521p s s') ∧ uv (res p521p s s') = arg p521p s .a2 ∧ ukeeps s s'
  pub := rvPub

/-- Limbs to the words of their residue. -/
def packRV : Contract isa where
  pre s := rvPre p521p s ∧ Tight (arg p521p s .a2)
  post s s' := res p521p s s' = uv (arg p521p s .a2) % p ∧ ukeeps s s'
  pub := rvPub

theorem umul_rv (s : State) (hs : umulRV.pre s) :
    ∃ t s', Exec isa mulFn s t s' ∧ abiPreserved s s' ∧ umulRV.post s s' := by
  obtain ⟨t, s', he, a, ⟨v1, v2⟩, k⟩ := fnP_rv (S := p521p) (by decide) (by decide) @core_spec hs.1 hs.2
  exact ⟨t, s', he, a, v1, v2, k⟩

theorem uadd_rv (s : State) (hs : uaddRV.pre s) :
    ∃ t s', Exec isa addFn s t s' ∧ abiPreserved s s' ∧ uaddRV.post s s' := by
  obtain ⟨t, s', he, a, ⟨v1, v2⟩, k⟩ := fnP_rv (S := p521p) (by decide) (by decide) @add_spec hs.1 hs.2
  exact ⟨t, s', he, a, v1, v2, k⟩

theorem usub_rv (s : State) (hs : usubRV.pre s) :
    ∃ t s', Exec isa subFn s t s' ∧ abiPreserved s s' ∧ usubRV.post s s' := by
  obtain ⟨t, s', he, a, ⟨v1, v2⟩, k⟩ := fnP_rv (S := p521p) (by decide) (by decide) @sub_spec hs.1 hs.2
  exact ⟨t, s', he, a, v1, v2, k⟩

theorem unpack_rv (s : State) (hs : unpackRV.pre s) :
    ∃ t s', Exec isa unpackFn s t s' ∧ abiPreserved s s' ∧ unpackRV.post s s' := by
  obtain ⟨t, s', he, a, ⟨v1, v2⟩, k⟩ := fnP_rv (S := p521p) (by decide) (by decide) @unpack_spec hs.1 hs.2
  exact ⟨t, s', he, a, v1, v2, k⟩

theorem pack_rv (s : State) (hs : packRV.pre s) :
    ∃ t s', Exec isa packFn s t s' ∧ abiPreserved s s' ∧ packRV.post s s' := by
  obtain ⟨t, s', he, a, v, k⟩ := fnP_rv (S := p521p) (by decide) (by decide) @pack_spec hs.1 hs.2
  exact ⟨t, s', he, a, v, k⟩

end VG.Proof.Weierstrass.RISCV64.P521Unsat
