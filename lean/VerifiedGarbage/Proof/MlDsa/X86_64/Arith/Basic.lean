module

public import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Common
import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
import VerifiedGarbage.Proof.MlKem.X86_64.Bytes
import VerifiedGarbage.Proof.MlKem.X86_64.Contracts
public import VerifiedGarbage.Proof.MlDsa.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.MlDsa.Arith.Zq

/-!
# ML-DSA on x86-64: the contracts

It uses the symbolic execution of ML-KEM's x86-64 proofs (`xrun`, `Keep`,
`WP.keep`, the counted loops, `Proof/MlKem/X86_64/Wp.lean`), which are about
the ISA, not ML-KEM.

For each function, a contract with the facts of its shared contract
(`Proof/MlDsa/Contract.lean`) spelled out for x86-64: the arguments in their
registers, the permitted regions, their disjointness, and the
postcondition. The proofs are written against these, and
`Verified.of_correct` moves them to the shared contracts, which imply them
(`mldsa_implies`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly gprPreserved_of wp_countdown wp_counted ifp ifn
  toNat_setWidth64 toNat_setWidth32_64 read_zero)
open VG.Spec.MlDsa (q n Poly Zq)
open VG.Proof.MlDsa (coeffAt polyAt Reduced PolyIs)

/-! ## Immediates -/

theorem sxQD : BitVec.signExtend 64 qImm = 8380417 := by decide

theorem sx_ofNat {n : Nat} (h : n < 2 ^ 31) : BitVec.signExtend 64 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n := by
  have hm : (BitVec.ofNat 32 n).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem ea_atD (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = s.gpr b + BitVec.ofNat 64 d := by
  simp only [State.ea, at_]
  congr 1

/-- `xrun` (`Proof/MlKem/X86_64/Wp.lean`) for this code's memory operands
and immediates. -/
tactic_template "xrund" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| xrun [ea_atD, sxQD, $ls,*])

/-! ## The contracts -/

/-- The return address. -/
abbrev retR (s : State) : Region := ⟨s.gpr .rsp, 8⟩

/-- A polynomial, at `p`. -/
abbrev pR (p : Addr) : Region := ⟨p, 1024⟩

/-- `vg_mldsa_ntt(f = rdi, scratch = rsi)` and `vg_mldsa_inv_ntt`: `f`
becomes `t f`. -/
def inPlaceK (t : Poly → Poly) : Contract isa where
  pre s :=
    s.rd = [] ∧ s.wr = [pR (s.gpr .rdi), pR (s.gpr .rsi)] ∧ (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) ∧
    (retR s).Disjoint (pR (s.gpr .rdi)) ∧ (retR s).Disjoint (pR (s.gpr .rsi)) ∧ Reduced s.mem (s.gpr .rdi)
  post s s' := PolyIs s'.mem (s.gpr .rdi) (t (polyAt s.mem (s.gpr .rdi)))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `vg_mldsa_add(f = rdi, g = rsi)` and `vg_mldsa_sub(f = rdi, g = rsi)`:
`f` becomes `t f g`. -/
def accK (t : Poly → Poly → Poly) : Contract isa where
  pre s :=
    s.rd = [pR (s.gpr .rsi)] ∧ s.wr = [pR (s.gpr .rdi)] ∧
    (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) ∧ (retR s).Disjoint (pR (s.gpr .rdi)) ∧
    (retR s).Disjoint (pR (s.gpr .rsi)) ∧ Reduced s.mem (s.gpr .rdi) ∧ Reduced s.mem (s.gpr .rsi)
  post s s' := PolyIs s'.mem (s.gpr .rdi) (t (polyAt s.mem (s.gpr .rdi)) (polyAt s.mem (s.gpr .rsi)))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `vg_mldsa_multiply_ntt(h = rdi, f = rsi, g = rdx)` and
`vg_mldsa_multiply_add_ntt`: `h` becomes `t h f g`, if `hPre` of `h` (for
`vg_mldsa_multiply_add_ntt`, that it is reduced). -/
def mulK (t : Poly → Poly → Poly → Poly) (hPre : Mem → Addr → Prop) : Contract isa where
  pre s :=
    s.rd = [pR (s.gpr .rsi), pR (s.gpr .rdx)] ∧ s.wr = [pR (s.gpr .rdi)] ∧
    (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) ∧ (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rdx)) ∧
    (retR s).Disjoint (pR (s.gpr .rdi)) ∧ (retR s).Disjoint (pR (s.gpr .rsi)) ∧
    (retR s).Disjoint (pR (s.gpr .rdx)) ∧ hPre s.mem (s.gpr .rdi) ∧
    Reduced s.mem (s.gpr .rsi) ∧ Reduced s.mem (s.gpr .rdx)
  post s s' := PolyIs s'.mem (s.gpr .rdi)
    (t (polyAt s.mem (s.gpr .rdi)) (polyAt s.mem (s.gpr .rsi)) (polyAt s.mem (s.gpr .rdx)))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rsp = s₂.gpr .rsp

/-! ## Satisfiability -/

/-- In memory of zeros, every polynomial is reduced. -/
theorem reduced_zero (p : Addr) : Reduced (fun _ => 0) p := fun _ _ => by
  simp only [coeffAt, Mem.readW, read_zero]
  decide

/-- `sig_implies`, whose satisfiability witness may need `Reduced` of the
memory of zeros. -/
tactic_template "mldsa_implies " "[" ls:Lean.Parser.Tactic.simpLemma,* "]"
    " [" ws:Lean.Parser.Tactic.simpLemma,* "]" " using " w:term : tactic => `(tactic| exact
  { pre := by sig_implies_pre [$ls,*]
    post := by sig_implies_post [$ls,*]
    pub := by sig_implies_pub [$ls,*]
    sat := by
      refine ⟨$w, ?_⟩
      sig_pre [$ls,*]
      and_intros
      all_goals first
        | rfl
        | decide
        | exact Region.disjoint_of_sep (by decide)
        | exact reduced_zero _
        | (intro a h₁ h₂
           set_option linter.unusedSimpArgs false in
           simp only [Region.Contains, $ws,*] at h₁ h₂
           bv_omega) })

end VG.Proof.MlDsa.X86_64.Arith
