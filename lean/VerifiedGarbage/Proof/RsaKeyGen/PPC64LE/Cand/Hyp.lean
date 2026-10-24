module

public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Ctx
public import VerifiedGarbage.Proof.RsaKeyGen.TrialFilter
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.Candidate
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32

/-!
# A candidate on PPC64LE: what trial division must do

`vg_rsa_keygen_candidate` takes its trial division as a parameter (`trial`,
the shared `Trial.trial hTrial` of the DSA's and RSA's searches, proven on
its own). `DivOk trial` is what the candidate's proofs need of it:

* from the candidate in array 0 of the Montgomery working space at `B`
  (`Env`), the number `n` of the table's entries to try in header word
  `hTrial`, and the table `TrialTable32` readable at its symbol's address
  (`DivIn`), it ends with `r22` the flag of a divisor among the first `n`
  entries (`trialPrefix`), memory unchanged, and only `tdRegs` (and the link
  register, which `adrSym` writes) changed;
* two runs from such states, with the same working space, `n`, table and
  stack pointer, and candidates that the first `n` entries divide alike,
  leak the same trace.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.Proof.Mont
open VG.Impl.RsaKeyGen.PPC64LE.Candidate (hTrial)
open VG.Impl.RsaKeyGen (TrialTable32.symbol TrialTable32.packed)
open VG.Proof.MillerRabin.PPC64LE (Env arr)

/-- The registers trial division may write (and the link register). -/
def tdRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r22, .r23, .r24]

/-- What trial division starts from. -/
structure DivIn (s : State) (B : Addr) (Z w n : Nat) : Prop where
  env : Env s B Z w
  cnt : word s.mem B (8 * hTrial) = BitVec.ofNat 64 n
  n1 : 1 ≤ n
  n2 : n ≤ 1024
  fit : (s.syms TrialTable32.symbol).toNat + 8 * 1024 ≤ 2 ^ 64
  tab : (⟨s.syms TrialTable32.symbol, 8 * 1024⟩ : Region) ∈ s.rd
  held : ∀ i < 1024, s.mem.readW (s.syms TrialTable32.symbol + BitVec.ofNat 64 (8 * i)) 64 =
    TrialTable32.packed.getD i 0

/-- Two runs of trial division whose traces must agree. -/
def DivRel (s₁ s₂ : State) : Prop :=
  ∃ B Z w n, DivIn s₁ B Z w n ∧ DivIn s₂ B Z w n ∧ s₁.sp = s₂.sp ∧
    s₁.syms TrialTable32.symbol = s₂.syms TrialTable32.symbol ∧
    ∀ i < n, entryDivides (arr s₁.mem B w 0) i = entryDivides (arr s₂.mem B w 0) i

/-- What the candidate's proofs need of trial division. -/
structure DivOk (trial : Prog isa) : Prop where
  ok : ∀ {s : State} {B : Addr} {Z w n : Nat}, DivIn s B Z w n →
    WP isa trial s fun t =>
      t.gpr .r22 = BitVec.ofNat 64 (if trialPrefix (arr s.mem B w 0) n then 1 else 0) ∧ t.mem = s.mem ∧
        (∀ r, r ∉ tdRegs → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp
  ct : ∀ {P : State → State → Prop}, (∀ s₁ s₂, P s₁ s₂ → DivRel s₁ s₂) → RelCT isa P trial fun _ _ => True

end VG.Proof.RsaKeyGen.PPC64LE.Cand
