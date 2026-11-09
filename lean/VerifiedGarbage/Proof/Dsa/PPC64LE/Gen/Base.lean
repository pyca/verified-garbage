module

public import VerifiedGarbage.Impl.Dsa.PPC64LE.Generation
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Spec.Dsa.ParameterSearchContract
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32
import VerifiedGarbage.Proof.RsaKeyGen.TrialTable32
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract

/-! # DSA parameter generation on PPC64LE: the public parameters

`mkG s`: the public parameters of a call of `vg_dsa_parameter_search` from
`s`: its arguments, the state's first two words (the seeds left and the
modulus's width) and the tape's bytes, which the contract makes public, and
the address of the table of small primes the probable-prime tests read
(`kT`), which the contract's calling convention adds to the readable regions.
`CIn s`: the contract's precondition (`cin_of_pre`), for the functions we
call using at most `STK` bytes below the stack pointer.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation

/-- The public parameters of a call. -/
structure GP where
  sp : Addr
  out : Addr
  outLen : Nat
  usedP : Addr
  /-- `rand`, which holds the seeds, the witnesses and the `h` candidates. -/
  wit : Addr
  witLen : Nat
  scr : Addr
  scrLen : Nat
  stP : Addr
  /-- The seeds left, `state[0]`. -/
  k0 : Nat
  pLen : Nat
  qLen : Nat
  witB : List Byte
  tab : Addr

/-- The modulus's width, `state[1]`. -/
abbrev pLenOf (s : State) : Nat := (s.mem.readW (s.gpr .r10 + 8) 64).toNat

def mkG (s : State) : GP where
  sp := s.sp
  out := s.gpr .r3
  outLen := (s.gpr .r4).toNat
  usedP := s.gpr .r5
  wit := s.gpr .r6
  witLen := (s.gpr .r7).toNat
  scr := s.gpr .r8
  scrLen := (s.gpr .r9).toNat
  stP := s.gpr .r10
  k0 := (s.mem.readW (s.gpr .r10) 64).toNat
  pLen := pLenOf s
  qLen := Spec.Dsa.generationQLen (pLenOf s)
  witB := Spec.Rsa.bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat
  tab := s.syms Impl.RsaKeyGen.TrialTable32.symbol

/-- The table of small primes the probable-prime tests read. -/
abbrev kT : List (String × List (BitVec 64)) := Impl.RsaKeyGen.TrialTable32.consts

namespace GP
variable (G : GP)

/-- The seeds are read from `rand`. -/
abbrev seeds : Addr := G.wit
abbrev seedsLen : Nat := G.witLen
abbrev seedsB : List Byte := G.witB

abbrev rScr : Region := ⟨G.scr, G.scrLen * 8⟩
abbrev rOut : Region := ⟨G.out, G.outLen⟩
abbrev rUsed : Region := ⟨G.usedP, 8⟩
abbrev rWit : Region := ⟨G.wit, G.witLen⟩
abbrev rSeeds : Region := G.rWit
abbrev rSt : Region := ⟨G.stP, 32⟩
abbrev rTab : Region := ⟨G.tab, 8192⟩

end GP

/-- The stack below the stack pointer the functions we call use. -/
abbrev rBelow (σ : State) (STK : Nat) : Region := ⟨σ.sp - BitVec.ofNat 64 STK, STK⟩

/-- The precondition under `abi`, for `STK` bytes of stack. -/
structure CIn0 (STK : Nat) (s : State) : Prop where
  spLo : STK ≤ s.sp.toNat
  rd : s.rd = [(mkG s).rWit]
  wr : s.wr = [(mkG s).rOut, (mkG s).rUsed, (mkG s).rScr, (mkG s).rSt]
  oU : (mkG s).rOut.Disjoint (mkG s).rUsed
  oW : (mkG s).rOut.Disjoint (mkG s).rWit
  oC : (mkG s).rOut.Disjoint (mkG s).rScr
  oS : (mkG s).rOut.Disjoint (mkG s).rSt
  uW : (mkG s).rUsed.Disjoint (mkG s).rWit
  uC : (mkG s).rUsed.Disjoint (mkG s).rScr
  uS : (mkG s).rUsed.Disjoint (mkG s).rSt
  wC : (mkG s).rWit.Disjoint (mkG s).rScr
  wS : (mkG s).rWit.Disjoint (mkG s).rSt
  cS : (mkG s).rScr.Disjoint (mkG s).rSt
  bO : (rBelow s STK).Disjoint (mkG s).rOut
  bU : (rBelow s STK).Disjoint (mkG s).rUsed
  bW : (rBelow s STK).Disjoint (mkG s).rWit
  bC : (rBelow s STK).Disjoint (mkG s).rScr
  bS : (rBelow s STK).Disjoint (mkG s).rSt
  nO : (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64
  nU : (s.gpr .r5).toNat + 8 ≤ 2 ^ 64
  nW : (s.gpr .r6).toNat + (s.gpr .r7).toNat ≤ 2 ^ 64
  nC : (s.gpr .r8).toNat + (s.gpr .r9).toNat * 8 ≤ 2 ^ 64
  nS : (s.gpr .r10).toNat + 32 ≤ 2 ^ 64
  valid : Spec.Dsa.generationPLenValid (pLenOf s)
  outLen : (s.gpr .r4).toNat = 2 * pLenOf s + Spec.Dsa.generationQLen (pLenOf s)
  scrLen : Spec.Dsa.generationScratchWords (pLenOf s) ≤ (s.gpr .r9).toNat
  seeds : (s.mem.readW (s.gpr .r10) 64).toNat ≤ Spec.Dsa.parameterSeeds
  budget : s.mem.readW (s.gpr .r10 + 16) 64 = BitVec.ofNat 64 (Spec.Dsa.parameterEntropy (pLenOf s))
  randLen : (s.gpr .r7).toNat ≤ Spec.Dsa.parameterEntropy (pLenOf s)

theorem cin0_of_pre {n : Nat} (s : State) (h : (Spec.Dsa.parameterSearchContract abi (n + 1)).pre s) :
    CIn0 (n + 1) s := by
  sig_pre [Spec.Dsa.parameterSearchContract, Spec.Dsa.parameterSearchSig, abi, argRegs, stackBelow] at h
  sig_pre [Spec.Dsa.parameterSearchContract, Spec.Dsa.parameterSearchSig, abi, argRegs, stackBelow] at h
  sig_split h
  constructor
  all_goals try dsimp only [mkG, GP.rOut, GP.rUsed, GP.rWit, GP.rScr, GP.rSt, pLenOf]
  all_goals with_reducible assumption

/-- The contract's precondition, for `STK` bytes of stack. -/
structure CIn (STK : Nat) (s : State) : Prop where
  spLo : STK ≤ s.sp.toNat
  rd : s.rd = [(mkG s).rWit, (mkG s).rTab]
  wr : s.wr = [(mkG s).rOut, (mkG s).rUsed, (mkG s).rScr, (mkG s).rSt]
  oU : (mkG s).rOut.Disjoint (mkG s).rUsed
  oW : (mkG s).rOut.Disjoint (mkG s).rWit
  oC : (mkG s).rOut.Disjoint (mkG s).rScr
  oS : (mkG s).rOut.Disjoint (mkG s).rSt
  uW : (mkG s).rUsed.Disjoint (mkG s).rWit
  uC : (mkG s).rUsed.Disjoint (mkG s).rScr
  uS : (mkG s).rUsed.Disjoint (mkG s).rSt
  wC : (mkG s).rWit.Disjoint (mkG s).rScr
  wS : (mkG s).rWit.Disjoint (mkG s).rSt
  cS : (mkG s).rScr.Disjoint (mkG s).rSt
  bO : (rBelow s STK).Disjoint (mkG s).rOut
  bU : (rBelow s STK).Disjoint (mkG s).rUsed
  bW : (rBelow s STK).Disjoint (mkG s).rWit
  bC : (rBelow s STK).Disjoint (mkG s).rScr
  bS : (rBelow s STK).Disjoint (mkG s).rSt
  nO : (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64
  nU : (s.gpr .r5).toNat + 8 ≤ 2 ^ 64
  nW : (s.gpr .r6).toNat + (s.gpr .r7).toNat ≤ 2 ^ 64
  nC : (s.gpr .r8).toNat + (s.gpr .r9).toNat * 8 ≤ 2 ^ 64
  nS : (s.gpr .r10).toNat + 32 ≤ 2 ^ 64
  valid : Spec.Dsa.generationPLenValid (pLenOf s)
  outLen : (s.gpr .r4).toNat = 2 * pLenOf s + Spec.Dsa.generationQLen (pLenOf s)
  scrLen : Spec.Dsa.generationScratchWords (pLenOf s) ≤ (s.gpr .r9).toNat
  seeds : (s.mem.readW (s.gpr .r10) 64).toNat ≤ Spec.Dsa.parameterSeeds
  budget : s.mem.readW (s.gpr .r10 + 16) 64 = BitVec.ofNat 64 (Spec.Dsa.parameterEntropy (pLenOf s))
  randLen : (s.gpr .r7).toNat ≤ Spec.Dsa.parameterEntropy (pLenOf s)
  held : Abi.constsHeld s.mem (fun name => s.syms name) kT
  tFit : (mkG s).tab.toNat + 8192 ≤ 2 ^ 64
  tO : (mkG s).rTab.Disjoint (mkG s).rOut
  tU : (mkG s).rTab.Disjoint (mkG s).rUsed
  tC : (mkG s).rTab.Disjoint (mkG s).rScr
  tS : (mkG s).rTab.Disjoint (mkG s).rSt
  tB : (mkG s).rTab.Disjoint (rBelow s STK)
  tAl : (mkG s).tab.toNat % 64 = 0

/-- The table's regions under `abi.withConsts kT`. -/
theorem constRegs_kT (s : State) : constRegs kT s = [(mkG s).rTab] := by
  simp only [constRegs, kT, Impl.RsaKeyGen.TrialTable32.consts, Abi.constRegions_cons, Abi.constRegions_nil,
    VG.Proof.RsaKeyGen.TrialTable32.packed_length]
  rfl

theorem cin_of_pre {n : Nat} (s : State)
    (h : (Spec.Dsa.parameterSearchContract (abi.withConsts kT) (n + 1)).pre s) : CIn (n + 1) s := by
  obtain ⟨h₀, hk⟩ := (pre_consts (c₀ := (Impl.RsaKeyGen.TrialTable32.symbol, Impl.RsaKeyGen.TrialTable32.packed))
    (cs := []) (sig := Spec.Dsa.parameterSearchSig)).mp h
  have c := cin0_of_pre (stripConsts kT s) h₀
  obtain ⟨hd, held, ht, hal⟩ := hk
  have e : constRegs [(Impl.RsaKeyGen.TrialTable32.symbol, Impl.RsaKeyGen.TrialTable32.packed)] s = _ :=
    constRegs_kT s
  rw [e] at ht hd hal
  obtain ⟨tFit, tW, tR⟩ := ht _ (List.mem_cons_self (l := []))
  have hrd : s.rd = (stripConsts kT s).rd ++
      s.rd.drop (s.rd.length - [(Impl.RsaKeyGen.TrialTable32.symbol, Impl.RsaKeyGen.TrialTable32.packed)].length) :=
    (List.take_append_drop _ _).symm
  rw [hd, c.rd] at hrd
  have hw : s.wr = [(mkG s).rOut, (mkG s).rUsed, (mkG s).rScr, (mkG s).rSt] := c.wr
  exact ⟨c.spLo, hrd, hw, c.oU, c.oW, c.oC, c.oS, c.uW, c.uC, c.uS, c.wC, c.wS, c.cS, c.bO, c.bU, c.bW, c.bC, c.bS, c.nO, c.nU, c.nW, c.nC, c.nS, c.valid, c.outLen, c.scrLen, c.seeds, c.budget, c.randLen, held, tFit,
    tW _ (by rw [hw]; simp), tW _ (by rw [hw]; simp), tW _ (by rw [hw]; simp), tW _ (by rw [hw]; simp),
    tR _ (by simp [abi, stackBelow]), hal _ (List.mem_cons_self (l := []))⟩

theorem CIn.lens {STK : Nat} {s : State} (h : CIn STK s) :
    ((mkG s).pLen = 128 ∧ (mkG s).qLen = 20) ∨ ((mkG s).pLen = 256 ∧ (mkG s).qLen = 32) ∨
      ((mkG s).pLen = 384 ∧ (mkG s).qLen = 32) := by
  have := h.valid
  simp only [Spec.Dsa.generationPLenValid, Bool.or_eq_true, beq_iff_eq] at this
  simp only [mkG, Spec.Dsa.generationQLen]
  rcases this with (e | e) | e <;> simp [e]

end VG.Proof.Dsa.PPC64LE.Gen
