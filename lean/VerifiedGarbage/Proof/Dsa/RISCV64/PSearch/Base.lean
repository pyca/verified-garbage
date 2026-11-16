module

public import VerifiedGarbage.Impl.Dsa.RISCV64.ParameterSearch
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Spec.Dsa.ParameterSearchContract
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.RISCV64.Consts
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32
import VerifiedGarbage.Proof.RsaKeyGen.TrialTable32
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract

/-! # DSA parameter search on RISC-V: the public parameters

`mkG s`: the public parameters of a call from `s`: the arguments, the
state's words 0 and 1 (the seeds the search may still reject and the
modulus's width), the tape's octets, which the contract makes public, and
the address of the table of small primes the probable-prime tests read
(`kT`), which the contract's calling convention adds to the readable
regions. `CIn STK s`: the contract's precondition (`cin_of_pre`), for the
functions we call using at most `STK` bytes below the stack pointer.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.PSearch
open VG VG.RISCV64
open VG.Impl.Dsa.RISCV64.ParameterSearch

/-- The public parameters of a call. -/
structure GP where
  sp : Addr
  out : Addr
  outLen : Nat
  used : Addr
  rand : Addr
  randLen : Nat
  scr : Addr
  scrLen : Nat
  state : Addr
  /-- The seeds the search may still reject, `state[0]`. -/
  left : Nat
  /-- The modulus's width, `state[1]`. -/
  pLen : Nat
  randB : List Byte
  tab : Addr

def mkG (s : State) : GP where
  sp := s.sp
  out := s.gpr .a0
  outLen := (s.gpr .a1).toNat
  used := s.gpr .a2
  rand := s.gpr .a3
  randLen := (s.gpr .a4).toNat
  scr := s.gpr .a5
  scrLen := (s.gpr .a6).toNat
  state := s.gpr .a7
  left := (s.mem.readW (s.gpr .a7) 64).toNat
  pLen := (s.mem.readW (s.gpr .a7 + 8) 64).toNat
  randB := Spec.Rsa.bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat
  tab := s.syms Impl.RsaKeyGen.TrialTable32.symbol

/-- The table of small primes the probable-prime tests read. -/
abbrev kT : List (String × List (BitVec 64)) := Impl.RsaKeyGen.TrialTable32.consts

namespace GP
variable (G : GP)

abbrev qLen : Nat := Spec.Dsa.generationQLen G.pLen
abbrev rOut : Region := ⟨G.out, G.outLen⟩
abbrev rUsed : Region := ⟨G.used, 8⟩
abbrev rRand : Region := ⟨G.rand, G.randLen⟩
abbrev rScr : Region := ⟨G.scr, G.scrLen * 8⟩
abbrev rState : Region := ⟨G.state, 32⟩
abbrev rTab : Region := ⟨G.tab, 8192⟩

end GP

/-- The stack below the stack pointer the functions we call use. -/
abbrev rBelow (σ : State) (STK : Nat) : Region := ⟨σ.sp - BitVec.ofNat 64 STK, STK⟩

/-- The contract's precondition, for `STK` bytes of stack. -/
structure CIn (STK : Nat) (s : State) : Prop where
  sp16 : s.sp.toNat % 16 = 0
  spLo : STK ≤ s.sp.toNat
  rd : s.rd = [(mkG s).rRand, (mkG s).rTab]
  wr : s.wr = [(mkG s).rOut, (mkG s).rUsed, (mkG s).rScr, (mkG s).rState]
  oU : (mkG s).rOut.Disjoint (mkG s).rUsed
  oR : (mkG s).rOut.Disjoint (mkG s).rRand
  oC : (mkG s).rOut.Disjoint (mkG s).rScr
  oT : (mkG s).rOut.Disjoint (mkG s).rState
  uR : (mkG s).rUsed.Disjoint (mkG s).rRand
  uC : (mkG s).rUsed.Disjoint (mkG s).rScr
  uT : (mkG s).rUsed.Disjoint (mkG s).rState
  rC : (mkG s).rRand.Disjoint (mkG s).rScr
  rT : (mkG s).rRand.Disjoint (mkG s).rState
  cT : (mkG s).rScr.Disjoint (mkG s).rState
  bO : (rBelow s STK).Disjoint (mkG s).rOut
  bU : (rBelow s STK).Disjoint (mkG s).rUsed
  bR : (rBelow s STK).Disjoint (mkG s).rRand
  bC : (rBelow s STK).Disjoint (mkG s).rScr
  bT : (rBelow s STK).Disjoint (mkG s).rState
  nO : (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64
  nU : (s.gpr .a2).toNat + 8 ≤ 2 ^ 64
  nR : (s.gpr .a3).toNat + (s.gpr .a4).toNat ≤ 2 ^ 64
  nC : (s.gpr .a5).toNat + (s.gpr .a6).toNat * 8 ≤ 2 ^ 64
  nT : (s.gpr .a7).toNat + 32 ≤ 2 ^ 64
  lens : Spec.Dsa.generationPLenValid (mkG s).pLen = true
  outLen : (mkG s).outLen = 2 * (mkG s).pLen + (mkG s).qLen
  scrLen : Spec.Dsa.generationScratchWords (mkG s).pLen ≤ (mkG s).scrLen
  left : (mkG s).left ≤ Spec.Dsa.parameterSeeds
  budget : s.mem.readW (s.gpr .a7 + 16) 64 = BitVec.ofNat 64 (Spec.Dsa.parameterEntropy (mkG s).pLen)
  randLen : (mkG s).randLen ≤ Spec.Dsa.parameterEntropy (mkG s).pLen
  alU : (s.gpr .a2).toNat % 8 = 0
  alC : (s.gpr .a5).toNat % 8 = 0
  alT : (s.gpr .a7).toNat % 8 = 0
  held : Abi.constsHeld s.mem (fun name => s.syms name) kT
  tFit : (mkG s).tab.toNat + 8192 ≤ 2 ^ 64
  tO : (mkG s).rTab.Disjoint (mkG s).rOut
  tU : (mkG s).rTab.Disjoint (mkG s).rUsed
  tC : (mkG s).rTab.Disjoint (mkG s).rScr
  tT : (mkG s).rTab.Disjoint (mkG s).rState
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
  sig_pre [Spec.Dsa.parameterSearchContract, Spec.Dsa.parameterSearchSig, abi, argRegs, List.append_eq] at h₀
  sig_pre [Spec.Dsa.parameterSearchContract, Spec.Dsa.parameterSearchSig, abi, argRegs, List.append_eq] at h₀
  obtain ⟨sp16, spLo, rd, wr, oU, oR, oC, oT, uR, uC, uT, rC, rT, cT, bO, bU, bR, bC, bT, nO, nU, nR, nC, nT,
    lens, outLen, scrLen, left, budget, randLen, alU, alC, alT⟩ := h₀
  obtain ⟨hd, held, ht, hal⟩ := hk
  have e : constRegs [(Impl.RsaKeyGen.TrialTable32.symbol, Impl.RsaKeyGen.TrialTable32.packed)] s = _ :=
    constRegs_kT s
  rw [e] at ht hd hal
  obtain ⟨tFit, tW, tR⟩ := ht _ (List.mem_cons_self (l := []))
  have hrd : s.rd = (stripConsts kT s).rd ++
      s.rd.drop (s.rd.length - [(Impl.RsaKeyGen.TrialTable32.symbol, Impl.RsaKeyGen.TrialTable32.packed)].length) :=
    (List.take_append_drop _ _).symm
  rw [hd] at hrd
  have e2 : (stripConsts kT s).rd = [(mkG s).rRand] := rd
  rw [e2] at hrd
  have hw : s.wr = [(mkG s).rOut, (mkG s).rUsed, (mkG s).rScr, (mkG s).rState] := wr
  exact ⟨sp16, spLo, hrd, hw, oU, oR, oC, oT, uR, uC, uT, rC, rT, cT, bO, bU, bR, bC, bT, nO, nU, nR, nC, nT,
    lens, outLen, scrLen, left, budget, randLen, alU, alC, alT, held, tFit,
    tW _ (by rw [hw]; simp), tW _ (by rw [hw]; simp), tW _ (by rw [hw]; simp), tW _ (by rw [hw]; simp),
    tR _ (by simp [abi, stackBelow]), hal _ (List.mem_cons_self (l := []))⟩

end VG.Proof.Dsa.RISCV64.PSearch
