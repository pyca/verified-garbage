module

public import VerifiedGarbage.Impl.Dsa.PPC64LE.Generation
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Spec.Dsa.Generate
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32
import VerifiedGarbage.Proof.RsaKeyGen.TrialTable32
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract

/-! # DSA parameter generation on PPC64LE: the public parameters

`mkG s`: the public parameters of a call from `s`, the tapes' bytes among
them, which the contract makes public, and the address of the table of
small primes the probable-prime tests read (`kT`), which the contract's
calling convention adds to the readable regions. `CIn s`: the contract's
precondition (`cin_of_pre`), for the functions we call using at most `STK`
bytes below the stack pointer.
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
  pLen : Nat
  qLen : Nat
  seeds : Addr
  seedsLen : Nat
  hs : Addr
  hsLen : Nat
  wit : Addr
  witLen : Nat
  scr : Addr
  scrLen : Nat
  seedsB : List Byte
  hsB : List Byte
  witB : List Byte
  tab : Addr

def mkG (s : State) : GP where
  sp := s.sp
  out := s.gpr .r3
  outLen := (s.gpr .r4).toNat
  pLen := (s.gpr .r5).toNat
  qLen := (s.gpr .r6).toNat
  seeds := s.gpr .r7
  seedsLen := (s.gpr .r8).toNat
  hs := s.gpr .r9
  hsLen := (s.gpr .r10).toNat
  wit := stackArg s 0
  witLen := (stackArg s 1).toNat
  scr := stackArg s 2
  scrLen := (stackArg s 3).toNat
  seedsB := Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat
  hsB := Spec.Rsa.bytesAt s.mem (s.gpr .r9) (s.gpr .r10).toNat
  witB := Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat
  tab := s.syms Impl.RsaKeyGen.TrialTable32.symbol

/-- The table of small primes the probable-prime tests read. -/
abbrev kT : List (String × List (BitVec 64)) := Impl.RsaKeyGen.TrialTable32.consts

namespace GP
variable (G : GP)

abbrev rScr : Region := ⟨G.scr, G.scrLen * 8⟩
abbrev rOut : Region := ⟨G.out, G.outLen⟩
abbrev rSeeds : Region := ⟨G.seeds, G.seedsLen⟩
abbrev rHs : Region := ⟨G.hs, G.hsLen⟩
abbrev rWit : Region := ⟨G.wit, G.witLen⟩
abbrev rArgs : Region := ⟨G.sp + BitVec.ofNat 64 (32 + 8 * (8 + 0)), 32⟩
abbrev rTab : Region := ⟨G.tab, 8192⟩

end GP

/-- The stack below the stack pointer the functions we call use. -/
abbrev rBelow (σ : State) (STK : Nat) : Region := ⟨σ.sp - BitVec.ofNat 64 STK, STK⟩

theorem stackArgs_four (s : State) :
    List.map (stackArg s) (List.range 4) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3] := rfl

/-- The precondition under `abi`, for `STK` bytes of stack. -/
structure CIn0 (STK : Nat) (s : State) : Prop where
  spLo : STK ≤ s.sp.toNat
  spHi : s.sp.toNat + 32 + 96 ≤ 2 ^ 64
  rd : s.rd = [(mkG s).rSeeds, (mkG s).rHs, (mkG s).rWit, (mkG s).rArgs]
  wr : s.wr = [(mkG s).rOut, (mkG s).rScr]
  oS : (mkG s).rOut.Disjoint (mkG s).rSeeds
  oH : (mkG s).rOut.Disjoint (mkG s).rHs
  oW : (mkG s).rOut.Disjoint (mkG s).rWit
  oC : (mkG s).rOut.Disjoint (mkG s).rScr
  oA : (mkG s).rOut.Disjoint (mkG s).rArgs
  sC : (mkG s).rSeeds.Disjoint (mkG s).rScr
  hC : (mkG s).rHs.Disjoint (mkG s).rScr
  wC : (mkG s).rWit.Disjoint (mkG s).rScr
  cA : (mkG s).rScr.Disjoint (mkG s).rArgs
  bO : (rBelow s STK).Disjoint (mkG s).rOut
  bS : (rBelow s STK).Disjoint (mkG s).rSeeds
  bH : (rBelow s STK).Disjoint (mkG s).rHs
  bW : (rBelow s STK).Disjoint (mkG s).rWit
  bC : (rBelow s STK).Disjoint (mkG s).rScr
  bA : (rBelow s STK).Disjoint (mkG s).rArgs
  nO : (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64
  nS : (s.gpr .r7).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64
  nH : (s.gpr .r9).toNat + (s.gpr .r10).toNat ≤ 2 ^ 64
  nW : (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64
  nC : (stackArg s 2).toNat + (stackArg s 3).toNat * 8 ≤ 2 ^ 64
  lens : Spec.Dsa.generationLengthsValid (s.gpr .r5).toNat (s.gpr .r6).toNat
  outLen : (s.gpr .r4).toNat = 2 * (s.gpr .r5).toNat + (s.gpr .r6).toNat
  seedsMod : (s.gpr .r8).toNat % (s.gpr .r6).toNat = 0
  hsMod : (s.gpr .r10).toNat % (s.gpr .r5).toNat = 0
  scrLen : Spec.Dsa.generationScratchWords (s.gpr .r5).toNat ≤ (stackArg s 3).toNat

theorem cin0_of_pre {n : Nat} (s : State) (h : (Spec.Dsa.generateParametersContract abi (n + 1)).pre s) :
    CIn0 (n + 1) s := by
  sig_pre [Spec.Dsa.generateParametersContract, Spec.Dsa.generateParametersSig, abi, argRegs, stackArgs_four,
    List.append_eq] at h
  sig_pre [Spec.Dsa.generateParametersContract, Spec.Dsa.generateParametersSig, abi, argRegs, stackArgs_four,
    List.append_eq] at h
  obtain ⟨spLo, spHi, rd, wr, oS, oH, oW, oC, oA, sC, hC, wC, cA, bO, bS, bH, bW, bC, bA, nO, nS, nH, nW, nC,
    lens, outLen, seedsMod, hsMod, scrLen⟩ := h
  exact ⟨spLo, spHi, rd, wr, oS, oH, oW, oC, oA, sC, hC, wC, cA, bO, bS, bH, bW, bC, bA, nO, nS, nH, nW, nC,
    lens, outLen, seedsMod, hsMod, scrLen⟩

/-- The contract's precondition, for `STK` bytes of stack. -/
structure CIn (STK : Nat) (s : State) : Prop where
  spLo : STK ≤ s.sp.toNat
  spHi : s.sp.toNat + 32 + 96 ≤ 2 ^ 64
  rd : s.rd = [(mkG s).rSeeds, (mkG s).rHs, (mkG s).rWit, (mkG s).rArgs, (mkG s).rTab]
  wr : s.wr = [(mkG s).rOut, (mkG s).rScr]
  oS : (mkG s).rOut.Disjoint (mkG s).rSeeds
  oH : (mkG s).rOut.Disjoint (mkG s).rHs
  oW : (mkG s).rOut.Disjoint (mkG s).rWit
  oC : (mkG s).rOut.Disjoint (mkG s).rScr
  oA : (mkG s).rOut.Disjoint (mkG s).rArgs
  sC : (mkG s).rSeeds.Disjoint (mkG s).rScr
  hC : (mkG s).rHs.Disjoint (mkG s).rScr
  wC : (mkG s).rWit.Disjoint (mkG s).rScr
  cA : (mkG s).rScr.Disjoint (mkG s).rArgs
  bO : (rBelow s STK).Disjoint (mkG s).rOut
  bS : (rBelow s STK).Disjoint (mkG s).rSeeds
  bH : (rBelow s STK).Disjoint (mkG s).rHs
  bW : (rBelow s STK).Disjoint (mkG s).rWit
  bC : (rBelow s STK).Disjoint (mkG s).rScr
  bA : (rBelow s STK).Disjoint (mkG s).rArgs
  nO : (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64
  nS : (s.gpr .r7).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64
  nH : (s.gpr .r9).toNat + (s.gpr .r10).toNat ≤ 2 ^ 64
  nW : (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64
  nC : (stackArg s 2).toNat + (stackArg s 3).toNat * 8 ≤ 2 ^ 64
  lens : Spec.Dsa.generationLengthsValid (s.gpr .r5).toNat (s.gpr .r6).toNat
  outLen : (s.gpr .r4).toNat = 2 * (s.gpr .r5).toNat + (s.gpr .r6).toNat
  seedsMod : (s.gpr .r8).toNat % (s.gpr .r6).toNat = 0
  hsMod : (s.gpr .r10).toNat % (s.gpr .r5).toNat = 0
  scrLen : Spec.Dsa.generationScratchWords (s.gpr .r5).toNat ≤ (stackArg s 3).toNat
  held : Abi.constsHeld s.mem (fun name => s.syms name) kT
  tFit : (mkG s).tab.toNat + 8192 ≤ 2 ^ 64
  tO : (mkG s).rTab.Disjoint (mkG s).rOut
  tC : (mkG s).rTab.Disjoint (mkG s).rScr
  tB : (mkG s).rTab.Disjoint (rBelow s STK)

/-- The table's regions under `abi.withConsts kT`. -/
theorem constRegs_kT (s : State) : constRegs kT s = [(mkG s).rTab] := by
  simp only [constRegs, kT, Impl.RsaKeyGen.TrialTable32.consts, Abi.constRegions_cons, Abi.constRegions_nil,
    VG.Proof.RsaKeyGen.TrialTable32.packed_length]
  rfl

theorem cin_of_pre {n : Nat} (s : State)
    (h : (Spec.Dsa.generateParametersContract (abi.withConsts kT) (n + 1)).pre s) : CIn (n + 1) s := by
  obtain ⟨h₀, hk⟩ := (pre_consts (c₀ := (Impl.RsaKeyGen.TrialTable32.symbol, Impl.RsaKeyGen.TrialTable32.packed))
    (cs := []) (sig := Spec.Dsa.generateParametersSig)).mp h
  have c := cin0_of_pre (stripConsts kT s) h₀
  obtain ⟨hd, held, ht, -⟩ := hk
  have e : constRegs [(Impl.RsaKeyGen.TrialTable32.symbol, Impl.RsaKeyGen.TrialTable32.packed)] s = _ :=
    constRegs_kT s
  rw [e] at ht hd
  obtain ⟨tFit, tW, tR⟩ := ht _ (List.mem_cons_self (l := []))
  have hrd : s.rd = (stripConsts kT s).rd ++
      s.rd.drop (s.rd.length - [(Impl.RsaKeyGen.TrialTable32.symbol, Impl.RsaKeyGen.TrialTable32.packed)].length) :=
    (List.take_append_drop _ _).symm
  rw [hd, c.rd] at hrd
  have hw : s.wr = [(mkG s).rOut, (mkG s).rScr] := c.wr
  exact ⟨c.spLo, c.spHi, hrd, hw, c.oS, c.oH, c.oW, c.oC, c.oA, c.sC, c.hC, c.wC, c.cA, c.bO, c.bS, c.bH, c.bW,
    c.bC, c.bA, c.nO, c.nS, c.nH, c.nW, c.nC, c.lens, c.outLen, c.seedsMod, c.hsMod, c.scrLen, held, tFit,
    tW _ (by rw [hw]; simp), tW _ (by rw [hw]; simp), tR _ (by simp [abi, stackBelow])⟩

end VG.Proof.Dsa.PPC64LE.Gen
