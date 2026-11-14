module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI
public import VerifiedGarbage.Proof.Rsa.Contract

/-! # Private CRT RSA resources supplied by the shared cdecl contract -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86
open VG.Proof.Dsa.X86 (argumentPointer)

structure CrtABI (s : State) : Prop where
  stackLow : 96 ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 76 ≤ 2 ^ 32
  rd : s.rd = [⟨argumentPointer s 2, (arg s 3).toNat⟩,
    ⟨argumentPointer s 4, (arg s 5).toNat⟩,
    ⟨argumentPointer s 6, (arg s 7).toNat⟩,
    ⟨argumentPointer s 8, (arg s 9).toNat⟩,
    ⟨argumentPointer s 10, (arg s 11).toNat⟩,
    ⟨argumentPointer s 12, (arg s 13).toNat⟩,
    ⟨argumentPointer s 14, (arg s 15).toNat⟩]
  wr : s.wr = [⟨argumentPointer s 0, (arg s 1).toNat⟩,
    ⟨argumentPointer s 16, (arg s 17).toNat * 8⟩, ⟨argAddr s 0, 72⟩]
  outScratch : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 16, (arg s 17).toNat * 8⟩
  retOut : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 0, (arg s 1).toNat⟩
  outBound : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  nScratch : (⟨argumentPointer s 2, (arg s 3).toNat⟩ : Region).Disjoint ⟨argumentPointer s 16, (arg s 17).toNat * 8⟩
  inScratch : (⟨argumentPointer s 4, (arg s 5).toNat⟩ : Region).Disjoint ⟨argumentPointer s 16, (arg s 17).toNat * 8⟩
  pScratch : (⟨argumentPointer s 6, (arg s 7).toNat⟩ : Region).Disjoint ⟨argumentPointer s 16, (arg s 17).toNat * 8⟩
  qScratch : (⟨argumentPointer s 8, (arg s 9).toNat⟩ : Region).Disjoint ⟨argumentPointer s 16, (arg s 17).toNat * 8⟩
  dpScratch : (⟨argumentPointer s 10, (arg s 11).toNat⟩ : Region).Disjoint ⟨argumentPointer s 16, (arg s 17).toNat * 8⟩
  dqScratch : (⟨argumentPointer s 12, (arg s 13).toNat⟩ : Region).Disjoint ⟨argumentPointer s 16, (arg s 17).toNat * 8⟩
  qiScratch : (⟨argumentPointer s 14, (arg s 15).toNat⟩ : Region).Disjoint ⟨argumentPointer s 16, (arg s 17).toNat * 8⟩
  scratchArgs : (⟨argumentPointer s 16, (arg s 17).toNat * 8⟩ : Region).Disjoint ⟨argAddr s 0, 72⟩
  retScratch : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 16, (arg s 17).toNat * 8⟩
  belowScratch : (⟨(s.gpr .esp).setWidth 64 - 96#64, 96⟩ : Region).Disjoint ⟨argumentPointer s 16, (arg s 17).toNat * 8⟩
  nBound : (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32
  inBound : (arg s 4).toNat + (arg s 5).toNat ≤ 2 ^ 32
  pBound : (arg s 6).toNat + (arg s 7).toNat ≤ 2 ^ 32
  qBound : (arg s 8).toNat + (arg s 9).toNat ≤ 2 ^ 32
  dpBound : (arg s 10).toNat + (arg s 11).toNat ≤ 2 ^ 32
  dqBound : (arg s 12).toNat + (arg s 13).toNat ≤ 2 ^ 32
  qiBound : (arg s 14).toNat + (arg s 15).toNat ≤ 2 ^ 32
  scratchBound : (arg s 16).toNat + (arg s 17).toNat * 8 ≤ 2 ^ 32
  lengths : Spec.Rsa.lenValid (arg s 3).toNat
  outLength : (arg s 1).toNat = (arg s 3).toNat
  inLength : (arg s 5).toNat = (arg s 3).toNat
  pPositive : 1 ≤ (arg s 7).toNat
  pLength : (arg s 7).toNat < (arg s 3).toNat
  qPositive : 1 ≤ (arg s 9).toNat
  qLength : (arg s 9).toNat < (arg s 3).toNat
  dpLength : (arg s 11).toNat = (arg s 7).toNat
  qiLength : (arg s 15).toNat = (arg s 7).toNat
  dqLength : (arg s 13).toNat = (arg s 9).toNat
  scratchLength : Spec.Rsa.scratchWords (arg s 3).toNat ≤ (arg s 17).toNat

theorem crtABI_of {s : State} (h : (Proof.Rsa.privateCrtContract abi 96).pre s) : CrtABI s := by
  sig_pre [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  constructor <;> with_reducible assumption

/-! ## `vg_rsa_private_crt_precomputed` -/

/-- `vg_rsa_private_crt`'s parameters, then the primes' cached values
`pre: *const u64, pre_len: usize`. -/
def privateCrtPrecomputedSig : Sig where
  params := Proof.Rsa.privateCrtSig.params ++ [("pre", .slice false .u64 "pre_len")]
  ret := some .u32

/-- `vg_rsa_private_crt`, given at `pre` the primes' `R² mod p` and `R² mod q`
(`Spec.Rsa.primeR2`, what follows the modulus's values in
`Spec.Rsa.privatePrecompute`), which hold only for `p q = n`. -/
def privateCrtPrecomputedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  privateCrtPrecomputedSig.contract A
    (pre := fun _out outLen n nLen _input inputLen p pLen q qLen _dp dpLen _dq dqLen _qinv
        qinvLen _scratch scratchLen pre preLen m =>
      Spec.Rsa.lenValid nLen.toNat ∧ outLen.toNat = nLen.toNat ∧ inputLen.toNat = nLen.toNat ∧
        1 ≤ pLen.toNat ∧ pLen.toNat < nLen.toNat ∧ 1 ≤ qLen.toNat ∧ qLen.toNat < nLen.toNat ∧
        dpLen.toNat = pLen.toNat ∧ qinvLen.toNat = pLen.toNat ∧ dqLen.toNat = qLen.toNat ∧
        Spec.Rsa.scratchWords nLen.toNat ≤ scratchLen.toNat ∧
        preLen.toNat = Spec.Rsa.primeWords pLen.toNat + Spec.Rsa.primeWords qLen.toNat ∧
        Spec.Rsa.wordsAt m pre preLen.toNat =
          Spec.Rsa.primeR2 (Spec.Rsa.bytesAt m p pLen.toNat) ++ Spec.Rsa.primeR2 (Spec.Rsa.bytesAt m q qLen.toNat) ∧
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt m p pLen.toNat) * Spec.Rsa.os2ip (Spec.Rsa.bytesAt m q qLen.toNat) =
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt m n nLen.toNat))
    (post := fun out _outLen n nLen input _inputLen p pLen q qLen dp _dpLen dq _dqLen qinv
        _qinvLen _scratch _scratchLen _pre _preLen m m' r =>
      Spec.Rsa.written m' out nLen.toNat r
        (Spec.Rsa.privateCrt (Spec.Rsa.bytesAt m n nLen.toNat) (Spec.Rsa.bytesAt m input nLen.toNat)
          (Spec.Rsa.bytesAt m p pLen.toNat) (Spec.Rsa.bytesAt m q qLen.toNat) (Spec.Rsa.bytesAt m dp pLen.toNat)
          (Spec.Rsa.bytesAt m dq qLen.toNat) (Spec.Rsa.bytesAt m qinv pLen.toNat)))
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen n nLen _input _inputLen _p _pLen _q _qLen _dp _dpLen _dq
        _dqLen _qinv _qinvLen _scratch _scratchLen _pre _preLen m =>
      (Spec.Rsa.bytesAt m n nLen.toNat).map (·.toNat))

/-- `privateCrtPrecomputedContract`'s resources and facts. -/
structure CrtABIP (s : State) : Prop where
  stackLow : 96 ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 4 + 80 ≤ 2 ^ 32
  rd : s.rd = [⟨argumentPointer s 2, (arg s 3).toNat⟩,
    ⟨argumentPointer s 4, (arg s 5).toNat⟩,
    ⟨argumentPointer s 6, (arg s 7).toNat⟩,
    ⟨argumentPointer s 8, (arg s 9).toNat⟩,
    ⟨argumentPointer s 10, (arg s 11).toNat⟩,
    ⟨argumentPointer s 12, (arg s 13).toNat⟩,
    ⟨argumentPointer s 14, (arg s 15).toNat⟩,
    ⟨argumentPointer s 18, (arg s 19).toNat * 8⟩]
  wr : s.wr = [⟨argumentPointer s 0, (arg s 1).toNat⟩,
    ⟨argumentPointer s 16, (arg s 17).toNat * 8⟩, ⟨argAddr s 0, 80⟩]
  outScratch : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 16, (arg s 17).toNat * 8⟩
  outPre : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 18, (arg s 19).toNat * 8⟩
  outArgs : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 80⟩
  retOut : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 0, (arg s 1).toNat⟩
  outBound : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  nScratch : (⟨argumentPointer s 2, (arg s 3).toNat⟩ : Region).Disjoint ⟨argumentPointer s 16, (arg s 17).toNat * 8⟩
  inScratch : (⟨argumentPointer s 4, (arg s 5).toNat⟩ : Region).Disjoint ⟨argumentPointer s 16, (arg s 17).toNat * 8⟩
  pScratch : (⟨argumentPointer s 6, (arg s 7).toNat⟩ : Region).Disjoint ⟨argumentPointer s 16, (arg s 17).toNat * 8⟩
  qScratch : (⟨argumentPointer s 8, (arg s 9).toNat⟩ : Region).Disjoint ⟨argumentPointer s 16, (arg s 17).toNat * 8⟩
  dpScratch : (⟨argumentPointer s 10, (arg s 11).toNat⟩ : Region).Disjoint ⟨argumentPointer s 16, (arg s 17).toNat * 8⟩
  dqScratch : (⟨argumentPointer s 12, (arg s 13).toNat⟩ : Region).Disjoint ⟨argumentPointer s 16, (arg s 17).toNat * 8⟩
  qiScratch : (⟨argumentPointer s 14, (arg s 15).toNat⟩ : Region).Disjoint ⟨argumentPointer s 16, (arg s 17).toNat * 8⟩
  scratchPre : (⟨argumentPointer s 16, (arg s 17).toNat * 8⟩ : Region).Disjoint ⟨argumentPointer s 18, (arg s 19).toNat * 8⟩
  scratchArgs : (⟨argumentPointer s 16, (arg s 17).toNat * 8⟩ : Region).Disjoint ⟨argAddr s 0, 80⟩
  preArgs : (⟨argumentPointer s 18, (arg s 19).toNat * 8⟩ : Region).Disjoint ⟨argAddr s 0, 80⟩
  retScratch : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 16, (arg s 17).toNat * 8⟩
  belowScratch : (⟨(s.gpr .esp).setWidth 64 - 96#64, 96⟩ : Region).Disjoint ⟨argumentPointer s 16, (arg s 17).toNat * 8⟩
  belowPre : (⟨(s.gpr .esp).setWidth 64 - 96#64, 96⟩ : Region).Disjoint ⟨argumentPointer s 18, (arg s 19).toNat * 8⟩
  nBound : (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32
  inBound : (arg s 4).toNat + (arg s 5).toNat ≤ 2 ^ 32
  pBound : (arg s 6).toNat + (arg s 7).toNat ≤ 2 ^ 32
  qBound : (arg s 8).toNat + (arg s 9).toNat ≤ 2 ^ 32
  dpBound : (arg s 10).toNat + (arg s 11).toNat ≤ 2 ^ 32
  dqBound : (arg s 12).toNat + (arg s 13).toNat ≤ 2 ^ 32
  qiBound : (arg s 14).toNat + (arg s 15).toNat ≤ 2 ^ 32
  scratchBound : (arg s 16).toNat + (arg s 17).toNat * 8 ≤ 2 ^ 32
  preBound : (arg s 18).toNat + (arg s 19).toNat * 8 ≤ 2 ^ 32
  lengths : Spec.Rsa.lenValid (arg s 3).toNat
  outLength : (arg s 1).toNat = (arg s 3).toNat
  inLength : (arg s 5).toNat = (arg s 3).toNat
  pPositive : 1 ≤ (arg s 7).toNat
  pLength : (arg s 7).toNat < (arg s 3).toNat
  qPositive : 1 ≤ (arg s 9).toNat
  qLength : (arg s 9).toNat < (arg s 3).toNat
  dpLength : (arg s 11).toNat = (arg s 7).toNat
  qiLength : (arg s 15).toNat = (arg s 7).toNat
  dqLength : (arg s 13).toNat = (arg s 9).toNat
  scratchLength : Spec.Rsa.scratchWords (arg s 3).toNat ≤ (arg s 17).toNat
  preLength : (arg s 19).toNat = Spec.Rsa.primeWords (arg s 7).toNat + Spec.Rsa.primeWords (arg s 9).toNat
  preValue : Spec.Rsa.wordsAt s.mem (argumentPointer s 18) (arg s 19).toNat =
    Spec.Rsa.primeR2 (Spec.Rsa.bytesAt s.mem (argumentPointer s 6) (arg s 7).toNat) ++
      Spec.Rsa.primeR2 (Spec.Rsa.bytesAt s.mem (argumentPointer s 8) (arg s 9).toNat)
  product : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (argumentPointer s 6) (arg s 7).toNat) *
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (argumentPointer s 8) (arg s 9).toNat) =
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat)

theorem crtABIP_of {s : State} (h : (privateCrtPrecomputedContract abi 96).pre s) : CrtABIP s := by
  sig_pre [privateCrtPrecomputedContract, privateCrtPrecomputedSig, Proof.Rsa.privateCrtSig, abi, argSlots, argVal,
    argBytes, stackBelow] at h
  sig_split h
  constructor <;> with_reducible assumption

end VG.Proof.Bignum.X86
