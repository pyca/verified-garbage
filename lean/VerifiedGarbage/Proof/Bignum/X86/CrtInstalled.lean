module

public import VerifiedGarbage.Proof.Bignum.X86.CrtInputs
public import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.Impl.Bignum.X86.CrtFn
public import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Proof.Dsa.X86.ABIResources
import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
public import VerifiedGarbage.Impl.Bignum.X86.CrtLayout
public import VerifiedGarbage.Proof.Dsa.X86.StackArgument
import VerifiedGarbage.Proof.Bignum.X86.CrtLayout
public import VerifiedGarbage.Proof.Mont.X86.OutsZ
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI
public import VerifiedGarbage.Proof.Rsa.Contract
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Bignum.X86.CrtSave
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Spec.Weierstrass

/-! ### `Bignum.X86.CrtEntry`, which this module and modules that import it used -/

section

/-! # Establishing the arithmetic workspace while preserving the caller ABI -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.X86.Wp VG.X86.Spill VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Bignum.X86

theorem entry_ok {s : State} {base : Addr} {size : Nat} {ptr : BitVec 32}
    (read : readSrc s (.mem (PublicFn.argument 16)) = some ptr)
    (hb : ptr.setWidth 64 = base) (hf : ptr.toNat + size ≤ 2 ^ 32) (hz : 48 ≤ size)
    (hw : (⟨base, size⟩ : Region) ∈ s.wr) (stk : StkOk (s.gpr .esp) base size) :
    WP isa (.block Crt.entry) s fun t =>
      Scr t base size ∧ Saved t.mem (off base) s.gpr Crt.savedRegisters ∧
      Keeps [.eax, .edi] s t ∧ Outside base 0 size s.mem t.mem := by
  unfold Crt.entry
  simp only [List.singleton_append]
  refine wp_movS read fun u U _ => ?_
  refine WP.block_append (WP.mono (entrySave_ok (base := base) (size := size) (by rw [U.gpr]; exact hb)
    (by rw [U.gpr]; exact hf) hz (by rw [U.wr]; exact hw)) fun v ⟨G, Rd, Wr, S, F⟩ => ?_)
  refine wp_movS rfl fun t T _ => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [T.gpr, G, U.gpr]; exact hb
    · rw [T.wr, Wr, U.wr]; exact hw
    · rw [← hb, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans ptr.isLt (by decide))]
      exact hf
    · rw [T.other _ (by decide), G, U.other _ (by decide)]
      exact stk
  · intro p hp
    rw [T.mem, S p hp]
    have H : p.1 ≠ .eax := by
      simp only [Crt.savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> decide
    exact U.other _ H
  · refine ⟨?_, ?_, ?_⟩
    · intro reg hr
      rw [T.other reg (by intro H; subst reg; exact hr (by simp)), G]
      exact U.other reg (by intro H; subst reg; exact hr (by simp))
    · rw [T.rd, Rd, U.rd]
    · rw [T.wr, Wr, U.wr]
  · intro a ha
    rw [T.mem]
    have H : ¬ InRegions [⟨base, size⟩] a 1 := by
      simp only [InRegions, List.mem_singleton, exists_eq_left, Region.Contains]
      change ¬ (ofs base a + 1 ≤ size)
      omega_using [ha]
    exact (F a (by intro reg hreg hcontains; exact H ⟨reg, hreg, hcontains⟩)).trans (congrFun U.mem a)

end VG.Proof.Bignum.X86.Crt

end

end

/-! ### `Bignum.X86.CrtResources`, which this module and modules that import it used -/

section

/-! ### `Bignum.X86.CrtABI`, which this module and modules that import it used -/

section

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

end

end

/-! # Caller resources for the public RSA workspace -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86

theorem CrtABI.space {s : State} (A : CrtABI s) :
    VG.Impl.Bignum.X86.Crt.size (Spec.Rsa.modulusWords (arg s 3).toNat) ≤
      (arg s 17).toNat * 8 := by
  have H := Crt.shared_scratch A.lengths.1
  have := A.scratchLength
  omega_using [H, this]

theorem CrtABI.used {s : State} (A : CrtABI s) : 224 ≤ (arg s 17).toNat * 8 := by
  have H := A.space
  rw [Crt.size_eq] at H
  omega_using [H]

theorem CrtABI.stackArgument {s : State} (A : CrtABI s) {i : Nat} (hi : i < 18) :
    StackArgument s (argumentPointer s 16) ((arg s 17).toNat * 8) i := by
  apply stackArgument_of (count := 18) (by have := A.stackBound; omega_using [this]) hi
  · rw [A.rd, A.wr]; simp
  · exact A.scratchArgs.symm

theorem CrtABI.stack {s : State} (A : CrtABI s) :
    StkOk (s.gpr .esp) (argumentPointer s 16) ((arg s 17).toNat * 8) := by
  apply VG.Proof.Weierstrass.X86.stkOk_of (by decide : 20 ≤ 96) A.stackLow
  · have H := A.scratchBound
    simpa only [argumentPointer, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans (arg s 16).isLt (by decide : 2 ^ 32 < 2 ^ 64))] using H
  · have H : 224 ≤ (arg s 17).toNat * 8 := A.used; omega_using [H]
  · exact A.belowScratch

theorem CrtABI.room {s : State} (A : CrtABI s) :
    CallRoom (s.gpr .esp) (argumentPointer s 16) ((arg s 17).toNat * 8) := by
  refine ⟨A.stackLow, ?_⟩
  simp only [below]
  rw [VG.X86.Taint.sub_setWidth A.stackLow]
  exact A.belowScratch

end VG.Proof.Bignum.X86

end

end

/-! # Install all caller resources for the private CRT operation -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86 VG.Impl.Bignum.X86

/-- What installing the working space needs of the caller's resources: `CrtABI`'s, or those
of a contract with more arguments. -/
structure CrtRes (s : State) : Prop where
  args : ∀ i, i < 18 → StackArgument s (argumentPointer s 16) ((arg s 17).toNat * 8) i
  scratchBound : (arg s 16).toNat + (arg s 17).toNat * 8 ≤ 2 ^ 32
  used : 224 ≤ (arg s 17).toNat * 8
  scratchW : (⟨argumentPointer s 16, (arg s 17).toNat * 8⟩ : Region) ∈ s.wr
  stack : StkOk (s.gpr .esp) (argumentPointer s 16) ((arg s 17).toNat * 8)
  lengths : Spec.Rsa.lenValid (arg s 3).toNat
  space : VG.Impl.Bignum.X86.Crt.size (Spec.Rsa.modulusWords (arg s 3).toNat) ≤ (arg s 17).toNat * 8
  pLength : (arg s 7).toNat < (arg s 3).toNat
  qLength : (arg s 9).toNat < (arg s 3).toNat
  room : CallRoom (s.gpr .esp) (argumentPointer s 16) ((arg s 17).toNat * 8)
  stackBound : (s.gpr .esp).toNat + 76 ≤ 2 ^ 32
  outLength : (arg s 1).toNat = (arg s 3).toNat
  inLength : (arg s 5).toNat = (arg s 3).toNat
  pPositive : 1 ≤ (arg s 7).toNat
  qPositive : 1 ≤ (arg s 9).toNat
  dpLength : (arg s 11).toNat = (arg s 7).toNat
  qiLength : (arg s 15).toNat = (arg s 7).toNat
  dqLength : (arg s 13).toNat = (arg s 9).toNat
  outBound : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  outW : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region) ∈ s.wr
  outScratch : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 16, (arg s 17).toNat * 8⟩
  compR : ∀ i ∈ componentArguments, (⟨argumentPointer s i, (arg s (i + 1)).toNat⟩ : Region) ∈ s.rd ++ s.wr
  nBound : (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32
  inBound : (arg s 4).toNat + (arg s 5).toNat ≤ 2 ^ 32
  pBound : (arg s 6).toNat + (arg s 7).toNat ≤ 2 ^ 32
  qBound : (arg s 8).toNat + (arg s 9).toNat ≤ 2 ^ 32
  dpBound : (arg s 10).toNat + (arg s 11).toNat ≤ 2 ^ 32
  dqBound : (arg s 12).toNat + (arg s 13).toNat ≤ 2 ^ 32
  qiBound : (arg s 14).toNat + (arg s 15).toNat ≤ 2 ^ 32
  nScratch : (⟨argumentPointer s 2, (arg s 3).toNat⟩ : Region).Disjoint ⟨argumentPointer s 16, (arg s 17).toNat * 8⟩
  inScratch : (⟨argumentPointer s 4, (arg s 5).toNat⟩ : Region).Disjoint ⟨argumentPointer s 16, (arg s 17).toNat * 8⟩
  pScratch : (⟨argumentPointer s 6, (arg s 7).toNat⟩ : Region).Disjoint ⟨argumentPointer s 16, (arg s 17).toNat * 8⟩
  qScratch : (⟨argumentPointer s 8, (arg s 9).toNat⟩ : Region).Disjoint ⟨argumentPointer s 16, (arg s 17).toNat * 8⟩
  dpScratch : (⟨argumentPointer s 10, (arg s 11).toNat⟩ : Region).Disjoint ⟨argumentPointer s 16, (arg s 17).toNat * 8⟩
  dqScratch : (⟨argumentPointer s 12, (arg s 13).toNat⟩ : Region).Disjoint ⟨argumentPointer s 16, (arg s 17).toNat * 8⟩
  qiScratch : (⟨argumentPointer s 14, (arg s 15).toNat⟩ : Region).Disjoint ⟨argumentPointer s 16, (arg s 17).toNat * 8⟩

theorem _root_.VG.Proof.Bignum.X86.CrtABI.res {s : State} (A : CrtABI s) : CrtRes s where
  args _ hi := A.stackArgument hi
  scratchBound := A.scratchBound
  used := A.used
  scratchW := by rw [A.wr]; simp
  stack := A.stack
  lengths := A.lengths
  space := A.space
  pLength := A.pLength
  qLength := A.qLength
  room := A.room
  stackBound := A.stackBound
  outLength := A.outLength
  inLength := A.inLength
  pPositive := A.pPositive
  qPositive := A.qPositive
  dpLength := A.dpLength
  qiLength := A.qiLength
  dqLength := A.dqLength
  outBound := A.outBound
  outW := by rw [A.wr]; simp
  outScratch := A.outScratch
  compR i hi := by
    rw [A.rd, A.wr]
    simp only [componentArguments, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  nBound := A.nBound
  inBound := A.inBound
  pBound := A.pBound
  qBound := A.qBound
  dpBound := A.dpBound
  dqBound := A.dqBound
  qiBound := A.qiBound
  nScratch := A.nScratch
  inScratch := A.inScratch
  pScratch := A.pScratch
  qScratch := A.qScratch
  dpScratch := A.dpScratch
  dqScratch := A.dqScratch
  qiScratch := A.qiScratch

theorem installedG_ok {s : State} (A : CrtRes s) :
    WP isa (.block Crt.entry) s fun t =>
      Inputs (argumentPointer s 16) ((arg s 17).toNat * 8) (arg s 3).toNat (arg s) t ∧
      Spill.Saved t.mem (off (argumentPointer s 16)) s.gpr Crt.savedRegisters ∧
      Keeps [.eax, .edi] s t ∧
      Outside (argumentPointer s 16) 0 ((arg s 17).toNat * 8) s.mem t.mem := by
  refine WP.mono (entry_ok (ptr := arg s 16)
    (A.args 16 (by decide)).readSrc rfl A.scratchBound
    (by have := A.used; omega_using [this]) A.scratchW A.stack) ?_
  intro t ⟨Sc, Saved, K, O⟩
  refine ⟨?_, Saved, K, O⟩
  refine ⟨Sc, A.lengths.1, A.lengths.2, A.space, ?_, ?_, ?_, ?_, A.pLength, A.qLength,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    by rw [K.1 _ (by decide)]; exact A.room, by rw [K.1 _ (by decide)]; exact A.stackBound⟩
  · intro i hi
    exact (CallArgument.mk (A.args i hi) rfl).keep K (by decide) O
  · simp only [← A.outLength, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp only [← A.inLength, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · exact BitVec.eq_of_toNat_eq A.dpLength
  · exact BitVec.eq_of_toNat_eq A.dqLength
  · exact BitVec.eq_of_toNat_eq A.qiLength
  · rw [← A.outLength]; exact A.outBound
  · rw [K.2.2]
    exact ⟨_, A.outW, by rw [← A.outLength]; exact Region.contains_self _ _⟩
  · rw [← A.outLength]; exact A.outScratch.symm
  · intro i hi
    have := A.lengths.1
    have := A.inLength
    have := A.pPositive
    have := A.qPositive
    have := A.dpLength
    have := A.dqLength
    have := A.qiLength
    simp only [componentArguments, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Nat.reduceAdd] <;> omega_arith
  · intro i hi
    have := A.inLength
    have := A.pLength
    have := A.qLength
    have := A.dpLength
    have := A.dqLength
    have := A.qiLength
    simp only [componentArguments, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Nat.reduceAdd] <;> omega_arith
  · intro i hi
    simp only [componentArguments, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact A.nBound
    · exact A.inBound
    · exact A.pBound
    · exact A.qBound
    · exact A.dpBound
    · exact A.dqBound
    · exact A.qiBound
  · intro i hi
    rw [K.2.1, K.2.2]
    exact ⟨_, A.compR i hi, Region.contains_self _ _⟩
  · intro i hi
    simp only [componentArguments, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact A.nScratch
    · exact A.inScratch
    · exact A.pScratch
    · exact A.qScratch
    · exact A.dpScratch
    · exact A.dqScratch
    · exact A.qiScratch


theorem installed_ok {s : State} (A : CrtABI s) :
    WP isa (.block Crt.entry) s fun t =>
      Inputs (argumentPointer s 16) ((arg s 17).toNat * 8) (arg s 3).toNat (arg s) t ∧
      Spill.Saved t.mem (off (argumentPointer s 16)) s.gpr Crt.savedRegisters ∧
      Keeps [.eax, .edi] s t ∧
      Outside (argumentPointer s 16) 0 ((arg s 17).toNat * 8) s.mem t.mem :=
  installedG_ok A.res

theorem _root_.VG.Proof.Bignum.X86.CrtABIP.res {s : State} (A : CrtABIP s) : CrtRes s := by
  have space : VG.Impl.Bignum.X86.Crt.size (Spec.Rsa.modulusWords (arg s 3).toNat) ≤ (arg s 17).toNat * 8 := by
    have H := Crt.shared_scratch A.lengths.1
    have := A.scratchLength
    omega_using [H, this]
  have used : 224 ≤ (arg s 17).toNat * 8 := by
    have H := space
    rw [Crt.size_eq] at H
    omega_using [H]
  exact {
  args := fun i hi => stackArgument_of (count := 20) (by have := A.stackBound; omega_using [this]) (by omega_using [hi])
    (by rw [A.rd, A.wr]; simp) A.scratchArgs.symm
  scratchBound := A.scratchBound
  used := used
  scratchW := by rw [A.wr]; simp
  stack := by
    apply VG.Proof.Weierstrass.X86.stkOk_of (by decide : 20 ≤ 96) A.stackLow
    · have H := A.scratchBound
      simpa only [argumentPointer, BitVec.toNat_setWidth,
        Nat.mod_eq_of_lt (Nat.lt_trans (arg s 16).isLt (by decide : 2 ^ 32 < 2 ^ 64))] using H
    · omega_using [used]
    · exact A.belowScratch
  lengths := A.lengths
  space := space
  pLength := A.pLength
  qLength := A.qLength
  room := by
    refine ⟨A.stackLow, ?_⟩
    simp only [below]
    rw [VG.X86.Taint.sub_setWidth A.stackLow]
    exact A.belowScratch
  stackBound := by have := A.stackBound; omega_using [this]
  outLength := A.outLength
  inLength := A.inLength
  pPositive := A.pPositive
  qPositive := A.qPositive
  dpLength := A.dpLength
  qiLength := A.qiLength
  dqLength := A.dqLength
  outBound := A.outBound
  outW := by rw [A.wr]; simp
  outScratch := A.outScratch
  compR := fun i hi => by
    rw [A.rd, A.wr]
    simp only [componentArguments, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  nBound := A.nBound
  inBound := A.inBound
  pBound := A.pBound
  qBound := A.qBound
  dpBound := A.dpBound
  dqBound := A.dqBound
  qiBound := A.qiBound
  nScratch := A.nScratch
  inScratch := A.inScratch
  pScratch := A.pScratch
  qScratch := A.qScratch
  dpScratch := A.dpScratch
  dqScratch := A.dqScratch
  qiScratch := A.qiScratch }

end VG.Proof.Bignum.X86.Crt
