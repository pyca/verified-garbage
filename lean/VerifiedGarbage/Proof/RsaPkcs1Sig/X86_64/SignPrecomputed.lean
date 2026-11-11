module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.SignPCT
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Rsa.PreKey
import VerifiedGarbage.Proof.Rsa.PrivCheck
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Bignum.X86_64.PubVerified

/-! # `vg_rsa_pkcs1_sign_precomputed` on x86-64

`Sign.codeP`, which calls `vg_rsa_private_checked_precomputed` with the
key's precomputed values `pre`, against `vg_rsa_pkcs1_sign_precomputed`'s
contract (`signPrecomputed_verified`): `sigContractP` implies it
(`signP_implies`), with a state that meets it (`satisfiablePre`), which holds
a real key (`Proof/Rsa/PreKey.lean`); and what its registration's scrub
needs of the contract (`signPrecomputed_postOut`).
-/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86_64.Sgn
open VG VG.X86_64
open VG.Proof.Rsa.X86_64 (CrtImpl)
open VG.Proof.Rsa.PreKey (keyIn keyMem key_pre_of)
open VG.Proof.Bignum.X86_64 (leak_eq)

/-! ## A state that meets the contract -/

/-- The stack arguments of `preState`; the key (`keyMem`) has `n` at
`0x2000`, `p` at `0x4200`, `q` at `0x4300` and `pre` at `0x4800`. -/
def preArgs : List Nat := [0, 0x4000, 1, 0x4200, 32, 0x4300, 32, 0x4400, 32, 0x4500, 32, 0x4600, 32, 0x20000, 0x420, 0x4800, 24]

/-- The memory of `preState`: the stack arguments from `0x10008`, and the
key. -/
def preMem (a : Addr) : Byte :=
  let i := a.toNat
  bif Nat.ble 0x10008 i && Nat.blt i 0x10090 then
    BitVec.ofNat 8 (preArgs.getD ((i - 0x10008) / 8) 0 / 256 ^ ((i - 0x10008) % 8))
  else bif keyIn i then keyMem a else 0

/-- `sigSatState` with the key and its precomputed values. -/
def preState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 64 | .rdx => 0x2000 | .rcx => 64 | .r8 => 0x3000 | .r9 => 1
    | .rsp => 0x10000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := preMem
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4000, 1⟩, ⟨0x4200, 32⟩, ⟨0x4300, 32⟩, ⟨0x4400, 32⟩, ⟨0x4500, 32⟩,
    ⟨0x4600, 32⟩, ⟨0x4800, 192⟩, ⟨0x10008, 136⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x20000, 8448⟩]

theorem preState_key : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt preState.mem 0x2000 64)
    (Spec.Rsa.bytesAt preState.mem 0x4200 32) (Spec.Rsa.bytesAt preState.mem 0x4300 32) =
      some (Spec.Rsa.wordsAt preState.mem 0x4800 24) :=
  key_pre_of fun a ha => by
    have hs : (Nat.ble 0x10008 a.toNat && Nat.blt a.toNat 0x10090) = false := by
      simp only [keyIn, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at ha
      refine Bool.eq_false_iff.mpr fun h => ?_
      simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
      omega
    show (bif _ then _ else _) = _
    rw [hs, Bool.cond_false, ha, Bool.cond_true]

theorem pre_args : stackArg preState 0 = 0 ∧ stackArg preState 1 = 0x4000 ∧ stackArg preState 2 = 1 ∧ stackArg preState 3 = 0x4200 ∧ stackArg preState 4 = 32 ∧ stackArg preState 5 = 0x4300 ∧ stackArg preState 6 = 32 ∧ stackArg preState 7 = 0x4400 ∧ stackArg preState 8 = 32 ∧ stackArg preState 9 = 0x4500 ∧ stackArg preState 10 = 32 ∧ stackArg preState 11 = 0x4600 ∧ stackArg preState 12 = 32 ∧ stackArg preState 13 = 0x20000 ∧ stackArg preState 14 = 0x420 ∧ stackArg preState 15 = 0x4800 ∧ stackArg preState 16 = 24 := by
  decide

theorem stackArgs_seventeen (s : State) :
    List.map (stackArg s) (List.range 17) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10, stackArg s 11, stackArg s 12, stackArg s 13, stackArg s 14, stackArg s 15, stackArg s 16] := rfl

theorem satisfiablePre : ∃ s, (Spec.RsaPkcs1Sig.signPrecomputedContract abi sigStack).pre s := by
  refine ⟨preState, ?_⟩
  sig_pre [Spec.RsaPkcs1Sig.signPrecomputedContract, Spec.RsaPkcs1Sig.signPrecomputedSig,
    Spec.RsaPkcs1Sig.signSig, abi, argRegs, stackArgs_seventeen, List.append_eq, sigStack]
  obtain ⟨-, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16⟩ := pre_args
  have ha : stackArgAddr preState 0 = 0x10008 := by decide
  simp only [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, ha]
  sig_and_intros
  rotate_right
  · rw [show BitVec.toNat (64 : BitVec 64) = 64 from rfl, show BitVec.toNat (32 : BitVec 64) = 32 from rfl,
      show BitVec.toNat (24 : BitVec 64) = 24 from rfl]
    exact preState_key
  all_goals first
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (simp only [Spec.Rsa.lenValid]; decide)

/-! ## The code -/

theorem signP_implies : sigContractP.Implies (Spec.RsaPkcs1Sig.signPrecomputedContract abi sigStack) where
  pre := fun _ h => h
  post := by
    sig_implies_post [Spec.RsaPkcs1Sig.signPrecomputedContract, Spec.RsaPkcs1Sig.signPrecomputedSig,
      Spec.RsaPkcs1Sig.signSig, abi, argRegs, sigContractP, sigContract, sigStack, stackArgs_seventeen,
      List.append_eq, List.range, List.range.loop]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.RsaPkcs1Sig.signPrecomputedContract, Spec.RsaPkcs1Sig.signPrecomputedSig,
      Spec.RsaPkcs1Sig.signSig, abi, argRegs, stackArgs_seventeen, List.append_eq, sigStack, List.range,
      List.range.loop] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13,
      a14, a15, a16⟩ := h
    obtain ⟨hne, hlk⟩ := List.append_inj hl (by
      simp only [List.length_map, List.length_append, Proof.Rsa.bytesAt_length', hcx, h9])
    obtain ⟨hn, he⟩ := leak_eq (by simp [Spec.Rsa.bytesAt, hcx]) hne
    refine ⟨⟨?_, a0, ?_, hn, he⟩, a15, a16, hlk⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
    · simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil, List.map_append,
        a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14]
  sat := satisfiablePre

/-- `vg_rsa_pkcs1_sign_precomputed`, calling
`vg_rsa_private_checked_precomputed` for the implementation `v` of the CRT,
meets its contract. -/
theorem signPrecomputed_verified (v : CrtImpl) :
    Verified target (Impl.RsaPkcs1Sig.X86_64.Sign.codeP (privNameP v) (privCodeP v))
      (Spec.RsaPkcs1Sig.signPrecomputedContract abi sigStack) :=
  Verified.of_correct (k := sigContractP) (codeP_correct' v) (codeP_constantTime v) signP_implies

/-! ## Without secret residue -/

/-- The postcondition reads the memory on return only in `out`. -/
theorem signPrecomputed_postOut (stack : Nat) :
    VG.X86_64.Scrub.PostOut (Spec.RsaPkcs1Sig.signPrecomputedContract abi stack)
      (Spec.RsaPkcs1Sig.signPrecomputedSig.retBits 64) :=
  VG.X86_64.Scrub.postOut_of_local_pre (leak := some _) VG.X86_64.Scrub.ScrubAbi.plain
    fun vs m m₁ m₂ r hlen hpre hb h => by
    obtain ⟨out, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 22) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨outLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨n, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨nLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨e, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨eLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨hash, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨digest, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨digestLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨p, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨pLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨q, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨qLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dp, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dpLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dq, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dqLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨qinv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨qinvLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨scratch, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨scratchLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨pre, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨preLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain rfl := List.eq_nil_of_length_eq_zero hlen
    simp only [Spec.RsaPkcs1Sig.signPrecomputedSig, Spec.RsaPkcs1Sig.signSig, Sig.bufs, List.cons_append,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
    have hol : outLen.toNat = nLen.toNat := hpre.2.1
    have hby : Spec.Rsa.bytesAt m₂ out nLen.toNat = Spec.Rsa.bytesAt m₁ out nLen.toNat :=
      VG.Proof.Rsa.X86_64.bytesAt_agree (by simp only [Elem.size]; omega)
        (by have := outLen.isLt; simp only [Elem.size]; omega) hb.1
    replace h : Spec.Rsa.writtenOutcome m₁ out nLen.toNat r _ := h
    show Spec.Rsa.writtenOutcome m₂ out nLen.toNat r _
    revert h
    generalize Spec.RsaPkcs1Sig.signId _ _ _ _ _ _ _ _ _ = o
    cases o <;> simp only [Spec.Rsa.writtenOutcome, hby] <;> exact id

end VG.Proof.RsaPkcs1Sig.X86_64.Sgn
