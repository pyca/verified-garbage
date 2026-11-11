module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecCT5
public import VerifiedGarbage.Proof.Framework.X86_64.AppendSlice
public import VerifiedGarbage.Proof.Rsa.PreKey
import VerifiedGarbage.Proof.Rsa.PrivCheck
import VerifiedGarbage.Proof.Rsa.X86_64.PrivImpl
import VerifiedGarbage.Proof.Framework.Contract

/-! # `vg_rsa_pkcs1_decrypt_precomputed` on x86-64

`vg_rsa_pkcs1_decrypt`'s code, which ignores the key's precomputed values
`pre` (`Spec/Rsa/PrivatePrecompute.lean` lets an implementation ignore them),
proven against `vg_rsa_pkcs1_decrypt_precomputed`'s contract from its own
(`verified_withSlice`), with a state that meets it (`satisfiablePre`), which
holds a real key (`Proof/Rsa/PreKey.lean`); and what its registration's scrub
needs of the contract (`decryptPrecomputed_postOut`).
-/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86_64.Dec
open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Decrypt VG.Proof.RsaPkcs1Enc.X86_64
open VG.Proof.Sha256.X86_64 (Compress)
open VG.Proof.Rsa.PreKey (keyIn keyMem key_pre_of)

theorem wordVals_eq (s : State) : wordVals 23 s = [s.gpr .rdi, s.gpr .rsi, s.gpr .rdx, s.gpr .rcx, s.gpr .r8, s.gpr .r9, stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10, stackArg s 11, stackArg s 12, stackArg s 13, stackArg s 14, stackArg s 15, stackArg s 16] := rfl

/-- `Spec.RsaPkcs1Enc.decryptSig.words 64`. -/
abbrev sigWords : List ArgWord :=
  [.addr, .int 64, .addr, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64]

/-! ## A state that meets the contract -/

/-- The stack arguments of `preState`; the key (`keyMem`) has `n` at
`0x2000`, `p` at `0x4200`, `q` at `0x4300` and `pre` at `0x4800`. -/
def preArgs : List Nat := [1, 0x4000, 1, 0x4100, 64, 0x4200, 32, 0x4300, 32, 0x4400, 32, 0x4500, 32, 0x4600, 32, 0x20000, 0x420, 0x4800, 24]

/-- The memory of `preState`: the stack arguments from `0x10008`, and the
key. -/
def preMem (a : Addr) : Byte :=
  let i := a.toNat
  bif Nat.ble 0x10008 i && Nat.blt i 0x100a0 then
    BitVec.ofNat 8 (preArgs.getD ((i - 0x10008) / 8) 0 / 256 ^ ((i - 0x10008) % 8))
  else bif keyIn i then keyMem a else 0

/-- `decSatState` with the key and its precomputed values. -/
def preState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 64 | .rdx => 0x1800 | .rcx => 0x2000 | .r8 => 64 | .r9 => 0x3000
    | .rsp => 0x10000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := preMem
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4000, 1⟩, ⟨0x4100, 64⟩, ⟨0x4200, 32⟩, ⟨0x4300, 32⟩, ⟨0x4400, 32⟩,
    ⟨0x4500, 32⟩, ⟨0x4600, 32⟩, ⟨0x4800, 192⟩, ⟨0x10008, 152⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1800, 8⟩, ⟨0x20000, 8448⟩]

theorem preState_key : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt preState.mem 0x2000 64)
    (Spec.Rsa.bytesAt preState.mem 0x4200 32) (Spec.Rsa.bytesAt preState.mem 0x4300 32) =
      some (Spec.Rsa.wordsAt preState.mem 0x4800 24) :=
  key_pre_of fun a ha => by
    have hs : (Nat.ble 0x10008 a.toNat && Nat.blt a.toNat 0x100a0) = false := by
      simp only [keyIn, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at ha
      refine Bool.eq_false_iff.mpr fun h => ?_
      simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
      omega
    show (bif _ then _ else _) = _
    rw [hs, Bool.cond_false, ha, Bool.cond_true]

theorem pre_args : stackArg preState 0 = 1 ∧ stackArg preState 1 = 0x4000 ∧ stackArg preState 2 = 1 ∧ stackArg preState 3 = 0x4100 ∧ stackArg preState 4 = 64 ∧ stackArg preState 5 = 0x4200 ∧ stackArg preState 6 = 32 ∧ stackArg preState 7 = 0x4300 ∧ stackArg preState 8 = 32 ∧ stackArg preState 9 = 0x4400 ∧ stackArg preState 10 = 32 ∧ stackArg preState 11 = 0x4500 ∧ stackArg preState 12 = 32 ∧ stackArg preState 13 = 0x4600 ∧ stackArg preState 14 = 32 ∧ stackArg preState 15 = 0x20000 ∧ stackArg preState 16 = 0x420 ∧ stackArg preState 17 = 0x4800 ∧ stackArg preState 18 = 24 := by
  decide

theorem stackArgs_nineteen (s : State) :
    List.map (stackArg s) (List.range 19) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10, stackArg s 11, stackArg s 12, stackArg s 13, stackArg s 14, stackArg s 15, stackArg s 16, stackArg s 17, stackArg s 18] := rfl

theorem satisfiablePre : ∃ s, (Spec.RsaPkcs1Enc.decryptPrecomputedContract abi decStack).pre s := by
  refine ⟨preState, ?_⟩
  rw [show decStack = 3480 from rfl]
  sig_pre [Spec.RsaPkcs1Enc.decryptPrecomputedContract, Spec.RsaPkcs1Enc.decryptPrecomputedSig,
    Spec.RsaPkcs1Enc.decryptSig, abi, argRegs, stackArgs_nineteen, List.append_eq]
  obtain ⟨-, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18⟩ := pre_args
  have ha : stackArgAddr preState 0 = 0x10008 := by decide
  simp only [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, ha]
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

theorem decryptPrecomputed_verified (v : Compress) (pv : PrivImpl) :
    Verified target (code (HH v) pv.name pv.code) (Spec.RsaPkcs1Enc.decryptPrecomputedContract abi decStack) := by
  refine verified_withSlice (sig := Spec.RsaPkcs1Enc.decryptSig) (nm := "pre") (e := .u64) (ln := "pre_len")
    (by decide) (dec_verified v pv) ?_ ?_ ?_ satisfiablePre
  · intro s h
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, -, -⟩ := h
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
  · intro s m' v hp hq
    exact hq
  · intro s₁ s₂ _ _ hpo h
    have e4 := hpo 4 (by decide)
    have e6 := hpo 6 (by decide)
    have hl : (Spec.RsaPkcs1Enc.decryptSig.words 64).length = 23 := by decide
    simp only [hl, sliceVals, wordVals_eq, List.cons_append, List.nil_append] at h e4 e6 ⊢
    change Curry.apply (α := Mem → List Nat) (sigWords ++ [.addr, .int 64]) _ _ s₁.mem =
      Curry.apply (α := Mem → List Nat) (sigWords ++ [.addr, .int 64]) _ _ s₂.mem at h
    change Curry.apply (α := Mem → List Nat) sigWords _ _ s₁.mem =
      Curry.apply (α := Mem → List Nat) sigWords _ _ s₂.mem
    change (s₁.gpr .r8).setWidth 64 = (s₂.gpr .r8).setWidth 64 at e4
    change (stackArg s₁ 0).setWidth 64 = (stackArg s₂ 0).setWidth 64 at e6
    dsimp only [sigWords, List.cons_append, List.nil_append, Curry.apply, ArgWord.ofRaw] at h ⊢
    refine List.append_inj_left h ?_
    simp only [List.length_map, List.length_append, Proof.Rsa.bytesAt_length', e4, e6]

/-! ## Without secret residue -/

/-- The postcondition reads the memory on return only in `out` and
`msg_len`. -/
theorem decryptPrecomputed_postOut (stack : Nat) :
    VG.X86_64.Scrub.PostOut (Spec.RsaPkcs1Enc.decryptPrecomputedContract abi stack)
      (Spec.RsaPkcs1Enc.decryptPrecomputedSig.retBits 64) :=
  VG.X86_64.Scrub.postOut_of_local_pre (leak := some _) VG.X86_64.Scrub.ScrubAbi.plain
    fun vs m m₁ m₂ r hlen hpre hb h => by
    obtain ⟨out, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 24) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨outLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨msgLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨n, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨nLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨e, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨eLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨d, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨input, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨inputLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
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
    simp only [Spec.RsaPkcs1Enc.decryptPrecomputedSig, Spec.RsaPkcs1Enc.decryptSig, Sig.bufs, List.cons_append,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
    have hol : outLen.toNat = nLen.toNat := hpre.2.1
    have hby : Spec.Rsa.bytesAt m₂ out nLen.toNat = Spec.Rsa.bytesAt m₁ out nLen.toNat :=
      VG.Proof.Rsa.X86_64.bytesAt_agree (by simp only [Elem.size]; omega)
        (by have := outLen.isLt; simp only [Elem.size]; omega) hb.1
    have hw : Spec.Rsa.wordsAt m₂ msgLen 1 = Spec.Rsa.wordsAt m₁ msgLen 1 := by
      simp only [Spec.Rsa.wordsAt, List.range, List.range.loop, List.map_cons, List.map_nil, Nat.mul_zero,
        BitVec.add_zero]
      rw [VG.Proof.Rsa.X86_64.readW_agree (by decide) (by decide) hb.2.1]
    replace h : Spec.RsaPkcs1Enc.writtenMsg m₁ out msgLen nLen.toNat r _ := h
    show Spec.RsaPkcs1Enc.writtenMsg m₂ out msgLen nLen.toNat r _
    revert h
    generalize Spec.RsaPkcs1Enc.decrypt _ _ _ _ _ _ _ _ _ = o
    cases o <;> simp only [Spec.RsaPkcs1Enc.writtenMsg, hby, hw] <;> exact id

end VG.Proof.RsaPkcs1Enc.X86_64.Dec
