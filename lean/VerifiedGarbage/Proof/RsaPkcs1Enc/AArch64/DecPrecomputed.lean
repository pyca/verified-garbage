module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.Callees
public import VerifiedGarbage.Proof.Framework.AArch64.AppendSlice
public import VerifiedGarbage.Proof.Rsa.PreKey
import VerifiedGarbage.Proof.Rsa.PrivCheck
import VerifiedGarbage.Proof.Framework.Contract

/-! # `vg_rsa_pkcs1_decrypt_precomputed` on AArch64

`vg_rsa_pkcs1_decrypt`'s code, which ignores the key's precomputed values
`pre` (`Spec/Rsa/PrivatePrecompute.lean` lets an implementation ignore them),
proven against `vg_rsa_pkcs1_decrypt_precomputed`'s contract from its own
(`verified_withSlice`), with a state that meets it (`satisfiablePre`), which
holds a real key (`Proof/Rsa/PreKey.lean`).
-/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.AArch64
open VG VG.AArch64
open VG.Proof.Rsa.PreKey (keyIn keyMem key_pre_of)

theorem decWordVals_eq (s : State) : wordVals 23 s = [s.gpr .x0, s.gpr .x1, s.gpr .x2, s.gpr .x3, s.gpr .x4, s.gpr .x5, s.gpr .x6, s.gpr .x7, stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10, stackArg s 11, stackArg s 12, stackArg s 13, stackArg s 14] := rfl

/-- `Spec.RsaPkcs1Enc.decryptSig.words 64`. -/
abbrev decSigWords : List ArgWord :=
  [.addr, .int 64, .addr, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64]

/-! ## A state that meets the contract -/

/-- The stack arguments of `decPreState`; the key (`keyMem`) has `n` at
`0x2000`, `p` at `0x4200`, `q` at `0x4300` and `pre` at `0x4800`. -/
def decPreArgs : List Nat := [1, 0x4100, 64, 0x4200, 32, 0x4300, 32, 0x4400, 32, 0x4500, 32, 0x4600, 32, 0x20000, 0x420, 0x4800, 24]

/-- The memory of `decPreState`: the stack arguments from `0x10000`, and the
key. -/
def decPreMem (a : Addr) : Byte :=
  let i := a.toNat
  bif Nat.ble 0x10000 i && Nat.blt i 0x10088 then
    BitVec.ofNat 8 (decPreArgs.getD ((i - 0x10000) / 8) 0 / 256 ^ ((i - 0x10000) % 8))
  else bif keyIn i then keyMem a else 0

/-- `decSatState` with the key and its precomputed values. -/
def decPreState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 64 | .x2 => 0x1800 | .x3 => 0x2000 | .x4 => 64 | .x5 => 0x3000 | .x6 => 1
    | .x7 => 0x4000 | _ => 0
  sp := 0x10000
  mem := decPreMem
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4000, 1⟩, ⟨0x4100, 64⟩, ⟨0x4200, 32⟩, ⟨0x4300, 32⟩, ⟨0x4400, 32⟩,
    ⟨0x4500, 32⟩, ⟨0x4600, 32⟩, ⟨0x4800, 192⟩, ⟨0x10000, 136⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1800, 8⟩, ⟨0x20000, 8448⟩]

theorem decPreState_key : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt decPreState.mem 0x2000 64)
    (Spec.Rsa.bytesAt decPreState.mem 0x4200 32) (Spec.Rsa.bytesAt decPreState.mem 0x4300 32) =
      some (Spec.Rsa.wordsAt decPreState.mem 0x4800 24) :=
  key_pre_of fun a ha => by
    have hs : (Nat.ble 0x10000 a.toNat && Nat.blt a.toNat 0x10088) = false := by
      simp only [keyIn, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at ha
      refine Bool.eq_false_iff.mpr fun h => ?_
      simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
      omega
    show (bif _ then _ else _) = _
    rw [hs, Bool.cond_false, ha, Bool.cond_true]

theorem decPre_args : stackArg decPreState 0 = 1 ∧ stackArg decPreState 1 = 0x4100 ∧ stackArg decPreState 2 = 64 ∧ stackArg decPreState 3 = 0x4200 ∧ stackArg decPreState 4 = 32 ∧ stackArg decPreState 5 = 0x4300 ∧ stackArg decPreState 6 = 32 ∧ stackArg decPreState 7 = 0x4400 ∧ stackArg decPreState 8 = 32 ∧ stackArg decPreState 9 = 0x4500 ∧ stackArg decPreState 10 = 32 ∧ stackArg decPreState 11 = 0x4600 ∧ stackArg decPreState 12 = 32 ∧ stackArg decPreState 13 = 0x20000 ∧ stackArg decPreState 14 = 0x420 ∧ stackArg decPreState 15 = 0x4800 ∧ stackArg decPreState 16 = 24 := by
  decide

theorem stackArgs_seventeen (s : State) :
    List.map (stackArg s) (List.range 17) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10, stackArg s 11, stackArg s 12, stackArg s 13, stackArg s 14, stackArg s 15, stackArg s 16] := rfl

theorem decSatisfiablePre (c : Proof.Rsa.AArch64.CrtImpl) :
    ∃ s, (Spec.RsaPkcs1Enc.decryptPrecomputedContract AArch64.abi (Dec.decStack (privOf c))).pre s := by
  rw [show Dec.decStack (privOf c) = 3472 from rfl]
  refine ⟨decPreState, ?_⟩
  sig_pre [Spec.RsaPkcs1Enc.decryptPrecomputedContract, Spec.RsaPkcs1Enc.decryptPrecomputedSig,
    Spec.RsaPkcs1Enc.decryptSig, AArch64.abi, AArch64.argRegs, stackArgs_seventeen, List.append_eq]
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16⟩ := decPre_args
  have ha : stackArgAddr decPreState 0 = 0x10000 := by decide
  simp only [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, ha]
  sig_and_intros
  rotate_right
  · rw [show BitVec.toNat (64 : BitVec 64) = 64 from rfl, show BitVec.toNat (32 : BitVec 64) = 32 from rfl,
      show BitVec.toNat (24 : BitVec 64) = 24 from rfl]
    exact decPreState_key
  all_goals first
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (simp only [Spec.Rsa.lenValid]; decide)

/-! ## The code -/

theorem decryptPrecomputed_verified (v : Proof.Sha256.AArch64.Compress) (c : Proof.Rsa.AArch64.CrtImpl) :
    Verified AArch64.target (Impl.RsaPkcs1Enc.AArch64.Decrypt.code (Dec.HH v) (privOf c).name (privOf c).code)
      (Spec.RsaPkcs1Enc.decryptPrecomputedContract AArch64.abi (Dec.decStack (privOf c))) := by
  refine verified_withSlice (sig := Spec.RsaPkcs1Enc.decryptSig) (nm := "pre") (e := .u64) (ln := "pre_len")
    (by decide) (by decide) (Dec.dec_verified v (privOf c) (dec_sat c)) ?_ ?_ ?_ (decSatisfiablePre c)
  · intro s h
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, -, -⟩ := h
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
  · intro s m' v hp hq
    exact hq
  · intro s₁ s₂ _ _ hpo h
    have e4 := hpo 4 (by decide)
    have e6 := hpo 6 (by decide)
    have hl : (Spec.RsaPkcs1Enc.decryptSig.words 64).length = 23 := by decide
    simp only [hl, sliceVals, decWordVals_eq, List.cons_append, List.nil_append] at h e4 e6 ⊢
    change Curry.apply (α := Mem → List Nat) (decSigWords ++ [.addr, .int 64]) _ _ s₁.mem =
      Curry.apply (α := Mem → List Nat) (decSigWords ++ [.addr, .int 64]) _ _ s₂.mem at h
    change Curry.apply (α := Mem → List Nat) decSigWords _ _ s₁.mem =
      Curry.apply (α := Mem → List Nat) decSigWords _ _ s₂.mem
    change (s₁.gpr .x4).setWidth 64 = (s₂.gpr .x4).setWidth 64 at e4
    change (s₁.gpr .x6).setWidth 64 = (s₂.gpr .x6).setWidth 64 at e6
    dsimp only [decSigWords, List.cons_append, List.nil_append, Curry.apply, ArgWord.ofRaw] at h ⊢
    refine List.append_inj_left h ?_
    simp only [List.length_map, List.length_append, Proof.Rsa.bytesAt_length', e4, e6]

end VG.Proof.RsaPkcs1Enc.AArch64
