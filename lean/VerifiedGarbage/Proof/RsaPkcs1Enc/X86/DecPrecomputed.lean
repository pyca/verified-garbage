module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecVerified
public import VerifiedGarbage.Proof.Framework.X86.AppendSlice
public import VerifiedGarbage.Proof.Rsa.PreKey
import VerifiedGarbage.Proof.Rsa.PrivCheck
import VerifiedGarbage.Proof.Framework.Contract

/-! # `vg_rsa_pkcs1_decrypt_precomputed` on x86

`vg_rsa_pkcs1_decrypt`'s code, which ignores the key's precomputed values `pre`
(`Spec/Rsa/PrivatePrecompute.lean` lets an implementation ignore them),
proven against `vg_rsa_pkcs1_decrypt_precomputed`'s contract from its own
(`verified_withSlice`), with a state that meets it (`satisfiablePre`), which
holds a real key (`Proof/Rsa/PreKey.lean`).
-/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86
open VG.Proof.Sha256.X86.Variants (Backend)
open VG.Proof.Rsa.X86.PrivChecked (CrtImpl)
open VG.Proof.Rsa.PreKey (keyIn keyMem key_pre_of)

theorem wordVals_eq (s : State) : wordVals 23 s = [argVal s 32 0, argVal s 32 1, argVal s 32 2, argVal s 32 3, argVal s 32 4, argVal s 32 5, argVal s 32 6, argVal s 32 7, argVal s 32 8, argVal s 32 9, argVal s 32 10, argVal s 32 11, argVal s 32 12, argVal s 32 13, argVal s 32 14, argVal s 32 15, argVal s 32 16, argVal s 32 17, argVal s 32 18, argVal s 32 19, argVal s 32 20, argVal s 32 21, argVal s 32 22] := rfl

/-- `Spec.RsaPkcs1Enc.decryptSig.words 32`. -/
abbrev sigWords : List ArgWord :=
  [.addr, .int 32, .addr, .addr, .int 32, .addr, .int 32, .addr, .int 32, .addr, .int 32, .addr, .int 32, .addr, .int 32, .addr, .int 32, .addr, .int 32, .addr, .int 32, .addr, .int 32]

/-! ## A state that meets the contract -/

/-- The arguments of `preState`; the key (`keyMem`) has `n` at `0x2000`,
`p` at `0x4200`, `q` at `0x4300` and `pre` at `0x4800`. -/
def preArgs : List Nat := [0x1000, 64, 0x6800, 0x2000, 64, 0x2100, 1, 0x2200, 1, 0x3000, 64, 0x4200, 32, 0x4300, 32, 0x4400, 32, 0x4500, 32, 0x4600, 32, 0xa000, 0x420, 0x4800, 24]

/-- The memory of `preState`: the arguments on the stack from `0x20004`,
and the key. -/
def preMem (a : Addr) : Byte :=
  let i := a.toNat
  bif Nat.ble 0x20004 i && Nat.blt i 0x20068 then
    BitVec.ofNat 8 (preArgs.getD ((i - 0x20004) / 4) 0 / 256 ^ ((i - 0x20004) % 4))
  else bif keyIn i then keyMem a else 0

def preState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := preMem
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x2200, 1⟩, ⟨0x3000, 64⟩, ⟨0x4200, 32⟩, ⟨0x4300, 32⟩,
    ⟨0x4400, 32⟩, ⟨0x4500, 32⟩, ⟨0x4600, 32⟩, ⟨0x4800, 192⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x6800, 8⟩, ⟨0xA000, 8448⟩, ⟨0x20004, 100⟩]

theorem preState_key : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt preState.mem 0x2000 64)
    (Spec.Rsa.bytesAt preState.mem 0x4200 32) (Spec.Rsa.bytesAt preState.mem 0x4300 32) =
      some (Spec.Rsa.wordsAt preState.mem 0x4800 24) :=
  key_pre_of fun a ha => by
    have hs : (Nat.ble 0x20004 a.toNat && Nat.blt a.toNat 0x20068) = false := by
      simp only [keyIn, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at ha
      refine Bool.eq_false_iff.mpr fun h => ?_
      simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
      omega
    show (bif _ then _ else _) = _
    rw [hs, Bool.cond_false, ha, Bool.cond_true]

theorem satisfiablePre : ∃ s, (Spec.RsaPkcs1Enc.decryptPrecomputedContract abi stackBytes).pre s := by
  have a3 : arg preState 3 = 0x2000 := by decide
  have p3 : BitVec.setWidth 64 (arg preState 3) = 0x2000 := by rw [a3]; decide
  have a11 : arg preState 11 = 0x4200 := by decide
  have p11 : BitVec.setWidth 64 (arg preState 11) = 0x4200 := by rw [a11]; decide
  have a13 : arg preState 13 = 0x4300 := by decide
  have p13 : BitVec.setWidth 64 (arg preState 13) = 0x4300 := by rw [a13]; decide
  have a23 : arg preState 23 = 0x4800 := by decide
  have p23 : BitVec.setWidth 64 (arg preState 23) = 0x4800 := by rw [a23]; decide
  have a4 : arg preState 4 = 64 := by decide
  have l4 : (arg preState 4).toNat = 64 := by rw [a4]; decide
  have a12 : arg preState 12 = 32 := by decide
  have l12 : (arg preState 12).toNat = 32 := by rw [a12]; decide
  have a14 : arg preState 14 = 32 := by decide
  have l14 : (arg preState 14).toNat = 32 := by rw [a14]; decide
  have a24 : arg preState 24 = 24 := by decide
  have l24 : (arg preState 24).toNat = 24 := by rw [a24]; decide
  have e : argAddr preState 0 = 0x20004 := by decide
  have esp : preState.gpr .esp = 0x20000 := rfl
  refine ⟨preState, ?_⟩
  sig_pre [Spec.RsaPkcs1Enc.decryptPrecomputedContract, Spec.RsaPkcs1Enc.decryptPrecomputedSig,
    Spec.RsaPkcs1Enc.decryptSig, abi, argSlots, argVal, argBytes, stackBelow, e, esp,
    stackBytes, frameBytes, Spec.Rsa.lenValid, Spec.Rsa.scratchWords, Spec.Rsa.privatePrecomputedWords]
  sig_and_intros
  rotate_right
  · rw [p3, p11, p13, p23, l4, l12, l14, l24]; exact preState_key
  all_goals first
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (intro a h₁ h₂
       sig_simp_only [Region.Contains, preState] at h₁ h₂
       bv_omega)

/-! ## The code -/

theorem decryptPrecomputed_verified (v : Backend) (c : CrtImpl) :
    Verified target (decryptCode v c) (Spec.RsaPkcs1Enc.decryptPrecomputedContract abi stackBytes) := by
  refine verified_withSlice (sig := Spec.RsaPkcs1Enc.decryptSig) (nm := "pre") (e := .u64) (ln := "pre_len")
    (by decide) (by decide) (code_verified v c) ?_ ?_ ?_ satisfiablePre
  · intro s h
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, -, -⟩ := h
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
  · intro s m' v hp hq
    exact hq
  · intro s₁ s₂ _ _ hpo h
    have e4 := hpo 4 (by decide)
    have e6 := hpo 6 (by decide)
    have hl : (Spec.RsaPkcs1Enc.decryptSig.words 32).length = 23 := by decide
    simp only [hl, sliceVals, wordVals_eq, List.cons_append, List.nil_append] at h e4 e6 ⊢
    change Curry.apply (α := Mem → List Nat) (sigWords ++ [.addr, .int 32]) _ _ s₁.mem =
      Curry.apply (α := Mem → List Nat) (sigWords ++ [.addr, .int 32]) _ _ s₂.mem at h
    change Curry.apply (α := Mem → List Nat) sigWords _ _ s₁.mem =
      Curry.apply (α := Mem → List Nat) sigWords _ _ s₂.mem
    change (argVal s₁ 32 4).setWidth 32 = (argVal s₂ 32 4).setWidth 32 at e4
    change (argVal s₁ 32 6).setWidth 32 = (argVal s₂ 32 6).setWidth 32 at e6
    dsimp only [sigWords, List.cons_append, List.nil_append, Curry.apply, ArgWord.ofRaw] at h ⊢
    refine List.append_inj_left h ?_
    simp only [List.length_map, List.length_append, Proof.Rsa.bytesAt_length', e4, e6]

end VG.Proof.RsaPkcs1Enc.X86.Dec
