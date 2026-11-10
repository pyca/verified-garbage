module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignVerified
public import VerifiedGarbage.Proof.Framework.X86.AppendSlice
public import VerifiedGarbage.Proof.Rsa.PreKey
import VerifiedGarbage.Proof.Rsa.PrivCheck
import VerifiedGarbage.Proof.Framework.Contract

/-! # `vg_rsa_pkcs1_sign_precomputed` on x86

`vg_rsa_pkcs1_sign`'s code, which ignores the key's precomputed values `pre`
(the specification lets an implementation ignore them), proven against
`vg_rsa_pkcs1_sign_precomputed`'s contract from its own (`verified_withSlice`).
-/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Sgn
open VG VG.X86
open VG.Proof.Rsa.X86.PrivChecked (CrtImpl privCode)

theorem wordVals_sign (s : State) : wordVals 21 s = [argVal s 32 0, argVal s 32 1, argVal s 32 2, argVal s 32 3, argVal s 32 4, argVal s 32 5, argVal s 32 6, argVal s 32 7, argVal s 32 8, argVal s 32 9, argVal s 32 10, argVal s 32 11, argVal s 32 12, argVal s 32 13, argVal s 32 14, argVal s 32 15, argVal s 32 16, argVal s 32 17, argVal s 32 18, argVal s 32 19, argVal s 32 20] := rfl

/-- `Spec.RsaPkcs1Sig.signSig.words 32`. -/
abbrev signWords : List ArgWord :=
  [.addr, .int 32, .addr, .int 32, .addr, .int 32, .int 32, .addr, .int 32, .addr, .int 32,
    .addr, .int 32, .addr, .int 32, .addr, .int 32, .addr, .int 32, .addr, .int 32]


/-! ## A state that meets the contract -/

open VG.Proof.Rsa.PreKey (keyIn keyMem key_pre_of)

/-- The arguments of `preState`: `out` at `0x1000`, the key (`keyMem`: `n`
at `0x2000`, `p` at `0x4200`, `q` at `0x4300`, `pre` at `0x4800`), `e` at
`0x3000`, `digest` at `0x4000`, `dp`, `dq` and `qinv` at `0x4400`, `0x4500`
and `0x4600`, `scratch` at `0xA000`. -/
def preArgs : List Nat := [0x1000, 64, 0x2000, 64, 0x3000, 1, 0, 0x4000, 64, 0x4200, 32, 0x4300, 32, 0x4400, 32, 0x4500, 32, 0x4600, 32, 0xa000, 0x420, 0x4800, 24]

/-- The memory of `preState`: the arguments on the stack from `0x20004`,
and the key. -/
def preMem (a : Addr) : Byte :=
  let i := a.toNat
  bif Nat.ble 0x20004 i && Nat.blt i 0x20060 then
    BitVec.ofNat 8 (preArgs.getD ((i - 0x20004) / 4) 0 / 256 ^ ((i - 0x20004) % 4))
  else bif keyIn i then keyMem a else 0

def preState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := preMem
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4000, 64⟩, ⟨0x4200, 32⟩, ⟨0x4300, 32⟩, ⟨0x4400, 32⟩,
    ⟨0x4500, 32⟩, ⟨0x4600, 32⟩, ⟨0x4800, 192⟩]
  wr := [⟨0x1000, 64⟩, ⟨0xA000, 8448⟩, ⟨0x20004, 92⟩]

theorem preState_key : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt preState.mem 0x2000 64)
    (Spec.Rsa.bytesAt preState.mem 0x4200 32) (Spec.Rsa.bytesAt preState.mem 0x4300 32) =
      some (Spec.Rsa.wordsAt preState.mem 0x4800 24) :=
  key_pre_of fun a ha => by
    have hs : (Nat.ble 0x20004 a.toNat && Nat.blt a.toNat 0x20060) = false := by
      simp only [keyIn, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at ha
      refine Bool.eq_false_iff.mpr fun h => ?_
      simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
      omega
    show (bif _ then _ else _) = _
    rw [hs, Bool.cond_false, ha, Bool.cond_true]

theorem satisfiablePre : ∃ s, (Spec.RsaPkcs1Sig.signPrecomputedContract abi sigStack).pre s := by
  have a2 : arg preState 2 = 0x2000 := by decide
  have a3 : arg preState 3 = 64 := by decide
  have a9 : arg preState 9 = 0x4200 := by decide
  have a10 : arg preState 10 = 32 := by decide
  have a11 : arg preState 11 = 0x4300 := by decide
  have a12 : arg preState 12 = 32 := by decide
  have a21 : arg preState 21 = 0x4800 := by decide
  have a22 : arg preState 22 = 24 := by decide
  have e : argAddr preState 0 = 0x20004 := by decide
  have esp : preState.gpr .esp = 0x20000 := rfl
  have p2 : BitVec.setWidth 64 (arg preState 2) = 0x2000 := by rw [a2]; decide
  have p9 : BitVec.setWidth 64 (arg preState 9) = 0x4200 := by rw [a9]; decide
  have p11 : BitVec.setWidth 64 (arg preState 11) = 0x4300 := by rw [a11]; decide
  have p21 : BitVec.setWidth 64 (arg preState 21) = 0x4800 := by rw [a21]; decide
  have l3 : (arg preState 3).toNat = 64 := by rw [a3]; decide
  have l10 : (arg preState 10).toNat = 32 := by rw [a10]; decide
  have l12 : (arg preState 12).toNat = 32 := by rw [a12]; decide
  have l22 : (arg preState 22).toNat = 24 := by rw [a22]; decide
  refine ⟨preState, ?_⟩
  sig_pre [Spec.RsaPkcs1Sig.signPrecomputedContract, Spec.RsaPkcs1Sig.signPrecomputedSig,
    Spec.RsaPkcs1Sig.signSig, abi, argSlots, argVal, argBytes, stackBelow, e, esp,
    sigStack, Spec.Rsa.lenValid, Spec.Rsa.scratchWords, Spec.Rsa.privatePrecomputedWords]
  sig_and_intros
  rotate_right
  · rw [p2, p9, p11, p21, l3, l10, l12, l22]; exact preState_key
  all_goals first
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (intro a h₁ h₂
       sig_simp_only [Region.Contains, preState] at h₁ h₂
       bv_omega)

theorem signPrecomputed_verified (v : CrtImpl) :
    Verified target (VG.Impl.RsaPkcs1Sig.X86.Sign.code (privName v) (privCode v))
      (Spec.RsaPkcs1Sig.signPrecomputedContract abi sigStack) := by
  refine verified_withSlice (sig := Spec.RsaPkcs1Sig.signSig) (nm := "pre") (e := .u64) (ln := "pre_len")
    (by decide) (by decide) (sign_verified v) ?_ ?_ ?_ satisfiablePre
  · intro s h
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, -, -⟩ := h
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  · intro s m' v hp hq
    exact hq
  · intro s₁ s₂ _ _ hpo h
    have e3 := hpo 3 (by decide)
    have e5 := hpo 5 (by decide)
    have hl : (Spec.RsaPkcs1Sig.signSig.words 32).length = 21 := by decide
    simp only [hl, sliceVals, wordVals_sign, List.cons_append, List.nil_append] at h e3 e5 ⊢
    change Curry.apply (α := Mem → List Nat) (signWords ++ [.addr, .int 32]) _ _ s₁.mem =
      Curry.apply (α := Mem → List Nat) (signWords ++ [.addr, .int 32]) _ _ s₂.mem at h
    change Curry.apply (α := Mem → List Nat) signWords _ _ s₁.mem =
      Curry.apply (α := Mem → List Nat) signWords _ _ s₂.mem
    change (argVal s₁ 32 3).setWidth 32 = (argVal s₂ 32 3).setWidth 32 at e3
    change (argVal s₁ 32 5).setWidth 32 = (argVal s₂ 32 5).setWidth 32 at e5
    dsimp only [signWords, List.cons_append, List.nil_append, Curry.apply, ArgWord.ofRaw] at h ⊢
    refine List.append_inj_left h ?_
    simp only [List.length_map, List.length_append, Proof.Rsa.bytesAt_length', e3, e5]

end VG.Proof.RsaPkcs1Sig.X86.Sgn
