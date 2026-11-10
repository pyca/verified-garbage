module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.SgVerified
public import VerifiedGarbage.Proof.Framework.Arm.AppendSlice
public import VerifiedGarbage.Proof.Rsa.PreKey
import VerifiedGarbage.Proof.Rsa.PrivCheck
import VerifiedGarbage.Proof.Framework.Contract

/-! # `vg_rsa_pkcs1_sign_precomputed` on ARMv7

`vg_rsa_pkcs1_sign`'s code, which ignores the key's precomputed values `pre`
(`Spec/Rsa/PrivatePrecompute.lean` lets an implementation ignore them),
proven against `vg_rsa_pkcs1_sign_precomputed`'s contract from its own
(`verified_withSlice`), with a state that meets it (`satisfiablePre`), which
holds a real key (`Proof/Rsa/PreKey.lean`).
-/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.Arm.Sg
open VG VG.Arm
open VG.Proof.Rsa.PreKey (keyIn keyMem key_pre_of)

theorem wordVals_eq (s : State) : wordVals 21 s = [Loc.val s (locAt 0), Loc.val s (locAt 1), Loc.val s (locAt 2), Loc.val s (locAt 3), Loc.val s (locAt 4), Loc.val s (locAt 5), Loc.val s (locAt 6), Loc.val s (locAt 7), Loc.val s (locAt 8), Loc.val s (locAt 9), Loc.val s (locAt 10), Loc.val s (locAt 11), Loc.val s (locAt 12), Loc.val s (locAt 13), Loc.val s (locAt 14), Loc.val s (locAt 15), Loc.val s (locAt 16), Loc.val s (locAt 17), Loc.val s (locAt 18), Loc.val s (locAt 19), Loc.val s (locAt 20)] := rfl

/-- `Spec.RsaPkcs1Sig.signSig.words 32`. -/
abbrev sigWords : List ArgWord :=
  [.addr, .int 32, .addr, .int 32, .addr, .int 32, .int 32, .addr, .int 32, .addr, .int 32, .addr, .int 32, .addr, .int 32, .addr, .int 32, .addr, .int 32, .addr, .int 32]

/-! ## A state that meets the contract -/

/-- The stack arguments of `preState`; the key (`keyMem`) has `n` at
`0x2000`, `p` at `0x4200`, `q` at `0x4300` and `pre` at `0x4800`. -/
def preArgs : List Nat := [0x2100, 1, 0, 0x3000, 0, 0x4200, 32, 0x4300, 32, 0x4400, 32, 0x4500, 32, 0x4600, 32, 0xa000, 0x420, 0x4800, 24]

/-- The memory of `preState`: the stack arguments from `0x8000`, and the
key. -/
def preMem (a : Addr) : Byte :=
  let i := a.toNat
  bif Nat.ble 0x8000 i && Nat.blt i 0x804c then
    BitVec.ofNat 8 (preArgs.getD ((i - 0x8000) / 4) 0 / 256 ^ ((i - 0x8000) % 4))
  else bif keyIn i then keyMem a else 0

def preState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 64 | .r2 => 0x2000 | .r3 => 64 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem := preMem
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x3000, 0⟩, ⟨0x4200, 32⟩, ⟨0x4300, 32⟩, ⟨0x4400, 32⟩, ⟨0x4500, 32⟩,
    ⟨0x4600, 32⟩, ⟨0x4800, 192⟩, ⟨0x8000, 76⟩]
  wr := [⟨0x1000, 64⟩, ⟨0xA000, 8448⟩]

theorem preState_key : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt preState.mem 0x2000 64)
    (Spec.Rsa.bytesAt preState.mem 0x4200 32) (Spec.Rsa.bytesAt preState.mem 0x4300 32) =
      some (Spec.Rsa.wordsAt preState.mem 0x4800 24) :=
  key_pre_of fun a ha => by
    have hs : (Nat.ble 0x8000 a.toNat && Nat.blt a.toNat 0x804c) = false := by
      simp only [keyIn, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at ha
      refine Bool.eq_false_iff.mpr fun h => ?_
      simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
      omega
    show (bif _ then _ else _) = _
    rw [hs, Bool.cond_false, ha, Bool.cond_true]

theorem satisfiablePre : ∃ s, (Spec.RsaPkcs1Sig.signPrecomputedContract abi stackBytes).pre s := by
  have p5 : BitVec.setWidth 64 (stackArg preState 5) = 0x4200 := by decide
  have p7 : BitVec.setWidth 64 (stackArg preState 7) = 0x4300 := by decide
  have p17 : BitVec.setWidth 64 (stackArg preState 17) = 0x4800 := by decide
  have l6 : (stackArg preState 6).toNat = 32 := by decide
  have l8 : (stackArg preState 8).toNat = 32 := by decide
  have l18 : (stackArg preState 18).toNat = 24 := by decide
  refine ⟨preState, ?_⟩
  sig_pre [Spec.RsaPkcs1Sig.signPrecomputedContract, Spec.RsaPkcs1Sig.signPrecomputedSig,
    Spec.RsaPkcs1Sig.signSig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  sig_and_intros
  rotate_right
  · rw [p5, p7, p17, l6, l8, l18, show BitVec.setWidth 64 (8192 : BitVec 32) = (0x2000 : Addr) by decide,
      show BitVec.toNat (64 : BitVec 32) = 64 by decide]
    exact preState_key
  all_goals first
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (simp only [Spec.Rsa.lenValid]; decide)

/-! ## The code -/

theorem signPrecomputed_verified (v : Proof.Rsa.Arm.CrtImpl) :
    Verified target (signCode v) (Spec.RsaPkcs1Sig.signPrecomputedContract abi stackBytes) := by
  refine verified_withSlice (sig := Spec.RsaPkcs1Sig.signSig) (nm := "pre") (e := .u64) (ln := "pre_len")
    (by decide) (by decide) (code_verified v) ?_ ?_ ?_ satisfiablePre
  · intro s h
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, -, -⟩ := h
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  · intro s m' v hp hq
    exact hq
  · intro s₁ s₂ _ _ hpo h
    have e3 := hpo 3 (by decide)
    have e5 := hpo 5 (by decide)
    have hl : (Spec.RsaPkcs1Sig.signSig.words 32).length = 21 := by decide
    simp only [hl, sliceVals, wordVals_eq, List.cons_append, List.nil_append] at h e3 e5 ⊢
    change Curry.apply (α := Mem → List Nat) (sigWords ++ [.addr, .int 32]) _ _ s₁.mem =
      Curry.apply (α := Mem → List Nat) (sigWords ++ [.addr, .int 32]) _ _ s₂.mem at h
    change Curry.apply (α := Mem → List Nat) sigWords _ _ s₁.mem =
      Curry.apply (α := Mem → List Nat) sigWords _ _ s₂.mem
    change (Loc.val s₁ (locAt 3)).setWidth 32 = (Loc.val s₂ (locAt 3)).setWidth 32 at e3
    change (Loc.val s₁ (locAt 5)).setWidth 32 = (Loc.val s₂ (locAt 5)).setWidth 32 at e5
    dsimp only [sigWords, List.cons_append, List.nil_append, Curry.apply, ArgWord.ofRaw] at h ⊢
    refine List.append_inj_left h ?_
    simp only [List.length_map, List.length_append, Proof.Rsa.bytesAt_length', e3, e5]

end VG.Proof.RsaPkcs1Sig.Arm.Sg
