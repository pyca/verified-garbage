module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.SignVerified
public import VerifiedGarbage.Proof.Framework.AArch64.AppendSlice
public import VerifiedGarbage.Proof.Rsa.PreKey
import VerifiedGarbage.Proof.Rsa.PrivCheck
import VerifiedGarbage.Proof.Framework.Contract

/-! # `vg_rsa_pkcs1_sign_precomputed` on AArch64

`vg_rsa_pkcs1_sign`'s code, which ignores the key's precomputed values `pre`
(`Spec/Rsa/PrivatePrecompute.lean` lets an implementation ignore them),
proven against `vg_rsa_pkcs1_sign_precomputed`'s contract from its own
(`verified_withSlice`), with a state that meets it (`satisfiablePre`), which
holds a real key (`Proof/Rsa/PreKey.lean`).
-/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.AArch64.Sgn
open VG VG.AArch64 VG.Impl.RsaPkcs1Sig.AArch64.Sign
open VG.Proof.Rsa.PreKey (keyIn keyMem key_pre_of)

theorem wordVals_eq (s : State) : wordVals 21 s = [s.gpr .x0, s.gpr .x1, s.gpr .x2, s.gpr .x3, s.gpr .x4, s.gpr .x5, s.gpr .x6, s.gpr .x7, stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10, stackArg s 11, stackArg s 12] := rfl

/-- `Spec.RsaPkcs1Sig.signSig.words 64`. -/
abbrev sigWords : List ArgWord :=
  [.addr, .int 64, .addr, .int 64, .addr, .int 64, .int 32, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64]

/-! ## A state that meets the contract -/

/-- The stack arguments of `preState`; the key (`keyMem`) has `n` at
`0x2000`, `p` at `0x4200`, `q` at `0x4300` and `pre` at `0x4800`. -/
def preArgs : List Nat := [1, 0x4200, 32, 0x4300, 32, 0x4400, 32, 0x4500, 32, 0x4600, 32, 0x10000, 0x420, 0x4800, 24]

/-- The memory of `preState`: the stack arguments from `2^40`, and the key. -/
def preMem (a : Addr) : Byte :=
  let i := a.toNat
  bif Nat.ble 0x10000000000 i && Nat.blt i 0x10000000078 then
    BitVec.ofNat 8 (preArgs.getD ((i - 0x10000000000) / 8) 0 / 256 ^ ((i - 0x10000000000) % 8))
  else bif keyIn i then keyMem a else 0

/-- `satState` with the key and its precomputed values. -/
def preState : State where
  gpr r := match r with
    | .x0 => 0x5000 | .x1 => 64 | .x2 => 0x2000 | .x3 => 64 | .x4 => 0x2100 | .x5 => 1 | .x7 => 0x3000
    | _ => 0
  sp := 0x10000000000
  mem := preMem
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x3000, 1⟩, ⟨0x4200, 32⟩, ⟨0x4300, 32⟩, ⟨0x4400, 32⟩, ⟨0x4500, 32⟩,
    ⟨0x4600, 32⟩, ⟨0x4800, 192⟩, ⟨0x10000000000, 120⟩]
  wr := [⟨0x5000, 64⟩, ⟨0x10000, 8448⟩]

theorem preState_key : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt preState.mem 0x2000 64)
    (Spec.Rsa.bytesAt preState.mem 0x4200 32) (Spec.Rsa.bytesAt preState.mem 0x4300 32) =
      some (Spec.Rsa.wordsAt preState.mem 0x4800 24) :=
  key_pre_of fun a ha => by
    have hs : (Nat.ble 0x10000000000 a.toNat && Nat.blt a.toNat 0x10000000078) = false := by
      simp only [keyIn, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at ha
      refine Bool.eq_false_iff.mpr fun h => ?_
      simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
      omega
    show (bif _ then _ else _) = _
    rw [hs, Bool.cond_false, ha, Bool.cond_true]

theorem pre_args : stackArg preState 0 = 1 ∧ stackArg preState 1 = 0x4200 ∧ stackArg preState 2 = 32 ∧ stackArg preState 3 = 0x4300 ∧ stackArg preState 4 = 32 ∧ stackArg preState 5 = 0x4400 ∧ stackArg preState 6 = 32 ∧ stackArg preState 7 = 0x4500 ∧ stackArg preState 8 = 32 ∧ stackArg preState 9 = 0x4600 ∧ stackArg preState 10 = 32 ∧ stackArg preState 11 = 0x10000 ∧ stackArg preState 12 = 0x420 ∧ stackArg preState 13 = 0x4800 ∧ stackArg preState 14 = 24 := by
  decide

theorem stackArgs_fifteen (s : State) :
    List.map (stackArg s) (List.range 15) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10, stackArg s 11, stackArg s 12, stackArg s 13, stackArg s 14] := rfl

theorem satisfiablePre (K : Nat) (hK : K ≤ 2 ^ 20) :
    ∃ s, (Spec.RsaPkcs1Sig.signPrecomputedContract abi (stk K)).pre s := by
  refine ⟨preState, ?_⟩
  have e : stk K = (frameBytes + K - 1) + 1 := by unfold stk frameBytes; omega
  rw [e]
  sig_pre [Spec.RsaPkcs1Sig.signPrecomputedContract, Spec.RsaPkcs1Sig.signPrecomputedSig, Spec.RsaPkcs1Sig.signSig,
    abi, argRegs, stackArgs_fifteen, List.append_eq]
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩ := pre_args
  have hS : frameBytes + K - 1 + 1 = 1152 + K := by unfold frameBytes; omega
  have hsp : (0x10000000000 : BitVec 64).toNat = 2 ^ 40 := by decide
  have hkb : ((0x10000000000 : BitVec 64) - BitVec.ofNat 64 (1152 + K)).toNat = 2 ^ 40 - (1152 + K) := by
    rw [BitVec.toNat_sub, hsp, BitVec.toNat_ofNat]; omega
  have ha : stackArgAddr preState 0 = 0x10000000000 := by decide
  simp only [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, hS, ha]
  have kd : ∀ (b : BitVec 64) (n : Nat), b.toNat + n ≤ 2 ^ 20 →
      Region.Disjoint ⟨0x10000000000 - BitVec.ofNat 64 (1152 + K), 1152 + K⟩ ⟨b, n⟩ := fun b n h =>
    Region.disjoint_of_le (.inr (by dsimp only; rw [hkb]; omega)) (by dsimp only; rw [hkb]; omega)
      (by dsimp only; omega)
  have kt : Region.Disjoint ⟨0x10000000000 - BitVec.ofNat 64 (1152 + K), 1152 + K⟩ ⟨0x10000000000, 120⟩ :=
    Region.disjoint_of_le (.inl (by dsimp only; rw [hkb, hsp]; omega))
      (by dsimp only; rw [hkb]; omega) (by dsimp only; rw [hsp]; omega)
  sig_and_intros
  rotate_right
  · exact preState_key
  all_goals first
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact kd _ _ (by decide)
    | exact kt
    | (rw [hsp]; omega)
    | (simp only [Spec.Rsa.lenValid]; decide)

/-! ## The code -/

theorem signPrecomputed_verified (c : PrivChecked) :
    Verified AArch64.target (Impl.RsaPkcs1Sig.AArch64.Sign.code c.name c.code)
      (Spec.RsaPkcs1Sig.signPrecomputedContract abi (stk c.stack)) := by
  refine verified_withSlice (sig := Spec.RsaPkcs1Sig.signSig) (nm := "pre") (e := .u64) (ln := "pre_len")
    (by decide) (by decide) (code_verified c) ?_ ?_ ?_ (satisfiablePre c.stack c.le)
  · intro s h
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, -, -⟩ := h
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  · intro s m' v hp hq
    exact hq
  · intro s₁ s₂ _ _ hpo h
    have e3 := hpo 3 (by decide)
    have e5 := hpo 5 (by decide)
    have hl : (Spec.RsaPkcs1Sig.signSig.words 64).length = 21 := by decide
    simp only [hl, sliceVals, wordVals_eq, List.cons_append, List.nil_append] at h e3 e5 ⊢
    change Curry.apply (α := Mem → List Nat) (sigWords ++ [.addr, .int 64]) _ _ s₁.mem =
      Curry.apply (α := Mem → List Nat) (sigWords ++ [.addr, .int 64]) _ _ s₂.mem at h
    change Curry.apply (α := Mem → List Nat) sigWords _ _ s₁.mem =
      Curry.apply (α := Mem → List Nat) sigWords _ _ s₂.mem
    change (s₁.gpr .x3).setWidth 64 = (s₂.gpr .x3).setWidth 64 at e3
    change (s₁.gpr .x5).setWidth 64 = (s₂.gpr .x5).setWidth 64 at e5
    dsimp only [sigWords, List.cons_append, List.nil_append, Curry.apply, ArgWord.ofRaw] at h ⊢
    refine List.append_inj_left h ?_
    simp only [List.length_map, List.length_append, Proof.Rsa.bytesAt_length', e3, e5]

end VG.Proof.RsaPkcs1Sig.AArch64.Sgn
