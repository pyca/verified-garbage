module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.Dec.Verified
public import VerifiedGarbage.Proof.Framework.RISCV64.AppendSlice
public import VerifiedGarbage.Proof.Rsa.PreKey
import VerifiedGarbage.Proof.Rsa.PrivCheck
import VerifiedGarbage.Proof.Framework.Contract

/-! # `vg_rsa_pkcs1_decrypt_precomputed` on RISC-V

`vg_rsa_pkcs1_decrypt`'s code, which ignores the key's precomputed values
`pre` (the specification lets an implementation ignore them), proven against
`vg_rsa_pkcs1_decrypt_precomputed`'s contract from its own
(`verified_withSlice`).
-/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.RISCV64.Dec
open VG VG.RISCV64 VG.Impl.RsaPkcs1Enc.RISCV64.Decrypt

/-- `Spec.RsaPkcs1Enc.decryptSig.words 64`. -/
abbrev decWords : List ArgWord :=
  [.addr, .int 64, .addr, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64,
    .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64]

theorem stackVals_dec (s : State) : stackVals 23 s = [s.gpr .a0, s.gpr .a1, s.gpr .a2, s.gpr .a3, s.gpr .a4,
    s.gpr .a5, s.gpr .a6, s.gpr .a7, stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4,
    stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10, stackArg s 11,
    stackArg s 12, stackArg s 13, stackArg s 14] := rfl

theorem stackVals_decP (s : State) : stackVals (23 + 2) s = stackVals 23 s ++ [stackArg s 15, stackArg s 16] :=
  rfl

/-! ## A state that meets the contract -/

open VG.Proof.Rsa.PreKey (keyIn keyMem key_pre_of)

/-- The stack arguments of `preState`: `d_len`, the input at `0x3000`, `p`
at `0x4200`, `q` at `0x4300`, `dp`, `dq` and `qinv` at `0x4400`, `0x4500`
and `0x4600`, `scratch` at `0xA000`, `pre` at `0x4800`. -/
def preArgs : List Nat := [1, 0x3000, 64, 0x4200, 32, 0x4300, 32, 0x4400, 32, 0x4500, 32, 0x4600, 32,
  0xa000, 0x420, 0x4800, 24]

/-- The memory of `preState`: the stack arguments at `0x10000`, and the key
(`keyMem`: `n` at `0x2000`, `p`, `q` and `pre`). -/
def preMem (a : Addr) : Byte :=
  let i := a.toNat
  bif Nat.ble 0x10000 i && Nat.blt i 0x10088 then
    BitVec.ofNat 8 (preArgs.getD ((i - 0x10000) / 8) 0 / 256 ^ ((i - 0x10000) % 8))
  else bif keyIn i then keyMem a else 0

/-- `out` at `0x1000`, the message's length at `0x6800`, `n` (64 bytes) at
`0x2000`, `e` and `d` at `0x2100` and `0x2200`, the stack arguments at
`sp = 0x10000`. -/
def preState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 64 | .a2 => 0x6800 | .a3 => 0x2000 | .a4 => 64 | .a5 => 0x2100 | .a6 => 1
    | .a7 => 0x2200 | _ => 0
  sp := 0x10000
  mem := preMem
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x2200, 1⟩, ⟨0x3000, 64⟩, ⟨0x4200, 32⟩, ⟨0x4300, 32⟩, ⟨0x4400, 32⟩,
    ⟨0x4500, 32⟩, ⟨0x4600, 32⟩, ⟨0x4800, 192⟩, ⟨0x10000, 136⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x6800, 8⟩, ⟨0xA000, 8448⟩]

theorem stackArgs_seventeen (s : State) :
    List.map (stackArg s) (List.range 17) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11, stackArg s 12, stackArg s 13, stackArg s 14, stackArg s 15, stackArg s 16] := rfl

theorem pre_args : stackArg preState 0 = 1 ∧ stackArg preState 1 = 0x3000 ∧ stackArg preState 2 = 64 ∧
    stackArg preState 3 = 0x4200 ∧ stackArg preState 4 = 32 ∧ stackArg preState 5 = 0x4300 ∧
    stackArg preState 6 = 32 ∧ stackArg preState 7 = 0x4400 ∧ stackArg preState 8 = 32 ∧
    stackArg preState 9 = 0x4500 ∧ stackArg preState 10 = 32 ∧ stackArg preState 11 = 0x4600 ∧
    stackArg preState 12 = 32 ∧ stackArg preState 13 = 0xA000 ∧ stackArg preState 14 = 1056 ∧
    stackArg preState 15 = 0x4800 ∧ stackArg preState 16 = 24 := by
  decide

theorem preState_key : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt preState.mem 0x2000 64)
    (Spec.Rsa.bytesAt preState.mem 0x4200 32) (Spec.Rsa.bytesAt preState.mem 0x4300 32) =
      some (Spec.Rsa.wordsAt preState.mem 0x4800 24) :=
  key_pre_of fun a ha => by
    have hs : (Nat.ble 0x10000 a.toNat && Nat.blt a.toNat 0x10088) = false := by
      simp only [keyIn, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at ha
      refine Bool.eq_false_iff.mpr fun h => ?_
      simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
      omega
    show (bif _ then _ else _) = _
    rw [hs, Bool.cond_false, ha, Bool.cond_true]

theorem satisfiablePre : ∃ s, (Spec.RsaPkcs1Enc.decryptPrecomputedContract abi stackBytes).pre s := by
  refine ⟨preState, ?_⟩
  have e : stackBytes = 3439 + 1 := rfl
  rw [e]
  sig_pre [Spec.RsaPkcs1Enc.decryptPrecomputedContract, Spec.RsaPkcs1Enc.decryptPrecomputedSig,
    Spec.RsaPkcs1Enc.decryptSig, abi, argRegs, stackArgs_seventeen, List.append_eq, List.range,
    List.range.loop]
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16⟩ := pre_args
  have ha : stackArgAddr preState 0 = 0x10000 := by decide
  simp only [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, ha]
  sig_and_intros
  rotate_right 4
  · exact preState_key
  all_goals first
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (unfold Spec.Rsa.lenValid; decide)

theorem decryptPrecomputed_verified :
    Verified target code (Spec.RsaPkcs1Enc.decryptPrecomputedContract abi stackBytes) := by
  refine verified_withSlice (sig := Spec.RsaPkcs1Enc.decryptSig) (nm := "pre") (e := .u64) (ln := "pre_len")
    (by decide) (by decide) dec_verified ?_ ?_ ?_ satisfiablePre
  · intro s h
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, -, -⟩ := h
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
  · intro s m' v hp hq
    exact hq
  · intro s₁ s₂ _ _ hpo h
    have e4 := hpo 4 (by decide)
    have e6 := hpo 6 (by decide)
    have hl : (Spec.RsaPkcs1Enc.decryptSig.words 64).length = 23 := by decide
    simp only [hl, stackVals_decP, stackVals_dec, List.cons_append, List.nil_append] at h e4 e6 ⊢
    change Curry.apply (α := Mem → List Nat) (decWords ++ [.addr, .int 64]) _ _ s₁.mem =
      Curry.apply (α := Mem → List Nat) (decWords ++ [.addr, .int 64]) _ _ s₂.mem at h
    change Curry.apply (α := Mem → List Nat) decWords _ _ s₁.mem =
      Curry.apply (α := Mem → List Nat) decWords _ _ s₂.mem
    change (s₁.gpr .a4).setWidth 64 = (s₂.gpr .a4).setWidth 64 at e4
    change (s₁.gpr .a6).setWidth 64 = (s₂.gpr .a6).setWidth 64 at e6
    dsimp only [decWords, List.cons_append, List.nil_append, Curry.apply, ArgWord.ofRaw] at h ⊢
    refine List.append_inj_left h ?_
    simp only [List.length_map, List.length_append, Proof.Rsa.bytesAt_length', e4, e6]

end VG.Proof.RsaPkcs1Enc.RISCV64.Dec
