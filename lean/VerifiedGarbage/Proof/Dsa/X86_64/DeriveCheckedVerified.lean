module

public import VerifiedGarbage.Proof.Dsa.X86_64.DeriveCheckedCT
public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
public import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
public import VerifiedGarbage.Proof.Dsa.Validation
public import VerifiedGarbage.Spec.Dsa.DomainChecked
-- Proofs inside exposed definitions (structure values) use these: Lean needs them public.
public import VerifiedGarbage.Proof.Bignum.Octets -- shake: keep
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Bignum.X86_64.CallPost
import VerifiedGarbage.Proof.Dsa.X86_64.PrevalidatedVerified
import VerifiedGarbage.Proof.Rsa.X86_64.CallMont
public import VerifiedGarbage.Impl.Dsa.X86_64.Generate
public import VerifiedGarbage.Spec.Dsa.Derive
public import VerifiedGarbage.Proof.Dsa.Contract
import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Dsa.X86_64.ParametersVerified
public import VerifiedGarbage.Proof.Dsa.X86_64.DeriveMainCT
public import VerifiedGarbage.Proof.Dsa.X86_64.DeriveCT
import VerifiedGarbage.Proof.Dsa.X86_64.ABIRegions
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingABI
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.MdStream.Spec
import VerifiedGarbage.Proof.Sha256.Stream
-- Proofs inside exposed definitions (structure values) use these: Lean needs them public.
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
public import VerifiedGarbage.Spec.Rsa.Contract

/-! ### `Dsa.X86_64.KeygenCalls`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.DeriveVerified`, which this module and modules that import it used -/

section

/-! # x86-64 DSA key derivation verified against the shared contract -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem stackArgs_three (s : State) : List.map (stackArg s) (List.range 3) =
    [stackArg s 0, stackArg s 1, stackArg s 2] := rfl

theorem disjoint_byte_ne {p q : Addr} {n m i j : Nat} (h : (⟨p, n⟩ : Region).Disjoint ⟨q, m⟩)
    (hi : i < n) (hj : j < m) (hn : n ≤ 2 ^ 64) (hm : m ≤ 2 ^ 64) :
    p + BitVec.ofNat 64 i ≠ q + BitVec.ofNat 64 j := fun he =>
  h _ (contains_byte p hi hn) (he ▸ contains_byte q hj hm)

structure DeriveABI (s : State) : Prop where
  stackBound : (s.gpr .rsp).toNat + 32 ≤ 2 ^ 64
  rd : s.rd = [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r9, (stackArg s 0).toNat⟩, ⟨stackArgAddr s 0, 24⟩]
  wr : s.wr = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩]
  outParams : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  outScalar : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .r9, (stackArg s 0).toNat⟩
  outScratch : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩
  paramsScratch : (⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩
  scalarScratch : (⟨s.gpr .r9, (stackArg s 0).toNat⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩
  scratchArgs : (⟨stackArg s 1, (stackArg s 2).toNat * 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 24⟩
  retScratch : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩
  retOut : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  outBound : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64
  paramsBound : (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64
  scalarBound : (s.gpr .r9).toNat + (stackArg s 0).toNat ≤ 2 ^ 64
  scratchBound : (stackArg s 1).toNat + (stackArg s 2).toNat * 8 ≤ 2 ^ 64
  lengths : Spec.Dsa.lengthsValid (s.gpr .r8).toNat (stackArg s 0).toNat
  outLength : (s.gpr .rsi).toNat = 3 * (s.gpr .r8).toNat + 2 * (stackArg s 0).toNat
  paramsLength : (s.gpr .rcx).toNat = 2 * (s.gpr .r8).toNat + (stackArg s 0).toNat
  scratchLength : Spec.Dsa.scratchWords (s.gpr .r8).toNat ≤ (stackArg s 2).toNat

theorem deriveABI_of {s : State} (h : (Spec.Dsa.deriveKeyContract abi).pre s) : DeriveABI s := by
  sig_pre [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three] at h
  sig_pre [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three] at h
  sig_split h
  constructor <;> with_reducible assumption

def DeriveABI.input {s : State} (h : DeriveABI s) : DeriveInput where
  base := stackArg s 1
  pLen := (s.gpr .r8).toNat
  qLen := (stackArg s 0).toNat
  params := Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat
  lengths := h.lengths
  paramsLength := (bytesAt_length _ _ _).trans h.paramsLength
  x := Spec.Rsa.bytesAt s.mem (s.gpr .r9) (stackArg s 0).toNat
  xLength := bytesAt_length _ _ _

theorem DeriveABI.used {s : State} (h : DeriveABI s) : deriveExtent ≤ (stackArg s 2).toNat * 8 := by
  have hl := h.lengths
  have hs := h.scratchLength
  unfold Spec.Dsa.lengthsValid at hl
  unfold Spec.Dsa.scratchWords at hs
  change 16096 ≤ _
  omega_arith

theorem DeriveABI.pre {s : State} (h : DeriveABI s) : DerivePre h.input s := by
  have hs : Scr s (stackArg s 1) ((stackArg s 2).toNat * 8) := Scr.of_mem (by rw [h.wr]; simp) h.scratchBound
  have hargs : (⟨stackArgAddr s 0, 24⟩ : Region) ∈ s.rd ++ s.wr := by rw [h.rd]; simp
  have hout : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region) ∈ s.wr := by rw [h.wr]; simp
  have hol : h.input.outLen = (s.gpr .rsi).toNat := h.outLength.symm
  have hu : usedBytes ≤ deriveExtent := by decide
  refine ⟨scratch_prefix hs h.used (by decide), ?_, ?_, (ofNat_toNat64 _).symm, rfl, (ofNat_toNat64 _).symm,
    source_shrink (src_of_region (by rw [h.rd]; simp) (Nat.le_of_lt (s.gpr .rcx).isLt) h.paramsScratch) h.used,
    source_shrink (src_of_region (p := s.gpr .r9) (by rw [h.rd]; simp) (Nat.le_of_lt (stackArg s 0).isLt)
      h.scalarScratch) h.used, ?_, ?_, ?_, ?_⟩
  · intro j hj hb
    exact stackWord_read (count := 3) hargs hj (by omega_arith) (by decide)
  · intro j hj hb i hi
    exact Nat.le_trans (Nat.le_trans hu h.used)
      (stackWord_separate (count := 3) h.scratchArgs hj (by omega_arith) (by decide) i hi)
  · intro i hi
    rw [hol] at hi
    exact ⟨_, hout, contains_byte _ hi (Nat.le_of_lt (s.gpr .rsi).isLt)⟩
  · intro i hi
    rw [hol] at hi
    exact Nat.le_trans h.used (out_scr h.outScratch (contains_byte _ hi (Nat.le_of_lt (s.gpr .rsi).isLt)))
  · intro i hi j hj
    rw [hol] at hj
    exact (disjoint_byte_ne h.outParams hj (by rw [h.paramsLength]; exact hi)
      (Nat.le_of_lt (s.gpr .rsi).isLt) (Nat.le_of_lt (s.gpr .rcx).isLt)).symm
  · intro i hi j hj
    rw [hol] at hj
    exact (disjoint_byte_ne h.outScalar hj hi
      (Nat.le_of_lt (s.gpr .rsi).isLt) (Nat.le_of_lt (stackArg s 0).isLt)).symm

def DeriveABI.call {s : State} (h : DeriveABI s) : DeriveCall := ⟨h.input, s, h.pre⟩

theorem deriveGprPreserved {s t : State} (h : DeriveABI s) (hp : DerivePost h.input s t) :
    gprPreserved s t := by
  obtain ⟨_, _, hsaved, hf, hk⟩ := hp
  refine ⟨?_, Mem.readW_congr fun i hi => ?_⟩
  · intro reg hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsaved 0 (by decide)
    · exact hsaved 1 (by decide)
    · exact hk.gpr (by decide)
    · exact hsaved 2 (by decide)
    · exact hsaved 3 (by decide)
    · exact hsaved 4 (by decide)
    · exact hsaved 5 (by decide)
  · refine hf _ (Nat.le_trans h.used (out_scr h.retScratch
      (contains_byte (s.gpr .rsp) (i := i) (len := 8) hi (by decide)))) fun j hj => ?_
    have hol : h.input.outLen = (s.gpr .rsi).toNat := h.outLength.symm
    rw [hol] at hj
    exact disjoint_byte_ne h.retOut hi hj (by decide) (Nat.le_of_lt (s.gpr .rsi).isLt)

theorem deriveSharedPost {s t : State} (h : DeriveABI s) (hp : DerivePost h.input s t) :
    (Spec.Dsa.deriveKeyContract abi).post s t := by
  sig_post [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three]
  have hol : h.input.outLen = (s.gpr .rsi).toNat := h.outLength.symm
  obtain ⟨hret, hbytes, _⟩ := hp
  refine ⟨?_, ?_⟩
  · rw [hret]
    change _ = Spec.Dsa.signStatus (Spec.Dsa.deriveKeyBytes h.input.pLen h.input.qLen h.input.params h.input.x)
    cases Spec.Dsa.deriveKeyBytes h.input.pLen h.input.qLen h.input.params h.input.x <;> rfl
  · rw [← hol]
    exact hbytes

theorem deriveCorrect (M : Mont) (Sq : MontS)
    (hmx : (Generate.deriveKey Sq.mm M.mm).allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (h : (Spec.Dsa.deriveKeyContract abi).pre s) :
    ∃ trace t, Exec isa (Generate.deriveKey Sq.mm M.mm) s trace t ∧ abiPreserved s t ∧
      (Spec.Dsa.deriveKeyContract abi).post s t := by
  have ha := deriveABI_of h
  obtain ⟨trace, t, he, hp⟩ := deriveMain_ok M Sq ha.pre
  exact ⟨trace, t, he, abiPreserved_of_exec hmx he (deriveGprPreserved ha hp), deriveSharedPost ha hp⟩

theorem ExecutionLayout.ext' {L₁ L₂ : ExecutionLayout} (hb : L₁.base = L₂.base) (hp : L₁.pLen = L₂.pLen)
    (hq : L₁.qLen = L₂.qLen) (hm : L₁.modulus = L₂.modulus) (hs : L₁.subgroup = L₂.subgroup)
    (hpi : L₁.pInverse = L₂.pInverse) (hqi : L₁.qInverse = L₂.qInverse) (hf : L₁.fields = L₂.fields) :
    L₁ = L₂ := by
  cases L₁
  cases L₂
  simp only at hb hp hq hm hs hpi hqi hf
  subst hb hp hq hm hs hpi hqi hf
  rfl

theorem derivePublicRelated {s₁ s₂ : State} (h₁ : DeriveABI s₁) (h₂ : DeriveABI s₂)
    (h : (Spec.Dsa.deriveKeyContract abi).pub s₁ s₂) : Two DeriveStart s₁ s₂ := by
  sig_pub [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hl, hdi, _, hdx, _, h8, h9, a0, a1, _⟩ := h
  have hpub := (List.append_inj' hl (List.length_singleton.trans List.length_singleton.symm)).1
  have hb := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hpub
  have hp : h₁.input.pLen = h₂.input.pLen := congrArg BitVec.toNat h8
  have hq : h₁.input.qLen = h₂.input.qLen := congrArg BitVec.toNat a0
  have hpb : h₁.input.params = h₂.input.params := hb
  have hpb' : h₁.input.pb = h₂.input.pb := by
    change h₁.input.params.take h₁.input.pLen = h₂.input.params.take h₂.input.pLen
    rw [hpb, hp]
  have hqb' : h₁.input.qb = h₂.input.qb := by
    change (h₁.input.params.drop h₁.input.pLen).take h₁.input.qLen =
      (h₂.input.params.drop h₂.input.pLen).take h₂.input.qLen
    rw [hpb, hp, hq]
  have hac : h₁.input.accepted = h₂.input.accepted := by
    unfold ParametersInput.accepted
    congr 1
  have hlayout : h₁.call.layout = h₂.call.layout := by
    have hf : deriveFieldValues s₁ (BitVec.ofNat 64 h₁.input.qLen) h₁.input.base h₁.input.accepted =
        deriveFieldValues s₂ (BitVec.ofNat 64 h₂.input.qLen) h₂.input.base h₂.input.accepted := by
      have hbase : h₁.input.base = h₂.input.base := a1
      funext f
      cases f <;> simp only [deriveFieldValues, hdi, hdx, h8, h9, hq, hbase, hac]
    exact ExecutionLayout.ext' a1 hp hq (congrArg Spec.Dsa.decodeBE hpb') (congrArg Spec.Dsa.decodeBE hqb')
      (show (0 : BitVec 64) = 0 from rfl) (show (0 : BitVec 64) = 0 from rfl) hf
  exact ⟨h₂.call, ⟨h₁.call, ⟨hlayout, hpb, hsp⟩, rfl⟩, ⟨h₂.call, ⟨rfl, rfl, rfl⟩, rfl⟩⟩

theorem deriveConstantTime (M : Mont) (Sq : MontS) :
    ConstantTime isa (Spec.Dsa.deriveKeyContract abi).pre
      (Spec.Dsa.deriveKeyContract abi).pub (Generate.deriveKey Sq.mm M.mm) := by
  intro s₁ s₂ trace₁ trace₂ t₁ t₂ h₁ h₂ hp e₁ e₂
  exact (deriveMain_ct M Sq _ _ _ _ _ _
    (derivePublicRelated (deriveABI_of h₁) (deriveABI_of h₂) hp) e₁ e₂).1

/-- An ordinary 1024/160 call with disjoint buffers. The all-zero domain is
allowed by the contract and rejected by the program. -/
def deriveSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 424 | .rdx => 0x2000 | .rcx => 276
    | .r8 => 128 | .r9 => 0x3000 | .rsp => 0x10000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x10008 then 20 else if a = 0x10011 then 0x80 else if a = 0x10019 then 8 else 0
  rd := [⟨0x2000, 276⟩, ⟨0x3000, 20⟩, ⟨0x10008, 24⟩]
  wr := [⟨0x1000, 424⟩, ⟨0x8000, 16384⟩]

end VG.Proof.Dsa.X86_64

end

end

/-! # The domain check and key derivation with call-based arithmetic backends -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Dsa.X86_64
open VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

theorem parameters_implies8 :
    (Proof.Dsa.checkParametersContract abi).Implies (Proof.Dsa.checkParametersContract abi 8) where
  pre := by
    intro s h
    sig_pre [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argRegs, stackArgs_zero, List.range, List.range.loop] at h
    sig_split h
    sig_pre [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argRegs, stackArgs_zero, List.range, List.range.loop]
    sig_and_intros
    sig_close
  post := by sig_implies_post [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argRegs,
    stackArgs_zero, List.range, List.range.loop]
  pub := by intro s t _ _ h; exact h
  sat := by
    sig_implies_sat [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argRegs, stackArgs_zero, List.range, List.range.loop]
      [parametersSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using parametersSatState

theorem derive_implies8 : (Spec.Dsa.deriveKeyContract abi).Implies (Spec.Dsa.deriveKeyContract abi 8) where
  pre := by
    intro s h
    sig_pre [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three, List.range, List.range.loop] at h
    sig_pre [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three, List.range, List.range.loop] at h
    sig_split h
    sig_pre [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three, List.range, List.range.loop]
    sig_pre [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three, List.range, List.range.loop]
    sig_and_intros
    sig_close
  post := by sig_implies_post [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three, List.range, List.range.loop]
  pub := by intro s t _ _ h; exact h
  sat := by
    sig_implies_sat [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three, List.range, List.range.loop]
      [deriveSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using deriveSatState

theorem parameters_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64)
    (hp : (Proof.Dsa.checkParametersContract abi).post s b) :
    (Proof.Dsa.checkParametersContract abi).post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  sig_post [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argRegs, stackArgs_zero, List.range, List.range.loop] at hp ⊢
  simpa only [State.patch_gpr] using hp

theorem derive_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64)
    (hs : (Spec.Dsa.deriveKeyContract abi).pre s) (hc : Clear (hole (s.gpr .rsp)) s)
    (hp : (Spec.Dsa.deriveKeyContract abi).post s b) :
    (Spec.Dsa.deriveKeyContract abi).post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  have ha := deriveABI_of hs
  have hm := Clear.miss_wr hc (by rw [ha.wr]; exact List.mem_cons_self) ha.outBound (Nat.le_refl _)
  sig_post [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three, List.range, List.range.loop] at hp ⊢
  simpa only [State.patch_gpr, patch_mem, bytesAt_overlay hm] using hp

theorem parameters_call_verified (M : Mont) (Sq : MontS) {c : Prog isa}
    (hc : c.InlineOk = true) (hin : c.inline = Generate.checkParameters Sq.mm M.mm)
    (hmx : (Generate.checkParameters Sq.mm M.mm).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target c (Proof.Dsa.checkParametersContract abi 8) :=
  Verified.of_inline_sig hc (hin ▸ parametersCorrect M Sq hmx) (hin ▸ parametersConstantTime M Sq)
    parameters_implies8 (fun _ h => Sig.clear_of_pre h) (fun _ _ _ _ h => Sig.rsp_of_pub h)
    (fun s b hv u _ _ hp => parameters_patch s b hv u hp)

theorem derive_call_verified (M : Mont) (Sq : MontS) {c : Prog isa}
    (hc : c.InlineOk = true) (hin : c.inline = Generate.deriveKey Sq.mm M.mm)
    (hmx : (Generate.deriveKey Sq.mm M.mm).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target c (Spec.Dsa.deriveKeyContract abi 8) :=
  Verified.of_inline_sig hc (hin ▸ deriveCorrect M Sq hmx) (hin ▸ deriveConstantTime M Sq)
    derive_implies8 (fun _ h => Sig.clear_of_pre h) (fun _ _ _ _ h => Sig.rsp_of_pub h)
    derive_patch

end VG.Proof.Dsa.X86_64

end

end

/-! # x86-64 DSA key derivation for a checked domain, against its contract

`Generate.deriveChecked` is verified against `deriveKeyDomainCheckedContract`
(`Spec/Dsa/DomainChecked.lean`): `deriveKeyContract` under the precondition
that the exact domain bytes pass `checkParametersBytes`. Key generation calls
it once its domain check has returned 1. -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64 VG.Proof.Rsa.X86_64

theorem deriveChecked_pre {s : State} {stack : Nat}
    (h : (Spec.Dsa.deriveKeyDomainCheckedContract abi stack).pre s) :
    (Spec.Dsa.deriveKeyContract abi stack).pre s ∧
      Spec.Dsa.checkParametersBytes (s.gpr .r8).toNat (stackArg s 0).toNat
        (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) = true := by
  sig_pre [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three,
    List.range, List.range.loop] at h
  sig_pre [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three,
    List.range, List.range.loop] at h
  sig_split h
  refine ⟨?_, by assumption⟩
  sig_pre [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three, List.range,
    List.range.loop]
  sig_pre [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three, List.range,
    List.range.loop]
  sig_and_intros <;> with_reducible assumption

theorem deriveChecked_of_pre {s : State} {stack : Nat} (h : (Spec.Dsa.deriveKeyContract abi stack).pre s)
    (hc : Spec.Dsa.checkParametersBytes (s.gpr .r8).toNat (stackArg s 0).toNat
        (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) = true) :
    (Spec.Dsa.deriveKeyDomainCheckedContract abi stack).pre s := by
  sig_pre [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three, List.range,
    List.range.loop] at h
  sig_pre [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three, List.range,
    List.range.loop] at h
  sig_pre [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three,
    List.range, List.range.loop]
  sig_pre [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three,
    List.range, List.range.loop]
  sig_split h
  sig_and_intros <;> with_reducible assumption

theorem deriveCheckedCorrect (M : Mont) (Sq : MontS)
    (hmx : (Generate.deriveChecked Sq.mm M.mm).allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (h : (Spec.Dsa.deriveKeyDomainCheckedContract abi).pre s) :
    ∃ trace t, Exec isa (Generate.deriveChecked Sq.mm M.mm) s trace t ∧ abiPreserved s t ∧
      (Spec.Dsa.deriveKeyDomainCheckedContract abi).post s t := by
  obtain ⟨hd, hc⟩ := deriveChecked_pre h
  have ha := deriveABI_of hd
  obtain ⟨trace, t, he, hp⟩ := deriveCheckedMain_ok M Sq ha.pre hc
  exact ⟨trace, t, he, abiPreserved_of_exec hmx he (deriveGprPreserved ha hp), deriveSharedPost ha hp⟩

theorem deriveCheckedConstantTime (M : Mont) (Sq : MontS) :
    ConstantTime isa (Spec.Dsa.deriveKeyDomainCheckedContract abi).pre
      (Spec.Dsa.deriveKeyDomainCheckedContract abi).pub (Generate.deriveChecked Sq.mm M.mm) := by
  intro s₁ s₂ trace₁ trace₂ t₁ t₂ h₁ h₂ hp e₁ e₂
  exact (deriveCheckedMain_ct M Sq _ _ _ _ _ _
    (derivePublicRelated (deriveABI_of (deriveChecked_pre h₁).1) (deriveABI_of (deriveChecked_pre h₂).1) hp)
      e₁ e₂).1

/-- `validKeyWitness`'s domain, the first 276 of its bytes. -/
def validDomainWitness : List Byte := VG.Proof.Dsa.validKeyWitness.take 276

theorem validDomainWitness_length : validDomainWitness.length = 276 := by
  simp only [validDomainWitness, List.length_take, VG.Proof.Dsa.validKeyWitness_length]; rfl

theorem validDomainWitness_valid : Spec.Dsa.checkParametersBytes 128 20 validDomainWitness = true := by
  decide +kernel

/-- `deriveSatState` with `validDomainWitness` at `0x2000`. -/
def deriveCheckedSatState : State where
  gpr := deriveSatState.gpr
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if 0x2000 ≤ a.toNat ∧ a.toNat < 0x2114 then
    validDomainWitness[a.toNat - 0x2000]?.getD 0 else deriveSatState.mem a
  rd := deriveSatState.rd
  wr := deriveSatState.wr

theorem deriveCheckedSat_domain :
    Spec.Rsa.bytesAt deriveCheckedSatState.mem 0x2000 276 = validDomainWitness :=
  bytesAt_window (base := 0x2000) validDomainWitness_length (by decide) fun a h₁ h₂ => by
    simp only [deriveCheckedSatState]
    exact ite_eq_left ⟨h₁, h₂⟩

theorem deriveCheckedSat_valid : Spec.Dsa.checkParametersBytes 128 20
    (Spec.Rsa.bytesAt deriveCheckedSatState.mem 0x2000 276) = true := by
  rw [deriveCheckedSat_domain]; exact validDomainWitness_valid

theorem deriveCheckedSatisfiable : ∃ s, (Spec.Dsa.deriveKeyDomainCheckedContract abi).pre s := by
  have ho : ∃ s, (Spec.Dsa.deriveKeyContract abi).pre s ∧ s = deriveCheckedSatState := by
    sig_implies_sat [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three]
      [deriveCheckedSatState, deriveSatState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using deriveCheckedSatState
  obtain ⟨s, h, rfl⟩ := ho
  exact ⟨_, deriveChecked_of_pre h deriveCheckedSat_valid⟩

theorem deriveCheckedSatisfiable8 : ∃ s, (Spec.Dsa.deriveKeyDomainCheckedContract abi 8).pre s := by
  have ho : ∃ s, (Spec.Dsa.deriveKeyContract abi 8).pre s ∧ s = deriveCheckedSatState := by
    sig_implies_sat [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three,
      List.range, List.range.loop]
      [deriveCheckedSatState, deriveSatState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using deriveCheckedSatState
  obtain ⟨s, h, rfl⟩ := ho
  exact ⟨_, deriveChecked_of_pre h deriveCheckedSat_valid⟩

theorem derive_checked_verified (M : Mont) (Sq : MontS)
    (hmx : (Generate.deriveChecked Sq.mm M.mm).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target (Generate.deriveChecked Sq.mm M.mm) (Spec.Dsa.deriveKeyDomainCheckedContract abi) :=
  ⟨deriveCheckedCorrect M Sq hmx, deriveCheckedConstantTime M Sq, deriveCheckedSatisfiable⟩

theorem deriveChecked_implies8 :
    (Spec.Dsa.deriveKeyDomainCheckedContract abi).Implies (Spec.Dsa.deriveKeyDomainCheckedContract abi 8) where
  pre := by
    intro s h
    sig_pre [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three,
      List.range, List.range.loop] at h
    sig_pre [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three,
      List.range, List.range.loop] at h
    sig_split h
    sig_pre [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three,
      List.range, List.range.loop]
    sig_pre [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three,
      List.range, List.range.loop]
    sig_and_intros
    sig_close
  post := by sig_implies_post [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, abi, argRegs,
    stackArgs_three, List.range, List.range.loop]
  pub := by intro s t _ _ h; exact h
  sat := deriveCheckedSatisfiable8

theorem deriveChecked_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64)
    (hs : (Spec.Dsa.deriveKeyDomainCheckedContract abi).pre s) (hc : Clear (hole (s.gpr .rsp)) s)
    (hp : (Spec.Dsa.deriveKeyDomainCheckedContract abi).post s b) :
    (Spec.Dsa.deriveKeyDomainCheckedContract abi).post s (b.patch (hole (s.gpr .rsp)) hv u) :=
  derive_patch s b hv u (deriveChecked_pre hs).1 hc hp

theorem derive_checked_call_verified (M : Mont) (Sq : MontS) {c : Prog isa}
    (hc : c.InlineOk = true) (hin : c.inline = Generate.deriveChecked Sq.mm M.mm)
    (hmx : (Generate.deriveChecked Sq.mm M.mm).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target c (Spec.Dsa.deriveKeyDomainCheckedContract abi 8) :=
  Verified.of_inline_sig hc (hin ▸ deriveCheckedCorrect M Sq hmx) (hin ▸ deriveCheckedConstantTime M Sq)
    deriveChecked_implies8 (fun _ h => Sig.clear_of_pre h) (fun _ _ _ _ h => Sig.rsp_of_pub h)
    deriveChecked_patch

end VG.Proof.Dsa.X86_64
