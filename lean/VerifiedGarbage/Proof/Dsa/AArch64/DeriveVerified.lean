module

import VerifiedGarbage.Proof.Dsa.AArch64.DeriveMainCT
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Dsa.AArch64.DeriveCT
import VerifiedGarbage.Proof.Dsa.AArch64.ABIRegions
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.AArch64.PcCode
import VerifiedGarbage.Proof.Bignum.Octets

/-! # AArch64 DSA key derivation verified against the shared contract -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem deriveStackArgs (s : State) : List.map (stackArg s) (List.range 1) =
    [stackArg s 0] := rfl

theorem disjoint_byte_ne {p q : Addr} {n m i j : Nat} (h : (⟨p, n⟩ : Region).Disjoint ⟨q, m⟩)
    (hi : i < n) (hj : j < m) (hn : n ≤ 2 ^ 64) (hm : m ≤ 2 ^ 64) :
    p + BitVec.ofNat 64 i ≠ q + BitVec.ofNat 64 j := fun he =>
  h _ (contains_byte p hi hn) (he ▸ contains_byte q hj hm)

structure DeriveABI (s : State) : Prop where
  stackBound : s.sp.toNat + 8 ≤ 2 ^ 64
  rd : s.rd = [⟨s.gpr .x2, (s.gpr .x3).toNat⟩, ⟨s.gpr .x5, (s.gpr .x6).toNat⟩, ⟨stackArgAddr s 0, 8⟩]
  wr : s.wr = [⟨s.gpr .x0, (s.gpr .x1).toNat⟩, ⟨s.gpr .x7, (stackArg s 0).toNat * 8⟩]
  outParams : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region).Disjoint ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
  outScalar : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region).Disjoint ⟨s.gpr .x5, (s.gpr .x6).toNat⟩
  outScratch : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region).Disjoint ⟨s.gpr .x7, (stackArg s 0).toNat * 8⟩
  paramsScratch : (⟨s.gpr .x2, (s.gpr .x3).toNat⟩ : Region).Disjoint ⟨s.gpr .x7, (stackArg s 0).toNat * 8⟩
  scalarScratch : (⟨s.gpr .x5, (s.gpr .x6).toNat⟩ : Region).Disjoint ⟨s.gpr .x7, (stackArg s 0).toNat * 8⟩
  scratchArgs : (⟨s.gpr .x7, (stackArg s 0).toNat * 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 8⟩
  outBound : (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64
  paramsBound : (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64
  scalarBound : (s.gpr .x5).toNat + (s.gpr .x6).toNat ≤ 2 ^ 64
  scratchBound : (s.gpr .x7).toNat + (stackArg s 0).toNat * 8 ≤ 2 ^ 64
  lengths : Spec.Dsa.lengthsValid (s.gpr .x4).toNat (s.gpr .x6).toNat
  outLength : (s.gpr .x1).toNat = 3 * (s.gpr .x4).toNat + 2 * (s.gpr .x6).toNat
  paramsLength : (s.gpr .x3).toNat = 2 * (s.gpr .x4).toNat + (s.gpr .x6).toNat
  scratchLength : Spec.Dsa.scratchWords (s.gpr .x4).toNat ≤ (stackArg s 0).toNat

theorem deriveABI_of {s : State} (h : (Spec.Dsa.deriveKeyContract abi).pre s) : DeriveABI s := by
  sig_pre [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, deriveStackArgs] at h
  sig_pre [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, deriveStackArgs] at h
  sig_split h
  constructor <;> with_reducible assumption

def DeriveABI.input {s : State} (h : DeriveABI s) : DeriveInput where
  base := s.gpr .x7
  pLen := (s.gpr .x4).toNat
  qLen := (s.gpr .x6).toNat
  params := Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat
  lengths := h.lengths
  paramsLength := (bytesAt_length _ _ _).trans h.paramsLength
  x := Spec.Rsa.bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat
  xLength := bytesAt_length _ _ _

theorem DeriveABI.used {s : State} (h : DeriveABI s) : deriveExtent ≤ (stackArg s 0).toNat * 8 := by
  have hl := h.lengths
  have hs := h.scratchLength
  unfold Spec.Dsa.lengthsValid at hl
  unfold Spec.Dsa.scratchWords at hs
  change 16096 ≤ _
  omega

theorem DeriveABI.pre {s : State} (h : DeriveABI s) : DerivePre h.input s := by
  have hs : Scr s (s.gpr .x7) ((stackArg s 0).toNat * 8) := Scr.of_mem (by rw [h.wr]; simp) h.scratchBound
  have hout : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region) ∈ s.wr := by rw [h.wr]; simp
  have hol : h.input.outLen = (s.gpr .x1).toNat := h.outLength.symm
  have hu : usedBytes ≤ deriveExtent := by decide
  refine ⟨scratch_prefix hs h.used (by decide), (ofNat_toNat64 _).symm, rfl, (ofNat_toNat64 _).symm,
    source_shrink (src_of_region (by rw [h.rd]; simp) (Nat.le_of_lt (s.gpr .x3).isLt) h.paramsScratch) h.used,
    source_shrink (src_of_region (p := s.gpr .x5) (by rw [h.rd]; simp) (Nat.le_of_lt (s.gpr .x6).isLt)
      h.scalarScratch) h.used, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hol] at hi
    exact ⟨_, hout, contains_byte _ hi (Nat.le_of_lt (s.gpr .x1).isLt)⟩
  · intro i hi
    rw [hol] at hi
    exact Nat.le_trans h.used (out_scr h.outScratch (contains_byte _ hi (Nat.le_of_lt (s.gpr .x1).isLt)))
  · intro i hi j hj
    rw [hol] at hj
    exact (disjoint_byte_ne h.outParams hj (by rw [h.paramsLength]; exact hi)
      (Nat.le_of_lt (s.gpr .x1).isLt) (Nat.le_of_lt (s.gpr .x3).isLt)).symm
  · intro i hi j hj
    rw [hol] at hj
    exact (disjoint_byte_ne h.outScalar hj hi
      (Nat.le_of_lt (s.gpr .x1).isLt) (Nat.le_of_lt (s.gpr .x6).isLt)).symm

def DeriveABI.call {s : State} (h : DeriveABI s) : DeriveCall := ⟨h.input, s, h.pre⟩

theorem derivePreserved {s t : State} (h : DeriveABI s) (hp : DerivePost h.input s t) :
    abiPreserved s t := abiPreserved_of_keep hp.2.2.2

theorem deriveSharedPost {s t : State} (h : DeriveABI s) (hp : DerivePost h.input s t) :
    (Spec.Dsa.deriveKeyContract abi).post s t := by
  sig_post [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, deriveStackArgs]
  have hol : h.input.outLen = (s.gpr .x1).toNat := h.outLength.symm
  obtain ⟨hret, hbytes, _⟩ := hp
  refine ⟨?_, ?_⟩
  · rw [hret]
    change _ = Spec.Dsa.signStatus (Spec.Dsa.deriveKeyBytes h.input.pLen h.input.qLen h.input.params h.input.x)
    cases Spec.Dsa.deriveKeyBytes h.input.pLen h.input.qLen h.input.params h.input.x <;> rfl
  · rw [← hol]
    exact hbytes

theorem deriveCorrect (M : Mont)
    (s : State) (h : (Spec.Dsa.deriveKeyContract abi).pre s) :
    ∃ trace t, Exec isa (Generate.deriveKey M.mm) s trace t ∧ abiPreserved s t ∧
      (Spec.Dsa.deriveKeyContract abi).post s t := by
  have ha := deriveABI_of h
  obtain ⟨trace, t, he, hp⟩ := deriveMain_ok M ha.pre
  exact ⟨trace, t, he, derivePreserved ha hp, deriveSharedPost ha hp⟩

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
  sig_pub [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, deriveStackArgs] at h
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
      rfl rfl hf
  exact ⟨h₂.call, ⟨h₁.call, ⟨hlayout, hpb, hsp⟩, rfl⟩, ⟨h₂.call, ⟨rfl, rfl, rfl⟩, rfl⟩, hsp⟩

theorem deriveConstantTime (M : Mont) :
    ConstantTime isa (Spec.Dsa.deriveKeyContract abi).pre
      (Spec.Dsa.deriveKeyContract abi).pub (Generate.deriveKey M.mm) := by
  intro s₁ s₂ trace₁ trace₂ t₁ t₂ h₁ h₂ hp e₁ e₂
  exact (deriveMain_ct M _ _ _ _ _ _
    (derivePublicRelated (deriveABI_of h₁) (deriveABI_of h₂) hp) e₁ e₂).1

/-- An ordinary 1024/160 call with disjoint buffers. The all-zero domain is
allowed by the contract and rejected by the program. -/
def deriveSatState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 424 | .x2 => 0x2000 | .x3 => 276
    | .x4 => 128 | .x5 => 0x3000 | .x6 => 20 | .x7 => 0x8000 | _ => 0
  sp := 0x10000
  mem a := if a = 0x10001 then 8 else 0
  rd := [⟨0x2000, 276⟩, ⟨0x3000, 20⟩, ⟨0x10000, 8⟩]
  wr := [⟨0x1000, 424⟩, ⟨0x8000, 16384⟩]

theorem deriveSatisfiable : ∃ s, (Spec.Dsa.deriveKeyContract abi).pre s := by
  sig_implies_sat [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, deriveStackArgs]
    [deriveSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using deriveSatState

theorem derive_verified (M : Mont)
    :
    Verified target (Generate.deriveKey M.mm) (Spec.Dsa.deriveKeyContract abi) :=
  ⟨deriveCorrect M, deriveConstantTime M, deriveSatisfiable⟩

end VG.Proof.Dsa.AArch64
