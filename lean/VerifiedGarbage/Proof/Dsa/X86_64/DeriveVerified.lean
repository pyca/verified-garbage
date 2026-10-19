module

public import VerifiedGarbage.Proof.Dsa.X86_64.DeriveMainCT
public import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Dsa.X86_64.DeriveCT
import VerifiedGarbage.Proof.Dsa.X86_64.ABIRegions
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingABI
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.MdStream.Spec
import VerifiedGarbage.Proof.Sha256.Stream

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
  omega

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
    exact stackWord_read (count := 3) hargs hj (by omega) (by decide)
  · intro j hj hb i hi
    exact Nat.le_trans (Nat.le_trans hu h.used)
      (stackWord_separate (count := 3) h.scratchArgs hj (by omega) (by decide) i hi)
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
      rfl rfl hf
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

theorem deriveSatisfiable : ∃ s, (Spec.Dsa.deriveKeyContract abi).pre s := by
  sig_implies_sat [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three]
    [deriveSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using deriveSatState

theorem derive_verified (M : Mont) (Sq : MontS)
    (hmx : (Generate.deriveKey Sq.mm M.mm).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target (Generate.deriveKey Sq.mm M.mm) (Spec.Dsa.deriveKeyContract abi) :=
  ⟨deriveCorrect M Sq hmx, deriveConstantTime M Sq, deriveSatisfiable⟩

end VG.Proof.Dsa.X86_64
