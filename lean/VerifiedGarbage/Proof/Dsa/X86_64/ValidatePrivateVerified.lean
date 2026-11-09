module

public import VerifiedGarbage.Proof.Dsa.X86_64.ValidatePrivateCT
public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
public import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
public import VerifiedGarbage.Proof.Dsa.X86_64.PrevalidatedSignVerified
-- Proofs inside exposed definitions (structure values) use these: Lean needs them public.
public import VerifiedGarbage.Proof.Bignum.Octets -- shake: keep
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Bignum.X86_64.CallPost
import VerifiedGarbage.Proof.Dsa.X86_64.ABIRegions
import VerifiedGarbage.Proof.Dsa.X86_64.ParametersVerified
import VerifiedGarbage.Proof.Dsa.X86_64.PrevalidatedVerified
import VerifiedGarbage.Proof.Dsa.X86_64.PublicSlices
import VerifiedGarbage.Proof.Rsa.X86_64.CallMont

/-! # The x86-64 DSA private-key validator verified against its contract

`validating_private_verified` is the program's proof;
`validating_private_call_verified` that of the code that calls the
Montgomery kernels, whose return addresses take eight bytes of stack. -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64 VG.Proof.Rsa.X86_64

structure PrivateABI (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩]
  wr : s.wr = [⟨s.gpr .r8, (s.gpr .r9).toNat * 8⟩]
  keyScratch : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat * 8⟩
  retKey : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  retScratch : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat * 8⟩
  keyBound : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64
  scratchBound : (s.gpr .r8).toNat + (s.gpr .r9).toNat * 8 ≤ 2 ^ 64
  lengths : Spec.Dsa.lengthsValid (s.gpr .rdx).toNat (s.gpr .rcx).toNat
  keyLength : (s.gpr .rsi).toNat = 3 * (s.gpr .rdx).toNat + 2 * (s.gpr .rcx).toNat
  scratchLength : Spec.Dsa.scratchWords (s.gpr .rdx).toNat ≤ (s.gpr .r9).toNat

theorem privateABI_of {s : State} (h : (Spec.Dsa.validatePrivateKeyContract abi).pre s) : PrivateABI s := by
  sig_pre [Spec.Dsa.validatePrivateKeyContract, Spec.Dsa.validatePrivateKeySig, abi, argRegs, stackArgs_zero] at h
  sig_split h
  constructor <;> with_reducible assumption

def PrivateABI.input {s : State} (h : PrivateABI s) : PrivateInput where
  base := s.gpr .r8
  pLen := (s.gpr .rdx).toNat
  qLen := (s.gpr .rcx).toNat
  key := Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat
  lengths := h.lengths
  keyLength := (bytesAt_length _ _ _).trans h.keyLength

theorem PrivateABI.used {s : State} (h : PrivateABI s) : usedBytes ≤ (s.gpr .r9).toNat * 8 := by
  have hl := h.lengths
  have hs := h.scratchLength
  unfold Spec.Dsa.lengthsValid at hl
  unfold Spec.Dsa.scratchWords at hs
  change 15712 ≤ _
  omega

theorem PrivateABI.pre {s : State} (h : PrivateABI s) : PrivatePre h.input s := by
  have hs : Scr s (s.gpr .r8) ((s.gpr .r9).toNat * 8) := Scr.of_mem (by rw [h.wr]; simp) h.scratchBound
  exact ⟨scratch_prefix hs h.used (by decide), rfl, (ofNat_toNat64 _).symm, (ofNat_toNat64 _).symm,
    source_shrink (src_of_region (by rw [h.rd]; simp) (Nat.le_of_lt (s.gpr .rsi).isLt) h.keyScratch) h.used⟩

def PrivateABI.call {s : State} (h : PrivateABI s) : PrivateCall := ⟨h.input, s, h.pre⟩

theorem privateGprPreserved {s t : State} (h : PrivateABI s) (hp : PrivatePost h.input s t) :
    gprPreserved s t := by
  obtain ⟨_, hsaved, hf, hk⟩ := hp
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
  · exact hf _ (Nat.le_trans h.used (out_scr h.retScratch
      (contains_byte (s.gpr .rsp) (i := i) (len := 8) hi (by decide))))

theorem privateSharedPost {s t : State} (h : PrivateABI s) (hp : PrivatePost h.input s t) :
    (Spec.Dsa.validatePrivateKeyContract abi).post s t := by
  sig_post [Spec.Dsa.validatePrivateKeyContract, Spec.Dsa.validatePrivateKeySig, abi, argRegs, stackArgs_zero]
  rw [hp.1]
  change _ = if Spec.Dsa.validatePrivateKeyBytes h.input.pLen h.input.qLen h.input.key = true then 1 else 0
  cases Spec.Dsa.validatePrivateKeyBytes h.input.pLen h.input.qLen h.input.key <;> rfl

theorem validatingPrivateCorrect (M : Mont) (Sq : MontS)
    (hmx : (PrevalidatedSign.validate Sq.mm M.mm).allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (h : (Spec.Dsa.validatePrivateKeyContract abi).pre s) :
    ∃ trace t, Exec isa (PrevalidatedSign.validate Sq.mm M.mm) s trace t ∧ abiPreserved s t ∧
      (Spec.Dsa.validatePrivateKeyContract abi).post s t := by
  have ha := privateABI_of h
  obtain ⟨trace, t, he, hp⟩ := privateMain_ok M Sq ha.pre
  exact ⟨trace, t, he, abiPreserved_of_exec hmx he (privateGprPreserved ha hp), privateSharedPost ha hp⟩

theorem privatePublicRelated {s₁ s₂ : State} (h₁ : PrivateABI s₁) (h₂ : PrivateABI s₂)
    (h : (Spec.Dsa.validatePrivateKeyContract abi).pub s₁ s₂) : Two PrivateStart s₁ s₂ := by
  sig_pub [Spec.Dsa.validatePrivateKeyContract, Spec.Dsa.validatePrivateKeySig, abi, argRegs,
    stackArgs_zero] at h
  obtain ⟨_, hl, hdi, _, hdx, hcx, h8, _⟩ := h
  have hpubl := (List.append_inj' hl (List.length_singleton.trans List.length_singleton.symm)).1
  have hb := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hpubl
  have hp : h₁.input.pLen = h₂.input.pLen := congrArg BitVec.toNat hdx
  have hq : h₁.input.qLen = h₂.input.qLen := congrArg BitVec.toNat hcx
  have hpub : h₁.input.key.take (3 * h₁.input.pLen + h₁.input.qLen) =
      h₂.input.key.take (3 * h₁.input.pLen + h₁.input.qLen) := by
    have hb' : h₁.input.key.take (3 * h₁.input.pLen + h₁.input.qLen) =
        h₂.input.key.take (3 * h₂.input.pLen + h₂.input.qLen) := hb
    rw [← hp, ← hq] at hb'
    exact hb'
  have hpb : h₁.input.components.p = h₂.input.components.p := by
    have he := prefix_component_eq (offset := 0) (len := h₁.input.pLen) hpub (by omega)
    simp only [List.drop_zero] at he
    change h₁.input.key.take h₁.input.pLen = h₂.input.key.take h₂.input.pLen
    rw [← hp]
    exact he
  have hqb : h₁.input.components.q = h₂.input.components.q := by
    have he := prefix_component_eq (offset := h₁.input.pLen) (len := h₁.input.qLen) hpub (by omega)
    change (h₁.input.key.drop h₁.input.pLen).take h₁.input.qLen =
      (h₂.input.key.drop h₂.input.pLen).take h₂.input.qLen
    rw [← hp, ← hq]
    exact he
  have hac : h₁.input.accepted = h₂.input.accepted := by
    unfold PrivateInput.accepted
    congr 1
  have hlayout : h₁.call.layout = h₂.call.layout := by
    change h₁.input.layout s₁ _ _ = h₂.input.layout s₂ _ _
    unfold PrivateInput.layout
    have hf : privateFieldValues s₁ h₁.input.accepted = privateFieldValues s₂ h₂.input.accepted := by
      funext f
      cases f <;> simp only [privateFieldValues, hdi, hdx, hcx, hac]
    congr 1
    · exact congrArg Spec.Dsa.decodeBE hpb
    · exact congrArg Spec.Dsa.decodeBE hqb
  exact ⟨h₂.call, ⟨h₁.call, ⟨hlayout, hpb, hqb⟩, rfl⟩, ⟨h₂.call, ⟨rfl, rfl, rfl⟩, rfl⟩⟩

theorem validatingPrivateConstantTime (M : Mont) (Sq : MontS) :
    ConstantTime isa (Spec.Dsa.validatePrivateKeyContract abi).pre
      (Spec.Dsa.validatePrivateKeyContract abi).pub (PrevalidatedSign.validate Sq.mm M.mm) := by
  intro s₁ s₂ trace₁ trace₂ t₁ t₂ h₁ h₂ hp e₁ e₂
  exact (privateMain_ct M Sq _ _ _ _ _ _
    (privatePublicRelated (privateABI_of h₁) (privateABI_of h₂) hp) e₁ e₂).1

/-- An ordinary 1024/160 call with disjoint buffers. The all-zero key is
allowed by the contract and rejected by the program. -/
def privateSatState : State where
  gpr r := match r with
    | .rdi => 0x2000 | .rsi => 424 | .rdx => 128 | .rcx => 20
    | .r8 => 0x8000 | .r9 => 2048 | .rsp => 0x10000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 424⟩]
  wr := [⟨0x8000, 16384⟩]

theorem validatingPrivateSatisfiable : ∃ s, (Spec.Dsa.validatePrivateKeyContract abi).pre s := by
  sig_implies_sat [Spec.Dsa.validatePrivateKeyContract, Spec.Dsa.validatePrivateKeySig, abi, argRegs,
    stackArgs_zero] [privateSatState, Mem.readW, Mem.read] using privateSatState

theorem validating_private_verified (M : Mont) (Sq : MontS)
    (hmx : (PrevalidatedSign.validate Sq.mm M.mm).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target (PrevalidatedSign.validate Sq.mm M.mm) (Spec.Dsa.validatePrivateKeyContract abi) :=
  ⟨validatingPrivateCorrect M Sq hmx, validatingPrivateConstantTime M Sq, validatingPrivateSatisfiable⟩

theorem validatingPrivate_implies8 :
    (Spec.Dsa.validatePrivateKeyContract abi).Implies (Spec.Dsa.validatePrivateKeyContract abi 8) where
  pre := by
    intro s h
    sig_pre [Spec.Dsa.validatePrivateKeyContract, Spec.Dsa.validatePrivateKeySig, abi, argRegs, stackArgs_zero,
      List.range, List.range.loop] at h
    sig_split h
    sig_pre [Spec.Dsa.validatePrivateKeyContract, Spec.Dsa.validatePrivateKeySig, abi, argRegs, stackArgs_zero,
      List.range, List.range.loop]
    sig_and_intros
    sig_close
  post := by sig_implies_post [Spec.Dsa.validatePrivateKeyContract, Spec.Dsa.validatePrivateKeySig, abi, argRegs,
    stackArgs_zero, List.range, List.range.loop]
  pub := by intro s t _ _ h; exact h
  sat := by
    sig_implies_sat [Spec.Dsa.validatePrivateKeyContract, Spec.Dsa.validatePrivateKeySig, abi, argRegs,
      stackArgs_zero, List.range, List.range.loop]
      [privateSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using privateSatState

theorem validatingPrivate_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64)
    (hp : (Spec.Dsa.validatePrivateKeyContract abi).post s b) :
    (Spec.Dsa.validatePrivateKeyContract abi).post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  sig_post [Spec.Dsa.validatePrivateKeyContract, Spec.Dsa.validatePrivateKeySig, abi, argRegs, stackArgs_zero,
    List.range, List.range.loop] at hp ⊢
  simpa only [State.patch_gpr] using hp

theorem validating_private_call_verified (M : Mont) (Sq : MontS) {c : Prog isa}
    (hc : c.InlineOk = true) (hin : c.inline = PrevalidatedSign.validate Sq.mm M.mm)
    (hmx : (PrevalidatedSign.validate Sq.mm M.mm).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target c (Spec.Dsa.validatePrivateKeyContract abi 8) :=
  Verified.of_inline_sig hc (hin ▸ validatingPrivateCorrect M Sq hmx) (hin ▸ validatingPrivateConstantTime M Sq)
    validatingPrivate_implies8 (fun _ h => Sig.clear_of_pre h) (fun _ _ _ _ h => Sig.rsp_of_pub h)
    (fun s b hv u _ _ hp => validatingPrivate_patch s b hv u hp)

end VG.Proof.Dsa.X86_64
