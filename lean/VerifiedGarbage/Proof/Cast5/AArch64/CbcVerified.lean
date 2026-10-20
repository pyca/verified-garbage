module

public import VerifiedGarbage.Proof.Cast5.AArch64.FbVerified
meta import VerifiedGarbage.Proof.Cast5.AArch64.FbVerified
import VerifiedGarbage.Proof.Modes.AArch64.CbcDecChained
meta import VerifiedGarbage.Proof.Modes.AArch64.CbcDecChained
import VerifiedGarbage.Proof.Modes.AArch64.CbcEncChained
meta import VerifiedGarbage.Proof.Modes.AArch64.CbcEncChained
import VerifiedGarbage.Proof.Cast5.AArch64.ModesLit
meta import VerifiedGarbage.Proof.Cast5.AArch64.ModesLit
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchConsts
meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratchConsts
import VerifiedGarbage.Impl.Aes.AArch64.Alloc
import VerifiedGarbage.Proof.Aes.Blocks
import VerifiedGarbage.Proof.AesCtr.Ctr32
import VerifiedGarbage.Proof.AesCtr.Spec
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Modes.AArch64.CbcEncLoop
import VerifiedGarbage.Proof.Modes.AArch64.CbcGroup
import VerifiedGarbage.Proof.Modes.AArch64.Copy
import VerifiedGarbage.Proof.Modes.AArch64.Counter
import VerifiedGarbage.Proof.Modes.AArch64.Steps
import VerifiedGarbage.Proof.Modes.AArch64.Unchain
import VerifiedGarbage.Proof.Modes.AArch64.Words
import VerifiedGarbage.Proof.Modes.Addr
import VerifiedGarbage.Proof.Modes.CbcNext
import VerifiedGarbage.Spec.Ctr.Contract
meta import VerifiedGarbage.Impl.Aes.AArch64.Alloc
meta import VerifiedGarbage.Proof.Aes.Blocks
meta import VerifiedGarbage.Proof.AesCtr.Ctr32
meta import VerifiedGarbage.Proof.AesCtr.Spec
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Mem
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Modes.AArch64.CbcEncLoop
meta import VerifiedGarbage.Proof.Modes.AArch64.CbcGroup
meta import VerifiedGarbage.Proof.Modes.AArch64.Copy
meta import VerifiedGarbage.Proof.Modes.AArch64.Counter
meta import VerifiedGarbage.Proof.Modes.AArch64.Steps
meta import VerifiedGarbage.Proof.Modes.AArch64.Unchain
meta import VerifiedGarbage.Proof.Modes.AArch64.Words
meta import VerifiedGarbage.Proof.Modes.Addr
meta import VerifiedGarbage.Proof.Modes.CbcNext
meta import VerifiedGarbage.Spec.Ctr.Contract

/-!
# CAST5-CBC on AArch64 meets its contracts

`cbcEncryptChained_wp`, `cbcDecryptChained_wp`: the modes' CBC that updates
the chaining value (`Proof.Modes.AArch64.cbcEncryptChained_wp` and
`cbcDecryptChained_wp`) over CAST5's core (`Mode.dirCoreSpec`), with the
working space at `x5`, under the feedback modes' precondition (`FPre`, as
the chaining value is written too). Encryption keeps the IV's address in
`x25`, which the core keeps (`Mode.crypt_keeps`), as those modes do. The
table of S-boxes is readable where the static `VG_CAST5_S1234` puts it and
holds the S-boxes. `cbcEncryptChained_verified`,
`cbcDecryptChained_verified`: each is correct and constant time, by the
taint analysis: the pointers, `rounds`, `n`, the stack pointer and the
table's address are public, and so is everything the code computes from
them, which it keeps in registers; the subkeys, the chaining value and the
data are secret. `cbcEncryptChained_framed` and `cbcDecryptChained_framed`
run them with their working space on the stack, zeroed on return: 112
bytes, the 13 words of the scratch buffer and 8 more (a frame is a multiple
of 16 bytes).
-/

@[expose] public section

namespace VG.Proof.Cast5.AArch64

open VG VG.AArch64 VG.Impl.Cast5.AArch64
open VG.Impl.Cast5 (s1234Sym s1234 ecbConsts)
open VG.Proof.Cast5.AArch64.Mode (dirCoreSpec TabAt SchedAt dirCore_bw)

/-- CBC encryption on AArch64 that updates the chaining value. -/
def cbcEncX : Contract isa where
  pre := FPre
  post s s' :=
    let cs := Spec.Cbc.encrypt (Spec.Cast5.cipher (keyOf s) (s.gpr .x1).toNat) (ivOf s) (dataOf s s.mem)
    dataOf s s'.mem = cs ∧ Spec.Aes.bytesAt s'.mem (s.gpr .x2) 8 = Spec.Cbc.next (ivOf s) cs
  pub := cbcPub

/-- CBC decryption on AArch64 that updates the chaining value. -/
def cbcDecX : Contract isa where
  pre := FPre
  post s s' :=
    dataOf s s'.mem = Spec.Cbc.decrypt (Spec.Cast5.invCipher (keyOf s) (s.gpr .x1).toNat) (ivOf s)
        (dataOf s s.mem) ∧
      Spec.Aes.bytesAt s'.mem (s.gpr .x2) 8 = Spec.Cbc.next (ivOf s) (dataOf s s.mem)
  pub := cbcPub

theorem cbcDecryptChained_wp {s₀ : State} (hp : cbcDecX.pre s₀) :
    WP isa cbcDecryptChained s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cbcDecX.post s₀ s' := by
  have hp' : FPre s₀ := hp
  have hwS : (⟨s₀.gpr .x5, 8 * 13⟩ : Region) ∈ s₀.wr := by rw [hp'.wr]; simp
  have e : 8 * (dirCore false).bw * (s₀.gpr .x4).toNat = (s₀.gpr .x4).toNat * 8 := by
    rw [dirCore_bw, Nat.mul_one, Nat.mul_comm]
  refine WP.mono (Proof.Modes.AArch64.cbcDecryptChained_wp (dirCoreSpec false) (r := modeRegs)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .x5) (P := s₀.gpr .x2) (D := s₀.gpr .x3) (n := (s₀.gpr .x4).toNat)
    (k := (keyOf s₀, (s₀.gpr .x1).toNat)) rfl rfl rfl rfl ⟨hwS, hp'.fS⟩
    (by rw [hp'.wr]; simp) (by rw [e, hp'.wr]; simp) hp'.dVS (by rw [e]; exact hp'.dDS) (by rw [e]; exact hp'.dVD)
    (by rw [e]; exact hp'.fD)
    ⟨⟨s₀.gpr .x0, rfl, rfl, hp'.schedAt, fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hp'.dKS
        · exact hp'.dKV⟩,
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], hp'.rounds, hp'.tabAt, fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hp'.dTS
        · exact hp'.dTV⟩)
    fun s' ⟨hcs, hdata, hiv, _, _, _⟩ => ⟨hcs, ?_⟩
  rw [dirCore_bw, Nat.mul_one, blocksOf_eq, blocksOf_eq] at hdata
  rw [dirCore_bw, Nat.mul_one, blocksOf_eq] at hiv
  exact ⟨hdata, hiv⟩

theorem cbcEncryptChained_wp {s₀ : State} (hp : cbcEncX.pre s₀) :
    WP isa cbcEncryptChained s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cbcEncX.post s₀ s' := by
  have hp' : FPre s₀ := hp
  have hwS : (⟨s₀.gpr .x5, 8 * 13⟩ : Region) ∈ s₀.wr := by rw [hp'.wr]; simp
  have e : 8 * (dirCore true).bw * (s₀.gpr .x4).toNat = (s₀.gpr .x4).toNat * 8 := by
    rw [dirCore_bw, Nat.mul_one, Nat.mul_comm]
  refine WP.mono (Proof.Modes.AArch64.cbcEncryptChained_wp (dirCoreSpec true) (r := modeRegs)
    ⟨by decide, by decide, by decide⟩ (by decide) (ivR := .x25)
    ⟨by decide, by decide, by decide, by decide, by decide⟩
    (B := s₀.gpr .x5) (P := s₀.gpr .x2) (D := s₀.gpr .x3) (n := (s₀.gpr .x4).toNat)
    (k := (keyOf s₀, (s₀.gpr .x1).toNat)) rfl rfl rfl rfl ⟨hwS, hp'.fS⟩
    (by rw [hp'.wr]; simp) (by rw [e, hp'.wr]; simp) hp'.dVS (by rw [e]; exact hp'.dDS) (by rw [e]; exact hp'.dVD)
    (by rw [e]; exact hp'.fD)
    ⟨⟨s₀.gpr .x0, rfl, rfl, hp'.schedAt, fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hp'.dKS
        · rw [e]; exact hp'.dKD⟩,
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], hp'.rounds, hp'.tabAt, fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hp'.dTS
        · rw [e]; exact hp'.dTD⟩ Mode.crypt_keeps)
    fun s' ⟨hcs, hdata, hiv, _, _, _⟩ => ⟨hcs, ?_⟩
  rw [dirCore_bw, Nat.mul_one, blocksOf_eq, blocksOf_eq] at hdata
  rw [dirCore_bw, Nat.mul_one, blocksOf_eq] at hiv
  exact ⟨hdata, hiv⟩

/-! ## Constant time -/

theorem cbcEncryptChained_ct : ConstantTime isa cbcEncX.pre cbcEncX.pub cbcEncryptChained :=
  VG.Taint.constantTime (A := taintS [s1234Sym]) (Taint.ofRegs modePub) fbTaint_agree (by taint_decide)

theorem cbcDecryptChained_ct : ConstantTime isa cbcDecX.pre cbcDecX.pub cbcDecryptChained :=
  VG.Taint.constantTime (A := taintS [s1234Sym]) (Taint.ofRegs modePub) fbTaint_agree (by taint_decide)

/-! ## The contracts -/

/-- CBC's chained contract with the working space as a sixth argument, under
the calling convention with the table. -/
abbrev cbcK (post : Spec.Cast5.cbcChainedSig.Post AArch64.abi.ptrBits) : Contract isa :=
  Proof.Cast5.modeScratchContract (AArch64.abi.withConsts ecbConsts) Spec.Cast5.cbcChainedSig 13
    (Proof.Cast5.cbcChainedPre AArch64.abi.ptrBits) post

/-- A state satisfying the precondition: one block, 16 rounds. -/
def cbcSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 16 | .x2 => 0x2000 | .x3 => 0x3000 | .x4 => 1 | .x5 => 0x4000 | _ => 0
  sp := 0x8000
  mem := ecbSatMem
  rd := [⟨0x1000, 128⟩, ⟨0x100000, 4096⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 8⟩, ⟨0x4000, 104⟩]
  syms _ := 0x100000

theorem cbc_implies {postX : State → State → Prop} {post : Spec.Cast5.cbcChainedSig.Post AArch64.abi.ptrBits}
    (hpost : ∀ s s', postX s s' → (cbcK post).post s s') :
    ({ pre := FPre, post := postX, pub := cbcPub } : Contract isa).Implies (cbcK post) where
  pre s h := by
    sig_pre [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Spec.Cast5.cbcChainedSig,
      Proof.Cast5.cbcChainedPre, AArch64.abi, AArch64.argRegs, ecbConsts_eq, Abi.withConsts, Abi.constRegions,
      Abi.constsHeld, stackBelow, s1234_length, Curry.withScratch] at h
    obtain ⟨hdr, hheld, hfit, hdw, htk, hw, dKV, dKD, dKS, dVD, dVS, dDS, fK, -, fD, fS, hr⟩ := h
    refine ⟨?_, hw, hheld, hfit, hdw _ (by rw [hw]; exact List.mem_cons_self),
      hdw _ (by rw [hw]; exact List.mem_cons_of_mem _ List.mem_cons_self),
      hdw _ (by rw [hw]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)), dKV, dKD, dKS,
      dVD, dVS, dDS, fK, fD, fS, hr⟩
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, htk, hdr]
    rfl
  post s s' _ hq := hpost s s' hq
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Spec.Cast5.cbcChainedSig,
      AArch64.abi, AArch64.argRegs, ecbConsts_eq, Abi.withConsts, Curry.withScratch] at h
    obtain ⟨hsp, hsy, h1, h2, h3, h4, h5, h6⟩ := h
    exact ⟨h1, h2, h3, h4, h5, h6, hsp, hsy⟩
  sat := ⟨cbcSat, by
    generalize e : cbcSat = s
    sig_pre [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Spec.Cast5.cbcChainedSig,
      Proof.Cast5.cbcChainedPre, AArch64.abi, AArch64.argRegs, ecbConsts_eq, Abi.withConsts, Abi.constRegions,
      Abi.constsHeld, stackBelow, s1234_length, Curry.withScratch]
    subst s
    refine ⟨rfl, ecbSatMem_held, by decide, ?_, ?_⟩
    · intro r hr
      change r ∈ [(⟨0x2000, 8⟩ : Region), ⟨0x3000, 8⟩, ⟨0x4000, 104⟩] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
    · repeat' apply And.intro
      all_goals first | rfl | decide | exact Or.inr rfl | exact Region.disjoint_of_sep (by decide)⟩

theorem cbcEncryptChained_verified :
    Verified AArch64.target cbcEncryptChained (cbcK (Proof.Cast5.cbcEncChainedPost AArch64.abi.ptrBits)) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs (rs := [.x30]) (cbcEncryptChained_wp hs) (by lit_decide)
        (by lit_decide)
      exact ⟨t, s', he, abi_of he h₁ h₃ (by lit_decide), h₂⟩)
    cbcEncryptChained_ct (cbc_implies fun s s' h => by
      sig_post [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Spec.Cast5.cbcChainedSig,
        Proof.Cast5.cbcEncChainedPost, AArch64.abi, AArch64.argRegs, ecbConsts_eq, Abi.withConsts, Curry.withScratch]
      exact h)

theorem cbcDecryptChained_verified :
    Verified AArch64.target cbcDecryptChained (cbcK (Proof.Cast5.cbcDecChainedPost AArch64.abi.ptrBits)) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs (rs := [.x30]) (cbcDecryptChained_wp hs) (by lit_decide)
        (by lit_decide)
      exact ⟨t, s', he, abi_of he h₁ h₃ (by lit_decide), h₂⟩)
    cbcDecryptChained_ct (cbc_implies fun s s' h => by
      sig_post [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Spec.Cast5.cbcChainedSig,
        Proof.Cast5.cbcDecChainedPost, AArch64.abi, AArch64.argRegs, ecbConsts_eq, Abi.withConsts, Curry.withScratch]
      exact h)

/-! ## The functions with their working space on the stack -/

/-- A state satisfying the functions' precondition, with 112 bytes of stack. -/
def cbcFrameSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 16 | .x2 => 0x2000 | .x3 => 0x3000 | .x4 => 1 | _ => 0
  sp := 0x8000
  mem := ecbSatMem
  rd := [⟨0x1000, 128⟩, ⟨0x100000, 4096⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 8⟩]
  syms _ := 0x100000

theorem cbcFrame_sat (post : Spec.Cast5.cbcChainedSig.Post AArch64.abi.ptrBits) :
    ∃ s, (Spec.Cast5.cbcChainedSig.contract (AArch64.abi.withConsts ecbConsts) (Proof.Cast5.cbcChainedPre AArch64.abi.ptrBits)
      post true (0 + 112)).pre s := by
  refine ⟨cbcFrameSat, ?_⟩
  generalize e : cbcFrameSat = s
  sig_pre [Spec.Cast5.cbcChainedSig, Proof.Cast5.cbcChainedPre, AArch64.abi, AArch64.argRegs, ecbConsts_eq, Abi.withConsts,
    Abi.constRegions, Abi.constsHeld, stackBelow, s1234_length]
  subst s
  refine ⟨by decide, rfl, ecbSatMem_held, by decide, ?_, ?_⟩
  · intro r hr
    change r ∈ [(⟨0x2000, 8⟩ : Region), ⟨0x3000, 8⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | rfl | decide | exact Or.inr rfl | exact Region.disjoint_of_sep (by decide)

/-- `cbcEncryptChained` with its working space on the stack. -/
theorem cbcEncryptChained_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 112 .x5 13 cbcEncryptChained)
      (Spec.Cast5.cbcEncryptChainedContract (AArch64.abi.withConsts ecbConsts) 112) :=
  AArch64.Verified.stackScratchWipedC (c₀ := (s1234Sym, s1234)) (cs := []) (sig := Spec.Cast5.cbcChainedSig)
    (nm := "scratch") (e := .u64) (n := 13) (pre := Proof.Cast5.cbcChainedPre AArch64.abi.ptrBits)
    (post := Proof.Cast5.cbcEncChainedPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 112)
    cbcEncryptChained_verified (by decide) (by decide) (by decide) (Proof.Cast5.cbcEncChainedPostOut_local _)
    (cbcFrame_sat _)

/-- `cbcDecryptChained` with its working space on the stack. -/
theorem cbcDecryptChained_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 112 .x5 13 cbcDecryptChained)
      (Spec.Cast5.cbcDecryptChainedContract (AArch64.abi.withConsts ecbConsts) 112) :=
  AArch64.Verified.stackScratchWipedC (c₀ := (s1234Sym, s1234)) (cs := []) (sig := Spec.Cast5.cbcChainedSig)
    (nm := "scratch") (e := .u64) (n := 13) (pre := Proof.Cast5.cbcChainedPre AArch64.abi.ptrBits)
    (post := Proof.Cast5.cbcDecChainedPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 112)
    cbcDecryptChained_verified (by decide) (by decide) (by decide) (Proof.Cast5.cbcDecChainedPostOut_local _)
    (cbcFrame_sat _)

end VG.Proof.Cast5.AArch64
