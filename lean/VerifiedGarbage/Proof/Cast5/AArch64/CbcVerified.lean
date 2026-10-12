import VerifiedGarbage.Proof.Cast5.AArch64.ModeCore
import VerifiedGarbage.Proof.Cast5.AArch64.ModesLit
import VerifiedGarbage.Proof.Cast5.AArch64.EcbVerified
import VerifiedGarbage.Proof.Cast5.ModeScratch
import VerifiedGarbage.Proof.Modes.AArch64.CbcDecrypt
import VerifiedGarbage.Proof.Modes.AArch64.CbcEncrypt
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchConsts

/-!
# CAST5-CBC on AArch64 meets its contracts

`cbcEncrypt_wp`, `cbcDecrypt_wp`: the modes' CBC encryption and decryption
(`Proof.Modes.AArch64.cbcEncrypt_wp` and `cbcDecrypt_wp`) over CAST5's core
(`Mode.dirCoreSpec`), with the working space at `x5`. The table of S-boxes is
readable where the static `VG_CAST5_S1234` puts it and holds the S-boxes.
`cbcEncrypt_verified`, `cbcDecrypt_verified`: each is correct and constant
time, by the taint analysis: the pointers, `rounds`, `n`, the stack pointer
and the table's address are public, and so is everything the code computes
from them, which it keeps in registers; the subkeys, the chaining value and
the data are secret. `cbcEncrypt_framed` and `cbcDecrypt_framed` run them
with their working space on the stack, zeroed on return: 112 bytes, the 13
words of the scratch buffer and 8 more (a frame is a multiple of 16 bytes).
-/

namespace VG.Proof.Cast5.AArch64

open VG VG.AArch64 VG.Impl.Cast5.AArch64
open VG.Impl.Cast5 (s1234Sym s1234 ecbConsts)
open VG.Proof.Cast5 (Held)
open VG.Proof.Cast5.AArch64.Mode (dirCoreSpec TabAt SchedAt dirCore_bw)

/-- The `n` blocks at `p`, as the modes read them. -/
theorem blocksOf_eq (m : Mem) (p : Addr) (n : Nat) :
    VG.Proof.Modes.blocksOf 8 m p n = Spec.Cast5.cbcBlocksAt m p n :=
  (Proof.Cast5.cbcBlocksAt_eq m p n).symm

/-- The facts of CBC's precondition on this target, with the working space at
`x5`. -/
structure CPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .x0, 128⟩, ⟨s.gpr .x2, 8⟩, ⟨s.syms s1234Sym, 4096⟩]
  wr : s.wr = [⟨s.gpr .x3, (s.gpr .x4).toNat * 8⟩, ⟨s.gpr .x5, 104⟩]
  held : ∀ i < 512, s.mem.readW (s.syms s1234Sym + BitVec.ofNat 64 (8 * i)) 64 = s1234.getD i 0
  fitT : (s.syms s1234Sym).toNat + 4096 ≤ 2 ^ 64
  dTD : Region.Disjoint ⟨s.syms s1234Sym, 4096⟩ ⟨s.gpr .x3, (s.gpr .x4).toNat * 8⟩
  dTS : Region.Disjoint ⟨s.syms s1234Sym, 4096⟩ ⟨s.gpr .x5, 104⟩
  dKD : Region.Disjoint ⟨s.gpr .x0, 128⟩ ⟨s.gpr .x3, (s.gpr .x4).toNat * 8⟩
  dKS : Region.Disjoint ⟨s.gpr .x0, 128⟩ ⟨s.gpr .x5, 104⟩
  dVD : Region.Disjoint ⟨s.gpr .x2, 8⟩ ⟨s.gpr .x3, (s.gpr .x4).toNat * 8⟩
  dVS : Region.Disjoint ⟨s.gpr .x2, 8⟩ ⟨s.gpr .x5, 104⟩
  dDS : Region.Disjoint ⟨s.gpr .x3, (s.gpr .x4).toNat * 8⟩ ⟨s.gpr .x5, 104⟩
  fK : (s.gpr .x0).toNat + 128 ≤ 2 ^ 64
  fD : (s.gpr .x3).toNat + (s.gpr .x4).toNat * 8 ≤ 2 ^ 64
  fS : (s.gpr .x5).toNat + 104 ≤ 2 ^ 64
  rounds : (s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 16

/-- The data, in blocks. -/
abbrev dataOf (s : State) (m : Mem) : List (List Byte) :=
  Spec.Cast5.cbcBlocksAt m (s.gpr .x3) (s.gpr .x4).toNat
/-- The chaining value. -/
abbrev ivOf (s : State) : List Byte := Spec.Aes.bytesAt s.mem (s.gpr .x2) 8
/-- The subkeys. -/
abbrev keyOf (s : State) : Spec.Cast5.Schedule := Spec.Cast5.scheduleAt s.mem (s.gpr .x0)

/-- The public arguments and the table's address. -/
def cbcPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
    s₁.sp = s₂.sp ∧ s₁.syms s1234Sym = s₂.syms s1234Sym

/-- CBC encryption on AArch64 with its working space at `x5`. -/
def cbcEncX : Contract isa where
  pre := CPre
  post s s' := dataOf s s'.mem = Spec.Cbc.encrypt (Spec.Cast5.cipher (keyOf s) (s.gpr .x1).toNat) (ivOf s)
    (dataOf s s.mem)
  pub := cbcPub

/-- CBC decryption on AArch64 with its working space at `x5`. -/
def cbcDecX : Contract isa where
  pre := CPre
  post s s' := dataOf s s'.mem = Spec.Cbc.decrypt (Spec.Cast5.invCipher (keyOf s) (s.gpr .x1).toNat) (ivOf s)
    (dataOf s s.mem)
  pub := cbcPub

/-- The table, as the core needs it. -/
theorem CPre.tabAt {s : State} (h : CPre s) : TabAt s :=
  ⟨by rw [h.rd]; simp, h.fitT, fun i hi => h.held i (by rw [s1234_length] at hi; exact hi), fun w hw => by
    rw [h.wr] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact h.dTD
    · exact h.dTS⟩

/-- The subkeys, as the core needs them. -/
theorem CPre.schedAt {s : State} (h : CPre s) : SchedAt s (s.gpr .x0) :=
  ⟨by rw [h.rd]; simp, h.fK, fun w hw => by
    rw [h.wr] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact h.dKD
    · exact h.dKS⟩

theorem CPre.x1 {s : State} (_ : CPre s) : s.gpr .x1 = BitVec.ofNat 64 (s.gpr .x1).toNat := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The key's arguments, apart from the regions `rs`. -/
theorem CPre.keyArgs {s : State} (h : CPre s) {rs : List Region}
    (hK : ∀ r ∈ rs, Region.Disjoint ⟨s.gpr .x0, 128⟩ r)
    (hT : ∀ r ∈ rs, Region.Disjoint ⟨s.syms s1234Sym, 4096⟩ r) :
    Mode.ModeKeyArgs s rs (keyOf s, (s.gpr .x1).toNat) :=
  ⟨⟨s.gpr .x0, rfl, rfl, h.schedAt, hK⟩, h.x1, h.rounds, h.tabAt, hT⟩

theorem cbcDecrypt_wp {s₀ : State} (hp : cbcDecX.pre s₀) :
    WP isa cbcDecrypt s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cbcDecX.post s₀ s' := by
  have hp' : CPre s₀ := hp
  have hwS : (⟨s₀.gpr .x5, 8 * 13⟩ : Region) ∈ s₀.wr := by rw [hp'.wr]; simp
  have hwD : (⟨s₀.gpr .x3, 8 * 1 * (s₀.gpr .x4).toNat⟩ : Region) ∈ s₀.wr := by
    rw [hp'.wr, Nat.mul_one, Nat.mul_comm]; simp
  have e : 8 * (dirCore false).bw * (s₀.gpr .x4).toNat = (s₀.gpr .x4).toNat * 8 := by
    rw [dirCore_bw, Nat.mul_one, Nat.mul_comm]
  refine WP.mono (Proof.Modes.AArch64.cbcDecrypt_wp (dirCoreSpec false) (r := modeRegs)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .x5) (P := s₀.gpr .x2) (D := s₀.gpr .x3) (n := (s₀.gpr .x4).toNat)
    (k := (keyOf s₀, (s₀.gpr .x1).toNat)) rfl rfl rfl rfl ⟨hwS, hp'.fS⟩
    (by rw [hp'.rd]; simp) hwD hp'.dVS (by rw [e]; exact hp'.dDS) (by rw [e]; exact hp'.fD)
    (hp'.keyArgs (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp'.dKS)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp'.dTS)))
    fun s' ⟨hcs, hdata, _, _, _⟩ => ⟨hcs, ?_⟩
  rw [dirCore_bw, Nat.mul_one, blocksOf_eq, blocksOf_eq] at hdata
  exact hdata

theorem cbcEncrypt_wp {s₀ : State} (hp : cbcEncX.pre s₀) :
    WP isa cbcEncrypt s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cbcEncX.post s₀ s' := by
  have hp' : CPre s₀ := hp
  have hwS : (⟨s₀.gpr .x5, 8 * 13⟩ : Region) ∈ s₀.wr := by rw [hp'.wr]; simp
  have hwD : (⟨s₀.gpr .x3, 8 * 1 * (s₀.gpr .x4).toNat⟩ : Region) ∈ s₀.wr := by
    rw [hp'.wr, Nat.mul_one, Nat.mul_comm]; simp
  have e : 8 * (dirCore true).bw * (s₀.gpr .x4).toNat = (s₀.gpr .x4).toNat * 8 := by
    rw [dirCore_bw, Nat.mul_one, Nat.mul_comm]
  refine WP.mono (Proof.Modes.AArch64.cbcEncrypt_wp (dirCoreSpec true) (r := modeRegs)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .x5) (P := s₀.gpr .x2) (D := s₀.gpr .x3) (n := (s₀.gpr .x4).toNat)
    (k := (keyOf s₀, (s₀.gpr .x1).toNat)) rfl rfl rfl rfl ⟨hwS, hp'.fS⟩
    (by rw [hp'.rd]; simp) hwD hp'.dVS (by rw [e]; exact hp'.dDS) (by rw [e]; exact hp'.dVD)
    (by rw [e]; exact hp'.fD)
    (hp'.keyArgs (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hp'.dKS
        · rw [e]; exact hp'.dKD)
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hp'.dTS
        · rw [e]; exact hp'.dTD)))
    fun s' ⟨hcs, hdata, _, _, _⟩ => ⟨hcs, ?_⟩
  rw [dirCore_bw, Nat.mul_one, blocksOf_eq, blocksOf_eq] at hdata
  exact hdata

/-! ## Constant time -/

/-- The public registers. -/
def modePub : List Reg := [.x0, .x1, .x2, .x3, .x4, .x5]

theorem cbcTaint_agree (s₁ s₂ : State) (_ : CPre s₁) (_ : CPre s₂) (hp : cbcPub s₁ s₂) :
    VG.AArch64.Taint.AgreeS [s1234Sym] (Taint.ofRegs modePub) s₁ s₂ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, hsp, hsy⟩ := hp
  refine ⟨⟨hsp, fun r hr => ?_⟩, fun n hn => ?_⟩
  · simp only [VG.AArch64.Taint.mem_ofRegs, modePub, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h1, h2, h3, h4, h5, h6]
  · simp only [List.mem_singleton] at hn
    subst hn
    exact hsy

theorem cbcEncrypt_ct : ConstantTime isa cbcEncX.pre cbcEncX.pub cbcEncrypt :=
  VG.Taint.constantTime (A := taintS [s1234Sym]) (Taint.ofRegs modePub) cbcTaint_agree (by taint_decide)

theorem cbcDecrypt_ct : ConstantTime isa cbcDecX.pre cbcDecX.pub cbcDecrypt :=
  VG.Taint.constantTime (A := taintS [s1234Sym]) (Taint.ofRegs modePub) cbcTaint_agree (by taint_decide)

/-- The callee-saved registers and the rest of the ABI, from what a mode
keeps. -/
theorem abi_of {c : Prog isa} {s s' : State} {t : List Leak} (he : Exec isa c s t s')
    (h₁ : ∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19))
    (h₃ : ∀ r ∈ [Reg.x30], s'.gpr r = s.gpr r) (hv : c.allInstrs keepsV = true) : abiPreserved s s' :=
  ⟨Modes.AArch64.preserved_of h₁ h₃, Exec.sp he, Exec.preservedV he hv⟩

/-! ## The contracts -/

/-- CBC's contract with the working space as a sixth argument, under the
calling convention with the table. -/
abbrev cbcK (post : Spec.Cast5.cbcSig.Post AArch64.abi.ptrBits) : Contract isa :=
  Proof.Cast5.modeScratchContract (AArch64.abi.withConsts ecbConsts) Spec.Cast5.cbcSig 13
    (Spec.Cast5.cbcPre AArch64.abi.ptrBits) post

/-- A state satisfying the precondition: one block, 16 rounds. -/
def cbcSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 16 | .x2 => 0x2000 | .x3 => 0x3000 | .x4 => 1 | .x5 => 0x4000 | _ => 0
  sp := 0x8000
  mem := ecbSatMem
  rd := [⟨0x1000, 128⟩, ⟨0x2000, 8⟩, ⟨0x100000, 4096⟩]
  wr := [⟨0x3000, 8⟩, ⟨0x4000, 104⟩]
  syms _ := 0x100000

theorem cbc_implies {postX : State → State → Prop} {post : Spec.Cast5.cbcSig.Post AArch64.abi.ptrBits}
    (hpost : ∀ s s', postX s s' → (cbcK post).post s s') :
    ({ pre := CPre, post := postX, pub := cbcPub } : Contract isa).Implies (cbcK post) where
  pre s h := by
    sig_pre [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Spec.Cast5.cbcSig,
      Spec.Cast5.cbcPre, AArch64.abi, AArch64.argRegs, ecbConsts_eq, Abi.withConsts, Abi.constRegions,
      Abi.constsHeld, stackBelow, s1234_length, Curry.withScratch] at h
    obtain ⟨hdr, hheld, hfit, hdw, htk, hw, dKD, dKS, dVD, dVS, dDS, fK, -, fD, fS, hr⟩ := h
    refine ⟨?_, hw, hheld, hfit, hdw _ (by rw [hw]; exact List.mem_cons_self),
      hdw _ (by rw [hw]; exact List.mem_cons_of_mem _ List.mem_cons_self), dKD, dKS, dVD, dVS, dDS, fK,
      fD, fS, hr⟩
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, htk, hdr]
    rfl
  post s s' _ hq := hpost s s' hq
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Spec.Cast5.cbcSig,
      AArch64.abi, AArch64.argRegs, ecbConsts_eq, Abi.withConsts, Curry.withScratch] at h
    obtain ⟨hsp, hsy, h1, h2, h3, h4, h5, h6⟩ := h
    exact ⟨h1, h2, h3, h4, h5, h6, hsp, hsy⟩
  sat := ⟨cbcSat, by
    generalize e : cbcSat = s
    sig_pre [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Spec.Cast5.cbcSig,
      Spec.Cast5.cbcPre, AArch64.abi, AArch64.argRegs, ecbConsts_eq, Abi.withConsts, Abi.constRegions,
      Abi.constsHeld, stackBelow, s1234_length, Curry.withScratch]
    subst s
    refine ⟨rfl, ecbSatMem_held, by decide, ?_, ?_⟩
    · intro r hr
      change r ∈ [(⟨0x3000, 8⟩ : Region), ⟨0x4000, 104⟩] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
    · repeat' apply And.intro
      all_goals first | rfl | decide | exact Or.inr rfl | exact Region.disjoint_of_sep (by decide)⟩

theorem cbcEncrypt_verified :
    Verified AArch64.target cbcEncrypt (cbcK (Proof.Cast5.cbcEncPost AArch64.abi.ptrBits)) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs (rs := [.x30]) (cbcEncrypt_wp hs) (by lit_decide)
        (by lit_decide)
      exact ⟨t, s', he, abi_of he h₁ h₃ (by lit_decide), h₂⟩)
    cbcEncrypt_ct (cbc_implies fun s s' h => by
      sig_post [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Spec.Cast5.cbcSig,
        Proof.Cast5.cbcEncPost, AArch64.abi, AArch64.argRegs, ecbConsts_eq, Abi.withConsts, Curry.withScratch]
      exact h)

theorem cbcDecrypt_verified :
    Verified AArch64.target cbcDecrypt (cbcK (Proof.Cast5.cbcDecPost AArch64.abi.ptrBits)) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs (rs := [.x30]) (cbcDecrypt_wp hs) (by lit_decide)
        (by lit_decide)
      exact ⟨t, s', he, abi_of he h₁ h₃ (by lit_decide), h₂⟩)
    cbcDecrypt_ct (cbc_implies fun s s' h => by
      sig_post [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Spec.Cast5.cbcSig,
        Proof.Cast5.cbcDecPost, AArch64.abi, AArch64.argRegs, ecbConsts_eq, Abi.withConsts, Curry.withScratch]
      exact h)

/-! ## The functions with their working space on the stack -/

/-- A state satisfying the functions' precondition, with 112 bytes of stack. -/
def cbcFrameSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 16 | .x2 => 0x2000 | .x3 => 0x3000 | .x4 => 1 | _ => 0
  sp := 0x8000
  mem := ecbSatMem
  rd := [⟨0x1000, 128⟩, ⟨0x2000, 8⟩, ⟨0x100000, 4096⟩]
  wr := [⟨0x3000, 8⟩]
  syms _ := 0x100000

theorem cbcFrame_sat (post : Spec.Cast5.cbcSig.Post AArch64.abi.ptrBits) :
    ∃ s, (Spec.Cast5.cbcSig.contract (AArch64.abi.withConsts ecbConsts) (Spec.Cast5.cbcPre AArch64.abi.ptrBits)
      post true (0 + 112)).pre s := by
  refine ⟨cbcFrameSat, ?_⟩
  generalize e : cbcFrameSat = s
  sig_pre [Spec.Cast5.cbcSig, Spec.Cast5.cbcPre, AArch64.abi, AArch64.argRegs, ecbConsts_eq, Abi.withConsts,
    Abi.constRegions, Abi.constsHeld, stackBelow, s1234_length]
  subst s
  refine ⟨by decide, rfl, ecbSatMem_held, by decide, ?_, ?_⟩
  · intro r hr
    change r ∈ [(⟨0x3000, 8⟩ : Region)] at hr
    simp only [List.mem_singleton] at hr; subst hr
    exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | rfl | decide | exact Or.inr rfl | exact Region.disjoint_of_sep (by decide)

/-- `cbcEncrypt` with its working space on the stack. -/
theorem cbcEncrypt_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 112 .x5 13 cbcEncrypt)
      (Spec.Cast5.cbcEncryptContract (AArch64.abi.withConsts ecbConsts) 112) :=
  AArch64.Verified.stackScratchWipedC (c₀ := (s1234Sym, s1234)) (cs := []) (sig := Spec.Cast5.cbcSig)
    (nm := "scratch") (e := .u64) (n := 13) (pre := Spec.Cast5.cbcPre AArch64.abi.ptrBits)
    (post := Proof.Cast5.cbcEncPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 112)
    cbcEncrypt_verified (by decide) (by decide) (by decide) (Proof.Cast5.cbcEncPostOut_local _) (cbcFrame_sat _)

/-- `cbcDecrypt` with its working space on the stack. -/
theorem cbcDecrypt_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 112 .x5 13 cbcDecrypt)
      (Spec.Cast5.cbcDecryptContract (AArch64.abi.withConsts ecbConsts) 112) :=
  AArch64.Verified.stackScratchWipedC (c₀ := (s1234Sym, s1234)) (cs := []) (sig := Spec.Cast5.cbcSig)
    (nm := "scratch") (e := .u64) (n := 13) (pre := Spec.Cast5.cbcPre AArch64.abi.ptrBits)
    (post := Proof.Cast5.cbcDecPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 112)
    cbcDecrypt_verified (by decide) (by decide) (by decide) (Proof.Cast5.cbcDecPostOut_local _) (cbcFrame_sat _)

end VG.Proof.Cast5.AArch64
