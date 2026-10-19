module

import VerifiedGarbage.Proof.Blowfish.AArch64.ModeCore
meta import VerifiedGarbage.Proof.Blowfish.AArch64.ModeCore
import VerifiedGarbage.Proof.Modes.AArch64.Fb
meta import VerifiedGarbage.Proof.Modes.AArch64.Fb
public import VerifiedGarbage.Proof.Blowfish.FbScratch
meta import VerifiedGarbage.Proof.Blowfish.FbScratch
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Blowfish.AArch64.KeepV
public import VerifiedGarbage.Proof.Blowfish.AArch64.ModesLit
public import VerifiedGarbage.Proof.Modes.Fb
public import VerifiedGarbage.Spec.Blowfish.Cfb
public import VerifiedGarbage.Impl.StackScratch.AArch64
meta import VerifiedGarbage.Proof.Framework.Contract
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Impl.Aes.AArch64.Alloc
import VerifiedGarbage.Proof.Aes.Blocks
import VerifiedGarbage.Proof.AesCtr.Ctr32
import VerifiedGarbage.Proof.AesCtr.Spec
import VerifiedGarbage.Proof.Blowfish.AArch64.Ecb
import VerifiedGarbage.Proof.Blowfish.AArch64.EcbMain
import VerifiedGarbage.Proof.Blowfish.AArch64.Exec
import VerifiedGarbage.Proof.Blowfish.AArch64.Lanes
import VerifiedGarbage.Proof.Blowfish.Blocks
import VerifiedGarbage.Proof.Blowfish.Schedule
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
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
import VerifiedGarbage.Spec.Blowfish.Contract
import VerifiedGarbage.Spec.Ctr.Contract
meta import VerifiedGarbage.Impl.Aes.AArch64.Alloc
meta import VerifiedGarbage.Proof.Aes.Blocks
meta import VerifiedGarbage.Proof.AesCtr.Ctr32
meta import VerifiedGarbage.Proof.AesCtr.Spec
meta import VerifiedGarbage.Proof.Blowfish.AArch64.Ecb
meta import VerifiedGarbage.Proof.Blowfish.AArch64.EcbMain
meta import VerifiedGarbage.Proof.Blowfish.AArch64.Exec
meta import VerifiedGarbage.Proof.Blowfish.AArch64.Lanes
meta import VerifiedGarbage.Proof.Blowfish.Blocks
meta import VerifiedGarbage.Proof.Blowfish.Schedule
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Mem
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd
meta import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
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
meta import VerifiedGarbage.Spec.Blowfish.Cfb
meta import VerifiedGarbage.Spec.Blowfish.Contract
meta import VerifiedGarbage.Spec.Ctr.Contract

/-!
# Blowfish-OFB and Blowfish-CFB64 on AArch64 meet their contracts

`ofb_wp`, `cfbEncrypt_wp`, `cfbDecrypt_wp`: the modes' OFB and CFB
(`Proof.Modes.AArch64.fb_wp`) over Blowfish's encryption core
(`dirCoreSpec true`), with the IV's address in `x25`, which the core never
writes (`crypt_keeps`), and the specification's results
(`Proof.Modes.ofb_of`, …). The low halves of `v8`–`v15` are kept because
the modes' code writes no vector register and every run of `crypt` keeps
them (`vKeep_of_vSafeBut`, `crypt_vKeep`). `ofb_verified`, …: each is
correct and constant time, by the taint analysis: the pointers, `n` and the
stack pointer are public, and so is everything the code computes from them,
which it keeps in registers; the IV is secret. `ofb_framed`, … run them with
their working space on the stack, zeroed on return: 224 bytes, the 28 words
of the scratch buffer.
-/

@[expose] public section

namespace VG.Proof.Blowfish.AArch64

open VG VG.AArch64 VG.Impl.Blowfish.AArch64

/-- The precondition of the feedback modes on AArch64, with the data `len`
bytes long and the working space at `x4`. -/
def fbPre (len : State → Nat) (s : State) : Prop :=
  let sched : Region := ⟨s.gpr .x0, 4168⟩
  let iv : Region := ⟨s.gpr .x1, 8⟩
  let data : Region := ⟨s.gpr .x2, len s⟩
  let scratch : Region := ⟨s.gpr .x4, 8 * 28⟩
  s.rd = [sched] ∧ s.wr = [iv, data, scratch] ∧ sched.Disjoint iv ∧ sched.Disjoint data ∧
    sched.Disjoint scratch ∧ iv.Disjoint data ∧ iv.Disjoint scratch ∧ data.Disjoint scratch ∧
    (s.gpr .x0).toNat + 4168 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 8 ≤ 2 ^ 64 ∧
    (s.gpr .x2).toNat + len s ≤ 2 ^ 64 ∧ (s.gpr .x4).toNat + 8 * 28 ≤ 2 ^ 64

/-- The public arguments. -/
def fbPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

/-- `n` blocks. -/
abbrev blkLen (s : State) : Nat := 8 * (s.gpr .x3).toNat

/-- The schedule, IV and data of `s`'s arguments. -/
abbrev ciphOf (s : State) : Spec.Cbc.Cipher := Spec.Blowfish.cipher (Spec.Blowfish.scheduleAt s.mem (s.gpr .x0))
abbrev ivOf (s : State) : List Byte := Spec.Aes.bytesAt s.mem (s.gpr .x1) 8
abbrev blocksOf (s : State) (m : Mem) : List (List Byte) := Spec.Blowfish.cbcBlocksAt m (s.gpr .x2) (s.gpr .x3).toNat

def ofbAArch64 : Contract isa where
  pre := fbPre blkLen
  post s s' := blocksOf s s'.mem = Spec.Ofb.crypt (ciphOf s) (ivOf s) (blocksOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .x1) 8 = Spec.Ofb.next (ciphOf s) (ivOf s) (s.gpr .x3).toNat
  pub := fbPub

def cfbEncAArch64 : Contract isa where
  pre := fbPre blkLen
  post s s' := blocksOf s s'.mem = Spec.Cfb.encrypt (ciphOf s) (ivOf s) (blocksOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .x1) 8 =
      Spec.Cbc.next (ivOf s) (Spec.Cfb.encrypt (ciphOf s) (ivOf s) (blocksOf s s.mem))
  pub := fbPub

def cfbDecAArch64 : Contract isa where
  pre := fbPre blkLen
  post s s' := blocksOf s s'.mem = Spec.Cfb.decrypt (ciphOf s) (ivOf s) (blocksOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .x1) 8 = Spec.Cbc.next (ivOf s) (blocksOf s s.mem)
  pub := fbPub

/-- What the modes' OFB and CFB give, for a mode `mo`: the data and the
IV as `fbOut` and `fbIn`, keeping the callee-saved registers. -/
theorem fb_wp' (mo : Impl.Modes.FbMode) {s₀ : State} (hp : fbPre blkLen s₀) :
    WP isa ((dirCore true).fb mo modeRegs .x25) s₀ fun s' =>
      (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
        s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧
      Modes.blocksOf 8 s'.mem (s₀.gpr .x2) (s₀.gpr .x3).toNat =
        (List.range (s₀.gpr .x3).toNat).map (Modes.fbOut mo 8 (ciphOf s₀) s₀.mem (s₀.gpr .x2) (ivOf s₀)) ∧
      Spec.Aes.bytesAt s'.mem (s₀.gpr .x1) 8 =
        Modes.fbIn mo 8 (ciphOf s₀) s₀.mem (s₀.gpr .x2) (ivOf s₀) (s₀.gpr .x3).toNat := by
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .x4, 8 * 28⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.AArch64.fb_wp (dirCoreSpec true) mo (r := modeRegs)
    ⟨by decide, by decide, by decide⟩ (by decide) (ivR := .x25)
    ⟨by decide, by decide, by decide, by decide, by decide⟩
    (B := s₀.gpr .x4) (P := s₀.gpr .x1) (D := s₀.gpr .x2) (n := (s₀.gpr .x3).toNat)
    (k := Spec.Blowfish.scheduleAt s₀.mem (s₀.gpr .x0)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp [Nat.mul_comm]) dVS dDS dVD fitD
    ⟨s₀.gpr .x0, rfl, rfl, ⟨by rw [hrd]; simp, fitK, fun w hw => by
      rw [hwr] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact dKV
      · exact dKD
      · exact dKS⟩, fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dKS⟩ crypt_keeps)
    fun s' ⟨hcs, hdata, hiv, _, _, _⟩ => ⟨hcs, by rw [dirCore_bw, Nat.mul_one] at hdata hiv; exact ⟨hdata, hiv⟩⟩

theorem ofb_wp {s₀ : State} (hp : ofbAArch64.pre s₀) :
    WP isa ofb s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ ofbAArch64.post s₀ s' :=
  WP.mono (fb_wp' .ofb hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.ofb_of 8 (ciphOf s₀) s₀.mem (s₀.gpr .x2) (ivOf s₀) (s₀.gpr .x3).toNat
    refine ⟨hg, ?_, by rw [hv, h2]⟩
    change Spec.Blowfish.cbcBlocksAt _ _ _ = Spec.Ofb.crypt _ _ (Spec.Blowfish.cbcBlocksAt _ _ _)
    rw [cbcBlocksAt_eq, cbcBlocksAt_eq, hd, h1]

theorem cfbEncrypt_wp {s₀ : State} (hp : cfbEncAArch64.pre s₀) :
    WP isa cfbEncrypt s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cfbEncAArch64.post s₀ s' :=
  WP.mono (fb_wp' .cfbEnc hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfbEnc_of 8 (ciphOf s₀) s₀.mem (s₀.gpr .x2) (ivOf s₀) (s₀.gpr .x3).toNat
    refine ⟨hg, ?_, ?_⟩
    · change Spec.Blowfish.cbcBlocksAt _ _ _ = Spec.Cfb.encrypt _ _ (Spec.Blowfish.cbcBlocksAt _ _ _)
      rw [cbcBlocksAt_eq, cbcBlocksAt_eq, hd, h1]
    · change _ = Spec.Cbc.next _ (Spec.Cfb.encrypt _ _ (Spec.Blowfish.cbcBlocksAt _ _ _))
      rw [hv, h2, cbcBlocksAt_eq]

theorem cfbDecrypt_wp {s₀ : State} (hp : cfbDecAArch64.pre s₀) :
    WP isa cfbDecrypt s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cfbDecAArch64.post s₀ s' :=
  WP.mono (fb_wp' .cfbDec hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfbDec_of 8 (ciphOf s₀) s₀.mem (s₀.gpr .x2) (ivOf s₀) (s₀.gpr .x3).toNat
    refine ⟨hg, ?_, ?_⟩
    · change Spec.Blowfish.cbcBlocksAt _ _ _ = Spec.Cfb.decrypt _ _ (Spec.Blowfish.cbcBlocksAt _ _ _)
      rw [cbcBlocksAt_eq, cbcBlocksAt_eq, hd, h1]
    · change _ = Spec.Cbc.next _ (Spec.Blowfish.cbcBlocksAt _ _ _)
      rw [hv, h2, cbcBlocksAt_eq]

/-- Every instruction keeps `v8`–`v15`, but in `crypt`. -/
theorem fb_vSafe (mo : Impl.Modes.FbMode) : VSafeBut (dirCore true).crypt ((dirCore true).fb mo modeRegs .x25) := by
  cases mo <;> vsafe_but

/-- The callee-saved registers and the rest of the ABI, from what a mode
keeps. -/
theorem abi_of {mo : Impl.Modes.FbMode} {s s' : State} {t : List Leak}
    (he : Exec isa ((dirCore true).fb mo modeRegs .x25) s t s')
    (h₁ : ∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19))
    (h₃ : ∀ r ∈ [Reg.x30], s'.gpr r = s.gpr r) : abiPreserved s s' :=
  ⟨Modes.AArch64.preserved_of h₁ h₃, Exec.sp he, vKeep_of_vSafeBut (fb_vSafe mo) (crypt_vKeep true) _ _ _ he⟩

/-! ## Constant time -/

theorem fbTaint_agree {len : State → Nat} (s₁ s₂ : State) (_ : fbPre len s₁) (_ : fbPre len s₂)
    (hp : fbPub s₁ s₂) : VG.AArch64.Taint.Agree (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) s₁ s₂ := by
  obtain ⟨h1, h2, h3, h4, h5, hsp⟩ := hp
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- A state satisfying the precondition (one block). -/
def fbSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x3000 | .x2 => 0x4000 | .x3 => 1 | .x4 => 0x5000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 4168⟩]
  wr := [⟨0x3000, 8⟩, ⟨0x4000, 8⟩, ⟨0x5000, 8 * 28⟩]

/-- A state satisfying the contracts' precondition: the schedule at
`0x1000`, the IV at `0x3000`, one block at `0x4000`. -/
def fbFrameSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x3000 | .x2 => 0x4000 | .x3 => 1 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 4168⟩]
  wr := [⟨0x3000, 8⟩, ⟨0x4000, 8⟩]

theorem ofb_verified :
    Verified AArch64.target ofb (Proof.Blowfish.fbScratchContract AArch64.abi 28 Proof.Blowfish.ofbPost) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs (rs := [.x30]) (ofb_wp hs) (by lit_decide) (by lit_decide)
      exact ⟨t, s', he, abi_of he h₁ h₃, h₂⟩)
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) fbTaint_agree
      (by taint_decide)) (by
    sig_implies [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Spec.Blowfish.ofbSig,
      Proof.Blowfish.ofbPost, ofbAArch64, fbPre, fbPub, AArch64.abi, AArch64.argRegs] [fbSat] using fbSat)

theorem cfbEncrypt_verified :
    Verified AArch64.target cfbEncrypt (Proof.Blowfish.fbScratchContract AArch64.abi 28 Proof.Blowfish.cfbEncPost) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs (rs := [.x30]) (cfbEncrypt_wp hs) (by lit_decide)
        (by lit_decide)
      exact ⟨t, s', he, abi_of he h₁ h₃, h₂⟩)
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) fbTaint_agree
      (by taint_decide)) (by
    sig_implies [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Spec.Blowfish.ofbSig,
      Proof.Blowfish.cfbEncPost, cfbEncAArch64, fbPre, fbPub, AArch64.abi, AArch64.argRegs] [fbSat] using fbSat)

theorem cfbDecrypt_verified :
    Verified AArch64.target cfbDecrypt (Proof.Blowfish.fbScratchContract AArch64.abi 28 Proof.Blowfish.cfbDecPost) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs (rs := [.x30]) (cfbDecrypt_wp hs) (by lit_decide)
        (by lit_decide)
      exact ⟨t, s', he, abi_of he h₁ h₃, h₂⟩)
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) fbTaint_agree
      (by taint_decide)) (by
    sig_implies [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Spec.Blowfish.ofbSig,
      Proof.Blowfish.cfbDecPost, cfbDecAArch64, fbPre, fbPub, AArch64.abi, AArch64.argRegs] [fbSat] using fbSat)

theorem ofbFrameSat_pre : ∃ s, (Spec.Blowfish.ofbContract AArch64.abi 224).pre s := by
  implies_sat [Spec.Blowfish.ofbContract, Spec.Blowfish.ofbSig, AArch64.abi, AArch64.argRegs]
    [fbFrameSat] using fbFrameSat

theorem cfbEncFrameSat_pre : ∃ s, (Spec.Blowfish.cfbEncryptContract AArch64.abi 224).pre s := by
  implies_sat [Spec.Blowfish.cfbEncryptContract, Spec.Blowfish.cfbSig, Spec.Blowfish.ofbSig, AArch64.abi,
    AArch64.argRegs] [fbFrameSat] using fbFrameSat

theorem cfbDecFrameSat_pre : ∃ s, (Spec.Blowfish.cfbDecryptContract AArch64.abi 224).pre s := by
  implies_sat [Spec.Blowfish.cfbDecryptContract, Spec.Blowfish.cfbSig, Spec.Blowfish.ofbSig, AArch64.abi,
    AArch64.argRegs] [fbFrameSat] using fbFrameSat

/-- OFB with its working space on the stack. -/
theorem ofb_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 224 .x4 28 ofb)
      (Spec.Blowfish.ofbContract AArch64.abi 224) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Blowfish.ofbSig) (nm := "scratch") (e := .u64)
    (n := 28) (post := Proof.Blowfish.ofbPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 224) ofb_verified
    (by decide) (by decide) (by decide) (Proof.Blowfish.ofbPostOut_local _) ofbFrameSat_pre

/-- CFB64 encryption with its working space on the stack. -/
theorem cfbEncrypt_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 224 .x4 28 cfbEncrypt)
      (Spec.Blowfish.cfbEncryptContract AArch64.abi 224) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Blowfish.cfbSig) (nm := "scratch") (e := .u64)
    (n := 28) (post := Proof.Blowfish.cfbEncPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 224) cfbEncrypt_verified
    (by decide) (by decide) (by decide) (Proof.Blowfish.cfbEncPostOut_local _) cfbEncFrameSat_pre

/-- CFB64 decryption with its working space on the stack. -/
theorem cfbDecrypt_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 224 .x4 28 cfbDecrypt)
      (Spec.Blowfish.cfbDecryptContract AArch64.abi 224) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Blowfish.cfbSig) (nm := "scratch") (e := .u64)
    (n := 28) (post := Proof.Blowfish.cfbDecPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 224) cfbDecrypt_verified
    (by decide) (by decide) (by decide) (Proof.Blowfish.cfbDecPostOut_local _) cfbDecFrameSat_pre

end VG.Proof.Blowfish.AArch64
