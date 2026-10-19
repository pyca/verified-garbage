module

import VerifiedGarbage.Proof.Seed.AArch64.Link
meta import VerifiedGarbage.Proof.Seed.AArch64.Link
import VerifiedGarbage.Proof.Modes.AArch64.Fb
meta import VerifiedGarbage.Proof.Modes.AArch64.Fb
public import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
public import VerifiedGarbage.Proof.Seed.FbScratch
meta import VerifiedGarbage.Proof.Seed.FbScratch
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Seed.AArch64.ModesLit
meta import VerifiedGarbage.Proof.Seed.AArch64.ModesLit
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Seed.AArch64.ModeCore
public import VerifiedGarbage.Spec.Seed.Cfb
public import VerifiedGarbage.Impl.StackScratch.AArch64
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Impl.Aes.AArch64.Alloc
import VerifiedGarbage.Proof.Aes.Blocks
import VerifiedGarbage.Proof.AesCcm.Mac
import VerifiedGarbage.Proof.AesCtr.Ctr32
import VerifiedGarbage.Proof.AesCtr.Spec
import VerifiedGarbage.Proof.AesSiv.Ctr32
import VerifiedGarbage.Proof.AesSiv.Words
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.ReadHalves
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Gcm.Bits
import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Modes.AArch64.CbcEncLoop
import VerifiedGarbage.Proof.Modes.AArch64.CbcGroup
import VerifiedGarbage.Proof.Modes.AArch64.Copy
import VerifiedGarbage.Proof.Modes.AArch64.Counter
import VerifiedGarbage.Proof.Modes.AArch64.Steps
import VerifiedGarbage.Proof.Modes.AArch64.Unchain
import VerifiedGarbage.Proof.Modes.AArch64.Words
import VerifiedGarbage.Proof.Modes.AArch64.Xor
import VerifiedGarbage.Proof.Modes.Addr
import VerifiedGarbage.Proof.Seed.AArch64.Setup
import VerifiedGarbage.Proof.Seed.AArch64.Swap
import VerifiedGarbage.Proof.Seed.Memory
import VerifiedGarbage.Proof.Seed.Scratch
import VerifiedGarbage.Spec.Ctr.Contract
meta import VerifiedGarbage.Impl.Aes.AArch64.Alloc
meta import VerifiedGarbage.Proof.Aes.Blocks
meta import VerifiedGarbage.Proof.AesCcm.Mac
meta import VerifiedGarbage.Proof.AesCtr.Ctr32
meta import VerifiedGarbage.Proof.AesCtr.Spec
meta import VerifiedGarbage.Proof.AesSiv.Ctr32
meta import VerifiedGarbage.Proof.AesSiv.Words
meta import VerifiedGarbage.Proof.Cmac.Dbl32
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Cmac.Stream
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.ReadHalves
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Gcm.Bits
meta import VerifiedGarbage.Proof.Gcm.Spec
meta import VerifiedGarbage.Proof.Gcm.Stream
meta import VerifiedGarbage.Proof.Modes.AArch64.CbcEncLoop
meta import VerifiedGarbage.Proof.Modes.AArch64.CbcGroup
meta import VerifiedGarbage.Proof.Modes.AArch64.Copy
meta import VerifiedGarbage.Proof.Modes.AArch64.Counter
meta import VerifiedGarbage.Proof.Modes.AArch64.Steps
meta import VerifiedGarbage.Proof.Modes.AArch64.Unchain
meta import VerifiedGarbage.Proof.Modes.AArch64.Words
meta import VerifiedGarbage.Proof.Modes.AArch64.Xor
meta import VerifiedGarbage.Proof.Modes.Addr
meta import VerifiedGarbage.Proof.Seed.AArch64.ModeCore
meta import VerifiedGarbage.Proof.Seed.AArch64.Setup
meta import VerifiedGarbage.Proof.Seed.AArch64.Swap
meta import VerifiedGarbage.Proof.Seed.Memory
meta import VerifiedGarbage.Proof.Seed.Scratch
meta import VerifiedGarbage.Spec.Ctr.Contract
meta import VerifiedGarbage.Spec.Seed.Cfb

/-!
# SEED-OFB and SEED-CFB128 on AArch64 meet their contracts

`ofb_wp`, `cfbEncrypt_wp`, `cfbDecrypt_wp`: the modes' OFB and CFB
(`Proof.Modes.AArch64.fb_wp`) over SEED encryption's core (`dirCoreSpec .encrypt`),
with the IV's address in `x25`, which the core keeps in `v31` around its
code (`BlockSpec.viaV`, `keepsReg_viaV`), and the specification's results
(`Proof.Modes.ofb_of`, …). `ofb_verified`, …: each is correct and constant
time, by the taint analysis with public values in vector registers
(`VectorTaint`): the pointers, `n` and the stack pointer are public, and so
is everything the code computes from them, which it keeps in registers (the
IV's address in `v31`, the data's address and the blocks left in `v29`
and `v30`, across the batch, which uses no vector instruction);
the IV is secret. `ofb_framed`, …
run them with their working space on the stack, zeroed on return: 1456
bytes, the 182 words of the scratch buffer.
-/

@[expose] public section

namespace VG.Proof.Seed.AArch64

open VG VG.AArch64 VG.Impl.Seed.AArch64

/-- The precondition of the feedback modes on AArch64, with the working
space at `x4`. -/
def fbPre (s : State) : Prop :=
  let sched : Region := ⟨s.gpr .x0, 128⟩
  let iv : Region := ⟨s.gpr .x1, 16⟩
  let data : Region := ⟨s.gpr .x2, 16 * (s.gpr .x3).toNat⟩
  let scratch : Region := ⟨s.gpr .x4, 8 * 182⟩
  s.rd = [sched] ∧ s.wr = [iv, data, scratch] ∧ sched.Disjoint iv ∧ sched.Disjoint data ∧
    sched.Disjoint scratch ∧ iv.Disjoint data ∧ iv.Disjoint scratch ∧ data.Disjoint scratch ∧
    (s.gpr .x0).toNat + 128 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 16 ≤ 2 ^ 64 ∧
    (s.gpr .x2).toNat + 16 * (s.gpr .x3).toNat ≤ 2 ^ 64 ∧ (s.gpr .x4).toNat + 8 * 182 ≤ 2 ^ 64

/-- The public arguments. -/
def fbPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

/-- The cipher, IV and data of `s`'s arguments. -/
abbrev ciphOf (s : State) : Spec.Cbc.Cipher := Spec.Seed.cipher (Spec.Seed.scheduleAt s.mem (s.gpr .x0))
abbrev ivOf (s : State) : List Byte := Spec.Aes.bytesAt s.mem (s.gpr .x1) 16
abbrev blocksOf (s : State) (m : Mem) : List (List Byte) := Spec.Cbc.blocksAt m (s.gpr .x2) (s.gpr .x3).toNat

def ofbAArch64 : Contract isa where
  pre := fbPre
  post s s' := blocksOf s s'.mem = Spec.Ofb.crypt (ciphOf s) (ivOf s) (blocksOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .x1) 16 = Spec.Ofb.next (ciphOf s) (ivOf s) (s.gpr .x3).toNat
  pub := fbPub

def cfbEncAArch64 : Contract isa where
  pre := fbPre
  post s s' := blocksOf s s'.mem = Spec.Cfb.encrypt (ciphOf s) (ivOf s) (blocksOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .x1) 16 =
      Spec.Cbc.next (ivOf s) (Spec.Cfb.encrypt (ciphOf s) (ivOf s) (blocksOf s s.mem))
  pub := fbPub

def cfbDecAArch64 : Contract isa where
  pre := fbPre
  post s s' := blocksOf s s'.mem = Spec.Cfb.decrypt (ciphOf s) (ivOf s) (blocksOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .x1) 16 = Spec.Cbc.next (ivOf s) (blocksOf s s.mem)
  pub := fbPub

/-- SEED encryption's core, with `x25` kept in `v31`. -/
def fbCoreSpec : Modes.AArch64.BlockSpec fbCore :=
  (dirCoreSpec .encrypt).viaV .v31 (by decide) (by decide) (by decide) fun _ h => h

attribute [local irreducible] Spec.Seed.cipher in
/-- The core's cipher is the contract's, without unfolding it. -/
theorem fbCipher_eq (k : Spec.Seed.Schedule) : fbCoreSpec.cipher k = Spec.Seed.cipher k := rfl

/-- The core keeps `x25`, where the modes keep the IV's address. -/
theorem keeps_x25 : Modes.AArch64.KeepsReg .x25 fbCore.prepare ∧ Modes.AArch64.KeepsReg .x25 fbCore.crypt :=
  Modes.AArch64.keepsReg_viaV (by decide +kernel) (by lit_decide)

/-- What the modes' OFB and CFB give, for a mode `mo`: the data and the IV
as `fbOut` and `fbIn`, keeping the callee-saved registers. -/
theorem fb_wp' (mo : Impl.Modes.FbMode) {s₀ : State} (hp : fbPre s₀) :
    WP isa (fbCore.fb mo ⟨.x1, .x2, .x3, .x4⟩ .x25) s₀ fun s' =>
      (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
        s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧
      Modes.blocksOf 16 s'.mem (s₀.gpr .x2) (s₀.gpr .x3).toNat =
        (List.range (s₀.gpr .x3).toNat).map (Modes.fbOut mo 16 (ciphOf s₀) s₀.mem (s₀.gpr .x2) (ivOf s₀)) ∧
      Spec.Aes.bytesAt s'.mem (s₀.gpr .x1) 16 =
        Modes.fbIn mo 16 (ciphOf s₀) s₀.mem (s₀.gpr .x2) (ivOf s₀) (s₀.gpr .x3).toNat := by
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .x4, 8 * 182⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.AArch64.fb_wp fbCoreSpec mo (r := ⟨.x1, .x2, .x3, .x4⟩)
    ⟨by decide, by decide, by decide⟩ (by decide) (ivR := .x25)
    ⟨by decide, by decide, by decide, by decide, by decide⟩
    (B := s₀.gpr .x4) (P := s₀.gpr .x1) (D := s₀.gpr .x2) (n := (s₀.gpr .x3).toNat)
    (k := Spec.Seed.scheduleAt s₀.mem (s₀.gpr .x0)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp) dVS dDS dVD fitD
    ⟨s₀.gpr .x0, rfl, rfl, by rw [hrd]; simp, fitK, fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dKS⟩ keeps_x25)
    fun s' ⟨hcs, hdata, hiv, _, _, _⟩ => ⟨hcs, by rw [fbCipher_eq] at hdata hiv; exact ⟨hdata, hiv⟩⟩

theorem ofb_wp {s₀ : State} (hp : ofbAArch64.pre s₀) :
    WP isa ofb s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ ofbAArch64.post s₀ s' :=
  WP.mono (fb_wp' .ofb hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.ofb_of 16 (ciphOf s₀) s₀.mem (s₀.gpr .x2) (ivOf s₀) (s₀.gpr .x3).toNat
    exact ⟨hg, hd.trans h1, hv.trans h2⟩

theorem cfbEncrypt_wp {s₀ : State} (hp : cfbEncAArch64.pre s₀) :
    WP isa cfbEncrypt s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cfbEncAArch64.post s₀ s' :=
  WP.mono (fb_wp' .cfbEnc hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfbEnc_of 16 (ciphOf s₀) s₀.mem (s₀.gpr .x2) (ivOf s₀) (s₀.gpr .x3).toNat
    exact ⟨hg, hd.trans h1, hv.trans h2⟩

theorem cfbDecrypt_wp {s₀ : State} (hp : cfbDecAArch64.pre s₀) :
    WP isa cfbDecrypt s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cfbDecAArch64.post s₀ s' :=
  WP.mono (fb_wp' .cfbDec hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfbDec_of 16 (ciphOf s₀) s₀.mem (s₀.gpr .x2) (ivOf s₀) (s₀.gpr .x3).toNat
    exact ⟨hg, hd.trans h1, hv.trans h2⟩

/-- The callee-saved registers and the rest of the ABI, from what a mode
keeps. -/
theorem modeAbi_of {c : Prog isa} {s s' : State} {t : List Leak} (he : Exec isa c s t s')
    (h₁ : ∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19))
    (h₃ : ∀ r ∈ [Reg.x30], s'.gpr r = s.gpr r) (hv : c.allInstrs keepsV = true) : abiPreserved s s' :=
  ⟨Modes.AArch64.preserved_of h₁ h₃, Exec.sp he, Exec.preservedV he hv⟩

/-! ## Constant time -/

theorem fbTaint_agree (s₁ s₂ : State) (_ : fbPre s₁) (_ : fbPre s₂) (hp : fbPub s₁ s₂) :
    VectorTaint.Agree (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4]) s₁ s₂ := by
  obtain ⟨h1, h2, h3, h4, h5, hsp⟩ := hp
  refine ⟨⟨hsp, fun r hr => ?_⟩, ?_⟩
  · simp only [VectorTaint.ofRegs, Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption
  · intro r hr
    simp [VectorTaint.ofRegs, RegSet.mem_ofList] at hr

/-- A state satisfying the precondition (one block). -/
def fbSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 1 | .x4 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 16⟩, ⟨0x4000, 8 * 182⟩]

theorem ofb_verified :
    Verified AArch64.target ofb (Proof.Seed.fbScratchContract AArch64.abi 182 Proof.Seed.ofbPost) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs' ofb_keeps_x30 (ofb_wp hs)
      exact ⟨t, s', he, modeAbi_of he h₁ h₃ (by lit_decide), h₂⟩)
    (VG.Taint.constantTime (A := VectorTaint.taint) (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4]) fbTaint_agree
      (by taint_decide)) (by
    sig_implies [Proof.Seed.fbScratchContract, Proof.Seed.fbScratchSig, Spec.Seed.ofbSig, Proof.Seed.ofbPost,
      ofbAArch64, fbPre, fbPub, AArch64.abi, AArch64.argRegs] [fbSat] using fbSat)

theorem cfbEncrypt_verified :
    Verified AArch64.target cfbEncrypt (Proof.Seed.fbScratchContract AArch64.abi 182 Proof.Seed.cfbEncPost) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs' cfbEncrypt_keeps_x30 (cfbEncrypt_wp hs)
      exact ⟨t, s', he, modeAbi_of he h₁ h₃ (by lit_decide), h₂⟩)
    (VG.Taint.constantTime (A := VectorTaint.taint) (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4]) fbTaint_agree
      (by taint_decide)) (by
    sig_implies [Proof.Seed.fbScratchContract, Proof.Seed.fbScratchSig, Spec.Seed.ofbSig, Proof.Seed.cfbEncPost,
      cfbEncAArch64, fbPre, fbPub, AArch64.abi, AArch64.argRegs] [fbSat] using fbSat)

theorem cfbDecrypt_verified :
    Verified AArch64.target cfbDecrypt (Proof.Seed.fbScratchContract AArch64.abi 182 Proof.Seed.cfbDecPost) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs' cfbDecrypt_keeps_x30 (cfbDecrypt_wp hs)
      exact ⟨t, s', he, modeAbi_of he h₁ h₃ (by lit_decide), h₂⟩)
    (VG.Taint.constantTime (A := VectorTaint.taint) (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4]) fbTaint_agree
      (by taint_decide)) (by
    sig_implies [Proof.Seed.fbScratchContract, Proof.Seed.fbScratchSig, Spec.Seed.ofbSig, Proof.Seed.cfbDecPost,
      cfbDecAArch64, fbPre, fbPub, AArch64.abi, AArch64.argRegs] [fbSat] using fbSat)

/-- A state satisfying the contracts' precondition: the schedule at
`0x1000`, the IV at `0x2000`, one block at `0x3000`. -/
def fbFrameSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 1 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 16⟩]

theorem ofbFrameSat_pre : ∃ s, (Spec.Seed.ofbContract AArch64.abi 1456).pre s := by
  implies_sat [Spec.Seed.ofbContract, Spec.Seed.ofbSig, AArch64.abi, AArch64.argRegs] [fbFrameSat] using fbFrameSat

theorem cfbEncFrameSat_pre : ∃ s, (Spec.Seed.cfbEncryptContract AArch64.abi 1456).pre s := by
  implies_sat [Spec.Seed.cfbEncryptContract, Spec.Seed.cfbSig, Spec.Seed.ofbSig, AArch64.abi, AArch64.argRegs]
    [fbFrameSat] using fbFrameSat

theorem cfbDecFrameSat_pre : ∃ s, (Spec.Seed.cfbDecryptContract AArch64.abi 1456).pre s := by
  implies_sat [Spec.Seed.cfbDecryptContract, Spec.Seed.cfbSig, Spec.Seed.ofbSig, AArch64.abi, AArch64.argRegs]
    [fbFrameSat] using fbFrameSat

/-- OFB with its working space on the stack. -/
theorem ofb_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 1456 .x4 182 ofb)
      (Spec.Seed.ofbContract AArch64.abi 1456) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Seed.ofbSig) (nm := "scratch") (e := .u64)
    (n := 182) (post := Proof.Seed.ofbPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 1456) ofb_verified
    (by decide) (by decide) (by decide) (Proof.Seed.ofbPostOut_local _) ofbFrameSat_pre

/-- CFB128 encryption with its working space on the stack. -/
theorem cfbEncrypt_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 1456 .x4 182 cfbEncrypt)
      (Spec.Seed.cfbEncryptContract AArch64.abi 1456) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Seed.cfbSig) (nm := "scratch") (e := .u64)
    (n := 182) (post := Proof.Seed.cfbEncPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 1456) cfbEncrypt_verified
    (by decide) (by decide) (by decide) (Proof.Seed.cfbEncPostOut_local _) cfbEncFrameSat_pre

/-- CFB128 decryption with its working space on the stack. -/
theorem cfbDecrypt_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 1456 .x4 182 cfbDecrypt)
      (Spec.Seed.cfbDecryptContract AArch64.abi 1456) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Seed.cfbSig) (nm := "scratch") (e := .u64)
    (n := 182) (post := Proof.Seed.cfbDecPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 1456) cfbDecrypt_verified
    (by decide) (by decide) (by decide) (Proof.Seed.cfbDecPostOut_local _) cfbDecFrameSat_pre

end VG.Proof.Seed.AArch64
