module

import VerifiedGarbage.Proof.TripleDes.AArch64.Link
meta import VerifiedGarbage.Proof.TripleDes.AArch64.Link
public import VerifiedGarbage.Proof.TripleDes.AArch64.BlockSum
meta import VerifiedGarbage.Proof.TripleDes.AArch64.BlockSum
import VerifiedGarbage.Proof.Modes.AArch64.Cfb8
meta import VerifiedGarbage.Proof.Modes.AArch64.Cfb8
public import VerifiedGarbage.Proof.TripleDes.FbScratch
meta import VerifiedGarbage.Proof.TripleDes.FbScratch
import VerifiedGarbage.Proof.TripleDes.AArch64.FbLit
meta import VerifiedGarbage.Proof.TripleDes.AArch64.FbLit
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.TripleDes.AArch64.Fb
public import VerifiedGarbage.Proof.TripleDes.AArch64.Lit
public import VerifiedGarbage.Proof.TripleDes.AArch64.RoundLit
public import VerifiedGarbage.Proof.TripleDes.AArch64.SboxTable
public import VerifiedGarbage.Proof.TripleDes.SboxTables
public import VerifiedGarbage.Spec.TripleDes.Cfb
public import VerifiedGarbage.Proof.Modes.AArch64.FbLoop
public import VerifiedGarbage.Proof.Modes.Cfb8
public import VerifiedGarbage.Impl.StackScratch.AArch64
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.TripleDes.AArch64.ModeCore
meta import VerifiedGarbage.Proof.TripleDes.AArch64.ModeCore
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
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Gcm.Bits
import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Modes.AArch64.CbcEncLoop
import VerifiedGarbage.Proof.Modes.AArch64.CbcGroup
import VerifiedGarbage.Proof.Modes.AArch64.Cfb8Loop
import VerifiedGarbage.Proof.Modes.AArch64.Cfb8Steps
import VerifiedGarbage.Proof.Modes.AArch64.Copy
import VerifiedGarbage.Proof.Modes.AArch64.Counter
import VerifiedGarbage.Proof.Modes.AArch64.Steps
import VerifiedGarbage.Proof.Modes.AArch64.Unchain
import VerifiedGarbage.Proof.Modes.AArch64.Words
import VerifiedGarbage.Proof.Modes.AArch64.Xor
import VerifiedGarbage.Proof.Modes.Addr
import VerifiedGarbage.Proof.Rc2.AArch64.BlockIO
import VerifiedGarbage.Proof.Rc2.AArch64.Cipher
import VerifiedGarbage.Proof.Rc2.AArch64.MemOps
import VerifiedGarbage.Proof.Rc2.Select
import VerifiedGarbage.Proof.Rc2.Word
import VerifiedGarbage.Proof.TripleDes.AArch64.Box
import VerifiedGarbage.Proof.TripleDes.AArch64.Bytes
import VerifiedGarbage.Proof.TripleDes.AArch64.Initial
import VerifiedGarbage.Proof.TripleDes.AArch64.Permutation
import VerifiedGarbage.Proof.TripleDes.AArch64.RoundBody
import VerifiedGarbage.Proof.TripleDes.AArch64.RoundFunction
import VerifiedGarbage.Proof.TripleDes.AArch64.Store
import VerifiedGarbage.Proof.TripleDes.AArch64.Tail
import VerifiedGarbage.Proof.TripleDes.AArch64.VerifiedBlock
import VerifiedGarbage.Proof.TripleDes.AArch64.Word
import VerifiedGarbage.Proof.TripleDes.Bytes
import VerifiedGarbage.Proof.TripleDes.Permutation
import VerifiedGarbage.Proof.TripleDes.Round
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.TripleDes.Word
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
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd64
meta import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.CallLay
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Gcm.Bits
meta import VerifiedGarbage.Proof.Gcm.Spec
meta import VerifiedGarbage.Proof.Gcm.Stream
meta import VerifiedGarbage.Proof.Modes.AArch64.CbcEncLoop
meta import VerifiedGarbage.Proof.Modes.AArch64.CbcGroup
meta import VerifiedGarbage.Proof.Modes.AArch64.Cfb8Loop
meta import VerifiedGarbage.Proof.Modes.AArch64.Cfb8Steps
meta import VerifiedGarbage.Proof.Modes.AArch64.Copy
meta import VerifiedGarbage.Proof.Modes.AArch64.Counter
meta import VerifiedGarbage.Proof.Modes.AArch64.Steps
meta import VerifiedGarbage.Proof.Modes.AArch64.Unchain
meta import VerifiedGarbage.Proof.Modes.AArch64.Words
meta import VerifiedGarbage.Proof.Modes.AArch64.Xor
meta import VerifiedGarbage.Proof.Modes.Addr
meta import VerifiedGarbage.Proof.Rc2.AArch64.BlockIO
meta import VerifiedGarbage.Proof.Rc2.AArch64.Cipher
meta import VerifiedGarbage.Proof.Rc2.AArch64.MemOps
meta import VerifiedGarbage.Proof.Rc2.Select
meta import VerifiedGarbage.Proof.Rc2.Word
meta import VerifiedGarbage.Proof.TripleDes.AArch64.Box
meta import VerifiedGarbage.Proof.TripleDes.AArch64.Bytes
meta import VerifiedGarbage.Proof.TripleDes.AArch64.Initial
meta import VerifiedGarbage.Proof.TripleDes.AArch64.Permutation
meta import VerifiedGarbage.Proof.TripleDes.AArch64.RoundBody
meta import VerifiedGarbage.Proof.TripleDes.AArch64.RoundFunction
meta import VerifiedGarbage.Proof.TripleDes.AArch64.Store
meta import VerifiedGarbage.Proof.TripleDes.AArch64.Tail
meta import VerifiedGarbage.Proof.TripleDes.AArch64.VerifiedBlock
meta import VerifiedGarbage.Proof.TripleDes.AArch64.Word
meta import VerifiedGarbage.Proof.TripleDes.Bytes
meta import VerifiedGarbage.Proof.TripleDes.Permutation
meta import VerifiedGarbage.Proof.TripleDes.Round
meta import VerifiedGarbage.Proof.TripleDes.Schedule
meta import VerifiedGarbage.Proof.TripleDes.Word
meta import VerifiedGarbage.Spec.Ctr.Contract
meta import VerifiedGarbage.Spec.TripleDes.Cfb

/-!
# Triple DES-OFB, -CFB64 and -CFB8 on AArch64 meet their contracts

`ofb_wp`, …, `cfb8Decrypt_wp`: the modes' OFB, CFB and CFB8
(`Proof.Modes.AArch64.fb_wp`, `cfb8_wp`) over CBC encryption's core
(`dirCoreSpec .encrypt`), with the IV's address in `x25`, which the core
never writes (`keepsReg_of_regSafe`), and the specification's results
(`Proof.Modes.ofb_of`, …). `ofb_verified`, …: each is correct and constant
time, by the taint analysis: the pointers, `n` (or `len`) and the stack
pointer are public, and so is everything the code computes from them, which
it keeps in registers; the IV is secret. `ofb_framed`, … run them with their
working space on the stack, zeroed on return: 1008 bytes, the 125 words of
the scratch buffer rounded up to the stack's alignment.
-/

@[expose] public section

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.Impl.TripleDes.AArch64

/-- The precondition of the feedback modes on AArch64, with the data `len`
bytes long and the working space at `x4`. -/
def fbPre (len : State → Nat) (s : State) : Prop :=
  let sched : Region := ⟨s.gpr .x0, 384⟩
  let iv : Region := ⟨s.gpr .x1, 8⟩
  let data : Region := ⟨s.gpr .x2, len s⟩
  let scratch : Region := ⟨s.gpr .x4, 8 * 125⟩
  s.rd = [sched] ∧ s.wr = [iv, data, scratch] ∧ sched.Disjoint iv ∧ sched.Disjoint data ∧
    sched.Disjoint scratch ∧ iv.Disjoint data ∧ iv.Disjoint scratch ∧ data.Disjoint scratch ∧
    (s.gpr .x0).toNat + 384 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 8 ≤ 2 ^ 64 ∧
    (s.gpr .x2).toNat + len s ≤ 2 ^ 64 ∧ (s.gpr .x4).toNat + 8 * 125 ≤ 2 ^ 64

/-- The public arguments. -/
def fbPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

/-- `n` blocks. -/
abbrev blkLen (s : State) : Nat := 8 * (s.gpr .x3).toNat

/-- `len` bytes. -/
abbrev byteLen (s : State) : Nat := (s.gpr .x3).toNat

/-- The schedule, IV and data of `s`'s arguments. -/
abbrev ciphOf (s : State) : Spec.Cbc.Cipher := Spec.TripleDes.cipher (Spec.TripleDes.scheduleAt s.mem (s.gpr .x0))
abbrev ivOf (s : State) : List Byte := Spec.TripleDes.bytesAt s.mem (s.gpr .x1) 8
abbrev blocksOf (s : State) (m : Mem) : List (List Byte) := Spec.TripleDes.cbcBlocksAt m (s.gpr .x2) (s.gpr .x3).toNat

def ofbAArch64 : Contract isa where
  pre := fbPre blkLen
  post s s' := blocksOf s s'.mem = Spec.Ofb.crypt (ciphOf s) (ivOf s) (blocksOf s s.mem) ∧
    Spec.TripleDes.bytesAt s'.mem (s.gpr .x1) 8 = Spec.Ofb.next (ciphOf s) (ivOf s) (s.gpr .x3).toNat
  pub := fbPub

def cfbEncAArch64 : Contract isa where
  pre := fbPre blkLen
  post s s' := blocksOf s s'.mem = Spec.Cfb.encrypt (ciphOf s) (ivOf s) (blocksOf s s.mem) ∧
    Spec.TripleDes.bytesAt s'.mem (s.gpr .x1) 8 =
      Spec.Cbc.next (ivOf s) (Spec.Cfb.encrypt (ciphOf s) (ivOf s) (blocksOf s s.mem))
  pub := fbPub

def cfbDecAArch64 : Contract isa where
  pre := fbPre blkLen
  post s s' := blocksOf s s'.mem = Spec.Cfb.decrypt (ciphOf s) (ivOf s) (blocksOf s s.mem) ∧
    Spec.TripleDes.bytesAt s'.mem (s.gpr .x1) 8 = Spec.Cbc.next (ivOf s) (blocksOf s s.mem)
  pub := fbPub

def cfb8EncAArch64 : Contract isa where
  pre := fbPre byteLen
  post s s' := Spec.TripleDes.bytesAt s'.mem (s.gpr .x2) (byteLen s) =
      Spec.Cfb8.encrypt (ciphOf s) (ivOf s) (Spec.TripleDes.bytesAt s.mem (s.gpr .x2) (byteLen s)) ∧
    Spec.TripleDes.bytesAt s'.mem (s.gpr .x1) 8 = Spec.Cfb8.next (ivOf s)
      (Spec.Cfb8.encrypt (ciphOf s) (ivOf s) (Spec.TripleDes.bytesAt s.mem (s.gpr .x2) (byteLen s)))
  pub := fbPub

def cfb8DecAArch64 : Contract isa where
  pre := fbPre byteLen
  post s s' := Spec.TripleDes.bytesAt s'.mem (s.gpr .x2) (byteLen s) =
      Spec.Cfb8.decrypt (ciphOf s) (ivOf s) (Spec.TripleDes.bytesAt s.mem (s.gpr .x2) (byteLen s)) ∧
    Spec.TripleDes.bytesAt s'.mem (s.gpr .x1) 8 =
      Spec.Cfb8.next (ivOf s) (Spec.TripleDes.bytesAt s.mem (s.gpr .x2) (byteLen s))
  pub := fbPub

/-- The core keeps `x25`, where the modes keep the IV's address. -/
theorem keeps_x25 :
    Modes.AArch64.KeepsReg .x25 (dirCore .encrypt).prepare ∧ Modes.AArch64.KeepsReg .x25 (dirCore .encrypt).crypt :=
  ⟨Modes.AArch64.keepsReg_of_regSafe (by decide +kernel), crypt_keeps_x25 .encrypt⟩

/-- What the modes' OFB and CFB give, for a mode `mo`: the data and the
IV as `fbOut` and `fbIn`, keeping the callee-saved registers. -/
theorem fb_wp' (mo : Impl.Modes.FbMode) {s₀ : State} (hp : fbPre blkLen s₀) :
    WP isa ((dirCore .encrypt).fb mo fbRegs .x25) s₀ fun s' =>
      (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
        s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧
      Modes.blocksOf 8 s'.mem (s₀.gpr .x2) (s₀.gpr .x3).toNat =
        (List.range (s₀.gpr .x3).toNat).map (Modes.fbOut mo 8 (ciphOf s₀) s₀.mem (s₀.gpr .x2) (ivOf s₀)) ∧
      Spec.TripleDes.bytesAt s'.mem (s₀.gpr .x1) 8 =
        Modes.fbIn mo 8 (ciphOf s₀) s₀.mem (s₀.gpr .x2) (ivOf s₀) (s₀.gpr .x3).toNat := by
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .x4, 8 * 125⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.AArch64.fb_wp (dirCoreSpec .encrypt) mo (r := fbRegs)
    ⟨by decide, by decide, by decide⟩ (by decide) (ivR := .x25)
    ⟨by decide, by decide, by decide, by decide, by decide⟩
    (B := s₀.gpr .x4) (P := s₀.gpr .x1) (D := s₀.gpr .x2) (n := (s₀.gpr .x3).toNat)
    (k := Spec.TripleDes.scheduleAt s₀.mem (s₀.gpr .x0)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp [Nat.mul_comm]) dVS dDS dVD fitD
    ⟨s₀.gpr .x0, rfl, rfl, by rw [hrd]; simp, fitK, fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dKS⟩ keeps_x25)
    fun s' ⟨hcs, hdata, hiv, _, _, _⟩ => ⟨hcs, by rw [dirCore_bw, Nat.mul_one] at hdata hiv; exact ⟨hdata, hiv⟩⟩

/-- What the modes' CFB8 gives: the data and the input block as `cfb8Out`
and `cfb8In`, keeping the callee-saved registers. -/
theorem cfb8_wp' (enc : Bool) {s₀ : State} (hp : fbPre byteLen s₀) :
    WP isa ((dirCore .encrypt).cfb8 enc fbRegs .x25) s₀ fun s' =>
      (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
        s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧
      Spec.TripleDes.bytesAt s'.mem (s₀.gpr .x2) (byteLen s₀) =
        (List.range (byteLen s₀)).map (Modes.cfb8Out enc (ciphOf s₀) s₀.mem (s₀.gpr .x2) (ivOf s₀)) ∧
      Spec.TripleDes.bytesAt s'.mem (s₀.gpr .x1) 8 =
        Modes.cfb8In enc (ciphOf s₀) s₀.mem (s₀.gpr .x2) (ivOf s₀) (byteLen s₀) := by
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .x4, 8 * 125⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.AArch64.cfb8_wp (dirCoreSpec .encrypt) enc (r := fbRegs)
    ⟨by decide, by decide, by decide⟩ (by decide) (ivR := .x25)
    ⟨by decide, by decide, by decide, by decide, by decide⟩
    (B := s₀.gpr .x4) (P := s₀.gpr .x1) (D := s₀.gpr .x2) (n := (s₀.gpr .x3).toNat)
    (k := Spec.TripleDes.scheduleAt s₀.mem (s₀.gpr .x0)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp) dVS dDS dVD fitD
    ⟨s₀.gpr .x0, rfl, rfl, by rw [hrd]; simp, fitK, fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dKS⟩ keeps_x25)
    fun s' ⟨hcs, hdata, hiv, _, _, _⟩ => ⟨hcs, by rw [dirCore_bw, Nat.mul_one] at hdata hiv; exact ⟨hdata, hiv⟩⟩

theorem ofb_wp {s₀ : State} (hp : ofbAArch64.pre s₀) :
    WP isa ofb s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ ofbAArch64.post s₀ s' :=
  WP.mono (fb_wp' .ofb hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.ofb_of 8 (ciphOf s₀) s₀.mem (s₀.gpr .x2) (ivOf s₀) (s₀.gpr .x3).toNat
    refine ⟨hg, ?_, by rw [hv, h2]⟩
    change Spec.TripleDes.cbcBlocksAt _ _ _ = Spec.Ofb.crypt _ _ (Spec.TripleDes.cbcBlocksAt _ _ _)
    rw [cbcBlocksAt_eq, cbcBlocksAt_eq, hd, h1]

theorem cfbEncrypt_wp {s₀ : State} (hp : cfbEncAArch64.pre s₀) :
    WP isa cfbEncrypt s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cfbEncAArch64.post s₀ s' :=
  WP.mono (fb_wp' .cfbEnc hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfbEnc_of 8 (ciphOf s₀) s₀.mem (s₀.gpr .x2) (ivOf s₀) (s₀.gpr .x3).toNat
    refine ⟨hg, ?_, ?_⟩
    · change Spec.TripleDes.cbcBlocksAt _ _ _ = Spec.Cfb.encrypt _ _ (Spec.TripleDes.cbcBlocksAt _ _ _)
      rw [cbcBlocksAt_eq, cbcBlocksAt_eq, hd, h1]
    · change _ = Spec.Cbc.next _ (Spec.Cfb.encrypt _ _ (Spec.TripleDes.cbcBlocksAt _ _ _))
      rw [hv, h2, cbcBlocksAt_eq]

theorem cfbDecrypt_wp {s₀ : State} (hp : cfbDecAArch64.pre s₀) :
    WP isa cfbDecrypt s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cfbDecAArch64.post s₀ s' :=
  WP.mono (fb_wp' .cfbDec hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfbDec_of 8 (ciphOf s₀) s₀.mem (s₀.gpr .x2) (ivOf s₀) (s₀.gpr .x3).toNat
    refine ⟨hg, ?_, ?_⟩
    · change Spec.TripleDes.cbcBlocksAt _ _ _ = Spec.Cfb.decrypt _ _ (Spec.TripleDes.cbcBlocksAt _ _ _)
      rw [cbcBlocksAt_eq, cbcBlocksAt_eq, hd, h1]
    · change _ = Spec.Cbc.next _ (Spec.TripleDes.cbcBlocksAt _ _ _)
      rw [hv, h2, cbcBlocksAt_eq]

theorem ivOf_ne (s : State) : ivOf s ≠ [] := by simp [ivOf, Spec.TripleDes.bytesAt]

theorem cfb8Encrypt_wp {s₀ : State} (hp : cfb8EncAArch64.pre s₀) :
    WP isa cfb8Encrypt s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cfb8EncAArch64.post s₀ s' :=
  WP.mono (cfb8_wp' true hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfb8Enc_of (ciphOf s₀) s₀.mem (byteLen s₀) (s₀.gpr .x2) (ivOf s₀) (ivOf_ne s₀)
    exact ⟨hg, hd.trans h1, hv.trans h2⟩

theorem cfb8Decrypt_wp {s₀ : State} (hp : cfb8DecAArch64.pre s₀) :
    WP isa cfb8Decrypt s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cfb8DecAArch64.post s₀ s' :=
  WP.mono (cfb8_wp' false hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfb8Dec_of (ciphOf s₀) s₀.mem (byteLen s₀) (s₀.gpr .x2) (ivOf s₀) (ivOf_ne s₀)
    exact ⟨hg, hd.trans h1, hv.trans h2⟩

/-- The callee-saved registers and the rest of the ABI, from what a mode
keeps. -/
theorem abi_of {c : Prog isa} {s s' : State} {t : List Leak} (he : Exec isa c s t s')
    (h₁ : ∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19))
    (h₃ : ∀ r ∈ [Reg.x30], s'.gpr r = s.gpr r) (hv : c.allInstrs keepsV = true) : abiPreserved s s' :=
  ⟨Modes.AArch64.preserved_of h₁ h₃, Exec.sp he, Exec.preservedV he hv⟩

/-! ## Constant time -/

theorem fbTaint_agree {len : State → Nat} (s₁ s₂ : State) (_ : fbPre len s₁) (_ : fbPre len s₂)
    (hp : fbPub s₁ s₂) : VG.AArch64.Taint.Agree (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) s₁ s₂ := by
  obtain ⟨h1, h2, h3, h4, h5, hsp⟩ := hp
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- A state satisfying the precondition (one block, or one byte). -/
def fbSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 1 | .x4 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 8⟩, ⟨0x4000, 8 * 125⟩]

def cfb8Sat : State := { fbSat with wr := [⟨0x2000, 8⟩, ⟨0x3000, 1⟩, ⟨0x4000, 8 * 125⟩] }

/-- A state satisfying the contracts' precondition: the schedule at
`0x1000`, the IV at `0x2000`, one block (or byte) at `0x3000`. -/
def fbFrameSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 1 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 8⟩]

def cfb8FrameSat : State := { fbFrameSat with wr := [⟨0x2000, 8⟩, ⟨0x3000, 1⟩] }

theorem ofb_verified :
    Verified AArch64.target ofb (Proof.TripleDes.fbScratchContract AArch64.abi 125 Proof.TripleDes.ofbPost) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs' ofb_keeps_x30 (ofb_wp hs)
      exact ⟨t, s', he, abi_of he h₁ h₃ (by lit_decide), h₂⟩)
    (VG.Taint.constantTime_of_exists (A := VectorTaint.taint)
        (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4])
      (fun s₁ s₂ h₁ h₂ hp => ⟨fbTaint_agree s₁ s₂ h₁ h₂ hp, fun v hv => by
        simp [VectorTaint.ofRegs, RegSet.mem_ofList] at hv⟩) (by taint_decide_sum [encSum])) (by
    sig_implies [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig,
      Proof.TripleDes.ofbPost, ofbAArch64, fbPre, fbPub, AArch64.abi, AArch64.argRegs] [fbSat] using fbSat)

theorem cfbEncrypt_verified :
    Verified AArch64.target cfbEncrypt (Proof.TripleDes.fbScratchContract AArch64.abi 125 Proof.TripleDes.cfbEncPost) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs' cfbEncrypt_keeps_x30 (cfbEncrypt_wp hs)
      exact ⟨t, s', he, abi_of he h₁ h₃ (by lit_decide), h₂⟩)
    (VG.Taint.constantTime_of_exists (A := VectorTaint.taint)
        (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4])
      (fun s₁ s₂ h₁ h₂ hp => ⟨fbTaint_agree s₁ s₂ h₁ h₂ hp, fun v hv => by
        simp [VectorTaint.ofRegs, RegSet.mem_ofList] at hv⟩) (by taint_decide_sum [encSum])) (by
    sig_implies [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig,
      Proof.TripleDes.cfbEncPost, cfbEncAArch64, fbPre, fbPub, AArch64.abi, AArch64.argRegs] [fbSat] using fbSat)

theorem cfbDecrypt_verified :
    Verified AArch64.target cfbDecrypt (Proof.TripleDes.fbScratchContract AArch64.abi 125 Proof.TripleDes.cfbDecPost) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs' cfbDecrypt_keeps_x30 (cfbDecrypt_wp hs)
      exact ⟨t, s', he, abi_of he h₁ h₃ (by lit_decide), h₂⟩)
    (VG.Taint.constantTime_of_exists (A := VectorTaint.taint)
        (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4])
      (fun s₁ s₂ h₁ h₂ hp => ⟨fbTaint_agree s₁ s₂ h₁ h₂ hp, fun v hv => by
        simp [VectorTaint.ofRegs, RegSet.mem_ofList] at hv⟩) (by taint_decide_sum [encSum])) (by
    sig_implies [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig,
      Proof.TripleDes.cfbDecPost, cfbDecAArch64, fbPre, fbPub, AArch64.abi, AArch64.argRegs] [fbSat] using fbSat)

theorem cfb8Encrypt_verified :
    Verified AArch64.target cfb8Encrypt
      (Proof.TripleDes.cfb8ScratchContract AArch64.abi 125 Proof.TripleDes.cfb8EncPost) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs' cfb8Encrypt_keeps_x30 (cfb8Encrypt_wp hs)
      exact ⟨t, s', he, abi_of he h₁ h₃ (by lit_decide), h₂⟩)
    (VG.Taint.constantTime_of_exists (A := VectorTaint.taint)
        (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4])
      (fun s₁ s₂ h₁ h₂ hp => ⟨fbTaint_agree s₁ s₂ h₁ h₂ hp, fun v hv => by
        simp [VectorTaint.ofRegs, RegSet.mem_ofList] at hv⟩) (by taint_decide_sum [encSum])) (by
    sig_implies [Proof.TripleDes.cfb8ScratchContract, Proof.TripleDes.cfb8ScratchSig, Spec.TripleDes.cfb8Sig,
      Proof.TripleDes.cfb8EncPost, cfb8EncAArch64, fbPre, fbPub, AArch64.abi, AArch64.argRegs] [cfb8Sat]
      using cfb8Sat)

theorem cfb8Decrypt_verified :
    Verified AArch64.target cfb8Decrypt
      (Proof.TripleDes.cfb8ScratchContract AArch64.abi 125 Proof.TripleDes.cfb8DecPost) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs' cfb8Decrypt_keeps_x30 (cfb8Decrypt_wp hs)
      exact ⟨t, s', he, abi_of he h₁ h₃ (by lit_decide), h₂⟩)
    (VG.Taint.constantTime_of_exists (A := VectorTaint.taint)
        (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4])
      (fun s₁ s₂ h₁ h₂ hp => ⟨fbTaint_agree s₁ s₂ h₁ h₂ hp, fun v hv => by
        simp [VectorTaint.ofRegs, RegSet.mem_ofList] at hv⟩) (by taint_decide_sum [encSum])) (by
    sig_implies [Proof.TripleDes.cfb8ScratchContract, Proof.TripleDes.cfb8ScratchSig, Spec.TripleDes.cfb8Sig,
      Proof.TripleDes.cfb8DecPost, cfb8DecAArch64, fbPre, fbPub, AArch64.abi, AArch64.argRegs] [cfb8Sat]
      using cfb8Sat)

theorem ofbFrameSat_pre : ∃ s, (Spec.TripleDes.ofbContract AArch64.abi 1008).pre s := by
  implies_sat [Spec.TripleDes.ofbContract, Spec.TripleDes.ofbSig, AArch64.abi, AArch64.argRegs]
    [fbFrameSat] using fbFrameSat

theorem cfbEncFrameSat_pre : ∃ s, (Spec.TripleDes.cfbEncryptContract AArch64.abi 1008).pre s := by
  implies_sat [Spec.TripleDes.cfbEncryptContract, Spec.TripleDes.cfbSig, Spec.TripleDes.ofbSig, AArch64.abi,
    AArch64.argRegs] [fbFrameSat] using fbFrameSat

theorem cfbDecFrameSat_pre : ∃ s, (Spec.TripleDes.cfbDecryptContract AArch64.abi 1008).pre s := by
  implies_sat [Spec.TripleDes.cfbDecryptContract, Spec.TripleDes.cfbSig, Spec.TripleDes.ofbSig, AArch64.abi,
    AArch64.argRegs] [fbFrameSat] using fbFrameSat

theorem cfb8EncFrameSat_pre : ∃ s, (Spec.TripleDes.cfb8EncryptContract AArch64.abi 1008).pre s := by
  implies_sat [Spec.TripleDes.cfb8EncryptContract, Spec.TripleDes.cfb8Sig, AArch64.abi, AArch64.argRegs]
    [cfb8FrameSat] using cfb8FrameSat

theorem cfb8DecFrameSat_pre : ∃ s, (Spec.TripleDes.cfb8DecryptContract AArch64.abi 1008).pre s := by
  implies_sat [Spec.TripleDes.cfb8DecryptContract, Spec.TripleDes.cfb8Sig, AArch64.abi, AArch64.argRegs]
    [cfb8FrameSat] using cfb8FrameSat

/-- OFB with its working space on the stack. -/
theorem ofb_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 1008 .x4 125 ofb)
      (Spec.TripleDes.ofbContract AArch64.abi 1008) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.TripleDes.ofbSig) (nm := "scratch") (e := .u64)
    (n := 125) (post := Proof.TripleDes.ofbPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 1008) ofb_verified
    (by decide) (by decide) (by decide) (Proof.TripleDes.ofbPostOut_local _) ofbFrameSat_pre

/-- CFB64 encryption with its working space on the stack. -/
theorem cfbEncrypt_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 1008 .x4 125 cfbEncrypt)
      (Spec.TripleDes.cfbEncryptContract AArch64.abi 1008) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.TripleDes.cfbSig) (nm := "scratch") (e := .u64)
    (n := 125) (post := Proof.TripleDes.cfbEncPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 1008) cfbEncrypt_verified
    (by decide) (by decide) (by decide) (Proof.TripleDes.cfbEncPostOut_local _) cfbEncFrameSat_pre

/-- CFB64 decryption with its working space on the stack. -/
theorem cfbDecrypt_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 1008 .x4 125 cfbDecrypt)
      (Spec.TripleDes.cfbDecryptContract AArch64.abi 1008) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.TripleDes.cfbSig) (nm := "scratch") (e := .u64)
    (n := 125) (post := Proof.TripleDes.cfbDecPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 1008) cfbDecrypt_verified
    (by decide) (by decide) (by decide) (Proof.TripleDes.cfbDecPostOut_local _) cfbDecFrameSat_pre

/-- CFB8 encryption with its working space on the stack. -/
theorem cfb8Encrypt_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 1008 .x4 125 cfb8Encrypt)
      (Spec.TripleDes.cfb8EncryptContract AArch64.abi 1008) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.TripleDes.cfb8Sig) (nm := "scratch") (e := .u64)
    (n := 125) (post := Proof.TripleDes.cfb8EncPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 1008) cfb8Encrypt_verified
    (by decide) (by decide) (by decide) (Proof.TripleDes.cfb8EncPostOut_local _) cfb8EncFrameSat_pre

/-- CFB8 decryption with its working space on the stack. -/
theorem cfb8Decrypt_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 1008 .x4 125 cfb8Decrypt)
      (Spec.TripleDes.cfb8DecryptContract AArch64.abi 1008) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.TripleDes.cfb8Sig) (nm := "scratch") (e := .u64)
    (n := 125) (post := Proof.TripleDes.cfb8DecPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 1008) cfb8Decrypt_verified
    (by decide) (by decide) (by decide) (Proof.TripleDes.cfb8DecPostOut_local _) cfb8DecFrameSat_pre

end VG.Proof.TripleDes.AArch64
