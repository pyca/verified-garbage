module

import VerifiedGarbage.Proof.TripleDes.X86_64.ModeCore
meta import VerifiedGarbage.Proof.TripleDes.X86_64.ModeCore
import VerifiedGarbage.Proof.TripleDes.X86_64.CallPatch
meta import VerifiedGarbage.Proof.TripleDes.X86_64.CallPatch
import VerifiedGarbage.Proof.Modes.X86_64.Fb
meta import VerifiedGarbage.Proof.Modes.X86_64.Fb
import VerifiedGarbage.Proof.Modes.X86_64.Cfb8
meta import VerifiedGarbage.Proof.Modes.X86_64.Cfb8
public import VerifiedGarbage.Proof.TripleDes.FbScratch
meta import VerifiedGarbage.Proof.TripleDes.FbScratch
public import VerifiedGarbage.Proof.TripleDes.X86_64.FbLit
public import VerifiedGarbage.Proof.TripleDes.X86_64.BlockSum
meta import VerifiedGarbage.Proof.TripleDes.X86_64.BlockSum
meta import VerifiedGarbage.Proof.TripleDes.X86_64.FbLit
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.TripleDes.SboxTables
public import VerifiedGarbage.Proof.TripleDes.X86_64.ConstantTime
public import VerifiedGarbage.Proof.TripleDes.X86_64.Lit
public import VerifiedGarbage.Proof.TripleDes.X86_64.RoundLit
public import VerifiedGarbage.Spec.TripleDes.Cfb
public import VerifiedGarbage.Proof.Modes.Cfb8
public import VerifiedGarbage.Proof.Modes.Fb
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
public import VerifiedGarbage.Spec.Weierstrass
meta import VerifiedGarbage.Proof.Framework.Contract
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.Aes.Blocks
import VerifiedGarbage.Proof.AesCtr.Ctr32
import VerifiedGarbage.Proof.AesCtr.Spec
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.X86_64.Words
import VerifiedGarbage.Proof.Modes.Addr
import VerifiedGarbage.Proof.Modes.X86_64.CbcEncLoop
import VerifiedGarbage.Proof.Modes.X86_64.CbcGroup
import VerifiedGarbage.Proof.Modes.X86_64.Cfb8Loop
import VerifiedGarbage.Proof.Modes.X86_64.Cfb8Steps
import VerifiedGarbage.Proof.Modes.X86_64.Copy
import VerifiedGarbage.Proof.Modes.X86_64.Counter
import VerifiedGarbage.Proof.Modes.X86_64.Steps
import VerifiedGarbage.Proof.Modes.X86_64.Unchain
import VerifiedGarbage.Proof.Modes.X86_64.Words
import VerifiedGarbage.Proof.Rc2.Word
import VerifiedGarbage.Proof.Rc2.X86_64.Sse2Finish
import VerifiedGarbage.Proof.TripleDes.Permutation
import VerifiedGarbage.Proof.TripleDes.X86_64.Box
import VerifiedGarbage.Proof.TripleDes.X86_64.Pre
import VerifiedGarbage.Proof.TripleDes.X86_64.RoundBody
import VerifiedGarbage.Spec.Ctr.Contract
import VerifiedGarbage.Spec.TripleDes.Contract
meta import VerifiedGarbage.Proof.Aes.Blocks
meta import VerifiedGarbage.Proof.AesCtr.Ctr32
meta import VerifiedGarbage.Proof.AesCtr.Spec
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Mem
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.Frame
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Framework.X86_64.Syms
meta import VerifiedGarbage.Proof.Framework.X86_64.Words
meta import VerifiedGarbage.Proof.Modes.Addr
meta import VerifiedGarbage.Proof.Modes.X86_64.CbcEncLoop
meta import VerifiedGarbage.Proof.Modes.X86_64.CbcGroup
meta import VerifiedGarbage.Proof.Modes.X86_64.Cfb8Loop
meta import VerifiedGarbage.Proof.Modes.X86_64.Cfb8Steps
meta import VerifiedGarbage.Proof.Modes.X86_64.Copy
meta import VerifiedGarbage.Proof.Modes.X86_64.Counter
meta import VerifiedGarbage.Proof.Modes.X86_64.Steps
meta import VerifiedGarbage.Proof.Modes.X86_64.Unchain
meta import VerifiedGarbage.Proof.Modes.X86_64.Words
meta import VerifiedGarbage.Proof.Rc2.Word
meta import VerifiedGarbage.Proof.Rc2.X86_64.Sse2Finish
meta import VerifiedGarbage.Proof.TripleDes.Permutation
meta import VerifiedGarbage.Proof.TripleDes.X86_64.Box
meta import VerifiedGarbage.Proof.TripleDes.X86_64.Pre
meta import VerifiedGarbage.Proof.TripleDes.X86_64.RoundBody
meta import VerifiedGarbage.Spec.Ctr.Contract
meta import VerifiedGarbage.Spec.TripleDes.Cfb
meta import VerifiedGarbage.Spec.TripleDes.Contract

/-!
# Triple DES-OFB, -CFB64 and -CFB8 on x86-64 meet their contracts

`ofb_wp`, …: the modes' OFB, CFB and CFB8 (`Proof.Modes.X86_64.fb_wp`,
`cfb8_wp`) over Triple DES encryption's core (`dirCoreSpec .encrypt`), with
the specification's results (`Proof.Modes.ofb_of`, …). `ofb_verified`, …:
each is correct and constant time, by the taint analysis: the pointers, the
length and the stack pointer are public, and so is everything the code
computes from them; the IV is secret. `ofb_framed`, … run them with their
working space on the stack, zeroed on return: 976 bytes, the 121 words of
the scratch buffer and 8 more.
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.Impl.TripleDes.X86_64

/-- The precondition of the feedback modes on x86-64, with the data `len`
bytes long and the working space at `r8`. -/
def fbPre (len : State → Nat) (s : State) : Prop :=
  let sched : Region := ⟨s.gpr .rdi, 384⟩
  let iv : Region := ⟨s.gpr .rsi, 8⟩
  let data : Region := ⟨s.gpr .rdx, len s⟩
  let scratch : Region := ⟨s.gpr .r8, 8 * 121⟩
  let ret : Region := ⟨s.gpr .rsp, 8⟩
  s.rd = [sched] ∧ s.wr = [iv, data, scratch] ∧ sched.Disjoint iv ∧ sched.Disjoint data ∧
    sched.Disjoint scratch ∧ iv.Disjoint data ∧ iv.Disjoint scratch ∧ data.Disjoint scratch ∧
    ret.Disjoint iv ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
    (s.gpr .rdi).toNat + 384 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 8 ≤ 2 ^ 64 ∧
    (s.gpr .rdx).toNat + len s ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + 8 * 121 ≤ 2 ^ 64

/-- The public arguments. -/
def fbPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `n` blocks. -/
abbrev blkLen (s : State) : Nat := 8 * (s.gpr .rcx).toNat

/-- `len` bytes. -/
abbrev byteLen (s : State) : Nat := (s.gpr .rcx).toNat

/-- The schedule, IV and data of `s`'s arguments. -/
abbrev ciphOf (s : State) : Spec.Cbc.Cipher := Spec.TripleDes.cipher (Spec.TripleDes.scheduleAt s.mem (s.gpr .rdi))
abbrev ivOf (s : State) : List Byte := Spec.TripleDes.bytesAt s.mem (s.gpr .rsi) 8
abbrev blocksOf (s : State) (m : Mem) : List (List Byte) := Spec.TripleDes.cbcBlocksAt m (s.gpr .rdx) (s.gpr .rcx).toNat

def ofbX86_64 : Contract isa where
  pre := fbPre blkLen
  post s s' := blocksOf s s'.mem = Spec.Ofb.crypt (ciphOf s) (ivOf s) (blocksOf s s.mem) ∧
    Spec.TripleDes.bytesAt s'.mem (s.gpr .rsi) 8 = Spec.Ofb.next (ciphOf s) (ivOf s) (s.gpr .rcx).toNat
  pub := fbPub

def cfbEncX86_64 : Contract isa where
  pre := fbPre blkLen
  post s s' := blocksOf s s'.mem = Spec.Cfb.encrypt (ciphOf s) (ivOf s) (blocksOf s s.mem) ∧
    Spec.TripleDes.bytesAt s'.mem (s.gpr .rsi) 8 =
      Spec.Cbc.next (ivOf s) (Spec.Cfb.encrypt (ciphOf s) (ivOf s) (blocksOf s s.mem))
  pub := fbPub

def cfbDecX86_64 : Contract isa where
  pre := fbPre blkLen
  post s s' := blocksOf s s'.mem = Spec.Cfb.decrypt (ciphOf s) (ivOf s) (blocksOf s s.mem) ∧
    Spec.TripleDes.bytesAt s'.mem (s.gpr .rsi) 8 = Spec.Cbc.next (ivOf s) (blocksOf s s.mem)
  pub := fbPub

def cfb8EncX86_64 : Contract isa where
  pre := fbPre byteLen
  post s s' := Spec.TripleDes.bytesAt s'.mem (s.gpr .rdx) (byteLen s) =
      Spec.Cfb8.encrypt (ciphOf s) (ivOf s) (Spec.TripleDes.bytesAt s.mem (s.gpr .rdx) (byteLen s)) ∧
    Spec.TripleDes.bytesAt s'.mem (s.gpr .rsi) 8 = Spec.Cfb8.next (ivOf s)
      (Spec.Cfb8.encrypt (ciphOf s) (ivOf s) (Spec.TripleDes.bytesAt s.mem (s.gpr .rdx) (byteLen s)))
  pub := fbPub

def cfb8DecX86_64 : Contract isa where
  pre := fbPre byteLen
  post s s' := Spec.TripleDes.bytesAt s'.mem (s.gpr .rdx) (byteLen s) =
      Spec.Cfb8.decrypt (ciphOf s) (ivOf s) (Spec.TripleDes.bytesAt s.mem (s.gpr .rdx) (byteLen s)) ∧
    Spec.TripleDes.bytesAt s'.mem (s.gpr .rsi) 8 =
      Spec.Cfb8.next (ivOf s) (Spec.TripleDes.bytesAt s.mem (s.gpr .rdx) (byteLen s))
  pub := fbPub

/-- What the modes' OFB and CFB give, for a mode `mo`: the data and the
IV as `fbOut` and `fbIn`, keeping the callee-saved registers. -/
theorem fb_wp' (mo : Impl.Modes.FbMode) {s₀ : State} (hp : fbPre blkLen s₀) :
    WP isa ((dirCore .encrypt).fb mo fbRegs) s₀ fun s' => gprPreserved s₀ s' ∧
      Modes.blocksOf 8 s'.mem (s₀.gpr .rdx) (s₀.gpr .rcx).toNat =
        (List.range (s₀.gpr .rcx).toNat).map (Modes.fbOut mo 8 (ciphOf s₀) s₀.mem (s₀.gpr .rdx) (ivOf s₀)) ∧
      Spec.TripleDes.bytesAt s'.mem (s₀.gpr .rsi) 8 = Modes.fbIn mo 8 (ciphOf s₀) s₀.mem (s₀.gpr .rdx) (ivOf s₀) (s₀.gpr .rcx).toNat := by
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, dRV, dRD, dRS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .r8, 8 * 121⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.X86_64.fb_wp (dirCoreSpec .encrypt) mo (r := fbRegs)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .r8) (P := s₀.gpr .rsi) (D := s₀.gpr .rdx) (n := (s₀.gpr .rcx).toNat)
    (k := Spec.TripleDes.scheduleAt s₀.mem (s₀.gpr .rdi)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp [Nat.mul_comm]) dVS dDS dVD fitD
    ⟨s₀.gpr .rdi, rfl, rfl, by rw [hrd]; simp, fitK, fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dKS⟩ ⟨Modes.X86_64.keepsIv_of_scal (by lit_decide), Modes.X86_64.keepsIv_of_scal (by lit_decide)⟩)
    fun s' ⟨hcs, hdata, hiv, hf, _, _⟩ =>
    ⟨⟨hcs, ?_⟩, by rw [dirCore_bw, Nat.mul_one] at hdata hiv; exact ⟨hdata, hiv⟩⟩
  rw [VG.Proof.Modes.X86_64.stkList_eq_nil rfl, List.append_nil] at hf
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact dRS
  · exact dRD
  · exact dRV

/-- What the modes' CFB8 gives: the data and the input block as `cfb8Out`
and `cfb8In`, keeping the callee-saved registers. -/
theorem cfb8_wp' (enc : Bool) {s₀ : State} (hp : fbPre byteLen s₀) :
    WP isa ((dirCore .encrypt).cfb8 enc fbRegs) s₀ fun s' => gprPreserved s₀ s' ∧
      Spec.TripleDes.bytesAt s'.mem (s₀.gpr .rdx) (byteLen s₀) =
        (List.range (byteLen s₀)).map (Modes.cfb8Out enc (ciphOf s₀) s₀.mem (s₀.gpr .rdx) (ivOf s₀)) ∧
      Spec.TripleDes.bytesAt s'.mem (s₀.gpr .rsi) 8 =
        Modes.cfb8In enc (ciphOf s₀) s₀.mem (s₀.gpr .rdx) (ivOf s₀) (byteLen s₀) := by
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, dRV, dRD, dRS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .r8, 8 * 121⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.X86_64.cfb8_wp (dirCoreSpec .encrypt) enc (r := fbRegs)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .r8) (P := s₀.gpr .rsi) (D := s₀.gpr .rdx) (n := (s₀.gpr .rcx).toNat)
    (k := Spec.TripleDes.scheduleAt s₀.mem (s₀.gpr .rdi)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp) dVS dDS dVD fitD
    ⟨s₀.gpr .rdi, rfl, rfl, by rw [hrd]; simp, fitK, fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dKS⟩ ⟨Modes.X86_64.keepsIv_of_scal (by lit_decide), Modes.X86_64.keepsIv_of_scal (by lit_decide)⟩)
    fun s' ⟨hcs, hdata, hiv, hf, _, _⟩ =>
    ⟨⟨hcs, ?_⟩, by rw [dirCore_bw, Nat.mul_one] at hdata hiv; exact ⟨hdata, hiv⟩⟩
  rw [VG.Proof.Modes.X86_64.stkList_eq_nil rfl, List.append_nil] at hf
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact dRS
  · exact dRD
  · exact dRV

theorem ofb_wp {s₀ : State} (hp : ofbX86_64.pre s₀) :
    WP isa ofbI s₀ fun s' => gprPreserved s₀ s' ∧ ofbX86_64.post s₀ s' :=
  WP.mono (fb_wp' .ofb hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.ofb_of 8 (ciphOf s₀) s₀.mem (s₀.gpr .rdx) (ivOf s₀) (s₀.gpr .rcx).toNat
    refine ⟨hg, ?_, by rw [hv, h2]⟩
    change Spec.TripleDes.cbcBlocksAt _ _ _ = Spec.Ofb.crypt _ _ (Spec.TripleDes.cbcBlocksAt _ _ _)
    rw [cbcBlocksAt_eq, cbcBlocksAt_eq, hd, h1]

theorem cfbEncrypt_wp {s₀ : State} (hp : cfbEncX86_64.pre s₀) :
    WP isa cfbEncryptI s₀ fun s' => gprPreserved s₀ s' ∧ cfbEncX86_64.post s₀ s' :=
  WP.mono (fb_wp' .cfbEnc hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfbEnc_of 8 (ciphOf s₀) s₀.mem (s₀.gpr .rdx) (ivOf s₀) (s₀.gpr .rcx).toNat
    refine ⟨hg, ?_, ?_⟩
    · change Spec.TripleDes.cbcBlocksAt _ _ _ = Spec.Cfb.encrypt _ _ (Spec.TripleDes.cbcBlocksAt _ _ _)
      rw [cbcBlocksAt_eq, cbcBlocksAt_eq, hd, h1]
    · change _ = Spec.Cbc.next _ (Spec.Cfb.encrypt _ _ (Spec.TripleDes.cbcBlocksAt _ _ _))
      rw [hv, h2, cbcBlocksAt_eq]

theorem cfbDecrypt_wp {s₀ : State} (hp : cfbDecX86_64.pre s₀) :
    WP isa cfbDecryptI s₀ fun s' => gprPreserved s₀ s' ∧ cfbDecX86_64.post s₀ s' :=
  WP.mono (fb_wp' .cfbDec hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfbDec_of 8 (ciphOf s₀) s₀.mem (s₀.gpr .rdx) (ivOf s₀) (s₀.gpr .rcx).toNat
    refine ⟨hg, ?_, ?_⟩
    · change Spec.TripleDes.cbcBlocksAt _ _ _ = Spec.Cfb.decrypt _ _ (Spec.TripleDes.cbcBlocksAt _ _ _)
      rw [cbcBlocksAt_eq, cbcBlocksAt_eq, hd, h1]
    · change _ = Spec.Cbc.next _ (Spec.TripleDes.cbcBlocksAt _ _ _)
      rw [hv, h2, cbcBlocksAt_eq]

theorem ivOf_ne (s : State) : ivOf s ≠ [] := by simp [ivOf, Spec.TripleDes.bytesAt]

theorem cfb8Encrypt_wp {s₀ : State} (hp : cfb8EncX86_64.pre s₀) :
    WP isa cfb8EncryptI s₀ fun s' => gprPreserved s₀ s' ∧ cfb8EncX86_64.post s₀ s' :=
  WP.mono (cfb8_wp' true hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfb8Enc_of (ciphOf s₀) s₀.mem (byteLen s₀) (s₀.gpr .rdx) (ivOf s₀) (ivOf_ne s₀)
    exact ⟨hg, hd.trans h1, hv.trans h2⟩

theorem cfb8Decrypt_wp {s₀ : State} (hp : cfb8DecX86_64.pre s₀) :
    WP isa cfb8DecryptI s₀ fun s' => gprPreserved s₀ s' ∧ cfb8DecX86_64.post s₀ s' :=
  WP.mono (cfb8_wp' false hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfb8Dec_of (ciphOf s₀) s₀.mem (byteLen s₀) (s₀.gpr .rdx) (ivOf s₀) (ivOf_ne s₀)
    exact ⟨hg, hd.trans h1, hv.trans h2⟩

/-! ## Constant time -/

def fbTaint : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .r8, .rsp], flags := false,
    lens := [8, 0, 8 * 121], bases := [(.r8, 2, 0)] }

theorem fbTaint_wf {len : State → Nat} (s : State) (hs : fbPre len s) : Taint.Wf fbTaint s := by
  obtain ⟨_, hwr, _, _, _, dVD, dVS, dDS, _, _, _, _, fitV, fitD, fitB⟩ := hs
  refine ⟨fun _ => ?_, ?_⟩
  · rw [hwr]
    refine ⟨?_, ?_, ?_⟩
    · exact List.Forall₂.cons (by change 8 ≤ 8; omega) (List.Forall₂.cons (by change 0 ≤ len s; omega)
        (List.Forall₂.cons (by change 8 * 121 ≤ 8 * 121; omega) List.Forall₂.nil))
    · refine List.Pairwise.cons (fun r hr => ?_) (List.Pairwise.cons (fun r hr => ?_)
        (List.Pairwise.cons (by simp) List.Pairwise.nil))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact dVD
        · exact dVS
      · obtain rfl := List.mem_singleton.mp hr; exact dDS
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · change 8 ≤ 2 ^ 64; omega
      · change len s ≤ 2 ^ 64; omega
      · change 8 * 121 ≤ 2 ^ 64; omega
  · intro p hp
    simp only [fbTaint, List.mem_singleton] at hp
    subst p
    unfold Taint.region
    rw [hwr]
    change s.gpr .r8 = s.gpr .r8 + (0 : BitVec 64)
    exact (BitVec.add_zero _).symm

theorem fbTaint_agree {len : State → Nat} (hlen : ∀ s t, s.gpr .rcx = t.gpr .rcx → len s = len t) (s t : State)
    (hs : fbPre len s) (ht : fbPre len t) (hp : fbPub s t) : X86_64.Taint.Agree fbTaint s t := by
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hp
  refine ⟨?_, ?_, fbTaint_wf s hs, fbTaint_wf t ht, ?_, ?_, ?_, X86_64.Taint.noXr⟩
  · constructor
    · intro r hr
      simp only [fbTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      exacts [p1, p2, p3, p4, p5, p6]
    · intro h
      change false = true at h
      contradiction
  · intro _
    rw [hs.2.1, ht.2.1, p2, p3, p5, hlen s t p4]
  · intro slot hslot
    change slot ∈ ([] : List (Nat × Nat × Nat)) at hslot
    exact False.elim (List.not_mem_nil hslot)
  · intro slot hslot
    change slot ∈ ([] : List (Nat × Nat × Nat)) at hslot
    exact False.elim (List.not_mem_nil hslot)
  · intro r hr
    simp only [fbTaint, RegSet.not_mem_empty] at hr

theorem blkLen_congr : ∀ s t : State, s.gpr .rcx = t.gpr .rcx → blkLen s = blkLen t := fun _ _ h => by
  simp only [blkLen, h]

theorem byteLen_congr : ∀ s t : State, s.gpr .rcx = t.gpr .rcx → byteLen s = byteLen t := fun _ _ h => by
  simp only [byteLen, h]

/-- A state satisfying the precondition (one block, or one byte). -/
def fbSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 1 | .r8 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 8⟩, ⟨0x4000, 8 * 121⟩]

def cfb8Sat : State := { fbSat with wr := [⟨0x2000, 8⟩, ⟨0x3000, 1⟩, ⟨0x4000, 8 * 121⟩] }

theorem ofb_correct (s : State) (hs : ofbX86_64.pre s) :
    ∃ t s', Exec isa ofbI s t s' ∧ abiPreserved s s' ∧ ofbX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hpost⟩ := ofb_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec (c := ofbI) (by lit_decide) he hg, hpost⟩

theorem ofb_ct : ConstantTime isa ofbX86_64.pre ofbX86_64.pub ofb := by
  obtain ⟨_, h⟩ : ∃ h, (taintS.check fbTaint ofb h).isSome = true :=
    by taint_decide_sum [encSum]
  exact VG.Taint.constantTime (A := taintS) fbTaint (fbTaint_agree blkLen_congr) h

theorem ofb_implies : ofbX86_64.Implies (Proof.TripleDes.fbScratchContract X86_64.abi 121 Proof.TripleDes.ofbPost) := by
    sig_implies [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig,
      Proof.TripleDes.ofbPost, ofbX86_64, fbPre, fbPub, X86_64.abi, X86_64.argRegs] [fbSat] using fbSat

theorem ofb_implies8 : ofbX86_64.Implies (Proof.TripleDes.fbScratchContract X86_64.abi 121 Proof.TripleDes.ofbPost 8) :=
  ofb_implies.stack8_abi (by
    sig_implies_sat [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, X86_64.abi, X86_64.argRegs, fbSat] [fbSat]
      using fbSat)

/-- The data and the IV are apart from the call's return address. -/
theorem ofb_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64)
    (hs : (Proof.TripleDes.fbScratchContract X86_64.abi 121 Proof.TripleDes.ofbPost 8).pre s) (hp : ofbX86_64.post s b) :
    ofbX86_64.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  obtain ⟨-, hwr, -, -, -, -, -, -, -, -, -, -, fitI, fitD, -⟩ := ofb_implies8.pre s hs
  have hbD := Clear.wr_bytes (Sig.clear_of_pre hs) (p := s.gpr .rdx) (n := 8 * (s.gpr .rcx).toNat)
    (by rw [hwr]; simp) (by simp only [blkLen] at fitD; omega)
  have hbI := Clear.wr_bytes (Sig.clear_of_pre hs) (p := s.gpr .rsi) (n := 8) (by rw [hwr]; simp) (by omega)
  obtain ⟨h₁, h₂⟩ := hp
  refine ⟨?_, ?_⟩
  · show Spec.TripleDes.cbcBlocksAt _ _ _ = _
    rw [cbcBlocksAt_congr (patch_mem hbD)]; exact h₁
  · rw [bytesAt_congr (patch_mem hbI)]; exact h₂

theorem ofb_inline : ofb.inline = ofbI := rfl

theorem ofb_verified :
    Verified X86_64.target ofb (Proof.TripleDes.fbScratchContract X86_64.abi 121 Proof.TripleDes.ofbPost 8) :=
  Verified.of_inline_ct (by lit_decide) (fun s hs => by rw [ofb_inline]; exact ofb_correct s hs) ofb_ct
    ofb_implies8 (fun _ h => Sig.clear_of_pre h) ofb_patch

theorem cfbEncrypt_correct (s : State) (hs : cfbEncX86_64.pre s) :
    ∃ t s', Exec isa cfbEncryptI s t s' ∧ abiPreserved s s' ∧ cfbEncX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hpost⟩ := cfbEncrypt_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec (c := cfbEncryptI) (by lit_decide) he hg, hpost⟩

theorem cfbEncrypt_ct : ConstantTime isa cfbEncX86_64.pre cfbEncX86_64.pub cfbEncrypt := by
  obtain ⟨_, h⟩ : ∃ h, (taintS.check fbTaint cfbEncrypt h).isSome = true :=
    by taint_decide_sum [encSum]
  exact VG.Taint.constantTime (A := taintS) fbTaint (fbTaint_agree blkLen_congr) h

theorem cfbEncrypt_implies : cfbEncX86_64.Implies (Proof.TripleDes.fbScratchContract X86_64.abi 121 Proof.TripleDes.cfbEncPost) := by
    sig_implies [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig,
      Proof.TripleDes.cfbEncPost, cfbEncX86_64, fbPre, fbPub, X86_64.abi, X86_64.argRegs] [fbSat] using fbSat

theorem cfbEncrypt_implies8 : cfbEncX86_64.Implies (Proof.TripleDes.fbScratchContract X86_64.abi 121 Proof.TripleDes.cfbEncPost 8) :=
  cfbEncrypt_implies.stack8_abi (by
    sig_implies_sat [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, X86_64.abi, X86_64.argRegs, fbSat] [fbSat]
      using fbSat)

/-- The data and the IV are apart from the call's return address. -/
theorem cfbEncrypt_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64)
    (hs : (Proof.TripleDes.fbScratchContract X86_64.abi 121 Proof.TripleDes.cfbEncPost 8).pre s) (hp : cfbEncX86_64.post s b) :
    cfbEncX86_64.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  obtain ⟨-, hwr, -, -, -, -, -, -, -, -, -, -, fitI, fitD, -⟩ := cfbEncrypt_implies8.pre s hs
  have hbD := Clear.wr_bytes (Sig.clear_of_pre hs) (p := s.gpr .rdx) (n := 8 * (s.gpr .rcx).toNat)
    (by rw [hwr]; simp) (by simp only [blkLen] at fitD; omega)
  have hbI := Clear.wr_bytes (Sig.clear_of_pre hs) (p := s.gpr .rsi) (n := 8) (by rw [hwr]; simp) (by omega)
  obtain ⟨h₁, h₂⟩ := hp
  refine ⟨?_, ?_⟩
  · show Spec.TripleDes.cbcBlocksAt _ _ _ = _
    rw [cbcBlocksAt_congr (patch_mem hbD)]; exact h₁
  · rw [bytesAt_congr (patch_mem hbI)]; exact h₂

theorem cfbEncrypt_inline : cfbEncrypt.inline = cfbEncryptI := rfl

theorem cfbEncrypt_verified :
    Verified X86_64.target cfbEncrypt (Proof.TripleDes.fbScratchContract X86_64.abi 121 Proof.TripleDes.cfbEncPost 8) :=
  Verified.of_inline_ct (by lit_decide) (fun s hs => by rw [cfbEncrypt_inline]; exact cfbEncrypt_correct s hs) cfbEncrypt_ct
    cfbEncrypt_implies8 (fun _ h => Sig.clear_of_pre h) cfbEncrypt_patch

theorem cfbDecrypt_correct (s : State) (hs : cfbDecX86_64.pre s) :
    ∃ t s', Exec isa cfbDecryptI s t s' ∧ abiPreserved s s' ∧ cfbDecX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hpost⟩ := cfbDecrypt_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec (c := cfbDecryptI) (by lit_decide) he hg, hpost⟩

theorem cfbDecrypt_ct : ConstantTime isa cfbDecX86_64.pre cfbDecX86_64.pub cfbDecrypt := by
  obtain ⟨_, h⟩ : ∃ h, (taintS.check fbTaint cfbDecrypt h).isSome = true :=
    by taint_decide_sum [encSum]
  exact VG.Taint.constantTime (A := taintS) fbTaint (fbTaint_agree blkLen_congr) h

theorem cfbDecrypt_implies : cfbDecX86_64.Implies (Proof.TripleDes.fbScratchContract X86_64.abi 121 Proof.TripleDes.cfbDecPost) := by
    sig_implies [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig,
      Proof.TripleDes.cfbDecPost, cfbDecX86_64, fbPre, fbPub, X86_64.abi, X86_64.argRegs] [fbSat] using fbSat

theorem cfbDecrypt_implies8 : cfbDecX86_64.Implies (Proof.TripleDes.fbScratchContract X86_64.abi 121 Proof.TripleDes.cfbDecPost 8) :=
  cfbDecrypt_implies.stack8_abi (by
    sig_implies_sat [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, X86_64.abi, X86_64.argRegs, fbSat] [fbSat]
      using fbSat)

/-- The data and the IV are apart from the call's return address. -/
theorem cfbDecrypt_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64)
    (hs : (Proof.TripleDes.fbScratchContract X86_64.abi 121 Proof.TripleDes.cfbDecPost 8).pre s) (hp : cfbDecX86_64.post s b) :
    cfbDecX86_64.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  obtain ⟨-, hwr, -, -, -, -, -, -, -, -, -, -, fitI, fitD, -⟩ := cfbDecrypt_implies8.pre s hs
  have hbD := Clear.wr_bytes (Sig.clear_of_pre hs) (p := s.gpr .rdx) (n := 8 * (s.gpr .rcx).toNat)
    (by rw [hwr]; simp) (by simp only [blkLen] at fitD; omega)
  have hbI := Clear.wr_bytes (Sig.clear_of_pre hs) (p := s.gpr .rsi) (n := 8) (by rw [hwr]; simp) (by omega)
  obtain ⟨h₁, h₂⟩ := hp
  refine ⟨?_, ?_⟩
  · show Spec.TripleDes.cbcBlocksAt _ _ _ = _
    rw [cbcBlocksAt_congr (patch_mem hbD)]; exact h₁
  · rw [bytesAt_congr (patch_mem hbI)]; exact h₂

theorem cfbDecrypt_inline : cfbDecrypt.inline = cfbDecryptI := rfl

theorem cfbDecrypt_verified :
    Verified X86_64.target cfbDecrypt (Proof.TripleDes.fbScratchContract X86_64.abi 121 Proof.TripleDes.cfbDecPost 8) :=
  Verified.of_inline_ct (by lit_decide) (fun s hs => by rw [cfbDecrypt_inline]; exact cfbDecrypt_correct s hs) cfbDecrypt_ct
    cfbDecrypt_implies8 (fun _ h => Sig.clear_of_pre h) cfbDecrypt_patch

theorem cfb8Encrypt_correct (s : State) (hs : cfb8EncX86_64.pre s) :
    ∃ t s', Exec isa cfb8EncryptI s t s' ∧ abiPreserved s s' ∧ cfb8EncX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hpost⟩ := cfb8Encrypt_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec (c := cfb8EncryptI) (by lit_decide) he hg, hpost⟩

theorem cfb8Encrypt_ct : ConstantTime isa cfb8EncX86_64.pre cfb8EncX86_64.pub cfb8Encrypt := by
  obtain ⟨_, h⟩ : ∃ h, (taintS.check fbTaint cfb8Encrypt h).isSome = true :=
    by taint_decide_sum [encSum]
  exact VG.Taint.constantTime (A := taintS) fbTaint (fbTaint_agree byteLen_congr) h

theorem cfb8Encrypt_implies : cfb8EncX86_64.Implies (Proof.TripleDes.cfb8ScratchContract X86_64.abi 121 Proof.TripleDes.cfb8EncPost) := by
    sig_implies [Proof.TripleDes.cfb8ScratchContract, Proof.TripleDes.cfb8ScratchSig, Spec.TripleDes.cfb8Sig,
      Proof.TripleDes.cfb8EncPost, cfb8EncX86_64, fbPre, fbPub, X86_64.abi, X86_64.argRegs] [cfb8Sat] using cfb8Sat

theorem cfb8Encrypt_implies8 : cfb8EncX86_64.Implies (Proof.TripleDes.cfb8ScratchContract X86_64.abi 121 Proof.TripleDes.cfb8EncPost 8) :=
  cfb8Encrypt_implies.stack8_abi (by
    sig_implies_sat [Proof.TripleDes.cfb8ScratchContract, Proof.TripleDes.cfb8ScratchSig, X86_64.abi, X86_64.argRegs, cfb8Sat] [cfb8Sat]
      using cfb8Sat)

/-- The data and the IV are apart from the call's return address. -/
theorem cfb8Encrypt_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64)
    (hs : (Proof.TripleDes.cfb8ScratchContract X86_64.abi 121 Proof.TripleDes.cfb8EncPost 8).pre s) (hp : cfb8EncX86_64.post s b) :
    cfb8EncX86_64.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  obtain ⟨-, hwr, -, -, -, -, -, -, -, -, -, -, fitI, fitD, -⟩ := cfb8Encrypt_implies8.pre s hs
  have hbD := Clear.wr_bytes (Sig.clear_of_pre hs) (p := s.gpr .rdx) (n := (s.gpr .rcx).toNat)
    (by rw [hwr]; simp) (by omega)
  have hbI := Clear.wr_bytes (Sig.clear_of_pre hs) (p := s.gpr .rsi) (n := 8) (by rw [hwr]; simp) (by omega)
  obtain ⟨h₁, h₂⟩ := hp
  refine ⟨?_, ?_⟩
  · rw [bytesAt_congr (patch_mem hbD)]; exact h₁
  · rw [bytesAt_congr (patch_mem hbI)]; exact h₂

theorem cfb8Encrypt_inline : cfb8Encrypt.inline = cfb8EncryptI := rfl

theorem cfb8Encrypt_verified :
    Verified X86_64.target cfb8Encrypt (Proof.TripleDes.cfb8ScratchContract X86_64.abi 121 Proof.TripleDes.cfb8EncPost 8) :=
  Verified.of_inline_ct (by lit_decide) (fun s hs => by rw [cfb8Encrypt_inline]; exact cfb8Encrypt_correct s hs) cfb8Encrypt_ct
    cfb8Encrypt_implies8 (fun _ h => Sig.clear_of_pre h) cfb8Encrypt_patch

theorem cfb8Decrypt_correct (s : State) (hs : cfb8DecX86_64.pre s) :
    ∃ t s', Exec isa cfb8DecryptI s t s' ∧ abiPreserved s s' ∧ cfb8DecX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hpost⟩ := cfb8Decrypt_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec (c := cfb8DecryptI) (by lit_decide) he hg, hpost⟩

theorem cfb8Decrypt_ct : ConstantTime isa cfb8DecX86_64.pre cfb8DecX86_64.pub cfb8Decrypt := by
  obtain ⟨_, h⟩ : ∃ h, (taintS.check fbTaint cfb8Decrypt h).isSome = true :=
    by taint_decide_sum [encSum]
  exact VG.Taint.constantTime (A := taintS) fbTaint (fbTaint_agree byteLen_congr) h

theorem cfb8Decrypt_implies : cfb8DecX86_64.Implies (Proof.TripleDes.cfb8ScratchContract X86_64.abi 121 Proof.TripleDes.cfb8DecPost) := by
    sig_implies [Proof.TripleDes.cfb8ScratchContract, Proof.TripleDes.cfb8ScratchSig, Spec.TripleDes.cfb8Sig,
      Proof.TripleDes.cfb8DecPost, cfb8DecX86_64, fbPre, fbPub, X86_64.abi, X86_64.argRegs] [cfb8Sat] using cfb8Sat

theorem cfb8Decrypt_implies8 : cfb8DecX86_64.Implies (Proof.TripleDes.cfb8ScratchContract X86_64.abi 121 Proof.TripleDes.cfb8DecPost 8) :=
  cfb8Decrypt_implies.stack8_abi (by
    sig_implies_sat [Proof.TripleDes.cfb8ScratchContract, Proof.TripleDes.cfb8ScratchSig, X86_64.abi, X86_64.argRegs, cfb8Sat] [cfb8Sat]
      using cfb8Sat)

/-- The data and the IV are apart from the call's return address. -/
theorem cfb8Decrypt_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64)
    (hs : (Proof.TripleDes.cfb8ScratchContract X86_64.abi 121 Proof.TripleDes.cfb8DecPost 8).pre s) (hp : cfb8DecX86_64.post s b) :
    cfb8DecX86_64.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  obtain ⟨-, hwr, -, -, -, -, -, -, -, -, -, -, fitI, fitD, -⟩ := cfb8Decrypt_implies8.pre s hs
  have hbD := Clear.wr_bytes (Sig.clear_of_pre hs) (p := s.gpr .rdx) (n := (s.gpr .rcx).toNat)
    (by rw [hwr]; simp) (by omega)
  have hbI := Clear.wr_bytes (Sig.clear_of_pre hs) (p := s.gpr .rsi) (n := 8) (by rw [hwr]; simp) (by omega)
  obtain ⟨h₁, h₂⟩ := hp
  refine ⟨?_, ?_⟩
  · rw [bytesAt_congr (patch_mem hbD)]; exact h₁
  · rw [bytesAt_congr (patch_mem hbI)]; exact h₂

theorem cfb8Decrypt_inline : cfb8Decrypt.inline = cfb8DecryptI := rfl

theorem cfb8Decrypt_verified :
    Verified X86_64.target cfb8Decrypt (Proof.TripleDes.cfb8ScratchContract X86_64.abi 121 Proof.TripleDes.cfb8DecPost 8) :=
  Verified.of_inline_ct (by lit_decide) (fun s hs => by rw [cfb8Decrypt_inline]; exact cfb8Decrypt_correct s hs) cfb8Decrypt_ct
    cfb8Decrypt_implies8 (fun _ h => Sig.clear_of_pre h) cfb8Decrypt_patch

/-- OFB with its working space on the stack. -/
theorem ofb_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 ofb)
      (Spec.TripleDes.ofbContract X86_64.abi 984) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.TripleDes.ofbSig) (nm := "scratch") (e := .u64)
    (n := 121) (post := Proof.TripleDes.ofbPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 976) ofb_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) (by decide)
    (Proof.TripleDes.ofbPostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

/-- CFB64 encryption with its working space on the stack. -/
theorem cfbEncrypt_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 cfbEncrypt)
      (Spec.TripleDes.cfbEncryptContract X86_64.abi 984) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.TripleDes.cfbSig) (nm := "scratch") (e := .u64)
    (n := 121) (post := Proof.TripleDes.cfbEncPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 976) cfbEncrypt_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) (by decide)
    (Proof.TripleDes.cfbEncPostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

/-- CFB64 decryption with its working space on the stack. -/
theorem cfbDecrypt_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 cfbDecrypt)
      (Spec.TripleDes.cfbDecryptContract X86_64.abi 984) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.TripleDes.cfbSig) (nm := "scratch") (e := .u64)
    (n := 121) (post := Proof.TripleDes.cfbDecPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 976) cfbDecrypt_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) (by decide)
    (Proof.TripleDes.cfbDecPostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

/-- CFB8 encryption with its working space on the stack. -/
theorem cfb8Encrypt_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 cfb8Encrypt)
      (Spec.TripleDes.cfb8EncryptContract X86_64.abi 984) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.TripleDes.cfb8Sig) (nm := "scratch") (e := .u64)
    (n := 121) (post := Proof.TripleDes.cfb8EncPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 976) cfb8Encrypt_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) (by decide)
    (Proof.TripleDes.cfb8EncPostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

/-- CFB8 decryption with its working space on the stack. -/
theorem cfb8Decrypt_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 cfb8Decrypt)
      (Spec.TripleDes.cfb8DecryptContract X86_64.abi 984) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.TripleDes.cfb8Sig) (nm := "scratch") (e := .u64)
    (n := 121) (post := Proof.TripleDes.cfb8DecPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 976) cfb8Decrypt_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) (by decide)
    (Proof.TripleDes.cfb8DecPostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.TripleDes.X86_64
