module

import VerifiedGarbage.Proof.Blowfish.X86_64.ModeCore
meta import VerifiedGarbage.Proof.Blowfish.X86_64.ModeCore
import VerifiedGarbage.Proof.Modes.X86_64.Fb
meta import VerifiedGarbage.Proof.Modes.X86_64.Fb
public import VerifiedGarbage.Proof.Blowfish.FbScratch
meta import VerifiedGarbage.Proof.Blowfish.FbScratch
import VerifiedGarbage.Proof.Blowfish.X86_64.ModesLit
meta import VerifiedGarbage.Proof.Blowfish.X86_64.ModesLit
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Blowfish.X86_64.Modes
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.Modes.Fb
public import VerifiedGarbage.Spec.Blowfish.Cfb
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Proof.Framework.TaintSum
public import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Aes.Blocks
import VerifiedGarbage.Proof.AesCtr.Ctr32
import VerifiedGarbage.Proof.AesCtr.Spec
import VerifiedGarbage.Proof.Blowfish.Schedule
import VerifiedGarbage.Proof.Blowfish.X86_64.Block
import VerifiedGarbage.Proof.Blowfish.X86_64.Combine
import VerifiedGarbage.Proof.Blowfish.X86_64.Ecb
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.LaneSse
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.X86_64.TaintMono
import VerifiedGarbage.Proof.Framework.X86_64.Words
import VerifiedGarbage.Proof.Modes.Addr
import VerifiedGarbage.Proof.Modes.X86_64.CbcEncLoop
import VerifiedGarbage.Proof.Modes.X86_64.CbcGroup
import VerifiedGarbage.Proof.Modes.X86_64.Copy
import VerifiedGarbage.Proof.Modes.X86_64.Counter
import VerifiedGarbage.Proof.Modes.X86_64.KeepIv
import VerifiedGarbage.Proof.Modes.X86_64.Steps
import VerifiedGarbage.Proof.Modes.X86_64.Unchain
import VerifiedGarbage.Proof.Modes.X86_64.Words
import VerifiedGarbage.Spec.Blowfish.Contract
import VerifiedGarbage.Spec.Ctr.Contract
import VerifiedGarbage.Spec.Rc2
meta import VerifiedGarbage.Proof.Aes.Blocks
meta import VerifiedGarbage.Proof.AesCtr.Ctr32
meta import VerifiedGarbage.Proof.AesCtr.Spec
meta import VerifiedGarbage.Proof.Blowfish.Schedule
meta import VerifiedGarbage.Proof.Blowfish.X86_64.Block
meta import VerifiedGarbage.Proof.Blowfish.X86_64.Combine
meta import VerifiedGarbage.Proof.Blowfish.X86_64.Ecb
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Mem
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.Frame
meta import VerifiedGarbage.Proof.Framework.X86_64.LaneSse
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Framework.X86_64.Syms
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintMono
meta import VerifiedGarbage.Proof.Framework.X86_64.Words
meta import VerifiedGarbage.Proof.Modes.Addr
meta import VerifiedGarbage.Proof.Modes.X86_64.CbcEncLoop
meta import VerifiedGarbage.Proof.Modes.X86_64.CbcGroup
meta import VerifiedGarbage.Proof.Modes.X86_64.Copy
meta import VerifiedGarbage.Proof.Modes.X86_64.Counter
meta import VerifiedGarbage.Proof.Modes.X86_64.KeepIv
meta import VerifiedGarbage.Proof.Modes.X86_64.Steps
meta import VerifiedGarbage.Proof.Modes.X86_64.Unchain
meta import VerifiedGarbage.Proof.Modes.X86_64.Words
meta import VerifiedGarbage.Spec.Blowfish.Cfb
meta import VerifiedGarbage.Spec.Blowfish.Contract
meta import VerifiedGarbage.Spec.Ctr.Contract
meta import VerifiedGarbage.Spec.Rc2

/-!
# Blowfish-OFB and -CFB64 on x86-64 meet their contracts

`ofb_wp`, `cfbEncrypt_wp`, `cfbDecrypt_wp`: the modes' OFB and CFB
(`Proof.Modes.X86_64.fb_wp`) over Blowfish's core (`modeCoreSpec`), with the
specification's results (`Proof.Modes.ofb_of`, …). `ofb_verified`, …: each
is correct and constant time, by the taint analysis: the pointers, `n` and
the stack pointer are public, and so is everything the code computes from
them; the IV is secret. `ofb_framed`, … run them with their working space on
the stack, zeroed on return: 96 bytes, the 11 words of the scratch buffer
and 8 more.
-/

@[expose] public section

namespace VG.Proof.Blowfish.X86_64

open VG VG.X86_64 VG.Impl.Blowfish.X86_64

/-- The precondition of the feedback modes on x86-64, with the data `len`
bytes long and the working space at `r8`. -/
def fbPre (len : State → Nat) (s : State) : Prop :=
  let sched : Region := ⟨s.gpr .rdi, 4168⟩
  let iv : Region := ⟨s.gpr .rsi, 8⟩
  let data : Region := ⟨s.gpr .rdx, len s⟩
  let scratch : Region := ⟨s.gpr .r8, 8 * 11⟩
  let ret : Region := ⟨s.gpr .rsp, 8⟩
  s.rd = [sched] ∧ s.wr = [iv, data, scratch] ∧ sched.Disjoint iv ∧ sched.Disjoint data ∧
    sched.Disjoint scratch ∧ iv.Disjoint data ∧ iv.Disjoint scratch ∧ data.Disjoint scratch ∧
    ret.Disjoint iv ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
    (s.gpr .rdi).toNat + 4168 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 8 ≤ 2 ^ 64 ∧
    (s.gpr .rdx).toNat + len s ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + 8 * 11 ≤ 2 ^ 64

/-- The public arguments. -/
def fbPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `n` blocks. -/
abbrev blkLen (s : State) : Nat := 8 * (s.gpr .rcx).toNat

/-- The schedule, IV and data of `s`'s arguments. -/
abbrev ciphOf (s : State) : Spec.Cbc.Cipher := Spec.Blowfish.cipher (Spec.Blowfish.scheduleAt s.mem (s.gpr .rdi))
abbrev ivOf (s : State) : List Byte := Spec.Aes.bytesAt s.mem (s.gpr .rsi) 8
abbrev blocksOf (s : State) (m : Mem) : List (List Byte) := Spec.Blowfish.cbcBlocksAt m (s.gpr .rdx) (s.gpr .rcx).toNat

def ofbX86_64 : Contract isa where
  pre := fbPre blkLen
  post s s' := blocksOf s s'.mem = Spec.Ofb.crypt (ciphOf s) (ivOf s) (blocksOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .rsi) 8 = Spec.Ofb.next (ciphOf s) (ivOf s) (s.gpr .rcx).toNat
  pub := fbPub

def cfbEncX86_64 : Contract isa where
  pre := fbPre blkLen
  post s s' := blocksOf s s'.mem = Spec.Cfb.encrypt (ciphOf s) (ivOf s) (blocksOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .rsi) 8 =
      Spec.Cbc.next (ivOf s) (Spec.Cfb.encrypt (ciphOf s) (ivOf s) (blocksOf s s.mem))
  pub := fbPub

def cfbDecX86_64 : Contract isa where
  pre := fbPre blkLen
  post s s' := blocksOf s s'.mem = Spec.Cfb.decrypt (ciphOf s) (ivOf s) (blocksOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .rsi) 8 = Spec.Cbc.next (ivOf s) (blocksOf s s.mem)
  pub := fbPub

/-- What the modes' OFB and CFB give, for a mode `mo`: the data and the
IV as `fbOut` and `fbIn`, keeping the callee-saved registers. -/
theorem fb_wp' (mo : Impl.Modes.FbMode) {s₀ : State} (hp : fbPre blkLen s₀) :
    WP isa ((dirCore true).fb mo modeRegs) s₀ fun s' => gprPreserved s₀ s' ∧
      Modes.blocksOf 8 s'.mem (s₀.gpr .rdx) (s₀.gpr .rcx).toNat =
        (List.range (s₀.gpr .rcx).toNat).map (Modes.fbOut mo 8 (ciphOf s₀) s₀.mem (s₀.gpr .rdx) (ivOf s₀)) ∧
      Spec.Aes.bytesAt s'.mem (s₀.gpr .rsi) 8 = Modes.fbIn mo 8 (ciphOf s₀) s₀.mem (s₀.gpr .rdx) (ivOf s₀) (s₀.gpr .rcx).toNat := by
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, dRV, dRD, dRS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .r8, 8 * 11⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.X86_64.fb_wp (dirCoreSpec true) mo (r := modeRegs)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .r8) (P := s₀.gpr .rsi) (D := s₀.gpr .rdx) (n := (s₀.gpr .rcx).toNat)
    (k := Spec.Blowfish.scheduleAt s₀.mem (s₀.gpr .rdi)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp [Nat.mul_comm]) dVS dDS dVD fitD
    ⟨s₀.gpr .rdi, rfl, rfl, ⟨by rw [hrd]; simp, fitK, fun w hw => by
      rw [hwr] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact dKV
      · exact dKD
      · exact dKS⟩, fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dKS⟩ ⟨Modes.X86_64.keepsIv_of_scal (by lit_decide), crypt_keepsIv true⟩)
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
    WP isa ofb s₀ fun s' => gprPreserved s₀ s' ∧ ofbX86_64.post s₀ s' :=
  WP.mono (fb_wp' .ofb hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.ofb_of 8 (ciphOf s₀) s₀.mem (s₀.gpr .rdx) (ivOf s₀) (s₀.gpr .rcx).toNat
    refine ⟨hg, ?_, by rw [hv, h2]⟩
    change Spec.Blowfish.cbcBlocksAt _ _ _ = Spec.Ofb.crypt _ _ (Spec.Blowfish.cbcBlocksAt _ _ _)
    rw [cbcBlocksAt_eq, cbcBlocksAt_eq, hd, h1]

theorem cfbEncrypt_wp {s₀ : State} (hp : cfbEncX86_64.pre s₀) :
    WP isa cfbEncrypt s₀ fun s' => gprPreserved s₀ s' ∧ cfbEncX86_64.post s₀ s' :=
  WP.mono (fb_wp' .cfbEnc hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfbEnc_of 8 (ciphOf s₀) s₀.mem (s₀.gpr .rdx) (ivOf s₀) (s₀.gpr .rcx).toNat
    refine ⟨hg, ?_, ?_⟩
    · change Spec.Blowfish.cbcBlocksAt _ _ _ = Spec.Cfb.encrypt _ _ (Spec.Blowfish.cbcBlocksAt _ _ _)
      rw [cbcBlocksAt_eq, cbcBlocksAt_eq, hd, h1]
    · change _ = Spec.Cbc.next _ (Spec.Cfb.encrypt _ _ (Spec.Blowfish.cbcBlocksAt _ _ _))
      rw [hv, h2, cbcBlocksAt_eq]

theorem cfbDecrypt_wp {s₀ : State} (hp : cfbDecX86_64.pre s₀) :
    WP isa cfbDecrypt s₀ fun s' => gprPreserved s₀ s' ∧ cfbDecX86_64.post s₀ s' :=
  WP.mono (fb_wp' .cfbDec hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfbDec_of 8 (ciphOf s₀) s₀.mem (s₀.gpr .rdx) (ivOf s₀) (s₀.gpr .rcx).toNat
    refine ⟨hg, ?_, ?_⟩
    · change Spec.Blowfish.cbcBlocksAt _ _ _ = Spec.Cfb.decrypt _ _ (Spec.Blowfish.cbcBlocksAt _ _ _)
      rw [cbcBlocksAt_eq, cbcBlocksAt_eq, hd, h1]
    · change _ = Spec.Cbc.next _ (Spec.Blowfish.cbcBlocksAt _ _ _)
      rw [hv, h2, cbcBlocksAt_eq]

/-! ## Constant time -/

def fbTaint : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .r8, .rsp], flags := false,
    lens := [8, 0, 8 * 11], bases := [(.r8, 2, 0)] }

theorem fbTaint_wf {len : State → Nat} (s : State) (hs : fbPre len s) : Taint.Wf fbTaint s := by
  obtain ⟨_, hwr, _, _, _, dVD, dVS, dDS, _, _, _, _, fitV, fitD, fitB⟩ := hs
  refine ⟨fun _ => ?_, ?_⟩
  · rw [hwr]
    refine ⟨?_, ?_, ?_⟩
    · exact List.Forall₂.cons (by change 8 ≤ 8; omega) (List.Forall₂.cons (by change 0 ≤ len s; omega)
        (List.Forall₂.cons (by change 8 * 11 ≤ 8 * 11; omega) List.Forall₂.nil))
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
      · change 8 * 11 ≤ 2 ^ 64; omega
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

/-- A state satisfying the precondition (one block, or one byte). -/
def fbSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x3000 | .rdx => 0x4000 | .rcx => 1 | .r8 => 0x5000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 4168⟩]
  wr := [⟨0x3000, 8⟩, ⟨0x4000, 8⟩, ⟨0x5000, 8 * 11⟩]

theorem ofb_verified :
    Verified X86_64.target ofb (Proof.Blowfish.fbScratchContract X86_64.abi 11 Proof.Blowfish.ofbPost) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, hg, hpost⟩ := ofb_wp hs
      exact ⟨t, s', he, abiPreserved_of_exec (c := ofb) (by lit_decide) he hg, hpost⟩)
    (VG.Taint.constantTime (A := taint) fbTaint (fbTaint_agree blkLen_congr) (by taint_decide)) (by
    sig_implies [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Spec.Blowfish.ofbSig,
      Proof.Blowfish.ofbPost, ofbX86_64, fbPre, fbPub, X86_64.abi, X86_64.argRegs] [fbSat] using fbSat)

theorem cfbEncrypt_verified :
    Verified X86_64.target cfbEncrypt (Proof.Blowfish.fbScratchContract X86_64.abi 11 Proof.Blowfish.cfbEncPost) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, hg, hpost⟩ := cfbEncrypt_wp hs
      exact ⟨t, s', he, abiPreserved_of_exec (c := cfbEncrypt) (by lit_decide) he hg, hpost⟩)
    (VG.Taint.constantTime (A := taint) fbTaint (fbTaint_agree blkLen_congr) (by taint_decide)) (by
    sig_implies [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Spec.Blowfish.ofbSig,
      Proof.Blowfish.cfbEncPost, cfbEncX86_64, fbPre, fbPub, X86_64.abi, X86_64.argRegs] [fbSat] using fbSat)

theorem cfbDecrypt_verified :
    Verified X86_64.target cfbDecrypt (Proof.Blowfish.fbScratchContract X86_64.abi 11 Proof.Blowfish.cfbDecPost) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, hg, hpost⟩ := cfbDecrypt_wp hs
      exact ⟨t, s', he, abiPreserved_of_exec (c := cfbDecrypt) (by lit_decide) he hg, hpost⟩)
    (VG.Taint.constantTime (A := taint) fbTaint (fbTaint_agree blkLen_congr) (by taint_decide)) (by
    sig_implies [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Spec.Blowfish.ofbSig,
      Proof.Blowfish.cfbDecPost, cfbDecX86_64, fbPre, fbPub, X86_64.abi, X86_64.argRegs] [fbSat] using fbSat)

/-- OFB with its working space on the stack. -/
theorem ofb_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 96 .r8 11 ofb)
      (Spec.Blowfish.ofbContract X86_64.abi 96) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Blowfish.ofbSig) (nm := "scratch") (e := .u64)
    (n := 11) (post := Proof.Blowfish.ofbPost X86_64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 96) ofb_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) (by decide)
    (Proof.Blowfish.ofbPostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

/-- CFB64 encryption with its working space on the stack. -/
theorem cfbEncrypt_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 96 .r8 11 cfbEncrypt)
      (Spec.Blowfish.cfbEncryptContract X86_64.abi 96) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Blowfish.cfbSig) (nm := "scratch") (e := .u64)
    (n := 11) (post := Proof.Blowfish.cfbEncPost X86_64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 96) cfbEncrypt_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) (by decide)
    (Proof.Blowfish.cfbEncPostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

/-- CFB64 decryption with its working space on the stack. -/
theorem cfbDecrypt_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 96 .r8 11 cfbDecrypt)
      (Spec.Blowfish.cfbDecryptContract X86_64.abi 96) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Blowfish.cfbSig) (nm := "scratch") (e := .u64)
    (n := 11) (post := Proof.Blowfish.cfbDecPost X86_64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 96) cfbDecrypt_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) (by decide)
    (Proof.Blowfish.cfbDecPostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Blowfish.X86_64
