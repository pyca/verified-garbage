module

public import VerifiedGarbage.Proof.Cast5.Arm.ModeCore
meta import VerifiedGarbage.Proof.Cast5.Arm.ModeCore
import VerifiedGarbage.Proof.Modes.Arm.CbcChained
meta import VerifiedGarbage.Proof.Modes.Arm.CbcChained
import VerifiedGarbage.Proof.Modes.Arm.OfbCfb
meta import VerifiedGarbage.Proof.Modes.Arm.OfbCfb
public import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
meta import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
public import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.Proof.Cast5.ModeScratch
public import VerifiedGarbage.Proof.Modes.Arm.SeqCT
meta import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Cast5.Arm.EcbVerified
meta import VerifiedGarbage.Proof.Cast5.Arm.EcbVerified
import VerifiedGarbage.Proof.Modes.Arm.Cbc
meta import VerifiedGarbage.Proof.Modes.Arm.Cbc
import VerifiedGarbage.Impl.Aes.Arm.Alloc
import VerifiedGarbage.Proof.Aes.Blocks
import VerifiedGarbage.Proof.Aes.SboxSpec
import VerifiedGarbage.Proof.AesCtr.Ctr32
import VerifiedGarbage.Proof.AesCtr.Spec
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.CmacAes.Arm.Words
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Linear
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Modes.Addr
import VerifiedGarbage.Proof.Modes.Arm.Counter
import VerifiedGarbage.Proof.Modes.Arm.SeqLoop
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Spec.Ctr.Contract
meta import VerifiedGarbage.Impl.Aes.Arm.Alloc
meta import VerifiedGarbage.Proof.Aes.Blocks
meta import VerifiedGarbage.Proof.Aes.SboxSpec
meta import VerifiedGarbage.Proof.AesCtr.Ctr32
meta import VerifiedGarbage.Proof.AesCtr.Spec
meta import VerifiedGarbage.Proof.Cast5.ModeScratch
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Mem
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.CmacAes.Arm.Words
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Linear
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Modes.Addr
meta import VerifiedGarbage.Proof.Modes.Arm.Counter
meta import VerifiedGarbage.Proof.Modes.Arm.SeqLoop
meta import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Spec.Ctr.Contract

/-!
# CAST5-CBC, CAST5-OFB and CAST5-CFB64 on ARMv7 meet their contracts

The generic modes one block at a time over CAST5's ECB functions
(`Proof.Modes.Arm.seq_verified` with `ecbSpec`, a core taking the number of
rounds and its working space as a stack argument) meet the contracts with a
scratch buffer of 39 words (`Proof.Cast5.modeScratchContract`): the modes'
72 bytes, then the 256 bytes the ECB function works in. The ECB functions use
no stack of their own, so the modes need only the 8 bytes their push of that
working space takes. The `_framed` theorems keep the buffer on the stack,
zeroed on return: 328 bytes more. The contracts are under
`Arm.abi.withConsts ecbConsts`: the ECB functions read the table
`VG_CAST5_S1234`, which the modes hold apart from what they write
(`tabsOk_of`).
-/

@[expose] public section

namespace VG.Proof.Cast5.Arm

open VG VG.Arm VG.Impl.Cast5.Arm VG.Impl.Modes.Arm VG.Proof.Modes.Arm
open VG.Impl.Cast5 (s1234Sym s1234 ecbConsts)

theorem blocksOf_eq' (m : Mem) (p : Addr) (n : Nat) :
    VG.Proof.Modes.blocksOf 8 m p n = Spec.Cast5.cbcBlocksAt m p n :=
  (Proof.Cast5.cbcBlocksAt_eq m p n).symm

/-- A state satisfying the precondition with the scratch buffer (no
blocks): the subkeys at `0x1000`, 12 rounds, the IV at `0x2000`, the data at
`0x3000`, and `n` and the scratch buffer's address `0` (the stack
arguments, in memory that is zero); the IV read (`ivW = false`) or read and
written. -/
def modeSat (ivW : Bool) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 12 | .r2 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := if ivW then [⟨0x1000, 128⟩, ⟨0x8000, 8⟩] else [⟨0x1000, 128⟩, ⟨0x2000, 8⟩, ⟨0x8000, 8⟩]
  wr := if ivW then [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0, 312⟩] else [⟨0x3000, 0⟩, ⟨0, 312⟩]

/-- A state satisfying the functions' precondition (no blocks). -/
def frameSat (ivW : Bool) : State :=
  { modeSat ivW with
    rd := if ivW then [⟨0x1000, 128⟩, ⟨0x8000, 4⟩] else [⟨0x1000, 128⟩, ⟨0x2000, 8⟩, ⟨0x8000, 4⟩]
    wr := if ivW then [⟨0x2000, 8⟩, ⟨0x3000, 0⟩] else [⟨0x3000, 0⟩] }

/-- What the contract says of the table, as the modes need it. -/
theorem tabsOk_of {s : State} {st : Nat} (h : ConstsOk ecbConsts st s) (hst : 0 < st) :
    TabsOk ecbConsts st s := by
  refine ⟨h.2.1, fun t ht => ⟨?_, (h.2.2 t ht).1, (h.2.2 t ht).2.1, (h.2.2 t ht).2.2 _ ?_⟩⟩
  · have hm : t ∈ s.rd.drop (s.rd.length - ecbConsts.length) := by rw [h.1]; exact ht
    exact List.mem_of_mem_drop hm
  · obtain ⟨k, rfl⟩ : ∃ k, st = k + 1 := ⟨st - 1, by omega⟩
    exact List.mem_singleton_self _

theorem s1234_length : s1234.length = 512 := by rw [Impl.Cast5.s1234, table_length]

/-- The memory of the witnesses: the table at `0x100000`, zero elsewhere
(irreducible: unfolding it in a definitional check would evaluate the
table). -/
@[irreducible] def modeSatMem : Mem := constMem 0x100000 s1234

theorem modeSatMem_held : ∀ i < s1234.length,
    modeSatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = s1234.getD i 0 := by
  unfold modeSatMem
  exact constMem_held _ _ (by rw [s1234_length]; decide)

/-- The witnesses' memory below the table. -/
theorem modeSatMem_readW (a : Addr) (ha : ∀ i < 4, ¬ (a + BitVec.ofNat 64 i - 0x100000).toNat < 4096) :
    modeSatMem.readW a 32 = 0 := by
  have e : modeSatMem.readW a 32 = Mem.readW (fun _ => (0 : Byte)) a 32 := by
    apply Mem.readW_congr
    intro i hi
    unfold modeSatMem constMem
    rw [s1234_length, ite_eq_right (ha i hi)]
  rw [e, Mem.readW, Mem.read_eq_of_bytes (n := 32 / 8) (v := 0) (fun i _ => by simp)]
  decide

/-- `modeSat` with the table. -/
def modeSatC (ivW : Bool) : State :=
  { modeSat ivW with mem := modeSatMem, rd := (modeSat ivW).rd ++ [⟨0x100000, 4096⟩], syms := fun _ => 0x100000 }

/-- `frameSat` with the table. -/
def frameSatC (ivW : Bool) : State :=
  { frameSat ivW with mem := modeSatMem, rd := (frameSat ivW).rd ++ [⟨0x100000, 4096⟩], syms := fun _ => 0x100000 }

theorem modeSatC_arg (ivW : Bool) {i : Nat} (hi : i < 2) : stackArg (modeSatC ivW) i = 0 :=
  modeSatMem_readW _ (by rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> cases ivW <;> decide)

theorem frameSatC_arg (ivW : Bool) {i : Nat} (hi : i < 2) : stackArg (frameSatC ivW) i = 0 :=
  modeSatMem_readW _ (by rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> cases ivW <;> decide)

theorem cbc_sat (post : Spec.Cast5.cbcChainedSig.Post Arm.abi.ptrBits) :
    ∃ s, (Proof.Cast5.modeScratchContract (Arm.abi.withConsts ecbConsts) Spec.Cast5.cbcChainedSig 39
      (Proof.Cast5.cbcChainedPre Arm.abi.ptrBits) post 8).pre s := by
  refine ⟨modeSatC true, ?_⟩
  have a0 := modeSatC_arg true (i := 0) (by decide)
  have a1 := modeSatC_arg true (i := 1) (by decide)
  have held := modeSatMem_held
  generalize e : modeSatC true = s at a0 a1
  sig_pre [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
    Spec.Cast5.cbcChainedSig, Proof.Cast5.cbcChainedPre, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, ecbConsts_eq,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow, s1234_length]
  subst e
  rw [a0, a1]
  refine ⟨by decide, by decide, by decide, fun i hi => held i (by rw [s1234_length]; exact hi), by decide, ?_, ?_⟩
  · intro r hr
    change r ∈ ([⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0, 312⟩] : List Region) at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide | rfl | exact Or.inl rfl

theorem cbcFrame_sat (post : Spec.Cast5.cbcChainedSig.Post Arm.abi.ptrBits) :
    ∃ s, (Spec.Cast5.cbcChainedSig.contract (Arm.abi.withConsts ecbConsts) (Proof.Cast5.cbcChainedPre Arm.abi.ptrBits) post true
      (8 + 328)).pre s := by
  refine ⟨frameSatC true, ?_⟩
  have a0 := frameSatC_arg true (i := 0) (by decide)
  have held := modeSatMem_held
  generalize e : frameSatC true = s at a0
  sig_pre [Spec.Cast5.cbcChainedSig, Proof.Cast5.cbcChainedPre, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, ecbConsts_eq,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow, s1234_length]
  subst e
  rw [a0]
  refine ⟨by decide, by decide, by decide, fun i hi => held i (by rw [s1234_length]; exact hi), by decide, ?_, ?_⟩
  · intro r hr
    change r ∈ ([⟨0x2000, 8⟩, ⟨0x3000, 0⟩] : List Region) at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide | rfl | exact Or.inl rfl

theorem ofb_sat (post : Spec.Cast5.ofbSig.Post Arm.abi.ptrBits) :
    ∃ s, (Proof.Cast5.modeScratchContract (Arm.abi.withConsts ecbConsts) Spec.Cast5.ofbSig 39
      (Spec.Cast5.ofbPre Arm.abi.ptrBits) post 8).pre s := by
  refine ⟨modeSatC true, ?_⟩
  have a0 := modeSatC_arg true (i := 0) (by decide)
  have a1 := modeSatC_arg true (i := 1) (by decide)
  have held := modeSatMem_held
  generalize e : modeSatC true = s at a0 a1
  sig_pre [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
    Spec.Cast5.ofbSig, Spec.Cast5.ofbPre, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, ecbConsts_eq,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow, s1234_length]
  subst e
  rw [a0, a1]
  refine ⟨by decide, by decide, by decide, fun i hi => held i (by rw [s1234_length]; exact hi), by decide, ?_, ?_⟩
  · intro r hr
    change r ∈ ([⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0, 312⟩] : List Region) at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide | rfl | exact Or.inl rfl

theorem ofbFrame_sat (post : Spec.Cast5.ofbSig.Post Arm.abi.ptrBits) :
    ∃ s, (Spec.Cast5.ofbSig.contract (Arm.abi.withConsts ecbConsts) (Spec.Cast5.ofbPre Arm.abi.ptrBits) post true
      (8 + 328)).pre s := by
  refine ⟨frameSatC true, ?_⟩
  have a0 := frameSatC_arg true (i := 0) (by decide)
  have held := modeSatMem_held
  generalize e : frameSatC true = s at a0
  sig_pre [Spec.Cast5.ofbSig, Spec.Cast5.ofbPre, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, ecbConsts_eq,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow, s1234_length]
  subst e
  rw [a0]
  refine ⟨by decide, by decide, by decide, fun i hi => held i (by rw [s1234_length]; exact hi), by decide, ?_, ?_⟩
  · intro r hr
    change r ∈ ([⟨0x2000, 8⟩, ⟨0x3000, 0⟩] : List Region) at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide | rfl | exact Or.inl rfl

theorem cfb_sat (post : Spec.Cast5.cfbSig.Post Arm.abi.ptrBits) :
    ∃ s, (Proof.Cast5.modeScratchContract (Arm.abi.withConsts ecbConsts) Spec.Cast5.cfbSig 39
      (Spec.Cast5.cfbPre Arm.abi.ptrBits) post 8).pre s := by
  refine ⟨modeSatC true, ?_⟩
  have a0 := modeSatC_arg true (i := 0) (by decide)
  have a1 := modeSatC_arg true (i := 1) (by decide)
  have held := modeSatMem_held
  generalize e : modeSatC true = s at a0 a1
  sig_pre [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
    Spec.Cast5.cfbSig, Spec.Cast5.cfbPre, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, ecbConsts_eq,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow, s1234_length]
  subst e
  rw [a0, a1]
  refine ⟨by decide, by decide, by decide, fun i hi => held i (by rw [s1234_length]; exact hi), by decide, ?_, ?_⟩
  · intro r hr
    change r ∈ ([⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0, 312⟩] : List Region) at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide | rfl | exact Or.inl rfl

theorem cfbFrame_sat (post : Spec.Cast5.cfbSig.Post Arm.abi.ptrBits) :
    ∃ s, (Spec.Cast5.cfbSig.contract (Arm.abi.withConsts ecbConsts) (Spec.Cast5.cfbPre Arm.abi.ptrBits) post true
      (8 + 328)).pre s := by
  refine ⟨frameSatC true, ?_⟩
  have a0 := frameSatC_arg true (i := 0) (by decide)
  have held := modeSatMem_held
  generalize e : frameSatC true = s at a0
  sig_pre [Spec.Cast5.cfbSig, Spec.Cast5.cfbPre, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, ecbConsts_eq,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow, s1234_length]
  subst e
  rw [a0]
  refine ⟨by decide, by decide, by decide, fun i hi => held i (by rw [s1234_length]; exact hi), by decide, ?_, ?_⟩
  · intro r hr
    change r ∈ ([⟨0x2000, 8⟩, ⟨0x3000, 0⟩] : List Region) at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide | rfl | exact Or.inl rfl

theorem cbcEncryptChainedTaint : SeqTaint (ecbCore true) cbcEncChained :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem cbcEncryptChained_implies : (seqArm (ecbCore true) (ecbSpec true) cbcEncChained).Implies
    (Proof.Cast5.modeScratchContract (Arm.abi.withConsts ecbConsts) Spec.Cast5.cbcChainedSig 39
      (Proof.Cast5.cbcChainedPre Arm.abi.ptrBits) (Proof.Cast5.cbcEncChainedPost Arm.abi.ptrBits) 8) where
  pre s h := by
    unfold Proof.Cast5.modeScratchContract Sig.scratchContract at h
    obtain ⟨h1, hk⟩ := pre_consts.mp h
    refine seqArm_pre_rwR' rfl (len := (· * 8)) (fun n => rfl) (rd' := (stripConsts ecbConsts s).rd) ?_
      (fun r hr => stripConsts_rd_mem hr) (tabsOk_of hk (by decide))
    sig_pre [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Cast5.cbcChainedSig, Proof.Cast5.cbcChainedPre, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h1
    exact h1
  post s s' _ h := by
    unfold Proof.Cast5.modeScratchContract Sig.scratchContract
    refine post_consts.mpr ?_
    sig_post [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Cast5.cbcChainedSig, Proof.Cast5.cbcEncChainedPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := cbcEncChained_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_rounds (c := ecbCore true) rfl s
    simp only [show (ecbCore true).bs = 8 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, Proof.Cast5.dirCipher, ↓reduceIte, State.addr, blocksOf_eq'] at e
    exact e
  pub s₁ s₂ _ _ h := by
    unfold Proof.Cast5.modeScratchContract Sig.scratchContract at h
    obtain ⟨h, hsy⟩ := pub_consts.mp h
    sig_pub [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Cast5.cbcChainedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pubR h fun x hx => symAddr_eq_iff.mp (hsy x hx)
  sat := cbc_sat _

theorem cbcEncryptChained_verified : Verified Arm.target cbcEncryptChained
    (Proof.Cast5.modeScratchContract (Arm.abi.withConsts ecbConsts) Spec.Cast5.cbcChainedSig 39
      (Proof.Cast5.cbcChainedPre Arm.abi.ptrBits) (Proof.Cast5.cbcEncChainedPost Arm.abi.ptrBits) 8) :=
  seq_verified (ecbSpec true) (cbcEncChained_ok _) cbcEncryptChainedTaint cbcEncryptChained_implies

/-- `cbcEncryptChained`, with its scratch buffer on the stack (zeroed on return). -/
theorem cbcEncryptChained_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 328 1 78 cbcEncryptChained)
      (Spec.Cast5.cbcEncryptChainedContract (Arm.abi.withConsts ecbConsts) 336) :=
  Arm.Verified.stackScratchWipedC (c₀ := (s1234Sym, s1234)) (cs := []) (sig := Spec.Cast5.cbcChainedSig) (nm := "scratch")
    (e := .u64) (n := 39) (pre := Proof.Cast5.cbcChainedPre Arm.abi.ptrBits) (post := Proof.Cast5.cbcEncChainedPost Arm.abi.ptrBits)
    (wa := true) (stack := 8) (m := 1) (bytes := 328)
    cbcEncryptChained_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun vs m₁ m₂ hl _ h => Proof.Cast5.modePre_local _ vs m₁ m₂ hl h) (Proof.Cast5.cbcEncChainedPost_local _)
    (Proof.Cast5.cbcEncChainedPostOut_local _) (cbcFrame_sat _)

theorem cbcDecryptChainedTaint : SeqTaint (ecbCore false) cbcDecChained :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem cbcDecryptChained_implies : (seqArm (ecbCore false) (ecbSpec false) cbcDecChained).Implies
    (Proof.Cast5.modeScratchContract (Arm.abi.withConsts ecbConsts) Spec.Cast5.cbcChainedSig 39
      (Proof.Cast5.cbcChainedPre Arm.abi.ptrBits) (Proof.Cast5.cbcDecChainedPost Arm.abi.ptrBits) 8) where
  pre s h := by
    unfold Proof.Cast5.modeScratchContract Sig.scratchContract at h
    obtain ⟨h1, hk⟩ := pre_consts.mp h
    refine seqArm_pre_rwR' rfl (len := (· * 8)) (fun n => rfl) (rd' := (stripConsts ecbConsts s).rd) ?_
      (fun r hr => stripConsts_rd_mem hr) (tabsOk_of hk (by decide))
    sig_pre [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Cast5.cbcChainedSig, Proof.Cast5.cbcChainedPre, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h1
    exact h1
  post s s' _ h := by
    unfold Proof.Cast5.modeScratchContract Sig.scratchContract
    refine post_consts.mpr ?_
    sig_post [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Cast5.cbcChainedSig, Proof.Cast5.cbcDecChainedPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := cbcDecChained_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_rounds (c := ecbCore false) rfl s
    simp only [show (ecbCore false).bs = 8 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, Proof.Cast5.dirCipher, Bool.false_eq_true, ↓reduceIte, State.addr, blocksOf_eq'] at e
    exact e
  pub s₁ s₂ _ _ h := by
    unfold Proof.Cast5.modeScratchContract Sig.scratchContract at h
    obtain ⟨h, hsy⟩ := pub_consts.mp h
    sig_pub [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Cast5.cbcChainedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pubR h fun x hx => symAddr_eq_iff.mp (hsy x hx)
  sat := cbc_sat _

theorem cbcDecryptChained_verified : Verified Arm.target cbcDecryptChained
    (Proof.Cast5.modeScratchContract (Arm.abi.withConsts ecbConsts) Spec.Cast5.cbcChainedSig 39
      (Proof.Cast5.cbcChainedPre Arm.abi.ptrBits) (Proof.Cast5.cbcDecChainedPost Arm.abi.ptrBits) 8) :=
  seq_verified (ecbSpec false) (cbcDecChained_ok _) cbcDecryptChainedTaint cbcDecryptChained_implies

/-- `cbcDecryptChained`, with its scratch buffer on the stack (zeroed on return). -/
theorem cbcDecryptChained_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 328 1 78 cbcDecryptChained)
      (Spec.Cast5.cbcDecryptChainedContract (Arm.abi.withConsts ecbConsts) 336) :=
  Arm.Verified.stackScratchWipedC (c₀ := (s1234Sym, s1234)) (cs := []) (sig := Spec.Cast5.cbcChainedSig) (nm := "scratch")
    (e := .u64) (n := 39) (pre := Proof.Cast5.cbcChainedPre Arm.abi.ptrBits) (post := Proof.Cast5.cbcDecChainedPost Arm.abi.ptrBits)
    (wa := true) (stack := 8) (m := 1) (bytes := 328)
    cbcDecryptChained_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun vs m₁ m₂ hl _ h => Proof.Cast5.modePre_local _ vs m₁ m₂ hl h) (Proof.Cast5.cbcDecChainedPost_local _)
    (Proof.Cast5.cbcDecChainedPostOut_local _) (cbcFrame_sat _)

theorem ofbTaint : SeqTaint (ecbCore true) VG.Impl.Modes.Arm.ofb :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem ofb_implies : (seqArm (ecbCore true) (ecbSpec true) VG.Impl.Modes.Arm.ofb).Implies
    (Proof.Cast5.modeScratchContract (Arm.abi.withConsts ecbConsts) Spec.Cast5.ofbSig 39
      (Spec.Cast5.ofbPre Arm.abi.ptrBits) (Proof.Cast5.ofbPost Arm.abi.ptrBits) 8) where
  pre s h := by
    unfold Proof.Cast5.modeScratchContract Sig.scratchContract at h
    obtain ⟨h1, hk⟩ := pre_consts.mp h
    refine seqArm_pre_rwR' rfl (len := (· * 8)) (fun n => rfl) (rd' := (stripConsts ecbConsts s).rd) ?_
      (fun r hr => stripConsts_rd_mem hr) (tabsOk_of hk (by decide))
    sig_pre [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Cast5.ofbSig, Spec.Cast5.ofbPre, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h1
    exact h1
  post s s' _ h := by
    unfold Proof.Cast5.modeScratchContract Sig.scratchContract
    refine post_consts.mpr ?_
    sig_post [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Cast5.ofbSig, Proof.Cast5.ofbPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := ofb_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_rounds (c := ecbCore true) rfl s
    simp only [show (ecbCore true).bs = 8 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, Proof.Cast5.dirCipher, ↓reduceIte, State.addr, blocksOf_eq'] at e
    exact e
  pub s₁ s₂ _ _ h := by
    unfold Proof.Cast5.modeScratchContract Sig.scratchContract at h
    obtain ⟨h, hsy⟩ := pub_consts.mp h
    sig_pub [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Cast5.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pubR h fun x hx => symAddr_eq_iff.mp (hsy x hx)
  sat := ofb_sat _

theorem ofb_verified : Verified Arm.target ofb
    (Proof.Cast5.modeScratchContract (Arm.abi.withConsts ecbConsts) Spec.Cast5.ofbSig 39
      (Spec.Cast5.ofbPre Arm.abi.ptrBits) (Proof.Cast5.ofbPost Arm.abi.ptrBits) 8) :=
  seq_verified (ecbSpec true) (ofb_ok _) ofbTaint ofb_implies

/-- `ofb`, with its scratch buffer on the stack (zeroed on return). -/
theorem ofb_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 328 1 78 ofb)
      (Spec.Cast5.ofbContract (Arm.abi.withConsts ecbConsts) 336) :=
  Arm.Verified.stackScratchWipedC (c₀ := (s1234Sym, s1234)) (cs := []) (sig := Spec.Cast5.ofbSig) (nm := "scratch")
    (e := .u64) (n := 39) (pre := Spec.Cast5.ofbPre Arm.abi.ptrBits) (post := Proof.Cast5.ofbPost Arm.abi.ptrBits)
    (wa := true) (stack := 8) (m := 1) (bytes := 328)
    ofb_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun vs m₁ m₂ hl _ h => Proof.Cast5.modePre_local _ vs m₁ m₂ hl h) (Proof.Cast5.ofbPost_local _)
    (Proof.Cast5.ofbPostOut_local _) (ofbFrame_sat _)

theorem cfbEncryptTaint : SeqTaint (ecbCore true) cfbEnc :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem cfbEncrypt_implies : (seqArm (ecbCore true) (ecbSpec true) cfbEnc).Implies
    (Proof.Cast5.modeScratchContract (Arm.abi.withConsts ecbConsts) Spec.Cast5.cfbSig 39
      (Spec.Cast5.cfbPre Arm.abi.ptrBits) (Proof.Cast5.cfbEncPost Arm.abi.ptrBits) 8) where
  pre s h := by
    unfold Proof.Cast5.modeScratchContract Sig.scratchContract at h
    obtain ⟨h1, hk⟩ := pre_consts.mp h
    refine seqArm_pre_rwR' rfl (len := (· * 8)) (fun n => rfl) (rd' := (stripConsts ecbConsts s).rd) ?_
      (fun r hr => stripConsts_rd_mem hr) (tabsOk_of hk (by decide))
    sig_pre [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Cast5.cfbSig, Spec.Cast5.cfbPre, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h1
    exact h1
  post s s' _ h := by
    unfold Proof.Cast5.modeScratchContract Sig.scratchContract
    refine post_consts.mpr ?_
    sig_post [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Cast5.cfbSig, Proof.Cast5.cfbEncPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := cfbEnc_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_rounds (c := ecbCore true) rfl s
    simp only [show (ecbCore true).bs = 8 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, Proof.Cast5.dirCipher, ↓reduceIte, State.addr, blocksOf_eq'] at e
    exact e
  pub s₁ s₂ _ _ h := by
    unfold Proof.Cast5.modeScratchContract Sig.scratchContract at h
    obtain ⟨h, hsy⟩ := pub_consts.mp h
    sig_pub [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Cast5.cfbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pubR h fun x hx => symAddr_eq_iff.mp (hsy x hx)
  sat := cfb_sat _

theorem cfbEncrypt_verified : Verified Arm.target cfbEncrypt
    (Proof.Cast5.modeScratchContract (Arm.abi.withConsts ecbConsts) Spec.Cast5.cfbSig 39
      (Spec.Cast5.cfbPre Arm.abi.ptrBits) (Proof.Cast5.cfbEncPost Arm.abi.ptrBits) 8) :=
  seq_verified (ecbSpec true) (cfbEnc_ok _) cfbEncryptTaint cfbEncrypt_implies

/-- `cfbEncrypt`, with its scratch buffer on the stack (zeroed on return). -/
theorem cfbEncrypt_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 328 1 78 cfbEncrypt)
      (Spec.Cast5.cfbEncryptContract (Arm.abi.withConsts ecbConsts) 336) :=
  Arm.Verified.stackScratchWipedC (c₀ := (s1234Sym, s1234)) (cs := []) (sig := Spec.Cast5.cfbSig) (nm := "scratch")
    (e := .u64) (n := 39) (pre := Spec.Cast5.cfbPre Arm.abi.ptrBits) (post := Proof.Cast5.cfbEncPost Arm.abi.ptrBits)
    (wa := true) (stack := 8) (m := 1) (bytes := 328)
    cfbEncrypt_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun vs m₁ m₂ hl _ h => Proof.Cast5.modePre_local _ vs m₁ m₂ hl h) (Proof.Cast5.cfbEncPost_local _)
    (Proof.Cast5.cfbEncPostOut_local _) (cfbFrame_sat _)

theorem cfbDecryptTaint : SeqTaint (ecbCore true) cfbDec :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem cfbDecrypt_implies : (seqArm (ecbCore true) (ecbSpec true) cfbDec).Implies
    (Proof.Cast5.modeScratchContract (Arm.abi.withConsts ecbConsts) Spec.Cast5.cfbSig 39
      (Spec.Cast5.cfbPre Arm.abi.ptrBits) (Proof.Cast5.cfbDecPost Arm.abi.ptrBits) 8) where
  pre s h := by
    unfold Proof.Cast5.modeScratchContract Sig.scratchContract at h
    obtain ⟨h1, hk⟩ := pre_consts.mp h
    refine seqArm_pre_rwR' rfl (len := (· * 8)) (fun n => rfl) (rd' := (stripConsts ecbConsts s).rd) ?_
      (fun r hr => stripConsts_rd_mem hr) (tabsOk_of hk (by decide))
    sig_pre [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Cast5.cfbSig, Spec.Cast5.cfbPre, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h1
    exact h1
  post s s' _ h := by
    unfold Proof.Cast5.modeScratchContract Sig.scratchContract
    refine post_consts.mpr ?_
    sig_post [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Cast5.cfbSig, Proof.Cast5.cfbDecPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := cfbDec_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_rounds (c := ecbCore true) rfl s
    simp only [show (ecbCore true).bs = 8 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, Proof.Cast5.dirCipher, ↓reduceIte, State.addr, blocksOf_eq'] at e
    exact e
  pub s₁ s₂ _ _ h := by
    unfold Proof.Cast5.modeScratchContract Sig.scratchContract at h
    obtain ⟨h, hsy⟩ := pub_consts.mp h
    sig_pub [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Cast5.cfbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pubR h fun x hx => symAddr_eq_iff.mp (hsy x hx)
  sat := cfb_sat _

theorem cfbDecrypt_verified : Verified Arm.target cfbDecrypt
    (Proof.Cast5.modeScratchContract (Arm.abi.withConsts ecbConsts) Spec.Cast5.cfbSig 39
      (Spec.Cast5.cfbPre Arm.abi.ptrBits) (Proof.Cast5.cfbDecPost Arm.abi.ptrBits) 8) :=
  seq_verified (ecbSpec true) (cfbDec_ok _) cfbDecryptTaint cfbDecrypt_implies

/-- `cfbDecrypt`, with its scratch buffer on the stack (zeroed on return). -/
theorem cfbDecrypt_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 328 1 78 cfbDecrypt)
      (Spec.Cast5.cfbDecryptContract (Arm.abi.withConsts ecbConsts) 336) :=
  Arm.Verified.stackScratchWipedC (c₀ := (s1234Sym, s1234)) (cs := []) (sig := Spec.Cast5.cfbSig) (nm := "scratch")
    (e := .u64) (n := 39) (pre := Spec.Cast5.cfbPre Arm.abi.ptrBits) (post := Proof.Cast5.cfbDecPost Arm.abi.ptrBits)
    (wa := true) (stack := 8) (m := 1) (bytes := 328)
    cfbDecrypt_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun vs m₁ m₂ hl _ h => Proof.Cast5.modePre_local _ vs m₁ m₂ hl h) (Proof.Cast5.cfbDecPost_local _)
    (Proof.Cast5.cfbDecPostOut_local _) (cfbFrame_sat _)

end VG.Proof.Cast5.Arm
