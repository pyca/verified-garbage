module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.BlocksVerified
public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.BlocksTo
public import VerifiedGarbage.Proof.AesGcm.X86_64.Iv96Contract
public import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Iv96CT
public import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Iv96CT
public import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.CallI
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# Whole-block functions given the block index, with prepared contexts

Untrusted: everything here is checked by Lean. `vg_aes_gcm_decrypt_blocks_prepared_iv96`
and `vg_aes_gcm_encrypt_blocks_to_prepared_iv96` meet the contracts of
`Spec/Gcm/PreparedIv96.lean` (through `decryptBlocksIv96X86_64M` and
`encryptBlocksToIv96X86_64M`): with loops given the index (`DecCodeI`,
`EncCodeI`), or with those of the functions without it, which ignore it.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64
open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open Gcm.X86_64.Stitch (CtxMode)

/-- A state satisfying the precondition of `vg_aes_gcm_decrypt_blocks_prepared_iv96`. -/
def blocksSatPI : State := { blocksSat with rd := [⟨0x1000, 1024⟩, ⟨0x8008, 16⟩] }

theorem decryptBlocksIv96_implies : (Proof.AesGcm.decryptBlocksIv96X86_64M CtxMode.prepared).Implies
    (Spec.Gcm.decryptBlocksPreparedIv96Contract X86_64.abi 8) :=
  { pre := by
      intro s h
      sig_pre [Spec.Gcm.decryptBlocksPreparedIv96Contract, Spec.Gcm.decryptBlocksPreparedIv96Sig,
        Spec.Gcm.decryptBlocksPreparedIv96Pre, Spec.Gcm.cryptBlocksPreparedSig, Spec.Gcm.cryptBlocksPrecomputedSig,
        Spec.Gcm.cryptBlocksPreparedPre, Proof.AesGcm.decryptBlocksIv96X86_64M, Proof.AesGcm.blocksPreMI,
        CtxMode.prepared, Proof.AesGcm.blocksPubI, Proof.AesGcm.blocksPub, X86_64.abi, Proof.AesGcm.arg,
        Proof.AesGcm.args, Proof.AesGcm.stk, Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg,
        X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs] at h
      sig_split h
      sig_reduce [Spec.Gcm.decryptBlocksPreparedIv96Contract, Spec.Gcm.decryptBlocksPreparedIv96Sig,
        Spec.Gcm.decryptBlocksPreparedIv96Pre, Spec.Gcm.cryptBlocksPreparedSig, Spec.Gcm.cryptBlocksPrecomputedSig,
        Spec.Gcm.cryptBlocksPreparedPre, Proof.AesGcm.decryptBlocksIv96X86_64M, Proof.AesGcm.blocksPreMI,
        CtxMode.prepared, Proof.AesGcm.blocksPubI, Proof.AesGcm.blocksPub, X86_64.abi, Proof.AesGcm.arg,
        Proof.AesGcm.args, Proof.AesGcm.stk, Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg,
        X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs]
      sig_simp [Spec.Gcm.decryptBlocksPreparedIv96Contract, Spec.Gcm.decryptBlocksPreparedIv96Sig,
        Spec.Gcm.decryptBlocksPreparedIv96Pre, Spec.Gcm.cryptBlocksPreparedSig, Spec.Gcm.cryptBlocksPrecomputedSig,
        Spec.Gcm.cryptBlocksPreparedPre, Proof.AesGcm.decryptBlocksIv96X86_64M, Proof.AesGcm.blocksPreMI,
        CtxMode.prepared, Proof.AesGcm.blocksPubI, Proof.AesGcm.blocksPub, X86_64.abi, Proof.AesGcm.arg,
        Proof.AesGcm.args, Proof.AesGcm.stk, Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg,
        X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs] []
      sig_and_intros
      sig_close
      all_goals try (rw [‹s.rd = _›]; exact Proof.AesGcm.inRegions_args2 _ _ (by decide))
      all_goals first
        | with_reducible assumption
        | with_reducible exact Region.Disjoint.symm ‹_›
        | omega
        | simp only [*, List.mem_cons, List.mem_singleton, true_or, or_true]
    post := by
      sig_implies_post [Spec.Gcm.decryptBlocksPreparedIv96Contract, Spec.Gcm.decryptBlocksPreparedIv96Sig,
        Spec.Gcm.decryptBlocksPreparedIv96Pre, Spec.Gcm.cryptBlocksPreparedSig, Spec.Gcm.cryptBlocksPrecomputedSig,
        Spec.Gcm.cryptBlocksPreparedPre, Proof.AesGcm.decryptBlocksIv96X86_64M,
        Proof.AesGcm.decryptBlocksX86_64, X86_64.abi, Proof.AesGcm.arg, X86_64.stackArg,
        X86_64.stackArgAddr, X86_64.argRegs]
    pub := by
      sig_implies_pub [Spec.Gcm.decryptBlocksPreparedIv96Contract, Spec.Gcm.decryptBlocksPreparedIv96Sig,
        Spec.Gcm.cryptBlocksPreparedSig, Spec.Gcm.cryptBlocksPrecomputedSig,
        Proof.AesGcm.decryptBlocksIv96X86_64M, Proof.AesGcm.blocksPubI, Proof.AesGcm.blocksPub, X86_64.abi,
        Proof.AesGcm.arg, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop,
        X86_64.argRegs]
    sat := ⟨blocksSatPI, by
      sig_pre [Spec.Gcm.decryptBlocksPreparedIv96Contract, Spec.Gcm.decryptBlocksPreparedIv96Sig,
        Spec.Gcm.decryptBlocksPreparedIv96Pre, Spec.Gcm.cryptBlocksPreparedSig, Spec.Gcm.cryptBlocksPrecomputedSig,
        Spec.Gcm.cryptBlocksPreparedPre, X86_64.abi, X86_64.argRegs, blocksSatPI, blocksSat]
      sig_and_intros
      all_goals first
        | rfl
        | decide
        | exact preparedPowersRepr_zero _
        | exact Region.disjoint_of_sep (by decide)⟩ }

/-! ## Whole-block decryption -/

section
variable (v : GcmImpl) {aligned : Bool} {p : Prog isa} (S : PieceS p)
include S

theorem decryptI_mx :
    (Blocks.decrypt v.callees.ctr v.callees.gh (some p) aligned true).allInstrs (fun i => !loadsMxcsr i) = true := by
  cases aligned <;>
    simp only [Blocks.decrypt, Blocks.blocks, Blocks.body, Blocks.head, Blocks.fullBody, Blocks.stitchPart,
      Blocks.scratchSetup, Blocks.tail, Blocks.ctrCall, Blocks.ghCall, Code.allInstrs, GcmImpl.callees, S.mxcsr,
      v.ctr.mxcsr, v.gh.mxcsr, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte] <;> decide +kernel

theorem decryptI_spSafe :
    (Blocks.decrypt v.callees.ctr v.callees.gh (some p) aligned true).all (fun i => !X86_64.isa.writesSp i) = true := by
  cases aligned <;>
    simp only [Blocks.decrypt, Blocks.blocks, Blocks.body, Blocks.head, Blocks.fullBody, Blocks.stitchPart,
      Blocks.scratchSetup, Blocks.tail, Blocks.ctrCall, Blocks.ghCall, Code.all, GcmImpl.callees, S.spSafe,
      v.ctr.spSafe, v.gh.spSafe, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte] <;> decide +kernel

theorem decryptI_xdepth : (Blocks.decrypt v.callees.ctr v.callees.gh (some p) aligned true).x86_64Depth ≤ 8 := by
  cases aligned <;>
    simp only [Blocks.decrypt, Blocks.blocks, Blocks.body, Blocks.head, Blocks.fullBody, Blocks.stitchPart,
      Blocks.scratchSetup, Blocks.tail, Blocks.ctrCall, Blocks.ghCall, Code.x86_64Depth, GcmImpl.callees, S.xdepth,
      v.ctr.noStack, v.gh.noStack, Nat.max_le, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte] <;>
    decide +kernel

theorem decryptI_depth : (Blocks.decrypt v.callees.ctr v.callees.gh (some p) aligned true).depth = 1 := by
  cases aligned <;>
    simp only [Blocks.decrypt, Blocks.blocks, Blocks.body, Blocks.head, Blocks.fullBody, Blocks.stitchPart,
      Blocks.scratchSetup, Blocks.tail, Blocks.ctrCall, Blocks.ghCall, Code.depth, GcmImpl.callees, S.depth,
      v.ctr.depth, v.gh.depth, Bool.false_eq_true, ↓reduceIte] <;> decide

theorem decryptI_nosp : NoSp (Blocks.decrypt v.callees.ctr v.callees.gh (some p) aligned true) := by
  have hc := ctr_nosp_all v.ctr
  have hg := gh_nosp_all v.gh
  refine nosp_of_all ?_
  cases aligned <;>
    simp only [Blocks.decrypt, Blocks.blocks, Blocks.body, Blocks.head, Blocks.fullBody, Blocks.stitchPart,
      Blocks.scratchSetup, Blocks.tail, Blocks.ctrCall, Blocks.ghCall, Code.allInstrs, GcmImpl.callees, S.nosp, hc,
      hg, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte] <;> decide +kernel

end

theorem idx16 (s : State) :
    s.mem.readW (Blocks.SP s + BitVec.ofNat 64 16) 32 = (Proof.AesGcm.arg s 1).setWidth 32 :=
  Proof.AesGcm.idx_readW s 1

theorem decryptI_correct (v : GcmImpl) (c : Blocks.DecCodeI CtxMode.prepared) :
    ∀ s, (Proof.AesGcm.decryptBlocksIv96X86_64M CtxMode.prepared).pre s →
      ∃ t s', Exec isa (Blocks.decrypt v.callees.ctr v.callees.gh (some c.dec) true true) s t s' ∧
        abiPreserved s s' ∧ Proof.AesGcm.decryptBlocksX86_64.post s s' := fun s h => by
  obtain ⟨hp, hx⟩ := Blocks.BP.ofMI h
  obtain ⟨t, s', he, hg, hq⟩ := Blocks.decryptI_wp v c hp hx
  exact ⟨t, s', he, abiPreserved_of_exec (decryptI_mx v c.S) he hg, hq⟩

theorem decryptI_ctP (v : GcmImpl) (c : Blocks.DecCodeI CtxMode.prepared) :
    ConstantTime isa (Proof.AesGcm.decryptBlocksIv96X86_64M CtxMode.prepared).pre Proof.AesGcm.blocksPubI
      (Blocks.decrypt v.callees.ctr v.callees.gh (some c.dec) true true) :=
  Blocks.decryptI_ct v c (k := Proof.AesGcm.decryptBlocksIv96X86_64M CtxMode.prepared) (fun _ h => Blocks.BP.ofMI h)
    fun s s' h => ⟨h.1, by rw [idx16, idx16]; exact h.2⟩

/-- With a loop given the block index. -/
theorem decryptBlocksPreparedIv96_verifiedI (v : GcmImpl) (c : Blocks.DecCodeI CtxMode.prepared) :
    Verified X86_64.target (Blocks.decrypt v.callees.ctr v.callees.gh (some c.dec) true true)
      (Spec.Gcm.decryptBlocksPreparedIv96Contract X86_64.abi 8) :=
  Verified.of_correct (k := Proof.AesGcm.decryptBlocksIv96X86_64M CtxMode.prepared) (decryptI_correct v c)
    (decryptI_ctP v c) decryptBlocksIv96_implies

/-- `vg_aes_gcm_decrypt_blocks_prepared_iv96` with a loop given the block
index, for its callers. -/
def decFnI (v : GcmImpl) (c : Blocks.DecCodeI CtxMode.prepared) : DecFnI CtxMode.prepared where
  fn := ⟨Spec.Gcm.decryptBlocksPreparedIv96Api.name ++ v.suffix,
    Blocks.decrypt v.callees.ctr v.callees.gh (some c.dec) true true⟩
  ok := decryptI_correct v c
  ct := decryptI_ctP v c
  nosp := decryptI_nosp v c.S
  depth := decryptI_depth v c.S
  mx := decryptI_mx v c.S
  sp := decryptI_spSafe v c.S
  xd := decryptI_xdepth v c.S

/-- With the loops of the function without the index, which ignore it. -/
theorem decryptBlocksPreparedIv96_verified (v : GcmImpl) (st : Option (StitchCode CtxMode.prepared true)) :
    Verified X86_64.target (Blocks.decrypt v.callees.ctr v.callees.gh (st.map (·.dec)) true (decFull st))
      (Spec.Gcm.decryptBlocksPreparedIv96Contract X86_64.abi 8) :=
  Verified.of_correct (k := Proof.AesGcm.decryptBlocksIv96X86_64M CtxMode.prepared)
    (fun s h => by
      obtain ⟨t, s', he, hg, hq⟩ := Blocks.decrypt_wpB v st (Blocks.BP.ofMI h).1
      exact ⟨t, s', he, abiPreserved_of_exec (decryptBlocks_mx v st) he hg, hq⟩)
    (Blocks.decrypt_ctG v st (k := Proof.AesGcm.decryptBlocksIv96X86_64M CtxMode.prepared) (fun _ h => (Blocks.BP.ofMI h).1) fun _ _ h => h.1)
    decryptBlocksIv96_implies

/-! ## Whole-block encryption out of place -/

/-- A state satisfying the precondition of `vg_aes_gcm_encrypt_blocks_to_prepared_iv96`. -/
def blocksToSatPI : State := { blocksToSat with rd := [⟨0x1000, 1024⟩, ⟨0x4000, 0⟩, ⟨0x8008, 32⟩] }

theorem encryptBlocksToIv96_pre : ∀ s, (Spec.Gcm.encryptBlocksToPreparedIv96Contract X86_64.abi 24).pre s →
    (Proof.AesGcm.encryptBlocksToIv96X86_64M CtxMode.prepared).pre s := by
  intro s h
  sig_pre [Spec.Gcm.encryptBlocksToPreparedIv96Contract, Spec.Gcm.encryptBlocksToPreparedIv96Sig,
        Spec.Gcm.encryptBlocksToPreparedIv96Pre, Spec.Gcm.encryptBlocksToPreparedIv96Post,
        Spec.Gcm.encryptBlocksToPreparedSig, Spec.Gcm.encryptBlocksToPrecomputedSig,
        Spec.Gcm.encryptBlocksToPreparedPre, Spec.Gcm.encryptBlocksToPost, Proof.AesGcm.encryptBlocksToIv96X86_64M,
        Proof.AesGcm.blocksToPost, Proof.AesGcm.blocksToPreMI, Proof.AesGcm.blocksToPubI, Proof.AesGcm.blocksToPub,
        X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
        X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
        X86_64.argRegs, CtxMode.prepared] at h
  sig_split h
  sig_reduce [Spec.Gcm.encryptBlocksToPreparedIv96Contract, Spec.Gcm.encryptBlocksToPreparedIv96Sig,
        Spec.Gcm.encryptBlocksToPreparedIv96Pre, Spec.Gcm.encryptBlocksToPreparedIv96Post,
        Spec.Gcm.encryptBlocksToPreparedSig, Spec.Gcm.encryptBlocksToPrecomputedSig,
        Spec.Gcm.encryptBlocksToPreparedPre, Spec.Gcm.encryptBlocksToPost, Proof.AesGcm.encryptBlocksToIv96X86_64M,
        Proof.AesGcm.blocksToPost, Proof.AesGcm.blocksToPreMI, Proof.AesGcm.blocksToPubI, Proof.AesGcm.blocksToPub,
        X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
        X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
        X86_64.argRegs, CtxMode.prepared]
  sig_simp [Spec.Gcm.encryptBlocksToPreparedIv96Contract, Spec.Gcm.encryptBlocksToPreparedIv96Sig,
        Spec.Gcm.encryptBlocksToPreparedIv96Pre, Spec.Gcm.encryptBlocksToPreparedIv96Post,
        Spec.Gcm.encryptBlocksToPreparedSig, Spec.Gcm.encryptBlocksToPrecomputedSig,
        Spec.Gcm.encryptBlocksToPreparedPre, Spec.Gcm.encryptBlocksToPost, Proof.AesGcm.encryptBlocksToIv96X86_64M,
        Proof.AesGcm.blocksToPost, Proof.AesGcm.blocksToPreMI, Proof.AesGcm.blocksToPubI, Proof.AesGcm.blocksToPub,
        X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
        X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
        X86_64.argRegs, CtxMode.prepared] []
  sig_and_intros
  sig_close
  all_goals first
    | with_reducible assumption
    | (rw [‹s.rd = _›]; exact Proof.AesGcm.inRegions_args4 _ _ _)
    | (rw [‹s.rd = _›]; exact Proof.AesGcm.covers_args4 _ _ _)
    | (rw [‹s.rd = _›]; simp)

theorem encryptBlocksToIv96_implies : (Proof.AesGcm.encryptBlocksToIv96X86_64M CtxMode.prepared).Implies
    (Spec.Gcm.encryptBlocksToPreparedIv96Contract X86_64.abi 24) :=
  { pre := encryptBlocksToIv96_pre
    post := by sig_implies_post [Spec.Gcm.encryptBlocksToPreparedIv96Contract, Spec.Gcm.encryptBlocksToPreparedIv96Sig,
        Spec.Gcm.encryptBlocksToPreparedIv96Pre, Spec.Gcm.encryptBlocksToPreparedIv96Post,
        Spec.Gcm.encryptBlocksToPreparedSig, Spec.Gcm.encryptBlocksToPrecomputedSig,
        Spec.Gcm.encryptBlocksToPreparedPre, Spec.Gcm.encryptBlocksToPost, Proof.AesGcm.encryptBlocksToIv96X86_64M,
        Proof.AesGcm.blocksToPost, Proof.AesGcm.blocksToPreMI, Proof.AesGcm.blocksToPubI, Proof.AesGcm.blocksToPub,
        X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
        X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
        X86_64.argRegs, CtxMode.prepared]
    pub := by sig_implies_pub [Spec.Gcm.encryptBlocksToPreparedIv96Contract, Spec.Gcm.encryptBlocksToPreparedIv96Sig,
        Spec.Gcm.encryptBlocksToPreparedIv96Pre, Spec.Gcm.encryptBlocksToPreparedIv96Post,
        Spec.Gcm.encryptBlocksToPreparedSig, Spec.Gcm.encryptBlocksToPrecomputedSig,
        Spec.Gcm.encryptBlocksToPreparedPre, Spec.Gcm.encryptBlocksToPost, Proof.AesGcm.encryptBlocksToIv96X86_64M,
        Proof.AesGcm.blocksToPost, Proof.AesGcm.blocksToPreMI, Proof.AesGcm.blocksToPubI, Proof.AesGcm.blocksToPub,
        X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
        X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
        X86_64.argRegs, CtxMode.prepared]
    sat := ⟨blocksToSatPI, by
      sig_pre [Spec.Gcm.encryptBlocksToPreparedIv96Contract, Spec.Gcm.encryptBlocksToPreparedIv96Sig,
        Spec.Gcm.encryptBlocksToPreparedIv96Pre, Spec.Gcm.encryptBlocksToPreparedSig,
        Spec.Gcm.encryptBlocksToPrecomputedSig, Spec.Gcm.encryptBlocksToPreparedPre, X86_64.abi, X86_64.argRegs,
        blocksToSatPI, blocksToSat]
      sig_and_intros
      all_goals first
        | rfl
        | decide
        | exact preparedPowersRepr_zero _
        | exact Region.disjoint_of_sep (by decide)⟩ }

section
variable {M : CtxMode} (B : BlkFn M) {aligned : Bool} {p : Prog isa} (S : PieceS p)
include S

theorem encryptToI_mx : (BlocksTo.encrypt B.enc (some p) aligned true).allInstrs (fun i => !loadsMxcsr i) = true := by
  have e := B.encMx
  cases aligned <;>
    simp only [BlocksTo.encrypt, BlocksTo.tail, BlocksTo.copyBlocks, BlocksTo.head, BlocksTo.stitchPart,
      Code.allInstrs, S.mxcsr, e, Bool.true_and, Bool.and_true, ↓reduceIte] <;> decide +kernel

theorem encryptToI_spSafe :
    (BlocksTo.encrypt B.enc (some p) aligned true).all (fun i => !X86_64.isa.writesSp i) = true := by
  have e := B.encSp
  cases aligned <;>
    simp only [BlocksTo.encrypt, BlocksTo.tail, BlocksTo.copyBlocks, BlocksTo.head, BlocksTo.stitchPart, Code.all,
      S.spSafe, e, Bool.true_and, Bool.and_true, ↓reduceIte] <;> decide +kernel

theorem encryptToI_xdepth : (BlocksTo.encrypt B.enc (some p) aligned true).x86_64Depth ≤ 24 := by
  have e := B.encXd
  cases aligned <;>
    simp only [BlocksTo.encrypt, BlocksTo.tail, BlocksTo.copyBlocks, BlocksTo.head, BlocksTo.stitchPart,
      Code.x86_64Depth, X86_64.Instr.frameBytes, List.length_cons, List.length_nil, S.xdepth, Nat.max_le] <;>
    omega

end

theorem idx32 (s : State) :
    s.mem.readW (BlocksTo.SP s + BitVec.ofNat 64 32) 32 = (Proof.AesGcm.arg s 3).setWidth 32 :=
  Proof.AesGcm.idx_readW s 3

/-- With a loop given the block index. -/
theorem encryptBlocksToPreparedIv96_verifiedI (B : BlkFn CtxMode.prepared) (c : BlocksTo.EncCodeI CtxMode.prepared) :
    Verified X86_64.target (BlocksTo.encrypt B.enc (some c.enc) true true)
      (Spec.Gcm.encryptBlocksToPreparedIv96Contract X86_64.abi 24) :=
  Verified.of_correct (k := Proof.AesGcm.encryptBlocksToIv96X86_64M CtxMode.prepared)
    (fun s h => by
      obtain ⟨hp, hx⟩ := BlocksTo.BT.ofMI h
      obtain ⟨t, s', he, hg, hq⟩ := BlocksTo.encryptI_wp B true c hp hx
      exact ⟨t, s', he, abiPreserved_of_exec (encryptToI_mx B c.S) he hg, hq⟩)
    (BlocksTo.encryptI_ct B true c (k := Proof.AesGcm.encryptBlocksToIv96X86_64M CtxMode.prepared)
      (fun _ h => BlocksTo.BT.ofMI h) fun s s' h => ⟨h.1, by rw [idx32, idx32]; exact h.2⟩)
    encryptBlocksToIv96_implies

/-- With the loop of the function without the index, which ignores it. -/
theorem encryptBlocksToPreparedIv96_verified (B : BlkFn CtxMode.prepared)
    (st : Option (StitchToCode CtxMode.prepared true)) :
    Verified X86_64.target (BlocksTo.encrypt B.enc (st.map (·.enc)) true (encFullTo st))
      (Spec.Gcm.encryptBlocksToPreparedIv96Contract X86_64.abi 24) :=
  Verified.of_correct (k := Proof.AesGcm.encryptBlocksToIv96X86_64M CtxMode.prepared)
    (fun s h => by
      obtain ⟨t, s', he, hg, hq⟩ := BlocksTo.encrypt_wpB B true (encFullTo st) (st.map (·.enc))
        (fun p e => by obtain ⟨i, rfl, rfl⟩ := Option.map_eq_some_iff.1 e; exact i.ok) (BlocksTo.BT.ofMI h).1
      exact ⟨t, s', he, abiPreserved_of_exec (encryptTo_mx st B) he hg, hq⟩)
    (BlocksTo.encrypt_ctG B st (k := Proof.AesGcm.encryptBlocksToIv96X86_64M CtxMode.prepared)
      (fun _ h => (BlocksTo.BT.ofMI h).1) fun _ _ h => h.1)
    encryptBlocksToIv96_implies

end VG.Proof.AesGcm.X86_64
