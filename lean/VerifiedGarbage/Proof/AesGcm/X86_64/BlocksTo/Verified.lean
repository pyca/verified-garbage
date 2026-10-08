import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.CT
import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksVerifiedP
import VerifiedGarbage.Spec.Gcm.OutOfPlace

/-!
# AES-GCM on whole blocks out of place, x86-64: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant time
of `vg_aes_gcm_encrypt_blocks_to` calling any `vg_aes_gcm_encrypt_blocks` `B`
(with or without out-of-place interleaved loops `st`), its code's static
facts (no load of `mxcsr`, `rsp` kept, 24 bytes of stack), and the shared
contracts of `Spec/Gcm/OutOfPlace.lean`, for the key contexts of
`vg_aes_gcm_init` and `vg_aes_gcm_init_precomputed`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open Gcm.X86_64.Stitch (CtxMode)

section
variable {M : CtxMode} (st : Option (StitchToCode M))

theorem headTo_mx : (BlocksTo.head (st.map (·.enc))).allInstrs (fun i => !loadsMxcsr i) = true := by
  rcases st with _ | i
  · rfl
  · simp only [Option.map, BlocksTo.head, BlocksTo.stitchPart, Code.allInstrs, i.P.mxcsr]; decide

theorem headTo_spSafe : (BlocksTo.head (st.map (·.enc))).all (fun i => !X86_64.isa.writesSp i) = true := by
  rcases st with _ | i
  · rfl
  · simp only [Option.map, BlocksTo.head, BlocksTo.stitchPart, Code.all, i.P.spSafe]; decide

theorem headTo_xdepth : (BlocksTo.head (st.map (·.enc))).x86_64Depth = 0 := by
  rcases st with _ | i
  · rfl
  · simp only [Option.map, BlocksTo.head, BlocksTo.stitchPart, Code.x86_64Depth, i.P.xdepth]; decide

variable (B : BlkFn M)

theorem encryptTo_mx : (BlocksTo.encrypt B.enc (st.map (·.enc))).allInstrs (fun i => !loadsMxcsr i) = true := by
  have e := B.encMx
  simp only [BlocksTo.encrypt, BlocksTo.tail, BlocksTo.copyBlocks, Code.allInstrs, headTo_mx st, e,
    Bool.true_and, Bool.and_true]
  decide +kernel

theorem encryptTo_spSafe :
    (BlocksTo.encrypt B.enc (st.map (·.enc))).all (fun i => !X86_64.isa.writesSp i) = true := by
  have e := B.encSp
  simp only [BlocksTo.encrypt, BlocksTo.tail, BlocksTo.copyBlocks, Code.all, headTo_spSafe st, e,
    Bool.true_and, Bool.and_true]
  decide +kernel

theorem encryptTo_xdepth : (BlocksTo.encrypt B.enc (st.map (·.enc))).x86_64Depth ≤ 24 := by
  have e := B.encXd
  simp only [BlocksTo.encrypt, BlocksTo.tail, BlocksTo.copyBlocks, Code.x86_64Depth, X86_64.Instr.frameBytes,
    List.length_cons, List.length_nil, headTo_xdepth st, Nat.max_le]
  omega

theorem encryptToM_correct (s : State) (hs : (Proof.AesGcm.encryptBlocksToX86_64M M).pre s) :
    ∃ t s', Exec isa (BlocksTo.encrypt B.enc (st.map (·.enc))) s t s' ∧ abiPreserved s s' ∧
      Proof.AesGcm.blocksToPost s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := BlocksTo.encrypt_wp B (st.map (·.enc))
    (fun p e => by obtain ⟨i, -, rfl⟩ := Option.map_eq_some_iff.1 e; exact i.ok) hs
  exact ⟨t, s', he, abiPreserved_of_exec (encryptTo_mx st B) he hg, hp⟩

end

/-- A state satisfying the precondition of `vg_aes_gcm_encrypt_blocks_to` (with no data,
and `scratch` at 0). -/
def blocksToSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x2000 | .rcx => 0x3000 | .r8 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x4000, 0⟩, ⟨0x8008, 24⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 16⟩, ⟨0, 0⟩, ⟨0, 2112⟩]

theorem blocksTo_pre : ∀ s, (Spec.Gcm.encryptBlocksToContract X86_64.abi 24).pre s →
    (Proof.AesGcm.encryptBlocksToX86_64M Gcm.X86_64.Stitch.CtxMode.base).pre s := by
  intro s h
  sig_pre [Spec.Gcm.encryptBlocksToContract, Spec.Gcm.encryptBlocksToSig, Spec.Gcm.encryptBlocksToPre,
      Spec.Gcm.encryptBlocksToPost, Proof.AesGcm.encryptBlocksToX86_64M, Proof.AesGcm.blocksToPost,
      Proof.AesGcm.blocksToPreM, Proof.AesGcm.blocksToPub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args,
      Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs,
      Gcm.X86_64.Stitch.CtxMode.base] at h
  sig_split h
  sig_reduce [Spec.Gcm.encryptBlocksToContract, Spec.Gcm.encryptBlocksToSig, Spec.Gcm.encryptBlocksToPre,
      Spec.Gcm.encryptBlocksToPost, Proof.AesGcm.encryptBlocksToX86_64M, Proof.AesGcm.blocksToPost,
      Proof.AesGcm.blocksToPreM, Proof.AesGcm.blocksToPub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args,
      Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs,
      Gcm.X86_64.Stitch.CtxMode.base]
  sig_simp [Spec.Gcm.encryptBlocksToContract, Spec.Gcm.encryptBlocksToSig, Spec.Gcm.encryptBlocksToPre,
      Spec.Gcm.encryptBlocksToPost, Proof.AesGcm.encryptBlocksToX86_64M, Proof.AesGcm.blocksToPost,
      Proof.AesGcm.blocksToPreM, Proof.AesGcm.blocksToPub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args,
      Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs,
      Gcm.X86_64.Stitch.CtxMode.base] []
  sig_and_intros
  sig_close
  all_goals first
    | with_reducible assumption
    | with_reducible exact Region.Disjoint.symm ‹_›
    | omega
    | (simp only [Nat.mul_comm] at *
       first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
    | simp only [*, List.mem_cons, List.mem_singleton, true_or, or_true]
    | (have e : s.mem.readW (s.gpr .rsp + 16#64) 64 = s.gpr .r9 := ‹_›
       simp only [e] at *
       first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)

theorem blocksTo_implies : (Proof.AesGcm.encryptBlocksToX86_64M Gcm.X86_64.Stitch.CtxMode.base).Implies
    (Spec.Gcm.encryptBlocksToContract X86_64.abi 24) := by
  exact { pre := blocksTo_pre
          post := by sig_implies_post [Spec.Gcm.encryptBlocksToContract, Spec.Gcm.encryptBlocksToSig, Spec.Gcm.encryptBlocksToPre,
      Spec.Gcm.encryptBlocksToPost, Proof.AesGcm.encryptBlocksToX86_64M, Proof.AesGcm.blocksToPost,
      Proof.AesGcm.blocksToPreM, Proof.AesGcm.blocksToPub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args,
      Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs,
      Gcm.X86_64.Stitch.CtxMode.base]
          pub := by sig_implies_pub [Spec.Gcm.encryptBlocksToContract, Spec.Gcm.encryptBlocksToSig, Spec.Gcm.encryptBlocksToPre,
      Spec.Gcm.encryptBlocksToPost, Proof.AesGcm.encryptBlocksToX86_64M, Proof.AesGcm.blocksToPost,
      Proof.AesGcm.blocksToPreM, Proof.AesGcm.blocksToPub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args,
      Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs,
      Gcm.X86_64.Stitch.CtxMode.base]
          sat := by sig_implies_sat [Spec.Gcm.encryptBlocksToContract, Spec.Gcm.encryptBlocksToSig, Spec.Gcm.encryptBlocksToPre,
      Spec.Gcm.encryptBlocksToPost, Proof.AesGcm.encryptBlocksToX86_64M, Proof.AesGcm.blocksToPost,
      Proof.AesGcm.blocksToPreM, Proof.AesGcm.blocksToPub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args,
      Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs,
      Gcm.X86_64.Stitch.CtxMode.base] [blocksToSat] using blocksToSat }

/-- A state satisfying the precondition of `vg_aes_gcm_encrypt_blocks_to_precomputed`:
`blocksToSat`, with a key context of 1024 bytes. -/
def blocksToSatP : State := { blocksToSat with rd := [⟨0x1000, 1024⟩, ⟨0x4000, 0⟩, ⟨0x8008, 24⟩] }

theorem blocksToP_pre : ∀ s, (Spec.Gcm.encryptBlocksToPrecomputedContract X86_64.abi 24).pre s →
    (Proof.AesGcm.encryptBlocksToX86_64M Gcm.X86_64.Stitch.CtxMode.powers).pre s := by
  intro s h
  sig_pre [Spec.Gcm.encryptBlocksToPrecomputedContract, Spec.Gcm.encryptBlocksToPrecomputedSig, Spec.Gcm.encryptBlocksToPrecomputedPre,
      Spec.Gcm.encryptBlocksToPost, Proof.AesGcm.encryptBlocksToX86_64M, Proof.AesGcm.blocksToPost,
      Proof.AesGcm.blocksToPreM, Proof.AesGcm.blocksToPub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args,
      Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs,
      Gcm.X86_64.Stitch.CtxMode.powers] at h
  sig_split h
  sig_reduce [Spec.Gcm.encryptBlocksToPrecomputedContract, Spec.Gcm.encryptBlocksToPrecomputedSig, Spec.Gcm.encryptBlocksToPrecomputedPre,
      Spec.Gcm.encryptBlocksToPost, Proof.AesGcm.encryptBlocksToX86_64M, Proof.AesGcm.blocksToPost,
      Proof.AesGcm.blocksToPreM, Proof.AesGcm.blocksToPub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args,
      Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs,
      Gcm.X86_64.Stitch.CtxMode.powers]
  sig_simp [Spec.Gcm.encryptBlocksToPrecomputedContract, Spec.Gcm.encryptBlocksToPrecomputedSig, Spec.Gcm.encryptBlocksToPrecomputedPre,
      Spec.Gcm.encryptBlocksToPost, Proof.AesGcm.encryptBlocksToX86_64M, Proof.AesGcm.blocksToPost,
      Proof.AesGcm.blocksToPreM, Proof.AesGcm.blocksToPub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args,
      Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs,
      Gcm.X86_64.Stitch.CtxMode.powers] []
  sig_and_intros
  sig_close
  all_goals first
    | with_reducible assumption
    | with_reducible exact Region.Disjoint.symm ‹_›
    | omega
    | (simp only [Nat.mul_comm] at *
       first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
    | simp only [*, List.mem_cons, List.mem_singleton, true_or, or_true]
    | (have e : s.mem.readW (s.gpr .rsp + 16#64) 64 = s.gpr .r9 := ‹_›
       simp only [e] at *
       first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)

theorem blocksToP_implies : (Proof.AesGcm.encryptBlocksToX86_64M Gcm.X86_64.Stitch.CtxMode.powers).Implies
    (Spec.Gcm.encryptBlocksToPrecomputedContract X86_64.abi 24) := by
  exact { pre := blocksToP_pre
          post := by sig_implies_post [Spec.Gcm.encryptBlocksToPrecomputedContract, Spec.Gcm.encryptBlocksToPrecomputedSig, Spec.Gcm.encryptBlocksToPrecomputedPre,
      Spec.Gcm.encryptBlocksToPost, Proof.AesGcm.encryptBlocksToX86_64M, Proof.AesGcm.blocksToPost,
      Proof.AesGcm.blocksToPreM, Proof.AesGcm.blocksToPub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args,
      Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs,
      Gcm.X86_64.Stitch.CtxMode.powers]
          pub := by sig_implies_pub [Spec.Gcm.encryptBlocksToPrecomputedContract, Spec.Gcm.encryptBlocksToPrecomputedSig, Spec.Gcm.encryptBlocksToPrecomputedPre,
      Spec.Gcm.encryptBlocksToPost, Proof.AesGcm.encryptBlocksToX86_64M, Proof.AesGcm.blocksToPost,
      Proof.AesGcm.blocksToPreM, Proof.AesGcm.blocksToPub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args,
      Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs,
      Gcm.X86_64.Stitch.CtxMode.powers]
          sat := ⟨blocksToSatP, by
            sig_pre [Spec.Gcm.encryptBlocksToPrecomputedContract, Spec.Gcm.encryptBlocksToPrecomputedSig,
              Spec.Gcm.encryptBlocksToPrecomputedPre, X86_64.abi, X86_64.argRegs, blocksToSatP, blocksToSat]
            sig_and_intros
            all_goals first
              | rfl
              | decide
              | exact powersRepr_zero _
              | exact Region.disjoint_of_sep (by decide)⟩ }

theorem encryptBlocksTo_verified (B : BlkFn CtxMode.base) (st : Option (StitchToCode CtxMode.base)) :
    Verified X86_64.target (BlocksTo.encrypt B.enc (st.map (·.enc))) (Spec.Gcm.encryptBlocksToContract X86_64.abi 24) :=
  Verified.of_correct (k := Proof.AesGcm.encryptBlocksToX86_64M CtxMode.base) (encryptToM_correct st B)
    (BlocksTo.encrypt_ct B st) blocksTo_implies

theorem encryptBlocksToP_verified (B : BlkFn CtxMode.powers) (st : Option (StitchToCode CtxMode.powers)) :
    Verified X86_64.target (BlocksTo.encrypt B.enc (st.map (·.enc)))
      (Spec.Gcm.encryptBlocksToPrecomputedContract X86_64.abi 24) :=
  Verified.of_correct (k := Proof.AesGcm.encryptBlocksToX86_64M CtxMode.powers) (encryptToM_correct st B)
    (BlocksTo.encrypt_ct B st) blocksToP_implies

end VG.Proof.AesGcm.X86_64
