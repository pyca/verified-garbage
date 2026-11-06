module

import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.CT
import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksVerifiedP
public import VerifiedGarbage.Spec.Gcm.OutOfPlace
public import VerifiedGarbage.Proof.Gcm.OutOfPlaceContract
public import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Contract
public import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Piece
public import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Call
import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Fn

/-!
# AES-GCM on whole blocks out of place, x86-64: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant time
of `vg_aes_gcm_encrypt_blocks_to` calling any `vg_aes_gcm_encrypt_blocks` `B`
(with or without out-of-place interleaved loops `st`), its code's static
facts (no load of `mxcsr`, `rsp` kept, 24 bytes of stack), and the shared
contracts of `Spec/Gcm/OutOfPlace.lean`, for the key contexts of
`vg_aes_gcm_init` and `vg_aes_gcm_init_precomputed`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open Gcm.X86_64.Stitch (CtxMode)

section
variable {M : CtxMode} {aligned : Bool} (st : Option (StitchToCode M aligned))

theorem headTo_mx : (BlocksTo.head (st.map (·.enc)) aligned (encFullTo st)).allInstrs (fun i => !loadsMxcsr i) = true := by
  rcases st with _ | ⟨enc, full, ok, P⟩
  · rfl
  · simp only [Option.map, Option.any, encFullTo, BlocksTo.head, BlocksTo.stitchPart, Code.allInstrs, P.mxcsr]
    cases full <;> cases aligned <;> rfl

theorem headTo_spSafe : (BlocksTo.head (st.map (·.enc)) aligned (encFullTo st)).all (fun i => !X86_64.isa.writesSp i) = true := by
  rcases st with _ | ⟨enc, full, ok, P⟩
  · rfl
  · simp only [Option.map, Option.any, encFullTo, BlocksTo.head, BlocksTo.stitchPart, Code.all, P.spSafe]
    cases full <;> cases aligned <;> rfl

theorem headTo_xdepth : (BlocksTo.head (st.map (·.enc)) aligned (encFullTo st)).x86_64Depth = 0 := by
  rcases st with _ | ⟨enc, full, ok, P⟩
  · rfl
  · simp only [Option.map, Option.any, encFullTo, BlocksTo.head, BlocksTo.stitchPart, Code.x86_64Depth, P.xdepth]
    cases full <;> cases aligned <;> rfl

variable (B : BlkFn M)

theorem encryptTo_mx : (BlocksTo.encrypt B.enc (st.map (·.enc)) aligned (encFullTo st)).allInstrs (fun i => !loadsMxcsr i) = true := by
  have e := B.encMx
  simp only [BlocksTo.encrypt, BlocksTo.tail, BlocksTo.copyBlocks, Code.allInstrs, headTo_mx st, e,
    Bool.true_and, Bool.and_true]
  decide +kernel

theorem encryptTo_spSafe :
    (BlocksTo.encrypt B.enc (st.map (·.enc)) aligned (encFullTo st)).all (fun i => !X86_64.isa.writesSp i) = true := by
  have e := B.encSp
  simp only [BlocksTo.encrypt, BlocksTo.tail, BlocksTo.copyBlocks, Code.all, headTo_spSafe st, e,
    Bool.true_and, Bool.and_true]
  decide +kernel

theorem encryptTo_xdepth : (BlocksTo.encrypt B.enc (st.map (·.enc)) aligned (encFullTo st)).x86_64Depth ≤ 24 := by
  have e := B.encXd
  simp only [BlocksTo.encrypt, BlocksTo.tail, BlocksTo.copyBlocks, Code.x86_64Depth, X86_64.Instr.frameBytes,
    List.length_cons, List.length_nil, headTo_xdepth st, Nat.max_le]
  omega

theorem encryptToM_correct (s : State) (hs : (Proof.AesGcm.encryptBlocksToX86_64M M).pre s) :
    ∃ t s', Exec isa (BlocksTo.encrypt B.enc (st.map (·.enc)) aligned (encFullTo st)) s t s' ∧ abiPreserved s s' ∧
      Proof.AesGcm.blocksToPost s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := BlocksTo.encrypt_wp B aligned (encFullTo st) (st.map (·.enc))
    (fun p e => by obtain ⟨i, rfl, rfl⟩ := Option.map_eq_some_iff.1 e; exact i.ok) hs
  exact ⟨t, s', he, abiPreserved_of_exec (encryptTo_mx st B) he hg, hp⟩

end

end VG.Proof.AesGcm.X86_64
