import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.CT
import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Verified
import VerifiedGarbage.Proof.AesGcm.X86_64.Frame
import VerifiedGarbage.Proof.AesGcm.X86_64.VerifiedP
import VerifiedGarbage.Proof.AesGcm.ScratchTo

/-!
# AES-GCM streaming encryption out of place, x86-64: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant time
of `vg_aes_gcm_stream_encrypt_to` calling any `vg_aes_gcm_encrypt_blocks_to`
`T` and `vg_aes_gcm_stream_encrypt` `E` (`BlkToFn`, `EncFn`), its code's
static facts (no load of `mxcsr`, `rsp` written only in frames, 2624 bytes
of stack), the shared contracts with a `scratch` buffer appended
(`streamEncryptToScratchContract`), and the shared contracts of
`Spec/Gcm/OutOfPlace.lean` in a frame of 2232 bytes holding the working
space (`Verified.stackArgScratch`): its 2192 bytes, a copy of the three
other stack arguments, and 16 more, for 4856 bytes of stack in all; for the
key contexts of `vg_aes_gcm_init` and `vg_aes_gcm_init_precomputed`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.StreamTo

open VG VG.X86_64 VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.StreamTo
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)

/-! ## The callees -/

/-- `vg_aes_gcm_encrypt_blocks_to`, named `n`, calling `B` and the loops `st`. -/
def BlkToFn.ofBlocks {M : CtxMode} (n : String) (B : BlkFn M) {aligned : Bool} (st : Option (StitchToCode M aligned)) : BlkToFn M where
  fn := ⟨n, BlocksTo.encrypt B.enc (st.map (·.enc)) aligned (encFullTo st)⟩
  ok := encryptToM_correct st B
  ct := BlocksTo.encrypt_ct B st
  sp := SpSafe.of_all (encryptTo_spSafe st B)
  xd := encryptTo_xdepth st B
  mx := encryptTo_mx st B
  spAll := encryptTo_spSafe st B

theorem framed_mx {bytes m : Nat} {c : Prog isa} (h : c.allInstrs (fun i => !loadsMxcsr i) = true) :
    (Impl.StackScratch.X86_64.withStackArgScratch bytes m c).allInstrs (fun i => !loadsMxcsr i) = true := by
  have hc : ((List.range m).flatMap (Impl.StackScratch.X86_64.copyArg bytes)).all (fun i => !loadsMxcsr i) =
      true :=
    List.all_eq_true.mpr fun i hi => by
      obtain ⟨j, -, hj⟩ := List.mem_flatMap.mp hi
      simp only [Impl.StackScratch.X86_64.copyArg, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl <;> rfl
  rw [Code.allInstrs_eq] at h ⊢
  simp only [Impl.StackScratch.X86_64.withStackArgScratch, Impl.StackScratch.X86_64.setArgs, instrs,
    List.all_append, List.all_cons, List.all_nil, h, hc, Bool.and_true, Bool.true_and]
  rfl

theorem framed_xdepth {bytes m d : Nat} {c : Prog isa} (h : c.x86_64Depth ≤ d) :
    (Impl.StackScratch.X86_64.withStackArgScratch bytes m c).x86_64Depth ≤ d + bytes := by
  simp only [Impl.StackScratch.X86_64.withStackArgScratch, Code.x86_64Depth, X86_64.Instr.frameBytes]
  omega

/-! ## The code -/

section
variable {M : CtxMode} (T : BlkToFn M) (E : EncFn M)

theorem encrypt_mx : (encrypt T.fn E.fn).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [encrypt, head, blocks, rest, Code.allInstrs, T.mx, E.mx, Bool.true_and, Bool.and_true]
  decide +kernel

theorem encrypt_spAll : (encrypt T.fn E.fn).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [encrypt, head, blocks, rest, Code.all, T.spAll, E.spAll, Bool.true_and, Bool.and_true]
  decide +kernel

theorem encrypt_xdepth : (encrypt T.fn E.fn).x86_64Depth ≤ 2624 := by
  have t := T.xd
  have e := E.xd
  simp only [encrypt, head, blocks, rest, copyLoop, Code.x86_64Depth, X86_64.Instr.frameBytes, List.length_cons,
    List.length_nil, Nat.max_le]
  omega

theorem encrypt_correct (s : State) (hs : (Proof.AesGcm.streamEncryptToX86_64M M).pre s) :
    ∃ t s', Exec isa (encrypt T.fn E.fn) s t s' ∧ abiPreserved s s' ∧ Proof.AesGcm.streamToPost s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := encrypt_wp T E hs
  exact ⟨t, s', he, abiPreserved_of_exec (encrypt_mx T E) he hg, hp⟩

end

/-! ## The contracts -/

/-- A state satisfying the precondition of `vg_aes_gcm_stream_encrypt_to`
with its working space (with no data, and `dst` and `scratch` at 0). -/
def streamToSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x3000 | .r9 => 0x4000 | .rsp => 0x9000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x4000, 0⟩, ⟨0x9008, 32⟩]
  wr := [⟨0x3000, 80⟩, ⟨0, 0⟩, ⟨0, 2192⟩]

theorem streamTo_implies : (Proof.AesGcm.streamEncryptToX86_64M CtxMode.base).Implies
    (Proof.AesGcm.streamEncryptToScratchContract X86_64.abi 2624) := by
  sig_implies [Proof.AesGcm.streamEncryptToScratchContract, Proof.AesGcm.streamEncryptToScratchSig,
      Spec.Gcm.streamEncryptToPre, Spec.Gcm.streamEncryptToPost, Proof.AesGcm.streamEncryptToX86_64M,
      Proof.AesGcm.streamToPreM, Proof.AesGcm.streamToPost, Proof.AesGcm.streamToPub, X86_64.abi,
      Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stkS, Proof.AesGcm.ret, Proof.AesGcm.rounds,
      X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs, CtxMode.base] [streamToSat] using streamToSat

/-- `streamToSat`, with a key context of 1024 bytes. -/
def streamToSatP : State := { streamToSat with rd := [⟨0x1000, 1024⟩, ⟨0x4000, 0⟩, ⟨0x9008, 32⟩] }

theorem streamToP_implies : (Proof.AesGcm.streamEncryptToX86_64M CtxMode.powers).Implies
    (Proof.AesGcm.streamEncryptToPrecomputedScratchContract X86_64.abi 2624) := by
  exact { pre := by sig_implies_pre [Proof.AesGcm.streamEncryptToPrecomputedScratchContract,
      Proof.AesGcm.streamEncryptToPrecomputedScratchSig, Spec.Gcm.streamEncryptToPrecomputedPre,
      Spec.Gcm.streamEncryptToPost, Proof.AesGcm.streamEncryptToX86_64M,
      Proof.AesGcm.streamToPreM, Proof.AesGcm.streamToPost, Proof.AesGcm.streamToPub, X86_64.abi,
      Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stkS, Proof.AesGcm.ret, Proof.AesGcm.rounds,
      X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs, CtxMode.powers]
          post := by sig_implies_post [Proof.AesGcm.streamEncryptToPrecomputedScratchContract,
      Proof.AesGcm.streamEncryptToPrecomputedScratchSig, Spec.Gcm.streamEncryptToPrecomputedPre,
      Spec.Gcm.streamEncryptToPost, Proof.AesGcm.streamEncryptToX86_64M,
      Proof.AesGcm.streamToPreM, Proof.AesGcm.streamToPost, Proof.AesGcm.streamToPub, X86_64.abi,
      Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stkS, Proof.AesGcm.ret, Proof.AesGcm.rounds,
      X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs, CtxMode.powers]
          pub := by sig_implies_pub [Proof.AesGcm.streamEncryptToPrecomputedScratchContract,
      Proof.AesGcm.streamEncryptToPrecomputedScratchSig, Spec.Gcm.streamEncryptToPrecomputedPre,
      Spec.Gcm.streamEncryptToPost, Proof.AesGcm.streamEncryptToX86_64M,
      Proof.AesGcm.streamToPreM, Proof.AesGcm.streamToPost, Proof.AesGcm.streamToPub, X86_64.abi,
      Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stkS, Proof.AesGcm.ret, Proof.AesGcm.rounds,
      X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs, CtxMode.powers]
          sat := ⟨streamToSatP, by
            sig_pre [Proof.AesGcm.streamEncryptToPrecomputedScratchContract,
              Proof.AesGcm.streamEncryptToPrecomputedScratchSig, Spec.Gcm.streamEncryptToPrecomputedPre,
              X86_64.abi, X86_64.argRegs, streamToSatP, streamToSat]
            sig_and_intros
            all_goals first
              | rfl
              | decide
              | exact powersRepr_of_zero fun _ _ => rfl
              | exact Region.disjoint_of_sep (by decide)⟩ }

theorem streamEncryptTo_core (T : BlkToFn CtxMode.base) (E : EncFn CtxMode.base) :
    Verified X86_64.target (encrypt T.fn E.fn) (Proof.AesGcm.streamEncryptToScratchContract X86_64.abi 2624) :=
  Verified.of_correct (k := Proof.AesGcm.streamEncryptToX86_64M CtxMode.base) (encrypt_correct T E)
    (encrypt_ct T E) streamTo_implies

theorem streamEncryptToP_core (T : BlkToFn CtxMode.powers) (E : EncFn CtxMode.powers) :
    Verified X86_64.target (encrypt T.fn E.fn)
      (Proof.AesGcm.streamEncryptToPrecomputedScratchContract X86_64.abi 2624) :=
  Verified.of_correct (k := Proof.AesGcm.streamEncryptToX86_64M CtxMode.powers) (encrypt_correct T E)
    (encrypt_ct T E) streamToP_implies

/-! ## In its frame -/

/-- A state satisfying the precondition of `vg_aes_gcm_stream_encrypt_to`,
without the working space. -/
def streamToFrameSat : State :=
  { streamToSat with rd := [⟨0x1000, 256⟩, ⟨0x4000, 0⟩, ⟨0x9008, 24⟩], wr := [⟨0x3000, 80⟩, ⟨0, 0⟩] }

theorem streamToFrameSat_pre : ∃ s, (Spec.Gcm.streamEncryptToContract X86_64.abi 4856).pre s := by
  implies_sat [Spec.Gcm.streamEncryptToContract, Spec.Gcm.streamEncryptToSig, Spec.Gcm.streamEncryptToPre,
    Spec.Gcm.streamEncryptToPost, X86_64.abi, X86_64.argRegs] [streamToFrameSat, streamToSat]
    using streamToFrameSat

theorem streamEncryptTo_framed (T : BlkToFn CtxMode.base) (E : EncFn CtxMode.base) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackArgScratch 2232 3 (encrypt T.fn E.fn))
      (Spec.Gcm.streamEncryptToContract X86_64.abi 4856) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Gcm.streamEncryptToSig) (nm := "scratch") (e := .u64)
    (n := 274) (pre := Spec.Gcm.streamEncryptToPre X86_64.abi.ptrBits)
    (post := Spec.Gcm.streamEncryptToPost X86_64.abi.ptrBits) (wa := true) (stack := 2624)
    (bytes := 2232) (streamEncryptTo_core T E) (by decide) (by decide) (by decide)
    (encrypt_spAll T E) (encrypt_xdepth T E) (Proof.AesGcm.streamEncryptToPre_local _)
    (Proof.AesGcm.streamEncryptToPost_local _) streamToFrameSat_pre

/-- `streamToFrameSat`, with a key context of 1024 bytes. -/
def streamToFrameSatP : State := { streamToFrameSat with rd := [⟨0x1000, 1024⟩, ⟨0x4000, 0⟩, ⟨0x9008, 24⟩] }

theorem streamToFrameSatP_pre : ∃ s, (Spec.Gcm.streamEncryptToPrecomputedContract X86_64.abi 4856).pre s := by
  refine ⟨streamToFrameSatP, ?_⟩
  sig_pre [Spec.Gcm.streamEncryptToPrecomputedContract, Spec.Gcm.streamEncryptToPrecomputedSig,
    Spec.Gcm.streamEncryptToPrecomputedPre, Spec.Gcm.streamEncryptToPost, X86_64.abi, X86_64.argRegs,
    streamToFrameSatP, streamToFrameSat, streamToSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact powersRepr_of_zero fun _ _ => rfl

theorem streamEncryptToP_framed (T : BlkToFn CtxMode.powers) (E : EncFn CtxMode.powers) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackArgScratch 2232 3 (encrypt T.fn E.fn))
      (Spec.Gcm.streamEncryptToPrecomputedContract X86_64.abi 4856) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Gcm.streamEncryptToPrecomputedSig) (nm := "scratch")
    (e := .u64) (n := 274) (pre := Spec.Gcm.streamEncryptToPrecomputedPre X86_64.abi.ptrBits)
    (post := Spec.Gcm.streamEncryptToPost X86_64.abi.ptrBits) (wa := true) (stack := 2624)
    (bytes := 2232) (streamEncryptToP_core T E) (by decide) (by decide) (by decide)
    (encrypt_spAll T E) (encrypt_xdepth T E) (Proof.AesGcm.streamEncryptToPrecomputedPre_local _)
    (Proof.AesGcm.streamEncryptToPrecomputedPost_local _) streamToFrameSatP_pre

end VG.Proof.AesGcm.X86_64.StreamTo
