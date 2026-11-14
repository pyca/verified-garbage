module

public import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86_64.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Cmac.TripleDesContract
public import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Lit

/-!
# Streaming TDEA-CMAC on x86-64: the shared contracts imply ours

The shared contracts with the working space as an argument, as
`Proof/CmacTripleDes/StreamScratch.lean` states them but with this target's
working space: the 120 bytes of the code of `init`, `update` and `finalize`
the functions run (slots 0–14), and for `absorb` 40 more, where it keeps our
caller's registers. `Frame.lean` moves them to the shared contracts of
`Spec/Cmac/TripleDesContract.lean`.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.X86_64

open VG VG.X86_64

/-! ## The contracts with the working space as an argument -/

/-- `vg_cmac_triple_des_stream_init` with `scratch: *mut [u64; 15]`. -/
def streamInitScratchSig15 : Sig where
  params := [("state", .array true .u64 52), ("key", .slice false .u8 "key_len"),
    ("scratch", .array true .u64 15)]

/-- `tdesStreamInitContract`, whatever `scratch` is. -/
def streamInitScratchContract15 {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamInitScratchSig15.contract A
    (pre := fun state key keyLen _scratch => Spec.Cmac.tdesStreamInitPre A.ptrBits state key keyLen)
    (post := fun state key keyLen _scratch => Spec.Cmac.tdesStreamInitPost A.ptrBits state key keyLen)
    (stack := stack)

/-- `vg_cmac_triple_des_absorb` with `scratch: *mut [u64; 20]`. -/
def absorbScratchSig20 : Sig where
  params := [("state", .array true .u64 52), ("count", .int .u64 true),
    ("data", .slice false .u8 "len"), ("scratch", .array true .u64 20)]

/-- `tdesAbsorbContract`, whatever `scratch` is. -/
def absorbScratchContract20 {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  absorbScratchSig20.contract A
    (post := fun state count data len _scratch => Spec.Cmac.tdesAbsorbPost A.ptrBits state count data len)
    (stack := stack)

/-- `vg_cmac_triple_des_finish` with `scratch: *mut [u64; 15]`. -/
def finishScratchSig15 : Sig where
  params := [("state", .array true .u64 52), ("count", .int .u64 true),
    ("out", .array true .u8 8), ("scratch", .array true .u64 15)]

/-- `tdesFinishContract`, whatever `scratch` is. -/
def finishScratchContract15 {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  finishScratchSig15.contract A
    (post := fun state count out _scratch => Spec.Cmac.tdesFinishPost A.ptrBits state count out)
    (stack := stack)

/-! ## The target's contracts imply them -/

/-- A state satisfying `vg_cmac_triple_des_stream_init`'s precondition. -/
def initSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x3000 | .rdx => 16 | .rcx => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x3000, 16⟩]
  wr := [⟨0x1000, 416⟩, ⟨0x4000, 120⟩]

theorem init_implies : initX86_64.Implies (streamInitScratchContract15 X86_64.abi 0) := by
  sig_implies [streamInitScratchContract15, streamInitScratchSig15, Spec.Cmac.tdesStreamInitPre,
    Spec.Cmac.tdesStreamInitPost, initX86_64, X86_64.abi, X86_64.argRegs] [initSat] using initSat

/-- A state satisfying `vg_cmac_triple_des_absorb`'s precondition (with no data). -/
def absorbSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rdx => 0x3000 | .r8 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x3000, 0⟩]
  wr := [⟨0x1000, 416⟩, ⟨0x4000, 160⟩]

theorem absorb_implies : absorbX86_64.Implies (absorbScratchContract20 X86_64.abi 0) := by
  sig_implies [absorbScratchContract20, absorbScratchSig20, Spec.Cmac.tdesAbsorbPost, absorbX86_64,
    X86_64.abi, X86_64.argRegs] [absorbSat] using absorbSat

/-- A state satisfying `vg_cmac_triple_des_finish`'s precondition. -/
def finishSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rdx => 0x2000 | .rcx => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 416⟩, ⟨0x2000, 8⟩, ⟨0x4000, 120⟩]

theorem finish_implies : finishX86_64.Implies (finishScratchContract15 X86_64.abi 0) := by
  sig_implies [finishScratchContract15, finishScratchSig15, Spec.Cmac.tdesFinishPost, finishX86_64,
    X86_64.abi, X86_64.argRegs] [finishSat] using finishSat

end VG.Proof.CmacTripleDes.Stream.X86_64
