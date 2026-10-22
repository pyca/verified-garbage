module

public import VerifiedGarbage.Impl.Dsa.Arm.KeyRandom
public import VerifiedGarbage.Impl.Dsa.Arm.RandomSign

/-!
# Bounded DSA key generation on 32-bit ARM (AAPCS)

`vg_dsa_generate_key` keeps its state, the callee-saved registers and its
register arguments in a frame of its own, the randomized signer's, whose
base `r11` holds. It checks p||q||g with `vg_dsa_check_parameters` before
consuming any of the tape, samples x from [1, q) with one budget of 128
draws, then derives p||q||g||y||x with `vg_dsa_derive_key`. Each call's
stack arguments are pushed as a frame of eight registers (to keep `sp`
8-byte aligned). Every failure zeros the whole output, and every exit
clears the scalar and publishes the consumed draws (`RandomSign.finish`).
-/

@[expose] public section
namespace VG.Impl.Dsa.Arm.GenerateKey
open VG VG.Arm Random

/-- Save the callee-saved registers and the register arguments, and start
with no draws consumed and a failed status. -/
def entry : List Instr :=
  [.addSp .r12 0] ++ RandomSign.savedRegs.zipIdx.map (fun (r, i) => .str r .r12 (4 * i)) ++
  [.mov .r11 (.reg .r12), st .r0 oOut, st .r1 oOutLen, st .r2 oUsedPtr, st .r3 oKey,
    .mov .r0 (.imm 0), st .r0 oUsed, st .r0 oStatus]

/-- `vg_dsa_check_parameters(params, params_len, p_len, q_len, scratch,
scratch_len)`: the registers, then the stack arguments in `r4` and `r5`. -/
def checkArgs : List Instr :=
  [ld .r0 oKey, ld .r1 (arg KeyRandom.aParamsLen), ld .r2 (arg KeyRandom.aPLen), ld .r3 (arg KeyRandom.aQLen), ld .r4 (arg KeyRandom.aScratch),
    ld .r5 (arg KeyRandom.aScratchLen)]

/-- `vg_dsa_derive_key(out, out_len, params, params_len, p_len, x, q_len,
scratch, scratch_len)`, with the sampled x: the registers, then the stack
arguments in `r4`–`r8`. -/
def deriveArgs : List Instr :=
  [ld .r0 oOut, ld .r1 oOutLen, ld .r2 oKey, ld .r3 (arg KeyRandom.aParamsLen), ld .r4 (arg KeyRandom.aPLen),
    .dp .add .r5 .r11 (.imm (BitVec.ofNat 32 oNonce)), ld .r6 (arg KeyRandom.aQLen), ld .r7 (arg KeyRandom.aScratch),
    ld .r8 (arg KeyRandom.aScratchLen)]

/-- A call, its stack arguments pushed. -/
def callWith (name : String) (callee : Prog isa) : Prog isa :=
  .frame (.push [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11]) (.call name callee) (.pop .r4 32)

/-- With an accepted draw, derive the key; its result is the status. -/
def derived (derive : String) (deriveKey : Prog isa) : Prog isa :=
  .seq (.block [.cmp .r0 (.imm 1)])
    (.ite .eq (.seq (.block deriveArgs) (.seq (callWith derive deriveKey) (.block [st .r0 oStatus])))
      (.block []))

/-- A checked domain: sample, then derive. -/
def generate (derive : String) (deriveKey : Prog isa) : Prog isa :=
  .seq prepare (.seq KeyRandom.sample (derived derive deriveKey))

def body (check derive : String) (checkParameters deriveKey : Prog isa) : Prog isa :=
  .seq (.block entry)
    (.seq (.block checkArgs)
      (.seq (callWith check checkParameters)
        (.seq (.block [.cmp .r0 (.imm 0)])
          (.seq (.ite .eq (.block []) (generate derive deriveKey)) RandomSign.finish))))

/-- The frame keeps the state across the calls. -/
def code (check derive : String) (checkParameters deriveKey : Prog isa) : Prog isa :=
  .frame (.alloc frameBytes) (body check derive checkParameters deriveKey) (.free frameBytes)

end VG.Impl.Dsa.Arm.GenerateKey
