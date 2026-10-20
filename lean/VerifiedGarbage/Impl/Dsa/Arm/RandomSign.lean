module

public import VerifiedGarbage.Impl.Dsa.Arm.Random

/-!
# Randomized DSA signing on 32-bit ARM (AAPCS)

`vg_dsa_sign_random` keeps its state, the callee-saved registers and its
register arguments in a frame of its own, whose base `r11` holds. Each
attempt samples a nonce and, if one is accepted, calls the supplied-nonce
signer, its seven stack arguments pushed as a frame of eight registers (to
keep `sp` 8-byte aligned); a zero result (a zero r or s) retries, up to
eight attempts. Every failure zeros the whole output, and every exit clears
the nonce and publishes the consumed draws.
-/

@[expose] public section
namespace VG.Impl.Dsa.Arm.RandomSign
open VG VG.Arm Random

/-- The registers saved at `4i` of the frame; `r11` last, as it is the base. -/
def savedRegs : List Reg := [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr]

/-- Save the callee-saved registers and the register arguments, and start
with no draws consumed. -/
def entry : List Instr :=
  [.addSp .r12 0] ++ savedRegs.zipIdx.map (fun (r, i) => .str r .r12 (4 * i)) ++
  [.mov .r11 (.reg .r12), st .r0 oOut, st .r1 oOutLen, st .r2 oUsedPtr, st .r3 oKey,
    .mov .r0 (.imm 0), st .r0 oUsed, .mov .r0 (.imm 8), st .r0 oAttempts]

/-- `vg_dsa_sign(out, out_len, key, key_len, p_len, nonce, q_len, digest,
digest_len, scratch, scratch_len)`, with the sampled nonce: the registers,
then the stack arguments in `r4`–`r10`. -/
def callArgs : List Instr :=
  [ld .r0 oOut, ld .r1 oOutLen, ld .r2 oKey, ld .r3 (arg aKeyLen), ld .r4 (arg aPLen),
    .dp .add .r5 .r11 (.imm (BitVec.ofNat 32 oNonce)), ld .r6 (arg aQLen), ld .r7 (arg aDigest),
    ld .r8 (arg aDigestLen), ld .r9 (arg aScratch), ld .r10 (arg aScratchLen)]

/-- The call, its stack arguments pushed. -/
def callSigner (name : String) (signer : Prog isa) : Prog isa :=
  .frame (.push [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11]) (.call name signer) (.pop .r4 32)

/-- Save the signer's result, and spend an attempt on a zero result. -/
def callFinish : Prog isa :=
  .seq (.block [st .r0 oStatus, .cmp .r0 (.imm 0)])
    (.ite .eq
      (.seq (.block [ld .r0 oAttempts, .subs .r0 .r0 (.imm 1), st .r0 oAttempts])
        (.ite .ne (.block [.mov .r0 (.imm 4), st .r0 oStatus]) (.block [])))
      (.block []))

/-- One attempt. Status 4 means a further attempt is needed. -/
def attempt (name : String) (signer : Prog isa) : Prog isa :=
  .seq sample
    (.seq (.block [.cmp .r0 (.imm 1)])
      (.ite .eq (.seq (.block callArgs) (.seq (callSigner name signer) callFinish)) (.block [])))

/-- Zero the whole output. -/
def zeroOut : Prog isa :=
  .seq (.block [ld .r1 oOut, ld .r2 oOutLen, .mov .r0 (.imm 0)])
    (.loop (.block [.strb .r0 .r1 0, .dp .add .r1 .r1 (.imm 1), .subs .r2 .r2 (.imm 1)]) .ne)

/-- Zero the output on failure, clear the nonce, publish the consumption
(a 64-bit count), and restore the callee-saved registers, `r11` last. -/
def finish : Prog isa :=
  .seq (.block [ld .r0 oStatus, .cmp .r0 (.imm 1)])
    (.seq (.ite .ne zeroOut (.block []))
      (.block (clearNonce ++ [ld .r4 oUsedPtr, ld .r0 oUsed, .str .r0 .r4 0, .mov .r0 (.imm 0),
        .str .r0 .r4 4, ld .r0 oStatus] ++
        (savedRegs.zipIdx.filter (·.1 != .r11)).map (fun (r, i) => ld r (4 * i)) ++ [ld .r11 28])))

def body (name : String) (signer : Prog isa) : Prog isa :=
  .seq (.block entry)
    (.seq prepare
      (.seq (.block [.cmp .r0 (.imm 0)])
        (.seq (.ite .eq (.block [st .r0 oStatus])
          (.loop (.seq (attempt name signer) (.block [ld .r0 oStatus, .cmp .r0 (.imm 4)])) .eq)) finish)))

/-- The frame keeps the loop's state across the calls. -/
def code (name : String) (signer : Prog isa) : Prog isa :=
  .frame (.alloc frameBytes) (body name signer) (.free frameBytes)

end VG.Impl.Dsa.Arm.RandomSign
