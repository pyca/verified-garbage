module

public import VerifiedGarbage.Impl.Dsa.X86.Random

/-!
# Randomized DSA signing on x86 (cdecl)

`vg_dsa_sign_random` keeps its state, a copy of the callee-saved registers
and the outgoing arguments of `vg_dsa_sign` in a frame of its own. Each
attempt samples a nonce and, if one is accepted, calls the supplied-nonce
signer; a zero result (a zero r or s) retries, up to eight attempts. Every
failure zeros the whole output, and every exit clears the nonce and
publishes the consumed draws.
-/

@[expose] public section
namespace VG.Impl.Dsa.X86.RandomSign
open VG VG.X86 VG.Impl.Mont.X86 Random

/-- Save the callee-saved registers, and start with no draws consumed. -/
def entry : List Instr :=
  [.store (sp oSaveEbx) .ebx, .store (sp oSaveEsi) .esi, .store (sp oSaveEdi) .edi,
    .store (sp oSaveEbp) .ebp, .mov .eax (.imm 0), .store (sp oUsed) .eax,
    .mov .eax (.imm 8), .store (sp oAttempts) .eax]

/-- Copy argument `j` to outgoing argument `i`. -/
def copyArg (j i : Nat) : List Instr := [.mov .eax (.mem (arg j)), .store (sp (4 * i)) .eax]

/-- `vg_dsa_sign(out, out_len, key, key_len, p_len, nonce, q_len, digest,
digest_len, scratch, scratch_len)`, with the sampled nonce. -/
def callArgs : List Instr :=
  copyArg aOut 0 ++ copyArg aOutLen 1 ++ copyArg aKey 2 ++ copyArg aKeyLen 3 ++
  copyArg aPLen 4 ++
  [.mov .eax (.reg .esp), .alu .add .eax (.imm (BitVec.ofNat 32 oNonce)), .store (sp 20) .eax] ++
  copyArg aQLen 6 ++ copyArg aDigest 7 ++ copyArg aDigestLen 8 ++ copyArg aScratch 9 ++
  copyArg aScratchLen 10

/-- Save the signer's result, and spend an attempt on a zero result. -/
def callFinish : Prog isa :=
  .seq (.block [.store (sp oStatus) .eax, .alu .cmp .eax (.imm 0)])
    (.ite .e
      (.seq (.block [.mov .eax (.mem (sp oAttempts)), .alu .sub .eax (.imm 1),
          .store (sp oAttempts) .eax])
        (.ite .ne (.block [.mov .eax (.imm 4), .store (sp oStatus) .eax]) (.block [])))
      (.block []))

/-- One attempt. Status 4 means a further attempt is needed. -/
def attempt (name : String) (signer : Prog isa) : Prog isa :=
  .seq sample
    (.seq (.block [.alu .cmp .eax (.imm 1)])
      (.ite .e (.seq (.block callArgs) (.seq (.call name signer) callFinish)) (.block [])))

/-- Zero the whole output. -/
def zeroOut : Prog isa :=
  .seq (.block [.mov .esi (.mem (arg aOut)), .mov .ecx (.mem (arg aOutLen)), .mov .eax (.imm 0)])
    (.loop (.block [.store8 (at_ .esi 0) .al, .alu .add .esi (.imm 1), .alu .sub .ecx (.imm 1)]) .ne)

/-- Zero the output on failure, clear the nonce, publish the consumption
(a 64-bit count), and restore the callee-saved registers. -/
def finish : Prog isa :=
  .seq (.block [.mov .eax (.mem (sp oStatus)), .alu .cmp .eax (.imm 1)])
    (.seq (.ite .ne zeroOut (.block []))
      (.block (clearNonce ++ [.mov .edx (.mem (arg aUsed)), .mov .eax (.mem (sp oUsed)),
        .store (at_ .edx 0) .eax, .mov .eax (.imm 0), .store (at_ .edx 4) .eax,
        .mov .ebx (.mem (sp oSaveEbx)), .mov .esi (.mem (sp oSaveEsi)),
        .mov .edi (.mem (sp oSaveEdi)), .mov .ebp (.mem (sp oSaveEbp)),
        .mov .eax (.mem (sp oStatus))])))

def body (name : String) (signer : Prog isa) : Prog isa :=
  .seq (.block entry)
    (.seq prepare
      (.seq (.block [.alu .cmp .eax (.imm 0)])
        (.seq (.ite .e (.block [.store (sp oStatus) .eax])
          (.loop (.seq (attempt name signer) (.block [.mov .eax (.mem (sp oStatus)),
            .alu .cmp .eax (.imm 4)])) .e)) finish)))

/-- The frame keeps the loop's state across the calls. -/
def code (name : String) (signer : Prog isa) : Prog isa :=
  .frame (.alloc frameBytes) (body name signer) (.free frameBytes)

end VG.Impl.Dsa.X86.RandomSign
