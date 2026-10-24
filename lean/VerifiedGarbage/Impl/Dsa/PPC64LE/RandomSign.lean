module

public import VerifiedGarbage.Impl.Dsa.PPC64LE.Random
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Sign

/-!
# Randomized DSA signing on PPC64LE

`vg_dsa_sign_random(out = r3, out_len = r4, used = r5, key = r6,
key_len = r7, p_len = r8, q_len = r9, digest = r10, digest_len, rand,
rand_len, scratch, scratch_len)`, the last five on the stack. It runs in the
frame of `Random.lean`: the entry saves the nonvolatile registers and the
return address, writes `vg_dsa_sign`'s arguments on the stack (`digest_len`,
`scratch`, `scratch_len`), keeps the others in the nonvolatile registers
(`r22` the digest, `r26` the attempts left) and zeroes the nonce. After the
scan of q (`prepareQ`), each of up to eight attempts samples a nonce
(`sample`) and, if one is accepted, calls `vg_dsa_sign` with it; a zero
result (a zero r or s, or an inconsistent key) spends an attempt. A
failure zeroes `out` (`finish`), and every exit zeroes the nonce and
writes the octets of `rand` consumed to `used`.
-/

@[expose] public section

namespace VG.Impl.Dsa.PPC64LE.RandomSign

open VG VG.PPC64LE VG.Impl.Dsa.PPC64LE Random

/-- Save the registers, `vg_dsa_sign`'s arguments on the stack, the state's
registers, and zero the nonce. -/
def entry : List Instr :=
  saveRegs ++
    [.load .d .r0 .r12 (argOff 0), .store .d .r0 .r12 oArgs, .load .d .r0 .r12 (argOff 3),
      .store .d .r0 .r12 (oArgs + 8), .load .d .r0 .r12 (argOff 4), .store .d .r0 .r12 (oArgs + 16),
      .load .d .r23 .r12 (argOff 1), .load .d .r24 .r12 (argOff 2), .addi .r18 .r3 0, .addi .r30 .r5 0,
      .addi .r19 .r6 0, .addi .r20 .r8 0, .addi .r21 .r9 0, .addi .r22 .r10 0, .li .r25 0, .li .r26 8] ++
    clearNonce

/-- `vg_dsa_sign(out, 2 q_len, key, 3 p_len + 2 q_len, p_len, nonce, q_len,
digest)`. -/
def callArgs : List Instr :=
  [.addi .r3 .r18 0, .add .r4 .r21 .r21, .addi .r5 .r19 0, .add .r6 .r20 .r20, .add .r6 .r6 .r20,
    .add .r6 .r6 .r4, .addi .r7 .r20 0, .addSp .r8 oNonce, .addi .r9 .r21 0, .addi .r10 .r22 0]

/-- A signature: status 1; a zero result spends an attempt, and the status
is 4 while one is left, else 0. -/
def callFinish : Prog isa :=
  .ite (.zero .w .r3)
    (.seq (.block [.subi .r26 .r26 1]) (.ite (.nonzero .d .r26) (.block [.li .r31 4]) (.block [.li .r31 0])))
    (.block [.li .r31 1])

/-- One attempt. -/
def attempt : Prog isa :=
  .seq sample (.seq (.block [.subi .r3 .r31 1])
    (.ite (.zero .d .r3) (.seq (.block callArgs) (.seq (.call "vg_dsa_sign" Sign.sign) callFinish)) (.block [])))

/-- The attempts, while the status is 4. -/
def attempts : Prog isa := .loop (.seq attempt (.block [.subi .r3 .r31 4])) (.zero .d .r3)

/-- The frame's body. -/
def body : Prog isa :=
  .seq (.block entry) (.seq prepareQ (.seq (.ite (.zero .d .r0) (.block [.li .r31 0]) attempts)
    (finish [.add .r5 .r21 .r21])))

/-- `vg_dsa_sign_random`. -/
def code : Prog isa := .frame (.alloc frameBytes) body (.free frameBytes)

end VG.Impl.Dsa.PPC64LE.RandomSign
