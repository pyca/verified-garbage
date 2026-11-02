module

public import VerifiedGarbage.Impl.Dsa.RISCV64.Random
public import VerifiedGarbage.Impl.Dsa.RISCV64.Sign

/-!
# Randomized DSA signing on RISC-V

`vg_dsa_sign_random(out = a0, out_len = a1, used = a2, key = a3,
key_len = a4, p_len = a5, q_len = a6, digest = a7, digest_len, rand,
rand_len, scratch, scratch_len)`, the last five on the stack. As on PPC64LE
(`Impl/Dsa/PPC64LE/RandomSign.lean`), it runs in the frame of `Random.lean`:
the entry saves the callee-saved registers and the return address, writes
`vg_dsa_sign`'s arguments on the stack (`digest_len`, `scratch`,
`scratch_len`), keeps `out`, `used` and the digest in the frame and the
others in the callee-saved registers (`s6` the attempts left), and zeroes
the nonce. After the scan of q (`prepareQ`), each of up to eight attempts
samples a nonce (`sample`) and, if one is accepted, calls `vg_dsa_sign`
with it; a zero result (a zero r or s, or an inconsistent key) spends an
attempt. A failure zeroes `out` (`finish`), and every exit zeroes the
nonce and writes the octets of `rand` consumed to `used`.
-/

@[expose] public section

namespace VG.Impl.Dsa.RISCV64.RandomSign

open VG VG.RISCV64 VG.Impl.Dsa.RISCV64 Random

/-- Save the registers, `vg_dsa_sign`'s arguments on the stack, the state,
and zero the nonce. -/
def entry : List Instr :=
  saveRegs ++
    [.store .d .a0 .t0 oOut, .store .d .a2 .t0 oUsed, .store .d .a7 .t0 oDig, .addi .s1 .a3 0,
      .shift .sll .d .s2 .a6 16, .add .s2 .s2 .a5, .addSp .t6 frameBytes,
      .load .d .s3 .t6 8, .load .d .s4 .t6 16, .load .d .t1 .t6 0, .load .d .t2 .t6 24, .load .d .t3 .t6 32,
      .store .d .t1 .t0 0, .store .d .t2 .t0 8, .store .d .t3 .t0 16, .li .s5 0, .li .s6 8] ++
    clearNonce

/-- `vg_dsa_sign(out, 2 q_len, key, 3 p_len + 2 q_len, p_len, nonce, q_len,
digest)`. -/
def callArgs : List Instr :=
  [.addSp .t3 0, .load .d .a0 .t3 oOut] ++ lenQ .a6 ++ [.add .a1 .a6 .a6, .addi .a2 .s1 0] ++ lenP .a4 ++
    [.add .a3 .a4 .a4, .add .a3 .a3 .a4, .add .a3 .a3 .a1, .addSp .a5 oNonce, .load .d .a7 .t3 oDig]

/-- A signature: status 1; a zero result spends an attempt, and the status
is 4 while one is left, else 0. The result, a `u32`, is zero-extended first. -/
def callFinish : Prog isa :=
  .seq (.block [.shift .sll .d .a0 .a0 32, .shift .srl .d .a0 .a0 32])
    (.ite (.zero .a0)
      (.seq (.block [.addi .s6 .s6 (-1)]) (.ite (.nonzero .s6) (.block [.li .s10 4]) (.block [.li .s10 0])))
      (.block [.li .s10 1]))

/-- One attempt. -/
def attempt : Prog isa :=
  .seq sample (.seq (.block [.addi .a0 .s10 (-1)])
    (.ite (.zero .a0) (.seq (.block callArgs) (.seq (.call "vg_dsa_sign" Sign.sign) callFinish)) (.block [])))

/-- The attempts, while the status is 4. -/
def attempts : Prog isa := .loop (.seq attempt (.block [.addi .a0 .s10 (-4)])) (.zero .a0)

/-- The frame's body. -/
def body : Prog isa :=
  .seq (.block entry) (.seq prepareQ (.seq (.ite (.zero .a0) (.block [.li .s10 0]) attempts)
    (finish (lenQ .t5 ++ [.add .t5 .t5 .t5]))))

/-- `vg_dsa_sign_random`. -/
def code : Prog isa := .frame (.alloc frameBytes) body (.free frameBytes)

end VG.Impl.Dsa.RISCV64.RandomSign
