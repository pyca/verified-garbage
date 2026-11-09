module

public import VerifiedGarbage.Impl.Dsa.RISCV64.Random
public import VerifiedGarbage.Impl.Dsa.RISCV64.Params
public import VerifiedGarbage.Impl.Dsa.RISCV64.Derive
public import VerifiedGarbage.Impl.Dsa.RISCV64.Prevalidated

/-!
# DSA key generation on RISC-V

`vg_dsa_generate_key(out = a0, out_len = a1, used = a2, params = a3,
params_len = a4, p_len = a5, q_len = a6, rand = a7, rand_len, scratch,
scratch_len)`, the last three on the stack. As on PPC64LE
(`Impl/Dsa/PPC64LE/Generate.lean`), it runs in the frame of `Random.lean`:
the entry saves the callee-saved registers and the return address, writes
the derivation's argument on the stack (`scratch_len`), keeps `out` and
`used` in the frame and the others in the callee-saved registers (`s1` the
domain, `s6` `scratch`) and zeroes the nonce. It checks the domain
(`vg_dsa_check_parameters`); a valid one is scanned for q (`prepareQ`), a
scalar x is sampled into the nonce (`sample`), and, if one is accepted,
`vg_dsa_derive_key_checked` (`deriveChecked`), the derivation without the
domain's checks, which have passed, writes p||q||g||y||x. A failure zeroes
`out` (`finish`), and every exit zeroes the nonce and writes the octets of `rand`
consumed to `used`. The callees' results, `u32`s, are zero-extended before
they are tested.
-/

@[expose] public section

namespace VG.Impl.Dsa.RISCV64.Generate

open VG VG.RISCV64 VG.Impl.Dsa.RISCV64 Random

/-- Save the registers, the derivation's argument on the stack, the
state, and zero the nonce. -/
def entry : List Instr :=
  saveRegs ++
    [.store .d .a0 .t0 oOut, .store .d .a2 .t0 oUsed, .addi .s1 .a3 0, .shift .sll .d .s2 .a6 16,
      .add .s2 .s2 .a5, .addi .s3 .a7 0, .addSp .t6 frameBytes, .load .d .s4 .t6 0, .load .d .s6 .t6 8,
      .load .d .t1 .t6 16, .store .d .t1 .t0 0, .li .s5 0] ++
    clearNonce

/-- `vg_dsa_derive_key_checked`, an internal function: `vg_dsa_derive_key`
(`Derive.derive`, with its arguments) for a domain that passes the checks,
which its caller has made. Of the checks of the domain it keeps only the
sizes, which give q's significant octets, and sets up the working spaces as
they leave them (`Prevalidated.setup`), so it does not compute `g^q mod p`
again; it checks x and y as `Derive.body` does. -/
def deriveChecked : Prog isa :=
  .seq (.block Derive.entry) (.seq (Prevalidated.setup Derive.body Derive.zeroOut) (.block restore))

/-- `a0`, a `u32`, zero-extended. -/
def zx : List Instr := [.shift .sll .d .a0 .a0 32, .shift .srl .d .a0 .a0 32]

/-- `vg_dsa_check_parameters(params, 2 p_len + q_len, p_len, q_len, scratch,
scratch_len)`. -/
def checkArgs : List Instr :=
  [.addi .a0 .s1 0] ++ lenP .a2 ++ lenQ .a3 ++
    [.add .a1 .a2 .a2, .add .a1 .a1 .a3, .addi .a4 .s6 0, .addSp .t3 0, .load .d .a5 .t3 0]

/-- `vg_dsa_derive_key_checked(out, 3 p_len + 2 q_len, params, 2 p_len + q_len,
p_len, nonce, q_len, scratch)`. -/
def deriveArgs : List Instr :=
  [.addSp .t3 0, .load .d .a0 .t3 oOut] ++ lenP .a4 ++ lenQ .a6 ++
    [.add .a3 .a4 .a4, .add .a3 .a3 .a6, .add .a1 .a3 .a4, .add .a1 .a1 .a6, .addi .a2 .s1 0,
      .addSp .a5 oNonce, .addi .a7 .s6 0]

/-- The key derived: status 1, else 0. -/
def deriveFinish : Prog isa :=
  .seq (.block zx) (.ite (.zero .a0) (.block [.li .s10 0]) (.block [.li .s10 1]))

/-- With an accepted x (status 1), the derivation. -/
def derive : Prog isa :=
  .seq (.block [.addi .a0 .s10 (-1)])
    (.ite (.zero .a0)
      (.seq (.block deriveArgs) (.seq (.call "vg_dsa_derive_key_checked" deriveChecked) deriveFinish)) (.block []))

/-- A valid domain: the scan of q, and unless `q ≤ 1` the sampling and the derivation. -/
def valid : Prog isa :=
  .seq prepareQ (.ite (.zero .a0) (.block [.li .s10 0]) (.seq sample derive))

/-- `t5 := 3 p_len + 2 q_len`. -/
def outLen : List Instr :=
  lenP .t5 ++ lenQ .t2 ++ [.add .t1 .t5 .t5, .add .t5 .t5 .t1, .add .t5 .t5 .t2, .add .t5 .t5 .t2]

/-- The frame's body. -/
def body : Prog isa :=
  .seq (.block entry) (.seq (.seq (.block checkArgs) (.call "vg_dsa_check_parameters" Params.checkParameters))
    (.seq (.seq (.block zx) (.ite (.zero .a0) (.block [.li .s10 0]) valid)) (finish outLen)))

/-- `vg_dsa_generate_key`. -/
def code : Prog isa := .frame (.alloc frameBytes) body (.free frameBytes)

end VG.Impl.Dsa.RISCV64.Generate
