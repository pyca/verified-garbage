module

public import VerifiedGarbage.Impl.Dsa.PPC64LE.Random
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Params
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Derive

/-!
# DSA key generation on PPC64LE

`vg_dsa_generate_key(out = r3, out_len = r4, used = r5, params = r6,
params_len = r7, p_len = r8, q_len = r9, rand = r10, rand_len, scratch,
scratch_len)`, the last three on the stack. It runs in the frame of
`Random.lean`: the entry saves the nonvolatile registers and the return
address, writes `vg_dsa_derive_key`'s argument on the stack (`scratch_len`),
keeps the others in the nonvolatile registers (`r19` the domain, `r22`
`scratch`, `r26` `scratch_len`) and zeroes the nonce. It checks the domain
(`vg_dsa_check_parameters`); a valid one is scanned for q (`prepareQ`), a
scalar x is sampled into the nonce (`sample`), and, if one is accepted,
`vg_dsa_derive_key` writes p||q||g||y||x. A failure zeroes `out`
(`finish`), and every exit zeroes the nonce and writes the octets of `rand`
consumed to `used`.
-/

@[expose] public section

namespace VG.Impl.Dsa.PPC64LE.Generate

open VG VG.PPC64LE VG.Impl.Dsa.PPC64LE Random

/-- Save the registers, `vg_dsa_derive_key`'s argument on the stack, the
state's registers, and zero the nonce. -/
def entry : List Instr :=
  saveRegs ++
    [.addi .r18 .r3 0, .addi .r30 .r5 0, .addi .r19 .r6 0, .addi .r20 .r8 0, .addi .r21 .r9 0,
      .addi .r23 .r10 0, .load .d .r24 .r12 (argOff 0), .load .d .r22 .r12 (argOff 1),
      .load .d .r26 .r12 (argOff 2), .store .d .r26 .r12 oArgs, .li .r25 0] ++
    clearNonce

/-- `vg_dsa_check_parameters(params, 2 p_len + q_len, p_len, q_len, scratch,
scratch_len)`. -/
def checkArgs : List Instr :=
  [.addi .r3 .r19 0, .add .r4 .r20 .r20, .add .r4 .r4 .r21, .addi .r5 .r20 0, .addi .r6 .r21 0,
    .addi .r7 .r22 0, .addi .r8 .r26 0]

/-- `vg_dsa_derive_key(out, 3 p_len + 2 q_len, params, 2 p_len + q_len,
p_len, nonce, q_len, scratch)`. -/
def deriveArgs : List Instr :=
  [.addi .r3 .r18 0, .add .r4 .r20 .r20, .add .r4 .r4 .r20, .add .r4 .r4 .r21, .add .r4 .r4 .r21,
    .addi .r5 .r19 0, .add .r6 .r20 .r20, .add .r6 .r6 .r21, .addi .r7 .r20 0, .addSp .r8 oNonce,
    .addi .r9 .r21 0, .addi .r10 .r22 0]

/-- The key derived: status 1, else 0. -/
def deriveFinish : Prog isa :=
  .ite (.zero .w .r3) (.block [.li .r31 0]) (.block [.li .r31 1])

/-- With an accepted x (status 1), the derivation. -/
def derive : Prog isa :=
  .seq (.block [.subi .r3 .r31 1])
    (.ite (.zero .d .r3)
      (.seq (.block deriveArgs) (.seq (.call "vg_dsa_derive_key" Derive.derive) deriveFinish)) (.block []))

/-- A valid domain: the scan of q, and unless `q ≤ 1` the sampling and the derivation. -/
def valid : Prog isa :=
  .seq prepareQ (.ite (.zero .d .r0) (.block [.li .r31 0]) (.seq sample derive))

/-- The frame's body. -/
def body : Prog isa :=
  .seq (.block entry) (.seq (.seq (.block checkArgs) (.call "vg_dsa_check_parameters" Params.checkParameters))
    (.seq (.ite (.zero .w .r3) (.block [.li .r31 0]) valid)
      (finish [.add .r17 .r20 .r20, .add .r17 .r17 .r20, .add .r17 .r17 .r21, .add .r17 .r17 .r21])))

/-- `vg_dsa_generate_key`. -/
def code : Prog isa := .frame (.alloc frameBytes) body (.free frameBytes)

end VG.Impl.Dsa.PPC64LE.Generate
