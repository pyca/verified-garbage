module

public import VerifiedGarbage.Impl.Dsa.PPC64LE.Common

/-!
# DSA on PPC64LE: the frame of the randomized functions, and rejection sampling

`vg_dsa_sign_random` and `vg_dsa_generate_key` run in a frame of
`frameBytes` bytes on the stack, which holds, above its 32-byte header:

* at `r1 + 96`, the arguments on the stack of the function they call
  (`vg_dsa_sign`'s `digest_len`, `scratch` and `scratch_len`, or
  `vg_dsa_derive_key`'s `scratch_len`), at the start of its Parameter Save
  Area's doubleword 8 (ELFv2 §2.2.3.3), written once on entry;
* at `r1 + oNonce`, the 32 octets of the nonce (or of x), the sampled
  scalar's `q_len` octets, big-endian, zeroed on entry and on exit;
* at `r1 + oSave`, the caller's `r14`–`r31` (`saveRegs`), and at
  `r1 + oLr` our return address.

The state lives in the nonvolatile registers, which the calls keep:
`r18` `out`, `r19` the key (or the domain p||q||g), `r20` `p_len`, `r21`
`q_len`, `r23` `rand`, `r24` `rand_len`, `r25` the octets of `rand`
consumed, `r27` the address of q's first significant octet, `r28` their
count (the width of a draw), `r29` the mask of its significant bits, `r30`
`used`, `r31` the status (4 while sampling or signing goes on).

`prepare` scans q (public): its significant octets (`sigLen`), the address
of the first, the mask of its bits (smeared right) and `r0 ≠ 0` exactly
when `q > 1`. `sample` draws up to 128 candidates of `r28` octets from
`rand + r25`: each is copied, its first octet masked, to the nonce's last
`r28` octets (the others stay zero), and compared with q (a borrow chain
and an or of the octets, without a branch); it leaves the status 1
(accepted), 2 (short tape) or 0 (128 rejections). Only the tape's length,
the count of draws and each candidate's acceptance reach a branch or an
address, as the contracts allow.
-/

@[expose] public section

namespace VG.Impl.Dsa.PPC64LE.Random

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE

/-! ## The frame -/

/-- The size of the frame. -/
def frameBytes : Nat := 304

/-- The callee's arguments on the stack. -/
def oArgs : Nat := 96

/-- The nonce's 32 octets. -/
def oNonce : Nat := 120

/-- The saved `r14`–`r31`. -/
def oSave : Nat := 152

/-- Our return address. -/
def oLr : Nat := 296

/-- Our `i`-th argument on the stack, above the frame. -/
def argOff (i : Nat) : Nat := frameBytes + 96 + 8 * i

/-- The nonvolatile registers saved, `r14`–`r31`. -/
def nv (i : Nat) : Reg :=
  [.r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30,
    .r31].getD i .r14

/-- Save `r14`–`r31` and the return address, through `r12 = r1`. -/
def saveRegs : List Instr :=
  [.addSp .r12 0] ++ (List.range 18).flatMap (fun i => [.store .d (nv i) .r12 (oSave + 8 * i)]) ++
    [.mflr .r0, .store .d .r0 .r12 oLr]

/-- Zero the nonce's 32 octets, through `r12 = r1`. -/
def clearNonce : List Instr :=
  [.addSp .r12 0, .li .r0 0, .store .d .r0 .r12 oNonce, .store .d .r0 .r12 (oNonce + 8),
    .store .d .r0 .r12 (oNonce + 16), .store .d .r0 .r12 (oNonce + 24)]

/-- Restore the return address and `r14`–`r31`. -/
def restoreRegs : List Instr :=
  [.addSp .r12 0, .load .d .r0 .r12 oLr, .mtlr .r0] ++
    (List.range 18).flatMap (fun i => [.load .d (nv i) .r12 (oSave + 8 * i)])

/-! ## The scan of q -/

/-- With q's `q_len` octets at `r12` (`r6 = q_len`): `r28 :=` its significant
octets, `r27 :=` the address of the first, `r29 :=` the mask of its
significant bits, and `r0 ≠ 0` exactly when `q > 1` (two significant
octets, or a first one of at least 2). -/
def prepare : Prog isa :=
  .seq sigLen (.block [.addi .r28 .r16 0, .add .r27 .r12 .r6, .sub .r27 .r27 .r16, .lbz .r3 .r27 0,
    .lsr .d .r4 .r3 1, .logic .or .r29 .r3 .r4, .lsr .d .r4 .r29 2, .logic .or .r29 .r29 .r4,
    .lsr .d .r4 .r29 4, .logic .or .r29 .r29 .r4,
    .lsr .d .r4 .r16 1, .lsr .d .r5 .r3 1, .logic .or .r4 .r4 .r5, .li .r5 0, .sub .r4 .r5 .r4,
    .lsr .d .r4 .r4 63, .sub .r5 .r5 .r16, .lsr .d .r5 .r5 63, .logic .and .r0 .r4 .r5])

/-- The scan of q at `r19 + r20` (`q_len` octets). -/
def prepareQ : Prog isa := .seq (.block [.add .r12 .r19 .r20, .addi .r6 .r21 0]) prepare

/-! ## A draw -/

/-- `r3 := 1` exactly when the tape has fewer than `r28` octets left:
`rand_len − used < width`, by the sign of the difference unless the
octets left are `2⁶³` or more. -/
def shortTest : List Instr :=
  [.sub .r3 .r24 .r25, .sub .r4 .r3 .r28, .lsr .d .r4 .r4 63, .lsr .d .r3 .r3 63, .li .r5 1,
    .logic .xor .r3 .r3 .r5, .logic .and .r3 .r3 .r4]

/-- The draw's place: the tape at `rand + used` (`r3`), the nonce's last
`r28` octets (`r4`), the count (`r5`) and the first octet's mask (`r6`). -/
def copyInit : List Instr :=
  [.add .r3 .r23 .r25, .addSp .r4 oNonce, .add .r4 .r4 .r21, .sub .r4 .r4 .r28, .addi .r5 .r28 0,
    .addi .r6 .r29 0]

/-- An octet of the draw, masked by `r6`, which is all ones after the first. -/
def copyByte : List Instr :=
  [.lbz .r0 .r3 0, .logic .and .r0 .r0 .r6, .stb .r0 .r4 0, .li .r6 255, .addi .r3 .r3 1, .addi .r4 .r4 1]

/-- The draw into the nonce, and the octets consumed. -/
def copy : Prog isa :=
  .seq (.block copyInit) (.seq (Precompute.countLoop .r5 copyByte) (.block [.add .r25 .r25 .r28]))

/-- The comparison from the ends: the nonce (`r3`) and q (`r4`), `r28`
octets; `r6` the borrow, `r7` the or of the nonce's octets. -/
def rangeInit : List Instr :=
  [.addSp .r3 oNonce, .add .r3 .r3 .r21, .add .r4 .r27 .r28, .addi .r5 .r28 0, .li .r6 0, .li .r7 0]

/-- An octet of the comparison, from the least significant. -/
def rangeByte : List Instr :=
  [.subi .r3 .r3 1, .subi .r4 .r4 1, .lbz .r0 .r3 0, .logic .or .r7 .r7 .r0, .lbz .r8 .r4 0,
    .add .r8 .r8 .r6, .sub .r0 .r0 .r8, .lsr .d .r6 .r0 63]

/-- `r6 := 1` exactly when the candidate is below q and not zero. -/
def rangeFinish : List Instr :=
  [.li .r0 0, .sub .r0 .r0 .r7, .lsr .d .r0 .r0 63, .logic .and .r6 .r6 .r0]

/-- Whether the candidate is accepted, into `r6`. -/
def inRange : Prog isa :=
  .seq (.block rangeInit) (.seq (Precompute.countLoop .r5 rangeByte) (.block rangeFinish))

/-- Accepted: status 1; otherwise a draw of the budget (`r17`) is spent,
and the status is 0 once none is left. -/
def drawFinish : Prog isa :=
  .ite (.nonzero .d .r6) (.block [.li .r31 1])
    (.seq (.block [.subi .r17 .r17 1]) (.ite (.zero .d .r17) (.block [.li .r31 0]) (.block [])))

/-- One draw: a short tape (status 2), or a candidate. -/
def draw : Prog isa :=
  .seq (.block shortTest) (.ite (.nonzero .d .r3) (.block [.li .r31 2]) (.seq (.seq copy inRange) drawFinish))

/-- Up to 128 draws, while the status is 4. -/
def sample : Prog isa :=
  .seq (.block [.li .r17 128, .li .r31 4]) (.loop (.seq draw (.block [.subi .r3 .r31 4])) (.zero .d .r3))

/-! ## The exit -/

/-- `out`'s `r5` octets := 0 (`r5 > 0`). -/
def zeroOut (len : List Instr) : Prog isa :=
  .seq (.block ([.addi .r4 .r18 0] ++ len ++ [.li .r0 0]))
    (Precompute.countLoop .r5 [.stb .r0 .r4 0, .addi .r4 .r4 1])

/-- Unless the status is 1, `out` (`len` computes its length into `r5`)
is zeroed; then the nonce, the octets consumed to `used`, the status, and
the registers. -/
def finish (len : List Instr) : Prog isa :=
  .seq (.block [.subi .r3 .r31 1]) (.seq (.ite (.zero .d .r3) (.block []) (zeroOut len))
    (.block (clearNonce ++ [.store .d .r25 .r30 0, .addi .r3 .r31 0] ++ restoreRegs)))

end VG.Impl.Dsa.PPC64LE.Random
