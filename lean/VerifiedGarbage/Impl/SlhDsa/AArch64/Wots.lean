module

public import VerifiedGarbage.Impl.SlhDsa.AArch64.Layout

/-!
# SLH-DSA (SHAKE) on AArch64: four WOTS⁺ public keys at once

`wotsLeaves4(scratch = x0, kp = x1, idx = x2, sig = x3)`, as on x86-64
(`Impl/SlhDsa/X86_64/Wots.lean`): it computes the WOTS⁺ public keys
(`wots_pkGen`, Algorithm 6) of the key pairs `kp` to `kp + 3` of an XMSS
tree, to the nodes `kp` to `kp + 3` at `oN`, one lane of `thash4` each. The
caller has put `PK.seed` and the tree's layer and tree addresses in the
lanes `A` and `B`, and `SK.seed` at `oSkSeed`. For the key pair `idx`, if it
is one of them, it also writes its WOTS⁺ signature (`wots_sign`, Algorithm
7) of the message whose `len` base-16 digits are the bytes at `oDigits` to
the `len·n` bytes at `sig`: chain `i` after `digits[i]` steps,
`chain(sk, 0, digits[i])`, is a value the computation of the public key
passes through (`chain_add`). It selects it with masks, never a branch or an
address that depends on `idx` or the digits, so that neither can affect
timing.

For each chain `i`, each lane's address gets the type `WOTS_PRF` and the
chain address `i`, and its message `SK.seed`: `thash4` computes the private
key values `PRF(PK.seed, SK.seed, skADRS)`, over the messages; then the type
`WOTS_HASH` and the hash addresses `0` to `14` in turn, each step one `F`.
Before each step `j`, and after the last (`j = 15`), each lane's value is
XORed into chain `i` of the signature under the mask of whether its key pair
is `idx` and `j` is the digit (`capture`). The value at the end of the chain
goes to the lane's `B` message at `i·n`; after the last chain, `T_len` of
those (the type `WOTS_PK`) are the public keys.

Registers: `x19` = `scratch`, `x20` = `kp`, `x21` = `i`, `x22` = `j`,
`x23` = `idx`, `x24` = `sig`: callee-saved registers, which `thash4` keeps;
the caller's values of them and its return address `x30` are saved in
frame 0. A loop's condition is `x9`, set at the end of its body.
-/

@[expose] public section

namespace VG.Impl.SlhDsa.AArch64.Wots

open VG.AArch64
open VG.Impl.SlhDsa.AArch64.Thash4 (mov)

variable (L : Layout) (t4name : String) (t4 : Prog isa)

/-- The registers saved in frame 0. -/
def saved : List Reg := [.x19, .x20, .x21, .x22, .x23, .x24, .x30]

/-- Save the registers and keep the arguments. -/
def pro : List Instr :=
  saveRegs 0 .x0 saved ++ [mov .x19 .x0, mov .x20 .x1, mov .x23 .x2, mov .x24 .x3]

/-- The key pair addresses `kp + k` in lanes `A` and `B`, and lane `B`'s
type `WOTS_PK` and zero chain and hash addresses; `i ← 0`. -/
def setup : List Instr :=
  (List.range 4).flatMap (fun k =>
    [.addImm .x .x10 .x20 k] ++
      setFieldR .x19 (Layout.laneA k + L.adrsOff + 20) .x10 ++ setFieldR .x19 (Layout.laneB k + L.adrsOff + 20) .x10 ++
      setField .x19 (Layout.laneB k + L.adrsOff + 16) 1 ++ setField .x19 (Layout.laneB k + L.adrsOff + 24) 0 ++
      setField .x19 (Layout.laneB k + L.adrsOff + 28) 0) ++
  [.movz .x .x21 0 0]

/-- Lane `k`'s address for `PRF`: the type `WOTS_PRF`, chain address `i`,
hash address 0; and its message `SK.seed`. -/
def prfLane (k : Nat) : List Instr :=
  setField .x19 (Layout.laneA k + L.adrsOff + 16) 5 ++ setFieldR .x19 (Layout.laneA k + L.adrsOff + 24) .x21 ++
    setField .x19 (Layout.laneA k + L.adrsOff + 28) 0 ++
    copyWords .x19 (Layout.laneA k + L.msgOff) .x19 Layout.oSkSeed (L.n / 8)

def prfLanes : List Instr := (List.range 4).flatMap (prfLane L)

/-- Each lane's address gets the type `WOTS_HASH`; `j ← 0`. -/
def hashType : List Instr :=
  (List.range 4).flatMap (fun k => setField .x19 (Layout.laneA k + L.adrsOff + 16) 0) ++ [.movz .x .x22 0 0]

/-- Lane `k`'s value XORed into chain `i` of the signature (at `x11`) under
the mask, all ones if `kp + k = idx` and `j` is digit `i` (`x10` holds
`j ⊕ digits[i]`), and zero otherwise: `x = ((kp + k) ⊕ idx) ∨ x10` is zero
exactly then, and below `2⁶³`, so `-((x - 1) ≫ 63)` is the mask (in `x12`). -/
def captureLane (k : Nat) : List Instr :=
  [.addImm .x .x12 .x20 k, .logic .eor .x .x12 .x12 .x23, .logic .orr .x .x12 .x12 .x10] ++ maskZero .x12 .x13 ++
  (List.range (L.n / 8)).flatMap fun w =>
    [.ldr .x .x13 .x11 (8 * w), .ldr .x .x14 .x19 (Layout.laneA k + L.msgOff + 8 * w),
      .logic .eor .x .x14 .x14 .x13, .logic .and .x .x14 .x14 .x12, .logic .eor .x .x13 .x13 .x14,
      .str .x .x13 .x11 (8 * w)]

/-- The capture at step `j` of chain `i`: `x10 ← j ⊕ digits[i]`,
`x11 ← sig + i·n`, and the four lanes. -/
def capture : List Instr :=
  [.add .x .x9 .x19 .x21, .ldrb .x9 .x9 Layout.oDigits, .logic .eor .x .x10 .x22 .x9, mov .x11 .x21] ++
    mulN L.n .x11 .x12 ++ [.add .x .x11 .x11 .x24] ++ (List.range 4).flatMap (captureLane L)

/-- Each lane's hash address `j`. -/
def hashAdrs : List Instr := (List.range 4).flatMap fun k => setFieldR .x19 (Layout.laneA k + L.adrsOff + 28) .x22

/-- A step of the chains: the capture, the hash address `j`, one `F`, and
`j + 1`, with `x9 = 0` after the 15th. -/
def stepBody : Prog isa :=
  .seq (.block (capture L ++ hashAdrs L))
    (.seq (thashCall L t4name t4 Layout.oA Layout.strideA (2 * L.n + 32))
      (.block [.addImm .x .x22 .x22 1, .subImm .x .x9 .x22 15]))

/-- The end of chain `i` of each lane to its `B` message at `i·n`. -/
def toB : List Instr :=
  [mov .x10 .x21] ++ mulN L.n .x10 .x11 ++ [.add .x .x10 .x10 .x19] ++
    (List.range 4).flatMap fun k => copyWords .x10 (Layout.laneB k + L.msgOff) .x19 (Layout.laneA k + L.msgOff) (L.n / 8)

/-- Chain `i` of the four lanes: the private key values, then the 15 steps
and the last capture, and `i + 1`, with `x9 = 0` after the last chain. -/
def chainBody : Prog isa :=
  .seq (.block (prfLanes L))
    (.seq (thashCall L t4name t4 Layout.oA Layout.strideA (2 * L.n + 32))
      (.seq (.block (hashType L))
        (.seq (.loop (stepBody L t4name t4) (.nonzero .x .x9))
          (.block (capture L ++ toB L ++ [.addImm .x .x21 .x21 1, .subImm .x .x9 .x21 L.len])))))

/-- `x10 ← scratch + kp·n`, the node of key pair `kp` less `oN`. -/
def leafPtr : List Instr := [mov .x10 .x20] ++ mulN L.n .x10 .x11 ++ [.add .x .x10 .x10 .x19]

/-- The public keys, `T_len` of the lanes `B`, to the nodes. -/
def leaves : Prog isa :=
  .seq (thashCall L t4name t4 Layout.oB Layout.strideB (L.n + 32 + L.len * L.n))
    (.block (leafPtr L ++ (List.range 4).flatMap fun k =>
      copyWords .x10 (Layout.oN + L.n * k) .x19 (Layout.laneB k + L.msgOff) (L.n / 8)))

/-- `wotsLeaves4`, calling the `thash4` named `t4name`, whose code is `t4`. -/
def wotsLeaves4 : Prog isa :=
  .seq (.block (pro ++ setup L))
    (.seq (.loop (chainBody L t4name t4) (.nonzero .x .x9))
      (.seq (leaves L t4name t4) (.block (restoreRegs 0 saved))))

end VG.Impl.SlhDsa.AArch64.Wots
