module

public import VerifiedGarbage.Impl.SlhDsa.X86_64.Layout

/-!
# SLH-DSA (SHAKE) on x86-64: four WOTS⁺ public keys at once

`wotsLeaves4(scratch = rdi, kp = rsi, idx = rdx, sig = rcx)` computes the
WOTS⁺ public keys (`wots_pkGen`, Algorithm 6) of the key pairs `kp` to
`kp + 3` of an XMSS tree, to the nodes `kp` to `kp + 3` at `oN`, one lane of
`thash4` each. The caller has put `PK.seed` and the tree's layer and tree
addresses in the lanes `A` and `B`, and `SK.seed` at `oSkSeed`. For the key
pair `idx`, if it is one of them, it also writes its WOTS⁺ signature
(`wots_sign`, Algorithm 7) of the message whose `len` base-16 digits are the
bytes at `oDigits` to the `len·n` bytes at `sig`: chain `i` after `digits[i]`
steps, `chain(sk, 0, digits[i])`, is a value the computation of the public
key passes through (`chain_add`). It selects it with masks, never a branch
or an address that depends on `idx` or the digits, so that neither can
affect timing.

For each chain `i`, each lane's address gets the type `WOTS_PRF` and the
chain address `i`, and its message `SK.seed`: `thash4` computes the private
key values `PRF(PK.seed, SK.seed, skADRS)`, over the messages; then the type
`WOTS_HASH` and the hash addresses `0` to `14` in turn, each step one `F`.
Before each step `j`, and after the last (`j = 15`), each lane's value is
XORed into chain `i` of the signature under the mask of whether its key pair
is `idx` and `j` is the digit (`capture`). The value at the end of the chain
goes to the lane's `B` message at `i·n`; after the last chain, `T_len` of
those (the type `WOTS_PK`) are the public keys.

Registers: `rbx` = `scratch`, `r12` = `kp`, `r13` = `i`, `rbp` = `j`,
`r14` = `idx`, `r15` = `sig`: the loop counters are in callee-saved
registers, which `thash4` keeps, and nothing is kept in memory but the
caller's registers.
-/

@[expose] public section

namespace VG.Impl.SlhDsa.X86_64.Wots

open VG.X86_64
open VG.Impl.Sha3.X86_64 (at_)

variable (L : Layout) (t4name : String) (t4 : Prog isa)

/-- `r ← r·n` (`n` 16, 24 or 32), through `tmp`. -/
def mulN (n : Nat) (r tmp : Reg) : List Instr :=
  if n = 24 then [.mov tmp (.reg r), .shift .shl r 4, .shift .shl tmp 3, .alu .add r (.reg tmp)]
  else [.shift .shl r (if n = 16 then 4 else 5)]

/-- Save the registers and keep the arguments. -/
def pro : List Instr :=
  saveRegs 0 .rdi ++ [.mov .rbx (.reg .rdi), .mov .r12 (.reg .rsi), .mov .r14 (.reg .rdx), .mov .r15 (.reg .rcx)]

/-- The key pair addresses `kp + k` in lanes `A` and `B`, and lane `B`'s
type `WOTS_PK` and zero chain and hash addresses; `i ← 0`. -/
def setup : List Instr :=
  (List.range 4).flatMap (fun k =>
    [.mov .r10 (.reg .r12), .alu .add .r10 (.imm (BitVec.ofNat 32 k))] ++
      setFieldR .rbx (Layout.laneA k + L.adrsOff + 20) .r10 ++ setFieldR .rbx (Layout.laneB k + L.adrsOff + 20) .r10 ++
      setField .rbx (Layout.laneB k + L.adrsOff + 16) 1 ++ setField .rbx (Layout.laneB k + L.adrsOff + 24) 0 ++
      setField .rbx (Layout.laneB k + L.adrsOff + 28) 0) ++
  [.mov32 .r13 (.imm 0)]

/-- Lane `k`'s address for `PRF`: the type `WOTS_PRF`, chain address `i`,
hash address 0; and its message `SK.seed`. -/
def prfLane (k : Nat) : List Instr :=
  setField .rbx (Layout.laneA k + L.adrsOff + 16) 5 ++ setFieldR .rbx (Layout.laneA k + L.adrsOff + 24) .r13 ++
    setField .rbx (Layout.laneA k + L.adrsOff + 28) 0 ++ copyWords .rbx (Layout.laneA k + L.msgOff) .rbx Layout.oSkSeed (L.n / 8)

def prfLanes : List Instr := (List.range 4).flatMap (prfLane L)

/-- Each lane's address gets the type `WOTS_HASH`; `j ← 0`. -/
def hashType : List Instr :=
  (List.range 4).flatMap (fun k => setField .rbx (Layout.laneA k + L.adrsOff + 16) 0) ++ [.mov32 .rbp (.imm 0)]

/-- Lane `k`'s value XORed into chain `i` of the signature (at `rsi`) under
the mask, all ones if `kp + k = idx` and `j` is digit `i` (`rdx` holds
`j ⊕ digits[i]`), and zero otherwise: `x = ((kp + k) ⊕ idx) ∨ rdx` is zero
exactly then, and below `2⁶³`, so `-((x - 1) ≫ 63)` is the mask (in `rdi`). -/
def captureLane (k : Nat) : List Instr :=
  [.mov .rax (.reg .r12), .alu .add .rax (.imm (BitVec.ofNat 32 k)), .alu .xor .rax (.reg .r14),
    .alu .or .rax (.reg .rdx), .alu .sub .rax (.imm 1), .shift .shr .rax 63, .mov32 .rdi (.imm 0),
    .alu .sub .rdi (.reg .rax)] ++
  (List.range (L.n / 8)).flatMap fun w =>
    [.mov .rax (.mem (at_ .rsi (8 * w))), .mov .rcx (.mem (at_ .rbx (Layout.laneA k + L.msgOff + 8 * w))),
      .alu .xor .rcx (.reg .rax), .alu .and .rcx (.reg .rdi), .alu .xor .rax (.reg .rcx),
      .store (at_ .rsi (8 * w)) .rax]

/-- `[rbx + r13 + oDigits]`: digit `i`. -/
def digitOp : MemOp := { base := .rbx, index := some .r13, scale := 1, disp := (Layout.oDigits : Int) }

/-- The capture at step `j` of chain `i`: `rdx ← j ⊕ digits[i]`,
`rsi ← sig + i·n`, and the four lanes. -/
def capture : List Instr :=
  [.movzx8 .rcx digitOp, .mov .rdx (.reg .rbp), .alu .xor .rdx (.reg .rcx), .mov .rsi (.reg .r13)] ++
    mulN L.n .rsi .rax ++ [.alu .add .rsi (.reg .r15)] ++ (List.range 4).flatMap (captureLane L)

/-- Each lane's hash address `j`. -/
def hashAdrs : List Instr := (List.range 4).flatMap fun k => setFieldR .rbx (Layout.laneA k + L.adrsOff + 28) .rbp

/-- A step of the chains: the capture, the hash address `j`, one `F`, and
`j + 1`, setting ZF after the 15th. -/
def stepBody : Prog isa :=
  .seq (.block (capture L ++ hashAdrs L))
    (.seq (thashCall L t4name t4 Layout.oA Layout.strideA (2 * L.n + 32))
      (.block [.alu .add .rbp (.imm 1), .alu .cmp .rbp (.imm 15)]))

/-- The end of chain `i` of each lane to its `B` message at `i·n`. -/
def toB : List Instr :=
  [.mov .rdx (.reg .r13)] ++ mulN L.n .rdx .rax ++ [.alu .add .rdx (.reg .rbx)] ++
    (List.range 4).flatMap fun k => copyWords .rdx (Layout.laneB k + L.msgOff) .rbx (Layout.laneA k + L.msgOff) (L.n / 8)

/-- Chain `i` of the four lanes: the private key values, then the 15 steps
and the last capture, and `i + 1`, setting ZF after the last chain. -/
def chainBody : Prog isa :=
  .seq (.block (prfLanes L))
    (.seq (thashCall L t4name t4 Layout.oA Layout.strideA (2 * L.n + 32))
      (.seq (.block (hashType L))
        (.seq (.loop (stepBody L t4name t4) .ne)
          (.block (capture L ++ toB L ++
            [.alu .add .r13 (.imm 1), .alu .cmp .r13 (.imm (BitVec.ofNat 32 L.len))])))))

/-- `rdx ← scratch + oN + kp·n`, the node of key pair `kp`. -/
def leafPtr : List Instr :=
  [.mov .rdx (.reg .r12)] ++ mulN L.n .rdx .rax ++
    [.alu .add .rdx (.reg .rbx), .alu .add .rdx (.imm (BitVec.ofNat 32 Layout.oN))]

/-- The public keys, `T_len` of the lanes `B`, to the nodes. -/
def leaves : Prog isa :=
  .seq (thashCall L t4name t4 Layout.oB Layout.strideB (L.n + 32 + L.len * L.n))
    (.block (leafPtr L ++ (List.range 4).flatMap fun k => copyWords .rdx (L.n * k) .rbx (Layout.laneB k + L.msgOff) (L.n / 8)))

/-- `wotsLeaves4`, calling the `thash4` named `t4name`, whose code is `t4`. -/
def wotsLeaves4 : Prog isa :=
  .seq (.block (pro ++ setup L))
    (.seq (.loop (chainBody L t4name t4) .ne)
      (.seq (leaves L t4name t4) (.block (restoreRegs 0))))

end VG.Impl.SlhDsa.X86_64.Wots
