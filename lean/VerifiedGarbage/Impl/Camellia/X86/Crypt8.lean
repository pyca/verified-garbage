module

public import VerifiedGarbage.Impl.Camellia.X86.Layers

/-!
# Eight blocks of bitsliced Camellia on x86 (32-bit)

`crypt8 g`: the eight blocks of the tail buffer (`Layers.lean` has the
scratch buffer's layout), bitsliced and whitened, run through `g` groups of
six rounds with FL and FLINV between them, whitened again and stored back
with their halves swapped, under the table of bitsliced subkeys at slot
104, in the order the rounds use them. `vg_camellia_crypt_prepared`
(`Prepared.lean`), which ECB (`Ecb.lean`) and the modes call, runs it.
-/

@[expose] public section

namespace VG.Impl.Camellia.X86

open VG.X86 VG.Impl.Aes.X86

inductive Dir | encrypt | decrypt
  deriving DecidableEq, Repr

/-- `kp := ` the address of slot `k`. -/
def kpAt (k : Nat) : List Instr := [movR kp .edi, addI kp (BitVec.ofNat 32 (4 * k))]

/-! ## Eight blocks, in the tail buffer -/

/-- Word `w` of the eight blocks (in the tail buffer) to its planes. -/
def toBsWord (w : Nat) : List Instr :=
  (List.range 8).flatMap (fun b => [movS .eax (tailAt b w), st b .eax]) ++ ortho ++
  (List.range 8).flatMap (fun j => [movS .eax j, st (stateSlot w j) .eax])

/-- XOR the 32 words at `kp` into the state's planes: those of `D1` then
`D2`, or (`swap`) of `D2` then `D1`. -/
def whiten (swap : Bool) : List Instr :=
  (List.range 32).flatMap fun i =>
    let k := d1Slot + (if swap then (i + 16) % 32 else i)
    [movS .eax k, .alu .xor .eax (.mem (slotAt kp i)), st k .eax]

/-- Bitslice both halves and whiten them (`kw1` for `D1`, `kw2` for `D2`);
`kp` is left at the first round's entry. -/
def head : List Instr :=
  (List.range 4).flatMap toBsWord ++ kpAt keySlot ++ whiten false ++ [addI kp 128]

/-- Two rounds: `D2 ^= F(D1, k)`, `D1 ^= F(D2, k')`; Z when `kp` reaches the
group's end (loaded from its slot: the analysis of constant time takes a
comparison with a memory operand as secret). -/
def pairBody : List Instr :=
  round 0 d1Slot d2Slot ++ round 16 d2Slot d1Slot ++
  [addI kp 128, movS .eax grpSlot, .alu .cmp .eax (.reg kp)]

/-- Z when `kp` is at the postwhitening's entry, `8 g` entries into the table. -/
def atEnd (g : Nat) : List Instr :=
  [movR .eax kp, subR .eax .edi, .alu .cmp .eax (.imm (BitVec.ofNat 32 (4 * keySlot + 512 * g)))]

/-- Six rounds, then FL and FLINV unless they were the last; Z when `kp` is
at the postwhitening's entry. -/
def groupBody (g : Nat) : Prog isa :=
  .seq (.block [movR .eax kp, addI .eax 384, st grpSlot .eax])
    (.seq (.loop (.block pairBody) .ne)
      (.seq (.block (atEnd g)) (.seq (.ite .ne (.block flLayer) (.block [])) (.block (atEnd g)))))

/-- Output word `w` of the eight blocks (to the tail buffer), from the
planes of `D2` (words 0 and 1) or `D1` (words 2 and 3). -/
def fromBsWord (w : Nat) : List Instr :=
  (List.range 8).flatMap (fun j => [movS .eax (stateSlot ((w + 2) % 4) j), st j .eax]) ++ ortho ++
  (List.range 8).flatMap (fun b => [movS .eax b, st (tailAt b w) .eax])

/-- The postwhitening (`kw3` for `D2`, `kw4` for `D1`), and the halves back
to the blocks, swapped. -/
def tail : List Instr := whiten true ++ (List.range 4).flatMap fromBsWord

/-- The eight blocks of the tail buffer, in place, for `g` groups. -/
def crypt8 (g : Nat) : Prog isa := .seq (.block head) (.seq (.loop (groupBody g) .ne) (.block tail))

end VG.Impl.Camellia.X86
