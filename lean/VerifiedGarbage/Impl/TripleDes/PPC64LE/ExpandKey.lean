module

public import VerifiedGarbage.Impl.TripleDes.PPC64LE.Common
public import VerifiedGarbage.Spec.TripleDes

/-!
# Triple DES key expansion on PPC64LE

`expandKey` (key = r3, key_len = r4, schedule = r5) expands each 8-byte
component key in turn: PC-1 splits it into C (`r0`) and D (`r7`), each round
rotates them and stores PC-2 of them in the round's slot (at `r6`), and
`r12` counts the rounds. Only volatile registers are used, so the function
needs no working space. The round count and the key length are public.
-/

@[expose] public section

namespace VG.Impl.TripleDes.PPC64LE.Key

open VG.PPC64LE VG.Impl.TripleDes.PPC64LE

def load (offset component : Nat) : List Instr :=
  ([.li .r8 offset, .loadRev .d .r8 .r3 .r8] : List Instr) ++
    permuteCode Spec.TripleDes.pc1 64 .r9 .r8 .r10 .r11 ++
    ([.lsr .d .r0 .r9 28, rr .r7 .r9] : List Instr) ++ mask .r7 28 ++
    [imm .r12 0, .addi .r6 .r5 (128 * component)]

def rotate28 (r : Reg) (n : Nat) : List Instr :=
  ([.lsr .d .r8 r (28 - n), .rotr .d r r (64 - n), .logic .xor r r .r8] : List Instr) ++ mask r 28

def rotate (n : Nat) : Prog isa := .block (rotate28 .r0 n ++ rotate28 .r7 n)

def rotation : Prog isa :=
  .seq (.block [.lsr .d .r8 .r12 1])
    (.ite (.zero .d .r8) (rotate 1)
      (.seq (.block [.subi .r8 .r12 8])
        (.ite (.zero .d .r8) (rotate 1)
          (.seq (.block [.subi .r8 .r12 15])
            (.ite (.zero .d .r8) (rotate 1) (rotate 2))))))

def storeRound : List Instr :=
  ([.lsl .r8 .r0 28, .logic .xor .r8 .r8 .r7] : List Instr) ++
    permuteCode Spec.TripleDes.pc2 56 .r9 .r8 .r10 .r11 ++
    ([.store .d .r9 .r6 0, .addi .r6 .r6 8, .addi .r12 .r12 1, .subi .r8 .r12 16] : List Instr)

def component (offset index : Nat) : Prog isa :=
  .seq (.block (load offset index)) (.loop (.seq rotation (.block storeRound)) (.nonzero .d .r8))

def copyThird : List Instr :=
  (List.range 16).flatMap fun j => [.load .d .r8 .r5 (8 * j), .store .d .r8 .r5 (256 + 8 * j)]

def expandKey : Prog isa :=
  .seq (component 0 0)
    (.seq (component 8 1)
      (.seq (.block [.subi .r8 .r4 16])
        (.ite (.zero .d .r8) (.block copyThird) (component 16 2))))

end VG.Impl.TripleDes.PPC64LE.Key
