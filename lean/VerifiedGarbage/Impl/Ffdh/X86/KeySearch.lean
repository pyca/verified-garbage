module

public import VerifiedGarbage.Impl.Ffdh.X86.KeyGen
public import VerifiedGarbage.Spec.Ffdh.Contract

/-!
# FFDH on i686: the key-generation controller

`vg_ffdh_generate_key_search` repeats an attempt of `vg_ffdh_generate_key`
on successive `p_len` octets of the random tape until it gives a key, a
budget runs out, or the tape does: range and degenerate-public-value
rejections never return to the host.

The first four state words are the budgets, the width and the next request
(their low halves; the high halves stay zero). The controller keeps its own
words in the rest, at `esi`: the caller's `esi`, the arguments it passes on,
the tape's current pointer and length, the octets consumed, the status and
`used`.
-/

@[expose] public section
namespace VG.Impl.Ffdh.X86.KeySearch
open VG VG.X86 VG.Impl.Mont.X86
open VG.Impl.Bignum.X86.PublicRt (argAt)

/-- The state's words, by their byte offsets. -/
def keysOff : Nat := 0
def scalarsOff : Nat := 8
def lenOff : Nat := 16
def requestOff : Nat := 24
def savedOff : Nat := 32
def xOff : Nat := 36
def yOff : Nat := 40
def domOff : Nat := 44
def dlenOff : Nat := 48
def randOff : Nat := 52
def leftOff : Nat := 56
def usedOff : Nat := 60
def scratchOff : Nat := 64
def slenOff : Nat := 68
def statusOff : Nat := 72
def upOff : Nat := 76

/-- A word of the state, at `esi`. -/
def st (d : Nat) : MemOp := at_ .esi d

/-- Argument `i` (`x, x_len, y, y_len, used, domain, domain_len, p_len, rand,
rand_len, scratch, scratch_len, state`) to the state's word at `d`. -/
def keep (i d : Nat) : List Instr := [.mov .eax (.mem (argAt 0 i)), .store (st d) .eax]

/-- `esi` the state, the caller's `esi` saved in it; the arguments kept;
nothing consumed; the request's high half zero. -/
def entry : List Instr :=
  [.mov .eax (.mem (argAt 0 12)), .store (at_ .eax savedOff) .esi, .mov .esi (.reg .eax)] ++
  keep 0 xOff ++ keep 2 yOff ++ keep 4 upOff ++ keep 5 domOff ++ keep 6 dlenOff ++ keep 7 lenOff ++
  keep 8 randOff ++ keep 9 leftOff ++ keep 10 scratchOff ++ keep 11 slenOff ++
  [.mov .eax (.imm 0), .store (st usedOff) .eax, .store (st (requestOff + 4)) .eax]

/-- `p_len` zeros at the pointer in the state's word at `d`. -/
def zeroOut (d : Nat) : Prog isa :=
  .seq (.block [.mov .edx (.mem (st d)), .mov .ecx (.mem (st lenOff)), .mov .eax (.imm 0)])
    (.loop (.block [.store8 (at_ .edx 0) .al, .alu .add .edx (.imm 1), .alu .sub .ecx (.imm 1)]) .ne)

/-- Zeros at `x` and `y`. -/
def zeroOutputs : Prog isa := .seq (zeroOut xOff) (zeroOut yOff)

/-- The budgets and the request zero, and `status`. -/
def terminal (status : Nat) : List Instr :=
  [.mov .eax (.imm 0), .store (st keysOff) .eax, .store (st scalarsOff) .eax, .store (st requestOff) .eax,
    .mov .eax (.imm (BitVec.ofNat 32 status)), .store (st statusOff) .eax]

def exhausted : Prog isa := .seq (.block (terminal 3)) zeroOutputs

/-- Ask for `p_len` octets: the tape holds less than an attempt. -/
def request : Prog isa :=
  .seq (.block [.mov .eax (.mem (st lenOff)), .store (st requestOff) .eax, .mov .eax (.imm 0),
    .store (st statusOff) .eax]) zeroOutputs

/-- The state's word at `d` to the callee's argument `j`. -/
def pass (d j : Nat) : List Instr := [.mov .eax (.mem (st d)), .store (at_ .esp (4 * j)) .eax]

/-- `vg_ffdh_generate_key`'s arguments `(x, p_len, y, p_len, domain, domain_len, p_len, rand,
p_len, scratch, scratch_len)`, for `p_len` octets at the tape's pointer. -/
def arguments : List Instr :=
  pass xOff 0 ++ pass lenOff 1 ++ pass yOff 2 ++ pass lenOff 3 ++ pass domOff 4 ++ pass dlenOff 5 ++
  pass lenOff 6 ++ pass randOff 7 ++ pass lenOff 8 ++ pass scratchOff 9 ++ pass slenOff 10

/-- The bytes of the attempt's frame of arguments. -/
def argsBytes : Nat := 44

/-- The attempt, a call of `vg_ffdh_generate_key`, in a frame of its arguments. -/
def attempt : Prog isa :=
  .frame (.alloc argsBytes) (.seq (.block arguments) (.call Spec.Ffdh.generateKeyApi.name GenerateKey.code))
    (.free argsBytes)

/-- The status to `edx`, and the attempt's `p_len` octets consumed. -/
def advance : List Instr :=
  [.mov .edx (.reg .eax), .mov .ecx (.mem (st lenOff)),
    .mov .eax (.mem (st randOff)), .alu .add .eax (.reg .ecx), .store (st randOff) .eax,
    .mov .eax (.mem (st leftOff)), .alu .sub .eax (.reg .ecx), .store (st leftOff) .eax,
    .mov .eax (.mem (st usedOff)), .alu .add .eax (.reg .ecx), .store (st usedOff) .eax]

/-- A scalar out of range: one fewer scalar left. -/
def rejectedScalar : List Instr :=
  [.mov .eax (.mem (st scalarsOff)), .alu .sub .eax (.imm 1), .store (st scalarsOff) .eax,
    .mov .eax (.imm 4), .store (st statusOff) .eax]

/-- A degenerate public value: one fewer key left, and the scalar budget again. -/
def rejectedPublic : List Instr :=
  [.mov .eax (.mem (st keysOff)), .alu .sub .eax (.imm 1), .store (st keysOff) .eax,
    .mov .eax (.imm 128), .store (st scalarsOff) .eax, .mov .eax (.imm 4), .store (st statusOff) .eax]

def classify : Prog isa := .seq (.block (advance ++ [.alu .cmp .edx (.imm 1)]))
  (.ite .e (.block (terminal 1))
    (.seq (.block [.alu .cmp .edx (.imm 2)])
      (.ite .e (.block rejectedScalar)
        (.seq (.block [.alu .cmp .edx (.imm 3)]) (.ite .e (.block rejectedPublic) exhausted)))))

/-- The borrow set when the tape holds less than an attempt. -/
def room : List Instr :=
  [.mov .eax (.mem (st leftOff)), .mov .ecx (.mem (st lenOff)), .alu .cmp .eax (.reg .ecx)]

def attemptOrRequest : Prog isa := .seq (.block room) (.ite .b request (.seq attempt classify))

def branch : Prog isa :=
  .seq (.block [.mov .eax (.mem (st keysOff)), .alu .test .eax (.reg .eax)])
    (.ite .e exhausted (.seq (.block [.mov .eax (.mem (st scalarsOff)), .alu .test .eax (.reg .eax)])
      (.ite .e exhausted attemptOrRequest)))

/-- The loop goes on while the status is 4, a rejection. -/
def iteration : Prog isa :=
  .seq branch (.block [.mov .eax (.mem (st statusOff)), .alu .cmp .eax (.imm 4)])

/-- `used` written (64 bits), the status returned and the caller's `esi` restored. -/
def finish : List Instr :=
  [.mov .ecx (.mem (st upOff)), .mov .eax (.mem (st usedOff)), .store (at_ .ecx 0) .eax,
    .mov .eax (.imm 0), .store (at_ .ecx 4) .eax, .mov .eax (.mem (st statusOff)),
    .mov .esi (.mem (st savedOff))]

def code : Prog isa := .seq (.block entry) (.seq (.loop iteration .e) (.block finish))

end VG.Impl.Ffdh.X86.KeySearch
