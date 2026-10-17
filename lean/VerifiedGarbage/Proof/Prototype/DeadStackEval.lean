import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Impl.Idea.X86_64
import VerifiedGarbage.Impl.Blowfish.X86_64
import VerifiedGarbage.Impl.StackScratch.X86_64

/-! Local experiment: does the x86-64 taint analysis, run on a stack-scratch
frame's body with the frame as writable region 0 and the old dead stack
public (the `Ctx` assumption), end with every byte of the frame in a public
slot? -/

namespace VG.Proto
open VG X86_64 X86_64.Taint Impl.StackScratch.X86_64

/-- Every byte of `[0, n)` of region `i` is in a public slot. -/
def covers (τ : T) (i n : Nat) : Bool :=
  (List.range n).all fun k => τ.slots.any fun sl => sl.1 == i && sl.2.1 ≤ k && k < sl.2.1 + sl.2.2

/-- The taint after the push of an `alloc bytes` frame, for a function whose
writable buffers have unknown lengths (`nwr` of them), with `pubs` public:
region 0 is the frame, `rsp` its base, its old bytes public a word at a time. -/
def τframe (pubs : List Reg) (nwr bytes : Nat) : T :=
  { regs := RegSet.ofList (.rsp :: pubs), flags := false,
    lens := bytes :: List.replicate nwr 0,
    bases := [(.rsp, 0, 0)],
    slots := (List.range (bytes / 8)).map fun k => (0, 8 * k, 8) }

def calleeSaved' : List Reg := [.rbx, .rbp, .r12, .r13, .r14, .r15]

/-- The frame body of `withStackScratch`/`Wiped`. -/
def body (bytes : Nat) (r : Reg) (c : Prog isa) (words : Nat) : Prog isa :=
  .seq (.block [.mov r (.reg .rsp), .alu .add r (.imm 8)]) (.seq c (.block (wipe words)))

def run (pubs : List Reg) (nwr bytes : Nat) (r : Reg) (c : Prog isa) (words : Nat) : String :=
  let τ := τframe (pubs ++ calleeSaved') nwr bytes
  let b := body bytes r c words
  match (taint.check τ b (Taint.hintOf taint τ b)) with
  | none => "analysis fails"
  | some τ' => s!"frame covered: {covers τ' 0 bytes}; slots {τ'.slots.length}"

-- IDEA ECB: unwiped today, spills only rbx/rbp.
#eval run [.rdi, .rsi, .rdx] 1 24 .rcx Impl.Idea.X86_64.ecb 0
-- Blowfish ECB, as registered (2 words wiped), and without the wipe.
#eval run [.rdi, .rsi, .rdx] 1 264 .rcx Impl.Blowfish.X86_64.encrypt 2
#eval run [.rdi, .rsi, .rdx] 1 264 .rcx Impl.Blowfish.X86_64.encrypt 0

end VG.Proto
