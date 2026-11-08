module

public import VerifiedGarbage.TCB.X86_64.Isa
public import VerifiedGarbage.TCB.Code

/-!
# The prepared key context's flag, on x86-64

A prepared key context of 1088 bytes holds, at byte 1024, a word that is 1
when its powers are absent. `onFlag c₁ c₂` reads it and runs `c₁` if it is
not 1 (the powers are there) and `c₂` if it is (the code that reads only the
key context).
-/

@[expose] public section

namespace VG.Impl.Gcm.X86_64.Flag

open VG.X86_64

/-- The flag word's offset in the prepared key context. -/
def flagOff : Nat := 1024

/-- `mov rax, [rdi + 1024]; cmp rax, 1`. -/
def testFlag : List Instr :=
  [.mov .rax (.mem { base := .rdi, disp := flagOff }), .alu .cmp .rax (.imm 1)]

/-- `c₁` where the flag word of the key context at `rdi` is not 1, `c₂` where
it is. -/
def onFlag (c₁ c₂ : Prog isa) : Prog isa :=
  .seq (.block testFlag) (Code.iteCold .ne c₁ c₂)

/-- `mov rax, v; mov [rdi + 1024], rax`: sets the flag word to `v`. -/
def storeFlag (v : BitVec 32) : List Instr :=
  [.mov .rax (.imm v), .store { base := .rdi, disp := flagOff } .rax]

/-- `vg_aes_gcm_prepare` computing no powers: the flag word says they are
absent. -/
def prepareAbsent : Prog isa :=
  .block (storeFlag 1)

/-- `vg_aes_gcm_prepare` computing the powers with `c`, after setting the flag
word to 0, so that the functions on the context read them. -/
def prepareFlagged (c : Prog isa) : Prog isa :=
  .seq (.block (storeFlag 0)) c

end VG.Impl.Gcm.X86_64.Flag
