module

public import VerifiedGarbage.Impl.AesGcm.X86
public import VerifiedGarbage.Impl.Scrub.X86

/-! The IA-32 AES-GCM contiguous seal reads the caller's arguments in their original slots.
The private frame contains the existing GCM workspace and the outgoing CTR destination. -/
@[expose] public section
namespace VG.Impl.AesGcm.X86.Contiguous
open VG.X86

abbrev frameBytes := 2608

/-- After reserving the frame, the caller's argument words follow it and the return address. -/
abbrev callerSlot (i : Nat) := frameBytes / 4 + i

def setup : List Instr :=
  [.mov .eax (.reg .esp), .alu .add .eax (imm 48)] ++ saveAt ++
    [.mov .esi (.reg .ebp), .alu .add .esi (imm stO)] ++
    keep (callerSlot 0) ctxO ++ keep (callerSlot 1) roundsO ++ keep (callerSlot 2) dO ++
    keep (callerSlot 3) nO ++ [.store (at_ .ebp nlO) .eax] ++ keep (callerSlot 4) aadO ++
    keep (callerSlot 5) alO ++ keep (callerSlot 6) dataO ++ keep (callerSlot 8) lenO ++
    keep (callerSlot 9) tpO ++ [.mov .eax (argOp (callerSlot 7)), .store (at_ .esp 0) .eax,
      .mov .eax (imm 0), .store (at_ .ebp zO) .eax]

def body (c : Callees) : Prog isa :=
  .seq (.block setup) (.seq (oneAad c) (.seq (Open.decTo c c.ctr)
    (.seq (.block (keep (callerSlot 7) dataO)) (.seq (oneTag c 0) (.seq (tagOut 0) (.block restore))))))

def sealContiguous (c : Callees) : Prog isa :=
  .frame (.alloc frameBytes) (body c) (.free frameBytes)

/-- Wipe the caller-scratch registers and the private frame before returning. -/
def scrubbed (c : Callees) : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 2640 (sealContiguous c)

end VG.Impl.AesGcm.X86.Contiguous
