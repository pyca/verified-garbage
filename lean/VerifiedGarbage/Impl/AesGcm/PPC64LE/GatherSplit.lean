module

public import VerifiedGarbage.Impl.AesGcm.PPC64LE.SealGather
public import VerifiedGarbage.Impl.AesGcm.PPC64LE.SealSplit

/-! # Gather AES-GCM plaintext through the verified split-seal entry

The first piece remains in its source buffer. Advance the destination past
it, gather the remaining pieces with the shared loop, and pass the first
piece to split seal. The existing Rust gather API supplies the descriptors.
The six argument-save slots may be reused for outgoing stack arguments once
the original arguments have been restored; the return address stays at 152.
-/

@[expose] public section
namespace VG.Impl.AesGcm.PPC64LE.GatherSplit
open VG.PPC64LE


def select : List Instr := [.load .d .r0 .r12 264,.lsr .d .r0 .r0 9]


def skip : List Instr :=
  [.load .d .r3 .r7 8,.add .r9 .r9 .r3,.addi .r7 .r7 16,.subi .r8 .r8 1]


def firstArgs : List Instr :=
  [.lsl .r11 .r10 4,.sub .r11 .r7 .r11,.load .d .r9 .r11 0,.load .d .r10 .r11 8]


def stackArgs : List Instr :=
  (List.range 3).flatMap (VG.Impl.StackScratch.PPC64LE.copyArg 160)


def callArgs : List Instr := firstArgs ++ SealGather.callArgs.take 6 ++ stackArgs


def sealCode : Prog isa :=
  VG.Impl.StackScratch.PPC64LE.withStackScratchArgs 2688 3 SealSplit.seal


def fast : Prog isa := .seq (.seq (.block skip) VG.Impl.Gather.PPC64LE.gather)
  (.seq (.block callArgs)
    (.seq (.call "vg_aes_gcm_seal_split" sealCode) (.block SealGather.ret)))


def body : Prog isa := .seq (.block select)
  (.ite (.zero .d .r0) SealGather.body fast)


def sealGather : Prog isa := SealGather.withBody body

end VG.Impl.AesGcm.PPC64LE.GatherSplit
