import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx512.Verified
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe

/-!
# The bitsliced ECB code on x86-64 writes `rsp` only in its frame

Each implementation of ECB runs its own batches and then the next one's
(`BitsliceAvx512.ecb d = .seq (wide d) (BitsliceAvx2.ecb d)`, and so on down
to the general-purpose registers' code), so the kernel checks each level's
own batches once here, for both `Artifact.spSafe` and the frame's
hypothesis, rather than every level below it again in each of them.
-/

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 Impl.TripleDes.X86_64

theorem bitslice_ecb_sp (d : Spec.TripleDes.Direction) :
    (Bitslice.ecb d).allInstrs (fun i => !isa.writesSp i) = true := by
  cases d
  · show Bitslice.encrypt.allInstrs _ = true; lit_decide
  · show Bitslice.decrypt.allInstrs _ = true; lit_decide

theorem sse_ecb_sp (d : Spec.TripleDes.Direction) :
    (BitsliceSse.ecb d).allInstrs (fun i => !isa.writesSp i) = true := by
  show ((BitsliceSse.wide d).allInstrs _ && (Bitslice.ecb d).allInstrs _) = true
  rw [bitslice_ecb_sp, Bool.and_true]
  cases d <;> lit_decide

theorem avx2_ecb_sp (d : Spec.TripleDes.Direction) :
    (BitsliceAvx2.ecb d).allInstrs (fun i => !isa.writesSp i) = true := by
  show ((BitsliceAvx2.wide d).allInstrs _ && (BitsliceSse.ecb d).allInstrs _) = true
  rw [sse_ecb_sp, Bool.and_true]
  cases d <;> lit_decide

theorem avx512_ecb_sp (d : Spec.TripleDes.Direction) :
    (BitsliceAvx512.ecb d).allInstrs (fun i => !isa.writesSp i) = true := by
  show ((BitsliceAvx512.wide d).allInstrs _ && (BitsliceAvx2.ecb d).allInstrs _) = true
  rw [avx2_ecb_sp, Bool.and_true]
  cases d <;> lit_decide

/-- An implementation of ECB that writes `rsp` only in its frames does so in
its stack frame too: `Artifact.spSafe`. -/
theorem ecb_spSafe {c : Prog isa} (h : c.allInstrs (fun i => !isa.writesSp i) = true) :
    (Impl.StackScratch.X86_64.withStackScratchWiped 1032 .rcx 128 c).all
      (fun i => !isa.writesSp i) = true :=
  withStackScratch_spSafe (by decide)
    (by simp only [Code.all, Code.all_of_allInstrs h, wipe_spSafe, Bool.and_self])

end VG.Proof.TripleDes.X86_64
