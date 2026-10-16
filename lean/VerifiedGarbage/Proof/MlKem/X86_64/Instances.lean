module

public import VerifiedGarbage.Proof.MlKem.X86_64.Top768
public import VerifiedGarbage.Proof.MlKem1024.X86_64.Top

/-!
# ML-KEM on x86-64: the stack pointer, for each implementation of `Sample4`

That no instruction of ML-KEM-768's and ML-KEM-1024's functions writes the
stack pointer, made with any implementation `v` of the four-way sampler,
which `Generic/MlKemSample4/X86_64/MlKem.lean` registers.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

theorem keyGen_spSafe (v : Sample4Impl) :
    (Impl.MlKem.X86_64.keyGen v.callee).all (fun i => !X86_64.isa.writesSp i) = true := by
  s4_sp v

theorem encapsH_spSafe (v : Sample4Impl) :
    (Impl.MlKem.X86_64.encapsH v.callee).all (fun i => !X86_64.isa.writesSp i) = true := by
  s4_sp v

theorem decaps_spSafe (v : Sample4Impl) :
    (Impl.MlKem.X86_64.decaps v.callee).all (fun i => !X86_64.isa.writesSp i) = true := by
  s4_sp v

theorem keyGen1024_spSafe (v : Sample4Impl) :
    (Impl.MlKem1024.X86_64.keyGen1024 v.callee).all (fun i => !X86_64.isa.writesSp i) = true := by
  s4_sp v

theorem encapsH1024_spSafe (v : Sample4Impl) :
    (Impl.MlKem1024.X86_64.encapsH1024 v.callee).all (fun i => !X86_64.isa.writesSp i) = true := by
  s4_sp v

theorem decaps1024_spSafe (v : Sample4Impl) :
    (Impl.MlKem1024.X86_64.decaps1024 v.callee).all (fun i => !X86_64.isa.writesSp i) = true := by
  s4_sp v

end VG.Proof.MlKem.X86_64
