module
public import VerifiedGarbage.Impl.MlKem1024.X86_64.Kem
public import VerifiedGarbage.Proof.MlKem.X86_64.KgBase
public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.RunA16

import VerifiedGarbage.Proof.MlKem.X86_64.Top768
public import VerifiedGarbage.Proof.MlKem.X86_64.KgH16Sel
meta import VerifiedGarbage.Proof.MlKem.X86_64.KgH16Sel
import VerifiedGarbage.Proof.MlKem1024.X86_64.Top
import VerifiedGarbage.Proof.MlKem.X86_64.Top16Ctl
meta import VerifiedGarbage.Proof.MlKem.X86_64.Top16Ctl
meta import VerifiedGarbage.Proof.MlKem.X86_64.EkSel16
import VerifiedGarbage.Proof.MlKem.X86_64.EkSel16
import VerifiedGarbage.Proof.MlKem.X86_64.Sel16
import VerifiedGarbage.Proof.MlKem.X86_64.DjSel16
meta import VerifiedGarbage.Proof.MlKem.X86_64.DjSel16
import VerifiedGarbage.Impl.MlKem.X86_64.KeyGenH16

/-!
# ML-KEM on x86-64: the stack pointer, for each implementation of `Sample4`

That no instruction of ML-KEM-768's and ML-KEM-1024's functions writes the
stack pointer, made with any implementation `v` of the four-way sampler,
which `Generic/MlKemSample4/X86_64/MlKem.lean` registers.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

theorem keyGen_spSafe (v : Sample4Impl) :
    (Impl.MlKem.X86_64.keyGen v.callee).all (fun i => !X86_64.isa.writesSp i) = true :=
  keyGenHSel_sp v (fun b B => by kgh_sp v b B kgRows768)
    (keyGenSel_sp v (fun _ c S => by s16_sp v c S kpke768) (by s4_sp v))

theorem encapsH_spSafe (v : Sample4Impl) :
    (Impl.MlKem.X86_64.encapsH v.callee).all (fun i => !X86_64.isa.writesSp i) = true :=
  encapsHSel_sp v (fun _ c S => by s16_sp v c S kpke768) (by s4_sp v)

theorem encaps_spSafe (v : Sample4Impl) :
    (Impl.MlKem.X86_64.encaps v.callee).all (fun i => !X86_64.isa.writesSp i) = true :=
  encapsSel_sp v (fun _ c b S B => by ek16_sp v c b S B kpke768) (by s4_sp v)

theorem decaps_spSafe (v : Sample4Impl) :
    (Impl.MlKem.X86_64.decaps v.callee).all (fun i => !X86_64.isa.writesSp i) = true :=
  decapsSel_sp v (fun _ c b S B => by ek16_sp v c b S B kpke768) (by s4_sp v)

theorem keyGen1024_spSafe (v : Sample4Impl) :
    (Impl.MlKem1024.X86_64.keyGen1024 v.callee).all (fun i => !X86_64.isa.writesSp i) = true :=
  keyGenSel_sp v (fun _ c S => by s16_sp v c S MlKem1024.X86_64.kpke1024) (by
    s4_sp v
    all_goals first | exact MlKem1024.X86_64.ce1024_sp _ | exact MlKem1024.X86_64.dd1024_sp _)

theorem encapsH1024_spSafe (v : Sample4Impl) :
    (Impl.MlKem1024.X86_64.encapsH1024 v.callee).all (fun i => !X86_64.isa.writesSp i) = true :=
  encapsHSel_sp v (fun _ c S => by s16_sp v c S MlKem1024.X86_64.kpke1024) (by
    s4_sp v
    all_goals first | exact MlKem1024.X86_64.ce1024_sp _ | exact MlKem1024.X86_64.dd1024_sp _)

theorem encaps1024_spSafe (v : Sample4Impl) :
    (Impl.MlKem1024.X86_64.encaps1024 v.callee).all (fun i => !X86_64.isa.writesSp i) = true :=
  encapsSel_sp v (fun _ c b S B => by ek16_sp v c b S B MlKem1024.X86_64.kpke1024) (by
    s4_sp v
    all_goals first | exact MlKem1024.X86_64.ce1024_sp _ | exact MlKem1024.X86_64.dd1024_sp _)

theorem decaps1024_spSafe (v : Sample4Impl) :
    (Impl.MlKem1024.X86_64.decaps1024 v.callee).all (fun i => !X86_64.isa.writesSp i) = true :=
  decapsSel_sp v (fun _ c b S B => by ek16_sp v c b S B MlKem1024.X86_64.kpke1024) (by
    s4_sp v
    all_goals first | exact MlKem1024.X86_64.ce1024_sp _ | exact MlKem1024.X86_64.dd1024_sp _)

end VG.Proof.MlKem.X86_64
