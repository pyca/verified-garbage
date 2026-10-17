module

import VerifiedGarbage.Proof.AesGcm.X86_64.InitPCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.InitPCT
public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.InitZ
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.InitZ
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.AesGcm.X86_64.InitCT
import VerifiedGarbage.Proof.Framework.X86_64.ZLaneSse
meta import VerifiedGarbage.Proof.AesGcm.X86_64.InitCT
meta import VerifiedGarbage.Proof.Framework.X86_64.ZLaneSse
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT

/-! # Constant-time key setup with prepared powers on 512-bit registers -/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64
open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64

theorem initZ_rel (v : GcmImpl) {s₀ s₀' : State} (hp : Proof.AesGcm.initPreparedX86_64.pre s₀)
    (hp' : Proof.AesGcm.initPreparedX86_64.pre s₀') (hq : Proof.AesGcm.initPreparedX86_64.pub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (Prepared.initZ v.callees) fun _ _ => True := by
  refine initWith_rel v (by decide) hp hp' hq ?_
  exact rel_taint (P := fun t₁ t₂ => InitTail (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .rsp) s₀.rd s₀.wr t₁ ∧
      InitTail (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .rsp) s₀'.rd s₀'.wr t₂)
    (c := .block (Prepared.powersZ ++ restore)) [.r13, .r15, .rsp]
    (fun _ _ h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h.1.1, h.2.1]
      · rw [h.1.2.1, h.2.2.1]
      · rw [h.1.2.2.1, h.2.2.2.1]) ⟨_, by taint_decide⟩

theorem initZ_ct (v : GcmImpl) :
    ConstantTime isa Proof.AesGcm.initPreparedX86_64.pre Proof.AesGcm.initPreparedX86_64.pub
      (Prepared.initZ v.callees) :=
  ct_of_rel fun _ _ hp hp' hq => initZ_rel v hp hp' hq

end VG.Proof.AesGcm.X86_64
