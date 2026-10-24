module

public import VerifiedGarbage.Impl.RsaPkcs1Enc.PPC64LE.Decrypt
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha256
meta import VerifiedGarbage.Impl.RsaPkcs1Enc.PPC64LE.Decrypt
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha256

/-!
# `vg_rsa_pkcs1_decrypt` on PPC64LE: the calls of SHA-256 and HMAC, in two runs

Each call of SHA-256's streaming functions and of HMAC-SHA-256's `init` and
`finalize` leaks the same in two runs whose stack pointers and argument
registers agree (the taint analysis, through the callees).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Impl.RsaPkcs1Enc.PPC64LE.Decrypt

/-- Two runs whose stack pointers and registers `rs` agree. -/
def AgreeOn (rs : List Reg) (a b : State) : Prop := a.sp = b.sp ∧ ∀ r ∈ rs, a.gpr r = b.gpr r

theorem rel_of {rs : List Reg} {c : Prog isa} {hc : VG.Taint.Hint T}
    (h : (taint.check (ofRegs rs) c hc).isSome = true) {P : State → State → Prop}
    (hp : ∀ a b, P a b → AgreeOn rs a b) : RelCT isa P c fun _ _ => True :=
  RelCT.taint (A := taint) (ofRegs rs) (fun a b hab => ⟨(hp a b hab).1, fun r hr =>
    (hp a b hab).2 r (RegSet.mem_ofList.mp hr)⟩) h

theorem init_rel {P : State → State → Prop} (hp : ∀ a b, P a b → AgreeOn [.r3] a b) :
    RelCT isa P initCall fun _ _ => True :=
  rel_of (by taint_decide) hp

theorem upd_rel {P : State → State → Prop} (hp : ∀ a b, P a b → AgreeOn [.r3, .r4, .r5, .r6, .r7] a b) :
    RelCT isa P updCall fun _ _ => True :=
  rel_of (by taint_decide) hp

theorem fin_rel {P : State → State → Prop} (hp : ∀ a b, P a b → AgreeOn [.r3, .r4, .r5, .r6] a b) :
    RelCT isa P finCall fun _ _ => True :=
  rel_of (by taint_decide) hp

theorem macInit_rel {P : State → State → Prop} (hp : ∀ a b, P a b → AgreeOn [.r3, .r4, .r5, .r6, .r7] a b) :
    RelCT isa P macInitCall fun _ _ => True :=
  rel_of (by taint_decide) hp

theorem macFin_rel {P : State → State → Prop} (hp : ∀ a b, P a b → AgreeOn [.r3, .r4, .r5, .r6, .r7] a b) :
    RelCT isa P macFinCall fun _ _ => True :=
  rel_of (by taint_decide) hp

end VG.Proof.RsaPkcs1Enc.PPC64LE.Dec
