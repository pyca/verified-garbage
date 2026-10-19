module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyTailTiming
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyCallPublic

/-! # The verifier body relates even calls with inconsistent precomputed moduli -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Ver
open VG VG.X86 VG.Impl.RsaPkcs1Sig.X86.Verify
open VG.Proof.Rsa.X86.PrivChecked (sp_agree pair_seq_ct)

theorem publicCall_relCT (v : PublicImpl) {g : Geometry} {bs : Fin 5 → List Byte}
    (len : g.signatureLength = g.length) :
    RelCT isa (fun s t => CallReady g bs s ∧ CallReady g bs t)
      (.call v.name v.code) (fun _ _ => True) := by
  apply RelCT.call v.verified.1 v.verified.2.1 (publicRd g) (publicWr g)
  intro s t h
  exact ⟨publicCall_pre h.1.context h.1.args len, publicCall_pre h.2.context h.2.args len,
    publicCall_pub h.1.context h.2.context h.1.args h.2.args,
    (publicCovers h.1.context).1, (publicCovers h.1.context).2,
    (publicCovers h.2.context).1, (publicCovers h.2.context).2, h.1.context.sp.trans h.2.context.sp.symm⟩

theorem callThenCheck_relCT (v : PublicImpl) {g : Geometry} {bs : Fin 5 → List Byte}
    (len : g.signatureLength = g.length) :
    RelCT isa (fun s t => Context g bs s ∧ Context g bs t)
      (.seq (.block pubArgs) (.seq (.call v.name v.code) afterPub)) (fun _ _ => True) := by
  apply pair_seq_ct (pubArgs_relCT.mono
    (fun _ _ h => sp_agree (h.1.sp.trans h.2.sp.symm)) (fun _ _ _ => trivial))
    (fun _ h => callArgs_ready h) (fun _ h => callArgs_ready h)
  exact pair_seq_ct (publicCall_relCT v len) (fun _ h => publicCall_ready v h len)
    (fun _ h => publicCall_ready v h len) afterPub_relCT

structure LengthDone (g : Geometry) (bs : Fin 5 → List Byte) (s : State) : Prop where
  context : Context g bs s
  flag : s.zf = some (decide (g.signatureLength = g.length))

theorem length_done {g : Geometry} {bs : Fin 5 → List Byte} {s : State} (h : Context g bs s) :
    WP isa (.block lenCheck) s (LengthDone g bs) := by
  refine WP.mono (lengthCheck_ok h) ?_
  rintro t ⟨ht, _, _, flag⟩
  exact ⟨ht, flag⟩

theorem body_relCT (v : PublicImpl) {g : Geometry} {bs : Fin 5 → List Byte} :
    RelCT isa (fun s t => Context g bs s ∧ Context g bs t) (body v.name v.code) (fun _ _ => True) := by
  unfold body
  apply pair_seq_ct (length_relCT.mono
    (fun _ _ h => sp_agree (h.1.sp.trans h.2.sp.symm)) (fun _ _ _ => trivial))
    (fun _ h => length_done h) (fun _ h => length_done h)
  apply RelCT.ite
  · intro s t h
    change s.zf.map (! ·) = t.zf.map (! ·)
    rw [h.1.flag, h.2.flag]
  · exact ret0_relCT.mono (fun _ _ h => sp_agree (h.1.1.context.sp.trans h.1.2.context.sp.symm)) (fun _ _ _ => trivial)
  · intro s t tr ur sf tf h E F
    have len : g.signatureLength = g.length := by
      have flag := h.2
      simpa only [eval, h.1.1.flag, Option.map_some, Option.some.injEq,
        Bool.not_eq_false', decide_eq_true_eq] using flag
    exact callThenCheck_relCT v len s t tr ur sf tf ⟨h.1.1.context, h.1.2.context⟩ E F

end VG.Proof.RsaPkcs1Sig.X86.Ver
