module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.EncryptStages
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.EncryptEraseTiming
public import VerifiedGarbage.Proof.Rsa.X86.PrivSetupTiming

/-! # Encryption traces agree for independent secret messages and padding -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Enc
open VG VG.X86 VG.Proof.Dsa.X86 VG.Proof.Bignum.X86
open VG.Impl.RsaPkcs1Enc.X86.Encrypt
open VG.Proof.Rsa.X86.PrivChecked (sp_agree pair_seq_ct)

theorem publicCall_relCT (v : PublicImpl) {g : Geometry} {bs1 bs2 : Fin 5 → List Byte}
    (exponent : bs1 1 = bs2 1) (pre : bs1 4 = bs2 4) :
    RelCT isa (fun s t => CallReady g bs1 s ∧ CallReady g bs2 t)
      (.call v.name v.code) (fun _ _ => True) := by
  apply RelCT.call v.verified.1 v.verified.2.1 (publicRd g) (publicWr g)
  intro s t h
  exact ⟨publicCall_pre h.1.context h.1.arguments, publicCall_pre h.2.context h.2.arguments,
    publicCall_pub h.1.context h.2.context exponent pre h.1.arguments h.2.arguments,
    (publicCovers h.1.context).1, (publicCovers h.1.context).2,
    (publicCovers h.2.context).1, (publicCovers h.2.context).2,
    h.1.context.sp.trans h.2.context.sp.symm⟩

theorem afterPub_relCT {g : Geometry} {bs1 bs2 : Fin 5 → List Byte} :
    RelCT isa (fun s t => Context g bs1 s ∧ Context g bs2 t) afterPub (fun _ _ => True) := by
  unfold afterPub
  apply pair_seq_ct (maskArgs_relCT.mono
    (fun _ _ h => sp_agree (h.1.sp.trans h.2.sp.symm)) (fun _ _ _ => trivial))
    (fun _ h => maskArgs_ready h) (fun _ h => maskArgs_ready h)
  apply pair_seq_ct (mask_relCT.mono (fun s t h => agree_regs (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.src.trans h.2.src.symm
    · exact h.1.count.trans h.2.count.symm)) (fun _ _ _ => trivial))
    (fun _ h => mask_done h) (fun _ h => mask_done h)
  exact wipe_relCT

theorem body_relCT (v : PublicImpl) {g : Geometry} {bs1 bs2 : Fin 5 → List Byte}
    (exponent : bs1 1 = bs2 1) (pre : bs1 4 = bs2 4) :
    RelCT isa (fun s t => Context g bs1 s ∧ Context g bs2 t)
      (body v.name v.code) (fun _ _ => True) := by
  unfold body
  apply pair_seq_ct (start_relCT.mono
    (fun _ _ h => sp_agree (h.1.sp.trans h.2.sp.symm)) (fun _ _ _ => trivial))
    (fun _ h => start_ready h) (fun _ h => start_ready h)
  apply pair_seq_ct encoding_relCT (fun _ h => encoding_done h) (fun _ h => encoding_done h)
  apply pair_seq_ct (callArgs_relCT.mono
    (fun _ _ h => sp_agree (h.1.sp.trans h.2.sp.symm)) (fun _ _ _ => trivial))
    (fun _ h => callArgs_ready h) (fun _ h => callArgs_ready h)
  exact pair_seq_ct (publicCall_relCT v exponent pre) (fun _ h => publicCall_done v h)
    (fun _ h => publicCall_done v h) afterPub_relCT

end VG.Proof.RsaPkcs1Enc.X86.Enc
