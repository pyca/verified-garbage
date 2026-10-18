module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.EncryptAfter
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.EncodeTiming
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignBlocksTiming
public import VerifiedGarbage.Proof.Rsa.X86.PrivReleaseTiming

/-! # Erasure traces depend only on the common public pointer and byte count -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Enc
open VG VG.X86 VG.Impl.RsaPkcs1Enc.X86.Encrypt VG.Proof.Dsa.X86
open VG.Proof.Rsa.X86.PrivChecked (sp_agree)

theorem wipe_relCT {g : Geometry} {bs1 bs2 : Fin 5 → List Byte} :
    RelCT isa (fun s t => Context g bs1 s ∧ Context g bs2 t) wipe (fun _ _ => True) := by
  intro s t tr ur sf tf H E F
  obtain ⟨hs, ht⟩ := H
  cases E with
  | seq E1 E2 =>
    cases F with
    | seq F1 F2 =>
      have T1 := (wipeArgs_relCT _ _ _ _ _ _ (sp_agree (hs.sp.trans ht.sp.symm)) E1 F1).1
      obtain ⟨_, _, Ks, _, Ss, Cs⟩ := wp_result (wipeArgs_ok hs) E1
      obtain ⟨_, _, Kt, _, St, Ct⟩ := wp_result (wipeArgs_ok ht) F1
      cases E2 with
      | seq E3 E4 =>
        cases F2 with
        | seq F3 F4 =>
          have agree : VG.X86.Taint.Agree VG.Proof.RsaPkcs1Sig.X86.Sgn.clearTaint _ _ := agree_regs (by
            intro r hr
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl
            · exact Ss.trans St.symm
            · exact Cs.trans Ct.symm)
          have T2 := (VG.Proof.RsaPkcs1Sig.X86.Sgn.clear_relCT _ _ _ _ _ _ agree E3 F3).1
          have spS := Exec.gpr (NoSp.of_all (by decide +kernel) : NoSp (.loop (.block VG.Impl.Bignum.X86.PublicFn.clearStep) .ne)) E3
          have spT := Exec.gpr (NoSp.of_all (by decide +kernel) : NoSp (.loop (.block VG.Impl.Bignum.X86.PublicFn.clearStep) .ne)) F3
          have sp := (spS.trans (Ks.1 .esp (by decide))).trans
            ((hs.sp.trans ht.sp.symm).trans ((spT.trans (Kt.1 .esp (by decide))).symm))
          have T3 := (VG.Proof.RsaPkcs1Sig.X86.Sgn.return_relCT _ _ _ _ _ _ (sp_agree sp) E4 F4).1
          exact ⟨by rw [T1, T2, T3], trivial⟩

end VG.Proof.RsaPkcs1Enc.X86.Enc
