module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.DecSel
import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.DecTaint
public import VerifiedGarbage.Proof.Bignum.Arm.MaskBytesCT
public import VerifiedGarbage.Proof.Bignum.Arm.CopyBytesCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# RSAES-PKCS1-v1_5 decryption on ARMv7: the body

The pieces in order, each correct and constant time at once (`body_vp`):
from a state of the body to the result the shared contract states (`Fin`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.Arm.Dec

open VG VG.Arm VG.Impl.RsaPkcs1Enc.Arm.Decrypt VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.Rsa.Arm.Recover (VP)

variable {P : EP}

theorem Base.of_mem {σ s t : State} (h : Base P σ s) (st : P.lay.St σ t) (hm : t.mem = s.mem) : Base P σ t :=
  h.frame st (rs := []) (by rw [hm]; exact Frame.refl _ _) fun _ h => absurd h List.not_mem_nil

/-! ## The private-key operation and `D` -/

theorem privArgs_vp : VP (S P) (.block privArgs) (R1 P) :=
  VP.stk (code := privArgs.tail) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁ h₂) fun _ _ h => privArgs_wp h

theorem dZero_vp : VP (R2 P) (.block dZero) (D1 P) :=
  VP.stk (code := [_, _, _, _, _]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1 h₂.1)
    fun _ _ h => dZero_wp h

theorem zero_vp : VP (D1 P) Impl.Bignum.Arm.maskBytes (D2 P) :=
  VP.ct Bignum.Arm.maskBytes_ct (fun _ _ _ _ h₁ h₂ => ⟨by rw [h₁.2.1, h₂.2.1], by rw [h₁.2.2.1, h₂.2.2.1]⟩)
    fun _ _ h => zero_wp h

theorem dCopy_vp : VP (D2 P) (.block dCopy) (D3 P) :=
  VP.stk (code := [_, _, _, _, _, _, _]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1.1 h₂.1.1)
    fun _ _ h => dCopy_wp h

theorem copy_vp : VP (D3 P) Impl.Bignum.Arm.copyBytes (D4 P) :=
  VP.ct Bignum.Arm.copyBytes_ct (fun _ _ _ _ h₁ h₂ => ⟨by rw [h₁.2.1, h₂.2.1], by rw [h₁.2.2.1, h₂.2.2.1],
    by rw [h₁.2.2.2, h₂.2.2.2]⟩) fun _ _ h => copy_wp h

/-! ## `DH` and `KDK` -/

theorem hashD_vp : VP (D4 P) (hashD decFns) (H6 P) :=
  ((VP.stk (code := [_]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1.1 h₂.1.1)
    fun _ _ h => shaInitArgs_wp h).seq shaInit_vp).seq
  (((VP.stk (code := [_, _, _, _, _, _, _]) (by decide) (by decide)
    (fun _ _ _ _ h₁ h₂ => S_sp h₁.1.1.1 h₂.1.1.1) fun _ _ h => shaUpdArgs_wp h).seq shaUpd_vp).seq
  ((VP.stk (code := [_, _, _, _, _]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1.1 h₂.1.1)
    fun _ _ h => shaFinArgs_wp h).seq shaFin_vp))

theorem kdkInitArgs_vp : VP (H6 P) (.block (macInitArgs sDH)) (K1 P) :=
  VP.stk (code := [_, _, _, _]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1.1 h₂.1.1)
    fun _ _ h => macInitArgs_wp (by decide) h.1.1 fun t st hm ha =>
      ⟨⟨h.1.of_mem st hm, by rw [hm]; exact h.2⟩, ha⟩

theorem kdkMac_vp : VP (H6 P) (kdkMac decFns) (K6 P) :=
  (kdkInitArgs_vp.seq kdkInit_vp).seq
  (((VP.stk (code := [_, _, _, _, _, _, _]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1.1 h₂.1.1)
    fun _ _ h => kdkUpdArgs_wp h).seq kdkUpd_vp).seq
  ((VP.stk (code := [_, _, _, _, _, _, _]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1.1 h₂.1.1)
    fun _ _ h => kdkFinArgs_wp h).seq kdkFin_vp))

/-! ## The padding and the output -/

theorem selPart_vp : VP (AL P) selPart (Fin P) :=
  (VP.stk (code := [_, _, _, _, _, _, _, _]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.sb.S h₂.sb.S)
    fun _ _ h => scanInit_wp h).seq (scanLoop_vp.seq
  ((VP.stk (code := [_, _, _, _]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1.S h₂.1.S)
    fun _ _ h => validLoads_wp h).seq
  ((VP.taint [.r0] validBlock_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.1, h₂.2.1]) fun _ _ h => validBlock_wp h).seq
  ((VP.stk (code := [_]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1.S h₂.1.S)
    fun _ _ h => mlLoad_wp h).seq
  ((VP.taint [.r1] mlStore_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2]) fun _ _ h => mlStore_wp h).seq
  ((VP.stk (code := [_, _, _, _, _]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1.1.S h₂.1.1.S)
    fun _ _ h => selInit_wp h).seq (selLoop_vp.seq
  (VP.stk (code := [_]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1 h₂.1)
    fun _ _ h => fin_wp h))))))))

/-! ## The body -/

theorem body_vp (v : Proof.Rsa.Arm.CrtImpl) :
    VP (S P) (body decFns (Proof.Rsa.Arm.privName v) (Proof.Rsa.Arm.privCode v)) (Fin P) :=
  privArgs_vp.seq ((call_vp v).seq (dZero_vp.seq (zero_vp.seq (dCopy_vp.seq (copy_vp.seq (hashD_vp.seq
    (kdkMac_vp.seq (clLoop_vp.seq (amLoop_vp.seq (alPart_vp.seq selPart_vp))))))))))

end VG.Proof.RsaPkcs1Enc.Arm.Dec
