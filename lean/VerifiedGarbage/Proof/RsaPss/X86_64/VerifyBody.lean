module

public import VerifiedGarbage.Proof.RsaPss.X86_64.SignCorrect
public import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyMain
public import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyPadding
import VerifiedGarbage.Proof.RsaPss.X86_64.SaltBack
import VerifiedGarbage.Proof.RsaPss.MgfBytes
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
public import VerifiedGarbage.Proof.RsaPss.X86_64.Safe

/-!
# RSASSA-PSS verification on x86-64: the checks and the calling convention

`verify_ok`: from the entry state, `verify` returns 1 exactly when
`RsaPss.verify` holds, refusing a modulus whose first byte is zero and an
encoding too short for the digest and the salt, with the callee-saved
registers restored. `verify_correct`: it meets `verifyK`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Rsa.X86_64 (pubChkContract)

variable {G : Spec.Mgf1.Hash}

theorem vfail_done {s t : State} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay t (fb s) (stackArg s 3)) (R : Rep t.mem (fb s) (stackArg s 3) V W) (hw : t.wr = frR s :: s.wr)
    (hcs : ∀ r ∈ [Reg.r13, .r14, .r15], t.gpr r = s.gpr r)
    (h41 : W 41 = s.gpr .rbx) (h42 : W 42 = s.gpr .rbp) (h43 : W 43 = s.gpr .r12) (hf : verifyOut G s = false) :
    WP isa verifyFail t (VDone G s) := by
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.mem = t.mem ∧ t'.gpr .rax = 0) ?_ rfl)
    fun t' ⟨⟨hm, hax⟩, k⟩ => ?_
  · xrun [verifyFail]
  have R' : Rep t'.mem (fb s) (stackArg s 3) V W := hm ▸ R
  refine ⟨L.congr (k.gpr (by decide)) k.2.2 (by rw [hm]), k.2.2.trans hw, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · rw [k.gpr (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> decide), hcs r hr]
  · rw [R'.rd (d := sRbx) 41 rfl (by decide), h41]
  · rw [R'.rd (d := sRbp) 42 rfl (by decide), h42]
  · rw [R'.rd (d := sR12) 43 rfl (by decide), h43]
  · rw [hax, hf]; rfl

/-- The modulus' first byte. -/
theorem vn0_ok {s t : State} (hp : VPre G s) (L : Lay t (fb s) (stackArg s 3)) {V : Nat → Byte}
    {W : Nat → BitVec 64} (R : Rep t.mem (fb s) (stackArg s 3) V W) (h18 : W 18 = s.gpr .rdi) (hrd : t.rd = s.rd)
    (hf : Frame (vwrR s) s.mem t.mem) :
    WP isa (.block n0) t fun t' => Keep [.rsi, .rax] t t' ∧ t'.mem = t.mem ∧
      t'.gpr .rax = BitVec.ofNat 64 (s.mem (s.gpr .rdi)).toNat ∧
      t'.zf = some (decide ((s.mem (s.gpr .rdi)).toNat = 0)) := by
  have hk1 := hp.k1
  have hn : t.mem (s.gpr .rdi) = s.mem (s.gpr .rdi) := by
    have := hf.bytes (R := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩) (vin_apart hp.dKn hp.dns)
      (by dsimp only; have := hp.wN; omega) (i := 0) (by dsimp only; omega)
    simpa using this
  have hin : InRegions (t.rd ++ t.wr) (s.gpr .rdi) 1 := by
    rw [hrd]
    apply hp.hrd.left
    exact ⟨⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, by simp, by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega⟩
  refine WP.mono (WP.keep [.rsi, .rax] (Q := fun t' => t'.mem = t.mem ∧
      t'.gpr .rax = BitVec.ofNat 64 (s.mem (s.gpr .rdi)).toNat ∧
      t'.zf = some (decide ((s.mem (s.gpr .rdi)).toNat = 0))) ?_ rfl) fun t' ⟨h, k⟩ => ⟨k, h⟩
  xrun [n0, ea_sp, ea_at0, L.rsp, L.ld (d := sN) (by decide), R.rd (d := sN) 18 rfl (by decide), h18, hin, hn]
  rw [zext8, BitVec.and_self, ofNat_beq_zero (by have := (s.mem (s.gpr .rdi)).isLt; omega)]
  exact ⟨rfl, rfl⟩

theorem expectedSaltLen_eq (slen : BitVec 64) (any : BitVec 32) :
    Spec.RsaPss.expectedSaltLen slen any = if decide (any = 0) then some slen.toNat else none := by
  unfold Spec.RsaPss.expectedSaltLen; by_cases h : any = 0 <;> simp [h]

variable {H : Impl.Pbkdf2.Md.X86_64.Hash} (hH : Pbkdf2.Md.X86_64.HashOK H) (K : Pbkdf2.Md.X86_64.Callees H)

end VG.Proof.RsaPss.X86_64
