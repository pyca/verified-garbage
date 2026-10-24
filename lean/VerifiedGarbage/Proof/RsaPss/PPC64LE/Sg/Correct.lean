module

public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.Enc
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.PrivCall
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Frame
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Entry
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.Checks

/-!
# RSASSA-PSS signing on PPC64LE: correctness

Untrusted: everything here is checked by Lean. The checks (`checks_done`): a
modulus whose first byte is zero (`signOut_zero`), and an encoding too short
for the digest (`chkEm`) or the salt (`chkSalt`: `signOut_long`) write zeros
and return 0; otherwise the encoding (`signEnc_ok`) and the private operation
(`priv_ok`) give `signOut` (`signOut_eq`). `code_correct`: the function
against its shared contract.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE.Sg

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE.Sign
open VG.Impl.RsaOaep.PPC64LE (frameBytes restore)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaOaep.PPC64LE (Base Saves restore_ok freed_gpr freed_mem)
open VG.Proof.RsaPkcs1Sig.PPC64LE (eval_zero eval_nonzero)

/-- The result and `out`, from the entry state `s`. -/
def Post (Gs : Spec.Mgf1.Hash) (s s' : State) : Prop :=
  abiPreserved s s' ∧ Spec.Rsa.writtenOutcome s'.mem (s.gpr .r3) (kk s) ((s'.gpr .r3).setWidth 32) (signOut Gs s)

/-- Before the restores. -/
def Done (Gs : Spec.Mgf1.Hash) (s t : State) : Prop :=
  Saves s t ∧ Spec.Rsa.writtenOutcome t.mem (s.gpr .r3) (kk s) ((t.gpr .r3).setWidth 32) (signOut Gs s)

theorem n0_eq {s t : State} (E : Entered s t) (hz : (t.gpr .r9 == 0) = true) : s.mem (s.gpr .r5) = 0 := by
  have h : n0 s = 0#64 := by rw [← E.r9]; simpa using hz
  apply BitVec.eq_of_toNat_eq
  have := congrArg BitVec.toNat h
  simp only [n0, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at this
  rw [Nat.mod_eq_of_lt (by have := (s.mem (s.gpr .r5)).isLt; omega)] at this
  simpa using this

theorem n0_ne {s t : State} (E : Entered s t) (hz : (t.gpr .r9 == 0) = false) : s.mem (s.gpr .r5) ≠ 0 :=
  fun h => by rw [E.r9, n0, h] at hz; simp at hz

section
variable {Gs : Spec.Mgf1.Hash} {s : State} (P : PreS Gs.len s)
include P

theorem fail_done {t : State} (h : Base Ss vS s t) (hv : signOut Gs s = .invalid) :
    WP isa Impl.RsaOaep.PPC64LE.encFail t (Done Gs s) :=
  WP.mono (fail_ok P h) fun u ⟨sv, _, h3, hb⟩ => ⟨sv, by rw [hv, h3]; exact ⟨rfl, hb⟩⟩

variable {H : Hash} (hH : HashOK H) (hGh : ∀ x, Gs.hash x = hH.SH.H.hash x) (hGl : Gs.len = H.D)
  (hGv : Proof.Mgf1.Valid Gs)
include hH hGh hGl hGv

theorem checks_done {t : State} (E : Entered s t) : WP isa (checks H) t (Done Gs s) := by
  have hk1 : 64 ≤ kk s := P.k1
  have hD64 : H.D ≤ 64 := hH.hD64
  refine WP.ite _ (eval_zero _ _) (fun hz => fail_done P E.base (signOut_zero Gs (by omega) (n0_eq E hz)))
    (fun hz => ?_)
  have h0 := n0_ne E hz
  refine WP.seq (WP.mono (chkEm_ok P hD64 E h0) fun t₃ ⟨E₃, r3⟩ => ?_)
  refine WP.ite _ (eval_nonzero _ _) (fun hc => fail_done P E₃.base (signOut_long Gs (by omega) h0 ?_))
    (fun hc => ?_)
  · rw [r3] at hc; simp at hc; omega
  have hem : H.D + 2 ≤ kk s - loN s := by rw [r3] at hc; simp at hc; omega
  refine WP.seq (WP.mono (chkSalt_ok P hD64 E₃ h0 hem) fun t₄ ⟨E₄, r3'⟩ => ?_)
  refine WP.ite _ (eval_nonzero _ _) (fun hc => fail_done P E₄.base (signOut_long Gs (by omega) h0 ?_))
    (fun hc => ?_)
  · rw [r3'] at hc; simp at hc; omega
  have hfit : Gs.len + (stackArg s 10).toNat + 2 ≤ kk s - loN s := by rw [r3'] at hc; simp at hc; omega
  refine signEnc_ok P hH hGh hGl hGv E₄ h0 hfit fun t' b' hb => ?_
  refine WP.mono (priv_ok P b' hb) fun u ⟨sv, _, hw⟩ => ⟨sv, ?_⟩
  rw [signOut_eq Gs hGv (by omega) h0 hfit]
  exact hw

theorem code_ok : WP isa (sign H) s (Post Gs s) := by
  refine WP.alloc (by decide) (by have := P.sp1; rw [stackBytes_eq] at this; unfold frameBytes; omega) ?_
  refine WP.seq (WP.mono (entry_ok P) fun t E => WP.seq (WP.mono
    (checks_done P hH hGh hGl hGv E) fun t' ⟨sv, res⟩ => WP.mono (restore_ok sv) fun w ⟨habi, h3, hm⟩ =>
      ⟨habi, ?_⟩))
  rw [freed_mem, freed_gpr, hm, h3]
  exact res

end

/-- The correctness of `vg_rsa_pss_<H>_mgf1_<H>_sign`, against its shared
contract. -/
theorem code_correct {H : Hash} (hH : HashOK H) {Gs : Spec.Mgf1.Hash} (hGh : ∀ x, Gs.hash x = hH.SH.H.hash x)
    (hGl : Gs.len = H.D) (hGv : Proof.Mgf1.Valid Gs) (s : State)
    (h : (Spec.RsaPss.signContract Gs Gs abi stackBytes).pre s) :
    ∃ t s', Exec isa (sign H) s t s' ∧ abiPreserved s s' ∧ (Spec.RsaPss.signContract Gs Gs abi stackBytes).post s s' := by
  obtain ⟨t, s', he, habi, hr⟩ := code_ok (preS_of h) hH hGh hGl hGv
  refine ⟨t, s', he, habi, ?_⟩
  have e : stackBytes = 3775 + 1 := rfl
  rw [e]
  sig_post [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi, argRegs, stackArgs_thirteen, List.append_eq]
  exact hr

end VG.Proof.RsaPss.PPC64LE.Sg
