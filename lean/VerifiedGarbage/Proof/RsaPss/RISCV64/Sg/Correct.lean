module

-- separate module: it builds in parallel with `CTPriv` and `CTBlocks`, which `Verified` also needs.

public import VerifiedGarbage.Proof.RsaPss.RISCV64.Sg.Enc
public import VerifiedGarbage.Proof.RsaPss.RISCV64.Sg.Priv
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RISCV64.Syms

/-!
# RSASSA-PSS signing on RISC-V: correctness

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPss/PPC64LE/Sg/Correct.lean`): the checks (`checks_done`): a
modulus whose first byte is zero (`signOut_zero`), and an encoding too short
for the digest (`chkEm`) or the salt (`chkSalt`: `signOut_long`) write zeros
and return 0; otherwise the encoding (`signEnc_ok`) and the private operation
(`priv_ok`) give `signOut` (`signOut_eq`). `code_correct`: the function
against its shared contract.
-/

@[expose] public section

namespace VG.Proof.RsaPss.RISCV64.Sg

open VG VG.RISCV64 VG.Impl.RsaPss.RISCV64.Sign
open VG.Impl.RsaOaep.RISCV64 (frameBytes restore)
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.RsaOaep.RISCV64 (Base Saves restore_ok TabS)
open VG.Impl.RsaPss.RISCV64 (MdFns)
open VG.Proof.RsaPss.RISCV64 (MdL TabM)
open VG.Proof.RsaPkcs1Sig.RISCV64 (eval_zero eval_nonzero)

/-- The result and `out`, from the entry state `s`. -/
def Post (Hs Gs : Spec.Mgf1.Hash) (s s' : State) : Prop :=
  abiPreserved s s' ∧
    Spec.Rsa.writtenOutcome s'.mem (s.gpr .a0) (kk s) ((s'.gpr .a0).setWidth 32) (signOut Hs Gs s)

/-- Before the restores. -/
def Done (Hs Gs : Spec.Mgf1.Hash) (s t : State) : Prop :=
  Saves s t ∧ Spec.Rsa.writtenOutcome t.mem (s.gpr .a0) (kk s) ((t.gpr .a0).setWidth 32) (signOut Hs Gs s)

theorem n0_eq {s t : State} (E : Entered s t) (hz : (t.gpr .t1 == 0) = true) : s.mem (s.gpr .a2) = 0 := by
  have h : n0S s = 0#64 := by rw [← E.t1]; simpa using hz
  apply BitVec.eq_of_toNat_eq
  have := congrArg BitVec.toNat h
  simp only [n0S, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at this
  rw [Nat.mod_eq_of_lt (by have := (s.mem (s.gpr .a2)).isLt; omega)] at this
  simpa using this

theorem n0_ne {s t : State} (E : Entered s t) (hz : (t.gpr .t1 == 0) = false) : s.mem (s.gpr .a2) ≠ 0 :=
  fun h => by rw [E.t1, n0S, h] at hz; simp at hz

section
variable {Hs Gs : Spec.Mgf1.Hash} {s : State} (P : PreS Hs.len s)
include P

theorem fail_done {t : State} (h : Base Ss vS s t) (hv : signOut Hs Gs s = .invalid) :
    WP isa Impl.RsaOaep.RISCV64.encFail t (Done Hs Gs s) :=
  WP.mono (fail_ok P h) fun u ⟨sv, _, h3, hb⟩ => ⟨sv, by rw [hv, h3]; exact ⟨rfl, hb⟩⟩

variable {H : Hash} (hH : HashOK H) (hF : H.F ≤ 208) {M : MdL H hH} {dg : String} {f : MdFns} {p : Addr}
  (T : TabM M dg f 14 Ss s p) (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = H.D)
  (hHv : Proof.Mgf1.Valid Hs) {G : Hash} (hG : HashOK G) (hGF : G.F ≤ 208) {g : Impl.RsaOaep.RISCV64.Fns}
  {pg : Addr} (TG : TabS G g 15 Ss s pg) (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D)
  (hGv : Proof.Mgf1.Valid Gs)
include hH hF T hHh hHl hHv hG hGF TG hGh hGl hGv

theorem checks_done {t : State} (E : Entered s t) (sy : t.syms = s.syms) :
    WP isa (checks H M.be f g) t (Done Hs Gs s) := by
  have hk1 : 64 ≤ kk s := P.k1
  have hD64 : H.D ≤ 64 := hH.hD64
  refine WP.ite _ (eval_zero _ _) (fun hz => fail_done P E.base (signOut_zero Hs Gs (by omega) (n0_eq E hz)))
    (fun hz => ?_)
  have h0 := n0_ne E hz
  refine WP.seq (WP.mono_syms (chkEm_ok P hD64 E h0) fun t₃ ⟨E₃, r3⟩ y₃ => ?_)
  refine WP.ite _ (eval_nonzero _ _) (fun hc => fail_done P E₃.base (signOut_long Hs Gs (by omega) h0 ?_))
    (fun hc => ?_)
  · rw [r3] at hc; simp at hc; omega
  have hem : H.D + 2 ≤ kk s - loN s := by rw [r3] at hc; simp at hc; omega
  refine WP.seq (WP.mono_syms (chkSalt_ok P hD64 E₃ h0 hem) fun t₄ ⟨E₄, r3'⟩ y₄ => ?_)
  refine WP.ite _ (eval_nonzero _ _) (fun hc => fail_done P E₄.base (signOut_long Hs Gs (by omega) h0 ?_))
    (fun hc => ?_)
  · rw [r3'] at hc; simp at hc; omega
  have hfit : Hs.len + (stackArg s 11).toNat + 2 ≤ kk s - loN s := by rw [r3'] at hc; simp at hc; omega
  refine signEnc_ok P hH hF T hHh hHl hHv hG hGF TG hGh hGl hGv E₄ (y₄.trans (y₃.trans sy)) h0 hfit
    fun t' b' sp' _ hb => ?_
  refine WP.mono (priv_ok P b' sp' hb) fun u ⟨sv, _, hw⟩ => ⟨sv, ?_⟩
  rw [signOut_eq Hs Gs hHv hGv (by omega) h0 hfit]
  exact hw

/-- The code for the hash function `H`, in its frame. -/
theorem code_ok : WP isa (signFor H M.be f g) s (Post Hs Gs s) := by
  refine WP.alloc (by decide) (by have := P.sp1; rw [stackBytes_eq] at this; unfold frameBytes; omega) ?_
  refine WP.seq (WP.mono_syms (pro_ok P) fun t₀ E₀ y₀ => WP.seq (WP.mono_syms (spill_ok P E₀) fun t E y =>
    WP.seq (WP.mono (checks_done P hH hF T hHh hHl hHv hG hGF TG hGh hGl hGv E (y.trans (y₀.trans rfl)))
      fun t' ⟨sv, res⟩ => WP.mono (restore_ok sv (fb_al8 P)) fun w ⟨habi, h3, hm⟩ => ⟨habi, ?_⟩)))
  show Spec.Rsa.writtenOutcome w.mem _ _ ((w.gpr .a0).setWidth 32) _
  rw [hm, h3]
  exact res

end

end VG.Proof.RsaPss.RISCV64.Sg
