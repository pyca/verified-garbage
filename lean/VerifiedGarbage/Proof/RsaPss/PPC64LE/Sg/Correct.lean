module

public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.Enc
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.PrivCall
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Frame
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Entry
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.Checks
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.ByIdx
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Entry

/-!
# RSASSA-PSS signing on PPC64LE: correctness

Untrusted: everything here is checked by Lean. The checks (`checks_done`): a
modulus whose first byte is zero (`signOut_zero`), and an encoding too short
for the digest (`chkEm`) or the salt (`chkSalt`: `signOut_long`) write zeros
and return 0; otherwise the encoding (`signEnc_ok`) and the private operation
(`priv_ok`) give `signOut` (`signOut_eq`). `sign_ok`: the function, from
an entry state whose hash function's table holds the index of the code's
sizes, through `byIdx`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE.Sg

variable {pc : Bool}

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE.Sign
open VG.Impl.RsaOaep.PPC64LE (frameBytes restore Fns tword)
open VG.Impl.RsaPss.PPC64LE (MdFns byIdx idxs shapeOf)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaOaep.PPC64LE (Base Saves restore_ok freed_gpr freed_mem TabS)
open VG.Proof.RsaPss.PPC64LE (MdTabS twordA_ok byIdx_ok idxs_certs tab_sub)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only eval_zero eval_nonzero wp_nil)

/-- The result and `out`, from the entry state `s`. -/
def Post (pc : Bool) (Gs Gm : Spec.Mgf1.Hash) (s s' : State) : Prop :=
  abiPreserved s s' ∧ (HypS pc s →
    Spec.Rsa.writtenOutcome s'.mem (s.gpr .r3) (kk s) ((s'.gpr .r3).setWidth 32) (signOut Gs Gm s))

/-- Before the restores. -/
def Done (pc : Bool) (Gs Gm : Spec.Mgf1.Hash) (s t : State) : Prop :=
  Saves s t ∧ (HypS pc s →
    Spec.Rsa.writtenOutcome t.mem (s.gpr .r3) (kk s) ((t.gpr .r3).setWidth 32) (signOut Gs Gm s))

theorem n0_eq {s t : State} (E : Entered s t) (hz : (t.gpr .r9 == 0) = true) : s.mem (s.gpr .r5) = 0 := by
  have h : n0 s = 0#64 := by rw [← E.r9]; simpa using hz
  apply BitVec.eq_of_toNat_eq
  have := congrArg BitVec.toNat h
  simp only [n0, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at this
  rw [Nat.mod_eq_of_lt (by have := (s.mem (s.gpr .r5)).isLt; omega_using [])] at this
  simpa using this

theorem n0_ne {s t : State} (E : Entered s t) (hz : (t.gpr .r9 == 0) = false) : s.mem (s.gpr .r5) ≠ 0 :=
  fun h => by rw [E.r9, n0, h] at hz; simp at hz

/-- The frame's body depends on the hash function only by its digest
length. -/
theorem body_D {H H' : Hash} (hD : H.D = H'.D) (f : MdFns) (g : Fns) (pc : Bool) :
    body H f g pc = body H' f g pc := by
  simp only [body, checks, signMain, mPrime, chkEm, chkSalt, putSalt, putH, dbArgs,
    Impl.RsaPss.PPC64LE.hashFixed, hD]

section
variable {Gs Gm : Spec.Mgf1.Hash} {s : State} (P : PreS pc Gs.len s)
include P

theorem fail_done {t : State} (h : Base Ss vS s t) (hv : signOut Gs Gm s = .invalid) :
    WP isa Impl.RsaOaep.PPC64LE.encFail t (Done pc Gs Gm s) :=
  WP.mono (fail_ok P h) fun u ⟨sv, _, h3, hb⟩ => ⟨sv, fun _ => by rw [hv, h3]; exact ⟨rfl, hb⟩⟩

variable {H : Hash} (hH : HashOK H) (hGh : ∀ x, Gs.hash x = hH.SH.H.hash x) (hGl : Gs.len = H.D)
  (hHv : Proof.Mgf1.Valid Gs) {G : Hash} (hG : HashOK G) {g : Fns} (Tg : TabS G g gArg Ss s (stackArg s 15))
  (hGmh : ∀ x, Gm.hash x = hG.SH.H.hash x) (hGml : Gm.len = G.D) (hGmv : Proof.Mgf1.Valid Gm)
  {cn dn : String} {cc dc : Prog isa} {f : MdFns} (T : MdTabS H cn cc dn dc f hArg Ss s (stackArg s 14))
include hH hGh hGl hHv hG Tg hGmh hGml hGmv T

theorem checks_done (X : pc = true → PreXS s) {t : State} (E : Entered s t) (sy : t.syms = s.syms) :
    WP isa (checks H f g pc) t (Done pc Gs Gm s) := by
  have hk1 : 64 ≤ kk s := P.k1
  have hD64 : H.D ≤ 64 := hH.hD64
  refine WP.ite _ (eval_zero _ _) (fun hz => fail_done P E.base (signOut_zero Gs Gm (by omega_using [hk1]) (n0_eq E hz)))
    (fun hz => ?_)
  have h0 := n0_ne E hz
  refine WP.seq (WP.mono_syms (chkEm_ok P hD64 E h0) fun t₃ ⟨E₃, r3⟩ y₃ => ?_)
  refine WP.ite _ (eval_nonzero _ _) (fun hc => fail_done P E₃.base (signOut_long Gs Gm (by omega_using [hk1]) h0 ?_))
    (fun hc => ?_)
  · rw [r3] at hc; simp at hc; omega_using [hGl, hc]
  have hem : H.D + 2 ≤ kk s - loN s := by rw [r3] at hc; simp at hc; omega_using [hc]
  refine WP.seq (WP.mono_syms (chkSalt_ok P hD64 E₃ h0 hem) fun t₄ ⟨E₄, r3'⟩ y₄ => ?_)
  refine WP.ite _ (eval_nonzero _ _) (fun hc => fail_done P E₄.base (signOut_long Gs Gm (by omega_using [hk1]) h0 ?_))
    (fun hc => ?_)
  · rw [r3'] at hc; simp at hc; omega_using [hGl, hc]
  have hfit : Gs.len + (stackArg s 11).toNat + 2 ≤ kk s - loN s := by rw [r3'] at hc; simp at hc; omega_using [hGl, hem, hc]
  refine signEnc_ok P hH hGl hG Tg hGmh hGml hGmv T hGh E₄ (y₄.trans (y₃.trans sy)) h0 hfit fun t' b' _ hb => ?_
  refine WP.mono (priv_ok P X b' hb) fun u ⟨sv, _, hw⟩ => ⟨sv, fun hy => ?_⟩
  rw [signOut_eq Gs Gm hHv hGmv (by omega_using [hk1]) h0 hfit]
  exact hw hy

theorem body_ok (X : pc = true → PreXS s) {u : State} (hu : Only [.r11, .r12] (allocated frameBytes s) u)
    (sy : u.syms = s.syms) : WP isa (body H f g pc) u fun w => Post pc Gs Gm s (freed frameBytes w) := by
  refine WP.seq (WP.mono_syms (entry_ok P hu) fun t E y => WP.seq (WP.mono
    (checks_done P hH hGh hGl hHv hG Tg hGmh hGml hGmv T X E (y.trans sy)) fun t' ⟨sv, res⟩ =>
      WP.mono (restore_ok sv) fun w ⟨habi, h3, hm⟩ => ⟨habi, fun hy => ?_⟩))
  rw [freed_mem, freed_gpr, hm, h3]
  exact res hy

/-- `vg_rsa_pss_sign`, from an entry state whose hash function's table holds
the index `i`, whose code is for `H`'s digest length. -/
theorem sign_ok (X : pc = true → PreXS s) {i : Nat}
    (hidx : s.mem.readW (stackArg s 14 + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 i)
    (hi : i ∈ idxs) (hD : (shapeOf i).1.D = H.D) : WP isa (signG f g pc) s (Post pc Gs Gm s) := by
  have hi8 : i < 8 := by simp only [idxs, List.mem_cons, List.not_mem_nil, or_false] at hi; omega_using [hi]
  refine WP.alloc (by decide) (by have := P.sp1; have := stackBytes_ge pc; unfold frameBytes; omega_arith) ?_
  show WP isa (.seq (.block (tword .r11 hArg 5 ++ [])) _) _ _
  refine WP.seq (WP.of_syms (twordA_ok (j := hArg) (k := 5) (p := stackArg s 14) (by decide) (by decide)
    ⟨aR pc s, by rw [P.hrd]; simp, in_aR (by decide)⟩
    ((P.ka.sub_left kR_sub).sub_right (in_aR_sub (pc := pc) (by decide))).symm
    rfl ⟨tHR s, by rw [P.hrd]; simp, Offset.contains_base _ (by decide) (by decide)⟩
    ((P.kth.sub_left kR_sub).sub_right (tab_sub (n := 11) (show 5 < 11 by decide))).symm fun u o e => wp_nil fun y => ?_))
  rw [show 8 * 5 = 40 from rfl, hidx] at e
  refine byIdx_ok (D := i) (by omega_using [hi8])
    (F := fun u' => Only [.r11, .r12] (allocated frameBytes s) u' ∧ u'.syms = s.syms ∧
      u'.gpr .r11 = BitVec.ofNat 64 i)
    (fun _ h => h.2.2) (fun u₁ u₂ ⟨o₁, y₁, e₁⟩ o y => ⟨(o₁.trans o).mono, y.trans y₁, by rw [o.get .r11]; exact e₁⟩)
    (fun u' ⟨o', y', _⟩ => ?_) hi (fun x hx => (idxs_certs x hx).1) u ⟨o.mono, y.trans rfl, e⟩
  rw [body_D hD]
  exact body_ok P hH hGh hGl hHv hG Tg hGmh hGml hGmv T X o' y'

end

end VG.Proof.RsaPss.PPC64LE.Sg
