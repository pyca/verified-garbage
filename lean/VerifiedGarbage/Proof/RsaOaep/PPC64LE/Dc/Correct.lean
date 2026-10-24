module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Main
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.MgfArith
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Label
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Out
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Entry

/-!
# RSAES-OAEP decryption on PPC64LE: correctness

Untrusted: everything here is checked by Lean. The entry, the private
operation (`priv_ok`), the check of `k ≥ 2 hLen + 2` (public), then either
zeros and the result `r = 2 ? 2 : 0` (`decFail_ok`, which is what `decOut`
says for a too short `k`) or the decoding (`decMain_ok`), and the restores:
RSAES-OAEP-DECRYPT (RFC 8017 §7.1.2). `code_correct`: the function against
its shared contract.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaOaep.PPC64LE.Dec VG.WriteBytes
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep wp_li wp_sub wp_lsr wp_nil eval_nonzero)
open VG.Proof.RsaPkcs1Sig (bytesAt_length bytesAt_writeBytes)
open VG.Proof.RsaOaep (decOut decOut_short)
open VG.Proof.Mgf1 (ifp ifn)

/-- The result and the outputs, from the entry state `s`. -/
def Post (Hs Gs : Spec.Mgf1.Hash) (s s' : State) : Prop :=
  abiPreserved s s' ∧ Spec.RsaOaep.writtenDecrypt s'.mem (s.gpr .r3) (s.gpr .r5) (kk s) ((s'.gpr .r3).setWidth 32)
    (decOut Hs Gs (labB s) (privO s))

/-- Before the restores. -/
def Done (Hs Gs : Spec.Mgf1.Hash) (s t : State) : Prop :=
  Saves s t ∧ Spec.RsaOaep.writtenDecrypt t.mem (s.gpr .r3) (s.gpr .r5) (kk s) ((t.gpr .r3).setWidth 32)
    (decOut Hs Gs (labB s) (privO s))

theorem AfterPriv.only {s v v' : State} {rs : List Reg} (A : AfterPriv s v) (P : PreD s) (o : Only rs v v')
    (hrs : ∀ r ∈ rs, r ∉ .r14 :: fx ++ hiRegs := by decide) : AfterPriv s v' := by
  have hm : v'.mem = v.mem := o.mem
  have b := A.base
  rw [← hm] at b
  exact ⟨b.only (fitsM P) o hrs, hm ▸ A.mem, hm ▸ A.em⟩

/-- `EM` too short for the hash: what decryption returns, from the private
operation's result. -/
theorem decOut_short' {Hs Gs : Spec.Mgf1.Hash} {lab : List Byte} {o : Spec.Rsa.Outcome} {k : Nat}
    (hl : ∀ em, o = .ok em → em.length = k) (hk : k < 2 * Hs.len + 2) :
    decOut Hs Gs lab o = if rcOf o = 2 then .fault else .invalid := by
  rw [decOut_short hl hk]
  cases o <;> rfl

section
variable {H G : Hash} (hH : HashOK H) (hG : HashOK G) {Hs Gs : Spec.Mgf1.Hash}
  (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = H.D) (hHv : Proof.Mgf1.Valid Hs)
  (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs)
  {s : State} (P : PreD s)
include hH hG hHh hHl hHv hGh hGl hGv P

omit hH hG hHh hHv hGh hGl hGv in
theorem fail_done {v : State} (A : AfterPriv s v) (hk : kk s < 2 * H.D + 2) :
    WP isa decFail v (Done Hs Gs s) := by
  have hrc := rcOf_le (privO s)
  refine WP.mono (decFail_ok P A.base hrc) fun u ⟨sv, _, hm, h3⟩ => ⟨sv, ?_⟩
  have hk2 := P.k2
  have ek : kk s = (s.gpr .r7).toNat := rfl
  have hl : ∀ em, privO s = .ok em → em.length = kk s := fun em he => by
    have := A.em; rw [he] at this; simp only [emOf] at this; rw [← this, bytesAt_length]
  rw [decOut_short' hl (by rw [hHl]; exact hk)]
  have hout : Spec.Rsa.bytesAt u.mem (s.gpr .r3) (kk s) = List.replicate (kk s) 0 := by
    have e := bytesAt_writeBytes v.mem (s.gpr .r3) (List.replicate (kk s) 0)
      (by rw [List.length_replicate]; omega)
    rw [List.length_replicate] at e
    rw [← e, hm]
    have f : Frame [mlR s] (writeBytes v.mem (s.gpr .r3) (List.replicate (kk s) 0))
        ((writeBytes v.mem (s.gpr .r3) (List.replicate (kk s) 0)).writeW (s.gpr .r5) (0#64)) :=
      (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    exact f _ (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact fun hc => P.oml _ (Offset.contains_base _ (by have := P.ok; omega) (by omega)) hc)
  have hml : u.mem.readW (s.gpr .r5) 64 = 0 := by rw [hm, Mem.readW_writeW_self64]; rfl
  have hrc2 := rcOf_le (privO s)
  by_cases h2 : rcOf (privO s) = 2
  · rw [ifp h2]; exact ⟨by rw [h3, ifp h2]; decide, hout, hml⟩
  · rw [ifn h2]; exact ⟨by rw [h3, ifn h2]; decide, hout, hml⟩

omit hH hG hHh hHl hHv hGh hGl hGv in
/-- The check of `k`: in `r3`, whether it is too short. -/
theorem chk_ok (hD64 : H.D ≤ 64) {v : State} (A : AfterPriv s v) :
    WP isa (.block (Dec.chkK H)) v fun v' => AfterPriv s v' ∧ (v'.gpr .r3 != 0) = decide (kk s < 2 * H.D + 2) := by
  have hk2 := P.k2
  have ek : kk s = (s.gpr .r7).toNat := rfl
  have e7 : s.gpr .r7 = BitVec.ofNat 64 (kk s) := ((BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _)).symm
  refine wp_li (by omega) fun v₁ o₁ e₁ => wp_sub fun v₂ o₂ e₂ => wp_lsr fun v₃ o₃ e₃ => wp_nil ?_
  have k₃ : Only [.r3] v v₃ := (o₁.trans (o₂.trans o₃)).mono
  refine ⟨A.only P k₃, ?_⟩
  rw [e₃, e₂, e₁, o₁.get .r15, Base.r15 A.base, e7]
  exact ne_zero_ltBit (by omega) (by omega)

/-- The branch on the check of `k`. -/
theorem ite_done {v : State} (A : AfterPriv s v) (r3 : (v.gpr .r3 != 0) = decide (kk s < 2 * H.D + 2)) :
    WP isa (.ite (.nonzero .d .r3) decFail (decMain H G)) v (Done Hs Gs s) :=
  WP.ite _ (eval_nonzero _ _) (fun hc => fail_done hHl P A (by rw [r3] at hc; simpa using hc))
    (fun hc => WP.mono (decMain_ok P hH hG hHh hHl hHv hGh hGl hGv A (by rw [r3] at hc; simp at hc; omega))
      fun u ⟨sv, _, hw⟩ => ⟨sv, hw⟩)

theorem checks_done {v : State} (A : AfterPriv s v) :
    WP isa (.block (Dec.chkK H)) v fun v' =>
      WP isa (.ite (.nonzero .d .r3) decFail (decMain H G)) v' (Done Hs Gs s) :=
  WP.mono (chk_ok P hH.hD64 A) fun _ ⟨A', r3⟩ => ite_done hH hG hHh hHl hHv hGh hGl hGv P A' r3

theorem code_ok : WP isa (decrypt H G) s (Post Hs Gs s) := by
  refine WP.alloc (by decide) (by have := P.sp1; rw [stackBytes_eq] at this; unfold frameBytes; omega) ?_
  refine WP.seq (WP.mono (entry_ok P) fun t E => ?_)
  refine WP.seq (WP.mono (priv_ok P E) fun v A => ?_)
  refine WP.seq (WP.mono (checks_done hH hG hHh hHl hHv hGh hGl hGv P A) fun v' h => WP.seq (WP.mono h
    fun t' ⟨sv, res⟩ => WP.mono (restore_ok sv) fun w ⟨habi, h3, hm⟩ => ⟨habi, ?_⟩))
  rw [freed_mem, freed_gpr, hm, h3]
  exact res

end

section
variable {H G : Hash} (hH : HashOK H) (hG : HashOK G) {Hs Gs : Spec.Mgf1.Hash}
  (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = H.D) (hHv : Proof.Mgf1.Valid Hs)
  (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs)
include hH hG hHh hHl hHv hGh hGl hGv

/-- The correctness of `vg_rsa_oaep_<H>_mgf1_<G>_decrypt`, against its shared
contract. -/
theorem code_correct (s : State) (h : (Spec.RsaOaep.decryptContract Hs Gs abi stackBytes).pre s) :
    ∃ t s', Exec isa (decrypt H G) s t s' ∧ abiPreserved s s' ∧
      (Spec.RsaOaep.decryptContract Hs Gs abi stackBytes).post s s' := by
  have P : PreD s := preD_of h
  obtain ⟨t, s', he, habi, hr⟩ := code_ok hH hG hHh hHl hHv hGh hGl hGv P
  refine ⟨t, s', he, habi, ?_⟩
  have e : stackBytes = 3775 + 1 := rfl
  rw [e]
  sig_post [Spec.RsaOaep.decryptContract, Spec.RsaOaep.decryptSig, abi, argRegs, stackArgs_fifteen, List.append_eq]
  rw [Proof.RsaOaep.decrypt_eq (by rw [bytesAt_length, bytesAt_length])]
  exact hr

end

end VG.Proof.RsaOaep.PPC64LE.Dec
