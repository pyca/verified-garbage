module

public import VerifiedGarbage.Proof.RsaOaep.AArch64.Label
public import VerifiedGarbage.Proof.Dsa.Generation.WordFrame
public import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.Omega

/-! # Hash output bytes and preservation of the persistent generation frame -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Proof.RsaOaep.AArch64
open VG.Proof.Pbkdf2.Md.AArch64

theorem hash_bytes_frame {G : Impl.Pbkdf2.Md.AArch64.Hash} (hG : Calls.StreamOK G.stream)
    {Hs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hG.SH.H.hash x)
    (hsize : ∀ bytes, (Hs.hash bytes).length = G.D) {s : State} {F S rp : Addr} {len : Nat}
    (L : Lay s F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep s.mem F S V W) (A : LabAt s F S W rp len) :
    WP isa (hashLabel G oDig) s fun t =>
      Lay t F S ∧ Step F S [] s t ∧ Frame [⟨S, oRsa⟩, retR F] s.mem t.mem ∧
      ∃ V', Rep t.mem F S V' W ∧ (∀ x, ¬ inR (labR oDig) x → V' x = V x) ∧
        Spec.Rsa.bytesAt t.mem (off S oDig) G.D = Hs.hash (Spec.Rsa.bytesAt s.mem rp len) := by
  refine WP.mono (hashLabel_ok hG hHh L R A (Or.inl rfl))
    fun t ⟨Lt, step, V', Rt, hf, hb⟩ => ?_
  refine ⟨Lt, step, ?_, V', Rt, hf, ?_⟩
  · exact VG.Proof.Dsa.Generation.frame_without_words (count := nW) step.frame
      (fun k hk => (Rt.fr k hk).trans (R.fr k hk).symm)
  · have hd : G.D ≤ 64 := Nat.le_trans hG.hDF hG.hF
    apply List.ext_getElem
    · rw [VG.Proof.Bignum.bytesAt_length, hsize]
    · intro i hi hi'
      have hiD : i < G.D := by simpa only [VG.Proof.Bignum.bytesAt_length] using hi
      simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
      change t.mem (off S oDig + BitVec.ofNat 64 i) = _
      rw [show off S oDig + BitVec.ofNat 64 i = off S (oDig + i) by
        simp only [off, BitVec.ofNat_add, BitVec.add_assoc],
        Rt.scr _ (by unfold oDig oRsa; omega), hb i hiD]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
      rfl

end VG.Proof.Dsa.AArch64.Generation
