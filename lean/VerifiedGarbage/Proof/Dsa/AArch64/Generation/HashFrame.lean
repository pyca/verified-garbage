module

public import VerifiedGarbage.Proof.RsaOaep.AArch64.Label
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Bignum.Words
meta import Lean.Elab.Tactic.Omega.Frontend
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `Dsa.Generation.WordFrame`, which only this module used -/

section

/-! # Unchanged frame words imply unchanged frame bytes -/

@[expose] public section
namespace VG.Proof.Dsa.Generation
open VG VG.Proof.Bignum

theorem words_preserve_byte {m m' : Mem} {B : Addr} {count i : Nat}
    (hw : ∀ k < count, m'.readW (off B (8 * k)) 64 = m.readW (off B (8 * k)) 64)
    (hi : i < 8 * count) : m' (off B i) = m (off B i) := by
  have he : off B (8 * (i / 8)) + BitVec.ofNat 64 (i % 8) = off B i := by
    simp only [off, BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [show 8 * (i / 8) + i % 8 = i by omega_using []]
  have h := congrArg (fun v : BitVec 64 => v.extractLsb' (8 * (i % 8)) 8)
    (hw (i / 8) (by omega_using [hi]))
  change (m'.read (off B (8 * (i / 8))) 8).extractLsb' (8 * (i % 8)) 8 =
    (m.read (off B (8 * (i / 8))) 8).extractLsb' (8 * (i % 8)) 8 at h
  rw [Mem.extractLsb'_read m' _ (by omega_using []), Mem.extractLsb'_read m _ (by omega_using []), he] at h
  exact h

theorem frame_without_words {m m' : Mem} {B : Addr} {count : Nat} {rs : List Region}
    (hf : Frame (⟨B, 8 * count⟩ :: rs) m m')
    (hw : ∀ k < count, m'.readW (off B (8 * k)) 64 = m.readW (off B (8 * k)) 64) :
    Frame rs m m' := by
  intro x hx
  by_cases hB : (⟨B, 8 * count⟩ : Region).Contains x 1
  · have hi : (x - B).toNat < 8 * count := by
      change (x - B).toNat + 1 ≤ 8 * count at hB
      omega_using [hB]
    have he : off B (x - B).toNat = x := by
      simp only [off, BitVec.ofNat_toNat]
      bv_omega
    simpa only [he] using words_preserve_byte hw hi
  · apply hf x
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hB
    · exact hx r hr

end VG.Proof.Dsa.Generation

end

end

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
        Rt.scr _ (by unfold oDig oRsa; omega_using [hd, hiD]), hb i hiD]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
      rfl

end VG.Proof.Dsa.AArch64.Generation
