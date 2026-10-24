module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Tag
public import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
import VerifiedGarbage.Proof.AesGcm.PPC64LE.TextAbsorb
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.AesGcm.PPC64LE

/-!
# AES-GCM on PPC64LE: the tag after the last piece (`finTag o`)

Untrusted: everything here is checked by Lean. As on ARMv7
(`Proof/AesGcm/Arm/FinTag.lean`): `finTag o` pads and absorbs the buffered
bytes (`flush`), of the text if there is any and else of the additional
data, then puts the tag into `W + o` (`tag`), for `aad_len` (`r22`) bytes
of additional data and `text_len` (`r23`) of text (`finTag_ok`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashInput ghash ghashFrom blocks zeros padLen toBytes ofBytes)
open VG.Proof.Gcm (Absorbed lensBlock padded)

/-- `tFrame` is within `tagFrame`. -/
theorem tFrame_sub {st w : Addr} {o : Nat} :
    ∀ r ∈ tFrame st w 16, ∃ r' ∈ tagFrame st w o, Region.Sub r r' := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., by simpa using Offset.sub_base st (show 16 + 16 ≤ 32 by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
  · exact ⟨⟨w + BitVec.ofNat 64 512, 2048⟩, by simp, Offset.sub _ (by decide) (by decide)⟩

theorem t_tagFrame {st w : Addr} {o : Nat} {m m' : Mem} (h : Frame (tFrame st w 16) m m') :
    Frame (tagFrame st w o) m m' := h.sub tFrame_sub

/-- After `finTag o`, from `m₀`. -/
structure FinOut (V : Reg → BitVec 64) (sp : Addr) (o R : Nat) (H : Block) (a ct : List Byte) (m₀ : Mem)
    (s : State) : Prop where
  env : Env V sp s
  out : Absorbed m₀ (V .r30 + BitVec.ofNat 64 16) (V .r30 + BitVec.ofNat 64 32) H (ghashInput a ct) →
    bytesAt s.mem (V .r31 + BitVec.ofNat 64 o) 16 =
      toBytes (ghashFrom H (ghash H (blocks (padded a ct))) [ofBytes (lensBlock (V .r22).toNat ct.length)]
        ^^^ ciphOf m₀ (V .r29) R (blockAt m₀ (V .r30)))
  frame : Frame (tagFrame (V .r30) (V .r31) o) m₀ s.mem

section
variable {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .r29) (V .r30) (V .r31))
include L

theorem finTag_ok {o R : Nat} (ho : o = 0 ∨ o = 112) {H : Block} {a ct : List Byte} {s : State}
    (he : Env V sp s) (h28 : V .r28 = BitVec.ofNat 64 R) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (hH : blockAt s.mem (V .r29 + BitVec.ofNat 64 240) = H)
    (ha : a.length % 16 = (V .r22).toNat % 16) (hP : (V .r23).toNat = ct.length) :
    WP isa (finTag o) s (FinOut V sp o R H a ct s.mem) := by
  have h22 := he.fr .r22 (by decide)
  have h23 := he.fr .r23 (by decide)
  -- `r26`: the length of the buffered bytes, modulo 16
  have mid : WP isa (.ite (.zero .d .r23) (.block [.li .r0 15, .logic .and .r26 .r22 .r0])
      (.block [.li .r0 15, .logic .and .r26 .r23 .r0])) s fun s₂ =>
      s₂.gpr .r26 = BitVec.ofNat 64 ((ghashInput a ct).length % 16) ∧
        (∀ r, r ≠ .r0 → r ≠ .r26 → s₂.gpr r = s.gpr r) ∧ Keeps s s₂ := by
    refine WP.ite _ (eval_zero (he.ofNat (r := .r23) (by decide)) (V .r23).isLt) (fun ht => ?_) (fun hf => ?_)
    · have hc : ct = [] := List.eq_nil_of_length_eq_zero (by rw [← hP]; simpa using ht)
      have e : (ghashInput a ct).length % 16 = (V .r22).toNat % 16 := by
        rw [hc, Proof.Gcm.ghashInput_nil, ha]
      have hand := and15 (V .r22)
      rw [e]
      crun [h22, hand]
      exact ⟨fun r a b => by simp [a, b], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
    · have hc : ct ≠ [] := fun e => by subst e; simp only [List.length_nil] at hP; simp [hP] at hf
      have e : (ghashInput a ct).length % 16 = (V .r23).toNat % 16 := by
        rw [Proof.Gcm.ghashInput_of_ne hc, List.length_append, List.length_append, Proof.Gcm.length_zeros, hP]
        have := Proof.Gcm.length_pad_mod a.length; omega
      have hand := and15 (V .r23)
      rw [e]
      crun [h23, hand]
      exact ⟨fun r a b => by simp [a, b], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  refine WP.seq (WP.mono mid fun s₂ ⟨h26₂, hg₂, hk₂⟩ => ?_)
  have he₂ := he.keep (fun r hr => hg₂ r (by revert r; decide) (by revert r; decide)) hk₂.sp hk₂.rd hk₂.wr
  refine WP.seq (WP.mono (flush_ok L (yo := 16) (.inr rfl) (x := ghashInput a ct) (H := H)
    ⟨he₂, by rw [hk₂.mem]; exact hH⟩ h26₂) fun s₄ hfl => ?_)
  have hf₄ := hfl.frame
  rw [hk₂.mem] at hf₄
  -- the lengths
  have h₅ : WP isa (.block [mov .r24 .r22, mov .r26 .r23]) s₄ fun s₅ =>
      s₅.gpr .r24 = V .r22 ∧ s₅.gpr .r26 = V .r23 ∧ (∀ r, r ≠ .r24 → r ≠ .r26 → s₅.gpr r = s₄.gpr r) ∧
        Keeps s₄ s₅ := by
    have e22 := hfl.env.fr .r22 (by decide)
    have e23 := hfl.env.fr .r23 (by decide)
    crun [mov, BitVec.or_self, e22, e23]
    exact ⟨fun r a b => by simp [a, b], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  refine WP.seq (WP.mono h₅ fun s₅ ⟨h24₅, h26₅, hg₅, hk₅⟩ => ?_)
  have he₅ := hfl.env.keep (fun r hr => hg₅ r (by revert r; decide) (by revert r; decide)) hk₅.sp hk₅.rd hk₅.wr
  refine WP.mono (tag_ok L ho he₅ h28 hR (H := H) (by rw [hk₅.mem]; exact hfl.hH) rfl) fun s₆ tg => ?_
  rw [h24₅, h26₅, hP, hk₅.mem] at tg
  refine ⟨tg.env, fun hab => ?_, (t_tagFrame hf₄).trans tg.frame⟩
  rw [tg.out]
  have hw := (hfl.abs (by rw [hk₂.mem]; exact hab)).whole_eq (by
    simp only [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _)
  rw [show ghashInput a ct ++ zeros (padLen (ghashInput a ct).length) = padded a ct from rfl] at hw
  rw [hw, ciph_frame hf₄ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.cs.sub_right (Lay.stSub (by decide))
      · exact L.cw'.sub_right (Lay.wSub (by decide))
      · exact L.cw'.sub_right (Lay.wSub (by decide))) hR,
    blockAt_frame hf₄ (j_tFrame L)]

end

end VG.Proof.AesGcm.PPC64LE
