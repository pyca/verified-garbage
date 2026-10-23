module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Hmac
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Deterministic ECDSA on PPC64LE: copying words

`copyW k src so dst d` copies the `4 k` bytes at `src + so` to `dst + d`, a
32-bit word at a time through `r8`, when the two ranges are apart: each word
written is the word read (`cpw_ok`), so the bytes written are the bytes read
(`copyW_ok`, by induction on the words).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE VG.Impl.Ecdsa.Rfc6979.PPC64LE
open VG.Proof.Mont.PPC64LE (Kp)

/-- One word copied through `r8`. -/
theorem cpw_ok {u : State} {src dst : Reg} {S D : Addr} (hs : u.gpr src = S) (hd : u.gpr dst = D)
    (hsr : src ≠ .r0) (hdr : dst ≠ .r0) (hd8 : dst ≠ .r8) {so d k : Nat} (hso : so + 4 * k < 2 ^ 15)
    (hdo : d + 4 * k < 2 ^ 15)
    (hr : InRegions (u.rd ++ u.wr) (S + BitVec.ofNat 64 (so + 4 * k)) 4)
    (hw : InRegions u.wr (D + BitVec.ofNat 64 (d + 4 * k)) 4) :
    WP isa (.block (Cfg.cpw src so dst d k)) u fun u' => Kp [.r8] u u' ∧
      u'.mem = u.mem.writeW (D + BitVec.ofNat 64 (d + 4 * k)) (u.mem.readW (S + BitVec.ofNat 64 (so + 4 * k)) 32) := by
  refine stepLwz hsr hso (by rw [hs]) hr fun u₁ k₁ m₁ v₁ => ?_
  refine stepStw hdr hdo (by rw [k₁.gpr _ (by simp [hd8]), hd]) (by rw [k₁.wr]; exact hw)
    fun u₂ k₂ g₂ m₂ => wp_nil ⟨k₁.trans k₂.mono, ?_⟩
  rw [m₂, v₁, m₁]
  congr 1
  exact BitVec.setWidth_setWidth_of_le _ (by decide) |>.trans (BitVec.setWidth_eq _)

theorem bytesAt_copied (m : Mem) (D S : Addr) :
    Spec.Sha256.bytesAt (m.writeW D (m.readW S 32)) D 4 = Spec.Sha256.bytesAt m S 4 := by
  rw [show (32 : Nat) = 8 * 4 from rfl, Proof.Hmac.Common.writeW_readW]
  have := Proof.Hmac.Common.bytesAt_writeBytes_self m D (Spec.Sha256.bytesAt m S 4) (by simp [Spec.Sha256.bytesAt])
  rwa [Proof.Hmac.Common.bytesAt_length] at this

theorem copyW_ok {src dst : Reg} {S D : Addr} {so d K : Nat} (hsr : src ≠ .r0) (hdr : dst ≠ .r0)
    (hd8 : dst ≠ .r8) (hs8 : src ≠ .r8)
    (hsep : Region.Disjoint ⟨S + BitVec.ofNat 64 so, 4 * K⟩ ⟨D + BitVec.ofNat 64 d, 4 * K⟩)
    (hdn : d + 4 * K < 2 ^ 64) (hso : so + 4 * K < 2 ^ 15) (hdo : d + 4 * K < 2 ^ 15) :
    ∀ k ≤ K, ∀ u : State, u.gpr src = S → u.gpr dst = D →
      (∀ j < K, InRegions (u.rd ++ u.wr) (S + BitVec.ofNat 64 (so + 4 * j)) 4) →
      (∀ j < K, InRegions u.wr (D + BitVec.ofNat 64 (d + 4 * j)) 4) →
      WP isa (.block (Cfg.copyW k src so dst d)) u fun u' =>
        Kp [.r8] u u' ∧ Frame [⟨D + BitVec.ofNat 64 d, 4 * K⟩] u.mem u'.mem ∧
        Spec.Sha256.bytesAt u'.mem (D + BitVec.ofNat 64 d) (4 * k) =
          Spec.Sha256.bytesAt u.mem (S + BitVec.ofNat 64 so) (4 * k)
  | 0, _, u, _, _, _, _ => wp_nil ⟨Kp.refl _ _, Frame.refl _ _, rfl⟩
  | k + 1, hk, u, hs, hd, hr, hw => by
    rw [Cfg.copyW, List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (copyW_ok hsr hdr hd8 hs8 hsep hdn hso hdo k (by omega) u hs hd hr hw)
      fun u₁ ⟨k₁, hf₁, hb₁⟩ => ?_
    refine WP.mono (cpw_ok (u := u₁) (S := S) (D := D) (k := k) (by rw [k₁.gpr _ (by simp [hs8]), hs])
      (by rw [k₁.gpr _ (by simp [hd8]), hd]) hsr hdr hd8 (by omega) (by omega)
      (by rw [k₁.rd, k₁.wr]; exact hr k (by omega)) (by rw [k₁.wr]; exact hw k (by omega)))
      fun u₂ ⟨k₂, hm₂⟩ => ?_
    -- The word written, within the destination.
    have hsub : Region.Sub ⟨D + BitVec.ofNat 64 (d + 4 * k), 4⟩ ⟨D + BitVec.ofNat 64 d, 4 * K⟩ :=
      Offset.sub _ (by omega) (by omega)
    have hf₂ : Frame [⟨D + BitVec.ofNat 64 (d + 4 * k), 4⟩] u₁.mem u₂.mem := by
      rw [hm₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Offset.contains _ (Nat.le_refl _) (by omega) (by omega))
    -- The word read, unchanged by the earlier words.
    have hsrc : Spec.Sha256.bytesAt u₁.mem (S + BitVec.ofNat 64 (so + 4 * k)) 4 =
        Spec.Sha256.bytesAt u.mem (S + BitVec.ofNat 64 (so + 4 * k)) 4 :=
      bytesAt_frame hf₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hsep.sub_left (Offset.sub _ (by omega) (by omega))) (by omega)
    refine ⟨k₁.trans k₂, hf₁.trans (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact hsub⟩), ?_⟩
    rw [show 4 * (k + 1) = 4 * k + 4 by omega, Proof.Hmac.Common.bytesAt_add, Proof.Hmac.Common.bytesAt_add,
      Offset.add_add, Offset.add_add, ← hsrc]
    congr 1
    · rw [← hb₁]
      exact bytesAt_frame hf₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega)
    · rw [hm₂]; exact bytesAt_copied _ _ _

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
