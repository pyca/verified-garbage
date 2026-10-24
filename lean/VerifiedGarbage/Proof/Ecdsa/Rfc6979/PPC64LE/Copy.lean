module

import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Hmac
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.PPC64LE
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Calls
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Layout
public import VerifiedGarbage.Proof.Mont.PPC64LE.Words
public import VerifiedGarbage.Spec.Sha256
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Step

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

/-- One byte copied through `r8`. -/
theorem cpb_ok {u : State} {src dst : Reg} {S D : Addr} (hs : u.gpr src = S) (hd : u.gpr dst = D)
    (hsr : src ≠ .r0) (hdr : dst ≠ .r0) (hd8 : dst ≠ .r8) {so d k : Nat} (hso : so + k < 2 ^ 15)
    (hdo : d + k < 2 ^ 15)
    (hr : InRegions (u.rd ++ u.wr) (S + BitVec.ofNat 64 (so + k)) 1)
    (hw : InRegions u.wr (D + BitVec.ofNat 64 (d + k)) 1) :
    WP isa (.block (Cfg.cpb src so dst d k)) u fun u' => Kp [.r8] u u' ∧
      u'.mem = u.mem.writeW (D + BitVec.ofNat 64 (d + k)) (u.mem.readW (S + BitVec.ofNat 64 (so + k)) 8) := by
  refine stepLbz hsr hso (by rw [hs]) hr fun u₁ k₁ m₁ v₁ => ?_
  refine stepStb hdr hdo (by rw [k₁.gpr _ (by simp [hd8]), hd]) (by rw [k₁.wr]; exact hw)
    fun u₂ k₂ g₂ m₂ => wp_nil ⟨k₁.trans k₂.mono, ?_⟩
  rw [m₂, v₁, m₁]
  congr 1
  exact BitVec.setWidth_setWidth_of_le _ (by decide) |>.trans (BitVec.setWidth_eq _)

theorem bytesAt_byteCopied (m : Mem) (D S : Addr) :
    Spec.Sha256.bytesAt (m.writeW D (m.readW S 8)) D 1 = Spec.Sha256.bytesAt m S 1 := by
  rw [show (8 : Nat) = 8 * 1 from rfl, Proof.Hmac.Common.writeW_readW]
  have := Proof.Hmac.Common.bytesAt_writeBytes_self m D (Spec.Sha256.bytesAt m S 1) (by simp [Spec.Sha256.bytesAt])
  rwa [Proof.Hmac.Common.bytesAt_length] at this

/-- Bytes `b`, `b + 1`, … copied one at a time. -/
theorem copyB_ok {src dst : Reg} {S D : Addr} {so d b K : Nat} (hsr : src ≠ .r0) (hdr : dst ≠ .r0)
    (hd8 : dst ≠ .r8) (hs8 : src ≠ .r8)
    (hsep : Region.Disjoint ⟨S + BitVec.ofNat 64 (so + b), K⟩ ⟨D + BitVec.ofNat 64 (d + b), K⟩)
    (hdn : d + b + K < 2 ^ 64) (hso : so + b + K < 2 ^ 15) (hdo : d + b + K < 2 ^ 15) :
    ∀ k ≤ K, ∀ u : State, u.gpr src = S → u.gpr dst = D →
      (∀ j < K, InRegions (u.rd ++ u.wr) (S + BitVec.ofNat 64 (so + (b + j))) 1) →
      (∀ j < K, InRegions u.wr (D + BitVec.ofNat 64 (d + (b + j))) 1) →
      WP isa (.block ((List.range k).flatMap fun j => Cfg.cpb src so dst d (b + j))) u fun u' =>
        Kp [.r8] u u' ∧ Frame [⟨D + BitVec.ofNat 64 (d + b), K⟩] u.mem u'.mem ∧
        Spec.Sha256.bytesAt u'.mem (D + BitVec.ofNat 64 (d + b)) k =
          Spec.Sha256.bytesAt u.mem (S + BitVec.ofNat 64 (so + b)) k
  | 0, _, u, _, _, _, _ => wp_nil ⟨Kp.refl _ _, Frame.refl _ _, rfl⟩
  | k + 1, hk, u, hs, hd, hr, hw => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (copyB_ok hsr hdr hd8 hs8 hsep hdn hso hdo k (by omega) u hs hd hr hw)
      fun u₁ ⟨k₁, hf₁, hb₁⟩ => ?_
    refine WP.mono (cpb_ok (u := u₁) (S := S) (D := D) (k := b + k) (by rw [k₁.gpr _ (by simp [hs8]), hs])
      (by rw [k₁.gpr _ (by simp [hd8]), hd]) hsr hdr hd8 (by omega) (by omega)
      (by rw [k₁.rd, k₁.wr]; exact hr k (by omega)) (by rw [k₁.wr]; exact hw k (by omega)))
      fun u₂ ⟨k₂, hm₂⟩ => ?_
    have hsub : Region.Sub ⟨D + BitVec.ofNat 64 (d + (b + k)), 1⟩ ⟨D + BitVec.ofNat 64 (d + b), K⟩ :=
      Offset.sub _ (by omega) (by omega)
    have hf₂ : Frame [⟨D + BitVec.ofNat 64 (d + (b + k)), 1⟩] u₁.mem u₂.mem := by
      rw [hm₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Offset.contains _ (Nat.le_refl _) (by omega) (by omega))
    have hsrc : Spec.Sha256.bytesAt u₁.mem (S + BitVec.ofNat 64 (so + (b + k))) 1 =
        Spec.Sha256.bytesAt u.mem (S + BitVec.ofNat 64 (so + (b + k))) 1 :=
      bytesAt_frame hf₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hsep.sub_left (Offset.sub _ (by omega) (by omega))) (by omega)
    refine ⟨k₁.trans k₂, hf₁.trans (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact hsub⟩), ?_⟩
    rw [Proof.Hmac.Common.bytesAt_add, Proof.Hmac.Common.bytesAt_add, Offset.add_add, Offset.add_add,
      show d + b + k = d + (b + k) by omega, show so + b + k = so + (b + k) by omega, ← hsrc]
    congr 1
    · rw [← hb₁]
      exact bytesAt_frame hf₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega)
    · rw [hm₂]; exact bytesAt_byteCopied _ _ _

/-- `n` bytes copied: 32-bit words, then the last `n % 4` bytes one at a time. -/
theorem copyN_ok {src dst : Reg} {S D : Addr} {so d n : Nat} (hsr : src ≠ .r0) (hdr : dst ≠ .r0)
    (hd8 : dst ≠ .r8) (hs8 : src ≠ .r8)
    (hsep : Region.Disjoint ⟨S + BitVec.ofNat 64 so, n⟩ ⟨D + BitVec.ofNat 64 d, n⟩)
    (hso : so + n < 2 ^ 15) (hdo : d + n < 2 ^ 15) (u : State) (hs : u.gpr src = S)
    (hd : u.gpr dst = D)
    (hr : ∀ j k, j + k ≤ n → InRegions (u.rd ++ u.wr) (S + BitVec.ofNat 64 (so + j)) k)
    (hw : ∀ j k, j + k ≤ n → InRegions u.wr (D + BitVec.ofNat 64 (d + j)) k) :
    WP isa (.block (Cfg.copyN n src so dst d)) u fun u' =>
      Kp [.r8] u u' ∧ Frame [⟨D + BitVec.ofNat 64 d, n⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (D + BitVec.ofNat 64 d) n = Spec.Sha256.bytesAt u.mem (S + BitVec.ofNat 64 so) n := by
  rw [Cfg.copyN, WP.block_append_iff]
  have h4 : 4 * (n / 4) ≤ n := Nat.mul_div_le n 4
  have h4' : 4 * (n / 4) + n % 4 = n := Nat.div_add_mod n 4
  refine WP.mono (copyW_ok (K := n / 4) hsr hdr hd8 hs8
    ((hsep.sub_left (Region.sub_prefix h4)).sub_right (Region.sub_prefix h4)) (by omega) (by omega) (by omega)
    (n / 4) (Nat.le_refl _) u hs hd (fun j hj => hr _ _ (by omega)) (fun j hj => hw _ _ (by omega)))
    fun u₁ ⟨k₁, f₁, v₁⟩ => ?_
  refine WP.mono (copyB_ok (b := 4 * (n / 4)) (K := n % 4) hsr hdr hd8 hs8
    ((hsep.sub_left (Offset.sub _ (by omega) (by omega))).sub_right (Offset.sub _ (by omega) (by omega)))
    (by omega) (by omega) (by omega) (n % 4) (Nat.le_refl _) u₁
    (by rw [k₁.gpr _ (by simp [hs8]), hs]) (by rw [k₁.gpr _ (by simp [hd8]), hd])
    (fun j hj => by rw [k₁.rd, k₁.wr]; exact hr _ _ (by omega))
    (fun j hj => by rw [k₁.wr]; exact hw _ _ (by omega)))
    fun u₂ ⟨k₂, f₂, v₂⟩ => ⟨k₁.trans k₂, ?_, ?_⟩
  · exact (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix h4⟩).trans
      (f₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega) (by omega)⟩)
  · rw [← h4', Proof.Hmac.Common.bytesAt_add, Proof.Hmac.Common.bytesAt_add, Offset.add_add, Offset.add_add, v₂]
    congr 1
    · rw [← v₁]
      exact bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega)
    · exact bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hsep.sub_left (Offset.sub _ (by omega) (by omega))).sub_right (Region.sub_prefix h4)) (by omega)

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
