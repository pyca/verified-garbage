import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Regs
import VerifiedGarbage.Proof.Hmac.Common

/-!
# Deterministic ECDSA on 32-bit ARM: copying words

`copyN k src so dst d` copies the `4 k` bytes at `src + so` to `dst + d`, a
word at a time through `r0`, when the two ranges are apart: each word
written is the word read (`copyW_ok`), so the bytes written are the bytes
read (`copyN_ok`, by induction on the words). The model's `ldr` and `str`
take any address, as ARMv7's do, so the ranges need not be aligned.
-/

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Proof.X25519.Arm (wp_ldr wp_str)

/-- One word copied through `r0`. -/
theorem copyW_ok {u : State} {src dst : Reg} {S D : BitVec 32} (hs : u.gpr src = S) (hd : u.gpr dst = D)
    {so d : Nat} (hso : so < 4096) (hdo : d < 4096) {SA DA : Addr}
    (hSA : State.addr (S + BitVec.ofNat 32 so) = SA) (hDA : State.addr (D + BitVec.ofNat 32 d) = DA)
    (hr : InRegions (u.rd ++ u.wr) SA 4) (hw : InRegions u.wr DA 4) (hdr : dst ≠ .r0) :
    WP isa (.block [.ldr .r0 src so, .str .r0 dst d]) u fun u' =>
      u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧ (∀ r, r ≠ .r0 → u'.gpr r = u.gpr r) ∧
      u'.mem = u.mem.writeW DA (u.mem.readW SA 32) :=
  wp_ldr (a := SA) hso (by rw [hs]; exact hSA) hr fun s₁ u₁ =>
    wp_str (a := DA) hdo (by rw [u₁.other _ hdr, hd]; exact hDA) (by rw [u₁.wr]; exact hw) fun s₂ m₂ =>
      WP.block_nil ⟨by rw [m₂.rd, u₁.rd], by rw [m₂.wr, u₁.wr], by rw [m₂.sp, u₁.sp],
        fun r hr => by rw [m₂.gpr, u₁.other _ hr], by rw [m₂.mem, u₁.mem, u₁.gpr]⟩

theorem bytesAt_copied (m : Mem) (D S : Addr) :
    Spec.Sha256.bytesAt (m.writeW D (m.readW S 32)) D 4 = Spec.Sha256.bytesAt m S 4 := by
  rw [show (32 : Nat) = 8 * 4 from rfl, Proof.Hmac.Common.writeW_readW]
  have := Proof.Hmac.Common.bytesAt_writeBytes_self m D (Spec.Sha256.bytesAt m S 4) (by simp [Spec.Sha256.bytesAt])
  rwa [Proof.Hmac.Common.bytesAt_length] at this

theorem copyN_ok {src dst : Reg} {S D : BitVec 32} {so d K : Nat} (hdr : dst ≠ .r0) (hsr : src ≠ .r0)
    (hsep : Region.Disjoint ⟨State.addr S + BitVec.ofNat 64 so, 4 * K⟩ ⟨State.addr D + BitVec.ofNat 64 d, 4 * K⟩)
    (hsn : S.toNat + so + 4 * K ≤ 2 ^ 32) (hdn : D.toNat + d + 4 * K ≤ 2 ^ 32) (hso : so + 4 * K ≤ 4096)
    (hdo : d + 4 * K ≤ 4096) :
    ∀ k ≤ K, ∀ u : State, u.gpr src = S → u.gpr dst = D →
      (∀ j < K, InRegions (u.rd ++ u.wr) (State.addr S + BitVec.ofNat 64 (so + 4 * j)) 4) →
      (∀ j < K, InRegions u.wr (State.addr D + BitVec.ofNat 64 (d + 4 * j)) 4) →
      WP isa (.block (Cfg.copyN k src so dst d)) u fun u' =>
        u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧ (∀ r, r ≠ .r0 → u'.gpr r = u.gpr r) ∧
        Frame [⟨State.addr D + BitVec.ofNat 64 d, 4 * K⟩] u.mem u'.mem ∧
        Spec.Sha256.bytesAt u'.mem (State.addr D + BitVec.ofNat 64 d) (4 * k) =
          Spec.Sha256.bytesAt u.mem (State.addr S + BitVec.ofNat 64 so) (4 * k)
  | 0, _, u, _, _, _, _ => WP.block_nil ⟨rfl, rfl, rfl, fun _ _ => rfl, Frame.refl _ _, rfl⟩
  | k + 1, hk, u, hs, hd, hr, hw => by
    rw [Cfg.copyN, List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (copyN_ok hdr hsr hsep hsn hdn hso hdo k (by omega) u hs hd hr hw)
      fun u₁ ⟨hrd₁, hwr₁, hsp₁, hg₁, hf₁, hb₁⟩ => ?_
    refine WP.mono (copyW_ok (u := u₁) (hg₁ _ hsr ▸ hs) (hg₁ _ hdr ▸ hd) (by omega) (by omega)
      (addr_add (by omega)) (addr_add (by omega)) (hrd₁ ▸ hwr₁ ▸ hr k (by omega)) (hwr₁ ▸ hw k (by omega)) hdr)
      fun u₂ ⟨hrd₂, hwr₂, hsp₂, hg₂, hm₂⟩ => ?_
    -- The word written, within the destination.
    have hsub : Region.Sub ⟨State.addr D + BitVec.ofNat 64 (d + 4 * k), 4⟩
        ⟨State.addr D + BitVec.ofNat 64 d, 4 * K⟩ :=
      Offset.sub _ (by omega) (by omega)
    have hf₂ : Frame [⟨State.addr D + BitVec.ofNat 64 (d + 4 * k), 4⟩] u₁.mem u₂.mem := by
      rw [hm₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Offset.contains _ (Nat.le_refl _) (by omega) (by omega))
    -- The word read, unchanged by the earlier words.
    have hsrc : Spec.Sha256.bytesAt u₁.mem (State.addr S + BitVec.ofNat 64 (so + 4 * k)) 4 =
        Spec.Sha256.bytesAt u.mem (State.addr S + BitVec.ofNat 64 (so + 4 * k)) 4 :=
      bytesAt_frame hf₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hsep.sub_left (Offset.sub _ (by omega) (by omega))) (by omega)
    refine ⟨hrd₂.trans hrd₁, hwr₂.trans hwr₁, hsp₂.trans hsp₁, fun r hr => (hg₂ r hr).trans (hg₁ r hr),
      hf₁.trans (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact hsub⟩), ?_⟩
    rw [show 4 * (k + 1) = 4 * k + 4 by omega, Proof.Hmac.Common.bytesAt_add, Proof.Hmac.Common.bytesAt_add,
      Offset.add_add, Offset.add_add, ← hsrc]
    refine congrArg₂ (· ++ ·) ?_ ?_
    · rw [← hb₁]
      exact bytesAt_frame hf₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega)
    · rw [hm₂]
      exact bytesAt_copied _ _ _

end VG.Proof.Ecdsa.Rfc6979.Arm
