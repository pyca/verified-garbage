import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Regs
import VerifiedGarbage.Proof.Hmac.Common

/-!
# Deterministic ECDSA on x86 (32-bit): copying words

`copyN k src so dst d` copies the `4 k` bytes at `src + so` to `dst + d`, a
word at a time through `eax`, when the two ranges are apart: each word
written is the word read (`copyW_ok`), so the bytes written are the bytes
read (`copyN_ok`, by induction on the words). The addresses the code
computes from `src` and `dst` are those of ranges at `SA` and `DA`.
`copyBytes Q` copies `Q ≥ 4` bytes: the whole words, then the last four bytes
again (`copyBytes_ok`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Ecdsa.Rfc6979.X86
open VG.Impl.Pbkdf2.Stream.X86 (at_)

/-- One word copied through `eax`. -/
theorem copyW_ok {u : State} {src dst : Reg} {S D : BitVec 32} (hs : u.gpr src = S) (hd : u.gpr dst = D)
    {so d : Nat} (hr : InRegions (u.rd ++ u.wr) (addr S so) 4) (hw : InRegions u.wr (addr D d) 4)
    (hdr : dst ≠ .eax) :
    WP isa (.block [.mov .eax (.mem (at_ src so)), .store (at_ dst d) .eax]) u fun u' =>
      u'.rd = u.rd ∧ u'.wr = u.wr ∧ (∀ r, r ≠ .eax → u'.gpr r = u.gpr r) ∧
      u'.mem = u.mem.writeW (addr D d) (u.mem.readW (addr S so) 32) :=
  wp_ldm hs hr fun u₁ v₁ => wp_stm (B := D) (by rw [v₁.other _ hdr, hd]) (by rw [v₁.wr]; exact hw)
    fun u₂ v₂ => WP.block_nil ⟨by rw [v₂.rd, v₁.rd], by rw [v₂.wr, v₁.wr],
      fun r hr => by rw [v₂.gpr, v₁.other _ hr], by rw [v₂.mem, v₁.gpr, v₁.mem]⟩

theorem bytesAt_copied (m : Mem) (D S : Addr) :
    Spec.Sha256.bytesAt (m.writeW D (m.readW S 32)) D 4 = Spec.Sha256.bytesAt m S 4 := by
  rw [show (32 : Nat) = 8 * 4 from rfl, Proof.Hmac.Common.writeW_readW]
  have := Proof.Hmac.Common.bytesAt_writeBytes_self m D (Spec.Sha256.bytesAt m S 4) (by simp [Spec.Sha256.bytesAt])
  rwa [Proof.Hmac.Common.bytesAt_length] at this

theorem copyN_ok {src dst : Reg} {S D : BitVec 32} {SA DA : Addr} {so d K : Nat} (hdr : dst ≠ .eax)
    (hsr : src ≠ .eax) (hSA : ∀ j < K, addr S (so + 4 * j) = SA + BitVec.ofNat 64 (4 * j))
    (hDA : ∀ j < K, addr D (d + 4 * j) = DA + BitVec.ofNat 64 (4 * j))
    (hsep : Region.Disjoint ⟨SA, 4 * K⟩ ⟨DA, 4 * K⟩) (hK : 4 * K < 2 ^ 32) :
    ∀ k ≤ K, ∀ u : State, u.gpr src = S → u.gpr dst = D →
      (∀ j < K, InRegions (u.rd ++ u.wr) (SA + BitVec.ofNat 64 (4 * j)) 4) →
      (∀ j < K, InRegions u.wr (DA + BitVec.ofNat 64 (4 * j)) 4) →
      WP isa (.block (Cfg.copyN k src so dst d)) u fun u' =>
        u'.rd = u.rd ∧ u'.wr = u.wr ∧ (∀ r, r ≠ .eax → u'.gpr r = u.gpr r) ∧
        Frame [⟨DA, 4 * K⟩] u.mem u'.mem ∧
        Spec.Sha256.bytesAt u'.mem DA (4 * k) = Spec.Sha256.bytesAt u.mem SA (4 * k)
  | 0, _, u, _, _, _, _ => WP.of_runBlock ⟨u, rfl, rfl, rfl, fun _ _ => rfl, Frame.refl _ _, rfl⟩
  | k + 1, hk, u, hs, hd, hr, hw => by
    rw [Cfg.copyN, List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (copyN_ok hdr hsr hSA hDA hsep hK k (by omega) u hs hd hr hw)
      fun u₁ ⟨hrd₁, hwr₁, hg₁, hf₁, hb₁⟩ => ?_
    refine WP.mono (copyW_ok (u := u₁) (so := so + 4 * k) (d := d + 4 * k) (hg₁ _ hsr ▸ hs) (hg₁ _ hdr ▸ hd)
      (by rw [hSA k (by omega), hrd₁, hwr₁]; exact hr k (by omega))
      (by rw [hDA k (by omega), hwr₁]; exact hw k (by omega)) hdr) fun u₂ ⟨hrd₂, hwr₂, hg₂, hm₂⟩ => ?_
    rw [hSA k (by omega), hDA k (by omega)] at hm₂
    -- The word written, within the destination.
    have hsub : Region.Sub ⟨DA + BitVec.ofNat 64 (4 * k), 4⟩ ⟨DA, 4 * K⟩ := Offset.sub_base _ (by omega)
    have hf₂ : Frame [⟨DA + BitVec.ofNat 64 (4 * k), 4⟩] u₁.mem u₂.mem := by
      rw [hm₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    -- The word read, unchanged by the earlier words.
    have hsrc : Spec.Sha256.bytesAt u₁.mem (SA + BitVec.ofNat 64 (4 * k)) 4 =
        Spec.Sha256.bytesAt u.mem (SA + BitVec.ofNat 64 (4 * k)) 4 :=
      bytesAt_frame hf₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hsep.sub_left (Offset.sub_base _ (by omega))) (by omega)
    refine ⟨hrd₂.trans hrd₁, hwr₂.trans hwr₁, fun r hr => (hg₂ r hr).trans (hg₁ r hr),
      hf₁.trans (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact hsub⟩), ?_⟩
    rw [show 4 * (k + 1) = 4 * k + 4 by omega, Proof.Hmac.Common.bytesAt_add, Proof.Hmac.Common.bytesAt_add,
      ← hsrc]
    congr 1
    · rw [← hb₁]
      exact bytesAt_frame hf₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.base_disjoint _ (by omega) (by omega)) (by omega)
    · rw [hm₂]; exact bytesAt_copied _ _ _

/-- The first `n` of `k` bytes. -/
theorem bytesAt_take (m : Mem) (p : Addr) {n k : Nat} (h : n ≤ k) :
    Spec.Sha256.bytesAt m p n = (Spec.Sha256.bytesAt m p k).take n := by
  rw [show k = n + (k - n) by omega, Proof.Hmac.Common.bytesAt_add, List.take_left']
  simp [Spec.Sha256.bytesAt]

theorem copyBytes_ok {src dst : Reg} {S D : BitVec 32} {SA DA : Addr} {so d Q : Nat} (hdr : dst ≠ .eax)
    (hsr : src ≠ .eax) (hSA : ∀ j, j + 4 ≤ Q → addr S (so + j) = SA + BitVec.ofNat 64 j)
    (hDA : ∀ j, j + 4 ≤ Q → addr D (d + j) = DA + BitVec.ofNat 64 j)
    (hsep : Region.Disjoint ⟨SA, Q⟩ ⟨DA, Q⟩) (h4 : 4 ≤ Q) (hQ : Q < 2 ^ 32) {u : State}
    (hs : u.gpr src = S) (hd : u.gpr dst = D)
    (hr : ∀ j, j + 4 ≤ Q → InRegions (u.rd ++ u.wr) (SA + BitVec.ofNat 64 j) 4)
    (hw : ∀ j, j + 4 ≤ Q → InRegions u.wr (DA + BitVec.ofNat 64 j) 4) :
    WP isa (.block (Cfg.copyBytes Q src so dst d)) u fun u' =>
      u'.rd = u.rd ∧ u'.wr = u.wr ∧ (∀ r, r ≠ .eax → u'.gpr r = u.gpr r) ∧
      Frame [⟨DA, Q⟩] u.mem u'.mem ∧ Spec.Sha256.bytesAt u'.mem DA Q = Spec.Sha256.bytesAt u.mem SA Q := by
  rw [Cfg.copyBytes, WP.block_append_iff]
  have hK : 4 * (Q / 4) ≤ Q := Nat.mul_div_le Q 4
  refine WP.mono (copyN_ok (S := S) (D := D) (SA := SA) (DA := DA) (so := so) (d := d) (K := Q / 4) hdr hsr
      (fun j hj => hSA (4 * j) (by omega)) (fun j hj => hDA (4 * j) (by omega))
      ((hsep.sub_left (Region.sub_prefix (by omega))).sub_right (Region.sub_prefix (by omega))) (by omega)
      (Q / 4) (Nat.le_refl _) u hs hd
      (fun j hj => hr (4 * j) (by omega)) fun j hj => hw (4 * j) (by omega))
    fun u₁ ⟨hrd₁, hwr₁, hg₁, hf₁, hb₁⟩ => ?_
  have hf₁' : Frame [⟨DA, Q⟩] u.mem u₁.mem :=
    hf₁.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega)⟩
  by_cases hm : Q % 4 = 0
  · simp only [hm, ite_true]
    have e : 4 * (Q / 4) = Q := by omega
    rw [e] at hb₁
    exact WP.block_nil ⟨hrd₁, hwr₁, hg₁, hf₁', hb₁⟩
  · simp only [hm, ite_false]
    have eS : addr S (so + Q - 4) = SA + BitVec.ofNat 64 (Q - 4) := by
      rw [show so + Q - 4 = so + (Q - 4) by omega]; exact hSA (Q - 4) (by omega)
    have eD : addr D (d + Q - 4) = DA + BitVec.ofNat 64 (Q - 4) := by
      rw [show d + Q - 4 = d + (Q - 4) by omega]; exact hDA (Q - 4) (by omega)
    refine WP.mono (copyW_ok (u := u₁) (so := so + Q - 4) (d := d + Q - 4) (hg₁ _ hsr ▸ hs) (hg₁ _ hdr ▸ hd)
      (by rw [eS, hrd₁, hwr₁]; exact hr (Q - 4) (by omega)) (by rw [eD, hwr₁]; exact hw (Q - 4) (by omega)) hdr)
      fun u₂ ⟨hrd₂, hwr₂, hg₂, hm₂⟩ => ?_
    rw [eS, eD] at hm₂
    have hf₂ : Frame [⟨DA + BitVec.ofNat 64 (Q - 4), 4⟩] u₁.mem u₂.mem := by
      rw [hm₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    refine ⟨hrd₂.trans hrd₁, hwr₂.trans hwr₁, fun r hr => (hg₂ r hr).trans (hg₁ r hr),
      hf₁'.trans (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base _ (by omega)⟩), ?_⟩
    rw [show Q = (Q - 4) + 4 by omega, Proof.Hmac.Common.bytesAt_add, Proof.Hmac.Common.bytesAt_add]
    congr 1
    · rw [bytesAt_frame hf₂ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.base_disjoint _ (by omega) (by omega)) (by omega),
        bytesAt_take _ _ (k := 4 * (Q / 4)) (by omega), hb₁, ← bytesAt_take _ _ (by omega)]
    · rw [hm₂, bytesAt_copied]
      exact bytesAt_frame hf₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hsep.sub_left (Offset.sub_base _ (by omega))).sub_right (Region.sub_prefix (by omega)))
        (by omega)

end VG.Proof.Ecdsa.Rfc6979.X86
