import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Regs
import VerifiedGarbage.Proof.Hmac.Common

/-!
# Deterministic ECDSA on x86-64: copying words

`copyN k src so dst d` copies the `8 k` bytes at `src + so` to `dst + d`, a
word at a time through `rax`, when the two ranges are apart: each word
written is the word read (`copyW_ok`), so the bytes written are the bytes
read (`copyN_ok`, by induction on the words). `copyBytes Q` copies `Q ≥ 8`
bytes: the whole words, then the last eight bytes again (`copyBytes_ok`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64

/-- One word copied through `rax`. -/
theorem copyW_ok {u : State} {src dst : Reg} {S D : Addr} (hs : u.gpr src = S) (hd : u.gpr dst = D)
    {so d : Nat} (hr : InRegions (u.rd ++ u.wr) (S + BitVec.ofNat 64 so) 8)
    (hw : InRegions u.wr (D + BitVec.ofNat 64 d) 8) (hdr : dst ≠ .rax) :
    WP isa (.block [.mov .rax (.mem (at_ src so)), .store (at_ dst d) .rax]) u fun u' =>
      u'.rd = u.rd ∧ u'.wr = u.wr ∧ (∀ r, r ≠ .rax → u'.gpr r = u.gpr r) ∧
      u'.mem = u.mem.writeW (D + BitVec.ofNat 64 d) (u.mem.readW (S + BitVec.ofNat 64 so) 64) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, State.store64, ea_at, hs,
    RegUpd.gpr_setReg_of_ne _ _ hdr, hd, hr, ite_true, Option.map_some, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.mem_setReg, RegUpd.gpr_setReg_self, hw, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, trivial⟩

theorem bytesAt_copied (m : Mem) (D S : Addr) :
    Spec.Sha256.bytesAt (m.writeW D (m.readW S 64)) D 8 = Spec.Sha256.bytesAt m S 8 := by
  rw [show (64 : Nat) = 8 * 8 from rfl, Proof.Hmac.Common.writeW_readW]
  have := Proof.Hmac.Common.bytesAt_writeBytes_self m D (Spec.Sha256.bytesAt m S 8) (by simp [Spec.Sha256.bytesAt])
  rwa [Proof.Hmac.Common.bytesAt_length] at this

theorem copyN_ok {src dst : Reg} {S D : Addr} {so d K : Nat} (hdr : dst ≠ .rax) (hsr : src ≠ .rax)
    (hsep : Region.Disjoint ⟨S + BitVec.ofNat 64 so, 8 * K⟩ ⟨D + BitVec.ofNat 64 d, 8 * K⟩)
    (hdn : d + 8 * K < 2 ^ 64) :
    ∀ k ≤ K, ∀ u : State, u.gpr src = S → u.gpr dst = D →
      (∀ j < K, InRegions (u.rd ++ u.wr) (S + BitVec.ofNat 64 (so + 8 * j)) 8) →
      (∀ j < K, InRegions u.wr (D + BitVec.ofNat 64 (d + 8 * j)) 8) →
      WP isa (.block (Cfg.copyN k src so dst d)) u fun u' =>
        u'.rd = u.rd ∧ u'.wr = u.wr ∧ (∀ r, r ≠ .rax → u'.gpr r = u.gpr r) ∧
        Frame [⟨D + BitVec.ofNat 64 d, 8 * K⟩] u.mem u'.mem ∧
        Spec.Sha256.bytesAt u'.mem (D + BitVec.ofNat 64 d) (8 * k) =
          Spec.Sha256.bytesAt u.mem (S + BitVec.ofNat 64 so) (8 * k)
  | 0, _, u, _, _, _, _ => WP.of_runBlock ⟨u, rfl, rfl, rfl, fun _ _ => rfl, Frame.refl _ _, rfl⟩
  | k + 1, hk, u, hs, hd, hr, hw => by
    rw [Cfg.copyN, List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (copyN_ok hdr hsr hsep hdn k (by omega) u hs hd hr hw)
      fun u₁ ⟨hrd₁, hwr₁, hg₁, hf₁, hb₁⟩ => ?_
    refine WP.mono (copyW_ok (u := u₁) (hg₁ _ hsr ▸ hs) (hg₁ _ hdr ▸ hd) (hrd₁ ▸ hwr₁ ▸ hr k (by omega))
      (hwr₁ ▸ hw k (by omega)) hdr) fun u₂ ⟨hrd₂, hwr₂, hg₂, hm₂⟩ => ?_
    -- The word written, within the destination.
    have hsub : Region.Sub ⟨D + BitVec.ofNat 64 (d + 8 * k), 8⟩ ⟨D + BitVec.ofNat 64 d, 8 * K⟩ :=
      Offset.sub _ (by omega) (by omega)
    have hf₂ : Frame [⟨D + BitVec.ofNat 64 (d + 8 * k), 8⟩] u₁.mem u₂.mem := by
      rw [hm₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Offset.contains _ (Nat.le_refl _) (by omega) (by omega))
    -- The word read, unchanged by the earlier words.
    have hsrc : Spec.Sha256.bytesAt u₁.mem (S + BitVec.ofNat 64 (so + 8 * k)) 8 =
        Spec.Sha256.bytesAt u.mem (S + BitVec.ofNat 64 (so + 8 * k)) 8 :=
      bytesAt_frame hf₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hsep.sub_left (Offset.sub _ (by omega) (by omega))) (by omega)
    refine ⟨hrd₂.trans hrd₁, hwr₂.trans hwr₁, fun r hr => (hg₂ r hr).trans (hg₁ r hr),
      hf₁.trans (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact hsub⟩), ?_⟩
    rw [show 8 * (k + 1) = 8 * k + 8 by omega, Proof.Hmac.Common.bytesAt_add, Proof.Hmac.Common.bytesAt_add,
      Offset.add_add, Offset.add_add, ← hsrc]
    congr 1
    · rw [← hb₁]
      exact bytesAt_frame hf₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega)
    · rw [hm₂]; exact bytesAt_copied _ _ _

/-- The first `n` of `k` bytes. -/
theorem bytesAt_take (m : Mem) (p : Addr) {n k : Nat} (h : n ≤ k) :
    Spec.Sha256.bytesAt m p n = (Spec.Sha256.bytesAt m p k).take n := by
  rw [show k = n + (k - n) by omega, Proof.Hmac.Common.bytesAt_add, List.take_left']
  simp [Spec.Sha256.bytesAt]

theorem copyBytes_ok {src dst : Reg} {S D : Addr} {so d Q : Nat} (hdr : dst ≠ .rax) (hsr : src ≠ .rax)
    (hsep : Region.Disjoint ⟨S + BitVec.ofNat 64 so, Q⟩ ⟨D + BitVec.ofNat 64 d, Q⟩) (h8 : 8 ≤ Q)
    (hso : so + Q < 2 ^ 64) (hdn : d + Q < 2 ^ 64) {u : State} (hs : u.gpr src = S) (hd : u.gpr dst = D)
    (hr : ∀ j, j + 8 ≤ Q → InRegions (u.rd ++ u.wr) (S + BitVec.ofNat 64 (so + j)) 8)
    (hw : ∀ j, j + 8 ≤ Q → InRegions u.wr (D + BitVec.ofNat 64 (d + j)) 8) :
    WP isa (.block (Cfg.copyBytes Q src so dst d)) u fun u' =>
      u'.rd = u.rd ∧ u'.wr = u.wr ∧ (∀ r, r ≠ .rax → u'.gpr r = u.gpr r) ∧
      Frame [⟨D + BitVec.ofNat 64 d, Q⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (D + BitVec.ofNat 64 d) Q = Spec.Sha256.bytesAt u.mem (S + BitVec.ofNat 64 so) Q := by
  rw [Cfg.copyBytes, WP.block_append_iff]
  have hK : 8 * (Q / 8) ≤ Q := Nat.mul_div_le Q 8
  refine WP.mono (copyN_ok (S := S) (D := D) (so := so) (d := d) (K := Q / 8) hdr hsr
      ((hsep.sub_left (Region.sub_prefix (by omega))).sub_right (Region.sub_prefix (by omega))) (by omega)
      (Q / 8) (Nat.le_refl _) u hs hd
      (fun j hj => hr (8 * j) (by omega)) fun j hj => hw (8 * j) (by omega))
    fun u₁ ⟨hrd₁, hwr₁, hg₁, hf₁, hb₁⟩ => ?_
  have hf₁' : Frame [⟨D + BitVec.ofNat 64 d, Q⟩] u.mem u₁.mem :=
    hf₁.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega)⟩
  by_cases hm : Q % 8 = 0
  · simp only [hm, ite_true]
    have e : 8 * (Q / 8) = Q := by omega
    rw [e] at hb₁
    exact WP.block_nil ⟨hrd₁, hwr₁, hg₁, hf₁', hb₁⟩
  · simp only [hm, ite_false]
    have hr' : InRegions (u₁.rd ++ u₁.wr) (S + BitVec.ofNat 64 (so + Q - 8)) 8 := by
      rw [hrd₁, hwr₁, show so + Q - 8 = so + (Q - 8) by omega]; exact hr (Q - 8) (by omega)
    have hw' : InRegions u₁.wr (D + BitVec.ofNat 64 (d + Q - 8)) 8 := by
      rw [hwr₁, show d + Q - 8 = d + (Q - 8) by omega]; exact hw (Q - 8) (by omega)
    refine WP.mono (copyW_ok (u := u₁) (so := so + Q - 8) (d := d + Q - 8) (hg₁ _ hsr ▸ hs) (hg₁ _ hdr ▸ hd)
      hr' hw' hdr) fun u₂ ⟨hrd₂, hwr₂, hg₂, hm₂⟩ => ?_
    have hf₂ : Frame [⟨D + BitVec.ofNat 64 (d + Q - 8), 8⟩] u₁.mem u₂.mem := by
      rw [hm₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Offset.contains _ (Nat.le_refl _) (by omega) (by omega))
    refine ⟨hrd₂.trans hrd₁, hwr₂.trans hwr₁, fun r hr => (hg₂ r hr).trans (hg₁ r hr),
      hf₁'.trans (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega) (by omega)⟩), ?_⟩
    rw [show Q = (Q - 8) + 8 by omega, Proof.Hmac.Common.bytesAt_add, Proof.Hmac.Common.bytesAt_add,
      Offset.add_add, Offset.add_add, show d + (Q - 8) = d + Q - 8 by omega,
      show so + (Q - 8) = so + Q - 8 by omega]
    congr 1
    · rw [bytesAt_frame hf₂ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega),
        bytesAt_take _ _ (k := 8 * (Q / 8)) (by omega), hb₁, ← bytesAt_take _ _ (by omega)]
    · rw [hm₂, bytesAt_copied]
      exact bytesAt_frame hf₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hsep.sub_left (Offset.sub _ (by omega) (by omega))).sub_right (Region.sub_prefix (by omega)))
        (by omega)

end VG.Proof.Ecdsa.Rfc6979.X86_64
