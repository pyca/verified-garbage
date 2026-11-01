module

public import VerifiedGarbage.Proof.AesCcm.RISCV64.Env
public import VerifiedGarbage.Proof.AesCcm.RISCV64.Wp
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.AesCcm.Words
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# AES-CCM on RISC-V: `Ctr₀` (`ctrs`) and the tag out (`tagOut`)

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/AesCcm/PPC64LE/Ctrs.lean`): `ctrs` zeroes `W + 48`, writes
`q − 1 = 14 − n` in its first byte and copies the `n`-byte nonce after it:
`Ctr₀ = [q − 1]₈ ‖ N ‖ 0⁸q` (A.3, `ctrs_wp`). `tagOut` copies the first
`tag_len` bytes of the tag at `W` to `tag` (`tagOut_wp`).
-/

@[expose] public section

namespace VG.Proof.AesCcm.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.AesCcm.RISCV64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCcm (length_bytesAt)

/-- Sixteen zero bytes, as two doublewords. -/
theorem zeros16_bytes (m : Mem) (p : Addr) :
    bytesAt ((m.writeW p (0 : BitVec 64)).writeW (p + BitVec.ofNat 64 8) (0 : BitVec 64)) p 16 =
      Spec.Ccm.zeros 16 := by
  rw [Proof.AesCcm.bytesAt_writeW64_at _ _ (o := 8) _ (by decide) (by decide),
    Proof.AesCcm.bytesAt_writeW64_base _ _ _ (by decide) (by decide)]
  simp only [Proof.Cmac.le8_zero, List.drop_append, List.take_append, List.drop_drop]
  simp [Spec.Ccm.zeros, Spec.Cmac.zeros, length_bytesAt]

/-- `Ctr₀` at `W + 48`, from the `n`-byte nonce at `N` (`a2`, `a3`). -/
theorem ctrs_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {N : Addr} (hN : Buf c s N c.nl)
    (h2 : s.gpr .a2 = N) (h3 : s.gpr .a3 = BitVec.ofNat 64 c.nl) :
    WP isa ctrs s fun s' => PK s s' ∧ Frame [⟨c.W + BitVec.ofNat 64 48, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s.mem N c.nl) 0 := by
  have h7 := L.h7
  have h13 := L.h13
  unfold ctrs ctrsSeg zero16
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_li (by decide) fun s₁ u₁ => ?_)
  refine wp_sd (a := c.W + BitVec.ofNat 64 48) (by decide)
    (by rw [u₁.other _ (by decide), E.s1]; rfl) (L.alW (by decide) (by decide))
    (by rw [u₁.wr]; exact E.perm.wW (by decide)) fun s₂ u₂ => ?_
  refine wp_sd (a := c.W + BitVec.ofNat 64 48 + BitVec.ofNat 64 8) (by decide)
    (by rw [u₂.gpr, u₁.other _ (by decide), E.s1, Offset.add_add]; rfl)
    (by rw [Offset.add_add]; exact L.alW (by decide) (by decide))
    (by rw [u₂.wr, u₁.wr, Offset.add_add]; exact E.perm.wW (by decide)) fun s₃ u₃ => ?_
  refine wp_li (by decide) fun s₄ u₄ => wp_sub fun s₅ u₅ => ?_
  refine wp_sb (a := c.W + BitVec.ofNat 64 48) (by decide)
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), E.s1]; rfl)
    (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact E.perm.wW (by decide)) fun s₆ u₆ => ?_
  refine wp_mv fun s₇ u₇ => wp_addi (by decide) fun s₈ u₈ => wp_mv fun s₉ u₉ => WP.block_nil ?_
  have pk₉ : PK s s₉ := (PK.ofUpd u₁).trans ((PK.ofMupd u₂).trans ((PK.ofMupd u₃).trans ((PK.ofUpd u₄).trans
    ((PK.ofUpd u₅).trans ((PK.ofMupd u₆).trans ((PK.ofUpd u₇).trans ((PK.ofUpd u₈).trans (PK.ofUpd u₉))))))))
  have E₉ := E.of_pk pk₉
  have g₄ : ∀ r, r ≠ .t0 → r ≠ .t1 → s₅.gpr r = s.gpr r := fun r h0 h1 => by
    rw [u₅.other _ h1, u₄.other _ h1, u₃.gpr, u₂.gpr, u₁.other _ h0]
  -- The memory before the copy.
  have m₉ : s₉.mem = (((s.mem.writeW (c.W + BitVec.ofNat 64 48) (0 : BitVec 64)).writeW
      (c.W + BitVec.ofNat 64 48 + BitVec.ofNat 64 8) (0 : BitVec 64)).writeW (c.W + BitVec.ofNat 64 48)
      (BitVec.ofNat 8 (15 - c.nl - 1) : Byte)) := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.gpr, u₄.gpr, u₄.other .a3 (by decide), u₃.gpr, u₂.gpr,
      u₁.other .a3 (by decide), h3, Proof.AesCcm.sub_low_byte (by omega), u₅.mem, u₄.mem, u₃.mem, u₂.gpr, u₂.mem,
      u₁.mem, u₁.gpr]
    rfl
  have hb : BytesPre s₉ N (c.W + BitVec.ofNat 64 49) c.nl :=
    { a0 := by rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.gpr, g₄ .a2 (by decide) (by decide), h2]
      a1 := by rw [u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), u₆.gpr,
        g₄ .s1 (by decide) (by decide), E.s1]; rfl
      a2 := by rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, g₄ .a3 (by decide) (by decide), h3]
      pos := by omega
      lt := by omega
      rd := by rw [pk₉.rd, pk₉.wr]; exact hN.rd
      wr := E₉.perm.wC (by omega)
      disj := hN.wd (by omega) }
  refine WP.mono (copy_wp s₉ hb) fun s₁₀ ⟨hm, _, k₁₀⟩ => ⟨pk₉.trans (PK.ofKeeps k₁₀), ?_, ?_⟩
  · rw [hm, m₉]
    have cB : ∀ d k, 48 ≤ d → d + k ≤ 64 →
        (⟨c.W + BitVec.ofNat 64 48, 16⟩ : Region).Contains (c.W + BitVec.ofNat 64 d) k :=
      fun d k h₁ h₂ => Offset.contains c.W h₁ (by omega) (by decide)
    refine ((Proof.Cmac.frame_store2 _ _ _).writeW (List.mem_singleton_self _) _ (cB 48 1 (by decide) (by decide))).trans
      (writeBytes_frame _ _ _ ?_)
    rw [length_bytesAt]; exact cB 49 c.nl (by decide) (by omega)
  · have hx : bytesAt s₉.mem N c.nl = bytesAt s.mem N c.nl := by
      rw [m₉]
      refine Proof.Cmac.bytesAt_frame (rs := [⟨c.W + BitVec.ofNat 64 48, 16⟩])
        (((Proof.Cmac.frame_store2 _ _ _).writeW (List.mem_singleton_self _) _
          (Offset.contains c.W (Nat.le_refl _) (by decide) (by decide)))) (fun r hr => ?_) (by omega)
      simp only [List.mem_singleton] at hr; subst hr; exact hN.wd (by decide)
    have hz : bytesAt ((s.mem.writeW (c.W + BitVec.ofNat 64 48) (0 : BitVec 64)).writeW
        (c.W + BitVec.ofNat 64 48 + BitVec.ofNat 64 8) (0 : BitVec 64)) (c.W + BitVec.ofNat 64 48) 16 =
        Spec.Ccm.zeros 16 := zeros16_bytes _ _
    rw [hm, hx, m₉, show c.W + BitVec.ofNat 64 49 = c.W + BitVec.ofNat 64 48 + BitVec.ofNat 64 1 from
        (Offset.add_add c.W 48 1).symm,
      Proof.AesCcm.bytesAt_writeBytes_at _ _ (o := 1) (n := 16) _ (by rw [length_bytesAt]; omega) (by decide),
      Proof.AesCcm.bytesAt_writeW8_base _ _ _ (by decide) (by decide), hz, length_bytesAt]
    simp only [Spec.Ccm.ctrBlock, length_bytesAt, Proof.AesCcm.be_zero, Spec.Ccm.zeros, List.take_succ_cons,
      List.take_zero, List.drop_replicate, List.cons_append, List.nil_append]
    rw [Nat.add_comm 1 c.nl, List.drop_succ_cons, List.drop_replicate]

/-- The first `tag_len` bytes of the tag at `W` copied to `tag`. -/
theorem tagOut_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) (S : Slots c s.mem)
    (hT : Covers [⟨c.T, c.tl⟩] s.wr) :
    WP isa tagOut s fun s' => PK s s' ∧ Frame [⟨c.T, c.tl⟩] s.mem s'.mem ∧
      bytesAt s'.mem c.T c.tl = bytesAt s.mem c.W c.tl := by
  have ht4 := L.t4
  have ht16 := L.t16
  unfold tagOut
  refine WP.seq (wp_ld (a := c.W + BitVec.ofNat 64 240) (by decide) (by rw [E.s1]; rfl)
    (L.alW (by decide) (by decide)) (E.perm.wR (by decide)) fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ =>
      WP.block_nil ?_)
  have pk₃ : PK s s₃ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans (PK.ofUpd u₃))
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have hwt : (⟨c.W, c.tl⟩ : Region).Disjoint ⟨c.T, c.tl⟩ :=
    (L.t_w.sub_right (Region.sub_prefix (by omega))).symm.sub_left (Region.sub_prefix (Nat.le_refl _))
  have hb : BytesPre s₃ c.W c.T c.tl :=
    { a0 := by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), E.s1]
      a1 := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, S.tag]
      a2 := by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), E.s2]
      pos := by omega
      lt := by omega
      rd := by
        rw [pk₃.rd, pk₃.wr]
        have h := E.perm.wCR (d := 0) (n := c.tl) (by omega)
        rw [BitVec.add_zero] at h
        exact h
      wr := by rw [pk₃.wr]; exact hT
      disj := hwt }
  refine WP.mono (copy_wp s₃ hb) fun s₄ ⟨hm, _, k₄⟩ => ⟨pk₃.trans (PK.ofKeeps k₄), ?_, ?_⟩
  · rw [hm, m₃]; exact writeBytes_frame _ _ _ (by rw [length_bytesAt]; exact Region.contains_self _ _)
  · rw [hm, m₃]
    have := Proof.AesCcm.bytesAt_writeBytes_base s.mem c.T (bytesAt s.mem c.W c.tl) (n := c.tl)
      (by rw [length_bytesAt]) (by have := L.tw; omega)
    rw [this, length_bytesAt, List.drop_eq_nil_of_le (by rw [length_bytesAt]), List.append_nil]

end VG.Proof.AesCcm.RISCV64
