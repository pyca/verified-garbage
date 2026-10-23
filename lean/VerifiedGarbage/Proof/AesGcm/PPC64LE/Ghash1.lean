module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Env
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# AES-GCM on PPC64LE: GHASH of one block (`ghash1`)

Untrusted: everything here is checked by Lean. `ghash1 yo b o` continues
GHASH, with the hash subkey at `C + 240` and the accumulator at `St + yo`,
over the block at `b + o` (`ghash1_wp`), by a call of `vg_ghash` with the
working space at `W`.
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE

open VG VG.Impl.AesGcm.PPC64LE
open VG.PPC64LE hiding wp_add wp_addi wp_and wp_ld wp_li wp_lsl wp_lsr wp_lwz wp_std wp_stw wp_sub wp_subi
  wp_xor
open VG.Proof.ChaCha20Poly1305.PPC64LE (wp_addi wp_li)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom)

theorem blocksAt_one (m : Mem) (p : Addr) : blocksAt m p 1 = [blockAt m p] := by
  simp [blocksAt, BitVec.add_zero]

/-- The hash subkey of the key context at `C`. -/
abbrev hk (m : Mem) (C : Addr) : Block := blockAt m (C + BitVec.ofNat 64 240)

/-- What `ghash1` does: the accumulator continued over the block `Db`,
writing only the accumulator and the first 256 bytes of `W`. -/
structure Gh1Post (s : State) (W St C : Addr) (yo : Nat) (Db : Addr) (s' : State) : Prop where
  pk : PK s s'
  args : ∀ r ∈ [Reg.r18, .r19, .r20], s'.gpr r = s.gpr r
  frame : Frame [⟨St + BitVec.ofNat 64 yo, 16⟩, ⟨W, 256⟩] s.mem s'.mem
  y : blockAt s'.mem (St + BitVec.ofNat 64 yo) =
    ghashFrom (hk s.mem C) (blockAt s.mem (St + BitVec.ofNat 64 yo)) [blockAt s.mem Db]

theorem ghash1_wp {s : State} {W St C : Addr} (h : Env s W St C) {yo : Nat} (hyo : yo + 16 ≤ 80)
    {b : Reg} {o : Nat} {Db : Addr} (hb : s.gpr b + BitVec.ofNat 64 o = Db)
    (hbr : b ≠ .r0 ∧ b ≠ .r3 ∧ b ≠ .r4) (ho : o < 2 ^ 15)
    (hrd : Covers [⟨Db, 16⟩] (s.rd ++ s.wr))
    (hyd : (⟨St + BitVec.ofNat 64 yo, 16⟩ : Region).Disjoint ⟨Db, 16⟩)
    (hds : (⟨Db, 16⟩ : Region).Disjoint ⟨W, 256⟩) :
    WP isa (ghash1 yo b o) s (Gh1Post s W St C yo Db) := by
  unfold ghash1
  refine WP.seq (wp_addi (by decide) (by decide) fun s₁ u₁ => wp_addi (by decide) (by omega)
    fun s₂ u₂ => wp_addi hbr.1 ho fun s₃ u₃ => wp_li (by decide) fun s₄ u₄ => wp_mv fun s₅ u₅ =>
      WP.block_nil ?_)
  have pk₅ : PK s s₅ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans
    ((PK.ofUpd u₄).trans (PK.ofUpd u₅))))
  have m₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hW0 : (⟨W, 256⟩ : Region) = ⟨W + BitVec.ofNat 64 0, 256⟩ := by rw [BitVec.add_zero]
  have hgp : GhPre s₅ (C + BitVec.ofNat 64 240) (St + BitVec.ofNat 64 yo) Db W 1 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, by decide, h.c_st (by decide) hyo, ?_, by rw [Nat.mul_one]; exact hyd,
      ?_, by rw [Nat.mul_one]; exact hds, by have := h.wfit; omega, ?_, ?_⟩
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
        u₁.gpr, h.r16]
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
        u₁.other _ (by decide), h.r15]
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ hbr.2.2,
        u₁.other _ hbr.2.1, hb]
    · rw [u₅.other _ (by decide), u₄.gpr]
    · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
        u₁.other _ (by decide), h.r14]
    · rw [hW0]; exact h.c_w (by decide) (by decide)
    · rw [hW0]; exact h.st_w hyo (by decide)
    · rw [pk₅.rd, pk₅.wr]
      refine Covers.append_left (Covers.pair (h.cIn (by decide)) (by rw [Nat.mul_one]; exact hrd))
        (Covers.pair (h.stRd hyo) ?_)
      rw [hW0]; exact h.wRd (by decide)
    · rw [pk₅.wr]
      refine Covers.pair (h.stIn hyo) ?_
      rw [hW0]; exact h.wIn (by decide)
  refine WP.mono (gh_call hgp) fun s' ⟨ck, hy⟩ => ⟨pk₅.trans (PK.ofCall ck), fun r hr => ?_, ?_, ?_⟩
  · have hp : r ∈ preserved := by revert r; decide
    have hn : r ≠ .r3 ∧ r ≠ .r4 ∧ r ≠ .r5 ∧ r ≠ .r6 ∧ r ≠ .r7 := by revert r; decide
    rw [ck.saved r hp, u₅.other _ hn.2.2.2.2, u₄.other _ hn.2.2.2.1, u₃.other _ hn.2.2.1, u₂.other _ hn.2.1,
      u₁.other _ hn.1]
  · rw [← m₅]; exact ck.frame
  · rw [hy, m₅, blocksAt_one]

end VG.Proof.AesGcm.PPC64LE
