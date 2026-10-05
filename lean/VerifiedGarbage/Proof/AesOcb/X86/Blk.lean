import VerifiedGarbage.Proof.AesOcb.X86.Dbl
import VerifiedGarbage.Proof.Cmac.Block32

/-!
# AES-OCB on x86: blocks copied and XORed a word at a time

Untrusted: everything here is checked by Lean. `copy16 s d` copies the
block at `W + s` to `W + d` (`copyMem16`), and `xor16 b s d` XORs the block
at `b + s` into `W + d` (`xorMem16`), a word at a time; as blocks, the
block written is the one read (`copyMem16_block`), or the XOR of the two
(`xorMem16_block`). The runs are within `W` (`copy16_ok`, `xor16W_ok`) or
read another buffer, apart from `W` (`xor16R_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem)
open VG.Impl.AesGcm.X86 (at_ imm slot)
open VG.Proof.AesGcm.X86 (w64 slotv slotv_eq w64_add in_off in_left)

/-! ## Memory -/

/-- The memory after the block at `A + s` is copied to `B + d`. -/
def copyMem16 (m : Mem) (A : Addr) (s : Nat) (B : Addr) (d : Nat) : Mem :=
  Proof.Cmac.store4 m (B + BitVec.ofNat 64 d) (m.readW (A + BitVec.ofNat 64 s) 32)
    (m.readW (A + BitVec.ofNat 64 (s + 4)) 32) (m.readW (A + BitVec.ofNat 64 (s + 8)) 32)
    (m.readW (A + BitVec.ofNat 64 (s + 12)) 32)

/-- The memory after the block at `A + s` is XORed into `B + d`. -/
def xorMem16 (m : Mem) (A : Addr) (s : Nat) (B : Addr) (d : Nat) : Mem :=
  Proof.Cmac.store4 m (B + BitVec.ofNat 64 d)
    (m.readW (B + BitVec.ofNat 64 d) 32 ^^^ m.readW (A + BitVec.ofNat 64 s) 32)
    (m.readW (B + BitVec.ofNat 64 (d + 4)) 32 ^^^ m.readW (A + BitVec.ofNat 64 (s + 4)) 32)
    (m.readW (B + BitVec.ofNat 64 (d + 8)) 32 ^^^ m.readW (A + BitVec.ofNat 64 (s + 8)) 32)
    (m.readW (B + BitVec.ofNat 64 (d + 12)) 32 ^^^ m.readW (A + BitVec.ofNat 64 (s + 12)) 32)

theorem copyMem16_frame (m : Mem) (A : Addr) (s : Nat) (B : Addr) (d : Nat) :
    Frame [⟨B + BitVec.ofNat 64 d, 16⟩] m (copyMem16 m A s B d) := Proof.Cmac.frame_store4 _ _ _ _ _

theorem xorMem16_frame (m : Mem) (A : Addr) (s : Nat) (B : Addr) (d : Nat) :
    Frame [⟨B + BitVec.ofNat 64 d, 16⟩] m (xorMem16 m A s B d) := Proof.Cmac.frame_store4 _ _ _ _ _

theorem copyMem16_bytes (m : Mem) (A : Addr) (s : Nat) (B : Addr) (d : Nat) :
    bytesAt (copyMem16 m A s B d) (B + BitVec.ofNat 64 d) 16 = bytesAt m (A + BitVec.ofNat 64 s) 16 := by
  rw [copyMem16, Proof.Cmac.bytesAt_store4, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW,
    Proof.Cmac.le4_readW, Proof.Cmac.bytesAt_split4, add_ofNat_assoc, add_ofNat_assoc, add_ofNat_assoc]

theorem copyMem16_block (m : Mem) (A : Addr) (s : Nat) (B : Addr) (d : Nat) :
    blockAtMem (copyMem16 m A s B d) (B + BitVec.ofNat 64 d) = blockAtMem m (A + BitVec.ofNat 64 s) := by
  rw [blockAtMem, copyMem16_bytes, ← blockAtMem]

theorem xorMem16_bytes (m : Mem) (A : Addr) (s : Nat) (B : Addr) (d : Nat) :
    bytesAt (xorMem16 m A s B d) (B + BitVec.ofNat 64 d) 16 =
      Spec.Cmac.xor (bytesAt m (B + BitVec.ofNat 64 d) 16) (bytesAt m (A + BitVec.ofNat 64 s) 16) := by
  rw [xorMem16, Proof.Cmac.bytesAt_store4, ← add_ofNat_assoc _ d 4, ← add_ofNat_assoc _ d 8,
    ← add_ofNat_assoc _ d 12, ← add_ofNat_assoc _ s 4, ← add_ofNat_assoc _ s 8, ← add_ofNat_assoc _ s 12,
    Proof.Cmac.xor_words4]

theorem xorMem16_block (m : Mem) (A : Addr) (s : Nat) (B : Addr) (d : Nat) :
    blockAtMem (xorMem16 m A s B d) (B + BitVec.ofNat 64 d) =
      blockAtMem m (B + BitVec.ofNat 64 d) ^^^ blockAtMem m (A + BitVec.ofNat 64 s) := by
  rw [blockAtMem, xorMem16_bytes, ← Proof.Ocb.xor_eq, Proof.Ocb.ofBytes_xor (Proof.Cmac.bytesAt_length _ _ _)
    (Proof.Cmac.bytesAt_length _ _ _)]
  rfl

/-! ## Runs -/

/-- `copy16 s d` within `W`, the blocks apart. -/
theorem copy16_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {s d : Nat} (hs : s + 16 ≤ 2560)
    (hd : d + 16 ≤ 2560) (hsd : s + 16 ≤ d ∨ d + 16 ≤ s) :
    ∃ t', runBlock isa (copy16 s d) t = some t' ∧ t'.mem = copyMem16 t.mem (w64 p.W) s (w64 p.W) d ∧
      (∀ r, r ≠ .eax → t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  refine ⟨_, by grun [copy16, E.ebp, L.aW, E.perm.wR, E.perm.wW], ?_, fun r h₁ => by gregs [h₁], by gmems [],
    by gmems []⟩
  gmems []
  rw [Proof.AesGcm.X86.store4_eq]
  rfl

/-- `xor16 .ebp s d` within `W`, the blocks apart. -/
theorem xor16W_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {s d : Nat} (hs : s + 16 ≤ 2560)
    (hd : d + 16 ≤ 2560) (hsd : s + 16 ≤ d ∨ d + 16 ≤ s) :
    ∃ t', runBlock isa (xor16 .ebp s d) t = some t' ∧ t'.mem = xorMem16 t.mem (w64 p.W) s (w64 p.W) d ∧
      (∀ r, r ≠ .eax → t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  refine ⟨_, by grun [xor16, xorW, E.ebp, L.aW, E.perm.wR, E.perm.wW], ?_, fun r h₁ => by gregs [h₁],
    by gmems [], by gmems []⟩
  gmems []
  rw [Proof.AesGcm.X86.store4_eq]
  simp only [Nat.add_zero]
  rfl

/-- A word of a buffer `⟨B, k⟩` apart from `W`, after a word of `W` written. -/
theorem readW_XW {p : Prm} (L : Lay p) {B : Addr} {k : Nat} (hB : B.toNat + k ≤ 2 ^ 32)
    (hd : (⟨B, k⟩ : Region).Disjoint ⟨w64 p.W, 2560⟩) (m : Mem) (v : BitVec 32) {a b : Nat} (ha : a + 4 ≤ k)
    (hb : b + 4 ≤ 2560) :
    (m.writeW (w64 p.W + BitVec.ofNat 64 b) v).readW (B + BitVec.ofNat 64 a) 32 = m.readW (B + BitVec.ofNat 64 a) 32 :=
  Mem.readW_writeW_sep (hd.sep (Offset.contains_base _ ha (by omega))
    (Offset.contains_base _ hb (by have := L.ww; omega))) (by decide)

/-- `xor16 b s d`, reading the block at `b + s` of a buffer `⟨w64 X, k⟩`
apart from `W`. -/
theorem xor16R_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {b : Reg} (hb : b ≠ .eax) {X : BitVec 32}
    (hX : t.gpr b = X) {k : Nat} (hk : X.toNat + k ≤ 2 ^ 32)
    (hdis : (⟨w64 X, k⟩ : Region).Disjoint ⟨w64 p.W, 2560⟩) (hR : Covers [⟨w64 X, k⟩] (t.rd ++ t.wr)) {s d : Nat}
    (hs : s + 16 ≤ k) (hd : d + 16 ≤ 2560) :
    ∃ t', runBlock isa (xor16 b s d) t = some t' ∧ t'.mem = xorMem16 t.mem (w64 X) s (w64 p.W) d ∧
      (∀ r, r ≠ .eax → t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have aX : ∀ {o : Nat}, o < k → w64 (X + BitVec.ofNat 32 o) = w64 X + BitVec.ofNat 64 o := fun ho =>
    w64_add (by omega)
  have rX : ∀ {o : Nat}, o + 4 ≤ k → InRegions (t.rd ++ t.wr) (w64 X + BitVec.ofNat 64 o) 4 := fun ho =>
    in_off hR ho (by omega)
  have hXk : (w64 X).toNat + k ≤ 2 ^ 32 := by rw [Proof.AesGcm.X86.toNat_w64]; exact hk
  refine ⟨_, by grun [xor16, xorW, E.ebp, hX, L.aW, aX, rX, E.perm.wR, E.perm.wW, (readW_XW L hXk hdis)],
    ?_, fun r h₁ => by gregs [h₁], by gmems [], by gmems []⟩
  gmems [(readW_XW L hXk hdis)]
  rw [Proof.AesGcm.X86.store4_eq]
  simp only [Nat.add_zero]
  rfl

end VG.Proof.AesOcb.X86
