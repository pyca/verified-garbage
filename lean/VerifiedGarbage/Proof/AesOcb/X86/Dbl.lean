import VerifiedGarbage.Proof.AesOcb.X86.Callee
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.Ocb.Spec

/-!
# AES-OCB on x86: doubling a block

Untrusted: everything here is checked by Lean. `dbl b s d` doubles the
block at `b + s` into `W + d` (`dblMem`): its words are byte-reversed into
numbers, doubled a word at a time as x86's CMAC does (`Proof.Cmac.dblW0`,
`dblW3`), and byte-reversed back, so that the block written is `double` of
the block read (`dblMem_block`). The run (`dblW_ok`, `dblK_ok`) reads each
word of the source before the word of the destination before it is
written, so the source may be the destination.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.X86 (at_ imm slot)
open VG.Proof.AesGcm.X86 (w64 slotv slotv_eq w64_add in_off in_left)

theorem bswap_eq (a : BitVec 32) : bswap a = byteRev32 a := rfl

theorem add_self_shl (x : BitVec 32) : x + x = x <<< 1 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  congr 1; omega

/-- The memory `dbl` leaves: the block at `A + s` doubled into `B + d`. -/
def dblMem (m : Mem) (A : Addr) (s : Nat) (B : Addr) (d : Nat) : Mem :=
  let b₀ := byteRev32 (m.readW (A + BitVec.ofNat 64 s) 32)
  let b₁ := byteRev32 (m.readW (A + BitVec.ofNat 64 (s + 4)) 32)
  let b₂ := byteRev32 (m.readW (A + BitVec.ofNat 64 (s + 8)) 32)
  let b₃ := byteRev32 (m.readW (A + BitVec.ofNat 64 (s + 12)) 32)
  Proof.Cmac.store4 m (B + BitVec.ofNat 64 d) (byteRev32 (Proof.Cmac.dblW0 b₀ b₁))
    (byteRev32 (Proof.Cmac.dblW0 b₁ b₂)) (byteRev32 (Proof.Cmac.dblW0 b₂ b₃)) (byteRev32 (Proof.Cmac.dblW3 b₀ b₃))

theorem dblMem_frame (m : Mem) (A : Addr) (s : Nat) (B : Addr) (d : Nat) :
    Frame [⟨B + BitVec.ofNat 64 d, 16⟩] m (dblMem m A s B d) :=
  Proof.Cmac.frame_store4 _ _ _ _ _

theorem dblMem_bytes (m : Mem) (A : Addr) (s : Nat) (B : Addr) (d : Nat) :
    bytesAt (dblMem m A s B d) (B + BitVec.ofNat 64 d) 16 = Spec.Cmac.dbl 16 (bytesAt m (A + BitVec.ofNat 64 s) 16) := by
  simp only [dblMem]
  rw [Proof.Cmac.bytesAt_store4, Proof.Cmac.le4_rev4, Proof.Cmac.dbl_words4,
    Proof.Cmac.dbl_eq (Proof.Cmac.bytesAt_length _ _ _), Proof.Cmac.ofBytes_rev4, add_ofNat_assoc,
    add_ofNat_assoc, add_ofNat_assoc]

/-- The block `dbl` writes is `double` of the block it reads. -/
theorem dblMem_block (m : Mem) (A : Addr) (s : Nat) (B : Addr) (d : Nat) :
    Spec.Ocb.blockAtMem (dblMem m A s B d) (B + BitVec.ofNat 64 d) =
      Spec.Ocb.double (Spec.Ocb.blockAtMem m (A + BitVec.ofNat 64 s)) := by
  rw [Spec.Ocb.blockAtMem, dblMem_bytes, Proof.Cmac.dbl_eq (Proof.Cmac.bytesAt_length _ _ _),
    Proof.Ocb.double_eq, Spec.Ocb.blockAtMem, Proof.Ocb.ofBytes_eq, Proof.Cmac.ofBytes_toBytes]

/-- `dbl` within `W` (`ebp`), from `W + s` to `W + d`, the same block or
apart. -/
theorem dblW_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {s d : Nat} (hs : s + 16 ≤ 2560)
    (hd : d + 16 ≤ 2560) (hsd : s = d ∨ s + 16 ≤ d ∨ d + 16 ≤ s) :
    ∃ t', runBlock isa (dbl .ebp s d) t = some t' ∧ t'.mem = dblMem t.mem (w64 p.W) s (w64 p.W) d ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  refine ⟨_, by grun [dbl, Impl.AesOcb.X86.dblW, E.ebp, L.aW, E.perm.wR, E.perm.wW], ?_, fun r h₁ h₂ h₃ => by
    gregs [h₁, h₂, h₃], by gmems [], by gmems []⟩
  gmems [bswap_eq, add_self_shl]
  rw [Proof.AesGcm.X86.store4_eq]
  simp only [Nat.add_zero, Nat.add_assoc, Nat.reduceAdd]
  rfl

/-- A word of the key context, after a word of `W` written. -/
theorem readW_KW {p : Prm} (L : Lay p) (m : Mem) (v : BitVec 32) {a b : Nat} (ha : a + 4 ≤ 256)
    (hb : b + 4 ≤ 2560) :
    (m.writeW (w64 p.W + BitVec.ofNat 64 b) v).readW (w64 p.K + BitVec.ofNat 64 a) 32 =
      m.readW (w64 p.K + BitVec.ofNat 64 a) 32 :=
  Mem.readW_writeW_sep (L.k_w.sep (Offset.contains_base _ ha (by have := L.kw; omega))
    (Offset.contains_base _ hb (by have := L.ww; omega))) (by decide)

/-- `dbl` from the key context (`ebx`) at `K + s` to `W + d`. -/
theorem dblK_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) (hb : t.gpr .ebx = p.K) {s d : Nat}
    (hs : s + 16 ≤ 256) (hd : d + 16 ≤ 2560) :
    ∃ t', runBlock isa (dbl .ebx s d) t = some t' ∧ t'.mem = dblMem t.mem (w64 p.K) s (w64 p.W) d ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  refine ⟨_, by grun [dbl, Impl.AesOcb.X86.dblW, E.ebp, hb, L.aW, L.aK, E.perm.wR, E.perm.wW, E.perm.kR,
    (readW_KW L)], ?_, fun r h₁ h₂ h₃ => by gregs [h₁, h₂, h₃], by gmems [], by gmems []⟩
  gmems [bswap_eq, add_self_shl, (readW_KW L)]
  rw [Proof.AesGcm.X86.store4_eq]
  simp only [Nat.add_zero, Nat.add_assoc, Nat.reduceAdd]
  rfl

end VG.Proof.AesOcb.X86
