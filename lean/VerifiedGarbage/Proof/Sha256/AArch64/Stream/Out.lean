module

import VerifiedGarbage.Proof.MdStream.AArch64.Words
public import VerifiedGarbage.Impl.Sha256.AArch64.Stream
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.MdStream.Spec
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Sha256.Stream

/-! # Streaming SHA-256 on AArch64: the digest, sixteen bytes at a time

`out256` writes the same bytes as `out32 8 true`: the hash value's eight
words, big-endian. -/

@[expose] public section

namespace VG.Proof.Sha256.AArch64.Stream

open VG VG.AArch64 VG.Proof.MdStream VG.Proof.MdStream.AArch64
open VG.Proof.Sha256.Stream (writeBytes writeBytes_append)

/-- Sixteen bytes loaded, their words byte-reversed. -/
theorem rev32b_read (m : Mem) (p : Addr) :
    VRevOp.rev32b.eval (m.read p 16) =
      ofVWords (rev32 (m.readW (p + BitVec.ofNat 64 0) 32)) (rev32 (m.readW (p + BitVec.ofNat 64 4) 32))
        (rev32 (m.readW (p + BitVec.ofNat 64 8) 32)) (rev32 (m.readW (p + BitVec.ofNat 64 12) 32)) := by
  apply vec_ext
  intro j hj
  rw [vword_rev32b _ hj, vword_read16 _ _ hj, vword_ofVWords _ _ _ _ hj]
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl

theorem writeW_rev32 (m : Mem) (a : Addr) (x : BitVec 32) :
    m.writeW a (rev32 x) = writeBytes m a (bytes32 true x) :=
  writeW32 m a true x

theorem writeBytes_at (m : Mem) (q : Addr) (xs ys : List Byte) (k : Nat) (hk : xs.length = k)
    (h : k + ys.length < 2 ^ 64) :
    writeBytes (writeBytes m q xs) (q + BitVec.ofNat 64 k) ys = writeBytes m q (xs ++ ys) := by
  subst hk; exact writeBytes_append m q xs ys h

/-- Two sixteen-byte stores of the words at `p`, byte-reversed, at `a`: the
eight words' big-endian bytes. -/
theorem write_digest (m : Mem) (p a : Addr) :
    (m.write (a + BitVec.ofNat 64 0) 16 (VRevOp.rev32b.eval (m.read (p + BitVec.ofNat 64 0) 16))).write
        (a + BitVec.ofNat 64 16) 16 (VRevOp.rev32b.eval (m.read (p + BitVec.ofNat 64 16) 16)) =
      writeBytes m a ((List.range 8).flatMap fun k => bytes32 true (m.readW (p + BitVec.ofNat 64 (4 * k)) 32)) := by
  rw [rev32b_read, rev32b_read, write16, write16]
  simp only [Offset.add_add, Nat.reduceAdd, writeW_rev32]
  rw [show (List.range 8) = [0, 1, 2, 3, 4, 5, 6, 7] from rfl,
    show a + BitVec.ofNat 64 0 = a from BitVec.add_zero a]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, Nat.reduceMul]
  have l := bytes32_length true
  rw [writeBytes_at _ _ _ _ 4 (l _) (by simp only [l]; decide),
    writeBytes_at _ _ _ _ 8 (by simp only [List.length_append, l]) (by simp only [l]; decide),
    writeBytes_at _ _ _ _ 12 (by simp only [List.length_append, l]) (by simp only [l]; decide),
    writeBytes_at _ _ _ _ 16 (by simp only [List.length_append, l]) (by simp only [l]; decide),
    writeBytes_at _ _ _ _ 20 (by simp only [List.length_append, l]) (by simp only [l]; decide),
    writeBytes_at _ _ _ _ 24 (by simp only [List.length_append, l]) (by simp only [l]; decide),
    writeBytes_at _ _ _ _ 28 (by simp only [List.length_append, l]) (by simp only [l]; decide)]
  simp only [List.append_assoc]

/-- `out256` writes the eight words at `x19` to `x21`, big-endian, as `out32 8 true` does. -/
theorem out256_ok {s₀ : State}
    (hin : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x19) 32) (hout : InRegions s₀.wr (s₀.gpr .x21) 32) :
    WP isa (.block Impl.Sha256.AArch64.Stream.out256) s₀ fun s' =>
      (∀ r, r ≠ .x9 → s'.gpr r = s₀.gpr r) ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.sp = s₀.sp ∧
      s'.mem = writeBytes s₀.mem (s₀.gpr .x21)
        ((List.range 8).flatMap fun k => bytes32 true (s₀.mem.readW (s₀.gpr .x19 + BitVec.ofNat 64 (4 * k)) 32)) := by
  have i0 : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x19 + BitVec.ofNat 64 0) 16 :=
    InRegions.offset hin (by decide) (by decide)
  have i16 : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x19 + BitVec.ofNat 64 16) 16 :=
    InRegions.offset hin (by decide) (by decide)
  have o0 : InRegions s₀.wr (s₀.gpr .x21 + BitVec.ofNat 64 0) 16 := InRegions.offset hout (by decide) (by decide)
  have o16 : InRegions s₀.wr (s₀.gpr .x21 + BitVec.ofNat 64 16) 16 := InRegions.offset hout (by decide) (by decide)
  apply WP.of_runBlock
  simp only [Impl.Sha256.AArch64.Stream.out256, reduceCtorEq, ↓reduceIte, Nat.reduceMod, Nat.reduceLT,
    Nat.reduceMul, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store,
    VOp.eval, Option.bind_some, Option.map_some, and_self, isa, RegUpd.gpr_setV, RegUpd.v_setV,
    RegUpd.mem_setV, RegUpd.rd_setV, RegUpd.wr_setV, i0, i16, o0, o16, Option.some.injEq,
    exists_eq_left']
  exact ⟨fun _ _ => trivial, trivial, trivial, rfl, write_digest _ _ _⟩

end VG.Proof.Sha256.AArch64.Stream
