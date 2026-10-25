module

public import VerifiedGarbage.Impl.MdStream.RISCV64
public import VerifiedGarbage.Proof.MdStream.Spec
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Sha256.Stream
import all Init.Data.Nat.Bitwise.Basic

/-!
# Streaming Merkle–Damgård hash functions on RISC-V: big-endian length fields and digests

What `lenBE` and `outBE` (`Impl/MdStream/RISCV64.lean`) write, for the
`ShapeD` of the hash functions whose length field and digest are big-endian
(SHA-1, SM3).
-/

@[expose] public section

namespace VG.Proof.MdStream.RISCV64

open VG VG.RISCV64 VG.RISCV64.ByteLoad VG.Impl.MdStream.RISCV64 VG.Impl.Words.RISCV64
open VG.WriteBytes (writeBytes writeBytes_nil writeBytes_append writeBytes_frame)

/-- The big-endian bytes of the message length in bits, from the byte count. -/
def beLen (x : BitVec 64) : List Byte :=
  (List.range 8).reverse.map fun i => (BitVec.ofNat 64 (8 * x.toNat)).extractLsb' (8 * i) 8

/-- An access at an offset within an access. -/
theorem contains_add {r : Region} {a : Addr} {n d m : Nat} (h : r.Contains a n) (hd : d + m ≤ n) :
    r.Contains (a + BitVec.ofNat 64 d) m := by
  simp only [Region.Contains] at h ⊢
  rw [show a + BitVec.ofNat 64 d - r.base = (a - r.base) + BitVec.ofNat 64 d by
    rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg]; ac_rfl, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- A byte of a register, as a right shift leaves it. -/
theorem shr_byte (x : BitVec 64) (s : Nat) : (x >>> s).setWidth 8 = x.extractLsb' s 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.getLsbD_ushiftRight, hi]

theorem beBytes_len (x : BitVec 64) : beBytes 8 (x <<< 3) = beLen x := by
  rw [beLen, Proof.Sha256.Stream.bits8]
  simp only [beBytes, shr_byte]
  rfl

theorem lenBE_ok {N : Nat} (hN : N + 64 ≤ 2048) (s : State)
    (hout : InRegions s.wr (s.gpr .s1 + BitVec.ofNat 64 (N + 56)) 8) :
    WP isa (.block (lenBE N)) s fun s' => (∀ r, r ≠ .t1 → r ≠ .t3 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = writeBytes s.mem (s.gpr .s1 + BitVec.ofNat 64 (N + 56)) (beLen (s.gpr .s4)) := by
  obtain ⟨R, hR, hc⟩ := hout
  unfold lenBE
  refine Steps.wp_sll (by decide) fun s₁ u₁ => ?_
  have e1 : s₁.gpr .s1 = s.gpr .s1 := u₁.other _ (by decide)
  refine WP.mono (storeBE_ok (by decide) (by decide) (by decide) (by decide) (by omega)
    fun j hj => ⟨R, by rw [u₁.wr]; exact hR, by
      rw [e1, BitVec.ofNat_add (N + 56) j, ← BitVec.add_assoc]
      exact contains_add hc (by omega)⟩) fun s' e => ?_
  subst e
  refine ⟨fun r h1 h3 => ?_, u₁.rd, u₁.wr, u₁.sp, ?_⟩
  · rw [RegUpd.gpr_write_of_ne _ _ h3]; exact u₁.other r h1
  · rw [RegUpd.mem_write, u₁.mem, e1, u₁.gpr, beBytes_len]

/-- A word of the digest, as `storeBE 4` stores it. -/
theorem beBytes_word (w : BitVec 32) : beBytes 4 (w.setWidth 64) = bytes32 true w := by
  simp only [beBytes, shr_byte, bytes32, ite_true]
  rw [show List.range 4 = [0, 1, 2, 3] from rfl]
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i hi <;> simp <;> omega

theorem flat_length (be : Bool) (f : Nat → BitVec 32) (k : Nat) :
    ((List.range k).flatMap fun j => bytes32 be (f j)).length = 4 * k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih, List.flatMap_singleton,
      bytes32_length]
    omega

/-- Bytes written right after `xs`, at `4 k`. -/
theorem writeBytes_after (m : Mem) (q : Addr) (xs ys : List Byte) {k : Nat} (hx : xs.length = 4 * k)
    (h : xs.length + ys.length < 2 ^ 64) :
    writeBytes (writeBytes m q xs) (q + BitVec.ofNat 64 (4 * k)) ys = writeBytes m q (xs ++ ys) := by
  rw [← hx, writeBytes_append _ _ _ _ h]

/-- The first `k` words of the digest are written. -/
structure OutI (s₀ : State) (k : Nat) (s : State) : Prop where
  keep : ∀ r, r ≠ .t1 → r ≠ .t2 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  mem : s.mem = writeBytes s₀.mem (s₀.gpr .s3) ((List.range k).flatMap fun j =>
    bytes32 true (s₀.mem.readW (s₀.gpr .s1 + BitVec.ofNat 64 (4 * j)) 32))

theorem out_step {n : Nat} (hn : n ≤ 16) {s₀ : State} (hin : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .s1) (4 * n))
    (hout : InRegions s₀.wr (s₀.gpr .s3) (4 * n))
    (hd : Region.Disjoint ⟨s₀.gpr .s1, 4 * n⟩ ⟨s₀.gpr .s3, 4 * n⟩)
    {k : Nat} (hk : k < n) {s : State} (h : OutI s₀ k s) :
    WP isa (.block (loadLE32 .t1 .t2 .s1 (4 * k) ++ storeBE 4 .t1 .t2 .s3 (4 * k))) s (OutI s₀ (k + 1)) := by
  obtain ⟨Rin, hRin, cin⟩ := hin
  obtain ⟨Rout, hRout, cout⟩ := hout
  have h1 : s.gpr .s1 = s₀.gpr .s1 := h.keep _ (by decide) (by decide)
  have h3 : s.gpr .s3 = s₀.gpr .s3 := h.keep _ (by decide) (by decide)
  have hP := flat_length true (fun j => s₀.mem.readW (s₀.gpr .s1 + BitVec.ofNat 64 (4 * j)) 32) k
  rw [WP.block_append_iff]
  refine WP.mono (loadLE32_ok (by decide) (by decide) (by decide) (by omega)
    ⟨Rin, by rw [h.rd, h.wr]; exact hRin, by rw [h1]; exact contains_add cin (by omega)⟩) fun s₁ e₁ => ?_
  subst e₁
  refine WP.mono (storeBE_ok (by decide) (by decide) (by decide) (by decide) (by omega)
    fun j hj => ⟨Rout, by rw [RegUpd.wr_write, RegUpd.wr_write, h.wr]; exact hRout, by
      rw [RegUpd.gpr_write_of_ne _ _ (by decide), RegUpd.gpr_write_of_ne _ _ (by decide), h3]
      exact contains_add cout (by omega)⟩) fun s₂ e₂ => ?_
  subst e₂
  -- The word read is the one of the initial memory: the output is elsewhere.
  have hread : s.mem.readW (s₀.gpr .s1 + BitVec.ofNat 64 (4 * k)) 32 =
      s₀.mem.readW (s₀.gpr .s1 + BitVec.ofNat 64 (4 * k)) 32 := by
    rw [h.mem]
    refine (writeBytes_frame (R := ⟨s₀.gpr .s3, 4 * n⟩) _ _ _ ?_).readW
      (r := ⟨s₀.gpr .s1 + BitVec.ofNat 64 (4 * k), 4⟩) (Region.contains_self _ _) ?_ (by decide)
    · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, hP]; omega
    · intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      subst hr'
      exact hd.sub_left (Offset.sub_base _ (by omega))
  refine ⟨fun r h1' h2' => ?_, h.rd, h.wr, h.sp, ?_⟩
  · simp only [RegUpd.gpr_write, h1', h2', ite_false]
    exact h.keep r h1' h2'
  · simp only [RegUpd.mem_write, RegUpd.gpr_write, reduceCtorEq, ↓reduceIte, h1, h3, hread,
      beBytes_word]
    rw [h.mem, writeBytes_after _ _ _ _ hP (by rw [hP, bytes32_length]; omega), List.range_succ,
      List.flatMap_append, List.flatMap_singleton]

theorem outBE_ok {n : Nat} (hn : n ≤ 16) (s : State) (hin : InRegions (s.rd ++ s.wr) (s.gpr .s1) (4 * n))
    (hout : InRegions s.wr (s.gpr .s3) (4 * n))
    (hd : Region.Disjoint ⟨s.gpr .s1, 4 * n⟩ ⟨s.gpr .s3, 4 * n⟩) :
    WP isa (.block (outBE n)) s fun s' => (∀ r, r ≠ .t1 → r ≠ .t2 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = writeBytes s.mem (s.gpr .s3) ((List.range n).flatMap fun j =>
        bytes32 true (s.mem.readW (s.gpr .s1 + BitVec.ofNat 64 (4 * j)) 32)) :=
  WP.mono (wp_range_flatMap (M := isa) (OutI s) (fun k s' hk h => out_step hn hin hout hd hk h) n
    (Nat.le_refl _) s ⟨fun _ _ _ => rfl, rfl, rfl, rfl, by simp [writeBytes_nil]⟩)
    fun s' h => ⟨h.keep, h.rd, h.wr, h.sp, h.mem⟩

end VG.Proof.MdStream.RISCV64
