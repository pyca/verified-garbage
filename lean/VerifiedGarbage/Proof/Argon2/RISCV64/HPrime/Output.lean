module
public import VerifiedGarbage.Impl.Argon2.RISCV64.HPrime
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.RISCV64.Wp
public import VerifiedGarbage.Spec.Blake2

import VerifiedGarbage.Proof.Argon2.RISCV64.HPrime.Copy
import VerifiedGarbage.Proof.Blake2.Stream
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # H′: emitting a digest or its 32-byte prefix -/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.HPrime

open VG VG.RISCV64 VG.Impl.Argon2.RISCV64.HPrime
open VG.RISCV64.Wp (wp_mv wp_addi wp_li wp_subi)
open VG.Spec.Blake2 (bytesAt)
open VG.WriteBytes

theorem bytesAt_writeBytes (m : Mem) (p : Addr) (xs : List Byte) (hn : xs.length < 2 ^ 64) :
    bytesAt (writeBytes m p xs) p xs.length = xs := by
  apply List.ext_getElem (by simp only [bytesAt, List.length_map, List.length_range])
  intro i _ hi
  simp only [bytesAt, List.getElem_map, List.getElem_range, writeBytes,
    Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2 ^ 64),
    hi, ite_true, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

theorem bytesAt_take (m : Mem) (p : Addr) (n k : Nat) (hn : n ≤ k) :
    (bytesAt m p k).take n = bytesAt m p n := by
  simp only [bytesAt, ← List.map_take, List.take_range, Nat.min_eq_left hn]

structure Copied (s : State) (k : Nat) (t : State) : Prop where
  output : t.gpr .s2 = s.gpr .s2 + BitVec.ofNat 64 k
  other : ∀ r, r ≠ .a6 → r ≠ .a3 → r ≠ .a2 → r ≠ .s2 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : t.mem = writeBytes s.mem (s.gpr .s2) (bytesAt s.mem (s.gpr .s4 + 768) k)

theorem copy_ok (s : State) (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 64)
    (count : s.gpr .a6 = BitVec.ofNat 64 k)
    (work : (⟨s.gpr .s4, 16384⟩ : Region) ∈ s.wr)
    (out : ∀ i < k, InRegions s.wr (s.gpr .s2 + BitVec.ofNat 64 i) 1)
    (sep : (⟨s.gpr .s4 + 768, k⟩ : Region).Disjoint ⟨s.gpr .s2, k⟩) :
    WP isa copy s (Copied s k) := by
  unfold copy
  refine WP.seq (wp_addi (by decide) fun u hu => WP.block_nil ?_)
  have src : u.gpr .a2 = s.gpr .s4 + 768 := by rw [hu.gpr]; rfl
  have other : ∀ r, r ≠ .a2 → u.gpr r = s.gpr r := fun r hr => hu.other r hr
  have mem : u.mem = s.mem := hu.mem
  have rd : u.rd = s.rd := hu.rd
  have wr : u.wr = s.wr := hu.wr
  have read : ∀ i < k, InRegions (u.rd ++ u.wr)
      (s.gpr .s4 + 768 + BitVec.ofNat 64 i) 1 := by
    intro i hi'
    rw [rd, wr, BitVec.add_assoc,
      show (768 : Addr) = BitVec.ofNat 64 768 from rfl, ← BitVec.ofNat_add]
    exact ⟨_, List.mem_append_right _ work,
      Offset.contains_base _ (by omega : 768 + i + 1 ≤ 16384) (by omega)⟩
  have loop := copyLoop_ok u _ _ k lo (by omega) src (other .s2 (by decide))
    ((other .a6 (by decide)).trans count) read
    (by intro i hi'; rw [wr]; exact out i hi') sep
  obtain ⟨tr, t, he, ht⟩ := loop
  refine ⟨tr, t, he, ht.destination,
    fun r h1 h2 h3 h4 => (ht.other r h1 h2 h3 h4).trans (other r h3),
    ht.rd.trans rd, ht.wr.trans wr, (VG.RISCV64.Exec.sp he).trans hu.sp, ?_⟩
  rw [ht.mem, mem, List.take_of_length_le]
  simp only [bytesAt, List.length_map, List.length_range, Nat.le_refl]

theorem Copied.frame {s t : State} {k : Nat} (h : Copied s k t) :
    Frame [⟨s.gpr .s2, k⟩] s.mem t.mem := by
  rw [h.mem]
  apply writeBytes_frame
  simpa only [bytesAt, List.length_map, List.length_range, BitVec.add_zero] using
    Offset.contains_base (s.gpr .s2) (d := 0) (n := k) (k := k) (by omega) (by decide)

structure Emitted (s t : State) : Prop where
  output : t.gpr .s2 = s.gpr .s2 + 32
  remaining : t.gpr .s3 = s.gpr .s3 - 32
  other : ∀ r, r ≠ .a6 → r ≠ .a3 → r ≠ .a2 → r ≠ .s2 → r ≠ .s3 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : t.mem = writeBytes s.mem (s.gpr .s2) (bytesAt s.mem (s.gpr .s4 + 768) 32)

theorem emitPrefix_ok (s : State)
    (work : (⟨s.gpr .s4, 16384⟩ : Region) ∈ s.wr)
    (out : ∀ i < 32, InRegions s.wr (s.gpr .s2 + BitVec.ofNat 64 i) 1)
    (sep : (⟨s.gpr .s4 + 768, 32⟩ : Region).Disjoint ⟨s.gpr .s2, 32⟩) :
    WP isa emitPrefix s (Emitted s) := by
  unfold emitPrefix
  refine WP.seq (wp_li (by decide) fun a ha => WP.block_nil ?_)
  have base : a.gpr .s4 = s.gpr .s4 := ha.other _ (by decide)
  have dst : a.gpr .s2 = s.gpr .s2 := ha.other _ (by decide)
  have workA : (⟨a.gpr .s4, 16384⟩ : Region) ∈ a.wr := by rw [base, ha.wr]; exact work
  have outA : ∀ i < 32, InRegions a.wr (a.gpr .s2 + BitVec.ofNat 64 i) 1 := by
    rw [dst, ha.wr]; exact out
  have sepA : (⟨a.gpr .s4 + 768, 32⟩ : Region).Disjoint ⟨a.gpr .s2, 32⟩ := by
    rw [base, dst]; exact sep
  refine WP.seq ((copy_ok a 32 (by decide) (by decide) ha.gpr workA outA sepA).mono ?_)
  intro u hu
  refine wp_subi (by decide) fun t ht => WP.block_nil ?_
  refine ⟨?_, ?_, fun r h1 h2 h3 h4 h5 => ?_, ht.rd.trans (hu.rd.trans ha.rd),
    ht.wr.trans (hu.wr.trans ha.wr), ht.sp.trans (hu.sp.trans ha.sp), ?_⟩
  · rw [ht.other _ (by decide), hu.output, dst]; rfl
  · rw [ht.gpr, hu.other _ (by decide) (by decide) (by decide) (by decide), ha.other _ (by decide)]
    rfl
  · exact (ht.other r h5).trans ((hu.other r h1 h2 h3 h4).trans (ha.other r h1))
  · rw [ht.mem, hu.mem, ha.mem, base, dst]

theorem Emitted.frame {s t : State} (h : Emitted s t) :
    Frame [⟨s.gpr .s2, 32⟩] s.mem t.mem := by
  rw [h.mem]
  apply writeBytes_frame
  simpa only [bytesAt, List.length_map, List.length_range, BitVec.add_zero] using
    Offset.contains_base (s.gpr .s2) (d := 0) (n := 32) (k := 32) (by decide) (by decide)

theorem Emitted.digest {s t : State} (h : Emitted s t)
    (sep : (⟨s.gpr .s4, 16384⟩ : Region).Disjoint ⟨s.gpr .s2, 32⟩) :
    bytesAt t.mem (s.gpr .s4 + 768) 64 = bytesAt s.mem (s.gpr .s4 + 768) 64 := by
  apply Proof.Blake2.bytesAt_congr
  intro i hi
  apply h.frame.bytes (R := ⟨s.gpr .s4 + 768, 64⟩) _ (show 64 ≤ 2 ^ 64 by decide) hi
  intro r hr
  simp only [List.mem_singleton] at hr; subst r
  exact sep.sub_left (Offset.sub_base _ (by decide : 768 + 64 ≤ 16384))

end VG.Proof.Argon2.RISCV64.HPrime
