module

public import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Backend
public import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Frame
public import VerifiedGarbage.Proof.Argon2.HPrime
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Compare
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Absorb
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Length
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Finalize
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Init
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Blake2.AArch64.Stream.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MdStream.AArch64.Common
public import VerifiedGarbage.Impl.Argon2.AArch64.HPrime
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Spec.Blake2
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Copy
import VerifiedGarbage.Proof.Blake2.Stream
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! ### `Argon2.AArch64.HPrime.Output`, which this module and modules that import it used -/

section

/-! # H′: emitting a digest or its 32-byte prefix -/

@[expose] public section

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime
open VG.Proof.MdStream.AArch64 (wp_mov wp_addImm wp_movz wp_subImm)
open VG.Spec.Blake2 (bytesAt)
open VG.WriteBytes

theorem bytesAt_writeBytes (m : Mem) (p : Addr) (xs : List Byte) (hn : xs.length < 2 ^ 64) :
    bytesAt (writeBytes m p xs) p xs.length = xs := by
  apply List.ext_getElem (by simp only [bytesAt, List.length_map, List.length_range])
  intro i _ hi
  simp only [bytesAt, List.getElem_map, List.getElem_range, writeBytes,
    Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hn, hi] : i < 2 ^ 64),
    hi, ite_true, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

theorem bytesAt_take (m : Mem) (p : Addr) (n k : Nat) (hn : n ≤ k) :
    (bytesAt m p k).take n = bytesAt m p n := by
  simp only [bytesAt, ← List.map_take, List.take_range, Nat.min_eq_left hn]

structure Copied (s : State) (k : Nat) (t : State) : Prop where
  output : t.gpr .x22 = s.gpr .x22 + BitVec.ofNat 64 k
  other : ∀ r, r ≠ .x8 → r ≠ .x3 → r ≠ .x2 → r ≠ .x22 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : t.mem = writeBytes s.mem (s.gpr .x22) (bytesAt s.mem (s.gpr .x24 + 768) k)

theorem copy_ok (s : State) (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 64)
    (count : s.gpr .x8 = BitVec.ofNat 64 k)
    (work : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr)
    (out : ∀ i < k, InRegions s.wr (s.gpr .x22 + BitVec.ofNat 64 i) 1)
    (sep : (⟨s.gpr .x24 + 768, k⟩ : Region).Disjoint ⟨s.gpr .x22, k⟩) :
    WP isa copy s (Copied s k) := by
  unfold copy
  refine WP.seq (wp_mov fun a ha => wp_addImm (by decide) fun u hu => WP.block_nil ?_)
  have src : u.gpr .x2 = s.gpr .x24 + 768 := by rw [hu.gpr, ha.gpr]; rfl
  have other : ∀ r, r ≠ .x2 → u.gpr r = s.gpr r := fun r hr =>
    (hu.other r hr).trans (ha.other r hr)
  have mem : u.mem = s.mem := hu.mem.trans ha.mem
  have rd : u.rd = s.rd := hu.rd.trans ha.rd
  have wr : u.wr = s.wr := hu.wr.trans ha.wr
  have read : ∀ i < k, InRegions (u.rd ++ u.wr)
      (s.gpr .x24 + 768 + BitVec.ofNat 64 i) 1 := by
    intro i hi'
    rw [rd, wr, BitVec.add_assoc,
      show (768 : Addr) = BitVec.ofNat 64 768 from rfl, ← BitVec.ofNat_add]
    exact ⟨_, List.mem_append_right _ work,
      Offset.contains_base _ (by omega_using [hi, hi'] : 768 + i + 1 ≤ 16384) (by omega_using [hi, hi'])⟩
  have loop := copyLoop_ok u _ _ k lo (by omega_using [hi]) src (other .x22 (by decide))
    ((other .x8 (by decide)).trans count) read
    (by intro i hi'; rw [wr]; exact out i hi') sep
  obtain ⟨tr, t, he, ht⟩ := loop
  refine ⟨tr, t, he, ht.destination,
    fun r h1 h2 h3 h4 => (ht.other r h1 h2 h3 h4).trans (other r h3),
    ht.rd.trans rd, ht.wr.trans wr, (VG.AArch64.Exec.sp he).trans (hu.sp.trans ha.sp), ?_⟩
  rw [ht.mem, mem, List.take_of_length_le]
  simp only [bytesAt, List.length_map, List.length_range, Nat.le_refl]

theorem Copied.frame {s t : State} {k : Nat} (h : Copied s k t) :
    Frame [⟨s.gpr .x22, k⟩] s.mem t.mem := by
  rw [h.mem]
  apply writeBytes_frame
  simpa only [bytesAt, List.length_map, List.length_range, BitVec.add_zero] using
    Offset.contains_base (s.gpr .x22) (d := 0) (n := k) (k := k) (by omega_using []) (by decide)

structure Emitted (s t : State) : Prop where
  output : t.gpr .x22 = s.gpr .x22 + 32
  remaining : t.gpr .x23 = s.gpr .x23 - 32
  other : ∀ r, r ≠ .x8 → r ≠ .x3 → r ≠ .x2 → r ≠ .x22 → r ≠ .x23 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : t.mem = writeBytes s.mem (s.gpr .x22) (bytesAt s.mem (s.gpr .x24 + 768) 32)

theorem emitPrefix_ok (s : State)
    (work : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr)
    (out : ∀ i < 32, InRegions s.wr (s.gpr .x22 + BitVec.ofNat 64 i) 1)
    (sep : (⟨s.gpr .x24 + 768, 32⟩ : Region).Disjoint ⟨s.gpr .x22, 32⟩) :
    WP isa emitPrefix s (Emitted s) := by
  unfold emitPrefix
  refine WP.seq (wp_movz fun a ha => WP.block_nil ?_)
  have base : a.gpr .x24 = s.gpr .x24 := ha.other _ (by decide)
  have dst : a.gpr .x22 = s.gpr .x22 := ha.other _ (by decide)
  have workA : (⟨a.gpr .x24, 16384⟩ : Region) ∈ a.wr := by rw [base, ha.wr]; exact work
  have outA : ∀ i < 32, InRegions a.wr (a.gpr .x22 + BitVec.ofNat 64 i) 1 := by
    rw [dst, ha.wr]; exact out
  have sepA : (⟨a.gpr .x24 + 768, 32⟩ : Region).Disjoint ⟨a.gpr .x22, 32⟩ := by
    rw [base, dst]; exact sep
  refine WP.seq ((copy_ok a 32 (by decide) (by decide) ha.gpr workA outA sepA).mono ?_)
  intro u hu
  refine wp_subImm (by decide) fun t ht => WP.block_nil ?_
  refine ⟨?_, ?_, fun r h1 h2 h3 h4 h5 => ?_, ht.rd.trans (hu.rd.trans ha.rd),
    ht.wr.trans (hu.wr.trans ha.wr), ht.sp.trans (hu.sp.trans ha.sp), ?_⟩
  · rw [ht.other _ (by decide), hu.output, dst]; rfl
  · rw [ht.gpr, hu.other _ (by decide) (by decide) (by decide) (by decide), ha.other _ (by decide)]
    rfl
  · exact (ht.other r h5).trans ((hu.other r h1 h2 h3 h4).trans (ha.other r h1))
  · rw [ht.mem, hu.mem, ha.mem, base, dst]

theorem Emitted.frame {s t : State} (h : Emitted s t) :
    Frame [⟨s.gpr .x22, 32⟩] s.mem t.mem := by
  rw [h.mem]
  apply writeBytes_frame
  simpa only [bytesAt, List.length_map, List.length_range, BitVec.add_zero] using
    Offset.contains_base (s.gpr .x22) (d := 0) (n := 32) (k := 32) (by decide) (by decide)

theorem Emitted.digest {s t : State} (h : Emitted s t)
    (sep : (⟨s.gpr .x24, 16384⟩ : Region).Disjoint ⟨s.gpr .x22, 32⟩) :
    bytesAt t.mem (s.gpr .x24 + 768) 64 = bytesAt s.mem (s.gpr .x24 + 768) 64 := by
  apply Proof.Blake2.bytesAt_congr
  intro i hi
  apply h.frame.bytes (R := ⟨s.gpr .x24 + 768, 64⟩) _ (show 64 ≤ 2 ^ 64 by decide) hi
  intro r hr
  simp only [List.mem_singleton] at hr; subst r
  exact sep.sub_left (Offset.sub_base _ (by decide : 768 + 64 ≤ 16384))

end VG.Proof.Argon2.AArch64.HPrime

end

end

/-! ### `Argon2.AArch64.HPrime.Chain`, which only this module used -/

section

/-! Merged from `Proof.Argon2.AArch64.HPrime.Next`. -/

@[expose] public section

section
/-! # H′: hashing the previous 64-byte digest -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime
open VG.Spec.Blake2 (b Repr bytesAt)
open VG.Proof.MdStream.AArch64 (wp_movz)

theorem next_ok (v : Backend) (s : State)
    (hlen : 1 ≤ (s.gpr .x1).toNat ∧ (s.gpr .x1).toNat ≤ 64)
    (hsp : 16 ≤ s.sp.toNat)
    (hwr : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr)
    (stackWork : (below s.sp 16).Disjoint ⟨s.gpr .x24, 16384⟩) :
    WP isa (next v.hash) s fun t =>
      (bytesAt t.mem (s.gpr .x24 + 768) 64).take (s.gpr .x1).toNat =
        Spec.Argon2.H (s.gpr .x1).toNat (bytesAt s.mem (s.gpr .x24 + 768) 64) ∧ Keeps s t := by
  unfold next
  refine WP.seq ((init_ok v s hlen hwr).mono ?_)
  rintro a ⟨reprA, regsA, rdA, wrA, spA, frameA⟩
  have ka : Keeps s a := ⟨regsA, rdA, wrA, spA, init_frame _ _ frameA⟩
  have digest : bytesAt a.mem (a.gpr .x24 + 768) 64 = bytesAt s.mem (s.gpr .x24 + 768) 64 := by
    rw [ka.x24]
    apply Proof.Blake2.bytesAt_congr
    intro i hi
    apply frameA.bytes (R := ⟨s.gpr .x24 + 768, 64⟩) _ (show 64 ≤ 2 ^ 64 by decide) hi
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact (Offset.base_disjoint _ (e := 768) (n := 64) (k := 192) (by decide) (by decide)).symm
  have reprA' : Repr b (Spec.Blake2.init b (s.gpr .x1).toNat 0) a.mem (a.gpr .x24) [] := by
    rw [ka.x24]; exact reprA
  have wrA' : (⟨a.gpr .x24, 16384⟩ : Region) ∈ a.wr := by rw [ka.x24, ka.wr]; exact hwr
  have swA : (below a.sp 16).Disjoint ⟨a.gpr .x24, 16384⟩ := by
    rw [ka.x24, ka.sp]; exact stackWork
  refine WP.seq ((absorbFixed_ok v a _ 768 64 (by decide) (by rw [ka.sp]; exact hsp) (by decide) (by decide) reprA' wrA' swA).mono ?_)
  rintro u ⟨reprU, ku⟩
  have ksu := ka.trans ku
  have reprU' : Repr b (Spec.Blake2.init b (s.gpr .x1).toNat 0) u.mem (u.gpr .x24)
      (bytesAt s.mem (s.gpr .x24 + 768) 64) := by
    rw [ku.x24]
    simpa only [show BitVec.ofNat 64 768 = (768 : Addr) from rfl, digest] using reprU
  refine WP.seq (wp_movz fun w hw => WP.block_nil ?_)
  have kw : Keeps u w := by
    refine ⟨fun r hr _ => ?_, hw.rd, hw.wr, hw.sp, ?_⟩
    · have hn : r ≠ .x1 := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact hw.other r hn
    · rw [hw.mem]; exact Frame.refl _ _
  have ksw := ksu.trans kw
  have reprW : Repr b (Spec.Blake2.init b (s.gpr .x1).toNat 0) w.mem (w.gpr .x24)
      (bytesAt s.mem (s.gpr .x24 + 768) 64) := by
    rw [hw.mem, kw.x24]; exact reprU'
  have length : (bytesAt s.mem (s.gpr .x24 + 768) 64).length = 64 := by
    simp only [bytesAt, List.length_map, List.length_range]
  have count : w.gpr .x1 = BitVec.ofNat 64 (bytesAt s.mem (s.gpr .x24 + 768) 64).length := by
    rw [length]; exact hw.gpr
  have bound : (bytesAt s.mem (s.gpr .x24 + 768) 64).length < 2 ^ 64 := by rw [length]; decide
  have wrW : (⟨w.gpr .x24, 16384⟩ : Region) ∈ w.wr := by rw [ksw.x24, ksw.wr]; exact hwr
  have swW : (below w.sp 16).Disjoint ⟨w.gpr .x24, 16384⟩ := by
    rw [ksw.x24, ksw.sp]; exact stackWork
  refine (finalize_ok v w _ _ reprW count bound (by rw [ksw.sp]; exact hsp) wrW swW).mono ?_
  rintro t ⟨out, regsT, rdT, wrT, spT, frameT⟩
  refine ⟨?_, ksw.trans ⟨regsT, rdT, wrT, spT, finalize_frame _ _ frameT⟩⟩
  have result := congrArg (List.take (s.gpr .x1).toNat) out
  rw [ksw.x24] at result
  exact result.trans (Proof.Argon2.H_stream _ _).symm

end VG.Proof.Argon2.AArch64.HPrime
end

/-! Merged from `Proof.Argon2.AArch64.HPrime.ChainStep`. -/
section
/-! # H′: one hash-and-prefix iteration -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime
open VG.Proof.MdStream.AArch64 (wp_movz)
open VG.Spec.Blake2 (bytesAt)

structure ChainStep (s t : State) : Prop where
  output : t.gpr .x22 = s.gpr .x22 + 32
  remaining : t.gpr .x23 = s.gpr .x23 - 32
  regs : ∀ r ∈ preserved, r ≠ .x30 → r ≠ .x22 → r ≠ .x23 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame [⟨s.gpr .x24, 832⟩, below s.sp 16, ⟨s.gpr .x22, 32⟩] s.mem t.mem
  digest : bytesAt t.mem (s.gpr .x24 + 768) 64 =
    Spec.Argon2.H 64 (bytesAt s.mem (s.gpr .x24 + 768) 64)
  bytes : bytesAt t.mem (s.gpr .x22) 32 =
    (Spec.Argon2.H 64 (bytesAt s.mem (s.gpr .x24 + 768) 64)).take 32
  comparison : t.gpr .x9 = if (s.gpr .x23 - 32).toNat < 65 then 1 else 0

theorem chainStep_ok (v : Backend) (s : State)
    (hsp : 16 ≤ s.sp.toNat)
    (remainingBound : 32 ≤ (s.gpr .x23).toNat ∧ (s.gpr .x23).toNat < 2 ^ 32)
    (work : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr)
    (out : ∀ i < 32, InRegions s.wr (s.gpr .x22 + BitVec.ofNat 64 i) 1)
    (sep : (⟨s.gpr .x24, 16384⟩ : Region).Disjoint ⟨s.gpr .x22, 32⟩)
    (stackWork : (below s.sp 16).Disjoint ⟨s.gpr .x24, 16384⟩) :
    WP isa (.seq (.block [.movz .x .x1 64 0])
      (.seq (next v.hash) (.seq emitPrefix (.block [.subImm .x .x9 .x23 65, .lsr .x .x9 .x9 63]))))
      s (ChainStep s) := by
  refine WP.seq (wp_movz fun a ha => WP.block_nil ?_)
  have ka : Keeps s a := Keeps.of_upd ha (by decide)
  have workA : (⟨a.gpr .x24, 16384⟩ : Region) ∈ a.wr := by rw [ka.x24, ka.wr]; exact work
  have stackA : (below a.sp 16).Disjoint ⟨a.gpr .x24, 16384⟩ := by
    rw [ka.x24, ka.sp]; exact stackWork
  have lengthA : (a.gpr .x1).toNat = 64 := by rw [ha.gpr]; rfl
  refine WP.seq ((next_ok v a (by rw [lengthA]; decide) (by rw [ka.sp]; exact hsp) workA stackA).mono ?_)
  rintro u ⟨du, ku⟩
  have ksu := ka.trans ku
  have dstU : u.gpr .x22 = s.gpr .x22 := ksu.regs _ (by decide) (by decide)
  have digestU : bytesAt u.mem (s.gpr .x24 + 768) 64 =
      Spec.Argon2.H 64 (bytesAt s.mem (s.gpr .x24 + 768) 64) := by
    simpa only [lengthA, ka.x24, ha.mem, bytesAt_take _ _ 64 64 (by decide)] using du
  have workU : (⟨u.gpr .x24, 16384⟩ : Region) ∈ u.wr := by rw [ksu.x24, ksu.wr]; exact work
  have outU : ∀ i < 32, InRegions u.wr (u.gpr .x22 + BitVec.ofNat 64 i) 1 := by
    rw [ksu.wr, dstU]; exact out
  have sepU : (⟨u.gpr .x24 + 768, 32⟩ : Region).Disjoint ⟨u.gpr .x22, 32⟩ := by
    rw [ksu.x24, dstU]
    exact sep.sub_left (Offset.sub_base _ (by decide : 768 + 32 ≤ 16384))
  refine WP.seq ((emitPrefix_ok u workU outU sepU).mono ?_)
  intro w hw
  have remainingW : (w.gpr .x23).toNat < 2 ^ 32 := by
    rw [hw.remaining, ksu.regs _ (by decide) (by decide),
      BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact remainingBound.1)]
    exact Nat.lt_of_le_of_lt (Nat.sub_le ..) remainingBound.2
  refine (compare_ok w remainingW).mono fun t compared => ?_
  have gt := compared.other
  have mt := compared.mem
  have rt := compared.rd
  have wt := compared.wr
  have fw : Frame [⟨s.gpr .x22, 32⟩] u.mem w.mem := by
    rw [← dstU]; exact hw.frame
  refine ⟨?_, ?_, fun r hr h30 h14 h15 => ?_, rt.trans (hw.rd.trans ksu.rd),
    wt.trans (hw.wr.trans ksu.wr), compared.sp.trans (hw.sp.trans ksu.sp), ?_, ?_, ?_, ?_⟩
  · rw [gt _ (by decide), hw.output, dstU]
  · rw [gt _ (by decide), hw.remaining, ksu.regs _ (by decide) (by decide)]
  · have h9 : r ≠ .x9 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [gt r h9]
    have hrax : r ≠ .x8 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hrcx : r ≠ .x3 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hrdx : r ≠ .x2 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (hw.other r hrax hrcx hrdx h14 h15).trans (ksu.regs r hr h30)
  · rw [mt]
    apply Frame.trans (ksu.frame.sub ?_) (fw.sub ?_)
    · intro r hr
      exact ⟨r, List.mem_append_left _ hr, fun _ hx => hx⟩
    · intro r hr
      exact ⟨r, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr), fun _ hx => hx⟩
  · rw [mt, ← digestU]
    apply Proof.Blake2.bytesAt_congr
    intro i hi
    apply fw.bytes (R := ⟨s.gpr .x24 + 768, 64⟩) _ (show 64 ≤ 2 ^ 64 by decide) hi
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact sep.sub_left (Offset.sub_base _ (by decide : 768 + 64 ≤ 16384))
  · rw [mt, hw.mem, dstU, ksu.x24, ← digestU, bytesAt_take _ _ 32 64 (by decide)]
    exact bytesAt_writeBytes _ _ _ (by simp only [bytesAt, List.length_map, List.length_range]; decide)
  · rw [compared.value, hw.remaining, ksu.regs _ (by decide) (by decide)]

end VG.Proof.Argon2.AArch64.HPrime
end

/-! # H′: repeating the hash-and-prefix iteration -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime
open VG.Spec.Blake2 (bytesAt)
open VG.Proof.Argon2 (chainDigest chainPrefixes)

structure ChainResult (s : State) (n : Nat) (t : State) : Prop where
  output : t.gpr .x22 = s.gpr .x22 + BitVec.ofNat 64 (32 * n)
  remaining : t.gpr .x23 = s.gpr .x23 - BitVec.ofNat 64 (32 * n)
  regs : ∀ r ∈ preserved, r ≠ .x30 → r ≠ .x22 → r ≠ .x23 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame [⟨s.gpr .x24, 832⟩, below s.sp 16, ⟨s.gpr .x22, 32 * n⟩] s.mem t.mem
  digest : bytesAt t.mem (s.gpr .x24 + 768) 64 =
    chainDigest n (bytesAt s.mem (s.gpr .x24 + 768) 64)
  bytes : bytesAt t.mem (s.gpr .x22) (32 * n) =
    chainPrefixes n (bytesAt s.mem (s.gpr .x24 + 768) 64)

theorem ChainResult.refl (s : State) : ChainResult s 0 s :=
  ⟨by simp, by simp, fun _ _ _ _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, rfl, rfl⟩

theorem ChainResult.cons {s u t : State} {n : Nat} (step : ChainStep s u)
    (tail : ChainResult u n t) (bound : 32 * (n + 1) < 2 ^ 64)
    (sep : (⟨s.gpr .x24, 16384⟩ : Region).Disjoint ⟨s.gpr .x22, 32 * (n + 1)⟩)
    (stackOut : (below s.sp 16).Disjoint ⟨s.gpr .x22, 32 * (n + 1)⟩) :
    ChainResult s (n + 1) t := by
  have base := step.regs .x24 (by decide) (by decide) (by decide) (by decide)
  have sp := step.sp
  have sum : 32 * (n + 1) = 32 + 32 * n := by omega_arith
  have sumBV : BitVec.ofNat 64 (32 * (n + 1)) = 32 + BitVec.ofNat 64 (32 * n) := by
    rw [sum, BitVec.ofNat_add]; rfl
  have tf : Frame [⟨s.gpr .x24, 832⟩, below s.sp 16,
      ⟨s.gpr .x22 + 32, 32 * n⟩] u.mem t.mem := by
    rw [← base, ← sp, ← step.output]; exact tail.frame
  have extend {m m' : Mem} (d k : Nat) (hk : d + k ≤ 32 * (n + 1))
      (h : Frame [⟨s.gpr .x24, 832⟩, below s.sp 16,
        ⟨s.gpr .x22 + BitVec.ofNat 64 d, k⟩] m m') :
      Frame [⟨s.gpr .x24, 832⟩, below s.sp 16, ⟨s.gpr .x22, 32 * (n + 1)⟩] m m' := by
    apply h.sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ hx => hx⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ hx => hx⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)),
        Offset.sub_base _ hk⟩
  refine ⟨?_, ?_, fun r hr h30 h1 h2 => (tail.regs r hr h30 h1 h2).trans (step.regs r hr h30 h1 h2),
    tail.rd.trans step.rd, tail.wr.trans step.wr, tail.sp.trans step.sp, ?_, ?_, ?_⟩
  · rw [tail.output, step.output, sumBV, BitVec.add_assoc]
  · rw [tail.remaining, step.remaining, sumBV, BitVec.sub_sub]
  · exact (extend 0 32 (by omega_arith) (by simpa only [BitVec.add_zero] using step.frame)).trans
      (extend 32 (32 * n) (by omega_arith) tf)
  · rw [← base, tail.digest, base, step.digest, Proof.Argon2.chainDigest]
  · have before : bytesAt t.mem (s.gpr .x22) 32 = bytesAt u.mem (s.gpr .x22) 32 := by
      apply Proof.Blake2.bytesAt_congr
      intro i hi
      apply tf.bytes (R := ⟨s.gpr .x22, 32⟩) _ (show 32 ≤ 2 ^ 64 by decide) hi
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (sep.sub_left (Region.sub_prefix (by decide))).symm.sub_left
          (Region.sub_prefix (by omega_arith))
      · exact stackOut.symm.sub_left (Region.sub_prefix (by omega_arith))
      · exact Offset.base_disjoint _ (e := 32) (n := 32 * n) (k := 32) (by decide) (by omega_arith)
    rw [sum, Proof.Blake2.bytesAt_add, before, step.bytes,
      show BitVec.ofNat 64 32 = (32 : Addr) from rfl, ← step.output, tail.bytes,
      base, step.digest]
    rw [Proof.Argon2.chainPrefixes]

theorem chain_ok (v : Backend) (n lastLen : Nat) (s : State)
    (positive : 1 ≤ n) (last : 33 ≤ lastLen ∧ lastLen ≤ 64)
    (bound : 32 * n + lastLen < 2 ^ 32)
    (hsp : 16 ≤ s.sp.toNat)
    (count : s.gpr .x23 = BitVec.ofNat 64 (32 * n + lastLen))
    (work : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr)
    (out : ∀ i < 32 * n, InRegions s.wr (s.gpr .x22 + BitVec.ofNat 64 i) 1)
    (sep : (⟨s.gpr .x24, 16384⟩ : Region).Disjoint ⟨s.gpr .x22, 32 * n⟩)
    (stackWork : (below s.sp 16).Disjoint ⟨s.gpr .x24, 16384⟩)
    (stackOut : (below s.sp 16).Disjoint ⟨s.gpr .x22, 32 * n⟩) :
    WP isa (chain v.hash) s (ChainResult s n) := by
  induction n generalizing s with
  | zero => omega_arith
  | succ n ih =>
    have out32 : ∀ i < 32, InRegions s.wr (s.gpr .x22 + BitVec.ofNat 64 i) 1 :=
      fun i hi => out i (by omega_arith)
    have sep32 := sep.sub_right (Region.sub_prefix (show 32 ≤ 32 * (n + 1) by omega_arith))
    obtain ⟨trace, u, run, step⟩ := chainStep_ok v s hsp
      (by rw [count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]; omega_arith) work out32 sep32 stackWork
    have base := step.regs .x24 (by decide) (by decide) (by decide) (by decide)
    have sp := step.sp
    have countU : u.gpr .x23 = BitVec.ofNat 64 (32 * n + lastLen) := by
      rw [step.remaining, count, show (32 : Addr) = BitVec.ofNat 64 32 from rfl,
        Offset.ofNat_sub_ofNat (by omega_arith : 32 ≤ 32 * (n + 1) + lastLen)]
      rw [show 32 * (n + 1) + lastLen - 32 = 32 * n + lastLen by omega_arith]
    have compareU : u.gpr .x9 = if 32 * n + lastLen < 65 then 1 else 0 := by
      rw [step.comparison, ← step.remaining, countU, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
    cases n with
    | zero =>
      have flag : isa.eval (.zero .x .x9) u = some false := by
        simp [eval, State.read, compareU, show lastLen < 65 by omega_arith]
      exact ⟨_, u, .loopExit run flag, (ChainResult.refl u).cons step (by omega_arith) sep stackOut⟩
    | succ n =>
      have workU : (⟨u.gpr .x24, 16384⟩ : Region) ∈ u.wr := by rw [base, step.wr]; exact work
      have outU : ∀ i < 32 * (n + 1), InRegions u.wr (u.gpr .x22 + BitVec.ofNat 64 i) 1 := by
        intro i hi
        rw [step.wr, step.output, BitVec.add_assoc,
          show (32 : Addr) = BitVec.ofNat 64 32 from rfl, ← BitVec.ofNat_add]
        exact out (32 + i) (by omega_arith)
      have suffix : Region.Sub ⟨u.gpr .x22, 32 * (n + 1)⟩ ⟨s.gpr .x22, 32 * (n + 1 + 1)⟩ := by
        rw [step.output]
        exact Offset.sub_base _ (by omega_arith : 32 + 32 * (n + 1) ≤ 32 * (n + 1 + 1))
      have sepU : (⟨u.gpr .x24, 16384⟩ : Region).Disjoint ⟨u.gpr .x22, 32 * (n + 1)⟩ := by
        rw [base]; exact sep.sub_right suffix
      have swU : (below u.sp 16).Disjoint ⟨u.gpr .x24, 16384⟩ := by
        rw [sp, base]; exact stackWork
      have soU : (below u.sp 16).Disjoint ⟨u.gpr .x22, 32 * (n + 1)⟩ := by
        rw [sp]; exact stackOut.sub_right suffix
      obtain ⟨trace', t, run', result⟩ := ih u (by omega_arith) (by omega_arith) (by rw [sp]; exact hsp) countU workU outU sepU swU soU
      have flag : isa.eval (.zero .x .x9) u = some true := by
        simp [eval, State.read, compareU, show ¬ 32 * (n + 1) + lastLen < 65 by omega_arith]
      exact ⟨_, t, .loopNext run flag run', result.cons step (by omega_arith) sep stackOut⟩

end VG.Proof.Argon2.AArch64.HPrime

end

end


/-! Merged from `Proof.Argon2.AArch64.HPrime.Written`. -/

@[expose] public section

section
/-! # H′: composing output fragments -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64
open VG.Spec.Blake2 (bytesAt)

/-- An output fragment, allowing hashing in the workspace between writes. -/
structure Written (s : State) (xs : List Byte) (t : State) : Prop where
  output : t.gpr .x22 = s.gpr .x22 + BitVec.ofNat 64 xs.length
  regs : ∀ r ∈ preserved, r ≠ .x30 → r ≠ .x22 → r ≠ .x23 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame [⟨s.gpr .x24, 832⟩, below s.sp 16, ⟨s.gpr .x22, xs.length⟩] s.mem t.mem
  bytes : bytesAt t.mem (s.gpr .x22) xs.length = xs

theorem Written.x24 {s t : State} {xs : List Byte} (h : Written s xs t) :
    t.gpr .x24 = s.gpr .x24 := h.regs _ (by decide) (by decide) (by decide) (by decide)

theorem Written.of_keeps {s t : State} (h : Keeps s t) : Written s [] t := by
  refine ⟨?_, fun r hr h30 _ _ => h.regs r hr h30, h.rd, h.wr, h.sp, ?_, rfl⟩
  · exact (h.regs .x22 (by decide) (by decide)).trans (BitVec.add_zero _).symm
  · exact h.frame.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ hx => hx⟩

theorem Written.before_keeps {s u t : State} {xs : List Byte} (h : Written u xs t)
    (k : Keeps s u) : Written s xs t := by
  have dst := k.regs .x22 (by decide) (by decide)
  refine ⟨by rw [h.output, dst], fun r hr h30 h1 h2 => (h.regs r hr h30 h1 h2).trans (k.regs r hr h30),
    h.rd.trans k.rd, h.wr.trans k.wr, h.sp.trans k.sp, ?_, ?_⟩
  · have before : Frame [⟨s.gpr .x24, 832⟩, below s.sp 16,
        ⟨s.gpr .x22, xs.length⟩] s.mem u.mem :=
      k.frame.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ hx => hx⟩
    exact before.trans (by simpa only [dst, k.x24, k.sp] using h.frame)
  · rw [← dst]; exact h.bytes

theorem Written.of_copied {s t : State} {k : Nat} (h : Copied s k t) (hk : k < 2 ^ 64) :
    Written s (bytesAt s.mem (s.gpr .x24 + 768) k) t := by
  have len : (bytesAt s.mem (s.gpr .x24 + 768) k).length = k := by
    simp only [bytesAt, List.length_map, List.length_range]
  refine ⟨by rw [len]; exact h.output, fun r hr _ h14 _ => ?_, h.rd, h.wr, h.sp, ?_, ?_⟩
  · have h1 : r ≠ .x8 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have h2 : r ≠ .x3 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have h3 : r ≠ .x2 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact h.other r h1 h2 h3 h14
  · rw [len]
    exact h.frame.sub fun r hr =>
      ⟨r, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr), fun _ hx => hx⟩
  · rw [h.mem]
    exact bytesAt_writeBytes _ _ _ (by rw [len]; exact hk)

theorem Written.of_emitted {s t : State} (h : Emitted s t) :
    Written s (bytesAt s.mem (s.gpr .x24 + 768) 32) t := by
  have len : (bytesAt s.mem (s.gpr .x24 + 768) 32).length = 32 := by
    simp only [bytesAt, List.length_map, List.length_range]
  refine ⟨by rw [len]; exact h.output, fun r hr _ h14 h15 => ?_, h.rd, h.wr, h.sp, ?_, ?_⟩
  · have h1 : r ≠ .x8 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have h2 : r ≠ .x3 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have h3 : r ≠ .x2 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact h.other r h1 h2 h3 h14 h15
  · rw [len]
    exact h.frame.sub fun r hr =>
      ⟨r, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr), fun _ hx => hx⟩
  · rw [h.mem]
    exact bytesAt_writeBytes _ _ _ (by rw [len]; decide)

theorem Written.of_chain {s t : State} {n : Nat} (h : ChainResult s n t) :
    Written s (Proof.Argon2.chainPrefixes n (bytesAt s.mem (s.gpr .x24 + 768) 64)) t := by
  refine ⟨?_, h.regs, h.rd, h.wr, h.sp, ?_, ?_⟩
  · simpa only [Proof.Argon2.chainPrefixes_length] using h.output
  · simpa only [Proof.Argon2.chainPrefixes_length] using h.frame
  · simpa only [Proof.Argon2.chainPrefixes_length] using h.bytes

theorem Written.trans {s u t : State} {xs ys : List Byte} (first : Written s xs u)
    (last : Written u ys t) (bound : xs.length + ys.length < 2 ^ 64)
    (sep : (⟨s.gpr .x24, 16384⟩ : Region).Disjoint ⟨s.gpr .x22, xs.length + ys.length⟩)
    (stack : (below s.sp 16).Disjoint ⟨s.gpr .x22, xs.length + ys.length⟩) :
    Written s (xs ++ ys) t := by
  have tf : Frame [⟨s.gpr .x24, 832⟩, below s.sp 16,
      ⟨s.gpr .x22 + BitVec.ofNat 64 xs.length, ys.length⟩] u.mem t.mem := by
    rw [← first.x24, ← first.sp, ← first.output]; exact last.frame
  have extend {m m' : Mem} (d k : Nat) (hk : d + k ≤ xs.length + ys.length)
      (h : Frame [⟨s.gpr .x24, 832⟩, below s.sp 16,
        ⟨s.gpr .x22 + BitVec.ofNat 64 d, k⟩] m m') :
      Frame [⟨s.gpr .x24, 832⟩, below s.sp 16,
        ⟨s.gpr .x22, (xs ++ ys).length⟩] m m' := by
    apply h.sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ hx => hx⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ hx => hx⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)),
        Offset.sub_base _ (by simpa only [List.length_append] using hk)⟩
  refine ⟨?_, fun r hr h30 h1 h2 => (last.regs r hr h30 h1 h2).trans (first.regs r hr h30 h1 h2),
    last.rd.trans first.rd, last.wr.trans first.wr, last.sp.trans first.sp, ?_, ?_⟩
  · rw [last.output, first.output, List.length_append, BitVec.ofNat_add, BitVec.add_assoc]
  · exact (extend 0 xs.length (by omega_using []) (by simpa only [BitVec.add_zero] using first.frame)).trans
      (extend xs.length ys.length (by omega_using []) tf)
  · have before : bytesAt t.mem (s.gpr .x22) xs.length = bytesAt u.mem (s.gpr .x22) xs.length := by
      apply Proof.Blake2.bytesAt_congr
      intro i hi
      apply tf.bytes (R := ⟨s.gpr .x22, xs.length⟩) _ (show xs.length ≤ 2 ^ 64 by omega_using [bound]) hi
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (sep.sub_left (Region.sub_prefix (by decide))).symm.sub_left (Region.sub_prefix (by omega_using []))
      · exact stack.symm.sub_left (Region.sub_prefix (by omega_using []))
      · exact Offset.base_disjoint _ (by omega_using []) (by omega_using [bound])
    rw [List.length_append, Proof.Blake2.bytesAt_add, before, first.bytes, ← first.output, last.bytes]

end VG.Proof.Argon2.AArch64.HPrime
end

/-! # H′: permissions and separation at an output cursor -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime
open VG.Proof.MdStream.AArch64 (wp_mov)
open VG.Spec.Blake2 (bytesAt)

structure Space (s : State) (n : Nat) : Prop where
  bound : n < 2 ^ 32
  spBound : 16 ≤ s.sp.toNat
  work : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr
  out : ∀ i < n, InRegions s.wr (s.gpr .x22 + BitVec.ofNat 64 i) 1
  sep : (⟨s.gpr .x24, 16384⟩ : Region).Disjoint ⟨s.gpr .x22, n⟩
  stackWork : (below s.sp 16).Disjoint ⟨s.gpr .x24, 16384⟩
  stackOut : (below s.sp 16).Disjoint ⟨s.gpr .x22, n⟩

theorem Space.advance {s t : State} {xs : List Byte} {n k : Nat}
    (h : Space s n) (written : Written s xs t) (size : xs.length + k ≤ n) : Space t k := by
  have suffix : Region.Sub ⟨t.gpr .x22, k⟩ ⟨s.gpr .x22, n⟩ := by
    rw [written.output]; exact Offset.sub_base _ size
  refine ⟨by have := h.bound; omega_using [size, this], by rw [written.sp]; exact h.spBound, ?_, ?_, ?_, ?_, ?_⟩
  · rw [written.wr, written.x24]; exact h.work
  · intro i hi
    rw [written.wr, written.output, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact h.out (xs.length + i) (by omega_using [size, hi])
  · rw [written.x24]; exact h.sep.sub_right suffix
  · rw [written.x24, written.sp]; exact h.stackWork
  · rw [written.sp]; exact h.stackOut.sub_right suffix

theorem Space.keeps {s t : State} {n : Nat} (h : Space s n) (k : Keeps s t) : Space t n :=
  h.advance (Written.of_keeps k) (by simp only [List.length_nil, Nat.zero_add, Nat.le_refl])

theorem Space.prefix {s : State} {n k : Nat} (h : Space s n) (hk : k ≤ n) : Space s k := by
  refine ⟨by have := h.bound; omega_using [hk, this], h.spBound, h.work, fun i hi => h.out i (by omega_using [hk, hi]),
    h.sep.sub_right (Region.sub_prefix hk), h.stackWork, h.stackOut.sub_right (Region.sub_prefix hk)⟩

theorem Space.join {s u t : State} {xs ys : List Byte} {n : Nat} (h : Space s n)
    (first : Written s xs u) (last : Written u ys t) (size : xs.length + ys.length ≤ n) :
    Written s (xs ++ ys) t :=
  first.trans last (by have := h.bound; omega_using [size, this])
    (h.sep.sub_right (Region.sub_prefix size)) (h.stackOut.sub_right (Region.sub_prefix size))

theorem copyRemaining_ok (s : State) (n : Nat) (space : Space s n)
    (lo : 1 ≤ n) (hi : n ≤ 64) (count : s.gpr .x23 = BitVec.ofNat 64 n) :
    WP isa copyRemaining s fun t => Written s (bytesAt s.mem (s.gpr .x24 + 768) n) t := by
  unfold copyRemaining
  refine WP.seq (wp_mov fun a ha => WP.block_nil ?_)
  have base := ha.other .x24 (by decide)
  have dst := ha.other .x22 (by decide)
  have workA : (⟨a.gpr .x24, 16384⟩ : Region) ∈ a.wr := by rw [base, ha.wr]; exact space.work
  have outA : ∀ i < n, InRegions a.wr (a.gpr .x22 + BitVec.ofNat 64 i) 1 := by
    rw [dst, ha.wr]; exact space.out
  have sepA : (⟨a.gpr .x24 + 768, n⟩ : Region).Disjoint ⟨a.gpr .x22, n⟩ := by
    rw [base, dst]; exact space.sep.sub_left (Offset.sub_base _ (by omega_using [hi] : 768 + n ≤ 16384))
  refine (copy_ok a n lo hi (ha.gpr.trans count) workA outA sepA).mono ?_
  intro t ht
  have result := Written.of_copied ht (by have := space.bound; omega_using [hi])
  refine ⟨?_, fun r hr h30 h1 h2 => ?_, result.rd.trans ha.rd, result.wr.trans ha.wr, result.sp.trans ha.sp, ?_, ?_⟩
  · simpa only [dst, ha.mem, base] using result.output
  · have hrax : r ≠ .x8 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (result.regs r hr h30 h1 h2).trans (ha.other r hrax)
  · simpa only [base, dst, ha.mem, ha.sp] using result.frame
  · simpa only [base, dst, ha.mem] using result.bytes

end VG.Proof.Argon2.AArch64.HPrime
