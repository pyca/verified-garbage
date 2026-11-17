module

import VerifiedGarbage.Proof.Argon2.PPC64LE.HPrime.Calls
public import VerifiedGarbage.Proof.Argon2.PPC64LE.HPrime.Frame
public import VerifiedGarbage.Proof.Argon2.HPrime
import VerifiedGarbage.Proof.Argon2.PPC64LE.HPrime.Compare
import VerifiedGarbage.Proof.Argon2.PPC64LE.HPrime.Absorb
import VerifiedGarbage.Proof.Argon2.PPC64LE.HPrime.Length
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Blake2.PPC64LE.Stream.Lit
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Argon2.PPC64LE.HPrime
public import VerifiedGarbage.Impl.MdStream.PPC64LE
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.Proof.MdStream.Spec
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Spec.Blake2
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.MdStream.PPC64LE.Common
import VerifiedGarbage.Proof.Blake2.Stream

/-! ### `Argon2.PPC64LE.HPrime.Output`, which this module and modules that import it used -/

section

/-! ### `Argon2.PPC64LE.HPrime.Copy`, which only this module used -/

section

/-! # H′: copying digest bytes -/

@[expose] public section

namespace VG.Proof.Argon2.PPC64LE.HPrime

open VG VG.PPC64LE VG.Impl.Argon2.PPC64LE.HPrime
open VG.Proof.MdStream.PPC64LE (wp_lbz wp_stb wp_addi wp_subi eval_nonzero)

theorem copyByte_ok (s : State)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .r5) 1)
    (hw : InRegions s.wr (s.gpr .r29) 1) :
    WP isa (.block copyByte) s fun t =>
      t.mem = s.mem.writeW (s.gpr .r29) (s.mem (s.gpr .r5)) ∧
      t.gpr .r5 = s.gpr .r5 + 1 ∧ t.gpr .r29 = s.gpr .r29 + 1 ∧
      t.gpr .r9 = s.gpr .r9 - 1 ∧
      (∀ r, r ≠ .r9 → r ≠ .r6 → r ≠ .r5 → r ≠ .r29 → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  unfold copyByte
  refine wp_lbz (a := s.gpr .r5) (by decide) (BitVec.add_zero _) hr fun a ha => ?_
  refine wp_stb (a := s.gpr .r29) (by decide) (by rw [ha.other _ (by decide)]; exact BitVec.add_zero _)
    (by rw [ha.wr]; exact hw) fun c hc => ?_
  refine wp_addi (by decide) fun d hd => wp_addi (by decide) fun e he =>
    wp_subi (by decide) fun t ht => WP.block_nil ?_
  have o : ∀ r, r ≠ .r9 → r ≠ .r6 → r ≠ .r5 → r ≠ .r29 → t.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [ht.other _ h1, he.other _ h4, hd.other _ h3, hc.gpr, ha.other _ h2]
  refine ⟨?_, ?_, ?_, ?_, o, ?_, ?_, ?_⟩
  · rw [ht.mem, he.mem, hd.mem, hc.mem, ha.gpr, ha.mem]
    congr 1
    ext i hi
    simp
  · rw [ht.other _ (by decide), he.other _ (by decide), hd.gpr, hc.gpr, ha.other _ (by decide)]; rfl
  · rw [ht.other _ (by decide), he.gpr, hd.other _ (by decide), hc.gpr, ha.other _ (by decide)]; rfl
  · rw [ht.gpr, he.other _ (by decide), hd.other _ (by decide), hc.gpr, ha.other _ (by decide)]; rfl
  · rw [ht.rd, he.rd, hd.rd, hc.rd, ha.rd]
  · rw [ht.wr, he.wr, hd.wr, hc.wr, ha.wr]
  · rw [ht.sp, he.sp, hd.sp, hc.sp, ha.sp]

open VG.WriteBytes
open VG.Spec.Blake2 (bytesAt)

/-- The prefix already copied, with every other register preserved. -/
structure CopyI (s₀ : State) (src dst : Addr) (k j : Nat) (s : State) : Prop where
  bound : j ≤ k
  source : s.gpr .r5 = src + BitVec.ofNat 64 j
  destination : s.gpr .r29 = dst + BitVec.ofNat 64 j
  count : s.gpr .r9 = BitVec.ofNat 64 (k - j)
  other : ∀ r, r ≠ .r9 → r ≠ .r6 → r ≠ .r5 → r ≠ .r29 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = writeBytes s₀.mem dst ((bytesAt s₀.mem src k).take j)

theorem copyLoop_ok (s₀ : State) (src dst : Addr) (k : Nat)
    (hk : 1 ≤ k) (hk' : k < 2 ^ 64)
    (hs : s₀.gpr .r5 = src) (hd : s₀.gpr .r29 = dst)
    (hn : s₀.gpr .r9 = BitVec.ofNat 64 k)
    (hr : ∀ i < k, InRegions (s₀.rd ++ s₀.wr) (src + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < k, InRegions s₀.wr (dst + BitVec.ofNat 64 i) 1)
    (hsep : Region.Disjoint ⟨src, k⟩ ⟨dst, k⟩) :
    WP isa (.loop (.block copyByte) (.nonzero .d .r9)) s₀ (CopyI s₀ src dst k k) := by
  refine WP.loop (M := isa) (fun n s => ∃ j, n = k - j ∧ j < k ∧ CopyI s₀ src dst k j s)
    ?_ k s₀ ⟨0, by omega_using [], hk, by omega_using [], by simpa using hs, by simpa using hd,
      by simpa using hn, fun _ _ _ _ _ => rfl, rfl, rfl, by rw [List.take_zero, writeBytes_nil]⟩
  rintro n s ⟨j, rfl, hj, h⟩
  have hlen : (bytesAt s₀.mem src k).length = k := by simp [bytesAt]
  have htake : ((bytesAt s₀.mem src k).take j).length = j := by
    rw [List.length_take, hlen, Nat.min_eq_left (by omega_using [hj])]
  have hb : s.mem (src + BitVec.ofNat 64 j) = s₀.mem (src + BitVec.ofNat 64 j) := by
    rw [h.mem]
    apply (writeBytes_frame s₀.mem dst _ (R := ⟨dst, k⟩)
      (by simpa only [BitVec.add_zero, htake] using
        (Offset.contains_base dst (k := k) (d := 0) (n := j) (by omega_using [hj]) (by decide)))).bytes
        (R := ⟨src, k⟩) _ (show k ≤ 2 ^ 64 by omega_using [hk']) hj
    simpa using hsep
  have hr' : InRegions (s.rd ++ s.wr) (s.gpr .r5) 1 := by
    rw [h.rd, h.wr, h.source]; exact hr j hj
  have hw' : InRegions s.wr (s.gpr .r29) 1 := by
    rw [h.wr, h.destination]; exact hw j hj
  refine (copyByte_ok s hr' hw').mono ?_
  rintro t ⟨hm, hs', hd', hn', ho, hrd, hwr, -⟩
  have hc : BitVec.ofNat 64 (k - j) - 1 = BitVec.ofNat 64 (k - (j + 1)) := by
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
      Offset.ofNat_sub_ofNat (by omega_using [hj] : 1 ≤ k - j)]
    congr 1
  have hi : CopyI s₀ src dst k (j + 1) t := by
    refine ⟨by omega_using [hj], ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_, hrd.trans h.rd, hwr.trans h.wr, ?_⟩
    · rw [hs', h.source, BitVec.ofNat_add, BitVec.add_assoc]; rfl
    · rw [hd', h.destination, BitVec.ofNat_add, BitVec.add_assoc]; rfl
    · rw [hn', h.count, hc]
    · exact (ho r h1 h2 h3 h4).trans (h.other r h1 h2 h3 h4)
    · have hj' : j < (bytesAt s₀.mem src k).length := by omega_using [hj, hlen]
      rw [hm, h.source, h.destination, hb, h.mem, List.take_add_one,
        List.getElem?_eq_getElem hj', Option.toList_some,
        writeBytes_snoc _ _ _ _ (by rw [htake]; omega_using [hk', hj]), htake]
      refine congrArg (fun b => (writeBytes s₀.mem dst ((bytesAt s₀.mem src k).take j)).writeW
        (dst + BitVec.ofNat 64 j) b) ?_
      simp only [bytesAt, List.getElem_map, List.getElem_range]
  have hz' : (t.gpr .r9 == 0) = decide (k - (j + 1) = 0) := by
    rw [hi.count]
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    constructor
    · intro he
      have ht := congrArg BitVec.toNat he
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hk'] : k - (j + 1) < 2 ^ 64),
        show (0 : BitVec 64).toNat = 0 from rfl] using ht
    · intro he; rw [he]; rfl
  by_cases he : j + 1 = k
  · refine .inl ⟨?_, he ▸ hi⟩
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, bne, hz', show k - (j + 1) = 0 by omega_using [he], decide_true, Bool.not_true]
  · refine .inr ⟨?_, k - (j + 1), by omega_using [hj], j + 1, rfl, by omega_using [hj, he], hi⟩
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, bne, hz', show k - (j + 1) ≠ 0 by omega_using [hj, he], decide_false, Bool.not_false]

end VG.Proof.Argon2.PPC64LE.HPrime

end

end


/-! # H′: emitting a digest or its 32-byte prefix -/

@[expose] public section

namespace VG.Proof.Argon2.PPC64LE.HPrime

open VG VG.PPC64LE VG.Impl.Argon2.PPC64LE.HPrime
open VG.Proof.MdStream.PPC64LE (wp_mov wp_addi wp_li wp_subi)
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
  output : t.gpr .r29 = s.gpr .r29 + BitVec.ofNat 64 k
  other : ∀ r, r ≠ .r9 → r ≠ .r6 → r ≠ .r5 → r ≠ .r29 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : t.mem = writeBytes s.mem (s.gpr .r29) (bytesAt s.mem (s.gpr .r31 + 768) k)

theorem copy_ok (s : State) (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 64)
    (count : s.gpr .r9 = BitVec.ofNat 64 k)
    (work : (⟨s.gpr .r31, 16384⟩ : Region) ∈ s.wr)
    (out : ∀ i < k, InRegions s.wr (s.gpr .r29 + BitVec.ofNat 64 i) 1)
    (sep : (⟨s.gpr .r31 + 768, k⟩ : Region).Disjoint ⟨s.gpr .r29, k⟩) :
    WP isa copy s (Copied s k) := by
  unfold copy
  refine WP.seq (wp_addi (by decide) fun u hu => WP.block_nil ?_)
  have src : u.gpr .r5 = s.gpr .r31 + 768 := by rw [hu.gpr]; rfl
  have other : ∀ r, r ≠ .r5 → u.gpr r = s.gpr r := fun r hr => hu.other r hr
  have mem : u.mem = s.mem := hu.mem
  have rd : u.rd = s.rd := hu.rd
  have wr : u.wr = s.wr := hu.wr
  have read : ∀ i < k, InRegions (u.rd ++ u.wr)
      (s.gpr .r31 + 768 + BitVec.ofNat 64 i) 1 := by
    intro i hi'
    rw [rd, wr, BitVec.add_assoc,
      show (768 : Addr) = BitVec.ofNat 64 768 from rfl, ← BitVec.ofNat_add]
    exact ⟨_, List.mem_append_right _ work,
      Offset.contains_base _ (by omega_using [hi, hi'] : 768 + i + 1 ≤ 16384) (by omega_using [hi, hi'])⟩
  have loop := copyLoop_ok u _ _ k lo (by omega_using [hi]) src (other .r29 (by decide))
    ((other .r9 (by decide)).trans count) read
    (by intro i hi'; rw [wr]; exact out i hi') sep
  obtain ⟨tr, t, he, ht⟩ := loop
  refine ⟨tr, t, he, ht.destination,
    fun r h1 h2 h3 h4 => (ht.other r h1 h2 h3 h4).trans (other r h3),
    ht.rd.trans rd, ht.wr.trans wr, (VG.PPC64LE.Exec.sp he).trans hu.sp, ?_⟩
  rw [ht.mem, mem, List.take_of_length_le]
  simp only [bytesAt, List.length_map, List.length_range, Nat.le_refl]

theorem Copied.frame {s t : State} {k : Nat} (h : Copied s k t) :
    Frame [⟨s.gpr .r29, k⟩] s.mem t.mem := by
  rw [h.mem]
  apply writeBytes_frame
  simpa only [bytesAt, List.length_map, List.length_range, BitVec.add_zero] using
    Offset.contains_base (s.gpr .r29) (d := 0) (n := k) (k := k) (by omega_using []) (by decide)

structure Emitted (s t : State) : Prop where
  output : t.gpr .r29 = s.gpr .r29 + 32
  remaining : t.gpr .r30 = s.gpr .r30 - 32
  other : ∀ r, r ≠ .r9 → r ≠ .r6 → r ≠ .r5 → r ≠ .r29 → r ≠ .r30 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : t.mem = writeBytes s.mem (s.gpr .r29) (bytesAt s.mem (s.gpr .r31 + 768) 32)

theorem emitPrefix_ok (s : State)
    (work : (⟨s.gpr .r31, 16384⟩ : Region) ∈ s.wr)
    (out : ∀ i < 32, InRegions s.wr (s.gpr .r29 + BitVec.ofNat 64 i) 1)
    (sep : (⟨s.gpr .r31 + 768, 32⟩ : Region).Disjoint ⟨s.gpr .r29, 32⟩) :
    WP isa emitPrefix s (Emitted s) := by
  unfold emitPrefix
  refine WP.seq (wp_li (by decide) fun a ha => WP.block_nil ?_)
  have base : a.gpr .r31 = s.gpr .r31 := ha.other _ (by decide)
  have dst : a.gpr .r29 = s.gpr .r29 := ha.other _ (by decide)
  have workA : (⟨a.gpr .r31, 16384⟩ : Region) ∈ a.wr := by rw [base, ha.wr]; exact work
  have outA : ∀ i < 32, InRegions a.wr (a.gpr .r29 + BitVec.ofNat 64 i) 1 := by
    rw [dst, ha.wr]; exact out
  have sepA : (⟨a.gpr .r31 + 768, 32⟩ : Region).Disjoint ⟨a.gpr .r29, 32⟩ := by
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
    Frame [⟨s.gpr .r29, 32⟩] s.mem t.mem := by
  rw [h.mem]
  apply writeBytes_frame
  simpa only [bytesAt, List.length_map, List.length_range, BitVec.add_zero] using
    Offset.contains_base (s.gpr .r29) (d := 0) (n := 32) (k := 32) (by decide) (by decide)

theorem Emitted.digest {s t : State} (h : Emitted s t)
    (sep : (⟨s.gpr .r31, 16384⟩ : Region).Disjoint ⟨s.gpr .r29, 32⟩) :
    bytesAt t.mem (s.gpr .r31 + 768) 64 = bytesAt s.mem (s.gpr .r31 + 768) 64 := by
  apply Proof.Blake2.bytesAt_congr
  intro i hi
  apply h.frame.bytes (R := ⟨s.gpr .r31 + 768, 64⟩) _ (show 64 ≤ 2 ^ 64 by decide) hi
  intro r hr
  simp only [List.mem_singleton] at hr; subst r
  exact sep.sub_left (Offset.sub_base _ (by decide : 768 + 64 ≤ 16384))

end VG.Proof.Argon2.PPC64LE.HPrime

end

end

/-! Merged from `Proof.Argon2.PPC64LE.HPrime.Next`. -/

@[expose] public section

section
/-! # H′: hashing the previous 64-byte digest -/

namespace VG.Proof.Argon2.PPC64LE.HPrime

open VG VG.PPC64LE VG.Impl.Argon2.PPC64LE.HPrime
open VG.Spec.Blake2 (b Repr bytesAt)
open VG.Proof.MdStream.PPC64LE (wp_li)

theorem next_ok (s : State)
    (hlen : 1 ≤ (s.gpr .r4).toNat ∧ (s.gpr .r4).toNat ≤ 64)
    (hsp : 48 ≤ s.sp.toNat)
    (hwr : (⟨s.gpr .r31, 16384⟩ : Region) ∈ s.wr)
    (stackWork : (below s.sp 48).Disjoint ⟨s.gpr .r31, 16384⟩) :
    WP isa (next) s fun t =>
      (bytesAt t.mem (s.gpr .r31 + 768) 64).take (s.gpr .r4).toNat =
        Spec.Argon2.H (s.gpr .r4).toNat (bytesAt s.mem (s.gpr .r31 + 768) 64) ∧ Keeps s t := by
  unfold next
  refine WP.seq ((init_ok s hlen hwr).mono ?_)
  rintro a ⟨reprA, regsA, rdA, wrA, spA, frameA⟩
  have ka : Keeps s a := ⟨regsA, rdA, wrA, spA, init_frame _ _ frameA⟩
  have digest : bytesAt a.mem (a.gpr .r31 + 768) 64 = bytesAt s.mem (s.gpr .r31 + 768) 64 := by
    rw [ka.r31]
    apply Proof.Blake2.bytesAt_congr
    intro i hi
    apply frameA.bytes (R := ⟨s.gpr .r31 + 768, 64⟩) _ (show 64 ≤ 2 ^ 64 by decide) hi
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact (Offset.base_disjoint _ (e := 768) (n := 64) (k := 192) (by decide) (by decide)).symm
  have reprA' : Repr b (Spec.Blake2.init b (s.gpr .r4).toNat 0) a.mem (a.gpr .r31) [] := by
    rw [ka.r31]; exact reprA
  have wrA' : (⟨a.gpr .r31, 16384⟩ : Region) ∈ a.wr := by rw [ka.r31, ka.wr]; exact hwr
  have swA : (below a.sp 48).Disjoint ⟨a.gpr .r31, 16384⟩ := by
    rw [ka.r31, ka.sp]; exact stackWork
  refine WP.seq ((absorbFixed_ok a _ 768 64 (by decide) (by rw [ka.sp]; exact hsp) (by decide) (by decide) reprA' wrA' swA).mono ?_)
  rintro u ⟨reprU, ku⟩
  have ksu := ka.trans ku
  have reprU' : Repr b (Spec.Blake2.init b (s.gpr .r4).toNat 0) u.mem (u.gpr .r31)
      (bytesAt s.mem (s.gpr .r31 + 768) 64) := by
    rw [ku.r31]
    simpa only [show BitVec.ofNat 64 768 = (768 : Addr) from rfl, digest] using reprU
  refine WP.seq (wp_li (by decide) fun w hw => WP.block_nil ?_)
  have kw : Keeps u w := by
    refine ⟨fun r hr => ?_, hw.rd, hw.wr, hw.sp, ?_⟩
    · exact hw.other r (preserved_ne hr)
    · rw [hw.mem]; exact Frame.refl _ _
  have ksw := ksu.trans kw
  have reprW : Repr b (Spec.Blake2.init b (s.gpr .r4).toNat 0) w.mem (w.gpr .r31)
      (bytesAt s.mem (s.gpr .r31 + 768) 64) := by
    rw [hw.mem, kw.r31]; exact reprU'
  have length : (bytesAt s.mem (s.gpr .r31 + 768) 64).length = 64 := by
    simp only [bytesAt, List.length_map, List.length_range]
  have count : w.gpr .r4 = BitVec.ofNat 64 (bytesAt s.mem (s.gpr .r31 + 768) 64).length := by
    rw [length]; exact hw.gpr
  have bound : (bytesAt s.mem (s.gpr .r31 + 768) 64).length < 2 ^ 64 := by rw [length]; decide
  have wrW : (⟨w.gpr .r31, 16384⟩ : Region) ∈ w.wr := by rw [ksw.r31, ksw.wr]; exact hwr
  have swW : (below w.sp 48).Disjoint ⟨w.gpr .r31, 16384⟩ := by
    rw [ksw.r31, ksw.sp]; exact stackWork
  refine (finalize_ok w _ _ reprW count bound (by rw [ksw.sp]; exact hsp) wrW swW).mono ?_
  rintro t ⟨out, regsT, rdT, wrT, spT, frameT⟩
  refine ⟨?_, ksw.trans ⟨regsT, rdT, wrT, spT, finalize_frame _ _ frameT⟩⟩
  have result := congrArg (List.take (s.gpr .r4).toNat) out
  rw [ksw.r31] at result
  exact result.trans (Proof.Argon2.H_stream _ _).symm

end VG.Proof.Argon2.PPC64LE.HPrime
end

/-! Merged from `Proof.Argon2.PPC64LE.HPrime.ChainStep`. -/
section
/-! # H′: one hash-and-prefix iteration -/

namespace VG.Proof.Argon2.PPC64LE.HPrime

open VG VG.PPC64LE VG.Impl.Argon2.PPC64LE.HPrime
open VG.Proof.MdStream.PPC64LE (wp_li)
open VG.Spec.Blake2 (bytesAt)

structure ChainStep (s t : State) : Prop where
  output : t.gpr .r29 = s.gpr .r29 + 32
  remaining : t.gpr .r30 = s.gpr .r30 - 32
  regs : ∀ r ∈ preserved, r ≠ .r29 → r ≠ .r30 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame [⟨s.gpr .r31, 832⟩, below s.sp 48, ⟨s.gpr .r29, 32⟩] s.mem t.mem
  digest : bytesAt t.mem (s.gpr .r31 + 768) 64 =
    Spec.Argon2.H 64 (bytesAt s.mem (s.gpr .r31 + 768) 64)
  bytes : bytesAt t.mem (s.gpr .r29) 32 =
    (Spec.Argon2.H 64 (bytesAt s.mem (s.gpr .r31 + 768) 64)).take 32
  comparison : t.gpr .r10 = if (s.gpr .r30 - 32).toNat < 65 then 1 else 0

theorem chainStep_ok (s : State)
    (hsp : 48 ≤ s.sp.toNat)
    (remainingBound : 32 ≤ (s.gpr .r30).toNat ∧ (s.gpr .r30).toNat < 2 ^ 32)
    (work : (⟨s.gpr .r31, 16384⟩ : Region) ∈ s.wr)
    (out : ∀ i < 32, InRegions s.wr (s.gpr .r29 + BitVec.ofNat 64 i) 1)
    (sep : (⟨s.gpr .r31, 16384⟩ : Region).Disjoint ⟨s.gpr .r29, 32⟩)
    (stackWork : (below s.sp 48).Disjoint ⟨s.gpr .r31, 16384⟩) :
    WP isa (.seq (.block [.li .r4 64]) (.seq next (.seq emitPrefix (.block cmpLeft))))
      s (ChainStep s) := by
  refine WP.seq (wp_li (by decide) fun a ha => WP.block_nil ?_)
  have ka : Keeps s a := Keeps.of_upd ha (by decide)
  have workA : (⟨a.gpr .r31, 16384⟩ : Region) ∈ a.wr := by rw [ka.r31, ka.wr]; exact work
  have stackA : (below a.sp 48).Disjoint ⟨a.gpr .r31, 16384⟩ := by
    rw [ka.r31, ka.sp]; exact stackWork
  have lengthA : (a.gpr .r4).toNat = 64 := by rw [ha.gpr]; rfl
  refine WP.seq ((next_ok a (by rw [lengthA]; decide) (by rw [ka.sp]; exact hsp) workA stackA).mono ?_)
  rintro u ⟨du, ku⟩
  have ksu := ka.trans ku
  have dstU : u.gpr .r29 = s.gpr .r29 := ksu.regs _ (by decide)
  have digestU : bytesAt u.mem (s.gpr .r31 + 768) 64 =
      Spec.Argon2.H 64 (bytesAt s.mem (s.gpr .r31 + 768) 64) := by
    simpa only [lengthA, ka.r31, ha.mem, bytesAt_take _ _ 64 64 (by decide)] using du
  have workU : (⟨u.gpr .r31, 16384⟩ : Region) ∈ u.wr := by rw [ksu.r31, ksu.wr]; exact work
  have outU : ∀ i < 32, InRegions u.wr (u.gpr .r29 + BitVec.ofNat 64 i) 1 := by
    rw [ksu.wr, dstU]; exact out
  have sepU : (⟨u.gpr .r31 + 768, 32⟩ : Region).Disjoint ⟨u.gpr .r29, 32⟩ := by
    rw [ksu.r31, dstU]
    exact sep.sub_left (Offset.sub_base _ (by decide : 768 + 32 ≤ 16384))
  refine WP.seq ((emitPrefix_ok u workU outU sepU).mono ?_)
  intro w hw
  have remainingW : (w.gpr .r30).toNat < 2 ^ 32 := by
    rw [hw.remaining, ksu.regs _ (by decide),
      BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact remainingBound.1)]
    exact Nat.lt_of_le_of_lt (Nat.sub_le ..) remainingBound.2
  refine (compare_ok w remainingW).mono fun t compared => ?_
  have gt := compared.other
  have mt := compared.mem
  have rt := compared.rd
  have wt := compared.wr
  have fw : Frame [⟨s.gpr .r29, 32⟩] u.mem w.mem := by
    rw [← dstU]; exact hw.frame
  refine ⟨?_, ?_, fun r hr h14 h15 => ?_, rt.trans (hw.rd.trans ksu.rd),
    wt.trans (hw.wr.trans ksu.wr), compared.sp.trans (hw.sp.trans ksu.sp), ?_, ?_, ?_, ?_⟩
  · rw [gt _ (by decide), hw.output, dstU]
  · rw [gt _ (by decide), hw.remaining, ksu.regs _ (by decide)]
  · rw [gt r (preserved_ne hr)]
    exact (hw.other r (preserved_ne hr) (preserved_ne hr) (preserved_ne hr) h14 h15).trans
      (ksu.regs r hr)
  · rw [mt]
    apply Frame.trans (ksu.frame.sub ?_) (fw.sub ?_)
    · intro r hr
      exact ⟨r, List.mem_append_left _ hr, fun _ hx => hx⟩
    · intro r hr
      exact ⟨r, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr), fun _ hx => hx⟩
  · rw [mt, ← digestU]
    apply Proof.Blake2.bytesAt_congr
    intro i hi
    apply fw.bytes (R := ⟨s.gpr .r31 + 768, 64⟩) _ (show 64 ≤ 2 ^ 64 by decide) hi
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact sep.sub_left (Offset.sub_base _ (by decide : 768 + 64 ≤ 16384))
  · rw [mt, hw.mem, dstU, ksu.r31, ← digestU, bytesAt_take _ _ 32 64 (by decide)]
    exact bytesAt_writeBytes _ _ _ (by simp only [bytesAt, List.length_map, List.length_range]; decide)
  · rw [compared.value, hw.remaining, ksu.regs _ (by decide)]

end VG.Proof.Argon2.PPC64LE.HPrime
end

/-! # H′: repeating the hash-and-prefix iteration -/

namespace VG.Proof.Argon2.PPC64LE.HPrime

open VG VG.PPC64LE VG.Impl.Argon2.PPC64LE.HPrime
open VG.Spec.Blake2 (bytesAt)
open VG.Proof.Argon2 (chainDigest chainPrefixes)
open VG.Proof.MdStream.PPC64LE (eval_zero)

structure ChainResult (s : State) (n : Nat) (t : State) : Prop where
  output : t.gpr .r29 = s.gpr .r29 + BitVec.ofNat 64 (32 * n)
  remaining : t.gpr .r30 = s.gpr .r30 - BitVec.ofNat 64 (32 * n)
  regs : ∀ r ∈ preserved, r ≠ .r29 → r ≠ .r30 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame [⟨s.gpr .r31, 832⟩, below s.sp 48, ⟨s.gpr .r29, 32 * n⟩] s.mem t.mem
  digest : bytesAt t.mem (s.gpr .r31 + 768) 64 =
    chainDigest n (bytesAt s.mem (s.gpr .r31 + 768) 64)
  bytes : bytesAt t.mem (s.gpr .r29) (32 * n) =
    chainPrefixes n (bytesAt s.mem (s.gpr .r31 + 768) 64)

theorem ChainResult.refl (s : State) : ChainResult s 0 s :=
  ⟨by simp, by simp, fun _ _ _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, rfl, rfl⟩

theorem ChainResult.cons {s u t : State} {n : Nat} (step : ChainStep s u)
    (tail : ChainResult u n t) (bound : 32 * (n + 1) < 2 ^ 64)
    (sep : (⟨s.gpr .r31, 16384⟩ : Region).Disjoint ⟨s.gpr .r29, 32 * (n + 1)⟩)
    (stackOut : (below s.sp 48).Disjoint ⟨s.gpr .r29, 32 * (n + 1)⟩) :
    ChainResult s (n + 1) t := by
  have base := step.regs .r31 (by decide) (by decide) (by decide)
  have sp := step.sp
  have sum : 32 * (n + 1) = 32 + 32 * n := by omega_arith
  have sumBV : BitVec.ofNat 64 (32 * (n + 1)) = 32 + BitVec.ofNat 64 (32 * n) := by
    rw [sum, BitVec.ofNat_add]; rfl
  have tf : Frame [⟨s.gpr .r31, 832⟩, below s.sp 48,
      ⟨s.gpr .r29 + 32, 32 * n⟩] u.mem t.mem := by
    rw [← base, ← sp, ← step.output]; exact tail.frame
  have extend {m m' : Mem} (d k : Nat) (hk : d + k ≤ 32 * (n + 1))
      (h : Frame [⟨s.gpr .r31, 832⟩, below s.sp 48,
        ⟨s.gpr .r29 + BitVec.ofNat 64 d, k⟩] m m') :
      Frame [⟨s.gpr .r31, 832⟩, below s.sp 48, ⟨s.gpr .r29, 32 * (n + 1)⟩] m m' := by
    apply h.sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ hx => hx⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ hx => hx⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)),
        Offset.sub_base _ hk⟩
  refine ⟨?_, ?_, fun r hr h1 h2 => (tail.regs r hr h1 h2).trans (step.regs r hr h1 h2),
    tail.rd.trans step.rd, tail.wr.trans step.wr, tail.sp.trans step.sp, ?_, ?_, ?_⟩
  · rw [tail.output, step.output, sumBV, BitVec.add_assoc]
  · rw [tail.remaining, step.remaining, sumBV, BitVec.sub_sub]
  · exact (extend 0 32 (by omega_arith) (by simpa only [BitVec.add_zero] using step.frame)).trans
      (extend 32 (32 * n) (by omega_arith) tf)
  · rw [← base, tail.digest, base, step.digest, Proof.Argon2.chainDigest]
  · have before : bytesAt t.mem (s.gpr .r29) 32 = bytesAt u.mem (s.gpr .r29) 32 := by
      apply Proof.Blake2.bytesAt_congr
      intro i hi
      apply tf.bytes (R := ⟨s.gpr .r29, 32⟩) _ (show 32 ≤ 2 ^ 64 by decide) hi
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

theorem chain_ok (n lastLen : Nat) (s : State)
    (positive : 1 ≤ n) (last : 33 ≤ lastLen ∧ lastLen ≤ 64)
    (bound : 32 * n + lastLen < 2 ^ 32)
    (hsp : 48 ≤ s.sp.toNat)
    (count : s.gpr .r30 = BitVec.ofNat 64 (32 * n + lastLen))
    (work : (⟨s.gpr .r31, 16384⟩ : Region) ∈ s.wr)
    (out : ∀ i < 32 * n, InRegions s.wr (s.gpr .r29 + BitVec.ofNat 64 i) 1)
    (sep : (⟨s.gpr .r31, 16384⟩ : Region).Disjoint ⟨s.gpr .r29, 32 * n⟩)
    (stackWork : (below s.sp 48).Disjoint ⟨s.gpr .r31, 16384⟩)
    (stackOut : (below s.sp 48).Disjoint ⟨s.gpr .r29, 32 * n⟩) :
    WP isa (chain) s (ChainResult s n) := by
  induction n generalizing s with
  | zero => omega_arith
  | succ n ih =>
    have out32 : ∀ i < 32, InRegions s.wr (s.gpr .r29 + BitVec.ofNat 64 i) 1 :=
      fun i hi => out i (by omega_arith)
    have sep32 := sep.sub_right (Region.sub_prefix (show 32 ≤ 32 * (n + 1) by omega_arith))
    obtain ⟨trace, u, run, step⟩ := chainStep_ok s hsp
      (by rw [count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]; omega_arith) work out32 sep32 stackWork
    have base := step.regs .r31 (by decide) (by decide) (by decide)
    have sp := step.sp
    have countU : u.gpr .r30 = BitVec.ofNat 64 (32 * n + lastLen) := by
      rw [step.remaining, count, show (32 : Addr) = BitVec.ofNat 64 32 from rfl,
        Offset.ofNat_sub_ofNat (by omega_arith : 32 ≤ 32 * (n + 1) + lastLen)]
      rw [show 32 * (n + 1) + lastLen - 32 = 32 * n + lastLen by omega_arith]
    have compareU : u.gpr .r10 = if 32 * n + lastLen < 65 then 1 else 0 := by
      rw [step.comparison, ← step.remaining, countU, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
    cases n with
    | zero =>
      have flag : isa.eval (.zero .d .r10) u = some false := by
        show VG.PPC64LE.eval (.zero .d .r10) u = _
        simp [eval_zero, compareU, show lastLen < 65 by omega_arith]
      exact ⟨_, u, .loopExit run flag, (ChainResult.refl u).cons step (by omega_arith) sep stackOut⟩
    | succ n =>
      have workU : (⟨u.gpr .r31, 16384⟩ : Region) ∈ u.wr := by rw [base, step.wr]; exact work
      have outU : ∀ i < 32 * (n + 1), InRegions u.wr (u.gpr .r29 + BitVec.ofNat 64 i) 1 := by
        intro i hi
        rw [step.wr, step.output, BitVec.add_assoc,
          show (32 : Addr) = BitVec.ofNat 64 32 from rfl, ← BitVec.ofNat_add]
        exact out (32 + i) (by omega_arith)
      have suffix : Region.Sub ⟨u.gpr .r29, 32 * (n + 1)⟩ ⟨s.gpr .r29, 32 * (n + 1 + 1)⟩ := by
        rw [step.output]
        exact Offset.sub_base _ (by omega_arith : 32 + 32 * (n + 1) ≤ 32 * (n + 1 + 1))
      have sepU : (⟨u.gpr .r31, 16384⟩ : Region).Disjoint ⟨u.gpr .r29, 32 * (n + 1)⟩ := by
        rw [base]; exact sep.sub_right suffix
      have swU : (below u.sp 48).Disjoint ⟨u.gpr .r31, 16384⟩ := by
        rw [sp, base]; exact stackWork
      have soU : (below u.sp 48).Disjoint ⟨u.gpr .r29, 32 * (n + 1)⟩ := by
        rw [sp]; exact stackOut.sub_right suffix
      obtain ⟨trace', t, run', result⟩ := ih u (by omega_arith) (by omega_arith) (by rw [sp]; exact hsp) countU workU outU sepU swU soU
      have flag : isa.eval (.zero .d .r10) u = some true := by
        show VG.PPC64LE.eval (.zero .d .r10) u = _
        simp [eval_zero, compareU, show ¬ 32 * (n + 1) + lastLen < 65 by omega_arith]
      exact ⟨_, t, .loopNext run flag run', result.cons step (by omega_arith) sep stackOut⟩

end VG.Proof.Argon2.PPC64LE.HPrime
