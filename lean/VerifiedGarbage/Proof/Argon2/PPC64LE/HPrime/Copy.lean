module

public import VerifiedGarbage.Impl.Argon2.PPC64LE.HPrime
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.MdStream.PPC64LE.Common
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Blake2
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

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
    ?_ k s₀ ⟨0, by omega, hk, by omega, by simpa using hs, by simpa using hd,
      by simpa using hn, fun _ _ _ _ _ => rfl, rfl, rfl, by rw [List.take_zero, writeBytes_nil]⟩
  rintro n s ⟨j, rfl, hj, h⟩
  have hlen : (bytesAt s₀.mem src k).length = k := by simp [bytesAt]
  have htake : ((bytesAt s₀.mem src k).take j).length = j := by
    rw [List.length_take, hlen, Nat.min_eq_left (by omega)]
  have hb : s.mem (src + BitVec.ofNat 64 j) = s₀.mem (src + BitVec.ofNat 64 j) := by
    rw [h.mem]
    apply (writeBytes_frame s₀.mem dst _ (R := ⟨dst, k⟩)
      (by simpa only [BitVec.add_zero, htake] using
        (Offset.contains_base dst (k := k) (d := 0) (n := j) (by omega) (by decide)))).bytes
        (R := ⟨src, k⟩) _ (show k ≤ 2 ^ 64 by omega) hj
    simpa using hsep
  have hr' : InRegions (s.rd ++ s.wr) (s.gpr .r5) 1 := by
    rw [h.rd, h.wr, h.source]; exact hr j hj
  have hw' : InRegions s.wr (s.gpr .r29) 1 := by
    rw [h.wr, h.destination]; exact hw j hj
  refine (copyByte_ok s hr' hw').mono ?_
  rintro t ⟨hm, hs', hd', hn', ho, hrd, hwr, -⟩
  have hc : BitVec.ofNat 64 (k - j) - 1 = BitVec.ofNat 64 (k - (j + 1)) := by
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
      Offset.ofNat_sub_ofNat (by omega : 1 ≤ k - j)]
    congr 1
  have hi : CopyI s₀ src dst k (j + 1) t := by
    refine ⟨by omega, ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_, hrd.trans h.rd, hwr.trans h.wr, ?_⟩
    · rw [hs', h.source, BitVec.ofNat_add, BitVec.add_assoc]; rfl
    · rw [hd', h.destination, BitVec.ofNat_add, BitVec.add_assoc]; rfl
    · rw [hn', h.count, hc]
    · exact (ho r h1 h2 h3 h4).trans (h.other r h1 h2 h3 h4)
    · have hj' : j < (bytesAt s₀.mem src k).length := by omega
      rw [hm, h.source, h.destination, hb, h.mem, List.take_add_one,
        List.getElem?_eq_getElem hj', Option.toList_some,
        writeBytes_snoc _ _ _ _ (by rw [htake]; omega), htake]
      refine congrArg (fun b => (writeBytes s₀.mem dst ((bytesAt s₀.mem src k).take j)).writeW
        (dst + BitVec.ofNat 64 j) b) ?_
      simp only [bytesAt, List.getElem_map, List.getElem_range]
  have hz' : (t.gpr .r9 == 0) = decide (k - (j + 1) = 0) := by
    rw [hi.count]
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    constructor
    · intro he
      have ht := congrArg BitVec.toNat he
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : k - (j + 1) < 2 ^ 64),
        show (0 : BitVec 64).toNat = 0 from rfl] using ht
    · intro he; rw [he]; rfl
  by_cases he : j + 1 = k
  · refine .inl ⟨?_, he ▸ hi⟩
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, bne, hz', show k - (j + 1) = 0 by omega, decide_true, Bool.not_true]
  · refine .inr ⟨?_, k - (j + 1), by omega, j + 1, rfl, by omega, hi⟩
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, bne, hz', show k - (j + 1) ≠ 0 by omega, decide_false, Bool.not_false]

end VG.Proof.Argon2.PPC64LE.HPrime
