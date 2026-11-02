module
import VerifiedGarbage.Proof.Argon2.RISCV64.HPrime.Calls
public import VerifiedGarbage.Proof.Argon2.RISCV64.HPrime.Frame
public import VerifiedGarbage.Proof.Argon2.HPrime

import VerifiedGarbage.Proof.Argon2.RISCV64.HPrime.Compare
import VerifiedGarbage.Proof.Argon2.RISCV64.HPrime.Output
import VerifiedGarbage.Proof.Argon2.RISCV64.HPrime.Absorb
import VerifiedGarbage.Proof.Argon2.RISCV64.HPrime.Length
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Blake2.RISCV64.Stream.Lit
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Argon2.RISCV64.HPrime
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill

/-! Merged from `Proof.Argon2.RISCV64.HPrime.Next`. -/

@[expose] public section

section
/-! # H′: hashing the previous 64-byte digest -/

namespace VG.Proof.Argon2.RISCV64.HPrime

open VG VG.RISCV64 VG.Impl.Argon2.RISCV64.HPrime
open VG.Spec.Blake2 (b Repr bytesAt)
open VG.RISCV64.Wp (wp_li)

theorem next_ok (s : State)
    (hlen : 1 ≤ (s.gpr .a1).toNat ∧ (s.gpr .a1).toNat ≤ 64)
    (hwr : (⟨s.gpr .s4, 16384⟩ : Region) ∈ s.wr) :
    WP isa (next) s fun t =>
      (bytesAt t.mem (s.gpr .s4 + 768) 64).take (s.gpr .a1).toNat =
        Spec.Argon2.H (s.gpr .a1).toNat (bytesAt s.mem (s.gpr .s4 + 768) 64) ∧ Keeps s t := by
  unfold next
  refine WP.seq ((init_ok s hlen hwr).mono ?_)
  rintro a ⟨reprA, regsA, rdA, wrA, spA, frameA⟩
  have ka : Keeps s a := ⟨regsA, rdA, wrA, spA, init_frame _ frameA⟩
  have digest : bytesAt a.mem (a.gpr .s4 + 768) 64 = bytesAt s.mem (s.gpr .s4 + 768) 64 := by
    rw [ka.s4]
    apply Proof.Blake2.bytesAt_congr
    intro i hi
    apply frameA.bytes (R := ⟨s.gpr .s4 + 768, 64⟩) _ (show 64 ≤ 2 ^ 64 by decide) hi
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact (Offset.base_disjoint _ (e := 768) (n := 64) (k := 192) (by decide) (by decide)).symm
  have reprA' : Repr b (Spec.Blake2.init b (s.gpr .a1).toNat 0) a.mem (a.gpr .s4) [] := by
    rw [ka.s4]; exact reprA
  have wrA' : (⟨a.gpr .s4, 16384⟩ : Region) ∈ a.wr := by rw [ka.s4, ka.wr]; exact hwr
  refine WP.seq ((absorbFixed_ok a _ 768 64 (by decide) (by decide) (by decide) (by decide) reprA' wrA').mono ?_)
  rintro u ⟨reprU, ku⟩
  have ksu := ka.trans ku
  have reprU' : Repr b (Spec.Blake2.init b (s.gpr .a1).toNat 0) u.mem (u.gpr .s4)
      (bytesAt s.mem (s.gpr .s4 + 768) 64) := by
    rw [ku.s4]
    simpa only [show BitVec.ofNat 64 768 = (768 : Addr) from rfl, digest] using reprU
  refine WP.seq (wp_li (by decide) fun w hw => WP.block_nil ?_)
  have kw : Keeps u w := by
    refine ⟨fun r hr => ?_, hw.rd, hw.wr, hw.sp, ?_⟩
    · exact hw.other r (preserved_ne hr)
    · rw [hw.mem]; exact Frame.refl _ _
  have ksw := ksu.trans kw
  have reprW : Repr b (Spec.Blake2.init b (s.gpr .a1).toNat 0) w.mem (w.gpr .s4)
      (bytesAt s.mem (s.gpr .s4 + 768) 64) := by
    rw [hw.mem, kw.s4]; exact reprU'
  have length : (bytesAt s.mem (s.gpr .s4 + 768) 64).length = 64 := by
    simp only [bytesAt, List.length_map, List.length_range]
  have count : w.gpr .a1 = BitVec.ofNat 64 (bytesAt s.mem (s.gpr .s4 + 768) 64).length := by
    rw [length]; exact hw.gpr
  have bound : (bytesAt s.mem (s.gpr .s4 + 768) 64).length < 2 ^ 64 := by rw [length]; decide
  have wrW : (⟨w.gpr .s4, 16384⟩ : Region) ∈ w.wr := by rw [ksw.s4, ksw.wr]; exact hwr
  refine (finalize_ok w _ _ reprW count bound wrW).mono ?_
  rintro t ⟨out, regsT, rdT, wrT, spT, frameT⟩
  refine ⟨?_, ksw.trans ⟨regsT, rdT, wrT, spT, finalize_frame _ frameT⟩⟩
  have result := congrArg (List.take (s.gpr .a1).toNat) out
  rw [ksw.s4] at result
  exact result.trans (Proof.Argon2.H_stream _ _).symm

end VG.Proof.Argon2.RISCV64.HPrime
end

/-! Merged from `Proof.Argon2.RISCV64.HPrime.ChainStep`. -/
section
/-! # H′: one hash-and-prefix iteration -/

namespace VG.Proof.Argon2.RISCV64.HPrime

open VG VG.RISCV64 VG.Impl.Argon2.RISCV64.HPrime
open VG.RISCV64.Wp (wp_li)
open VG.Spec.Blake2 (bytesAt)

structure ChainStep (s t : State) : Prop where
  output : t.gpr .s2 = s.gpr .s2 + 32
  remaining : t.gpr .s3 = s.gpr .s3 - 32
  regs : ∀ r ∈ preserved, r ≠ .s2 → r ≠ .s3 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame [⟨s.gpr .s4, 832⟩, ⟨s.gpr .s2, 32⟩] s.mem t.mem
  digest : bytesAt t.mem (s.gpr .s4 + 768) 64 =
    Spec.Argon2.H 64 (bytesAt s.mem (s.gpr .s4 + 768) 64)
  bytes : bytesAt t.mem (s.gpr .s2) 32 =
    (Spec.Argon2.H 64 (bytesAt s.mem (s.gpr .s4 + 768) 64)).take 32
  comparison : t.gpr .a7 = if (s.gpr .s3 - 32).toNat < 65 then 1 else 0

theorem chainStep_ok (s : State)
    (remainingBound : 32 ≤ (s.gpr .s3).toNat ∧ (s.gpr .s3).toNat < 2 ^ 32)
    (work : (⟨s.gpr .s4, 16384⟩ : Region) ∈ s.wr)
    (out : ∀ i < 32, InRegions s.wr (s.gpr .s2 + BitVec.ofNat 64 i) 1)
    (sep : (⟨s.gpr .s4, 16384⟩ : Region).Disjoint ⟨s.gpr .s2, 32⟩) :
    WP isa (.seq (.block [.li .a1 64]) (.seq next (.seq emitPrefix (.block cmpLeft))))
      s (ChainStep s) := by
  refine WP.seq (wp_li (by decide) fun a ha => WP.block_nil ?_)
  have ka : Keeps s a := Keeps.of_upd ha (by decide)
  have workA : (⟨a.gpr .s4, 16384⟩ : Region) ∈ a.wr := by rw [ka.s4, ka.wr]; exact work
  have lengthA : (a.gpr .a1).toNat = 64 := by rw [ha.gpr]; rfl
  refine WP.seq ((next_ok a (by rw [lengthA]; decide) workA).mono ?_)
  rintro u ⟨du, ku⟩
  have ksu := ka.trans ku
  have dstU : u.gpr .s2 = s.gpr .s2 := ksu.regs _ (by decide)
  have digestU : bytesAt u.mem (s.gpr .s4 + 768) 64 =
      Spec.Argon2.H 64 (bytesAt s.mem (s.gpr .s4 + 768) 64) := by
    simpa only [lengthA, ka.s4, ha.mem, bytesAt_take _ _ 64 64 (by decide)] using du
  have workU : (⟨u.gpr .s4, 16384⟩ : Region) ∈ u.wr := by rw [ksu.s4, ksu.wr]; exact work
  have outU : ∀ i < 32, InRegions u.wr (u.gpr .s2 + BitVec.ofNat 64 i) 1 := by
    rw [ksu.wr, dstU]; exact out
  have sepU : (⟨u.gpr .s4 + 768, 32⟩ : Region).Disjoint ⟨u.gpr .s2, 32⟩ := by
    rw [ksu.s4, dstU]
    exact sep.sub_left (Offset.sub_base _ (by decide : 768 + 32 ≤ 16384))
  refine WP.seq ((emitPrefix_ok u workU outU sepU).mono ?_)
  intro w hw
  have remainingW : (w.gpr .s3).toNat < 2 ^ 32 := by
    rw [hw.remaining, ksu.regs _ (by decide),
      BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact remainingBound.1)]
    exact Nat.lt_of_le_of_lt (Nat.sub_le ..) remainingBound.2
  refine (compare_ok w remainingW).mono fun t compared => ?_
  have gt := compared.other
  have mt := compared.mem
  have rt := compared.rd
  have wt := compared.wr
  have fw : Frame [⟨s.gpr .s2, 32⟩] u.mem w.mem := by
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
      exact ⟨r, List.mem_cons_of_mem _ hr, fun _ hx => hx⟩
  · rw [mt, ← digestU]
    apply Proof.Blake2.bytesAt_congr
    intro i hi
    apply fw.bytes (R := ⟨s.gpr .s4 + 768, 64⟩) _ (show 64 ≤ 2 ^ 64 by decide) hi
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact sep.sub_left (Offset.sub_base _ (by decide : 768 + 64 ≤ 16384))
  · rw [mt, hw.mem, dstU, ksu.s4, ← digestU, bytesAt_take _ _ 32 64 (by decide)]
    exact bytesAt_writeBytes _ _ _ (by simp only [bytesAt, List.length_map, List.length_range]; decide)
  · rw [compared.value, hw.remaining, ksu.regs _ (by decide)]

end VG.Proof.Argon2.RISCV64.HPrime
end

/-! # H′: repeating the hash-and-prefix iteration -/

namespace VG.Proof.Argon2.RISCV64.HPrime

open VG VG.RISCV64 VG.Impl.Argon2.RISCV64.HPrime
open VG.Spec.Blake2 (bytesAt)
open VG.Proof.Argon2 (chainDigest chainPrefixes)
open VG.RISCV64.Wp (eval_zero)

structure ChainResult (s : State) (n : Nat) (t : State) : Prop where
  output : t.gpr .s2 = s.gpr .s2 + BitVec.ofNat 64 (32 * n)
  remaining : t.gpr .s3 = s.gpr .s3 - BitVec.ofNat 64 (32 * n)
  regs : ∀ r ∈ preserved, r ≠ .s2 → r ≠ .s3 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame [⟨s.gpr .s4, 832⟩, ⟨s.gpr .s2, 32 * n⟩] s.mem t.mem
  digest : bytesAt t.mem (s.gpr .s4 + 768) 64 =
    chainDigest n (bytesAt s.mem (s.gpr .s4 + 768) 64)
  bytes : bytesAt t.mem (s.gpr .s2) (32 * n) =
    chainPrefixes n (bytesAt s.mem (s.gpr .s4 + 768) 64)

theorem ChainResult.refl (s : State) : ChainResult s 0 s :=
  ⟨by simp, by simp, fun _ _ _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, rfl, rfl⟩

theorem ChainResult.cons {s u t : State} {n : Nat} (step : ChainStep s u)
    (tail : ChainResult u n t) (bound : 32 * (n + 1) < 2 ^ 64)
    (sep : (⟨s.gpr .s4, 16384⟩ : Region).Disjoint ⟨s.gpr .s2, 32 * (n + 1)⟩) :
    ChainResult s (n + 1) t := by
  have base := step.regs .s4 (by decide) (by decide) (by decide)
  have sum : 32 * (n + 1) = 32 + 32 * n := by omega_arith
  have sumBV : BitVec.ofNat 64 (32 * (n + 1)) = 32 + BitVec.ofNat 64 (32 * n) := by
    rw [sum, BitVec.ofNat_add]; rfl
  have tf : Frame [⟨s.gpr .s4, 832⟩,
      ⟨s.gpr .s2 + 32, 32 * n⟩] u.mem t.mem := by
    rw [← base, ← step.output]; exact tail.frame
  have extend {m m' : Mem} (d k : Nat) (hk : d + k ≤ 32 * (n + 1))
      (h : Frame [⟨s.gpr .s4, 832⟩,
        ⟨s.gpr .s2 + BitVec.ofNat 64 d, k⟩] m m') :
      Frame [⟨s.gpr .s4, 832⟩, ⟨s.gpr .s2, 32 * (n + 1)⟩] m m' := by
    apply h.sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ hx => hx⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Offset.sub_base _ hk⟩
  refine ⟨?_, ?_, fun r hr h1 h2 => (tail.regs r hr h1 h2).trans (step.regs r hr h1 h2),
    tail.rd.trans step.rd, tail.wr.trans step.wr, tail.sp.trans step.sp, ?_, ?_, ?_⟩
  · rw [tail.output, step.output, sumBV, BitVec.add_assoc]
  · rw [tail.remaining, step.remaining, sumBV, BitVec.sub_sub]
  · exact (extend 0 32 (by omega_arith) (by simpa only [BitVec.add_zero] using step.frame)).trans
      (extend 32 (32 * n) (by omega_arith) tf)
  · rw [← base, tail.digest, base, step.digest, Proof.Argon2.chainDigest]
  · have before : bytesAt t.mem (s.gpr .s2) 32 = bytesAt u.mem (s.gpr .s2) 32 := by
      apply Proof.Blake2.bytesAt_congr
      intro i hi
      apply tf.bytes (R := ⟨s.gpr .s2, 32⟩) _ (show 32 ≤ 2 ^ 64 by decide) hi
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (sep.sub_left (Region.sub_prefix (show 832 ≤ 16384 by decide))).symm.sub_left
          (Region.sub_prefix (show 32 ≤ 32 * (n + 1) by omega_arith))
      · exact Offset.base_disjoint _ (e := 32) (n := 32 * n) (k := 32) (by decide) (by omega_arith)
    rw [sum, Proof.Blake2.bytesAt_add, before, step.bytes,
      show BitVec.ofNat 64 32 = (32 : Addr) from rfl, ← step.output, tail.bytes,
      base, step.digest]
    rw [Proof.Argon2.chainPrefixes]

theorem chain_ok (n lastLen : Nat) (s : State)
    (positive : 1 ≤ n) (last : 33 ≤ lastLen ∧ lastLen ≤ 64)
    (bound : 32 * n + lastLen < 2 ^ 32)
    (count : s.gpr .s3 = BitVec.ofNat 64 (32 * n + lastLen))
    (work : (⟨s.gpr .s4, 16384⟩ : Region) ∈ s.wr)
    (out : ∀ i < 32 * n, InRegions s.wr (s.gpr .s2 + BitVec.ofNat 64 i) 1)
    (sep : (⟨s.gpr .s4, 16384⟩ : Region).Disjoint ⟨s.gpr .s2, 32 * n⟩) :
    WP isa (chain) s (ChainResult s n) := by
  induction n generalizing s with
  | zero => omega_arith
  | succ n ih =>
    have out32 : ∀ i < 32, InRegions s.wr (s.gpr .s2 + BitVec.ofNat 64 i) 1 :=
      fun i hi => out i (by omega_arith)
    have sep32 := sep.sub_right (Region.sub_prefix (show 32 ≤ 32 * (n + 1) by omega_arith))
    obtain ⟨trace, u, run, step⟩ := chainStep_ok s
      (by rw [count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]; omega_arith) work out32 sep32
    have base := step.regs .s4 (by decide) (by decide) (by decide)
    have sp := step.sp
    have countU : u.gpr .s3 = BitVec.ofNat 64 (32 * n + lastLen) := by
      rw [step.remaining, count, show (32 : Addr) = BitVec.ofNat 64 32 from rfl,
        Offset.ofNat_sub_ofNat (by omega_arith : 32 ≤ 32 * (n + 1) + lastLen)]
      rw [show 32 * (n + 1) + lastLen - 32 = 32 * n + lastLen by omega_arith]
    have compareU : u.gpr .a7 = if 32 * n + lastLen < 65 then 1 else 0 := by
      rw [step.comparison, ← step.remaining, countU, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
    cases n with
    | zero =>
      have flag : isa.eval (.zero .a7) u = some false := by
        show VG.RISCV64.eval (.zero .a7) u = _
        simp [eval_zero, compareU, show lastLen < 65 by omega_arith]
      exact ⟨_, u, .loopExit run flag, (ChainResult.refl u).cons step (by omega_arith) sep⟩
    | succ n =>
      have workU : (⟨u.gpr .s4, 16384⟩ : Region) ∈ u.wr := by rw [base, step.wr]; exact work
      have outU : ∀ i < 32 * (n + 1), InRegions u.wr (u.gpr .s2 + BitVec.ofNat 64 i) 1 := by
        intro i hi
        rw [step.wr, step.output, BitVec.add_assoc,
          show (32 : Addr) = BitVec.ofNat 64 32 from rfl, ← BitVec.ofNat_add]
        exact out (32 + i) (by omega_arith)
      have suffix : Region.Sub ⟨u.gpr .s2, 32 * (n + 1)⟩ ⟨s.gpr .s2, 32 * (n + 1 + 1)⟩ := by
        rw [step.output]
        exact Offset.sub_base _ (by omega_arith : 32 + 32 * (n + 1) ≤ 32 * (n + 1 + 1))
      have sepU : (⟨u.gpr .s4, 16384⟩ : Region).Disjoint ⟨u.gpr .s2, 32 * (n + 1)⟩ := by
        rw [base]; exact sep.sub_right suffix
      obtain ⟨trace', t, run', result⟩ := ih u (by omega_arith) (by omega_arith) countU workU outU sepU
      have flag : isa.eval (.zero .a7) u = some true := by
        show VG.RISCV64.eval (.zero .a7) u = _
        simp [eval_zero, compareU, show ¬ 32 * (n + 1) + lastLen < 65 by omega_arith]
      exact ⟨_, t, .loopNext run flag run', result.cons step (by omega_arith) sep⟩

end VG.Proof.Argon2.RISCV64.HPrime
