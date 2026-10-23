module
public import VerifiedGarbage.Proof.Argon2.PPC64LE.HPrime.Calls
public import VerifiedGarbage.Proof.Argon2.PPC64LE.HPrime.Frame
public import VerifiedGarbage.Proof.Argon2.HPrime

import VerifiedGarbage.Proof.Argon2.PPC64LE.HPrime.Compare
import VerifiedGarbage.Proof.Argon2.PPC64LE.HPrime.Output
import VerifiedGarbage.Proof.Argon2.PPC64LE.HPrime.Absorb
import VerifiedGarbage.Proof.Argon2.PPC64LE.HPrime.Length
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Blake2.PPC64LE.Stream.Lit
import VerifiedGarbage.Proof.Framework.Contract

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
  have sum : 32 * (n + 1) = 32 + 32 * n := by omega
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
  · exact (extend 0 32 (by omega) (by simpa only [BitVec.add_zero] using step.frame)).trans
      (extend 32 (32 * n) (by omega) tf)
  · rw [← base, tail.digest, base, step.digest, Proof.Argon2.chainDigest]
  · have before : bytesAt t.mem (s.gpr .r29) 32 = bytesAt u.mem (s.gpr .r29) 32 := by
      apply Proof.Blake2.bytesAt_congr
      intro i hi
      apply tf.bytes (R := ⟨s.gpr .r29, 32⟩) _ (show 32 ≤ 2 ^ 64 by decide) hi
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (sep.sub_left (Region.sub_prefix (by decide))).symm.sub_left
          (Region.sub_prefix (by omega))
      · exact stackOut.symm.sub_left (Region.sub_prefix (by omega))
      · exact Offset.base_disjoint _ (e := 32) (n := 32 * n) (k := 32) (by decide) (by omega)
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
  | zero => omega
  | succ n ih =>
    have out32 : ∀ i < 32, InRegions s.wr (s.gpr .r29 + BitVec.ofNat 64 i) 1 :=
      fun i hi => out i (by omega)
    have sep32 := sep.sub_right (Region.sub_prefix (show 32 ≤ 32 * (n + 1) by omega))
    obtain ⟨trace, u, run, step⟩ := chainStep_ok s hsp
      (by rw [count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega) work out32 sep32 stackWork
    have base := step.regs .r31 (by decide) (by decide) (by decide)
    have sp := step.sp
    have countU : u.gpr .r30 = BitVec.ofNat 64 (32 * n + lastLen) := by
      rw [step.remaining, count, show (32 : Addr) = BitVec.ofNat 64 32 from rfl,
        Offset.ofNat_sub_ofNat (by omega : 32 ≤ 32 * (n + 1) + lastLen)]
      rw [show 32 * (n + 1) + lastLen - 32 = 32 * n + lastLen by omega]
    have compareU : u.gpr .r10 = if 32 * n + lastLen < 65 then 1 else 0 := by
      rw [step.comparison, ← step.remaining, countU, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    cases n with
    | zero =>
      have flag : isa.eval (.zero .d .r10) u = some false := by
        show VG.PPC64LE.eval (.zero .d .r10) u = _
        simp [eval_zero, compareU, show lastLen < 65 by omega]
      exact ⟨_, u, .loopExit run flag, (ChainResult.refl u).cons step (by omega) sep stackOut⟩
    | succ n =>
      have workU : (⟨u.gpr .r31, 16384⟩ : Region) ∈ u.wr := by rw [base, step.wr]; exact work
      have outU : ∀ i < 32 * (n + 1), InRegions u.wr (u.gpr .r29 + BitVec.ofNat 64 i) 1 := by
        intro i hi
        rw [step.wr, step.output, BitVec.add_assoc,
          show (32 : Addr) = BitVec.ofNat 64 32 from rfl, ← BitVec.ofNat_add]
        exact out (32 + i) (by omega)
      have suffix : Region.Sub ⟨u.gpr .r29, 32 * (n + 1)⟩ ⟨s.gpr .r29, 32 * (n + 1 + 1)⟩ := by
        rw [step.output]
        exact Offset.sub_base _ (by omega : 32 + 32 * (n + 1) ≤ 32 * (n + 1 + 1))
      have sepU : (⟨u.gpr .r31, 16384⟩ : Region).Disjoint ⟨u.gpr .r29, 32 * (n + 1)⟩ := by
        rw [base]; exact sep.sub_right suffix
      have swU : (below u.sp 48).Disjoint ⟨u.gpr .r31, 16384⟩ := by
        rw [sp, base]; exact stackWork
      have soU : (below u.sp 48).Disjoint ⟨u.gpr .r29, 32 * (n + 1)⟩ := by
        rw [sp]; exact stackOut.sub_right suffix
      obtain ⟨trace', t, run', result⟩ := ih u (by omega) (by omega) (by rw [sp]; exact hsp) countU workU outU sepU swU soU
      have flag : isa.eval (.zero .d .r10) u = some true := by
        show VG.PPC64LE.eval (.zero .d .r10) u = _
        simp [eval_zero, compareU, show ¬ 32 * (n + 1) + lastLen < 65 by omega]
      exact ⟨_, t, .loopNext run flag run', result.cons step (by omega) sep stackOut⟩

end VG.Proof.Argon2.PPC64LE.HPrime
