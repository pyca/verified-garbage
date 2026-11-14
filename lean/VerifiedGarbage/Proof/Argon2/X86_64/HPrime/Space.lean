module

public import VerifiedGarbage.Proof.Argon2.HPrime
public import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Frame
public import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Init
public import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Output
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Absorb
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Finalize
import VerifiedGarbage.Proof.MdStream.X86_64.Common
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract

/-! ### `Argon2.X86_64.HPrime.Chain`, which only this module used -/

section

/-! Merged from `Proof.Argon2.X86_64.HPrime.Next`. -/

@[expose] public section

section
/-! # H′: hashing the previous 64-byte digest -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime
open VG.Spec.Blake2 (b Repr bytesAt)
open VG.Proof.MdStream.X86_64 (wp_mov32i)

theorem next_ok (v : Proof.Blake2.X86_64.Backend) (s : State)
    (hlen : 1 ≤ (s.gpr .rsi).toNat ∧ (s.gpr .rsi).toNat ≤ 64)
    (hwr : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr)
    (stackWork : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rbx, 16384⟩) :
    WP isa (next (hash v)) s fun t =>
      (bytesAt t.mem (s.gpr .rbx + 768) 64).take (s.gpr .rsi).toNat =
        Spec.Argon2.H (s.gpr .rsi).toNat (bytesAt s.mem (s.gpr .rbx + 768) 64) ∧ Keeps s t := by
  unfold next
  have retSub : Region.Sub (below (s.gpr .rsp) 8) (below (s.gpr .rsp) 16) := below_sub (by decide) (by decide)
  have retState := (stackWork.sub_left retSub).sub_right
    (Region.sub_prefix (base := s.gpr .rbx) (len := 192) (len' := 16384) (by decide))
  refine WP.seq ((init_ok v s hlen hwr retState).mono ?_)
  rintro a ⟨reprA, regsA, rdA, wrA, frameA⟩
  have ka : Keeps s a := ⟨regsA, rdA, wrA, init_frame _ _ frameA⟩
  have digest : bytesAt a.mem (a.gpr .rbx + 768) 64 = bytesAt s.mem (s.gpr .rbx + 768) 64 := by
    rw [ka.rbx]
    apply Proof.Blake2.bytesAt_congr
    intro i hi
    apply frameA.bytes (R := ⟨s.gpr .rbx + 768, 64⟩) _ (show 64 ≤ 2 ^ 64 by decide) hi
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (Offset.base_disjoint _ (e := 768) (n := 64) (k := 192) (by decide) (by decide)).symm
    · exact ((stackWork.sub_left retSub).sub_right (Offset.sub_base _ (by decide : 768 + 64 ≤ 16384))).symm
  have reprA' : Repr b (Spec.Blake2.init b (s.gpr .rsi).toNat 0) a.mem (a.gpr .rbx) [] := by
    rw [ka.rbx]; exact reprA
  have wrA' : (⟨a.gpr .rbx, 16384⟩ : Region) ∈ a.wr := by rw [ka.rbx, ka.wr]; exact hwr
  have swA : (below (a.gpr .rsp) 16).Disjoint ⟨a.gpr .rbx, 16384⟩ := by
    rw [ka.rbx, ka.rsp]; exact stackWork
  refine WP.seq ((absorbFixed_ok v a _ 768 64 (by decide) (by decide) reprA' wrA' swA).mono ?_)
  rintro u ⟨reprU, ku⟩
  have ksu := ka.trans ku
  have reprU' : Repr b (Spec.Blake2.init b (s.gpr .rsi).toNat 0) u.mem (u.gpr .rbx)
      (bytesAt s.mem (s.gpr .rbx + 768) 64) := by
    rw [ku.rbx]
    simpa only [show BitVec.ofNat 64 768 = (768 : Addr) from rfl, digest] using reprU
  refine WP.seq (wp_mov32i fun w hw _ _ => WP.block_nil ?_)
  have kw : Keeps u w := by
    refine ⟨fun r hr => ?_, hw.rd, hw.wr, ?_⟩
    · have hn : r ≠ .rsi := by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact hw.other r hn
    · rw [hw.mem]; exact Frame.refl _ _
  have ksw := ksu.trans kw
  have reprW : Repr b (Spec.Blake2.init b (s.gpr .rsi).toNat 0) w.mem (w.gpr .rbx)
      (bytesAt s.mem (s.gpr .rbx + 768) 64) := by
    rw [hw.mem, kw.rbx]; exact reprU'
  have length : (bytesAt s.mem (s.gpr .rbx + 768) 64).length = 64 := by
    simp only [bytesAt, List.length_map, List.length_range]
  have count : w.gpr .rsi = BitVec.ofNat 64 (bytesAt s.mem (s.gpr .rbx + 768) 64).length := by
    rw [length]; exact hw.gpr
  have bound : (bytesAt s.mem (s.gpr .rbx + 768) 64).length < 2 ^ 64 := by rw [length]; decide
  have wrW : (⟨w.gpr .rbx, 16384⟩ : Region) ∈ w.wr := by rw [ksw.rbx, ksw.wr]; exact hwr
  have swW : (below (w.gpr .rsp) 16).Disjoint ⟨w.gpr .rbx, 16384⟩ := by
    rw [ksw.rbx, ksw.rsp]; exact stackWork
  refine (finalize_ok v w _ _ reprW count bound wrW swW).mono ?_
  rintro t ⟨out, regsT, rdT, wrT, frameT⟩
  refine ⟨?_, ksw.trans ⟨regsT, rdT, wrT, finalize_frame _ _ frameT⟩⟩
  have result := congrArg (List.take (s.gpr .rsi).toNat) out
  rw [ksw.rbx] at result
  exact result.trans (Proof.Argon2.H_stream _ _).symm

end VG.Proof.Argon2.X86_64.HPrime
end

/-! Merged from `Proof.Argon2.X86_64.HPrime.ChainStep`. -/
section
/-! # H′: one hash-and-prefix iteration -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime
open VG.Proof.MdStream.X86_64 (wp_mov32i wp_cmpi)
open VG.Spec.Blake2 (bytesAt)

structure ChainStep (s t : State) : Prop where
  output : t.gpr .r14 = s.gpr .r14 + 32
  remaining : t.gpr .r15 = s.gpr .r15 - 32
  regs : ∀ r ∈ calleeSaved, r ≠ .r14 → r ≠ .r15 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨s.gpr .rbx, 832⟩, below (s.gpr .rsp) 16, ⟨s.gpr .r14, 32⟩] s.mem t.mem
  digest : bytesAt t.mem (s.gpr .rbx + 768) 64 =
    Spec.Argon2.H 64 (bytesAt s.mem (s.gpr .rbx + 768) 64)
  bytes : bytesAt t.mem (s.gpr .r14) 32 =
    (Spec.Argon2.H 64 (bytesAt s.mem (s.gpr .rbx + 768) 64)).take 32
  cf : t.cf = some (decide ((s.gpr .r15 - 32).toNat < 65))

theorem chainStep_ok (v : Proof.Blake2.X86_64.Backend) (s : State)
    (work : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr)
    (out : ∀ i < 32, InRegions s.wr (s.gpr .r14 + BitVec.ofNat 64 i) 1)
    (sep : (⟨s.gpr .rbx, 16384⟩ : Region).Disjoint ⟨s.gpr .r14, 32⟩)
    (stackWork : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rbx, 16384⟩) :
    WP isa (.seq (.block [.mov32 .rsi (.imm 64)])
      (.seq (next (hash v)) (.seq emitPrefix (.block [.alu .cmp .r15 (.imm 65)]))))
      s (ChainStep s) := by
  refine WP.seq (wp_mov32i fun a ha _ _ => WP.block_nil ?_)
  have ka : Keeps s a := by
    refine ⟨fun r hr => ?_, ha.rd, ha.wr, ?_⟩
    · have hn : r ≠ .rsi := by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact ha.other r hn
    · rw [ha.mem]; exact Frame.refl _ _
  have workA : (⟨a.gpr .rbx, 16384⟩ : Region) ∈ a.wr := by rw [ka.rbx, ka.wr]; exact work
  have stackA : (below (a.gpr .rsp) 16).Disjoint ⟨a.gpr .rbx, 16384⟩ := by
    rw [ka.rbx, ka.rsp]; exact stackWork
  have lengthA : (a.gpr .rsi).toNat = 64 := by rw [ha.gpr]; rfl
  refine WP.seq ((next_ok v a (by rw [lengthA]; decide) workA stackA).mono ?_)
  rintro u ⟨du, ku⟩
  have ksu := ka.trans ku
  have dstU : u.gpr .r14 = s.gpr .r14 := ksu.regs _ (by decide)
  have digestU : bytesAt u.mem (s.gpr .rbx + 768) 64 =
      Spec.Argon2.H 64 (bytesAt s.mem (s.gpr .rbx + 768) 64) := by
    simpa only [lengthA, ka.rbx, ha.mem, bytesAt_take _ _ 64 64 (by decide)] using du
  have workU : (⟨u.gpr .rbx, 16384⟩ : Region) ∈ u.wr := by rw [ksu.rbx, ksu.wr]; exact work
  have outU : ∀ i < 32, InRegions u.wr (u.gpr .r14 + BitVec.ofNat 64 i) 1 := by
    rw [ksu.wr, dstU]; exact out
  have sepU : (⟨u.gpr .rbx + 768, 32⟩ : Region).Disjoint ⟨u.gpr .r14, 32⟩ := by
    rw [ksu.rbx, dstU]
    exact sep.sub_left (Offset.sub_base _ (by decide : 768 + 32 ≤ 16384))
  refine WP.seq ((emitPrefix_ok u workU outU sepU).mono ?_)
  intro w hw
  refine wp_cmpi fun t gt mt rt wt cf _ => WP.block_nil ?_
  have fw : Frame [⟨s.gpr .r14, 32⟩] u.mem w.mem := by
    rw [← dstU]; exact hw.frame
  refine ⟨?_, ?_, fun r hr h14 h15 => ?_, rt.trans (hw.rd.trans ksu.rd),
    wt.trans (hw.wr.trans ksu.wr), ?_, ?_, ?_, ?_⟩
  · rw [gt, hw.output, dstU]
  · rw [gt, hw.remaining, ksu.regs _ (by decide)]
  · rw [gt]
    have hrax : r ≠ .rax := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hrcx : r ≠ .rcx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hrdx : r ≠ .rdx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (hw.other r hrax hrcx hrdx h14 h15).trans (ksu.regs r hr)
  · rw [mt]
    apply Frame.trans (ksu.frame.sub ?_) (fw.sub ?_)
    · intro r hr
      exact ⟨r, List.mem_append_left _ hr, fun _ hx => hx⟩
    · intro r hr
      exact ⟨r, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr), fun _ hx => hx⟩
  · rw [mt, ← digestU]
    apply Proof.Blake2.bytesAt_congr
    intro i hi
    apply fw.bytes (R := ⟨s.gpr .rbx + 768, 64⟩) _ (show 64 ≤ 2 ^ 64 by decide) hi
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact sep.sub_left (Offset.sub_base _ (by decide : 768 + 64 ≤ 16384))
  · rw [mt, hw.mem, dstU, ksu.rbx, ← digestU, bytesAt_take _ _ 32 64 (by decide)]
    exact bytesAt_writeBytes _ _ _ (by simp only [bytesAt, List.length_map, List.length_range]; decide)
  · rw [cf, hw.remaining, ksu.regs _ (by decide)]
    rfl

end VG.Proof.Argon2.X86_64.HPrime
end

/-! # H′: repeating the hash-and-prefix iteration -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime
open VG.Spec.Blake2 (bytesAt)
open VG.Proof.Argon2 (chainDigest chainPrefixes)

structure ChainResult (s : State) (n : Nat) (t : State) : Prop where
  output : t.gpr .r14 = s.gpr .r14 + BitVec.ofNat 64 (32 * n)
  remaining : t.gpr .r15 = s.gpr .r15 - BitVec.ofNat 64 (32 * n)
  regs : ∀ r ∈ calleeSaved, r ≠ .r14 → r ≠ .r15 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨s.gpr .rbx, 832⟩, below (s.gpr .rsp) 16, ⟨s.gpr .r14, 32 * n⟩] s.mem t.mem
  digest : bytesAt t.mem (s.gpr .rbx + 768) 64 =
    chainDigest n (bytesAt s.mem (s.gpr .rbx + 768) 64)
  bytes : bytesAt t.mem (s.gpr .r14) (32 * n) =
    chainPrefixes n (bytesAt s.mem (s.gpr .rbx + 768) 64)

theorem ChainResult.refl (s : State) : ChainResult s 0 s :=
  ⟨by simp, by simp, fun _ _ _ _ => rfl, rfl, rfl, Frame.refl _ _, rfl, rfl⟩

theorem ChainResult.cons {s u t : State} {n : Nat} (step : ChainStep s u)
    (tail : ChainResult u n t) (bound : 32 * (n + 1) < 2 ^ 64)
    (sep : (⟨s.gpr .rbx, 16384⟩ : Region).Disjoint ⟨s.gpr .r14, 32 * (n + 1)⟩)
    (stackOut : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .r14, 32 * (n + 1)⟩) :
    ChainResult s (n + 1) t := by
  have base := step.regs .rbx (by decide) (by decide) (by decide)
  have sp := step.regs .rsp (by decide) (by decide) (by decide)
  have sum : 32 * (n + 1) = 32 + 32 * n := by omega_using []
  have sumBV : BitVec.ofNat 64 (32 * (n + 1)) = 32 + BitVec.ofNat 64 (32 * n) := by
    rw [sum, BitVec.ofNat_add]; rfl
  have tf : Frame [⟨s.gpr .rbx, 832⟩, below (s.gpr .rsp) 16,
      ⟨s.gpr .r14 + 32, 32 * n⟩] u.mem t.mem := by
    rw [← base, ← sp, ← step.output]; exact tail.frame
  have extend {m m' : Mem} (d k : Nat) (hk : d + k ≤ 32 * (n + 1))
      (h : Frame [⟨s.gpr .rbx, 832⟩, below (s.gpr .rsp) 16,
        ⟨s.gpr .r14 + BitVec.ofNat 64 d, k⟩] m m') :
      Frame [⟨s.gpr .rbx, 832⟩, below (s.gpr .rsp) 16, ⟨s.gpr .r14, 32 * (n + 1)⟩] m m' := by
    apply h.sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ hx => hx⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ hx => hx⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)),
        Offset.sub_base _ hk⟩
  refine ⟨?_, ?_, fun r hr h1 h2 => (tail.regs r hr h1 h2).trans (step.regs r hr h1 h2),
    tail.rd.trans step.rd, tail.wr.trans step.wr, ?_, ?_, ?_⟩
  · rw [tail.output, step.output, sumBV, BitVec.add_assoc]
  · rw [tail.remaining, step.remaining, sumBV, BitVec.sub_sub]
  · exact (extend 0 32 (by omega_using []) (by simpa only [BitVec.add_zero] using step.frame)).trans
      (extend 32 (32 * n) (by omega_using []) tf)
  · rw [← base, tail.digest, base, step.digest, Proof.Argon2.chainDigest]
  · have before : bytesAt t.mem (s.gpr .r14) 32 = bytesAt u.mem (s.gpr .r14) 32 := by
      apply Proof.Blake2.bytesAt_congr
      intro i hi
      apply tf.bytes (R := ⟨s.gpr .r14, 32⟩) _ (show 32 ≤ 2 ^ 64 by decide) hi
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (sep.sub_left (Region.sub_prefix (by decide))).symm.sub_left
          (Region.sub_prefix (by omega_using []))
      · exact stackOut.symm.sub_left (Region.sub_prefix (by omega_using []))
      · exact Offset.base_disjoint _ (e := 32) (n := 32 * n) (k := 32) (by decide) (by omega_using [bound])
    rw [sum, Proof.Blake2.bytesAt_add, before, step.bytes,
      show BitVec.ofNat 64 32 = (32 : Addr) from rfl, ← step.output, tail.bytes,
      base, step.digest]
    rw [Proof.Argon2.chainPrefixes]

theorem chain_ok (v : Proof.Blake2.X86_64.Backend) (n lastLen : Nat) (s : State)
    (positive : 1 ≤ n) (last : 33 ≤ lastLen ∧ lastLen ≤ 64)
    (bound : 32 * n + lastLen < 2 ^ 64)
    (count : s.gpr .r15 = BitVec.ofNat 64 (32 * n + lastLen))
    (work : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr)
    (out : ∀ i < 32 * n, InRegions s.wr (s.gpr .r14 + BitVec.ofNat 64 i) 1)
    (sep : (⟨s.gpr .rbx, 16384⟩ : Region).Disjoint ⟨s.gpr .r14, 32 * n⟩)
    (stackWork : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rbx, 16384⟩)
    (stackOut : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .r14, 32 * n⟩) :
    WP isa (chain (hash v)) s (ChainResult s n) := by
  induction n generalizing s with
  | zero => omega
  | succ n ih =>
    have out32 : ∀ i < 32, InRegions s.wr (s.gpr .r14 + BitVec.ofNat 64 i) 1 :=
      fun i hi => out i (by omega_using [hi])
    have sep32 := sep.sub_right (Region.sub_prefix (show 32 ≤ 32 * (n + 1) by omega_using []))
    obtain ⟨trace, u, run, step⟩ := chainStep_ok v s work out32 sep32 stackWork
    have base := step.regs .rbx (by decide) (by decide) (by decide)
    have sp := step.regs .rsp (by decide) (by decide) (by decide)
    have countU : u.gpr .r15 = BitVec.ofNat 64 (32 * n + lastLen) := by
      rw [step.remaining, count, show (32 : Addr) = BitVec.ofNat 64 32 from rfl,
        Offset.ofNat_sub_ofNat (by omega_using [] : 32 ≤ 32 * (n + 1) + lastLen)]
      rw [show 32 * (n + 1) + lastLen - 32 = 32 * n + lastLen by omega_using []]
    have cfU : u.cf = some (decide (32 * n + lastLen < 65)) := by
      rw [step.cf, ← step.remaining, countU, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [bound])]
    cases n with
    | zero =>
      have flag : isa.eval .ae u = some false := by
        simp only [eval, cfU, show 32 * 0 + lastLen < 65 by omega_using [last], decide_true,
          Option.map_some, Bool.not_true]
      exact ⟨_, u, .loopExit run flag, (ChainResult.refl u).cons step (by omega_using []) sep stackOut⟩
    | succ n =>
      have workU : (⟨u.gpr .rbx, 16384⟩ : Region) ∈ u.wr := by rw [base, step.wr]; exact work
      have outU : ∀ i < 32 * (n + 1), InRegions u.wr (u.gpr .r14 + BitVec.ofNat 64 i) 1 := by
        intro i hi
        rw [step.wr, step.output, BitVec.add_assoc,
          show (32 : Addr) = BitVec.ofNat 64 32 from rfl, ← BitVec.ofNat_add]
        exact out (32 + i) (by omega_using [hi])
      have suffix : Region.Sub ⟨u.gpr .r14, 32 * (n + 1)⟩ ⟨s.gpr .r14, 32 * (n + 1 + 1)⟩ := by
        rw [step.output]
        exact Offset.sub_base _ (by omega_using [] : 32 + 32 * (n + 1) ≤ 32 * (n + 1 + 1))
      have sepU : (⟨u.gpr .rbx, 16384⟩ : Region).Disjoint ⟨u.gpr .r14, 32 * (n + 1)⟩ := by
        rw [base]; exact sep.sub_right suffix
      have swU : (below (u.gpr .rsp) 16).Disjoint ⟨u.gpr .rbx, 16384⟩ := by
        rw [sp, base]; exact stackWork
      have soU : (below (u.gpr .rsp) 16).Disjoint ⟨u.gpr .r14, 32 * (n + 1)⟩ := by
        rw [sp]; exact stackOut.sub_right suffix
      obtain ⟨trace', t, run', result⟩ := ih u (by omega_using []) (by omega_using [bound]) countU workU outU sepU swU soU
      have flag : isa.eval .ae u = some true := by
        simp only [eval, cfU, show ¬ 32 * (n + 1) + lastLen < 65 by omega_using [last], decide_false,
          Option.map_some, Bool.not_false]
      exact ⟨_, t, .loopNext run flag run', result.cons step (by omega_using [bound]) sep stackOut⟩

end VG.Proof.Argon2.X86_64.HPrime

end

end


/-! Merged from `Proof.Argon2.X86_64.HPrime.Written`. -/

@[expose] public section

section
/-! # H′: composing output fragments -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64
open VG.Spec.Blake2 (bytesAt)

/-- An output fragment, allowing hashing in the workspace between writes. -/
structure Written (s : State) (xs : List Byte) (t : State) : Prop where
  output : t.gpr .r14 = s.gpr .r14 + BitVec.ofNat 64 xs.length
  regs : ∀ r ∈ calleeSaved, r ≠ .r14 → r ≠ .r15 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨s.gpr .rbx, 832⟩, below (s.gpr .rsp) 16, ⟨s.gpr .r14, xs.length⟩] s.mem t.mem
  bytes : bytesAt t.mem (s.gpr .r14) xs.length = xs

theorem Written.rbx {s t : State} {xs : List Byte} (h : Written s xs t) :
    t.gpr .rbx = s.gpr .rbx := h.regs _ (by decide) (by decide) (by decide)

theorem Written.rsp {s t : State} {xs : List Byte} (h : Written s xs t) :
    t.gpr .rsp = s.gpr .rsp := h.regs _ (by decide) (by decide) (by decide)

theorem Written.of_keeps {s t : State} (h : Keeps s t) : Written s [] t := by
  refine ⟨?_, fun r hr _ _ => h.regs r hr, h.rd, h.wr, ?_, rfl⟩
  · exact (h.regs .r14 (by decide)).trans (BitVec.add_zero _).symm
  · exact h.frame.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ hx => hx⟩

theorem Written.before_keeps {s u t : State} {xs : List Byte} (h : Written u xs t)
    (k : Keeps s u) : Written s xs t := by
  have dst := k.regs .r14 (by decide)
  refine ⟨by rw [h.output, dst], fun r hr h1 h2 => (h.regs r hr h1 h2).trans (k.regs r hr),
    h.rd.trans k.rd, h.wr.trans k.wr, ?_, ?_⟩
  · have before : Frame [⟨s.gpr .rbx, 832⟩, below (s.gpr .rsp) 16,
        ⟨s.gpr .r14, xs.length⟩] s.mem u.mem :=
      k.frame.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ hx => hx⟩
    exact before.trans (by simpa only [dst, k.rbx, k.rsp] using h.frame)
  · rw [← dst]; exact h.bytes

theorem Written.of_copied {s t : State} {k : Nat} (h : Copied s k t) (hk : k < 2 ^ 64) :
    Written s (bytesAt s.mem (s.gpr .rbx + 768) k) t := by
  have len : (bytesAt s.mem (s.gpr .rbx + 768) k).length = k := by
    simp only [bytesAt, List.length_map, List.length_range]
  refine ⟨by rw [len]; exact h.output, fun r hr h14 _ => ?_, h.rd, h.wr, ?_, ?_⟩
  · have h1 : r ≠ .rax := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have h2 : r ≠ .rcx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have h3 : r ≠ .rdx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact h.other r h1 h2 h3 h14
  · rw [len]
    exact h.frame.sub fun r hr =>
      ⟨r, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr), fun _ hx => hx⟩
  · rw [h.mem]
    exact bytesAt_writeBytes _ _ _ (by rw [len]; exact hk)

theorem Written.of_emitted {s t : State} (h : Emitted s t) :
    Written s (bytesAt s.mem (s.gpr .rbx + 768) 32) t := by
  have len : (bytesAt s.mem (s.gpr .rbx + 768) 32).length = 32 := by
    simp only [bytesAt, List.length_map, List.length_range]
  refine ⟨by rw [len]; exact h.output, fun r hr h14 h15 => ?_, h.rd, h.wr, ?_, ?_⟩
  · have h1 : r ≠ .rax := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have h2 : r ≠ .rcx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have h3 : r ≠ .rdx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact h.other r h1 h2 h3 h14 h15
  · rw [len]
    exact h.frame.sub fun r hr =>
      ⟨r, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr), fun _ hx => hx⟩
  · rw [h.mem]
    exact bytesAt_writeBytes _ _ _ (by rw [len]; decide)

theorem Written.of_chain {s t : State} {n : Nat} (h : ChainResult s n t) :
    Written s (Proof.Argon2.chainPrefixes n (bytesAt s.mem (s.gpr .rbx + 768) 64)) t := by
  refine ⟨?_, h.regs, h.rd, h.wr, ?_, ?_⟩
  · simpa only [Proof.Argon2.chainPrefixes_length] using h.output
  · simpa only [Proof.Argon2.chainPrefixes_length] using h.frame
  · simpa only [Proof.Argon2.chainPrefixes_length] using h.bytes

theorem Written.trans {s u t : State} {xs ys : List Byte} (first : Written s xs u)
    (last : Written u ys t) (bound : xs.length + ys.length < 2 ^ 64)
    (sep : (⟨s.gpr .rbx, 16384⟩ : Region).Disjoint ⟨s.gpr .r14, xs.length + ys.length⟩)
    (stack : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .r14, xs.length + ys.length⟩) :
    Written s (xs ++ ys) t := by
  have tf : Frame [⟨s.gpr .rbx, 832⟩, below (s.gpr .rsp) 16,
      ⟨s.gpr .r14 + BitVec.ofNat 64 xs.length, ys.length⟩] u.mem t.mem := by
    rw [← first.rbx, ← first.rsp, ← first.output]; exact last.frame
  have extend {m m' : Mem} (d k : Nat) (hk : d + k ≤ xs.length + ys.length)
      (h : Frame [⟨s.gpr .rbx, 832⟩, below (s.gpr .rsp) 16,
        ⟨s.gpr .r14 + BitVec.ofNat 64 d, k⟩] m m') :
      Frame [⟨s.gpr .rbx, 832⟩, below (s.gpr .rsp) 16,
        ⟨s.gpr .r14, (xs ++ ys).length⟩] m m' := by
    apply h.sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ hx => hx⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ hx => hx⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)),
        Offset.sub_base _ (by simpa only [List.length_append] using hk)⟩
  refine ⟨?_, fun r hr h1 h2 => (last.regs r hr h1 h2).trans (first.regs r hr h1 h2),
    last.rd.trans first.rd, last.wr.trans first.wr, ?_, ?_⟩
  · rw [last.output, first.output, List.length_append, BitVec.ofNat_add, BitVec.add_assoc]
  · exact (extend 0 xs.length (by omega_using []) (by simpa only [BitVec.add_zero] using first.frame)).trans
      (extend xs.length ys.length (by omega_using []) tf)
  · have before : bytesAt t.mem (s.gpr .r14) xs.length = bytesAt u.mem (s.gpr .r14) xs.length := by
      apply Proof.Blake2.bytesAt_congr
      intro i hi
      apply tf.bytes (R := ⟨s.gpr .r14, xs.length⟩) _ (show xs.length ≤ 2 ^ 64 by omega_using [bound]) hi
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (sep.sub_left (Region.sub_prefix (by decide))).symm.sub_left (Region.sub_prefix (by omega_using []))
      · exact stack.symm.sub_left (Region.sub_prefix (by omega_using []))
      · exact Offset.base_disjoint _ (by omega_using []) (by omega_using [bound])
    rw [List.length_append, Proof.Blake2.bytesAt_add, before, first.bytes, ← first.output, last.bytes]

end VG.Proof.Argon2.X86_64.HPrime
end

/-! # H′: permissions and separation at an output cursor -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime
open VG.Proof.MdStream.X86_64 (wp_mov)
open VG.Spec.Blake2 (bytesAt)

structure Space (s : State) (n : Nat) : Prop where
  bound : n < 2 ^ 64
  work : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr
  out : ∀ i < n, InRegions s.wr (s.gpr .r14 + BitVec.ofNat 64 i) 1
  sep : (⟨s.gpr .rbx, 16384⟩ : Region).Disjoint ⟨s.gpr .r14, n⟩
  stackWork : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rbx, 16384⟩
  stackOut : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .r14, n⟩

theorem Space.advance {s t : State} {xs : List Byte} {n k : Nat}
    (h : Space s n) (written : Written s xs t) (size : xs.length + k ≤ n) : Space t k := by
  have suffix : Region.Sub ⟨t.gpr .r14, k⟩ ⟨s.gpr .r14, n⟩ := by
    rw [written.output]; exact Offset.sub_base _ size
  refine ⟨by have := h.bound; omega_using [size, this], ?_, ?_, ?_, ?_, ?_⟩
  · rw [written.wr, written.rbx]; exact h.work
  · intro i hi
    rw [written.wr, written.output, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact h.out (xs.length + i) (by omega_using [size, hi])
  · rw [written.rbx]; exact h.sep.sub_right suffix
  · rw [written.rbx, written.rsp]; exact h.stackWork
  · rw [written.rsp]; exact h.stackOut.sub_right suffix

theorem Space.keeps {s t : State} {n : Nat} (h : Space s n) (k : Keeps s t) : Space t n :=
  h.advance (Written.of_keeps k) (by simp only [List.length_nil, Nat.zero_add, Nat.le_refl])

theorem Space.prefix {s : State} {n k : Nat} (h : Space s n) (hk : k ≤ n) : Space s k := by
  refine ⟨by have := h.bound; omega_using [hk, this], h.work, fun i hi => h.out i (by omega_using [hk, hi]),
    h.sep.sub_right (Region.sub_prefix hk), h.stackWork, h.stackOut.sub_right (Region.sub_prefix hk)⟩

theorem Space.join {s u t : State} {xs ys : List Byte} {n : Nat} (h : Space s n)
    (first : Written s xs u) (last : Written u ys t) (size : xs.length + ys.length ≤ n) :
    Written s (xs ++ ys) t :=
  first.trans last (by have := h.bound; omega_using [size, this])
    (h.sep.sub_right (Region.sub_prefix size)) (h.stackOut.sub_right (Region.sub_prefix size))

theorem copyRemaining_ok (s : State) (n : Nat) (space : Space s n)
    (lo : 1 ≤ n) (hi : n ≤ 64) (count : s.gpr .r15 = BitVec.ofNat 64 n) :
    WP isa copyRemaining s fun t => Written s (bytesAt s.mem (s.gpr .rbx + 768) n) t := by
  unfold copyRemaining
  refine WP.seq (wp_mov fun a ha _ _ => WP.block_nil ?_)
  have base := ha.other .rbx (by decide)
  have dst := ha.other .r14 (by decide)
  have workA : (⟨a.gpr .rbx, 16384⟩ : Region) ∈ a.wr := by rw [base, ha.wr]; exact space.work
  have outA : ∀ i < n, InRegions a.wr (a.gpr .r14 + BitVec.ofNat 64 i) 1 := by
    rw [dst, ha.wr]; exact space.out
  have sepA : (⟨a.gpr .rbx + 768, n⟩ : Region).Disjoint ⟨a.gpr .r14, n⟩ := by
    rw [base, dst]; exact space.sep.sub_left (Offset.sub_base _ (by omega_using [hi] : 768 + n ≤ 16384))
  refine (copy_ok a n lo hi (ha.gpr.trans count) workA outA sepA).mono ?_
  intro t ht
  have result := Written.of_copied ht space.bound
  refine ⟨?_, fun r hr h1 h2 => ?_, result.rd.trans ha.rd, result.wr.trans ha.wr, ?_, ?_⟩
  · simpa only [dst, ha.mem, base] using result.output
  · have hrax : r ≠ .rax := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (result.regs r hr h1 h2).trans (ha.other r hrax)
  · simpa only [base, dst, ha.mem, ha.other .rsp (by decide)] using result.frame
  · simpa only [base, dst, ha.mem] using result.bytes

end VG.Proof.Argon2.X86_64.HPrime
