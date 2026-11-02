module

public import VerifiedGarbage.Proof.Argon2.RISCV64.HPrime.Contract
import VerifiedGarbage.Proof.Argon2.RISCV64.HPrime.Compare
public import VerifiedGarbage.Proof.Argon2.RISCV64.HPrime.Space
import VerifiedGarbage.Proof.Argon2.RISCV64.HPrime.Absorb
import VerifiedGarbage.Proof.Argon2.RISCV64.HPrime.Calls
import VerifiedGarbage.Proof.Argon2.RISCV64.HPrime.Chain
import VerifiedGarbage.Proof.Argon2.RISCV64.HPrime.Length
import VerifiedGarbage.Proof.Argon2.RISCV64.HPrime.Setup
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Blake2.RISCV64.Stream.Lit

@[expose] public section

/-! Merged from `Proof.Argon2.RISCV64.HPrime.First`. -/
section
/-! Merged from `Proof.Argon2.RISCV64.HPrime.FinishInput`. -/
section
/-! # H′: finalizing the prefixed input -/

namespace VG.Proof.Argon2.RISCV64.HPrime

open VG VG.RISCV64 VG.Impl.Argon2.RISCV64.HPrime
open VG.Spec.Blake2 (b Repr bytesAt)
open VG.RISCV64.Wp (wp_mv wp_addi)

theorem finishInput_ok (s : State)
    (h0 : Spec.Blake2.HashValue 64) (d : List Byte)
    (repr : Repr b h0 s.mem (s.gpr .s4) d)
    (length : d.length = 4 + (s.gpr .s1).toNat) (bound : (s.gpr .s1).toNat < 2 ^ 32)
    (hwr : (⟨s.gpr .s4, 16384⟩ : Region) ∈ s.wr) :
    WP isa (finishInput) s fun t =>
      bytesAt t.mem (s.gpr .s4 + 768) 64 = Spec.Blake2.finalHash b h0 d ∧ Keeps s t := by
  unfold finishInput
  refine WP.seq (wp_addi (by decide) fun u hu => WP.block_nil ?_)
  have ku : Keeps s u := Keeps.of_upd hu (by decide)
  have repr' : Repr b h0 u.mem (u.gpr .s4) d := by rw [hu.mem, ku.s4]; exact repr
  have count : u.gpr .a1 = BitVec.ofNat 64 d.length := by
    rw [hu.gpr, length, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact BitVec.add_comm _ _
  have len : d.length < 2 ^ 64 := by rw [length]; omega_arith
  have wr : (⟨u.gpr .s4, 16384⟩ : Region) ∈ u.wr := by rw [ku.s4, ku.wr]; exact hwr
  refine (finalize_ok u h0 d repr' count len wr).mono ?_
  rintro t ⟨out, regs, rd, wr', sp', frame⟩
  refine ⟨?_, ku.trans ⟨regs, rd, wr', sp', finalize_frame _ frame⟩⟩
  simpa only [ku.s4] using out

end VG.Proof.Argon2.RISCV64.HPrime
end

/-! # H′: the hash of the length prefix and input -/

namespace VG.Proof.Argon2.RISCV64.HPrime

open VG VG.RISCV64 VG.Impl.Argon2.RISCV64.HPrime
open VG.Spec.Blake2 (b Repr bytesAt)

theorem first_ok (s : State)
    (hlen : 1 ≤ (s.gpr .s3).toNat ∧ (s.gpr .s3).toNat < 2 ^ 32)
    (len : (s.gpr .s1).toNat < 2 ^ 32)
    (headBytes : bytesAt s.mem (s.gpr .s4 + 832) 4 = Spec.Argon2.le32 (s.gpr .s3).toNat)
    (hwr : (⟨s.gpr .s4, 16384⟩ : Region) ∈ s.wr)
    (hdata : Covers [⟨s.gpr .s0, (s.gpr .s1).toNat⟩] (s.rd ++ s.wr))
    (dataWork : (⟨s.gpr .s0, (s.gpr .s1).toNat⟩ : Region).Disjoint ⟨s.gpr .s4, 16384⟩) :
    WP isa (first) s fun t =>
      (bytesAt t.mem (s.gpr .s4 + 768) 64).take (min (s.gpr .s3).toNat 64) =
        Spec.Argon2.H (min (s.gpr .s3).toNat 64)
          (Spec.Argon2.le32 (s.gpr .s3).toNat ++ bytesAt s.mem (s.gpr .s0) (s.gpr .s1).toNat) ∧
      Keeps s t := by
  unfold first
  refine WP.seq ((chooseLength_ok s hlen.2).mono ?_)
  rintro a ⟨lengthA, ka⟩
  have na : (a.gpr .a1).toNat = min (s.gpr .s3).toNat 64 := by
    rw [lengthA, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  have wrA : (⟨a.gpr .s4, 16384⟩ : Region) ∈ a.wr := by rw [ka.s4, ka.wr]; exact hwr
  have lenA : 1 ≤ (a.gpr .a1).toNat ∧ (a.gpr .a1).toNat ≤ 64 := by rw [na]; omega_arith
  refine WP.seq ((init_ok a lenA wrA).mono ?_)
  rintro u ⟨reprU, regsU, rdU, wrU, spU, frameU⟩
  have ku : Keeps a u := ⟨regsU, rdU, wrU, spU, init_frame _ frameU⟩
  have ksu := ka.trans ku
  have reprU' : Repr b (Spec.Blake2.init b (min (s.gpr .s3).toNat 64) 0) u.mem (u.gpr .s4) [] := by
    rw [ku.s4]; simpa only [na] using reprU
  have wrU' : (⟨u.gpr .s4, 16384⟩ : Region) ∈ u.wr := by rw [ksu.s4, ksu.wr]; exact hwr
  have headU : bytesAt u.mem (u.gpr .s4 + 832) 4 = Spec.Argon2.le32 (s.gpr .s3).toNat := by
    rw [ksu.s4, ksu.prefix]; exact headBytes
  refine WP.seq ((absorbFixed_ok u _ 832 4 (by decide) (by decide) (by decide) (by decide) reprU' wrU').mono ?_)
  rintro w ⟨reprW, kw⟩
  have ksw := ksu.trans kw
  have r12 : w.gpr .s0 = s.gpr .s0 := ksw.regs _ (by decide)
  have r13 : w.gpr .s1 = s.gpr .s1 := ksw.regs _ (by decide)
  have headLen : (Spec.Argon2.le32 (s.gpr .s3).toNat).length = 4 := by
    simp only [Spec.Argon2.le32, Spec.Blake2.wordBytes, List.length_map, List.length_range]
  have reprW' : Repr b (Spec.Blake2.init b (min (s.gpr .s3).toNat 64) 0) w.mem (w.gpr .s4)
      (Spec.Argon2.le32 (s.gpr .s3).toNat) := by
    rw [kw.s4]
    simpa only [show BitVec.ofNat 64 832 = (832 : Addr) from rfl, headU] using reprW
  have wrW : (⟨w.gpr .s4, 16384⟩ : Region) ∈ w.wr := by rw [ksw.s4, ksw.wr]; exact hwr
  have dataW : Covers [⟨w.gpr .s0, (w.gpr .s1).toNat⟩] (w.rd ++ w.wr) := by
    rw [r12, r13, ksw.rd, ksw.wr]; exact hdata
  have dwW : (⟨w.gpr .s0, (w.gpr .s1).toNat⟩ : Region).Disjoint ⟨w.gpr .s4, 16384⟩ := by
    rw [r12, r13, ksw.s4]; exact dataWork
  have inputW : bytesAt w.mem (w.gpr .s0) (w.gpr .s1).toNat =
      bytesAt s.mem (s.gpr .s0) (s.gpr .s1).toNat := by
    rw [r12, r13]
    exact ksw.bytes _ (show (s.gpr .s1).toNat ≤ 2 ^ 64 by omega_arith)
      (dataWork.sub_right (Region.sub_prefix (show 832 ≤ 16384 by decide)))
  refine WP.seq ((absorbInput_ok w _ _ headLen reprW' (by rw [r13]; exact len)
    wrW dataW dwW).mono ?_)
  rintro x ⟨reprX, kx⟩
  have ksx := ksw.trans kx
  have reprX' : Repr b (Spec.Blake2.init b (min (s.gpr .s3).toNat 64) 0) x.mem (x.gpr .s4)
      (Spec.Argon2.le32 (s.gpr .s3).toNat ++ bytesAt s.mem (s.gpr .s0) (s.gpr .s1).toNat) := by
    rw [kx.s4]; simpa only [inputW] using reprX
  have r13X : x.gpr .s1 = s.gpr .s1 := ksx.regs _ (by decide)
  have length : (Spec.Argon2.le32 (s.gpr .s3).toNat ++ bytesAt s.mem (s.gpr .s0) (s.gpr .s1).toNat).length =
      4 + (x.gpr .s1).toNat := by
    rw [List.length_append, headLen, r13X]
    simp only [bytesAt, List.length_map, List.length_range]
  have wrX : (⟨x.gpr .s4, 16384⟩ : Region) ∈ x.wr := by rw [ksx.s4, ksx.wr]; exact hwr
  refine (finishInput_ok x _ _ reprX' length (by rw [r13X]; exact len) wrX).mono ?_
  rintro t ⟨out, kt⟩
  refine ⟨?_, ksx.trans kt⟩
  have result := congrArg (List.take (min (s.gpr .s3).toNat 64)) out
  rw [ksx.s4] at result
  exact result.trans (Proof.Argon2.H_stream _ _).symm

end VG.Proof.Argon2.RISCV64.HPrime
end

/-! Merged from `Proof.Argon2.RISCV64.HPrime.Finish`. -/
section
/-! Merged from `Proof.Argon2.RISCV64.HPrime.Extend`. -/
section
/-! # H′: the prefixes and final digest of a long output -/

namespace VG.Proof.Argon2.RISCV64.HPrime

open VG VG.RISCV64 VG.Impl.Argon2.RISCV64.HPrime
open VG.RISCV64.Wp (wp_mv)
open VG.Spec.Blake2 (bytesAt)
open VG.Proof.Argon2 (chainDigest chainPrefixes)

theorem maybeChain_ok (n lastLen : Nat) (s : State)
    (space : Space s (32 * n + lastLen)) (last : 33 ≤ lastLen ∧ lastLen ≤ 64)
    (count : s.gpr .s3 = BitVec.ofNat 64 (32 * n + lastLen))
    (comparison : s.gpr .a7 = if 32 * n + lastLen < 65 then 1 else 0) :
    WP isa (.ite (.nonzero .a7) (.block []) (chain)) s (ChainResult s n) := by
  refine WP.ite (decide (32 * n + lastLen < 65)) (by by_cases h : 32 * n + lastLen < 65 <;>
    simp [VG.RISCV64.eval, comparison, h]) ?_ ?_
  · intro h
    have hn : n = 0 := by have := of_decide_eq_true h; omega_arith
    subst n
    exact WP.block_nil (ChainResult.refl s)
  · intro h
    have hn : 1 ≤ n := by have := of_decide_eq_false h; omega_arith
    have p := space.prefix (show 32 * n ≤ 32 * n + lastLen by omega_arith)
    exact chain_ok n lastLen s hn last space.bound count p.work p.out p.sep

theorem extendDigest_ok (n lastLen : Nat) (s : State)
    (space : Space s (32 * (n + 1) + lastLen)) (last : 33 ≤ lastLen ∧ lastLen ≤ 64)
    (count : s.gpr .s3 = BitVec.ofNat 64 (32 * (n + 1) + lastLen)) :
    WP isa (extendDigest) s fun t =>
      Written s ((bytesAt s.mem (s.gpr .s4 + 768) 64).take 32 ++
        chainPrefixes n (bytesAt s.mem (s.gpr .s4 + 768) 64)) t ∧
      (bytesAt t.mem (s.gpr .s4 + 768) 64).take lastLen =
        Spec.Argon2.H lastLen (chainDigest n (bytesAt s.mem (s.gpr .s4 + 768) 64)) ∧
      t.gpr .s3 = BitVec.ofNat 64 lastLen := by
  unfold extendDigest
  have short := space.prefix (show 32 ≤ 32 * (n + 1) + lastLen by omega_arith)
  have sep32 := short.sep.sub_left (Offset.sub_base _ (by decide : 768 + 32 ≤ 16384))
  refine WP.seq ((emitPrefix_ok s short.work short.out sep32).mono ?_)
  intro a ha
  have wa := Written.of_emitted ha
  have lenA : (bytesAt s.mem (s.gpr .s4 + 768) 32).length = 32 := by
    simp only [bytesAt, List.length_map, List.length_range]
  have spaceA : Space a (32 * n + lastLen) := space.advance wa (by rw [lenA]; omega_arith)
  have countA : a.gpr .s3 = BitVec.ofNat 64 (32 * n + lastLen) := by
    rw [ha.remaining, count, show (32 : Addr) = BitVec.ofNat 64 32 from rfl,
      Offset.ofNat_sub_ofNat (by omega_arith : 32 ≤ 32 * (n + 1) + lastLen)]
    rw [show 32 * (n + 1) + lastLen - 32 = 32 * n + lastLen by omega_arith]
  have digestA : bytesAt a.mem (a.gpr .s4 + 768) 64 = bytesAt s.mem (s.gpr .s4 + 768) 64 := by
    rw [wa.s4]; exact ha.digest short.sep
  refine WP.seq ((compare_ok a (by rw [countA, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := spaceA.bound; omega_arith)]; exact spaceA.bound)).mono fun u compared => ?_)
  have ku := compared.keeps
  have countU : u.gpr .s3 = BitVec.ofNat 64 (32 * n + lastLen) :=
    (compared.other _ (by decide)).trans countA
  have compareU : u.gpr .a7 = if 32 * n + lastLen < 65 then 1 else 0 := by
    rw [compared.value, countA, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := spaceA.bound; omega_arith)]
  refine WP.seq ((maybeChain_ok n lastLen u (spaceA.keeps ku) last countU compareU).mono ?_)
  intro w hw
  have ww := (Written.of_chain hw).before_keeps ku
  have digestU : bytesAt u.mem (u.gpr .s4 + 768) 64 = bytesAt s.mem (s.gpr .s4 + 768) 64 := by
    rw [compared.mem, ku.s4]; exact digestA
  have ww' : Written a (chainPrefixes n (bytesAt s.mem (s.gpr .s4 + 768) 64)) w := by
    simpa only [digestU] using ww
  have wsw := space.join wa ww' (by rw [lenA, Proof.Argon2.chainPrefixes_length]; omega_arith)
  have produced : ((bytesAt s.mem (s.gpr .s4 + 768) 32) ++
      chainPrefixes n (bytesAt s.mem (s.gpr .s4 + 768) 64)).length = 32 * (n + 1) := by
    rw [List.length_append, lenA, Proof.Argon2.chainPrefixes_length]; omega_arith
  have spaceW : Space w lastLen := space.advance wsw (by rw [produced])
  have countW : w.gpr .s3 = BitVec.ofNat 64 lastLen := by
    rw [hw.remaining, countU, Offset.ofNat_sub_ofNat (by omega_arith : 32 * n ≤ 32 * n + lastLen)]
    rw [Nat.add_sub_cancel_left]
  have digestW : bytesAt w.mem (w.gpr .s4 + 768) 64 =
      chainDigest n (bytesAt s.mem (s.gpr .s4 + 768) 64) := by
    rw [hw.regs .s4 (by decide) (by decide) (by decide), hw.digest, digestU]
  refine WP.seq (wp_mv fun x hx => WP.block_nil ?_)
  have kx : Keeps w x := Keeps.of_upd hx (by decide)
  have spaceX := spaceW.keeps kx
  have lenX : (x.gpr .a1).toNat = lastLen := by
    rw [hx.gpr, countW, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := spaceW.bound; omega_arith)]
  refine (next_ok x (by rw [lenX]; omega_arith) spaceX.work).mono ?_
  rintro t ⟨dt, kt⟩
  have wwt := Written.of_keeps (kx.trans kt)
  have written := space.join wsw wwt (by rw [produced, List.length_nil]; omega_arith)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [List.append_nil, bytesAt_take _ _ 32 64 (by decide)] using written
  · rw [lenX, kx.s4, hx.mem, digestW, wsw.s4] at dt
    exact dt
  · rw [kt.regs _ (by decide), kx.regs _ (by decide)]; exact countW

theorem longOutput_ok (n lastLen : Nat) (s : State)
    (space : Space s (32 * (n + 1) + lastLen)) (last : 33 ≤ lastLen ∧ lastLen ≤ 64)
    (count : s.gpr .s3 = BitVec.ofNat 64 (32 * (n + 1) + lastLen)) :
    WP isa (.seq (extendDigest) copyRemaining) s fun t =>
      Written s (Spec.Argon2.longHash lastLen (n + 1) (bytesAt s.mem (s.gpr .s4 + 768) 64)) t := by
  refine WP.seq ((extendDigest_ok n lastLen s space last count).mono ?_)
  rintro u ⟨written, digest, remaining⟩
  have len : ((bytesAt s.mem (s.gpr .s4 + 768) 64).take 32 ++
      chainPrefixes n (bytesAt s.mem (s.gpr .s4 + 768) 64)).length = 32 * (n + 1) := by
    simp only [List.length_append, List.length_take, bytesAt, List.length_map,
      List.length_range, Proof.Argon2.chainPrefixes_length]
    omega_arith
  have spaceU : Space u lastLen := space.advance written (by rw [len])
  refine (copyRemaining_ok u lastLen spaceU (by omega_arith) last.2 remaining).mono ?_
  intro t copied
  have out : bytesAt u.mem (u.gpr .s4 + 768) lastLen =
      Spec.Argon2.H lastLen (chainDigest n (bytesAt s.mem (s.gpr .s4 + 768) 64)) := by
    rw [written.s4, ← bytesAt_take _ _ lastLen 64 last.2]; exact digest
  have all := space.join written copied (by
    rw [len]; simp only [bytesAt, List.length_map, List.length_range, Nat.le_refl])
  rw [out, ← Proof.Argon2.longHash_chain] at all
  exact all

end VG.Proof.Argon2.RISCV64.HPrime
end

/-! # H′: emitting the complete short or long output -/

namespace VG.Proof.Argon2.RISCV64.HPrime

open VG VG.RISCV64 VG.Impl.Argon2.RISCV64.HPrime
open VG.Spec.Blake2 (bytesAt)

theorem finishOutput_ok (s : State) (n : Nat) (input : List Byte)
    (space : Space s n) (positive : 1 ≤ n) (count : s.gpr .s3 = BitVec.ofNat 64 n)
    (digest : (bytesAt s.mem (s.gpr .s4 + 768) 64).take (min n 64) =
      Spec.Argon2.H (min n 64) (Spec.Argon2.le32 n ++ input)) :
    WP isa (finishOutput) s (Written s (Spec.Argon2.hPrime n input)) := by
  unfold finishOutput
  refine WP.seq ((compare_ok s (by rw [count, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := space.bound; omega_arith)]; exact space.bound)).mono fun u compared => ?_)
  have ku := compared.keeps
  have countU : u.gpr .s3 = BitVec.ofNat 64 n := (compared.other _ (by decide)).trans count
  have compareU : u.gpr .a7 = if n < 65 then 1 else 0 := by
    rw [compared.value, count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := space.bound; omega_arith)]
  apply WP.seq
  refine WP.ite (decide (n < 65)) (by by_cases h : n < 65 <;> simp [VG.RISCV64.eval, compareU, h]) ?_ ?_
  · intro h
    have short : n ≤ 64 := by have := of_decide_eq_true h; omega_arith
    apply WP.block_nil
    refine (copyRemaining_ok u n (space.keeps ku) positive short countU).mono ?_
    intro t ht
    have result := ht.before_keeps ku
    have value : bytesAt u.mem (u.gpr .s4 + 768) n = Spec.Argon2.hPrime n input := by
      rw [compared.mem, ku.s4, ← bytesAt_take _ _ n 64 short]
      simpa only [Nat.min_eq_left short, Spec.Argon2.hPrime, ite_eq_left short] using digest
    rw [value] at result
    exact result
  · intro h
    have long : 64 < n := by have := of_decide_eq_false h; omega_arith
    let r := (n + 31) / 32 - 2
    let lastLen := n - 32 * r
    have bounds : 1 ≤ r ∧ 33 ≤ lastLen ∧ lastLen ≤ 64 ∧ 32 * r + lastLen = n :=
      Proof.Argon2.longHash_bounds n long
    obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero (show r ≠ 0 by omega_arith)
    change r = q + 1 at hq
    have size : 32 * (q + 1) + lastLen = n := by rw [← hq]; exact bounds.2.2.2
    have spaceU : Space u (32 * (q + 1) + lastLen) := by rw [size]; exact space.keeps ku
    have countLong : u.gpr .s3 = BitVec.ofNat 64 (32 * (q + 1) + lastLen) := by rw [size]; exact countU
    apply WP.seq_iff.mp
    refine (longOutput_ok q lastLen u spaceU ⟨bounds.2.1, bounds.2.2.1⟩ countLong).mono ?_
    intro t ht
    have result := ht.before_keeps ku
    have digestU : bytesAt u.mem (u.gpr .s4 + 768) 64 =
        Spec.Argon2.H 64 (Spec.Argon2.le32 n ++ input) := by
      rw [compared.mem, ku.s4]
      simpa only [Nat.min_eq_right (show 64 ≤ n by omega_arith), bytesAt_take _ _ 64 64 (by decide)] using digest
    have value : Spec.Argon2.longHash lastLen (q + 1) (bytesAt u.mem (u.gpr .s4 + 768) 64) =
        Spec.Argon2.hPrime n input := by
      rw [digestU, ← hq, Spec.Argon2.hPrime, ite_eq_right (show ¬ n ≤ 64 by omega_arith)]
    rw [value] at result
    exact result

end VG.Proof.Argon2.RISCV64.HPrime
end

/-! # H′: functional correctness of the complete RISC-V program -/

namespace VG.Proof.Argon2.RISCV64.HPrime

open VG VG.RISCV64 VG.Impl.Argon2.RISCV64.HPrime
open VG.Spec.Blake2 (bytesAt)

theorem code_wp (s : State) (pre : localContract.pre s) :
    WP isa code s fun t => localContract.post s t ∧
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.gpr .ra = s.gpr .ra ∧
      Frame [outputR s, workR s] s.mem t.mem := by
  obtain ⟨rd, wr, len, lo, hi, hal, dw, ow⟩ := pre
  have work : (workR s) ∈ s.wr := by rw [wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  unfold code
  refine WP.seq ((setup_ok s work hal).mono ?_)
  intro a ha
  have workA : (⟨a.gpr .s4, 16384⟩ : Region) ∈ a.wr := by
    rw [ha.workspace, ha.wr]; exact work
  have dataA : Covers [⟨a.gpr .s0, (a.gpr .s1).toNat⟩] (a.rd ++ a.wr) := by
    rw [ha.input, ha.length, ha.rd, rd]
    intro p n ⟨r, hr, hc⟩
    exact ⟨r, List.mem_append_left _ hr, hc⟩
  have dwA : (⟨a.gpr .s0, (a.gpr .s1).toNat⟩ : Region).Disjoint ⟨a.gpr .s4, 16384⟩ := by
    rw [ha.input, ha.length, ha.workspace]; exact dw
  have inputA : bytesAt a.mem (a.gpr .s0) (a.gpr .s1).toNat =
      bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat := by
    rw [ha.input, ha.length, ha.mem]
    apply Proof.Blake2.bytesAt_congr
    intro i hi'
    apply (setupMem_frame s).bytes (R := inputR s) _ (show (s.gpr .a1).toNat ≤ 2 ^ 64 by omega_arith) hi'
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact dw.sub_right (Offset.sub_base _ (by decide : 832 + 64 ≤ 16384))
  have headA : bytesAt a.mem (a.gpr .s4 + 832) 4 = Spec.Argon2.le32 (a.gpr .s3).toNat := by
    rw [ha.mem, ha.workspace, ha.remaining]; exact setupMem_prefix s
  have spaceA : Space a (s.gpr .a3).toNat := by
    refine ⟨hi, workA, ?_, ?_⟩
    · intro i hi'
      rw [ha.wr, ha.output, wr]
      exact ⟨outputR s, List.mem_cons_self .., Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    · rw [ha.workspace, ha.output]; exact ow.symm
  refine WP.seq ((first_ok a (by rw [ha.remaining]; exact ⟨lo, hi⟩)
    (by rw [ha.length]; exact len) headA workA dataA dwA).mono ?_)
  rintro b ⟨digestB, kb⟩
  have spaceB := spaceA.keeps kb
  have countB : b.gpr .s3 = BitVec.ofNat 64 (s.gpr .a3).toNat := by
    rw [kb.regs _ (by decide), ha.remaining, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have digestB' : (bytesAt b.mem (b.gpr .s4 + 768) 64).take (min (s.gpr .a3).toNat 64) =
      Spec.Argon2.H (min (s.gpr .a3).toNat 64)
        (Spec.Argon2.le32 (s.gpr .a3).toNat ++ bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) := by
    rw [kb.s4]
    simpa only [ha.remaining, inputA] using digestB
  refine WP.seq ((finishOutput_ok b (s.gpr .a3).toNat
    (bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) spaceB lo countB digestB').mono ?_)
  intro x hx
  have baseB : b.gpr .s4 = s.gpr .a4 := kb.s4.trans ha.workspace
  have dstB : b.gpr .s2 = s.gpr .a2 := (kb.regs _ (by decide)).trans ha.output
  have wrX : x.wr = s.wr := hx.wr.trans (kb.wr.trans ha.wr)
  have frame : Frame [⟨s.gpr .a4, 832⟩, outputR s] a.mem x.mem := by
    have fb : Frame [⟨s.gpr .a4, 832⟩, outputR s] a.mem b.mem := by
      apply kb.frame.sub
      intro r hr
      rw [ha.workspace] at hr
      exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    exact fb.trans (by simpa only [baseB, dstB, outputR, Proof.Argon2.hPrime_length] using hx.frame)
  have keep (d : Nat) (dlo : 832 ≤ d) (dhi : d + 8 ≤ 16384) :
      x.mem.readW (s.gpr .a4 + BitVec.ofNat 64 d) 64 = a.mem.readW (s.gpr .a4 + BitVec.ofNat 64 d) 64 := by
    apply frame.readW (r := ⟨s.gpr .a4 + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact (Offset.base_disjoint _ dlo (by omega_arith)).symm
    · exact (ow.sub_right (Offset.sub_base _ dhi)).symm
  have values : Spill.Saved (s.gpr .a4) s.gpr saved x.mem := by
    intro p hp
    have bounds := saved_bounds p hp
    rw [keep p.2 (by omega_arith) (by omega_arith), ha.mem]; exact setupMem_saved s p hp
  have baseX := (hx.regs .s4 (by decide) (by decide) (by decide)).trans baseB
  have readable : workR s ∈ x.rd ++ x.wr := List.mem_append_right _ (wrX.symm ▸ work)
  refine (restore_ok s x baseX hal (fun r hr hm => ?_) readable values).mono ?_
  · have h : r ≠ .s4 ∧ r ≠ .s0 ∧ r ≠ .s1 ∧ r ≠ .s2 ∧ r ≠ .s3 := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> exact fun e => hm (by subst e; decide)
    rw [hx.regs r hr h.2.2.2.1 h.2.2.2.2, kb.regs r hr]
    exact ha.other r h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
  rintro t ⟨regs, ra, mem, _, _, _⟩
  refine ⟨?_, regs, ra, ?_⟩
  · change bytesAt t.mem (s.gpr .a2) (s.gpr .a3).toNat = _
    rw [mem]
    simpa only [dstB, Proof.Argon2.hPrime_length] using hx.bytes
  · rw [mem]
    have setupFrame : Frame [outputR s, workR s] s.mem a.mem := by
      rw [ha.mem]
      apply (setupMem_frame s).sub
      intro r hr
      simp only [List.mem_singleton] at hr; subst r
      exact ⟨workR s, List.mem_cons_of_mem _ (List.mem_cons_self ..),
        Offset.sub_base _ (by decide : 832 + 64 ≤ 16384)⟩
    apply setupFrame.trans
    apply frame.sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨workR s, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.sub_prefix (by decide)⟩
    · exact ⟨outputR s, List.mem_cons_self .., fun _ h => h⟩

theorem code_correct (s : State) (pre : localContract.pre s) :
    ∃ tr t, Exec isa code s tr t ∧ abiPreserved s t ∧ localContract.post s t := by
  obtain ⟨tr, t, run, post, regs, lr, _⟩ := code_wp s pre
  exact ⟨tr, t, run, ⟨regs, VG.RISCV64.Exec.sp run, lr⟩, post⟩

end VG.Proof.Argon2.RISCV64.HPrime
