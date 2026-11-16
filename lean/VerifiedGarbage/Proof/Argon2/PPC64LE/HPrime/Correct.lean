module

public import VerifiedGarbage.Proof.Argon2.PPC64LE.HPrime.Contract
import VerifiedGarbage.Proof.Argon2.PPC64LE.HPrime.Compare
public import VerifiedGarbage.Proof.Argon2.PPC64LE.HPrime.Space
import VerifiedGarbage.Proof.Argon2.PPC64LE.HPrime.Absorb
import VerifiedGarbage.Proof.Argon2.PPC64LE.HPrime.Calls
import VerifiedGarbage.Proof.Argon2.PPC64LE.HPrime.Chain
import VerifiedGarbage.Proof.Argon2.PPC64LE.HPrime.Length
import VerifiedGarbage.Proof.Argon2.PPC64LE.HPrime.Setup
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Blake2.PPC64LE.Stream.Lit

@[expose] public section

/-! Merged from `Proof.Argon2.PPC64LE.HPrime.First`. -/
section
/-! Merged from `Proof.Argon2.PPC64LE.HPrime.FinishInput`. -/
section
/-! # H′: finalizing the prefixed input -/

namespace VG.Proof.Argon2.PPC64LE.HPrime

open VG VG.PPC64LE VG.Impl.Argon2.PPC64LE.HPrime
open VG.Spec.Blake2 (b Repr bytesAt)
open VG.Proof.MdStream.PPC64LE (wp_mov wp_addi)

theorem finishInput_ok (s : State)
    (h0 : Spec.Blake2.HashValue 64) (d : List Byte)
    (repr : Repr b h0 s.mem (s.gpr .r31) d)
    (length : d.length = 4 + (s.gpr .r28).toNat) (bound : (s.gpr .r28).toNat < 2 ^ 32)
    (hsp : 48 ≤ s.sp.toNat)
    (hwr : (⟨s.gpr .r31, 16384⟩ : Region) ∈ s.wr)
    (stackWork : (below s.sp 48).Disjoint ⟨s.gpr .r31, 16384⟩) :
    WP isa (finishInput) s fun t =>
      bytesAt t.mem (s.gpr .r31 + 768) 64 = Spec.Blake2.finalHash b h0 d ∧ Keeps s t := by
  unfold finishInput
  refine WP.seq (wp_addi (by decide) fun u hu => WP.block_nil ?_)
  obtain ku : Keeps s u := Keeps.of_upd hu (by decide)
  obtain repr' : Repr b h0 u.mem (u.gpr .r31) d := by rw [hu.mem, ku.r31]; exact repr
  obtain count : u.gpr .r4 = BitVec.ofNat 64 d.length := by
    rw [hu.gpr, length, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact BitVec.add_comm _ _
  obtain len : d.length < 2 ^ 64 := by rw [length]; omega_arith
  obtain wr : (⟨u.gpr .r31, 16384⟩ : Region) ∈ u.wr := by rw [ku.r31, ku.wr]; exact hwr
  obtain sw : (below u.sp 48).Disjoint ⟨u.gpr .r31, 16384⟩ := by
    rw [ku.r31, ku.sp]; exact stackWork
  refine (finalize_ok u h0 d repr' count len (by rw [ku.sp]; exact hsp) wr sw).mono ?_
  rintro t ⟨out, regs, rd, wr', sp', frame⟩
  refine ⟨?_, ku.trans ⟨regs, rd, wr', sp', finalize_frame _ _ frame⟩⟩
  simpa only [ku.r31] using out

end VG.Proof.Argon2.PPC64LE.HPrime
end

/-! # H′: the hash of the length prefix and input -/

namespace VG.Proof.Argon2.PPC64LE.HPrime

open VG VG.PPC64LE VG.Impl.Argon2.PPC64LE.HPrime
open VG.Spec.Blake2 (b Repr bytesAt)

theorem first_ok (s : State)
    (hlen : 1 ≤ (s.gpr .r30).toNat ∧ (s.gpr .r30).toNat < 2 ^ 32)
    (len : (s.gpr .r28).toNat < 2 ^ 32)
    (headBytes : bytesAt s.mem (s.gpr .r31 + 832) 4 = Spec.Argon2.le32 (s.gpr .r30).toNat)
    (hsp : 48 ≤ s.sp.toNat)
    (hwr : (⟨s.gpr .r31, 16384⟩ : Region) ∈ s.wr)
    (hdata : Covers [⟨s.gpr .r27, (s.gpr .r28).toNat⟩] (s.rd ++ s.wr))
    (dataWork : (⟨s.gpr .r27, (s.gpr .r28).toNat⟩ : Region).Disjoint ⟨s.gpr .r31, 16384⟩)
    (stackWork : (below s.sp 48).Disjoint ⟨s.gpr .r31, 16384⟩)
    (stackData : (below s.sp 48).Disjoint ⟨s.gpr .r27, (s.gpr .r28).toNat⟩) :
    WP isa (first) s fun t =>
      (bytesAt t.mem (s.gpr .r31 + 768) 64).take (min (s.gpr .r30).toNat 64) =
        Spec.Argon2.H (min (s.gpr .r30).toNat 64)
          (Spec.Argon2.le32 (s.gpr .r30).toNat ++ bytesAt s.mem (s.gpr .r27) (s.gpr .r28).toNat) ∧
      Keeps s t := by
  unfold first
  refine WP.seq ((chooseLength_ok s hlen.2).mono ?_)
  rintro a ⟨lengthA, ka⟩
  obtain na : (a.gpr .r4).toNat = min (s.gpr .r30).toNat 64 := by
    rw [lengthA, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  obtain wrA : (⟨a.gpr .r31, 16384⟩ : Region) ∈ a.wr := by rw [ka.r31, ka.wr]; exact hwr
  obtain swA : (below a.sp 48).Disjoint ⟨a.gpr .r31, 16384⟩ := by
    rw [ka.r31, ka.sp]; exact stackWork
  obtain lenA : 1 ≤ (a.gpr .r4).toNat ∧ (a.gpr .r4).toNat ≤ 64 := by rw [na]; omega_arith
  refine WP.seq ((init_ok a lenA wrA).mono ?_)
  rintro u ⟨reprU, regsU, rdU, wrU, spU, frameU⟩
  obtain ku : Keeps a u := ⟨regsU, rdU, wrU, spU, init_frame _ _ frameU⟩
  obtain ksu := ka.trans ku
  obtain reprU' : Repr b (Spec.Blake2.init b (min (s.gpr .r30).toNat 64) 0) u.mem (u.gpr .r31) [] := by
    rw [ku.r31]; simpa only [na] using reprU
  obtain wrU' : (⟨u.gpr .r31, 16384⟩ : Region) ∈ u.wr := by rw [ksu.r31, ksu.wr]; exact hwr
  obtain swU : (below u.sp 48).Disjoint ⟨u.gpr .r31, 16384⟩ := by
    rw [ksu.r31, ksu.sp]; exact stackWork
  obtain headU : bytesAt u.mem (u.gpr .r31 + 832) 4 = Spec.Argon2.le32 (s.gpr .r30).toNat := by
    rw [ksu.r31, ksu.prefix stackWork]; exact headBytes
  refine WP.seq ((absorbFixed_ok u _ 832 4 (by decide) (by rw [ksu.sp]; exact hsp) (by decide) (by decide) reprU' wrU' swU).mono ?_)
  rintro w ⟨reprW, kw⟩
  obtain ksw := ksu.trans kw
  obtain r12 : w.gpr .r27 = s.gpr .r27 := ksw.regs _ (by decide)
  obtain r13 : w.gpr .r28 = s.gpr .r28 := ksw.regs _ (by decide)
  obtain headLen : (Spec.Argon2.le32 (s.gpr .r30).toNat).length = 4 := by
    simp only [Spec.Argon2.le32, Spec.Blake2.wordBytes, List.length_map, List.length_range]
  obtain reprW' : Repr b (Spec.Blake2.init b (min (s.gpr .r30).toNat 64) 0) w.mem (w.gpr .r31)
      (Spec.Argon2.le32 (s.gpr .r30).toNat) := by
    rw [kw.r31]
    simpa only [show BitVec.ofNat 64 832 = (832 : Addr) from rfl, headU] using reprW
  obtain wrW : (⟨w.gpr .r31, 16384⟩ : Region) ∈ w.wr := by rw [ksw.r31, ksw.wr]; exact hwr
  obtain dataW : Covers [⟨w.gpr .r27, (w.gpr .r28).toNat⟩] (w.rd ++ w.wr) := by
    rw [r12, r13, ksw.rd, ksw.wr]; exact hdata
  obtain dwW : (⟨w.gpr .r27, (w.gpr .r28).toNat⟩ : Region).Disjoint ⟨w.gpr .r31, 16384⟩ := by
    rw [r12, r13, ksw.r31]; exact dataWork
  obtain swW : (below w.sp 48).Disjoint ⟨w.gpr .r31, 16384⟩ := by
    rw [ksw.sp, ksw.r31]; exact stackWork
  obtain sdW : (below w.sp 48).Disjoint ⟨w.gpr .r27, (w.gpr .r28).toNat⟩ := by
    rw [ksw.sp, r12, r13]; exact stackData
  obtain inputW : bytesAt w.mem (w.gpr .r27) (w.gpr .r28).toNat =
      bytesAt s.mem (s.gpr .r27) (s.gpr .r28).toNat := by
    rw [r12, r13]
    exact ksw.bytes _ (show (s.gpr .r28).toNat ≤ 2 ^ 64 by omega_arith)
      (dataWork.sub_right (Region.sub_prefix (by decide))) stackData.symm
  refine WP.seq ((absorbInput_ok w _ _ headLen reprW' (by rw [r13]; exact len)
    (by rw [ksw.sp]; exact hsp) wrW dataW dwW swW sdW).mono ?_)
  rintro x ⟨reprX, kx⟩
  obtain ksx := ksw.trans kx
  obtain reprX' : Repr b (Spec.Blake2.init b (min (s.gpr .r30).toNat 64) 0) x.mem (x.gpr .r31)
      (Spec.Argon2.le32 (s.gpr .r30).toNat ++ bytesAt s.mem (s.gpr .r27) (s.gpr .r28).toNat) := by
    rw [kx.r31]; simpa only [inputW] using reprX
  obtain r13X : x.gpr .r28 = s.gpr .r28 := ksx.regs _ (by decide)
  obtain length : (Spec.Argon2.le32 (s.gpr .r30).toNat ++ bytesAt s.mem (s.gpr .r27) (s.gpr .r28).toNat).length =
      4 + (x.gpr .r28).toNat := by
    rw [List.length_append, headLen, r13X]
    simp only [bytesAt, List.length_map, List.length_range]
  obtain wrX : (⟨x.gpr .r31, 16384⟩ : Region) ∈ x.wr := by rw [ksx.r31, ksx.wr]; exact hwr
  obtain swX : (below x.sp 48).Disjoint ⟨x.gpr .r31, 16384⟩ := by
    rw [ksx.sp, ksx.r31]; exact stackWork
  refine (finishInput_ok x _ _ reprX' length (by rw [r13X]; exact len) (by rw [ksx.sp]; exact hsp) wrX swX).mono ?_
  rintro t ⟨out, kt⟩
  refine ⟨?_, ksx.trans kt⟩
  obtain result := congrArg (List.take (min (s.gpr .r30).toNat 64)) out
  rw [ksx.r31] at result
  exact result.trans (Proof.Argon2.H_stream _ _).symm

end VG.Proof.Argon2.PPC64LE.HPrime
end

/-! Merged from `Proof.Argon2.PPC64LE.HPrime.Finish`. -/
section
/-! Merged from `Proof.Argon2.PPC64LE.HPrime.Extend`. -/
section
/-! # H′: the prefixes and final digest of a long output -/

namespace VG.Proof.Argon2.PPC64LE.HPrime

open VG VG.PPC64LE VG.Impl.Argon2.PPC64LE.HPrime
open VG.Proof.MdStream.PPC64LE (wp_mov)
open VG.Spec.Blake2 (bytesAt)
open VG.Proof.Argon2 (chainDigest chainPrefixes)

theorem maybeChain_ok (n lastLen : Nat) (s : State)
    (space : Space s (32 * n + lastLen)) (last : 33 ≤ lastLen ∧ lastLen ≤ 64)
    (count : s.gpr .r30 = BitVec.ofNat 64 (32 * n + lastLen))
    (comparison : s.gpr .r10 = if 32 * n + lastLen < 65 then 1 else 0) :
    WP isa (.ite (.nonzero .d .r10) (.block []) (chain)) s (ChainResult s n) := by
  refine WP.ite (decide (32 * n + lastLen < 65)) (by by_cases h : 32 * n + lastLen < 65 <;>
    simp [eval, State.read, comparison, h]) ?_ ?_
  · intro h
    obtain hn : n = 0 := by have := of_decide_eq_true h; omega_arith
    subst n
    exact WP.block_nil (ChainResult.refl s)
  · intro h
    obtain hn : 1 ≤ n := by have := of_decide_eq_false h; omega_arith
    obtain p := space.prefix (show 32 * n ≤ 32 * n + lastLen by omega_arith)
    exact chain_ok n lastLen s hn last space.bound space.spBound count p.work p.out p.sep p.stackWork p.stackOut

theorem extendDigest_ok (n lastLen : Nat) (s : State)
    (space : Space s (32 * (n + 1) + lastLen)) (last : 33 ≤ lastLen ∧ lastLen ≤ 64)
    (count : s.gpr .r30 = BitVec.ofNat 64 (32 * (n + 1) + lastLen)) :
    WP isa (extendDigest) s fun t =>
      Written s ((bytesAt s.mem (s.gpr .r31 + 768) 64).take 32 ++
        chainPrefixes n (bytesAt s.mem (s.gpr .r31 + 768) 64)) t ∧
      (bytesAt t.mem (s.gpr .r31 + 768) 64).take lastLen =
        Spec.Argon2.H lastLen (chainDigest n (bytesAt s.mem (s.gpr .r31 + 768) 64)) ∧
      t.gpr .r30 = BitVec.ofNat 64 lastLen := by
  unfold extendDigest
  obtain short := space.prefix (show 32 ≤ 32 * (n + 1) + lastLen by omega_arith)
  obtain sep32 := short.sep.sub_left (Offset.sub_base _ (by decide : 768 + 32 ≤ 16384))
  refine WP.seq ((emitPrefix_ok s short.work short.out sep32).mono ?_)
  intro a ha
  obtain wa := Written.of_emitted ha
  obtain lenA : (bytesAt s.mem (s.gpr .r31 + 768) 32).length = 32 := by
    simp only [bytesAt, List.length_map, List.length_range]
  obtain spaceA : Space a (32 * n + lastLen) := space.advance wa (by rw [lenA]; omega_arith)
  obtain countA : a.gpr .r30 = BitVec.ofNat 64 (32 * n + lastLen) := by
    rw [ha.remaining, count, show (32 : Addr) = BitVec.ofNat 64 32 from rfl,
      Offset.ofNat_sub_ofNat (by omega_arith : 32 ≤ 32 * (n + 1) + lastLen)]
    rw [show 32 * (n + 1) + lastLen - 32 = 32 * n + lastLen by omega_arith]
  obtain digestA : bytesAt a.mem (a.gpr .r31 + 768) 64 = bytesAt s.mem (s.gpr .r31 + 768) 64 := by
    rw [wa.r31]; exact ha.digest short.sep
  refine WP.seq ((compare_ok a (by rw [countA, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := spaceA.bound; omega_arith)]; exact spaceA.bound)).mono fun u compared => ?_)
  have ku := compared.keeps
  obtain countU : u.gpr .r30 = BitVec.ofNat 64 (32 * n + lastLen) :=
    (compared.other _ (by decide)).trans countA
  obtain compareU : u.gpr .r10 = if 32 * n + lastLen < 65 then 1 else 0 := by
    rw [compared.value, countA, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := spaceA.bound; omega_arith)]
  refine WP.seq ((maybeChain_ok n lastLen u (spaceA.keeps ku) last countU compareU).mono ?_)
  intro w hw
  obtain ww := (Written.of_chain hw).before_keeps ku
  obtain digestU : bytesAt u.mem (u.gpr .r31 + 768) 64 = bytesAt s.mem (s.gpr .r31 + 768) 64 := by
    rw [compared.mem, ku.r31]; exact digestA
  obtain ww' : Written a (chainPrefixes n (bytesAt s.mem (s.gpr .r31 + 768) 64)) w := by
    simpa only [digestU] using ww
  obtain wsw := space.join wa ww' (by rw [lenA, Proof.Argon2.chainPrefixes_length]; omega_arith)
  obtain produced : ((bytesAt s.mem (s.gpr .r31 + 768) 32) ++
      chainPrefixes n (bytesAt s.mem (s.gpr .r31 + 768) 64)).length = 32 * (n + 1) := by
    rw [List.length_append, lenA, Proof.Argon2.chainPrefixes_length]; omega_arith
  obtain spaceW : Space w lastLen := space.advance wsw (by rw [produced])
  obtain countW : w.gpr .r30 = BitVec.ofNat 64 lastLen := by
    rw [hw.remaining, countU, Offset.ofNat_sub_ofNat (by omega_arith : 32 * n ≤ 32 * n + lastLen)]
    rw [Nat.add_sub_cancel_left]
  obtain digestW : bytesAt w.mem (w.gpr .r31 + 768) 64 =
      chainDigest n (bytesAt s.mem (s.gpr .r31 + 768) 64) := by
    rw [hw.regs .r31 (by decide) (by decide) (by decide), hw.digest, digestU]
  refine WP.seq (wp_mov fun x hx => WP.block_nil ?_)
  obtain kx : Keeps w x := Keeps.of_upd hx (by decide)
  obtain spaceX := spaceW.keeps kx
  obtain lenX : (x.gpr .r4).toNat = lastLen := by
    rw [hx.gpr, countW, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := spaceW.bound; omega_arith)]
  refine (next_ok x (by rw [lenX]; omega_arith) spaceX.spBound spaceX.work spaceX.stackWork).mono ?_
  rintro t ⟨dt, kt⟩
  obtain wwt := Written.of_keeps (kx.trans kt)
  obtain written := space.join wsw wwt (by rw [produced, List.length_nil]; omega_arith)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [List.append_nil, bytesAt_take _ _ 32 64 (by decide)] using written
  · rw [lenX, kx.r31, hx.mem, digestW, wsw.r31] at dt
    exact dt
  · rw [kt.regs _ (by decide), kx.regs _ (by decide)]; exact countW

theorem longOutput_ok (n lastLen : Nat) (s : State)
    (space : Space s (32 * (n + 1) + lastLen)) (last : 33 ≤ lastLen ∧ lastLen ≤ 64)
    (count : s.gpr .r30 = BitVec.ofNat 64 (32 * (n + 1) + lastLen)) :
    WP isa (.seq (extendDigest) copyRemaining) s fun t =>
      Written s (Spec.Argon2.longHash lastLen (n + 1) (bytesAt s.mem (s.gpr .r31 + 768) 64)) t := by
  refine WP.seq ((extendDigest_ok n lastLen s space last count).mono ?_)
  rintro u ⟨written, digest, remaining⟩
  obtain len : ((bytesAt s.mem (s.gpr .r31 + 768) 64).take 32 ++
      chainPrefixes n (bytesAt s.mem (s.gpr .r31 + 768) 64)).length = 32 * (n + 1) := by
    simp only [List.length_append, List.length_take, bytesAt, List.length_map,
      List.length_range, Proof.Argon2.chainPrefixes_length]
    omega_arith
  obtain spaceU : Space u lastLen := space.advance written (by rw [len])
  refine (copyRemaining_ok u lastLen spaceU (by omega_arith) last.2 remaining).mono ?_
  intro t copied
  obtain out : bytesAt u.mem (u.gpr .r31 + 768) lastLen =
      Spec.Argon2.H lastLen (chainDigest n (bytesAt s.mem (s.gpr .r31 + 768) 64)) := by
    rw [written.r31, ← bytesAt_take _ _ lastLen 64 last.2]; exact digest
  obtain all := space.join written copied (by
    rw [len]; simp only [bytesAt, List.length_map, List.length_range, Nat.le_refl])
  rw [out, ← Proof.Argon2.longHash_chain] at all
  exact all

end VG.Proof.Argon2.PPC64LE.HPrime
end

/-! # H′: emitting the complete short or long output -/

namespace VG.Proof.Argon2.PPC64LE.HPrime

open VG VG.PPC64LE VG.Impl.Argon2.PPC64LE.HPrime
open VG.Spec.Blake2 (bytesAt)

theorem finishOutput_ok (s : State) (n : Nat) (input : List Byte)
    (space : Space s n) (positive : 1 ≤ n) (count : s.gpr .r30 = BitVec.ofNat 64 n)
    (digest : (bytesAt s.mem (s.gpr .r31 + 768) 64).take (min n 64) =
      Spec.Argon2.H (min n 64) (Spec.Argon2.le32 n ++ input)) :
    WP isa (finishOutput) s (Written s (Spec.Argon2.hPrime n input)) := by
  unfold finishOutput
  refine WP.seq ((compare_ok s (by rw [count, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := space.bound; omega_arith)]; exact space.bound)).mono fun u compared => ?_)
  have ku := compared.keeps
  obtain countU : u.gpr .r30 = BitVec.ofNat 64 n := (compared.other _ (by decide)).trans count
  obtain compareU : u.gpr .r10 = if n < 65 then 1 else 0 := by
    rw [compared.value, count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := space.bound; omega_arith)]
  apply WP.seq
  refine WP.ite (decide (n < 65)) (by by_cases h : n < 65 <;> simp [eval, State.read, compareU, h]) ?_ ?_
  · intro h
    obtain short : n ≤ 64 := by have := of_decide_eq_true h; omega_arith
    apply WP.block_nil
    refine (copyRemaining_ok u n (space.keeps ku) positive short countU).mono ?_
    intro t ht
    obtain result := ht.before_keeps ku
    obtain value : bytesAt u.mem (u.gpr .r31 + 768) n = Spec.Argon2.hPrime n input := by
      rw [compared.mem, ku.r31, ← bytesAt_take _ _ n 64 short]
      simpa only [Nat.min_eq_left short, Spec.Argon2.hPrime, ite_eq_left short] using digest
    rw [value] at result
    exact result
  · intro h
    obtain long : 64 < n := by have := of_decide_eq_false h; omega_arith
    let r := (n + 31) / 32 - 2
    let lastLen := n - 32 * r
    obtain bounds : 1 ≤ r ∧ 33 ≤ lastLen ∧ lastLen ≤ 64 ∧ 32 * r + lastLen = n :=
      Proof.Argon2.longHash_bounds n long
    obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero (show r ≠ 0 by omega_arith)
    change r = q + 1 at hq
    obtain size : 32 * (q + 1) + lastLen = n := by rw [← hq]; exact bounds.2.2.2
    obtain spaceU : Space u (32 * (q + 1) + lastLen) := by rw [size]; exact space.keeps ku
    obtain countLong : u.gpr .r30 = BitVec.ofNat 64 (32 * (q + 1) + lastLen) := by rw [size]; exact countU
    apply WP.seq_iff.mp
    refine (longOutput_ok q lastLen u spaceU ⟨bounds.2.1, bounds.2.2.1⟩ countLong).mono ?_
    intro t ht
    obtain result := ht.before_keeps ku
    obtain digestU : bytesAt u.mem (u.gpr .r31 + 768) 64 =
        Spec.Argon2.H 64 (Spec.Argon2.le32 n ++ input) := by
      rw [compared.mem, ku.r31]
      simpa only [Nat.min_eq_right (show 64 ≤ n by omega_arith), bytesAt_take _ _ 64 64 (by decide)] using digest
    obtain value : Spec.Argon2.longHash lastLen (q + 1) (bytesAt u.mem (u.gpr .r31 + 768) 64) =
        Spec.Argon2.hPrime n input := by
      rw [digestU, ← hq, Spec.Argon2.hPrime, ite_eq_right (show ¬ n ≤ 64 by omega_arith)]
    rw [value] at result
    exact result

end VG.Proof.Argon2.PPC64LE.HPrime
end

/-! # H′: functional correctness of the complete ARM64 program -/

namespace VG.Proof.Argon2.PPC64LE.HPrime

open VG VG.PPC64LE VG.Impl.Argon2.PPC64LE.HPrime
open VG.Spec.Blake2 (bytesAt)

theorem code_wp (s : State) (pre : localContract.pre s) :
    WP isa code s fun t => localContract.post s t ∧
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.lr = s.lr ∧
      Frame [outputR s, workR s, stackR s] s.mem t.mem := by
  obtain ⟨rd, wr, len, lo, hi, hsp, dw, ow, sd, so, sw⟩ := pre
  obtain work : (workR s) ∈ s.wr := by rw [wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  unfold code
  refine WP.seq ((setup_ok s work).mono ?_)
  intro a ha
  have sp := ha.sp
  obtain workA : (⟨a.gpr .r31, 16384⟩ : Region) ∈ a.wr := by
    rw [ha.workspace, ha.wr]; exact work
  obtain dataA : Covers [⟨a.gpr .r27, (a.gpr .r28).toNat⟩] (a.rd ++ a.wr) := by
    rw [ha.input, ha.length, ha.rd, rd]
    intro p n ⟨r, hr, hc⟩
    exact ⟨r, List.mem_append_left _ hr, hc⟩
  obtain dwA : (⟨a.gpr .r27, (a.gpr .r28).toNat⟩ : Region).Disjoint ⟨a.gpr .r31, 16384⟩ := by
    rw [ha.input, ha.length, ha.workspace]; exact dw
  obtain swA : (below a.sp 48).Disjoint ⟨a.gpr .r31, 16384⟩ := by
    rw [sp, ha.workspace]; exact sw
  obtain sdA : (below a.sp 48).Disjoint ⟨a.gpr .r27, (a.gpr .r28).toNat⟩ := by
    rw [sp, ha.input, ha.length]; exact sd
  obtain inputA : bytesAt a.mem (a.gpr .r27) (a.gpr .r28).toNat =
      bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat := by
    rw [ha.input, ha.length, ha.mem]
    apply Proof.Blake2.bytesAt_congr
    intro i hi'
    apply (setupMem_frame s).bytes (R := inputR s) _ (show (s.gpr .r4).toNat ≤ 2 ^ 64 by omega_arith) hi'
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact dw.sub_right (Offset.sub_base _ (by decide : 832 + 64 ≤ 16384))
  obtain headA : bytesAt a.mem (a.gpr .r31 + 832) 4 = Spec.Argon2.le32 (a.gpr .r30).toNat := by
    rw [ha.mem, ha.workspace, ha.remaining]; exact setupMem_prefix s
  obtain spaceA : Space a (s.gpr .r6).toNat := by
    refine ⟨hi, by rw [sp]; exact hsp, workA, ?_, ?_, swA, ?_⟩
    · intro i hi'
      rw [ha.wr, ha.output, wr]
      exact ⟨outputR s, List.mem_cons_self .., Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    · rw [ha.workspace, ha.output]; exact ow.symm
    · rw [sp, ha.output]; exact so
  refine WP.seq ((first_ok a (by rw [ha.remaining]; exact ⟨lo, hi⟩)
    (by rw [ha.length]; exact len) headA (by rw [sp]; exact hsp) workA dataA dwA swA sdA).mono ?_)
  rintro b ⟨digestB, kb⟩
  obtain spaceB := spaceA.keeps kb
  obtain countB : b.gpr .r30 = BitVec.ofNat 64 (s.gpr .r6).toNat := by
    rw [kb.regs _ (by decide), ha.remaining, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain digestB' : (bytesAt b.mem (b.gpr .r31 + 768) 64).take (min (s.gpr .r6).toNat 64) =
      Spec.Argon2.H (min (s.gpr .r6).toNat 64)
        (Spec.Argon2.le32 (s.gpr .r6).toNat ++ bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat) := by
    rw [kb.r31]
    simpa only [ha.remaining, inputA] using digestB
  refine WP.seq ((finishOutput_ok b (s.gpr .r6).toNat
    (bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat) spaceB lo countB digestB').mono ?_)
  intro x hx
  obtain baseB : b.gpr .r31 = s.gpr .r7 := kb.r31.trans ha.workspace
  obtain spB : b.sp = s.sp := kb.sp.trans sp
  obtain dstB : b.gpr .r29 = s.gpr .r5 := (kb.regs _ (by decide)).trans ha.output
  obtain wrX : x.wr = s.wr := hx.wr.trans (kb.wr.trans ha.wr)
  obtain frame : Frame [⟨s.gpr .r7, 832⟩, stackR s, outputR s] a.mem x.mem := by
    obtain fb : Frame [⟨s.gpr .r7, 832⟩, stackR s, outputR s] a.mem b.mem := by
      apply kb.frame.sub
      intro r hr
      rw [ha.workspace, sp] at hr
      exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    exact fb.trans (by simpa only [baseB, spB, dstB, stackR, outputR, Proof.Argon2.hPrime_length] using hx.frame)
  have keep (d : Nat) (dlo : 832 ≤ d) (dhi : d + 8 ≤ 16384) :
      x.mem.readW (s.gpr .r7 + BitVec.ofNat 64 d) 64 = a.mem.readW (s.gpr .r7 + BitVec.ofNat 64 d) 64 := by
    apply frame.readW (r := ⟨s.gpr .r7 + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact (Offset.base_disjoint _ dlo (by omega_arith)).symm
    · exact (sw.sub_right (Offset.sub_base _ dhi)).symm
    · exact (ow.sub_right (Offset.sub_base _ dhi)).symm
  obtain values : ∀ r d, (r, d) ∈ saved →
      x.mem.readW (s.gpr .r7 + BitVec.ofNat 64 d) 64 = s.gpr r := by
    intro r d hr
    obtain bounds := saved_bounds (r, d) hr
    rw [keep d (by omega_arith) (by omega_arith), ha.mem]; exact setupMem_saved s r d hr
  obtain lrSlot : x.mem.readW (s.gpr .r7 + BitVec.ofNat 64 880) 64 = s.lr := by
    rw [keep 880 (by decide) (by decide), ha.mem]; exact setupMem_lr s
  obtain baseX := (hx.regs .r31 (by decide) (by decide) (by decide)).trans baseB
  obtain readable : workR s ∈ x.rd ++ x.wr := List.mem_append_right _ (wrX.symm ▸ work)
  refine (restore_ok s x baseX (fun r hr hm => ?_) readable values lrSlot).mono ?_
  · have h : r ≠ .r0 ∧ r ≠ .r31 ∧ r ≠ .r27 ∧ r ≠ .r28 ∧ r ≠ .r29 ∧ r ≠ .r30 := by
      refine ⟨preserved_ne hr, ?_, ?_, ?_, ?_, ?_⟩ <;> exact fun e => hm (by subst e; decide)
    rw [hx.regs r hr h.2.2.2.2.1 h.2.2.2.2.2, kb.regs r hr]
    exact ha.other r h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2
  rintro t ⟨regs, lr, mem, _, _, _⟩
  refine ⟨?_, regs, lr, ?_⟩
  · change bytesAt t.mem (s.gpr .r5) (s.gpr .r6).toNat = _
    rw [mem]
    simpa only [dstB, Proof.Argon2.hPrime_length] using hx.bytes
  · rw [mem]
    obtain setupFrame : Frame [outputR s, workR s, stackR s] s.mem a.mem := by
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
    rcases hr with rfl | rfl | rfl
    · exact ⟨workR s, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.sub_prefix (by decide)⟩
    · exact ⟨stackR s, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), fun _ h => h⟩
    · exact ⟨outputR s, List.mem_cons_self .., fun _ h => h⟩

theorem code_correct (s : State) (pre : localContract.pre s) :
    ∃ tr t, Exec isa code s tr t ∧ abiPreserved s t ∧ localContract.post s t := by
  obtain ⟨tr, t, run, post, regs, lr, _⟩ := code_wp s pre
  exact ⟨tr, t, run, ⟨regs, VG.PPC64LE.Exec.sp run, lr⟩, post⟩

end VG.Proof.Argon2.PPC64LE.HPrime
