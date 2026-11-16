module

public import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Contract
public import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Space
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Absorb
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Input
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Length
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Setup
import VerifiedGarbage.Proof.Blake2.X86_64.Stream.CT
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Finalize
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Copy
import VerifiedGarbage.Proof.MdStream.X86_64.Common
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Spill

/-! Merged from `Proof.Argon2.X86_64.HPrime.Restore`. -/

@[expose] public section

section
/-! # H′: restoring the caller's registers -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime

theorem restore_ok (original s : State) (base : s.gpr .rbx = original.gpr .r8)
    (sp : s.gpr .rsp = original.gpr .rsp)
    (readable : (⟨original.gpr .r8, 16384⟩ : Region) ∈ s.rd ++ s.wr)
    (values : ∀ r d, (r, d) ∈ saved →
      s.mem.readW (original.gpr .r8 + BitVec.ofNat 64 d) 64 = original.gpr r) :
    WP isa (.block restore) s fun t =>
      (∀ r ∈ calleeSaved, t.gpr r = original.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have read (d : Nat) (h : d + 8 ≤ 16384) :
      InRegions (s.rd ++ s.wr) (original.gpr .r8 + BitVec.ofNat 64 d) 8 :=
    ⟨_, readable, Offset.contains_base _ h (by omega_arith)⟩
  obtain r840 := read 840 (by decide)
  obtain r848 := read 848 (by decide)
  obtain r856 := read 856 (by decide)
  obtain r864 := read 864 (by decide)
  obtain r872 := read 872 (by decide)
  obtain r880 := read 880 (by decide)
  obtain v840 := values .rbp 840 (by decide)
  obtain v848 := values .r12 848 (by decide)
  obtain v856 := values .r13 856 (by decide)
  obtain v864 := values .r14 864 (by decide)
  obtain v872 := values .r15 872 (by decide)
  obtain v880 := values .rbx 880 (by decide)
  apply WP.of_runBlock
  simp only [restore, saved, List.map_cons, List.map_nil, runBlock_cons,
    runStep_some, runBlock_nil, exec, readSrc, State.load64, ea_at,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    base, r840, r848, r856, r864, r872, r880, v840, v848, v856, v864, v872, v880,
    reduceCtorEq, ite_true, ite_false, Option.map_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨fun r hr => ?_, trivial, trivial, trivial⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [reduceCtorEq, ite_true, ite_false, sp]

end VG.Proof.Argon2.X86_64.HPrime
end

/-! Merged from `Proof.Argon2.X86_64.HPrime.First`. -/
section
/-! Merged from `Proof.Argon2.X86_64.HPrime.FinishInput`. -/
section
/-! # H′: finalizing the prefixed input -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime
open VG.Spec.Blake2 (b Repr bytesAt)
open VG.Proof.MdStream.X86_64 (wp_mov wp_addi)

theorem finishInput_ok (v : Proof.Blake2.X86_64.Backend) (s : State)
    (h0 : Spec.Blake2.HashValue 64) (d : List Byte)
    (repr : Repr b h0 s.mem (s.gpr .rbx) d)
    (length : d.length = 4 + (s.gpr .r13).toNat) (bound : (s.gpr .r13).toNat < 2 ^ 32)
    (hwr : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr)
    (stackWork : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rbx, 16384⟩) :
    WP isa (finishInput (hash v)) s fun t =>
      bytesAt t.mem (s.gpr .rbx + 768) 64 = Spec.Blake2.finalHash b h0 d ∧ Keeps s t := by
  unfold finishInput
  refine WP.seq (wp_mov fun a ha _ _ => wp_addi fun u hu => WP.block_nil ?_)
  obtain ku : Keeps s u := by
    refine ⟨fun r hr => ?_, hu.rd.trans ha.rd, hu.wr.trans ha.wr, ?_⟩
    · have hn : r ≠ .rsi := by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact (hu.other r hn).trans (ha.other r hn)
    · rw [hu.mem, ha.mem]; exact Frame.refl _ _
  obtain repr' : Repr b h0 u.mem (u.gpr .rbx) d := by rw [hu.mem, ha.mem, ku.rbx]; exact repr
  obtain count : u.gpr .rsi = BitVec.ofNat 64 d.length := by
    rw [hu.gpr, ha.gpr, length, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact BitVec.add_comm _ _
  obtain len : d.length < 2 ^ 64 := by rw [length]; omega_arith
  obtain wr : (⟨u.gpr .rbx, 16384⟩ : Region) ∈ u.wr := by rw [ku.rbx, ku.wr]; exact hwr
  obtain sw : (below (u.gpr .rsp) 16).Disjoint ⟨u.gpr .rbx, 16384⟩ := by
    rw [ku.rbx, ku.rsp]; exact stackWork
  refine (finalize_ok v u h0 d repr' count len wr sw).mono ?_
  rintro t ⟨out, regs, rd, wr', frame⟩
  refine ⟨?_, ku.trans ⟨regs, rd, wr', finalize_frame _ _ frame⟩⟩
  simpa only [ku.rbx] using out

end VG.Proof.Argon2.X86_64.HPrime
end

/-! # H′: the hash of the length prefix and input -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime
open VG.Spec.Blake2 (b Repr bytesAt)

theorem first_ok (v : Proof.Blake2.X86_64.Backend) (s : State)
    (hlen : 1 ≤ (s.gpr .r15).toNat ∧ (s.gpr .r15).toNat < 2 ^ 32)
    (len : (s.gpr .r13).toNat < 2 ^ 32)
    (headBytes : bytesAt s.mem (s.gpr .rbx + 832) 4 = Spec.Argon2.le32 (s.gpr .r15).toNat)
    (hwr : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr)
    (hdata : Covers [⟨s.gpr .r12, (s.gpr .r13).toNat⟩] (s.rd ++ s.wr))
    (dataWork : (⟨s.gpr .r12, (s.gpr .r13).toNat⟩ : Region).Disjoint ⟨s.gpr .rbx, 16384⟩)
    (stackWork : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rbx, 16384⟩)
    (stackData : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .r12, (s.gpr .r13).toNat⟩) :
    WP isa (first (hash v)) s fun t =>
      (bytesAt t.mem (s.gpr .rbx + 768) 64).take (min (s.gpr .r15).toNat 64) =
        Spec.Argon2.H (min (s.gpr .r15).toNat 64)
          (Spec.Argon2.le32 (s.gpr .r15).toNat ++ bytesAt s.mem (s.gpr .r12) (s.gpr .r13).toNat) ∧
      Keeps s t := by
  unfold first
  refine WP.seq ((chooseLength_ok s).mono ?_)
  rintro a ⟨lengthA, ka⟩
  obtain na : (a.gpr .rsi).toNat = min (s.gpr .r15).toNat 64 := by
    rw [lengthA, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  obtain wrA : (⟨a.gpr .rbx, 16384⟩ : Region) ∈ a.wr := by rw [ka.rbx, ka.wr]; exact hwr
  obtain swA : (below (a.gpr .rsp) 16).Disjoint ⟨a.gpr .rbx, 16384⟩ := by
    rw [ka.rbx, ka.rsp]; exact stackWork
  obtain retA : (below (a.gpr .rsp) 8).Disjoint ⟨a.gpr .rbx, 192⟩ :=
    (swA.sub_left (below_sub (by decide) (by decide))).sub_right (Region.sub_prefix (by decide))
  obtain lenA : 1 ≤ (a.gpr .rsi).toNat ∧ (a.gpr .rsi).toNat ≤ 64 := by rw [na]; omega_arith
  refine WP.seq ((init_ok v a lenA wrA retA).mono ?_)
  rintro u ⟨reprU, regsU, rdU, wrU, frameU⟩
  obtain ku : Keeps a u := ⟨regsU, rdU, wrU, init_frame _ _ frameU⟩
  obtain ksu := ka.trans ku
  obtain reprU' : Repr b (Spec.Blake2.init b (min (s.gpr .r15).toNat 64) 0) u.mem (u.gpr .rbx) [] := by
    rw [ku.rbx]; simpa only [na] using reprU
  obtain wrU' : (⟨u.gpr .rbx, 16384⟩ : Region) ∈ u.wr := by rw [ksu.rbx, ksu.wr]; exact hwr
  obtain swU : (below (u.gpr .rsp) 16).Disjoint ⟨u.gpr .rbx, 16384⟩ := by
    rw [ksu.rbx, ksu.rsp]; exact stackWork
  obtain headU : bytesAt u.mem (u.gpr .rbx + 832) 4 = Spec.Argon2.le32 (s.gpr .r15).toNat := by
    rw [ksu.rbx, ksu.prefix stackWork]; exact headBytes
  refine WP.seq ((absorbFixed_ok v u _ 832 4 (by decide) (by decide) reprU' wrU' swU).mono ?_)
  rintro w ⟨reprW, kw⟩
  obtain ksw := ksu.trans kw
  obtain r12 : w.gpr .r12 = s.gpr .r12 := ksw.regs _ (by decide)
  obtain r13 : w.gpr .r13 = s.gpr .r13 := ksw.regs _ (by decide)
  obtain headLen : (Spec.Argon2.le32 (s.gpr .r15).toNat).length = 4 := by
    simp only [Spec.Argon2.le32, Spec.Blake2.wordBytes, List.length_map, List.length_range]
  obtain reprW' : Repr b (Spec.Blake2.init b (min (s.gpr .r15).toNat 64) 0) w.mem (w.gpr .rbx)
      (Spec.Argon2.le32 (s.gpr .r15).toNat) := by
    rw [kw.rbx]
    simpa only [show BitVec.ofNat 64 832 = (832 : Addr) from rfl, headU] using reprW
  obtain wrW : (⟨w.gpr .rbx, 16384⟩ : Region) ∈ w.wr := by rw [ksw.rbx, ksw.wr]; exact hwr
  obtain dataW : Covers [⟨w.gpr .r12, (w.gpr .r13).toNat⟩] (w.rd ++ w.wr) := by
    rw [r12, r13, ksw.rd, ksw.wr]; exact hdata
  obtain dwW : (⟨w.gpr .r12, (w.gpr .r13).toNat⟩ : Region).Disjoint ⟨w.gpr .rbx, 16384⟩ := by
    rw [r12, r13, ksw.rbx]; exact dataWork
  obtain swW : (below (w.gpr .rsp) 16).Disjoint ⟨w.gpr .rbx, 16384⟩ := by
    rw [ksw.rsp, ksw.rbx]; exact stackWork
  obtain sdW : (below (w.gpr .rsp) 16).Disjoint ⟨w.gpr .r12, (w.gpr .r13).toNat⟩ := by
    rw [ksw.rsp, r12, r13]; exact stackData
  obtain inputW : bytesAt w.mem (w.gpr .r12) (w.gpr .r13).toNat =
      bytesAt s.mem (s.gpr .r12) (s.gpr .r13).toNat := by
    rw [r12, r13]
    exact ksw.bytes _ (show (s.gpr .r13).toNat ≤ 2 ^ 64 by omega_arith)
      (dataWork.sub_right (Region.sub_prefix (by decide))) stackData.symm
  refine WP.seq ((absorbInput_ok v w _ _ headLen reprW' (by rw [r13]; exact len)
    wrW dataW dwW swW sdW).mono ?_)
  rintro x ⟨reprX, kx⟩
  obtain ksx := ksw.trans kx
  obtain reprX' : Repr b (Spec.Blake2.init b (min (s.gpr .r15).toNat 64) 0) x.mem (x.gpr .rbx)
      (Spec.Argon2.le32 (s.gpr .r15).toNat ++ bytesAt s.mem (s.gpr .r12) (s.gpr .r13).toNat) := by
    rw [kx.rbx]; simpa only [inputW] using reprX
  obtain r13X : x.gpr .r13 = s.gpr .r13 := ksx.regs _ (by decide)
  obtain length : (Spec.Argon2.le32 (s.gpr .r15).toNat ++ bytesAt s.mem (s.gpr .r12) (s.gpr .r13).toNat).length =
      4 + (x.gpr .r13).toNat := by
    rw [List.length_append, headLen, r13X]
    simp only [bytesAt, List.length_map, List.length_range]
  obtain wrX : (⟨x.gpr .rbx, 16384⟩ : Region) ∈ x.wr := by rw [ksx.rbx, ksx.wr]; exact hwr
  obtain swX : (below (x.gpr .rsp) 16).Disjoint ⟨x.gpr .rbx, 16384⟩ := by
    rw [ksx.rsp, ksx.rbx]; exact stackWork
  refine (finishInput_ok v x _ _ reprX' length (by rw [r13X]; exact len) wrX swX).mono ?_
  rintro t ⟨out, kt⟩
  refine ⟨?_, ksx.trans kt⟩
  obtain result := congrArg (List.take (min (s.gpr .r15).toNat 64)) out
  rw [ksx.rbx] at result
  exact result.trans (Proof.Argon2.H_stream _ _).symm

end VG.Proof.Argon2.X86_64.HPrime
end

/-! Merged from `Proof.Argon2.X86_64.HPrime.Finish`. -/
section
/-! Merged from `Proof.Argon2.X86_64.HPrime.Extend`. -/
section
/-! # H′: the prefixes and final digest of a long output -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime
open VG.Proof.MdStream.X86_64 (wp_mov wp_cmpi)
open VG.Spec.Blake2 (bytesAt)
open VG.Proof.Argon2 (chainDigest chainPrefixes)

theorem maybeChain_ok (v : Proof.Blake2.X86_64.Backend) (n lastLen : Nat) (s : State)
    (space : Space s (32 * n + lastLen)) (last : 33 ≤ lastLen ∧ lastLen ≤ 64)
    (count : s.gpr .r15 = BitVec.ofNat 64 (32 * n + lastLen))
    (cf : s.cf = some (decide (32 * n + lastLen < 65))) :
    WP isa (.ite .b (.block []) (chain (hash v))) s (ChainResult s n) := by
  refine WP.ite (decide (32 * n + lastLen < 65)) (by simp only [eval, cf]) ?_ ?_
  · intro h
    obtain hn : n = 0 := by have := of_decide_eq_true h; omega_arith
    subst n
    exact WP.block_nil (ChainResult.refl s)
  · intro h
    obtain hn : 1 ≤ n := by have := of_decide_eq_false h; omega_arith
    obtain p := space.prefix (show 32 * n ≤ 32 * n + lastLen by omega_arith)
    exact chain_ok v n lastLen s hn last space.bound count p.work p.out p.sep p.stackWork p.stackOut

theorem extendDigest_ok (v : Proof.Blake2.X86_64.Backend) (n lastLen : Nat) (s : State)
    (space : Space s (32 * (n + 1) + lastLen)) (last : 33 ≤ lastLen ∧ lastLen ≤ 64)
    (count : s.gpr .r15 = BitVec.ofNat 64 (32 * (n + 1) + lastLen)) :
    WP isa (extendDigest (hash v)) s fun t =>
      Written s ((bytesAt s.mem (s.gpr .rbx + 768) 64).take 32 ++
        chainPrefixes n (bytesAt s.mem (s.gpr .rbx + 768) 64)) t ∧
      (bytesAt t.mem (s.gpr .rbx + 768) 64).take lastLen =
        Spec.Argon2.H lastLen (chainDigest n (bytesAt s.mem (s.gpr .rbx + 768) 64)) ∧
      t.gpr .r15 = BitVec.ofNat 64 lastLen := by
  unfold extendDigest
  obtain short := space.prefix (show 32 ≤ 32 * (n + 1) + lastLen by omega_arith)
  obtain sep32 := short.sep.sub_left (Offset.sub_base _ (by decide : 768 + 32 ≤ 16384))
  refine WP.seq ((emitPrefix_ok s short.work short.out sep32).mono ?_)
  intro a ha
  obtain wa := Written.of_emitted ha
  obtain lenA : (bytesAt s.mem (s.gpr .rbx + 768) 32).length = 32 := by
    simp only [bytesAt, List.length_map, List.length_range]
  obtain spaceA : Space a (32 * n + lastLen) := space.advance wa (by rw [lenA]; omega_arith)
  obtain countA : a.gpr .r15 = BitVec.ofNat 64 (32 * n + lastLen) := by
    rw [ha.remaining, count, show (32 : Addr) = BitVec.ofNat 64 32 from rfl,
      Offset.ofNat_sub_ofNat (by omega_arith : 32 ≤ 32 * (n + 1) + lastLen)]
    rw [show 32 * (n + 1) + lastLen - 32 = 32 * n + lastLen by omega_arith]
  obtain digestA : bytesAt a.mem (a.gpr .rbx + 768) 64 = bytesAt s.mem (s.gpr .rbx + 768) 64 := by
    rw [wa.rbx]; exact ha.digest short.sep
  refine WP.seq (wp_cmpi fun u gu mu ru wu cf _ => WP.block_nil ?_)
  obtain ku : Keeps a u := ⟨fun r _ => congrFun gu r, ru, wu, by rw [mu]; exact Frame.refl _ _⟩
  obtain countU : u.gpr .r15 = BitVec.ofNat 64 (32 * n + lastLen) := (congrFun gu _).trans countA
  obtain cfU : u.cf = some (decide (32 * n + lastLen < 65)) := by
    rw [cf, countA, BitVec.toNat_ofNat, Nat.mod_eq_of_lt spaceA.bound]; rfl
  refine WP.seq ((maybeChain_ok v n lastLen u (spaceA.keeps ku) last countU cfU).mono ?_)
  intro w hw
  obtain ww := (Written.of_chain hw).before_keeps ku
  obtain digestU : bytesAt u.mem (u.gpr .rbx + 768) 64 = bytesAt s.mem (s.gpr .rbx + 768) 64 := by
    rw [mu, gu]; exact digestA
  obtain ww' : Written a (chainPrefixes n (bytesAt s.mem (s.gpr .rbx + 768) 64)) w := by
    simpa only [digestU] using ww
  obtain wsw := space.join wa ww' (by rw [lenA, Proof.Argon2.chainPrefixes_length]; omega_arith)
  obtain produced : ((bytesAt s.mem (s.gpr .rbx + 768) 32) ++
      chainPrefixes n (bytesAt s.mem (s.gpr .rbx + 768) 64)).length = 32 * (n + 1) := by
    rw [List.length_append, lenA, Proof.Argon2.chainPrefixes_length]; omega_arith
  obtain spaceW : Space w lastLen := space.advance wsw (by rw [produced])
  obtain countW : w.gpr .r15 = BitVec.ofNat 64 lastLen := by
    rw [hw.remaining, countU, Offset.ofNat_sub_ofNat (by omega_arith : 32 * n ≤ 32 * n + lastLen)]
    rw [Nat.add_sub_cancel_left]
  obtain digestW : bytesAt w.mem (w.gpr .rbx + 768) 64 =
      chainDigest n (bytesAt s.mem (s.gpr .rbx + 768) 64) := by
    rw [hw.regs .rbx (by decide) (by decide) (by decide), hw.digest, digestU]
  refine WP.seq (wp_mov fun x hx _ _ => WP.block_nil ?_)
  obtain kx : Keeps w x := by
    refine ⟨fun r hr => ?_, hx.rd, hx.wr, ?_⟩
    · have hn : r ≠ .rsi := by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact hx.other r hn
    · rw [hx.mem]; exact Frame.refl _ _
  obtain spaceX := spaceW.keeps kx
  obtain lenX : (x.gpr .rsi).toNat = lastLen := by
    rw [hx.gpr, countW, BitVec.toNat_ofNat, Nat.mod_eq_of_lt spaceW.bound]
  refine (next_ok v x (by rw [lenX]; omega_arith) spaceX.work spaceX.stackWork).mono ?_
  rintro t ⟨dt, kt⟩
  obtain wwt := Written.of_keeps (kx.trans kt)
  obtain written := space.join wsw wwt (by rw [produced, List.length_nil]; omega_arith)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [List.append_nil, bytesAt_take _ _ 32 64 (by decide)] using written
  · rw [lenX, kx.rbx, hx.mem, digestW, wsw.rbx] at dt
    exact dt
  · rw [kt.regs _ (by decide), kx.regs _ (by decide)]; exact countW

theorem longOutput_ok (v : Proof.Blake2.X86_64.Backend) (n lastLen : Nat) (s : State)
    (space : Space s (32 * (n + 1) + lastLen)) (last : 33 ≤ lastLen ∧ lastLen ≤ 64)
    (count : s.gpr .r15 = BitVec.ofNat 64 (32 * (n + 1) + lastLen)) :
    WP isa (.seq (extendDigest (hash v)) copyRemaining) s fun t =>
      Written s (Spec.Argon2.longHash lastLen (n + 1) (bytesAt s.mem (s.gpr .rbx + 768) 64)) t := by
  refine WP.seq ((extendDigest_ok v n lastLen s space last count).mono ?_)
  rintro u ⟨written, digest, remaining⟩
  obtain len : ((bytesAt s.mem (s.gpr .rbx + 768) 64).take 32 ++
      chainPrefixes n (bytesAt s.mem (s.gpr .rbx + 768) 64)).length = 32 * (n + 1) := by
    simp only [List.length_append, List.length_take, bytesAt, List.length_map,
      List.length_range, Proof.Argon2.chainPrefixes_length]
    omega_arith
  obtain spaceU : Space u lastLen := space.advance written (by rw [len])
  refine (copyRemaining_ok u lastLen spaceU (by omega_arith) last.2 remaining).mono ?_
  intro t copied
  obtain out : bytesAt u.mem (u.gpr .rbx + 768) lastLen =
      Spec.Argon2.H lastLen (chainDigest n (bytesAt s.mem (s.gpr .rbx + 768) 64)) := by
    rw [written.rbx, ← bytesAt_take _ _ lastLen 64 last.2]; exact digest
  obtain all := space.join written copied (by
    rw [len]; simp only [bytesAt, List.length_map, List.length_range, Nat.le_refl])
  rw [out, ← Proof.Argon2.longHash_chain] at all
  exact all

end VG.Proof.Argon2.X86_64.HPrime
end

/-! # H′: emitting the complete short or long output -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime
open VG.Proof.MdStream.X86_64 (wp_cmpi)
open VG.Spec.Blake2 (bytesAt)

theorem finishOutput_ok (v : Proof.Blake2.X86_64.Backend) (s : State) (n : Nat) (input : List Byte)
    (space : Space s n) (positive : 1 ≤ n) (count : s.gpr .r15 = BitVec.ofNat 64 n)
    (digest : (bytesAt s.mem (s.gpr .rbx + 768) 64).take (min n 64) =
      Spec.Argon2.H (min n 64) (Spec.Argon2.le32 n ++ input)) :
    WP isa (finishOutput (hash v)) s (Written s (Spec.Argon2.hPrime n input)) := by
  unfold finishOutput
  refine WP.seq (wp_cmpi fun u gu mu ru wu cf _ => WP.block_nil ?_)
  obtain ku : Keeps s u := ⟨fun r _ => congrFun gu r, ru, wu, by rw [mu]; exact Frame.refl _ _⟩
  obtain countU : u.gpr .r15 = BitVec.ofNat 64 n := (congrFun gu _).trans count
  obtain cfU : u.cf = some (decide (n < 65)) := by
    rw [cf, count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt space.bound]; rfl
  apply WP.seq
  refine WP.ite (decide (n < 65)) (by simp only [eval, cfU]) ?_ ?_
  · intro h
    obtain short : n ≤ 64 := by have := of_decide_eq_true h; omega_arith
    apply WP.block_nil
    refine (copyRemaining_ok u n (space.keeps ku) positive short countU).mono ?_
    intro t ht
    obtain result := ht.before_keeps ku
    obtain value : bytesAt u.mem (u.gpr .rbx + 768) n = Spec.Argon2.hPrime n input := by
      rw [mu, gu, ← bytesAt_take _ _ n 64 short]
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
    obtain countLong : u.gpr .r15 = BitVec.ofNat 64 (32 * (q + 1) + lastLen) := by rw [size]; exact countU
    apply WP.seq_iff.mp
    refine (longOutput_ok v q lastLen u spaceU ⟨bounds.2.1, bounds.2.2.1⟩ countLong).mono ?_
    intro t ht
    obtain result := ht.before_keeps ku
    obtain digestU : bytesAt u.mem (u.gpr .rbx + 768) 64 =
        Spec.Argon2.H 64 (Spec.Argon2.le32 n ++ input) := by
      rw [mu, gu]
      simpa only [Nat.min_eq_right (show 64 ≤ n by omega_arith), bytesAt_take _ _ 64 64 (by decide)] using digest
    obtain value : Spec.Argon2.longHash lastLen (q + 1) (bytesAt u.mem (u.gpr .rbx + 768) 64) =
        Spec.Argon2.hPrime n input := by
      rw [digestU, ← hq, Spec.Argon2.hPrime, ite_eq_right (show ¬ n ≤ 64 by omega_arith)]
    rw [value] at result
    exact result

end VG.Proof.Argon2.X86_64.HPrime
end

/-! # H′: functional correctness of the complete x86-64 program -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime
open VG.Spec.Blake2 (bytesAt)

theorem code_wp (v : Proof.Blake2.X86_64.Backend) (s : State) (pre : localContract.pre s) :
    WP isa (code (hash v)) s fun t => localContract.post s t ∧
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧
      Frame [outputR s, workR s, stackR s] s.mem t.mem := by
  obtain ⟨rd, wr, len, lo, hi, dw, ow, sd, so, sw, _, _⟩ := pre
  obtain work : (workR s) ∈ s.wr := by rw [wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  unfold code
  refine WP.seq ((setup_ok s work).mono ?_)
  intro a ha
  obtain sp : a.gpr .rsp = s.gpr .rsp := ha.other _ (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain workA : (⟨a.gpr .rbx, 16384⟩ : Region) ∈ a.wr := by
    rw [ha.workspace, ha.wr]; exact work
  obtain dataA : Covers [⟨a.gpr .r12, (a.gpr .r13).toNat⟩] (a.rd ++ a.wr) := by
    rw [ha.input, ha.length, ha.rd, rd]
    intro p n ⟨r, hr, hc⟩
    exact ⟨r, List.mem_append_left _ hr, hc⟩
  obtain dwA : (⟨a.gpr .r12, (a.gpr .r13).toNat⟩ : Region).Disjoint ⟨a.gpr .rbx, 16384⟩ := by
    rw [ha.input, ha.length, ha.workspace]; exact dw
  obtain swA : (below (a.gpr .rsp) 16).Disjoint ⟨a.gpr .rbx, 16384⟩ := by
    rw [sp, ha.workspace]; exact sw
  obtain sdA : (below (a.gpr .rsp) 16).Disjoint ⟨a.gpr .r12, (a.gpr .r13).toNat⟩ := by
    rw [sp, ha.input, ha.length]; exact sd
  obtain inputA : bytesAt a.mem (a.gpr .r12) (a.gpr .r13).toNat =
      bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat := by
    rw [ha.input, ha.length, ha.mem]
    apply Proof.Blake2.bytesAt_congr
    intro i hi'
    apply (setupMem_frame s).bytes (R := inputR s) _ (show (s.gpr .rsi).toNat ≤ 2 ^ 64 by omega_arith) hi'
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact dw.sub_right (Offset.sub_base _ (by decide : 832 + 56 ≤ 16384))
  obtain headA : bytesAt a.mem (a.gpr .rbx + 832) 4 = Spec.Argon2.le32 (a.gpr .r15).toNat := by
    rw [ha.mem, ha.workspace, ha.remaining]; exact setupMem_prefix s
  obtain spaceA : Space a (s.gpr .rcx).toNat := by
    refine ⟨by omega_arith, workA, ?_, ?_, swA, ?_⟩
    · intro i hi'
      rw [ha.wr, ha.output, wr]
      exact ⟨outputR s, List.mem_cons_self .., Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    · rw [ha.workspace, ha.output]; exact ow.symm
    · rw [sp, ha.output]; exact so
  refine WP.seq ((first_ok v a (by rw [ha.remaining]; exact ⟨lo, hi⟩)
    (by rw [ha.length]; exact len) headA workA dataA dwA swA sdA).mono ?_)
  rintro b ⟨digestB, kb⟩
  obtain spaceB := spaceA.keeps kb
  obtain countB : b.gpr .r15 = BitVec.ofNat 64 (s.gpr .rcx).toNat := by
    rw [kb.regs _ (by decide), ha.remaining, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain digestB' : (bytesAt b.mem (b.gpr .rbx + 768) 64).take (min (s.gpr .rcx).toNat 64) =
      Spec.Argon2.H (min (s.gpr .rcx).toNat 64)
        (Spec.Argon2.le32 (s.gpr .rcx).toNat ++ bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) := by
    rw [kb.rbx]
    simpa only [ha.remaining, inputA] using digestB
  refine WP.seq ((finishOutput_ok v b (s.gpr .rcx).toNat
    (bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) spaceB lo countB digestB').mono ?_)
  intro x hx
  obtain baseB : b.gpr .rbx = s.gpr .r8 := kb.rbx.trans ha.workspace
  obtain spB : b.gpr .rsp = s.gpr .rsp := kb.rsp.trans sp
  obtain dstB : b.gpr .r14 = s.gpr .rdx := (kb.regs _ (by decide)).trans ha.output
  obtain wrX : x.wr = s.wr := hx.wr.trans (kb.wr.trans ha.wr)
  obtain frame : Frame [⟨s.gpr .r8, 832⟩, stackR s, outputR s] a.mem x.mem := by
    obtain fb : Frame [⟨s.gpr .r8, 832⟩, stackR s, outputR s] a.mem b.mem := by
      apply kb.frame.sub
      intro r hr
      rw [ha.workspace, sp] at hr
      exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    exact fb.trans (by simpa only [baseB, spB, dstB, stackR, outputR, Proof.Argon2.hPrime_length] using hx.frame)
  obtain values : ∀ r d, (r, d) ∈ saved →
      x.mem.readW (s.gpr .r8 + BitVec.ofNat 64 d) 64 = s.gpr r := by
    intro r d hr
    obtain bounds : ∀ rd ∈ saved, 832 ≤ rd.2 ∧ rd.2 + 8 ≤ 16384 := by decide
    obtain ⟨dlo, dhi⟩ := bounds (r, d) hr
    obtain keep : x.mem.readW (s.gpr .r8 + BitVec.ofNat 64 d) 64 =
        a.mem.readW (s.gpr .r8 + BitVec.ofNat 64 d) 64 := by
      apply frame.readW (r := ⟨s.gpr .r8 + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact (Offset.base_disjoint _ dlo (by omega_arith)).symm
      · exact (sw.sub_right (Offset.sub_base _ dhi)).symm
      · exact (ow.sub_right (Offset.sub_base _ dhi)).symm
    rw [keep, ha.mem]; exact setupMem_saved s r d hr
  obtain baseX := hx.rbx.trans baseB
  obtain spX := hx.rsp.trans spB
  obtain readable : workR s ∈ x.rd ++ x.wr := List.mem_append_right _ (wrX.symm ▸ work)
  refine (restore_ok s x baseX spX readable values).mono ?_
  rintro t ⟨regs, mem, _, _⟩
  refine ⟨?_, regs, ?_⟩
  · change bytesAt t.mem (s.gpr .rdx) (s.gpr .rcx).toNat = _
    rw [mem]
    simpa only [dstB, Proof.Argon2.hPrime_length] using hx.bytes
  · rw [mem]
    obtain setupFrame : Frame [outputR s, workR s, stackR s] s.mem a.mem := by
      rw [ha.mem]
      apply (setupMem_frame s).sub
      intro r hr
      simp only [List.mem_singleton] at hr; subst r
      exact ⟨workR s, List.mem_cons_of_mem _ (List.mem_cons_self ..),
        Offset.sub_base _ (by decide : 832 + 56 ≤ 16384)⟩
    apply setupFrame.trans
    apply frame.sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨workR s, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.sub_prefix (by decide)⟩
    · exact ⟨stackR s, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), fun _ h => h⟩
    · exact ⟨outputR s, List.mem_cons_self .., fun _ h => h⟩

theorem code_mxcsr (v : Proof.Blake2.X86_64.Backend) :
    (code (hash v)).allInstrs (fun i => !loadsMxcsr i) = true := by
  obtain init : (hash v).init.allInstrs (fun i => !loadsMxcsr i) = true := by
    change (Impl.Blake2.X86_64.Stream.init Spec.Blake2.b).allInstrs _ = true
    lit_decide
  have update : (hash v).update.allInstrs (fun i => !loadsMxcsr i) = true := v.updateMxcsr
  have finalize : (hash v).finalize.allInstrs (fun i => !loadsMxcsr i) = true := v.finalizeMxcsr
  simp only [code, setup, saved, first, chooseLength, Impl.Argon2.X86_64.HPrime.init,
    initArgs, absorbFixed, fixedArgs, Impl.Argon2.X86_64.HPrime.update, updateArgs,
    absorbInput, inputArgs, finishInput, Impl.Argon2.X86_64.HPrime.finalize, finalizeArgs,
    finishOutput, extendDigest, emitPrefix, copy, copyByte, chain, next, copyRemaining,
    restore, Code.allInstrs]
  rw [init, update, finalize]
  decide +kernel

theorem code_correct (v : Proof.Blake2.X86_64.Backend) (s : State) (pre : localContract.pre s) :
    ∃ tr t, Exec isa (code (hash v)) s tr t ∧ abiPreserved s t ∧ localContract.post s t := by
  obtain ⟨tr, t, run, post, regs, frame⟩ := code_wp v s pre
  refine ⟨tr, t, run, abiPreserved_of_exec (code_mxcsr v) run ⟨regs, ?_⟩, post⟩
  apply frame.readW (r := retR s) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  obtain ⟨_, _, _, _, _, _, _, _, _, _, retOut, retWork⟩ := pre
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact retOut
  · exact retWork
  · exact Offset.base_disjoint_below _ (by decide)

end VG.Proof.Argon2.X86_64.HPrime
