module

public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.Framework.AArch64.RelCT -- shake: keep (pairs with its `public meta import` for `taint_decide`)
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd -- shake: keep (brun's simp set reads its lemmas)
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract
public meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeFrameCTState
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Workspace
import VerifiedGarbage.Proof.Bignum.CrtExp
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeFrameCTState
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Workspace
meta import VerifiedGarbage.Proof.Bignum.CrtExp
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeBytesCT
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeBytesCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Dsa.AArch64.ProbablePrime.Params
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.EntryAllocated
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Kernel
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PublicKernel
public import VerifiedGarbage.Impl.Dsa.AArch64.ProbablePrime
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.AArch64.StackStore
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeTrial
public import VerifiedGarbage.Impl.Dsa.Generation.Layout
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeBytes
import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Arguments
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeArguments
meta import VerifiedGarbage.Proof.Dsa.AArch64.ProbablePrime.Params
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.EntryAllocated
meta import VerifiedGarbage.Proof.MillerRabin.AArch64.Kernel
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PublicKernel
meta import VerifiedGarbage.Impl.Dsa.AArch64.ProbablePrime
meta import VerifiedGarbage.Proof.MlKem.AArch64.Wp
meta import VerifiedGarbage.Proof.Bignum.Words
meta import VerifiedGarbage.Proof.Bignum.AArch64.Run
meta import VerifiedGarbage.Proof.Framework.AArch64.StackStore
meta import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeTrial
meta import VerifiedGarbage.Impl.Dsa.Generation.Layout
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeBytes
meta import VerifiedGarbage.Proof.Dsa.BitLengthBounds
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Arguments
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeArguments

/-! ### `Dsa.AArch64.ProbablePrime.Body`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.ProbablePrime.Entry`, which only this module used -/

section

/-! # The probable-prime test's arguments in the generation's frame slots -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.ProbablePrime
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64.ProbablePrime VG.Impl.Dsa.Generation.Layout
open VG.Impl.Bignum.AArch64 (movi)

/-- The memory after the entry's stores. -/
def entryMem (s : State) (F : Addr) : Mem :=
  ((((s.mem.writeW (off F 40) (s.gpr .x0)).writeW (off F 112) (s.gpr .x2)).writeW (off F 120) (s.gpr .x3)).writeW
    (off F usedSlot) (s.gpr .x4)).writeW (off F 128) (0 : BitVec 64)

theorem entryMem_word (s : State) (F : Addr) :
    word (entryMem s F) F 40 = s.gpr .x0 ∧ word (entryMem s F) F 112 = s.gpr .x2 ∧
      word (entryMem s F) F 120 = s.gpr .x3 ∧ word (entryMem s F) F usedSlot = s.gpr .x4 ∧
      word (entryMem s F) F 128 = 0 := by
  unfold entryMem usedSlot
  have o (m : Mem) {d : Nat} (v : BitVec 64) (e : Nat) (he : e + 8 ≤ d ∨ d + 8 ≤ e) (hd : d + 8 ≤ 272) (he' : e + 8 ≤ 272) :
      word (m.writeW (off F d) v) F e = word m F e :=
    (writeW_outside m F v (by omega_using [hd])).word (by omega_using [he]) (by omega_using [he'])
  refine ⟨?_, ?_, ?_, ?_, word_writeW_self _ _ _ _⟩
  · rw [o _ _ 40 (by decide) (by decide) (by decide), o _ _ 40 (by decide) (by decide) (by decide),
      o _ _ 40 (by decide) (by decide) (by decide), o _ _ 40 (by decide) (by decide) (by decide),
      word_writeW_self]
  · rw [o _ _ 112 (by decide) (by decide) (by decide), o _ _ 112 (by decide) (by decide) (by decide),
      o _ _ 112 (by decide) (by decide) (by decide), word_writeW_self]
  · rw [o _ _ 120 (by decide) (by decide) (by decide), o _ _ 120 (by decide) (by decide) (by decide),
      word_writeW_self]
  · rw [o _ _ 136 (by decide) (by decide) (by decide), word_writeW_self]

theorem entry_ok {s : State} {F : Addr} (hsp : s.sp = F)
    (hw : ∀ d, d + 8 ≤ 272 → InRegions s.wr (off F d) 8) :
    WP isa (.block entry) s fun t =>
      t.mem = entryMem s F ∧ t.gpr .x0 = off (s.gpr .x0) arithmetic ∧ Keep [.x0, .x3] s t := by
  obtain hr40 : InRegions (s.rd ++ s.wr) (off F 40) 8 := by
    obtain ⟨r, hr, hc⟩ := hw 40 (by decide); exact ⟨r, List.mem_append_right _ hr, hc⟩
  obtain h40 := (entryMem_word s F).1
  obtain run : WP isa (.block entry) s fun t => t.mem = entryMem s F ∧ t.gpr .x0 = off (s.gpr .x0) arithmetic := by
    rw [show entry = [.strSp .x0 40, .strSp .x2 112, .strSp .x3 120, .strSp .x4 usedSlot, movi .x3 0] ++
      ([.strSp .x3 128, .ldrSp .x0 40, movi .x3 arithmetic, .add .x .x0 .x0 .x3] : List Instr) from rfl]
    apply WP.block_append
    obtain run1 : WP isa (.block [.strSp .x0 40, .strSp .x2 112, .strSp .x3 120, .strSp .x4 usedSlot, movi .x3 0]) s
        fun u => u.mem = (((s.mem.writeW (off F 40) (s.gpr .x0)).writeW (off F 112) (s.gpr .x2)).writeW
          (off F 120) (s.gpr .x3)).writeW (off F usedSlot) (s.gpr .x4) ∧ u.gpr .x3 = 0 ∧ u.gpr .x0 = s.gpr .x0 ∧
          u.sp = F ∧ u.rd = s.rd ∧ u.wr = s.wr := by
      unfold usedSlot
      brun [exec_storeSp (by decide : 40 % 8 = 0 ∧ 40 < 32768), exec_storeSp (by decide : 112 % 8 = 0 ∧ 112 < 32768),
        exec_storeSp (by decide : 120 % 8 = 0 ∧ 120 < 32768), exec_storeSp (by decide : 136 % 8 = 0 ∧ 136 < 32768),
        hsp, hw 40 (by decide), hw 112 (by decide), hw 120 (by decide), hw 136 (by decide), off]
      done
    refine WP.mono run1 fun u ⟨hm, h3, h0, hspu, hrd, hwr⟩ => ?_
    obtain hw128 : InRegions u.wr (off F 128) 8 := by rw [hwr]; exact hw 128 (by decide)
    obtain hr40' : InRegions (u.rd ++ u.wr) (off F 40) 8 := by rw [hrd, hwr]; exact hr40
    obtain hread : (u.mem.writeW (off F 128) (0 : BitVec 64)).readW (off F 40) 64 = s.gpr .x0 := by
      have := h40; unfold entryMem at this; rw [← hm] at this; exact this
    brun [exec_storeSp (by decide : 128 % 8 = 0 ∧ 128 < 32768), exec_ldrSp (by decide : 40 % 8 = 0 ∧ 40 < 32768),
      hspu, hw128, hr40', h3, off, entryMem, hm]
    rw [show BitVec.setWidth 64 (BitVec.ofNat 16 arithmetic) = BitVec.ofNat 64 arithmetic by decide]
    exact congrArg (· + BitVec.ofNat 64 arithmetic) (by simpa only [hm, off] using hread)
  exact WP.mono (WP.keep [.x0, .x3] run (by decide)) fun t ⟨⟨hm, hx⟩, k⟩ => ⟨hm, hx, k⟩

end VG.Proof.Dsa.AArch64.ProbablePrime

end

end

/-! ### `Dsa.AArch64.Generation.PrimeFootprint`, which only this module used -/

section

/-! Bound every write of the complete native candidate-primality call. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Ffdh.AArch64.ParameterCandidate VG.Proof.MillerRabin VG.Proof.MillerRabin.AArch64

theorem primeRanges_bound {w : Nat} (hw : w ≤ 48) :
    ∀ r ∈ primeRanges w, r.1 + r.2 ≤ VG.Impl.Dsa.Generation.Layout.arithmeticBytes := by
  simp only [primeRanges, primeTrialRanges, modulusRanges, mpRanges, mpTail,
    drawRoundRanges, sampleRoundRanges, testRanges, witnessRoundRanges, witnessMontRanges, Caller.callRanges,
    mutRanges, Proof.MillerRabin.Round.compact, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Caller.pad, slot, hdrBytes, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes,
    aX, aTab, aAcc, aTmp, aY, aXm, aOne, aR2, aR1, aRm1, aE,
    kElen, kP, kUsed, kI, kUni, kStat, kU, sMinv, sCnt, sFn,
    VG.Impl.Dsa.Generation.Layout.arithmeticBytes]
  and_intros <;> omega_arith

theorem checkPrimeRanges_bound {w : Nat} (hw : w ≤ 48) :
    ∀ r ∈ workspaceRanges ++ (128, 128) :: (slot w 0, 8 * (w + 2)) :: primeRanges w,
      r.1 + r.2 ≤ VG.Impl.Dsa.Generation.Layout.arithmeticBytes := by
  intro r hr
  simp only [workspaceRanges, List.cons_append, List.nil_append, List.mem_cons] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | hr
  · decide
  · decide
  · decide
  · decide
  · simp only [slot, hdrBytes, VG.Impl.Dsa.Generation.Layout.arithmeticBytes]; omega_using [hw]
  · exact primeRanges_bound hw r hr

theorem prime_global_frame {B : Addr} {rs : List (Nat × Nat)} {extra : List Region} {m m' : Mem}
    (hf : WorkFrame B rs extra m m')
    (hb : ∀ r ∈ rs, r.1 + r.2 ≤ VG.Impl.Dsa.Generation.Layout.arithmeticBytes) :
    Frame (⟨B, VG.Impl.Dsa.Generation.Layout.arithmeticBytes⟩ :: extra) m m' := by
  intro a ha
  apply hf a (fun r hr => ha r (List.mem_cons_of_mem _ hr))
  intro r hr
  right
  obtain h := ha ⟨B, VG.Impl.Dsa.Generation.Layout.arithmeticBytes⟩ (by simp)
  change ¬ ofs B a < VG.Impl.Dsa.Generation.Layout.arithmeticBytes at h
  exact Nat.le_trans (hb r hr) (Nat.le_of_not_gt h)

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # The probable-prime test's body, between its frame's push and pop

The entry stores the arguments in the generation's frame slots, the test is
the generation's own, and the exit writes `used` and the status. -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/ProbablePrime/Exit.lean`, which only this module imported.
section

/-! # The probable-prime test's octets read and status, as the function returns them -/

section
namespace VG.Proof.Dsa.AArch64.ProbablePrime
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64.ProbablePrime VG.Impl.RsaKeyGen.AArch64.Candidate

theorem exit_ok {u : State} {B F U used st : Addr} (hx0 : u.gpr .x0 = B) (hsp : u.sp = F)
    (hrU : InRegions (u.rd ++ u.wr) (off B (8 * kUsed)) 8) (hrS : InRegions (u.rd ++ u.wr) (off B (8 * kStat)) 8)
    (hrF : InRegions (u.rd ++ u.wr) (off F usedSlot) 8) (hwU : InRegions u.wr U 8)
    (hU : word u.mem F usedSlot = U) (hused : word u.mem B (8 * kUsed) = used)
    (hst : word u.mem B (8 * kStat) = st) (hsep : Mem.Sep (off B (8 * kStat)) 8 U 8) :
    WP isa (.block exit) u fun t =>
      t.mem = u.mem.writeW U used ∧ t.gpr .x0 = st - (st >>> 1) ∧ Keep [.x0, .x3, .x4] u t := by
  obtain hread : (u.mem.writeW U used).readW (off B (8 * kStat)) 64 = st := by
    rw [Mem.readW_writeW_sep hsep (by decide)]; exact hst
  obtain run : WP isa (.block exit) u fun t => t.mem = u.mem.writeW U used ∧ t.gpr .x0 = st - (st >>> 1) := by
    unfold exit usedSlot at *
    simp only [word, off, kUsed, kStat, VG.Impl.Bignum.sFn] at hrU hrS hrF hU hused hst hread
    rw [← hx0] at hrU hrS hused hst hread
    rw [← hsp] at hrF hU
    brun [State.write, exec_ldrSp (by decide : 136 % 8 = 0 ∧ 136 < 32768), hrU, hrS, hrF, hwU, hused, hread, hU, kUsed, kStat, BitVec.add_zero,
      VG.Impl.Bignum.sFn]
    done
  exact WP.mono (WP.keep [.x0, .x3, .x4] run (by decide)) fun t ⟨⟨hm, hx⟩, k⟩ => ⟨hm, hx, k⟩

end VG.Proof.Dsa.AArch64.ProbablePrime
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/PrimeFromFrame.lean`, which only this module imported.
section

/-! # A complete native candidate test using retained generation arguments -/

section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64.Generation VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.MillerRabin.AArch64 VG.Impl.Bignum.AArch64

/-- Candidate setup, padded loading, trial division and the shared RSA
Miller–Rabin loop implement the exact DSA probable-prime operation. -/
theorem primeFromFrame_ok (M : Mont) (K : VG.Proof.Dsa.AArch64.Generation.PublicKernel) {P : PrimeParams} {s : State} 
    {used candidate : Nat} {W : Nat → BitVec 64} {bs : List Byte}
    (hg : VG.Proof.Rsa.AArch64.Ws s P.B P.Z P.w) (hc : candidate < 2 ^ 16) (hk : P.checks < 2 ^ 16)
    {F : Addr} (hsp : s.sp = F)
    (hr : ∀ k < 34, InRegions (s.rd ++ s.wr) (off F (8 * k)) 8)
    (hwords : ∀ k < 34, word s.mem F (8 * k) = W k)
    (hsep : ∀ k < 34, ∀ j < 32, Mem.Sep (off F (8 * k)) 8 (off P.B (8 * j)) 8)
    (hwp : W 5 + BitVec.ofNat 64 VG.Impl.Dsa.Generation.Layout.witness = P.p)
    (hwr : W 14 = P.rp) (hwl : W 15 = BitVec.ofNat 64 P.rand.length)
    (hwu : W 16 = BitVec.ofNat 64 used)
    (htape : Src s P.B P.Z P.rp P.rand) (hout : ∀ i < P.len, InRegions s.wr (off P.p i) 1)
    (hlen : bs.length = P.len) (hvalue : Spec.Rsa.os2ip bs = P.N)
    (hsrc : Src s P.B P.Z (W 5 + BitVec.ofNat 64 candidate) bs)
    (hu : used ≤ P.rand.length) (hw : P.w ≤ 48) (hz : slot P.w aTab + 2048 ≤ P.Z)
    (hn : 8161 < P.N) (hpolicy : 1024 < Spec.Dsa.bitLength P.N ↔ 16 < P.w)
    (hchecks : P.checks = Spec.Dsa.primeChecks (Spec.Dsa.bitLength P.N)) :
    WP isa (primeFromFrame M.mm K.run candidate P.len P.drawBytes P.checks) s fun t =>
      let res := Spec.Dsa.probablePrime P.N (P.rand.drop used)
      ∃ used', PrimeInput P used' t ∧ used' ≤ P.rand.length ∧
        (res = none → word t.mem P.B (8 * kStat) = BitVec.ofNat 64 0) ∧
        (∀ b rest, res = some (b, rest) →
          word t.mem P.B (8 * kStat) = BitVec.ofNat 64 (if b then 1 else 3) ∧
          used' = P.rand.length - rest.length) ∧
        WorkFrame P.B ((128, 128) :: (slot P.w 0, 8 * (P.w + 2)) :: primeRanges P.w)
          (primeExtras P) s.mem t.mem ∧ Keep mmRegs s t := by
  unfold primeFromFrame
  refine WP.seq (WP.mono (primeArguments_ok hg hc hk hsp hr hwords hsep hwp hwr hwl hwu htape hout)
    fun u ⟨hi, hptr, hf, ku⟩ => ?_)
  obtain src : Src u P.B P.Z (W 5 + BitVec.ofNat 64 candidate) bs :=
    hsrc.congrK (fun a ha => hf a (Or.inr (Nat.le_trans hg.h256 ha))) ku
  refine WP.mono (primeBytes_ok M K hi hptr hlen hvalue src hu hw hz hn hpolicy hchecks)
    fun t ⟨used', ht, hut, he, hb, ft, kt⟩ => ?_
  obtain ff : Frm P.B [(128, 128)] s.mem u.mem := Frm.of_outside hf (by simp)
  exact ⟨used', ht, hut, he, hb,
    (ff.work.mono (by simp)).trans (ft.mono (fun _ hr => List.mem_cons_of_mem _ hr)),
    (ku.trans kt).mono (by decide)⟩

end VG.Proof.Dsa.AArch64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/CheckPrime.lean`, which only this module imported.
section

/-! # The native primality operation starts with arbitrary scratch contents -/

section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64.Generation VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.MillerRabin.AArch64 VG.Impl.Bignum.AArch64

theorem checkPrime_ok (M : Mont) (K : VG.Proof.Dsa.AArch64.Generation.PublicKernel) {P : PrimeParams} {s : State}
    {used candidate : Nat} {W : Nat → BitVec 64} {bs : List Byte}
    (hS : Scr s P.B P.Z) (hdi : s.gpr .x0 = P.B)
    (hc : candidate < 2 ^ 16) (hk : P.checks < 2 ^ 16) {F : Addr} (hsp : s.sp = F)
    (hr : ∀ k < 34, InRegions (s.rd ++ s.wr) (off F (8 * k)) 8)
    (hwords : ∀ k < 34, word s.mem F (8 * k) = W k)
    (hsep : ∀ k < 34, ∀ j < 32, Mem.Sep (off F (8 * k)) 8 (off P.B (8 * j)) 8)
    (hframe : ∀ k < 34, ∀ i < 8, P.Z ≤ ofs P.B (off (off F (8 * k)) i))
    (hwp : W 5 + BitVec.ofNat 64 VG.Impl.Dsa.Generation.Layout.witness = P.p)
    (hwr : W 14 = P.rp) (hwl : W 15 = BitVec.ofNat 64 P.rand.length)
    (hwu : W 16 = BitVec.ofNat 64 used)
    (htape : Src s P.B P.Z P.rp P.rand) (hout : ∀ i < P.len, InRegions s.wr (off P.p i) 1)
    (hlen : bs.length = P.len) (hvalue : Spec.Rsa.os2ip bs = P.N)
    (hsrc : Src s P.B P.Z (W 5 + BitVec.ofNat 64 candidate) bs)
    (hu : used ≤ P.rand.length) (hw : P.w ≤ 48) (hz : slot P.w aTab + 2048 ≤ P.Z)
    (hn : 8161 < P.N) (hpolicy : 1024 < Spec.Dsa.bitLength P.N ↔ 16 < P.w)
    (hchecks : P.checks = Spec.Dsa.primeChecks (Spec.Dsa.bitLength P.N)) :
    WP isa (checkPrime M.mm K.run P.w candidate P.len P.drawBytes P.checks) s fun t =>
      let res := Spec.Dsa.probablePrime P.N (P.rand.drop used)
      ∃ used', PrimeInput P used' t ∧ used' ≤ P.rand.length ∧
        (res = none → word t.mem P.B (8 * kStat) = BitVec.ofNat 64 0) ∧
        (∀ b rest, res = some (b, rest) →
          word t.mem P.B (8 * kStat) = BitVec.ofNat 64 (if b then 1 else 3) ∧
          used' = P.rand.length - rest.length) ∧
        WorkFrame P.B (workspaceRanges ++ (128, 128) ::
          (slot P.w 0, 8 * (P.w + 2)) :: primeRanges P.w) (primeExtras P) s.mem t.mem ∧
        Keep mmRegs s t := by
  unfold checkPrime
  obtain hz16 : slot P.w 16 ≤ P.Z := Nat.le_trans (Nat.add_le_add_left
    (Nat.mul_le_mul_right (8 * (P.w + 2)) (by decide : 16 ≤ 28)) 256) P.room
  refine WP.seq (WP.mono (workspace_ok hS hdi hz16 (by have := P.w4; omega) hw)
    fun u ⟨hg, _, hf, ku⟩ => ?_)
  obtain hb : ∀ r ∈ workspaceRanges, r.1 + r.2 ≤ P.Z := by
    have := hg.h256
    simp only [workspaceRanges, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> simp only <;> omega
  obtain hwu' : ∀ k < 34, word u.mem F (8 * k) = W k := by
    intro k h
    rw [frame_word_of_workspace hf hb (hframe k h), hwords k h]
  obtain tape := htape.congrK (InScr.of_frm hf hb) ku
  obtain src := hsrc.congrK (InScr.of_frm hf hb) ku
  refine WP.mono (primeFromFrame_ok M K hg hc hk (ku.sp.trans hsp)
    (fun k h => by rw [ku.rd, ku.wr]; exact hr k h) hwu' hsep hwp hwr hwl hwu tape
    (fun i h => by rw [ku.wr]; exact hout i h) hlen hvalue src hu hw hz hn hpolicy hchecks)
    fun t ⟨used', ht, hut, he, hs, ft, kt⟩ => ?_
  exact ⟨used', ht, hut, he, hs,
    (hf.work.mono (fun _ h => List.mem_append_left _ h)).trans (ft.mono (fun _ h => List.mem_append_right _ h)),
    (ku.trans kt).mono (by decide)⟩

end VG.Proof.Dsa.AArch64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.AArch64.ProbablePrime
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64.ProbablePrime VG.Impl.Dsa.Generation.Layout
open VG.Impl.RsaKeyGen.AArch64.Candidate VG.Proof.MillerRabin.AArch64
open VG.Proof.Dsa.AArch64.Generation (PrimeParams PrimeInput primeExtras primeRanges allocState)
open VG.Impl.Bignum.AArch64 (seqs)

/-- The body of the function, inside its frame. -/
abbrev body (bits : Nat) (mul : Nat → Nat → Nat → Prog isa) (roundCode : List (Prog isa)) : Prog isa :=
  seqs [.block entry, test bits mul roundCode, .block exit]

/-- The frame's base. -/
abbrev frameBase (s : State) : Addr := s.sp - BitVec.ofNat 64 272

/-- The memory the test may change. -/
def changed (bits : Nat) (s : State) : List Region :=
  [⟨off (s.gpr .x0) arithmetic, arithmeticBytes⟩, ⟨off (s.gpr .x0) witness, len bits⟩,
    ⟨frameBase s, 272⟩, ⟨s.gpr .x4, 8⟩]

/-- The test's result as the function returns it. -/
def BodyPost (bits : Nat) (s t : State) : Prop :=
  let res := Spec.Dsa.probablePrime (candidateOf bits s)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
  t.gpr .x0 = BitVec.ofNat 64 (Proof.Dsa.ProbablePrime.status res) ∧
  (∀ b rest, res = some (b, rest) →
    t.mem.readW (s.gpr .x4) 64 = BitVec.ofNat 64 ((s.gpr .x3).toNat - rest.length)) ∧
  Frame (changed bits s) s.mem t.mem ∧
  (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧
  (∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64)

theorem frame_toNat {bits : Nat} {s : State} (A : PrimeABI bits s) :
    (frameBase s).toNat + 272 = s.sp.toNat := by
  have h : 272 ≤ s.sp.toNat := A.stackLower
  obtain hle : BitVec.ofNat 64 272 ≤ s.sp := by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega_using [h]
  rw [frameBase, BitVec.toNat_sub_of_le hle, BitVec.toNat_ofNat]
  omega_using [h]

theorem frame_sub (s : State) : Region.Sub ⟨frameBase s, 272⟩ (below s.sp 272) :=
  fun _ h => h

theorem frame_contains (s : State) {d n : Nat} (h : d + n ≤ 272) :
    (⟨frameBase s, 272⟩ : Region).Contains (off (frameBase s) d) n :=
  Offset.contains_base _ h (by omega_using [h])

/-- The frame's region. -/
abbrev frameRegion (s : State) : Region := ⟨frameBase s, 272⟩

/-- What the entry leaves: the test's arguments in the frame, the arithmetic
workspace in `x0`, and the memory changed only in the frame. -/
structure Prepared {bits : Nat} (hb : Supported bits) {s : State} (A : PrimeABI bits s) (u : State) : Prop where
  scr : Scr u (params hb A).B (params hb A).Z
  x0 : u.gpr .x0 = (params hb A).B
  sp : u.sp = frameBase s
  wr : u.wr = (allocState 272 s).wr
  rd : u.rd = s.rd
  frame : Frame [frameRegion s] s.mem u.mem
  keep : Keep [.x0, .x3] (allocState 272 s) u
  arena : word u.mem (frameBase s) 40 = s.gpr .x0
  tapePtr : word u.mem (frameBase s) 112 = s.gpr .x2
  tapeLength : word u.mem (frameBase s) 120 = s.gpr .x3
  usedPtr : word u.mem (frameBase s) usedSlot = s.gpr .x4
  used : word u.mem (frameBase s) 128 = 0
  tape : Src u (params hb A).B (params hb A).Z (params hb A).rp (params hb A).rand
  source : Src u (params hb A).B (params hb A).Z (off (s.gpr .x0) (candidate bits))
    (Spec.Rsa.bytesAt s.mem (off (s.gpr .x0) (candidate bits)) (len bits))

theorem prepared {bits : Nat} (hb : Supported bits) {s : State} (A : PrimeABI bits s) {u2 : State}
    (m2 : u2.mem = entryMem (allocState 272 s) (frameBase s))
    (x02 : u2.gpr .x0 = off ((allocState 272 s).gpr .x0) arithmetic) (k2 : Keep [.x0, .x3] (allocState 272 s) u2) :
    Prepared hb A u2 := by
  obtain hFn := frame_toNat A
  obtain hws : wsRegion s ∈ s.wr := by rw [A.wr]; exact List.mem_cons_self
  obtain hU : (⟨s.gpr .x4, 8⟩ : Region) ∈ s.wr := by rw [A.wr]; simp
  obtain hlen : len bits ≤ 384 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  obtain hw48 : words bits ≤ 48 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  obtain fws : ∀ {e k : Nat}, e + k ≤ domainCheck →
      Region.Disjoint ⟨frameBase s, 272⟩ ⟨off (s.gpr .x0) e, k⟩ := fun h =>
    (A.stackWs.sub_left (frame_sub s)).sub_right (ws_sub A h)
  obtain fused : Region.Disjoint ⟨frameBase s, 272⟩ ⟨s.gpr .x4, 8⟩ :=
    A.stackUsed.sub_left (frame_sub s)
  obtain frand : Region.Disjoint ⟨frameBase s, 272⟩ ⟨s.gpr .x2, (s.gpr .x3).toNat⟩ :=
    A.stackRand.sub_left (frame_sub s)
  have g0 : (allocState 272 s).gpr .x0 = s.gpr .x0 := rfl
  have g2 : (allocState 272 s).gpr .x2 = s.gpr .x2 := rfl
  have g3 : (allocState 272 s).gpr .x3 = s.gpr .x3 := rfl
  have g4 : (allocState 272 s).gpr .x4 = s.gpr .x4 := rfl
  have wr2 : u2.wr = (allocState 272 s).wr := k2.wr
  have rd2 : u2.rd = s.rd := k2.rd
  have sp2 : u2.sp = frameBase s := k2.sp
  -- The frame is all the entry and the save changed.
  obtain F02 : Frame [⟨frameBase s, 272⟩] s.mem u2.mem := by
    obtain fl : Frame [⟨frameBase s, 272⟩] s.mem (allocState 272 s).mem := Frame.refl _ _
    rw [m2]
    unfold entryMem
    exact ((((fl.writeW List.mem_cons_self _ (frame_contains s (by decide))).writeW List.mem_cons_self _
      (frame_contains s (by decide))).writeW List.mem_cons_self _ (frame_contains s (by decide))).writeW
      List.mem_cons_self _ (frame_contains s (by decide))).writeW List.mem_cons_self _ (frame_contains s (by decide))
  -- Words of the frame, and the candidate's and the tape's bytes.
  obtain ew := entryMem_word (allocState 272 s) (frameBase s)
  rw [g0, g2, g3, g4] at ew
  obtain hB : Scr u2 (params hb A).B (params hb A).Z := by
    obtain h0 : Scr u2 (s.gpr .x0) ((s.gpr .x1).toNat * 8) :=
      Scr.of_mem (by rw [wr2]; exact List.mem_cons_of_mem _ hws) A.wsBound
    exact h0.sub (o := arithmetic) (n := arithmeticBytes)
      (by have := A.size; have : arithmetic + arithmeticBytes = domainCheck := rfl; omega_arith) (by decide)
  obtain D0 : Region.Disjoint ⟨frameBase s, 272⟩ ⟨(params hb A).B, (params hb A).Z⟩ :=
    fws (e := arithmetic) (k := arithmeticBytes) (by decide)
  obtain candOut : ∀ i < len bits, ¬ (⟨frameBase s, 272⟩ : Region).Contains
      (off (s.gpr .x0) (candidate bits) + BitVec.ofNat 64 i) 1 := by
    intro i hi hc
    obtain hd := fws (e := candidate bits) (k := len bits)
      (by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide)
    exact hd _ hc (contains_byte _ hi (by omega_using [hlen]))
  obtain randOut : ∀ i < (s.gpr .x3).toNat, ¬ (⟨frameBase s, 272⟩ : Region).Contains
      (s.gpr .x2 + BitVec.ofNat 64 i) 1 := by
    intro i hi hc
    exact frand _ hc (contains_byte _ hi (by have := A.randBound; omega_using []))
  obtain htape : Src u2 (params hb A).B (params hb A).Z (params hb A).rp (params hb A).rand := by
    change Src u2 (off (s.gpr .x0) arithmetic) arithmeticBytes (s.gpr .x2)
      (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
    refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
    · rw [bytesAt_length] at hi
      refine ⟨_, List.mem_append_left _ (by rw [rd2, A.rd]; exact List.mem_cons_self), ?_⟩
      exact contains_byte _ hi (by have := A.randBound; omega_using [])
    · have hi' : i < (s.gpr .x3).toNat := by rw [bytesAt_length] at hi; exact hi
      rw [F02 _ (by simpa only [List.mem_singleton, forall_eq] using randOut i hi')]
      simp only [bytesAt_eq, List.getElem_map, List.getElem_range]
    · have hi' : i < (s.gpr .x3).toNat := by rw [bytesAt_length] at hi; exact hi
      exact out_scr ((A.wsRand.symm).sub_right (ws_sub A (by decide)))
        (contains_byte _ hi' (by have := A.randBound; omega_using []))
  obtain hsrc : Src u2 (params hb A).B (params hb A).Z
      (word u2.mem (frameBase s) (8 * 5) + BitVec.ofNat 64 (candidate bits))
      (Spec.Rsa.bytesAt s.mem (off (s.gpr .x0) (candidate bits)) (len bits)) := by
    rw [show 8 * 5 = 40 from rfl, m2, ew.1]
    change Src u2 (off (s.gpr .x0) arithmetic) arithmeticBytes (off (s.gpr .x0) (candidate bits))
      (Spec.Rsa.bytesAt s.mem (off (s.gpr .x0) (candidate bits)) (len bits))
    obtain hcand : candidate bits + len bits ≤ witness := by
      rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
    refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
    · rw [bytesAt_length] at hi
      refine ⟨_, List.mem_append_right _ (by rw [wr2]; exact List.mem_cons_of_mem _ hws), ?_⟩
      rw [show off (s.gpr .x0) (candidate bits) + BitVec.ofNat 64 i = off (s.gpr .x0) (candidate bits + i) by
        simp only [off, BitVec.add_assoc, BitVec.ofNat_add]]
      exact Offset.contains_base _ (by have := A.size; have : witness ≤ domainCheck := (by decide); omega_arith)
        (by have : witness < 2 ^ 64 := (by decide); omega_using [hcand, hi, this])
    · have hi' : i < len bits := by rw [bytesAt_length] at hi; exact hi
      rw [F02 _ (by simpa only [List.mem_singleton, forall_eq] using candOut i hi')]
      simp only [bytesAt_eq, List.getElem_map, List.getElem_range]
    · have hi' : i < len bits := by rw [bytesAt_length] at hi; exact hi
      refine out_scr (r := ⟨off (s.gpr .x0) (candidate bits), len bits⟩) ?_
        (contains_byte _ hi' (by omega_using [hlen]))
      exact Offset.disjoint (s.gpr .x0) (Or.inl (by have : witness ≤ arithmetic := (by decide); omega_using [hcand, this]))
        (by have : witness < 2 ^ 64 := (by decide); omega_using [hcand, this]) (by decide)
  refine ⟨hB, x02.trans (by rw [g0]; rfl), sp2, wr2, rd2, F02, k2, by rw [m2]; exact ew.1, by rw [m2]; exact ew.2.1,
    by rw [m2]; exact ew.2.2.1, by rw [m2]; exact ew.2.2.2.1, by rw [m2]; exact ew.2.2.2.2, htape, ?_⟩
  have h := hsrc
  rw [show 8 * 5 = 40 from rfl, m2, ew.1] at h
  exact h

/-- What the test leaves. -/
structure Tested {bits : Nat} (hb : Supported bits) {s : State} (A : PrimeABI bits s) (u : State) : Prop where
  input : ∃ used', PrimeInput (params hb A) used' u ∧ used' ≤ (params hb A).rand.length ∧
    (Spec.Dsa.probablePrime (params hb A).N ((params hb A).rand.drop 0) = none →
      word u.mem (params hb A).B (8 * kStat) = BitVec.ofNat 64 0) ∧
    (∀ b rest, Spec.Dsa.probablePrime (params hb A).N ((params hb A).rand.drop 0) = some (b, rest) →
      word u.mem (params hb A).B (8 * kStat) = BitVec.ofNat 64 (if b then 1 else 3) ∧
      used' = (params hb A).rand.length - rest.length)
  sp : u.sp = frameBase s
  wr : u.wr = (allocState 272 s).wr
  rd : u.rd = s.rd
  frame : Frame [frameRegion s, ⟨(params hb A).B, arithmeticBytes⟩, ⟨(params hb A).p, len bits⟩] s.mem u.mem
  regs : ∀ r ∈ preserved, u.gpr r = s.gpr r
  vectors : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  usedPtr : word u.mem (frameBase s) usedSlot = s.gpr .x4

theorem test_ok (M : Mont) (K : VG.Proof.Dsa.AArch64.Generation.PublicKernel) {bits : Nat} (hb : Supported bits) {s : State} (A : PrimeABI bits s)
    {u2 : State} (P : Prepared hb A u2) :
    WP isa (test bits M.mm K.run) u2 (Tested hb A) := by
  obtain hFn := frame_toNat A
  obtain hws : wsRegion s ∈ s.wr := by rw [A.wr]; exact List.mem_cons_self
  obtain hU : (⟨s.gpr .x4, 8⟩ : Region) ∈ s.wr := by rw [A.wr]; simp
  obtain hlen : len bits ≤ 384 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  obtain hw48 : words bits ≤ 48 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  obtain fws : ∀ {e k : Nat}, e + k ≤ domainCheck →
      Region.Disjoint ⟨frameBase s, 272⟩ ⟨off (s.gpr .x0) e, k⟩ := fun h =>
    (A.stackWs.sub_left (frame_sub s)).sub_right (ws_sub A h)
  obtain fused : Region.Disjoint ⟨frameBase s, 272⟩ ⟨s.gpr .x4, 8⟩ :=
    A.stackUsed.sub_left (frame_sub s)
  obtain D0 : Region.Disjoint ⟨frameBase s, 272⟩ ⟨(params hb A).B, (params hb A).Z⟩ :=
    fws (e := arithmetic) (k := arithmeticBytes) (by decide)
  obtain frameOut : ∀ r ∈ [(⟨(params hb A).B, arithmeticBytes⟩ : Region), ⟨(params hb A).p, len bits⟩],
      Region.Disjoint ⟨frameBase s, 272⟩ r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact D0
    · exact fws (by have : witness + 384 ≤ domainCheck := (by decide); omega_using [hlen, this])
  obtain inFrame : ∀ {d n : Nat}, d + n ≤ 272 → ∀ r ∈ [(⟨(params hb A).B, arithmeticBytes⟩ : Region),
      ⟨(params hb A).p, len bits⟩], Region.Disjoint ⟨off (frameBase s) d, n⟩ r :=
    fun h r hr => (frameOut r hr).sub_left (Offset.sub_base _ h)
  unfold test
  obtain hlow := ((bitLength_iff_bounds (by have := hb.le; omega_using [this])).mp A.bits).1
  -- The test.
  refine WP.mono (VG.Proof.Dsa.AArch64.Generation.checkPrime_ok M K (P := params hb A) (s := u2)
    (used := 0) (candidate := candidate bits) (W := fun k => word u2.mem (frameBase s) (8 * k))
    P.scr P.x0
    (by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide)
    (by change checks bits < _; rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide)
    P.sp
    (fun k hk => ⟨_, List.mem_append_right _ (by rw [P.wr]; exact List.mem_cons_self),
      frame_contains s (by omega_using [hk])⟩)
    (fun _ _ => rfl)
    (fun k hk j hj => D0.sep (frame_contains s (by omega_using [hk]))
      (Offset.contains_base _ (by change 8 * j + 8 ≤ arithmeticBytes; unfold arithmeticBytes; omega_using [hj]) (by omega_using [hj])))
    (fun k hk i hi => by
      rw [off_off]
      exact out_scr D0 (frame_contains s (by omega_using [hk, hi])))
    (by rw [show 8 * 5 = 40 from rfl, P.arena]; rfl)
    (by rw [show 8 * 14 = 112 from rfl, P.tapePtr]; rfl)
    (by
      rw [show 8 * 15 = 120 from rfl, P.tapeLength]
      change s.gpr .x3 = BitVec.ofNat 64 (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat).length
      rw [bytesAt_length, ofNat_toNat64])
    (by rw [show 8 * 16 = 128 from rfl, P.used]; rfl)
    P.tape
    (fun i hi => by
      refine ⟨_, by rw [P.wr]; exact List.mem_cons_of_mem _ hws, ?_⟩
      change (wsRegion s).Contains (off (off (s.gpr .x0) witness) i) 1
      rw [off_off]
      exact Offset.contains_base _ (by have := A.size; have : witness + 384 ≤ domainCheck := (by decide); change i < len bits at hi; omega_arith)
        (by have : witness + 384 < 2 ^ 64 := (by decide); change i < len bits at hi; omega_using [hlen, this, hi]))
    (bytesAt_length _ _ _) rfl (by rw [show 8 * 5 = 40 from rfl, P.arena]; exact P.source) (Nat.zero_le _) hw48
    (by change Bignum.slot (words bits) aTab + 2048 ≤ arithmeticBytes
        rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide)
    (by
      change 8161 < candidateOf bits s
      obtain h2 : 2 ^ 159 ≤ 2 ^ (bits - 1) := Nat.pow_le_pow_right (by decide) (by have := hb.le; omega_using [this])
      have : (8161 : Nat) < 2 ^ 159 := by decide
      exact Nat.lt_of_lt_of_le this (Nat.le_trans h2 hlow))
    (by
      change 1024 < Spec.Dsa.bitLength (candidateOf bits s) ↔ 16 < words bits
      rw [A.bits]; rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide)
    (by
      change checks bits = Spec.Dsa.primeChecks (Spec.Dsa.bitLength (candidateOf bits s))
      rw [A.bits]; rfl)) fun u3 h3 => ?_
  obtain ⟨used', inp, hub, hnone, hsome, wf3, k3⟩ := h3
  obtain F23 : Frame [⟨(params hb A).B, arithmeticBytes⟩, ⟨(params hb A).p, len bits⟩] u2.mem u3.mem :=
    VG.Proof.Dsa.AArch64.Generation.prime_global_frame wf3
      (VG.Proof.Dsa.AArch64.Generation.checkPrimeRanges_bound hw48)
  refine ⟨⟨used', inp, hub, hnone, hsome⟩, k3.sp.trans P.sp, k3.wr.trans P.wr, k3.rd.trans P.rd,
    (P.frame.mono (by simp)).trans (F23.mono (by simp)), fun r hr => ?_, fun r hr => ?_, ?_⟩
  · have hm : r ∉ mmRegs := by revert r; decide
    obtain h3 : r ∉ [Reg.x0, .x3] := by revert r; decide
    exact (k3.gpr r hm).trans (P.keep.gpr r h3)
  · exact (k3.vcs r hr).trans (P.keep.vcs r hr)
  rw [← P.usedPtr]
  exact F23.readW (Offset.contains_base _ (d := 0) (n := 8) (k := 8) (by decide) (by decide) |> fun h => by
    simpa only [off, BitVec.add_zero] using h) (inFrame (d := usedSlot) (n := 8) (by decide)) (by decide)

theorem finish_ok {bits : Nat} (hb : Supported bits) {s : State} (A : PrimeABI bits s) {u3 : State}
    (T : Tested hb A u3) :
    WP isa (.block exit) u3 fun t =>
      t.sp = (allocState 272 s).sp ∧ t.wr = (allocState 272 s).wr ∧ t.rd = s.rd ∧ BodyPost bits s t := by
  obtain hFn := frame_toNat A
  obtain hws : wsRegion s ∈ s.wr := by rw [A.wr]; exact List.mem_cons_self
  obtain hU : (⟨s.gpr .x4, 8⟩ : Region) ∈ s.wr := by rw [A.wr]; simp
  obtain hlen : len bits ≤ 384 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  obtain hw48 : words bits ≤ 48 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  obtain fws : ∀ {e k : Nat}, e + k ≤ domainCheck →
      Region.Disjoint ⟨frameBase s, 272⟩ ⟨off (s.gpr .x0) e, k⟩ := fun h =>
    (A.stackWs.sub_left (frame_sub s)).sub_right (ws_sub A h)
  obtain fused : Region.Disjoint ⟨frameBase s, 272⟩ ⟨s.gpr .x4, 8⟩ :=
    A.stackUsed.sub_left (frame_sub s)
  obtain D0 : Region.Disjoint ⟨frameBase s, 272⟩ ⟨(params hb A).B, (params hb A).Z⟩ :=
    fws (e := arithmetic) (k := arithmeticBytes) (by decide)
  obtain frameOut : ∀ r ∈ [(⟨(params hb A).B, arithmeticBytes⟩ : Region), ⟨(params hb A).p, len bits⟩],
      Region.Disjoint ⟨frameBase s, 272⟩ r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact D0
    · exact fws (by have : witness + 384 ≤ domainCheck := (by decide); omega_using [hlen, this])
  obtain inFrame : ∀ {d n : Nat}, d + n ≤ 272 → ∀ r ∈ [(⟨(params hb A).B, arithmeticBytes⟩ : Region),
      ⟨(params hb A).p, len bits⟩], Region.Disjoint ⟨off (frameBase s) d, n⟩ r :=
    fun h r hr => (frameOut r hr).sub_left (Offset.sub_base _ h)
  obtain ⟨⟨used', inp, hub, hnone, hsome⟩, sp3, wr3, rd3, F03, g3, v3, hU3⟩ := T
  -- The exit.
  refine WP.mono (exit_ok (u := u3) (B := (params hb A).B) (F := frameBase s) (U := s.gpr .x4)
    (used := BitVec.ofNat 64 used') (st := word u3.mem (params hb A).B (8 * kStat))
    inp.ws.x0 sp3
    (inp.ws.scr.ld (d := 216) (by have := inp.ws.h256; omega_using [this]))
    (inp.ws.scr.ld (d := 248) (by have := inp.ws.h256; omega_using [this]))
    ⟨_, List.mem_append_right _ (by rw [wr3]; exact List.mem_cons_self), frame_contains s (by decide)⟩
    ⟨⟨s.gpr .x4, 8⟩, by rw [wr3]; exact List.mem_cons_of_mem _ hU, Region.contains_self _ _⟩
    hU3 inp.used rfl
    (by
      obtain h := A.wsUsed.sub_left (ws_sub A (d := arithmetic + 248) (n := 8) (by decide))
      rw [show off (s.gpr .x0) (arithmetic + 248) = off (params hb A).B (8 * kStat) by
        simp only [params, off, BitVec.add_assoc, BitVec.ofNat_add]; rfl] at h
      exact h.sep (Region.contains_self _ _) (Region.contains_self _ _))) fun u4 h4 => ?_
  obtain ⟨m4, x04, k4⟩ := h4
  obtain sp4 : u4.sp = frameBase s := k4.sp.trans sp3
  obtain wr4 : u4.wr = (allocState 272 s).wr := k4.wr.trans wr3
  obtain rd4 : u4.rd = s.rd := k4.rd.trans rd3
  -- What changed since the save: the entry's slots, the test's workspace and buffer, and `used`.
  obtain F34 : Frame [⟨s.gpr .x4, 8⟩] u3.mem u4.mem := by
    rw [m4]; exact (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
  refine ⟨sp4, wr4, rd4, ?_, ?_, ?_, fun r hr => ?_, fun r hr => (k4.vcs r hr).trans (v3 r hr)⟩
  · rw [x04]
    change word u3.mem (params hb A).B (8 * kStat) - word u3.mem (params hb A).B (8 * kStat) >>> 1 =
      BitVec.ofNat 64 (Proof.Dsa.ProbablePrime.status (Spec.Dsa.probablePrime (params hb A).N (params hb A).rand))
    rw [show Spec.Dsa.probablePrime (params hb A).N (params hb A).rand =
      Spec.Dsa.probablePrime (params hb A).N (List.drop 0 (params hb A).rand) from rfl]
    cases h : Spec.Dsa.probablePrime (params hb A).N (List.drop 0 (params hb A).rand) with
    | none => rw [hnone h]; decide
    | some r =>
      obtain ⟨b, rest⟩ := r
      rw [(hsome b rest h).1]
      cases b <;> simp only [Proof.Dsa.ProbablePrime.status] <;> decide
  · intro b rest h
    have h' : Spec.Dsa.probablePrime (params hb A).N (List.drop 0 (params hb A).rand) = some (b, rest) := h
    rw [m4, Mem.readW_writeW_self64, (hsome b rest h').2]
    change BitVec.ofNat 64 ((Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat).length - rest.length) = _
    rw [bytesAt_length]
  · rw [m4]
    obtain F34 : Frame [⟨s.gpr .x4, 8⟩] u3.mem (u3.mem.writeW (s.gpr .x4) (BitVec.ofNat 64 used')) :=
      (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
    refine (F03.mono ?_).trans (F34.mono (by simp [changed]))
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [changed, params]
  · have h4 : r ∉ [Reg.x0, .x3, .x4] := by revert r; decide
    exact (k4.gpr r h4).trans (g3 r hr)

theorem body_ok (M : Mont) (K : VG.Proof.Dsa.AArch64.Generation.PublicKernel) {bits : Nat} (hb : Supported bits) {s : State}
    (A : PrimeABI bits s) :
    WP isa (body bits M.mm K.run) (allocState 272 s) fun t =>
      t.sp = (allocState 272 s).sp ∧ t.wr = (allocState 272 s).wr ∧ t.rd = s.rd ∧
      BodyPost bits s t := by
  obtain hwF : ∀ d, d + 8 ≤ 272 → InRegions (allocState 272 s).wr (off (frameBase s) d) 8 :=
    fun d hd => ⟨_, List.mem_cons_self, frame_contains s hd⟩
  simp only [body, seqs]
  refine WP.seq (WP.mono (entry_ok (s := allocState 272 s) (F := frameBase s) rfl hwF)
    fun u2 ⟨m2, x02, k2⟩ => ?_)
  exact WP.seq (WP.mono (test_ok M K hb A (prepared hb A m2 x02 k2)) fun u3 T => finish_ok hb A T)

end VG.Proof.Dsa.AArch64.ProbablePrime

end

end

/-! ### `Dsa.AArch64.Generation.CheckPrimeCT`, which only this module used -/

section

/-! ### `Dsa.AArch64.Generation.PrimeFromFrameCT`, which only this module used -/

section

/-! ### `Dsa.AArch64.Generation.PrimalityCT`, which this module and modules that import it used -/

section

/-! # Discharge the primality timing certificates at every supported DSA width -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MillerRabin.AArch64

def PrimeWidths (len drawBytes : Nat) : Prop :=
  (len = 20 ∧ drawBytes = 24) ∨ (len = 32 ∧ drawBytes = 32) ∨
    (len = 128 ∧ drawBytes = 128) ∨ (len = 256 ∧ drawBytes = 256) ∨ (len = 384 ∧ drawBytes = 384)

theorem primeBytes_supported_ct (M : Mont) (K : VG.Proof.Dsa.AArch64.Generation.PublicKernel) {len drawBytes : Nat}
    (h : PrimeWidths len drawBytes) :
    RelCT isa (Two (PrimeBytesBefore len drawBytes))
      (Impl.Dsa.AArch64.Generation.primeBytes M.mm K.run len drawBytes) (fun _ _ => True) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals exact primeBytes_ct M K _ _ (by taint_decide) (by taint_decide)

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! The retained frame supplies the complete verified primality operation. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MillerRabin.AArch64
open VG.Impl.Dsa.AArch64.Generation

theorem primeFromFrame_ct (M : Mont) (K : VG.Proof.Dsa.AArch64.Generation.PublicKernel) (candidate len draw checks : Nat)
    (hwidth : PrimeWidths len draw) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0])
      (.block (headerArguments (primeArguments candidate len draw checks))) hc).isSome = true) :
    RelCT isa (Two (PrimeFrameBefore candidate len draw checks))
      (primeFromFrame M.mm K.run candidate len draw checks) (fun _ _ => True) := by
  unfold primeFromFrame
  refine RelCT.seq (two_post (two_taint [.x0] ?_ ht) (fun _ _ h => primeFrame_arguments h)) ?_
  · intro p s t hs ht r hr
    obtain rfl := List.mem_singleton.mp hr
    exact hs.1.good.x0.trans ht.1.good.x0.symm
  · exact two_map PrimeFramePublic.bytes (fun _ _ h => h) (primeBytes_supported_ct M K hwidth)

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.WorkspaceCTState`, which only this module used -/

section

/-! # Workspace initialization preserves the public frame arguments and input tapes -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64

theorem primeWorkspace_ready {p : PrimeFramePublic} {s : State}
    (h : PrimeFrameInputs p s)
    (hs : Scr s p.bytes.call.draw.prime.B p.bytes.call.draw.prime.Z)
    (hdi : s.gpr .x0 = p.bytes.call.draw.prime.B) :
    WP isa (Impl.Dsa.AArch64.Generation.workspace p.bytes.call.draw.prime.w) s (PrimeFrameState p) := by
  have hz := p.bytes.call.draw.prime.z256
  have hroom : slot p.bytes.call.draw.prime.w 16 ≤ p.bytes.call.draw.prime.Z :=
    Nat.le_trans (slot_mono _ (by decide)) p.bytes.call.draw.prime.room
  refine WP.mono (workspace_ok hs hdi hroom (by have := p.bytes.call.draw.prime.w4; omega_using [this])
    (by have := p.bytes.call.width; omega_using [this])) fun t ⟨hg, _, hf, hk⟩ => ?_
  have hr : ∀ r ∈ workspaceRanges, r.1 + r.2 ≤ p.bytes.call.draw.prime.Z := by
    intro r hr
    simp only [workspaceRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only <;> omega_using [hz]
  have headers (k : Nat) (hkw : k < 34) :
      VG.Proof.Bignum.word t.mem p.F (8 * k) = VG.Proof.Bignum.word s.mem p.F (8 * k) :=
    frame_word_of_workspace hf hr (p.outside k hkw)
  refine { good := hg
           stack := hk.sp.trans h.stack
           read := fun k hkw => by rw [hk.rd, hk.wr]; exact h.read k hkw
           arena := (headers 5 (by decide)).trans h.arena
           tapePtr := (headers 14 (by decide)).trans h.tapePtr
           tapeLength := (headers 15 (by decide)).trans h.tapeLength
           used := (headers 16 (by decide)).trans h.used
           tape := h.tape.congrK (InScr.of_frm hf hr) hk
           source := h.source.congrK (InScr.of_frm hf hr) hk
           writable := fun i hi => by rw [hk.wr]; exact h.writable i hi
           usedBound := h.usedBound }

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # The complete native primality call accepts uninitialized arithmetic scratch -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MillerRabin.AArch64
open VG.Impl.Dsa.AArch64.Generation

def CheckPrimeBefore (w candidate len draw checks : Nat) (p : PrimeFramePublic) (s : State) : Prop :=
  PrimeFrameInputs p s ∧ Scr s p.bytes.call.draw.prime.B p.bytes.call.draw.prime.Z ∧
    s.gpr .x0 = p.bytes.call.draw.prime.B ∧ p.bytes.call.draw.prime.w = w ∧
    p.candidate = candidate ∧ p.bytes.call.draw.prime.len = len ∧
    p.bytes.call.draw.prime.drawBytes = draw ∧ p.bytes.call.draw.prime.checks = checks

theorem checkPrime_workspace {w candidate len draw checks : Nat} {p : PrimeFramePublic} {s : State}
    (h : CheckPrimeBefore w candidate len draw checks p s) :
    WP isa (workspace w) s (PrimeFrameBefore candidate len draw checks p) := by
  have hw := primeWorkspace_ready h.1 h.2.1 h.2.2.1
  rw [h.2.2.2.1] at hw
  exact WP.mono hw fun _ ht => ⟨ht, h.2.2.2.2⟩

theorem checkPrime_ct (M : Mont) (K : VG.Proof.Dsa.AArch64.Generation.PublicKernel) (w candidate len draw checks : Nat)
    (hwidth : PrimeWidths len draw) {hc₁ hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0]) (workspace w) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.x0])
      (.block (headerArguments (primeArguments candidate len draw checks))) hc₂).isSome = true) :
    RelCT isa (Two (CheckPrimeBefore w candidate len draw checks))
      (checkPrime M.mm K.run w candidate len draw checks) (fun _ _ => True) := by
  unfold checkPrime
  refine RelCT.seq (two_post (two_taint [.x0] ?_ ht₁)
    (fun _ _ h => checkPrime_workspace h)) (primeFromFrame_ct M K candidate len draw checks hwidth ht₂)
  intro p s t hs ht r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact hs.2.2.1.trans ht.2.2.1.symm

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # The probable-prime test's timing depends only on its public inputs -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.ProbablePrime
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MillerRabin.AArch64
open VG.Impl.Dsa.AArch64.ProbablePrime VG.Impl.Dsa.Generation.Layout VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Dsa.AArch64.Generation (PrimeParams PrimeCallPublic PrimeBytesPublic PrimeFramePublic
  PrimeFrameInputs CheckPrimeBefore allocState)
open VG.Impl.Bignum.AArch64 (ldh)

/-- What the contract makes public: the arguments, the stack pointer, the
candidate and the tape. -/
structure View where
  x0 : Addr
  x1 : Addr
  x2 : Addr
  x3 : Addr
  x4 : Addr
  sp : Addr
  N : Nat
  rand : List Byte

def view (bits : Nat) (s : State) : View :=
  ⟨s.gpr .x0, s.gpr .x1, s.gpr .x2, s.gpr .x3, s.gpr .x4, s.sp, candidateOf bits s,
    Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat⟩

theorem map_toNat_inj : ∀ {l₁ l₂ : List Byte}, l₁.map (·.toNat) = l₂.map (·.toNat) → l₁ = l₂
  | [], [], _ => rfl
  | a :: l₁, b :: l₂, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, map_toNat_inj h.2]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem view_of_pub {bits : Nat} {s₁ s₂ : State} (h : (contract bits).pub s₁ s₂) :
    view bits s₁ = view bits s₂ := by
  sig_pub [contract, Proof.Dsa.ProbablePrime.contract, Proof.Dsa.ProbablePrime.sig, abi, argRegs] at h
  obtain ⟨hsp, hl, h0, h1, h2, h3, h4⟩ := h
  obtain ⟨hN, hr⟩ := List.cons.inj hl
  have hr' := map_toNat_inj hr
  unfold view candidateOf
  rw [hN, hr', hsp, h0, h1, h2, h3, h4]

/-- Big-endian octet strings of one length are equal if their values are. -/
theorem os2ip_inj : ∀ {l₁ l₂ : List Byte}, l₁.length = l₂.length →
    Spec.Rsa.os2ip l₁ = Spec.Rsa.os2ip l₂ → l₁ = l₂
  | [], [], _, _ => rfl
  | a :: l₁, b :: l₂, hl, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    rw [os2ip_cons, os2ip_cons, hl] at h
    have h₁ := os2ip_lt l₁
    have h₂ := os2ip_lt l₂
    rw [hl] at h₁
    have hd : (a.toNat * 256 ^ l₂.length + Spec.Rsa.os2ip l₁) / 256 ^ l₂.length =
        (b.toNat * 256 ^ l₂.length + Spec.Rsa.os2ip l₂) / 256 ^ l₂.length := by rw [h]
    have hm : (a.toNat * 256 ^ l₂.length + Spec.Rsa.os2ip l₁) % 256 ^ l₂.length =
        (b.toNat * 256 ^ l₂.length + Spec.Rsa.os2ip l₂) % 256 ^ l₂.length := by rw [h]
    have hp : 0 < 256 ^ l₂.length := Nat.pow_pos (by decide)
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt h₁, Nat.zero_add,
      Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt h₂, Nat.zero_add] at hd
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h₁,
      Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h₂] at hm
    rw [BitVec.eq_of_toNat_eq hd, os2ip_inj hl hm]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

theorem params_ext {P Q : PrimeParams} (hB : P.B = Q.B) (hp : P.p = Q.p) (hrp : P.rp = Q.rp)
    (hZ : P.Z = Q.Z) (hw : P.w = Q.w) (hN : P.N = Q.N) (hlen : P.len = Q.len)
    (hd : P.drawBytes = Q.drawBytes) (hc : P.checks = Q.checks) (hr : P.rand = Q.rand) : P = Q := by
  cases P; cases Q
  simp only at hB hp hrp hZ hw hN hlen hd hc hr
  subst hB hp hrp hZ hw hN hlen hd hc hr
  rfl

/-- The test's public parameters, as the generation's timing lemmas take them. -/
def callPublic {bits : Nat} (hb : Supported bits) {s : State} (A : PrimeABI bits s) : PrimeCallPublic where
  draw := ⟨params hb A, 0⟩
  arena := s.gpr .x0
  base := rfl
  width := by change words bits ≤ 48; rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  tab := by
    change Bignum.slot (words bits) aTab + 2048 ≤ arithmeticBytes
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  large := by
    change 8161 < candidateOf bits s
    have hlow := ((bitLength_iff_bounds (by have := hb.le; omega_using [this])).mp A.bits).1
    have h2 : 2 ^ 159 ≤ 2 ^ (bits - 1) := Nat.pow_le_pow_right (by decide) (by have := hb.le; omega_using [this])
    have : (8161 : Nat) < 2 ^ 159 := by decide
    exact Nat.lt_of_lt_of_le this (Nat.le_trans h2 hlow)
  policy := by
    change 1024 < Spec.Dsa.bitLength (candidateOf bits s) ↔ 16 < words bits
    rw [A.bits]; rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide

def bytesPublic {bits : Nat} (hb : Supported bits) {s : State} (A : PrimeABI bits s) : PrimeBytesPublic where
  call := callPublic hb A
  source := off (s.gpr .x0) (candidate bits)
  bytes := Spec.Rsa.bytesAt s.mem (off (s.gpr .x0) (candidate bits)) (len bits)
  length := bytesAt_length _ _ _
  value := rfl

def framePublic {bits : Nat} (hb : Supported bits) {s : State} (A : PrimeABI bits s) : PrimeFramePublic where
  bytes := bytesPublic hb A
  F := frameBase s
  candidate := candidate bits
  candidateBound := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  checksBound := by change checks bits < _; rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  checks := by
    change checks bits = Spec.Dsa.primeChecks (Spec.Dsa.bitLength (candidateOf bits s))
    rw [A.bits]; rfl
  source := rfl
  witness := rfl
  separate := by
    intro k hk j hj
    have D0 : Region.Disjoint ⟨frameBase s, 272⟩ ⟨off (s.gpr .x0) arithmetic, arithmeticBytes⟩ :=
      (A.stackWs.sub_left (frame_sub s)).sub_right (ws_sub A (by decide))
    exact D0.sep (frame_contains s (by omega_using [hk]))
      (Offset.contains_base _ (by change 8 * j + 8 ≤ arithmeticBytes; unfold arithmeticBytes; omega_using [hj]) (by omega_using [hj]))
  outside := by
    intro k hk i hi
    have D0 : Region.Disjoint ⟨frameBase s, 272⟩ ⟨off (s.gpr .x0) arithmetic, arithmeticBytes⟩ :=
      (A.stackWs.sub_left (frame_sub s)).sub_right (ws_sub A (by decide))
    rw [off_off]
    exact out_scr D0 (frame_contains s (by omega_using [hk, hi]))

theorem framePublic_eq {bits : Nat} (hb : Supported bits) {s₁ s₂ : State} (A₁ : PrimeABI bits s₁)
    (A₂ : PrimeABI bits s₂) (hv : view bits s₁ = view bits s₂) : framePublic hb A₁ = framePublic hb A₂ := by
  simp only [view, View.mk.injEq] at hv
  obtain ⟨h0, -, h2, -, -, hsp, hN, hr⟩ := hv
  have hP : params hb A₁ = params hb A₂ :=
    params_ext (by simp only [params, h0]) (by simp only [params, h0]) h2 rfl rfl hN rfl rfl rfl hr
  have hbytes : Spec.Rsa.bytesAt s₁.mem (off (s₁.gpr .x0) (candidate bits)) (len bits) =
      Spec.Rsa.bytesAt s₂.mem (off (s₂.gpr .x0) (candidate bits)) (len bits) :=
    os2ip_inj (by rw [bytesAt_length, bytesAt_length]) hN
  rw [h0] at hbytes
  have hF : frameBase s₁ = frameBase s₂ := by simp only [frameBase, hsp]
  unfold framePublic bytesPublic callPublic
  simp only [hP, hbytes, h0, hF]

theorem before_of_prepared {bits : Nat} (hb : Supported bits) {s : State} (A : PrimeABI bits s) {u : State}
    (P : Prepared hb A u) :
    CheckPrimeBefore (words bits) (candidate bits) (len bits) (draw bits) (checks bits) (framePublic hb A) u := by
  have hws : wsRegion s ∈ s.wr := by rw [A.wr]; exact List.mem_cons_self
  have hlen : len bits ≤ 384 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  refine ⟨⟨P.sp, fun k hk => ⟨_, List.mem_append_right _ (by rw [P.wr]; exact List.mem_cons_self),
      frame_contains s (by omega_using [hk])⟩, P.arena, P.tapePtr, ?_,
      by change word u.mem (frameBase s) 128 = BitVec.ofNat 64 0; rw [P.used]; rfl, P.tape, P.source,
      fun i hi => ?_, Nat.zero_le _⟩, P.scr, P.x0, rfl, rfl, rfl, rfl, rfl⟩
  · change word u.mem (frameBase s) 120 =
      BitVec.ofNat 64 (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat).length
    rw [P.tapeLength]
    rw [bytesAt_length, ofNat_toNat64]
  · refine ⟨_, by rw [P.wr]; exact List.mem_cons_of_mem _ hws, ?_⟩
    change (wsRegion s).Contains (off (off (s.gpr .x0) witness) i) 1
    change i < len bits at hi
    rw [off_off]
    exact Offset.contains_base _ (by have := A.size; have : witness + 384 ≤ domainCheck := (by decide); omega_arith)
      (by have : witness + 384 < 2 ^ 64 := (by decide); omega_using [hlen, hi, this])

/-! ## The stages, each with the public view of the arguments -/

def Entered (bits : Nat) (v : View) (u : State) : Prop :=
  ∃ s, ∃ _ : PrimeABI bits s, view bits s = v ∧ u = allocState 272 s

def PreparedAt {bits : Nat} (hb : Supported bits) (v : View) (u : State) : Prop :=
  ∃ s, ∃ A : PrimeABI bits s, view bits s = v ∧ Prepared hb A u

def TestedAt {bits : Nat} (hb : Supported bits) (v : View) (u : State) : Prop :=
  ∃ s, ∃ A : PrimeABI bits s, view bits s = v ∧ Tested hb A u

/-- The workspace and `used` in their registers. -/
def Loaded (v : View) (u : State) : Prop :=
  u.gpr .x0 = off v.x0 arithmetic ∧ u.gpr .x4 = v.x4

theorem post_of_exec {c : Prog isa} {s t : State} {trace : List Leak} {Q : State → Prop}
    (h : WP isa c s Q) (he : Exec isa c s trace t) : Q t := by
  obtain ⟨_, u, hu, hq⟩ := h
  obtain ⟨_, heq⟩ := Exec.det he hu
  rw [heq]
  exact hq

theorem entry_ct {bits : Nat} (hb : Supported bits) :
    RelCT isa (Two (Entered bits)) (.block entry) (Two (PreparedAt hb)) :=
  two_piece [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide) fun v u ⟨s, A, hv, hu⟩ => by
    subst hu
    exact WP.mono (entry_ok (s := allocState 272 s) (F := frameBase s) rfl
      (fun d hd => ⟨_, List.mem_cons_self, frame_contains s hd⟩))
      fun t ⟨m, x, k⟩ => ⟨s, A, hv, prepared hb A m x k⟩

theorem test_ct (M : Mont) (K : VG.Proof.Dsa.AArch64.Generation.PublicKernel) {bits : Nat} (hb : Supported bits) :
    RelCT isa (Two (PreparedAt hb)) (test bits M.mm K.run) (Two (TestedAt hb)) := by
  have hct : RelCT isa (Two (CheckPrimeBefore (words bits) (candidate bits) (len bits) (draw bits) (checks bits)))
      (test bits M.mm K.run) fun _ _ => True := by
    unfold test
    rcases hb with rfl | rfl | rfl | rfl | rfl <;>
      exact VG.Proof.Dsa.AArch64.Generation.checkPrime_ct M K _ _ _ _ _
        (by unfold VG.Proof.Dsa.AArch64.Generation.PrimeWidths; decide +kernel) (by taint_decide) (by taint_decide)
  intro u₁ u₂ t₁ t₂ u₁' u₂' ⟨v, ⟨s₁, A₁, hv₁, P₁⟩, ⟨s₂, A₂, hv₂, P₂⟩, hsp⟩ e₁ e₂
  have hp₂ : CheckPrimeBefore (words bits) (candidate bits) (len bits) (draw bits) (checks bits)
      (framePublic hb A₁) u₂ := by
    rw [framePublic_eq hb A₁ A₂ (hv₁.trans hv₂.symm)]; exact before_of_prepared hb A₂ P₂
  refine ⟨(hct _ _ _ _ _ _ ⟨_, before_of_prepared hb A₁ P₁, hp₂, hsp⟩ e₁ e₂).1, v,
    ⟨s₁, A₁, hv₁, post_of_exec (test_ok M K hb A₁ P₁) e₁⟩,
    ⟨s₂, A₂, hv₂, post_of_exec (test_ok M K hb A₂ P₂) e₂⟩, ?_⟩
  rw [(Exec.rdwr e₁).2.2, (Exec.rdwr e₂).2.2, hsp]

/-- The exit's loads of the workspace's word and of `used`. -/
abbrev exitLoad : List Instr := [ldh .x3 kUsed, .ldrSp .x4 usedSlot]

abbrev exitStatus : List Instr := [.str .x .x3 .x4 0, ldh .x0 kStat, .lsr .x .x3 .x0 1, .sub .x .x0 .x0 .x3]

theorem load_ok {bits : Nat} {hb : Supported bits} {v : View} {u : State} (h : TestedAt hb v u) :
    WP isa (.block exitLoad) u (Loaded v) := by
  obtain ⟨s, A, rfl, T⟩ := h
  obtain ⟨⟨_, inp, _⟩, hsp, hwr, _, _, _, _, hU⟩ := T
  have hx0 := inp.ws.x0
  have h216 := inp.ws.scr.ld (d := 216) (by have := inp.ws.h256; omega_using [this])
  have h136 : InRegions (u.rd ++ u.wr) (off (frameBase s) usedSlot) 8 :=
    ⟨_, List.mem_append_right _ (by rw [hwr]; exact List.mem_cons_self), frame_contains s (by decide)⟩
  have run : WP isa (.block exitLoad) u fun t => t.gpr .x4 = s.gpr .x4 := by
    simp only [word, off, usedSlot] at hU h136 h216
    rw [← hsp] at hU h136
    rw [← hx0] at h216
    brun [State.write, exec_ldrSp (by decide : 136 % 8 = 0 ∧ 136 < 32768), h216, h136, hU, kUsed,
      VG.Impl.Bignum.sFn, usedSlot]
  exact WP.mono (WP.keep [.x3, .x4] run (by decide)) fun t ⟨h4, k⟩ =>
    ⟨(k.gpr .x0 (by decide)).trans hx0, h4⟩

theorem exit_ct {bits : Nat} (hb : Supported bits) :
    RelCT isa (Two (TestedAt hb)) (.block exit) fun _ _ => True := by
  have pins : Pins (TestedAt hb) [.x0] := by
    rintro v u₁ u₂ ⟨s₁, A₁, rfl, T₁⟩ ⟨s₂, A₂, h₂, T₂⟩ r hr
    obtain rfl := List.mem_singleton.mp hr
    obtain ⟨⟨_, inp₁, _⟩, _⟩ := T₁
    obtain ⟨⟨_, inp₂, _⟩, _⟩ := T₂
    rw [inp₁.ws.x0, inp₂.ws.x0]
    simp only [view, View.mk.injEq] at h₂
    change off (s₁.gpr .x0) arithmetic = off (s₂.gpr .x0) arithmetic
    rw [h₂.1]
  change RelCT isa _ (.block (exitLoad ++ exitStatus)) _
  refine RelCT.block_append (RelCT.seq (two_piece [.x0] pins (by taint_decide) fun v u h => load_ok h) ?_)
  intro s t xs ys u w hp es et
  have pl : Pins Loaded [.x0, .x4] := by
    rintro v a b ⟨a0, a4⟩ ⟨b0, b4⟩ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [a0, b0]
    · rw [a4, b4]
  exact two_taint [.x0, .x4] pl (by taint_decide) _ _ _ _ _ _ hp es et

theorem code_ct (M : Mont) (K : VG.Proof.Dsa.AArch64.Generation.PublicKernel) {bits : Nat} (hb : Supported bits) :
    ConstantTime isa (contract bits).pre (contract bits).pub (code bits M.mm K.run) := by
  intro s t xs ys u v hs ht hp es et
  have ct : RelCT isa (fun s t => (contract bits).pre s ∧ (contract bits).pre t ∧ (contract bits).pub s t)
      (code bits M.mm K.run) (fun _ _ => True) := by
    apply RelCT.alloc
    refine RelCT.mono (RelCT.seq (entry_ct hb) (RelCT.seq (test_ct M K hb) (exit_ct hb))) ?_ fun _ _ h => h
    rintro a b ⟨s₁, s₂, ⟨h₁, h₂, hp⟩, rfl, rfl⟩
    have hv := view_of_pub hp
    refine ⟨view bits s₁, ⟨s₁, primeABI_of h₁, rfl, rfl⟩, ⟨s₂, primeABI_of h₂, hv.symm, rfl⟩, ?_⟩
    simp only [view, View.mk.injEq] at hv
    change s₁.sp - _ = s₂.sp - _
    rw [hv.2.2.2.2.2.1]
  exact (ct _ _ _ _ _ _ ⟨hs, ht, hp⟩ es et).1

end VG.Proof.Dsa.AArch64.ProbablePrime
