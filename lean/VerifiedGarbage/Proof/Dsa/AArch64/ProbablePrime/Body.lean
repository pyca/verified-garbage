module

public import VerifiedGarbage.Proof.Dsa.AArch64.ProbablePrime.Params
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.EntryAllocated
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Kernel
public import VerifiedGarbage.Proof.Dsa.AArch64.ProbablePrime.Entry
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeInput

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeFootprint
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Impl.Dsa.AArch64.ProbablePrime
import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd -- shake: keep: its symbolic execution names RegUpd lemmas by path, which shake does not see
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Arguments
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ProbablePrime
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeArguments
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Workspace
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.FrameWord
public import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract
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
  have hread : (u.mem.writeW U used).readW (off B (8 * kStat)) 64 = st := by
    rw [Mem.readW_writeW_sep hsep (by decide)]; exact hst
  have run : WP isa (.block exit) u fun t => t.mem = u.mem.writeW U used ∧ t.gpr .x0 = st - (st >>> 1) := by
    unfold exit usedSlot at *
    simp only [word, off, kUsed, kStat, VG.Impl.Bignum.sFn] at hrU hrS hrF hU hused hst hread
    rw [← hx0] at hrU hrS hused hst hread
    rw [← hsp] at hrF hU
    brun [State.write, exec_ldrSp (by decide : 136 % 8 = 0 ∧ 136 < 32768), hrU, hrS, hrF, hwU, hused, hread, hU, kUsed, kStat, BitVec.add_zero,
      VG.Impl.Bignum.sFn]
    done
  exact WP.mono (WP.keep [.x0, .x3, .x4] run (by decide)) fun t ⟨⟨hm, hx⟩, k⟩ => ⟨hm, hx, k⟩

/-- The test's 0, 1 and 3 are the function's 0, 1 and 2. -/
theorem status_halve (b : Option Bool) :
    let st : BitVec 64 := BitVec.ofNat 64 (match b with | none => 0 | some true => 1 | some false => 3)
    st - (st >>> 1) = BitVec.ofNat 64 (match b with | none => 0 | some true => 1 | some false => 2) := by
  rcases b with _ | _ | _ <;> decide

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
theorem primeFromFrame_ok (M : Mont) (K : Kernel) {P : PrimeParams} {s : State} 
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
  have src : Src u P.B P.Z (W 5 + BitVec.ofNat 64 candidate) bs :=
    hsrc.congrK (fun a ha => hf a (Or.inr (Nat.le_trans hg.h256 ha))) ku
  refine WP.mono (primeBytes_ok M K hi hptr hlen hvalue src hu hw hz hn hpolicy hchecks)
    fun t ⟨used', ht, hut, he, hb, ft, kt⟩ => ?_
  have ff : Frm P.B [(128, 128)] s.mem u.mem := Frm.of_outside hf (by simp)
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

theorem checkPrime_ok (M : Mont) (K : Kernel) {P : PrimeParams} {s : State}
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
  have hz16 : slot P.w 16 ≤ P.Z := Nat.le_trans (Nat.add_le_add_left
    (Nat.mul_le_mul_right (8 * (P.w + 2)) (by decide : 16 ≤ 28)) 256) P.room
  refine WP.seq (WP.mono (workspace_ok hS hdi hz16 (by have := P.w4; omega) hw)
    fun u ⟨hg, _, hf, ku⟩ => ?_)
  have hb : ∀ r ∈ workspaceRanges, r.1 + r.2 ≤ P.Z := by
    have := hg.h256
    simp only [workspaceRanges, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> simp only <;> omega
  have hwu' : ∀ k < 34, word u.mem F (8 * k) = W k := by
    intro k h
    rw [frame_word_of_workspace hf hb (hframe k h), hwords k h]
  have tape := htape.congrK (InScr.of_frm hf hb) ku
  have src := hsrc.congrK (InScr.of_frm hf hb) ku
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
  have hle : BitVec.ofNat 64 272 ≤ s.sp := by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega
  rw [frameBase, BitVec.toNat_sub_of_le hle, BitVec.toNat_ofNat]
  omega

theorem frame_sub (s : State) : Region.Sub ⟨frameBase s, 272⟩ (below s.sp 272) :=
  fun _ h => h

theorem frame_contains (s : State) {d n : Nat} (h : d + n ≤ 272) :
    (⟨frameBase s, 272⟩ : Region).Contains (off (frameBase s) d) n :=
  Offset.contains_base _ h (by omega)

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
  have hFn := frame_toNat A
  have hws : wsRegion s ∈ s.wr := by rw [A.wr]; exact List.mem_cons_self
  have hU : (⟨s.gpr .x4, 8⟩ : Region) ∈ s.wr := by rw [A.wr]; simp
  have hlen : len bits ≤ 384 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  have hw48 : words bits ≤ 48 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  have fws : ∀ {e k : Nat}, e + k ≤ domainCheck →
      Region.Disjoint ⟨frameBase s, 272⟩ ⟨off (s.gpr .x0) e, k⟩ := fun h =>
    (A.stackWs.sub_left (frame_sub s)).sub_right (ws_sub A h)
  have fused : Region.Disjoint ⟨frameBase s, 272⟩ ⟨s.gpr .x4, 8⟩ :=
    A.stackUsed.sub_left (frame_sub s)
  have frand : Region.Disjoint ⟨frameBase s, 272⟩ ⟨s.gpr .x2, (s.gpr .x3).toNat⟩ :=
    A.stackRand.sub_left (frame_sub s)
  have g0 : (allocState 272 s).gpr .x0 = s.gpr .x0 := rfl
  have g2 : (allocState 272 s).gpr .x2 = s.gpr .x2 := rfl
  have g3 : (allocState 272 s).gpr .x3 = s.gpr .x3 := rfl
  have g4 : (allocState 272 s).gpr .x4 = s.gpr .x4 := rfl
  have wr2 : u2.wr = (allocState 272 s).wr := k2.wr
  have rd2 : u2.rd = s.rd := k2.rd
  have sp2 : u2.sp = frameBase s := k2.sp
  -- The frame is all the entry and the save changed.
  have F02 : Frame [⟨frameBase s, 272⟩] s.mem u2.mem := by
    have fl : Frame [⟨frameBase s, 272⟩] s.mem (allocState 272 s).mem := Frame.refl _ _
    rw [m2]
    unfold entryMem
    exact ((((fl.writeW List.mem_cons_self _ (frame_contains s (by decide))).writeW List.mem_cons_self _
      (frame_contains s (by decide))).writeW List.mem_cons_self _ (frame_contains s (by decide))).writeW
      List.mem_cons_self _ (frame_contains s (by decide))).writeW List.mem_cons_self _ (frame_contains s (by decide))
  -- Words of the frame, and the candidate's and the tape's bytes.
  have ew := entryMem_word (allocState 272 s) (frameBase s)
  rw [g0, g2, g3, g4] at ew
  have hB : Scr u2 (params hb A).B (params hb A).Z := by
    have h0 : Scr u2 (s.gpr .x0) ((s.gpr .x1).toNat * 8) :=
      Scr.of_mem (by rw [wr2]; exact List.mem_cons_of_mem _ hws) A.wsBound
    exact h0.sub (o := arithmetic) (n := arithmeticBytes)
      (by have := A.size; have : arithmetic + arithmeticBytes = domainCheck := rfl; omega) (by decide)
  have D0 : Region.Disjoint ⟨frameBase s, 272⟩ ⟨(params hb A).B, (params hb A).Z⟩ :=
    fws (e := arithmetic) (k := arithmeticBytes) (by decide)
  have candOut : ∀ i < len bits, ¬ (⟨frameBase s, 272⟩ : Region).Contains
      (off (s.gpr .x0) (candidate bits) + BitVec.ofNat 64 i) 1 := by
    intro i hi hc
    have hd := fws (e := candidate bits) (k := len bits)
      (by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide)
    exact hd _ hc (contains_byte _ hi (by omega))
  have randOut : ∀ i < (s.gpr .x3).toNat, ¬ (⟨frameBase s, 272⟩ : Region).Contains
      (s.gpr .x2 + BitVec.ofNat 64 i) 1 := by
    intro i hi hc
    exact frand _ hc (contains_byte _ hi (by have := A.randBound; omega))
  have htape : Src u2 (params hb A).B (params hb A).Z (params hb A).rp (params hb A).rand := by
    change Src u2 (off (s.gpr .x0) arithmetic) arithmeticBytes (s.gpr .x2)
      (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
    refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
    · rw [bytesAt_length] at hi
      refine ⟨_, List.mem_append_left _ (by rw [rd2, A.rd]; exact List.mem_cons_self), ?_⟩
      exact contains_byte _ hi (by have := A.randBound; omega)
    · have hi' : i < (s.gpr .x3).toNat := by rw [bytesAt_length] at hi; exact hi
      rw [F02 _ (by simpa only [List.mem_singleton, forall_eq] using randOut i hi')]
      simp only [bytesAt_eq, List.getElem_map, List.getElem_range]
    · have hi' : i < (s.gpr .x3).toNat := by rw [bytesAt_length] at hi; exact hi
      exact out_scr ((A.wsRand.symm).sub_right (ws_sub A (by decide)))
        (contains_byte _ hi' (by have := A.randBound; omega))
  have hsrc : Src u2 (params hb A).B (params hb A).Z
      (word u2.mem (frameBase s) (8 * 5) + BitVec.ofNat 64 (candidate bits))
      (Spec.Rsa.bytesAt s.mem (off (s.gpr .x0) (candidate bits)) (len bits)) := by
    rw [show 8 * 5 = 40 from rfl, m2, ew.1]
    change Src u2 (off (s.gpr .x0) arithmetic) arithmeticBytes (off (s.gpr .x0) (candidate bits))
      (Spec.Rsa.bytesAt s.mem (off (s.gpr .x0) (candidate bits)) (len bits))
    have hcand : candidate bits + len bits ≤ witness := by
      rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
    refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
    · rw [bytesAt_length] at hi
      refine ⟨_, List.mem_append_right _ (by rw [wr2]; exact List.mem_cons_of_mem _ hws), ?_⟩
      rw [show off (s.gpr .x0) (candidate bits) + BitVec.ofNat 64 i = off (s.gpr .x0) (candidate bits + i) by
        simp only [off, BitVec.add_assoc, BitVec.ofNat_add]]
      exact Offset.contains_base _ (by have := A.size; have : witness ≤ domainCheck := (by decide); omega)
        (by have : witness < 2 ^ 64 := (by decide); omega)
    · have hi' : i < len bits := by rw [bytesAt_length] at hi; exact hi
      rw [F02 _ (by simpa only [List.mem_singleton, forall_eq] using candOut i hi')]
      simp only [bytesAt_eq, List.getElem_map, List.getElem_range]
    · have hi' : i < len bits := by rw [bytesAt_length] at hi; exact hi
      refine out_scr (r := ⟨off (s.gpr .x0) (candidate bits), len bits⟩) ?_
        (contains_byte _ hi' (by omega))
      exact Offset.disjoint (s.gpr .x0) (Or.inl (by have : witness ≤ arithmetic := (by decide); omega))
        (by have : witness < 2 ^ 64 := (by decide); omega) (by decide)
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

theorem test_ok (M : Mont) (K : Kernel) {bits : Nat} (hb : Supported bits) {s : State} (A : PrimeABI bits s)
    {u2 : State} (P : Prepared hb A u2) :
    WP isa (test bits M.mm K.run) u2 (Tested hb A) := by
  have hFn := frame_toNat A
  have hws : wsRegion s ∈ s.wr := by rw [A.wr]; exact List.mem_cons_self
  have hU : (⟨s.gpr .x4, 8⟩ : Region) ∈ s.wr := by rw [A.wr]; simp
  have hlen : len bits ≤ 384 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  have hw48 : words bits ≤ 48 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  have fws : ∀ {e k : Nat}, e + k ≤ domainCheck →
      Region.Disjoint ⟨frameBase s, 272⟩ ⟨off (s.gpr .x0) e, k⟩ := fun h =>
    (A.stackWs.sub_left (frame_sub s)).sub_right (ws_sub A h)
  have fused : Region.Disjoint ⟨frameBase s, 272⟩ ⟨s.gpr .x4, 8⟩ :=
    A.stackUsed.sub_left (frame_sub s)
  have D0 : Region.Disjoint ⟨frameBase s, 272⟩ ⟨(params hb A).B, (params hb A).Z⟩ :=
    fws (e := arithmetic) (k := arithmeticBytes) (by decide)
  have frameOut : ∀ r ∈ [(⟨(params hb A).B, arithmeticBytes⟩ : Region), ⟨(params hb A).p, len bits⟩],
      Region.Disjoint ⟨frameBase s, 272⟩ r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact D0
    · exact fws (by have : witness + 384 ≤ domainCheck := (by decide); omega)
  have inFrame : ∀ {d n : Nat}, d + n ≤ 272 → ∀ r ∈ [(⟨(params hb A).B, arithmeticBytes⟩ : Region),
      ⟨(params hb A).p, len bits⟩], Region.Disjoint ⟨off (frameBase s) d, n⟩ r :=
    fun h r hr => (frameOut r hr).sub_left (Offset.sub_base _ h)
  unfold test
  have hlow := ((bitLength_iff_bounds (by have := hb.le; omega)).mp A.bits).1
  -- The test.
  refine WP.mono (VG.Proof.Dsa.AArch64.Generation.checkPrime_ok M K (P := params hb A) (s := u2)
    (used := 0) (candidate := candidate bits) (W := fun k => word u2.mem (frameBase s) (8 * k))
    P.scr P.x0
    (by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide)
    (by change checks bits < _; rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide)
    P.sp
    (fun k hk => ⟨_, List.mem_append_right _ (by rw [P.wr]; exact List.mem_cons_self),
      frame_contains s (by omega)⟩)
    (fun _ _ => rfl)
    (fun k hk j hj => D0.sep (frame_contains s (by omega))
      (Offset.contains_base _ (by change 8 * j + 8 ≤ arithmeticBytes; unfold arithmeticBytes; omega) (by omega)))
    (fun k hk i hi => by
      rw [off_off]
      exact out_scr D0 (frame_contains s (by omega)))
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
      exact Offset.contains_base _ (by have := A.size; have : witness + 384 ≤ domainCheck := (by decide); change i < len bits at hi; omega)
        (by have : witness + 384 < 2 ^ 64 := (by decide); change i < len bits at hi; omega))
    (bytesAt_length _ _ _) rfl (by rw [show 8 * 5 = 40 from rfl, P.arena]; exact P.source) (Nat.zero_le _) hw48
    (by change Bignum.slot (words bits) aTab + 2048 ≤ arithmeticBytes
        rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide)
    (by
      change 8161 < candidateOf bits s
      have h2 : 2 ^ 159 ≤ 2 ^ (bits - 1) := Nat.pow_le_pow_right (by decide) (by have := hb.le; omega)
      have : (8161 : Nat) < 2 ^ 159 := by decide
      exact Nat.lt_of_lt_of_le this (Nat.le_trans h2 hlow))
    (by
      change 1024 < Spec.Dsa.bitLength (candidateOf bits s) ↔ 16 < words bits
      rw [A.bits]; rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide)
    (by
      change checks bits = Spec.Dsa.primeChecks (Spec.Dsa.bitLength (candidateOf bits s))
      rw [A.bits]; rfl)) fun u3 h3 => ?_
  obtain ⟨used', inp, hub, hnone, hsome, wf3, k3⟩ := h3
  have F23 : Frame [⟨(params hb A).B, arithmeticBytes⟩, ⟨(params hb A).p, len bits⟩] u2.mem u3.mem :=
    VG.Proof.Dsa.AArch64.Generation.prime_global_frame wf3
      (VG.Proof.Dsa.AArch64.Generation.checkPrimeRanges_bound hw48)
  refine ⟨⟨used', inp, hub, hnone, hsome⟩, k3.sp.trans P.sp, k3.wr.trans P.wr, k3.rd.trans P.rd,
    (P.frame.mono (by simp)).trans (F23.mono (by simp)), fun r hr => ?_, fun r hr => ?_, ?_⟩
  · have hm : r ∉ mmRegs := by revert r; decide
    have h3 : r ∉ [Reg.x0, .x3] := by revert r; decide
    exact (k3.gpr r hm).trans (P.keep.gpr r h3)
  · exact (k3.vcs r hr).trans (P.keep.vcs r hr)
  rw [← P.usedPtr]
  exact F23.readW (Offset.contains_base _ (d := 0) (n := 8) (k := 8) (by decide) (by decide) |> fun h => by
    simpa only [off, BitVec.add_zero] using h) (inFrame (d := usedSlot) (n := 8) (by decide)) (by decide)

theorem finish_ok {bits : Nat} (hb : Supported bits) {s : State} (A : PrimeABI bits s) {u3 : State}
    (T : Tested hb A u3) :
    WP isa (.block exit) u3 fun t =>
      t.sp = (allocState 272 s).sp ∧ t.wr = (allocState 272 s).wr ∧ t.rd = s.rd ∧ BodyPost bits s t := by
  have hFn := frame_toNat A
  have hws : wsRegion s ∈ s.wr := by rw [A.wr]; exact List.mem_cons_self
  have hU : (⟨s.gpr .x4, 8⟩ : Region) ∈ s.wr := by rw [A.wr]; simp
  have hlen : len bits ≤ 384 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  have hw48 : words bits ≤ 48 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  have fws : ∀ {e k : Nat}, e + k ≤ domainCheck →
      Region.Disjoint ⟨frameBase s, 272⟩ ⟨off (s.gpr .x0) e, k⟩ := fun h =>
    (A.stackWs.sub_left (frame_sub s)).sub_right (ws_sub A h)
  have fused : Region.Disjoint ⟨frameBase s, 272⟩ ⟨s.gpr .x4, 8⟩ :=
    A.stackUsed.sub_left (frame_sub s)
  have D0 : Region.Disjoint ⟨frameBase s, 272⟩ ⟨(params hb A).B, (params hb A).Z⟩ :=
    fws (e := arithmetic) (k := arithmeticBytes) (by decide)
  have frameOut : ∀ r ∈ [(⟨(params hb A).B, arithmeticBytes⟩ : Region), ⟨(params hb A).p, len bits⟩],
      Region.Disjoint ⟨frameBase s, 272⟩ r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact D0
    · exact fws (by have : witness + 384 ≤ domainCheck := (by decide); omega)
  have inFrame : ∀ {d n : Nat}, d + n ≤ 272 → ∀ r ∈ [(⟨(params hb A).B, arithmeticBytes⟩ : Region),
      ⟨(params hb A).p, len bits⟩], Region.Disjoint ⟨off (frameBase s) d, n⟩ r :=
    fun h r hr => (frameOut r hr).sub_left (Offset.sub_base _ h)
  obtain ⟨⟨used', inp, hub, hnone, hsome⟩, sp3, wr3, rd3, F03, g3, v3, hU3⟩ := T
  -- The exit.
  refine WP.mono (exit_ok (u := u3) (B := (params hb A).B) (F := frameBase s) (U := s.gpr .x4)
    (used := BitVec.ofNat 64 used') (st := word u3.mem (params hb A).B (8 * kStat))
    inp.ws.x0 sp3
    (inp.ws.scr.ld (d := 216) (by have := inp.ws.h256; omega))
    (inp.ws.scr.ld (d := 248) (by have := inp.ws.h256; omega))
    ⟨_, List.mem_append_right _ (by rw [wr3]; exact List.mem_cons_self), frame_contains s (by decide)⟩
    ⟨⟨s.gpr .x4, 8⟩, by rw [wr3]; exact List.mem_cons_of_mem _ hU, Region.contains_self _ _⟩
    hU3 inp.used rfl
    (by
      have h := A.wsUsed.sub_left (ws_sub A (d := arithmetic + 248) (n := 8) (by decide))
      rw [show off (s.gpr .x0) (arithmetic + 248) = off (params hb A).B (8 * kStat) by
        simp only [params, off, BitVec.add_assoc, BitVec.ofNat_add]; rfl] at h
      exact h.sep (Region.contains_self _ _) (Region.contains_self _ _))) fun u4 h4 => ?_
  obtain ⟨m4, x04, k4⟩ := h4
  have sp4 : u4.sp = frameBase s := k4.sp.trans sp3
  have wr4 : u4.wr = (allocState 272 s).wr := k4.wr.trans wr3
  have rd4 : u4.rd = s.rd := k4.rd.trans rd3
  -- What changed since the save: the entry's slots, the test's workspace and buffer, and `used`.
  have F34 : Frame [⟨s.gpr .x4, 8⟩] u3.mem u4.mem := by
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
    have F34 : Frame [⟨s.gpr .x4, 8⟩] u3.mem (u3.mem.writeW (s.gpr .x4) (BitVec.ofNat 64 used')) :=
      (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
    refine (F03.mono ?_).trans (F34.mono (by simp [changed]))
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [changed, params]
  · have h4 : r ∉ [Reg.x0, .x3, .x4] := by revert r; decide
    exact (k4.gpr r h4).trans (g3 r hr)

theorem body_ok (M : Mont) (K : Kernel) {bits : Nat} (hb : Supported bits) {s : State}
    (A : PrimeABI bits s) :
    WP isa (body bits M.mm K.run) (allocState 272 s) fun t =>
      t.sp = (allocState 272 s).sp ∧ t.wr = (allocState 272 s).wr ∧ t.rd = s.rd ∧
      BodyPost bits s t := by
  have hwF : ∀ d, d + 8 ≤ 272 → InRegions (allocState 272 s).wr (off (frameBase s) d) 8 :=
    fun d hd => ⟨_, List.mem_cons_self, frame_contains s hd⟩
  simp only [body, seqs]
  refine WP.seq (WP.mono (entry_ok (s := allocState 272 s) (F := frameBase s) rfl hwF)
    fun u2 ⟨m2, x02, k2⟩ => ?_)
  exact WP.seq (WP.mono (test_ok M K hb A (prepared hb A m2 x02 k2)) fun u3 T => finish_ok hb A T)

end VG.Proof.Dsa.AArch64.ProbablePrime
