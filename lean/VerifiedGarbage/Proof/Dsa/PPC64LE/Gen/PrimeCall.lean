module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Bytes
public import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract
public import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchConsts
import VerifiedGarbage.Proof.RsaKeyGen.TrialTable32

/-! # DSA parameter generation on PPC64LE: calling the probable-prime test

`PrimeOk L code`: a verified probable-prime test of layout `L`, which uses at
most 176 bytes of stack. The witnesses from `u` on (`GP.randP`, `GP.rRand`)
are unchanged since the call's entry (`GI.randBytes`). A call's changes to
the working space are only in the test's ranges (`frame_of_keeps`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation

/-- A verified test of layout `L`, which reads the table of small primes,
with the stack it uses. -/
structure PrimeOk (L : Impl.Dsa.ProbablePrime.Layout) (code : Prog isa) : Prop where
  verified : Verified target code (Proof.Dsa.ProbablePrime.contract L (abi.withConsts kT) 176)
  stack : sdepth code ≤ 176

/-- A region's writes and a working space's kept bytes: what changed is the
working space's ranges `rs` and the other regions. -/
theorem frame_of_keeps {B : Addr} {wsLen : Nat} {rs : List (Nat × Nat)} {rest : List Region} {m m' : Mem}
    (hB : B.toNat + 8 * wsLen ≤ 2 ^ 64) (hrs : ∀ r ∈ rs, r.1 + r.2 ≤ 8 * wsLen)
    (f : Frame (⟨B, wsLen * 8⟩ :: rest) m m') (hk : Proof.Dsa.ModPow.Keeps B wsLen rs m m') :
    Frame (rs.map (fun r => ⟨B + BitVec.ofNat 64 r.1, r.2⟩) ++ rest) m m' := by
  intro x hx
  by_cases hin : (⟨B, wsLen * 8⟩ : Region).Contains x 1
  · simp only [Region.Contains] at hin
    have hi : (x - B).toNat < 8 * wsLen := by omega
    have ex : x = B + BitVec.ofNat 64 (x - B).toNat := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm]; exact (BitVec.sub_add_cancel x B).symm
    rw [ex]
    refine hk _ hi fun r hr => ?_
    have hr' := hx _ (List.mem_append_left _ (List.mem_map.mpr ⟨r, hr, rfl⟩))
    have hb := hrs r hr
    by_contra hc
    simp only [not_or, Nat.not_lt, Nat.not_le] at hc
    apply hr'
    have e : x - (B + BitVec.ofNat 64 r.1) = BitVec.ofNat 64 ((x - B).toNat - r.1) := by
      apply BitVec.eq_of_toNat_eq
      rw [← BitVec.sub_sub,
        BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega),
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    show (x - (B + BitVec.ofNat 64 r.1)).toNat + 1 ≤ r.2
    rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  · exact f x fun r hr => by
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hin
      · exact hx r (List.mem_append_right _ hr)

/-! ## The witnesses -/

/-- Where the witnesses from `u` on start: `witnesses` itself when none is left. -/
abbrev GP.randP (G : GP) (u : Nat) : Addr := if u = G.witLen then G.wit else G.wit + BitVec.ofNat 64 u

/-- The witnesses from `u` on. -/
abbrev GP.rRand (G : GP) (u : Nat) : Region := ⟨G.randP u, G.witLen - u⟩

section
variable {G : GP} {STK : Nat} {σ s : State} {V : Nat → BitVec 64} {LS : List Nat}

theorem GI.witFit (h : GI G STK σ V LS s) : G.wit.toNat + G.witLen ≤ 2 ^ 64 := by
  have := h.pre.nW; rw [← h.hG]; exact this

theorem GI.randSub (h : GI G STK σ V LS s) {u : Nat} (hu : u ≤ G.witLen) : Region.Sub (G.rRand u) G.rWit := by
  have := h.witFit
  rcases Nat.lt_or_ge u G.witLen with hl | hl
  · show Region.Sub ⟨_, _⟩ _
    rw [GP.randP, ite_eq_right (by omega)]; exact Offset.sub_base _ (by omega)
  · intro a ha; simp only [Region.Contains, show G.witLen - u = 0 by omega] at ha; omega

theorem GI.randFit (h : GI G STK σ V LS s) {u : Nat} (hu : u ≤ G.witLen) :
    (G.randP u).toNat + (G.witLen - u) ≤ 2 ^ 64 := by
  have := h.witFit
  rcases Nat.lt_or_ge u G.witLen with hl | hl
  · rw [GP.randP, ite_eq_right (by omega), BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := u) (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  · have := (G.randP u).isLt; omega

/-- The witnesses are apart from what the search changes. -/
theorem GI.wit_apart (h : GI G STK σ V LS s) : ∀ r ∈ [G.rScr, rBelow σ STK], G.rWit.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [← h.hG]; exact h.pre.wC
  · rw [← h.hG]; exact h.pre.bW.symm

/-- The witnesses from `u` on, in memory. -/
theorem GI.randBytes (h : GI G STK σ V LS s) {u : Nat} (hu : u ≤ G.witLen) :
    Spec.Rsa.bytesAt s.mem (G.randP u) (G.witLen - u) = G.witB.drop u := by
  have fit := h.witFit
  have hw : Spec.Rsa.bytesAt s.mem G.wit G.witLen = G.witB := by
    rw [VG.Proof.Dsa.Generation.frame_bytesAt h.frame h.wit_apart (by omega), ← h.hG]; rfl
  rcases Nat.lt_or_ge u G.witLen with hl | hl
  · obtain ⟨d, hd⟩ : ∃ d, G.witLen = u + d := ⟨G.witLen - u, by omega⟩
    rw [GP.randP, ite_eq_right (by omega), show G.witLen - u = d by omega, ← hw, hd,
      VG.Proof.Dsa.Generation.bytesAt_append, List.drop_left' (by simp [Spec.Rsa.bytesAt])]
  · rw [show G.witLen - u = 0 by omega, List.drop_of_length_le (by
      rw [← hw]; simp [Spec.Rsa.bytesAt]; omega)]
    rfl

end

/-! ## The test's contract, as facts -/

/-- The test's contract under `abi`, without the table. -/
abbrev primeK0 (L : Impl.Dsa.ProbablePrime.Layout) : Contract isa := Proof.Dsa.ProbablePrime.contract L abi 176

/-- The test's contract. -/
abbrev primeK (L : Impl.Dsa.ProbablePrime.Layout) : Contract isa :=
  Proof.Dsa.ProbablePrime.contract L (abi.withConsts kT) 176

/-- The candidate at `ws`. -/
abbrev candOf (L : Impl.Dsa.ProbablePrime.Layout) (s : State) : Nat :=
  Proof.Dsa.ProbablePrime.candidateAt L s.mem (s.gpr .r3)

/-- The precondition, as facts. -/
structure PIn (L : Impl.Dsa.ProbablePrime.Layout) (s : State) : Prop where
  spLo : 176 ≤ s.sp.toNat
  rd : s.rd = [⟨s.gpr .r5, (s.gpr .r6).toNat⟩]
  wr : s.wr = [⟨s.gpr .r3, (s.gpr .r4).toNat * 8⟩, ⟨s.gpr .r7, 8⟩]
  wR : Region.Disjoint ⟨s.gpr .r3, (s.gpr .r4).toNat * 8⟩ ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
  wU : Region.Disjoint ⟨s.gpr .r3, (s.gpr .r4).toNat * 8⟩ ⟨s.gpr .r7, 8⟩
  rU : Region.Disjoint ⟨s.gpr .r5, (s.gpr .r6).toNat⟩ ⟨s.gpr .r7, 8⟩
  bW : Region.Disjoint ⟨s.sp - 176#64, 176⟩ ⟨s.gpr .r3, (s.gpr .r4).toNat * 8⟩
  bR : Region.Disjoint ⟨s.sp - 176#64, 176⟩ ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
  bU : Region.Disjoint ⟨s.sp - 176#64, 176⟩ ⟨s.gpr .r7, 8⟩
  fw : (s.gpr .r3).toNat + (s.gpr .r4).toNat * 8 ≤ 2 ^ 64
  fr : (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64
  fu : (s.gpr .r7).toNat + 8 ≤ 2 ^ 64
  size : L.size ≤ 8 * (s.gpr .r4).toNat
  odd : candOf L s % 2 = 1
  bl : Spec.Dsa.bitLength (candOf L s) = L.bits

theorem pre_of_pin {L : Impl.Dsa.ProbablePrime.Layout} {s : State} (h : PIn L s) : (primeK0 L).pre s := by
  sig_pre [primeK0, Proof.Dsa.ProbablePrime.contract, Proof.Dsa.ProbablePrime.sig, abi, argRegs]
  exact ⟨h.spLo, h.rd, h.wr, h.wR, h.wU, h.rU, h.bW, h.bR, h.bU, h.fw, h.fr, h.fu, h.size, h.odd, h.bl⟩

/-- The test's result. -/
abbrev resOf (L : Impl.Dsa.ProbablePrime.Layout) (s : State) : Option (Bool × Spec.RsaKeyGen.Rand) :=
  Spec.Dsa.probablePrime (candOf L s) (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)

/-- The postcondition, as facts. -/
def PPost (L : Impl.Dsa.ProbablePrime.Layout) (s t : State) : Prop :=
  ((t.gpr .r3).setWidth 32).toNat = Proof.Dsa.ProbablePrime.status (resOf L s) ∧
    Proof.Dsa.ModPow.Keeps (s.gpr .r3) (s.gpr .r4).toNat L.scratch s.mem t.mem ∧
    ∀ b rest, resOf L s = some (b, rest) →
      Spec.Rsa.wordsAt t.mem (s.gpr .r7) 1 = [BitVec.ofNat 64 ((s.gpr .r6).toNat - rest.length)]

theorem ppost_of_post {L : Impl.Dsa.ProbablePrime.Layout} {s t : State} (h : (primeK L).post s t) : PPost L s t := by
  replace h : (primeK0 L).post s t := post_consts (c₀ := (Impl.RsaKeyGen.TrialTable32.symbol,
    Impl.RsaKeyGen.TrialTable32.packed)) (cs := []) |>.mp h
  sig_post [primeK0, Proof.Dsa.ProbablePrime.contract, Proof.Dsa.ProbablePrime.sig, abi, argRegs] at h
  exact h

/-- Two calls with the same public arguments, candidate and tape. -/
theorem pub_of {L : Impl.Dsa.ProbablePrime.Layout} {s t : State} (sp : s.sp = t.sp)
    (p3 : s.gpr .r3 = t.gpr .r3) (p4 : s.gpr .r4 = t.gpr .r4) (p5 : s.gpr .r5 = t.gpr .r5)
    (p6 : s.gpr .r6 = t.gpr .r6) (p7 : s.gpr .r7 = t.gpr .r7) (hc : candOf L s = candOf L t)
    (hr : Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat = Spec.Rsa.bytesAt t.mem (t.gpr .r5) (t.gpr .r6).toNat) :
    (primeK0 L).pub s t := by
  sig_pub [primeK0, Proof.Dsa.ProbablePrime.contract, Proof.Dsa.ProbablePrime.sig, abi, argRegs]
  exact ⟨sp, by simp only [candOf] at hc; rw [hc, hr], p3, p4, p5, p6, p7⟩

/-! ## The call -/

/-- The test's arguments, in `r3`–`r7`. -/
abbrev TArgs (G : GP) (u : Nat) (s : State) : Prop :=
  s.gpr .r3 = G.sa (wB G.pLen) ∧ s.gpr .r4 = BitVec.ofNat 64 (wWords G.pLen) ∧ s.gpr .r5 = G.randP u ∧
    s.gpr .r6 = BitVec.ofNat 64 (G.witLen - u) ∧ s.gpr .r7 = G.sa fUsedOut

/-- The regions the test is given. -/
abbrev tRd (G : GP) (u : Nat) : List Region := [⟨G.randP u, (BitVec.ofNat 64 (G.witLen - u)).toNat⟩]
abbrev tWr (G : GP) : List Region :=
  [⟨G.sa (wB G.pLen), (BitVec.ofNat 64 (wWords G.pLen)).toNat * 8⟩, ⟨G.sa fUsedOut, 8⟩]

/-- The test's entry, without the table. -/
abbrev tEntry (G : GP) (u : Nat) (s : State) : State := s.callEntry.withRegions (tRd G u) (tWr G)

/-- The regions the test reads, the table among them. -/
abbrev tRdK (G : GP) (u : Nat) : List Region := tRd G u ++ [G.rTab]

/-- The test's entry. -/
abbrev tEntryK (G : GP) (u : Nat) (s : State) : State := s.callEntry.withRegions (tRdK G u) (tWr G)

theorem strip_tEntryK (G : GP) (u : Nat) (s : State) : stripConsts kT (tEntryK G u s) = tEntry G u s := rfl

section
variable {G : GP} {σ s : State} {c : Cfg}

theorem GI.witLt {V : Nat → BitVec 64} {LS : List Nat} (h : GI G 176 σ V LS s) : G.witLen < 2 ^ 64 := by
  rw [← h.hG]; exact (stackArg σ 1).isLt

theorem wWords_lt {L : Nat} (hL : L = 128 ∨ L = 256 ∨ L = 384) : wWords L < 2 ^ 15 := by
  rcases hL with rfl | rfl | rfl <;> decide

/-- The test's arguments meet its precondition. -/
theorem SS.tEntry_pin (h : SS G 176 σ c s) {L : Impl.Dsa.ProbablePrime.Layout} {u : Nat} (regs : TArgs G u s)
    (hu : u ≤ G.witLen) (hsize : L.size ≤ 8 * wWords G.pLen) {cb : List Byte}
    (hcb : Spec.Rsa.bytesAt s.mem (G.sa (wB G.pLen) + BitVec.ofNat 64 L.candidate) (L.bits / 8) = cb)
    (hodd : Spec.Dsa.decodeBE cb % 2 = 1) (hbl : Spec.Dsa.bitLength (Spec.Dsa.decodeBE cb) = L.bits) :
    PIn L (tEntry G u s) := by
  have gi := h.gi
  have big := gi.wBig
  have kb := gi.kBig
  have fit := gi.scrFit
  have wl := gi.witLt
  have lens := gi.lens3
  have wBl : wB G.pLen < 2 ^ 15 := by rcases lens with e | e | e <;> rw [e] <;> decide
  have wWp : 0 < wWords G.pLen := by rcases lens with e | e | e <;> rw [e] <;> decide
  obtain ⟨r3, r4, r5, r6, r7⟩ := regs
  have e4 : (BitVec.ofNat 64 (wWords G.pLen)).toNat = wWords G.pLen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := wWords_lt lens; omega)]
  have e6 : (BitVec.ofNat 64 (G.witLen - u)).toNat = G.witLen - u := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have g : ∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r7], (tEntry G u s).gpr r = s.gpr r := fun r hr => by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)]
  have W8 : wB G.pLen + wWords G.pLen * 8 ≤ G.scrLen * 8 := by omega
  have hwW : (G.rs (wB G.pLen) (wWords G.pLen * 8)).Disjoint G.rWit := by
    have := gi.pre.wC; rw [gi.hG] at this; exact this.symm.sub_left (sw G W8)
  have hRand := gi.randSub hu
  have hfU : fUsedOut + 8 ≤ G.scrLen * 8 := by simp only [fUsedOut]; have := gi.hEnd_le; simp only [hEnd] at this; omega
  have hbS : (rBelow σ 176).Disjoint G.rScr := by have := gi.pre.bC; rw [gi.hG] at this; exact this
  have hbW : (rBelow σ 176).Disjoint G.rWit := by have := gi.pre.bW; rw [gi.hG] at this; exact this
  have sp : (tEntry G u s).sp = σ.sp := by rw [State.withRegions_sp, State.callEntry_sp, gi.sp]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sp]; exact gi.pre.spLo
  · rw [State.withRegions_rd, g _ (by simp), g _ (by simp), r5, r6]
  · rw [State.withRegions_wr, g .r3 (by simp), g .r4 (by simp), g .r7 (by simp), r3, r4, r7]
  · rw [g _ (by simp), g _ (by simp), g _ (by simp), g _ (by simp), r3, r4, r5, r6, e4, e6]
    exact hwW.sub_right hRand
  · rw [g _ (by simp), g _ (by simp), g _ (by simp), r3, r4, r7, e4]
    exact gi.sdisj (.inr (by simp only [fUsedOut, wB, kB, pB]; omega)) W8 hfU
  · rw [g _ (by simp), g _ (by simp), g _ (by simp), r5, r6, r7, e6]
    have := gi.pre.wC; rw [gi.hG] at this
    exact (this.sub_left hRand).sub_right (sw G hfU)
  · rw [sp, g _ (by simp), g _ (by simp), r3, r4, e4]; exact hbS.sub_right (sw G W8)
  · rw [sp, g _ (by simp), g _ (by simp), r5, r6, e6]; exact hbW.sub_right hRand
  · rw [sp, g _ (by simp), r7]; exact hbS.sub_right (sw G hfU)
  · rw [g _ (by simp), g _ (by simp), r3, r4, e4]
    show (G.scr + BitVec.ofNat 64 (wB G.pLen)).toNat + _ ≤ _
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := wB G.pLen) (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [g _ (by simp), g _ (by simp), r5, r6, e6]; exact gi.randFit hu
  · rw [g _ (by simp), r7]
    show (G.scr + BitVec.ofNat 64 fUsedOut).toNat + 8 ≤ _
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := fUsedOut) (by simp only [fUsedOut]; omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [g _ (by simp), r4, e4]; exact hsize
  · simp only [candOf, Proof.Dsa.ProbablePrime.candidateAt, State.withRegions_mem, State.callEntry_mem]
    rw [g _ (by simp), r3, hcb]; exact hodd
  · simp only [candOf, Proof.Dsa.ProbablePrime.candidateAt, State.withRegions_mem, State.callEntry_mem]
    rw [g _ (by simp), r3, hcb]; exact hbl

/-- The test's regions are the search's. -/
theorem SS.tCovers (h : SS G 176 σ c s) {u : Nat} (hu : u ≤ G.witLen) :
    Covers (tRdK G u) s.rd ∧ Covers (tWr G) s.wr := by
  have gi := h.gi
  have big := gi.wBig
  have wl := gi.witLt
  have lens := gi.lens3
  have e4 : (BitVec.ofNat 64 (wWords G.pLen)).toNat = wWords G.pLen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := wWords_lt lens; omega)]
  have e6 : (BitVec.ofNat 64 (G.witLen - u)).toNat = G.witLen - u := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hfU : fUsedOut + 8 ≤ G.scrLen * 8 := by simp only [fUsedOut]; have := gi.hEnd_le; simp only [hEnd] at this; omega
  refine ⟨Covers.append_left ?_ (Covers.of_mem fun r hr => ?_), ?_⟩
  · rw [gi.rd, gi.pre.rd, gi.hG]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    rcases Nat.lt_or_ge u G.witLen with hl | hl
    · refine ⟨G.rWit, by simp, u, ?_, ?_⟩
      · show G.randP u = G.wit + BitVec.ofNat 64 u
        rw [GP.randP, ite_eq_right (by omega)]
      · show u + (BitVec.ofNat 64 (G.witLen - u)).toNat ≤ G.witLen
        rw [e6]; omega
    · refine ⟨G.rWit, by simp, 0, ?_, ?_⟩
      · show G.randP u = G.wit + BitVec.ofNat 64 0
        rw [GP.randP, ite_eq_left (by omega)]; simp
      · show 0 + (BitVec.ofNat 64 (G.witLen - u)).toNat ≤ G.witLen
        rw [e6]; omega
  · simp only [List.mem_singleton] at hr; subst hr
    rw [gi.rd, gi.pre.rd, gi.hG]; simp
  · rw [gi.wr, gi.pre.wr, gi.hG]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨G.rScr, by simp, wB G.pLen, rfl, by show wB G.pLen + (BitVec.ofNat 64 (wWords G.pLen)).toNat * 8 ≤ G.scrLen * 8; rw [e4]; omega⟩
    · exact ⟨G.rScr, by simp, fUsedOut, rfl, hfU⟩

/-- The table, at the test's entry, under `abi.withConsts`. -/
theorem SS.tConsts (h : SS G 176 σ c s) (hy : s.syms = σ.syms) (u : Nat) : ConstsOk kT 176 (tEntryK G u s) := by
  have gi := h.gi
  have fit := gi.scrFit
  have tf : G.tab.toNat + 8192 ≤ 2 ^ 64 := by have := gi.pre.tFit; rw [gi.hG] at this; exact this
  have et : (mkG (tEntryK G u s)).rTab = G.rTab := by
    show (⟨s.syms Impl.RsaKeyGen.TrialTable32.symbol, 8192⟩ : Region) = ⟨G.tab, 8192⟩
    rw [hy, ← gi.hG]; rfl
  have hC : G.rTab.Disjoint G.rScr := by have := gi.pre.tC; rw [gi.hG] at this; exact this
  have hB : G.rTab.Disjoint (rBelow σ 176) := by have := gi.pre.tB; rw [gi.hG] at this; exact this
  have big := gi.wBig
  have kb := gi.kBig
  have lens := gi.lens3
  have e4 : (BitVec.ofNat 64 (wWords G.pLen)).toNat = wWords G.pLen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := wWords_lt lens; omega)]
  have hfU : fUsedOut + 8 ≤ G.scrLen * 8 := by simp only [fUsedOut]; have := gi.hEnd_le; simp only [hEnd] at this; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [constRegs_kT, et]; rfl
  · intro k hk i hi
    simp only [kT, Impl.RsaKeyGen.TrialTable32.consts, List.mem_cons, List.not_mem_nil, or_false] at hk
    subst hk
    have held := gi.pre.held _ List.mem_cons_self i hi
    dsimp only at hi held
    have hi' : i < 1024 := by rw [VG.Proof.RsaKeyGen.TrialTable32.packed_length] at hi; exact hi
    dsimp only
    rw [show (tEntryK G u s).mem = s.mem from rfl, show (tEntryK G u s).syms = s.syms from rfl]
    have eg : σ.syms Impl.RsaKeyGen.TrialTable32.symbol = G.tab := by rw [← gi.hG]; rfl
    rw [← held, hy, eg]
    refine gi.frame.readW (r := G.rTab) (Offset.contains_base _ (show 8 * i + 64 / 8 ≤ 8192 by omega) (by omega)) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hC
    · exact hB
  · intro t ht
    rw [constRegs_kT, et, List.mem_singleton] at ht
    subst ht
    refine ⟨tf, fun r hr => ?_, fun r hr => ?_⟩
    · simp only [tEntryK, State.withRegions_wr, tWr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [e4]; exact hC.sub_right (sw G (by omega))
      · exact hC.sub_right (sw G hfU)
    · have : abi.reserved 176 (tEntryK G u s) = [rBelow σ 176] := by
        show stackBelow s.sp 176 = _
        rw [gi.sp]; rfl
      rw [this, List.mem_singleton] at hr
      subst hr; exact hB
  · intro t ht
    rw [constRegs_kT, et, List.mem_singleton] at ht
    subst ht
    have := gi.pre.tAl; rw [gi.hG] at this; exact this

/-- The test's arguments meet its precondition. -/
theorem SS.tPre (h : SS G 176 σ c s) (hy : s.syms = σ.syms) {L : Impl.Dsa.ProbablePrime.Layout} {u : Nat}
    (regs : TArgs G u s) (hu : u ≤ G.witLen) (hsize : L.size ≤ 8 * wWords G.pLen) {cb : List Byte}
    (hcb : Spec.Rsa.bytesAt s.mem (G.sa (wB G.pLen) + BitVec.ofNat 64 L.candidate) (L.bits / 8) = cb)
    (hodd : Spec.Dsa.decodeBE cb % 2 = 1) (hbl : Spec.Dsa.bitLength (Spec.Dsa.decodeBE cb) = L.bits) :
    (primeK L).pre (tEntryK G u s) :=
  (pre_consts (c₀ := (Impl.RsaKeyGen.TrialTable32.symbol, Impl.RsaKeyGen.TrialTable32.packed)) (cs := [])).mpr
    ⟨pre_of_pin (h.tEntry_pin regs hu hsize hcb hodd hbl), h.tConsts hy u⟩

/-- Two calls with the same public arguments, candidate and tape, and the
same table. -/
theorem pubK_of {L : Impl.Dsa.ProbablePrime.Layout} {s t : State} (h : (primeK0 L).pub (stripConsts kT s) (stripConsts kT t))
    (hy : s.syms Impl.RsaKeyGen.TrialTable32.symbol = t.syms Impl.RsaKeyGen.TrialTable32.symbol) :
    (primeK L).pub s t := by
  refine (pub_consts (c₀ := (Impl.RsaKeyGen.TrialTable32.symbol, Impl.RsaKeyGen.TrialTable32.packed))
    (cs := [])).mpr ⟨(pub_stripConsts (K := kT)).mp h, fun k hk => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  subst hk; exact hy

theorem pubK_tEntry {L : Impl.Dsa.ProbablePrime.Layout} {G : GP} {u : Nat} {s t : State}
    (h : (primeK0 L).pub (tEntry G u s) (tEntry G u t))
    (hy : s.syms Impl.RsaKeyGen.TrialTable32.symbol = t.syms Impl.RsaKeyGen.TrialTable32.symbol) :
    (primeK L).pub (tEntryK G u s) (tEntryK G u t) :=
  pubK_of h hy

/-- The test's result on the candidate `cb` with the witnesses from `u` on. -/
abbrev tRes (G : GP) (cb : List Byte) (u : Nat) : Option (Bool × Spec.RsaKeyGen.Rand) :=
  Spec.Dsa.probablePrime (Spec.Dsa.decodeBE cb) (G.witB.drop u)

/-- The call of a test: its status in `r3`'s low half, the witnesses it read
at `fUsedOut` when the tape sufficed, and memory changed only in the test's
ranges of its working space, the count's word and the stack. -/
theorem SS.primeCall_ok {L : Impl.Dsa.ProbablePrime.Layout} {code : Prog isa} {name : String}
    (ok : PrimeOk L code) (h : SS G 176 σ c s) (hy : s.syms = σ.syms) {u : Nat} (regs : TArgs G u s)
    (hu : u ≤ G.witLen) (hsize : L.size ≤ 8 * wWords G.pLen) (hL : ∀ r ∈ L.scratch, r.1 + r.2 ≤ 8 * wWords G.pLen)
    {cb : List Byte}
    (hcb : Spec.Rsa.bytesAt s.mem (G.sa (wB G.pLen) + BitVec.ofNat 64 L.candidate) (L.bits / 8) = cb)
    (hodd : Spec.Dsa.decodeBE cb % 2 = 1) (hbl : Spec.Dsa.bitLength (Spec.Dsa.decodeBE cb) = L.bits)
    {Q : State → Prop}
    (k : ∀ t, (∀ r ∈ preserved, t.gpr r = s.gpr r) → t.rd = s.rd → t.wr = s.wr → t.sp = s.sp →
      Frame (L.scratch.map (fun r => G.rs (wB G.pLen + r.1) r.2) ++ [G.rs fUsedOut 8, rBelow σ 176]) s.mem t.mem →
      ((t.gpr .r3).setWidth 32).toNat = Proof.Dsa.ProbablePrime.status (tRes G cb u) →
      (∀ b rest, tRes G cb u = some (b, rest) →
        Spec.Rsa.wordsAt t.mem (G.sa fUsedOut) 1 = [BitVec.ofNat 64 (G.witLen - u - rest.length)]) → Q t) :
    WP isa (.call name code) s Q := by
  have gi := h.gi
  have big := gi.wBig
  have kb := gi.kBig
  have fit := gi.scrFit
  have wl := gi.witLt
  have lens := gi.lens3
  have wBl : wB G.pLen < 2 ^ 15 := by rcases lens with e | e | e <;> rw [e] <;> decide
  have pin := h.tPre hy regs hu hsize hcb hodd hbl
  obtain ⟨r3, r4, r5, r6, r7⟩ := regs
  have e4 : (BitVec.ofNat 64 (wWords G.pLen)).toNat = wWords G.pLen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := wWords_lt lens; omega)]
  have e6 : (BitVec.ofNat 64 (G.witLen - u)).toNat = G.witLen - u := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have W8 : wB G.pLen + wWords G.pLen * 8 ≤ G.scrLen * 8 := by omega
  have hfU : fUsedOut + 8 ≤ G.scrLen * 8 := by simp only [fUsedOut]; have := gi.hEnd_le; simp only [hEnd] at this; omega
  have wWp : 0 < wWords G.pLen := by rcases lens with e | e | e <;> rw [e] <;> decide
  have hBfit : (G.sa (wB G.pLen)).toNat + 8 * wWords G.pLen ≤ 2 ^ 64 := by
    show (G.scr + BitVec.ofNat 64 (wB G.pLen)).toNat + _ ≤ _
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := wB G.pLen) (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  obtain ⟨hcovR, hcovW⟩ := h.tCovers hu
  refine WP.callAny ok.verified.1 pin (Covers.append hcovR hcovW)
    hcovW (fun t rd wr sp f g post => ?_) (by have := ok.stack; omega)
  have pp := ppost_of_post post
  obtain ⟨st, keeps, used⟩ := pp
  have eg : ∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r7], (tEntryK G u s).gpr r = s.gpr r := fun r hr => by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)]
  have hres : resOf L (tEntryK G u s) = tRes G cb u := by
    simp only [resOf, candOf, Proof.Dsa.ProbablePrime.candidateAt, State.withRegions_mem, State.callEntry_mem]
    rw [eg .r3 (by simp), eg .r5 (by simp), eg .r6 (by simp), r3, hcb, r5, r6, e6, gi.randBytes hu]
  refine k t g rd wr sp ?_ ?_ ?_
  · rw [State.withRegions_mem, State.callEntry_mem, State.withRegions_mem, eg .r3 (by simp), eg .r4 (by simp),
      r3, r4, e4] at keeps
    have f' := frame_of_keeps (B := G.sa (wB G.pLen)) (wsLen := wWords G.pLen) (rs := L.scratch)
      (rest := [⟨G.sa fUsedOut, 8⟩, below s.sp (sdepth code)])
      hBfit hL (by rw [← e4]; exact f) keeps
    refine f'.sub fun x hx => ?_
    simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with ⟨r, hr, rfl⟩ | rfl | rfl
    · exact ⟨G.rs (wB G.pLen + r.1) r.2, List.mem_append_left _ (List.mem_map.mpr ⟨r, hr, rfl⟩), by
        rw [GP.sa_add]; exact fun _ h => h⟩
    · exact ⟨G.rs fUsedOut 8, by simp, fun _ h => h⟩
    · refine ⟨rBelow σ 176, by simp, ?_⟩
      have := ok.stack
      rw [gi.sp]
      exact Offset.sub_below _ (by omega) (by omega)
  · rw [State.withRegions_gpr] at st; rw [← hres]; exact st
  · intro b rest e
    have := used b rest (by rw [hres]; exact e)
    rw [State.withRegions_mem, eg .r7 (by simp), eg .r6 (by simp), r7, r6, e6] at this
    rw [this, Nat.sub_sub]

end

end VG.Proof.Dsa.PPC64LE.Gen
