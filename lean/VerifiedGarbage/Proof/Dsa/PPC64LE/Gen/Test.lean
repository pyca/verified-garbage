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
public import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Dsa.Generation.RandomSuffix
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-! ### `Dsa.PPC64LE.Gen.PrimeCall`, which only this module used -/

section

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
    rw [GP.randP, ite_eq_right (by omega_using [hl])]; exact Offset.sub_base _ (by omega_using [hu])
  · intro a ha; simp only [Region.Contains, show G.witLen - u = 0 by omega_using [hl]] at ha; omega

theorem GI.randFit (h : GI G STK σ V LS s) {u : Nat} (hu : u ≤ G.witLen) :
    (G.randP u).toNat + (G.witLen - u) ≤ 2 ^ 64 := by
  have := h.witFit
  rcases Nat.lt_or_ge u G.witLen with hl | hl
  · rw [GP.randP, ite_eq_right (by omega_using [hl]), BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := u) (by omega_using [this, hl]),
      Nat.mod_eq_of_lt (by omega_using [this, hl])]
    omega_using [hu, this]
  · have := (G.randP u).isLt; omega_using [hl]

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
    rw [VG.Proof.Dsa.Generation.frame_bytesAt h.frame h.wit_apart (by omega_using [fit]), ← h.hG]; rfl
  rcases Nat.lt_or_ge u G.witLen with hl | hl
  · obtain ⟨d, hd⟩ : ∃ d, G.witLen = u + d := ⟨G.witLen - u, by omega_using [hu]⟩
    rw [GP.randP, ite_eq_right (by omega_using [hl]), show G.witLen - u = d by omega_using [hd], ← hw, hd,
      VG.Proof.Dsa.Generation.bytesAt_append, List.drop_left' (by simp [Spec.Rsa.bytesAt])]
  · rw [show G.witLen - u = 0 by omega_using [hl], List.drop_of_length_le (by
      rw [← hw]; simp [Spec.Rsa.bytesAt]; omega_using [hl])]
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

section
variable {G : GP} {σ s : State} {c : Cfg}

theorem GI.witLt {V : Nat → BitVec 64} {LS : List Nat} (h : GI G 176 σ V LS s) : G.witLen < 2 ^ 64 := by
  rw [← h.hG]; exact (σ.gpr .r7).isLt

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
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := wWords_lt lens; omega_using [this])]
  have e6 : (BitVec.ofNat 64 (G.witLen - u)).toNat = G.witLen - u := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [wl])]
  have g : ∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r7], (tEntry G u s).gpr r = s.gpr r := fun r hr => by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)]
  have W8 : wB G.pLen + wWords G.pLen * 8 ≤ G.scrLen * 8 := by omega_using [big]
  have hwW : (G.rs (wB G.pLen) (wWords G.pLen * 8)).Disjoint G.rWit := by
    have := gi.pre.wC; rw [gi.hG] at this; exact this.symm.sub_left (sw G W8)
  have hRand := gi.randSub hu
  have hfU : fUsedOut + 8 ≤ G.scrLen * 8 := by simp only [fUsedOut]; have := gi.hEnd_le; simp only [hEnd] at this; omega_using [this]
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
    exact gi.sdisj (.inr (by simp only [fUsedOut, wB, kB, pB]; omega_using [])) W8 hfU
  · rw [g _ (by simp), g _ (by simp), g _ (by simp), r5, r6, r7, e6]
    have := gi.pre.wC; rw [gi.hG] at this
    exact (this.sub_left hRand).sub_right (sw G hfU)
  · rw [sp, g _ (by simp), g _ (by simp), r3, r4, e4]; exact hbS.sub_right (sw G W8)
  · rw [sp, g _ (by simp), g _ (by simp), r5, r6, e6]; exact hbW.sub_right hRand
  · rw [sp, g _ (by simp), r7]; exact hbS.sub_right (sw G hfU)
  · rw [g _ (by simp), g _ (by simp), r3, r4, e4]
    show (G.scr + BitVec.ofNat 64 (wB G.pLen)).toNat + _ ≤ _
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := wB G.pLen) (by omega_using [wBl]),
      Nat.mod_eq_of_lt (by omega_using [big, fit, wWp])]
    omega_using [big, fit]
  · rw [g _ (by simp), g _ (by simp), r5, r6, e6]; exact gi.randFit hu
  · rw [g _ (by simp), r7]
    show (G.scr + BitVec.ofNat 64 fUsedOut).toNat + 8 ≤ _
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := fUsedOut) (by simp only [fUsedOut]; omega_using []),
      Nat.mod_eq_of_lt (by omega_using [fit, hfU])]
    omega_using [fit, hfU]
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
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := wWords_lt lens; omega_using [this])]
  have e6 : (BitVec.ofNat 64 (G.witLen - u)).toNat = G.witLen - u := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [wl])]
  have hfU : fUsedOut + 8 ≤ G.scrLen * 8 := by simp only [fUsedOut]; have := gi.hEnd_le; simp only [hEnd] at this; omega_using [this]
  refine ⟨Covers.append_left ?_ (Covers.of_mem fun r hr => ?_), ?_⟩
  · rw [gi.rd, gi.pre.rd, gi.hG]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    rcases Nat.lt_or_ge u G.witLen with hl | hl
    · refine ⟨G.rWit, by simp, u, ?_, ?_⟩
      · show G.randP u = G.wit + BitVec.ofNat 64 u
        rw [GP.randP, ite_eq_right (by omega_using [hl])]
      · show u + (BitVec.ofNat 64 (G.witLen - u)).toNat ≤ G.witLen
        rw [e6]; omega_using [hu]
    · refine ⟨G.rWit, by simp, 0, ?_, ?_⟩
      · show G.randP u = G.wit + BitVec.ofNat 64 0
        rw [GP.randP, ite_eq_left (by omega_using [hu, hl])]; simp
      · show 0 + (BitVec.ofNat 64 (G.witLen - u)).toNat ≤ G.witLen
        rw [e6]; omega_using []
  · simp only [List.mem_singleton] at hr; subst hr
    rw [gi.rd, gi.pre.rd, gi.hG]; simp
  · rw [gi.wr, gi.pre.wr, gi.hG]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨G.rScr, by simp, wB G.pLen, rfl, by show wB G.pLen + (BitVec.ofNat 64 (wWords G.pLen)).toNat * 8 ≤ G.scrLen * 8; rw [e4]; omega_using [big]⟩
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
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := wWords_lt lens; omega_using [this])]
  have hfU : fUsedOut + 8 ≤ G.scrLen * 8 := by simp only [fUsedOut]; have := gi.hEnd_le; simp only [hEnd] at this; omega_using [this]
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
    refine gi.frame.readW (r := G.rTab) (Offset.contains_base _ (show 8 * i + 64 / 8 ≤ 8192 by omega_using [hi']) (by omega_using [hi'])) (fun r hr => ?_) (by decide)
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
      · rw [e4]; exact hC.sub_right (sw G (by omega_using [big]))
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
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := wWords_lt lens; omega_using [this])]
  have e6 : (BitVec.ofNat 64 (G.witLen - u)).toNat = G.witLen - u := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [wl])]
  have W8 : wB G.pLen + wWords G.pLen * 8 ≤ G.scrLen * 8 := by omega_using [big]
  have hfU : fUsedOut + 8 ≤ G.scrLen * 8 := by simp only [fUsedOut]; have := gi.hEnd_le; simp only [hEnd] at this; omega_using [this]
  have wWp : 0 < wWords G.pLen := by rcases lens with e | e | e <;> rw [e] <;> decide
  have hBfit : (G.sa (wB G.pLen)).toNat + 8 * wWords G.pLen ≤ 2 ^ 64 := by
    show (G.scr + BitVec.ofNat 64 (wB G.pLen)).toNat + _ ≤ _
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := wB G.pLen) (by omega_using [wBl]),
      Nat.mod_eq_of_lt (by omega_using [big, fit, wWp])]
    omega_using [big, fit]
  obtain ⟨hcovR, hcovW⟩ := h.tCovers hu
  refine WP.callAny ok.verified.1 pin (Covers.append hcovR hcovW)
    hcovW (fun t rd wr sp f g post => ?_) (by have := ok.stack; omega_using [this])
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
      exact Offset.sub_below _ (by omega_using [this]) (by omega_using [this])
  · rw [State.withRegions_gpr] at st; rw [← hres]; exact st
  · intro b rest e
    have := used b rest (by rw [hres]; exact e)
    rw [State.withRegions_mem, eg .r7 (by simp), eg .r6 (by simp), r7, r6, e6] at this
    rw [this, Nat.sub_sub]

end

end VG.Proof.Dsa.PPC64LE.Gen

end

end


/-! # DSA parameter generation on PPC64LE: a probable-prime test (`test_vp`)

`test pLen c src n name code` copies the candidate to byte `c` of the
working space of the functions we call and tests it with the witnesses from
`fUsed` on: `fRes` := its status, and `fUsed` := the witnesses it read when
the tape sufficed (`testCfg`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation

/-- A stage: a state of the search with the contents `c`, and `X` of the run. -/
abbrev St (G : GP) (c : Cfg) (X : State → Prop) (σ s : State) : Prop := SS G 176 σ c s ∧ X σ

/-- The stage after a test, from its result `res`. -/
def testCfg (c : Cfg) (cl : Claims) (witLen : Nat) : Option (Bool × Spec.RsaKeyGen.Rand) → Cfg
  | none => { c with cl := cl }.setV fRes 0
  | some (b, rest) => ({ c with cl := cl }.setV fRes (BitVec.ofNat 64 (if b then 1 else 2))).setV fUsed
      (BitVec.ofNat 64 (witLen - rest.length))

section
variable {G : GP} {c : Cfg} {X : State → Prop}

theorem varOk_of {o : Nat} (h : o + 8 ≤ fSave ∧ o % 8 = 0 ∧ o ≠ fLR ∧ o ∉ [fOut, fWit, fWitLen, fUsedP, fStP]) :
    VarOk G o := by
  refine ⟨h.1, h.2.1, h.2.2.1, fun p hp e => h.2.2.2 ?_⟩
  simp only [fixedWords, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> simp [e]

theorem varOk_fRes : VarOk G fRes := varOk_of (by decide)
theorem varOk_fUsed : VarOk G fUsed := varOk_of (by decide)
theorem varOk_fUsedOut : VarOk G fUsedOut := varOk_of (by decide)

/-! ## The arguments -/

/-- `r3`–`r7`, the test's arguments, from the header. -/
theorem targs_vp {u : Nat} (hu : u ≤ G.witLen) (hU : fUsed ∈ c.LS) (hUv : c.V fUsed = BitVec.ofNat 64 u) :
    VP (St G c X) (.seq (.block [scr .r3 (wB G.pLen), .li .r4 (wWords G.pLen), ld .r9 fUsed, ld .r5 fWit,
        ld .r6 fWitLen, .add .r5 .r5 .r9, .sub .r6 .r6 .r9, scr .r7 fUsedOut])
        (.ite (.zero .d .r6) (.block [ld .r5 fWit]) (.block [])))
      (fun σ s => St G c X σ s ∧ TArgs G u s) := by
  let M : State → State → Prop := fun σ s => St G c X σ s ∧ s.gpr .r3 = G.sa (wB G.pLen) ∧
    s.gpr .r4 = BitVec.ofNat 64 (wWords G.pLen) ∧ s.gpr .r5 = G.wit + BitVec.ofNat 64 u ∧
    s.gpr .r6 = BitVec.ofNat 64 (G.witLen - u) ∧ s.gpr .r7 = G.sa fUsedOut
  refine VP.seq (G := M) (VP.pub (SS.pub (c := fun _ => c) fun σ s h => h.1) []
    ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28]) (.block [scr .r3 (wB 128), .li .r4 (wWords 128),
      ld .r9 fUsed, ld .r5 fWit, ld .r6 fWitLen, .add .r5 .r5 .r9, .sub .r6 .r6 .r9, scr .r7 fUsedOut]), rfl⟩
    (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨h, x⟩ => ?_) ?_
  · have gi := h.gi
    have lens := gi.lens3
    have wl := gi.witLt
    have wBl : wB G.pLen < 2 ^ 15 := by rcases lens with e | e | e <;> rw [e] <;> decide
    refine WP.sp_eq ?_
    refine WP.wr (exec_addi (by decide) wBl) fun s₁ u₁ sp₁ _ => ?_
    have h₁ := h.of_upd u₁ sp₁ (by decide)
    refine WP.wr (exec_li (wWords_lt lens)) fun s₂ u₂ sp₂ _ => ?_
    have h₂ := h₁.of_upd u₂ sp₂ (by decide)
    refine h₂.ldK (o := fUsed) (by decide) (by decide) ((h₂.gi.slotV hU).trans hUv) (by decide) fun s₃ h₃ u₃ => ?_
    refine h₃.ldK (o := fWit) (by decide) (by decide) (h₃.gi.fixedV (v := G.wit) (by simp [fixedWords])) (by decide)
      fun s₄ h₄ u₄ => ?_
    refine h₄.ldK (o := fWitLen) (by decide) (by decide)
      (h₄.gi.fixedV (v := BitVec.ofNat 64 G.witLen) (by simp [fixedWords])) (by decide)
      fun s₅ h₅ u₅ => ?_
    refine WP.wr exec_add fun s₆ u₆ sp₆ _ => ?_
    have h₆ := h₅.of_upd u₆ sp₆ (by decide)
    refine WP.wr exec_sub fun s₇ u₇ sp₇ _ => ?_
    have h₇ := h₆.of_upd u₇ sp₇ (by decide)
    refine WP.wr (exec_addi (by decide) (by decide)) fun s₈ u₈ sp₈ _ => WP.block_nil fun _ => ?_
    have h₈ := h₇.of_upd u₈ sp₈ (by decide)
    refine ⟨⟨h₈, x⟩, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
        u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, gi.r28]
    · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
        u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
    · rw [u₈.other .r5 (by decide), u₇.other .r5 (by decide), u₆.gpr, u₅.other .r5 (by decide),
        u₅.other .r9 (by decide), u₄.gpr, u₄.other .r9 (by decide), u₃.gpr]
    · rw [u₈.other .r6 (by decide), u₇.gpr, u₆.other .r6 (by decide), u₆.other .r9 (by decide), u₅.gpr,
        u₅.other .r9 (by decide), u₄.other .r9 (by decide), u₃.gpr, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_using [hu, wl])
        (by omega_using [hu])]
    · rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), gi.r28]
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.2.2.2.2.1, h₂.2.2.2.2.1]) ?_ ?_
  · refine VP.pub (SS.pub (c := fun _ => c) fun σ s h => h.1.1.1) []
      ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28]) (.block [ld .r5 fWit]), rfl⟩
      (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨⟨⟨h, x⟩, r3, r4, r5, r6, r7⟩, e⟩ => ?_
    have wl := h.gi.witLt
    rw [eval_zero, r6, ofNat_beq_zero (by omega_using [wl])] at e
    have hu' : u = G.witLen := by simp at e; omega_using [hu, e]
    refine WP.sp_eq (h.ldK (o := fWit) (by decide) (by decide) (h.gi.fixedV (v := G.wit) (by simp [fixedWords]))
      (by decide) fun t ht ut => WP.block_nil fun sp => ⟨⟨ht, x⟩, ?_, ?_, ?_, ?_, ?_⟩)
    · rw [ut.other _ (by decide), r3]
    · rw [ut.other _ (by decide), r4]
    · rw [ut.gpr, GP.randP, ite_eq_left hu']
    · rw [ut.other _ (by decide), r6]
    · rw [ut.other _ (by decide), r7]
  · refine VP.block_nil fun σ s ⟨⟨hx, r3, r4, r5, r6, r7⟩, e⟩ => ⟨hx, r3, r4, ?_, r6, r7⟩
    have wl := hx.1.gi.witLt
    rw [eval_zero, r6, ofNat_beq_zero (by omega_using [wl])] at e
    have hu' : u ≠ G.witLen := by simp at e; omega_using [e]
    rw [r5, GP.randP, ite_eq_right hu']

/-! ## The call -/

/-- After the call: the count's word known when the tape sufficed. -/
def callCfg (c : Cfg) (cl : Claims) (witLen u : Nat) : Option (Bool × Spec.RsaKeyGen.Rand) → Cfg
  | none => { c with cl := cl }
  | some (_, rest) => { c with cl := cl }.setV fUsedOut (BitVec.ofNat 64 (witLen - u - rest.length))

/-- One more known header word. -/
theorem GI.addSlot {STK : Nat} {σ t : State} {V : Nat → BitVec 64} {LS : List Nat} (h : GI G STK σ V LS t) {o : Nat}
    (ho : VarOk G o) {v : BitVec 64} (hv : fw t.mem G o = v) : GI G STK σ (upd V o v) (o :: LS) t := by
  refine ⟨h.pre, h.hG, h.sp, h.rd, h.wr, h.r28, h.saved, h.lr, h.fixed, fun o' ho' => ?_, fun o' ho' => ?_, h.frame⟩
  · by_cases e : o' = o
    · subst e; rw [upd_self]; exact hv
    · rw [upd_ne _ _ e]; exact h.slots o' (List.mem_of_ne_of_mem e ho')
  · rcases List.mem_cons.mp ho' with rfl | ho'
    · exact ho
    · exact h.ls o' ho'

/-- The call of the test on the candidate `cb` at byte `L.candidate` of the
working space, with the witnesses from `u` on. -/
theorem primeCall_vp {L : Impl.Dsa.ProbablePrime.Layout} {code : Prog isa} {name : String} {u : Nat}
    {cb : List Byte} {cl' : Claims} (ok : PrimeOk L code) (hu : u ≤ G.witLen)
    (hsize : L.size ≤ 8 * wWords G.pLen) (hL : ∀ r ∈ L.scratch, r.1 + r.2 ≤ 8 * wWords G.pLen)
    (hcb : (wB G.pLen + L.candidate, cb) ∈ c.cl) (hcbl : cb.length = L.bits / 8)
    (hodd : Spec.Dsa.decodeBE cb % 2 = 1) (hbl : Spec.Dsa.bitLength (Spec.Dsa.decodeBE cb) = L.bits)
    (hU : ∀ o ∈ c.LS, fUsedOut + 8 ≤ o ∨ o + 8 ≤ fUsedOut)
    (hcl : ∀ x ∈ cl', x ∈ c.cl ∧ ∀ r ∈ L.scratch, Apart (wB G.pLen + r.1) r.2 x) :
    VP (fun σ s => St G c X σ s ∧ TArgs G u s) (.call name code)
      (fun σ t => St G (callCfg c cl' G.witLen u (tRes G cb u)) X σ t ∧
        ((t.gpr .r3).setWidth 32).toNat = Proof.Dsa.ProbablePrime.status (tRes G cb u)) := by
  have bytes : ∀ σ s, SS G 176 σ c s →
      Spec.Rsa.bytesAt s.mem (G.sa (wB G.pLen) + BitVec.ofNat 64 L.candidate) (L.bits / 8) = cb := fun σ s h => by
    have := h.sb _ hcb; rw [hcbl, ← GP.sa_add] at this; exact this
  refine VP.of_ct' (fun σ₁ σ₂ => ?_) fun σ s ⟨⟨h, x⟩, regs⟩ hy => ?_
  · refine (RelCT.call ok.verified.1 ok.verified.2.1 (tRdK G u) (tWr G)
      fun s₁ s₂ ⟨⟨⟨⟨h₁, _⟩, g₁⟩, y₁⟩, ⟨⟨⟨h₂, _⟩, g₂⟩, y₂⟩⟩ => ?_).mono (fun _ _ h => h) fun _ _ _ => trivial
    have p₁ := h₁.tPre y₁ g₁ hu hsize (bytes _ _ h₁) hodd hbl
    have p₂ := h₂.tPre y₂ g₂ hu hsize (bytes _ _ h₂) hodd hbl
    obtain ⟨cr₁, cw₁⟩ := h₁.tCovers hu
    obtain ⟨cr₂, cw₂⟩ := h₂.tCovers hu
    have eg : ∀ {s : State}, ∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r7], (tEntry G u s).gpr r = s.gpr r := fun r hr => by
      rw [State.withRegions_gpr, State.callEntry_gpr _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)]
    have et : ∀ {σ s : State} {c : Cfg}, SS G 176 σ c s → s.syms = σ.syms →
        s.syms Impl.RsaKeyGen.TrialTable32.symbol = G.tab := fun h y => by rw [y, ← h.gi.hG]; rfl
    obtain ⟨a3, a4, a5, a6, a7⟩ := g₁
    obtain ⟨b3, b4, b5, b6, b7⟩ := g₂
    refine ⟨p₁, p₂, pubK_tEntry (pub_of ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ((et h₁ y₁).trans (et h₂ y₂).symm),
      Covers.append cr₁ cw₁, cw₁, Covers.append cr₂ cw₂, cw₂⟩
    · have e₁ : s₁.sp = G.sp := by rw [h₁.gi.sp, ← h₁.gi.hG]; rfl
      have e₂ : s₂.sp = G.sp := by rw [h₂.gi.sp, ← h₂.gi.hG]; rfl
      show s₁.sp = s₂.sp
      rw [e₁, e₂]
    · rw [eg _ (by simp), eg _ (by simp), a3, b3]
    · rw [eg _ (by simp), eg _ (by simp), a4, b4]
    · rw [eg _ (by simp), eg _ (by simp), a5, b5]
    · rw [eg _ (by simp), eg _ (by simp), a6, b6]
    · rw [eg _ (by simp), eg _ (by simp), a7, b7]
    · simp only [candOf, Proof.Dsa.ProbablePrime.candidateAt, State.withRegions_mem, State.callEntry_mem]
      rw [eg _ (by simp), eg _ (by simp), a3, b3, bytes _ _ h₁, bytes _ _ h₂]
    · have wl := h₁.gi.witLt
      have e6 : (BitVec.ofNat 64 (G.witLen - u)).toNat = G.witLen - u := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [wl])]
      simp only [State.withRegions_mem, State.callEntry_mem]
      rw [eg _ (by simp), eg _ (by simp), eg _ (by simp), eg _ (by simp), a5, a6, b5, b6, e6, h₁.gi.randBytes hu,
        h₂.gi.randBytes hu]
  have hU' : ∀ o ∈ c.LS, fUsedOut + 8 ≤ o ∨ o + 8 ≤ fUsedOut := hU
  refine h.primeCall_ok (name := name) ok hy regs hu hsize hL (bytes _ _ h) hodd hbl
    fun t g rd wr sp f st used => ⟨⟨?_, x⟩, st⟩
  have big := h.gi.wBig
  have kb := h.gi.kBig
  have hE := h.gi.hEnd_le
  have h' : SS G 176 σ { c with cl := cl' } t := by
    refine h.of_hdrScrs (keep_of_preserved g rd wr) sp (os := L.scratch.map fun r => (wB G.pLen + r.1, r.2))
      (fun p hp => ?_) (hw := [fUsedOut]) (fun o ho => ?_) (by
        refine f.sub fun x hx => ?_
        rcases List.mem_append.mp hx with h1 | h2
        · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h1
          exact ⟨G.rs (wB G.pLen + q.1) q.2, List.mem_append_left _ (List.mem_append_left _
            (List.mem_map.mpr ⟨(wB G.pLen + q.1, q.2), List.mem_map.mpr ⟨q, hq, rfl⟩, rfl⟩)), fun _ h => h⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
          rcases h2 with rfl | rfl
          · exact ⟨G.rs fUsedOut 8, List.mem_append_left _ (List.mem_append_right _ (by simp)), fun _ h => h⟩
          · exact ⟨rBelow σ 176, List.mem_append_right _ (by simp), fun _ h => h⟩) fun y hy => ⟨(hcl y hy).1, fun p hp => ?_⟩
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      have := hL q hq
      refine ⟨by simp only [hEnd, wB, kB, pB, fSave] at hE ⊢; omega_using [], .inr (by omega_using []), by simp; omega_using [big, this]⟩
    · simp only [List.mem_singleton] at ho; subst ho; exact ⟨varOk_fUsedOut, hU'⟩
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact (hcl y hy).2 q hq
  unfold callCfg
  split
  · exact h'
  · rename_i b rest e
    refine ⟨h'.gi.addSlot varOk_fUsedOut ?_, h'.sb, h'.clOk, h'.arrs, h'.liveOk, h'.ksl, h'.kslOk⟩
    have := used b rest e
    simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero,
      List.cons.injEq, and_true] at this
    exact this

/-! ## The result -/

theorem status_lt (res : Option (Bool × Spec.RsaKeyGen.Rand)) : Proof.Dsa.ProbablePrime.status res < 3 := by
  unfold Proof.Dsa.ProbablePrime.status; split <;> decide

/-- The test's result, zero-extended, into `fRes`. -/
theorem testRes_vp {c' : Cfg} {res : Option (Bool × Spec.RsaKeyGen.Rand)} :
    VP (fun σ t => St G c' X σ t ∧ ((t.gpr .r3).setWidth 32).toNat = Proof.Dsa.ProbablePrime.status res)
      (.block [.lsr .w .r3 .r3 0, st .r3 fRes])
      (fun σ t => St G (c'.setV fRes (BitVec.ofNat 64 (Proof.Dsa.ProbablePrime.status res))) X σ t ∧
        t.gpr .r3 = BitVec.ofNat 64 (Proof.Dsa.ProbablePrime.status res)) := by
  refine VP.pub (SS.pub (c := fun _ => c') fun σ s h => h.1.1) []
    ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28]) (.block [.lsr .w .r3 .r3 0, st .r3 fRes]), rfl⟩
    (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨⟨h, x⟩, r3⟩ => ?_
  have hv : ((s.gpr .r3).setWidth 32 >>> 0).setWidth 64 = BitVec.ofNat 64 (Proof.Dsa.ProbablePrime.status res) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.ushiftRight_zero, BitVec.toNat_setWidth, r3, BitVec.toNat_ofNat]
  refine WP.wr (exec_lsr_w (by decide)) fun s₁ u₁ sp₁ _ => ?_
  have h₁ := h.of_upd u₁ sp₁ (by decide)
  refine h₁.stF varOk_fRes fun t ht m _ => WP.block_nil ⟨⟨?_, x⟩, ?_⟩
  · rw [u₁.gpr, hv] at ht; exact ht
  · rw [m.gpr, u₁.gpr, hv]

/-- `fUsed` := the witnesses read, unless the tape ran out. -/
theorem testTail_vp {cl' : Claims} {u cand : Nat} (hU : fUsed ∈ c.LS) (hUv : c.V fUsed = BitVec.ofNat 64 u)
    (hU88 : fUsedOut ∉ c.LS) (hwl : G.witB.length = G.witLen) (hu : u ≤ G.witLen) :
    VP (fun σ t => St G ((callCfg c cl' G.witLen u (Spec.Dsa.probablePrime cand (G.witB.drop u))).setV fRes
        (BitVec.ofNat 64 (Proof.Dsa.ProbablePrime.status (Spec.Dsa.probablePrime cand (G.witB.drop u))))) X σ t ∧
        t.gpr .r3 = BitVec.ofNat 64 (Proof.Dsa.ProbablePrime.status (Spec.Dsa.probablePrime cand (G.witB.drop u))))
      (.ite (.zero .d .r3) (.block []) (.block [ld .r4 fUsedOut, ld .r5 fUsed, .add .r5 .r5 .r4, st .r5 fUsed]))
      (St G (testCfg c cl' G.witLen (Spec.Dsa.probablePrime cand (G.witB.drop u))) X) := by
  generalize hres : Spec.Dsa.probablePrime cand (G.witB.drop u) = res
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.2, h₂.2]) ?_ ?_
  · refine VP.block_nil fun σ s ⟨⟨⟨h, x⟩, r3⟩, z⟩ => ?_
    rw [eval_zero, r3, ofNat_beq_zero (by have := status_lt res; omega_using [this])] at z
    rcases res with _ | ⟨b, rest⟩
    · exact ⟨h, x⟩
    · cases b <;> simp [Proof.Dsa.ProbablePrime.status] at z
  rcases res with _ | ⟨b, rest⟩
  · exact VP.of_false fun σ s ⟨⟨_, r3⟩, z⟩ => by
      rw [eval_zero, r3] at z; simp [Proof.Dsa.ProbablePrime.status] at z
  -- The tape sufficed: `fUsed` := `u` and the count.
  have rl : rest.length ≤ G.witLen - u := by
    have := (VG.Proof.Dsa.Generation.probablePrime_suffix hres).length_le
    rw [List.length_drop, hwl] at this; exact this
  let x : BitVec 64 := BitVec.ofNat 64 (G.witLen - u - rest.length)
  let st0 : BitVec 64 := BitVec.ofNat 64 (Proof.Dsa.ProbablePrime.status (some (b, rest)))
  let c6 : Cfg := ({ c with cl := cl' }.setV fUsedOut x).setV fRes st0
  have v88 : c6.V fUsedOut = x := by
    show upd (upd c.V fUsedOut x) fRes st0 fUsedOut = x; rw [upd_ne _ _ (by decide), upd_self]
  have vU : c6.V fUsed = BitVec.ofNat 64 u := by
    show upd (upd c.V fUsedOut x) fRes st0 fUsed = _; rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), hUv]
  refine VP.pub (SS.pub (c := fun _ => c6) fun σ s h => h.1.1.1) []
    ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28])
      (.block [ld .r4 fUsedOut, ld .r5 fUsed, .add .r5 .r5 .r4, st .r5 fUsed]), rfl⟩
    (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨⟨⟨h, xx⟩, _⟩, _⟩ => ?_
  change SS G 176 σ c6 s at h
  refine WP.sp_eq (h.ldK (o := fUsedOut) (by decide) (by decide) ((h.gi.slotV (by simp [c6])).trans v88)
    (by decide) fun s₁ h₁ u₁ => ?_)
  refine h₁.ldK (o := fUsed) (by decide) (by decide) ((h₁.gi.slotV (by simp [c6, hU])).trans vU) (by decide)
    fun s₂ h₂ u₂ => ?_
  refine WP.wr exec_add fun s₃ u₃ sp₃ _ => ?_
  have h₃ := h₂.of_upd u₃ sp₃ (by decide)
  refine h₃.stF varOk_fUsed fun t ht _ _ => WP.block_nil fun _ => ⟨?_, xx⟩
  have v5 : s₃.gpr .r5 = BitVec.ofNat 64 (G.witLen - rest.length) := by
    rw [u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.gpr]
    show BitVec.ofNat 64 u + BitVec.ofNat 64 (G.witLen - u - rest.length) = _
    rw [← BitVec.ofNat_add, show u + (G.witLen - u - rest.length) = G.witLen - rest.length by omega_using [hu, rl]]
  rw [v5] at ht
  refine ht.mono (fun o ho => ?_) (fun x hx => hx) (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩)
  simp only [testCfg, c6, Cfg.setV, List.mem_cons] at ho ⊢
  rcases ho with rfl | rfl | ho
  · exact ⟨by simp, by simp [upd]⟩
  · refine ⟨by simp, ?_⟩
    simp only [upd, show fRes ≠ fUsed by decide, ite_false, ite_true]
    cases b <;> rfl
  · refine ⟨by simp [ho], ?_⟩
    have n88 : o ≠ fUsedOut := fun e => hU88 (e ▸ ho)
    have e : st0 = BitVec.ofNat 64 (if b then 1 else 2) := by cases b <;> rfl
    simp only [upd, n88, ite_false, e]

/-! ## The test -/

/-- The stage after copying the candidate `cb` from `src` to byte `cand` of
the working space of the functions we call. -/
abbrev candCfg (G : GP) (c : Cfg) (cand : Nat) (cb : List Byte) : Cfg :=
  { c with cl := (wB G.pLen + cand, cb) :: c.cl.filter fun x => decide (Apart (wB G.pLen + cand) cb.length x) }

/-- The test of the candidate at `src` (`cb`), copied to the test's working
space, with the tape from `fUsed`: its result in `fRes` and the witnesses it
read in `fUsed`. -/
theorem test_vp {L : Impl.Dsa.ProbablePrime.Layout} {code : Prog isa} {name : String} {u src : Nat}
    {cb : List Byte} {cl' : Claims} (ok : PrimeOk L code) (hu : u ≤ G.witLen) (hU : fUsed ∈ c.LS)
    (hUv : c.V fUsed = BitVec.ofNat 64 u) (hwl : G.witB.length = G.witLen)
    (hsize : L.size ≤ 8 * wWords G.pLen) (hL : ∀ r ∈ L.scratch, r.1 + r.2 ≤ 8 * wWords G.pLen)
    (hcand : L.candidate + L.bits / 8 ≤ 8 * wWords G.pLen) (hcand15 : wB G.pLen + L.candidate < 2 ^ 15)
    (hsrc : (src, cb) ∈ c.cl) (hsrcK : src + cb.length ≤ kB G.pLen) (hcbl : cb.length = L.bits / 8) (hn0 : 0 < cb.length) (hn15 : cb.length < 2 ^ 15)
    (hs15 : src < 2 ^ 15) (hodd : Spec.Dsa.decodeBE cb % 2 = 1)
    (hbl : Spec.Dsa.bitLength (Spec.Dsa.decodeBE cb) = L.bits)
    (hU' : ∀ o ∈ c.LS, fUsedOut + 8 ≤ o ∨ o + 8 ≤ fUsedOut) (hU88 : fUsedOut ∉ c.LS)
    (hcl : ∀ x ∈ cl', x ∈ (candCfg G c L.candidate cb).cl ∧ ∀ r ∈ L.scratch, Apart (wB G.pLen + r.1) r.2 x) :
    VP (St G c X) (test G.pLen L.candidate src cb.length name code)
      (St G (testCfg c cl' G.witLen (tRes G cb u)) X) := by
  have hc0 : ∀ σ s, St G c X σ s → wB G.pLen + L.candidate + cb.length ≤ G.scrLen * 8 := fun σ s ⟨h, _⟩ => by
    have := h.gi.wBig; omega_using [hcand, hcbl, this]
  refine VP.seq (G := St G (candCfg G c L.candidate cb) X)
    (copyS_vp (c := fun _ => c) (fun σ s h => h.1) hn0 hn15 hcand15 hs15
      (fun σ s h => ⟨by have := h.1.gi.kBig; simp only [hEnd, wB, kB, pB, fSave] at this ⊢; omega_using [], by
        simp only [List.length_replicate]; exact .inr (by omega_using []), by simp only [List.length_replicate]; exact hc0 σ s h⟩)
      (fun σ s h => by have := (h.1.clOk _ hsrc).2.2; exact this)
      (.inr (by have := (show kB G.pLen ≤ wB G.pLen by simp only [wB]; omega_using []); omega_using [hsrcK, this]))
      fun σ s t ⟨h, x⟩ h' _ b => ⟨?_, x⟩) ?_
  · refine ⟨h'.gi, h'.sb.cons (by rw [b]; have := h.sb _ hsrc; rw [this]), fun y hy => ?_, h'.arrs, h'.liveOk,
      h'.ksl, h'.kslOk⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨by have := h.gi.kBig; simp only [hEnd, wB, kB, pB, fSave] at this ⊢; omega_using [], .inr (by omega_using []),
        hc0 σ s ⟨h, x⟩⟩
    · exact h'.clOk y hy
  refine VP.assoc (VP.seq (targs_vp (c := candCfg G c L.candidate cb) hu hU hUv)
    (VP.seq (primeCall_vp (c := candCfg G c L.candidate cb) (cl' := cl') (name := name) ok hu hsize hL
      List.mem_cons_self hcbl hodd hbl hU' hcl)
      (VP.seq testRes_vp (testTail_vp (c := candCfg G c L.candidate cb) hU hUv hU88 hwl hu))))

end

end VG.Proof.Dsa.PPC64LE.Gen
