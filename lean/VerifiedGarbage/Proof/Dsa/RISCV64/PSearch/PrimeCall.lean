module

public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.Bytes
public import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract
public import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.TrialTable32

/-! # DSA parameter search on RISC-V: calling the probable-prime test

As on PPC64LE (`Proof/Dsa/PPC64LE/Gen/PrimeCall.lean`), with the one tape
`rand`. `PrimeOk L code`: a verified probable-prime test of layout `L`,
which uses at most `STK0` bytes of stack. It is called with the working
space of the functions we call (`wB p_len` on, `wsW` words: the rest of
`scratch`), the tape from the cursor `u` on (`GP.randP`, `GP.rRand`), which
is unchanged since the call's entry (`GI.randBytes`), and `fUsedOut` for the
octets it reads. A call's changes to the working space are only in the
test's ranges (`frame_of_keeps`).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.PSearch
open VG VG.RISCV64
open VG.Impl.Dsa.RISCV64.ParameterSearch

/-- A verified test of layout `L`, which reads the table of small primes,
with the stack it uses. -/
structure PrimeOk (L : Impl.Dsa.ProbablePrime.Layout) (code : Prog isa) : Prop where
  verified : Verified target code (Proof.Dsa.ProbablePrime.contract L (abi.withConsts kT) STK0)
  stack : sdepth code ≤ STK0

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

/-! ## The tape -/

/-- Where the tape from `u` on starts: `rand` itself when nothing is left. -/
abbrev GP.randP (G : GP) (u : Nat) : Addr := if u = G.randLen then G.rand else G.rand + BitVec.ofNat 64 u

/-- The tape from `u` on. -/
abbrev GP.rRand' (G : GP) (u : Nat) : Region := ⟨G.randP u, G.randLen - u⟩

/-- The words of the working space the functions we call use. -/
abbrev GP.wsW (G : GP) : Nat := G.scrLen - wB G.pLen / 8

section
variable {G : GP} {STK : Nat} {σ s : State} {V : Nat → BitVec 64} {LS : List Nat}

theorem GI.randFit0 (h : GI G STK σ V LS s) : G.rand.toNat + G.randLen ≤ 2 ^ 64 := by
  have := h.pre.nR; rw [← h.hG]; exact this

theorem GI.randLt (h : GI G STK σ V LS s) : G.randLen < 2 ^ 64 := by
  rw [← h.hG]; exact (σ.gpr .a4).isLt

theorem GI.randSub (h : GI G STK σ V LS s) {u : Nat} (hu : u ≤ G.randLen) :
    Region.Sub (G.rRand' u) G.rRand := by
  have := h.randFit0
  rcases Nat.lt_or_ge u G.randLen with hl | hl
  · show Region.Sub ⟨_, _⟩ _
    rw [GP.randP, ite_eq_right (by omega)]; exact Offset.sub_base _ (by omega)
  · intro a ha; simp only [Region.Contains, show G.randLen - u = 0 by omega] at ha; omega

theorem GI.randFit (h : GI G STK σ V LS s) {u : Nat} (hu : u ≤ G.randLen) :
    (G.randP u).toNat + (G.randLen - u) ≤ 2 ^ 64 := by
  have := h.randFit0
  rcases Nat.lt_or_ge u G.randLen with hl | hl
  · rw [GP.randP, ite_eq_right (by omega), BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := u) (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  · have := (G.randP u).isLt; omega

/-- The tape is apart from what the search changes. -/
theorem GI.rand_apart (h : GI G STK σ V LS s) : ∀ r ∈ [G.rScr, rBelow σ STK], G.rRand.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [← h.hG]; exact h.pre.rC
  · rw [← h.hG]; exact h.pre.bR.symm

theorem GI.randB_len (h : GI G STK σ V LS s) : G.randB.length = G.randLen := by
  rw [← h.hG]; simp [mkG, Spec.Rsa.bytesAt]

/-- The tape from `u` on, in memory. -/
theorem GI.randBytes (h : GI G STK σ V LS s) {u : Nat} (hu : u ≤ G.randLen) :
    Spec.Rsa.bytesAt s.mem (G.randP u) (G.randLen - u) = G.randB.drop u := by
  have fit := h.randFit0
  have hw : Spec.Rsa.bytesAt s.mem G.rand G.randLen = G.randB := by
    rw [VG.Proof.Dsa.Generation.frame_bytesAt h.frame h.rand_apart (by omega), ← h.hG]; rfl
  rcases Nat.lt_or_ge u G.randLen with hl | hl
  · obtain ⟨d, hd⟩ : ∃ d, G.randLen = u + d := ⟨G.randLen - u, by omega⟩
    rw [GP.randP, ite_eq_right (by omega), show G.randLen - u = d by omega, ← hw, hd,
      VG.Proof.Dsa.Generation.bytesAt_append, List.drop_left' (by simp [Spec.Rsa.bytesAt])]
  · rw [show G.randLen - u = 0 by omega, List.drop_of_length_le (by
      rw [← hw]; simp [Spec.Rsa.bytesAt]; omega)]
    rfl

end

/-! ## The test's contract, as facts -/

/-- The test's contract under `abi`, without the table. -/
abbrev primeK0 (L : Impl.Dsa.ProbablePrime.Layout) : Contract isa := Proof.Dsa.ProbablePrime.contract L abi STK0

/-- The test's contract. -/
abbrev primeK (L : Impl.Dsa.ProbablePrime.Layout) : Contract isa :=
  Proof.Dsa.ProbablePrime.contract L (abi.withConsts kT) STK0

/-- The candidate at `ws`. -/
abbrev candOf (L : Impl.Dsa.ProbablePrime.Layout) (s : State) : Nat :=
  Proof.Dsa.ProbablePrime.candidateAt L s.mem (s.gpr .a0)

/-- The precondition, as facts. -/
structure PIn (L : Impl.Dsa.ProbablePrime.Layout) (s : State) : Prop where
  sp16 : s.sp.toNat % 16 = 0
  spLo : STK0 ≤ s.sp.toNat
  rd : s.rd = [⟨s.gpr .a2, (s.gpr .a3).toNat⟩]
  wr : s.wr = [⟨s.gpr .a0, (s.gpr .a1).toNat * 8⟩, ⟨s.gpr .a4, 8⟩]
  wR : Region.Disjoint ⟨s.gpr .a0, (s.gpr .a1).toNat * 8⟩ ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
  wU : Region.Disjoint ⟨s.gpr .a0, (s.gpr .a1).toNat * 8⟩ ⟨s.gpr .a4, 8⟩
  rU : Region.Disjoint ⟨s.gpr .a2, (s.gpr .a3).toNat⟩ ⟨s.gpr .a4, 8⟩
  bW : Region.Disjoint ⟨s.sp - 512#64, 512⟩ ⟨s.gpr .a0, (s.gpr .a1).toNat * 8⟩
  bR : Region.Disjoint ⟨s.sp - 512#64, 512⟩ ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
  bU : Region.Disjoint ⟨s.sp - 512#64, 512⟩ ⟨s.gpr .a4, 8⟩
  fw : (s.gpr .a0).toNat + (s.gpr .a1).toNat * 8 ≤ 2 ^ 64
  fr : (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64
  fu : (s.gpr .a4).toNat + 8 ≤ 2 ^ 64
  size : L.size ≤ 8 * (s.gpr .a1).toNat
  odd : candOf L s % 2 = 1
  bl : Spec.Dsa.bitLength (candOf L s) = L.bits
  al0 : (s.gpr .a0).toNat % 8 = 0
  al4 : (s.gpr .a4).toNat % 8 = 0

theorem pre_of_pin {L : Impl.Dsa.ProbablePrime.Layout} {s : State} (h : PIn L s) : (primeK0 L).pre s := by
  sig_pre [primeK0, Proof.Dsa.ProbablePrime.contract, Proof.Dsa.ProbablePrime.sig, abi, argRegs]
  exact ⟨h.sp16, h.spLo, h.rd, h.wr, h.wR, h.wU, h.rU, h.bW, h.bR, h.bU, h.fw, h.fr, h.fu, h.size, h.odd, h.bl,
    h.al0, h.al4⟩

/-- The test's result. -/
abbrev resOf (L : Impl.Dsa.ProbablePrime.Layout) (s : State) : Option (Bool × Spec.RsaKeyGen.Rand) :=
  Spec.Dsa.probablePrime (candOf L s) (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)

/-- The postcondition, as facts. -/
def PPost (L : Impl.Dsa.ProbablePrime.Layout) (s t : State) : Prop :=
  ((t.gpr .a0).setWidth 32).toNat = Proof.Dsa.ProbablePrime.status (resOf L s) ∧
    Proof.Dsa.ModPow.Keeps (s.gpr .a0) (s.gpr .a1).toNat L.scratch s.mem t.mem ∧
    ∀ b rest, resOf L s = some (b, rest) →
      Spec.Rsa.wordsAt t.mem (s.gpr .a4) 1 = [BitVec.ofNat 64 ((s.gpr .a3).toNat - rest.length)]

theorem ppost_of_post {L : Impl.Dsa.ProbablePrime.Layout} {s t : State} (h : (primeK L).post s t) : PPost L s t := by
  replace h : (primeK0 L).post s t := post_consts (c₀ := (Impl.RsaKeyGen.TrialTable32.symbol,
    Impl.RsaKeyGen.TrialTable32.packed)) (cs := []) |>.mp h
  sig_post [primeK0, Proof.Dsa.ProbablePrime.contract, Proof.Dsa.ProbablePrime.sig, abi, argRegs] at h
  exact h

/-- Two calls with the same public arguments, candidate and tape. -/
theorem pub_of {L : Impl.Dsa.ProbablePrime.Layout} {s t : State} (sp : s.sp = t.sp)
    (p0 : s.gpr .a0 = t.gpr .a0) (p1 : s.gpr .a1 = t.gpr .a1) (p2 : s.gpr .a2 = t.gpr .a2)
    (p3 : s.gpr .a3 = t.gpr .a3) (p4 : s.gpr .a4 = t.gpr .a4) (hc : candOf L s = candOf L t)
    (hr : Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat = Spec.Rsa.bytesAt t.mem (t.gpr .a2) (t.gpr .a3).toNat) :
    (primeK0 L).pub s t := by
  sig_pub [primeK0, Proof.Dsa.ProbablePrime.contract, Proof.Dsa.ProbablePrime.sig, abi, argRegs]
  exact ⟨sp, by simp only [candOf] at hc; rw [hc, hr], p0, p1, p2, p3, p4⟩

/-! ## The call -/

/-- The test's arguments, in `a0`–`a4`. -/
abbrev TArgs (G : GP) (u : Nat) (s : State) : Prop :=
  s.gpr .a0 = G.sa (wB G.pLen) ∧ s.gpr .a1 = BitVec.ofNat 64 G.wsW ∧ s.gpr .a2 = G.randP u ∧
    s.gpr .a3 = BitVec.ofNat 64 (G.randLen - u) ∧ s.gpr .a4 = G.sa fUsedOut

/-- The regions the test is given. -/
abbrev tRd (G : GP) (u : Nat) : List Region := [⟨G.randP u, (BitVec.ofNat 64 (G.randLen - u)).toNat⟩]
abbrev tWr (G : GP) : List Region :=
  [⟨G.sa (wB G.pLen), (BitVec.ofNat 64 G.wsW).toNat * 8⟩, ⟨G.sa fUsedOut, 8⟩]

/-- The test's entry, without the table. -/
abbrev tEntry (G : GP) (u : Nat) (s : State) : State := s.callEntry.withRegions (tRd G u) (tWr G)

/-- The regions the test reads, the table among them. -/
abbrev tRdK (G : GP) (u : Nat) : List Region := tRd G u ++ [G.rTab]

/-- The test's entry. -/
abbrev tEntryK (G : GP) (u : Nat) (s : State) : State := s.callEntry.withRegions (tRdK G u) (tWr G)

theorem strip_tEntryK (G : GP) (u : Nat) (s : State) : stripConsts kT (tEntryK G u s) = tEntry G u s := rfl

section
variable {G : GP} {σ s : State} {c : Cfg}

/-- The working space of the functions we call is the rest of `scratch`. -/
theorem SS.wsFit (h : SS G STK0 σ c s) :
    G.wsW < 2 ^ 63 ∧ wB G.pLen + G.wsW * 8 = G.scrLen * 8 ∧ 256 * G.pLen ≤ G.wsW * 8 ∧ wB G.pLen % 8 = 0 := by
  have gi := h.gi
  have big := gi.wBig
  have fit := gi.scrFit
  have l := lay_ok gi.lens
  have : G.scrLen ≤ 2 ^ 61 := by omega
  have := gi.lens
  simp only [GP.wsW]
  omega

theorem eg_entry {G : GP} {u : Nat} {s : State} {r : Reg} (hr : r ∈ [Reg.a0, .a1, .a2, .a3, .a4]) :
    (tEntry G u s).gpr r = s.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)]

/-- The test's arguments meet its precondition. -/
theorem SS.tEntry_pin (h : SS G STK0 σ c s) {L : Impl.Dsa.ProbablePrime.Layout} {u : Nat} (regs : TArgs G u s)
    (hu : u ≤ G.randLen) (hsize : L.size ≤ 8 * G.wsW) {cb : List Byte}
    (hcb : Spec.Rsa.bytesAt s.mem (G.sa (wB G.pLen) + BitVec.ofNat 64 L.candidate) (L.bits / 8) = cb)
    (hodd : Spec.Dsa.decodeBE cb % 2 = 1) (hbl : Spec.Dsa.bitLength (Spec.Dsa.decodeBE cb) = L.bits) :
    PIn L (tEntry G u s) := by
  have gi := h.gi
  have big := gi.wBig
  have kb := gi.kBig
  have fit := gi.scrFit
  have wl := gi.randLt
  obtain ⟨w63, wEq, wPos, w8⟩ := h.wsFit
  have pL := gi.lens
  obtain ⟨r0, r1, r2, r3, r4⟩ := regs
  have e1 : (BitVec.ofNat 64 G.wsW).toNat = G.wsW := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have e3 : (BitVec.ofNat 64 (G.randLen - u)).toNat = G.randLen - u := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have W8 : wB G.pLen + G.wsW * 8 ≤ G.scrLen * 8 := by omega
  have hwW : (G.rs (wB G.pLen) (G.wsW * 8)).Disjoint G.rRand := by
    have := gi.pre.rC; rw [gi.hG] at this; exact this.symm.sub_left (sw G W8)
  have hRand := gi.randSub hu
  have hE := gi.hEnd_le
  have hfU : fUsedOut + 8 ≤ G.scrLen * 8 := by simp only [hEnd, fSave, fUsedOut] at hE ⊢; omega
  have hbS : (rBelow σ STK0).Disjoint G.rScr := by have := gi.pre.bC; rw [gi.hG] at this; exact this
  have hbR : (rBelow σ STK0).Disjoint G.rRand := by have := gi.pre.bR; rw [gi.hG] at this; exact this
  have sp : (tEntry G u s).sp = σ.sp := by rw [State.withRegions_sp, State.callEntry_sp, gi.sp]
  have al : ∀ {o}, o % 8 = 0 → o + 8 ≤ G.scrLen * 8 → (G.sa o).toNat % 8 = 0 := fun h8 ho => gi.al8 h8 ho
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sp]; exact gi.pre.sp16
  · rw [sp]; exact gi.pre.spLo
  · rw [State.withRegions_rd, eg_entry (by simp), eg_entry (by simp), r2, r3]
  · rw [State.withRegions_wr, eg_entry (r := .a0) (by simp), eg_entry (r := .a1) (by simp),
      eg_entry (r := .a4) (by simp), r0, r1, r4]
  · rw [eg_entry (r := .a0) (by simp), eg_entry (r := .a1) (by simp), eg_entry (r := .a2) (by simp),
      eg_entry (r := .a3) (by simp), r0, r1, r2, r3, e1, e3]
    exact hwW.sub_right hRand
  · rw [eg_entry (r := .a0) (by simp), eg_entry (r := .a1) (by simp), eg_entry (r := .a4) (by simp), r0, r1, r4, e1]
    exact gi.sdisj (.inr (by have := (lay_ok gi.lens).1; simp only [fUsedOut, wB, kB, pB] at this ⊢; omega)) W8 hfU
  · rw [eg_entry (r := .a2) (by simp), eg_entry (r := .a3) (by simp), eg_entry (r := .a4) (by simp), r2, r3, r4, e3]
    have := gi.pre.rC; rw [gi.hG] at this
    exact (this.sub_left hRand).sub_right (sw G hfU)
  · rw [sp, eg_entry (r := .a0) (by simp), eg_entry (r := .a1) (by simp), r0, r1, e1]
    exact hbS.sub_right (sw G W8)
  · rw [sp, eg_entry (r := .a2) (by simp), eg_entry (r := .a3) (by simp), r2, r3, e3]
    exact hbR.sub_right hRand
  · rw [sp, eg_entry (r := .a4) (by simp), r4]; exact hbS.sub_right (sw G hfU)
  · rw [eg_entry (r := .a0) (by simp), eg_entry (r := .a1) (by simp), r0, r1, e1]
    show (G.scr + BitVec.ofNat 64 (wB G.pLen)).toNat + _ ≤ _
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := wB G.pLen) (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [eg_entry (r := .a2) (by simp), eg_entry (r := .a3) (by simp), r2, r3, e3]; exact gi.randFit hu
  · rw [eg_entry (r := .a4) (by simp), r4]
    show (G.scr + BitVec.ofNat 64 fUsedOut).toNat + 8 ≤ _
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := fUsedOut) (by simp only [fUsedOut]; omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [eg_entry (r := .a1) (by simp), r1, e1]; exact hsize
  · simp only [candOf, Proof.Dsa.ProbablePrime.candidateAt, State.withRegions_mem, State.callEntry_mem]
    rw [eg_entry (r := .a0) (by simp), r0, hcb]; exact hodd
  · simp only [candOf, Proof.Dsa.ProbablePrime.candidateAt, State.withRegions_mem, State.callEntry_mem]
    rw [eg_entry (r := .a0) (by simp), r0, hcb]; exact hbl
  · rw [eg_entry (r := .a0) (by simp), r0]; exact al w8 (by omega)
  · rw [eg_entry (r := .a4) (by simp), r4]; exact al (by decide) hfU

/-- The test's regions are the search's. -/
theorem SS.tCovers (h : SS G STK0 σ c s) {u : Nat} (hu : u ≤ G.randLen) :
    Covers (tRdK G u) s.rd ∧ Covers (tWr G) s.wr := by
  have gi := h.gi
  have wl := gi.randLt
  obtain ⟨w63, wEq, wPos, w8⟩ := h.wsFit
  have pL := gi.lens
  have e1 : (BitVec.ofNat 64 G.wsW).toNat = G.wsW := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have e3 : (BitVec.ofNat 64 (G.randLen - u)).toNat = G.randLen - u := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hE := gi.hEnd_le
  have hfU : fUsedOut + 8 ≤ G.scrLen * 8 := by simp only [hEnd, fSave, fUsedOut] at hE ⊢; omega
  refine ⟨VG.Covers.append_left ?_ (VG.Covers.of_mem fun r hr => ?_), ?_⟩
  · rw [gi.rd, gi.pre.rd, gi.hG]
    refine VG.Covers.of_sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    rcases Nat.lt_or_ge u G.randLen with hl | hl
    · refine ⟨G.rRand, by simp, u, ?_, ?_⟩
      · show G.randP u = G.rand + BitVec.ofNat 64 u
        rw [GP.randP, ite_eq_right (by omega)]
      · show u + (BitVec.ofNat 64 (G.randLen - u)).toNat ≤ G.randLen
        rw [e3]; omega
    · refine ⟨G.rRand, by simp, 0, ?_, ?_⟩
      · show G.randP u = G.rand + BitVec.ofNat 64 0
        rw [GP.randP, ite_eq_left (by omega)]; simp
      · show 0 + (BitVec.ofNat 64 (G.randLen - u)).toNat ≤ G.randLen
        rw [e3]; omega
  · simp only [List.mem_singleton] at hr; subst hr
    rw [gi.rd, gi.pre.rd, gi.hG]; simp
  · rw [gi.wr, gi.pre.wr, gi.hG]
    refine VG.Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨G.rScr, by simp, wB G.pLen, rfl, by
        show wB G.pLen + (BitVec.ofNat 64 G.wsW).toNat * 8 ≤ G.scrLen * 8; rw [e1]; omega⟩
    · exact ⟨G.rScr, by simp, fUsedOut, rfl, hfU⟩

/-- The table, at the test's entry, under `abi.withConsts`. -/
theorem SS.tConsts (h : SS G STK0 σ c s) (hy : s.syms = σ.syms) (u : Nat) : ConstsOk kT STK0 (tEntryK G u s) := by
  have gi := h.gi
  have tf : G.tab.toNat + 8192 ≤ 2 ^ 64 := by have := gi.pre.tFit; rw [gi.hG] at this; exact this
  have et : (mkG (tEntryK G u s)).rTab = G.rTab := by
    show (⟨s.syms Impl.RsaKeyGen.TrialTable32.symbol, 8192⟩ : Region) = ⟨G.tab, 8192⟩
    rw [hy, ← gi.hG]; rfl
  have hC : G.rTab.Disjoint G.rScr := by have := gi.pre.tC; rw [gi.hG] at this; exact this
  have hB : G.rTab.Disjoint (rBelow σ STK0) := by have := gi.pre.tB; rw [gi.hG] at this; exact this
  obtain ⟨w63, wEq, wPos, w8⟩ := h.wsFit
  have pL := gi.lens
  have e1 : (BitVec.ofNat 64 G.wsW).toNat = G.wsW := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hE := gi.hEnd_le
  have hfU : fUsedOut + 8 ≤ G.scrLen * 8 := by simp only [hEnd, fSave, fUsedOut] at hE ⊢; omega
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
    refine gi.frame.readW (r := G.rTab) (Offset.contains_base _ (show 8 * i + 64 / 8 ≤ 8192 by omega) (by omega))
      (fun r hr => ?_) (by decide)
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
      · rw [e1]; exact hC.sub_right (sw G (by omega))
      · exact hC.sub_right (sw G hfU)
    · have : abi.reserved STK0 (tEntryK G u s) = [rBelow σ STK0] := by
        show stackBelow s.sp STK0 = _
        rw [gi.sp]; rfl
      rw [this, List.mem_singleton] at hr
      subst hr; exact hB
  · intro t ht
    rw [constRegs_kT, et, List.mem_singleton] at ht
    subst ht
    have := gi.pre.tAl; rw [gi.hG] at this; exact this

/-- The test's arguments meet its precondition. -/
theorem SS.tPre (h : SS G STK0 σ c s) (hy : s.syms = σ.syms) {L : Impl.Dsa.ProbablePrime.Layout} {u : Nat}
    (regs : TArgs G u s) (hu : u ≤ G.randLen) (hsize : L.size ≤ 8 * G.wsW) {cb : List Byte}
    (hcb : Spec.Rsa.bytesAt s.mem (G.sa (wB G.pLen) + BitVec.ofNat 64 L.candidate) (L.bits / 8) = cb)
    (hodd : Spec.Dsa.decodeBE cb % 2 = 1) (hbl : Spec.Dsa.bitLength (Spec.Dsa.decodeBE cb) = L.bits) :
    (primeK L).pre (tEntryK G u s) :=
  (pre_consts (c₀ := (Impl.RsaKeyGen.TrialTable32.symbol, Impl.RsaKeyGen.TrialTable32.packed)) (cs := [])).mpr
    ⟨pre_of_pin (h.tEntry_pin regs hu hsize hcb hodd hbl), h.tConsts hy u⟩

/-- Two calls with the same public arguments, candidate and tape, and the
same table. -/
theorem pubK_tEntry {L : Impl.Dsa.ProbablePrime.Layout} {u : Nat} {s t : State}
    (h : (primeK0 L).pub (tEntry G u s) (tEntry G u t))
    (hy : s.syms Impl.RsaKeyGen.TrialTable32.symbol = t.syms Impl.RsaKeyGen.TrialTable32.symbol) :
    (primeK L).pub (tEntryK G u s) (tEntryK G u t) := by
  refine (pub_consts (c₀ := (Impl.RsaKeyGen.TrialTable32.symbol, Impl.RsaKeyGen.TrialTable32.packed))
    (cs := [])).mpr ⟨(pub_stripConsts (K := kT)).mp h, fun k hk => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  subst hk; exact hy

/-- The test's result on the candidate `cb` with the tape from `u` on. -/
abbrev tRes (G : GP) (cb : List Byte) (u : Nat) : Option (Bool × Spec.RsaKeyGen.Rand) :=
  Spec.Dsa.probablePrime (Spec.Dsa.decodeBE cb) (G.randB.drop u)

/-- The call of a test: its status in `a0`'s low half, the octets it read
at `fUsedOut` when the tape sufficed, and memory changed only in the test's
ranges of its working space, the count's word and the stack. -/
theorem SS.primeCall_ok {L : Impl.Dsa.ProbablePrime.Layout} {code : Prog isa} {name : String}
    (ok : PrimeOk L code) (h : SS G STK0 σ c s) (hy : s.syms = σ.syms) {u : Nat} (regs : TArgs G u s)
    (hu : u ≤ G.randLen) (hsize : L.size ≤ 8 * G.wsW) (hL : ∀ r ∈ L.scratch, r.1 + r.2 ≤ 8 * G.wsW)
    {cb : List Byte}
    (hcb : Spec.Rsa.bytesAt s.mem (G.sa (wB G.pLen) + BitVec.ofNat 64 L.candidate) (L.bits / 8) = cb)
    (hodd : Spec.Dsa.decodeBE cb % 2 = 1) (hbl : Spec.Dsa.bitLength (Spec.Dsa.decodeBE cb) = L.bits)
    {Q : State → Prop}
    (k : ∀ t, (∀ r ∈ preserved, t.gpr r = s.gpr r) → t.rd = s.rd → t.wr = s.wr → t.sp = s.sp →
      Frame (L.scratch.map (fun r => G.rs (wB G.pLen + r.1) r.2) ++ [G.rs fUsedOut 8, rBelow σ STK0]) s.mem t.mem →
      ((t.gpr .a0).setWidth 32).toNat = Proof.Dsa.ProbablePrime.status (tRes G cb u) →
      (∀ b rest, tRes G cb u = some (b, rest) →
        Spec.Rsa.wordsAt t.mem (G.sa fUsedOut) 1 = [BitVec.ofNat 64 (G.randLen - u - rest.length)]) → Q t) :
    WP isa (.call name code) s Q := by
  have gi := h.gi
  have fit := gi.scrFit
  have wl := gi.randLt
  obtain ⟨w63, wEq, wPos, w8⟩ := h.wsFit
  have pL := gi.lens
  have pin := h.tPre hy regs hu hsize hcb hodd hbl
  obtain ⟨r0, r1, r2, r3, r4⟩ := regs
  have e1 : (BitVec.ofNat 64 G.wsW).toNat = G.wsW := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have e3 : (BitVec.ofNat 64 (G.randLen - u)).toNat = G.randLen - u := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hBfit : (G.sa (wB G.pLen)).toNat + 8 * G.wsW ≤ 2 ^ 64 := by
    show (G.scr + BitVec.ofNat 64 (wB G.pLen)).toNat + _ ≤ _
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := wB G.pLen) (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  obtain ⟨hcovR, hcovW⟩ := h.tCovers hu
  refine WP.callAny ok.verified.1 pin (Covers.append hcovR hcovW)
    hcovW (fun t rd wr sp f g post => ?_) (by have := ok.stack; simp only [STK0] at this; omega)
  have pp := ppost_of_post post
  obtain ⟨st, keeps, used⟩ := pp
  have eg : ∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a4], (tEntryK G u s).gpr r = s.gpr r := fun r hr => by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)]
  have hres : resOf L (tEntryK G u s) = tRes G cb u := by
    simp only [resOf, candOf, Proof.Dsa.ProbablePrime.candidateAt, State.withRegions_mem, State.callEntry_mem]
    rw [eg .a0 (by simp), eg .a2 (by simp), eg .a3 (by simp), r0, hcb, r2, r3, e3, gi.randBytes hu]
  refine k t g rd wr sp ?_ ?_ ?_
  · rw [State.withRegions_mem, State.callEntry_mem, State.withRegions_mem, eg .a0 (by simp), eg .a1 (by simp),
      r0, r1, e1] at keeps
    have f' := frame_of_keeps (B := G.sa (wB G.pLen)) (wsLen := G.wsW) (rs := L.scratch)
      (rest := [⟨G.sa fUsedOut, 8⟩, below s.sp (sdepth code)])
      hBfit hL (by rw [← e1]; exact f) keeps
    refine f'.sub fun x hx => ?_
    simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with ⟨r, hr, rfl⟩ | rfl | rfl
    · exact ⟨G.rs (wB G.pLen + r.1) r.2, List.mem_append_left _ (List.mem_map.mpr ⟨r, hr, rfl⟩), by
        rw [GP.sa_add]; exact fun _ h => h⟩
    · exact ⟨G.rs fUsedOut 8, by simp, fun _ h => h⟩
    · refine ⟨rBelow σ STK0, by simp, ?_⟩
      have := ok.stack
      have := gi.pre.spLo
      rw [gi.sp]
      exact Offset.sub_below _ (by omega) (by omega)
  · rw [State.withRegions_gpr] at st; rw [← hres]; exact st
  · intro b rest e
    have := used b rest (by rw [hres]; exact e)
    rw [State.withRegions_mem, eg .a4 (by simp), eg .a3 (by simp), r4, r3, e3] at this
    rw [this, Nat.sub_sub]

end

end VG.Proof.Dsa.RISCV64.PSearch
