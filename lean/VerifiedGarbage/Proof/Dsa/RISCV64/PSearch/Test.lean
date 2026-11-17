module

public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.Ctl
public import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Generation.RandomSuffix
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.Bytes
public import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract
public import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaKeyGen.TrialTable32

/-! ### `Dsa.RISCV64.PSearch.PrimeCall`, which this module and modules that import it used -/

section

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
    obtain hi : (x - B).toNat < 8 * wsLen := by omega
    obtain ex : x = B + BitVec.ofNat 64 (x - B).toNat := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm]; exact (BitVec.sub_add_cancel x B).symm
    rw [ex]
    refine hk _ hi fun r hr => ?_
    obtain hr' := hx _ (List.mem_append_left _ (List.mem_map.mpr ⟨r, hr, rfl⟩))
    obtain hb := hrs r hr
    by_contra hc
    simp only [not_or, Nat.not_lt, Nat.not_le] at hc
    apply hr'
    obtain e : x - (B + BitVec.ofNat 64 r.1) = BitVec.ofNat 64 ((x - B).toNat - r.1) := by
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
  obtain hw : Spec.Rsa.bytesAt s.mem G.rand G.randLen = G.randB := by
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
  obtain l := lay_ok gi.lens
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
  obtain e1 : (BitVec.ofNat 64 G.wsW).toNat = G.wsW := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  obtain e3 : (BitVec.ofNat 64 (G.randLen - u)).toNat = G.randLen - u := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  obtain W8 : wB G.pLen + G.wsW * 8 ≤ G.scrLen * 8 := by omega
  obtain hwW : (G.rs (wB G.pLen) (G.wsW * 8)).Disjoint G.rRand := by
    have := gi.pre.rC; rw [gi.hG] at this; exact this.symm.sub_left (sw G W8)
  obtain hRand := gi.randSub hu
  have hE := gi.hEnd_le
  obtain hfU : fUsedOut + 8 ≤ G.scrLen * 8 := by simp only [hEnd, fSave, fUsedOut] at hE ⊢; omega
  obtain hbS : (rBelow σ STK0).Disjoint G.rScr := by have := gi.pre.bC; rw [gi.hG] at this; exact this
  obtain hbR : (rBelow σ STK0).Disjoint G.rRand := by have := gi.pre.bR; rw [gi.hG] at this; exact this
  obtain sp : (tEntry G u s).sp = σ.sp := by rw [State.withRegions_sp, State.callEntry_sp, gi.sp]
  obtain al : ∀ {o}, o % 8 = 0 → o + 8 ≤ G.scrLen * 8 → (G.sa o).toNat % 8 = 0 := fun h8 ho => gi.al8 h8 ho
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
  obtain e1 : (BitVec.ofNat 64 G.wsW).toNat = G.wsW := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  obtain e3 : (BitVec.ofNat 64 (G.randLen - u)).toNat = G.randLen - u := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hE := gi.hEnd_le
  obtain hfU : fUsedOut + 8 ≤ G.scrLen * 8 := by simp only [hEnd, fSave, fUsedOut] at hE ⊢; omega
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
  obtain tf : G.tab.toNat + 8192 ≤ 2 ^ 64 := by have := gi.pre.tFit; rw [gi.hG] at this; exact this
  obtain et : (mkG (tEntryK G u s)).rTab = G.rTab := by
    show (⟨s.syms Impl.RsaKeyGen.TrialTable32.symbol, 8192⟩ : Region) = ⟨G.tab, 8192⟩
    rw [hy, ← gi.hG]; rfl
  obtain hC : G.rTab.Disjoint G.rScr := by have := gi.pre.tC; rw [gi.hG] at this; exact this
  obtain hB : G.rTab.Disjoint (rBelow σ STK0) := by have := gi.pre.tB; rw [gi.hG] at this; exact this
  obtain ⟨w63, wEq, wPos, w8⟩ := h.wsFit
  have pL := gi.lens
  obtain e1 : (BitVec.ofNat 64 G.wsW).toNat = G.wsW := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hE := gi.hEnd_le
  obtain hfU : fUsedOut + 8 ≤ G.scrLen * 8 := by simp only [hEnd, fSave, fUsedOut] at hE ⊢; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [constRegs_kT, et]; rfl
  · intro k hk i hi
    simp only [kT, Impl.RsaKeyGen.TrialTable32.consts, List.mem_cons, List.not_mem_nil, or_false] at hk
    subst hk
    obtain held := gi.pre.held _ List.mem_cons_self i hi
    dsimp only at hi held
    obtain hi' : i < 1024 := by rw [VG.Proof.RsaKeyGen.TrialTable32.packed_length] at hi; exact hi
    dsimp only
    rw [show (tEntryK G u s).mem = s.mem from rfl, show (tEntryK G u s).syms = s.syms from rfl]
    obtain eg : σ.syms Impl.RsaKeyGen.TrialTable32.symbol = G.tab := by rw [← gi.hG]; rfl
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
  obtain pin := h.tPre hy regs hu hsize hcb hodd hbl
  obtain ⟨r0, r1, r2, r3, r4⟩ := regs
  obtain e1 : (BitVec.ofNat 64 G.wsW).toNat = G.wsW := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  obtain e3 : (BitVec.ofNat 64 (G.randLen - u)).toNat = G.randLen - u := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  obtain hBfit : (G.sa (wB G.pLen)).toNat + 8 * G.wsW ≤ 2 ^ 64 := by
    show (G.scr + BitVec.ofNat 64 (wB G.pLen)).toNat + _ ≤ _
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := wB G.pLen) (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  obtain ⟨hcovR, hcovW⟩ := h.tCovers hu
  refine WP.callAny ok.verified.1 pin (Covers.append hcovR hcovW)
    hcovW (fun t rd wr sp f g post => ?_) (by have := ok.stack; simp only [STK0] at this; omega)
  obtain pp := ppost_of_post post
  obtain ⟨st, keeps, used⟩ := pp
  obtain eg : ∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a4], (tEntryK G u s).gpr r = s.gpr r := fun r hr => by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)]
  obtain hres : resOf L (tEntryK G u s) = tRes G cb u := by
    simp only [resOf, candOf, Proof.Dsa.ProbablePrime.candidateAt, State.withRegions_mem, State.callEntry_mem]
    rw [eg .a0 (by simp), eg .a2 (by simp), eg .a3 (by simp), r0, hcb, r2, r3, e3, gi.randBytes hu]
  refine k t g rd wr sp ?_ ?_ ?_
  · rw [State.withRegions_mem, State.callEntry_mem, State.withRegions_mem, eg .a0 (by simp), eg .a1 (by simp),
      r0, r1, e1] at keeps
    obtain f' := frame_of_keeps (B := G.sa (wB G.pLen)) (wsLen := G.wsW) (rs := L.scratch)
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

end

end

/-! # DSA parameter search on RISC-V: a probable-prime test (`test_vp`)

As on PPC64LE (`Proof/Dsa/PPC64LE/Gen/Test.lean`). `test pLen src n name
code` copies the candidate to byte 0 of the working space of the functions
we call and tests it with the tape from the cursor `fUsed` on: `fRes` := its
status, and `fUsed` := the octets it read when the tape sufficed
(`testCfg`).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.PSearch
open VG VG.RISCV64 VG.RISCV64.Steps
open VG.Impl.Dsa.RISCV64.ParameterSearch

/-- The stage after a test, from its result `res`. -/
def testCfg (c : Cfg) (cl : Claims) (randLen : Nat) : Option (Bool × Spec.RsaKeyGen.Rand) → Cfg
  | none => { c with cl := cl }.setV fRes 0
  | some (b, rest) => ({ c with cl := cl }.setV fRes (BitVec.ofNat 64 (if b then 1 else 2))).setV fUsed
      (BitVec.ofNat 64 (randLen - rest.length))

theorem varOk_fRes {G : GP} : VarOk G fRes := varOk_of (by decide)
theorem varOk_fUsedOut {G : GP} : VarOk G fUsedOut := varOk_of (by decide)

/-- One more known header word. -/
theorem GI.addSlot {G : GP} {STK : Nat} {σ t : State} {V : Nat → BitVec 64} {LS : List Nat}
    (h : GI G STK σ V LS t) {o : Nat} (ho : VarOk G o) {v : BitVec 64} (hv : fw t.mem G o = v) :
    GI G STK σ (upd V o v) (o :: LS) t := by
  refine ⟨h.pre, h.hG, h.sp, h.rd, h.wr, h.s6, h.saved, h.ra, h.fixed, fun o' ho' => ?_, fun o' ho' => ?_,
    h.frame⟩
  · by_cases e : o' = o
    · subst e; rw [upd_self]; exact hv
    · rw [upd_ne _ _ e]; exact h.slots o' (List.mem_of_ne_of_mem e ho')
  · rcases List.mem_cons.mp ho' with rfl | ho'
    · exact ho
    · exact h.ls o' ho'

section
variable {G : GP} {STK : Nat} {σ : State} {c : Cfg} {s t : State}

/-- A step that writes the ranges `os` of `scratch` (past the header, apart
from the key working space), the header words `hw` (variable, not among
`LS`) and the stack below the stack pointer: the claims `cl'`, each kept and
apart from the ranges. -/
theorem SS.of_hdrScrs {ws : List Reg} (h : SS G STK σ c s) (r : Keep ws s t) (sp : t.sp = s.sp)
    {os : List (Nat × Nat)} (hon : ∀ p ∈ os, ClOk G (p.1, List.replicate p.2 0)) {hw : List Nat}
    (hhw : ∀ o ∈ hw, VarOk G o ∧ ∀ o' ∈ c.LS, o + 8 ≤ o' ∨ o' + 8 ≤ o)
    (f : Frame (G.rss os ++ hw.map (fun o => G.rs o 8) ++ [rBelow σ STK]) s.mem t.mem) {cl' : Claims}
    (hcl : ∀ x ∈ cl', x ∈ c.cl ∧ ∀ p ∈ os, Apart p.1 p.2 x)
    (h6 : .s6 ∉ ws := by decide) : SS G STK σ { c with cl := cl' } t := by
  have gi := h.gi
  have big := gi.wBig
  have kb := gi.kBig
  have fit := gi.scrFit
  have hE := gi.hEnd_le
  obtain lk := (lay_ok gi.lens).1
  obtain hon' : ∀ p ∈ os, hEnd ≤ p.1 ∧ (p.1 + p.2 ≤ kB G.pLen ∨ wB G.pLen ≤ p.1) ∧ p.1 + p.2 ≤ G.scrLen * 8 :=
    fun p hp => by have := hon p hp; simp only [ClOk, List.length_replicate] at this; exact this
  obtain hw' : ∀ o ∈ hw, o + 8 ≤ fSave := fun o ho => (hhw o ho).1.1
  obtain mem : ∀ r' ∈ G.rss os ++ hw.map (fun o => G.rs o 8) ++ [rBelow σ STK],
      (∃ p ∈ os, r' = G.rs p.1 p.2) ∨ (∃ o ∈ hw, r' = G.rs o 8) ∨ r' = rBelow σ STK := fun r' hr' => by
    simp only [GP.rss, List.mem_append, List.mem_map, List.mem_singleton] at hr'
    rcases hr' with (⟨p, hp, rfl⟩ | ⟨o, ho, rfl⟩) | rfl
    · exact .inl ⟨p, hp, rfl⟩
    · exact .inr (.inl ⟨o, ho, rfl⟩)
    · exact .inr (.inr rfl)
  obtain kd : ∀ r' ∈ G.rss os ++ hw.map (fun o => G.rs o 8) ++ [rBelow σ STK],
      (⟨G.KB, kz G.pLen⟩ : Region).Disjoint r' := fun r' hr' => by
    rcases mem r' hr' with ⟨p, hp, rfl⟩ | ⟨o, ho, rfl⟩ | rfl
    · obtain ⟨_, a, b⟩ := hon' p hp; exact gi.kdisj a b
    · have := hw' o ho
      exact gi.kdisj (.inl (by simp only [pB, pBytes, fSave] at this lk ⊢; omega))
        (by simp only [hEnd] at hE; omega)
    · exact gi.scr_below (by omega)
  obtain hd : ∀ q, q + 8 ≤ hEnd → (∀ o ∈ hw, o + 8 ≤ q ∨ q + 8 ≤ o) →
      ∀ r' ∈ G.rss os ++ hw.map (fun o => G.rs o 8) ++ [rBelow σ STK], (G.rs q 8).Disjoint r' :=
    fun q hq hq' r' hr' => by
      rcases mem r' hr' with ⟨p, hp, rfl⟩ | ⟨o, ho, rfl⟩ | rfl
      · obtain ⟨a, _, b⟩ := hon' p hp; exact gi.sdisj (.inl (by omega)) (by omega) b
      · have := hw' o ho
        exact gi.sdisj (hq' o ho).symm (by omega) (by simp only [hEnd] at hE; omega)
      · exact gi.scr_below (by omega)
  obtain fixedFar : ∀ p ∈ fixedWords G, ∀ o ∈ hw, o + 8 ≤ p.1 ∨ p.1 + 8 ≤ o := fun p hp o ho => by
    obtain ⟨_, a8, _, af⟩ := (hhw o ho).1
    obtain ⟨b, b8⟩ := fixed_ok G p hp
    have := af p hp; omega
  obtain gi' : GI G STK σ c.V c.LS t := by
    refine ⟨gi.pre, gi.hG, sp.trans gi.sp, r.2.1.trans gi.rd, r.2.2.trans gi.wr, (r.gpr h6).trans gi.s6,
      fun i hi => ?_, ?_, fun p hp => ?_, fun p hp => ?_, gi.ls, gi.frame.trans (f.sub fun x hx => ?_)⟩
    · rw [fw_frame f (hd _ (by simp only [hEnd]; omega) fun o ho => by
        have := hw' o ho; simp only [fSave] at *; omega)]
      exact gi.saved i hi
    · rw [fw_frame f (hd _ (by decide) fun o ho => by
        obtain ⟨_, a8, aL, _⟩ := (hhw o ho).1; simp only [fRA] at aL ⊢; omega)]
      exact gi.ra
    · rw [fw_frame f (hd _ (by have := (fixed_ok G p hp).1; simp only [hEnd]; omega) (fixedFar p hp))]
      exact gi.fixed p hp
    · rw [fw_frame f (hd _ (by have := (gi.ls p hp).1; simp only [hEnd]; omega) fun o ho => (hhw o ho).2 p hp)]
      exact gi.slots p hp
    · rcases mem x hx with ⟨p, hp, rfl⟩ | ⟨o, ho, rfl⟩ | rfl
      · exact ⟨G.rScr, List.mem_cons_self, sw G (hon' p hp).2.2⟩
      · exact ⟨G.rScr, List.mem_cons_self, sw G (by have := hw' o ho; simp only [hEnd] at hE; omega)⟩
      · exact ⟨rBelow σ STK, by simp, fun _ h => h⟩
  refine ⟨gi', fun x hx => ?_, fun x hx => h.clOk x (hcl x hx).1, fun j hj => ?_, h.liveOk, fun d hd' => ?_,
    h.kslOk⟩
  · obtain ⟨hm, ha⟩ := hcl x hx
    obtain ⟨xE, _, xb⟩ := h.clOk x hm
    rw [VG.Proof.Dsa.Generation.frame_bytesAt f (fun r' hr' => by
      rcases mem r' hr' with ⟨p, hp, rfl⟩ | ⟨o, ho, rfl⟩ | rfl
      · exact gi.sdisj (ha p hp) xb (hon' p hp).2.2
      · have := hw' o ho
        exact gi.sdisj (.inr (by simp only [hEnd] at xE; omega)) xb (by simp only [hEnd] at hE; omega)
      · exact gi.scr_below xb) (by omega)]
    exact h.sb x hm
  · rw [num_frame h.lens f kd (h.liveOk j hj)]; exact h.arrs j hj
  · rw [slot_frame f kd (h.kslOk d hd')]; exact h.ksl d hd'

end

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-! ## The arguments -/

theorem shr3 {x : Nat} (hx : x < 2 ^ 64) : BitVec.ofNat 64 x >>> 3 = BitVec.ofNat 64 (x / 8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt (by omega)]

/-- The second block of the test: `a0`–`a4`, its arguments, but `a2` when
nothing is left of the tape. -/
abbrev tblock (pLen : Nat) : List Instr :=
  scrB .a0 (wB pLen) ++ wsLen .a1 pLen ++ ([ld .t2 fUsed, ld .a2 fWit, ld .a3 fWitLen,
    .add .a2 .a2 .t2, .sub .a3 .a3 .t2, scr .a4 fUsedOut] : List Instr)

/-- `a0`–`a4`, the test's arguments, from the header. -/
theorem targs_vp {u : Nat} (hu : u ≤ G.randLen) (hU : fUsed ∈ c.LS) (hUv : c.V fUsed = BitVec.ofNat 64 u) :
    VP (St G c X) (.seq (.block (tblock G.pLen)) (.ite (.zero .a3) (.block [ld .a2 fWit]) (.block [])))
      (fun σ s => St G c X σ s ∧ TArgs G u s) := by
  let M : State → State → Prop := fun σ s => St G c X σ s ∧ s.gpr .a0 = G.sa (wB G.pLen) ∧
    s.gpr .a1 = BitVec.ofNat 64 G.wsW ∧ s.gpr .a2 = G.rand + BitVec.ofNat 64 u ∧
    s.gpr .a3 = BitVec.ofNat 64 (G.randLen - u) ∧ s.gpr .a4 = G.sa fUsedOut
  refine VP.seq (G := M) (VP.pub (SS.pub (c := fun _ => c) fun σ s h => h.1) []
    ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6]) (.block (tblock G.pLen)), by kernel_rfl⟩
    (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨h, x⟩ => ?_) ?_
  · have gi := h.gi
    have lens := gi.lens
    have wl := gi.randLt
    obtain ⟨w63, wEq, wPos, w8⟩ := h.wsFit
    obtain l := lay_ok lens
    obtain h7 : wB G.pLen / 4096 < 8 := by rcases lens with e | e | e <;> rw [e] <;> decide
    simp only [tblock, wsLen, List.cons_append, List.nil_append, List.append_assoc]
    refine scrB_ok (by decide) gi.s6 l.2.2.2.1 h7 fun s₁ K₁ m₁ sp₁ v₀ => ?_
    obtain h₁ := h.of_keep K₁ m₁ sp₁
    refine h₁.ldK (o := fScrLen) (by decide) (by decide)
      (h₁.gi.fixedV (v := BitVec.ofNat 64 G.scrLen) (by simp [fixedWords])) (t := .a1) (by decide)
      fun s₂ h₂ u₂ => ?_
    refine WP.cons exec_lui ?_
    obtain u₂' := Upd.write s₂ .t3 (sext32 (BitVec.ofNat 20 (wB G.pLen / 4096) ++ (0 : BitVec 12)))
    obtain h₂' := h₂.of_upd u₂' (by decide)
    refine wp_srl (by decide) fun s₃ u₃ => ?_
    obtain h₃ := h₂'.of_upd u₃ (by decide)
    refine wp_sub fun s₄ u₄ => ?_
    obtain h₄ := h₃.of_upd u₄ (by decide)
    refine h₄.ldK (o := fUsed) (by decide) (by decide) ((h₄.gi.slotV hU).trans hUv) (t := .t2) (by decide)
      fun s₅ h₅ u₅ => ?_
    refine h₅.ldK (o := fWit) (by decide) (by decide) (h₅.gi.fixedV (v := G.rand) (by simp [fixedWords]))
      (t := .a2) (by decide) fun s₆ h₆ u₆ => ?_
    refine h₆.ldK (o := fWitLen) (by decide) (by decide)
      (h₆.gi.fixedV (v := BitVec.ofNat 64 G.randLen) (by simp [fixedWords])) (t := .a3) (by decide)
      fun s₇ h₇ u₇ => ?_
    refine wp_add fun s₈ u₈ => ?_
    obtain h₈ := h₇.of_upd u₈ (by decide)
    refine wp_sub fun s₉ u₉ => ?_
    obtain h₉ := h₈.of_upd u₉ (by decide)
    refine wp_addi (by decide) fun s₁₀ u₁₀ => WP.block_nil ?_
    obtain h₁₀ := h₉.of_upd u₁₀ (by decide)
    obtain lv : sext32 (BitVec.ofNat 20 (wB G.pLen / 4096) ++ (0 : BitVec 12)) = BitVec.ofNat 64 (wB G.pLen) := by
      rw [luiv _ h7, show 4096 * (wB G.pLen / 4096) = wB G.pLen by omega]
    refine ⟨⟨h₁₀, x⟩, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
        u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂'.other _ (by decide), u₂.other _ (by decide), v₀]
    · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
        u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
        u₂'.other _ (by decide), u₂.gpr, u₃.gpr, u₂'.gpr, lv, shr3 (by omega),
        BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]
    · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide),
        u₇.other _ (by decide), u₆.gpr, u₆.other _ (by decide), u₅.gpr]
    · rw [u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide), u₈.other _ (by decide), u₇.gpr,
        u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega)
        (by omega)]
    · rw [u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
        u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂'.other _ (by decide), u₂.other _ (by decide), K₁.gpr (by decide), gi.s6]
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.2.2.2.2.1, h₂.2.2.2.2.1]) ?_ ?_
  · refine VP.pub (SS.pub (c := fun _ => c) fun σ s h => h.1.1.1) []
      ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6]) (.block [ld .a2 fWit]), by kernel_rfl⟩
      (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨⟨⟨h, x⟩, r0, r1, r2, r3, r4⟩, e⟩ => ?_
    have wl := h.gi.randLt
    rw [eval_zero, r3, ofNat_beq_zero (by omega)] at e
    obtain hu' : u = G.randLen := by simp at e; omega
    refine h.ldK (o := fWit) (by decide) (by decide) (h.gi.fixedV (v := G.rand) (by simp [fixedWords]))
      (t := .a2) (by decide) fun t ht ut => WP.block_nil ⟨⟨ht, x⟩, ?_, ?_, ?_, ?_, ?_⟩
    · rw [ut.other _ (by decide), r0]
    · rw [ut.other _ (by decide), r1]
    · rw [ut.gpr, GP.randP, ite_eq_left hu']
    · rw [ut.other _ (by decide), r3]
    · rw [ut.other _ (by decide), r4]
  · refine VP.block_nil fun σ s ⟨⟨hx, r0, r1, r2, r3, r4⟩, e⟩ => ⟨hx, r0, r1, ?_, r3, r4⟩
    have wl := hx.1.gi.randLt
    rw [eval_zero, r3, ofNat_beq_zero (by omega)] at e
    obtain hu' : u ≠ G.randLen := by simp at e; omega
    rw [r2, GP.randP, ite_eq_right hu']

/-! ## The call -/

/-- After the call: the count's word known when the tape sufficed. -/
def callCfg (c : Cfg) (cl : Claims) (randLen u : Nat) : Option (Bool × Spec.RsaKeyGen.Rand) → Cfg
  | none => { c with cl := cl }
  | some (_, rest) => { c with cl := cl }.setV fUsedOut (BitVec.ofNat 64 (randLen - u - rest.length))

/-- The call of the test on the candidate `cb` at byte `L.candidate` of the
working space, with the tape from `u` on. -/
theorem primeCall_vp {L : Impl.Dsa.ProbablePrime.Layout} {code : Prog isa} {name : String} {u : Nat}
    {cb : List Byte} {cl' : Claims} (ok : PrimeOk L code) (hu : u ≤ G.randLen)
    (hsize : L.size ≤ 256 * G.pLen) (hL : ∀ r ∈ L.scratch, r.1 + r.2 ≤ 256 * G.pLen)
    (hcb : (wB G.pLen + L.candidate, cb) ∈ c.cl) (hcbl : cb.length = L.bits / 8)
    (hodd : Spec.Dsa.decodeBE cb % 2 = 1) (hbl : Spec.Dsa.bitLength (Spec.Dsa.decodeBE cb) = L.bits)
    (hU : ∀ o ∈ c.LS, fUsedOut + 8 ≤ o ∨ o + 8 ≤ fUsedOut)
    (hcl : ∀ x ∈ cl', x ∈ c.cl ∧ ∀ r ∈ L.scratch, Apart (wB G.pLen + r.1) r.2 x) :
    VP (fun σ s => St G c X σ s ∧ TArgs G u s) (.call name code)
      (fun σ t => St G (callCfg c cl' G.randLen u (tRes G cb u)) X σ t ∧
        ((t.gpr .a0).setWidth 32).toNat = Proof.Dsa.ProbablePrime.status (tRes G cb u)) := by
  obtain bytes : ∀ σ s, SS G STK0 σ c s →
      Spec.Rsa.bytesAt s.mem (G.sa (wB G.pLen) + BitVec.ofNat 64 L.candidate) (L.bits / 8) = cb := fun σ s h => by
    have := h.sb _ hcb; rw [hcbl, ← GP.sa_add] at this; exact this
  obtain sz : ∀ σ s, SS G STK0 σ c s → L.size ≤ 8 * G.wsW ∧ ∀ r ∈ L.scratch, r.1 + r.2 ≤ 8 * G.wsW :=
    fun σ s h => by
      have := h.wsFit.2.2.1
      exact ⟨by omega, fun r hr => by have := hL r hr; omega⟩
  refine VP.of_ct' (fun σ₁ σ₂ => ?_) fun σ s ⟨⟨h, x⟩, regs⟩ hy => ?_
  · refine (RelCT.call ok.verified.1 ok.verified.2.1 (tRdK G u) (tWr G)
      fun s₁ s₂ ⟨⟨⟨⟨h₁, _⟩, g₁⟩, y₁⟩, ⟨⟨⟨h₂, _⟩, g₂⟩, y₂⟩⟩ => ?_).mono (fun _ _ h => h) fun _ _ _ => trivial
    obtain p₁ := h₁.tPre y₁ g₁ hu (sz _ _ h₁).1 (bytes _ _ h₁) hodd hbl
    obtain p₂ := h₂.tPre y₂ g₂ hu (sz _ _ h₂).1 (bytes _ _ h₂) hodd hbl
    obtain ⟨cr₁, cw₁⟩ := h₁.tCovers hu
    obtain ⟨cr₂, cw₂⟩ := h₂.tCovers hu
    obtain et : ∀ {σ s : State} {c : Cfg}, SS G STK0 σ c s → s.syms = σ.syms →
        s.syms Impl.RsaKeyGen.TrialTable32.symbol = G.tab := fun h y => by rw [y, ← h.gi.hG]; rfl
    obtain ⟨a0, a1, a2, a3, a4⟩ := g₁
    obtain ⟨b0, b1, b2, b3, b4⟩ := g₂
    refine ⟨p₁, p₂, pubK_tEntry (pub_of ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ((et h₁ y₁).trans (et h₂ y₂).symm),
      Covers.append cr₁ cw₁, cw₁, Covers.append cr₂ cw₂, cw₂⟩
    · have e₁ : s₁.sp = G.sp := by rw [h₁.gi.sp, ← h₁.gi.hG]; rfl
      obtain e₂ : s₂.sp = G.sp := by rw [h₂.gi.sp, ← h₂.gi.hG]; rfl
      show s₁.sp = s₂.sp
      rw [e₁, e₂]
    · rw [eg_entry (by simp), eg_entry (by simp), a0, b0]
    · rw [eg_entry (by simp), eg_entry (by simp), a1, b1]
    · rw [eg_entry (by simp), eg_entry (by simp), a2, b2]
    · rw [eg_entry (by simp), eg_entry (by simp), a3, b3]
    · rw [eg_entry (by simp), eg_entry (by simp), a4, b4]
    · simp only [candOf, Proof.Dsa.ProbablePrime.candidateAt, State.withRegions_mem, State.callEntry_mem]
      rw [eg_entry (by simp), eg_entry (by simp), a0, b0, bytes _ _ h₁, bytes _ _ h₂]
    · have wl := h₁.gi.randLt
      obtain e3 : (BitVec.ofNat 64 (G.randLen - u)).toNat = G.randLen - u := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      simp only [State.withRegions_mem, State.callEntry_mem]
      rw [eg_entry (r := .a2) (by simp), eg_entry (r := .a2) (by simp), eg_entry (r := .a3) (by simp),
        eg_entry (r := .a3) (by simp), a2, a3, b2, b3, e3, h₁.gi.randBytes hu, h₂.gi.randBytes hu]
  refine h.primeCall_ok (name := name) ok hy regs hu (sz _ _ h).1 (sz _ _ h).2 (bytes _ _ h) hodd hbl
    fun t g rd wr sp f st used => ⟨⟨?_, x⟩, st⟩
  have big := h.gi.wBig
  have kb := h.gi.kBig
  have hE := h.gi.hEnd_le
  have wf := h.wsFit
  obtain h' : SS G STK0 σ { c with cl := cl' } t := by
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
          · exact ⟨rBelow σ STK0, List.mem_append_right _ (by simp), fun _ h => h⟩)
      fun y hy => ⟨(hcl y hy).1, fun p hp => ?_⟩
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      have := hL q hq
      refine ⟨by have := (lay_ok h.lens).1; simp only [hEnd, wB, kB, pB, fSave] at hE this ⊢; omega,
        .inr (by omega), by simp; omega⟩
    · simp only [List.mem_singleton] at ho; subst ho; exact ⟨varOk_fUsedOut, hU⟩
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

theorem zext32 (x : BitVec 64) : x <<< 32 >>> 32 = BitVec.ofNat 64 ((x.setWidth 32).toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  omega

/-- The test's result, zero-extended, into `fRes`. -/
theorem testRes_vp {c' : Cfg} {res : Option (Bool × Spec.RsaKeyGen.Rand)} :
    VP (fun σ t => St G c' X σ t ∧ ((t.gpr .a0).setWidth 32).toNat = Proof.Dsa.ProbablePrime.status res)
      (.block [.shift .sll .d .a0 .a0 32, .shift .srl .d .a0 .a0 32, st .a0 fRes])
      (fun σ t => St G (c'.setV fRes (BitVec.ofNat 64 (Proof.Dsa.ProbablePrime.status res))) X σ t ∧
        t.gpr .a0 = BitVec.ofNat 64 (Proof.Dsa.ProbablePrime.status res)) := by
  refine VP.pub (SS.pub (c := fun _ => c') fun σ s h => h.1.1) []
    ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6])
      (.block [.shift .sll .d .a0 .a0 32, .shift .srl .d .a0 .a0 32, st .a0 fRes]), by kernel_rfl⟩
    (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨⟨h, x⟩, a0⟩ => ?_
  refine wp_sll (by decide) fun s₁ u₁ => ?_
  refine wp_srl (by decide) fun s₂ u₂ => ?_
  obtain hv : s₂.gpr .a0 = BitVec.ofNat 64 (Proof.Dsa.ProbablePrime.status res) := by
    rw [u₂.gpr, u₁.gpr, zext32, a0]
  obtain h₂ := (h.of_upd u₁ (by decide)).of_upd u₂ (by decide)
  refine h₂.stF varOk_fRes fun t ht m => WP.block_nil ⟨⟨?_, x⟩, ?_⟩
  · rw [hv] at ht; exact ht
  · rw [m.gpr, hv]

/-- `fUsed` := the octets read, unless the tape ran out. -/
theorem testTail_vp {cl' : Claims} {u cand : Nat} (hU : fUsed ∈ c.LS) (hUv : c.V fUsed = BitVec.ofNat 64 u)
    (hU88 : fUsedOut ∉ c.LS) (hwl : G.randB.length = G.randLen) (hu : u ≤ G.randLen) :
    VP (fun σ t => St G ((callCfg c cl' G.randLen u (Spec.Dsa.probablePrime cand (G.randB.drop u))).setV fRes
        (BitVec.ofNat 64 (Proof.Dsa.ProbablePrime.status (Spec.Dsa.probablePrime cand (G.randB.drop u))))) X σ t ∧
        t.gpr .a0 = BitVec.ofNat 64 (Proof.Dsa.ProbablePrime.status (Spec.Dsa.probablePrime cand (G.randB.drop u))))
      (.ite (.zero .a0) (.block []) (.block [ld .t3 fUsedOut, ld .t4 fUsed, .add .t4 .t4 .t3, st .t4 fUsed]))
      (St G (testCfg c cl' G.randLen (Spec.Dsa.probablePrime cand (G.randB.drop u))) X) := by
  generalize hres : Spec.Dsa.probablePrime cand (G.randB.drop u) = res
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.2, h₂.2]) ?_ ?_
  · refine VP.block_nil fun σ s ⟨⟨⟨h, x⟩, a0⟩, z⟩ => ?_
    rw [eval_zero, a0, ofNat_beq_zero (by have := status_lt res; omega)] at z
    rcases res with _ | ⟨b, rest⟩
    · exact ⟨h, x⟩
    · cases b <;> simp [Proof.Dsa.ProbablePrime.status] at z
  rcases res with _ | ⟨b, rest⟩
  · exact VP.of_false fun σ s ⟨⟨_, a0⟩, z⟩ => by
      rw [eval_zero, a0] at z; simp [Proof.Dsa.ProbablePrime.status] at z
  obtain rl : rest.length ≤ G.randLen - u := by
    have := (VG.Proof.Dsa.Generation.probablePrime_suffix hres).length_le
    rw [List.length_drop, hwl] at this; exact this
  let x : BitVec 64 := BitVec.ofNat 64 (G.randLen - u - rest.length)
  let st0 : BitVec 64 := BitVec.ofNat 64 (Proof.Dsa.ProbablePrime.status (some (b, rest)))
  let c6 : Cfg := ({ c with cl := cl' }.setV fUsedOut x).setV fRes st0
  obtain v88 : c6.V fUsedOut = x := by
    show upd (upd c.V fUsedOut x) fRes st0 fUsedOut = x; rw [upd_ne _ _ (by decide), upd_self]
  obtain vU : c6.V fUsed = BitVec.ofNat 64 u := by
    show upd (upd c.V fUsedOut x) fRes st0 fUsed = _; rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), hUv]
  refine VP.pub (SS.pub (c := fun _ => c6) fun σ s h => h.1.1.1) []
    ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6])
      (.block [ld .t3 fUsedOut, ld .t4 fUsed, .add .t4 .t4 .t3, st .t4 fUsed]), by kernel_rfl⟩
    (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨⟨⟨h, xx⟩, _⟩, _⟩ => ?_
  change SS G STK0 σ c6 s at h
  refine h.ldK (o := fUsedOut) (by decide) (by decide) ((h.gi.slotV (by simp [c6])).trans v88) (t := .t3)
    (by decide) fun s₁ h₁ u₁ => ?_
  refine h₁.ldK (o := fUsed) (by decide) (by decide) ((h₁.gi.slotV (by simp [c6, hU])).trans vU) (t := .t4)
    (by decide) fun s₂ h₂ u₂ => ?_
  refine wp_add fun s₃ u₃ => ?_
  obtain h₃ := h₂.of_upd u₃ (by decide)
  refine h₃.stF varOk_fUsed fun t ht _ => WP.block_nil ⟨?_, xx⟩
  obtain v4 : s₃.gpr .t4 = BitVec.ofNat 64 (G.randLen - rest.length) := by
    rw [u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.gpr]
    show BitVec.ofNat 64 u + BitVec.ofNat 64 (G.randLen - u - rest.length) = _
    rw [← BitVec.ofNat_add, show u + (G.randLen - u - rest.length) = G.randLen - rest.length by omega]
  rw [v4] at ht
  refine ht.mono (fun o ho => ?_) (fun x hx => hx) (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩)
  simp only [testCfg, c6, Cfg.setV, List.mem_cons] at ho ⊢
  rcases ho with rfl | rfl | ho
  · exact ⟨by simp, by simp [upd]⟩
  · refine ⟨by simp, ?_⟩
    simp only [upd, show fRes ≠ fUsed by decide, ite_false, ite_true]
    cases b <;> rfl
  · refine ⟨by simp [ho], ?_⟩
    obtain n88 : o ≠ fUsedOut := fun e => hU88 (e ▸ ho)
    obtain e : st0 = BitVec.ofNat 64 (if b then 1 else 2) := by cases b <;> rfl
    simp only [upd, n88, ite_false, e]

/-! ## The test -/

theorem wB_facts {L : Nat} (hL : L = 128 ∨ L = 256 ∨ L = 384) :
    hEnd ≤ wB L ∧ wB L / 4096 < 8 ∧ wB L % 4096 = 0 := by
  rcases hL with rfl | rfl | rfl <;> decide

/-- `ClOk` of a claim at `o + 0` past `wB`, stated with `o` a variable so
that no one checks `wB pLen + 0 ≡ wB pLen` by unfolding `wB`. -/
theorem clOk_w0 {o : Nat} {l : List Byte} (h1 : hEnd ≤ o) (h2 : wB G.pLen ≤ o) (h3 : o + l.length ≤ G.scrLen * 8) :
    ClOk G (o + 0, l) :=
  ⟨h1, .inr h2, h3⟩

theorem clOk_rep0 {o n : Nat} (h1 : hEnd ≤ o) (h2 : wB G.pLen ≤ o) (h3 : o + n ≤ G.scrLen * 8) :
    ClOk G (o + 0, List.replicate n 0) :=
  clOk_w0 h1 h2 (by simp only [List.length_replicate]; exact h3)

theorem cert_big (x o n : Nat) :
    (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s6])
      (.block (([scr .a0 x] : List Instr) ++ (scrB .a1 o ++ ([.addi .a1 .a1 0] : List Instr)) ++ ([.li .a2 n] : List Instr)))
      (VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6])
        (.block (([scr .a0 x] : List Instr) ++ (scrB .a1 o ++ ([.addi .a1 .a1 0] : List Instr)) ++
          ([.li .a2 n] : List Instr))))).isSome = true := by
  kernel_rfl

theorem St.c0 {σ s : State} {n : Nat} (hn : n < 2048) (h : St G c X σ s) :
    wB G.pLen + n ≤ G.scrLen * 8 ∧ n ≤ 256 * G.pLen ∧ hEnd ≤ wB G.pLen ∧ kB G.pLen ≤ wB G.pLen ∧
      G.scr.toNat + G.scrLen * 8 ≤ 2 ^ 64 := by
  obtain h1 := h.1.gi.wBig; have h3 := h.1.gi.kBig; have h4 := h.1.gi.scrFit; have h5 := h.1.lens
  exact ⟨by omega, by omega, (wB_facts h.1.lens).1, by omega, by omega⟩

/-- The stage after copying the candidate `cb` to byte 0 of the working space
of the functions we call. -/
abbrev candCfg (G : GP) (c : Cfg) (cb : List Byte) : Cfg :=
  { c with cl := (wB G.pLen + 0, cb) :: c.cl.filter fun x => decide (Apart (wB G.pLen + 0) cb.length x) }

/-- The test of the candidate at `src` (`cb`), copied to the test's working
space, with the tape from `fUsed`: its result in `fRes` and the octets it
read in `fUsed`. -/
theorem test_vp {L : Impl.Dsa.ProbablePrime.Layout} {code : Prog isa} {name : String} {u src : Nat}
    {cb : List Byte} {cl' : Claims} (ok : PrimeOk L code) (hc0 : L.candidate = 0) (hu : u ≤ G.randLen)
    (hU : fUsed ∈ c.LS) (hUv : c.V fUsed = BitVec.ofNat 64 u) (hwl : G.randB.length = G.randLen)
    (hsize : L.size ≤ 256 * G.pLen) (hL : ∀ r ∈ L.scratch, r.1 + r.2 ≤ 256 * G.pLen)
    (hsrc : (src, cb) ∈ c.cl) (hsrcK : src + cb.length ≤ kB G.pLen) (hcbl : cb.length = L.bits / 8)
    (hn0 : 0 < cb.length) (hn2 : cb.length < 2048) (hs2 : src < 2048) (hodd : Spec.Dsa.decodeBE cb % 2 = 1)
    (hbl : Spec.Dsa.bitLength (Spec.Dsa.decodeBE cb) = L.bits)
    (hU' : ∀ o ∈ c.LS, fUsedOut + 8 ≤ o ∨ o + 8 ≤ fUsedOut) (hU88 : fUsedOut ∉ c.LS)
    (hcl : ∀ x ∈ cl', x ∈ (candCfg G c cb).cl ∧ ∀ r ∈ L.scratch, Apart (wB G.pLen + r.1) r.2 x) :
    VP (St G c X) (test G.pLen src cb.length name code)
      (St G (testCfg c cl' G.randLen (tRes G cb u)) X) := by
  obtain hc0' : ∀ σ s, St G c X σ s → wB G.pLen + cb.length ≤ G.scrLen * 8 ∧ cb.length ≤ 256 * G.pLen ∧
      hEnd ≤ wB G.pLen ∧ kB G.pLen ≤ wB G.pLen ∧ G.scr.toNat + G.scrLen * 8 ≤ 2 ^ 64 :=
    fun σ s h => St.c0 hn2 h
  obtain wl : ∀ σ s, St G c X σ s → wB G.pLen / 4096 < 8 ∧ wB G.pLen % 4096 = 0 := fun σ s ⟨h, _⟩ =>
    (wB_facts h.lens).2
  simp only [test, Impl.Rsa.RISCV64.Keys.seqs]
  refine VP.seq (G := St G (candCfg G c cb) X) (copyN_vp (c := fun _ => c) (o := wB G.pLen + 0) (S := G.sa src)
    (fun σ s h => h.1) hn0 (by omega) (cert_big _ _ _)
    (fun σ s hs => pro_scr_big (c := fun _ => c) (fun σ s h => h.1) hs2 (wl σ s hs).2 (wl σ s hs).1 (by decide)
      hn2 σ s hs)
    (fun σ s h => by
      obtain ⟨k1, _, k3, _, _⟩ := hc0' σ s h
      exact clOk_rep0 k3 (Nat.le_refl _) k1)
    (fun σ s h => by
      have gi := h.1.gi
      obtain sS := (h.1.clOk _ hsrc).2.2
      obtain ⟨k1, _, _, k4, _⟩ := hc0' σ s h
      refine ⟨fun i hi => by rw [GP.sa_add]; exact gi.inRdWr (o := src + i) (n := 1) (by omega), ?_⟩
      exact Offset.sep _ (.inr (by omega)) (by omega) (by omega))
    fun σ s t ⟨h, x⟩ h' _ b => ⟨?_, x⟩) ?_
  · refine ⟨h'.gi, h'.sb.cons (by rw [b]; have := h.sb _ hsrc; rw [this]), fun y hy => ?_, h'.arrs, h'.liveOk,
      h'.ksl, h'.kslOk⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · obtain ⟨k1, _, k3, _, _⟩ := hc0' σ s ⟨h, x⟩
      exact clOk_w0 k3 (Nat.le_refl _) k1
    · exact h'.clOk y hy
  obtain hcb : (wB G.pLen + L.candidate, cb) ∈ (candCfg G c cb).cl := by rw [hc0]; exact List.mem_cons_self
  refine VP.assoc (VP.seq (targs_vp (c := candCfg G c cb) hu hU hUv)
    (VP.seq (primeCall_vp (c := candCfg G c cb) (cl' := cl') (name := name) ok hu hsize hL
      hcb hcbl hodd hbl hU' hcl)
      (VP.seq testRes_vp (testTail_vp (c := candCfg G c cb) hU hUv hU88 hwl hu))))

end

end VG.Proof.Dsa.RISCV64.PSearch
