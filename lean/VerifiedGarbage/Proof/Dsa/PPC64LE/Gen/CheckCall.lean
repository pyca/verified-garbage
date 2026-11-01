module

import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Test
public import VerifiedGarbage.Spec.Dsa.Derive
public import VerifiedGarbage.Proof.Dsa.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.St
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.Inline
public import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
public import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract

/-! # DSA parameter generation on PPC64LE: calling the domain check

`CheckOk code`: a verified `vg_dsa_check_parameters`, which uses at most 176
bytes of stack. `checkCall_vp`: its call on p‖q‖g at `sPacked`, with the
working space of the tests (`wB`) as its scratch: its verdict in `r3`'s low
half, and `scratch` changed only in that working space.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation

/-- A verified domain check, with the stack it uses. -/
structure CheckOk (code : Prog isa) : Prop where
  verified : Verified target code (Proof.Dsa.checkParametersContract abi)
  stack : sdepth code ≤ 176

/-- The check's contract. -/
abbrev checkK : Contract isa := Proof.Dsa.checkParametersContract abi

/-- The precondition, as facts. -/
structure CkIn (s : State) : Prop where
  spLo : 176 ≤ s.sp.toNat
  rd : s.rd = [⟨s.gpr .r3, (s.gpr .r4).toNat⟩]
  wr : s.wr = [⟨s.gpr .r7, (s.gpr .r8).toNat * 8⟩]
  rW : Region.Disjoint ⟨s.gpr .r3, (s.gpr .r4).toNat⟩ ⟨s.gpr .r7, (s.gpr .r8).toNat * 8⟩
  bR : Region.Disjoint ⟨s.sp - 176#64, 176⟩ ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
  bW : Region.Disjoint ⟨s.sp - 176#64, 176⟩ ⟨s.gpr .r7, (s.gpr .r8).toNat * 8⟩
  fr : (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64
  fw : (s.gpr .r7).toNat + (s.gpr .r8).toNat * 8 ≤ 2 ^ 64
  lens : Spec.Dsa.lengthsValid (s.gpr .r5).toNat (s.gpr .r6).toNat
  len : (s.gpr .r4).toNat = 2 * (s.gpr .r5).toNat + (s.gpr .r6).toNat
  words : Spec.Dsa.scratchWords (s.gpr .r5).toNat ≤ (s.gpr .r8).toNat

theorem pre_of_ckin {s : State} (h : CkIn s) : checkK.pre s := by
  sig_pre [checkK, Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argRegs]
  exact ⟨h.rd, h.wr, h.rW, h.fr, h.fw, h.lens, h.len, h.words⟩

/-- The verdict on the parameters at `r3`. -/
abbrev ckRes (s : State) : Bool :=
  Spec.Dsa.checkParametersBytes (s.gpr .r5).toNat (s.gpr .r6).toNat
    (Spec.Rsa.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat)

theorem cpost_of_post {s t : State} (h : checkK.post s t) :
    ((t.gpr .r3).setWidth 32).toNat = if ckRes s = true then 1 else 0 := by
  sig_post [checkK, Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argRegs] at h
  exact h

/-- Two calls with the same arguments and parameters. -/
theorem cpub_of {s t : State} (sp : s.sp = t.sp) (p3 : s.gpr .r3 = t.gpr .r3) (p4 : s.gpr .r4 = t.gpr .r4)
    (p5 : s.gpr .r5 = t.gpr .r5) (p6 : s.gpr .r6 = t.gpr .r6) (p7 : s.gpr .r7 = t.gpr .r7)
    (p8 : s.gpr .r8 = t.gpr .r8)
    (hb : Spec.Rsa.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat = Spec.Rsa.bytesAt t.mem (t.gpr .r3) (t.gpr .r4).toNat) :
    checkK.pub s t := by
  sig_pub [checkK, Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argRegs]
  exact ⟨sp, by rw [hb], p3, p4, p5, p6, p7, p8⟩

/-! ## The call -/

/-- The bytes of p‖q‖g. -/
abbrev nPk (G : GP) : Nat := 2 * G.pLen + G.qLen

/-- The check's arguments, in `r3`–`r8`. -/
abbrev CArgs (G : GP) (s : State) : Prop :=
  s.gpr .r3 = G.sa sPacked ∧ s.gpr .r4 = BitVec.ofNat 64 (nPk G) ∧ s.gpr .r5 = BitVec.ofNat 64 G.pLen ∧
    s.gpr .r6 = BitVec.ofNat 64 G.qLen ∧ s.gpr .r7 = G.sa (wB G.pLen) ∧
    s.gpr .r8 = BitVec.ofNat 64 (wWords G.pLen)

/-- The regions the check is given. -/
abbrev cRd (G : GP) : List Region := [⟨G.sa sPacked, (BitVec.ofNat 64 (nPk G)).toNat⟩]
abbrev cWr (G : GP) : List Region := [⟨G.sa (wB G.pLen), (BitVec.ofNat 64 (wWords G.pLen)).toNat * 8⟩]

/-- The check's entry. -/
abbrev cEntry (G : GP) (s : State) : State := s.callEntry.withRegions (cRd G) (cWr G)

section
variable {G : GP} {σ s : State} {c : Cfg}

theorem cEntry_gpr {r : Reg} (hr : r ∈ [Reg.r3, .r4, .r5, .r6, .r7, .r8]) : (cEntry G s).gpr r = s.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]

/-- The sizes of the check's arguments. -/
theorem ck_sizes (hl : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32)) :
    sPacked + nPk G ≤ wB G.pLen ∧ wWords G.pLen < 2 ^ 15 ∧ 0 < wWords G.pLen ∧
      Spec.Dsa.scratchWords G.pLen ≤ wWords G.pLen ∧ Spec.Dsa.lengthsValid G.pLen G.qLen ∧ hEnd ≤ sPacked ∧
      nPk G < 2 ^ 15 := by
  rcases hl with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> simp only [nPk, e1, e2] <;> decide

/-- The check's arguments meet its precondition. -/
theorem SS.cEntry_ckin (h : SS G 176 σ c s) (regs : CArgs G s) : CkIn (cEntry G s) := by
  have gi := h.gi
  have big := gi.wBig
  have fit := gi.scrFit
  obtain ⟨hsz, w15, wp, ws, lv, _⟩ := ck_sizes gi.lens
  have hp15 : G.pLen < 2 ^ 15 := by rcases gi.lens3 with e | e | e <;> rw [e] <;> decide
  have hq15 : G.qLen < 2 ^ 15 := by rcases gi.lens with ⟨_, e⟩ | ⟨_, e⟩ | ⟨_, e⟩ <;> rw [e] <;> decide
  obtain ⟨r3, r4, r5, r6, r7, r8⟩ := regs
  have e4 : (BitVec.ofNat 64 (nPk G)).toNat = nPk G := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simp only [nPk]; omega)]
  have e5 : (BitVec.ofNat 64 G.pLen).toNat = G.pLen := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have e6 : (BitVec.ofNat 64 G.qLen).toNat = G.qLen := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have e8 : (BitVec.ofNat 64 (wWords G.pLen)).toNat = wWords G.pLen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have W8 : wB G.pLen + wWords G.pLen * 8 ≤ G.scrLen * 8 := by omega
  have P8 : sPacked + nPk G ≤ G.scrLen * 8 := by omega
  have hbS : (rBelow σ 176).Disjoint G.rScr := by have := gi.pre.bC; rw [gi.hG] at this; exact this
  have sp : (cEntry G s).sp = σ.sp := by rw [State.withRegions_sp, State.callEntry_sp, gi.sp]
  have g := fun r hr => cEntry_gpr (G := G) (s := s) (r := r) hr
  have fitS : ∀ o, o < G.scrLen * 8 → (G.sa o).toNat = G.scr.toNat + o := fun o ho => by
    show (G.scr + BitVec.ofNat 64 o).toNat = _
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega), Nat.mod_eq_of_lt (by omega)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sp]; exact gi.pre.spLo
  · rw [State.withRegions_rd, g .r3 (by simp), g .r4 (by simp), r3, r4]
  · rw [State.withRegions_wr, g .r7 (by simp), g .r8 (by simp), r7, r8]
  · rw [g .r3 (by simp), g .r4 (by simp), g .r7 (by simp), g .r8 (by simp), r3, r4, r7, r8, e4, e8]
    exact gi.sdisj (.inl hsz) P8 W8
  · rw [sp, g .r3 (by simp), g .r4 (by simp), r3, r4, e4]; exact hbS.sub_right (sw G P8)
  · rw [sp, g .r7 (by simp), g .r8 (by simp), r7, r8, e8]; exact hbS.sub_right (sw G W8)
  · rw [g .r3 (by simp), g .r4 (by simp), r3, r4, e4, fitS _ (by omega)]; omega
  · rw [g .r7 (by simp), g .r8 (by simp), r7, r8, e8, fitS _ (by omega)]; omega
  · rw [g .r5 (by simp), g .r6 (by simp), r5, r6, e5, e6]; exact lv
  · rw [g .r4 (by simp), g .r5 (by simp), g .r6 (by simp), r4, r5, r6, e4, e5, e6]
  · rw [g .r5 (by simp), g .r8 (by simp), r5, r8, e5, e8]; exact ws

/-- The check's regions are the search's. -/
theorem SS.cCovers (h : SS G 176 σ c s) : Covers (cRd G ++ cWr G) (s.rd ++ s.wr) ∧ Covers (cWr G) s.wr := by
  have gi := h.gi
  have big := gi.wBig
  obtain ⟨hsz, w15, _, _, _, _, n15⟩ := ck_sizes gi.lens
  have e4 : (BitVec.ofNat 64 (nPk G)).toNat = nPk G := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have e8 : (BitVec.ofNat 64 (wWords G.pLen)).toNat = wWords G.pLen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have inS : G.rScr ∈ s.wr := by rw [gi.wr, gi.pre.wr, gi.hG]; simp
  have cw : Covers (cWr G) s.wr := (Covers.of_sub (rs' := [G.rScr]) fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact ⟨G.rScr, List.mem_singleton_self _, wB G.pLen, rfl,
      show wB G.pLen + (BitVec.ofNat 64 (wWords G.pLen)).toNat * 8 ≤ G.scrLen * 8 by rw [e8]; omega⟩).trans
    (Covers.of_mem fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact inS)
  have cr : Covers (cRd G) s.wr := (Covers.of_sub (rs' := [G.rScr]) fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact ⟨G.rScr, List.mem_singleton_self _, sPacked, rfl,
      show sPacked + (BitVec.ofNat 64 (nPk G)).toNat ≤ G.scrLen * 8 by rw [e4]; omega⟩).trans
    (Covers.of_mem fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact inS)
  exact ⟨Covers.append_left (cr.right) (cw.right), cw⟩

/-- The call of the check on the parameters `pk` at `sPacked`: its verdict
in `r3`'s low half, and memory changed only in the tests' working space and
the stack. -/
theorem SS.checkCall_ok {code : Prog isa} {name : String} (ok : CheckOk code) (h : SS G 176 σ c s)
    (regs : CArgs G s) {pk : List Byte} (hpk : Spec.Rsa.bytesAt s.mem (G.sa sPacked) (nPk G) = pk)
    {Q : State → Prop}
    (k : ∀ t, (∀ r ∈ preserved, t.gpr r = s.gpr r) → t.rd = s.rd → t.wr = s.wr → t.sp = s.sp →
      Frame [G.rs (wB G.pLen) (wWords G.pLen * 8), rBelow σ 176] s.mem t.mem →
      ((t.gpr .r3).setWidth 32).toNat = (if Spec.Dsa.checkParametersBytes G.pLen G.qLen pk then 1 else 0) → Q t) :
    WP isa (.call name code) s Q := by
  have gi := h.gi
  obtain ⟨_, w15, _⟩ := ck_sizes gi.lens
  have hp15 : G.pLen < 2 ^ 15 := by rcases gi.lens3 with e | e | e <;> rw [e] <;> decide
  have hq15 : G.qLen < 2 ^ 15 := by rcases gi.lens with ⟨_, e⟩ | ⟨_, e⟩ | ⟨_, e⟩ <;> rw [e] <;> decide
  have pin := h.cEntry_ckin regs
  obtain ⟨r3, r4, r5, r6, r7, r8⟩ := regs
  have e4 : (BitVec.ofNat 64 (nPk G)).toNat = nPk G := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simp only [nPk]; omega)]
  have e8 : (BitVec.ofNat 64 (wWords G.pLen)).toNat = wWords G.pLen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨hc, hw⟩ := h.cCovers
  refine WP.callAny ok.verified.1 (pre_of_ckin pin) hc hw (fun t rd wr sp f g post => ?_) (by have := ok.stack; omega)
  have st := cpost_of_post post
  have hres : ckRes (cEntry G s) = Spec.Dsa.checkParametersBytes G.pLen G.qLen pk := by
    simp only [ckRes, State.withRegions_mem, State.callEntry_mem]
    rw [cEntry_gpr (by simp), cEntry_gpr (by simp), cEntry_gpr (by simp), cEntry_gpr (by simp), r3, r4, r5, r6, e4,
      hpk, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  refine k t g rd wr sp ?_ ?_
  · refine f.sub fun x hx => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ⟨G.rs (wB G.pLen) (wWords G.pLen * 8), by simp, by rw [e8]; exact fun _ h => h⟩
    · refine ⟨rBelow σ 176, by simp, ?_⟩
      have := ok.stack
      rw [gi.sp]
      exact Offset.sub_below _ (by omega) (by omega)
  · rw [State.withRegions_gpr] at st; rw [st, hres]

end

end VG.Proof.Dsa.PPC64LE.Gen
