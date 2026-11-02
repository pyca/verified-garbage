module

import Mathlib.Tactic.ClearExcept

import VerifiedGarbage.Proof.Dsa.Arm.Gen.KSStore
public import VerifiedGarbage.Proof.Dsa.Arm.PowVerified
public import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Test
public import VerifiedGarbage.Proof.Rsa.Arm.CvLoad
public import VerifiedGarbage.Proof.Rsa.Arm.DivContext
public import VerifiedGarbage.Proof.Rsa.Arm.KeyBits
import VerifiedGarbage.Proof.Dsa.Arm.Gen.Bytes
import VerifiedGarbage.Proof.Dsa.Arm.Gen.CT
public import VerifiedGarbage.Proof.Rsa.Arm.RvVP

/-! # DSA parameter generation on ARMv7: the exponentiation

`powCall_vp`: `vg_dsa_pow_{n}_{e}` (`Impl/Dsa/Arm/Pow.lean`) called on the
working space at `sA`, under its contract on ARM (`Proof.Dsa.Arm.Pow.powArm`):
the number at its result is the base to the exponent modulo the modulus.
`PowOk n e code`: a verified exponentiation that uses no more stack than
the frame leaves below it.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm
open VG.Impl.Dsa.Arm.Generation
open VG.Impl.Mont.Arm.Dynamic (modS baseS expS resS contextBytes)
open VG.Proof.X25519.Arm (Rest Upd wp_movw)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Arm.FrameStack (armStack belowA)

/-- A verified exponentiation. -/
structure PowOk (n e : Nat) (code : Prog isa) : Prop where
  correct : ∀ s, (Proof.Dsa.Arm.Pow.powArm n e).pre s →
    ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ (Proof.Dsa.Arm.Pow.powArm n e).post s s'
  ct : ConstantTime isa (Proof.Dsa.Arm.Pow.powArm n e).pre (Proof.Dsa.Arm.Pow.powArm n e).pub code
  stack : armStack code ≤ 176

/-- The exponentiation's numbers in its working space at `sA`. -/
abbrev PowIn (G : GP) (n e pv hv ev : Nat) (m : Mem) : Prop :=
  (m.read (G.sa (sA + modS n)) (8 * n)).toNat = pv ∧ (m.read (G.sa (sA + baseS n)) (8 * n)).toNat = hv ∧
    (m.read (G.sa (sA + expS n)) (4 * e)).toNat = ev

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- The working space's region. -/
abbrev GP.rPow (G : GP) : Region := ⟨G.sa sA, wa G.pLen / 8 * 8⟩

theorem powCall_vp {L n e : Nat} {name : String} {code : Prog isa} (ok : PowOk n e code) (hL : L = G.pLen)
    (hctx : contextBytes n ≤ wa G.pLen) {pv hv ev : Nat} (hodd : pv % 2 = 1) (hgt : 1 < pv) {cl' : Claims}
    (hcl : ∀ x ∈ cl', x ∈ c.cl ∧ Apart sA (wa G.pLen) x) :
    VP (fun σ s => St G c X σ s ∧ PowIn G n e pv hv ev s.mem)
      (.seq (.block (scr L .r0 sA ++ ([.movw .r1 (BitVec.ofNat 16 (wa L / 8))] : List Instr))) (.call name code))
      (fun σ t => St G { c with cl := cl' } X σ t ∧
        (t.mem.read (G.sa (sA + resS n)) (8 * n)).toNat = hv ^ ev % pv) := by
  subst hL
  have w8 : wa G.pLen / 8 * 8 = wa G.pLen := by simp only [wa]; omega_arith
  refine VP.seq (G := fun σ s => (St G c X σ s ∧ PowIn G n e pv hv ev s.mem) ∧
      s.gpr .r0 = G.scr + BitVec.ofNat 32 sA ∧ s.gpr .r1 = BitVec.ofNat 32 (wa G.pLen / 8))
    (VP.taint [.r8] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r8])
      (.block (scr 128 .r0 sA ++ [.movw .r1 (BitVec.ofNat 16 2)])), rfl⟩
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.1.r8, h₂.1.1.r8])
      fun σ s ⟨⟨h, x⟩, pin⟩ => ?_) ?_
  · have big := h.gi.scrBig
    have l := h.lens
    refine scr_ok (d := .r0) (o := sA) h.r8 rfl l (by simp only [sK]; omega_arith) fun s₁ v₁ R₁ M₁ =>
      wp_movw fun s₂ u₂ => WP.block_nil ⟨⟨⟨h.of_rest ((R₁.mono (by simp)).trans (u₂.rest (by simp)) :
        Rest [.r12, .r0, .r1] s s₂) (by rw [u₂.mem, M₁]), x⟩, by rw [u₂.mem, M₁]; exact pin⟩,
        by rw [u₂.other _ (by decide), v₁], ?_⟩
    rw [u₂.gpr]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have : wa G.pLen / 8 < 2 ^ 16 := by simp only [wa]; omega_arith
    omega_arith
  -- The call, from the working space and its length.
  have facts : ∀ σ s, (St G c X σ s ∧ PowIn G n e pv hv ev s.mem) ∧ s.gpr .r0 = G.scr + BitVec.ofNat 32 sA ∧
      s.gpr .r1 = BitVec.ofNat 32 (wa G.pLen / 8) →
      (Proof.Dsa.Arm.Pow.powArm n e).pre (s.callEntry.withRegions [] [G.rPow]) ∧
      Covers ([] ++ [G.rPow]) (s.rd ++ s.wr) ∧ Covers [G.rPow] s.wr ∧ armStack code ≤ s.sp.toNat ∧
      State.addr (s.gpr .r0) = G.sa sA ∧ ((s.gpr .r1).toNat = wa G.pLen / 8) := fun σ s ⟨⟨⟨h, _⟩, pin⟩, r0, r1⟩ => by
    have gi := h.gi
    have big := gi.scrBig
    have fit := gi.scrFit
    have kz0 : 0 < kz G.pLen := by simp only [kz]; omega_arith
    have l := h.lens
    have aS : State.addr (G.scr + BitVec.ofNat 32 sA) = G.sa sA := h.addr (n := wa G.pLen)
      (by simp only [sK] at big ⊢; omega_arith) (by simp only [wa]; omega_arith)
    have r1n : (s.gpr .r1).toNat = wa G.pLen / 8 := by
      rw [r1, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by simp only [wa]; omega_arith)
    have inS : G.rScr ∈ s.wr := by rw [gi.wr, gi.pre.wr, gi.hG]; simp
    have cov : Covers [G.rPow] s.wr := (Covers.of_sub (rs' := [G.rScr]) fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact ⟨G.rScr, List.mem_singleton_self _, sA, rfl, show sA + wa G.pLen / 8 * 8 ≤ G.scrLen * 8 by
        simp only [sK] at big; omega_arith⟩).trans
      (Covers.of_mem fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact inS)
    have e0 : ∀ o, State.addr (s.gpr .r0) + BitVec.ofNat 64 o = G.sa (sA + o) := fun o => by
      rw [r0, aS]; simp only [GP.sa]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    refine ⟨⟨rfl, ?_, ?_, ?_, ?_, ?_⟩, Covers.right cov, cov, ?_, by rw [r0, aS], r1n⟩
    · show [G.rPow] = [⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat * 8⟩]
      rw [r0, aS, r1n]
    · show (s.gpr .r0).toNat + (s.gpr .r1).toNat * 8 ≤ 2 ^ 32
      rw [r1n, r0, h.toNat (by simp only [sK]; omega_arith)]; simp only [sK] at big; omega_arith
    · show contextBytes n ≤ 8 * (s.gpr .r1).toNat
      rw [r1n]; omega_arith
    · show Proof.Dsa.ModPow.numAt s.mem (State.addr (s.gpr .r0)) (modS n) (8 * n) % 2 = 1
      rw [Proof.Dsa.ModPow.numAt, e0, pin.1]; exact hodd
    · show 1 < Proof.Dsa.ModPow.numAt s.mem (State.addr (s.gpr .r0)) (modS n) (8 * n)
      rw [Proof.Dsa.ModPow.numAt, e0, pin.1]; exact hgt
    · rw [gi.sp]; have := gi.sp176; have := ok.stack; omega_arith
  refine VP.of_ct (fun σ₁ σ₂ => RelCT.call ok.correct ok.ct [] [G.rPow] fun s₁ s₂ ⟨h₁, h₂⟩ => ?_)
    fun σ s hs => ?_
  · obtain ⟨p₁, c₁, w₁, -, -, -⟩ := facts _ _ h₁
    obtain ⟨p₂, c₂, w₂, -, -, -⟩ := facts _ _ h₂
    refine ⟨p₁, p₂, ⟨?_, ?_, ?_⟩, c₁, w₁, c₂, w₂⟩
    · show s₁.sp = s₂.sp
      rw [h₁.1.1.1.gi.sp, h₂.1.1.1.gi.sp]
    · show s₁.callEntry.gpr .r0 = s₂.callEntry.gpr .r0
      rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), h₁.2.1, h₂.2.1]
    · show s₁.callEntry.gpr .r1 = s₂.callEntry.gpr .r1
      rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), h₁.2.2, h₂.2.2]
  obtain ⟨pre, hc, hw, hd, a0, r1n⟩ := facts σ s hs
  obtain ⟨⟨⟨h, x⟩, pin⟩, r0, r1⟩ := hs
  refine FrameStack.WP.callF ok.correct pre hc hw hd fun s' hrd hwr hsp f hpres hpost => ?_
  have gi := h.gi
  have big := gi.scrBig
  have l := h.lens
  have R : Rest [.r0, .r1, .r2, .r3, .r12, .lr] s s' := ⟨fun r hr => by
    refine hpres r ?_ ?_ <;> clear * - hr <;> cases r <;> simp_all [preserved], hrd, hwr, hsp⟩
  have bl : Region.Sub (belowA s.sp (armStack code)) G.rBelow := by
    have := gi.sp176; have := ok.stack
    refine fun a ha => ?_
    have hs' := FrameStack.belowA_sub (sp := s.sp) (a := armStack code) (b := 176) (by omega_arith)
      (by rw [gi.sp]; omega_arith) a ha
    rw [gi.sp] at hs'
    show Region.Contains ⟨State.addr G.sp - 176#64, 176⟩ a 1
    have e : State.addr (G.sp - BitVec.ofNat 32 176) = State.addr G.sp - 176#64 := FrameStack.addr_sub' (by omega_arith)
    simpa only [FrameStack.belowA, e] using hs'
  refine ⟨⟨h.of_scr R (o := sA) (n := wa G.pLen) (by simp only [sK]; omega_arith)
    (f.sub fun r hr => ?_) fun y hy => .inl (hcl y hy), x⟩, ?_⟩
  · simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact ⟨G.rs sA (wa G.pLen), List.mem_cons_self, by rw [GP.rPow, w8]; exact fun _ h => h⟩
    · exact ⟨G.rBelow, by simp, bl⟩
  · obtain ⟨v, -⟩ := hpost
    simp only [Proof.Dsa.ModPow.numAt, State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem,
      State.callEntry_gpr _ (show Reg.r0 ∉ linkRegs by decide)] at v
    have e0 : ∀ o, State.addr (s.gpr .r0) + BitVec.ofNat 64 o = G.sa (sA + o) := fun o => by
      rw [a0]; simp only [GP.sa]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [e0, e0, e0, e0, pin.1, pin.2.1, pin.2.2] at v
    exact v

end

end VG.Proof.Dsa.Arm.Gen
