module

public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Frame
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Out
public import VerifiedGarbage.Spec.RsaKeyGen.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem

/-!
# A candidate on PPC64LE: the results

`cOp s0`: what the contract asks of the call from `s0`, `CQ`: its results.
`Ctx`: the body's state with `out` still zero; `fin_ok`, `finNone_post`,
`finPrime_post`: each way the body ends gives the contract's results.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.RsaKeyGen.PPC64LE.Candidate (finish finNone finPrime)

/-- `out_len`. -/
abbrev oL (s0 : State) : Nat := (s0.gpr .r4).toNat

/-- `rand_len`. -/
abbrev rL (s0 : State) : Nat := (PPC64LE.stackArg s0 0).toNat

/-- `e`'s octets. -/
abbrev eB (s0 : State) : List Byte := Spec.Rsa.bytesAt s0.mem (s0.gpr .r6) (s0.gpr .r7).toNat

/-- `p`'s octets. -/
abbrev pB (s0 : State) : List Byte := Spec.Rsa.bytesAt s0.mem (s0.gpr .r8) (s0.gpr .r9).toNat

/-- `rand`'s octets. -/
abbrev rB (s0 : State) : List Byte := Spec.Rsa.bytesAt s0.mem (s0.gpr .r10) (rL s0)

/-- What the call computes. -/
def cOp (s0 : State) : Option (Spec.RsaKeyGen.Candidate × Spec.RsaKeyGen.Rand) :=
  Spec.RsaKeyGen.candidateOp (oL s0) (Spec.Rsa.bytesAt s0.mem (s0.gpr .r6) (s0.gpr .r7).toNat)
    (Spec.Rsa.bytesAt s0.mem (s0.gpr .r8) (s0.gpr .r9).toNat) (Spec.Rsa.bytesAt s0.mem (s0.gpr .r10) (rL s0))

/-- What `out` holds at the end. -/
def outOf (s0 : State) : List Byte :=
  match cOp s0 with
  | some (.prime c, _) => Spec.Rsa.i2osp c (oL s0)
  | _ => List.replicate (oL s0) 0

/-- What `used` holds at the end. -/
def usedOf (s0 : State) : Nat :=
  match cOp s0 with
  | some (_, rest) => rL s0 - rest.length
  | none => 0

/-- The contract's results. -/
def CQ (s0 : State) (r : BitVec 64) (m : Mem) : Prop :=
  r.toNat = Spec.RsaKeyGen.candidateStatus (cOp s0) ∧ Spec.Rsa.bytesAt m (s0.gpr .r3) (oL s0) = outOf s0 ∧
    Spec.Rsa.wordsAt m (s0.gpr .r5) 1 = [BitVec.ofNat 64 (usedOf s0)]

/-- The body's state, `out` still zero. -/
structure Ctx (s0 s : State) : Prop where
  bx : Bx s0 s
  r23 : s.gpr .r23 = s0.gpr .r3
  r24 : s.gpr .r24 = s0.gpr .r4
  r25 : s.gpr .r25 = s0.gpr .r5
  zero : Spec.Rsa.bytesAt s.mem (s0.gpr .r3) (oL s0) = List.replicate (oL s0) 0

theorem oL_lt {s0 : State} (hp : CIn s0) : oL s0 ≤ 512 := hp.valid.2.1

/-- `Ctx` through code that writes only `scratch` and the stack below the
frame. -/
theorem Ctx.step {s0 s t : State} (h : Ctx s0 s) (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr)
    (f : Frame [cS s0, below (off (cB s0) 176) 176] s.mem t.mem) (r2 : t.gpr .r2 = s.gpr .r2)
    (r23 : t.gpr .r23 = s.gpr .r23) (r24 : t.gpr .r24 = s.gpr .r24) (r25 : t.gpr .r25 = s.gpr .r25) :
    Ctx s0 t := by
  have hp := h.bx.pre
  have hf := cB_fit hp
  have bF : below (off (cB s0) 176) 176 = ⟨cB s0, 176⟩ := by
    simp only [below, off, BitVec.add_sub_cancel]
  refine ⟨h.bx.step sp rd wr (f.mono (by simp)) r2, r23.trans h.r23, r24.trans h.r24, r25.trans h.r25, ?_⟩
  rw [bytes_keep f (by have := oL_lt hp; omega) (fun ρ hρ => ?_)]
  · exact h.zero
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hρ
  rcases hρ with rfl | rfl
  · exact hp.oS
  · rw [bF]; exact (hp.Fo.sub_left (Region.sub_prefix (by decide))).symm

theorem wordsAt_one (m : Mem) (U : Addr) (v : BitVec 64) : Spec.Rsa.wordsAt (m.writeW U v) U 1 = [v] := by
  simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero,
    Mem.readW_writeW_self64]

/-- The end through `finish k`, `used` from `r28`, `out` still zero. -/
theorem fin_ok (k : Nat) (hk : k < 2 ^ 15) {s0 u : State} (hc : Ctx s0 u)
    (hst : Spec.RsaKeyGen.candidateStatus (cOp s0) = k) (hout : outOf s0 = List.replicate (oL s0) 0)
    (hus : u.gpr .r28 = BitVec.ofNat 64 (usedOf s0)) :
    WP isa (finish k) u fun t => Bx s0 t ∧ CQ s0 (t.gpr .r3) t.mem := by
  have hp := hc.bx.pre
  have hU : InRegions u.wr (s0.gpr .r5) 8 :=
    ⟨cU s0, by rw [hc.bx.wr, bodyWr, hp.wr]; simp, Region.contains_self _ _⟩
  refine WP.mono (finish_ok k hc.r25 hU hk) fun t ⟨⟨tm, t3⟩, kt⟩ => ?_
  have fu : Frame [cU s0] u.mem t.mem := by
    rw [tm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hc.bx.step kt.sp kt.rd kt.wr (fu.mono (by simp)) (kt.gpr _ (by decide)), ?_, ?_, ?_⟩
  · rw [t3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hst]
  · rw [bytes_keep fu (by have := oL_lt hp; omega) (fun ρ hρ => by
      simp only [List.mem_singleton] at hρ; subst hρ; exact hp.oU), hc.zero, hout]
  · rw [tm, hus]; exact wordsAt_one _ _ _

/-- The end through `finNone`, when `rand` is too short. -/
theorem finNone_post {s0 u : State} (hc : Ctx s0 u) (hres : cOp s0 = none) :
    WP isa finNone u fun t => Bx s0 t ∧ CQ s0 (t.gpr .r3) t.mem := by
  have hp := hc.bx.pre
  have hU : InRegions u.wr (s0.gpr .r5) 8 :=
    ⟨cU s0, by rw [hc.bx.wr, bodyWr, hp.wr]; simp, Region.contains_self _ _⟩
  refine WP.mono (finNone_ok hc.r25 hU) fun t ⟨⟨tm, t3, _⟩, kt⟩ => ?_
  have fu : Frame [cU s0] u.mem t.mem := by
    rw [tm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hc.bx.step kt.sp kt.rd kt.wr (fu.mono (by simp)) (kt.gpr _ (by decide)), ?_, ?_, ?_⟩
  · rw [t3, hres]; rfl
  · rw [bytes_keep fu (by have := oL_lt hp; omega) (fun ρ hρ => by
      simp only [List.mem_singleton] at hρ; subst hρ; exact hp.oU), hc.zero, outOf, hres]
  · rw [tm, usedOf, hres]; exact wordsAt_one _ _ _

/-- The end through `finPrime`: the probable prime `c`, of `w` words, from
array 0 to `out`. -/
theorem finPrime_post {s0 u : State} {B : Addr} {Z w c : Nat} {rest : Spec.RsaKeyGen.Rand} (hc : Ctx s0 u)
    (hs : Scr u B Z) (h31 : u.gpr .r31 = B) (hZ : 256 + oL s0 ≤ Z) (hw : oL s0 = 8 * w) (hw1 : 1 ≤ w)
    (hd : (cO s0).Disjoint ⟨B, Z⟩) (hval : val32 u.mem B 256 (2 * w) = c)
    (hres : cOp s0 = some (.prime c, rest)) (hus : u.gpr .r28 = BitVec.ofNat 64 (rL s0 - rest.length)) :
    WP isa finPrime u fun t => Bx s0 t ∧ CQ s0 (t.gpr .r3) t.mem := by
  have hp := hc.bx.pre
  have hfo := hp.fo
  have hnw := hs.nowrap
  have hL := oL_lt hp
  simp only [oL] at hL hZ hw
  have hO : ∀ i < (s0.gpr .r4).toNat, InRegions u.wr (off (s0.gpr .r3) i) 1 := fun i hi =>
    ⟨cO s0, by rw [hc.bx.wr, bodyWr, hp.wr]; simp, Offset.contains_base _ (d := i) (by omega) (by omega)⟩
  have hsep : ∀ i < (s0.gpr .r4).toNat, ∀ x, ofs B x < Z → off (s0.gpr .r3) i ≠ x := fun i hi x hx e => by
    refine hd _ (Offset.contains_base _ (d := i) (by omega) (by omega)) ?_
    show Region.Contains _ (off (s0.gpr .r3) i) 1
    rw [e]; simp only [Region.Contains]; simp only [ofs] at hx; omega
  unfold finPrime
  have cp := copyOut_ok hs h31 hc.r23 (by rw [hc.r24]; simp) (by omega) hZ hO (by omega) hsep
  rw [WP.seq_iff] at cp
  rw [WP.seq_iff]
  refine WP.mono cp fun t₁ h₁ => ?_
  rw [WP.seq_iff]
  refine WP.mono h₁ fun t₂ ⟨hb, ho, k₂⟩ => ?_
  have fo : Frame [cO s0] u.mem t₂.mem := frame_of_outside ho (by omega)
  have b₂ := hc.bx.step k₂.sp k₂.rd k₂.wr (fo.mono (by simp)) (k₂.gpr _ (by decide))
  have hU : InRegions t₂.wr (s0.gpr .r5) 8 :=
    ⟨cU s0, by rw [b₂.wr, bodyWr, hp.wr]; simp, Region.contains_self _ _⟩
  refine WP.mono (finish_ok 1 ((k₂.gpr _ (by decide)).trans hc.r25) hU (by decide)) fun t ⟨⟨tm, t3⟩, kt⟩ => ?_
  have fu : Frame [cU s0] t₂.mem t.mem := by
    rw [tm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨b₂.step kt.sp kt.rd kt.wr (fu.mono (by simp)) (kt.gpr _ (by decide)), ?_, ?_, ?_⟩
  · rw [t3, hres]; rfl
  · rw [bytes_keep fu (by simp only [oL]; omega) (fun ρ hρ => by
      simp only [List.mem_singleton] at hρ; subst hρ; exact hp.oU), bytes_of_copy hw hb, hval, outOf, hres]
  · rw [tm, (k₂.gpr _ (by decide)).trans hus, usedOf, hres]; exact wordsAt_one _ _ _

end VG.Proof.RsaKeyGen.PPC64LE.Cand
