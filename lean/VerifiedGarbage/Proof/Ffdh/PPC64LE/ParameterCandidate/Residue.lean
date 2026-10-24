module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Phase
import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.SmallMod
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# An FFDH parameter candidate on PPC64LE: the generator's congruence

`residue_ok`: `hBad` is zero exactly when array 0 is 11 modulo 24 (for the
generator 2), or 3 or 7 modulo 10 (for 5).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE

/-- The congruence the generator asks of p. -/
def goodRes (g x : Nat) : Prop := if g = 2 then x % 24 = 11 else x % 10 = 3 ∨ x % 10 = 7

/-- The registers `residue` writes. -/
def resRegs : List Reg := [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r14]

theorem res2 : ∀ r < 24, (BitVec.ofNat 64 r ^^^ BitVec.ofNat 64 11 = 0#64 ↔ r = 11) := by decide

theorem res5 : ∀ r < 10, ((BitVec.ofNat 64 r ||| BitVec.ofNat 64 4) ^^^ BitVec.ofNat 64 7 = 0#64 ↔ r = 3 ∨ r = 7) := by
  decide

/-- `hBad` stored over `m`. -/
theorem bad_post {m : Mem} {p : PP} {t : State} {v : BitVec 64} {P : Prop}
    (tm : t.mem = m.writeW (p.B + BitVec.ofNat 64 200) v) (hv : v = 0#64 ↔ P) :
    (word t.mem p.B (8 * hBad) = 0#64 ↔ P) ∧ Frm p.B [(8 * hBad, 8)] m t.mem := by
  refine ⟨?_, ?_⟩
  · simp only [word, off, hBad, Nat.reduceMul, tm, rw_self]; exact hv
  · rw [tm]
    exact frm_writeW (a := 200) (Frm.refl _ _ _) _ ⟨_, List.mem_singleton_self _, by decide, by decide⟩ (by decide)

theorem residue_ok {p : PP} {s : State} (h : St p s) (hp : Ph p p.bits s) :
    WP isa residue s fun t =>
      ((word t.mem p.B (8 * hBad) = 0#64 ↔ goodRes p.g (wv s.mem p.B (slot (wOf p.bits) 0) (wOf p.bits))) ∧
        Frm p.B [(8 * hBad, 8)] s.mem t.mem) ∧ Keep resRegs s t := by
  have hb1 := h.dims.b1
  have hb2 := h.dims.b2
  have hn := h.dims.n
  have h10 := hp.r10
  have h11 := hp.r11
  generalize hwd : wOf p.bits = w at h10 h11 ⊢
  have hw8 : 8 ≤ w := by simp only [wOf] at hwd; omega
  have hw128 : w ≤ 128 := by simp only [wOf] at hwd; omega
  have hZ : slot w 0 + 8 * w ≤ p.Z := by simp only [slot, hdrBytes, PP.Z, PP.L] at hn ⊢; omega
  generalize hx : wv s.mem p.B (slot w 0) w = x
  have kd : ∀ d, d < 2 ^ 62 → 2 ≤ d → ∀ (tail : List Instr) {u : State} (Q : State → Prop),
      WP isa (.block [.li .r4 d]) u (fun v => (v.gpr .r4 = BitVec.ofNat 64 d ∧ v.mem = u.mem) ∧ Keep [.r4] u v) →
      St p u → u.gpr .r10 = off p.B (slot w 0) → u.gpr .r11 = BitVec.ofNat 64 (2 * w) → u.mem = s.mem →
      (∀ t', t'.gpr .r3 = BitVec.ofNat 64 (x % d) → t'.mem = s.mem → St p t' →
        WP isa (.block tail) t' fun t => Q t ∧ Keep (.r4 :: smRegs) t' t) →
      WP isa (.seq (.block [.li .r4 d]) (.seq smallMod (.block tail))) u fun t => Q t ∧ Keep resRegs u t := by
    intro d hd hd2 tail u Q hli hu u10 u11 um ht
    refine WP.seq (WP.mono hli fun v ⟨⟨v4, vm⟩, kv⟩ => ?_)
    refine WP.seq (WP.mono (smallMod_ok (hu.scr.congr kv.wr) ((kv.gpr .r10 (by decide)).trans u10)
      ((kv.gpr .r11 (by decide)).trans u11) v4 (by omega) (by omega) hZ hd2 hd) fun t' ⟨⟨t3, tm'⟩, kt'⟩ => ?_)
    rw [vm, um, hx] at t3
    have k3 := kv.trans kt'
    refine WP.mono (ht t' t3 (by rw [tm', vm, um]) (hu.step (by rw [tm', vm]; exact Frm.refl _ _ _) k3))
      fun t ⟨q, kt⟩ => ⟨q, (k3.trans kt).mono (by decide)⟩
  unfold residue
  refine WP.seq (WP.mono (WP.keep [.r3] (Q := fun u => u.gpr .r3 = BitVec.ofNat 64 p.g - 2#64 ∧ u.mem = s.mem)
    (by simp only [ldh, hGen]; prun [h.r31, h.ld (d := 128) (by decide), h.args.gen']) (by decide))
    fun u ⟨⟨u3, um⟩, ku⟩ => ?_)
  have hu := h.step (by rw [um]; exact Frm.refl _ _ _) ku
  have u10 := (ku.gpr .r10 (by decide)).trans h10
  have u11 := (ku.gpr .r11 (by decide)).trans h11
  refine WP.ite (u.gpr .r3 == 0) (eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
  · have hg : p.g = 2 := by
      rcases h.dims.g with hg | hg <;> rw [u3, hg] at hb
      · exact hg
      · exact absurd hb (by decide)
    refine WP.mono (kd 24 (by decide) (by decide) _ _ (WP.keep _ (by prun []) (by decide)) hu u10 u11 um
      fun t' t3 tm' ht' => ?_) fun t ⟨q, k⟩ => ⟨q, (ku.trans k).mono (by decide)⟩
    refine WP.mono (WP.keep [.r3, .r4] (Q := fun t => t.mem = s.mem.writeW (p.B + BitVec.ofNat 64 200)
      (BitVec.ofNat 64 (x % 24) ^^^ BitVec.ofNat 64 11)) ?_ (by decide)) fun t ⟨tm, kt⟩ =>
        ⟨bad_post tm ?_, kt.mono (by decide)⟩
    · simp only [sth, hBad]
      prun [ht'.r31, ht'.st (d := 200) (by decide), tm', t3]
    · rw [res2 _ (Nat.mod_lt _ (by decide)), goodRes, ite_eq_left hg]
  · have hg : p.g = 5 := by
      rcases h.dims.g with hg | hg <;> rw [u3, hg] at hb
      · exact absurd hb (by decide)
      · exact hg
    refine WP.mono (kd 10 (by decide) (by decide) _ _ (WP.keep _ (by prun []) (by decide)) hu u10 u11 um
      fun t' t3 tm' ht' => ?_) fun t ⟨q, k⟩ => ⟨q, (ku.trans k).mono (by decide)⟩
    refine WP.mono (WP.keep [.r3, .r4] (Q := fun t => t.mem = s.mem.writeW (p.B + BitVec.ofNat 64 200)
      ((BitVec.ofNat 64 (x % 10) ||| BitVec.ofNat 64 4) ^^^ BitVec.ofNat 64 7)) ?_ (by decide)) fun t ⟨tm, kt⟩ =>
        ⟨bad_post tm ?_, kt.mono (by decide)⟩
    · simp only [sth, hBad]
      prun [ht'.r31, ht'.st (d := 200) (by decide), tm', t3]
    · rw [res5 _ (Nat.mod_lt _ (by decide)), goodRes, ite_eq_right (by omega)]

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate
