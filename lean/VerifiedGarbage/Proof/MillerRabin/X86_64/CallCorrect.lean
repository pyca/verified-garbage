module
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.Table
public import VerifiedGarbage.Impl.MillerRabin.X86_64.Round
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline

import VerifiedGarbage.Proof.MillerRabin.X86_64.Context
import VerifiedGarbage.Proof.MillerRabin.X86_64.FramedCall
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallStack
import VerifiedGarbage.Proof.MillerRabin.X86_64.EntrySaved
import VerifiedGarbage.Proof.MillerRabin.X86_64.StackPrepared
import VerifiedGarbage.Proof.MillerRabin.X86_64.StageContext
import VerifiedGarbage.Proof.MillerRabin.Representation
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.X86_64.MontFnVerified
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.MillerRabin.X86_64.StackContext
import VerifiedGarbage.Impl.RsaKeyGen.X86_64.Candidate
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp

/-!
# Correctness of the round with Montgomery calls

`round_math_ok` and `round_correct` for a body `code` that calls the
Montgomery multiplication where `body M.mm` runs it inline
(`code.inline = body M.mm`): the calls' return address is 120 bytes below
`rsp`, under the frames' 112, which the precondition keeps from the
workspace (`framed_call_ok`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaKeyGen VG.Proof.RsaKeyGen.X86_64
open VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Impl.MillerRabin.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Bignum.X86_64.MontFn (numAt_eq)

private theorem result32' (p : Bool) :
    ((BitVec.ofNat 64 p.toNat).setWidth 32).toNat = if p then 1 else 0 := by
  cases p <;> decide

theorem round_call_math_ok (M : Mont) {code : Prog isa} (hi : code.InlineOk = true)
    (hcode : code.inline = VG.Impl.MillerRabin.X86_64.body M.mm) {s : State} (hpre : roundPre s) :
    WP isa (.seq (.block stage) (.frame (.push saved) (.frame (.push [.rbp]) code (.pop .rbp 1)) (.pop .r11 13)))
      s fun t =>
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ roundPost s t ∧
      Frame [⟨s.gpr .rsp - 120#64, 120⟩, ⟨s.gpr .rdi, (s.gpr .rsi).toNat * 8⟩] s.mem t.mem := by
  obtain ⟨hdim, bm, hc, he, hodd, h3, hx⟩ := initial_ctx hpre
  rcases hpre with ⟨hrd, hwr, hn, hsp, hret, hstack, hL, hP⟩
  rw [Nat.mul_comm (s.gpr .rsi).toNat 8] at hdim hc hn hwr hstack
  let B := s.gpr .rdi
  let n := (s.gpr .rsi).toNat
  let w := Proof.Rsa.Mont.wOf s.mem B
  let c := Proof.Rsa.Mont.numAt s.mem B w 0
  have hR := coprime_pow2 hodd (64 * w)
  obtain ⟨b, _, hb⟩ := witness_exists hR hx
  have hX : wv s.mem B (slot w aXm) w = Spec.Rsa.powMod b 1 c * 2 ^ (64 * w) % c := by
    simpa only [VG.Proof.Bignum.powMod_eq, Nat.pow_one] using hb
  have hz : 256 ≤ 8 * n := by
    have := hdr_lt_slot w 8 (show 31 < 32 by decide)
    have hz0 : slot w 8 ≤ 8 * n := hdim.z
    change 256 ≤ 8 * n
    omega_arith
  refine WP.seq (WP.mono (stage_ok hc.good hdim.z) fun u ⟨hm, hv, hk⟩ => ?_)
  have hu : u.gpr .rsp = s.gpr .rsp := hk.gpr (by decide)
  have hsu : 120 ≤ (u.gpr .rsp).toNat := hu ▸ hsp
  have hdu : Region.Disjoint ⟨u.gpr .rsp - 112#64, 112⟩ ⟨B, 8 * n⟩ := by
    rw [hu]
    exact hstack.sub_left (Offset.sub_below _ (a := 112) (n := 112) (b := 120) (m := 120) (by decide) (by decide))
  have ⟨hcu, heu⟩ := staged_context hc he hm hk
  have hce := entered_ctx hcu hdim hsu hdu
  have hee := entered_exp heu hdim hsu hc.good.scr.nowrap hdu
  have hXe : wv (entered u).mem B (slot w aXm) w = Spec.Rsa.powMod b 1 c * 2 ^ (64 * w) % c := by
    rw [entered_wv hsu hc.good.scr.nowrap hdu (by
      have := slot_le (w := w) (show aXm < 8 by decide)
      have hz0 : slot w 8 ≤ 8 * n := hdim.z
      omega_arith), hm]
    exact hX
  have hdu120 : Region.Disjoint ⟨u.gpr .rsp - 120#64, 120⟩ ⟨B, 8 * n⟩ := by
    rw [hu]
    exact hstack
  have hclear := entered_clear (hk.2.1.trans hrd) (hk.2.2.trans hwr) hdu120
  have hhole : Region.Disjoint ⟨B, 8 * n⟩ (hole ((entered u).gpr .rsp)) := by
    rw [entered_hole]
    exact (hdu120.sub_left (Offset.sub_below _ (by decide : 120 ≤ 120) (by decide : 120 - 120 + 8 ≤ 120))).symm
  refine WP.mono (framed_call_ok M hi hcode hclear hhole hsu hce hdim hee hodd h3 hXe hdu.symm
    (entered_saved_headers hv hm hsu hc.good.scr.nowrap hz hdu)) ?_
  rintro t ⟨hout, hregs, hkeep, hframe⟩
  refine ⟨fun r hr => (hregs r hr).trans (hk.gpr (by revert r; decide)), ⟨?_, ?_⟩, ?_⟩
  · intro b' hb'
    have heq : Proof.MillerRabin.Round.round c b = Proof.MillerRabin.Round.round c b' := by
      apply round_eq_of_mont (by have hc3 : 3 ≤ c := h3; omega_arith) hR
      rw [← hb, ← hb']
      exact (numAt_eq s.mem B w aXm).symm
    have hr32 := congrArg (fun x : BitVec 64 => (x.setWidth 32).toNat) hout
    exact hr32.trans ((result32' _).trans (congrArg (fun p : Bool => if p then 1 else 0) heq))
  · intro i hi hh ha ht
    exact (hkeep i hi hh ha ht).trans (congrArg (fun m : Mem => m (B + BitVec.ofNat 64 i)) hm)
  · intro x hx'
    refine (hframe x ?_).trans (congrArg (fun m : Mem => m x) hm)
    simpa only [hu, B, n, Nat.mul_comm] using hx'

/-- The round, with the body `code`, preserves the calling convention. -/
theorem round_call_correct (M : Mont) {code : Prog isa} (hi : code.InlineOk = true)
    (hcode : code.inline = VG.Impl.MillerRabin.X86_64.body M.mm)
    (hload : ∀ i ∈ instrs (.seq (.block stage)
      (.frame (.push saved) (.frame (.push [.rbp]) code (.pop .rbp 1)) (.pop .r11 13)) : Prog isa),
        loadsMxcsr i = false)
    (s : State) (h : roundPre s) :
    ∃ tr t, Exec isa (.seq (.block stage)
      (.frame (.push saved) (.frame (.push [.rbp]) code (.pop .rbp 1)) (.pop .r11 13))) s tr t ∧
      abiPreserved s t ∧ roundPost s t := by
  obtain ⟨tr, t, he, hregs, hp, hf⟩ := round_call_math_ok M hi hcode h
  refine ⟨tr, t, he, ⟨hregs, ?_, ?_⟩, hp⟩
  · apply hf.readW (r := ⟨s.gpr .rsp, 8⟩)
    · simp only [Region.Contains, BitVec.sub_self]
      decide
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · have ha : s.gpr .rsp = (s.gpr .rsp - 120#64) + 120#64 := by bv_omega
        conv_lhs => rw [ha]
        exact Offset.disjoint_base (s.gpr .rsp - 120#64) (by decide : 120 ≤ 120) (by decide : 120 + 8 ≤ 2 ^ 64)
      · exact h.2.2.2.2.1
    · decide
  · rw [VG.X86_64.Exec.mxcsr hload he]

end VG.Proof.MillerRabin.X86_64
