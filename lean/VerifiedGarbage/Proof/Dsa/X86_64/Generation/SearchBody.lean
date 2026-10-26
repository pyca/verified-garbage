module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchEntry
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchControl
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PAttempt
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.NeZero
import Mathlib.Data.Int.ModEq
public import Mathlib.Algebra.Group.Nat.Defs

/-! # The complete p body returns the persistent state needed by its next iteration -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout
open VG.Proof.Pbkdf2.Md.X86_64 VG.Proof.MillerRabin.X86_64

def SearchPlan.candidate (p : SearchPlan) (counter : Nat) : Nat :=
  Spec.Dsa.pCandidate (8 * p.attempt.construct.len) (8 * p.attempt.construct.hash.len)
    (Spec.Rsa.os2ip p.attempt.construct.qb) p.attempt.construct.hash.seed
    (1 + counter * (p.attempt.construct.hash.count + 1))

def SearchPlan.stepResult (p : SearchPlan) (counter used : Nat) : Option (Bool × List Byte) :=
  if p.candidate counter < 2 ^ (8 * p.attempt.construct.len - 1) then some (false, p.attempt.rand.drop used)
  else Spec.Dsa.probablePrime (p.candidate counter) (p.attempt.rand.drop used)

theorem searchBody_ok {G1 G256 : Impl.Pbkdf2.Md.X86_64.Stream} {p : SearchPlan}
    (hG : Calls.StreamOK (if p.attempt.construct.hash.len = 20 then G1 else G256))
    {H : Spec.Mgf1.Hash} (hHh : ∀ x, H.hash x = hG.SH.H.hash x)
    (hsize : ∀ bytes, (H.hash bytes).length = (if p.attempt.construct.hash.len = 20 then G1 else G256).D)
    (M : Mont) (K : Kernel)
    (hd : (if p.attempt.construct.hash.len = 20 then G1 else G256).D = p.attempt.construct.hash.len)
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * p.attempt.construct.hash.len) bs)
    (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * p.attempt.construct.hash.len) bs).length = 8 * p.attempt.construct.hash.len)
    {s : State} {W : Nat → BitVec 64} {counter used : Nat} (h : SearchMemory p W s)
    (ctrl : SearchControl p.C counter (p.attempt.construct.hash.count + 1) s)
    (hc : counter < 32 * p.attempt.construct.len)
    (hused : W 16 = BitVec.ofNat 64 used) (hu : used ≤ p.attempt.rand.length) :
    WP isa (Impl.Dsa.X86_64.Generation.pAttempt G1 G256 M.mm K.run
      p.attempt.construct.len p.attempt.construct.hash.len) s fun t =>
      SearchControl p.C counter (p.attempt.construct.hash.count + 1) t ∧
      ∃ (W' : Nat → BitVec 64) (used' : Nat) (status : BitVec 64),
        SearchMemory p W' t ∧ used' ≤ p.attempt.rand.length ∧ W' 16 = BitVec.ofNat 64 used' ∧
        W' 19 = status ∧ word t.mem p.C 16 = status ∧
        Spec.Rsa.bytesAt t.mem (off (p.attempt.construct.hash.W 5) Impl.Dsa.Generation.Layout.p) p.attempt.construct.len =
          Spec.Dsa.encodeBE p.attempt.construct.len (p.candidate counter) ∧
        Spec.Rsa.bytesAt t.mem (off (p.attempt.construct.hash.W 5) exponent) p.attempt.construct.len =
          Spec.Dsa.encodeBE p.attempt.construct.len ((p.candidate counter - 1) / Spec.Rsa.os2ip p.attempt.construct.qb) ∧
        (p.stepResult counter used = none → status = BitVec.ofNat 64 0) ∧
        (∀ b rest, p.stepResult counter used = some (b, rest) →
          status = BitVec.ofNat 64 (if b then 1 else 3) ∧ used' = p.attempt.rand.length - rest.length) ∧
        Frame (searchWrites p.attempt p.C) s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  let offset := 1 + counter * (p.attempt.construct.hash.count + 1)
  have carry : offset + p.attempt.construct.hash.count < 2 ^ 32 := by
    have hcmax : counter < 12288 := by rcases p.attempt.construct.width with hh | hh | hh <;> omega
    have hmul := Nat.mul_le_mul_left counter (show p.attempt.construct.hash.count + 1 ≤ 12 by
      have := p.attempt.construct.hash.count_le; omega)
    dsimp only [offset]
    omega_using [p.attempt.construct.hash.count_le, hcmax, hmul]
  let call := h.attemptPlan offset carry
  have h5 := h.slots 5 (by simp [searchSlots])
  have cw5 : call.construct.hash.W 5 = p.attempt.construct.hash.W 5 := by
    simpa [SearchMemory.attemptPlan, PPrimalityPlan.reframe, PConstructPlan.reframe, HashPlan.reframe,
      attemptWords, upd, call] using h5
  have clen : call.construct.len = p.attempt.construct.len := rfl
  have cF : call.construct.hash.F = p.attempt.construct.hash.F := rfl
  have changed : call.changed = p.attempt.changed := by
    dsimp only [call, SearchMemory.attemptPlan, PPrimalityPlan.reframe, PConstructPlan.reframe,
      HashPlan.reframe, PPrimalityPlan.changed, PPrimalityPlan.testWrites, PConstructPlan.changed, HashPlan.changed]
    simp only [attemptWords, upd, ite_false, show ¬ (5 : Nat) = 27 by decide,
      show ¬ (5 : Nat) = 2 by decide, show ¬ (5 : Nat) = 0 by decide, h5]
  refine WP.mono (pAttempt_ok (p := call) hG hHh hsize M K hd (h.entry offset carry H)
    ctrl rfl (by rw [cw5]; exact p.controlBase) hhash hseedsize
    (by simpa [call, SearchMemory.attemptPlan, PPrimalityPlan.reframe, PConstructPlan.reframe,
      HashPlan.reframe, attemptWords, upd] using hused) hu h.tape
    (by
      change (⟨p.attempt.rp, p.attempt.rand.length⟩ : Region).Disjoint ⟨p.attempt.construct.hash.F, frameBytes⟩
      exact p.tapeSeparate _ (by simp [searchWrites]))
    (by simpa only [cw5, clen] using h.witnessWrite)
    (by rw [changed]; exact p.controlSeparate) p.frameControl p.hashControl
    (by simpa only [cw5, clen] using p.pControl) (by simpa only [cw5, clen] using p.exponentControl))
    fun t ⟨ct, Wused, status, V, bound, Lt, Rt, htstatus, bp, be, he, hr, ft, rdt, wrt⟩ => ?_
  have ff : Frame (searchWrites p.attempt p.C) s.mem t.mem := by
    change Frame (⟨p.C, 24⟩ :: ⟨p.attempt.construct.hash.F, frameBytes⟩ :: p.attempt.changed) s.mem t.mem
    simpa only [changed, cF] using ft
  let W' := upd (upd call.construct.hash.W 16 (BitVec.ofNat 64 Wused)) 19 status
  have memory : SearchMemory p W' t := h.frame Lt ⟨V, Rt⟩ (by
    intro k hk
    dsimp only [W', call, SearchMemory.attemptPlan, PPrimalityPlan.reframe, PConstructPlan.reframe, HashPlan.reframe]
    simp only [searchSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [upd, attemptWords]) ff rdt wrt
  refine ⟨ct, W', Wused, status, memory, bound, by simp [W', upd], by simp [W', upd], htstatus,
    ?_, ?_, he, hr, ff, rdt, wrt⟩
  · rw [cw5] at bp
    exact bp
  · rw [cw5] at be
    exact be

end VG.Proof.Dsa.X86_64.Generation
