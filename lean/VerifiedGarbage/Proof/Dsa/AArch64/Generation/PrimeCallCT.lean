module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeCall
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeCall
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Bignum.AArch64.Run
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract

/-! # Calling the probable-prime test in constant time

The test's arguments are the generation's pointers and lengths, and its
leak, the candidate and the unread tape, is public: so is its status, which
the result then branches on. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.Generation.Layout

/-- What two runs of a call agree on. -/
structure PrimeTestPublic (bits : Nat) where
  F : Addr
  S : Addr
  A : Addr
  rp : Addr
  rand : List Byte
  N : Nat
  used : Nat
  geometry : PrimeCallGeometry bits F S A rp rand.length

def PrimeTestBefore (bits : Nat) (a : PrimeTestPublic bits) (s : State) : Prop :=
  ∃ W V, PrimeCallInputs bits a.F a.S a.A a.rp a.rand a.N a.used W V s

theorem PrimeCallInputs.congr {bits : Nat} {F S A rp : Addr} {rand : List Byte} {N used : Nat}
    {W : Nat → BitVec 64} {V : Nat → Byte} {s t : State}
    (h : PrimeCallInputs bits F S A rp rand N used W V s)
    (hm : t.mem = s.mem) (hsp : t.sp = s.sp) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) :
    PrimeCallInputs bits F S A rp rand N used W V t where
  layout := h.layout.congr hsp hwr (by rw [hm])
  rep := hm ▸ h.rep
  arena := h.arena
  arenaWrite := h.arenaWrite.congr hwr
  tapePtr := h.tapePtr
  tapeLength := h.tapeLength
  usedSlot := h.usedSlot
  usedBound := h.usedBound
  tapeSize := h.tapeSize
  tapeCover := by rw [hrd, hwr]; exact h.tapeCover
  tapeBytes := by rw [hm]; exact h.tapeBytes
  candidate := by rw [hm]; exact h.candidate
  odd := h.odd
  bitLen := h.bitLen

/-- The arguments in their registers. -/
def PrimeTestReady (bits : Nat) (a : PrimeTestPublic bits) (u : State) : Prop :=
  ∃ s W V, PrimeCallInputs bits a.F a.S a.A a.rp a.rand a.N a.used W V s ∧
    u.gpr .x0 = a.A ∧ u.gpr .x1 = BitVec.ofNat 64 (domainCheck / 8) ∧
    u.gpr .x2 = a.rp + BitVec.ofNat 64 a.used ∧ u.gpr .x3 = BitVec.ofNat 64 (a.rand.length - a.used) ∧
    u.gpr .x4 = off a.F 152 ∧ u.mem = s.mem ∧ u.sp = a.F ∧ u.rd = s.rd ∧ u.wr = s.wr

/-- The test's status. -/
def PrimeTestPublic.status {bits : Nat} (a : PrimeTestPublic bits) : Nat :=
  Proof.Dsa.ProbablePrime.status (Spec.Dsa.probablePrime a.N (a.rand.drop a.used))

theorem PrimeTestPublic.status_lt {bits : Nat} (a : PrimeTestPublic bits) : a.status < 3 := by
  unfold PrimeTestPublic.status
  rcases Spec.Dsa.probablePrime a.N (a.rand.drop a.used) with _ | ⟨_ | _, _⟩ <;>
    simp only [Proof.Dsa.ProbablePrime.status] <;> decide

def PrimeTestDone (bits : Nat) (a : PrimeTestPublic bits) (t : State) : Prop :=
  t.sp = a.F ∧ (t.gpr .x0).setWidth 32 = BitVec.ofNat 32 a.status

def PrimeTestStatus (bits : Nat) (a : PrimeTestPublic bits) (t : State) : Prop :=
  t.sp = a.F ∧ t.gpr .x0 = BitVec.ofNat 64 a.status

theorem primeCallArgs_ct (bits : Nat) :
    RelCT isa (Two (PrimeTestBefore bits)) (.block Impl.Dsa.AArch64.Generation.primeCallArgs)
      (Two (PrimeTestReady bits)) := by
  refine two_piece [] (fun _ _ _ _ _ _ hr => nomatch hr) (by taint_decide) fun a s ⟨W, V, h⟩ => ?_
  exact WP.mono (primeCallArgs_ok h) fun u ⟨h0, h1, h2, h3, h4, hm, ku⟩ =>
    ⟨s, W, V, h, h0, h1, h2, h3, h4, hm, ku.sp.trans h.layout.sp, ku.rd, ku.wr⟩

theorem primeCallTest_ct (T : PrimeTest) {bits : Nat} (hb : ProbablePrime.Supported bits) :
    RelCT isa (Two (PrimeTestReady bits)) (T.run bits) (Two (PrimeTestDone bits)) := by
  refine two_post ?_ fun a u ⟨s, W, V, h, h0, h1, h2, h3, h4, hm, hsp, hrd, hwr⟩ =>
    WP.mono (primeCall_call_ok T hb h a.geometry h0 h1 h2 h3 h4 hm hsp hrd hwr) fun t C => ⟨C.sp, C.status⟩
  refine RelCT.callEx (T.verified bits hb).1 (T.verified bits hb).2.1 fun s₁ s₂ ⟨a, h₁, h₂, _⟩ => ?_
  obtain ⟨_, _, _, i₁, h0₁, h1₁, h2₁, h3₁, h4₁, hm₁, hsp₁, hrd₁, hwr₁⟩ := h₁
  obtain ⟨_, _, _, i₂, h0₂, h1₂, h2₂, h3₂, h4₂, hm₂, hsp₂, hrd₂, hwr₂⟩ := h₂
  have E₁ := primeCall_entry i₁ a.geometry h0₁ h1₁ h2₁ h3₁ h4₁ hm₁ hsp₁ hrd₁ hwr₁
  have E₂ := primeCall_entry i₂ a.geometry h0₂ h1₂ h2₂ h3₂ h4₂ hm₂ hsp₂ hrd₂ hwr₂
  refine ⟨_, _, _, _, E₁.pre, E₂.pre, ?_, E₁.reads, E₁.writes, E₂.reads, E₂.writes⟩
  sig_pub [ProbablePrime.contract, Proof.Dsa.ProbablePrime.contract, Proof.Dsa.ProbablePrime.sig, abi, argRegs]
  have hl : (BitVec.ofNat 64 (a.rand.length - a.used)).toNat = a.rand.length - a.used := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := i₁.tapeSize; omega)]
  rw [hsp₁, hsp₂, h0₁, h0₂, h2₁, h2₂, h3₁, h3₂, h1₁, h1₂, h4₁, h4₂, hl, E₁.candidate, E₂.candidate,
    E₁.tape, E₂.tape]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem primeCallStatus_ct (bits : Nat) :
    RelCT isa (Two (PrimeTestDone bits)) Impl.Dsa.AArch64.Generation.primeCallStatus fun _ _ => True := by
  unfold Impl.Dsa.AArch64.Generation.primeCallStatus
  refine RelCT.seq (two_piece (Ψ := PrimeTestStatus bits) [] (fun _ _ _ _ _ _ hr => nomatch hr)
    (by taint_decide) fun a t ⟨hsp, hx0⟩ => ?_) ?_
  · have hk := a.status_lt
    have hz : (BitVec.ofNat 32 a.status).setWidth 64 = BitVec.ofNat 64 a.status := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
    have run0 : WP isa (.block [.addImm .w .x0 .x0 0]) t fun u => u.gpr .x0 = BitVec.ofNat 64 a.status := by
      brun [exec_addImm_w_zero, State.write, hx0, hz]
    exact WP.mono (WP.keep [.x0] run0 (by decide)) fun u ⟨hu, ku⟩ => ⟨ku.sp.trans hsp, hu⟩
  · exact two_taint [.x0] (fun a s₁ s₂ h₁ h₂ r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact h₁.2.trans h₂.2.symm) (by taint_decide)

theorem primeCall_ct (T : PrimeTest) {bits : Nat} (hb : ProbablePrime.Supported bits) :
    RelCT isa (Two (PrimeTestBefore bits)) (Impl.Dsa.AArch64.Generation.primeCall T.run bits)
      fun _ _ => True := by
  unfold Impl.Dsa.AArch64.Generation.primeCall
  exact RelCT.seq (primeCallArgs_ct bits) (RelCT.seq (primeCallTest_ct T hb) (primeCallStatus_ct bits))

end VG.Proof.Dsa.AArch64.Generation
