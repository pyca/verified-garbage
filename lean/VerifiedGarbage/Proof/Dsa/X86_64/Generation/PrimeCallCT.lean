module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeCall
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeCall
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Call
meta import VerifiedGarbage.Proof.Framework.X86_64.Inline
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.MlKem.X86_64.Wp
meta import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract

/-! # Calling the probable-prime test in constant time

The test's arguments are the generation's pointers and lengths, and its
leak, the candidate and the unread tape, is public: so is its status, which
the result then branches on. -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
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
    (hm : t.mem = s.mem) (hsp : t.gpr .rsp = s.gpr .rsp) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) :
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
    u.gpr .rdi = a.A ∧ u.gpr .rsi = BitVec.ofNat 64 (domainCheck / 8) ∧
    u.gpr .rdx = a.rp + BitVec.ofNat 64 a.used ∧ u.gpr .rcx = BitVec.ofNat 64 (a.rand.length - a.used) ∧
    u.gpr .r8 = off a.F 152 ∧ u.gpr .r9 = BitVec.ofNat 64 bits ∧ u.mem = s.mem ∧ u.gpr .rsp = a.F ∧
    u.rd = s.rd ∧ u.wr = s.wr

/-- The test's status. -/
def PrimeTestPublic.status {bits : Nat} (a : PrimeTestPublic bits) : Nat :=
  Proof.Dsa.ProbablePrime.status (Spec.Dsa.probablePrime a.N (a.rand.drop a.used))

theorem PrimeTestPublic.status_lt {bits : Nat} (a : PrimeTestPublic bits) : a.status < 3 := by
  unfold PrimeTestPublic.status
  rcases Spec.Dsa.probablePrime a.N (a.rand.drop a.used) with _ | ⟨_ | _, _⟩ <;>
    simp only [Proof.Dsa.ProbablePrime.status] <;> decide

def PrimeTestDone (bits : Nat) (a : PrimeTestPublic bits) (t : State) : Prop :=
  t.gpr .rsp = a.F ∧ (t.gpr .rax).setWidth 32 = BitVec.ofNat 32 a.status

def PrimeTestStatus (bits : Nat) (a : PrimeTestPublic bits) (t : State) : Prop :=
  t.gpr .rsp = a.F ∧ t.gpr .rax = BitVec.ofNat 64 a.status

theorem primeCallArgs_ct {bits : Nat} (hb : ProbablePrime.Supported bits) :
    RelCT isa (Two (PrimeTestBefore bits)) (.block (Impl.Dsa.X86_64.Generation.primeCallArgs bits))
      (Two (PrimeTestReady bits)) := by
  have pins : Pins (PrimeTestBefore bits) [.rsp] := fun a s₁ s₂ ⟨_, _, h₁⟩ ⟨_, _, h₂⟩ r hr => by
    obtain rfl := List.mem_singleton.mp hr
    exact h₁.layout.rsp.trans h₂.layout.rsp.symm
  refine two_post ?_ fun a s ⟨W, V, h⟩ => ?_
  · rcases hb with rfl | rfl | rfl | rfl | rfl <;> exact two_taint [.rsp] pins (by taint_decide)
  exact WP.mono (primeCallArgs_ok hb h) fun u ⟨hdi, hsi, hdx, hcx, h8, h9, hm, ku⟩ =>
    ⟨s, W, V, h, hdi, hsi, hdx, hcx, h8, h9, hm, (ku.gpr (by decide)).trans h.layout.rsp, ku.2.1, ku.2.2⟩

theorem primeCallTest_ct (T : PrimeTest) {bits : Nat} (hb : ProbablePrime.Supported bits) :
    RelCT isa (Two (PrimeTestReady bits)) T.run (Two (PrimeTestDone bits)) := by
  refine two_post ?_ fun a u ⟨s, W, V, h, hdi, hsi, hdx, hcx, h8, h9, hm, hsp, hrd, hwr⟩ =>
    WP.mono (primeCall_call_ok T hb h a.geometry hdi hsi hdx hcx h8 h9 hm hsp hrd hwr)
      fun t C => ⟨C.rsp, C.status⟩
  refine RelCT.callEx T.verified.1 T.verified.2.1 fun s₁ s₂ ⟨a, h₁, h₂⟩ => ?_
  obtain ⟨_, _, _, i₁, hdi₁, hsi₁, hdx₁, hcx₁, h8₁, h9₁, hm₁, hsp₁, hrd₁, hwr₁⟩ := h₁
  obtain ⟨_, _, _, i₂, hdi₂, hsi₂, hdx₂, hcx₂, h8₂, h9₂, hm₂, hsp₂, hrd₂, hwr₂⟩ := h₂
  have E₁ := primeCall_entry hb i₁ a.geometry hdi₁ hsi₁ hdx₁ hcx₁ h8₁ h9₁ hm₁ hsp₁ hrd₁ hwr₁
  have E₂ := primeCall_entry hb i₂ a.geometry hdi₂ hsi₂ hdx₂ hcx₂ h8₂ h9₂ hm₂ hsp₂ hrd₂ hwr₂
  refine ⟨_, _, _, _, E₁.pre, E₂.pre, ?_, E₁.reads, E₁.writes, E₂.reads, E₂.writes, hsp₁.trans hsp₂.symm⟩
  sig_pub [ProbablePrime.contract, Proof.Dsa.ProbablePrime.sizedContract, Proof.Dsa.ProbablePrime.sizedSig,
    abi, argRegs]
  have hl : (BitVec.ofNat 64 (a.rand.length - a.used)).toNat = a.rand.length - a.used := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := i₁.tapeSize; omega)]
  have hbits : (BitVec.ofNat 64 bits).toNat = bits := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hb.le; omega)]
  rw [hsp₁, hsp₂, hdi₁, hdi₂, hdx₁, hdx₂, hcx₁, hcx₂, hsi₁, hsi₂, h8₁, h8₂, h9₁, h9₂, hl, hbits,
    E₁.candidate, E₂.candidate, E₁.tape, E₂.tape]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem primeCallResult_ct (bits : Nat) :
    RelCT isa (Two (PrimeTestDone bits)) Impl.Dsa.X86_64.Generation.primeCallResult fun _ _ => True := by
  unfold Impl.Dsa.X86_64.Generation.primeCallResult
  refine RelCT.seq (two_post (Ψ := PrimeTestStatus bits) (two_taint [.rsp] (fun a s₁ s₂ h₁ h₂ r hr => by
    obtain rfl := List.mem_singleton.mp hr
    exact h₁.1.trans h₂.1.symm) (by taint_decide)) fun a t ⟨hsp, hrax⟩ => ?_) ?_
  · have hk := a.status_lt
    have hz : ((t.gpr .rax).setWidth 32).setWidth 64 = BitVec.ofNat 64 a.status := by
      rw [hrax]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
    exact WP.mono (WP.keep [.rax] (Q := fun x => x.gpr .rax = BitVec.ofNat 64 a.status) (by xrun [hz]) rfl)
      fun x ⟨hx, kx⟩ => ⟨(kx.gpr (by decide)).trans hsp, hx⟩
  · unfold Impl.Dsa.X86_64.Generation.primeCallStatus
    exact two_taint [.rsp, .rax] (fun a s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h₁.1.trans h₂.1.symm
      · exact h₁.2.trans h₂.2.symm) (by taint_decide)

theorem primeCall_ct (T : PrimeTest) {bits : Nat} (hb : ProbablePrime.Supported bits) :
    RelCT isa (Two (PrimeTestBefore bits)) (Impl.Dsa.X86_64.Generation.primeCall T.run bits)
      fun _ _ => True := by
  unfold Impl.Dsa.X86_64.Generation.primeCall
  exact RelCT.seq (primeCallArgs_ct hb) (RelCT.seq (primeCallTest_ct T hb) (primeCallResult_ct bits))

end VG.Proof.Dsa.X86_64.Generation
