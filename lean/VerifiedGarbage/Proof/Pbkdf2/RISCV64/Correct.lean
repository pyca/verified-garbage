module

public import VerifiedGarbage.Proof.Pbkdf2.RISCV64.IterateMain
public import VerifiedGarbage.Proof.Pbkdf2.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Hmac.Generic.Implies
public import VerifiedGarbage.Spec.Pbkdf2.Generic
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public meta import VerifiedGarbage.Impl.Pbkdf2.RISCV64

/-!
# PBKDF2-HMAC's iteration over a Merkle–Damgård hash function on RISC-V: `Verified`

`ct` is the taint analysis of `main` after the entry block, which
zero-extends `n`: `n` is public only in its low 32 bits, so the two runs
agree on the whole of `a2` only once correctness says what the block leaves
there (`RelCT.wpDep`). `verified` moves `correct` (`IterateMain.lean`) to the
shared contract of an instance of the hash function, with no stack.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.RISCV64

open VG VG.RISCV64
open VG.Impl.Pbkdf2.RISCV64 (It)
open VG.Proof.MdStream (Md)

/-! ## Constant time -/

/-- `iterate` is constant time, given the taint analysis of `main`, for any
precondition whose public data are `iterK`'s. -/
theorem ctOf (P : It) {pre : State → Prop} {pub : State → State → Prop}
    (hpub : ∀ s₁ s₂, pub s₁ s₂ → s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧
      (s₁.gpr .a2).setWidth 32 = (s₂.gpr .a2).setWidth 32 ∧ s₁.gpr .a3 = s₂.gpr .a3 ∧
      s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.sp = s₂.sp)
    {hc : VG.Taint.Hint taint.T}
    (hb : (taint.check (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) P.main hc).isSome = true) :
    ConstantTime isa pre pub P.iterate := by
  refine RelCT.constantTime (Q := fun _ _ => True) (RelCT.seq ?_ (RelCT.taint (A := taint)
    (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) (fun _ _ h => h) hb))
  have ag4 : ∀ s₁ s₂ : State, pre s₁ ∧ pre s₂ ∧ pub s₁ s₂ →
      taint.Agree (Taint.ofRegs [.a0, .a1, .a3, .a4]) s₁ s₂ := by
    rintro s₁ s₂ ⟨_, _, hq⟩
    obtain ⟨h0, h1, _, h3, h4, hsp⟩ := hpub s₁ s₂ hq
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [h0, h1, h3, h4]
  refine RelCT.mono (RelCT.wpDep (F := Entry) (RelCT.taint (A := taint) (Taint.ofRegs [.a0, .a1, .a3, .a4])
    ag4 (by taint_decide)) fun s₁ s₂ _ => ⟨entry_ok s₁, entry_ok s₂⟩) (fun _ _ h => h) ?_
  rintro s₁' s₂' ⟨-, σ₁, σ₂, ⟨_, _, hq⟩, a, b⟩
  obtain ⟨h0, h1, h2, h3, h4, hsp⟩ := hpub σ₁ σ₂ hq
  refine ⟨by rw [a.sp, b.sp, hsp], fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [a.other _ (by decide), b.other _ (by decide), h0]
  · rw [a.other _ (by decide), b.other _ (by decide), h1]
  · rw [a.a2, b.a2, nn, nn, h2]
  · rw [a.other _ (by decide), b.other _ (by decide), h3]
  · rw [a.other _ (by decide), b.other _ (by decide), h4]

/-- `iterate` is constant time, given the taint analysis of `main`. -/
theorem ct (P : It) (S : Spec.Hmac.StreamingHash) (Wi : Nat) {hc : VG.Taint.Hint taint.T}
    (hb : (taint.check (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) P.main hc).isSome = true) :
    ConstantTime isa (iterK S Wi).pre (iterK S Wi).pub P.iterate :=
  ctOf P (fun _ _ h => h) hb

theorem iterate_noFrames (P : It) (hc : P.cmpC.noFrames = true) : P.iterate.noFrames = true := by
  simp [It.iterate, It.main, It.body, It.compressAt, Code.noFrames, hc]

/-! ## The shared contract -/

theorem pre_of {P : It} {Wi : Nat} {S : Spec.Hmac.StreamingHash} (hS : S.stateBytes = P.N + P.B)
    (hD : S.digestBytes = P.D) {s₀ : State} (h : (iterK S Wi).pre s₀) : Pre P Wi s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := h
  simp only [hS, hD] at *
  exact ⟨h0, h1, h2, h3, h4, h5, h6⟩

theorem iterImp {I : Spec.Hmac.Instance} (hs : ∃ s, (Proof.Pbkdf2.Instance.iterateContract I RISCV64.abi 0).pre s) :
    (iterK I.S (8 * I.scratch)).Implies (Proof.Pbkdf2.Instance.iterateContract I RISCV64.abi 0) := by
  generic_implies [Proof.Pbkdf2.Instance.iterateContract, Proof.Pbkdf2.iterateContract, Proof.Pbkdf2.iterateSig,
    iterK, RISCV64.abi, RISCV64.argRegs] using hs

/-- `iterate` against the shared contract of an instance `I` of the hash
function, with the `Wi` bytes of scratch space it uses, given its constant
time. -/
theorem verified {P : It} {Wi L : Nat} {H : Md P.B P.N L} {iv : H.HV} {I : Spec.Hmac.Instance}
    (ho : HashOk P Wi I.S H iv) (hf : CalleeOk H P.CW P.cmpC) (hfit : Wi ≤ 8 * I.scratch)
    (ct : ConstantTime isa (iterK I.S Wi).pre (iterK I.S Wi).pub P.iterate)
    (hs : ∃ s, (Proof.Pbkdf2.Instance.iterateContract I RISCV64.abi 0).pre s) :
    Verified RISCV64.target P.iterate (Proof.Pbkdf2.Instance.iterateContract I RISCV64.abi 0) := by
  have imp := iterImp hs
  have hS : I.S.stateBytes = P.N + P.B := ho.link.hS
  have hD : I.S.digestBytes = P.D := ho.link.hD
  have wide : ∀ s, (iterK I.S (8 * I.scratch)).pre s →
      (iterK I.S Wi).pre (s.withRegions s.rd [⟨s.gpr .a3, I.S.digestBytes⟩, ⟨s.gpr .a4, Wi⟩]) := by
    intro s ⟨h1, _, h3, h4, h5, h6, h7⟩
    exact ⟨h1, rfl, h3, h4.sub_right (Region.sub_prefix hfit), h5, h6.sub_right (Region.sub_prefix hfit),
      h7.sub_right (Region.sub_prefix hfit)⟩
  have v : Verified RISCV64.target P.iterate (iterK I.S Wi) :=
    ⟨fun s hs => by
      obtain ⟨t, s', he, h₁, h₂⟩ := correct ho hf (pre_of hS hD hs); exact ⟨t, s', he, h₁, h₂⟩, ct,
      imp.sat_left.elim fun s h => ⟨_, wide s h⟩⟩
  refine (Verified.widen v (fun s => [⟨s.gpr .a3, I.S.digestBytes⟩, ⟨s.gpr .a4, Wi⟩]) wide
      (fun _ h => ?_) (fun _ _ _ h => h) (fun _ _ _ _ h => h) imp.sat_left).of_implies imp
  obtain ⟨_, h2, _⟩ := h
  rw [h2]
  exact .cons ⟨rfl, Nat.le_refl _⟩ (.cons ⟨rfl, hfit⟩ .nil)

/-- A state satisfying `iterate`'s precondition, with states of `S` bytes, a
digest of `D` bytes and `sc` bytes of scratch space. -/
def iterSat (S D sc : Nat) : State where
  gpr r := match r with
    | .a0 => 0x10000 | .a1 => 0x20000 | .a2 => 1 | .a3 => 0x30000 | .a4 => 0x40000
    | _ => 0
  sp := 0x90000
  mem _ := 0
  rd := [⟨0x10000, 2 * S⟩, ⟨0x20000, D⟩]
  wr := [⟨0x30000, D⟩, ⟨0x40000, sc⟩]

end VG.Proof.Pbkdf2.RISCV64
