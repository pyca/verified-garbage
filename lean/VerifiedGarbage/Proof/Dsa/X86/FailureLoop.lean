module

public import VerifiedGarbage.Proof.Dsa.X86.FailureStep
public import VerifiedGarbage.Spec.Rsa.Contract

/-! # Complete public-domain rejection zeroization and termination -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Zeroize

structure FailureInv (out : BitVec 32) (len i : Nat) (s t : State) : Prop where
  pointer : t.gpr .esi = out + BitVec.ofNat 32 i
  counter : t.gpr .ecx = BitVec.ofNat 32 (len - i)
  zero : t.gpr .eax = 0
  bytes : Prefix t.mem (out.setWidth 64) i
  mem : Outside (out.setWidth 64) 0 len s.mem t.mem
  keeps : Keeps [.esi, .ecx] s t

theorem failureLoop_ok {s : State} {out : BitVec 32} {len : Nat}
    (hl : 0 < len) (h32 : len < 2 ^ 32) (hf : out.toNat + len ≤ 2 ^ 32)
    (hp : s.gpr .esi = out) (hc : s.gpr .ecx = BitVec.ofNat 32 len) (hz : s.gpr .eax = 0)
    (hw : ∀ i, i < len → InRegions s.wr (out.setWidth 64 + BitVec.ofNat 64 i) 1) :
    WP isa (.loop (.block failureStep) .ne) s fun t =>
      Spec.Rsa.bytesAt t.mem (out.setWidth 64) len = List.replicate len 0 ∧
      t.gpr .eax = 0 ∧ Outside (out.setWidth 64) 0 len s.mem t.mem ∧ Keeps [.esi, .ecx] s t := by
  have I0 : FailureInv out len 0 s s :=
    ⟨by simpa using hp, by simpa using hc, hz, by intro j hj; omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩
  refine WP.loop (M := isa) (fun k t => ∃ i, k = len - i ∧ i < len ∧ FailureInv out len i s t)
    ?_ len s ⟨0, rfl, hl, I0⟩
  rintro k t ⟨i, rfl, hi, I⟩
  refine WP.mono (failureStep_ok hi hf h32 I.pointer I.counter I.zero
    (by rw [I.keeps.2.2]; exact hw i hi) I.bytes) fun u ⟨P, C, Z, B, O, K⟩ => ?_
  have next : FailureInv out len (i + 1) s u :=
    ⟨P, C, by rw [K.1 _ (by decide), I.zero], B, I.mem.trans O, I.keeps.trans K⟩
  by_cases done : i + 1 = len
  · refine .inl ⟨?_, ?_, next.zero, next.mem, next.keeps⟩
    · simp only [eval, Z, done, decide_true, Option.map_some, Bool.not_true]
    · have H := prefix_spec (done ▸ next.bytes)
      exact H
  · refine .inr ⟨?_, len - (i + 1), by omega, i + 1, rfl, by omega, next⟩
    simp only [eval, Z, decide_eq_false done, Option.map_some, Bool.not_false]

end VG.Proof.Dsa.X86
