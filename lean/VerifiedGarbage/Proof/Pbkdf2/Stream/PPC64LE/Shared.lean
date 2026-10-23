module

public import VerifiedGarbage.Proof.Pbkdf2.Stream.PPC64LE.Iterate
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Hmac.Generic.Implies
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Impl.Pbkdf2.Stream.PPC64LE
import all Init.Data.Nat.Bitwise.Basic

/-!
# PBKDF2 over any streaming hash function on PPC64LE: the shared contract

`iterate`'s generic proof (`Iter.correct`) is written against `iterG`, with
the working space the code uses. Its constant time (`ct`) is the taint
analysis of `iterateBody` (checked for each hash function's code) after the
first block, which zero-extends `n`: `n` is public only in its low 32 bits,
so the two runs agree on the whole of `r5` only once correctness says what
the block leaves there (`RelCT.wpDep`). The proof is widened to the working
space of the shared contract (`Verified.widen`) and moved to it
(`generic_implies`), for any instance `I` of the hash function.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Stream.PPC64LE.Shared

open VG.PPC64LE
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Impl.Pbkdf2.Stream.PPC64LE.Iter (bytes)
open VG.Proof.MdStream.PPC64LE (Upd wp_lsl wp_lsr)

variable {H : Hash} (hH : HashOK H)

/-- What the first block of `iterate` does to the registers. -/
def ZextPost (s s' : State) : Prop :=
  s'.gpr .r5 = BitVec.ofNat 64 ((s.gpr .r5).setWidth 32).toNat ∧
    (∀ r, r ≠ .r0 → r ≠ .r5 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp

theorem zext_wp (s : State) :
    WP isa (.block (.mflr .r0 :: VG.Impl.Pbkdf2.Stream.PPC64LE.zextN)) s (ZextPost s) := by
  refine Proof.MdStream.PPC64LE.WP.cons exec_mflr (wp_lsl (by decide) fun s₁ x₁ =>
    wp_lsr (by decide) fun s₂ x₂ => WP.block_nil ⟨?_, fun r h0 h5 => ?_, ?_⟩)
  · rw [x₂.gpr, x₁.gpr, show (s.write .r0 s.lr).gpr .r5 = s.gpr .r5 from rfl,
      VG.Proof.Pbkdf2.Stream.PPC64LE.Iter.zext32]
  · rw [x₂.other r h5, x₁.other r h5]; simp only [State.write, h0, ite_false]
  · rw [x₂.sp, x₁.sp]; rfl

/-- `iterate` is constant time, given the taint analysis of its body. -/
theorem ct (SH : Spec.Hmac.StreamingHash) (Wi : Nat) {hc : VG.Taint.Hint taint.T}
    (hb : (taint.check (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7]) (VG.Impl.Pbkdf2.Stream.PPC64LE.iterateBody H)
      hc).isSome = true) :
    ConstantTime isa (iterG SH Wi 96).pre (iterG SH Wi 96).pub (VG.Impl.Pbkdf2.Stream.PPC64LE.iterate H) := by
  refine RelCT.constantTime (Q := fun _ _ => True) (RelCT.seq ?_ (RelCT.taint (A := taint)
    (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7]) (fun _ _ h => h) hb))
  have ag4 : ∀ s₁ s₂ : State, (iterG SH Wi 96).pre s₁ ∧ (iterG SH Wi 96).pre s₂ ∧ (iterG SH Wi 96).pub s₁ s₂ →
      taint.Agree (Taint.ofRegs [.r3, .r4, .r6, .r7]) s₁ s₂ := by
    rintro s₁ s₂ ⟨_, _, h3, h4, _, h6, h7, hsp⟩
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
  refine RelCT.mono (RelCT.wpDep (F := ZextPost) (RelCT.taint (A := taint) (Taint.ofRegs [.r3, .r4, .r6, .r7])
    ag4 (by taint_decide)) fun s₁ s₂ _ => ⟨zext_wp s₁, zext_wp s₂⟩) (fun _ _ h => h) ?_
  · rintro s₁' s₂' ⟨-, σ₁, σ₂, ⟨_, _, h3, h4, h5, h6, h7, hsp⟩, ⟨a5, ao, asp⟩, ⟨b5, bo, bsp⟩⟩
    refine ⟨by rw [asp, bsp, hsp], fun r hr => ?_⟩
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [ao _ (by decide) (by decide), bo _ (by decide) (by decide), h3]
    · rw [ao _ (by decide) (by decide), bo _ (by decide) (by decide), h4]
    · rw [a5, b5, h5]
    · rw [ao _ (by decide) (by decide), bo _ (by decide) (by decide), h6]
    · rw [ao _ (by decide) (by decide), bo _ (by decide) (by decide), h7]

variable {I : Spec.Hmac.Instance} (hSH : hH.SH = I.S)

theorem iterImp (hs : ∃ s, (I.iterateContract PPC64LE.abi 96).pre s) :
    (iterG I.S (8 * I.scratch) 96).Implies (I.iterateContract PPC64LE.abi 96) := by
  generic_implies [Spec.Hmac.Instance.iterateContract, Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig,
    iterG, PPC64LE.abi, PPC64LE.argRegs] using hs

include hSH in
/-- `iterate` against the shared contract, given its constant time. -/
theorem iterate (hfit : bytes H ≤ 8 * I.scratch)
    (ct : ConstantTime isa (iterG hH.SH (bytes H) 96).pre (iterG hH.SH (bytes H) 96).pub
      (VG.Impl.Pbkdf2.Stream.PPC64LE.iterate H))
    (hs : ∃ s, (I.iterateContract PPC64LE.abi 96).pre s) :
    Verified PPC64LE.target (VG.Impl.Pbkdf2.Stream.PPC64LE.iterate H) (I.iterateContract PPC64LE.abi 96) := by
  have imp := iterImp hs
  rw [← hSH] at imp
  have wide : ∀ s, (iterG hH.SH (8 * I.scratch) 96).pre s →
      (iterG hH.SH (bytes H) 96).pre (s.withRegions s.rd [⟨s.gpr .r6, hH.SH.digestBytes⟩,
        ⟨s.gpr .r7, bytes H⟩]) := by
    intro s ⟨h1, _, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
    exact ⟨h1, rfl, h3, h4.sub_right (Region.sub_prefix hfit), h5, h6.sub_right (Region.sub_prefix hfit),
      h7.sub_right (Region.sub_prefix hfit), h8, h9, h10, h11, h12.sub_right (Region.sub_prefix hfit)⟩
  have v : Verified PPC64LE.target (VG.Impl.Pbkdf2.Stream.PPC64LE.iterate H) (iterG hH.SH (bytes H) 96) :=
    ⟨fun s hs => by obtain ⟨t, s', he, h₁, h₂⟩ := Iter.correct hH hs; exact ⟨t, s', he, h₁, h₂⟩, ct,
      imp.sat_left.elim fun s h => ⟨_, wide s h⟩⟩
  refine (Verified.widen v (fun s => [⟨s.gpr .r6, hH.SH.digestBytes⟩, ⟨s.gpr .r7, bytes H⟩]) wide
      (fun _ h => ?_) (fun _ _ _ h => h) (fun _ _ _ _ h => h) imp.sat_left).of_implies imp
  obtain ⟨_, h2, _⟩ := h
  rw [h2]
  exact .cons ⟨rfl, Nat.le_refl _⟩ (.cons ⟨rfl, hfit⟩ .nil)

end VG.Proof.Pbkdf2.Stream.PPC64LE.Shared
