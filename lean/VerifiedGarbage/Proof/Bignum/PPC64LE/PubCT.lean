module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.PubCorrect
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.PubCorrect
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# The RSA public-key operation on PPC64LE: constant time

The taint analysis treats memory as secret, so the working space's address,
which `loadS` loads from the stack, is secret to it although it is public.
Two runs are related by `Two` (`MontCT.lean`) at each step, both satisfying
the same predicate for the same public data `PD`: after `loadS` it fixes the
working space's address (`L1`), and after `setup` the registers `Mid` fixes,
from which the taint analysis checks the rest of the function. Nothing after
`setup` branches on memory: the loops count `e_len`, `w`, the 33 bits of the
exponent and `k`.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Pub

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Impl.Bignum VG.Impl.Bignum.PPC64LE
  VG.Impl.Bignum.PPC64LE.PublicChecked
open VG.Proof.Bignum.PPC64LE (Two Pins two_post two_taint)

/-- On entry. -/
def C0 (d : PD) (s : State) : Prop := fnContract.pre s ∧ dataOf s = d

/-- After `loadS`: what `saveRegs` and `setup` read. -/
def L1 (d : PD) (s : State) : Prop :=
  s.gpr .r11 = d.S ∧ s.gpr .r3 = d.O ∧ s.gpr .r4 = BitVec.ofNat 64 d.k

theorem pins_C0 : Pins C0 [.r3, .r4] := by
  rintro d s₁ s₂ ⟨-, h₁⟩ ⟨-, h₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (congrArg PD.O h₁).trans (congrArg PD.O h₂).symm
  · exact BitVec.eq_of_toNat_eq ((congrArg PD.k h₁).trans (congrArg PD.k h₂).symm)

theorem pins_L1 : Pins L1 [.r11, .r3, .r4] := by
  rintro d s₁ s₂ ⟨a11, a3, a4⟩ ⟨b11, b3, b4⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [a11, b11]
  · rw [a3, b3]
  · rw [a4, b4]

theorem pins_Mid : Pins Mid [.r5, .r7, .r8, .r9, .r10, .r11, .r23, .r27, .r28, .r29] := by
  rintro d s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h₁.r5, h₂.r5]
  · rw [h₁.r7, h₂.r7]
  · rw [h₁.r8, h₂.r8]
  · rw [h₁.r9, h₂.r9]
  · rw [h₁.r10, h₂.r10]
  · rw [h₁.r11, h₂.r11]
  · rw [h₁.r23, h₂.r23]
  · rw [h₁.r27, h₂.r27]
  · rw [h₁.r28, h₂.r28]
  · rw [h₁.r29, h₂.r29]

theorem loadS_L1 {d : PD} {s : State} (h : C0 d s) : WP isa (.block loadS) s (L1 d) := by
  obtain ⟨hp, rfl⟩ := h
  refine WP.mono (loadS_ok s ⟨stackArgs s, List.mem_append_left _ (by rw [hp.2.1]; simp),
    by simp [Region.Contains]⟩) fun t ⟨⟨a11, _, _⟩, k⟩ => ⟨a11, k.gpr .r3 (by decide), ?_⟩
  rw [k.gpr .r4 (by decide)]; simp [dataOf]

theorem front_rel : RelCT isa (Two C0) (.block (PublicChecked.save ++ setup)) (Two Mid) := by
  refine two_post ?_ fun _ _ h => by obtain ⟨hp, rfl⟩ := h; exact WP.mono (front_ok hp) fun _ h => h.1
  unfold PublicChecked.save
  rw [List.append_assoc]
  exact RelCT.block_append (RelCT.seq (two_post (two_taint _ pins_C0 (by taint_decide)) fun _ _ h => loadS_L1 h)
    (two_taint _ pins_L1 (by taint_decide)))

theorem fn_rel : RelCT isa (Two C0) publicChecked fun _ _ => True := by
  unfold publicChecked
  exact RelCT.seq front_rel (two_taint _ pins_Mid (by taint_decide))

theorem fn_ct : ConstantTime isa fnContract.pre fnContract.pub publicChecked :=
  RelCT.constantTime (fn_rel.mono (fun s t ⟨hs, ht, hsp, h3, h4, h5, _, h7, h8, h9, _, h0, h1, _⟩ =>
    ⟨dataOf s, ⟨hs, rfl⟩, ⟨ht, by simp only [dataOf]; rw [h3, h4, h5, h7, h8, h9, h0, h1]⟩, hsp⟩)
    fun _ _ h => h)

end VG.Proof.Bignum.PPC64LE.Pub
