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
from which the taint analysis checks the checks (`prep`), whose loops count
`e_len`, `w` and `k`. After them, `Pw` fixes those registers and `r24`,
which holds `e`'s bits, a function of its bytes, which are public: the
power's loops and branches follow `e`'s bits, and nothing else branches on
memory.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Pub

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Impl.Bignum VG.Impl.Bignum.PPC64LE
  VG.Impl.Bignum.PPC64LE.PublicChecked
open VG.Proof.Bignum.PPC64LE (Two Pins two_post two_taint)

/-- On entry, with the public data and `e`'s bytes. -/
def C0 (a : PD × List Byte) (s : State) : Prop :=
  fnContract.pre s ∧ dataOf s = a.1 ∧ Spec.Rsa.bytesAt s.mem a.1.E a.1.L = a.2

/-- After `loadS`: what `saveRegs` and `setup` read. -/
def L1 (a : PD × List Byte) (s : State) : Prop :=
  s.gpr .r11 = a.1.S ∧ s.gpr .r3 = a.1.O ∧ s.gpr .r4 = BitVec.ofNat 64 a.1.k

/-- After `setup`, with `e`'s bytes. -/
def MidE (a : PD × List Byte) (s : State) : Prop := Mid a.1 s ∧ Spec.Rsa.bytesAt s.mem a.1.E a.1.L = a.2

/-- After the checks: what the power, the output and `restore` read, `e`'s
bits in `r24`, which are public. -/
def Pw (a : PD × List Byte) (s : State) : Prop :=
  s.gpr .r10 = off a.1.S (slot a.1.w 0) ∧ s.gpr .r11 = BitVec.ofNat 64 (2 * a.1.w) ∧
    s.gpr .r29 = BitVec.ofNat 64 (8 * (a.1.w + 2)) ∧ s.gpr .r23 = a.1.S ∧ s.gpr .r27 = off a.1.O 0 ∧
    s.gpr .r28 = BitVec.ofNat 64 a.1.k ∧ s.gpr .r24 = BitVec.ofNat 64 (sat (Spec.Rsa.os2ip a.2)) <<< 31

theorem pins_C0 : Pins C0 [.r3, .r4] := by
  rintro d s₁ s₂ ⟨-, h₁, -⟩ ⟨-, h₂, -⟩ r hr
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

theorem pins_MidE : Pins MidE [.r5, .r7, .r8, .r9, .r10, .r11, .r23, .r27, .r28, .r29] := by
  rintro d s₁ s₂ ⟨h₁, -⟩ ⟨h₂, -⟩ r hr
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

theorem pins_Pw : Pins Pw [.r10, .r11, .r23, .r24, .r27, .r28, .r29] := by
  rintro d s₁ s₂ ⟨a10, a11, a29, a23, a27, a28, a24⟩ ⟨b10, b11, b29, b23, b27, b28, b24⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a10, b10]
  · rw [a11, b11]
  · rw [a23, b23]
  · rw [a24, b24]
  · rw [a27, b27]
  · rw [a28, b28]
  · rw [a29, b29]

theorem loadS_L1 {a : PD × List Byte} {s : State} (h : C0 a s) : WP isa (.block loadS) s (L1 a) := by
  obtain ⟨d, eB⟩ := a
  obtain ⟨hp, rfl, -⟩ := h
  refine WP.mono (loadS_ok s ⟨stackArgs s, List.mem_append_left _ (by rw [hp.2.1]; simp),
    by simp [Region.Contains]⟩) fun t ⟨⟨a11, _, _⟩, k⟩ => ⟨a11, k.gpr .r3 (by decide), ?_⟩
  rw [k.gpr .r4 (by decide)]; simp [dataOf]

theorem front_rel : RelCT isa (Two C0) (.block (PublicChecked.save ++ setup)) (Two MidE) := by
  refine two_post ?_ fun ⟨d, eB⟩ _ h => by
    obtain ⟨hp, rfl, he⟩ := h
    exact WP.mono (front_ok hp) fun _ h => ⟨h.1, (front_e hp h.2.2.2).trans he⟩
  unfold PublicChecked.save
  rw [List.append_assoc]
  exact RelCT.block_append (RelCT.seq (two_post (two_taint _ pins_C0 (by taint_decide)) fun _ _ h => loadS_L1 h)
    (two_taint _ pins_L1 (by taint_decide)))

/-- The checks: `e`'s bits in `r24` are those of its bytes, which are public. -/
theorem prep_rel : RelCT isa (Two MidE) prep (Two Pw) := by
  refine two_post (two_taint _ pins_MidE (by taint_decide)) fun a s ⟨h, he⟩ =>
    WP.mono (prep_ok h) fun u ⟨t, h5, _, _, k6, _, k7⟩ => ?_
  have g : ∀ r ∈ [Reg.r11, .r23, .r24, .r27, .r28, .r29], u.gpr r = t.gpr r := fun r hr => by
    rw [k7.gpr r (by revert r hr; decide), k6.gpr r (by revert r hr; decide)]
  have k5 := h5.keep
  refine ⟨by rw [k7.gpr .r10 (by decide), k6.gpr .r10 (by decide)]; exact h5.r10, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g _ (by decide), k5.gpr .r11 (by decide)]; exact h.r11
  · rw [g _ (by decide), k5.gpr .r29 (by decide)]; exact h.r29
  · rw [g _ (by decide), k5.gpr .r23 (by decide)]; exact h.r23
  · rw [g _ (by decide), k5.gpr .r27 (by decide)]; exact h.r27
  · rw [g _ (by decide), k5.gpr .r28 (by decide)]; exact h.r28
  · rw [g _ (by decide), h5.r24, PD.ev, he]

theorem fn_rel : RelCT isa (Two C0) publicChecked fun _ _ => True := by
  unfold publicChecked
  exact RelCT.seq front_rel (RelCT.seq prep_rel (two_taint _ pins_Pw (by taint_decide)))

/-- Equal public data give equal bytes of `e`. -/
theorem e_eq {s t : State} {n : Nat} {p q : Addr} {a b : Addr} {l : Nat}
    (h : (Spec.Rsa.wordsAt s.mem p n).map (·.toNat) ++ (Spec.Rsa.bytesAt s.mem a l).map (·.toNat) =
      (Spec.Rsa.wordsAt t.mem q n).map (·.toNat) ++ (Spec.Rsa.bytesAt t.mem b l).map (·.toNat)) :
    Spec.Rsa.bytesAt t.mem b l = Spec.Rsa.bytesAt s.mem a l := by
  have h2 := (List.append_inj h (by simp [Spec.Rsa.wordsAt])).2
  exact ((List.map_inj_right fun x y h => BitVec.eq_of_toNat_eq h).mp h2).symm

theorem fn_ct : ConstantTime isa fnContract.pre fnContract.pub publicChecked :=
  RelCT.constantTime (fn_rel.mono (fun s t ⟨hs, ht, hsp, h3, h4, h5, h6, h7, h8, h9, _, h0, h1, hl⟩ =>
    ⟨(dataOf s, Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat), ⟨hs, rfl, rfl⟩,
      ⟨ht, by simp only [dataOf]; rw [h3, h4, h5, h7, h8, h9, h0, h1], by
        rw [← h5, ← h6, ← h7, ← h8] at hl; exact e_eq hl⟩, hsp⟩)
    fun _ _ h => h)

end VG.Proof.Bignum.PPC64LE.Pub
