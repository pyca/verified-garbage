module

public import VerifiedGarbage.Proof.Bignum.RISCV64.PubCorrect
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Bignum.RISCV64.PubCorrect
meta import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# The RSA public-key operation on RISC-V: constant time

`fn_ct`: two runs with the same public data (the pointers, the lengths,
`pre` and `e`) take the same path through the same addresses, as on PPC64LE:
taint checks of the code between states that pin the registers its addresses
and branches read, `e`'s bits among them, which are public.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.Pub

open VG VG.RISCV64 VG.RISCV64.Taint VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Bignum.RISCV64.PublicChecked
open VG.Proof.Bignum.RISCV64.Pre (Two Pins two_post two_taint)
open VG.Proof.Bignum (slot)

/-- On entry, with the public data and `e`'s bytes. -/
def C0 (a : PD × List Byte) (s : State) : Prop :=
  fnContract.pre s ∧ dataOf s = a.1 ∧ Spec.Rsa.bytesAt s.mem a.1.E a.1.L = a.2

/-- After `loadS`: what `saveRegs` and `setup` read. -/
def L1 (a : PD × List Byte) (s : State) : Prop :=
  s.gpr .t0 = a.1.S ∧ s.gpr .a0 = a.1.O ∧ s.gpr .a1 = BitVec.ofNat 64 a.1.k

/-- After `setup`, with `e`'s bytes. -/
def MidE (a : PD × List Byte) (s : State) : Prop := Mid a.1 s ∧ Spec.Rsa.bytesAt s.mem a.1.E a.1.L = a.2

/-- After the checks: what the power, the output and `restore` read, `e`'s
bits in `s7`, which are public. -/
def Pw (a : PD × List Byte) (s : State) : Prop :=
  s.gpr .a7 = off a.1.S (slot a.1.w 0) ∧ s.gpr .t0 = BitVec.ofNat 64 a.1.w ∧
    s.gpr .s5 = BitVec.ofNat 64 (8 * (a.1.w + 2)) ∧ s.gpr .s6 = a.1.S ∧ s.gpr .s10 = off a.1.O 0 ∧
    s.gpr .s11 = BitVec.ofNat 64 a.1.k ∧ s.gpr .s7 = BitVec.ofNat 64 (sat (Spec.Rsa.os2ip a.2)) <<< 31

theorem pins_C0 : Pins C0 [.a0, .a1] := by
  rintro d s₁ s₂ ⟨-, h₁, -⟩ ⟨-, h₂, -⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (congrArg PD.O h₁).trans (congrArg PD.O h₂).symm
  · exact BitVec.eq_of_toNat_eq ((congrArg PD.k h₁).trans (congrArg PD.k h₂).symm)

theorem pins_L1 : Pins L1 [.t0, .a0, .a1] := by
  rintro d s₁ s₂ ⟨a0', a0, a1⟩ ⟨b0', b0, b1⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [a0', b0']
  · rw [a0, b0]
  · rw [a1, b1]

theorem pins_MidE : Pins MidE [.a2, .a4, .a5, .a6, .a7, .t0, .s6, .s10, .s11, .s5] := by
  rintro d s₁ s₂ ⟨h₁, -⟩ ⟨h₂, -⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h₁.a2, h₂.a2]
  · rw [h₁.a4, h₂.a4]
  · rw [h₁.a5, h₂.a5]
  · rw [h₁.a6, h₂.a6]
  · rw [h₁.a7, h₂.a7]
  · rw [h₁.t0, h₂.t0]
  · rw [h₁.s6, h₂.s6]
  · rw [h₁.s10, h₂.s10]
  · rw [h₁.s11, h₂.s11]
  · rw [h₁.s5, h₂.s5]

theorem pins_Pw : Pins Pw [.a7, .t0, .s5, .s6, .s7, .s10, .s11] := by
  rintro d s₁ s₂ ⟨a7, a0, a5, a6, a10, a11, a7'⟩ ⟨b7, b0, b5, b6, b10, b11, b7'⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a7, b7]
  · rw [a0, b0]
  · rw [a5, b5]
  · rw [a6, b6]
  · rw [a7', b7']
  · rw [a10, b10]
  · rw [a11, b11]

theorem loadS_L1 {a : PD × List Byte} {s : State} (h : C0 a s) : WP isa (.block loadS) s (L1 a) := by
  obtain ⟨d, eB⟩ := a
  obtain ⟨hp, rfl, -⟩ := h
  have alsp := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  refine WP.mono (loadS_ok s ⟨stackArgs s, List.mem_append_left _ (by rw [hp.1]; simp),
    by simp [Region.Contains]⟩ (by omega)) fun t ⟨⟨a0', _, _⟩, k⟩ => ⟨a0', k.gpr (by decide), ?_⟩
  rw [k.gpr (by decide)]; simp [dataOf]

theorem front_rel : RelCT isa (Two C0) (.block (PublicChecked.save ++ setup)) (Two MidE) := by
  refine two_post ?_ fun ⟨d, eB⟩ _ h => by
    obtain ⟨hp, rfl, he⟩ := h
    exact WP.mono (front_ok hp) fun _ h => ⟨h.1, (front_e hp h.2.2.2).trans he⟩
  unfold PublicChecked.save
  rw [List.append_assoc]
  exact RelCT.block_append (RelCT.seq (two_post (two_taint _ pins_C0 (by taint_decide)) fun _ _ h => loadS_L1 h)
    (two_taint _ pins_L1 (by taint_decide)))

/-- The checks: `e`'s bits in `s7` are those of its bytes, which are public. -/
theorem prep_rel : RelCT isa (Two MidE) prep (Two Pw) := by
  refine two_post (two_taint _ pins_MidE (by taint_decide)) fun a s ⟨h, he⟩ =>
    WP.mono (prep_ok h) fun u ⟨t, h5, _, _, k6, _, k7⟩ => ?_
  have g : ∀ r ∈ [Reg.t0, .s5, .s6, .s7, .s10, .s11], u.gpr r = t.gpr r := fun r hr => by
    rw [k7.gpr (by revert r hr; decide), k6.gpr (by revert r hr; decide)]
  have k5 := h5.keep
  refine ⟨by rw [k7.gpr (by decide), k6.gpr (by decide)]; exact h5.a7, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g _ (by decide), k5.gpr (by decide)]; exact h.t0
  · rw [g _ (by decide), k5.gpr (by decide)]; exact h.s5
  · rw [g _ (by decide), k5.gpr (by decide)]; exact h.s6
  · rw [g _ (by decide), k5.gpr (by decide)]; exact h.s10
  · rw [g _ (by decide), k5.gpr (by decide)]; exact h.s11
  · rw [g _ (by decide), h5.s7, PD.ev, he]

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
  RelCT.constantTime (fn_rel.mono (fun s t ⟨hs, ht, hsp, h0, h1, h2, h3, h4, h5, h6, _, h8, h9, hl⟩ =>
    ⟨(dataOf s, Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat), ⟨hs, rfl, rfl⟩,
      ⟨ht, by simp only [dataOf]; rw [h0, h1, h2, h4, h5, h6, h8, h9], by
        rw [← h2, ← h3, ← h4, ← h5] at hl; exact e_eq hl⟩, hsp⟩)
    fun _ _ h => h)

end VG.Proof.Bignum.RISCV64.Pub
