module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtFront
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtFront
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtSave
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The RSA private-key operation on PPC64LE: constant time, the front

The public data of a run (`dataOf`): the argument registers, the stack
arguments and `n`'s bytes. Two runs are related by `Two` (`MontCT.lean`)
for the same public data. The taint analysis keeps memory secret, so the
working space's address, from the stack, is pinned once loaded (`L1`), and
the front (`front_rel`) ends with `Front`.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE (Two Pins two_post two_taint)

/-- The public data of a run. -/
def dataOf (s : State) : List (BitVec 64) × List (BitVec 64) × List Byte :=
  (argRegs.map s.gpr, (List.range 10).map (stackArg s), Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)

/-- On entry. -/
def C0 (d : List (BitVec 64) × List (BitVec 64) × List Byte) (s : State) : Prop :=
  fnContract.pre s ∧ dataOf s = d

/-- What the public data fixes. -/
structure DataEq (s₀ s₀' : State) : Prop where
  r3 : s₀.gpr .r3 = s₀'.gpr .r3
  r4 : s₀.gpr .r4 = s₀'.gpr .r4
  r5 : s₀.gpr .r5 = s₀'.gpr .r5
  r6 : s₀.gpr .r6 = s₀'.gpr .r6
  r7 : s₀.gpr .r7 = s₀'.gpr .r7
  r8 : s₀.gpr .r8 = s₀'.gpr .r8
  r9 : s₀.gpr .r9 = s₀'.gpr .r9
  r10 : s₀.gpr .r10 = s₀'.gpr .r10
  sa : ∀ i < 10, stackArg s₀ i = stackArg s₀' i
  nb : Spec.Rsa.bytesAt s₀.mem (s₀.gpr .r5) (s₀.gpr .r6).toNat =
    Spec.Rsa.bytesAt s₀'.mem (s₀'.gpr .r5) (s₀'.gpr .r6).toNat

theorem dataEq_of {s₀ s₀' : State} (h : dataOf s₀ = dataOf s₀') : DataEq s₀ s₀' := by
  have h1 : argRegs.map s₀.gpr = argRegs.map s₀'.gpr := congrArg Prod.fst h
  have h2 : (List.range 10).map (stackArg s₀) = (List.range 10).map (stackArg s₀') :=
    congrArg (fun x => x.2.1) h
  have h3 := congrArg (fun x => x.2.2) h
  have m := List.map_inj_left.mp h1
  exact ⟨m _ (by decide), m _ (by decide), m _ (by decide), m _ (by decide), m _ (by decide), m _ (by decide),
    m _ (by decide), m _ (by decide), fun i hi => List.map_inj_left.mp h2 i (List.mem_range.mpr hi), h3⟩

theorem two_data {d : List (BitVec 64) × List (BitVec 64) × List Byte} {s₀ s₀' : State} (h : C0 d s₀)
    (h' : C0 d s₀') : DataEq s₀ s₀' := dataEq_of (h.2.trans h'.2.symm)

theorem pins_C0 : Pins C0 [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10] := by
  rintro d s₁ s₂ h₁ h₂ r hr
  have E := two_data h₁ h₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [E.r3, E.r4, E.r5, E.r6, E.r7, E.r8, E.r9, E.r10]

/-- After loading the working space's address. -/
def L1 (d : List (BitVec 64) × List (BitVec 64) × List Byte) (s : State) : Prop :=
  ∃ s₀, C0 d s₀ ∧ s.gpr .r11 = stackArg s₀ 8 ∧ Keep [.r11] s₀ s

theorem pins_L1 : Pins L1 [.r11, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10] := by
  rintro d s₁ s₂ ⟨s₀, h₀, a11, k⟩ ⟨s₀', h₀', b11, k'⟩ r hr
  have E := two_data h₀ h₀'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a11, b11, E.sa 8 (by decide)]
  all_goals rw [k.gpr _ (by decide), k'.gpr _ (by decide)]
  exacts [E.r3, E.r4, E.r5, E.r6, E.r7, E.r8, E.r9, E.r10]

/-- After the front. -/
def LF (d : List (BitVec 64) × List (BitVec 64) × List Byte) (s : State) : Prop := ∃ s₀, C0 d s₀ ∧ Front s₀ s

theorem pins_LF : Pins LF [.r10, .r11, .r21, .r23, .r27, .r28, .r29] := by
  rintro d s₁ s₂ ⟨s₀, h₀, F⟩ ⟨s₀', h₀', F'⟩ r hr
  have E := two_data h₀ h₀'
  have eS : cS s₀ = cS s₀' := E.sa 8 (by decide)
  have eX : cwX s₀ = cwX s₀' := by simp only [cwX, ck, E.r6]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [F.r10, F'.r10, eS, eX]
  · rw [F.r11, F'.r11, eX]
  · rw [F.r21, F'.r21, eS, eX]
  · rw [F.r23, F'.r23, eS]
  · rw [F.r27, F'.r27, eS, eX]
  · rw [F.r28, F'.r28, eX]
  · rw [F.r29, F'.r29, eX]

theorem loadS_L1 {d : List (BitVec 64) × List (BitVec 64) × List Byte} {s : State} (h : C0 d s) :
    WP isa (.block [.addSp .r11 160, .load .d .r11 .r11 0]) s (L1 d) := by
  have hp := h.1
  refine WP.mono (loadS_ok s ⟨⟨stackArgAddr s 0, 80⟩, List.mem_append_left _ (by rw [hp.2.1]; simp), ?_⟩)
    fun t ⟨⟨a11, _, _⟩, k⟩ => ⟨s, h, a11, k⟩
  show Region.Contains _ (s.sp + BitVec.ofNat 64 (32 + 8 * (8 + 8))) 8
  rw [show s.sp + BitVec.ofNat 64 (32 + 8 * (8 + 8)) = (s.sp + BitVec.ofNat 64 (32 + 8 * (8 + 0))) +
    BitVec.ofNat 64 64 by rw [BitVec.add_assoc]; rfl]
  exact Offset.contains_base _ (by omega) (by omega)

theorem front_rel : RelCT isa (Two C0) (.block (Crt.save ++ Crt.args ++ setupX)) (Two LF) := by
  refine two_post ?_ fun _ _ h => WP.mono (front_ok _ h.1) fun t ht => ⟨_, h, ht⟩
  unfold Crt.save
  simp only [List.append_assoc]
  exact RelCT.block_append (RelCT.seq (two_post (two_taint _ pins_C0 (by taint_decide)) fun _ _ h => loadS_L1 h)
    (two_taint _ pins_L1 (by taint_decide)))

end VG.Proof.Bignum.PPC64LE.Crt
