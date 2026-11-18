module

public import VerifiedGarbage.Proof.MlDsa.X86.Pack.BitPack
import VerifiedGarbage.Proof.MlDsa.Pack.Arith
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.MlDsa.X86.Pack.BitPack
meta import VerifiedGarbage.Proof.MlDsa.Pack.Arith
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
import VerifiedGarbage.Proof.MlDsa.Arith.Mem
meta import VerifiedGarbage.Proof.MlDsa.Arith.Mem
public import VerifiedGarbage.Proof.MlDsa.X86.Round.Hint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlDsa.X86.Round.Hint
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.MlDsa.X86.Round.Bits
meta import VerifiedGarbage.Proof.MlDsa.X86.Round.Bits
import VerifiedGarbage.Proof.MlKem.X86.Common
import VerifiedGarbage.Proof.MlDsa.X86.Sample.RejNtt
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.MlKem.X86.Common
meta import VerifiedGarbage.Proof.MlDsa.X86.Sample.RejNtt
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.MlDsa.Sample.LeNat
meta import VerifiedGarbage.Proof.MlDsa.Sample.LeNat
public import VerifiedGarbage.Impl.MlDsa.X86.Sample.Ball
public import VerifiedGarbage.Proof.MlDsa.X86.Sample.Sponge
public import VerifiedGarbage.Proof.MlDsa.Sample.ExpandMask
meta import VerifiedGarbage.Impl.MlDsa.X86.Sample.Ball
meta import VerifiedGarbage.Proof.MlDsa.X86.Sample.Sponge
meta import VerifiedGarbage.Proof.MlDsa.Sample.ExpandMask
import VerifiedGarbage.Proof.MlDsa.Sample.Word
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.PlainSimp
meta import VerifiedGarbage.Proof.MlDsa.Sample.Word
meta import VerifiedGarbage.Proof.Framework.InstancePriority
meta import VerifiedGarbage.Proof.Framework.GetElem
meta import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `MlDsa.X86.Round.HintF`, which the modules that import this one used -/

section

/-! ### `MlDsa.X86.Round.NormLt`, which the modules that import this one used -/

section

/-! ### `MlDsa.X86.Sample.BallTop`, which the modules that import this one used -/

section

/-! ### `MlDsa.X86.Sample.BallLoop`, which only this module used -/

section

/-! ### `MlDsa.X86.Sample.Ball`, which only this module used -/

section

/-! ### `MlDsa.Sample.Signs`, which this module and modules that import it used -/

section

/-!
# ML-DSA: the sign bits of `SampleInBall` in two 32-bit words

An implementation with 32-bit words keeps the sign bits of `SampleInBall` not
yet used, the first 8 bytes of the output as a little-endian integer `S`
shifted right by the number `t` of signs used, as two words: `S / 2^t` (modulo
`2³²`) and `S / 2^(t+32)`. They start as the two little-endian words of the
bytes (`readW_lo`, `readW_hi`); the next sign is the low bit of the first
(`signBit_eq`); and shifting the pair right by one bit is the first shifted
right by one plus the low bit of the second rotated to the top
(`signs_shift`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Sample

open VG.Spec.MlDsa

/-- A value less than `2ⁿ`, rotated right by `n`, is shifted left by `32 - n`. -/
theorem rotr_small32 (x : BitVec 32) {n : Nat} (h0 : 0 < n) (h : n < 32) (hx : x.toNat < 2 ^ n) :
    (x.rotateRight n).toNat = x.toNat * 2 ^ (32 - n) := by
  rw [BitVec.rotateRight_def, BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft]
  simp only [Nat.mod_eq_of_lt h]
  rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hx, Nat.zero_or, Nat.shiftLeft_eq]
  apply Nat.mod_eq_of_lt
  have : x.toNat * 2 ^ (32 - n) < 2 ^ n * 2 ^ (32 - n) := Nat.mul_lt_mul_of_pos_right hx (Nat.two_pow_pos _)
  rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)] at this
  exact this

theorem and_one_toNat (x : BitVec 32) : (x &&& 1).toNat = x.toNat % 2 := by
  rw [BitVec.toNat_and, show (1 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod]

/-- The high word shifted right by one bit. -/
theorem signs_shift_hi {S : Nat} (hS : S < 2 ^ 64) (t : Nat) :
    BitVec.ofNat 32 (S / 2 ^ (t + 32)) >>> 1 = BitVec.ofNat 32 (S / 2 ^ (t + 1 + 32)) := by
  have e : S / 2 ^ (t + 1 + 32) = S / 2 ^ (t + 32) / 2 := by
    rw [show t + 1 + 32 = t + 32 + 1 by omega_using [], Nat.pow_succ, Nat.div_div_eq_div_mul]
  have hl : S / 2 ^ (t + 32) < 2 ^ 32 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
    exact Nat.lt_of_lt_of_le hS (Nat.pow_le_pow_right (by decide) (by omega_using []))
  rw [e]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt (by omega_using [hl])]

/-- The word at `a` whose bits `j < 32` are the bits `o + j` of `X`. -/
theorem readW_bits (m : Mem) (a : Addr) (X : List Byte) (o : Nat)
    (hb : ∀ b < 4, m (a + BitVec.ofNat 64 b) = X.getD (o / 8 + b) 0) (ho : o % 8 = 0) :
    m.readW a 32 = BitVec.ofNat 32 (leNat X / 2 ^ o) := by
  apply BitVec.eq_of_toNat_eq
  apply Nat.eq_of_testBit_eq
  intro j
  rw [BitVec.toNat_ofNat, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hj : j < 32
  · rw [← BitVec.getLsbD, readW32_getLsbD m a hj, hb (j / 8) (by omega_using [hj]), testBit_leNat,
      show (j + o) / 8 = o / 8 + j / 8 by omega_using [ho], show (j + o) % 8 = j % 8 by omega_using [ho]]
    simp [hj]
  · simp only [hj, decide_false, Bool.false_and]
    exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (m.readW a 32).isLt (Nat.pow_le_pow_right (by decide) (by omega_using [hj])))

/-- The first word of the first 8 bytes of `X`. -/
theorem readW_lo (m : Mem) (a : Addr) (X : List Byte) (hb : ∀ b < 8, m (a + BitVec.ofNat 64 b) = X.getD b 0) :
    m.readW a 32 = BitVec.ofNat 32 (leNat (X.take 8) / 2 ^ 0) :=
  readW_bits m a (X.take 8) 0 (fun b h => by
    rw [Nat.zero_div, Nat.zero_add, hb b (by omega_using [h]), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega_using [h])])
    rfl

/-- The second word of the first 8 bytes of `X`. -/
theorem readW_hi (m : Mem) (a : Addr) (X : List Byte) (hb : ∀ b < 8, m (a + BitVec.ofNat 64 b) = X.getD b 0) :
    m.readW (a + 4) 32 = BitVec.ofNat 32 (leNat (X.take 8) / 2 ^ (0 + 32)) :=
  readW_bits m (a + 4) (X.take 8) 32 (fun b h => by
    rw [BitVec.add_assoc, show (4 : BitVec 64) + BitVec.ofNat 64 b = BitVec.ofNat 64 (4 + b) by
      rw [BitVec.ofNat_add]; rfl, hb (4 + b) (by omega_using [h]), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_take_of_lt (by omega_using [h])]) rfl

/-- The next sign: the low bit of the first word. -/
theorem signBit_eq (S t : Nat) :
    (BitVec.ofNat 32 (S / 2 ^ t) &&& 1 == 0) = !(S.testBit t) := by
  have e : (BitVec.ofNat 32 (S / 2 ^ t) &&& 1).toNat = S / 2 ^ t % 2 := by
    rw [and_one_toNat, BitVec.toNat_ofNat]
    omega_using []
  rw [testBit_eq]
  by_cases h : S / 2 ^ t % 2 = 1
  · simp only [h, decide_true, Bool.not_true, beq_eq_false_iff_ne, ne_eq]
    intro h'; rw [h'] at e; simp at e; omega_using [h, e]
  · simp only [h, decide_false, Bool.not_false, beq_iff_eq]
    exact BitVec.eq_of_toNat_eq (by rw [e]; simp; omega_using [h])

/-- The pair of words shifted right by one bit. -/
theorem signs_shift (S t : Nat) :
    BitVec.ofNat 32 (S / 2 ^ t) >>> 1 + (BitVec.ofNat 32 (S / 2 ^ (t + 32)) &&& 1).rotateRight 1 =
      BitVec.ofNat 32 (S / 2 ^ (t + 1)) := by
  have e1 : S / 2 ^ (t + 1) = S / 2 ^ t / 2 := by rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
  have e2 : S / 2 ^ (t + 32) = S / 2 ^ (t + 1) / 2 ^ 31 := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  generalize S / 2 ^ t = A at e1
  rw [e2, e1]
  generalize hB : A / 2 = B
  have hm : (BitVec.ofNat 32 (B / 2 ^ 31) &&& 1).toNat = B / 2 ^ 31 % 2 := by
    rw [and_one_toNat, BitVec.toNat_ofNat]
    omega_using []
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    rotr_small32 _ (by decide) (by decide) (by rw [hm]; omega_using []), hm, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega_using [hB]

end VG.Proof.MlDsa.Sample

end

end

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_sample_in_ball`, the state of the loop

The body is the SHAKE256 output of `c̃` at `scratch + 840` (`sponge_piece`),
`c` zeroed (`zero_piece`), the setup of the loop (`setup_piece`): `i = 256 -
τ`, and the sign bits `S` (the first 8 bytes of the output, as a little-endian
integer) in the argument slots of `len` and `tau` as two words; then the 264
iterations of the loop (`BallLoop.lean`). Iteration `k` starts from the state
`st B τ k = bFold τ (signs X) (0, 256 - τ) ((X.drop 8).take k)` of
`SampleInBall`'s loop (`Proof/MlDsa/Sample/Ball.lean`): the polynomial at `c`,
`i` in `edi`, and the `t = i + τ - 256` signs used shifted out of the words
(`BI`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Sample.Ball

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86
open VG.Proof.MlDsa.X86.Sample
open VG.Proof.MlDsa.Sample
open VG.Impl.MlDsa.X86.Sample (argOp bZero bSetup qImm sponge outOff)
open VG.Spec.MlDsa (Zq q H n ofInt IPoly)
open VG.Proof.MlDsa (coeffAt ballParams)
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.X86.Sample (cR E1)

/-- The layout: `sampleInBall(ctilde, len, tau, c, scratch)`, `len` bytes of
`c̃`, 272 bytes of SHAKE256. -/
def L : Lay := { nA := 5, iA := 3, iS := 4, rate := 136, outlen := 272, mlen := none }

theorem hL : L.Ok :=
  ⟨by decide, by decide, by decide, by decide, by decide, fun k hk => by simp [L] at hk,
    ⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩⟩

/-- `τ`. -/
abbrev τ (s₀ : State) : Nat := (arg s₀ 2).toNat

/-- The precondition. -/
def QPre (s₀ : State) : Prop := Pre L s₀ ∧ ((arg s₀ 1).toNat, τ s₀) ∈ ballParams

/-- The pointers, `esp` and `c̃` agree. -/
def QPub (s₀ s₀' : State) : Prop := PubP L s₀ s₀' ∧ L.Msg s₀ = L.Msg s₀'

theorem QPre.τ_le {s₀ : State} (hp : QPre s₀) : τ s₀ ≤ 60 := by
  have h := hp.2
  simp only [ballParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  omega_arith

/-! ## The loop of `SampleInBall`, from the message -/

/-- The output. -/
abbrev Xb (B : List Byte) : List Byte := H B 272

/-- The sign bits, as an integer. -/
abbrev Sg (B : List Byte) : Nat := leNat ((Xb B).take 8)

/-- The state of the loop after `k` iterations. -/
abbrev st (B : List Byte) (τ : Nat) (k : Nat) : IPoly × Nat :=
  bFold τ (signs (Xb B)) (Vector.replicate n 0, 256 - τ) (((Xb B).drop 8).take k)

/-- The byte of iteration `k`. -/
abbrev jb (B : List Byte) (k : Nat) : Byte := (Xb B).getD (8 + k) 0

theorem out_eq (s₀ : State) : L.out s₀ = Xb (L.Msg s₀) := (H_eq _ _).symm

theorem Xb_length (B : List Byte) : (Xb B).length = 272 := H_length _ _

theorem st_zero (B : List Byte) (τ : Nat) : st B τ 0 = (Vector.replicate n 0, 256 - τ) := by
  simp [st, bFold]

theorem st_succ (B : List Byte) (τ : Nat) {k : Nat} (hk : k < 264) :
    st B τ (k + 1) = bStep τ (signs (Xb B)) (st B τ k) (jb B k) := by
  have hl : ((Xb B).drop 8).length = 264 := by rw [List.length_drop, Xb_length]
  simp only [st]
  rw [List.take_add_one, List.getElem?_eq_getElem (by rw [hl]; exact hk), Option.toList_some, bFold_snoc]
  congr 1
  rw [jb, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [Xb_length]; omega_arith), Option.getD_some,
    List.getElem_drop]

theorem st_le (B : List Byte) (τ k : Nat) : (st B τ k).2 ≤ 256 := bFold_le (by simp [n]) _

theorem st_ge (B : List Byte) (τ k : Nat) : 256 - τ ≤ (st B τ k).2 :=
  bFold_ge (Vector.replicate n 0, 256 - τ) _

/-! ## The state of the loop -/

/-- Iteration `k`, with the loop's state `S`. -/
structure BI (s₀ : State) (k : Nat) (S : IPoly × Nat) (s : State) : Prop extends Base L s₀ s where
  out : ∀ p < 272, s.mem (L.sA s₀ + BitVec.ofNat 64 (840 + p)) = (Xb (L.Msg s₀)).getD p 0
  esi : s.gpr .esi = L.sP s₀ + BitVec.ofNat 32 (848 + k)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (264 - k)
  ebp : s.gpr .ebp = L.aP s₀
  edi : s.gpr .edi = BitVec.ofNat 32 S.2
  poly : ∀ j < 256, coeffAt s.mem (L.aA s₀) j = zw (ofInt S.1[j]!)
  lo : s.mem.readW (argAddr s₀ 1) 32 = BitVec.ofNat 32 (Sg (L.Msg s₀) / 2 ^ (S.2 + τ s₀ - 256))
  hi : s.mem.readW (argAddr s₀ 2) 32 = BitVec.ofNat 32 (Sg (L.Msg s₀) / 2 ^ (S.2 + τ s₀ - 256 + 32))

/-! ## `c` zeroed -/

/-- After `k` words of `c`. -/
structure ZI (s₀ : State) (k : Nat) (s : State) : Prop extends Out L s₀ s where
  ebp : s.gpr .ebp = L.aP s₀
  eax : s.gpr .eax = 0
  edi : s.gpr .edi = L.aP s₀ + BitVec.ofNat 32 (4 * k)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (256 - k)
  zero : ∀ j < k, coeffAt s.mem (L.aA s₀) j = 0

theorem zinit_piece : Piece QPre QPub (Out L) (ZI · 0)
    (.block [.mov .ebp (.mem (argOp 3)), .mov .eax (.imm 0), .mov .edi (.reg .ebp), .mov .ecx (.imm 256)]) := by
  refine Piece.taint [.esp] (fun s₀ s hp h => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_) (by native_taint_decide)
  · have a₃ := h.argEa (i := 3)
    have i₃ := h.argIn hp.1 (i := 3) (by decide)
    have v₃ := h.args 3 (by decide)
    simp only [Nat.reduceMul, Nat.reduceAdd] at a₃
    apply WP.of_runBlock
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceAdd, Nat.reduceMul, argOp, at_, runBlock_cons, runStep_some, runBlock_nil, exec,
      readSrc, State.ea, State.load32, State.setReg, Option.map_some, a₃, i₃, v₃, 
      Option.some.injEq, exists_eq_left']
    exact ⟨⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, h.args, by simp [h.esi]⟩, h.out⟩, by simp; rfl, by simp,
      by simp; rfl, by simp, fun j hj => absurd hj (by omega_arith)⟩
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.esp, h'.esp, hq.1.e1]

theorem zstep {s₀ : State} (hp : QPre s₀) {k : Nat} (hk : k < 256) {s : State} (h : ZI s₀ k s) :
    WP isa (.block [.store (at_ .edi 0) .eax, .alu .add .edi (.imm 4), .alu .sub .ecx (.imm 1)]) s
      fun s' => ZI s₀ (k + 1) s' ∧ eval .ne s' = some (decide (k + 1 < 256)) := by
  have ha := hp.1.a_fit
  have ea : (L.aP s₀ + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 0).setWidth 64 = coeffAddr (L.aA s₀) k := by
    rw [ea_add (by simp only [L] at ha ⊢; omega_arith)]; rfl
  have hin : InRegions s.wr (coeffAddr (L.aA s₀) k) 4 := hp.1.inA h.wr hk
  have fa : Frame [L.aR s₀] s.mem (s.mem.writeW (coeffAddr (L.aA s₀) k) (0 : BitVec 32)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (coeff_contains _ hk)
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, at_, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    State.ea, State.store32, State.setReg, arithFlags, State.setFlags, Option.bind_some, h.edi, h.eax, ea, hin,
    Option.some.injEq, exists_eq_left']
  refine ⟨⟨⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame.writeW (r := L.aR s₀) (by simp) _ (coeff_contains _ hk)⟩,
    args_frame hp.1 h.args fa (by simp only [List.mem_singleton, forall_eq]; exact hp.1.a_g.symm),
    by simp [h.esi]⟩, fun p hp' => ?_⟩, by simp [h.ebp], by simp [h.eax], ?_, ?_, fun j hj => ?_⟩, ?_⟩
  · refine (fa _ fun r hr hc => ?_).trans (h.out p hp')
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.1.a_s _ hc ((hp.1.sub_s (o := 840 + p) (n := 1) (by simp only [L] at hp' ⊢; omega_arith)) _
      (Region.contains_self _ _))
  · simp only [ite_true]
    rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, add_ofNat_add]; congr 2
  · simp only [ite_true, h.ecx]
    exact cnt_next hk
  · rw [coeffAt_writeW _ _ (by omega_arith) hk]
    by_cases e : k = j
    · rw [ifT e]
    · rw [ifF e]; exact h.zero j (by omega_arith)
  · simp only [eval, h.ecx]
    exact cnt_ne hk (by omega_arith)

theorem zero_piece : Piece QPre QPub (Out L) (ZI · 256) bZero :=
  Piece.seq zinit_piece (Piece.countLoop (by decide) (fun k s₀ s => ZI s₀ k s) [.edi]
    (fun k hk s₀ s hp h => zstep hp hk h)
    (fun k _ s₀ s₀' s s' _ _ hq h h' r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      rw [h.edi, h'.edi, hq.1.aP hL]) (by native_taint_decide))

/-! ## The setup of the loop -/

theorem argAddr_eq {s₀ : State} (hp : QPre s₀) {i : Nat} (hi : i < 5) :
    argAddr s₀ i = (E0 s₀).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) :=
  ea_off (by have := hp.1.sp'; simp only [L, E0] at this ⊢; omega_arith)

/-- The two argument slots of the sign bits, apart. -/
theorem slots_sep {s₀ : State} (hp : QPre s₀) : Mem.Sep (argAddr s₀ 1) 4 (argAddr s₀ 2) 4 := by
  rw [argAddr_eq hp (by decide), argAddr_eq hp (by decide)]
  exact Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)

theorem setup_piece : Piece QPre QPub (ZI · 256) (fun s₀ s => BI s₀ 0 (st (L.Msg s₀) (τ s₀) 0) s)
    (.block bSetup) := by
  refine Piece.taint [.esp, .esi] (fun s₀ s hp h => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_)
    (by native_taint_decide)
  · have hs := hp.1.s_fit
    have a₁ := h.argEa (i := 1)
    have a₂ := h.argEa (i := 2)
    have i₂ := h.argIn hp.1 (i := 2) (by decide)
    have v₂ := h.args 2 (by decide)
    have w₁ := h.argInW hp.1 (i := 1) (by decide)
    have w₂ := h.argInW hp.1 (i := 2) (by decide)
    simp only [Nat.reduceMul, Nat.reduceAdd] at a₁ a₂
    have e0 : (L.sP s₀ + BitVec.ofNat 32 840).setWidth 64 = L.sA s₀ + BitVec.ofNat 64 840 := hp.1.off_eq (by omega_arith)
    have e4 : (L.sP s₀ + BitVec.ofNat 32 844).setWidth 64 = L.sA s₀ + BitVec.ofNat 64 844 := hp.1.off_eq (by omega_arith)
    have r0 := hp.1.inS' h.wr (o := 840) (n := 4) (by omega_arith)
    have r4 := hp.1.inS' h.wr (o := 844) (n := 4) (by omega_arith)
    have hb : ∀ b < 8, s.mem (L.sA s₀ + BitVec.ofNat 64 840 + BitVec.ofNat 64 b) = (Xb (L.Msg s₀)).getD b 0 :=
      fun b hb => by rw [BitVec.add_assoc, ← BitVec.ofNat_add, h.out b (by simp only [L]; omega_arith), out_eq]
    have vlo := readW_lo s.mem _ _ hb
    have vhi := readW_hi s.mem _ _ hb
    rw [BitVec.add_assoc, show BitVec.ofNat 64 840 + (4 : BitVec 64) = BitVec.ofNat 64 844 from rfl] at vhi
    have hτ := hp.τ_le
    have fin : ∀ s' : State, s'.gpr .esp = s.gpr .esp → s'.gpr .esi = L.sP s₀ + BitVec.ofNat 32 848 →
        s'.gpr .ecx = BitVec.ofNat 32 264 → s'.gpr .ebp = s.gpr .ebp → s'.gpr .edi = 256 - arg s₀ 2 →
        s'.rd = s.rd → s'.wr = s.wr →
        s'.mem = (s.mem.writeW (argAddr s₀ 1) (BitVec.ofNat 32 (Sg (L.Msg s₀) / 2 ^ 0))).writeW (argAddr s₀ 2)
          (BitVec.ofNat 32 (Sg (L.Msg s₀) / 2 ^ (0 + 32))) →
        BI s₀ 0 (st (L.Msg s₀) (τ s₀) 0) s' := by
      intro s' e1 e2 e3 e4 e5 e6 e7 e8
      have f₁ : Frame [L.gR s₀] s.mem s'.mem := by
        rw [e8]
        exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (arg_contains (n := 5) (by decide) hp.1.sp')).writeW
          (List.mem_singleton_self _) _ (arg_contains (n := 5) (by decide) hp.1.sp')
      rw [st_zero]
      refine ⟨⟨by rw [e1, h.esp], by rw [e6, h.rd], by rw [e7, h.wr], h.frame.trans (f₁.mono (by simp))⟩,
        fun p hp' => ?_, e2, e3, by rw [e4, h.ebp], ?_, fun j hj => ?_, ?_, ?_⟩
      · rw [f₁.bytes (R := ⟨L.sA s₀, 2048⟩) (by simp only [List.mem_singleton, forall_eq]; exact hp.1.s_g)
          (show (2048 : Nat) ≤ 2 ^ 64 by decide) (show 840 + p < 2048 by omega_arith)]
        rw [h.out p hp', out_eq]
      · rw [e5]
        exact eq_ofNat_of_toNat (by
          rw [BitVec.toNat_sub, show (256 : BitVec 32).toNat = 256 from rfl]
          simp only [τ] at hτ ⊢
          omega_arith)
      · rw [coeffAt_eq, f₁.readW (coeff_contains _ hj) (by simp only [List.mem_singleton, forall_eq]; exact hp.1.a_g)
          (by decide), ← coeffAt_eq, h.zero j hj,
          getElem!_pos (Vector.replicate n (0 : Int)) j (by simp only [n]; omega_arith), Vector.getElem_replicate]
        decide
      · rw [e8, Mem.readW_writeW_sep (slots_sep hp) (by decide), Mem.readW_writeW_self32,
          show 256 - τ s₀ + τ s₀ - 256 = 0 by omega_arith]
      · rw [e8, Mem.readW_writeW_self32, show 256 - τ s₀ + τ s₀ - 256 = 0 by omega_arith]
    apply WP.of_runBlock
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceMul, Nat.reducePow, bSetup, argOp, outOff, at_, runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu, readSrc, State.ea, State.load32, State.store32, State.setReg, arithFlags, State.setFlags,
      Option.map_some, Option.bind_some, h.esi, a₁, a₂, i₂, v₂, w₁, w₂, e0, e4, r0, r4, vlo, vhi, Nat.reduceAdd,
      Option.some.injEq, exists_eq_left']
    exact fin _ (by simp) (by simp) (by simp) (by simp) (by simp) rfl rfl rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h.esp, h'.esp, hq.1.e1]
    · rw [h.esi, h'.esi, hq.1.sP hL]

end VG.Proof.MlDsa.X86.Sample.Ball

end

end

/-!
# ML-DSA on x86 (32-bit): the loop of `vg_mldsa_sample_in_ball`

Iteration `k` takes the byte `j` of the output: while `i < 256` (`cmp_piece`),
if `j ≤ i`, it copies `c[j]` to `c[i]` and tests the next sign bit, the low
bit of the first word (`move_ok`); stores `±1` to `c[j]` (`sign_piece`) and
shifts the two words right by one bit (`shift_ok`), incrementing `i`: `bStep`
of `Proof/MlDsa/Sample/Ball.lean`. Its branches and addresses depend on `i`,
`j` and the sign bits, functions of `c̃`, which agree in two runs with the
same `c̃` (`QPub`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Sample.Ball

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86
open VG.Proof.MlDsa.X86.Sample
open VG.Proof.MlDsa.Sample
open VG.Impl.MlDsa.X86.Sample (argOp bMove bShift bSet bTry bBody qImm)
open VG.Spec.MlDsa (Zq q H n ofInt IPoly)
open VG.Proof.MlDsa (coeffAt)
open VG.Proof.MlDsa.X86.Sample.RejNtt (nil_piece)

/-- The state of iteration `k`. -/
abbrev S' (s₀ : State) (k : Nat) : IPoly × Nat := st (L.Msg s₀) (τ s₀) k

/-- The byte of iteration `k`. -/
abbrev j' (s₀ : State) (k : Nat) : Nat := (jb (L.Msg s₀) k).toNat

/-- The signs used before iteration `k`. -/
abbrev t' (s₀ : State) (k : Nat) : Nat := (S' s₀ k).2 + τ s₀ - 256

/-- The sign bits. -/
abbrev G (s₀ : State) : Nat := Sg (L.Msg s₀)

/-- The coefficient iteration `k` sets `c[j]` to. -/
abbrev sg (s₀ : State) (k : Nat) : Int := if (signs (Xb (L.Msg s₀))).getD (t' s₀ k) false then -1 else 1

theorem G_lt (s₀ : State) : G s₀ < 2 ^ 64 := by
  have := leNat_lt ((Xb (L.Msg s₀)).take 8)
  rwa [List.length_take, Xb_length, show min 8 272 = 8 from rfl] at this

theorem sg_eq (s₀ : State) (k : Nat) : sg s₀ k = if (G s₀).testBit (t' s₀ k) then -1 else 1 := by
  simp only [sg, signs_getD]

/-- The polynomial with `c[i] ← c[j]`. -/
abbrev P1 (s₀ : State) (k : Nat) : IPoly := (S' s₀ k).1.set! (S' s₀ k).2 (S' s₀ k).1[j' s₀ k]!

/-- After `c[i] ← c[j]`, with the next sign bit in `ebx` (and ZF). -/
structure M1 (s₀ : State) (k : Nat) (s : State) : Prop extends Base L s₀ s where
  out : ∀ p < 272, s.mem (L.sA s₀ + BitVec.ofNat 64 (840 + p)) = (Xb (L.Msg s₀)).getD p 0
  esi : s.gpr .esi = L.sP s₀ + BitVec.ofNat 32 (848 + k)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (264 - k)
  ebp : s.gpr .ebp = L.aP s₀
  edi : s.gpr .edi = BitVec.ofNat 32 (S' s₀ k).2
  eax : s.gpr .eax = L.aP s₀ + BitVec.ofNat 32 (4 * j' s₀ k)
  poly : ∀ jj < 256, coeffAt s.mem (L.aA s₀) jj = zw (ofInt (P1 s₀ k)[jj]!)
  lo : s.mem.readW (argAddr s₀ 1) 32 = BitVec.ofNat 32 (G s₀ / 2 ^ t' s₀ k)
  hi : s.mem.readW (argAddr s₀ 2) 32 = BitVec.ofNat 32 (G s₀ / 2 ^ (t' s₀ k + 32))
  ebx : s.gpr .ebx = BitVec.ofNat 32 (G s₀ / 2 ^ t' s₀ k)
  lt : (S' s₀ k).2 < 256
  le : j' s₀ k ≤ (S' s₀ k).2

/-! ## Addresses -/

theorem quad_add (x p : BitVec 32) (m : Nat) (hx : x = BitVec.ofNat 32 m) :
    x + x + (x + x) + p = p + BitVec.ofNat 32 (4 * m) := by
  rw [hx, ofNat_add_ofNat, ofNat_add_ofNat, BitVec.add_comm]
  congr 2; omega_arith

theorem coef_ea {s₀ : State} (hp : QPre s₀) {i : Nat} (hi : i < 256) :
    (L.aP s₀ + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0).setWidth 64 = coeffAddr (L.aA s₀) i := by
  have ha := hp.1.a_fit
  rw [ea_add (by simp only [L] at ha ⊢; omega_arith)]; rfl

theorem coef_in {s₀ s : State} (hp : QPre s₀) (h : Base L s₀ s) {i : Nat} (hi : i < 256) :
    InRegions (s.rd ++ s.wr) (coeffAddr (L.aA s₀) i) 4 :=
  let ⟨r, hr, hc⟩ := hp.1.inA h.wr hi; ⟨r, List.mem_append_right _ hr, hc⟩

theorem coef_arg_sep {s₀ : State} (hp : QPre s₀) {i a : Nat} (hi : i < 256) (ha : a < 5) :
    Mem.Sep (argAddr s₀ a) 4 (coeffAddr (L.aA s₀) i) 4 :=
  fun x h₁ h₂ => hp.1.a_g x ((coeff_contains _ hi).byte h₂) ((arg_contains (n := 5) ha hp.1.sp').byte h₁)

/-! ## Moving `c[j]` to `c[i]` -/

theorem move_ok {s₀ : State} (hp : QPre s₀) {k : Nat} {s : State} (h : BI s₀ k (S' s₀ k) s)
    (hlt : (S' s₀ k).2 < 256) (hax : s.gpr .eax = BitVec.ofNat 32 (j' s₀ k)) (hle : j' s₀ k ≤ (S' s₀ k).2) :
    WP isa (.block bMove) s fun s' => M1 s₀ k s' ∧ eval .e s' = some (!(G s₀).testBit (t' s₀ k)) := by
  have hj : j' s₀ k < 256 := by omega_arith
  have eaj := coef_ea hp hj
  have eai := coef_ea hp hlt
  have inj := coef_in hp h.toBase hj
  have ini := hp.1.inA h.wr hlt
  have a₁ := h.argEa (i := 1)
  have i₁ := h.argIn hp.1 (i := 1) (by decide)
  simp only [Nat.mul_one, Nat.reduceAdd] at a₁
  have hvj : s.mem.readW (coeffAddr (L.aA s₀) (j' s₀ k)) 32 = zw (ofInt (S' s₀ k).1[j' s₀ k]!) := h.poly _ hj
  have rlo : ∀ W : BitVec 32, (s.mem.writeW (coeffAddr (L.aA s₀) (S' s₀ k).2) W).readW (argAddr s₀ 1) 32 =
      BitVec.ofNat 32 (G s₀ / 2 ^ t' s₀ k) := fun W => by
    rw [Mem.readW_writeW_sep (coef_arg_sep hp hlt (by decide)) (by decide)]; exact h.lo
  have fa : ∀ W : BitVec 32, Frame [L.aR s₀] s.mem (s.mem.writeW (coeffAddr (L.aA s₀) (S' s₀ k).2) W) :=
    fun W => (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (coeff_contains _ hlt)
  have fin : ∀ s' : State, s'.gpr .esp = s.gpr .esp → s'.gpr .esi = s.gpr .esi → s'.gpr .ecx = s.gpr .ecx →
      s'.gpr .ebp = s.gpr .ebp → s'.gpr .edi = s.gpr .edi →
      s'.gpr .eax = L.aP s₀ + BitVec.ofNat 32 (4 * j' s₀ k) →
      s'.gpr .ebx = BitVec.ofNat 32 (G s₀ / 2 ^ t' s₀ k) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = s.mem.writeW (coeffAddr (L.aA s₀) (S' s₀ k).2) (zw (ofInt (S' s₀ k).1[j' s₀ k]!)) →
      M1 s₀ k s' := by
    intro s' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
    refine ⟨⟨by rw [e1, h.esp], by rw [e8, h.rd], by rw [e9, h.wr], ?_⟩, fun p hp' => ?_, by rw [e2, h.esi],
      by rw [e3, h.ecx], by rw [e4, h.ebp], by rw [e5, h.edi], e6, fun jj hjj => ?_, by rw [e10]; exact rlo _,
      ?_, e7, hlt, hle⟩
    · rw [e10]; exact h.frame.writeW (r := L.aR s₀) (by simp) _ (coeff_contains _ hlt)
    · rw [e10]
      refine ((fa _) _ fun r hr hc => ?_).trans (h.out p hp')
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.1.a_s _ hc ((hp.1.sub_s (o := 840 + p) (n := 1) (by omega_arith)) _ (Region.contains_self _ _))
    · rw [e10, coeffAt_writeW _ _ hjj hlt, P1, ipoly_set!_get _ _ (by simp only [n]; omega_arith)]
      by_cases e : (S' s₀ k).2 = jj
      · rw [ifT e, ifT e]
      · rw [ifF e, ifF e]; exact h.poly jj hjj
    · rw [e10, Mem.readW_writeW_sep (coef_arg_sep hp hlt (by decide)) (by decide)]; exact h.hi
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reduceAdd, Nat.reduceMul, Nat.reducePow, bMove, argOp, at_, runBlock_cons, runStep_some, runBlock_nil, exec,
    execAlu, readSrc, State.ea, State.load32, State.store32, State.setReg, arithFlags, State.setFlags,
    Option.map_some, Option.bind_some, hax, h.ebp, h.edi, quad_add _ _ _ rfl, eaj, eai, inj, ini, hvj, a₁, i₁,
    rlo, Option.some.injEq, exists_eq_left']
  refine ⟨fin _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) rfl rfl rfl, ?_⟩
  simp only [eval, signBit_eq]

/-! ## Two runs agree -/

namespace QPub
variable {s₀ s₀' : State} (hq : QPub s₀ s₀')
include hq

theorem eτ : τ s₀ = τ s₀' := by rw [τ, τ, hq.1.2 2 (by decide)]
theorem eS (k : Nat) : S' s₀ k = S' s₀' k := by simp only [S', hq.2, hq.eτ]
theorem ej (k : Nat) : j' s₀ k = j' s₀' k := by simp only [j', hq.2]
theorem et (k : Nat) : t' s₀ k = t' s₀' k := by simp only [t', hq.eS k, hq.eτ]
theorem eG : G s₀ = G s₀' := by simp only [G, hq.2]

end QPub

/-! ## The sign -/

theorem sign_piece (k : Nat) :
    Piece QPre QPub (fun s₀ s => M1 s₀ k s ∧ eval .e s = some (!(G s₀).testBit (t' s₀ k)))
      (fun s₀ s => M1 s₀ k s ∧ s.gpr .edx = zw (ofInt (sg s₀ k)))
      (.ite .e (.block [.mov .edx (.imm 1)]) (.block [.mov .edx (.imm (qImm - 1))])) := by
  refine Piece.ite (fun s₀ => !(G s₀).testBit (t' s₀ k)) (fun _ _ _ h => h.2)
    (fun s₀ s₀' _ _ hq => by rw [hq.eG, hq.et]) ?_ ?_
  · refine Piece.taint [] (fun s₀ s _ ⟨⟨h, _⟩, hb⟩ => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
      (by native_taint_decide)
    have hs : sg s₀ k = 1 := by
      rw [sg_eq]; simp only [Bool.not_eq_true'] at hb; rw [hb]; rfl
    apply WP.of_runBlock
    simp only [↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      State.setReg, Option.map_some, Option.some.injEq, exists_eq_left']
    refine ⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, h.out, by simp [h.esi], by simp [h.ecx], by simp [h.ebp],
      by simp [h.edi], by simp [h.eax], h.poly, h.lo, h.hi, by simp [h.ebx], h.lt, h.le⟩, ?_⟩
    rw [hs]; simp; rfl
  · refine Piece.taint [] (fun s₀ s _ ⟨⟨h, _⟩, hb⟩ => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
      (by native_taint_decide)
    have hs : sg s₀ k = -1 := by
      rw [sg_eq]; simp only [Bool.not_eq_false'] at hb; rw [hb]; rfl
    apply WP.of_runBlock
    simp only [↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      State.setReg, Option.map_some, Option.some.injEq, exists_eq_left']
    refine ⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, h.out, by simp [h.esi], by simp [h.ecx], by simp [h.ebp],
      by simp [h.edi], by simp [h.eax], h.poly, h.lo, h.hi, by simp [h.ebx], h.lt, h.le⟩, ?_⟩
    rw [hs]; simp; rfl

/-! ## `c[j] ← ±1`, and the sign bits shifted -/

theorem st_set {s₀ : State} {k : Nat} (hk : k < 264) (hlt : (S' s₀ k).2 < 256) (hle : j' s₀ k ≤ (S' s₀ k).2) :
    S' s₀ (k + 1) = ((P1 s₀ k).set! (j' s₀ k) (sg s₀ k), (S' s₀ k).2 + 1) := by
  rw [S', st_succ _ _ hk, bStep, ifT (show (S' s₀ k).2 < n by simp only [n]; omega_arith), ifF (Nat.not_lt.mpr hle)]

theorem shift_ok {s₀ : State} (hp : QPre s₀) {k : Nat} (hk : k < 264) {s : State} (h : M1 s₀ k s)
    (hdx : s.gpr .edx = zw (ofInt (sg s₀ k))) :
    WP isa (.block bShift) s fun s' => BI s₀ k (S' s₀ (k + 1)) s' := by
  have hj : j' s₀ k < 256 := by have := h.lt; have := h.le; omega_arith
  have eaj := coef_ea hp hj
  have inj := hp.1.inA h.wr hj
  have a₁ := h.argEa (i := 1)
  have a₂ := h.argEa (i := 2)
  have i₂ := h.argIn hp.1 (i := 2) (by decide)
  have w₁ := h.argInW hp.1 (i := 1) (by decide)
  have w₂ := h.argInW hp.1 (i := 2) (by decide)
  simp only [Nat.mul_one, Nat.reduceMul, Nat.reduceAdd] at a₁ a₂
  have rhi : ∀ W : BitVec 32, (s.mem.writeW (coeffAddr (L.aA s₀) (j' s₀ k)) W).readW (argAddr s₀ 2) 32 =
      BitVec.ofNat 32 (G s₀ / 2 ^ (t' s₀ k + 32)) := fun W => by
    rw [Mem.readW_writeW_sep (coef_arg_sep hp hj (by decide)) (by decide)]; exact h.hi
  have ge : 256 - τ s₀ ≤ (S' s₀ k).2 := st_ge (L.Msg s₀) (τ s₀) k
  have hτ := hp.τ_le
  have et : (S' s₀ (k + 1)).2 + τ s₀ - 256 = t' s₀ k + 1 := by
    rw [st_set hk h.lt h.le]; simp only [t']; omega_arith
  have fin : ∀ s' : State, s'.gpr .esp = s.gpr .esp → s'.gpr .esi = s.gpr .esi → s'.gpr .ecx = s.gpr .ecx →
      s'.gpr .ebp = s.gpr .ebp → s'.gpr .edi = s.gpr .edi + 1 → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = ((s.mem.writeW (coeffAddr (L.aA s₀) (j' s₀ k)) (zw (ofInt (sg s₀ k)))).writeW (argAddr s₀ 1)
        (BitVec.ofNat 32 (G s₀ / 2 ^ (t' s₀ k + 1)))).writeW (argAddr s₀ 2)
        (BitVec.ofNat 32 (G s₀ / 2 ^ (t' s₀ k + 1 + 32))) →
      BI s₀ k (S' s₀ (k + 1)) s' := by
    intro s' e1 e2 e3 e4 e5 e6 e7 e8
    have fg : Frame [L.gR s₀] (s.mem.writeW (coeffAddr (L.aA s₀) (j' s₀ k)) (zw (ofInt (sg s₀ k)))) s'.mem := by
      rw [e8]
      exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (arg_contains (n := 5) (by decide) hp.1.sp')).writeW
        (List.mem_singleton_self _) _ (arg_contains (n := 5) (by decide) hp.1.sp')
    have fa : Frame [L.aR s₀] s.mem (s.mem.writeW (coeffAddr (L.aA s₀) (j' s₀ k)) (zw (ofInt (sg s₀ k)))) :=
      (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (coeff_contains _ hj)
    have fw : Frame (L.W s₀) (P0 s₀).mem s'.mem :=
      (h.frame.trans (fa.mono (by simp))).trans (fg.mono (by simp))
    refine ⟨⟨by rw [e1, h.esp], by rw [e6, h.rd], by rw [e7, h.wr], fw⟩, fun p hp' => ?_, by rw [e2, h.esi],
      by rw [e3, h.ecx], by rw [e4, h.ebp], ?_, fun jj hjj => ?_, ?_, ?_⟩
    · rw [fg.bytes (R := ⟨L.sA s₀, 2048⟩) (by simp only [List.mem_singleton, forall_eq]; exact hp.1.s_g)
        (show (2048 : Nat) ≤ 2 ^ 64 by decide) (show 840 + p < 2048 by omega_arith)]
      refine (fa _ fun r hr hc => ?_).trans (h.out p hp')
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.1.a_s _ hc ((hp.1.sub_s (o := 840 + p) (n := 1) (by omega_arith)) _ (Region.contains_self _ _))
    · rw [e5, h.edi, st_set hk h.lt h.le, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ofNat_add_ofNat]
    · rw [coeffAt_eq, fg.readW (coeff_contains _ hjj) (by simp only [List.mem_singleton, forall_eq]; exact hp.1.a_g)
        (by decide), ← coeffAt_eq, coeffAt_writeW _ _ hjj hj, st_set hk h.lt h.le,
        ipoly_set!_get _ _ (by simp only [n]; omega_arith)]
      by_cases e : j' s₀ k = jj
      · rw [ifT e, ifT e]
      · rw [ifF e, ifF e]; exact h.poly jj hjj
    · rw [e8, Mem.readW_writeW_sep (slots_sep hp) (by decide), Mem.readW_writeW_self32, et]
    · rw [e8, Mem.readW_writeW_self32, et]
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reducePow, and_self, bShift, argOp, at_, runBlock_cons, runStep_some, runBlock_nil, exec,
    execAlu, execShift, readSrc, State.ea, State.load32, State.store32, State.setReg, arithFlags, State.setFlags,
    Option.map_some, Option.bind_some, h.eax, h.ebx, hdx, eaj, inj, a₁, a₂, i₂, w₁, w₂, rhi, signs_shift,
    signs_shift_hi (G_lt s₀), Option.some.injEq, exists_eq_left']
  exact fin _ (by simp) (by simp) (by simp) (by simp) (by simp) rfl rfl rfl

/-! ## An iteration -/

theorem st_skip {s₀ : State} {k : Nat} (hk : k < 264) (hgt : (S' s₀ k).2 < j' s₀ k) :
    S' s₀ (k + 1) = S' s₀ k := by
  rw [S', st_succ _ _ hk, bStep]
  by_cases hl : (S' s₀ k).2 < n
  · rw [ifT hl, ifT hgt]
  · rw [ifF hl]

theorem st_full {s₀ : State} {k : Nat} (hk : k < 264) (hf : ¬ (S' s₀ k).2 < 256) : S' s₀ (k + 1) = S' s₀ k := by
  rw [S', st_succ _ _ hk, bStep, ifF (show ¬ (S' s₀ k).2 < n by simp only [n]; omega_arith)]

theorem set_piece (k : Nat) (hk : k < 264) :
    Piece QPre QPub (fun s₀ s => ((BI s₀ k (S' s₀ k) s ∧ (S' s₀ k).2 < 256 ∧
        s.gpr .eax = BitVec.ofNat 32 (j' s₀ k)) ∧ eval .b s = some (decide ((S' s₀ k).2 < j' s₀ k))) ∧
        decide ((S' s₀ k).2 < j' s₀ k) = false)
      (fun s₀ s => BI s₀ k (S' s₀ (k + 1)) s) bSet := by
  refine Piece.seq (Piece.taint [.eax, .edi, .ebp, .esp]
    (fun s₀ s hp ⟨⟨⟨h, hlt, hax⟩, _⟩, hb⟩ => move_ok hp h hlt hax (by simp at hb; omega_arith))
    (fun s₀ s₀' s s' _ _ hq ⟨⟨⟨h, _, hax⟩, _⟩, _⟩ ⟨⟨⟨h', _, hax'⟩, _⟩, _⟩ r hr => ?_) (by native_taint_decide))
    (Piece.seq (sign_piece k) (Piece.taint [.eax, .edi, .esp] (fun s₀ s hp ⟨h, hdx⟩ => shift_ok hp hk h hdx)
      (fun s₀ s₀' s s' _ _ hq ⟨h, _⟩ ⟨h', _⟩ r hr => ?_) (by native_taint_decide)))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [hax, hax', hq.ej]
    · rw [h.edi, h'.edi, hq.eS]
    · rw [h.ebp, h'.ebp, hq.1.aP hL]
    · rw [h.esp, h'.esp, hq.1.e1]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h.eax, h'.eax, hq.ej, hq.1.aP hL]
    · rw [h.edi, h'.edi, hq.eS]
    · rw [h.esp, h'.esp, hq.1.e1]

theorem try_piece (k : Nat) (hk : k < 264) :
    Piece QPre QPub (fun s₀ s => BI s₀ k (S' s₀ k) s ∧ (S' s₀ k).2 < 256)
      (fun s₀ s => BI s₀ k (S' s₀ (k + 1)) s) bTry := by
  refine Piece.seq (B := fun s₀ s => (BI s₀ k (S' s₀ k) s ∧ (S' s₀ k).2 < 256 ∧
      s.gpr .eax = BitVec.ofNat 32 (j' s₀ k)) ∧ eval .b s = some (decide ((S' s₀ k).2 < j' s₀ k))) ?_
    (Piece.ite (fun s₀ => decide ((S' s₀ k).2 < j' s₀ k)) (fun _ _ _ h => h.2)
      (fun s₀ s₀' _ _ hq => by rw [hq.eS, hq.ej]) ?_ (set_piece k hk))
  · refine Piece.taint [.esi] (fun s₀ s hp ⟨h, hlt⟩ => ?_) (fun s₀ s₀' s s' _ _ hq ⟨h, _⟩ ⟨h', _⟩ r hr => ?_)
      (by native_taint_decide)
    · have hs := hp.1.s_fit
      have e0 : (L.sP s₀ + BitVec.ofNat 32 (848 + k) + BitVec.ofNat 32 0).setWidth 64 =
          L.sA s₀ + BitVec.ofNat 64 (840 + (8 + k)) := by
        rw [ea_add (by simp only [L] at hs ⊢; omega_arith)]; congr 2; omega_arith
      have i0 := hp.1.inS' h.wr (o := 840 + (8 + k)) (n := 1) (by omega_arith)
      have v0 := h.out (8 + k) (by omega_arith)
      have hle : (S' s₀ k).2 ≤ 256 := st_le (L.Msg s₀) (τ s₀) k
      apply WP.of_runBlock
      simp only [reduceCtorEq, ↓reduceIte, at_, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
        readSrc, State.ea, State.load8, State.setReg, arithFlags, State.setFlags, Option.map_some,
        Option.bind_some, h.esi, e0, i0, v0, Option.some.injEq, exists_eq_left']
      refine ⟨⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, h.out, by simp [h.esi], by simp [h.ecx], by simp [h.ebp],
        by simp [h.edi], h.poly, h.lo, h.hi⟩, hlt, ?_⟩, ?_⟩
      · exact eq_ofNat_of_toNat (toNat_byte32 _)
      · simp only [eval, h.edi, toNat_byte32, toNat_ofNat32 (show (S' s₀ k).2 < 2 ^ 32 by omega_arith)]
    · simp only [List.mem_singleton] at hr
      subst hr
      rw [h.esi, h'.esi, hq.1.sP hL]
  · exact nil_piece fun s₀ s _ ⟨⟨⟨h, _⟩, _⟩, hb⟩ => st_skip hk (of_decide_eq_true hb) ▸ h

theorem body_piece (k : Nat) (hk : k < 264) :
    Piece QPre QPub (fun s₀ s => BI s₀ k (S' s₀ k) s)
      (fun s₀ s => BI s₀ (k + 1) (S' s₀ (k + 1)) s ∧ eval .ne s = some (decide (k + 1 < 264))) bBody := by
  refine Piece.seq (B := fun s₀ s => BI s₀ k (S' s₀ k) s ∧ eval .b s = some (decide ((S' s₀ k).2 < 256)))
    (Piece.taint [] (fun s₀ s _ h => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp)) (by native_taint_decide))
    (Piece.seq (B := fun s₀ s => BI s₀ k (S' s₀ (k + 1)) s)
      (Piece.ite (fun s₀ => decide ((S' s₀ k).2 < 256)) (fun _ _ _ h => h.2)
        (fun s₀ s₀' _ _ hq => by rw [hq.eS])
        ((try_piece k hk).mono (fun _ _ _ ⟨⟨h, _⟩, hb⟩ => ⟨h, of_decide_eq_true hb⟩) fun _ _ _ h => h)
        (nil_piece fun s₀ s _ ⟨⟨h, _⟩, hb⟩ => st_full hk (of_decide_eq_false hb) ▸ h))
      (Piece.taint [] (fun s₀ s _ h => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp)) (by native_taint_decide)))
  · have hle : (S' s₀ k).2 ≤ 256 := st_le (L.Msg s₀) (τ s₀) k
    have h256 : (256 : BitVec 32).toNat = 256 := rfl
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags,
      Option.bind_some, Option.some.injEq, exists_eq_left']
    refine ⟨⟨⟨h.esp, h.rd, h.wr, h.frame⟩, h.out, h.esi, h.ecx, h.ebp, h.edi, h.poly, h.lo, h.hi⟩, ?_⟩
    simp only [eval, h.edi, h256, toNat_ofNat32 (show (S' s₀ k).2 < 2 ^ 32 by omega_arith)]
  · apply WP.of_runBlock
    simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
      State.setReg, arithFlags, State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left']
    refine ⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, h.out, ?_, ?_, by simp [h.ebp], by simp [h.edi], h.poly,
      h.lo, h.hi⟩, ?_⟩
    · simp only [ite_true, h.esi]
      rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, add_ofNat_add]; congr 2
    · simp only [ite_true, h.ecx]
      exact cnt_next hk
    · simp only [eval, h.ecx]
      exact cnt_ne hk (by omega_arith)

theorem loop_piece : Piece QPre QPub (fun s₀ s => BI s₀ 0 (S' s₀ 0) s) (fun s₀ s => BI s₀ 264 (S' s₀ 264) s)
    (.loop bBody .ne) :=
  Piece.loop (fun k s₀ s => BI s₀ k (S' s₀ k) s) (by decide) fun k hk => body_piece k hk

end VG.Proof.MlDsa.X86.Sample.Ball

end

end

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_sample_in_ball`

The SHAKE256 output, `c` zeroed, the setup and the loop (`Ball.lean`,
`BallLoop.lean`) leave the state of `SampleInBall`'s loop over the 264 bytes
after the sign bits (`ballFold`) at `c` and `i` in `edi`; the function returns
`i >> 8`, and `sampleInBall_some` and `sampleInBall_none`
(`Proof/MlDsa/Sample/Ball.lean`) give the contract. Two runs with the same
pointers and `c̃` leak the same (`QPub`): the contract lets the function leak
`c̃`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Sample.Ball

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86
open VG.Proof.MlDsa.X86.Sample
open VG.Proof.MlDsa.Sample
open VG.Impl.MlDsa.X86.Sample (bZero bSetup bBody retJ sponge argOp)
open VG.Spec.MlDsa (Zq q H n ofInt IPoly)
open VG.Proof.MlDsa (coeffAt)

/-- The end: `i >> 8` in `eax`. -/
structure Fin (s₀ s : State) : Prop extends BI s₀ 264 (S' s₀ 264) s where
  eax : s.gpr .eax = BitVec.ofNat 32 ((S' s₀ 264).2 / 256)

theorem fin_piece : Piece QPre QPub (fun s₀ s => BI s₀ 264 (S' s₀ 264) s) Fin (.block (retJ .edi)) := by
  refine Piece.taint [] (fun s₀ s _ h => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
    (by native_taint_decide)
  have hl : (S' s₀ 264).2 ≤ 256 := st_le _ _ _
  refine wp_movr (wp_shr (by decide) (by decide) fun s' o e => WP.block_nil_iff.mpr ?_)
  have g : ∀ r, r ≠ .eax → s'.gpr r = s.gpr r := fun r hr => by
    rw [o.gpr r (by simp [hr])]; simp [State.setReg, hr]
  refine ⟨⟨⟨by rw [g _ (by decide), h.esp], by rw [o.rd]; exact h.rd, by rw [o.wr]; exact h.wr,
    by rw [o.mem]; exact h.frame⟩, by rw [o.mem]; exact h.out, by rw [g _ (by decide), h.esi],
    by rw [g _ (by decide), h.ecx], by rw [g _ (by decide), h.ebp], by rw [g _ (by decide), h.edi],
    by rw [o.mem]; exact h.poly, by rw [o.mem]; exact h.lo, by rw [o.mem]; exact h.hi⟩, ?_⟩
  rw [e]
  simp only [State.setReg, ite_true, h.edi]
  exact eq_ofNat_of_toNat (by rw [toNat_shr, toNat_ofNat32 (show (S' s₀ 264).2 < 2 ^ 32 by omega_using [hl])])

theorem main_piece : Piece QPre QPub (fun s₀ s => s = P0 s₀) Fin
    (.seq (sponge 4 136 (.mem (argOp 1)) 272) <|
      .seq bZero <| .seq (.block bSetup) <| .seq (.loop bBody .ne) (.block (retJ .edi))) :=
  Piece.seq ((sponge_piece hL).pre_mono (fun _ h => h.1) fun _ _ _ _ h => h.1) <|
    Piece.seq zero_piece <| Piece.seq setup_piece <| Piece.seq loop_piece fin_piece

theorem piece : Piece QPre QPub (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (Fin s₀) s₀ s')
    Impl.MlDsa.X86.Sample.sampleInBall :=
  Piece.leaf L.W (NoSp.of_all (by decide +kernel))
    (fun _ hp => ⟨by have := hp.1.sp; omega_using [this], by have := hp.1.sp'; omega_using [this]⟩)
    (fun _ hp => hp.1.hW) (fun _ _ _ _ hq => hq.1.1)
    (main_piece.mono (fun _ _ _ h => h) fun _ _ _ h => ⟨⟨h.frame, h.esp, h.rd, h.wr⟩, h⟩)

theorem QPre.of {s₀ : State} (h : (Proof.MlDsa.sampleInBallContract X86.abi 56).pre s₀) : QPre s₀ := by
  sig_pre [Proof.MlDsa.sampleInBallContract, Proof.MlDsa.sampleInBallSig, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22⟩ := h
  have hl : (arg s₀ 1).toNat < 136 := by
    simp only [Proof.MlDsa.ballParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h22
    omega_using [h22]
  exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, hl⟩, h22⟩

theorem S'_all (s₀ : State) : S' s₀ 264 = ballFold (τ s₀) (H (L.Msg s₀) 272) := by
  simp only [S', st, ballFold]
  rw [List.take_of_length_le (by rw [List.length_drop, Xb_length])]

theorem toRq_getElem! (v : IPoly) {i : Nat} (hi : i < n) : (Spec.MlDsa.toRq v)[i]! = ofInt v[i]! := by
  rw [getElem!_pos _ i hi, getElem!_pos _ i hi]
  simp only [Spec.MlDsa.toRq, Vector.getElem_map]

/-- Memory with the arguments `0`, `32`, `39`, `0x100` and `0x1000` at `0x5004`. -/
def satMem : Mem := fun a =>
  if a = 0x5008 then 32 else if a = 0x500c then 39 else if a = 0x5011 then 1 else if a = 0x5015 then 0x10 else 0

theorem verified :
    Verified X86.target Impl.MlDsa.X86.Sample.sampleInBall (Proof.MlDsa.sampleInBallContract X86.abi 56) := by
  refine Piece.verified ((piece.pre_mono (fun _ h => QPre.of h) fun s s' _ _ h => ?_).mono
    (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · sig_pub [Proof.MlDsa.sampleInBallContract, Proof.MlDsa.sampleInBallSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes] at h
    obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆, e₇⟩ := h
    refine ⟨⟨e₁, fun i hi => ?_⟩, ?_⟩
    · match i, hi with
      | 0, _ => exact e₃
      | 1, _ => exact e₄
      | 2, _ => exact e₅
      | 3, _ => exact e₆
      | 4, _ => exact e₇
    · exact RejNtt.map_toNat_inj e₂
  · obtain ⟨habi, -, -, s, hfin, hm, hax⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [Proof.MlDsa.sampleInBallContract, Proof.MlDsa.sampleInBallSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]
    rw [setWidth_append32, hax, hfin.eax]
    have hl : (S' s₀ 264).2 ≤ 256 := st_le _ _ _
    have hp : Proof.MlDsa.PolyIs s.mem (L.aA s₀) (Spec.MlDsa.toRq (S' s₀ 264).1) :=
      polyIs_of_coeffAt fun i hi => by rw [hfin.poly i (by simp only [n] at hi; omega_using [hi]), toRq_getElem! _ hi]
    rw [S'_all] at hl hp
    replace hp := Proof.MlDsa.Arith.polyIs_frame hm (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ((QPre.of h₀).1.hW _ List.mem_cons_self).1.symm) hp
    rw [S'_all]
    by_cases e : (ballFold (τ s₀) (H (L.Msg s₀) 272)).2 = 256
    · rw [e]
      refine ⟨fun _ => hp.1, .inl ⟨rfl, { Spec.MlDsa.minBounds with ball := 272 }, ?_⟩⟩
      show (Spec.MlDsa.sampleInBall (τ s₀) 272 (L.Msg s₀)).map Spec.MlDsa.toRq =
        some (Proof.MlDsa.polyAt s'.mem (L.aA s₀))
      rw [sampleInBall_some _ (by decide) e, hp.2]
      rfl
    · rw [Nat.div_eq_of_lt (by omega_using [hl, e])]
      refine ⟨fun h => absurd (congrArg BitVec.toNat h) (by show ¬ (0 = 1); decide), .inr ⟨rfl, ?_⟩⟩
      show (Spec.MlDsa.sampleInBall (τ s₀) Spec.MlDsa.minBounds.ball (L.Msg s₀)).map Spec.MlDsa.toRq = none
      rw [sampleInBall_none _ (B := 272) (by decide) (by decide) e]
      rfl
  · let st := satState satMem [⟨0, 32⟩] [⟨0x100, 1024⟩, ⟨0x1000, 2048⟩, ⟨0x5004, 20⟩]
    refine ⟨st, ?_⟩
    sig_sat_check [Proof.MlDsa.sampleInBallContract, Proof.MlDsa.sampleInBallSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]

end VG.Proof.MlDsa.X86.Sample.Ball

end

end

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_norm_lt`

`ebp` is all ones while every coefficient `a` so far has `a < bound` or `q - a
< bound`, and zero otherwise (`NInv`): each comparison borrows into a mask
(`nl_step`). Its low bit is the result (`normZq_lt`, `normRq_lt`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Round

open VG VG.X86 VG.X86.Wp VG.Impl.MlDsa.X86.Round
open VG.Impl.MlKem.X86 (at_ leaf)
open VG.Spec.MlDsa (q normRq normZq)
open VG.Proof.MlDsa (coeffAt Reduced polyAt normLtContract normLtSig)
open VG.Proof.MlDsa.Round (coeffAddr pR coeff_contains n_eq q_eq polyAt_val normZq_lt normRq_lt)
open VG.Proof.MlKem.X86 (Only E0 P0 P0_esp P0_wr frameR retR LeafPost LeafEnd Piece satState
  toNat_ofNat32 eq_ofNat_of_toNat ptr_next cnt_next cnt_ne setWidth_append32)

structure NPre (s₀ : State) : Prop where
  sp : 16 ≤ (E0 s₀).toNat
  sp' : (E0 s₀).toNat + 4 + 8 ≤ 2 ^ 32
  rd : s₀.rd = [pR (pA s₀ 0), aR s₀ 2]
  wr : s₀.wr = []
  ret_f : (retR s₀).Disjoint (pR (pA s₀ 0))
  ret_a : (retR s₀).Disjoint (aR s₀ 2)
  stk_f : (stkR s₀).Disjoint (pR (pA s₀ 0))
  stk_a : (stkR s₀).Disjoint (aR s₀ 2)
  f_fit : (arg s₀ 0).toNat + 1024 ≤ 2 ^ 32
  f_red : Reduced s₀.mem (pA s₀ 0)

theorem NPre.of {s₀ : State} (h : (normLtContract X86.abi 16).pre s₀) : NPre s₀ := by
  sig_pre [normLtContract, normLtSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

/-- The public data: the stack pointer, the pointer and the bound. -/
def NPub (s₀ s₀' : State) : Prop := E0 s₀ = E0 s₀' ∧ arg s₀ 0 = arg s₀' 0 ∧ arg s₀ 1 = arg s₀' 1

/-- Coefficient `i` is within the bound. -/
def okC (s₀ : State) (i : Nat) : Prop :=
  (coeffAt s₀.mem (pA s₀ 0) i).toNat < (arg s₀ 1).toNat ∨ q - (coeffAt s₀.mem (pA s₀ 0) i).toNat < (arg s₀ 1).toNat

instance (s₀ : State) (i : Nat) : Decidable (okC s₀ i) := by unfold okC; infer_instance

/-- The mask for the first `k` coefficients. -/
def maskN (s₀ : State) (k : Nat) : BitVec 32 := if ∀ i < k, okC s₀ i then BitVec.allOnes 32 else 0

/-- After `k` coefficients. -/
structure NInv (s₀ : State) (k : Nat) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  mem : s.mem = (P0 s₀).mem
  esi : s.gpr .esi = arg s₀ 0 + BitVec.ofNat 32 (4 * k)
  ebx : s.gpr .ebx = arg s₀ 1
  ecx : s.gpr .ecx = BitVec.ofNat 32 (256 - k)
  ebp : s.gpr .ebp = maskN s₀ k

theorem maskN_succ (s₀ : State) (k : Nat) :
    maskN s₀ k &&& ((if okC s₀ k then BitVec.allOnes 32 else 0)) = maskN s₀ (k + 1) := by
  unfold maskN
  have e : (∀ i < k + 1, okC s₀ i) ↔ ((∀ i < k, okC s₀ i) ∧ okC s₀ k) :=
    ⟨fun h' => ⟨fun i hi => h' i (by omega_using [hi]), h' k (by omega_using [])⟩, fun ⟨h₁, h₂⟩ i hi => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      exacts [h₁ i hi, h₂]⟩
  by_cases h : ∀ i < k, okC s₀ i <;> by_cases hk : okC s₀ k
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true hk),
      ite_eq_left_of_eq_true _ _ (eq_true (e.mpr ⟨h, hk⟩))]; simp
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_right_of_eq_false _ _ (eq_false hk),
      ite_eq_right_of_eq_false _ _ (eq_false fun h' => hk (e.mp h').2)]; simp
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_right_of_eq_false _ _ (eq_false fun h' => h (e.mp h').1)]; simp
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_right_of_eq_false _ _ (eq_false fun h' => h (e.mp h').1)]; simp

theorem nlBody_eq : nlBody =
    [.mov .eax (.mem (at_ .esi 0)), .mov .edx (.imm qImm), .alu .sub .edx (.reg .eax), .alu .cmp .eax (.reg .ebx),
      .alu .sbb .eax (.reg .eax), .alu .cmp .edx (.reg .ebx), .alu .sbb .edx (.reg .edx), .alu .or .eax (.reg .edx),
      .alu .and .ebp (.reg .eax), .alu .add .esi (.imm 4), .alu .sub .ecx (.imm 1)] := rfl

theorem mask_or (b c : Bool) :
    ((if b then BitVec.allOnes 32 else 0) ||| (if c then BitVec.allOnes 32 else 0)) =
      if (b || c) then BitVec.allOnes 32 else 0 := by
  cases b <;> cases c <;> simp

theorem nl_step {s₀ : State} (hp : NPre s₀) {k : Nat} (hk : k < 256) {s : State} (h : NInv s₀ k s) :
    WP isa (.block nlBody) s fun s' => NInv s₀ (k + 1) s' ∧ eval .ne s' = some (decide (k + 1 < 256)) := by
  have hk' : k < VG.Spec.MlDsa.n := by rw [n_eq]; exact hk
  have hin : InRegions (s.rd ++ s.wr) (addr (arg s₀ 0 + BitVec.ofNat 32 (4 * k)) 0) 4 := by
    rw [addr_cf hp.f_fit hk, h.rd, h.wr, pushed_rd, P0_wr, hp.rd]
    exact ⟨_, by simp, coeff_contains _ hk'⟩
  have hv : (s.mem.readW (addr (arg s₀ 0 + BitVec.ofNat 32 (4 * k)) 0) 32) = coeffAt s₀.mem (pA s₀ 0) k := by
    rw [addr_cf hp.f_fit hk, h.mem, ← VG.Proof.MlDsa.Round.coeffAt_eq]
    exact in_keep (W := []) hp.sp (Frame.refl _ _) hp.stk_f (by simp) hk
  have ha := hp.f_red k hk'
  rw [nlBody_eq]
  refine wp_ldm h.esi hin fun s₁ u₁ => wp_movi fun s₂ u₂ => wp_subr fun s₃ u₃ _ => wp_cmp fun s₄ f₄ c₄ _ =>
    wp_sbb_self c₄ fun s₅ u₅ => wp_cmp fun s₆ f₆ c₆ _ => wp_sbb_self c₆ fun s₇ u₇ => wp_or fun s₈ u₈ =>
    wp_and fun s₉ u₉ => wp_addi fun s₁₀ u₁₀ => wp_subi fun s₁₁ u₁₁ _ z₁₁ =>
    WP.block_nil_iff.mpr ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [u₁₁.other _ (by decide : Reg.esp ≠ .ecx), u₁₀.other _ (by decide : Reg.esp ≠ .esi),
      u₉.other _ (by decide : Reg.esp ≠ .ebp), u₈.other _ (by decide : Reg.esp ≠ .eax), u₇.other _ (by decide : Reg.esp ≠ .edx),
      f₆.gpr, u₅.other _ (by decide : Reg.esp ≠ .eax), f₄.gpr, u₃.other _ (by decide : Reg.esp ≠ .edx),
      u₂.other _ (by decide : Reg.esp ≠ .edx), u₁.other _ (by decide : Reg.esp ≠ .eax), h.esp]
  · rw [u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, f₆.rd, u₅.rd, f₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, f₆.wr, u₅.wr, f₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
  · rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, f₆.mem, u₅.mem, f₄.mem, u₃.mem, u₂.mem, u₁.mem, h.mem]
  · rw [u₁₁.other _ (by decide), u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), f₆.gpr, u₅.other _ (by decide), f₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.esi]
    exact ptr_next _ _ 4
  · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), f₆.gpr, u₅.other _ (by decide), f₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.ebx]
  · rw [u₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), f₆.gpr, u₅.other _ (by decide), f₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.ecx]
    exact cnt_next hk
  · have ea₃ : s₃.gpr .eax = coeffAt s₀.mem (pA s₀ 0) k := by
      rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hv]
    have eb₃ : s₃.gpr .ebx = arg s₀ 1 := by
      rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.ebx]
    have ed₅ : (s₅.gpr .edx).toNat = q - (coeffAt s₀.mem (pA s₀ 0) k).toNat := by
      rw [u₅.other _ (by decide), f₄.gpr, u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.gpr, hv,
        BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact Nat.le_of_lt ha)]
      rfl
    have eb₅ : s₅.gpr .ebx = arg s₀ 1 := by rw [u₅.other _ (by decide), f₄.gpr, eb₃]
    rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide),
      f₆.gpr, u₅.other _ (by decide), f₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h.ebp, u₈.gpr, u₇.other _ (by decide), f₆.gpr, u₅.gpr, u₇.gpr, mask_or, ← maskN_succ]
    congr 1
    rw [ea₃, eb₃, ed₅, eb₅]
    unfold okC
    by_cases h1 : (coeffAt s₀.mem (pA s₀ 0) k).toNat < (arg s₀ 1).toNat
    · simp [h1]
    · by_cases h2 : q - (coeffAt s₀.mem (pA s₀ 0) k).toNat < (arg s₀ 1).toNat
      · simp [h1, h2]
      · simp [h1, h2]
  · simp only [eval, z₁₁, Option.map_some]
    rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), f₆.gpr, u₅.other _ (by decide), f₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.ecx]
    exact cnt_ne hk (by decide)

/-- After `nlInit`. -/
structure NS1 (s₀ s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  mem : s.mem = (P0 s₀).mem
  esi : s.gpr .esi = arg s₀ 0
  ebx : s.gpr .ebx = arg s₀ 1
  ebp : s.gpr .ebp = BitVec.allOnes 32

theorem maskN_zero (s₀ : State) : maskN s₀ 0 = BitVec.allOnes 32 :=
  ite_eq_left_of_eq_true _ _ (eq_true fun _ h => absurd h (Nat.not_lt_zero _))

theorem nl_piece : Piece NPre NPub (fun s₀ s => s = s₀)
    (fun s₀ s' => LeafPost (fun s => NInv s₀ 256 s ∧ s.gpr .eax = maskN s₀ 256 &&& 1) s₀ s') normLt := by
  refine Piece.leaf (fun _ => []) (NoSp.of_all (by decide +kernel))
    (fun _ hp => ⟨hp.sp, by have := hp.sp'; omega_using [this]⟩) (fun _ _ r hr => absurd hr (by simp)) (fun _ _ _ _ hq => hq.1)
    ((Piece.seq (B := NS1) ?_ (Piece.seq (B := fun s₀ s => NInv s₀ 256 s)
      (Piece.seq (B := fun s₀ s => NInv s₀ 0 s) ?_ ?_) ?_)).mono
      (fun _ _ _ h => h) fun _ _ _ h => ⟨⟨by rw [h.1.mem]; exact Frame.refl _ _, h.1.esp, h.1.rd, h.1.wr⟩, h⟩)
  · refine Piece.taint [.esp] (fun s₀ s hp e => ?_) (fun s₀ s₀' s s' _ _ hq e e' r hr => ?_) (by native_taint_decide)
    · subst e
      have hin : aR s₀ 2 ∈ s₀.rd ++ s₀.wr := by simp [hp.rd]
      obtain ⟨a₀, i₀, v₀⟩ := arg_P0 (i := 0) (by omega_using []) hp.sp hp.sp' hin hp.stk_a
      obtain ⟨a₁, i₁, v₁⟩ := arg_P0 (i := 1) (by omega_using []) hp.sp hp.sp' hin hp.stk_a
      simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceAdd] at a₀ a₁
      apply WP.of_runBlock
      simp only [reduceCtorEq, ↓reduceIte, nlInit, at_, runBlock_cons, runStep_some, runBlock_nil,
        exec, readSrc, State.ea, State.load32, State.setReg, Option.map_some, a₀, a₁, i₀, i₁, v₀, v₁,
        Option.some.injEq, exists_eq_left']
      exact ⟨by simp, rfl, rfl, rfl, by simp, by simp, by simp⟩
    · simp only [List.mem_singleton] at hr
      subst hr
      rw [e, e', P0_esp, P0_esp, hq.1]
  · refine Piece.taint [] (fun s₀ s hp h => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
      (by native_taint_decide)
    refine wp_movi fun s₁ u₁ => WP.block_nil_iff.mpr ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₁.other _ (by decide), h.esp]
    · rw [u₁.rd, h.rd]
    · rw [u₁.wr, h.wr]
    · rw [u₁.mem, h.mem]
    · rw [u₁.other _ (by decide), h.esi]; simp
    · rw [u₁.other _ (by decide), h.ebx]
    · rw [u₁.gpr]; rfl
    · rw [u₁.other _ (by decide), h.ebp, maskN_zero]
  · exact Piece.countLoop (by decide) (fun k s₀ s => NInv s₀ k s) [.esp, .esi, .ecx]
      (fun k hk s₀ s hp h => nl_step hp hk h)
      (fun k _ s₀ s₀' s s' _ _ hq h h' r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h.esp, h'.esp, P0_esp, P0_esp, hq.1]
        · rw [h.esi, h'.esi, hq.2.1]
        · rw [h.ecx, h'.ecx]) (by native_taint_decide)
  · refine Piece.taint [] (fun s₀ s hp h => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
      (by native_taint_decide)
    refine wp_mov fun s₁ u₁ => wp_andi fun s₂ u₂ => WP.block_nil_iff.mpr ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [u₂.other _ (by decide), u₁.other _ (by decide), h.esp]
    · rw [u₂.rd, u₁.rd, h.rd]
    · rw [u₂.wr, u₁.wr, h.wr]
    · rw [u₂.mem, u₁.mem, h.mem]
    · rw [u₂.other _ (by decide), u₁.other _ (by decide), h.esi]
    · rw [u₂.other _ (by decide), u₁.other _ (by decide), h.ebx]
    · rw [u₂.other _ (by decide), u₁.other _ (by decide), h.ecx]
    · rw [u₂.other _ (by decide), u₁.other _ (by decide), h.ebp]
    · rw [u₂.gpr, u₁.gpr, h.ebp]

theorem maskN_and_one (s₀ : State) :
    (maskN s₀ 256 &&& 1).toNat = if ∀ i : Nat, i < 256 → okC s₀ i then 1 else 0 := by
  unfold maskN
  by_cases h : ∀ i < 256, okC s₀ i
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true h)]; rfl
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_right_of_eq_false _ _ (eq_false h)]; rfl

/-- Memory with the arguments `0` and `1` at `0x5004`. -/
def nlSatMem : Mem := fun a => if a = 0x5008 then 1 else 0

theorem normLt_verified : Verified X86.target normLt (normLtContract X86.abi 16) := by
  refine Piece.verified ((nl_piece.pre_mono (fun _ h => NPre.of h) fun s s' _ _ h => by
      sig_pub [normLtContract, normLtSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, ⟨_, hinv⟩, -, hax⟩ := hq
    refine ⟨habi, ?_⟩
    have hp := NPre.of h₀
    sig_post [normLtContract, normLtSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [setWidth_append32, hax, hinv]
    apply BitVec.eq_of_toNat_eq
    rw [maskN_and_one]
    have e : (∀ i < 256, okC s₀ i) ↔ normRq [polyAt s₀.mem (pA s₀ 0)] < (arg s₀ 1).toNat := by
      rw [normRq_lt]
      refine forall_congr' fun i => imp_congr_right fun hi => ?_
      rw [normZq_lt, polyAt_val hp.f_red hi]
      rfl
    by_cases h : ∀ i : Nat, i < 256 → okC s₀ i
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true (e.mp h))]; rfl
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_right_of_eq_false _ _ (eq_false fun h' => h (e.mpr h'))]
      rfl
  · let st := satState nlSatMem [⟨0, 1024⟩, ⟨0x5004, 8⟩] []
    refine ⟨st, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [normLtContract, normLtSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      sig_and_intros
      all_goals first
        | trivial
        | (rw [show BitVec.setWidth 64 (arg st 0) = BitVec.ofNat 64 0 by decide]
           refine reduced_zero (fun a ha => ?_) 0 (by decide)
           simp only [nlSatMem]
           rw [ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega_using [ha])])
        | decide +kernel

end VG.Proof.MlDsa.X86.Round

end

end

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_make_hint` and `vg_mldsa_use_hint`

Both functions are the prologue and the loops of `Hint.lean`; `makeHint` then
returns the count in `ecx`, which is the number of 1s (`sumV_ones`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Round

open VG VG.X86 VG.X86.Wp VG.Impl.MlDsa.X86.Round
open VG.Impl.MlKem.X86 (at_ leaf)
open VG.Spec.MlDsa (q)
open VG.Proof.MlDsa (gamma2s coeffAt Reduced polyAt HintIs NatPolyIs hintOnes hintAt makeHintContract makeHintSig useHintContract useHintSig)
open VG.Proof.MlDsa.Round (coeffAddr pR n_eq q_eq polyAt_val hintIs_of_toNat natPolyIs_of_toNat zipWith_get
  hintAt_get onesFrom onesFrom_step onesFrom_n hintOnes_single makeHint_eq useHint_eq)
open VG.Proof.MlKem.X86 (Only E0 P0 P0_esp P0_wr frameR retR LeafPost LeafEnd Piece satState toNat_ofNat32
  setWidth_append32)

theorem HPre.of_mh {s₀ : State} (h : (makeHintContract X86.abi 16).pre s₀) : HPre true s₀ := by
  sig_pre [makeHintContract, makeHintSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    fun _ => h22, h23⟩

theorem HPre.of_uh {s₀ : State} (h : (useHintContract X86.abi 16).pre s₀) : HPre false s₀ := by
  sig_pre [useHintContract, useHintSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    fun h => absurd h (by decide), h22⟩

/-! ## `useHint` -/

theorem uh_piece : Piece (HPre false) HPub (fun s₀ s => s = s₀)
    (fun s₀ s' => LeafPost (fun s => HInv (uhV (arg s₀ 2).toNat) false s₀ 256 s) s₀ s') useHint :=
  Piece.leaf (fun s₀ => [pR (pA s₀ 3), aR s₀ 4]) (NoSp.of_all (by decide +kernel))
    (fun _ hp => ⟨hp.sp, by have := hp.sp'; omega_using [this]⟩) (fun _ hp => hW hp) (fun _ _ _ _ hq => hq.1)
    ((Piece.seq (hintInit_piece false) (hint_ite (fun g hg => uhCore_spec hg) (by native_taint_decide)
      (by native_taint_decide))).mono (fun _ _ _ h => h) fun _ _ _ h => ⟨⟨h.frame, h.esp, h.rd, h.wr⟩, h⟩)

theorem uhV_lt {g : Nat} (hg : g ∈ gamma2s) (a b : Nat) : uhV g a b < 2 ^ 32 := by
  have hm : 0 < VG.Proof.MlDsa.Round.hbM g := by
    rcases VG.Proof.MlDsa.Round.mem_gamma2s hg with e | e <;> rw [e] <;> decide
  have : VG.Proof.MlDsa.Round.hbM g ≤ 44 := by
    rcases VG.Proof.MlDsa.Round.mem_gamma2s hg with e | e <;> rw [e] <;> decide
  unfold uhV
  exact Nat.lt_of_lt_of_le (Nat.mod_lt _ hm) (by omega_using [this])

theorem uh_post {s₀ s : State} (hp : HPre false s₀) (h : HInv (uhV (arg s₀ 2).toNat) false s₀ 256 s) :
    NatPolyIs s.mem (pA s₀ 3) (Vector.zipWith (fun hj rj => (VG.Spec.MlDsa.useHint (arg s₀ 2).toNat hj rj).toNat)
      ((hintAt s₀.mem (pA s₀ 0) 1).headD (Vector.replicate VG.Spec.MlDsa.n false)) (polyAt s₀.mem (pA s₀ 1))) := by
  refine natPolyIs_of_toNat fun i hi => ?_
  rw [h.out i hi, zipWith_get _ _ _ hi, hintAt_get _ _ hi, useHint_eq hp.g2, polyAt_val hp.b_red hi,
    toNat_ofNat32 (uhV_lt hp.g2 _ _), Int.toNat_natCast]
  unfold uhV
  congr 1
  by_cases e : coeffAt s₀.mem (pA s₀ 0) i = 0
  · have e' : cA s₀ i = 0 := by simp [cA, e]
    have d : decide (coeffAt s₀.mem (pA s₀ 0) i ≠ 0) = false := decide_eq_false fun h => h e
    rw [ite_eq_right_of_eq_false _ _ (eq_false fun h' => h' e')]
    simp only [d, Bool.false_eq_true, ↓reduceIte]
  · have e' : cA s₀ i ≠ 0 := fun h' => e (BitVec.eq_of_toNat_eq h')
    have d : decide (coeffAt s₀.mem (pA s₀ 0) i ≠ 0) = true := decide_eq_true e
    rw [ite_eq_left_of_eq_true _ _ (eq_true e')]
    simp only [d, ↓reduceIte]

/-- Memory with the arguments `0x400`, `0x800`, `(q - 1)/32` and `0` at `0x5004`. -/
def hintSatMem : Mem := fun a =>
  if a = 0x5005 then 4 else if a = 0x5009 then 8 else if a = 0x500d then 0xff else if a = 0x500e then 3 else 0

theorem hintSat_zero (a : Addr) (ha : a.toNat < 0x5000) : hintSatMem a = 0 := by
  simp only [hintSatMem]
  rw [ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega_using [ha]),
    ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega_using [ha]),
    ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega_using [ha]),
    ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega_using [ha])]

theorem useHint_verified : Verified X86.target useHint (useHintContract X86.abi 16) := by
  refine Piece.verified ((uh_piece.pre_mono (fun _ h => HPre.of_uh h) fun s s' _ _ h => by
      sig_pub [useHintContract, useHintSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [useHintContract, useHintSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    exact Proof.MlDsa.Arith.natPolyIs_frame hm (fun r hr => by rw [List.mem_singleton.mp hr]; exact (hW (HPre.of_uh h₀) _ List.mem_cons_self).1.symm)
      (uh_post (HPre.of_uh h₀) hinv)
  · let st := satState hintSatMem [⟨0x400, 1024⟩, ⟨0x800, 1024⟩] [⟨0, 1024⟩, ⟨0x5004, 16⟩]
    have a0 : arg st 0 = 0x400 := by decide
    have a1 : arg st 1 = 0x800 := by decide
    have a2 : arg st 2 = 261888 := by decide
    have a3 : arg st 3 = 0 := by decide
    have e : argAddr st 0 = 0x5004 := by decide
    refine ⟨st, ?_⟩
    sig_pre [useHintContract, useHintSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [a0, a1, a2, a3, e]
    refine ⟨by decide, by decide, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      by decide, by decide, by decide, by decide, reduced_zero hintSat_zero 0x800 (by decide)⟩
    all_goals exact Region.disjoint_of_sep (by decide)

/-! ## `makeHint` -/

/-- After the loops, the count to `eax`. -/
def MhEnd (s₀ s : State) : Prop :=
  HInv (mhV (arg s₀ 2).toNat) true s₀ 256 s ∧ s.gpr .eax = BitVec.ofNat 32 (sumV (mhV (arg s₀ 2).toNat) s₀ 256)

theorem mh_piece : Piece (HPre true) HPub (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (MhEnd s₀) s₀ s')
    makeHint :=
  Piece.leaf (fun s₀ => [pR (pA s₀ 3), aR s₀ 4]) (NoSp.of_all (by decide +kernel))
    (fun _ hp => ⟨hp.sp, by have := hp.sp'; omega_using [this]⟩) (fun _ hp => hW hp) (fun _ _ _ _ hq => hq.1)
    ((Piece.seq (hintInit_piece true) (Piece.seq (hint_ite (fun g hg => mhCore_spec hg) (by native_taint_decide)
      (by native_taint_decide)) (Piece.taint [] (fun s₀ s hp h => wp_mov fun s₁ u₁ => WP.block_nil_iff.mpr
        ⟨⟨by rw [u₁.other _ (by decide), h.esp], by rw [u₁.rd, h.rd], by rw [u₁.wr, h.wr],
          by rw [u₁.other _ (by decide), h.esi], by rw [u₁.other _ (by decide), h.edi],
          by rw [u₁.other _ (by decide), h.ebp], by rw [u₁.mem]; exact h.frame, by rw [u₁.mem]; exact h.slot,
          fun i hi => by rw [u₁.mem]; exact h.out i hi, fun e => by rw [u₁.other _ (by decide)]; exact h.ecx e⟩,
          by rw [u₁.gpr]; exact h.ecx rfl⟩)
        (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp)) (by native_taint_decide)))).mono (fun _ _ _ h => h)
      fun _ _ _ h => ⟨⟨h.1.frame, h.1.esp, h.1.rd, h.1.wr⟩, h⟩)

theorem mhV_le {g a b : Nat} : mhV g a b ≤ 1 := by unfold mhV; split <;> omega_using []

theorem sumV_le {g : Nat} {s₀ : State} : ∀ k, sumV (mhV g) s₀ k ≤ k
  | 0 => Nat.le_refl _
  | k + 1 => by have := sumV_le (g := g) (s₀ := s₀) k; have := @mhV_le g (cA s₀ k) (cB s₀ k); simp only [sumV]; omega_arith

/-- The hint of `makeHint`, coefficient by coefficient. -/
theorem mh_get {s₀ : State} (hp : HPre true s₀) {i : Nat} (hi : i < 256) :
    ((Vector.zipWith (VG.Spec.MlDsa.makeHint (arg s₀ 2).toNat) (polyAt s₀.mem (pA s₀ 0))
      (polyAt s₀.mem (pA s₀ 1)))[i]!).toNat = mhV (arg s₀ 2).toNat (cA s₀ i) (cB s₀ i) := by
  have hi' : i < VG.Spec.MlDsa.n := by rw [n_eq]; exact hi
  rw [zipWith_get _ _ _ hi', makeHint_eq hp.g2, polyAt_val (hp.a_red rfl) hi', polyAt_val hp.b_red hi', mhV]
  by_cases e : hbV (arg s₀ 2).toNat (cB s₀ i) = hbV (arg s₀ 2).toNat ((cB s₀ i + cA s₀ i) % q)
  · rw [ite_eq_left_of_eq_true _ _ (eq_true e)]
    simp only [hbV] at e
    simp [e]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false e)]
    simp only [hbV] at e
    simp [e]

theorem sumV_ones {s₀ : State} (hp : HPre true s₀) :
    ∀ k ≤ 256, sumV (mhV (arg s₀ 2).toNat) s₀ k + onesFrom (Vector.zipWith (VG.Spec.MlDsa.makeHint (arg s₀ 2).toNat)
      (polyAt s₀.mem (pA s₀ 0)) (polyAt s₀.mem (pA s₀ 1))) k =
      onesFrom (Vector.zipWith (VG.Spec.MlDsa.makeHint (arg s₀ 2).toNat) (polyAt s₀.mem (pA s₀ 0))
        (polyAt s₀.mem (pA s₀ 1))) 0
  | 0, _ => Nat.zero_add _
  | k + 1, hk => by
    rw [← sumV_ones hp k (by omega_using [hk]), onesFrom_step _ (show k < VG.Spec.MlDsa.n by rw [n_eq]; omega_using [hk]), mh_get hp (by omega_using [hk])]
    simp only [sumV]
    omega_using []

theorem mh_post {s₀ s : State} (hp : HPre true s₀) (h : MhEnd s₀ s) :
    HintIs s.mem (pA s₀ 3) 1 [Vector.zipWith (VG.Spec.MlDsa.makeHint (arg s₀ 2).toNat) (polyAt s₀.mem (pA s₀ 0))
      (polyAt s₀.mem (pA s₀ 1))] ∧
    (s.gpr .eax).toNat = hintOnes [Vector.zipWith (VG.Spec.MlDsa.makeHint (arg s₀ 2).toNat) (polyAt s₀.mem (pA s₀ 0))
      (polyAt s₀.mem (pA s₀ 1))] := by
  refine ⟨hintIs_of_toNat fun j hj => ?_, ?_⟩
  · rw [h.1.out j hj]
    exact congrArg (BitVec.ofNat 32) (mh_get hp hj).symm
  · rw [h.2, toNat_ofNat32 (by have := sumV_le (g := (arg s₀ 2).toNat) (s₀ := s₀) 256; omega_using [this]), hintOnes_single,
      ← sumV_ones hp 256 (Nat.le_refl _), show (256 : Nat) = VG.Spec.MlDsa.n from rfl, onesFrom_n, Nat.add_zero]

theorem makeHint_verified : Verified X86.target makeHint (makeHintContract X86.abi 16) := by
  refine Piece.verified ((mh_piece.pre_mono (fun _ h => HPre.of_mh h) fun s s' _ _ h => by
      sig_pub [makeHintContract, makeHintSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, hax⟩ := hq
    refine ⟨habi, ?_⟩
    have hp := HPre.of_mh h₀
    have ⟨p1, p2⟩ := mh_post hp hinv
    sig_post [makeHintContract, makeHintSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [setWidth_append32, hax]
    exact ⟨Proof.MlDsa.Arith.hintIs_frame hm (fun r hr => by rw [List.mem_singleton.mp hr]; exact (hW hp _ List.mem_cons_self).1.symm) p1, p2⟩
  · let st := satState hintSatMem [⟨0x400, 1024⟩, ⟨0x800, 1024⟩] [⟨0, 1024⟩, ⟨0x5004, 16⟩]
    have a0 : arg st 0 = 0x400 := by decide
    have a1 : arg st 1 = 0x800 := by decide
    have a2 : arg st 2 = 261888 := by decide
    have a3 : arg st 3 = 0 := by decide
    have e : argAddr st 0 = 0x5004 := by decide
    refine ⟨st, ?_⟩
    sig_pre [makeHintContract, makeHintSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [a0, a1, a2, a3, e]
    refine ⟨by decide, by decide, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      by decide, by decide, by decide, by decide, reduced_zero hintSat_zero 0x400 (by decide),
      reduced_zero hintSat_zero 0x800 (by decide)⟩
    all_goals exact Region.disjoint_of_sep (by decide)

end VG.Proof.MlDsa.X86.Round

end

end

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_bit_unpack` and `vg_mldsa_unpack_t1`

`bitUnpack(v, len, a, b, f)` loads `v` into `esi`, `f` into `edi` and `b` into
`eax`, and branches on `b` to the unpack loop for its width
(`unpackLoop_piece`); `unpackT1(v, f)` is the loop for 10-bit fields. The
coefficient of a field `y` is `b - y`, plus `q` if that borrows (`subModQ`),
which is `b - y` in `ℤ_q` (`Pack/Arith.lean`), or `y · 2¹³`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Pack.Unpack

open VG VG.X86 VG.Impl.MlDsa.X86.Pack
open VG.Proof.MlKem.X86 (Piece Piece.seq Piece.leaf Piece.verified P0 E0 LeafEnd LeafPost satState rotr_small)
open VG.Spec.MlDsa VG.Proof.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Pack
open VG.Proof.MlDsa.X86.Pack
open VG.Proof.MlDsa.X86.Pack.BitPack (subModQ subModQ_toNat mem_bitPackParams sh3 sh4 sh13 sh18 sh20)

/-- The word `buFin B` stores for the field `y`. -/
abbrev buWord (B y : Nat) : BitVec 32 := subModQ (BitVec.ofNat 32 B) (BitVec.ofNat 32 y)

theorem buFin_ok (B d : Nat) : FinOk (buFin B) d (buWord B) := fun j s hout _ => by
  refine WP.keep _ ?_ (by rfl)
  unfold buFin
  xrun [hout]
  rw [buWord, BitVec.ofNat_toNat]
  rfl

/-- The word `t1Fin` stores for the field `y`. -/
abbrev t1Word (y : Nat) : BitVec 32 := (BitVec.ofNat 32 y).rotateRight 19

theorem t1Fin_ok : FinOk t1Fin 10 t1Word := fun j s hout _ => by
  refine WP.keep _ ?_ (by rfl)
  unfold t1Fin
  xrun [hout]
  rw [t1Word, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- A field of `d ≤ 20` bits of the input. -/
theorem field_lt (X d k : Nat) (hd : d ≤ 20) : X / 2 ^ (d * k) % 2 ^ d < 2 ^ 20 :=
  Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos d)) (Nat.pow_le_pow_right (by decide) hd)

/-! ## `vg_mldsa_bit_unpack` -/

namespace BU

section
variable (s₀ : State)
/-- The input pointer `v`. -/
abbrev vP : State → BitVec 32 := (arg · 0)
/-- Its length. -/
abbrev vL : State → Nat := fun s₀ => (arg s₀ 1).toNat
/-- The output pointer `f`. -/
abbrev fP : State → BitVec 32 := (arg · 4)
/-- `a`. -/
abbrev aN : Nat := (arg s₀ 2).toNat
/-- `b`. -/
abbrev bN : Nat := (arg s₀ 3).toNat
end

structure Pre (s₀ : State) : Prop where
  lay : Lay 5 vP fP vL (fun _ => 1024) s₀
  ab : (aN s₀, bN s₀) ∈ bitPackParams
  len_eq : (arg s₀ 1).toNat = 32 * bitlen (aN s₀ + bN s₀)

theorem Pre.of {s₀ : State} (h : (bitUnpackContract X86.abi 16).pre s₀) : Pre s₀ := by
  sig_pre [bitUnpackContract, bitUnpackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩, h16, h17⟩

def Pub (s₀ s₀' : State) : Prop :=
  E0 s₀ = E0 s₀' ∧ arg s₀ 0 = arg s₀' 0 ∧ arg s₀ 1 = arg s₀' 1 ∧ arg s₀ 2 = arg s₀' 2 ∧
    arg s₀ 3 = arg s₀' 3 ∧ arg s₀ 4 = arg s₀' 4

/-- The end of every branch. -/
def Fin (s₀ s : State) : Prop :=
  LeafEnd s₀ [outR fP (fun _ => 1024) s₀] s ∧
    PolyIs s.mem (oA fP s₀) (toRq (bitUnpack (bytesAt s₀.mem (iA vP s₀) (arg s₀ 1).toNat) (aN s₀) (bN s₀)))

/-- The loop for `b = B`, of width `d = bitlen (a + b)`. -/
theorem branch {d c nb B : Nat} (hs : Shape d c nb) (hB : B ≤ 2 ^ 19) {X : State → Prop}
    (hX : ∀ s₀, Pre s₀ → X s₀ → bN s₀ = B ∧ bitlen (aN s₀ + B) = d) {h₁ : Taint.Hint VG.X86.Taint.T}
    (ht₁ : (VG.X86.taint.check (τr []) (.block [.mov .ecx (.imm (BitVec.ofNat 32 (256 / c)))]) h₁).isSome = true)
    {h₂ : Taint.Hint VG.X86.Taint.T}
    (ht₂ : (VG.X86.taint.check (τr loopRegs) (.block (unpackBody (buFin B) d c nb)) h₂).isSome = true) :
    Piece Pre Pub (fun s₀ s => Start vP fP s₀ s ∧ X s₀) Fin (unpackLoop (buFin B) d c nb) := by
  have hq : q = 8380417 := rfl
  have hlen : ∀ s₀, Pre s₀ → X s₀ → (arg s₀ 1).toNat = 32 * d := fun s₀ h₀ hx => by
    rw [h₀.len_eq, (hX s₀ h₀ hx).1, (hX s₀ h₀ hx).2]
  refine (unpackLoop_piece (buFin_ok B d) hs vP fP (X := X) (fun s₀ h₀ hx => ?_)
    (fun _ _ _ _ hq => ⟨hq.1, hq.2.1, hq.2.2.2.2.2⟩) ht₁ ht₂).mono (fun _ _ _ h => h)
    (fun s₀ s h₀ ⟨⟨he, hc⟩, hx⟩ => ?_)
  · have hp := h₀.lay
    have hi : inR vP vL s₀ = ⟨iA vP s₀, 32 * d⟩ := by simp only [inR, vL, hlen s₀ h₀ hx]
    exact ⟨by rw [← hi]; exact hp.inR_mem, hp.outR_mem, by rw [← hi]; exact hp.i_o,
      by have := hp.i_fit; rwa [vL, hlen s₀ h₀ hx] at this, hp.o_fit⟩
  · have hp := h₀.lay
    obtain ⟨e₁, e₂⟩ := hX s₀ h₀ hx
    refine ⟨he, polyIs_of_toNat fun i hi => ?_⟩
    have hy := field_lt (inNum (P0 s₀).mem (iA vP s₀) d) d i hs.d20
    have hy' := hy
    unfold inNum at hy'
    rw [hp.bytes_keep (by simp only [vL]; rw [hlen s₀ h₀ hx])] at hy'
    rw [hc i hi, buWord, subModQ_toNat (by rw [BitVec.toNat_ofNat]; omega_arith) (by rw [BitVec.toNat_ofNat]; omega_arith),
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show B < 2 ^ 32 by omega_arith),
      Nat.mod_eq_of_lt (show _ < 2 ^ 32 by omega_arith), toRq, Vector.getElem_map, bitUnpack_get _ _ _ hi,
      hlen s₀ h₀ hx, e₁, e₂, ofInt_sub (by omega_arith), inNum, hp.bytes_keep (by simp only [vL]; rw [hlen s₀ h₀ hx])]

/-- The branch for `b = B` is the one for `a = A`, of width `d'`. -/
theorem pick {s₀ : State} (h₀ : Pre s₀) {A B d' : Nat} (hd : bitlen (A + B) = d') (e : (arg s₀ 3).toNat = B)
    (hA : ∀ a, (a = 2 ∧ B = 2) ∨ (a = 4 ∧ B = 4) ∨ (a = 4095 ∧ B = 4096) ∨ (a = 131071 ∧ B = 131072) ∨
      (a = 524287 ∧ B = 524288) → a = A) : bN s₀ = B ∧ bitlen (aN s₀ + B) = d' := by
  have := mem_bitPackParams h₀.ab
  rw [show bN s₀ = B from e] at this
  rw [hA _ this]; exact ⟨e, hd⟩

theorem body_piece : Piece Pre Pub (fun s₀ s => s = P0 s₀) Fin
    (.seq (.block (ldArgs 0 4 3))
      (sel 2 (unpackLoop (buFin 2) 3 8 3)
        (sel 4 (unpackLoop (buFin 4) 4 2 1)
          (sel 4096 (unpackLoop (buFin 4096) 13 8 13)
            (sel 131072 (unpackLoop (buFin 131072) 18 4 9) (unpackLoop (buFin 524288) 20 2 5)))))) := by
  have hw : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → arg s₀ 3 = arg s₀' 3 := fun _ _ _ _ hq => hq.2.2.2.2.1
  refine Piece.seq (ldArgs_piece (k := 5) (by decide) (by decide) (by decide) (fun _ h => h.lay)
    (fun _ _ _ _ hq => hq.1) (by native_taint_decide)) ?_
  refine sel_piece (arg · 3) (by decide) hw (by native_taint_decide)
    (branch sh3 (by decide) (fun s₀ h₀ ⟨_, e⟩ => pick h₀ (A := 2) (by decide) e fun _ _ => by omega_arith)
      (by native_taint_decide) (by native_taint_decide)) ?_
  refine sel_piece (arg · 3) (by decide) hw (by native_taint_decide)
    (branch sh4 (by decide) (fun s₀ h₀ ⟨_, e⟩ => pick h₀ (A := 4) (by decide) e fun _ _ => by omega_arith)
      (by native_taint_decide) (by native_taint_decide)) ?_
  refine sel_piece (arg · 3) (by decide) hw (by native_taint_decide)
    (branch sh13 (by decide) (fun s₀ h₀ ⟨_, e⟩ => pick h₀ (A := 4095) (by decide) e fun _ _ => by omega_arith)
      (by native_taint_decide) (by native_taint_decide)) ?_
  refine sel_piece (arg · 3) (by decide) hw (by native_taint_decide)
    (branch sh18 (by decide) (fun s₀ h₀ ⟨_, e⟩ => pick h₀ (A := 131071) (by decide) e fun _ _ => by omega_arith)
      (by native_taint_decide) (by native_taint_decide)) ?_
  refine (branch sh20 (B := 524288) (by decide) (fun s₀ h₀ ⟨⟨⟨⟨_, e₂⟩, e₄⟩, e₄₀⟩, e₁₃⟩ =>
      pick h₀ (A := 524287) (by decide) (by have := mem_bitPackParams h₀.ab; simp only [aN, bN] at this; omega_arith)
        fun _ _ => by omega_arith)
      (by native_taint_decide) (by native_taint_decide)).mono (fun _ _ _ ⟨⟨h, _⟩, hx⟩ => ⟨h, hx⟩) fun _ _ _ h => h

theorem piece : Piece Pre Pub (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (Fin s₀) s₀ s')
    Impl.MlDsa.X86.Pack.bitUnpack :=
  Piece.leaf (fun s₀ => [outR fP (fun _ => 1024) s₀]) (NoSp.of_all (by decide +kernel))
    (fun _ h => h.lay.leafE) (fun _ h => h.lay.leafW) (fun _ _ _ _ hq => hq.1)
    (body_piece.mono (fun _ _ _ h => h) fun _ _ _ h => ⟨h.1, h⟩)

/-- Memory with the arguments `0`, `96`, `2`, `2` and `0x400` at `0x5004`. -/
def satMem : Mem := fun a =>
  if a = 0x5008 then 96 else if a = 0x500c then 2 else if a = 0x5010 then 2 else if a = 0x5015 then 4 else 0

theorem verified : Verified X86.target Impl.MlDsa.X86.Pack.bitUnpack (bitUnpackContract X86.abi 16) := by
  refine Piece.verified ((piece.pre_mono (fun _ h => Pre.of h) fun s s' _ _ h => by
      sig_pub [bitUnpackContract, bitUnpackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [bitUnpackContract, bitUnpackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    exact Proof.MlDsa.Arith.polyIs_frame hm (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ((Pre.of h₀).lay.leafW _ List.mem_cons_self).1.symm) hinv.2
  · let st := satState satMem [⟨0, 96⟩] [⟨0x400, 1024⟩, ⟨0x5004, 20⟩]
    have a0 : arg st 0 = 0 := by decide
    have a1 : arg st 1 = 96 := by decide
    have a2 : arg st 2 = 2 := by decide
    have a3 : arg st 3 = 2 := by decide
    have a4 : arg st 4 = 0x400 := by decide
    have e : argAddr st 0 = 0x5004 := by decide
    refine ⟨st, ?_⟩
    sig_pre [bitUnpackContract, bitUnpackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [a0, a1, a2, a3, a4, e]
    and_intros
    all_goals first
      | rfl
      | exact Region.disjoint_of_sep (by decide)
      | (simp only [bitPackParams]; decide)
      | decide

end BU

/-! ## `vg_mldsa_unpack_t1` -/

namespace T1

/-- The input pointer `v`. -/
abbrev vP : State → BitVec 32 := (arg · 0)
/-- The output pointer `f`. -/
abbrev fP : State → BitVec 32 := (arg · 1)

abbrev Pre (s₀ : State) : Prop := Lay 2 vP fP (fun _ => 320) (fun _ => 1024) s₀

theorem Pre.of {s₀ : State} (h : (unpackT1Contract X86.abi 16).pre s₀) : Pre s₀ := by
  sig_pre [unpackT1Contract, unpackT1Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩

def Pub (s₀ s₀' : State) : Prop := E0 s₀ = E0 s₀' ∧ arg s₀ 0 = arg s₀' 0 ∧ arg s₀ 1 = arg s₀' 1

/-- The end of the loop. -/
def Fin (s₀ s : State) : Prop :=
  LeafEnd s₀ [outR fP (fun _ => 1024) s₀] s ∧
    PolyIs s.mem (oA fP s₀) ((simpleBitUnpack (bytesAt s₀.mem (iA vP s₀) 320) t1Max).map
      fun c => ofInt (c * 2 ^ d : Nat))

theorem sh10 : Shape 10 4 5 := ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩

theorem body_piece : Piece Pre Pub (fun s₀ s => s = P0 s₀) Fin
    (.seq (.block (ldPtrs 0 1)) (unpackLoop t1Fin 10 4 5)) := by
  refine Piece.seq (ldPtrs_piece (k := 2) (by decide) (by decide) (fun _ h => h)
    (fun _ _ _ _ hq => hq.1) (by native_taint_decide)) ?_
  refine (unpackLoop_piece t1Fin_ok sh10 vP fP (X := fun _ => True) (fun s₀ hp _ => ?_)
    (fun _ _ _ _ hq => hq) (by native_taint_decide) (by native_taint_decide)).mono (fun _ _ _ h => h)
    (fun s₀ s hp ⟨⟨he, hc⟩, _⟩ => ⟨he, polyIs_of_toNat fun i hi => ?_⟩)
  · exact ⟨hp.inR_mem, hp.outR_mem, hp.i_o, hp.i_fit, hp.o_fit⟩
  · rw [hc i hi, inNum, hp.bytes_keep (by decide)]
    have hy := Nat.mod_lt (Proof.MlKem.digits 8 ((bytesAt s₀.mem (iA vP s₀) 320).map (·.toNat)) / 2 ^ (10 * i))
      (show 2 ^ 10 > 0 by decide)
    rw [t1Word, rotr_small _ (by decide) (by decide) (by rw [BitVec.toNat_ofNat]; omega_arith),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show _ < 2 ^ 32 by omega_arith), show 32 - 19 = 13 from rfl,
      Vector.getElem_map, simpleBitUnpack_get _ _ hi, show bitlen t1Max = 10 by decide, ofInt_t1 hy]

theorem piece : Piece Pre Pub (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (Fin s₀) s₀ s')
    Impl.MlDsa.X86.Pack.unpackT1 :=
  Piece.leaf (fun s₀ => [outR fP (fun _ => 1024) s₀]) (NoSp.of_all (by decide +kernel))
    (fun _ h => h.leafE) (fun _ h => h.leafW) (fun _ _ _ _ hq => hq.1)
    (body_piece.mono (fun _ _ _ h => h) fun _ _ _ h => ⟨h.1, h⟩)

/-- Memory with the arguments `0` and `0x400` at `0x5004`. -/
def satMem : Mem := fun a => if a = 0x5009 then 4 else 0

theorem verified : Verified X86.target Impl.MlDsa.X86.Pack.unpackT1 (unpackT1Contract X86.abi 16) := by
  refine Piece.verified ((piece.pre_mono (fun _ h => Pre.of h) fun s s' _ _ h => by
      sig_pub [unpackT1Contract, unpackT1Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [unpackT1Contract, unpackT1Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    exact Proof.MlDsa.Arith.polyIs_frame hm (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ((Pre.of h₀).leafW _ List.mem_cons_self).1.symm) hinv.2
  · refine ⟨satState satMem [⟨0, 320⟩] [⟨0x400, 1024⟩, ⟨0x5004, 8⟩], ?_⟩
    sig_sat_check [unpackT1Contract, unpackT1Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]

end T1

end VG.Proof.MlDsa.X86.Pack.Unpack
