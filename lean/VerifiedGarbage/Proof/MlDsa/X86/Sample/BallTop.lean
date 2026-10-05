import VerifiedGarbage.Proof.MlDsa.X86.Sample.RejNtt
import VerifiedGarbage.Proof.MlDsa.Sample.Signs
import VerifiedGarbage.Impl.MlDsa.X86.Sample.Ball

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Sample.Ball`. -/
section

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

namespace VG.Proof.MlDsa.X86.Sample.Ball

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86
open VG.Proof.MlDsa.X86.Sample
open VG.Proof.MlDsa.Sample
open VG.Impl.MlDsa.X86.Sample (argOp bZero bSetup qImm sponge outOff)
open VG.Spec.MlDsa (Zq q H n ofInt coeffAt IPoly ballParams)
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.X86.Sample (cR E1)

/-- The layout: `sampleInBall(ctilde, len, tau, c, scratch)`, `len` bytes of
`c̃`, 272 bytes of SHAKE256. -/
def L : VG.Proof.MlDsa.X86.Sample.Lay := { nA := 5, iA := 3, iS := 4, rate := 136, outlen := 272, mlen := none }

theorem hL : L.Ok :=
  ⟨by decide, by decide, by decide, by decide, by decide, fun k hk => by simp [VG.Proof.MlDsa.X86.Sample.Ball.L] at hk,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

/-- `τ`. -/
abbrev τ (s₀ : State) : Nat := (arg s₀ 2).toNat

/-- The precondition. -/
def QPre (s₀ : State) : Prop := VG.Proof.MlDsa.X86.Sample.Pre VG.Proof.MlDsa.X86.Sample.Ball.L s₀ ∧ ((arg s₀ 1).toNat, VG.Proof.MlDsa.X86.Sample.Ball.τ s₀) ∈ ballParams

/-- The pointers, `esp` and `c̃` agree. -/
def QPub (s₀ s₀' : State) : Prop := PubP VG.Proof.MlDsa.X86.Sample.Ball.L s₀ s₀' ∧ L.Msg s₀ = L.Msg s₀'

theorem QPre.τ_le {s₀ : State} (hp : VG.Proof.MlDsa.X86.Sample.Ball.QPre s₀) : VG.Proof.MlDsa.X86.Sample.Ball.τ s₀ ≤ 60 := by
  have h := hp.2
  simp only [ballParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  omega

theorem QPre.len {s₀ : State} (hp : VG.Proof.MlDsa.X86.Sample.Ball.QPre s₀) : (arg s₀ 1).toNat < 136 := by
  have h := hp.2
  simp only [ballParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  omega

/-! ## The loop of `SampleInBall`, from the message -/

/-- The output. -/
abbrev Xb (B : List Byte) : List Byte := H B 272

/-- The sign bits, as an integer. -/
abbrev Sg (B : List Byte) : Nat := leNat ((VG.Proof.MlDsa.X86.Sample.Ball.Xb B).take 8)

/-- The state of the loop after `k` iterations. -/
abbrev st (B : List Byte) (τ : Nat) (k : Nat) : IPoly × Nat :=
  bFold τ (signs (VG.Proof.MlDsa.X86.Sample.Ball.Xb B)) (Vector.replicate VG.Spec.MlDsa.n 0, 256 - τ) (((VG.Proof.MlDsa.X86.Sample.Ball.Xb B).drop 8).take k)

/-- The byte of iteration `k`. -/
abbrev jb (B : List Byte) (k : Nat) : Byte := (VG.Proof.MlDsa.X86.Sample.Ball.Xb B).getD (8 + k) 0

/-- The signs used after `k` iterations. -/
abbrev tu (B : List Byte) (τ k : Nat) : Nat := (VG.Proof.MlDsa.X86.Sample.Ball.st B τ k).2 + τ - 256

theorem out_eq (s₀ : State) : L.out s₀ = VG.Proof.MlDsa.X86.Sample.Ball.Xb (L.Msg s₀) := (VG.Proof.MlDsa.Sample.H_eq _ _).symm

theorem Xb_length (B : List Byte) : (VG.Proof.MlDsa.X86.Sample.Ball.Xb B).length = 272 := VG.Proof.MlDsa.Sample.H_length _ _

theorem st_zero (B : List Byte) (τ : Nat) : VG.Proof.MlDsa.X86.Sample.Ball.st B τ 0 = (Vector.replicate VG.Spec.MlDsa.n 0, 256 - τ) := by
  simp [VG.Proof.MlDsa.X86.Sample.Ball.st, bFold]

theorem st_succ (B : List Byte) (τ : Nat) {k : Nat} (hk : k < 264) :
    VG.Proof.MlDsa.X86.Sample.Ball.st B τ (k + 1) = bStep τ (signs (VG.Proof.MlDsa.X86.Sample.Ball.Xb B)) (VG.Proof.MlDsa.X86.Sample.Ball.st B τ k) (VG.Proof.MlDsa.X86.Sample.Ball.jb B k) := by
  have hl : ((VG.Proof.MlDsa.X86.Sample.Ball.Xb B).drop 8).length = 264 := by rw [List.length_drop, VG.Proof.MlDsa.X86.Sample.Ball.Xb_length]
  simp only [VG.Proof.MlDsa.X86.Sample.Ball.st]
  rw [List.take_add_one, List.getElem?_eq_getElem (by rw [hl]; exact hk), Option.toList_some, bFold_snoc]
  congr 1
  rw [VG.Proof.MlDsa.X86.Sample.Ball.jb, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [VG.Proof.MlDsa.X86.Sample.Ball.Xb_length]; omega), Option.getD_some,
    List.getElem_drop]

theorem st_le (B : List Byte) (τ k : Nat) : (VG.Proof.MlDsa.X86.Sample.Ball.st B τ k).2 ≤ 256 := bFold_le (by simp [VG.Spec.MlDsa.n]) _

theorem st_ge (B : List Byte) (τ k : Nat) : 256 - τ ≤ (VG.Proof.MlDsa.X86.Sample.Ball.st B τ k).2 :=
  bFold_ge (Vector.replicate VG.Spec.MlDsa.n 0, 256 - τ) _

/-! ## The state of the loop -/

/-- Iteration `k`, with the loop's state `S`. -/
structure BI (s₀ : State) (k : Nat) (S : IPoly × Nat) (s : State) : Prop extends Base VG.Proof.MlDsa.X86.Sample.Ball.L s₀ s where
  out : ∀ p < 272, s.mem (L.sA s₀ + BitVec.ofNat 64 (840 + p)) = (VG.Proof.MlDsa.X86.Sample.Ball.Xb (L.Msg s₀)).getD p 0
  esi : s.gpr .esi = L.sP s₀ + BitVec.ofNat 32 (848 + k)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (264 - k)
  ebp : s.gpr .ebp = L.aP s₀
  edi : s.gpr .edi = BitVec.ofNat 32 S.2
  poly : ∀ j < 256, coeffAt s.mem (L.aA s₀) j = zw (ofInt S.1[j]!)
  lo : s.mem.readW (argAddr s₀ 1) 32 = BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Sample.Ball.Sg (L.Msg s₀) / 2 ^ (S.2 + VG.Proof.MlDsa.X86.Sample.Ball.τ s₀ - 256))
  hi : s.mem.readW (argAddr s₀ 2) 32 = BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Sample.Ball.Sg (L.Msg s₀) / 2 ^ (S.2 + VG.Proof.MlDsa.X86.Sample.Ball.τ s₀ - 256 + 32))

/-! ## `c` zeroed -/

/-- After `k` words of `c`. -/
structure ZI (s₀ : State) (k : Nat) (s : State) : Prop extends Out VG.Proof.MlDsa.X86.Sample.Ball.L s₀ s where
  ebp : s.gpr .ebp = L.aP s₀
  eax : s.gpr .eax = 0
  edi : s.gpr .edi = L.aP s₀ + BitVec.ofNat 32 (4 * k)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (256 - k)
  zero : ∀ j < k, coeffAt s.mem (L.aA s₀) j = 0

theorem zinit_piece : Piece VG.Proof.MlDsa.X86.Sample.Ball.QPre VG.Proof.MlDsa.X86.Sample.Ball.QPub (Out VG.Proof.MlDsa.X86.Sample.Ball.L) (VG.Proof.MlDsa.X86.Sample.Ball.ZI · 0)
    (.block [.mov .ebp (.mem (argOp 3)), .mov .eax (.imm 0), .mov .edi (.reg .ebp), .mov .ecx (.imm 256)]) := by
  refine Piece.taint [.esp] (fun s₀ s hp h => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_) (by taint_decide)
  · have a₃ := h.argEa (i := 3)
    have i₃ := h.argIn hp.1 (i := 3) (by decide)
    have v₃ := h.args 3 (by decide)
    simp only [Nat.reduceMul, Nat.reduceAdd] at a₃
    apply WP.of_runBlock
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceAdd, Nat.reduceMul, argOp, at_, runBlock_cons, runStep_some, runBlock_nil, exec,
      readSrc, State.ea, State.load32, State.setReg, Option.map_some, a₃, i₃, v₃,
      Option.some.injEq, exists_eq_left']
    exact ⟨⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, h.args, by simp [h.esi]⟩, h.out⟩, by simp; rfl, by simp,
      by simp; rfl, by simp, fun j hj => absurd hj (by omega)⟩
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.esp, h'.esp, hq.1.e1]

theorem zstep {s₀ : State} (hp : VG.Proof.MlDsa.X86.Sample.Ball.QPre s₀) {k : Nat} (hk : k < 256) {s : State} (h : VG.Proof.MlDsa.X86.Sample.Ball.ZI s₀ k s) :
    WP isa (.block [.store (at_ .edi 0) .eax, .alu .add .edi (.imm 4), .alu .sub .ecx (.imm 1)]) s
      fun s' => VG.Proof.MlDsa.X86.Sample.Ball.ZI s₀ (k + 1) s' ∧ VG.X86.eval .ne s' = some (decide (k + 1 < 256)) := by
  have ha := hp.1.a_fit
  have ea : (L.aP s₀ + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 0).setWidth 64 = coeffAddr (L.aA s₀) k := by
    rw [ea_add (by simp only [VG.Proof.MlDsa.X86.Sample.Ball.L] at ha ⊢; omega)]; rfl
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
    exact hp.1.a_s _ hc ((hp.1.sub_s (o := 840 + p) (n := 1) (by simp only [VG.Proof.MlDsa.X86.Sample.Ball.L] at hp' ⊢; omega)) _
      (Region.contains_self _ _))
  · simp only [ite_true]
    rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, add_ofNat_add]; congr 2
  · simp only [ite_true, h.ecx]
    exact cnt_next hk
  · rw [coeffAt_writeW _ _ (by omega) hk]
    by_cases e : k = j
    · rw [ifT e]
    · rw [ifF e]; exact h.zero j (by omega)
  · simp only [VG.X86.eval, h.ecx]
    exact cnt_ne hk (by omega)

theorem zero_piece : Piece VG.Proof.MlDsa.X86.Sample.Ball.QPre VG.Proof.MlDsa.X86.Sample.Ball.QPub (Out VG.Proof.MlDsa.X86.Sample.Ball.L) (VG.Proof.MlDsa.X86.Sample.Ball.ZI · 256) bZero :=
  Piece.seq VG.Proof.MlDsa.X86.Sample.Ball.zinit_piece (Piece.countLoop (by decide) (fun k s₀ s => VG.Proof.MlDsa.X86.Sample.Ball.ZI s₀ k s) [.edi]
    (fun k hk s₀ s hp h => VG.Proof.MlDsa.X86.Sample.Ball.zstep hp hk h)
    (fun k _ s₀ s₀' s s' _ _ hq h h' r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      rw [h.edi, h'.edi, hq.1.aP VG.Proof.MlDsa.X86.Sample.Ball.hL]) (by taint_decide))

/-! ## The setup of the loop -/

theorem argAddr_eq {s₀ : State} (hp : VG.Proof.MlDsa.X86.Sample.Ball.QPre s₀) {i : Nat} (hi : i < 5) :
    argAddr s₀ i = (E0 s₀).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) :=
  ea_off (by have := hp.1.sp'; simp only [VG.Proof.MlDsa.X86.Sample.Ball.L, E0] at this ⊢; omega)

/-- The two argument slots of the sign bits, apart. -/
theorem slots_sep {s₀ : State} (hp : VG.Proof.MlDsa.X86.Sample.Ball.QPre s₀) : Mem.Sep (argAddr s₀ 1) 4 (argAddr s₀ 2) 4 := by
  rw [VG.Proof.MlDsa.X86.Sample.Ball.argAddr_eq hp (by decide), VG.Proof.MlDsa.X86.Sample.Ball.argAddr_eq hp (by decide)]
  exact Offset.sep _ (by omega) (by omega) (by omega)

theorem setup_piece : Piece VG.Proof.MlDsa.X86.Sample.Ball.QPre VG.Proof.MlDsa.X86.Sample.Ball.QPub (VG.Proof.MlDsa.X86.Sample.Ball.ZI · 256) (fun s₀ s => VG.Proof.MlDsa.X86.Sample.Ball.BI s₀ 0 (VG.Proof.MlDsa.X86.Sample.Ball.st (L.Msg s₀) (VG.Proof.MlDsa.X86.Sample.Ball.τ s₀) 0) s)
    (.block bSetup) := by
  refine Piece.taint [.esp, .esi] (fun s₀ s hp h => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_)
    (by taint_decide)
  · have hs := hp.1.s_fit
    have a₁ := h.argEa (i := 1)
    have a₂ := h.argEa (i := 2)
    have i₂ := h.argIn hp.1 (i := 2) (by decide)
    have v₂ := h.args 2 (by decide)
    have w₁ := h.argInW hp.1 (i := 1) (by decide)
    have w₂ := h.argInW hp.1 (i := 2) (by decide)
    simp only [Nat.reduceMul, Nat.reduceAdd] at a₁ a₂
    have e0 : (L.sP s₀ + BitVec.ofNat 32 840).setWidth 64 = L.sA s₀ + BitVec.ofNat 64 840 := hp.1.off_eq (by omega)
    have e4 : (L.sP s₀ + BitVec.ofNat 32 844).setWidth 64 = L.sA s₀ + BitVec.ofNat 64 844 := hp.1.off_eq (by omega)
    have r0 := hp.1.inS' h.wr (o := 840) (n := 4) (by omega)
    have r4 := hp.1.inS' h.wr (o := 844) (n := 4) (by omega)
    have hb : ∀ b < 8, s.mem (L.sA s₀ + BitVec.ofNat 64 840 + BitVec.ofNat 64 b) = (VG.Proof.MlDsa.X86.Sample.Ball.Xb (L.Msg s₀)).getD b 0 :=
      fun b hb => by rw [BitVec.add_assoc, ← BitVec.ofNat_add, h.out b (by simp only [VG.Proof.MlDsa.X86.Sample.Ball.L]; omega), VG.Proof.MlDsa.X86.Sample.Ball.out_eq]
    have vlo := readW_lo s.mem _ _ hb
    have vhi := readW_hi s.mem _ _ hb
    rw [BitVec.add_assoc, show BitVec.ofNat 64 840 + (4 : BitVec 64) = BitVec.ofNat 64 844 from rfl] at vhi
    have hτ := hp.τ_le
    have fin : ∀ s' : State, s'.gpr .esp = s.gpr .esp → s'.gpr .esi = L.sP s₀ + BitVec.ofNat 32 848 →
        s'.gpr .ecx = BitVec.ofNat 32 264 → s'.gpr .ebp = s.gpr .ebp → s'.gpr .edi = 256 - arg s₀ 2 →
        s'.rd = s.rd → s'.wr = s.wr →
        s'.mem = (s.mem.writeW (argAddr s₀ 1) (BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Sample.Ball.Sg (L.Msg s₀) / 2 ^ 0))).writeW (argAddr s₀ 2)
          (BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Sample.Ball.Sg (L.Msg s₀) / 2 ^ (0 + 32))) →
        VG.Proof.MlDsa.X86.Sample.Ball.BI s₀ 0 (VG.Proof.MlDsa.X86.Sample.Ball.st (L.Msg s₀) (VG.Proof.MlDsa.X86.Sample.Ball.τ s₀) 0) s' := by
      intro s' e1 e2 e3 e4 e5 e6 e7 e8
      have f₁ : Frame [L.gR s₀] s.mem s'.mem := by
        rw [e8]
        exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (VG.Proof.MlKem.X86.arg_contains (n := 5) (by decide) hp.1.sp')).writeW
          (List.mem_singleton_self _) _ (VG.Proof.MlKem.X86.arg_contains (n := 5) (by decide) hp.1.sp')
      rw [VG.Proof.MlDsa.X86.Sample.Ball.st_zero]
      refine ⟨⟨by rw [e1, h.esp], by rw [e6, h.rd], by rw [e7, h.wr], h.frame.trans (f₁.mono (by simp))⟩,
        fun p hp' => ?_, e2, e3, by rw [e4, h.ebp], ?_, fun j hj => ?_, ?_, ?_⟩
      · rw [f₁.bytes (R := ⟨L.sA s₀, 2048⟩) (by simp only [List.mem_singleton, forall_eq]; exact hp.1.s_g)
          (show (2048 : Nat) ≤ 2 ^ 64 by decide) (show 840 + p < 2048 by omega)]
        rw [h.out p hp', VG.Proof.MlDsa.X86.Sample.Ball.out_eq]
      · rw [e5]
        exact eq_ofNat_of_toNat (by
          rw [BitVec.toNat_sub, show (256 : BitVec 32).toNat = 256 from rfl]
          simp only [VG.Proof.MlDsa.X86.Sample.Ball.τ] at hτ ⊢
          omega)
      · rw [coeffAt_eq, f₁.readW (coeff_contains _ hj) (by simp only [List.mem_singleton, forall_eq]; exact hp.1.a_g)
          (by decide), ← coeffAt_eq, h.zero j hj,
          getElem!_pos (Vector.replicate VG.Spec.MlDsa.n (0 : Int)) j (by simp only [VG.Spec.MlDsa.n]; omega), Vector.getElem_replicate]
        decide
      · rw [e8, Mem.readW_writeW_sep (VG.Proof.MlDsa.X86.Sample.Ball.slots_sep hp) (by decide), Mem.readW_writeW_self32,
          show 256 - VG.Proof.MlDsa.X86.Sample.Ball.τ s₀ + VG.Proof.MlDsa.X86.Sample.Ball.τ s₀ - 256 = 0 by omega]
      · rw [e8, Mem.readW_writeW_self32, show 256 - VG.Proof.MlDsa.X86.Sample.Ball.τ s₀ + VG.Proof.MlDsa.X86.Sample.Ball.τ s₀ - 256 = 0 by omega]
    apply WP.of_runBlock
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceMul, Nat.reducePow, bSetup, argOp, outOff, at_, runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu, readSrc, State.ea, State.load32, State.store32, State.setReg, arithFlags, State.setFlags,
      Option.map_some, Option.bind_some, h.esi, a₁, a₂, i₂, v₂, w₁, w₂, e0, e4, r0, r4, vlo, vhi, Nat.reduceAdd,
      Option.some.injEq, exists_eq_left']
    exact fin _ (by simp) (by simp) (by simp) (by simp) (by simp) rfl rfl rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h.esp, h'.esp, hq.1.e1]
    · rw [h.esi, h'.esi, hq.1.sP VG.Proof.MlDsa.X86.Sample.Ball.hL]

end VG.Proof.MlDsa.X86.Sample.Ball

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Sample.BallLoop`. -/
section

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

namespace VG.Proof.MlDsa.X86.Sample.Ball

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86
open VG.Proof.MlDsa.X86.Sample
open VG.Proof.MlDsa.Sample
open VG.Impl.MlDsa.X86.Sample (argOp bMove bShift bSet bTry bBody qImm)
open VG.Spec.MlDsa (Zq q H n ofInt coeffAt IPoly)
open VG.Proof.MlDsa.X86.Sample.RejNtt (nil_piece)

/-- The state of iteration `k`. -/
abbrev S' (s₀ : State) (k : Nat) : IPoly × Nat := VG.Proof.MlDsa.X86.Sample.Ball.st (L.Msg s₀) (VG.Proof.MlDsa.X86.Sample.Ball.τ s₀) k

/-- The byte of iteration `k`. -/
abbrev j' (s₀ : State) (k : Nat) : Nat := (VG.Proof.MlDsa.X86.Sample.Ball.jb (L.Msg s₀) k).toNat

/-- The signs used before iteration `k`. -/
abbrev t' (s₀ : State) (k : Nat) : Nat := (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ k).2 + VG.Proof.MlDsa.X86.Sample.Ball.τ s₀ - 256

/-- The sign bits. -/
abbrev G (s₀ : State) : Nat := VG.Proof.MlDsa.X86.Sample.Ball.Sg (L.Msg s₀)

/-- The coefficient iteration `k` sets `c[j]` to. -/
abbrev sg (s₀ : State) (k : Nat) : Int := if (signs (VG.Proof.MlDsa.X86.Sample.Ball.Xb (L.Msg s₀))).getD (VG.Proof.MlDsa.X86.Sample.Ball.t' s₀ k) false then -1 else 1

theorem G_lt (s₀ : State) : VG.Proof.MlDsa.X86.Sample.Ball.G s₀ < 2 ^ 64 := by
  have := leNat_lt ((VG.Proof.MlDsa.X86.Sample.Ball.Xb (L.Msg s₀)).take 8)
  rwa [List.length_take, VG.Proof.MlDsa.X86.Sample.Ball.Xb_length, show min 8 272 = 8 from rfl] at this

theorem sg_eq (s₀ : State) (k : Nat) : VG.Proof.MlDsa.X86.Sample.Ball.sg s₀ k = if (VG.Proof.MlDsa.X86.Sample.Ball.G s₀).testBit (VG.Proof.MlDsa.X86.Sample.Ball.t' s₀ k) then -1 else 1 := by
  simp only [VG.Proof.MlDsa.X86.Sample.Ball.sg, signs_getD]

/-- The polynomial with `c[i] ← c[j]`. -/
abbrev P1 (s₀ : State) (k : Nat) : IPoly := (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ k).1.set! (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ k).2 (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ k).1[VG.Proof.MlDsa.X86.Sample.Ball.j' s₀ k]!

/-- After `c[i] ← c[j]`, with the next sign bit in `ebx` (and ZF). -/
structure M1 (s₀ : State) (k : Nat) (s : State) : Prop extends Base VG.Proof.MlDsa.X86.Sample.Ball.L s₀ s where
  out : ∀ p < 272, s.mem (L.sA s₀ + BitVec.ofNat 64 (840 + p)) = (VG.Proof.MlDsa.X86.Sample.Ball.Xb (L.Msg s₀)).getD p 0
  esi : s.gpr .esi = L.sP s₀ + BitVec.ofNat 32 (848 + k)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (264 - k)
  ebp : s.gpr .ebp = L.aP s₀
  edi : s.gpr .edi = BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ k).2
  eax : s.gpr .eax = L.aP s₀ + BitVec.ofNat 32 (4 * VG.Proof.MlDsa.X86.Sample.Ball.j' s₀ k)
  poly : ∀ jj < 256, coeffAt s.mem (L.aA s₀) jj = zw (ofInt (VG.Proof.MlDsa.X86.Sample.Ball.P1 s₀ k)[jj]!)
  lo : s.mem.readW (argAddr s₀ 1) 32 = BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Sample.Ball.G s₀ / 2 ^ VG.Proof.MlDsa.X86.Sample.Ball.t' s₀ k)
  hi : s.mem.readW (argAddr s₀ 2) 32 = BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Sample.Ball.G s₀ / 2 ^ (VG.Proof.MlDsa.X86.Sample.Ball.t' s₀ k + 32))
  ebx : s.gpr .ebx = BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Sample.Ball.G s₀ / 2 ^ VG.Proof.MlDsa.X86.Sample.Ball.t' s₀ k)
  lt : (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ k).2 < 256
  le : VG.Proof.MlDsa.X86.Sample.Ball.j' s₀ k ≤ (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ k).2

/-! ## Addresses -/

theorem quad_add (x p : BitVec 32) (m : Nat) (hx : x = BitVec.ofNat 32 m) :
    x + x + (x + x) + p = p + BitVec.ofNat 32 (4 * m) := by
  rw [hx, ofNat_add_ofNat, ofNat_add_ofNat, BitVec.add_comm]
  congr 2; omega

theorem coef_ea {s₀ : State} (hp : VG.Proof.MlDsa.X86.Sample.Ball.QPre s₀) {i : Nat} (hi : i < 256) :
    (L.aP s₀ + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0).setWidth 64 = coeffAddr (L.aA s₀) i := by
  have ha := hp.1.a_fit
  rw [ea_add (by simp only [VG.Proof.MlDsa.X86.Sample.Ball.L] at ha ⊢; omega)]; rfl

theorem coef_in {s₀ s : State} (hp : VG.Proof.MlDsa.X86.Sample.Ball.QPre s₀) (h : Base VG.Proof.MlDsa.X86.Sample.Ball.L s₀ s) {i : Nat} (hi : i < 256) :
    InRegions (s.rd ++ s.wr) (coeffAddr (L.aA s₀) i) 4 :=
  let ⟨r, hr, hc⟩ := hp.1.inA h.wr hi; ⟨r, List.mem_append_right _ hr, hc⟩

theorem coef_arg_sep {s₀ : State} (hp : VG.Proof.MlDsa.X86.Sample.Ball.QPre s₀) {i a : Nat} (hi : i < 256) (ha : a < 5) :
    Mem.Sep (argAddr s₀ a) 4 (coeffAddr (L.aA s₀) i) 4 :=
  fun x h₁ h₂ => hp.1.a_g x ((coeff_contains _ hi).byte h₂) ((VG.Proof.MlKem.X86.arg_contains (n := 5) ha hp.1.sp').byte h₁)

/-! ## Moving `c[j]` to `c[i]` -/

theorem move_ok {s₀ : State} (hp : VG.Proof.MlDsa.X86.Sample.Ball.QPre s₀) {k : Nat} {s : State} (h : VG.Proof.MlDsa.X86.Sample.Ball.BI s₀ k (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ k) s)
    (hlt : (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ k).2 < 256) (hax : s.gpr .eax = BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Sample.Ball.j' s₀ k)) (hle : VG.Proof.MlDsa.X86.Sample.Ball.j' s₀ k ≤ (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ k).2) :
    WP isa (.block bMove) s fun s' => VG.Proof.MlDsa.X86.Sample.Ball.M1 s₀ k s' ∧ VG.X86.eval .e s' = some (!(VG.Proof.MlDsa.X86.Sample.Ball.G s₀).testBit (VG.Proof.MlDsa.X86.Sample.Ball.t' s₀ k)) := by
  have hj : VG.Proof.MlDsa.X86.Sample.Ball.j' s₀ k < 256 := by omega
  have eaj := VG.Proof.MlDsa.X86.Sample.Ball.coef_ea hp hj
  have eai := VG.Proof.MlDsa.X86.Sample.Ball.coef_ea hp hlt
  have inj := VG.Proof.MlDsa.X86.Sample.Ball.coef_in hp h.toBase hj
  have ini := hp.1.inA h.wr hlt
  have a₁ := h.argEa (i := 1)
  have i₁ := h.argIn hp.1 (i := 1) (by decide)
  simp only [Nat.mul_one, Nat.reduceAdd] at a₁
  have hvj : s.mem.readW (coeffAddr (L.aA s₀) (VG.Proof.MlDsa.X86.Sample.Ball.j' s₀ k)) 32 = zw (ofInt (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ k).1[VG.Proof.MlDsa.X86.Sample.Ball.j' s₀ k]!) := h.poly _ hj
  have rlo : ∀ W : BitVec 32, (s.mem.writeW (coeffAddr (L.aA s₀) (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ k).2) W).readW (argAddr s₀ 1) 32 =
      BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Sample.Ball.G s₀ / 2 ^ VG.Proof.MlDsa.X86.Sample.Ball.t' s₀ k) := fun W => by
    rw [Mem.readW_writeW_sep (VG.Proof.MlDsa.X86.Sample.Ball.coef_arg_sep hp hlt (by decide)) (by decide)]; exact h.lo
  have fa : ∀ W : BitVec 32, Frame [L.aR s₀] s.mem (s.mem.writeW (coeffAddr (L.aA s₀) (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ k).2) W) :=
    fun W => (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (coeff_contains _ hlt)
  have fin : ∀ s' : State, s'.gpr .esp = s.gpr .esp → s'.gpr .esi = s.gpr .esi → s'.gpr .ecx = s.gpr .ecx →
      s'.gpr .ebp = s.gpr .ebp → s'.gpr .edi = s.gpr .edi →
      s'.gpr .eax = L.aP s₀ + BitVec.ofNat 32 (4 * VG.Proof.MlDsa.X86.Sample.Ball.j' s₀ k) →
      s'.gpr .ebx = BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Sample.Ball.G s₀ / 2 ^ VG.Proof.MlDsa.X86.Sample.Ball.t' s₀ k) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = s.mem.writeW (coeffAddr (L.aA s₀) (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ k).2) (zw (ofInt (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ k).1[VG.Proof.MlDsa.X86.Sample.Ball.j' s₀ k]!)) →
      VG.Proof.MlDsa.X86.Sample.Ball.M1 s₀ k s' := by
    intro s' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
    refine ⟨⟨by rw [e1, h.esp], by rw [e8, h.rd], by rw [e9, h.wr], ?_⟩, fun p hp' => ?_, by rw [e2, h.esi],
      by rw [e3, h.ecx], by rw [e4, h.ebp], by rw [e5, h.edi], e6, fun jj hjj => ?_, by rw [e10]; exact rlo _,
      ?_, e7, hlt, hle⟩
    · rw [e10]; exact h.frame.writeW (r := L.aR s₀) (by simp) _ (coeff_contains _ hlt)
    · rw [e10]
      refine ((fa _) _ fun r hr hc => ?_).trans (h.out p hp')
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.1.a_s _ hc ((hp.1.sub_s (o := 840 + p) (n := 1) (by omega)) _ (Region.contains_self _ _))
    · rw [e10, coeffAt_writeW _ _ hjj hlt, VG.Proof.MlDsa.X86.Sample.Ball.P1, ipoly_set!_get _ _ (by simp only [VG.Spec.MlDsa.n]; omega)]
      by_cases e : (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ k).2 = jj
      · rw [ifT e, ifT e]
      · rw [ifF e, ifF e]; exact h.poly jj hjj
    · rw [e10, Mem.readW_writeW_sep (VG.Proof.MlDsa.X86.Sample.Ball.coef_arg_sep hp hlt (by decide)) (by decide)]; exact h.hi
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reduceAdd, Nat.reduceMul, Nat.reducePow, bMove, argOp, at_, runBlock_cons, runStep_some, runBlock_nil, exec,
    execAlu, readSrc, State.ea, State.load32, State.store32, State.setReg, arithFlags, State.setFlags,
    Option.map_some, Option.bind_some, hax, h.ebp, h.edi, VG.Proof.MlDsa.X86.Sample.Ball.quad_add _ _ _ rfl, eaj, eai, inj, ini, hvj, a₁, i₁,
    rlo, Option.some.injEq, exists_eq_left']
  refine ⟨fin _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) rfl rfl rfl, ?_⟩
  simp only [VG.X86.eval, signBit_eq]

/-! ## Two runs agree -/

namespace QPub
variable {s₀ s₀' : State} (hq : VG.Proof.MlDsa.X86.Sample.Ball.QPub s₀ s₀')
include hq

theorem eτ : VG.Proof.MlDsa.X86.Sample.Ball.τ s₀ = VG.Proof.MlDsa.X86.Sample.Ball.τ s₀' := by rw [VG.Proof.MlDsa.X86.Sample.Ball.τ, VG.Proof.MlDsa.X86.Sample.Ball.τ, hq.1.2 2 (by decide)]
theorem eS (k : Nat) : VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ k = VG.Proof.MlDsa.X86.Sample.Ball.S' s₀' k := by simp only [VG.Proof.MlDsa.X86.Sample.Ball.S', hq.2, hq.eτ]
theorem ej (k : Nat) : VG.Proof.MlDsa.X86.Sample.Ball.j' s₀ k = VG.Proof.MlDsa.X86.Sample.Ball.j' s₀' k := by simp only [VG.Proof.MlDsa.X86.Sample.Ball.j', hq.2]
theorem et (k : Nat) : VG.Proof.MlDsa.X86.Sample.Ball.t' s₀ k = VG.Proof.MlDsa.X86.Sample.Ball.t' s₀' k := by simp only [VG.Proof.MlDsa.X86.Sample.Ball.t', hq.eS k, hq.eτ]
theorem eG : VG.Proof.MlDsa.X86.Sample.Ball.G s₀ = VG.Proof.MlDsa.X86.Sample.Ball.G s₀' := by simp only [VG.Proof.MlDsa.X86.Sample.Ball.G, hq.2]

end QPub

/-! ## The sign -/

theorem sign_piece (k : Nat) :
    Piece VG.Proof.MlDsa.X86.Sample.Ball.QPre VG.Proof.MlDsa.X86.Sample.Ball.QPub (fun s₀ s => VG.Proof.MlDsa.X86.Sample.Ball.M1 s₀ k s ∧ VG.X86.eval .e s = some (!(VG.Proof.MlDsa.X86.Sample.Ball.G s₀).testBit (VG.Proof.MlDsa.X86.Sample.Ball.t' s₀ k)))
      (fun s₀ s => VG.Proof.MlDsa.X86.Sample.Ball.M1 s₀ k s ∧ s.gpr .edx = zw (ofInt (VG.Proof.MlDsa.X86.Sample.Ball.sg s₀ k)))
      (.ite .e (.block [.mov .edx (.imm 1)]) (.block [.mov .edx (.imm (qImm - 1))])) := by
  refine Piece.ite (fun s₀ => !(VG.Proof.MlDsa.X86.Sample.Ball.G s₀).testBit (VG.Proof.MlDsa.X86.Sample.Ball.t' s₀ k)) (fun _ _ _ h => h.2)
    (fun s₀ s₀' _ _ hq => by rw [hq.eG, hq.et]) ?_ ?_
  · refine Piece.taint [] (fun s₀ s _ ⟨⟨h, _⟩, hb⟩ => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
      (by taint_decide)
    have hs : VG.Proof.MlDsa.X86.Sample.Ball.sg s₀ k = 1 := by
      rw [VG.Proof.MlDsa.X86.Sample.Ball.sg_eq]; simp only [Bool.not_eq_true'] at hb; rw [hb]; rfl
    apply WP.of_runBlock
    simp only [↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      State.setReg, Option.map_some, Option.some.injEq, exists_eq_left']
    refine ⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, h.out, by simp [h.esi], by simp [h.ecx], by simp [h.ebp],
      by simp [h.edi], by simp [h.eax], h.poly, h.lo, h.hi, by simp [h.ebx], h.lt, h.le⟩, ?_⟩
    rw [hs]; simp; rfl
  · refine Piece.taint [] (fun s₀ s _ ⟨⟨h, _⟩, hb⟩ => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
      (by taint_decide)
    have hs : VG.Proof.MlDsa.X86.Sample.Ball.sg s₀ k = -1 := by
      rw [VG.Proof.MlDsa.X86.Sample.Ball.sg_eq]; simp only [Bool.not_eq_false'] at hb; rw [hb]; rfl
    apply WP.of_runBlock
    simp only [↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      State.setReg, Option.map_some, Option.some.injEq, exists_eq_left']
    refine ⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, h.out, by simp [h.esi], by simp [h.ecx], by simp [h.ebp],
      by simp [h.edi], by simp [h.eax], h.poly, h.lo, h.hi, by simp [h.ebx], h.lt, h.le⟩, ?_⟩
    rw [hs]; simp; rfl

/-! ## `c[j] ← ±1`, and the sign bits shifted -/

theorem st_set {s₀ : State} {k : Nat} (hk : k < 264) (hlt : (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ k).2 < 256) (hle : VG.Proof.MlDsa.X86.Sample.Ball.j' s₀ k ≤ (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ k).2) :
    VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ (k + 1) = ((VG.Proof.MlDsa.X86.Sample.Ball.P1 s₀ k).set! (VG.Proof.MlDsa.X86.Sample.Ball.j' s₀ k) (VG.Proof.MlDsa.X86.Sample.Ball.sg s₀ k), (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ k).2 + 1) := by
  rw [VG.Proof.MlDsa.X86.Sample.Ball.S', VG.Proof.MlDsa.X86.Sample.Ball.st_succ _ _ hk, bStep, ifT (show (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ k).2 < VG.Spec.MlDsa.n by simp only [VG.Spec.MlDsa.n]; omega), ifF (Nat.not_lt.mpr hle)]

theorem shift_ok {s₀ : State} (hp : VG.Proof.MlDsa.X86.Sample.Ball.QPre s₀) {k : Nat} (hk : k < 264) {s : State} (h : VG.Proof.MlDsa.X86.Sample.Ball.M1 s₀ k s)
    (hdx : s.gpr .edx = zw (ofInt (VG.Proof.MlDsa.X86.Sample.Ball.sg s₀ k))) :
    WP isa (.block bShift) s fun s' => VG.Proof.MlDsa.X86.Sample.Ball.BI s₀ k (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ (k + 1)) s' := by
  have hj : VG.Proof.MlDsa.X86.Sample.Ball.j' s₀ k < 256 := by have := h.lt; have := h.le; omega
  have eaj := VG.Proof.MlDsa.X86.Sample.Ball.coef_ea hp hj
  have inj := hp.1.inA h.wr hj
  have a₁ := h.argEa (i := 1)
  have a₂ := h.argEa (i := 2)
  have i₂ := h.argIn hp.1 (i := 2) (by decide)
  have w₁ := h.argInW hp.1 (i := 1) (by decide)
  have w₂ := h.argInW hp.1 (i := 2) (by decide)
  simp only [Nat.mul_one, Nat.reduceMul, Nat.reduceAdd] at a₁ a₂
  have rhi : ∀ W : BitVec 32, (s.mem.writeW (coeffAddr (L.aA s₀) (VG.Proof.MlDsa.X86.Sample.Ball.j' s₀ k)) W).readW (argAddr s₀ 2) 32 =
      BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Sample.Ball.G s₀ / 2 ^ (VG.Proof.MlDsa.X86.Sample.Ball.t' s₀ k + 32)) := fun W => by
    rw [Mem.readW_writeW_sep (VG.Proof.MlDsa.X86.Sample.Ball.coef_arg_sep hp hj (by decide)) (by decide)]; exact h.hi
  have ge : 256 - VG.Proof.MlDsa.X86.Sample.Ball.τ s₀ ≤ (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ k).2 := VG.Proof.MlDsa.X86.Sample.Ball.st_ge (L.Msg s₀) (VG.Proof.MlDsa.X86.Sample.Ball.τ s₀) k
  have hτ := hp.τ_le
  have et : (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ (k + 1)).2 + VG.Proof.MlDsa.X86.Sample.Ball.τ s₀ - 256 = VG.Proof.MlDsa.X86.Sample.Ball.t' s₀ k + 1 := by
    rw [VG.Proof.MlDsa.X86.Sample.Ball.st_set hk h.lt h.le]; simp only [VG.Proof.MlDsa.X86.Sample.Ball.t']; omega
  have fin : ∀ s' : State, s'.gpr .esp = s.gpr .esp → s'.gpr .esi = s.gpr .esi → s'.gpr .ecx = s.gpr .ecx →
      s'.gpr .ebp = s.gpr .ebp → s'.gpr .edi = s.gpr .edi + 1 → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = ((s.mem.writeW (coeffAddr (L.aA s₀) (VG.Proof.MlDsa.X86.Sample.Ball.j' s₀ k)) (zw (ofInt (VG.Proof.MlDsa.X86.Sample.Ball.sg s₀ k)))).writeW (argAddr s₀ 1)
        (BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Sample.Ball.G s₀ / 2 ^ (VG.Proof.MlDsa.X86.Sample.Ball.t' s₀ k + 1)))).writeW (argAddr s₀ 2)
        (BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Sample.Ball.G s₀ / 2 ^ (VG.Proof.MlDsa.X86.Sample.Ball.t' s₀ k + 1 + 32))) →
      VG.Proof.MlDsa.X86.Sample.Ball.BI s₀ k (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ (k + 1)) s' := by
    intro s' e1 e2 e3 e4 e5 e6 e7 e8
    have fg : Frame [L.gR s₀] (s.mem.writeW (coeffAddr (L.aA s₀) (VG.Proof.MlDsa.X86.Sample.Ball.j' s₀ k)) (zw (ofInt (VG.Proof.MlDsa.X86.Sample.Ball.sg s₀ k)))) s'.mem := by
      rw [e8]
      exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (VG.Proof.MlKem.X86.arg_contains (n := 5) (by decide) hp.1.sp')).writeW
        (List.mem_singleton_self _) _ (VG.Proof.MlKem.X86.arg_contains (n := 5) (by decide) hp.1.sp')
    have fa : Frame [L.aR s₀] s.mem (s.mem.writeW (coeffAddr (L.aA s₀) (VG.Proof.MlDsa.X86.Sample.Ball.j' s₀ k)) (zw (ofInt (VG.Proof.MlDsa.X86.Sample.Ball.sg s₀ k)))) :=
      (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (coeff_contains _ hj)
    have fw : Frame (L.W s₀) (P0 s₀).mem s'.mem :=
      (h.frame.trans (fa.mono (by simp))).trans (fg.mono (by simp))
    refine ⟨⟨by rw [e1, h.esp], by rw [e6, h.rd], by rw [e7, h.wr], fw⟩, fun p hp' => ?_, by rw [e2, h.esi],
      by rw [e3, h.ecx], by rw [e4, h.ebp], ?_, fun jj hjj => ?_, ?_, ?_⟩
    · rw [fg.bytes (R := ⟨L.sA s₀, 2048⟩) (by simp only [List.mem_singleton, forall_eq]; exact hp.1.s_g)
        (show (2048 : Nat) ≤ 2 ^ 64 by decide) (show 840 + p < 2048 by omega)]
      refine (fa _ fun r hr hc => ?_).trans (h.out p hp')
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.1.a_s _ hc ((hp.1.sub_s (o := 840 + p) (n := 1) (by omega)) _ (Region.contains_self _ _))
    · rw [e5, h.edi, VG.Proof.MlDsa.X86.Sample.Ball.st_set hk h.lt h.le, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ofNat_add_ofNat]
    · rw [coeffAt_eq, fg.readW (coeff_contains _ hjj) (by simp only [List.mem_singleton, forall_eq]; exact hp.1.a_g)
        (by decide), ← coeffAt_eq, coeffAt_writeW _ _ hjj hj, VG.Proof.MlDsa.X86.Sample.Ball.st_set hk h.lt h.le,
        ipoly_set!_get _ _ (by simp only [VG.Spec.MlDsa.n]; omega)]
      by_cases e : VG.Proof.MlDsa.X86.Sample.Ball.j' s₀ k = jj
      · rw [ifT e, ifT e]
      · rw [ifF e, ifF e]; exact h.poly jj hjj
    · rw [e8, Mem.readW_writeW_sep (VG.Proof.MlDsa.X86.Sample.Ball.slots_sep hp) (by decide), Mem.readW_writeW_self32, et]
    · rw [e8, Mem.readW_writeW_self32, et]
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reducePow, and_self, bShift, argOp, at_, runBlock_cons, runStep_some, runBlock_nil, exec,
    execAlu, execShift, readSrc, State.ea, State.load32, State.store32, State.setReg, arithFlags, State.setFlags,
    Option.map_some, Option.bind_some, h.eax, h.ebx, hdx, eaj, inj, a₁, a₂, i₂, w₁, w₂, rhi, signs_shift,
    signs_shift_hi (VG.Proof.MlDsa.X86.Sample.Ball.G_lt s₀), Option.some.injEq, exists_eq_left']
  exact fin _ (by simp) (by simp) (by simp) (by simp) (by simp) rfl rfl rfl

/-! ## An iteration -/

theorem st_skip {s₀ : State} {k : Nat} (hk : k < 264) (hgt : (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ k).2 < VG.Proof.MlDsa.X86.Sample.Ball.j' s₀ k) :
    VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ (k + 1) = VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ k := by
  rw [VG.Proof.MlDsa.X86.Sample.Ball.S', VG.Proof.MlDsa.X86.Sample.Ball.st_succ _ _ hk, bStep]
  by_cases hl : (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ k).2 < VG.Spec.MlDsa.n
  · rw [ifT hl, ifT hgt]
  · rw [ifF hl]

theorem st_full {s₀ : State} {k : Nat} (hk : k < 264) (hf : ¬ (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ k).2 < 256) : VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ (k + 1) = VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ k := by
  rw [VG.Proof.MlDsa.X86.Sample.Ball.S', VG.Proof.MlDsa.X86.Sample.Ball.st_succ _ _ hk, bStep, ifF (show ¬ (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ k).2 < VG.Spec.MlDsa.n by simp only [VG.Spec.MlDsa.n]; omega)]

theorem set_piece (k : Nat) (hk : k < 264) :
    Piece VG.Proof.MlDsa.X86.Sample.Ball.QPre VG.Proof.MlDsa.X86.Sample.Ball.QPub (fun s₀ s => ((VG.Proof.MlDsa.X86.Sample.Ball.BI s₀ k (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ k) s ∧ (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ k).2 < 256 ∧
        s.gpr .eax = BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Sample.Ball.j' s₀ k)) ∧ VG.X86.eval .b s = some (decide ((VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ k).2 < VG.Proof.MlDsa.X86.Sample.Ball.j' s₀ k))) ∧
        decide ((VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ k).2 < VG.Proof.MlDsa.X86.Sample.Ball.j' s₀ k) = false)
      (fun s₀ s => VG.Proof.MlDsa.X86.Sample.Ball.BI s₀ k (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ (k + 1)) s) bSet := by
  refine Piece.seq (Piece.taint [.eax, .edi, .ebp, .esp]
    (fun s₀ s hp ⟨⟨⟨h, hlt, hax⟩, _⟩, hb⟩ => VG.Proof.MlDsa.X86.Sample.Ball.move_ok hp h hlt hax (by simp at hb; omega))
    (fun s₀ s₀' s s' _ _ hq ⟨⟨⟨h, _, hax⟩, _⟩, _⟩ ⟨⟨⟨h', _, hax'⟩, _⟩, _⟩ r hr => ?_) (by taint_decide))
    (Piece.seq (VG.Proof.MlDsa.X86.Sample.Ball.sign_piece k) (Piece.taint [.eax, .edi, .esp] (fun s₀ s hp ⟨h, hdx⟩ => VG.Proof.MlDsa.X86.Sample.Ball.shift_ok hp hk h hdx)
      (fun s₀ s₀' s s' _ _ hq ⟨h, _⟩ ⟨h', _⟩ r hr => ?_) (by taint_decide)))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [hax, hax', hq.ej]
    · rw [h.edi, h'.edi, hq.eS]
    · rw [h.ebp, h'.ebp, hq.1.aP VG.Proof.MlDsa.X86.Sample.Ball.hL]
    · rw [h.esp, h'.esp, hq.1.e1]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h.eax, h'.eax, hq.ej, hq.1.aP VG.Proof.MlDsa.X86.Sample.Ball.hL]
    · rw [h.edi, h'.edi, hq.eS]
    · rw [h.esp, h'.esp, hq.1.e1]

theorem try_piece (k : Nat) (hk : k < 264) :
    Piece VG.Proof.MlDsa.X86.Sample.Ball.QPre VG.Proof.MlDsa.X86.Sample.Ball.QPub (fun s₀ s => VG.Proof.MlDsa.X86.Sample.Ball.BI s₀ k (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ k) s ∧ (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ k).2 < 256)
      (fun s₀ s => VG.Proof.MlDsa.X86.Sample.Ball.BI s₀ k (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ (k + 1)) s) bTry := by
  refine Piece.seq (B := fun s₀ s => (VG.Proof.MlDsa.X86.Sample.Ball.BI s₀ k (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ k) s ∧ (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ k).2 < 256 ∧
      s.gpr .eax = BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Sample.Ball.j' s₀ k)) ∧ VG.X86.eval .b s = some (decide ((VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ k).2 < VG.Proof.MlDsa.X86.Sample.Ball.j' s₀ k))) ?_
    (Piece.ite (fun s₀ => decide ((VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ k).2 < VG.Proof.MlDsa.X86.Sample.Ball.j' s₀ k)) (fun _ _ _ h => h.2)
      (fun s₀ s₀' _ _ hq => by rw [hq.eS, hq.ej]) ?_ (VG.Proof.MlDsa.X86.Sample.Ball.set_piece k hk))
  · refine Piece.taint [.esi] (fun s₀ s hp ⟨h, hlt⟩ => ?_) (fun s₀ s₀' s s' _ _ hq ⟨h, _⟩ ⟨h', _⟩ r hr => ?_)
      (by taint_decide)
    · have hs := hp.1.s_fit
      have e0 : (L.sP s₀ + BitVec.ofNat 32 (848 + k) + BitVec.ofNat 32 0).setWidth 64 =
          L.sA s₀ + BitVec.ofNat 64 (840 + (8 + k)) := by
        rw [ea_add (by simp only [VG.Proof.MlDsa.X86.Sample.Ball.L] at hs ⊢; omega)]; congr 2; omega
      have i0 := hp.1.inS' h.wr (o := 840 + (8 + k)) (n := 1) (by omega)
      have v0 := h.out (8 + k) (by omega)
      have hle : (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ k).2 ≤ 256 := VG.Proof.MlDsa.X86.Sample.Ball.st_le (L.Msg s₀) (VG.Proof.MlDsa.X86.Sample.Ball.τ s₀) k
      apply WP.of_runBlock
      simp only [reduceCtorEq, ↓reduceIte, at_, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
        readSrc, State.ea, State.load8, State.setReg, arithFlags, State.setFlags, Option.map_some,
        Option.bind_some, h.esi, e0, i0, v0, Option.some.injEq, exists_eq_left']
      refine ⟨⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, h.out, by simp [h.esi], by simp [h.ecx], by simp [h.ebp],
        by simp [h.edi], h.poly, h.lo, h.hi⟩, hlt, ?_⟩, ?_⟩
      · exact eq_ofNat_of_toNat (toNat_byte32 _)
      · simp only [VG.X86.eval, h.edi, toNat_byte32, toNat_ofNat32 (show (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ k).2 < 2 ^ 32 by omega)]
    · simp only [List.mem_singleton] at hr
      subst hr
      rw [h.esi, h'.esi, hq.1.sP VG.Proof.MlDsa.X86.Sample.Ball.hL]
  · exact VG.Proof.MlDsa.X86.Sample.RejNtt.nil_piece fun s₀ s _ ⟨⟨⟨h, _⟩, _⟩, hb⟩ => VG.Proof.MlDsa.X86.Sample.Ball.st_skip hk (of_decide_eq_true hb) ▸ h

theorem body_piece (k : Nat) (hk : k < 264) :
    Piece VG.Proof.MlDsa.X86.Sample.Ball.QPre VG.Proof.MlDsa.X86.Sample.Ball.QPub (fun s₀ s => VG.Proof.MlDsa.X86.Sample.Ball.BI s₀ k (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ k) s)
      (fun s₀ s => VG.Proof.MlDsa.X86.Sample.Ball.BI s₀ (k + 1) (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ (k + 1)) s ∧ VG.X86.eval .ne s = some (decide (k + 1 < 264))) bBody := by
  refine Piece.seq (B := fun s₀ s => VG.Proof.MlDsa.X86.Sample.Ball.BI s₀ k (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ k) s ∧ VG.X86.eval .b s = some (decide ((VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ k).2 < 256)))
    (Piece.taint [] (fun s₀ s _ h => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp)) (by taint_decide))
    (Piece.seq (B := fun s₀ s => VG.Proof.MlDsa.X86.Sample.Ball.BI s₀ k (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ (k + 1)) s)
      (Piece.ite (fun s₀ => decide ((VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ k).2 < 256)) (fun _ _ _ h => h.2)
        (fun s₀ s₀' _ _ hq => by rw [hq.eS])
        ((VG.Proof.MlDsa.X86.Sample.Ball.try_piece k hk).mono (fun _ _ _ ⟨⟨h, _⟩, hb⟩ => ⟨h, of_decide_eq_true hb⟩) fun _ _ _ h => h)
        (VG.Proof.MlDsa.X86.Sample.RejNtt.nil_piece fun s₀ s _ ⟨⟨h, _⟩, hb⟩ => VG.Proof.MlDsa.X86.Sample.Ball.st_full hk (of_decide_eq_false hb) ▸ h))
      (Piece.taint [] (fun s₀ s _ h => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp)) (by taint_decide)))
  · have hle : (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ k).2 ≤ 256 := VG.Proof.MlDsa.X86.Sample.Ball.st_le (L.Msg s₀) (VG.Proof.MlDsa.X86.Sample.Ball.τ s₀) k
    have h256 : (256 : BitVec 32).toNat = 256 := rfl
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags,
      Option.bind_some, Option.some.injEq, exists_eq_left']
    refine ⟨⟨⟨h.esp, h.rd, h.wr, h.frame⟩, h.out, h.esi, h.ecx, h.ebp, h.edi, h.poly, h.lo, h.hi⟩, ?_⟩
    simp only [VG.X86.eval, h.edi, h256, toNat_ofNat32 (show (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ k).2 < 2 ^ 32 by omega)]
  · apply WP.of_runBlock
    simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
      State.setReg, arithFlags, State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left']
    refine ⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, h.out, ?_, ?_, by simp [h.ebp], by simp [h.edi], h.poly,
      h.lo, h.hi⟩, ?_⟩
    · simp only [ite_true, h.esi]
      rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, add_ofNat_add]; congr 2
    · simp only [ite_true, h.ecx]
      exact cnt_next hk
    · simp only [VG.X86.eval, h.ecx]
      exact cnt_ne hk (by omega)

theorem loop_piece : Piece VG.Proof.MlDsa.X86.Sample.Ball.QPre VG.Proof.MlDsa.X86.Sample.Ball.QPub (fun s₀ s => VG.Proof.MlDsa.X86.Sample.Ball.BI s₀ 0 (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ 0) s) (fun s₀ s => VG.Proof.MlDsa.X86.Sample.Ball.BI s₀ 264 (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ 264) s)
    (.loop bBody .ne) :=
  Piece.loop (fun k s₀ s => VG.Proof.MlDsa.X86.Sample.Ball.BI s₀ k (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ k) s) (by decide) fun k hk => VG.Proof.MlDsa.X86.Sample.Ball.body_piece k hk

end VG.Proof.MlDsa.X86.Sample.Ball

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Sample.BallTop`. -/
section

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

namespace VG.Proof.MlDsa.X86.Sample.Ball

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86
open VG.Proof.MlDsa.X86.Sample
open VG.Proof.MlDsa.Sample
open VG.Impl.MlDsa.X86.Sample (bZero bSetup bBody retJ sponge argOp)
open VG.Spec.MlDsa (Zq q H n ofInt coeffAt IPoly)

/-- The end: `i >> 8` in `eax`. -/
structure Fin (s₀ s : State) : Prop extends VG.Proof.MlDsa.X86.Sample.Ball.BI s₀ 264 (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ 264) s where
  eax : s.gpr .eax = BitVec.ofNat 32 ((VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ 264).2 / 256)

theorem fin_piece : Piece VG.Proof.MlDsa.X86.Sample.Ball.QPre VG.Proof.MlDsa.X86.Sample.Ball.QPub (fun s₀ s => VG.Proof.MlDsa.X86.Sample.Ball.BI s₀ 264 (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ 264) s) VG.Proof.MlDsa.X86.Sample.Ball.Fin (.block (retJ .edi)) := by
  refine Piece.taint [] (fun s₀ s _ h => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
    (by taint_decide)
  have hl : (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ 264).2 ≤ 256 := VG.Proof.MlDsa.X86.Sample.Ball.st_le _ _ _
  refine wp_movr (wp_shr (by decide) (by decide) fun s' o e => WP.block_nil_iff.mpr ?_)
  have g : ∀ r, r ≠ .eax → s'.gpr r = s.gpr r := fun r hr => by
    rw [o.gpr r (by simp [hr])]; simp [State.setReg, hr]
  refine ⟨⟨⟨by rw [g _ (by decide), h.esp], by rw [o.rd]; exact h.rd, by rw [o.wr]; exact h.wr,
    by rw [o.mem]; exact h.frame⟩, by rw [o.mem]; exact h.out, by rw [g _ (by decide), h.esi],
    by rw [g _ (by decide), h.ecx], by rw [g _ (by decide), h.ebp], by rw [g _ (by decide), h.edi],
    by rw [o.mem]; exact h.poly, by rw [o.mem]; exact h.lo, by rw [o.mem]; exact h.hi⟩, ?_⟩
  rw [e]
  simp only [State.setReg, ite_true, h.edi]
  exact eq_ofNat_of_toNat (by rw [toNat_shr, toNat_ofNat32 (show (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ 264).2 < 2 ^ 32 by omega)])

theorem main_piece : Piece VG.Proof.MlDsa.X86.Sample.Ball.QPre VG.Proof.MlDsa.X86.Sample.Ball.QPub (fun s₀ s => s = P0 s₀) VG.Proof.MlDsa.X86.Sample.Ball.Fin
    (.seq (sponge 4 136 (.mem (argOp 1)) 272) <|
      .seq bZero <| .seq (.block bSetup) <| .seq (.loop bBody .ne) (.block (retJ .edi))) :=
  Piece.seq ((sponge_piece VG.Proof.MlDsa.X86.Sample.Ball.hL).pre_mono (fun _ h => h.1) fun _ _ _ _ h => h.1) <|
    Piece.seq VG.Proof.MlDsa.X86.Sample.Ball.zero_piece <| Piece.seq VG.Proof.MlDsa.X86.Sample.Ball.setup_piece <| Piece.seq VG.Proof.MlDsa.X86.Sample.Ball.loop_piece VG.Proof.MlDsa.X86.Sample.Ball.fin_piece

theorem piece : Piece VG.Proof.MlDsa.X86.Sample.Ball.QPre VG.Proof.MlDsa.X86.Sample.Ball.QPub (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (VG.Proof.MlDsa.X86.Sample.Ball.Fin s₀) s₀ s')
    Impl.MlDsa.X86.Sample.sampleInBall :=
  Piece.leaf L.W (NoSp.of_all (by decide +kernel))
    (fun _ hp => ⟨by have := hp.1.sp; omega, by have := hp.1.sp'; omega⟩)
    (fun _ hp => hp.1.hW) (fun _ _ _ _ hq => hq.1.1)
    (main_piece.mono (fun _ _ _ h => h) fun _ _ _ h => ⟨⟨h.frame, h.esp, h.rd, h.wr⟩, h⟩)

theorem QPre.of {s₀ : State} (h : (Spec.MlDsa.sampleInBallContract X86.abi 56).pre s₀) : VG.Proof.MlDsa.X86.Sample.Ball.QPre s₀ := by
  sig_pre [Spec.MlDsa.sampleInBallContract, Spec.MlDsa.sampleInBallSig, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22⟩ := h
  have hl : (arg s₀ 1).toNat < 136 := by
    simp only [Spec.MlDsa.ballParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h22
    omega
  exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, hl⟩, h22⟩

theorem S'_all (s₀ : State) : VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ 264 = ballFold (VG.Proof.MlDsa.X86.Sample.Ball.τ s₀) (H (L.Msg s₀) 272) := by
  simp only [VG.Proof.MlDsa.X86.Sample.Ball.S', VG.Proof.MlDsa.X86.Sample.Ball.st, ballFold]
  rw [List.take_of_length_le (by rw [List.length_drop, VG.Proof.MlDsa.X86.Sample.Ball.Xb_length])]

theorem toRq_getElem! (v : IPoly) {i : Nat} (hi : i < VG.Spec.MlDsa.n) : (Spec.MlDsa.toRq v)[i]! = ofInt v[i]! := by
  rw [getElem!_pos _ i hi, getElem!_pos _ i hi]
  simp only [Spec.MlDsa.toRq, Vector.getElem_map]

/-- Memory with the arguments `0`, `32`, `39`, `0x100` and `0x1000` at `0x5004`. -/
def satMem : Mem := fun a =>
  if a = 0x5008 then 32 else if a = 0x500c then 39 else if a = 0x5011 then 1 else if a = 0x5015 then 0x10 else 0

theorem verified :
    Verified X86.target Impl.MlDsa.X86.Sample.sampleInBall (Spec.MlDsa.sampleInBallContract X86.abi 56) := by
  refine Piece.verified ((piece.pre_mono (fun _ h => QPre.of h) fun s s' _ _ h => ?_).mono
    (fun _ _ _ h => h) fun s₀ s' _ hq => ?_) ?_
  · sig_pub [Spec.MlDsa.sampleInBallContract, Spec.MlDsa.sampleInBallSig, X86.abi, X86.argSlots, X86.argVal,
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
    sig_post [Spec.MlDsa.sampleInBallContract, Spec.MlDsa.sampleInBallSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]
    rw [setWidth_append32, hax, hfin.eax, hm]
    have hl : (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ 264).2 ≤ 256 := VG.Proof.MlDsa.X86.Sample.Ball.st_le _ _ _
    have hp : Spec.MlDsa.PolyIs s.mem (L.aA s₀) (Spec.MlDsa.toRq (VG.Proof.MlDsa.X86.Sample.Ball.S' s₀ 264).1) :=
      polyIs_of_coeffAt fun i hi => by rw [hfin.poly i (by simp only [VG.Spec.MlDsa.n] at hi; omega), VG.Proof.MlDsa.X86.Sample.Ball.toRq_getElem! _ hi]
    rw [VG.Proof.MlDsa.X86.Sample.Ball.S'_all] at hl hp
    rw [VG.Proof.MlDsa.X86.Sample.Ball.S'_all]
    by_cases e : (ballFold (VG.Proof.MlDsa.X86.Sample.Ball.τ s₀) (H (L.Msg s₀) 272)).2 = 256
    · rw [e]
      refine ⟨fun _ => hp.1, .inl ⟨rfl, { Spec.MlDsa.minBounds with ball := 272 }, ?_⟩⟩
      show (Spec.MlDsa.sampleInBall (VG.Proof.MlDsa.X86.Sample.Ball.τ s₀) 272 (L.Msg s₀)).map Spec.MlDsa.toRq =
        some (Spec.MlDsa.polyAt s.mem (L.aA s₀))
      rw [sampleInBall_some _ (by decide) e, hp.2]
      rfl
    · rw [Nat.div_eq_of_lt (by omega)]
      refine ⟨fun h => absurd (congrArg BitVec.toNat h) (by show ¬ (0 = 1); decide), .inr ⟨rfl, ?_⟩⟩
      show (Spec.MlDsa.sampleInBall (VG.Proof.MlDsa.X86.Sample.Ball.τ s₀) Spec.MlDsa.minBounds.ball (L.Msg s₀)).map Spec.MlDsa.toRq = none
      rw [sampleInBall_none _ (B := 272) (by decide) (by decide) e]
      rfl
  · let st := VG.Proof.MlKem.X86.satState VG.Proof.MlDsa.X86.Sample.Ball.satMem [⟨0, 32⟩] [⟨0x100, 1024⟩, ⟨0x1000, 2048⟩, ⟨0x5004, 20⟩]
    refine ⟨st, ?_⟩
    sig_sat_check [Spec.MlDsa.sampleInBallContract, Spec.MlDsa.sampleInBallSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]

end VG.Proof.MlDsa.X86.Sample.Ball

end
