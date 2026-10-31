module

public import VerifiedGarbage.Proof.MlDsa.AArch64.PreparedKey.Layout
import VerifiedGarbage.Proof.MlDsa.AArch64.PreparedKey.Secret
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Inst
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha3.AArch64.Sums

/-! # Key preparation does not branch on decoded coefficients -/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Impl.MlDsa.AArch64.PreparedKey

theorem sameIn_post {S : Nat} {B : List Reg} {x y x' y' : State}
    {Wx Wy : List Region} (hx : PostB S x x' Wx) (hy : PostB S y y' Wy)
    (hb : ∀ r ∈ B, r ∈ keptRegs) (h : SameIn B x y) : SameIn B x' y' := by
  exact ⟨fun r hr => by rw [hx.bs r (hb r hr), hy.bs r (hb r hr), h.1 r hr],
    by rw [hx.sp, hy.sp, h.2]⟩

theorem unpackT1_tr {S : Nat} {P : Impl.MlDsa.AArch64.KeyGen.Prims}
    (C : CalleeOk S P.unpackT1 (unpackT1Contract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {B : List Reg} (hB : LayIn B (rbs ++ wbs))
    {v f : Ptr} (hc : rwChk rbs wbs v 320 f 1024 = true)
    {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay S rbs wbs x ∧ Lay S rbs wbs y ∧ SameIn B x y) :
    RelCT isa Q (Impl.MlDsa.AArch64.KeyGen.unpackT1At P v f) fun _ _ => True := by
  obtain ⟨_, c2, c3⟩ := rw_parts hc
  have hbs : v.1 ∈ B ∧ f.1 ∈ B := ⟨ptr_bs hB c2, ptr_bs hB c3⟩
  refine callAt_tr C (KeyGen.t1_args hB c2 c3)
    (by simp only [List.map_cons, List.map_nil]; decide) fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, e⟩ := hQ x y hp
  refine ⟨_, _, KeyGen.t1_pre Lx hc h1, ?_, ?_, (rw_cov Lx hc).1,
    (rw_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hbs.1, e.pa hbs.2]
    exact KeyGen.t1_pre Ly hc h2
  · sig_pub [unpackT1Contract, unpackT1Sig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r0 h2, Args.r1 h2, Args.sp h1, Args.sp h2]
    simp only [Arg.val]
    exact ⟨e.2, e.pa hbs.1, e.pa hbs.2⟩
  · rw [e.pa hbs.1, e.pa hbs.2]
    exact (rw_cov Ly hc).1
  · rw [e.pa hbs.2]
    exact (rw_cov Ly hc).2

abbrev prepBases : List Reg := [.x25, .x26, .x28]

def PrepRel (S : Nat) (rbs wbs : List (Reg × Nat)) (x y : State) : Prop :=
  Lay S rbs wbs x ∧ Lay S rbs wbs y ∧ SameIn prepBases x y

theorem prepBases_kept : ∀ r ∈ prepBases, r ∈ keptRegs := by decide

theorem publicPoly_tr {rbs wbs : List (Reg × Nat)}
    (hB : LayIn prepBases (rbs ++ wbs)) {p : Params} {i : Nat}
    (hc : rwChk rbs wbs (.x25, 32 + 320 * i) 320
      (.x26, p.pkLen + 1024 * i) 1024 = true)
    (hi : ipChk rbs wbs (.x26, p.pkLen + 1024 * i) (.x28, 0) = true) :
    RelCT isa (PrepRel 16 rbs wbs) (publicPoly p i) fun _ _ => True := by
  unfold publicPoly transform
  refine RelCT.seq (R := fun (x y : State) => Lay 16 rbs wbs x ∧ Lay 16 rbs wbs y ∧
    SameIn prepBases x y ∧ Reduced x.mem (pa x (.x26, p.pkLen + 1024 * i)) ∧
    Reduced y.mem (pa y (.x26, p.pkLen + 1024 * i))) (RelCT.postDep
    (unpackT1_tr KeyGen.prims_ok.unpackT1 hB hc (fun _ _ h => h))
    (fun x y h => ⟨KeyGen.t1At_ok (by decide) KeyGen.prims_ok.unpackT1 h.1 hc,
      KeyGen.t1At_ok (by decide) KeyGen.prims_ok.unpackT1 h.2.1 hc⟩)
    (fun x y x' y' h hx hy => ?_)) ?_
  · exact ⟨h.1.post hx.1, h.2.1.post hy.1,
      sameIn_post hx.1 hy.1 prepBases_kept h.2.2,
      by rw [hx.1.pa (p := (.x26, p.pkLen + 1024 * i))
        (show Reg.x26 ∈ keptRegs by decide)]; exact hx.2.2.1,
      by rw [hy.1.pa (p := (.x26, p.pkLen + 1024 * i))
        (show Reg.x26 ∈ keptRegs by decide)]; exact hy.2.2.1⟩
  · exact ipAt_tr KeyGen.prims_ok.ntt hB hi
      (fun _ _ h => ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2, h.2.2.1⟩)

theorem unpackTransform_tr {rbs wbs : List (Reg × Nat)}
    (hB : LayIn prepBases (rbs ++ wbs)) {src offset len a b : Nat}
    (hc : rwChk rbs wbs (.x25, src) len (.x26, offset) 1024 = true)
    (hi : ipChk rbs wbs (.x26, offset) (.x28, 0) = true) (hb : BpOk a b len) :
    RelCT isa (PrepRel 16 rbs wbs) (.seq
      (callAt "vg_mldsa_bit_unpack" Impl.MlDsa.AArch64.Pack.bitUnpack
        [(.x0, .ptr (.x25, src)), (.x1, .imm len), (.x2, .imm a),
          (.x3, .imm b), (.x4, .ptr (.x26, offset))])
      (transform offset)) fun _ _ => True := by
  unfold transform
  refine RelCT.seq (R := fun (x y : State) => Lay 16 rbs wbs x ∧ Lay 16 rbs wbs y ∧
    SameIn prepBases x y ∧ Reduced x.mem (pa x (.x26, offset)) ∧
    Reduced y.mem (pa y (.x26, offset))) (RelCT.postDep
    (buAt_tr KeyGen.prims_ok.bitUnpack hB hc hb (fun _ _ h => h))
    (fun x y h => ⟨buAt_ok (by decide) KeyGen.prims_ok.bitUnpack h.1 hc hb,
      buAt_ok (by decide) KeyGen.prims_ok.bitUnpack h.2.1 hc hb⟩)
    (fun x y x' y' h hx hy => ?_)) ?_
  · exact ⟨h.1.post hx.1, h.2.1.post hy.1,
      sameIn_post hx.1 hy.1 prepBases_kept h.2.2,
      by rw [hx.1.pa (p := (.x26, offset))
        (show Reg.x26 ∈ keptRegs by decide)]; exact hx.2.2.1,
      by rw [hy.1.pa (p := (.x26, offset))
        (show Reg.x26 ∈ keptRegs by decide)]; exact hy.2.2.1⟩
  · exact ipAt_tr KeyGen.prims_ok.ntt hB hi
      (fun _ _ h => ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2, h.2.2.1⟩)

theorem prep_layout_ok (bytes count : Nat) :
    LayIn prepBases (input bytes ++ output bytes count) := by
  intro b hb
  simp only [input, output, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl <;> simp [prepBases, keptRegs]

theorem secretPoly_tr {p : Params}
    (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) {i : Nat}
    (hi : i < p.ℓ + 2 * p.k) :
    RelCT isa (PrepRel 16 (input p.skLen) (output p.skLen (p.ℓ + 2 * p.k)))
      (secretPoly p i) fun _ _ => True := by
  obtain ⟨src, len, a, b, he⟩ : ∃ src len a b, secretPiece p i = (src, len, a, b) := by
    rcases secretPiece p i with ⟨src, len, a, b⟩
    exact ⟨src, len, a, b, rfl⟩
  have hchecks := secret_checks hp hi
  rw [he] at hchecks
  unfold secretPoly
  rw [he]
  exact unpackTransform_tr (prep_layout_ok _ _) hchecks.1 hchecks.2.1 hchecks.2.2

theorem publicPoly_preserves {p : Params}
    (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) {i : Nat} (hi : i < p.k) :
    RelCT isa (PrepRel 16 (input p.pkLen) (output p.pkLen p.k))
      (publicPoly p i) (PrepRel 16 (input p.pkLen) (output p.pkLen p.k)) := by
  obtain ⟨hc, hi'⟩ := public_checks hp hi
  refine RelCT.postDep (publicPoly_tr (prep_layout_ok _ _) hc hi')
    (fun x y h => ⟨WP.mono (publicPoly_ok h.1 hc hi') (fun _ h => h.1),
      WP.mono (publicPoly_ok h.2.1 hc hi') (fun _ h => h.1)⟩)
    (fun x y x' y' h hx hy => ?_)
  exact ⟨h.1.post hx, h.2.1.post hy, sameIn_post hx hy prepBases_kept h.2.2⟩

theorem secretPoly_preserves {p : Params}
    (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) {i : Nat} (hi : i < p.ℓ + 2 * p.k) :
    RelCT isa (PrepRel 16 (input p.skLen) (output p.skLen (p.ℓ + 2 * p.k)))
      (secretPoly p i) (PrepRel 16 (input p.skLen) (output p.skLen (p.ℓ + 2 * p.k))) := by
  refine RelCT.postDep (secretPoly_tr hp hi)
    (fun x y h => ⟨WP.mono (secretPoly_ok hp h.1 rfl hi) (fun _ h => h.1),
      WP.mono (secretPoly_ok hp h.2.1 rfl hi) (fun _ h => h.1)⟩)
    (fun x y x' y' h hx hy => ?_)
  exact ⟨h.1.post hx, h.2.1.post hy, sameIn_post hx hy prepBases_kept h.2.2⟩

theorem copy_prepare_taint (bytes : Nat) :
    (taint.check (AArch64.Taint.ofRegs prepBases)
      (copy (.x26, 0) (.x25, 0) bytes) (copyHint bytes)).isSome = true := by
  dsimp only [copy, copyHint, Impl.MlDsa.AArch64.Call.lea,
    Impl.MlDsa.AArch64.Call.movV]
  (repeat' split) <;> rfl

theorem copy_preserves (bytes count : Nat)
    (hc : copyChk (input bytes) (output bytes count) (.x26, 0) (.x25, 0) bytes = true) :
    RelCT isa (PrepRel 16 (input bytes) (output bytes count))
      (copy (.x26, 0) (.x25, 0) bytes) (PrepRel 16 (input bytes) (output bytes count)) := by
  refine RelCT.postDep (taintRel prepBases (fun _ _ h => ⟨h.2.2.2, h.2.2.1⟩)
    (copy_prepare_taint bytes))
    (fun x y h => ⟨WP.mono (copy_ok h.1 hc) (fun _ h => h.1),
      WP.mono (copy_ok h.2.1 hc) (fun _ h => h.1)⟩)
    (fun x y x' y' h hx hy => ?_)
  exact ⟨h.1.post hx, h.2.1.post hy, sameIn_post hx hy prepBases_kept h.2.2⟩

theorem public_body_tr {p : Params}
    (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    RelCT isa (PrepRel 16 (input p.pkLen) (output p.pkLen p.k))
      (.seq (copy (.x26, 0) (.x25, 0) p.pkLen)
        (Impl.MlDsa.AArch64.Call.seqR (publicPoly p) 0 p.k))
      (PrepRel 16 (input p.pkLen) (output p.pkLen p.k)) := by
  exact RelCT.seq (copy_preserves _ _ (public_copy_check hp))
    (seqR_tr p.k 0 (fun _ _ hi => publicPoly_preserves hp (by omega)))

theorem secret_body_tr {p : Params}
    (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    RelCT isa (PrepRel 16 (input p.skLen) (output p.skLen (p.ℓ + 2 * p.k)))
      (.seq (copy (.x26, 0) (.x25, 0) p.skLen)
        (Impl.MlDsa.AArch64.Call.seqR (secretPoly p) 0 (p.ℓ + 2 * p.k)))
      (PrepRel 16 (input p.skLen) (output p.skLen (p.ℓ + 2 * p.k))) := by
  exact RelCT.seq (copy_preserves _ _ (secret_copy_check hp))
    (seqR_tr (p.ℓ + 2 * p.k) 0 (fun _ _ hi => secretPoly_preserves hp (by omega)))

end VG.Proof.MlDsa.AArch64.PreparedKey
