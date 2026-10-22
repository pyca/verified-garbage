module

public import VerifiedGarbage.Proof.Dsa.Arm.Gen.KSLoad
public import VerifiedGarbage.Proof.Bignum.Arm.ReverseBuffer
import VerifiedGarbage.Proof.Rsa.Arm.CvStore
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter generation on ARMv7: numbers out of the key working space

`storeBE L j o n` (`storeBE_vp`): the claim at byte `o` of `scratch` := the
low `n` bytes of array `j`, big-endian.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm VG.Proof.Mont VG.Proof.Rsa.Arm.Keys
open VG.Impl.Dsa.Arm.Generation
open VG.Impl.Rsa.Arm.Keys (hdr ptr)
open VG.Proof.X25519.Arm (Rest Upd wp_mov wp_movw wp_dp wp_mul op2_imm op2_reg dpVal)
open VG.Proof.Rsa.Arm.Recover (VP)

section
variable {G : GP} {σ : State} {c : Cfg} {s : State}

/-- The pointer to array `j`, from a state of the search. -/
theorem SS.ptr_ok (h : SS G σ c s) {r : Reg} (hr : r ∉ [.r7, .r8, .r9]) {j : Nat} (hj : j < 256)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, t.gpr r = G.KB + BitVec.ofNat 32 (arr G.w j) → Rest [r] s t → t.mem = s.mem →
      WP isa (.block rest) t Q) :
    WP isa (.block (ptr r j ++ rest)) s Q := by
  have r7 : r ≠ .r7 := fun e => hr (by simp [e])
  have r8 : r ≠ .r8 := fun e => hr (by simp [e])
  unfold ptr
  refine wp_mov (op2_imm (encodable_lt hj)) fun s1 u1 => ?_
  refine wp_mul fun s2 u2 => ?_
  refine wp_dp (op2_reg _ _) fun s3 u3 => ?_
  refine wp_dp (op2_imm (by decide)) fun t u4 => ?_
  have rest : Rest [r] s t :=
    (u1.rest (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans (u4.rest (by simp))))
  refine k t ?_ rest (by rw [u4.mem, u3.mem, u2.mem, u1.mem])
  rw [u4.gpr, dpVal, u3.gpr, dpVal, u2.gpr, u1.gpr, u2.other .r8 r8.symm, u1.other .r8 r8.symm,
    u1.other .r7 r7.symm, h.r7, h.r8]
  exact ptr_val _ _ _

end

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- The claim at byte `o` of `scratch` := `[j]`'s low `n` bytes, big-endian. -/
theorem storeBE_vp {L j o n : Nat} (cert : Cert7 (storeBE L j o n)) (hL : L = G.pLen) (hj : j ∈ c.live)
    (hn0 : 0 < n) (hnw : n ≤ 4 * G.w) (hoK : o + n ≤ sK G.pLen) {cl' : Claims}
    (hcl : ∀ x ∈ cl', x ∈ c.cl ∧ Apart o n x) :
    VP (St G c X) (storeBE L j o n)
      (St G { c with cl := (o, Spec.Rsa.i2osp (c.A j % 2 ^ (8 * n)) n) :: cl' } X) := by
  refine ks_vp cert (fun σ s h => h.1) fun σ s ⟨h, x⟩ => ?_
  subst hL
  have gi := h.gi
  have big := gi.scrBig
  have fit := gi.scrFit
  have l := h.lens
  have kb := h.kbNat
  have hjN := h.liveOk j hj
  have fa : arr G.w j + S G.w ≤ kz G.pLen := (h.ws).arr_fit hjN
  have hS : S G.w = 4 * (G.w + 2) := rfl
  have w96 : G.w ≤ 96 := by simp only [GP.w]; omega
  have inS : G.rScr ∈ s.wr := by rw [gi.wr, gi.pre.wr, gi.hG]; simp
  have ad : State.addr (G.KB + BitVec.ofNat 32 (arr G.w j)) = off (State.addr G.KB) (arr G.w j) :=
    h.ws.addr (by omega)
  have e : off (State.addr G.KB) (arr G.w j) = G.sa (sK G.pLen + arr G.w j) := by
    rw [gi.kaddr]; simp only [off, GP.sa]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have as : State.addr (G.scr + BitVec.ofNat 32 o) = G.sa o := gi.saddr (by omega)
  have va := h.arrs.get hj
  unfold storeBE
  refine WP.seq (h.ptr_ok (r := .r1) (by decide) (by simp only [nArrs] at hjN; omega) fun s₁ p₁ R₁ m₁ => ?_)
  refine wp_movw fun s₂ u₂ => ?_
  refine wp_dp (op2_reg _ _) fun s₃ u₃ => ?_
  have r8₃ : s₃.gpr .r8 = G.KB := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), R₁.gpr _ (by decide), h.r8]
  refine scr_ok (d := .r0) (o := o) r8₃ rfl l (by omega) fun s₄ v₄ R₄ M₄ => ?_
  refine wp_movw fun s₅ u₅ => WP.block_nil ?_
  have R₅ : Rest [.r0, .r1, .r2, .r12, .lr] s s₅ := (R₁.mono (by simp)).trans ((u₂.rest (by simp)).trans
    ((u₃.rest (by simp)).trans ((R₄.mono (by simp)).trans (u₅.rest (by simp)))))
  have m₅ : s₅.mem = s.mem := by rw [u₅.mem, M₄, u₃.mem, u₂.mem, m₁]
  have wr₅ : s₅.wr = s.wr := R₅.wr
  have srcFit : (G.KB + BitVec.ofNat 32 (arr G.w j)).toNat + n ≤ 2 ^ 32 := by
    rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat]; omega
  have dstFit : (G.scr + BitVec.ofNat 32 o).toNat + n ≤ 2 ^ 32 := by
    rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat]; omega
  refine WP.mono (VG.Proof.Bignum.Arm.reverseBuffer_ok s₅ (src := G.KB + BitVec.ofNat 32 (arr G.w j)) (dst := G.scr + BitVec.ofNat 32 o)
    (n := n) hn0 srcFit dstFit (by omega)
    ⟨G.rScr, List.mem_append_right _ (by rw [wr₅]; exact inS), by
      rw [ad, e]; exact Offset.contains_base _ (by omega) (by omega)⟩
    ⟨G.rScr, by rw [wr₅]; exact inS, by rw [as]; exact Offset.contains_base _ (by omega) (by omega)⟩
    (by rw [ad, e, as]; exact gi.sdisj (.inr (by omega)) (by omega) (by omega))
    (by rw [u₅.other _ (by decide), v₄])
    (by rw [u₅.other _ (by decide), R₄.gpr _ (by decide), u₃.gpr, dpVal, u₂.gpr, u₂.other _ (by decide), p₁,
      setWidth_ofNat16 (by omega)])
    (by rw [u₅.gpr, setWidth_ofNat16 (by omega)])) ?_
  rintro t ⟨bt, ft, _, rt⟩
  rw [as, ad, m₅, VG.Proof.Rsa.Arm.CrtValues.read_low _ _ (n := G.w) hnw,
    show val32 s.mem (State.addr G.KB) (arr G.w j) G.w = num s.mem G.KB G.w j from rfl, va] at bt
  rw [as, m₅] at ft
  refine ⟨h.of_scr (R₅.trans (rt.mono (by simp))) (o := o) (n := n) hoK (ft.mono (by simp)) fun y hy => ?_, x⟩
  rcases List.mem_cons.mp hy with rfl | hy
  · exact .inr ⟨by rw [VG.Proof.Rsa.i2osp_length]; exact bt, by rw [VG.Proof.Rsa.i2osp_length]; exact hoK⟩
  · exact .inl (hcl y hy)

end

end VG.Proof.Dsa.Arm.Gen
