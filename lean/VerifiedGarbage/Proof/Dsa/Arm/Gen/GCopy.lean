module

public import VerifiedGarbage.Proof.Dsa.Arm.Gen.KSStore
public import VerifiedGarbage.Proof.Bignum.Arm.CopyBuffer
import VerifiedGarbage.Proof.Rsa.Arm.CvStore
import VerifiedGarbage.Proof.Rsa.Arm.CvLoad
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter generation on ARMv7: copies between the arrays and `scratch`

`copyOut_vp`: the low `n` bytes of array `j` to byte `dst` of `scratch`, as
they are (little-endian); `copyIn_vp`: array `j` := the number of
`4 w` bytes at byte `src` of `scratch`.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm VG.Proof.Mont VG.Proof.Rsa.Arm.Keys
open VG.Impl.Dsa.Arm.Generation
open VG.Impl.Rsa.Arm.Keys (hdr ptr)
open VG.Proof.X25519.Arm (Rest Upd wp_movw)
open VG.Proof.Rsa.Arm.Recover (VP)

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- Byte `dst` of `scratch` := the low `n` bytes of `[j]`, little-endian. -/
theorem copyOut_vp {L j dst n : Nat} (cert : Cert7 (copyN (scr L .r0 dst) (ptr .r1 j) n)) (hL : L = G.pLen)
    (hj : j ∈ c.live) (hn0 : 0 < n) (hnw : n ≤ 4 * G.w) (hd : dst + n ≤ sK G.pLen) {cl' : Claims}
    (hcl : ∀ x ∈ cl', x ∈ c.cl ∧ Apart dst n x) {E : Mem → Prop}
    (hE : ∀ m m', E m → Frame [G.rs dst n] m m' → E m') :
    VP (fun σ s => St G c X σ s ∧ E s.mem) (copyN (scr L .r0 dst) (ptr .r1 j) n)
      (fun σ t => St G { c with cl := cl' } X σ t ∧ E t.mem ∧
        (t.mem.read (G.sa dst) n).toNat = c.A j % 2 ^ (8 * n)) := by
  refine ks_vp cert (fun σ s h => h.1.1) fun σ s ⟨⟨h, x⟩, ex⟩ => ?_
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
  have as : State.addr (G.scr + BitVec.ofNat 32 dst) = G.sa dst := gi.saddr (by omega)
  have va := h.arrs.get hj
  unfold copyN
  rw [List.append_assoc]
  refine WP.seq (h.ptr_ok (r := .r1) (by decide) (by simp only [nArrs] at hjN; omega) fun s₁ p₁ R₁ m₁ => ?_)
  have r8₁ : s₁.gpr .r8 = G.KB := by rw [R₁.gpr _ (by decide), h.r8]
  refine scr_ok (d := .r0) (o := dst) r8₁ rfl l (by omega) fun s₂ v₂ R₂ M₂ => ?_
  refine wp_movw fun s₃ u₃ => WP.block_nil ?_
  have R₃ : Rest [.r0, .r1, .r12, .lr] s s₃ := (R₁.mono (by simp)).trans ((R₂.mono (by simp)).trans
    (u₃.rest (by simp)))
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, M₂, m₁]
  have srcFit : (G.KB + BitVec.ofNat 32 (arr G.w j)).toNat + n ≤ 2 ^ 32 := by
    rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat]; omega
  have dstFit : (G.scr + BitVec.ofNat 32 dst).toNat + n ≤ 2 ^ 32 := by
    rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat]; omega
  refine WP.mono (VG.Proof.Bignum.Arm.copyBuffer_ok s₃ (src := G.KB + BitVec.ofNat 32 (arr G.w j))
    (dst := G.scr + BitVec.ofNat 32 dst) (n := n) hn0 srcFit dstFit (by omega)
    ⟨G.rScr, List.mem_append_right _ (by rw [R₃.wr]; exact inS), by
      rw [ad, e]; exact Offset.contains_base _ (by omega) (by omega)⟩
    ⟨G.rScr, by rw [R₃.wr]; exact inS, by rw [as]; exact Offset.contains_base _ (by omega) (by omega)⟩
    (by rw [ad, e, as]; exact gi.sdisj (.inr (by omega)) (by omega) (by omega))
    (by rw [u₃.other _ (by decide), v₂])
    (by rw [u₃.other _ (by decide), R₂.gpr _ (by decide), p₁])
    (by rw [u₃.gpr, setWidth_ofNat16 (by omega)])) ?_
  rintro t ⟨rt, ft, _, Rt⟩
  rw [as, m₃] at ft
  rw [as, ad, m₃] at rt
  refine ⟨⟨h.of_scr ((R₃.mono (ws' := [.r0, .r1, .r2, .r12, .lr]) (by simp)).trans (Rt.mono (by simp))) (o := dst) (n := n) hd (ft.mono (by simp))
    fun y hy => .inl (hcl y hy), x⟩, hE _ _ ex ft, ?_⟩
  rw [rt, VG.Proof.Rsa.Arm.CrtValues.read_low _ _ (n := G.w) hnw]
  exact congrArg (· % 2 ^ (8 * n)) va

/-- `[j]` := the number of `4 w` bytes at byte `src` of `scratch`. -/
theorem copyIn_vp {L j src n v : Nat} (cert : Cert7 (copyN (ptr .r0 j) (scr L .r1 src) n)) (hL : L = G.pLen)
    (hjN : j < nArrs) (hn : n = 4 * G.w) (hs : src + n ≤ sK G.pLen) :
    VP (fun σ s => St G c X σ s ∧ (s.mem.read (G.sa src) n).toNat = v) (copyN (ptr .r0 j) (scr L .r1 src) n)
      (St G { c with A := KU c.A j v, live := j :: c.live } X) := by
  refine ks_vp cert (fun σ s h => h.1.1) fun σ s ⟨⟨h, x⟩, ev⟩ => ?_
  subst hL
  have gi := h.gi
  have big := gi.scrBig
  have fit := gi.scrFit
  have l := h.lens
  have kb := h.kbNat
  have fa : arr G.w j + S G.w ≤ kz G.pLen := (h.ws).arr_fit hjN
  have hS : S G.w = 4 * (G.w + 2) := rfl
  have w96 : G.w ≤ 96 := by simp only [GP.w]; omega
  have w1 : 1 ≤ G.w := by simp only [GP.w]; omega
  have inS : G.rScr ∈ s.wr := by rw [gi.wr, gi.pre.wr, gi.hG]; simp
  have ad : State.addr (G.KB + BitVec.ofNat 32 (arr G.w j)) = off (State.addr G.KB) (arr G.w j) :=
    h.ws.addr (by omega)
  have e : off (State.addr G.KB) (arr G.w j) = G.sa (sK G.pLen + arr G.w j) := by
    rw [gi.kaddr]; simp only [off, GP.sa]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have as : State.addr (G.scr + BitVec.ofNat 32 src) = G.sa src := gi.saddr (by omega)
  unfold copyN
  rw [List.append_assoc]
  refine WP.seq (scr_ok (d := .r1) (o := src) h.r8 rfl l (by omega) fun s₁ v₁ R₁ M₁ => ?_)
  have h₁ := h.of_rest (R₁.mono (ws' := [.r12, .r1]) (by simp)) M₁
  refine h₁.ptr_ok (r := .r0) (by decide) (by simp only [nArrs] at hjN; omega) fun s₂ p₂ R₂ m₂ => ?_
  refine wp_movw fun s₃ u₃ => WP.block_nil ?_
  have R₃ : Rest [.r0, .r1, .r12, .lr] s s₃ := (R₁.mono (by simp)).trans ((R₂.mono (by simp)).trans
    (u₃.rest (by simp)))
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, m₂, M₁]
  have srcFit : (G.scr + BitVec.ofNat 32 src).toNat + n ≤ 2 ^ 32 := by
    rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat]; omega
  have dstFit : (G.KB + BitVec.ofNat 32 (arr G.w j)).toNat + n ≤ 2 ^ 32 := by
    rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat]; omega
  refine WP.mono (VG.Proof.Bignum.Arm.copyBuffer_ok s₃ (src := G.scr + BitVec.ofNat 32 src)
    (dst := G.KB + BitVec.ofNat 32 (arr G.w j)) (n := n) (by omega) srcFit dstFit (by omega)
    ⟨G.rScr, List.mem_append_right _ (by rw [R₃.wr]; exact inS), by
      rw [as]; exact Offset.contains_base _ (by omega) (by omega)⟩
    ⟨G.rScr, by rw [R₃.wr]; exact inS, by rw [ad, e]; exact Offset.contains_base _ (by omega) (by omega)⟩
    (by rw [ad, e, as]; exact gi.sdisj (.inl (by omega)) (by omega) (by omega))
    (by rw [u₃.other _ (by decide), p₂])
    (by rw [u₃.other _ (by decide), R₂.gpr _ (by decide), v₁])
    (by rw [u₃.gpr, setWidth_ofNat16 (by omega)])) ?_
  rintro t ⟨rt, ft, _, Rt⟩
  rw [ad, m₃] at ft rt
  rw [as] at rt
  have hrK : Region.Sub ⟨off (State.addr G.KB) (arr G.w j), n⟩ ⟨off (State.addr G.KB) (arr G.w j), S G.w⟩ :=
    fun a h => by simp only [Region.Contains] at h ⊢; omega
  have k : Keep G.KB G.w [j] [] s.mem t.mem :=
    VG.Proof.Rsa.Arm.CrtValues.Keep.of_frame_arr (ft.sub fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, hrK⟩) (by omega)
  have fK : Frame [G.rK] s.mem t.mem := ft.sub fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact ⟨G.rK, List.mem_singleton_self _, Offset.sub_base (State.addr G.KB) (by omega)⟩
  have vw : num t.mem G.KB G.w j = v := by
    rw [← ev, ← rt, hn]
    exact (VG.Proof.Bignum.read_eq_val32 t.mem (State.addr G.KB) G.w (arr G.w j)).symm
  exact ⟨h.of_op ((R₃.mono (ws' := [.r0, .r1, .r2, .r12, .lr]) (by simp)).trans (Rt.mono (by simp))) fK hjN k vw, x⟩

end

end VG.Proof.Dsa.Arm.Gen
