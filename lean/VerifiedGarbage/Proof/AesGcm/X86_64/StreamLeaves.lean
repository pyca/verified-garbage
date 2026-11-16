module

public import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTextS
public import VerifiedGarbage.Proof.AesGcm.X86_64.SealLeaves
public import VerifiedGarbage.Proof.AesGcm.X86_64.OpenLeaves
import VerifiedGarbage.Proof.AesGcm.X86_64.CryptOk
import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks
import VerifiedGarbage.Proof.AesGcm.X86_64.Ghash1
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamCrypt
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# AES-GCM on x86-64: what `streamTextS` leaves in `W`

Untrusted: everything here is checked by Lean. With implementations of
`vg_aes_ctr32` and `vg_ghash` that never touch their working space, and a
blocks function that leaves in its `scratch` a function of its arguments
(`BlkLeft`), `streamTextS` leaves in `W` from byte 448 on what that
function says if it called it (at least 256 bytes), and else what was
there (`streamTextS_leaves`); and at `192`–`224` the lengths and the data's
address past what it did in the pieces before the rest. Each piece keeps
`W + 448` (`Keep448`): the additional data padded (`startS_keep`), the
head (`headPart_keep`) and the rest (`part_keep`); the whole blocks leave
what the function says (`blocks_leaves`).
-/

-- separate module: its one importer imports `Instances`, and with it every proof of AES-GCM on x86-64; these generic proofs need no re-checking when one of those changes

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt zeros padLen ghashInput)
open VG.Proof.Gcm (Absorbed Ctr)

/-- The bytes of `W` from 448 on, the blocks function's `scratch`, as they were. -/
abbrev Keep448 (W : Addr) (m m' : Mem) : Prop :=
  ∀ x, (⟨W + BitVec.ofNat 64 448, 2112⟩ : Region).Contains x 1 → m' x = m x

theorem Keep448.refl (W : Addr) (m : Mem) : Keep448 W m m := fun _ _ => rfl

theorem Keep448.trans {W : Addr} {m₁ m₂ m₃ : Mem} (h₁ : Keep448 W m₁ m₂) (h₂ : Keep448 W m₂ m₃) :
    Keep448 W m₁ m₃ := fun x hx => (h₂ x hx).trans (h₁ x hx)

theorem Keep448.of_eq {W : Addr} {m₁ m₂ : Mem} (h : m₂ = m₁) : Keep448 W m₁ m₂ := fun _ _ => by rw [h]

theorem Keep448.of_frame {W : Addr} {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨W + BitVec.ofNat 64 448, 2112⟩ : Region).Disjoint r) : Keep448 W m m' :=
  fun _ hx => frame_at hf hd hx

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

theorem k448_crFrameS {s : State} {Dj : Addr} {k : Nat} (hd : DataOk St W SP s Dj k) :
    ∀ r ∈ crFrameS St W SP Dj k 0, (⟨W + BitVec.ofNat 64 448, 2112⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hd.w.sub_right (Lay.wSub (by decide))).symm
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact Lay.disj_empty
  · exact (L.stk_w (by decide)).symm

theorem k448_absFrame : ∀ r ∈ absFrame St W SP 16 0, (⟨W + BitVec.ofNat 64 448, 2112⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact Lay.disj_empty
  · exact (L.stk_w (by decide)).symm

theorem k448_sFrame : ∀ r ∈ sFrame St W SP 16 0, (⟨W + BitVec.ofNat 64 448, 2112⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact Lay.disj_empty
  · exact (L.stk_w (by decide)).symm

theorem k448_slots {d k : Nat} (h : d + k ≤ 448) :
    ∀ r ∈ [(⟨W + BitVec.ofNat 64 d, k⟩ : Region)], (⟨W + BitVec.ofNat 64 448, 2112⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact L.w_w (.inr h) (by decide) (by omega_arith)

end

/-- `absorb`'s output with no working space for `vg_ghash`, with all 256. -/
theorem AbsOut.of0 {Ctx St W SP : Addr} {yo : Nat} {H : Block} {x₀ x : List Byte} {m₀ : Mem} {s : State}
    (h : AbsOut Ctx St W SP yo H x₀ x m₀ s 2560 0) : AbsOut Ctx St W SP yo H x₀ x m₀ s :=
  ⟨h.env, h.abs, h.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · exact ⟨⟨St + BitVec.ofNat 64 32, 16⟩, by simp, fun _ h => h⟩
    · exact ⟨⟨W + BitVec.ofNat 64 512, 256⟩, by simp, sub_empty⟩
    · exact ⟨below SP 8, by simp, fun _ h => h⟩⟩

/-! ## The pieces that keep `W + 448` -/

section
variable (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} {Hyp : Prop} {Ctx St W SP : Addr} {R : Nat} {H icb : Block}
  {x₀ : List Byte} {P₀ : Nat} {t : Bool} {D : Addr} {n : Nat} {m₀ : Mem}

/-- `partWith_ok`'s pieces, keeping `W + 448`: so does `partWith`. -/
theorem partWith_keep (K : SCtx M Ctx St W SP R H D n m₀) (enc : Bool) {cr ab : Prog isa} {j k : Nat} {s : State}
    (hcr : ∀ {t : State}, CrIn Ctx St W SP R icb (P₀ + j) (D + BitVec.ofNat 64 j) k t →
      WP isa cr t fun t' => CrOut Ctx St W SP R icb (P₀ + j) (D + BitVec.ofNat 64 j) k t.mem t' ∧
        Keep448 W t.mem t'.mem)
    (hab : ∀ {x : List Byte} {t : State}, x.length % 16 = (P₀ + j) % 16 →
      AbsIn Ctx St W SP 16 H x (D + BitVec.ofNat 64 j) k t →
      WP isa ab t fun t' => AbsOut Ctx St W SP 16 H x (x ++ bytesAt t.mem (D + BitVec.ofNat 64 j) k) t.mem t' ∧
        Keep448 W t.mem t'.mem)
    (h : SInv M Hyp Ctx St W SP R H icb x₀ P₀ enc D n m₀ j s t)
    (hx : x₀.length % 16 = P₀ % 16) (hk : j + k ≤ n)
    (h12 : s.gpr .r12 = D + BitVec.ofNat 64 j) (hbp : s.gpr .rbp = BitVec.ofNat 64 k)
    (hbx : s.gpr .rbx = BitVec.ofNat 64 ((P₀ + j) % 16))
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 j)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 k)
    (htl : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 (P₀ + j)) :
    WP isa (partWith enc cr ab) s fun s' => Keep448 W s.mem s'.mem := by
  have L := K.lay
  have hD := h.data
  have hj := h.le
  obtain hdj : DataW Ctx St W SP s (D + BitVec.ofNat 64 j) k := (hD.drop hj).take (by omega_arith)
  obtain hR := h.rounds K
  obtain hH := h.hH K
  obtain hxl : (x₀ ++ ctext enc (ciphOf m₀ Ctx R) icb P₀ (bytesAt m₀ D j)).length % 16 = (P₀ + j) % 16 := by
    rw [List.length_append, length_ctext, length_bytesAt]; omega_arith
  cases enc
  · simp only [partWith, Bool.false_eq_true, ↓reduceIte]
    obtain hai : AbsIn Ctx St W SP 16 H (x₀ ++ ctext false (ciphOf m₀ Ctx R) icb P₀ (bytesAt m₀ D j))
        (D + BitVec.ofNat 64 j) k s := ⟨h.env, h12, hbp, by rw [hbx, hxl], hdj.ok, hH⟩
    refine WP.seq (WP.mono (WP.with_rdwr (hab hxl hai)) fun s₂ ⟨⟨ao, k₂⟩, rd₂, wr₂⟩ => ?_)
    obtain sl₂ : ∀ d, 176 ≤ d → d + 8 ≤ 240 →
        s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ =>
      ao.frame.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (slot_absFrame L h₁ (by omega_arith))
        (by decide)
    obtain ⟨s₃, run₃, h12₃, hbp₃, hbx₃, hg₃, hm₃, hrd₃, hwr₃⟩ := load_ok ao.env
      ((sl₂ 200 (by decide) (by decide)).trans hdat) ((sl₂ 208 (by decide) (by decide)).trans hlen)
      ((sl₂ 192 (by decide) (by decide)).trans htl)
    refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
    obtain he₃ := ao.env.keep (load_env hg₃) hrd₃ hwr₃
    rw [toNat_mod16] at hbx₃
    obtain hR₃ : RoundsAt s₃.mem W R := hm₃ ▸ rounds_frame ao.frame (slot_absFrame L (by decide) (by decide)) hR
    obtain hdj₃ : DataW Ctx St W SP s₃ (D + BitVec.ofNat 64 j) k := hdj.of_eq (hrd₃.trans rd₂) (hwr₃.trans wr₂)
    exact WP.mono (hcr ⟨he₃, h12₃, hbp₃, hbx₃, hdj₃, hR₃⟩) fun s₄ ⟨_, k₄⟩ =>
      k₂.trans ((Keep448.of_eq hm₃).trans k₄)
  · simp only [partWith, ↓reduceIte]
    refine WP.seq (WP.mono (WP.with_rdwr (hcr ⟨h.env, h12, hbp, hbx, hdj, hR⟩))
      fun s₂ ⟨⟨co, k₂⟩, rd₂, wr₂⟩ => ?_)
    obtain sl₂ : ∀ d, 176 ≤ d → d + 8 ≤ 240 →
        s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ =>
      co.frame.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (slot_crFrame L hdj.ok h₁ (by omega_arith))
        (by decide)
    obtain ⟨s₃, run₃, h12₃, hbp₃, hbx₃, hg₃, hm₃, hrd₃, hwr₃⟩ := load_ok co.env
      ((sl₂ 200 (by decide) (by decide)).trans hdat) ((sl₂ 208 (by decide) (by decide)).trans hlen)
      ((sl₂ 192 (by decide) (by decide)).trans htl)
    refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
    obtain he₃ := co.env.keep (load_env hg₃) hrd₃ hwr₃
    rw [toNat_mod16] at hbx₃
    obtain hdj₃ : DataW Ctx St W SP s₃ (D + BitVec.ofNat 64 j) k := hdj.of_eq (hrd₃.trans rd₂) (hwr₃.trans wr₂)
    obtain hH₃ : blockAt s₃.mem (Ctx + BitVec.ofNat 64 240) = H := by
      rw [hm₃, blockAt_frame co.frame (fun r hr => (ctx_crFrame L hdj r hr).sub_left (Lay.ctxSub (by decide))), hH]
    obtain hai : AbsIn Ctx St W SP 16 H (x₀ ++ ctext true (ciphOf m₀ Ctx R) icb P₀ (bytesAt m₀ D j))
        (D + BitVec.ofNat 64 j) k s₃ := ⟨he₃, h12₃, hbp₃, by rw [hbx₃, hxl], hdj₃.ok, hH₃⟩
    exact WP.mono (hab hxl hai) fun s₄ ⟨_, k₄⟩ => k₂.trans ((Keep448.of_eq hm₃).trans k₄)

/-- `part_ok`'s `partWith`, with callees that never touch their working
space: it keeps `W + 448`. -/
theorem part_keep (gf : GhashFree v.gh.fn.code) (cf : Proof.Aes.X86_64.Ctr32Free v.ctr.callee)
    (K : SCtx M Ctx St W SP R H D n m₀) (enc : Bool) {j k : Nat} {s : State}
    (h : SInv M Hyp Ctx St W SP R H icb x₀ P₀ enc D n m₀ j s t)
    (hx : x₀.length % 16 = P₀ % 16) (hk : j + k ≤ n)
    (h12 : s.gpr .r12 = D + BitVec.ofNat 64 j) (hbp : s.gpr .rbp = BitVec.ofNat 64 k)
    (hbx : s.gpr .rbx = BitVec.ofNat 64 ((P₀ + j) % 16))
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 j)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 k)
    (htl : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 (P₀ + j)) :
    WP isa (partWith enc (crypt v.callees) (absorb v.callees 16)) s fun s' => Keep448 W s.mem s'.mem :=
  partWith_keep K enc
    (fun hc => WP.mono (crypt_okP v K.lay (CrCallP.free v cf) hc) fun _ ⟨o, f⟩ =>
      ⟨o, Keep448.of_frame f (k448_crFrameS K.lay hc.data.ok)⟩)
    (fun _ ha => WP.mono (absorb_ok v (G := GhFits.free v gf 2560) K.lay (.inr rfl) ha) fun _ o =>
      ⟨o.of0, Keep448.of_frame o.frame (k448_absFrame K.lay)⟩)
    h hx hk h12 hbp hbx hdat hlen htl

/-- `headPart_ok`'s piece, with an implementation of `vg_ghash` that never
touches its working space: it keeps `W + 448`. -/
theorem headPart_keep (gf : GhashFree v.gh.fn.code) (K : SCtx M Ctx St W SP R H D n m₀) (enc : Bool) {s : State}
    (h : SInv M Hyp Ctx St W SP R H icb x₀ P₀ enc D n m₀ 0 s t)
    (hx : x₀.length % 16 = P₀ % 16) (hn : n ≠ 0)
    (h12 : s.gpr .r12 = D + BitVec.ofNat 64 0) (hbp : s.gpr .rbp = BitVec.ofNat 64 (headLen P₀ n))
    (hbx : s.gpr .rbx = BitVec.ofNat 64 ((P₀ + 0) % 16))
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 0)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (headLen P₀ n))
    (htl : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 (P₀ + 0)) :
    WP isa (headPart v.callees enc) s fun s' => Keep448 W s.mem s'.mem := by
  obtain hlt := Nat.mod_lt (P₀ + 0) (show 16 > 0 by decide)
  obtain ⟨s₁, run₁, hz₁, hg₁, hm₁, hrd₁, hwr₁⟩ := test_ok s .rbx hbx (by omega_arith)
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  obtain I₁ := h.regs (fun r _ => by rw [hg₁]) hm₁ hrd₁ hwr₁
  refine WP.ite (decide ((P₀ + 0) % 16 = 0)) (eval_e hz₁) (fun _ => ?_) (fun hf => ?_)
  · exact WP.block_nil (Keep448.of_eq hm₁)
  · have h0 : P₀ % 16 ≠ 0 := by simpa using hf
    obtain e : headLen P₀ n = min (16 - P₀ % 16) n := by simp [headLen, h0]
    obtain hk0 : headLen P₀ n ≠ 0 := by rw [e]; omega_arith
    obtain hle : headLen P₀ n ≤ 16 - (P₀ + 0) % 16 := by rw [e, Nat.add_zero]; omega_arith
    obtain hkn : 0 + headLen P₀ n ≤ n := by have := headLen_le P₀ n; omega_arith
    refine WP.mono (partWith_keep K enc
      (fun hc => WP.mono (cryptHead_okF hc hk0 (by rwa [Nat.add_zero])) fun s' ⟨hm, f⟩ => by
        obtain e' : min (16 - (P₀ + 0) % 16) (headLen P₀ n) = headLen P₀ n := Nat.min_eq_right hle
        rw [e'] at hm
        exact ⟨⟨hm.env, hm.rounds, hm.ctr, hm.done, hm.frame⟩, Keep448.of_frame f fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hc.data.ok.w.sub_right (Lay.wSub (by decide))).symm⟩)
      (fun hxl ha => WP.mono (absorbHead_out v (G := GhFits.free v gf 2560) K.lay (.inr rfl) ha hk0
          (by rw [hxl, Nat.add_zero]; exact h0) (by rw [hxl]; exact hle)) fun _ o =>
        ⟨o.of0, Keep448.of_frame o.frame (k448_absFrame K.lay)⟩)
      I₁ hx hkn (by rw [hg₁]; exact h12) (by rw [hg₁]; exact hbp) (by rw [hg₁]; exact hbx)
      (by rw [hm₁]; exact hdat) (by rw [hm₁]; exact hlen) (by rw [hm₁]; exact htl))
      fun s' k => (Keep448.of_eq hm₁).trans k

end

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

/-- `startS_ok`'s piece, with an implementation of `vg_ghash` that never
touches its working space: it keeps `W + 448`. -/
theorem startS_keep (gf : GhashFree v.gh.fn.code) {s : State} (he : Env Ctx St W SP s) {aL P : Nat}
    (hP : P < 2 ^ 64) (hal : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 aL)
    (htl : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 P) :
    WP isa (.seq (.block [.mov .rax (.mem (at_ .r15 tlenO)), .alu .test .rax (.reg .rax)])
      (.ite .e (firstFlushS v.callees) (.block []))) s fun s' => Keep448 W s.mem s'.mem := by
  obtain r₂ := he.perm.wR (show 192 + 8 ≤ 2560 by decide)
  obtain ⟨s₂, run₂, hz₂, hg₂, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa [.mov .rax (.mem (at_ .r15 tlenO)),
      .alu .test .rax (.reg .rax)] s = some s₂ ∧ s₂.zf = some (decide (P = 0)) ∧
      (∀ r, r ≠ .rax → s₂.gpr r = s.gpr r) ∧ s₂.mem = s.mem ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
    refine ⟨_, by xrun [he.r15, r₂], ?_, ?_, ?_⟩
    · simp only [zf_arithFlags, gpr_setReg, ite_true, htl, and_self_beq hP]
    · intro r a; simp [gpr_setReg, gpr_arithFlags, a]
    all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  obtain he₂ : Env Ctx St W SP s₂ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide)) hrd₂ hwr₂
  refine WP.ite (decide (P = 0)) (eval_e hz₂) (fun _ => ?_) (fun _ => WP.block_nil (Keep448.of_eq hm₂))
  obtain r₃ := he₂.perm.wR (show 184 + 8 ≤ 2560 by decide)
  obtain ⟨s₃, run₃, hbx₃, hg₃, hm₃, hrd₃, hwr₃⟩ : ∃ s₃, runBlock isa [.mov .rbx (.mem (at_ .r15 alenO)),
      .alu .and .rbx (imm 15)] s₂ = some s₃ ∧ s₃.gpr .rbx = BitVec.ofNat 64 (aL % 16) ∧
      (∀ r, r ≠ .rbx → s₃.gpr r = s₂.gpr r) ∧ s₃.mem = s₂.mem ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
    obtain hand := and15 (BitVec.ofNat 64 aL)
    rw [imm_eq (by decide), toNat_mod16] at hand
    refine ⟨_, by xrun [he₂.r15, r₃], ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, hm₂, hal, hand]
    · intro r a; simp [gpr_setReg, gpr_arithFlags, a]
    all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
  unfold firstFlushS
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  obtain he₃ : Env Ctx St W SP s₃ := he₂.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₃ _ (by decide)) hrd₃ hwr₃
  refine WP.mono (flushS_ok v (G := GhFits.free v gf 2560) L (yo := 16) (.inr rfl)
    (H := blockAt s₃.mem (Ctx + BitVec.ofNat 64 240)) (x := List.replicate aL 0) ⟨he₃, rfl⟩
    (by rw [hbx₃, List.length_replicate])) fun s₄ fo => ?_
  rw [← hm₂, ← hm₃]
  exact Keep448.of_frame fo.frame (k448_sFrame L)

end

section
variable {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

/-- `callBlocks_ok`'s call, of a function that leaves `Lb` in its `scratch`. -/
theorem callBlocks_okL (enc : Bool) {Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 →
      Addr → Addr → Option (BitVec 8)} (hL : BlkLeft Lb (if enc then B.enc else B.dec).code M)
    {R : Nat} {D : Addr} {n q : Nat} {s : State} (h : ObIn M Ctx St W SP R D n q s) :
    WP isa (.frame (.push [.rax]) (.call (if enc then B.enc else B.dec).name
      (if enc then B.enc else B.dec).code) (.pop .rax 1)) s fun s₄ =>
      (∀ r ∈ calleeSaved, s₄.gpr r = s.gpr r) ∧ s₄.rd = s.rd ∧ s₄.wr = s.wr ∧
      Frame (obFrame St W SP D q) s.mem s₄.mem ∧
      ∀ x, (⟨W + BitVec.ofNat 64 448, 2112⟩ : Region).Contains x 1 →
        s₄.mem x = (Lb Ctx (BitVec.ofNat 64 R) (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 16) D
          (BitVec.ofNat 64 q) (W + BitVec.ofNat 64 448) x).getD (s.mem x) := by
  cases enc
  · exact obFrameD_okL L B hL h
  · exact obFrameE_okL L B hL h

end

section
variable {M : Gcm.X86_64.Stitch.CtxMode} {Hyp : Prop} {Ctx St W SP : Addr} {R : Nat} {H icb : Block}
  {x₀ : List Byte} {P₀ : Nat} {t : Bool} {D : Addr} {n : Nat} {m₀ : Mem}

/-- `blocks_ok`'s `streamBlocks`, of a function that leaves `Lb` in its
`scratch`: there, if there was a whole block, what `Lb` says. -/
theorem blocks_leaves (B : BlkFn M) (K : SCtx M Ctx St W SP R H D n m₀) (enc : Bool)
    {Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr → Option (BitVec 8)}
    (hL : BlkLeft Lb (if enc then B.enc else B.dec).code M) {j : Nat} {s : State}
    (h : SInv M Hyp Ctx St W SP R H icb x₀ P₀ enc D n m₀ j s t)
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 j)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (n - j))
    (htl : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 (P₀ + j)) :
    WP isa (streamBlocks (if enc then B.enc else B.dec)) s fun s' =>
      s'.mem.readW (W + BitVec.ofNat 64 216) 64 = s.mem.readW (W + BitVec.ofNat 64 216) 64 ∧
      ∀ x, (⟨W + BitVec.ofNat 64 448, 2112⟩ : Region).Contains x 1 →
        s'.mem x = (if (n - j) / 16 = 0 then none else Lb Ctx (BitVec.ofNat 64 R) (St + BitVec.ofNat 64 48)
          (St + BitVec.ofNat 64 16) (D + BitVec.ofNat 64 j) (BitVec.ofNat 64 ((n - j) / 16))
          (W + BitVec.ofNat 64 448) x).getD (s.mem x) := by
  have L := K.lay
  have hD := h.data
  have hlt := hD.ok.lt
  have hj := h.le
  have he := h.env
  generalize hq : (n - j) / 16 = q
  unfold streamBlocks
  refine WP.seq (WP.mono (sb1_ok (L := n - j) (by omega_arith) he hlen) fun s₁ ⟨r₁, z₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
  rw [hq] at r₁ z₁
  obtain he₁ : Env Ctx St W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide)) rd₁ wr₁
  obtain h₁ : SInv M Hyp Ctx St W SP R H icb x₀ P₀ enc D n m₀ j s₁ t := h.regs (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide)) m₁ rd₁ wr₁
  refine WP.ite (decide (q = 0)) (by simp only [eval, z₁]) (fun hz => ?_) (fun hz => ?_)
  · simp only [decide_eq_true_eq] at hz
    subst hz
    exact WP.block_nil ⟨by rw [m₁], fun x _ => by rw [m₁]; rfl⟩
  · simp only [decide_eq_false_iff_not] at hz
    obtain hqk : j + q * 16 ≤ n := by omega_arith
    obtain hR₁ := h₁.rounds K
    refine WP.seq (WP.mono (ob2_ok (D := D + BitVec.ofNat 64 j) he₁ hR₁ (by rw [m₁]; exact hdat))
      fun s₂ ⟨a1, a2, a3, a4, a5, a6, a7, g₂, m₂, rd₂, wr₂⟩ => ?_)
    obtain he₂ : Env Ctx St W SP s₂ := he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₂ _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)) rd₂ wr₂
    obtain m₂' : s₂.mem = s.mem := m₂.trans m₁
    obtain hdq : DataW Ctx St W SP s₂ (D + BitVec.ofNat 64 j) (n - j) := (hD.drop hj).of_eq (rd₂.trans rd₁) (wr₂.trans wr₁)
    obtain obi : ObIn M Ctx St W SP R (D + BitVec.ofNat 64 j) (n - j) q s₂ := ⟨he₂, hdq, by omega_arith, K.t_c, K.t_w,
      K.t_d.sub_right (Offset.sub_base D (by omega_arith)), K.sp24, a1, a2, a3, a4, a5, by rw [a6, r₁], a7, K.rounds.2, K.t_s,
      (h.ext K).of_eq (rd₂.trans rd₁) (wr₂.trans wr₁) m₂'⟩
    refine WP.seq (WP.mono (callBlocks_okL B L enc hL obi) fun s₄ ⟨cs₄, rd₄, wr₄, fr₄, o₄⟩ => ?_)
    obtain he₄ : Env Ctx St W SP s₄ := he₂.of_saved cs₄ rd₄ wr₄
    obtain kp : ∀ d, 176 ≤ d → d + 8 ≤ 240 →
        s₄.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ => by
      rw [fr₄.readW (Region.contains_self _ _) (slot_obFrame L hdq.ok.w (by omega_arith) K.t_w h₁ h₂) (by decide), m₂']
    refine WP.mono (sb3_ok (L := n - j) (by omega_arith) he₄ ((kp 200 (by decide) (by decide)).trans hdat)
      ((kp 208 (by decide) (by decide)).trans hlen) ((kp 192 (by decide) (by decide)).trans htl))
      fun s₅ ⟨_, _, _, _, f₅, _, _⟩ => ⟨?_, fun x hx => ?_⟩
    · rw [f₅.readW (r := ⟨W + BitVec.ofNat 64 216, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.w_w (.inr (by decide)) (by decide) (by decide)) (by decide), kp 216 (by decide) (by decide)]
    · rw [frame_at f₅ (k448_slots L (by decide)) hx, o₄ x hx, m₂', ite_eq_right hz]

end

/-- Where `streamTextS` leaves the data kept, of `n` bytes after `P` of text:
at the start, if fewer than 256, else past the head and the whole blocks. -/
def stJ (P n : Nat) : Nat := if n < 256 then 0 else headLen P n + 16 * ((n - headLen P n) / 16)

theorem stJ_le (P n : Nat) : stJ P n ≤ n := by
  have := headLen_le P n
  unfold stJ; split <;> omega_arith

section
variable (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} {Hyp : Prop} {Ctx St W SP : Addr} {R : Nat} {H icb : Block}
  {D : Addr} {n : Nat} {m₀ : Mem}

/-- `streamTextS enc`, with callees that never touch their working space and
a blocks function that leaves `Lb` in its `scratch`: the lengths and the data
kept at `192`–`216` past `stJ`, the whole length at `216` if it called the
blocks function, and in its `scratch` what `Lb` says if it did. -/
theorem streamTextS_leaves (gf : GhashFree v.gh.fn.code) (cf : Proof.Aes.X86_64.Ctr32Free v.ctr.callee)
    (B : BlkFn M) (K : SCtx M Ctx St W SP R H D n m₀) (enc : Bool)
    {Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr → Option (BitVec 8)}
    (hL : BlkLeft Lb (if enc then B.enc else B.dec).code M) {s : State}
    (he : Env Ctx St W SP s) (hm : s.mem = m₀) (hd : DataW Ctx St W SP s D n)
    (hcov : Covers [⟨Ctx, M.len⟩] (s.rd ++ s.wr)) (hbp : s.gpr .rbp = BitVec.ofNat 64 n)
    {a c₀ : List Byte} (hP : c₀.length < 2 ^ 64)
    (hal : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 a.length)
    (htl : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 c₀.length)
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n)
    (hyA : Hyp → Absorbed m₀ (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (ghashInput a c₀))
    (hyC : Hyp → Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx R) icb c₀.length) :
    WP isa (streamTextS (v.withBlk B) enc) s fun s' =>
      s'.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 (c₀.length + stJ c₀.length n) ∧
      s'.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 (stJ c₀.length n) ∧
      s'.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (n - stJ c₀.length n) ∧
      s'.mem.readW (W + BitVec.ofNat 64 216) 64 =
        (if n < 256 then s.mem.readW (W + BitVec.ofNat 64 216) 64 else BitVec.ofNat 64 n) ∧
      ∀ x, (⟨W + BitVec.ofNat 64 448, 2112⟩ : Region).Contains x 1 →
        s'.mem x = (if n < 256 then none else Lb Ctx (BitVec.ofNat 64 R) (St + BitVec.ofNat 64 48)
          (St + BitVec.ofNat 64 16) (D + BitVec.ofNat 64 (headLen c₀.length n))
          (BitVec.ofNat 64 ((n - headLen c₀.length n) / 16)) (W + BitVec.ofNat 64 448) x).getD (s.mem x) := by
  have hlt := hd.ok.lt
  have L := K.lay
  obtain hx : (a ++ zeros (padLen a.length) ++ c₀).length % 16 = c₀.length % 16 := by
    have := Proof.Gcm.length_pad_mod a.length
    simp only [List.length_append, Proof.Gcm.length_zeros]; omega_arith
  simp only [streamTextS]
  obtain ⟨s₁, run₁, hz₁, hg₁, hm₁, hrd₁, hwr₁⟩ := test_ok s .rbp hbp hlt
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  obtain he₁ : Env Ctx St W SP s₁ := he.keep (fun r _ => by rw [hg₁]) hrd₁ hwr₁
  refine WP.ite (decide (n = 0)) (eval_e hz₁) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    simp only [stJ, show (0 : Nat) < 256 by decide, ↓reduceIte, Nat.add_zero, Nat.sub_zero, BitVec.add_zero]
    exact WP.block_nil ⟨by rw [hm₁]; exact htl, by rw [hm₁]; exact hdat, by rw [hm₁]; exact hlen, by rw [hm₁],
      fun x _ => by rw [hm₁]; rfl⟩
  obtain h0 : n ≠ 0 := by simpa using hf
  obtain sl₁ : ∀ d, s₁.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d => by
    rw [hm₁]
  refine WP.assoc (WP.seq (WP.mono (wp_both (startS_ok v K enc he₁ (hm₁.trans hm) (hd.of_eq hrd₁ hwr₁)
    (by rw [hrd₁, hwr₁]; exact hcov) (c₀ := c₀) hP (by rw [sl₁]; exact hal) (by rw [sl₁]; exact htl) hyA hyC)
    (startS_keep v L gf he₁ hP (by rw [sl₁]; exact hal) (by rw [sl₁]; exact htl)))
    fun s₂ ⟨⟨I₂, sl₂⟩, k₂⟩ => ?_))
  rw [hm₁] at k₂
  obtain ⟨s₃, run₃, h12₃, hbp₃, hbx₃, hg₃, hm₃, hrd₃, hwr₃⟩ := load_ok I₂.env
    ((sl₂ 200 (by decide) (by decide)).trans ((sl₁ 200).trans hdat))
    ((sl₂ 208 (by decide) (by decide)).trans ((sl₁ 208).trans hlen))
    ((sl₂ 192 (by decide) (by decide)).trans ((sl₁ 192).trans htl))
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  rw [toNat_mod16] at hbx₃
  obtain I₃ := I₂.regs (load_env hg₃) hm₃ hrd₃ hwr₃
  obtain sl₃ : ∀ d, 176 ≤ d → d + 8 ≤ 240 →
      s₃.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ => by
    rw [hm₃, sl₂ d h₁ h₂, sl₁]
  obtain k₃ : Keep448 W s.mem s₃.mem := k₂.trans (Keep448.of_eq hm₃)
  obtain ⟨s₃', run₃', hcf, hg', hm', hrd', hwr'⟩ := small_ok s₃ hbp₃ hlt
  refine WP.seq (WP.of_runBlock ⟨s₃', run₃', ?_⟩)
  obtain I₃' := I₃.regs (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg' _ (by decide)) hm' hrd' hwr'
  obtain h12₃' : s₃'.gpr .r12 = D := by rw [hg' .r12 (by decide)]; exact h12₃
  obtain hbp₃' : s₃'.gpr .rbp = BitVec.ofNat 64 n := by rw [hg' .rbp (by decide)]; exact hbp₃
  obtain hbx₃' : s₃'.gpr .rbx = BitVec.ofNat 64 (c₀.length % 16) := by rw [hg' .rbx (by decide)]; exact hbx₃
  obtain sl₃' : ∀ d, 176 ≤ d → d + 8 ≤ 240 →
      s₃'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ => by
    rw [hm']; exact sl₃ d h₁ h₂
  obtain k₃' : Keep448 W s.mem s₃'.mem := k₃.trans (Keep448.of_eq hm')
  generalize hJ : stJ c₀.length n = J
  obtain hJn : J ≤ n := hJ ▸ stJ_le c₀.length n
  -- Where the rest starts: all of it if short, after the head and the whole blocks otherwise.
  refine WP.seq (WP.mono (Q := fun (s' : State) =>
      SInv M Hyp Ctx St W SP R H icb (a ++ zeros (padLen a.length) ++ c₀) c₀.length enc D n m₀ J s' false ∧
      s'.gpr .r12 = D + BitVec.ofNat 64 J ∧ s'.gpr .rbp = BitVec.ofNat 64 (n - J) ∧
      s'.gpr .rbx = BitVec.ofNat 64 ((c₀.length + J) % 16) ∧
      s'.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 J ∧
      s'.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (n - J) ∧
      s'.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 (c₀.length + J) ∧
      s'.mem.readW (W + BitVec.ofNat 64 216) 64 =
        (if n < 256 then s.mem.readW (W + BitVec.ofNat 64 216) 64 else BitVec.ofNat 64 n) ∧
      ∀ x, (⟨W + BitVec.ofNat 64 448, 2112⟩ : Region).Contains x 1 →
        s'.mem x = (if n < 256 then none else Lb Ctx (BitVec.ofNat 64 R) (St + BitVec.ofNat 64 48)
          (St + BitVec.ofNat 64 16) (D + BitVec.ofNat 64 (headLen c₀.length n))
          (BitVec.ofNat 64 ((n - headLen c₀.length n) / 16)) (W + BitVec.ofNat 64 448) x).getD (s.mem x))
    (WP.ite (decide (n < 256)) (eval_b hcf) (fun ht => ?_) (fun hf' => ?_))
    fun s' ⟨I, h12, hbp, hbx, hd', hl, ht, h216, hw⟩ => ?_)
  · obtain hn : n < 256 := by simpa using ht
    obtain hJ0 : J = 0 := by rw [← hJ]; simp [stJ, hn]
    subst hJ0
    refine WP.block_nil ⟨I₃', by simp [h12₃'], by rw [Nat.sub_zero]; exact hbp₃', by rw [hbx₃', Nat.add_zero],
      by rw [sl₃' 200 (by decide) (by decide), hdat]; simp, by rw [sl₃' 208 (by decide) (by decide), hlen, Nat.sub_zero],
      by rw [sl₃' 192 (by decide) (by decide), htl, Nat.add_zero], by rw [sl₃' 216 (by decide) (by decide)]; simp [hn],
      fun x hx => by rw [k₃' x hx]; simp [hn]⟩
  · obtain hn : ¬ n < 256 := by simpa using hf'
    -- The head.
    refine WP.seq (WP.mono (sHead_ok I₃'.env hlt hbx₃' hbp₃') fun s₄ ⟨hbp₄, hg₄, hl₄, ha₄, f₄, hrd₄, hwr₄⟩ => ?_)
    generalize hk : headLen c₀.length n = k at hbp₄ hl₄
    obtain hkn : k ≤ n := hk ▸ headLen_le c₀.length n
    obtain hk16 : k < 16 := by rw [← hk]; unfold headLen; split <;> omega_arith
    obtain hkw := headLen_whole c₀.length n
    rw [hk] at hkw
    obtain g₄ : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s₄.gpr r = s₃'.gpr r := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg₄ _ (by decide) (by decide)
    obtain I₄ := I₃'.slots K g₄ hrd₄ hwr₄ (by decide) (by decide) f₄
    obtain sl₄ : ∀ d, 176 ≤ d → d + 8 ≤ 208 →
        s₄.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ => by
      rw [f₄.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact K.lay.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)) (by decide), sl₃' d h₁ (by omega_arith)]
    obtain k₄ : Keep448 W s.mem s₄.mem := k₃'.trans (Keep448.of_frame f₄ (k448_slots L (by decide)))
    subst hk
    refine WP.seq (WP.mono (wp_both (headPart_ok v K enc I₄ hx h0 (by simp [hg₄ .r12 (by decide) (by decide), h12₃'])
      hbp₄ (by rw [hg₄ .rbx (by decide) (by decide), hbx₃', Nat.add_zero]) (by rw [sl₄ 200 (by decide) (by decide), hdat]; simp) hl₄
      (by rw [sl₄ 192 (by decide) (by decide), htl, Nat.add_zero]))
      (headPart_keep v gf K enc I₄ hx h0 (by simp [hg₄ .r12 (by decide) (by decide), h12₃'])
      hbp₄ (by rw [hg₄ .rbx (by decide) (by decide), hbx₃', Nat.add_zero]) (by rw [sl₄ 200 (by decide) (by decide), hdat]; simp) hl₄
      (by rw [sl₄ 192 (by decide) (by decide), htl, Nat.add_zero]))) fun s₅ ⟨⟨I₅, sl₅⟩, k₅⟩ => ?_)
    obtain k₅' : Keep448 W s.mem s₅.mem := k₄.trans k₅
    generalize hk : headLen c₀.length n = k at hkn hk16 hkw I₅ hl₄ hJ ⊢
    -- Past the head.
    refine WP.seq (WP.mono (next_ok I₅.env (D := D) (P := c₀.length) hkn hlt (by rw [sl₅ 208 (by decide) (by decide), hl₄])
      (by rw [sl₅ 200 (by decide) (by decide), sl₄ 200 (by decide) (by decide), hdat])
      (by rw [sl₅ 192 (by decide) (by decide), sl₄ 192 (by decide) (by decide), htl])
      (by rw [sl₅ 216 (by decide) (by decide), ha₄])) fun s₆ ⟨g₆, d₆, t₆, l₆, f₆, hrd₆, hwr₆⟩ => ?_)
    obtain I₆ := I₅.slots K (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₆ _ (by decide) (by decide)) hrd₆ hwr₆ (Nat.le_refl _) (by decide) f₆
    rw [Nat.zero_add] at I₆
    obtain k₆ : Keep448 W s.mem s₆.mem := k₅'.trans (Keep448.of_frame f₆ (k448_slots L (by decide)))
    obtain a₆ : s₆.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n := by
      rw [f₆.readW (r := ⟨W + BitVec.ofNat 64 216, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.w_w (.inr (by decide)) (by decide) (by decide)) (by decide), sl₅ 216 (by decide) (by decide), ha₄]
    -- The whole blocks.
    refine WP.seq (WP.mono (wp_both (blocks_ok B K enc I₆ hx d₆ l₆ t₆ (fun hq => hkw.resolve_left (by omega_arith)))
      (blocks_leaves B K enc hL I₆ d₆ l₆ t₆)) fun s₇ ⟨⟨I₇, d₇, l₇, t₇⟩, a₇, c₇⟩ => ?_)
    obtain hq0 : ¬ (n - k) / 16 = 0 := by omega_using [hn, hkn, hk16]
    obtain hJ' : J = k + 16 * ((n - k) / 16) := by rw [← hJ]; simp [stJ, hn, hk]
    subst hJ'
    -- The rest.
    obtain ⟨s₈, run₈, h12₈, hbp₈, hbx₈, hg₈, hm₈, hrd₈, hwr₈⟩ := load_ok I₇.env d₇ l₇ t₇
    rw [toNat_mod16] at hbx₈
    obtain I₈ := I₇.regs (load_env hg₈) hm₈ hrd₈ hwr₈
    obtain e₈ : n - (k + 16 * ((n - k) / 16)) = (n - k) % 16 := by omega_arith
    exact WP.of_runBlock ⟨s₈, run₈, I₈, h12₈, by rw [hbp₈, e₈], hbx₈, by rw [hm₈]; exact d₇,
      by rw [hm₈, l₇, e₈], by rw [hm₈]; exact t₇, by rw [hm₈, a₇, a₆]; simp [hn],
      fun x hx => by rw [hm₈, c₇ x hx, ite_eq_right hq0, k₆ x hx]; simp [hn]⟩
  -- The rest.
  refine WP.mono (wp_both (part_ok v K enc I hx (j := J) (k := n - J) (by omega_arith) h12 hbp hbx hd' hl ht)
    (part_keep v gf cf K enc I hx (j := J) (k := n - J) (by omega_arith) h12 hbp hbx hd' hl ht))
    fun s'' ⟨⟨_, sl⟩, k''⟩ => ?_
  refine ⟨by rw [sl 192 (by decide) (by decide), ht], by rw [sl 200 (by decide) (by decide), hd'],
    by rw [sl 208 (by decide) (by decide), hl], by rw [sl 216 (by decide) (by decide), h216],
    fun x hx => by rw [k'' x hx, hw x hx]⟩

end

/-! ## The functions -/

/-- The word `j` that `stream_encrypt` and `stream_decrypt` leave in `W` (`a 1`)
up to byte 224, of their argument registers `g` and stack arguments `a`, if
they write it: the saved registers (16 to 21), `rounds` (22), `aad_len`
(23), the text so far and the address and length of the data kept past
`stJ` (24 to 26), and the whole length if they called the blocks function
(27). -/
def streamWord (g : Reg → BitVec 64) (a : Nat → BitVec 64) (j : Nat) : Option (BitVec 64) :=
  match j with
  | 16 => some (g .rbx)
  | 17 => some (g .rbp)
  | 18 => some (g .r12)
  | 19 => some (g .r13)
  | 20 => some (g .r14)
  | 21 => some (g .r15)
  | 22 => some (g .rsi)
  | 23 => some (g .rcx)
  | 24 => some (BitVec.ofNat 64 ((g .r8).toNat + stJ (g .r8).toNat (a 0).toNat))
  | 25 => some (g .r9 + BitVec.ofNat 64 (stJ (g .r8).toNat (a 0).toNat))
  | 26 => some (BitVec.ofNat 64 ((a 0).toNat - stJ (g .r8).toNat (a 0).toNat))
  | 27 => if (a 0).toNat < 256 then none else some (BitVec.ofNat 64 (a 0).toNat)
  | _ => none

/-- What `stream_encrypt` and `stream_decrypt` leave at `x` in `W` (`a 1`), of
their argument registers `g` and stack arguments `a`, with a blocks function
that leaves `Lb` in its `scratch`: up to byte 224 the bytes of `streamWord`,
from 448 those `Lb` says if there were 256 bytes, and elsewhere nothing
written (`none`). -/
def streamL (Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr →
      Option (BitVec 8)) (g : Reg → BitVec 64) (a : Nat → BitVec 64) (x : Addr) : Option (BitVec 8) :=
  if (x - a 1).toNat < 224 then
    (streamWord g a ((x - a 1).toNat / 8)).map fun w => w.extractLsb' (8 * ((x - a 1).toNat % 8)) 8
  else if (x - a 1).toNat < 448 ∨ (a 0).toNat < 256 then none
  else Lb (g .rdi) (BitVec.ofNat 64 (g .rsi).toNat) (g .rdx + BitVec.ofNat 64 48) (g .rdx + BitVec.ofNat 64 16)
    (g .r9 + BitVec.ofNat 64 (headLen (g .r8).toNat (a 0).toNat))
    (BitVec.ofNat 64 (((a 0).toNat - headLen (g .r8).toNat (a 0).toNat) / 16)) (a 1 + BitVec.ofNat 64 448) x

/-- `streamL`, from what is left: the words `streamWord` gives, the bytes
where it gives none and up to 448 as they were, and the blocks function's
`scratch`. -/
theorem streamL_of {Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr →
      Option (BitVec 8)} {g : Reg → BitVec 64} {a : Nat → BitVec 64} {m m' : Mem} {W : Addr} (hW : a 1 = W)
    (hw : ∀ j, 16 ≤ j → j < 28 → ∀ w, streamWord g a j = some w → m'.readW (W + BitVec.ofNat 64 (8 * j)) 64 = w)
    (hn : ∀ d, d < 2560 → (d < 224 → streamWord g a (d / 8) = none) →
      (224 ≤ d → d < 448 ∨ (a 0).toNat < 256) → m' (W + BitVec.ofNat 64 d) = m (W + BitVec.ofNat 64 d))
    (hb : ∀ d, 448 ≤ d → d < 2560 → ¬ (a 0).toNat < 256 →
      m' (W + BitVec.ofNat 64 d) = (Lb (g .rdi) (BitVec.ofNat 64 (g .rsi).toNat) (g .rdx + BitVec.ofNat 64 48)
        (g .rdx + BitVec.ofNat 64 16) (g .r9 + BitVec.ofNat 64 (headLen (g .r8).toNat (a 0).toNat))
        (BitVec.ofNat 64 (((a 0).toNat - headLen (g .r8).toNat (a 0).toNat) / 16)) (W + BitVec.ofNat 64 448)
        (W + BitVec.ofNat 64 d)).getD (m (W + BitVec.ofNat 64 d))) :
    ∀ x, (⟨W, 2560⟩ : Region).Contains x 1 → m' x = (streamL Lb g a x).getD (m x) := by
  intro x hx
  obtain hlt : (x - W).toNat < 2560 := by simp only [Region.Contains] at hx; omega_using [hx]
  generalize hd : (x - W).toNat = d at hlt
  obtain ex : x = W + BitVec.ofNat 64 d := by
    rw [← hd, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  subst ex
  simp only [streamL, hW, hd]
  by_cases h224 : d < 224
  · simp only [h224, ↓reduceIte]
    cases hj : streamWord g a (d / 8) with
    | none =>
      simp only [Option.map_none, Option.getD_none]
      exact hn d hlt (fun _ => hj) fun h => absurd h (by omega_arith)
    | some w =>
      simp only [Option.map_some, Option.getD_some]
      obtain h16 : 16 ≤ d / 8 := by
        refine Nat.le_of_not_lt fun h => ?_
        rcases (by omega_arith : d / 8 = 0 ∨ d / 8 = 1 ∨ d / 8 = 2 ∨ d / 8 = 3 ∨ d / 8 = 4 ∨ d / 8 = 5 ∨ d / 8 = 6 ∨
          d / 8 = 7 ∨ d / 8 = 8 ∨ d / 8 = 9 ∨ d / 8 = 10 ∨ d / 8 = 11 ∨ d / 8 = 12 ∨ d / 8 = 13 ∨ d / 8 = 14 ∨
          d / 8 = 15) with e | e | e | e | e | e | e | e | e | e | e | e | e | e | e | e <;>
          rw [e] at hj <;> simp [streamWord] at hj
      rw [← Offset.add_add_eq W (show 8 * (d / 8) + d % 8 = d by omega_arith),
        byte_readW64' m' (W + BitVec.ofNat 64 (8 * (d / 8))) (j := d % 8) (by omega_arith),
        hw (d / 8) h16 (by omega_arith) w hj]
  · simp only [h224, ↓reduceIte]
    by_cases h448 : d < 448 ∨ (a 0).toNat < 256
    · simp only [h448, ↓reduceIte, Option.getD_none]
      exact hn d hlt (fun h' => absurd h' h224) fun _ => h448
    · simp only [h448, ↓reduceIte]
      rw [not_or] at h448
      exact hb d (by omega_arith) hlt h448.2

/-- What `stream_encrypt`'s precondition says of `St`, `W` and the stack
arguments, beyond `CryptCtx`. -/
theorem streamCryptPre_more {cl : Nat} {s : State} (hp : Proof.AesGcm.streamCryptPre cl s) :
    (⟨s.gpr .rdx, 80⟩ : Region).Disjoint ⟨stackArg s 1, 2560⟩ ∧
      (⟨s.gpr .rdx, 80⟩ : Region).Disjoint ⟨s.gpr .rsp + BitVec.ofNat 64 8, 16⟩ ∧
      (⟨s.gpr .r9, (stackArg s 0).toNat⟩ : Region).Disjoint ⟨s.gpr .rsp + BitVec.ofNat 64 8, 16⟩ := by
  simp only [Proof.AesGcm.streamCryptPre, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.args,
    Proof.AesGcm.arg, Proof.AesGcm.rounds] at hp
  obtain ⟨-, -, -, -, -, -, d_sw, d_sa, -, d_da, -⟩ := hp
  obtain hA : stackArgAddr s 0 = s.gpr .rsp + BitVec.ofNat 64 8 := by simp [stackArgAddr]
  rw [hA] at d_sa d_da
  exact ⟨d_sw, d_sa, d_da⟩

open VG.Spec.Gcm (ctxH ctxCiph inc32) in
/-- One run of `stream_encrypt` (`enc`) or `stream_decrypt`, with callees that
never touch their working space and a blocks function that leaves `Lb` in
its `scratch`: it leaves `W` as `streamL` says, and its return address and
stack arguments as they were. -/
theorem streamS_leaves (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M)
    (gf : GhashFree v.gh.fn.code) (cf : Proof.Aes.X86_64.Ctr32Free v.ctr.callee) (enc : Bool)
    {Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr → Option (BitVec 8)}
    (hL : BlkLeft Lb (if enc then B.enc else B.dec).code M) {s : State}
    (hp : Proof.AesGcm.streamCryptPre M.len s) (hok : M.ok s.mem (s.gpr .rdi)) :
    WP isa (.seq (.block cryptEntry) (.seq (streamTextS (v.withBlk B) enc) (.block restore))) s fun s' =>
      (∀ x, (⟨stackArg s 1, 2560⟩ : Region).Contains x 1 →
        s'.mem x = (streamL Lb s.gpr (fun i => stackArg s i) x).getD (s.mem x)) ∧
      ∀ x, (⟨s.gpr .rsp, 24⟩ : Region).Contains x 1 → s'.mem x = s.mem x := by
  have C := CryptCtx.of hp M.ge
  have X := CtxExt.ofCrypt hp hok
  have hR := C.rounds
  obtain ⟨dSW, dSA, dDA⟩ := streamCryptPre_more hp
  have hP : (s.gpr .r8).toNat < 2 ^ 64 := (s.gpr .r8).isLt
  generalize hc₀ : List.replicate (s.gpr .r8).toNat (0 : Byte) = c₀
  obtain hT : (s.gpr .r8).toNat = c₀.length := by rw [← hc₀, List.length_replicate]
  rw [hT] at hP
  generalize hCtx : s.gpr .rdi = Ctx at *
  generalize hSt : s.gpr .rdx = St at *
  generalize hW : stackArg s 1 = W at *
  generalize hSP : s.gpr .rsp = SP at *
  generalize hD : s.gpr .r9 = D at *
  generalize hn : (stackArg s 0).toNat = n at *
  have L := C.lay
  generalize hR' : (s.gpr .rsi).toNat = R at *
  refine WP.seq (WP.mono (cryptEntry_ok hCtx hSt hD hSP hW hn C.perm C.ww C.args C.dA (by rw [hR']; exact hR))
    fun s₁ E => ?_)
  have hRo : RoundsAt s₁.mem W R := hR' ▸ E.rounds
  have dCE : ∀ r ∈ [entryR W], (⟨Ctx, 256⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact L.cw'.sub_right (Lay.wSub (by decide))
  have K : SCtx M Ctx St W SP R (blockAt s₁.mem (Ctx + BitVec.ofNat 64 240)) D n s₁.mem := ⟨L, hRo, rfl, C.t_c,
    C.t_s, C.t_w, C.t_d, C.sp24, X.w, X.cs, X.cw, X.cd, X.ct, M.frame E.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact X.cw.sub_right (Lay.wSub (by decide))) X.w X.ok⟩
  have htl : s₁.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 c₀.length := by
    rw [E.tlen, ← hT, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hal : s₁.mem.readW (W + BitVec.ofNat 64 184) 64 =
      BitVec.ofNat 64 (List.replicate (s.gpr .rcx).toNat (0 : Byte)).length := by
    rw [E.alen, List.length_replicate, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.seq (WP.mono (wp_both
    (streamTextS_ok v B K enc (Hyp := False) (icb := 0) E.env rfl (C.data.of_eq E.rd E.wr)
      (by rw [E.rd, E.wr]; exact X.cov) E.rbp hP hal htl E.dat E.len (fun h => h.elim) (fun h => h.elim))
    (streamTextS_leaves v gf cf B K enc (Hyp := False) (icb := 0) hL E.env rfl (C.data.of_eq E.rd E.wr)
      (by rw [E.rd, E.wr]; exact X.cov) E.rbp hP hal htl E.dat E.len (fun h => h.elim) (fun h => h.elim)))
    fun s₂ ⟨⟨he₂, _, _, f₂, _⟩, l192, l200, l208, l216, lW⟩ => ?_)
  have hsv₂ : SavedAt s₂.mem W s := E.saved.frame f₂ (w_stFrame L C.data.ok.w C.t_w (by decide) (by decide))
  have hret : s₂.mem.readW SP 64 = s.mem.readW SP 64 := by
    rw [ret_kept f₂ (ret_stFrame C.rS C.rD C.rW), ret_kept E.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact C.rW.sub_right (Lay.wSub (by decide)))]
  refine WP.mono (exit_ok he₂.r15 (by rw [he₂.rsp, hSP]) (covers_left he₂.perm.w) hsv₂ (by rw [hSP, hret]))
    fun s' ⟨_, hm, _⟩ => ⟨?_, ?_⟩
  · -- `W`.
    have fE : ∀ d, d < 128 ∨ 216 ≤ d → d < 2560 → s₁.mem (W + BitVec.ofNat 64 d) = s.mem (W + BitVec.ofNat 64 d) := by
      intro d h₁ h₂
      refine frame_at E.frame (fun r hr => ?_) (Region.contains_self _ _)
      simp only [List.mem_singleton] at hr; subst hr
      rcases h₁ with h₁ | h₁
      · exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
      · exact L.w_w (.inr (by omega_arith)) (by omega_arith) (by decide)
    have f2 : ∀ d, d < 192 ∨ (224 ≤ d ∧ d < 448) →
        s₂.mem (W + BitVec.ofNat 64 d) = s₁.mem (W + BitVec.ofNat 64 d) := by
      intro d h₁
      have hdl : d + 1 ≤ 2560 := by omega_arith
      refine frame_at f₂ (fun r hr => ?_) (Region.contains_self _ _)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ((dSW.sub_left (Lay.stSub (by decide))).sub_right (Lay.wSub hdl)).symm
      · exact (C.dE.sub_right (Lay.wSub hdl)).symm
      · simp only [tReg, Bool.false_eq_true, ↓reduceIte]; exact Lay.disj_empty
      · rcases h₁ with h₁ | h₁
        · exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
        · exact L.w_w (.inr (by omega_arith)) (by omega_arith) (by decide)
      · exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
      · exact (C.t_w.sub_right (Lay.wSub hdl)).symm
    have rW : ∀ d, 128 ≤ d → d + 8 ≤ 192 →
        s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ =>
      f₂.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
        (w_stFrame L C.data.ok.w C.t_w h₁ h₂) (by decide)
    refine streamL_of (W := W) (m := s.mem) (m' := s'.mem) hW (fun j h₁ h₂ w hj => ?_) (fun d hd h224 h448 => ?_)
      (fun d h₁ hd hnot => ?_)
    · rw [hm]
      rcases (by omega_arith : j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨ j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
        j = 25 ∨ j = 26 ∨ j = 27) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · obtain rfl := Option.some.inj hj; exact hsv₂ (.rbx, 128) (by simp [saved])
      · obtain rfl := Option.some.inj hj; exact hsv₂ (.rbp, 136) (by simp [saved])
      · obtain rfl := Option.some.inj hj; exact hsv₂ (.r12, 144) (by simp [saved])
      · obtain rfl := Option.some.inj hj; exact hsv₂ (.r13, 152) (by simp [saved])
      · obtain rfl := Option.some.inj hj; exact hsv₂ (.r14, 160) (by simp [saved])
      · obtain rfl := Option.some.inj hj; exact hsv₂ (.r15, 168) (by simp [saved])
      · obtain rfl := Option.some.inj hj
        rw [show 8 * 22 = 176 from rfl, rW 176 (by decide) (by decide), hRo.1, ← hR', BitVec.ofNat_toNat,
          BitVec.setWidth_eq]
      · obtain rfl := Option.some.inj hj
        rw [show 8 * 23 = 184 from rfl, rW 184 (by decide) (by decide), E.alen]
      · simp only [streamWord, hT, hn] at hj
        obtain rfl := Option.some.inj hj; exact l192
      · simp only [streamWord, hT, hn, hD] at hj
        obtain rfl := Option.some.inj hj; exact l200
      · simp only [streamWord, hT, hn] at hj
        obtain rfl := Option.some.inj hj; exact l208
      · simp only [streamWord, hn] at hj
        by_cases h256 : n < 256
        · simp [h256] at hj
        · simp only [h256, ↓reduceIte, Option.some.injEq] at hj
          subst hj
          rw [show 8 * 27 = 216 from rfl, l216]; simp [h256]
    · rw [hm]
      by_cases h128 : d < 128
      · rw [f2 d (.inl (by omega_arith)), fE d (.inl h128) hd]
      by_cases h2 : d < 224
      · -- Only the whole length, if no blocks: as on entry.
        obtain hw := h224 h2
        obtain ⟨h27, h256⟩ : d / 8 = 27 ∧ n < 256 := by
          rcases (by omega_arith : d / 8 = 16 ∨ d / 8 = 17 ∨ d / 8 = 18 ∨ d / 8 = 19 ∨ d / 8 = 20 ∨ d / 8 = 21 ∨
            d / 8 = 22 ∨ d / 8 = 23 ∨ d / 8 = 24 ∨ d / 8 = 25 ∨ d / 8 = 26 ∨ d / 8 = 27) with
            e | e | e | e | e | e | e | e | e | e | e | e <;> rw [e] at hw <;> simp [streamWord, hn] at hw
          exact ⟨e, hw⟩
        obtain ed : W + BitVec.ofNat 64 d = W + BitVec.ofNat 64 216 + BitVec.ofNat 64 (d % 8) :=
          (Offset.add_add_eq W (show 216 + d % 8 = d by omega_arith)).symm
        rw [ed, byte_readW64' s₂.mem (W + BitVec.ofNat 64 216) (j := d % 8) (by omega_arith), l216]
        simp only [h256, ↓reduceIte]
        rw [← byte_readW64' s₁.mem (W + BitVec.ofNat 64 216) (j := d % 8) (by omega_arith), ← ed]
        exact fE d (.inr (by omega_arith)) hd
      · rcases h448 (by omega_arith) with h | h
        · rw [f2 d (.inr ⟨by omega_arith, h⟩), fE d (.inr (by omega_arith)) hd]
        · by_cases h4 : d < 448
          · rw [f2 d (.inr ⟨by omega_arith, h4⟩), fE d (.inr (by omega_arith)) hd]
          · rw [hn] at h
            rw [lW _ (Offset.contains _ (by omega_arith) (by omega_arith) (by decide))]
            simp only [h, ↓reduceIte, Option.getD_none]
            exact fE d (.inr (by omega_arith)) hd
    · rw [hn] at hnot
      rw [hm, lW _ (Offset.contains _ h₁ (by omega_arith) (by decide))]
      simp only [hnot, ↓reduceIte, hCtx, hR', hSt, hD, hT, hn]
      rw [fE d (.inr (by omega_arith)) hd]
  · -- The return address and the stack arguments.
    intro x hx
    rw [hm]
    have hsplit : (⟨SP, 8⟩ : Region).Contains x 1 ∨ (⟨SP + BitVec.ofNat 64 8, 16⟩ : Region).Contains x 1 := by
      by_cases h8 : (x - SP).toNat < 8
      · exact .inl (by simp only [Region.Contains] at hx ⊢; omega_using [h8])
      · refine .inr ?_
        have := (Offset.lt_iff x SP (d := 8) (n := 16) (by decide)).2
          ⟨by omega_arith, by simp only [Region.Contains] at hx; omega_using [hx]⟩
        simp only [Region.Contains]; omega_using [this]
    rcases hsplit with h | h
    · rw [frame_at f₂ (ret_stFrame C.rS C.rD C.rW) h, frame_at E.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact C.rW.sub_right (Lay.wSub (by decide))) h]
    · refine (frame_at f₂ (fun r hr => ?_) h).trans (frame_at E.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact C.dA.sub_right (Lay.wSub (by decide))) h)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact (dSA.sub_left (Lay.stSub (by decide))).symm
      · exact dDA.symm
      · simp only [tReg, Bool.false_eq_true, ↓reduceIte]; exact Lay.disj_empty
      · exact C.dA.sub_right (Lay.wSub (by decide))
      · exact C.dA.sub_right (Lay.wSub (by decide))
      · exact Offset.disjoint_below SP (n := 24) (d := 8) (k := 16) (by decide)


end VG.Proof.AesGcm.X86_64
