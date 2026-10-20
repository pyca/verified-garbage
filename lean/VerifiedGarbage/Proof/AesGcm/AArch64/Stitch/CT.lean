module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Seal
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.CT
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Pre
import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Ok
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Seal
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Entry
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Pad
import VerifiedGarbage.Proof.AesGcm.AArch64.PieceCT
import VerifiedGarbage.Proof.AesGcm.AArch64.Rel
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Seal
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.CT
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Pre
meta import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Ok
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Seal
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Entry
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Pad
meta import VerifiedGarbage.Proof.AesGcm.AArch64.PieceCT
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Rel
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# AES-GCM on AArch64, interleaved: `sealWithS` is constant time

Untrusted: everything here is checked by Lean. As `Fast/CT.lean` does for
`runWithP`: `front` and the code between the calls by the taint analysis, the
calls by `cryptAl_rel`, the hash's call and `rel_ctr`, with the interleaved
loop and its table (`stitched_rel`, for a `tb` that leaks the same in two runs)
in between; the correctness lemmas give both runs' states.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64.Fast

open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Taint VG.Impl.AesGcm.AArch64
open VG.Proof.AesGcm.AArch64
open VG.Proof.Gcm.AArch64.Pmull
open VG.Impl.Gcm.AArch64.Pmull (LO MID HI A T C Y tReg sReg poly)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)
open VG.Proof.Gcm.AArch64.Stitch (Gh8Ok)

/-- The registers of the interleaved loop's arguments. -/
abbrev stRegs : List Reg := [.x9, .x19, .x20, .x21, .x22, .x23, .x26]

/-- `stitched [] tb k` in two runs that agree on the arguments, given `tb`
then `k` in two runs that agree on them and on `x9`, from states that differ
from the runs' only in `x9`. -/
theorem stitched_rel {tb : List Instr} {k : Prog isa} {u₁ u₂ : State} {n : Nat} (hsp : u₁.sp = u₂.sp)
    (hr : ∀ r ∈ stRegs, r ≠ .x9 → u₁.gpr r = u₂.gpr r)
    (h26₁ : u₁.gpr .x26 = BitVec.ofNat 64 n) (hn : n < 2 ^ 64)
    (hk : ∀ v₁ v₂ : State, v₁.sp = v₂.sp → (∀ r ∈ stRegs, v₁.gpr r = v₂.gpr r) →
      (∀ r, r ≠ .x9 → v₁.gpr r = u₁.gpr r) → v₁.mem = u₁.mem → v₁.rd = u₁.rd → v₁.wr = u₁.wr →
      v₁.sp = u₁.sp →
      (∀ r, r ≠ .x9 → v₂.gpr r = u₂.gpr r) → v₂.mem = u₂.mem → v₂.rd = u₂.rd → v₂.wr = u₂.wr →
      v₂.sp = u₂.sp →
      RelCT isa (Eq2 v₁ v₂) (.seq (.block tb) k) TT) :
    RelCT isa (Eq2 u₁ u₂) (Impl.AesGcm.AArch64.Stitch.stitched [] tb k) TT := by
  have h26₂ : u₂.gpr .x26 = BitVec.ofNat 64 n := by rw [← hr .x26 (by simp) (by decide), h26₁]
  unfold Impl.AesGcm.AArch64.Stitch.stitched
  refine rel_seq (rel_taint [.x26] hsp (by agree_tac [h26₁, h26₂]) ⟨_, by taint_decide⟩)
    (F₁ := fun v => v = u₁.write .x .x9 (u₁.read .x .x26 >>> 7))
    (F₂ := fun v => v = u₂.write .x .x9 (u₂.read .x .x26 >>> 7))
    (WP.block_cons_iff.mpr ⟨_, exec_lsr_x (sh := 7) (by decide), WP.block_nil rfl⟩)
    (WP.block_cons_iff.mpr ⟨_, exec_lsr_x (sh := 7) (by decide), WP.block_nil rfl⟩) fun v₁ v₂ e₁ e₂ => ?_
  subst e₁ e₂
  have e9 : ∀ {u : State}, u.gpr .x26 = BitVec.ofNat 64 n →
      (u.write .x .x9 (u.read .x .x26 >>> 7)).gpr .x9 = BitVec.ofNat 64 (n / 128) := fun h => by
    rw [RegUpd.gpr_write_self]
    simp only [State.read, BitVec.setWidth_eq, Size.bits, h]
    exact Gcm.AArch64.Stitch.ushr7 hn
  refine rel_ite (Proof.Aes.AArch64.Aese.eval_zero (e9 h26₁) (by omega))
    (Proof.Aes.AArch64.Aese.eval_zero (e9 h26₂) (by omega))
    (fun _ => by exact rel_taint [] (by simp only [RegUpd.sp_write, hsp]) (by agree_tac []) ⟨_, by taint_decide⟩)
    fun _ => ?_
  rw [List.nil_append]
  refine hk _ _ (by simp only [RegUpd.sp_write, hsp]) (fun r hr' => ?_) (fun r h => RegUpd.gpr_write_of_ne _ _ _ h)
    (RegUpd.mem_write _ _ _ _) (RegUpd.rd_write _ _ _ _) (RegUpd.wr_write _ _ _ _) (RegUpd.sp_write _ _ _ _)
    (fun r h => RegUpd.gpr_write_of_ne _ _ _ h) (RegUpd.mem_write _ _ _ _) (RegUpd.rd_write _ _ _ _) (RegUpd.wr_write _ _ _ _)
    (RegUpd.sp_write _ _ _ _)
  by_cases h9 : r = .x9
  · subst h9; rw [e9 h26₁, e9 h26₂]
  · rw [RegUpd.gpr_write_of_ne _ _ _ h9, RegUpd.gpr_write_of_ne _ _ _ h9]; exact hr r hr' h9

/-- `powTbl` then the encryption, in two runs that agree on the arguments. -/
theorem powTblEnc_rel {v₁ v₂ : State} (hsp : v₁.sp = v₂.sp) (hr : ∀ r ∈ stRegs, v₁.gpr r = v₂.gpr r) :
    RelCT isa (Eq2 v₁ v₂) (.seq (.block Impl.AesGcm.AArch64.Stitch.powTbl) Impl.Gcm.AArch64.Stitch.enc) TT :=
  rel_taint stRegs hsp hr ⟨_, by taint_decide⟩

section
variable {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W)
include L

/-- `Mid` after `cryptAl` on part `⟨D₂, n₂⟩` of the text. -/
theorem Mid.cryptS {H : Block} {R n n₂ P : Nat} {D D₂ Tg X : Addr} {ρ s s' : State} {icb : Block}
    (h : Mid Ctx W SP H R n D Tg X ρ s) (hsub : Region.Sub ⟨D₂, n₂⟩ ⟨D, n⟩)
    (hd : DataW Ctx (W + BitVec.ofNat 64 16) W s D₂ n₂)
    (o : CrOut Ctx (W + BitVec.ofNat 64 16) W SP s.gpr R icb P D₂ n₂ s.mem s')
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Mid Ctx W SP H R n D Tg X ρ s' := by
  have dWK : ∀ r ∈ crFrame (W + BitVec.ofNat 64 16) W D₂ n₂, (keyR W).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hd.ok.w.sub_right (Lay.wSub (by decide))).symm
    · exact (L.st_w (a := 48) (n := 32) (by decide) (.inr ⟨by decide, by decide⟩)).symm
    · exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)
  refine ⟨o.env, by rw [o.kept .x22 (by decide), h.x22], h.rounds, by rw [o.kept .x26 (by decide), h.x26],
    by rw [o.kept .x27 (by decide), h.x27], by rw [o.kept .x28 (by decide), h.x28],
    by rw [hH_crFrame L hd o.frame, h.hH], h.key.frame o.frame dWK, h.data.of_eq hrd hwr,
    h.fr.trans (o.frame.sub fun r hr => ?_), hrd.trans h.rd, hwr.trans h.wr⟩
  simp only [crFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), hsub⟩
  · exact ⟨_, List.mem_cons_self .., stW (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩

/-- `Mid.absorbX`, for the whole blocks of part `⟨D₂, n₂⟩` of the text. -/
theorem Mid.absorbXS {H : Block} {R n n₂ : Nat} {D D₂ Tg X : Addr} {ρ s s' : State} {x : List Byte} {j : Nat}
    {ex : List Region} (h : Mid Ctx W SP H R n D Tg X ρ s)
    (o : AbsMid Ctx (W + BitVec.ofNat 64 16) W SP s.gpr 16 H x D₂ n₂ 0 s.mem j s' ex)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hexK : ∀ r ∈ ex, (keyR W).Disjoint r) :
    Mid Ctx W SP H R n D Tg X s' s' := by
  refine ⟨o.env, by rw [o.kept .x22 (by decide), h.x22], h.rounds, by rw [o.kept .x26 (by decide), h.x26],
    by rw [o.kept .x27 (by decide), h.x27], by rw [o.kept .x28 (by decide), h.x28], o.hH,
    h.key.frame o.frame fun r hr => ?_, h.data.of_eq hrd hwr, Frame.refl _ _, rfl, rfl⟩
  simp only [List.mem_cons] at hr
  rcases hr with rfl | rfl | rfl | hr
  · exact (L.st_w (a := 16) (n := 16) (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact (L.st_w (a := 32) (n := 16) (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)
  · exact hexK r hr

/-- `ctE_ok`, for the whole blocks of part `⟨D₂, n₂⟩` of the text. -/
theorem ctE'_ok (hMK : MulKey) {o : Nat} (ho : o = 0 ∨ o = 112) {H : Block} {R n n₂ : Nat} {D D₂ Tg X : Addr}
    {ρ s₄ s₇ : State} {x : List Byte} {j : Nat} {ex : List Region}
    (h : Mid Ctx W SP H R n D Tg X ρ s₇)
    (hm : AbsMid Ctx (W + BitVec.ofNat 64 16) W SP s₄.gpr 16 H x D₂ n₂ 0 s₄.mem j s₇ ex)
    (hlt : n₂ - j < 16) :
    WP isa (.seq (.block (Impl.AesGcm.AArch64.Fast.hReload ++ Impl.Gcm.AArch64.Pmull.loadRev Y .x20 16 ++
        [mov .x13 .x24, mov .x12 .x23])) (.seq Impl.AesGcm.AArch64.Fast.padMul (.block (Impl.AesGcm.AArch64.Fast.lensTagAt o)))) s₇
      fun s => ∃ k Yv J m, Tag1 Ctx (W + BitVec.ofNat 64 16) W SP k o R Yv J m s ∧ k .x28 = Tg := by
  have he₇ := h.env
  have hjn := hm.le
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (reload_ok (H := H) (by rw [he₇.x19]; exact he₇.perm.wR (by decide))
    (by rw [he₇.x19]; exact he₇.perm.wR (by decide)) (by rw [he₇.x19]) (by rw [he₇.x19]; exact h.key.2)
    h.key.1) fun s₈ ⟨hk₈, g₈, v₈, m₈, rd₈, wr₈, sp₈⟩ => ?_
  have he₈ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₈ := he₇.keep (fun r hr => g₈ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₈ rd₈ wr₈
  refine WP.mono (loadRev_ok Y .x20 16 s₈ (by decide) (by decide) (by rw [he₈.x20]; exact he₈.perm.stR (by decide)))
    fun s₉ ⟨l₉, o₉⟩ => ?_
  have he₉ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₉ := he₈.keep (fun r _ => by rw [o₉.gpr]) o₉.sp o₉.rd o₉.wr
  obtain ⟨s₁₀, run₁₀, x13₁₀, x12₁₀, r₁₀, v₁₀⟩ : ∃ s₁₀, runBlock isa [mov .x13 .x24, mov .x12 .x23] s₉ = some s₁₀ ∧
      s₁₀.gpr .x13 = BitVec.ofNat 64 (n₂ - j) ∧ s₁₀.gpr .x12 = D₂ + BitVec.ofNat 64 j ∧
      Regs [.x13, .x12] s₉ s₁₀ ∧ s₁₀.v = s₉.v := by
    refine ⟨_, by arun [], ?_⟩
    refine ⟨?_, ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩, rfl⟩
    · simp [gpr_write, o₉.gpr, g₈ .x24 (by decide), hm.x24]
    · simp [gpr_write, o₉.gpr, g₈ .x23 (by decide), hm.x23]
  refine WP.of_runBlock ⟨s₁₀, run₁₀, ?_⟩
  have he₁₀ := he₉.of_regs r₁₀
  have hk₁₀ : HKey H s₁₀ :=
    hk₈.of_v (by rw [v₁₀, o₉.v C (by decide)]) (by rw [v₁₀, o₉.v _ (by decide)]) (by rw [v₁₀, o₉.v _ (by decide)])
  have hdj : DataOk (W + BitVec.ofNat 64 16) W s₁₀ (D₂ + BitVec.ofNat 64 j) (n₂ - j) :=
    (hm.data.drop hjn).of_eq (by rw [r₁₀.rd, o₉.rd, rd₈]) (by rw [r₁₀.wr, o₉.wr, wr₈])
  refine WP.seq (WP.mono (WP.with_rdwr (padMul_ok hMK (y := blockAt s₈.mem (s₈.gpr .x20 + BitVec.ofNat 64 16)) he₁₀ hk₁₀
    (by rw [v₁₀, l₉, rev64b_read]) x12₁₀ x13₁₀ (by omega) hdj.rd
    (hdj.w.sub_right (Lay.wSub (by decide))))) fun s₁₁ ⟨⟨y₁₁, hk₁₁, he₁₁, og₁₁, f₁₁, v₁₁⟩, rd₁₁, wr₁₁⟩ => ?_)
  unfold Impl.AesGcm.AArch64.Fast.lensTagAt
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  have w₁ := he₁₁.perm.wW (show 96 + 8 ≤ 2560 by decide)
  have w₂ := he₁₁.perm.wW (show 104 + 8 ≤ 2560 by decide)
  have q₁ := he₁₁.perm.wR (show 224 + 8 ≤ 2560 by decide)
  obtain ⟨s₁₂, run₁₂, og₁₂, sp₁₂, rd₁₂, wr₁₂, v₁₂⟩ : ∃ s₁₂, runBlock isa
      [.ldr .x .x10 .x19 alenO, .lsl .x .x9 .x10 3, .rev .x9 .x9, .str .x .x9 .x19 tO, .lsl .x .x9 .x26 3,
        .rev .x9 .x9, .str .x .x9 .x19 (tO + 8)] s₁₁ = some s₁₂ ∧
      Others [.x9, .x10] s₁₁ s₁₂ ∧ s₁₂.sp = s₁₁.sp ∧ s₁₂.rd = s₁₁.rd ∧ s₁₂.wr = s₁₁.wr ∧ s₁₂.v = s₁₁.v := by
    refine ⟨_, by arun [he₁₁.x19, q₁, w₁, w₂], ?_⟩
    exact ⟨by others_tac, rfl, rfl, rfl, rfl⟩
  refine WP.of_runBlock ⟨s₁₂, run₁₂, ?_⟩
  have he₁₂ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁₂ := he₁₁.keep (fun r hr => og₁₂ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₁₂ rd₁₂ wr₁₂
  have hk₁₂ : HKey H s₁₂ := hk₁₁.of_v (by rw [v₁₂]) (by rw [v₁₂]) (by rw [v₁₂])
  rw [WP.block_append_iff]
  refine WP.mono (mulT_ok hMK (y := padStep H (blockAt s₈.mem (s₈.gpr .x20 + BitVec.ofNat 64 16))
      (bytesAt s₁₀.mem (D₂ + BitVec.ofNat 64 j) (n₂ - j))) hk₁₂ (by rw [v₁₂]; exact y₁₁)
      (by rw [he₁₂.x19]; exact he₁₂.perm.wR (by decide)))
    fun s₁₃ ⟨y₁₃, _, o₁₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (storeY_ok y₁₃ (by rw [o₁₃.gpr, o₁₃.wr, he₁₂.x20]; exact he₁₂.perm.stW (by decide)))
    fun s₁₄ ⟨_, _, o₁₄⟩ => ?_
  have g₁₄ : s₁₄.gpr = s₁₂.gpr := by rw [o₁₄.gpr]; exact o₁₃.gpr
  have he₁₄ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁₄ :=
    he₁₂.keep (fun r _ => by rw [g₁₄]) (by rw [o₁₄.sp, o₁₃.sp]) (by rw [o₁₄.rd, o₁₃.rd]) (by rw [o₁₄.wr, o₁₃.wr])
  have x22₁₄ : s₁₄.gpr .x22 = BitVec.ofNat 64 R := by
    rw [g₁₄, og₁₂ _ (by decide), og₁₁ _ (by decide), r₁₀.others _ (by decide), o₉.gpr, g₈ _ (by decide), h.x22]
  have x28₁₄ : s₁₄.gpr .x28 = Tg := by
    rw [g₁₄, og₁₂ _ (by decide), og₁₁ _ (by decide), r₁₀.others _ (by decide), o₉.gpr, g₈ _ (by decide), h.x28]
  exact WP.mono (tagSeg_ok L (o := o) ho he₁₄ (fun _ _ => rfl : Kept s₁₄.gpr s₁₄) x22₁₄ h.rounds)
    fun s' h' => ⟨_, _, _, _, h', x28₁₄⟩

omit L in
/-- The front's frame is in the working space. -/
theorem frontFrame'_work (W : Addr) :
    ∀ r ∈ frontFrame' (W + BitVec.ofNat 64 16) W, Region.Sub r (workR W) := by
  intro r hr
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl) | rfl <;> exact Lay.wSub (by decide)

omit L in
/-- After `front`: what the interleaved loop needs, from `FFront`. -/
theorem stIn_of {H : Block} {iv a : List Byte} {R n : Nat} {D : Addr} {ρ σ s₂ : State} {tb : List Instr}
    (h₂ : FFront Ctx (W + BitVec.ofNat 64 16) W SP H iv a D n σ s₂)
    (hd : DataW Ctx (W + BitVec.ofNat 64 16) W σ D n) (h22 : σ.gpr .x22 = BitVec.ofNat 64 R)
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hf : Frame [workR W, ⟨D, n⟩] ρ.mem σ.mem) (hrd : σ.rd = ρ.rd)
    (hwr : σ.wr = ρ.wr)
    (htb : ∀ u : State, Env Ctx (W + BitVec.ofNat 64 16) W SP u → u.rd = ρ.rd → u.wr = ρ.wr →
      Frame [workR W, ⟨D, n⟩] ρ.mem u.mem → KeyAt H u.mem W → WP isa (.block tb) u (Stitch.TblPost W H u)) :
    Stitch.SIn Ctx (W + BitVec.ofNat 64 16) W SP H (a ++ Spec.Gcm.zeros (Spec.Gcm.padLen a.length))
      (Spec.Gcm.inc32 (Spec.Gcm.j0 H iv)) R D n s₂ ∧ Stitch.TbOk Ctx (W + BitVec.ofNat 64 16) W SP H tb s₂ ∧
      Frame [workR W, ⟨D, n⟩] ρ.mem s₂.mem := by
  have F₂ : Frame [workR W, ⟨D, n⟩] ρ.mem s₂.mem :=
    hf.trans (h₂.frame.sub fun r hr => ⟨_, List.mem_cons_self .., frontFrame'_work W r hr⟩)
  refine ⟨⟨h₂.env, by rw [h₂.x22, h22], hR, h₂.x23, h₂.x26, hd.of_eq (by rw [h₂.rd]) (by rw [h₂.wr]), h₂.hH,
    h₂.cb, h₂.y, ?_⟩, fun u he hm hrd' hwr' _ => htb u he (by rw [hrd', h₂.rd, hrd]) (by rw [hwr', h₂.wr, hwr])
    (by rw [hm]; exact F₂) (by rw [hm]; exact h₂.key), F₂⟩
  rw [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _

/-- After the interleaved loop and the pointers of the rest: `Mid`, and the
arguments of `cryptAl` on the rest. -/
theorem stOut_of {H : Block} {iv a : List Byte} {R n : Nat} {D Tg : Addr} {ρ σ s₂ s₃ s₄ : State}
    {c : Mem → List Byte}
    (h₂ : FFront Ctx (W + BitVec.ofNat 64 16) W SP H iv a D n σ s₂)
    (hd : DataW Ctx (W + BitVec.ofNat 64 16) W σ D n) (h22 : σ.gpr .x22 = BitVec.ofNat 64 R)
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (h28 : σ.gpr .x28 = Tg) (F₂ : Frame [workR W, ⟨D, n⟩] ρ.mem s₂.mem)
    (hrd : σ.rd = ρ.rd) (hwr : σ.wr = ρ.wr)
    (hm : Stitch.SMid Ctx (W + BitVec.ofNat 64 16) W SP H (a ++ Spec.Gcm.zeros (Spec.Gcm.padLen a.length))
      (Spec.Gcm.inc32 (Spec.Gcm.j0 H iv)) R D n c s₂ s₃)
    (x23 : s₄.gpr .x23 = D + BitVec.ofNat 64 (Stitch.pre n))
    (x27 : s₄.gpr .x27 = D + BitVec.ofNat 64 (Stitch.pre n))
    (x24 : s₄.gpr .x24 = BitVec.ofNat 64 (n - Stitch.pre n))
    (x25 : s₄.gpr .x25 = BitVec.ofNat 64 (Stitch.pre n % 16))
    (r₄ : Regs [.x9, .x23, .x27, .x24, .x25] s₃ s₄) :
    Mid Ctx W SP H R n D Tg (D + BitVec.ofNat 64 (Stitch.pre n)) ρ s₄ ∧
      CrIn Ctx (W + BitVec.ofNat 64 16) W SP s₄.gpr R (Stitch.pre n) (D + BitVec.ofNat 64 (Stitch.pre n))
        (n - Stitch.pre n) s₄ := by
  have hpn : Stitch.pre n ≤ n := Nat.mul_div_le n 128
  have subP : Region.Sub ⟨D, Stitch.pre n⟩ ⟨D, n⟩ := Region.sub_prefix hpn
  have hd₄ : DataW Ctx (W + BitVec.ofNat 64 16) W s₄ D n :=
    hd.of_eq (by rw [r₄.rd, hm.rd, h₂.rd]) (by rw [r₄.wr, hm.wr, h₂.wr])
  have he₄ := hm.env.of_regs r₄
  have g : ∀ r ∈ [Reg.x22, .x26, .x28], s₄.gpr r = s₂.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact (r₄.others _ (by decide)).trans (hm.gpr _ (by decide))
  have hH₄ : blockAt s₄.mem (Ctx + BitVec.ofNat 64 240) = H := by
    rw [r₄.mem, blockAt_frame hm.frame fun r hr => ?_, h₂.hH]
    simp only [Stitch.sFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (L.cs.sub_left (Lay.ctxSub (by decide))).sub_right (Lay.stSub (by decide))
    · exact (L.cs.sub_left (Lay.ctxSub (by decide))).sub_right (Lay.stSub (by decide))
    · exact (hd.ctx.sub_left (Lay.ctxSub (by decide))).sub_right subP
    · exact (L.cw'.sub_left (Lay.ctxSub (by decide))).sub_right (Lay.wSub (by decide))
  have key₄ : KeyAt H s₄.mem W := by
    rw [r₄.mem]
    refine h₂.key.frame hm.frame fun r hr => ?_
    simp only [Stitch.sFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (L.st_w (a := 16) (n := 16) (by decide) (.inr ⟨by decide, by decide⟩)).symm
    · exact (L.st_w (a := 48) (n := 16) (by decide) (.inr ⟨by decide, by decide⟩)).symm
    · exact ((hd.ok.w.sub_left subP).sub_right (Lay.wSub (by decide))).symm
    · exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)
  have F₄ : Frame [workR W, ⟨D, n⟩] ρ.mem s₄.mem := by
    rw [r₄.mem]
    refine F₂.trans (hm.frame.sub fun r hr => ?_)
    simp only [Stitch.sFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., stW (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., stW (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), subP⟩
    · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
  have x22₄ : s₄.gpr .x22 = BitVec.ofNat 64 R := by rw [g _ (by simp), h₂.x22, h22]
  exact ⟨⟨he₄, x22₄, hR, by rw [g _ (by simp), h₂.x26], x27, by rw [g _ (by simp), h₂.x28, h28], hH₄, key₄, hd₄,
    F₄, by rw [r₄.rd, hm.rd, h₂.rd, hrd], by rw [r₄.wr, hm.wr, h₂.wr, hwr]⟩,
    ⟨he₄, fun _ _ => rfl, x22₄, hR, x23, x24, x25, hd₄.drop hpn⟩⟩

/-- The arguments of the call on the whole blocks of the rest of the ciphertext. -/
theorem ctCS_ok {H : Block} {R n : Nat} {D Tg : Addr} {ρ s₄ : State}
    (h : Mid Ctx W SP H R n D Tg (D + BitVec.ofNat 64 (Stitch.pre n)) ρ s₄)
    (h25 : s₄.gpr .x25 = BitVec.ofNat 64 0) :
    WP isa (.block (([mov .x23 .x27] : List Instr) ++ Impl.AesGcm.AArch64.Stitch.whole ++ ([.sub .x .x24 .x26 .x9] : List Instr) ++ absSeg2 16)) s₄
      (Abs3 Ctx (W + BitVec.ofNat 64 16) W SP s₄.gpr 16 H [] (D + BitVec.ofNat 64 (Stitch.pre n)) (n - Stitch.pre n)
        0 s₄.mem 0) := by
  have hn := h.data.ok.lt
  have hpn : Stitch.pre n ≤ n := Nat.mul_div_le n 128
  rw [WP.block_append_iff]
  obtain ⟨s₅, run₅, x23₅, x24₅, r₅⟩ := Stitch.absArgsE_ok h.x27 h.x26 hn
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  have hM : AbsMid Ctx (W + BitVec.ofNat 64 16) W SP s₄.gpr 16 H [] (D + BitVec.ofNat 64 (Stitch.pre n))
      (n - Stitch.pre n) 0 s₄.mem 0 s₅ :=
    ⟨h.env.of_regs r₅, fun r hr => r₅.others r (by
        simp only [keptRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> decide), Nat.zero_le _, by rw [x23₅]; simp,
      by rw [x24₅, Nat.sub_zero], by rw [r₅.others _ (by decide), h25],
      (h.data.ok.drop hpn).of_eq r₅.rd r₅.wr, by rw [r₅.mem]; exact h.hH,
      fun ha => by rw [r₅.mem]; simpa [bytesAt] using ha, .inr rfl, by rw [r₅.mem]; exact Frame.refl _ _⟩
  exact absSeg2_ok L (.inr rfl) hM

/-- `front`, the interleaved loop and the pointers of the rest: `Mid`, and
the arguments of `cryptAl` on the rest. -/
theorem ctAS_ok (hMK : MulKey) (gh : Gh8Ok) {tb : List Instr} {k : Reg → BitVec 64} {H : Block}
    {Np A D Tg : Addr} {al n R : Nat} {ρ s₁ : State}
    (hJ : J0In Ctx (W + BitVec.ofNat 64 16) W SP k H Np 12 s₁) (haad : DataOk (W + BitVec.ofNat 64 16) W s₁ A al)
    (hal : al ≤ 16) (h4 : s₁.gpr .x4 = A) (h5 : s₁.gpr .x5 = BitVec.ofNat 64 al) (h6 : s₁.gpr .x6 = D)
    (h7 : s₁.gpr .x7 = BitVec.ofNat 64 n) (hdat : DataW Ctx (W + BitVec.ofNat 64 16) W s₁ D n)
    (h22 : s₁.gpr .x22 = BitVec.ofNat 64 R) (hR : R = 10 ∨ R = 12 ∨ R = 14) (h28 : s₁.gpr .x28 = Tg)
    (hf : Frame [workR W, ⟨D, n⟩] ρ.mem s₁.mem) (hrd : s₁.rd = ρ.rd) (hwr : s₁.wr = ρ.wr)
    (htb : ∀ u : State, Env Ctx (W + BitVec.ofNat 64 16) W SP u → u.rd = ρ.rd → u.wr = ρ.wr →
      Frame [workR W, ⟨D, n⟩] ρ.mem u.mem → KeyAt H u.mem W → WP isa (.block tb) u (Stitch.TblPost W H u)) :
    WP isa (.seq Impl.AesGcm.AArch64.Fast.front (.seq (Impl.AesGcm.AArch64.Stitch.stitched [] tb
        Impl.Gcm.AArch64.Stitch.enc) (.block (Impl.AesGcm.AArch64.Stitch.whole ++
        ([.add .x .x23 .x23 .x9, mov .x27 .x23, .sub .x .x24 .x26 .x9, imm .x25 0] : List Instr))))) s₁
      fun s₄ => Mid Ctx W SP H R n D Tg (D + BitVec.ofNat 64 (Stitch.pre n)) ρ s₄ ∧
        CrIn Ctx (W + BitVec.ofNat 64 16) W SP s₄.gpr R (Stitch.pre n) (D + BitVec.ofNat 64 (Stitch.pre n))
          (n - Stitch.pre n) s₄ := by
  have hn := hdat.ok.lt
  refine WP.seq (WP.mono (front_ok L hMK hJ haad hal h4 h5 h6 h7) fun s₂ h₂ => ?_)
  obtain ⟨hS, hT, F₂⟩ := stIn_of h₂ hdat h22 hR hf hrd hwr htb
  refine WP.seq (WP.mono (Stitch.stitchE_ok L gh hT hS) fun s₃ hm => ?_)
  obtain ⟨s₄, run₄, x23₄, x27₄, x24₄, x25₄, r₄⟩ := Stitch.afterE_ok (u := s₃) (D := D) (n := n)
    (by rw [hm.gpr _ (by decide), h₂.x23]) (by rw [hm.gpr _ (by decide), h₂.x26]) hn
  exact WP.of_runBlock ⟨s₄, run₄, stOut_of L h₂ hdat h22 hR h28 F₂ hrd hwr hm x23₄ x27₄ x24₄ x25₄ r₄⟩

theorem runWithSX_rel (v : GcmImpl) (cl : Prog isa) (hMK : MulKey) (gh : Gh8Ok) {tb : List Instr}
    {k₁ k₂ : Reg → BitVec 64} {H₁ H₂ : Block}
    {Np A D Tg : Addr} {al n R : Nat} {ρ₁ ρ₂ σ₁ σ₂ : State} {ex : List Region}
    (hexW : ∀ r ∈ ex, (workR W).Disjoint r) (hexC : ∀ r ∈ ex, (⟨Ctx, 256⟩ : Region).Disjoint r)
    (hJ₁ : J0In Ctx (W + BitVec.ofNat 64 16) W SP k₁ H₁ Np 12 σ₁)
    (hJ₂ : J0In Ctx (W + BitVec.ofNat 64 16) W SP k₂ H₂ Np 12 σ₂)
    (ha₁ : DataOk (W + BitVec.ofNat 64 16) W σ₁ A al) (ha₂ : DataOk (W + BitVec.ofNat 64 16) W σ₂ A al)
    (hal : al ≤ 16)
    (hx₁ : σ₁.gpr .x4 = A ∧ σ₁.gpr .x5 = BitVec.ofNat 64 al ∧ σ₁.gpr .x6 = D ∧ σ₁.gpr .x7 = BitVec.ofNat 64 n)
    (hx₂ : σ₂.gpr .x4 = A ∧ σ₂.gpr .x5 = BitVec.ofNat 64 al ∧ σ₂.gpr .x6 = D ∧ σ₂.gpr .x7 = BitVec.ofNat 64 n)
    (hd₁ : DataW Ctx (W + BitVec.ofNat 64 16) W σ₁ D n) (hd₂ : DataW Ctx (W + BitVec.ofNat 64 16) W σ₂ D n)
    (h22₁ : σ₁.gpr .x22 = BitVec.ofNat 64 R) (h22₂ : σ₂.gpr .x22 = BitVec.ofNat 64 R) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (h28₁ : σ₁.gpr .x28 = Tg) (h28₂ : σ₂.gpr .x28 = Tg)
    (hf₁ : Frame [workR W, ⟨D, n⟩] ρ₁.mem σ₁.mem) (hrd₁ : σ₁.rd = ρ₁.rd) (hwr₁ : σ₁.wr = ρ₁.wr)
    (hf₂ : Frame [workR W, ⟨D, n⟩] ρ₂.mem σ₂.mem) (hrd₂ : σ₂.rd = ρ₂.rd) (hwr₂ : σ₂.wr = ρ₂.wr)
    (hgh₁ : ∀ {s : State} {Y Dd S : Addr} {nb : Nat}, GhCall s (Ctx + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR W) → Region.Sub ⟨S, 256⟩ (workR W) →
      s.rd = ρ₁.rd → s.wr = ρ₁.wr → s.sp = SP → Frame [workR W, ⟨D, n⟩] ρ₁.mem s.mem →
      Region.Sub ⟨Dd, 16 * nb⟩ (⟨D, n⟩ : Region) →
      WP isa cl s fun u => GhPost s (Ctx + BitVec.ofNat 64 240) Y Dd S nb u ex)
    (hgh₂ : ∀ {s : State} {Y Dd S : Addr} {nb : Nat}, GhCall s (Ctx + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR W) → Region.Sub ⟨S, 256⟩ (workR W) →
      s.rd = ρ₂.rd → s.wr = ρ₂.wr → s.sp = SP → Frame [workR W, ⟨D, n⟩] ρ₂.mem s.mem →
      Region.Sub ⟨Dd, 16 * nb⟩ (⟨D, n⟩ : Region) →
      WP isa cl s fun u => GhPost s (Ctx + BitVec.ofNat 64 240) Y Dd S nb u ex)
    (hrel : ∀ {s₁ s₂ : State} {Y Dd S : Addr} {nb : Nat}, GhCall s₁ (Ctx + BitVec.ofNat 64 240) Y Dd S nb →
      GhCall s₂ (Ctx + BitVec.ofNat 64 240) Y Dd S nb → Region.Sub ⟨Y, 16⟩ (workR W) → Region.Sub ⟨S, 256⟩ (workR W) →
      s₁.sp = SP → s₂.sp = SP →
      s₁.rd = ρ₁.rd → s₁.wr = ρ₁.wr → Frame [workR W, ⟨D, n⟩] ρ₁.mem s₁.mem →
      s₂.rd = ρ₂.rd → s₂.wr = ρ₂.wr → Frame [workR W, ⟨D, n⟩] ρ₂.mem s₂.mem →
      Region.Sub ⟨Dd, 16 * nb⟩ (⟨D, n⟩ : Region) →
      RelCT isa (Eq2 s₁ s₂) cl TT)
    (htb₁ : ∀ u : State, Env Ctx (W + BitVec.ofNat 64 16) W SP u → u.rd = ρ₁.rd → u.wr = ρ₁.wr →
      Frame [workR W, ⟨D, n⟩] ρ₁.mem u.mem → KeyAt H₁ u.mem W → WP isa (.block tb) u (Stitch.TblPost W H₁ u))
    (htb₂ : ∀ u : State, Env Ctx (W + BitVec.ofNat 64 16) W SP u → u.rd = ρ₂.rd → u.wr = ρ₂.wr →
      Frame [workR W, ⟨D, n⟩] ρ₂.mem u.mem → KeyAt H₂ u.mem W → WP isa (.block tb) u (Stitch.TblPost W H₂ u))
    (htbrel : ∀ v₁ v₂ : State, v₁.sp = SP → v₂.sp = SP → (∀ r ∈ stRegs, v₁.gpr r = v₂.gpr r) →
      v₁.rd = ρ₁.rd → v₁.wr = ρ₁.wr → Frame [workR W, ⟨D, n⟩] ρ₁.mem v₁.mem →
      v₂.rd = ρ₂.rd → v₂.wr = ρ₂.wr → Frame [workR W, ⟨D, n⟩] ρ₂.mem v₂.mem →
      RelCT isa (Eq2 v₁ v₂) (.seq (.block tb) Impl.Gcm.AArch64.Stitch.enc) TT) :
    RelCT isa (Eq2 σ₁ σ₂) (Impl.AesGcm.AArch64.Stitch.runWithS v.callees tb cl) TT := by
  obtain ⟨x4₁, x5₁, x6₁, x7₁⟩ := hx₁
  obtain ⟨x4₂, x5₂, x6₂, x7₂⟩ := hx₂
  have hn := hd₁.ok.lt
  have hpn : Stitch.pre n ≤ n := Nat.mul_div_le n 128
  have hP16 : Stitch.pre n % 16 = 0 := by simp only [Stitch.pre]; omega
  have subR : Region.Sub ⟨D + BitVec.ofNat 64 (Stitch.pre n), n - Stitch.pre n⟩ ⟨D, n⟩ := Offset.sub_base D (by omega)
  unfold Impl.AesGcm.AArch64.Stitch.runWithS
  have chunk : RelCT isa (Eq2 σ₁ σ₂) (.seq Impl.AesGcm.AArch64.Fast.front (.seq (Impl.AesGcm.AArch64.Stitch.stitched []
      tb Impl.Gcm.AArch64.Stitch.enc) (.block (Impl.AesGcm.AArch64.Stitch.whole ++
      [.add .x .x23 .x23 .x9, mov .x27 .x23, .sub .x .x24 .x26 .x9, imm .x25 0])))) TT := by
    refine rel_seq (rel_taint [.x4, .x5, .x6, .x7, .x19, .x20, .x21, .x23]
        (by rw [hJ₁.env.sp, hJ₂.env.sp])
        (by agree_tac [x4₁, x4₂, x5₁, x5₂, x6₁, x6₂, x7₁, x7₂, hJ₁.env.x19, hJ₂.env.x19, hJ₁.env.x20, hJ₂.env.x20,
          hJ₁.env.x21, hJ₂.env.x21, hJ₁.x23, hJ₂.x23]) ⟨_, by taint_decide⟩)
      (front_ok L hMK hJ₁ ha₁ hal x4₁ x5₁ x6₁ x7₁) (front_ok L hMK hJ₂ ha₂ hal x4₂ x5₂ x6₂ x7₂)
      fun s₂ t₂ h₂ k₂ => ?_
    obtain ⟨S₁, T₁, F₁⟩ := stIn_of h₂ hd₁ h22₁ hR hf₁ hrd₁ hwr₁ htb₁
    obtain ⟨S₂, T₂, F₂⟩ := stIn_of k₂ hd₂ h22₂ hR hf₂ hrd₂ hwr₂ htb₂
    refine rel_seq (stitched_rel (n := n) (by rw [h₂.env.sp, k₂.env.sp]) (fun r hr h9 => ?_) h₂.x26 hn
        fun v₁ v₂ hsp hr g₁ m₁ r₁ w₁ sp₁ g₂ m₂ r₂ w₂ sp₂ => htbrel v₁ v₂ (by rw [sp₁, h₂.env.sp])
          (by rw [sp₂, k₂.env.sp]) hr (by rw [r₁, h₂.rd, hrd₁]) (by rw [w₁, h₂.wr, hwr₁]) (by rw [m₁]; exact F₁)
          (by rw [r₂, k₂.rd, hrd₂]) (by rw [w₂, k₂.wr, hwr₂]) (by rw [m₂]; exact F₂))
      (Stitch.stitchE_ok L gh T₁ S₁) (Stitch.stitchE_ok L gh T₂ S₂) fun s₃ t₃ m₁ m₂ => ?_
    · simp only [stRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact absurd rfl h9
      · rw [h₂.env.x19, k₂.env.x19]
      · rw [h₂.env.x20, k₂.env.x20]
      · rw [h₂.env.x21, k₂.env.x21]
      · rw [h₂.x22, k₂.x22, h22₁, h22₂]
      · rw [h₂.x23, k₂.x23]
      · rw [h₂.x26, k₂.x26]
    exact rel_taint [.x19, .x20, .x21, .x23, .x26] (by rw [m₁.env.sp, m₂.env.sp])
      (by agree_tac [m₁.env.x19, m₂.env.x19, m₁.env.x20, m₂.env.x20, m₁.env.x21, m₂.env.x21,
        m₁.gpr .x23 (by decide), m₂.gpr .x23 (by decide), m₁.gpr .x26 (by decide), m₂.gpr .x26 (by decide),
        h₂.x23, k₂.x23, h₂.x26, k₂.x26]) ⟨_, by taint_decide⟩
  refine RelCT.seq_assoc3 (rel_seq chunk
    (ctAS_ok L hMK gh hJ₁ ha₁ hal x4₁ x5₁ x6₁ x7₁ hd₁ h22₁ hR h28₁ hf₁ hrd₁ hwr₁ htb₁)
    (ctAS_ok L hMK gh hJ₂ ha₂ hal x4₂ x5₂ x6₂ x7₂ hd₂ h22₂ hR h28₂ hf₂ hrd₂ hwr₂ htb₂)
    fun s₃ t₃ ⟨m₁, c₁⟩ ⟨m₂, c₂⟩ => ?_)
  refine rel_seq (cryptAl_rel L v c₁ c₂ hP16) (WP.with_rdwr (cryptAl_ok L v (icb := 0) c₁ hP16))
    (WP.with_rdwr (cryptAl_ok L v (icb := 0) c₂ hP16)) fun s₄ t₄ ⟨o₁, rd₁, wr₁⟩ ⟨o₂, rd₂, wr₂⟩ => ?_
  have M₁ := Mid.cryptS L m₁ subR c₁.data o₁ rd₁ wr₁
  have M₂ := Mid.cryptS L m₂ subR c₂.data o₂ rd₂ wr₂
  refine rel_seq (rel_taint [.x19, .x20, .x21, .x26, .x27] (by rw [M₁.env.sp, M₂.env.sp])
      (by agree_tac [M₁.env.x19, M₂.env.x19, M₁.env.x20, M₂.env.x20, M₁.env.x21, M₂.env.x21, M₁.x26, M₂.x26,
        M₁.x27, M₂.x27]) ⟨_, by taint_decide⟩)
    (WP.with_rdwr (ctCS_ok L M₁ (by rw [o₁.x25, hP16]))) (WP.with_rdwr (ctCS_ok L M₂ (by rw [o₂.x25, hP16]))) fun s₅ t₅ ⟨a₁, rd₅, wr₅⟩ ⟨a₂, rd₅', wr₅'⟩ => ?_
  have fr₁ : Frame [workR W, ⟨D, n⟩] ρ₁.mem s₅.mem := M₁.fr.trans (absFrame_wd a₁.frame)
  have fr₂ : Frame [workR W, ⟨D, n⟩] ρ₂.mem t₅.mem := M₂.fr.trans (absFrame_wd a₂.frame)
  have r₁ : s₅.rd = ρ₁.rd := rd₅.trans M₁.rd
  have w₁ : s₅.wr = ρ₁.wr := wr₅.trans M₁.wr
  have r₂ : t₅.rd = ρ₂.rd := rd₅'.trans M₂.rd
  have w₂ : t₅.wr = ρ₂.wr := wr₅'.trans M₂.wr
  have sY : Region.Sub ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16, 16⟩ (workR W) := stW (by decide)
  have sS : Region.Sub ⟨W + BitVec.ofNat 64 512, 256⟩ (workR W) := Lay.wSub (by decide)
  have hexH : ∀ r ∈ ex, (⟨Ctx + BitVec.ofNat 64 240, 16⟩ : Region).Disjoint r := fun r hr =>
    (hexC r hr).sub_left (Lay.ctxSub (d := 240) (n := 16) (by decide))
  have hexB : ∀ r ∈ ex, (⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32, 16⟩ : Region).Disjoint r := fun r hr =>
    (hexW r hr).sub_left (stW (by decide))
  have hexK : ∀ r ∈ ex, (keyR W).Disjoint r := fun r hr => (hexW r hr).sub_left (Lay.wSub (by decide))
  have hDd : Region.Sub ⟨D + BitVec.ofNat 64 (Stitch.pre n) + BitVec.ofNat 64 0, 16 * ((n - Stitch.pre n - 0) / 16)⟩
      ⟨D, n⟩ := fun x hx => subR x (Offset.sub_base _ (by omega) x hx)
  refine rel_seq (hrel a₁.call a₂.call sY sS a₁.env.sp a₂.env.sp r₁ w₁ fr₁ r₂ w₂ fr₂ hDd)
    (WP.with_rdwr (absCall2WithX_ok L (.inr rfl) (Q := fun _ => True) hexH hexB a₁
      (WP.mono (hgh₁ a₁.call sY sS r₁ w₁ a₁.env.sp fr₁ hDd) fun _ g => ⟨g, trivial⟩)))
    (WP.with_rdwr (absCall2WithX_ok L (.inr rfl) (Q := fun _ => True) hexH hexB a₂
      (WP.mono (hgh₂ a₂.call sY sS r₂ w₂ a₂.env.sp fr₂ hDd) fun _ g => ⟨g, trivial⟩)))
    fun s₇ t₇ ⟨⟨⟨b₁, l₁⟩, _⟩, rd₇, wr₇⟩ ⟨⟨⟨b₂, l₂⟩, _⟩, rd₇', wr₇'⟩ => ?_
  have N₁ := Mid.absorbXS L M₁ b₁ (by rw [rd₇, rd₅]) (by rw [wr₇, wr₅]) hexK
  have N₂ := Mid.absorbXS L M₂ b₂ (by rw [rd₇', rd₅']) (by rw [wr₇', wr₅']) hexK
  refine RelCT.seq_assoc3 (rel_seq (rel_taint [.x19, .x20, .x21, .x23, .x24, .x26] (by rw [N₁.env.sp, N₂.env.sp])
      (by agree_tac [N₁.env.x19, N₂.env.x19, N₁.env.x20, N₂.env.x20, N₁.env.x21, N₂.env.x21, b₁.x23, b₂.x23,
        b₁.x24, b₂.x24, N₁.x26, N₂.x26]) ⟨_, by taint_decide⟩)
    (ctE'_ok L hMK (.inl rfl) N₁ b₁ l₁) (ctE'_ok L hMK (.inl rfl) N₂ b₂ l₂) fun s₁₆ t₁₆ ⟨_, _, _, _, T₁, k28₁⟩ ⟨_, _, _, _, T₂, k28₂⟩ => ?_)
  refine rel_seq (rel_ctr v.ctr T₁.call T₂.call (by rw [T₁.env.sp, T₂.env.sp]))
    (tagCall_ok L v (.inl rfl) T₁) (tagCall_ok L v (.inl rfl) T₂) fun s₁₇ t₁₇ O₁ O₂ => ?_
  exact rel_taint [.x19, .x28] (by rw [O₁.env.sp, O₂.env.sp])
    (by agree_tac [O₁.env.x19, O₂.env.x19, O₁.kept .x28 (by decide), O₂.kept .x28 (by decide), k28₁, k28₂])
    ⟨_, by taint_decide⟩

end

/-- `seal` with the path for TLS records, its whole blocks hashed by `gh`, is
constant time, for a `gh` that hashes as `vg_ghash` and leaks the same in two
runs, called with memory changed since the entry only in the working space and
the text. -/
theorem sealWithSX_ct (v : GcmImpl) (cl : Prog isa) (hMK : MulKey) (gh : Gh8Ok) {tb : List Instr} {w : Nat}
    (hw : w = 1 ∨ w = 2)
    {extra extraW : State → List Region} {pre : State → Prop}
    (hpre : ∀ s, pre s → sealPreXW w (extra s) s (extraW s))
    {ex : State → List Region}
    (hexW : ∀ {σ : State}, pre σ → ∀ r ∈ ex σ, (workR (stackArg σ w)).Disjoint r)
    (hexC : ∀ {σ : State}, pre σ → ∀ r ∈ ex σ, (⟨σ.gpr .x0, 256⟩ : Region).Disjoint r)
    (hexq : ∀ {σ₁ σ₂ : State}, onePub (w + 1) σ₁ σ₂ → ex σ₂ = ex σ₁)
    (hgh : ∀ {σ s : State} {Y Dd S : Addr} {nb : Nat}, pre σ →
      GhCall s (σ.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR (stackArg σ w)) → Region.Sub ⟨S, 256⟩ (workR (stackArg σ w)) →
      s.rd = σ.rd → s.wr = σ.wr → s.sp = σ.sp →
      Frame [workR (stackArg σ w), ⟨σ.gpr .x6, (σ.gpr .x7).toNat⟩] σ.mem s.mem →
      Region.Sub ⟨Dd, 16 * nb⟩ (⟨σ.gpr .x6, (σ.gpr .x7).toNat⟩ : Region) →
      WP isa cl s fun u => GhPost s (σ.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb u (ex σ))
    (hrel : ∀ {σ₁ σ₂ s₁ s₂ : State} {Y Dd S : Addr} {nb : Nat}, pre σ₁ → pre σ₂ → onePub (w + 1) σ₁ σ₂ →
      GhCall s₁ (σ₁.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      GhCall s₂ (σ₁.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR (stackArg σ₁ w)) → Region.Sub ⟨S, 256⟩ (workR (stackArg σ₁ w)) →
      s₁.sp = σ₁.sp → s₂.sp = σ₁.sp →
      s₁.rd = σ₁.rd → s₁.wr = σ₁.wr →
      Frame [workR (stackArg σ₁ w), ⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩] σ₁.mem s₁.mem →
      s₂.rd = σ₂.rd → s₂.wr = σ₂.wr →
      Frame [workR (stackArg σ₁ w), ⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩] σ₂.mem s₂.mem →
      Region.Sub ⟨Dd, 16 * nb⟩ (⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩ : Region) →
      RelCT isa (Eq2 s₁ s₂) cl TT)
    (htb : ∀ {σ : State}, pre σ → TbFor tb w σ)
    (htbrel : ∀ {σ₁ σ₂ : State}, pre σ₁ → pre σ₂ → onePub (w + 1) σ₁ σ₂ → ∀ v₁ v₂ : State, v₁.sp = σ₁.sp →
      v₂.sp = σ₁.sp → (∀ r ∈ stRegs, v₁.gpr r = v₂.gpr r) →
      v₁.rd = σ₁.rd → v₁.wr = σ₁.wr →
      Frame [workR (stackArg σ₁ w), ⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩] σ₁.mem v₁.mem →
      v₂.rd = σ₂.rd → v₂.wr = σ₂.wr →
      Frame [workR (stackArg σ₁ w), ⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩] σ₂.mem v₂.mem →
      RelCT isa (Eq2 v₁ v₂) (.seq (.block tb) Impl.Gcm.AArch64.Stitch.enc) TT) :
    ConstantTime isa pre (onePub (w + 1)) (Impl.AesGcm.AArch64.Stitch.sealWithS v.callees (8 * w) tb cl) := by
  refine ct_of fun σ₁ σ₂ p₁ p₂ hq => ?_
  have h₁ := hpre _ p₁
  have h₂ := hpre _ p₂
  have hq₀ := hq
  have exq := hexq hq
  obtain ⟨f₁, f₂⟩ := oneFacts (by omega : w < w + 1) (sealCore h₁) (sealCore h₂) hq
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, qsp, qa⟩ := hq
  have qt : stackArg σ₁ 0 = stackArg σ₂ 0 := qa 0 (by omega)
  have L := f₁.ol.lay
  have hT₁ : σ₁.mem.readW (σ₁.sp + BitVec.ofNat 64 0) 64 = stackArg σ₁ 0 := rfl
  have hT₂ : σ₂.mem.readW (σ₂.sp + BitVec.ofNat 64 0) 64 = stackArg σ₁ 0 := qt.symm
  have hW₁ : σ₁.mem.readW (σ₁.sp + BitVec.ofNat 64 (8 * w)) 64 = stackArg σ₁ w := rfl
  have hW₂ : σ₂.mem.readW (σ₂.sp + BitVec.ofNat 64 (8 * w)) 64 = stackArg σ₁ w := f₂.hW
  have hk : 8 * w % 8 = 0 ∧ 8 * w < 32768 := by omega
  unfold Impl.AesGcm.AArch64.Stitch.sealWithS
  refine rel_seq (entryStash_rel (k := 8 * w) (j := 0) (by omega) rfl (.inl rfl) f₁ f₂ (by omega) qsp
      (by agree_tac [q0, q1, q2, q3, q4, q5, q6, q7]))
    (WP.block_and (entryStash_ok (V := stackArg σ₁ 0) hk (by decide) hW₁ (f₁.hsp w (by omega))
      (f₁.hsp 0 (by omega)) hT₁ (f₁.argW (by omega)) rfl f₁.perm)
      (entry_keeps hk (by decide) hW₁ (f₁.hsp w (by omega)) (f₁.hsp 0 (by omega)) f₁.perm.w))
    (WP.block_and (entryStash_ok (V := stackArg σ₁ 0) hk (by decide) hW₂ (f₂.hsp w (by omega))
      (f₂.hsp 0 (by omega)) hT₂ (f₂.argW (by omega)) q0.symm f₂.perm)
      (entry_keeps hk (by decide) hW₂ (f₂.hsp w (by omega)) (f₂.hsp 0 (by omega)) f₂.perm.w))
    fun τ₁ τ₂ ⟨a₁, k₁⟩ ⟨a₂, k₂⟩ => ?_
  have k5₁ : τ₁.gpr .x5 = BitVec.ofNat 64 (σ₁.gpr .x5).toNat := by rw [k₁ .x5 (by simp), ofNat_toNat']
  have k5₂ : τ₂.gpr .x5 = BitVec.ofNat 64 (σ₁.gpr .x5).toNat := by rw [k₂ .x5 (by simp), ← q5, ofNat_toNat']
  have k24₁ : τ₁.gpr .x24 = BitVec.ofNat 64 (σ₁.gpr .x3).toNat := by rw [a₁.2.2.2.1, ofNat_toNat']
  have k24₂ : τ₂.gpr .x24 = BitVec.ofNat 64 (σ₁.gpr .x3).toNat := by rw [a₂.2.2.2.1, ← q3, ofNat_toNat']
  refine rel_seq (rel_taint [.x5, .x24] (by rw [a₁.1.sp, a₂.1.sp, qsp]) (by agree_tac [k5₁, k5₂, k24₁, k24₂])
      ⟨_, by taint_decide⟩)
    (cond_ok k5₁ (σ₁.gpr .x5).isLt k24₁ (σ₁.gpr .x3).isLt) (cond_ok k5₂ (σ₁.gpr .x5).isLt k24₂ (σ₁.gpr .x3).isLt)
    fun u₁ u₂ ⟨c₁, r₁⟩ ⟨c₂, r₂⟩ => ?_
  have b₁ := SealEntered.of_regs a₁ r₁
  have b₂ := SealEntered.of_regs a₂ r₂
  refine rel_ite (eval_zero c₁ (by split <;> decide)) (eval_zero c₂ (by split <;> decide)) (fun ht => ?_)
    (fun _ => sealRest_rel v h₁ h₂ hq₀ b₁ b₂)
  have hc : (σ₁.gpr .x5).toNat ≤ 16 ∧ (σ₁.gpr .x3).toNat = 12 := by
    by_contra hc; simp [hc] at ht
  have gu₁ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], u₁.gpr r = σ₁.gpr r := fun r hr => by
    rw [r₁.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), k₁ r hr]
  have gu₂ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], u₂.gpr r = σ₁.gpr r := fun r hr => by
    rw [r₂.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), k₂ r hr]
    simp at hr; rcases hr with rfl | rfl | rfl | rfl
    · exact q4.symm
    · exact q5.symm
    · exact q6.symm
    · exact q7.symm
  -- `thr`, on the length, which is public.
  refine rel_seq (rel_taint [.x7] (by rw [r₁.sp, r₂.sp, a₁.1.sp, a₂.1.sp, qsp])
      (by agree_tac [gu₁ .x7 (by simp), gu₂ .x7 (by simp)]) ⟨_, by taint_decide⟩)
    (Stitch.thr_ok u₁) (Stitch.thr_ok u₂) fun v₁ v₂ ⟨x9₁, t₁⟩ ⟨x9₂, t₂⟩ => ?_
  have e9 : v₂.gpr .x9 = BitVec.ofNat 64 (v₁.gpr .x9).toNat := by
    rw [ofNat_toNat', x9₁, x9₂, gu₁ .x7 (by simp), gu₂ .x7 (by simp)]
  have b₁ := SealEntered.of_regs b₁ t₁
  have b₂ := SealEntered.of_regs b₂ t₂
  have i₁ := frontIn_of f₁ rfl rfl rfl rfl rfl rfl b₁
  have i₂ := frontIn_of f₂ q3.symm q2.symm q4.symm q5.symm q6.symm q7.symm b₂
  rw [← qsp] at i₂
  rw [hc.2] at i₁ i₂
  have ol := f₁.ol
  have sub16 : Region.Sub ⟨stackArg σ₁ w + BitVec.ofNat 64 16, 80⟩ (workR (stackArg σ₁ w)) := Lay.wSub (by decide)
  have hn := (σ₁.gpr .x7).isLt
  have g₁ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], v₁.gpr r = σ₁.gpr r := fun r hr => by
    rw [t₁.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), gu₁ r hr]
  have g₂ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], v₂.gpr r = σ₁.gpr r := fun r hr => by
    rw [t₂.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), gu₂ r hr]
  have mkD : ∀ {σ u : State}, OneFacts σ σ₁ (w + 1) w → u.wr = σ.wr →
      DataW (σ₁.gpr .x0) (stackArg σ₁ w + BitVec.ofNat 64 16) (stackArg σ₁ w) u (σ₁.gpr .x6) (σ₁.gpr .x7).toNat :=
    fun f wr => ⟨⟨covers_left (by rw [wr]; exact f.dataW), hn, ol.dw, ol.data.sub_right sub16, ol.data⟩,
      by rw [wr]; exact f.dataW, ol.cd⟩
  have hf : ∀ {σ u : State}, Frame [entryR (stackArg σ₁ w)] σ.mem u.mem →
      Frame [workR (stackArg σ₁ w), ⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩] σ.mem u.mem :=
    fun f => f.sub fun r hr => ⟨_, List.mem_cons_self .., entryR_work _ r hr⟩
  have hgh₂ := @hgh σ₂
  rw [f₂.hW, ← q0, ← q6, ← q7] at hgh₂
  have htb₂ := htb p₂
  unfold TbFor at htb₂
  rw [f₂.hW, ← q0, ← q6, ← q7, ← qsp] at htb₂
  have e₁ := b₁
  have e₂ := b₂
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, bf₁, -, brd₁, bwr₁⟩ := e₁
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, bf₂, -, brd₂, bwr₂⟩ := e₂
  have hH₁ : blockAt v₁.mem (σ₁.gpr .x0 + BitVec.ofNat 64 240) = Spec.Gcm.ctxH σ₁.mem (σ₁.gpr .x0) :=
    blockAt_frame bf₁ (keep_of_sub (entryR_work _) (ol.ctx.sub_left (Lay.ctxSub (d := 240) (n := 16) (by decide))))
  have hH₂ : blockAt v₂.mem (σ₁.gpr .x0 + BitVec.ofNat 64 240) = Spec.Gcm.ctxH σ₂.mem (σ₁.gpr .x0) :=
    blockAt_frame bf₂ (keep_of_sub (entryR_work _) (ol.ctx.sub_left (Lay.ctxSub (d := 240) (n := 16) (by decide))))
  refine rel_ite (eval_zero (a := (v₁.gpr .x9).toNat) (by rw [ofNat_toNat']) (v₁.gpr .x9).isLt)
    (eval_zero e9 (v₁.gpr .x9).isLt) (fun _ => ?_) (fun _ => ?_)
  · refine runWithPX_rel L v cl hMK (Tg := stackArg σ₁ 0) (R := (σ₁.gpr .x1).toNat) (hexW p₁) (hexC p₁)
      ⟨i₁.env, i₁.kept, i₁.x23, i₁.x24, i₁.x26, i₁.x27, i₁.non, rfl⟩
      ⟨i₂.env, i₂.kept, i₂.x23, i₂.x24, i₂.x26, i₂.x27, i₂.non, rfl⟩ i₁.aad i₂.aad hc.1
      ⟨g₁ .x4 (by simp), by rw [g₁ .x5 (by simp), ofNat_toNat'], g₁ .x6 (by simp), by rw [g₁ .x7 (by simp), ofNat_toNat']⟩
      ⟨g₂ .x4 (by simp), by rw [g₂ .x5 (by simp), ofNat_toNat'], g₂ .x6 (by simp), by rw [g₂ .x7 (by simp), ofNat_toNat']⟩
      (mkD f₁ b₁.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2) (mkD f₂ b₂.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
      (by rw [b₁.2.1, ofNat_toNat']) (by rw [b₂.2.1, ← q1, ofNat_toNat']) ol.rounds b₁.2.2.2.2.2.2.1 b₂.2.2.2.2.2.2.1
      (hf bf₁) brd₁ bwr₁ (hf bf₂) brd₂ bwr₂ ?_ ?_ ?_
    · intro s Y Dd S nb c y z r w' sp f hd
      exact hgh p₁ c y z r w' sp f hd
    · intro s Y Dd S nb c y z r w' sp f hd
      rw [← exq]
      exact hgh₂ p₂ c y z r w' (sp.trans qsp) f hd
    · intro s₁ s₂ Y Dd S nb c₁ c₂ y z sp₁ sp₂ r₁ w₁ f₁ r₂ w₂ f₂ hd
      exact hrel p₁ p₂ hq₀ c₁ c₂ y z sp₁ sp₂ r₁ w₁ f₁ r₂ w₂ f₂ hd
  · refine runWithSX_rel L v cl hMK gh (Tg := stackArg σ₁ 0) (R := (σ₁.gpr .x1).toNat) (hexW p₁) (hexC p₁)
      ⟨i₁.env, i₁.kept, i₁.x23, i₁.x24, i₁.x26, i₁.x27, i₁.non, rfl⟩
      ⟨i₂.env, i₂.kept, i₂.x23, i₂.x24, i₂.x26, i₂.x27, i₂.non, rfl⟩ i₁.aad i₂.aad hc.1
      ⟨g₁ .x4 (by simp), by rw [g₁ .x5 (by simp), ofNat_toNat'], g₁ .x6 (by simp), by rw [g₁ .x7 (by simp), ofNat_toNat']⟩
      ⟨g₂ .x4 (by simp), by rw [g₂ .x5 (by simp), ofNat_toNat'], g₂ .x6 (by simp), by rw [g₂ .x7 (by simp), ofNat_toNat']⟩
      (mkD f₁ b₁.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2) (mkD f₂ b₂.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
      (by rw [b₁.2.1, ofNat_toNat']) (by rw [b₂.2.1, ← q1, ofNat_toNat']) ol.rounds b₁.2.2.2.2.2.2.1 b₂.2.2.2.2.2.2.1
      (hf bf₁) brd₁ bwr₁ (hf bf₂) brd₂ bwr₂ ?_ ?_ ?_ ?_ ?_ ?_
    · intro s Y Dd S nb c y z r w' sp f hd
      exact hgh p₁ c y z r w' sp f hd
    · intro s Y Dd S nb c y z r w' sp f hd
      rw [← exq]
      exact hgh₂ p₂ c y z r w' (sp.trans qsp) f hd
    · intro s₁ s₂ Y Dd S nb c₁ c₂ y z sp₁ sp₂ r₁ w₁ f₁ r₂ w₂ f₂ hd
      exact hrel p₁ p₂ hq₀ c₁ c₂ y z sp₁ sp₂ r₁ w₁ f₁ r₂ w₂ f₂ hd
    · intro u he hrd hwr hf' key
      rw [hH₁] at key ⊢
      exact htb p₁ u he hrd hwr hf' key
    · intro u he hrd hwr hf' key
      rw [hH₂] at key ⊢
      exact htb₂ u he hrd hwr hf' key
    · intro v₁ v₂ sp₁ sp₂ hr r₁ w₁ f₁ r₂ w₂ f₂
      exact htbrel p₁ p₂ hq₀ v₁ v₂ sp₁ sp₂ hr r₁ w₁ f₁ r₂ w₂ f₂

/-- `sealWithEX_ct`, for a call that writes only what `vg_ghash` does. -/
theorem sealWithS_ct (v : GcmImpl) (cl : Prog isa) (hMK : MulKey) (gh : Gh8Ok) {tb : List Instr} {w : Nat}
    (hw : w = 1 ∨ w = 2)
    {extra : State → List Region} {pre : State → Prop} (hpre : ∀ s, pre s → sealPreXW w (extra s) s)
    (hgh : ∀ {σ s : State} {Y Dd S : Addr} {nb : Nat}, pre σ →
      GhCall s (σ.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR (stackArg σ w)) → Region.Sub ⟨S, 256⟩ (workR (stackArg σ w)) →
      s.rd = σ.rd → s.wr = σ.wr → s.sp = σ.sp →
      Frame [workR (stackArg σ w), ⟨σ.gpr .x6, (σ.gpr .x7).toNat⟩] σ.mem s.mem →
      WP isa cl s (GhPost s (σ.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb))
    (hrel : ∀ {σ₁ σ₂ s₁ s₂ : State} {Y Dd S : Addr} {nb : Nat}, pre σ₁ → pre σ₂ → onePub (w + 1) σ₁ σ₂ →
      GhCall s₁ (σ₁.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      GhCall s₂ (σ₁.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR (stackArg σ₁ w)) → Region.Sub ⟨S, 256⟩ (workR (stackArg σ₁ w)) →
      s₁.sp = σ₁.sp → s₂.sp = σ₁.sp →
      s₁.rd = σ₁.rd → s₁.wr = σ₁.wr →
      Frame [workR (stackArg σ₁ w), ⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩] σ₁.mem s₁.mem →
      s₂.rd = σ₂.rd → s₂.wr = σ₂.wr →
      Frame [workR (stackArg σ₁ w), ⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩] σ₂.mem s₂.mem →
      RelCT isa (Eq2 s₁ s₂) cl TT)
    (htb : ∀ {σ : State}, pre σ → TbFor tb w σ)
    (htbrel : ∀ {σ₁ σ₂ : State}, pre σ₁ → pre σ₂ → onePub (w + 1) σ₁ σ₂ → ∀ v₁ v₂ : State, v₁.sp = σ₁.sp →
      v₂.sp = σ₁.sp → (∀ r ∈ stRegs, v₁.gpr r = v₂.gpr r) →
      v₁.rd = σ₁.rd → v₁.wr = σ₁.wr →
      Frame [workR (stackArg σ₁ w), ⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩] σ₁.mem v₁.mem →
      v₂.rd = σ₂.rd → v₂.wr = σ₂.wr →
      Frame [workR (stackArg σ₁ w), ⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩] σ₂.mem v₂.mem →
      RelCT isa (Eq2 v₁ v₂) (.seq (.block tb) Impl.Gcm.AArch64.Stitch.enc) TT) :
    ConstantTime isa pre (onePub (w + 1)) (Impl.AesGcm.AArch64.Stitch.sealWithS v.callees (8 * w) tb cl) :=
  sealWithSX_ct v cl hMK gh hw hpre (ex := fun _ => []) (fun _ => by simp) (fun _ => by simp) (fun _ => rfl)
    (fun p c y z r w sp f _ => hgh p c y z r w sp f)
    (fun p₁ p₂ hq c₁ c₂ y z sp₁ sp₂ r₁ w₁ f₁ r₂ w₂ f₂ _ => hrel p₁ p₂ hq c₁ c₂ y z sp₁ sp₂ r₁ w₁ f₁ r₂ w₂ f₂)
    htb htbrel


end VG.Proof.AesGcm.AArch64.Fast
