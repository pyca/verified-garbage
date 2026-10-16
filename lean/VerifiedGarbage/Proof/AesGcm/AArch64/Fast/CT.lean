module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Seal
public import VerifiedGarbage.Proof.AesGcm.AArch64.SealCT
meta import VerifiedGarbage.Proof.AesGcm.AArch64.SealCT
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Seal
import VerifiedGarbage.Proof.AesGcm.AArch64.Cmp
import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Cmp
meta import VerifiedGarbage.Proof.Cmac.Frame
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# AES-GCM on AArch64: `vg_aes_gcm_seal` with the path for TLS records is constant time

Untrusted: everything here is checked by Lean. The entry by `entryStash_rel`,
`cond` and the code of `run` between its calls by the taint analysis, from the
registers that hold the pointers and lengths (public in both runs), the calls
by `cryptAl_rel`, `rel_gh` and `rel_ctr`, and `sealRest` by `sealRest_rel`.
At each call, the correctness lemmas give both runs' states (`Mid`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64.Fast

open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Taint VG.Impl.AesGcm.AArch64
open VG.Proof.AesGcm.AArch64
open VG.Proof.Gcm.Poly VG.Proof.Gcm.AArch64.Pmull
open VG.Impl.Gcm.AArch64.Pmull (LO MID HI A T C Y tReg sReg poly)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- Reassociating a sequence, in two runs. -/
theorem RelCT.seq_assoc {a b c : Prog isa} {P Q : State → State → Prop}
    (h : RelCT isa P (.seq (.seq a b) c) Q) : RelCT isa P (.seq a (.seq b c)) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq ea e₁' => cases e₁' with
    | seq eb ec => cases e₂ with
      | seq fa e₂' => cases e₂' with
        | seq fb fc =>
          have := h _ _ _ _ _ _ hp (.seq (.seq ea eb) ec) (.seq (.seq fa fb) fc)
          simpa [List.append_assoc] using this

/-- Reassociating three pieces before the rest, in two runs. -/
theorem RelCT.seq_assoc3 {a b c r : Prog isa} {P Q : State → State → Prop}
    (h : RelCT isa P (.seq (.seq a (.seq b c)) r) Q) : RelCT isa P (.seq a (.seq b (.seq c r))) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq ea e₁' => cases e₁' with
    | seq eb e₁'' => cases e₁'' with
      | seq ec er => cases e₂ with
        | seq fa e₂' => cases e₂' with
          | seq fb e₂'' => cases e₂'' with
            | seq fc fr =>
              have := h _ _ _ _ _ _ hp (.seq (.seq ea (.seq eb ec)) er) (.seq (.seq fa (.seq fb fc)) fr)
              simpa [List.append_assoc] using this

/-- Between the calls of `run`: where everything is, the pointers and lengths
in their registers, and `H'` kept. -/
structure Mid (Ctx W SP : Addr) (H : Block) (R n : Nat) (D Tg : Addr) (s : State) : Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP s
  x22 : s.gpr .x22 = BitVec.ofNat 64 R
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  x26 : s.gpr .x26 = BitVec.ofNat 64 n
  x27 : s.gpr .x27 = D
  x28 : s.gpr .x28 = Tg
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H
  key : KeyAt H s.mem W
  data : DataW Ctx (W + BitVec.ofNat 64 16) W s D n

section
variable {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W)
include L

/-- `Mid` after `cryptAl`. -/
theorem Mid.crypt {H : Block} {R n : Nat} {D Tg : Addr} {s s' : State} {icb : Block}
    (h : Mid Ctx W SP H R n D Tg s) (o : CrOut Ctx (W + BitVec.ofNat 64 16) W SP s.gpr R icb 0 D n s.mem s')
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Mid Ctx W SP H R n D Tg s' := by
  have dWK : ∀ r ∈ crFrame (W + BitVec.ofNat 64 16) W D n, (keyR W).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (h.data.ok.w.sub_right (Lay.wSub (by decide))).symm
    · exact (L.st_w (a := 48) (n := 32) (by decide) (.inr ⟨by decide, by decide⟩)).symm
    · exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)
  exact ⟨o.env, by rw [o.kept .x22 (by decide), h.x22], h.rounds, by rw [o.kept .x26 (by decide), h.x26],
    by rw [o.kept .x27 (by decide), h.x27], by rw [o.kept .x28 (by decide), h.x28],
    by rw [hH_crFrame L h.data o.frame, h.hH], h.key.frame o.frame dWK, h.data.of_eq hrd hwr⟩

/-- `Mid` after the call of `vg_ghash` on the whole blocks. -/
theorem Mid.absorb {H : Block} {R n : Nat} {D Tg : Addr} {s s' : State} {x : List Byte} {j : Nat}
    (h : Mid Ctx W SP H R n D Tg s)
    (o : AbsMid Ctx (W + BitVec.ofNat 64 16) W SP s.gpr 16 H x D n 0 s.mem j s')
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Mid Ctx W SP H R n D Tg s' := by
  refine ⟨o.env, by rw [o.kept .x22 (by decide), h.x22], h.rounds, by rw [o.kept .x26 (by decide), h.x26],
    by rw [o.kept .x27 (by decide), h.x27], by rw [o.kept .x28 (by decide), h.x28], o.hH,
    h.key.frame o.frame fun r hr => ?_, h.data.of_eq hrd hwr⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (L.st_w (a := 16) (n := 16) (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact (L.st_w (a := 32) (n := 16) (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)

/-- `front` and the moves after it: `Mid`, and the arguments of `cryptAl`. -/
theorem ctA_ok {k : Reg → BitVec 64} {H : Block} {Np A D Tg : Addr} {al n R : Nat} {s₁ : State}
    (hJ : J0In Ctx (W + BitVec.ofNat 64 16) W SP k H Np 12 s₁) (haad : DataOk (W + BitVec.ofNat 64 16) W s₁ A al)
    (hal : al ≤ 16) (h4 : s₁.gpr .x4 = A) (h5 : s₁.gpr .x5 = BitVec.ofNat 64 al) (h6 : s₁.gpr .x6 = D)
    (h7 : s₁.gpr .x7 = BitVec.ofNat 64 n) (hdat : DataW Ctx (W + BitVec.ofNat 64 16) W s₁ D n)
    (h22 : s₁.gpr .x22 = BitVec.ofNat 64 R) (hR : R = 10 ∨ R = 12 ∨ R = 14) (h28 : s₁.gpr .x28 = Tg) :
    WP isa (.seq Impl.AesGcm.AArch64.Fast.front (.block [mov .x27 .x23, mov .x24 .x26, imm .x25 0])) s₁
      fun s₃ => Mid Ctx W SP H R n D Tg s₃ ∧ CrIn Ctx (W + BitVec.ofNat 64 16) W SP s₃.gpr R 0 D n s₃ := by
  refine WP.seq (WP.mono (front_ok L hJ haad hal h4 h5 h6 h7) fun s₂ h₂ => ?_)
  obtain ⟨s₃, run₃, x27₃, x24₃, x25₃, r₃⟩ : ∃ s₃, runBlock isa [mov .x27 .x23, mov .x24 .x26, imm .x25 0] s₂ =
      some s₃ ∧ s₃.gpr .x27 = D ∧ s₃.gpr .x24 = BitVec.ofNat 64 n ∧
      s₃.gpr .x25 = BitVec.ofNat 64 (0 % 16) ∧ Regs [.x27, .x24, .x25] s₂ s₃ := by
    refine ⟨_, by arun [], ?_⟩
    exact ⟨by simp [gpr_write, h₂.x23], by simp [gpr_write, h₂.x26], by simp [gpr_write],
      ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have he₃ := h₂.env.of_regs r₃
  have hd₃ : DataW Ctx (W + BitVec.ofNat 64 16) W s₃ D n := hdat.of_eq (by rw [r₃.rd, h₂.rd]) (by rw [r₃.wr, h₂.wr])
  have x22₃ : s₃.gpr .x22 = BitVec.ofNat 64 R := by rw [r₃.others _ (by decide), h₂.x22, h22]
  exact ⟨⟨he₃, x22₃, hR, by rw [r₃.others _ (by decide), h₂.x26], x27₃, by rw [r₃.others _ (by decide), h₂.x28, h28],
    by rw [r₃.mem]; exact h₂.hH, by rw [r₃.mem]; exact h₂.key, hd₃⟩, ⟨he₃, fun _ _ => rfl, x22₃, hR,
    by rw [r₃.others _ (by decide), h₂.x23], x24₃, x25₃, hd₃⟩⟩

/-- The arguments of the call on the whole blocks of the ciphertext. -/
theorem ctC_ok {H : Block} {R n : Nat} {D Tg : Addr} {s₄ : State} (h : Mid Ctx W SP H R n D Tg s₄)
    (h25 : s₄.gpr .x25 = BitVec.ofNat 64 0) :
    WP isa (.block ([mov .x23 .x27, mov .x24 .x26] ++ absSeg2 16)) s₄
      (Abs3 Ctx (W + BitVec.ofNat 64 16) W SP s₄.gpr 16 H [] D n 0 s₄.mem 0) := by
  rw [WP.block_append_iff]
  obtain ⟨s₅, run₅, x23₅, x24₅, r₅⟩ : ∃ s₅, runBlock isa [mov .x23 .x27, mov .x24 .x26] s₄ =
      some s₅ ∧ s₅.gpr .x23 = D ∧ s₅.gpr .x24 = BitVec.ofNat 64 n ∧ Regs [.x23, .x24] s₄ s₅ := by
    refine ⟨_, by arun [], ?_⟩
    exact ⟨by simp [gpr_write, h.x27], by simp [gpr_write, h.x26], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  have hM : AbsMid Ctx (W + BitVec.ofNat 64 16) W SP s₄.gpr 16 H [] D n 0 s₄.mem 0 s₅ :=
    ⟨h.env.of_regs r₅, fun r hr => r₅.others r (by
        simp only [keptRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> decide), Nat.zero_le _, by rw [x23₅]; simp,
      by rw [x24₅, Nat.sub_zero], by rw [r₅.others _ (by decide), h25],
      h.data.ok.of_eq r₅.rd r₅.wr, by rw [r₅.mem]; exact h.hH, fun ha => by rw [r₅.mem]; simpa [bytesAt] using ha,
      .inr rfl, by rw [r₅.mem]; exact Frame.refl _ _⟩
  exact absSeg2_ok L (.inr rfl) hM

/-- From the call on the whole blocks to the call of the tag: `H'` and `Y`
reloaded, the last bytes and the lengths absorbed, and the arguments of the
call. -/
theorem ctE_ok {H : Block} {R n : Nat} {D Tg : Addr} {s₄ s₇ : State} {x : List Byte} {j : Nat}
    (h : Mid Ctx W SP H R n D Tg s₇) (hm : AbsMid Ctx (W + BitVec.ofNat 64 16) W SP s₄.gpr 16 H x D n 0 s₄.mem j s₇)
    (hlt : n - j < 16) :
    WP isa (.seq (.block (Impl.AesGcm.AArch64.Fast.hReload ++ Impl.Gcm.AArch64.Pmull.loadRev Y .x20 16 ++
        [mov .x13 .x24, mov .x12 .x23])) (.seq Impl.AesGcm.AArch64.Fast.padMul (.block Impl.AesGcm.AArch64.Fast.lensTag))) s₇
      fun s => ∃ k Yv J m, Tag1 Ctx (W + BitVec.ofNat 64 16) W SP k 0 R Yv J m s ∧ k .x28 = Tg := by
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
  refine WP.mono (ldrev_ok Y .x20 16 s₈ (by decide) (by decide) (by rw [he₈.x20]; exact he₈.perm.stR (by decide)))
    fun s₉ ⟨l₉, o₉⟩ => ?_
  have he₉ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₉ := he₈.keep (fun r _ => by rw [o₉.gpr]) o₉.sp o₉.rd o₉.wr
  obtain ⟨s₁₀, run₁₀, x13₁₀, x12₁₀, r₁₀, v₁₀⟩ : ∃ s₁₀, runBlock isa [mov .x13 .x24, mov .x12 .x23] s₉ = some s₁₀ ∧
      s₁₀.gpr .x13 = BitVec.ofNat 64 (n - j) ∧ s₁₀.gpr .x12 = D + BitVec.ofNat 64 j ∧
      Regs [.x13, .x12] s₉ s₁₀ ∧ s₁₀.v = s₉.v := by
    refine ⟨_, by arun [], ?_⟩
    refine ⟨?_, ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩, rfl⟩
    · simp [gpr_write, o₉.gpr, g₈ .x24 (by decide), hm.x24]
    · simp [gpr_write, o₉.gpr, g₈ .x23 (by decide), hm.x23]
  refine WP.of_runBlock ⟨s₁₀, run₁₀, ?_⟩
  have he₁₀ := he₉.of_regs r₁₀
  have hk₁₀ : HKey H s₁₀ :=
    hk₈.of_v (by rw [v₁₀, o₉.v C (by decide)]) (by rw [v₁₀, o₉.v _ (by decide)]) (by rw [v₁₀, o₉.v _ (by decide)])
  have hdj : DataOk (W + BitVec.ofNat 64 16) W s₁₀ (D + BitVec.ofNat 64 j) (n - j) :=
    (h.data.ok.drop hjn).of_eq (by rw [r₁₀.rd, o₉.rd, rd₈]) (by rw [r₁₀.wr, o₉.wr, wr₈])
  refine WP.seq (WP.mono (WP.with_rdwr (padMul_ok (y := blockAt s₈.mem (s₈.gpr .x20 + BitVec.ofNat 64 16)) he₁₀ hk₁₀
    (by rw [v₁₀]; exact l₉) x12₁₀ x13₁₀ (by omega) hdj.rd
    (hdj.w.sub_right (Lay.wSub (by decide))))) fun s₁₁ ⟨⟨y₁₁, hk₁₁, he₁₁, og₁₁, f₁₁, v₁₁⟩, rd₁₁, wr₁₁⟩ => ?_)
  unfold Impl.AesGcm.AArch64.Fast.lensTag
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
  refine WP.mono (mulT_ok (y := padStep H (blockAt s₈.mem (s₈.gpr .x20 + BitVec.ofNat 64 16))
      (bytesAt s₁₀.mem (D + BitVec.ofNat 64 j) (n - j))) hk₁₂ (by rw [v₁₂]; exact y₁₁)
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
  exact WP.mono (tagSeg_ok L (o := 0) (.inl rfl) he₁₄ (fun _ _ => rfl : Kept s₁₄.gpr s₁₄) x22₁₄ h.rounds)
    fun s' h' => ⟨_, _, _, _, h', x28₁₄⟩

/-- `run` in two runs, from the same public pointers and lengths. -/
theorem run_rel (v : GcmImpl) {k₁ k₂ : Reg → BitVec 64} {H₁ H₂ : Block} {Np A D Tg : Addr} {al n R : Nat}
    {σ₁ σ₂ : State}
    (hJ₁ : J0In Ctx (W + BitVec.ofNat 64 16) W SP k₁ H₁ Np 12 σ₁)
    (hJ₂ : J0In Ctx (W + BitVec.ofNat 64 16) W SP k₂ H₂ Np 12 σ₂)
    (ha₁ : DataOk (W + BitVec.ofNat 64 16) W σ₁ A al) (ha₂ : DataOk (W + BitVec.ofNat 64 16) W σ₂ A al)
    (hal : al ≤ 16)
    (hx₁ : σ₁.gpr .x4 = A ∧ σ₁.gpr .x5 = BitVec.ofNat 64 al ∧ σ₁.gpr .x6 = D ∧ σ₁.gpr .x7 = BitVec.ofNat 64 n)
    (hx₂ : σ₂.gpr .x4 = A ∧ σ₂.gpr .x5 = BitVec.ofNat 64 al ∧ σ₂.gpr .x6 = D ∧ σ₂.gpr .x7 = BitVec.ofNat 64 n)
    (hd₁ : DataW Ctx (W + BitVec.ofNat 64 16) W σ₁ D n) (hd₂ : DataW Ctx (W + BitVec.ofNat 64 16) W σ₂ D n)
    (h22₁ : σ₁.gpr .x22 = BitVec.ofNat 64 R) (h22₂ : σ₂.gpr .x22 = BitVec.ofNat 64 R) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (h28₁ : σ₁.gpr .x28 = Tg) (h28₂ : σ₂.gpr .x28 = Tg) :
    RelCT isa (Eq2 σ₁ σ₂) (Impl.AesGcm.AArch64.Fast.run v.callees) TT := by
  obtain ⟨x4₁, x5₁, x6₁, x7₁⟩ := hx₁
  obtain ⟨x4₂, x5₂, x6₂, x7₂⟩ := hx₂
  unfold Impl.AesGcm.AArch64.Fast.run
  refine RelCT.seq_assoc (rel_seq (rel_taint [.x4, .x5, .x6, .x7, .x19, .x20, .x21, .x23]
      (by rw [hJ₁.env.sp, hJ₂.env.sp])
      (by agree_tac [x4₁, x4₂, x5₁, x5₂, x6₁, x6₂, x7₁, x7₂, hJ₁.env.x19, hJ₂.env.x19, hJ₁.env.x20, hJ₂.env.x20,
        hJ₁.env.x21, hJ₂.env.x21, hJ₁.x23, hJ₂.x23]) ⟨_, by taint_decide⟩)
    (ctA_ok L hJ₁ ha₁ hal x4₁ x5₁ x6₁ x7₁ hd₁ h22₁ hR h28₁) (ctA_ok L hJ₂ ha₂ hal x4₂ x5₂ x6₂ x7₂ hd₂ h22₂ hR h28₂)
    fun s₃ t₃ ⟨m₁, c₁⟩ ⟨m₂, c₂⟩ => ?_)
  refine rel_seq (cryptAl_rel L v c₁ c₂ (by decide)) (WP.with_rdwr (cryptAl_ok L v (icb := 0) c₁ (by decide)))
    (WP.with_rdwr (cryptAl_ok L v (icb := 0) c₂ (by decide))) fun s₄ t₄ ⟨o₁, rd₁, wr₁⟩ ⟨o₂, rd₂, wr₂⟩ => ?_
  have M₁ := Mid.crypt L m₁ o₁ rd₁ wr₁
  have M₂ := Mid.crypt L m₂ o₂ rd₂ wr₂
  refine rel_seq (rel_taint [.x19, .x20, .x21, .x26, .x27] (by rw [M₁.env.sp, M₂.env.sp])
      (by agree_tac [M₁.env.x19, M₂.env.x19, M₁.env.x20, M₂.env.x20, M₁.env.x21, M₂.env.x21, M₁.x26, M₂.x26,
        M₁.x27, M₂.x27]) ⟨_, by taint_decide⟩)
    (WP.with_rdwr (ctC_ok L M₁ o₁.x25)) (WP.with_rdwr (ctC_ok L M₂ o₂.x25)) fun s₅ t₅ ⟨a₁, rd₅, wr₅⟩ ⟨a₂, rd₅', wr₅'⟩ => ?_
  refine rel_seq (rel_gh v.gh a₁.call a₂.call (by rw [a₁.env.sp, a₂.env.sp]))
    (WP.with_rdwr (absCall2_ok L (.inr rfl) v a₁)) (WP.with_rdwr (absCall2_ok L (.inr rfl) v a₂))
    fun s₇ t₇ ⟨⟨b₁, l₁⟩, rd₇, wr₇⟩ ⟨⟨b₂, l₂⟩, rd₇', wr₇'⟩ => ?_
  have N₁ := Mid.absorb L M₁ b₁ (by rw [rd₇, rd₅]) (by rw [wr₇, wr₅])
  have N₂ := Mid.absorb L M₂ b₂ (by rw [rd₇', rd₅']) (by rw [wr₇', wr₅'])
  refine RelCT.seq_assoc3 (rel_seq (rel_taint [.x19, .x20, .x21, .x23, .x24, .x26] (by rw [N₁.env.sp, N₂.env.sp])
      (by agree_tac [N₁.env.x19, N₂.env.x19, N₁.env.x20, N₂.env.x20, N₁.env.x21, N₂.env.x21, b₁.x23, b₂.x23,
        b₁.x24, b₂.x24, N₁.x26, N₂.x26]) ⟨_, by taint_decide⟩)
    (ctE_ok L N₁ b₁ l₁) (ctE_ok L N₂ b₂ l₂) fun s₁₆ t₁₆ ⟨_, _, _, _, T₁, k28₁⟩ ⟨_, _, _, _, T₂, k28₂⟩ => ?_)
  refine rel_seq (rel_ctr v.ctr T₁.call T₂.call (by rw [T₁.env.sp, T₂.env.sp]))
    (tagCall_ok L v (.inl rfl) T₁) (tagCall_ok L v (.inl rfl) T₂) fun s₁₇ t₁₇ O₁ O₂ => ?_
  exact rel_taint [.x19, .x28] (by rw [O₁.env.sp, O₂.env.sp])
    (by agree_tac [O₁.env.x19, O₂.env.x19, O₁.kept .x28 (by decide), O₂.kept .x28 (by decide), k28₁, k28₂])
    ⟨_, by taint_decide⟩

end

/-- `SealEntered` after code that writes only `x9` and `x10`. -/
theorem SealEntered.of_regs {σ σ₀ τ τ' : State} (h : SealEntered σ σ₀ τ) (r : Regs [.x9, .x10] τ τ') :
    SealEntered σ σ₀ τ' := by
  obtain ⟨he, x22, x23, x24, x26, x27, x28, sA, sL, sD, sN, sT, f, sv, rd, wr⟩ := h
  exact ⟨he.of_regs r, by rw [r.others _ (by decide), x22], by rw [r.others _ (by decide), x23],
    by rw [r.others _ (by decide), x24], by rw [r.others _ (by decide), x26], by rw [r.others _ (by decide), x27],
    by rw [r.others _ (by decide), x28], by rw [r.mem, sA], by rw [r.mem, sL], by rw [r.mem, sD], by rw [r.mem, sN],
    by rw [r.mem, sT], by rw [r.mem]; exact f, by rw [r.mem]; exact sv, by rw [r.rd, rd], by rw [r.wr, wr]⟩

/-- `vg_aes_gcm_seal` with the path for TLS records is constant time. -/
theorem seal_ct (v : GcmImpl) :
    ConstantTime isa sealAArch64.pre sealAArch64.pub (Impl.AesGcm.AArch64.Fast.«seal» v.callees) := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  have hq₀ := hq
  obtain ⟨f₁, f₂⟩ := oneFacts (by decide : 1 < 2) (sealCore h₁) (sealCore h₂) hq
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, qsp, qa⟩ := hq
  have qt : stackArg σ₁ 0 = stackArg σ₂ 0 := qa 0 (by decide)
  have L := f₁.ol.lay
  have hT₁ : σ₁.mem.readW (σ₁.sp + BitVec.ofNat 64 0) 64 = stackArg σ₁ 0 := rfl
  have hT₂ : σ₂.mem.readW (σ₂.sp + BitVec.ofNat 64 0) 64 = stackArg σ₁ 0 := qt.symm
  have hW₁ : σ₁.mem.readW (σ₁.sp + BitVec.ofNat 64 8) 64 = stackArg σ₁ 1 := rfl
  have hW₂ : σ₂.mem.readW (σ₂.sp + BitVec.ofNat 64 8) 64 = stackArg σ₁ 1 := f₂.hW
  unfold Impl.AesGcm.AArch64.Fast.«seal»
  refine rel_seq (entryStash_rel (k := 8) (j := 0) (.inl rfl) rfl (.inl rfl) f₁ f₂ (by decide) qsp
      (by agree_tac [q0, q1, q2, q3, q4, q5, q6, q7]))
    (WP.block_and (entryStash_ok (V := stackArg σ₁ 0) (by decide) (by decide) hW₁ (f₁.hsp 1 (by decide))
      (f₁.hsp 0 (by decide)) hT₁ (f₁.argW (by decide)) rfl f₁.perm)
      (entry_keeps (by decide) (by decide) hW₁ (f₁.hsp 1 (by decide)) (f₁.hsp 0 (by decide)) f₁.perm.w))
    (WP.block_and (entryStash_ok (V := stackArg σ₁ 0) (by decide) (by decide) hW₂ (f₂.hsp 1 (by decide))
      (f₂.hsp 0 (by decide)) hT₂ (f₂.argW (by decide)) q0.symm f₂.perm)
      (entry_keeps (by decide) (by decide) hW₂ (f₂.hsp 1 (by decide)) (f₂.hsp 0 (by decide)) f₂.perm.w))
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
  have i₁ := frontIn_of f₁ rfl rfl rfl rfl rfl rfl b₁
  have i₂ := frontIn_of f₂ q3.symm q2.symm q4.symm q5.symm q6.symm q7.symm b₂
  rw [← qsp] at i₂
  rw [hc.2] at i₁ i₂
  have ol := f₁.ol
  have sub16 : Region.Sub ⟨stackArg σ₁ 1 + BitVec.ofNat 64 16, 80⟩ (workR (stackArg σ₁ 1)) := Lay.wSub (by decide)
  have hn := (σ₁.gpr .x7).isLt
  have g₁ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], u₁.gpr r = σ₁.gpr r := fun r hr => by
    rw [r₁.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), k₁ r hr]
  have g₂ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], u₂.gpr r = σ₁.gpr r := fun r hr => by
    rw [r₂.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), k₂ r hr]
    simp at hr; rcases hr with rfl | rfl | rfl | rfl
    · exact q4.symm
    · exact q5.symm
    · exact q6.symm
    · exact q7.symm
  have mkD : ∀ {σ u : State}, OneFacts σ σ₁ 2 1 → u.wr = σ.wr →
      DataW (σ₁.gpr .x0) (stackArg σ₁ 1 + BitVec.ofNat 64 16) (stackArg σ₁ 1) u (σ₁.gpr .x6) (σ₁.gpr .x7).toNat :=
    fun f wr => ⟨⟨covers_left (by rw [wr]; exact f.dataW), hn, ol.dw, ol.data.sub_right sub16, ol.data⟩,
      by rw [wr]; exact f.dataW, ol.cd⟩
  exact run_rel L v (Tg := stackArg σ₁ 0) (R := (σ₁.gpr .x1).toNat)
    ⟨i₁.env, i₁.kept, i₁.x23, i₁.x24, i₁.x26, i₁.x27, i₁.non, rfl⟩
    ⟨i₂.env, i₂.kept, i₂.x23, i₂.x24, i₂.x26, i₂.x27, i₂.non, rfl⟩ i₁.aad i₂.aad hc.1
    ⟨g₁ .x4 (by simp), by rw [g₁ .x5 (by simp), ofNat_toNat'], g₁ .x6 (by simp), by rw [g₁ .x7 (by simp), ofNat_toNat']⟩
    ⟨g₂ .x4 (by simp), by rw [g₂ .x5 (by simp), ofNat_toNat'], g₂ .x6 (by simp), by rw [g₂ .x7 (by simp), ofNat_toNat']⟩
    (mkD f₁ b₁.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2) (mkD f₂ b₂.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
    (by rw [b₁.2.1, ofNat_toNat']) (by rw [b₂.2.1, ← q1, ofNat_toNat']) ol.rounds b₁.2.2.2.2.2.2.1 b₂.2.2.2.2.2.2.1

end VG.Proof.AesGcm.AArch64.Fast
