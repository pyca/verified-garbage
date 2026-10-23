module

import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Run
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Run
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Tables
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.ShortBytes
import VerifiedGarbage.Proof.Gcm.Short
import VerifiedGarbage.Proof.AesGcm.AArch64.Cmp
import VerifiedGarbage.Proof.AesGcm.AArch64.Env
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Mul
import VerifiedGarbage.Proof.AesGcm.AArch64.Fn
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Seal
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Entry
public import VerifiedGarbage.Proof.AesGcm.AArch64.Seal
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.ShortCopy
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.ShortAes

/-!
# AES-GCM on AArch64, short records: `sealShort`

Untrusted: everything here is checked by Lean. `sealShort`
(`Impl/AesGcm/AArch64/Stitch.lean`) seals a record of 17 to 96 bytes as
`seal` does (`sealShort_ok`): `J₀` and the first counter block as `front`
leaves them (`j012_ok`, `initState_ok`), the table of keys (`TbFor`), one
`aesPart` over `B₁` and one `ghPart` over `B₂` (`Gh8Ok`), whose zero first
blocks leave GHASH from zero as it is (`ghashFrom_zeros`), and the counter
block `2³² − 1` steps after `inc₃₂(J₀)`, `J₀` (`repeat_inc32_pred`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64.Fast

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64 VG.WriteBytes
open VG.Proof.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ghash blocks zeros padLen ofBytes inc32 ctxH ctxCiph gctr)
open VG.Proof.Gcm.AArch64.Stitch (TblOk Gh8Ok)

/-- What `tb` must do, from a state of the path for TLS records: write the
table of keys of the context's hash subkey (`Stitch.TblPost`). -/
def TbFor (tb : List Instr) (w : Nat) (s : State) : Prop :=
  ∀ u : State, Env (s.gpr .x0) (stackArg s w + BitVec.ofNat 64 16) (stackArg s w) s.sp u →
    u.rd = s.rd → u.wr = s.wr →
    Frame [workR (stackArg s w), ⟨s.gpr .x6, (s.gpr .x7).toNat⟩] s.mem u.mem →
    KeyAt (Spec.Gcm.ctxH s.mem (s.gpr .x0)) u.mem (stackArg s w) →
    WP isa (.block tb) u (Stitch.TblPost (stackArg s w) (Spec.Gcm.ctxH s.mem (s.gpr .x0)) u)

/-- `TbFor` without the key `H'` at `W + hO`, which `pwTbl` does not read:
what the paths that never compute `H'` (`sealShort`) need of `tb`. -/
def TbForP (tb : List Instr) (w : Nat) (s : State) : Prop :=
  ∀ u : State, Env (s.gpr .x0) (stackArg s w + BitVec.ofNat 64 16) (stackArg s w) s.sp u →
    u.rd = s.rd → u.wr = s.wr →
    Frame [workR (stackArg s w), ⟨s.gpr .x6, (s.gpr .x7).toNat⟩] s.mem u.mem →
    WP isa (.block tb) u (Stitch.TblPost (stackArg s w) (Spec.Gcm.ctxH s.mem (s.gpr .x0)) u)

theorem TbForP.tbFor {tb : List Instr} {w : Nat} {s : State} (h : TbForP tb w s) : TbFor tb w s :=
  fun u he hrd hwr hf _ => h u he hrd hwr hf

theorem ofNat_lsr {n k : Nat} (hn : n < 2 ^ 64) : BitVec.ofNat 64 n >>> k = BitVec.ofNat 64 (n / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hn)]

/-- `shortThr`: `x9 = ⌊(n + 31) / 128⌋`, zero exactly when `n ≤ shortMax`. -/
theorem shortThr_ok {n : Nat} (s : State) (h7 : s.gpr .x7 = BitVec.ofNat 64 n) (hn : n + 31 < 2 ^ 64) :
    WP isa (.block Impl.AesGcm.AArch64.Stitch.shortThr) s fun s' =>
      s'.gpr .x9 = BitVec.ofNat 64 ((n + 31) / 128) ∧ Regs [.x9, .x10] s s' := by
  refine WP.of_runBlock ⟨_, by arun [Impl.AesGcm.AArch64.Stitch.shortThr, Impl.AesGcm.AArch64.Stitch.shortMax], ?_⟩
  refine ⟨?_, by others_tac, rfl, rfl, rfl, rfl⟩
  simp only [gpr_write, ite_true, h7, State.read, BitVec.setWidth_eq, Size.bits]
  rw [BitVec.ofNat_add_ofNat, ofNat_lsr hn]

/-- `shortMin`: `x9 = ⌊(n + 15) / 32⌋`, zero exactly when `n ≤ 16`. -/
theorem shortMin_ok {n : Nat} (s : State) (h7 : s.gpr .x7 = BitVec.ofNat 64 n) (hn : n + 15 < 2 ^ 64) :
    WP isa (.block Impl.AesGcm.AArch64.Stitch.shortMin) s fun s' =>
      s'.gpr .x9 = BitVec.ofNat 64 ((n + 15) / 32) ∧ Regs [.x9, .x10] s s' := by
  refine WP.of_runBlock ⟨_, by arun [Impl.AesGcm.AArch64.Stitch.shortMin], ?_⟩
  refine ⟨?_, by others_tac, rfl, rfl, rfl, rfl⟩
  simp only [gpr_write, ite_true, h7, State.read, BitVec.setWidth_eq, Size.bits]
  rw [BitVec.ofNat_add_ofNat, ofNat_lsr hn]

/-- A region apart from the 2560 bytes of the working space, neither wrapping
around, is at most `2⁶⁴ − 2560` bytes long. -/
theorem len_of_disjoint {D W : Addr} {n : Nat} (hd : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hD : D.toNat + n ≤ 2 ^ 64) (hW : W.toNat + 2560 ≤ 2 ^ 64) : n + 2560 ≤ 2 ^ 64 := by
  refine Classical.byContradiction fun h => ?_
  by_cases hDW : D.toNat ≤ W.toNat
  · refine hd W ?_ ?_
    · simp only [Region.Contains, BitVec.toNat_sub]; omega
    · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  · refine hd D ?_ ?_
    · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
    · simp only [Region.Contains, BitVec.toNat_sub]; omega

open VG.Proof.Gcm.AArch64.Stitch (TblOk) in
/-- The table, outside a frame apart from it. -/
theorem tblOk_frame {m m' : Mem} {W : Addr} {H : Block} {rs : List Region} (h : TblOk m W H) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (Stitch.tblR W).Disjoint r) : TblOk m' W H where
  sw k h₁ h₂ := by
    rw [hf.readW (r := ⟨W + BitVec.ofNat 64 (Impl.Gcm.AArch64.Stitch.sOff k), 16⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (Offset.sub W (by unfold Impl.Gcm.AArch64.Stitch.sOff Impl.Gcm.AArch64.Stitch.tbl; omega)
        (by unfold Impl.Gcm.AArch64.Stitch.sOff Impl.Gcm.AArch64.Stitch.tbl; omega))) (by decide)]
    exact h.sw k h₁ h₂
  key p hp := by
    rw [hf.readW (r := ⟨W + BitVec.ofNat 64 (Impl.Gcm.AArch64.Stitch.kOff p), 16⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (Offset.sub W (by unfold Impl.Gcm.AArch64.Stitch.kOff Impl.Gcm.AArch64.Stitch.tbl; omega)
        (by unfold Impl.Gcm.AArch64.Stitch.kOff Impl.Gcm.AArch64.Stitch.tbl; omega))) (by decide)]
    exact h.key p hp

/-- `sealShort`, from the entry of `seal`, for a record of 17 to 96 bytes. -/
theorem sealShort_ok (gh : Gh8Ok) {tb : List Instr} {w : Nat} {extra extraW : List Region} {s s₁ : State}
    (hs : sealPreXW w extra s extraW) (htb : TbForP tb w s)
    (h₁ : SealEntry w s s₁) (hx : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], s₁.gpr r = s.gpr r)
    (h12 : (s.gpr .x3).toNat = 12) (h16 : (s.gpr .x5).toNat ≤ 16)
    (hlo : 17 ≤ (s.gpr .x7).toNat) (hhi : (s.gpr .x7).toNat ≤ 96) :
    WP isa (Impl.AesGcm.AArch64.Stitch.sealShort tb) s₁ fun s' => GprAbi s s' ∧ sealAArch64.post s s' := by
  obtain ⟨he₁, x22₁, x23₁, x24₁, x26₁, x27₁, x28₁, sl₁, sl₂, sl₃, sl₄, sl₅, f₁, sv₁, rd₁, wr₁⟩ := h₁
  have hx4 := hx .x4 (by simp)
  have hx5 := hx .x5 (by simp)
  have hx6 := hx .x6 (by simp)
  have hx7 := hx .x7 (by simp)
  obtain ⟨ol, tW, dtw, ddt⟩ := sealLay hs
  simp only [sealAArch64]
  obtain ⟨L, perm, hsp, dnW, daW, ddW, dcW, daA, dnd, dad, dcd, wn, wa, wd, hR, nR, aR, dW⟩ := ol
  have h3 := ofNat_toNat' (s.gpr .x3)
  have h5 := ofNat_toNat' (s.gpr .x5)
  have h7 := ofNat_toNat' (s.gpr .x7)
  have htb' := htb
  unfold TbForP at htb'
  generalize hW : stackArg s w = W at *
  generalize hTg : stackArg s 0 = Tg at *
  generalize hCtx : s.gpr .x0 = Ctx at *
  generalize hRR : (s.gpr .x1).toNat = R at *
  generalize hNp : s.gpr .x2 = Np at *
  generalize hnl : (s.gpr .x3).toNat = nl at *
  generalize hA : s.gpr .x4 = A at *
  generalize hal : (s.gpr .x5).toNat = al at *
  generalize hD : s.gpr .x6 = D at *
  generalize hn : (s.gpr .x7).toNat = n at *
  subst h12
  have hRb : R = 10 ∨ R = 12 ∨ R = 14 := by rw [← hRR]; exact hR
  unfold Impl.AesGcm.AArch64.Stitch.sealShort Impl.AesGcm.AArch64.Stitch.shortPre
  have sub16 : Region.Sub ⟨W + BitVec.ofNat 64 16, 80⟩ (workR W) := Lay.wSub (by decide)
  have kc := keep_of_sub (entryR_work W) (dcW.sub_left (Lay.ctxSub (d := 240) (n := 16) (by decide)))
  have hH₁ : blockAt s₁.mem (Ctx + BitVec.ofNat 64 240) = ctxH s.mem Ctx := blockAt_frame f₁ kc
  have hnon : DataOk (W + BitVec.ofNat 64 16) W s₁ Np 12 :=
    ⟨by rw [rd₁, wr₁]; exact nR, hnl ▸ (s.gpr .x3).isLt, wn, dnW.sub_right sub16, dnW⟩
  have iv₁ : bytesAt s₁.mem Np 12 = bytesAt s.mem Np 12 :=
    bytesAt_frame f₁ (keep_of_sub (entryR_work W) dnW) (by omega_arith)
  have hJ : J0In Ctx (W + BitVec.ofNat 64 16) W s.sp s₁.gpr (ctxH s.mem Ctx) Np 12 s₁ :=
    ⟨he₁, fun _ _ => rfl, x23₁, by rw [x24₁, ← h3], by rw [x26₁, ← h3], x27₁, hnon, hH₁⟩
  generalize hc : (n + 15) / 16 = c
  have hc1 : 2 ≤ c := by omega_arith
  have hc6 : c ≤ 6 := by omega_arith
  have hcn : n ≤ 16 * c := by omega_arith
  have hcn' : 16 * c ≤ n + 15 := by omega_arith
  -- `J₀`, the first counter block, and the lengths.
  refine WP.seq (WP.seq (WP.block_append_iff.mpr (WP.block_append_iff.mpr
    (WP.mono (WP.with_rdwr (WP.block_and (j012_ok L hJ) (j012_others hJ))) fun s₂ ⟨⟨h₂, o₂⟩, rd₂, wr₂⟩ =>
      WP.mono (WP.with_rdwr (WP.block_and (initState_ok L h₂) (initState_others h₂.env)))
        fun s₃ ⟨⟨h₃, o₃⟩, rd₃, wr₃⟩ => ?_))))
  rw [iv₁] at h₃
  have o₁₃ : ∀ r ∉ [Reg.x9, .x10, .x11, .x12], s₃.gpr r = s₁.gpr r := fun r hr => by rw [o₃ r hr, o₂ r hr]
  have F₃ : Frame [workR W, ⟨D, n⟩] s.mem s₃.mem := by
    have wE : ∀ {r : Region}, Region.Sub r (workR W) → ∃ r' ∈ [workR W, (⟨D, n⟩ : Region)], Region.Sub r r' :=
      fun h => ⟨_, List.mem_cons_self .., h⟩
    have j0W : ∀ r ∈ j0Frame (W + BitVec.ofNat 64 16) W, Region.Sub r (workR W) := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub16
      · exact Lay.wSub (by decide)
      · exact Lay.wSub (by decide)
    exact (f₁.sub fun r hr => wE (entryR_work W r hr)).trans (h₃.frame.sub fun r hr => wE (j0W r hr))
  refine WP.mono (Stitch.shortLen_ok (n := n) (D := D) (al := al) s₃ (by rw [o₁₃ _ (by decide), hx7, ← h7])
    (by rw [o₁₃ _ (by decide), hx6]) (by rw [o₁₃ _ (by decide), hx5, ← h5]) (by omega_arith))
    fun t₀ ⟨x26₅, x27₅, x24₅, x25₅, g₅, m₅, v₅, sp₅, rd₅, wr₅⟩ => ?_
  rw [hc] at x25₅
  have he₅ : Env Ctx (W + BitVec.ofNat 64 16) W s.sp t₀ := h₃.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₅ _ (by decide) (by decide) (by decide) (by decide)) sp₅ rd₅ wr₅
  -- The table.
  refine WP.seq (WP.mono (htb' t₀ he₅ (by rw [rd₅, rd₃, rd₂, rd₁]) (by rw [wr₅, wr₃, wr₂, wr₁])
    (by rw [m₅]; exact F₃)) fun s₄ ⟨tbl₄, ft₄, g₄, sp₄, rd₄, wr₄⟩ => ?_)
  rw [m₅] at ft₄
  have he₄ : Env Ctx (W + BitVec.ofNat 64 16) W s.sp s₄ := he₅.keep (fun r hr => g₄ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₄ rd₄ wr₄
  -- The buffers zeroed.
  refine WP.mono (Stitch.zeroBufs_ok (c := c) hc6 s₄ he₄.x19 (by rw [g₄ _ (by decide), x25₅])
    he₄.perm.w) fun s₆ ⟨m₆, g₆, sp₆, rd₆, wr₆⟩ => ?_
  have he₆ : Env Ctx (W + BitVec.ofNat 64 16) W s.sp s₆ := he₄.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₆ _ (by decide)) sp₆ rd₆ wr₆
  have x25₆ : s₆.gpr .x25 = BitVec.ofNat 64 (16 * c) := by rw [g₆ _ (by decide), g₄ _ (by decide), x25₅]
  have x26₆ : s₆.gpr .x26 = BitVec.ofNat 64 n := by rw [g₆ _ (by decide), g₄ _ (by decide), x26₅]
  have x27₆ : s₆.gpr .x27 = D := by rw [g₆ _ (by decide), g₄ _ (by decide), x27₅]
  have x24₆ : s₆.gpr .x24 = BitVec.ofNat 64 al := by rw [g₆ _ (by decide), g₄ _ (by decide), x24₅]
  have x4₆ : s₆.gpr .x4 = A := by
    rw [g₆ _ (by decide), g₄ _ (by decide), g₅ _ (by decide) (by decide) (by decide) (by decide),
      o₁₃ _ (by decide), hx4]
  have rd₆' : s₆.rd = s.rd := by rw [rd₆, rd₄, rd₅, rd₃, rd₂, rd₁]
  have wr₆' : s₆.wr = s.wr := by rw [wr₆, wr₄, wr₅, wr₃, wr₂, wr₁]
  -- The text, to block `p` of `B₁`.
  unfold Impl.AesGcm.AArch64.Stitch.textIn
  refine WP.seq (WP.seq ?_)
  rw [WP.block_append_iff]
  obtain ⟨t₁, run₁, x11₁, g₁', m₁', v₁', sp₁', rd₁', wr₁'⟩ := Stitch.atP_ok (c := c) .x11
    Impl.AesGcm.AArch64.Stitch.b1O 1 (by decide) (by unfold Impl.AesGcm.AArch64.Stitch.b1O; omega_arith) s₆ he₆.x19
    x25₆ (by decide)
  refine WP.of_runBlock ⟨t₁, run₁, ?_⟩
  obtain ⟨s₇, run₇, x12₇, x13₇, r₇⟩ : ∃ s₇, runBlock isa [mov .x12 .x27, mov .x13 .x26] t₁ = some s₇ ∧
      s₇.gpr .x12 = D ∧ s₇.gpr .x13 = BitVec.ofNat 64 n ∧ Regs [.x12, .x13] t₁ s₇ := by
    refine ⟨_, by arun [], ?_⟩
    exact ⟨by simp [gpr_write, g₁' .x27 (by decide), x27₆], by simp [gpr_write, g₁' .x26 (by decide), x26₆],
      ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  refine WP.of_runBlock ⟨s₇, run₇, ?_⟩
  have x11₇ : s₇.gpr .x11 = W + BitVec.ofNat 64 (880 - 16 * c) := by
    rw [r₇.others _ (by decide), x11₁]; rfl
  have rd₇ : s₇.rd = s.rd := by rw [r₇.rd, rd₁', rd₆']
  have wr₇ : s₇.wr = s.wr := by rw [r₇.wr, wr₁', wr₆']
  have m₇ : s₇.mem = s₆.mem := by rw [r₇.mem, m₁']
  refine WP.mono (Stitch.copyQ_ok s₇ ⟨x12₇, x11₇, x13₇, by omega_arith, by rw [rd₇, wr₇]; exact covers_left dW,
    by rw [wr₇]; exact covers_off perm.w (by omega_arith) (by decide),
    ddW.sub_right (Lay.wSub (by omega_arith))⟩) fun s₈ ⟨m₈, g₈, sp₈, rd₈, wr₈⟩ => ?_
  have he₈ : Env Ctx (W + BitVec.ofNat 64 16) W s.sp s₈ := he₆.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> rw [g₈ _ (by decide), r₇.others _ (by decide), g₁' _ (by decide)])
    (by rw [sp₈, r₇.sp, sp₁']) (by rw [rd₈, r₇.rd, rd₁']) (by rw [wr₈, r₇.wr, wr₁'])
  have x25₈ : s₈.gpr .x25 = BitVec.ofNat 64 (16 * c) := by
    rw [g₈ _ (by decide), r₇.others _ (by decide), g₁' _ (by decide), x25₆]
  -- The counter, and one pass of AES over `B₁`.
  refine WP.seq (WP.mono (Stitch.shortCtr_ok (W := W) (St := W + BitVec.ofNat 64 16) hc6 s₈ he₈.x19
    he₈.x20 x25₈ (he₈.perm.stR (by decide))) fun s₉ ⟨x10₉, x9₉, g₉, m₉, v₉, sp₉, rd₉, wr₉⟩ => ?_)
  have he₉ : Env Ctx (W + BitVec.ofNat 64 16) W s.sp s₉ := he₈.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₉ _ (by decide) (by decide)) sp₉ rd₉ wr₉
  have x22₉ : s₉.gpr .x22 = BitVec.ofNat 64 R := by
    rw [g₉ _ (by decide) (by decide), g₈ _ (by decide), r₇.others _ (by decide), g₁' _ (by decide),
      g₆ _ (by decide), g₄ _ (by decide), g₅ _ (by decide) (by decide) (by decide) (by decide),
      h₃.kept .x22 (by decide),
      x22₁, ← hRR, ofNat_toNat']
  have hp₉ : Proof.Gcm.AArch64.Stitch.APre R 0 (2 ^ 32 + c - 7) s₉ := {
    rounds := hRb
    o_le := by decide
    keys := fun r hr => by
      rw [Proof.Gcm.AArch64.Stitch.kp, he₉.x21]
      exact in_off he₉.perm.ctx (by omega_arith) (by decide)
    ctr := by
      rw [Proof.Gcm.AArch64.Stitch.cbA, he₉.x20, add_ofNat_zero]
      exact he₉.perm.stR (by decide)
    data := fun j hj => by
      rw [x9₉, Offset.add_add]
      exact he₉.perm.wR (by unfold Impl.AesGcm.AArch64.Stitch.b1O; omega_arith)
    x10 := by
      rw [x10₉]
      simp only [Proof.Gcm.AArch64.Stitch.c0, Proof.Gcm.AArch64.Stitch.cbk, Proof.Gcm.AArch64.Stitch.cbA, m₉,
        he₉.x20] }
  refine WP.seq (WP.mono (Stitch.shortAesB_ok s₉ hp₉ x22₉ x9₉ (covers_off he₉.perm.w (by decide) (by decide)))
    fun s₁₀ ⟨ks₁₀, f₁₀, g₁₀, sp₁₀, rd₁₀, wr₁₀, _⟩ => ?_)
  have he₁₀ : Env Ctx (W + BitVec.ofNat 64 16) W s.sp s₁₀ := he₉.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₁₀ _ (by decide)) sp₁₀ rd₁₀ wr₁₀
  have x25₁₀ : s₁₀.gpr .x25 = BitVec.ofNat 64 (16 * c) := by
    rw [g₁₀ _ (by decide), g₉ _ (by decide) (by decide), x25₈]
  have k₁₀ : ∀ r ∈ [Reg.x4, .x24, .x26, .x27, .x28], s₁₀.gpr r = s₆.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      rw [g₁₀ _ (by decide), g₉ _ (by decide) (by decide), g₈ _ (by decide), r₇.others _ (by decide),
        g₁' _ (by decide)]
  have rd₁₀' : s₁₀.rd = s.rd := by rw [rd₁₀, rd₉, rd₈, rd₇]
  have wr₁₀' : s₁₀.wr = s.wr := by rw [wr₁₀, wr₉, wr₈, wr₇]
  -- The ciphertext, to the text and to `B₂`.
  unfold Impl.AesGcm.AArch64.Stitch.textOut
  refine WP.seq (WP.seq ?_)
  rw [WP.block_append_iff]
  obtain ⟨t₂, run₂, x12t₂, g₂', m₂', -, sp₂', rd₂', wr₂'⟩ := Stitch.atP_ok (c := c) .x12
    Impl.AesGcm.AArch64.Stitch.b1O 1 (by decide) (by unfold Impl.AesGcm.AArch64.Stitch.b1O; omega_arith) s₁₀ he₁₀.x19
    x25₁₀ (by decide)
  refine WP.of_runBlock ⟨t₂, run₂, ?_⟩
  obtain ⟨s₁₁, run₁₁, x11₁₁, x13₁₁, r₁₁⟩ : ∃ s₁₁, runBlock isa [mov .x11 .x27, mov .x13 .x26] t₂ = some s₁₁ ∧
      s₁₁.gpr .x11 = D ∧ s₁₁.gpr .x13 = BitVec.ofNat 64 n ∧ Regs [.x11, .x13] t₂ s₁₁ := by
    refine ⟨_, by arun [], ?_⟩
    exact ⟨by simp [gpr_write, g₂' .x27 (by decide), k₁₀ .x27 (by simp), x27₆],
      by simp [gpr_write, g₂' .x26 (by decide), k₁₀ .x26 (by simp), x26₆], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  refine WP.of_runBlock ⟨s₁₁, run₁₁, ?_⟩
  have x12₁₁ : s₁₁.gpr .x12 = W + BitVec.ofNat 64 (880 - 16 * c) := by
    rw [r₁₁.others _ (by decide), x12t₂]; rfl
  have rd₁₁ : s₁₁.rd = s.rd := by rw [r₁₁.rd, rd₂', rd₁₀']
  have wr₁₁ : s₁₁.wr = s.wr := by rw [r₁₁.wr, wr₂', wr₁₀']
  have m₁₁ : s₁₁.mem = s₁₀.mem := by rw [r₁₁.mem, m₂']
  refine WP.seq (WP.mono (Stitch.copyQ_ok s₁₁ ⟨x12₁₁, x11₁₁, x13₁₁, by omega_arith,
    by rw [rd₁₁, wr₁₁]; exact covers_left (covers_off perm.w (by omega_arith) (by decide)),
    by rw [wr₁₁]; exact dW, (ddW.sub_right (Lay.wSub (by omega_arith))).symm⟩) fun s₁₂ ⟨m₁₂, g₁₂, sp₁₂, rd₁₂, wr₁₂⟩ => ?_)
  have k₁₂ : ∀ r ∈ [Reg.x4, .x19, .x20, .x21, .x24, .x25, .x26, .x27, .x28], s₁₂.gpr r = s₁₀.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [g₁₂ _ (by decide), r₁₁.others _ (by decide), g₂' _ (by decide)]
  have he₁₂ : Env Ctx (W + BitVec.ofNat 64 16) W s.sp s₁₂ := he₁₀.keep (fun r hr => k₁₂ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp))
    (by rw [sp₁₂, r₁₁.sp, sp₂']) (by rw [rd₁₂, rd₁₁, rd₁₀']) (by rw [wr₁₂, wr₁₁, wr₁₀'])
  refine WP.mono (Stitch.ctToB2_ok (by omega_arith) hc6 hcn s₁₂ he₁₂.x19 (by rw [k₁₂ .x25 (by simp), x25₁₀])
    (by rw [k₁₂ .x26 (by simp), k₁₀ .x26 (by simp), x26₆]) he₁₂.perm.w) fun s₁₃ ⟨m₁₃, g₁₃, sp₁₃, rd₁₃, wr₁₃⟩ => ?_
  have k₁₃ : ∀ r ∈ [Reg.x4, .x19, .x20, .x21, .x24, .x25, .x26, .x27, .x28], s₁₃.gpr r = s₁₀.gpr r := fun r hr => by
    have hr' : r ∉ [Reg.x9, .x11, .x12, .x13, .x14, .x15] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [g₁₃ r hr', k₁₂ r hr]
  have he₁₃ : Env Ctx (W + BitVec.ofNat 64 16) W s.sp s₁₃ := he₁₂.keep (fun r hr => g₁₃ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) sp₁₃ rd₁₃ wr₁₃
  -- The additional data, to `B₂`.
  refine WP.seq (WP.mono (Stitch.aadIn_ok (A := A) (al := al) hc6 s₁₃ he₁₃.x19
    (by rw [k₁₃ .x25 (by simp), x25₁₀]) he₁₃.perm.w (by rw [k₁₃ .x4 (by simp), k₁₀ .x4 (by simp), x4₆])
    (by rw [k₁₃ .x24 (by simp), k₁₀ .x24 (by simp), x24₆]) h16
    (by rw [rd₁₃, wr₁₃, rd₁₂, wr₁₂, rd₁₁, wr₁₁]; exact aR) (daW.sub_right (Lay.wSub (by omega_arith))))
    fun s₁₄ ⟨m₁₄, g₁₄, sp₁₄, rd₁₄, wr₁₄⟩ => ?_)
  have k₁₄ : ∀ r ∈ [Reg.x4, .x19, .x20, .x21, .x24, .x25, .x26, .x27, .x28], s₁₄.gpr r = s₁₀.gpr r := fun r hr => by
    have hr' : r ∉ [Reg.x11, .x12, .x13, .x14, .x15] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [g₁₄ r hr', k₁₃ r hr]
  have he₁₄ : Env Ctx (W + BitVec.ofNat 64 16) W s.sp s₁₄ := he₁₃.keep (fun r hr => g₁₄ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) sp₁₄ rd₁₄ wr₁₄
  have x26₁₄ : s₁₄.gpr .x26 = BitVec.ofNat 64 n := by rw [k₁₄ .x26 (by simp), k₁₀ .x26 (by simp), x26₆]
  have x24₁₄ : s₁₄.gpr .x24 = BitVec.ofNat 64 al := by rw [k₁₄ .x24 (by simp), k₁₀ .x24 (by simp), x24₆]
  -- The lengths block, GHASH, the tag, and the exit.
  simp only [Impl.AesGcm.AArch64.Stitch.shortTag, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (Stitch.lensB_ok s₁₄ he₁₄.x19 he₁₄.perm.w x24₁₄ x26₁₄ (by omega_arith) (by omega_arith))
    fun s₁₅ ⟨lens₁₅, fL₁₅, og₁₅, sp₁₅, rd₁₅, wr₁₅, _⟩ => ?_
  have he₁₅ : Env Ctx (W + BitVec.ofNat 64 16) W s.sp s₁₅ := he₁₄.keep (fun r hr => og₁₅ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) sp₁₅ rd₁₅ wr₁₅
  -- What the writes since the table keep.
  let BR : Region := ⟨W + BitVec.ofNat 64 768, 256⟩
  have one : ∀ {m m' : Mem} {q : Addr} {k : Nat}, Frame [⟨q, k⟩] m m' →
      (∃ r' ∈ [BR, ⟨D, n⟩], Region.Sub ⟨q, k⟩ r') → Frame [BR, ⟨D, n⟩] m m' := fun h hs =>
    h.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hs
  have wB : ∀ {e k : Nat}, 768 ≤ e → e + k ≤ 1024 → ∃ r' ∈ [BR, ⟨D, n⟩],
      Region.Sub ⟨W + BitVec.ofNat 64 e, k⟩ r' := fun h₁ h₂ => ⟨_, List.mem_cons_self .., Offset.sub W h₁ (by omega_arith)⟩
  have wD : ∃ r' ∈ [BR, ⟨D, n⟩], Region.Sub ⟨D, n⟩ r' := ⟨_, by simp, fun _ h => h⟩
  have F₄₉ : Frame [BR, ⟨D, n⟩] s₄.mem s₉.mem := by
    rw [m₉, m₈, m₇, m₆]
    exact ((one (writeBytes_frame' _ List.length_replicate) (wB (by decide) (by decide))).trans
      (one (writeBytes_frame' _ List.length_replicate) (wB (by omega_arith) (by omega_arith)))).trans
      (one (writeBytes_frame' _ (Proof.AesCcm.length_bytesAt _ _ _)) (wB (by omega_arith) (by omega_arith)))
  have F₉₁₅ : Frame [BR, ⟨D, n⟩] s₉.mem s₁₅.mem := by
    have a₁ : Frame [BR, ⟨D, n⟩] s₉.mem s₁₀.mem := one f₁₀ (wB (by decide) (by decide))
    have a₂ : Frame [BR, ⟨D, n⟩] s₁₀.mem s₁₂.mem := by
      rw [m₁₂, m₁₁]; exact one (writeBytes_frame' _ (Proof.AesCcm.length_bytesAt _ _ _)) wD
    have a₃ : Frame [BR, ⟨D, n⟩] s₁₂.mem s₁₃.mem := by
      rw [m₁₃]
      exact (one (writeBytes_frame' _ (Proof.AesCcm.length_bytesAt _ _ _)) (wB (by omega_arith) (by omega_arith))).trans
        (one (writeBytes_frame' _ List.length_replicate) (wB (by omega_arith) (by omega_arith)))
    have a₄ : Frame [BR, ⟨D, n⟩] s₁₃.mem s₁₄.mem := by
      rw [m₁₄]; exact one (writeBytes_frame' _ (Proof.AesCcm.length_bytesAt _ _ _)) (wB (by omega_arith) (by omega_arith))
    exact (((a₁.trans a₂).trans a₃).trans a₄).trans (one fL₁₅ (wB (by decide) (by decide)))
  have dBR : ∀ {X : Region}, X.Disjoint (workR W) → X.Disjoint ⟨D, n⟩ → ∀ r ∈ [BR, ⟨D, n⟩], X.Disjoint r :=
    fun h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h₁.sub_right (Lay.wSub (by decide))
      · exact h₂
  have dWBR : ∀ {e k : Nat}, e + k ≤ 768 → ∀ r ∈ [BR, ⟨D, n⟩], (⟨W + BitVec.ofNat 64 e, k⟩ : Region).Disjoint r :=
    fun h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint W (.inl h) (by omega_arith) (by decide)
      · exact (ddW.sub_right (Lay.wSub (by omega_arith))).symm
  have tbl₁₅ : TblOk s₁₅.mem W (ctxH s.mem Ctx) :=
    tblOk_frame (tblOk_frame tbl₄ F₄₉ (dWBR (by decide))) F₉₁₅ (dWBR (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (Stitch.shortGh_ok gh s₁₅ he₁₅.x19 tbl₁₅ (covers_left he₁₅.perm.w))
    fun s₁₆ ⟨y₁₆, g₁₆, m₁₆, sp₁₆, rd₁₆, wr₁₆⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (Stitch.shortTagAt_ok (W := W) (o := 0) (.inl rfl) hc6 s₁₆ (by rw [g₁₆ _ (by decide) (by decide),
      he₁₅.x19]) (by rw [g₁₆ _ (by decide) (by decide), og₁₅ _ (by decide), k₁₄ .x25 (by simp), x25₁₀]) y₁₆
      (by rw [wr₁₆, wr₁₅]; exact he₁₄.perm.w))
    fun s₁₇ ⟨tag₁₇, fT₁₇, g₁₇, sp₁₇, rd₁₇, wr₁₇⟩ => ?_
  have k₁₇ : ∀ r ∈ [Reg.x19, .x20, .x21, .x28], s₁₇.gpr r = s₁₄.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      rw [g₁₇ _ (by decide), g₁₆ _ (by decide) (by decide), og₁₅ _ (by decide)]
  have x28₁₇ : s₁₇.gpr .x28 = Tg := by
    rw [k₁₇ .x28 (by simp), k₁₄ .x28 (by simp), k₁₀ .x28 (by simp), g₆ _ (by decide), g₄ _ (by decide),
      g₅ _ (by decide) (by decide) (by decide) (by decide), h₃.kept .x28 (by decide), x28₁]
  have he₁₇ : Env Ctx (W + BitVec.ofNat 64 16) W s.sp s₁₇ := he₁₄.keep (fun r hr => k₁₇ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl <;> simp)) (by rw [sp₁₇, sp₁₆, sp₁₅]) (by rw [rd₁₇, rd₁₆, rd₁₅])
    (by rw [wr₁₇, wr₁₆, wr₁₅])
  have rd₁₇' : s₁₇.rd = s.rd := by rw [rd₁₇, rd₁₆, rd₁₅, rd₁₄, rd₁₃, rd₁₂, rd₁₁]
  have wr₁₇' : s₁₇.wr = s.wr := by rw [wr₁₇, wr₁₆, wr₁₅, wr₁₄, wr₁₃, wr₁₂, wr₁₁]
  rw [WP.block_append_iff]
  refine WP.mono (tagOut_ok he₁₇.x19 x28₁₇ (covers_left he₁₇.perm.w) (by rw [wr₁₇']; exact tW)
    (dtw.sub_right (Region.sub_prefix (by decide)))) fun s₁₈ ⟨out₁₈, f₁₈, og₁₈, sp₁₈, rd₁₈, wr₁₈⟩ => ?_
  have he₁₈ : Env Ctx (W + BitVec.ofNat 64 16) W s.sp s₁₈ := he₁₇.keep (fun r hr => og₁₈ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₁₈ rd₁₈ wr₁₈
  have sv₁₈ : SavedAt s₁₈.mem W s := by
    refine ((((sv₁.frame h₃.frame (saved_j0Frame L)).frame ft₄ fun r hr => ?_).frame (F₄₉.trans F₉₁₅)
      fun r hr => ?_).frame (by rw [← m₁₆, ← add_ofNat_zero W]; exact fT₁₇) (saved_tag16 L)).frame f₁₈ fun r hr => ?_
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)
      · exact (ddW.sub_right (Lay.wSub (by decide))).symm
    · simp only [List.mem_singleton] at hr; subst hr
      exact (dtw.sub_right (Lay.wSub (by decide))).symm
  refine WP.mono (exit_ok he₁₈.x19 he₁₈.sp (covers_left he₁₈.perm.w) sv₁₈) fun s' ⟨ga, hm, _⟩ => ⟨ga, ?_⟩
  rw [hm]
  simp only [Impl.AesGcm.AArch64.Stitch.b2O, Impl.AesGcm.AArch64.Stitch.b1O] at m₆ ks₁₀ y₁₆ f₁₀ tag₁₇
  have lb := Proof.AesCcm.length_bytesAt
  have selfB : ∀ (m : Mem) (q : Addr) (xs : List Byte) {k : Nat}, xs.length = k → k < 2 ^ 64 →
      bytesAt (writeBytes m q xs) q k = xs := fun m q xs _ hk hk' => by
    subst hk; exact bytesAt_writeBytes_self m q xs hk'
  have wf : ∀ (m : Mem) (q : Addr) (xs : List Byte) {k : Nat}, xs.length = k →
      Frame [⟨q, k⟩] m (writeBytes m q xs) := fun m _ _ _ hk => writeBytes_frame' m hk
  have one1 : ∀ {X r : Region}, X.Disjoint r → ∀ r' ∈ [r], X.Disjoint r' := fun h r' hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'; exact h
  have dWW : ∀ {d k e j : Nat}, d + k ≤ e ∨ e + j ≤ d → d + k ≤ 2560 → e + j ≤ 2560 →
      (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, j⟩ :=
    fun h h₁ h₂ => Offset.disjoint W h (by omega_arith) (by omega_arith)
  have dDW : ∀ {e j : Nat}, e + j ≤ 2560 → (⟨D, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, j⟩ :=
    fun h => ddW.sub_right (Lay.wSub h)
  have F₀₄ : Frame [workR W] s.mem s₄.mem := by
    have w' : ∀ {r : Region}, Region.Sub r (workR W) → ∃ r' ∈ [workR W], Region.Sub r r' :=
      fun h => ⟨_, List.mem_singleton_self _, h⟩
    refine ((f₁.sub fun r hr => w' (entryR_work W r hr)).trans (h₃.frame.sub fun r hr => w' ?_)).trans
      (ft₄.sub fun r hr => w' ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub16
      · exact Lay.wSub (by decide)
      · exact Lay.wSub (by decide)
    · simp only [List.mem_singleton] at hr; subst hr; exact Lay.wSub (by decide)
  generalize hJ : Spec.Gcm.j0 (ctxH s.mem Ctx) (bytesAt s.mem Np 12) = J
  have cb₃ := h₃.cb
  rw [hJ] at cb₃
  simp only [Offset.add_add] at cb₃
  -- The text, until it is encrypted.
  have hD₇ : bytesAt s₇.mem D n = bytesAt s.mem D n := by
    rw [m₇, m₆, bytesAt_frame (wf _ _ _ List.length_replicate) (one1 (dDW (by omega_arith))) (by omega_arith),
      bytesAt_frame (wf _ _ _ List.length_replicate) (one1 (dDW (by decide))) (by omega_arith),
      bytesAt_frame F₀₄ (one1 ddW) (by omega_arith)]
  have hP : bytesAt s₉.mem (W + BitVec.ofNat 64 768 + BitVec.ofNat 64 (16 * (7 - c))) n = bytesAt s.mem D n := by
    rw [Offset.add_add, show 768 + 16 * (7 - c) = 880 - 16 * c by omega_arith, m₉, m₈,
      selfB _ _ _ (lb _ _ _) (by omega_arith), hD₇]
  -- The key schedule and the counter block.
  have hsch : Proof.Gcm.AArch64.Stitch.sch R s₉ = bytesAt s.mem Ctx (16 * (R + 1)) := by
    have dC : (⟨Ctx, 16 * (R + 1)⟩ : Region).Disjoint (workR W) := dcW.sub_left (Region.sub_prefix (by omega_arith))
    simp only [Proof.Gcm.AArch64.Stitch.sch, Proof.Gcm.AArch64.Stitch.kp, he₉.x21]
    rw [bytesAt_frame F₄₉ (dBR dC (dcd.sub_left (Region.sub_prefix (by omega_arith)))) (by omega_arith),
      bytesAt_frame F₀₄ (one1 dC) (by omega_arith)]
  have hcb : Proof.Gcm.AArch64.Stitch.cbk s₉ = inc32 J := by
    simp only [Proof.Gcm.AArch64.Stitch.cbk, Proof.Gcm.AArch64.Stitch.cbA, he₉.x20, Offset.add_add]
    rw [blockAt_frame F₄₉ (dWBR (by decide)),
      blockAt_frame ft₄ (one1 (dWW (.inl (by decide)) (by decide) (by decide))), cb₃]
  -- The ciphertext, and `CIPH_K(J₀)`, in `B₁`.
  have hC₁₀ : bytesAt s₁₀.mem (W + BitVec.ofNat 64 (880 - 16 * c)) n =
      gctr (ctxCiph s.mem Ctx R) (inc32 J) (bytesAt s.mem D n) := by
    have := Stitch.b1_gctr hcn hc6 ks₁₀ hP
    rw [Offset.add_add, show 768 + 16 * (7 - c) = 880 - 16 * c by omega_arith, hsch, hcb] at this
    exact this
  have hz₉ : bytesAt s₉.mem (W + BitVec.ofNat 64 768 + BitVec.ofNat 64 (16 * (6 - c))) 16 = zeros 16 := by
    rw [Offset.add_add, show 768 + 16 * (6 - c) = 864 - 16 * c by omega_arith, m₉, m₈,
      bytesAt_frame (wf _ _ _ (lb _ _ _)) (one1 (dWW (.inl (by omega_arith)) (by omega_arith) (by omega_arith))) (by decide), m₇, m₆,
      selfB _ _ _ List.length_replicate (by decide)]
    rfl
  have hE : blockAt s₁₀.mem (W + BitVec.ofNat 64 (864 - 16 * c)) = ctxCiph s.mem Ctx R J := by
    rw [hcb] at ks₁₀
    have := Stitch.b1_j0 hc6 ks₁₀ hz₉
    rw [Offset.add_add, show 768 + 16 * (6 - c) = 864 - 16 * c by omega_arith, hsch] at this
    exact this
  have hE₁₆ : blockAt s₁₆.mem (W + BitVec.ofNat 64 (864 - 16 * c)) = ctxCiph s.mem Ctx R J := by
    rw [m₁₆, blockAt_frame fL₁₅ (one1 (dWW (.inl (by omega_arith)) (by omega_arith) (by decide))), m₁₄,
      blockAt_frame (wf _ _ _ (lb _ _ _)) (one1 (dWW (.inl (by omega_arith)) (by omega_arith) (by omega_arith))), m₁₃,
      blockAt_frame (wf _ _ _ List.length_replicate) (one1 (dWW (.inl (by omega_arith)) (by omega_arith) (by omega_arith))),
      blockAt_frame (wf _ _ _ (lb _ _ _)) (one1 (dWW (.inl (by omega_arith)) (by omega_arith) (by omega_arith))), m₁₂,
      blockAt_frame (wf _ _ _ (lb _ _ _)) (one1 (dDW (by omega_arith)).symm), m₁₁, hE]
  -- The text, at the end.
  have hC₁₂ : bytesAt s₁₂.mem (W + BitVec.ofNat 64 (880 - 16 * c)) n =
      gctr (ctxCiph s.mem Ctx R) (inc32 J) (bytesAt s.mem D n) := by
    rw [m₁₂, bytesAt_frame (wf _ _ _ (lb _ _ _)) (one1 (dDW (by omega_arith)).symm) (by omega_arith), m₁₁, hC₁₀]
  have hdata : bytesAt s₁₈.mem D n = gctr (ctxCiph s.mem Ctx R) (inc32 J) (bytesAt s.mem D n) := by
    rw [bytesAt_frame f₁₈ (one1 ddt) (by omega_arith), bytesAt_frame fT₁₇ (one1 (dDW (by decide))) (by omega_arith), m₁₆,
      bytesAt_frame fL₁₅ (one1 (dDW (by decide))) (by omega_arith), m₁₄,
      bytesAt_frame (wf _ _ _ (lb _ _ _)) (one1 (dDW (by omega_arith))) (by omega_arith), m₁₃,
      bytesAt_frame (wf _ _ _ List.length_replicate) (one1 (dDW (by omega_arith))) (by omega_arith),
      bytesAt_frame (wf _ _ _ (lb _ _ _)) (one1 (dDW (by omega_arith))) (by omega_arith), m₁₂,
      selfB _ _ _ (lb _ _ _) (by omega_arith), m₁₁, hC₁₀]
  -- What `B₂` holds, and its GHASH.
  generalize hCg : gctr (ctxCiph s.mem Ctx R) (inc32 J) (bytesAt s.mem D n) = Cg at hC₁₂ hdata
  have hCl : Cg.length = n := by rw [← hCg, Proof.Gcm.length_gctr, lb]
  have hA₁₃ : bytesAt s₁₃.mem A al = bytesAt s.mem A al := by
    have dA : ∀ {e j : Nat}, e + j ≤ 2560 → (⟨A, al⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, j⟩ :=
      fun h => daW.sub_right (Lay.wSub h)
    rw [m₁₃, bytesAt_frame (wf _ _ _ List.length_replicate) (one1 (dA (by omega_arith))) (by omega_arith),
      bytesAt_frame (wf _ _ _ (lb _ _ _)) (one1 (dA (by omega_arith))) (by omega_arith), m₁₂,
      bytesAt_frame (wf _ _ _ (lb _ _ _)) (one1 dad) (by omega_arith), m₁₁,
      bytesAt_frame f₁₀ (one1 (dA (by decide))) (by omega_arith), bytesAt_frame F₄₉ (dBR daW dad) (by omega_arith),
      bytesAt_frame F₀₄ (one1 daW) (by omega_arith)]
  have hZ₆ : bytesAt s₆.mem (W + BitVec.ofNat 64 896) 128 = zeros 128 := by
    rw [m₆, bytesAt_frame (wf _ _ _ List.length_replicate) (one1 (dWW (.inr (by omega_arith)) (by decide) (by omega_arith)))
      (by decide), selfB _ _ _ List.length_replicate (by decide)]
    rfl
  have fY : Frame [⟨W + BitVec.ofNat 64 768, 128⟩, ⟨D, n⟩] s₆.mem s₁₂.mem := by
    have oneG : ∀ {m m' : Mem} {q : Addr} {k : Nat}, Frame [⟨q, k⟩] m m' →
        (∃ r' ∈ [(⟨W + BitVec.ofNat 64 768, 128⟩ : Region), ⟨D, n⟩], Region.Sub ⟨q, k⟩ r') →
        Frame [⟨W + BitVec.ofNat 64 768, 128⟩, ⟨D, n⟩] m m' := fun h hs =>
      h.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hs
    have a₁ : Frame [⟨W + BitVec.ofNat 64 768, 128⟩, ⟨D, n⟩] s₆.mem s₉.mem := by
      rw [m₉, m₈, m₇]
      exact oneG (wf _ _ _ (lb _ _ _)) ⟨_, List.mem_cons_self .., Offset.sub W (by omega_arith) (by omega_arith)⟩
    have a₂ : Frame [⟨W + BitVec.ofNat 64 768, 128⟩, ⟨D, n⟩] s₁₀.mem s₁₂.mem := by
      rw [m₁₂, m₁₁]; exact oneG (wf _ _ _ (lb _ _ _)) ⟨_, by simp, fun _ h => h⟩
    exact (a₁.trans (oneG f₁₀ ⟨_, List.mem_cons_self .., fun _ h => h⟩)).trans a₂
  have L := Stitch.b2_layout (G := W + BitVec.ofNat 64 896) (c := c) (n := n)
    (Q := bytesAt s₁₂.mem (W + BitVec.ofNat 64 (880 - 16 * c)) (16 * c)) (A := bytesAt s₁₃.mem A al)
    (lens := Proof.Gcm.lensBlock al n) (mZ := s₆.mem) (mY := s₁₂.mem) (mL := s₁₅.mem) hc6 hcn
    (by omega_arith) (lb _ _ _) (by rw [lb]; exact h16) hZ₆ fY (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dWW (.inr (by decide)) (by decide) (by decide)
      · exact (dDW (by decide)).symm)
    (by
      simp only [Offset.add_add]
      rw [show 896 + (112 - 16 * c) = 1008 - 16 * c by omega_arith, show 896 + (112 - 16 * c + n) = 1008 - 16 * c + n by omega_arith,
        show 896 + (96 - 16 * c) = 992 - 16 * c by omega_arith, ← m₁₃, ← m₁₄]
      exact fL₁₅)
    (by rw [Offset.add_add]; exact lens₁₅)
  rw [← Proof.AesCcm.bytesAt_prefix _ _ (show n ≤ 16 * c from hcn), hC₁₂, hA₁₃,
    show 16 * c - n = Spec.Gcm.padLen Cg.length by rw [hCl]; simp only [Spec.Gcm.padLen]; omega_arith,
    show Proof.Gcm.lensBlock al n = Proof.Gcm.lensBlock (bytesAt s.mem A al).length Cg.length by rw [lb, hCl]] at L
  have hg : Spec.Gcm.ghashFrom (ctxH s.mem Ctx) 0 ((List.range 8).map fun j =>
      blockAt s₁₅.mem (W + BitVec.ofNat 64 (896 + 16 * j))) =
      Spec.Gcm.ghashFrom (ctxH s.mem Ctx) (ghash (ctxH s.mem Ctx) (blocks (Proof.Gcm.padded (bytesAt s.mem A al) Cg)))
        [ofBytes (Proof.Gcm.lensBlock (bytesAt s.mem A al).length Cg.length)] := by
    rw [show ((List.range 8).map fun j => blockAt s₁₅.mem (W + BitVec.ofNat 64 (896 + 16 * j))) =
        Spec.Gcm.blocksAt s₁₅.mem (W + BitVec.ofNat 64 896) 8 by simp only [Spec.Gcm.blocksAt, Offset.add_add],
      Proof.Gcm.blocksAt_eq, L]
    exact Proof.Gcm.ghash_lead _ _ (by rw [lb]; exact h16)
  -- The tag.
  have bt : ∀ (m : Mem) (p : Addr), bytesAt m p 16 = Spec.Gcm.toBytes (blockAt m p) := fun m p => by
    rw [blockAt, Proof.Cmac.toBytes_ofBytes (lb _ _ _)]
  have htag : bytesAt s₁₈.mem Tg 16 = Spec.Gcm.toBytes (Spec.Gcm.ghashFrom (ctxH s.mem Ctx)
      (ghash (ctxH s.mem Ctx) (blocks (Proof.Gcm.padded (bytesAt s.mem A al) Cg)))
        [ofBytes (Proof.Gcm.lensBlock (bytesAt s.mem A al).length Cg.length)] ^^^ ctxCiph s.mem Ctx R J) := by
    rw [out₁₈, bt, ← add_ofNat_zero W, tag₁₇, hE₁₆, hg]
  rw [hdata, htag, Spec.Gcm.encryptWith, Proof.Gcm.fullTag_eq,
    List.take_of_length_le (by rw [Proof.Cmac.toBytes_length]), hJ, hCg]

end VG.Proof.AesGcm.AArch64.Fast
