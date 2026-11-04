module

import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Steps
public import VerifiedGarbage.Proof.Mont.AArch64.Words
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Weierstrass.AArch64.BytesLen
import Mathlib.Logic.Function.Basic
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Copy
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Msg
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Reduce
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Blocks
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import Mathlib.Tactic.Conv
import Mathlib.Tactic.SplitIfs

/-!
# Deterministic ECDSA on AArch64: scalars longer than the hash

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Wide.lean`), for a hash function
whose output is shorter than the curve's scalars (`wide`): the `Q` bytes at
an offset in the frame's top bytes, shifted right in place through the words
at `scratch + 2560` (`convB_ok`, by `loadBytes_ok`, `shrWords_ok` and
`storeBytes_ok`, with `scratch` in `x0`; only P-521's scalars, the only
ones with `sh ≠ 0`, are shifted); `h`, `Q - D` zero bytes then the digest
(`hPrep_ok`); the digest for `core` if `sh ≠ 0`, the digest between
`Q - D - 1` zero bytes and one, shifted right by `8 - sh` bits, which is the
digest's number shifted left by `sh` bits (`xPrep_ok`); and the candidate
`T`, `m` successive `V = HMAC_K(V)` each copied after the last
(`candW_ok`), its first `Q` bytes then shifted right by `sh` bits
(`candTop_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64
open VG.Proof.Mont (wordsVal Outside off ofs)
open VG.Proof.Mont.AArch64 (Scr KeepRegs)
open VG.Proof.Weierstrass.AArch64 (loadBytes_ok shrWords_ok storeBytes_ok)

variable {P : RfcHash} {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} {L : Lay dn E} {g : Reg → BitVec 64} {m₀ : Mem}

/-- In the wide case, the frame has 272 bytes at its top. -/
theorem e272 (hLe : L.e = P.e) (hW : P.wide = true) : L.e = 272 := by
  rw [hLe]; simp only [RfcHash.e, hW, ite_true]

/-- `x0 ← scratch`. -/
theorem ldScr_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) :
    WP isa (.block [.ldrSp .x0 fScratch]) u (Upd L g m₀ u .x0 L.scr) := by
  have h200 := hc.inFr (d := 200) (by omega_arith) (by omega_arith)
  apply WP.of_runBlock
  simp only [fScratch, runBlock_cons, runStep_some, runBlock_nil, exec, State.load, Nat.reduceMod,
    Nat.reduceLT, and_self, ite_true, hc.sp, Offset.add_add, Nat.reduceAdd, h200, Option.map_some, read8,
    hc.pScr, Option.some.injEq, exists_eq_left']
  exact ⟨hc.set hL (d := .x0) (by decide) rfl rfl rfl rfl (fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr) rfl, rfl,
    by rw [RegUpd.gpr_write_self]; exact BitVec.setWidth_eq _, fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr⟩

/-- `x3 ← 0 - 1`, all ones. -/
theorem ones_ok (u : State) :
    WP isa (.block [.movz .x .x3 0 0, .subImm .x .x3 .x3 1]) u fun u' =>
      u'.gpr .x3 = BitVec.allOnes 64 ∧ KeepRegs [.x3] u u' ∧ u'.mem = u.mem ∧ u'.syms = u.syms := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show 16 * 0 < Size.x.bits by decide,
    show (1 : Nat) < 4096 by decide, ite_true, State.read, Size.bits, RegUpd.gpr_write_self,
    Option.some.injEq, exists_eq_left']
  refine ⟨by decide, ⟨fun r hr => ?_, rfl, rfl, rfl⟩, rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  rw [RegUpd.gpr_write_of_ne _ _ _ hr, RegUpd.gpr_write_of_ne _ _ _ hr]

theorem keep_pres {rs : List Reg} {s s' : State} (h : KeepRegs rs s s') (hrs : ∀ r ∈ rs, r ∉ preserved) :
    ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r := fun r hr _ =>
  h.gpr r fun h' => hrs r h' hr

/-- `sh ≠ 0` only for P-521, whose scalars are longer than any hash. -/
theorem wide_of_sh (hsh : P.R.sh ≠ 0) : P.R.wide = true := by
  cases hr : P.R.wide
  · have := P.R.sizesA hr; have := P.R.nBits_len; omega_arith
  · rfl

/-- The curve's scalars are longer than any hash, so this hash is shorter. -/
theorem wide_of_R (hRW : P.R.wide = true) : P.wide = true := by
  have := P.R.sizesW hRW
  have := P.sizes
  simp only [RfcHash.wide, RfcHash.Q, decide_eq_true_eq]; omega

/-- `convB o s`: the `Q` bytes at `sp + o`, in the frame's top bytes,
shifted right by `s` bits in place, through the words at `scratch + 2560`
(`scratch` in `x0`), for P-521's scalars. -/
theorem convB_ok (hL : L.Ok) (hLe : L.e = P.e) (hRW : P.R.wide = true) {t : State} (hc : Ctx L g m₀ t)
    (h0 : t.gpr .x0 = L.scr) {o s : Nat} (ho₁ : 224 ≤ o) (ho₂ : o + 72 ≤ 496) (ho8 : o % 8 = 0) (hs₁ : 1 ≤ s)
    (hs₂ : s < 64) :
    WP isa (.block ((cfgOf P).convB o s)) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 (16 + o), P.Q⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 (16 + o)) P.Q =
        Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 (16 + o)) P.Q) >>> s) := by
  obtain ⟨hw9, hQ66, -⟩ := P.R.sizesW hRW
  have he := e272 hLe (wide_of_R hRW)
  have nB := hL.nB
  have nc := hL.nc
  have hcw : (cfgOf P).w = 9 := hw9
  have hcl : (cfgOf P).len = 66 := hQ66
  have hQ : P.Q = 66 := hQ66
  simp only [Cfg.convB, hcw, hcl]
  rw [hQ]
  rw [show ∀ (l : List Instr), Instr.addSp .x6 o :: l = Cfg.fr .x6 o ++ l from fun _ => rfl]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono_syms (fr_ok hL hc (d := .x6) (by decide) (o := o) (by omega_arith)) fun u₂ h₂ sy₂ => ?_
  have hc₂ := h₂.ctx
  have hS₂ : Scr u₂ L.scr 8192 :=
    ⟨by rw [h₂.keep _ (by decide), h0], by rw [hc₂.wr]; simp, nc, by decide⟩
  have hx6 : u₂.gpr .x6 = L.B + BitVec.ofNat 64 (16 + o) := h₂.val
  rw [WP.block_append_iff]
  refine WP.mono_syms (loadBytes_ok hS₂ (len := 66) (n := 9) (o := 2560) (src := .x6) (by decide) (by decide)
    (by omega_arith) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun d hd => by rw [hx6, Offset.add_add]; exact hc₂.inFr (by omega_arith) (by omega_arith))
    (by rw [hx6]; exact (hL.stk_scr (by omega_arith) (by omega_arith)))) fun u₃ ⟨hv₃, k₃, O₃⟩ sy₃ => ?_
  rw [WP.block_append_iff]
  have hS₃ : Scr u₃ L.scr 8192 := ⟨by rw [k₃.gpr _ (by decide)]; exact hS₂.x0, k₃.wr ▸ hS₂.wr, nc, by decide⟩
  refine WP.mono_syms (shrWords_ok hS₃ (n := 9) (o := 2560) (sh := s) (by omega_arith) (by decide) hs₁ hs₂)
    fun u₄ ⟨hv₄, k₄, O₄⟩ sy₄ => ?_
  rw [WP.block_append_iff]
  refine WP.mono_syms (ones_ok u₄) fun u₅ ⟨h3₅, k₅, m₅, _⟩ sy₅ => ?_
  have hS₅ : Scr u₅ L.scr 8192 :=
    ⟨by rw [k₅.gpr _ (by decide), k₄.gpr _ (by decide)]; exact hS₃.x0, k₅.wr ▸ k₄.wr ▸ hS₃.wr, nc, by decide⟩
  have hx6₅ : u₅.gpr .x6 = L.B + BitVec.ofNat 64 (16 + o) := by
    rw [k₅.gpr _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (by decide), hx6]
  have hwr₅ : u₅.wr = u₂.wr := by rw [k₅.wr, k₄.wr, k₃.wr]
  refine WP.mono_syms (storeBytes_ok hS₅ (len := 66) (n := 9) (d := 0) (a := 2560) (dst := .x6) (by decide)
    (by decide) (by decide) true (by rw [h3₅]; rfl) (by omega_arith) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by rw [hx6₅, add_ofNat_zero, toNat_add_of (by omega_arith)]; omega_arith)
    (fun e m hem => by
      rw [hx6₅, add_ofNat_zero, Offset.add_add, hwr₅]; exact hc₂.inFrW (by omega_arith) (by omega_arith))
    (by rw [hx6₅, add_ofNat_zero]; exact (hL.stk_scr (by omega_arith) (by omega_arith)).symm)) fun u₆ ⟨hb₆, k₆, O₆⟩ sy₆ => ?_
  rw [hx6₅, add_ofNat_zero] at hb₆ O₆
  -- What changed: the words at `scratch + 2560`, and the bytes converted.
  have hf : Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 (16 + o), 66⟩] t.mem u₆.mem := by
    have f₃ := frame_of_outside (O₃.trans O₄) (by omega_arith)
    have f₆ := frame_of_outside O₆ (by omega_arith)
    rw [add_ofNat_zero, m₅] at f₆
    rw [h₂.mem, show 8 * 9 = 72 from rfl] at f₃
    exact (f₃.sub fun r hr => ⟨r, by simp_all, sub_refl _⟩).trans (f₆.sub fun r hr => ⟨r, by simp_all, sub_refl _⟩)
  have hk : ∀ r ∈ preserved, r ≠ .x30 → u₆.gpr r = t.gpr r := fun r hr h30 => by
    rw [keep_pres k₆ (by decide) r hr h30, keep_pres k₅ (by decide) r hr h30, keep_pres k₄ (by decide) r hr h30,
      keep_pres k₃ (by decide) r hr h30, h₂.keep _ (ne_cs hr (by decide))]
  refine ⟨hc.keep hL (by rw [k₆.rd, k₅.rd, k₄.rd, k₃.rd, hc₂.rd, hc.rd]) (by rw [k₆.wr, hwr₅, hc₂.wr, hc.wr])
      (by rw [k₆.sp, k₅.sp, k₄.sp, k₃.sp, hc₂.sp, hc.sp]) hk hf (fun r hr => ?_)
      (by rw [sy₆, sy₅, sy₄, sy₃, sy₂]), hf, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact safe_scr L (by omega_arith)
    · exact safe_high L (by omega_arith) (by omega_arith)
  · rw [← Rfc6979.ecdsa_bytesAt, hb₆]
    simp only [ite_true]
    rw [m₅, hv₄, hv₃, hx6, h₂.mem, Rfc6979.ecdsa_bytesAt]

/-- `conv o s`: `scratch` into `x0`, then `convB o s`. -/
theorem conv_ok (hL : L.Ok) (hLe : L.e = P.e) (hRW : P.R.wide = true) {t : State} (hc : Ctx L g m₀ t)
    {o s : Nat} (ho₁ : 224 ≤ o) (ho₂ : o + 72 ≤ 496) (ho8 : o % 8 = 0) (hs₁ : 1 ≤ s) (hs₂ : s < 64) :
    WP isa ((cfgOf P).conv o s) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 (16 + o), P.Q⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 (16 + o)) P.Q =
        Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 (16 + o)) P.Q) >>> s) :=
  WP.seq (WP.mono (ldScr_ok hL hc) fun u h => by
    rw [← h.mem]; exact convB_ok hL hLe hRW h.ctx h.val ho₁ ho₂ ho8 hs₁ hs₂)

/-! ## Zero words and copies in the frame's top bytes -/

/-- `k` zero words from `sp + o` (the frame in `x15`, zero in `x11`). -/
theorem zstr_ok {t : State} (hc : Ctx L g m₀ t) {o : Nat} (ho₁ : 224 ≤ o) (ho₂ : o + 72 ≤ 224 + L.e)
    (ho8 : o % 8 = 0) : ∀ k ≤ 9, ∀ u : State, u.wr = t.wr → u.gpr .x15 = L.B + BitVec.ofNat 64 16 →
    u.gpr .x11 = 0 →
    WP isa (.block ((List.range k).map fun j => .str .x .x11 .x15 (o + 8 * j))) u fun u' =>
      u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧ u'.gpr = u.gpr ∧
      Frame [⟨L.B + BitVec.ofNat 64 (16 + o), 72⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (16 + o)) (8 * k) = List.replicate (8 * k) 0
  | 0, _, u, _, _, _ => WP.of_runBlock ⟨u, rfl, rfl, rfl, rfl, rfl, Frame.refl _ _, rfl⟩
  | k + 1, hk, u, hwu, h15, h11 => by
    have := L.he
    rw [List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (zstr_ok hc ho₁ ho₂ ho8 k (by omega_arith) u hwu h15 h11) fun u₁ ⟨hrd, hwr, hsp, hg, hf, hb⟩ => ?_
    refine WP.mono (str15_ok (u := u₁) ((hwr.trans hwu).trans hc.wr) (by rw [hg, h15]) (t := .x11) (o := o + 8 * k)
      (by omega_arith) (by omega_arith)) fun u₂ ⟨hrd₂, hwr₂, hsp₂, hg₂, hm₂⟩ => ?_
    have hf₂ : Frame [⟨L.B + BitVec.ofNat 64 (16 + (o + 8 * k)), 8⟩] u₁.mem u₂.mem := by
      rw [hm₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    refine ⟨hrd₂.trans hrd, hwr₂.trans hwr, hsp₂.trans hsp, hg₂.trans hg, hf.trans (hf₂.sub fun r hr =>
      ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega_arith) (by omega_arith)⟩), ?_⟩
    rw [show 8 * (k + 1) = 8 * k + 8 by omega_arith, Proof.Hmac.Common.bytesAt_add, Offset.add_add,
      show 16 + o + 8 * k = 16 + (o + 8 * k) by omega_arith,
      bytesAt_frame hf₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by omega_arith), hb, hm₂,
      hg, h11, bytesAt_writeW_zero64 _ _ (Nat.le_refl _), List.replicate_append_replicate]

/-- Nine zero words at `sp + o` (the frame in `x15`), through `x11`. -/
theorem zero9_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (h15 : t.gpr .x15 = L.B + BitVec.ofNat 64 16)
    {o : Nat} (ho₁ : 224 ≤ o) (ho₂ : o + 72 ≤ 224 + L.e) (ho8 : o % 8 = 0) :
    WP isa (.block (Cfg.zero9 o)) t fun t' => Ctx L g m₀ t' ∧ (∀ r, r ≠ .x11 → t'.gpr r = t.gpr r) ∧
      Frame [⟨L.B + BitVec.ofNat 64 (16 + o), 72⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 (16 + o)) 72 = List.replicate 72 0 := by
  rw [Cfg.zero9, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movz_ok hL hc (d := .x11) (by decide) (n := 0) (by decide)) fun u₁ h₁ => ?_
  refine WP.mono_syms (zstr_ok hc ho₁ ho₂ ho8 9 (Nat.le_refl _) u₁ (by rw [h₁.ctx.wr, hc.wr])
    (by rw [h₁.keep _ (by decide), h15]) h₁.val) fun u₂ ⟨hrd, hwr, hsp, hg, hf, hb⟩ hsy => ?_
  refine ⟨h₁.ctx.keep hL hrd hwr hsp (fun r _ _ => by rw [hg]) hf (hsy := hsy) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact safe_high L (by omega_arith) (by omega_arith)),
    fun r hr => by rw [hg, h₁.keep _ hr], h₁.mem ▸ hf, hb⟩

/-- `Q` bytes copied by `copyBytes` from `src` to the frame's top bytes at
`sp + d`, whose address is in `x14`, with `Ctx` kept. -/
theorem copyBX_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {src : Reg} {S : Addr} (hs : u.gpr src = S)
    (hsr : src ≠ .x11) {d Q : Nat} (h14 : u.gpr .x14 = L.B + BitVec.ofNat 64 (16 + d)) (h8 : 8 ≤ Q)
    (hQ : Q < 4096) (hd₁ : 224 ≤ d) (hd₂ : d + Q ≤ 224 + L.e)
    (hr : ∀ j, j + 8 ≤ Q → InRegions (u.rd ++ u.wr) (S + BitVec.ofNat 64 j) 8)
    (hsep : Region.Disjoint ⟨S, Q⟩ ⟨L.B + BitVec.ofNat 64 (16 + d), Q⟩) :
    WP isa (.block (Cfg.copyBytes Q src .x14)) u fun u' => Ctx L g m₀ u' ∧
      (∀ r, r ≠ .x11 → r ≠ .x13 → r ≠ .x14 → u'.gpr r = u.gpr r) ∧
      Frame [⟨L.B + BitVec.ofNat 64 (16 + d), Q⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (16 + d)) Q = Spec.Sha256.bytesAt u.mem S Q := by
  have he := L.he
  have nB := hL.nB
  refine WP.mono_syms (copyBytes_ok (by decide) hsr (by decide) hsep h8 hQ hs h14 hr fun j hj => by
    rw [Offset.add_add]; exact hc.inFrW (by omega_arith) (by omega_arith)) fun u' ⟨hrd, hwr, hsp, hg, hf, hb⟩ hsy => ?_
  exact ⟨hc.keep hL hrd hwr hsp (fun r hr _ => hg r (ne_cs hr (by decide)) (ne_cs hr (by decide))
      (ne_cs hr (by decide))) hf (hsy := hsy)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_high L (by omega_arith) (by omega_arith)),
    hg, hf, hb⟩

/-- `x14 ← x15 + k`. -/
theorem x14_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (h15 : u.gpr .x15 = L.B + BitVec.ofNat 64 16) {k : Nat}
    (hk : k < 4096) :
    WP isa (.block [.addImm .x .x14 .x15 k]) u (Upd L g m₀ u .x14 (L.B + BitVec.ofNat 64 (16 + k))) := by
  refine WP.mono (addImm_ok hL hc (d := .x14) (by decide) h15 hk) fun u' h => ?_
  rw [Offset.add_add] at h
  exact h

/-! ## `h` and the digest for `core` -/

/-- `h`: `Q - D` zero bytes, then the digest (at `x1`), at `fX`. -/
theorem hPrep_ok (hL : L.Ok) (hLe : L.e = P.e) (hW : P.wide = true) (hdn : P.H.D ≤ dn) {t : State}
    (hc : Ctx L g m₀ t) (h1 : t.gpr .x1 = L.dg) :
    WP isa (.block (cfgOf P).hPrep) t fun t' => Ctx L g m₀ t' ∧
      (∀ r, r ≠ .x11 → r ≠ .x13 → r ≠ .x14 → r ≠ .x15 → t'.gpr r = t.gpr r) ∧
      t'.gpr .x15 = L.B + BitVec.ofNat 64 16 ∧
      Frame [⟨L.B + BitVec.ofNat 64 240, 72⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 240) P.Q =
        List.replicate (P.Q - P.H.D) 0 ++ Spec.Sha256.bytesAt t.mem L.dg P.H.D := by
  have he := e272 hLe hW
  have hQD : P.H.D < P.Q := by simpa [RfcHash.wide] using hW
  have := P.sizes
  rw [show (cfgOf P).hPrep = Cfg.fr .x15 0 ++ Cfg.zero9 fX ++ [.addImm .x .x14 .x15 (224 + P.Q - P.H.D)] ++
      Cfg.copyBytes P.H.D .x1 .x14 from rfl, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (fr_ok hL hc (d := .x15) (by decide) (o := 0) (by decide)) fun u₀ h₀ => ?_
  have h15₀ : u₀.gpr .x15 = L.B + BitVec.ofNat 64 16 := h₀.val
  refine WP.mono (zero9_ok hL h₀.ctx h15₀ (o := fX) (by decide) (by rw [he]; decide) (by decide))
    fun u₁ ⟨hc₁, hg₁, hf₁, hb₁⟩ => ?_
  simp only [show 16 + fX = 240 from rfl] at hf₁ hb₁
  have hdg₁ : Spec.Sha256.bytesAt u₁.mem L.dg P.H.D = Spec.Sha256.bytesAt t.mem L.dg P.H.D := by
    rw [bytesAt_frame hf₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hL.stk_DG (by omega)).symm.sub_left (Region.sub_prefix hdn)) (by anums), h₀.mem]
  have h15₁ : u₁.gpr .x15 = L.B + BitVec.ofNat 64 16 := (hg₁ _ (by decide)).trans h15₀
  refine WP.mono (x14_ok hL hc₁ h15₁ (k := 224 + P.Q - P.H.D) (by anums)) fun u₂ h₂ => ?_
  have e₁ : 16 + (224 + P.Q - P.H.D) = 16 + (224 + (P.Q - P.H.D)) := by omega
  rw [e₁] at h₂
  have hsep : Region.Disjoint ⟨L.dg, P.H.D⟩ ⟨L.B + BitVec.ofNat 64 (16 + (224 + (P.Q - P.H.D))), P.H.D⟩ :=
    (hL.stk_DG (by rw [he]; anums)).symm.sub_left (Region.sub_prefix hdn)
  refine WP.mono (copyBX_ok hL h₂.ctx (src := .x1) (S := L.dg)
    (by rw [h₂.keep _ (by decide), hg₁ _ (by decide), h₀.keep _ (by decide), h1]) (by decide) h₂.val (by anums)
    (by anums) (by omega) (by rw [he]; anums)
    (fun j hj => by
      have := h₂.ctx.inDg (o := j) (n := 8) (by omega) (by anums)
      exact this) hsep)
    fun u₃ ⟨hc₃, hg₃, hf₃, hb₃⟩ => ?_
  rw [h₂.mem, hdg₁] at hb₃
  rw [show 16 + (224 + (P.Q - P.H.D)) = 240 + (P.Q - P.H.D) by omega] at hf₃ hb₃
  refine ⟨hc₃, fun r a b c d => by
      rw [hg₃ r a b c, h₂.keep r c, hg₁ r a, h₀.keep r d], by
      rw [hg₃ _ (by decide) (by decide) (by decide), h₂.keep _ (by decide), h15₁],
    (h₀.mem ▸ hf₁).trans (by
      rw [← h₂.mem]
      exact hf₃.sub fun r hr => ⟨_, List.mem_singleton_self _,
        by simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega) (by anums)⟩), ?_⟩
  rw [show P.Q = (P.Q - P.H.D) + P.H.D by omega, Proof.Hmac.Common.bytesAt_add, Offset.add_add,
    show P.Q - P.H.D + P.H.D - P.H.D = P.Q - P.H.D by omega, hb₃,
    bytesAt_frame hf₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega) (by omega) (by anums)) (by omega), h₂.mem]
  have := bytesAt_take u₁.mem (L.B + BitVec.ofNat 64 240) (n := P.Q - P.H.D) (k := 72) (by anums)
  rw [this, hb₁, List.take_replicate, Nat.min_eq_left (by anums)]

theorem shift_back (e sh : Nat) (hs : sh < 8) : (e * 2 ^ 8) >>> (8 - sh) = e * 2 ^ sh := by
  rw [Nat.shiftRight_eq_div_pow, show e * 2 ^ 8 = e * 2 ^ sh * 2 ^ (8 - sh) by
    rw [Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

/-- If `sh ≠ 0`: the digest for `core`, the digest's number shifted left by
`sh` bits, in `Q` bytes at `fXc`, with the frame in `x15`, `digest` in `x1`
and `scratch` in `x0`. -/
theorem xPrep_ok (hL : L.Ok) (hLe : L.e = P.e) (hdn : P.H.D ≤ dn) (hsh : P.R.sh ≠ 0)
    {t : State} (hc : Ctx L g m₀ t) (h1 : t.gpr .x1 = L.dg) (h0 : t.gpr .x0 = L.scr)
    (h15 : t.gpr .x15 = L.B + BitVec.ofNat 64 16) :
    WP isa (.block (cfgOf P).xPrep) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 312, 72⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 312) P.Q =
        Spec.Weierstrass.toBytes P.Q (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem L.dg P.H.D) * 2 ^ P.R.sh) := by
  have hRW := wide_of_sh hsh
  have hW := wide_of_R hRW
  have he := e272 hLe hW
  have hQD : P.H.D < P.Q := by simpa [RfcHash.wide] using hW
  have hsl := P.R.nBits_len
  have hsh8 : P.R.sh < 8 := by omega
  have hsc : (cfgOf P).sh = P.R.sh := rfl
  have := P.sizes
  rw [Cfg.xPrep, hsc, ite_eq_right_of_eq_false _ _ (eq_false hsh),
    show Cfg.zero9 fXc ++ ([.addImm .x .x14 .x15 (fXc + (cfgOf P).len - (cfgOf P).D - 1)] : List Instr) ++
      Cfg.copyBytes (cfgOf P).D .x1 .x14 ++ (cfgOf P).convB fXc (8 - P.R.sh) =
      Cfg.zero9 fXc ++ [.addImm .x .x14 .x15 (296 + P.Q - P.H.D - 1)] ++ Cfg.copyBytes P.H.D .x1 .x14 ++
        (cfgOf P).convB fXc (8 - P.R.sh) from rfl, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (zero9_ok hL hc h15 (o := fXc) (by decide) (by rw [he]; decide) (by decide))
    fun u₁ ⟨hc₁, hg₁, hf₁, hb₁⟩ => ?_
  simp only [show 16 + fXc = 312 from rfl] at hf₁ hb₁
  have hdg₁ : Spec.Sha256.bytesAt u₁.mem L.dg P.H.D = Spec.Sha256.bytesAt t.mem L.dg P.H.D :=
    bytesAt_frame hf₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hL.stk_DG (by omega)).symm.sub_left (Region.sub_prefix hdn)) (by anums)
  have h15₁ : u₁.gpr .x15 = L.B + BitVec.ofNat 64 16 := (hg₁ _ (by decide)).trans h15
  refine WP.mono (x14_ok hL hc₁ h15₁ (k := 296 + P.Q - P.H.D - 1) (by anums)) fun u₂ h₂ => ?_
  have e₁ : 16 + (296 + P.Q - P.H.D - 1) = 16 + (296 + (P.Q - P.H.D - 1)) := by omega
  rw [e₁] at h₂
  have hsep : Region.Disjoint ⟨L.dg, P.H.D⟩ ⟨L.B + BitVec.ofNat 64 (16 + (296 + (P.Q - P.H.D - 1))), P.H.D⟩ :=
    (hL.stk_DG (by rw [he]; anums)).symm.sub_left (Region.sub_prefix hdn)
  refine WP.mono (copyBX_ok hL h₂.ctx (src := .x1) (S := L.dg)
    (by rw [h₂.keep _ (by decide), hg₁ _ (by decide), h1]) (by decide) h₂.val (by anums)
    (by anums) (by omega) (by rw [he]; anums)
    (fun j hj => h₂.ctx.inDg (o := j) (n := 8) (by omega) (by anums)) hsep)
    fun u₃ ⟨hc₃, hg₃, hf₃, hb₃⟩ => ?_
  rw [h₂.mem, hdg₁] at hb₃
  rw [show 16 + (296 + (P.Q - P.H.D - 1)) = 312 + (P.Q - P.H.D - 1) by omega] at hf₃ hb₃
  have h0₃ : u₃.gpr .x0 = L.scr := by
    rw [hg₃ _ (by decide) (by decide) (by decide), h₂.keep _ (by decide), hg₁ _ (by decide), h0]
  refine WP.mono (convB_ok hL hLe hRW hc₃ h0₃ (o := fXc) (s := 8 - P.R.sh) (by decide) (by decide) (by decide)
    (by omega) (by omega)) fun u₄ ⟨hc₄, hf₄, hb₄⟩ => ?_
  simp only [show 16 + fXc = 312 from rfl] at hf₄ hb₄
  rw [h₂.mem] at hf₃
  refine ⟨hc₄, ?_, ?_⟩
  · refine ((hf₁.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩).trans
      (hf₃.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩)).trans
      (hf₄.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact sub_refl _
    · simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega) (by anums)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., sub_refl _⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Region.sub_prefix (by anums)⟩
  · -- `Q - D - 1` zero bytes, the digest, and a zero byte, shifted right by `8 - sh` bits.
    have hY : Spec.Sha256.bytesAt u₃.mem (L.B + BitVec.ofNat 64 312) P.Q =
        List.replicate (P.Q - P.H.D - 1) 0 ++ (Spec.Sha256.bytesAt t.mem L.dg P.H.D ++ List.replicate 1 0) := by
      have hz : ∀ a n, a + n ≤ 72 → Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 (312 + a)) n =
          List.replicate n 0 := fun a n han => by
        have h1 := bytesAt_take u₁.mem (L.B + BitVec.ofNat 64 312) (n := a + n) (k := 72) (by omega)
        rw [hb₁, List.take_replicate, Nat.min_eq_left (by omega), Proof.Hmac.Common.bytesAt_add, Offset.add_add,
          ← List.replicate_append_replicate] at h1
        exact (List.append_inj h1 (by simp [Spec.Sha256.bytesAt])).2
      have e := Proof.Hmac.Common.bytesAt_add u₃.mem (L.B + BitVec.ofNat 64 312) (P.Q - P.H.D - 1) (P.H.D + 1)
      have e' := Proof.Hmac.Common.bytesAt_add u₃.mem (L.B + BitVec.ofNat 64 312 + BitVec.ofNat 64 (P.Q - P.H.D - 1))
        P.H.D 1
      rw [show P.Q - P.H.D - 1 + (P.H.D + 1) = P.Q by omega] at e
      rw [Offset.add_add, Offset.add_add] at e'
      rw [Offset.add_add] at e
      have p₁ : Spec.Sha256.bytesAt u₃.mem (L.B + BitVec.ofNat 64 312) (P.Q - P.H.D - 1) =
          List.replicate (P.Q - P.H.D - 1) 0 := by
        rw [bytesAt_frame hf₃ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Offset.disjoint _ (by omega) (by omega) (by anums)) (by omega)]
        have := hz 0 (P.Q - P.H.D - 1) (by anums)
        rwa [Nat.add_zero] at this
      have p₃ : Spec.Sha256.bytesAt u₃.mem (L.B + BitVec.ofNat 64 (312 + (P.Q - P.H.D - 1) + P.H.D)) 1 =
          List.replicate 1 0 := by
        rw [bytesAt_frame hf₃ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Offset.disjoint _ (by omega) (by omega) (by anums)) (by omega),
          show 312 + (P.Q - P.H.D - 1) + P.H.D = 312 + (P.Q - P.H.D - 1 + P.H.D) by omega]
        exact hz (P.Q - P.H.D - 1 + P.H.D) 1 (by anums)
      rw [e, e', hb₃, p₁, p₃]
    rw [hb₄, hY, Rfc6979.ofBytes_zeros, Rfc6979.ofBytes_append_zeros, show 8 * 1 = 8 from rfl,
      shift_back _ _ hsh8]

/-! ## The candidate -/

/-- `genT` with one more `V`: the last after the others. -/
theorem genT_succ (H : Spec.Hmac.HashFunction) (K : List Byte) : ∀ (k : Nat) (V : List Byte),
    Spec.Ecdsa.Rfc6979.genT H K (k + 1) V =
      ((Spec.Ecdsa.Rfc6979.genT H K k V).1 ++ Spec.Hmac.hmac H K (Spec.Ecdsa.Rfc6979.genT H K k V).2,
        Spec.Hmac.hmac H K (Spec.Ecdsa.Rfc6979.genT H K k V).2)
  | 0, V => by simp [Spec.Ecdsa.Rfc6979.genT]
  | k + 1, V => by
    show (Spec.Hmac.hmac H K V ++ (Spec.Ecdsa.Rfc6979.genT H K (k + 1) (Spec.Hmac.hmac H K V)).1,
        (Spec.Ecdsa.Rfc6979.genT H K (k + 1) (Spec.Hmac.hmac H K V)).2) =
      ((Spec.Hmac.hmac H K V ++ (Spec.Ecdsa.Rfc6979.genT H K k (Spec.Hmac.hmac H K V)).1) ++
          Spec.Hmac.hmac H K (Spec.Ecdsa.Rfc6979.genT H K k (Spec.Hmac.hmac H K V)).2,
        Spec.Hmac.hmac H K (Spec.Ecdsa.Rfc6979.genT H K k (Spec.Hmac.hmac H K V)).2)
    rw [genT_succ H K k (Spec.Hmac.hmac H K V)]
    simp

theorem genT_length (P : RfcHash) (K : List Byte) : ∀ (k : Nat) (V : List Byte),
    (Spec.Ecdsa.Rfc6979.genT P.ok.SH.H K k V).1.length = k * P.H.D
  | 0, V => by simp [Spec.Ecdsa.Rfc6979.genT]
  | k + 1, V => by
    rw [genT_succ, List.length_append, genT_length P K k V, RfcHash.mac_length]
    rw [Nat.succ_mul]

/-- What a candidate changes: `scratch`, the stack below the frame, `K` and
`V`, and `T` at the frame's top. -/
abbrev CWW {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) : List Region :=
  [L.SCR, ⟨L.B, 144⟩, ⟨L.B + BitVec.ofNat 64 384, 128⟩]

theorem kvw_cww : ∀ r ∈ KVW L, ∃ r' ∈ CWW L, Region.Sub r r' := fun r hr => ⟨r, by
  simp only [CWW, KVW, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
  rcases hr with h | h <;> simp [h], sub_refl _⟩

/-- `V`'s `D` bytes copied to `T + k D`. -/
theorem keepV_ok (hL : L.Ok) (hLe : L.e = P.e) (hW : P.wide = true) {t : State} (hc : Ctx L g m₀ t) {k : Nat}
    (hk : k * P.H.D + P.H.D ≤ 128) :
    WP isa (.block ((cfgOf P).keepV k)) t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.B + BitVec.ofNat 64 (384 + k * P.H.D), P.H.D⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (384 + k * P.H.D)) P.H.D = vOf P L t.mem := by
  have he := e272 hLe hW
  have := P.sizes
  rw [show (cfgOf P).keepV k = Cfg.fr .x15 0 ++ [.addImm .x .x13 .x15 fV] ++ [.addImm .x .x14 .x15 (368 + k * P.H.D)] ++
      Cfg.copyBytes P.H.D .x13 .x14 from rfl, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (fr_ok hL hc (d := .x15) (by decide) (o := 0) (by decide)) fun u₀ h₀ => ?_
  refine WP.mono (addImm_ok hL h₀.ctx (d := .x13) (by decide) h₀.val (k := fV) (by decide)) fun u₁ h₁ => ?_
  rw [Offset.add_add] at h₁
  refine WP.mono (x14_ok hL h₁.ctx (by rw [h₁.keep _ (by decide), h₀.val]) (k := 368 + k * P.H.D) (by anums))
    fun u₂ h₂ => ?_
  rw [show 16 + (368 + k * P.H.D) = 384 + k * P.H.D by omega] at h₂
  have hsep : Region.Disjoint ⟨L.B + BitVec.ofNat 64 80, P.H.D⟩ ⟨L.B + BitVec.ofNat 64 (384 + k * P.H.D), P.H.D⟩ :=
    Offset.disjoint _ (by anums) (by anums) (by have := hL.nB; anums)
  refine WP.mono (copyBX_ok hL h₂.ctx (src := .x13) (S := L.B + BitVec.ofNat 64 80) (d := 368 + k * P.H.D)
    (by rw [h₂.keep _ (by decide)]; exact h₁.val) (by decide) (by rw [h₂.val]; congr 2; omega) (by anums) (by anums)
    (by omega) (by rw [he]; omega)
    (fun j hj => by rw [Offset.add_add]; exact h₂.ctx.inFr (by omega) (by anums))
    (by rw [show 16 + (368 + k * P.H.D) = 384 + k * P.H.D by omega]; exact hsep))
    fun u₃ ⟨hc₃, _, hf₃, hb₃⟩ => ?_
  rw [show 16 + (368 + k * P.H.D) = 384 + k * P.H.D by omega] at hf₃ hb₃
  rw [h₂.mem, h₁.mem, h₀.mem] at hf₃ hb₃
  exact ⟨hc₃, hf₃, hb₃⟩

/-- The first `k` `V`s of the candidate: each `V = HMAC_K(V)`, copied to `T`
after the ones before. -/
theorem candW_ok (hL : L.Ok) (hLe : L.e = P.e) (hW : P.wide = true) (hT : TabL P L) :
    ∀ k, k * P.H.D ≤ 128 → ∀ {t : State}, Ctx L g m₀ t →
    WP isa ((cfgOf P).candW k) t fun u => Ctx L g m₀ u ∧ Frame (CWW L) t.mem u.mem ∧
      kOf P L u.mem = kOf P L t.mem ∧
      vOf P L u.mem = (Spec.Ecdsa.Rfc6979.genT P.ok.SH.H (kOf P L t.mem) k (vOf P L t.mem)).2 ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 384) (k * P.H.D) =
        (Spec.Ecdsa.Rfc6979.genT P.ok.SH.H (kOf P L t.mem) k (vOf P L t.mem)).1
  | 0, _, t, hc => WP.of_runBlock ⟨t, rfl, hc, Frame.refl _ _, rfl, rfl, by simp [Spec.Ecdsa.Rfc6979.genT,
      Spec.Sha256.bytesAt]⟩
  | k + 1, hk, t, hc => by
    have he := e272 hLe hW
    have hk' : k * P.H.D + P.H.D ≤ 128 := by rw [Nat.succ_mul] at hk; exact hk
    rw [Cfg.candW]
    refine WP.seq (WP.mono (candW_ok hL hLe hW hT k (by anums) hc) fun u₁ ⟨hc₁, hf₁, hk₁, hv₁, hb₁⟩ => ?_)
    refine WP.seq (WP.mono (hmacV_ok hL hT hc₁) fun u₂ ⟨hc₂, hf₂, hk₂, hv₂⟩ => ?_)
    refine WP.mono (keepV_ok hL hLe hW hc₂ hk') fun u₃ ⟨hc₃, hf₃, hb₃⟩ => ?_
    -- What the copy keeps: `K`, `V` and `scratch`.
    have dKV : ∀ {o : Nat}, 16 ≤ o → o + P.H.D ≤ 144 →
        Spec.Sha256.bytesAt u₃.mem (L.B + BitVec.ofNat 64 o) P.H.D = Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 o) P.H.D :=
      fun h₁ h₂ => bytesAt_frame hf₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega) (by anums) (by have := hL.nB; anums)) (by anums)
    have hk₃ : kOf P L u₃.mem = kOf P L u₂.mem := dKV (by decide) (by anums)
    have hv₃ : vOf P L u₃.mem = vOf P L u₂.mem := dKV (by decide) (by anums)
    refine ⟨hc₃, ?_, ?_, ?_, ?_⟩
    · refine ((hf₁.trans (hf₂.sub kvw_cww)).trans (hf₃.sub fun r hr => ?_))
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨L.B + BitVec.ofNat 64 384, 128⟩, by simp [CWW], Offset.sub _ (by omega) (by anums)⟩
    · rw [hk₃, hk₂, hk₁]
    · rw [hv₃, hv₂, genT_succ, hk₁, hv₁]
    · rw [genT_succ, Nat.succ_mul, Proof.Hmac.Common.bytesAt_add, Offset.add_add, hb₃, ← hb₁, hv₂, hk₁, hv₁]
      congr 1
      · -- `T`'s first `k` `V`s, kept by the HMAC and the copy.
        rw [bytesAt_frame hf₃ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Offset.disjoint _ (by omega) (by omega) (by have := hL.nB; anums)) (by anums)]
        exact bytesAt_frame hf₂ (fun r hr => by
          simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact hL.stk_SCR (by rw [he]; anums)
          · exact Offset.disjoint_base _ (by omega) (by anums)) (by anums)

/-- If `sh ≠ 0`: `T`'s first `Q` bytes shifted right by `sh` bits. -/
theorem candTop_ok (hL : L.Ok) (hLe : L.e = P.e) (hsh : P.R.sh ≠ 0) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).candTop t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 384, P.Q⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 384) P.Q =
        Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 384) P.Q) >>> P.R.sh) := by
  have hsl := P.R.nBits_len
  have hsc : (cfgOf P).sh = P.R.sh := rfl
  rw [Cfg.candTop, hsc, ite_eq_right_of_eq_false _ _ (eq_false hsh)]
  refine WP.mono (conv_ok hL hLe (wide_of_sh hsh) hc (o := fT) (s := P.R.sh) (by decide) (by decide) (by decide)
    (by omega) (by omega)) fun u ⟨hcu, hfu, hbu⟩ => ?_
  simp only [show 16 + fT = 384 from rfl] at hfu hbu
  exact ⟨hcu, hfu, hbu⟩

end VG.Proof.Ecdsa.Rfc6979.AArch64
