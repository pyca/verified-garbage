module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Steps
public import VerifiedGarbage.Proof.Mont.AArch64.Words
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Weierstrass.AArch64.BytesLen
import Mathlib.Logic.Function.Basic
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Copy
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Msg
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Reduce
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import Mathlib.Tactic.Conv
import Mathlib.Tactic.SplitIfs

/-!
# Deterministic ECDSA on AArch64: P-521's shifts, and the candidate's `V`s

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Wide.lean`), for P-521 (`big`),
whose scalars are longer than any digest and whose `n` has fewer bits than
them: the `Q` bytes at an offset above the frame's pointers, shifted right
in place through the words at `scratch + 2560` (`conv_ok`, by
`loadBytes_ok`, `shrWords_ok` and `storeBytes_ok`, with `scratch` in `x0`),
as for the candidate `T`'s first `Q` bytes (`candTop_ok`); zero words above
the pointers (`zero9_ok`); and `genT` with one more `V` (`genT_succ`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64
open VG.Proof.Mont (wordsVal Outside off ofs)
open VG.Proof.Mont.AArch64 (Scr KeepRegs)
open VG.Proof.Weierstrass.AArch64 (loadBytes_ok shrWords_ok storeBytes_ok)

variable {P : RfcHash} {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} {L : Lay dn E} {g : Reg → BitVec 64} {m₀ : Mem}

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

/-- `conv o s`: the `Q` bytes at `sp + o`, in the frame's top bytes, shifted
right by `s` bits in place, through the words at `scratch + 2560`. -/
theorem conv_ok (hL : L.Ok) (hW : P.R.big = true) {t : State} (hc : Ctx L g m₀ t)
    {o s : Nat} (ho₁ : 232 ≤ o) (ho₂ : o + 72 ≤ 600) (ho8 : o % 8 = 0) (hs₁ : 1 ≤ s) (hs₂ : s < 64) :
    WP isa ((cfgOf P).conv o s) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 (16 + o), P.Q⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 (16 + o)) P.Q =
        Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 (16 + o)) P.Q) >>> s) := by
  obtain ⟨hw9, hQ66, -⟩ := P.sizesW hW
  have he := L.he
  have nB := hL.nB
  have nc := hL.nc
  have hcw : (cfgOf P).w = 9 := hw9
  have hcl : (cfgOf P).len = 66 := hQ66
  simp only [Cfg.conv, Cfg.convB, hcw, hcl]
  rw [hQ66]
  refine WP.seq (WP.mono_syms (ldScr_ok hL hc) fun u₁ h₁ sy₁ => ?_)
  rw [show ∀ (l : List Instr), Instr.addSp .x6 o :: l = Cfg.fr .x6 o ++ l from fun _ => rfl]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono_syms (fr_ok hL h₁.ctx (d := .x6) (by decide) (o := o) (by omega_arith)) fun u₂ h₂ sy₂ => ?_
  have hc₂ := h₂.ctx
  have hS₂ : Scr u₂ L.scr 8192 :=
    ⟨by rw [h₂.keep _ (by decide), h₁.val], by rw [hc₂.wr]; simp, nc, by decide⟩
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
    rw [h₂.mem, h₁.mem, show 8 * 9 = 72 from rfl] at f₃
    exact (f₃.sub fun r hr => ⟨r, by simp_all, sub_refl _⟩).trans (f₆.sub fun r hr => ⟨r, by simp_all, sub_refl _⟩)
  have hk : ∀ r ∈ preserved, r ≠ .x30 → u₆.gpr r = t.gpr r := fun r hr h30 => by
    rw [keep_pres k₆ (by decide) r hr h30, keep_pres k₅ (by decide) r hr h30, keep_pres k₄ (by decide) r hr h30,
      keep_pres k₃ (by decide) r hr h30, h₂.keep _ (ne_cs hr (by decide)), h₁.keep _ (ne_cs hr (by decide))]
  refine ⟨hc.keep hL (by rw [k₆.rd, k₅.rd, k₄.rd, k₃.rd, hc₂.rd, hc.rd]) (by rw [k₆.wr, hwr₅, hc₂.wr, hc.wr])
      (by rw [k₆.sp, k₅.sp, k₄.sp, k₃.sp, hc₂.sp, hc.sp]) hk hf (fun r hr => ?_)
      (by rw [sy₆, sy₅, sy₄, sy₃, sy₂, sy₁]), hf, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact safe_scr L (by omega_arith)
    · exact safe_high L (by omega_arith) (by omega_arith)
  · rw [← Rfc6979.ecdsa_bytesAt, hb₆]
    simp only [ite_true]
    rw [m₅, hv₄, hv₃, hx6, h₂.mem, h₁.mem, Rfc6979.ecdsa_bytesAt]

/-! ## Zero words -/

/-- A zero word (`x14`) at `sp + o` (from `x15`), above the frame's pointers. -/
theorem zstr_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (h15 : u.gpr .x15 = L.B + BitVec.ofNat 64 16)
    (h14 : u.gpr .x14 = 0) {o : Nat} (ho₁ : 232 ≤ o) (ho₂ : o + 8 ≤ 216 + 8 * L.e) (ho8 : o % 8 = 0) :
    WP isa (.block [.str .x .x14 .x15 o]) u fun u' => Ctx L g m₀ u' ∧ u'.gpr = u.gpr ∧
      Frame [⟨L.B + BitVec.ofNat 64 (16 + o), 8⟩] u.mem u'.mem ∧
      ∀ k ≤ 8, Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (16 + o)) k = List.replicate k 0 := by
  have nB := hL.nB
  have he := L.he
  refine WP.mono_syms (strW_ok (t := .x14) (dst := .x15) (D := L.B + BitVec.ofNat 64 16) (d := o) h15
    ⟨ho8, by omega_arith⟩ (by rw [Offset.add_add]; exact hc.inFrW (by omega_arith) (by omega_arith)))
    fun u₂ ⟨hrd, hwr, hsp, hg, _, hm⟩ hsy => ?_
  rw [Offset.add_add, h14] at hm
  have hf : Frame [⟨L.B + BitVec.ofNat 64 (16 + o), 8⟩] u.mem u₂.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  exact ⟨hc.keep hL hrd hwr hsp (fun r _ _ => by rw [hg]) hf (hsy := hsy)
    (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact safe_high L (d := 16 + o) (n := 8) (by omega) (by omega)),
    hg, hf, fun k hk => by rw [hm]; exact bytesAt_writeW_zero64 _ _ hk⟩

/-- `k` zero words at `sp + o`, above the frame's pointers. -/
theorem zstrs_ok (hL : L.Ok) {o : Nat} (ho₁ : 232 ≤ o) (ho₂ : o + 72 ≤ 216 + 8 * L.e) (ho8 : o % 8 = 0) :
    ∀ k ≤ 9, ∀ {u : State}, Ctx L g m₀ u → u.gpr .x15 = L.B + BitVec.ofNat 64 16 → u.gpr .x14 = 0 →
    WP isa (.block ((List.range k).map fun j => Instr.str .x .x14 .x15 (o + 8 * j))) u
      fun u' => Ctx L g m₀ u' ∧ u'.gpr = u.gpr ∧ Frame [⟨L.B + BitVec.ofNat 64 (16 + o), 72⟩] u.mem u'.mem ∧
        Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (16 + o)) (8 * k) = List.replicate (8 * k) 0
  | 0, _, u, hc, _, _ => WP.of_runBlock ⟨u, rfl, hc, rfl, Frame.refl _ _, rfl⟩
  | k + 1, hk, u, hc, h15, h14 => by
    have := hL.nB
    have := L.he
    rw [List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (zstrs_ok hL ho₁ ho₂ ho8 k (by omega) hc h15 h14) fun u₁ ⟨hc₁, hg₁, hf₁, hb₁⟩ => ?_
    refine WP.mono (zstr_ok hL hc₁ (by rw [hg₁, h15]) (by rw [hg₁, h14]) (o := o + 8 * k) (by omega) (by omega)
      (by omega)) fun u₂ ⟨hc₂, hg₂, hf₂, hb₂⟩ => ?_
    refine ⟨hc₂, hg₂.trans hg₁, hf₁.trans (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _,
      by simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega) (by omega)⟩), ?_⟩
    rw [show 8 * (k + 1) = 8 * k + 8 by omega, Proof.Hmac.Common.bytesAt_add, Offset.add_add,
      show 16 + o + 8 * k = 16 + (o + 8 * k) by omega, hb₂ 8 (Nat.le_refl _),
      bytesAt_frame hf₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega), hb₁, List.replicate_append_replicate]

/-- Nine zero words at `sp + o`, above the frame's pointers, through `x15` and `x14`. -/
theorem zero9_ok (hL : L.Ok) {o : Nat} (ho₁ : 232 ≤ o) (ho₂ : o + 72 ≤ 216 + 8 * L.e) (ho8 : o % 8 = 0)
    {u : State} (hc : Ctx L g m₀ u) :
    WP isa (.block (Cfg.zero9 o)) u fun u' => Ctx L g m₀ u' ∧
      (∀ r, r ≠ .x14 → r ≠ .x15 → u'.gpr r = u.gpr r) ∧ u'.gpr .x15 = L.B + BitVec.ofNat 64 16 ∧
      Frame [⟨L.B + BitVec.ofNat 64 (16 + o), 72⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (16 + o)) 72 = List.replicate 72 0 := by
  rw [Cfg.zero9, WP.block_append_iff, show ([.addSp .x15 0, .movz .x .x14 0 0] : List Instr) =
    Cfg.fr .x15 0 ++ [.movz .x .x14 0 0] from rfl, WP.block_append_iff]
  refine WP.mono (fr_ok hL hc (d := .x15) (by decide) (o := 0) (by decide)) fun u₁ h₁ => ?_
  refine WP.mono (movz_ok hL h₁.ctx (d := .x14) (by decide) (n := 0) (by decide)) fun u₂ h₂ => ?_
  rw [Nat.add_zero] at h₁
  refine WP.mono (zstrs_ok hL ho₁ ho₂ ho8 9 (Nat.le_refl _) h₂.ctx (by rw [h₂.keep _ (by decide), h₁.val]) h₂.val)
    fun u' ⟨hc', hg', hf', hb'⟩ => ⟨hc', fun r a b => by rw [hg', h₂.keep _ a, h₁.keep _ b],
      by rw [hg', h₂.keep _ (by decide), h₁.val], by rw [h₂.mem, h₁.mem] at hf'; exact hf', hb'⟩

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
    rw [genT_succ, List.length_append, genT_length P K k V, mac_length]
    rw [Nat.succ_mul]

/-- If `big`: `T`'s first `Q` bytes shifted right by `sh` bits. -/
theorem candTop_ok (hL : L.Ok) (hW : P.R.big = true) (hsh : P.R.sh ≠ 0) (hsh8 : P.R.sh < 8) {t : State}
    (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).candTop t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 (16 + fT), P.Q⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (16 + fT)) P.Q =
        Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 (16 + fT)) P.Q) >>> P.R.sh) := by
  have hsc : (cfgOf P).sh = P.R.sh := rfl
  have hbc : (cfgOf P).big = true := hW
  rw [Cfg.candTop, hbc, ite_eq_left_of_eq_true _ _ (eq_self true), hsc]
  exact conv_ok hL hW hc (o := fT) (s := P.R.sh) (by decide) (by decide) (by decide) (by omega) (by omega)

end VG.Proof.Ecdsa.Rfc6979.AArch64
