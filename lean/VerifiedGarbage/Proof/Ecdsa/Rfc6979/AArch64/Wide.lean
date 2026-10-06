import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Steps
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Weierstrass.AArch64.BytesLen

/-!
# Deterministic ECDSA on AArch64: scalars longer than the hash

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Wide.lean`), for a curve whose
scalars are longer than the hash function's output (`wide`: P-521's 66
bytes with SHA-512's 64): the `Q` bytes at an offset in the frame's top
bytes, shifted right in place through the words at `scratch + 2560`
(`conv_ok`, by `loadBytes_ok`, `shrWords_ok` and `storeBytes_ok`, with
`scratch` in `x0`); the digest for `core`, the digest then `Q - D` zero
bytes shifted right, which is the digest's number shifted left by `sh` bits
(`coreDigest_ok`); and the candidate, `V` kept in the frame's top bytes and,
after the next `V`, its first word after it, shifted right by `sh` bits
(`candW_ok`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64
open VG.Proof.Mont (wordsVal Outside off ofs)
open VG.Proof.Mont.AArch64 (Scr KeepRegs)
open VG.Proof.Weierstrass.AArch64 (loadBytes_ok shrWords_ok storeBytes_ok)

variable {P : RfcHash} {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} {L : Lay dn E} {g : Reg → BitVec 64} {m₀ : Mem}

/-- In the wide case, the frame has 144 bytes at its top. -/
theorem e144 (hw : L.wide = P.R.wide) (hW : P.R.wide = true) : L.e = 144 := by
  rw [L.ew, hw, hW]; rfl

/-- `x0 ← scratch`. -/
theorem ldScr_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) :
    WP isa (.block [.ldrSp .x0 fScratch]) u (Upd L g m₀ u .x0 L.scr) := by
  have h200 := hc.inFr (d := 200) (by omega) (by omega)
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
theorem conv_ok (hL : L.Ok) (hw : L.wide = P.R.wide) (hW : P.R.wide = true) {t : State} (hc : Ctx L g m₀ t)
    {o s : Nat} (ho₁ : 224 ≤ o) (ho₂ : o + 72 ≤ 368) (ho8 : o % 8 = 0) (hs₁ : 1 ≤ s) (hs₂ : s < 64) :
    WP isa ((cfgOf P).conv o s) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 (16 + o), P.Q⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 (16 + o)) P.Q =
        Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 (16 + o)) P.Q) >>> s) := by
  obtain ⟨hw9, hQ66, -, -⟩ := P.sizesW hW
  have he := e144 hw hW
  have nB := hL.nB
  have nc := hL.nc
  have hcw : (cfgOf P).w = 9 := hw9
  have hcl : (cfgOf P).len = 66 := hQ66
  simp only [Cfg.conv, hcw, hcl]
  rw [hQ66]
  refine WP.seq (WP.mono_syms (ldScr_ok hL hc) fun u₁ h₁ sy₁ => ?_)
  rw [show ∀ (l : List Instr), Instr.addSp .x6 o :: l = Cfg.fr .x6 o ++ l from fun _ => rfl]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono_syms (fr_ok hL h₁.ctx (d := .x6) (by decide) (o := o) (by omega)) fun u₂ h₂ sy₂ => ?_
  have hc₂ := h₂.ctx
  have hS₂ : Scr u₂ L.scr 8192 :=
    ⟨by rw [h₂.keep _ (by decide), h₁.val], by rw [hc₂.wr]; simp, nc, by decide⟩
  have hx6 : u₂.gpr .x6 = L.B + BitVec.ofNat 64 (16 + o) := h₂.val
  rw [WP.block_append_iff]
  refine WP.mono_syms (loadBytes_ok hS₂ (len := 66) (n := 9) (o := 2560) (src := .x6) (by decide) (by decide)
    (by omega) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun d hd => by rw [hx6, Offset.add_add]; exact hc₂.inFr (by omega) (by omega))
    (by rw [hx6]; exact (hL.stk_scr (by omega) (by omega)))) fun u₃ ⟨hv₃, k₃, O₃⟩ sy₃ => ?_
  rw [WP.block_append_iff]
  have hS₃ : Scr u₃ L.scr 8192 := ⟨by rw [k₃.gpr _ (by decide)]; exact hS₂.x0, k₃.wr ▸ hS₂.wr, nc, by decide⟩
  refine WP.mono_syms (shrWords_ok hS₃ (n := 9) (o := 2560) (sh := s) (by omega) (by decide) hs₁ hs₂)
    fun u₄ ⟨hv₄, k₄, O₄⟩ sy₄ => ?_
  rw [WP.block_append_iff]
  refine WP.mono_syms (ones_ok u₄) fun u₅ ⟨h3₅, k₅, m₅, _⟩ sy₅ => ?_
  have hS₅ : Scr u₅ L.scr 8192 :=
    ⟨by rw [k₅.gpr _ (by decide), k₄.gpr _ (by decide)]; exact hS₃.x0, k₅.wr ▸ k₄.wr ▸ hS₃.wr, nc, by decide⟩
  have hx6₅ : u₅.gpr .x6 = L.B + BitVec.ofNat 64 (16 + o) := by
    rw [k₅.gpr _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (by decide), hx6]
  have hwr₅ : u₅.wr = u₂.wr := by rw [k₅.wr, k₄.wr, k₃.wr]
  refine WP.mono_syms (storeBytes_ok hS₅ (len := 66) (n := 9) (d := 0) (a := 2560) (dst := .x6) (by decide)
    (by decide) (by decide) true (by rw [h3₅]; rfl) (by omega) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by rw [hx6₅, add_ofNat_zero, toNat_add_of (by omega)]; omega)
    (fun e m hem => by
      rw [hx6₅, add_ofNat_zero, Offset.add_add, hwr₅]; exact hc₂.inFrW (by omega) (by omega))
    (by rw [hx6₅, add_ofNat_zero]; exact (hL.stk_scr (by omega) (by omega)).symm)) fun u₆ ⟨hb₆, k₆, O₆⟩ sy₆ => ?_
  rw [hx6₅, add_ofNat_zero] at hb₆ O₆
  -- What changed: the words at `scratch + 2560`, and the bytes converted.
  have hf : Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 (16 + o), 66⟩] t.mem u₆.mem := by
    have f₃ := frame_of_outside (O₃.trans O₄) (by omega)
    have f₆ := frame_of_outside O₆ (by omega)
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
    · exact safe_scr L (by omega)
    · exact safe_high L (by omega) (by omega)
  · rw [← Rfc6979.ecdsa_bytesAt, hb₆]
    simp only [ite_true]
    rw [m₅, hv₄, hv₃, hx6, h₂.mem, h₁.mem, Rfc6979.ecdsa_bytesAt]

/-! ## Copies into the frame's top bytes -/

/-- `8 K` bytes copied to `sp + d`, in the frame's top bytes, by `copyN`, with `Ctx` kept. -/
theorem copyF_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (h15 : u.gpr .x15 = L.B + BitVec.ofNat 64 16)
    {src : Reg} {S : Addr} (hs : u.gpr src = S) (hsr : src ≠ .x11) {so d K : Nat} (hd₁ : 224 ≤ d)
    (hd₂ : d + 8 * K ≤ 224 + L.e) (hd8 : d % 8 = 0) (hso : so % 8 = 0 ∧ so + 8 * K ≤ 32768)
    (hr : ∀ j < K, InRegions (u.rd ++ u.wr) (S + BitVec.ofNat 64 (so + 8 * j)) 8)
    (hsep : Region.Disjoint ⟨S + BitVec.ofNat 64 so, 8 * K⟩ ⟨L.B + BitVec.ofNat 64 (16 + d), 8 * K⟩) :
    WP isa (.block (Cfg.copyN K src so .x15 d)) u fun u' => Ctx L g m₀ u' ∧
      (∀ r, r ≠ .x11 → u'.gpr r = u.gpr r) ∧ Frame [⟨L.B + BitVec.ofNat 64 (16 + d), 8 * K⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (16 + d)) (8 * K) =
        Spec.Sha256.bytesAt u.mem (S + BitVec.ofNat 64 so) (8 * K) := by
  have nB := hL.nB
  have he := L.he
  have hsep' := hsep
  rw [← Offset.add_add] at hsep'
  refine WP.mono_syms (copyN_ok (K := K) (by decide) hsr hsep' (by omega) hso ⟨hd8, by omega⟩ K (Nat.le_refl _)
    u hs h15 hr fun j hj => by rw [Offset.add_add]; exact hc.inFrW (by omega) (by omega))
    fun u' ⟨hrd, hwr, hsp, hg, hf, hb⟩ hsy => ?_
  rw [Offset.add_add] at hf hb
  exact ⟨hc.keep hL hrd hwr hsp (fun r hr _ => hg r (ne_cs hr (by decide))) hf (hsy := hsy)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_high L (by omega) (by omega)),
    hg, hf, hb⟩

/-- A zero word at `sp + o`, in the frame's top bytes, through `x11`. -/
theorem zeroF_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (h15 : u.gpr .x15 = L.B + BitVec.ofNat 64 16)
    {o : Nat} (ho₁ : 224 ≤ o) (ho₂ : o + 8 ≤ 224 + L.e) (ho8 : o % 8 = 0) :
    WP isa (.block [.movz .x .x11 0 0, .str .x .x11 .x15 o]) u fun u' => Ctx L g m₀ u' ∧
      (∀ r, r ≠ .x11 → u'.gpr r = u.gpr r) ∧ Frame [⟨L.B + BitVec.ofNat 64 (16 + o), 8⟩] u.mem u'.mem ∧
      ∀ k ≤ 8, Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (16 + o)) k = List.replicate k 0 := by
  have nB := hL.nB
  have he := L.he
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movz_ok hL hc (d := .x11) (by decide) (n := 0) (by decide)) fun u₁ h₁ => ?_
  refine WP.mono_syms (strW_ok (t := .x11) (dst := .x15) (D := L.B + BitVec.ofNat 64 16) (d := o)
    (by rw [h₁.keep _ (by decide), h15]) ⟨ho8, by omega⟩
    (by rw [Offset.add_add]; exact h₁.ctx.inFrW (by omega) (by omega))) fun u₂ ⟨hrd, hwr, hsp, hg, _, hm⟩ hsy => ?_
  rw [Offset.add_add, h₁.val] at hm
  have hf : Frame [⟨L.B + BitVec.ofNat 64 (16 + o), 8⟩] u₁.mem u₂.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨h₁.ctx.keep hL hrd hwr hsp (fun r _ _ => by rw [hg]) hf (hsy := hsy)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_high L (by omega) (by omega)),
    fun r hr => by rw [hg, h₁.keep _ hr], h₁.mem ▸ hf, fun k hk => by
      rw [hm]; exact bytesAt_writeW_zero64 _ _ hk⟩

/-- `sh` is 7 for P-521's sizes. -/
theorem sh7 (hW : P.R.wide = true) : P.R.sh = 7 := by
  have h₁ := P.R.nBits_len; have h₂ := P.R.sizesW hW; omega

theorem shift_mul (e : Nat) : (e * 2 ^ (8 * 2)) >>> 9 = e * 2 ^ 7 := by
  rw [Nat.shiftRight_eq_div_pow, show e * 2 ^ (8 * 2) = e * 2 ^ 7 * 2 ^ 9 by rw [Nat.mul_assoc, ← Nat.pow_add],
    Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

/-! ## The digest for `core` -/

/-- The digest (at `x1`) and a zero word after it, in the frame's top bytes. -/
theorem dig_ok (hL : L.Ok) (hw : L.wide = P.R.wide) (hW : P.R.wide = true) (hdn : P.H.D ≤ dn)
    {t : State} (hc : Ctx L g m₀ t) (h1 : t.gpr .x1 = L.dg) :
    WP isa (.block (([.addSp .x15 0, .movz .x .x11 0 0, .str .x .x11 .x15 (fX + (cfgOf P).H.D)] : List Instr) ++
      Cfg.copyN ((cfgOf P).H.D / 8) .x1 0 .x15 fX)) t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.B + BitVec.ofNat 64 240, 72⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 240) 66 =
        Spec.Sha256.bytesAt t.mem L.dg 64 ++ List.replicate 2 0 := by
  obtain ⟨-, -, hD64, -⟩ := P.sizesW hW
  have he := e144 hw hW
  have nB := hL.nB
  have ng := hL.ng
  have hcD : (cfgOf P).H.D = 64 := hD64
  simp only [hcD, fX, Nat.reduceAdd, Nat.reduceDiv]
  rw [hD64] at hdn
  rw [List.cons_append, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (fr_ok hL hc (d := .x15) (by decide) (o := 0) (by decide)) fun u₁ h₁ => ?_
  have h15 : u₁.gpr .x15 = L.B + BitVec.ofNat 64 16 := h₁.val
  rw [WP.block_append_iff]
  refine WP.mono (zeroF_ok hL h₁.ctx h15 (o := 288) (by omega) (by omega) (by decide))
    fun u₂ ⟨hc₂, hg₂, hf₂, hz₂⟩ => ?_
  have hdgSep : Region.Disjoint ⟨L.dg, 64⟩ ⟨L.B + BitVec.ofNat 64 240, 72⟩ :=
    (hL.stk_DG (d := 240) (n := 72) (by omega)).symm.sub_left (Region.sub_prefix hdn)
  have hdg₂ : Spec.Sha256.bytesAt u₂.mem L.dg 64 = Spec.Sha256.bytesAt t.mem L.dg 64 := by
    rw [bytesAt_frame hf₂ (p := L.dg) (n := 64) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hdgSep.sub_right (Offset.sub _ (by omega) (by omega))) (by omega), h₁.mem]
  refine WP.mono (copyF_ok hL hc₂ (by rw [hg₂ _ (by decide)]; exact h15) (src := .x1) (S := L.dg)
    (by rw [hg₂ _ (by decide), h₁.keep _ (by decide), h1]) (by decide) (so := 0) (d := 224) (K := 8)
    (by omega) (by omega) (by decide) ⟨by decide, by decide⟩ (fun j hj => hc₂.inDg (by omega) (by omega))
    (by rw [add_ofNat_zero]; exact hdgSep.sub_right (Region.sub_prefix (by omega))))
    fun u₃ ⟨hc₃, _, hf₃, hb₃⟩ => ?_
  rw [add_ofNat_zero] at hb₃
  simp only [Nat.reduceAdd, Nat.reduceMul] at hf₂ hz₂ hf₃ hb₃
  refine ⟨hc₃, ?_, ?_⟩
  · rw [← h₁.mem]
    refine (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      (hf₃.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    · simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega) (by omega)
    · simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega)
  · rw [show (66 : Nat) = 64 + 2 from rfl, Proof.Hmac.Common.bytesAt_add, hb₃, hdg₂, Offset.add_add]
    refine congrArg (Spec.Sha256.bytesAt t.mem L.dg 64 ++ ·) ?_
    rw [bytesAt_frame hf₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega) (by omega) (by omega))
        (by omega)]
    have h4 := hz₂ (2 + 6) (by omega)
    rw [Proof.Hmac.Common.bytesAt_add, ← List.replicate_append_replicate] at h4
    simp only [Nat.reduceAdd] at h4 ⊢
    exact (List.append_inj h4 (by simp [Spec.Sha256.bytesAt])).1

/-- The digest for `core`: the digest's number shifted left by `sh` bits, in
`Q` bytes in the frame's top bytes. -/
theorem coreDigest_ok (hL : L.Ok) (hw : L.wide = P.R.wide) (hW : P.R.wide = true) (hdn : P.H.D ≤ dn)
    {t : State} (hc : Ctx L g m₀ t) (h1 : t.gpr .x1 = L.dg) :
    WP isa (cfgOf P).coreDigest t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 240, 72⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 240) P.Q =
        Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem L.dg P.H.D) * 2 ^ P.R.sh) := by
  obtain ⟨-, hQ66, hD64, -⟩ := P.sizesW hW
  have he := e144 hw hW
  have hsh := sh7 hW
  have hcD : (cfgOf P).H.D = 64 := hD64
  have hcl : (cfgOf P).len = 66 := hQ66
  have hcs : (cfgOf P).sh = 7 := hsh
  rw [Cfg.coreDigest]
  refine WP.seq (WP.mono (dig_ok hL hw hW hdn hc h1) fun u₁ ⟨hc₁, hf₁, hY⟩ => ?_)
  rw [hcD, hcl, hcs, show 8 * (66 - 64) - 7 = 9 from rfl]
  refine WP.mono (conv_ok hL hw hW hc₁ (o := fX) (s := 9) (by decide) (by decide) (by decide) (by omega)
    (by omega)) fun u₂ ⟨hc₂, hf₂, hb₂⟩ => ?_
  simp only [fX, Nat.reduceAdd] at hf₂ hb₂
  rw [hQ66] at hf₂ hb₂ ⊢
  refine ⟨hc₂, ?_, ?_⟩
  · refine (hf₁.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩).trans
      (hf₂.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact sub_refl _
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., sub_refl _⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Region.sub_prefix (by omega)⟩
  · -- The digest then two zero bytes, shifted right by 9 bits.
    rw [hb₂, hY, hD64, hsh, ofBytes_append_zeros, shift_mul]

/-! ## The candidate -/

/-- `V`'s `D` bytes to the candidate's place. -/
theorem keepV_ok (hL : L.Ok) (hw : L.wide = P.R.wide) (hW : P.R.wide = true) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block (cfgOf P).keepV) t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.B + BitVec.ofNat 64 312, 64⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 312) 64 = vOf P L t.mem := by
  obtain ⟨-, -, hD64, -⟩ := P.sizesW hW
  have he := e144 hw hW
  have nB := hL.nB
  have hcD : (cfgOf P).H.D = 64 := hD64
  simp only [Cfg.keepV, hcD, fV, fKb, Nat.reduceDiv]
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (fr_ok hL hc (d := .x15) (by decide) (o := 0) (by decide)) fun u₁ h₁ => ?_
  have h15 : u₁.gpr .x15 = L.B + BitVec.ofNat 64 16 := h₁.val
  refine WP.mono (copyF_ok hL h₁.ctx h15 h15 (by decide) (so := 64) (d := 296) (K := 8) (by omega) (by omega)
    (by decide) ⟨by decide, by decide⟩ (fun j hj => by rw [Offset.add_add]; exact h₁.ctx.inFr (by omega) (by omega))
    (by rw [Offset.add_add]; exact Offset.disjoint _ (by omega) (by omega) (by omega)))
    fun u₂ ⟨hc₂, _, hf₂, hb₂⟩ => ?_
  simp only [Offset.add_add, Nat.reduceAdd, Nat.reduceMul] at hf₂ hb₂
  rw [h₁.mem] at hf₂ hb₂
  exact ⟨hc₂, hf₂, by rw [hb₂, vOf, hD64]⟩

/-- The candidate's next eight bytes, from `V`. -/
theorem top_ok (hL : L.Ok) (hw : L.wide = P.R.wide) (hW : P.R.wide = true) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block [.addSp .x15 0, .ldr .x .x11 .x15 fV, .str .x .x11 .x15 (fKb + (cfgOf P).H.D)]) t fun u =>
      Ctx L g m₀ u ∧ Frame [⟨L.B + BitVec.ofNat 64 376, 8⟩] t.mem u.mem ∧
      u.mem = t.mem.writeW (L.B + BitVec.ofNat 64 376) (t.mem.readW (L.B + BitVec.ofNat 64 80) 64) := by
  obtain ⟨-, -, hD64, -⟩ := P.sizesW hW
  have he := e144 hw hW
  have nB := hL.nB
  have hcD : (cfgOf P).H.D = 64 := hD64
  simp only [hcD, fV, fKb, Nat.reduceAdd]
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (fr_ok hL hc (d := .x15) (by decide) (o := 0) (by decide)) fun u₄ h₄ => ?_
  have h15 : u₄.gpr .x15 = L.B + BitVec.ofNat 64 16 := h₄.val
  refine WP.mono_syms (copyW_ok (u := u₄) (src := .x15) (dst := .x15) (so := 64) (d := 360) h15 h15
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by rw [Offset.add_add]; exact h₄.ctx.inFr (by omega) (by omega))
    (by rw [Offset.add_add]; exact h₄.ctx.inFrW (by omega) (by omega)) (by decide))
    fun u₅ ⟨hrd₅, hwr₅, hsp₅, hg₅, hm₅⟩ hsy₅ => ?_
  rw [Offset.add_add, Offset.add_add, h₄.mem] at hm₅
  simp only [Nat.reduceAdd] at hm₅
  have hf₅ : Frame [⟨L.B + BitVec.ofNat 64 376, 8⟩] t.mem u₅.mem := by
    rw [hm₅]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨h₄.ctx.keep hL hrd₅ hwr₅ hsp₅ (fun r hr _ => hg₅ r (ne_cs hr (by decide))) (h₄.mem ▸ hf₅)
    (hsy := hsy₅) fun r hr => ?_, hf₅, hm₅⟩
  simp only [List.mem_singleton] at hr; subst hr; exact safe_high L (by omega) (by omega)

/-- What a candidate changes: `scratch`, the stack below the frame, `K` and
`V`, and the candidate in the frame's top bytes. -/
abbrev CWW {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) : List Region :=
  [L.SCR, ⟨L.B, 144⟩, ⟨L.B + BitVec.ofNat 64 312, 72⟩]

theorem kvw_cww : ∀ r ∈ KVW L, ∃ r' ∈ CWW L, Region.Sub r r' := fun r hr => ⟨r, by
  simp only [CWW, KVW, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
  rcases hr with h | h <;> simp [h], sub_refl _⟩

/-- Two `V`s to a candidate: `V = HMAC_K(V)`, kept in the frame's top
bytes, then `V = HMAC_K(V)` again, its first word after it, and the
candidate's `Q` bytes shifted right by `sh` bits. -/
theorem candW_ok (hL : L.Ok) (hw : L.wide = P.R.wide) (hW : P.R.wide = true) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).cand t fun u => Ctx L g m₀ u ∧ Frame (CWW L) t.mem u.mem ∧
      kOf P L u.mem = kOf P L t.mem ∧
      vOf P L u.mem = P.mac (kOf P L t.mem) (P.mac (kOf P L t.mem) (vOf P L t.mem)) ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 312) P.Q =
        Spec.Weierstrass.toBytes P.Q (Spec.Weierstrass.ofBytes ((P.mac (kOf P L t.mem) (vOf P L t.mem) ++
          P.mac (kOf P L t.mem) (P.mac (kOf P L t.mem) (vOf P L t.mem))).take P.Q) >>> P.R.sh) := by
  obtain ⟨-, hQ66, hD64, -⟩ := P.sizesW hW
  have he := e144 hw hW
  have hsh := sh7 hW
  have nB := hL.nB
  have hwd : (cfgOf P).wide = true := hW
  have hcD : (cfgOf P).H.D = 64 := hD64
  simp only [Cfg.cand, Cfg.candTop, hwd, ite_true]
  refine WP.seq (WP.mono (hmacV_ok hL hc) fun u₁ ⟨hc₁, hf₁, hk₁, hv₁⟩ => ?_)
  -- `V` in the frame's top bytes.
  refine WP.seq (WP.mono (keepV_ok hL hw hW hc₁) fun u₂ ⟨hc₂, hf₂, hb₂⟩ => ?_)
  have kv₂ : ∀ r ∈ [(⟨L.B + BitVec.ofNat 64 312, 64⟩ : Region)], Region.Disjoint ⟨L.B, 144⟩ r := by
    simp only [List.mem_singleton]; rintro r rfl; exact (Offset.disjoint_base _ (by omega) (by omega)).symm
  have kv : ∀ {m m' : Mem} {ws : List Region}, Frame ws m m' → (∀ r ∈ ws, Region.Disjoint ⟨L.B, 144⟩ r) →
      kOf P L m' = kOf P L m ∧ vOf P L m' = vOf P L m := fun hf hd =>
    ⟨bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Offset.sub_base _ (by anums))) (by anums),
      bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Offset.sub_base _ (by anums))) (by anums)⟩
  have e₂ := kv hf₂ kv₂
  refine WP.seq (WP.mono (hmacV_ok hL hc₂) fun u₃ ⟨hc₃, hf₃, hk₃, hv₃⟩ => ?_)
  have hb₃ : Spec.Sha256.bytesAt u₃.mem (L.B + BitVec.ofNat 64 312) 64 = vOf P L u₁.mem := by
    rw [bytesAt_frame hf₃ (fun r hr => by
      simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hL.stk_SCR (by omega)
      · exact Offset.disjoint_base _ (by omega) (by omega)) (by omega), hb₂]
  refine WP.seq (WP.mono (top_ok hL hw hW hc₃) fun u₅ ⟨hc₅, hf₅, hm₅⟩ => ?_)
  refine WP.mono (conv_ok hL hw hW hc₅ (o := 296) (s := P.R.sh) (by omega) (by omega) (by decide) (by omega)
    (by omega)) fun u₆ ⟨hc₆, hf₆, hb₆⟩ => ?_
  simp only [Nat.reduceAdd] at hf₆ hb₆
  have dK₆ : ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 2560, 72⟩ : Region), ⟨L.B + BitVec.ofNat 64 312, P.Q⟩],
      Region.Disjoint ⟨L.B, 144⟩ r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact (hL.kc.sub_left (Region.sub_prefix (by omega))).sub_right (Offset.sub_base _ (by omega))
    · exact (Offset.disjoint_base _ (by omega) (by omega)).symm
  have dK₅ : ∀ r ∈ [(⟨L.B + BitVec.ofNat 64 376, 8⟩ : Region)], Region.Disjoint ⟨L.B, 144⟩ r := by
    simp only [List.mem_singleton]; rintro r rfl; exact (Offset.disjoint_base _ (by omega) (by omega)).symm
  have e₆ := kv hf₆ dK₆
  have e₅ := kv hf₅ dK₅
  refine ⟨hc₆, ?_, ?_, ?_, ?_⟩
  · have c₃ : (⟨L.B + BitVec.ofNat 64 312, 72⟩ : Region) ∈ CWW L := by simp [CWW]
    have c₁ : L.SCR ∈ CWW L := by simp [CWW]
    refine ((((hf₁.sub kvw_cww).trans (hf₂.sub fun r hr => ⟨_, c₃, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega)⟩)).trans
      (hf₃.sub kvw_cww)).trans (hf₅.sub fun r hr => ⟨_, c₃, by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega) (by omega)⟩)).trans
      (hf₆.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, c₁, Offset.sub_base _ (by omega)⟩
    · exact ⟨_, c₃, Offset.sub _ (by omega) (by omega)⟩
  · rw [e₆.1, e₅.1, hk₃, e₂.1, hk₁]
  · rw [e₆.2, e₅.2, hv₃, e₂.1, e₂.2, hv₁, hk₁]
  · -- The candidate's bytes: the first `V`, then the next two of the second.
    have hkv : P.mac (kOf P L t.mem) (vOf P L t.mem) = vOf P L u₁.mem := hv₁.symm
    have hv₃' : P.mac (kOf P L t.mem) (P.mac (kOf P L t.mem) (vOf P L t.mem)) = vOf P L u₃.mem := by
      rw [hv₃, e₂.1, e₂.2, hv₁, hk₁]
    rw [hQ66] at hb₆ ⊢
    rw [hb₆, hv₃', hkv, List.take_append, List.take_of_length_le (by simp [Spec.Sha256.bytesAt]; omega),
      show 66 - (vOf P L u₁.mem).length = 2 by simp [Spec.Sha256.bytesAt]; omega]
    refine congrArg (fun x => Spec.Weierstrass.toBytes 66 (Spec.Weierstrass.ofBytes x >>> P.R.sh)) ?_
    rw [show (66 : Nat) = 64 + 2 from rfl, Proof.Hmac.Common.bytesAt_add, Offset.add_add]
    simp only [Nat.reduceAdd]
    refine congrArg₂ (· ++ ·) ?_ ?_
    · rw [bytesAt_frame hf₅ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega) (by omega) (by omega))
          (by omega), hb₃]
    · rw [bytesAt_take _ _ (k := 8) (by omega), hm₅, bytesAt_copied]
      show _ = (Spec.Sha256.bytesAt u₃.mem (L.B + BitVec.ofNat 64 80) P.H.D).take 2
      rw [hD64, ← bytesAt_take _ _ (by omega), ← bytesAt_take _ _ (by omega)]

end VG.Proof.Ecdsa.Rfc6979.AArch64
