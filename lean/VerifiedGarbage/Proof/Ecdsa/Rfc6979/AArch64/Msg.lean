import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Blocks

/-!
# Deterministic ECDSA on AArch64: the messages of steps d, f and h.3

`V ‖ b`, and `‖ d ‖ h` if `full`, at `scratch + 2256`, for `V` of `D` bytes
(`msg_ok`): `V` copied from the frame (`head_ok`), the byte `b`, then the
private key and `h` copied (`tail_ok`), through `x12`, which points after `b`.
If two `V`s make a candidate (`msgW_ok`, P-521 with SHA-512): `‖ d ‖ 0 0 ‖
digest` instead, `d`'s 66 bytes through `x12` and its last eight through
`x13` and `x14` (`copyBytes`), a zero word, then the digest over all but its
first two bytes.
-/

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64

variable {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} {L : Lay dn E} {g : Reg → BitVec 64} {m₀ : Mem}

/-- `8 K` bytes copied to `scratch + e + d` by `copyN`, with `Ctx` kept. -/
theorem copy_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {src : Reg} {S : Addr} (hs : u.gpr src = S)
    (hsr : src ≠ .x11) {dst : Reg} (hdr : dst ≠ .x11) {e : Nat} (hdi : u.gpr dst = L.scr + BitVec.ofNat 64 e)
    {so d K : Nat} (hd : e + d + 8 * K ≤ 8192) (hso : so % 8 = 0 ∧ so + 8 * K ≤ 32768)
    (hdo : d % 8 = 0 ∧ d + 8 * K ≤ 32768)
    (hr : ∀ j < K, InRegions (u.rd ++ u.wr) (S + BitVec.ofNat 64 (so + 8 * j)) 8)
    (hsep : Region.Disjoint ⟨S + BitVec.ofNat 64 so, 8 * K⟩ ⟨L.scr + BitVec.ofNat 64 (e + d), 8 * K⟩) :
    WP isa (.block (Cfg.copyN K src so dst d)) u fun u' => Ctx L g m₀ u' ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧
      (∀ r, r ≠ .x11 → u'.gpr r = u.gpr r) ∧ Frame [⟨L.scr + BitVec.ofNat 64 (e + d), 8 * K⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.scr + BitVec.ofNat 64 (e + d)) (8 * K) =
        Spec.Sha256.bytesAt u.mem (S + BitVec.ofNat 64 so) (8 * K) := by
  have hsep' := hsep
  rw [← Offset.add_add] at hsep'
  refine WP.mono_syms (copyN_ok (K := K) hdr hsr hsep' (by omega) hso hdo K (Nat.le_refl _) u hs hdi hr
    fun j hj => by rw [Offset.add_add]; exact hc.inScrW (by omega))
    fun u' ⟨hrd, hwr, hsp, hg, hf, hb⟩ hsy => ?_
  rw [Offset.add_add] at hf hb
  exact ⟨hc.keep hL hrd hwr hsp (fun r hr _ => hg r (ne_cs hr (by decide))) hf (hsy := hsy)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L hd),
    hrd, hwr, hg, hf, hb⟩

/-- The pointers: `scratch` in `x9`, `d` in `x10`, the frame in `x15`, and,
if `wide`, `digest` in `x8`. -/
theorem ptrs_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (wide : Bool) :
    WP isa (.block (Cfg.msgPtrs wide)) t fun u => Ctx L g m₀ u ∧ u.mem = t.mem ∧ u.gpr .x9 = L.scr ∧
      u.gpr .x10 = L.d ∧ u.gpr .x15 = L.B + BitVec.ofNat 64 16 ∧ (wide = true → u.gpr .x8 = L.dg) := by
  have h200 := hc.inFr (d := 200) (by omega) (by omega)
  have h208 := hc.inFr (d := 208) (by omega) (by omega)
  have h216 := hc.inFr (d := 216) (by omega) (by omega)
  apply WP.of_runBlock
  cases wide
  · simp only [Cfg.msgPtrs, fScratch, fD, Bool.false_eq_true, ite_false, List.append_nil, runBlock_cons,
      runStep_some, runBlock_nil, exec, Nat.reduceMod,
      Nat.reduceLT, and_self, ite_true, State.load, RegUpd.gpr_write, RegUpd.sp_write, RegUpd.rd_write,
      RegUpd.wr_write, RegUpd.mem_write, reduceCtorEq, ite_false, hc.sp, Offset.add_add, Nat.reduceAdd, h200,
      h216, Option.map_some, read8, hc.pScr, hc.pD, BitVec.setWidth_eq, show (0 : Nat) < 4096 by decide,
      BitVec.add_zero, Option.some.injEq, exists_eq_left']
    refine ⟨hc.regs hL rfl rfl rfl rfl (fun r hr h30 => ?_) rfl, trivial, trivial, trivial, trivial, fun h => nomatch h⟩
    have h₁ : r ∉ [Reg.x9, .x10, .x15] := not_pres hr _ (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h₁
    simp only [RegUpd.gpr_write, h₁.1, h₁.2.1, h₁.2.2, ite_false]
  · simp only [Cfg.msgPtrs, fScratch, fD, fDigest, ite_true, List.cons_append, List.nil_append, runBlock_cons,
      runStep_some, runBlock_nil, exec, Nat.reduceMod,
      Nat.reduceLT, and_self, ite_true, State.load, RegUpd.gpr_write, RegUpd.sp_write, RegUpd.rd_write,
      RegUpd.wr_write, RegUpd.mem_write, reduceCtorEq, ite_false, hc.sp, Offset.add_add, Nat.reduceAdd, h200,
      h208, h216, Option.map_some, read8, hc.pScr, hc.pD, hc.pDg, BitVec.setWidth_eq,
      show (0 : Nat) < 4096 by decide, BitVec.add_zero, Option.some.injEq, exists_eq_left']
    refine ⟨hc.regs hL rfl rfl rfl rfl (fun r hr h30 => ?_) rfl, trivial, trivial, trivial, trivial, fun _ => trivial⟩
    have h₁ : r ∉ [Reg.x8, .x9, .x10, .x15] := not_pres hr _ (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h₁
    simp only [RegUpd.gpr_write, h₁.1, h₁.2.1, h₁.2.2.1, h₁.2.2.2, ite_false]

theorem byte_self (m : Mem) (a : Addr) (v : BitVec (8 * 1)) : m.write a 1 v a = v := by
  simp only [Mem.write, BitVec.sub_self, BitVec.toNat_zero, Nat.mul_zero, Nat.zero_lt_one, ite_true]
  exact BitVec.extractLsb'_eq_self

theorem movzb (b : Nat) :
    BitVec.setWidth 8 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 64 (BitVec.ofNat 16 b) <<< (16 * 0)))) =
      BitVec.ofNat 8 b := by
  apply BitVec.eq_of_toNat_eq
  simp only [Nat.mul_zero, BitVec.shiftLeft_zero, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- The byte `b` stored at `scratch + o`, through `x9`. -/
theorem strb_ok {u : State} (hc : Ctx L g m₀ u) (h9 : u.gpr .x9 = L.scr) {b o : Nat} (ho : o < 4096) :
    WP isa (.block [.movz .x .x11 (BitVec.ofNat 16 b) 0, .strb .x11 .x9 o]) u fun u' =>
      u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧ (∀ r, r ≠ .x11 → u'.gpr r = u.gpr r) ∧
      u'.mem = u.mem.write (L.scr + BitVec.ofNat 64 o) 1 (BitVec.ofNat 8 b) := by
  have w := hc.inScrW (o := o) (n := 1) (by omega)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show 16 * 0 < Size.x.bits by decide, ite_true,
    addr, Nat.mod_one, ho, and_self, Option.bind_some, State.store, State.read, Size.bits, RegUpd.gpr_write,
    RegUpd.wr_write, RegUpd.mem_write, reduceCtorEq, ite_false, h9, w, Option.some.injEq,
    exists_eq_left']
  refine ⟨by atriv, by atriv, by atriv, fun r hr => ?_, by rw [movzb]⟩
  simp only [hr, ite_false]

/-- `V ‖ b`, for `V` of `D` bytes, with `scratch` in `x9` and the frame in `x15`. -/
theorem head_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (h9 : t.gpr .x9 = L.scr)
    (h15 : t.gpr .x15 = L.B + BitVec.ofNat 64 16) (b : Nat) {D : Nat} (hD : D ≤ 64)
    (hD8 : D % 8 = 0) :
    WP isa (.block (Cfg.copyN (D / 8) .x15 fV .x9 sMsg ++
      ([.movz .x .x11 (BitVec.ofNat 16 b) 0, .strb .x11 .x9 (sMsg + D)] : List Instr))) t fun u =>
      Ctx L g m₀ u ∧ (∀ r, r ≠ .x11 → u.gpr r = t.gpr r) ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2256, D + 1⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 2256) (D + 1) =
        Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 80) D ++ [BitVec.ofNat 8 b] := by
  have e8 : 8 * (D / 8) = D := by omega
  simp only [fV, sMsg]
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok hL hc (S := L.B + BitVec.ofNat 64 16) (src := .x15) h15 (by decide) (dst := .x9)
    (by decide) (e := 0) (by rw [add_ofNat_zero]; exact h9) (so := 64) (d := 2256) (K := D / 8) (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    (fun j hj => by rw [Offset.add_add]; exact hc.inFr (by omega) (by omega))
    (by rw [Offset.add_add]; exact hL.stk_scr (by omega) (by omega))) fun u₂ ⟨hc₂, hrd₂, hwr₂, hg₂, hf₂, hb₂⟩ => ?_
  rw [e8, Nat.zero_add] at hf₂ hb₂
  have h9₂ : u₂.gpr .x9 = L.scr := (hg₂ _ (by decide)).trans h9
  refine WP.mono_syms (strb_ok hc₂ h9₂ (b := b) (o := 2256 + D) (by omega))
    fun u₃ ⟨hrd₃, hwr₃, hsp₃, hg₃, hm₃⟩ sy₃ => ?_
  have hf₃ : Frame [⟨L.scr + BitVec.ofNat 64 (2256 + D), 1⟩] u₂.mem u₃.mem := by
    rw [hm₃]; exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hc₂.keep hL hrd₃ hwr₃ hsp₃ (fun r hr _ => hg₃ r (ne_cs hr (by decide))) hf₃ (hsy := sy₃)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L (by omega)),
    fun r hr => (hg₃ r hr).trans (hg₂ r hr), ?_, ?_⟩
  · refine (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      (hf₃.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by omega) (by omega)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by omega) (by omega)
  · rw [Proof.Hmac.Common.bytesAt_add, Offset.add_add]
    have e₁ : Spec.Sha256.bytesAt u₃.mem (L.scr + BitVec.ofNat 64 2256) D =
        Spec.Sha256.bytesAt u₂.mem (L.scr + BitVec.ofNat 64 2256) D :=
      bytesAt_frame hf₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega)
    rw [e₁, hb₂, Offset.add_add]
    refine congrArg (fun y => Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 (16 + 64)) D ++ y) ?_
    show [u₃.mem (L.scr + BitVec.ofNat 64 (2256 + D) + BitVec.ofNat 64 0)] = _
    rw [add_ofNat_zero, hm₃, byte_self]

/-- `‖ d ‖ h`, `w` words each, after `D + 1` bytes, with `scratch` in `x9`,
`d` in `x10` and the frame in `x15`. -/
theorem tail_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (h9 : u.gpr .x9 = L.scr) (h10 : u.gpr .x10 = L.d)
    (h15 : u.gpr .x15 = L.B + BitVec.ofNat 64 16) {D : Nat} (hD : D ≤ 64) {w : Nat} (hw : w ≤ 6)
    (hq : 8 * w ≤ L.q) :
    WP isa (.block (.addImm .x .x12 .x9 (sMsg + D + 1) ::
      (Cfg.copyN w .x10 0 .x12 0 ++ Cfg.copyN w .x15 fH .x12 (8 * w)))) u
      fun u' => Ctx L g m₀ u' ∧ Frame [⟨L.scr + BitVec.ofNat 64 (2256 + D + 1), 16 * w⟩] u.mem u'.mem ∧
        Spec.Sha256.bytesAt u'.mem (L.scr + BitVec.ofNat 64 (2256 + D + 1)) (16 * w) =
          Spec.Sha256.bytesAt u.mem L.d (8 * w) ++
            Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 144) (8 * w) := by
  simp only [fH, sMsg]
  rw [← List.singleton_append, WP.block_append_iff]
  have h₁ : WP isa (.block [.addImm .x .x12 .x9 (2256 + D + 1)]) u
      (Upd L g m₀ u .x12 (L.scr + BitVec.ofNat 64 (2256 + D + 1))) := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show 2256 + D + 1 < 4096 by omega, ite_true,
      State.read, Size.bits, BitVec.setWidth_eq, h9, Option.some.injEq, exists_eq_left']
    exact ⟨hc.set hL (d := .x12) (by decide) rfl rfl rfl rfl (fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr) rfl, rfl,
      by rw [RegUpd.gpr_write_self]; exact BitVec.setWidth_eq _, fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr⟩
  refine WP.mono h₁ fun u₁ h₁ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok hL h₁.ctx (u := u₁) (src := .x10) (by rw [h₁.keep _ (by decide), h10]) (by decide)
    (dst := .x12) (by decide) (e := 2256 + D + 1) h₁.val (so := 0) (d := 0) (K := w) (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (fun j hj => h₁.ctx.inD (by omega) (by omega))
    (by rw [add_ofNat_zero, Nat.add_zero]
        exact (hL.dc.sub_left (Region.sub_prefix hq)).sub_right
          (Offset.sub_base (d := 2256 + D + 1) (n := 8 * w) _ (by omega))))
    fun u₂ ⟨hc₂, hrd₂, hwr₂, hg₂, hf₂, hb₂⟩ => ?_
  rw [Nat.add_zero] at hf₂ hb₂
  have h12₂ : u₂.gpr .x12 = L.scr + BitVec.ofNat 64 (2256 + D + 1) := (hg₂ _ (by decide)).trans h₁.val
  refine WP.mono (copy_ok hL hc₂ (S := L.B + BitVec.ofNat 64 16) (src := .x15)
    (by rw [hg₂ _ (by decide), h₁.keep _ (by decide), h15]) (by decide) (dst := .x12) (by decide)
    (e := 2256 + D + 1) h12₂ (so := 128) (d := 8 * w) (K := w) (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    (fun j hj => by rw [Offset.add_add]; exact hc₂.inFr (by omega) (by omega))
    (by rw [Offset.add_add]; exact hL.stk_scr (by omega) (by omega))) fun u₃ ⟨hc₃, _, _, _, hf₃, hb₃⟩ => ?_
  refine ⟨hc₃, ?_, ?_⟩
  · rw [h₁.mem] at hf₂
    refine (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      (hf₃.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by omega) (by omega)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by omega) (by omega)
  · rw [show 16 * w = 8 * w + 8 * w by omega, Proof.Hmac.Common.bytesAt_add _ _ (8 * w) (8 * w), Offset.add_add, hb₃,
      Offset.add_add, bytesAt_frame hf₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega), hb₂, add_ofNat_zero, h₁.mem]
    refine congrArg (fun y => Spec.Sha256.bytesAt u.mem L.d (8 * w) ++ y) ?_
    rw [← h₁.mem]
    exact bytesAt_frame hf₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hL.stk_scr (by omega) (by omega)) (by omega)

/-- The message `V ‖ b` (`‖ d ‖ h` if `full`, `w` words each) at
`scratch + 2256`, for `V` of `D` bytes. -/
theorem msg_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (h9 : t.gpr .x9 = L.scr) (h10 : t.gpr .x10 = L.d)
    (h15 : t.gpr .x15 = L.B + BitVec.ofNat 64 16) (b : Nat) (full : Bool) {D w : Nat} (Q : Nat) (hD : D ≤ 64)
    (hD8 : D % 8 = 0) (hwq : full = true → w ≤ 6 ∧ 8 * w ≤ L.q) :
    WP isa (.block (Cfg.msg w Q D b full false)) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2256, D + 16 * w + 1⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.scr + BitVec.ofNat 64 2256) (if full then D + 16 * w + 1 else D + 1) =
        Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 80) D ++ [BitVec.ofNat 8 b] ++
          (if full then Spec.Sha256.bytesAt t.mem L.d (8 * w) ++
            Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 144) (8 * w)
          else []) := by
  cases full
  · simp only [Cfg.msg, Bool.false_eq_true, ite_false, List.append_nil]
    refine WP.mono (head_ok hL hc h9 h15 b hD hD8) fun u ⟨hcu, _, hf, hb⟩ =>
      ⟨hcu, hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩, hb⟩
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.sub _ (by omega) (by omega)
  · obtain ⟨hw, hq⟩ := hwq rfl
    simp only [Cfg.msg, ite_true, Bool.false_eq_true, ite_false]
    rw [WP.block_append_iff]
    refine WP.mono (head_ok hL hc h9 h15 b hD hD8) fun u ⟨hcu, hg, hf, hb⟩ =>
      WP.mono (tail_ok hL hcu ((hg _ (by decide)).trans h9) ((hg _ (by decide)).trans h10)
        ((hg _ (by decide)).trans h15) hD hw hq)
      fun u' ⟨hcu', hf', hb'⟩ => ⟨hcu', ?_, ?_⟩
    · refine (hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
        (hf'.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
      · simp only [List.mem_singleton] at hr; subst hr
        exact Offset.sub _ (by omega) (by omega)
      · simp only [List.mem_singleton] at hr; subst hr
        exact Offset.sub _ (by omega) (by omega)
    · rw [show D + 16 * w + 1 = (D + 1) + 16 * w by omega, Proof.Hmac.Common.bytesAt_add _ _ (D + 1) (16 * w),
        Offset.add_add,
        show 2256 + (D + 1) = 2256 + D + 1 by omega, hb',
        bytesAt_frame hf' (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega), hb]
      refine congrArg (fun y => Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 80) D ++ [BitVec.ofNat 8 b] ++ y) ?_
      rw [bytesAt_frame hf (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hL.dc.sub_left (Region.sub_prefix hq)).sub_right
            (Offset.sub_base (d := 2256) (n := D + 1) _ (by omega))) (by omega),
        bytesAt_frame hf (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact hL.stk_scr (by omega) (by omega)) (by omega)]

/-! ## The message of steps d and f, when two `V`s make a candidate -/

/-- The bytes of a zero word. -/
theorem bytesAt_writeW_zero64 (m : Mem) (p : Addr) {k : Nat} (hk : k ≤ 8) :
    Spec.Sha256.bytesAt (m.writeW p (0 : BitVec 64)) p k = List.replicate k 0 := by
  rw [List.eq_replicate_iff]
  refine ⟨by simp [Spec.Sha256.bytesAt], fun b hb => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
  have hi := List.mem_range.mp hi
  have e : (p + BitVec.ofNat 64 i - p).toNat = i := by
    rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp only [Mem.writeW, Mem.write, e, show i < 64 / 8 by omega, ite_true]
  apply BitVec.eq_of_toNat_eq; simp

/-- `d ← src + k`. -/
theorem addImm_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {d src : Reg} (hd : d ∉ preserved) {S : Addr}
    (hs : u.gpr src = S) {k : Nat} (hk : k < 4096) :
    WP isa (.block [.addImm .x d src k]) u (Upd L g m₀ u d (S + BitVec.ofNat 64 k)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, hk, ite_true, State.read, Size.bits,
    BitVec.setWidth_eq, hs, Option.some.injEq, exists_eq_left']
  exact ⟨hc.set hL hd rfl rfl rfl rfl (fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr) rfl, rfl,
    by rw [RegUpd.gpr_write_self]; exact BitVec.setWidth_eq _, fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr⟩

/-- A word stored at `dst + d`. -/
theorem strW_ok {u : State} {t dst : Reg} {D : Addr} (hd : u.gpr dst = D) {d : Nat}
    (hdo : d % 8 = 0 ∧ d < 32768) (hw : InRegions u.wr (D + BitVec.ofNat 64 d) 8) :
    WP isa (.block [.str .x t dst d]) u fun u' => u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧
      u'.gpr = u.gpr ∧ u'.syms = u.syms ∧ u'.mem = u.mem.writeW (D + BitVec.ofNat 64 d) (u.gpr t) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes, hdo, and_self, ite_true,
    Option.bind_some, State.store, State.read, Size.bits, BitVec.setWidth_eq, hd, hw, write8,
    Option.some.injEq, exists_eq_left']

/-- A word copied from `S + so` to `scratch + e`, with `Ctx` kept. -/
theorem copyScr_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {src dst : Reg} {S : Addr} {e : Nat}
    (hs : u.gpr src = S)
    (hdi : u.gpr dst = L.scr + BitVec.ofNat 64 e) (hdr : dst ≠ .x11) (he : e + 8 ≤ 8192)
    (hr : InRegions (u.rd ++ u.wr) S 8) :
    WP isa (.block [.ldr .x .x11 src 0, .str .x .x11 dst 0]) u fun u' => Ctx L g m₀ u' ∧
      (∀ r, r ≠ .x11 → u'.gpr r = u.gpr r) ∧ Frame [⟨L.scr + BitVec.ofNat 64 e, 8⟩] u.mem u'.mem ∧
      u'.mem = u.mem.writeW (L.scr + BitVec.ofNat 64 e) (u.mem.readW S 64) := by
  refine WP.mono_syms (copyW_ok (so := 0) (d := 0) hs hdi ⟨rfl, by decide⟩ ⟨rfl, by decide⟩
    (by rw [add_ofNat_zero]; exact hr) (by rw [add_ofNat_zero]; exact hc.inScrW he) hdr)
    fun u' ⟨hrd, hwr, hsp, hg, hm⟩ hsy => ?_
  rw [add_ofNat_zero, add_ofNat_zero] at hm
  have hf : Frame [⟨L.scr + BitVec.ofNat 64 e, 8⟩] u.mem u'.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  exact ⟨hc.keep hL hrd hwr hsp (fun r hr _ => hg r (ne_cs hr (by decide))) hf (hsy := hsy)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L he), hg, hf, hm⟩

/-- A zero word at `scratch + o`, through `x13`. -/
theorem zeroScr_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {o : Nat}
    (h13 : u.gpr .x13 = L.scr + BitVec.ofNat 64 o) (ho : o + 8 ≤ 8192) :
    WP isa (.block [.movz .x .x11 0 0, .str .x .x11 .x13 0]) u fun u' => Ctx L g m₀ u' ∧
      (∀ r, r ≠ .x11 → u'.gpr r = u.gpr r) ∧ Frame [⟨L.scr + BitVec.ofNat 64 o, 8⟩] u.mem u'.mem ∧
      ∀ k ≤ 8, Spec.Sha256.bytesAt u'.mem (L.scr + BitVec.ofNat 64 o) k = List.replicate k 0 := by
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movz_ok hL hc (d := .x11) (by decide) (n := 0) (by decide)) fun u₁ h₁ => ?_
  refine WP.mono_syms (strW_ok (t := .x11) (dst := .x13) (D := L.scr + BitVec.ofNat 64 o) (d := 0) (by rw [h₁.keep _ (by decide), h13])
    ⟨rfl, by decide⟩ (by rw [add_ofNat_zero]; exact h₁.ctx.inScrW ho)) fun u₂ ⟨hrd, hwr, hsp, hg, _, hm⟩ hsy => ?_
  rw [add_ofNat_zero, h₁.val] at hm
  have hf : Frame [⟨L.scr + BitVec.ofNat 64 o, 8⟩] u₁.mem u₂.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨h₁.ctx.keep hL hrd hwr hsp (fun r _ _ => by rw [hg]) hf (hsy := hsy)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L ho),
    fun r hr => by rw [hg, h₁.keep _ hr], h₁.mem ▸ hf, fun k hk => by
      rw [hm]; exact bytesAt_writeW_zero64 _ _ hk⟩

/-- `‖ d ‖ 0 0 ‖ digest` after `V ‖ b`, for `d` of 66 bytes and a digest of
64, with `scratch` in `x9`, `d` in `x10` and `digest` in `x8`. -/
theorem tailW_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (h9 : u.gpr .x9 = L.scr) (h10 : u.gpr .x10 = L.d)
    (h8 : u.gpr .x8 = L.dg) (hq : 66 ≤ L.q) (hdn : 64 ≤ dn) :
    WP isa (.block (.addImm .x .x12 .x9 (sMsg + 64 + 1) ::
      (Cfg.copyBytes 66 .x10 .x12 ++
        ([.addImm .x .x13 .x9 (sMsg + 64 + 1 + 66), .movz .x .x11 0 0, .str .x .x11 .x13 0,
          .addImm .x .x14 .x9 (sMsg + 1 + 2 * 66)] : List Instr) ++ Cfg.copyN (64 / 8) .x8 0 .x14 0))) u
      fun u' => Ctx L g m₀ u' ∧ Frame [⟨L.scr + BitVec.ofNat 64 2321, 132⟩] u.mem u'.mem ∧
        Spec.Sha256.bytesAt u'.mem (L.scr + BitVec.ofNat 64 2321) 132 =
          Spec.Sha256.bytesAt u.mem L.d 66 ++ List.replicate 2 0 ++ Spec.Sha256.bytesAt u.mem L.dg 64 := by
  have nd := hL.nd
  have ng := hL.ng
  have nc := hL.nc
  simp only [Cfg.copyBytes, sMsg, Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub,
    show ¬ (2 = 0) from by decide, ite_false, List.append_assoc, List.cons_append, List.nil_append]
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (addImm_ok hL hc (d := .x12) (src := .x9) (by decide) h9 (k := 2321) (by decide)) fun u₁ h₁ => ?_
  rw [WP.block_append_iff]
  -- `d`'s first 64 bytes.
  refine WP.mono (copy_ok hL h₁.ctx (u := u₁) (src := .x10) (by rw [h₁.keep _ (by decide), h10]) (by decide)
    (dst := .x12) (by decide) (e := 2321) h₁.val (so := 0) (d := 0) (K := 8) (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (fun j hj => h₁.ctx.inD (by omega) (by omega))
    (by rw [add_ofNat_zero, Nat.add_zero]
        exact (hL.dc.sub_left (Region.sub_prefix (by omega))).sub_right (Offset.sub_base _ (by omega))))
    fun u₂ ⟨hc₂, _, _, hg₂, hf₂, hb₂⟩ => ?_
  rw [Nat.add_zero] at hf₂ hb₂
  rw [add_ofNat_zero, h₁.mem] at hb₂
  rw [h₁.mem] at hf₂
  -- Its last eight, through `x13` and `x14`.
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (addImm_ok hL hc₂ (d := .x13) (src := .x10) (by decide)
    (by rw [hg₂ _ (by decide), h₁.keep _ (by decide), h10]) (k := 58) (by decide)) fun u₃ h₃ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (addImm_ok hL h₃.ctx (d := .x14) (src := .x12) (by decide)
    (by rw [h₃.keep _ (by decide), hg₂ _ (by decide), h₁.val]) (k := 58) (by decide)) fun u₄ h₄ => ?_
  rw [Offset.add_add] at h₄
  rw [show ∀ (a b : Instr) (l : List Instr), a :: b :: l = [a, b] ++ l from fun _ _ _ => rfl,
    WP.block_append_iff]
  refine WP.mono (copyScr_ok hL h₄.ctx (src := .x13) (dst := .x14) (e := 2379)
    (by rw [h₄.keep _ (by decide), h₃.val]) h₄.val (by decide) (by omega)
    (h₄.ctx.inD (o := 58) (n := 8) (by omega) (by omega))) fun u₅ ⟨hc₅, hg₅, hf₅, hm₅⟩ => ?_
  -- The zero word.
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (addImm_ok hL hc₅ (d := .x13) (src := .x9) (by decide)
    (by rw [hg₅ _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), hg₂ _ (by decide),
      h₁.keep _ (by decide), h9]) (k := 2387) (by decide)) fun u₆ h₆ => ?_
  rw [show ∀ (a b : Instr) (l : List Instr), a :: b :: l = [a, b] ++ l from fun _ _ _ => rfl,
    WP.block_append_iff]
  refine WP.mono (zeroScr_ok hL h₆.ctx h₆.val (by omega)) fun u₇ ⟨hc₇, hg₇, hf₇, hz₇⟩ => ?_
  -- The digest.
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (addImm_ok hL hc₇ (d := .x14) (src := .x9) (by decide)
    (by rw [hg₇ _ (by decide), h₆.keep _ (by decide), hg₅ _ (by decide), h₄.keep _ (by decide),
      h₃.keep _ (by decide), hg₂ _ (by decide), h₁.keep _ (by decide), h9]) (k := 2389) (by decide)) fun u₈ h₈ => ?_
  have h8' : u₈.gpr .x8 = L.dg := by
    rw [h₈.keep _ (by decide), hg₇ _ (by decide), h₆.keep _ (by decide), hg₅ _ (by decide),
      h₄.keep _ (by decide), h₃.keep _ (by decide), hg₂ _ (by decide), h₁.keep _ (by decide), h8]
  refine WP.mono (copy_ok hL h₈.ctx (u := u₈) (src := .x8) h8' (by decide)
    (dst := .x14) (by decide) (e := 2389) h₈.val (so := 0) (d := 0) (K := 8) (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (fun j hj => h₈.ctx.inDg (by omega) (by omega))
    (by rw [add_ofNat_zero, Nat.add_zero]
        exact (hL.gc.sub_left (Region.sub_prefix (by omega))).sub_right (Offset.sub_base _ (by omega))))
    fun u₉ ⟨hc₉, _, _, _, hf₉, hb₉⟩ => ?_
  rw [Nat.add_zero] at hf₉ hb₉
  rw [add_ofNat_zero] at hb₉
  -- The frames, from one state to the next.
  have f₅ := hf₅
  rw [h₄.mem, h₃.mem] at f₅
  have f₇ := hf₇
  rw [h₆.mem] at f₇
  have f₉ := hf₉
  rw [h₈.mem] at f₉
  rw [h₄.mem, h₃.mem] at hm₅
  -- `d` and the digest, unchanged before their copies.
  have sd : ∀ {m m' : Mem} {e n : Nat}, Frame [⟨L.scr + BitVec.ofNat 64 e, n⟩] m m' → e + n ≤ 8192 →
      ∀ {p : Addr} {k : Nat}, Region.Disjoint ⟨p, k⟩ L.SCR → k ≤ 2 ^ 64 →
      Spec.Sha256.bytesAt m' p k = Spec.Sha256.bytesAt m p k := fun hf he _ _ hd hk =>
    bytesAt_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hd.sub_right (Offset.sub_base _ he)) hk
  have dG : Region.Disjoint ⟨L.dg, 64⟩ L.SCR := hL.gc.sub_left (Region.sub_prefix (by omega))
  have kp : ∀ {m m' : Mem} {e n o k : Nat}, Frame [⟨L.scr + BitVec.ofNat 64 e, n⟩] m m' →
      (o + k ≤ e ∨ e + n ≤ o) → e + n ≤ 8192 → o + k ≤ 8192 →
      Spec.Sha256.bytesAt m' (L.scr + BitVec.ofNat 64 o) k = Spec.Sha256.bytesAt m (L.scr + BitVec.ofNat 64 o) k :=
    fun hf h he ho => bytesAt_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ h (by omega) (by omega)) (by omega)
  refine ⟨hc₉, ?_, ?_⟩
  · have c : ∀ {e n : Nat}, 2321 ≤ e → e + n ≤ 2453 →
        Region.Sub ⟨L.scr + BitVec.ofNat 64 e, n⟩ ⟨L.scr + BitVec.ofNat 64 2321, 132⟩ := fun h₁ h₂ =>
      Offset.sub _ h₁ h₂
    refine (((hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      (f₅.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)).trans
      (f₇.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)).trans
      (f₉.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩) <;>
    · simp only [List.mem_singleton] at hr; subst hr; exact c (by omega) (by omega)
  · -- 132 = 58 + 8 + 2 + 64.
    rw [show (132 : Nat) = 58 + (8 + (2 + 64)) from rfl, Proof.Hmac.Common.bytesAt_add,
      Proof.Hmac.Common.bytesAt_add, Proof.Hmac.Common.bytesAt_add, Offset.add_add, Offset.add_add, Offset.add_add]
    simp only [Nat.reduceAdd]
    rw [hb₉, h₈.mem, show 8 * 8 = 64 from rfl, sd f₇ (by omega) dG (by omega), sd f₅ (by omega) dG (by omega), sd hf₂ (by omega) dG (by omega),
      kp f₉ (o := 2387) (k := 2) (by omega) (by omega) (by omega), hz₇ 2 (by omega),
      kp f₉ (o := 2379) (k := 8) (by omega) (by omega) (by omega),
      kp f₇ (o := 2379) (k := 8) (by omega) (by omega) (by omega), hm₅, bytesAt_copied,
      kp f₉ (o := 2321) (k := 58) (by omega) (by omega) (by omega),
      kp f₇ (o := 2321) (k := 58) (by omega) (by omega) (by omega),
      kp f₅ (o := 2321) (k := 58) (by omega) (by omega) (by omega),
      bytesAt_take _ _ (show 58 ≤ 64 by omega), hb₂, ← bytesAt_take _ _ (show 58 ≤ 64 by omega),
      sd hf₂ (by omega) (p := L.d + BitVec.ofNat 64 58) (k := 8) (hL.dc.sub_left (Offset.sub_base _ (by omega)))
        (by omega),
      show (66 : Nat) = 58 + 8 from rfl, Proof.Hmac.Common.bytesAt_add]
    simp only [List.append_assoc]

/-- The message `V ‖ b ‖ d ‖ 0 0 ‖ digest` at `scratch + 2256`, for `V` of 64
bytes, `d` of 66 and a digest of 64 (P-521 with SHA-512). -/
theorem msgW_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (h9 : t.gpr .x9 = L.scr) (h10 : t.gpr .x10 = L.d)
    (h15 : t.gpr .x15 = L.B + BitVec.ofNat 64 16) (h8 : t.gpr .x8 = L.dg) (b : Nat) {w : Nat} (hq : 66 ≤ L.q)
    (hdn : 64 ≤ dn) :
    WP isa (.block (Cfg.msg w 66 64 b true true)) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2256, 64 + 2 * 66 + 1⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.scr + BitVec.ofNat 64 2256) (64 + 2 * 66 + 1) =
        Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 80) 64 ++ [BitVec.ofNat 8 b] ++
          (Spec.Sha256.bytesAt t.mem L.d 66 ++ List.replicate 2 0 ++ Spec.Sha256.bytesAt t.mem L.dg 64) := by
  simp only [Cfg.msg, ite_true]
  rw [WP.block_append_iff]
  refine WP.mono (head_ok hL hc h9 h15 b (D := 64) (by omega) (by omega)) fun u ⟨hcu, hg, hf, hb⟩ =>
    WP.mono (tailW_ok hL hcu ((hg _ (by decide)).trans h9) ((hg _ (by decide)).trans h10)
      ((hg _ (by decide)).trans h8) hq hdn) fun u' ⟨hcu', hf', hb'⟩ => ⟨hcu', ?_, ?_⟩
  · refine (hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      (hf'.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by omega) (by omega)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by omega) (by omega)
  · have nc := hL.nc
    rw [show 64 + 2 * 66 + 1 = 65 + 132 from rfl, Proof.Hmac.Common.bytesAt_add, Offset.add_add, hb',
      bytesAt_frame hf' (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega), hb]
    have hd : ∀ {p : Addr} {k : Nat}, Region.Disjoint ⟨p, k⟩ L.SCR → k ≤ 2 ^ 64 →
        Spec.Sha256.bytesAt u.mem p k = Spec.Sha256.bytesAt t.mem p k := fun h hk =>
      bytesAt_frame hf (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact h.sub_right (Offset.sub_base _ (by omega))) hk
    rw [hd (hL.dc.sub_left (Region.sub_prefix (by omega))) (by omega),
      hd (hL.gc.sub_left (Region.sub_prefix (by omega))) (by omega)]

end VG.Proof.Ecdsa.Rfc6979.AArch64
