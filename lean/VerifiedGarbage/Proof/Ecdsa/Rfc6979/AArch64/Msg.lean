import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Blocks

/-!
# Deterministic ECDSA on AArch64: the messages of steps d, f and h.3

`V ‖ b`, and `‖ d ‖ h` if `full`, at `scratch + 2256`, for `V` of `D` bytes
(`msg_ok`): `V` copied from the frame (`head_ok`), the byte `b`, then the
private key and `h` copied (`tail_ok`), through `x12`, which points after `b`.
-/

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64

variable {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {m₀ : Mem}

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

/-- The pointers: `scratch` in `x9`, `d` in `x10`, the frame in `x15`. -/
theorem ptrs_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.msgPtrs) t fun u => Ctx L g m₀ u ∧ u.mem = t.mem ∧ u.gpr .x9 = L.scr ∧
      u.gpr .x10 = L.d ∧ u.gpr .x15 = L.B + BitVec.ofNat 64 16 := by
  have h184 := hc.inFr (d := 184) (by omega) (by omega)
  have h200 := hc.inFr (d := 200) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [Cfg.msgPtrs, fScratch, fD, runBlock_cons, runStep_some, runBlock_nil, exec, Nat.reduceMod,
    Nat.reduceLT, and_self, ite_true, State.load, RegUpd.gpr_write, RegUpd.sp_write, RegUpd.rd_write,
    RegUpd.wr_write, RegUpd.mem_write, reduceCtorEq, ite_false, hc.sp, Offset.add_add, Nat.reduceAdd, h184,
    h200, Option.map_some, read8, hc.pScr, hc.pD, BitVec.setWidth_eq, show (0 : Nat) < 4096 by decide,
    BitVec.add_zero, Option.some.injEq, exists_eq_left']
  refine ⟨hc.regs hL rfl rfl rfl rfl (fun r hr h30 => ?_) rfl, trivial⟩
  have h₁ : r ∉ [Reg.x9, .x10, .x15] := not_pres hr _ (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h₁
  simp only [RegUpd.gpr_write, h₁.1, h₁.2.1, h₁.2.2, ite_false]

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

/-- `‖ d ‖ h`, after `D + 1` bytes, with `scratch` in `x9`, `d` in `x10` and the frame in `x15`. -/
theorem tail_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (h9 : u.gpr .x9 = L.scr) (h10 : u.gpr .x10 = L.d)
    (h15 : u.gpr .x15 = L.B + BitVec.ofNat 64 16) {D : Nat} (hD : D ≤ 64) :
    WP isa (.block (.addImm .x .x12 .x9 (sMsg + D + 1) ::
      (Cfg.copyN 4 .x10 0 .x12 0 ++ Cfg.copyN 4 .x15 fH .x12 32))) u
      fun u' => Ctx L g m₀ u' ∧ Frame [⟨L.scr + BitVec.ofNat 64 (2256 + D + 1), 64⟩] u.mem u'.mem ∧
        Spec.Sha256.bytesAt u'.mem (L.scr + BitVec.ofNat 64 (2256 + D + 1)) 64 =
          Spec.Sha256.bytesAt u.mem L.d 32 ++ Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 144) 32 := by
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
    (dst := .x12) (by decide) (e := 2256 + D + 1) h₁.val (so := 0) (d := 0) (K := 4) (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (fun j hj => h₁.ctx.inD (by omega))
    (by rw [add_ofNat_zero, Nat.add_zero]; exact hL.dc.sub_right (Offset.sub_base _ (by omega))))
    fun u₂ ⟨hc₂, hrd₂, hwr₂, hg₂, hf₂, hb₂⟩ => ?_
  rw [Nat.add_zero] at hf₂ hb₂
  have h12₂ : u₂.gpr .x12 = L.scr + BitVec.ofNat 64 (2256 + D + 1) := (hg₂ _ (by decide)).trans h₁.val
  refine WP.mono (copy_ok hL hc₂ (S := L.B + BitVec.ofNat 64 16) (src := .x15)
    (by rw [hg₂ _ (by decide), h₁.keep _ (by decide), h15]) (by decide) (dst := .x12) (by decide)
    (e := 2256 + D + 1) h12₂ (so := 128) (d := 32) (K := 4) (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
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
  · rw [Proof.Hmac.Common.bytesAt_add _ _ 32 32, Offset.add_add, show (32 : Nat) = 8 * 4 from rfl, hb₃,
      Offset.add_add, bytesAt_frame hf₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega), hb₂, add_ofNat_zero, h₁.mem]
    refine congrArg (fun y => Spec.Sha256.bytesAt u.mem L.d (8 * 4) ++ y) ?_
    rw [← h₁.mem]
    exact bytesAt_frame hf₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hL.stk_scr (by omega) (by omega)) (by omega)

/-- The message `V ‖ b` (`‖ d ‖ h` if `full`) at `scratch + 2256`, for `V` of `D` bytes. -/
theorem msg_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (h9 : t.gpr .x9 = L.scr) (h10 : t.gpr .x10 = L.d)
    (h15 : t.gpr .x15 = L.B + BitVec.ofNat 64 16) (b : Nat) (full : Bool) {D : Nat} (hD : D ≤ 64)
    (hD8 : D % 8 = 0) :
    WP isa (.block (Cfg.msg D b full)) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2256, D + 65⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.scr + BitVec.ofNat 64 2256) (if full then D + 65 else D + 1) =
        Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 80) D ++ [BitVec.ofNat 8 b] ++
          (if full then Spec.Sha256.bytesAt t.mem L.d 32 ++ Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 144) 32
          else []) := by
  cases full
  · simp only [Cfg.msg, Bool.false_eq_true, ite_false, List.append_nil]
    refine WP.mono (head_ok hL hc h9 h15 b hD hD8) fun u ⟨hcu, _, hf, hb⟩ =>
      ⟨hcu, hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩, hb⟩
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.sub _ (by omega) (by omega)
  · simp only [Cfg.msg, ite_true]
    rw [WP.block_append_iff]
    refine WP.mono (head_ok hL hc h9 h15 b hD hD8) fun u ⟨hcu, hg, hf, hb⟩ =>
      WP.mono (tail_ok hL hcu ((hg _ (by decide)).trans h9) ((hg _ (by decide)).trans h10)
        ((hg _ (by decide)).trans h15) hD)
      fun u' ⟨hcu', hf', hb'⟩ => ⟨hcu', ?_, ?_⟩
    · refine (hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
        (hf'.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
      · simp only [List.mem_singleton] at hr; subst hr
        exact Offset.sub _ (by omega) (by omega)
      · simp only [List.mem_singleton] at hr; subst hr
        exact Offset.sub _ (by omega) (by omega)
    · rw [show D + 65 = (D + 1) + 64 by omega, Proof.Hmac.Common.bytesAt_add _ _ (D + 1) 64, Offset.add_add,
        show 2256 + (D + 1) = 2256 + D + 1 by omega, hb',
        bytesAt_frame hf' (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega), hb]
      refine congrArg (fun y => Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 80) D ++ [BitVec.ofNat 8 b] ++ y) ?_
      rw [bytesAt_frame hf (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact hL.dc.sub_right (Offset.sub_base _ (by omega))) (by omega),
        bytesAt_frame hf (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact hL.stk_scr (by omega) (by omega)) (by omega)]

end VG.Proof.Ecdsa.Rfc6979.AArch64
