module
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Regs
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Hash

import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Copy
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Syms

/-!
# Deterministic ECDSA on AArch64: the messages of steps d, f and h.3

The byte `b`, and `‖ d ‖ h` if `full`, at `scratch + 2256` (`msg_ok`), as on
x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Msg.lean`): the byte (`strb_ok`), then
the private key and `h`, `Q` bytes each, copied (`tail_ok`) through `x12`,
which points after `b`, by `copyBytes` (`copyB_ok`). HMAC's text is `V` (`D`
bytes, from the frame, the table's `update` with it), then this message.
-/

@[expose] public section

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
  refine WP.mono_syms (copyN_ok (K := K) hdr hsr hsep' (by omega_arith) hso hdo K (Nat.le_refl _) u hs hdi hr
    fun j hj => by rw [Offset.add_add]; exact hc.inScrW (by omega_arith))
    fun u' ⟨hrd, hwr, hsp, hg, hf, hb⟩ hsy => ?_
  rw [Offset.add_add] at hf hb
  exact ⟨hc.keep hL hrd hwr hsp (fun r hr _ => hg r (ne_cs hr (by decide))) hf (hsy := hsy)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L hd),
    hrd, hwr, hg, hf, hb⟩

/-- The pointers: `scratch` in `x9`, `d` in `x10` and the frame in `x15`. -/
theorem ptrs_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.msgPtrs) t fun u => Ctx L g m₀ u ∧ u.mem = t.mem ∧ u.gpr .x9 = L.scr ∧
      u.gpr .x10 = L.d ∧ u.gpr .x15 = L.B + BitVec.ofNat 64 16 := by
  have h200 := hc.inFr (d := 200) (by omega_arith) (by omega_arith)
  have h216 := hc.inFr (d := 216) (by omega_arith) (by omega_arith)
  apply WP.of_runBlock
  simp only [Cfg.msgPtrs, fScratch, fD, runBlock_cons, runStep_some, runBlock_nil, exec, Nat.reduceMod,
    Nat.reduceLT, and_self, ite_true, State.load, RegUpd.gpr_write, RegUpd.sp_write, RegUpd.rd_write,
    RegUpd.wr_write, RegUpd.mem_write, reduceCtorEq, ite_false, hc.sp, Offset.add_add, Nat.reduceAdd, h200,
    h216, Option.map_some, read8, hc.pScr, hc.pD, BitVec.setWidth_eq, show (0 : Nat) < 4096 by decide,
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
  omega_arith

/-- The byte `b` stored at `scratch + o`, through `x9`. -/
theorem strb_ok {u : State} (hc : Ctx L g m₀ u) (h9 : u.gpr .x9 = L.scr) {b o : Nat} (ho : o < 4096) :
    WP isa (.block [.movz .x .x11 (BitVec.ofNat 16 b) 0, .strb .x11 .x9 o]) u fun u' =>
      u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧ (∀ r, r ≠ .x11 → u'.gpr r = u.gpr r) ∧
      u'.mem = u.mem.write (L.scr + BitVec.ofNat 64 o) 1 (BitVec.ofNat 8 b) := by
  have w := hc.inScrW (o := o) (n := 1) (by omega_arith)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show 16 * 0 < Size.x.bits by decide, ite_true,
    addr, Nat.mod_one, ho, and_self, Option.bind_some, State.store, State.read, Size.bits, RegUpd.gpr_write,
    RegUpd.wr_write, RegUpd.mem_write, reduceCtorEq, ite_false, h9, w, Option.some.injEq,
    exists_eq_left']
  refine ⟨by atriv, by atriv, by atriv, fun r hr => ?_, by rw [movzb]⟩
  simp only [hr, ite_false]

/-- The bytes of a zero word. -/
theorem bytesAt_writeW_zero64 (m : Mem) (p : Addr) {k : Nat} (hk : k ≤ 8) :
    Spec.Sha256.bytesAt (m.writeW p (0 : BitVec 64)) p k = List.replicate k 0 := by
  rw [List.eq_replicate_iff]
  refine ⟨by simp [Spec.Sha256.bytesAt], fun b hb => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
  have hi := List.mem_range.mp hi
  have e : (p + BitVec.ofNat 64 i - p).toNat = i := by
    rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  simp only [Mem.writeW, Mem.write, e, show i < 64 / 8 by omega_arith, ite_true]
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

/-- `copyBytes`: `len` bytes copied from `S` to `scratch + e`, with `Ctx` kept. -/
theorem copyB_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {src dst : Reg} {S : Addr} {e len : Nat}
    (hs : u.gpr src = S) (hdi : u.gpr dst = L.scr + BitVec.ofNat 64 e) (hsr : src ≠ .x11) (hdr : dst ≠ .x11)
    (hd13 : dst ≠ .x13) (h8 : 8 ≤ len) (hl : len ≤ 72) (he : e + len ≤ 8192)
    (hr : ∀ j, j + 8 ≤ len → InRegions (u.rd ++ u.wr) (S + BitVec.ofNat 64 j) 8)
    (hsep : Region.Disjoint ⟨S, len⟩ ⟨L.scr + BitVec.ofNat 64 e, len⟩) :
    WP isa (.block (Cfg.copyBytes len src dst)) u fun u' => Ctx L g m₀ u' ∧
      (∀ r, r ≠ .x11 → r ≠ .x13 → r ≠ .x14 → u'.gpr r = u.gpr r) ∧
      Frame [⟨L.scr + BitVec.ofNat 64 e, len⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.scr + BitVec.ofNat 64 e) len = Spec.Sha256.bytesAt u.mem S len :=
  WP.mono_syms (copyBytes_ok hdr hsr hd13 hsep h8 (by omega_arith) hs hdi hr
    fun j hj => by rw [Offset.add_add]; exact hc.inScrW (by omega_arith)) fun u' ⟨hrd, hwr, hsp, hg, hf, hb⟩ hsy =>
    ⟨hc.keep hL hrd hwr hsp (fun r hr _ => hg r (ne_cs hr (by decide)) (ne_cs hr (by decide))
      (ne_cs hr (by decide))) hf (hsy := hsy)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L he), hg, hf, hb⟩

/-- `‖ d ‖ h`, `Q` bytes each, after the byte at `scratch + 2256`, with
`scratch` in `x9`, `d` in `x10` and the frame in `x15` (`h` at `ho` in it),
by `copyBytes` through `x12` and through `x13` and `x14`. -/
theorem tail_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (h9 : u.gpr .x9 = L.scr) (h10 : u.gpr .x10 = L.d)
    (h15 : u.gpr .x15 = L.B + BitVec.ofNat 64 16) {Q ho : Nat} (h8 : 8 ≤ Q) (hQ : Q ≤ 66)
    (hho : 16 + ho + Q ≤ 240 + 8 * L.e) (hho' : ho < 4096) (hq : Q ≤ L.q) :
    WP isa (.block (.addImm .x .x12 .x9 (sMsg + 1) :: Cfg.copyBytes Q .x10 .x12 ++
        ([.addImm .x .x13 .x15 ho, .addImm .x .x14 .x12 Q] : List Instr) ++ Cfg.copyBytes Q .x13 .x14)) u
      fun u' => Ctx L g m₀ u' ∧ Frame [⟨L.scr + BitVec.ofNat 64 2257, 2 * Q⟩] u.mem u'.mem ∧
        Spec.Sha256.bytesAt u'.mem (L.scr + BitVec.ofNat 64 2257) (2 * Q) =
          Spec.Sha256.bytesAt u.mem L.d Q ++ Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (16 + ho)) Q := by
  have he := L.he
  simp only [sMsg]
  rw [List.cons_append, List.cons_append, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (addImm_ok hL hc (d := .x12) (src := .x9) (by decide) h9 (k := 2256 + 1) (by omega_arith))
    fun u₁ h₁ => ?_
  rw [← h₁.mem]
  -- `d`'s bytes, then `h`'s, each copied from where nothing written since is.
  have dS : Region.Disjoint ⟨L.d, Q⟩ ⟨L.scr + BitVec.ofNat 64 (2256 + 1), Q⟩ :=
    (hL.dc.sub_left (Region.sub_prefix hq)).sub_right (Offset.sub_base _ (by omega_arith))
  have hS : ∀ {m m' : Mem} {e : Nat}, Frame [⟨L.scr + BitVec.ofNat 64 e, Q⟩] m m' → e + Q ≤ 8192 →
      Spec.Sha256.bytesAt m' (L.B + BitVec.ofNat 64 (16 + ho)) Q =
        Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 (16 + ho)) Q :=
    fun hf he => bytesAt_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hL.stk_scr (by omega_arith) (by omega_arith)) (by omega_arith)
  have fr : ∀ {m₁ m₂ m₃ : Mem}, Frame [⟨L.scr + BitVec.ofNat 64 (2256 + 1), Q⟩] m₁ m₂ →
      Frame [⟨L.scr + BitVec.ofNat 64 (2256 + 1 + Q), Q⟩] m₂ m₃ →
      Frame [⟨L.scr + BitVec.ofNat 64 2257, 2 * Q⟩] m₁ m₃ := fun f₁ f₂ =>
    (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega_arith)⟩).trans
    (f₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega_arith) (by omega_arith)⟩)
  have cat : ∀ {m₂ m₃ : Mem}, Frame [⟨L.scr + BitVec.ofNat 64 (2256 + 1 + Q), Q⟩] m₂ m₃ →
      Spec.Sha256.bytesAt m₃ (L.scr + BitVec.ofNat 64 2257) (2 * Q) =
        Spec.Sha256.bytesAt m₂ (L.scr + BitVec.ofNat 64 (2256 + 1)) Q ++
          Spec.Sha256.bytesAt m₃ (L.scr + BitVec.ofNat 64 (2256 + 1 + Q)) Q := fun f₂ => by
    rw [show 2 * Q = Q + Q by omega_arith, Proof.Hmac.Common.bytesAt_add, Offset.add_add,
      bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by omega_arith)]
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (copyB_ok hL h₁.ctx (u := u₁) (src := .x10) (dst := .x12) (e := 2256 + 1) (len := Q)
    (by rw [h₁.keep _ (by decide), h10]) h₁.val (by decide) (by decide) (by decide) h8 (by omega_arith) (by omega_arith)
    (fun j hj => h₁.ctx.inD (by omega_arith) (by omega_arith)) dS) fun u₂ ⟨hc₂, hg₂, hf₂, hb₂⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (addImm_ok hL hc₂ (d := .x13) (src := .x15) (by decide)
    (by rw [hg₂ _ (by decide) (by decide) (by decide), h₁.keep _ (by decide), h15]) (k := ho) hho')
    fun u₃ h₃ => ?_
  refine WP.mono (addImm_ok hL h₃.ctx (d := .x14) (src := .x12) (by decide)
    (by rw [h₃.keep _ (by decide), hg₂ _ (by decide) (by decide) (by decide), h₁.val]) (k := Q) (by omega_arith))
    fun u₄ h₄ => ?_
  rw [Offset.add_add] at h₃ h₄
  refine WP.mono (copyB_ok hL h₄.ctx (src := .x13) (dst := .x14) (S := L.B + BitVec.ofNat 64 (16 + ho))
    (e := 2256 + 1 + Q) (len := Q)
    (by rw [h₄.keep _ (by decide)]; exact h₃.val) h₄.val (by decide) (by decide) (by decide) h8 (by omega_arith)
    (by omega_arith)
    (fun j hj => by rw [Offset.add_add]; exact h₄.ctx.inFr (by omega_arith) (by omega_arith))
    (hL.stk_scr (by omega_arith) (by omega_arith))) fun u₅ ⟨hc₅, _, hf₅, hb₅⟩ => ?_
  rw [h₄.mem, h₃.mem] at hf₅ hb₅
  refine ⟨hc₅, fr hf₂ hf₅, ?_⟩
  rw [cat hf₅, hb₂, hb₅, hS hf₂ (by omega_arith)]

variable {P : RfcHash}

/-- `h` in the frame. -/
abbrev hOf (P : RfcHash) {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (m : Mem) : List Byte :=
  Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 (16 + (cfgOf P).fHo)) P.Q

/-- The length of the message. -/
abbrev mlen (P : RfcHash) (full : Bool) : Nat := if full then 1 + 2 * P.Q else 1

/-- The message `b` (`‖ d ‖ h` if `full`, `Q` bytes each) at `scratch + 2256`. -/
theorem msg_ok (hL : L.Ok) (hq : L.q = P.Q) {t : State} (hc : Ctx L g m₀ t) (h9 : t.gpr .x9 = L.scr)
    (h10 : t.gpr .x10 = L.d) (h15 : t.gpr .x15 = L.B + BitVec.ofNat 64 16) (b : Nat) (full : Bool) :
    WP isa (.block ((cfgOf P).msg b full)) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2256, 1 + 2 * P.Q⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.scr + BitVec.ofNat 64 2256) (mlen P full) =
        [BitVec.ofNat 8 b] ++ (if full then Spec.Sha256.bytesAt t.mem L.d P.Q ++ hOf P L t.mem else []) := by
  have hQ := P.sizes
  have he := L.he
  have hho : 16 + (cfgOf P).fHo + P.Q ≤ 240 + 8 * L.e ∧ (cfgOf P).fHo < 4096 := by
    simp only [Cfg.fHo, cfgOf]
    rcases Bool.eq_false_or_eq_true P.R.big with h | h <;>
      simp only [h, fX, fH, ite_true, ite_false, Bool.false_eq_true] <;> exact ⟨by anums, by decide⟩
  have hb : ∀ {u : State}, Ctx L g m₀ u → u.gpr .x9 = L.scr →
      WP isa (.block [.movz .x .x11 (BitVec.ofNat 16 b) 0, .strb .x11 .x9 sMsg]) u fun u' => Ctx L g m₀ u' ∧
        (∀ r, r ≠ .x11 → u'.gpr r = u.gpr r) ∧ Frame [⟨L.scr + BitVec.ofNat 64 2256, 1⟩] u.mem u'.mem ∧
        Spec.Sha256.bytesAt u'.mem (L.scr + BitVec.ofNat 64 2256) 1 = [BitVec.ofNat 8 b] := fun {u} hcu h9u =>
    WP.mono_syms (strb_ok hcu h9u (b := b) (o := 2256) (by decide)) fun u' ⟨hrd, hwr, hsp, hg, hm⟩ hsy => by
      have hf : Frame [⟨L.scr + BitVec.ofNat 64 2256, 1⟩] u.mem u'.mem := by
        rw [hm]; exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
      refine ⟨hcu.keep hL hrd hwr hsp (fun r hr _ => hg r (ne_cs hr (by decide))) hf (hsy := hsy)
          (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L (by decide)), hg, hf, ?_⟩
      show [u'.mem (L.scr + BitVec.ofNat 64 2256 + BitVec.ofNat 64 0)] = _
      rw [add_ofNat_zero, hm, byte_self]
  cases full
  · simp only [Cfg.msg, Bool.false_eq_true, ite_false, List.append_nil, mlen]
    refine WP.mono (hb hc h9) fun u ⟨hcu, _, hf, hb⟩ =>
      ⟨hcu, hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩, hb⟩
    simp only [List.mem_singleton] at hr; subst hr
    exact Region.sub_prefix (by omega_arith)
  · simp only [Cfg.msg, ite_true, mlen]
    rw [WP.block_append_iff]
    refine WP.mono (hb hc h9) fun u ⟨hcu, hg, hf, hb⟩ => ?_
    refine WP.mono (tail_ok hL hcu ((hg _ (by decide)).trans h9) ((hg _ (by decide)).trans h10)
      ((hg _ (by decide)).trans h15) (Q := (cfgOf P).len) (ho := (cfgOf P).fHo)
      (by show 8 ≤ P.Q; anums) (by show P.Q ≤ 66; anums) hho.1 hho.2 (by rw [hq]; rfl))
      fun u' ⟨hcu', hf', hb'⟩ => ?_
    have hlen : (cfgOf P).len = P.Q := rfl
    rw [hlen] at hf' hb'
    refine ⟨hcu', ?_, ?_⟩
    · refine (hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
        (hf'.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
      · simp only [List.mem_singleton] at hr; subst hr
        exact Region.sub_prefix (by omega_arith)
      · simp only [List.mem_singleton] at hr; subst hr
        exact Offset.sub _ (by omega_arith) (by omega_arith)
    · rw [Proof.Hmac.Common.bytesAt_add _ _ 1 (2 * P.Q), Offset.add_add]
      have hb'' : Spec.Sha256.bytesAt u'.mem (L.scr + BitVec.ofNat 64 2257) (2 * P.Q) =
          Spec.Sha256.bytesAt u.mem L.d P.Q ++ hOf P L u.mem := hb'
      rw [hb'', bytesAt_frame hf' (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by anums)) (by omega_arith), hb]
      refine congrArg ([BitVec.ofNat 8 b] ++ ·) ?_
      have hdq : Spec.Sha256.bytesAt u.mem L.d P.Q = Spec.Sha256.bytesAt t.mem L.d P.Q :=
        bytesAt_frame hf (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hL.dc.sub_left (Region.sub_prefix (by rw [hq]))).sub_right (Offset.sub_base _ (by omega_arith)))
          (by anums)
      rw [hdq]
      refine congrArg (Spec.Sha256.bytesAt t.mem L.d P.Q ++ ·) ?_
      exact bytesAt_frame hf (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hL.stk_scr (by omega_arith) (by omega_arith)) (by anums)

end VG.Proof.Ecdsa.Rfc6979.AArch64
