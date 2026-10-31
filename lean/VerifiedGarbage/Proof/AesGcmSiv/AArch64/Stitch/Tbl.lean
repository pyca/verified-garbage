module

public import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Stitch.Steps
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Tbl
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract

/-!
# AES-GCM-SIV on AArch64, eight blocks at a time: the table of keys

Untrusted: everything here is checked by Lean. `tblBuild_ok`: `tblBuild`
(`Impl.AesGcmSiv.AArch64.Stitch`) leaves the table of keys of GHASH's key `H`
(at `W + 64`) at `W + tblO` (`TblOk`): `H'` computed from `H` as
`vg_ghash_aes`'s prologue computes it (`keyV`), the powers by its `powers`
(`Proof.AesGcm.AArch64.Stitch.powers_ok`), from `PrepPow` (the algebra's
one fact, a hypothesis here), and stored as AES-GCM's table is, at another
place in `W`.
-/

@[expose] public section

local notation "ofVDwords" => VG.Proof.Gcm.Clmul.ofVDwords

namespace VG.Proof.AesGcmSiv.AArch64.Stitch

open VG VG.AArch64
open VG.AArch64.RegUpd (v_setV_self v_setV_of_ne gpr_setV mem_setV rd_setV wr_setV sp_setV)
open VG.Proof.Gcm.AArch64.Pmull (ext8 VOnly pp PrepPow keyV mulV_ok swap_ok consts_ok loadRev_ok rev64b_read
  ext8_ext8 tReg_free sReg_free free_A ne_tReg ne_sReg tReg_ne_sReg)
open VG.Proof.AesGcm.AArch64.Stitch (PInv PT powers_ok powV readW_write_self readW_write_sep kv_ok kpack_eq
  pkl_range tReg_nlow sReg_nlow)
open VG.Proof.Gcm.AArch64.Stitch (kpack)
open VG.Impl.Gcm.AArch64.Pmull (LO MID HI A T C tReg sReg poly)
open VG.Impl.AesGcmSiv.AArch64.Stitch (tblO sOff kOff tblBuild)
open VG.Impl.Gcm.AArch64.Stitch (pk pl)
open VG.Spec.Gcm (Block blockAt)

/-! ## `H'` -/

/-- `Pmull.consts_ok`, with the stack pointer kept. -/
theorem consts_ok' (s : State) :
    WP isa (.block Impl.Gcm.AArch64.Pmull.consts) s fun s' =>
      s'.v C = ofVDwords poly poly ∧ s'.v (tReg 2) = Proof.Gcm.AArch64.Pmull.xInv2 ∧
      s'.v (sReg 2) = ext8 Proof.Gcm.AArch64.Pmull.xInv2 Proof.Gcm.AArch64.Pmull.xInv2 ∧
      (∀ r, r ≠ C → r ≠ tReg 2 → r ≠ sReg 2 → s'.v r = s.v r) ∧
      (∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.AArch64.Pmull.consts, tReg, sReg, runBlock_cons, runStep_some, runBlock_nil,
    Proof.Gcm.AArch64.Pmull.exec_movz_x (show 16 * 3 < 64 by decide),
    Proof.Gcm.AArch64.Pmull.exec_movz_x (show 16 * 0 < 64 by decide),
    Proof.Gcm.AArch64.Pmull.exec_dup_d2, Proof.Gcm.AArch64.Pmull.exec_ins_d2 (show 0 < 2 by decide),
    Proof.Gcm.AArch64.Pmull.exec_ins_d2 (show 1 < 2 by decide),
    Proof.Gcm.AArch64.Pmull.v_setV, gpr_setV, VG.AArch64.RegUpd.v_write, Proof.Gcm.AArch64.Pmull.gpr_write_x,
    ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left', Proof.Gcm.AArch64.Pmull.setLane_pair,
    mem_setV, rd_setV, wr_setV, sp_setV, VG.AArch64.RegUpd.mem_write, VG.AArch64.RegUpd.rd_write,
    VG.AArch64.RegUpd.wr_write, VG.AArch64.RegUpd.sp_write, and_true]
  refine ⟨by decide, by decide, by rw [Proof.Gcm.AArch64.Pmull.ext8_eq]; decide, fun r hc ht hs => ?_,
    fun r h5 h6 h7 => ?_⟩
  · simp only [hc, ht, hs, ite_false]
  · simp only [h5, h6, h7, ite_false]

/-- `H` loaded from `x19 + 64`, the constants, and `H'`. -/
theorem hPrime_ok (hP : PrepPow) {s : State}
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 Impl.AesGcmSiv.AArch64.hO) 16) :
    WP isa (.block (Impl.Gcm.AArch64.Pmull.loadRev A .x19 Impl.AesGcmSiv.AArch64.hO ++
        Impl.Gcm.AArch64.Pmull.consts ++ Impl.Gcm.AArch64.Pmull.mul (sReg 1) A (sReg 2) (tReg 2) ++
        ([.vop (.ext (tReg 1) (sReg 1) (sReg 1) 8)] : List Instr))) s fun s' =>
      PInv (blockAt s.mem (s.gpr .x19 + BitVec.ofNat 64 Impl.AesGcmSiv.AArch64.hO)) 1 s' ∧
      (∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.sp = s.sp ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadRev_ok A .x19 _ s (by decide) (by decide) hin) fun s₁ ⟨l₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (consts_ok' s₁) fun s₂ ⟨c₂, t₂, w₂, kv₂, kg₂, m₂, rd₂, wr₂, sp₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mulV_ok (sReg 1) A (sReg 2) (tReg 2) s₂ free_A (sReg_free _) (tReg_free _)
    (by rw [w₂, t₂]) c₂) fun s₃ ⟨m₃, o₃⟩ => ?_
  refine WP.mono (swap_ok (tReg 1) (sReg 1) s₃) fun s₄ ⟨w₄, o₄⟩ => ?_
  have hA₂ : s₂.v A = s₁.v A := kv₂ A (by decide) (ne_tReg 2) (ne_sReg 2)
  have hm : s₃.v (sReg 1) = ext8 (keyV (blockAt s.mem (s.gpr .x19 + BitVec.ofNat 64 Impl.AesGcmSiv.AArch64.hO)))
      (keyV (blockAt s.mem (s.gpr .x19 + BitVec.ofNat 64 Impl.AesGcmSiv.AArch64.hO))) := by
    rw [m₃, hA₂, l₁, t₂, rev64b_read, keyV, ext8_ext8]
  have s₁' : s₄.v (sReg 1) = s₃.v (sReg 1) := o₄.v _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; exact fun e => tReg_ne_sReg _ _ e.symm)
  refine ⟨⟨?_, fun k hk hk1 => ?_, fun k hk hk1 => ?_⟩, fun r h5 h6 h7 => ?_, ?_, ?_, ?_, ?_⟩
  · have h : C ∉ [LO, MID, HI, T, sReg 1] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨by decide, by decide, by decide, by decide, ne_sReg 1⟩
    rw [o₄.v C (by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact ne_tReg 1), o₃.v C h, c₂]
  · obtain rfl : k = 1 := by omega
    rw [w₄, hm, ext8_ext8, hP.key]
  · obtain rfl : k = 1 := by omega
    rw [s₁', hm, hP.key]
  · rw [o₄.gpr, o₃.gpr, kg₂ r h5 h6 h7, o₁.gpr]
  · rw [o₄.mem, o₃.mem, m₂, o₁.mem]
  · rw [o₄.sp, o₃.sp, sp₂, o₁.sp]
  · rw [o₄.rd, o₃.rd, rd₂, o₁.rd]
  · rw [o₄.wr, o₃.wr, wr₂, o₁.wr]

/-! ## The table -/

/-- Where the table is. -/
abbrev tblR (W : Addr) : Region := ⟨W + BitVec.ofNat 64 tblO, 192⟩

theorem sOff_eq (k : Nat) : sOff (k + 1) = tblO + 16 * k := by unfold sOff; omega

theorem kOff_eq (p : Nat) : kOff p = tblO + 128 + 16 * p := by unfold kOff; omega

theorem tblO_eq : tblO = 480 := rfl

/-- A store into the table. -/
theorem st_ok (t : VReg) {d : Nat} (hd : tblO ≤ d) (hd' : d + 16 ≤ tblO + 192) (h16 : d % 16 = 0) {s : State}
    (hw : InRegions s.wr (s.gpr .x19 + BitVec.ofNat 64 tblO) 192) :
    WP isa (.block [.strq t .x19 d]) s fun s' =>
      s' = { s with mem := s.mem.write (s.gpr .x19 + BitVec.ofNat 64 d) 16 (s.v t) } ∧
      Frame [tblR (s.gpr .x19)] s.mem s'.mem := by
  have hin : InRegions s.wr (s.gpr .x19 + BitVec.ofNat 64 d) 16 := by
    have := CallLay.inRegions_sub (off := d - tblO) (l := 16) hw (by omega) (by decide)
    rwa [Offset.add_add, show tblO + (d - tblO) = d by omega] at this
  refine WP.block_cons_iff.mpr ⟨_, Proof.Gcm.AArch64.Pmull.exec_strq h16 (by rw [tblO_eq] at hd'; omega) hin,
    WP.block_nil ⟨rfl, ?_⟩⟩
  exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Offset.contains _ hd (by omega) (by decide))

/-- The table's first `n` powers and `q` pairs of keys stored. -/
structure TS (s₀ : State) (H : Block) (n q : Nat) (s : State) : Prop where
  v : ∀ r, r ∉ [VReg.v2, .v3, .v4] → s.v r = s₀.v r
  gpr : s.gpr = s₀.gpr
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [tblR (s₀.gpr .x19)] s₀.mem s.mem
  sw : ∀ k < n, s.mem.readW (s₀.gpr .x19 + BitVec.ofNat 64 (sOff (k + 1))) 128 = ext8 (pp H (k + 1)) (pp H (k + 1))
  key : ∀ p < q, s.mem.readW (s₀.gpr .x19 + BitVec.ofNat 64 (kOff p)) 128 = kpack H (pk p) (pl p)

/-- The powers stored. -/
theorem sws_ok {s₀ : State} {H : Block} (hI : PT H 8 s₀)
    (hw : InRegions s₀.wr (s₀.gpr .x19 + BitVec.ofNat 64 tblO) 192) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap fun k => [.strq (sReg (k + 1)) .x19 (sOff (k + 1))]))
      s₀ (TS s₀ H n 0) := by
  intro n hn
  induction n with
  | zero => exact WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, Frame.refl _ _, nofun, nofun⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun s h => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have e := sOff_eq n
    refine WP.mono (st_ok (s := s) (sReg (n + 1)) (d := sOff (n + 1)) (by omega) (by omega)
      (by rw [e, tblO_eq]; omega) (by rw [h.wr, h.gpr]; exact hw)) fun s' ⟨hs', f'⟩ => ?_
    subst hs'
    refine ⟨h.v, h.gpr, h.sp, h.rd, h.wr, h.frame.trans (h.gpr ▸ f'), fun k hk => ?_, nofun⟩
    dsimp only
    rw [h.gpr]
    rcases (by omega : k = n ∨ k < n) with rfl | hk'
    · rw [readW_write_self, h.v _ (sReg_nlow _), hI.sw _ (by omega) (by omega)]
    · rw [readW_write_sep (by rw [sOff_eq, sOff_eq]; omega) (by rw [sOff_eq, tblO_eq]; omega)
        (by rw [tblO_eq] at e; omega), h.sw k hk']

/-- A pair of keys stored. -/
theorem key_ok {s₀ : State} {H : Block} (hI : PT H 8 s₀)
    (hw : InRegions s₀.wr (s₀.gpr .x19 + BitVec.ofNat 64 tblO) 192) {q : Nat} (hq : q < 4) {s : State}
    (h : TS s₀ H 8 q s) :
    WP isa (.block [.vop (.logic .eor .v2 (sReg (pk q)) (tReg (pk q))),
      .vop (.logic .eor .v3 (sReg (pl q)) (tReg (pl q))),
      .vop (.ext .v4 .v2 .v3 8), .strq .v4 .x19 (kOff q)]) s (TS s₀ H 8 (q + 1)) := by
  obtain ⟨k1, k8, l1, l8⟩ := pkl_range q hq
  have e := kOff_eq q
  rw [show ∀ a b c d : Instr, [a, b, c, d] = [a, b, c] ++ [d] from fun _ _ _ _ => rfl, WP.block_append_iff]
  refine WP.mono (kv_ok (pk q) (pl q) s) fun s₃ ⟨v4, v₃, g₃, m₃, sp₃, rd₃, wr₃⟩ => ?_
  refine WP.mono (st_ok .v4 (d := kOff q) (by omega) (by omega) (by rw [e, tblO_eq]; omega)
    (by rw [wr₃, g₃, h.wr, h.gpr]; exact hw)) fun s' ⟨hs', f'⟩ => ?_
  subst hs'
  refine ⟨fun r hr => by dsimp only; rw [v₃ r hr, h.v r hr], by dsimp only; rw [g₃, h.gpr],
    by dsimp only; rw [sp₃, h.sp], by dsimp only; rw [rd₃, h.rd], by dsimp only; rw [wr₃, h.wr],
    h.frame.trans (by rw [← m₃]; rw [show tblR (s₃.gpr .x19) = tblR (s₀.gpr .x19) by rw [g₃, h.gpr]] at f'; exact f'),
    fun k hk => ?_, fun p hp => ?_⟩
  · dsimp only
    rw [g₃, m₃, h.gpr, readW_write_sep (by rw [sOff_eq, kOff_eq]; omega) (by rw [sOff_eq, tblO_eq]; omega)
      (by rw [tblO_eq] at e; omega), h.sw k hk]
  · dsimp only
    rw [g₃, m₃, h.gpr]
    rcases (by omega : p = q ∨ p < q) with rfl | hp'
    · rw [readW_write_self, v4, h.v _ (sReg_nlow _), h.v _ (tReg_nlow _), h.v _ (sReg_nlow _),
        h.v _ (tReg_nlow _), hI.sw _ k1 k8, hI.t _ k1 k8, hI.sw _ l1 l8, hI.t _ l1 l8, kpack_eq]
      rfl
    · rw [readW_write_sep (by rw [kOff_eq, kOff_eq]; omega) (by rw [kOff_eq, tblO_eq]; omega)
        (by rw [tblO_eq] at e; omega), h.key p hp']

/-- The table stores. -/
abbrev tblStores : List Instr :=
  (List.range 8).flatMap (fun k => [.strq (sReg (k + 1)) .x19 (sOff (k + 1))]) ++
  (List.range 4).flatMap fun p =>
    [.vop (.logic .eor .v2 (sReg (pk p)) (tReg (pk p))),
     .vop (.logic .eor .v3 (sReg (pl p)) (tReg (pl p))),
     .vop (.ext .v4 .v2 .v3 8), .strq .v4 .x19 (kOff p)]

/-- The table of keys: the powers with their halves swapped, and the pairs' keys. -/
theorem tbl_ok {s₀ : State} {H : Block} (hI : PT H 8 s₀)
    (hw : InRegions s₀.wr (s₀.gpr .x19 + BitVec.ofNat 64 tblO) 192) :
    WP isa (.block tblStores) s₀ (TS s₀ H 8 4) := by
  have ks : ∀ q ≤ 4, ∀ s, TS s₀ H 8 0 s → WP isa (.block ((List.range q).flatMap fun p =>
      [.vop (.logic .eor .v2 (sReg (pk p)) (tReg (pk p))), .vop (.logic .eor .v3 (sReg (pl p)) (tReg (pl p))),
       .vop (.ext .v4 .v2 .v3 8), .strq .v4 .x19 (kOff p)])) s (TS s₀ H 8 q) := by
    intro q hq s h
    induction q with
    | zero => exact WP.block_nil ⟨h.v, h.gpr, h.sp, h.rd, h.wr, h.frame, h.sw, nofun⟩
    | succ q ih =>
      rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
      refine WP.mono (ih (by omega)) fun s' h' => ?_
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact key_ok hI hw (by omega) h'
  rw [tblStores, WP.block_append_iff]
  exact WP.mono (sws_ok hI hw 8 (Nat.le_refl _)) fun s h => ks 4 (by decide) s h

theorem TS.tblOk {s₀ s : State} {H : Block} (h : TS s₀ H 8 4 s) : TblOk s.mem (s₀.gpr .x19) H :=
  ⟨fun k hk hk8 => by
    have := h.sw (k - 1) (by omega)
    rwa [show k - 1 + 1 = k by omega] at this, h.key⟩

/-- `tblBuild`: the table of keys of `H` (at `x19 + 64`), and only `x5`–`x7`,
the vector registers and the table written. -/
theorem tblBuild_ok (hP : PrepPow) {s : State}
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 Impl.AesGcmSiv.AArch64.hO) 16)
    (hw : InRegions s.wr (s.gpr .x19 + BitVec.ofNat 64 tblO) 192) :
    WP isa (.block tblBuild) s fun s' =>
      TblOk s'.mem (s.gpr .x19) (blockAt s.mem (s.gpr .x19 + BitVec.ofNat 64 Impl.AesGcmSiv.AArch64.hO)) ∧
      Frame [tblR (s.gpr .x19)] s.mem s'.mem ∧
      (∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  rw [show tblBuild = (Impl.Gcm.AArch64.Pmull.loadRev A .x19 Impl.AesGcmSiv.AArch64.hO ++
        Impl.Gcm.AArch64.Pmull.consts ++ Impl.Gcm.AArch64.Pmull.mul (sReg 1) A (sReg 2) (tReg 2) ++
        ([.vop (.ext (tReg 1) (sReg 1) (sReg 1) 8)] : List Instr)) ++ Impl.Gcm.AArch64.Pmull.powers ++ tblStores
      by simp only [tblBuild, tblStores, List.append_assoc], WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (hPrime_ok hP hin) fun s₁ ⟨p₁, g₁, m₁, sp₁, rd₁, wr₁⟩ => ?_
  refine WP.mono (powers_ok hP p₁) fun s₂ ⟨p₂, o₂⟩ => ?_
  have g₂ : s₂.gpr .x19 = s.gpr .x19 := by rw [o₂.gpr, g₁ _ (by decide) (by decide) (by decide)]
  refine WP.mono (tbl_ok p₂.pt (by rw [o₂.wr, wr₁, g₂]; exact hw)) fun s₃ h₃ => ?_
  refine ⟨?_, ?_, fun r h5 h6 h7 => ?_, ?_, ?_, ?_⟩
  · have := h₃.tblOk; rwa [g₂] at this
  · have f := h₃.frame
    rw [g₂, o₂.mem, m₁] at f; exact f
  · rw [h₃.gpr, o₂.gpr, g₁ r h5 h6 h7]
  · rw [h₃.sp, o₂.sp, sp₁]
  · rw [h₃.rd, o₂.rd, rd₁]
  · rw [h₃.wr, o₂.wr, wr₁]

end VG.Proof.AesGcmSiv.AArch64.Stitch
