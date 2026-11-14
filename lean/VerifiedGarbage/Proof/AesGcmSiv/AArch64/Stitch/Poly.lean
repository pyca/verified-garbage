module

public import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Stitch.Loops
public import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Stitch.Steps
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Tbl
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Polyval
import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Ok
import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `AesGcmSiv.AArch64.Stitch.Tbl`, which only this module used -/

section

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
  · obtain rfl : k = 1 := by omega_using [hk, hk1]
    rw [w₄, hm, ext8_ext8, hP.key]
  · obtain rfl : k = 1 := by omega_using [hk, hk1]
    rw [s₁', hm, hP.key]
  · rw [o₄.gpr, o₃.gpr, kg₂ r h5 h6 h7, o₁.gpr]
  · rw [o₄.mem, o₃.mem, m₂, o₁.mem]
  · rw [o₄.sp, o₃.sp, sp₂, o₁.sp]
  · rw [o₄.rd, o₃.rd, rd₂, o₁.rd]
  · rw [o₄.wr, o₃.wr, wr₂, o₁.wr]

/-! ## The table -/

/-- Where the table is. -/
abbrev tblR (W : Addr) : Region := ⟨W + BitVec.ofNat 64 tblO, 192⟩

theorem sOff_eq (k : Nat) : sOff (k + 1) = tblO + 16 * k := by unfold sOff; omega_using []

theorem kOff_eq (p : Nat) : kOff p = tblO + 128 + 16 * p := by unfold kOff; omega_using []

theorem tblO_eq : tblO = 480 := rfl

/-- A store into the table. -/
theorem st_ok (t : VReg) {d : Nat} (hd : tblO ≤ d) (hd' : d + 16 ≤ tblO + 192) (h16 : d % 16 = 0) {s : State}
    (hw : InRegions s.wr (s.gpr .x19 + BitVec.ofNat 64 tblO) 192) :
    WP isa (.block [.strq t .x19 d]) s fun s' =>
      s' = { s with mem := s.mem.write (s.gpr .x19 + BitVec.ofNat 64 d) 16 (s.v t) } ∧
      Frame [tblR (s.gpr .x19)] s.mem s'.mem := by
  have hin : InRegions s.wr (s.gpr .x19 + BitVec.ofNat 64 d) 16 := by
    have := CallLay.inRegions_sub (off := d - tblO) (l := 16) hw (by omega_using [hd']) (by decide)
    rwa [Offset.add_add, show tblO + (d - tblO) = d by omega_using [hd]] at this
  refine WP.block_cons_iff.mpr ⟨_, Proof.Gcm.AArch64.Pmull.exec_strq h16 (by rw [tblO_eq] at hd'; omega_using [hd']) hin,
    WP.block_nil ⟨rfl, ?_⟩⟩
  exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Offset.contains _ hd (by omega_using [hd']) (by decide))

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
    refine WP.mono (ih (by omega_using [hn])) fun s h => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have e := sOff_eq n
    refine WP.mono (st_ok (s := s) (sReg (n + 1)) (d := sOff (n + 1)) (by omega_using [e]) (by omega_using [hn, e])
      (by rw [e, tblO_eq]; omega_using []) (by rw [h.wr, h.gpr]; exact hw)) fun s' ⟨hs', f'⟩ => ?_
    subst hs'
    refine ⟨h.v, h.gpr, h.sp, h.rd, h.wr, h.frame.trans (h.gpr ▸ f'), fun k hk => ?_, nofun⟩
    dsimp only
    rw [h.gpr]
    rcases (by omega_using [hk] : k = n ∨ k < n) with rfl | hk'
    · rw [readW_write_self, h.v _ (sReg_nlow _), hI.sw _ (by omega_using []) (by omega_using [hn])]
    · rw [readW_write_sep (by rw [sOff_eq, sOff_eq]; omega_using [hk']) (by rw [sOff_eq, tblO_eq]; omega_using [hn, hk])
        (by rw [tblO_eq] at e; omega_using [hn, e]), h.sw k hk']

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
  refine WP.mono (st_ok .v4 (d := kOff q) (by omega_using [e]) (by omega_using [hq, e]) (by rw [e, tblO_eq]; omega_using [])
    (by rw [wr₃, g₃, h.wr, h.gpr]; exact hw)) fun s' ⟨hs', f'⟩ => ?_
  subst hs'
  refine ⟨fun r hr => by dsimp only; rw [v₃ r hr, h.v r hr], by dsimp only; rw [g₃, h.gpr],
    by dsimp only; rw [sp₃, h.sp], by dsimp only; rw [rd₃, h.rd], by dsimp only; rw [wr₃, h.wr],
    h.frame.trans (by rw [← m₃]; rw [show tblR (s₃.gpr .x19) = tblR (s₀.gpr .x19) by rw [g₃, h.gpr]] at f'; exact f'),
    fun k hk => ?_, fun p hp => ?_⟩
  · dsimp only
    rw [g₃, m₃, h.gpr, readW_write_sep (by rw [sOff_eq, kOff_eq]; omega_using [hk]) (by rw [sOff_eq, tblO_eq]; omega_using [hk])
      (by rw [tblO_eq] at e; omega_using [hq, e]), h.sw k hk]
  · dsimp only
    rw [g₃, m₃, h.gpr]
    rcases (by omega_using [hp] : p = q ∨ p < q) with rfl | hp'
    · rw [readW_write_self, v4, h.v _ (sReg_nlow _), h.v _ (tReg_nlow _), h.v _ (sReg_nlow _),
        h.v _ (tReg_nlow _), hI.sw _ k1 k8, hI.t _ k1 k8, hI.sw _ l1 l8, hI.t _ l1 l8, kpack_eq]
      rfl
    · rw [readW_write_sep (by rw [kOff_eq, kOff_eq]; omega_using [hp']) (by rw [kOff_eq, tblO_eq]; omega_using [hq, hp])
        (by rw [tblO_eq] at e; omega_using [hq, e]), h.key p hp']

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
      refine WP.mono (ih (by omega_using [hq])) fun s' h' => ?_
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact key_ok hI hw (by omega_using [hq]) h'
  rw [tblStores, WP.block_append_iff]
  exact WP.mono (sws_ok hI hw 8 (Nat.le_refl _)) fun s h => ks 4 (by decide) s h

theorem TS.tblOk {s₀ s : State} {H : Block} (h : TS s₀ H 8 4 s) : TblOk s.mem (s₀.gpr .x19) H :=
  ⟨fun k hk hk8 => by
    have := h.sw (k - 1) (by omega_using [hk8])
    rwa [show k - 1 + 1 = k by omega_using [hk]] at this, h.key⟩

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

end

end


/-!
# AES-GCM-SIV on AArch64, eight blocks at a time: POLYVAL of the data

Untrusted: everything here is checked by Lean. `polyData_ok`: `polyData`
(`Impl.AesGcmSiv.AArch64.Stitch`) absorbs the data padded with zeros, as
`absorb` does (`Proof.AesGcmSiv.AArch64.absorb_ok`): its batches by
`ghLoop`, from the table of keys `tblBuild` writes (`polyBatch_ok`), the
rest by `absorb`; and `polyval_ok` is `Proof.AesGcmSiv.AArch64.polyval_ok`
with it.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.AArch64.Stitch

open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcmSiv.AArch64 (Prm Lay Env Perm envRegs Absorbed AbsPost absR absorbR absorbR_buf absR_sub
  elemsAt absorb_ok lens_ok tagIn_ok tagInMem tagInMem_frame tagInMem_bytes polyR PolyPost absorbR_H)
open VG.Proof.GcmSiv.Words (hkeyOf tagInputG)
open VG.Proof.AesGcm.AArch64 (GcmImpl Others covers_left lsr_ofNat eval_zero add_ofNat_assoc length_bytesAt)
open VG.Proof.Gcm.AArch64.Pmull (ext8 VOnly PrepPow rev64b_read blockAt_store ext8_ext8)
open VG.Proof.Gcm.AArch64.Stitch (Gh8Ok)
open VG.Impl.AesGcmSiv.AArch64.Stitch
open VG.Impl.Gcm.AArch64.Stitch (Y C)
open VG.Spec.Gcm (Block blockAt ghashFrom)

/-! ## Words -/

theorem getLsbD_read (m : Mem) : ∀ (n : Nat) (a : Addr) (i : Nat), i < 8 * n →
    (m.read a n).getLsbD i = (m (a + BitVec.ofNat 64 (i / 8))).getLsbD (i % 8)
  | 0, _, _, h => absurd h (by omega_arith)
  | n + 1, a, i, h => by
    simp only [Mem.read, BitVec.getLsbD_append]
    by_cases hi : i < 8
    · simp [hi, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]
    · simp only [hi, ite_false]
      rw [getLsbD_read m n (a + 1) (i - 8) (by omega_arith)]
      have e1 : (i - 8) / 8 = i / 8 - 1 := by omega_arith
      have e2 : (i - 8) % 8 = i % 8 := by omega_arith
      rw [e1, e2]
      congr 2
      rw [BitVec.add_assoc]; congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
      omega_arith

/-- 16 bytes as two doublewords. -/
theorem readW128_q (m : Mem) (a : Addr) : m.readW a 128 = m.readW (a + BitVec.ofNat 64 8) 64 ++ m.readW a 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [Mem.readW, BitVec.getLsbD_setWidth, BitVec.getLsbD_append]
  rw [getLsbD_read _ 16 a i (by omega_arith)]
  by_cases h : i < 64
  · simp only [h, decide_true, Bool.cond_true, BitVec.getLsbD_setWidth]
    rw [getLsbD_read _ 8 a i (by omega_arith)]
    simp [hi, h]
  · simp only [h, decide_false, Bool.cond_false, BitVec.getLsbD_setWidth]
    rw [getLsbD_read _ 8 _ (i - 64) (by omega_arith), Offset.add_add, show 8 + (i - 64) / 8 = i / 8 by omega_arith,
      show (i - 64) % 8 = i % 8 by omega_arith]
    simp [hi, h, show i - 64 < 64 by omega_arith]

/-- 16 bytes as a number. -/
theorem ofBytes_readW (m : Mem) (a : Addr) : Spec.GcmSiv.ofBytes (bytesAt m a 16) = m.readW a 128 := by
  rw [GcmSiv.ofBytes_bytesAt, readW128_q]

/-! ## The setup and the end of `ghLoop` -/

/-- `batches` and `ghSetup`: the data's pointer and batches, the reduction
constant and `Y` as loaded. -/
theorem ghPre_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) :
    WP isa (.block (batches ++ ghSetup)) s fun s' =>
      s'.gpr .x9 = p.D + BitVec.ofNat 64 (128 * 0) ∧ s'.gpr .x11 = BitVec.ofNat 64 (p.n / 128 - 0) ∧
      s'.v C = ofVDwords Impl.Gcm.AArch64.Pmull.poly Impl.Gcm.AArch64.Pmull.poly ∧
      s'.v Y = ext8 (blockAt s.mem (p.W + BitVec.ofNat 64 80)) (blockAt s.mem (p.W + BitVec.ofNat 64 80)) ∧
      Others [.x9, .x11, .x12] s s' ∧ s'.mem = s.mem ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hy : InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 80) 16 := by
    rw [E.x19]; exact E.perm.wR (by decide)
  simp only [batches, ghSetup, List.cons_append, List.nil_append]
  rw [WP.block_cons_iff]
  refine ⟨_, exec_addImm_x (imm := 0) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_lsr_x (sh := 7) (by decide), ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, Proof.Gcm.AArch64.Pmull.exec_movz_x (imm := 0xc200) (hw := 3) (by decide) _, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, Proof.Gcm.AArch64.Pmull.exec_dup_d2 C .x12 _, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, Proof.Gcm.AArch64.Pmull.exec_ldrq (t := Y) (off := 80) (by decide) (by decide)
    (by simpa only [gpr_setV, rd_setV, wr_setV, gpr_write_of_ne _ _ _ (show Reg.x19 ≠ Reg.x12 by decide),
      gpr_write_of_ne _ _ _ (show Reg.x19 ≠ Reg.x11 by decide),
      gpr_write_of_ne _ _ _ (show Reg.x19 ≠ Reg.x9 by decide), rd_write, wr_write] using hy), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, Proof.Gcm.AArch64.Pmull.exec_rev64b Y Y _, WP.block_nil ?_⟩
  refine ⟨?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · simp only [gpr_setV, gpr_write, reduceCtorEq, ite_false, ite_true, State.read, BitVec.setWidth_eq, E.x25,
      Nat.mul_zero, BitVec.add_zero]
  · simp only [gpr_setV, gpr_write, reduceCtorEq, ite_false, ite_true, State.read, BitVec.setWidth_eq, E.x26,
      Nat.sub_zero]
    rw [lsr_ofNat _ _ L.n_lt]
  · simp only [v_write, v_setV_of_ne _ _ (show C ≠ Y by decide), v_setV_self, gpr_write_self]
    rfl
  · simp only [v_write, v_setV_self, mem_setV, mem_write, gpr_setV, gpr_write_of_ne _ _ _ (show Reg.x19 ≠ Reg.x12 by decide),
      gpr_write_of_ne _ _ _ (show Reg.x19 ≠ Reg.x11 by decide), gpr_write_of_ne _ _ _ (show Reg.x19 ≠ Reg.x9 by decide),
      E.x19]
    rw [rev64b_read]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setV, gpr_write_of_ne _ _ _ hr.1, gpr_write_of_ne _ _ _ hr.2.1, gpr_write_of_ne _ _ _ hr.2.2]

/-- `ghFinish`: `Y` stored back to `W + 80`. -/
theorem ghFinish_ok {p : Prm} {s : State} (hx19 : s.gpr .x19 = p.W)
    (hw : InRegions s.wr (p.W + BitVec.ofNat 64 80) 16) :
    WP isa (.block ghFinish) s fun s' =>
      blockAt s'.mem (p.W + BitVec.ofNat 64 80) = ext8 (s.v Y) (s.v Y) ∧
      Frame [⟨p.W + BitVec.ofNat 64 80, 16⟩] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  rw [ghFinish, WP.block_cons_iff]
  refine ⟨_, Proof.Gcm.AArch64.Pmull.exec_rev64b Y Y _, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, Proof.Gcm.AArch64.Pmull.exec_strq (t := Y) (off := 80) (by decide) (by decide)
    (by simpa only [wr_setV, gpr_setV, hx19] using hw), WP.block_nil ?_⟩
  refine ⟨?_, ?_, rfl, rfl, rfl, rfl⟩
  · show blockAt ((s.setV Y _).mem.write ((s.setV Y _).gpr .x19 + BitVec.ofNat 64 80) 16 ((s.setV Y _).v Y)) _ = _
    rw [gpr_setV, v_setV_self, mem_setV, hx19, blockAt_store]
  · show Frame _ s.mem ((s.setV Y _).mem.write ((s.setV Y _).gpr .x19 + BitVec.ofNat 64 80) 16 _)
    rw [gpr_setV, mem_setV, hx19]
    exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)

/-! ## The batches -/

theorem elemsAt_eq {m m' : Mem} {D : Addr} {k : Nat}
    (h : ∀ i < k, m'.readW (D + BitVec.ofNat 64 (16 * i)) 128 = m.readW (D + BitVec.ofNat 64 (16 * i)) 128) :
    (List.range k).map (fun i => m'.readW (D + BitVec.ofNat 64 (16 * i)) 128) = elemsAt m D k := by
  refine List.map_congr_left fun i hi => ?_
  rw [h i (List.mem_range.mp hi), ofBytes_readW]

/-- The batches of the data hashed by `ghLoop`, from the table of keys. -/
theorem polyBatch_ok (hP : PrepPow) (gh : Gh8Ok) (e3 : Bool) {p : Prm} (L : Lay p) {t : State} (E : Env p t)
    (hnb : 1 ≤ p.n / 128) :
    WP isa (.seq (.block (tblBuild ++ batches ++ ghSetup)) (.seq (ghLoop e3) (.block ghFinish))) t
      (Absorbed p (absR p.W) (elemsAt t.mem p.D (8 * (p.n / 128))) t) := by
  have hn := L.n_lt
  have hww := L.ww
  rw [List.append_assoc, WP.seq_iff, WP.block_append_iff]
  refine WP.mono (tblBuild_ok hP (by rw [E.x19]; exact E.perm.wR (by decide)) (by rw [E.x19]; exact E.perm.wW (by decide)))
    fun s₁ ⟨tok₁, f₁, g₁, sp₁, rd₁, wr₁⟩ => ?_
  have E₁ : Env p s₁ := E.keep (fun r hr => g₁ r (by simp at hr; rcases hr with h|h|h|h|h|h|h|h <;> subst h <;> decide)
    (by simp at hr; rcases hr with h|h|h|h|h|h|h|h <;> subst h <;> decide)
    (by simp at hr; rcases hr with h|h|h|h|h|h|h|h <;> subst h <;> decide)) sp₁ rd₁ wr₁
  refine WP.mono (ghPre_ok L E₁) fun s₂ ⟨x9₂, x11₂, c₂, y₂, o₂, m₂, sp₂, rd₂, wr₂⟩ => ?_
  rw [E.x19] at tok₁ f₁
  -- The context of the loop.
  let σ : Ctx := ⟨p.W, p.W + BitVec.ofNat 64 240, p.D, p.R, p.n / 128, blockAt t.mem (p.W + BitVec.ofNat 64 64),
    s₂.mem, t.rd, t.wr⟩
  have hd₁ : Frame [tblR p.W] t.mem s₂.mem := by rw [m₂]; exact f₁
  have dT : (⟨p.D, p.n⟩ : Region).Disjoint (tblR p.W) := L.d_w' (by decide)
  have hp : KPre σ := {
    rounds := by rcases L.rounds with h | h <;> simp [σ, h]
    nb1 := hnb
    n16 := by show 128 * (p.n / 128) < 2 ^ 64; omega_arith
    k_in := by
      show InRegions (t.rd ++ t.wr) (p.W + BitVec.ofNat 64 240) (16 * (p.R + 1))
      exact E.perm.wR (by rcases L.rounds with h | h <;> rw [h] <;> decide)
    c_in := E.perm.wR (by decide)
    d_in := by
      show InRegions t.wr p.D (128 * (p.n / 128))
      exact E.perm.d _ _ ⟨⟨p.D, p.n⟩, List.mem_singleton_self _, by
        simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; omega_arith⟩
    t_in := E.perm.wR (by decide)
    d_k := by
      show (⟨p.D, 128 * (p.n / 128)⟩ : Region).Disjoint ⟨p.W + BitVec.ofNat 64 240, 16 * (p.R + 1)⟩
      exact (L.d_w' (d := 240) (k := 16 * (p.R + 1)) (by rcases L.rounds with h | h <;> rw [h] <;> decide)).sub_left
        (Region.sub_prefix (by omega_arith))
    d_c := by
      show (⟨p.D, 128 * (p.n / 128)⟩ : Region).Disjoint _
      exact (L.d_w' (by decide)).sub_left (Region.sub_prefix (by omega_arith))
    d_t := by
      show (⟨p.D, 128 * (p.n / 128)⟩ : Region).Disjoint _
      exact (L.d_w' (by decide)).sub_left (Region.sub_prefix (by omega_arith))
    wrap_t := by show p.W.toNat + 480 + 192 ≤ 2 ^ 64; omega_arith
    wrap_c := by show p.W.toNat + 96 + 16 ≤ 2 ^ 64; omega_arith
    wrap_k := by
      show (p.W + BitVec.ofNat 64 240).toNat + 16 * (p.R + 1) ≤ 2 ^ 64
      rw [L.toNat_W (by decide)]; rcases L.rounds with h | h <;> rw [h] <;> omega_arith
    tbl := by show TblOk s₂.mem p.W _; rw [m₂]; exact tok₁ }
  have hI : GInv σ (blockAt t.mem (p.W + BitVec.ofNat 64 80)) s₂ 0 s₂ := {
    le := Nat.zero_le _
    x9 := x9₂
    x11 := x11₂
    gpr := fun _ _ _ => rfl
    y := by
      rw [y₂, yh, Nat.mul_zero, List.range_zero, List.map_nil]
      have e : blockAt s₁.mem (p.W + BitVec.ofNat 64 80) = blockAt t.mem (p.W + BitVec.ofNat 64 80) :=
        Proof.AesGcm.AArch64.blockAt_frame f₁ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact L.w_w (.inl (by decide)) (by decide) (by decide))
      rw [e]; rfl
    cr := c₂
    mem := rfl
    sp := rfl
    rd := rfl
    wr := rfl }
  have x19₂ : s₂.gpr .x19 = p.W := by rw [o₂ _ (by decide), E₁.x19]
  refine WP.seq (WP.mono (ghLoop_ok e3 hp gh x19₂ (by rw [rd₂, wr₂, rd₁, wr₁]) hI) fun s₃ G => ?_)
  refine WP.mono (ghFinish_ok (p := p) (s := s₃) (by rw [G.gpr _ (by decide) (by decide), x19₂])
    (by rw [G.wr, wr₂, wr₁]; exact E.perm.wW (by decide))) fun s₄ ⟨b₄, f₄, g₄, sp₄, rd₄, wr₄⟩ => ?_
  refine ⟨E₁.keep (fun r hr => ?_) (by rw [sp₄, G.sp, sp₂]) (by rw [rd₄, G.rd, rd₂])
    (by rw [wr₄, G.wr, wr₂]), by rw [rd₄, G.rd, rd₂, rd₁], by rw [wr₄, G.wr, wr₂, wr₁], ?_, ?_⟩
  · simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [g₄, G.gpr r (by rcases hr with h|h|h|h|h|h|h|h <;> subst h <;> decide)
      (by rcases hr with h|h|h|h|h|h|h|h <;> subst h <;> decide),
      o₂ r (by rcases hr with h|h|h|h|h|h|h|h <;> subst h <;> decide)]
  · have f₁' : Frame (absR p.W) t.mem s₁.mem := f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨p.W + BitVec.ofNat 64 480, 1280⟩, by simp [absR], Region.sub_prefix (by decide)⟩
    have f₄' : Frame (absR p.W) s₃.mem s₄.mem := f₄.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, by simp [absR], fun _ h => h⟩
    have e₃ : s₃.mem = s₁.mem := by rw [G.mem, ← m₂]
    exact f₁'.trans (e₃ ▸ f₄')
  · rw [b₄, G.y, ext8_ext8, yh]
    have e : blockAt s₁.mem (p.W + BitVec.ofNat 64 80) = blockAt t.mem (p.W + BitVec.ofNat 64 80) :=
      Proof.AesGcm.AArch64.blockAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.w_w (.inl (by decide)) (by decide) (by decide))
    refine congrArg _ (elemsAt_eq fun i hi => ?_)
    have hσ : σ.nb = p.n / 128 := rfl
    show s₂.mem.readW _ 128 = _
    rw [m₂]
    exact f₁.readW (r := ⟨p.D, p.n⟩) (Offset.contains_base p.D (by omega_arith) (by omega_arith))
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dT) (by decide)

theorem pad16_append {a b : List Byte} (ha : a.length % 16 = 0) :
    Spec.GcmSiv.pad16 (a ++ b) = a ++ Spec.GcmSiv.pad16 b := by
  simp only [Spec.GcmSiv.pad16, List.length_append, List.append_assoc]
  congr 3; omega_arith

/-- The elements of the data padded: those of its batches, then those of
the rest padded. -/
theorem elems_split (m : Mem) (D : Addr) (n : Nat) :
    Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt m D n)) =
      elemsAt m D (8 * (n / 128)) ++
        Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt m (D + BitVec.ofNat 64 (128 * (n / 128))) (n - 128 * (n / 128)))) := by
  have e := Proof.Cmac.bytesAt_add m D (128 * (n / 128)) (n - 128 * (n / 128))
  rw [show 128 * (n / 128) + (n - 128 * (n / 128)) = n by omega_arith] at e
  rw [e, pad16_append (by rw [length_bytesAt]; omega_arith),
    GcmSiv.elems_append (by rw [length_bytesAt]; omega_arith),
    show 128 * (n / 128) = 16 * (8 * (n / 128)) by omega_arith, GcmSiv.elems_bytesAt]

/-- The start of `ifBatch`: `x9` the number of batches. -/
theorem batchHead_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    WP isa (.block [.lsr .x .x9 .x26 7]) t fun t₁ => t₁.gpr .x9 = BitVec.ofNat 64 (p.n / 128) ∧
      Env p t₁ ∧ t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr :=
  WP.run ⟨_, by grun [], rfl⟩ fun t₁ ht₁ => by
    subst ht₁
    refine ⟨by simp [gpr_write, E.x26, lsr_ofNat _ _ L.n_lt], E.write (by decide) _, rfl, rfl, rfl⟩

/-- `rest`: the data past its batches. -/
theorem rest_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    WP isa (.block rest) t fun t₁ =>
      t₁.gpr .x27 = p.D + BitVec.ofNat 64 (128 * (p.n / 128)) ∧
      t₁.gpr .x28 = BitVec.ofNat 64 (p.n - 128 * (p.n / 128)) ∧
      Env p t₁ ∧ Others [.x9, .x27, .x28] t t₁ ∧ t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr :=
  WP.run ⟨_, by simp only [rest]; grun [], rfl⟩ fun t₁ ht₁ => by
    subst ht₁
    have hl : (BitVec.ofNat 64 p.n >>> 7) <<< 7 = BitVec.ofNat 64 (128 * (p.n / 128)) := by
      rw [lsr_ofNat _ _ L.n_lt, Proof.AesGcmSiv.AArch64.ofNat_lsl]; congr 1; omega_arith
    refine ⟨by simp [gpr_write, E.x25, E.x26, hl], ?_, ?_, by others_tac, rfl, rfl, rfl⟩
    · simp [gpr_write, E.x26, hl, Proof.AesGcm.AArch64.ofNat_sub (show 128 * (p.n / 128) ≤ p.n by omega_arith) L.n_lt]
    · exact ((((E.write (by decide) _).write (by decide) _).write (by decide) _).write (by decide) _)

/-- The batches, if the data has one. -/
theorem polyBatches_ok (hP : PrepPow) (gh : Gh8Ok) (e3 : Bool) {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    WP isa (ifBatch (.seq (.block (tblBuild ++ batches ++ ghSetup)) (.seq (ghLoop e3) (.block ghFinish)))) t
      (Absorbed p (absR p.W) (elemsAt t.mem p.D (8 * (p.n / 128))) t) := by
  have hn := L.n_lt
  unfold ifBatch
  refine WP.seq (WP.mono (batchHead_ok L E) fun t₁ ⟨x9₁, E₁, m₁, rd₁, wr₁⟩ => ?_)
  refine WP.ite (decide (p.n / 128 = 0)) (eval_zero x9₁ (by omega_arith)) (fun h => ?_) (fun h => ?_)
  · have h0 : p.n / 128 = 0 := by simpa using h
    refine WP.block_nil ⟨E₁, rd₁, wr₁, by rw [m₁]; exact Frame.refl _ _, ?_⟩
    rw [h0, m₁]; simp [elemsAt, ghashFrom]
  · have h1 : 1 ≤ p.n / 128 := by simp at h; omega_arith
    exact WP.mono (polyBatch_ok hP gh e3 L E₁ h1) fun t₂ A => by rw [m₁] at A; exact A.of_eq m₁ rd₁ wr₁

/-- `polyData`: the data padded absorbed. -/
theorem polyData_ok (hP : PrepPow) (gh : Gh8Ok) (e3 : Bool) (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    WP isa (polyData e3 v.callees) t (AbsPost p (Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt t.mem p.D p.n))) t) := by
  have hn := L.n_lt
  unfold polyData ifBatch
  -- The batches.
  have hb := polyBatches_ok hP gh e3 L E
  refine WP.seq (WP.mono hb fun t₂ A => ?_)
  -- The rest.
  refine WP.seq (WP.mono (rest_ok L A.env) fun t₃ ⟨x27₃, x28₃, E₃, o₃, m₃, rd₃, wr₃⟩ => ?_)
  have hc : Covers [⟨p.D + BitVec.ofNat 64 (128 * (p.n / 128)), p.n - 128 * (p.n / 128)⟩] (t₃.rd ++ t₃.wr) := by
    rw [rd₃, wr₃, A.rd, A.wr]
    exact covers_left (Proof.AesGcm.AArch64.covers_off E.perm.d (by omega_arith) hn)
  have dW : (⟨p.D + BitVec.ofNat 64 (128 * (p.n / 128)), p.n - 128 * (p.n / 128)⟩ : Region).Disjoint ⟨p.W, 3808⟩ :=
    L.d_w.sub_left (Offset.sub_base p.D (by omega_arith))
  refine WP.mono (absorb_ok v L E₃ hc (by omega_arith) (by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 128 * (p.n / 128)) (by omega_arith)]
      have := L.dw; have := Nat.mod_le (p.D.toNat + 128 * (p.n / 128)) (2 ^ 64); omega_arith)
    dW x27₃ x28₃) fun t₄ P₄ => ?_
  have e : bytesAt t₃.mem (p.D + BitVec.ofNat 64 (128 * (p.n / 128))) (p.n - 128 * (p.n / 128)) =
      bytesAt t.mem (p.D + BitVec.ofNat 64 (128 * (p.n / 128))) (p.n - 128 * (p.n / 128)) := by
    rw [m₃]
    exact Proof.AesGcm.AArch64.bytesAt_frame A.frame (fun r hr => dW.sub_right (by
      simp only [absR, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Proof.AesGcmSiv.AArch64.Lay.wSub (by decide))) (by omega_arith)
  rw [e] at P₄
  rw [elems_split]
  exact AbsPost.trans L (A.sub (absR_sub p.W)) (P₄.of_eq m₃ rd₃ wr₃)

/-- `polyval` with `polyData` (`Proof.AesGcmSiv.AArch64.polyval_ok`). -/
theorem polyval_ok (hP : PrepPow) (gh : Gh8Ok) (e3 : Bool) (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t)
    (hG : Spec.Gcm.blockAt t.mem (p.W + BitVec.ofNat 64 64) =
      hkeyOf (Spec.GcmSiv.ofBytes (bytesAt t.mem (p.W + BitVec.ofNat 64 16) 16)))
    (hY : Spec.Gcm.blockAt t.mem (p.W + BitVec.ofNat 64 80) = 0) :
    WP isa (Impl.AesGcmSiv.AArch64.Stitch.polyval e3 v.callees) t (PolyPost p t) := by
  -- The additional data.
  refine WP.seq (WP.of_runBlock ⟨_, by grun [], ?_⟩)
  refine WP.seq (WP.mono (absorb_ok v L ((E.write (by decide) _).write (by decide) _) (by simp only [rd_write, wr_write]; exact E.perm.aad) L.al_lt L.aw L.a_w
    (by simp [gpr_write, E.x23]) (by simp [gpr_write, E.x24])) fun t₂ P₂ => ?_)
  simp only [mem_write] at P₂
  have P₂' := P₂.of_eq (t := t) rfl rfl rfl
  -- The data.
  refine WP.seq (WP.mono (polyData_ok hP gh e3 v L P₂.env) fun t₄ P₄ => ?_)
  rw [Proof.AesGcm.AArch64.bytesAt_frame P₂.frame (absorbR_buf L.d_w) (by have := L.n_lt; omega_arith)] at P₄
  have P₂₄ := AbsPost.trans L P₂' P₄
  -- The lengths.
  refine WP.seq (WP.mono (lens_ok v L P₂₄.env) fun t₅ P₅ => ?_)
  have P₂₅ := AbsPost.trans L P₂₄ P₅
  -- The tag input.
  obtain ⟨t₆, run₆, hm₆, ho₆, sp₆, rd₆, wr₆⟩ := tagIn_ok P₂₅.env
  refine WP.of_runBlock ⟨t₆, run₆, P₂₅.env.keep (fun q hq => ho₆ q (by
      simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₆ rd₆ wr₆,
    by rw [rd₆, P₂₅.rd], by rw [wr₆, P₂₅.wr], ?_, ?_⟩
  · refine (P₂₅.frame.mono fun q hq => List.mem_cons_of_mem _ hq).trans ?_
    rw [hm₆]
    exact (tagInMem_frame _ _ _).mono fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact List.mem_cons_self
  · have hp : ∀ xs ys : List Byte, (Spec.GcmSiv.pad16 xs ++ Spec.GcmSiv.pad16 ys).length % 16 = 0 := fun xs ys => by
      rw [List.length_append]; have := GcmSiv.pad16_mod xs; have := GcmSiv.pad16_mod ys; omega_arith
    have nN : bytesAt t₅.mem p.N 12 = bytesAt t.mem p.N 12 :=
      Proof.AesGcm.AArch64.bytesAt_frame P₂₅.frame (absorbR_buf L.n_w) (by decide)
    rw [hm₆, tagInMem_bytes, nN, P₂₅.out, hG, hY, tagInputG, length_bytesAt, length_bytesAt,
      GcmSiv.elems_append (hp _ _), GcmSiv.elems_append (GcmSiv.pad16_mod _),
      GcmSiv.elems_single (bs := Spec.GcmSiv.le64 (8 * p.al) ++ Spec.GcmSiv.le64 (8 * p.n))
        (by simp [Spec.GcmSiv.le64])]
    simp only [mem_write]

end VG.Proof.AesGcmSiv.AArch64.Stitch
