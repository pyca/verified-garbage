module

import VerifiedGarbage.Proof.Framework.Arm.Syms
public import VerifiedGarbage.Proof.Mont.Arm.Words
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Blocks
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Weierstrass.Arm.BytesLen
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Regs
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
import Batteries.Logic
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.AesGcm.Arm.Loops
import VerifiedGarbage.Proof.AesGcm.Arm.Run
import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Hash
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Upd
public import VerifiedGarbage.Proof.Framework.ICall

/-! ### `Ecdsa.Rfc6979.Arm.Hmac`, which this module and modules that import it used -/

section

/-!
# Deterministic ECDSA on 32-bit ARM: HMAC through the table

The table's functions, each called indirectly (`tcall_ok`: the table's word,
which `Ctx` says holds the function of `L.F`, whose call an indirect call of
`L.f`'s functions reaches), in the frame of their stack arguments as
PBKDF2's code calls them (`VG.Proof.Pbkdf2.Whole.Arm`), with the lengths and
counts the table's `D` and `B` give:

* HMAC's `init` with the key `K` (`D` bytes, the frame's first): HMAC's
  states for the block key `K₀` of `K` (`init_step`);
* the streaming `update` of the inner state with `len` bytes of data in the
  frame or in `scratch` above HMAC's working space (`DataOk`), the inner
  state holding `K₀ ⊕ ipad ‖ text`, of `B + |text|` bytes: it then holds the
  data after `text` (`upd_call`), with `V` (`updV_step`) or with the message
  at `scratch + sMsg` (`updM_step`);
* HMAC's `finalize`, with the count `B + D + len` for a text of that
  length, writing `HMAC(K₀, text)` (`D` bytes) to the frame at `dst`
  (`fin_step`).

`St P L g m₀ t text` is what holds between them: `Ctx`, and HMAC's states
for `K₀` with the inner one holding `text`. They change only HMAC's states
and working space (the first 2256 bytes of `scratch`), the 24 bytes below
the frame, and `dst`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Impl.Pbkdf2.Stream.Arm (scrAt)
open VG.Proof.Pbkdf2.Whole.Arm (After HiArgs HfArgs UpdL hi_frame hf_frame upd_frame stk fr1 fr2 upd4)
open VG.Proof.HmacTable.Arm (TabOK TabMem tA)
open VG.Proof.X25519.Arm (op2_reg op2_imm dpVal)

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

/-- The layout's table is of `P`'s hash function and functions. -/
def TabL (P : RfcHash) {dn : Nat} (L : Lay dn) : Prop := L.F = P.F ∧ L.f = P.f

/-! ## The stack below the frame -/

theorem Ctx.spA (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) : State.addr t.sp = L.B + BitVec.ofNat 64 24 := by
  rw [hc.sp]; exact hL.fpA0

theorem Ctx.sp24 (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) : 24 ≤ t.sp.toNat := by
  rw [← toNat_addr, hc.spA hL, Offset.toNat_add_ofNat]
  have := hL.B_fit; rw [Nat.mod_eq_of_lt (by omega_arith)]; omega_arith

/-- The 24 bytes below the frame, where the calls' frames go. -/
theorem Ctx.stk_eq (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) : stk t = ⟨L.B, 24⟩ := by
  simp only [stk, hc.spA hL]
  exact congrArg (fun b => (⟨b, 24⟩ : Region)) (BitVec.add_sub_cancel _ _)

/-- The 16 bytes below the stack pointer, which `update` may use. -/
theorem Ctx.below_eq (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    Pbkdf2.Stream.Arm.below t = ⟨L.B + BitVec.ofNat 64 8, 16⟩ := by
  simp only [Pbkdf2.Stream.Arm.below, hc.spA hL]
  exact congrArg (fun b => (⟨b, 16⟩ : Region)) (Offset.add_ofNat_sub L.B (show 16 ≤ 24 by decide))

theorem ptr_preserved : ∀ r ∈ ptrRegs, r ∈ preserved ∧ r ≠ .lr := by decide

/-- What a call leaves keeps `Ctx`, if it writes only safe regions and the
24 bytes below the frame. -/
theorem Ctx.after (hL : L.Ok) {u u' : State} (hc : Ctx L g m₀ u) {ws : List Region} (ha : After u ws u')
    (hs : ∀ r ∈ ws, Safe L r) (sy : u'.syms=u.syms) : Ctx L g m₀ u' :=
  hc.keep hL ha.rd ha.wr ha.sp (fun r hr => ha.cs r (ptr_preserved r hr).1 (ptr_preserved r hr).2) ha.frame
    (fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact hs r hr
      · simp only [List.mem_singleton] at hr; subst hr
        rw [hc.stk_eq hL]
        exact .inr (.inr (Region.sub_prefix (by omega_arith)))) sy

/-- The same, for `update`, which may use the 16 bytes below the stack pointer. -/
theorem Ctx.afterU (hL : L.Ok) {u u' : State} (hc : Ctx L g m₀ u) {ws : List Region}
    (ha : Pbkdf2.Stream.Arm.After u ws u') (hs : ∀ r ∈ ws, Safe L r) (sy : u'.syms=u.syms) : Ctx L g m₀ u' :=
  hc.keep hL ha.rd ha.wr ha.sp (fun r hr => ha.cs r (ptr_preserved r hr).1 (ptr_preserved r hr).2) ha.frame
    (fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact hs r hr
      · simp only [List.mem_singleton] at hr; subst hr
        rw [hc.below_eq hL]
        exact safe_low L (by omega_arith)) sy

/-! ## Addresses -/

theorem scr_toNat (hL : L.Ok) {o : Nat} (ho : o < 8192) : (L.scr + BitVec.ofNat 32 o).toNat = L.scr.toNat + o := by
  have := hL.nc
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith : o < 2 ^ 32)]
  exact Nat.mod_eq_of_lt (by omega_arith)

theorem fp_toNat (hL : L.Ok) {o : Nat} (ho : o ≤ 512) :
    (L.fp + BitVec.ofNat 32 o).toNat = L.sp.toNat - 512 + o := by
  have := hL.nB; have := L.sp.isLt; have := hL.na
  obtain hfp : L.fp.toNat = L.sp.toNat - 512 := VG.Arm.FrameStack.sub_toNat' (by omega_arith)
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith : o < 2 ^ 32), hfp]
  exact Nat.mod_eq_of_lt (by omega_arith)

/-- The stack below the frame and parts of it are apart from `scratch`. -/
theorem low_scr (hL : L.Ok) {n e k : Nat} (hn : n ≤ 536) (h : e + k ≤ 8192) :
    Region.Disjoint ⟨L.B, n⟩ ⟨State.addr L.scr + BitVec.ofNat 64 e, k⟩ :=
  (hL.kc.sub_left (Region.sub_prefix (by omega_arith))).sub_right (Offset.sub_base _ h)

/-- The part of `scratch` HMAC's functions use: its states and working space. -/
abbrev WK {dn : Nat} (L : Lay dn) : Region := ⟨State.addr L.scr, 2256⟩

theorem wk_safe {r : Region} (h : Region.Sub r (WK L)) : Safe L r :=
  .inr (.inl (sub_trans h (Region.sub_prefix (by omega_arith))))

theorem scr_wk (hL : L.Ok) {o n : Nat} (ho : o < 8192) (h : o + n ≤ 2256) :
    Region.Sub ⟨State.addr (L.scr + BitVec.ofNat 32 o), n⟩ (WK L) := by
  rw [scrA hL ho]; exact Offset.sub_base _ h

/-- The memory a call changes: within `ws`, each in `WK`, or in the 24 bytes below the frame. -/
theorem after_frame (hL : L.Ok) {u u' : State} (hc : Ctx L g m₀ u) {ws : List Region} (ha : After u ws u')
    (hs : ∀ r ∈ ws, Region.Sub r (WK L)) : Frame [WK L, ⟨L.B, 24⟩] u.mem u'.mem :=
  ha.frame.sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨WK L, by simp, hs r hr⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨L.B, 24⟩, by simp, by rw [hc.stk_eq hL]; exact sub_refl _⟩

theorem after_frameU (hL : L.Ok) {u u' : State} (hc : Ctx L g m₀ u) {ws : List Region}
    (ha : Pbkdf2.Stream.Arm.After u ws u') (hs : ∀ r ∈ ws, Region.Sub r (WK L)) :
    Frame [WK L, ⟨L.B, 24⟩] u.mem u'.mem :=
  ha.frame.sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨WK L, by simp, hs r hr⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨L.B, 24⟩, by simp, by rw [hc.below_eq hL]; exact Offset.sub_base _ (by omega_arith)⟩

/-! ## The indirect call -/

theorem push_some_gpr {rs : List Reg} {s u : State} (h : isa.push (.push rs) s = some u) :
    u.gpr = s.gpr ∧ u.syms = s.syms := by
  simp only [isa, push] at h; split at h <;> cases h; exact ⟨rfl, rfl⟩

/-- The call of the table's function `j`, among `ts`: its address, the
table's word `j`, into `lr` (`hw`), which is that of `n`, whose code an
indirect call of `ts` reaches (`ht`), then the frame of its call. -/
theorem tcall_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {j : Nat} (hj : j < 3) {n : String} {c : Prog isa}
    {ts : List (String × Prog isa)} {rs : List Reg} {r : Reg} {k : Nat} {Q : State → Prop}
    (hw : m₀.readW (tA L.tab (4 * j)) 32 = u.syms n)
    (ht : ts.find? (fun q => (u.syms q.1).setWidth 64 == (u.syms n).setWidth 64) = some (n, c))
    (hf : ∀ u', Ctx L g m₀ u' → u'.mem = u.mem → u'.syms = u.syms → (∀ q, q ≠ .lr → u'.gpr q = u.gpr q) →
      WP isa (.frame (.push rs) (.call n c) (.pop r k)) u' Q) :
    WP isa (Cfg.tcall j ts rs r k) u Q := by
  unfold Cfg.tcall
  refine WP.seq ?_
  refine WP.mono_syms (Q := fun u' => Ctx L g m₀ u' ∧ u'.mem = u.mem ∧
      u'.gpr .lr = m₀.readW (tA L.tab (4 * j)) 32 ∧ ∀ q, q ≠ .lr → u'.gpr q = u.gpr q)
    (tabLd_ok hL hc (d := .lr) (by decide) (o := 4 * j) (by omega_using [hj]) fun u' c' m' v' k' =>
      WP.block_nil ⟨c', m', v', k'⟩) fun u' ⟨c', m', v', k'⟩ sy => ?_
  refine WP.frame_icalls_of_call (fun s₁ hp => ?_) (hf u' c' m' sy k')
  obtain ⟨g₁, y₁⟩ := push_some_gpr hp
  refine ⟨_, rfl, ?_⟩
  show s₁.gpr .lr |>.setWidth 64 |> fun a => (ts.find? fun p => (s₁.syms p.1).setWidth 64 == a) = some (n, c)
  simp only [g₁, y₁, v', hw, sy]
  exact ht

/-! ## HMAC's `init` -/

/-- The key `K`: the first `D` bytes of the frame. -/
abbrev keyOf (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) : List Byte :=
  Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 24) P.F.H.D

/-- HMAC's states for the key `K` in the frame on entry `t`, the inner one
holding `text` after its block of key. -/
structure St (P : RfcHash) {dn : Nat} (L : Lay dn) (g : Reg → BitVec 32) (m₀ : Mem) (t : State)
    (text : List Byte) (u : State) : Prop where
  ctx : Ctx L g m₀ u
  r9 : u.gpr .r9 = t.gpr .r9
  frame : Frame [WK L, ⟨L.B, 24⟩] t.mem u.mem
  inner : P.ok.hH.SH.Repr u.mem (State.addr (L.scr + BitVec.ofNat 32 0))
    (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.ok.hH.SH.H (keyOf P L t.mem)) Spec.Hmac.ipad ++ text)
  outer : P.ok.hH.SH.Repr u.mem (State.addr (L.scr + BitVec.ofNat 32 192))
    (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.ok.hH.SH.H (keyOf P L t.mem)) Spec.Hmac.opad)

/-- The arguments of HMAC's `init`. -/
theorem initArgs_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.initArgs) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧
      t'.gpr .r0 = L.scr + BitVec.ofNat 32 0 ∧ t'.gpr .r1 = L.scr + BitVec.ofNat 32 192 ∧
      t'.gpr .r2 = L.fp + BitVec.ofNat 32 0 ∧ t'.gpr .r3 = BitVec.ofNat 32 P.F.H.D ∧
      t'.gpr .r12 = L.scr + BitVec.ofNat 32 384 ∧ t'.gpr .r9 = t.gpr .r9 := by
  simp only [Cfg.initArgs, List.append_assoc, List.cons_append, List.nil_append]
  refine scrAt_ok hc (d := .r0) (by decide) (o := sInner) (by decide) fun t₁ c₁ m₁ v₁ k₁ => ?_
  refine scrAt_ok c₁ (d := .r1) (by decide) (o := sOuter) (by decide) fun t₂ c₂ m₂ v₂ k₂ => ?_
  refine fpAdd_ok c₂ (d := .r2) (by decide) (o := fK) (by decide) fun t₃ c₃ m₃ v₃ k₃ => ?_
  refine ldD_ok hL c₃ (d := .r3) (by decide) fun t₄ c₄ m₄ v₄ k₄ => ?_
  rw [← List.append_nil (scrAt .r12 sWork)]
  refine scrAt_ok c₄ (d := .r12) (by decide) (o := sWork) (by decide) fun t₅ c₅ m₅ v₅ k₅ => ?_
  refine WP.block_nil ⟨c₅, by rw [m₅, m₄, m₃, m₂, m₁], ?_, ?_, ?_, ?_, v₅, ?_⟩
  · rw [k₅ _ (by decide) (by decide), k₄ _ (by decide), k₃ _ (by decide), k₂ _ (by decide) (by decide)]
    exact v₁
  · rw [k₅ _ (by decide) (by decide), k₄ _ (by decide), k₃ _ (by decide)]
    exact v₂
  · rw [k₅ _ (by decide) (by decide), k₄ _ (by decide)]
    exact v₃
  · rw [k₅ _ (by decide) (by decide), v₄, hT.1]
  · rw [k₅ _ (by decide) (by decide), k₄ _ (by decide), k₃ _ (by decide), k₂ _ (by decide) (by decide),
      k₁ _ (by decide) (by decide)]

/-- The arguments of HMAC's `init`, as its frame needs them. -/
theorem initA (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (h0 : u.gpr .r0 = L.scr + BitVec.ofNat 32 0)
    (h1 : u.gpr .r1 = L.scr + BitVec.ofNat 32 192) (h2 : u.gpr .r2 = L.fp + BitVec.ofNat 32 0)
    (h3 : u.gpr .r3 = BitVec.ofNat 32 P.F.H.D) (h12 : u.gpr .r12 = L.scr + BitVec.ofNat 32 384) :
    HiArgs P.ok.hH.SH P.ok.Wi u (L.scr + BitVec.ofNat 32 0) (L.scr + BitVec.ofNat 32 192)
      (L.fp + BitVec.ofNat 32 0) (L.scr + BitVec.ofNat 32 384) P.F.H.D := by
  obtain e0 := scrA hL (o := 0) (by decide)
  obtain e1 := scrA hL (o := 192) (by decide)
  obtain e3 := scrA hL (o := 384) (by decide)
  obtain ek := hL.fpA (o := 0) (by omega_arith)
  obtain hst := hc.stk_eq hL
  have := hL.nc; have := hL.nB; have := L.sp.isLt
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hS, _, hB⟩ := P.sizes
  exact
    { r0 := h0, r1 := h1, r2 := h2, r3 := h3, r12 := h12
      klB := by rw [hB]; anums
      kl32 := by anums
      sp := hc.sp24 hL
      cr := hc.covers fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [ek]; exact ⟨L.FR, by simp, within_fr _ (by omega_arith) (by anums)⟩
      cw := hc.coversW fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [e0]; exact ⟨L.SCR, by simp, within_off _ (by anums)⟩
        · rw [e1]; exact ⟨L.SCR, by simp, within_off _ (by anums)⟩
        · rw [e3]; exact ⟨L.SCR, by simp, within_off _ (by anums)⟩
      i_o := by rw [e0, e1]; exact Offset.disjoint _ (by anums) (by anums) (by anums)
      i_k := by rw [e0, ek]; exact (hL.stk_scr (by anums) (by anums)).symm
      i_s := by rw [e0, e3]; exact Offset.disjoint _ (by anums) (by anums) (by anums)
      o_k := by rw [e1, ek]; exact (hL.stk_scr (by anums) (by anums)).symm
      o_s := by rw [e1, e3]; exact Offset.disjoint _ (by anums) (by anums) (by anums)
      k_s := by rw [ek, e3]; exact hL.stk_scr (by anums) (by anums)
      b_i := by rw [hst, e0]; exact low_scr hL (by omega_arith) (by anums)
      b_o := by rw [hst, e1]; exact low_scr hL (by omega_arith) (by anums)
      b_k := by rw [hst, ek]; exact Offset.base_disjoint _ (by omega_arith) (by anums)
      b_s := by rw [hst, e3]; exact low_scr hL (by omega_arith) (by anums)
      ni := by rw [scr_toNat hL (by decide)]; anums
      no := by rw [scr_toNat hL (by decide)]; anums
      nk := by rw [fp_toNat hL (by omega_arith)]; anums
      nsc := by rw [scr_toNat hL (by decide)]; anums }

/-- HMAC's states for the key `K`, by the table's `init`. -/
theorem init_step (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).initK t (St P L g m₀ t []) := by
  refine WP.seq (WP.mono (initArgs_ok hL hT hc) fun u ⟨hcu, hmu, h0, h1, h2, h3, h12, h9⟩ => ?_)
  obtain hok : TabOK P.F P.f u.syms := hT.1 ▸ hT.2 ▸ hcu.tabOk
  refine tcall_ok hL hcu (j := 0) (by decide) (n := P.F.hiN) (c := P.F.hiC)
    (by rw [show 4 * 0 = 0 from rfl, ← hT.1]; exact hcu.tabMem.1) hok.i
    fun u₁ c₁ m₁ y₁ k₁ => ?_
  apply WP.of_syms
  refine hi_frame P.ok.hi P.ok.hiSt (initA hL c₁ (by rw [k₁ _ (by decide)]; exact h0)
    (by rw [k₁ _ (by decide)]; exact h1) (by rw [k₁ _ (by decide)]; exact h2)
    (by rw [k₁ _ (by decide)]; exact h3) (by rw [k₁ _ (by decide)]; exact h12)) fun u' ha hi ho sy => ?_
  obtain ek : Spec.Sha256.bytesAt u₁.mem (State.addr (L.fp + BitVec.ofNat 32 0)) P.F.H.D = keyOf P L t.mem := by
    rw [hL.fpA (by omega_arith), m₁, hmu]
  obtain hws : ∀ r ∈ HiArgs.wr P.ok.hH.SH P.ok.Wi (L.scr + BitVec.ofNat 32 0) (L.scr + BitVec.ofNat 32 192)
      (L.scr + BitVec.ofNat 32 384), Region.Sub r (WK L) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> exact scr_wk hL (by decide) (by anums)
  refine ⟨c₁.after hL ha (fun r hr => wk_safe (hws r hr)) sy,
    by rw [ha.cs .r9 (by decide) (by decide), k₁ _ (by decide), h9],
    by rw [← hmu, ← m₁]; exact after_frame hL c₁ ha hws,
    by rw [← ek, List.append_nil]; exact hi, by rw [← ek]; exact ho⟩

/-! ## The streaming `update` -/

/-- Where the data may be: in the frame below `T`'s end, or in `scratch`
above HMAC's working space. -/
def DataOk {dn : Nat} (L : Lay dn) (da : BitVec 32) (len : Nat) : Prop :=
  (∃ o, da = L.fp + BitVec.ofNat 32 o ∧ o + len ≤ 464) ∨
    (∃ o, da = L.scr + BitVec.ofNat 32 o ∧ 2256 ≤ o ∧ o + len < 8192)

namespace DataOk

variable {da : BitVec 32} {len : Nat}

theorem addr (hd : DataOk L da len) (hL : L.Ok) :
    (∃ o, State.addr da = L.B + BitVec.ofNat 64 o ∧ 24 ≤ o ∧ o + len ≤ 488) ∨
      (∃ o, State.addr da = State.addr L.scr + BitVec.ofNat 64 o ∧ 2256 ≤ o ∧ o + len ≤ 8192) := by
  rcases hd with ⟨o, rfl, h⟩ | ⟨o, rfl, h₁, h₂⟩
  · exact .inl ⟨24 + o, hL.fpA (by omega_arith), by omega_arith, by omega_arith⟩
  · exact .inr ⟨o, scrA hL (by omega_arith), h₁, by omega_arith⟩

theorem nowrap (hd : DataOk L da len) (hL : L.Ok) : da.toNat + len ≤ 2 ^ 32 := by
  have := hL.nc; have := hL.nB; have := L.sp.isLt; have := hL.na
  rcases hd with ⟨o, rfl, h⟩ | ⟨o, rfl, h₁, h₂⟩
  · rw [fp_toNat hL (by omega_arith)]; omega_arith
  · rw [scr_toNat hL (by omega_arith)]; omega_arith

theorem low (hd : DataOk L da len) (hL : L.Ok) : Region.Disjoint ⟨L.B, 24⟩ ⟨State.addr da, len⟩ := by
  rcases hd.addr hL with ⟨o, e, h₁, h₂⟩ | ⟨o, e, h₁, h₂⟩ <;> rw [e]
  · exact Offset.base_disjoint _ h₁ (by omega_arith)
  · exact low_scr hL (by omega_arith) h₂

/-- The data is apart from HMAC's states and working space. -/
theorem work (hd : DataOk L da len) (hL : L.Ok) {e k : Nat} (h : e + k ≤ 2256) :
    Region.Disjoint ⟨State.addr da, len⟩ ⟨State.addr L.scr + BitVec.ofNat 64 e, k⟩ := by
  rcases hd.addr hL with ⟨o, e', h₁, h₂⟩ | ⟨o, e', h₁, h₂⟩ <;> rw [e']
  · exact hL.stk_scr (by omega_arith) (by omega_arith)
  · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)

theorem within (hd : DataOk L da len) (hL : L.Ok) :
    ∃ R ∈ [L.D, L.DG, L.FR, L.OUT, L.SCR], Within ⟨State.addr da, len⟩ R := by
  rcases hd.addr hL with ⟨o, e, h₁, h₂⟩ | ⟨o, e, h₁, h₂⟩ <;> rw [e]
  · exact ⟨L.FR, by simp, within_fr _ h₁ (by omega_arith)⟩
  · exact ⟨L.SCR, by simp, within_off _ h₂⟩

end DataOk

theorem xorPad_length (k : List Byte) (p : Byte) : (Spec.Hmac.xorPad k p).length = k.length :=
  List.length_map _

theorem blockKey_length {k : List Byte} (hk : k.length = P.F.H.D) :
    (Spec.Hmac.blockKey P.ok.hH.SH.H k).length = P.F.H.B := by
  obtain ⟨_, _, _, _, _, _, _, hDB, _, _, _, _, hB⟩ := P.sizes
  simp only [Spec.Hmac.blockKey, hk, hB, show ¬ P.F.H.B < P.F.H.D by omega_arith, ite_false, List.length_append,
    List.length_replicate]
  omega_arith

theorem keyOf_length (m : Mem) : (keyOf P L m).length = P.F.H.D := by simp [keyOf, Spec.Sha256.bytesAt]

theorem append_zero {k : Nat} (hk : k < 2 ^ 32) : (0 : BitVec 32) ++ BitVec.ofNat 32 k = BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_append, BitVec.toNat_ofNat, show (0 : BitVec 32).toNat = 0 from rfl,
    Nat.zero_shiftLeft, Nat.zero_or]
  omega_arith

/-- The arguments of the streaming `update`, as its frame needs them. -/
theorem updA (hL : L.Ok) {w : State} (hcw : Ctx L g m₀ w) {da : BitVec 32} {len : Nat} (hd : DataOk L da len)
    (hlen : len ≤ 256)
    (h0 : w.gpr .r0 = L.scr + BitVec.ofNat 32 0) (h1 : w.gpr .r1 = da)
    (h7 : w.gpr .r7 = BitVec.ofNat 32 len) (h10 : w.gpr .r10 = L.scr + BitVec.ofNat 32 384) :
    UpdL P.ok.hH w (L.scr + BitVec.ofNat 32 0) da (L.scr + BitVec.ofNat 32 384) len := by
  obtain e0 := scrA hL (o := 0) (by decide)
  obtain e3 := scrA hL (o := 384) (by decide)
  obtain hb := hcw.below_eq hL
  obtain hn := hd.nowrap hL
  have := hL.nc
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hS, _, hB⟩ := P.sizes
  obtain bsub : Region.Sub ⟨L.B + BitVec.ofNat 64 8, 16⟩ ⟨L.B, 24⟩ := Offset.sub_base _ (by omega_arith)
  exact
    { r0 := h0, r1 := h1, r7 := h7, r10 := h10
      hlen := by omega_arith
      sp16 := by have := hcw.sp24 hL; omega_arith
      cd := hcw.covers fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hd.within hL
      cw := hcw.coversW fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [e0]; exact ⟨L.SCR, by simp, within_off _ (by anums)⟩
        · rw [e3]; exact ⟨L.SCR, by simp, within_off _ (by anums)⟩
      st_sc := by rw [e0, e3]; exact Offset.disjoint _ (by anums) (by anums) (by anums)
      d_st := by rw [e0]; exact hd.work hL (by anums)
      d_sc := by rw [e3]; exact hd.work hL (by anums)
      b_st := by rw [hb, e0]; exact (low_scr hL (by omega_arith) (by anums)).sub_left bsub
      b_d := by rw [hb]; exact (hd.low hL).sub_left bsub
      b_sc := by rw [hb, e3]; exact (low_scr hL (by omega_arith) (by anums)).sub_left bsub
      nst := by rw [scr_toNat hL (by decide)]; anums
      nd := hn
      nsc := by rw [scr_toNat hL (by decide)]; anums }

/-- The table's `update` of the inner state with `len` bytes at `da`, from
the state its arguments leave (the count `B + |text|` in `r3:r2`). -/
theorem upd_call (hL : L.Ok) (hT : TabL P L) {t w : State} {text : List Byte} (hw : St P L g m₀ t text w)
    {da : BitVec 32} {len : Nat} (hd : DataOk L da len) (hlen : len ≤ 256)
    (h0 : w.gpr .r0 = L.scr + BitVec.ofNat 32 0) (h1 : w.gpr .r1 = da)
    (h2 : w.gpr .r2 = BitVec.ofNat 32 (P.F.H.B + text.length)) (h3 : w.gpr .r3 = 0)
    (h7 : w.gpr .r7 = BitVec.ofNat 32 len) (h10 : w.gpr .r10 = L.scr + BitVec.ofNat 32 384)
    (htl : P.F.H.B + text.length < 2 ^ 32) :
    WP isa (Cfg.tcall 1 P.f.upd upd4 .r1 16) w (St P L g m₀ t (text ++ Spec.Sha256.bytesAt w.mem (State.addr da) len)) := by
  have hcw := hw.ctx
  obtain hok : TabOK P.F P.f w.syms := hT.1 ▸ hT.2 ▸ hcw.tabOk
  refine tcall_ok hL hcw (j := 1) (by decide) (n := P.F.H.updN) (c := P.F.H.updC)
    (by rw [show 4 * 1 = 4 from rfl, ← hT.1]; exact hcw.tabMem.2.1) hok.u
    fun u₁ c₁ m₁ y₁ k₁ => ?_
  obtain hw₁ : St P L g m₀ t text u₁ :=
    ⟨c₁, by rw [k₁ _ (by decide)]; exact hw.r9, m₁ ▸ hw.frame, m₁ ▸ hw.inner, m₁ ▸ hw.outer⟩
  apply WP.of_syms
  refine upd_frame P.ok.hH (updA hL c₁ hd hlen (by rw [k₁ _ (by decide)]; exact h0)
    (by rw [k₁ _ (by decide)]; exact h1) (by rw [k₁ _ (by decide)]; exact h7)
    (by rw [k₁ _ (by decide)]; exact h10)) fun w' af hr sy => ?_
  obtain hws : ∀ r ∈ [(⟨State.addr (L.scr + BitVec.ofNat 32 0), P.F.H.S⟩ : Region),
      ⟨State.addr (L.scr + BitVec.ofNat 32 384), P.ok.hH.Wb⟩], Region.Sub r (WK L) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> exact scr_wk hL (by decide) (by anums)
  obtain hcount : Pbkdf2.Stream.Arm.count u₁ = BitVec.ofNat 64
      (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.ok.hH.SH.H (keyOf P L t.mem)) Spec.Hmac.ipad ++ text).length := by
    rw [Pbkdf2.Stream.Arm.count, k₁ _ (by decide), k₁ _ (by decide), h2, h3, List.length_append, xorPad_length,
      blockKey_length (keyOf_length _)]
    exact append_zero htl
  refine ⟨c₁.afterU hL af (fun r hr => wk_safe (hws r hr)) sy,
    by rw [af.cs .r9 (by decide) (by decide)]; exact hw₁.r9,
    hw₁.frame.trans (after_frameU hL c₁ af hws), ?_, ?_⟩
  · rw [← m₁, ← List.append_assoc]
    exact hr _ hw₁.inner hcount
  · refine P.ok.hH.repr u₁.mem w'.mem _ _ _ (fun i hi => ?_) hw₁.outer
    refine Frame.bytes (R := ⟨State.addr (L.scr + BitVec.ofNat 32 192), P.F.H.S⟩) af.frame (fun r hr => ?_)
      (by show P.F.H.S ≤ 2 ^ 64; anums) hi
    rw [scrA hL (by decide)] at hr ⊢
    rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (by anums) (by anums) (by anums)
      · rw [scrA hL (by decide)]; exact Offset.disjoint _ (by anums) (by anums) (by anums)
    · simp only [List.mem_singleton] at hr; subst hr
      rw [c₁.below_eq hL]
      exact ((low_scr hL (n := 24) (by omega_arith) (by anums)).sub_left (Offset.sub_base _ (by omega_arith))).symm

/-- `V`, of `D` bytes, in the frame. -/
abbrev vOf (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) : List Byte :=
  Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 88) P.F.H.D

/-- The inner state updated with `V`, the first text after the key. -/
theorem updV_step (hL : L.Ok) (hT : TabL P L) {t u : State} (hu : St P L g m₀ t [] u) :
    WP isa (cfgOf P).updV u (St P L g m₀ t (vOf P L u.mem)) := by
  unfold Cfg.updV
  have hc := hu.ctx
  simp only [Cfg.updVArgs, List.append_assoc, List.cons_append, List.nil_append]
  refine WP.seq ?_
  refine scrAt_ok hc (d := .r0) (by decide) (o := sInner) (by decide) fun t₁ c₁ m₁ v₁ k₁ => ?_
  refine fpAdd_ok c₁ (d := .r1) (by decide) (o := fV) (by decide) fun t₂ c₂ m₂ v₂ k₂ => ?_
  refine ldB_ok hL c₂ (d := .r2) (by decide) fun t₃ c₃ m₃ v₃ k₃ => ?_
  refine mov0_ok c₃ (d := .r3) (by decide) fun t₄ c₄ m₄ v₄ k₄ => ?_
  refine ldD_ok hL c₄ (d := .r7) (by decide) fun t₅ c₅ m₅ v₅ k₅ => ?_
  rw [← List.append_nil (scrAt .r10 sWork)]
  refine scrAt_ok c₅ (d := .r10) (by decide) (o := sWork) (by decide) fun t₆ c₆ m₆ v₆ k₆ => ?_
  refine WP.block_nil ?_
  obtain hm : t₆.mem = u.mem := by rw [m₆, m₅, m₄, m₃, m₂, m₁]
  obtain hv : State.addr (L.fp + BitVec.ofNat 32 64) = L.B + BitVec.ofNat 64 88 := hL.fpA (by omega_arith)
  obtain hw : St P L g m₀ t [] t₆ :=
    ⟨c₆, by rw [k₆ _ (by decide) (by decide), k₅ _ (by decide), k₄ _ (by decide), k₃ _ (by decide),
        k₂ _ (by decide), k₁ _ (by decide) (by decide)]; exact hu.r9,
      hm ▸ hu.frame, hm ▸ hu.inner, hm ▸ hu.outer⟩
  have := upd_call (P := P) hL hT hw (da := L.fp + BitVec.ofNat 32 64) (len := P.F.H.D)
    (.inl ⟨64, rfl, by anums⟩) (by anums)
    (by rw [k₆ _ (by decide) (by decide), k₅ _ (by decide), k₄ _ (by decide), k₃ _ (by decide),
      k₂ _ (by decide)]; exact v₁)
    (by rw [k₆ _ (by decide) (by decide), k₅ _ (by decide), k₄ _ (by decide), k₃ _ (by decide)]; exact v₂)
    (by rw [k₆ _ (by decide) (by decide), k₅ _ (by decide), k₄ _ (by decide), v₃, hT.1]; rfl)
    (by rw [k₆ _ (by decide) (by decide), k₅ _ (by decide)]; exact v₄)
    (by rw [k₆ _ (by decide) (by decide), v₅, hT.1]) v₆ (by simp only [List.length_nil]; anums)
  rw [hm, hv, List.nil_append] at this
  have e : (cfgOf P).f.upd = P.f.upd := rfl
  rw [e]; exact this

/-- Where the messages are. -/
abbrev msgA {dn : Nat} (L : Lay dn) : Addr := State.addr L.scr + BitVec.ofNat 64 2256

/-- The inner state updated with the message's `len` bytes, after `V`. -/
theorem updM_step (hL : L.Ok) (hT : TabL P L) {t u : State} {text : List Byte} (hu : St P L g m₀ t text u)
    (htl : text.length = P.F.H.D) {len : Nat} (hlen : len ≤ 256) :
    WP isa ((cfgOf P).updM len) u (St P L g m₀ t (text ++ Spec.Sha256.bytesAt u.mem (msgA L) len)) := by
  unfold Cfg.updM
  have hc := hu.ctx
  simp only [Cfg.updMArgs, List.append_assoc, List.cons_append, List.nil_append]
  refine WP.seq ?_
  refine scrAt_ok hc (d := .r0) (by decide) (o := sInner) (by decide) fun t₁ c₁ m₁ v₁ k₁ => ?_
  refine scrAt_ok c₁ (d := .r1) (by decide) (o := sMsg) (by decide) fun t₂ c₂ m₂ v₂ k₂ => ?_
  refine ldB_ok hL c₂ (d := .r2) (by decide) fun t₃ c₃ m₃ v₃ k₃ => ?_
  refine ldD_ok hL c₃ (d := .r3) (by decide) fun t₄ c₄ m₄ v₄ k₄ => ?_
  refine wp_dpS (op2_reg _ _) fun t₅ u₅ => ?_
  obtain c₅ := c₄.upd u₅ (by decide)
  refine mov0_ok c₅ (d := .r3) (by decide) fun t₆ c₆ m₆ v₆ k₆ => ?_
  refine movw_ok c₆ (d := .r7) (by decide) (v := len) (by omega_arith) fun t₇ c₇ m₇ v₇ k₇ => ?_
  rw [← List.append_nil (scrAt .r10 sWork)]
  refine scrAt_ok c₇ (d := .r10) (by decide) (o := sWork) (by decide) fun t₈ c₈ m₈ v₈ k₈ => ?_
  refine WP.block_nil ?_
  obtain hm : t₈.mem = u.mem := by rw [m₈, m₇, m₆, u₅.mem, m₄, m₃, m₂, m₁]
  obtain hmA : State.addr (L.scr + BitVec.ofNat 32 2256) = msgA L := scrA hL (by decide)
  obtain hw : St P L g m₀ t text t₈ :=
    ⟨c₈, by rw [k₈ _ (by decide) (by decide), k₇ _ (by decide), k₆ _ (by decide), u₅.other _ (by decide),
        k₄ _ (by decide), k₃ _ (by decide), k₂ _ (by decide) (by decide), k₁ _ (by decide) (by decide)]; exact hu.r9,
      hm ▸ hu.frame, hm ▸ hu.inner, hm ▸ hu.outer⟩
  obtain h2 : t₈.gpr .r2 = BitVec.ofNat 32 (P.F.H.B + text.length) := by
    rw [k₈ _ (by decide) (by decide), k₇ _ (by decide), k₆ _ (by decide), u₅.gpr, dpVal,
      k₄ _ (by decide), v₃, v₄, hT.1, htl, BitVec.ofNat_add]
  have := upd_call (P := P) hL hT hw (da := L.scr + BitVec.ofNat 32 2256) (len := len)
    (.inr ⟨2256, rfl, by omega_arith, by omega_arith⟩) hlen
    (by rw [k₈ _ (by decide) (by decide), k₇ _ (by decide), k₆ _ (by decide), u₅.other _ (by decide),
      k₄ _ (by decide), k₃ _ (by decide), k₂ _ (by decide) (by decide)]; exact v₁)
    (by rw [k₈ _ (by decide) (by decide), k₇ _ (by decide), k₆ _ (by decide), u₅.other _ (by decide),
      k₄ _ (by decide), k₃ _ (by decide)]; exact v₂)
    h2 (by rw [k₈ _ (by decide) (by decide), k₇ _ (by decide)]; exact v₆)
    (by rw [k₈ _ (by decide) (by decide)]; exact v₇) v₈ (by rw [htl]; anums)
  rw [hm, hmA] at this
  exact this

/-! ## HMAC's `finalize` -/

/-- After HMAC's `finalize`: the MAC of `text` in the frame at `dst`. -/
structure Done (P : RfcHash) {dn : Nat} (L : Lay dn) (g : Reg → BitVec 32) (m₀ : Mem) (t : State)
    (text : List Byte) (dst : Nat) (u : State) : Prop where
  ctx : Ctx L g m₀ u
  r9 : u.gpr .r9 = t.gpr .r9
  frame : Frame [WK L, ⟨L.B, 24⟩, ⟨L.B + BitVec.ofNat 64 (24 + dst), P.F.H.D⟩] t.mem u.mem
  mac : Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (24 + dst)) P.F.H.D = P.mac (keyOf P L t.mem) text

/-- The arguments of HMAC's `finalize`, as its frame needs them. -/
theorem finA (hL : L.Ok) {w : State} (hcw : Ctx L g m₀ w) {dst : Nat} (hdst : dst + P.F.H.D ≤ 128)
    (h0 : w.gpr .r0 = L.scr + BitVec.ofNat 32 0) (h1 : w.gpr .r1 = L.scr + BitVec.ofNat 32 192)
    (h10 : w.gpr .r10 = L.fp + BitVec.ofNat 32 dst) (h12 : w.gpr .r12 = L.scr + BitVec.ofNat 32 384) :
    HfArgs P.ok.hH.SH P.ok.Wf w (L.scr + BitVec.ofNat 32 0) (L.scr + BitVec.ofNat 32 192)
      (L.fp + BitVec.ofNat 32 dst) (L.scr + BitVec.ofNat 32 384) := by
  obtain e0 := scrA hL (o := 0) (by decide)
  obtain e1 := scrA hL (o := 192) (by decide)
  obtain e3 := scrA hL (o := 384) (by decide)
  obtain eo := hL.fpA (o := dst) (by omega_arith)
  obtain hst := hcw.stk_eq hL
  have := hL.nc; have := hL.nB; have := L.sp.isLt
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hS, hD, hB⟩ := P.sizes
  exact
    { r0 := h0, r1 := h1, r10 := h10, r12 := h12
      sp := hcw.sp24 hL
      cr := hcw.covers fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [e1]; exact ⟨L.SCR, by simp, within_off _ (by anums)⟩
      cw := hcw.coversW fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [e0]; exact ⟨L.SCR, by simp, within_off _ (by anums)⟩
        · rw [eo]; exact ⟨L.FR, by simp, within_fr _ (by omega_arith) (by anums)⟩
        · rw [e3]; exact ⟨L.SCR, by simp, within_off _ (by anums)⟩
      i_u := by rw [e0, e1]; exact Offset.disjoint _ (by anums) (by anums) (by anums)
      i_o := by rw [e0, eo]; exact (hL.stk_scr (by anums) (by anums)).symm
      i_s := by rw [e0, e3]; exact Offset.disjoint _ (by anums) (by anums) (by anums)
      u_o := by rw [e1, eo]; exact (hL.stk_scr (by anums) (by anums)).symm
      u_s := by rw [e1, e3]; exact Offset.disjoint _ (by anums) (by anums) (by anums)
      o_s := by rw [eo, e3]; exact hL.stk_scr (by anums) (by anums)
      b_i := by rw [hst, e0]; exact low_scr hL (by omega_arith) (by anums)
      b_u := by rw [hst, e1]; exact low_scr hL (by omega_arith) (by anums)
      b_o := by rw [hst, eo]; exact Offset.base_disjoint _ (by omega_arith) (by anums)
      b_s := by rw [hst, e3]; exact low_scr hL (by omega_arith) (by anums)
      ni := by rw [scr_toNat hL (by decide)]; anums
      nu := by rw [scr_toNat hL (by decide)]; anums
      no := by rw [fp_toNat hL (by omega_arith)]; anums
      nsc := by rw [scr_toNat hL (by decide)]; anums }

theorem reprOK : Proof.Pbkdf2.Whole.Arm.ReprOK P.ok.hH.SH := fun m m' p q msg hb =>
  P.ok.hH.repr m m' p q msg (fun i hi => hb i (by rw [P.ok.hH.hS]; exact hi))

/-- `HMAC(K₀, text)` to the frame at `dst`, for a text of `D + len` bytes. -/
theorem fin_step (hL : L.Ok) (hT : TabL P L) {t u : State} {text : List Byte} {len dst : Nat}
    (hu : St P L g m₀ t text u) (htl : text.length = P.F.H.D + len) (hlen : len ≤ 256)
    (hdst : dst + P.F.H.D ≤ 128) (he : encodable (BitVec.ofNat 32 dst) = true)
    (hle : encodable (BitVec.ofNat 32 len) = true) :
    WP isa ((cfgOf P).fin len dst) u (Done P L g m₀ t text dst) := by
  unfold Cfg.fin
  have hc := hu.ctx
  simp only [Cfg.finArgs, List.append_assoc, List.cons_append, List.nil_append]
  refine WP.seq ?_
  refine scrAt_ok hc (d := .r0) (by decide) (o := sInner) (by decide) fun t₁ c₁ m₁ v₁ k₁ => ?_
  refine scrAt_ok c₁ (d := .r1) (by decide) (o := sOuter) (by decide) fun t₂ c₂ m₂ v₂ k₂ => ?_
  refine ldB_ok hL c₂ (d := .r2) (by decide) fun t₃ c₃ m₃ v₃ k₃ => ?_
  refine ldD_ok hL c₃ (d := .r3) (by decide) fun t₄ c₄ m₄ v₄ k₄ => ?_
  refine wp_dpS (op2_reg _ _) fun t₅ u₅ => ?_
  obtain c₅ := c₄.upd u₅ (by decide)
  refine wp_dpS (op2_imm hle) fun t₆ u₆ => ?_
  obtain c₆ := c₅.upd u₆ (by decide)
  refine mov0_ok c₆ (d := .r3) (by decide) fun t₇ c₇ m₇ v₇ k₇ => ?_
  refine fpAdd_ok c₇ (d := .r10) (by decide) he fun t₈ c₈ m₈ v₈ k₈ => ?_
  rw [← List.append_nil (scrAt .r12 sWork)]
  refine scrAt_ok c₈ (d := .r12) (by decide) (o := sWork) (by decide) fun t₉ c₉ m₉ v₉ k₉ => ?_
  refine WP.block_nil ?_
  obtain hmm : t₉.mem = u.mem := by rw [m₉, m₈, m₇, u₆.mem, u₅.mem, m₄, m₃, m₂, m₁]
  obtain h2 : t₉.gpr .r2 = BitVec.ofNat 32 (P.F.H.B + text.length) := by
    rw [k₉ _ (by decide) (by decide), k₈ _ (by decide), k₇ _ (by decide), u₆.gpr, dpVal, u₅.gpr, dpVal,
      k₄ _ (by decide), v₃, v₄, hT.1, htl, BitVec.ofNat_add, BitVec.ofNat_add, BitVec.add_assoc]
  obtain h3 : t₉.gpr .r3 = 0 := by rw [k₉ _ (by decide) (by decide), k₈ _ (by decide)]; exact v₇
  obtain h9 : t₉.gpr .r9 = t.gpr .r9 := by
    rw [k₉ _ (by decide) (by decide), k₈ _ (by decide), k₇ _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), k₄ _ (by decide), k₃ _ (by decide), k₂ _ (by decide) (by decide),
      k₁ _ (by decide) (by decide)]; exact hu.r9
  obtain hok : TabOK P.F P.f t₉.syms := hT.1 ▸ hT.2 ▸ c₉.tabOk
  refine tcall_ok hL c₉ (j := 2) (by decide) (n := P.F.hfN) (c := P.F.hfC)
    (by rw [show 4 * 2 = 8 from rfl, ← hT.1]; exact c₉.tabMem.2.2) hok.f
    fun w c₁₀ m₁₀ y₁₀ k₁₀ => ?_
  apply WP.of_syms
  refine hf_frame reprOK (by anums) P.ok.hf P.ok.hfSt (finA hL c₁₀ hdst
    (by rw [k₁₀ _ (by decide), k₉ _ (by decide) (by decide), k₈ _ (by decide), k₇ _ (by decide),
      u₆.other _ (by decide), u₅.other _ (by decide), k₄ _ (by decide), k₃ _ (by decide),
      k₂ _ (by decide) (by decide)]; exact v₁)
    (by rw [k₁₀ _ (by decide), k₉ _ (by decide) (by decide), k₈ _ (by decide), k₇ _ (by decide),
      u₆.other _ (by decide), u₅.other _ (by decide), k₄ _ (by decide), k₃ _ (by decide)]; exact v₂)
    (by rw [k₁₀ _ (by decide), k₉ _ (by decide) (by decide)]; exact v₈)
    (by rw [k₁₀ _ (by decide)]; exact v₉)) fun w' ha hpost sy => ?_
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hS, hD, hB⟩ := P.sizes
  obtain eo := hL.fpA (o := dst) (by omega_arith)
  obtain hk := blockKey_length (P := P) (keyOf_length (L := L) t.mem)
  obtain hm := hpost _ text (by rw [hk, hB])
    (by rw [hk]; anums) (by rw [m₁₀, hmm]; exact hu.inner)
    (by rw [k₁₀ _ (by decide), k₁₀ _ (by decide), h3, h2, hB]; exact append_zero (by rw [htl]; anums))
    (by rw [m₁₀, hmm]; exact hu.outer)
  rw [eo, hD] at hm
  obtain hws : ∀ r ∈ HfArgs.wr P.ok.hH.SH P.ok.Wf (L.scr + BitVec.ofNat 32 0) (L.fp + BitVec.ofNat 32 dst)
      (L.scr + BitVec.ofNat 32 384) ++ [stk w], ∃ r' ∈ [WK L, ⟨L.B, 24⟩,
        (⟨L.B + BitVec.ofNat 64 (24 + dst), P.F.H.D⟩ : Region)], Region.Sub r r' := by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, c₁₀.stk_eq hL]
    rintro r (rfl | rfl | rfl | rfl)
    · exact ⟨WK L, by simp, scr_wk hL (by decide) (by anums)⟩
    · exact ⟨⟨L.B + BitVec.ofNat 64 (24 + dst), P.F.H.D⟩, by simp, by rw [eo, hD]; exact sub_refl _⟩
    · exact ⟨WK L, by simp, scr_wk hL (by decide) (by anums)⟩
    · exact ⟨⟨L.B, 24⟩, by simp, sub_refl _⟩
  refine ⟨c₁₀.keep hL ha.rd ha.wr ha.sp (fun r hr => ha.cs r (ptr_preserved r hr).1 (ptr_preserved r hr).2)
      ha.frame (fun r hr => ?_) sy, by rw [ha.cs .r9 (by decide) (by decide), k₁₀ _ (by decide), h9],
    (hu.frame.sub fun r hr => ⟨r, by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h],
      sub_refl _⟩).trans (by rw [← hmm, ← m₁₀]; exact ha.frame.sub hws), hm⟩
  obtain ⟨r', hr', hs⟩ := hws r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl
  · exact wk_safe hs
  · exact .inr (.inr (sub_trans hs (Region.sub_prefix (by omega_arith))))
  · exact .inr (.inr (sub_trans hs (Offset.sub_base _ (by anums))))

end VG.Proof.Ecdsa.Rfc6979.Arm

end

end

/-! ### `Ecdsa.Rfc6979.Arm.Wide`, which only this module used -/

section

/-!
# Deterministic ECDSA on 32-bit ARM: the shifts of P-521's numbers

For a `big` curve (P-521, whose 66-byte scalars are longer than every
digest): the `Q` bytes at an offset in the frame, shifted right in place
through the words at `scratch + 2560` (`conv_ok`, by `loadBytes_ok`,
`shrWords_ok` and `storeBytes_ok`, with `out` and `d` kept in `r2` and `r3`
meanwhile, as those use `r4` and `r5`), for `core`'s digest and the
candidate.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Proof.Mont (wordsVal Outside off ofs)
open VG.Proof.Mont.Arm (Scr)
open VG.Proof.X25519.Arm (Rest Upd wp_ldr wp_str wp_dp wp_mov wp_movw op2_reg op2_imm dpVal)
open VG.Proof.Weierstrass.Arm (loadBytes_ok shrWords_ok storeBytes_ok)

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

theorem frame_of_outside {base : Addr} {d n : Nat} {m m' : Mem} (h : Outside base d n m m')
    (hn : d + n ≤ 2 ^ 64) : Frame [⟨base + BitVec.ofNat 64 d, n⟩] m m' := fun x hx => h x (by
  obtain h₁ := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at h₁
  obtain h₂ := Offset.lt_iff x base hn
  simp only [ofs]
  omega_arith)

/-- `scratch`'s first 4096 bytes, as the conversions address them from `r12`. -/
theorem scr_of (hL : L.Ok) {t : State} (hwr : t.wr = [L.FR, L.OUT, L.SCR]) (h12 : t.gpr .r12 = L.scr) :
    Scr t (State.addr L.scr) 4096 :=
  ⟨by rw [h12], ⟨8192, by omega_arith, by omega_arith, by rw [hwr]; simp⟩, by have := hL.nc; rw [toNat_addr]; omega_arith,
    Nat.le_refl _⟩

theorem scr_keep {s s' : State} {base : Addr} {size : Nat} (h : Scr s base size) (h12 : s'.gpr .r12 = s.gpr .r12)
    (hwr : s'.wr = s.wr) : Scr s' base size :=
  ⟨h12 ▸ h.wb, hwr ▸ h.wr, h.nowrap, h.small⟩

theorem allOnes_movt : ((0xffff : BitVec 16) ++ ((0xffff : BitVec 16).setWidth 32).extractLsb' 0 16 : BitVec 32) =
    BitVec.allOnes 32 := by decide

/-- `conv o s`: the `Q` bytes at `r8 + o`, in the frame, shifted
right by `s` bits in place, through the words at `scratch + 2560`. -/
theorem conv_ok (hL : L.Ok) (hW : P.R.big = true) {t : State} (hc : Ctx L g m₀ t)
    {o s : Nat} (ho₁ : 192 ≤ o) (ho₂ : o + 72 ≤ 468) (hoe : encodable (BitVec.ofNat 32 o) = true) (hs₁ : 1 ≤ s)
    (hs₂ : s < 32) :
    WP isa (.block ((cfgOf P).conv o s)) t fun t' => Ctx L g m₀ t' ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r10 → r ≠ .r12 → t'.gpr r = t.gpr r) ∧
      Frame [⟨State.addr L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 (24 + o), P.Q⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 (24 + o)) P.Q =
        Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 (24 + o)) P.Q) >>> s) := by
  apply WP.of_syms
  obtain ⟨hw9, hQ66, -, -⟩ := P.sizesW hW
  have nB := hL.nB
  have nc := hL.nc
  obtain hfp : L.fp.toNat = L.sp.toNat - 512 := VG.Arm.FrameStack.sub_toNat' (by omega_arith)
  have := hL.na
  have := L.sp.isLt
  obtain hw2 : (cfgOf P).w / 2 = P.w := by simp only [cfgOf, show P.R.E.C.len = 66 from hQ66, show P.w = 9 from hw9]; decide
  have hlen : (cfgOf P).len = P.Q := rfl
  simp only [Cfg.conv, hw2, hlen, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_movS (op2_reg _ _) fun u₁ v₁ => wp_movS (op2_reg _ _) fun u₂ v₂ => ?_
  refine wp_dpS (op2_imm hoe) fun u₃ v₃ => wp_movS (op2_reg _ _) fun u₄ v₄ => ?_
  obtain K₄ : Rest [.r1, .r2, .r3, .r12] t u₄ :=
    (v₁.rest (by simp)).trans <| (v₂.rest (by simp)).trans <| (v₃.rest (by simp)).trans (v₄.rest (by simp))
  obtain h12 : u₄.gpr .r12 = L.scr := by
    rw [v₄.gpr, v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide), hc.r11]
  obtain hS₄ : Scr u₄ (State.addr L.scr) 4096 := scr_of hL (by rw [K₄.wr, hc.wr]) h12
  obtain hr1 : u₄.gpr .r1 = L.fp + BitVec.ofNat 32 o := by
    rw [v₄.other _ (by decide), v₃.gpr, dpVal, v₂.other _ (by decide), v₁.other _ (by decide), hc.r8]
  obtain ha₁ : State.addr (L.fp + BitVec.ofNat 32 o) = L.B + BitVec.ofNat 64 (24 + o) := hL.fpA (by omega_arith)
  rw [WP.block_append_iff]
  refine WP.mono (loadBytes_ok hS₄ (len := P.Q) (n := P.w) (o := 2560) (src := .r1) (by decide) (by omega_arith)
    (by rw [hr1, fp_toNat hL (by omega_arith)]; omega_arith) (by omega_arith) (by omega_arith)
    (fun d hd => by rw [hr1, ha₁, Offset.add_add, K₄.rd, K₄.wr]; exact hc.inFr (by omega_arith) (by omega_arith))
    (by rw [hr1, ha₁]; exact (hL.stk_scr (by omega_arith) (by omega_arith)))) fun u₅ ⟨hv₅, k₅, O₅⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (shrWords_ok (scr_keep hS₄ (k₅.gpr _ (by decide)) k₅.wr) (n := P.w) (o := 2560) (sh := s)
    (by omega_arith) hs₁ hs₂) fun u₆ ⟨hv₆, k₆, O₆⟩ => ?_
  refine wp_movwS fun u₇ v₇ => wp_movt fun u₈ v₈ => ?_
  obtain h10 : u₈.gpr .r10 = BitVec.allOnes 32 := by rw [v₈.gpr, v₇.gpr]; exact allOnes_movt
  obtain K₈ : Rest [.r4, .r5, .r10] u₅ u₈ :=
    (k₆.mono (by simp)).trans <| (v₇.rest (by simp)).trans (v₈.rest (by simp))
  obtain hS₈ : Scr u₈ (State.addr L.scr) 4096 := scr_keep hS₄
    (by rw [K₈.gpr _ (by decide), k₅.gpr _ (by decide)]) (by rw [K₈.wr, k₅.wr])
  obtain h8 : u₈.gpr .r8 = L.fp := by rw [K₈.gpr _ (by decide), k₅.gpr _ (by decide), K₄.gpr _ (by decide), hc.r8]
  obtain hdst : State.addr (u₈.gpr .r8) + BitVec.ofNat 64 o = L.B + BitVec.ofNat 64 (24 + o) := by
    rw [h8, hL.fpA0, Offset.add_add]
  rw [WP.block_append_iff]
  refine WP.mono (storeBytes_ok hS₈ (len := P.Q) (n := P.w) (d := o) (a := 2560) (dst := .r8) (by decide)
    (by decide) true (by rw [h10]; rfl) (by omega_arith) (by omega_arith) (by omega_arith) (by rw [h8]; omega_arith) (by omega_arith)
    (fun e m hem => by
      rw [hdst, Offset.add_add, K₈.wr, k₅.wr, K₄.wr]; exact hc.inFrW (by omega_arith) (by omega_arith))
    (by rw [hdst]; exact (hL.stk_scr (by omega_arith) (by omega_arith)).symm)) fun u₉ ⟨hb₉, k₉, O₉⟩ => ?_
  rw [hdst] at hb₉ O₉
  refine wp_movS (op2_reg _ _) fun u₁₀ v₁₀ => wp_movS (op2_reg _ _) fun u₁₁ v₁₁ => WP.block_nil (fun sy => ?_)
  -- Through the conversion, every register but those it writes.
  obtain K : ∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r10 → r ≠ .r12 →
      u₉.gpr r = t.gpr r := fun r h1 h2 h3 h4 h5 h10' h12' => by
    rw [k₉.gpr _ (by simp [h4, h5]), K₈.gpr _ (by simp [h4, h5, h10']), k₅.gpr _ (by simp [h4]),
      K₄.gpr _ (by simp [h1, h2, h3, h12'])]
  obtain hr2 : u₉.gpr .r2 = t.gpr .r4 := by
    rw [k₉.gpr _ (by decide), K₈.gpr _ (by decide), k₅.gpr _ (by decide), v₄.other _ (by decide),
      v₃.other _ (by decide), v₂.other _ (by decide), v₁.gpr]
  obtain hr3 : u₉.gpr .r3 = t.gpr .r5 := by
    rw [k₉.gpr _ (by decide), K₈.gpr _ (by decide), k₅.gpr _ (by decide), v₄.other _ (by decide),
      v₃.other _ (by decide), v₂.gpr, v₁.other _ (by decide)]
  obtain hg : ∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r10 → r ≠ .r12 → u₁₁.gpr r = t.gpr r :=
    fun r h1 h2 h3 h10' h12' => by
      by_cases h4 : r = .r4
      · subst h4; rw [v₁₁.other _ (by decide), v₁₀.gpr, hr2]
      by_cases h5 : r = .r5
      · subst h5; rw [v₁₁.gpr, v₁₀.other _ (by decide), hr3]
      rw [v₁₁.other _ h5, v₁₀.other _ h4, K r h1 h2 h3 h4 h5 h10' h12']
  obtain m₄ : u₄.mem = t.mem := by rw [v₄.mem, v₃.mem, v₂.mem, v₁.mem]
  obtain m₈ : u₈.mem = u₆.mem := by rw [v₈.mem, v₇.mem]
  obtain hm : u₁₁.mem = u₉.mem := by rw [v₁₁.mem, v₁₀.mem]
  -- What changed: the words at `scratch + 2560`, and the bytes converted.
  obtain hf : Frame [⟨State.addr L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 (24 + o), P.Q⟩]
      t.mem u₁₁.mem := by
    obtain f₅ := frame_of_outside (O₅.trans O₆) (by omega_arith)
    obtain f₉ := frame_of_outside O₉ (by omega_arith)
    rw [BitVec.add_zero, m₈] at f₉
    rw [show 8 * P.w = 72 by omega_arith, m₄] at f₅
    rw [hm]
    exact (f₅.sub fun r hr => ⟨r, by simp_all, sub_refl _⟩).trans (f₉.sub fun r hr => ⟨r, by simp_all, sub_refl _⟩)
  obtain hp : ∀ r ∈ ptrRegs, r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r10 ∧ r ≠ .r12 := by decide
  refine ⟨hc.keep hL (by rw [v₁₁.rd, v₁₀.rd, k₉.rd, K₈.rd, k₅.rd, K₄.rd])
      (by rw [v₁₁.wr, v₁₀.wr, k₉.wr, K₈.wr, k₅.wr, K₄.wr]) (by rw [v₁₁.sp, v₁₀.sp, k₉.sp, K₈.sp, k₅.sp, K₄.sp])
      (fun r hr => hg r (hp r hr).1 (hp r hr).2.1 (hp r hr).2.2.1 (hp r hr).2.2.2.1 (hp r hr).2.2.2.2) hf
      (fun r hr => ?_) sy, hg, hf, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact safe_scr L (by omega_arith)
    · exact safe_low L (by omega_arith)
  · rw [ecdsa_bytesAt] at hb₉
    simp only [ite_true] at hb₉
    rw [hm, hb₉, m₈, hv₆, hv₅, hr1, ha₁, ecdsa_bytesAt, m₄]

end VG.Proof.Ecdsa.Rfc6979.Arm

end

end


/-!
# Deterministic ECDSA on 32-bit ARM: the digest into `X`

The byte loop `copyLoop` (`Proof/AesGcm/Arm/Loops.lean`), `r3` bytes from
`r1` to `r2` with `Ctx` kept, for a destination the code may write apart
from the source (`cp_ok`); zero words in the frame (`zeroN_ok`); and `X`
(`prepX_ok`): `Q - m` zero bytes, then the digest's first `m = min(D, Q)`,
its length the smaller of the table's `D` and `Q`, computed without a branch
(`min_ok`: `Q + ((D - Q) & mask)`, the mask all ones iff `D - Q` borrows).
If `big`, `core`'s digest (`prepC_ok`): `Q - 1 - D` zero bytes, the digest
and a zero byte, shifted right by `8 - sh` bits, which is the digest's
integer shifted left by `sh` bits.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Impl.AesGcm.Arm (copyLoop imm)
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_str op2_reg op2_imm dpVal)

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

/-! ## A byte loop -/

/-- `n` bytes from `q` (`r1`) to `p` (`r2`), `n` in `r3`, by `copyLoop`:
`Ctx` kept, for a destination the code may write apart from the source. -/
theorem cp_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {p q : BitVec 32} {n : Nat} (hn : 0 < n)
    (hn' : n < 2 ^ 32) (h1 : u.gpr .r1 = q) (h2 : u.gpr .r2 = p) (h3 : u.gpr .r3 = BitVec.ofNat 32 n)
    (fq : q.toNat + n ≤ 2 ^ 32) (fp : p.toNat + n ≤ 2 ^ 32)
    (hr : ∃ R ∈ [L.D, L.DG, L.FR, L.OUT, L.SCR], Within ⟨State.addr q, n⟩ R)
    (hw : ∃ R ∈ [L.FR, L.OUT, L.SCR], Within ⟨State.addr p, n⟩ R) (hs : Safe L ⟨State.addr p, n⟩)
    (hd : (⟨State.addr q, n⟩ : Region).Disjoint ⟨State.addr p, n⟩) :
    WP isa copyLoop u fun u' => Ctx L g m₀ u' ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → u'.gpr r = u.gpr r) ∧
      Frame [⟨State.addr p, n⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (State.addr p) n = Spec.Sha256.bytesAt u.mem (State.addr q) n := by
  obtain pre : VG.Proof.AesGcm.Arm.LoopPre u q p n :=
    ⟨h1, h2, h3, hn, hn', fq, fp, hc.covers fun r hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'; exact hr,
      hc.coversW fun r hr' => by simp only [List.mem_singleton] at hr'; subst hr'; exact hw, hd⟩
  refine WP.mono_syms (VG.Proof.AesGcm.Arm.copyLoop_ok u pre) fun u' ⟨hm, O⟩ sy => ?_
  obtain hlen : (Spec.Aes.bytesAt u.mem (State.addr q) n).length = n := by simp [Spec.Aes.bytesAt]
  obtain hf : Frame [⟨State.addr p, n⟩] u.mem u'.mem := by
    rw [hm]
    exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [hlen]; exact Region.contains_self _ _)
  obtain hp : ∀ r ∈ ptrRegs, r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by decide
  refine ⟨hc.keep hL O.rd O.wr O.sp (fun r hr' => O.other r (hp r hr').1 (hp r hr').2.1 (hp r hr').2.2.1
      (hp r hr').2.2.2.1 (hp r hr').2.2.2.2) hf
      (fun r hr' => by simp only [List.mem_singleton] at hr'; subst hr'; exact hs) sy,
    O.other, hf, ?_⟩
  rw [hm]
  have := Proof.Hmac.Common.bytesAt_writeBytes_self u.mem (State.addr p) (Spec.Aes.bytesAt u.mem (State.addr q) n)
    (by rw [hlen]; omega_arith)
  rw [hlen] at this
  exact this

/-! ## Zero words in the frame -/

theorem zeroN_raw (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {o : Nat} (h0 : u.gpr .r0 = 0) : ∀ k, o + 4 * k ≤ 468 →
    WP isa (.block ((List.range k).map fun j => .str .r0 .r8 (o + 4 * j))) u
      fun u' => u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧ u'.gpr = u.gpr ∧
        Frame [⟨L.B + BitVec.ofNat 64 (24 + o), 4 * k⟩] u.mem u'.mem ∧
        ∀ j < k, u'.mem.readW (L.B + BitVec.ofNat 64 (24 + o + 4 * j)) 32 = 0
  | 0, _ => WP.block_nil ⟨rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | k + 1, hk => by
    rw [List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (zeroN_raw hL hc h0 k (by omega_arith)) fun u₁ ⟨hrd, hwr, hsp, hg, hf, hv⟩ => ?_
    obtain e₁ : State.addr (L.fp + BitVec.ofNat 32 (o + 4 * k)) = L.B + BitVec.ofNat 64 (24 + o + 4 * k) := by
      rw [hL.fpA (by omega_arith), Nat.add_assoc]
    refine wp_strS (a := L.B + BitVec.ofNat 64 (24 + o + 4 * k)) (by omega_arith) (by rw [hg, hc.r8]; exact e₁)
      (by rw [hwr]; exact hc.inFrW (by omega_arith) (by omega_arith)) fun u₂ v₂ => WP.block_nil ?_
    obtain sep : ∀ x y, x + 4 ≤ y ∨ y + 4 ≤ x → x + 4 ≤ 536 → y + 4 ≤ 536 →
        Mem.Sep (L.B + BitVec.ofNat 64 x) (32 / 8) (L.B + BitVec.ofNat 64 y) (32 / 8) :=
      fun x y h h₁ h₂ => Offset.sep _ h (by omega_arith) (by omega_arith)
    obtain hm₂ : u₂.mem = u₁.mem.writeW (L.B + BitVec.ofNat 64 (24 + o + 4 * k)) (0 : BitVec 32) := by
      rw [v₂.mem, hg, h0]
    refine ⟨by rw [v₂.rd, hrd], by rw [v₂.wr, hwr], by rw [v₂.sp, hsp], by rw [v₂.gpr, hg], ?_, fun j hj => ?_⟩
    · refine (hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans ?_
      · simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega_arith)
      · rw [hm₂]
        exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
          (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))
    · rw [hm₂]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [Mem.readW_writeW_sep (sep _ _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
        exact hv j hj
      · rw [Mem.readW_writeW_self32]

/-- `k` zero words at the frame's `o`, through `r0`: their bytes are zero. -/
theorem zeroN_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {k o : Nat} (ho : o + 4 * k ≤ 468) :
    WP isa (.block (Cfg.zeroN k o)) u fun u' => Ctx L g m₀ u' ∧ (∀ r, r ≠ .r0 → u'.gpr r = u.gpr r) ∧
      Frame [⟨L.B + BitVec.ofNat 64 (24 + o), 4 * k⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (24 + o)) (4 * k) = List.replicate (4 * k) 0 := by
  rw [Cfg.zeroN]
  refine wp_movS (op2_imm (by decide)) fun u₁ v₁ => ?_
  obtain hc₁ := hc.upd v₁ (by decide)
  refine WP.mono_syms (zeroN_raw hL hc₁ (o := o) v₁.gpr k ho) fun u' ⟨hrd, hwr, hsp, hg, hf, hv⟩ sy => ?_
  refine ⟨hc₁.keep hL hrd hwr hsp (fun r _ => by rw [hg]) hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by omega_arith)) sy,
    fun r hr => by rw [hg, v₁.other _ hr], by rw [← v₁.mem]; exact hf, ?_⟩
  rw [bytesAt_of_readW _ _ (0 : BitVec 32) fun j hj => by rw [Offset.add_add]; exact hv j hj]
  exact List.eq_replicate_iff.mpr ⟨by simp, fun b hb => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hb; simp⟩

/-! ## `X` -/

theorem min_val (D Q : Nat) (hD : D < 2 ^ 32) (hQ : Q < 2 ^ 32) :
    BitVec.ofNat 32 Q + ((BitVec.ofNat 32 D - BitVec.ofNat 32 Q) &&&
      (0#32 + 0#32 + (if decide ((BitVec.ofNat 32 Q).toNat ≤ (BitVec.ofNat 32 D).toNat) = true then 1 else 0) -
        1#32)) = BitVec.ofNat 32 (min D Q) := by
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hD, Nat.mod_eq_of_lt hQ]
  by_cases h : Q ≤ D
  · simp only [h, decide_true, ↓reduceIte, Nat.min_eq_right h]
    rw [show (0#32 + 0#32 + 1 - 1#32 : BitVec 32) = 0#32 by decide, BitVec.and_zero, BitVec.add_zero]
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, Nat.min_eq_left (by omega_arith : D ≤ Q)]
    rw [show (0#32 + 0#32 + 0 - 1#32 : BitVec 32) = BitVec.allOnes 32 by decide, BitVec.and_allOnes,
      BitVec.add_comm, BitVec.sub_add_cancel]

/-- `r3 = min(D, Q)` (`r0 = Q` and `r7`, `r12` changed). -/
theorem min_ok (hL : L.Ok) (hT : TabL P L) {u : State} (hc : Ctx L g m₀ u) {is : List Instr} {Q' : State → Prop}
    (k : ∀ u', Ctx L g m₀ u' → u'.mem = u.mem → u'.gpr .r3 = BitVec.ofNat 32 (min P.F.H.D P.Q) →
      (∀ r, r ≠ .r0 → r ≠ .r3 → r ≠ .r7 → r ≠ .r12 → u'.gpr r = u.gpr r) → WP isa (.block is) u' Q') :
    WP isa (.block (([.ldr .r3 .r6 tD, .movw .r0 (BitVec.ofNat 16 P.Q), .subs .r12 .r3 (.reg .r0),
      .mov .r7 (imm 0), .adc .r7 .r7 (imm 0), .dp .sub .r7 .r7 (imm 1), .dp .and .r12 .r12 (.reg .r7),
      .dp .add .r3 .r0 (.reg .r12)] : List Instr) ++ is)) u Q' := by
  simp only [List.cons_append, List.nil_append]
  obtain hD : P.F.H.D < 2 ^ 32 := by anums
  obtain hQ : P.Q < 2 ^ 16 := by anums
  refine ldD_ok hL hc (d := .r3) (by decide) fun u₁ c₁ m₁ v₁ k₁ => ?_
  rw [hT.1] at v₁
  refine movw_ok c₁ (d := .r0) (by decide) hQ fun u₂ c₂ m₂ v₂ k₂ => ?_
  refine wp_subsC (op2_reg _ _) fun u₃ v₃ c₃ => ?_
  obtain c₃' := c₂.upd v₃ (by decide)
  refine wp_movC (op2_imm (by decide)) fun u₄ v₄ c₄ => wp_adc (op2_imm (by decide)) fun u₅ v₅ => ?_
  refine wp_dpS (op2_imm (by decide)) fun u₆ v₆ => wp_dpS (op2_reg _ _) fun u₇ v₇ => ?_
  refine wp_dpS (op2_reg _ _) fun u₈ v₈ => ?_
  obtain c₈ := (((((c₃'.upd v₄ (by decide)).upd v₅ (by decide)).upd v₆ (by decide)).upd v₇ (by decide)).upd v₈ (by decide))
  refine k u₈ c₈ (by rw [v₈.mem, v₇.mem, v₆.mem, v₅.mem, v₄.mem, v₃.mem, m₂, m₁]) ?_ fun r h0 h3 h7 h12 => ?_
  · have e12 : u₃.gpr .r12 = BitVec.ofNat 32 P.F.H.D - BitVec.ofNat 32 P.Q := by
      rw [v₃.gpr, k₂ _ (by decide), v₁, v₂]
    obtain ec : u₄.c = decide ((BitVec.ofNat 32 P.Q).toNat ≤ (BitVec.ofNat 32 P.F.H.D).toNat) := by
      rw [c₄, c₃, v₂, k₂ _ (by decide), v₁]
    obtain e7₆ : u₆.gpr .r7 = 0#32 + 0#32 + (if u₄.c then 1 else 0) - 1#32 := by
      rw [v₆.gpr, dpVal, v₅.gpr, v₄.gpr]
    obtain e12₆ : u₆.gpr .r12 = u₃.gpr .r12 := by
      rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide)]
    obtain e12₇ : u₇.gpr .r12 = u₆.gpr .r12 &&& u₆.gpr .r7 := by rw [v₇.gpr, dpVal]
    obtain e0₇ : u₇.gpr .r0 = BitVec.ofNat 32 P.Q := by
      rw [v₇.other _ (by decide), v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide),
        v₃.other _ (by decide), v₂]
    rw [v₈.gpr, dpVal, e0₇, e12₇, e12₆, e7₆, e12, ec]
    exact min_val _ _ hD (by omega_arith)
  · rw [v₈.other _ h3, v₇.other _ h12, v₆.other _ h7, v₅.other _ h7, v₄.other _ h7, v₃.other _ h12, k₂ _ h0,
      k₁ _ h3]

theorem addr_shuffle (a f b : BitVec 32) : a + f - b = f + (a - b) := by
  rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_comm a f, BitVec.add_assoc]

/-- `r2 = fp + (a - n)` for `r3 = n`, and `r1 = digest`, from the frame's slot. -/
theorem dstArgs_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {a n : Nat} (ha : a < 2 ^ 16) (hn : n ≤ a)
    (h3 : u.gpr .r3 = BitVec.ofNat 32 n) :
    WP isa (.block [.movw .r2 (BitVec.ofNat 16 a), .dp .add .r2 .r2 (.reg .r8), .dp .sub .r2 .r2 (.reg .r3),
      .ldr .r1 .r8 fDigest]) u fun u' => Ctx L g m₀ u' ∧ u'.mem = u.mem ∧
        u'.gpr .r2 = L.fp + BitVec.ofNat 32 (a - n) ∧ u'.gpr .r1 = L.dg ∧ u'.gpr .r3 = BitVec.ofNat 32 n ∧
        ∀ r, r ≠ .r1 → r ≠ .r2 → u'.gpr r = u.gpr r := by
  refine movw_ok hc (d := .r2) (by decide) ha fun u₁ c₁ m₁ v₁ k₁ => ?_
  refine wp_dpS (op2_reg _ _) fun u₂ v₂ => wp_dpS (op2_reg _ _) fun u₃ v₃ => ?_
  obtain c₃ := (c₁.upd v₂ (by decide)).upd v₃ (by decide)
  refine frLd_ok hL c₃ (d := .r1) (by decide) (o := fDigest) (by decide) fun u₄ c₄ m₄ v₄ k₄ => WP.block_nil ?_
  refine ⟨c₄, by rw [m₄, v₃.mem, v₂.mem, m₁], ?_, by rw [v₄]; exact c₃.pDg, ?_, fun r h1 h2 => ?_⟩
  · rw [k₄ _ (by decide), v₃.gpr, dpVal, v₂.gpr, dpVal, v₁, v₂.other .r3 (by decide),
      k₁ .r3 (by decide), k₁ .r8 (by decide), h3, hc.r8, addr_shuffle, VG.Proof.AesGcm.Arm.ofNat_sub32 hn (by omega_arith)]
  · rw [k₄ _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide), k₁ _ (by decide), h3]
  · rw [k₄ _ h1, v₃.other _ h2, v₂.other _ h2, k₁ _ h2]

/-- The arguments of `X`'s copy: `X` cleared, `r3 = m = min(D, Q)`, the
digest in `r1`, `X + Q - m` in `r2`. -/
theorem xArgs_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block (cfgOf P).xArgs) t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.B + BitVec.ofNat 64 216, 68⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 216) 68 = List.replicate 68 0 ∧
      u.gpr .r3 = BitVec.ofNat 32 (min P.F.H.D P.Q) ∧
      u.gpr .r2 = L.fp + BitVec.ofNat 32 (fX + P.Q - min P.F.H.D P.Q) ∧ u.gpr .r1 = L.dg := by
  rw [Cfg.xArgs, WP.block_append_iff]
  refine WP.mono (zeroN_ok hL hc (k := 17) (o := fX) (by decide)) fun u₁ ⟨c₁, _, f₁, b₁⟩ => ?_
  refine (min_ok hL hT c₁ (is := [.movw .r2 (BitVec.ofNat 16 (fX + P.Q)), .dp .add .r2 .r2 (.reg .r8),
      .dp .sub .r2 .r2 (.reg .r3), .ldr .r1 .r8 fDigest]) fun u₂ c₂ m₂ v₂ _ => ?_ : _)
  refine WP.mono (dstArgs_ok hL c₂ (a := fX + P.Q) (n := min P.F.H.D P.Q) (by simp only [fX]; anums)
    (by simp only [fX]; omega_arith) v₂) fun u₃ ⟨c₃, m₃, h2, h1, h3, _⟩ => ?_
  obtain hm : u₃.mem = u₁.mem := by rw [m₃, m₂]
  exact ⟨c₃, hm ▸ f₁, hm ▸ b₁, h3, h2, h1⟩

/-- `X`, the `Q` bytes at `fX`: `Q - m` zero bytes, then the digest's first
`m = min(D, Q)`. -/
theorem prepX_ok (hL : L.Ok) (hT : TabL P L) (hdn : P.F.H.D ≤ dn) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).prepX t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.B + BitVec.ofNat 64 216, 68⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 216) P.Q =
        List.replicate (P.Q - min P.F.H.D P.Q) 0 ++ Spec.Sha256.bytesAt t.mem (State.addr L.dg) (min P.F.H.D P.Q) := by
  have hb := hL.B_fit
  have ng := hL.ng
  obtain ⟨_, _, _, _, hD16, hD64, _, _, _, _, _, _, _⟩ := P.sizes
  obtain ⟨_, _, _, _, hQ8, hQ66, _, _⟩ := P.wsizes
  have : fX = 192 := rfl
  rw [Cfg.prepX]
  refine WP.seq (WP.mono (xArgs_ok hL hT hc) fun u₅ ⟨hc₅, hf₁, hb₁, h3, h2, h1⟩ => ?_)
  obtain hm : min P.F.H.D P.Q ≤ P.Q := Nat.min_le_right _ _
  obtain hm16 : 16 ≤ min P.F.H.D P.Q := by omega_arith
  obtain hpa : State.addr (L.fp + BitVec.ofNat 32 (fX + P.Q - min P.F.H.D P.Q)) =
      L.B + BitVec.ofNat 64 (216 + (P.Q - min P.F.H.D P.Q)) := by
    rw [hL.fpA (by omega_arith)]; congr 2; omega_arith
  refine WP.mono (cp_ok hL hc₅ (p := L.fp + BitVec.ofNat 32 (fX + P.Q - min P.F.H.D P.Q)) (q := L.dg)
      (n := min P.F.H.D P.Q) (by omega_arith) (by omega_arith) h1 h2 h3 (by omega_arith)
      (by rw [fp_toNat hL (by omega_arith)]; have := hL.na; omega_arith)
      ⟨L.DG, by simp, within_base _ (by omega_arith)⟩
      (by rw [hpa]; exact ⟨L.FR, by simp, within_fr _ (by omega_arith) (by omega_arith)⟩)
      (by rw [hpa]; exact safe_low L (by omega_arith))
      (by rw [hpa]; exact (hL.stk_DG (d := 216 + (P.Q - min P.F.H.D P.Q)) (n := min P.F.H.D P.Q)
        (by omega_arith)).symm.sub_left (Region.sub_prefix (by omega_arith))))
    fun u ⟨hc', _, hf, hbt⟩ => ?_
  rw [hpa] at hf hbt
  obtain hdg : Spec.Sha256.bytesAt u₅.mem (State.addr L.dg) (min P.F.H.D P.Q) =
      Spec.Sha256.bytesAt t.mem (State.addr L.dg) (min P.F.H.D P.Q) :=
    bytesAt_frame hf₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((hL.stk_DG (d := 216) (n := 68) (by omega_arith)).symm.sub_left
        (Region.sub_prefix (by omega_arith)))) (by omega_arith)
  refine ⟨hc', hf₁.trans (hf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by omega_arith) (by omega_arith)⟩), ?_⟩
  rw [show P.Q = (P.Q - min P.F.H.D P.Q) + min P.F.H.D P.Q by omega_arith, Proof.Hmac.Common.bytesAt_add,
    Offset.add_add, hbt, ← show P.Q = (P.Q - min P.F.H.D P.Q) + min P.F.H.D P.Q by omega_arith,
    bytesAt_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)) (by omega_arith),
    hdg, bytesAt_take _ _ (k := 68) (by omega_arith), hb₁, List.take_replicate, Nat.min_eq_left (by omega_arith)]

/-! ## P-521's digest for `core` -/

theorem shift_back (e sh : Nat) (hs : sh < 8) : (e * 2 ^ 8) >>> (8 - sh) = e * 2 ^ sh := by
  rw [Nat.shiftRight_eq_div_pow, show e * 2 ^ 8 = e * 2 ^ sh * 2 ^ (8 - sh) by
    rw [Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega_arith, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

/-- If `big`: the digest for `core`, the digest's number shifted left by
`sh` bits, in `Q` bytes at `fXc`. -/
theorem prepC_ok (hL : L.Ok) (hT : TabL P L) (hW : P.R.big = true) (hdn : P.F.H.D ≤ dn) {t : State}
    (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).prepC t fun u => Ctx L g m₀ u ∧
      Frame [⟨State.addr L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 284, 68⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 284) P.Q =
        Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem (State.addr L.dg) P.F.H.D) * 2 ^ P.R.sh) := by
  have hb := hL.B_fit
  have ng := hL.ng
  obtain ⟨-, hQ66, -, hQD⟩ := P.sizesW hW
  obtain ⟨_, _, _, _, hD16, hD64, _, _, _, _, _, _, _⟩ := P.sizes
  have hsl := P.R.nBits_len
  obtain hnb5 := (P.R.sizesW hW).2.2
  obtain hsh8 : P.R.sh < 8 := by simp only [RfcHash.Q] at hQ66; omega_arith
  obtain hsh1 : 1 ≤ P.R.sh := by simp only [RfcHash.Q] at hQ66; omega_arith
  have : fXc = 260 := rfl
  have hsc : (cfgOf P).sh = P.R.sh := rfl
  rw [Cfg.prepC]
  refine WP.seq ?_
  rw [Cfg.xcArgs, WP.block_append_iff]
  refine WP.mono (zeroN_ok hL hc (k := 17) (o := fXc) (by decide)) fun u₁ ⟨c₁, _, f₁, b₁⟩ => ?_
  rw [show 24 + fXc = 284 from rfl, show 4 * 17 = 68 from rfl] at f₁ b₁
  refine ldD_ok hL c₁ (d := .r3) (by decide) fun u₂ c₂ m₂ v₂ _ => ?_
  rw [hT.1] at v₂
  refine WP.mono (dstArgs_ok hL c₂ (a := fXc + (cfgOf P).len - 1) (n := P.F.H.D) (by simp only [cfgOf_len]; anums)
    (by simp only [cfgOf_len]; omega_arith) v₂) fun u₃ ⟨c₃, m₃, h2, h1, h3, _⟩ => ?_
  rw [cfgOf_len] at h2
  obtain hm₁ : u₃.mem = u₁.mem := by rw [m₃, m₂]
  obtain hdg : Spec.Sha256.bytesAt u₁.mem (State.addr L.dg) P.F.H.D = Spec.Sha256.bytesAt t.mem (State.addr L.dg) P.F.H.D :=
    bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((hL.stk_DG (d := 284) (n := 68) (by omega_arith)).symm.sub_left (Region.sub_prefix hdn))) (by omega_arith)
  obtain hpa : State.addr (L.fp + BitVec.ofNat 32 (fXc + P.Q - 1 - P.F.H.D)) =
      L.B + BitVec.ofNat 64 (284 + (P.Q - 1 - P.F.H.D)) := by
    rw [hL.fpA (by omega_arith)]; congr 2; omega_arith
  refine WP.seq (WP.mono (cp_ok hL c₃ (p := L.fp + BitVec.ofNat 32 (fXc + P.Q - 1 - P.F.H.D)) (q := L.dg)
      (n := P.F.H.D) (by omega_arith) (by omega_arith) h1 h2 h3 (by omega_arith)
      (by rw [fp_toNat hL (by omega_arith)]; have := hL.na; omega_arith)
      ⟨L.DG, by simp, within_base _ hdn⟩
      (by rw [hpa]; exact ⟨L.FR, by simp, within_fr _ (by omega_arith) (by omega_arith)⟩)
      (by rw [hpa]; exact safe_low L (by omega_arith))
      (by rw [hpa]; exact (hL.stk_DG (d := 284 + (P.Q - 1 - P.F.H.D)) (n := P.F.H.D)
        (by omega_arith)).symm.sub_left (Region.sub_prefix hdn)))
    fun u₄ ⟨c₄, _, f₄, b₄⟩ => ?_)
  rw [hpa] at f₄ b₄
  rw [hsc]
  refine WP.mono (conv_ok hL hW c₄ (o := fXc) (s := 8 - P.R.sh) (by omega_arith) (by omega_arith) (by decide)
    (by omega_arith) (by omega_arith)) fun u₆ ⟨c₆, _, f₆, b₆⟩ => ?_
  refine ⟨c₆, ?_, ?_⟩
  · have g₁ : Frame [⟨State.addr L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 284, 68⟩] t.mem u₁.mem :=
      f₁.sub fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; simp, sub_refl _⟩
    obtain g₄ : Frame [⟨State.addr L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 284, 68⟩] u₃.mem u₄.mem :=
      f₄.sub fun r hr => ⟨⟨L.B + BitVec.ofNat 64 284, 68⟩, by simp, by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega_arith) (by omega_arith)⟩
    obtain g₆ : Frame [⟨State.addr L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 284, 68⟩] u₄.mem u₆.mem :=
      f₆.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Region.sub_prefix (by omega_arith)⟩
    rw [hm₁] at g₄
    exact (g₁.trans g₄).trans g₆
  · -- `Q - D - 1` zero bytes, the digest, and a zero byte, shifted right by `8 - sh` bits.
    obtain hz : ∀ a n, a + n ≤ 68 → Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 (284 + a)) n =
        List.replicate n 0 := fun a n han => by
      obtain h1 := bytesAt_take u₁.mem (L.B + BitVec.ofNat 64 284) (n := a + n) (k := 68) (by omega_arith)
      rw [b₁, List.take_replicate, Nat.min_eq_left (by omega_arith), Proof.Hmac.Common.bytesAt_add, Offset.add_add,
        ← List.replicate_append_replicate] at h1
      exact (List.append_inj h1 (by simp [Spec.Sha256.bytesAt])).2
    obtain hY : Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 284) P.Q =
        List.replicate (P.Q - 1 - P.F.H.D) 0 ++ (Spec.Sha256.bytesAt t.mem (State.addr L.dg) P.F.H.D ++
          List.replicate 1 0) := by
      obtain e := Proof.Hmac.Common.bytesAt_add u₄.mem (L.B + BitVec.ofNat 64 284) (P.Q - 1 - P.F.H.D)
        (P.F.H.D + 1)
      obtain e' := Proof.Hmac.Common.bytesAt_add u₄.mem
        (L.B + BitVec.ofNat 64 284 + BitVec.ofNat 64 (P.Q - 1 - P.F.H.D)) P.F.H.D 1
      rw [show P.Q - 1 - P.F.H.D + (P.F.H.D + 1) = P.Q by omega_arith] at e
      rw [Offset.add_add, Offset.add_add] at e'
      rw [Offset.add_add] at e
      obtain p₁ : Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 284) (P.Q - 1 - P.F.H.D) =
          List.replicate (P.Q - 1 - P.F.H.D) 0 := by
        rw [bytesAt_frame f₄ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith))
          (by omega_arith), hm₁]
        have := hz 0 (P.Q - 1 - P.F.H.D) (by omega_arith)
        rwa [Nat.add_zero] at this
      obtain p₃ : Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 (284 + (P.Q - 1 - P.F.H.D) + P.F.H.D)) 1 =
          List.replicate 1 0 := by
        rw [bytesAt_frame f₄ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith))
          (by omega_arith), hm₁, show 284 + (P.Q - 1 - P.F.H.D) + P.F.H.D = 284 + (P.Q - 1 - P.F.H.D + P.F.H.D) by
            omega_arith]
        exact hz (P.Q - 1 - P.F.H.D + P.F.H.D) 1 (by omega_arith)
      rw [e, e', b₄, hm₁, hdg, p₁, p₃]
    rw [show 24 + fXc = 284 from rfl] at b₆
    rw [b₆, hY, ofBytes_zeros, ofBytes_append_zeros, show 8 * 1 = 8 from rfl, shift_back _ _ hsh8]

end VG.Proof.Ecdsa.Rfc6979.Arm
