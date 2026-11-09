module

import VerifiedGarbage.Proof.Framework.Arm.Syms
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Hash
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Upd
public import VerifiedGarbage.Proof.Framework.ICall
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Regs
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

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
  have hfp : L.fp.toNat = L.sp.toNat - 512 := VG.Arm.FrameStack.sub_toNat' (by omega_arith)
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
    (tabLd_ok hL hc (d := .lr) (by decide) (o := 4 * j) (by omega) fun u' c' m' v' k' =>
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
  have e0 := scrA hL (o := 0) (by decide)
  have e1 := scrA hL (o := 192) (by decide)
  have e3 := scrA hL (o := 384) (by decide)
  have ek := hL.fpA (o := 0) (by omega_arith)
  have hst := hc.stk_eq hL
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
  have hok : TabOK P.F P.f u.syms := hT.1 ▸ hT.2 ▸ hcu.tabOk
  refine tcall_ok hL hcu (j := 0) (by decide) (n := P.F.hiN) (c := P.F.hiC)
    (by rw [show 4 * 0 = 0 from rfl, ← hT.1]; exact hcu.tabMem.1) hok.i
    fun u₁ c₁ m₁ y₁ k₁ => ?_
  apply WP.of_syms
  refine hi_frame P.ok.hi P.ok.hiSt (initA hL c₁ (by rw [k₁ _ (by decide)]; exact h0)
    (by rw [k₁ _ (by decide)]; exact h1) (by rw [k₁ _ (by decide)]; exact h2)
    (by rw [k₁ _ (by decide)]; exact h3) (by rw [k₁ _ (by decide)]; exact h12)) fun u' ha hi ho sy => ?_
  have ek : Spec.Sha256.bytesAt u₁.mem (State.addr (L.fp + BitVec.ofNat 32 0)) P.F.H.D = keyOf P L t.mem := by
    rw [hL.fpA (by omega_arith), m₁, hmu]
  have hws : ∀ r ∈ HiArgs.wr P.ok.hH.SH P.ok.Wi (L.scr + BitVec.ofNat 32 0) (L.scr + BitVec.ofNat 32 192)
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
  have e0 := scrA hL (o := 0) (by decide)
  have e3 := scrA hL (o := 384) (by decide)
  have hb := hcw.below_eq hL
  have hn := hd.nowrap hL
  have := hL.nc
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hS, _, hB⟩ := P.sizes
  have bsub : Region.Sub ⟨L.B + BitVec.ofNat 64 8, 16⟩ ⟨L.B, 24⟩ := Offset.sub_base _ (by omega_arith)
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
  have hok : TabOK P.F P.f w.syms := hT.1 ▸ hT.2 ▸ hcw.tabOk
  refine tcall_ok hL hcw (j := 1) (by decide) (n := P.F.H.updN) (c := P.F.H.updC)
    (by rw [show 4 * 1 = 4 from rfl, ← hT.1]; exact hcw.tabMem.2.1) hok.u
    fun u₁ c₁ m₁ y₁ k₁ => ?_
  have hw₁ : St P L g m₀ t text u₁ :=
    ⟨c₁, by rw [k₁ _ (by decide)]; exact hw.r9, m₁ ▸ hw.frame, m₁ ▸ hw.inner, m₁ ▸ hw.outer⟩
  apply WP.of_syms
  refine upd_frame P.ok.hH (updA hL c₁ hd hlen (by rw [k₁ _ (by decide)]; exact h0)
    (by rw [k₁ _ (by decide)]; exact h1) (by rw [k₁ _ (by decide)]; exact h7)
    (by rw [k₁ _ (by decide)]; exact h10)) fun w' af hr sy => ?_
  have hws : ∀ r ∈ [(⟨State.addr (L.scr + BitVec.ofNat 32 0), P.F.H.S⟩ : Region),
      ⟨State.addr (L.scr + BitVec.ofNat 32 384), P.ok.hH.Wb⟩], Region.Sub r (WK L) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> exact scr_wk hL (by decide) (by anums)
  have hcount : Pbkdf2.Stream.Arm.count u₁ = BitVec.ofNat 64
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
  have hm : t₆.mem = u.mem := by rw [m₆, m₅, m₄, m₃, m₂, m₁]
  have hv : State.addr (L.fp + BitVec.ofNat 32 64) = L.B + BitVec.ofNat 64 88 := hL.fpA (by omega_arith)
  have hw : St P L g m₀ t [] t₆ :=
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
  have c₅ := c₄.upd u₅ (by decide)
  refine mov0_ok c₅ (d := .r3) (by decide) fun t₆ c₆ m₆ v₆ k₆ => ?_
  refine movw_ok c₆ (d := .r7) (by decide) (v := len) (by omega_arith) fun t₇ c₇ m₇ v₇ k₇ => ?_
  rw [← List.append_nil (scrAt .r10 sWork)]
  refine scrAt_ok c₇ (d := .r10) (by decide) (o := sWork) (by decide) fun t₈ c₈ m₈ v₈ k₈ => ?_
  refine WP.block_nil ?_
  have hm : t₈.mem = u.mem := by rw [m₈, m₇, m₆, u₅.mem, m₄, m₃, m₂, m₁]
  have hmA : State.addr (L.scr + BitVec.ofNat 32 2256) = msgA L := scrA hL (by decide)
  have hw : St P L g m₀ t text t₈ :=
    ⟨c₈, by rw [k₈ _ (by decide) (by decide), k₇ _ (by decide), k₆ _ (by decide), u₅.other _ (by decide),
        k₄ _ (by decide), k₃ _ (by decide), k₂ _ (by decide) (by decide), k₁ _ (by decide) (by decide)]; exact hu.r9,
      hm ▸ hu.frame, hm ▸ hu.inner, hm ▸ hu.outer⟩
  have h2 : t₈.gpr .r2 = BitVec.ofNat 32 (P.F.H.B + text.length) := by
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
  have e0 := scrA hL (o := 0) (by decide)
  have e1 := scrA hL (o := 192) (by decide)
  have e3 := scrA hL (o := 384) (by decide)
  have eo := hL.fpA (o := dst) (by omega_arith)
  have hst := hcw.stk_eq hL
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
  have c₅ := c₄.upd u₅ (by decide)
  refine wp_dpS (op2_imm hle) fun t₆ u₆ => ?_
  have c₆ := c₅.upd u₆ (by decide)
  refine mov0_ok c₆ (d := .r3) (by decide) fun t₇ c₇ m₇ v₇ k₇ => ?_
  refine fpAdd_ok c₇ (d := .r10) (by decide) he fun t₈ c₈ m₈ v₈ k₈ => ?_
  rw [← List.append_nil (scrAt .r12 sWork)]
  refine scrAt_ok c₈ (d := .r12) (by decide) (o := sWork) (by decide) fun t₉ c₉ m₉ v₉ k₉ => ?_
  refine WP.block_nil ?_
  have hmm : t₉.mem = u.mem := by rw [m₉, m₈, m₇, u₆.mem, u₅.mem, m₄, m₃, m₂, m₁]
  have h2 : t₉.gpr .r2 = BitVec.ofNat 32 (P.F.H.B + text.length) := by
    rw [k₉ _ (by decide) (by decide), k₈ _ (by decide), k₇ _ (by decide), u₆.gpr, dpVal, u₅.gpr, dpVal,
      k₄ _ (by decide), v₃, v₄, hT.1, htl, BitVec.ofNat_add, BitVec.ofNat_add, BitVec.add_assoc]
  have h3 : t₉.gpr .r3 = 0 := by rw [k₉ _ (by decide) (by decide), k₈ _ (by decide)]; exact v₇
  have h9 : t₉.gpr .r9 = t.gpr .r9 := by
    rw [k₉ _ (by decide) (by decide), k₈ _ (by decide), k₇ _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), k₄ _ (by decide), k₃ _ (by decide), k₂ _ (by decide) (by decide),
      k₁ _ (by decide) (by decide)]; exact hu.r9
  have hok : TabOK P.F P.f t₉.syms := hT.1 ▸ hT.2 ▸ c₉.tabOk
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
  have eo := hL.fpA (o := dst) (by omega_arith)
  have hk := blockKey_length (P := P) (keyOf_length (L := L) t.mem)
  have hm := hpost _ text (by rw [hk, hB])
    (by rw [hk]; anums) (by rw [m₁₀, hmm]; exact hu.inner)
    (by rw [k₁₀ _ (by decide), k₁₀ _ (by decide), h3, h2, hB]; exact append_zero (by rw [htl]; anums))
    (by rw [m₁₀, hmm]; exact hu.outer)
  rw [eo, hD] at hm
  have hws : ∀ r ∈ HfArgs.wr P.ok.hH.SH P.ok.Wf (L.scr + BitVec.ofNat 32 0) (L.fp + BitVec.ofNat 32 dst)
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
