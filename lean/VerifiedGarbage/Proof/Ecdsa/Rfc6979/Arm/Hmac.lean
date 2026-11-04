module

import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Framework.ICall
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Calls
import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Common
import VerifiedGarbage.Proof.Pbkdf2.MdKeys
import VerifiedGarbage.Proof.Hmac.Common
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Hash
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Upd
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Regs
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Copy
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Deterministic ECDSA on 32-bit ARM: one HMAC, through the table

`HMAC_K(data)` (`Cfg.hmac`), for the key `K` (of the hash function's output
length) in the frame and `len` bytes of data in the frame or in `scratch`
above HMAC's working space (`DataOk`), written to the frame at `dst`, from
the table's streaming functions, each called indirectly (`tload_ok`: the
table's word, which `Ctx` says holds the function of `L.G`, whose call an
indirect call of `L.f`'s functions reaches), as on x86-64
(`Proof/Ecdsa/Rfc6979/X86_64/Hmac.lean`): the states for the key
(`init_step`: each set by `init`, `initCall_ok`, and updated with the padded
key, `padBlk_ok` and `updCall_ok`), the inner state updated with the data
(`upd_step`), and the MAC (`fin_step`: the inner state finalized,
`finCall_ok`, the outer one updated with its digest and finalized, and the
digest copied). `update` and `finalize` are called in the frames of their
stack arguments, as PBKDF2's code calls them (`VG.Proof.Pbkdf2.Whole.Arm`).
They change only HMAC's states and working space, the padded key and what
`finalize` writes (all within the first 2256 bytes of `scratch`), the 24
bytes below the frame, and `dst` (`hmac_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Impl.Pbkdf2.Stream.Arm (scrAt)
open VG.Proof.Pbkdf2.Whole.Arm (UpdL upd_frame stk)
open VG.Proof.Pbkdf2.Stream.Arm (FinArgs fin_frame init_call)
open VG.WriteBytes (writeBytes writeBytes_append writeBytes_nil writeBytes_frame)

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

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

theorem ptr_r0' : ∀ r ∈ ptrRegs, r ≠ .r0 := by decide

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

theorem fp_toNat (hL : L.Ok) {o : Nat} (ho : o ≤ 216 + 4 * L.e) :
    (L.fp + BitVec.ofNat 32 o).toNat = L.sp.toNat - (216 + 4 * L.e) + o := by
  have := hL.nB; have := L.sp.isLt; have := L.he
  have hfp : L.fp.toNat = L.sp.toNat - (216 + 4 * L.e) := VG.Arm.FrameStack.sub_toNat' (by omega_arith)
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith : o < 2 ^ 32), hfp]
  exact Nat.mod_eq_of_lt (by omega_arith)

/-- The stack below the frame and parts of it are apart from `scratch`. -/
theorem low_scr (hL : L.Ok) {n e k : Nat} (hn : n ≤ 240) (h : e + k ≤ 8192) :
    Region.Disjoint ⟨L.B, n⟩ ⟨State.addr L.scr + BitVec.ofNat 64 e, k⟩ :=
  (hL.kc.sub_left (Region.sub_prefix (by omega_arith))).sub_right (Offset.sub_base _ h)

/-- The part of `scratch` HMAC's functions use: its states and working space. -/
abbrev WK {dn : Nat} (L : Lay dn) : Region := ⟨State.addr L.scr, 2256⟩

theorem wk_safe {r : Region} (h : Region.Sub r (WK L)) : Safe L r :=
  .inr (.inl (sub_trans h (Region.sub_prefix (by omega_arith))))

theorem scr_wk (hL : L.Ok) {o n : Nat} (ho : o < 8192) (h : o + n ≤ 2256) :
    Region.Sub ⟨State.addr (L.scr + BitVec.ofNat 32 o), n⟩ (WK L) := by
  rw [scrA hL ho]; exact Offset.sub_base _ h

theorem after_frameU (hL : L.Ok) {u u' : State} (hc : Ctx L g m₀ u) {ws : List Region}
    (ha : Pbkdf2.Stream.Arm.After u ws u') (hs : ∀ r ∈ ws, Region.Sub r (WK L)) :
    Frame [WK L, ⟨L.B, 24⟩] u.mem u'.mem :=
  ha.frame.sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨WK L, by simp, hs r hr⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨L.B, 24⟩, by simp, by rw [hc.below_eq hL]; exact Offset.sub_base _ (by omega_arith)⟩


/-! ## The table -/

/-- The layout's table is of `P`'s streaming functions, and its indirect
calls reach the functions of `P.f`. -/
def TabL (P : RfcHash) {dn : Nat} (L : Lay dn) : Prop := L.G = P.H ∧ L.f = P.f

/-- The table's words, as on entry. -/
theorem Ctx.tabWord (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {o : Nat} (ho : o + 4 ≤ 20) :
    t.mem.readW (State.addr L.tab + BitVec.ofNat 64 o) 32 = m₀.readW (State.addr L.tab + BitVec.ofNat 64 o) 32 :=
  hc.frame.readW (r := L.TAB) (Offset.contains_base _ ho (by have := hL.nt; omega_arith)) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.to
    · exact hL.tc
    · exact hL.tk) (by decide)

/-- The table's word `j` into `r`. -/
theorem tload_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {r : Reg} (hr : r ∉ ptrRegs) {j : Nat}
    (hj : 4 * j + 4 ≤ 20) :
    WP isa (.block (Cfg.tload r j)) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧ t'.syms = t.syms ∧
      t'.gpr r = m₀.readW (State.addr (L.tab + BitVec.ofNat 32 (4 * j))) 32 ∧ (∀ q, q ≠ r → t'.gpr q = t.gpr q) := by
  have ha : State.addr (L.tab + BitVec.ofNat 32 (4 * j)) = State.addr L.tab + BitVec.ofNat 64 (4 * j) :=
    addr_add (by have := hL.nt; omega_arith)
  refine wp_ldrS (a := State.addr L.tab + BitVec.ofNat 64 (4 * j)) (by omega_arith) (by rw [hc.r4]; exact ha)
    (hc.inTab hL hj) fun u v => WP.block_nil ⟨hc.upd v hr, v.mem, v.syms, ?_, v.other⟩
  rw [v.gpr, hc.tabWord hL hj, ha]

/-- An indirect call through `r`, which holds the address of `n`, reaches it. -/
theorem icall_reach {s : State} {r : Reg} {ts : List (String × Prog isa)} {n : String} {c : Prog isa}
    (hf : ts.find? (fun q => (s.syms q.1).setWidth 64 == (s.syms n).setWidth 64) = some (n, c))
    (hr : s.gpr r = s.syms n) :
    isa.icall (.blx r) s = some ((s.gpr r).setWidth 64) ∧
      icallTarget isa s ((s.gpr r).setWidth 64) ts = some (n, c) :=
  ⟨rfl, by show ts.find? (fun q => (s.syms q.1).setWidth 64 == (s.gpr r).setWidth 64) = _; rw [hr]; exact hf⟩

theorem push_some {rs : List Reg} {s u : State} (h : isa.push (.push rs) s = some u) :
    u.gpr = s.gpr ∧ u.syms = s.syms := by
  simp only [isa, push] at h; split at h <;> cases h; exact ⟨rfl, rfl⟩

/-- An indirect call through `r` in a frame pushing `rs`, from a state where
`r` holds the address of `n`, reaches it. -/
theorem frame_reach {s : State} {r : Reg} {rs : List Reg} {ts : List (String × Prog isa)} {n : String}
    {c : Prog isa} (hf : ts.find? (fun q => (s.syms q.1).setWidth 64 == (s.syms n).setWidth 64) = some (n, c))
    (hr : s.gpr r = s.syms n) :
    ∀ s₁, isa.push (.push rs) s = some s₁ → ∃ a, isa.icall (.blx r) s₁ = some a ∧
      icallTarget isa s₁ a ts = some (n, c) := fun s₁ hp => by
  obtain ⟨g, y⟩ := push_some hp
  have h := icall_reach (s := s₁) (r := r) (ts := ts) (n := n) (c := c) (by rw [y]; exact hf)
    (by rw [g, y]; exact hr)
  exact ⟨_, h.1, h.2⟩

/-- `d ← scratch + o`, alone. -/
theorem scrAt_blk {t : State} (hc : Ctx L g m₀ t) {d : Reg} (hd : d ∉ ptrRegs) {o : Nat} (ho : o < 2 ^ 16) :
    WP isa (.block (scrAt d o)) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧
      t'.gpr d = L.scr + BitVec.ofNat 32 o ∧ (∀ r, r ≠ d → r ≠ .r12 → t'.gpr r = t.gpr r) := by
  rw [← List.append_nil (scrAt d o)]
  exact scrAt_ok hc hd ho fun t' c m v k => WP.block_nil ⟨c, m, v, k⟩

/-! ## The streaming `init` -/

/-- The writes of a call, within `scratch`'s first 2256 bytes and the stack below the frame. -/
theorem frame_call (hL : L.Ok) {u u' : State} (hc : Ctx L g m₀ u) {ws : List Region}
    (ha : Pbkdf2.Stream.Arm.After u ws u') :
    Frame (ws ++ [⟨L.B, 24⟩]) u.mem u'.mem :=
  ha.frame.sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, sub_refl _⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨L.B, 24⟩, by simp, by rw [hc.below_eq hL]; exact Offset.sub_base _ (by omega_arith)⟩

/-- `init` of the state at `scratch + o`: it represents the empty message. -/
theorem initCall_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) {o : Nat} (ho : o + 192 ≤ 384) :
    WP isa ((cfgOf P).initCall o) t fun u => Ctx L g m₀ u ∧ u.gpr .r9 = t.gpr .r9 ∧
      Frame [⟨State.addr L.scr + BitVec.ofNat 64 o, P.H.S⟩, ⟨L.B, 24⟩] t.mem u.mem ∧
      P.ok.SH.Repr u.mem (State.addr L.scr + BitVec.ofNat 64 o) [] := by
  unfold Cfg.initCall
  refine WP.seq (WP.mono (scrAt_blk hc (d := .r0) (by decide) (o := o) (by omega_arith)) fun u₁ ⟨c₁, m₁, v₁, k₁⟩ =>
    WP.seq (WP.mono (tload_ok hL c₁ (r := .r12) (by decide) (j := 0) (by decide)) fun u₂ ⟨c₂, m₂, y₂, v₂, k₂⟩ => ?_))
  have htm := c₂.tabMem
  have hok := c₂.tabOk
  rw [hT.1] at htm hok
  rw [hT.2] at hok
  have hn : u₂.gpr .r12 = u₂.syms P.H.initN := by rw [v₂]; exact htm.1
  obtain ⟨hi, hf⟩ := icall_reach (ts := (cfgOf P).f.init) hok.1 hn
  refine WP.icalls_of_call hi hf ?_
  apply WP.of_syms
  have e : State.addr (L.scr + BitVec.ofNat 32 o) = State.addr L.scr + BitVec.ofNat 64 o := scrA hL (by omega_arith)
  refine init_call P.ok (st := L.scr + BitVec.ofNat 32 o) ((k₂ _ (by decide)).trans v₁)
    (by rw [scr_toNat hL (by omega_arith)]; have := hL.nc; anums)
    (c₂.coversW fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [e]; exact ⟨L.SCR, by simp, within_off _ (by anums)⟩) fun u' af hr sy => ?_
  rw [e] at af hr
  refine ⟨c₂.afterU hL af (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact wk_safe (Offset.sub_base _ (by anums))) sy,
    by rw [af.cs .r9 (by decide) (by decide), k₂ _ (by decide), k₁ _ (by decide) (by decide)], ?_, hr⟩
  have := frame_call hL c₂ af
  rwa [m₂, m₁] at this


/-! ## The streaming `update` -/

/-- Code that sets `r1` to the data's address `da`, changing nothing else but `r12`. -/
def DataA {dn : Nat} (L : Lay dn) (g : Reg → BitVec 32) (m₀ : Mem) (dataA : List Instr) (da : BitVec 32) : Prop :=
  ∀ (u : State) (is : List Instr) (Q : State → Prop), Ctx L g m₀ u →
    (∀ u', Ctx L g m₀ u' → u'.mem = u.mem → u'.gpr .r1 = da → (∀ r, r ≠ .r1 → r ≠ .r12 → u'.gpr r = u.gpr r) →
      WP isa (.block is) u' Q) → WP isa (.block (dataA ++ is)) u Q

theorem append_zero {k : Nat} (hk : k < 2 ^ 32) : (0 : BitVec 32) ++ BitVec.ofNat 32 k = BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_append, BitVec.toNat_ofNat, show (0 : BitVec 32).toNat = 0 from rfl,
    Nat.zero_shiftLeft, Nat.zero_or]
  omega_arith

theorem count_of {s : State} {c : Nat} (hc : c < 2 ^ 32) (h2 : s.gpr .r2 = BitVec.ofNat 32 c) (h3 : s.gpr .r3 = 0) :
    Pbkdf2.Stream.Arm.count s = BitVec.ofNat 64 c := by
  rw [Pbkdf2.Stream.Arm.count, h2, h3]; exact append_zero hc

/-- The arguments of `update`: the state at `scratch + o` holding `cnt`
bytes, the data, its length and the working space. -/
theorem updArgs_ok {u : State} (hc : Ctx L g m₀ u) {o cnt : Nat} (ho : o < 2 ^ 16) {dataA : List Instr}
    {da : BitVec 32} (hdA : DataA L g m₀ dataA da) (hcnt : cnt < 2 ^ 16) {len : Nat} (hlen : len < 2 ^ 16) :
    WP isa (.block (Cfg.updArgs o cnt dataA len)) u fun u' => Ctx L g m₀ u' ∧
      u'.mem = u.mem ∧ u'.gpr .r0 = L.scr + BitVec.ofNat 32 o ∧ u'.gpr .r1 = da ∧
      u'.gpr .r2 = BitVec.ofNat 32 cnt ∧ u'.gpr .r3 = 0 ∧ u'.gpr .r7 = BitVec.ofNat 32 len ∧
      u'.gpr .r10 = L.scr + BitVec.ofNat 32 384 ∧ u'.gpr .r9 = u.gpr .r9 := by
  simp only [Cfg.updArgs, List.append_assoc, List.cons_append, List.nil_append]
  refine scrAt_ok hc (d := .r0) (by decide) (o := o) ho fun t₁ c₁ m₁ v₁ k₁ => ?_
  refine hdA t₁ _ _ c₁ fun t₂ c₂ m₂ v₂ k₂ => ?_
  refine movw_ok c₂ (d := .r2) (by decide) hcnt fun t₃ c₃ m₃ v₃ k₃ => ?_
  refine mov0_ok c₃ (d := .r3) (by decide) fun t₄ c₄ m₄ v₄ k₄ => ?_
  refine movw_ok c₄ (d := .r7) (by decide) hlen fun t₅ c₅ m₅ v₅ k₅ => ?_
  rw [← List.append_nil (scrAt .r10 sWork)]
  refine scrAt_ok c₅ (d := .r10) (by decide) (o := sWork) (by decide) fun t₆ c₆ m₆ v₆ k₆ => ?_
  refine WP.block_nil ⟨c₆, by rw [m₆, m₅, m₄, m₃, m₂, m₁], ?_, ?_, ?_, ?_, ?_, v₆, ?_⟩
  · rw [k₆ _ (by decide) (by decide), k₅ _ (by decide), k₄ _ (by decide), k₃ _ (by decide),
      k₂ _ (by decide) (by decide)]
    exact v₁
  · rw [k₆ _ (by decide) (by decide), k₅ _ (by decide), k₄ _ (by decide), k₃ _ (by decide), v₂]
  · rw [k₆ _ (by decide) (by decide), k₅ _ (by decide), k₄ _ (by decide), v₃]
  · rw [k₆ _ (by decide) (by decide), k₅ _ (by decide), v₄]
  · rw [k₆ _ (by decide) (by decide), v₅]
  · rw [k₆ _ (by decide) (by decide), k₅ _ (by decide), k₄ _ (by decide), k₃ _ (by decide),
      k₂ _ (by decide) (by decide), k₁ _ (by decide) (by decide)]

/-- Where data `update` reads may be: within a buffer or the frame, and
apart from the state it updates, the working space and the stack below the
frame. -/
structure UpdD (P : RfcHash) {dn : Nat} (L : Lay dn) (o : Nat) (da : BitVec 32) (len : Nat) : Prop where
  cov : ∃ R ∈ [L.D, L.DG, L.FR, L.OUT, L.SCR], Within ⟨State.addr da, len⟩ R
  st : Region.Disjoint ⟨State.addr da, len⟩ ⟨State.addr L.scr + BitVec.ofNat 64 o, P.H.S⟩
  wk : Region.Disjoint ⟨State.addr da, len⟩ ⟨State.addr L.scr + BitVec.ofNat 64 384, P.ok.Wb⟩
  low : Region.Disjoint ⟨L.B, 24⟩ ⟨State.addr da, len⟩
  nw : da.toNat + len ≤ 2 ^ 32

/-- The arguments of the streaming `update`, as its frame needs them. -/
theorem updA (hL : L.Ok) {w : State} (hcw : Ctx L g m₀ w) {o : Nat} (ho : o + 192 ≤ 384) {da : BitVec 32}
    {len : Nat} (hd : UpdD P L o da len) (hlen : len < 2 ^ 16)
    (h0 : w.gpr .r0 = L.scr + BitVec.ofNat 32 o) (h1 : w.gpr .r1 = da)
    (h7 : w.gpr .r7 = BitVec.ofNat 32 len) (h10 : w.gpr .r10 = L.scr + BitVec.ofNat 32 384) :
    UpdL P.ok w (L.scr + BitVec.ofNat 32 o) da (L.scr + BitVec.ofNat 32 384) len := by
  have e0 := scrA hL (o := o) (by omega_arith)
  have e3 := scrA hL (o := 384) (by decide)
  have hb := hcw.below_eq hL
  have := hL.nc
  have bsub : Region.Sub ⟨L.B + BitVec.ofNat 64 8, 16⟩ ⟨L.B, 24⟩ := Offset.sub_base _ (by omega_arith)
  exact
    { r0 := h0, r1 := h1, r7 := h7, r10 := h10
      hlen := by omega_arith
      sp16 := by have := hcw.sp24 hL; omega_arith
      cd := hcw.covers fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hd.cov
      cw := hcw.coversW fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [e0]; exact ⟨L.SCR, by simp, within_off _ (by anums)⟩
        · rw [e3]; exact ⟨L.SCR, by simp, within_off _ (by anums)⟩
      st_sc := by rw [e0, e3]; exact Offset.disjoint _ (by anums) (by anums) (by anums)
      d_st := by rw [e0]; exact hd.st
      d_sc := by rw [e3]; exact hd.wk
      b_st := by rw [hb, e0]; exact (low_scr hL (by omega_arith) (by anums)).sub_left bsub
      b_d := by rw [hb]; exact hd.low.sub_left bsub
      b_sc := by rw [hb, e3]; exact (low_scr hL (by omega_arith) (by anums)).sub_left bsub
      nst := by rw [scr_toNat hL (by omega_arith)]; anums
      nd := hd.nw
      nsc := by rw [scr_toNat hL (by decide)]; anums }

/-- `update` of the state at `scratch + o` with `len` bytes at `da`: a
state that represents `cnt` bytes `msg` represents them too. -/
theorem updCall_gen (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) {o cnt : Nat} (ho : o + 192 ≤ 384)
    {dataA : List Instr} {da : BitVec 32} {len : Nat} (hdA : DataA L g m₀ dataA da) (hd : UpdD P L o da len)
    (hcnt : cnt < 2 ^ 16) (hlen : len < 2 ^ 16) :
    WP isa ((cfgOf P).updCall o cnt dataA len) t fun u => Ctx L g m₀ u ∧ u.gpr .r9 = t.gpr .r9 ∧
      Frame [⟨State.addr L.scr + BitVec.ofNat 64 o, P.H.S⟩, ⟨State.addr L.scr + BitVec.ofNat 64 384, P.ok.Wb⟩,
        ⟨L.B, 24⟩] t.mem u.mem ∧
      ∀ msg : List Byte, P.ok.SH.Repr t.mem (State.addr L.scr + BitVec.ofNat 64 o) msg → msg.length = cnt →
        P.ok.SH.Repr u.mem (State.addr L.scr + BitVec.ofNat 64 o)
          (msg ++ Spec.Sha256.bytesAt t.mem (State.addr da) len) := by
  unfold Cfg.updCall
  refine WP.seq (WP.mono (updArgs_ok hc (o := o) (by omega_arith) hdA hcnt hlen)
    fun w ⟨hcw, hmw, h0, h1, h2, h3, h7, h10, h9⟩ =>
    WP.seq (WP.mono (tload_ok hL hcw (r := .r12) (by decide) (j := 1) (by decide)) fun w' ⟨c', m', y', v', k'⟩ => ?_))
  have htm := c'.tabMem
  have hok := c'.tabOk
  rw [hT.1] at htm hok
  rw [hT.2] at hok
  have hn : w'.gpr .r12 = w'.syms P.H.updN := by rw [v']; exact htm.2.1
  refine WP.frame_icalls_of_call (frame_reach (ts := (cfgOf P).f.upd) hok.2.1 hn) ?_
  apply WP.of_syms
  have e0 : State.addr (L.scr + BitVec.ofNat 32 o) = State.addr L.scr + BitVec.ofNat 64 o := scrA hL (by omega_arith)
  have e3 : State.addr (L.scr + BitVec.ofNat 32 384) = State.addr L.scr + BitVec.ofNat 64 384 := scrA hL (by decide)
  refine upd_frame P.ok (updA hL c' ho hd hlen ((k' _ (by decide)).trans h0) ((k' _ (by decide)).trans h1)
    ((k' _ (by decide)).trans h7) ((k' _ (by decide)).trans h10)) fun w'' af hrr sy => ?_
  rw [e0, e3] at af
  rw [e0] at hrr
  have hmem : w'.mem = t.mem := m'.trans hmw
  refine ⟨c'.afterU hL af (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact wk_safe (Offset.sub_base _ (by anums))) sy,
    by rw [af.cs .r9 (by decide) (by decide), k' _ (by decide), h9], ?_, ?_⟩
  · have := frame_call hL c' af
    rwa [hmem] at this
  · intro msg hr hml
    have := hrr msg (by rw [hmem]; exact hr) (by
      rw [count_of (by omega_arith) ((k' _ (by decide)).trans h2) ((k' _ (by decide)).trans h3), hml])
    rwa [hmem] at this

/-- `update` of the state at `scratch + o`, holding the `cnt` bytes `msg`,
with `len` bytes at `da`: the state represents them too. -/
theorem updCall_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) {o cnt : Nat} (ho : o + 192 ≤ 384)
    {dataA : List Instr} {da : BitVec 32} {len : Nat} (hdA : DataA L g m₀ dataA da) (hd : UpdD P L o da len)
    (hcnt : cnt < 2 ^ 16) (hlen : len < 2 ^ 16) {msg : List Byte}
    (hr : P.ok.SH.Repr t.mem (State.addr L.scr + BitVec.ofNat 64 o) msg) (hml : msg.length = cnt) :
    WP isa ((cfgOf P).updCall o cnt dataA len) t fun u => Ctx L g m₀ u ∧ u.gpr .r9 = t.gpr .r9 ∧
      Frame [⟨State.addr L.scr + BitVec.ofNat 64 o, P.H.S⟩, ⟨State.addr L.scr + BitVec.ofNat 64 384, P.ok.Wb⟩,
        ⟨L.B, 24⟩] t.mem u.mem ∧
      P.ok.SH.Repr u.mem (State.addr L.scr + BitVec.ofNat 64 o) (msg ++ Spec.Sha256.bytesAt t.mem (State.addr da) len) :=
  WP.mono (updCall_gen hL hT hc ho hdA hd hcnt hlen) fun _ ⟨c, r, f, h⟩ => ⟨c, r, f, h msg hr hml⟩

/-! ## The streaming `finalize` -/

/-- The arguments of `finalize`: the state at `scratch + o` holding `cnt`
bytes, the output and the working space. -/
theorem finArgs_ok {u : State} (hc : Ctx L g m₀ u) {o cnt : Nat} (ho : o < 2 ^ 16) (hcnt : cnt < 2 ^ 16) :
    WP isa (.block (Cfg.finArgs o cnt)) u fun u' => Ctx L g m₀ u' ∧ u'.mem = u.mem ∧
      u'.gpr .r0 = L.scr + BitVec.ofNat 32 o ∧ u'.gpr .r2 = BitVec.ofNat 32 cnt ∧ u'.gpr .r3 = 0 ∧
      u'.gpr .r1 = L.scr + BitVec.ofNat 32 1920 ∧ u'.gpr .r12 = L.scr + BitVec.ofNat 32 384 ∧
      u'.gpr .r9 = u.gpr .r9 := by
  simp only [Cfg.finArgs, List.append_assoc, List.cons_append, List.nil_append]
  refine scrAt_ok hc (d := .r0) (by decide) (o := o) ho fun t₁ c₁ m₁ v₁ k₁ => ?_
  refine movw_ok c₁ (d := .r2) (by decide) hcnt fun t₂ c₂ m₂ v₂ k₂ => ?_
  refine mov0_ok c₂ (d := .r3) (by decide) fun t₃ c₃ m₃ v₃ k₃ => ?_
  refine scrAt_ok c₃ (d := .r1) (by decide) (o := sTmp) (by decide) fun t₄ c₄ m₄ v₄ k₄ => ?_
  rw [← List.append_nil (scrAt .r12 sWork)]
  refine scrAt_ok c₄ (d := .r12) (by decide) (o := sWork) (by decide) fun t₅ c₅ m₅ v₅ k₅ => ?_
  refine WP.block_nil ⟨c₅, by rw [m₅, m₄, m₃, m₂, m₁], ?_, ?_, ?_, ?_, by rw [v₅]; rfl, ?_⟩
  · rw [k₅ _ (by decide) (by decide), k₄ _ (by decide) (by decide), k₃ _ (by decide), k₂ _ (by decide)]
    exact v₁
  · rw [k₅ _ (by decide) (by decide), k₄ _ (by decide) (by decide), k₃ _ (by decide), v₂]
  · rw [k₅ _ (by decide) (by decide), k₄ _ (by decide) (by decide), v₃]
  · rw [k₅ _ (by decide) (by decide), v₄]; rfl
  · rw [k₅ _ (by decide) (by decide), k₄ _ (by decide) (by decide), k₃ _ (by decide), k₂ _ (by decide),
      k₁ _ (by decide) (by decide)]

/-- The arguments of `finalize`, as its frame needs them. -/
theorem finA (hL : L.Ok) {w : State} (hcw : Ctx L g m₀ w) {o : Nat} (ho : o + 192 ≤ 384)
    (h0 : w.gpr .r0 = L.scr + BitVec.ofNat 32 o) (h1 : w.gpr .r1 = L.scr + BitVec.ofNat 32 1920)
    (h12 : w.gpr .r12 = L.scr + BitVec.ofNat 32 384) :
    FinArgs P.ok w (L.scr + BitVec.ofNat 32 o) (L.scr + BitVec.ofNat 32 1920) (L.scr + BitVec.ofNat 32 384) := by
  have e0 : State.addr (L.scr + BitVec.ofNat 32 o) = State.addr L.scr + BitVec.ofNat 64 o := scrA hL (by omega_arith)
  have e1 : State.addr (L.scr + BitVec.ofNat 32 1920) = State.addr L.scr + BitVec.ofNat 64 1920 := scrA hL (by decide)
  have e3 : State.addr (L.scr + BitVec.ofNat 32 384) = State.addr L.scr + BitVec.ofNat 64 384 := scrA hL (by decide)
  have hb := hcw.below_eq hL
  have := hL.nc
  have bsub : Region.Sub ⟨L.B + BitVec.ofNat 64 8, 16⟩ ⟨L.B, 24⟩ := Offset.sub_base _ (by omega_arith)
  exact
    { r0 := h0, r1 := h1, r12 := h12
      sp16 := by have := hcw.sp24 hL; omega_arith
      cw := hcw.coversW fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [e0]; exact ⟨L.SCR, by simp, within_off _ (by anums)⟩
        · rw [e1]; exact ⟨L.SCR, by simp, within_off _ (by anums)⟩
        · rw [e3]; exact ⟨L.SCR, by simp, within_off _ (by anums)⟩
      st_o := by rw [e0, e1]; exact Offset.disjoint _ (by anums) (by anums) (by anums)
      st_sc := by rw [e0, e3]; exact Offset.disjoint _ (by anums) (by anums) (by anums)
      o_sc := by rw [e1, e3]; exact Offset.disjoint _ (by anums) (by anums) (by anums)
      b_st := by rw [hb, e0]; exact (low_scr hL (by omega_arith) (by anums)).sub_left bsub
      b_o := by rw [hb, e1]; exact (low_scr hL (by omega_arith) (by anums)).sub_left bsub
      b_sc := by rw [hb, e3]; exact (low_scr hL (by omega_arith) (by anums)).sub_left bsub
      nst := by rw [scr_toNat hL (by omega_arith)]; anums
      no := by rw [scr_toNat hL (by decide)]; anums
      nsc := by rw [scr_toNat hL (by decide)]; anums }

/-- `finalize` of the state at `scratch + o` into `scratch + sTmp`: for a
state that represents `cnt` bytes `msg`, its first `D` bytes are the digest. -/
theorem finCall_gen (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) {o cnt : Nat} (ho : o + 192 ≤ 384)
    (hcnt : cnt < 2 ^ 16) :
    WP isa ((cfgOf P).finCall o cnt) t fun u => Ctx L g m₀ u ∧ u.gpr .r9 = t.gpr .r9 ∧
      Frame [⟨State.addr L.scr + BitVec.ofNat 64 o, P.H.S⟩, ⟨State.addr L.scr + BitVec.ofNat 64 1920, P.H.F⟩,
        ⟨State.addr L.scr + BitVec.ofNat 64 384, P.ok.Wb⟩, ⟨L.B, 24⟩] t.mem u.mem ∧
      ∀ msg : List Byte, P.ok.SH.Repr t.mem (State.addr L.scr + BitVec.ofNat 64 o) msg → msg.length = cnt →
        (Spec.Sha256.bytesAt u.mem (State.addr L.scr + BitVec.ofNat 64 1920) P.H.F).take P.H.D =
          P.ok.SH.H.hash msg := by
  unfold Cfg.finCall
  refine WP.seq (WP.mono (finArgs_ok hc (o := o) (by omega_arith) hcnt)
    fun w ⟨hcw, hmw, h0, h2, h3, h1, h12, h9⟩ =>
    WP.seq (WP.mono (tload_ok hL hcw (r := .r7) (by decide) (j := 2) (by decide)) fun w' ⟨c', m', y', v', k'⟩ => ?_))
  have htm := c'.tabMem
  have hok := c'.tabOk
  rw [hT.1] at htm hok
  rw [hT.2] at hok
  have hn : w'.gpr .r7 = w'.syms P.H.finN := by rw [v']; exact htm.2.2
  refine WP.frame_icalls_of_call (frame_reach (ts := (cfgOf P).f.fin) hok.2.2 hn) ?_
  apply WP.of_syms
  have e0 : State.addr (L.scr + BitVec.ofNat 32 o) = State.addr L.scr + BitVec.ofNat 64 o := scrA hL (by omega_arith)
  have e1 : State.addr (L.scr + BitVec.ofNat 32 1920) = State.addr L.scr + BitVec.ofNat 64 1920 := scrA hL (by decide)
  have e3 : State.addr (L.scr + BitVec.ofNat 32 384) = State.addr L.scr + BitVec.ofNat 64 384 := scrA hL (by decide)
  refine fin_frame P.ok (finA hL c' ho ((k' _ (by decide)).trans h0) ((k' _ (by decide)).trans h1)
    ((k' _ (by decide)).trans h12)) fun w'' af hrr sy => ?_
  rw [e0, e1, e3] at af
  rw [e0, e1] at hrr
  have hmem : w'.mem = t.mem := m'.trans hmw
  refine ⟨c'.afterU hL af (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact wk_safe (Offset.sub_base _ (by anums))) sy,
    by rw [af.cs .r9 (by decide) (by decide), k' _ (by decide), h9], ?_, ?_⟩
  · have := frame_call hL c' af
    rwa [hmem] at this
  · intro msg hr hml
    exact hrr msg (by rw [hmem]; exact hr) (by rw [hml]; omega_arith) (by
      rw [count_of (by omega_arith) ((k' _ (by decide)).trans h2) ((k' _ (by decide)).trans h3), hml])

/-- `finalize` of the state at `scratch + o`, holding the `cnt` bytes `msg`,
into `scratch + sTmp`: its first `D` bytes are the digest. -/
theorem finCall_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) {o cnt : Nat} (ho : o + 192 ≤ 384)
    (hcnt : cnt < 2 ^ 16) {msg : List Byte}
    (hr : P.ok.SH.Repr t.mem (State.addr L.scr + BitVec.ofNat 64 o) msg) (hml : msg.length = cnt) :
    WP isa ((cfgOf P).finCall o cnt) t fun u => Ctx L g m₀ u ∧ u.gpr .r9 = t.gpr .r9 ∧
      Frame [⟨State.addr L.scr + BitVec.ofNat 64 o, P.H.S⟩, ⟨State.addr L.scr + BitVec.ofNat 64 1920, P.H.F⟩,
        ⟨State.addr L.scr + BitVec.ofNat 64 384, P.ok.Wb⟩, ⟨L.B, 24⟩] t.mem u.mem ∧
      (Spec.Sha256.bytesAt u.mem (State.addr L.scr + BitVec.ofNat 64 1920) P.H.F).take P.H.D = P.ok.SH.H.hash msg :=
  WP.mono (finCall_gen hL hT hc ho hcnt) fun _ ⟨c, r, f, h⟩ => ⟨c, r, f, h msg hr hml⟩


/-! ## The padded key -/

/-- The first `n` bytes of the key of `D` bytes at `K` (in `m`), padded with
zeros and XORed with `c` in every byte. -/
def padBytes (m : Mem) (K : Addr) (D : Nat) (c : Byte) (n : Nat) : List Byte :=
  (List.range n).map fun i => if i < D then m (K + BitVec.ofNat 64 i) ^^^ c else c

theorem padBytes_length (m : Mem) (K : Addr) (D : Nat) (c : Byte) (n : Nat) : (padBytes m K D c n).length = n := by
  simp [padBytes]

/-- Four more bytes, a word of the key's or of `c`. -/
theorem padBytes_succ (m : Mem) (K : Addr) {D : Nat} (c : Byte) {k : Nat} (hD : D % 4 = 0) :
    padBytes m K D c (4 * k + 4) = padBytes m K D c (4 * k) ++
      (if k < D / 4 then (Spec.Sha256.bytesAt m (K + BitVec.ofNat 64 (4 * k)) 4).map (· ^^^ c)
       else List.replicate 4 c) := by
  simp only [padBytes, List.range_add, List.map_append, List.map_map]
  congr 1
  split
  · simp only [Spec.Sha256.bytesAt, List.map_map]
    refine List.map_congr_left fun j hj => ?_
    have := List.mem_range.mp hj
    simp only [Function.comp, show 4 * k + j < D by omega_arith, ite_true, Offset.add_add]
  · rw [show List.replicate 4 c = (List.range 4).map fun _ => c from rfl]
    refine List.map_congr_left fun j hj => ?_
    have := List.mem_range.mp hj
    simp only [Function.comp, show ¬ 4 * k + j < D by omega_arith, ite_false]

/-- All `B` bytes: `K₀ ⊕ c`, for a key of `D ≤ B` bytes. -/
theorem padBytes_eq (m : Mem) (K : Addr) {D : Nat} (c : Byte) (H : Spec.Hmac.HashFunction)
    (hD : D ≤ H.blockSize) :
    padBytes m K D c H.blockSize = Spec.Hmac.xorPad (Spec.Hmac.blockKey H (Spec.Sha256.bytesAt m K D)) c := by
  rw [Proof.Pbkdf2.MdKeys.blockKey_short H (by simp only [Proof.Hmac.Common.bytesAt_length]; exact hD)]
  apply List.ext_getElem (by simp [padBytes, Spec.Hmac.xorPad, Proof.Hmac.Common.bytesAt_length]; omega_arith)
  intro i h₁ h₂
  simp only [padBytes, List.getElem_map, List.getElem_range, Spec.Hmac.xorPad]
  by_cases hi : i < D
  · rw [List.getElem_append_left (by simp [Proof.Hmac.Common.bytesAt_length, hi])]
    simp [hi, Spec.Sha256.bytesAt]
  · simp only [hi, ite_false]
    rw [List.getElem_append_right (by simp [Proof.Hmac.Common.bytesAt_length]; omega_arith)]
    simp

/-- Word `k` of the padded key, after `4 k` of its bytes. -/
theorem padW_ok {t : State} (P0 K : Addr) (D : Nat) (c : Byte) {k : Nat} (hD : D % 4 = 0) (hk : 4 * k + 4 < 2 ^ 64)
    (hpo : 1792 + 4 * k < 4096)
    {u : State} (hsc : State.addr (u.gpr .r11 + BitVec.ofNat 32 (sPad + 4 * k)) = P0 + BitVec.ofNat 64 (4 * k))
    (hfp : k < D / 4 → State.addr (u.gpr .r8 + BitVec.ofNat 32 (fK + 4 * k)) = K + BitVec.ofNat 64 (4 * k))
    (hc1 : u.gpr .r1 = c ++ c ++ c ++ c)
    (hrK : k < D / 4 → InRegions (u.rd ++ u.wr) (K + BitVec.ofNat 64 (4 * k)) 4)
    (hw : InRegions u.wr (P0 + BitVec.ofNat 64 (4 * k)) 4)
    (hm : u.mem = writeBytes t.mem P0 (padBytes t.mem K D c (4 * k)))
    (hKd : k < D / 4 → Spec.Sha256.bytesAt u.mem (K + BitVec.ofNat 64 (4 * k)) 4 =
      Spec.Sha256.bytesAt t.mem (K + BitVec.ofNat 64 (4 * k)) 4)
    (cf : Cfg) (hcD : cf.D = D) :
    WP isa (.block (cf.padW k)) u fun u' => u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧
      (∀ r, r ≠ .r0 → u'.gpr r = u.gpr r) ∧ u'.mem = writeBytes t.mem P0 (padBytes t.mem K D c (4 * k + 4)) := by
  have hl := padBytes_length t.mem K D c (4 * k)
  have hap : ∀ ys : List Byte, ys.length = 4 →
      writeBytes (writeBytes t.mem P0 (padBytes t.mem K D c (4 * k))) (P0 + BitVec.ofNat 64 (4 * k)) ys =
        writeBytes t.mem P0 (padBytes t.mem K D c (4 * k) ++ ys) := fun ys hys => by
    have := writeBytes_append t.mem P0 (padBytes t.mem K D c (4 * k)) ys (by rw [hl, hys]; omega_arith)
    rwa [hl] at this
  by_cases hkD : k < D / 4
  · rw [Cfg.padW, ite_eq_left_of_eq_true _ _ (eq_true (by rw [hcD]; exact hkD))]
    refine VG.Proof.X25519.Arm.wp_ldr (by simp only [fK]; omega_arith) (hfp hkD) (hrK hkD) fun s₁ u₁ => ?_
    refine Pbkdf2.Stream.Arm.wp_eor (VG.Proof.X25519.Arm.op2_reg _ _) fun s₂ u₂ => ?_
    refine VG.Proof.X25519.Arm.wp_str (a := P0 + BitVec.ofNat 64 (4 * k)) (by simp only [sPad]; omega_arith)
      (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact hsc)
      (by rw [u₂.wr, u₁.wr]; exact hw) fun s₃ m₃ => WP.block_nil ?_
    refine ⟨by rw [m₃.rd, u₂.rd, u₁.rd], by rw [m₃.wr, u₂.wr, u₁.wr], by rw [m₃.sp, u₂.sp, u₁.sp],
      fun r hr => by rw [m₃.gpr, u₂.other r hr, u₁.other r hr], ?_⟩
    rw [m₃.mem, u₂.mem, u₁.mem, u₂.gpr, u₁.gpr, u₁.other .r1 (by decide), hc1,
      Proof.Pbkdf2.MdKeys.writeW_xorRep, hKd hkD, hm, hap _ (by simp [Proof.Hmac.Common.bytesAt_length]),
      padBytes_succ _ _ _ hD, ite_eq_left_of_eq_true _ _ (eq_true hkD)]
  · rw [Cfg.padW, ite_eq_right_of_eq_false _ _ (eq_false (by rw [hcD]; exact hkD))]
    refine VG.Proof.X25519.Arm.wp_str (a := P0 + BitVec.ofNat 64 (4 * k)) (by simp only [sPad]; omega_arith) hsc hw
      fun s₃ m₃ => WP.block_nil ?_
    refine ⟨m₃.rd, m₃.wr, m₃.sp, fun r _ => by rw [m₃.gpr], ?_⟩
    rw [m₃.mem, hc1, Proof.Pbkdf2.MdKeys.writeW_rep, hm, hap _ (by simp), padBytes_succ _ _ _ hD,
      ite_eq_right_of_eq_false _ _ (eq_false hkD)]


/-- The first `k` words of the padded key, from the state `u`. -/
theorem padWs_ok (P0 K : Addr) {D : Nat} (c : Byte) (cf : Cfg) (hcD : cf.D = D)
    (hD : D % 4 = 0) {n : Nat} (hn : n ≤ 32) (hsep : Region.Disjoint ⟨K, D⟩ ⟨P0, 4 * n⟩)
    (hDn : D ≤ 4 * n) (hD64 : D ≤ 64) :
    ∀ k ≤ n, ∀ u : State, (∀ j < n, State.addr (u.gpr .r11 + BitVec.ofNat 32 (sPad + 4 * j)) =
        P0 + BitVec.ofNat 64 (4 * j)) →
      (∀ j < D / 4, State.addr (u.gpr .r8 + BitVec.ofNat 32 (fK + 4 * j)) = K + BitVec.ofNat 64 (4 * j)) →
      u.gpr .r1 = c ++ c ++ c ++ c →
      (∀ j < D / 4, InRegions (u.rd ++ u.wr) (K + BitVec.ofNat 64 (4 * j)) 4) →
      (∀ j < n, InRegions u.wr (P0 + BitVec.ofNat 64 (4 * j)) 4) →
      WP isa (.block ((List.range k).flatMap cf.padW)) u fun u' => u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧
        (∀ r, r ≠ .r0 → u'.gpr r = u.gpr r) ∧ u'.mem = writeBytes u.mem P0 (padBytes u.mem K D c (4 * k))
  | 0, _, u, _, _, _, _, _ => WP.block_nil ⟨rfl, rfl, rfl, fun _ _ => rfl, by simp [padBytes, writeBytes_nil]⟩
  | k + 1, hk, u, hsc, hfp, hc1, hr, hw => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (padWs_ok P0 K c cf hcD hD hn hsep hDn hD64 k (by omega_arith) u hsc hfp hc1 hr hw)
      fun u₁ ⟨hrd₁, hwr₁, hsp₁, hg₁, hm₁⟩ => ?_
    have hf : Frame [⟨P0, 4 * n⟩] u.mem u₁.mem := by
      rw [hm₁]; exact writeBytes_frame _ _ _ (by
        rw [padBytes_length]
        have := Offset.contains_base P0 (d := 0) (n := 4 * k) (k := 4 * n) (by omega_arith) (by omega_arith)
        rwa [BitVec.add_zero] at this)
    refine WP.mono (padW_ok (t := u) P0 K D c (k := k) hD (by omega_arith) (by omega_arith)
      (by rw [hg₁ _ (by decide)]; exact hsc k (by omega_arith))
      (fun hkD => by rw [hg₁ _ (by decide)]; exact hfp k hkD) (by rw [hg₁ _ (by decide)]; exact hc1)
      (fun hkD => by rw [hrd₁, hwr₁]; exact hr k hkD) (by rw [hwr₁]; exact hw k (by omega_arith)) hm₁
      (fun hkD => bytesAt_frame hf (fun r hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact hsep.sub_left (Offset.sub_base _ (by omega_arith))) (by omega_arith)) cf hcD)
      fun u₂ ⟨hrd₂, hwr₂, hsp₂, hg₂, hm₂⟩ => ⟨hrd₂.trans hrd₁, hwr₂.trans hwr₁, hsp₂.trans hsp₁,
        fun r hr' => (hg₂ r hr').trans (hg₁ r hr'), by rw [hm₂, show 4 * (k + 1) = 4 * k + 4 by omega_arith]⟩

theorem ipad32_eq : ((ipad32 >>> 16).setWidth 16 ++ ((ipad32.setWidth 16).setWidth 32).extractLsb' 0 16 : BitVec 32) =
    Spec.Hmac.ipad ++ Spec.Hmac.ipad ++ Spec.Hmac.ipad ++ Spec.Hmac.ipad := by decide
theorem opad32_eq : ((opad32 >>> 16).setWidth 16 ++ ((opad32.setWidth 16).setWidth 32).extractLsb' 0 16 : BitVec 32) =
    Spec.Hmac.opad ++ Spec.Hmac.opad ++ Spec.Hmac.opad ++ Spec.Hmac.opad := by decide

/-- The key `K`: the first `D` bytes of the frame. -/
abbrev keyOf (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) : List Byte :=
  Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 24) P.H.D

/-- Where the padded key is. -/
abbrev padA {dn : Nat} (L : Lay dn) : Addr := State.addr L.scr + BitVec.ofNat 64 1792

/-- `K₀ ⊕ c` at `scratch + sPad`. -/
theorem padBlk_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {x : BitVec 32} {c : Byte}
    (hx : ((x >>> 16).setWidth 16 ++ ((x.setWidth 16).setWidth 32).extractLsb' 0 16 : BitVec 32) = c ++ c ++ c ++ c) :
    WP isa (.block ((cfgOf P).padBlk x)) t fun u => Ctx L g m₀ u ∧ u.gpr .r9 = t.gpr .r9 ∧
      Frame [⟨padA L, P.H.B⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (padA L) P.H.B =
        Spec.Hmac.xorPad (Spec.Hmac.blockKey P.ok.SH.H (keyOf P L t.mem)) c := by
  obtain ⟨_, _, _, hD64, hD4, hDB, hB128, hB4, _, _, _, _, _, hBs⟩ := P.sizes
  have := hL.nc; have := L.he
  rw [Cfg.padBlk, WP.block_append_iff]
  refine WP.of_syms (wp_movwS fun u₁ v₁ => wp_movt' fun u₂ v₂ => WP.block_nil fun hsy => ?_)
  have hc₂ : Ctx L g m₀ u₂ := (hc.upd v₁ (by decide)).upd v₂ (by decide)
  have hc1 : u₂.gpr .r1 = c ++ c ++ c ++ c := by rw [v₂.gpr, v₁.gpr]; exact hx
  have hm₂ : u₂.mem = t.mem := by rw [v₂.mem, v₁.mem]
  have hsep : Region.Disjoint ⟨L.B + BitVec.ofNat 64 24, P.H.D⟩ ⟨padA L, 4 * (P.H.B / 4)⟩ :=
    hL.stk_scr (by anums) (by anums)
  have hW := padWs_ok (padA L) (L.B + BitVec.ofNat 64 24) (D := P.H.D) c (cfgOf P) rfl hD4 (n := P.H.B / 4)
    (by omega_arith) hsep (by omega_arith) hD64 (P.H.B / 4) (Nat.le_refl _) u₂
    (fun j hj => by rw [hc₂.r11, scrA hL (by simp only [sPad]; omega_arith), Offset.add_add]; rfl)
    (fun j hj => by rw [hc₂.r8, hL.fpA (by simp only [fK]; omega_arith), Offset.add_add, fK, Nat.zero_add]) hc1
    (fun j hj => by rw [Offset.add_add]; exact hc₂.inFr (by omega_arith) (by omega_arith))
    (fun j hj => by rw [Offset.add_add]; exact hc₂.inScrW (by omega_arith))
  refine WP.mono_syms hW fun u₃ ⟨hrd₃, hwr₃, hsp₃, hg₃, hm₃⟩ hsy₃ => ?_
  have hf : Frame [⟨padA L, P.H.B⟩] t.mem u₃.mem := by
    rw [hm₃, hm₂]; exact writeBytes_frame _ _ _ (by
      rw [padBytes_length]
      have := Offset.contains_base (padA L) (d := 0) (n := 4 * (P.H.B / 4)) (k := P.H.B) (by omega_arith) (by omega_arith)
      rwa [BitVec.add_zero] at this)
  refine ⟨hc₂.keep hL hrd₃ hwr₃ hsp₃ (fun r hr => hg₃ r (ptr_r0' r hr)) (by rw [hm₂]; exact hf) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L (by omega_arith)) hsy₃,
    by rw [hg₃ _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide)], hf, ?_⟩
  have e4 : 4 * (P.H.B / 4) = P.H.B := by omega_arith
  rw [e4] at hm₃
  rw [hm₃, hm₂, Proof.Hmac.Generic.Common.bytesAt_writeBytes_self' (padBytes_length _ _ _ _ _) (by omega_arith),
    show P.H.B = P.ok.SH.H.blockSize from hBs.symm, padBytes_eq _ _ _ _ (by rw [hBs]; omega_arith)]

/-! ## HMAC's states for the key -/

/-- A state's representation, kept by memory that changed apart from it. -/
theorem repr_keep {m m' : Mem} {ws : List Region} (hf : Frame ws m m') {p : Addr}
    (hd : ∀ r ∈ ws, Region.Disjoint ⟨p, P.H.S⟩ r) {msg : List Byte} (hr : P.ok.SH.Repr m p msg) :
    P.ok.SH.Repr m' p msg :=
  P.ok.repr m m' p p msg (fun i hi => Frame.bytes (R := ⟨p, P.H.S⟩) hf hd (by show P.H.S ≤ 2 ^ 64; anums) hi) hr

/-- A region of `scratch` below `2256`, as part of what HMAC changes. -/
theorem sub_hm {e k : Nat} (h : e + k ≤ 2256) :
    ∃ r' ∈ [WK L, ⟨L.B, 24⟩], Region.Sub ⟨State.addr L.scr + BitVec.ofNat 64 e, k⟩ r' :=
  ⟨_, List.mem_cons_self .., Offset.sub_base _ h⟩

theorem low_hm : ∃ r' ∈ [WK L, ⟨L.B, 24⟩], Region.Sub ⟨L.B, 24⟩ r' :=
  ⟨⟨L.B, 24⟩, by simp, sub_refl _⟩

/-- The key survives what HMAC changes. -/
theorem keyOf_hm (hL : L.Ok) {m m' : Mem} (hf : Frame [WK L, ⟨L.B, 24⟩] m m') :
    keyOf P L m' = keyOf P L m :=
  bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have := hL.stk_scr (d := 24) (n := P.H.D) (e := 0) (k := 2256) (by anums) (by decide)
      rwa [BitVec.add_zero] at this
    · exact Offset.disjoint_base _ (by omega_arith) (by anums)) (by anums)

/-- After `hinit`: HMAC's states for the key `K` in the frame on entry `t`. -/
structure Inited (P : RfcHash) {dn : Nat} (L : Lay dn) (g : Reg → BitVec 32) (m₀ : Mem) (t u : State) : Prop where
  ctx : Ctx L g m₀ u
  r9 : u.gpr .r9 = t.gpr .r9
  frame : Frame [WK L, ⟨L.B, 24⟩] t.mem u.mem
  inner : P.ok.SH.Repr u.mem (State.addr L.scr + BitVec.ofNat 64 0)
    (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.ok.SH.H (keyOf P L t.mem)) Spec.Hmac.ipad)
  outer : P.ok.SH.Repr u.mem (State.addr L.scr + BitVec.ofNat 64 192)
    (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.ok.SH.H (keyOf P L t.mem)) Spec.Hmac.opad)

theorem xorPad_length (k : List Byte) (p : Byte) : (Spec.Hmac.xorPad k p).length = k.length :=
  List.length_map _

theorem keyOf_length (m : Mem) : (keyOf P L m).length = P.H.D := by simp [keyOf, Spec.Sha256.bytesAt]

theorem blockKey_length {k : List Byte} (hk : k.length = P.H.D) :
    (Spec.Hmac.blockKey P.ok.SH.H k).length = P.H.B := by
  obtain ⟨_, _, _, _, _, hDB, _, _, _, _, _, _, _, hB⟩ := P.sizes
  simp only [Spec.Hmac.blockKey, hk, hB, show ¬ P.H.B < P.H.D by omega_arith, ite_false, List.length_append,
    List.length_replicate]
  omega_arith

/-- The padded key, as `update` reads it at `scratch + sPad`. -/
theorem padData (hL : L.Ok) {o : Nat} (ho : o + 192 ≤ 384) :
    UpdD P L o (L.scr + BitVec.ofNat 32 1792) P.H.B := by
  have e := scrA hL (o := 1792) (by decide)
  have := hL.nc
  exact ⟨by rw [e]; exact ⟨L.SCR, by simp, within_off _ (by anums)⟩, by rw [e]; exact Offset.disjoint _ (by anums) (by anums) (by anums),
    by rw [e]; exact Offset.disjoint _ (by anums) (by anums) (by anums), by rw [e]; exact low_scr hL (by omega_arith) (by anums),
    by rw [scr_toNat hL (by decide)]; anums⟩

/-- The address of the data at `scratch + o` in `r1`. -/
theorem scrData {o : Nat} (ho : o < 2 ^ 16) : DataA L g m₀ (scrAt .r1 o) (L.scr + BitVec.ofNat 32 o) :=
  fun _ _ _ hu k => scrAt_ok hu (d := .r1) (by decide) ho fun u' c m v kk => k u' c m v kk

theorem seq_seq {a b c : Prog isa} {s : State} {P Q : State → Prop} (h : WP isa (.seq a b) s P)
    (hc : ∀ s', P s' → WP isa c s' Q) : WP isa (.seq a (.seq b c)) s Q := by
  rw [WP.seq_iff] at h ⊢
  refine WP.mono h fun s₁ h₁ => ?_
  rw [WP.seq_iff]
  exact WP.mono h₁ hc


/-- `hinit`: each state set by `init` and updated with its padded key. -/
theorem init_step (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).hinit t (Inited P L g m₀ t) := by
  obtain ⟨hS, hWb, _, _, _, _, hB128, _, _, _, _, _, _, _⟩ := P.sizes
  have := hL.nc
  have dS : ∀ {a b : Nat}, a + 192 ≤ b ∨ b + 192 ≤ a → b + 192 ≤ 8192 → a + 192 ≤ 8192 →
      Region.Disjoint ⟨State.addr L.scr + BitVec.ofNat 64 a, P.H.S⟩ ⟨State.addr L.scr + BitVec.ofNat 64 b, P.H.S⟩ :=
    fun h hb ha => Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
  unfold Cfg.hinit
  refine WP.seq (WP.mono (initCall_ok hL hT hc (o := 0) (by decide)) fun u₁ ⟨hc₁, h9₁, hf₁, hr₁⟩ => ?_)
  refine WP.seq (WP.mono (initCall_ok hL hT hc₁ (o := 192) (by decide)) fun u₂ ⟨hc₂, h9₂, hf₂, hr₂⟩ => ?_)
  have hr₁' := repr_keep hf₂ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dS (.inl (by decide)) (by decide) (by decide)
    · exact (low_scr hL (by omega_arith) (by anums)).symm) hr₁
  have hF₂ : Frame [WK L, ⟨L.B, 24⟩] t.mem u₂.mem :=
    (hf₁.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sub_hm (by anums)
      · exact low_hm).trans (hf₂.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sub_hm (by anums)
      · exact low_hm)
  have hk₂ : keyOf P L u₂.mem = keyOf P L t.mem := keyOf_hm hL hF₂
  refine WP.seq (WP.mono (padBlk_ok (P := P) hL hc₂ ipad32_eq) fun u₃ ⟨hc₃, h9₃, hf₃, hb₃⟩ => ?_)
  have dP : ∀ {a : Nat}, a + 192 ≤ 384 →
      Region.Disjoint ⟨State.addr L.scr + BitVec.ofNat 64 a, P.H.S⟩ ⟨padA L, P.H.B⟩ :=
    fun h => Offset.disjoint _ (by anums) (by anums) (by anums)
  have hr₁₃ := repr_keep hf₃ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dP (by decide)) hr₁'
  have hr₂₃ := repr_keep hf₃ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dP (by decide)) hr₂
  refine WP.seq (WP.mono (updCall_ok hL hT hc₃ (o := 0) (by decide) (scrData (by decide)) (padData hL (by decide))
    (by anums) (by anums) hr₁₃ rfl) fun u₄ ⟨hc₄, h9₄, hf₄, hr₄⟩ => ?_)
  have dW : ∀ {a : Nat}, a + 192 ≤ 384 → ∀ {b : Nat}, b + 192 ≤ 384 → a + 192 ≤ b ∨ b + 192 ≤ a →
      ∀ r ∈ [(⟨State.addr L.scr + BitVec.ofNat 64 b, P.H.S⟩ : Region),
        ⟨State.addr L.scr + BitVec.ofNat 64 384, P.ok.Wb⟩, ⟨L.B, 24⟩],
        Region.Disjoint ⟨State.addr L.scr + BitVec.ofNat 64 a, P.H.S⟩ r := fun ha b hb hab r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact dS hab (by omega_arith) (by omega_arith)
    · exact Offset.disjoint _ (by anums) (by anums) (by anums)
    · exact (low_scr hL (by omega_arith) (by anums)).symm
  have hr₂₄ := repr_keep hf₄ (dW (a := 192) (by decide) (b := 0) (by decide) (.inr (by decide))) hr₂₃
  have hF₄ : Frame [WK L, ⟨L.B, 24⟩] t.mem u₄.mem :=
    (hF₂.trans (hf₃.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact sub_hm (by anums))).trans (hf₄.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub_hm (by anums)
      · exact sub_hm (by anums)
      · exact low_hm)
  have hk₄ : keyOf P L u₄.mem = keyOf P L t.mem := keyOf_hm hL hF₄
  refine WP.seq (WP.mono (padBlk_ok (P := P) hL hc₄ opad32_eq) fun u₅ ⟨hc₅, h9₅, hf₅, hb₅⟩ => ?_)
  have hr₁₅ := repr_keep hf₅ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dP (by decide)) hr₄
  have hr₂₅ := repr_keep hf₅ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dP (by decide)) hr₂₄
  refine WP.mono (updCall_ok hL hT hc₅ (o := 192) (by decide) (scrData (by decide)) (padData hL (by decide))
    (by anums) (by anums) hr₂₅ rfl) fun u₆ ⟨hc₆, h9₆, hf₆, hr₆⟩ => ?_
  have hr₁₆ := repr_keep hf₆ (dW (a := 0) (by decide) (b := 192) (by decide) (.inl (by decide))) hr₁₅
  have e : State.addr (L.scr + BitVec.ofNat 32 1792) = padA L := scrA hL (by decide)
  refine ⟨hc₆, by rw [h9₆, h9₅, h9₄, h9₃, h9₂, h9₁], (hF₄.trans (hf₅.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact sub_hm (by anums))).trans (hf₆.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub_hm (by anums)
      · exact sub_hm (by anums)
      · exact low_hm), ?_, ?_⟩
  · rw [List.nil_append, e, hb₃, hk₂] at hr₁₆; exact hr₁₆
  · rw [List.nil_append, e, hb₅, hk₄] at hr₆; exact hr₆

/-! ## The data -/

/-- Where the data may be: in the frame below `out`, or in `scratch` above
HMAC's working space. -/
def DataOk {dn : Nat} (L : Lay dn) (da : BitVec 32) (len : Nat) : Prop :=
  (∃ o, da = L.fp + BitVec.ofNat 32 o ∧ o + len ≤ 176) ∨
    (∃ o, da = L.scr + BitVec.ofNat 32 o ∧ 2256 ≤ o ∧ o + len < 8192)

namespace DataOk

variable {da : BitVec 32} {len : Nat}

theorem addr (hd : DataOk L da len) (hL : L.Ok) :
    (∃ o, State.addr da = L.B + BitVec.ofNat 64 o ∧ 24 ≤ o ∧ o + len ≤ 200) ∨
      (∃ o, State.addr da = State.addr L.scr + BitVec.ofNat 64 o ∧ 2256 ≤ o ∧ o + len ≤ 8192) := by
  rcases hd with ⟨o, rfl, h⟩ | ⟨o, rfl, h₁, h₂⟩
  · exact .inl ⟨24 + o, hL.fpA (by omega_arith), by omega_arith, by omega_arith⟩
  · exact .inr ⟨o, scrA hL (by omega_arith), h₁, by omega_arith⟩

theorem nowrap (hd : DataOk L da len) (hL : L.Ok) : da.toNat + len ≤ 2 ^ 32 := by
  have := hL.nc; have := hL.nB; have := L.sp.isLt
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

theorem upd (hd : DataOk L da len) (hL : L.Ok) : UpdD P L 0 da len where
  cov := hd.within hL
  st := hd.work hL (by anums)
  wk := hd.work hL (by anums)
  low := hd.low hL
  nw := hd.nowrap hL

/-- The data survives what HMAC changes. -/
theorem keep (hd : DataOk L da len) (hL : L.Ok) {m m' : Mem} (hf : Frame [WK L, ⟨L.B, 24⟩] m m') :
    Spec.Sha256.bytesAt m' (State.addr da) len = Spec.Sha256.bytesAt m (State.addr da) len :=
  bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa using hd.work hL (e := 0) (k := 2256) (by omega_arith)
    · exact (hd.low hL).symm) (by
      rcases hd with ⟨o, -, h⟩ | ⟨o, -, -, h⟩ <;> omega_arith)

end DataOk

/-- After `hupd`: the inner state holds the data too. -/
structure Updated (P : RfcHash) {dn : Nat} (L : Lay dn) (g : Reg → BitVec 32) (m₀ : Mem) (t : State)
    (da : BitVec 32) (len : Nat) (u : State) : Prop where
  ctx : Ctx L g m₀ u
  r9 : u.gpr .r9 = t.gpr .r9
  frame : Frame [WK L, ⟨L.B, 24⟩] t.mem u.mem
  inner : P.ok.SH.Repr u.mem (State.addr L.scr + BitVec.ofNat 64 0)
    (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.ok.SH.H (keyOf P L t.mem)) Spec.Hmac.ipad ++
      Spec.Sha256.bytesAt t.mem (State.addr da) len)
  outer : P.ok.SH.Repr u.mem (State.addr L.scr + BitVec.ofNat 64 192)
    (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.ok.SH.H (keyOf P L t.mem)) Spec.Hmac.opad)

theorem upd_step (hL : L.Ok) (hT : TabL P L) {t u : State} (hu : Inited P L g m₀ t u) {dataA : List Instr}
    {da : BitVec 32} {len : Nat} (hdA : DataA L g m₀ dataA da) (hd : DataOk L da len) (hlen : len ≤ 256) :
    WP isa ((cfgOf P).hupd dataA len) u (Updated P L g m₀ t da len) := by
  have := hL.nc
  refine WP.mono (updCall_ok hL hT hu.ctx (o := 0) (cnt := P.H.B) (by decide) hdA (hd.upd hL) (by anums)
    (by omega_arith) hu.inner
    (by rw [xorPad_length, blockKey_length (keyOf_length _)])) fun w ⟨hcw, h9w, hfw, hrw⟩ => ?_
  refine ⟨hcw, by rw [h9w, hu.r9], hu.frame.trans (hfw.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub_hm (by anums)
      · exact sub_hm (by anums)
      · exact low_hm), by rw [← hd.keep hL hu.frame]; exact hrw, repr_keep hfw (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint _ (by anums) (by anums) (by anums)
    · exact Offset.disjoint _ (by anums) (by anums) (by anums)
    · exact (low_scr hL (by omega_arith) (by anums)).symm) hu.outer⟩

/-! ## The MAC -/

/-- After `hfin`: the MAC in the frame at `dst`. -/
structure Done (P : RfcHash) {dn : Nat} (L : Lay dn) (g : Reg → BitVec 32) (m₀ : Mem) (t : State)
    (da : BitVec 32) (len dst : Nat) (u : State) : Prop where
  ctx : Ctx L g m₀ u
  r9 : u.gpr .r9 = t.gpr .r9
  frame : Frame [WK L, ⟨L.B, 24⟩, ⟨L.B + BitVec.ofNat 64 (24 + dst), P.H.D⟩] t.mem u.mem
  mac : Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (24 + dst)) P.H.D =
    P.mac (keyOf P L t.mem) (Spec.Sha256.bytesAt t.mem (State.addr da) len)

/-- Where `finalize` writes. -/
abbrev tmpA {dn : Nat} (L : Lay dn) : Addr := State.addr L.scr + BitVec.ofNat 64 1920

/-- The first `D` bytes `finalize` wrote: the digest. -/
theorem tmp_digest {m : Mem} {msg : List Byte}
    (h : (Spec.Sha256.bytesAt m (tmpA L) P.H.F).take P.H.D = P.ok.SH.H.hash msg) :
    Spec.Sha256.bytesAt m (tmpA L) P.H.D = P.ok.SH.H.hash msg := by
  rw [bytesAt_take _ _ (show P.H.D ≤ P.H.F from P.ok.hDF)]; exact h

/-- What `finalize` writes and the working space, within what HMAC changes. -/
theorem fin_hm {o : Nat} (ho : o + 192 ≤ 384) : ∀ r ∈ [(⟨State.addr L.scr + BitVec.ofNat 64 o, P.H.S⟩ : Region),
    ⟨tmpA L, P.H.F⟩, ⟨State.addr L.scr + BitVec.ofNat 64 384, P.ok.Wb⟩, ⟨L.B, 24⟩],
    ∃ r' ∈ [WK L, ⟨L.B, 24⟩], Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact sub_hm (by anums)
  · exact sub_hm (by anums)
  · exact sub_hm (by anums)
  · exact low_hm

/-- The MAC's `D` bytes, from `scratch + sTmp` to the frame at `dst`. -/
theorem hcopy_ok (hL : L.Ok) {w : State} (hc : Ctx L g m₀ w) {dst : Nat} (hdst : dst + P.H.D ≤ 176) :
    WP isa (.block (Cfg.copyN ((cfgOf P).D / 4) .r11 sTmp .r8 dst)) w fun w' => Ctx L g m₀ w' ∧
      w'.gpr .r9 = w.gpr .r9 ∧ Frame [⟨L.B + BitVec.ofNat 64 (24 + dst), P.H.D⟩] w.mem w'.mem ∧
      Spec.Sha256.bytesAt w'.mem (L.B + BitVec.ofNat 64 (24 + dst)) P.H.D =
        Spec.Sha256.bytesAt w.mem (State.addr L.scr + BitVec.ofNat 64 1920) P.H.D := by
  have := hL.nc; have := L.sp.isLt; have := hL.nB; have := L.he
  obtain ⟨_, _, _, hD64, hD4, -⟩ := P.sizes
  have e4 : 4 * (P.H.D / 4) = P.H.D := by omega_arith
  have hsep : Region.Disjoint ⟨State.addr L.scr + BitVec.ofNat 64 1920, 4 * (P.H.D / 4)⟩
      ⟨State.addr L.fp + BitVec.ofNat 64 dst, 4 * (P.H.D / 4)⟩ := by
    rw [hL.fpA0, Offset.add_add, e4]; exact (hL.stk_scr (by omega_arith) (by omega_arith)).symm
  have hfpn : L.fp.toNat = L.sp.toNat - (216 + 4 * L.e) := VG.Arm.FrameStack.sub_toNat' (by omega_arith)
  refine WP.mono_syms (copyN_ok (src := .r11) (dst := .r8) (S := L.scr) (D := L.fp) (so := 1920) (d := dst)
    (K := P.H.D / 4) (by decide) (by decide) hsep (by omega_arith) (by rw [hfpn]; omega_arith) (by omega_arith)
    (by omega_arith) (P.H.D / 4) (Nat.le_refl _) w hc.r11 hc.r8
    (fun j hj => hc.inScr (by omega_arith)) (fun j hj => by
      rw [hL.fpA0, Offset.add_add]; exact hc.inFrW (by omega_arith) (by omega_arith)))
    fun w₅ ⟨hrd₅, hwr₅, hsp₅, hg₅, hf₅, hb₅⟩ hsy₅ => ?_
  rw [hL.fpA0, Offset.add_add, e4] at hf₅ hb₅
  exact ⟨hc.keep hL hrd₅ hwr₅ hsp₅ (fun r hr => hg₅ r (ptr_r0' r hr)) hf₅
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by omega_arith)) hsy₅,
    hg₅ _ (by decide), hf₅, hb₅⟩

theorem fin_step (hL : L.Ok) (hT : TabL P L) {t u : State} {da : BitVec 32} {len dst : Nat}
    (hu : Updated P L g m₀ t da len u) (hlen : len ≤ 256) (hdst : dst + P.H.D ≤ 176) :
    WP isa ((cfgOf P).hfin len dst) u (Done P L g m₀ t da len dst) := by
  have := hL.nc; have := L.sp.isLt; have := hL.nB; have := L.he
  have hkl := blockKey_length (P := P) (keyOf_length (L := L) t.mem)
  have hdl : (Spec.Sha256.bytesAt t.mem (State.addr da) len).length = len := by simp [Spec.Sha256.bytesAt]
  unfold Cfg.hfin
  refine WP.seq (WP.mono (finCall_ok hL hT hu.ctx (o := 0) (by decide) (cnt := P.H.B + len) (by anums) hu.inner
    (by rw [List.length_append, xorPad_length, hkl, hdl])) fun w₁ ⟨hc₁, h9₁, hf₁, hd₁⟩ => ?_)
  have hd₁' := tmp_digest hd₁
  have ho₁ := repr_keep hf₁ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Offset.disjoint _ (by anums) (by anums) (by anums)
    · exact Offset.disjoint _ (by anums) (by anums) (by anums)
    · exact Offset.disjoint _ (by anums) (by anums) (by anums)
    · exact (low_scr hL (by omega_arith) (by anums)).symm) hu.outer
  have e1 : State.addr (L.scr + BitVec.ofNat 32 1920) = tmpA L := scrA hL (by decide)
  have tmpD : UpdD P L 192 (L.scr + BitVec.ofNat 32 1920) P.H.D :=
    ⟨by rw [e1]; exact ⟨L.SCR, by simp, within_off _ (by anums)⟩,
      by rw [e1]; exact Offset.disjoint _ (by anums) (by anums) (by anums),
      by rw [e1]; exact Offset.disjoint _ (by anums) (by anums) (by anums),
      by rw [e1]; exact low_scr hL (by omega_arith) (by anums), by rw [scr_toNat hL (by decide)]; anums⟩
  refine WP.seq (WP.mono (updCall_ok hL hT hc₁ (o := 192) (cnt := P.H.B) (by decide) (scrData (by decide)) tmpD
    (by anums) (by anums) ho₁ (by rw [xorPad_length, hkl])) fun w₂ ⟨hc₂, h9₂, hf₂, hr₂⟩ => ?_)
  rw [e1, hd₁'] at hr₂
  refine WP.seq (WP.mono (finCall_ok hL hT hc₂ (o := 192) (by decide) (cnt := P.H.B + P.H.D) (by anums) hr₂
    (by rw [List.length_append, xorPad_length, hkl, P.macLen])) fun w₃ ⟨hc₃, h9₃, hf₃, hd₃⟩ => ?_)
  have hd₃' := tmp_digest hd₃
  refine WP.mono (hcopy_ok hL hc₃ hdst) fun w₅ ⟨hc₅, h9₅, hf₅, hb₅⟩ => ⟨hc₅, by rw [h9₅, h9₃, h9₂, h9₁, hu.r9], ?_, ?_⟩
  · have e : ∀ {r : Region}, (∃ r' ∈ [WK L, ⟨L.B, 24⟩], Region.Sub r r') →
        ∃ r' ∈ [WK L, ⟨L.B, 24⟩, ⟨L.B + BitVec.ofNat 64 (24 + dst), P.H.D⟩], Region.Sub r r' :=
      fun ⟨r', hr', hs⟩ => ⟨r', by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr' ⊢; rcases hr' with h | h <;> simp [h], hs⟩
    refine ((((hu.frame.sub fun r hr => e ⟨r, hr, sub_refl _⟩).trans (hf₁.sub fun r hr => e (fin_hm (by decide) r hr))).trans
      (hf₂.sub fun r hr => e ?_)).trans (hf₃.sub fun r hr => e (fin_hm (by decide) r hr))).trans ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub_hm (by anums)
      · exact sub_hm (by anums)
      · exact low_hm
    · exact hf₅.sub fun r hr => ⟨r, by simp_all, sub_refl _⟩
  · rw [hb₅, hd₃']
    rfl

/-! ## The whole HMAC -/

/-- `HMAC_K(data)`, for the key `K` in the frame, to the frame at `dst`. -/
theorem hmac_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) {dataA : List Instr} {da : BitVec 32}
    {len dst : Nat} (hdA : DataA L g m₀ dataA da) (hd : DataOk L da len) (hlen : len ≤ 256)
    (hdst : dst + P.H.D ≤ 176) :
    WP isa ((cfgOf P).hmac dataA len dst) t (Done P L g m₀ t da len dst) :=
  WP.seq (WP.mono (init_step hL hT hc) fun _ hu => WP.seq (WP.mono (upd_step hL hT hu hdA hd hlen) fun _ hw =>
    fin_step hL hT hw hlen hdst))

end VG.Proof.Ecdsa.Rfc6979.Arm

