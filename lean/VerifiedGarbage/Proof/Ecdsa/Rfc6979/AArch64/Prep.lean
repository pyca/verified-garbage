module

-- separate module: its proofs (the buffers X and h) build in parallel with `Steps`, which `Cand` also imports
public import VerifiedGarbage.Proof.Mont.AArch64.Words
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Weierstrass.AArch64.BytesLen
import Mathlib.Logic.Function.Basic
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Copy
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Msg
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Reduce
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import Mathlib.Tactic.Conv
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Loops
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Hash
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Regs
public import VerifiedGarbage.Proof.Framework.ICall

/-! ### `Ecdsa.Rfc6979.AArch64.Steps`, which this module and modules that import it used -/

section

/-! ### `Ecdsa.Rfc6979.AArch64.Hmac`, which only this module used -/

section

/-!
# Deterministic ECDSA on AArch64: HMAC through the table

The table's functions, each called indirectly (`tcall_ok`: the table's word,
which `Ctx` says holds the function of `L.H`, whose call an indirect call of
`L.f`'s functions reaches), with the lengths and counts the frame's `D` and
`B` give (`ldF_ok`, `add_ok`), as on x86-64
(`Proof/Ecdsa/Rfc6979/X86_64/Hmac.lean`):

* HMAC's `init` with the key `K` (`D` bytes, the frame's first): HMAC's states
  for the block key `K₀` of `K` (`init_step`);
* the streaming `update` of the inner state with `len` bytes of data in the
  frame below its pointers or in `scratch` above HMAC's working space
  (`DataOk`), the inner state holding `K₀ ⊕ ipad ‖ text`, of `B + |text|`
  bytes: it then holds the data after `text` (`upd_call_ok`), with `V`
  (`updV_step`) or with the message at `scratch + sMsg` (`updM_step`);
* HMAC's `finalize`, with the count `B + D + len` for a text of that length,
  writing `HMAC(K₀, text)` (`D` bytes) to the frame at `dst` (`fin_step`).

`St P L g m₀ k0 text` is what holds between them: `Ctx`, and HMAC's states
for `K₀` with the inner one holding `text`. They change only HMAC's states
and working space (the first 2256 bytes of `scratch`), the 16 bytes below
the frame (`W`), and `dst`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64
open VG.Proof.Pbkdf2.Md.AArch64.Calls (After)

/-- Where the data may be: in the frame below its pointers, or in `scratch`
above HMAC's working space. -/
def DataOk {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (da : Addr) (len : Nat) : Prop :=
  (∃ o, da = L.B + BitVec.ofNat 64 o ∧ 16 ≤ o ∧ o + len ≤ 200) ∨
    (∃ o, da = L.scr + BitVec.ofNat 64 o ∧ 2256 ≤ o ∧ o + len ≤ 8192)

variable {P : RfcHash} {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} {L : Lay dn E} {g : Reg → BitVec 64} {m₀ : Mem}

namespace DataOk

variable {da : Addr} {len : Nat}

theorem low (hd : DataOk L da len) (hL : L.Ok) : Region.Disjoint ⟨L.B, 16⟩ ⟨da, len⟩ := by
  rcases hd with ⟨o, rfl, h₁, h₂⟩ | ⟨o, rfl, h₁, h₂⟩
  · exact Offset.base_disjoint _ h₁ (by omega_using [h₂])
  · exact hL.low_scr h₂

/-- The data is apart from HMAC's states and working space. -/
theorem work (hd : DataOk L da len) (hL : L.Ok) {e k : Nat} (h : e + k ≤ 2256) :
    Region.Disjoint ⟨da, len⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ := by
  rcases hd with ⟨o, rfl, h₁, h₂⟩ | ⟨o, rfl, h₁, h₂⟩
  · exact hL.stk_scr (by have := L.he; omega_using [h₂]) (by omega_using [h])
  · exact Offset.disjoint _ (by omega_using [h, h₁]) (by omega_using [h₂]) (by omega_using [h])

theorem within (hd : DataOk L da len) :
    ∃ R ∈ [L.D, L.DG, L.FR, L.OUT, L.SCR], Within ⟨da, len⟩ R := by
  rcases hd with ⟨o, rfl, h₁, h₂⟩ | ⟨o, rfl, h₁, h₂⟩
  · exact ⟨L.FR, by simp, within_fr _ h₁ (by omega_using [h₂])⟩
  · exact ⟨L.SCR, by simp, within_off _ h₂⟩

end DataOk

theorem Ctx.sp16 (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) : 16 ≤ u.sp.toNat := by
  rw [hc.sp, toNat_add_of (by have := hL.nB; omega_using [this])]; omega_using []

/-! ## Loads from the frame, and sums -/

/-- `d ← [sp + o]`, a word of the frame. -/
theorem ldF_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {d : Reg} (hd : d ∉ preserved) {o : Nat}
    (ho : o + 8 ≤ 224 + 8 * L.e) (h8 : o % 8 = 0) :
    WP isa (.block [.ldrSp d o]) u (Upd L g m₀ u d (u.mem.readW (L.B + BitVec.ofNat 64 (16 + o)) 64)) := by
  have hr := hc.inFr (d := 16 + o) (by omega_using []) (by omega_using [ho])
  have ho' : o < 32768 := by have := L.he; omega_using [ho, this]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.load,
    BitVec.setWidth_eq, hc.sp, Offset.add_add, h8, ho', and_self, hr, ite_true, Option.map_some, read8,
    Option.some.injEq, exists_eq_left']
  exact ⟨hc.set hL hd rfl rfl rfl rfl (fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr) rfl, rfl,
    by rw [RegUpd.gpr_write_self]; exact BitVec.setWidth_eq _, fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr⟩

/-- `d ← d + r`. -/
theorem add_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {d r : Reg} (hd : d ∉ preserved) :
    WP isa (.block [.add .x d d r]) u (Upd L g m₀ u d (u.gpr d + u.gpr r)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits, BitVec.setWidth_eq,
    Option.some.injEq, exists_eq_left']
  exact ⟨hc.set hL hd rfl rfl rfl rfl (fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr) rfl, rfl,
    by rw [RegUpd.gpr_write_self]; exact BitVec.setWidth_eq _, fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr⟩

/-- `d ← d + n`. -/
theorem addI_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {d : Reg} (hd : d ∉ preserved) {n : Nat}
    (hn : n < 4096) :
    WP isa (.block [.addImm .x d d n]) u (Upd L g m₀ u d (u.gpr d + BitVec.ofNat 64 n)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, hn, ite_true, State.read, Size.bits,
    BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  exact ⟨hc.set hL hd rfl rfl rfl rfl (fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr) rfl, rfl,
    by rw [RegUpd.gpr_write_self]; exact BitVec.setWidth_eq _, fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr⟩

/-! ## The table -/

/-- The layout's table is of `P`'s hash function and functions. -/
def TabL (P : RfcHash) {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) : Prop := L.H = P.H ∧ L.f = P.f

/-- The frame's `D`. -/
theorem Ctx.dl (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) :
    t.mem.readW (L.B + BitVec.ofNat 64 (16 + fDl)) 64 = BitVec.ofNat 64 P.H.D := by
  rw [← hT.1]; exact hc.pDl

/-- The frame's `B`. -/
theorem Ctx.bl (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) :
    t.mem.readW (L.B + BitVec.ofNat 64 (16 + fBl)) 64 = BitVec.ofNat 64 P.H.P.B := by
  rw [← hT.1]; exact hc.pBl

/-- `d ← D`, from the frame. -/
theorem ldD_ok (hL : L.Ok) (hT : TabL P L) {u : State} (hc : Ctx L g m₀ u) {d : Reg} (hd : d ∉ preserved) :
    WP isa (.block [.ldrSp d fDl]) u (Upd L g m₀ u d (BitVec.ofNat 64 P.H.D)) :=
  WP.mono (ldF_ok hL hc hd (o := fDl) (by simp only [fDl]; have := L.he; omega_using []) rfl) fun _ h =>
    ⟨h.ctx, h.mem, h.val.trans (hc.dl hT), h.keep⟩

/-- `d ← B`, from the frame. -/
theorem ldB_ok (hL : L.Ok) (hT : TabL P L) {u : State} (hc : Ctx L g m₀ u) {d : Reg} (hd : d ∉ preserved) :
    WP isa (.block [.ldrSp d fBl]) u (Upd L g m₀ u d (BitVec.ofNat 64 P.H.P.B)) :=
  WP.mono (ldF_ok hL hc hd (o := fBl) (by simp only [fBl]; have := L.he; omega_using [this]) rfl) fun _ h =>
    ⟨h.ctx, h.mem, h.val.trans (hc.bl hT), h.keep⟩

/-- The table's word `j` into `x16`, through its address in the frame. -/
theorem tblk_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {j : Nat} (hj : 8 * j + 8 ≤ 48) :
    WP isa (.block [.ldrSp .x16 fTab, .ldr .x .x16 .x16 (8 * j)]) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧
      t'.gpr .x16 = m₀.readW (L.tab + BitVec.ofNat 64 (8 * j)) 64 ∧ (∀ r, r ≠ .x16 → t'.gpr r = t.gpr r) ∧
      t'.syms = t.syms := by
  rw [show ([.ldrSp .x16 fTab, .ldr .x .x16 .x16 (8 * j)] : List Instr) =
    [.ldrSp .x16 fTab] ++ [.ldr .x .x16 .x16 (8 * j)] from rfl, WP.block_append_iff]
  have he := L.he
  refine WP.mono_syms (ldF_ok hL hc (d := .x16) (by decide) (o := fTab) (by simp only [fTab, extra]; omega_using [he]) rfl)
    fun t₁ h₁ hs₁ => ?_
  have h16 : t₁.gpr .x16 = L.tab := by
    rw [h₁.val, show 16 + fTab = 232 + 8 * L.e by simp only [fTab, extra]; omega_using [he]]; exact hc.pTab
  have ht := h₁.ctx.inTab hL (o := 8 * j) hj
  have hj' : 8 * j < 32768 := by omega_using [hj]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes, Nat.mul_mod_right, hj', and_self,
    ite_true, Option.bind_some, State.load, Size.bits, BitVec.setWidth_eq, h16, ht, Option.map_some,
    read8, h₁.ctx.tab_word hL hj, Option.some.injEq, exists_eq_left']
  refine ⟨h₁.ctx.set hL (d := .x16) (by decide) rfl rfl rfl rfl (fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr) rfl,
    h₁.mem, by rw [RegUpd.gpr_write_self]; exact BitVec.setWidth_eq _, fun r hr => ?_, hs₁⟩
  rw [RegUpd.gpr_write_of_ne _ _ _ hr, h₁.keep r hr]

/-- The indirect call of the table's function `j`, at the address its word
`j` holds, of `n`. -/
theorem tcall_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {j : Nat} (hj : 8 * j + 8 ≤ 48)
    {n : String} {c : Prog isa} {ts : List (String × Prog isa)}
    (hw : m₀.readW (L.tab + BitVec.ofNat 64 (8 * j)) 64 = t.syms n)
    (hf : ts.find? (fun q => t.syms q.1 == t.syms n) = some (n, c)) {Q : State → Prop}
    (h : ∀ t', Ctx L g m₀ t' → t'.mem = t.mem → (∀ r, r ≠ .x16 → t'.gpr r = t.gpr r) → t'.syms = t.syms →
      WP isa (.call n c) t' Q) :
    WP isa (Cfg.tcall j ts) t Q := by
  unfold Cfg.tcall
  refine WP.seq (WP.mono (tblk_ok hL hc hj) fun t' ⟨hc', hm, h16, hk, hsy⟩ => ?_)
  refine WP.icalls_of_call (a := t.syms n) (by simp only [icall, h16, hw]) ?_ (h t' hc' hm hk hsy)
  show ts.find? (fun q => isa.fnAddr t' q.1 == t.syms n) = _
  simp only [isa]; rw [hsy]; exact hf

/-! ## HMAC's states -/

/-- The key `K`: the first `D` bytes of the frame. -/
abbrev keyOf (P : RfcHash) {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (m : Mem) : List Byte :=
  Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 16) P.H.D

/-- HMAC's states for the block key `k0`, the inner one holding `text`
after `K₀ ⊕ ipad`. -/
structure St (P : RfcHash) {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (g : Reg → BitVec 64)
    (m₀ : Mem) (k0 text : List Byte) (u : State) : Prop where
  ctx : Ctx L g m₀ u
  klen : k0.length = P.H.P.B
  tlen : text.length ≤ 512
  inner : P.ok.SH.Repr u.mem (L.scr + BitVec.ofNat 64 0) (Spec.Hmac.xorPad k0 Spec.Hmac.ipad ++ text)
  outer : P.ok.SH.Repr u.mem (L.scr + BitVec.ofNat 64 192) (Spec.Hmac.xorPad k0 Spec.Hmac.opad)

/-- What HMAC's functions write: their states and working space, and the
stack below the frame. -/
abbrev W {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) : List Region := [⟨L.scr, 2256⟩, ⟨L.B, 16⟩]

theorem scr_work {e k : Nat} (h : e + k ≤ 2256) : Region.Sub ⟨L.scr + BitVec.ofNat 64 e, k⟩ ⟨L.scr, 2256⟩ :=
  Offset.sub_base _ h

/-- What a call leaves keeps `Ctx`, if it writes only safe regions and the
16 bytes below the frame. -/
theorem Ctx.after (hL : L.Ok) {u u' : State} (hc : Ctx L g m₀ u) {ws : List Region} (ha : After u ws u')
    (hs : ∀ r ∈ ws, Safe L r) : Ctx L g m₀ u' :=
  hc.keep hL ha.rd ha.wr ha.sp ha.cs ha.frame (hsy := ha.syms) fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact hs r hr
    · simp only [List.mem_singleton] at hr; subst hr
      rw [hc.below_eq]
      exact .inr (.inr (.inl (Region.sub_prefix (by omega_using []))))

/-- The memory a call changes: within `ws`, each in `⟨scratch, 2256⟩` or in
the 16 bytes below the frame. -/
theorem after_frame {u u' : State} (hc : Ctx L g m₀ u) {ws : List Region} (ha : After u ws u')
    (hs : ∀ r ∈ ws, Region.Sub r ⟨L.scr, 2256⟩) : Frame (W L) u.mem u'.mem :=
  ha.frame.sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨⟨L.scr, 2256⟩, by simp, hs r hr⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨L.B, 16⟩, by simp, by rw [hc.below_eq]; exact sub_refl _⟩

/-! ## HMAC's `init` -/

/-- The arguments of HMAC's `init`. -/
theorem initArgs_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.initArgs) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧
      t'.gpr .x0 = L.scr + BitVec.ofNat 64 0 ∧ t'.gpr .x1 = L.scr + BitVec.ofNat 64 192 ∧
      t'.gpr .x2 = L.B + BitVec.ofNat 64 16 ∧ t'.gpr .x3 = BitVec.ofNat 64 P.H.D ∧
      t'.gpr .x4 = L.scr + BitVec.ofNat 64 384 := by
  rw [Cfg.initArgs, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (scr_ok hL hc (d := .x0) (by decide) (a := 0) (by decide)) fun u₁ h₁ => ?_
  refine WP.mono (scr_ok hL h₁.ctx (d := .x1) (by decide) (a := 192) (by decide)) fun u₂ h₂ => ?_
  refine WP.mono (fr_ok hL h₂.ctx (d := .x2) (by decide) (o := 0) (by decide)) fun u₃ h₃ => ?_
  refine WP.mono (ldD_ok hL hT h₃.ctx (d := .x3) (by decide)) fun u₄ h₄ => ?_
  refine WP.mono (scr_ok hL h₄.ctx (d := .x4) (by decide) (a := 384) (by decide)) fun u₅ h₅ => ?_
  refine ⟨h₅.ctx, by rw [h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem], ?_, ?_, ?_, ?_, h₅.val⟩
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.keep _ (by decide), h₁.val]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.val]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.val]
  · rw [h₅.keep _ (by decide), h₄.val]

theorem initA (hL : L.Ok) {u : State} (hcu : Ctx L g m₀ u) (h0 : u.gpr .x0 = L.scr + BitVec.ofNat 64 0)
    (h1 : u.gpr .x1 = L.scr + BitVec.ofNat 64 192) (h2 : u.gpr .x2 = L.B + BitVec.ofNat 64 16)
    (h3 : u.gpr .x3 = BitVec.ofNat 64 P.H.D) (h4 : u.gpr .x4 = L.scr + BitVec.ofNat 64 384) :
    Proof.Pbkdf2.Md.AArch64.Pbk.InitArgs (H := P.H) u (L.scr + BitVec.ofNat 64 0)
      (L.scr + BitVec.ofNat 64 192) (L.B + BitVec.ofNat 64 16) (L.scr + BitVec.ofNat 64 384) P.H.D := by
  have hsp : below u.sp 16 = ⟨L.B, 16⟩ := hcu.below_eq
  have he := L.he
  exact
    { x0 := h0, x1 := h1, x2 := h2, x3 := by rw [h3, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by anums)
      x4 := h4, klB := by anums
      cr := hcu.covers fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨L.FR, by simp, within_fr _ (by omega_using []) (by anums)⟩
      cw := hcu.coversW fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> exact ⟨L.SCR, by simp, within_off _ (by anums)⟩
      i_o := Offset.disjoint _ (by anums) (by anums) (by anums)
      i_s := Offset.disjoint _ (by anums) (by anums) (by anums)
      o_s := Offset.disjoint _ (by anums) (by anums) (by anums)
      k_i := hL.stk_scr (by anums) (by anums)
      k_o := hL.stk_scr (by anums) (by anums)
      k_s := hL.stk_scr (by anums) (by anums)
      sp16 := hcu.sp16 hL
      stk_i := by rw [hsp]; exact hL.low_scr (by anums)
      stk_o := by rw [hsp]; exact hL.low_scr (by anums)
      stk_k := by rw [hsp]; exact Offset.base_disjoint _ (by omega_using []) (by anums)
      stk_s := by rw [hsp]; exact hL.low_scr (by anums)
      scnw := by rw [toNat_add_of (by have := hL.nc; omega_using [this])]; have := hL.nc; anums }

theorem xorPad_length (k : List Byte) (p : Byte) : (Spec.Hmac.xorPad k p).length = k.length :=
  List.length_map _

theorem blockKey_length {k : List Byte} (hk : k.length = P.H.D) :
    (Spec.Hmac.blockKey P.ok.SH.H k).length = P.H.P.B := by
  have hB := P.ok.hB
  have hDB : P.H.D < P.H.P.B := by anums
  simp only [Spec.Hmac.blockKey, hk, hB, show ¬ P.H.P.B < P.H.D by omega_using [hDB], ite_false, List.length_append,
    List.length_replicate]
  omega_using [hDB]

theorem keyOf_length (m : Mem) : (keyOf P L m).length = P.H.D := by simp [keyOf, Spec.Sha256.bytesAt]

/-- HMAC's `init` with the key `K` in the frame: HMAC's states for its block key. -/
theorem init_step (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).initK t fun u => St P L g m₀ (Spec.Hmac.blockKey P.ok.SH.H (keyOf P L t.mem)) [] u ∧
      Frame (W L) t.mem u.mem := by
  refine WP.seq (WP.mono (initArgs_ok hL hT hc) fun u ⟨hcu, hmu, h0, h1, h2, h3, h4⟩ => ?_)
  have hok := hcu.tabOk
  have htm := hcu.tabMem
  rw [hT.1, hT.2] at hok
  rw [hT.1] at htm
  refine tcall_ok hL hcu (j := 0) (by decide) htm.1 hok.i fun u' hc' hm' hk' _ => ?_
  have hk0 : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4], u'.gpr r = u.gpr r := fun r hr => hk' r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
  have a := initA (P := P) hL hc' ((hk0 _ (by simp)).trans h0) ((hk0 _ (by simp)).trans h1)
    ((hk0 _ (by simp)).trans h2) ((hk0 _ (by simp)).trans h3) ((hk0 _ (by simp)).trans h4)
  refine Proof.Pbkdf2.Md.AArch64.Pbk.hinit_call P.ok P.hI P.hId a fun v ha hi ho => ?_
  have hsafe : ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 0, P.H.S⟩ : Region), ⟨L.scr + BitVec.ofNat 64 192, P.H.S⟩,
      ⟨L.scr + BitVec.ofNat 64 384, 8 * P.H.W⟩], Region.Sub r ⟨L.scr, 2256⟩ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> exact scr_work (by anums)
  have hkey : Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 16) P.H.D = keyOf P L t.mem := by
    rw [hm', hmu]
  rw [hkey] at hi ho
  refine ⟨⟨hc'.after hL ha fun r hr => .inr (.inl (sub_trans (hsafe r hr) (Region.sub_prefix (by omega_using [])))),
    blockKey_length (keyOf_length _), by simp, by simpa using hi, ho⟩, ?_⟩
  rw [← hmu, ← hm']
  exact after_frame hc' ha hsafe

/-! ## The streaming `update` -/

/-- The arguments of the streaming `update` with `V`. -/
theorem updVArgs_ok (hL : L.Ok) (hT : TabL P L) {u : State} (hc : Ctx L g m₀ u) :
    WP isa (.block Cfg.updVArgs) u fun u' => Ctx L g m₀ u' ∧
      u'.mem = u.mem ∧ u'.gpr .x0 = L.scr + BitVec.ofNat 64 0 ∧ u'.gpr .x1 = BitVec.ofNat 64 P.H.P.B ∧
      u'.gpr .x2 = L.B + BitVec.ofNat 64 80 ∧ u'.gpr .x3 = BitVec.ofNat 64 P.H.D ∧
      u'.gpr .x4 = L.scr + BitVec.ofNat 64 384 := by
  rw [Cfg.updVArgs, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (scr_ok hL hc (d := .x0) (by decide) (a := 0) (by decide)) fun u₁ h₁ => ?_
  refine WP.mono (ldB_ok hL hT h₁.ctx (d := .x1) (by decide)) fun u₂ h₂ => ?_
  refine WP.mono (fr_ok hL h₂.ctx (d := .x2) (by decide) (o := fV) (by decide)) fun u₃ h₃ => ?_
  refine WP.mono (ldD_ok hL hT h₃.ctx (d := .x3) (by decide)) fun u₄ h₄ => ?_
  refine WP.mono (scr_ok hL h₄.ctx (d := .x4) (by decide) (a := 384) (by decide)) fun u₅ h₅ => ?_
  refine ⟨h₅.ctx, by rw [h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem], ?_, ?_, ?_, ?_, h₅.val⟩
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.keep _ (by decide), h₁.val]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.val]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.val]; rfl
  · rw [h₅.keep _ (by decide), h₄.val]

/-- The arguments of the streaming `update` with the message's `len` bytes. -/
theorem updMArgs_ok (hL : L.Ok) (hT : TabL P L) {u : State} (hc : Ctx L g m₀ u) {len : Nat}
    (hlen : len < 2 ^ 16) :
    WP isa (.block (Cfg.updMArgs len)) u fun u' => Ctx L g m₀ u' ∧
      u'.mem = u.mem ∧ u'.gpr .x0 = L.scr + BitVec.ofNat 64 0 ∧
      u'.gpr .x1 = BitVec.ofNat 64 (P.H.P.B + P.H.D) ∧
      u'.gpr .x2 = L.scr + BitVec.ofNat 64 sMsg ∧ u'.gpr .x3 = BitVec.ofNat 64 len ∧
      u'.gpr .x4 = L.scr + BitVec.ofNat 64 384 := by
  rw [Cfg.updMArgs, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (scr_ok hL hc (d := .x0) (by decide) (a := 0) (by decide)) fun u₁ h₁ => ?_
  rw [show ([.ldrSp .x1 fBl, .ldrSp .x9 fDl, .add .x .x1 .x1 .x9] : List Instr) =
    [.ldrSp .x1 fBl] ++ [.ldrSp .x9 fDl] ++ [.add .x .x1 .x1 .x9] from rfl, WP.block_append_iff,
    WP.block_append_iff]
  refine WP.mono (ldB_ok hL hT h₁.ctx (d := .x1) (by decide)) fun u₂ h₂ => ?_
  refine WP.mono (ldD_ok hL hT h₂.ctx (d := .x9) (by decide)) fun u₂' h₂' => ?_
  refine WP.mono (add_ok hL h₂'.ctx (d := .x1) (r := .x9) (by decide)) fun u₂'' h₂'' => ?_
  refine WP.mono (scr_ok hL h₂''.ctx (d := .x2) (by decide) (a := sMsg) (by decide)) fun u₃ h₃ => ?_
  refine WP.mono (movz_ok hL h₃.ctx (d := .x3) (by decide) hlen) fun u₄ h₄ => ?_
  refine WP.mono (scr_ok hL h₄.ctx (d := .x4) (by decide) (a := 384) (by decide)) fun u₅ h₅ => ?_
  refine ⟨h₅.ctx, by rw [h₅.mem, h₄.mem, h₃.mem, h₂''.mem, h₂'.mem, h₂.mem, h₁.mem], ?_, ?_, ?_, ?_, h₅.val⟩
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), h₂''.keep _ (by decide),
      h₂'.keep _ (by decide), h₂.keep _ (by decide), h₁.val]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), h₂''.val, h₂'.val,
      h₂'.keep _ (by decide), h₂.val, BitVec.ofNat_add_ofNat]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.val]
  · rw [h₅.keep _ (by decide), h₄.val]

/-- The arguments of the streaming `update`. -/
theorem updA (hL : L.Ok) {w : State} (hcw : Ctx L g m₀ w) {da : Addr} {len : Nat} (hd : DataOk L da len)
    (hlen : len ≤ 256) (h0 : w.gpr .x0 = L.scr + BitVec.ofNat 64 0) (h2 : w.gpr .x2 = da)
    (h3 : w.gpr .x3 = BitVec.ofNat 64 len) (h4 : w.gpr .x4 = L.scr + BitVec.ofNat 64 384) :
    Proof.Pbkdf2.Md.AArch64.Calls.UpdArgs P.ok.stream w (L.scr + BitVec.ofNat 64 0) da
      (L.scr + BitVec.ofNat 64 384) len := by
  have hsp : below w.sp 16 = ⟨L.B, 16⟩ := hcw.below_eq
  exact
    { x0 := h0, x2 := h2, x3 := by rw [h3, BitVec.toNat_ofNat]; omega_using [hlen], x4 := h4
      cd := hcw.covers fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hd.within
      cw := hcw.coversW fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact ⟨L.SCR, by simp, within_off _ (by anums)⟩
      st_sc := Offset.disjoint _ (by anums) (by anums) (by anums)
      d_st := hd.work hL (by anums)
      d_sc := hd.work hL (by anums)
      sp16 := hcw.sp16 hL
      stk_st := by rw [hsp]; exact hL.low_scr (by anums)
      stk_d := by rw [hsp]; exact hd.low hL
      stk_sc := by rw [hsp]; exact hL.low_scr (by anums) }

/-- The table's `update` of the inner state, holding `text`, with the data. -/
theorem upd_call_ok (hL : L.Ok) (hT : TabL P L) {k0 text : List Byte} {u : State} (hu : St P L g m₀ k0 text u)
    {da : Addr} {len : Nat} (hd : DataOk L da len) (hlen : len ≤ 256) (htl : text.length + len ≤ 512)
    (h0 : u.gpr .x0 = L.scr + BitVec.ofNat 64 0) (h1 : u.gpr .x1 = BitVec.ofNat 64 (P.H.P.B + text.length))
    (h2 : u.gpr .x2 = da) (h3 : u.gpr .x3 = BitVec.ofNat 64 len) (h4 : u.gpr .x4 = L.scr + BitVec.ofNat 64 384) :
    WP isa (Cfg.tcall 1 P.f.upd) u fun u' => St P L g m₀ k0 (text ++ Spec.Sha256.bytesAt u.mem da len) u' ∧
      Frame (W L) u.mem u'.mem := by
  have hc := hu.ctx
  have hok := hc.tabOk
  have htm := hc.tabMem
  rw [hT.1, hT.2] at hok
  rw [hT.1] at htm
  refine tcall_ok hL hc (j := 1) (by decide) htm.2.1 hok.u fun w hcw hmw hkw _ => ?_
  have hk0 : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4], w.gpr r = u.gpr r := fun r hr => hkw r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
  have a := updA (P := P) hL hcw hd hlen ((hk0 _ (by simp)).trans h0) ((hk0 _ (by simp)).trans h2)
    ((hk0 _ (by simp)).trans h3) ((hk0 _ (by simp)).trans h4)
  refine Proof.Pbkdf2.Md.AArch64.Calls.upd_call P.ok.stream a fun w' af hr => ?_
  have hws : ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 0, P.H.stream.S⟩ : Region),
      ⟨L.scr + BitVec.ofNat 64 384, P.ok.stream.Wb⟩], Region.Sub r ⟨L.scr, 2256⟩ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> exact scr_work (by anums)
  have hkl := hu.klen
  refine ⟨⟨hcw.after hL af fun r hr => .inr (.inl (sub_trans (hws r hr) (Region.sub_prefix (by omega_using [])))),
    hkl, by simp [Spec.Sha256.bytesAt]; omega_using [htl], ?_, ?_⟩, hmw ▸ after_frame hcw af hws⟩
  · rw [← hmw, ← List.append_assoc]
    exact hr _ (hmw ▸ hu.inner) (by
      rw [(hk0 _ (by simp)).trans h1, List.length_append, xorPad_length, hkl])
  · refine P.ok.stream.repr w.mem w'.mem _ _ _ (fun i hi => ?_) (hmw ▸ hu.outer)
    refine Frame.bytes (R := ⟨L.scr + BitVec.ofNat 64 192, P.H.stream.S⟩) af.frame (fun r hr => ?_)
      (by show P.H.stream.S ≤ 2 ^ 64; anums) hi
    rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by anums) (by anums) (by anums)
    · simp only [List.mem_singleton] at hr; subst hr
      rw [hcw.below_eq]
      exact (hL.low_scr (by anums)).symm

/-- The inner state, for the key `K₀`, updated with `V`. -/
theorem updV_step (hL : L.Ok) (hT : TabL P L) {k0 : List Byte} {u : State} (hu : St P L g m₀ k0 [] u) :
    WP isa (cfgOf P).updV u fun u' =>
      St P L g m₀ k0 (Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 80) P.H.D) u' ∧
      Frame (W L) u.mem u'.mem := by
  refine WP.seq (WP.mono (updVArgs_ok hL hT hu.ctx) fun w ⟨hcw, hmw, h0, h1, h2, h3, h4⟩ => ?_)
  have hw : St P L g m₀ k0 [] w := ⟨hcw, hu.klen, hu.tlen, hmw ▸ hu.inner, hmw ▸ hu.outer⟩
  refine WP.mono (upd_call_ok hL hT hw (len := P.H.D)
    (.inl ⟨80, rfl, by omega_using [], by anums⟩) (by anums) (by simp; anums) h0 (by simpa using h1) h2 h3 h4)
    fun u' ⟨hs, hf⟩ => ?_
  rw [List.nil_append, hmw] at hs
  exact ⟨hs, hmw ▸ hf⟩

/-- The inner state, for the key `K₀`, holding `text`, updated with the message's `len` bytes. -/
theorem updM_step (hL : L.Ok) (hT : TabL P L) {k0 text : List Byte} {u : State}
    (hu : St P L g m₀ k0 text u) (ht : text.length = P.H.D) {len : Nat} (hlen : len ≤ 256) :
    WP isa ((cfgOf P).updM len) u fun u' =>
      St P L g m₀ k0 (text ++ Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 sMsg) len) u' ∧
      Frame (W L) u.mem u'.mem := by
  refine WP.seq (WP.mono (updMArgs_ok hL hT hu.ctx (len := len) (by omega_using [hlen]))
    fun w ⟨hcw, hmw, h0, h1, h2, h3, h4⟩ => ?_)
  have hw : St P L g m₀ k0 text w := ⟨hcw, hu.klen, hu.tlen, hmw ▸ hu.inner, hmw ▸ hu.outer⟩
  refine WP.mono (upd_call_ok hL hT hw (len := len) (.inr ⟨sMsg, rfl, by decide, by simp only [sMsg]; omega_using [hlen]⟩)
    hlen (by rw [ht]; anums) h0 (by rw [h1, ht]) h2 h3 h4) fun u' ⟨hs, hf⟩ => ?_
  rw [hmw] at hs
  exact ⟨hs, hmw ▸ hf⟩

/-! ## HMAC's `finalize` -/

theorem finArgs_ok (hL : L.Ok) (hT : TabL P L) {u : State} (hc : Ctx L g m₀ u) {len dst : Nat}
    (hlen : len < 4096) (hdst : dst < 4096) :
    WP isa (.block (Cfg.finArgs len dst)) u
      fun u' => Ctx L g m₀ u' ∧ u'.mem = u.mem ∧ u'.gpr .x0 = L.scr + BitVec.ofNat 64 0 ∧
        u'.gpr .x1 = L.scr + BitVec.ofNat 64 192 ∧ u'.gpr .x2 = BitVec.ofNat 64 (P.H.P.B + P.H.D + len) ∧
        u'.gpr .x3 = L.B + BitVec.ofNat 64 (16 + dst) ∧ u'.gpr .x4 = L.scr + BitVec.ofNat 64 384 := by
  rw [Cfg.finArgs, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (scr_ok hL hc (d := .x0) (by decide) (a := 0) (by decide)) fun u₁ h₁ => ?_
  refine WP.mono (scr_ok hL h₁.ctx (d := .x1) (by decide) (a := 192) (by decide)) fun u₂ h₂ => ?_
  rw [show ([.ldrSp .x2 fBl, .ldrSp .x9 fDl, .add .x .x2 .x2 .x9, .addImm .x .x2 .x2 len] : List Instr) =
    [.ldrSp .x2 fBl] ++ [.ldrSp .x9 fDl] ++ [.add .x .x2 .x2 .x9] ++ [.addImm .x .x2 .x2 len] from rfl,
    WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ldB_ok hL hT h₂.ctx (d := .x2) (by decide)) fun u₃ h₃ => ?_
  refine WP.mono (ldD_ok hL hT h₃.ctx (d := .x9) (by decide)) fun u₃' h₃' => ?_
  refine WP.mono (add_ok hL h₃'.ctx (d := .x2) (r := .x9) (by decide)) fun u₃'' h₃'' => ?_
  refine WP.mono (addI_ok hL h₃''.ctx (d := .x2) (by decide) hlen) fun u₃''' h₃''' => ?_
  refine WP.mono (fr_ok hL h₃'''.ctx (d := .x3) (by decide) hdst) fun u₄ h₄ => ?_
  refine WP.mono (scr_ok hL h₄.ctx (d := .x4) (by decide) (a := 384) (by decide)) fun u₅ h₅ => ?_
  refine ⟨h₅.ctx, by rw [h₅.mem, h₄.mem, h₃'''.mem, h₃''.mem, h₃'.mem, h₃.mem, h₂.mem, h₁.mem], ?_, ?_, ?_, ?_,
    h₅.val⟩
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃'''.keep _ (by decide), h₃''.keep _ (by decide),
      h₃'.keep _ (by decide), h₃.keep _ (by decide), h₂.keep _ (by decide), h₁.val]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃'''.keep _ (by decide), h₃''.keep _ (by decide),
      h₃'.keep _ (by decide), h₃.keep _ (by decide), h₂.val]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃'''.val, h₃''.val, h₃'.val, h₃'.keep _ (by decide),
      h₃.val, BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat]
  · rw [h₅.keep _ (by decide), h₄.val]

/-- The arguments of HMAC's `finalize`. -/
theorem finA (hL : L.Ok) {w : State} (hcw : Ctx L g m₀ w) {cnt : Nat} {dst : Nat} (hdst : dst + P.H.D ≤ 184)
    (h0 : w.gpr .x0 = L.scr + BitVec.ofNat 64 0) (h1 : w.gpr .x1 = L.scr + BitVec.ofNat 64 192)
    (h2 : w.gpr .x2 = BitVec.ofNat 64 cnt) (h3 : w.gpr .x3 = L.B + BitVec.ofNat 64 (16 + dst))
    (h4 : w.gpr .x4 = L.scr + BitVec.ofNat 64 384) :
    Proof.Pbkdf2.Md.AArch64.Pbk.FinArgs (H := P.H) w (L.scr + BitVec.ofNat 64 0)
      (L.scr + BitVec.ofNat 64 192) (BitVec.ofNat 64 cnt) (L.B + BitVec.ofNat 64 (16 + dst))
      (L.scr + BitVec.ofNat 64 384) := by
  have hsp : below w.sp 16 = ⟨L.B, 16⟩ := hcw.below_eq
  have he := L.he
  exact
    { x0 := h0, x1 := h1, x2 := h2, x3 := h3, x4 := h4
      cr := hcw.covers fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨L.SCR, by simp, within_off _ (by anums)⟩
      cw := hcw.coversW fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨L.SCR, by simp, within_off _ (by anums)⟩
        · exact ⟨L.FR, by simp, within_fr _ (by omega_using []) (by anums)⟩
        · exact ⟨L.SCR, by simp, within_off _ (by anums)⟩
      i_u := Offset.disjoint _ (by anums) (by anums) (by anums)
      i_o := (hL.stk_scr (d := 16 + dst) (by anums) (by anums)).symm
      i_s := Offset.disjoint _ (by anums) (by anums) (by anums)
      u_o := (hL.stk_scr (d := 16 + dst) (by anums) (by anums)).symm
      u_s := Offset.disjoint _ (by anums) (by anums) (by anums)
      o_s := hL.stk_scr (by anums) (by anums)
      sp16 := hcw.sp16 hL
      stk_i := by rw [hsp]; exact hL.low_scr (by anums)
      stk_u := by rw [hsp]; exact hL.low_scr (by anums)
      stk_o := by rw [hsp]; exact Offset.base_disjoint _ (by omega_using []) (by anums)
      stk_s := by rw [hsp]; exact hL.low_scr (by anums)
      scnw := by rw [toNat_add_of (by have := hL.nc; omega_using [this])]; have := hL.nc; anums }

/-- HMAC's `finalize`, for the key `K₀` and the text `text`, of `D + len`
bytes: the MAC in the frame at `dst`. -/
theorem fin_step (hL : L.Ok) (hT : TabL P L) {k0 text : List Byte} {u : State} (hu : St P L g m₀ k0 text u)
    {len dst : Nat} (ht : text.length = P.H.D + len) (hlen : len < 4096) (hdst : dst + P.H.D ≤ 184) :
    WP isa ((cfgOf P).fin len dst) u fun u' => Ctx L g m₀ u' ∧
      Frame (W L ++ [⟨L.B + BitVec.ofNat 64 (16 + dst), P.H.D⟩]) u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (16 + dst)) P.H.D =
        Spec.Hmac.hmacBlockKey P.ok.SH.H k0 text := by
  refine WP.seq (WP.mono (finArgs_ok hL hT hu.ctx (len := len) (dst := dst) hlen (by omega_using [hdst]))
    fun w ⟨hcw, hmw, h0, h1, h2, h3, h4⟩ => ?_)
  have hok := hcw.tabOk
  have htm := hcw.tabMem
  rw [hT.1, hT.2] at hok
  rw [hT.1] at htm
  refine tcall_ok hL hcw (j := 2) (by decide) htm.2.2 hok.f fun w₁ hc₁ hm₁ hk₁ _ => ?_
  have hk0 : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4], w₁.gpr r = w.gpr r := fun r hr => hk₁ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
  have a := finA (P := P) hL hc₁ (cnt := P.H.P.B + P.H.D + len) hdst ((hk0 _ (by simp)).trans h0)
    ((hk0 _ (by simp)).trans h1) ((hk0 _ (by simp)).trans h2) ((hk0 _ (by simp)).trans h3)
    ((hk0 _ (by simp)).trans h4)
  refine Proof.Pbkdf2.Md.AArch64.Pbk.hfin_call P.ok P.hF P.hFd a fun w' ha hpost => ?_
  have hws : ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 0, P.H.S⟩ : Region),
      ⟨L.B + BitVec.ofNat 64 (16 + dst), P.H.D⟩, ⟨L.scr + BitVec.ofNat 64 384, 8 * P.H.W⟩] ++
      [below w₁.sp 16], ∃ r' ∈ W L ++ [⟨L.B + BitVec.ofNat 64 (16 + dst), P.H.D⟩], Region.Sub r r' := by
    simp only [W, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, hc₁.below_eq]
    rintro r (rfl | rfl | rfl | rfl)
    · exact ⟨⟨L.scr, 2256⟩, by simp, scr_work (by anums)⟩
    · exact ⟨⟨L.B + BitVec.ofNat 64 (16 + dst), P.H.D⟩, by simp, sub_refl _⟩
    · exact ⟨⟨L.scr, 2256⟩, by simp, scr_work (by anums)⟩
    · exact ⟨⟨L.B, 16⟩, by simp, sub_refl _⟩
  have hm : w₁.mem = u.mem := hm₁.trans hmw
  refine ⟨hc₁.keep hL ha.rd ha.wr ha.sp ha.cs ha.frame (hsy := ha.syms) fun r hr => ?_,
    hm ▸ ha.frame.sub hws, ?_⟩
  · obtain ⟨r', hr', hs⟩ := hws r hr
    simp only [W, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · exact .inr (.inl (sub_trans hs (Region.sub_prefix (by omega_using []))))
    · exact .inr (.inr (.inl (sub_trans hs (Region.sub_prefix (by omega_using [])))))
    · exact (safe_low L (by anums)).of_sub hs
  · have hk := hu.klen
    exact hpost _ _ hk (by rw [hk]; have := hu.tlen; anums) (hm ▸ hu.inner)
      (by rw [ht]; congr 1; omega_using []) (hm ▸ hu.outer)

end VG.Proof.Ecdsa.Rfc6979.AArch64

end

end


/-!
# Deterministic ECDSA on AArch64: the steps on `K` and `V`

Each HMAC with the key `K` and `V` (both of the digest length `D`, at the
start of the frame) is HMAC's states for `K` (by `init`, then saved, or
restored from the copy), the table's `update` with `V` and, for a new `K`,
with the message at `scratch + 2256`, then `finalize` into `V`
(`vfin_ok`) or `K` (`vmfin_ok`): `V = HMAC_K(V)` from a new `K`, saving the
states (`hmacVS_ok`), or from the saved ones (`hmacVR_ok`);
`K = HMAC_K(V ‖ m)` (`hmacKB_ok`). With the message `b ‖ d ‖ h` or `b`
(`msg_ok`): steps d–e and f–g (`rekeyFull_ok`) and h.3 (`rekey_ok`). They
change only `scratch`, the stack below the frame, `K` and `V` (`KVW`).

HMAC's two states just after `init` with the key `K` depend only on `K`, so
the code keeps a copy of them at `scratch + 3072` (`SavedB`) after an `init`
(`save_ok`), and, for a later HMAC with the same `K`, copies them back in
place of `init` (`restore_ok`). A state moves with its bytes
(`StreamOK.repr`), as on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Prep.lean`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64

variable {P : RfcHash} {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} {L : Lay dn E} {g : Reg → BitVec 64} {m₀ : Mem}

/-- `scratch` in `x9`. -/
theorem scrPtr_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.scrPtr) t fun u => Ctx L g m₀ u ∧ u.mem = t.mem ∧ u.gpr .x9 = L.scr ∧
      ∀ r, r ≠ .x9 → u.gpr r = t.gpr r :=
  WP.mono (ldF_ok hL hc (d := .x9) (by decide) (o := fScratch) (by simp only [fScratch]; have := L.he; omega_using []) rfl)
    fun u h => ⟨h.ctx, h.mem, h.val.trans hc.pScr, h.keep⟩

/-- A copy at `scratch + 3072` of HMAC's inner and outer states for the block key `k0`. -/
def SavedB (P : RfcHash) {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (m : Mem) (k0 : List Byte) : Prop :=
  P.ok.SH.Repr m (L.scr + BitVec.ofNat 64 3072) (Spec.Hmac.xorPad k0 Spec.Hmac.ipad) ∧
    P.ok.SH.Repr m (L.scr + BitVec.ofNat 64 3264) (Spec.Hmac.xorPad k0 Spec.Hmac.opad)

/-- The copy's region. -/
abbrev SaveR {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) : Region := ⟨L.scr + BitVec.ofNat 64 3072, 384⟩

theorem state_le (P : RfcHash) : P.H.P.N + P.H.P.B ≤ 192 ∧ P.H.stream.S = P.H.P.N + P.H.P.B := by
  have := P.ok.B_le; have := P.ok.N_le; exact ⟨by omega_arith, rfl⟩

/-- The bytes of `n` at `p` in `m'` are those at `q` in `m`, one by one. -/
theorem byte_of_bytesAt {m m' : Mem} {p q : Addr} {n : Nat}
    (h : Spec.Sha256.bytesAt m' p n = Spec.Sha256.bytesAt m q n) {i : Nat} (hi : i < n) :
    m' (p + BitVec.ofNat 64 i) = m (q + BitVec.ofNat 64 i) := by
  have := congrArg (·[i]?) h
  simpa [Spec.Sha256.bytesAt, hi] using this

/-- The copy survives memory that changed apart from it. -/
theorem SavedB.frame {m m' : Mem} {k0 : List Byte} (hS : SavedB P L m k0) {ws : List Region}
    (hf : Frame ws m m') (hd : ∀ r ∈ ws, Region.Disjoint (SaveR L) r) : SavedB P L m' k0 := by
  obtain ⟨hle, hS'⟩ := state_le P
  refine ⟨P.ok.stream.repr _ _ _ _ _ (fun i hi => Frame.bytes (R := ⟨L.scr + BitVec.ofNat 64 3072, 192⟩) hf
      (fun r hr => (hd r hr).sub_left (Offset.sub _ (by omega_using []) (by omega_using []))) (by decide : (192 : Nat) ≤ 2 ^ 64)
      (show i < 192 by omega_using [hle, hS', hi])) hS.1,
    P.ok.stream.repr _ _ _ _ _ (fun i hi => Frame.bytes (R := ⟨L.scr + BitVec.ofNat 64 3264, 192⟩) hf
      (fun r hr => (hd r hr).sub_left (Offset.sub _ (by omega_using []) (by omega_using []))) (by decide : (192 : Nat) ≤ 2 ^ 64)
      (show i < 192 by omega_using [hle, hS', hi])) hS.2⟩

/-- What HMAC's functions write is apart from the copy. -/
theorem W_save (hL : L.Ok) : ∀ r ∈ W L, Region.Disjoint (SaveR L) r := by
  intro r hr
  simp only [W, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (Offset.disjoint_base _ (by decide) (by decide))
  · exact ((hL.kc.sub_left (Region.sub_prefix (by omega_using []))).sub_right (Offset.sub_base _ (by decide))).symm

/-- The arguments of the copy of 384 bytes from `scratch + a` to `scratch + d`. -/
theorem copyArgs_ok (hL : L.Ok) {a d : Nat} (ha : a < 4096) (hd : d < 4096) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block (([.ldrSp .x9 fScratch] : List Instr) ++ ([.addImm .x .x11 .x9 a] : List Instr) ++
      ([.addImm .x .x12 .x9 d] : List Instr) ++ ([.movz .x .x13 (BitVec.ofNat 16 384) 0] : List Instr))) t fun u => Ctx L g m₀ u ∧ u.mem = t.mem ∧
        u.gpr .x11 = L.scr + BitVec.ofNat 64 a ∧ u.gpr .x12 = L.scr + BitVec.ofNat 64 d ∧
        u.gpr .x13 = BitVec.ofNat 64 384 := by
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  exact WP.mono (scrPtr_ok hL hc) fun u₁ ⟨hc₁, hm₁, h9₁, _⟩ =>
    WP.mono (addImm_ok hL hc₁ (d := .x11) (by decide) h9₁ ha) fun u₂ h₂ =>
    WP.mono (addImm_ok hL h₂.ctx (d := .x12) (by decide) (by rw [h₂.keep _ (by decide), h9₁]) hd) fun u₃ h₃ =>
    WP.mono (movz_ok hL h₃.ctx (d := .x13) (by decide) (n := 384) (by decide)) fun u₄ h₄ =>
      ⟨h₄.ctx, by rw [h₄.mem, h₃.mem, h₂.mem, hm₁], by rw [h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.val],
        by rw [h₄.keep _ (by decide), h₃.val], h₄.val⟩

/-- The 384 bytes at `scratch + a` copied to `scratch + d`, apart, by
`cpLoop`, from `x11 = scratch + a`, `x12 = scratch + d` and `x13 = 384`. -/
theorem copy384_ok (hL : L.Ok) {a d : Nat} (ha : a < 4096) (hd : d < 4096) (hsep : a + 384 ≤ d ∨ d + 384 ≤ a)
    (hd₂ : d + 384 ≤ 8192) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.seq (.block (([.ldrSp .x9 fScratch] : List Instr) ++ ([.addImm .x .x11 .x9 a] : List Instr) ++
      ([.addImm .x .x12 .x9 d] : List Instr) ++ ([.movz .x .x13 (BitVec.ofNat 16 384) 0] : List Instr))) Cfg.cpLoop) t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 d, 384⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 d) 384 =
        Spec.Sha256.bytesAt t.mem (L.scr + BitVec.ofNat 64 a) 384 := by
  refine WP.seq (WP.mono (copyArgs_ok hL ha hd hc) fun u ⟨hcu, hmu, h11, h12, h13⟩ => ?_)
  have hnc := hL.nc
  refine WP.mono (cp_ok hL hcu (p := L.scr + BitVec.ofNat 64 d) (q := L.scr + BitVec.ofNat 64 a) (n := 384)
    (by decide) (by decide) h13 h12 h11 ?_ (hcu.inScrW hd₂) (safe_scr L hd₂)
    (fun i hi => by rw [Offset.add_add]; exact hcu.inScr (by omega_using [ha, hi]))
    (fun i hi h => Offset.disjoint L.scr (d := a + i) (n := 1) (e := d) (k := 384) (by omega_using [hsep, hi]) (by omega_using [ha, hi]) (by omega_using [hd]) _
      (by rw [← Offset.add_add]; exact Region.contains_self _ _) h))
    fun u' ⟨hc', _, hf, hb⟩ => ⟨hc', hmu ▸ hf, by rw [hb, hmu]⟩
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega_using [hd]), Nat.mod_eq_of_lt (by omega_using [hd, hnc])]
  omega_using [hd, hnc]

/-- After `init`: the states copied to `scratch + 3072`, and `St` kept. -/
theorem save_ok (hL : L.Ok) {k0 : List Byte} {u : State} (hu : St P L g m₀ k0 [] u) :
    WP isa Cfg.save u fun u' => St P L g m₀ k0 [] u' ∧ SavedB P L u'.mem k0 ∧
      Frame [SaveR L] u.mem u'.mem := by
  obtain ⟨hle, hS'⟩ := state_le P
  refine WP.mono (copy384_ok hL (a := 0) (d := 3072) (by decide) (by decide) (by decide) (by decide)
    hu.ctx) fun u' ⟨hc', hf', hb'⟩ => ?_
  have hst : ∀ o, o + 192 ≤ 384 → ∀ i < P.H.P.N + P.H.P.B,
      u'.mem (L.scr + BitVec.ofNat 64 o + BitVec.ofNat 64 i) = u.mem (L.scr + BitVec.ofNat 64 o + BitVec.ofNat 64 i) :=
    fun o ho i hi => Frame.bytes (R := ⟨L.scr + BitVec.ofNat 64 o, 192⟩) hf'
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega_using [ho]) (by omega_using [ho]) (by omega_using [])) (by decide : (192 : Nat) ≤ 2 ^ 64)
      (show i < 192 by omega_using [hle, hi])
  have hin := hu.inner
  rw [List.append_nil] at hin
  refine ⟨⟨hc', hu.klen, hu.tlen, ?_, ?_⟩, ⟨?_, ?_⟩, hf'⟩
  · rw [List.append_nil]; exact P.ok.stream.repr _ _ _ _ _ (fun i hi => hst 0 (by decide) i hi) hin
  · exact P.ok.stream.repr _ _ _ _ _ (fun i hi => hst 192 (by decide) i hi) hu.outer
  · exact P.ok.stream.repr _ _ _ _ _ (fun i hi => byte_of_bytesAt hb' (by omega_using [hle, hS', hi])) hin
  · exact P.ok.stream.repr _ _ _ _ _ (fun i hi => by
      have h := byte_of_bytesAt hb' (i := 192 + i) (by omega_using [hle, hS', hi])
      have e1 : L.scr + BitVec.ofNat 64 3264 + BitVec.ofNat 64 i =
          L.scr + BitVec.ofNat 64 3072 + BitVec.ofNat 64 (192 + i) := by
        rw [Offset.add_add, Offset.add_add]; congr 2; omega_using []
      have e2 : L.scr + BitVec.ofNat 64 192 + BitVec.ofNat 64 i =
          L.scr + BitVec.ofNat 64 0 + BitVec.ofNat 64 (192 + i) := by
        rw [Offset.add_add, Offset.add_add, Nat.zero_add]
      rw [e1, e2]; exact h) hu.outer

/-- The copy back: HMAC's states for the block key `k0`, and the copy kept. -/
theorem restore_ok (hL : L.Ok) {k0 : List Byte} {t : State} (hc : Ctx L g m₀ t) (hS : SavedB P L t.mem k0)
    (hk : k0.length = P.H.P.B) :
    WP isa Cfg.restore t fun u => St P L g m₀ k0 [] u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 0, 8 * 48⟩] t.mem u.mem ∧ SavedB P L u.mem k0 := by
  obtain ⟨hle, hS'⟩ := state_le P
  refine WP.mono (copy384_ok hL (a := 3072) (d := 0) (by decide) (by decide) (by decide) (by decide)
    hc) fun u ⟨hcu, hf, hb⟩ => ?_
  refine ⟨⟨hcu, hk, by simp, ?_, ?_⟩, hf, hS.frame hf fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (by decide) (by decide) (by decide)⟩
  · rw [List.append_nil]; exact P.ok.stream.repr _ _ _ _ _ (fun i hi => byte_of_bytesAt hb (by omega_using [hle, hS', hi])) hS.1
  · exact P.ok.stream.repr _ _ _ _ _ (fun i hi => by
      have h := byte_of_bytesAt hb (i := 192 + i) (by omega_using [hle, hS', hi])
      have e1 : L.scr + BitVec.ofNat 64 192 + BitVec.ofNat 64 i =
          L.scr + BitVec.ofNat 64 0 + BitVec.ofNat 64 (192 + i) := by
        rw [Offset.add_add, Offset.add_add, Nat.zero_add]
      have e2 : L.scr + BitVec.ofNat 64 3264 + BitVec.ofNat 64 i =
          L.scr + BitVec.ofNat 64 3072 + BitVec.ofNat 64 (192 + i) := by
        rw [Offset.add_add, Offset.add_add]; congr 2; omega_using []
      rw [e1, e2]; exact h) hS.2

/-- `K` and `V` (of the hash function's output length), in the frame. -/
abbrev kOf (P : RfcHash) {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (m : Mem) : List Byte := keyOf P L m
abbrev vOf (P : RfcHash) {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (m : Mem) : List Byte :=
  Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 80) P.H.D

/-- A copy of HMAC's states for the key `K`. -/
abbrev SavedK (P : RfcHash) {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (m : Mem) (K : List Byte) : Prop :=
  SavedB P L m (Spec.Hmac.blockKey P.ok.SH.H K)

theorem hash_length (P : RfcHash) (m : List Byte) : (P.ok.SH.H.hash m).length = P.H.D := by
  have := P.ok.sizes.DN
  simp only [P.ok.hash, List.length_take, Proof.MdStream.Md.hash, P.ok.md.digest_length]
  omega_using [this]

/-- HMAC with a key is HMAC with its block key. -/
theorem mac_eq (P : RfcHash) (K t : List Byte) :
    P.mac K t = Spec.Hmac.hmacBlockKey P.ok.SH.H (Spec.Hmac.blockKey P.ok.SH.H K) t := rfl

/-- HMAC's output is the hash function's. -/
theorem mac_length (P : RfcHash) (K t : List Byte) : (P.mac K t).length = P.H.D := hash_length P _

/-- What the steps change: `scratch`, the stack below the frame, `K` and `V`. -/
abbrev KVW {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) : List Region := [L.SCR, ⟨L.B, 144⟩]

theorem kvw_of {rs : List Region} (h : ∀ r ∈ rs, Region.Sub r L.SCR ∨ Region.Sub r ⟨L.B, 144⟩) :
    ∀ r ∈ rs, ∃ r' ∈ KVW L, Region.Sub r r' := fun r hr => by
  rcases h r hr with h | h
  · exact ⟨_, by simp, h⟩
  · exact ⟨⟨L.B, 144⟩, by simp, h⟩

/-- HMAC's writes, and the MAC's place `dst` (`K` or `V`), within `KVW`. -/
theorem wd_kvw {dst : Nat} (h : dst + P.H.D ≤ 128) :
    ∀ r ∈ W L ++ [⟨L.B + BitVec.ofNat 64 (16 + dst), P.H.D⟩], ∃ r' ∈ KVW L, Region.Sub r r' :=
  kvw_of fun r hr => by
    simp only [W, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl (Region.sub_prefix (by omega_using []))
    · exact .inr (Region.sub_prefix (by omega_using []))
    · exact .inr (Offset.sub_base _ (by omega_using [h]))

/-- The `D` bytes at `o` in the frame survive HMAC's writes and the MAC's at `dst`. -/
theorem kv_frame {dst : Nat} (hL : L.Ok) {m m' : Mem}
    (hf : Frame (W L ++ [⟨L.B + BitVec.ofNat 64 (16 + dst), P.H.D⟩]) m m')
    {o : Nat} (ho : 16 ≤ o) (hod : o + P.H.D ≤ 16 + dst ∨ 16 + dst + P.H.D ≤ o) (hoe : o + P.H.D ≤ 200)
    (hdst : dst + P.H.D ≤ 184) :
    Spec.Sha256.bytesAt m' (L.B + BitVec.ofNat 64 o) P.H.D = Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 o) P.H.D :=
  bytesAt_frame hf (fun r hr => by
    have := L.he
    simp only [W, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.stk_scr0 (by omega_using [hoe]) (by decide)
    · exact Offset.disjoint_base _ ho (by anums)
    · exact Offset.disjoint _ hod (by omega_using [hoe]) (by omega_using [hdst])) (by anums)

/-- What HMAC's functions write, with the MAC at `dst` in the frame, is apart from the copy. -/
theorem wd_save (hL : L.Ok) {dst : Nat} (hdst : dst + P.H.D ≤ 184) :
    ∀ r ∈ W L ++ [⟨L.B + BitVec.ofNat 64 (16 + dst), P.H.D⟩], Region.Disjoint (SaveR L) r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact W_save hL r hr
  · simp only [List.mem_singleton] at hr; subst hr
    exact (hL.stk_scr (by have := L.he; anums) (by decide)).symm

/-- The message's bytes survive HMAC's writes. -/
theorem msg_W (hL : L.Ok) {m m' : Mem} (hf : Frame (W L) m m') {len : Nat} (hlen : 2256 + len ≤ 8192) :
    Spec.Sha256.bytesAt m' (L.scr + BitVec.ofNat 64 2256) len = Spec.Sha256.bytesAt m (L.scr + BitVec.ofNat 64 2256) len :=
  bytesAt_frame hf (fun r hr => by
    simp only [W, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint_base _ (Nat.le_refl _) (by omega_using [hlen])
    · exact (hL.low_scr (by omega_using [hlen])).symm) (by omega_using [hlen])

/-- `update` with `V`, then `finalize` into the frame at `dst`: `HMAC(K₀, V)`. -/
theorem vfin_ok (hL : L.Ok) (hT : TabL P L) {k0 : List Byte} {u : State} (hu : St P L g m₀ k0 [] u) {dst : Nat}
    (hdst : dst + P.H.D ≤ 184) :
    WP isa (.seq (cfgOf P).updV ((cfgOf P).fin 0 dst)) u fun u' => Ctx L g m₀ u' ∧
      Frame (W L ++ [⟨L.B + BitVec.ofNat 64 (16 + dst), P.H.D⟩]) u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (16 + dst)) P.H.D =
        Spec.Hmac.hmacBlockKey P.ok.SH.H k0 (vOf P L u.mem) := by
  refine WP.seq (WP.mono (updV_step hL hT hu) fun w ⟨hw, hfw⟩ => ?_)
  refine WP.mono (fin_step hL hT hw (len := 0) (dst := dst) (by simp [Spec.Sha256.bytesAt]) (by decide) hdst)
    fun u' ⟨hc', hf', hm'⟩ => ⟨hc', ?_, hm'⟩
  exact (hfw.sub fun r hr => ⟨r, List.mem_append_left _ hr, sub_refl _⟩).trans hf'

/-- `update` with `V`, then with the message's `len` bytes, then `finalize`
into `K`: `HMAC(K₀, V ‖ m)`. -/
theorem vmfin_ok (hL : L.Ok) (hT : TabL P L) {k0 : List Byte} {u : State} (hu : St P L g m₀ k0 [] u) {len : Nat}
    (hlen : len ≤ 256) :
    WP isa (.seq (cfgOf P).updV (.seq ((cfgOf P).updM len) ((cfgOf P).fin len fK))) u fun u' => Ctx L g m₀ u' ∧
      Frame (W L ++ [⟨L.B + BitVec.ofNat 64 (16 + fK), P.H.D⟩]) u.mem u'.mem ∧
      kOf P L u'.mem = Spec.Hmac.hmacBlockKey P.ok.SH.H k0
        (vOf P L u.mem ++ Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 2256) len) := by
  refine WP.seq (WP.mono (updV_step hL hT hu) fun w ⟨hw, hfw⟩ => ?_)
  refine WP.seq (WP.mono (updM_step hL hT hw (by simp [Spec.Sha256.bytesAt]) hlen) fun w' ⟨hw', hfw'⟩ => ?_)
  refine WP.mono (fin_step hL hT hw' (len := len) (dst := fK)
    (by simp [Spec.Sha256.bytesAt]) (by omega_using [hlen]) (by simp only [fK]; anums)) fun u' ⟨hc', hf', hm'⟩ => ⟨hc', ?_, ?_⟩
  · exact ((hfw.sub fun r hr => ⟨r, List.mem_append_left _ hr, sub_refl _⟩).trans
      (hfw'.sub fun r hr => ⟨r, List.mem_append_left _ hr, sub_refl _⟩)).trans hf'
  · show Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 16) P.H.D = _
    rw [show L.B + BitVec.ofNat 64 16 = L.B + BitVec.ofNat 64 (16 + fK) from rfl, hm',
      show sMsg = 2256 from rfl, msg_W hL hfw (len := len) (by omega_using [hlen])]

/-- `V = HMAC_K(V)`, HMAC's states for `K` saved. -/
theorem hmacVS_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).hmacVS t fun t' => Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
      kOf P L t'.mem = kOf P L t.mem ∧ vOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem) ∧
      SavedK P L t'.mem (kOf P L t'.mem) := by
  refine WP.seq (WP.mono (init_step hL hT hc) fun u ⟨hu, hfu⟩ => ?_)
  refine WP.seq (WP.mono (save_ok hL hu) fun u' ⟨hu', hS, hf'⟩ => ?_)
  refine WP.mono (vfin_ok hL hT hu' (dst := fV) (by simp only [fV]; anums)) fun t' ⟨hc', hf'', hm⟩ => ?_
  have hW : Frame (W L ++ [SaveR L]) t.mem u'.mem :=
    (hfu.sub fun r hr => ⟨r, List.mem_append_left _ hr, sub_refl _⟩).trans
      (hf'.sub fun r hr => ⟨r, List.mem_append_right _ hr, sub_refl _⟩)
  have hk : kOf P L t'.mem = kOf P L t.mem := by
    show Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 16) P.H.D = _
    rw [kv_frame hL hf'' (o := 16) (by decide) (.inl (by simp only [fV]; anums)) (by anums) (by simp only [fV]; anums)]
    exact bytesAt_frame hW (fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · simp only [W, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hL.stk_scr0 (by have := L.he; anums) (by decide)
        · exact Offset.disjoint_base _ (by omega_using []) (by anums)
      · simp only [List.mem_singleton] at hr; subst hr
        exact hL.stk_scr (by have := L.he; anums) (by decide)) (by anums)
  have hv : vOf P L u'.mem = vOf P L t.mem :=
    bytesAt_frame hW (fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · simp only [W, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hL.stk_scr0 (by have := L.he; anums) (by decide)
        · exact Offset.disjoint_base _ (by omega_using []) (by anums)
      · simp only [List.mem_singleton] at hr; subst hr
        exact hL.stk_scr (by have := L.he; anums) (by decide)) (by anums)
  refine ⟨hc', ?_, hk, ?_, ?_⟩
  · refine (hW.sub fun r hr => ?_).trans (hf''.sub (wd_kvw (P := P) (dst := fV) (by simp only [fV]; anums)))
    rcases List.mem_append.mp hr with hr | hr
    · exact wd_kvw (P := P) (dst := fV) (by simp only [fV]; anums) r (List.mem_append_left _ hr)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨L.SCR, by simp, Offset.sub_base _ (by decide)⟩
  · rw [show vOf P L t'.mem = Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 (16 + fV)) P.H.D from rfl, hm, hv,
      mac_eq]
  · rw [hk]; exact hS.frame hf'' (wd_save hL (by simp only [fV]; anums))

/-- `V = HMAC_K(V)`, from the saved states for `K`, which it keeps. -/
theorem hmacVR_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t)
    (hS : SavedK P L t.mem (kOf P L t.mem)) :
    WP isa (cfgOf P).hmacVR t fun t' => Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
      kOf P L t'.mem = kOf P L t.mem ∧ vOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem) ∧
      SavedK P L t'.mem (kOf P L t'.mem) := by
  refine WP.seq (WP.mono (restore_ok hL hc hS (blockKey_length (keyOf_length _))) fun u ⟨hu, hfu, hSu⟩ => ?_)
  refine WP.mono (vfin_ok hL hT hu (dst := fV) (by simp only [fV]; anums)) fun t' ⟨hc', hf', hm⟩ => ?_
  have hR : Region.Disjoint ⟨L.B + BitVec.ofNat 64 16, 128⟩ ⟨L.scr + BitVec.ofNat 64 0, 8 * 48⟩ :=
    hL.stk_scr (by have := L.he; anums) (by decide)
  have hk : kOf P L t'.mem = kOf P L t.mem := by
    show Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 16) P.H.D = _
    rw [kv_frame hL hf' (o := 16) (by decide) (.inl (by simp only [fV]; anums)) (by anums) (by simp only [fV]; anums)]
    exact bytesAt_frame hfu (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hR.sub_left (Offset.sub _ (by omega_using []) (by anums))) (by anums)
  have hv : vOf P L u.mem = vOf P L t.mem :=
    bytesAt_frame hfu (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hR.sub_left (Offset.sub _ (by omega_using []) (by anums))) (by anums)
  refine ⟨hc', ?_, hk, ?_, ?_⟩
  · refine (hfu.sub fun r hr => ?_).trans (hf'.sub (wd_kvw (P := P) (dst := fV) (by simp only [fV]; anums)))
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨L.SCR, by simp, Offset.sub_base _ (by decide)⟩
  · rw [show vOf P L t'.mem = Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 (16 + fV)) P.H.D from rfl, hm, hv,
      mac_eq]
  · rw [hk]; exact hSu.frame hf' (wd_save hL (by simp only [fV]; anums))

/-- `K = HMAC_K(V ‖ m)`, for the message `m` of `len` bytes at
`scratch + 2256`, from HMAC's states for `K` by `init` or, if `fresh` is
false, from the saved ones. -/
theorem hmacKB_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) {len : Nat} (hlen : len ≤ 256)
    (fresh : Bool) (hS : fresh = false → SavedK P L t.mem (kOf P L t.mem)) :
    WP isa ((cfgOf P).hmacK fresh len) t fun t' =>
      Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧ vOf P L t'.mem = vOf P L t.mem ∧
      kOf P L t'.mem = P.mac (kOf P L t.mem)
        (vOf P L t.mem ++ Spec.Sha256.bytesAt t.mem (L.scr + BitVec.ofNat 64 2256) len) := by
  have post : ∀ {u : State}, St P L g m₀ (Spec.Hmac.blockKey P.ok.SH.H (kOf P L t.mem)) [] u →
      ∀ {ws : List Region}, Frame ws t.mem u.mem → (∀ r ∈ ws, ∃ r' ∈ KVW L, Region.Sub r r') →
      (∀ r ∈ ws, Region.Disjoint ⟨L.B + BitVec.ofNat 64 80, P.H.D⟩ r) →
      (∀ r ∈ ws, Region.Disjoint ⟨L.scr + BitVec.ofNat 64 2256, len⟩ r) →
      WP isa (.seq (cfgOf P).updV (.seq ((cfgOf P).updM len) ((cfgOf P).fin len fK))) u fun t' =>
        Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧ vOf P L t'.mem = vOf P L t.mem ∧
        kOf P L t'.mem = P.mac (kOf P L t.mem)
          (vOf P L t.mem ++ Spec.Sha256.bytesAt t.mem (L.scr + BitVec.ofNat 64 2256) len) := by
    intro u hu ws hf hk hdv hdm
    refine WP.mono (vmfin_ok hL hT hu hlen) fun t' ⟨hc', hf', hm⟩ => ⟨hc', ?_, ?_, ?_⟩
    · exact (hf.sub hk).trans (hf'.sub (wd_kvw (P := P) (dst := fK) (by simp only [fK]; anums)))
    · show Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 80) P.H.D = _
      rw [kv_frame hL hf' (o := 80) (by decide) (.inr (by simp only [fK]; anums)) (by anums) (by simp only [fK]; anums)]
      exact bytesAt_frame hf hdv (by anums)
    · rw [hm]
      have hv : vOf P L u.mem = vOf P L t.mem := bytesAt_frame hf hdv (by anums)
      have hmsg : Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 2256) len =
          Spec.Sha256.bytesAt t.mem (L.scr + BitVec.ofNat 64 2256) len := bytesAt_frame hf hdm (by omega_using [hlen])
      rw [hv, hmsg, mac_eq]
  cases fresh
  · refine WP.seq (WP.mono (restore_ok hL hc (hS rfl) (blockKey_length (keyOf_length _))) fun u ⟨hu, hfu, _⟩ => ?_)
    have hu' : St P L g m₀ (Spec.Hmac.blockKey P.ok.SH.H (kOf P L t.mem)) [] u := hu
    refine post hu' hfu (fun r hr => ?_) (fun r hr => ?_) (fun r hr => ?_) <;>
      simp only [List.mem_singleton] at hr <;> subst hr
    · exact ⟨L.SCR, by simp, Offset.sub_base _ (by decide)⟩
    · exact hL.stk_scr (by have := L.he; anums) (by decide)
    · exact Offset.disjoint _ (by omega_using []) (by omega_using [hlen]) (by decide)
  · refine WP.seq (WP.mono (init_step hL hT hc) fun u ⟨hu, hfu⟩ => ?_)
    refine post hu hfu (fun r hr => ?_) (fun r hr => ?_) (fun r hr => ?_) <;>
      simp only [W, List.mem_cons, List.not_mem_nil, or_false] at hr <;> rcases hr with rfl | rfl
    · exact ⟨L.SCR, by simp, Region.sub_prefix (by omega_using [])⟩
    · exact ⟨⟨L.B, 144⟩, by simp, Region.sub_prefix (by omega_using [])⟩
    · exact hL.stk_scr0 (by have := L.he; anums) (by decide)
    · exact Offset.disjoint_base _ (by omega_using []) (by anums)
    · exact Offset.disjoint_base _ (by decide) (by omega_using [hlen])
    · exact hL.low_scr (by omega_using [hlen]) |>.symm

/-- What the steps need of the layout: the scalars' bytes, and the table of `P`. -/
def HOk (P : RfcHash) {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) : Prop := L.q = P.Q ∧ TabL P L

/-- `K = HMAC_K(V ‖ m)`, then `V = HMAC_K(V)`, for the message `m = b (‖ d ‖ h)`. -/
theorem rekey_gen (hL : L.Ok) (hq : HOk P L) {t : State} (hc : Ctx L g m₀ t) {b : Nat} {full : Bool}
    (fresh : Bool) (hS : fresh = false → SavedK P L t.mem (kOf P L t.mem)) :
    WP isa (.seq (.block Cfg.msgPtrs) (.seq (.block ((cfgOf P).msg b full))
      (.seq ((cfgOf P).hmacK fresh (mlen P full)) (cfgOf P).hmacVS))) t
      fun t' => Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
        kOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem ++ [BitVec.ofNat 8 b] ++
          (if full then Spec.Sha256.bytesAt t.mem L.d P.Q ++ hOf P L t.mem else [])) ∧
        vOf P L t'.mem = P.mac (kOf P L t'.mem) (vOf P L t.mem) ∧ SavedK P L t'.mem (kOf P L t'.mem) := by
  have hT := hq.2
  refine WP.seq (WP.mono (ptrs_ok hL hc) fun p ⟨hcp, hmp, h9p, h10p, h15p⟩ => ?_)
  rw [← hmp] at hS ⊢
  refine WP.seq (WP.mono (msg_ok (P := P) hL hq.1 hcp h9p h10p h15p b full) fun u ⟨hcu, hfu, hbu⟩ => ?_)
  have hsafe : Region.Disjoint ⟨L.B + BitVec.ofNat 64 16, 128⟩ ⟨L.scr + BitVec.ofNat 64 2256, 1 + 2 * P.Q⟩ :=
    hL.stk_scr (by have := L.he; anums) (by anums)
  have hku : kOf P L u.mem = kOf P L p.mem := bytesAt_frame hfu (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hsafe.sub_left (Offset.sub _ (by omega_using []) (by anums))) (by anums)
  have hvu : vOf P L u.mem = vOf P L p.mem := bytesAt_frame hfu (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hsafe.sub_left (Offset.sub _ (by omega_using []) (by anums))) (by anums)
  have hSu : fresh = false → SavedK P L u.mem (kOf P L u.mem) := fun h => hku ▸ (hS h).frame hfu fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (by anums) (by anums) (by anums)
  refine WP.seq (WP.mono (hmacKB_ok (P := P) hL hT hcu (len := mlen P full)
    (by cases full <;> simp only [mlen, Bool.false_eq_true, ite_true, ite_false] <;> anums) fresh hSu)
    fun w ⟨hcw, hfw, hvw, hkw⟩ => ?_)
  refine WP.mono (hmacVS_ok hL hT hcw) fun t' ⟨hc', hf', hk', hv', hs'⟩ => ⟨hc', ?_, ?_, ?_, hs'⟩
  · exact ((hfu.sub (kvw_of fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact .inl (Offset.sub_base _ (by anums)))).trans hfw).trans hf'
  · rw [hk', hkw, hku, hvu, hbu, List.append_assoc]
  · rw [hv', hk', hvw, hvu]

/-- `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then `V = HMAC_K(V)` (steps d–e, f–g). -/
theorem rekeyFull_ok (hL : L.Ok) (hq : HOk P L) {t : State} (hc : Ctx L g m₀ t) (b : Nat)
    (hS : b ≠ 0 → SavedK P L t.mem (kOf P L t.mem)) :
    WP isa ((cfgOf P).rekeyFull b) t fun t' => Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
      kOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem ++ [BitVec.ofNat 8 b] ++
        (Spec.Sha256.bytesAt t.mem L.d P.Q ++ hOf P L t.mem)) ∧
      vOf P L t'.mem = P.mac (kOf P L t'.mem) (vOf P L t.mem) ∧ SavedK P L t'.mem (kOf P L t'.mem) := by
  unfold Cfg.rekeyFull
  refine WP.mono (rekey_gen (full := true) hL hq hc (decide (b = 0)) fun h => hS (by simpa using h))
    fun t' h => ?_
  simpa using h

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)` (step h.3). -/
theorem rekey_ok (hL : L.Ok) (hq : HOk P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).rekey t fun t' => Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
      kOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem ++ [0]) ∧
      vOf P L t'.mem = P.mac (kOf P L t'.mem) (vOf P L t.mem) ∧ SavedK P L t'.mem (kOf P L t'.mem) :=
  WP.mono (rekey_gen (b := 0) (full := false) hL hq hc true (fun h => absurd h (by decide)))
    fun _ h => ⟨h.1, h.2.1, by rw [h.2.2.1]; simp, h.2.2.2⟩

end VG.Proof.Ecdsa.Rfc6979.AArch64

end

end

/-! ### `Ecdsa.Rfc6979.AArch64.Wide`, which only this module used -/

section

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
  obtain h200 := hc.inFr (d := 200) (by omega_arith) (by omega_arith)
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
  obtain hS₂ : Scr u₂ L.scr 8192 :=
    ⟨by rw [h₂.keep _ (by decide), h₁.val], by rw [hc₂.wr]; simp, nc, by decide⟩
  have hx6 : u₂.gpr .x6 = L.B + BitVec.ofNat 64 (16 + o) := h₂.val
  rw [WP.block_append_iff]
  refine WP.mono_syms (loadBytes_ok hS₂ (len := 66) (n := 9) (o := 2560) (src := .x6) (by decide) (by decide)
    (by omega_arith) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun d hd => by rw [hx6, Offset.add_add]; exact hc₂.inFr (by omega_arith) (by omega_arith))
    (by rw [hx6]; exact (hL.stk_scr (by omega_arith) (by omega_arith)))) fun u₃ ⟨hv₃, k₃, O₃⟩ sy₃ => ?_
  rw [WP.block_append_iff]
  obtain hS₃ : Scr u₃ L.scr 8192 := ⟨by rw [k₃.gpr _ (by decide)]; exact hS₂.x0, k₃.wr ▸ hS₂.wr, nc, by decide⟩
  refine WP.mono_syms (shrWords_ok hS₃ (n := 9) (o := 2560) (sh := s) (by omega_arith) (by decide) hs₁ hs₂)
    fun u₄ ⟨hv₄, k₄, O₄⟩ sy₄ => ?_
  rw [WP.block_append_iff]
  refine WP.mono_syms (ones_ok u₄) fun u₅ ⟨h3₅, k₅, m₅, _⟩ sy₅ => ?_
  obtain hS₅ : Scr u₅ L.scr 8192 :=
    ⟨by rw [k₅.gpr _ (by decide), k₄.gpr _ (by decide)]; exact hS₃.x0, k₅.wr ▸ k₄.wr ▸ hS₃.wr, nc, by decide⟩
  obtain hx6₅ : u₅.gpr .x6 = L.B + BitVec.ofNat 64 (16 + o) := by
    rw [k₅.gpr _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (by decide), hx6]
  obtain hwr₅ : u₅.wr = u₂.wr := by rw [k₅.wr, k₄.wr, k₃.wr]
  refine WP.mono_syms (storeBytes_ok hS₅ (len := 66) (n := 9) (d := 0) (a := 2560) (dst := .x6) (by decide)
    (by decide) (by decide) true (by rw [h3₅]; rfl) (by omega_arith) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by rw [hx6₅, add_ofNat_zero, toNat_add_of (by omega_arith)]; omega_arith)
    (fun e m hem => by
      rw [hx6₅, add_ofNat_zero, Offset.add_add, hwr₅]; exact hc₂.inFrW (by omega_arith) (by omega_arith))
    (by rw [hx6₅, add_ofNat_zero]; exact (hL.stk_scr (by omega_arith) (by omega_arith)).symm)) fun u₆ ⟨hb₆, k₆, O₆⟩ sy₆ => ?_
  rw [hx6₅, add_ofNat_zero] at hb₆ O₆
  -- What changed: the words at `scratch + 2560`, and the bytes converted.
  obtain hf : Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 (16 + o), 66⟩] t.mem u₆.mem := by
    obtain f₃ := frame_of_outside (O₃.trans O₄) (by omega_arith)
    obtain f₆ := frame_of_outside O₆ (by omega_arith)
    rw [add_ofNat_zero, m₅] at f₆
    rw [h₂.mem, h₁.mem, show 8 * 9 = 72 from rfl] at f₃
    exact (f₃.sub fun r hr => ⟨r, by simp_all, sub_refl _⟩).trans (f₆.sub fun r hr => ⟨r, by simp_all, sub_refl _⟩)
  obtain hk : ∀ r ∈ preserved, r ≠ .x30 → u₆.gpr r = t.gpr r := fun r hr h30 => by
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
  obtain hf : Frame [⟨L.B + BitVec.ofNat 64 (16 + o), 8⟩] u.mem u₂.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  exact ⟨hc.keep hL hrd hwr hsp (fun r _ _ => by rw [hg]) hf (hsy := hsy)
    (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact safe_high L (d := 16 + o) (n := 8) (by omega_using [ho₁]) (by omega_using [ho₂])),
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
    refine WP.mono (zstrs_ok hL ho₁ ho₂ ho8 k (by omega_using [hk]) hc h15 h14) fun u₁ ⟨hc₁, hg₁, hf₁, hb₁⟩ => ?_
    refine WP.mono (zstr_ok hL hc₁ (by rw [hg₁, h15]) (by rw [hg₁, h14]) (o := o + 8 * k) (by omega_using [ho₁]) (by omega_using [ho₂, hk])
      (by omega_using [ho8])) fun u₂ ⟨hc₂, hg₂, hf₂, hb₂⟩ => ?_
    refine ⟨hc₂, hg₂.trans hg₁, hf₁.trans (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _,
      by simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega_using []) (by omega_using [hk])⟩), ?_⟩
    rw [show 8 * (k + 1) = 8 * k + 8 by omega_using [], Proof.Hmac.Common.bytesAt_add, Offset.add_add,
      show 16 + o + 8 * k = 16 + (o + 8 * k) by omega_using [], hb₂ 8 (Nat.le_refl _),
      bytesAt_frame hf₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega_using []) (by omega_arith) (by omega_arith)) (by omega_using [hk]), hb₁, List.replicate_append_replicate]

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
  exact conv_ok hL hW hc (o := fT) (s := P.R.sh) (by decide) (by decide) (by decide) (by omega_using [hsh]) (by omega_using [hsh8])

end VG.Proof.Ecdsa.Rfc6979.AArch64

end

end


/-!
# Deterministic ECDSA on AArch64: the digest into `X`

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Prep.lean`): the byte loop
`cpLoop`, `x13` bytes from `x11` to `x12` with `Ctx` kept, for a destination
the code may write apart from the source (`cp_ok`), and `X` (`prepX_ok`):
`Q - m` zero bytes, then the digest's first `m = min(D, Q)`, its length the
smaller of the frame's `D` and `Q` (`min_ok`, by `subs` and `csel`); and, if
`big`, the digest for `core` (`prepC_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64
open VG.Proof.RsaOaep.AArch64 (count_loop counter_step counter_ne carry_sub read_one byte64 byte_rt64 write1_apply)
open VG.Proof.Mgf1 (ifp ifn)

variable {P : RfcHash} {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} {L : Lay dn E} {g : Reg → BitVec 64} {m₀ : Mem}

/-! ## `X` -/

/-- `subs x10, x13, x9; csel x13, x9, x13`: the smaller of the two in `x13`. -/
theorem min_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h13 : u.gpr .x13 = BitVec.ofNat 64 a) (h9 : u.gpr .x9 = BitVec.ofNat 64 b) :
    WP isa (.block [.subs .x .x10 .x13 .x9, .csel .x .x13 .x9 .x13]) u fun u' => Ctx L g m₀ u' ∧
      u'.mem = u.mem ∧ u'.gpr .x13 = BitVec.ofNat 64 (min a b) ∧
      ∀ r, r ≠ .x10 → r ≠ .x13 → u'.gpr r = u.gpr r := by
  obtain hta : (u.gpr .x13).toNat = a := by rw [h13, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
  obtain htb : (u.gpr .x9).toNat = b := by rw [h9, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits, BitVec.setWidth_eq,
    RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, RegUpd.mem_addWithCarry, RegUpd.gpr_write, RegUpd.mem_write,
    reduceCtorEq, ite_false, ite_true, Option.some.injEq, exists_eq_left']
  rw [carry_sub, hta, htb]
  refine ⟨hc.regs hL (by atriv) (by atriv) (by atriv) (by atriv) (fun r hr _ => ?_) (by atriv), by atriv, ?_,
    fun r h₁ h₂ => ?_⟩
  · simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, ne_cs hr (by decide : Reg.x13 ∉ preserved),
      ne_cs hr (by decide : Reg.x10 ∉ preserved), ite_false]
  · by_cases h : b ≤ a
    · simp only [h, decide_true, ite_true, h9, Nat.min_eq_right h]
    · simp only [h, decide_false, Bool.false_eq_true, ite_false, h13, Nat.min_eq_left (show a ≤ b by omega_using [h])]
  · simp only [h₁, h₂, ite_false]

/-- `x12 = sp + o - x13` and the digest in `x11`. -/
theorem xTail_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {o : Nat} (ho : o < 4096) :
    WP isa (.block [.addSp .x12 o, .sub .x .x12 .x12 .x13, .ldrSp .x11 fDigest]) u fun u' => Ctx L g m₀ u' ∧
      u'.mem = u.mem ∧ u'.gpr .x12 = L.B + BitVec.ofNat 64 (16 + o) - u.gpr .x13 ∧ u'.gpr .x11 = L.dg ∧
      ∀ r, r ≠ .x11 → r ≠ .x12 → u'.gpr r = u.gpr r := by
  rw [show ([.addSp .x12 o, .sub .x .x12 .x12 .x13, .ldrSp .x11 fDigest] : List Instr) =
    Cfg.fr .x12 o ++ [.sub .x .x12 .x12 .x13] ++ [.ldrSp .x11 fDigest] from rfl, WP.block_append_iff,
    WP.block_append_iff]
  refine WP.mono (fr_ok hL hc (d := .x12) (by decide) ho) fun u₁ h₁ => ?_
  refine WP.mono (show WP isa (.block [.sub .x .x12 .x12 .x13]) u₁
      (Upd L g m₀ u₁ .x12 (u₁.gpr .x12 - u₁.gpr .x13)) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits, BitVec.setWidth_eq,
      Option.some.injEq, exists_eq_left']
    exact ⟨h₁.ctx.set hL (d := .x12) (by decide) rfl rfl rfl rfl (fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr) rfl,
      rfl, by rw [RegUpd.gpr_write_self]; exact BitVec.setWidth_eq _,
      fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr⟩) fun u₂ h₂ => ?_
  refine WP.mono (ldF_ok hL h₂.ctx (d := .x11) (by decide) (o := fDigest) (by simp only [fDigest]; have := L.he; omega_using [])
    rfl) fun u₃ h₃ => ?_
  refine ⟨h₃.ctx, by rw [h₃.mem, h₂.mem, h₁.mem], by rw [h₃.keep _ (by decide), h₂.val, h₁.val,
    h₁.keep _ (by decide)], by rw [h₃.val, h₂.mem, h₁.mem]; exact hc.pDg, fun r a b => by
    rw [h₃.keep _ a, h₂.keep _ b, h₁.keep _ b]⟩

theorem sub_min (B : Addr) {a b c : Nat} (h : c ≤ b) :
    B + BitVec.ofNat 64 (a + b) - BitVec.ofNat 64 c = B + BitVec.ofNat 64 (a + (b - c)) := by
  rw [show a + b = a + (b - c) + c by omega_using [h], ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc, BitVec.add_sub_cancel]

/-- The arguments of `X`'s copy: `X` cleared, `x13 = m = min(D, Q)`, the
digest in `x11` and `X + Q - m` in `x12`. -/
theorem xArgs_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block (cfgOf P).xArgs) t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.B + BitVec.ofNat 64 (16 + fX), 72⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (16 + fX)) 72 = List.replicate 72 0 ∧
      u.gpr .x13 = BitVec.ofNat 64 (min P.H.D P.Q) ∧
      u.gpr .x12 = L.B + BitVec.ofNat 64 (16 + fX + (P.Q - min P.H.D P.Q)) ∧ u.gpr .x11 = L.dg := by
  have he := L.he
  obtain ⟨-, -, -, -, -, -, hD16, hD64, -, -, -, -, -, -, hQ8, hQ66, -, -⟩ := P.sizes
  have hlen : (cfgOf P).len = P.Q := rfl
  rw [Cfg.xArgs, WP.block_append_iff]
  refine WP.mono (zero9_ok hL (o := fX) (by decide) (by simp only [fX]; omega_using [he]) (by decide) hc)
    fun u₁ ⟨hc₁, _, _, hf₁, hb₁⟩ => ?_
  rw [hlen, show ([.ldrSp .x13 fDl, .movz .x .x9 (BitVec.ofNat 16 P.Q) 0, .subs .x .x10 .x13 .x9,
      .csel .x .x13 .x9 .x13, .addSp .x12 (fX + P.Q), .sub .x .x12 .x12 .x13, .ldrSp .x11 fDigest] : List Instr) =
    [.ldrSp .x13 fDl] ++ [.movz .x .x9 (BitVec.ofNat 16 P.Q) 0] ++ [.subs .x .x10 .x13 .x9, .csel .x .x13 .x9 .x13] ++
      [.addSp .x12 (fX + P.Q), .sub .x .x12 .x12 .x13, .ldrSp .x11 fDigest] from rfl,
    WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ldD_ok hL hT hc₁ (d := .x13) (by decide)) fun u₂ h₂ => ?_
  refine WP.mono (movz_ok hL h₂.ctx (d := .x9) (by decide) (n := P.Q) (by omega_using [hQ66])) fun u₃ h₃ => ?_
  obtain h13₃ : u₃.gpr .x13 = BitVec.ofNat 64 P.H.D := by rw [h₃.keep _ (by decide), h₂.val]
  refine WP.mono (min_ok hL h₃.ctx (a := P.H.D) (b := P.Q) (by omega_using [hD64]) (by omega_using [hQ66]) h13₃ h₃.val)
    fun u₄ ⟨hc₄, hm₄, h13₄, hg₄⟩ => ?_
  refine WP.mono (xTail_ok hL hc₄ (o := fX + P.Q) (by simp only [fX]; omega_using [hQ66]))
    fun u₅ ⟨hc₅, hm₅, h12₅, h11₅, hg₅⟩ => ?_
  obtain hm : min P.H.D P.Q ≤ P.Q := Nat.min_le_right _ _
  rw [h13₄, ← Nat.add_assoc, sub_min _ hm] at h12₅
  obtain hm₅' : u₅.mem = u₁.mem := by rw [hm₅, hm₄, h₃.mem, h₂.mem]
  exact ⟨hc₅, hm₅' ▸ hf₁, hm₅' ▸ hb₁, by rw [hg₅ _ (by decide) (by decide), h13₄], h12₅, h11₅⟩

/-- `X`, the `Q` bytes at `fX`: `Q - m` zero bytes, then the digest's first
`m = min(D, Q)`. -/
theorem prepX_ok (hL : L.Ok) (hT : TabL P L) (hdn : P.H.D ≤ dn) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).prepX t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.B + BitVec.ofNat 64 (16 + fX), 72⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (16 + fX)) P.Q =
        List.replicate (P.Q - min P.H.D P.Q) 0 ++ Spec.Sha256.bytesAt t.mem L.dg (min P.H.D P.Q) := by
  have he := L.he
  have hnb := hL.nB
  obtain ⟨-, -, -, -, -, -, hD16, hD64, -, -, -, -, -, -, hQ8, hQ66, -, -⟩ := P.sizes
  rw [Cfg.prepX]
  refine WP.seq (WP.mono (xArgs_ok hL hT hc) fun u₅ ⟨hc₅, hf₁, hb₁, h13₅, h12₅, h11₅⟩ => ?_)
  obtain hm : min P.H.D P.Q ≤ P.Q := Nat.min_le_right _ _
  obtain hm8 : 8 ≤ min P.H.D P.Q := by omega_using [hD16, hQ8]
  refine WP.mono (cp_ok hL hc₅ (p := L.B + BitVec.ofNat 64 (16 + fX + (P.Q - min P.H.D P.Q))) (q := L.dg)
      (n := min P.H.D P.Q) (by omega_using [hD16, hQ8]) (by omega_using [hD64]) h13₅ h12₅ h11₅ ?_ (hc₅.inFrW (by omega_using []) (by simp only [fX]; omega_using [he, hQ66]))
      (safe_high L (by simp only [fX]; omega_using []) (by simp only [fX]; omega_using [he, hQ66]))
      (fun i hi => hc₅.inDg (o := i) (n := 1) (by omega_using [hdn, hi]) (by omega_using [hD64, hi]))
      (fun i hi hcon => hL.kg _ (Offset.sub_base L.B (k := 256 + 8 * L.e) (by simp only [fX]; omega_using [he, hQ66]) _ hcon)
        (Offset.contains_base L.dg (d := i) (n := 1) (k := dn) (by omega_using [hdn, hi]) (by omega_using [hD64, hi]))))
    fun u ⟨hc', _, hf, hb⟩ => ?_
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 + fX + _) (by simp only [fX]; omega_using [hQ66]),
      Nat.mod_eq_of_lt (by simp only [fX]; omega_using [he, hnb, hQ66])]
    simp only [fX]; omega_using [he, hnb, hQ66]
  obtain hdn' : min P.H.D P.Q ≤ dn := by omega_using [hdn]
  obtain hdg : Spec.Sha256.bytesAt u₅.mem L.dg (min P.H.D P.Q) = Spec.Sha256.bytesAt t.mem L.dg (min P.H.D P.Q) :=
    bytesAt_frame hf₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact fun a h₁ h₂ => hL.kg a (Offset.sub_base L.B (d := 16 + fX) (n := 72) (k := 256 + 8 * L.e)
        (by simp only [fX]; omega_using [he]) a h₂) (Region.sub_prefix hdn' a h₁)) (by omega_using [hD64])
  refine ⟨hc', hf₁.trans ?_, ?_⟩
  · exact hf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by omega_using []) (by simp only [fX]; omega_using [hQ66])⟩
  · rw [show P.Q = (P.Q - min P.H.D P.Q) + min P.H.D P.Q by omega_using [], Proof.Hmac.Common.bytesAt_add,
      Offset.add_add, hb, ← show P.Q = (P.Q - min P.H.D P.Q) + min P.H.D P.Q by omega_using [],
      bytesAt_frame hf (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inl (by omega_using [])) (by simp only [fX]; omega_using [hQ66]) (by simp only [fX]; omega_using [hQ66])) (by omega_using [hQ66]),
      hdg]
    rw [bytesAt_take _ _ (k := 72) (by omega_using [hQ66]), hb₁, List.take_replicate, Nat.min_eq_left (by omega_using [hQ66])]

/-! ## P-521's digest for `core` -/

theorem shift_back (e sh : Nat) (hs : sh < 8) : (e * 2 ^ 8) >>> (8 - sh) = e * 2 ^ sh := by
  rw [Nat.shiftRight_eq_div_pow, show e * 2 ^ 8 = e * 2 ^ sh * 2 ^ (8 - sh) by
    rw [Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega_using [hs], Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

/-- If `big`: the digest for `core`, the digest's number shifted left by
`sh` bits, in `Q` bytes at `fXc`. -/
theorem prepC_ok (hL : L.Ok) (hT : TabL P L) (hW : P.R.big = true) (hdn : P.H.D ≤ dn) {t : State}
    (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).prepC t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 (16 + fXc), 72⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (16 + fXc)) P.Q =
        Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem L.dg P.H.D) * 2 ^ P.R.sh) := by
  have he := L.he
  have hnb := hL.nB
  obtain ⟨-, hQ66, hQD⟩ := P.sizesW hW
  obtain ⟨-, -, -, -, -, -, hD16, hD64, -, -, -, -, -, -, -, -, -, -⟩ := P.sizes
  have hsl := P.R.nBits_len
  obtain hnb5 := (P.R.sizesW hW).2.2
  obtain hsh8 : P.R.sh < 8 := by simp only [RfcHash.Q] at hQ66; omega_using [hsl]
  obtain hsh1 : 1 ≤ P.R.sh := by simp only [RfcHash.Q] at hQ66; omega_using [hsl, hnb5]
  have hlen : (cfgOf P).len = P.Q := rfl
  have hsc : (cfgOf P).sh = P.R.sh := rfl
  rw [Cfg.prepC]
  refine WP.seq ?_
  rw [Cfg.xcArgs, WP.block_append_iff]
  refine WP.mono (zero9_ok hL (o := fXc) (by decide) (by simp only [fXc]; omega_using [he]) (by decide) hc)
    fun u₁ ⟨hc₁, _, _, hf₁, hb₁⟩ => ?_
  rw [hlen, show ([.ldrSp .x13 fDl, .addSp .x12 (fXc + P.Q - 1), .sub .x .x12 .x12 .x13, .ldrSp .x11 fDigest] :
      List Instr) = [.ldrSp .x13 fDl] ++ [.addSp .x12 (fXc + P.Q - 1), .sub .x .x12 .x12 .x13, .ldrSp .x11 fDigest]
      from rfl, WP.block_append_iff]
  refine WP.mono (ldD_ok hL hT hc₁ (d := .x13) (by decide)) fun u₂ h₂ => ?_
  refine WP.mono (xTail_ok hL h₂.ctx (o := fXc + P.Q - 1) (by simp only [fXc]; omega_using [hQ66]))
    fun u₃ ⟨hc₃, hm₃, h12₃, h11₃, hg₃⟩ => ?_
  obtain hx : 16 + (fXc + P.Q - 1 - P.H.D) = 16 + fXc + (P.Q - 1 - P.H.D) := by omega_using [hQD]
  rw [h₂.val, show 16 + (fXc + P.Q - 1) = 16 + (fXc + P.Q - 1) from rfl, sub_min _ (by omega_using [hQD]), hx] at h12₃
  obtain hm₁ : u₃.mem = u₁.mem := by rw [hm₃, h₂.mem]
  obtain hdg : Spec.Sha256.bytesAt u₁.mem L.dg P.H.D = Spec.Sha256.bytesAt t.mem L.dg P.H.D :=
    bytesAt_frame hf₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact fun a h₁ h₂ => hL.kg a (Offset.sub_base L.B (d := 16 + fXc) (n := 72) (k := 256 + 8 * L.e)
        (by simp only [fXc]; omega_using [he]) a h₂) (Region.sub_prefix hdn a h₁)) (by omega_using [hD64])
  refine WP.seq (WP.mono (cp_ok hL hc₃ (p := L.B + BitVec.ofNat 64 (16 + fXc + (P.Q - 1 - P.H.D))) (q := L.dg)
      (n := P.H.D) (by omega_using [hD16]) (by omega_using [hD64]) (by rw [hg₃ _ (by decide) (by decide), h₂.val])
      h12₃ h11₃ ?_ (hc₃.inFrW (by omega_using []) (by simp only [fXc]; omega_using [he, hQ66, hQD]))
      (safe_high L (by simp only [fXc]; omega_using []) (by simp only [fXc]; omega_using [he, hQ66, hQD]))
      (fun i hi => hc₃.inDg (o := i) (n := 1) (by omega_using [hdn, hi]) (by omega_using [hD64, hi]))
      (fun i hi hcon => hL.kg _ (Offset.sub_base L.B (k := 256 + 8 * L.e) (by simp only [fXc]; omega_using [he, hQ66, hQD]) _ hcon)
        (Offset.contains_base L.dg (d := i) (n := 1) (k := dn) (by omega_using [hdn, hi]) (by omega_using [hD64, hi]))))
    fun u₄ ⟨hc₄, _, hf₄, hb₄⟩ => ?_)
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 + fXc + _) (by simp only [fXc]; omega_using [hQ66]),
      Nat.mod_eq_of_lt (by simp only [fXc]; omega_using [he, hnb, hQ66])]
    simp only [fXc]; omega_using [he, hnb, hQ66, hQD]
  rw [hsc]
  refine WP.mono (conv_ok hL hW hc₄ (o := fXc) (s := 8 - P.R.sh) (by decide) (by decide) (by decide) (by omega_using [hsl])
    (by omega_using [])) fun u₆ ⟨hc₆, hf₆, hb₆⟩ => ?_
  refine ⟨hc₆, ?_, ?_⟩
  · refine ((hf₁.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩).trans
      (hm₁ ▸ hf₄.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩)).trans
      (hf₆.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact fun _ h => h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Region.sub_prefix (by omega_using [hQ66])⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega_using []) (by simp only [fXc]; omega_using [hQ66, hQD])
  · -- `Q - D - 1` zero bytes, the digest, and a zero byte, shifted right by `8 - sh` bits.
    obtain hz : ∀ a n, a + n ≤ 72 → Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 (16 + fXc + a)) n =
        List.replicate n 0 := fun a n han => by
      obtain h1 := bytesAt_take u₁.mem (L.B + BitVec.ofNat 64 (16 + fXc)) (n := a + n) (k := 72) (by omega_using [han])
      rw [hb₁, List.take_replicate, Nat.min_eq_left (by omega_using [han]), Proof.Hmac.Common.bytesAt_add, Offset.add_add,
        ← List.replicate_append_replicate] at h1
      exact (List.append_inj h1 (by simp [Spec.Sha256.bytesAt])).2
    obtain hY : Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 (16 + fXc)) P.Q =
        List.replicate (P.Q - 1 - P.H.D) 0 ++ (Spec.Sha256.bytesAt t.mem L.dg P.H.D ++ List.replicate 1 0) := by
      obtain e := Proof.Hmac.Common.bytesAt_add u₄.mem (L.B + BitVec.ofNat 64 (16 + fXc)) (P.Q - 1 - P.H.D)
        (P.H.D + 1)
      obtain e' := Proof.Hmac.Common.bytesAt_add u₄.mem
        (L.B + BitVec.ofNat 64 (16 + fXc) + BitVec.ofNat 64 (P.Q - 1 - P.H.D)) P.H.D 1
      rw [show P.Q - 1 - P.H.D + (P.H.D + 1) = P.Q by omega_using [hQD]] at e
      rw [Offset.add_add, Offset.add_add] at e'
      rw [Offset.add_add] at e
      obtain p₁ : Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 (16 + fXc)) (P.Q - 1 - P.H.D) =
          List.replicate (P.Q - 1 - P.H.D) 0 := by
        rw [bytesAt_frame hf₄ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Offset.disjoint _ (.inl (by omega_using [])) (by simp only [fXc]; omega_using [hQ66]) (by simp only [fXc]; omega_using [hQ66, hQD]))
          (by omega_using [hQ66]), hm₁]
        have := hz 0 (P.Q - 1 - P.H.D) (by omega_using [hQ66])
        rwa [Nat.add_zero] at this
      obtain p₃ : Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 (16 + fXc + (P.Q - 1 - P.H.D) + P.H.D)) 1 =
          List.replicate 1 0 := by
        rw [bytesAt_frame hf₄ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Offset.disjoint _ (.inr (by omega_using [])) (by simp only [fXc]; omega_using [hQ66, hQD]) (by simp only [fXc]; omega_using [hQ66, hQD]))
          (by omega_using []), hm₁, show 16 + fXc + (P.Q - 1 - P.H.D) + P.H.D = 16 + fXc + (P.Q - 1 - P.H.D + P.H.D) by omega_using []]
        exact hz (P.Q - 1 - P.H.D + P.H.D) 1 (by omega_using [hQ66, hQD])
      rw [e, e', hb₄, hm₁, hdg, p₁, p₃]
    rw [hb₆, hY, Rfc6979.ofBytes_zeros, Rfc6979.ofBytes_append_zeros, show 8 * 1 = 8 from rfl, shift_back _ _ hsh8]

end VG.Proof.Ecdsa.Rfc6979.AArch64
