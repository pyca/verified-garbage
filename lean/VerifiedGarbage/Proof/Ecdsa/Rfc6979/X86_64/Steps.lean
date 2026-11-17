module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Hash
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.X86_64
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Regs
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Copy
import VerifiedGarbage.Proof.Hmac.Common

/-! ### `Ecdsa.Rfc6979.X86_64.Hmac`, which only this module used -/

section

/-!
# Deterministic ECDSA on x86-64: HMAC through the table

The table's functions, each called indirectly (`tcall_ok`: the table's word,
which `Ctx` says holds the function of `L.H`, whose call an indirect call of
`L.f`'s functions reaches), with the lengths and counts the frame's `D` and
`B` give (`ldF_ok`, `addF_ok`):

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
and working space (the first 2256 bytes of `scratch`), the 24 bytes below the
frame (`W`), and `dst`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64

/-- Where the data may be: in the frame below its pointers, or in `scratch`
above HMAC's working space. -/
def DataOk {dn : Nat} (L : Lay dn) (da : Addr) (len : Nat) : Prop :=
  (∃ o, da = L.B + BitVec.ofNat 64 o ∧ 24 ≤ o ∧ o + len ≤ 208) ∨
    (∃ o, da = L.scr + BitVec.ofNat 64 o ∧ 2256 ≤ o ∧ o + len ≤ 8192)

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {m₀ : Mem}

namespace DataOk

variable {da : Addr} {len : Nat}

theorem low (hd : DataOk L da len) (hL : L.Ok) : Region.Disjoint ⟨L.B, 24⟩ ⟨da, len⟩ := by
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

/-! ## Loads from the frame -/

/-- `d ← [rsp + o]`, a word of the frame. -/
theorem ldF_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {d : Reg} (hd : d ∉ calleeSaved) {o : Nat}
    (ho : o + 8 ≤ 224 + 8 * L.e) :
    WP isa (.block [.mov d (.mem (stk o))]) u
      (Upd L g m₀ u d (u.mem.readW (L.B + BitVec.ofNat 64 (24 + o)) 64)) := by
  obtain hr := hc.inFr (d := 24 + o) (by omega_using []) (by omega_using [ho])
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, ea_stk, hc.rsp,
    Offset.add_add, hr, ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨hc.set hL hd rfl rfl rfl rfl fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl,
    RegUpd.gpr_setReg_self _ _ _, fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr⟩

/-- `d ← d + [rsp + o]`, a word of the frame. -/
theorem addF_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {d : Reg} (hd : d ∉ calleeSaved) {o : Nat}
    (ho : o + 8 ≤ 224 + 8 * L.e) :
    WP isa (.block [.alu .add d (.mem (stk o))]) u
      (Upd L g m₀ u d (u.gpr d + u.mem.readW (L.B + BitVec.ofNat 64 (24 + o)) 64)) := by
  obtain hr := hc.inFr (d := 24 + o) (by omega_using []) (by omega_using [ho])
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, State.load64, ea_stk, hc.rsp,
    Offset.add_add, hr, ite_true, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨hc.set hL hd rfl rfl rfl rfl fun r hr => ?_, rfl, RegUpd.gpr_setReg_self _ _ _, fun r hr => ?_⟩
  · rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]
  · rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]

/-- `d ← d + n`. -/
theorem addI_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {d : Reg} (hd : d ∉ calleeSaved) {n : Nat}
    (hn : n < 2 ^ 31) :
    WP isa (.block [.alu .add d (.imm (BitVec.ofNat 32 n))]) u (Upd L g m₀ u d (u.gpr d + BitVec.ofNat 64 n)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, sx32 hn,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨hc.set hL hd rfl rfl rfl rfl fun r hr => ?_, rfl, RegUpd.gpr_setReg_self _ _ _, fun r hr => ?_⟩
  · rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]
  · rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]

/-! ## The table -/

/-- The layout's table is of `P`'s hash function and functions. -/
def TabL (P : RfcHash) {dn : Nat} (L : Lay dn) : Prop := L.H = P.H ∧ L.f = P.f

/-- The frame's `D`. -/
theorem Ctx.dl (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) :
    t.mem.readW (L.B + BitVec.ofNat 64 (24 + fDl)) 64 = BitVec.ofNat 64 P.H.D := by
  rw [← hT.1]; exact hc.pDl

/-- The frame's `B`. -/
theorem Ctx.bl (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) :
    t.mem.readW (L.B + BitVec.ofNat 64 (24 + fBl)) 64 = BitVec.ofNat 64 P.H.P.B := by
  rw [← hT.1]; exact hc.pBl

/-- The table's words, as on entry. -/
theorem Ctx.tabWord (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {o : Nat} (ho : o + 8 ≤ 48) :
    t.mem.readW (L.tab + BitVec.ofNat 64 o) 64 = m₀.readW (L.tab + BitVec.ofNat 64 o) 64 :=
  hc.frame.readW (r := L.TAB) (Offset.contains_base _ ho (by have := hL.nt; omega_using [ho])) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.to
    · exact hL.tc
    · exact hL.tk) (by decide)

/-- The table's address into `r11`. -/
theorem tblk1_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block [.mov .r11 (.mem (stk fTab))]) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧
      t'.gpr .r11 = L.tab ∧ (∀ r, r ≠ .r11 → t'.gpr r = t.gpr r) := by
  have he := L.he
  refine WP.mono (ldF_ok hL hc (d := .r11) (by decide) (o := fTab) (by simp only [fTab, extra]; omega_using [he]))
    fun t' h => ⟨h.ctx, h.mem, h.val.trans ?_, h.keep⟩
  rw [show 24 + fTab = 240 + 8 * L.e by simp only [fTab, extra]; omega_using [he]]; exact hc.pTab

/-- The table's word `j` into `r11`, from its address there. -/
theorem tblk2_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (h11 : t.gpr .r11 = L.tab) {j : Nat}
    (hj : 8 * j + 8 ≤ 48) :
    WP isa (.block [.mov .r11 (.mem (at_ .r11 (8 * j)))]) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧
      t'.gpr .r11 = m₀.readW (L.tab + BitVec.ofNat 64 (8 * j)) 64 ∧ (∀ r, r ≠ .r11 → t'.gpr r = t.gpr r) ∧
      t'.syms = t.syms := by
  obtain ht := hc.inTab hL (o := 8 * j) hj
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, ea_at, h11, ht, ite_true,
    Option.map_some, hc.tabWord hL hj, RegUpd.gpr_setReg_self, RegUpd.mem_setReg, Option.some.injEq,
    exists_eq_left']
  exact ⟨hc.set hL (d := .r11) (by decide) rfl rfl rfl rfl fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, trivial,
    trivial, fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl⟩

/-- The indirect call of the table's function `j`, at the address its word
`j` holds, of `n`. -/
theorem tcall_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {j : Nat} (hj : 8 * j + 8 ≤ 48)
    {n : String} {c : Prog isa} {ts : List (String × Prog isa)}
    (hw : m₀.readW (L.tab + BitVec.ofNat 64 (8 * j)) 64 = t.syms n)
    (hf : ts.find? (fun q => t.syms q.1 == t.syms n) = some (n, c)) {Q : State → Prop}
    (h : ∀ t', Ctx L g m₀ t' → t'.mem = t.mem → (∀ r, r ≠ .r11 → t'.gpr r = t.gpr r) → t'.syms = t.syms →
      WP isa (.call n c) t' Q) :
    WP isa (Cfg.tcall j ts) t Q := by
  unfold Cfg.tcall
  rw [show ([.mov .r11 (.mem (stk fTab)), .mov .r11 (.mem (at_ .r11 (8 * j)))] : List Instr) =
    [.mov .r11 (.mem (stk fTab))] ++ [.mov .r11 (.mem (at_ .r11 (8 * j)))] from rfl]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono_syms (tblk1_ok hL hc) fun t₁ ⟨hc₁, hm₁, h11₁, hk₁⟩ hs₁ =>
    WP.mono (tblk2_ok hL hc₁ h11₁ hj) fun t' ⟨hc', hm, h11, hk, hsy⟩ => ?_
  obtain hsy' : t'.syms = t.syms := hsy.trans hs₁
  refine WP.icalls_of_call (a := t.syms n) (by simp only [X86_64.icall, h11, hw]) ?_
    (h t' hc' (hm.trans hm₁) (fun r hr => (hk r hr).trans (hk₁ r hr)) hsy')
  show ts.find? (fun q => t'.syms q.1 == t.syms n) = _
  rw [hsy']; exact hf

/-! ## HMAC's states -/

/-- The key `K`: the first `D` bytes of the frame. -/
abbrev keyOf (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) : List Byte :=
  Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 24) P.H.D

/-- HMAC's states for the block key `k0`, the inner one holding `text`
after `K₀ ⊕ ipad`. -/
structure St (P : RfcHash) {dn : Nat} (L : Lay dn) (g : Reg → BitVec 64) (m₀ : Mem) (k0 text : List Byte)
    (u : State) : Prop where
  ctx : Ctx L g m₀ u
  klen : k0.length = P.H.P.B
  tlen : text.length ≤ 512
  inner : P.ok.SH.Repr u.mem (L.scr + BitVec.ofNat 64 0) (Spec.Hmac.xorPad k0 Spec.Hmac.ipad ++ text)
  outer : P.ok.SH.Repr u.mem (L.scr + BitVec.ofNat 64 192) (Spec.Hmac.xorPad k0 Spec.Hmac.opad)

/-- What HMAC's functions write: their states and working space, and the
stack below the frame. -/
abbrev W {dn : Nat} (L : Lay dn) : List Region := [⟨L.scr, 2256⟩, ⟨L.B, 24⟩]

/-- The writes of a call, within HMAC's working space and the stack below the frame. -/
theorem safe_call {u : State} (hc : Ctx L g m₀ u) {ws : List Region} (hs : ∀ r ∈ ws, Safe L r) {n : Nat}
    (hn : n ≤ 24) : ∀ r ∈ ws ++ [below (u.gpr .rsp) n], Safe L r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact hs r hr
  · simp only [List.mem_singleton] at hr; subst hr
    exact .inr (.inr (.inl ((hc.below_sub hn).trans (Region.sub_prefix (by omega_using [])))))

theorem scr_work {e k : Nat} (h : e + k ≤ 2256) : Region.Sub ⟨L.scr + BitVec.ofNat 64 e, k⟩ ⟨L.scr, 2256⟩ :=
  Offset.sub_base _ h

/-! ## HMAC's `init` -/

/-- The arguments of HMAC's `init`. -/
theorem initArgs_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.initArgs) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧
      t'.gpr .rdi = L.scr + BitVec.ofNat 64 0 ∧ t'.gpr .rsi = L.scr + BitVec.ofNat 64 192 ∧
      t'.gpr .rdx = L.B + BitVec.ofNat 64 24 ∧ t'.gpr .rcx = BitVec.ofNat 64 P.H.D ∧
      t'.gpr .r8 = L.scr + BitVec.ofNat 64 384 := by
  rw [Cfg.initArgs, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (scr_ok hL hc (d := .rdi) (by decide) (a := 0) (by decide)) fun u₁ h₁ => ?_
  refine WP.mono (scr_ok hL h₁.ctx (d := .rsi) (by decide) (a := 192) (by decide)) fun u₂ h₂ => ?_
  refine WP.mono (fr_ok hL h₂.ctx (d := .rdx) (by decide) (o := 0) (by decide)) fun u₃ h₃ => ?_
  refine WP.mono (ldF_ok hL h₃.ctx (d := .rcx) (by decide) (o := fDl) (by simp only [fDl]; have := L.he; omega_using []))
    fun u₄ h₄ => ?_
  refine WP.mono (scr_ok hL h₄.ctx (d := .r8) (by decide) (a := 384) (by decide)) fun u₅ h₅ => ?_
  refine ⟨h₅.ctx, by rw [h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem], ?_, ?_, ?_, ?_, h₅.val⟩
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.keep _ (by decide), h₁.val]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.val]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.val]
  · rw [h₅.keep _ (by decide), h₄.val]; exact h₃.ctx.dl hT

theorem initA (hL : L.Ok) {u : State} (hcu : Ctx L g m₀ u) (hdi : u.gpr .rdi = L.scr + BitVec.ofNat 64 0)
    (hsi : u.gpr .rsi = L.scr + BitVec.ofNat 64 192) (hdx : u.gpr .rdx = L.B + BitVec.ofNat 64 24)
    (hcx : u.gpr .rcx = BitVec.ofNat 64 P.H.D) (h8 : u.gpr .r8 = L.scr + BitVec.ofNat 64 384) :
    Proof.Pbkdf2.Md.X86_64.Pbk.InitArgs (H := P.H) u (L.scr + BitVec.ofNat 64 0)
      (L.scr + BitVec.ofNat 64 192) (L.B + BitVec.ofNat 64 24) (L.scr + BitVec.ofNat 64 384) P.H.D := by
  obtain hsp : below (u.gpr .rsp) 24 = ⟨L.B, 24⟩ := by rw [hcu.rsp, below24]
  have he := L.he
  exact
    { rdi := hdi, rsi := hsi, rdx := hdx, rcx := by rw [hcx, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by nums)
      r8 := h8, klB := by nums
      cr := hcu.covers fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨L.FR, by simp, within_fr _ (by omega_using []) (by nums)⟩
      cw := hcu.coversW fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> exact ⟨L.SCR, by simp, within_off _ (by nums)⟩
      i_o := Offset.disjoint _ (by nums) (by nums) (by nums)
      i_s := Offset.disjoint _ (by nums) (by nums) (by nums)
      o_s := Offset.disjoint _ (by nums) (by nums) (by nums)
      k_i := hL.stk_scr (by nums) (by nums)
      k_o := hL.stk_scr (by nums) (by nums)
      k_s := hL.stk_scr (by nums) (by nums)
      stk_i := by rw [hsp]; exact hL.low_scr (by nums)
      stk_o := by rw [hsp]; exact hL.low_scr (by nums)
      stk_k := by rw [hsp]; exact Offset.base_disjoint _ (by omega_using []) (by nums)
      stk_s := by rw [hsp]; exact hL.low_scr (by nums)
      scnw := by rw [toNat_add_of (by have := hL.nc; omega_using [this])]; have := hL.nc; nums }

theorem xorPad_length (k : List Byte) (p : Byte) : (Spec.Hmac.xorPad k p).length = k.length :=
  List.length_map _

theorem blockKey_length {k : List Byte} (hk : k.length = P.H.D) :
    (Spec.Hmac.blockKey P.ok.SH.H k).length = P.H.P.B := by
  have hB := P.ok.hB
  obtain hDB : P.H.D < P.H.P.B := by nums
  simp only [Spec.Hmac.blockKey, hk, hB, show ¬ P.H.P.B < P.H.D by omega_using [hDB], ite_false, List.length_append,
    List.length_replicate]
  omega_using [hDB]

theorem keyOf_length (m : Mem) : (keyOf P L m).length = P.H.D := by simp [keyOf, Spec.Sha256.bytesAt]

/-- HMAC's `init` with the key `K` in the frame: HMAC's states for its block key. -/
theorem init_step (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).initK t fun u => St P L g m₀ (Spec.Hmac.blockKey P.ok.SH.H (keyOf P L t.mem)) [] u ∧
      Frame (W L) t.mem u.mem := by
  refine WP.seq (WP.mono (initArgs_ok hL hT hc) fun u ⟨hcu, hmu, hdi, hsi, hdx, hcx, h8⟩ => ?_)
  have hok := hcu.tabOk
  have htm := hcu.tabMem
  rw [hT.1, hT.2] at hok
  rw [hT.1] at htm
  refine tcall_ok hL hcu (j := 0) (by decide) htm.1 hok.i fun u' hc' hm' hk' _ => ?_
  obtain hk0 : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8], u'.gpr r = u.gpr r := fun r hr => hk' r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
  obtain a := initA (P := P) hL hc' ((hk0 _ (by simp)).trans hdi) ((hk0 _ (by simp)).trans hsi)
    ((hk0 _ (by simp)).trans hdx) ((hk0 _ (by simp)).trans hcx) ((hk0 _ (by simp)).trans h8)
  obtain hsp : below (u'.gpr .rsp) 24 = ⟨L.B, 24⟩ := by rw [hc'.rsp, below24]
  refine WP.of_syms (Proof.Pbkdf2.Md.X86_64.Pbk.hinit_call P.ok P.hI P.hIsp P.hId a
    fun v hrd hwr hcs hf hi ho hsy => ?_)
  obtain hsafe : ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 0, P.H.S⟩ : Region), ⟨L.scr + BitVec.ofNat 64 192, P.H.S⟩,
      ⟨L.scr + BitVec.ofNat 64 384, 8 * P.H.W⟩], Region.Sub r ⟨L.scr, 2256⟩ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> exact scr_work (by nums)
  obtain hkey : Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 24) P.H.D = keyOf P L t.mem := by
    rw [hm', hmu]
  rw [hkey] at hi ho
  refine ⟨⟨hc'.keep hL hrd hwr (hcs .rsp (by decide)) (fun r hr _ => hcs r hr) hf
    (safe_call hc' (fun r hr => .inr (.inl ((hsafe r hr).trans (Region.sub_prefix (by omega_using []))))) (Nat.le_refl _))
    hsy, blockKey_length (keyOf_length _), by simp, by simpa using hi, ho⟩, ?_⟩
  rw [← hmu, ← hm']
  exact hf.sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨⟨L.scr, 2256⟩, by simp, hsafe r hr⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨L.B, 24⟩, by simp, by rw [hsp]; exact sub_refl _⟩

/-! ## The streaming `update` -/

/-- The arguments of the streaming `update` with `V`. -/
theorem updVArgs_ok (hL : L.Ok) (hT : TabL P L) {u : State} (hc : Ctx L g m₀ u) :
    WP isa (.block Cfg.updVArgs) u fun u' => Ctx L g m₀ u' ∧
      u'.mem = u.mem ∧ u'.gpr .rdi = L.scr + BitVec.ofNat 64 0 ∧ u'.gpr .rsi = BitVec.ofNat 64 P.H.P.B ∧
      u'.gpr .rdx = L.B + BitVec.ofNat 64 88 ∧ u'.gpr .rcx = BitVec.ofNat 64 P.H.D ∧
      u'.gpr .r8 = L.scr + BitVec.ofNat 64 384 := by
  rw [Cfg.updVArgs, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (scr_ok hL hc (d := .rdi) (by decide) (a := 0) (by decide)) fun u₁ h₁ => ?_
  refine WP.mono (ldF_ok hL h₁.ctx (d := .rsi) (by decide) (o := fBl) (by simp only [fBl]; have := L.he; omega_using [this]))
    fun u₂ h₂ => ?_
  refine WP.mono (fr_ok hL h₂.ctx (d := .rdx) (by decide) (o := fV) (by decide)) fun u₃ h₃ => ?_
  refine WP.mono (ldF_ok hL h₃.ctx (d := .rcx) (by decide) (o := fDl) (by simp only [fDl]; have := L.he; omega_using []))
    fun u₄ h₄ => ?_
  refine WP.mono (scr_ok hL h₄.ctx (d := .r8) (by decide) (a := 384) (by decide)) fun u₅ h₅ => ?_
  refine ⟨h₅.ctx, by rw [h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem], ?_, ?_, ?_, ?_, h₅.val⟩
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.keep _ (by decide), h₁.val]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.val, h₁.mem]; exact hc.bl hT
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.val]; rfl
  · rw [h₅.keep _ (by decide), h₄.val]; exact h₃.ctx.dl hT

/-- The arguments of the streaming `update` with the message's `len` bytes. -/
theorem updMArgs_ok (hL : L.Ok) (hT : TabL P L) {u : State} (hc : Ctx L g m₀ u) {len : Nat}
    (hlen : len < 2 ^ 32) :
    WP isa (.block (Cfg.updMArgs len)) u fun u' => Ctx L g m₀ u' ∧
      u'.mem = u.mem ∧ u'.gpr .rdi = L.scr + BitVec.ofNat 64 0 ∧
      u'.gpr .rsi = BitVec.ofNat 64 (P.H.P.B + P.H.D) ∧
      u'.gpr .rdx = L.scr + BitVec.ofNat 64 sMsg ∧ u'.gpr .rcx = BitVec.ofNat 64 len ∧
      u'.gpr .r8 = L.scr + BitVec.ofNat 64 384 := by
  rw [Cfg.updMArgs, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (scr_ok hL hc (d := .rdi) (by decide) (a := 0) (by decide)) fun u₁ h₁ => ?_
  rw [show ([.mov .rsi (.mem (stk fBl)), .alu .add .rsi (.mem (stk fDl))] : List Instr) =
    [.mov .rsi (.mem (stk fBl))] ++ [.alu .add .rsi (.mem (stk fDl))] from rfl, WP.block_append_iff]
  refine WP.mono (ldF_ok hL h₁.ctx (d := .rsi) (by decide) (o := fBl) (by simp only [fBl]; have := L.he; omega_using [this]))
    fun u₂ h₂ => ?_
  refine WP.mono (addF_ok hL h₂.ctx (d := .rsi) (by decide) (o := fDl) (by simp only [fDl]; have := L.he; omega_using []))
    fun u₂' h₂' => ?_
  refine WP.mono (scr_ok hL h₂'.ctx (d := .rdx) (by decide) (a := sMsg) (by decide)) fun u₃ h₃ => ?_
  refine WP.mono (mov32_ok hL h₃.ctx (d := .rcx) (by decide) hlen) fun u₄ h₄ => ?_
  refine WP.mono (scr_ok hL h₄.ctx (d := .r8) (by decide) (a := 384) (by decide)) fun u₅ h₅ => ?_
  refine ⟨h₅.ctx, by rw [h₅.mem, h₄.mem, h₃.mem, h₂'.mem, h₂.mem, h₁.mem], ?_, ?_, ?_, ?_, h₅.val⟩
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), h₂'.keep _ (by decide),
      h₂.keep _ (by decide), h₁.val]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), h₂'.val, h₂.val, h₂.mem, h₁.mem,
      hc.bl hT, hc.dl hT, BitVec.ofNat_add_ofNat]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.val]
  · rw [h₅.keep _ (by decide), h₄.val]

/-- The arguments of the streaming `update`. -/
theorem updA (hL : L.Ok) {w : State} (hcw : Ctx L g m₀ w) {da : Addr} {len : Nat} (hd : DataOk L da len)
    (hlen : len ≤ 256) (hdi : w.gpr .rdi = L.scr + BitVec.ofNat 64 0) (hdx : w.gpr .rdx = da)
    (hcx : w.gpr .rcx = BitVec.ofNat 64 len) (h8 : w.gpr .r8 = L.scr + BitVec.ofNat 64 384) :
    Proof.Pbkdf2.Md.X86_64.Calls.UpdArgs P.ok.stream w (L.scr + BitVec.ofNat 64 0) da
      (L.scr + BitVec.ofNat 64 384) len := by
  obtain hsp : Region.Sub (below (w.gpr .rsp) 16) ⟨L.B, 24⟩ := hcw.below_sub (by omega_using [])
  exact
    { rdi := hdi, rdx := hdx, rcx := by rw [hcx, BitVec.toNat_ofNat]; omega_using [hlen], r8 := h8
      cd := hcw.covers fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hd.within
      cw := hcw.coversW fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact ⟨L.SCR, by simp, within_off _ (by nums)⟩
      st_sc := Offset.disjoint _ (by nums) (by nums) (by nums)
      d_st := hd.work hL (by nums)
      d_sc := hd.work hL (by nums)
      stk_st := (hL.low_scr (by nums)).sub_left hsp
      stk_d := (hd.low hL).sub_left hsp
      stk_sc := (hL.low_scr (by nums)).sub_left hsp }

/-- The table's `update` of the inner state, holding `text`, with the data. -/
theorem upd_call_ok (hL : L.Ok) (hT : TabL P L) {k0 text : List Byte} {u : State} (hu : St P L g m₀ k0 text u)
    {da : Addr} {len : Nat} (hd : DataOk L da len) (hlen : len ≤ 256) (htl : text.length + len ≤ 512)
    (hdi : u.gpr .rdi = L.scr + BitVec.ofNat 64 0) (hsi : u.gpr .rsi = BitVec.ofNat 64 (P.H.P.B + text.length))
    (hdx : u.gpr .rdx = da) (hcx : u.gpr .rcx = BitVec.ofNat 64 len) (h8 : u.gpr .r8 = L.scr + BitVec.ofNat 64 384) :
    WP isa (Cfg.tcall 1 P.f.upd) u fun u' => St P L g m₀ k0 (text ++ Spec.Sha256.bytesAt u.mem da len) u' ∧
      Frame (W L) u.mem u'.mem := by
  have hc := hu.ctx
  have hok := hc.tabOk
  have htm := hc.tabMem
  rw [hT.1, hT.2] at hok
  rw [hT.1] at htm
  refine tcall_ok hL hc (j := 1) (by decide) htm.2.1 hok.u fun w hcw hmw hkw _ => ?_
  obtain hk0 : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8], w.gpr r = u.gpr r := fun r hr => hkw r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
  obtain hsp : Region.Sub (below (w.gpr .rsp) 16) ⟨L.B, 24⟩ := hcw.below_sub (by omega_using [])
  obtain a := updA (P := P) hL hcw hd hlen ((hk0 _ (by simp)).trans hdi) ((hk0 _ (by simp)).trans hdx)
    ((hk0 _ (by simp)).trans hcx) ((hk0 _ (by simp)).trans h8)
  refine WP.of_syms (Proof.Pbkdf2.Md.X86_64.Calls.upd_call P.ok.stream a (by omega_using [hlen]) fun w' af hr hsy => ?_)
  obtain hws : ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 0, P.H.stream.S⟩ : Region),
      ⟨L.scr + BitVec.ofNat 64 384, P.ok.stream.Wb⟩], Region.Sub r ⟨L.scr, 2256⟩ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> exact scr_work (by nums)
  obtain hf' : Frame (W L) w.mem w'.mem := af.frame.sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨⟨L.scr, 2256⟩, by simp, hws r hr⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨L.B, 24⟩, by simp, hsp⟩
  have hkl := hu.klen
  refine ⟨⟨hcw.keep hL af.rd af.wr (af.cs .rsp (by decide)) (fun r hr _ => af.cs r hr) af.frame
      (safe_call hcw (fun r hr => .inr (.inl ((hws r hr).trans (Region.sub_prefix (by omega_using []))))) (by omega_using [])) hsy,
    hkl, by simp [Spec.Sha256.bytesAt]; omega_using [htl], ?_, ?_⟩, hmw ▸ hf'⟩
  · rw [← hmw, ← List.append_assoc]
    exact hr _ (hmw ▸ hu.inner) (by
      rw [(hk0 _ (by simp)).trans hsi, List.length_append, xorPad_length, hkl])
  · refine P.ok.sh_reloc w.mem w'.mem _ _ _ (fun i hi => ?_) (hmw ▸ hu.outer)
    refine Frame.bytes (R := ⟨L.scr + BitVec.ofNat 64 192, P.H.P.N + P.H.P.B⟩) af.frame (fun r hr => ?_)
      (by show P.H.S ≤ 2 ^ 64; nums) hi
    rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by nums) (by nums) (by nums)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ((hL.low_scr (by nums)).sub_left hsp).symm

/-- The inner state, for the key `K₀`, updated with `V`. -/
theorem updV_step (hL : L.Ok) (hT : TabL P L) {k0 : List Byte} {u : State} (hu : St P L g m₀ k0 [] u) :
    WP isa (cfgOf P).updV u fun u' =>
      St P L g m₀ k0 (Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 88) P.H.D) u' ∧
      Frame (W L) u.mem u'.mem := by
  refine WP.seq (WP.mono (updVArgs_ok hL hT hu.ctx) fun w ⟨hcw, hmw, hdi, hsi, hdx, hcx, h8⟩ => ?_)
  obtain hw : St P L g m₀ k0 [] w := ⟨hcw, hu.klen, hu.tlen, hmw ▸ hu.inner, hmw ▸ hu.outer⟩
  refine WP.mono (upd_call_ok hL hT hw (len := P.H.D)
    (.inl ⟨88, rfl, by omega_using [], by nums⟩) (by nums) (by simp; nums) hdi (by simpa using hsi) hdx hcx h8)
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
    fun w ⟨hcw, hmw, hdi, hsi, hdx, hcx, h8⟩ => ?_)
  obtain hw : St P L g m₀ k0 text w := ⟨hcw, hu.klen, hu.tlen, hmw ▸ hu.inner, hmw ▸ hu.outer⟩
  refine WP.mono (upd_call_ok hL hT hw (len := len) (.inr ⟨sMsg, rfl, by decide, by simp only [sMsg]; omega_using [hlen]⟩)
    hlen (by rw [ht]; nums) hdi (by rw [hsi, ht]) hdx hcx h8) fun u' ⟨hs, hf⟩ => ?_
  rw [hmw] at hs
  exact ⟨hs, hmw ▸ hf⟩

/-! ## HMAC's `finalize` -/

theorem finArgs_ok (hL : L.Ok) (hT : TabL P L) {u : State} (hc : Ctx L g m₀ u) {len dst : Nat}
    (hlen : len < 2 ^ 31) (hdst : dst < 2 ^ 31) :
    WP isa (.block (Cfg.finArgs len dst)) u
      fun u' => Ctx L g m₀ u' ∧ u'.mem = u.mem ∧ u'.gpr .rdi = L.scr + BitVec.ofNat 64 0 ∧
        u'.gpr .rsi = L.scr + BitVec.ofNat 64 192 ∧ u'.gpr .rdx = BitVec.ofNat 64 (P.H.P.B + P.H.D + len) ∧
        u'.gpr .rcx = L.B + BitVec.ofNat 64 (24 + dst) ∧ u'.gpr .r8 = L.scr + BitVec.ofNat 64 384 := by
  rw [Cfg.finArgs, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (scr_ok hL hc (d := .rdi) (by decide) (a := 0) (by decide)) fun u₁ h₁ => ?_
  refine WP.mono (scr_ok hL h₁.ctx (d := .rsi) (by decide) (a := 192) (by decide)) fun u₂ h₂ => ?_
  rw [show ([.mov .rdx (.mem (stk fBl)), .alu .add .rdx (.mem (stk fDl)),
      .alu .add .rdx (.imm (BitVec.ofNat 32 len))] : List Instr) =
    [.mov .rdx (.mem (stk fBl))] ++ [.alu .add .rdx (.mem (stk fDl))] ++
      [.alu .add .rdx (.imm (BitVec.ofNat 32 len))] from rfl, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ldF_ok hL h₂.ctx (d := .rdx) (by decide) (o := fBl) (by simp only [fBl]; have := L.he; omega_using [this]))
    fun u₃ h₃ => ?_
  refine WP.mono (addF_ok hL h₃.ctx (d := .rdx) (by decide) (o := fDl) (by simp only [fDl]; have := L.he; omega_using []))
    fun u₃' h₃' => ?_
  refine WP.mono (addI_ok hL h₃'.ctx (d := .rdx) (by decide) hlen) fun u₃'' h₃'' => ?_
  refine WP.mono (fr_ok hL h₃''.ctx (d := .rcx) (by decide) hdst) fun u₄ h₄ => ?_
  refine WP.mono (scr_ok hL h₄.ctx (d := .r8) (by decide) (a := 384) (by decide)) fun u₅ h₅ => ?_
  obtain hm2 : u₂.mem = u.mem := by rw [h₂.mem, h₁.mem]
  refine ⟨h₅.ctx, by rw [h₅.mem, h₄.mem, h₃''.mem, h₃'.mem, h₃.mem, hm2], ?_, ?_, ?_, ?_, h₅.val⟩
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃''.keep _ (by decide), h₃'.keep _ (by decide),
      h₃.keep _ (by decide), h₂.keep _ (by decide), h₁.val]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃''.keep _ (by decide), h₃'.keep _ (by decide),
      h₃.keep _ (by decide), h₂.val]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃''.val, h₃'.val, h₃.val, h₃.mem, hm2, hc.bl hT,
      hc.dl hT, BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat]
  · rw [h₅.keep _ (by decide), h₄.val]

/-- The arguments of HMAC's `finalize`. -/
theorem finA (hL : L.Ok) {w : State} (hcw : Ctx L g m₀ w) {cnt : Nat} {dst : Nat} (hdst : dst + P.H.D ≤ 184)
    (hdi : w.gpr .rdi = L.scr + BitVec.ofNat 64 0) (hsi : w.gpr .rsi = L.scr + BitVec.ofNat 64 192)
    (hdx : w.gpr .rdx = BitVec.ofNat 64 cnt) (hcx : w.gpr .rcx = L.B + BitVec.ofNat 64 (24 + dst))
    (h8 : w.gpr .r8 = L.scr + BitVec.ofNat 64 384) :
    Proof.Pbkdf2.Md.X86_64.Pbk.FinArgs (H := P.H) w (L.scr + BitVec.ofNat 64 0)
      (L.scr + BitVec.ofNat 64 192) (BitVec.ofNat 64 cnt) (L.B + BitVec.ofNat 64 (24 + dst))
      (L.scr + BitVec.ofNat 64 384) := by
  obtain hsp : below (w.gpr .rsp) 24 = ⟨L.B, 24⟩ := by rw [hcw.rsp, below24]
  have he := L.he
  exact
    { rdi := hdi, rsi := hsi, rdx := hdx, rcx := hcx, r8 := h8
      cr := hcw.covers fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨L.SCR, by simp, within_off _ (by nums)⟩
      cw := hcw.coversW fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨L.SCR, by simp, within_off _ (by nums)⟩
        · exact ⟨L.FR, by simp, within_fr _ (by omega_using []) (by nums)⟩
        · exact ⟨L.SCR, by simp, within_off _ (by nums)⟩
      i_u := Offset.disjoint _ (by nums) (by nums) (by nums)
      i_o := (hL.stk_scr (d := 24 + dst) (by nums) (by nums)).symm
      i_s := Offset.disjoint _ (by nums) (by nums) (by nums)
      u_o := (hL.stk_scr (d := 24 + dst) (by nums) (by nums)).symm
      u_s := Offset.disjoint _ (by nums) (by nums) (by nums)
      o_s := hL.stk_scr (by nums) (by nums)
      stk_i := by rw [hsp]; exact hL.low_scr (by nums)
      stk_u := by rw [hsp]; exact hL.low_scr (by nums)
      stk_o := by rw [hsp]; exact Offset.base_disjoint _ (by omega_using []) (by nums)
      stk_s := by rw [hsp]; exact hL.low_scr (by nums)
      scnw := by rw [toNat_add_of (by have := hL.nc; omega_using [this])]; have := hL.nc; nums }

/-- HMAC's `finalize`, for the key `K₀` and the text `text`, of `D + len`
bytes: the MAC in the frame at `dst`. -/
theorem fin_step (hL : L.Ok) (hT : TabL P L) {k0 text : List Byte} {u : State} (hu : St P L g m₀ k0 text u)
    {len dst : Nat} (ht : text.length = P.H.D + len) (hlen : len < 2 ^ 31) (hdst : dst + P.H.D ≤ 184) :
    WP isa ((cfgOf P).fin len dst) u fun u' => Ctx L g m₀ u' ∧
      Frame (W L ++ [⟨L.B + BitVec.ofNat 64 (24 + dst), P.H.D⟩]) u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (24 + dst)) P.H.D =
        Spec.Hmac.hmacBlockKey P.ok.SH.H k0 text := by
  refine WP.seq (WP.mono (finArgs_ok hL hT hu.ctx (len := len) (dst := dst) hlen (by omega_using [hdst]))
    fun w ⟨hcw, hmw, hdi, hsi, hdx, hcx, h8⟩ => ?_)
  have hok := hcw.tabOk
  have htm := hcw.tabMem
  rw [hT.1, hT.2] at hok
  rw [hT.1] at htm
  refine tcall_ok hL hcw (j := 2) (by decide) htm.2.2 hok.f fun w₁ hc₁ hm₁ hk₁ _ => ?_
  obtain hk0 : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8], w₁.gpr r = w.gpr r := fun r hr => hk₁ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
  obtain hsp : below (w₁.gpr .rsp) 24 = ⟨L.B, 24⟩ := by rw [hc₁.rsp, below24]
  obtain a := finA (P := P) hL hc₁ (cnt := P.H.P.B + P.H.D + len) hdst ((hk0 _ (by simp)).trans hdi)
    ((hk0 _ (by simp)).trans hsi) ((hk0 _ (by simp)).trans hdx) ((hk0 _ (by simp)).trans hcx)
    ((hk0 _ (by simp)).trans h8)
  refine WP.of_syms (Proof.Pbkdf2.Md.X86_64.Pbk.hfin_call P.ok P.hF P.hFsp P.hFd a
    fun w' hrd hwr hcs hf hpost hsy => ?_)
  obtain hws : ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 0, P.H.S⟩ : Region),
      ⟨L.B + BitVec.ofNat 64 (24 + dst), P.H.D⟩, ⟨L.scr + BitVec.ofNat 64 384, 8 * P.H.W⟩] ++
      [below (w₁.gpr .rsp) 24], ∃ r' ∈ W L ++ [⟨L.B + BitVec.ofNat 64 (24 + dst), P.H.D⟩], Region.Sub r r' := by
    simp only [W, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, hsp]
    rintro r (rfl | rfl | rfl | rfl)
    · exact ⟨⟨L.scr, 2256⟩, by simp, scr_work (by nums)⟩
    · exact ⟨⟨L.B + BitVec.ofNat 64 (24 + dst), P.H.D⟩, by simp, sub_refl _⟩
    · exact ⟨⟨L.scr, 2256⟩, by simp, scr_work (by nums)⟩
    · exact ⟨⟨L.B, 24⟩, by simp, sub_refl _⟩
  obtain hm : w₁.mem = u.mem := hm₁.trans hmw
  refine ⟨hc₁.keep hL hrd hwr (hcs .rsp (by decide)) (fun r hr _ => hcs r hr) hf (hsy := hsy) fun r hr => ?_,
    hm ▸ hf.sub hws, ?_⟩
  · obtain ⟨r', hr', hs⟩ := hws r hr
    simp only [W, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · exact .inr (.inl (hs.trans (Region.sub_prefix (by omega_using []))))
    · exact .inr (.inr (.inl (hs.trans (Region.sub_prefix (by omega_using [])))))
    · exact (safe_low L (by nums)).of_sub hs
  · have hk := hu.klen
    exact hpost _ _ hk (by rw [hk]; have := hu.tlen; nums) (hm ▸ hu.inner)
      (by rw [ht]; congr 1; omega_using []) (hm ▸ hu.outer)

end VG.Proof.Ecdsa.Rfc6979.X86_64

end

end

/-! ### `Ecdsa.Rfc6979.X86_64.Msg`, which only this module used -/

section

/-!
# Deterministic ECDSA on x86-64: the messages of steps d, f and h.3

The byte `b`, and `‖ d ‖ h` if `full`, at `scratch + 2256` (`msg_ok`): the
byte (`byte_ok`), then the private key and `h` copied (`tail_ok`). HMAC's
text is `V` (`D` bytes, from the frame, the table's `update` with it), then
this message.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64

variable {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {m₀ : Mem}

/-- `8 K` bytes copied to `scratch + d` by `copyN`, with `Ctx` kept. -/
theorem copy_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {src : Reg} {S : Addr} (hs : u.gpr src = S)
    (hsr : src ≠ .rax) (hdi : u.gpr .rdi = L.scr) {so d K : Nat} (hd : d + 8 * K ≤ 8192)
    (hr : ∀ j < K, InRegions (u.rd ++ u.wr) (S + BitVec.ofNat 64 (so + 8 * j)) 8)
    (hsep : Region.Disjoint ⟨S + BitVec.ofNat 64 so, 8 * K⟩ ⟨L.scr + BitVec.ofNat 64 d, 8 * K⟩) :
    WP isa (.block (Cfg.copyN K src so .rdi d)) u fun u' => Ctx L g m₀ u' ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧
      (∀ r, r ≠ .rax → u'.gpr r = u.gpr r) ∧ Frame [⟨L.scr + BitVec.ofNat 64 d, 8 * K⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.scr + BitVec.ofNat 64 d) (8 * K) =
        Spec.Sha256.bytesAt u.mem (S + BitVec.ofNat 64 so) (8 * K) :=
  WP.mono_syms (copyN_ok (K := K) (by decide) hsr hsep (by have := hL.nc; omega_using [hd]) K (Nat.le_refl _) u hs hdi hr
    fun j hj => hc.inScrW (by omega_using [hd, hj])) fun u' ⟨hrd, hwr, hg, hf, hb⟩ hsy =>
    ⟨hc.keep hL hrd hwr (hg _ (by decide)) (fun r hr _ => hg r (ne_cs hr (by decide))) hf
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L hd) hsy,
      hrd, hwr, hg, hf, hb⟩

theorem fr_add (B : Addr) (o : Nat) : B + BitVec.ofNat 64 24 + BitVec.ofNat 64 o = B + BitVec.ofNat 64 (24 + o) :=
  Offset.add_add _ _ _

/-- The pointers: `scratch` in `rdi` and `d` in `rsi`. -/
theorem ptrs_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.msgPtrs) t fun u => Ctx L g m₀ u ∧ u.mem = t.mem ∧ u.gpr .rdi = L.scr ∧
      u.gpr .rsi = L.d := by
  obtain h208 := hc.inFr (d := 208) (by omega_using []) (by omega_using [])
  obtain h224 := hc.inFr (d := 224) (by omega_using []) (by omega_using [])
  apply WP.of_runBlock
  simp only [Cfg.msgPtrs, fScratch, fD, runBlock_cons,
    runStep_some, runBlock_nil, exec, readSrc, State.load64, ea_stk, hc.rsp, Offset.add_add, Nat.reduceAdd, h208,
    h224, ite_true, Option.map_some, hc.pScr, hc.pD, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.mem_setReg, reduceCtorEq, ite_false, Option.some.injEq, exists_eq_left']
  exact ⟨hc.regs hL rfl rfl rfl rfl (by cs_tac), by triv, by triv, by triv⟩

/-- `Q` bytes copied to `scratch + d` by `copyBytes`, with `Ctx` kept. -/
theorem copyB_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {src : Reg} {S : Addr} (hs : u.gpr src = S)
    (hsr : src ≠ .rax) (hdi : u.gpr .rdi = L.scr) {so d Q : Nat} (h8 : 8 ≤ Q) (hd : d + Q ≤ 8192)
    (hso : so + Q < 2 ^ 64)
    (hr : ∀ j, j + 8 ≤ Q → InRegions (u.rd ++ u.wr) (S + BitVec.ofNat 64 (so + j)) 8)
    (hsep : Region.Disjoint ⟨S + BitVec.ofNat 64 so, Q⟩ ⟨L.scr + BitVec.ofNat 64 d, Q⟩) :
    WP isa (.block (Cfg.copyBytes Q src so .rdi d)) u fun u' => Ctx L g m₀ u' ∧
      (∀ r, r ≠ .rax → u'.gpr r = u.gpr r) ∧ Frame [⟨L.scr + BitVec.ofNat 64 d, Q⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.scr + BitVec.ofNat 64 d) Q =
        Spec.Sha256.bytesAt u.mem (S + BitVec.ofNat 64 so) Q :=
  WP.mono_syms (copyBytes_ok (by decide) hsr hsep h8 hso (by omega_using [hd]) hs hdi hr fun j hj => hc.inScrW (by omega_using [hd, hj]))
    fun u' ⟨hrd, hwr, hg, hf, hb⟩ hsy =>
    ⟨hc.keep hL hrd hwr (hg _ (by decide)) (fun r hr _ => hg r (ne_cs hr (by decide))) hf
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L hd) hsy, hg, hf, hb⟩

/-- The byte `b` at `scratch + 2256`, with `scratch` in `rdi`. -/
theorem byte_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (hdi : t.gpr .rdi = L.scr) (b : Nat) :
    WP isa (.block ([.mov32 .rax (.imm (BitVec.ofNat 32 b)), .store8 (at_ .rdi sMsg) .rax] : List Instr)) t
      fun u => Ctx L g m₀ u ∧ (∀ r, r ≠ .rax → u.gpr r = t.gpr r) ∧
        Frame [⟨L.scr + BitVec.ofNat 64 2256, 1⟩] t.mem u.mem ∧
        Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 2256) 1 = [BitVec.ofNat 8 b] := by
  obtain w := hc.inScrW (o := 2256) (n := 1) (by decide)
  apply WP.of_runBlock
  simp only [sMsg, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32, State.store8, ea_at,
    RegUpd.gpr_setReg, reduceCtorEq, ite_false, RegUpd.mem_setReg, hdi,
    RegUpd.wr_setReg, w, ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  obtain hb8 : ((BitVec.ofNat 32 b).setWidth 64).setWidth 8 = BitVec.ofNat 8 b := by
    apply BitVec.eq_of_toNat_eq; simp
  rw [hb8]
  obtain hf₃ : Frame [⟨L.scr + BitVec.ofNat 64 2256, 1⟩] t.mem
      (t.mem.writeW (L.scr + BitVec.ofNat 64 2256) (BitVec.ofNat 8 b)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hc.keep hL rfl rfl (by trivial)
      (fun r hr hr' => by first | trivial | rfl | exact RegUpd.gpr_setReg_of_ne _ _ (ne_cs hr (by decide))) hf₃
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L (by decide)) rfl,
    fun r hr => ?_, hf₃, ?_⟩
  · simp only [hr, ite_false]
  · show [(t.mem.writeW (L.scr + BitVec.ofNat 64 2256) (BitVec.ofNat 8 b))
      (L.scr + BitVec.ofNat 64 2256 + BitVec.ofNat 64 0)] = _
    rw [add_ofNat_zero, WriteBytes.writeW8_apply]; simp

/-- `d ‖ h`, `Q` bytes each, at `scratch + a`, with `scratch` in `rdi` and
`d` in `rsi`, `h` at `ho` in the frame. -/
theorem tail_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (hdi : u.gpr .rdi = L.scr) (hsi : u.gpr .rsi = L.d)
    {a Q ho : Nat} (ha : a + 2 * Q ≤ 8192) (h8 : 8 ≤ Q) (hQ : Q ≤ 66) (hho : 24 + ho + Q ≤ 240 + 8 * L.e)
    (hq : Q ≤ L.q) :
    WP isa (.block (Cfg.copyBytes Q .rsi 0 .rdi a ++ Cfg.copyBytes Q .rsp ho .rdi (a + Q))) u
      fun u' => Ctx L g m₀ u' ∧ Frame [⟨L.scr + BitVec.ofNat 64 a, 2 * Q⟩] u.mem u'.mem ∧
        Spec.Sha256.bytesAt u'.mem (L.scr + BitVec.ofNat 64 a) (2 * Q) =
          Spec.Sha256.bytesAt u.mem L.d Q ++
            Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (24 + ho)) Q := by
  rw [WP.block_append_iff]
  refine WP.mono (copyB_ok hL hc (src := .rsi) hsi (by decide) hdi (so := 0) (d := a) h8 (by omega_using [ha])
    (by omega_using [hQ]) (fun j hj => by rw [Nat.zero_add]; exact hc.inD (by omega_using [hq, hj]) (by omega_using [hQ, hj]))
    (by rw [add_ofNat_zero]
        exact (hL.dc.sub_left (Region.sub_prefix hq)).sub_right (Offset.sub_base _ (by omega_using [ha]))))
    fun u₂ ⟨hc₂, hg₂, hf₂, hb₂⟩ => ?_
  obtain hdi₂ : u₂.gpr .rdi = L.scr := (hg₂ _ (by decide)).trans hdi
  refine WP.mono (copyB_ok hL hc₂ (S := L.B + BitVec.ofNat 64 24) (src := .rsp) hc₂.rsp (by decide) hdi₂
    (so := ho) (d := a + Q) h8 (by omega_using [ha]) (by have := L.he; omega_using [hho, this])
    (fun j hj => by rw [fr_add]; exact hc₂.inFr (by omega_using []) (by omega_using [hho, hj]))
    (by rw [fr_add]; exact hL.stk_scr (by omega_using [hho]) (by omega_using [ha]))) fun u₃ ⟨hc₃, _, hf₃, hb₃⟩ => ?_
  refine ⟨hc₃, ?_, ?_⟩
  · refine (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      (hf₃.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by omega_using []) (by omega_using [])
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by omega_using []) (by omega_using [])
  · rw [show 2 * Q = Q + Q by omega_using [], Proof.Hmac.Common.bytesAt_add _ _ Q Q, Offset.add_add,
      hb₃, fr_add,
      bytesAt_frame hf₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega_using []) (by omega_using [ha]) (by omega_using [ha])) (by omega_using [hQ]),
      hb₂, add_ofNat_zero]
    refine congrArg (fun y => Spec.Sha256.bytesAt u.mem L.d Q ++ y) ?_
    exact bytesAt_frame hf₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hL.stk_scr (by omega_using [hho]) (by omega_using [ha])) (by omega_using [hQ])

variable {P : RfcHash}

/-- `h` in the frame. -/
abbrev hOf (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) : List Byte :=
  Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 (24 + (cfgOf P).fHo)) P.Q

/-- The length of the message. -/
abbrev mlen (P : RfcHash) (full : Bool) : Nat := if full then 1 + 2 * P.Q else 1

/-- The message `b` (`‖ d ‖ h` if `full`, `Q` bytes each) at `scratch + 2256`. -/
theorem msg_ok (hL : L.Ok) (hq : L.q = P.Q) {t : State} (hc : Ctx L g m₀ t) (hdi : t.gpr .rdi = L.scr)
    (hsi : t.gpr .rsi = L.d) (b : Nat) (full : Bool) :
    WP isa (.block ((cfgOf P).msg b full)) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2256, 1 + 2 * P.Q⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.scr + BitVec.ofNat 64 2256) (mlen P full) =
        [BitVec.ofNat 8 b] ++ (if full then Spec.Sha256.bytesAt t.mem L.d P.Q ++ hOf P L t.mem else []) := by
  have hQ := P.sizes
  have hlen : (cfgOf P).len = P.Q := rfl
  obtain hho : 24 + (cfgOf P).fHo + P.Q ≤ 240 + 8 * L.e := by
    have := L.he
    simp only [Cfg.fHo, cfgOf]
    rcases Bool.eq_false_or_eq_true P.R.big with h | h <;>
      simp only [h, fX, fH, ite_true, ite_false, Bool.false_eq_true] <;> nums
  cases full
  · simp only [Cfg.msg, Bool.false_eq_true, ite_false, List.append_nil, mlen]
    refine WP.mono (byte_ok hL hc hdi b) fun u ⟨hcu, _, hf, hb⟩ =>
      ⟨hcu, hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩, hb⟩
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.sub _ (by omega_using []) (by omega_using [])
  · simp only [Cfg.msg, ite_true, sMsg, mlen]
    rw [WP.block_append_iff]
    refine WP.mono (byte_ok hL hc hdi b) fun u ⟨hcu, hg, hf, hb⟩ => ?_
    obtain hdi' : u.gpr .rdi = L.scr := (hg _ (by decide)).trans hdi
    obtain hsi' : u.gpr .rsi = L.d := (hg _ (by decide)).trans hsi
    refine WP.mono (tail_ok hL hcu hdi' hsi' (a := 2256 + 1) (Q := (cfgOf P).len) (ho := (cfgOf P).fHo)
      (by show _ + 2 * P.Q ≤ _; nums) (by show 8 ≤ P.Q; nums) (by show P.Q ≤ 66; nums) hho (by rw [hq]; rfl))
      fun u' ⟨hcu', hf', hb'⟩ => ⟨hcu', ?_, ?_⟩
    · refine (hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
        (hf'.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
      · simp only [List.mem_singleton] at hr; subst hr
        exact Offset.sub _ (by omega_using []) (by omega_using [])
      · simp only [List.mem_singleton] at hr; subst hr
        exact Offset.sub _ (by omega_using []) (by omega_using [hlen])
    · rw [Proof.Hmac.Common.bytesAt_add _ _ 1 (2 * P.Q), Offset.add_add]
      have hb'' : Spec.Sha256.bytesAt u'.mem (L.scr + BitVec.ofNat 64 (2256 + 1)) (2 * P.Q) =
          Spec.Sha256.bytesAt u.mem L.d P.Q ++ hOf P L u.mem := hb'
      rw [hb'', bytesAt_frame hf' (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega_using []) (by omega_using []) (by nums)) (by omega_using []), hb]
      refine congrArg ([BitVec.ofNat 8 b] ++ ·) ?_
      obtain hdq : Spec.Sha256.bytesAt u.mem L.d P.Q = Spec.Sha256.bytesAt t.mem L.d P.Q :=
        bytesAt_frame hf (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hL.dc.sub_left (Region.sub_prefix (by rw [hq]))).sub_right (Offset.sub_base _ (by omega_using [])))
          (by nums)
      rw [hdq]
      refine congrArg (Spec.Sha256.bytesAt t.mem L.d P.Q ++ ·) ?_
      exact bytesAt_frame hf (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hL.stk_scr (by omega_using [hho]) (by omega_using [])) (by nums)

end VG.Proof.Ecdsa.Rfc6979.X86_64

end

end


/-!
# Deterministic ECDSA on x86-64: the steps on `K` and `V`

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
(`HashOK.sh_reloc`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {m₀ : Mem}

/-- `scratch` in `rdi`. -/
theorem scrPtr_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.scrPtr) t fun u => Ctx L g m₀ u ∧ u.mem = t.mem ∧ u.gpr .rdi = L.scr ∧
      ∀ r, r ≠ .rdi → u.gpr r = t.gpr r :=
  WP.mono (ldF_ok hL hc (d := .rdi) (by decide) (o := fScratch) (by simp only [fScratch]; have := L.he; omega_using []))
    fun u h => ⟨h.ctx, h.mem, h.val.trans hc.pScr, h.keep⟩

/-- A copy at `scratch + 3072` of HMAC's inner and outer states for the block key `k0`. -/
def SavedB (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) (k0 : List Byte) : Prop :=
  P.ok.SH.Repr m (L.scr + BitVec.ofNat 64 3072) (Spec.Hmac.xorPad k0 Spec.Hmac.ipad) ∧
    P.ok.SH.Repr m (L.scr + BitVec.ofNat 64 3264) (Spec.Hmac.xorPad k0 Spec.Hmac.opad)

/-- The copy's region. -/
abbrev SaveR {dn : Nat} (L : Lay dn) : Region := ⟨L.scr + BitVec.ofNat 64 3072, 384⟩

theorem state_le (P : RfcHash) : P.H.P.N + P.H.P.B ≤ 192 := by
  have := P.ok.B_le; have := P.ok.N_le; omega_arith

/-- The bytes of `n` at `p` in `m'` are those at `q` in `m`, one by one. -/
theorem byte_of_bytesAt {m m' : Mem} {p q : Addr} {n : Nat}
    (h : Spec.Sha256.bytesAt m' p n = Spec.Sha256.bytesAt m q n) {i : Nat} (hi : i < n) :
    m' (p + BitVec.ofNat 64 i) = m (q + BitVec.ofNat 64 i) := by
  have := congrArg (·[i]?) h
  simpa [Spec.Sha256.bytesAt, hi] using this

/-- The copy survives memory that changed apart from it. -/
theorem SavedB.frame {m m' : Mem} {k0 : List Byte} (hS : SavedB P L m k0) {ws : List Region}
    (hf : Frame ws m m') (hd : ∀ r ∈ ws, Region.Disjoint (SaveR L) r) : SavedB P L m' k0 := by
  obtain hle := state_le P
  refine ⟨P.ok.sh_reloc _ _ _ _ _ (fun i hi => Frame.bytes (R := ⟨L.scr + BitVec.ofNat 64 3072, 192⟩) hf
      (fun r hr => (hd r hr).sub_left (Offset.sub _ (by omega_using []) (by omega_using []))) (by decide : (192 : Nat) ≤ 2 ^ 64)
      (show i < 192 by omega_using [hle, hi])) hS.1,
    P.ok.sh_reloc _ _ _ _ _ (fun i hi => Frame.bytes (R := ⟨L.scr + BitVec.ofNat 64 3264, 192⟩) hf
      (fun r hr => (hd r hr).sub_left (Offset.sub _ (by omega_using []) (by omega_using []))) (by decide : (192 : Nat) ≤ 2 ^ 64)
      (show i < 192 by omega_using [hle, hi])) hS.2⟩

/-- What HMAC's functions write is apart from the copy. -/
theorem W_save (hL : L.Ok) : ∀ r ∈ W L, Region.Disjoint (SaveR L) r := by
  intro r hr
  simp only [W, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (Offset.disjoint_base _ (by decide) (by decide))
  · exact ((hL.kc.sub_left (Region.sub_prefix (by omega_using []))).sub_right (Offset.sub_base _ (by decide))).symm

/-- After `init`: the states copied to `scratch + 3072`, and `St` kept. -/
theorem save_ok (hL : L.Ok) {k0 : List Byte} {u : State} (hu : St P L g m₀ k0 [] u) :
    WP isa (.block Cfg.save) u fun u' => St P L g m₀ k0 [] u' ∧ SavedB P L u'.mem k0 ∧
      Frame [SaveR L] u.mem u'.mem := by
  obtain hle := state_le P
  rw [Cfg.save, WP.block_append_iff]
  refine WP.mono (scrPtr_ok hL hu.ctx) fun u₁ ⟨hc₁, hm₁, hd₁, _⟩ => ?_
  rw [show Cfg.copyStates true = Cfg.copyN 48 .rdi sInner .rdi sSave from rfl]
  refine WP.mono (copy_ok hL hc₁ (src := .rdi) (S := L.scr) hd₁ (by decide) hd₁ (so := 0) (d := 3072) (K := 48)
    (by decide) (fun j hj => hc₁.inScr (by omega_using [hj])) (Offset.disjoint _ (by decide) (by decide) (by decide)))
    fun u' ⟨hc', _, _, _, hf', hb'⟩ => ?_
  rw [hm₁] at hf' hb'
  obtain hst : ∀ o, o + 192 ≤ 384 → ∀ i < P.H.P.N + P.H.P.B,
      u'.mem (L.scr + BitVec.ofNat 64 o + BitVec.ofNat 64 i) = u.mem (L.scr + BitVec.ofNat 64 o + BitVec.ofNat 64 i) :=
    fun o ho i hi => Frame.bytes (R := ⟨L.scr + BitVec.ofNat 64 o, 192⟩) hf'
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega_using [ho]) (by omega_using [ho]) (by omega_using [])) (by decide : (192 : Nat) ≤ 2 ^ 64)
      (show i < 192 by omega_using [hle, hi])
  have hin := hu.inner
  rw [List.append_nil] at hin
  refine ⟨⟨hc', hu.klen, hu.tlen, ?_, ?_⟩, ⟨?_, ?_⟩, hf'⟩
  · rw [List.append_nil]; exact P.ok.sh_reloc _ _ _ _ _ (fun i hi => hst 0 (by decide) i hi) hin
  · exact P.ok.sh_reloc _ _ _ _ _ (fun i hi => hst 192 (by decide) i hi) hu.outer
  · exact P.ok.sh_reloc _ _ _ _ _ (fun i hi => byte_of_bytesAt hb' (by omega_using [hle, hi])) hin
  · exact P.ok.sh_reloc _ _ _ _ _ (fun i hi => by
      obtain h := byte_of_bytesAt hb' (i := 192 + i) (by omega_using [hle, hi])
      obtain e1 : L.scr + BitVec.ofNat 64 3264 + BitVec.ofNat 64 i =
          L.scr + BitVec.ofNat 64 3072 + BitVec.ofNat 64 (192 + i) := by
        rw [Offset.add_add, Offset.add_add]; congr 2; omega_using []
      obtain e2 : L.scr + BitVec.ofNat 64 192 + BitVec.ofNat 64 i =
          L.scr + BitVec.ofNat 64 0 + BitVec.ofNat 64 (192 + i) := by
        rw [Offset.add_add, Offset.add_add, Nat.zero_add]
      rw [e1, e2]; exact h) hu.outer

/-- The copy back: HMAC's states for the block key `k0`, and the copy kept. -/
theorem restore_ok (hL : L.Ok) {k0 : List Byte} {t : State} (hc : Ctx L g m₀ t) (hS : SavedB P L t.mem k0)
    (hk : k0.length = P.H.P.B) :
    WP isa (.block Cfg.restore) t fun u => St P L g m₀ k0 [] u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 0, 8 * 48⟩] t.mem u.mem ∧ SavedB P L u.mem k0 := by
  obtain hle := state_le P
  rw [Cfg.restore, WP.block_append_iff]
  refine WP.mono (scrPtr_ok hL hc) fun u₁ ⟨hc₁, hm₁, hd₁, _⟩ => ?_
  rw [show Cfg.copyStates false = Cfg.copyN 48 .rdi sSave .rdi sInner from rfl]
  refine WP.mono (copy_ok hL hc₁ (src := .rdi) (S := L.scr) hd₁ (by decide) hd₁ (so := 3072) (d := 0) (K := 48)
    (by decide) (fun j hj => hc₁.inScr (by omega_using [hj])) (Offset.disjoint _ (by decide) (by decide) (by decide)))
    fun u ⟨hcu, _, _, _, hf, hb⟩ => ?_
  rw [hm₁] at hf hb
  refine ⟨⟨hcu, hk, by simp, ?_, ?_⟩, hf, hS.frame hf fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (by decide) (by decide) (by decide)⟩
  · rw [List.append_nil]; exact P.ok.sh_reloc _ _ _ _ _ (fun i hi => byte_of_bytesAt hb (by omega_using [hle, hi])) hS.1
  · exact P.ok.sh_reloc _ _ _ _ _ (fun i hi => by
      obtain h := byte_of_bytesAt hb (i := 192 + i) (by omega_using [hle, hi])
      obtain e1 : L.scr + BitVec.ofNat 64 192 + BitVec.ofNat 64 i =
          L.scr + BitVec.ofNat 64 0 + BitVec.ofNat 64 (192 + i) := by
        rw [Offset.add_add, Offset.add_add, Nat.zero_add]
      obtain e2 : L.scr + BitVec.ofNat 64 3264 + BitVec.ofNat 64 i =
          L.scr + BitVec.ofNat 64 3072 + BitVec.ofNat 64 (192 + i) := by
        rw [Offset.add_add, Offset.add_add]; congr 2; omega_using []
      rw [e1, e2]; exact h) hS.2

/-- `K` and `V` (of the hash function's output length), in the frame. -/
abbrev kOf (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) : List Byte := keyOf P L m
abbrev vOf (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) : List Byte :=
  Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 88) P.H.D

/-- A copy of HMAC's states for the key `K`. -/
abbrev SavedK (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) (K : List Byte) : Prop :=
  SavedB P L m (Spec.Hmac.blockKey P.ok.SH.H K)

theorem hash_length (P : RfcHash) (m : List Byte) : (P.ok.SH.H.hash m).length = P.H.D := by
  have := P.ok.hDN
  simp only [P.ok.hash, List.length_take, Proof.MdStream.Md.hash, P.ok.md.digest_length]
  omega_using [this]

/-- HMAC with a key is HMAC with its block key. -/
theorem mac_eq (P : RfcHash) (K t : List Byte) :
    P.mac K t = Spec.Hmac.hmacBlockKey P.ok.SH.H (Spec.Hmac.blockKey P.ok.SH.H K) t := rfl

/-- HMAC's output is the hash function's. -/
theorem mac_length (P : RfcHash) (K t : List Byte) : (P.mac K t).length = P.H.D := hash_length P _

/-- What the steps change: `scratch`, the stack below the frame, `K` and `V`. -/
abbrev KVW {dn : Nat} (L : Lay dn) : List Region := [L.SCR, ⟨L.B, 152⟩]

theorem kvw_of {rs : List Region} (h : ∀ r ∈ rs, Region.Sub r L.SCR ∨ Region.Sub r ⟨L.B, 152⟩) :
    ∀ r ∈ rs, ∃ r' ∈ KVW L, Region.Sub r r' := fun r hr => by
  rcases h r hr with h | h
  · exact ⟨_, by simp, h⟩
  · exact ⟨⟨L.B, 152⟩, by simp, h⟩

/-- HMAC's writes, and the MAC's place `dst` (`K` or `V`), within `KVW`. -/
theorem wd_kvw {dst : Nat} (h : dst + P.H.D ≤ 128) :
    ∀ r ∈ W L ++ [⟨L.B + BitVec.ofNat 64 (24 + dst), P.H.D⟩], ∃ r' ∈ KVW L, Region.Sub r r' :=
  kvw_of fun r hr => by
    simp only [W, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl (Region.sub_prefix (by omega_using []))
    · exact .inr (Region.sub_prefix (by omega_using []))
    · exact .inr (Offset.sub_base _ (by omega_using [h]))

/-- The `D` bytes at `o` in the frame survive HMAC's writes and the MAC's at `dst`. -/
theorem kv_frame {dst : Nat} (hL : L.Ok) {m m' : Mem}
    (hf : Frame (W L ++ [⟨L.B + BitVec.ofNat 64 (24 + dst), P.H.D⟩]) m m')
    {o : Nat} (ho : 24 ≤ o) (hod : o + P.H.D ≤ 24 + dst ∨ 24 + dst + P.H.D ≤ o) (hoe : o + P.H.D ≤ 240)
    (hdst : dst + P.H.D ≤ 184) :
    Spec.Sha256.bytesAt m' (L.B + BitVec.ofNat 64 o) P.H.D = Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 o) P.H.D :=
  bytesAt_frame hf (fun r hr => by
    have := L.he
    simp only [W, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.stk_scr0 (by omega_using [hoe]) (by decide)
    · exact Offset.disjoint_base _ ho (by nums)
    · exact Offset.disjoint _ hod (by omega_using [hoe]) (by omega_using [hdst])) (by nums)

/-- What HMAC's functions write, with the MAC at `dst` in the frame, is apart from the copy. -/
theorem wd_save (hL : L.Ok) {dst : Nat} (hdst : dst + P.H.D ≤ 184) :
    ∀ r ∈ W L ++ [⟨L.B + BitVec.ofNat 64 (24 + dst), P.H.D⟩], Region.Disjoint (SaveR L) r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact W_save hL r hr
  · simp only [List.mem_singleton] at hr; subst hr
    exact (hL.stk_scr (by have := L.he; nums) (by decide)).symm

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
      Frame (W L ++ [⟨L.B + BitVec.ofNat 64 (24 + dst), P.H.D⟩]) u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (24 + dst)) P.H.D =
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
      Frame (W L ++ [⟨L.B + BitVec.ofNat 64 (24 + fK), P.H.D⟩]) u.mem u'.mem ∧
      kOf P L u'.mem = Spec.Hmac.hmacBlockKey P.ok.SH.H k0
        (vOf P L u.mem ++ Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 2256) len) := by
  refine WP.seq (WP.mono (updV_step hL hT hu) fun w ⟨hw, hfw⟩ => ?_)
  refine WP.seq (WP.mono (updM_step hL hT hw (by simp [Spec.Sha256.bytesAt]) hlen) fun w' ⟨hw', hfw'⟩ => ?_)
  refine WP.mono (fin_step hL hT hw' (len := len) (dst := fK)
    (by simp [Spec.Sha256.bytesAt]) (by omega_using [hlen]) (by simp only [fK]; nums)) fun u' ⟨hc', hf', hm'⟩ => ⟨hc', ?_, ?_⟩
  · exact ((hfw.sub fun r hr => ⟨r, List.mem_append_left _ hr, sub_refl _⟩).trans
      (hfw'.sub fun r hr => ⟨r, List.mem_append_left _ hr, sub_refl _⟩)).trans hf'
  · show Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 24) P.H.D = _
    rw [show L.B + BitVec.ofNat 64 24 = L.B + BitVec.ofNat 64 (24 + fK) from rfl, hm',
      show sMsg = 2256 from rfl, msg_W hL hfw (len := len) (by omega_using [hlen])]

/-- `V = HMAC_K(V)`, HMAC's states for `K` saved. -/
theorem hmacVS_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).hmacVS t fun t' => Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
      kOf P L t'.mem = kOf P L t.mem ∧ vOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem) ∧
      SavedK P L t'.mem (kOf P L t'.mem) := by
  refine WP.seq (WP.mono (init_step hL hT hc) fun u ⟨hu, hfu⟩ => ?_)
  refine WP.seq (WP.mono (save_ok hL hu) fun u' ⟨hu', hS, hf'⟩ => ?_)
  refine WP.mono (vfin_ok hL hT hu' (dst := fV) (by simp only [fV]; nums)) fun t' ⟨hc', hf'', hm⟩ => ?_
  obtain hW : Frame (W L ++ [SaveR L]) t.mem u'.mem :=
    (hfu.sub fun r hr => ⟨r, List.mem_append_left _ hr, sub_refl _⟩).trans
      (hf'.sub fun r hr => ⟨r, List.mem_append_right _ hr, sub_refl _⟩)
  obtain hk : kOf P L t'.mem = kOf P L t.mem := by
    show Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 24) P.H.D = _
    rw [kv_frame hL hf'' (o := 24) (by decide) (.inl (by simp only [fV]; nums)) (by nums) (by simp only [fV]; nums)]
    exact bytesAt_frame hW (fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · simp only [W, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hL.stk_scr0 (by have := L.he; nums) (by decide)
        · exact Offset.disjoint_base _ (by omega_using []) (by nums)
      · simp only [List.mem_singleton] at hr; subst hr
        exact hL.stk_scr (by have := L.he; nums) (by decide)) (by nums)
  obtain hv : vOf P L u'.mem = vOf P L t.mem :=
    bytesAt_frame hW (fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · simp only [W, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hL.stk_scr0 (by have := L.he; nums) (by decide)
        · exact Offset.disjoint_base _ (by omega_using []) (by nums)
      · simp only [List.mem_singleton] at hr; subst hr
        exact hL.stk_scr (by have := L.he; nums) (by decide)) (by nums)
  refine ⟨hc', ?_, hk, ?_, ?_⟩
  · refine (hW.sub fun r hr => ?_).trans (hf''.sub (wd_kvw (P := P) (dst := fV) (by simp only [fV]; nums)))
    rcases List.mem_append.mp hr with hr | hr
    · exact wd_kvw (P := P) (dst := fV) (by simp only [fV]; nums) r (List.mem_append_left _ hr)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨L.SCR, by simp, Offset.sub_base _ (by decide)⟩
  · rw [show vOf P L t'.mem = Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 (24 + fV)) P.H.D from rfl, hm, hv,
      mac_eq]
  · rw [hk]; exact hS.frame hf'' (wd_save hL (by simp only [fV]; nums))

/-- `V = HMAC_K(V)`, from the saved states for `K`, which it keeps. -/
theorem hmacVR_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t)
    (hS : SavedK P L t.mem (kOf P L t.mem)) :
    WP isa (cfgOf P).hmacVR t fun t' => Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
      kOf P L t'.mem = kOf P L t.mem ∧ vOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem) ∧
      SavedK P L t'.mem (kOf P L t'.mem) := by
  refine WP.seq (WP.mono (restore_ok hL hc hS (blockKey_length (keyOf_length _))) fun u ⟨hu, hfu, hSu⟩ => ?_)
  refine WP.mono (vfin_ok hL hT hu (dst := fV) (by simp only [fV]; nums)) fun t' ⟨hc', hf', hm⟩ => ?_
  obtain hR : Region.Disjoint ⟨L.B + BitVec.ofNat 64 24, 128⟩ ⟨L.scr + BitVec.ofNat 64 0, 8 * 48⟩ :=
    hL.stk_scr (by have := L.he; nums) (by decide)
  obtain hk : kOf P L t'.mem = kOf P L t.mem := by
    show Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 24) P.H.D = _
    rw [kv_frame hL hf' (o := 24) (by decide) (.inl (by simp only [fV]; nums)) (by nums) (by simp only [fV]; nums)]
    exact bytesAt_frame hfu (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hR.sub_left (Offset.sub _ (by omega_using []) (by nums))) (by nums)
  obtain hv : vOf P L u.mem = vOf P L t.mem :=
    bytesAt_frame hfu (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hR.sub_left (Offset.sub _ (by omega_using []) (by nums))) (by nums)
  refine ⟨hc', ?_, hk, ?_, ?_⟩
  · refine (hfu.sub fun r hr => ?_).trans (hf'.sub (wd_kvw (P := P) (dst := fV) (by simp only [fV]; nums)))
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨L.SCR, by simp, Offset.sub_base _ (by decide)⟩
  · rw [show vOf P L t'.mem = Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 (24 + fV)) P.H.D from rfl, hm, hv,
      mac_eq]
  · rw [hk]; exact hSu.frame hf' (wd_save hL (by simp only [fV]; nums))

/-- `K = HMAC_K(V ‖ m)`, for the message `m` of `len` bytes at
`scratch + 2256`, from HMAC's states for `K` by `init` or, if `fresh` is
false, from the saved ones. -/
theorem hmacKB_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) {len : Nat} (hlen : len ≤ 256)
    (fresh : Bool) (hS : fresh = false → SavedK P L t.mem (kOf P L t.mem)) :
    WP isa ((cfgOf P).hmacK fresh len) t fun t' =>
      Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧ vOf P L t'.mem = vOf P L t.mem ∧
      kOf P L t'.mem = P.mac (kOf P L t.mem)
        (vOf P L t.mem ++ Spec.Sha256.bytesAt t.mem (L.scr + BitVec.ofNat 64 2256) len) := by
  obtain post : ∀ {u : State}, St P L g m₀ (Spec.Hmac.blockKey P.ok.SH.H (kOf P L t.mem)) [] u →
      ∀ {ws : List Region}, Frame ws t.mem u.mem → (∀ r ∈ ws, ∃ r' ∈ KVW L, Region.Sub r r') →
      (∀ r ∈ ws, Region.Disjoint ⟨L.B + BitVec.ofNat 64 88, P.H.D⟩ r) →
      (∀ r ∈ ws, Region.Disjoint ⟨L.scr + BitVec.ofNat 64 2256, len⟩ r) →
      WP isa (.seq (cfgOf P).updV (.seq ((cfgOf P).updM len) ((cfgOf P).fin len fK))) u fun t' =>
        Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧ vOf P L t'.mem = vOf P L t.mem ∧
        kOf P L t'.mem = P.mac (kOf P L t.mem)
          (vOf P L t.mem ++ Spec.Sha256.bytesAt t.mem (L.scr + BitVec.ofNat 64 2256) len) := by
    intro u hu ws hf hk hdv hdm
    refine WP.mono (vmfin_ok hL hT hu hlen) fun t' ⟨hc', hf', hm⟩ => ⟨hc', ?_, ?_, ?_⟩
    · exact (hf.sub hk).trans (hf'.sub (wd_kvw (P := P) (dst := fK) (by simp only [fK]; nums)))
    · show Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 88) P.H.D = _
      rw [kv_frame hL hf' (o := 88) (by decide) (.inr (by simp only [fK]; nums)) (by nums) (by simp only [fK]; nums)]
      exact bytesAt_frame hf hdv (by nums)
    · rw [hm]
      obtain hv : vOf P L u.mem = vOf P L t.mem := bytesAt_frame hf hdv (by nums)
      obtain hmsg : Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 2256) len =
          Spec.Sha256.bytesAt t.mem (L.scr + BitVec.ofNat 64 2256) len := bytesAt_frame hf hdm (by omega_using [hlen])
      rw [hv, hmsg, mac_eq]
  cases fresh
  · refine WP.seq (WP.mono (restore_ok hL hc (hS rfl) (blockKey_length (keyOf_length _))) fun u ⟨hu, hfu, _⟩ => ?_)
    have hu' : St P L g m₀ (Spec.Hmac.blockKey P.ok.SH.H (kOf P L t.mem)) [] u := hu
    refine post hu' hfu (fun r hr => ?_) (fun r hr => ?_) (fun r hr => ?_) <;>
      simp only [List.mem_singleton] at hr <;> subst hr
    · exact ⟨L.SCR, by simp, Offset.sub_base _ (by decide)⟩
    · exact hL.stk_scr (by have := L.he; nums) (by decide)
    · exact Offset.disjoint _ (by omega_using []) (by omega_using [hlen]) (by decide)
  · refine WP.seq (WP.mono (init_step hL hT hc) fun u ⟨hu, hfu⟩ => ?_)
    refine post hu hfu (fun r hr => ?_) (fun r hr => ?_) (fun r hr => ?_) <;>
      simp only [W, List.mem_cons, List.not_mem_nil, or_false] at hr <;> rcases hr with rfl | rfl
    · exact ⟨L.SCR, by simp, Region.sub_prefix (by omega_using [])⟩
    · exact ⟨⟨L.B, 152⟩, by simp, Region.sub_prefix (by omega_using [])⟩
    · exact hL.stk_scr0 (by have := L.he; nums) (by decide)
    · exact Offset.disjoint_base _ (by omega_using []) (by nums)
    · exact Offset.disjoint_base _ (by decide) (by omega_using [hlen])
    · exact hL.low_scr (by omega_using [hlen]) |>.symm

/-- What the steps need of the layout: the scalars' bytes, and the table of `P`. -/
def HOk (P : RfcHash) {dn : Nat} (L : Lay dn) : Prop := L.q = P.Q ∧ TabL P L

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
  refine WP.seq (WP.mono (ptrs_ok hL hc) fun p ⟨hcp, hmp, hdip, hsip⟩ => ?_)
  rw [← hmp] at hS ⊢
  refine WP.seq (WP.mono (msg_ok (P := P) hL hq.1 hcp hdip hsip b full) fun u ⟨hcu, hfu, hbu⟩ => ?_)
  obtain hsafe : Region.Disjoint ⟨L.B + BitVec.ofNat 64 24, 128⟩ ⟨L.scr + BitVec.ofNat 64 2256, 1 + 2 * P.Q⟩ :=
    hL.stk_scr (by have := L.he; nums) (by nums)
  obtain hku : kOf P L u.mem = kOf P L p.mem := bytesAt_frame hfu (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hsafe.sub_left (Offset.sub _ (by omega_using []) (by nums))) (by nums)
  obtain hvu : vOf P L u.mem = vOf P L p.mem := bytesAt_frame hfu (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hsafe.sub_left (Offset.sub _ (by omega_using []) (by nums))) (by nums)
  obtain hSu : fresh = false → SavedK P L u.mem (kOf P L u.mem) := fun h => hku ▸ (hS h).frame hfu fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (by nums) (by nums) (by nums)
  refine WP.seq (WP.mono (hmacKB_ok (P := P) hL hT hcu (len := mlen P full)
    (by cases full <;> simp only [mlen, Bool.false_eq_true, ite_true, ite_false] <;> nums) fresh hSu)
    fun w ⟨hcw, hfw, hvw, hkw⟩ => ?_)
  refine WP.mono (hmacVS_ok hL hT hcw) fun t' ⟨hc', hf', hk', hv', hs'⟩ => ⟨hc', ?_, ?_, ?_, hs'⟩
  · exact ((hfu.sub (kvw_of fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact .inl (Offset.sub_base _ (by nums)))).trans hfw).trans hf'
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

end VG.Proof.Ecdsa.Rfc6979.X86_64
