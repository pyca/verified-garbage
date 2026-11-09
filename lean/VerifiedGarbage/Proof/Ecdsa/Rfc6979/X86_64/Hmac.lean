module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Hash
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec

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
  · exact Offset.base_disjoint _ h₁ (by omega)
  · exact hL.low_scr h₂

/-- The data is apart from HMAC's states and working space. -/
theorem work (hd : DataOk L da len) (hL : L.Ok) {e k : Nat} (h : e + k ≤ 2256) :
    Region.Disjoint ⟨da, len⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ := by
  rcases hd with ⟨o, rfl, h₁, h₂⟩ | ⟨o, rfl, h₁, h₂⟩
  · exact hL.stk_scr (by have := L.he; omega) (by omega)
  · exact Offset.disjoint _ (by omega) (by omega) (by omega)

theorem within (hd : DataOk L da len) :
    ∃ R ∈ [L.D, L.DG, L.FR, L.OUT, L.SCR], Within ⟨da, len⟩ R := by
  rcases hd with ⟨o, rfl, h₁, h₂⟩ | ⟨o, rfl, h₁, h₂⟩
  · exact ⟨L.FR, by simp, within_fr _ h₁ (by omega)⟩
  · exact ⟨L.SCR, by simp, within_off _ h₂⟩

end DataOk

/-! ## Loads from the frame -/

/-- `d ← [rsp + o]`, a word of the frame. -/
theorem ldF_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {d : Reg} (hd : d ∉ calleeSaved) {o : Nat}
    (ho : o + 8 ≤ 224 + 8 * L.e) :
    WP isa (.block [.mov d (.mem (stk o))]) u
      (Upd L g m₀ u d (u.mem.readW (L.B + BitVec.ofNat 64 (24 + o)) 64)) := by
  have hr := hc.inFr (d := 24 + o) (by omega) (by omega)
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
  have hr := hc.inFr (d := 24 + o) (by omega) (by omega)
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
  hc.frame.readW (r := L.TAB) (Offset.contains_base _ ho (by have := hL.nt; omega)) (fun r hr => by
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
  refine WP.mono (ldF_ok hL hc (d := .r11) (by decide) (o := fTab) (by simp only [fTab, extra]; omega))
    fun t' h => ⟨h.ctx, h.mem, h.val.trans ?_, h.keep⟩
  rw [show 24 + fTab = 240 + 8 * L.e by simp only [fTab, extra]; omega]; exact hc.pTab

/-- The table's word `j` into `r11`, from its address there. -/
theorem tblk2_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (h11 : t.gpr .r11 = L.tab) {j : Nat}
    (hj : 8 * j + 8 ≤ 48) :
    WP isa (.block [.mov .r11 (.mem (at_ .r11 (8 * j)))]) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧
      t'.gpr .r11 = m₀.readW (L.tab + BitVec.ofNat 64 (8 * j)) 64 ∧ (∀ r, r ≠ .r11 → t'.gpr r = t.gpr r) ∧
      t'.syms = t.syms := by
  have ht := hc.inTab hL (o := 8 * j) hj
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
  have hsy' : t'.syms = t.syms := hsy.trans hs₁
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
    exact .inr (.inr (.inl ((hc.below_sub hn).trans (Region.sub_prefix (by omega)))))

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
  refine WP.mono (ldF_ok hL h₃.ctx (d := .rcx) (by decide) (o := fDl) (by simp only [fDl]; have := L.he; omega))
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
  have hsp : below (u.gpr .rsp) 24 = ⟨L.B, 24⟩ := by rw [hcu.rsp, below24]
  have he := L.he
  exact
    { rdi := hdi, rsi := hsi, rdx := hdx, rcx := by rw [hcx, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by nums)
      r8 := h8, klB := by nums
      cr := hcu.covers fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨L.FR, by simp, within_fr _ (by omega) (by nums)⟩
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
      stk_k := by rw [hsp]; exact Offset.base_disjoint _ (by omega) (by nums)
      stk_s := by rw [hsp]; exact hL.low_scr (by nums)
      scnw := by rw [toNat_add_of (by have := hL.nc; omega)]; have := hL.nc; nums }

theorem xorPad_length (k : List Byte) (p : Byte) : (Spec.Hmac.xorPad k p).length = k.length :=
  List.length_map _

theorem blockKey_length {k : List Byte} (hk : k.length = P.H.D) :
    (Spec.Hmac.blockKey P.ok.SH.H k).length = P.H.P.B := by
  have hB := P.ok.hB
  have hDB : P.H.D < P.H.P.B := by nums
  simp only [Spec.Hmac.blockKey, hk, hB, show ¬ P.H.P.B < P.H.D by omega, ite_false, List.length_append,
    List.length_replicate]
  omega

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
  have hk0 : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8], u'.gpr r = u.gpr r := fun r hr => hk' r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
  have a := initA (P := P) hL hc' ((hk0 _ (by simp)).trans hdi) ((hk0 _ (by simp)).trans hsi)
    ((hk0 _ (by simp)).trans hdx) ((hk0 _ (by simp)).trans hcx) ((hk0 _ (by simp)).trans h8)
  have hsp : below (u'.gpr .rsp) 24 = ⟨L.B, 24⟩ := by rw [hc'.rsp, below24]
  refine WP.of_syms (Proof.Pbkdf2.Md.X86_64.Pbk.hinit_call P.ok P.hI P.hIsp P.hId a
    fun v hrd hwr hcs hf hi ho hsy => ?_)
  have hsafe : ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 0, P.H.S⟩ : Region), ⟨L.scr + BitVec.ofNat 64 192, P.H.S⟩,
      ⟨L.scr + BitVec.ofNat 64 384, 8 * P.H.W⟩], Region.Sub r ⟨L.scr, 2256⟩ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> exact scr_work (by nums)
  have hkey : Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 24) P.H.D = keyOf P L t.mem := by
    rw [hm', hmu]
  rw [hkey] at hi ho
  refine ⟨⟨hc'.keep hL hrd hwr (hcs .rsp (by decide)) (fun r hr _ => hcs r hr) hf
    (safe_call hc' (fun r hr => .inr (.inl ((hsafe r hr).trans (Region.sub_prefix (by omega))))) (Nat.le_refl _))
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
  refine WP.mono (ldF_ok hL h₁.ctx (d := .rsi) (by decide) (o := fBl) (by simp only [fBl]; have := L.he; omega))
    fun u₂ h₂ => ?_
  refine WP.mono (fr_ok hL h₂.ctx (d := .rdx) (by decide) (o := fV) (by decide)) fun u₃ h₃ => ?_
  refine WP.mono (ldF_ok hL h₃.ctx (d := .rcx) (by decide) (o := fDl) (by simp only [fDl]; have := L.he; omega))
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
  refine WP.mono (ldF_ok hL h₁.ctx (d := .rsi) (by decide) (o := fBl) (by simp only [fBl]; have := L.he; omega))
    fun u₂ h₂ => ?_
  refine WP.mono (addF_ok hL h₂.ctx (d := .rsi) (by decide) (o := fDl) (by simp only [fDl]; have := L.he; omega))
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
  have hsp : Region.Sub (below (w.gpr .rsp) 16) ⟨L.B, 24⟩ := hcw.below_sub (by omega)
  exact
    { rdi := hdi, rdx := hdx, rcx := by rw [hcx, BitVec.toNat_ofNat]; omega, r8 := h8
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
  have hk0 : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8], w.gpr r = u.gpr r := fun r hr => hkw r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
  have hsp : Region.Sub (below (w.gpr .rsp) 16) ⟨L.B, 24⟩ := hcw.below_sub (by omega)
  have a := updA (P := P) hL hcw hd hlen ((hk0 _ (by simp)).trans hdi) ((hk0 _ (by simp)).trans hdx)
    ((hk0 _ (by simp)).trans hcx) ((hk0 _ (by simp)).trans h8)
  refine WP.of_syms (Proof.Pbkdf2.Md.X86_64.Calls.upd_call P.ok.stream a (by omega) fun w' af hr hsy => ?_)
  have hws : ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 0, P.H.stream.S⟩ : Region),
      ⟨L.scr + BitVec.ofNat 64 384, P.ok.stream.Wb⟩], Region.Sub r ⟨L.scr, 2256⟩ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> exact scr_work (by nums)
  have hf' : Frame (W L) w.mem w'.mem := af.frame.sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨⟨L.scr, 2256⟩, by simp, hws r hr⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨L.B, 24⟩, by simp, hsp⟩
  have hkl := hu.klen
  refine ⟨⟨hcw.keep hL af.rd af.wr (af.cs .rsp (by decide)) (fun r hr _ => af.cs r hr) af.frame
      (safe_call hcw (fun r hr => .inr (.inl ((hws r hr).trans (Region.sub_prefix (by omega))))) (by omega)) hsy,
    hkl, by simp [Spec.Sha256.bytesAt]; omega, ?_, ?_⟩, hmw ▸ hf'⟩
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
  have hw : St P L g m₀ k0 [] w := ⟨hcw, hu.klen, hu.tlen, hmw ▸ hu.inner, hmw ▸ hu.outer⟩
  refine WP.mono (upd_call_ok hL hT hw (len := P.H.D)
    (.inl ⟨88, rfl, by omega, by nums⟩) (by nums) (by simp; nums) hdi (by simpa using hsi) hdx hcx h8)
    fun u' ⟨hs, hf⟩ => ?_
  rw [List.nil_append, hmw] at hs
  exact ⟨hs, hmw ▸ hf⟩

/-- The inner state, for the key `K₀`, holding `text`, updated with the message's `len` bytes. -/
theorem updM_step (hL : L.Ok) (hT : TabL P L) {k0 text : List Byte} {u : State}
    (hu : St P L g m₀ k0 text u) (ht : text.length = P.H.D) {len : Nat} (hlen : len ≤ 256) :
    WP isa ((cfgOf P).updM len) u fun u' =>
      St P L g m₀ k0 (text ++ Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 sMsg) len) u' ∧
      Frame (W L) u.mem u'.mem := by
  refine WP.seq (WP.mono (updMArgs_ok hL hT hu.ctx (len := len) (by omega))
    fun w ⟨hcw, hmw, hdi, hsi, hdx, hcx, h8⟩ => ?_)
  have hw : St P L g m₀ k0 text w := ⟨hcw, hu.klen, hu.tlen, hmw ▸ hu.inner, hmw ▸ hu.outer⟩
  refine WP.mono (upd_call_ok hL hT hw (len := len) (.inr ⟨sMsg, rfl, by decide, by simp only [sMsg]; omega⟩)
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
  refine WP.mono (ldF_ok hL h₂.ctx (d := .rdx) (by decide) (o := fBl) (by simp only [fBl]; have := L.he; omega))
    fun u₃ h₃ => ?_
  refine WP.mono (addF_ok hL h₃.ctx (d := .rdx) (by decide) (o := fDl) (by simp only [fDl]; have := L.he; omega))
    fun u₃' h₃' => ?_
  refine WP.mono (addI_ok hL h₃'.ctx (d := .rdx) (by decide) hlen) fun u₃'' h₃'' => ?_
  refine WP.mono (fr_ok hL h₃''.ctx (d := .rcx) (by decide) hdst) fun u₄ h₄ => ?_
  refine WP.mono (scr_ok hL h₄.ctx (d := .r8) (by decide) (a := 384) (by decide)) fun u₅ h₅ => ?_
  have hm2 : u₂.mem = u.mem := by rw [h₂.mem, h₁.mem]
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
  have hsp : below (w.gpr .rsp) 24 = ⟨L.B, 24⟩ := by rw [hcw.rsp, below24]
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
        · exact ⟨L.FR, by simp, within_fr _ (by omega) (by nums)⟩
        · exact ⟨L.SCR, by simp, within_off _ (by nums)⟩
      i_u := Offset.disjoint _ (by nums) (by nums) (by nums)
      i_o := (hL.stk_scr (d := 24 + dst) (by nums) (by nums)).symm
      i_s := Offset.disjoint _ (by nums) (by nums) (by nums)
      u_o := (hL.stk_scr (d := 24 + dst) (by nums) (by nums)).symm
      u_s := Offset.disjoint _ (by nums) (by nums) (by nums)
      o_s := hL.stk_scr (by nums) (by nums)
      stk_i := by rw [hsp]; exact hL.low_scr (by nums)
      stk_u := by rw [hsp]; exact hL.low_scr (by nums)
      stk_o := by rw [hsp]; exact Offset.base_disjoint _ (by omega) (by nums)
      stk_s := by rw [hsp]; exact hL.low_scr (by nums)
      scnw := by rw [toNat_add_of (by have := hL.nc; omega)]; have := hL.nc; nums }

/-- HMAC's `finalize`, for the key `K₀` and the text `text`, of `D + len`
bytes: the MAC in the frame at `dst`. -/
theorem fin_step (hL : L.Ok) (hT : TabL P L) {k0 text : List Byte} {u : State} (hu : St P L g m₀ k0 text u)
    {len dst : Nat} (ht : text.length = P.H.D + len) (hlen : len < 2 ^ 31) (hdst : dst + P.H.D ≤ 184) :
    WP isa ((cfgOf P).fin len dst) u fun u' => Ctx L g m₀ u' ∧
      Frame (W L ++ [⟨L.B + BitVec.ofNat 64 (24 + dst), P.H.D⟩]) u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (24 + dst)) P.H.D =
        Spec.Hmac.hmacBlockKey P.ok.SH.H k0 text := by
  refine WP.seq (WP.mono (finArgs_ok hL hT hu.ctx (len := len) (dst := dst) hlen (by omega))
    fun w ⟨hcw, hmw, hdi, hsi, hdx, hcx, h8⟩ => ?_)
  have hok := hcw.tabOk
  have htm := hcw.tabMem
  rw [hT.1, hT.2] at hok
  rw [hT.1] at htm
  refine tcall_ok hL hcw (j := 2) (by decide) htm.2.2 hok.f fun w₁ hc₁ hm₁ hk₁ _ => ?_
  have hk0 : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8], w₁.gpr r = w.gpr r := fun r hr => hk₁ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
  have hsp : below (w₁.gpr .rsp) 24 = ⟨L.B, 24⟩ := by rw [hc₁.rsp, below24]
  have a := finA (P := P) hL hc₁ (cnt := P.H.P.B + P.H.D + len) hdst ((hk0 _ (by simp)).trans hdi)
    ((hk0 _ (by simp)).trans hsi) ((hk0 _ (by simp)).trans hdx) ((hk0 _ (by simp)).trans hcx)
    ((hk0 _ (by simp)).trans h8)
  refine WP.of_syms (Proof.Pbkdf2.Md.X86_64.Pbk.hfin_call P.ok P.hF P.hFsp P.hFd a
    fun w' hrd hwr hcs hf hpost hsy => ?_)
  have hws : ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 0, P.H.S⟩ : Region),
      ⟨L.B + BitVec.ofNat 64 (24 + dst), P.H.D⟩, ⟨L.scr + BitVec.ofNat 64 384, 8 * P.H.W⟩] ++
      [below (w₁.gpr .rsp) 24], ∃ r' ∈ W L ++ [⟨L.B + BitVec.ofNat 64 (24 + dst), P.H.D⟩], Region.Sub r r' := by
    simp only [W, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, hsp]
    rintro r (rfl | rfl | rfl | rfl)
    · exact ⟨⟨L.scr, 2256⟩, by simp, scr_work (by nums)⟩
    · exact ⟨⟨L.B + BitVec.ofNat 64 (24 + dst), P.H.D⟩, by simp, sub_refl _⟩
    · exact ⟨⟨L.scr, 2256⟩, by simp, scr_work (by nums)⟩
    · exact ⟨⟨L.B, 24⟩, by simp, sub_refl _⟩
  have hm : w₁.mem = u.mem := hm₁.trans hmw
  refine ⟨hc₁.keep hL hrd hwr (hcs .rsp (by decide)) (fun r hr _ => hcs r hr) hf (hsy := hsy) fun r hr => ?_,
    hm ▸ hf.sub hws, ?_⟩
  · obtain ⟨r', hr', hs⟩ := hws r hr
    simp only [W, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · exact .inr (.inl (hs.trans (Region.sub_prefix (by omega))))
    · exact .inr (.inr (.inl (hs.trans (Region.sub_prefix (by omega)))))
    · exact (safe_low L (by nums)).of_sub hs
  · have hk := hu.klen
    exact hpost _ _ hk (by rw [hk]; have := hu.tlen; nums) (hm ▸ hu.inner)
      (by rw [ht]; congr 1; omega) (hm ▸ hu.outer)

end VG.Proof.Ecdsa.Rfc6979.X86_64
