module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Hash
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.ICall
import VerifiedGarbage.Proof.Pbkdf2.MdKeys
import VerifiedGarbage.Proof.Hmac.Common

/-!
# Deterministic ECDSA on x86-64: one HMAC, through the table

`HMAC_K(data)` (`Cfg.hmac`), for the key `K` (of the hash function's output
length) in the frame and `len` bytes of data in the frame or in `scratch`
above HMAC's working space (`DataOk`), written to the frame at `dst`, from
the table's streaming functions, each called indirectly (`tcall_ok`: the
table's word, which `Ctx` says holds the function of `L.G`, whose call an
indirect call of `L.f`'s functions reaches): the states for the key
(`init_step`: each set by `init`, `initCall_ok`, and updated with the padded
key, `padBlk_ok` and `updCall_ok`), the inner state updated with the data
(`upd_step`), and the MAC (`fin_step`: the inner state finalized,
`finCall_ok`, the outer one updated with its digest and finalized, and the
digest copied). They change only HMAC's states and working space, the padded
key and what `finalize` writes (all within the first 2256 bytes of
`scratch`), the 24 bytes below the frame, and `dst` (`hmac_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64
open VG.WriteBytes (writeBytes writeBytes_append writeBytes_nil writeBytes_frame)

/-- Where the data may be: in the frame below its pointers, or in `scratch`
above HMAC's working space. -/
def DataOk {dn : Nat} (L : Lay dn) (da : Addr) (len : Nat) : Prop :=
  (∃ o, da = L.B + BitVec.ofNat 64 o ∧ 24 ≤ o ∧ o + len ≤ 192) ∨
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
  · exact hL.stk_scr (by omega) (by omega)
  · exact Offset.disjoint _ (by omega) (by omega) (by omega)

theorem within (hd : DataOk L da len) :
    ∃ R ∈ [L.D, L.DG, L.FR, L.OUT, L.SCR], Within ⟨da, len⟩ R := by
  rcases hd with ⟨o, rfl, h₁, h₂⟩ | ⟨o, rfl, h₁, h₂⟩
  · exact ⟨L.FR, by simp, within_fr _ h₁ (by omega)⟩
  · exact ⟨L.SCR, by simp, within_off _ h₂⟩

end DataOk

/-! ## The table -/

/-- The layout's table is of `P`'s hash function and functions, and its
frame has `P`'s words above the pointers. -/
def TabL (P : RfcHash) {dn : Nat} (L : Lay dn) : Prop := L.G = P.H.stream ∧ L.f = P.f ∧ L.e = P.e

/-- The table's words, as on entry. -/
theorem Ctx.tabWord (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {o : Nat} (ho : o + 8 ≤ 40) :
    t.mem.readW (L.tab + BitVec.ofNat 64 o) 64 = m₀.readW (L.tab + BitVec.ofNat 64 o) 64 :=
  hc.frame.readW (r := L.TAB) (Offset.contains_base _ ho (by have := hL.nt; omega)) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.to
    · exact hL.tc
    · exact hL.tk) (by decide)

/-- The indirect call of the table's function `j`, at the address its word
`j` holds, of `n`. -/
theorem tcall_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) {j : Nat} (hj : 8 * j + 8 ≤ 40)
    {n : String} {c : Prog isa} {ts : List (String × Prog isa)}
    (hw : m₀.readW (L.tab + BitVec.ofNat 64 (8 * j)) 64 = t.syms n)
    (hf : ts.find? (fun q => t.syms q.1 == t.syms n) = some (n, c)) {Q : State → Prop}
    (h : ∀ t', Ctx L g m₀ t' → t'.mem = t.mem → (∀ r, r ≠ .r11 → t'.gpr r = t.gpr r) → t'.syms = t.syms →
      WP isa (.call n c) t' Q) :
    WP isa ((cfgOf P).tcall j ts) t Q := by
  have hx : (cfgOf P).fTab = 216 + 8 * L.e := by rw [Cfg.fTab, extra_eq, hT.2.2]; rfl
  have hs := hc.inFr (d := 240 + 8 * L.e) (by omega) (by omega)
  have ht := hc.inTab hL (o := 8 * j) hj
  have hb : WP isa (.block [.mov .r11 (.mem (stk (cfgOf P).fTab)), .mov .r11 (.mem (at_ .r11 (8 * j)))]) t
      fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧ t'.gpr .r11 = t.syms n ∧
        (∀ r, r ≠ .r11 → t'.gpr r = t.gpr r) ∧ t'.syms = t.syms := by
    apply WP.of_runBlock
    simp only [hx, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, ea_stk, ea_at, hc.rsp,
      Offset.add_add, show 24 + (216 + 8 * L.e) = 240 + 8 * L.e by omega, hs, ite_true, Option.map_some,
      hc.pTab, RegUpd.gpr_setReg_self, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, ht,
      hc.tabWord hL hj, hw, Option.some.injEq, exists_eq_left']
    refine ⟨hc.set hL (d := .r11) (by decide) rfl rfl rfl rfl fun r hr => ?_, trivial, trivial, fun r hr => ?_, rfl⟩
    · rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_setReg_of_ne _ _ hr]
    · rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_setReg_of_ne _ _ hr]
  unfold Cfg.tcall
  refine WP.seq (WP.mono hb fun t' ⟨hc', hm, h11, hk, hsy⟩ => ?_)
  refine WP.icalls_of_call (a := t.syms n) (by simp only [X86_64.icall, h11]) ?_ (h t' hc' hm hk hsy)
  show ts.find? (fun q => t'.syms q.1 == t.syms n) = _
  rw [hsy]; exact hf

/-! ## The streaming `init` -/

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

/-- `init` of the state at `scratch + o`: it represents the empty message. -/
theorem initCall_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) {o : Nat} (ho : o + 192 ≤ 384) :
    WP isa ((cfgOf P).initCall o) t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 o, P.H.S⟩, ⟨L.B, 24⟩] t.mem u.mem ∧
      P.ok.SH.Repr u.mem (L.scr + BitVec.ofNat 64 o) [] := by
  refine WP.seq (WP.mono (scr_ok hL hc (d := .rdi) (by decide) (a := o) (by omega)) fun u h => ?_)
  have hok := h.ctx.tabOk
  have htm := h.ctx.tabMem
  rw [hT.1, hT.2.1] at hok
  rw [hT.1] at htm
  refine tcall_ok hL hT h.ctx (j := 0) (by decide) (n := P.H.stream.initN) (c := P.H.stream.initC) htm.1 hok.1
    fun u' hc' hm' hk' _ => ?_
  have hdi : u'.gpr .rdi = L.scr + BitVec.ofNat 64 o := (hk' _ (by decide)).trans h.val
  have hsp : below (u'.gpr .rsp) 24 = ⟨L.B, 24⟩ := by rw [hc'.rsp, below24]
  refine WP.of_syms (Proof.Pbkdf2.Md.X86_64.Calls.init_call P.ok.stream hdi
    (hc'.coversW fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨L.SCR, by simp, within_off _ (by nums)⟩)
    ((hL.low_scr (by nums)).sub_left (hc'.below_sub (by omega))) fun u'' af hr hsy => ?_)
  have hsafe : Region.Sub ⟨L.scr + BitVec.ofNat 64 o, P.H.stream.S⟩ ⟨L.scr, 2256⟩ := scr_work (by nums)
  refine ⟨hc'.keep hL af.rd af.wr (af.cs .rsp (by decide)) (fun r hr _ => af.cs r hr) af.frame
      (safe_call hc' (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact .inr (.inl (hsafe.trans (Region.sub_prefix (by omega))))) (by omega)) hsy, ?_, hr⟩
  rw [← h.mem, ← hm']
  exact af.frame.sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., sub_refl _⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨L.B, 24⟩, by simp, hc'.below_sub (by omega)⟩

/-! ## The streaming `update` -/

/-- The arguments of `update`: the state at `scratch + o` holding `cnt`
bytes, the data, its length and the working space. -/
theorem updArgs_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {o cnt : Nat} (ho : o < 2 ^ 31)
    {dataA : List Instr} {da : Addr} {len : Nat}
    (hdA : ∀ u, Ctx L g m₀ u → WP isa (.block dataA) u (Upd L g m₀ u .rdx da)) (hcnt : cnt < 2 ^ 32)
    (hlen : len < 2 ^ 32) :
    WP isa (.block (Cfg.updArgs o cnt dataA len)) u fun u' => Ctx L g m₀ u' ∧
      u'.mem = u.mem ∧ u'.gpr .rdi = L.scr + BitVec.ofNat 64 o ∧ u'.gpr .rsi = BitVec.ofNat 64 cnt ∧
      u'.gpr .rdx = da ∧ u'.gpr .rcx = BitVec.ofNat 64 len ∧ u'.gpr .r8 = L.scr + BitVec.ofNat 64 384 := by
  rw [Cfg.updArgs, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (scr_ok hL hc (d := .rdi) (by decide) (a := o) ho) fun u₁ h₁ => ?_
  refine WP.mono (mov32_ok hL h₁.ctx (d := .rsi) (by decide) hcnt) fun u₂ h₂ => ?_
  refine WP.mono (hdA u₂ h₂.ctx) fun u₃ h₃ => ?_
  refine WP.mono (mov32_ok hL h₃.ctx (d := .rcx) (by decide) hlen) fun u₄ h₄ => ?_
  refine WP.mono (scr_ok hL h₄.ctx (d := .r8) (by decide) (a := 384) (by decide)) fun u₅ h₅ => ?_
  refine ⟨h₅.ctx, by rw [h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem], ?_, ?_, ?_, ?_, h₅.val⟩
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.keep _ (by decide), h₁.val]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.val]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.val]
  · rw [h₅.keep _ (by decide), h₄.val]

/-- Where data `update` reads may be: within a buffer or the frame, and
apart from the state it updates, the working space and the stack below the
frame. -/
structure UpdData (P : RfcHash) {dn : Nat} (L : Lay dn) (o : Nat) (da : Addr) (len : Nat) : Prop where
  cov : ∃ R ∈ [L.D, L.DG, L.FR, L.OUT, L.SCR], Within ⟨da, len⟩ R
  st : Region.Disjoint ⟨da, len⟩ ⟨L.scr + BitVec.ofNat 64 o, P.H.S⟩
  wk : Region.Disjoint ⟨da, len⟩ ⟨L.scr + BitVec.ofNat 64 384, P.ok.stream.Wb⟩
  low : Region.Disjoint ⟨L.B, 24⟩ ⟨da, len⟩

/-- `update` of the state at `scratch + o`, holding `cnt` bytes, with `len`
bytes at `da`: the state represents them too. -/
theorem updCall_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) {o cnt : Nat} (ho : o + 192 ≤ 384)
    {dataA : List Instr} {da : Addr} {len : Nat}
    (hdA : ∀ u, Ctx L g m₀ u → WP isa (.block dataA) u (Upd L g m₀ u .rdx da)) (hd : UpdData P L o da len)
    (hcnt : cnt < 2 ^ 32) (hlen : len < 2 ^ 32)
    {msg : List Byte} (hr : P.ok.SH.Repr t.mem (L.scr + BitVec.ofNat 64 o) msg) (hml : msg.length = cnt) :
    WP isa ((cfgOf P).updCall o cnt dataA len) t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 o, P.H.S⟩, ⟨L.scr + BitVec.ofNat 64 384, P.ok.stream.Wb⟩, ⟨L.B, 24⟩]
        t.mem u.mem ∧
      P.ok.SH.Repr u.mem (L.scr + BitVec.ofNat 64 o) (msg ++ Spec.Sha256.bytesAt t.mem da len) := by
  refine WP.seq (WP.mono (updArgs_ok hL hc (o := o) (by omega) hdA hcnt hlen)
    fun w ⟨hcw, hmw, hdi, hsi, hdx, hcx, h8⟩ => ?_)
  have hok := hcw.tabOk
  have htm := hcw.tabMem
  rw [hT.1, hT.2.1] at hok
  rw [hT.1] at htm
  refine tcall_ok hL hT hcw (j := 1) (by decide) (n := P.H.stream.updN) (c := P.H.stream.updC) htm.2.1 hok.2.1
    fun w' hc' hm' hk' _ => ?_
  have hsp : Region.Sub (below (w'.gpr .rsp) 16) ⟨L.B, 24⟩ := hc'.below_sub (by omega)
  have a : Proof.Pbkdf2.Md.X86_64.Calls.UpdArgs P.ok.stream w' (L.scr + BitVec.ofNat 64 o) da
      (L.scr + BitVec.ofNat 64 384) len :=
    { rdi := (hk' _ (by decide)).trans hdi, rdx := (hk' _ (by decide)).trans hdx
      rcx := by rw [hk' _ (by decide), hcx, BitVec.toNat_ofNat]; omega
      r8 := (hk' _ (by decide)).trans h8
      cd := hc'.covers fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hd.cov
      cw := hc'.coversW fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact ⟨L.SCR, by simp, within_off _ (by nums)⟩
      st_sc := Offset.disjoint _ (by nums) (by nums) (by nums)
      d_st := hd.st
      d_sc := hd.wk
      stk_st := (hL.low_scr (by nums)).sub_left hsp
      stk_d := hd.low.sub_left hsp
      stk_sc := (hL.low_scr (by nums)).sub_left hsp }
  refine WP.of_syms (Proof.Pbkdf2.Md.X86_64.Calls.upd_call P.ok.stream a (by omega) fun w'' af hrr hsy => ?_)
  have hws : ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 o, P.H.stream.S⟩ : Region),
      ⟨L.scr + BitVec.ofNat 64 384, P.ok.stream.Wb⟩], Region.Sub r ⟨L.scr, 2256⟩ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> exact scr_work (by nums)
  refine ⟨hc'.keep hL af.rd af.wr (af.cs .rsp (by decide)) (fun r hr _ => af.cs r hr) af.frame
      (safe_call hc' (fun r hr => .inr (.inl ((hws r hr).trans (Region.sub_prefix (by omega))))) (by omega)) hsy,
    ?_, ?_⟩
  · rw [← hmw, ← hm']
    exact af.frame.sub fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, List.mem_cons_self .., sub_refl _⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), sub_refl _⟩
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨L.B, 24⟩, by simp, hsp⟩
  · have := hrr msg (by rw [hm', hmw]; exact hr) (by rw [hk' _ (by decide), hsi, hml])
    rwa [hm', hmw] at this

/-! ## The streaming `finalize` -/

/-- `finalize` of the state at `scratch + o`, holding `cnt` bytes, into
`scratch + sTmp`: its first `D` bytes are the digest. -/
theorem finCall_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) {o cnt : Nat} (ho : o + 192 ≤ 384)
    (hcnt : cnt < 2 ^ 32) {msg : List Byte} (hr : P.ok.SH.Repr t.mem (L.scr + BitVec.ofNat 64 o) msg)
    (hml : msg.length = cnt) :
    WP isa ((cfgOf P).finCall o cnt) t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 o, P.H.S⟩, ⟨L.scr + BitVec.ofNat 64 1920, P.H.stream.F⟩,
        ⟨L.scr + BitVec.ofNat 64 384, P.ok.stream.Wb⟩, ⟨L.B, 24⟩] t.mem u.mem ∧
      (Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 1920) P.H.stream.F).take P.H.D = P.ok.SH.H.hash msg := by
  have hb : WP isa (.block (Cfg.finArgs o cnt)) t fun w => Ctx L g m₀ w ∧ w.mem = t.mem ∧
      w.gpr .rdi = L.scr + BitVec.ofNat 64 o ∧ w.gpr .rsi = BitVec.ofNat 64 cnt ∧
      w.gpr .rdx = L.scr + BitVec.ofNat 64 1920 ∧ w.gpr .rcx = L.scr + BitVec.ofNat 64 384 := by
    rw [Cfg.finArgs, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
    refine WP.mono (scr_ok hL hc (d := .rdi) (by decide) (a := o) (by omega)) fun u₁ h₁ => ?_
    refine WP.mono (mov32_ok hL h₁.ctx (d := .rsi) (by decide) hcnt) fun u₂ h₂ => ?_
    refine WP.mono (scr_ok hL h₂.ctx (d := .rdx) (by decide) (a := 1920) (by decide)) fun u₃ h₃ => ?_
    refine WP.mono (scr_ok hL h₃.ctx (d := .rcx) (by decide) (a := 384) (by decide)) fun u₄ h₄ => ?_
    refine ⟨h₄.ctx, by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem], ?_, ?_, ?_, h₄.val⟩
    · rw [h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.keep _ (by decide), h₁.val]
    · rw [h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.val]
    · rw [h₄.keep _ (by decide), h₃.val]
  refine WP.seq (WP.mono hb fun w ⟨hcw, hmw, hdi, hsi, hdx, hcx⟩ => ?_)
  have hok := hcw.tabOk
  have htm := hcw.tabMem
  rw [hT.1, hT.2.1] at hok
  rw [hT.1] at htm
  refine tcall_ok hL hT hcw (j := 2) (by decide) (n := P.H.stream.finN) (c := P.H.stream.finC) htm.2.2 hok.2.2
    fun w' hc' hm' hk' _ => ?_
  have hsp : Region.Sub (below (w'.gpr .rsp) 16) ⟨L.B, 24⟩ := hc'.below_sub (by omega)
  have a : Proof.Pbkdf2.Md.X86_64.Calls.FinArgs P.ok.stream w' (L.scr + BitVec.ofNat 64 o)
      (L.scr + BitVec.ofNat 64 1920) (L.scr + BitVec.ofNat 64 384) :=
    { rdi := (hk' _ (by decide)).trans hdi, rdx := (hk' _ (by decide)).trans hdx
      rcx := (hk' _ (by decide)).trans hcx
      cw := hc'.coversW fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> exact ⟨L.SCR, by simp, within_off _ (by nums)⟩
      st_o := Offset.disjoint _ (by nums) (by nums) (by nums)
      st_sc := Offset.disjoint _ (by nums) (by nums) (by nums)
      o_sc := Offset.disjoint _ (by nums) (by nums) (by nums)
      stk_st := (hL.low_scr (by nums)).sub_left hsp
      stk_o := (hL.low_scr (by nums)).sub_left hsp
      stk_sc := (hL.low_scr (by nums)).sub_left hsp }
  refine WP.of_syms (Proof.Pbkdf2.Md.X86_64.Calls.fin_call P.ok.stream a fun w'' af hrr hsy => ?_)
  have hws : ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 o, P.H.stream.S⟩ : Region),
      ⟨L.scr + BitVec.ofNat 64 1920, P.H.stream.F⟩, ⟨L.scr + BitVec.ofNat 64 384, P.ok.stream.Wb⟩],
      Region.Sub r ⟨L.scr, 2256⟩ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> exact scr_work (by nums)
  refine ⟨hc'.keep hL af.rd af.wr (af.cs .rsp (by decide)) (fun r hr _ => af.cs r hr) af.frame
      (safe_call hc' (fun r hr => .inr (.inl ((hws r hr).trans (Region.sub_prefix (by omega))))) (by omega)) hsy,
    ?_, ?_⟩
  · rw [← hmw, ← hm']
    exact af.frame.sub fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨_, List.mem_cons_self .., sub_refl _⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), sub_refl _⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), sub_refl _⟩
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨L.B, 24⟩, by simp, hsp⟩
  · exact hrr msg (by rw [hm', hmw]; exact hr) (by rw [hml]; omega) (by rw [hk' _ (by decide), hsi, hml])

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
    simp only [Function.comp, show 4 * k + j < D by omega, ite_true, Offset.add_add]
  · rw [show List.replicate 4 c = (List.range 4).map fun _ => c from rfl]
    refine List.map_congr_left fun j hj => ?_
    have := List.mem_range.mp hj
    simp only [Function.comp, show ¬ 4 * k + j < D by omega, ite_false]

/-- All `B` bytes: `K₀ ⊕ c`, for a key of `D ≤ B` bytes. -/
theorem padBytes_eq (m : Mem) (K : Addr) {D : Nat} (c : Byte) (H : Spec.Hmac.HashFunction)
    (hD : D ≤ H.blockSize) :
    padBytes m K D c H.blockSize = Spec.Hmac.xorPad (Spec.Hmac.blockKey H (Spec.Sha256.bytesAt m K D)) c := by
  rw [Proof.Pbkdf2.MdKeys.blockKey_short H (by simp only [Proof.Hmac.Common.bytesAt_length]; exact hD)]
  apply List.ext_getElem (by simp [padBytes, Spec.Hmac.xorPad, Proof.Hmac.Common.bytesAt_length]; omega)
  intro i h₁ h₂
  simp only [padBytes, List.getElem_map, List.getElem_range, Spec.Hmac.xorPad]
  by_cases hi : i < D
  · rw [List.getElem_append_left (by simp [Proof.Hmac.Common.bytesAt_length, hi])]
    simp [hi, Spec.Sha256.bytesAt]
  · simp only [hi, ite_false]
    rw [List.getElem_append_right (by simp [Proof.Hmac.Common.bytesAt_length]; omega)]
    simp

/-- Word `k` of the padded key, after `4 k` of its bytes. -/
theorem padW_ok {t : State} (P0 K : Addr) (D : Nat) (c : Byte) {k : Nat} (hD : D % 4 = 0) (hk : 4 * k + 4 < 2 ^ 64)
    {u : State} (hdi : u.gpr .rdi + BitVec.ofNat 64 1792 = P0) (hsp : u.gpr .rsp = K)
    (hcx : (u.gpr .rcx).setWidth 32 = c ++ c ++ c ++ c)
    (hrK : k < D / 4 → InRegions (u.rd ++ u.wr) (K + BitVec.ofNat 64 (4 * k)) 4)
    (hw : InRegions u.wr (P0 + BitVec.ofNat 64 (4 * k)) 4)
    (hm : u.mem = writeBytes t.mem P0 (padBytes t.mem K D c (4 * k)))
    (hKd : k < D / 4 → Spec.Sha256.bytesAt u.mem (K + BitVec.ofNat 64 (4 * k)) 4 =
      Spec.Sha256.bytesAt t.mem (K + BitVec.ofNat 64 (4 * k)) 4)
    (cf : Impl.Ecdsa.Rfc6979.X86_64.Cfg) (hcD : cf.D = D) :
    WP isa (.block (cf.padW k)) u fun u' => u'.rd = u.rd ∧ u'.wr = u.wr ∧
      (∀ r, r ≠ .rax → u'.gpr r = u.gpr r) ∧ u'.mem = writeBytes t.mem P0 (padBytes t.mem K D c (4 * k + 4)) := by
  have hl := padBytes_length t.mem K D c (4 * k)
  have hap : ∀ ys : List Byte, ys.length = 4 →
      writeBytes (writeBytes t.mem P0 (padBytes t.mem K D c (4 * k))) (P0 + BitVec.ofNat 64 (4 * k)) ys =
        writeBytes t.mem P0 (padBytes t.mem K D c (4 * k) ++ ys) := fun ys hys => by
    have := writeBytes_append t.mem P0 (padBytes t.mem K D c (4 * k)) ys (by rw [hl, hys]; omega)
    rwa [hl] at this
  have hst : u.ea (at_ .rdi (sPad + 4 * k)) = P0 + BitVec.ofNat 64 (4 * k) := by
    rw [ea_at, ← hdi, Offset.add_add]; rfl
  have sw : ∀ x : BitVec 32, (x.setWidth 64).setWidth 32 = x := fun x => by
    rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
  by_cases hkD : k < D / 4
  · rw [Cfg.padW, ite_eq_left_of_eq_true _ _ (eq_true (by rw [hcD]; exact hkD))]
    refine Proof.Sha256.X86_64.Stream.wp_mov32m (a := K + BitVec.ofNat 64 (4 * k))
      (by rw [ea_stk, hsp, fK, Nat.zero_add]) (hrK hkD) fun s₁ u₁ => ?_
    refine Proof.Pbkdf2.Md.X86_64.Calls.wp_xor32r fun s₂ u₂ => ?_
    refine Proof.Sha256.X86_64.Stream.wp_store32 (a := P0 + BitVec.ofNat 64 (4 * k))
      (by rw [ea_at, u₂.other _ (by decide : Reg.rdi ≠ .rax), u₁.other _ (by decide : Reg.rdi ≠ .rax), ← hdi,
        Offset.add_add]; rfl)
      (by rw [u₂.wr, u₁.wr]; exact hw) fun s₃ g₃ m₃ rd₃ wr₃ => WP.block_nil ?_
    refine ⟨by rw [rd₃, u₂.rd, u₁.rd], by rw [wr₃, u₂.wr, u₁.wr],
      fun r hr => by rw [g₃, u₂.other r hr, u₁.other r hr], ?_⟩
    rw [m₃, u₂.mem, u₁.mem, u₂.gpr, u₁.gpr, u₁.other .rcx (by decide), sw, sw, hcx,
      Proof.Pbkdf2.MdKeys.writeW_xorRep, hKd hkD, hm, hap _ (by simp [Proof.Hmac.Common.bytesAt_length]),
      padBytes_succ _ _ _ hD, ite_eq_left_of_eq_true _ _ (eq_true hkD)]
  · rw [Cfg.padW, ite_eq_right_of_eq_false _ _ (eq_false (by rw [hcD]; exact hkD))]
    refine Proof.Sha256.X86_64.Stream.wp_store32 (a := P0 + BitVec.ofNat 64 (4 * k)) hst hw
      fun s₃ g₃ m₃ rd₃ wr₃ => WP.block_nil ?_
    refine ⟨rd₃, wr₃, fun r _ => by rw [g₃], ?_⟩
    rw [m₃, hcx, Proof.Pbkdf2.MdKeys.writeW_rep, hm, hap _ (by simp), padBytes_succ _ _ _ hD, ite_eq_right_of_eq_false _ _ (eq_false hkD)]

/-- The first `k` words of the padded key, from the state `u`. -/
theorem padWs_ok (P0 K : Addr) {D : Nat} (c : Byte) (cf : Impl.Ecdsa.Rfc6979.X86_64.Cfg) (hcD : cf.D = D)
    (hD : D % 4 = 0) {n : Nat} (hn : 4 * n + 4 < 2 ^ 64) (hsep : Region.Disjoint ⟨K, D⟩ ⟨P0, 4 * n⟩)
    (hDn : D ≤ 4 * n) :
    ∀ k ≤ n, ∀ u : State, u.gpr .rdi + BitVec.ofNat 64 1792 = P0 → u.gpr .rsp = K →
      (u.gpr .rcx).setWidth 32 = c ++ c ++ c ++ c →
      (∀ j < D / 4, InRegions (u.rd ++ u.wr) (K + BitVec.ofNat 64 (4 * j)) 4) →
      (∀ j < n, InRegions u.wr (P0 + BitVec.ofNat 64 (4 * j)) 4) →
      WP isa (.block ((List.range k).flatMap cf.padW)) u fun u' => u'.rd = u.rd ∧ u'.wr = u.wr ∧
        (∀ r, r ≠ .rax → u'.gpr r = u.gpr r) ∧ u'.mem = writeBytes u.mem P0 (padBytes u.mem K D c (4 * k))
  | 0, _, u, _, _, _, _, _ => WP.of_runBlock ⟨u, rfl, rfl, rfl, fun _ _ => rfl, by simp [padBytes, writeBytes_nil]⟩
  | k + 1, hk, u, hdi, hsp, hcx, hr, hw => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (padWs_ok P0 K c cf hcD hD hn hsep hDn k (by omega) u hdi hsp hcx hr hw)
      fun u₁ ⟨hrd₁, hwr₁, hg₁, hm₁⟩ => ?_
    have hf : Frame [⟨P0, 4 * n⟩] u.mem u₁.mem := by
      rw [hm₁]; exact writeBytes_frame _ _ _ (by
        rw [padBytes_length]
        have := Offset.contains_base P0 (d := 0) (n := 4 * k) (k := 4 * n) (by omega) (by omega)
        rwa [BitVec.add_zero] at this)
    refine WP.mono (padW_ok (t := u) P0 K D c (k := k) hD (by omega) (by rw [hg₁ _ (by decide), hdi])
      (by rw [hg₁ _ (by decide), hsp]) (by rw [hg₁ _ (by decide), hcx])
      (fun hkD => by rw [hrd₁, hwr₁]; exact hr k hkD) (by rw [hwr₁]; exact hw k (by omega)) hm₁
      (fun hkD => bytesAt_frame hf (fun r hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact hsep.sub_left (Offset.sub_base _ (by omega))) (by omega)) cf hcD)
      fun u₂ ⟨hrd₂, hwr₂, hg₂, hm₂⟩ => ⟨hrd₂.trans hrd₁, hwr₂.trans hwr₁,
        fun r hr' => (hg₂ r hr').trans (hg₁ r hr'), by rw [hm₂, show 4 * (k + 1) = 4 * k + 4 by omega]⟩

theorem ipad32_eq : ipad32 = Spec.Hmac.ipad ++ Spec.Hmac.ipad ++ Spec.Hmac.ipad ++ Spec.Hmac.ipad := by decide
theorem opad32_eq : opad32 = Spec.Hmac.opad ++ Spec.Hmac.opad ++ Spec.Hmac.opad ++ Spec.Hmac.opad := by decide

/-- The key `K`: the first `D` bytes of the frame. -/
abbrev keyOf (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) : List Byte :=
  Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 24) P.H.D

/-- `K₀ ⊕ c` at `scratch + sPad`. -/
theorem padBlk_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (c : Byte) :
    WP isa (.block ((cfgOf P).padBlk (c ++ c ++ c ++ c))) t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 1792, P.H.P.B⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 1792) P.H.P.B =
        Spec.Hmac.xorPad (Spec.Hmac.blockKey P.ok.SH.H (keyOf P L t.mem)) c := by
  have hB4 : P.H.P.B % 8 = 0 := by nums
  have h208 := hc.inFr (d := 208) (by omega) (by omega)
  rw [Cfg.padBlk, WP.block_append_iff, WP.block_append_iff]
  have h₁ : WP isa (.block Cfg.scrPtr) t fun u => Ctx L g m₀ u ∧ u.mem = t.mem ∧ u.gpr .rdi = L.scr ∧
      ∀ r, r ≠ .rdi → u.gpr r = t.gpr r := by
    apply WP.of_runBlock
    simp only [Cfg.scrPtr, fScratch, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, ea_stk,
      hc.rsp, Offset.add_add, Nat.reduceAdd, h208, ite_true, Option.map_some, hc.pScr, RegUpd.gpr_setReg_self,
      RegUpd.mem_setReg, Option.some.injEq, exists_eq_left']
    exact ⟨hc.set hL (d := .rdi) (by decide) rfl rfl rfl rfl fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, trivial,
      trivial, fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr⟩
  refine WP.mono h₁ fun u₁ ⟨hc₁, hm₁, hdi₁, hk₁⟩ => ?_
  refine WP.of_syms (Proof.Sha256.X86_64.Stream.wp_mov32i fun u₂ h₂ _ _ => WP.block_nil fun hsy => ?_)
  have hcx : (u₂.gpr .rcx).setWidth 32 = c ++ c ++ c ++ c := by
    rw [h₂.gpr, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
  have hc₂ : Ctx L g m₀ u₂ := hc₁.set hL (d := .rcx) (by decide) h₂.rd h₂.wr h₂.mem hsy h₂.other
  have hdi₂ : u₂.gpr .rdi = L.scr := (h₂.other _ (by decide)).trans hdi₁
  have hsep : Region.Disjoint ⟨L.B + BitVec.ofNat 64 24, P.H.D⟩ ⟨L.scr + BitVec.ofNat 64 1792, 4 * (P.H.P.B / 4)⟩ :=
    hL.stk_scr (by nums) (by nums)
  have hW := padWs_ok (L.scr + BitVec.ofNat 64 1792) (L.B + BitVec.ofNat 64 24) (D := P.H.D) c (cfgOf P) rfl
    (by nums) (n := P.H.P.B / 4) (by nums) hsep (by nums) (P.H.P.B / 4) (Nat.le_refl _) u₂ (by rw [hdi₂])
    hc₂.rsp hcx (fun j hj => by
      rw [Offset.add_add]
      exact ⟨L.FR, by rw [hc₂.rd, hc₂.wr]; simp, Offset.contains _ (by omega) (by have := L.he; nums)
        (by have := hL.nb; have := L.he; omega)⟩)
    (fun j hj => by rw [Offset.add_add]; exact hc₂.inScrW (by nums))
  change WP isa (.block ((List.range (P.H.P.B / 4)).flatMap (cfgOf P).padW)) u₂ _
  refine WP.mono_syms hW fun u₃ ⟨hrd₃, hwr₃, hg₃, hm₃⟩ hsy₃ => ?_
  have hm₂ : u₂.mem = t.mem := h₂.mem.trans hm₁
  have hf : Frame [⟨L.scr + BitVec.ofNat 64 1792, P.H.P.B⟩] t.mem u₃.mem := by
    rw [hm₃, hm₂]; exact writeBytes_frame _ _ _ (by
      rw [padBytes_length]
      have := Offset.contains_base (L.scr + BitVec.ofNat 64 1792) (d := 0) (n := 4 * (P.H.P.B / 4)) (k := P.H.P.B)
        (by omega) (by omega)
      rwa [BitVec.add_zero] at this)
  refine ⟨hc₂.keep hL hrd₃ hwr₃ (hg₃ _ (by decide)) (fun r hr _ => hg₃ r (ne_cs hr (by decide)))
      (by rw [hm₂]; exact hf) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L (by nums)) hsy₃, hf, ?_⟩
  have e4 : 4 * (P.H.P.B / 4) = P.H.P.B := by omega
  rw [e4] at hm₃
  rw [hm₃, hm₂, Proof.Hmac.Generic.Common.bytesAt_writeBytes_self' (padBytes_length _ _ _ _ _) (by nums),
    show P.H.P.B = P.ok.SH.H.blockSize from P.ok.hB.symm, padBytes_eq _ _ _ _ (by rw [P.ok.hB]; nums)]

-- @@BODY@@
end VG.Proof.Ecdsa.Rfc6979.X86_64
