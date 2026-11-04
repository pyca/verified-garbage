module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Hash
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Regs
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Calls
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Copy
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.ICall
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MdStream.AArch64.Common
import VerifiedGarbage.Proof.Pbkdf2.MdKeys
import VerifiedGarbage.Proof.Hmac.Common

/-!
# Deterministic ECDSA on AArch64: one HMAC, through the table

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Hmac.lean`): `HMAC_K(data)`
(`Cfg.hmac`), for the key `K` (of the hash function's output length) in the
frame and `len` bytes of data in the frame or in `scratch` above HMAC's
working space (`DataOk`), written to the frame at `dst`, from the table's
streaming functions, each called indirectly (`tcall_ok`: the table's word,
which `Ctx` says holds the function of `L.G`, whose call an indirect call of
`L.f`'s functions reaches): the states for the key (`init_step`: each set by
`init`, `initCall_ok`, and updated with the padded key, `padBlk_ok` and
`updCall_ok`), the inner state updated with the data (`upd_step`), and the
MAC (`fin_step`: the inner state finalized, `finCall_ok`, the outer one
updated with its digest and finalized, and the digest copied). They change
only HMAC's states and working space, the padded key and what `finalize`
writes (all within the first 2256 bytes of `scratch`), the 16 bytes below
the frame, and `dst` (`hmac_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64
open VG.WriteBytes (writeBytes writeBytes_append writeBytes_nil writeBytes_frame)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (After)

/-- Where the data may be: in the frame below its pointers, or in `scratch`
above HMAC's working space. -/
def DataOk {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (da : Addr) (len : Nat) : Prop :=
  (∃ o, da = L.B + BitVec.ofNat 64 o ∧ 16 ≤ o ∧ o + len ≤ 184) ∨
    (∃ o, da = L.scr + BitVec.ofNat 64 o ∧ 2256 ≤ o ∧ o + len ≤ 8192)

variable {P : RfcHash} {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} {L : Lay dn E} {g : Reg → BitVec 64} {m₀ : Mem}

namespace DataOk

variable {da : Addr} {len : Nat}

theorem low (hd : DataOk L da len) (hL : L.Ok) : Region.Disjoint ⟨L.B, 16⟩ ⟨da, len⟩ := by
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

theorem Ctx.sp16 (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) : 16 ≤ u.sp.toNat := by
  rw [hc.sp, toNat_add_of (by have := hL.nB; omega)]; omega

/-- What a call leaves keeps `Ctx`, if it writes only safe regions and the
16 bytes below the frame. -/
theorem Ctx.after (hL : L.Ok) {u u' : State} (hc : Ctx L g m₀ u) {ws : List Region} (ha : After u ws u')
    (hs : ∀ r ∈ ws, Safe L r) : Ctx L g m₀ u' :=
  hc.keep hL ha.rd ha.wr ha.sp ha.cs ha.frame (hsy := ha.syms) fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact hs r hr
    · simp only [List.mem_singleton] at hr; subst hr
      rw [hc.below_eq]
      exact .inr (.inr (.inl (Region.sub_prefix (by omega))))

/-! ## The table -/

/-- The layout's table is of `P`'s hash function and functions, and its
frame has `P`'s bytes at its top. -/
def TabL (P : RfcHash) {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) : Prop :=
  L.G = P.H.stream ∧ L.f = P.f ∧ L.e = P.e

/-- The table's words, as on entry. -/
theorem Ctx.tabWord (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {o : Nat} (ho : o + 8 ≤ 40) :
    t.mem.readW (L.tab + BitVec.ofNat 64 o) 64 = m₀.readW (L.tab + BitVec.ofNat 64 o) 64 :=
  hc.frame.readW (r := L.TAB) (Offset.contains_base _ ho (by have := hL.nt; omega)) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.to
    · exact hL.tc
    · exact hL.tk) (by decide)

/-- The table's address into `x16`. -/
theorem tblk1_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block [.ldrSp .x16 fTab]) t (Upd L g m₀ t .x16 L.tab) := by
  have h232 := hc.inFr (d := 232) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [fTab, runBlock_cons, runStep_some, runBlock_nil, exec, State.load, BitVec.setWidth_eq, hc.sp, Offset.add_add, Nat.reduceAdd, Nat.reduceMod, Nat.reduceLT, and_self,
    h232, ite_true, Option.map_some, read8, hc.pTab, Option.some.injEq, exists_eq_left']
  exact ⟨hc.set hL (d := .x16) (by decide) rfl rfl rfl rfl (fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr) rfl, rfl,
    by rw [RegUpd.gpr_write_self]; exact BitVec.setWidth_eq _, fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr⟩

/-- The table's word `j` into `x16`, from its address there. -/
theorem tblk2_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (h16 : t.gpr .x16 = L.tab) {j : Nat}
    (hj : 8 * j + 8 ≤ 40) :
    WP isa (.block [.ldr .x .x16 .x16 (8 * j)]) t
      (Upd L g m₀ t .x16 (m₀.readW (L.tab + BitVec.ofNat 64 (8 * j)) 64)) := by
  have ht := hc.inTab hL (o := 8 * j) hj
  have hj' : 8 * j < 4096 * 8 := by omega
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, Size.bits, Size.bytes,
    BitVec.setWidth_eq, h16, Nat.mul_mod_right, hj', and_self, ite_true, Option.bind_some, ht, Option.map_some,
    read8, hc.tabWord hL hj, Option.some.injEq, exists_eq_left']
  exact ⟨hc.set hL (d := .x16) (by decide) rfl rfl rfl rfl (fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr) rfl, rfl,
    by rw [RegUpd.gpr_write_self]; exact BitVec.setWidth_eq _, fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr⟩

/-- The indirect call of the table's function `j`, at the address its word
`j` holds, of `n`. -/
theorem tcall_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {j : Nat} (hj : 8 * j + 8 ≤ 40)
    {n : String} {c : Prog isa} {ts : List (String × Prog isa)}
    (hw : m₀.readW (L.tab + BitVec.ofNat 64 (8 * j)) 64 = t.syms n)
    (hf : ts.find? (fun q => t.syms q.1 == t.syms n) = some (n, c)) {Q : State → Prop}
    (h : ∀ t', Ctx L g m₀ t' → t'.mem = t.mem → (∀ r, r ≠ .x16 → t'.gpr r = t.gpr r) → t'.syms = t.syms →
      WP isa (.call n c) t' Q) :
    WP isa (Cfg.tcall j ts) t Q := by
  unfold Cfg.tcall
  refine WP.seq (WP.mono_syms (tblk1_ok hL hc) fun t₁ h₁ hs₁ =>
    WP.seq (WP.mono_syms (tblk2_ok hL h₁.ctx h₁.val hj) fun t' h₂ hsy => ?_))
  refine WP.icalls_of_call (a := t.syms n) (by simp only [icall, h₂.val, hw]) ?_
    (h t' h₂.ctx (h₂.mem.trans h₁.mem) (fun r hr => (h₂.keep r hr).trans (h₁.keep r hr)) (hsy.trans hs₁))
  show ts.find? (fun q => isa.fnAddr t' q.1 == t.syms n) = _
  simp only [isa]; rw [hsy, hs₁]; exact hf

/-! ## The streaming `init` -/

/-- The writes of a call, within HMAC's working space and the stack below the frame. -/
theorem scr_work {e k : Nat} (h : e + k ≤ 2256) : Region.Sub ⟨L.scr + BitVec.ofNat 64 e, k⟩ ⟨L.scr, 2256⟩ :=
  Offset.sub_base _ h

theorem scr_safe {r : Region} (h : Region.Sub r ⟨L.scr, 2256⟩) : Safe L r :=
  .inr (.inl (sub_trans h (Region.sub_prefix (by omega))))

/-- The call of `init` of the state at `scratch + o`, in `x0`. -/
theorem initRaw_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {o : Nat} (ho : o + 192 ≤ 384)
    (h0 : u.gpr .x0 = L.scr + BitVec.ofNat 64 o) :
    WP isa (.call P.H.stream.initN P.H.stream.initC) u fun u' => Ctx L g m₀ u' ∧
      Frame [⟨L.scr + BitVec.ofNat 64 o, P.H.S⟩, ⟨L.B, 16⟩] u.mem u'.mem ∧
      P.ok.SH.Repr u'.mem (L.scr + BitVec.ofNat 64 o) [] := by
  refine Proof.Pbkdf2.Md.AArch64.Calls.init_call P.ok.stream h0
    (hc.coversW fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨L.SCR, by simp, within_off _ (by anums)⟩) fun u' af hr => ?_
  have hsafe : Region.Sub ⟨L.scr + BitVec.ofNat 64 o, P.H.stream.S⟩ ⟨L.scr, 2256⟩ := scr_work (by anums)
  refine ⟨hc.after hL af fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact scr_safe hsafe, ?_, hr⟩
  exact af.frame.sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., sub_refl _⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨L.B, 16⟩, by simp, by rw [hc.below_eq]; exact sub_refl _⟩

/-- `init` of the state at `scratch + o`: it represents the empty message. -/
theorem initCall_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) {o : Nat} (ho : o + 192 ≤ 384) :
    WP isa ((cfgOf P).initCall o) t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 o, P.H.S⟩, ⟨L.B, 16⟩] t.mem u.mem ∧
      P.ok.SH.Repr u.mem (L.scr + BitVec.ofNat 64 o) [] := by
  refine WP.seq (WP.mono (scr_ok hL hc (d := .x0) (by decide) (a := o) (by omega)) fun u h => ?_)
  have hok := h.ctx.tabOk
  have htm := h.ctx.tabMem
  rw [hT.1, hT.2.1] at hok
  rw [hT.1] at htm
  refine tcall_ok hL h.ctx (j := 0) (by decide) (n := P.H.stream.initN) (c := P.H.stream.initC) htm.1 hok.i
    fun u' hc' hm' hk' _ => ?_
  refine WP.mono (initRaw_ok hL hc' ho ((hk' _ (by decide)).trans h.val)) fun v ⟨hcv, hf, hr⟩ => ?_
  rw [hm', h.mem] at hf
  exact ⟨hcv, hf, hr⟩

/-! ## The streaming `update` -/

/-- The arguments of `update`: the state at `scratch + o` holding `cnt`
bytes, the data, its length and the working space. -/
theorem updArgs_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {o cnt : Nat} (ho : o < 4096)
    {dataA : List Instr} {da : Addr} {len : Nat}
    (hdA : ∀ u, Ctx L g m₀ u → WP isa (.block dataA) u (Upd L g m₀ u .x2 da)) (hcnt : cnt < 2 ^ 16)
    (hlen : len < 2 ^ 16) :
    WP isa (.block (Cfg.updArgs o cnt dataA len)) u fun u' => Ctx L g m₀ u' ∧
      u'.mem = u.mem ∧ u'.gpr .x0 = L.scr + BitVec.ofNat 64 o ∧ u'.gpr .x1 = BitVec.ofNat 64 cnt ∧
      u'.gpr .x2 = da ∧ u'.gpr .x3 = BitVec.ofNat 64 len ∧ u'.gpr .x4 = L.scr + BitVec.ofNat 64 384 := by
  rw [Cfg.updArgs, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (scr_ok hL hc (d := .x0) (by decide) (a := o) ho) fun u₁ h₁ => ?_
  refine WP.mono (movz_ok hL h₁.ctx (d := .x1) (by decide) hcnt) fun u₂ h₂ => ?_
  refine WP.mono (hdA u₂ h₂.ctx) fun u₃ h₃ => ?_
  refine WP.mono (movz_ok hL h₃.ctx (d := .x3) (by decide) hlen) fun u₄ h₄ => ?_
  refine WP.mono (scr_ok hL h₄.ctx (d := .x4) (by decide) (a := 384) (by decide)) fun u₅ h₅ => ?_
  refine ⟨h₅.ctx, by rw [h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem], ?_, ?_, ?_, ?_, h₅.val⟩
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.keep _ (by decide), h₁.val]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.val]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.val]
  · rw [h₅.keep _ (by decide), h₄.val]

/-- Where data `update` reads may be: within a buffer or the frame, and
apart from the state it updates, the working space and the stack below the
frame. -/
structure UpdData (P : RfcHash) {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (o : Nat) (da : Addr)
    (len : Nat) : Prop where
  cov : ∃ R ∈ [L.D, L.DG, L.FR, L.OUT, L.SCR], Within ⟨da, len⟩ R
  st : Region.Disjoint ⟨da, len⟩ ⟨L.scr + BitVec.ofNat 64 o, P.H.S⟩
  wk : Region.Disjoint ⟨da, len⟩ ⟨L.scr + BitVec.ofNat 64 384, P.ok.stream.Wb⟩
  low : Region.Disjoint ⟨L.B, 16⟩ ⟨da, len⟩

/-- The arguments of `update`, as the streaming proofs state them. -/
theorem updArgsOf (hL : L.Ok) {w : State} (hc : Ctx L g m₀ w) {o : Nat} (ho : o + 192 ≤ 384) {da : Addr}
    {len : Nat} (hd : UpdData P L o da len) (hlen : len < 2 ^ 16) (h0 : w.gpr .x0 = L.scr + BitVec.ofNat 64 o)
    (h2 : w.gpr .x2 = da) (h3 : w.gpr .x3 = BitVec.ofNat 64 len) (h4 : w.gpr .x4 = L.scr + BitVec.ofNat 64 384) :
    Proof.Pbkdf2.Md.AArch64.Calls.UpdArgs P.ok.stream w (L.scr + BitVec.ofNat 64 o) da
      (L.scr + BitVec.ofNat 64 384) len := by
  have hsp : below w.sp 16 = ⟨L.B, 16⟩ := hc.below_eq
  exact { x0 := h0, x2 := h2
          x3 := by rw [h3, BitVec.toNat_ofNat]; omega
          x4 := h4
          cd := hc.covers fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact hd.cov
          cw := hc.coversW fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl <;> exact ⟨L.SCR, by simp, within_off _ (by anums)⟩
          st_sc := Offset.disjoint _ (by anums) (by anums) (by anums)
          d_st := hd.st
          d_sc := hd.wk
          sp16 := hc.sp16 hL
          stk_st := by rw [hsp]; exact hL.low_scr (by anums)
          stk_d := by rw [hsp]; exact hd.low
          stk_sc := by rw [hsp]; exact hL.low_scr (by anums) }

/-- The call of `update`, with its arguments. -/
theorem updRaw_ok (hL : L.Ok) {w : State} (hc : Ctx L g m₀ w) {o : Nat} (ho : o + 192 ≤ 384) {da : Addr}
    {len : Nat} (a : Proof.Pbkdf2.Md.AArch64.Calls.UpdArgs P.ok.stream w (L.scr + BitVec.ofNat 64 o) da
      (L.scr + BitVec.ofNat 64 384) len) {cnt : Nat} (h1 : w.gpr .x1 = BitVec.ofNat 64 cnt) :
    WP isa (.call P.H.stream.updN P.H.stream.updC) w fun u => Ctx L g m₀ u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 o, P.H.S⟩, ⟨L.scr + BitVec.ofNat 64 384, P.ok.stream.Wb⟩, ⟨L.B, 16⟩]
        w.mem u.mem ∧ ∀ msg : List Byte, P.ok.SH.Repr w.mem (L.scr + BitVec.ofNat 64 o) msg → msg.length = cnt →
      P.ok.SH.Repr u.mem (L.scr + BitVec.ofNat 64 o) (msg ++ Spec.Sha256.bytesAt w.mem da len) := by
  refine Proof.Pbkdf2.Md.AArch64.Calls.upd_call P.ok.stream a fun w' af hrr => ?_
  have hws : ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 o, P.H.stream.S⟩ : Region),
      ⟨L.scr + BitVec.ofNat 64 384, P.ok.stream.Wb⟩], Region.Sub r ⟨L.scr, 2256⟩ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> exact scr_work (by anums)
  refine ⟨hc.after hL af fun r hr => scr_safe (hws r hr), ?_, fun msg hr hml => hrr msg hr (by rw [h1, hml])⟩
  exact af.frame.sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., sub_refl _⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), sub_refl _⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨L.B, 16⟩, by simp, by rw [hc.below_eq]; exact sub_refl _⟩

/-- `update` of the state at `scratch + o`, holding `cnt` bytes, with `len`
bytes at `da`. -/
theorem updCall_gen (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) {o cnt : Nat} (ho : o + 192 ≤ 384)
    {dataA : List Instr} {da : Addr} {len : Nat}
    (hdA : ∀ u, Ctx L g m₀ u → WP isa (.block dataA) u (Upd L g m₀ u .x2 da)) (hd : UpdData P L o da len)
    (hcnt : cnt < 2 ^ 16) (hlen : len < 2 ^ 16) :
    WP isa ((cfgOf P).updCall o cnt dataA len) t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 o, P.H.S⟩, ⟨L.scr + BitVec.ofNat 64 384, P.ok.stream.Wb⟩, ⟨L.B, 16⟩]
        t.mem u.mem ∧ ∀ msg : List Byte, P.ok.SH.Repr t.mem (L.scr + BitVec.ofNat 64 o) msg → msg.length = cnt →
      P.ok.SH.Repr u.mem (L.scr + BitVec.ofNat 64 o) (msg ++ Spec.Sha256.bytesAt t.mem da len) := by
  refine WP.seq (WP.mono (updArgs_ok hL hc (o := o) (by omega) hdA hcnt hlen)
    fun w ⟨hcw, hmw, h0, h1, h2, h3, h4⟩ => ?_)
  have hok := hcw.tabOk
  have htm := hcw.tabMem
  rw [hT.1, hT.2.1] at hok
  rw [hT.1] at htm
  refine tcall_ok hL hcw (j := 1) (by decide) (n := P.H.stream.updN) (c := P.H.stream.updC) htm.2.1 hok.u
    fun w' hc' hm' hk' _ => ?_
  have a := updArgsOf hL hc' ho hd hlen ((hk' _ (by decide)).trans h0) ((hk' _ (by decide)).trans h2)
    ((hk' _ (by decide)).trans h3) ((hk' _ (by decide)).trans h4)
  refine WP.mono (updRaw_ok hL hc' ho a ((hk' _ (by decide)).trans h1)) fun u ⟨hcu, hf, hr⟩ => ?_
  rw [hm', hmw] at hf hr
  exact ⟨hcu, hf, hr⟩

/-- `update` of the state at `scratch + o`, holding `cnt` bytes, with `len`
bytes at `da`: the state represents them too. -/
theorem updCall_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) {o cnt : Nat} (ho : o + 192 ≤ 384)
    {dataA : List Instr} {da : Addr} {len : Nat}
    (hdA : ∀ u, Ctx L g m₀ u → WP isa (.block dataA) u (Upd L g m₀ u .x2 da)) (hd : UpdData P L o da len)
    (hcnt : cnt < 2 ^ 16) (hlen : len < 2 ^ 16)
    {msg : List Byte} (hr : P.ok.SH.Repr t.mem (L.scr + BitVec.ofNat 64 o) msg) (hml : msg.length = cnt) :
    WP isa ((cfgOf P).updCall o cnt dataA len) t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 o, P.H.S⟩, ⟨L.scr + BitVec.ofNat 64 384, P.ok.stream.Wb⟩, ⟨L.B, 16⟩]
        t.mem u.mem ∧
      P.ok.SH.Repr u.mem (L.scr + BitVec.ofNat 64 o) (msg ++ Spec.Sha256.bytesAt t.mem da len) :=
  WP.mono (updCall_gen hL hT hc ho hdA hd hcnt hlen) fun _ ⟨a, b, c⟩ => ⟨a, b, c msg hr hml⟩

/-! ## The streaming `finalize` -/

/-- The arguments of `finalize`, as the streaming proofs state them. -/
theorem finArgsOf (hL : L.Ok) {w : State} (hc : Ctx L g m₀ w) {o : Nat} (ho : o + 192 ≤ 384)
    (h0 : w.gpr .x0 = L.scr + BitVec.ofNat 64 o) (h2 : w.gpr .x2 = L.scr + BitVec.ofNat 64 1920)
    (h3 : w.gpr .x3 = L.scr + BitVec.ofNat 64 384) :
    Proof.Pbkdf2.Md.AArch64.Calls.FinArgs P.ok.stream w (L.scr + BitVec.ofNat 64 o)
      (L.scr + BitVec.ofNat 64 1920) (L.scr + BitVec.ofNat 64 384) := by
  have hsp : below w.sp 16 = ⟨L.B, 16⟩ := hc.below_eq
  exact { x0 := h0, x2 := h2, x3 := h3
          cw := hc.coversW fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl <;> exact ⟨L.SCR, by simp, within_off _ (by anums)⟩
          st_o := Offset.disjoint _ (by anums) (by anums) (by anums)
          st_sc := Offset.disjoint _ (by anums) (by anums) (by anums)
          o_sc := Offset.disjoint _ (by anums) (by anums) (by anums)
          sp16 := hc.sp16 hL
          stk_st := by rw [hsp]; exact hL.low_scr (by anums)
          stk_o := by rw [hsp]; exact hL.low_scr (by anums)
          stk_sc := by rw [hsp]; exact hL.low_scr (by anums) }

/-- The call of `finalize`, with its arguments. -/
theorem finRaw_ok (hL : L.Ok) {w : State} (hc : Ctx L g m₀ w) {o : Nat} (ho : o + 192 ≤ 384)
    (a : Proof.Pbkdf2.Md.AArch64.Calls.FinArgs P.ok.stream w (L.scr + BitVec.ofNat 64 o)
      (L.scr + BitVec.ofNat 64 1920) (L.scr + BitVec.ofNat 64 384)) {cnt : Nat} (hcnt : cnt < 2 ^ 16)
    (h1 : w.gpr .x1 = BitVec.ofNat 64 cnt) :
    WP isa (.call P.H.stream.finN P.H.stream.finC) w fun u => Ctx L g m₀ u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 o, P.H.S⟩, ⟨L.scr + BitVec.ofNat 64 1920, P.H.stream.F⟩,
        ⟨L.scr + BitVec.ofNat 64 384, P.ok.stream.Wb⟩, ⟨L.B, 16⟩] w.mem u.mem ∧
      ∀ msg : List Byte, P.ok.SH.Repr w.mem (L.scr + BitVec.ofNat 64 o) msg → msg.length = cnt →
      (Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 1920) P.H.stream.F).take P.H.D = P.ok.SH.H.hash msg := by
  refine Proof.Pbkdf2.Md.AArch64.Calls.fin_call P.ok.stream a fun w' af hrr => ?_
  have hws : ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 o, P.H.stream.S⟩ : Region),
      ⟨L.scr + BitVec.ofNat 64 1920, P.H.stream.F⟩, ⟨L.scr + BitVec.ofNat 64 384, P.ok.stream.Wb⟩],
      Region.Sub r ⟨L.scr, 2256⟩ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> exact scr_work (by anums)
  refine ⟨hc.after hL af fun r hr => scr_safe (hws r hr), ?_,
    fun msg hr hml => hrr msg hr (by rw [hml]; omega) (by rw [h1, hml])⟩
  exact af.frame.sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., sub_refl _⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), sub_refl _⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), sub_refl _⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨L.B, 16⟩, by simp, by rw [hc.below_eq]; exact sub_refl _⟩

/-- The arguments of `finalize`: the state at `scratch + o` holding `cnt`
bytes, the output and the working space. -/
theorem finArgs_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {o cnt : Nat} (ho : o + 192 ≤ 384)
    (hcnt : cnt < 2 ^ 16) :
    WP isa (.block (Cfg.finArgs o cnt)) t fun w => Ctx L g m₀ w ∧ w.mem = t.mem ∧
      w.gpr .x0 = L.scr + BitVec.ofNat 64 o ∧ w.gpr .x1 = BitVec.ofNat 64 cnt ∧
      w.gpr .x2 = L.scr + BitVec.ofNat 64 1920 ∧ w.gpr .x3 = L.scr + BitVec.ofNat 64 384 := by
  rw [Cfg.finArgs, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (scr_ok hL hc (d := .x0) (by decide) (a := o) (by omega)) fun u₁ h₁ => ?_
  refine WP.mono (movz_ok hL h₁.ctx (d := .x1) (by decide) hcnt) fun u₂ h₂ => ?_
  refine WP.mono (scr_ok hL h₂.ctx (d := .x2) (by decide) (a := 1920) (by decide)) fun u₃ h₃ => ?_
  refine WP.mono (scr_ok hL h₃.ctx (d := .x3) (by decide) (a := 384) (by decide)) fun u₄ h₄ => ?_
  refine ⟨h₄.ctx, by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem], ?_, ?_, ?_, h₄.val⟩
  · rw [h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.keep _ (by decide), h₁.val]
  · rw [h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.val]
  · rw [h₄.keep _ (by decide), h₃.val]

/-- `finalize` of the state at `scratch + o`, holding `cnt` bytes, into
`scratch + sTmp`. -/
theorem finCall_gen (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) {o cnt : Nat} (ho : o + 192 ≤ 384)
    (hcnt : cnt < 2 ^ 16) :
    WP isa ((cfgOf P).finCall o cnt) t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 o, P.H.S⟩, ⟨L.scr + BitVec.ofNat 64 1920, P.H.stream.F⟩,
        ⟨L.scr + BitVec.ofNat 64 384, P.ok.stream.Wb⟩, ⟨L.B, 16⟩] t.mem u.mem ∧
      ∀ msg : List Byte, P.ok.SH.Repr t.mem (L.scr + BitVec.ofNat 64 o) msg → msg.length = cnt →
      (Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 1920) P.H.stream.F).take P.H.D = P.ok.SH.H.hash msg := by
  refine WP.seq (WP.mono (finArgs_ok hL hc ho hcnt) fun w ⟨hcw, hmw, h0, h1, h2, h3⟩ => ?_)
  have hok := hcw.tabOk
  have htm := hcw.tabMem
  rw [hT.1, hT.2.1] at hok
  rw [hT.1] at htm
  refine tcall_ok hL hcw (j := 2) (by decide) (n := P.H.stream.finN) (c := P.H.stream.finC) htm.2.2 hok.f
    fun w' hc' hm' hk' _ => ?_
  have a := finArgsOf (P := P) hL hc' ho ((hk' _ (by decide)).trans h0) ((hk' _ (by decide)).trans h2)
    ((hk' _ (by decide)).trans h3)
  refine WP.mono (finRaw_ok hL hc' ho a hcnt ((hk' _ (by decide)).trans h1)) fun u ⟨hcu, hf, hr⟩ => ?_
  rw [hm', hmw] at hf hr
  exact ⟨hcu, hf, hr⟩

/-- `finalize` of the state at `scratch + o`, holding `cnt` bytes, into
`scratch + sTmp`: its first `D` bytes are the digest. -/
theorem finCall_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) {o cnt : Nat} (ho : o + 192 ≤ 384)
    (hcnt : cnt < 2 ^ 16) {msg : List Byte} (hr : P.ok.SH.Repr t.mem (L.scr + BitVec.ofNat 64 o) msg)
    (hml : msg.length = cnt) :
    WP isa ((cfgOf P).finCall o cnt) t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 o, P.H.S⟩, ⟨L.scr + BitVec.ofNat 64 1920, P.H.stream.F⟩,
        ⟨L.scr + BitVec.ofNat 64 384, P.ok.stream.Wb⟩, ⟨L.B, 16⟩] t.mem u.mem ∧
      (Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 1920) P.H.stream.F).take P.H.D = P.ok.SH.H.hash msg :=
  WP.mono (finCall_gen hL hT hc ho hcnt) fun _ ⟨a, b, c⟩ => ⟨a, b, c msg hr hml⟩

/-- `scratch` in `x9`. -/
theorem scrPtr_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.scrPtr) t (Upd L g m₀ t .x9 L.scr) := by
  have h200 := hc.inFr (d := 200) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [Cfg.scrPtr, fScratch, runBlock_cons, runStep_some, runBlock_nil, exec, State.load,
    BitVec.setWidth_eq, hc.sp, Offset.add_add, Nat.reduceAdd, Nat.reduceMod, Nat.reduceLT, and_self,
    h200, ite_true, Option.map_some, read8, hc.pScr, Option.some.injEq, exists_eq_left']
  exact ⟨hc.set hL (d := .x9) (by decide) rfl rfl rfl rfl (fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr) rfl, rfl,
    by rw [RegUpd.gpr_write_self]; exact BitVec.setWidth_eq _, fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr⟩

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

/-- `eor` of two 32-bit registers. -/
theorem wp_eor32 {is : List Instr} {s : State} {Q : State → Prop} {d n m : Reg}
    (k : ∀ s', Proof.MdStream.AArch64.Upd s s' d (((s.gpr n).setWidth 32 ^^^ (s.gpr m).setWidth 32).setWidth 64) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.logic .eor .w d n m :: is)) s Q :=
  Proof.MdStream.AArch64.WP.cons (s' := s.write .w d ((s.gpr n).setWidth 32 ^^^ (s.gpr m).setWidth 32)) rfl
    (k _ (Proof.MdStream.AArch64.Upd.write _ _ _ _))

/-- Word `k` of the padded key, after `4 k` of its bytes. -/
theorem padW_ok {t : State} (P0 K : Addr) (D : Nat) (c : Byte) {k : Nat} (hD : D % 4 = 0)
    (hk : 4 * k + 4 < 2 ^ 64)
    (hkB : 4 * k < 1792) {u : State} (h9 : u.gpr .x9 + BitVec.ofNat 64 1792 = P0) (h15 : u.gpr .x15 = K)
    (h10 : (u.gpr .x10).setWidth 32 = c ++ c ++ c ++ c)
    (hrK : k < D / 4 → InRegions (u.rd ++ u.wr) (K + BitVec.ofNat 64 (4 * k)) 4)
    (hw : InRegions u.wr (P0 + BitVec.ofNat 64 (4 * k)) 4)
    (hm : u.mem = writeBytes t.mem P0 (padBytes t.mem K D c (4 * k)))
    (hKd : k < D / 4 → Spec.Sha256.bytesAt u.mem (K + BitVec.ofNat 64 (4 * k)) 4 =
      Spec.Sha256.bytesAt t.mem (K + BitVec.ofNat 64 (4 * k)) 4)
    (cf : Impl.Ecdsa.Rfc6979.AArch64.Cfg) (hcD : cf.D = D) :
    WP isa (.block (cf.padW k)) u fun u' => u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧
      (∀ r, r ≠ .x11 → u'.gpr r = u.gpr r) ∧ u'.mem = writeBytes t.mem P0 (padBytes t.mem K D c (4 * k + 4)) := by
  have hl := padBytes_length t.mem K D c (4 * k)
  have hap : ∀ ys : List Byte, ys.length = 4 →
      writeBytes (writeBytes t.mem P0 (padBytes t.mem K D c (4 * k))) (P0 + BitVec.ofNat 64 (4 * k)) ys =
        writeBytes t.mem P0 (padBytes t.mem K D c (4 * k) ++ ys) := fun ys hys => by
    have := writeBytes_append t.mem P0 (padBytes t.mem K D c (4 * k)) ys (by rw [hl, hys]; omega)
    rwa [hl] at this
  have hst : u.gpr .x9 + BitVec.ofNat 64 (sPad + 4 * k) = P0 + BitVec.ofNat 64 (4 * k) := by
    rw [← h9, Offset.add_add]; rfl
  have ho : (sPad + 4 * k) % 4 = 0 ∧ sPad + 4 * k < 4096 * 4 := ⟨by unfold sPad; omega, by unfold sPad; omega⟩
  have sw : ∀ x : BitVec 32, (x.setWidth 64).setWidth 32 = x := fun x => by
    rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
  by_cases hkD : k < D / 4
  · rw [Cfg.padW, ite_eq_left_of_eq_true _ _ (eq_true (by rw [hcD]; exact hkD))]
    have hKo : (fK + 4 * k) % 4 = 0 ∧ fK + 4 * k < 4096 * 4 := ⟨by unfold fK; omega, by unfold fK; omega⟩
    refine Proof.MdStream.AArch64.wp_ldr32 hKo (a := K + BitVec.ofNat 64 (4 * k))
      (by rw [h15, fK, Nat.zero_add]) (hrK hkD) fun s₁ u₁ => ?_
    refine wp_eor32 fun s₂ u₂ => ?_
    refine Proof.MdStream.AArch64.wp_str32 ho (a := P0 + BitVec.ofNat 64 (4 * k))
      (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hst])
      (by rw [u₂.wr, u₁.wr]; exact hw) fun s₃ m₃ => WP.block_nil ?_
    refine ⟨by rw [m₃.rd, u₂.rd, u₁.rd], by rw [m₃.wr, u₂.wr, u₁.wr], by rw [m₃.sp, u₂.sp, u₁.sp],
      fun r hr => by rw [m₃.gpr, u₂.other r hr, u₁.other r hr], ?_⟩
    rw [m₃.mem, u₂.mem, u₁.mem, u₂.gpr, u₁.gpr, u₁.other .x10 (by decide), sw, sw, h10,
      Proof.Pbkdf2.MdKeys.writeW_xorRep, hKd hkD, hm, hap _ (by simp [Proof.Hmac.Common.bytesAt_length]),
      padBytes_succ _ _ _ hD, ite_eq_left_of_eq_true _ _ (eq_true hkD)]
  · rw [Cfg.padW, ite_eq_right_of_eq_false _ _ (eq_false (by rw [hcD]; exact hkD))]
    refine Proof.MdStream.AArch64.wp_str32 ho (a := P0 + BitVec.ofNat 64 (4 * k)) hst hw
      fun s₃ m₃ => WP.block_nil ?_
    refine ⟨m₃.rd, m₃.wr, m₃.sp, fun r _ => by rw [m₃.gpr], ?_⟩
    rw [m₃.mem, h10, Proof.Pbkdf2.MdKeys.writeW_rep, hm, hap _ (by simp), padBytes_succ _ _ _ hD,
      ite_eq_right_of_eq_false _ _ (eq_false hkD)]

/-- The first `k` words of the padded key, from the state `u`. -/
theorem padWs_ok (P0 K : Addr) {D : Nat} (c : Byte) (cf : Impl.Ecdsa.Rfc6979.AArch64.Cfg) (hcD : cf.D = D)
    (hD : D % 4 = 0) {n : Nat} (hn : 4 * n + 4 < 2 ^ 64) (hn' : 4 * n ≤ 1792)
    (hsep : Region.Disjoint ⟨K, D⟩ ⟨P0, 4 * n⟩) (hDn : D ≤ 4 * n) :
    ∀ k ≤ n, ∀ u : State, u.gpr .x9 + BitVec.ofNat 64 1792 = P0 → u.gpr .x15 = K →
      (u.gpr .x10).setWidth 32 = c ++ c ++ c ++ c →
      (∀ j < D / 4, InRegions (u.rd ++ u.wr) (K + BitVec.ofNat 64 (4 * j)) 4) →
      (∀ j < n, InRegions u.wr (P0 + BitVec.ofNat 64 (4 * j)) 4) →
      WP isa (.block ((List.range k).flatMap cf.padW)) u fun u' => u'.rd = u.rd ∧ u'.wr = u.wr ∧
        u'.sp = u.sp ∧ (∀ r, r ≠ .x11 → u'.gpr r = u.gpr r) ∧
        u'.mem = writeBytes u.mem P0 (padBytes u.mem K D c (4 * k))
  | 0, _, u, _, _, _, _, _ => WP.of_runBlock ⟨u, rfl, rfl, rfl, rfl, fun _ _ => rfl, by simp [padBytes, writeBytes_nil]⟩
  | k + 1, hk, u, h9, h15, h10, hr, hw => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (padWs_ok P0 K c cf hcD hD hn hn' hsep hDn k (by omega) u h9 h15 h10 hr hw)
      fun u₁ ⟨hrd₁, hwr₁, hsp₁, hg₁, hm₁⟩ => ?_
    have hf : Frame [⟨P0, 4 * n⟩] u.mem u₁.mem := by
      rw [hm₁]; exact writeBytes_frame _ _ _ (by
        rw [padBytes_length]
        have := Offset.contains_base P0 (d := 0) (n := 4 * k) (k := 4 * n) (by omega) (by omega)
        rwa [BitVec.add_zero] at this)
    refine WP.mono (padW_ok (t := u) P0 K D c (k := k) hD (by omega) (by omega)
      (by rw [hg₁ _ (by decide), h9]) (by rw [hg₁ _ (by decide), h15]) (by rw [hg₁ _ (by decide), h10])
      (fun hkD => by rw [hrd₁, hwr₁]; exact hr k hkD) (by rw [hwr₁]; exact hw k (by omega)) hm₁
      (fun hkD => bytesAt_frame hf (fun r hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact hsep.sub_left (Offset.sub_base _ (by omega))) (by omega)) cf hcD)
      fun u₂ ⟨hrd₂, hwr₂, hsp₂, hg₂, hm₂⟩ => ⟨hrd₂.trans hrd₁, hwr₂.trans hwr₁, hsp₂.trans hsp₁,
        fun r hr' => (hg₂ r hr').trans (hg₁ r hr'), by rw [hm₂, show 4 * (k + 1) = 4 * k + 4 by omega]⟩

theorem ipad32_eq : ipad32 = Spec.Hmac.ipad ++ Spec.Hmac.ipad ++ Spec.Hmac.ipad ++ Spec.Hmac.ipad := by decide
theorem opad32_eq : opad32 = Spec.Hmac.opad ++ Spec.Hmac.opad ++ Spec.Hmac.opad ++ Spec.Hmac.opad := by decide

/-- The 64-bit value `movz` then `movk` (of the high half) build of a
32-bit constant `x`, from any value `v`. -/
def movzkV (x : BitVec 32) : BitVec 64 :=
  ((x.extractLsb' 0 16).setWidth 64 <<< (16 * 0) &&& ~~~((0xFFFF : BitVec 64) <<< (16 * 1))) |||
    ((x.extractLsb' 16 16).setWidth 64 <<< (16 * 1))

theorem movzk_ipad : (movzkV ipad32).setWidth 32 = Spec.Hmac.ipad ++ Spec.Hmac.ipad ++ Spec.Hmac.ipad ++ Spec.Hmac.ipad := by
  decide
theorem movzk_opad : (movzkV opad32).setWidth 32 = Spec.Hmac.opad ++ Spec.Hmac.opad ++ Spec.Hmac.opad ++ Spec.Hmac.opad := by
  decide

/-- The key `K`: the first `D` bytes of the frame. -/
abbrev keyOf (P : RfcHash) {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (m : Mem) : List Byte :=
  Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 16) P.H.D

/-- The frame in `x15` and the pad in `x10`. -/
theorem padHead_ok {t : State} (x : BitVec 32) :
    WP isa (.block [.addSp .x15 0, .movz .x .x10 (x.extractLsb' 0 16) 0, .movk .x .x10 (x.extractLsb' 16 16) 1]) t
      fun u => u.rd = t.rd ∧ u.wr = t.wr ∧ u.sp = t.sp ∧ u.mem = t.mem ∧ u.syms = t.syms ∧
        u.gpr .x15 = t.sp ∧ u.gpr .x10 = movzkV x ∧ ∀ r, r ≠ .x10 → r ≠ .x15 → u.gpr r = t.gpr r := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits, BitVec.add_zero,
    Option.some.injEq, exists_eq_left', show (0 : Nat) < 4096 by decide, ite_true,
    show 16 * 0 < 64 by decide, show 16 * 1 < 64 by decide]
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, fun r h₁ h₂ => ?_⟩
  · rw [RegUpd.gpr_write_of_ne _ _ _ (by decide), RegUpd.gpr_write_of_ne _ _ _ (by decide),
      RegUpd.gpr_write_self, BitVec.setWidth_eq]
  · rw [RegUpd.gpr_write_self, RegUpd.gpr_write_self, BitVec.setWidth_eq, BitVec.setWidth_eq, BitVec.setWidth_eq]
    rfl
  · rw [RegUpd.gpr_write_of_ne _ _ _ h₁, RegUpd.gpr_write_of_ne _ _ _ h₁, RegUpd.gpr_write_of_ne _ _ _ h₂]


/-- `K₀ ⊕ c` at `scratch + sPad`, for the pad `x`, `c` in each byte. -/
theorem padBlk_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (x : BitVec 32) (c : Byte)
    (hx : (movzkV x).setWidth 32 = c ++ c ++ c ++ c) :
    WP isa (.block ((cfgOf P).padBlk x)) t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 1792, P.H.P.B⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 1792) P.H.P.B =
        Spec.Hmac.xorPad (Spec.Hmac.blockKey P.ok.SH.H (keyOf P L t.mem)) c := by
  have hB4 : P.H.P.B % 8 = 0 := by anums
  rw [Cfg.padBlk, Cfg.padBody, WP.block_append_iff]
  refine WP.mono (scrPtr_ok hL hc) fun u₁ h₁ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (padHead_ok x) fun u₂ ⟨hrd₂, hwr₂, hsp₂, hm₂, hsy₂, h15₂, h10₂, hg₂⟩ => ?_
  have hc₂ : Ctx L g m₀ u₂ := h₁.ctx.regs hL hrd₂ hwr₂ hm₂ hsp₂
    (fun r hr _ => hg₂ r (ne_cs hr (by decide)) (ne_cs hr (by decide))) hsy₂
  have h9₂ : u₂.gpr .x9 = L.scr := (hg₂ _ (by decide) (by decide)).trans h₁.val
  have h10 : (u₂.gpr .x10).setWidth 32 = c ++ c ++ c ++ c := by rw [h10₂, hx]
  have hsep : Region.Disjoint ⟨L.B + BitVec.ofNat 64 16, P.H.D⟩ ⟨L.scr + BitVec.ofNat 64 1792, 4 * (P.H.P.B / 4)⟩ :=
    hL.stk_scr (by anums) (by anums)
  have hW := padWs_ok (L.scr + BitVec.ofNat 64 1792) (L.B + BitVec.ofNat 64 16) (D := P.H.D) c (cfgOf P) rfl
    (by anums) (n := P.H.P.B / 4) (by anums) (by anums) hsep (by anums) (P.H.P.B / 4) (Nat.le_refl _) u₂
    (by rw [h9₂]) (by rw [h15₂, h₁.ctx.sp]) h10 (fun j hj => by
      rw [Offset.add_add]
      exact ⟨L.FR, by rw [hc₂.rd, hc₂.wr]; simp, Offset.contains _ (by omega) (by have := L.he; anums)
        (by have := hL.nB; have := L.he; omega)⟩)
    (fun j hj => by rw [Offset.add_add]; exact hc₂.inScrW (by anums))
  refine WP.mono_syms hW fun u₃ ⟨hrd₃, hwr₃, hsp₃, hg₃, hm₃⟩ hsy₃ => ?_
  have hm₂' : u₂.mem = t.mem := hm₂.trans h₁.mem
  have hf : Frame [⟨L.scr + BitVec.ofNat 64 1792, P.H.P.B⟩] t.mem u₃.mem := by
    rw [hm₃, hm₂']; exact writeBytes_frame _ _ _ (by
      rw [padBytes_length]
      have := Offset.contains_base (L.scr + BitVec.ofNat 64 1792) (d := 0) (n := 4 * (P.H.P.B / 4)) (k := P.H.P.B)
        (by omega) (by omega)
      rwa [BitVec.add_zero] at this)
  refine ⟨hc₂.keep hL hrd₃ hwr₃ hsp₃ (fun r hr _ => hg₃ r (ne_cs hr (by decide)))
      (by rw [hm₂']; exact hf) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L (by anums)) hsy₃, hf, ?_⟩
  have e4 : 4 * (P.H.P.B / 4) = P.H.P.B := by omega
  rw [e4] at hm₃
  rw [hm₃, hm₂', Proof.Hmac.Generic.Common.bytesAt_writeBytes_self' (padBytes_length _ _ _ _ _) (by anums),
    show P.H.P.B = P.ok.SH.H.blockSize from P.ok.hB.symm, padBytes_eq _ _ _ _ (by rw [P.ok.hB]; anums)]

/-! ## HMAC's states for the key -/

/-- A state's representation, kept by memory that changed apart from it. -/
theorem repr_keep {m m' : Mem} {ws : List Region} (hf : Frame ws m m') {p : Addr}
    (hd : ∀ r ∈ ws, Region.Disjoint ⟨p, 192⟩ r) {msg : List Byte} (hr : P.ok.SH.Repr m p msg) :
    P.ok.SH.Repr m' p msg :=
  P.ok.stream.repr m m' p p msg (fun i hi => Frame.bytes (R := ⟨p, 192⟩) hf hd (by show 192 ≤ 2 ^ 64; decide)
    (show i < 192 by anums)) hr

/-- A region of `scratch` below `2256`, as part of what HMAC changes. -/
theorem sub_hm {e k : Nat} (h : e + k ≤ 2256) :
    ∃ r' ∈ [(⟨L.scr, 2256⟩ : Region), ⟨L.B, 16⟩], Region.Sub ⟨L.scr + BitVec.ofNat 64 e, k⟩ r' :=
  ⟨_, List.mem_cons_self .., scr_work h⟩

theorem low_hm : ∃ r' ∈ [(⟨L.scr, 2256⟩ : Region), ⟨L.B, 16⟩], Region.Sub ⟨L.B, 16⟩ r' :=
  ⟨⟨L.B, 16⟩, by simp, sub_refl _⟩

/-- The key survives what HMAC changes. -/
theorem keyOf_hm (hL : L.Ok) {m m' : Mem} (hf : Frame [⟨L.scr, 2256⟩, ⟨L.B, 16⟩] m m') :
    keyOf P L m' = keyOf P L m :=
  bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hL.stk_scr0 (by anums) (by decide)
    · exact Offset.disjoint_base _ (by omega) (by anums)) (by anums)

/-- After `hinit`: HMAC's states for the key `K` in the frame on entry `t`. -/
structure Inited (P : RfcHash) {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (g : Reg → BitVec 64)
    (m₀ : Mem) (t u : State) : Prop where
  ctx : Ctx L g m₀ u
  frame : Frame [⟨L.scr, 2256⟩, ⟨L.B, 16⟩] t.mem u.mem
  inner : P.ok.SH.Repr u.mem (L.scr + BitVec.ofNat 64 0)
    (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.ok.SH.H (keyOf P L t.mem)) Spec.Hmac.ipad)
  outer : P.ok.SH.Repr u.mem (L.scr + BitVec.ofNat 64 192)
    (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.ok.SH.H (keyOf P L t.mem)) Spec.Hmac.opad)

theorem xorPad_length (k : List Byte) (p : Byte) : (Spec.Hmac.xorPad k p).length = k.length :=
  List.length_map _

theorem keyOf_length (m : Mem) : (keyOf P L m).length = P.H.D := by simp [keyOf, Spec.Sha256.bytesAt]

theorem blockKey_length {k : List Byte} (hk : k.length = P.H.D) :
    (Spec.Hmac.blockKey P.ok.SH.H k).length = P.H.P.B := by
  have hB := P.ok.hB
  have hDB : P.H.D < P.H.P.B := by anums
  simp only [Spec.Hmac.blockKey, hk, hB, show ¬ P.H.P.B < P.H.D by omega, ite_false, List.length_append,
    List.length_replicate]
  omega

/-- The padded key, as `update` reads it at `scratch + sPad`. -/
theorem padData (hL : L.Ok) {o : Nat} (ho : o + 192 ≤ 384) :
    UpdData P L o (L.scr + BitVec.ofNat 64 1792) P.H.P.B where
  cov := ⟨L.SCR, by simp, within_off _ (by anums)⟩
  st := Offset.disjoint _ (by anums) (by anums) (by anums)
  wk := Offset.disjoint _ (by anums) (by anums) (by anums)
  low := hL.low_scr (by anums)

/-- The address of the padded key in `x2`. -/
theorem padA (hL : L.Ok) : ∀ u, Ctx L g m₀ u →
    WP isa (.block (Cfg.scr .x2 sPad)) u (Upd L g m₀ u .x2 (L.scr + BitVec.ofNat 64 1792)) :=
  fun _ hu => scr_ok hL hu (d := .x2) (by decide) (a := 1792) (by decide)

/-- `hinit`: each state set by `init` and updated with its padded key. -/
theorem init_step (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).hinit t (Inited P L g m₀ t) := by
  have dS : ∀ {a b : Nat}, a + 192 ≤ b ∨ b + 192 ≤ a → b + 192 ≤ 8192 → a + 192 ≤ 8192 →
      Region.Disjoint ⟨L.scr + BitVec.ofNat 64 a, 192⟩ ⟨L.scr + BitVec.ofNat 64 b, P.H.S⟩ :=
    fun h hb ha => Offset.disjoint _ (by anums) (by anums) (by anums)
  unfold Cfg.hinit
  refine WP.seq (WP.mono (initCall_ok hL hT hc (o := 0) (by decide)) fun u₁ ⟨hc₁, hf₁, hr₁⟩ => ?_)
  refine WP.seq (WP.mono (initCall_ok hL hT hc₁ (o := 192) (by decide)) fun u₂ ⟨hc₂, hf₂, hr₂⟩ => ?_)
  have hr₁' := repr_keep hf₂ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dS (.inl (by decide)) (by decide) (by decide)
    · exact (hL.low_scr (by decide)).symm) hr₁
  have hF₂ : Frame [⟨L.scr, 2256⟩, ⟨L.B, 16⟩] t.mem u₂.mem :=
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
  refine WP.seq (WP.mono (padBlk_ok hL hc₂ (P := P) ipad32 Spec.Hmac.ipad movzk_ipad) fun u₃ ⟨hc₃, hf₃, hb₃⟩ => ?_)
  have dP : ∀ {a : Nat}, a + 192 ≤ 384 →
      Region.Disjoint ⟨L.scr + BitVec.ofNat 64 a, 192⟩ ⟨L.scr + BitVec.ofNat 64 1792, P.H.P.B⟩ :=
    fun h => Offset.disjoint _ (by anums) (by anums) (by anums)
  have hr₁₃ := repr_keep hf₃ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dP (by decide)) hr₁'
  have hr₂₃ := repr_keep hf₃ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dP (by decide)) hr₂
  refine WP.seq (WP.mono (updCall_ok hL hT hc₃ (o := 0) (by decide) (padA hL) (padData hL (by decide))
    (by anums) (by anums) hr₁₃ rfl) fun u₄ ⟨hc₄, hf₄, hr₄⟩ => ?_)
  have dW : ∀ {a : Nat}, a + 192 ≤ 384 → ∀ {b : Nat}, b + 192 ≤ 384 → a + 192 ≤ b ∨ b + 192 ≤ a →
      ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 b, P.H.S⟩ : Region), ⟨L.scr + BitVec.ofNat 64 384, P.ok.stream.Wb⟩,
        ⟨L.B, 16⟩], Region.Disjoint ⟨L.scr + BitVec.ofNat 64 a, 192⟩ r := fun ha b hb hab r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact dS hab (by anums) (by omega)
    · exact Offset.disjoint _ (by omega) (by anums) (by anums)
    · exact (hL.low_scr (by omega)).symm
  have hr₂₄ := repr_keep hf₄ (dW (a := 192) (by decide) (b := 0) (by decide) (.inr (by decide))) hr₂₃
  have hF₄ : Frame [⟨L.scr, 2256⟩, ⟨L.B, 16⟩] t.mem u₄.mem :=
    (hF₂.trans (hf₃.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact sub_hm (by anums))).trans (hf₄.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub_hm (by anums)
      · exact sub_hm (by anums)
      · exact low_hm)
  have hk₄ : keyOf P L u₄.mem = keyOf P L t.mem := keyOf_hm hL hF₄
  refine WP.seq (WP.mono (padBlk_ok hL hc₄ (P := P) opad32 Spec.Hmac.opad movzk_opad) fun u₅ ⟨hc₅, hf₅, hb₅⟩ => ?_)
  have hr₁₅ := repr_keep hf₅ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dP (by decide)) hr₄
  have hr₂₅ := repr_keep hf₅ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dP (by decide)) hr₂₄
  refine WP.mono (updCall_ok hL hT hc₅ (o := 192) (by decide) (padA hL) (padData hL (by decide))
    (by anums) (by anums) hr₂₅ rfl) fun u₆ ⟨hc₆, hf₆, hr₆⟩ => ?_
  have hr₁₆ := repr_keep hf₆ (dW (a := 0) (by decide) (b := 192) (by decide) (.inl (by decide))) hr₁₅
  refine ⟨hc₆, (hF₄.trans (hf₅.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact sub_hm (by anums))).trans (hf₆.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub_hm (by anums)
      · exact sub_hm (by anums)
      · exact low_hm), ?_, ?_⟩
  · rw [List.nil_append, hb₃, hk₂] at hr₁₆; exact hr₁₆
  · rw [List.nil_append, hb₅, hk₄] at hr₆; exact hr₆

/-! ## The data -/

/-- After `hupd`: the inner state holds the data too. -/
structure Updated (P : RfcHash) {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (g : Reg → BitVec 64)
    (m₀ : Mem) (t : State) (da : Addr) (len : Nat) (u : State) : Prop where
  ctx : Ctx L g m₀ u
  frame : Frame [⟨L.scr, 2256⟩, ⟨L.B, 16⟩] t.mem u.mem
  inner : P.ok.SH.Repr u.mem (L.scr + BitVec.ofNat 64 0)
    (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.ok.SH.H (keyOf P L t.mem)) Spec.Hmac.ipad ++
      Spec.Sha256.bytesAt t.mem da len)
  outer : P.ok.SH.Repr u.mem (L.scr + BitVec.ofNat 64 192)
    (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.ok.SH.H (keyOf P L t.mem)) Spec.Hmac.opad)

theorem DataOk.upd (hL : L.Ok) {da : Addr} {len : Nat} (hd : DataOk L da len) : UpdData P L 0 da len where
  cov := hd.within
  st := hd.work hL (by anums)
  wk := hd.work hL (by anums)
  low := hd.low hL

/-- The data survives what HMAC changes. -/
theorem DataOk.keep (hL : L.Ok) {da : Addr} {len : Nat} (hd : DataOk L da len) {m m' : Mem}
    (hf : Frame [⟨L.scr, 2256⟩, ⟨L.B, 16⟩] m m') : Spec.Sha256.bytesAt m' da len = Spec.Sha256.bytesAt m da len :=
  bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa using hd.work hL (e := 0) (k := 2256) (by omega)
    · exact (hd.low hL).symm) (by
      rcases hd with ⟨o, -, -, h⟩ | ⟨o, -, -, h⟩ <;> omega)

theorem upd_step (hL : L.Ok) (hT : TabL P L) {t u : State} (hu : Inited P L g m₀ t u) {dataA : List Instr}
    {da : Addr} {len : Nat} (hdA : ∀ u, Ctx L g m₀ u → WP isa (.block dataA) u (Upd L g m₀ u .x2 da))
    (hd : DataOk L da len) (hlen : len ≤ 256) :
    WP isa ((cfgOf P).hupd dataA len) u (Updated P L g m₀ t da len) := by
  refine WP.mono (updCall_ok hL hT hu.ctx (o := 0) (cnt := P.H.P.B) (by decide) hdA (hd.upd hL) (by anums)
    (by omega) hu.inner
    (by rw [xorPad_length, blockKey_length (keyOf_length _)])) fun w ⟨hcw, hfw, hrw⟩ => ?_
  refine ⟨hcw, hu.frame.trans (hfw.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub_hm (by anums)
      · exact sub_hm (by anums)
      · exact low_hm), by rw [← hd.keep hL hu.frame]; exact hrw, repr_keep hfw (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint _ (by anums) (by anums) (by anums)
    · exact Offset.disjoint _ (by anums) (by anums) (by anums)
    · exact (hL.low_scr (by decide)).symm) hu.outer⟩

/-! ## The MAC -/

/-- After `hfin`: the MAC in the frame at `dst`. -/
structure Done (P : RfcHash) {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (g : Reg → BitVec 64)
    (m₀ : Mem) (t : State) (da : Addr) (len dst : Nat) (u : State) : Prop where
  ctx : Ctx L g m₀ u
  frame : Frame [⟨L.scr, 2256⟩, ⟨L.B, 16⟩, ⟨L.B + BitVec.ofNat 64 (16 + dst), P.H.D⟩] t.mem u.mem
  mac : Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (16 + dst)) P.H.D =
    P.mac (keyOf P L t.mem) (Spec.Sha256.bytesAt t.mem da len)

/-- The hash function's output is `D` bytes. -/
theorem hash_length (P : RfcHash) (m : List Byte) : (P.ok.SH.H.hash m).length = P.H.D := by
  have := P.ok.sizes.DN
  simp only [P.ok.hash, List.length_take, Proof.MdStream.Md.hash, P.ok.md.digest_length]
  omega

/-- The first `D` bytes `finalize` wrote: the digest. -/
theorem tmp_digest {m : Mem} {msg : List Byte}
    (h : (Spec.Sha256.bytesAt m (L.scr + BitVec.ofNat 64 1920) P.H.stream.F).take P.H.D = P.ok.SH.H.hash msg) :
    Spec.Sha256.bytesAt m (L.scr + BitVec.ofNat 64 1920) P.H.D = P.ok.SH.H.hash msg := by
  rw [bytesAt_take _ _ (show P.H.D ≤ P.H.stream.F from P.ok.stream.hDF)]; exact h

/-- What `finalize` writes and the working space, within what HMAC changes. -/
theorem fin_hm {o : Nat} (ho : o + 192 ≤ 384) : ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 o, P.H.S⟩ : Region),
    ⟨L.scr + BitVec.ofNat 64 1920, P.H.stream.F⟩, ⟨L.scr + BitVec.ofNat 64 384, P.ok.stream.Wb⟩, ⟨L.B, 16⟩],
    ∃ r' ∈ [(⟨L.scr, 2256⟩ : Region), ⟨L.B, 16⟩], Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact sub_hm (by anums)
  · exact sub_hm (by anums)
  · exact sub_hm (by anums)
  · exact low_hm

/-- The addresses of the digest's copy: `scratch + sTmp` in `x13`, the frame's `dst` in `x14`. -/
theorem copyHead_ok {t : State} {dst : Nat} (hdst : dst < 4096) :
    WP isa (.block [.addSp .x15 0, .addImm .x .x13 .x9 sTmp, .addImm .x .x14 .x15 dst]) t
      fun u => u.rd = t.rd ∧ u.wr = t.wr ∧ u.sp = t.sp ∧ u.mem = t.mem ∧ u.syms = t.syms ∧
        u.gpr .x13 = t.gpr .x9 + BitVec.ofNat 64 1920 ∧ u.gpr .x14 = t.sp + BitVec.ofNat 64 dst ∧
        ∀ r, r ≠ .x13 → r ≠ .x14 → r ≠ .x15 → u.gpr r = t.gpr r := by
  apply WP.of_runBlock
  simp only [sTmp, runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits, BitVec.add_zero,
    Option.some.injEq, exists_eq_left', show (0 : Nat) < 4096 by decide, show (1920 : Nat) < 4096 by decide,
    hdst, ite_true]
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, fun r h₁ h₂ h₃ => ?_⟩
  · rw [RegUpd.gpr_write_of_ne _ _ _ (by decide), RegUpd.gpr_write_self, BitVec.setWidth_eq,
      RegUpd.gpr_write_of_ne _ _ _ (by decide), BitVec.setWidth_eq]
  · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, RegUpd.gpr_write_of_ne _ _ _ (by decide),
      RegUpd.gpr_write_self, BitVec.setWidth_eq, BitVec.setWidth_eq]
  · rw [RegUpd.gpr_write_of_ne _ _ _ h₂, RegUpd.gpr_write_of_ne _ _ _ h₁, RegUpd.gpr_write_of_ne _ _ _ h₃]

theorem fin_step (hL : L.Ok) (hT : TabL P L) {t u : State} {da : Addr} {len dst : Nat}
    (hu : Updated P L g m₀ t da len u) (hlen : len ≤ 256) (hdst : dst + P.H.D ≤ 168) :
    WP isa ((cfgOf P).hfin len dst) u (Done P L g m₀ t da len dst) := by
  have hkl := blockKey_length (P := P) (keyOf_length (L := L) t.mem)
  have hdl : (Spec.Sha256.bytesAt t.mem da len).length = len := by simp [Spec.Sha256.bytesAt]
  unfold Cfg.hfin
  refine WP.seq (WP.mono (finCall_ok hL hT hu.ctx (o := 0) (by decide) (cnt := P.H.P.B + len) (by anums) hu.inner
    (by rw [List.length_append, xorPad_length, hkl, hdl])) fun w₁ ⟨hc₁, hf₁, hd₁⟩ => ?_)
  have hd₁' := tmp_digest hd₁
  have ho₁ := repr_keep hf₁ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Offset.disjoint _ (by anums) (by anums) (by anums)
    · exact Offset.disjoint _ (by anums) (by anums) (by anums)
    · exact Offset.disjoint _ (by anums) (by anums) (by anums)
    · exact (hL.low_scr (by decide)).symm) hu.outer
  have tmpD : UpdData P L 192 (L.scr + BitVec.ofNat 64 1920) P.H.D :=
    ⟨⟨L.SCR, by simp, within_off _ (by anums)⟩, Offset.disjoint _ (by anums) (by anums) (by anums),
      Offset.disjoint _ (by anums) (by anums) (by anums), hL.low_scr (by anums)⟩
  refine WP.seq (WP.mono (updCall_ok hL hT hc₁ (o := 192) (cnt := P.H.P.B) (by decide)
    (fun _ hu' => scr_ok hL hu' (d := .x2) (by decide) (a := 1920) (by decide)) tmpD (by anums) (by anums) ho₁
    (by rw [xorPad_length, hkl])) fun w₂ ⟨hc₂, hf₂, hr₂⟩ => ?_)
  rw [hd₁'] at hr₂
  refine WP.seq (WP.mono (finCall_ok hL hT hc₂ (o := 192) (by decide) (cnt := P.H.P.B + P.H.D) (by anums) hr₂
    (by rw [List.length_append, xorPad_length, hkl, hash_length])) fun w₃ ⟨hc₃, hf₃, hd₃⟩ => ?_)
  have hd₃' := tmp_digest hd₃
  rw [WP.block_append_iff]
  refine WP.mono (scrPtr_ok hL hc₃) fun w₄ h₄ => ?_
  rw [Cfg.copyOut, WP.block_append_iff]
  refine WP.mono (copyHead_ok (t := w₄) (dst := dst) (by omega))
    fun w₅ ⟨hrd₅, hwr₅, hsp₅, hm₅, hsy₅, h13₅, h14₅, hg₅⟩ => ?_
  have hc₅ : Ctx L g m₀ w₅ := h₄.ctx.regs hL hrd₅ hwr₅ hm₅ hsp₅
    (fun r hr _ => hg₅ r (ne_cs hr (by decide)) (ne_cs hr (by decide)) (ne_cs hr (by decide))) hsy₅
  have hS : w₅.gpr .x13 = L.scr + BitVec.ofNat 64 1920 := by rw [h13₅, h₄.val]
  have hD : w₅.gpr .x14 = L.B + BitVec.ofNat 64 (16 + dst) := by rw [h14₅, h₄.ctx.sp, Offset.add_add]
  have hsep : Region.Disjoint ⟨L.scr + BitVec.ofNat 64 1920, P.H.D⟩ ⟨L.B + BitVec.ofNat 64 (16 + dst), P.H.D⟩ :=
    (hL.stk_scr (by anums) (by anums)).symm
  refine WP.mono_syms (copyBytes_ok (src := .x13) (dst := .x14) (Q := P.H.D) (by decide) (by decide) (by decide)
    hsep (by anums) (by anums) hS hD
    (fun j hj => by rw [Offset.add_add]; exact hc₅.inScr (by anums)) (fun j hj => by
      rw [Offset.add_add]; exact hc₅.inFrW (by omega) (by have := L.he; omega)))
    fun w₆ ⟨hrd₆, hwr₆, hsp₆, hg₆, hf₆, hb₆⟩ hsy₆ => ?_
  refine ⟨hc₅.keep hL hrd₆ hwr₆ hsp₆ (fun r hr _ => hg₆ r (ne_cs hr (by decide)) (ne_cs hr (by decide))
    (ne_cs hr (by decide))) hf₆
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by omega)) hsy₆, ?_, ?_⟩
  · have e : ∀ {r : Region}, (∃ r' ∈ [(⟨L.scr, 2256⟩ : Region), ⟨L.B, 16⟩], Region.Sub r r') →
        ∃ r' ∈ [(⟨L.scr, 2256⟩ : Region), ⟨L.B, 16⟩, ⟨L.B + BitVec.ofNat 64 (16 + dst), P.H.D⟩], Region.Sub r r' :=
      fun ⟨r', hr', hs⟩ => ⟨r', by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr' ⊢; rcases hr' with h | h <;> simp [h], hs⟩
    refine ((((hu.frame.sub fun r hr => e ⟨r, hr, sub_refl _⟩).trans (hf₁.sub fun r hr => e (fin_hm (by decide) r hr))).trans
      (hf₂.sub fun r hr => e ?_)).trans (hf₃.sub fun r hr => e (fin_hm (by decide) r hr))).trans ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub_hm (by anums)
      · exact sub_hm (by anums)
      · exact low_hm
    · rw [← h₄.mem, ← hm₅]; exact hf₆.sub fun r hr => ⟨r, by simp_all, sub_refl _⟩
  · rw [hb₆, hm₅, h₄.mem, hd₃']
    rfl

/-! ## The whole HMAC -/

/-- `HMAC_K(data)`, for the key `K` in the frame, to the frame at `dst`. -/
theorem hmac_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) {dataA : List Instr} {da : Addr}
    {len dst : Nat} (hdA : ∀ u, Ctx L g m₀ u → WP isa (.block dataA) u (Upd L g m₀ u .x2 da))
    (hd : DataOk L da len) (hlen : len ≤ 256) (hdst : dst + P.H.D ≤ 168) :
    WP isa ((cfgOf P).hmac dataA len dst) t (Done P L g m₀ t da len dst) :=
  WP.seq (WP.mono (init_step hL hT hc) fun _ hu => WP.seq (WP.mono (upd_step hL hT hu hdA hd hlen) fun _ hw =>
    fin_step hL hT hw hlen hdst))

end VG.Proof.Ecdsa.Rfc6979.AArch64
