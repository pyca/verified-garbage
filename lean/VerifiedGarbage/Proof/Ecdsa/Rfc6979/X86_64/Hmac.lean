module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Hash
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs

/-!
# Deterministic ECDSA on x86-64: one HMAC

`HMAC_K(data)` (`Cfg.hmac`), for the key `K` (of the hash function's output
length) in the frame and `len` bytes of data in the frame or in `scratch`
above HMAC's working space (`DataOk`), written to the frame at `dst`: HMAC's
`init` with `K` (`init_step`), the streaming `update` on the inner state
(`upd_step`), and HMAC's `finalize` (`fin_step`), for any hash function `P`,
each the case of `P`'s number of a dispatch (`callH_ok`), with the lengths
from the frame's numbers of the hash function (`HashLay`). They change only
HMAC's states and working space (the first 2560 bytes of `scratch`), the 24
bytes below the frame, and `dst` (`hmac_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64

/-- Where the data may be: in the frame below its pointers, or in `scratch`
above HMAC's working space. -/
def DataOk {dn : Nat} (L : Lay dn) (da : Addr) (len : Nat) : Prop :=
  (∃ o, da = L.B + BitVec.ofNat 64 o ∧ 24 ≤ o ∧ o + len ≤ 192) ∨
    (∃ o, da = L.scr + BitVec.ofNat 64 o ∧ 2560 ≤ o ∧ o + len ≤ 8192)

/-- The frame's numbers of the hash function are `P`'s. -/
def HashLay (P : RfcHash) {dn : Nat} (L : Lay dn) : Prop := L.sel = P.k ∧ L.hl = P.H.D ∧ L.bs = P.H.P.B

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {m₀ : Mem}

namespace DataOk

variable {da : Addr} {len : Nat}

theorem low (hd : DataOk L da len) (hL : L.Ok) : Region.Disjoint ⟨L.B, 24⟩ ⟨da, len⟩ := by
  rcases hd with ⟨o, rfl, h₁, h₂⟩ | ⟨o, rfl, h₁, h₂⟩
  · exact Offset.base_disjoint _ h₁ (by omega)
  · exact hL.low_scr h₂

/-- The data is apart from HMAC's states and working space. -/
theorem work (hd : DataOk L da len) (hL : L.Ok) {e k : Nat} (h : e + k ≤ 2560) :
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

/-! ## The frame's numbers of the hash function, and the dispatch -/

theorem ldHL_ok (hL : L.Ok) (hq : HashLay P L) {u : State} (hc : Ctx L g m₀ u) {d : Reg} (hd : d ∉ calleeSaved) :
    WP isa (.block [.mov d (.mem (stk fHL))]) u (Upd L g m₀ u d (BitVec.ofNat 64 P.H.D)) :=
  WP.mono (ld_ok hL hc hd (o := fHL) (by decide)) fun _ h => { h with val := h.val.trans (hq.2.1 ▸ hc.pHL) }

theorem ldBS_ok (hL : L.Ok) (hq : HashLay P L) {u : State} (hc : Ctx L g m₀ u) {d : Reg} (hd : d ∉ calleeSaved) :
    WP isa (.block [.mov d (.mem (stk fBS))]) u (Upd L g m₀ u d (BitVec.ofNat 64 P.H.P.B)) :=
  WP.mono (ld_ok hL hc hd (o := fBS) (by decide)) fun _ h => { h with val := h.val.trans (hq.2.2 ▸ hc.pBS) }

theorem ldSel_ok (hL : L.Ok) (hq : HashLay P L) {u : State} (hc : Ctx L g m₀ u) :
    WP isa (.block Cfg.selLd) u (Upd L g m₀ u .rax (BitVec.ofNat 64 P.k)) :=
  WP.mono (ld_ok hL hc (d := .rax) (by decide) (o := fSel) (by decide)) fun _ h =>
    { h with val := h.val.trans (hq.1 ▸ hc.pSel) }

/-- `d ← d + D`. -/
theorem addHL_ok (hL : L.Ok) (hq : HashLay P L) {u : State} (hc : Ctx L g m₀ u) {d : Reg} (hd : d ∉ calleeSaved) :
    WP isa (.block [.alu .add d (.mem (stk fHL))]) u (Upd L g m₀ u d (u.gpr d + BitVec.ofNat 64 P.H.D)) :=
  WP.mono (addMem_ok hL hc hd (o := fHL) (by decide)) fun _ h =>
    { h with val := h.val.trans (congrArg (u.gpr d + ·) (hq.2.1 ▸ hc.pHL)) }

/-- A dispatch on the hash function: the call of `P`'s, from a state of other flags. -/
theorem callH_ok (P : RfcHash) {f : Impl.Pbkdf2.Md.X86_64.Hash → String × Prog isa} {s : State}
    {Q : State → Prop} (hs : s.gpr .rax = BitVec.ofNat 64 P.k)
    (h : ∀ s', Proof.Dispatch.X86_64.FlagsOnly s s' → WP isa (.call (f P.H).1 (f P.H).2) s' Q) :
    WP isa ((cfgOf P).callH f) s Q := by
  have hk := P.hk
  have hk8 : P.k < 8 := by
    simp only [Spec.Ecdsa.Rfc6979.hashIds, List.mem_cons, List.not_mem_nil, or_false] at hk; omega
  have hsel : Proof.Dispatch.X86_64.sel s = P.k := by
    rw [Proof.Dispatch.X86_64.sel, hs, BitVec.toNat_ofNat]; omega
  have hkeys := keys_cases P fun H => (Code.call (f H).1 (f H).2 : Prog isa)
  refine Proof.Dispatch.chain_wp Proof.Dispatch.X86_64.tests _ ?_ ?_ ?_ fun c hc s' hr _ => ?_
  · intro i hi
    rw [Proof.Dispatch.keys, hkeys] at hi
    simp only [Spec.Ecdsa.Rfc6979.hashIds, List.mem_cons, List.not_mem_nil, or_false] at hi; omega
  · rw [Proof.Dispatch.keys, hkeys, hsel]; exact hk
  · rw [Proof.Dispatch.keys, hkeys]; decide
  · rw [hsel] at hc
    rw [case_eq P (fun H => (Code.call (f H).1 (f H).2 : Prog isa)) hc]
    exact h s' hr

theorem Ctx.flags (hL : L.Ok) {u u' : State} (hc : Ctx L g m₀ u) (h : Proof.Dispatch.X86_64.FlagsOnly u u') :
    Ctx L g m₀ u' := by
  obtain ⟨_, _, _, _, rfl⟩ := h
  exact hc.regs hL rfl rfl rfl rfl fun _ _ => rfl

/-! ## HMAC's `init` -/

/-- The arguments of HMAC's `init`, and `hash`. -/
theorem initArgs_ok (hL : L.Ok) (hq : HashLay P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.hmacArgs₁) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧
      t'.gpr .rdi = L.scr + BitVec.ofNat 64 0 ∧ t'.gpr .rsi = L.scr + BitVec.ofNat 64 256 ∧
      t'.gpr .rdx = L.B + BitVec.ofNat 64 24 ∧ t'.gpr .rcx = BitVec.ofNat 64 P.H.D ∧
      t'.gpr .r8 = L.scr + BitVec.ofNat 64 512 ∧ t'.gpr .rax = BitVec.ofNat 64 P.k := by
  rw [Cfg.hmacArgs₁, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff,
    WP.block_append_iff]
  refine WP.mono (scr_ok hL hc (d := .rdi) (by decide) (a := 0) (by decide)) fun u₁ h₁ => ?_
  refine WP.mono (scr_ok hL h₁.ctx (d := .rsi) (by decide) (a := 256) (by decide)) fun u₂ h₂ => ?_
  refine WP.mono (fr_ok hL h₂.ctx (d := .rdx) (by decide) (o := 0) (by decide)) fun u₃ h₃ => ?_
  refine WP.mono (ldHL_ok hL hq h₃.ctx (d := .rcx) (by decide)) fun u₄ h₄ => ?_
  refine WP.mono (scr_ok hL h₄.ctx (d := .r8) (by decide) (a := 512) (by decide)) fun u₅ h₅ => ?_
  refine WP.mono (ldSel_ok hL hq h₅.ctx) fun u₆ h₆ => ?_
  refine ⟨h₆.ctx, by rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem], ?_, ?_, ?_, ?_, ?_, h₆.val⟩
  · rw [h₆.keep _ (by decide), h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide),
      h₂.keep _ (by decide), h₁.val]
  · rw [h₆.keep _ (by decide), h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.val]
  · rw [h₆.keep _ (by decide), h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.val]
  · rw [h₆.keep _ (by decide), h₅.keep _ (by decide), h₄.val]
  · rw [h₆.keep _ (by decide), h₅.val]

/-- The writes of a call, within HMAC's working space and the stack below the frame. -/
theorem safe_call {u : State} (hc : Ctx L g m₀ u) {ws : List Region} (hs : ∀ r ∈ ws, Safe L r) {n : Nat}
    (hn : n ≤ 24) : ∀ r ∈ ws ++ [below (u.gpr .rsp) n], Safe L r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact hs r hr
  · simp only [List.mem_singleton] at hr; subst hr
    exact .inr (.inr (.inl ((hc.below_sub hn).trans (Region.sub_prefix (by omega)))))

/-- The key `K`: the first `D` bytes of the frame. -/
abbrev keyOf (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) : List Byte :=
  Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 24) P.H.D

/-- After HMAC's `init`: HMAC's states for the key `K` in the frame on entry `t`. -/
structure Inited (P : RfcHash) {dn : Nat} (L : Lay dn) (g : Reg → BitVec 64) (m₀ : Mem) (t u : State) : Prop where
  ctx : Ctx L g m₀ u
  frame : Frame [⟨L.scr, 2560⟩, ⟨L.B, 24⟩] t.mem u.mem
  inner : P.ok.SH.Repr u.mem (L.scr + BitVec.ofNat 64 0)
    (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.ok.SH.H (keyOf P L t.mem)) Spec.Hmac.ipad)
  outer : P.ok.SH.Repr u.mem (L.scr + BitVec.ofNat 64 256)
    (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.ok.SH.H (keyOf P L t.mem)) Spec.Hmac.opad)

theorem scr_work {e k : Nat} (h : e + k ≤ 2560) : Region.Sub ⟨L.scr + BitVec.ofNat 64 e, k⟩ ⟨L.scr, 2560⟩ :=
  Offset.sub_base _ h

theorem initA (hL : L.Ok) {u : State} (hcu : Ctx L g m₀ u) (hdi : u.gpr .rdi = L.scr + BitVec.ofNat 64 0)
    (hsi : u.gpr .rsi = L.scr + BitVec.ofNat 64 256) (hdx : u.gpr .rdx = L.B + BitVec.ofNat 64 24)
    (hcx : u.gpr .rcx = BitVec.ofNat 64 P.H.D) (h8 : u.gpr .r8 = L.scr + BitVec.ofNat 64 512) :
    Proof.Pbkdf2.Md.X86_64.Pbk.InitArgs (H := P.H) u (L.scr + BitVec.ofNat 64 0)
      (L.scr + BitVec.ofNat 64 256) (L.B + BitVec.ofNat 64 24) (L.scr + BitVec.ofNat 64 512) P.H.D := by
  have hsp : below (u.gpr .rsp) 24 = ⟨L.B, 24⟩ := by rw [hcu.rsp, below24]
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

theorem init_step (hL : L.Ok) (hq : HashLay P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.seq (.block Cfg.hmacArgs₁) ((cfgOf P).callH fun H => (H.hmacInitN, H.hmacInit))) t
      (Inited P L g m₀ t) := by
  refine WP.seq (WP.mono (initArgs_ok hL hq hc) fun u₀ ⟨hcu₀, hmu₀, hdi₀, hsi₀, hdx₀, hcx₀, h8₀, hax⟩ =>
    callH_ok P hax fun u hf => ?_)
  have hcu := hcu₀.flags hL hf
  have hmu : u.mem = t.mem := hf.mem.trans hmu₀
  have hdi := (hf.gpr .rdi).trans hdi₀
  have hsi := (hf.gpr .rsi).trans hsi₀
  have hdx := (hf.gpr .rdx).trans hdx₀
  have hcx := (hf.gpr .rcx).trans hcx₀
  have h8 := (hf.gpr .r8).trans h8₀
  have hsp : below (u.gpr .rsp) 24 = ⟨L.B, 24⟩ := by rw [hcu.rsp, below24]
  have a := initA (P := P) hL hcu hdi hsi hdx hcx h8
  refine WP.of_syms (Proof.Pbkdf2.Md.X86_64.Pbk.hinit_call P.ok P.hI P.hIsp P.hId a
    fun u' hrd hwr hcs hf hi ho hsy => ?_)
  have hsafe : ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 0, P.H.S⟩ : Region), ⟨L.scr + BitVec.ofNat 64 256, P.H.S⟩,
      ⟨L.scr + BitVec.ofNat 64 512, 8 * P.H.W⟩], Region.Sub r ⟨L.scr, 2560⟩ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> exact scr_work (by nums)
  refine ⟨hcu.keep hL hrd hwr (hcs .rsp (by decide)) (fun r hr _ => hcs r hr) hf
    (safe_call hcu (fun r hr => .inr (.inl ((hsafe r hr).trans (Region.sub_prefix (by omega))))) (Nat.le_refl _))
    hsy,
    hmu ▸ hf.sub fun r hr => ?_, by rw [← hmu]; exact hi, by rw [← hmu]; exact ho⟩
  rcases List.mem_append.mp hr with hr | hr
  · exact ⟨⟨L.scr, 2560⟩, by simp, hsafe r hr⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨L.B, 24⟩, by simp, by rw [hsp]; exact sub_refl _⟩

/-! ## The streaming `update` -/

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

theorem updArgs_ok (hL : L.Ok) (hq : HashLay P L) {u : State} (hc : Ctx L g m₀ u) {dataA : List Instr} {da : Addr}
    (hdA : ∀ u, Ctx L g m₀ u → WP isa (.block dataA) u (Upd L g m₀ u .rdx da)) {e : Nat} (he : e < 2 ^ 31) :
    WP isa (.block (Cfg.hmacArgs₂ dataA e)) u fun u' => Ctx L g m₀ u' ∧
      u'.mem = u.mem ∧ u'.gpr .rdi = L.scr + BitVec.ofNat 64 0 ∧ u'.gpr .rsi = BitVec.ofNat 64 P.H.P.B ∧
      u'.gpr .rdx = da ∧ u'.gpr .rcx = BitVec.ofNat 64 (P.H.D + e) ∧ u'.gpr .r8 = L.scr + BitVec.ofNat 64 512 ∧
      u'.gpr .rax = BitVec.ofNat 64 P.k := by
  rw [Cfg.hmacArgs₂, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff,
    WP.block_append_iff]
  refine WP.mono (scr_ok hL hc (d := .rdi) (by decide) (a := 0) (by decide)) fun u₁ h₁ => ?_
  refine WP.mono (ldBS_ok hL hq h₁.ctx (d := .rsi) (by decide)) fun u₂ h₂ => ?_
  refine WP.mono (hdA u₂ h₂.ctx) fun u₃ h₃ => ?_
  rw [show ([.mov .rcx (.mem (stk fHL)), .alu .add .rcx (.imm (BitVec.ofNat 32 e))] : List Instr) =
    [.mov .rcx (.mem (stk fHL))] ++ [.alu .add .rcx (.imm (BitVec.ofNat 32 e))] from rfl, WP.block_append_iff]
  refine WP.mono (ldHL_ok hL hq h₃.ctx (d := .rcx) (by decide)) fun u₄ h₄ => ?_
  refine WP.mono (addImm_ok hL h₄.ctx (d := .rcx) (by decide) he) fun u₄' h₄' => ?_
  refine WP.mono (scr_ok hL h₄'.ctx (d := .r8) (by decide) (a := 512) (by decide)) fun u₅ h₅ => ?_
  refine WP.mono (ldSel_ok hL hq h₅.ctx) fun u₆ h₆ => ?_
  refine ⟨h₆.ctx, by rw [h₆.mem, h₅.mem, h₄'.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem], ?_, ?_, ?_, ?_, ?_, h₆.val⟩
  · rw [h₆.keep _ (by decide), h₅.keep _ (by decide), h₄'.keep _ (by decide), h₄.keep _ (by decide),
      h₃.keep _ (by decide), h₂.keep _ (by decide), h₁.val]
  · rw [h₆.keep _ (by decide), h₅.keep _ (by decide), h₄'.keep _ (by decide), h₄.keep _ (by decide),
      h₃.keep _ (by decide), h₂.val]
  · rw [h₆.keep _ (by decide), h₅.keep _ (by decide), h₄'.keep _ (by decide), h₄.keep _ (by decide), h₃.val]
  · rw [h₆.keep _ (by decide), h₅.keep _ (by decide), h₄'.val, h₄.val, BitVec.ofNat_add_ofNat]
  · rw [h₆.keep _ (by decide), h₅.val]

/-- After the streaming `update`: the inner state holds the data too. -/
structure Updated (P : RfcHash) {dn : Nat} (L : Lay dn) (g : Reg → BitVec 64) (m₀ : Mem) (t : State) (da : Addr)
    (len : Nat) (u : State) : Prop where
  ctx : Ctx L g m₀ u
  frame : Frame [⟨L.scr, 2560⟩, ⟨L.B, 24⟩] t.mem u.mem
  inner : P.ok.SH.Repr u.mem (L.scr + BitVec.ofNat 64 0)
    (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.ok.SH.H (keyOf P L t.mem)) Spec.Hmac.ipad ++
      Spec.Sha256.bytesAt t.mem da len)
  outer : P.ok.SH.Repr u.mem (L.scr + BitVec.ofNat 64 256)
    (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.ok.SH.H (keyOf P L t.mem)) Spec.Hmac.opad)

/-- The arguments of the streaming `update`. -/
theorem updA (hL : L.Ok) {w : State} (hcw : Ctx L g m₀ w) {da : Addr} {len : Nat} (hd : DataOk L da len)
    (hlen : len ≤ 256) (hdi : w.gpr .rdi = L.scr + BitVec.ofNat 64 0) (hdx : w.gpr .rdx = da)
    (hcx : w.gpr .rcx = BitVec.ofNat 64 len) (h8 : w.gpr .r8 = L.scr + BitVec.ofNat 64 512) :
    Proof.Pbkdf2.Md.X86_64.Calls.UpdArgs P.ok.stream w (L.scr + BitVec.ofNat 64 0) da
      (L.scr + BitVec.ofNat 64 512) len := by
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

theorem upd_step (hL : L.Ok) (hq : HashLay P L) {t u : State} (hu : Inited P L g m₀ t u) {dataA : List Instr}
    {da : Addr} {e : Nat} (hdA : ∀ u, Ctx L g m₀ u → WP isa (.block dataA) u (Upd L g m₀ u .rdx da))
    (hd : DataOk L da (P.H.D + e)) (hlen : P.H.D + e ≤ 256) :
    WP isa (.seq (.block (Cfg.hmacArgs₂ dataA e)) ((cfgOf P).callH fun H => (H.updN, H.updC))) u
      (Updated P L g m₀ t da (P.H.D + e)) := by
  refine WP.seq (WP.mono (updArgs_ok hL hq hu.ctx hdA (e := e) (by omega))
    fun w₀ ⟨hcw₀, hmw₀, hdi₀, hsi₀, hdx₀, hcx₀, h8₀, hax⟩ => callH_ok P hax fun w hf => ?_)
  have hcw := hcw₀.flags hL hf
  have hmw : w.mem = u.mem := hf.mem.trans hmw₀
  have hdi := (hf.gpr .rdi).trans hdi₀
  have hsi := (hf.gpr .rsi).trans hsi₀
  have hdx := (hf.gpr .rdx).trans hdx₀
  have hcx := (hf.gpr .rcx).trans hcx₀
  have h8 := (hf.gpr .r8).trans h8₀
  generalize P.H.D + e = len at hd hlen hcx ⊢
  have hsp : Region.Sub (below (w.gpr .rsp) 16) ⟨L.B, 24⟩ := hcw.below_sub (by omega)
  have a := updA (P := P) hL hcw hd hlen hdi hdx hcx h8
  refine WP.of_syms (Proof.Pbkdf2.Md.X86_64.Calls.upd_call P.ok.stream a (by omega) fun w' af hr hsy => ?_)
  have hws : ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 0, P.H.stream.S⟩ : Region),
      ⟨L.scr + BitVec.ofNat 64 512, P.ok.stream.Wb⟩], Region.Sub r ⟨L.scr, 2560⟩ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> exact scr_work (by nums)
  have hf' : Frame [⟨L.scr, 2560⟩, ⟨L.B, 24⟩] w.mem w'.mem := af.frame.sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨⟨L.scr, 2560⟩, by simp, hws r hr⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨L.B, 24⟩, by simp, hsp⟩
  have hdata : Spec.Sha256.bytesAt w.mem da len = Spec.Sha256.bytesAt t.mem da len := by
    rw [hmw]
    refine bytesAt_frame hu.frame (fun r hr => ?_) (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa using hd.work hL (e := 0) (k := 2560) (by omega)
    · exact (hd.low hL).symm
  refine ⟨hcw.keep hL af.rd af.wr (af.cs .rsp (by decide)) (fun r hr _ => af.cs r hr) af.frame
      (safe_call hcw (fun r hr => .inr (.inl ((hws r hr).trans (Region.sub_prefix (by omega))))) (by omega)) hsy,
    hu.frame.trans (hmw ▸ hf'), ?_, ?_⟩
  · rw [← hdata]
    exact hr _ (hmw ▸ hu.inner) (by rw [hsi, xorPad_length, blockKey_length (keyOf_length _)])
  · refine P.ok.sh_reloc w.mem w'.mem _ _ _ (fun i hi => ?_) (hmw ▸ hu.outer)
    refine Frame.bytes (R := ⟨L.scr + BitVec.ofNat 64 256, P.H.P.N + P.H.P.B⟩) af.frame (fun r hr => ?_)
      (by show P.H.S ≤ 2 ^ 64; nums) hi
    rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by nums) (by nums) (by nums)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ((hL.low_scr (by nums)).sub_left hsp).symm

/-! ## HMAC's `finalize` -/

theorem finArgs_ok (hL : L.Ok) (hq : HashLay P L) {u : State} (hc : Ctx L g m₀ u) {e dst : Nat} (he : e < 2 ^ 31)
    (hdst : dst < 2 ^ 31) :
    WP isa (.block (Cfg.hmacArgs₃ e dst)) u
      fun u' => Ctx L g m₀ u' ∧ u'.mem = u.mem ∧ u'.gpr .rdi = L.scr + BitVec.ofNat 64 0 ∧
        u'.gpr .rsi = L.scr + BitVec.ofNat 64 256 ∧ u'.gpr .rdx = BitVec.ofNat 64 (P.H.P.B + (P.H.D + e)) ∧
        u'.gpr .rcx = L.B + BitVec.ofNat 64 (24 + dst) ∧ u'.gpr .r8 = L.scr + BitVec.ofNat 64 512 ∧
        u'.gpr .rax = BitVec.ofNat 64 P.k := by
  rw [Cfg.hmacArgs₃, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff,
    WP.block_append_iff]
  refine WP.mono (scr_ok hL hc (d := .rdi) (by decide) (a := 0) (by decide)) fun u₁ h₁ => ?_
  refine WP.mono (scr_ok hL h₁.ctx (d := .rsi) (by decide) (a := 256) (by decide)) fun u₂ h₂ => ?_
  rw [show ([.mov .rdx (.mem (stk fBS)), .alu .add .rdx (.mem (stk fHL)), .alu .add .rdx (.imm (BitVec.ofNat 32 e))] :
    List Instr) = [.mov .rdx (.mem (stk fBS)), .alu .add .rdx (.mem (stk fHL))] ++
      [.alu .add .rdx (.imm (BitVec.ofNat 32 e))] from rfl, WP.block_append_iff]
  rw [show ([.mov .rdx (.mem (stk fBS)), .alu .add .rdx (.mem (stk fHL))] : List Instr) =
    [.mov .rdx (.mem (stk fBS))] ++ [.alu .add .rdx (.mem (stk fHL))] from rfl, WP.block_append_iff]
  refine WP.mono (ldBS_ok hL hq h₂.ctx (d := .rdx) (by decide)) fun u₃₀ h₃₀ => ?_
  refine WP.mono (addHL_ok hL hq h₃₀.ctx (d := .rdx) (by decide)) fun u₃ h₃ => ?_
  refine WP.mono (addImm_ok hL h₃.ctx (d := .rdx) (by decide) he) fun u₃' h₃' => ?_
  refine WP.mono (fr_ok hL h₃'.ctx (d := .rcx) (by decide) hdst) fun u₄ h₄ => ?_
  refine WP.mono (scr_ok hL h₄.ctx (d := .r8) (by decide) (a := 512) (by decide)) fun u₅ h₅ => ?_
  refine WP.mono (ldSel_ok hL hq h₅.ctx) fun u₆ h₆ => ?_
  refine ⟨h₆.ctx, by rw [h₆.mem, h₅.mem, h₄.mem, h₃'.mem, h₃.mem, h₃₀.mem, h₂.mem, h₁.mem], ?_, ?_, ?_, ?_, ?_,
    h₆.val⟩
  · rw [h₆.keep _ (by decide), h₅.keep _ (by decide), h₄.keep _ (by decide), h₃'.keep _ (by decide),
      h₃.keep _ (by decide), h₃₀.keep _ (by decide), h₂.keep _ (by decide), h₁.val]
  · rw [h₆.keep _ (by decide), h₅.keep _ (by decide), h₄.keep _ (by decide), h₃'.keep _ (by decide),
      h₃.keep _ (by decide), h₃₀.keep _ (by decide), h₂.val]
  · rw [h₆.keep _ (by decide), h₅.keep _ (by decide), h₄.keep _ (by decide), h₃'.val, h₃.val, h₃₀.val,
      BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat, Nat.add_assoc]
  · rw [h₆.keep _ (by decide), h₅.keep _ (by decide), h₄.val]
  · rw [h₆.keep _ (by decide), h₅.val]

/-- After HMAC's `finalize`: the MAC in the frame at `dst`. -/
structure Done (P : RfcHash) {dn : Nat} (L : Lay dn) (g : Reg → BitVec 64) (m₀ : Mem) (t : State) (da : Addr)
    (len dst : Nat) (u : State) : Prop where
  ctx : Ctx L g m₀ u
  frame : Frame [⟨L.scr, 2560⟩, ⟨L.B, 24⟩, ⟨L.B + BitVec.ofNat 64 (24 + dst), P.H.D⟩] t.mem u.mem
  mac : Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (24 + dst)) P.H.D =
    P.mac (keyOf P L t.mem) (Spec.Sha256.bytesAt t.mem da len)

/-- The arguments of HMAC's `finalize`. -/
theorem finA (hL : L.Ok) {w : State} (hcw : Ctx L g m₀ w) {len dst : Nat} (hdst : dst + P.H.D ≤ 168)
    (hdi : w.gpr .rdi = L.scr + BitVec.ofNat 64 0) (hsi : w.gpr .rsi = L.scr + BitVec.ofNat 64 256)
    (hdx : w.gpr .rdx = BitVec.ofNat 64 (P.H.P.B + len)) (hcx : w.gpr .rcx = L.B + BitVec.ofNat 64 (24 + dst))
    (h8 : w.gpr .r8 = L.scr + BitVec.ofNat 64 512) :
    Proof.Pbkdf2.Md.X86_64.Pbk.FinArgs (H := P.H) w (L.scr + BitVec.ofNat 64 0)
      (L.scr + BitVec.ofNat 64 256) (BitVec.ofNat 64 (P.H.P.B + len)) (L.B + BitVec.ofNat 64 (24 + dst))
      (L.scr + BitVec.ofNat 64 512) := by
  have hsp : below (w.gpr .rsp) 24 = ⟨L.B, 24⟩ := by rw [hcw.rsp, below24]
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

theorem fin_step (hL : L.Ok) (hq : HashLay P L) {t u : State} {da : Addr} {e dst : Nat}
    (hu : Updated P L g m₀ t da (P.H.D + e) u) (hlen : P.H.D + e ≤ 256) (hdst : dst + P.H.D ≤ 168) :
    WP isa (.seq (.block (Cfg.hmacArgs₃ e dst)) ((cfgOf P).callH fun H => (H.hmacFinN, H.hmacFin))) u
      (Done P L g m₀ t da (P.H.D + e) dst) := by
  refine WP.seq (WP.mono (finArgs_ok hL hq hu.ctx (e := e) (dst := dst) (by omega) (by omega))
    fun w₀ ⟨hcw₀, hmw₀, hdi₀, hsi₀, hdx₀, hcx₀, h8₀, hax⟩ => callH_ok P hax fun w hf => ?_)
  have hcw := hcw₀.flags hL hf
  have hmw : w.mem = u.mem := hf.mem.trans hmw₀
  have hdi := (hf.gpr .rdi).trans hdi₀
  have hsi := (hf.gpr .rsi).trans hsi₀
  have hdx := (hf.gpr .rdx).trans hdx₀
  have hcx := (hf.gpr .rcx).trans hcx₀
  have h8 := (hf.gpr .r8).trans h8₀
  generalize P.H.D + e = len at hu hlen hdx ⊢
  have hsp : below (w.gpr .rsp) 24 = ⟨L.B, 24⟩ := by rw [hcw.rsp, below24]
  have a := finA (P := P) hL hcw (len := len) hdst hdi hsi hdx hcx h8
  refine WP.of_syms (Proof.Pbkdf2.Md.X86_64.Pbk.hfin_call P.ok P.hF P.hFsp P.hFd a
    fun w' hrd hwr hcs hf hpost hsy => ?_)
  have hws : ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 0, P.H.S⟩ : Region),
      ⟨L.B + BitVec.ofNat 64 (24 + dst), P.H.D⟩, ⟨L.scr + BitVec.ofNat 64 512, 8 * P.H.W⟩] ++
      [below (w.gpr .rsp) 24], ∃ r' ∈ [(⟨L.scr, 2560⟩ : Region), ⟨L.B, 24⟩,
        ⟨L.B + BitVec.ofNat 64 (24 + dst), P.H.D⟩], Region.Sub r r' := by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, hsp]
    rintro r (rfl | rfl | rfl | rfl)
    · exact ⟨⟨L.scr, 2560⟩, by simp, scr_work (by nums)⟩
    · exact ⟨⟨L.B + BitVec.ofNat 64 (24 + dst), P.H.D⟩, by simp, sub_refl _⟩
    · exact ⟨⟨L.scr, 2560⟩, by simp, scr_work (by nums)⟩
    · exact ⟨⟨L.B, 24⟩, by simp, sub_refl _⟩
  have hl : (Spec.Sha256.bytesAt t.mem da len).length = len := by simp [Spec.Sha256.bytesAt]
  refine ⟨hcw.keep hL hrd hwr (hcs .rsp (by decide)) (fun r hr _ => hcs r hr) hf (hsy := hsy) fun r hr => ?_,
    hu.frame.sub (fun r hr => ⟨r, by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h],
      sub_refl _⟩) |>.trans (hmw ▸ hf.sub hws), ?_⟩
  · obtain ⟨r', hr', hs⟩ := hws r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · exact .inr (.inl (hs.trans (Region.sub_prefix (by omega))))
    · exact .inr (.inr (.inl (hs.trans (Region.sub_prefix (by omega)))))
    · exact (safe_low L (by omega)).of_sub hs
  · have hk := blockKey_length (P := P) (keyOf_length (L := L) t.mem)
    exact hpost _ _ hk (by rw [hk, hl]; nums)
      (hmw ▸ hu.inner) (by rw [hl]) (hmw ▸ hu.outer)

/-! ## The whole HMAC -/

theorem seq_seq {a b c : Prog isa} {s : State} {P Q : State → Prop} (h : WP isa (.seq a b) s P)
    (hc : ∀ s', P s' → WP isa c s' Q) : WP isa (.seq a (.seq b c)) s Q := by
  rw [WP.seq_iff] at h ⊢
  refine WP.mono h fun s₁ h₁ => ?_
  rw [WP.seq_iff]
  exact WP.mono h₁ hc

/-- `HMAC_K(data)`, for the key `K` in the frame, to the frame at `dst`. -/
theorem hmac_ok (hL : L.Ok) (hq : HashLay P L) {t : State} (hc : Ctx L g m₀ t) {dataA : List Instr} {da : Addr}
    {e dst : Nat} (hdA : ∀ u, Ctx L g m₀ u → WP isa (.block dataA) u (Upd L g m₀ u .rdx da))
    (hd : DataOk L da (P.H.D + e)) (hlen : P.H.D + e ≤ 256) (hdst : dst + P.H.D ≤ 168) :
    WP isa ((cfgOf P).hmac dataA e dst) t (Done P L g m₀ t da (P.H.D + e) dst) :=
  seq_seq (init_step hL hq hc) fun _ hu => seq_seq (upd_step hL hq hu hdA hd hlen) fun _ hw =>
    fin_step hL hq hw hlen hdst

end VG.Proof.Ecdsa.Rfc6979.X86_64
