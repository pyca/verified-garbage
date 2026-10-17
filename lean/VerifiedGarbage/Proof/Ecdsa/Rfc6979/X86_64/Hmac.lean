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
each a call of the tier's function (`Proof/Hmac/Any/X86_64/Calls.lean`) with
`P`'s number, with the lengths from the frame's numbers of the hash function
(`HashLay`). They change only HMAC's states and working space (the first 2560
bytes of `scratch`), the 32 bytes below the frame, and the 64 bytes at `dst`
(`hmac_ok`).
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

theorem low (hd : DataOk L da len) (hL : L.Ok) : Region.Disjoint L.CALLS ⟨da, len⟩ := by
  rcases hd with ⟨o, rfl, h₁, h₂⟩ | ⟨o, rfl, h₁, h₂⟩
  · rw [L.shift]; exact Offset.base_disjoint _ (by omega) (by omega)
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

theorem ldArg_ok (hL : L.Ok) (hq : HashLay P L) {u : State} (hc : Ctx L g m₀ u) :
    WP isa (.block Cfg.selArg) u (Upd L g m₀ u .r9 (BitVec.ofNat 64 P.k)) :=
  WP.mono (ld_ok hL hc (d := .r9) (by decide) (o := fSel) (by decide)) fun _ h =>
    { h with val := h.val.trans (hq.1 ▸ hc.pSel) }

/-- `hash`, as the tier's functions take it. -/
theorem r9_toNat {u : State} (h : u.gpr .r9 = BitVec.ofNat 64 P.k) : (u.gpr .r9).toNat = P.k := by
  rw [h, BitVec.toNat_ofNat]; have := hashIds_lt P.hk; omega

/-- The stack the calls use is apart from the frame above it. -/
theorem calls_fr {d n : Nat} (h₁ : 24 ≤ d) (h₂ : d + n ≤ 2 ^ 63) : Region.Disjoint L.CALLS ⟨L.B + BitVec.ofNat 64 d, n⟩ := by
  rw [L.shift]; exact Offset.base_disjoint _ (by omega) (by omega)

/-- `d ← d + D`. -/
theorem addHL_ok (hL : L.Ok) (hq : HashLay P L) {u : State} (hc : Ctx L g m₀ u) {d : Reg} (hd : d ∉ calleeSaved) :
    WP isa (.block [.alu .add d (.mem (stk fHL))]) u (Upd L g m₀ u d (u.gpr d + BitVec.ofNat 64 P.H.D)) :=
  WP.mono (addMem_ok hL hc hd (o := fHL) (by decide)) fun _ h =>
    { h with val := h.val.trans (congrArg (u.gpr d + ·) (hq.2.1 ▸ hc.pHL)) }

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
      t'.gpr .r8 = L.scr + BitVec.ofNat 64 512 ∧ t'.gpr .r9 = BitVec.ofNat 64 P.k := by
  rw [Cfg.hmacArgs₁, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff,
    WP.block_append_iff]
  refine WP.mono (scr_ok hL hc (d := .rdi) (by decide) (a := 0) (by decide)) fun u₁ h₁ => ?_
  refine WP.mono (scr_ok hL h₁.ctx (d := .rsi) (by decide) (a := 256) (by decide)) fun u₂ h₂ => ?_
  refine WP.mono (fr_ok hL h₂.ctx (d := .rdx) (by decide) (o := 0) (by decide)) fun u₃ h₃ => ?_
  refine WP.mono (ldHL_ok hL hq h₃.ctx (d := .rcx) (by decide)) fun u₄ h₄ => ?_
  refine WP.mono (scr_ok hL h₄.ctx (d := .r8) (by decide) (a := 512) (by decide)) fun u₅ h₅ => ?_
  refine WP.mono (ldArg_ok hL hq h₅.ctx) fun u₆ h₆ => ?_
  refine ⟨h₆.ctx, by rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem], ?_, ?_, ?_, ?_, ?_, h₆.val⟩
  · rw [h₆.keep _ (by decide), h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide),
      h₂.keep _ (by decide), h₁.val]
  · rw [h₆.keep _ (by decide), h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.val]
  · rw [h₆.keep _ (by decide), h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.val]
  · rw [h₆.keep _ (by decide), h₅.keep _ (by decide), h₄.val]
  · rw [h₆.keep _ (by decide), h₅.val]

/-- The writes of a call, within HMAC's working space and the stack below the frame. -/
theorem safe_call {u : State} (hc : Ctx L g m₀ u) {ws : List Region} (hs : ∀ r ∈ ws, Safe L r) {n : Nat}
    (hn : n ≤ 32) : ∀ r ∈ ws ++ [below (u.gpr .rsp) n], Safe L r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact hs r hr
  · simp only [List.mem_singleton] at hr; subst hr
    exact (safe_calls L).of_sub (hc.below_sub hn)

/-- The key `K`: the first `D` bytes of the frame. -/
abbrev keyOf (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) : List Byte :=
  Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 24) P.H.D

/-- After HMAC's `init`: HMAC's states for the key `K` in the frame on entry `t`. -/
structure Inited (P : RfcHash) {dn : Nat} (L : Lay dn) (g : Reg → BitVec 64) (m₀ : Mem) (t u : State) : Prop where
  ctx : Ctx L g m₀ u
  frame : Frame [⟨L.scr, 2560⟩, L.CALLS] t.mem u.mem
  inner : P.ok.SH.Repr u.mem (L.scr + BitVec.ofNat 64 0)
    (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.ok.SH.H (keyOf P L t.mem)) Spec.Hmac.ipad)
  outer : P.ok.SH.Repr u.mem (L.scr + BitVec.ofNat 64 256)
    (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.ok.SH.H (keyOf P L t.mem)) Spec.Hmac.opad)

theorem scr_work {e k : Nat} (h : e + k ≤ 2560) : Region.Sub ⟨L.scr + BitVec.ofNat 64 e, k⟩ ⟨L.scr, 2560⟩ :=
  Offset.sub_base _ h

/-- HMAC's buffers in `scratch`: the states, and the working space. -/
theorem hbufs_scr : ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 0, 192⟩ : Region), ⟨L.scr + BitVec.ofNat 64 256, 192⟩,
    ⟨L.scr + BitVec.ofNat 64 512, 8 * 234⟩], Region.Sub r ⟨L.scr, 2560⟩ := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl) <;> exact scr_work (by omega)

theorem initA (hL : L.Ok) {u : State} (hcu : Ctx L g m₀ u) (hdi : u.gpr .rdi = L.scr + BitVec.ofNat 64 0)
    (hsi : u.gpr .rsi = L.scr + BitVec.ofNat 64 256) (hdx : u.gpr .rdx = L.B + BitVec.ofNat 64 24)
    (hcx : u.gpr .rcx = BitVec.ofNat 64 P.H.D) (h8 : u.gpr .r8 = L.scr + BitVec.ofNat 64 512)
    (h9 : u.gpr .r9 = BitVec.ofNat 64 P.k) :
    Proof.Hmac.Any.X86_64.InitA u (L.scr + BitVec.ofNat 64 0) (L.scr + BitVec.ofNat 64 256)
      (L.B + BitVec.ofNat 64 24) (L.scr + BitVec.ofNat 64 512) P.H.D P.k := by
  have hsp : below (u.gpr .rsp) 32 = L.CALLS := by rw [hcu.rsp, below32]
  exact
    { rdi := hdi, rsi := hsi, rdx := hdx, rcx := by rw [hcx, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by nums)
      r8 := h8, r9 := r9_toNat h9, hsel := P.hsel
      klB := fun I hI => by
        rw [P.inst_eq] at hI; cases hI
        rw [P.iS, P.ok.hB]; nums
      cr := hcu.covers fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨L.FR, by simp, within_fr _ (by omega) (by nums)⟩
      cw := hcu.coversW fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> exact ⟨L.SCR, by simp, within_off _ (by omega)⟩
      i_o := Offset.disjoint _ (by omega) (by omega) (by omega)
      i_s := Offset.disjoint _ (by omega) (by omega) (by omega)
      o_s := Offset.disjoint _ (by omega) (by omega) (by omega)
      k_i := hL.stk_scr (by nums) (by omega)
      k_o := hL.stk_scr (by nums) (by omega)
      k_s := hL.stk_scr (by nums) (by omega)
      stk_i := by rw [hsp]; exact hL.low_scr (by omega)
      stk_o := by rw [hsp]; exact hL.low_scr (by omega)
      stk_k := by rw [hsp]; exact calls_fr (by omega) (by nums)
      stk_s := by rw [hsp]; exact hL.low_scr (by omega)
      scnw := by rw [toNat_add_of (by have := hL.nc; omega)]; have := hL.nc; omega }

theorem init_step (hL : L.Ok) (hq : HashLay P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.seq (.block Cfg.hmacArgs₁) (.call (cfgOf P).initN (cfgOf P).initC)) t (Inited P L g m₀ t) := by
  refine WP.seq (WP.mono (initArgs_ok hL hq hc) fun u ⟨hcu, hmu, hdi, hsi, hdx, hcx, h8, h9⟩ => ?_)
  have a := initA (P := P) hL hcu hdi hsi hdx hcx h8 h9
  refine WP.of_syms (Proof.Hmac.Any.X86_64.init_call P.T a fun u' hrd hwr hcs hf hpost hsy => ?_)
  obtain ⟨hi, ho⟩ := hpost _ P.inst_eq
  rw [P.iS, hmu] at hi ho
  refine ⟨hcu.keep hL hrd hwr (hcs .rsp (by decide)) (fun r hr _ => hcs r hr) hf
    (safe_call hcu (fun r hr => .inr (.inl ((hbufs_scr r hr).trans (Region.sub_prefix (by omega))))) (Nat.le_refl _))
    hsy,
    hmu ▸ hf.sub fun r hr => ?_, hi, ho⟩
  rcases List.mem_append.mp hr with hr | hr
  · exact ⟨⟨L.scr, 2560⟩, by simp, hbufs_scr r hr⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨L.CALLS, by simp, hcu.below_sub (Nat.le_refl _)⟩

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
      u'.gpr .r9 = BitVec.ofNat 64 P.k := by
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
  refine WP.mono (ldArg_ok hL hq h₅.ctx) fun u₆ h₆ => ?_
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
  frame : Frame [⟨L.scr, 2560⟩, L.CALLS] t.mem u.mem
  inner : P.ok.SH.Repr u.mem (L.scr + BitVec.ofNat 64 0)
    (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.ok.SH.H (keyOf P L t.mem)) Spec.Hmac.ipad ++
      Spec.Sha256.bytesAt t.mem da len)
  outer : P.ok.SH.Repr u.mem (L.scr + BitVec.ofNat 64 256)
    (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.ok.SH.H (keyOf P L t.mem)) Spec.Hmac.opad)

/-- The arguments of the streaming `update`. -/
theorem updA (hL : L.Ok) {w : State} (hcw : Ctx L g m₀ w) {da : Addr} {len : Nat} (hd : DataOk L da len)
    (hdi : w.gpr .rdi = L.scr + BitVec.ofNat 64 0) (hsi : w.gpr .rsi = BitVec.ofNat 64 P.H.P.B)
    (hdx : w.gpr .rdx = da) (hcx : w.gpr .rcx = BitVec.ofNat 64 len) (hlen : len ≤ 256)
    (h8 : w.gpr .r8 = L.scr + BitVec.ofNat 64 512) (h9 : w.gpr .r9 = BitVec.ofNat 64 P.k) :
    Proof.Hmac.Any.X86_64.UpdA w (L.scr + BitVec.ofNat 64 0) (BitVec.ofNat 64 P.H.P.B) da
      (L.scr + BitVec.ofNat 64 512) len P.k := by
  have hsp : Region.Sub (below (w.gpr .rsp) 24) L.CALLS := hcw.below_sub (by omega)
  exact
    { rdi := hdi, rsi := hsi, rdx := hdx, rcx := by rw [hcx, BitVec.toNat_ofNat]; omega, r8 := h8
      r9 := r9_toNat h9, hsel := P.hsel
      cd := hcw.covers fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hd.within
      cw := hcw.coversW fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact ⟨L.SCR, by simp, within_off _ (by omega)⟩
      st_sc := Offset.disjoint _ (by omega) (by omega) (by omega)
      d_st := hd.work hL (by omega)
      d_sc := hd.work hL (by omega)
      stk_st := (hL.low_scr (by omega)).sub_left hsp
      stk_d := (hd.low hL).sub_left hsp
      stk_sc := (hL.low_scr (by omega)).sub_left hsp }

theorem upd_step (hL : L.Ok) (hq : HashLay P L) {t u : State} (hu : Inited P L g m₀ t u) {dataA : List Instr}
    {da : Addr} {e : Nat} (hdA : ∀ u, Ctx L g m₀ u → WP isa (.block dataA) u (Upd L g m₀ u .rdx da))
    (hd : DataOk L da (P.H.D + e)) (hlen : P.H.D + e ≤ 256) :
    WP isa (.seq (.block (Cfg.hmacArgs₂ dataA e)) (.call (cfgOf P).updN (cfgOf P).updC)) u
      (Updated P L g m₀ t da (P.H.D + e)) := by
  refine WP.seq (WP.mono (updArgs_ok hL hq hu.ctx hdA (e := e) (by omega))
    fun w ⟨hcw, hmw, hdi, hsi, hdx, hcx, h8, h9⟩ => ?_)
  generalize P.H.D + e = len at hd hlen hcx ⊢
  have hsp : Region.Sub (below (w.gpr .rsp) 24) L.CALLS := hcw.below_sub (by omega)
  have a := updA (P := P) hL hcw hd hdi hsi hdx hcx hlen h8 h9
  refine WP.of_syms (Proof.Hmac.Any.X86_64.upd_call P.T a fun w' hrd hwr hcs hfr hpost hsy => ?_)
  have hws : ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 0, 192⟩ : Region), ⟨L.scr + BitVec.ofNat 64 512, 8 * 234⟩],
      Region.Sub r ⟨L.scr, 2560⟩ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> exact scr_work (by omega)
  have hf' : Frame [⟨L.scr, 2560⟩, L.CALLS] w.mem w'.mem := hfr.sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨⟨L.scr, 2560⟩, by simp, hws r hr⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨L.CALLS, by simp, hsp⟩
  have hdata : Spec.Sha256.bytesAt w.mem da len = Spec.Sha256.bytesAt t.mem da len := by
    rw [hmw]
    refine bytesAt_frame hu.frame (fun r hr => ?_) (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa using hd.work hL (e := 0) (k := 2560) (by omega)
    · exact (hd.low hL).symm
  have hr := hpost _ P.inst_eq
  rw [P.iS] at hr
  refine ⟨hcw.keep hL hrd hwr (hcs .rsp (by decide)) (fun r hr _ => hcs r hr) hfr
      (safe_call hcw (fun r hr => .inr (.inl ((hws r hr).trans (Region.sub_prefix (by omega))))) (by omega)) hsy,
    hu.frame.trans (hmw ▸ hf'), ?_, ?_⟩
  · rw [← hdata]
    exact hr _ (hmw ▸ hu.inner) (by rw [xorPad_length, blockKey_length (keyOf_length _)])
  · refine P.ok.sh_reloc w.mem w'.mem _ _ _ (fun i hi => ?_) (hmw ▸ hu.outer)
    refine Frame.bytes (R := ⟨L.scr + BitVec.ofNat 64 256, P.H.P.N + P.H.P.B⟩) hfr (fun r hr => ?_)
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
        u'.gpr .r9 = BitVec.ofNat 64 P.k := by
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
  refine WP.mono (ldArg_ok hL hq h₅.ctx) fun u₆ h₆ => ?_
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
  frame : Frame [⟨L.scr, 2560⟩, L.CALLS, ⟨L.B + BitVec.ofNat 64 (24 + dst), 64⟩] t.mem u.mem
  mac : Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (24 + dst)) P.H.D =
    P.mac (keyOf P L t.mem) (Spec.Sha256.bytesAt t.mem da len)

/-- The arguments of HMAC's `finalize`. -/
theorem finA (hL : L.Ok) {w : State} (hcw : Ctx L g m₀ w) {len dst : Nat} (hdst : dst + 64 ≤ 128)
    (hdi : w.gpr .rdi = L.scr + BitVec.ofNat 64 0) (hsi : w.gpr .rsi = L.scr + BitVec.ofNat 64 256)
    (hdx : w.gpr .rdx = BitVec.ofNat 64 (P.H.P.B + len)) (hcx : w.gpr .rcx = L.B + BitVec.ofNat 64 (24 + dst))
    (h8 : w.gpr .r8 = L.scr + BitVec.ofNat 64 512) (h9 : w.gpr .r9 = BitVec.ofNat 64 P.k) :
    Proof.Hmac.Any.X86_64.FinA w (L.scr + BitVec.ofNat 64 0)
      (L.scr + BitVec.ofNat 64 256) (BitVec.ofNat 64 (P.H.P.B + len)) (L.B + BitVec.ofNat 64 (24 + dst))
      (L.scr + BitVec.ofNat 64 512) P.k := by
  have hsp : below (w.gpr .rsp) 32 = L.CALLS := by rw [hcw.rsp, below32]
  exact
    { rdi := hdi, rsi := hsi, rdx := hdx, rcx := hcx, r8 := h8, r9 := r9_toNat h9, hsel := P.hsel
      cr := hcw.covers fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨L.SCR, by simp, within_off _ (by omega)⟩
      cw := hcw.coversW fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨L.SCR, by simp, within_off _ (by omega)⟩
        · exact ⟨L.FR, by simp, within_fr _ (by omega) (by have := L.he; omega)⟩
        · exact ⟨L.SCR, by simp, within_off _ (by omega)⟩
      i_u := Offset.disjoint _ (by omega) (by omega) (by omega)
      i_o := (hL.stk_scr (d := 24 + dst) (by have := L.he; omega) (by omega)).symm
      i_s := Offset.disjoint _ (by omega) (by omega) (by omega)
      u_o := (hL.stk_scr (d := 24 + dst) (by have := L.he; omega) (by omega)).symm
      u_s := Offset.disjoint _ (by omega) (by omega) (by omega)
      o_s := hL.stk_scr (by have := L.he; omega) (by omega)
      stk_i := by rw [hsp]; exact hL.low_scr (by omega)
      stk_u := by rw [hsp]; exact hL.low_scr (by omega)
      stk_o := by rw [hsp]; exact calls_fr (by omega) (by omega)
      stk_s := by rw [hsp]; exact hL.low_scr (by omega)
      scnw := by rw [toNat_add_of (by have := hL.nc; omega)]; have := hL.nc; omega }

theorem fin_step (hL : L.Ok) (hq : HashLay P L) {t u : State} {da : Addr} {e dst : Nat}
    (hu : Updated P L g m₀ t da (P.H.D + e) u) (hlen : P.H.D + e ≤ 256) (hdst : dst + 64 ≤ 128) :
    WP isa (.seq (.block (Cfg.hmacArgs₃ e dst)) (.call (cfgOf P).finN (cfgOf P).finC)) u
      (Done P L g m₀ t da (P.H.D + e) dst) := by
  refine WP.seq (WP.mono (finArgs_ok hL hq hu.ctx (e := e) (dst := dst) (by omega) (by omega))
    fun w ⟨hcw, hmw, hdi, hsi, hdx, hcx, h8, h9⟩ => ?_)
  generalize P.H.D + e = len at hu hlen hdx ⊢
  have hsp : below (w.gpr .rsp) 32 = L.CALLS := by rw [hcw.rsp, below32]
  have a := finA (P := P) hL hcw (len := len) hdst hdi hsi hdx hcx h8 h9
  refine WP.of_syms (Proof.Hmac.Any.X86_64.fin_call P.T a fun w' hrd hwr hcs hf hpost hsy => ?_)
  have hws : ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 0, 192⟩ : Region),
      ⟨L.B + BitVec.ofNat 64 (24 + dst), 64⟩, ⟨L.scr + BitVec.ofNat 64 512, 8 * 234⟩] ++
      [below (w.gpr .rsp) 32], ∃ r' ∈ [(⟨L.scr, 2560⟩ : Region), L.CALLS,
        ⟨L.B + BitVec.ofNat 64 (24 + dst), 64⟩], Region.Sub r r' := by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, hsp]
    rintro r (rfl | rfl | rfl | rfl)
    · exact ⟨⟨L.scr, 2560⟩, by simp, scr_work (by omega)⟩
    · exact ⟨⟨L.B + BitVec.ofNat 64 (24 + dst), 64⟩, by simp, sub_refl _⟩
    · exact ⟨⟨L.scr, 2560⟩, by simp, scr_work (by omega)⟩
    · exact ⟨L.CALLS, by simp, sub_refl _⟩
  have hl : (Spec.Sha256.bytesAt t.mem da len).length = len := by simp [Spec.Sha256.bytesAt]
  have hp := hpost _ P.inst_eq
  rw [P.iS, P.ok.hD] at hp
  refine ⟨hcw.keep hL hrd hwr (hcs .rsp (by decide)) (fun r hr _ => hcs r hr) hf (hsy := hsy) fun r hr => ?_,
    hu.frame.sub (fun r hr => ⟨r, by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h],
      sub_refl _⟩) |>.trans (hmw ▸ hf.sub hws), ?_⟩
  · obtain ⟨r', hr', hs⟩ := hws r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · exact .inr (.inl (hs.trans (Region.sub_prefix (by omega))))
    · exact (safe_calls L).of_sub hs
    · exact (safe_low L (by omega)).of_sub hs
  · have hk := blockKey_length (P := P) (keyOf_length (L := L) t.mem)
    exact hp _ _ (hk.trans P.ok.hB.symm) (by rw [hk, hl]; nums)
      (hmw ▸ hu.inner) (by rw [hl, P.ok.hB]) (hmw ▸ hu.outer)

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
    (hd : DataOk L da (P.H.D + e)) (hlen : P.H.D + e ≤ 256) (hdst : dst + 64 ≤ 128) :
    WP isa ((cfgOf P).hmac dataA e dst) t (Done P L g m₀ t da (P.H.D + e) dst) :=
  seq_seq (init_step hL hq hc) fun _ hu => seq_seq (upd_step hL hq hu hdA hd hlen) fun _ hw =>
    fin_step hL hq hw hlen hdst

end VG.Proof.Ecdsa.Rfc6979.X86_64
