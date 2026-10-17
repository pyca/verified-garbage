module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Hash
public import VerifiedGarbage.Proof.Framework.AArch64.Dispatch
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs

/-!
# Deterministic ECDSA on AArch64: one HMAC

`HMAC_K(data)` (`Cfg.hmac`), for the key `K` (of the hash function's output
length) in the frame and `len` bytes of data in the frame or in `scratch`
above HMAC's working space (`DataOk`), written to the frame at `dst`: HMAC's
`init` with `K` (`init_step`), the streaming `update` on the inner state
(`upd_step`), and HMAC's `finalize` (`fin_step`), for any hash function `P`,
each called through the dispatch on the hash function's number (`disp_wp`:
the one of `P`), with the sizes `D` and `B` loaded from the frame. They
change only HMAC's states and working space (the first 2432 bytes of
`scratch`), the 16 bytes below the frame, and `dst` (`hmac_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64
open VG.Proof.Pbkdf2.Md.AArch64.Calls (After)

/-- Where the data may be: in the frame below its pointers, or in `scratch`
above HMAC's working space. -/
def DataOk {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (da : Addr) (len : Nat) : Prop :=
  (∃ o, da = L.B + BitVec.ofNat 64 o ∧ 16 ≤ o ∧ o + len ≤ 216) ∨
    (∃ o, da = L.scr + BitVec.ofNat 64 o ∧ 2432 ≤ o ∧ o + len ≤ 8192)

variable {P : RfcHash} {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} {L : Lay dn E} {g : Reg → BitVec 64} {m₀ : Mem}

namespace DataOk

variable {da : Addr} {len : Nat}

theorem low (hd : DataOk L da len) (hL : L.Ok) : Region.Disjoint ⟨L.B, 16⟩ ⟨da, len⟩ := by
  rcases hd with ⟨o, rfl, h₁, h₂⟩ | ⟨o, rfl, h₁, h₂⟩
  · exact Offset.base_disjoint _ h₁ (by omega)
  · exact hL.low_scr h₂

/-- The data is apart from HMAC's states and working space. -/
theorem work (hd : DataOk L da len) (hL : L.Ok) {e k : Nat} (h : e + k ≤ 2432) :
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

/-- The frame's facts for the hash function `P`: its number and its block size. -/
def HashOk (P : RfcHash) {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) : Prop :=
  L.sel = P.k ∧ L.bl = P.H.P.B

/-! ## The dispatch -/

theorem Ctx.writesOnly {u u' : State} (hL : L.Ok) (hc : Ctx L g m₀ u) {t : Reg} (ht : t ∉ preserved)
    (hw : Dispatch.AArch64.WritesOnly t u u') : Ctx L g m₀ u' := by
  obtain ⟨v, rfl⟩ := hw
  exact hc.set hL ht rfl rfl rfl rfl (fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr) rfl

theorem keys_disp (f : Nat → Prog isa) :
    Dispatch.keys (hashIds.map fun k => (k, f k)) = hashIds := by
  simp [Dispatch.keys, List.map_map, Function.comp_def]

/-- `f` of `P`'s hash function, which the dispatch on its number (in `x9`)
runs, from a state differing in `x10` alone. -/
theorem disp_wp (P : RfcHash) {f : Impl.Pbkdf2.Md.AArch64.Hash → Prog isa} {s : State} {Q : State → Prop}
    (h9 : s.gpr .x9 = BitVec.ofNat 64 P.k)
    (h : ∀ s', Dispatch.AArch64.WritesOnly .x10 s s' → WP isa (f P.H) s' Q) :
    WP isa ((cfgOf P).disp f) s Q := by
  have hk : P.k ∈ hashIds := by
    have := P.hk; simp only [Spec.Ecdsa.Rfc6979.hashIds, List.mem_cons] at this; simp only [hashIds, List.mem_cons]
    exact this
  have hsel : Dispatch.AArch64.sel .x9 s = P.k := by
    simp only [Dispatch.AArch64.sel, h9, BitVec.toNat_ofNat]; have := P.k8; omega
  refine Dispatch.chain_wp (Dispatch.AArch64.tests .x10 .x9 (by decide)) _ ?_ ?_ ?_ fun c hc s' hr _ => ?_
  · rw [keys_disp]; decide
  · rw [keys_disp, hsel]; exact hk
  · rw [keys_disp]; decide
  · rw [hsel] at hc
    obtain ⟨a, -, ha⟩ := List.mem_map.mp hc
    simp only [Prod.mk.injEq] at ha
    obtain ⟨rfl, rfl⟩ := ha
    simp only [hs_k]
    exact h s' hr

theorem Ctx.sp16 (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) : 16 ≤ u.sp.toNat := by
  rw [hc.sp, toNat_add_of (by have := hL.nB; omega)]; omega

/-! ## HMAC's `init` -/

/-- The arguments of HMAC's `init`, and the selector. -/
theorem initArgs_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.hmacArgs₁) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧
      t'.gpr .x0 = L.scr + BitVec.ofNat 64 0 ∧ t'.gpr .x1 = L.scr + BitVec.ofNat 64 192 ∧
      t'.gpr .x2 = L.B + BitVec.ofNat 64 16 ∧ t'.gpr .x3 = BitVec.ofNat 64 dn ∧
      t'.gpr .x4 = L.scr + BitVec.ofNat 64 384 ∧ t'.gpr .x9 = BitVec.ofNat 64 L.sel := by
  rw [Cfg.hmacArgs₁, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff,
    WP.block_append_iff]
  refine WP.mono (scr_ok hL hc (d := .x0) (by decide) (a := 0) (by decide)) fun u₁ h₁ => ?_
  refine WP.mono (scr_ok hL h₁.ctx (d := .x1) (by decide) (a := 192) (by decide)) fun u₂ h₂ => ?_
  refine WP.mono (fr_ok hL h₂.ctx (d := .x2) (by decide) (o := 0) (by decide)) fun u₃ h₃ => ?_
  refine WP.mono (ldDl_ok hL h₃.ctx (d := .x3) (by decide)) fun u₄ h₄ => ?_
  refine WP.mono (scr_ok hL h₄.ctx (d := .x4) (by decide) (a := 384) (by decide)) fun u₅ h₅ => ?_
  refine WP.mono (ldSel_ok hL h₅.ctx (d := .x9) (by decide)) fun u₆ h₆ => ?_
  refine ⟨h₆.ctx, by rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem], ?_, ?_, ?_, ?_, ?_, h₆.val⟩
  · rw [h₆.keep _ (by decide), h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide),
      h₂.keep _ (by decide), h₁.val]
  · rw [h₆.keep _ (by decide), h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.val]
  · rw [h₆.keep _ (by decide), h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.val]
  · rw [h₆.keep _ (by decide), h₅.keep _ (by decide), h₄.val]
  · rw [h₆.keep _ (by decide), h₅.val]

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

/-- The key `K`: the first `D` bytes of the frame. -/
abbrev keyOf (P : RfcHash) {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (m : Mem) : List Byte :=
  Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 16) P.H.D

/-- After HMAC's `init`: HMAC's states for the key `K` in the frame on entry `t`. -/
structure Inited (P : RfcHash) {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (g : Reg → BitVec 64) (m₀ : Mem) (t u : State) : Prop where
  ctx : Ctx L g m₀ u
  frame : Frame [⟨L.scr, 2432⟩, ⟨L.B, 16⟩] t.mem u.mem
  inner : P.ok.SH.Repr u.mem (L.scr + BitVec.ofNat 64 0)
    (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.ok.SH.H (keyOf P L t.mem)) Spec.Hmac.ipad)
  outer : P.ok.SH.Repr u.mem (L.scr + BitVec.ofNat 64 192)
    (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.ok.SH.H (keyOf P L t.mem)) Spec.Hmac.opad)

theorem scr_work {e k : Nat} (h : e + k ≤ 2432) : Region.Sub ⟨L.scr + BitVec.ofNat 64 e, k⟩ ⟨L.scr, 2432⟩ :=
  Offset.sub_base _ h

/-- The memory a call changes: within `ws`, each in `⟨scratch, 2432⟩` or in
the 16 bytes below the frame. -/
theorem after_frame {u u' : State} (hc : Ctx L g m₀ u) {ws : List Region} (ha : After u ws u')
    (hs : ∀ r ∈ ws, Region.Sub r ⟨L.scr, 2432⟩) : Frame [⟨L.scr, 2432⟩, ⟨L.B, 16⟩] u.mem u'.mem :=
  ha.frame.sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨⟨L.scr, 2432⟩, by simp, hs r hr⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨L.B, 16⟩, by simp, by rw [hc.below_eq]; exact sub_refl _⟩

theorem initA (hL : L.Ok) {u : State} (hcu : Ctx L g m₀ u) (h0 : u.gpr .x0 = L.scr + BitVec.ofNat 64 0)
    (h1 : u.gpr .x1 = L.scr + BitVec.ofNat 64 192) (h2 : u.gpr .x2 = L.B + BitVec.ofNat 64 16)
    (h3 : u.gpr .x3 = BitVec.ofNat 64 P.H.D) (h4 : u.gpr .x4 = L.scr + BitVec.ofNat 64 384) :
    Proof.Pbkdf2.Md.AArch64.Pbk.InitArgs (H := P.H) u (L.scr + BitVec.ofNat 64 0)
      (L.scr + BitVec.ofNat 64 192) (L.B + BitVec.ofNat 64 16) (L.scr + BitVec.ofNat 64 384) P.H.D := by
  have hsp : below u.sp 16 = ⟨L.B, 16⟩ := hcu.below_eq
  exact
    { x0 := h0, x1 := h1, x2 := h2, x3 := by rw [h3, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by anums)
      x4 := h4, klB := by anums
      cr := hcu.covers fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨L.FR, by simp, within_fr _ (by omega) (by anums)⟩
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
      stk_k := by rw [hsp]; exact Offset.base_disjoint _ (by omega) (by anums)
      stk_s := by rw [hsp]; exact hL.low_scr (by anums)
      scnw := by rw [toNat_add_of (by have := hL.nc; omega)]; have := hL.nc; anums }

theorem WritesOnly.mem' {u u' : State} {t : Reg} (hw : Dispatch.AArch64.WritesOnly t u u') : u'.mem = u.mem :=
  Dispatch.AArch64.WritesOnly.mem hw

theorem init_step (hL : L.Ok) (hdn : dn = P.H.D) (hh : HashOk P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.seq (.block Cfg.hmacArgs₁) ((cfgOf P).disp fun H => .call H.hmacInitN H.hmacInit)) t
      (Inited P L g m₀ t) := by
  refine WP.seq (WP.mono (initArgs_ok hL hc) fun u ⟨hcu, hmu, h0, h1, h2, h3, h4, h9⟩ => ?_)
  refine disp_wp P (by rw [h9, hh.1]) fun w hw => ?_
  have hcw := hcu.writesOnly hL (by decide) hw
  have g : ∀ r, r ≠ .x10 → w.gpr r = u.gpr r := fun r hr => Dispatch.AArch64.WritesOnly.gpr hw hr
  have hmw : w.mem = t.mem := (WritesOnly.mem' hw).trans hmu
  have a := initA (P := P) hL hcw (by rw [g _ (by decide), h0]) (by rw [g _ (by decide), h1])
    (by rw [g _ (by decide), h2]) (by rw [g _ (by decide), h3, hdn]) (by rw [g _ (by decide), h4])
  refine Proof.Pbkdf2.Md.AArch64.Pbk.hinit_call P.ok P.hI P.hId a fun u' ha hi ho => ?_
  have hsafe : ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 0, P.H.S⟩ : Region), ⟨L.scr + BitVec.ofNat 64 192, P.H.S⟩,
      ⟨L.scr + BitVec.ofNat 64 384, 8 * P.H.W⟩], Region.Sub r ⟨L.scr, 2432⟩ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> exact scr_work (by anums)
  exact ⟨hcw.after hL ha fun r hr => .inr (.inl (sub_trans (hsafe r hr) (Region.sub_prefix (by omega)))),
    hmw ▸ after_frame hcw ha hsafe, by rw [← hmw]; exact hi, by rw [← hmw]; exact ho⟩

/-! ## The streaming `update` -/

theorem xorPad_length (k : List Byte) (p : Byte) : (Spec.Hmac.xorPad k p).length = k.length :=
  List.length_map _

theorem blockKey_length {k : List Byte} (hk : k.length = P.H.D) :
    (Spec.Hmac.blockKey P.ok.SH.H k).length = P.H.P.B := by
  have hB := P.ok.hB
  have hDB : P.H.D < P.H.P.B := by anums
  simp only [Spec.Hmac.blockKey, hk, hB, show ¬ P.H.P.B < P.H.D by omega, ite_false, List.length_append,
    List.length_replicate]
  omega

theorem keyOf_length (m : Mem) : (keyOf P L m).length = P.H.D := by simp [keyOf, Spec.Sha256.bytesAt]

/-- `x3 ← D + ex`. -/
theorem dlex_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {d : Reg} (hd : d ∉ preserved) {ex : Nat}
    (hex : ex < 4096) :
    WP isa (.block [.ldrSp d fDl, .addImm .x d d ex]) u (Upd L g m₀ u d (BitVec.ofNat 64 (dn + ex))) := by
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (ldDl_ok hL hc hd) fun u₁ h₁ => WP.mono (addI_ok hL h₁.ctx hd hex) fun u₂ h₂ =>
    ⟨h₂.ctx, h₂.mem.trans h₁.mem, by rw [h₂.val, h₁.val, BitVec.ofNat_add_ofNat], fun r hr => by
      rw [h₂.keep r hr, h₁.keep r hr]⟩

theorem updArgs_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {dataA : List Instr} {da : Addr} {ex : Nat}
    (hdA : ∀ u, Ctx L g m₀ u → WP isa (.block dataA) u (Upd L g m₀ u .x2 da)) (hex : ex < 4096) :
    WP isa (.block (Cfg.hmacArgs₂ dataA ex)) u fun u' => Ctx L g m₀ u' ∧
      u'.mem = u.mem ∧ u'.gpr .x0 = L.scr + BitVec.ofNat 64 0 ∧ u'.gpr .x1 = BitVec.ofNat 64 L.bl ∧
      u'.gpr .x2 = da ∧ u'.gpr .x3 = BitVec.ofNat 64 (dn + ex) ∧ u'.gpr .x4 = L.scr + BitVec.ofNat 64 384 ∧
      u'.gpr .x9 = BitVec.ofNat 64 L.sel := by
  rw [Cfg.hmacArgs₂, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff,
    WP.block_append_iff]
  refine WP.mono (scr_ok hL hc (d := .x0) (by decide) (a := 0) (by decide)) fun u₁ h₁ => ?_
  refine WP.mono (ldBl_ok hL h₁.ctx (d := .x1) (by decide)) fun u₂ h₂ => ?_
  refine WP.mono (hdA u₂ h₂.ctx) fun u₃ h₃ => ?_
  refine WP.mono (dlex_ok hL h₃.ctx (d := .x3) (by decide) hex) fun u₄ h₄ => ?_
  refine WP.mono (scr_ok hL h₄.ctx (d := .x4) (by decide) (a := 384) (by decide)) fun u₅ h₅ => ?_
  refine WP.mono (ldSel_ok hL h₅.ctx (d := .x9) (by decide)) fun u₆ h₆ => ?_
  refine ⟨h₆.ctx, by rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem], ?_, ?_, ?_, ?_, ?_, h₆.val⟩
  · rw [h₆.keep _ (by decide), h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide),
      h₂.keep _ (by decide), h₁.val]
  · rw [h₆.keep _ (by decide), h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.val]
  · rw [h₆.keep _ (by decide), h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.val]
  · rw [h₆.keep _ (by decide), h₅.keep _ (by decide), h₄.val]
  · rw [h₆.keep _ (by decide), h₅.val]

/-- After the streaming `update`: the inner state holds the data too. -/
structure Updated (P : RfcHash) {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (g : Reg → BitVec 64) (m₀ : Mem) (t : State) (da : Addr)
    (len : Nat) (u : State) : Prop where
  ctx : Ctx L g m₀ u
  frame : Frame [⟨L.scr, 2432⟩, ⟨L.B, 16⟩] t.mem u.mem
  inner : P.ok.SH.Repr u.mem (L.scr + BitVec.ofNat 64 0)
    (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.ok.SH.H (keyOf P L t.mem)) Spec.Hmac.ipad ++
      Spec.Sha256.bytesAt t.mem da len)
  outer : P.ok.SH.Repr u.mem (L.scr + BitVec.ofNat 64 192)
    (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.ok.SH.H (keyOf P L t.mem)) Spec.Hmac.opad)

/-- The arguments of the streaming `update`. -/
theorem updA (hL : L.Ok) {w : State} (hcw : Ctx L g m₀ w) {da : Addr} {len : Nat} (hd : DataOk L da len)
    (hlen : len ≤ 256) (h0 : w.gpr .x0 = L.scr + BitVec.ofNat 64 0) (h2 : w.gpr .x2 = da)
    (h3 : w.gpr .x3 = BitVec.ofNat 64 len) (h4 : w.gpr .x4 = L.scr + BitVec.ofNat 64 384) :
    Proof.Pbkdf2.Md.AArch64.Calls.UpdArgs P.ok.stream w (L.scr + BitVec.ofNat 64 0) da
      (L.scr + BitVec.ofNat 64 384) len := by
  have hsp : below w.sp 16 = ⟨L.B, 16⟩ := hcw.below_eq
  exact
    { x0 := h0, x2 := h2, x3 := by rw [h3, BitVec.toNat_ofNat]; omega, x4 := h4
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

theorem upd_step (hL : L.Ok) (hdn : dn = P.H.D) (hh : HashOk P L) {t u : State} (hu : Inited P L g m₀ t u)
    {dataA : List Instr} {da : Addr} {ex : Nat}
    (hdA : ∀ u, Ctx L g m₀ u → WP isa (.block dataA) u (Upd L g m₀ u .x2 da)) (hd : DataOk L da (P.H.D + ex))
    (hlen : P.H.D + ex ≤ 256) :
    WP isa (.seq (.block (Cfg.hmacArgs₂ dataA ex)) ((cfgOf P).disp fun H => .call H.updN H.updC)) u
      (Updated P L g m₀ t da (P.H.D + ex)) := by
  refine WP.seq (WP.mono (updArgs_ok hL hu.ctx hdA (ex := ex) (by omega))
    fun w₀ ⟨hcw₀, hmw₀, h0, h1, h2, h3, h4, h9⟩ => ?_)
  refine disp_wp P (by rw [h9, hh.1]) fun w hw => ?_
  have hcw := hcw₀.writesOnly hL (by decide) hw
  have g' : ∀ r, r ≠ .x10 → w.gpr r = w₀.gpr r := fun r hr => Dispatch.AArch64.WritesOnly.gpr hw hr
  have hmw : w.mem = u.mem := (WritesOnly.mem' hw).trans hmw₀
  have a := updA (P := P) hL hcw hd hlen (by rw [g' _ (by decide), h0]) (by rw [g' _ (by decide), h2])
    (by rw [g' _ (by decide), h3, hdn]) (by rw [g' _ (by decide), h4])
  have h1 : w.gpr .x1 = BitVec.ofNat 64 P.H.P.B := by rw [g' _ (by decide), h1, hh.2]
  refine Proof.Pbkdf2.Md.AArch64.Calls.upd_call P.ok.stream a fun w' af hr => ?_
  have hws : ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 0, P.H.stream.S⟩ : Region),
      ⟨L.scr + BitVec.ofNat 64 384, P.ok.stream.Wb⟩], Region.Sub r ⟨L.scr, 2432⟩ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> exact scr_work (by anums)
  have hdata : Spec.Sha256.bytesAt w.mem da (P.H.D + ex) = Spec.Sha256.bytesAt t.mem da (P.H.D + ex) := by
    rw [hmw]
    refine bytesAt_frame hu.frame (fun r hr => ?_) (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa using hd.work hL (e := 0) (k := 2432) (by omega)
    · exact (hd.low hL).symm
  refine ⟨hcw.after hL af fun r hr => .inr (.inl (sub_trans (hws r hr) (Region.sub_prefix (by omega)))),
    hu.frame.trans (hmw ▸ after_frame hcw af hws), ?_, ?_⟩
  · rw [← hdata]
    exact hr _ (hmw ▸ hu.inner) (by rw [h1, xorPad_length, blockKey_length (keyOf_length _)])
  · refine P.ok.stream.repr w.mem w'.mem _ _ _ (fun i hi => ?_) (hmw ▸ hu.outer)
    refine Frame.bytes (R := ⟨L.scr + BitVec.ofNat 64 192, P.H.stream.S⟩) af.frame (fun r hr => ?_)
      (by show P.H.stream.S ≤ 2 ^ 64; anums) hi
    rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by anums) (by anums) (by anums)
    · simp only [List.mem_singleton] at hr; subst hr
      rw [hcw.below_eq]
      exact (hL.low_scr (by anums)).symm

/-! ## HMAC's `finalize` -/

theorem finArgs_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {ex dst : Nat} (hex : ex < 4096)
    (hdst : dst < 4096) :
    WP isa (.block (Cfg.hmacArgs₃ ex dst)) u
      fun u' => Ctx L g m₀ u' ∧ u'.mem = u.mem ∧ u'.gpr .x0 = L.scr + BitVec.ofNat 64 0 ∧
        u'.gpr .x1 = L.scr + BitVec.ofNat 64 192 ∧ u'.gpr .x2 = BitVec.ofNat 64 (L.bl + (dn + ex)) ∧
        u'.gpr .x3 = L.B + BitVec.ofNat 64 (16 + dst) ∧ u'.gpr .x4 = L.scr + BitVec.ofNat 64 384 ∧
        u'.gpr .x9 = BitVec.ofNat 64 L.sel := by
  have e : ∀ (l : List Instr) (a b c d : Instr), l ++ [a, b, c, d] = l ++ [a] ++ [b] ++ [c] ++ [d] := by simp
  rw [Cfg.hmacArgs₃, e, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff,
    WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (scr_ok hL hc (d := .x0) (by decide) (a := 0) (by decide)) fun u₁ h₁ => ?_
  refine WP.mono (scr_ok hL h₁.ctx (d := .x1) (by decide) (a := 192) (by decide)) fun u₂ h₂ => ?_
  refine WP.mono (ldBl_ok hL h₂.ctx (d := .x2) (by decide)) fun u₃ h₃ => ?_
  refine WP.mono (ldDl_ok hL h₃.ctx (d := .x3) (by decide)) fun u₄ h₄ => ?_
  refine WP.mono (addR_ok hL h₄.ctx (d := .x2) (n := .x2) (m := .x3) (by decide)) fun u₅ h₅ => ?_
  refine WP.mono (addI_ok hL h₅.ctx (d := .x2) (n := .x2) (by decide) hex) fun u₆ h₆ => ?_
  refine WP.mono (fr_ok hL h₆.ctx (d := .x3) (by decide) hdst) fun u₇ h₇ => ?_
  refine WP.mono (scr_ok hL h₇.ctx (d := .x4) (by decide) (a := 384) (by decide)) fun u₈ h₈ => ?_
  refine WP.mono (ldSel_ok hL h₈.ctx (d := .x9) (by decide)) fun u₉ h₉ => ?_
  refine ⟨h₉.ctx, by rw [h₉.mem, h₈.mem, h₇.mem, h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem], ?_, ?_, ?_, ?_,
    ?_, h₉.val⟩
  · rw [h₉.keep _ (by decide), h₈.keep _ (by decide), h₇.keep _ (by decide), h₆.keep _ (by decide),
      h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.keep _ (by decide), h₁.val]
  · rw [h₉.keep _ (by decide), h₈.keep _ (by decide), h₇.keep _ (by decide), h₆.keep _ (by decide),
      h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.val]
  · rw [h₉.keep _ (by decide), h₈.keep _ (by decide), h₇.keep _ (by decide), h₆.val, h₅.val,
      h₄.keep _ (by decide), h₄.val, h₃.val, BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat, Nat.add_assoc]
  · rw [h₉.keep _ (by decide), h₈.keep _ (by decide), h₇.val]
  · rw [h₉.keep _ (by decide), h₈.val]

/-- After HMAC's `finalize`: the MAC in the frame at `dst`. -/
structure Done (P : RfcHash) {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (g : Reg → BitVec 64) (m₀ : Mem) (t : State) (da : Addr)
    (len dst : Nat) (u : State) : Prop where
  ctx : Ctx L g m₀ u
  frame : Frame [⟨L.scr, 2432⟩, ⟨L.B, 16⟩, ⟨L.B + BitVec.ofNat 64 (16 + dst), P.H.D⟩] t.mem u.mem
  mac : Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (16 + dst)) P.H.D =
    P.mac (keyOf P L t.mem) (Spec.Sha256.bytesAt t.mem da len)

/-- The arguments of HMAC's `finalize`. -/
theorem finA (hL : L.Ok) {w : State} (hcw : Ctx L g m₀ w) {len dst : Nat} (hdst : dst + P.H.D ≤ 200)
    (h0 : w.gpr .x0 = L.scr + BitVec.ofNat 64 0) (h1 : w.gpr .x1 = L.scr + BitVec.ofNat 64 192)
    (h2 : w.gpr .x2 = BitVec.ofNat 64 (P.H.P.B + len)) (h3 : w.gpr .x3 = L.B + BitVec.ofNat 64 (16 + dst))
    (h4 : w.gpr .x4 = L.scr + BitVec.ofNat 64 384) :
    Proof.Pbkdf2.Md.AArch64.Pbk.FinArgs (H := P.H) w (L.scr + BitVec.ofNat 64 0)
      (L.scr + BitVec.ofNat 64 192) (BitVec.ofNat 64 (P.H.P.B + len)) (L.B + BitVec.ofNat 64 (16 + dst))
      (L.scr + BitVec.ofNat 64 384) := by
  have hsp : below w.sp 16 = ⟨L.B, 16⟩ := hcw.below_eq
  exact
    { x0 := h0, x1 := h1, x2 := h2, x3 := h3, x4 := h4
      cr := hcw.covers fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨L.SCR, by simp, within_off _ (by anums)⟩
      cw := hcw.coversW fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨L.SCR, by simp, within_off _ (by anums)⟩
        · exact ⟨L.FR, by simp, within_fr _ (by omega) (by anums)⟩
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
      stk_o := by rw [hsp]; exact Offset.base_disjoint _ (by omega) (by anums)
      stk_s := by rw [hsp]; exact hL.low_scr (by anums)
      scnw := by rw [toNat_add_of (by have := hL.nc; omega)]; have := hL.nc; anums }

theorem fin_step (hL : L.Ok) (hdn : dn = P.H.D) (hh : HashOk P L) {t u : State} {da : Addr} {ex dst : Nat}
    (hu : Updated P L g m₀ t da (P.H.D + ex) u) (hlen : P.H.D + ex ≤ 256) (hdst : dst + P.H.D ≤ 200) :
    WP isa (.seq (.block (Cfg.hmacArgs₃ ex dst)) ((cfgOf P).disp fun H => .call H.hmacFinN H.hmacFin)) u
      (Done P L g m₀ t da (P.H.D + ex) dst) := by
  refine WP.seq (WP.mono (finArgs_ok hL hu.ctx (ex := ex) (dst := dst) (by omega) (by omega))
    fun w₀ ⟨hcw₀, hmw₀, h0, h1, h2, h3, h4, h9⟩ => ?_)
  refine disp_wp P (by rw [h9, hh.1]) fun w hw => ?_
  have hcw := hcw₀.writesOnly hL (by decide) hw
  have g' : ∀ r, r ≠ .x10 → w.gpr r = w₀.gpr r := fun r hr => Dispatch.AArch64.WritesOnly.gpr hw hr
  have hmw : w.mem = u.mem := (WritesOnly.mem' hw).trans hmw₀
  have a := finA (P := P) hL hcw (len := P.H.D + ex) hdst (by rw [g' _ (by decide), h0])
    (by rw [g' _ (by decide), h1]) (by rw [g' _ (by decide), h2, hh.2, hdn])
    (by rw [g' _ (by decide), h3]) (by rw [g' _ (by decide), h4])
  refine Proof.Pbkdf2.Md.AArch64.Pbk.hfin_call P.ok P.hF P.hFd a fun w' ha hpost => ?_
  have hws : ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 0, P.H.S⟩ : Region),
      ⟨L.B + BitVec.ofNat 64 (16 + dst), P.H.D⟩, ⟨L.scr + BitVec.ofNat 64 384, 8 * P.H.W⟩] ++
      [below w.sp 16], ∃ r' ∈ [(⟨L.scr, 2432⟩ : Region), ⟨L.B, 16⟩,
        ⟨L.B + BitVec.ofNat 64 (16 + dst), P.H.D⟩], Region.Sub r r' := by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, hcw.below_eq]
    rintro r (rfl | rfl | rfl | rfl)
    · exact ⟨⟨L.scr, 2432⟩, by simp, scr_work (by anums)⟩
    · exact ⟨⟨L.B + BitVec.ofNat 64 (16 + dst), P.H.D⟩, by simp, sub_refl _⟩
    · exact ⟨⟨L.scr, 2432⟩, by simp, scr_work (by anums)⟩
    · exact ⟨⟨L.B, 16⟩, by simp, sub_refl _⟩
  have hl : (Spec.Sha256.bytesAt t.mem da (P.H.D + ex)).length = P.H.D + ex := by simp [Spec.Sha256.bytesAt]
  refine ⟨hcw.keep hL ha.rd ha.wr ha.sp ha.cs ha.frame (hsy := ha.syms) fun r hr => ?_,
    hu.frame.sub (fun r hr => ⟨r, by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h],
      sub_refl _⟩) |>.trans (hmw ▸ ha.frame.sub hws), ?_⟩
  · obtain ⟨r', hr', hs⟩ := hws r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · exact .inr (.inl (sub_trans hs (Region.sub_prefix (by omega))))
    · exact .inr (.inr (.inl (sub_trans hs (Region.sub_prefix (by omega)))))
    · exact .inr (.inr (.inl (sub_trans hs (Offset.sub_base _ (by anums)))))
  · have hk := blockKey_length (P := P) (keyOf_length (L := L) t.mem)
    exact hpost _ _ hk (by rw [hk, hl]; anums)
      (hmw ▸ hu.inner) (by rw [hl]) (hmw ▸ hu.outer)

/-! ## The whole HMAC -/

theorem seq_seq {a b c : Prog isa} {s : State} {P Q : State → Prop} (h : WP isa (.seq a b) s P)
    (hc : ∀ s', P s' → WP isa c s' Q) : WP isa (.seq a (.seq b c)) s Q := by
  rw [WP.seq_iff] at h ⊢
  refine WP.mono h fun s₁ h₁ => ?_
  rw [WP.seq_iff]
  exact WP.mono h₁ hc

/-- `HMAC_K(data)`, for the key `K` in the frame, to the frame at `dst`. -/
theorem hmac_ok (hL : L.Ok) (hdn : dn = P.H.D) (hh : HashOk P L) {t : State} (hc : Ctx L g m₀ t)
    {dataA : List Instr} {da : Addr} {ex dst : Nat}
    (hdA : ∀ u, Ctx L g m₀ u → WP isa (.block dataA) u (Upd L g m₀ u .x2 da)) (hd : DataOk L da (P.H.D + ex))
    (hlen : P.H.D + ex ≤ 256) (hdst : dst + P.H.D ≤ 200) :
    WP isa ((cfgOf P).hmac dataA ex dst) t (Done P L g m₀ t da (P.H.D + ex) dst) :=
  seq_seq (init_step hL hdn hh hc) fun _ hu => seq_seq (upd_step hL hdn hh hu hdA hd hlen) fun _ hw =>
    fin_step hL hdn hh hw hlen hdst

end VG.Proof.Ecdsa.Rfc6979.AArch64
