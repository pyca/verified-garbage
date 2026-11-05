module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Hash
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Regs
public import VerifiedGarbage.Proof.Framework.ICall
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Deterministic ECDSA on x86 (32-bit): HMAC through the table

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Hmac.lean`): the table's
functions, each called indirectly in a frame of its arguments (`tcall_ok`:
the table's word, which `Ctx` says holds the function of `L.H`, whose call
an indirect call of `L.f`'s functions reaches), with the lengths and counts
the frame's `D` and `B` give:

* HMAC's `init` with the key `K` (`D` bytes, the frame's first): HMAC's
  states for the block key `K₀` of `K` (`init_step`);
* the streaming `update` of the inner state with `len` bytes of data in the
  frame below the saved registers or in `scratch` above HMAC's working space
  (`DataOk`), the inner state holding `K₀ ⊕ ipad ‖ text`, of `B + |text|`
  bytes: it then holds the data after `text` (`upd_call_ok`), with `V`
  (`updV_step`) or with the message at `scratch + sMsg` (`updM_step`);
* HMAC's `finalize`, with the count `B + D + len` for a text of that length,
  writing `HMAC(K₀, text)` (`D` bytes) to the frame at `dst` (`fin_step`).

`St P L g m₀ k0 text` is what holds between them: `Ctx`, and HMAC's states
for `K₀` with the inner one holding `text`. They change only HMAC's states
and working space (the first 2256 bytes of `scratch`), the 76 bytes below the
frame (`W`), and `dst`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Ecdsa.Rfc6979.X86
open VG.Proof.Pbkdf2.Whole.X86 (HiArgs HfArgs hi_frame hf_frame)
open VG.Proof.Pbkdf2.Stream.X86 (UpdArgs upd_frame)

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

/-! ## Pointers into `scratch` and the frame -/

namespace Lay.Ok

theorem scrv (hL : L.Ok) {o : Nat} (ho : o < 8192) :
    (L.sc + BitVec.ofNat 32 o).setWidth 64 = L.scr + BitVec.ofNat 64 o :=
  addr_eq (by have := hL.nc; omega_arith)

theorem scrN (hL : L.Ok) {o : Nat} (ho : o < 8192) : (L.sc + BitVec.ofNat 32 o).toNat = L.sc.toNat + o := by
  have := hL.nc
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]

theorem frv (hL : L.Ok) {o : Nat} (ho : o < 540) :
    (L.F + BitVec.ofNat 32 o).setWidth 64 = L.B + BitVec.ofNat 64 (76 + o) := hL.addrF ho

theorem frN (hL : L.Ok) {o : Nat} (ho : o < 540) : (L.F + BitVec.ofNat 32 o).toNat = L.E.toNat - 512 + o := by
  have := hL.e588; have := hL.e28
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega_arith), hL.FN,
    Nat.mod_eq_of_lt (by omega_arith)]

/-- Two ranges of `scratch`. -/
theorem scr_disj (hL : L.Ok) {a n b k : Nat} (h : a + n ≤ b ∨ b + k ≤ a) (ha : a < 8192) (hb : b < 8192)
    (han : a + n ≤ 8192) (hbk : b + k ≤ 8192) :
    Region.Disjoint ⟨(L.sc + BitVec.ofNat 32 a).setWidth 64, n⟩ ⟨(L.sc + BitVec.ofNat 32 b).setWidth 64, k⟩ := by
  have := hL.nc
  rw [hL.scrv ha, hL.scrv hb]
  exact Offset.disjoint _ h (by omega_arith) (by omega_arith)

/-- A range of the frame, and one of `scratch`. -/
theorem fr_scr (hL : L.Ok) {o n b k : Nat} (ho : o + n ≤ 512) (hb : b < 8192) (hbk : b + k ≤ 8192) :
    Region.Disjoint ⟨(L.F + BitVec.ofNat 32 o).setWidth 64, n⟩ ⟨(L.sc + BitVec.ofNat 32 b).setWidth 64, k⟩ := by
  rw [hL.frv (by omega_arith), hL.scrv hb]
  exact hL.stk_scr (by omega_arith) hbk

/-- The 76 bytes below the frame, and a range of `scratch`. -/
theorem low_scr' (hL : L.Ok) {b k : Nat} (hb : b < 8192) (hbk : b + k ≤ 8192) :
    Region.Disjoint (below L.F 76) ⟨(L.sc + BitVec.ofNat 32 b).setWidth 64, k⟩ := by
  rw [hL.below_F, hL.scrv hb]; exact hL.low_scr hbk

/-- The 76 bytes below the frame, and a range of the frame. -/
theorem low_fr (hL : L.Ok) {o n : Nat} (ho : o + n ≤ 512) :
    Region.Disjoint (below L.F 76) ⟨(L.F + BitVec.ofNat 32 o).setWidth 64, n⟩ := by
  have := hL.nB
  rw [hL.below_F, hL.frv (by omega_arith)]; exact Offset.base_disjoint _ (by omega_arith) (by omega_arith)

/-- The 48 bytes below the frame (the streaming functions' calls) are among the 76. -/
theorem below48 (hL : L.Ok) : Region.Sub (below L.F 48) (below L.F 76) :=
  below_sub (by omega_arith) (by rw [hL.FN]; have := hL.e588; omega_arith)

end Lay.Ok

theorem within_scr (hL : L.Ok) {a n : Nat} (ha : a < 8192) (h : a + n ≤ 8192) :
    Within ⟨(L.sc + BitVec.ofNat 32 a).setWidth 64, n⟩ L.SCR := by
  rw [hL.scrv ha]; exact within_off _ h

theorem within_frv (hL : L.Ok) {o n : Nat} (h : o + n ≤ 512) :
    Within ⟨(L.F + BitVec.ofNat 32 o).setWidth 64, n⟩ L.FR := by
  rw [hL.frv (by omega_arith)]; exact within_fr _ (by omega_arith) (by omega_arith)

/-- Where the data may be: in the frame below the saved registers, or in
`scratch` above HMAC's working space. -/
def DataOk {dn : Nat} (L : Lay dn) (dv : BitVec 32) (len : Nat) : Prop :=
  (∃ o, dv = L.F + BitVec.ofNat 32 o ∧ o + len ≤ 128) ∨
    (∃ o, dv = L.sc + BitVec.ofNat 32 o ∧ 2256 ≤ o ∧ o + len ≤ 3072)

namespace DataOk

variable {dv : BitVec 32} {len : Nat}

theorem low (hd : DataOk L dv len) (hL : L.Ok) : Region.Disjoint (below L.F 76) ⟨dv.setWidth 64, len⟩ := by
  rcases hd with ⟨o, rfl, h⟩ | ⟨o, rfl, h₁, h₂⟩
  · exact hL.low_fr (by omega_arith)
  · exact hL.low_scr' (by omega_arith) (by omega_arith)

/-- The data is apart from HMAC's states and working space. -/
theorem work (hd : DataOk L dv len) (hL : L.Ok) {e k : Nat} (h : e + k ≤ 2256) :
    Region.Disjoint ⟨dv.setWidth 64, len⟩ ⟨(L.sc + BitVec.ofNat 32 e).setWidth 64, k⟩ := by
  rcases hd with ⟨o, rfl, h'⟩ | ⟨o, rfl, h₁, h₂⟩
  · exact hL.fr_scr (by omega_arith) (by omega_arith) (by omega_arith)
  · exact hL.scr_disj (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)

theorem within (hd : DataOk L dv len) (hL : L.Ok) :
    ∃ R ∈ [L.D, L.DG, L.FR, L.OUT, L.SCR], Within ⟨dv.setWidth 64, len⟩ R := by
  rcases hd with ⟨o, rfl, h⟩ | ⟨o, rfl, h₁, h₂⟩
  · exact ⟨L.FR, by simp, within_frv hL (by omega_arith)⟩
  · exact ⟨L.SCR, by simp, within_scr hL (by omega_arith) (by omega_arith)⟩

theorem fits (hd : DataOk L dv len) (hL : L.Ok) : dv.toNat + len ≤ 2 ^ 32 := by
  rcases hd with ⟨o, rfl, h⟩ | ⟨o, rfl, h₁, h₂⟩
  · rw [hL.frN (by omega_arith)]; have := hL.e28; have := hL.e588; omega_arith
  · rw [hL.scrN (by omega_arith)]; have := hL.nc; omega_arith

end DataOk

/-! ## Loads from the frame -/

/-- `d ← [esp + o]`, a word of the frame. -/
theorem ldF_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {d : Reg} (hd : d ≠ .esp) {o : Nat}
    (ho : o + 4 ≤ 512) :
    WP isa (.block [.mov d (.mem (stk o))]) u
      (Upd L g m₀ u d (u.mem.readW (L.B + BitVec.ofNat 64 (76 + o)) 32)) := by
  have e := hL.addrF (o := o) (by omega_arith)
  refine wp_ldm hc.esp (by rw [e]; exact hc.inFr (by omega_arith) (by omega_arith) hL) fun u' v => WP.block_nil ?_
  rw [e] at v
  exact Upd.of_wp hL hc hd v

/-- `d ← d + [esp + o]`, a word of the frame. -/
theorem addF_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {d : Reg} (hd : d ≠ .esp) {o : Nat}
    (ho : o + 4 ≤ 512) :
    WP isa (.block [.alu .add d (.mem (stk o))]) u
      (Upd L g m₀ u d (u.gpr d + u.mem.readW (L.B + BitVec.ofNat 64 (76 + o)) 32)) := by
  have e := hL.addrF (o := o) (by omega_arith)
  refine wp_addm hc.esp (by rw [e]; exact hc.inFr (by omega_arith) (by omega_arith) hL) fun u' v => WP.block_nil ?_
  rw [e] at v
  exact Upd.of_wp hL hc hd v

/-- `d ← d + n`. -/
theorem addI_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {d : Reg} (hd : d ≠ .esp) (v : BitVec 32) :
    WP isa (.block [.alu .add d (.imm v)]) u (Upd L g m₀ u d (u.gpr d + v)) :=
  wp_addi fun _ v₁ => WP.block_nil (Upd.of_wp hL hc hd v₁)

/-! ## The table -/

/-- The layout's table is of `P`'s hash function and functions. -/
def TabL (P : RfcHash) {dn : Nat} (L : Lay dn) : Prop := L.H = P.F ∧ L.f = P.f

/-- The frame's `D`. -/
theorem Ctx.dl (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) :
    t.mem.readW (L.B + BitVec.ofNat 64 (76 + fDl)) 32 = BitVec.ofNat 32 P.F.H.D := by
  rw [← hT.1]; exact hc.pDl

/-- The frame's `B`. -/
theorem Ctx.bl (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) :
    t.mem.readW (L.B + BitVec.ofNat 64 (76 + fBl)) 32 = BitVec.ofNat 32 P.F.H.B := by
  rw [← hT.1]; exact hc.pBl

/-- The indirect call of the table's function `j`, at the address its word
`j` holds, of `n`, in a frame pushing `rs`. -/
theorem tcall_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {j : Nat} (hj : 4 * j + 4 ≤ 24)
    {n : String} {c : Prog isa} {ts : List (String × Prog isa)} {rs : List Reg}
    (hw : m₀.readW (addr L.tb (4 * j)) 32 = t.syms n)
    (hf : ts.find? (fun q => (t.syms q.1).setWidth 64 == (t.syms n).setWidth 64) = some (n, c))
    {Q : State → Prop}
    (h : ∀ t', Ctx L g m₀ t' → t'.mem = t.mem → (∀ r, r ≠ .ebx → t'.gpr r = t.gpr r) → t'.syms = t.syms →
      WP isa (.frame (.push rs) (.call n c) (.pop .eax rs.length)) t' Q) :
    WP isa (Cfg.tcall j ts rs) t Q := by
  unfold Cfg.tcall
  refine WP.seq (WP.mono (arg_ok hL hc (d := .ebx) (by decide) (i := 5) (by decide)) fun t₁ h₁ => ?_)
  refine WP.seq ?_
  have hb : t₁.gpr .ebx = L.tb := h₁.val
  refine wp_ldm hb (h₁.ctx.inTab hL hj) fun t₂ v₂ => WP.block_nil ?_
  have u₂ := Upd.of_wp hL h₁.ctx (d := .ebx) (by decide) v₂
  have hsy : t₂.syms = t.syms := u₂.syms.trans h₁.syms
  have hm : t₂.mem = t.mem := u₂.mem.trans h₁.mem
  have hk : ∀ r, r ≠ .ebx → t₂.gpr r = t.gpr r := fun r hr => (u₂.keep r hr).trans (h₁.keep r hr)
  have hv : t₂.gpr .ebx = (t.syms n) := by
    rw [u₂.val, h₁.ctx.tabWord hL hj, hw]
  refine WP.frame_icalls_of_call (fun u hp => ⟨_, rfl, ?_⟩) (h t₂ u₂.ctx hm hk hsy)
  obtain ⟨-, -, -, rfl⟩ := push_some hp
  show icallTarget isa (pushed rs t₂) (((pushed rs t₂).gpr .ebx).setWidth 64) ts = some (n, c)
  rw [pushed_gpr _ _ (by decide), hv, icallTarget_congr (s₂ := t) fun q _ => by
    show ((pushed rs t₂).syms q.1).setWidth 64 = (t.syms q.1).setWidth 64
    rw [show (pushed rs t₂).syms = t₂.syms from pushRegs_syms t₂ rs, hsy]]
  exact hf

/-! ## HMAC's states -/

/-- The key `K`: the first `D` bytes of the frame. -/
abbrev keyOf (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) : List Byte :=
  Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 76) P.F.H.D

/-- HMAC's states for the block key `k0`, the inner one holding `text`
after `K₀ ⊕ ipad`. -/
structure St (P : RfcHash) {dn : Nat} (L : Lay dn) (g : Reg → BitVec 32) (m₀ : Mem) (k0 text : List Byte)
    (u : State) : Prop where
  ctx : Ctx L g m₀ u
  klen : k0.length = P.F.H.B
  tlen : text.length ≤ 512
  inner : P.ok.hH.SH.Repr u.mem (L.scr + BitVec.ofNat 64 0) (Spec.Hmac.xorPad k0 Spec.Hmac.ipad ++ text)
  outer : P.ok.hH.SH.Repr u.mem (L.scr + BitVec.ofNat 64 192) (Spec.Hmac.xorPad k0 Spec.Hmac.opad)

/-- What HMAC's functions write: their states and working space, and the
stack below the frame. -/
abbrev W {dn : Nat} (L : Lay dn) : List Region := [⟨L.scr, 2256⟩, ⟨L.B, 76⟩]

theorem scr_work {e k : Nat} (h : e + k ≤ 2256) : Region.Sub ⟨L.scr + BitVec.ofNat 64 e, k⟩ ⟨L.scr, 2256⟩ :=
  Offset.sub_base _ h

theorem scr_work' (hL : L.Ok) {e k : Nat} (he : e < 8192) (h : e + k ≤ 2256) :
    Region.Sub ⟨(L.sc + BitVec.ofNat 32 e).setWidth 64, k⟩ ⟨L.scr, 2256⟩ := by
  rw [hL.scrv he]; exact scr_work h

theorem W_safe : ∀ r ∈ W L, Safe L r := by
  intro r hr
  simp only [W, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact .inr (.inl (Region.sub_prefix (by omega_arith)))
  · exact .inr (.inr (.inl (Region.sub_prefix (by omega_arith))))

/-- The writes of a call, within HMAC's working space and the stack below the frame. -/
theorem safe_call (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {ws : List Region} (hs : ∀ r ∈ ws, Safe L r) {n : Nat}
    (hn : n ≤ 76) : ∀ r ∈ ws ++ [below (u.gpr .esp) n], Safe L r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact hs r hr
  · simp only [List.mem_singleton] at hr; subst hr
    refine .inr (.inr (.inl (sub_trans (below_sub hn (by rw [hc.esp, hL.FN]; have := hL.e588; omega_arith)) ?_)))
    rw [hc.esp, hL.below_F]; exact Region.sub_prefix (by omega_arith)

theorem xorPad_length (k : List Byte) (p : Byte) : (Spec.Hmac.xorPad k p).length = k.length :=
  List.length_map _

theorem blockKey_length {k : List Byte} (hk : k.length = P.F.H.D) :
    (Spec.Hmac.blockKey P.ok.hH.SH.H k).length = P.F.H.B := by
  have hB := P.ok.hH.hB
  have hDB : P.F.H.D < P.F.H.B := by nums
  simp only [Spec.Hmac.blockKey, hk, hB, show ¬ P.F.H.B < P.F.H.D by omega_arith, ite_false, List.length_append,
    List.length_replicate]
  omega_arith

theorem keyOf_length (m : Mem) : (keyOf P L m).length = P.F.H.D := by simp [keyOf, Spec.Sha256.bytesAt]

/-! ## HMAC's `init` -/

/-- The arguments of HMAC's `init`. -/
theorem initArgs_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.initArgs) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧ t'.syms = t.syms ∧
      t'.gpr .edi = L.sc + BitVec.ofNat 32 0 ∧ t'.gpr .esi = L.sc + BitVec.ofNat 32 192 ∧
      t'.gpr .edx = L.F + BitVec.ofNat 32 0 ∧ t'.gpr .ecx = BitVec.ofNat 32 P.F.H.D ∧
      t'.gpr .ebp = L.sc + BitVec.ofNat 32 384 := by
  rw [Cfg.initArgs, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (scr_ok hL hc (d := .edi) (by decide) 0) fun u₁ h₁ => ?_
  refine WP.mono (scr_ok hL h₁.ctx (d := .esi) (by decide) 192) fun u₂ h₂ => ?_
  refine WP.mono (fr_ok hL h₂.ctx (d := .edx) (by decide) 0) fun u₃ h₃ => ?_
  refine WP.mono (ldF_ok hL h₃.ctx (d := .ecx) (by decide) (o := fDl) (by decide)) fun u₄ h₄ => ?_
  refine WP.mono (scr_ok hL h₄.ctx (d := .ebp) (by decide) 384) fun u₅ h₅ => ?_
  refine ⟨h₅.ctx, by rw [h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem], by rw [h₅.syms, h₄.syms, h₃.syms, h₂.syms, h₁.syms],
    ?_, ?_, ?_, ?_, h₅.val⟩
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.keep _ (by decide), h₁.val]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.val]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.val]
  · rw [h₅.keep _ (by decide), h₄.val]; exact h₃.ctx.dl hT

theorem initA (hL : L.Ok) {u : State} (hcu : Ctx L g m₀ u) (hdi : u.gpr .edi = L.sc + BitVec.ofNat 32 0)
    (hsi : u.gpr .esi = L.sc + BitVec.ofNat 32 192) (hdx : u.gpr .edx = L.F + BitVec.ofNat 32 0)
    (hcx : u.gpr .ecx = BitVec.ofNat 32 P.F.H.D) (hbp : u.gpr .ebp = L.sc + BitVec.ofNat 32 384) :
    HiArgs P.ok.hH.SH P.ok.Wi u (L.sc + BitVec.ofNat 32 0) (L.sc + BitVec.ofNat 32 192)
      (L.F + BitVec.ofNat 32 0) (L.sc + BitVec.ofNat 32 384) P.F.H.D := by
  have hS := P.ok.hH.hS
  have hB := P.ok.hH.hB
  have nc := hL.nc
  have hsp : Proof.Pbkdf2.Whole.X86.stk u = below L.F 76 := by
    show below (u.gpr .esp) 76 = _; rw [hcu.esp]
  exact
    { edi := hdi, esi := hsi, edx := hdx, ecx := hcx, ebp := hbp
      klB := by rw [hB]; nums
      kl32 := by nums
      sp := by rw [hcu.esp, hL.FN]; have := hL.e588; omega_arith
      cr := hcu.covers fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨L.FR, by simp, within_frv hL (by nums)⟩
      cw := hcu.coversW fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;>
          exact ⟨L.SCR, by simp, within_scr hL (by omega_arith) (by first | nums | (rw [hS]; nums))⟩
      i_o := hL.scr_disj (by rw [hS]; nums) (by omega_arith) (by omega_arith) (by rw [hS]; nums) (by rw [hS]; nums)
      i_k := (hL.fr_scr (by nums) (by omega_arith) (by rw [hS]; nums)).symm
      i_s := hL.scr_disj (by rw [hS]; nums) (by omega_arith) (by omega_arith) (by rw [hS]; nums) (by nums)
      o_k := (hL.fr_scr (by nums) (by omega_arith) (by rw [hS]; nums)).symm
      o_s := hL.scr_disj (by rw [hS]; nums) (by omega_arith) (by omega_arith) (by rw [hS]; nums) (by nums)
      k_s := hL.fr_scr (by nums) (by omega_arith) (by nums)
      b_i := by rw [hsp]; exact hL.low_scr' (by omega_arith) (by rw [hS]; nums)
      b_o := by rw [hsp]; exact hL.low_scr' (by omega_arith) (by rw [hS]; nums)
      b_k := by rw [hsp]; exact hL.low_fr (by nums)
      b_s := by rw [hsp]; exact hL.low_scr' (by omega_arith) (by nums)
      ni := by rw [hL.scrN (by omega_arith), hS]; nums
      no := by rw [hL.scrN (by omega_arith), hS]; nums
      nk := by rw [hL.frN (by omega_arith)]; have := hL.e28; have := hL.e588; nums
      nsc := by rw [hL.scrN (by omega_arith)]; nums }

/-- HMAC's `init` with the key `K` in the frame: HMAC's states for its block key. -/
theorem init_step (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).initK t fun u => St P L g m₀ (Spec.Hmac.blockKey P.ok.hH.SH.H (keyOf P L t.mem)) [] u ∧
      Frame (W L) t.mem u.mem := by
  refine WP.seq (WP.mono (initArgs_ok hL hT hc) fun u ⟨hcu, hmu, hsu, hdi, hsi, hdx, hcx, hbp⟩ => ?_)
  have hok := hcu.tabOk
  have htm := hcu.tabMem
  rw [hT.1, hT.2] at hok
  rw [hT.1] at htm
  refine tcall_ok hL hcu (j := 0) (by decide) htm.1 hok.i fun u' hc' hm' hk' hs' => ?_
  have hk0 : ∀ r ∈ [Reg.edi, .esi, .edx, .ecx, .ebp], u'.gpr r = u.gpr r := fun r hr => hk' r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
  have a := initA (P := P) hL hc' ((hk0 _ (by simp)).trans hdi) ((hk0 _ (by simp)).trans hsi)
    ((hk0 _ (by simp)).trans hdx) ((hk0 _ (by simp)).trans hcx) ((hk0 _ (by simp)).trans hbp)
  have hS := P.ok.hH.hS
  refine WP.of_syms (hi_frame P.ok.hi P.ok.hiSp P.ok.hiSU a fun v af hi ho hsy => ?_)
  have hsafe : ∀ r ∈ [(⟨(L.sc + BitVec.ofNat 32 0).setWidth 64, P.ok.hH.SH.stateBytes⟩ : Region),
      ⟨(L.sc + BitVec.ofNat 32 192).setWidth 64, P.ok.hH.SH.stateBytes⟩,
      ⟨(L.sc + BitVec.ofNat 32 384).setWidth 64, P.ok.Wi * 8⟩], Region.Sub r ⟨L.scr, 2256⟩ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> exact scr_work' hL (by omega_arith) (by first | nums | (rw [hS]; nums))
  have hk : Spec.Sha256.bytesAt u'.mem ((L.F + BitVec.ofNat 32 0).setWidth 64) P.F.H.D = keyOf P L t.mem := by
    rw [hm', hmu, hL.frv (by omega_arith)]
  have hb : below (u'.gpr .esp) 76 = ⟨L.B, 76⟩ := by rw [hc'.esp, hL.below_F]
  refine ⟨⟨hc'.keep (hsy := hsy) hL af.rd af.wr (af.cs .esp (by decide)) af.frame
      (safe_call hL hc' (fun r hr => .inr (.inl (sub_trans (hsafe r hr) (Region.sub_prefix (by omega_arith)))))
        (Nat.le_refl _)),
    blockKey_length (keyOf_length _), by simp, ?_, ?_⟩, ?_⟩
  · rw [← hL.scrv (by omega_arith), ← hk, List.append_nil]; exact hi
  · rw [← hL.scrv (by omega_arith), ← hk]; exact ho
  · rw [← hmu, ← hm']
    exact af.frame.sub fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact ⟨⟨L.scr, 2256⟩, by simp, hsafe r hr⟩
      · simp only [List.mem_singleton] at hr; subst hr
        refine ⟨⟨L.B, 76⟩, by simp, ?_⟩
        rw [show Proof.Pbkdf2.Whole.X86.stk u' = below (u'.gpr .esp) 76 from rfl, hb]
        exact sub_refl _

/-! ## The streaming `update` -/

/-- The arguments of the streaming `update` with `V`. -/
theorem updVArgs_ok (hL : L.Ok) (hT : TabL P L) {u : State} (hc : Ctx L g m₀ u) :
    WP isa (.block Cfg.updVArgs) u fun u' => Ctx L g m₀ u' ∧ u'.mem = u.mem ∧ u'.syms = u.syms ∧
      u'.gpr .edi = L.sc + BitVec.ofNat 32 0 ∧ u'.gpr .esi = BitVec.ofNat 32 P.F.H.B ∧ u'.gpr .eax = 0 ∧
      u'.gpr .edx = L.F + BitVec.ofNat 32 fV ∧ u'.gpr .ecx = BitVec.ofNat 32 P.F.H.D ∧
      u'.gpr .ebp = L.sc + BitVec.ofNat 32 384 := by
  rw [Cfg.updVArgs, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (scr_ok hL hc (d := .edi) (by decide) 0) fun u₁ h₁ => ?_
  rw [show ([.mov .esi (.mem (stk fBl)), .mov .eax (.imm 0)] : List Instr) =
    [.mov .esi (.mem (stk fBl))] ++ [.mov .eax (.imm 0)] from rfl, WP.block_append_iff]
  refine WP.mono (ldF_ok hL h₁.ctx (d := .esi) (by decide) (o := fBl) (by decide)) fun u₂ h₂ => ?_
  refine WP.mono (movi_ok hL h₂.ctx (d := .eax) (by decide) 0) fun u₂' h₂' => ?_
  refine WP.mono (fr_ok hL h₂'.ctx (d := .edx) (by decide) fV) fun u₃ h₃ => ?_
  refine WP.mono (ldF_ok hL h₃.ctx (d := .ecx) (by decide) (o := fDl) (by decide)) fun u₄ h₄ => ?_
  refine WP.mono (scr_ok hL h₄.ctx (d := .ebp) (by decide) 384) fun u₅ h₅ => ?_
  refine ⟨h₅.ctx, by rw [h₅.mem, h₄.mem, h₃.mem, h₂'.mem, h₂.mem, h₁.mem],
    by rw [h₅.syms, h₄.syms, h₃.syms, h₂'.syms, h₂.syms, h₁.syms], ?_, ?_, ?_, ?_, ?_, h₅.val⟩
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), h₂'.keep _ (by decide),
      h₂.keep _ (by decide), h₁.val]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), h₂'.keep _ (by decide), h₂.val,
      h₁.mem]; exact hc.bl hT
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), h₂'.val]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.val]
  · rw [h₅.keep _ (by decide), h₄.val]; exact h₃.ctx.dl hT

/-- The arguments of the streaming `update` with the message's `len` bytes. -/
theorem updMArgs_ok (hL : L.Ok) (hT : TabL P L) {u : State} (hc : Ctx L g m₀ u) (len : Nat) :
    WP isa (.block (Cfg.updMArgs len)) u fun u' => Ctx L g m₀ u' ∧ u'.mem = u.mem ∧ u'.syms = u.syms ∧
      u'.gpr .edi = L.sc + BitVec.ofNat 32 0 ∧ u'.gpr .esi = BitVec.ofNat 32 (P.F.H.B + P.F.H.D) ∧
      u'.gpr .eax = 0 ∧ u'.gpr .edx = L.sc + BitVec.ofNat 32 sMsg ∧ u'.gpr .ecx = BitVec.ofNat 32 len ∧
      u'.gpr .ebp = L.sc + BitVec.ofNat 32 384 := by
  rw [Cfg.updMArgs, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (scr_ok hL hc (d := .edi) (by decide) 0) fun u₁ h₁ => ?_
  rw [show ([.mov .esi (.mem (stk fBl)), .alu .add .esi (.mem (stk fDl)), .mov .eax (.imm 0)] : List Instr) =
    [.mov .esi (.mem (stk fBl))] ++ [.alu .add .esi (.mem (stk fDl))] ++ [.mov .eax (.imm 0)] from rfl,
    WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ldF_ok hL h₁.ctx (d := .esi) (by decide) (o := fBl) (by decide)) fun u₂ h₂ => ?_
  refine WP.mono (addF_ok hL h₂.ctx (d := .esi) (by decide) (o := fDl) (by decide)) fun u₂' h₂' => ?_
  refine WP.mono (movi_ok hL h₂'.ctx (d := .eax) (by decide) 0) fun v₂ i₂ => ?_
  refine WP.mono (scr_ok hL i₂.ctx (d := .edx) (by decide) sMsg) fun u₃ h₃ => ?_
  refine WP.mono (movi_ok hL h₃.ctx (d := .ecx) (by decide) _) fun u₄ h₄ => ?_
  refine WP.mono (scr_ok hL h₄.ctx (d := .ebp) (by decide) 384) fun u₅ h₅ => ?_
  refine ⟨h₅.ctx, by rw [h₅.mem, h₄.mem, h₃.mem, i₂.mem, h₂'.mem, h₂.mem, h₁.mem],
    by rw [h₅.syms, h₄.syms, h₃.syms, i₂.syms, h₂'.syms, h₂.syms, h₁.syms], ?_, ?_, ?_, ?_, ?_, h₅.val⟩
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), i₂.keep _ (by decide),
      h₂'.keep _ (by decide), h₂.keep _ (by decide), h₁.val]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), i₂.keep _ (by decide), h₂'.val,
      h₂.val, h₂.mem, h₁.mem, hc.bl hT, hc.dl hT, BitVec.ofNat_add_ofNat]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), i₂.val]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.val]
  · rw [h₅.keep _ (by decide), h₄.val]

/-- The arguments of the streaming `update`. -/
theorem updA (hL : L.Ok) {w : State} (hcw : Ctx L g m₀ w) {dv : BitVec 32} {len : Nat} (hd : DataOk L dv len)
    (hlen : len ≤ 256) {c : Nat} (hdi : w.gpr .edi = L.sc + BitVec.ofNat 32 0)
    (hsi : w.gpr .esi = BitVec.ofNat 32 c) (hax : w.gpr .eax = 0) (hdx : w.gpr .edx = dv)
    (hcx : w.gpr .ecx = BitVec.ofNat 32 len) (hbp : w.gpr .ebp = L.sc + BitVec.ofNat 32 384) :
    UpdArgs P.ok.hH w .esi .edi (L.sc + BitVec.ofNat 32 0) dv (L.sc + BitVec.ofNat 32 384)
      (BitVec.ofNat 32 c) len := by
  have hsp : Region.Sub (Proof.Pbkdf2.Stream.X86.stk w) (below L.F 76) := by
    show Region.Sub (below (w.gpr .esp) 48) _; rw [hcw.esp]; exact hL.below48
  exact
    { hst := hdi, hlo := hsi, eax := hax, ecx := hcx, edx := hdx, ebp := hbp, hr := by decide, hl := by decide
      hlen := by omega_arith
      sp48 := by rw [hcw.esp, hL.FN]; have := hL.e588; omega_arith
      cd := hcw.covers fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hd.within hL
      cw := hcw.coversW fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact ⟨L.SCR, by simp, within_scr hL (by omega_arith) (by nums)⟩
      st_sc := hL.scr_disj (by nums) (by omega_arith) (by omega_arith) (by nums) (by nums)
      d_st := hd.work hL (by nums)
      d_sc := hd.work hL (by nums)
      b_st := (hL.low_scr' (by omega_arith) (by nums)).sub_left hsp
      b_d := (hd.low hL).sub_left hsp
      b_sc := (hL.low_scr' (by omega_arith) (by nums)).sub_left hsp
      nst := by rw [hL.scrN (by omega_arith)]; have := hL.nc; nums
      nd := hd.fits hL
      nsc := by rw [hL.scrN (by omega_arith)]; have := hL.nc; nums }

/-- The table's `update` of the inner state, holding `text`, with the data. -/
theorem upd_call_ok (hL : L.Ok) (hT : TabL P L) {k0 text : List Byte} {u : State} (hu : St P L g m₀ k0 text u)
    {dv : BitVec 32} {len : Nat} (hd : DataOk L dv len) (hlen : len ≤ 256) (htl : text.length + len ≤ 512)
    (hdi : u.gpr .edi = L.sc + BitVec.ofNat 32 0) (hsi : u.gpr .esi = BitVec.ofNat 32 (P.F.H.B + text.length))
    (hax : u.gpr .eax = 0) (hdx : u.gpr .edx = dv) (hcx : u.gpr .ecx = BitVec.ofNat 32 len)
    (hbp : u.gpr .ebp = L.sc + BitVec.ofNat 32 384) :
    WP isa (Cfg.tcall 1 P.f.upd upd6) u fun u' =>
      St P L g m₀ k0 (text ++ Spec.Sha256.bytesAt u.mem (dv.setWidth 64) len) u' ∧ Frame (W L) u.mem u'.mem := by
  have hc := hu.ctx
  have hok := hc.tabOk
  have htm := hc.tabMem
  rw [hT.1, hT.2] at hok
  rw [hT.1] at htm
  refine tcall_ok hL hc (j := 1) (by decide) htm.2.1 hok.u fun w hcw hmw hkw _ => ?_
  have hk0 : ∀ r ∈ [Reg.edi, .esi, .eax, .edx, .ecx, .ebp], w.gpr r = u.gpr r := fun r hr => hkw r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have hsp : Region.Sub (Proof.Pbkdf2.Stream.X86.stk w) (below L.F 76) := by
    show Region.Sub (below (w.gpr .esp) 48) _; rw [hcw.esp]; exact hL.below48
  have a := updA (P := P) hL hcw hd hlen ((hk0 _ (by simp)).trans hdi) ((hk0 _ (by simp)).trans hsi)
    ((hk0 _ (by simp)).trans hax) ((hk0 _ (by simp)).trans hdx) ((hk0 _ (by simp)).trans hcx)
    ((hk0 _ (by simp)).trans hbp)
  refine WP.of_syms (upd_frame P.ok.hH a fun w' af hr hsy => ?_)
  have hws : ∀ r ∈ [(⟨(L.sc + BitVec.ofNat 32 0).setWidth 64, P.F.H.S⟩ : Region),
      ⟨(L.sc + BitVec.ofNat 32 384).setWidth 64, P.ok.hH.Wb⟩], Region.Sub r ⟨L.scr, 2256⟩ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> exact scr_work' hL (by omega_arith) (by nums)
  have h76 : Region.Sub (below L.F 76) ⟨L.B, 76⟩ := by rw [hL.below_F]; exact sub_refl _
  have hf' : Frame (W L) w.mem w'.mem := af.frame.sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨⟨L.scr, 2256⟩, by simp, hws r hr⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨L.B, 76⟩, by simp, sub_trans hsp h76⟩
  have hkl := hu.klen
  have hS := P.ok.hH.hS
  refine ⟨⟨hcw.keep (hsy := hsy) hL af.rd af.wr (af.cs .esp (by decide)) af.frame fun r hr => ?_, hkl,
    by simp [Spec.Sha256.bytesAt]; omega_arith, ?_, ?_⟩, hmw ▸ hf'⟩
  · rcases List.mem_append.mp hr with hr | hr
    · exact .inr (.inl (sub_trans (hws r hr) (Region.sub_prefix (by omega_arith))))
    · simp only [List.mem_singleton] at hr; subst hr
      exact .inr (.inr (.inl (sub_trans hsp (sub_trans h76 (Region.sub_prefix (by omega_arith))))))
  · rw [← hmw, ← List.append_assoc, ← hL.scrv (by omega_arith)]
    refine hr _ (by rw [hL.scrv (by omega_arith)]; exact hmw ▸ hu.inner) ?_
    rw [List.length_append, xorPad_length, hkl, Proof.Pbkdf2.Stream.X86.zero_append_ofNat (by nums)]
  · refine P.reprOK w.mem w'.mem _ _ _ (fun i hi => ?_) (hmw ▸ hu.outer)
    refine Frame.bytes (R := ⟨L.scr + BitVec.ofNat 64 192, P.ok.hH.SH.stateBytes⟩) af.frame (fun r hr => ?_)
      (by show P.ok.hH.SH.stateBytes ≤ 2 ^ 64; rw [hS]; nums) hi
    rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [hS]
      rcases hr with rfl | rfl <;> (rw [hL.scrv (by omega_arith)]; exact Offset.disjoint _ (by nums) (by nums) (by nums))
    · simp only [List.mem_singleton] at hr; subst hr
      rw [← hL.scrv (by omega_arith)]
      exact ((hL.low_scr' (by omega_arith) (by rw [hS]; nums)).sub_left hsp).symm

/-- The inner state, for the key `K₀`, updated with `V`. -/
theorem updV_step (hL : L.Ok) (hT : TabL P L) {k0 : List Byte} {u : State} (hu : St P L g m₀ k0 [] u) :
    WP isa (cfgOf P).updV u fun u' =>
      St P L g m₀ k0 (Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 140) P.F.H.D) u' ∧
      Frame (W L) u.mem u'.mem := by
  refine WP.seq (WP.mono (updVArgs_ok hL hT hu.ctx) fun w ⟨hcw, hmw, _, hdi, hsi, hax, hdx, hcx, hbp⟩ => ?_)
  have hw : St P L g m₀ k0 [] w := ⟨hcw, hu.klen, hu.tlen, hmw ▸ hu.inner, hmw ▸ hu.outer⟩
  refine WP.mono (upd_call_ok hL hT hw (len := P.F.H.D)
    (.inl ⟨fV, rfl, by simp only [fV]; nums⟩) (by nums) (by simp; nums) hdi (by simpa using hsi) hax hdx hcx hbp)
    fun u' ⟨hs, hf⟩ => ?_
  rw [List.nil_append, hmw, hL.frv (by decide)] at hs
  exact ⟨hs, hmw ▸ hf⟩

/-- The inner state, for the key `K₀`, holding `text`, updated with the message's `len` bytes. -/
theorem updM_step (hL : L.Ok) (hT : TabL P L) {k0 text : List Byte} {u : State}
    (hu : St P L g m₀ k0 text u) (ht : text.length = P.F.H.D) {len : Nat} (hlen : len ≤ 256) :
    WP isa ((cfgOf P).updM len) u fun u' =>
      St P L g m₀ k0 (text ++ Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 sMsg) len) u' ∧
      Frame (W L) u.mem u'.mem := by
  refine WP.seq (WP.mono (updMArgs_ok hL hT hu.ctx len)
    fun w ⟨hcw, hmw, _, hdi, hsi, hax, hdx, hcx, hbp⟩ => ?_)
  have hw : St P L g m₀ k0 text w := ⟨hcw, hu.klen, hu.tlen, hmw ▸ hu.inner, hmw ▸ hu.outer⟩
  refine WP.mono (upd_call_ok hL hT hw (len := len) (.inr ⟨sMsg, rfl, by decide, by simp only [sMsg]; omega_arith⟩)
    hlen (by rw [ht]; nums) hdi (by rw [hsi, ht]) hax hdx hcx hbp) fun u' ⟨hs, hf⟩ => ?_
  rw [hmw, hL.scrv (by decide)] at hs
  exact ⟨hs, hmw ▸ hf⟩

/-! ## HMAC's `finalize` -/

theorem finArgs_ok (hL : L.Ok) (hT : TabL P L) {u : State} (hc : Ctx L g m₀ u) (len dst : Nat) :
    WP isa (.block (Cfg.finArgs len dst)) u
      fun u' => Ctx L g m₀ u' ∧ u'.mem = u.mem ∧ u'.syms = u.syms ∧ u'.gpr .edx = L.sc + BitVec.ofNat 32 0 ∧
        u'.gpr .esi = L.sc + BitVec.ofNat 32 192 ∧ u'.gpr .eax = BitVec.ofNat 32 (P.F.H.B + P.F.H.D + len) ∧
        u'.gpr .ecx = 0 ∧ u'.gpr .edi = L.F + BitVec.ofNat 32 dst ∧ u'.gpr .ebp = L.sc + BitVec.ofNat 32 384 := by
  rw [Cfg.finArgs, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (scr_ok hL hc (d := .edx) (by decide) 0) fun u₁ h₁ => ?_
  refine WP.mono (scr_ok hL h₁.ctx (d := .esi) (by decide) 192) fun u₂ h₂ => ?_
  rw [show ([.mov .eax (.mem (stk fBl)), .alu .add .eax (.mem (stk fDl)),
      .alu .add .eax (.imm (BitVec.ofNat 32 len)), .mov .ecx (.imm 0)] : List Instr) =
    [.mov .eax (.mem (stk fBl))] ++ [.alu .add .eax (.mem (stk fDl))] ++
      [.alu .add .eax (.imm (BitVec.ofNat 32 len))] ++ [.mov .ecx (.imm 0)] from rfl, WP.block_append_iff,
    WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ldF_ok hL h₂.ctx (d := .eax) (by decide) (o := fBl) (by decide)) fun u₃ h₃ => ?_
  refine WP.mono (addF_ok hL h₃.ctx (d := .eax) (by decide) (o := fDl) (by decide)) fun v₃ i₃ => ?_
  refine WP.mono (addI_ok hL i₃.ctx (d := .eax) (by decide) _) fun w₃ j₃ => ?_
  refine WP.mono (movi_ok hL j₃.ctx (d := .ecx) (by decide) 0) fun x₃ k₃ => ?_
  refine WP.mono (fr_ok hL k₃.ctx (d := .edi) (by decide) dst) fun u₄ h₄ => ?_
  refine WP.mono (scr_ok hL h₄.ctx (d := .ebp) (by decide) 384) fun u₅ h₅ => ?_
  have hm2 : u₂.mem = u.mem := by rw [h₂.mem, h₁.mem]
  refine ⟨h₅.ctx, by rw [h₅.mem, h₄.mem, k₃.mem, j₃.mem, i₃.mem, h₃.mem, hm2],
    by rw [h₅.syms, h₄.syms, k₃.syms, j₃.syms, i₃.syms, h₃.syms, h₂.syms, h₁.syms], ?_, ?_, ?_, ?_, ?_, h₅.val⟩
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), k₃.keep _ (by decide), j₃.keep _ (by decide),
      i₃.keep _ (by decide), h₃.keep _ (by decide), h₂.keep _ (by decide), h₁.val]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), k₃.keep _ (by decide), j₃.keep _ (by decide),
      i₃.keep _ (by decide), h₃.keep _ (by decide), h₂.val]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), k₃.keep _ (by decide), j₃.val, i₃.val, h₃.val,
      h₃.mem, hm2, hc.bl hT, hc.dl hT, BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), k₃.val]
  · rw [h₅.keep _ (by decide), h₄.val]

/-- The arguments of HMAC's `finalize`. -/
theorem finA (hL : L.Ok) {w : State} (hcw : Ctx L g m₀ w) {cnt dst : Nat} (hdst : dst + P.F.H.D ≤ 128)
    (hdx : w.gpr .edx = L.sc + BitVec.ofNat 32 0) (hsi : w.gpr .esi = L.sc + BitVec.ofNat 32 192)
    (hax : w.gpr .eax = BitVec.ofNat 32 cnt) (hcx : w.gpr .ecx = 0)
    (hdi : w.gpr .edi = L.F + BitVec.ofNat 32 dst) (hbp : w.gpr .ebp = L.sc + BitVec.ofNat 32 384) :
    HfArgs P.ok.hH.SH P.ok.Wf w (L.sc + BitVec.ofNat 32 0) (L.sc + BitVec.ofNat 32 192)
      (BitVec.ofNat 32 cnt) 0 (L.F + BitVec.ofNat 32 dst) (L.sc + BitVec.ofNat 32 384) := by
  have hS := P.ok.hH.hS
  have hD := P.ok.hH.hD
  have nc := hL.nc
  have hsp : Proof.Pbkdf2.Whole.X86.stk w = below L.F 76 := by
    show below (w.gpr .esp) 76 = _; rw [hcw.esp]
  exact
    { edx := hdx, esi := hsi, eax := hax, ecx := hcx, edi := hdi, ebp := hbp
      sp := by rw [hcw.esp, hL.FN]; have := hL.e588; omega_arith
      cr := hcw.covers fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨L.SCR, by simp, within_scr hL (by omega_arith) (by rw [hS]; nums)⟩
      cw := hcw.coversW fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨L.SCR, by simp, within_scr hL (by omega_arith) (by rw [hS]; nums)⟩
        · exact ⟨L.FR, by simp, within_frv hL (by rw [hD]; nums)⟩
        · exact ⟨L.SCR, by simp, within_scr hL (by omega_arith) (by nums)⟩
      i_u := hL.scr_disj (by rw [hS]; nums) (by omega_arith) (by omega_arith) (by rw [hS]; nums) (by rw [hS]; nums)
      i_o := (hL.fr_scr (by rw [hD]; nums) (by omega_arith) (by rw [hS]; nums)).symm
      i_s := hL.scr_disj (by rw [hS]; nums) (by omega_arith) (by omega_arith) (by rw [hS]; nums) (by nums)
      u_o := (hL.fr_scr (by rw [hD]; nums) (by omega_arith) (by rw [hS]; nums)).symm
      u_s := hL.scr_disj (by rw [hS]; nums) (by omega_arith) (by omega_arith) (by rw [hS]; nums) (by nums)
      o_s := hL.fr_scr (by rw [hD]; nums) (by omega_arith) (by nums)
      b_i := by rw [hsp]; exact hL.low_scr' (by omega_arith) (by rw [hS]; nums)
      b_u := by rw [hsp]; exact hL.low_scr' (by omega_arith) (by rw [hS]; nums)
      b_o := by rw [hsp]; exact hL.low_fr (by rw [hD]; nums)
      b_s := by rw [hsp]; exact hL.low_scr' (by omega_arith) (by nums)
      ni := by rw [hL.scrN (by omega_arith), hS]; nums
      nu := by rw [hL.scrN (by omega_arith), hS]; nums
      no := by rw [hL.frN (by omega_arith), hD]; have := hL.e28; have := hL.e588; nums
      nsc := by rw [hL.scrN (by omega_arith)]; nums }

/-- HMAC's `finalize`, for the key `K₀` and the text `text`, of `D + len`
bytes: the MAC in the frame at `dst`. -/
theorem fin_step (hL : L.Ok) (hT : TabL P L) {k0 text : List Byte} {u : State} (hu : St P L g m₀ k0 text u)
    {len dst : Nat} (ht : text.length = P.F.H.D + len) (hlen : len ≤ 256) (hdst : dst + P.F.H.D ≤ 128) :
    WP isa ((cfgOf P).fin len dst) u fun u' => Ctx L g m₀ u' ∧
      Frame (W L ++ [⟨L.B + BitVec.ofNat 64 (76 + dst), P.F.H.D⟩]) u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (76 + dst)) P.F.H.D =
        Spec.Hmac.hmacBlockKey P.ok.hH.SH.H k0 text := by
  refine WP.seq (WP.mono (finArgs_ok hL hT hu.ctx len dst)
    fun w ⟨hcw, hmw, _, hdx, hsi, hax, hcx, hdi, hbp⟩ => ?_)
  have hok := hcw.tabOk
  have htm := hcw.tabMem
  rw [hT.1, hT.2] at hok
  rw [hT.1] at htm
  refine tcall_ok hL hcw (j := 2) (by decide) htm.2.2 hok.f fun w₁ hc₁ hm₁ hk₁ _ => ?_
  have hk0 : ∀ r ∈ [Reg.edx, .esi, .eax, .ecx, .edi, .ebp], w₁.gpr r = w.gpr r := fun r hr => hk₁ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have a := finA (P := P) hL hc₁ (cnt := P.F.H.B + P.F.H.D + len) hdst ((hk0 _ (by simp)).trans hdx)
    ((hk0 _ (by simp)).trans hsi) ((hk0 _ (by simp)).trans hax) ((hk0 _ (by simp)).trans hcx)
    ((hk0 _ (by simp)).trans hdi) ((hk0 _ (by simp)).trans hbp)
  have hS := P.ok.hH.hS
  have hD := P.ok.hH.hD
  have hB := P.ok.hH.hB
  refine WP.of_syms (hf_frame P.reprOK (by rw [hS]; nums) P.ok.hf P.ok.hfSp P.ok.hfSU a fun w' af hpost hsy => ?_)
  have hO : (L.F + BitVec.ofNat 32 dst).setWidth 64 = L.B + BitVec.ofNat 64 (76 + dst) := hL.frv (by nums)
  have hws : ∀ r ∈ [(⟨(L.sc + BitVec.ofNat 32 0).setWidth 64, P.ok.hH.SH.stateBytes⟩ : Region),
      ⟨(L.F + BitVec.ofNat 32 dst).setWidth 64, P.ok.hH.SH.digestBytes⟩,
      ⟨(L.sc + BitVec.ofNat 32 384).setWidth 64, P.ok.Wf * 8⟩] ++ [below (w₁.gpr .esp) 76],
      ∃ r' ∈ W L ++ [⟨L.B + BitVec.ofNat 64 (76 + dst), P.F.H.D⟩], Region.Sub r r' := by
    simp only [W, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, hc₁.esp, hL.below_F]
    rintro r (rfl | rfl | rfl | rfl)
    · exact ⟨⟨L.scr, 2256⟩, by simp, scr_work' hL (by omega_arith) (by rw [hS]; nums)⟩
    · exact ⟨⟨L.B + BitVec.ofNat 64 (76 + dst), P.F.H.D⟩, by simp, by rw [hO, hD]; exact sub_refl _⟩
    · exact ⟨⟨L.scr, 2256⟩, by simp, scr_work' hL (by omega_arith) (by nums)⟩
    · exact ⟨⟨L.B, 76⟩, by simp, sub_refl _⟩
  have hm : w₁.mem = u.mem := hm₁.trans hmw
  refine ⟨hc₁.keep (hsy := hsy) hL af.rd af.wr (af.cs .esp (by decide)) af.frame fun r hr => ?_,
    hm ▸ af.frame.sub hws, ?_⟩
  · obtain ⟨r', hr', hs⟩ := hws r hr
    simp only [W, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · exact .inr (.inl (sub_trans hs (Region.sub_prefix (by omega_arith))))
    · exact .inr (.inr (.inl (sub_trans hs (Region.sub_prefix (by omega_arith)))))
    · exact (safe_low L (by nums)).of_sub hs
  · have hk := hu.klen
    have := hpost k0 text (by rw [hk, hB]) (by rw [hk]; have := hu.tlen; nums)
      (by rw [hL.scrv (by omega_arith)]; exact hm ▸ hu.inner)
      (by rw [hB, ht, Proof.Pbkdf2.Stream.X86.zero_append_ofNat (by nums)]; congr 1; omega_arith)
      (by rw [hL.scrv (by omega_arith)]; exact hm ▸ hu.outer)
    rw [hO, hD] at this
    exact this

end VG.Proof.Ecdsa.Rfc6979.X86
