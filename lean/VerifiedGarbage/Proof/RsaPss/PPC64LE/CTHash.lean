module

public import VerifiedGarbage.Proof.RsaPss.PPC64LE.CTBlocks
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.CTTab
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.CTFixed
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.MHash
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Hash
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTBase
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTCalls
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTBlocks
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.View
public import VerifiedGarbage.Impl.RsaPss.PPC64LE
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Two
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Mid

/-!
# RSASSA-PSS verification on PPC64LE: hashing `M'` for a given salt length, twice

Untrusted: everything here is checked by Lean. After the public operation,
two runs are compared through the anchor `a` with `BL`: `Base` from entry
states whose encoding parameters are those of their registers and that hold
the tables of the hash functions (`PreL`: the hash function's of `MdHash`
and MGF1's of `Hash`, as `Tabs` names them), that agree with the anchor on
what `Base` fixes and on the tables and the addresses of their functions
(`PubL`), with the entry's addresses of statics. `hashFixed_ct`: the hash of
`M'` for a given salt length, its blocks by the taint analysis and its calls
through the table by `tcall_twoM`, `init_ct`, `upd_ct` and `fin_ct`, with
arguments from the anchor.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE
open VG.Impl.RsaOaep.PPC64LE (oSt oDig oW oRsa Fns)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC off off_off fx hiRegs Agree Ok B BT BT.b B.agree B.only pins_of st_wp
  two_seq UpdArgs FinArgs init_ct upd_ct fin_ct HashCT sdis sc_cov cR_dis hfits offs st_taint TabS TabA)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep Two Pins two_post wp_li wp_addi wp_subi wp_add wp_mov wp_nil
  eval_nonzero)

/-- The tables on entry. -/
def TabsOn (Z : Tabs) (s : State) : Prop :=
  TabS Z.G Z.g gArg Sp s (stackArg s 7) ∧ MdTabS Z.H Z.cn Z.cc Z.dn Z.dc Z.f hArg Sp s (stackArg s 6)

/-- The tables at the anchor's addresses, with its addresses of their functions. -/
def TabsAg (Z : Tabs) (a s : State) : Prop :=
  stackArg s 7 = stackArg a 7 ∧ s.syms Z.G.initN = a.syms Z.G.initN ∧ s.syms Z.G.updN = a.syms Z.G.updN ∧
    s.syms Z.G.finN = a.syms Z.G.finN ∧ stackArg s 6 = stackArg a 6 ∧ s.syms Z.H.initN = a.syms Z.H.initN ∧
    s.syms Z.H.updN = a.syms Z.H.updN ∧ s.syms Z.H.finN = a.syms Z.H.finN ∧ s.syms Z.cn = a.syms Z.cn ∧
    s.syms Z.dn = a.syms Z.dn

/-- An entry state whose encoding parameters are those of its registers, with
the tables. -/
abbrev PreL (D : Nat) (Z : Tabs) (s : State) : Prop :=
  Lay D s (lo s).toNat (dbLen D s).toNat ((cm s).setWidth 8) ∧ TabsOn Z s

/-- What it agrees on with the anchor. -/
abbrev PubL (D : Nat) (Z : Tabs) (a s : State) : Prop := Agree Sp (vP D) a s ∧ TabsAg Z a s

theorem Lay.canon {D lN dN : Nat} {c : Byte} {s : State} (L : Lay D s lN dN c) :
    Lay D s (lo s).toNat (dbLen D s).toNat ((cm s).setWidth 8) := by
  have h1 : (lo s).toNat = lN := by rw [L.hlo, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := L.l1; omega_arith)]
  have h2 : (dbLen D s).toNat = dN := by
    rw [L.hdb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := L.hk; have := L.k2; omega_arith)]
  have h3 : (cm s).setWidth 8 = c := by rw [L.hc, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
  rw [h1, h2, h3]; exact L

theorem lOk (D : Nat) (Z : Tabs) : Ok Sp (vP D) (PreL D Z) (PubL D Z) := ⟨fun P => P.1.F, fun p => p.1⟩

theorem tabG (D : Nat) (Z : Tabs) : TabA Z.G Z.g gArg Sp (PreL D Z) (PubL D Z) :=
  ⟨fun P => P.2.1, fun p => p.2.1, fun p => p.2.2.1, fun p => p.2.2.2.1, fun p => p.2.2.2.2.1⟩

theorem tabH (D : Nat) (Z : Tabs) : MdTabA Z.H Z.cn Z.cc Z.dn Z.dc Z.f hArg Sp (PreL D Z) (PubL D Z) :=
  ⟨fun P => P.2.2, fun p => p.2.2.2.2.2.1, fun p => p.2.2.2.2.2.2.1, fun p => p.2.2.2.2.2.2.2.1,
    fun p => p.2.2.2.2.2.2.2.2.1, fun p => p.2.2.2.2.2.2.2.2.2.1, fun p => p.2.2.2.2.2.2.2.2.2.2⟩

/-- `Base` from such an entry state agreeing with the anchor, with its
addresses of statics. -/
abbrev BL (D : Nat) (Z : Tabs) : State → State → Prop := BT Sp (vP D) (PreL D Z) (PubL D Z)

section
variable {D : Nat} {Z : Tabs}

theorem BL.r14 {a t : State} (h : BL D Z a t) : t.gpr .r14 = Sp a := ((h.b.agree (lOk D Z)).2.1)
theorem BL.v {a t : State} (h : BL D Z a t) {r : Reg} (hr : r ∈ fx := by decide) : t.gpr r = vP D a r :=
  (h.b.agree (lOk D Z)).2.2 r hr
theorem BL.only' {a t t' : State} {rs : List Reg} (h : BL D Z a t) (o : Only rs t t') (y : t'.syms = t.syms)
    (hrs : ∀ r ∈ rs, r ∉ .r14 :: fx ++ hiRegs := by decide) : BL D Z a t' :=
  let ⟨s, P, p, b, sy⟩ := h; ⟨s, P, p, b.only P.1.F o hrs, y.trans sy⟩

theorem bl_pins {α : Type} {Φ : α → State → Prop} {an : α → State} (h : ∀ x t, Φ x t → BL D Z (an x) t)
    (rs : List Reg) (hrs : ∀ r ∈ rs, r ∈ Reg.r14 :: fx := by decide) : Pins Φ rs :=
  pins_of (lOk D Z) (fun x t hx => (h x t hx).b) rs hrs

/-- The anchor's numbers, from an entry state with `PreL` agreeing with it. -/
theorem agree_lay {a s : State} (P : PreL D Z s) (g : PubL D Z a s) :
    Lay D s (lo a).toNat (dbLen D a).toNat ((cm a).setWidth 8) := by
  have e17 : lo s = lo a := g.1.v .r17 (by decide)
  have e18 : cm s = cm a := g.1.v .r18 (by decide)
  have e21 : dbLen D s = dbLen D a := g.1.v .r21 (by decide)
  rw [← e17, ← e18, ← e21]; exact P.1

theorem BL.dn {a t : State} (h : BL D Z a t) :
    1 ≤ (dbLen D a).toNat ∧ (lo a).toNat + (dbLen D a).toNat + D + 1 ≤ 1024 ∧ 0 < D ∧ D ≤ 64 := by
  obtain ⟨s, P, g, -, -⟩ := h
  have L := agree_lay P g
  have := L.hk; have := L.k2
  exact ⟨L.d1, by omega_arith, L.D0, L.D64⟩

end

/-! ## `hashFixed`, through the table -/

theorem hashFixed_ct {D : Nat} {Z : Tabs} (hH : HashOK Z.H) (cH : HashCT hH) (hD : Z.H.D = D) :
    RelCT isa (Two fun a t => BL D Z a t ∧ (stackArg a 0).toNat + 8 + D ≤ 2048) (hashFixed Z.H Z.f hArg)
      fun _ _ => True :=
  hashFixedG_ct (lOk D Z) hH cH (tabH D Z) hD (fun a => (stackArg a 0).toNat) fun a => by
    show stackArg a 0 = _; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-! ## `ctHash`, in two runs -/

section CtHash

open VG.Proof.MdStream (Md)
open VG.Proof.MdStream.PPC64LE (CalleeOk compressK ofNat_shr ofNat_shl)
open VG.Impl.RsaOaep.PPC64LE (tcall)
open VG.Proof.RsaOaep.PPC64LE (view fb)
open VG.Impl.MdStream.PPC64LE (Params lg)
open VG.Proof.MdHashTable.PPC64LE (digestK)
open VG.Proof.RsaPkcs1Sig.PPC64LE (wp_lsr wp_lsl wp_add)

variable {D : Nat} {Z : Tabs} {P : Params} {md : Md P.B P.N P.L}

/-- The number of blocks `ctHash` compresses, from the anchor's `dbLen`. -/
def nbmOf (D : Nat) (P : Params) (a : State) : Nat := ((dbLen D a).toNat + (8 + D - 1 + P.L)) / P.B + 1

/-- After `ctLens`: `nbm` in `r28` and `ℓ` in `r29`, of some salt length
below `dbLen`. -/
def K1 (D : Nat) (Z : Tabs) (P : Params) (a t : State) : Prop :=
  BL D Z a t ∧ t.gpr .r28 = BitVec.ofNat 64 (nbmOf D P a) ∧
    ∃ sl < (dbLen D a).toNat, t.gpr .r29 = BitVec.ofNat 64 (8 + D + sl)

/-- After `lenField`: `nbm` in `r28` and some last block below it in `r27`. -/
def K2 (D : Nat) (Z : Tabs) (P : Params) (a t : State) : Prop :=
  BL D Z a t ∧ t.gpr .r28 = BitVec.ofNat 64 (nbmOf D P a) ∧ ∃ fb < nbmOf D P a, t.gpr .r27 = BitVec.ofNat 64 fb

/-- In the compression loop, before block `ac.2`. -/
def LI (D : Nat) (Z : Tabs) (P : Params) (ac : State × Nat) (u : State) : Prop :=
  BL D Z ac.1 u ∧ u.gpr .r28 = BitVec.ofNat 64 (nbmOf D P ac.1 - ac.2) ∧ u.gpr .r26 = BitVec.ofNat 64 ac.2 ∧
    ac.2 < nbmOf D P ac.1 ∧ ∃ fb < nbmOf D P ac.1, u.gpr .r27 = BitVec.ofNat 64 fb

theorem nbm_le (ok : CtOK P md Z.cc Z.dc) {a t : State} (h : BL D Z a t) :
    nbmOf D P a * P.B ≤ 2048 ∧ 0 < nbmOf D P a := by
  obtain ⟨hd1, hd2, hD0, hD64⟩ := h.dn
  have hBd := ok.dims.B
  have hLd := ok.dims.L
  have := Nat.div_mul_le_self ((dbLen D a).toNat + (8 + D - 1 + P.L)) P.B
  refine ⟨?_, Nat.succ_pos _⟩
  unfold nbmOf
  rw [Nat.add_mul, Nat.one_mul]; rcases hBd with e | e <;> rw [e] at this ⊢ <;> omega

theorem ne0_ofNat {k : Nat} (hk : k < 2 ^ 64) : (BitVec.ofNat 64 k != 0) = decide (k ≠ 0) := by
  by_cases h : k = 0
  · subst h; rfl
  · have e : BitVec.ofNat 64 k ≠ 0 := fun e => h (by
      have := congrArg BitVec.toNat e; rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at this)
    rw [show (BitVec.ofNat 64 k != 0) = true from bne_iff_ne.mpr e]; simp [h]

theorem pins_r28 {α : Type} {Φ : α → State → Prop} {an : α → State} {v : α → BitVec 64}
    (hb : ∀ x t, Φ x t → BL D Z (an x) t) (h28 : ∀ x t, Φ x t → t.gpr .r28 = v x) : Pins Φ [.r14, .r28] :=
  fun x t₁ t₂ h₁ h₂ => ⟨((bl_pins hb []) x t₁ t₂ h₁ h₂).1, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [(hb x t₁ h₁).r14, (hb x t₂ h₂).r14]
    · rw [h28 x t₁ h₁, h28 x t₂ h₂]⟩

section
variable (ok : CtOK P md Z.cc Z.dc)
include ok

theorem ctLens_wp (hD : Z.H.D = D) {a t : State} (h : BL D Z a t)
    (hs : ∃ sl < (dbLen D a).toNat, t.gpr .r25 = BitVec.ofNat 64 sl) :
    WP isa (.block (ctLens Z.H P)) t (K1 D Z P a) := by
  obtain ⟨hd1, hd2, hD0, hD64⟩ := h.dn
  obtain ⟨s, Pr, p, b, sy⟩ := h
  have L := agree_lay Pr p
  obtain ⟨sl, hsl, h25⟩ := hs
  obtain ⟨hlg1, hlg7, hlg⟩ := ok.dims.log
  have hLd := ok.dims.L
  subst hD
  refine WP.of_syms (wp_addi (h := by omega) fun t₁ o₁ e₁ => wp_addi (h := by omega) fun t₂ o₂ e₂ =>
    wp_lsr (h := by omega) fun t₃ o₃ e₃ => wp_addi (h := by decide) fun t₄ o₄ e₄ => wp_nil fun y₄ => ?_)
  have k₄ : Only [.r29, .r28] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  refine ⟨⟨s, Pr, p, b.only L.F k₄, y₄.trans sy⟩, ?_, sl, hsl, ?_⟩
  · rw [e₄, e₃, e₂, o₁.get .r21, b.pdb, L.hdb, BitVec.ofNat_add_ofNat, ofNat_shr (by omega), hlg,
      BitVec.ofNat_add_ofNat]; rfl
  · rw [o₄.get .r29, o₃.get .r29, o₂.get .r29, e₁, h25, BitVec.ofNat_add_ofNat]; congr 1; omega

omit ok in
theorem hInit_K1 (hH : HashOK Z.H) {a t : State} (h : K1 D Z P a t) : WP isa (hInit Z.f hArg) t (K1 D Z P a) := by
  obtain ⟨⟨s, Pr, p, b, sy⟩, h28, sl, hsl, h29⟩ := h
  have X := lOk D Z
  refine WP.seq (WP.of_syms (wp_addi fun t₁ o₁ e₁ => wp_nil fun y₁ => ?_))
  exact WP.mono (initM_ok (X.fits Pr) ((tabH D Z).tab Pr) hH (b.only (X.fits Pr) o₁) (y₁.trans sy)
    (by rw [e₁, b.r14])) fun t₂ ⟨⟨b₂, g₂, _⟩, y₂⟩ =>
      ⟨⟨s, Pr, p, b₂, y₂⟩, by rw [g₂ _ (by decide), o₁.get .r28, h28], sl, hsl,
        by rw [g₂ _ (by decide), o₁.get .r29, h29]⟩

theorem pad80_K1 {a t : State} (h : K1 D Z P a t) : WP isa (pad80 P) t (K1 D Z P a) := by
  obtain ⟨hnb, hn0⟩ := nbm_le ok h.1
  obtain ⟨hd1, hd2, hD0, hD64⟩ := h.1.dn
  obtain ⟨⟨s, Pr, p, b, sy⟩, h28, sl, hsl, h29⟩ := h
  have L := agree_lay Pr p
  obtain ⟨hlg1, hlg7, hlg⟩ := ok.dims.log
  exact WP.of_syms (WP.mono (pad80_ok L hlg hlg7 b h28 h29 hnb (Nat.mul_pos hn0 ok.dims.pos) (by omega))
    fun t' ⟨b', k', _⟩ y => ⟨⟨s, Pr, p, b', y.trans sy⟩, by rw [k'.get .r28, h28], sl, hsl, by rw [k'.get .r29, h29]⟩)

theorem lenField_K2 {a t : State} (h : K1 D Z P a t) : WP isa (.block (lenField P)) t (K2 D Z P a) := by
  obtain ⟨hd1, hd2, hD0, hD64⟩ := h.1.dn
  obtain ⟨⟨s, Pr, p, b, sy⟩, h28, sl, hsl, h29⟩ := h
  have L := agree_lay Pr p
  obtain ⟨hlg1, hlg7, hlg⟩ := ok.dims.log
  have hNd := ok.dims.N
  have hBd := ok.dims.B
  have hLd := ok.dims.L
  have hO : oLen = 4608 := rfl
  refine WP.of_syms (WP.mono (lenField_ok L ok.shape ok.lenLr (by rcases hBd with e | e <;> omega) hLd.2 hlg7
    b h29 (by omega)) fun t' ⟨b', k', g27, _⟩ y => ⟨⟨s, Pr, p, b', y.trans sy⟩, by rw [k'.get .r28, h28],
      (8 + D + sl + P.L) / 2 ^ lg P, ?_, g27⟩)
  rw [hlg]; unfold nbmOf
  exact Nat.lt_succ_of_le (Nat.div_le_div_right (by omega))

theorem lenLoop_K2 {a t : State} (h : K2 D Z P a t) : WP isa (lenLoop P) t (K2 D Z P a) := by
  obtain ⟨hnb, hn0⟩ := nbm_le ok h.1
  obtain ⟨⟨s, Pr, p, b, sy⟩, h28, fb, hfb, h27⟩ := h
  have L := agree_lay Pr p
  have hBd := ok.dims.B
  have hLd := ok.dims.L
  have hn32 : nbmOf D P a ≤ 32 := by rcases hBd with e | e <;> rw [e] at hnb <;> omega
  exact WP.of_syms (WP.mono (lenLoop_ok L hBd (by rcases hBd with e | e <;> omega) hLd.1 b h28 h27 hn0 hnb
    (by omega) (len := (List.range P.L).map fun k => view t.mem (Sp s) (oLen + k)) fun k hk => by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk, Option.map_some,
        Option.getD_some])
    fun t' ⟨b', k', _⟩ y => ⟨⟨s, Pr, p, b', y.trans sy⟩, by rw [k'.get .r28, h28], fb, hfb, by rw [k'.get .r27, h27]⟩)

/-- The arguments of the compression of block `ac.2`. -/
def CA (D : Nat) (Z : Tabs) (P : Params) (ac : State × Nat) (u : State) : Prop :=
  LI D Z P ac u ∧ u.gpr .r3 = off (Sp ac.1) oSt ∧ u.gpr .r4 = off (Sp ac.1) (oY + P.B * ac.2) ∧
    u.gpr .r5 = BitVec.ofNat 64 1 ∧ u.gpr .r6 = off (Sp ac.1) oW

omit ok in
theorem compArgs_CA {ac : State × Nat} {u : State} (h : LI D Z P ac u) (hlg : 2 ^ lg P = P.B) (hlg7 : lg P ≤ 7)
    (hb : P.B * ac.2 + P.B ≤ 2048) : WP isa (.block (compArgs P)) u (CA D Z P ac) := by
  have h14 := h.1.r14
  refine WP.of_syms (wp_addi (h := by decide) fun u₁ p₁ f₁ => wp_lsl (h := by omega) fun u₂ p₂ f₂ =>
    wp_add fun u₃ p₃ f₃ => wp_addi (h := by decide) fun u₄ p₄ f₄ => wp_li (by decide) fun u₅ p₅ f₅ =>
    wp_addi (h := by decide) fun u₆ p₆ f₆ => wp_nil fun y₆ => ?_)
  have k₆ : Only [.r3, .r4, .r5, .r6] u u₆ := (p₁.trans (p₂.trans (p₃.trans (p₄.trans (p₅.trans p₆))))).mono
  obtain ⟨hb', h28, h26, hi, fb, hfb, h27⟩ := h
  refine ⟨⟨hb'.only' k₆ y₆, by rw [k₆.get .r28, h28], by rw [k₆.get .r26, h26], hi, fb, hfb,
    by rw [k₆.get .r27, h27]⟩, by rw [p₆.get .r3, p₅.get .r3, p₄.get .r3, p₃.get .r3, p₂.get .r3, f₁, h14],
    ?_, by rw [p₆.get .r5, f₅], by rw [f₆, p₅.get .r14, p₄.get .r14, p₃.get .r14, p₂.get .r14, p₁.get .r14, h14]⟩
  rw [p₆.get .r4, p₅.get .r4, f₄, f₃, f₂, p₁.get .r26, h26, p₂.get .r14, p₁.get .r14, h14,
    ofNat_shl (by rw [hlg]; omega), hlg]
  show _ = Sp ac.1 + _
  rw [BitVec.add_comm (BitVec.ofNat 64 _) (Sp ac.1), BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega

theorem comp_LI {ac : State × Nat} {u : State} (h : CA D Z P ac u) (hb : P.B * ac.2 + P.B ≤ 2048) :
    WP isa (tcall hArg 3 Z.f.comp) u (LI D Z P ac) := by
  obtain ⟨⟨⟨s, Pr, p, b, sy⟩, h28, h26, hi, fb, hfb, h27⟩, h3, h4, h5, h6⟩ := h
  have X := lOk D Z
  have hS : Sp s = Sp ac.1 := (X.agree p).S
  exact WP.mono (compM_ok (X.fits Pr) ((tabH D Z).tab Pr) ok.callee ok.dims.N.2 ok.dims.so.2 b sy (b := P.B * ac.2)
    (by rw [h3, hS]) (by rw [h4, hS]) h5 (by rw [h6, hS]) hb) fun u' ⟨⟨b', g', _⟩, y'⟩ =>
      ⟨⟨s, Pr, p, b', y'⟩, by rw [g' _ (by decide), h28], by rw [g' _ (by decide), h26], hi, fb, hfb,
        by rw [g' _ (by decide), h27]⟩

theorem sel_LI {ac : State × Nat} {u : State} (h : LI D Z P ac u) : WP isa (selHash P) u (LI D Z P ac) := by
  obtain ⟨hnb, hn0⟩ := nbm_le ok h.1
  obtain ⟨⟨s, Pr, p, b, sy⟩, h28, h26, hi, fb, hfb, h27⟩ := h
  have L := agree_lay Pr p
  have hBd := ok.dims.B
  have hn32 : nbmOf D P ac.1 ≤ 32 := by rcases hBd with e | e <;> rw [e] at hnb <;> omega
  exact WP.of_syms (WP.mono (selHash_ok L ok.dims.N.1 ok.dims.N.2 b h26 h27 (by omega) (by omega))
    fun u' ⟨b', k', _⟩ y => ⟨⟨s, Pr, p, b', y.trans sy⟩, by rw [k'.get .r28, h28], by rw [k'.get .r26, h26], hi,
      fb, hfb, by rw [k'.get .r27, h27]⟩)

/-- After the step of the compression loop. -/
def LS (D : Nat) (Z : Tabs) (P : Params) (ac : State × Nat) (u : State) : Prop :=
  BL D Z ac.1 u ∧ u.gpr .r28 = BitVec.ofNat 64 (nbmOf D P ac.1 - (ac.2 + 1)) ∧
    u.gpr .r26 = BitVec.ofNat 64 (ac.2 + 1) ∧ ∃ fb < nbmOf D P ac.1, u.gpr .r27 = BitVec.ofNat 64 fb

omit ok in
theorem step_LS {ac : State × Nat} {u : State} (h : LI D Z P ac u) :
    WP isa (.block [.addi .r26 .r26 1, .subi .r28 .r28 1]) u (LS D Z P ac) := by
  obtain ⟨hb, h28, h26, hi, fb, hfb, h27⟩ := h
  refine WP.of_syms (wp_addi fun u₁ p₁ f₁ => wp_subi fun u₂ p₂ f₂ => wp_nil fun y₂ => ?_)
  have k₂ : Only [.r26, .r28] u u₂ := (p₁.trans p₂).mono
  refine ⟨hb.only' k₂ y₂, ?_, by rw [p₂.get .r26, f₁, h26, BitVec.ofNat_add_ofNat], fb, hfb,
    by rw [k₂.get .r27, h27]⟩
  rw [f₂, p₁.get .r28, h28, show nbmOf D P ac.1 - ac.2 = (nbmOf D P ac.1 - (ac.2 + 1)) + 1 by omega,
    ← BitVec.ofNat_add_ofNat, BitVec.add_sub_cancel]

omit ok in
theorem ca_args {ac : State × Nat} {t u : State} (h : CA D Z P ac t) (o : Only [.r12] t u) (y : u.syms = t.syms)
    (hb : P.B * ac.2 + P.B ≤ 2048) (hN : P.N ≤ 64) (hso : P.so ≤ 1024) :
    ∃ s, CompArgs Sp (vP D) P s u (P.B * ac.2) ∧ u.gpr .r3 = off (Sp ac.1) oSt ∧
      u.gpr .r4 = off (Sp ac.1) (oY + P.B * ac.2) ∧ u.gpr .r5 = BitVec.ofNat 64 1 ∧ u.gpr .r6 = off (Sp ac.1) oW ∧
      u.sp = fb ac.1 := by
  obtain ⟨⟨hm, -⟩, x3, x4, x5, x6⟩ := h
  obtain ⟨s, Pr, p, b, -⟩ := hm.only' o y
  have X := lOk D Z
  have hS : Sp s = Sp ac.1 := (X.agree p).S
  refine ⟨s, ⟨X.fits Pr, b, by rw [o.get .r3, x3, hS], by rw [o.get .r4, x4, hS], by rw [o.get .r5, x5],
    by rw [o.get .r6, x6, hS], hb, hN, hso⟩, by rw [o.get .r3, x3], by rw [o.get .r4, x4], by rw [o.get .r5, x5],
    by rw [o.get .r6, x6], Base.spA X.s p b⟩

end

theorem hInit_two {α : Type} {Φ : α → State → Prop} {an : α → State} (hH : HashOK Z.H) (cH : HashCT hH)
    (hb : ∀ x t, Φ x t → BL D Z (an x) t) : RelCT isa (Two Φ) (hInit Z.f hArg) fun _ _ => True := by
  have X := lOk D Z
  have A := tabH D Z
  refine RelCT.seq (two_post (Ψ := fun x t => BL D Z (an x) t ∧ t.gpr .r3 = off (Sp (an x)) oSt)
      (st_taint (bl_pins hb [])) fun x t h => WP.of_syms (wp_addi fun t' o e => wp_nil fun y =>
        ⟨(hb x t h).only' o y, by rw [e, (hb x t h).r14]⟩))
    (tcall_twoM X.s A (an := an) (fun x t h => h.1) (k := 0) (by decide)
      (fun P p => ⟨(A.tab P).ok.i, by rw [Nat.mul_zero, BitVec.add_zero]; exact (A.tab P).mem.1, A.ai p⟩)
      (init_ct (S := Sp) (vf := vP D) cH fun u₁ u₂ hp => ?_))
  obtain ⟨x, ⟨t₁, h₁, o₁, y₁⟩, ⟨t₂, h₂, o₂, y₂⟩⟩ := hp
  obtain ⟨s₁, P₁, p₁, b₁, -⟩ := h₁.1.only' o₁ y₁
  obtain ⟨s₂, P₂, p₂, b₂, -⟩ := h₂.1.only' o₂ y₂
  exact ⟨s₁, s₂, X.fits P₁, b₁, by rw [o₁.get .r3, h₁.2, (X.agree p₁).S], X.fits P₂, b₂,
    by rw [o₂.get .r3, h₂.2, (X.agree p₂).S], by rw [o₁.get .r3, o₂.get .r3, h₁.2, h₂.2],
    (Base.spA X.s p₁ b₁).trans (Base.spA X.s p₂ b₂).symm⟩

/-- `ctHash` keeps `BL`. -/
theorem ctHash_wp (hH : HashOK Z.H) (hD : Z.H.D = D) (ok : CtOK P md Z.cc Z.dc) {a t : State} (h : BL D Z a t)
    (hs : ∃ sl < (dbLen D a).toNat, t.gpr .r25 = BitVec.ofNat 64 sl) :
    WP isa (ctHash Z.H P Z.f hArg) t (BL D Z a) := by
  refine WP.seq (WP.mono (ctLens_wp ok hD h hs) fun t₁ h₁ => ?_)
  refine WP.seq (WP.mono (hInit_K1 hH h₁) fun t₂ h₂ => ?_)
  refine WP.seq (WP.mono (pad80_K1 ok h₂) fun t₃ h₃ => ?_)
  refine WP.seq (WP.mono (lenField_K2 ok h₃) fun t₄ h₄ => ?_)
  refine WP.seq (WP.mono (lenLoop_K2 ok h₄) fun t₅ h₅ => ?_)
  obtain ⟨hnb, hn0⟩ := nbm_le ok h₅.1
  obtain ⟨⟨s, Pr, p, b, sy⟩, h28, fb, hfb, h27⟩ := h₅
  have L := agree_lay Pr p
  have X := lOk D Z
  refine WP.seq (WP.mono (compLoop_ok L ((tabH D Z).tab Pr) ok b sy h28 h27 hn0 hnb hfb) fun t₆ I => ?_)
  refine WP.seq (WP.of_syms (wp_addi (h := by decide) fun t₇ o₇ e₇ => wp_addi (h := by decide)
    fun t₈ o₈ e₈ => wp_nil fun y₈ => ?_))
  have k : Only [.r3, .r4] t₆ t₈ := (o₇.trans o₈).mono
  exact WP.mono (digM_ok (X.fits Pr) ((tabH D Z).tab Pr) ok.dig ok.digNF ok.dims.N.2 (I.base.only (X.fits Pr) k)
    (y₈.trans I.sy) (by rw [o₈.get .r3, e₇, I.base.r14]) (by rw [e₈, o₇.get .r14, I.base.r14]))
    fun t' ⟨⟨b', _⟩, y'⟩ => ⟨s, Pr, p, b', y'⟩

/-- `ctHash` from some salt length below `dbLen` in `r25`, in both runs. -/
theorem ctHash_ct (hH : HashOK Z.H) (cH : HashCT hH) (hD : Z.H.D = D) (ok : CtOK P md Z.cc Z.dc)
    (ct : CtTaint P) (hcc : ConstantTime isa (compressK md).pre (compressK md).pub Z.cc)
    (hdc : ConstantTime isa (digestK md).pre (digestK md).pub Z.dc) :
    RelCT isa (Two fun a t => BL D Z a t ∧ ∃ sl < (dbLen D a).toNat, t.gpr .r25 = BitVec.ofNat 64 sl)
      (ctHash Z.H P Z.f hArg) fun _ _ => True := by
  have X := lOk D Z
  have A := tabH D Z
  obtain ⟨hlg1, hlg7, hlg⟩ := ok.dims.log
  refine two_seq (Ψ := K1 D Z P) (ctLens_taint Z.H ct (bl_pins (an := id) (fun _ _ h => h.1) []))
    (fun a t h => ctLens_wp ok hD h.1 h.2) ?_
  refine two_seq (Ψ := K1 D Z P) (hInit_two hH cH (an := id) fun _ _ h => h.1) (fun a t h => hInit_K1 hH h) ?_
  refine two_seq (Ψ := K1 D Z P) (pad80_taint ct (pins_r28 (an := id) (fun _ _ h => h.1) fun _ _ h => h.2.1))
    (fun a t h => pad80_K1 ok h) ?_
  refine two_seq (Ψ := K2 D Z P) (lenField_taint ct (bl_pins (an := id) (fun _ _ h => h.1) [.r14]))
    (fun a t h => lenField_K2 ok h) ?_
  refine two_seq (Ψ := K2 D Z P) (lenLoop_taint ct (pins_r28 (an := id) (fun _ _ h => h.1) fun _ _ h => h.2.1))
    (fun a t h => lenLoop_K2 ok h) ?_
  refine RelCT.seq (R := Two fun a t => BL D Z a t) ?_ ?_
  · -- The compression loop.
    let Ln := fun (n : Nat) (ac : State × Nat) (u : State) => LI D Z P ac u ∧ n = nbmOf D P ac.1 - ac.2
    have hbB : ∀ {ac u}, LI D Z P ac u → P.B * ac.2 + P.B ≤ 2048 := fun {ac u} h => by
      obtain ⟨hnb, -⟩ := nbm_le ok h.1
      have hi := h.2.2.2.1
      calc P.B * ac.2 + P.B = P.B * (ac.2 + 1) := (Nat.mul_succ _ _).symm
        _ ≤ P.B * nbmOf D P ac.1 := Nat.mul_le_mul_left _ hi
        _ = nbmOf D P ac.1 * P.B := Nat.mul_comm _ _
        _ ≤ 2048 := hnb
    have step : ∀ n, RelCT isa (Two (Ln n)) (.seq (.block (compArgs P)) (.seq (tcall hArg 3 Z.f.comp)
        (.seq (selHash P) (.block [.addi .r26 .r26 1, .subi .r28 .r28 1])))) fun s₁ s₂ =>
        isa.eval (.nonzero .d .r28) s₁ = isa.eval (.nonzero .d .r28) s₂ ∧
        (isa.eval (.nonzero .d .r28) s₁ = some false → Two (fun a t => BL D Z a t) s₁ s₂) ∧
        (isa.eval (.nonzero .d .r28) s₁ = some true → ∃ m < n, Two (Ln m) s₁ s₂) := fun n => by
      refine two_seq (Ψ := fun ac u => CA D Z P ac u ∧ n = nbmOf D P ac.1 - ac.2)
        (compArgs_taint ct (bl_pins (an := Prod.fst) (fun _ _ h => h.1.1) []))
        (fun ac u h => (compArgs_CA h.1 hlg hlg7 (hbB h.1)).mono fun u' h' => ⟨h', h.2⟩) ?_
      refine two_seq (Ψ := Ln n) (tcall_twoM X.s A (an := Prod.fst) (fun ac t h => h.1.1.1) (k := 3) (by decide)
          (fun P p => ⟨(A.tab P).ok.c, by rw [show 8 * 3 = 24 from rfl]; exact (A.tab P).mc, A.ac p⟩)
          (comp_ct (S := Sp) (vf := vP D) ok.callee hcc fun u₁ u₂ ⟨ac, ⟨t₁, h₁, o₁, y₁⟩, ⟨t₂, h₂, o₂, y₂⟩⟩ => ?_))
        (fun ac u h => (comp_LI ok h.1 (hbB h.1.1)).mono fun u' h' => ⟨h', h.2⟩) ?_
      · obtain ⟨s₁, C₁, x3, x4, x5, x6, xs⟩ := ca_args h₁.1 o₁ y₁ (hbB h₁.1.1) ok.dims.N.2 ok.dims.so.2
        obtain ⟨s₂, C₂, z3, z4, z5, z6, zs⟩ := ca_args h₂.1 o₂ y₂ (hbB h₂.1.1) ok.dims.N.2 ok.dims.so.2
        refine ⟨s₁, s₂, _, _, C₁, C₂, fun r hr => ?_, xs.trans zs.symm⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        exacts [x3.trans z3.symm, x4.trans z4.symm, x5.trans z5.symm, x6.trans z6.symm]
      refine two_seq (Ψ := Ln n) (selHash_taint ct (bl_pins (an := Prod.fst) (fun _ _ h => h.1.1) [.r14]))
        (fun ac u h => (sel_LI ok h.1).mono fun u' h' => ⟨h', h.2⟩) ?_
      refine (two_post (Ψ := fun ac u => LS D Z P ac u ∧ n = nbmOf D P ac.1 - ac.2 ∧ ac.2 < nbmOf D P ac.1)
        (compStep_taint (bl_pins (an := Prod.fst) (fun _ _ h => h.1.1) []))
        fun ac u h => (step_LS h.1).mono fun u' h' => ⟨h', h.2, h.1.2.2.2.1⟩).mono (fun _ _ h => h)
          fun s₁ s₂ ⟨ac, ⟨h₁, hn, hi⟩, ⟨h₂, _, _⟩⟩ => ?_
      have hnb' : nbmOf D P ac.1 - (ac.2 + 1) < 2 ^ 64 := by
        have := (nbm_le ok h₁.1).1
        have : nbmOf D P ac.1 ≤ nbmOf D P ac.1 * P.B := Nat.le_mul_of_pos_right _ ok.dims.pos
        omega
      rw [eval_nonzero, eval_nonzero, h₁.2.1, h₂.2.1, ne0_ofNat hnb']
      refine ⟨rfl, fun _ => ⟨ac.1, h₁.1, h₂.1⟩, fun e => ?_⟩
      have hlt : ac.2 + 1 < nbmOf D P ac.1 := by simp only [Option.some.injEq, decide_eq_true_eq] at e; omega
      exact ⟨nbmOf D P ac.1 - (ac.2 + 1), by omega, (ac.1, ac.2 + 1),
        ⟨⟨h₁.1, h₁.2.1, h₁.2.2.1, hlt, h₁.2.2.2⟩, rfl⟩, ⟨⟨h₂.1, h₂.2.1, h₂.2.2.1, hlt, h₂.2.2.2⟩, rfl⟩⟩
    refine RelCT.seq (two_post (Ψ := fun a t => LI D Z P (a, 0) t)
        (compInit_taint (bl_pins (an := id) (fun _ _ h => h.1) [])) fun a t h => ?_)
      ((RelCT.exists_ fun n => RelCT.loop (fun n => Two (Ln n)) step n).mono
        (fun _ _ ⟨a, h₁, h₂⟩ => ⟨nbmOf D P a - 0, (a, 0), ⟨h₁, rfl⟩, ⟨h₂, rfl⟩⟩) fun _ _ h => h)
    obtain ⟨-, hn0⟩ := nbm_le ok h.1
    obtain ⟨hm, h28, fb, hfb, h27⟩ := h
    exact WP.of_syms (wp_li (by decide) fun t' o e => wp_nil fun y =>
      ⟨hm.only' o y, by rw [o.get .r28, h28, Nat.sub_zero], e, hn0, fb, hfb, by rw [o.get .r27, h27]⟩)
  · -- The digest.
    have hN := ok.dims.N
    refine two_seq (Ψ := fun a t => BL D Z a t ∧ t.gpr .r3 = off (Sp a) oSel ∧ t.gpr .r4 = off (Sp a) oDig)
      (digArgs_taint (bl_pins (an := id) (fun _ _ h => h) [])) (fun a t h => WP.of_syms (wp_addi (h := by decide)
        fun t₁ o₁ e₁ => wp_addi (h := by decide) fun t₂ o₂ e₂ => wp_nil fun y => ?_)) ?_
    · have k : Only [.r3, .r4] t t₂ := (o₁.trans o₂).mono
      exact ⟨h.only' k y, by rw [o₂.get .r3, e₁, h.r14], by rw [e₂, o₁.get .r14, h.r14]⟩
    refine tcall_twoM X.s A (an := id) (fun a t h => h.1) (k := 4) (by decide)
      (fun P p => ⟨(A.tab P).ok.d, by rw [show 8 * 4 = 32 from rfl]; exact (A.tab P).md, A.ad p⟩)
      (dig_ct (S := Sp) (vf := vP D) (P := P) ok.dig hdc fun u₁ u₂ ⟨a, ⟨t₁, h₁, o₁, y₁⟩, ⟨t₂, h₂, o₂, y₂⟩⟩ => ?_)
    obtain ⟨s₁, P₁, p₁, b₁, -⟩ := h₁.1.only' o₁ y₁
    obtain ⟨s₂, P₂, p₂, b₂, -⟩ := h₂.1.only' o₂ y₂
    have S₁ : Sp s₁ = Sp a := (X.agree p₁).S
    have S₂ : Sp s₂ = Sp a := (X.agree p₂).S
    refine ⟨s₁, s₂, ⟨X.fits P₁, b₁, by rw [o₁.get .r3, h₁.2.1, S₁], by rw [o₁.get .r4, h₁.2.2, S₁], hN.2⟩,
      ⟨X.fits P₂, b₂, by rw [o₂.get .r3, h₂.2.1, S₂], by rw [o₂.get .r4, h₂.2.2, S₂], hN.2⟩, fun r hr => ?_,
      (Base.spA X.s p₁ b₁).trans (Base.spA X.s p₂ b₂).symm⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [o₁.get .r3, o₂.get .r3, h₁.2.1, h₂.2.1]
    · rw [o₁.get .r4, o₂.get .r4, h₁.2.2, h₂.2.2]

end CtHash

end VG.Proof.RsaPss.PPC64LE
