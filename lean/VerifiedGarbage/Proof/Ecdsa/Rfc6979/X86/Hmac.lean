import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Hash
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Calls

/-!
# Deterministic ECDSA on x86 (32-bit): one HMAC

`HMAC_K(data)` (`Cfg.hmac`), as on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Hmac.lean`),
for the key `K` (of the hash function's output length) in the frame and
`len` bytes of data in the frame or in `scratch` above HMAC's working space
(`DataOk`), written to the frame at `dst`: HMAC's `init` with `K`
(`init_step`), the streaming `update` on the inner state (`upd_step`), and
HMAC's `finalize` (`fin_step`), each called in a frame of its arguments
(`hi_frame`, `upd_frame`, `hf_frame`), for any hash function `P`. They
change only HMAC's states and working space (the first 2256 bytes of
`scratch`), the 76 bytes below the frame, and `dst` (`hmac_ok`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.Impl.Ecdsa.Rfc6979.X86
open VG.Proof.Pbkdf2.Whole.X86 (HiArgs HfArgs hi_frame hf_frame hi5 hf6)
open VG.Proof.Pbkdf2.Stream.X86 (UpdArgs upd_frame upd6)

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

/-! ## Pointers into `scratch` and the frame -/

namespace Lay.Ok

theorem scrv (hL : L.Ok) {o : Nat} (ho : o < 8192) :
    (L.a3 + BitVec.ofNat 32 o).setWidth 64 = L.scr + BitVec.ofNat 64 o :=
  addr_eq (by have := hL.nc; omega)

theorem scrN (hL : L.Ok) {o : Nat} (ho : o < 8192) : (L.a3 + BitVec.ofNat 32 o).toNat = L.a3.toNat + o := by
  have := hL.nc
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem frv (hL : L.Ok) {o : Nat} (ho : o < 216 + 4 * L.e) :
    (L.F + BitVec.ofNat 32 o).setWidth 64 = L.B + BitVec.ofNat 64 (76 + o) := hL.addrF ho

theorem FN (hL : L.Ok) : L.F.toNat = L.E.toNat - (196 + 4 * L.e) := sub_toNat (by have := hL.e272; omega)

theorem frN (hL : L.Ok) {o : Nat} (ho : o < 216 + 4 * L.e) : (L.F + BitVec.ofNat 32 o).toNat = L.E.toNat - (196 + 4 * L.e) + o := by
  have := hL.e272; have := hL.e20
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega), hL.FN,
    Nat.mod_eq_of_lt (by omega)]

/-- Two ranges of `scratch`. -/
theorem scr_disj (hL : L.Ok) {a n b k : Nat} (h : a + n ≤ b ∨ b + k ≤ a) (ha : a < 8192) (hb : b < 8192)
    (han : a + n ≤ 8192) (hbk : b + k ≤ 8192) :
    Region.Disjoint ⟨(L.a3 + BitVec.ofNat 32 a).setWidth 64, n⟩ ⟨(L.a3 + BitVec.ofNat 32 b).setWidth 64, k⟩ := by
  have := hL.nc
  rw [hL.scrv ha, hL.scrv hb]
  exact Offset.disjoint _ h (by omega) (by omega)

/-- A range of the frame, and one of `scratch`. -/
theorem fr_scr (hL : L.Ok) {o n b k : Nat} (ho : o + n ≤ 196 + 4 * L.e) (hb : b < 8192) (hbk : b + k ≤ 8192) :
    Region.Disjoint ⟨(L.F + BitVec.ofNat 32 o).setWidth 64, n⟩ ⟨(L.a3 + BitVec.ofNat 32 b).setWidth 64, k⟩ := by
  rw [hL.frv (by omega), hL.scrv hb]
  exact hL.stk_scr (by omega) hbk

/-- The 76 bytes below the frame, and a range of `scratch`. -/
theorem low_scr' (hL : L.Ok) {b k : Nat} (hb : b < 8192) (hbk : b + k ≤ 8192) :
    Region.Disjoint (below L.F 76) ⟨(L.a3 + BitVec.ofNat 32 b).setWidth 64, k⟩ := by
  rw [hL.below_F, hL.scrv hb]; exact hL.low_scr hbk

/-- The 76 bytes below the frame, and a range of the frame. -/
theorem low_fr (hL : L.Ok) {o n : Nat} (ho : o + n ≤ 196 + 4 * L.e) :
    Region.Disjoint (below L.F 76) ⟨(L.F + BitVec.ofNat 32 o).setWidth 64, n⟩ := by
  have := hL.nB
  rw [hL.below_F, hL.frv (by omega)]; exact Offset.base_disjoint _ (by omega) (by omega)

/-- The 48 bytes below the frame (the streaming functions' calls) are among the 76. -/
theorem below48 (hL : L.Ok) : Region.Sub (below L.F 48) (below L.F 76) :=
  below_sub (by omega) (by rw [hL.FN]; have := hL.e272; omega)

end Lay.Ok

theorem within_scr (hL : L.Ok) {a n : Nat} (ha : a < 8192) (h : a + n ≤ 8192) :
    Within ⟨(L.a3 + BitVec.ofNat 32 a).setWidth 64, n⟩ L.SCR := by
  rw [hL.scrv ha]; exact within_off _ h

theorem within_frv (hL : L.Ok) {o n : Nat} (h : o + n ≤ 196 + 4 * L.e) :
    Within ⟨(L.F + BitVec.ofNat 32 o).setWidth 64, n⟩ L.FR := by
  rw [hL.frv (by omega)]; exact within_fr _ (by omega) (by omega)

/-- Where the data may be: in the frame below the saved registers, or in
`scratch` above HMAC's working space. -/
def DataOk {dn : Nat} (L : Lay dn) (dv : BitVec 32) (len : Nat) : Prop :=
  (∃ o, dv = L.F + BitVec.ofNat 32 o ∧ o + len ≤ 180) ∨
    (∃ o, dv = L.a3 + BitVec.ofNat 32 o ∧ 2256 ≤ o ∧ o + len ≤ 4096)

namespace DataOk

variable {dv : BitVec 32} {len : Nat}

theorem low (hd : DataOk L dv len) (hL : L.Ok) : Region.Disjoint (below L.F 76) ⟨dv.setWidth 64, len⟩ := by
  rcases hd with ⟨o, rfl, h⟩ | ⟨o, rfl, h₁, h₂⟩
  · exact hL.low_fr (by omega)
  · exact hL.low_scr' (by omega) (by omega)

/-- The data is apart from HMAC's states and working space. -/
theorem work (hd : DataOk L dv len) (hL : L.Ok) {e k : Nat} (h : e + k ≤ 2256) :
    Region.Disjoint ⟨dv.setWidth 64, len⟩ ⟨(L.a3 + BitVec.ofNat 32 e).setWidth 64, k⟩ := by
  rcases hd with ⟨o, rfl, h'⟩ | ⟨o, rfl, h₁, h₂⟩
  · exact hL.fr_scr (by omega) (by omega) (by omega)
  · exact hL.scr_disj (by omega) (by omega) (by omega) (by omega) (by omega)

theorem within (hd : DataOk L dv len) (hL : L.Ok) :
    ∃ R ∈ [L.D, L.DG, L.ARGS, L.FR, L.OUT, L.SCR], Within ⟨dv.setWidth 64, len⟩ R := by
  rcases hd with ⟨o, rfl, h⟩ | ⟨o, rfl, h₁, h₂⟩
  · exact ⟨L.FR, by simp, within_frv hL (by omega)⟩
  · exact ⟨L.SCR, by simp, within_scr hL (by omega) (by omega)⟩

theorem fits (hd : DataOk L dv len) (hL : L.Ok) : dv.toNat + len ≤ 2 ^ 32 := by
  rcases hd with ⟨o, rfl, h⟩ | ⟨o, rfl, h₁, h₂⟩
  · rw [hL.frN (by omega)]; have := hL.e20; have := hL.e272; omega
  · rw [hL.scrN (by omega)]; have := hL.nc; omega

end DataOk

/-! ## HMAC's `init` -/

/-- The arguments of HMAC's `init`. -/
theorem initArgs_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (D : Nat) :
    WP isa (.block (Cfg.hmacArgs₁ L.wide D)) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧
      t'.gpr .edi = L.a3 + BitVec.ofNat 32 0 ∧ t'.gpr .esi = L.a3 + BitVec.ofNat 32 192 ∧
      t'.gpr .edx = L.F + BitVec.ofNat 32 0 ∧ t'.gpr .ecx = BitVec.ofNat 32 D ∧
      t'.gpr .ebp = L.a3 + BitVec.ofNat 32 384 := by
  rw [Cfg.hmacArgs₁, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (scr_ok hL hc (d := .edi) (by decide) 0) fun u₁ h₁ => ?_
  refine WP.mono (scr_ok hL h₁.ctx (d := .esi) (by decide) 192) fun u₂ h₂ => ?_
  refine WP.mono (fr_ok hL h₂.ctx (d := .edx) (by decide) 0) fun u₃ h₃ => ?_
  refine WP.mono (movi_ok hL h₃.ctx (d := .ecx) (by decide) _) fun u₄ h₄ => ?_
  refine WP.mono (scr_ok hL h₄.ctx (d := .ebp) (by decide) 384) fun u₅ h₅ => ?_
  refine ⟨h₅.ctx, by rw [h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem], ?_, ?_, ?_, ?_, h₅.val⟩
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.keep _ (by decide), h₁.val]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.val]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.val]
  · rw [h₅.keep _ (by decide), h₄.val]

/-- The writes of a call, within HMAC's working space and the stack below the frame. -/
theorem safe_call (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {ws : List Region} (hs : ∀ r ∈ ws, Safe L r) {n : Nat}
    (hn : n ≤ 76) : ∀ r ∈ ws ++ [below (u.gpr .esp) n], Safe L r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact hs r hr
  · simp only [List.mem_singleton] at hr; subst hr
    refine .inr (.inr (.inl (sub_trans (below_sub hn (by rw [hc.esp, hL.FN]; have := hL.e272; omega)) ?_)))
    rw [hc.esp, hL.below_F]; exact Region.sub_prefix (by omega)

/-- The key `K`: the first `D` bytes of the frame. -/
abbrev keyOf (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) : List Byte :=
  Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 76) P.F.H.D

/-- After HMAC's `init`: HMAC's states for the key `K` in the frame on entry `t`. -/
structure Inited (P : RfcHash) {dn : Nat} (L : Lay dn) (g : Reg → BitVec 32) (m₀ : Mem) (t u : State) : Prop where
  ctx : Ctx L g m₀ u
  frame : Frame [⟨L.scr, 2256⟩, ⟨L.B, 76⟩] t.mem u.mem
  inner : P.ok.hH.SH.Repr u.mem (L.scr + BitVec.ofNat 64 0)
    (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.ok.hH.SH.H (keyOf P L t.mem)) Spec.Hmac.ipad)
  outer : P.ok.hH.SH.Repr u.mem (L.scr + BitVec.ofNat 64 192)
    (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.ok.hH.SH.H (keyOf P L t.mem)) Spec.Hmac.opad)

theorem scr_work {e k : Nat} (h : e + k ≤ 2256) : Region.Sub ⟨L.scr + BitVec.ofNat 64 e, k⟩ ⟨L.scr, 2256⟩ :=
  Offset.sub_base _ h

theorem scr_work' (hL : L.Ok) {e k : Nat} (he : e < 8192) (h : e + k ≤ 2256) :
    Region.Sub ⟨(L.a3 + BitVec.ofNat 32 e).setWidth 64, k⟩ ⟨L.scr, 2256⟩ := by
  rw [hL.scrv he]; exact scr_work h

theorem initA (hL : L.Ok) {u : State} (hcu : Ctx L g m₀ u) (hdi : u.gpr .edi = L.a3 + BitVec.ofNat 32 0)
    (hsi : u.gpr .esi = L.a3 + BitVec.ofNat 32 192) (hdx : u.gpr .edx = L.F + BitVec.ofNat 32 0)
    (hcx : u.gpr .ecx = BitVec.ofNat 32 P.F.H.D) (hbp : u.gpr .ebp = L.a3 + BitVec.ofNat 32 384) :
    HiArgs P.ok.hH.SH P.ok.Wi u (L.a3 + BitVec.ofNat 32 0) (L.a3 + BitVec.ofNat 32 192)
      (L.F + BitVec.ofNat 32 0) (L.a3 + BitVec.ofNat 32 384) P.F.H.D := by
  have hS := P.ok.hH.hS
  have hB := P.ok.hH.hB
  have nc := hL.nc
  have hsp : Proof.Pbkdf2.Whole.X86.stk u = below L.F 76 := by
    show below (u.gpr .esp) 76 = _; rw [hcu.esp]
  exact
    { edi := hdi, esi := hsi, edx := hdx, ecx := hcx, ebp := hbp
      klB := by rw [hB]; nums
      kl32 := by nums
      sp := by rw [hcu.esp, hL.FN]; have := hL.e272; omega
      cr := hcu.covers fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨L.FR, by simp, within_frv hL (by nums)⟩
      cw := hcu.coversW fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;>
          exact ⟨L.SCR, by simp, within_scr hL (by omega) (by first | nums | (rw [hS]; nums))⟩
      i_o := hL.scr_disj (by rw [hS]; nums) (by omega) (by omega) (by rw [hS]; nums) (by rw [hS]; nums)
      i_k := (hL.fr_scr (by nums) (by omega) (by rw [hS]; nums)).symm
      i_s := hL.scr_disj (by rw [hS]; nums) (by omega) (by omega) (by rw [hS]; nums) (by nums)
      o_k := (hL.fr_scr (by nums) (by omega) (by rw [hS]; nums)).symm
      o_s := hL.scr_disj (by rw [hS]; nums) (by omega) (by omega) (by rw [hS]; nums) (by nums)
      k_s := hL.fr_scr (by nums) (by omega) (by nums)
      b_i := by rw [hsp]; exact hL.low_scr' (by omega) (by rw [hS]; nums)
      b_o := by rw [hsp]; exact hL.low_scr' (by omega) (by rw [hS]; nums)
      b_k := by rw [hsp]; exact hL.low_fr (by nums)
      b_s := by rw [hsp]; exact hL.low_scr' (by omega) (by nums)
      ni := by rw [hL.scrN (by omega), hS]; nums
      no := by rw [hL.scrN (by omega), hS]; nums
      nk := by rw [hL.frN (by omega)]; have := hL.e20; have := hL.e272; nums
      nsc := by rw [hL.scrN (by omega)]; nums }

theorem init_step (hL : L.Ok) (hw : L.wide = (cfgOf P).wide) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.seq (.block (Cfg.hmacArgs₁ (cfgOf P).wide P.F.H.D))
      (.frame (.push [.ebp, .ecx, .edx, .esi, .edi]) (.call P.F.hiN P.F.hiC) (.pop .eax 5))) t
      (Inited P L g m₀ t) := by
  have hA := initArgs_ok hL hc P.F.H.D
  rw [hw] at hA
  refine WP.seq (WP.mono hA fun u ⟨hcu, hmu, hdi, hsi, hdx, hcx, hbp⟩ => ?_)
  have a := initA (P := P) hL hcu hdi hsi hdx hcx hbp
  have hS := P.ok.hH.hS
  refine WP.of_syms ?_
  refine hi_frame P.ok.hi P.ok.hiSp P.ok.hiSU a fun u' af hi ho hsy => ?_
  have hsafe : ∀ r ∈ [(⟨(L.a3 + BitVec.ofNat 32 0).setWidth 64, P.ok.hH.SH.stateBytes⟩ : Region),
      ⟨(L.a3 + BitVec.ofNat 32 192).setWidth 64, P.ok.hH.SH.stateBytes⟩,
      ⟨(L.a3 + BitVec.ofNat 32 384).setWidth 64, P.ok.Wi * 8⟩], Region.Sub r ⟨L.scr, 2256⟩ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> exact scr_work' hL (by omega) (by first | nums | (rw [hS]; nums))
  have hk : Spec.Sha256.bytesAt u.mem ((L.F + BitVec.ofNat 32 0).setWidth 64) P.F.H.D = keyOf P L t.mem := by
    rw [hmu, hL.frv (by omega)]
  refine ⟨hcu.keep (hsy := hsy) hL af.rd af.wr af.esp af.frame
      (safe_call hL hcu (fun r hr => .inr (.inl (sub_trans (hsafe r hr) (Region.sub_prefix (by omega)))))
        (Nat.le_refl _)),
    hmu ▸ af.frame.sub fun r hr => ?_, ?_, ?_⟩
  · rcases List.mem_append.mp hr with hr | hr
    · exact ⟨⟨L.scr, 2256⟩, by simp, hsafe r hr⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨L.B, 76⟩, by simp, by
        show Region.Sub (below (u.gpr .esp) 76) _; rw [hcu.esp, hL.below_F]; exact sub_refl _⟩
  · rw [← hL.scrv (by omega), ← hk]; exact hi
  · rw [← hL.scrv (by omega), ← hk]; exact ho

/-! ## The streaming `update` -/

theorem xorPad_length (k : List Byte) (p : Byte) : (Spec.Hmac.xorPad k p).length = k.length :=
  List.length_map _

theorem blockKey_length {k : List Byte} (hk : k.length = P.F.H.D) :
    (Spec.Hmac.blockKey P.ok.hH.SH.H k).length = P.F.H.B := by
  have hB := P.ok.hH.hB
  have hDB : P.F.H.D < P.F.H.B := by nums
  simp only [Spec.Hmac.blockKey, hk, hB, show ¬ P.F.H.B < P.F.H.D by omega, ite_false, List.length_append,
    List.length_replicate]
  omega

theorem keyOf_length (m : Mem) : (keyOf P L m).length = P.F.H.D := by simp [keyOf, Spec.Sha256.bytesAt]

/-- `d ← v; e ← w`. -/
theorem movi2_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {d e : Reg} (hd : d ≠ .esp) (he : e ≠ .esp)
    (hde : e ≠ d) (v w : BitVec 32) :
    WP isa (.block [.mov d (.imm v), .mov e (.imm w)]) u fun u' => Ctx L g m₀ u' ∧ u'.mem = u.mem ∧
      u'.gpr d = v ∧ u'.gpr e = w ∧ ∀ r, r ≠ d → r ≠ e → u'.gpr r = u.gpr r :=
  Wp.wp_movi fun u₁ v₁ => Wp.wp_movi fun u₂ v₂ => WP.block_nil
    ⟨(Upd.of_wp hL (Upd.of_wp hL hc hd v₁).ctx he v₂).ctx, by rw [v₂.mem, v₁.mem],
      by rw [v₂.other _ (Ne.symm hde), v₁.gpr], v₂.gpr, fun r h₁ h₂ => by rw [v₂.other _ h₂, v₁.other _ h₁]⟩

theorem updArgs_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {dataA : List Instr} {dv : BitVec 32} {len : Nat}
    (hdA : ∀ u, Ctx L g m₀ u → WP isa (.block dataA) u (Upd L g m₀ u .edx dv)) (B : Nat) :
    WP isa (.block (Cfg.hmacArgs₂ L.wide B dataA len)) u fun u' => Ctx L g m₀ u' ∧
      u'.mem = u.mem ∧ u'.gpr .edi = L.a3 + BitVec.ofNat 32 0 ∧ u'.gpr .esi = BitVec.ofNat 32 B ∧
      u'.gpr .eax = 0 ∧ u'.gpr .edx = dv ∧ u'.gpr .ecx = BitVec.ofNat 32 len ∧
      u'.gpr .ebp = L.a3 + BitVec.ofNat 32 384 := by
  rw [Cfg.hmacArgs₂, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (scr_ok hL hc (d := .edi) (by decide) 0) fun u₁ h₁ => ?_
  refine WP.mono (movi2_ok hL h₁.ctx (d := .esi) (e := .eax) (by decide) (by decide) (by decide) _ _)
    fun u₂ ⟨c₂, m₂, si₂, ax₂, k₂⟩ => ?_
  refine WP.mono (hdA u₂ c₂) fun u₃ h₃ => ?_
  refine WP.mono (movi_ok hL h₃.ctx (d := .ecx) (by decide) _) fun u₄ h₄ => ?_
  refine WP.mono (scr_ok hL h₄.ctx (d := .ebp) (by decide) 384) fun u₅ h₅ => ?_
  refine ⟨h₅.ctx, by rw [h₅.mem, h₄.mem, h₃.mem, m₂, h₁.mem], ?_, ?_, ?_, ?_, ?_, h₅.val⟩
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), k₂ _ (by decide) (by decide), h₁.val]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), si₂]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), ax₂]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.val]
  · rw [h₅.keep _ (by decide), h₄.val]

/-- After the streaming `update`: the inner state holds the data too. -/
structure Updated (P : RfcHash) {dn : Nat} (L : Lay dn) (g : Reg → BitVec 32) (m₀ : Mem) (t : State)
    (dv : BitVec 32) (len : Nat) (u : State) : Prop where
  ctx : Ctx L g m₀ u
  frame : Frame [⟨L.scr, 2256⟩, ⟨L.B, 76⟩] t.mem u.mem
  inner : P.ok.hH.SH.Repr u.mem (L.scr + BitVec.ofNat 64 0)
    (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.ok.hH.SH.H (keyOf P L t.mem)) Spec.Hmac.ipad ++
      Spec.Sha256.bytesAt t.mem (dv.setWidth 64) len)
  outer : P.ok.hH.SH.Repr u.mem (L.scr + BitVec.ofNat 64 192)
    (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.ok.hH.SH.H (keyOf P L t.mem)) Spec.Hmac.opad)

/-- The arguments of the streaming `update`. -/
theorem updA (hL : L.Ok) {w : State} (hcw : Ctx L g m₀ w) {dv : BitVec 32} {len : Nat} (hd : DataOk L dv len)
    (hlen : len ≤ 256) (hdi : w.gpr .edi = L.a3 + BitVec.ofNat 32 0)
    (hsi : w.gpr .esi = BitVec.ofNat 32 P.F.H.B) (hax : w.gpr .eax = 0) (hdx : w.gpr .edx = dv)
    (hcx : w.gpr .ecx = BitVec.ofNat 32 len) (hbp : w.gpr .ebp = L.a3 + BitVec.ofNat 32 384) :
    UpdArgs P.ok.hH w .esi .edi (L.a3 + BitVec.ofNat 32 0) dv (L.a3 + BitVec.ofNat 32 384)
      (BitVec.ofNat 32 P.F.H.B) len := by
  have hsp : Region.Sub (Proof.Pbkdf2.Stream.X86.stk w) (below L.F 76) := by
    show Region.Sub (below (w.gpr .esp) 48) _; rw [hcw.esp]; exact hL.below48
  exact
    { hst := hdi, hlo := hsi, eax := hax, ecx := hcx, edx := hdx, ebp := hbp, hr := by decide, hl := by decide
      hlen := by omega
      sp48 := by rw [hcw.esp, hL.FN]; have := hL.e272; omega
      cd := hcw.covers fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hd.within hL
      cw := hcw.coversW fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact ⟨L.SCR, by simp, within_scr hL (by omega) (by nums)⟩
      st_sc := hL.scr_disj (by nums) (by omega) (by omega) (by nums) (by nums)
      d_st := hd.work hL (by nums)
      d_sc := hd.work hL (by nums)
      b_st := (hL.low_scr' (by omega) (by nums)).sub_left hsp
      b_d := (hd.low hL).sub_left hsp
      b_sc := (hL.low_scr' (by omega) (by nums)).sub_left hsp
      nst := by rw [hL.scrN (by omega)]; have := hL.nc; nums
      nd := hd.fits hL
      nsc := by rw [hL.scrN (by omega)]; have := hL.nc; nums }

theorem upd_step (hL : L.Ok) (hw : L.wide = (cfgOf P).wide) {t u : State} (hu : Inited P L g m₀ t u)
    {dataA : List Instr} {dv : BitVec 32}
    {len : Nat} (hdA : ∀ u, Ctx L g m₀ u → WP isa (.block dataA) u (Upd L g m₀ u .edx dv))
    (hd : DataOk L dv len) (hlen : len ≤ 256) :
    WP isa (.seq (.block (Cfg.hmacArgs₂ (cfgOf P).wide P.F.H.B dataA len))
      (.frame (.push [.ebp, .ecx, .edx, .eax, .esi, .edi]) (.call P.F.H.updN P.F.H.updC) (.pop .eax 6))) u
      (Updated P L g m₀ t dv len) := by
  have hA := updArgs_ok hL hu.ctx hdA (len := len) P.F.H.B
  rw [hw] at hA
  refine WP.seq (WP.mono hA fun w ⟨hcw, hmw, hdi, hsi, hax, hdx, hcx, hbp⟩ => ?_)
  have hsp : Region.Sub (Proof.Pbkdf2.Stream.X86.stk w) (below L.F 76) := by
    show Region.Sub (below (w.gpr .esp) 48) _; rw [hcw.esp]; exact hL.below48
  have a := updA (P := P) hL hcw hd hlen hdi hsi hax hdx hcx hbp
  have hS := P.ok.hH.hS
  refine WP.of_syms ?_
  refine upd_frame P.ok.hH a fun w' af hr hsy => ?_
  have hws : ∀ r ∈ [(⟨(L.a3 + BitVec.ofNat 32 0).setWidth 64, P.F.H.S⟩ : Region),
      ⟨(L.a3 + BitVec.ofNat 32 384).setWidth 64, P.ok.hH.Wb⟩], Region.Sub r ⟨L.scr, 2256⟩ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> exact scr_work' hL (by omega) (by nums)
  have h76 : Region.Sub (below L.F 76) ⟨L.B, 76⟩ := by rw [hL.below_F]; exact sub_refl _
  have hf' : Frame [⟨L.scr, 2256⟩, ⟨L.B, 76⟩] w.mem w'.mem := af.frame.sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨⟨L.scr, 2256⟩, by simp, hws r hr⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨L.B, 76⟩, by simp, sub_trans hsp h76⟩
  have hdata : Spec.Sha256.bytesAt w.mem (dv.setWidth 64) len = Spec.Sha256.bytesAt t.mem (dv.setWidth 64) len := by
    rw [hmw]
    refine bytesAt_frame hu.frame (fun r hr => ?_) (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have := hd.work hL (e := 0) (k := 2256) (by omega)
      rwa [hL.scrv (by omega), BitVec.add_zero] at this
    · rw [← hL.below_F]; exact (hd.low hL).symm
  refine ⟨hcw.keep (hsy := hsy) hL af.rd af.wr af.esp af.frame fun r hr => ?_, hu.frame.trans (hmw ▸ hf'), ?_, ?_⟩
  · rcases List.mem_append.mp hr with hr | hr
    · exact .inr (.inl (sub_trans (hws r hr) (Region.sub_prefix (by omega))))
    · simp only [List.mem_singleton] at hr; subst hr
      exact .inr (.inr (.inl (sub_trans hsp (sub_trans h76 (Region.sub_prefix (by omega))))))
  · rw [← hdata, ← hL.scrv (by omega)]
    refine hr _ (by rw [hL.scrv (by omega)]; exact hmw ▸ hu.inner) ?_
    rw [xorPad_length, blockKey_length (keyOf_length _), Proof.Pbkdf2.Stream.X86.zero_append_ofNat (by nums)]
  · refine P.reprOK w.mem w'.mem _ _ _ (fun i hi => ?_) (hmw ▸ hu.outer)
    refine Frame.bytes (R := ⟨L.scr + BitVec.ofNat 64 192, P.ok.hH.SH.stateBytes⟩) af.frame (fun r hr => ?_)
      (by show P.ok.hH.SH.stateBytes ≤ 2 ^ 64; rw [hS]; nums) hi
    rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [hS]
      rcases hr with rfl | rfl <;> (rw [hL.scrv (by omega)]; exact Offset.disjoint _ (by nums) (by nums) (by nums))
    · simp only [List.mem_singleton] at hr; subst hr
      rw [← hL.scrv (by omega)]
      exact ((hL.low_scr' (by omega) (by rw [hS]; nums)).sub_left hsp).symm

/-! ## HMAC's `finalize` -/

theorem finArgs_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (B len dst : Nat) :
    WP isa (.block (Cfg.hmacArgs₃ L.wide B len dst)) u
      fun u' => Ctx L g m₀ u' ∧ u'.mem = u.mem ∧ u'.gpr .edx = L.a3 + BitVec.ofNat 32 0 ∧
        u'.gpr .esi = L.a3 + BitVec.ofNat 32 192 ∧ u'.gpr .eax = BitVec.ofNat 32 (B + len) ∧
        u'.gpr .ecx = 0 ∧ u'.gpr .edi = L.F + BitVec.ofNat 32 dst ∧ u'.gpr .ebp = L.a3 + BitVec.ofNat 32 384 := by
  rw [Cfg.hmacArgs₃, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (scr_ok hL hc (d := .edx) (by decide) 0) fun u₁ h₁ => ?_
  refine WP.mono (scr_ok hL h₁.ctx (d := .esi) (by decide) 192) fun u₂ h₂ => ?_
  refine WP.mono (movi2_ok hL h₂.ctx (d := .eax) (e := .ecx) (by decide) (by decide) (by decide) _ _)
    fun u₃ ⟨c₃, m₃, ax₃, cx₃, k₃⟩ => ?_
  refine WP.mono (fr_ok hL c₃ (d := .edi) (by decide) dst) fun u₄ h₄ => ?_
  refine WP.mono (scr_ok hL h₄.ctx (d := .ebp) (by decide) 384) fun u₅ h₅ => ?_
  refine ⟨h₅.ctx, by rw [h₅.mem, h₄.mem, m₃, h₂.mem, h₁.mem], ?_, ?_, ?_, ?_, ?_, h₅.val⟩
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), k₃ _ (by decide) (by decide), h₂.keep _ (by decide), h₁.val]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), k₃ _ (by decide) (by decide), h₂.val]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), ax₃]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), cx₃]
  · rw [h₅.keep _ (by decide), h₄.val]

/-- After HMAC's `finalize`: the MAC in the frame at `dst`. -/
structure Done (P : RfcHash) {dn : Nat} (L : Lay dn) (g : Reg → BitVec 32) (m₀ : Mem) (t : State)
    (dv : BitVec 32) (len dst : Nat) (u : State) : Prop where
  ctx : Ctx L g m₀ u
  frame : Frame [⟨L.scr, 2256⟩, ⟨L.B, 76⟩, ⟨L.B + BitVec.ofNat 64 (76 + dst), P.F.H.D⟩] t.mem u.mem
  mac : Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (76 + dst)) P.F.H.D =
    P.mac (keyOf P L t.mem) (Spec.Sha256.bytesAt t.mem (dv.setWidth 64) len)

/-- The arguments of HMAC's `finalize`. -/
theorem finA (hL : L.Ok) {w : State} (hcw : Ctx L g m₀ w) {len dst : Nat} (hdst : dst + P.F.H.D ≤ 180)
    (hdx : w.gpr .edx = L.a3 + BitVec.ofNat 32 0) (hsi : w.gpr .esi = L.a3 + BitVec.ofNat 32 192)
    (hax : w.gpr .eax = BitVec.ofNat 32 (P.F.H.B + len)) (hcx : w.gpr .ecx = 0)
    (hdi : w.gpr .edi = L.F + BitVec.ofNat 32 dst) (hbp : w.gpr .ebp = L.a3 + BitVec.ofNat 32 384) :
    HfArgs P.ok.hH.SH P.ok.Wf w (L.a3 + BitVec.ofNat 32 0) (L.a3 + BitVec.ofNat 32 192)
      (BitVec.ofNat 32 (P.F.H.B + len)) 0 (L.F + BitVec.ofNat 32 dst) (L.a3 + BitVec.ofNat 32 384) := by
  have hS := P.ok.hH.hS
  have hD := P.ok.hH.hD
  have nc := hL.nc
  have hsp : Proof.Pbkdf2.Whole.X86.stk w = below L.F 76 := by
    show below (w.gpr .esp) 76 = _; rw [hcw.esp]
  exact
    { edx := hdx, esi := hsi, eax := hax, ecx := hcx, edi := hdi, ebp := hbp
      sp := by rw [hcw.esp, hL.FN]; have := hL.e272; omega
      cr := hcw.covers fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨L.SCR, by simp, within_scr hL (by omega) (by rw [hS]; nums)⟩
      cw := hcw.coversW fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨L.SCR, by simp, within_scr hL (by omega) (by rw [hS]; nums)⟩
        · exact ⟨L.FR, by simp, within_frv hL (by rw [hD]; nums)⟩
        · exact ⟨L.SCR, by simp, within_scr hL (by omega) (by nums)⟩
      i_u := hL.scr_disj (by rw [hS]; nums) (by omega) (by omega) (by rw [hS]; nums) (by rw [hS]; nums)
      i_o := (hL.fr_scr (by rw [hD]; nums) (by omega) (by rw [hS]; nums)).symm
      i_s := hL.scr_disj (by rw [hS]; nums) (by omega) (by omega) (by rw [hS]; nums) (by nums)
      u_o := (hL.fr_scr (by rw [hD]; nums) (by omega) (by rw [hS]; nums)).symm
      u_s := hL.scr_disj (by rw [hS]; nums) (by omega) (by omega) (by rw [hS]; nums) (by nums)
      o_s := hL.fr_scr (by rw [hD]; nums) (by omega) (by nums)
      b_i := by rw [hsp]; exact hL.low_scr' (by omega) (by rw [hS]; nums)
      b_u := by rw [hsp]; exact hL.low_scr' (by omega) (by rw [hS]; nums)
      b_o := by rw [hsp]; exact hL.low_fr (by rw [hD]; nums)
      b_s := by rw [hsp]; exact hL.low_scr' (by omega) (by nums)
      ni := by rw [hL.scrN (by omega), hS]; nums
      nu := by rw [hL.scrN (by omega), hS]; nums
      no := by rw [hL.frN (by omega), hD]; have := hL.e20; have := hL.e272; nums
      nsc := by rw [hL.scrN (by omega)]; nums }

theorem fin_step (hL : L.Ok) (hw : L.wide = (cfgOf P).wide) {t u : State} {dv : BitVec 32} {len dst : Nat}
    (hu : Updated P L g m₀ t dv len u) (hlen : len ≤ 256) (hdst : dst + P.F.H.D ≤ 180) :
    WP isa (.seq (.block (Cfg.hmacArgs₃ (cfgOf P).wide P.F.H.B len dst))
      (.frame (.push [.ebp, .edi, .ecx, .eax, .esi, .edx]) (.call P.F.hfN P.F.hfC) (.pop .eax 6))) u
      (Done P L g m₀ t dv len dst) := by
  have hA := finArgs_ok hL hu.ctx P.F.H.B len dst
  rw [hw] at hA
  refine WP.seq (WP.mono hA fun w ⟨hcw, hmw, hdx, hsi, hax, hcx, hdi, hbp⟩ => ?_)
  have a := finA (P := P) hL hcw (len := len) hdst hdx hsi hax hcx hdi hbp
  have hS := P.ok.hH.hS
  have hD := P.ok.hH.hD
  have hB := P.ok.hH.hB
  refine WP.of_syms ?_
  refine hf_frame P.reprOK (by rw [hS]; nums) P.ok.hf P.ok.hfSp P.ok.hfSU a fun w' af hpost hsy => ?_
  have hO : (L.F + BitVec.ofNat 32 dst).setWidth 64 = L.B + BitVec.ofNat 64 (76 + dst) := hL.frv (by nums)
  have hws : ∀ r ∈ [(⟨(L.a3 + BitVec.ofNat 32 0).setWidth 64, P.ok.hH.SH.stateBytes⟩ : Region),
      ⟨(L.F + BitVec.ofNat 32 dst).setWidth 64, P.ok.hH.SH.digestBytes⟩,
      ⟨(L.a3 + BitVec.ofNat 32 384).setWidth 64, P.ok.Wf * 8⟩] ++ [below (w.gpr .esp) 76],
      ∃ r' ∈ [(⟨L.scr, 2256⟩ : Region), ⟨L.B, 76⟩, ⟨L.B + BitVec.ofNat 64 (76 + dst), P.F.H.D⟩],
        Region.Sub r r' := by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, hcw.esp, hL.below_F]
    rintro r (rfl | rfl | rfl | rfl)
    · exact ⟨⟨L.scr, 2256⟩, by simp, scr_work' hL (by omega) (by rw [hS]; nums)⟩
    · exact ⟨⟨L.B + BitVec.ofNat 64 (76 + dst), P.F.H.D⟩, by simp, by rw [hO, hD]; exact sub_refl _⟩
    · exact ⟨⟨L.scr, 2256⟩, by simp, scr_work' hL (by omega) (by nums)⟩
    · exact ⟨⟨L.B, 76⟩, by simp, sub_refl _⟩
  have hl : (Spec.Sha256.bytesAt t.mem (dv.setWidth 64) len).length = len := by simp [Spec.Sha256.bytesAt]
  refine ⟨hcw.keep (hsy := hsy) hL af.rd af.wr af.esp af.frame fun r hr => ?_,
    hu.frame.sub (fun r hr => ⟨r, by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h],
      sub_refl _⟩) |>.trans (hmw ▸ af.frame.sub hws), ?_⟩
  · obtain ⟨r', hr', hs⟩ := hws r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · exact .inr (.inl (sub_trans hs (Region.sub_prefix (by omega))))
    · exact .inr (.inr (.inl (sub_trans hs (Region.sub_prefix (by omega)))))
    · exact .inr (.inr (.inl (sub_trans hs (Offset.sub_base _ (by nums)))))
  · have hk := blockKey_length (P := P) (keyOf_length (L := L) t.mem)
    have := hpost (Spec.Hmac.blockKey P.ok.hH.SH.H (keyOf P L t.mem)) (Spec.Sha256.bytesAt t.mem (dv.setWidth 64) len)
      (by rw [hk, hB]) (by rw [hk, hl]; nums)
      (by rw [hL.scrv (by omega)]; exact hmw ▸ hu.inner)
      (by rw [hB, hl]; exact Proof.Pbkdf2.Stream.X86.zero_append_ofNat (by nums))
      (by rw [hL.scrv (by omega)]; exact hmw ▸ hu.outer)
    rw [hO, hD] at this
    exact this

/-! ## The whole HMAC -/

theorem seq_seq {a b c : Prog isa} {s : State} {P Q : State → Prop} (h : WP isa (.seq a b) s P)
    (hc : ∀ s', P s' → WP isa c s' Q) : WP isa (.seq a (.seq b c)) s Q := by
  rw [WP.seq_iff] at h ⊢
  refine WP.mono h fun s₁ h₁ => ?_
  rw [WP.seq_iff]
  exact WP.mono h₁ hc

/-- `HMAC_K(data)`, for the key `K` in the frame, to the frame at `dst`. -/
theorem hmac_ok (hL : L.Ok) (hw : L.wide = (cfgOf P).wide) {t : State} (hc : Ctx L g m₀ t) {dataA : List Instr} {dv : BitVec 32} {len dst : Nat}
    (hdA : ∀ u, Ctx L g m₀ u → WP isa (.block dataA) u (Upd L g m₀ u .edx dv)) (hd : DataOk L dv len)
    (hlen : len ≤ 256) (hdst : dst + P.F.H.D ≤ 180) :
    WP isa ((cfgOf P).hmac dataA len dst) t (Done P L g m₀ t dv len dst) :=
  seq_seq (init_step hL hw hc) fun _ hu => seq_seq (upd_step hL hw hu hdA hd hlen) fun _ hu' =>
    fin_step hL hw hu' hlen hdst

end VG.Proof.Ecdsa.Rfc6979.X86
