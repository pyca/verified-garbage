module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Hash
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Regs
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.ICall
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Pbkdf2.MdKeys
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Copy
public import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# Deterministic ECDSA on x86 (32-bit): one HMAC, through the table

`HMAC_K(data)` (`Cfg.hmac`), as on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Hmac.lean`),
for the key `K` (of the hash function's output length) in the frame and
`len` bytes of data in the frame or in `scratch` above HMAC's working space
(`DataOk`), written to the frame at `dst`, from the table's streaming
functions, each called indirectly in a frame of its arguments (`tcall_ok`:
the table's word, which `Ctx` says holds the function of `L.G`, whose call
an indirect call of `L.f`'s functions reaches): the states for the key
(`init_step`: each set by `init`, `initCall_ok`, and updated with the padded
key, `padBlk_ok` and `updCall_ok`), the inner state updated with the data
(`upd_step`), and the MAC (`fin_step`: the inner state finalized,
`finCall_ok`, the outer one updated with its digest and finalized, and the
digest copied). They change only HMAC's states and working space, the padded
key and what `finalize` writes (all within the first 2256 bytes of
`scratch`), the 76 bytes below the frame, and `dst` (`hmac_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.Impl.Ecdsa.Rfc6979.X86
open VG.Proof.Pbkdf2.Stream.X86 (InitArgs UpdArgs FinArgs init_frame upd_frame fin_frame)
open VG.WriteBytes (writeBytes writeBytes_append writeBytes_nil writeBytes_frame)

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

/-! ## Pointers into `scratch` and the frame -/

namespace Lay.Ok

theorem scrv (hL : L.Ok) {o : Nat} (ho : o < 8192) :
    (L.a4 + BitVec.ofNat 32 o).setWidth 64 = L.scr + BitVec.ofNat 64 o :=
  addr_eq (by have := hL.nc; omega_arith)

theorem scrN (hL : L.Ok) {o : Nat} (ho : o < 8192) : (L.a4 + BitVec.ofNat 32 o).toNat = L.a4.toNat + o := by
  have := hL.nc
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]

theorem frv (hL : L.Ok) {o : Nat} (ho : o < 224 + 4 * L.e) :
    (L.F + BitVec.ofNat 32 o).setWidth 64 = L.B + BitVec.ofNat 64 (76 + o) := hL.addrF ho

theorem FN (hL : L.Ok) : L.F.toNat = L.E.toNat - (196 + 4 * L.e) := sub_toNat (by have := hL.e272; omega_arith)

theorem frN (hL : L.Ok) {o : Nat} (ho : o < 224 + 4 * L.e) : (L.F + BitVec.ofNat 32 o).toNat = L.E.toNat - (196 + 4 * L.e) + o := by
  have := hL.e272; have := hL.e28
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega_arith), hL.FN,
    Nat.mod_eq_of_lt (by omega_arith)]

/-- Two ranges of `scratch`. -/
theorem scr_disj (hL : L.Ok) {a n b k : Nat} (h : a + n ≤ b ∨ b + k ≤ a) (ha : a < 8192) (hb : b < 8192)
    (han : a + n ≤ 8192) (hbk : b + k ≤ 8192) :
    Region.Disjoint ⟨(L.a4 + BitVec.ofNat 32 a).setWidth 64, n⟩ ⟨(L.a4 + BitVec.ofNat 32 b).setWidth 64, k⟩ := by
  have := hL.nc
  rw [hL.scrv ha, hL.scrv hb]
  exact Offset.disjoint _ h (by omega_arith) (by omega_arith)

/-- A range of the frame, and one of `scratch`. -/
theorem fr_scr (hL : L.Ok) {o n b k : Nat} (ho : o + n ≤ 196 + 4 * L.e) (hb : b < 8192) (hbk : b + k ≤ 8192) :
    Region.Disjoint ⟨(L.F + BitVec.ofNat 32 o).setWidth 64, n⟩ ⟨(L.a4 + BitVec.ofNat 32 b).setWidth 64, k⟩ := by
  rw [hL.frv (by omega_arith), hL.scrv hb]
  exact hL.stk_scr (by omega_arith) hbk

/-- The 76 bytes below the frame, and a range of `scratch`. -/
theorem low_scr' (hL : L.Ok) {b k : Nat} (hb : b < 8192) (hbk : b + k ≤ 8192) :
    Region.Disjoint (below L.F 76) ⟨(L.a4 + BitVec.ofNat 32 b).setWidth 64, k⟩ := by
  rw [hL.below_F, hL.scrv hb]; exact hL.low_scr hbk

/-- The 76 bytes below the frame, and a range of the frame. -/
theorem low_fr (hL : L.Ok) {o n : Nat} (ho : o + n ≤ 196 + 4 * L.e) :
    Region.Disjoint (below L.F 76) ⟨(L.F + BitVec.ofNat 32 o).setWidth 64, n⟩ := by
  have := hL.nB
  rw [hL.below_F, hL.frv (by omega_arith)]; exact Offset.base_disjoint _ (by omega_arith) (by omega_arith)

/-- The 48 bytes below the frame (the streaming functions' calls) are among the 76. -/
theorem below48 (hL : L.Ok) : Region.Sub (below L.F 48) (below L.F 76) :=
  below_sub (by omega_arith) (by rw [hL.FN]; have := hL.e272; omega_arith)

end Lay.Ok

theorem within_scr (hL : L.Ok) {a n : Nat} (ha : a < 8192) (h : a + n ≤ 8192) :
    Within ⟨(L.a4 + BitVec.ofNat 32 a).setWidth 64, n⟩ L.SCR := by
  rw [hL.scrv ha]; exact within_off _ h

theorem within_frv (hL : L.Ok) {o n : Nat} (h : o + n ≤ 196 + 4 * L.e) :
    Within ⟨(L.F + BitVec.ofNat 32 o).setWidth 64, n⟩ L.FR := by
  rw [hL.frv (by omega_arith)]; exact within_fr _ (by omega_arith) (by omega_arith)

/-- Where the data may be: in the frame below the saved registers, or in
`scratch` above HMAC's working space. -/
def DataOk {dn : Nat} (L : Lay dn) (dv : BitVec 32) (len : Nat) : Prop :=
  (∃ o, dv = L.F + BitVec.ofNat 32 o ∧ o + len ≤ 180) ∨
    (∃ o, dv = L.a4 + BitVec.ofNat 32 o ∧ 2256 ≤ o ∧ o + len ≤ 4096)

namespace DataOk

variable {dv : BitVec 32} {len : Nat}

theorem low (hd : DataOk L dv len) (hL : L.Ok) : Region.Disjoint (below L.F 76) ⟨dv.setWidth 64, len⟩ := by
  rcases hd with ⟨o, rfl, h⟩ | ⟨o, rfl, h₁, h₂⟩
  · exact hL.low_fr (by omega_arith)
  · exact hL.low_scr' (by omega_arith) (by omega_arith)

/-- The data is apart from HMAC's states and working space. -/
theorem work (hd : DataOk L dv len) (hL : L.Ok) {e k : Nat} (h : e + k ≤ 2256) :
    Region.Disjoint ⟨dv.setWidth 64, len⟩ ⟨(L.a4 + BitVec.ofNat 32 e).setWidth 64, k⟩ := by
  rcases hd with ⟨o, rfl, h'⟩ | ⟨o, rfl, h₁, h₂⟩
  · exact hL.fr_scr (by omega_arith) (by omega_arith) (by omega_arith)
  · exact hL.scr_disj (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)

theorem within (hd : DataOk L dv len) (hL : L.Ok) :
    ∃ R ∈ [L.D, L.DG, L.ARGS, L.FR, L.OUT, L.SCR], Within ⟨dv.setWidth 64, len⟩ R := by
  rcases hd with ⟨o, rfl, h⟩ | ⟨o, rfl, h₁, h₂⟩
  · exact ⟨L.FR, by simp, within_frv hL (by omega_arith)⟩
  · exact ⟨L.SCR, by simp, within_scr hL (by omega_arith) (by omega_arith)⟩

theorem fits (hd : DataOk L dv len) (hL : L.Ok) : dv.toNat + len ≤ 2 ^ 32 := by
  rcases hd with ⟨o, rfl, h⟩ | ⟨o, rfl, h₁, h₂⟩
  · rw [hL.frN (by omega_arith)]; have := hL.e28; have := hL.e272; omega_arith
  · rw [hL.scrN (by omega_arith)]; have := hL.nc; omega_arith

end DataOk

/-! ## The table -/

/-- The layout's table is of `P`'s hash function and functions, and its
frame is the size of `P`'s code. -/
def TabL (P : RfcHash) {dn : Nat} (L : Lay dn) : Prop :=
  L.G = P.H ∧ L.f = P.f ∧ L.e = P.e ∧ L.wide = P.wide ∧ L.hHigh = P.R.hHigh

theorem TabL.cw (hT : TabL P L) : (cfgOf P).wide = L.wide := hT.2.2.2.1.symm
theorem TabL.ch (hT : TabL P L) : (cfgOf P).hHigh = L.hHigh := hT.2.2.2.2.symm

/-- The table's words, as on entry. -/
theorem Ctx.tabWord (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {o : Nat} (ho : o + 4 ≤ 20) :
    t.mem.readW (L.tab + BitVec.ofNat 64 o) 32 = m₀.readW (L.tab + BitVec.ofNat 64 o) 32 :=
  hc.frame.readW (r := L.TAB) (Offset.contains_base _ ho (by have := hL.nt; omega_arith)) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.to
    · exact hL.tc
    · exact hL.tk) (by decide)

theorem Lay.Ok.tabA (hL : L.Ok) {o : Nat} (ho : o + 4 ≤ 20) : addr L.a5 o = L.tab + BitVec.ofNat 64 o :=
  addr_eq (by have := hL.nt; omega_arith)

/-- The table's address into `esi`. -/
theorem tblk1_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block [.mov .esi ((cfgOf P).arg 5)]) t (Upd L g m₀ t .esi L.a5) :=
  argC_ok hL hT.cw hT.ch hc (d := .esi) (by decide) (i := 5) (by omega)

/-- The table's word `j` into `esi`, from its address there. -/
theorem tblk2_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (hsi : t.gpr .esi = L.a5) {j : Nat}
    (hj : 4 * j + 4 ≤ 20) :
    WP isa (.block [.mov .esi (.mem (Impl.Pbkdf2.Stream.X86.at_ .esi (4 * j)))]) t
      (Upd L g m₀ t .esi (m₀.readW (L.tab + BitVec.ofNat 64 (4 * j)) 32)) := by
  have hin : InRegions (t.rd ++ t.wr) (addr L.a5 (4 * j)) 4 := by rw [hL.tabA hj]; exact hc.inTab hL hj
  refine Wp.wp_ldm hsi hin fun t' u => WP.block_nil ?_
  have e := hc.tabWord hL hj
  rw [← hL.tabA hj] at e
  rw [e, hL.tabA hj] at u
  exact Upd.of_wp hL hc (by decide) u

/-- The indirect call of the table's function `j`, at the address its word
`j` holds, of `n`, in a frame pushing `rs`. -/
theorem tcall_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) {j : Nat} (hj : 4 * j + 4 ≤ 20)
    {n : String} {c : Prog isa} {ts : List (String × Prog isa)} {rs : List Reg}
    (hw : m₀.readW (L.tab + BitVec.ofNat 64 (4 * j)) 32 = t.syms n)
    (hf : ts.find? (fun q => (t.syms q.1).setWidth 64 == (t.syms n).setWidth 64) = some (n, c)) {Q : State → Prop}
    (h : ∀ t', Ctx L g m₀ t' → t'.mem = t.mem → (∀ r, r ≠ .esi → t'.gpr r = t.gpr r) → t'.syms = t.syms →
      WP isa (.frame (.push rs) (.call n c) (.pop .eax rs.length)) t' Q) :
    WP isa ((cfgOf P).tcall j ts rs) t Q := by
  unfold Cfg.tcall
  refine WP.seq (WP.mono_syms (tblk1_ok hL hT hc) fun t₁ h₁ hs₁ =>
    WP.seq (WP.mono_syms (tblk2_ok hL h₁.ctx h₁.val hj) fun t' h' hs' => ?_))
  refine WP.frame_icalls_of_call (fun u hp => ⟨_, rfl, ?_⟩)
    (h t' h'.ctx (h'.mem.trans h₁.mem) (fun r hr => (h'.keep r hr).trans (h₁.keep r hr)) (hs'.trans hs₁))
  obtain ⟨-, -, -, rfl⟩ := push_some hp
  show ts.find? (fun q => ((pushed rs t').syms q.1).setWidth 64 == ((pushed rs t').gpr .esi).setWidth 64) = _
  rw [pushed_gpr _ _ (by decide), show (pushed rs t').syms = t'.syms from pushRegs_syms t' rs, h'.val, hw,
    hs'.trans hs₁]
  exact hf

/-! ## The streaming calls -/

/-- The writes of a call, within HMAC's working space and the stack below the frame. -/
theorem safe_call (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {ws : List Region} (hs : ∀ r ∈ ws, Safe L r) {n : Nat}
    (hn : n ≤ 76) : ∀ r ∈ ws ++ [below (u.gpr .esp) n], Safe L r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact hs r hr
  · simp only [List.mem_singleton] at hr; subst hr
    refine .inr (.inr (.inl (sub_trans (below_sub hn (by rw [hc.esp, hL.FN]; have := hL.e272; omega_arith)) ?_)))
    rw [hc.esp, hL.below_F]; exact Region.sub_prefix (by omega_arith)

theorem scr_work {e k : Nat} (h : e + k ≤ 2256) : Region.Sub ⟨L.scr + BitVec.ofNat 64 e, k⟩ ⟨L.scr, 2256⟩ :=
  Offset.sub_base _ h

theorem scr_work' (hL : L.Ok) {e k : Nat} (he : e < 8192) (h : e + k ≤ 2256) :
    Region.Sub ⟨(L.a4 + BitVec.ofNat 32 e).setWidth 64, k⟩ ⟨L.scr, 2256⟩ := by
  rw [hL.scrv he]; exact scr_work h

theorem stk_sub (hL : L.Ok) {w : State} (hc : Ctx L g m₀ w) :
    Region.Sub (Proof.Pbkdf2.Stream.X86.stk w) ⟨L.B, 76⟩ := by
  show Region.Sub (below (w.gpr .esp) 48) _
  rw [hc.esp, ← hL.below_F]; exact hL.below48

theorem sp48 (hL : L.Ok) {w : State} (hc : Ctx L g m₀ w) : 48 ≤ (w.gpr .esp).toNat := by
  rw [hc.esp, hL.FN]; have := hL.e272; omega_arith

/-- What a call changes, within what HMAC changes. -/
abbrev HM {dn : Nat} (L : Lay dn) : List Region := [⟨L.scr, 2256⟩, ⟨L.B, 76⟩]

theorem sub_hm {e k : Nat} (h : e + k ≤ 2256) :
    ∃ r' ∈ HM L, Region.Sub ⟨L.scr + BitVec.ofNat 64 e, k⟩ r' :=
  ⟨_, List.mem_cons_self .., scr_work h⟩

theorem low_hm : ∃ r' ∈ HM L, Region.Sub ⟨L.B, 76⟩ r' := ⟨⟨L.B, 76⟩, by simp, sub_refl _⟩

/-- `init`'s argument: the state at `scratch + o`, in `ebx`. -/
theorem initArgsOf (hL : L.Ok) {w : State} (hc : Ctx L g m₀ w) {o : Nat} (ho : o + 256 ≤ 512)
    (hbx : w.gpr .ebx = L.a4 + BitVec.ofNat 32 o) : InitArgs (H := P.H) w .ebx (L.a4 + BitVec.ofNat 32 o) := by
  have hS := P.ok.hSB
  have nc := hL.nc
  exact ⟨hbx, by decide, sp48 hL hc, hc.coversW fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨L.SCR, by simp, within_scr hL (by omega_arith) (by omega_arith)⟩,
      ((hL.low_scr' (by omega_arith) (by omega_arith)).sub_left (by rw [← hc.esp]; exact
        (show Region.Sub (Proof.Pbkdf2.Stream.X86.stk w) (below (w.gpr .esp) 76) from
          below_sub (by omega_arith) (by rw [hc.esp, hL.FN]; have := hL.e272; omega_arith)))),
      by rw [hL.scrN (by omega_arith)]; omega_arith⟩

/-- `init` of the state at `scratch + o`, in `ebx`, in its frame. -/
theorem initRaw_ok (hL : L.Ok) {w : State} (hc : Ctx L g m₀ w) {o : Nat} (ho : o + 256 ≤ 512)
    (hbx : w.gpr .ebx = L.a4 + BitVec.ofNat 32 o) :
    WP isa (P.H.callInit .ebx) w fun u => Ctx L g m₀ u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 o, P.H.S⟩, ⟨L.B, 76⟩] w.mem u.mem ∧
      P.ok.SH.Repr u.mem (L.scr + BitVec.ofNat 64 o) [] := by
  have hS := P.ok.hSB
  have nc := hL.nc
  have a := initArgsOf (P := P) hL hc ho hbx
  refine WP.of_syms (init_frame P.ok a fun u af hr hsy => ?_)
  rw [hL.scrv (by omega_arith)] at af hr
  refine ⟨hc.keep (hsy := hsy) hL af.rd af.wr af.esp af.frame fun r hr => ?_, af.frame.sub fun r hr => ?_, hr⟩
  · rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_singleton] at hr; subst hr
      exact safe_scr L (by omega_arith)
    · simp only [List.mem_singleton] at hr; subst hr
      exact .inr (.inr (.inl (sub_trans (stk_sub hL hc) (Region.sub_prefix (by omega_arith)))))
  · rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., sub_refl _⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨L.B, 76⟩, by simp, stk_sub hL hc⟩

/-- `init` of the state at `scratch + o`: it represents the empty message. -/
theorem initCall_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) {o : Nat} (ho : o + 256 ≤ 512) :
    WP isa ((cfgOf P).initCall o) t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 o, P.H.S⟩, ⟨L.B, 76⟩] t.mem u.mem ∧
      P.ok.SH.Repr u.mem (L.scr + BitVec.ofNat 64 o) [] := by
  refine WP.seq (WP.mono (scr_ok hL hT.cw hT.ch hc (d := .ebx) (by decide) o) fun u h => ?_)
  have hok := h.ctx.tabOk
  have htm := h.ctx.tabMem
  rw [hT.1, hT.2.1] at hok
  rw [hT.1] at htm
  refine tcall_ok hL hT h.ctx (j := 0) (by decide) (n := P.H.initN) (c := P.H.initC) htm.1 hok.1
    fun u' hc' hm' hk' _ => ?_
  refine WP.mono (initRaw_ok hL hc' ho ((hk' _ (by decide)).trans h.val)) fun v ⟨hcv, hf, hr⟩ => ?_
  rw [hm', h.mem] at hf
  exact ⟨hcv, hf, hr⟩

/-- `d ← v; e ← w`. -/
theorem movi2_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {d e : Reg} (hd : d ≠ .esp) (he : e ≠ .esp)
    (hde : e ≠ d) (v w : BitVec 32) :
    WP isa (.block [.mov d (.imm v), .mov e (.imm w)]) u fun u' => Ctx L g m₀ u' ∧ u'.mem = u.mem ∧
      u'.gpr d = v ∧ u'.gpr e = w ∧ ∀ r, r ≠ d → r ≠ e → u'.gpr r = u.gpr r :=
  Wp.wp_movi fun u₁ v₁ => Wp.wp_movi fun u₂ v₂ => WP.block_nil
    ⟨(Upd.of_wp hL (Upd.of_wp hL hc hd v₁).ctx he v₂).ctx, by rw [v₂.mem, v₁.mem],
      by rw [v₂.other _ (Ne.symm hde), v₁.gpr], v₂.gpr, fun r h₁ h₂ => by rw [v₂.other _ h₂, v₁.other _ h₁]⟩

/-- The arguments of `update`: the state at `scratch + o` holding `cnt`
bytes, the data, its length and the working space. -/
theorem updArgs_ok (hL : L.Ok) (hT : TabL P L) {u : State} (hc : Ctx L g m₀ u) {o cnt : Nat}
    {dataA : List Instr} {dv : BitVec 32} {len : Nat}
    (hdA : ∀ u, Ctx L g m₀ u → WP isa (.block dataA) u (Upd L g m₀ u .edx dv)) :
    WP isa (.block ((cfgOf P).updArgs o cnt dataA len)) u fun u' => Ctx L g m₀ u' ∧
      u'.mem = u.mem ∧ u'.gpr .ebx = L.a4 + BitVec.ofNat 32 o ∧ u'.gpr .edi = BitVec.ofNat 32 cnt ∧
      u'.gpr .eax = 0 ∧ u'.gpr .edx = dv ∧ u'.gpr .ecx = BitVec.ofNat 32 len ∧
      u'.gpr .ebp = L.a4 + BitVec.ofNat 32 512 := by
  rw [Cfg.updArgs, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (scr_ok hL hT.cw hT.ch hc (d := .ebx) (by decide) o) fun u₁ h₁ => ?_
  refine WP.mono (movi2_ok hL h₁.ctx (d := .edi) (e := .eax) (by decide) (by decide) (by decide) _ _)
    fun u₂ ⟨c₂, m₂, di₂, ax₂, k₂⟩ => ?_
  refine WP.mono (hdA u₂ c₂) fun u₃ h₃ => ?_
  refine WP.mono (movi_ok hL h₃.ctx (d := .ecx) (by decide) _) fun u₄ h₄ => ?_
  refine WP.mono (scr_ok hL hT.cw hT.ch h₄.ctx (d := .ebp) (by decide) 512) fun u₅ h₅ => ?_
  refine ⟨h₅.ctx, by rw [h₅.mem, h₄.mem, h₃.mem, m₂, h₁.mem], ?_, ?_, ?_, ?_, ?_, h₅.val⟩
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), k₂ _ (by decide) (by decide), h₁.val]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), di₂]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), ax₂]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.val]
  · rw [h₅.keep _ (by decide), h₄.val]

/-- Where data `update` reads may be: within a buffer or the frame, and
apart from the state it updates, the working space and the stack below the
frame. -/
structure UpdData (P : RfcHash) {dn : Nat} (L : Lay dn) (o : Nat) (dv : BitVec 32) (len : Nat) : Prop where
  cov : ∃ R ∈ [L.D, L.DG, L.ARGS, L.FR, L.OUT, L.SCR], Within ⟨dv.setWidth 64, len⟩ R
  st : Region.Disjoint ⟨dv.setWidth 64, len⟩ ⟨L.scr + BitVec.ofNat 64 o, P.H.S⟩
  wk : Region.Disjoint ⟨dv.setWidth 64, len⟩ ⟨L.scr + BitVec.ofNat 64 512, P.ok.Wb⟩
  low : Region.Disjoint ⟨L.B, 76⟩ ⟨dv.setWidth 64, len⟩
  fit : dv.toNat + len ≤ 2 ^ 32

/-- `update`'s arguments: the state at `scratch + o` holding `cnt` bytes, the
`len` bytes at `dv`, and the working space. -/
theorem updArgsOf (hL : L.Ok) {w : State} (hc : Ctx L g m₀ w) {o : Nat} (ho : o + 256 ≤ 512) {dv : BitVec 32}
    {len : Nat} (hd : UpdData P L o dv len) (hlen : len < 2 ^ 32) {cnt : Nat}
    (hbx : w.gpr .ebx = L.a4 + BitVec.ofNat 32 o) (hdi : w.gpr .edi = BitVec.ofNat 32 cnt) (hax : w.gpr .eax = 0)
    (hdx : w.gpr .edx = dv) (hcx : w.gpr .ecx = BitVec.ofNat 32 len) (hbp : w.gpr .ebp = L.a4 + BitVec.ofNat 32 512) :
    UpdArgs P.ok w .edi .ebx (L.a4 + BitVec.ofNat 32 o) dv (L.a4 + BitVec.ofNat 32 512) (BitVec.ofNat 32 cnt) len := by
  have hS := P.ok.hSB
  have hWb := P.sizes.2.1
  have nc := hL.nc
  have hsp := stk_sub hL hc
  have aS : (L.a4 + BitVec.ofNat 32 o).setWidth 64 = L.scr + BitVec.ofNat 64 o := hL.scrv (by omega_arith)
  have aW : (L.a4 + BitVec.ofNat 32 512).setWidth 64 = L.scr + BitVec.ofNat 64 512 := hL.scrv (by omega_arith)
  exact
    { hst := hbx, hlo := hdi, eax := hax, ecx := hcx, edx := hdx, ebp := hbp, hr := by decide, hl := by decide
      hlen := hlen
      sp48 := sp48 hL hc
      cd := hc.covers fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hd.cov
      cw := hc.coversW fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact ⟨L.SCR, by simp, within_scr hL (by omega_arith) (by omega_arith)⟩
      st_sc := by rw [aS, aW]; exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
      d_st := by rw [aS]; exact hd.st
      d_sc := by rw [aW]; exact hd.wk
      b_st := by rw [aS]; exact (hL.low_scr (by omega_arith)).sub_left hsp
      b_d := hd.low.sub_left hsp
      b_sc := by rw [aW]; exact (hL.low_scr (by omega_arith)).sub_left hsp
      nst := by rw [hL.scrN (by omega_arith)]; omega_arith
      nd := hd.fit
      nsc := by rw [hL.scrN (by omega_arith)]; omega_arith }

/-- `update` of the state at `scratch + o`, holding `cnt` bytes, with `len`
bytes at `dv`, in its frame. -/
theorem updRaw_ok (hL : L.Ok) {w : State} (hc : Ctx L g m₀ w) {o : Nat} (ho : o + 256 ≤ 512) {dv : BitVec 32}
    {len : Nat} (hd : UpdData P L o dv len) (hlen : len < 2 ^ 32) {cnt : Nat} (hcnt : cnt < 2 ^ 32)
    (hbx : w.gpr .ebx = L.a4 + BitVec.ofNat 32 o) (hdi : w.gpr .edi = BitVec.ofNat 32 cnt) (hax : w.gpr .eax = 0)
    (hdx : w.gpr .edx = dv) (hcx : w.gpr .ecx = BitVec.ofNat 32 len) (hbp : w.gpr .ebp = L.a4 + BitVec.ofNat 32 512) :
    WP isa (.frame (.push Impl.Ecdsa.Rfc6979.X86.upd6) (.call P.H.updN P.H.updC) (.pop .eax upd6.length)) w
      fun u => Ctx L g m₀ u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 o, P.H.S⟩, ⟨L.scr + BitVec.ofNat 64 512, P.ok.Wb⟩, ⟨L.B, 76⟩] w.mem u.mem ∧
      ∀ msg : List Byte, P.ok.SH.Repr w.mem (L.scr + BitVec.ofNat 64 o) msg → msg.length = cnt →
        P.ok.SH.Repr u.mem (L.scr + BitVec.ofNat 64 o) (msg ++ Spec.Sha256.bytesAt w.mem (dv.setWidth 64) len) := by
  have hS := P.ok.hSB
  have hWb := P.sizes.2.1
  have nc := hL.nc
  have hsp := stk_sub hL hc
  have aS : (L.a4 + BitVec.ofNat 32 o).setWidth 64 = L.scr + BitVec.ofNat 64 o := hL.scrv (by omega_arith)
  have aW : (L.a4 + BitVec.ofNat 32 512).setWidth 64 = L.scr + BitVec.ofNat 64 512 := hL.scrv (by omega_arith)
  have a := updArgsOf (P := P) hL hc ho hd hlen hbx hdi hax hdx hcx hbp
  refine WP.of_syms (upd_frame P.ok a fun u af hr hsy => ?_)
  rw [aS, aW] at af; rw [aS] at hr
  refine ⟨hc.keep (hsy := hsy) hL af.rd af.wr af.esp af.frame fun r hr => ?_, af.frame.sub fun r hr => ?_,
    fun msg hm hml => hr msg hm (by rw [hml, Proof.Pbkdf2.Stream.X86.zero_append_ofNat hcnt])⟩
  · rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact safe_scr L (by omega_arith)
    · simp only [List.mem_singleton] at hr; subst hr
      exact .inr (.inr (.inl (sub_trans hsp (Region.sub_prefix (by omega_arith)))))
  · rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., sub_refl _⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), sub_refl _⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨L.B, 76⟩, by simp, hsp⟩

/-- `update` of the state at `scratch + o`, holding `cnt` bytes, with `len`
bytes at `dv`. -/
theorem updCall_gen (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) {o cnt : Nat} (ho : o + 256 ≤ 512)
    {dataA : List Instr} {dv : BitVec 32} {len : Nat}
    (hdA : ∀ u, Ctx L g m₀ u → WP isa (.block dataA) u (Upd L g m₀ u .edx dv)) (hd : UpdData P L o dv len)
    (hcnt : cnt < 2 ^ 32) (hlen : len < 2 ^ 32) :
    WP isa ((cfgOf P).updCall o cnt dataA len) t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 o, P.H.S⟩, ⟨L.scr + BitVec.ofNat 64 512, P.ok.Wb⟩, ⟨L.B, 76⟩] t.mem u.mem ∧
      ∀ msg : List Byte, P.ok.SH.Repr t.mem (L.scr + BitVec.ofNat 64 o) msg → msg.length = cnt →
        P.ok.SH.Repr u.mem (L.scr + BitVec.ofNat 64 o) (msg ++ Spec.Sha256.bytesAt t.mem (dv.setWidth 64) len) := by
  refine WP.seq (WP.mono (updArgs_ok hL hT hc (o := o) (cnt := cnt) (len := len) hdA)
    fun w ⟨hcw, hmw, hbx, hdi, hax, hdx, hcx, hbp⟩ => ?_)
  have hok := hcw.tabOk
  have htm := hcw.tabMem
  rw [hT.1, hT.2.1] at hok
  rw [hT.1] at htm
  refine tcall_ok hL hT hcw (j := 1) (by decide) (n := P.H.updN) (c := P.H.updC) htm.2.1 hok.2.1
    fun w' hc' hm' hk' _ => ?_
  refine WP.mono (updRaw_ok hL hc' ho hd hlen hcnt ((hk' _ (by decide)).trans hbx) ((hk' _ (by decide)).trans hdi)
    ((hk' _ (by decide)).trans hax) ((hk' _ (by decide)).trans hdx) ((hk' _ (by decide)).trans hcx)
    ((hk' _ (by decide)).trans hbp)) fun u ⟨hcu, hf, hr⟩ => ?_
  rw [hm', hmw] at hf hr
  exact ⟨hcu, hf, hr⟩

/-- `update` of the state at `scratch + o`, holding `cnt` bytes, with `len`
bytes at `dv`: the state represents them too. -/
theorem updCall_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) {o cnt : Nat} (ho : o + 256 ≤ 512)
    {dataA : List Instr} {dv : BitVec 32} {len : Nat}
    (hdA : ∀ u, Ctx L g m₀ u → WP isa (.block dataA) u (Upd L g m₀ u .edx dv)) (hd : UpdData P L o dv len)
    (hcnt : cnt < 2 ^ 32) (hlen : len < 2 ^ 32)
    {msg : List Byte} (hr : P.ok.SH.Repr t.mem (L.scr + BitVec.ofNat 64 o) msg) (hml : msg.length = cnt) :
    WP isa ((cfgOf P).updCall o cnt dataA len) t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 o, P.H.S⟩, ⟨L.scr + BitVec.ofNat 64 512, P.ok.Wb⟩, ⟨L.B, 76⟩] t.mem u.mem ∧
      P.ok.SH.Repr u.mem (L.scr + BitVec.ofNat 64 o) (msg ++ Spec.Sha256.bytesAt t.mem (dv.setWidth 64) len) :=
  WP.mono (updCall_gen hL hT hc ho hdA hd hcnt hlen) fun _ ⟨a, b, c⟩ => ⟨a, b, c msg hr hml⟩

/-- The arguments of `finalize`: the state at `scratch + o` holding `cnt`
bytes, the output and the working space. -/
theorem finArgs_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) (o cnt : Nat) :
    WP isa (.block ((cfgOf P).finArgs o cnt)) t fun w => Ctx L g m₀ w ∧ w.mem = t.mem ∧
      w.gpr .ebx = L.a4 + BitVec.ofNat 32 o ∧ w.gpr .eax = BitVec.ofNat 32 cnt ∧ w.gpr .ecx = 0 ∧
      w.gpr .edx = L.a4 + BitVec.ofNat 32 1152 ∧ w.gpr .ebp = L.a4 + BitVec.ofNat 32 512 := by
  rw [Cfg.finArgs, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (scr_ok hL hT.cw hT.ch hc (d := .ebx) (by decide) o) fun u₁ h₁ => ?_
  refine WP.mono (movi2_ok hL h₁.ctx (d := .eax) (e := .ecx) (by decide) (by decide) (by decide) _ _)
    fun u₂ ⟨c₂, m₂, ax₂, cx₂, k₂⟩ => ?_
  refine WP.mono (scr_ok hL hT.cw hT.ch c₂ (d := .edx) (by decide) 1152) fun u₃ h₃ => ?_
  refine WP.mono (scr_ok hL hT.cw hT.ch h₃.ctx (d := .ebp) (by decide) 512) fun u₄ h₄ => ?_
  refine ⟨h₄.ctx, by rw [h₄.mem, h₃.mem, m₂, h₁.mem], ?_, ?_, ?_, ?_, h₄.val⟩
  · rw [h₄.keep _ (by decide), h₃.keep _ (by decide), k₂ _ (by decide) (by decide), h₁.val]
  · rw [h₄.keep _ (by decide), h₃.keep _ (by decide), ax₂]
  · rw [h₄.keep _ (by decide), h₃.keep _ (by decide), cx₂]
  · rw [h₄.keep _ (by decide), h₃.val]

/-- `finalize`'s arguments: the state at `scratch + o` holding `cnt` bytes,
the output at `scratch + sTmp`, and the working space. -/
theorem finArgsOf (hL : L.Ok) {w : State} (hc : Ctx L g m₀ w) {o : Nat} (ho : o + 256 ≤ 512) {cnt : Nat}
    (hbx : w.gpr .ebx = L.a4 + BitVec.ofNat 32 o) (hax : w.gpr .eax = BitVec.ofNat 32 cnt) (hcx : w.gpr .ecx = 0)
    (hdx : w.gpr .edx = L.a4 + BitVec.ofNat 32 1152) (hbp : w.gpr .ebp = L.a4 + BitVec.ofNat 32 512) :
    FinArgs P.ok w .ebx (L.a4 + BitVec.ofNat 32 o) (L.a4 + BitVec.ofNat 32 1152) (L.a4 + BitVec.ofNat 32 512)
      (BitVec.ofNat 32 cnt) 0 := by
  have hS := P.ok.hSB
  have hWb := P.sizes.2.1
  have hF := P.ok.hF
  have nc := hL.nc
  have hsp := stk_sub hL hc
  have aS : (L.a4 + BitVec.ofNat 32 o).setWidth 64 = L.scr + BitVec.ofNat 64 o := hL.scrv (by omega_arith)
  have aO : (L.a4 + BitVec.ofNat 32 1152).setWidth 64 = L.scr + BitVec.ofNat 64 1152 := hL.scrv (by omega_arith)
  have aW : (L.a4 + BitVec.ofNat 32 512).setWidth 64 = L.scr + BitVec.ofNat 64 512 := hL.scrv (by omega_arith)
  exact
    { hst := hbx, eax := hax, ecx := hcx, edx := hdx, ebp := hbp, hr := by decide
      sp48 := sp48 hL hc
      cw := hc.coversW fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> exact ⟨L.SCR, by simp, within_scr hL (by omega_arith) (by omega_arith)⟩
      st_o := by rw [aS, aO]; exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
      st_sc := by rw [aS, aW]; exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
      o_sc := by rw [aO, aW]; exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
      b_st := by rw [aS]; exact (hL.low_scr (by omega_arith)).sub_left hsp
      b_o := by rw [aO]; exact (hL.low_scr (by omega_arith)).sub_left hsp
      b_sc := by rw [aW]; exact (hL.low_scr (by omega_arith)).sub_left hsp
      nst := by rw [hL.scrN (by omega_arith)]; omega_arith
      no := by rw [hL.scrN (by omega_arith)]; omega_arith
      nsc := by rw [hL.scrN (by omega_arith)]; omega_arith }

/-- `finalize` of the state at `scratch + o`, holding `cnt` bytes, into
`scratch + sTmp`, in its frame. -/
theorem finRaw_ok (hL : L.Ok) {w : State} (hc : Ctx L g m₀ w) {o : Nat} (ho : o + 256 ≤ 512) {cnt : Nat}
    (hcnt : cnt < 2 ^ 32)
    (hbx : w.gpr .ebx = L.a4 + BitVec.ofNat 32 o) (hax : w.gpr .eax = BitVec.ofNat 32 cnt) (hcx : w.gpr .ecx = 0)
    (hdx : w.gpr .edx = L.a4 + BitVec.ofNat 32 1152) (hbp : w.gpr .ebp = L.a4 + BitVec.ofNat 32 512) :
    WP isa (.frame (.push Impl.Ecdsa.Rfc6979.X86.fin5) (.call P.H.finN P.H.finC) (.pop .eax fin5.length)) w
      fun u => Ctx L g m₀ u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 o, P.H.S⟩, ⟨L.scr + BitVec.ofNat 64 1152, P.H.F⟩,
        ⟨L.scr + BitVec.ofNat 64 512, P.ok.Wb⟩, ⟨L.B, 76⟩] w.mem u.mem ∧
      ∀ msg : List Byte, P.ok.SH.Repr w.mem (L.scr + BitVec.ofNat 64 o) msg → msg.length = cnt →
        (Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 1152) P.H.F).take P.H.D = P.ok.SH.H.hash msg := by
  have hS := P.ok.hSB
  have hWb := P.sizes.2.1
  have hF := P.ok.hF
  have nc := hL.nc
  have hsp := stk_sub hL hc
  have aS : (L.a4 + BitVec.ofNat 32 o).setWidth 64 = L.scr + BitVec.ofNat 64 o := hL.scrv (by omega_arith)
  have aO : (L.a4 + BitVec.ofNat 32 1152).setWidth 64 = L.scr + BitVec.ofNat 64 1152 := hL.scrv (by omega_arith)
  have aW : (L.a4 + BitVec.ofNat 32 512).setWidth 64 = L.scr + BitVec.ofNat 64 512 := hL.scrv (by omega_arith)
  have a := finArgsOf (P := P) hL hc ho hbx hax hcx hdx hbp
  refine WP.of_syms (fin_frame P.ok a fun u af hr hsy => ?_)
  rw [aS, aO, aW] at af; rw [aS, aO] at hr
  refine ⟨hc.keep (hsy := hsy) hL af.rd af.wr af.esp af.frame fun r hr => ?_, af.frame.sub fun r hr => ?_,
    fun msg hm hml => hr msg hm (by rw [hml]; omega_arith) (by
      rw [hml]; exact Proof.Pbkdf2.Stream.X86.zero_append_ofNat hcnt)⟩
  · rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact safe_scr L (by omega_arith)
    · simp only [List.mem_singleton] at hr; subst hr
      exact .inr (.inr (.inl (sub_trans hsp (Region.sub_prefix (by omega_arith)))))
  · rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., sub_refl _⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), sub_refl _⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), sub_refl _⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨L.B, 76⟩, by simp, hsp⟩

/-- `finalize` of the state at `scratch + o`, holding `cnt` bytes, into
`scratch + sTmp`. -/
theorem finCall_gen (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) {o cnt : Nat} (ho : o + 256 ≤ 512)
    (hcnt : cnt < 2 ^ 32) :
    WP isa ((cfgOf P).finCall o cnt) t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 o, P.H.S⟩, ⟨L.scr + BitVec.ofNat 64 1152, P.H.F⟩,
        ⟨L.scr + BitVec.ofNat 64 512, P.ok.Wb⟩, ⟨L.B, 76⟩] t.mem u.mem ∧
      ∀ msg : List Byte, P.ok.SH.Repr t.mem (L.scr + BitVec.ofNat 64 o) msg → msg.length = cnt →
        (Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 1152) P.H.F).take P.H.D = P.ok.SH.H.hash msg := by
  refine WP.seq (WP.mono (finArgs_ok hL hT hc o cnt) fun w ⟨hcw, hmw, hbx, hax, hcx, hdx, hbp⟩ => ?_)
  have hok := hcw.tabOk
  have htm := hcw.tabMem
  rw [hT.1, hT.2.1] at hok
  rw [hT.1] at htm
  refine tcall_ok hL hT hcw (j := 2) (by decide) (n := P.H.finN) (c := P.H.finC) htm.2.2 hok.2.2
    fun w' hc' hm' hk' _ => ?_
  refine WP.mono (finRaw_ok hL hc' ho hcnt ((hk' _ (by decide)).trans hbx) ((hk' _ (by decide)).trans hax)
    ((hk' _ (by decide)).trans hcx) ((hk' _ (by decide)).trans hdx) ((hk' _ (by decide)).trans hbp))
    fun u ⟨hcu, hf, hr⟩ => ?_
  rw [hm', hmw] at hf hr
  exact ⟨hcu, hf, hr⟩

/-- `finalize` of the state at `scratch + o`, holding `cnt` bytes, into
`scratch + sTmp`: its first `D` bytes are the digest. -/
theorem finCall_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) {o cnt : Nat} (ho : o + 256 ≤ 512)
    (hcnt : cnt < 2 ^ 32) {msg : List Byte} (hr : P.ok.SH.Repr t.mem (L.scr + BitVec.ofNat 64 o) msg)
    (hml : msg.length = cnt) :
    WP isa ((cfgOf P).finCall o cnt) t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 o, P.H.S⟩, ⟨L.scr + BitVec.ofNat 64 1152, P.H.F⟩,
        ⟨L.scr + BitVec.ofNat 64 512, P.ok.Wb⟩, ⟨L.B, 76⟩] t.mem u.mem ∧
      (Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 1152) P.H.F).take P.H.D = P.ok.SH.H.hash msg :=
  WP.mono (finCall_gen hL hT hc ho hcnt) fun _ ⟨a, b, c⟩ => ⟨a, b, c msg hr hml⟩

/-- `scratch` in `edi`. -/
theorem scrPtr_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block (cfgOf P).scrPtr) t (Upd L g m₀ t .edi L.a4) :=
  argC_ok hL hT.cw hT.ch hc (d := .edi) (by decide) (i := 4) (by omega)

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

/-- Word `k` of the padded key, after `4 k` of its bytes, with the key at
`K` (from `esp`, at `F`) and the pad at `P0` (from `edi`, at `A`). -/
theorem padW_ok {t : State} (F A : BitVec 32) (P0 K : Addr) (D : Nat) (c : Byte) {k : Nat} (hD : D % 4 = 0)
    (hk : 4 * k + 4 < 2 ^ 64)
    (hKa : k < D / 4 → addr F (fK + 4 * k) = K + BitVec.ofNat 64 (4 * k))
    (hPa : addr A (sPad + 4 * k) = P0 + BitVec.ofNat 64 (4 * k))
    {u : State} (hdi : u.gpr .edi = A) (hsp : u.gpr .esp = F) (hcx : u.gpr .ecx = c ++ c ++ c ++ c)
    (hrK : k < D / 4 → InRegions (u.rd ++ u.wr) (K + BitVec.ofNat 64 (4 * k)) 4)
    (hw : InRegions u.wr (P0 + BitVec.ofNat 64 (4 * k)) 4)
    (hm : u.mem = writeBytes t.mem P0 (padBytes t.mem K D c (4 * k)))
    (hKd : k < D / 4 → Spec.Sha256.bytesAt u.mem (K + BitVec.ofNat 64 (4 * k)) 4 =
      Spec.Sha256.bytesAt t.mem (K + BitVec.ofNat 64 (4 * k)) 4)
    (cf : Cfg) (hcD : cf.D = D) :
    WP isa (.block (cf.padW k)) u fun u' => u'.rd = u.rd ∧ u'.wr = u.wr ∧
      (∀ r, r ≠ .eax → u'.gpr r = u.gpr r) ∧ u'.mem = writeBytes t.mem P0 (padBytes t.mem K D c (4 * k + 4)) := by
  have hl := padBytes_length t.mem K D c (4 * k)
  have hap : ∀ ys : List Byte, ys.length = 4 →
      writeBytes (writeBytes t.mem P0 (padBytes t.mem K D c (4 * k))) (P0 + BitVec.ofNat 64 (4 * k)) ys =
        writeBytes t.mem P0 (padBytes t.mem K D c (4 * k) ++ ys) := fun ys hys => by
    have := writeBytes_append t.mem P0 (padBytes t.mem K D c (4 * k)) ys (by rw [hl, hys]; omega)
    rwa [hl] at this
  by_cases hkD : k < D / 4
  · rw [Cfg.padW, ite_eq_left_of_eq_true _ _ (eq_true (by rw [hcD]; exact hkD))]
    refine Wp.wp_ldm (B := F) hsp (by rw [hKa hkD]; exact hrK hkD) fun s₁ u₁ => ?_
    refine Wp.wp_xor fun s₂ u₂ => ?_
    refine Wp.wp_stm (B := A) (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hdi])
      (by rw [u₂.wr, u₁.wr, hPa]; exact hw) fun s₃ m₃ => WP.block_nil ?_
    refine ⟨by rw [m₃.rd, u₂.rd, u₁.rd], by rw [m₃.wr, u₂.wr, u₁.wr],
      fun r hr => by rw [m₃.gpr, u₂.other r hr, u₁.other r hr], ?_⟩
    rw [m₃.mem, u₂.mem, u₁.mem, u₂.gpr, u₁.gpr, u₁.other .ecx (by decide), hcx, hKa hkD, hPa,
      Proof.Pbkdf2.MdKeys.writeW_xorRep, hKd hkD, hm, hap _ (by simp [Proof.Hmac.Common.bytesAt_length]),
      padBytes_succ _ _ _ hD, ite_eq_left_of_eq_true _ _ (eq_true hkD)]
  · rw [Cfg.padW, ite_eq_right_of_eq_false _ _ (eq_false (by rw [hcD]; exact hkD))]
    refine Wp.wp_stm (B := A) hdi (by rw [hPa]; exact hw) fun s₃ m₃ => WP.block_nil ?_
    refine ⟨m₃.rd, m₃.wr, fun r _ => by rw [m₃.gpr], ?_⟩
    rw [m₃.mem, hcx, hPa, Proof.Pbkdf2.MdKeys.writeW_rep, hm, hap _ (by simp), padBytes_succ _ _ _ hD,
      ite_eq_right_of_eq_false _ _ (eq_false hkD)]

/-- The first `k` words of the padded key, from the state `u`. -/
theorem padWs_ok (F A : BitVec 32) (P0 K : Addr) {D : Nat} (c : Byte) (cf : Cfg) (hcD : cf.D = D)
    (hD : D % 4 = 0) {n : Nat} (hn : 4 * n + 4 < 2 ^ 64) (hsep : Region.Disjoint ⟨K, D⟩ ⟨P0, 4 * n⟩)
    (hDn : D ≤ 4 * n) (hKa : ∀ j < D / 4, addr F (fK + 4 * j) = K + BitVec.ofNat 64 (4 * j))
    (hPa : ∀ j < n, addr A (sPad + 4 * j) = P0 + BitVec.ofNat 64 (4 * j)) :
    ∀ k ≤ n, ∀ u : State, u.gpr .edi = A → u.gpr .esp = F → u.gpr .ecx = c ++ c ++ c ++ c →
      (∀ j < D / 4, InRegions (u.rd ++ u.wr) (K + BitVec.ofNat 64 (4 * j)) 4) →
      (∀ j < n, InRegions u.wr (P0 + BitVec.ofNat 64 (4 * j)) 4) →
      WP isa (.block ((List.range k).flatMap cf.padW)) u fun u' => u'.rd = u.rd ∧ u'.wr = u.wr ∧
        (∀ r, r ≠ .eax → u'.gpr r = u.gpr r) ∧ u'.mem = writeBytes u.mem P0 (padBytes u.mem K D c (4 * k))
  | 0, _, u, _, _, _, _, _ => WP.of_runBlock ⟨u, rfl, rfl, rfl, fun _ _ => rfl, by simp [padBytes, writeBytes_nil]⟩
  | k + 1, hk, u, hdi, hsp, hcx, hr, hw => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (padWs_ok F A P0 K c cf hcD hD hn hsep hDn hKa hPa k (by omega) u hdi hsp hcx hr hw)
      fun u₁ ⟨hrd₁, hwr₁, hg₁, hm₁⟩ => ?_
    have hf : Frame [⟨P0, 4 * n⟩] u.mem u₁.mem := by
      rw [hm₁]; exact writeBytes_frame _ _ _ (by
        rw [padBytes_length]
        have := Offset.contains_base P0 (d := 0) (n := 4 * k) (k := 4 * n) (by omega) (by omega)
        rwa [BitVec.add_zero] at this)
    refine WP.mono (padW_ok (t := u) F A P0 K D c (k := k) hD (by omega) (fun h => hKa k h) (hPa k (by omega))
      (by rw [hg₁ _ (by decide), hdi]) (by rw [hg₁ _ (by decide), hsp]) (by rw [hg₁ _ (by decide), hcx])
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
  Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 76) P.H.D

/-- `K₀ ⊕ c` at `scratch + sPad`. -/
theorem padBlk_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) (c : Byte) :
    WP isa (.block ((cfgOf P).padBlk (c ++ c ++ c ++ c))) t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 1024, P.H.B⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 1024) P.H.B =
        Spec.Hmac.xorPad (Spec.Hmac.blockKey P.ok.SH.H (keyOf P L t.mem)) c := by
  have hB4 : P.H.B % 4 = 0 := by nums
  have nc := hL.nc
  have nB := hL.nB
  rw [Cfg.padBlk, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (scrPtr_ok hL hT hc) fun u₁ h₁ => ?_
  refine WP.of_syms (Wp.wp_movi fun u₂ h₂ => WP.block_nil fun hsy => ?_)
  have hc₂ : Ctx L g m₀ u₂ := (Upd.of_wp hL h₁.ctx (by decide) h₂).ctx
  have hdi₂ : u₂.gpr .edi = L.a4 := (h₂.other _ (by decide)).trans h₁.val
  have hsp₂ : u₂.gpr .esp = L.F := hc₂.esp
  have hsep : Region.Disjoint ⟨L.B + BitVec.ofNat 64 76, P.H.D⟩ ⟨L.scr + BitVec.ofNat 64 1024, 4 * (P.H.B / 4)⟩ :=
    hL.stk_scr (by nums) (by nums)
  have hW := padWs_ok L.F L.a4 (L.scr + BitVec.ofNat 64 1024) (L.B + BitVec.ofNat 64 76) (D := P.H.D) c (cfgOf P)
    rfl (by nums) (n := P.H.B / 4) (by nums) hsep (by nums)
    (fun j hj => by
      rw [hL.addrF (by simp only [fK]; nums), Offset.add_add]; simp only [fK, Nat.zero_add])
    (fun j hj => by rw [addr_eq (by simp only [sPad]; have := hL.nc; nums), Offset.add_add]; rfl)
    (P.H.B / 4) (Nat.le_refl _) u₂ hdi₂ hsp₂ h₂.gpr (fun j hj => by
      rw [Offset.add_add]
      exact ⟨L.FR, by rw [hc₂.rd, hc₂.wr]; simp, Offset.contains _ (by omega) (by nums)
        (by have := L.he; omega)⟩)
    (fun j hj => by rw [Offset.add_add]; exact hc₂.inScrW (by nums))
  change WP isa (.block ((List.range (P.H.B / 4)).flatMap (cfgOf P).padW)) u₂ _
  refine WP.mono_syms hW fun u₃ ⟨hrd₃, hwr₃, hg₃, hm₃⟩ hsy₃ => ?_
  have hm₂ : u₂.mem = t.mem := h₂.mem.trans h₁.mem
  have hf : Frame [⟨L.scr + BitVec.ofNat 64 1024, P.H.B⟩] t.mem u₃.mem := by
    rw [hm₃, hm₂]; exact writeBytes_frame _ _ _ (by
      rw [padBytes_length]
      have := Offset.contains_base (L.scr + BitVec.ofNat 64 1024) (d := 0) (n := 4 * (P.H.B / 4)) (k := P.H.B)
        (by omega) (by omega)
      rwa [BitVec.add_zero] at this)
  refine ⟨hc₂.keep hL hrd₃ hwr₃ (hg₃ _ (by decide)) (by rw [hm₂]; exact hf) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L (by nums)) hsy₃, hf, ?_⟩
  have e4 : 4 * (P.H.B / 4) = P.H.B := by omega
  rw [e4] at hm₃
  rw [hm₃, hm₂, Proof.Hmac.Generic.Common.bytesAt_writeBytes_self' (padBytes_length _ _ _ _ _) (by nums),
    show P.H.B = P.ok.SH.H.blockSize from P.ok.hB.symm, padBytes_eq _ _ _ _ (by rw [P.ok.hB]; nums)]

/-! ## HMAC's states for the key -/

/-- A state's representation, kept by memory that changed apart from it. -/
theorem repr_keep {m m' : Mem} {ws : List Region} (hf : Frame ws m m') {p : Addr}
    (hd : ∀ r ∈ ws, Region.Disjoint ⟨p, 256⟩ r) {msg : List Byte} (hr : P.ok.SH.Repr m p msg) :
    P.ok.SH.Repr m' p msg :=
  P.ok.repr m m' p p msg (fun i hi => Frame.bytes (R := ⟨p, 256⟩) hf hd (by show 256 ≤ 2 ^ 64; decide)
    (show i < 256 by nums)) hr

/-- The key survives what HMAC changes. -/
theorem keyOf_hm (hL : L.Ok) {m m' : Mem} (hf : Frame (HM L) m m') :
    keyOf P L m' = keyOf P L m :=
  bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hL.stk_scr0 (by nums) (by decide)
    · exact Offset.disjoint_base _ (by omega) (by nums)) (by nums)

/-- After `hinit`: HMAC's states for the key `K` in the frame on entry `t`. -/
structure Inited (P : RfcHash) {dn : Nat} (L : Lay dn) (g : Reg → BitVec 32) (m₀ : Mem) (t u : State) : Prop where
  ctx : Ctx L g m₀ u
  frame : Frame (HM L) t.mem u.mem
  inner : P.ok.SH.Repr u.mem (L.scr + BitVec.ofNat 64 0)
    (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.ok.SH.H (keyOf P L t.mem)) Spec.Hmac.ipad)
  outer : P.ok.SH.Repr u.mem (L.scr + BitVec.ofNat 64 256)
    (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.ok.SH.H (keyOf P L t.mem)) Spec.Hmac.opad)

theorem xorPad_length (k : List Byte) (p : Byte) : (Spec.Hmac.xorPad k p).length = k.length :=
  List.length_map _

theorem keyOf_length (m : Mem) : (keyOf P L m).length = P.H.D := by simp [keyOf, Spec.Sha256.bytesAt]

theorem blockKey_length {k : List Byte} (hk : k.length = P.H.D) :
    (Spec.Hmac.blockKey P.ok.SH.H k).length = P.H.B := by
  have hB := P.ok.hB
  have hDB : P.H.D < P.H.B := by nums
  simp only [Spec.Hmac.blockKey, hk, hB, show ¬ P.H.B < P.H.D by omega, ite_false, List.length_append,
    List.length_replicate]
  omega

/-- The padded key, as `update` reads it at `scratch + sPad`. -/
theorem padData (hL : L.Ok) {o : Nat} (ho : o + 256 ≤ 512) :
    UpdData P L o (L.a4 + BitVec.ofNat 32 1024) P.H.B where
  cov := ⟨L.SCR, by simp, within_scr hL (by omega) (by nums)⟩
  st := by rw [hL.scrv (by omega)]; exact Offset.disjoint _ (by nums) (by nums) (by nums)
  wk := by rw [hL.scrv (by omega)]; exact Offset.disjoint _ (by nums) (by nums) (by nums)
  low := by rw [hL.scrv (by omega)]; exact hL.low_scr (by nums)
  fit := by rw [hL.scrN (by omega)]; have := hL.nc; nums

/-- The address of the padded key in `edx`. -/
theorem padA (hL : L.Ok) (hT : TabL P L) : ∀ u, Ctx L g m₀ u →
    WP isa (.block ((cfgOf P).scr .edx sPad)) u (Upd L g m₀ u .edx (L.a4 + BitVec.ofNat 32 1024)) :=
  fun _ hu => scr_ok hL hT.cw hT.ch hu (d := .edx) (by decide) 1024

theorem pad_bytes (hL : L.Ok) (m : Mem) :
    Spec.Sha256.bytesAt m ((L.a4 + BitVec.ofNat 32 1024).setWidth 64) P.H.B =
      Spec.Sha256.bytesAt m (L.scr + BitVec.ofNat 64 1024) P.H.B := by
  rw [hL.scrv (by omega)]

/-- `hinit`: each state set by `init` and updated with its padded key. -/
theorem init_step (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).hinit t (Inited P L g m₀ t) := by
  have hS : P.H.S ≤ 256 := by nums
  have hW : P.ok.Wb ≤ 512 := by nums
  have dS : ∀ {a b : Nat}, a + 256 ≤ b ∨ b + 256 ≤ a → b + 256 ≤ 8192 → a + 256 ≤ 8192 →
      Region.Disjoint ⟨L.scr + BitVec.ofNat 64 a, 256⟩ ⟨L.scr + BitVec.ofNat 64 b, P.H.S⟩ :=
    fun h hb ha => Offset.disjoint _ (by omega) (by omega) (by omega)
  unfold Cfg.hinit
  refine WP.seq (WP.mono (initCall_ok hL hT hc (o := 0) (by decide)) fun u₁ ⟨hc₁, hf₁, hr₁⟩ => ?_)
  refine WP.seq (WP.mono (initCall_ok hL hT hc₁ (o := 256) (by decide)) fun u₂ ⟨hc₂, hf₂, hr₂⟩ => ?_)
  have hr₁' := repr_keep hf₂ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dS (.inl (by decide)) (by decide) (by decide)
    · exact (hL.low_scr (by decide)).symm) hr₁
  have hF₂ : Frame (HM L) t.mem u₂.mem :=
    (hf₁.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sub_hm (by nums)
      · exact low_hm).trans (hf₂.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sub_hm (by nums)
      · exact low_hm)
  have hk₂ : keyOf P L u₂.mem = keyOf P L t.mem := keyOf_hm hL hF₂
  have hp₃ := padBlk_ok hL hT hc₂ (P := P) Spec.Hmac.ipad
  rw [← ipad32_eq] at hp₃
  refine WP.seq (WP.mono hp₃ fun u₃ ⟨hc₃, hf₃, hb₃⟩ => ?_)
  have dP : ∀ {a : Nat}, a + 256 ≤ 512 →
      Region.Disjoint ⟨L.scr + BitVec.ofNat 64 a, 256⟩ ⟨L.scr + BitVec.ofNat 64 1024, P.H.B⟩ :=
    fun h => Offset.disjoint _ (by nums) (by nums) (by nums)
  have hr₁₃ := repr_keep hf₃ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dP (by decide)) hr₁'
  have hr₂₃ := repr_keep hf₃ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dP (by decide)) hr₂
  refine WP.seq (WP.mono (updCall_ok hL hT hc₃ (o := 0) (by decide) (padA hL hT) (padData hL (by decide))
    (by nums) (by nums) hr₁₃ rfl) fun u₄ ⟨hc₄, hf₄, hr₄⟩ => ?_)
  have dW : ∀ {a : Nat}, a + 256 ≤ 512 → ∀ {b : Nat}, b + 256 ≤ 512 → a + 256 ≤ b ∨ b + 256 ≤ a →
      ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 b, P.H.S⟩ : Region), ⟨L.scr + BitVec.ofNat 64 512, P.ok.Wb⟩,
        ⟨L.B, 76⟩], Region.Disjoint ⟨L.scr + BitVec.ofNat 64 a, 256⟩ r := fun ha b hb hab r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact dS hab (by nums) (by omega)
    · exact Offset.disjoint _ (by omega) (by omega) (by nums)
    · exact (hL.low_scr (by omega)).symm
  have hr₂₄ := repr_keep hf₄ (dW (a := 256) (by decide) (b := 0) (by decide) (.inr (by decide))) hr₂₃
  have hF₄ : Frame (HM L) t.mem u₄.mem :=
    (hF₂.trans (hf₃.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact sub_hm (by nums))).trans (hf₄.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub_hm (by nums)
      · exact sub_hm (by nums)
      · exact low_hm)
  have hk₄ : keyOf P L u₄.mem = keyOf P L t.mem := keyOf_hm hL hF₄
  have hp₅ := padBlk_ok hL hT hc₄ (P := P) Spec.Hmac.opad
  rw [← opad32_eq] at hp₅
  refine WP.seq (WP.mono hp₅ fun u₅ ⟨hc₅, hf₅, hb₅⟩ => ?_)
  have hr₁₅ := repr_keep hf₅ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dP (by decide)) hr₄
  have hr₂₅ := repr_keep hf₅ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dP (by decide)) hr₂₄
  refine WP.mono (updCall_ok hL hT hc₅ (o := 256) (by decide) (padA hL hT) (padData hL (by decide))
    (by nums) (by nums) hr₂₅ rfl) fun u₆ ⟨hc₆, hf₆, hr₆⟩ => ?_
  have hr₁₆ := repr_keep hf₆ (dW (a := 0) (by decide) (b := 256) (by decide) (.inl (by decide))) hr₁₅
  refine ⟨hc₆, (hF₄.trans (hf₅.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact sub_hm (by nums))).trans (hf₆.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub_hm (by nums)
      · exact sub_hm (by nums)
      · exact low_hm), ?_, ?_⟩
  · rw [List.nil_append, pad_bytes hL, hb₃, hk₂] at hr₁₆; exact hr₁₆
  · rw [List.nil_append, pad_bytes hL, hb₅, hk₄] at hr₆; exact hr₆

/-! ## The data -/

/-- After `hupd`: the inner state holds the data too. -/
structure Updated (P : RfcHash) {dn : Nat} (L : Lay dn) (g : Reg → BitVec 32) (m₀ : Mem) (t : State)
    (dv : BitVec 32) (len : Nat) (u : State) : Prop where
  ctx : Ctx L g m₀ u
  frame : Frame (HM L) t.mem u.mem
  inner : P.ok.SH.Repr u.mem (L.scr + BitVec.ofNat 64 0)
    (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.ok.SH.H (keyOf P L t.mem)) Spec.Hmac.ipad ++
      Spec.Sha256.bytesAt t.mem (dv.setWidth 64) len)
  outer : P.ok.SH.Repr u.mem (L.scr + BitVec.ofNat 64 256)
    (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.ok.SH.H (keyOf P L t.mem)) Spec.Hmac.opad)

theorem DataOk.upd (hL : L.Ok) {dv : BitVec 32} {len : Nat} (hd : DataOk L dv len) : UpdData P L 0 dv len where
  cov := hd.within hL
  st := by have := hd.work hL (e := 0) (k := P.H.S) (by nums); rwa [hL.scrv (by omega)] at this
  wk := by have := hd.work hL (e := 512) (k := P.ok.Wb) (by nums); rwa [hL.scrv (by omega)] at this
  low := by have := hd.low hL; rwa [hL.below_F] at this
  fit := hd.fits hL

/-- The data survives what HMAC changes. -/
theorem DataOk.keep (hL : L.Ok) {dv : BitVec 32} {len : Nat} (hd : DataOk L dv len) {m m' : Mem}
    (hf : Frame (HM L) m m') :
    Spec.Sha256.bytesAt m' (dv.setWidth 64) len = Spec.Sha256.bytesAt m (dv.setWidth 64) len :=
  bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have := hd.work hL (e := 0) (k := 2256) (by omega)
      rwa [hL.scrv (by omega), BitVec.add_zero] at this
    · rw [← hL.below_F]; exact (hd.low hL).symm) (by
      rcases hd with ⟨o, -, h⟩ | ⟨o, -, -, h⟩ <;> omega)

theorem upd_step (hL : L.Ok) (hT : TabL P L) {t u : State} (hu : Inited P L g m₀ t u) {dataA : List Instr}
    {dv : BitVec 32} {len : Nat} (hdA : ∀ u, Ctx L g m₀ u → WP isa (.block dataA) u (Upd L g m₀ u .edx dv))
    (hd : DataOk L dv len) (hlen : len ≤ 256) :
    WP isa ((cfgOf P).hupd dataA len) u (Updated P L g m₀ t dv len) := by
  refine WP.mono (updCall_ok hL hT hu.ctx (o := 0) (cnt := P.H.B) (by decide) hdA (hd.upd hL) (by nums)
    (by omega) hu.inner
    (by rw [xorPad_length, blockKey_length (keyOf_length _)])) fun w ⟨hcw, hfw, hrw⟩ => ?_
  refine ⟨hcw, hu.frame.trans (hfw.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub_hm (by nums)
      · exact sub_hm (by nums)
      · exact low_hm), by rw [← hd.keep hL hu.frame]; exact hrw, repr_keep hfw (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint _ (by nums) (by nums) (by nums)
    · exact Offset.disjoint _ (by nums) (by nums) (by nums)
    · exact (hL.low_scr (by decide)).symm) hu.outer⟩

/-! ## The MAC -/

/-- After `hfin`: the MAC in the frame at `dst`. -/
structure Done (P : RfcHash) {dn : Nat} (L : Lay dn) (g : Reg → BitVec 32) (m₀ : Mem) (t : State)
    (dv : BitVec 32) (len dst : Nat) (u : State) : Prop where
  ctx : Ctx L g m₀ u
  frame : Frame [⟨L.scr, 2256⟩, ⟨L.B, 76⟩, ⟨L.B + BitVec.ofNat 64 (76 + dst), P.H.D⟩] t.mem u.mem
  mac : Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (76 + dst)) P.H.D =
    P.mac (keyOf P L t.mem) (Spec.Sha256.bytesAt t.mem (dv.setWidth 64) len)

/-- The first `D` bytes `finalize` wrote: the digest. -/
theorem tmp_digest {m : Mem} {msg : List Byte}
    (h : (Spec.Sha256.bytesAt m (L.scr + BitVec.ofNat 64 1152) P.H.F).take P.H.D = P.ok.SH.H.hash msg) :
    Spec.Sha256.bytesAt m (L.scr + BitVec.ofNat 64 1152) P.H.D = P.ok.SH.H.hash msg := by
  rw [bytesAt_take _ _ (show P.H.D ≤ P.H.F from P.ok.hDF)]; exact h

/-- The inner digest, the outer `update`'s data. -/
theorem tmpData (hL : L.Ok) : UpdData P L 256 (L.a4 + BitVec.ofNat 32 1152) P.H.D :=
  ⟨⟨L.SCR, by simp, within_scr hL (by omega) (by nums)⟩,
    by rw [hL.scrv (by omega)]; exact Offset.disjoint _ (by nums) (by nums) (by nums),
    by rw [hL.scrv (by omega)]; exact Offset.disjoint _ (by nums) (by nums) (by nums),
    by rw [hL.scrv (by omega)]; exact hL.low_scr (by nums),
    by rw [hL.scrN (by omega)]; have := hL.nc; nums⟩

/-- What `finalize` writes and the working space, within what HMAC changes. -/
theorem fin_hm {o : Nat} (ho : o + 256 ≤ 512) : ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 o, P.H.S⟩ : Region),
    ⟨L.scr + BitVec.ofNat 64 1152, P.H.F⟩, ⟨L.scr + BitVec.ofNat 64 512, P.ok.Wb⟩, ⟨L.B, 76⟩],
    ∃ r' ∈ HM L, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact sub_hm (by nums)
  · exact sub_hm (by nums)
  · exact sub_hm (by nums)
  · exact low_hm

theorem fin_step (hL : L.Ok) (hT : TabL P L) {t u : State} {dv : BitVec 32} {len dst : Nat}
    (hu : Updated P L g m₀ t dv len u) (hlen : len ≤ 256) (hdst : dst + P.H.D ≤ 180) :
    WP isa ((cfgOf P).hfin len dst) u (Done P L g m₀ t dv len dst) := by
  have hkl := blockKey_length (P := P) (keyOf_length (L := L) t.mem)
  have hdl : (Spec.Sha256.bytesAt t.mem (dv.setWidth 64) len).length = len := by simp [Spec.Sha256.bytesAt]
  unfold Cfg.hfin
  refine WP.seq (WP.mono (finCall_ok hL hT hu.ctx (o := 0) (by decide) (cnt := P.H.B + len) (by nums) hu.inner
    (by rw [List.length_append, xorPad_length, hkl, hdl])) fun w₁ ⟨hc₁, hf₁, hd₁⟩ => ?_)
  have hd₁' := tmp_digest hd₁
  have ho₁ := repr_keep hf₁ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Offset.disjoint _ (by nums) (by nums) (by nums)
    · exact Offset.disjoint _ (by nums) (by nums) (by nums)
    · exact Offset.disjoint _ (by nums) (by nums) (by nums)
    · exact (hL.low_scr (by decide)).symm) hu.outer
  have tmpD := tmpData (P := P) hL
  refine WP.seq (WP.mono (updCall_ok hL hT hc₁ (o := 256) (cnt := P.H.B) (by decide)
    (fun _ hu' => scr_ok hL hT.cw hT.ch hu' (d := .edx) (by decide) 1152) tmpD (by nums) (by nums) ho₁
    (by rw [xorPad_length, hkl])) fun w₂ ⟨hc₂, hf₂, hr₂⟩ => ?_)
  rw [hL.scrv (by omega), hd₁'] at hr₂
  refine WP.seq (WP.mono (finCall_ok hL hT hc₂ (o := 256) (by decide) (cnt := P.H.B + P.H.D) (by nums) hr₂
    (by rw [List.length_append, xorPad_length, hkl, P.macLen])) fun w₃ ⟨hc₃, hf₃, hd₃⟩ => ?_)
  have hd₃' := tmp_digest hd₃
  rw [WP.block_append_iff]
  refine WP.mono (scrPtr_ok hL hT hc₃) fun w₄ h₄ => ?_
  have hsep : Region.Disjoint ⟨L.scr + BitVec.ofNat 64 1152, P.H.D⟩ ⟨L.B + BitVec.ofNat 64 (76 + dst), P.H.D⟩ :=
    (hL.stk_scr (by nums) (by nums)).symm
  refine WP.mono_syms (copyBytes_ok (src := .edi) (dst := .esp) (S := L.a4) (D := L.F)
    (SA := L.scr + BitVec.ofNat 64 1152) (DA := L.B + BitVec.ofNat 64 (76 + dst))
    (so := 1152) (d := dst) (Q := P.H.D) (by decide) (by decide)
    (fun j hj => by rw [addr_eq (by have := hL.nc; nums), Offset.add_add])
    (fun j hj => by rw [hL.addrF (by nums), Offset.add_add]; congr 2; omega)
    hsep (by nums) (by nums) h₄.val h₄.ctx.esp
    (fun j hj => by rw [Offset.add_add]; exact h₄.ctx.inScr (by nums)) (fun j hj => by
      rw [Offset.add_add]; exact h₄.ctx.inFrW (by omega) (by nums) hL))
    fun w₅ ⟨hrd₅, hwr₅, hg₅, hf₅, hb₅⟩ hsy₅ => ?_
  refine ⟨h₄.ctx.keep hL hrd₅ hwr₅ (hg₅ _ (by decide)) hf₅
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by nums)) hsy₅, ?_, ?_⟩
  · have e : ∀ {r : Region}, (∃ r' ∈ HM L, Region.Sub r r') →
        ∃ r' ∈ [(⟨L.scr, 2256⟩ : Region), ⟨L.B, 76⟩, ⟨L.B + BitVec.ofNat 64 (76 + dst), P.H.D⟩], Region.Sub r r' :=
      fun ⟨r', hr', hs⟩ => ⟨r', by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr' ⊢; rcases hr' with h | h <;> simp [h], hs⟩
    refine ((((hu.frame.sub fun r hr => e ⟨r, hr, sub_refl _⟩).trans (hf₁.sub fun r hr => e (fin_hm (by decide) r hr))).trans
      (hf₂.sub fun r hr => e ?_)).trans (hf₃.sub fun r hr => e (fin_hm (by decide) r hr))).trans ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub_hm (by nums)
      · exact sub_hm (by nums)
      · exact low_hm
    · rw [← h₄.mem]; exact hf₅.sub fun r hr => ⟨r, by simp_all, sub_refl _⟩
  · rw [hb₅, h₄.mem, hd₃']
    rfl

/-! ## The whole HMAC -/

/-- `HMAC_K(data)`, for the key `K` in the frame, to the frame at `dst`. -/
theorem hmac_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) {dataA : List Instr} {dv : BitVec 32}
    {len dst : Nat} (hdA : ∀ u, Ctx L g m₀ u → WP isa (.block dataA) u (Upd L g m₀ u .edx dv))
    (hd : DataOk L dv len) (hlen : len ≤ 256) (hdst : dst + P.H.D ≤ 180) :
    WP isa ((cfgOf P).hmac dataA len dst) t (Done P L g m₀ t dv len dst) :=
  WP.seq (WP.mono (init_step hL hT hc) fun _ hu => WP.seq (WP.mono (upd_step hL hT hu hdA hd hlen) fun _ hw =>
    fin_step hL hT hw hlen hdst))

end VG.Proof.Ecdsa.Rfc6979.X86
