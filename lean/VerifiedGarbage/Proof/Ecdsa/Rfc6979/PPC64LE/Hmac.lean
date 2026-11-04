module

import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Args
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Calls
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Copy
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Entry
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.ICall
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Proof.Pbkdf2.MdKeys
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Layout
public import VerifiedGarbage.Proof.Mont.PPC64LE.Words

/-!
# Deterministic ECDSA on PPC64LE: one HMAC, through the table

`HMAC_K(data)` (`Cfg.hmac`), for the key `K` (of the hash function's output
length) at the frame's `K` and `len` bytes of data in the frame or in
`scratch` above HMAC's working space (`DataOk`), written to the frame at
`dst`, from the table's streaming functions, each called indirectly
(`tcall_ok`: the table's word, which `SyOk` says holds the function of
`L.G`, whose call an indirect call of `L.f`'s functions reaches): the states
for the key (`init_step`: each set by `init`, `initCall_ok`, and updated
with the padded key, `padBlk_ok` and `updCall_ok`), the inner state updated
with the data (`upd_step`), and the MAC (`fin_step`: the inner state
finalized, `finCall_ok`, the outer one updated with its digest and
finalized, and the digest copied). They change only HMAC's states and
working space, the padded key and what `finalize` writes (all within the
first 2256 bytes of `scratch`), the 96 bytes below the frame, and `dst`
(`hmac_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE VG.Impl.Ecdsa.Rfc6979.PPC64LE
open VG.Proof.Mont.PPC64LE (Kp)
open VG.WriteBytes (writeBytes writeBytes_append writeBytes_nil writeBytes_frame)

variable {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {lr : Addr} {m₀ : Mem}

theorem Lay.Ok.sp_toNat {L : Lay dn} (hL : L.Ok) : (L.B + BitVec.ofNat 64 96).toNat = L.B.toNat + 96 := by
  have := hL.nB
  rw [Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (by omega_arith : 96 < 2 ^ 64), Nat.mod_eq_of_lt (by omega_arith)]

theorem Lay.below96 (L : Lay dn) : below (L.B + BitVec.ofNat 64 96) 96 = ⟨L.B, 96⟩ := by
  show (⟨L.B + BitVec.ofNat 64 96 - BitVec.ofNat 64 96, 96⟩ : Region) = _
  rw [BitVec.add_sub_cancel]

theorem Lay.below48 (L : Lay dn) : below (L.B + BitVec.ofNat 64 96) 48 = ⟨L.B + BitVec.ofNat 64 48, 48⟩ := by
  show (⟨L.B + BitVec.ofNat 64 96 - BitVec.ofNat 64 48, 48⟩ : Region) = _
  congr 1
  rw [show (BitVec.ofNat 64 96 : BitVec 64) = BitVec.ofNat 64 48 + BitVec.ofNat 64 48 from rfl, ← BitVec.add_assoc,
    BitVec.add_sub_cancel]

/-- The code and the layout are of the hash function `P`: its sizes and the
functions an indirect call may reach, and the table's. -/
structure KOk (P : Kit) (c : Cfg) (L : Lay dn) : Prop where
  D : c.D = P.H.D
  B : c.B = P.H.B
  f : c.f = P.f
  G : L.G = P.H
  lf : L.f = P.f

/-- The key `K`: the first `D` bytes of the frame's `K`. -/
abbrev keyOf (P : Kit) (L : Lay dn) (m : Mem) : List Byte := Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 128) P.H.D

/-- The regions of `scratch` HMAC uses: the states, the working space, the
padded key and what `finalize` writes. -/
abbrev hmacScr (L : Lay dn) : Region := ⟨L.scr, 2256⟩

theorem scr_sub (L : Lay dn) {e k : Nat} (h : e + k ≤ 2256) : Region.Sub ⟨L.scr + BitVec.ofNat 64 e, k⟩ (hmacScr L) :=
  Offset.sub_base _ h

/-- A region of `scratch` below `2256`, as part of what HMAC changes. -/
theorem sub_hm {e k : Nat} (h : e + k ≤ 2256) :
    ∃ r' ∈ [hmacScr L, ⟨L.B, 96⟩], Region.Sub ⟨L.scr + BitVec.ofNat 64 e, k⟩ r' :=
  ⟨_, List.mem_cons_self .., scr_sub L h⟩

theorem low_hm : ∃ r' ∈ [hmacScr L, ⟨L.B, 96⟩], Region.Sub ⟨L.B + BitVec.ofNat 64 48, 48⟩ r' :=
  ⟨⟨L.B, 96⟩, by simp, Offset.sub_base _ (by omega)⟩

/-- The sizes of the hash function, as the proofs use them. -/
theorem Kit.sizes (P : Kit) : P.H.S ≤ 192 ∧ 384 + P.H.W ≤ 1792 ∧ 0 < P.H.D ∧ P.H.D ≤ 64 ∧ P.H.D % 4 = 0 ∧
    P.H.D ≤ P.H.B ∧ (P.H.B = 64 ∨ P.H.B = 128) ∧ P.H.D ≤ P.H.FD ∧ P.H.FD ≤ 64 :=
  ⟨P.hS, P.hW, P.hH.hD0, P.hH.hD64, P.hH.hD4, P.hH.hDB, P.hH.dims.B, P.hH.hDF, P.hH.hFD64⟩

/-- Facts about the sizes of the hash function `‹Kit›`, and the arithmetic
they decide. -/
macro "nums" : tactic => `(tactic| first | omega |
  (obtain ⟨_, _, _, _, _, _, _, _, _⟩ := Kit.sizes ‹Kit›; omega))

/-! ## The table -/

/-- The indirect call of the table's function `j`, at the address its word
`j` holds, of `n`. -/
theorem tcall_ok (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) {j : Nat} (hj : 8 * j + 8 ≤ 40)
    {n : String} {c : Prog isa} {ts : List (String × Prog isa)}
    (hw : m₀.readW (L.tab + BitVec.ofNat 64 (8 * j)) 64 = t.syms n)
    (hf : ts.find? (fun q => t.syms q.1 == t.syms n) = some (n, c)) {Q : State → Prop}
    (h : ∀ t', Ctx L g lr m₀ t' → t'.mem = t.mem → Kp [.r12] t t' → t'.syms = t.syms →
      WP isa (.call n c) t' Q) :
    WP isa (Cfg.tcall j ts) t Q := by
  unfold Cfg.tcall
  refine WP.seq (WP.mono_syms (tword_ok hL hc hj) fun t' ⟨hc', hm, k, h12⟩ hsy => ?_)
  refine WP.icalls_of_call (a := t'.gpr .r12) rfl ?_ (h t' hc' hm k hsy)
  show ts.find? (fun q => t'.syms q.1 == t'.gpr .r12) = _
  rw [h12, hw, hsy]; exact hf

/-- The writes of a call, within `scratch` and the stack below the frame. -/
theorem safe_call {ws : List Region} (hs : ∀ r ∈ ws, ∃ e k, r = ⟨L.scr + BitVec.ofNat 64 e, k⟩ ∧ e + k ≤ 2256) :
    ∀ r ∈ ws ++ [⟨L.B + BitVec.ofNat 64 48, 48⟩], Safe L r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨e, k, rfl, h⟩ := hs r hr
    exact safe_scr L (by omega)
  · simp only [List.mem_singleton] at hr; subst hr
    exact safe_low L (by omega)

/-! ## The streaming `init` -/

/-- `init` of the state at `scratch + o`: it represents the empty message. -/
theorem initCall_ok (P : Kit) {c : Cfg} (hK : KOk P c L) (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t)
    (hy : SyOk L m₀ t) {o : Nat} (ho : o + 192 ≤ 384) :
    WP isa (c.initCall o) t fun u => Ctx L g lr m₀ u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 o, P.H.S⟩, ⟨L.B + BitVec.ofNat 64 48, 48⟩] t.mem u.mem ∧
      P.hH.SH.Repr u.mem (L.scr + BitVec.ofNat 64 o) [] ∧ u.syms = t.syms := by
  have hnc := hL.nc
  have hS := P.hS
  unfold Cfg.initCall
  refine WP.seq (WP.mono_syms (initArgs_ok hL hc (o := o) (by omega)) fun u ⟨hcu, hmu, _, h3⟩ hsu => ?_)
  have hok := hy.tabOk
  have htm := hy.tabMem
  rw [hK.G, hK.lf] at hok
  rw [hK.G] at htm
  rw [hK.f]
  refine tcall_ok hL hcu (j := 0) (by decide) (n := P.H.initN) (c := P.H.initC)
    (by rw [Nat.mul_zero, BitVec.add_zero, hsu]; exact htm.1) (by rw [hsu]; exact hok.i) fun u' hc' hm' k' hs' => ?_
  have hsp : u'.sp = L.B + BitVec.ofNat 64 96 := hc'.sp
  have hcall : WP isa (.call P.H.initN P.H.initC) u' fun v => Ctx L g lr m₀ v ∧
      Frame [⟨L.scr + BitVec.ofNat 64 o, P.H.S⟩, ⟨L.B + BitVec.ofNat 64 48, 48⟩] t.mem v.mem ∧
      P.hH.SH.Repr v.mem (L.scr + BitVec.ofNat 64 o) [] := P.hH.callInit_ok (st := L.scr + BitVec.ofNat 64 o)
    (by rw [k'.gpr _ (by decide), h3])
    ⟨by rw [hsp, hL.sp_toNat]; omega, by rw [hsp, L.below48]; exact hL.stk_scr (by omega) (by omega)⟩
    (hc'.covers fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨L.SCR, by simp, within_off _ (by omega)⟩)
    (hc'.coversW fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨L.SCR, by simp, within_off _ (by omega)⟩)
    fun s' h₁ h₂ h₃ h₄ hcs hr => by
      rw [hsp, L.below48] at h₄
      exact ⟨hc'.keep hL h₁ h₂ h₃ hcs h₄ (safe_call fun r hr => by
        simp only [List.mem_singleton] at hr; exact ⟨o, P.H.S, hr, by omega⟩), by rw [← hmu, ← hm']; exact h₄, hr⟩
  exact WP.mono_syms hcall fun v ⟨hcv, hf, hr⟩ hsv => ⟨hcv, hf, hr, by rw [hsv, hs', hsu]⟩

/-! ## The streaming `update` -/

/-- Where data `update` reads may be: within a buffer or the frame, and
apart from the state it updates, the working space and the stack the calls use. -/
structure UpdData (P : Kit) (L : Lay dn) (o : Nat) (da : Addr) (len : Nat) : Prop where
  cov : ∃ R ∈ [L.D, L.DG, L.FR, L.OUT, L.SCR], Within ⟨da, len⟩ R
  st : Region.Disjoint ⟨da, len⟩ ⟨L.scr + BitVec.ofNat 64 o, P.H.S⟩
  wk : Region.Disjoint ⟨da, len⟩ ⟨L.scr + BitVec.ofNat 64 384, P.H.W⟩
  low : Region.Disjoint ⟨L.B + BitVec.ofNat 64 48, 48⟩ ⟨da, len⟩

/-- `update` of the state at `scratch + o`, holding `cnt` bytes, with `len`
bytes at `da`: the state represents them too. -/
theorem updCall_ok (P : Kit) {c : Cfg} (hK : KOk P c L) (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t)
    (hy : SyOk L m₀ t) {o cnt : Nat} (ho : o + 192 ≤ 384) {dataA : List Instr} {da : Addr} {len : Nat}
    (hdA : ∀ u, Ctx L g lr m₀ u → u.gpr .r12 = L.scr → WP isa (.block dataA) u fun u' =>
      Kp [.r5] u u' ∧ u'.mem = u.mem ∧ u'.gpr .r5 = da)
    (hd : UpdData P L o da len) (hcnt : cnt < 2 ^ 15) (hlen : len < 2 ^ 15)
    {msg : List Byte} (hr : P.hH.SH.Repr t.mem (L.scr + BitVec.ofNat 64 o) msg) (hml : msg.length = cnt) :
    WP isa (c.updCall o cnt dataA len) t fun u => Ctx L g lr m₀ u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 o, P.H.S⟩, ⟨L.scr + BitVec.ofNat 64 384, P.H.W⟩,
        ⟨L.B + BitVec.ofNat 64 48, 48⟩] t.mem u.mem ∧
      P.hH.SH.Repr u.mem (L.scr + BitVec.ofNat 64 o) (msg ++ Spec.Sha256.bytesAt t.mem da len) ∧
      u.syms = t.syms := by
  have hnc := hL.nc
  have hnB := hL.nB
  have hS := P.hS
  have hW := P.hW
  simp only [sWork, sPad] at hW
  unfold Cfg.updCall
  refine WP.seq (WP.mono_syms (updArgs_ok hL hc (o := o) (by omega) hcnt hlen hdA)
    fun u ⟨hcu, hmu, _, h3, h4, h5, h6, h7⟩ hsu => ?_)
  have hok := hy.tabOk
  have htm := hy.tabMem
  rw [hK.G, hK.lf] at hok
  rw [hK.G] at htm
  rw [hK.f]
  refine tcall_ok hL hcu (j := 1) (by decide) (n := P.H.updN) (c := P.H.updC)
    (by rw [Nat.mul_one, hsu]; exact htm.2.1) (by rw [hsu]; exact hok.u) fun u' hc' hm' k' hs' => ?_
  have hsp : u'.sp = L.B + BitVec.ofNat 64 96 := hc'.sp
  have hcall : WP isa (.call P.H.updN P.H.updC) u' fun v => Ctx L g lr m₀ v ∧
      Frame [⟨L.scr + BitVec.ofNat 64 o, P.H.S⟩, ⟨L.scr + BitVec.ofNat 64 384, P.H.W⟩,
        ⟨L.B + BitVec.ofNat 64 48, 48⟩] t.mem v.mem ∧
      P.hH.SH.Repr v.mem (L.scr + BitVec.ofNat 64 o) (msg ++ Spec.Sha256.bytesAt t.mem da len) :=
    P.hH.callUpd_ok (st := L.scr + BitVec.ofNat 64 o) (dat := da)
    (scr := L.scr + BitVec.ofNat 64 384) (len := len) (by rw [k'.gpr _ (by decide), h3])
    (by rw [k'.gpr _ (by decide), h5])
    (by rw [k'.gpr _ (by decide), h6, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
    (by rw [k'.gpr _ (by decide), h7]) (Offset.disjoint _ (by omega) (by omega) (by omega)) hd.st hd.wk
    (by rw [hsp, hL.sp_toNat]; omega) (by rw [hsp, L.below48]; exact hL.stk_scr (by omega) (by omega))
    (by rw [hsp, L.below48]; exact hd.low) (by rw [hsp, L.below48]; exact hL.stk_scr (by omega) (by omega))
    (hc'.covers fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hd.cov
      all_goals exact ⟨L.SCR, by simp, within_off _ (by omega)⟩)
    (hc'.coversW fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨L.SCR, by simp, within_off _ (by omega)⟩)
    fun s' h₁ h₂ h₃ h₄ hcs hupd => by
      rw [hsp, L.below48] at h₄
      refine ⟨hc'.keep hL h₁ h₂ h₃ hcs h₄ (safe_call fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨o, P.H.S, rfl, by omega⟩
        · exact ⟨384, P.H.W, rfl, by omega⟩), by rw [← hmu, ← hm']; exact h₄, ?_⟩
      have := hupd msg (by rw [hm', hmu]; exact hr) (by rw [k'.gpr _ (by decide), h4, hml])
      rwa [hm', hmu] at this
  exact WP.mono_syms hcall fun v ⟨hcv, hf, hr'⟩ hsv => ⟨hcv, hf, hr', by rw [hsv, hs', hsu]⟩

/-! ## The streaming `finalize` -/

/-- `finalize` of the state at `scratch + o`, holding `cnt` bytes, into
`scratch + sTmp`: its first `D` bytes are the digest. -/
theorem finCall_ok (P : Kit) {c : Cfg} (hK : KOk P c L) (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t)
    (hy : SyOk L m₀ t) {o cnt : Nat} (ho : o + 192 ≤ 384) (hcnt : cnt < 2 ^ 15) {msg : List Byte}
    (hr : P.hH.SH.Repr t.mem (L.scr + BitVec.ofNat 64 o) msg) (hml : msg.length = cnt) :
    WP isa (c.finCall o cnt) t fun u => Ctx L g lr m₀ u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 o, P.H.S⟩, ⟨L.scr + BitVec.ofNat 64 1920, P.H.FD⟩,
        ⟨L.scr + BitVec.ofNat 64 384, P.H.W⟩, ⟨L.B + BitVec.ofNat 64 48, 48⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 1920) P.H.D = P.hH.SH.H.hash msg ∧ u.syms = t.syms := by
  have hnc := hL.nc
  have hnB := hL.nB
  have hS := P.hS
  have hW := P.hW
  have hFD := P.hH.hFD64
  have hDF := P.hH.hDF
  simp only [sWork, sPad] at hW
  unfold Cfg.finCall
  refine WP.seq (WP.mono_syms (finArgs_ok hL hc (o := o) (by omega) hcnt)
    fun u ⟨hcu, hmu, _, h3, h4, h5, h6⟩ hsu => ?_)
  have hok := hy.tabOk
  have htm := hy.tabMem
  rw [hK.G, hK.lf] at hok
  rw [hK.G] at htm
  rw [hK.f]
  refine tcall_ok hL hcu (j := 2) (by decide) (n := P.H.finN) (c := P.H.finC)
    (by rw [show 8 * 2 = 16 from rfl, hsu]; exact htm.2.2) (by rw [hsu]; exact hok.f) fun u' hc' hm' k' hs' => ?_
  have hsp : u'.sp = L.B + BitVec.ofNat 64 96 := hc'.sp
  have hcall : WP isa (.call P.H.finN P.H.finC) u' fun v => Ctx L g lr m₀ v ∧
      Frame [⟨L.scr + BitVec.ofNat 64 o, P.H.S⟩, ⟨L.scr + BitVec.ofNat 64 1920, P.H.FD⟩,
        ⟨L.scr + BitVec.ofNat 64 384, P.H.W⟩, ⟨L.B + BitVec.ofNat 64 48, 48⟩] t.mem v.mem ∧
      Spec.Sha256.bytesAt v.mem (L.scr + BitVec.ofNat 64 1920) P.H.D = P.hH.SH.H.hash msg :=
    P.hH.callFin_ok (st := L.scr + BitVec.ofNat 64 o) (o := L.scr + BitVec.ofNat 64 1920)
    (scr := L.scr + BitVec.ofNat 64 384) (by rw [k'.gpr _ (by decide), h3]) (by rw [k'.gpr _ (by decide), h5])
    (by rw [k'.gpr _ (by decide), h6]) (Offset.disjoint _ (by omega) (by omega) (by omega))
    (Offset.disjoint _ (by omega) (by omega) (by omega)) (Offset.disjoint _ (by omega) (by omega) (by omega))
    (by rw [hsp, hL.sp_toNat]; omega) (by rw [hsp, L.below48]; exact hL.stk_scr (by omega) (by omega))
    (by rw [hsp, L.below48]; exact hL.stk_scr (by omega) (by omega))
    (by rw [hsp, L.below48]; exact hL.stk_scr (by omega) (by omega))
    (hc'.covers fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact ⟨L.SCR, by simp, within_off _ (by omega)⟩)
    (hc'.coversW fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact ⟨L.SCR, by simp, within_off _ (by omega)⟩)
    fun s' h₁ h₂ h₃ h₄ hcs hfin => by
      rw [hsp, L.below48] at h₄
      refine ⟨hc'.keep hL h₁ h₂ h₃ hcs h₄ (safe_call fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨o, P.H.S, rfl, by omega⟩
        · exact ⟨1920, P.H.FD, rfl, by omega⟩
        · exact ⟨384, P.H.W, rfl, by omega⟩), by rw [← hmu, ← hm']; exact h₄, ?_⟩
      have hl : msg.length < 2 ^ 64 := by rw [hml]; omega
      have := hfin msg (by rw [hm', hmu]; exact hr) hl (by rw [k'.gpr _ (by decide), h4, hml])
      rw [bytesAt_take _ _ hDF, this, ← P.hH.hashTake]
  exact WP.mono_syms hcall fun v ⟨hcv, hf, hr'⟩ hsv => ⟨hcv, hf, hr', by rw [hsv, hs', hsu]⟩

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

theorem sw32 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

/-- Word `k` of the padded key, after `4 k` of its bytes. -/
theorem padW_ok {t : State} (P0 K : Addr) (D : Nat) (c : Byte) {k : Nat} (hD : D % 4 = 0) (hk : 4 * k + 4 < 2 ^ 64)
    (hk15 : 1792 + 4 * k < 2 ^ 15) {u : State}
    (hP : u.gpr .r12 + BitVec.ofNat 64 (1792 + 4 * k) = P0 + BitVec.ofNat 64 (4 * k))
    (hK : u.gpr .r11 + BitVec.ofNat 64 (32 + 4 * k) = K + BitVec.ofNat 64 (4 * k))
    (h9 : (u.gpr .r9).setWidth 32 = c ++ c ++ c ++ c)
    (hrK : k < D / 4 → InRegions (u.rd ++ u.wr) (K + BitVec.ofNat 64 (4 * k)) 4)
    (hw : InRegions u.wr (P0 + BitVec.ofNat 64 (4 * k)) 4)
    (hm : u.mem = writeBytes t.mem P0 (padBytes t.mem K D c (4 * k)))
    (hKd : k < D / 4 → Spec.Sha256.bytesAt u.mem (K + BitVec.ofNat 64 (4 * k)) 4 =
      Spec.Sha256.bytesAt t.mem (K + BitVec.ofNat 64 (4 * k)) 4)
    (cf : Cfg) (hcD : cf.D = D) :
    WP isa (.block (cf.padW k)) u fun u' => Kp [.r8] u u' ∧
      u'.mem = writeBytes t.mem P0 (padBytes t.mem K D c (4 * k + 4)) := by
  have hl := padBytes_length t.mem K D c (4 * k)
  have hap : ∀ ys : List Byte, ys.length = 4 →
      writeBytes (writeBytes t.mem P0 (padBytes t.mem K D c (4 * k))) (P0 + BitVec.ofNat 64 (4 * k)) ys =
        writeBytes t.mem P0 (padBytes t.mem K D c (4 * k) ++ ys) := fun ys hys => by
    have := writeBytes_append t.mem P0 (padBytes t.mem K D c (4 * k)) ys (by rw [hl, hys]; omega)
    rwa [hl] at this
  by_cases hkD : k < D / 4
  · rw [Cfg.padW, ite_eq_left_of_eq_true _ _ (eq_true (by rw [hcD]; exact hkD))]
    refine stepLwz (a := K + BitVec.ofNat 64 (4 * k)) (by decide) (by simp only [fK]; omega)
      (by simp only [fK]; exact hK) (hrK hkD) fun u₁ k₁ m₁ v₁ => ?_
    refine stepXor fun u₂ k₂ m₂ v₂ => ?_
    refine stepStw (a := P0 + BitVec.ofNat 64 (4 * k)) (by decide) (by simp only [sPad]; omega)
      (by rw [k₂.gpr _ (by decide), k₁.gpr _ (by decide)]; simp only [sPad]; exact hP)
      (by rw [k₂.wr, k₁.wr]; exact hw) fun u₃ k₃ g₃ m₃ => wp_nil ⟨(k₁.trans k₂).trans k₃.mono, ?_⟩
    rw [m₃, m₂, m₁, v₂, v₁, k₁.gpr _ (by decide), BitVec.setWidth_xor, sw32, h9,
      Proof.Pbkdf2.MdKeys.writeW_xorRep, hKd hkD, hm, hap _ (by simp [Proof.Hmac.Common.bytesAt_length]),
      padBytes_succ _ _ _ hD, ite_eq_left_of_eq_true _ _ (eq_true hkD)]
  · rw [Cfg.padW, ite_eq_right_of_eq_false _ _ (eq_false (by rw [hcD]; exact hkD))]
    refine stepStw (a := P0 + BitVec.ofNat 64 (4 * k)) (by decide) (by simp only [sPad]; omega)
      (by simp only [sPad]; exact hP) hw fun u₃ k₃ g₃ m₃ => wp_nil ⟨k₃.mono, ?_⟩
    rw [m₃, h9, Proof.Pbkdf2.MdKeys.writeW_rep, hm, hap _ (by simp), padBytes_succ _ _ _ hD,
      ite_eq_right_of_eq_false _ _ (eq_false hkD)]

/-- The first `k` words of the padded key, from the state `u`. -/
theorem padWs_ok (P0 K : Addr) {D : Nat} (c : Byte) (cf : Cfg) (hcD : cf.D = D)
    (hD : D % 4 = 0) {n : Nat} (hn : 4 * n + 4 < 2 ^ 64) (hn15 : 1792 + 4 * n < 2 ^ 15)
    (hsep : Region.Disjoint ⟨K, D⟩ ⟨P0, 4 * n⟩) (hDn : D ≤ 4 * n) :
    ∀ k ≤ n, ∀ u : State, (∀ j, u.gpr .r12 + BitVec.ofNat 64 (1792 + 4 * j) = P0 + BitVec.ofNat 64 (4 * j)) →
      (∀ j, u.gpr .r11 + BitVec.ofNat 64 (32 + 4 * j) = K + BitVec.ofNat 64 (4 * j)) →
      (u.gpr .r9).setWidth 32 = c ++ c ++ c ++ c →
      (∀ j < D / 4, InRegions (u.rd ++ u.wr) (K + BitVec.ofNat 64 (4 * j)) 4) →
      (∀ j < n, InRegions u.wr (P0 + BitVec.ofNat 64 (4 * j)) 4) →
      WP isa (.block ((List.range k).flatMap cf.padW)) u fun u' => Kp [.r8] u u' ∧
        u'.mem = writeBytes u.mem P0 (padBytes u.mem K D c (4 * k))
  | 0, _, u, _, _, _, _, _ => wp_nil ⟨Kp.refl _ _, by simp [padBytes, writeBytes_nil]⟩
  | k + 1, hk, u, hP, hK, h9, hr, hw => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (padWs_ok P0 K c cf hcD hD hn hn15 hsep hDn k (by omega) u hP hK h9 hr hw)
      fun u₁ ⟨k₁, hm₁⟩ => ?_
    have hf : Frame [⟨P0, 4 * n⟩] u.mem u₁.mem := by
      rw [hm₁]; exact writeBytes_frame _ _ _ (by
        rw [padBytes_length]
        have := Offset.contains_base P0 (d := 0) (n := 4 * k) (k := 4 * n) (by omega) (by omega)
        rwa [BitVec.add_zero] at this)
    refine WP.mono (padW_ok (t := u) P0 K D c (k := k) hD (by omega) (by omega)
      (by rw [k₁.gpr _ (by decide)]; exact hP k) (by rw [k₁.gpr _ (by decide)]; exact hK k)
      (by rw [k₁.gpr _ (by decide)]; exact h9)
      (fun hkD => by rw [k₁.rd, k₁.wr]; exact hr k hkD) (by rw [k₁.wr]; exact hw k (by omega)) hm₁
      (fun hkD => bytesAt_frame hf (fun r hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact hsep.sub_left (Offset.sub_base _ (by omega))) (by omega)) cf hcD)
      fun u₂ ⟨k₂, hm₂⟩ => ⟨k₁.trans k₂, by rw [hm₂, show 4 * (k + 1) = 4 * k + 4 by omega]⟩

theorem ipad32_eq : ipad32 = Spec.Hmac.ipad ++ Spec.Hmac.ipad ++ Spec.Hmac.ipad ++ Spec.Hmac.ipad := by decide
theorem opad32_eq : opad32 = Spec.Hmac.opad ++ Spec.Hmac.opad ++ Spec.Hmac.opad ++ Spec.Hmac.opad := by decide

/-- `K₀ ⊕ c` at `scratch + sPad`. -/
theorem padBlk_ok (P : Kit) {cf : Cfg} (hK : KOk P cf L) (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) (c : Byte) :
    WP isa (.block (cf.padBlk (c ++ c ++ c ++ c))) t fun u => Ctx L g lr m₀ u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 1792, P.H.B⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 1792) P.H.B =
        Spec.Hmac.xorPad (Spec.Hmac.blockKey P.hH.SH.H (keyOf P L t.mem)) c := by
  have hnc := hL.nc
  have hnB := hL.nB
  have hB : P.H.B % 4 = 0 ∧ P.H.B ≤ 128 := by rcases P.hH.dims.B with h | h <;> omega
  rw [Cfg.padBlk, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (scrBase_ok hL hc) fun u₁ ⟨hc₁, hm₁, k₁, b₁, s₁⟩ => ?_
  simp only [Impl.Mont.PPC64LE.movImm]
  refine stepLis fun u₂ k₂ m₂ v₂ => ?_
  refine stepOri fun u₃ k₃ m₃ v₃ => wp_nil ?_
  have h9 : (u₃.gpr .r9).setWidth 32 = c ++ c ++ c ++ c := by rw [v₃, v₂]; exact lis_ori _
  have k₃' : Kp [.r9] u₁ u₃ := k₂.trans k₃
  have hc₃ : Ctx L g lr m₀ u₃ := hc₁.kp hL k₃' (by rw [m₃, m₂])
  have r12 : u₃.gpr .r12 = L.scr := by rw [k₃'.gpr _ (by decide), s₁]
  have r11 : u₃.gpr .r11 = L.B + BitVec.ofNat 64 96 := by rw [k₃'.gpr _ (by decide), b₁]
  have hm₃ : u₃.mem = t.mem := by rw [m₃, m₂, hm₁]
  have hDB := P.hH.hDB
  have hD4 := P.hH.hD4
  have hD64 := P.hH.hD64
  have e4 : 4 * (P.H.B / 4) = P.H.B := by omega
  have hsep : Region.Disjoint ⟨L.B + BitVec.ofNat 64 128, P.H.D⟩ ⟨L.scr + BitVec.ofNat 64 1792, 4 * (P.H.B / 4)⟩ :=
    hL.stk_scr (by have := L.e_le; omega) (by omega)
  rw [hK.B]
  refine WP.mono (padWs_ok (L.scr + BitVec.ofNat 64 1792) (L.B + BitVec.ofNat 64 128) (D := P.H.D) c cf hK.D hD4
    (n := P.H.B / 4) (by omega) (by omega) hsep (by omega) (P.H.B / 4) (Nat.le_refl _) u₃
    (fun j => by rw [r12, Offset.add_add])
    (fun j => by rw [r11, fr_add, fr_add, show 96 + (32 + 4 * j) = 128 + 4 * j by omega])
    h9 (fun j hj => by rw [fr_add]; exact hc₃.inFr (by omega) (by have := L.e_le; omega))
    (fun j hj => by rw [Offset.add_add]; exact hc₃.inScrW (by omega))) fun u₄ ⟨k₄, hm₄⟩ => ?_
  have hf : Frame [⟨L.scr + BitVec.ofNat 64 1792, P.H.B⟩] t.mem u₄.mem := by
    rw [hm₄, hm₃]; exact writeBytes_frame _ _ _ (by
      rw [padBytes_length]
      have := Offset.contains_base (L.scr + BitVec.ofNat 64 1792) (d := 0) (n := 4 * (P.H.B / 4)) (k := P.H.B)
        (by omega) (by omega)
      rwa [BitVec.add_zero] at this)
  refine ⟨hc₃.keep hL k₄.rd k₄.wr k₄.sp (fun r hr => k₄.gpr r fun h => by
      simp only [List.mem_singleton] at h; subst h; simp [preserved] at hr) (by rw [hm₃]; exact hf)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L (by omega)), hf, ?_⟩
  rw [e4] at hm₄
  rw [hm₄, hm₃, Proof.Hmac.Generic.Common.bytesAt_writeBytes_self' (padBytes_length _ _ _ _ _) (by omega),
    show P.H.B = P.hH.SH.H.blockSize from P.hH.hB.symm, padBytes_eq _ _ _ _ (by rw [P.hH.hB]; omega)]


/-! ## HMAC's states for the key -/

/-- A state's representation, kept by memory that changed apart from it. -/
theorem repr_keep (P : Kit) {m m' : Mem} {ws : List Region} (hf : Frame ws m m') {p : Addr}
    (hd : ∀ r ∈ ws, Region.Disjoint ⟨p, P.H.S⟩ r) {msg : List Byte} (hr : P.hH.SH.Repr m p msg) :
    P.hH.SH.Repr m' p msg :=
  P.hH.congr m m' p msg (fun i hi => Frame.bytes (R := ⟨p, P.H.S⟩) hf hd (by have := P.hS; show P.H.S ≤ 2 ^ 64; omega)
    hi) hr

/-- The key survives what HMAC changes. -/
theorem keyOf_hm (P : Kit) (hL : L.Ok) {m m' : Mem} (hf : Frame [hmacScr L, ⟨L.B, 96⟩] m m') :
    keyOf P L m' = keyOf P L m :=
  bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have := hL.stk_scr (d := 128) (n := P.H.D) (e := 0) (k := 2256) (by have := L.e_le; nums) (by omega)
      rwa [BitVec.add_zero] at this
    · exact Offset.disjoint_base _ (by omega) (by have := hL.nB; nums)) (by nums)

/-- After `hinit`: HMAC's states for the key `K` in the frame on entry `t`. -/
structure Inited (P : Kit) (L : Lay dn) (g : Reg → BitVec 64) (lr : Addr) (m₀ : Mem) (t u : State) : Prop where
  ctx : Ctx L g lr m₀ u
  frame : Frame [hmacScr L, ⟨L.B, 96⟩] t.mem u.mem
  inner : P.hH.SH.Repr u.mem (L.scr + BitVec.ofNat 64 0)
    (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.hH.SH.H (keyOf P L t.mem)) Spec.Hmac.ipad)
  outer : P.hH.SH.Repr u.mem (L.scr + BitVec.ofNat 64 192)
    (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.hH.SH.H (keyOf P L t.mem)) Spec.Hmac.opad)
  sy : u.syms = t.syms

theorem xorPad_length (k : List Byte) (p : Byte) : (Spec.Hmac.xorPad k p).length = k.length :=
  List.length_map _

theorem keyOf_length (P : Kit) (m : Mem) : (keyOf P L m).length = P.H.D := by simp [keyOf, Spec.Sha256.bytesAt]

theorem blockKey_length (P : Kit) {k : List Byte} (hk : k.length ≤ P.H.B) :
    (Spec.Hmac.blockKey P.hH.SH.H k).length = P.H.B := by
  have hB := P.hH.hB
  simp only [Spec.Hmac.blockKey, hB, show ¬ P.H.B < k.length by omega, ite_false, List.length_append,
    List.length_replicate]
  omega

theorem keyBlock_length (P : Kit) (m : Mem) (c : Byte) :
    (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.hH.SH.H (keyOf P L m)) c).length = P.H.B := by
  rw [xorPad_length, blockKey_length P (by rw [keyOf_length]; exact P.hH.hDB)]

/-- The padded key, as `update` reads it at `scratch + sPad`. -/
theorem padData (P : Kit) (hL : L.Ok) {o : Nat} (ho : o + 192 ≤ 384) :
    UpdData P L o (L.scr + BitVec.ofNat 64 1792) P.H.B where
  cov := ⟨L.SCR, by simp, within_off _ (by nums)⟩
  st := Offset.disjoint _ (by nums) (by have := hL.nc; nums) (by have := hL.nc; nums)
  wk := Offset.disjoint _ (by nums) (by have := hL.nc; nums) (by have := hL.nc; nums)
  low := hL.stk_scr (by omega) (by nums)

theorem frame_hm {m m' : Mem} {ws : List Region} (hf : Frame ws m m')
    (h : ∀ r ∈ ws, ∃ r' ∈ [hmacScr L, ⟨L.B, 96⟩], Region.Sub r r') : Frame [hmacScr L, ⟨L.B, 96⟩] m m' :=
  hf.sub h

/-- `hinit`: each state set by `init` and updated with its padded key. -/
theorem init_step (P : Kit) {c : Cfg} (hK : KOk P c L) (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t)
    (hy : SyOk L m₀ t) : WP isa c.hinit t (Inited P L g lr m₀ t) := by
  have hnc := hL.nc
  have hS : P.H.S ≤ 192 := P.hS
  have hW := P.hW
  simp only [sWork, sPad] at hW
  have dS : ∀ {a b : Nat}, a + 192 ≤ b ∨ b + 192 ≤ a → b + 192 ≤ 8192 → a + 192 ≤ 8192 →
      Region.Disjoint ⟨L.scr + BitVec.ofNat 64 a, P.H.S⟩ ⟨L.scr + BitVec.ofNat 64 b, P.H.S⟩ :=
    fun h hb ha => Offset.disjoint _ (by omega) (by omega) (by omega)
  have dL : ∀ {a : Nat}, a + 192 ≤ 384 → Region.Disjoint ⟨L.scr + BitVec.ofNat 64 a, P.H.S⟩ ⟨L.B + BitVec.ofNat 64 48, 48⟩ :=
    fun h => (hL.stk_scr (by omega) (by omega)).symm
  have dP : ∀ {a : Nat}, a + 192 ≤ 384 →
      Region.Disjoint ⟨L.scr + BitVec.ofNat 64 a, P.H.S⟩ ⟨L.scr + BitVec.ofNat 64 1792, P.H.B⟩ :=
    fun h => Offset.disjoint _ (by nums) (by nums) (by nums)
  have dW : ∀ {a : Nat}, a + 192 ≤ 384 →
      Region.Disjoint ⟨L.scr + BitVec.ofNat 64 a, P.H.S⟩ ⟨L.scr + BitVec.ofNat 64 384, P.H.W⟩ :=
    fun h => Offset.disjoint _ (by omega) (by omega) (by omega)
  have hdA : ∀ u, Ctx L g lr m₀ u → u.gpr .r12 = L.scr → WP isa (.block [.addi .r5 .r12 sPad]) u fun u' =>
      Kp [.r5] u u' ∧ u'.mem = u.mem ∧ u'.gpr .r5 = L.scr + BitVec.ofNat 64 1792 :=
    fun u _ h12 => dataS_ok u h12 (o := 1792) (by decide)
  unfold Cfg.hinit
  rw [hK.B]
  refine WP.seq (WP.mono (initCall_ok P hK hL hc hy (o := 0) (by decide)) fun u₁ ⟨hc₁, hf₁, hr₁, hs₁⟩ => ?_)
  refine WP.seq (WP.mono (initCall_ok P hK hL hc₁ (hy.of_syms hs₁) (o := 192) (by decide))
    fun u₂ ⟨hc₂, hf₂, hr₂, hs₂⟩ => ?_)
  have hr₁' := repr_keep P hf₂ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dS (.inl (by decide)) (by decide) (by decide)
    · exact dL (by decide)) hr₁
  have hF₂ : Frame [hmacScr L, ⟨L.B, 96⟩] t.mem u₂.mem :=
    (frame_hm hf₁ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sub_hm (by nums)
      · exact low_hm).trans (frame_hm hf₂ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sub_hm (by nums)
      · exact low_hm)
  have hk₂ : keyOf P L u₂.mem = keyOf P L t.mem := keyOf_hm P hL hF₂
  have hp₃ := padBlk_ok P hK hL hc₂ Spec.Hmac.ipad
  rw [← ipad32_eq] at hp₃
  refine WP.seq (WP.mono_syms hp₃ fun u₃ ⟨hc₃, hf₃, hb₃⟩ hs₃ => ?_)
  have hr₁₃ := repr_keep P hf₃ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dP (by decide)) hr₁'
  have hr₂₃ := repr_keep P hf₃ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dP (by decide)) hr₂
  have hy₃ : SyOk L m₀ u₃ := hy.of_syms (hs₃.trans (hs₂.trans hs₁))
  refine WP.seq (WP.mono (updCall_ok P hK hL hc₃ hy₃ (o := 0) (cnt := 0) (by decide) hdA (padData P hL (by decide))
    (by decide) (by nums) hr₁₃ rfl) fun u₄ ⟨hc₄, hf₄, hr₄, hs₄⟩ => ?_)
  have hr₂₄ := repr_keep P hf₄ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact dS (.inr (by decide)) (by decide) (by decide)
    · exact dW (by decide)
    · exact dL (by decide)) hr₂₃
  have hF₄ : Frame [hmacScr L, ⟨L.B, 96⟩] t.mem u₄.mem :=
    (hF₂.trans (frame_hm hf₃ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact sub_hm (by nums))).trans (frame_hm hf₄ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub_hm (by nums)
      · exact sub_hm (by nums)
      · exact low_hm)
  have hk₄ : keyOf P L u₄.mem = keyOf P L t.mem := keyOf_hm P hL hF₄
  have hp₅ := padBlk_ok P hK hL hc₄ Spec.Hmac.opad
  rw [← opad32_eq] at hp₅
  refine WP.seq (WP.mono_syms hp₅ fun u₅ ⟨hc₅, hf₅, hb₅⟩ hs₅ => ?_)
  have hr₁₅ := repr_keep P hf₅ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dP (by decide)) hr₄
  have hr₂₅ := repr_keep P hf₅ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dP (by decide)) hr₂₄
  have hy₅ : SyOk L m₀ u₅ := hy₃.of_syms (hs₅.trans hs₄)
  refine WP.mono (updCall_ok P hK hL hc₅ hy₅ (o := 192) (cnt := 0) (by decide) hdA (padData P hL (by decide))
    (by decide) (by nums) hr₂₅ rfl) fun u₆ ⟨hc₆, hf₆, hr₆, hs₆⟩ => ?_
  have hr₁₆ := repr_keep P hf₆ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact dS (.inl (by decide)) (by decide) (by decide)
    · exact dW (by decide)
    · exact dL (by decide)) hr₁₅
  refine ⟨hc₆, (hF₄.trans (frame_hm hf₅ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact sub_hm (by nums))).trans (frame_hm hf₆ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub_hm (by nums)
      · exact sub_hm (by nums)
      · exact low_hm), ?_, ?_, by rw [hs₆, hs₅, hs₄, hs₃, hs₂, hs₁]⟩
  · rw [List.nil_append, hb₃, hk₂] at hr₁₆; exact hr₁₆
  · rw [List.nil_append, hb₅, hk₄] at hr₆; exact hr₆

/-! ## The data -/

/-- Where the data may be: in the frame's `K`, `V` and `h`, or in `scratch`
above HMAC's working space. -/
def DataOk (L : Lay dn) (da : Addr) (len : Nat) : Prop :=
  (∃ o, da = L.B + BitVec.ofNat 64 o ∧ 128 ≤ o ∧ o + len ≤ 312) ∨
    (∃ o, da = L.scr + BitVec.ofNat 64 o ∧ 2256 ≤ o ∧ o + len ≤ 8192)

namespace DataOk

variable {da : Addr} {len : Nat}

/-- The data is apart from HMAC's part of `scratch`. -/
theorem scr (hd : DataOk L da len) (hL : L.Ok) {e k : Nat} (h : e + k ≤ 2256) :
    Region.Disjoint ⟨da, len⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ := by
  rcases hd with ⟨o, rfl, h₁, h₂⟩ | ⟨o, rfl, h₁, h₂⟩
  · exact hL.stk_scr (by omega) (by omega)
  · exact Offset.disjoint _ (by omega) (by have := hL.nc; omega) (by have := hL.nc; omega)

/-- The data is apart from the stack below the frame. -/
theorem low (hd : DataOk L da len) (hL : L.Ok) {e k : Nat} (h : e + k ≤ 96) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 e, k⟩ ⟨da, len⟩ := by
  rcases hd with ⟨o, rfl, h₁, h₂⟩ | ⟨o, rfl, h₁, h₂⟩
  · exact Offset.disjoint _ (by omega) (by have := hL.nB; omega) (by have := hL.nB; omega)
  · exact hL.stk_scr (by omega) (by omega)

theorem within (hd : DataOk L da len) : ∃ R ∈ [L.D, L.DG, L.FR, L.OUT, L.SCR], Within ⟨da, len⟩ R := by
  rcases hd with ⟨o, rfl, h₁, h₂⟩ | ⟨o, rfl, h₁, h₂⟩
  · exact ⟨L.FR, by simp, within_fr _ h₁ (by omega)⟩
  · exact ⟨L.SCR, by simp, within_off _ h₂⟩

theorem len_le (hd : DataOk L da len) : len ≤ 8192 := by
  rcases hd with ⟨o, rfl, h₁, h₂⟩ | ⟨o, rfl, h₁, h₂⟩ <;> omega

theorem upd (P : Kit) (hL : L.Ok) (hd : DataOk L da len) : UpdData P L 0 da len where
  cov := hd.within
  st := hd.scr hL (by nums)
  wk := hd.scr hL (by nums)
  low := hd.low hL (by omega)

/-- The data survives what HMAC changes. -/
theorem keep (hL : L.Ok) (hd : DataOk L da len) {m m' : Mem} (hf : Frame [hmacScr L, ⟨L.B, 96⟩] m m') :
    Spec.Sha256.bytesAt m' da len = Spec.Sha256.bytesAt m da len :=
  bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa using hd.scr hL (e := 0) (k := 2256) (by omega)
    · simpa using (hd.low hL (e := 0) (k := 96) (by omega)).symm) (by have := hd.len_le; omega)

end DataOk

/-- After `hupd`: the inner state holds the data too. -/
structure Updated (P : Kit) (L : Lay dn) (g : Reg → BitVec 64) (lr : Addr) (m₀ : Mem) (t : State) (da : Addr)
    (len : Nat) (u : State) : Prop where
  ctx : Ctx L g lr m₀ u
  frame : Frame [hmacScr L, ⟨L.B, 96⟩] t.mem u.mem
  inner : P.hH.SH.Repr u.mem (L.scr + BitVec.ofNat 64 0)
    (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.hH.SH.H (keyOf P L t.mem)) Spec.Hmac.ipad ++
      Spec.Sha256.bytesAt t.mem da len)
  outer : P.hH.SH.Repr u.mem (L.scr + BitVec.ofNat 64 192)
    (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.hH.SH.H (keyOf P L t.mem)) Spec.Hmac.opad)
  sy : u.syms = t.syms

theorem upd_step (P : Kit) {c : Cfg} (hK : KOk P c L) (hL : L.Ok) {t u : State} (hu : Inited P L g lr m₀ t u)
    (hy : SyOk L m₀ t) {dataA : List Instr} {da : Addr} {len : Nat}
    (hdA : ∀ u, Ctx L g lr m₀ u → u.gpr .r12 = L.scr → WP isa (.block dataA) u fun u' =>
      Kp [.r5] u u' ∧ u'.mem = u.mem ∧ u'.gpr .r5 = da)
    (hd : DataOk L da len) (hlen : len ≤ 256) :
    WP isa (c.hupd dataA len) u (Updated P L g lr m₀ t da len) := by
  have hnc := hL.nc
  unfold Cfg.hupd
  rw [hK.B]
  refine WP.mono (updCall_ok P hK hL hu.ctx (hy.of_syms hu.sy) (o := 0) (cnt := P.H.B) (by decide) hdA (hd.upd P hL)
    (by rcases P.hH.dims.B with h | h <;> omega) (by omega) hu.inner (keyBlock_length P _ _))
    fun w ⟨hcw, hfw, hrw, hsw⟩ => ?_
  refine ⟨hcw, hu.frame.trans (frame_hm hfw fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub_hm (by nums)
      · exact sub_hm (by nums)
      · exact low_hm), by rw [← hd.keep hL hu.frame]; exact hrw, repr_keep P hfw (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint _ (by nums) (by nums) (by nums)
    · exact Offset.disjoint _ (by nums) (by nums) (by nums)
    · exact (hL.stk_scr (by omega) (by nums)).symm) hu.outer, hsw.trans hu.sy⟩

/-! ## The MAC -/

/-- After `hfin`: the MAC in the frame at `dst`. -/
structure Macd (P : Kit) (L : Lay dn) (g : Reg → BitVec 64) (lr : Addr) (m₀ : Mem) (t : State) (da : Addr)
    (len dst : Nat) (u : State) : Prop where
  ctx : Ctx L g lr m₀ u
  frame : Frame [hmacScr L, ⟨L.B, 96⟩, ⟨L.B + BitVec.ofNat 64 (96 + dst), P.H.D⟩] t.mem u.mem
  mac : Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (96 + dst)) P.H.D =
    Spec.Hmac.hmac P.hH.SH.H (keyOf P L t.mem) (Spec.Sha256.bytesAt t.mem da len)
  sy : u.syms = t.syms

theorem fin_step (P : Kit) {c : Cfg} (hK : KOk P c L) (hL : L.Ok) {t u : State} {da : Addr} {len dst : Nat}
    (hu : Updated P L g lr m₀ t da len u) (hy : SyOk L m₀ t) (hlen : len ≤ 256) (hdst : 32 ≤ dst ∧ dst + 64 ≤ 216) :
    WP isa (c.hfin len dst) u (Macd P L g lr m₀ t da len dst) := by
  have hnc := hL.nc
  have hnB := hL.nB
  have hB : P.H.B ≤ 128 := by rcases P.hH.dims.B with h | h <;> omega
  have hkl := keyBlock_length P (L := L) t.mem Spec.Hmac.ipad
  have hko := keyBlock_length P (L := L) t.mem Spec.Hmac.opad
  have hdl : (Spec.Sha256.bytesAt t.mem da len).length = len := by simp [Spec.Sha256.bytesAt]
  unfold Cfg.hfin
  rw [hK.B, hK.D]
  refine WP.seq (WP.mono (finCall_ok P hK hL hu.ctx (hy.of_syms hu.sy) (o := 0) (by decide) (cnt := P.H.B + len)
    (by omega) hu.inner (by rw [List.length_append, hkl, hdl])) fun w₁ ⟨hc₁, hf₁, hd₁, hs₁⟩ => ?_)
  have ho₁ := repr_keep P hf₁ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Offset.disjoint _ (by nums) (by nums) (by nums)
    · exact Offset.disjoint _ (by nums) (by nums) (by nums)
    · exact Offset.disjoint _ (by nums) (by nums) (by nums)
    · exact (hL.stk_scr (by omega) (by nums)).symm) hu.outer
  have tmpD : UpdData P L 192 (L.scr + BitVec.ofNat 64 1920) P.H.D :=
    ⟨⟨L.SCR, by simp, within_off _ (by nums)⟩, Offset.disjoint _ (by nums) (by nums) (by nums),
      Offset.disjoint _ (by nums) (by nums) (by nums), hL.stk_scr (by omega) (by nums)⟩
  have hy₁ : SyOk L m₀ w₁ := hy.of_syms (hs₁.trans hu.sy)
  refine WP.seq (WP.mono (updCall_ok P hK hL hc₁ hy₁ (o := 192) (cnt := P.H.B) (by decide)
    (fun u _ h12 => dataS_ok u h12 (o := 1920) (by decide)) tmpD (by omega) (by nums) ho₁ hko)
    fun w₂ ⟨hc₂, hf₂, hr₂, hs₂⟩ => ?_)
  rw [hd₁] at hr₂
  refine WP.seq (WP.mono (finCall_ok P hK hL hc₂ (hy₁.of_syms hs₂) (o := 192) (by decide) (cnt := P.H.B + P.H.D)
    (by nums) hr₂ (by rw [List.length_append, hko, P.hH.hashLen])) fun w₃ ⟨hc₃, hf₃, hd₃, hs₃⟩ => ?_)
  refine WP.of_syms ?_
  rw [WP.block_append_iff]
  refine WP.mono (scrBase_ok hL hc₃) fun w₄ ⟨hc₄, hm₄, k₄, b₄, s₄⟩ => ?_
  have e4 : 4 * (P.H.D / 4) = P.H.D := by have := P.hH.hD4; omega
  have hsep : Region.Disjoint ⟨L.scr + BitVec.ofNat 64 1920, 4 * (P.H.D / 4)⟩
      ⟨L.B + BitVec.ofNat 64 96 + BitVec.ofNat 64 dst, 4 * (P.H.D / 4)⟩ := by
    rw [fr_add]; exact (hL.stk_scr (by nums) (by nums)).symm
  refine WP.mono (copyW_ok (src := .r12) (dst := .r11) (S := L.scr) (D := L.B + BitVec.ofNat 64 96)
    (so := 1920) (d := dst) (K := P.H.D / 4) (by decide) (by decide) (by decide) (by decide) hsep (by nums)
    (by nums) (by nums) (P.H.D / 4) (Nat.le_refl _) w₄ s₄ b₄ (fun j hj => hc₄.inScr (by nums))
    (fun j hj => by rw [fr_add]; have := P.hH.hD64; exact hc₄.inFrW (by omega) (by omega)))
    fun w₅ ⟨k₅, hf₅, hb₅⟩ hs₅ => ?_
  rw [fr_add, e4] at hf₅ hb₅
  refine ⟨hc₄.keep hL k₅.rd k₅.wr k₅.sp (fun r hr => k₅.gpr r fun h => by
      simp only [List.mem_singleton] at h; subst h; simp [preserved] at hr) hf₅
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by nums)), ?_, ?_, ?_⟩
  · have e : ∀ {r : Region}, (∃ r' ∈ [hmacScr L, ⟨L.B, 96⟩], Region.Sub r r') →
        ∃ r' ∈ [hmacScr L, ⟨L.B, 96⟩, ⟨L.B + BitVec.ofNat 64 (96 + dst), P.H.D⟩], Region.Sub r r' :=
      fun ⟨r', hr', hs⟩ => ⟨r', by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr' ⊢; rcases hr' with h | h <;> simp [h], hs⟩
    have fh : ∀ {o : Nat}, o + 192 ≤ 384 → ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 o, P.H.S⟩ : Region),
        ⟨L.scr + BitVec.ofNat 64 1920, P.H.FD⟩, ⟨L.scr + BitVec.ofNat 64 384, P.H.W⟩,
        ⟨L.B + BitVec.ofNat 64 48, 48⟩], ∃ r' ∈ [hmacScr L, ⟨L.B, 96⟩], Region.Sub r r' := fun ho r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact sub_hm (by nums)
      · exact sub_hm (by nums)
      · exact sub_hm (by nums)
      · exact low_hm
    refine ((((hu.frame.sub fun r hr => e ⟨r, hr, fun _ h => h⟩).trans (hf₁.sub fun r hr => e (fh (by decide) r hr))).trans
      (hf₂.sub fun r hr => e ?_)).trans (hf₃.sub fun r hr => e (fh (by decide) r hr))).trans ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub_hm (by nums)
      · exact sub_hm (by nums)
      · exact low_hm
    · rw [← hm₄]; exact hf₅.sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩
  · rw [hb₅, hm₄, hd₃]
    rfl
  · rw [hs₅, hs₃, hs₂, hs₁, hu.sy]

/-! ## The whole HMAC -/

/-- `HMAC_K(data)`, for the key `K` in the frame, to the frame at `dst`. -/
theorem hmac_ok (P : Kit) {c : Cfg} (hK : KOk P c L) (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t)
    (hy : SyOk L m₀ t) {dataA : List Instr} {da : Addr} {len dst : Nat} (hd : DataOk L da len) (hlen : len ≤ 256)
    (hdst : 32 ≤ dst ∧ dst + 64 ≤ 216)
    (hdA : ∀ u, Ctx L g lr m₀ u → u.gpr .r12 = L.scr → WP isa (.block dataA) u fun u' =>
      Kp [.r5] u u' ∧ u'.mem = u.mem ∧ u'.gpr .r5 = da) :
    WP isa (c.hmac dataA len dst) t (Macd P L g lr m₀ t da len dst) :=
  WP.seq (WP.mono (init_step P hK hL hc hy) fun _ hu => WP.seq (WP.mono (upd_step P hK hL hu hy hdA hd hlen)
    fun _ hw => fin_step P hK hL hw hy hlen hdst))

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
