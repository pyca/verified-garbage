module

public import VerifiedGarbage.Proof.Ecdsa.X86.CombLays
public import VerifiedGarbage.Proof.Ecdsa.X86.CombTaint
import VerifiedGarbage.Proof.Weierstrass.X86.Rep
import VerifiedGarbage.Proof.Weierstrass.X86.TCombJ
import VerifiedGarbage.Proof.Weierstrass.X86.TCombRcb
import VerifiedGarbage.Proof.Ecdsa.X86.Stages
import VerifiedGarbage.Proof.Ecdsa.X86.Lays
import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Proof.Framework.X86.CallBody
import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Weierstrass.X86.CallOps

/-!
# ECDSA on x86 (32-bit): `[k]G`

`Cfg.gMul` is the comb for a curve with one (with Booth's digits and
Jacobian additions, or by complete additions), else the ladder; each leaves
`R = [k]G`, from the table of `k`'s bits, changing only the slots and word of
`gW` (`gMul_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass

variable {c : Cfg}

/-- What `[k]G` may write, by the comb (with `b R mod p` in `EM`) or the
ladder: their slots and the word past the table of `k`'s bits. -/
abbrev gW (c : Cfg) : List (Nat × Nat) :=
  slW c [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP, EM] ++
    (wkW c ++ [(bitsAt c.n 0 + 64 * c.n, 4)])

/-- A slot is apart from the word past the table of `k`'s bits. -/
theorem apart_pad {i : Nat} (hi : i < 45) (hn : c.n < 10 := by n10) :
    ∀ w ∈ [(bitsAt c.n 0 + 64 * c.n, 4)], c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  intro w hw
  rw [List.mem_singleton.mp hw]
  exact Or.inl (sl_below_bits c hi 0 _)

/-- A slot apart from what `[k]G` writes. -/
theorem apart_gW {i : Nat} (hi : i < 45)
    (hl : i ∉ [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP, EM])
    (hn : c.n < 10 := by n10) :
    ∀ w ∈ gW c, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i :=
  apart_append (apart_slW hl) (apart_append (apart_wk hi) (apart_pad hi))

theorem fixedOk_gW (hn : c.n < 10 := by n10) : FixedOk c (gW c) := by
  refine (fixedOk_slW (by decide)).append ((fixedOk_wk (hn := hn)).append ?_)
  intro w hw
  rw [List.mem_singleton.mp hw]
  exact Or.inr (Nat.le_trans (Nat.le_add_right _ _) (sl_below_bits c (by decide) 0 _))

/-- Tables `1` and `2` are apart from what `[k]G` writes. -/
theorem tbl_apart_gW {j t : Nat} (hj : j = 1 ∨ j = 2) (ht : t < 64 * c.n) (hn : c.n < 10 := by n10) :
    ∀ w ∈ gW c, bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t := by
  refine apart_append (tbl_apart_slW (by decide) j t)
    (apart_append (tbl_apart_wk (by omega_using [hj]) ht) ?_)
  intro w hw
  rw [List.mem_singleton.mp hw]
  simp only [bitsAt_eq]
  rcases hj with rfl | rfl <;> exact Or.inr (by omega_using [])

/-- The flag word apart from what `[k]G` writes. -/
theorem flag_unch_gW {base : Addr} {m m' : Mem} (hu : Unch base (gW c) m m')
    (h7 : c.n < 10) (h0 : 0 < c.n) (hn : base.toNat + size ≤ 2 ^ 32) :
    m'.readW (off base (c.sl FLAG)) 32 = m.readW (off base (c.sl FLAG)) 32 := by
  have hF := sl_le c h7 (i := FLAG) (by decide)
  refine Unch.readW32 hu (fun w hw => ?_) (by omega_using [hn, hF])
  rcases (apart_gW (c := c) (i := FLAG) (by decide) (by decide)) w hw with h | h
  · exact Or.inl (by omega_using [h0, h])
  · exact Or.inr h

/-- Prepare the comb's Montgomery constant (`b`, or `3b`: `x`) and retain its public table
pointer. -/
theorem combPrepare_ok (hc : CfgOk c) {d : CombData} (hcd : c.comb = some d) (x : Nat)
    {base : Addr} {g : Reg → BitVec 32} {s : State} {k : Nat}
    (hs : Scr s base size) (F : Fixed c base g s.mem) (hkl : k < 2 ^ (64 * c.n))
    (ht₀ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 0 + t)) = if k.testBit t then 1 else 0)
    (hTM : TblMem s ((g .eax).setWidth 64) (c.combWords d))
    (hout : ∀ i < (c.combWords d).length, ∀ b < 8,
      size ≤ ofs base ((g .eax).setWidth 64 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b))
    (hap : ∀ r ∈ s.wr ++ [below (s.gpr .esp) 20],
      Region.Disjoint ⟨(g .eax).setWidth 64, 8 * (c.combWords d).length⟩ r)
    (hsp : 20 ≤ (s.gpr .esp).toNat) :
    WP isa (.block (setConst c.n (c.sl EM) (c.mont x))) s fun s₁ =>
      Keeps [.eax] s s₁ ∧ Scr s₁ base size ∧ ModOkW c.MP' size c.C.p s₁.mem base ∧
      TCombFixed (c.combCfg d) c.C base size s₁ k ((g .eax).setWidth 64) (c.combWords d) ∧
      Unch base (slW c [EM]) s.mem s₁.mem ∧ sv c base s₁ EM = c.mont x := by
  have h7 := hc.n10
  have hn := hs.nowrap
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by have := hc.p_ge; omega_using [this])
  have hp3 := hc.p_ge
  refine WP.mono (setConst_ok hs (n := c.n) (o := c.sl EM) (x := c.mont x)
    (sl_le c h7 (by decide)) (by have := hc.p_lt; have := hmont x; omega_arith))
    fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have F₁ := F.unch h7 hn (fixedOk_slW (l := [EM]) (by decide)) O₁.unch
  have ht₁ : ∀ t < 64 * c.n, s₁.mem (off base (bitsAt c.n 0 + t)) = if k.testBit t then 1 else 0 :=
    fun t ht => by
      rw [tbl_unch (W := slW c [EM]) O₁.unch h7 (j := 0) (by decide) ht (tbl_apart_slW (by decide) 0 t)]
      exact ht₀ t ht
  have hTM₁ : TblMem s₁ ((g .eax).setWidth 64) (c.combWords d) :=
    hTM.of_unch (by rw [k₁.2.1, k₁.2.2]) O₁.unch (fun w hw => by
      rw [List.mem_singleton.mp hw]; exact sl_le c h7 (by decide)) hout
  have hF : TCombFixed (c.combCfg d) c.C base size s₁ k ((g .eax).setWidth 64)
      (tcombWords (c.combCfg d).M.n (2 ^ (64 * (c.combCfg d).M.n)) c.C.p d.tbl) := by
    refine ⟨?_, fun y hy => ?_, F₁.zero, ht₁, hkl, ?_, hTM₁, hout,
      by rw [k₁.2.2, k₁.1 _ (by decide)]; exact hap, by rw [k₁.1 _ (by decide)]; exact hsp⟩
    · show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₁.mem _ (c.sl AP) c.n) = _
      rw [F₁.ap]; exact toM_cmont hc _
    · simp only [combRo, TCombCfg.toComb, Cfg.combCfg, Cfg.rcbSlots, List.mem_cons, List.not_mem_nil,
        or_false] at hy
      rcases hy with rfl | rfl | rfl
      · exact lt_of_eq_of_lt F₁.ap (hmont _)
      · exact lt_of_eq_of_lt e₁ (hmont _)
      · exact lt_of_eq_of_lt F₁.zero (by omega_using [hp3])
    · change (s₁.mem.readW (off base Cfg.combPtr) 32).setWidth 64 = _
      rw [F₁.table (by simp [hcd])]
  exact ⟨k₁, hs₁, modP_of hc F₁.mp, hF, O₁.unch, e₁⟩

/-- The comb's code (`Cfg.combBody`, the body of `vg_<curve>_comb`): `R = [k]G`
from the table of `k`'s bits and the comb's tables. -/
theorem combBody_ok (hc : CfgOk c) (hC : Law c.C) (hT : CombTbls c) {d : CombData}
    (hcd : c.comb = some d) (hd : CombOk c d) {base : Addr} {g : Reg → BitVec 32}
    {s : State} (hs : Scr s base size) (F : Fixed c base g s.mem) {k : Nat} (hkl : k < 2 ^ (64 * c.n))
    (ht₀ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 0 + t)) = if k.testBit t then 1 else 0)
    (hTM : TblMem s ((g .eax).setWidth 64) (c.combWords d))
    (hout : ∀ i < (c.combWords d).length, ∀ b < 8,
      size ≤ ofs base ((g .eax).setWidth 64 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b))
    (hap : ∀ r ∈ s.wr ++ [below (s.gpr .esp) 20],
      Region.Disjoint ⟨(g .eax).setWidth 64, 8 * (c.combWords d).length⟩ r)
    (hsp20 : 20 ≤ (s.gpr .esp).toNat) (hsp : SpOk (c.combBody d) 20) :
    WP isa (c.combBody d) s fun s' => Keeps (powClob) s s' ∧ Unch base (gW c) s.mem s'.mem ∧
      ModOkW c.MP' size c.C.p s'.mem base ∧
      (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s'.mem base x c.n < c.C.p) ∧
      Rep c.C (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY))
        (tmv c.C c.n base s' (c.sl RZ)) (mul k (G c.C)) := by
  have h7 := hc.n10
  have hp3 := hc.p_ge
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega_using [hp3])
  unfold Cfg.combBody at hsp ⊢
  have hn := hs.nowrap
  -- What the comb and the constant in `EM` write is `[k]G`'s to write.
  have cover : ∀ {m₁ m' : Mem}, Unch base (slW c [EM]) s.mem m₁ →
      Unch base (slW c [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP] ++
        wkW c ++ [(bitsAt c.n 0 + 64 * c.n, 4)]) m₁ m' → Unch base (gW c) s.mem m' := by
    intro m₁ m' U₁ U'
    refine Unch.cover (U₁.trans U') fun w hw => ?_
    rcases List.mem_append.mp hw with hw | hw
    · rw [List.mem_singleton.mp hw]
      exact ⟨_, List.mem_append_left _ (List.mem_map_of_mem (f := fun i => (c.sl i, 8 * c.n))
        (show EM ∈ [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP, EM] by decide)),
        Nat.le_refl _, Nat.le_refl _⟩
    rcases List.mem_append.mp hw with hw | hw
    · rcases List.mem_append.mp hw with hw | hw
      · have sub : ∀ i ∈ [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP],
            i ∈ [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP, EM] := by decide
        exact ⟨w, List.mem_append_left _ (List.map_subset _ sub hw), Nat.le_refl _, Nat.le_refl _⟩
      · exact ⟨w, List.mem_append_right _ (List.mem_append_left _ hw), Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨w, List.mem_append_right _ (List.mem_append_right _ hw), Nat.le_refl _, Nat.le_refl _⟩
  have hkeep : ∀ {s₁ : State}, Keeps [.eax] s s₁ → Keeps powClob s s₁ := fun k₁ =>
    k₁.mono fun r hr => by rw [List.mem_singleton.mp hr]; simp [powClob, clob]
  by_cases hjac : d.jac = true
  · -- Booth's digits and Jacobian additions, with `b R mod p` in `EM`.
    rw [ite_eq_left hjac] at hsp ⊢
    refine WP.seq (WP.mono (combPrepare_ok hc hcd c.C.b hs F hkl ht₀ hTM hout hap hsp20)
      fun s₁ ⟨k₁, hs₁, M₁, hF, U₁, _⟩ => ?_)
    refine WP.mono (tcombJ_ok (tcombLay hc hd) hC ((hT d hcd).2 hjac).2 hc.onG
      (tcombVals hc hC (hT d hcd).1) hc.p_lt
      (by show 1 ≤ bitsAt c.n 0; rw [bitsAt_eq]; omega_using []) ((hT d hcd).2 hjac).1 hkl hs₁
      M₁ hF hsp.right) fun s' ⟨K', U', M', L', R'⟩ => ⟨(hkeep k₁).trans K', ?_, M', L', R'⟩
    change Unch base ((slW c [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP] ++
      wkW c) ++ [(bitsAt c.n 0 + 64 * c.n, 4 * (c.combCfg d).zw)]) s₁.mem s'.mem at U'
    have hz := zw_le hd hjac
    refine cover U₁ (Unch.cover U' fun w hw => ?_)
    rcases List.mem_append.mp hw with hw | hw
    · exact ⟨w, List.mem_append_left _ hw, Nat.le_refl _, Nat.le_refl _⟩
    · rw [List.mem_singleton.mp hw]
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), Nat.le_refl _,
        by dsimp only; omega_using [hz]⟩
  · -- Complete additions, with `3b R mod p` in `EM`.
    have htop := hd.top (Bool.not_eq_true _ ▸ hjac)
    rw [ite_eq_right hjac] at hsp ⊢
    refine WP.seq (WP.mono (combPrepare_ok hc hcd (3 * c.C.b) hs F hkl ht₀ hTM hout hap hsp20)
      fun s₁ ⟨k₁, hs₁, M₁, hF, U₁, e₁⟩ => ?_)
    refine WP.mono (comb_ok (tcombLay hc hd) ⟨htop.1, htop.2⟩ hC hc.onG
      (tcombVals hc hC (hT d hcd).1) hc.p_lt hs₁ M₁ hF (by
        show toM c.C.p (2 ^ (64 * c.n)) (sv c base s₁ EM) = _
        rw [e₁]; exact toM_cmont hc _) hsp.right)
      fun s' ⟨K', U', M', L', R'⟩ => ⟨(hkeep k₁).trans K', ?_, M', L', R'⟩
    change Unch base (slW c [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP] ++
      wkW c) s₁.mem s'.mem at U'
    exact cover U₁ (U'.mono fun w hw => List.mem_append_left _ hw)


/-- The return address a call stores, apart from the stack its callee's
calls use. -/
theorem ret_below_disjoint {sp : BitVec 32} (h : 24 ≤ sp.toNat) :
    Region.Disjoint (below sp 4) (below (sp - BitVec.ofNat 32 4) 20) := by
  intro a h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  have hb := sp.isLt
  have e₁ : ((sp - BitVec.ofNat 32 4).setWidth 64).toNat = sp.toNat - 4 := by
    rw [BitVec.toNat_setWidth, X86.sub_toNat (by omega_using [h])]
    exact Nat.mod_eq_of_lt (by omega_using [hb])
  have e₂ : ((sp - BitVec.ofNat 32 4 - BitVec.ofNat 32 20).setWidth 64).toNat = sp.toNat - 24 := by
    have e : (sp - BitVec.ofNat 32 4).toNat = sp.toNat - 4 := X86.sub_toNat (by omega_using [h])
    rw [BitVec.toNat_setWidth, X86.sub_toNat (by omega_using [h, e]), e]
    exact Nat.mod_eq_of_lt (by omega_using [hb])
  rw [BitVec.toNat_sub, e₁] at h₁
  rw [BitVec.toNat_sub, e₂] at h₂
  have ha := a.isLt
  omega_using [h₁, h₂, h, hb, ha]

/-- What the comb reads, in the state a call of it leaves (`State.callEntry`),
whose return address is apart from the working space and the tables: and the
working space as it was. -/
theorem combEntry (hc : CfgOk c) {d : CombData} {base : Addr} {g : Reg → BitVec 32}
    {s : State} (hs : Scr s base size) (F : Fixed c base g s.mem) {k : Nat}
    (ht₀ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 0 + t)) = if k.testBit t then 1 else 0)
    (hTM : TblMem s ((g .eax).setWidth 64) (c.combWords d))
    (hap : ∀ r ∈ s.wr ++ [below (s.gpr .esp) 24],
      Region.Disjoint ⟨(g .eax).setWidth 64, 8 * (c.combWords d).length⟩ r)
    (hst : ∀ r ∈ s.wr, Region.Disjoint (below (s.gpr .esp) 24) r)
    (hsp24 : 24 ≤ (s.gpr .esp).toNat) :
    Scr s.callEntry base size ∧ Fixed c base g s.callEntry.mem ∧
      (∀ t < 64 * c.n, s.callEntry.mem (off base (bitsAt c.n 0 + t)) = if k.testBit t then 1 else 0) ∧
      TblMem s.callEntry ((g .eax).setWidth 64) (c.combWords d) ∧
      (∀ r ∈ s.callEntry.wr ++ [below (s.callEntry.gpr .esp) 20],
        Region.Disjoint ⟨(g .eax).setWidth 64, 8 * (c.combWords d).length⟩ r) ∧
      20 ≤ (s.callEntry.gpr .esp).toNat ∧ Unch base (wkW c) s.mem s.callEntry.mem := by
  have h7 := hc.n10
  have hn := hs.nowrap
  obtain e4 : (s.gpr .esp - 4 : BitVec 32) = s.gpr .esp - BitVec.ofNat 32 4 := rfl
  obtain hesp : (s.callEntry.gpr .esp).toNat = (s.gpr .esp).toNat - 4 := by
    rw [State.callEntry_esp, e4, sub_toNat (by omega_using [hsp24])]
  -- What the call stores: the return address, below `esp`.
  obtain fr : Frame [below (s.gpr .esp) 4] s.mem s.callEntry.mem :=
    Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _
      (by rw [e4]; exact below_top (k := 4) (Nat.le_refl _) (by omega_using [hsp24]) (Nat.le_refl _))
  obtain s4 : Region.Sub (below (s.gpr .esp) 4) (below (s.gpr .esp) 24) :=
    below_le_sub (by decide) hsp24
  obtain s20 : Region.Sub (below (s.callEntry.gpr .esp) 20) (below (s.gpr .esp) 24) := by
    rw [State.callEntry_esp, e4]; exact below_inner (by decide) hsp24
  obtain hws : Region.Disjoint (below (s.gpr .esp) 24) ⟨base, size⟩ := hst _ hs.wr
  obtain U₀ : Unch base (wkW c) s.mem s.callEntry.mem := fun x hx => fr x fun r hr hcx => by
    rw [List.mem_singleton.mp hr] at hcx
    have hx' := hx Mont.outW (by simp [wkW])
    have hlt : ofs base x < size := by
      have := (x - base).isLt
      have e : size = 8192 := rfl
      simp only [ofs] at hx' ⊢; omega_using [hx', this, e]
    exact hws x (s4 x hcx) (by simp only [Region.Contains]; simp only [ofs] at hlt; omega_using [hlt])
  -- The comb's view of the state the call leaves.
  obtain hs' : Scr s.callEntry base size :=
    ⟨by rw [State.callEntry_gpr _ (by decide)]; exact hs.edi, hs.wr, hn,
      stkOk_of (z := 20) (Nat.le_refl _) (by omega_using [hesp, hsp24]) hn (by decide) (by
        have := hws.sub_left s20
        simp only [below] at this
        rwa [VG.X86.Taint.sub_setWidth (by omega_using [hesp, hsp24])] at this)⟩
  obtain F' : Fixed c base g s.callEntry.mem := F.unch h7 hn fixedOk_wk U₀
  obtain ht' : ∀ t < 64 * c.n, s.callEntry.mem (off base (bitsAt c.n 0 + t)) =
      if k.testBit t then 1 else 0 := fun t ht => by
    rw [tbl_unch U₀ h7 (j := 0) (by decide) ht (tbl_apart_wk (by decide) ht)]; exact ht₀ t ht
  obtain hTM' : TblMem s.callEntry ((g .eax).setWidth 64) (c.combWords d) :=
    hTM.of_frame rfl fr fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact (hap _ (List.mem_append_right _ (List.mem_singleton_self _))).sub_right s4
  obtain hap' : ∀ r ∈ s.callEntry.wr ++ [below (s.callEntry.gpr .esp) 20],
      Region.Disjoint ⟨(g .eax).setWidth 64, 8 * (c.combWords d).length⟩ r := fun r hr => by
    rw [State.callEntry_wr] at hr
    rcases List.mem_append.mp hr with hr | hr
    · exact hap r (List.mem_append_left _ hr)
    · rw [List.mem_singleton.mp hr]
      exact (hap _ (List.mem_append_right _ (List.mem_singleton_self _))).sub_right s20
  exact ⟨hs', F', ht', hTM', hap', by omega_using [hesp, hsp24], U₀⟩

/-- A call of the comb (`vg_<curve>_comb`, `Cfg.gMul`): `combBody_ok`, from the
state the call leaves, whose return address is apart from the working space
and the tables, and which the comb leaves where it is. -/
theorem combCall_ok (hc : CfgOk c) (hC : Law c.C) (hT : CombTbls c) {d : CombData}
    (hcd : c.comb = some d) (hd : CombOk c d) {base : Addr} {g : Reg → BitVec 32}
    {s : State} (hs : Scr s base size) (F : Fixed c base g s.mem) {k : Nat} (hkl : k < 2 ^ (64 * c.n))
    (ht₀ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 0 + t)) = if k.testBit t then 1 else 0)
    (hTM : TblMem s ((g .eax).setWidth 64) (c.combWords d))
    (hout : ∀ i < (c.combWords d).length, ∀ b < 8,
      size ≤ ofs base ((g .eax).setWidth 64 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b))
    (hap : ∀ r ∈ s.wr ++ [below (s.gpr .esp) 24],
      Region.Disjoint ⟨(g .eax).setWidth 64, 8 * (c.combWords d).length⟩ r)
    (hst : ∀ r ∈ s.wr, Region.Disjoint (below (s.gpr .esp) 24) r)
    (hsp24 : 24 ≤ (s.gpr .esp).toNat) (hsp : SpOk (.call c.combName (c.combBody d)) 24) :
    WP isa (.call c.combName (c.combBody d)) s fun s' => Keeps (powClob) s s' ∧
      Unch base (gW c) s.mem s'.mem ∧
      ModOkW c.MP' size c.C.p s'.mem base ∧
      (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s'.mem base x c.n < c.C.p) ∧
      Rep c.C (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY))
        (tmv c.C c.n base s' (c.sl RZ)) (mul k (G c.C)) := by
  obtain ⟨hs', F', ht', hTM', hap', h20, U₀⟩ := combEntry hc hs F ht₀ hTM hap hst hsp24
  obtain e4 : (s.gpr .esp - 4 : BitVec 32) = s.gpr .esp - BitVec.ofNat 32 4 := rfl
  obtain s4 : Region.Sub (below (s.gpr .esp) 4) (below (s.gpr .esp) 24) :=
    below_le_sub (by decide) hsp24
  obtain hspB : SpOk (c.combBody d) 20 := ⟨fun i hi => hsp.1 i hi,
    Nat.le_of_add_le_add_right (show stackUse (c.combBody d) + 4 ≤ 20 + 4 from hsp.2)⟩
  refine WP.callBody (WP.mono (WP.withFrame hspB.1 hspB.2 h20
    (combBody_ok hc hC hT hcd hd hs' F' hkl ht' hTM' hout hap' h20 hspB))
    fun u ⟨⟨K, U, M, L, R⟩, fu⟩ => ?_)
  obtain huesp : u.gpr .esp = s.gpr .esp - 4 := by
    rw [K.1 .esp (by decide), State.callEntry_esp]
  refine ⟨huesp, ?_, ?_⟩
  · -- The return address is where the call stored it.
    obtain hc4 : (below (s.gpr .esp) 4).Contains ((s.gpr .esp - 4).setWidth 64) (32 / 8) := by
      rw [e4]; exact below_top (k := 4) (Nat.le_refl _) (by omega_using [hsp24]) (by decide)
    obtain hd4 : ∀ r ∈ s.callEntry.wr ++ [below (s.callEntry.gpr .esp) 20],
        (below (s.gpr .esp) 4).Disjoint r := fun r hr => by
      rw [State.callEntry_wr] at hr
      rcases List.mem_append.mp hr with hr | hr
      · exact (hst r hr).sub_left s4
      · rw [List.mem_singleton.mp hr, State.callEntry_esp, e4]; exact ret_below_disjoint hsp24
    rw [fu.readW hc4 hd4 (by decide), State.callEntry_mem, Mem.readW_writeW_self32]
  · refine ⟨⟨fun r hr => ?_, by rw [RegUpd.rd_setReg, K.2.1]; rfl, by rw [RegUpd.wr_setReg, K.2.2]; rfl⟩,
      ?_, M, L, R⟩
    · by_cases he : r = .esp
      · subst he; exact RegUpd.gpr_setReg_self _ _ _
      · rw [RegUpd.gpr_setReg_of_ne _ _ he, K.1 r hr, State.callEntry_gpr _ he]
    · rw [RegUpd.mem_setReg]
      refine Unch.cover (U₀.trans U) fun w hw => ⟨w, ?_, Nat.le_refl _, Nat.le_refl _⟩
      rcases List.mem_append.mp hw with hw | hw
      · exact List.mem_append_right _ (List.mem_append_left _ hw)
      · exact hw

/-- `R = [k]G`, by a call of the comb or by the ladder, from the table of `k`'s
bits, with `R = O` (for the ladder) and the comb's tables (`hTb`) where the
comb reads them, and the stack the call uses apart from the writable regions
(`hst`). -/
theorem gMul_ok' (hc : CfgOk c) (hC : Law c.C) (hT : CombTbls c)
    (hCo : ∀ d, c.comb = some d → CombOk c d) {base : Addr} {g : Reg → BitVec 32}
    {s : State} (hs : Scr s base size) (F : Fixed c base g s.mem) {k : Nat} (hkl : k < 2 ^ (64 * c.n))
    (hrx : sv c base s RX = 0) (hry : sv c base s RY = c.mont 1) (hrz : sv c base s RZ = 0)
    (ht₀ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 0 + t)) = if k.testBit t then 1 else 0)
    (hTb : ∀ d, c.comb = some d → TblMem s ((g .eax).setWidth 64) (c.combWords d) ∧
      (∀ i < (c.combWords d).length, ∀ b < 8,
        size ≤ ofs base ((g .eax).setWidth 64 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b)) ∧
      ∀ r ∈ s.wr ++ [below (s.gpr .esp) c.stk],
        Region.Disjoint ⟨(g .eax).setWidth 64, 8 * (c.combWords d).length⟩ r)
    (hst : ∀ r ∈ s.wr, Region.Disjoint (below (s.gpr .esp) c.stk) r)
    (hspz : c.stk ≤ (s.gpr .esp).toNat) (hsp : SpOk c.gMul c.stk) :
    WP isa c.gMul s fun s' => Keeps (powClob) s s' ∧ Unch base (gW c) s.mem s'.mem ∧
      ModOkW c.MP' size c.C.p s'.mem base ∧
      (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s'.mem base x c.n < c.C.p) ∧
      Rep c.C (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY))
        (tmv c.C c.n base s' (c.sl RZ)) (mul k (G c.C)) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega_using [hp3])
  unfold Cfg.gMul
  cases hcd : c.comb with
  | none =>
    have hlt : ∀ x ∈ ladR c.ladderCfg, wordsVal s.mem base x c.MP'.n < c.C.p := by
      intro x hx
      have hx' : x ∈ [AP, B3P, GX, GY, ONEP, RX, RY, RZ].map c.sl := hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      show sv c _ s i < c.C.p
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact lt_of_eq_of_lt F.ap (hmont _)
      · exact lt_of_eq_of_lt F.b3p (hmont _)
      · exact lt_of_eq_of_lt F.gx (hmont _)
      · exact lt_of_eq_of_lt F.gy (hmont _)
      · exact lt_of_eq_of_lt F.onep (Nat.mod_lt _ (by omega_using [hp3]))
      · exact lt_of_eq_of_lt hrx (by omega_using [hp3])
      · exact lt_of_eq_of_lt hry (hmont _)
      · exact lt_of_eq_of_lt hrz (by omega_using [hp3])
    have hG : Rep c.C (tmv c.C c.n base s (c.sl GX)) (tmv c.C c.n base s (c.sl GY))
        (tmv c.C c.n base s (c.sl ONEP)) (G c.C) := by
      show Rep c.C (toM _ _ (wordsVal s.mem _ (c.sl GX) c.n)) (toM _ _ (wordsVal s.mem _ (c.sl GY) c.n))
        (toM _ _ (wordsVal s.mem _ (c.sl ONEP) c.n)) (G c.C)
      rw [F.gx, F.gy, F.onep, toM_cmont hc, toM_cmont hc, toM_one hpR]
      exact rep_affine' hC _ _
    have hR : Rep c.C (tmv c.C c.n base s (c.sl RX)) (tmv c.C c.n base s (c.sl RY))
        (tmv c.C c.n base s (c.sl RZ)) (mul (k >>> (64 * c.n)) (G c.C)) := by
      show Rep c.C (toM _ _ (sv c _ s RX)) (toM _ _ (sv c _ s RY)) (toM _ _ (sv c _ s RZ)) _
      rw [hrx, hry, hrz, toM_cmont hc, toM_zero, shiftRight_eq_zero hkl, mul_zero_pt]
      exact rep_infinity' hC
    have hstep := step_rep (L := c.ladderCfg) (k := k) hC hc.onG (by
        show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem _ (c.sl AP) c.n) = _
        rw [F.ap]; exact toM_cmont hc _)
      (by
        show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem _ (c.sl B3P) c.n) = _
        rw [F.b3p]; exact toM_cmont hc _) hG
    refine WP.mono (ladder_ok (ladLay hc) (ladWk hc) hpR hs (modP_of hc F.mp) hlt hstep hR ht₀)
      fun s' ⟨K', U', M', L', R'⟩ => ⟨K', ?_, M', L', by rw [Nat.shiftRight_zero] at R'; exact R'⟩
    rw [ladWx_eq] at U'
    have hsub : slW c [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX, TY, TZ,
        TMP] ⊆ slW c [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP, EM] :=
      List.map_subset _ (by decide)
    exact Unch.cover U' fun w hw => ⟨w, by
      rcases List.mem_append.mp hw with hw | hw
      · exact List.mem_append_left _ (hsub hw)
      · exact List.mem_append_right _ (List.mem_append_left _ hw), Nat.le_refl _, Nat.le_refl _⟩
  | some d =>
    obtain ⟨hTM, hout, hap⟩ := hTb d hcd
    obtain e24 : c.stk = 24 := Cfg.stk_comb hcd
    rw [e24] at hap hst hspz hsp
    unfold Cfg.gMul at hsp
    rw [hcd] at hsp
    exact combCall_ok hc hC hT hcd (hCo d hcd) hs F hkl ht₀ hTM hout hap hst hspz hsp

/-- The constant time of a call of the comb, from its code's. -/
theorem GMulRel.of_body (hc : CfgOk c) {d : CombData} {ss : Bool} (hcd : c.comb = some d)
    (h : GMulRelB c d ss) : GMulRel c d ss := by
  intro base g₁ g₂ s₀ t₀ k₁ k₂ hs₁ hs₂ F₁ F₂ hk₁ hk₂ hb₁ hb₂ hTM₁ hTM₂ hout hap₁ hap₂ hst₁ hst₂
    hsp₁ hsp₂ hg wf₁ wf₂ hw he
  rw [Cfg.stk_comb hcd] at hap₁ hap₂ hst₁ hst₂ hsp₁ hsp₂
  obtain ⟨S₁, F₁', b₁, T₁, a₁, z₁, -⟩ := combEntry hc hs₁ F₁ hb₁ hTM₁ hap₁ hst₁ hsp₁
  obtain ⟨S₂, F₂', b₂, T₂, a₂, z₂, -⟩ := combEntry hc hs₂ F₂ hb₂ hTM₂ hap₂ hst₂ hsp₂
  unfold Cfg.gMul
  rw [hcd]
  exact RelCT.callBody (h S₁ S₂ F₁' F₂' hk₁ hk₂ b₁ b₂ T₁ T₂ hout a₁ a₂ z₁ z₂ hg
      (combWf_callEntry wf₁ hsp₁ hst₁) (combWf_callEntry wf₂ hsp₂ hst₂)
      (by rw [State.callEntry_wr, State.callEntry_wr, hw])
      (by rw [State.callEntry_esp, State.callEntry_esp, he]))
    (fun _ _ e => ⟨by rw [e.1], by rw [e.2]⟩) (fun _ _ e => by rw [e.1, e.2]; exact he)

end VG.Proof.Ecdsa.X86
