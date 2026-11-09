module

public import VerifiedGarbage.Proof.RsaPss.X86_64.ChkCtBase
public import VerifiedGarbage.Proof.RsaPss.X86_64.MgfCT
import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyFixed
import VerifiedGarbage.Proof.RsaPss.X86_64.PrefixCheck
import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyBlocks
import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyCtBase
import VerifiedGarbage.Proof.RsaPss.MgfBytes
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.RsaPss.X86_64.SignEnc
import VerifiedGarbage.Proof.Framework.X86_64.Syms

/-!
# RSASSA-PSS verification on x86-64: `DB` in two runs

After the call: `acc`'s first bits, `DB ⊕= MGF1(H)` (`mgfXor_ct`), its top
bits, and the scan for its first nonzero byte and the checks of it, each
constant time from the public words of both runs (`JM`). The scan's result,
the salt's position, is secret: only its bound is kept (`X7`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Chk

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)

variable {T : Tabs}

theorem km_ne {k j : Nat} (h : k ∈ KM) (hj : j ∉ KM) : k ≠ j := fun e => hj (e ▸ h)

theorem km_upd {s : State} {W : Nat → BitVec 64} (hw : ∀ k ∈ KM, W k = vw T.H s k) {j : Nat} (hj : j ∉ KM)
    (v : BitVec 64) : ∀ k ∈ KM, upd W j v k = vw T.H s k := fun k hk => by
  simp only [upd]; rw [ifn (km_ne hk hj)]; exact hw k hk

/-- After the call, with nothing else. -/
abbrev JT (H : Hash) : State → State → Prop := JM H fun _ _ _ => True

/-- `JM` as a public piece's start. -/
theorem jm_vs {X : State → (Nat → Byte) → (Nat → BitVec 64) → Prop} {a t : State} (h : VAt T (JM T.H X) a t)
    (ks : List Nat) (hks : ∀ k ∈ ks, k ∈ KM := by decide) :
    ∃ s X', VSib T a s ∧ VS T.H s t ks [] X' :=
  let ⟨s, S, h⟩ := h; ⟨s, _, S, h.1.sub hks [] (fun _ hp => by cases hp) fun _ _ x => x⟩

theorem vlo_le (s : State) : vlo s ≤ 1 := Nat.zero_le 1

theorem acc0_ct : RelCT isa (Two (VAt T (JT T.H))) (.block acc0) (Two (VAt T (JT T.H))) := by
  obtain ⟨_, hc⟩ := vFixed.acc0
  refine two_post (vtwo (T := T) (H := T.H) [17, 21, 23, 25, 26] [] (fun _ => []) (fun a t h => jm_vs h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hk1 := hp.k1; have hk2 := hp.k2
  have : vlo s = 0 := rfl; have : veml s = (s.gpr .rdx).toNat - vlo s := rfl
  refine X86_64.WP.mono_syms (acc0_ok v.L R (c := cmask s) (k := (s.gpr .rdx).toNat) (lo := vlo s)
    (by rw [hw 17 (by decide)]; show s.gpr .rdx = _; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (hw 23 (by decide)) (by rw [hw 25 (by decide)]; rfl) (hw 26 (by decide))
    (by omega_arith) hk2 (by omega_arith)) fun u ⟨L', k', R'⟩ sy =>
    ⟨s, S, v.next L' k'.2.2 R' (km_upd hw (by decide) _) trivial sy, k'.2.1.trans hrd, hok⟩

/-- `MGF1`'s anchor: `DB`'s place and length. -/
def mgfA (H : Hash) (a : State) : MA := ⟨fb a, stackArg a 0, a.wr, oEm + vlo a, vdb H.D a, a.syms⟩

/-- A public word of the entry state `a`. -/
theorem pw_w {H : Hash} {a : State} {ks : List Nat} {W : Nat → BitVec 64} (hw : ∀ p ∈ pw H a ks, W p.1 = p.2)
    {k : Nat} (hk : k ∈ ks) : W k = vw H a k :=
  hw (k, vw H a k) (List.mem_map.mpr ⟨k, hk, rfl⟩)

/-- The slots of the table of `MdHash`, in a run. -/
theorem vs_ht {s t : State} {ks : List Nat} {rs : List (Reg × BitVec 64)}
    {X : (Nat → Byte) → (Nat → BitVec 64) → Prop} (hp : Pre T s) (v : VS T.H s t ks rs X) {W : Nat → BitVec 64}
    (hw : ∀ k ∈ ks, W k = vw T.H s k) (h8 : 8 ∈ ks := by decide) (h9 : 9 ∈ ks := by decide)
    (h10 : 10 ∈ ks := by decide) : HT T.H T.dn T.f W t.syms := by
  rw [v.sy]; exact hp.tabs.hf.ht ((hw 8 h8).trans hp.tabs.h0) ((hw 9 h9).trans hp.tabs.h3) ((hw 10 h10).trans hp.tabs.h4)

/-- The slots of the table of `Hash`, in a run. -/
theorem vs_gt {s t : State} {ks : List Nat} {rs : List (Reg × BitVec 64)}
    {X : (Nat → Byte) → (Nat → BitVec 64) → Prop} (hp : Pre T s) (v : VS T.H s t ks rs X) {W : Nat → BitVec 64}
    (hw : ∀ k ∈ ks, W k = vw T.H s k) (h11 : 11 ∈ ks := by decide) (h12 : 12 ∈ ks := by decide)
    (h13 : 13 ∈ ks := by decide) (h14 : 14 ∈ ks := by decide) : GT T.G T.g W t.syms := by
  rw [v.sy]
  exact hp.tabs.gf.gt ((hw 11 h11).trans hp.tabs.g0) ((hw 12 h12).trans hp.tabs.g1) ((hw 13 h13).trans hp.tabs.g2)
    ((hw 14 h14).trans hp.tabs.g4)

theorem jt_me {a t : State} (h : VAt T (JT T.H) a t) : ME T.G T.g 1 T.H (mgfA T.H a) t := by
  obtain ⟨s, S, v, -, hok⟩ := h
  have hp := S.pa
  have hk1 := hp.k1; have hk2 := hp.k2
  have tb := hp.tabs
  have : vlo a = 0 := rfl; have : veml a = (a.gpr .rdx).toNat - vlo a := rfl
  rw [S.veml] at hok
  obtain ⟨L, w, ⟨V, W, R, hw, -⟩, rg⟩ := vs_pub S v
  refine ⟨⟨S.rest, ⟨by simp only [mgfA]; omega_arith, by simp only [mgfA, vdb]; omega_arith, ?_⟩⟩,
    ⟨L, w, ⟨V, W, R, fun p hp => ?_, trivial⟩, rg⟩, S.syG.tr v.sy⟩
  · simp only [mgfA, vdb, veml] at hok ⊢; omega_arith
  · simp only [mgfA, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact pw_w hw (k := 21) (by decide)
    · exact pw_w hw (k := 23) (by decide)
    · exact pw_w hw (k := 24) (by decide)
    · exact (pw_w hw (k := 14) (by decide)).trans tb.g4
    · exact (pw_w hw (k := 11) (by decide)).trans tb.g0
    · exact (pw_w hw (k := 12) (by decide)).trans tb.g1
    · exact (pw_w hw (k := 13) (by decide)).trans tb.g2

variable (hH : HashOK T.H) (K : Callees T.H) (hG : Pbkdf2.Md.X86_64.Calls.StreamOK T.G) {Gs : Spec.Mgf1.Hash}
  (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = T.G.D) (hGv : Proof.Mgf1.Valid Gs)

include hG hGh hGl hGv in
theorem mgf_ct (hc : HashChecks T.H.P T.H.D 1) :
    RelCT isa (Two (VAt T (JT T.H))) (mgfXor T.H T.g) (Two (VAt T (JT T.H))) := by
  refine two_post (two_map (mgfA T.H) (fun a t h => jt_me h)
    (mgfXor_ct hG hGh hGl hGv hc (fixedChecks (.inl rfl)))) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hk1 := hp.k1; have hk2 := hp.k2
  have : vlo s = 0 := rfl; have : veml s = (s.gpr .rdx).toNat - vlo s := rfl
  refine X86_64.WP.mono_syms (mgfXor_ok hG hGh hGl hGv T.H v.L R (vs_gt hp v hw) (e := oEm + vlo s)
    (db := vdb T.H.D s)
    ⟨by omega_arith, by unfold vdb; omega_arith, by unfold vdb veml at *; unfold oEm; omega_arith⟩ (hw 23 (by decide))
    (hw 24 (by decide))) fun u ⟨L', rd', wr', _, V', W', R', hW', _⟩ sy =>
    ⟨s, S, ⟨L', wr'.trans v.wr, ⟨V', W', R', fun k hk => (hW' k (km_lt hk) (by
      simp only [KM, List.mem_cons, List.not_mem_nil, or_false] at hk; omega_arith)).trans (hw k hk), trivial⟩,
      (fun _ hp => by cases hp), sy.trans v.sy⟩, rd'.trans hrd, hok⟩

theorem clearTop_ct : RelCT isa (Two (VAt T (JT T.H))) (.block clearTop) (Two (VAt T (JT T.H))) := by
  obtain ⟨_, hc⟩ := vFixed.clearTop
  refine two_post (vtwo (T := T) (H := T.H) [23] [] (fun _ => []) (fun a t h => jm_vs h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have : vlo s = 0 := rfl; have : veml s = (s.gpr .rdx).toNat - vlo s := rfl
  exact X86_64.WP.mono_syms (clearTop_ok v.L R (e := oEm + vlo s) (c := cmask s) (hw 23 (by decide))
    (by rw [hw 25 (by decide)]; rfl) (by unfold oEm oRsa; omega_arith))
    fun u ⟨L', k', R'⟩ sy => ⟨s, S, v.next L' k'.2.2 R' hw trivial sy, k'.2.1.trans hrd, hok⟩

/-- After the scan: its registers. -/
def JC6 (H : Hash) (s t : State) : Prop :=
  JT H s t ∧ ∃ (fd : Bool) (pos : Nat) (val : Byte), pos < vdb H.D s ∧
    t.gpr .rdx = (if fd then BitVec.allOnes 64 else 0) ∧ t.gpr .rsi = BitVec.ofNat 64 pos ∧
    t.gpr .r11 = BitVec.setWidth 64 val

theorem posScan_ct : RelCT isa (Two (VAt T (JT T.H))) posScan (Two (VAt T (JC6 T.H))) := by
  obtain ⟨_, hc⟩ := vFixed.posScan
  refine two_post (vtwo (T := T) (H := T.H) [23, 24] [] (fun _ => []) (fun a t h => jm_vs h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hk2 := hp.k2
  have : vlo s = 0 := rfl; have : veml s = (s.gpr .rdx).toNat - vlo s := rfl
  have hdb1 : 1 ≤ vdb T.H.D s := by unfold vdb; omega_arith
  exact X86_64.WP.mono_syms (posScan_ok v.L R (e := oEm + vlo s) (db := vdb T.H.D s) (hw 23 (by decide)) (hw 24 (by decide))
    hdb1 (by unfold vdb veml oEm oRsa; omega_arith)) fun u ⟨k', hm', hdx, hsi, h11⟩ sy =>
    ⟨s, S, ⟨v.keep k' hm' (by decide) (fun _ hp => by cases hp) sy, k'.2.1.trans hrd, hok⟩, _, _, _,
      fnz_getD_lt hdb1, hdx, hsi, h11⟩

/-- The length of `M'`, from the salt's position, which is secret. -/
def X7 (H : Hash) (s : State) (_ : Nat → Byte) (W : Nat → BitVec 64) : Prop :=
  ∃ pos, pos < vdb H.D s ∧ W 27 = BitVec.ofNat 64 (vdb H.D s - pos - 1 + (8 + H.D)) ∧
    W 34 = BitVec.ofNat 64 pos

include hH in
theorem posCheck_ct (hc : VerifyChecks T.H.P T.H.D) :
    RelCT isa (Two (VAt T (JC6 T.H))) (posCheck T.H) (Two (VAt T (JM T.H (X7 T.H)))) := by
  obtain ⟨_, hc⟩ := hc.posCheck
  refine two_post (vtwo (T := T) (H := T.H) [24, 35, 36] [] (fun _ => []) (fun a t h => jm_vs (let ⟨s, S, h⟩ := h;
    ⟨s, S, h.1⟩) _) (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, ⟨v, hrd, hok⟩, fd, pos, val, hpos, hdx, hsi, h11⟩ => ?_
  obtain ⟨V, W, R, hw, -⟩ := v.W
  exact X86_64.WP.mono_syms (posCheck_ok hH v.L R (db := vdb T.H.D s) (pos := pos) (fd := fd) (val := val)
    (fixed := decide ((s.gpr .r9).setWidth 32 = 0)) (hw 24 (by decide))
    (by rw [hw 35 (by decide)]; simp only [vw, decide_eq_true_eq]) hpos hdx hsi h11) fun u ⟨L', k', R'⟩ sy =>
    ⟨s, S, v.next L' k'.2.2 R' (km_upd (km_upd (km_upd hw (by decide) _) (by decide) _) (by decide) _)
      ⟨pos, hpos, by simp [upd], by simp [upd]⟩ sy, k'.2.1.trans hrd, hok⟩

/-- Testing the public salt mode before the scan. -/
theorem scanAny_ct : RelCT isa (Two (VAt T (JT T.H)))
    (.block [.mov .rax (.mem (sp sAny)), .alu .test .rax (.reg .rax)])
    (Two fun a t => VAt T (JT T.H) a t ∧
      isa.eval .e t = some (decide (vw T.H a 35 = 0))) := by
  obtain ⟨_, hc⟩ := vFixed.scanAny
  refine two_post (vtwo (T := T) (H := T.H) [35] [] (fun _ => [])
    (fun a t h => jm_vs h _) (fun _ => rfl) (by decide) hc)
    fun a t ⟨s, S, v, hrd, hok⟩ => ?_
  obtain ⟨V, W, R, hw, _⟩ := v.W
  refine X86_64.WP.mono_syms (WP.keep [.rax] (Q := fun u => u.mem = t.mem ∧
    u.zf = some (decide (W 35 = 0))) ?_ rfl) fun u ⟨⟨hm, hz⟩, ku⟩ sy => ?_
  · xrun [ea_sp, v.L.rsp, v.L.ld (d := sAny) (by decide), R.rd (d := sAny) 35 rfl (by decide)]
    rw [BitVec.and_self]
    rfl
  · refine ⟨⟨s, S, v.keep ku hm (by decide) (fun _ hp => by cases hp) sy, ku.2.1.trans hrd, hok⟩, ?_⟩
    change u.zf = _
    rw [hz, hw 35 (by decide), S.vw]

/-- And the bound on the requested length. -/
theorem scanLen_ct : RelCT isa (Two (VAt T (JT T.H)))
    (.block [.mov .rax (.mem (sp sSlen)), .alu .cmp .rax (.mem (sp sDb))])
    (Two fun a t => VAt T (JT T.H) a t ∧
      isa.eval .b t = some (decide ((a.gpr .r8).toNat < vdb T.H.D a))) := by
  obtain ⟨_, hc⟩ := vFixed.scanLen
  refine two_post (vtwo (T := T) (H := T.H) [24, 36] [] (fun _ => [])
    (fun a t h => jm_vs h _) (fun _ => rfl) (by decide) hc)
    fun a t ⟨s, S, v, hrd, hok⟩ => ?_
  obtain ⟨V, W, R, hw, _⟩ := v.W
  have hk2 := S.ps.k2
  refine X86_64.WP.mono_syms (WP.keep [.rax] (Q := fun u => u.mem = t.mem ∧
    u.cf = some (decide ((s.gpr .r8).toNat < vdb T.H.D s))) ?_ rfl) fun u ⟨⟨hm, hz⟩, ku⟩ sy => ?_
  · xrun [ea_sp, v.L.rsp, v.L.ld (d := sSlen) (by decide), v.L.ld (d := sDb) (by decide),
      R.rd (d := sSlen) 36 rfl (by decide), R.rd (d := sDb) 24 rfl (by decide),
      hw 36 (by decide), hw 24 (by decide)]
    simp only [vw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show vdb T.H.D s < 2 ^ 64 by unfold vdb veml; omega_arith)]
  · refine ⟨⟨s, S, v.keep ku hm (by decide) (fun _ hp => by cases hp) sy, ku.2.1.trans hrd, hok⟩, ?_⟩
    change u.cf = _
    rw [hz, S.rsl, S.vdb]

/-- After the call, with the salt's length given and less than `DB`'s. -/
def JTF (H : Hash) (s t : State) : Prop := JT H s t ∧ (s.gpr .r8).toNat < vdb H.D s

include hH in
theorem prefixCheck_ct (hc : VerifyChecks T.H.P T.H.D) :
    RelCT isa (Two (VAt T (JTF T.H))) (prefixCheck T.H) (Two (VAt T (JM T.H (X7 T.H)))) := by
  obtain ⟨_, hc⟩ := hc.prefixCheck
  refine two_post (vtwo (T := T) (H := T.H) [23, 24, 36] [] (fun _ => []) (fun a t h => jm_vs (let ⟨s, S, h⟩ := h;
    ⟨s, S, h.1⟩) _) (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, ⟨v, hrd, hok⟩, hlt⟩ => ?_
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hk2 := hp.k2
  have : vlo s = 0 := rfl; have : veml s = (s.gpr .rdx).toNat - vlo s := rfl
  refine X86_64.WP.mono_syms (prefixCheck_ok hH v.L R (e := oEm + vlo s) (db := vdb T.H.D s) (sl := (s.gpr .r8).toNat)
    (hw 23 (by decide)) (hw 24 (by decide)) (by rw [hw 36 (by decide)]; simp [vw]) hlt
    (by unfold vdb veml oEm oRsa; omega_arith) (by unfold vdb veml; omega_arith)) fun u ⟨L', k', a', _, R'⟩ sy =>
    ⟨s, S, v.next L' k'.2.2 R' (km_upd (km_upd (km_upd hw (by decide) _) (by decide) _) (by decide) _)
      ⟨vdb T.H.D s - (s.gpr .r8).toNat - 1, by omega_arith, ?_, by simp [upd]⟩ sy, k'.2.1.trans hrd, hok⟩
  simp only [upd, Nat.reduceEqDiff, ite_true]
  congr 1
  omega_arith

include hH in
theorem scanCheck_ct (hc : VerifyChecks T.H.P T.H.D) :
    RelCT isa (Two (VAt T (JT T.H))) (scanCheck T.H) (Two (VAt T (JM T.H (X7 T.H)))) := by
  have generic := (posScan_ct (T := T)).seq (posCheck_ct hH hc)
  unfold scanCheck
  refine scanAny_ct.seq (two_ite (fun a t₁ t₂ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_
    (generic.mono (fun _ _ => two_mono fun _ _ h => h.1.1) fun _ _ h => h))
  refine (scanLen_ct.seq (two_ite (fun a t₁ t₂ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_
    (generic.mono (fun _ _ => two_mono fun _ _ h => h.1.1) fun _ _ h => h))).mono
    (fun _ _ => two_mono fun _ _ h => h.1.1) (fun _ _ h => h)
  refine (prefixCheck_ct hH hc).mono (fun _ _ => two_mono fun a t ⟨⟨⟨s, S, h⟩, hz⟩, hb⟩ => ?_) fun _ _ h => h
  have hf : (a.gpr .r8).toNat < vdb T.H.D a := by
    rw [hz, Option.some.injEq, decide_eq_true_eq] at hb
    exact hb
  exact ⟨s, S, h, by rwa [S.rsl, S.vdb]⟩

end VG.Proof.RsaPss.X86_64.Chk
