module

public import VerifiedGarbage.Proof.RsaPss.X86_64.AnyVerifyCtCall
public import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyCtMid
public import VerifiedGarbage.Proof.RsaPss.X86_64.MgfAnyCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
public import VerifiedGarbage.Proof.RsaPss.X86_64.MgfCT
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyFixed

/-!
# RSASSA-PSS verification on x86-64: `DB` in two runs

After the call: `acc`'s first bits, `DB ⊕= MGF1(H)` (`mgfXor_ct`), its top
bits, and the scan for its first nonzero byte and the checks of it, each
constant time from the public words of both runs (`JMA`). The scan's result,
the salt's position, is secret: only its bound is kept (`X7A`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Any

open VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64 VG.Impl.RsaPss.X86_64.AnyHash
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)

variable {G : Spec.Mgf1.Hash} {H : Hash} {k g : Nat}

theorem km_neA {k j : Nat} (h : k ∈ KMA) (hj : j ∉ KMA) : k ≠ j := fun e => hj (e ▸ h)

theorem km_updA {s : State} {W : Nat → BitVec 64} (hw : ∀ k ∈ KMA, W k = vwA H s k) {j : Nat} (hj : j ∉ KMA)
    (v : BitVec 64) : ∀ k ∈ KMA, upd W j v k = vwA H s k := fun k hk => by
  simp only [upd]; rw [ifn (km_neA hk hj)]; exact hw k hk

theorem km_subA {ks : List Nat} (h : ∀ k ∈ ks, k ∈ KMA := by decide) : ∀ k ∈ ks, k ∈ KMA := h

variable (H) in
/-- After the call, with nothing else. -/
abbrev JTA : State → State → Prop := JMA H fun _ _ _ => True

/-- `JMA` as a public piece's start. -/
theorem jm_vsA {X : State → (Nat → Byte) → (Nat → BitVec 64) → Prop} {a t : State} (h : VAtA G k g (JMA H X) a t)
    (ks : List Nat) (hks : ∀ k ∈ ks, k ∈ KMA := by decide) :
    ∃ s X', VSibA G k g a s ∧ VSA H s t ks [] X' :=
  let ⟨s, S, h⟩ := h; ⟨s, _, S, h.1.sub hks [] (fun _ hp => by cases hp) fun _ _ x => x⟩

theorem acc0_ctA : RelCT isa (Two (VAtA G k g (JTA H))) (.block acc0) (Two (VAtA G k g (JTA H))) := by
  obtain ⟨_, hc⟩ := vFixed.acc0
  refine two_post (vtwoA (G := G) (H := H) [17, 21, 23, 25, 26] [] (fun _ => []) (fun a t h => jm_vsA h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hk1 := hp.k1; have hk2 := hp.k2
  have := vlo_le s
  refine WP.mono (acc0_ok v.L R (c := (maskV (n0v s)).setWidth 8) (k := (s.gpr .rsi).toNat) (lo := vlo s)
    (by rw [hw 17 (by decide)]; show s.gpr .rsi = _; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (hw 23 (by decide)) (by rw [hw 25 (by decide)]; exact maskV_byte (BitVec.isLt _)) (hw 26 (by decide))
    (by omega) hk2 (by omega)) fun u ⟨L', k', R'⟩ =>
    ⟨s, S, v.next L' k'.2.2 R' (km_updA hw (by decide) _) trivial, k'.2.1.trans hrd, hok⟩

/-- `MGF1`'s anchor: `DB`'s place and length. -/
def mgfAA (H : Hash) (a : State) : MA := ⟨fb a, stackArg a 4, a.wr, oEm + vlo a, vdb H.D a⟩

theorem vw15 {a s : State} (S : VSibA G k g a s) (hGl : G.len = H.D) : a.gpr .r9 = BitVec.ofNat 64 H.D := by
  rw [← hGl, ← S.pa.hdl, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem jt_meA (hD0 : 0 < H.D) (hD64 : H.D ≤ 64) (hGl : G.len = H.D) {a t : State} (h : VAtA G k g (JTA H) a t) :
    MEA 1 H.D g (mgfAA H a) t := by
  obtain ⟨s, S, v, -, hok⟩ := h
  have hp := S.pa
  have hk1 := hp.k1; have hk2 := hp.k2
  have := vlo_le a
  rw [S.veml] at hok
  refine ⟨⟨S.rest, ⟨by simp only [mgfAA]; omega, by simp only [mgfAA, vdb]; omega, ?_⟩, hD0, hD64⟩,
    (vs_pubA S v).sub (fun p hp => ?_) (fun _ h => h) fun _ _ _ => trivial⟩
  · simp only [mgfAA, vdb, veml] at hok ⊢; omega
  · simp only [mwsE, mgfAA, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · simp [pwA, KMA, vwA, vw15 S hGl]
    · simp [pwA, KMA, vwA]
    · simp [pwA, KMA, vwA]
    · simp [pwA, KMA, vwA]
    · simp only [pwA, KMA, vwA, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
        Prod.mk.injEq, Nat.reduceEqDiff, false_and, false_or, true_and]
      rw [← S.2.2.2.2]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

variable (hH : HashOK H) (K : Callees H) (lk : MgfLink H hH)

include hH in
/-- MGF1, with the hash function `hs[g]`. -/
theorem mgfAny_ctA {hs : List Hash} (hg : g < hs.length) (hl : hs.length ≤ 2 ^ 31) (hG : HashOK hs[g])
    (KG : Callees hs[g]) (lkG : MgfLink hs[g] hG) (hcg : PssChecks hs[g].P hs[g].D) :
    RelCT isa (Two (VAtA lk.G k g (JTA H))) (mgfXorAny hs) (Two (VAtA lk.G k g (JTA H))) := by
  have hD := hH.hD0
  have hDN := hH.hDN
  have hN := hH.N_le
  have hGv := validG hG lkG.hash lkG.len
  refine two_post (two_map (mgfAA H) (fun a t h => jt_meA hD (by omega) lk.len h)
    (mgfXorAny_ct 1 H.D lkG.G hg hG KG hl lkG.hash lkG.len hGv hcg.hash1 (fixedChecks (.inl rfl))
      (anyMgfChecks (.inl rfl)))) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hk1 := hp.k1; have hk2 := hp.k2
  have := vlo_le s
  have h15 : W 15 = BitVec.ofNat 64 H.D := (hw 15 (by decide)).trans (by
    simp only [vwA]; rw [← lk.len, ← hp.hdl, BitVec.ofNat_toNat, BitVec.setWidth_eq])
  have h48 : W 48 = BitVec.ofNat 64 g := (hw 48 (by decide)).trans (by
    simp only [vwA]; rw [← S.msel_eq]; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat])
  refine WP.mono (mgfXorAny_ok hg hl hG KG lkG.hash lkG.len hGv v.L R (e := oEm + vlo s) (db := vdb H.D s)
    ⟨by omega, by unfold vdb; omega, by unfold vdb veml at *; unfold oEm; omega⟩ hD (by omega) (hw 23 (by decide))
    (hw 24 (by decide)) h15 h48) fun u ⟨L', rd', wr', _, V', W', R', hW', _⟩ =>
    ⟨s, S, ⟨L', wr'.trans v.wr, ⟨V', W', R', fun k hk => (hW' k (km_ltA hk) (by
      simp only [KMA, List.mem_cons, List.not_mem_nil, or_false] at hk; omega)).trans (hw k hk), trivial⟩,
      fun _ hp => by cases hp⟩, rd'.trans hrd, hok⟩

theorem clearTop_ctA : RelCT isa (Two (VAtA G k g (JTA H))) (.block clearTop) (Two (VAtA G k g (JTA H))) := by
  obtain ⟨_, hc⟩ := vFixed.clearTop
  refine two_post (vtwoA (G := G) (H := H) [23] [] (fun _ => []) (fun a t h => jm_vsA h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have := vlo_le s
  exact WP.mono (clearTop_ok v.L R (e := oEm + vlo s) (c := (maskV (n0v s)).setWidth 8) (hw 23 (by decide))
    (by rw [hw 25 (by decide)]; exact maskV_byte (BitVec.isLt _)) (by unfold oEm oRsa; omega))
    fun u ⟨L', k', R'⟩ => ⟨s, S, v.next L' k'.2.2 R' hw trivial, k'.2.1.trans hrd, hok⟩

variable (H) in
/-- After the scan: its registers. -/
def JC6A (s t : State) : Prop :=
  JTA H s t ∧ ∃ (fd : Bool) (pos : Nat) (val : Byte), pos < vdb H.D s ∧
    t.gpr .rdx = (if fd then BitVec.allOnes 64 else 0) ∧ t.gpr .rsi = BitVec.ofNat 64 pos ∧
    t.gpr .r11 = BitVec.setWidth 64 val

theorem posScan_ctA : RelCT isa (Two (VAtA G k g (JTA H))) posScan (Two (VAtA G k g (JC6A H))) := by
  obtain ⟨_, hc⟩ := vFixed.posScan
  refine two_post (vtwoA (G := G) (H := H) [23, 24] [] (fun _ => []) (fun a t h => jm_vsA h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hk2 := hp.k2
  have := vlo_le s
  have hdb1 : 1 ≤ vdb H.D s := by unfold vdb; omega
  exact WP.mono (posScan_ok v.L R (e := oEm + vlo s) (db := vdb H.D s) (hw 23 (by decide)) (hw 24 (by decide))
    hdb1 (by unfold vdb veml oEm oRsa; omega)) fun u ⟨k', hm', hdx, hsi, h11⟩ =>
    ⟨s, S, ⟨v.keep k' hm' (by decide) (fun _ hp => by cases hp), k'.2.1.trans hrd, hok⟩, _, _, _,
      fnz_getD_lt hdb1, hdx, hsi, h11⟩

variable (H) in
/-- The length of `M'`, from the salt's position, which is secret. -/
def X7A (s : State) (_ : Nat → Byte) (W : Nat → BitVec 64) : Prop :=
  ∃ pos, pos < vdb H.D s ∧ W 27 = BitVec.ofNat 64 (vdb H.D s - pos - 1 + (8 + H.D)) ∧
    W 34 = BitVec.ofNat 64 pos

include hH in
theorem posCheck_ctA (hc : VerifyChecks H.P H.D) :
    RelCT isa (Two (VAtA G k g (JC6A H))) (posCheck H) (Two (VAtA G k g (JMA H (X7A H)))) := by
  obtain ⟨_, hc⟩ := hc.posCheck
  refine two_post (vtwoA (G := G) (H := H) [24, 35, 36] [] (fun _ => []) (fun a t h => jm_vsA (let ⟨s, S, h⟩ := h;
    ⟨s, S, h.1⟩) _) (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, ⟨v, hrd, hok⟩, fd, pos, val, hpos, hdx, hsi, h11⟩ => ?_
  obtain ⟨V, W, R, hw, -⟩ := v.W
  exact WP.mono (posCheck_ok hH v.L R (db := vdb H.D s) (pos := pos) (fd := fd) (val := val)
    (fixed := decide ((stackArg s 3).setWidth 32 = 0)) (hw 24 (by decide))
    (by rw [hw 35 (by decide)]; simp only [vwA, decide_eq_true_eq]) hpos hdx hsi h11) fun u ⟨L', k', R'⟩ =>
    ⟨s, S, v.next L' k'.2.2 R' (km_updA (km_updA (km_updA hw (by decide) _) (by decide) _) (by decide) _)
      ⟨pos, hpos, by simp [upd], by simp [upd]⟩, k'.2.1.trans hrd, hok⟩

end VG.Proof.RsaPss.X86_64.Any
