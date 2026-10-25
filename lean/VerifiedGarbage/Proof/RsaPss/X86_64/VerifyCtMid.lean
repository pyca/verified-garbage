module

public import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyCtCall
public import VerifiedGarbage.Proof.RsaPss.X86_64.MgfCT
import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyFixed
import VerifiedGarbage.Proof.RsaPss.X86_64.PrefixCheck
import VerifiedGarbage.Proof.RsaPss.MgfBytes
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.RsaPss.X86_64.SignEnc

/-!
# RSASSA-PSS verification on x86-64: `DB` in two runs

After the call: `acc`'s first bits, `DB ⊕= MGF1(H)` (`mgfXor_ct`), its top
bits, and the scan for its first nonzero byte and the checks of it, each
constant time from the public words of both runs (`JM`). The scan's result,
the salt's position, is secret: only its bound is kept (`X7`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)

variable {G : Spec.Mgf1.Hash} {H : Hash} {extra : State → State → Prop}

theorem km_ne {k j : Nat} (h : k ∈ KM) (hj : j ∉ KM) : k ≠ j := fun e => hj (e ▸ h)

theorem km_upd {s : State} {W : Nat → BitVec 64} (hw : ∀ k ∈ KM, W k = vw H s k) {j : Nat} (hj : j ∉ KM)
    (v : BitVec 64) : ∀ k ∈ KM, upd W j v k = vw H s k := fun k hk => by
  simp only [upd]; rw [ifn (km_ne hk hj)]; exact hw k hk

theorem km_sub {ks : List Nat} (h : ∀ k ∈ ks, k ∈ KM := by decide) : ∀ k ∈ ks, k ∈ KM := h

variable (H) in
/-- After the call, with nothing else. -/
abbrev JT : State → State → Prop := JM H fun _ _ _ => True

/-- `JM` as a public piece's start. -/
theorem jm_vs {X : State → (Nat → Byte) → (Nat → BitVec 64) → Prop} {a t : State} (h : VAt (extra := extra) G (JM H X) a t)
    (ks : List Nat) (hks : ∀ k ∈ ks, k ∈ KM := by decide) :
    ∃ s X', VSib (extra := extra) G a s ∧ VS H s t ks [] X' :=
  let ⟨s, S, h⟩ := h; ⟨s, _, S, h.1.sub hks [] (fun _ hp => by cases hp) fun _ _ x => x⟩

theorem vlo_le (s : State) : vlo s ≤ 1 := by unfold vlo loV; split <;> omega_arith

theorem acc0_ct : RelCT isa (Two (VAt (extra := extra) G (JT H))) (.block acc0) (Two (VAt (extra := extra) G (JT H))) := by
  obtain ⟨_, hc⟩ := vFixed.acc0
  refine two_post (vtwo (G := G) (H := H) [17, 21, 23, 25, 26] [] (fun _ => []) (fun a t h => jm_vs h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hk1 := hp.k1; have hk2 := hp.k2
  have := vlo_le s
  refine WP.mono (acc0_ok v.L R (c := (maskV (n0v s)).setWidth 8) (k := (s.gpr .rsi).toNat) (lo := vlo s)
    (by rw [hw 17 (by decide)]; show s.gpr .rsi = _; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (hw 23 (by decide)) (by rw [hw 25 (by decide)]; exact maskV_byte (BitVec.isLt _)) (hw 26 (by decide))
    (by omega_arith) hk2 (by omega_arith)) fun u ⟨L', k', R'⟩ =>
    ⟨s, S, v.next L' k'.2.2 R' (km_upd hw (by decide) _) trivial, k'.2.1.trans hrd, hok⟩

/-- `MGF1`'s anchor: `DB`'s place and length. -/
def mgfA (H : Hash) (a : State) : MA := ⟨fb a, stackArg a 3, a.wr, oEm + vlo a, vdb H.D a⟩

theorem jt_me {a t : State} (h : VAt (extra := extra) G (JT H) a t) : ME H 1 (mgfA H a) t := by
  obtain ⟨s, S, v, -, hok⟩ := h
  have hp := S.pa
  have hk1 := hp.k1; have hk2 := hp.k2
  have := vlo_le a
  rw [S.veml] at hok
  refine ⟨⟨S.rest, ⟨by simp only [mgfA]; omega_arith, by simp only [mgfA, vdb]; omega_arith, ?_⟩⟩,
    (vs_pub S v).sub (fun p hp => ?_) (fun _ h => h) fun _ _ _ => trivial⟩
  · simp only [mgfA, vdb, veml] at hok ⊢; omega_arith
  · simp only [mgfA, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp [pw, KM, vw]

variable (hH : HashOK H) (K : Callees H) (lk : MgfLink H hH)

include hH K in
theorem mgf_ct (hc : HashChecks H.P H.D 1) :
    RelCT isa (Two (VAt (extra := extra) lk.G (JT H))) (mgfXor H) (Two (VAt (extra := extra) lk.G (JT H))) := by
  have hG := validG hH lk.hash lk.len
  refine two_post (two_map (mgfA H) (fun a t h => jt_me h)
    (mgfXor_ct hH K 1 lk.hash lk.len hG hc (fixedChecks (.inl rfl)))) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hk1 := hp.k1; have hk2 := hp.k2
  have := vlo_le s
  refine WP.mono (mgfXor_ok hH K lk.hash lk.len hG v.L R (e := oEm + vlo s) (db := vdb H.D s)
    ⟨by omega_arith, by unfold vdb; omega_arith, by unfold vdb veml at *; unfold oEm; omega_arith⟩ (hw 23 (by decide))
    (hw 24 (by decide))) fun u ⟨L', rd', wr', _, V', W', R', hW', _⟩ =>
    ⟨s, S, ⟨L', wr'.trans v.wr, ⟨V', W', R', fun k hk => (hW' k (km_lt hk) (by
      simp only [KM, List.mem_cons, List.not_mem_nil, or_false] at hk; omega_arith)).trans (hw k hk), trivial⟩,
      fun _ hp => by cases hp⟩, rd'.trans hrd, hok⟩

theorem clearTop_ct : RelCT isa (Two (VAt (extra := extra) G (JT H))) (.block clearTop) (Two (VAt (extra := extra) G (JT H))) := by
  obtain ⟨_, hc⟩ := vFixed.clearTop
  refine two_post (vtwo (G := G) (H := H) [23] [] (fun _ => []) (fun a t h => jm_vs h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have := vlo_le s
  exact WP.mono (clearTop_ok v.L R (e := oEm + vlo s) (c := (maskV (n0v s)).setWidth 8) (hw 23 (by decide))
    (by rw [hw 25 (by decide)]; exact maskV_byte (BitVec.isLt _)) (by unfold oEm oRsa; omega_arith))
    fun u ⟨L', k', R'⟩ => ⟨s, S, v.next L' k'.2.2 R' hw trivial, k'.2.1.trans hrd, hok⟩

variable (H) in
/-- After the scan: its registers. -/
def JC6 (s t : State) : Prop :=
  JT H s t ∧ ∃ (fd : Bool) (pos : Nat) (val : Byte), pos < vdb H.D s ∧
    t.gpr .rdx = (if fd then BitVec.allOnes 64 else 0) ∧ t.gpr .rsi = BitVec.ofNat 64 pos ∧
    t.gpr .r11 = BitVec.setWidth 64 val

theorem posScan_ct : RelCT isa (Two (VAt (extra := extra) G (JT H))) posScan (Two (VAt (extra := extra) G (JC6 H))) := by
  obtain ⟨_, hc⟩ := vFixed.posScan
  refine two_post (vtwo (G := G) (H := H) [23, 24] [] (fun _ => []) (fun a t h => jm_vs h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hk2 := hp.k2
  have := vlo_le s
  have hdb1 : 1 ≤ vdb H.D s := by unfold vdb; omega_arith
  exact WP.mono (posScan_ok v.L R (e := oEm + vlo s) (db := vdb H.D s) (hw 23 (by decide)) (hw 24 (by decide))
    hdb1 (by unfold vdb veml oEm oRsa; omega_arith)) fun u ⟨k', hm', hdx, hsi, h11⟩ =>
    ⟨s, S, ⟨v.keep k' hm' (by decide) (fun _ hp => by cases hp), k'.2.1.trans hrd, hok⟩, _, _, _,
      fnz_getD_lt hdb1, hdx, hsi, h11⟩

variable (H) in
/-- The length of `M'`, from the salt's position, which is secret. -/
def X7 (s : State) (_ : Nat → Byte) (W : Nat → BitVec 64) : Prop :=
  ∃ pos, pos < vdb H.D s ∧ W 27 = BitVec.ofNat 64 (vdb H.D s - pos - 1 + (8 + H.D)) ∧
    W 34 = BitVec.ofNat 64 pos

include hH in
theorem posCheck_ct (hc : VerifyChecks H.P H.D) :
    RelCT isa (Two (VAt (extra := extra) G (JC6 H))) (posCheck H) (Two (VAt (extra := extra) G (JM H (X7 H)))) := by
  obtain ⟨_, hc⟩ := hc.posCheck
  refine two_post (vtwo (G := G) (H := H) [24, 35, 36] [] (fun _ => []) (fun a t h => jm_vs (let ⟨s, S, h⟩ := h;
    ⟨s, S, h.1⟩) _) (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, ⟨v, hrd, hok⟩, fd, pos, val, hpos, hdx, hsi, h11⟩ => ?_
  obtain ⟨V, W, R, hw, -⟩ := v.W
  exact WP.mono (posCheck_ok hH v.L R (db := vdb H.D s) (pos := pos) (fd := fd) (val := val)
    (fixed := decide ((stackArg s 2).setWidth 32 = 0)) (hw 24 (by decide))
    (by rw [hw 35 (by decide)]; simp only [vw, decide_eq_true_eq]) hpos hdx hsi h11) fun u ⟨L', k', R'⟩ =>
    ⟨s, S, v.next L' k'.2.2 R' (km_upd (km_upd (km_upd hw (by decide) _) (by decide) _) (by decide) _)
      ⟨pos, hpos, by simp [upd], by simp [upd]⟩, k'.2.1.trans hrd, hok⟩

/-- Testing the public salt mode before the scan. -/
theorem scanAny_ct : RelCT isa (Two (VAt (extra := extra) G (JT H)))
    (.block [.mov .rax (.mem (sp sAny)), .alu .test .rax (.reg .rax)])
    (Two fun a t => VAt (extra := extra) G (JT H) a t ∧
      isa.eval .e t = some (decide (vw H a 35 = 0))) := by
  obtain ⟨_, hc⟩ := vFixed.scanAny
  refine two_post (vtwo (G := G) (H := H) [35] [] (fun _ => [])
    (fun a t h => jm_vs h _) (fun _ => rfl) (by decide) hc)
    fun a t ⟨s, S, v, hrd, hok⟩ => ?_
  obtain ⟨V, W, R, hw, _⟩ := v.W
  refine WP.mono (WP.keep [.rax] (Q := fun u => u.mem = t.mem ∧
    u.zf = some (decide (W 35 = 0))) ?_ rfl) fun u ⟨⟨hm, hz⟩, ku⟩ => ?_
  · xrun [ea_sp, v.L.rsp, v.L.ld (d := sAny) (by decide), R.rd (d := sAny) 35 rfl (by decide)]
    rw [BitVec.and_self]
    rfl
  · refine ⟨⟨s, S, v.keep ku hm (by decide) (fun _ hp => by cases hp), ku.2.1.trans hrd, hok⟩, ?_⟩
    change u.zf = _
    rw [hz, hw 35 (by decide), S.vw]

/-- And the bound on the requested length. -/
theorem scanLen_ct : RelCT isa (Two (VAt (extra := extra) G (JT H)))
    (.block [.mov .rax (.mem (sp sSlen)), .alu .cmp .rax (.mem (sp sDb))])
    (Two fun a t => VAt (extra := extra) G (JT H) a t ∧
      isa.eval .b t = some (decide ((stackArg a 1).toNat < vdb H.D a))) := by
  obtain ⟨_, hc⟩ := vFixed.scanLen
  refine two_post (vtwo (G := G) (H := H) [24, 36] [] (fun _ => [])
    (fun a t h => jm_vs h _) (fun _ => rfl) (by decide) hc)
    fun a t ⟨s, S, v, hrd, hok⟩ => ?_
  obtain ⟨V, W, R, hw, _⟩ := v.W
  have hk2 := S.ps.k2
  refine WP.mono (WP.keep [.rax] (Q := fun u => u.mem = t.mem ∧
    u.cf = some (decide ((stackArg s 1).toNat < vdb H.D s))) ?_ rfl) fun u ⟨⟨hm, hz⟩, ku⟩ => ?_
  · xrun [ea_sp, v.L.rsp, v.L.ld (d := sSlen) (by decide), v.L.ld (d := sDb) (by decide),
      R.rd (d := sSlen) 36 rfl (by decide), R.rd (d := sDb) 24 rfl (by decide),
      hw 36 (by decide), hw 24 (by decide)]
    simp only [vw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show vdb H.D s < 2 ^ 64 by unfold vdb veml; omega_arith)]
  · refine ⟨⟨s, S, v.keep ku hm (by decide) (fun _ hp => by cases hp), ku.2.1.trans hrd, hok⟩, ?_⟩
    change u.cf = _
    rw [hz, S.arg1, S.vdb]

variable (H) in
/-- After the call, with the salt's length given and less than `DB`'s. -/
def JTF (s t : State) : Prop := JT H s t ∧ (stackArg s 1).toNat < vdb H.D s

include hH in
theorem prefixCheck_ct (hc : VerifyChecks H.P H.D) :
    RelCT isa (Two (VAt (extra := extra) G (JTF H))) (prefixCheck H) (Two (VAt (extra := extra) G (JM H (X7 H)))) := by
  obtain ⟨_, hc⟩ := hc.prefixCheck
  refine two_post (vtwo (G := G) (H := H) [23, 24, 36] [] (fun _ => []) (fun a t h => jm_vs (let ⟨s, S, h⟩ := h;
    ⟨s, S, h.1⟩) _) (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, ⟨v, hrd, hok⟩, hlt⟩ => ?_
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hk2 := hp.k2
  have := vlo_le s
  refine WP.mono (prefixCheck_ok hH v.L R (e := oEm + vlo s) (db := vdb H.D s) (sl := (stackArg s 1).toNat)
    (hw 23 (by decide)) (hw 24 (by decide)) (by rw [hw 36 (by decide)]; simp [vw]) hlt
    (by unfold vdb veml oEm oRsa; omega_arith) (by unfold vdb veml; omega_arith)) fun u ⟨L', k', a', _, R'⟩ =>
    ⟨s, S, v.next L' k'.2.2 R' (km_upd (km_upd (km_upd hw (by decide) _) (by decide) _) (by decide) _)
      ⟨vdb H.D s - (stackArg s 1).toNat - 1, by omega_arith, ?_, by simp [upd]⟩, k'.2.1.trans hrd, hok⟩
  simp only [upd, Nat.reduceEqDiff, ite_true]
  congr 1
  omega_arith

include hH in
theorem scanCheck_ct (hc : VerifyChecks H.P H.D) :
    RelCT isa (Two (VAt (extra := extra) G (JT H))) (scanCheck H) (Two (VAt (extra := extra) G (JM H (X7 H)))) := by
  have generic := (posScan_ct (extra := extra) (G := G) (H := H)).seq (posCheck_ct (extra := extra) hH hc)
  unfold scanCheck
  refine scanAny_ct.seq (two_ite (fun a t₁ t₂ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_
    (generic.mono (fun _ _ => two_mono fun _ _ h => h.1.1) fun _ _ h => h))
  refine (scanLen_ct.seq (two_ite (fun a t₁ t₂ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_
    (generic.mono (fun _ _ => two_mono fun _ _ h => h.1.1) fun _ _ h => h))).mono
    (fun _ _ => two_mono fun _ _ h => h.1.1) (fun _ _ h => h)
  refine (prefixCheck_ct hH hc).mono (fun _ _ => two_mono fun a t ⟨⟨⟨s, S, h⟩, hz⟩, hb⟩ => ?_) fun _ _ h => h
  have hf : (stackArg a 1).toNat < vdb H.D a := by
    rw [hz, Option.some.injEq, decide_eq_true_eq] at hb
    exact hb
  exact ⟨s, S, h, by rwa [S.arg1, S.vdb]⟩

end VG.Proof.RsaPss.X86_64
