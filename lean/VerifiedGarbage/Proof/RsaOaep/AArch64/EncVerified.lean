import VerifiedGarbage.Proof.RsaOaep.AArch64.EncCT1
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncVerified
import VerifiedGarbage.Proof.Framework.Contract

/-!
# RSAES-OAEP encryption on AArch64: verified

The prologue and the check of `k` (`head_ct`), from two entry states whose
public data agree; the failure (`encFail_tr`); the check of the message's
length; and `encMain_tr`, put together (`enc_ct`): the two branches are on
`k` and the message's length, which are public. With correctness
(`enc_ok`), `vg_rsa_oaep_<H>_mgf1_<G>_encrypt`, for any implementation of the
hash functions and `pv` of `vg_rsa_public_checked`, is verified against the
shared contract with the stack it and its callee use (`enc_verified`), given
that the contract is satisfiable for it (which the registration file
checks).
-/

namespace VG.Proof.RsaOaep.AArch64.Enc

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Proof.Mgf1 (ifp ifn)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (StreamOK)
open VG.Proof.RsaPkcs1Enc.AArch64 (PubImpl)
open VG.Proof.RsaPkcs1Enc.AArch64.Enc (leak_split bytesAt_length)
open VG.Proof.RsaOaep.AArch64.Dec (entered)

/-- `x11` all ones iff `k < 2 hLen + 2`. -/
def KX (D k : Nat) (_ : Nat → BitVec 64) (t : State) : Prop :=
  t.gpr .x11 = if 2 * D + 2 ≤ k then 0 else BitVec.allOnes 64

/-- `x11` all ones iff `mLen > k - 2 hLen - 2`. -/
def MX (D k mLen : Nat) (_ : Nat → BitVec 64) (t : State) : Prop :=
  t.gpr .x11 = if mLen ≤ k - (2 * D + 2) then 0 else BitVec.allOnes 64

/-- Zeros to `out` and 0, in both runs the same. -/
theorem encFail_tr {P : Nat} {e : Env} (hL : e.L.Ok) (hP16 : 16 ≤ e.L.P) {X : (Nat → BitVec 64) → State → Prop} :
    RelCT isa (PW P e X) encFail fun _ _ => True := by
  have hk64 := hL.k64
  refine RelCT.seq (R := PW P e fun _ _ => True) (pw_wp (pw_seq_tr [.x11, .x12, .x13]
    (fun r => if r = .x11 then e.L.out else if r = .x12 then e.L.k else 0)
    (by taint_decide) (by taint_decide)
    fun _ _ _ _ _ _ _ _ hc R hS _ => zeroE_pin hL hP16 hc R hS)
    fun _ _ _ _ _ _ _ _ hc R hS _ => ?_) (pw_taint [] (by taint_decide) nopin)
  refine WP.mono (zeroOut_ok (hc.lay hL hP16 R hS.scr) R hS.out (by rw [hS.k, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]) (by omega) hL.k1024
    (Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨e.L.OUT, by rw [hc.wr]; simp, 0, (BitVec.add_zero _).symm, by simp⟩)
    hL.bO (out_apart hL hP16)) fun _ ⟨_, Su, Ru, _⟩ =>
      In.of_step hL hP16 hc Su (fun r hr => by rw [List.mem_singleton.mp hr]; exact fun _ h => h) Ru hS trivial

/-! ## The prologue and the check of `k` -/

theorem head_ok {Hs Gs : Spec.Mgf1.Hash} {H : Hash} (hD : H.D ≤ 64) {P : Nat} {s : State}
    (h : (encSpec Hs Gs P).pre s) (hP : 16 ≤ P) :
    WP isa (.block (encPrologue ++ chkK H)) (entered s)
      (In (lay Hs.len P s) s.gpr s.v s.mem (KX H.D (lay Hs.len P s).k.toNat)) := by
  have hL := lay_ok h
  rw [WP.block_append_iff]
  refine WP.mono (prologue_ok h) fun t ⟨hc, _, hS⟩ => ?_
  have R : Rep t.mem (lay Hs.len P s).Q (lay Hs.len P s).scr (fun o => t.mem (off (lay Hs.len P s).scr o))
      (fun j => word t.mem (lay Hs.len P s).Q (8 * j)) := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  have hk3 : (fun j => word t.mem (lay Hs.len P s).Q (8 * j)) 21 = BitVec.ofNat 64 (lay Hs.len P s).k.toNat :=
    hS.k.trans (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])
  exact WP.mono (chkK_ok (H := H) (hc.lay hL hP R hS.scr) R hk3 hL.k1024 (by omega))
    fun _ ⟨_, S1, hm1, x11⟩ => In.of_step hL hP hc S1 nil_ws (by rw [hm1]; exact R) hS x11

/-- Two calls whose public data agree, in the inner frame. -/
def Entered (Hs Gs : Spec.Mgf1.Hash) (P : Nat) (a b : State) : Prop :=
  ∃ s₁ s₂, (encSpec Hs Gs P).pre s₁ ∧ (encSpec Hs Gs P).pre s₂ ∧ (encSpec Hs Gs P).pub s₁ s₂ ∧
    a = entered s₁ ∧ b = entered s₂

theorem head_ct (Hs Gs : Spec.Mgf1.Hash) {H : Hash} (hD : H.D ≤ 64) {P : Nat} (hP : 16 ≤ P) :
    RelCT isa (Entered Hs Gs P) (.block (encPrologue ++ chkK H))
      fun a b => ∃ e : Env, e.L.D = Hs.len ∧ PW P e (KX H.D e.L.k.toNat) a b := by
  intro a b ta tb a' b' ⟨s₁, s₂, h₁, h₂, hp, ea, eb⟩ e₁ e₂
  subst ea eb
  sig_pub [Spec.RsaOaep.encryptContract, Spec.RsaOaep.encryptSig, AArch64.abi, AArch64.argRegs,
    _root_.List.range, _root_.List.range.loop, List.append_eq] at hp
  obtain ⟨hsp, hl, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4⟩ := hp
  have ht := (RelCT.taint (A := taint) (P := fun x y => x.sp = y.sp) (Taint.ofRegs [])
    (fun _ _ h => ⟨h, fun _ hr => False.elim (by simp at hr)⟩)
    (check_of_zImm (τ := Taint.ofRegs []) (c' := .block (encPrologue ++ chkK gH)) (by rfl) (by taint_decide))
    _ _ _ _ _ _ (by
      show (entered s₁).sp = (entered s₂).sp
      rw [entered_sp Hs.len P, entered_sp Hs.len P]; simp only [lay, hsp]) e₁ e₂).1
  obtain ⟨_, u₁, x₁, y₁⟩ := head_ok hD h₁ hP
  obtain ⟨_, u₂, x₂, y₂⟩ := head_ok hD h₂ hP
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  have e : lay Hs.len P s₂ = lay Hs.len P s₁ := by
    simp only [lay, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4, hsp]
  obtain ⟨hn, he⟩ := leak_split hl (by rw [bytesAt_length, bytesAt_length, h3])
  refine ⟨ht, ⟨lay Hs.len P s₁, s₁.gpr, s₂.gpr, s₁.v, s₂.v, s₁.mem, s₂.mem⟩, rfl, lay_ok h₁, rfl, ⟨?_, ?_⟩,
    y₁, e ▸ y₂⟩
  · show Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x2) (s₁.gpr .x3).toNat =
      Spec.Rsa.bytesAt s₂.mem (s₁.gpr .x2) (s₁.gpr .x3).toNat
    rw [hn, h2, h3]
  · show Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x4) (s₁.gpr .x5).toNat =
      Spec.Rsa.bytesAt s₂.mem (s₁.gpr .x4) (s₁.gpr .x5).toNat
    rw [he, h4, h5]

theorem pub_sp {Hs Gs : Spec.Mgf1.Hash} {P : Nat} {s₁ s₂ : State} (h : (encSpec Hs Gs P).pub s₁ s₂) :
    s₁.sp = s₂.sp := by
  sig_pub [Spec.RsaOaep.encryptContract, Spec.RsaOaep.encryptSig, AArch64.abi, AArch64.argRegs,
    _root_.List.range, _root_.List.range.loop, List.append_eq] at h
  exact h.1

/-- `In` with `X`, as `In` with nothing more. -/
theorem In.forget {L : ELay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem}
    {X : (Nat → BitVec 64) → State → Prop} {t : State} (h : In L g vv m₀ X t) : In L g vv m₀ (fun _ _ => True) t :=
  ⟨h.1, h.2.choose, h.2.choose_spec.choose, h.2.choose_spec.choose_spec.1, h.2.choose_spec.choose_spec.2.1, trivial⟩

variable {Hl Gm : Hash} (hH : StreamOK Hl.stream) (hG : StreamOK Gm.stream)

include hH hG in
theorem enc_ct {Hs Gs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = Hl.D)
    (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = Gm.D) (hGv : Proof.Mgf1.Valid Gs) (pv : PubImpl)
    {P : Nat} (hP : pv.S + 1 ≤ P) (hP16 : 16 ≤ P) :
    ConstantTime isa (encSpec Hs Gs P).pre (encSpec Hs Gs P).pub (encrypt Hl Gm pv.name pv.code) := by
  obtain ⟨-, hzF, -, hzDF, -⟩ := sizes hH
  have hD64 : Hl.D ≤ 64 := Nat.le_trans hzDF hzF
  refine RelCT.constantTime (RelCT.pushFrame (fun _ _ h => pub_sp h.2.2) (RelCT.alloc (R := fun _ _ => True) ?_))
  rw [encBody_eq]
  refine ((head_ct Hs Gs hD64 hP16).seq (Q := fun _ _ => True) ?_).mono ?_ fun _ _ _ => trivial
  · refine RelCT.ite (fun a b ⟨e, _, _, _, _, ⟨_, _, _, _, _, xa⟩, ⟨_, _, _, _, _, xb⟩⟩ => by
      rw [eval_nonzero, eval_nonzero, xa, xb]) ?_ ?_
    · intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨⟨e, _, hL, hP', hp⟩, _⟩ e₁ e₂
      exact encFail_tr hL (hP' ▸ hP16) _ _ _ _ _ _ ⟨hL, hP', hp⟩ e₁ e₂
    intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨⟨e, hDe, hL, hP', hk, f₁, f₂⟩, hb⟩ e₁ e₂
    have hP16' : 16 ≤ e.L.P := hP' ▸ hP16
    have hkD : 2 * Hl.D + 2 ≤ e.L.k.toNat := by
      by_contra hc
      rw [eval_nonzero, f₁.2.choose_spec.choose_spec.2.2, ifn (by omega)] at hb
      exact absurd hb (by decide)
    refine (RelCT.seq (Q := fun _ _ => True) (pw_blk (X' := MX Hl.D e.L.k.toNat e.L.ml.toNat) []
      (check_of_zImm (τ := Taint.ofRegs []) (c' := .block (chkMsg gH)) (by rfl) (by taint_decide)) nopin
      fun _ _ _ _ _ _ _ _ hc R hS _ => WP.mono (chkMsg_ok (H := Hl) (hc.lay hL hP16' R hS.scr) R
        (by rw [hS.k, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by rw [hS.ml, BitVec.ofNat_toNat, BitVec.setWidth_eq])
        hL.k1024 e.L.ml.isLt hkD)
        fun _ ⟨_, Su, hm, x11⟩ => In.of_step hL hP16' hc Su nil_ws (by rw [hm]; exact R) hS x11) ?_) _ _ _ _ _ _
      ⟨hL, hP', hk, f₁.forget, f₂.forget⟩ e₁ e₂
    refine RelCT.ite (fun a b ⟨_, _, _, ⟨_, _, _, _, _, xa⟩, ⟨_, _, _, _, _, xb⟩⟩ => by
      rw [eval_nonzero, eval_nonzero, xa, xb]) ?_ ?_
    · exact (encFail_tr hL hP16').mono (fun _ _ h => h.1) fun _ _ h => h
    · intro a₁ a₂ u₁ u₂ a₁' a₂' ⟨⟨_, _, _, g₁, g₂⟩, hb'⟩ e₁ e₂
      have hmk : e.L.ml.toNat ≤ e.L.k.toNat - (2 * Hl.D + 2) := by
        by_contra hc
        rw [eval_nonzero, g₁.2.choose_spec.choose_spec.2.2, ifn (by omega)] at hb'
        exact absurd hb' (by decide)
      exact encMain_tr hH hG hHh hGh hGl hGv pv hL (hP' ▸ hP) hP16' (hDe.trans hHl) (by omega) _ _ _ _ _ _
        ⟨hL, hP', hk, g₁.forget, g₂.forget⟩ e₁ e₂
  · rintro _ _ ⟨_, _, ⟨s₁, s₂, ⟨h₁, h₂, hp⟩, rfl, rfl⟩, rfl, rfl⟩
    exact ⟨s₁, s₂, h₁, h₂, hp, rfl, rfl⟩

/-- The stack below the frames: the callee's, and at least 16 bytes. -/
def encP (pv : PubImpl) : Nat := max pv.stack 16

/-- The stack the function uses: the callee's and the frames'. -/
def encStack (pv : PubImpl) : Nat := encP pv + 288

include hH hG in
/-- `vg_rsa_oaep_<H>_mgf1_<G>_encrypt`, with `pv`. -/
theorem enc_verified {Hs Gs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = Hl.D)
    (hHv : Proof.Mgf1.Valid Hs) (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = Gm.D)
    (hGv : Proof.Mgf1.Valid Gs) (pv : PubImpl)
    (hsat : ∃ s, (Spec.RsaOaep.encryptContract Hs Gs AArch64.abi (encStack pv)).pre s) :
    Verified AArch64.target (encrypt Hl Gm pv.name pv.code)
      (Spec.RsaOaep.encryptContract Hs Gs AArch64.abi (encStack pv)) := by
  have hP : pv.S + 1 ≤ encP pv := pv.stack_eq ▸ Nat.le_max_left _ _
  have hP16 : 16 ≤ encP pv := Nat.le_max_right _ _
  exact Verified.of_correct (fun _ h => by
    obtain ⟨t, s', he, hp⟩ := enc_ok hH hG hHh hHl hHv hGh hGl hGv pv hP hP16 h
    exact ⟨t, s', he, hp⟩) (enc_ct hH hG hHh hHl hGh hGl hGv pv hP hP16) (Contract.Implies.refl hsat)

end VG.Proof.RsaOaep.AArch64.Enc
