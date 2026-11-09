module

public import VerifiedGarbage.Proof.RsaPss.AArch64.ChkCTMain
import VerifiedGarbage.Proof.RsaPss.AArch64.FixedSaltCopy
import VerifiedGarbage.Proof.RsaPss.AArch64.CtHashCT
import VerifiedGarbage.Proof.RsaPss.AArch64.SignEnc
import VerifiedGarbage.Proof.RsaPss.AArch64.CtHash
import VerifiedGarbage.Proof.Framework.RelSplit
meta import VerifiedGarbage.Proof.RsaPss.AArch64.ChkCTMain
meta import VerifiedGarbage.Proof.RsaPss.AArch64.FixedSaltCopy
meta import VerifiedGarbage.Proof.RsaPss.AArch64.CtHashCT
meta import VerifiedGarbage.Proof.RsaPss.AArch64.SignEnc
meta import VerifiedGarbage.Proof.RsaPss.AArch64.CtHash
meta import VerifiedGarbage.Proof.Framework.RelSplit
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Two
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Two
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset

/-! Fixed-length verification copies and hashes only public lengths. -/

@[expose] public section
namespace VG.Proof.RsaPss.AArch64.Chk.Fixed
open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.MlKem.AArch64 (Only Keep wp_nil wp_add wp_sub wp_addImm eval_zero)
open VG.Proof.RsaPkcs1Sig.AArch64 (Two Pins two_taint two_post two_map two_ite wp_ldrSp)
open VG.Proof.RsaPss.AArch64.Sgn (fb)

abbrev salt (a : State) : Nat := (a.gpr .x4).toNat
abbrev blocks (H : Hash) (a : State) : Nat := (8 + H.D + salt a + H.P.L) / H.P.B + 1
abbrev FV (T : Tabs) (D : Nat) (a u : State) : Prop :=
  VR T D (vregs D) vslots a u ∧ salt a < dbA D a

theorem clear_ct {T : Tabs} {D : Nat} : RelCT isa (Two (FV T D)) clearY (Two (FV T D)) :=
  two_post (two_taint [.x20] (VR.pins fun r hr => by simp at hr; exact .inl hr) (by taint_decide))
    fun a u ⟨h, hs⟩ => WP.mono_syms (clearY_ok h.L (fun _ _ => rfl)) fun _ ⟨k, f, _⟩ sy =>
      ⟨h.keep k (nk_of (by decide)) (by decide) f (vslots_S h.L) sy, hs⟩

variable {T : Tabs} (hH : HashOK T.H)
include hH in
theorem digest_ct : RelCT isa (Two (FV T T.H.D)) (copyDigest T.H) (Two (FV T T.H.D)) := by
  refine two_post (Φ := FV T T.H.D) ?_ fun a u ⟨h, hs⟩ => WP.mono_syms
    (copyDigest_ok hH h.L (fun _ _ => rfl) h.sdig h.dig.1 h.dig.2) fun _ ⟨k, f, _⟩ sy =>
      ⟨h.keep k (nk_of (by decide)) (by decide) f (vslots_S h.L) sy, hs⟩
  unfold copyDigest
  refine RelCT.seq_block_append (M := isa) (l₁ := [ld .x11 sDig]) ?_
  refine two_step (Ψ := fun a u => VR T T.H.D (vregs T.H.D ++ [(.x11, fun a => a.gpr .x0)]) vslots a u)
    (two_taint [] (pins_nil fun a s₁ s₂ h₁ h₂ => by rw [h₁.1.L.sp, h₂.1.L.sp]) (by taint_decide))
    (fun a u hu => ?_)
    (two_taintE [.x11, .x20] (VR.pins' fun r hr => by simp at hr; rcases hr with rfl | rfl <;> simp)
      (c' := Code.eraseOff (.seq (.block [.addImm .x .x14 .x20 (oY + 8), movi .x12 zH.D])
        Impl.RsaPkcs1Sig.AArch64.copyLoop)) rfl (by taint_decide))
  obtain ⟨h, _⟩ := hu
  unfold ld
  refine WP.of_syms ?_
  refine wp_ldrSp (by decide) (ld_slot h.L (by decide)) fun u' o e =>
    wp_nil fun sy => (h.congr o.sp o.rd o.wr (o.get .x20) (fun q hq => ?_)
      (fun q hq => by rw [o.mem]; exact h.sl q hq) sy (by rw [o.mem]; exact Frame.refl _ _))
  rcases List.mem_append.mp hq with hq | hq
  · rw [o.get q.1 (nk_of (by decide) q hq)]; exact h.r q hq
  · rw [List.mem_singleton.mp hq, e, h.L.sp]; exact h.sdig

include hH in
theorem copy_ct : RelCT isa (Two (FV T T.H.D)) (Impl.RsaPss.AArch64.FixedSalt.copySalt T.H)
    (Two (FV T T.H.D)) := by
  refine two_post (Φ := FV T T.H.D) ?_ fun a u ⟨h, hs⟩ => ?_
  rotate_left
  · have := h.ok.db
    refine WP.mono_syms (VG.Proof.RsaPss.AArch64.FixedSalt.copySalt_ok hH h.L (fun _ _ => rfl)
      (e := oEm + loA a) (db := dbA T.H.D a) (sl := salt a) (by omega_arith) (by unfold oEm oY; omega_arith)
      (by omega_arith) (by omega_arith) h.x24 h.x25
      (by rw [h.ssl, BitVec.ofNat_toNat, BitVec.setWidth_eq])) fun _ ⟨k, f, _⟩ sy =>
        ⟨h.keep k (nk_of (by decide)) (by decide) f (vslots_S h.L) sy, hs⟩
  unfold Impl.RsaPss.AArch64.FixedSalt.copySalt
  refine two_step (Ψ := fun a t => t.sp = fb a ∧
      t.gpr .x11 = off (scr a) (oEm + loA a) + BitVec.ofNat 64 (dbA T.H.D a) - a.gpr .x4 ∧
      t.gpr .x12 = a.gpr .x4 ∧ t.gpr .x14 = off (scr a) (oY + 8 + T.H.D))
    (two_taintE [] (pins_nil fun a s₁ s₂ h₁ h₂ => by rw [h₁.1.L.sp, h₂.1.L.sp])
      (c' := Code.eraseOff (.block [.add .x .x11 .x24 .x25, ld .x12 sSaltLen,
        .sub .x .x11 .x11 .x12, .addImm .x .x14 .x20 (oY + 8 + zH.D)])) rfl (by taint_decide))
    (fun a u ⟨h, _⟩ => ?_) ?_
  · refine wp_add fun u₁ o₁ e₁ => wp_ldrSp (by decide)
      (by rw [o₁.sp, o₁.rd, o₁.wr]; exact ld_slot h.L (by decide)) fun u₂ o₂ e₂ =>
      wp_sub fun u₃ o₃ e₃ => wp_addImm (by have := hH.sizes.DN; have := hH.N_le; unfold oY; omega_arith)
        fun u₄ o₄ e₄ => wp_nil ?_
    refine ⟨by rw [o₄.sp, o₃.sp, o₂.sp, o₁.sp, h.L.sp], ?_, ?_, ?_⟩
    · rw [o₄.get .x11, e₃, o₂.get .x11, e₁, h.x24, h.x25, e₂, o₁.sp, h.L.sp, o₁.mem, h.ssl]
    · rw [o₄.get .x12, o₃.get .x12, e₂, o₁.sp, h.L.sp, o₁.mem, h.ssl]
    · rw [e₄, o₃.get .x20, o₂.get .x20, o₁.get .x20, h.L.x20]
  · exact two_taint [.x11, .x12, .x14] (fun a s₁ s₂ h₁ h₂ =>
      ⟨by rw [h₁.1, h₂.1], fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h₁.2.1, h₂.2.1]
        · rw [h₁.2.2.1, h₂.2.2.1]
        · rw [h₁.2.2.2, h₂.2.2.2]⟩) (by taint_decide)

def regs (D : Nat) : List (Reg × (State → BitVec 64)) :=
  vregs D ++ [(.x22, fun a => BitVec.ofNat 64 (8 + D + salt a))]
def slots (H : Hash) : List (Nat × (State → BitVec 64)) :=
  vslots ++ [(sNb, fun a => BitVec.ofNat 64 (blocks H a))]

include hH in
theorem len_ct : RelCT isa (Two (FV T T.H.D)) (.block (signLen T.H))
    (Two fun a u => VR T T.H.D (regs T.H.D) (slots T.H) a u ∧ salt a < dbA T.H.D a) := by
  refine two_post (two_taintE [] (pins_nil fun a s₁ s₂ h₁ h₂ => by rw [h₁.1.L.sp, h₂.1.L.sp])
    (c' := Code.eraseOff (.block (signLen zH))) rfl (by taint_decide)) fun a u ⟨h, hs⟩ => ?_
  have := h.ok.db
  refine WP.mono_syms (signLen_ok hH h.L (sl := salt a)
    (by rw [h.ssl, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by omega_arith)) fun u' ⟨k, x22, m⟩ sy =>
      ⟨h.congr k.sp k.rd k.wr (k.get .x20) (fun q hq => ?_) (fun q hq => ?_) sy
        (by rw [m]; exact (frame_slot _ _ sNb _).mono (by simp [mgfWr])), hs⟩
  · rcases List.mem_append.mp hq with hq | hq
    · rw [k.get q.1 (nk_of (by decide) q hq)]; exact h.r q hq
    · rw [List.mem_singleton.mp hq]; exact x22
  · rcases List.mem_append.mp hq with hq | hq
    · rw [m, slot_keep (frame_slot _ _ sNb _) (vslots_sNb q hq)]; exact h.sl q hq
    · rw [List.mem_singleton.mp hq, m, Mem.readW_writeW_self64]

include hH in
theorem hash_ct (hc : PssChecks T.H.P T.H.D) (hdo : DigOK T.H.P) :
    RelCT isa (Two fun a u => VR T T.H.D (regs T.H.D) (slots T.H) a u ∧ salt a < dbA T.H.D a) (ctHash T.f T.H) (Two (VR T T.H.D (vregs T.H.D) vslots)) := by
  have hDN := hH.sizes.DN
  have hN := hH.N_le
  have hL := hH.L
  have hB0 := hH.B_pos
  have hBl := hH.B_le
  have hlg : 2 ^ lgB T.H = T.H.P.B ∧ lgB T.H < 64 := by
    unfold lgB
    rcases hH.sizes.B with h | h <;> rw [h]
    · rw [show (64 : Nat) = 2 ^ 6 from rfl, Nat.log2_two_pow]; decide
    · rw [show (128 : Nat) = 2 ^ 7 from rfl, Nat.log2_two_pow]; decide
  have hb : ∀ a : State, salt a ≤ 1024 → 8 + T.H.D + salt a + 1 + T.H.P.L ≤ blocks T.H a * T.H.P.B ∧ blocks T.H a * T.H.P.B ≤ 2048 :=
    fun a hs => by
      have hnb1 := Nat.lt_div_mul_add (a := 8 + T.H.D + salt a + T.H.P.L) (b := T.H.P.B) hB0
      have hnb2 := Nat.div_mul_le_self (8 + T.H.D + salt a + T.H.P.L) T.H.P.B
      have hnbB : ((8 + T.H.D + salt a + T.H.P.L) / T.H.P.B + 1) * T.H.P.B =
          (8 + T.H.D + salt a + T.H.P.L) / T.H.P.B * T.H.P.B + T.H.P.B := Nat.succ_mul _ _
      show _ ≤ ((8 + T.H.D + salt a + T.H.P.L) / T.H.P.B + 1) * T.H.P.B ∧ ((8 + T.H.D + salt a + T.H.P.L) / T.H.P.B + 1) * T.H.P.B ≤ 2048
      rw [hnbB]; omega_arith
  have x19 : ∀ {a u : State}, VR T T.H.D (regs T.H.D) (slots T.H) a u → u.gpr .x19 = off (scr a) oSt := fun h =>
    h.r (.x19, fun a => off (scr a) oSt) (by simp [regs, vregs])
  have x21 : ∀ {a u : State}, VR T T.H.D (regs T.H.D) (slots T.H) a u → u.gpr .x21 = off (scr a) oDig := fun h =>
    h.r (.x21, fun a => off (scr a) oDig) (by simp [regs, vregs])
  have x22 : ∀ {a u : State}, VR T T.H.D (regs T.H.D) (slots T.H) a u → u.gpr .x22 = BitVec.ofNat 64 (8 + T.H.D + salt a) :=
    fun h => h.r (.x22, fun a => BitVec.ofNat 64 (8 + T.H.D + salt a)) (by simp [regs])
  have nb : ∀ {a u : State}, VR T T.H.D (regs T.H.D) (slots T.H) a u →
      u.mem.readW (off (fb a) sNb) 64 = BitVec.ofNat 64 (blocks T.H a) := fun h =>
    h.sl (sNb, fun a => BitVec.ofNat 64 (blocks T.H a)) (by simp [slots])
  refine two_post (two_map (fun a => (⟨fb a, scr a, blocks T.H a, none, a.syms T.H.initN, a.syms T.H.compN, a.syms T.dn⟩ : HA)) (fun a u ⟨h, hsalt⟩ => {
      L := h.L
      x19 := x19 h
      x21 := x21 h
      nb := nb h
      len := ⟨8 + T.H.D + salt a, x22 h, (hb a (by have := h.ok.db; omega_arith)).1⟩
      hnb := (hb a (by have := h.ok.db; omega_arith)).2
      fx := fun _ e => nomatch e
      ht := h.ht
      ai := h.names _ (by simp [Tabs.names])
      ac := h.names _ (by simp [Tabs.names])
      ad := h.names _ (by simp [Tabs.names]) }) (ctHash_ct hH hc hdo)) fun a u ⟨h, hsalt⟩ => ?_
  have hs : salt a ≤ 1024 := by have := h.ok.db; omega_arith
  refine WP.mono_syms (ctHashWith_out hH (pad80 T.H) h.L (fun _ _ => rfl) (x19 h) (x21 h) (x22 h) (nb h)
    (hb a hs).1 (hb a hs).2 (fun L' R' h22' hNb' => ?_) h.ht hdo) fun u' O sy => ?_
  · exact WP.mono (pad80_ok T.H L' R' hlg.1 hlg.2 (by omega_arith) (hb a hs).2 (by have := (hb a hs).1; omega_arith) h22' hNb')
      fun _ ⟨k, f, r⟩ => ⟨k.mono, f, r⟩
  refine h.congr O.sp O.rd O.wr (O.cs .x20 (by decide)) (fun q hq => ?_) (fun q hq => ?_) sy
    (O.fr.mono (by simp [mgfWr]))
  · rw [O.cs q.1 ((by decide : ∀ r ∈ [Reg.x19, .x21, .x23, .x24, .x25], r ∈ [Reg.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x28]) _ (vregs_fst hq))]; exact h.r q (List.mem_append_left _ hq)
  · rw [slot_keep O.fr fun r hr => ?_]
    · exact h.sl q (List.mem_append_left _ hq)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.L.dFS.sub_left (Offset.sub_base _ (vslots_fb q hq))
    · exact slot_not_below _ (vslots_fb q hq)

include hH in
theorem finish_ct (hc : PssChecks T.H.P T.H.D) (hdo : DigOK T.H.P) :
    RelCT isa (Two (FV T T.H.D)) (Impl.RsaPss.AArch64.FixedSalt.finish T.f T.H) (Two fun a t => t.sp = fb a) := by
  unfold Impl.RsaPss.AArch64.FixedSalt.finish seqs seqs seqs seqs seqs
  exact RelCT.seq clear_ct (RelCT.seq (digest_ct hH) (RelCT.seq (copy_ct hH)
    (RelCT.seq (len_ct hH) (RelCT.seq (hash_ct hH hc hdo) (cmpH_vct hH)))))

end VG.Proof.RsaPss.AArch64.Chk.Fixed

namespace VG.Proof.RsaPss.AArch64.Chk
open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.MlKem.AArch64 (wp_nil eval_zero)
open VG.Proof.RsaPkcs1Sig.AArch64 (Two two_taint two_post two_map two_ite wp_ldrSp)
open VG.Proof.RsaPss.AArch64.Sgn (fb)

variable {T : Tabs} (hH : HashOK T.H)
include hH in
theorem select_ct (hc : PssChecks T.H.P T.H.D) (hdo : DigOK T.H.P) :
    RelCT isa (Two fun a u => VR T T.H.D (vregs T.H.D) vslots a u ∧ PS T.H.D a u)
      (Impl.RsaPss.AArch64.FixedSalt.select T.f T.H) (Two fun a t => t.sp = fb a) := by
  unfold Impl.RsaPss.AArch64.FixedSalt.select
  refine two_step (Ψ := fun a u => (VR T T.H.D (vregs T.H.D) vslots a u ∧ PS T.H.D a u) ∧ u.gpr .x9 = anyC a)
    (two_taint [] (pins_nil fun a s₁ s₂ h₁ h₂ => by rw [h₁.1.L.sp, h₂.1.L.sp]) (by taint_decide))
    (fun a u ⟨h, p⟩ => ?_) ?_
  · unfold ld
    refine WP.of_syms ?_
    refine wp_ldrSp (by decide) (ld_slot h.L (by decide)) fun t o e => wp_nil fun sy => ?_
    exact ⟨⟨h.only o (nk_of (by decide)) (by decide) sy, by obtain ⟨pos, hp, ep⟩ := p; exact ⟨pos, hp, by rw [o.mem]; exact ep⟩⟩, by rw [e, h.L.sp, h.sany]⟩
  · refine two_ite (fun a s₁ s₂ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.2, h₂.2]) ?_ ?_
    · refine two_map id (fun a u h => ?_) (Fixed.finish_ct hH hc hdo)
      have ha : anyC a = 0 := by
        have hb := h.2
        rw [eval_zero, h.1.2] at hb
        exact beq_iff_eq.mp (Option.some.inj hb)
      exact ⟨h.1.1.1, h.1.1.1.ok.salt ha⟩
    · refine two_map (Φ' := fun a u => VR T T.H.D (vregs T.H.D) vslots a u ∧ PS T.H.D a u) id (fun _ _ h => h.1.1) ?_
      unfold seqs seqs seqs seqs seqs seqs
      exact RelCT.seq clearY_vct (RelCT.seq (copyDigest_vct hH) (RelCT.seq (copyDb_vct hH)
        (RelCT.seq (shift_vct hH) (RelCT.seq (verifyNb_vct hH) (RelCT.seq (ctHash_vct hH hc hdo) (cmpH_vct hH))))))

include hH in
/-- Both verification paths branch and access memory only through public values. -/
theorem check_ct {Gs : Spec.Mgf1.Hash} (hGm : VG.Proof.Pbkdf2.Md.AArch64.Calls.StreamOK T.G)
    (hGh : ∀ x, Gs.hash x = hGm.SH.H.hash x) (hGl : Gs.len = T.G.D) (hGv : Proof.Mgf1.Valid Gs)
    (hc : PssChecks T.H.P T.H.D) (hdo : DigOK T.H.P) :
    RelCT isa (Two (VR T T.H.D (vregs T.H.D) vslots))
      (seqs [.block acc0, mgfXor T.H T.g, .block clearTop, posScan, posCheck,
        Impl.RsaPss.AArch64.FixedSalt.select T.f T.H])
      (Two fun a t => t.sp = fb a) := by
  unfold seqs seqs seqs seqs seqs
  exact RelCT.seq acc0_vct (RelCT.seq (mgfXor_vct hGm hGh hGl hGv) (RelCT.seq clearTop_vct
    (RelCT.seq posScan_vct (RelCT.seq posCheck_vct (select_ct hH hc hdo)))))

end VG.Proof.RsaPss.AArch64.Chk
