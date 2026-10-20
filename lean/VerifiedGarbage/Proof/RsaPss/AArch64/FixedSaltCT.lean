module

public import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyCTMain
import VerifiedGarbage.Proof.RsaPss.AArch64.FixedSaltCopy
import VerifiedGarbage.Proof.RsaPss.AArch64.CtHashCT
import VerifiedGarbage.Proof.RsaPss.AArch64.SignEnc
import VerifiedGarbage.Proof.RsaPss.AArch64.CtHash
import VerifiedGarbage.Proof.RsaPss.AArch64.RelSplit
meta import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyCTMain
meta import VerifiedGarbage.Proof.RsaPss.AArch64.FixedSaltCopy
meta import VerifiedGarbage.Proof.RsaPss.AArch64.CtHashCT
meta import VerifiedGarbage.Proof.RsaPss.AArch64.SignEnc
meta import VerifiedGarbage.Proof.RsaPss.AArch64.CtHash
meta import VerifiedGarbage.Proof.RsaPss.AArch64.RelSplit
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Two
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Two
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset

/-! Fixed-length verification copies and hashes only public lengths. -/

@[expose] public section
namespace VG.Proof.RsaPss.AArch64.Vfy.Fixed
open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.MlKem.AArch64 (Only Keep wp_nil wp_add wp_sub wp_addImm eval_zero)
open VG.Proof.RsaPkcs1Sig.AArch64 (Two Pins two_taint two_post two_map two_ite wp_ldrSp)
open VG.Proof.RsaPss.AArch64.Sgn (fb)

abbrev salt (a : State) : Nat := (a.gpr .x7).toNat
abbrev blocks (H : Hash) (a : State) : Nat := (8 + H.D + salt a + H.P.L) / H.P.B + 1
abbrev FV (D K : Nat) (a u : State) : Prop :=
  VR D K (vregs D) vslots a u ∧ salt a < dbA D a

theorem clear_ct {D K : Nat} : RelCT isa (Two (FV D K)) clearY (Two (FV D K)) :=
  two_post (two_taint [.x20] (VR.pins fun r hr => by simp at hr; exact .inl hr) (by taint_decide))
    fun a u ⟨h, hs⟩ => WP.mono (clearY_ok h.L (fun _ _ => rfl)) fun _ ⟨k, f, _⟩ =>
      ⟨h.keep k (nk_of (by decide)) (by decide) f (vslots_S h.L), hs⟩

variable {H : Hash} (hH : HashOK H)
include hH in
theorem digest_ct {K : Nat} : RelCT isa (Two (FV H.D K)) (copyDigest H) (Two (FV H.D K)) := by
  refine two_post (Φ := FV H.D K) ?_ fun a u ⟨h, hs⟩ => WP.mono
    (copyDigest_ok hH h.L (fun _ _ => rfl) h.sdig h.dig.1 h.dig.2) fun _ ⟨k, f, _⟩ =>
      ⟨h.keep k (nk_of (by decide)) (by decide) f (vslots_S h.L), hs⟩
  unfold copyDigest
  refine RelCT.seq_block_append (M := isa) (l₁ := [ld .x11 sDig]) ?_
  refine two_step (Ψ := fun a u => VR H.D K (vregs H.D ++ [(.x11, fun a => a.gpr .x4)]) vslots a u)
    (two_taint [] (pins_nil fun a s₁ s₂ h₁ h₂ => by rw [h₁.1.L.sp, h₂.1.L.sp]) (by taint_decide))
    (fun a u hu => ?_)
    (two_taintE [.x11, .x20] (VR.pins' fun r hr => by simp at hr; rcases hr with rfl | rfl <;> simp)
      (c' := Code.eraseOff (.seq (.block [.addImm .x .x14 .x20 (oY + 8), movi .x12 zH.D])
        Impl.RsaPkcs1Sig.AArch64.copyLoop)) rfl (by taint_decide))
  obtain ⟨h, _⟩ := hu
  unfold ld
  refine wp_ldrSp (by decide) (ld_slot h.L (by decide)) fun u' o e =>
    wp_nil (h.congr o.sp o.rd o.wr (o.get .x20) (fun q hq => ?_) fun q hq => by rw [o.mem]; exact h.sl q hq)
  rcases List.mem_append.mp hq with hq | hq
  · rw [o.get q.1 (nk_of (by decide) q hq)]; exact h.r q hq
  · rw [List.mem_singleton.mp hq, e, h.L.sp]; exact h.sdig

include hH in
theorem copy_ct {K : Nat} : RelCT isa (Two (FV H.D K)) (Impl.RsaPss.AArch64.FixedSalt.copySalt H)
    (Two (FV H.D K)) := by
  refine two_post (Φ := FV H.D K) ?_ fun a u ⟨h, hs⟩ => ?_
  rotate_left
  · have := h.ok.db
    refine WP.mono (VG.Proof.RsaPss.AArch64.FixedSalt.copySalt_ok hH h.L (fun _ _ => rfl)
      (e := oEm + loA a) (db := dbA H.D a) (sl := salt a) (by omega) (by unfold oEm oY; omega)
      (by omega) (by omega) h.x24 h.x25
      (by rw [h.ssl, BitVec.ofNat_toNat, BitVec.setWidth_eq])) fun _ ⟨k, f, _⟩ =>
        ⟨h.keep k (nk_of (by decide)) (by decide) f (vslots_S h.L), hs⟩
  unfold Impl.RsaPss.AArch64.FixedSalt.copySalt
  refine two_step (Ψ := fun a t => t.sp = fb a ∧
      t.gpr .x11 = off (scr a) (oEm + loA a) + BitVec.ofNat 64 (dbA H.D a) - a.gpr .x7 ∧
      t.gpr .x12 = a.gpr .x7 ∧ t.gpr .x14 = off (scr a) (oY + 8 + H.D))
    (two_taintE [] (pins_nil fun a s₁ s₂ h₁ h₂ => by rw [h₁.1.L.sp, h₂.1.L.sp])
      (c' := Code.eraseOff (.block [.add .x .x11 .x24 .x25, ld .x12 sSaltLen,
        .sub .x .x11 .x11 .x12, .addImm .x .x14 .x20 (oY + 8 + zH.D)])) rfl (by taint_decide))
    (fun a u ⟨h, _⟩ => ?_) ?_
  · refine wp_add fun u₁ o₁ e₁ => wp_ldrSp (by decide)
      (by rw [o₁.sp, o₁.rd, o₁.wr]; exact ld_slot h.L (by decide)) fun u₂ o₂ e₂ =>
      wp_sub fun u₃ o₃ e₃ => wp_addImm (by have := hH.sizes.DN; have := hH.N_le; unfold oY; omega)
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
theorem len_ct {K : Nat} : RelCT isa (Two (FV H.D K)) (.block (signLen H))
    (Two fun a u => VR H.D K (regs H.D) (slots H) a u ∧ salt a < dbA H.D a) := by
  refine two_post (two_taintE [] (pins_nil fun a s₁ s₂ h₁ h₂ => by rw [h₁.1.L.sp, h₂.1.L.sp])
    (c' := Code.eraseOff (.block (signLen zH))) rfl (by taint_decide)) fun a u ⟨h, hs⟩ => ?_
  have := h.ok.db
  refine WP.mono (signLen_ok hH h.L (sl := salt a)
    (by rw [h.ssl, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by omega)) fun u' ⟨k, x22, m⟩ =>
      ⟨h.congr k.sp k.rd k.wr (k.get .x20) (fun q hq => ?_) (fun q hq => ?_), hs⟩
  · rcases List.mem_append.mp hq with hq | hq
    · rw [k.get q.1 (nk_of (by decide) q hq)]; exact h.r q hq
    · rw [List.mem_singleton.mp hq]; exact x22
  · rcases List.mem_append.mp hq with hq | hq
    · rw [m, slot_keep (frame_slot _ _ sNb _) (vslots_sNb q hq)]; exact h.sl q hq
    · rw [List.mem_singleton.mp hq, m, Mem.readW_writeW_self64]

include hH in
theorem hash_ct {K : Nat} (hc : PssChecks H.P H.D) :
    RelCT isa (Two fun a u => VR H.D K (regs H.D) (slots H) a u ∧ salt a < dbA H.D a) (ctHash H) (Two (VR H.D K (vregs H.D) vslots)) := by
  have hDN := hH.sizes.DN
  have hN := hH.N_le
  have hL := hH.L
  have hB0 := hH.B_pos
  have hBl := hH.B_le
  have hlg : 2 ^ lgB H = H.P.B ∧ lgB H < 64 := by
    unfold lgB
    rcases hH.sizes.B with h | h <;> rw [h]
    · rw [show (64 : Nat) = 2 ^ 6 from rfl, Nat.log2_two_pow]; decide
    · rw [show (128 : Nat) = 2 ^ 7 from rfl, Nat.log2_two_pow]; decide
  have hb : ∀ a : State, salt a ≤ 1024 → 8 + H.D + salt a + 1 + H.P.L ≤ blocks H a * H.P.B ∧ blocks H a * H.P.B ≤ 2048 :=
    fun a hs => by
      have hnb1 := Nat.lt_div_mul_add (a := 8 + H.D + salt a + H.P.L) (b := H.P.B) hB0
      have hnb2 := Nat.div_mul_le_self (8 + H.D + salt a + H.P.L) H.P.B
      have hnbB : ((8 + H.D + salt a + H.P.L) / H.P.B + 1) * H.P.B =
          (8 + H.D + salt a + H.P.L) / H.P.B * H.P.B + H.P.B := Nat.succ_mul _ _
      show _ ≤ ((8 + H.D + salt a + H.P.L) / H.P.B + 1) * H.P.B ∧ ((8 + H.D + salt a + H.P.L) / H.P.B + 1) * H.P.B ≤ 2048
      rw [hnbB]; omega
  have x19 : ∀ {a u : State}, VR H.D K (regs H.D) (slots H) a u → u.gpr .x19 = off (scr a) oSt := fun h =>
    h.r (.x19, fun a => off (scr a) oSt) (by simp [regs, vregs])
  have x21 : ∀ {a u : State}, VR H.D K (regs H.D) (slots H) a u → u.gpr .x21 = off (scr a) oDig := fun h =>
    h.r (.x21, fun a => off (scr a) oDig) (by simp [regs, vregs])
  have x22 : ∀ {a u : State}, VR H.D K (regs H.D) (slots H) a u → u.gpr .x22 = BitVec.ofNat 64 (8 + H.D + salt a) :=
    fun h => h.r (.x22, fun a => BitVec.ofNat 64 (8 + H.D + salt a)) (by simp [regs])
  have nb : ∀ {a u : State}, VR H.D K (regs H.D) (slots H) a u →
      u.mem.readW (off (fb a) sNb) 64 = BitVec.ofNat 64 (blocks H a) := fun h =>
    h.sl (sNb, fun a => BitVec.ofNat 64 (blocks H a)) (by simp [slots])
  refine two_post (two_map (fun a => (⟨fb a, scr a, blocks H a, none⟩ : HA)) (fun a u ⟨h, hsalt⟩ => {
      L := h.L
      x19 := x19 h
      x21 := x21 h
      nb := nb h
      len := ⟨8 + H.D + salt a, x22 h, (hb a (by have := h.ok.db; omega)).1⟩
      hnb := (hb a (by have := h.ok.db; omega)).2
      fx := fun _ e => nomatch e }) (ctHash_ct hH hc)) fun a u ⟨h, hsalt⟩ => ?_
  have hs : salt a ≤ 1024 := by have := h.ok.db; omega
  refine WP.mono (ctHashWith_out hH (pad80 H) h.L (fun _ _ => rfl) (x19 h) (x21 h) (x22 h) (nb h) (hb a hs).1
    (hb a hs).2 fun L' R' h22' hNb' => ?_) fun u' O => ?_
  · exact WP.mono (pad80_ok H L' R' hlg.1 hlg.2 (by omega) (hb a hs).2 (by have := (hb a hs).1; omega) h22' hNb')
      fun _ ⟨k, f, r⟩ => ⟨k.mono, f, r⟩
  refine h.congr O.sp O.rd O.wr (O.cs .x20 (by decide)) (fun q hq => ?_) fun q hq => ?_
  · rw [O.cs q.1 ((by decide : ∀ r ∈ [Reg.x19, .x21, .x23, .x24, .x25], r ∈ [Reg.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x28]) _ (vregs_fst hq))]; exact h.r q (List.mem_append_left _ hq)
  · rw [slot_keep O.fr fun r hr => ?_]
    · exact h.sl q (List.mem_append_left _ hq)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.L.dFS.sub_left (Offset.sub_base _ (vslots_fb q hq))
    · exact slot_not_below _ (vslots_fb q hq)

include hH in
theorem finish_ct {K : Nat} (hc : PssChecks H.P H.D) :
    RelCT isa (Two (FV H.D K)) (Impl.RsaPss.AArch64.FixedSalt.finish H) (Two fun a t => t.sp = fb a) := by
  unfold Impl.RsaPss.AArch64.FixedSalt.finish seqs seqs seqs seqs seqs
  exact RelCT.seq clear_ct (RelCT.seq (digest_ct hH) (RelCT.seq (copy_ct hH)
    (RelCT.seq (len_ct hH) (RelCT.seq (hash_ct hH hc) (cmpH_vct hH)))))

end VG.Proof.RsaPss.AArch64.Vfy.Fixed

namespace VG.Proof.RsaPss.AArch64.Vfy
open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.MlKem.AArch64 (wp_nil eval_zero)
open VG.Proof.RsaPkcs1Sig.AArch64 (Two two_taint two_post two_map two_ite wp_ldrSp)
open VG.Proof.RsaPss.AArch64.Sgn (fb)

variable {H : Hash} (hH : HashOK H)
include hH in
theorem select_ct {K : Nat} (hc : PssChecks H.P H.D) :
    RelCT isa (Two fun a u => VR H.D K (vregs H.D) vslots a u ∧ PS H.D a u)
      (Impl.RsaPss.AArch64.FixedSalt.select H) (Two fun a t => t.sp = fb a) := by
  unfold Impl.RsaPss.AArch64.FixedSalt.select
  refine two_step (Ψ := fun a u => (VR H.D K (vregs H.D) vslots a u ∧ PS H.D a u) ∧ u.gpr .x9 = anyV a)
    (two_taint [] (pins_nil fun a s₁ s₂ h₁ h₂ => by rw [h₁.1.L.sp, h₂.1.L.sp]) (by taint_decide))
    (fun a u ⟨h, p⟩ => ?_) ?_
  · unfold ld
    refine wp_ldrSp (by decide) (ld_slot h.L (by decide)) fun t o e => wp_nil ?_
    exact ⟨⟨h.only o (nk_of (by decide)) (by decide), by obtain ⟨pos, hp, ep⟩ := p; exact ⟨pos, hp, by rw [o.mem]; exact ep⟩⟩, by rw [e, h.L.sp, h.sany]⟩
  · refine two_ite (fun a s₁ s₂ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.2, h₂.2]) ?_ ?_
    · refine two_map id (fun a u h => ?_) (Fixed.finish_ct hH (K := K) hc)
      have ha : anyV a = 0 := by
        have hb := h.2
        rw [eval_zero, h.1.2] at hb
        exact beq_iff_eq.mp (Option.some.inj hb)
      exact ⟨h.1.1.1, h.1.1.1.ok.salt ha⟩
    · refine two_map (Φ' := fun a u => VR H.D K (vregs H.D) vslots a u ∧ PS H.D a u) id (fun _ _ h => h.1.1) ?_
      unfold seqs seqs seqs seqs seqs seqs
      exact RelCT.seq clearY_vct (RelCT.seq (copyDigest_vct hH) (RelCT.seq (copyDb_vct hH)
        (RelCT.seq (shift_vct hH) (RelCT.seq (verifyNb_vct hH) (RelCT.seq (ctHash_vct hH hc) (cmpH_vct hH))))))

/-- Both verification paths branch and access memory only through public values. -/
theorem check_ct {K : Nat} {G : Spec.Mgf1.Hash} (hGh : ∀ x, G.hash x = hH.SH.H.hash x) (hGl : G.len = H.D)
    (hG : Proof.Mgf1.Valid G) (hc : PssChecks H.P H.D) :
    RelCT isa (Two (VR H.D K (vregs H.D) vslots))
      (seqs [.block acc0, mgfXor H, .block clearTop, posScan, posCheck, Impl.RsaPss.AArch64.FixedSalt.select H])
      (Two fun a t => t.sp = fb a) := by
  unfold seqs seqs seqs seqs seqs
  exact RelCT.seq acc0_vct (RelCT.seq (mgfXor_vct hH hGh hGl hG hc) (RelCT.seq clearTop_vct
    (RelCT.seq posScan_vct (RelCT.seq posCheck_vct (select_ct hH hc)))))

end VG.Proof.RsaPss.AArch64.Vfy
