import VerifiedGarbage.Proof.RsaPss.AArch64.CtHash
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Two
import VerifiedGarbage.Proof.Framework.AArch64.TaintEraseOff

/-!
# RSASSA-PSS on AArch64: `ctHashWith` is constant time

Two runs of `ctHashWith` with the same frame, working space and number of
blocks (`HA`), hashing messages of any lengths that fit in the blocks
(`HE`), leak the same trace (`ctHashWith_ct`). The pieces between the calls
and the loads of the number of blocks are checked by the taint analysis, on
the code without its immediates (`two_taintE`: the immediates that depend on
the hash function are not read by the analysis) or, for the hash function's
length field and digest code, by `PssChecks`, once for each hash function;
the calls are constant time by their callees' contracts; the loads of the
number of blocks are public by correctness, and the loops go the same way in
both runs.
-/

namespace VG.Proof.RsaPss.AArch64

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_movz wp_addImm wp_lsr wp_lsl)
open VG.Proof.RsaPkcs1Sig.AArch64 (Two Pins two_taint two_post wp_mov wp_ldrSp)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)

/-- Code the taint analysis checks without its immediates. -/
theorem two_taintE {α : Type} {Φ : α → State → Prop} {c c' : Prog isa} (rs : List Reg) (hpin : Pins Φ rs)
    (he : Code.eraseOff c = c') {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (h : (taint.check (VG.AArch64.Taint.ofRegs rs) c' hc).isSome = true) :
    RelCT isa (Two Φ) c fun _ _ => True :=
  two_taint rs hpin (Taint.isSome_check_of_eraseOff he h)

/-- The taint checks of the hash function's code in `ctHashWith`, once for
each hash function: its length field from `ℓ` (secret) and its digest. -/
structure PssChecks (H : Hash) : Prop where
  lenField : ∃ hc, (taint.check (VG.AArch64.Taint.ofRegs [.x20]) (.block (lenField H)) hc).isSome = true
  digestOut : ∃ hc, (taint.check (VG.AArch64.Taint.ofRegs [.x20, .x21]) (.block (digestOut H)) hc).isSome = true

/-- A hash function with every size zero and no code: the code that depends
on a hash function only through its immediates is, without them, that of
`zH` (`Code.eraseOff`), which the taint analysis evaluates. -/
def zH : Hash := ⟨⟨0, 0, 0, 0, [], []⟩, 0, 0, "", .block [], "", .block [], "", .block [], "", .block [], "", "", ""⟩

/-- What two runs of `ctHashWith` share. -/
structure HA where
  F : Addr
  S : Addr
  nbm : Nat

/-- A run of `ctHashWith` and its pieces, with the anchor's frame, working
space and number of blocks: the message's length `ℓ` (secret) fits. -/
structure HE (H : Hash) (a : HA) (u : State) : Prop where
  L : Lay u a.F a.S
  x19 : u.gpr .x19 = off a.S oSt
  x21 : u.gpr .x21 = off a.S oDig
  nb : u.mem.readW (off a.F sNb) 64 = BitVec.ofNat 64 a.nbm
  len : ∃ ℓ, u.gpr .x22 = BitVec.ofNat 64 ℓ ∧ ℓ + 1 + H.P.L ≤ a.nbm * H.P.B
  hnb : a.nbm * H.P.B ≤ 2048

theorem HE.pins {H : Hash} {rs : List Reg} (h : ∀ r ∈ rs, r = .x19 ∨ r = .x20 ∨ r = .x21) :
    Pins (HE H) rs := fun a s₁ s₂ h₁ h₂ => by
  refine ⟨by rw [h₁.L.sp, h₂.L.sp], fun r hr => ?_⟩
  rcases h r hr with rfl | rfl | rfl
  · rw [h₁.x19, h₂.x19]
  · rw [h₁.L.x20, h₂.L.x20]
  · rw [h₁.x21, h₂.x21]

/-- `HE` after code that keeps the registers it fixes and writes only the
working space. -/
theorem HE.keep {H : Hash} {a : HA} {u u' : State} (h : HE H a u) {rs : List Reg} (k : Keep rs u u')
    (hr : ∀ r ∈ [Reg.x19, .x20, .x21, .x22], r ∉ rs) (hf : Frame [⟨a.S, oRsa⟩] u.mem u'.mem) : HE H a u' where
  L := h.L.congr k.sp k.wr (k.gpr .x20 (hr _ (by simp)))
  x19 := by rw [k.gpr .x19 (hr _ (by simp))]; exact h.x19
  x21 := by rw [k.gpr .x21 (hr _ (by simp))]; exact h.x21
  nb := by rw [nb_keep hf h.L.nbS]; exact h.nb
  len := by obtain ⟨ℓ, e, f⟩ := h.len; exact ⟨ℓ, by rw [k.gpr .x22 (hr _ (by simp))]; exact e, f⟩
  hnb := h.hnb

section
variable {H : Hash} (hH : HashOK H)

/-! ## `init` -/

/-- Before the call of `init`. -/
def HI (H : Hash) (a : HA) (u : State) : Prop := HE H a u ∧ u.gpr .x0 = off a.S oSt

include hH in
theorem ctInit_ct : RelCT isa (Two (HE H)) (ctInit H) (Two (HE H)) := by
  have hN := hH.N_le; have hBl := hH.B_le
  refine two_post ?_ fun a u h => WP.mono (ctInit_ok hH h.L h.x19) fun u' ⟨sp, _, wr, cs, _, fr, _⟩ => ?_
  · unfold ctInit
    refine RelCT.seq (two_post (Ψ := HI H)
      (two_taint [.x19] (HE.pins fun r hr => by simp at hr; exact .inl hr) (by taint_decide))
      fun a u h => wp_mov fun u' o e => wp_nil ⟨h.keep o.keep (by decide) (by rw [o.mem]; exact Frame.refl _ _),
        by rw [e, h.x19]⟩) ?_
    refine (RelCT.exists_ (P := fun a s₁ s₂ => HI H a s₁ ∧ HI H a s₂) fun a =>
      VG.Proof.Pbkdf2.Md.AArch64.Calls.init_rel hH.stream (st := off a.S oSt) fun s s' ⟨h₁, h₂⟩ =>
        ⟨h₁.2, h₂.2, Covers.one (h₁.1.L.st (n := H.P.N + H.P.B) (by unfold oSt oRsa; omega)),
          Covers.one (h₂.1.L.st (n := H.P.N + H.P.B) (by unfold oSt oRsa; omega)),
          by rw [h₁.1.L.sp, h₂.1.L.sp]⟩).mono (fun _ _ h => h) fun _ _ h => h
  · have hfr : Frame [⟨a.S, oRsa⟩, below a.F 16] u.mem u'.mem := fr.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, Offset.sub_base _ (by unfold oSt oRsa; omega)⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
    have g : ∀ r ∈ [Reg.x19, .x20, .x21, .x22], u'.gpr r = u.gpr r := fun r hr => cs r (by revert r; decide)
      (by revert r; decide)
    exact {
      L := h.L.congr sp wr (g .x20 (by simp))
      x19 := by rw [g .x19 (by simp)]; exact h.x19
      x21 := by rw [g .x21 (by simp)]; exact h.x21
      nb := by
        rw [nb_keep hfr fun r hr => ?_]; exact h.nb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.L.dFS.sub_left (Offset.sub_base _ (by decide))
        · exact slot_not_below _ (by decide)
      len := by obtain ⟨ℓ, e, f⟩ := h.len; exact ⟨ℓ, by rw [g .x22 (by simp)]; exact e, f⟩
      hnb := h.hnb }

/-! ## The padding, the length field and the digest -/

/-- `HE`, with registers the anchor fixes. -/
def HR (H : Hash) (rs : List (Reg × (HA → BitVec 64))) (a : HA) (u : State) : Prop :=
  HE H a u ∧ ∀ p ∈ rs, u.gpr p.1 = p.2 a

theorem HR.pins {H : Hash} {rs : List (Reg × (HA → BitVec 64))} {qs : List Reg}
    (h : ∀ r ∈ qs, r = .x19 ∨ r = .x20 ∨ r = .x21 ∨ ∃ f, (r, f) ∈ rs) : Pins (HR H rs) qs :=
  fun a s₁ s₂ h₁ h₂ => by
    refine ⟨by rw [h₁.1.L.sp, h₂.1.L.sp], fun r hr => ?_⟩
    rcases h r hr with rfl | rfl | rfl | ⟨f, hf⟩
    · rw [h₁.1.x19, h₂.1.x19]
    · rw [h₁.1.L.x20, h₂.1.L.x20]
    · rw [h₁.1.x21, h₂.1.x21]
    · rw [h₁.2 _ hf, h₂.2 _ hf]

include hH in
theorem lenField_ct (hc : PssChecks H) : RelCT isa (Two (HE H)) (.block (lenField H)) (Two (HE H)) := by
  have hd := hH.sizes.dims
  have hNL := hH.sizes.NL
  have hN := hH.N_le
  have hB := hH.B_le
  obtain ⟨_, hcl⟩ := hc.lenField
  refine two_post (two_taint [.x20] (HE.pins fun r hr => by simp at hr; exact .inr (.inl hr)) hcl)
    fun a u h => WP.mono (lenField_ok H hH.shape h.L (fun _ _ => rfl) (by omega) hd.L.2)
      fun u' ⟨k, h19, fr, _⟩ => ?_
  exact {
    L := h.L.congr k.sp k.wr (k.get .x20)
    x19 := h19
    x21 := by rw [k.get .x21]; exact h.x21
    nb := by rw [nb_keep fr h.L.nbS]; exact h.nb
    len := by obtain ⟨ℓ, e, f⟩ := h.len; exact ⟨ℓ, by rw [k.get .x22]; exact e, f⟩
    hnb := h.hnb }

theorem digestOut_ct (hc : PssChecks H) : RelCT isa (Two (HE H)) (.block (digestOut H)) fun _ _ => True := by
  obtain ⟨_, hcl⟩ := hc.digestOut
  exact two_taint [.x20, .x21] (HE.pins fun r hr => by simp at hr; rcases hr with rfl | rfl <;> simp) hcl

theorem fixedPad_ct (ℓ : Nat) (h4 : oY + ℓ < 4096) (hℓ : ∀ a : HA, ℓ < a.nbm * H.P.B) :
    RelCT isa (Two (HE H)) (fixedPad80 ℓ) (Two (HE H)) := by
  refine two_post (two_taintE [.x20] (HE.pins fun r hr => by simp at hr; exact .inr (.inl hr))
    (c' := .block [.addImm .x .x10 .x20 0, .ldrb .x9 .x10 0, .movz .x .x13 0 0, .logic .orr .x .x9 .x9 .x13,
      .strb .x9 .x10 0]) rfl (by taint_decide)) fun a u h => WP.mono (fixedPad_ok h.L (fun _ _ => rfl) (hℓ a) h4)
      fun u' ⟨k, fr, _⟩ => h.keep k (by decide) fr

include hH in
theorem pad80_ct : RelCT isa (Two (HE H)) (pad80 H) (Two (HE H)) := by
  have hB := hH.B_le
  have hB0 := hH.B_pos
  have hlg : 2 ^ lgB H = H.P.B ∧ lgB H < 64 := by
    unfold lgB
    rcases hH.sizes.B with h | h <;> rw [h]
    · rw [show (64 : Nat) = 2 ^ 6 from rfl, Nat.log2_two_pow]; decide
    · rw [show (128 : Nat) = 2 ^ 7 from rfl, Nat.log2_two_pow]; decide
  refine two_post ?_ fun a u h => ?_
  · unfold pad80
    refine RelCT.seq (two_post (Ψ := HR H [(.x10, fun a => off a.S oY), (.x11, fun _ => (BitVec.ofNat 16 0).setWidth 64),
        (.x12, fun a => BitVec.ofNat 64 a.nbm <<< lgB H)])
      (two_taintE [.x20] (HE.pins fun r hr => by simp at hr; exact .inr (.inl hr))
        (c' := .block [.addImm .x .x10 .x20 0, .movz .x .x11 0 0, .ldrSp .x12 sNb, .lsl .x .x12 .x12 0]) rfl
        (by taint_decide))
      fun a u h => ?_) ?_
    · unfold ld movi
      refine wp_addImm (by decide) fun u₁ o₁ e₁ => wp_movz fun u₂ o₂ e₂ => wp_ldrSp (by decide) ?_
        fun u₃ o₃ e₃ => wp_lsl hlg.2 fun u₄ o₄ e₄ => wp_nil ⟨h.keep
          (Only.mono (rs' := [.x10, .x11, .x12]) (o₁.trans (o₂.trans (o₃.trans o₄)))).keep (by decide)
          (by rw [o₄.mem, o₃.mem, o₂.mem, o₁.mem]; exact Frame.refl _ _), fun p hp => ?_⟩
      · rw [o₂.sp, o₁.sp, h.L.sp, o₂.rd, o₁.rd, o₂.wr, o₁.wr]; exact h.L.fld (by decide)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl
        · rw [o₄.get .x10, o₃.get .x10, o₂.get .x10, e₁, h.L.x20]
        · rw [o₄.get .x11, o₃.get .x11, e₂]
        · rw [e₄, e₃, o₂.sp, o₁.sp, h.L.sp, o₂.mem, o₁.mem, h.nb]
    · exact two_taint [.x10, .x11, .x12] (HR.pins fun r hr => by
        simp at hr; rcases hr with rfl | rfl | rfl <;> simp) (by taint_decide)
  · obtain ⟨ℓ, e, f⟩ := h.len
    have := h.hnb
    exact WP.mono (pad80_ok H h.L (fun _ _ => rfl) hlg.1 hlg.2 (ℓ := ℓ) (by omega) h.hnb
      (by omega) e h.nb) fun u' ⟨k, fr, _⟩ => h.keep k (by decide) fr

include hH in
theorem lenLoop_ct : RelCT isa (Two (HE H)) (lenLoop H) (Two (HE H)) := by
  have hB := hH.B_le
  have hB0 := hH.B_pos
  have hd := hH.sizes.dims
  have hlg : 2 ^ lgB H = H.P.B ∧ lgB H < 64 := by
    unfold lgB
    rcases hH.sizes.B with h | h <;> rw [h]
    · rw [show (64 : Nat) = 2 ^ 6 from rfl, Nat.log2_two_pow]; decide
    · rw [show (128 : Nat) = 2 ^ 7 from rfl, Nat.log2_two_pow]; decide
  have hLB : H.P.L < H.P.B := by have : 0 < H.P.N := hd.N.1; have := hH.sizes.NL; omega
  refine two_post ?_ fun a u h => ?_
  · unfold lenLoop
    refine RelCT.seq (two_post (Ψ := HR H [(.x10, fun a => off a.S (oY + H.P.B - H.P.L)),
        (.x11, fun _ => (BitVec.ofNat 16 0).setWidth 64), (.x12, fun a => BitVec.ofNat 64 a.nbm)])
      (two_taintE [.x20] (HE.pins fun r hr => by simp at hr; exact .inr (.inl hr))
        (c' := Code.eraseOff (.block ([.addImm .x .x10 .x20 (oY + zH.P.B - zH.P.L), movi .x11 0, ld .x12 sNb] ++
          Impl.RsaPss.AArch64.lastBlk zH .x15))) rfl (by taint_decide))
      fun a u h => ?_) ?_
    · unfold ld movi Impl.RsaPss.AArch64.lastBlk
      simp only [List.cons_append, List.nil_append]
      refine wp_addImm (by unfold oY; omega) fun u₁ o₁ e₁ => wp_movz fun u₂ o₂ e₂ => wp_ldrSp (by decide) ?_
        fun u₃ o₃ e₃ => wp_addImm (by omega) fun u₄ o₄ e₄ => wp_lsr hlg.2 fun u₅ o₅ e₅ => wp_nil ⟨h.keep
          (Only.mono (rs' := [.x10, .x11, .x12, .x15]) (o₁.trans (o₂.trans (o₃.trans (o₄.trans o₅))))).keep
          (by decide) (by rw [o₅.mem, o₄.mem, o₃.mem, o₂.mem, o₁.mem]; exact Frame.refl _ _), fun p hp => ?_⟩
      · rw [o₂.sp, o₁.sp, h.L.sp, o₂.rd, o₁.rd, o₂.wr, o₁.wr]; exact h.L.fld (by decide)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl
        · rw [o₅.get .x10, o₄.get .x10, o₃.get .x10, o₂.get .x10, e₁, h.L.x20]
        · rw [o₅.get .x11, o₄.get .x11, o₃.get .x11, e₂]
        · rw [o₅.get .x12, o₄.get .x12, e₃, o₂.sp, o₁.sp, h.L.sp, o₂.mem, o₁.mem, h.nb]
    · exact two_taintE [.x10, .x11, .x12, .x20] (HR.pins fun r hr => by
        simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> simp)
        (c' := Code.eraseOff (.loop (.seq (.block (eqMask .x13 .x11 .x15 ++ [.addImm .x .x14 .x20 oLen, Impl.MdStream.AArch64.mov .x16 .x10,
            movi .x17 zH.P.L]))
          (.seq (.loop (.block [.ldrb .x9 .x14 0, .logic .and .x .x9 .x9 .x13, .ldrb .x8 .x16 0,
              .logic .orr .x .x8 .x8 .x9, .strb .x8 .x16 0, .addImm .x .x14 .x14 1, .addImm .x .x16 .x16 1,
              .subImm .x .x17 .x17 1]) (.nonzero .x .x17))
            (.block [.addImm .x .x10 .x10 zH.P.B, .addImm .x .x11 .x11 1, .subImm .x .x12 .x12 1])))
          (.nonzero .x .x12))) rfl (by taint_decide)
  · obtain ⟨ℓ, e, f⟩ := h.len
    have := h.hnb
    have hfb : (ℓ + H.P.L) / H.P.B < a.nbm := (Nat.div_lt_iff_lt_mul hB0).mpr (by omega)
    exact WP.mono (lenLoop_ok H h.L (fun _ _ => rfl) hlg.1 hlg.2 (by omega) hd.L.1 hd.L.2 hB (ℓ := ℓ) (by omega)
      h.hnb hfb e h.nb) fun u' ⟨k, fr, _⟩ => h.keep k (by decide) fr

end

end VG.Proof.RsaPss.AArch64
