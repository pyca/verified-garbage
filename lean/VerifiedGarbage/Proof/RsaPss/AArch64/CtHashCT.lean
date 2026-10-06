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

/-- A block related by the taint analysis and by correctness, then the rest. -/
theorem two_step {α : Type} {Φ Ψ : α → State → Prop} {l : List Instr} {c : Prog isa} {Q : State → State → Prop}
    (ht : RelCT isa (Two Φ) (.block l) fun _ _ => True) (hw : ∀ a s, Φ a s → WP isa (.block l) s (Ψ a))
    (h : RelCT isa (Two Ψ) c Q) : RelCT isa (Two Φ) (.seq (.block l) c) Q :=
  RelCT.seq (two_post ht hw) h

theorem pins_nil {α : Type} {Φ : α → State → Prop} (h : ∀ a s₁ s₂, Φ a s₁ → Φ a s₂ → s₁.sp = s₂.sp) : Pins Φ [] :=
  fun a s₁ s₂ h₁ h₂ => ⟨h a s₁ s₂ h₁ h₂, fun _ h => absurd h List.not_mem_nil⟩

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
  /-- The message's length, if public (MGF1's). -/
  fx : Option Nat

/-- A run of `ctHashWith` and its pieces, with the anchor's frame, working
space and number of blocks: the message's length `ℓ` (secret) fits. -/
structure HE (H : Hash) (a : HA) (u : State) : Prop where
  L : Lay u a.F a.S
  x19 : u.gpr .x19 = off a.S oSt
  x21 : u.gpr .x21 = off a.S oDig
  nb : u.mem.readW (off a.F sNb) 64 = BitVec.ofNat 64 a.nbm
  len : ∃ ℓ, u.gpr .x22 = BitVec.ofNat 64 ℓ ∧ ℓ + 1 + H.P.L ≤ a.nbm * H.P.B
  hnb : a.nbm * H.P.B ≤ 2048
  fx : ∀ ℓ, a.fx = some ℓ → u.gpr .x22 = BitVec.ofNat 64 ℓ

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
  fx := fun ℓ e => by rw [k.gpr .x22 (hr _ (by simp))]; exact h.fx ℓ e

section
variable {H : Hash} (hH : HashOK H)

/-! ## `init` -/

/-- Before the call of `init`. -/
def HI (H : Hash) (a : HA) (u : State) : Prop := HE H a u ∧ u.gpr .x0 = off a.S oSt

include hH in
theorem ctInit_tr : RelCT isa (Two (HE H)) (ctInit H) fun _ _ => True := by
  have hN := hH.N_le; have hBl := hH.B_le
  unfold ctInit
  refine RelCT.seq (two_post (Ψ := HI H)
    (two_taint [.x19] (HE.pins fun r hr => by simp at hr; exact .inl hr) (by taint_decide))
    fun a u h => wp_mov fun u' o e => wp_nil ⟨h.keep o.keep (by decide) (by rw [o.mem]; exact Frame.refl _ _),
      by rw [e, h.x19]⟩) ?_
  refine (RelCT.exists_ (P := fun a s₁ s₂ => HI H a s₁ ∧ HI H a s₂) fun a =>
    VG.Proof.Pbkdf2.Md.AArch64.Calls.init_rel hH.stream (st := off a.S oSt) fun s s' ⟨h₁, h₂⟩ =>
      ⟨h₁.2, h₂.2, Covers.one (h₁.1.L.st (n := H.P.N + H.P.B) (by unfold oSt oRsa; omega)),
        Covers.one (h₂.1.L.st (n := H.P.N + H.P.B) (by unfold oSt oRsa; omega)),
        by rw [h₁.1.L.sp, h₂.1.L.sp]⟩).mono (fun _ _ h => h) fun _ _ h => h

include hH in
theorem ctInit_wp {a : HA} {u : State} (h : HE H a u) : WP isa (ctInit H) u (HE H a) := by
  have hN := hH.N_le; have hBl := hH.B_le
  refine WP.mono (ctInit_ok hH h.L h.x19) fun u' ⟨sp, _, wr, cs, _, fr, _⟩ => ?_
  have hfr : Frame [⟨a.S, oRsa⟩, below a.F 16] u.mem u'.mem := fr.sub fun r hr => by
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
    hnb := h.hnb
    fx := fun ℓ e => by rw [g .x22 (by simp)]; exact h.fx ℓ e }

/-- Facts about the anchor alone, kept by code that keeps the per-run ones. -/
theorem two_X {α : Type} {Φ Ψ : α → State → Prop} {c : Prog isa} (X : α → Prop)
    (hct : RelCT isa (Two Φ) c fun _ _ => True) (hw : ∀ a s, Φ a s → WP isa c s (Ψ a)) :
    RelCT isa (Two fun a s => Φ a s ∧ X a) c (Two fun a s => Ψ a s ∧ X a) :=
  two_post (hct.mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, h₁.1, h₂.1⟩) fun _ _ h => h)
    fun a s h => WP.mono (hw a s h.1) fun _ h' => ⟨h', h.2⟩

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
    hnb := h.hnb
    fx := fun ℓ e => by rw [k.get .x22]; exact h.fx ℓ e }

theorem digestOut_ct (hc : PssChecks H) : RelCT isa (Two (HE H)) (.block (digestOut H)) fun _ _ => True := by
  obtain ⟨_, hcl⟩ := hc.digestOut
  exact two_taint [.x20, .x21] (HE.pins fun r hr => by simp at hr; rcases hr with rfl | rfl <;> simp) hcl

theorem fixedPad_ct (ℓ : Nat) (h4 : oY + ℓ < 4096) :
    RelCT isa (Two fun a u => HE H a u ∧ a.fx = some ℓ) (fixedPad80 ℓ) (Two (HE H)) := by
  refine two_post (two_taintE [.x20] (fun a s₁ s₂ h₁ h₂ => HE.pins (H := H) (rs := [.x20])
      (fun r hr => by simp at hr; exact .inr (.inl hr)) a s₁ s₂ h₁.1 h₂.1)
    (c' := .block [.addImm .x .x10 .x20 0, .ldrb .x9 .x10 0, .movz .x .x13 0 0, .logic .orr .x .x9 .x9 .x13,
      .strb .x9 .x10 0]) rfl (by taint_decide)) fun a u ⟨h, hf⟩ => ?_
  have hℓ : ℓ < a.nbm * H.P.B := by
    obtain ⟨ℓ', e, f⟩ := h.len
    have e' := h.fx ℓ hf
    rw [e] at e'
    have := h.hnb
    have := congrArg BitVec.toNat e'
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    omega
  exact WP.mono (fixedPad_ok h.L (fun _ _ => rfl) hℓ h4) fun u' ⟨k, fr, _⟩ => h.keep k (by decide) fr

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

/-! ## The blocks -/

include hH in
/-- The block `b`'s address, for the call of the compression function. -/
theorem compArgs_ok {u : State} {F S : Addr} (L : Lay u F S) {b nbm : Nat} (hb : b < nbm)
    (hnb : nbm * H.P.B ≤ 2048) (h27 : u.gpr .x27 = BitVec.ofNat 64 b) (h19 : u.gpr .x19 = off S oSt) :
    WP isa (.block (compArgs H)) u fun u₃ => Only [.x1] u u₃ ∧
      VG.Proof.Pbkdf2.AArch64.CallOk u₃ H.P.N H.P.B H.P.so (off S oSt) S (off S (oY + H.P.B * b)) := by
  have hso := so_lt hH
  have hN := hH.N_le
  have hB0 := hH.B_pos
  have hBl := hH.B_le
  have hlg : 2 ^ lgB H = H.P.B ∧ lgB H < 64 := by
    unfold lgB
    rcases hH.sizes.B with h | h <;> rw [h]
    · rw [show (64 : Nat) = 2 ^ 6 from rfl, Nat.log2_two_pow]; decide
    · rw [show (128 : Nat) = 2 ^ 7 from rfl, Nat.log2_two_pow]; decide
  have hBb : H.P.B * (b + 1) ≤ H.P.B * nbm := Nat.mul_le_mul_left _ hb
  have hBn : H.P.B * nbm ≤ 2048 := by rw [Nat.mul_comm]; exact hnb
  have hBb' : H.P.B * b + H.P.B ≤ H.P.B * nbm := by rw [← Nat.mul_succ]; exact hBb
  have hnb1 : nbm ≤ 2048 := Nat.le_trans (Nat.le_mul_of_pos_right _ hB0) hnb
  have hcm : b * H.P.B = H.P.B * b := Nat.mul_comm _ _
  unfold compArgs
  refine wp_lsl hlg.2 fun u₁ o₁ e₁ => VG.Proof.MlKem.AArch64.wp_add fun u₂ o₂ e₂ =>
    wp_addImm (by decide) fun u₃ o₃ e₃ => wp_nil ?_
  have O₃ : Only [.x1] u u₃ := (o₁.trans (o₂.trans o₃)).mono
  have x1 : u₃.gpr .x1 = off S (oY + H.P.B * b) := by
    rw [e₃, e₂, e₁, o₁.get .x20, h27, L.x20, lsl_val (by rw [hlg.1]; omega), hlg.1]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mul_comm b]; omega
  refine ⟨O₃, {
    x19 := by rw [O₃.get .x19, h19]
    x20 := by rw [O₃.get .x20, L.x20]
    x1 := x1
    st_scr := by
      have := Offset.disjoint S (d := oSt) (n := H.P.N) (e := 0) (k := H.P.so) (by unfold oSt; omega)
        (by unfold oSt; omega) (by omega)
      rwa [BitVec.add_zero] at this
    src_st := Offset.disjoint S (by unfold oY oSt; omega) (by unfold oY; omega) (by unfold oSt; omega)
    src_scr := by
      have := Offset.disjoint S (d := oY + H.P.B * b) (n := H.P.B) (e := 0) (k := H.P.so) (by unfold oY; omega)
        (by unfold oY; omega) (by omega)
      rwa [BitVec.add_zero] at this
    cov := by
      rw [O₃.rd, O₃.wr]
      refine Covers.cons (Covers.one (L.ld (by unfold oY oRsa; omega))) (Covers.cons
        (Covers.one (L.ld (by unfold oSt oRsa; omega))) (Covers.cons (Covers.one ?_) Covers.nil))
      have := L.ld (o := 0) (n := H.P.so) (by unfold oRsa; omega)
      rwa [off, BitVec.add_zero] at this
    covW := by
      rw [O₃.wr]
      refine Covers.cons (Covers.one (L.st (by unfold oSt oRsa; omega))) (Covers.cons (Covers.one ?_) Covers.nil)
      have := L.st (o := 0) (n := H.P.so) (by unfold oRsa; omega)
      rwa [off, BitVec.add_zero] at this }⟩

/-- In the loop over the blocks, before block `p.2`: a run of `compLoop`
from `t` (`CInv`). -/
def CI (p : HA × Nat) (u : State) : Prop :=
  ∃ t V₀ h₀ ℓ, HE H p.1 t ∧ t.gpr .x22 = BitVec.ofNat 64 ℓ ∧ ℓ + 1 + H.P.L ≤ p.1.nbm * H.P.B ∧
    CInv hH t p.1.F p.1.S V₀ h₀ p.1.nbm ((ℓ + H.P.L) / H.P.B) p.2 u

/-- Before the call of the compression function. -/
def CA (H : Hash) (p : HA × Nat) (u : State) : Prop :=
  VG.Proof.Pbkdf2.AArch64.CallOk u H.P.N H.P.B H.P.so (off p.1.S oSt) p.1.S (off p.1.S (oY + H.P.B * p.2)) ∧
    Lay u p.1.F p.1.S ∧ u.gpr .x27 = BitVec.ofNat 64 p.2 ∧ p.2 < 2 ^ 62 ∧
      ∃ ℓ, u.gpr .x22 = BitVec.ofNat 64 ℓ ∧ ℓ < 2 ^ 62

/-- After it. -/
def CB (p : HA × Nat) (u : State) : Prop :=
  Lay u p.1.F p.1.S ∧ u.gpr .x27 = BitVec.ofNat 64 p.2 ∧ p.2 < 2 ^ 62 ∧
    ∃ ℓ, u.gpr .x22 = BitVec.ofNat 64 ℓ ∧ ℓ < 2 ^ 62

theorem CI.lay {p : HA × Nat} {u : State} (h : CI hH p u) : Lay u p.1.F p.1.S :=
  let ⟨_, _, _, _, ht, _, _, I⟩ := h; ht.L.congr I.sp I.wr (I.cs .x20 (by decide))

theorem CI.x27 {p : HA × Nat} {u : State} (h : CI hH p u) : u.gpr .x27 = BitVec.ofNat 64 p.2 :=
  let ⟨_, _, _, _, _, _, _, I⟩ := h; I.x27

include hH in
theorem body_ct :
    RelCT isa (Two fun p u => CI hH p u ∧ p.2 < p.1.nbm)
      (seqs [.block (compArgs H), Impl.MdStream.AArch64.compressAt H.compN H.compC, select H, .block nextBlock])
      fun _ _ => True := by
  have hN0 := hH.sizes.dims.N.1
  have hN := hH.N_le
  have hL := hH.L
  have hlg : 2 ^ lgB H = H.P.B ∧ lgB H < 64 := by
    unfold lgB
    rcases hH.sizes.B with h | h <;> rw [h]
    · rw [show (64 : Nat) = 2 ^ 6 from rfl, Nat.log2_two_pow]; decide
    · rw [show (128 : Nat) = 2 ^ 7 from rfl, Nat.log2_two_pow]; decide
  simp only [seqs]
  refine RelCT.seq (two_post (Ψ := CA H)
    (two_taintE [.x20, .x27] (fun p u₁ u₂ ⟨h₁, _⟩ ⟨h₂, _⟩ => by
        refine ⟨by rw [(h₁.lay hH).sp, (h₂.lay hH).sp], fun r hr => ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [(h₁.lay hH).x20, (h₂.lay hH).x20]
        · rw [h₁.x27 hH, h₂.x27 hH])
      (c' := Code.eraseOff (.block (compArgs zH))) rfl (by taint_decide))
    fun p u ⟨h, hb⟩ => ?_) ?_
  · have Lh := h.lay hH
    obtain ⟨t, V₀, h₀, ℓ, ht, e, f, I⟩ := h
    have := ht.hnb
    refine WP.mono (compArgs_ok hH Lh hb ht.hnb I.x27 (by rw [I.cs .x19 (by decide), ht.x19]))
      fun u₃ ⟨O, C⟩ => ⟨C, Lh.congr O.sp O.wr (O.get .x20), by rw [O.get .x27, I.x27], by
        have h0 := hH.B_pos; have : p.2 * H.P.B < p.1.nbm * H.P.B := Nat.mul_lt_mul_of_pos_right hb h0
        have : p.2 ≤ p.2 * H.P.B := Nat.le_mul_of_pos_right _ h0
        omega, ℓ, by rw [O.get .x22, I.cs .x22 (by decide), e], by omega⟩
  refine RelCT.seq (two_post (Ψ := CB) ((RelCT.exists_ (P := fun p s₁ s₂ => CA H p s₁ ∧ CA H p s₂) fun p =>
      VG.Proof.Pbkdf2.AArch64.compressAt_rel hH.comp fun s₁ s₂ ⟨h₁, h₂⟩ =>
        ⟨h₁.1, h₂.1, by rw [h₁.2.1.sp, h₂.2.1.sp]⟩).mono (fun _ _ h => h) fun _ _ h => h)
    fun p u ⟨C, Lu, h27, hb, ℓ, e, f⟩ => VG.Proof.Pbkdf2.AArch64.compressAt_ok hH.comp C
      fun v vrd vwr vcs vsp _ _ => ⟨Lu.congr vsp vwr (vcs .x20 (by decide) (by decide)),
        by rw [vcs .x27 (by decide) (by decide), h27], hb, ℓ, by rw [vcs .x22 (by decide) (by decide), e], f⟩) ?_
  refine RelCT.seq (two_post (Ψ := fun p u => u.sp = p.1.F)
    (two_taintE [.x20, .x27] (fun p u₁ u₂ ⟨L₁, a₁, _, _⟩ ⟨L₂, a₂, _, _⟩ => by
        refine ⟨by rw [L₁.sp, L₂.sp], fun r hr => ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [L₁.x20, L₂.x20]
        · rw [a₁, a₂])
      (c' := Code.eraseOff (select zH)) rfl (by taint_decide))
    fun p u ⟨Lu, h27, hb, ℓ, e, f⟩ => WP.mono (select_ok H Lu (fun _ _ => rfl) hlg.1 hlg.2 hN0 hN hL.2 f
      (b := p.2) hb e h27) fun v ⟨k, _, _⟩ => by rw [k.sp, Lu.sp]) ?_
  exact two_taint [] (fun _ _ _ h₁ h₂ => ⟨by rw [h₁, h₂], fun _ h => absurd h List.not_mem_nil⟩) (by taint_decide)

theorem CI.he {a : HA} {u : State} (h : CI hH (a, a.nbm) u) : HE H a u := by
  obtain ⟨t, _, _, ℓ, ht, e, f, I⟩ := h
  have fx := ht.fx
  exact {
    L := ht.L.congr I.sp I.wr (I.cs .x20 (by decide))
    x19 := by rw [I.cs .x19 (by decide)]; exact ht.x19
    x21 := by rw [I.cs .x21 (by decide)]; exact ht.x21
    nb := by rw [nb_keep I.fr ht.L.nbS]; exact ht.nb
    len := ⟨ℓ, by rw [I.cs .x22 (by decide)]; exact e, f⟩
    hnb := ht.hnb
    fx := fun ℓ e => by rw [I.cs .x22 (by decide)]; exact fx ℓ e }

include hH in
theorem compLoop_ct : RelCT isa (Two (HE H)) (compLoop H) (Two (HE H)) := by
  have hB0 := hH.B_pos
  have hlg : 2 ^ lgB H = H.P.B ∧ lgB H < 64 := by
    unfold lgB
    rcases hH.sizes.B with h | h <;> rw [h]
    · rw [show (64 : Nat) = 2 ^ 6 from rfl, Nat.log2_two_pow]; decide
    · rw [show (128 : Nat) = 2 ^ 7 from rfl, Nat.log2_two_pow]; decide
  unfold compLoop
  refine RelCT.seq (two_post (Ψ := fun a u => CI hH (a, 0) u ∧ 0 < a.nbm)
    (two_taint [] (HE.pins fun _ h => absurd h List.not_mem_nil) (by taint_decide)) fun a u h => ?_) ?_
  · obtain ⟨ℓ, e, f⟩ := h.len
    refine wp_movz fun u' o e' => wp_nil ⟨⟨u, fun o => u.mem (off a.S o), hH.md.stateAt u.mem (off a.S oSt), ℓ, h,
      e, f, {
        sp := o.sp, rd := o.rd, wr := o.wr
        cs := fun r hr => o.gpr r (by revert r; decide)
        x27 := by rw [e']; rfl
        vec := o.vcs
        fr := by rw [o.mem]; exact Frame.refl _ _
        keep := fun x _ _ => by rw [o.mem]
        st := by rw [o.mem, hH.md.compressList_zero]
        sel := fun h => absurd h (Nat.not_lt_zero _) }⟩, ?_⟩
    rcases Nat.eq_zero_or_pos a.nbm with h0 | h0
    · rw [h0, Nat.zero_mul] at f; omega
    · exact h0
  refine RelCT.exists_ fun a => ?_
  let I : Nat → State → State → Prop := fun n => Two fun p u => CI hH p u ∧ p.2 < p.1.nbm ∧ n = p.1.nbm - p.2
  refine (RelCT.loop (Q := Two (HE H)) I (fun n => ?_) a.nbm).mono
    (fun s₁ s₂ ⟨h₁, h₂⟩ => ⟨(a, 0), ⟨h₁.1, h₁.2, rfl⟩, h₂.1, h₂.2, rfl⟩) fun _ _ h => h
  have T : RelCT isa (I n) _ _ := (two_post (Ψ := fun p u => CI hH (p.1, p.2 + 1) u ∧
      ((u.gpr .x9).toNat ≠ 0 ↔ p.2 + 1 ≠ p.1.nbm) ∧ p.2 < p.1.nbm ∧ n = p.1.nbm - p.2)
    ((body_ct hH).mono (fun _ _ ⟨p, h₁, h₂⟩ => ⟨p, ⟨h₁.1, h₁.2.1⟩, h₂.1, h₂.2.1⟩) fun _ _ h => h)
    fun p u ⟨h, hb, hn⟩ => by
      obtain ⟨t, V₀, h₀, ℓ, ht, e, f, Ic⟩ := h
      have := ht.hnb
      exact WP.mono (comp_step hH ht.L hlg.1 hlg.2 (by omega) ht.hnb hb e ht.x19 ht.nb Ic)
        fun u' ⟨I', fl⟩ => ⟨⟨t, V₀, h₀, ℓ, ht, e, f, I'⟩, fl, hb, hn⟩)
  refine T.mono (fun _ _ h => h) fun s₁ s₂ ⟨⟨a', b⟩, ⟨c₁, f₁, hb, hn⟩, c₂, f₂, _, _⟩ => ?_
  dsimp only at c₁ c₂ f₁ f₂ hb hn
  have ev : ∀ {u : State}, ((u.gpr .x9).toNat ≠ 0 ↔ b + 1 ≠ a'.nbm) →
      isa.eval (.nonzero .x .x9) u = some (decide (b + 1 ≠ a'.nbm)) := fun hf => by
    rw [VG.Proof.MlKem.AArch64.eval_nonzero, VG.Proof.MlKem.AArch64.ne_zero_iff, decide_eq_decide.mpr hf]
  refine ⟨by rw [ev f₁, ev f₂], fun hc => ?_, fun hc => ?_⟩
  · rw [ev f₁, Option.some.injEq, decide_eq_false_iff_not, Decidable.not_not] at hc
    rw [hc] at c₁ c₂
    exact ⟨a', c₁.he hH, c₂.he hH⟩
  · rw [ev f₁, Option.some.injEq, decide_eq_true_eq] at hc
    exact ⟨n - 1, by omega, (a', b + 1), ⟨c₁, by dsimp only; omega, by dsimp only; omega⟩, c₂,
      by dsimp only; omega, by dsimp only; omega⟩

/-! ## The whole hash -/

include hH in
theorem ctHashWith_ct (hc : PssChecks H) {padding : Prog isa} {X : HA → Prop}
    (hp : RelCT isa (Two fun a u => HE H a u ∧ X a) padding (Two (HE H))) :
    RelCT isa (Two fun a u => HE H a u ∧ X a) (ctHashWith H padding) fun _ _ => True := by
  unfold ctHashWith seqs seqs seqs seqs seqs
  exact RelCT.seq (two_X X (ctInit_tr hH) fun _ _ h => ctInit_wp hH h) (RelCT.seq hp (RelCT.seq
    (lenField_ct hH hc) (RelCT.seq (lenLoop_ct hH) (RelCT.seq (compLoop_ct hH) (digestOut_ct hc)))))

include hH in
theorem ctHash_ct (hc : PssChecks H) : RelCT isa (Two (HE H)) (ctHash H) fun _ _ => True :=
  (ctHashWith_ct hH hc (X := fun _ => True) ((pad80_ct hH).mono
    (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, h₁.1, h₂.1⟩) fun _ _ h => h)).mono
    (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, ⟨h₁, trivial⟩, h₂, trivial⟩) fun _ _ h => h

include hH in
theorem mgfHash_ct (hc : PssChecks H) :
    RelCT isa (Two fun a u => HE H a u ∧ a.fx = some (H.D + 4)) (mgfHash H) fun _ _ => True := by
  have hDN := hH.sizes.DN
  have hN := hH.N_le
  exact ctHashWith_ct hH hc (fixedPad_ct (H.D + 4) (by unfold oY; omega))

end

end VG.Proof.RsaPss.AArch64
