module

public import VerifiedGarbage.Proof.SlhDsa.AArch64.SignCtx
public import VerifiedGarbage.Proof.SlhDsa.AArch64.KeyGenPro
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-!
# SLH-DSA (SHAKE) on AArch64, `sign`: the body's first block

From the entry `σ`, after `x9 ← ctx_len ≫ 8`: the caller's registers saved
at `oTop` (`scratch` in `x7`), the arguments kept in `x19`–`x25`, the two
bytes `0 ‖ ctx_len` of `M′` at `oHdr`, and the four keys copied to `oKeys`
(`pro_ok`): `Ctx`, and `HRegs`, the registers the hashes read.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.Sign

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.AArch64 (Layout copyWords saveRegsAt)
open VG.Impl.SlhDsa.AArch64.Thash4 (mov)
open VG.Impl.SlhDsa.AArch64.Shake (topSaved)
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_addImm wp_movz wp_strb)

/-- The registers the hashes read: `msg`, `msg_len`, `ctx`, `ctx_len`, `addrnd`, `sig`. -/
structure HRegs (σ t : State) : Prop where
  x20 : t.gpr .x20 = σ.gpr .x1
  x21 : t.gpr .x21 = σ.gpr .x2
  x22 : t.gpr .x22 = σ.gpr .x3
  x23 : t.gpr .x23 = σ.gpr .x4
  x24 : t.gpr .x24 = σ.gpr .x5
  x25 : t.gpr .x25 = σ.gpr .x6

/-- The body's first block. -/
abbrev proCode (p : Params) : List Instr :=
  saveRegsAt Layout.oTop .x7 topSaved ++
    [mov .x19 .x7, mov .x20 .x1, mov .x21 .x2, mov .x22 .x3, mov .x23 .x4, mov .x24 .x5, mov .x25 .x6,
      .movz .x .x9 0 0, .strb .x9 .x19 Layout.oHdr, .strb .x23 .x19 (Layout.oHdr + 1)] ++
    (List.range 4).flatMap (fun c => copyWords .x19 (Layout.oKeys + 32 * c) .x0 (p.n * c) (p.n / 8))

theorem write8_at (m : Mem) (a : Addr) (v : BitVec 8) : m.writeW a v a = v := by
  have := write_byte m a (k := 1) (j := 0) v (by decide) (by decide)
  unfold Mem.writeW
  simpa using this

theorem write8_off (m : Mem) (a x : Addr) (v : BitVec 8) (h : x ≠ a) : m.writeW a v x = m x := by
  unfold Mem.writeW
  refine write_off m a x (k := 1) v fun hl => h ?_
  have h0 : (x - a).toNat = 0 := by omega
  have : x - a = 0 := BitVec.eq_of_toNat_eq (by rw [h0]; rfl)
  rw [← BitVec.sub_add_cancel x a, this]; exact BitVec.zero_add _

theorem key_chunk (p : Params) (σ : State) {c : Nat} (hc : c < 4) :
    bytesAt σ.mem (σ.gpr .x0 + BitVec.ofNat 64 (p.n * c)) p.n = chunk (skB p σ) p.n c := by
  rw [skB, Params.skLen, KeyGen.chunk_bytesAt _ _ (c := 4) hc]

theorem bytes2 (m : Mem) (a : Addr) : bytesAt m a 2 = [m a, m (a + BitVec.ofNat 64 1)] := by
  simp [bytesAt, List.range_succ]

theorem pro_ok {p : Params} (hz : Sz p) {σ s : State} (hK : SG p σ) (h4 : (σ.gpr .x4).toNat < 256)
    (hs : Only [.x9] σ s) :
    WP isa (.block (proCode p)) s fun t => Ctx p σ t ∧ HRegs σ t := by
  have hn := hz.n32
  have h8 := hz.n8
  have hsc : scratchLen = 65536 := rfl
  have eT : Layout.oTop = 1536 := rfl
  have eH : Layout.oHdr = 1632 := rfl
  have eK : Layout.oKeys = 1664 := rfl
  have g : ∀ r, r ≠ .x9 → s.gpr r = σ.gpr r := fun r h => hs.get r (by simpa using h)
  obtain ⟨S, hS⟩ : ∃ S, σ.gpr .x7 = S := ⟨_, rfl⟩
  have fS : S.toNat + scratchLen ≤ 2 ^ 64 := by rw [← hS]; exact hK.f_scr
  have hw : (⟨S, scratchLen⟩ : Region) ∈ s.wr := by rw [hs.wr, hK.wr, hS]; simp
  have hsub : ∀ {o l : Nat}, o + l ≤ scratchLen → Region.Sub ⟨S + BitVec.ofNat 64 o, l⟩ ⟨S, scratchLen⟩ :=
    fun h => Offset.sub_base S h
  simp only [proCode, List.append_assoc, List.cons_append, List.nil_append]
  refine saveRegsAt_ok (s := s) (b := .x7) ⟨by decide, by decide⟩
    (by rw [g _ (by decide), hS]; exact KeyGen.in_scr hw (by decide)) fun s₁ k₁ sv₁ f₁ => ?_
  rw [g _ (by decide), hS] at sv₁ f₁
  refine wp_addImm (by decide) fun s₂ o₂ e₂ => wp_addImm (by decide) fun s₃ o₃ e₃ => wp_addImm (by decide)
    fun s₄ o₄ e₄ => wp_addImm (by decide) fun s₅ o₅ e₅ => wp_addImm (by decide) fun s₆ o₆ e₆ =>
    wp_addImm (by decide) fun s₇ o₇ e₇ => wp_addImm (by decide) fun s₈ o₈ e₈ => wp_movz fun s₉ o₉ e₉ => ?_
  have k₉ : Keep [.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x9] s s₉ :=
    (k₁.trans ((((((((o₂.trans o₃).trans o₄).trans o₅).trans o₆).trans o₇).trans o₈).trans o₉).keep)).mono
      (by decide)
  have hm₉ : s₉.mem = s₁.mem := by
    rw [o₉.mem, o₈.mem, o₇.mem, o₆.mem, o₅.mem, o₄.mem, o₃.mem, o₂.mem]
  have h19 : s₉.gpr .x19 = S := by
    rw [o₉.get .x19, o₈.get .x19, o₇.get .x19, o₆.get .x19, o₅.get .x19, o₄.get .x19, o₃.get .x19, e₂,
      BitVec.add_zero, k₁.get .x7, g _ (by decide), hS]
  have h23 : s₉.gpr .x23 = σ.gpr .x4 := by
    rw [o₉.get .x23, o₈.get .x23, o₇.get .x23, e₆, BitVec.add_zero, o₅.get .x4, o₄.get .x4, o₃.get .x4,
      o₂.get .x4, k₁.get .x4, g _ (by decide)]
  have hr : HRegs σ s₉ := by
    refine ⟨?_, ?_, ?_, h23, ?_, ?_⟩
    · rw [o₉.get .x20, o₈.get .x20, o₇.get .x20, o₆.get .x20, o₅.get .x20, o₄.get .x20, e₃, BitVec.add_zero,
        o₂.get .x1, k₁.get .x1, g _ (by decide)]
    · rw [o₉.get .x21, o₈.get .x21, o₇.get .x21, o₆.get .x21, o₅.get .x21, e₄, BitVec.add_zero,
        o₃.get .x2, o₂.get .x2, k₁.get .x2, g _ (by decide)]
    · rw [o₉.get .x22, o₈.get .x22, o₇.get .x22, o₆.get .x22, e₅, BitVec.add_zero,
        o₄.get .x3, o₃.get .x3, o₂.get .x3, k₁.get .x3, g _ (by decide)]
    · rw [o₉.get .x24, o₈.get .x24, e₇, BitVec.add_zero, o₆.get .x5, o₅.get .x5, o₄.get .x5, o₃.get .x5,
        o₂.get .x5, k₁.get .x5, g _ (by decide)]
    · rw [o₉.get .x25, e₈, BitVec.add_zero, o₇.get .x6, o₆.get .x6, o₅.get .x6, o₄.get .x6, o₃.get .x6,
        o₂.get .x6, k₁.get .x6, g _ (by decide)]
  refine wp_strb (a := S + BitVec.ofNat 64 Layout.oHdr) (by decide) (by rw [h19])
    (by rw [k₉.wr]; exact KeyGen.in_scr hw (by decide)) fun s₁₀ m₁₀ => ?_
  refine wp_strb (a := S + BitVec.ofNat 64 (Layout.oHdr + 1)) (by decide) (by rw [m₁₀.gpr, h19])
    (by rw [m₁₀.wr, k₉.wr]; exact KeyGen.in_scr hw (by decide)) fun s₁₁ m₁₁ => ?_
  have k₁₁ : Keep [.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x9] s s₁₁ :=
    (k₉.trans (m₁₀.keep.trans m₁₁.keep)).mono (by decide)
  -- the keys
  have hX : s₁₁.gpr .x0 = σ.gpr .x0 := by rw [k₁₁.get .x0, g _ (by decide)]
  have hr₁₁ : (⟨σ.gpr .x0, p.n * 4⟩ : Region) ∈ s₁₁.rd := by
    rw [k₁₁.rd, hs.rd, hK.rd]; simp [Params.skLen, Nat.mul_comm]
  rw [← List.append_nil ((List.range 4).flatMap fun c => copyWords .x19 (Layout.oKeys + 32 * c) .x0 (p.n * c) (p.n / 8))]
  refine KeyGen.copyIn_ok (n := p.n) hn h8 (xd := .x19) (xs := .x0) (by decide) (by decide) (D := S)
    (X := σ.gpr .x0) (by rw [m₁₁.gpr, m₁₀.gpr, h19]) hX (o := Layout.oKeys) (K := 4) (by decide) ⟨by decide, by decide⟩
    (by rw [k₁₁.wr]; exact KeyGen.in_scr hw (by decide)) ⟨_, List.mem_append_left _ hr₁₁, Region.contains_self _ _⟩
    (by omega) (by have := hK.f_sk; simp only [Params.skLen] at this; omega)
    (by
      have := hK.sk_scr
      rw [hS] at this
      simp only [Params.skLen] at this
      rw [Nat.mul_comm]
      exact this.sub_right (hsub (by decide))) fun t ht => wp_nil ?_
  have aH : S + BitVec.ofNat 64 Layout.oHdr + BitVec.ofNat 64 1 = S + BitVec.ofNat 64 (Layout.oHdr + 1) := addr_add _ _ _
  have hne : S + BitVec.ofNat 64 Layout.oHdr ≠ S + BitVec.ofNat 64 (Layout.oHdr + 1) :=
    Offset.add_ofNat_ne S (by omega) (by omega) (by omega)
  -- the writes, all in `scratch`
  have F₁₁ : Frame [⟨S + BitVec.ofNat 64 Layout.oHdr, 2⟩] s₉.mem s₁₁.mem := by
    rw [m₁₁.mem, m₁₀.mem]
    refine ((frame_write _ _ (k := 1) _).sub fun r hr => ?_).trans ((frame_write _ _ (k := 1) _).sub fun r hr => ?_) <;>
      simp only [List.mem_singleton] at hr <;> subst hr
    · exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩
    · exact ⟨_, List.mem_singleton_self _, Offset.sub S (by omega) (by omega)⟩
  have hsc' : ∀ {o l : Nat}, o + l ≤ scratchLen → ∀ r ∈ [(⟨S + BitVec.ofNat 64 o, l⟩ : Region)],
      ∃ r' ∈ [SCR σ, SIG p σ, below σ.sp 16], Region.Sub r r' := fun {o l} h r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self .., by show Region.Sub _ ⟨σ.gpr .x7, scratchLen⟩; rw [hS]; exact hsub h⟩
  have hall : Frame [SCR σ, SIG p σ, below σ.sp 16] σ.mem t.mem := by
    have h1 : Frame [SCR σ, SIG p σ, below σ.sp 16] s.mem s₁.mem :=
      f₁.sub (hsc' (by simp only [topSaved, List.length]; omega))
    have h2 : Frame [SCR σ, SIG p σ, below σ.sp 16] s₁.mem s₁₁.mem := by
      rw [← hm₉]; exact F₁₁.sub (hsc' (by omega))
    have h3 : Frame [SCR σ, SIG p σ, below σ.sp 16] s₁₁.mem t.mem := ht.frame.sub (hsc' (by omega))
    rw [← hs.mem]; exact h1.trans (h2.trans h3)
  refine ⟨⟨by rw [ht.keep.rd, k₁₁.rd, hs.rd], by rw [ht.keep.wr, k₁₁.wr, hs.wr], by rw [ht.keep.sp, k₁₁.sp, hs.sp],
    by rw [ht.keep.get .x19, m₁₁.gpr, m₁₀.gpr, h19, hS], fun r hr => ?_, fun r hr => ?_, fun i hi => ?_, ?_,
    fun c hc => ?_, hall⟩, ?_⟩
  · rw [ht.keep.get r (by revert r; decide), k₁₁.get r (by revert r; decide), g r (by revert r; decide)]
  · rw [ht.keep.vcs r hr, k₁₁.vcs r hr, hs.vcs r hr]
  · have d1 : ∀ r ∈ [(⟨S + BitVec.ofNat 64 Layout.oKeys, 32 * 4⟩ : Region)],
        Region.Disjoint ⟨S + BitVec.ofNat 64 (Layout.oTop + 8 * i), 8⟩ r := fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint S (by omega) (by omega) (by omega)
    have d2 : ∀ r ∈ [(⟨S + BitVec.ofNat 64 Layout.oHdr, 2⟩ : Region)],
        Region.Disjoint ⟨S + BitVec.ofNat 64 (Layout.oTop + 8 * i), 8⟩ r := fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint S (by omega) (by omega) (by omega)
    rw [hS, ht.frame.readW (Region.contains_self _ _) d1 (by decide),
      F₁₁.readW (Region.contains_self _ _) d2 (by decide), hm₉,
      sv₁ i (by simp only [topSaved, List.length]; omega)]
    obtain ⟨r, hr⟩ : ∃ r, topSaved[i]'(by simp only [topSaved, List.length]; omega) = r := ⟨_, rfl⟩
    have hr9 : r ≠ .x9 := by
      subst hr; exact (show ∀ q ∈ topSaved, q ≠ .x9 by decide) _ (List.getElem_mem _)
    rw [hr, g r hr9, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp only [topSaved, List.length]; omega),
      Option.getD_some, hr]
  · rw [hS, bytesAt_frame ht.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint S (by omega) (by omega) (by omega))
      (by omega), bytes2, aH, m₁₁.mem, write8_at, write8_off _ _ _ _ hne, m₁₀.mem, write8_at, m₁₀.gpr, h23, e₉]
    simp only [List.cons.injEq, and_true]
    exact ⟨by decide, BitVec.eq_of_toNat_eq (by simp)⟩
  · rw [hS, ht.bytes c hc]
    have hnc : p.n * c + p.n ≤ p.n * 4 := by
      have := Nat.mul_le_mul_left p.n (show c + 1 ≤ 4 by omega); rwa [Nat.mul_succ] at this
    rw [bytesAt_frame F₁₁ (fun r hr => ?_) (by omega), hm₉, bytesAt_frame f₁ (fun r hr => ?_) (by omega), hs.mem] <;>
      simp only [List.mem_singleton] at hr <;> subst hr
    · have := hK.sk_scr; rw [hS] at this; simp only [Params.skLen] at this
      exact (this.sub_left (Offset.sub_base (n := p.n) (k := 4 * p.n) _ (by omega))).sub_right (hsub (by first | omega | (simp only [topSaved, List.length]; omega)))
    · have := hK.sk_scr; rw [hS] at this; simp only [Params.skLen] at this
      exact (this.sub_left (Offset.sub_base (n := p.n) (k := 4 * p.n) _ (by omega))).sub_right (hsub (by first | omega | (simp only [topSaved, List.length]; omega)))
  · exact ⟨by rw [ht.keep.get .x20, m₁₁.gpr, m₁₀.gpr, hr.x20], by rw [ht.keep.get .x21, m₁₁.gpr, m₁₀.gpr, hr.x21],
      by rw [ht.keep.get .x22, m₁₁.gpr, m₁₀.gpr, hr.x22], by rw [ht.keep.get .x23, m₁₁.gpr, m₁₀.gpr, hr.x23],
      by rw [ht.keep.get .x24, m₁₁.gpr, m₁₀.gpr, hr.x24], by rw [ht.keep.get .x25, m₁₁.gpr, m₁₀.gpr, hr.x25]⟩

end VG.Proof.SlhDsa.AArch64.Sign
