module

-- separate module: the state of the body and its first block, which the hash, the calls and the constant-time proofs share

public import VerifiedGarbage.Proof.SlhDsa.AArch64.VerifyTop
public import VerifiedGarbage.Proof.SlhDsa.AArch64.SignPro
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-!
# SLH-DSA (SHAKE) on AArch64, `verify`: the body's first block

From the entry state `σ` (`scratch = S = x7`, `sig = x5`): `Ctx` holds once
the body's first block has saved the caller's registers at `oTop`, kept the
arguments in `x19`–`x24`, written the formatted message's header at `oHdr`
and copied `PK.seed` and `PK.root` to `oPkSeed` and `oPkRoot` (`pro_ok`):
the permissions and `sp`, `x19 = S`, `x24 = sig`, the callee-saved registers
no code writes, the saved registers, the header and the keys, and that
memory changed only in `scratch` and the 16 bytes below `sp`. Writes in
`scratch` outside `PROT` (`oTop` to `oDigest`) or below `sp` keep it
(`Ctx.of_frame`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.VerifyTop

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.AArch64 (Layout copyWords saveRegsAt)
open VG.Impl.SlhDsa.AArch64.Thash4 (mov)
open VG.Impl.SlhDsa.AArch64.Shake (topSaved)
open VG.Proof.SlhDsa.AArch64.Sign (SCR PROT untouched prot_sub write8_at write8_off bytes2)
open VG.Proof.MlKem.AArch64 (Only Keep wp_nil wp_addImm wp_movz wp_strb)

/-- In the body, after its first block. -/
structure Ctx (p : Params) (σ t : State) : Prop where
  rd : t.rd = σ.rd
  wr : t.wr = σ.wr
  sp : t.sp = σ.sp
  x19 : t.gpr .x19 = σ.gpr .x7
  x24 : t.gpr .x24 = σ.gpr .x5
  cs : ∀ r ∈ untouched, t.gpr r = σ.gpr r
  vcs : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (σ.v r).extractLsb' 0 64
  saved : ∀ i < 8, t.mem.readW (at' (σ.gpr .x7) (Layout.oTop + 8 * i)) 64 = σ.gpr (topSaved.getD i .x19)
  hdr : bytesAt t.mem (at' (σ.gpr .x7) Layout.oHdr) 2 = [0, BitVec.ofNat 8 (σ.gpr .x4).toNat]
  keys : ∀ c < 2, bytesAt t.mem (at' (σ.gpr .x7) (Layout.oPkSeed + 32 * c)) p.n =
    bytesAt σ.mem (σ.gpr .x0 + BitVec.ofNat 64 (p.n * c)) p.n
  frame : Frame [SCR σ, below σ.sp 16] σ.mem t.mem

/-- The registers the hash reads: `msg`, `msg_len`, `ctx`, `ctx_len`. -/
structure HRegs (σ t : State) : Prop where
  x20 : t.gpr .x20 = σ.gpr .x1
  x21 : t.gpr .x21 = σ.gpr .x2
  x22 : t.gpr .x22 = σ.gpr .x3
  x23 : t.gpr .x23 = σ.gpr .x4

/-- A region the body may write without breaking `Ctx`. -/
def Free (σ : State) (r : Region) : Prop :=
  (Region.Sub r (SCR σ) ∧ r.Disjoint (PROT σ)) ∨ Region.Sub r (below σ.sp 16)

theorem frame_free {σ : State} {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (h : ∀ r ∈ rs, Free σ r) : Frame [SCR σ, below σ.sp 16] m m' :=
  hf.sub fun r hr => by
    rcases h r hr with ⟨h1, -⟩ | h1
    · exact ⟨_, List.mem_cons_self .., h1⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), h1⟩

/-- Bytes of `PROT` are kept by writes in free regions. -/
theorem prot_keep {p : Params} {σ : State} (hK : VG p σ) {rs : List Region}
    (h : ∀ r ∈ rs, Free σ r) {a : Addr} {n : Nat} (ha : Region.Sub ⟨a, n⟩ (PROT σ)) :
    ∀ r ∈ rs, Region.Disjoint ⟨a, n⟩ r := fun r hr => by
  rcases h r hr with ⟨-, h1⟩ | h1
  · exact (h1.symm.sub_left ha)
  · exact (hK.stk_scr.symm.sub_left (fun x hx => Offset.sub_base _ (by simp only [scratchLen]; decide) x (ha x hx))).sub_right h1

theorem Ctx.of_frame {p : Params} (hn : p.n ≤ 32) {σ t t' : State} (hK : VG p σ) (hc : Ctx p σ t) (hrd : t'.rd = t.rd)
    (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp) (h19 : t'.gpr .x19 = t.gpr .x19) (h24 : t'.gpr .x24 = t.gpr .x24)
    (hcs : ∀ r ∈ untouched, t'.gpr r = t.gpr r)
    (hv : ∀ r ∈ preservedV, (t'.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64)
    {rs : List Region} (hf : Frame rs t.mem t'.mem) (hfr : ∀ r ∈ rs, Free σ r) : Ctx p σ t' := by
  have eT : Layout.oTop = 1536 := rfl
  refine ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp, h19.trans hc.x19, h24.trans hc.x24,
    fun r hr => (hcs r hr).trans (hc.cs r hr), fun r hr => (hv r hr).trans (hc.vcs r hr), fun i hi => ?_, ?_,
    fun c hc' => ?_, hc.frame.trans (frame_free hf hfr)⟩
  · rw [hf.readW (r := ⟨at' (σ.gpr .x7) (Layout.oTop + 8 * i), 8⟩) (Region.contains_self _ _)
      (prot_keep hK hfr (prot_sub σ (by omega) (by omega))) (by decide)]
    exact hc.saved i hi
  · rw [bytesAt_frame hf (prot_keep hK hfr (prot_sub σ (by simp only [Layout.oHdr]; omega)
      (by simp only [Layout.oHdr]; omega))) (by decide)]
    exact hc.hdr
  · rw [bytesAt_frame hf (prot_keep hK hfr (prot_sub σ (by simp only [Layout.oPkSeed, Layout.oKeys]; omega)
      (by simp only [Layout.oPkSeed, Layout.oKeys]; omega))) (by omega)]
    exact hc.keys c hc'

/-- A step that writes no memory and keeps `x19`, `x24` and the untouched registers keeps `Ctx`. -/
theorem Ctx.of_keep {p : Params} (hn : p.n ≤ 32) {σ t t' : State} (hK : VG p σ) (hc : Ctx p σ t) {rs : List Reg}
    (hk : Only rs t t') (h19 : Reg.x19 ∉ rs) (h24 : Reg.x24 ∉ rs) (hu : ∀ r ∈ untouched, r ∉ rs) : Ctx p σ t' :=
  hc.of_frame hn hK hk.keep.rd hk.keep.wr hk.keep.sp (hk.get .x19 h19) (hk.get .x24 h24) (fun r hr => hk.get r (hu r hr))
    hk.keep.vcs
    (rs := []) (fun x _ => by rw [hk.mem]) (fun _ h => absurd h List.not_mem_nil)

/-! ## The first block -/

/-- The body's first block. -/
abbrev proCode (p : Params) : List Instr :=
  saveRegsAt Layout.oTop .x7 topSaved ++
    [mov .x19 .x7, mov .x20 .x1, mov .x21 .x2, mov .x22 .x3, mov .x23 .x4, mov .x24 .x5,
      .movz .x .x9 0 0, .strb .x9 .x19 Layout.oHdr, .strb .x23 .x19 (Layout.oHdr + 1)] ++
    (List.range 2).flatMap (fun c => copyWords .x19 (Layout.oPkSeed + 32 * c) .x0 (p.n * c) (p.n / 8))

theorem pro_ok {p : Params} (hz : Sz p) {σ s : State} (hK : VG p σ) (hs : Only [.x9, .x10] σ s) :
    WP isa (.block (proCode p)) s fun t => Ctx p σ t ∧ HRegs σ t := by
  have hn := hz.n32
  have h8 := hz.n8
  have hsc : scratchLen = 65536 := rfl
  have eT : Layout.oTop = 1536 := rfl
  have eH : Layout.oHdr = 1632 := rfl
  have eK : Layout.oPkSeed = 1728 := rfl
  have hpk : p.pkLen = p.n * 2 := by simp only [Params.pkLen]; omega
  have g : ∀ r, r ≠ .x9 → r ≠ .x10 → s.gpr r = σ.gpr r := fun r h h' => hs.get r (by simp [h, h'])
  obtain ⟨S, hS⟩ : ∃ S, σ.gpr .x7 = S := ⟨_, rfl⟩
  have fS : S.toNat + scratchLen ≤ 2 ^ 64 := by rw [← hS]; exact hK.f_scr
  have hw : (⟨S, scratchLen⟩ : Region) ∈ s.wr := by rw [hs.wr, hK.wr, hS]; simp
  have hsub : ∀ {o l : Nat}, o + l ≤ scratchLen → Region.Sub ⟨S + BitVec.ofNat 64 o, l⟩ ⟨S, scratchLen⟩ :=
    fun h => Offset.sub_base S h
  simp only [proCode, List.append_assoc, List.cons_append, List.nil_append]
  refine saveRegsAt_ok (s := s) (b := .x7) ⟨by decide, by decide⟩
    (by rw [g _ (by decide) (by decide), hS]; exact KeyGen.in_scr hw (by decide)) fun s₁ k₁ sv₁ f₁ => ?_
  rw [g _ (by decide) (by decide), hS] at sv₁ f₁
  refine wp_addImm (by decide) fun s₂ o₂ e₂ => wp_addImm (by decide) fun s₃ o₃ e₃ => wp_addImm (by decide)
    fun s₄ o₄ e₄ => wp_addImm (by decide) fun s₅ o₅ e₅ => wp_addImm (by decide) fun s₆ o₆ e₆ =>
    wp_addImm (by decide) fun s₇ o₇ e₇ => wp_movz fun s₉ o₉ e₉ => ?_
  have k₉ : Keep [.x19, .x20, .x21, .x22, .x23, .x24, .x9] s s₉ :=
    (k₁.trans (((((((o₂.trans o₃).trans o₄).trans o₅).trans o₆).trans o₇).trans o₉).keep)).mono
      (by decide)
  have hm₉ : s₉.mem = s₁.mem := by
    rw [o₉.mem, o₇.mem, o₆.mem, o₅.mem, o₄.mem, o₃.mem, o₂.mem]
  have h19 : s₉.gpr .x19 = S := by
    rw [o₉.get .x19, o₇.get .x19, o₆.get .x19, o₅.get .x19, o₄.get .x19, o₃.get .x19, e₂,
      BitVec.add_zero, k₁.get .x7, g _ (by decide) (by decide), hS]
  have h23 : s₉.gpr .x23 = σ.gpr .x4 := by
    rw [o₉.get .x23, o₇.get .x23, e₆, BitVec.add_zero, o₅.get .x4, o₄.get .x4, o₃.get .x4,
      o₂.get .x4, k₁.get .x4, g _ (by decide) (by decide)]
  have h24 : s₉.gpr .x24 = σ.gpr .x5 := by
    rw [o₉.get .x24, e₇, BitVec.add_zero, o₆.get .x5, o₅.get .x5, o₄.get .x5, o₃.get .x5,
      o₂.get .x5, k₁.get .x5, g _ (by decide) (by decide)]
  have hr : HRegs σ s₉ := by
    refine ⟨?_, ?_, ?_, h23⟩
    · rw [o₉.get .x20, o₇.get .x20, o₆.get .x20, o₅.get .x20, o₄.get .x20, e₃, BitVec.add_zero,
        o₂.get .x1, k₁.get .x1, g _ (by decide) (by decide)]
    · rw [o₉.get .x21, o₇.get .x21, o₆.get .x21, o₅.get .x21, e₄, BitVec.add_zero,
        o₃.get .x2, o₂.get .x2, k₁.get .x2, g _ (by decide) (by decide)]
    · rw [o₉.get .x22, o₇.get .x22, o₆.get .x22, e₅, BitVec.add_zero,
        o₄.get .x3, o₃.get .x3, o₂.get .x3, k₁.get .x3, g _ (by decide) (by decide)]
  refine wp_strb (a := S + BitVec.ofNat 64 Layout.oHdr) (by decide) (by rw [h19])
    (by rw [k₉.wr]; exact KeyGen.in_scr hw (by decide)) fun s₁₀ m₁₀ => ?_
  refine wp_strb (a := S + BitVec.ofNat 64 (Layout.oHdr + 1)) (by decide) (by rw [m₁₀.gpr, h19])
    (by rw [m₁₀.wr, k₉.wr]; exact KeyGen.in_scr hw (by decide)) fun s₁₁ m₁₁ => ?_
  have k₁₁ : Keep [.x19, .x20, .x21, .x22, .x23, .x24, .x9] s s₁₁ :=
    (k₉.trans (m₁₀.keep.trans m₁₁.keep)).mono (by decide)
  -- the keys
  have hX : s₁₁.gpr .x0 = σ.gpr .x0 := by rw [k₁₁.get .x0, g _ (by decide) (by decide)]
  have hr₁₁ : (⟨σ.gpr .x0, p.n * 2⟩ : Region) ∈ s₁₁.rd := by
    rw [k₁₁.rd, hs.rd, hK.rd, ← hpk]; simp
  rw [← List.append_nil ((List.range 2).flatMap fun c => copyWords .x19 (Layout.oPkSeed + 32 * c) .x0 (p.n * c) (p.n / 8))]
  refine KeyGen.copyIn_ok (n := p.n) hn h8 (xd := .x19) (xs := .x0) (by decide) (by decide) (D := S)
    (X := σ.gpr .x0) (by rw [m₁₁.gpr, m₁₀.gpr, h19]) hX (o := Layout.oPkSeed) (K := 2) (by decide) ⟨by decide, by decide⟩
    (by rw [k₁₁.wr]; exact KeyGen.in_scr hw (by decide)) ⟨_, List.mem_append_left _ hr₁₁, Region.contains_self _ _⟩
    (by omega) (by have := hK.f_pk; omega)
    (by
      have := hK.pk_scr
      rw [hS, hpk] at this
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
      ∃ r' ∈ [SCR σ, below σ.sp 16], Region.Sub r r' := fun {o l} h r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self .., by show Region.Sub _ ⟨σ.gpr .x7, scratchLen⟩; rw [hS]; exact hsub h⟩
  have hall : Frame [SCR σ, below σ.sp 16] σ.mem t.mem := by
    have h1 : Frame [SCR σ, below σ.sp 16] s.mem s₁.mem :=
      f₁.sub (hsc' (by simp only [topSaved, List.length]; omega))
    have h2 : Frame [SCR σ, below σ.sp 16] s₁.mem s₁₁.mem := by
      rw [← hm₉]; exact F₁₁.sub (hsc' (by omega))
    have h3 : Frame [SCR σ, below σ.sp 16] s₁₁.mem t.mem := ht.frame.sub (hsc' (by omega))
    rw [← hs.mem]; exact h1.trans (h2.trans h3)
  refine ⟨⟨by rw [ht.keep.rd, k₁₁.rd, hs.rd], by rw [ht.keep.wr, k₁₁.wr, hs.wr], by rw [ht.keep.sp, k₁₁.sp, hs.sp],
    by rw [ht.keep.get .x19, m₁₁.gpr, m₁₀.gpr, h19, hS], by rw [ht.keep.get .x24, m₁₁.gpr, m₁₀.gpr, h24],
    fun r hr => ?_, fun r hr => ?_, fun i hi => ?_, ?_, fun c hc => ?_, hall⟩, ?_⟩
  · rw [ht.keep.get r (by revert r; decide), k₁₁.get r (by revert r; decide),
      g r (by revert r; decide) (by revert r; decide)]
  · rw [ht.keep.vcs r hr, k₁₁.vcs r hr, hs.vcs r hr]
  · have d1 : ∀ r ∈ [(⟨S + BitVec.ofNat 64 Layout.oPkSeed, 32 * 2⟩ : Region)],
        Region.Disjoint ⟨S + BitVec.ofNat 64 (Layout.oTop + 8 * i), 8⟩ r := fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint S (by omega) (by omega) (by omega)
    have d2 : ∀ r ∈ [(⟨S + BitVec.ofNat 64 Layout.oHdr, 2⟩ : Region)],
        Region.Disjoint ⟨S + BitVec.ofNat 64 (Layout.oTop + 8 * i), 8⟩ r := fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint S (by omega) (by omega) (by omega)
    rw [hS, ht.frame.readW (Region.contains_self _ _) d1 (by decide),
      F₁₁.readW (Region.contains_self _ _) d2 (by decide), hm₉,
      sv₁ i (by simp only [topSaved, List.length]; omega)]
    obtain ⟨r, hr⟩ : ∃ r, topSaved[i]'(by simp only [topSaved, List.length]; omega) = r := ⟨_, rfl⟩
    have hr9 : r ≠ .x9 ∧ r ≠ .x10 := by
      subst hr; exact (show ∀ q ∈ topSaved, q ≠ .x9 ∧ q ≠ .x10 by decide) _ (List.getElem_mem _)
    rw [hr, g r hr9.1 hr9.2, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by simp only [topSaved, List.length]; omega), Option.getD_some, hr]
  · rw [hS, bytesAt_frame ht.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint S (by omega) (by omega) (by omega))
      (by omega), bytes2, aH, m₁₁.mem, write8_at, write8_off _ _ _ _ hne, m₁₀.mem, write8_at, m₁₀.gpr, h23, e₉]
    simp only [List.cons.injEq, and_true]
    exact ⟨by decide, BitVec.eq_of_toNat_eq (by simp)⟩
  · rw [hS, ht.bytes c hc]
    have hnc : p.n * c + p.n ≤ p.n * 2 := by
      have := Nat.mul_le_mul_left p.n (show c + 1 ≤ 2 by omega); rwa [Nat.mul_succ] at this
    rw [bytesAt_frame F₁₁ (fun r hr => ?_) (by omega), hm₉, bytesAt_frame f₁ (fun r hr => ?_) (by omega), hs.mem] <;>
      simp only [List.mem_singleton] at hr <;> subst hr
    · have := hK.pk_scr; rw [hS, hpk] at this
      exact (this.sub_left (Offset.sub_base (n := p.n) (k := p.n * 2) _ (by omega))).sub_right
        (hsub (by first | omega | (simp only [topSaved, List.length]; omega)))
    · have := hK.pk_scr; rw [hS, hpk] at this
      exact (this.sub_left (Offset.sub_base (n := p.n) (k := p.n * 2) _ (by omega))).sub_right
        (hsub (by first | omega | (simp only [topSaved, List.length]; omega)))
  · exact ⟨by rw [ht.keep.get .x20, m₁₁.gpr, m₁₀.gpr, hr.x20], by rw [ht.keep.get .x21, m₁₁.gpr, m₁₀.gpr, hr.x21],
      by rw [ht.keep.get .x22, m₁₁.gpr, m₁₀.gpr, hr.x22], by rw [ht.keep.get .x23, m₁₁.gpr, m₁₀.gpr, hr.x23]⟩

end VG.Proof.SlhDsa.AArch64.VerifyTop
