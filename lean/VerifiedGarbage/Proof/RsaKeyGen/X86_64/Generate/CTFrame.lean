module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Generate.Classify
public import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # The frame's public words, for the taint analysis

Two runs with the same public descriptor have the same writable regions, the
frame first, and the same frame words 0 to 7 and 11 (the pointers and
lengths the controller loads): the taint analysis starts from `r12` and
`rsp` public, `r12` the frame's base and those words public (`genT`), and so
from any frame state of each (`AnyFrame`) — or, inside a call's frame of its
stack arguments, from `genT'` with `rsp` that frame's base.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Generate

open VG.Proof.RsaKeyGen.SearchFrame

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64.Generation (allocated allocated_rsp allocated_reg)
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch (limitOf)

/-- The writable regions in the frame: the frame, the key's buffer, `used`,
the working space and the state. -/
def genWr (p : GenPublic) : List Region := [p.frame, cK p, rU p, rS p, cS p]

/-- A frame state of some run with the public descriptor `p`. -/
def AnyFrame (p : GenPublic) (s : State) : Prop := ∃ original used st, GenFrame p original used st s

/-- The taint: `rs`, `r12` and `rsp` public, `r12` the frame's base, the
frame's words 0 to 7 and 11 public. -/
def genT (rs : List Reg) : X86_64.Taint.T :=
  { regs := .ofList (rs ++ [.r12, .rsp]), flags := false, lens := [160, 0, 0, 0, 0], bases := [(.r12, 0, 0)],
    slots := [(0, 0, 64), (0, 88, 8)] }

/-- The taint inside a call's frame of `k` octets: that frame first, `rsp`
its base. -/
def genT' (k : Nat) (rs : List Reg) : X86_64.Taint.T :=
  { regs := .ofList (rs ++ [.r12, .rsp]), flags := false, lens := [k, 160, 0, 0, 0, 0],
    bases := [(.rsp, 0, 0), (.r12, 1, 0)], slots := [(1, 0, 64), (1, 88, 8)] }

section

variable {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}

theorem GenFrame.wr_eq (h : GenFrame p original used st s) : s.wr = genWr p := by
  have hs : inScr original = rS p := by rw [← h.input.2]; rfl
  rw [h.wr, h.input.1.2.2.2.1]
  simp only [inWrites]
  rw [h.key_region, h.used_region, h.state_region, hs]; rfl

theorem genWr_wf (hf : CFacts p) (hfk : p.frame.Disjoint (cK p))
    (hfu : p.frame.Disjoint (rU p)) (hfs : p.frame.Disjoint (rS p)) (hft : p.frame.Disjoint (cS p)) :
    (genWr p).Pairwise Region.Disjoint ∧ ∀ r ∈ genWr p, r.len ≤ 2 ^ 64 := by
  refine ⟨?_, ?_⟩
  · simp only [genWr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨⟨hfk, hfu, hfs, hft⟩, ⟨hf.kU, hf.kS, hf.kT⟩, ⟨hf.uS, hf.uT⟩, hf.sT, fun _ h => h.elim⟩
  · simp only [genWr, List.mem_cons, List.not_mem_nil, or_false]
    have := hf.nK; have := hf.nS
    rintro r (rfl | rfl | rfl | rfl | rfl) <;> simp only <;> omega

theorem GenFrame.frame_facts (h : GenFrame p original used st s) :
    p.frame.Disjoint (cK p) ∧ p.frame.Disjoint (rU p) ∧ p.frame.Disjoint (rS p) ∧ p.frame.Disjoint (cS p) := by
  have hs : inScr original = rS p := by rw [← h.input.2]; rfl
  refine ⟨h.frame_key, ?_, ?_, h.state_frame⟩
  · have := h.input.frame_disjoint_writes (r := inUsed original) (by simp [inWrites])
    rwa [h.used_region] at this
  · have := h.input.frame_disjoint_writes (r := inScr original) (by simp [inWrites])
    rwa [hs] at this

end

/-- A word's bytes agree where the words do. -/
theorem word_bytes {m₁ m₂ : Mem} {a : Addr} (h : m₁.readW a 64 = m₂.readW a 64) {k : Nat} (hk : k < 8) :
    m₁ (a + BitVec.ofNat 64 k) = m₂ (a + BitVec.ofNat 64 k) := by
  rw [← byte_readW m₁ a (w := 64) (by omega), ← byte_readW m₂ a (w := 64) (by omega), h]

/-- Two frame states with the same descriptor agree on the frame's public
bytes. -/
theorem frame_slots {p : GenPublic} {s₁ s₂ : State} (h₁ : AnyFrame p s₁) (h₂ : AnyFrame p s₂) {k : Nat}
    (hk : k < 64 ∨ (88 ≤ k ∧ k < 96)) :
    s₁.mem (p.F + BitVec.ofNat 64 k) = s₂.mem (p.F + BitVec.ofNat 64 k) := by
  obtain ⟨o₁, u₁, t₁, g₁⟩ := h₁
  obtain ⟨o₂, u₂, t₂, g₂⟩ := h₂
  have hF : p.F.toNat + 160 ≤ 2 ^ 64 := g₁.scr.nowrap
  have hw (j : Nat) (v : BitVec 64) (hj : ∀ u, (j, v) ∈ p.headers u) :
      s₁.mem.readW (p.F + BitVec.ofNat 64 (8 * j)) 64 = s₂.mem.readW (p.F + BitVec.ofNat 64 (8 * j)) 64 :=
    (g₁.header (hj u₁)).trans (g₂.header (hj u₂)).symm
  have key (j : Nat) (v : BitVec 64) (hj : ∀ u, (j, v) ∈ p.headers u) (hk' : 8 * j ≤ k ∧ k < 8 * j + 8) :
      s₁.mem (p.F + BitVec.ofNat 64 k) = s₂.mem (p.F + BitVec.ofNat 64 k) := by
    rw [show p.F + BitVec.ofNat 64 k = p.F + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 (k - 8 * j) by
      rw [Offset.add_add]; congr 2; omega]
    exact word_bytes (hw j v hj) (by omega)
  have hq : k / 8 < 8 ∨ k / 8 = 11 := by omega
  rcases hq with hq | hq
  · have : k / 8 = 0 ∨ k / 8 = 1 ∨ k / 8 = 2 ∨ k / 8 = 3 ∨ k / 8 = 4 ∨ k / 8 = 5 ∨ k / 8 = 6 ∨ k / 8 = 7 := by omega
    rcases this with h | h | h | h | h | h | h | h
    · exact key 0 p.kp (fun _ => by simp [GenPublic.headers]) (by omega)
    · exact key 1 (BitVec.ofNat 64 p.L) (fun _ => by simp [GenPublic.headers]) (by omega)
    · exact key 2 p.up (fun _ => by simp [GenPublic.headers]) (by omega)
    · exact key 3 p.rp (fun _ => by simp [GenPublic.headers]) (by omega)
    · exact key 4 (BitVec.ofNat 64 p.randLen) (fun _ => by simp [GenPublic.headers]) (by omega)
    · exact key 5 p.B (fun _ => by simp [GenPublic.headers]) (by omega)
    · exact key 6 (BitVec.ofNat 64 (p.Z / 8)) (fun _ => by simp [GenPublic.headers]) (by omega)
    · exact key 7 p.stp (fun _ => by simp [GenPublic.headers]) (by omega)
  · exact key 11 (BitVec.ofNat 64 (limitOf p.L p.eB)) (fun _ => by simp [GenPublic.headers]) (by omega)

theorem any_agree {p : GenPublic} {rs : List Reg} {s₁ s₂ : State} (h₁ : AnyFrame p s₁) (h₂ : AnyFrame p s₂)
    (hrs : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) : X86_64.Taint.Agree (genT rs) s₁ s₂ := by
  obtain ⟨o₁, u₁, t₁, g₁⟩ := id h₁
  obtain ⟨o₂, u₂, t₂, g₂⟩ := id h₂
  have hf := g₁.input.cfacts
  obtain ⟨hfk, hfu, hfs, hft⟩ := g₁.frame_facts
  obtain ⟨hpw, hlen⟩ := genWr_wf hf hfk hfu hfs hft
  have wf : ∀ {s : State}, s.wr = genWr p → s.gpr .r12 = p.F → X86_64.Taint.Wf (genT rs) s := fun hw hr => by
    refine ⟨fun _ => ⟨?_, ?_, ?_⟩, fun q hq => ?_⟩
    · rw [hw]; exact .cons (Nat.le_refl _) (.cons (Nat.zero_le _) (.cons (Nat.zero_le _) (.cons (Nat.zero_le _)
        (.cons (Nat.zero_le _) .nil))))
    · rw [hw]; exact hpw
    · rw [hw]; exact hlen
    · simp only [genT, List.mem_singleton] at hq; subst hq
      simp only [X86_64.Taint.region, hw, genWr, List.getD_cons_zero]
      rw [hr, BitVec.add_zero]
  have hb : ∀ {s : State}, s.wr = genWr p → ∀ k, X86_64.Taint.byteAddr s 0 k = p.F + BitVec.ofNat 64 k := fun hw k => by
    simp only [X86_64.Taint.byteAddr, X86_64.Taint.region, hw, genWr, List.getD_cons_zero]
  refine ⟨⟨fun r hr => ?_, fun hf => by cases hf⟩, fun _ => by rw [g₁.wr_eq, g₂.wr_eq],
    wf g₁.wr_eq g₁.r12, wf g₂.wr_eq g₂.r12, fun sl hsl => ?_, fun sl hsl k hk₁ hk₂ => ?_, X86_64.Taint.noLo,
    X86_64.Taint.noXr⟩
  · rcases List.mem_append.mp (RegSet.mem_ofList.mp hr) with hr | hr
    · exact hrs r hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [g₁.r12, g₂.r12]
      · rw [g₁.rsp, g₂.rsp]
  · simp only [genT, List.mem_cons, List.not_mem_nil, or_false] at hsl
    rcases hsl with rfl | rfl <;> simp [genT]
  · simp only [genT, List.mem_cons, List.not_mem_nil, or_false] at hsl
    rcases hsl with rfl | rfl <;> simp only at hk₁ hk₂ ⊢ <;> rw [hb g₁.wr_eq, hb g₂.wr_eq]
    · exact frame_slots h₁ h₂ (.inl hk₂)
    · exact frame_slots h₁ h₂ (.inr ⟨hk₁, hk₂⟩)

/-- Code the taint analysis checks from `genT rs`. -/
theorem frame_taint {α : Type} {Φ : α → State → Prop} {c : Prog isa} (g : α → GenPublic) (rs : List Reg)
    (hΦ : ∀ a s, Φ a s → AnyFrame (g a) s) (hrs : Pins Φ rs) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (h : (taint.check (genT rs) c hc).isSome = true) : RelCT isa (Two Φ) c fun _ _ => True :=
  RelCT.taint (A := taint) (genT rs) (fun _ _ ⟨a, h₁, h₂⟩ => any_agree (hΦ a _ h₁) (hΦ a _ h₂) (hrs a _ _ h₁ h₂)) h

/-- Inside a call's frame of `k` octets below the controller's. -/
theorem alloc_agree {p : GenPublic} {rs : List Reg} {k : Nat} (hk : k ≤ 392) {s₁ s₂ : State}
    (h₁ : AnyFrame p s₁) (h₂ : AnyFrame p s₂)
    (hrs : ∀ r ∈ rs, (allocated k s₁).gpr r = (allocated k s₂).gpr r) :
    X86_64.Taint.Agree (genT' k rs) (allocated k s₁) (allocated k s₂) := by
  obtain ⟨o₁, u₁, t₁, g₁⟩ := id h₁
  obtain ⟨o₂, u₂, t₂, g₂⟩ := id h₂
  have hf := g₁.input.cfacts
  obtain ⟨hfk, hfu, hfs, hft⟩ := g₁.frame_facts
  obtain ⟨hpw, hlen⟩ := genWr_wf hf hfk hfu hfs hft
  have hst := hf.stack
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hst
  obtain ⟨sK, sU, sS, sT, -⟩ := hst
  have hFk : p.F - BitVec.ofNat 64 k = p.sp - BitVec.ofNat 64 (160 + k) := by
    rw [GenPublic.F, BitVec.sub_sub, BitVec.ofNat_add]
  have hA : Region.Sub ⟨p.F - BitVec.ofNat 64 k, k⟩ (cStack p) := by
    rw [hFk]; exact Offset.sub_below p.sp (by omega) (by omega)
  have hAF : (⟨p.F - BitVec.ofNat 64 k, k⟩ : Region).Disjoint p.frame := by
    have := Offset.sep_below p.sp 552 (a := 160 + k) (n := k) (b := 160) (k := 160) (by omega) (by decide)
      (Or.inl (by omega)) (by omega) (by decide)
    rw [← hFk] at this
    exact disj_of_sep this
  have hwr : ∀ {s : State} {o : State} {u : Nat} {t : KeyProgress}, GenFrame p o u t s →
      (allocated k s).wr = ⟨p.F - BitVec.ofNat 64 k, k⟩ :: genWr p := fun {s} _ _ _ g => by
    show (⟨s.gpr .rsp - BitVec.ofNat 64 k, k⟩ : Region) :: s.wr = _
    rw [g.rsp, g.wr_eq]
  have wf : ∀ {s : State} {o : State} {u : Nat} {t : KeyProgress}, GenFrame p o u t s →
      X86_64.Taint.Wf (genT' k rs) (allocated k s) := fun g => by
    refine ⟨fun _ => ⟨?_, ?_, ?_⟩, fun q hq => ?_⟩
    · rw [hwr g]; exact .cons (Nat.le_refl _) (.cons (Nat.le_refl _) (.cons (Nat.zero_le _) (.cons (Nat.zero_le _)
        (.cons (Nat.zero_le _) (.cons (Nat.zero_le _) .nil)))))
    · rw [hwr g]
      refine List.Pairwise.cons (fun r hr => ?_) hpw
      simp only [genWr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact hAF
      · exact (sK.sub_right hA).symm
      · exact (sU.sub_right hA).symm
      · exact (sS.sub_right hA).symm
      · exact (sT.sub_right hA).symm
    · rw [hwr g]
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · show k ≤ 2 ^ 64; omega
      · exact hlen r hr
    · simp only [genT', List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · simp only [X86_64.Taint.region, hwr g, List.getD_cons_zero]
        rw [allocated_rsp, g.rsp, BitVec.add_zero]
      · simp only [X86_64.Taint.region, hwr g, genWr, List.getD_cons_succ, List.getD_cons_zero]
        rw [allocated_reg _ _ _ (by decide), g.r12, BitVec.add_zero]
  have hb : ∀ {s : State} {o : State} {u : Nat} {t : KeyProgress}, GenFrame p o u t s → ∀ j,
      X86_64.Taint.byteAddr (allocated k s) 1 j = p.F + BitVec.ofNat 64 j := fun g j => by
    simp only [X86_64.Taint.byteAddr, X86_64.Taint.region, hwr g, genWr, List.getD_cons_succ, List.getD_cons_zero]
  refine ⟨⟨fun r hr => ?_, fun hf => by cases hf⟩, fun _ => by rw [hwr g₁, hwr g₂], wf g₁, wf g₂,
    fun sl hsl => ?_, fun sl hsl j hj₁ hj₂ => ?_, X86_64.Taint.noLo, X86_64.Taint.noXr⟩
  · rcases List.mem_append.mp (RegSet.mem_ofList.mp hr) with hr | hr
    · exact hrs r hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [allocated_reg _ _ _ (by decide), allocated_reg _ _ _ (by decide), g₁.r12, g₂.r12]
      · rw [allocated_rsp, allocated_rsp, g₁.rsp, g₂.rsp]
  · simp only [genT', List.mem_cons, List.not_mem_nil, or_false] at hsl
    rcases hsl with rfl | rfl <;> simp [genT']
  · simp only [genT', List.mem_cons, List.not_mem_nil, or_false] at hsl
    rcases hsl with rfl | rfl <;> simp only at hj₁ hj₂ ⊢ <;> rw [hb g₁, hb g₂] <;>
      simp only [VG.Proof.Ffdh.X86_64.Generation.allocated_mem]
    · exact frame_slots h₁ h₂ (.inl hj₂)
    · exact frame_slots h₁ h₂ (.inr ⟨hj₁, hj₂⟩)

end VG.Proof.RsaKeyGen.X86_64.Generate
