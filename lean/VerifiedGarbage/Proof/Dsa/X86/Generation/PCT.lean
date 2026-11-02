module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.PAttempt
import VerifiedGarbage.Proof.Dsa.X86.Generation.QCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.TimingFlags
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86.Syms
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Geo
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TestCT
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TimingBase
import VerifiedGarbage.Proof.Dsa.X86.Generation.AddBE
import VerifiedGarbage.Proof.Dsa.X86.Generation.Base
import VerifiedGarbage.Proof.Dsa.X86.Generation.Copy
import VerifiedGarbage.Proof.Dsa.X86.Generation.Words

/-! # Two runs of p's search from the same seed leak the same -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Dsa.X86.Generation
open VG.Impl.Mont.X86 (sc)

/-- Before a hash of X: seed `a.1` and the counter's offset `a.2`. -/
def PH (E : Env) (g : Geo) (a : Nat × Nat) (s : State) : Prop :=
  Base E s ∧ (a.1 + 1) * E.qLen ≤ E.seedsLen ∧
    s.mem.readW (off E.base fSeed) 32 = (E.seeds + BitVec.ofNat 64 (a.1 * E.qLen)).setWidth 32 ∧
    s.mem.readW (off E.base fOffset) 32 = BitVec.ofNat 32 a.2 ∧ a.2 + g.count + 256 ≤ 2 ^ 32

theorem addBE_erase (n : Nat) : Code.erase (addBE n) = Code.erase (addBE 1) := rfl

theorem pHash_ct {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hq : E.qLen = g.qLen) {j : Nat}
    (hj : j ≤ g.count) : RelCT isa (Both (PH E g)) (g.pHash j) (Both (PH E g)) := by
  have sz := v.size_ge
  have nl := G.hash.N_le
  have bd := G.bounds
  have hN := G.N
  have Ap := hRanges_apart G v hj
  have hjq : (j + 1) * g.qLen ≤ (g.count + 1) * g.qLen := Nat.mul_le_mul_right _ (by omega)
  refine both_post ?_ fun a s h => WP.mono (pHash_ok G v hq h.1 h.2.1 h.2.2.1 h.2.2.2.1
    (by have := h.2.2.2.2; omega) hj)
    fun t ⟨B', _, C, _⟩ => ⟨B', h.2.1, ?_, ?_, h.2.2.2.2⟩
  rotate_left
  · rw [Env.Chg.word v C (by simp only [fSeed, hdr]; omega) (fun o ho => ⟨(Ap o ho).1, by
      simp only [hRanges, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl <;> simp only [hashAt, sState, sHScr, sX, fSeed, hdr] <;> omega⟩),
      h.2.2.1]
  · rw [Env.Chg.word v C (by simp only [fOffset, hdr]; omega) (fun o ho => ⟨(Ap o ho).1, by
      simp only [hRanges, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl <;> simp only [hashAt, sState, sHScr, sX, fOffset, hdr] <;> omega⟩),
      h.2.2.2.1]
  unfold Geo.pHash
  simp only [seqs]
  -- The seed.
  refine RelCT.seq (both_post (Ψ := fun a t => Base E t ∧ t.mem.readW (off E.base fOffset) 32 = BitVec.ofNat 32 a.2 ∧
      a.2 + g.count + 256 ≤ 2 ^ 32)
    (both_map (fun a => (E.seeds + BitVec.ofNat 64 (a.1 * E.qLen)).setWidth 32) (fun a s h => ⟨h.1, h.2.2.1⟩)
      (copyIn_ct v (w := fSeed) (by decide) _ _)) fun a s h => ?_) ?_
  · refine VG.X86.WP.mono_syms (seedIn_ok G v hq h.1 h.2.1 h.2.2.1) fun t₁ ⟨_, F₁, K₁⟩ sy₁ => ?_
    have C₁ : E.Chg (hRanges g j) s.mem t₁.mem := Env.Chg.of_frame F₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Env.in_range (o := (sState, 128)) (by simp [hRanges]) (by omega) (by simp only [sState]; omega)
    refine ⟨h.1.keep v C₁ Ap (K₁.1 _ (by decide)) (K₁.1 _ (by decide)) K₁.2.1 K₁.2.2 sy₁, ?_, h.2.2.2.2⟩
    rw [Env.Chg.word v C₁ (by simp only [fOffset, hdr]; omega) (fun o ho => ⟨(Ap o ho).1, by
      simp only [hRanges, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl <;> simp only [hashAt, sState, sHScr, sX, fOffset, hdr] <;> omega⟩),
      h.2.2.2.1]
  -- `seed + offset + j`'s addend and the end of the seed.
  refine RelCT.seq (both_post (Ψ := fun a t => Base E t ∧
      t.gpr .edx = E.base.setWidth 32 + BitVec.ofNat 32 (sState + g.H.N + g.qLen - 1) ∧
      t.gpr .ecx = BitVec.ofNat 32 (a.2 + j) ∧ a.2 + j + 256 ≤ 2 ^ 32)
    (both_agree [.esp, .edi] (fun _ => baseVal E) (fun _ _ h => base_pins h.1)
      (tcheckE _ _ (.block (scr .edx 0 ++ [.mov .ecx (.mem (sc 0)), .alu .add .ecx (.imm (BitVec.ofNat 32 0))]))
        rfl (by decide +kernel) (by decide +kernel))) fun a t h => ?_) ?_
  · refine scr_ok fun t₂ e₂ g₂ m₂ rd₂ wr₂ sy₂ =>
      ld_ok (Scr.of_eq h.1.scr (g₂ _ (by decide)) (g₂ _ (by decide)) wr₂) (d := fOffset)
        (by simp only [fOffset, hdr]; omega) fun t₃ u₃ => wp_addi fun t₄ u₄ => WP.block_nil ?_
    have edi₄ : t₄.gpr .edi = t.gpr .edi := by rw [u₄.other _ (by decide), u₃.other _ (by decide), g₂ _ (by decide)]
    have esp₄ : t₄.gpr .esp = t.gpr .esp := by rw [u₄.other _ (by decide), u₃.other _ (by decide), g₂ _ (by decide)]
    refine ⟨h.1.regs (by rw [u₄.mem, u₃.mem, m₂]) edi₄ esp₄ (by rw [u₄.rd, u₃.rd, rd₂]) (by rw [u₄.wr, u₃.wr, wr₂])
      (by rw [u₄.syms, u₃.syms, sy₂]), ?_, ?_, by omega⟩
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), e₂, h.1.edi]
    · rw [u₄.gpr, u₃.gpr, m₂, h.2.1, BitVec.ofNat_add]
  -- The addition.
  refine RelCT.seq (both_post (Ψ := fun _ t => Base E t)
    (both_agree [.esp, .edi, .edx] (fun _ r => if r = .edx then
        E.base.setWidth 32 + BitVec.ofNat 32 (sState + g.H.N + g.qLen - 1) else baseVal E r)
      (fun a t h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact base_pins h.1 _ (by simp)
        · exact base_pins h.1 _ (by simp)
        · exact h.2.1)
      (tcheckE _ _ (addBE 1) (addBE_erase _) (by decide +kernel) (by decide +kernel))) fun a t h => ?_) ?_
  · have hs := h.1.scr
    refine VG.X86.WP.mono_syms (addBE_ok hs (o := sState + g.H.N) (n := g.qLen) (c := a.2 + j)
      (by omega) (by simp only [sState]; omega) h.2.2.2 (by rw [h.2.1, h.1.edi]) h.2.2.1) fun t₅ ⟨_, F₅, K₅, _⟩ sy₅ => ?_
    refine h.1.keep v (os := [(sState, 128)]) (Env.Chg.of_frame F₅ fun r hr => ?_) (fun o ho => ?_)
      (K₅.1 _ (by decide)) (K₅.1 _ (by decide)) K₅.2.1 K₅.2.2 sy₅
    · simp only [List.mem_singleton] at hr; subst hr
      exact Env.in_range (o := (sState, 128)) (List.mem_singleton_self _) (by omega) (by simp only [sState]; omega)
    · simp only [List.mem_singleton] at ho; subst ho
      simp only [sState, fOut, fHs, fWitLen, hdr]; omega
  -- The hash.
  exact both_map (fun _ => ()) (fun _ _ h => h) (hash_ct G v _)

theorem pX_ct {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hq : E.qLen = g.qLen) :
    RelCT isa (Both (PH E g)) g.pX fun _ _ => True := by
  unfold Geo.pX
  refine seqs_last (fun p hp => ?_) (both_agree [.esp, .edi] (fun _ => baseVal E) (fun _ _ h => base_pins h.1)
    (tcheckE _ _ (.block (orByte 0 0x80 ++ orByte 0 1)) rfl (by decide +kernel) (by decide +kernel)))
  simp only [List.mem_map, List.mem_range] at hp
  obtain ⟨j, hj, rfl⟩ := hp
  exact pHash_ct G v hq (by omega)

/-- p's arithmetic: its trace depends only on `esp` and `edi`, which it keeps. -/
theorem pArith_ct {g : Geo} (G : GeoOk g) :
    RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (pArith g.pLen g.qLen) (VG.X86.Taint.Agree (τr [.esp, .edi])) := by
  rcases G.lengths with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rw [h₁, h₂] <;> exact tkeep _ _ (by decide +kernel)

/-- Before a counter's candidate. -/
structure PAIn (E : Env) (g : Geo) (k offset Q used : Nat) (s : State) : Prop where
  base : Base E s
  hk : (k + 1) * E.qLen ≤ E.seedsLen
  seed : s.mem.readW (off E.base fSeed) 32 = (E.seeds + BitVec.ofNat 64 (k * E.qLen)).setWidth 32
  offW : s.mem.readW (off E.base fOffset) 32 = BitVec.ofNat 32 offset
  hoff : offset + g.count + 256 ≤ 2 ^ 32
  q : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off E.base (sPk + g.pLen)) g.qLen) = Q
  q0 : 0 < Q
  usedW : s.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 used
  hu : used ≤ E.witLen
  p4 : s.mem.readW (off E.base fP) 32 = BitVec.ofNat 32 4

/-- `PAIn` with its parameters together. -/
abbrev PAIn' (E : Env) (g : Geo) (a : Nat × Nat × Nat × Nat) : State → Prop := PAIn E g a.1 a.2.1 a.2.2.1 a.2.2.2

/-- The candidate into the test's working space. -/
theorem paCopy_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) {k offset Q used : Nat} {s s₅ : State}
    (F : PAFront E g k offset Q used s s₅) (hu : used ≤ E.witLen)
    (hge : ¬ pcand g E k offset Q < 2 ^ (8 * g.pLen - 1)) :
    WP isa (copyS (sPP + (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.pLen)).candidate) sPk g.pLen) s₅
      (TPre E (8 * g.pLen) (used, pcand g E k offset Q)) := by
  have sz := v.size_ge
  have bd := G.bounds
  have nw := v.scratchFit
  have Apa := paRanges_apart G v
  have e256 : (256 : Nat) ^ g.pLen = 2 ^ (8 * g.pLen) := by rw [Nat.pow_mul]
  have lay : (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.pLen)).size ≤ 8 * ppWords := by
    rcases G.lengths with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> decide
  have candLe : (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.pLen)).candidate + g.pLen ≤ 8 * ppWords := by
    simp only [VG.Impl.Dsa.X86.ProbablePrime.layout] at lay ⊢; omega
  refine VG.X86.WP.mono_syms (copyS_ok F.base.scr
    (dst := sPP + (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.pLen)).candidate) (src := sPk) (n := g.pLen)
    (by omega) (by simp only [sPP, ppWords] at candLe ⊢; omega) (by simp only [sPk]; omega)
    (by right; simp only [sPP, sPk]; omega)) fun t₆ ⟨R₆, F₆, K₆⟩ sy₆ => ?_
  have pp : (sPP, 8 * ppWords) ∈ paRanges g := by simp [paRanges]
  have C₆ : E.Chg [(sPP, 8 * ppWords)] s₅.mem t₆.mem := Env.Chg.of_frame F₆ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Env.in_range (List.mem_singleton_self _) (by omega) (by omega)
  have App : E.Apart [(sPP, 8 * ppWords)] := fun o ho => Apa o (by simp only [List.mem_singleton] at ho; rw [ho]; exact pp)
  refine ⟨F.base.keep v C₆ App (K₆.1 _ (by decide)) (K₆.1 _ (by decide)) K₆.2.1 K₆.2.2 sy₆, ?_, hu, ?_, F.odd,
    (VG.Proof.Dsa.bitLength_iff_bounds (by omega)).mpr ⟨by omega, F.lt⟩⟩
  · rw [Env.Chg.word v C₆ (by simp only [fUsed, hdr]; omega) (fun o ho => by
      simp only [List.mem_singleton] at ho; subst ho; simp only [sPP, ppWords, fUsed, hdr]; omega), F.used]
  · unfold Proof.Dsa.ProbablePrime.candidateAt
    have b8 : (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.pLen)).bits / 8 = g.pLen := by
      show 8 * g.pLen / 8 = g.pLen; omega
    rw [b8, VG.Offset.add_add, R₆, F.pk, VG.Proof.Dsa.decodeBE_encodeBE (by rw [e256]; exact F.lt)]

theorem pAttempt_ct {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hq : E.qLen = g.qLen) :
    RelCT isa (Both (PAIn' E g)) g.pAttempt fun _ _ => True := by
  have sz := v.size_ge
  have lay : (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.pLen)).size ≤ 8 * ppWords := by
    rcases G.lengths with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> decide
  unfold Geo.pAttempt
  simp only [seqs]
  -- X.
  refine RelCT.seq (both_post (Ψ := fun a t => ∃ s, PAIn' E g a s ∧ XPost E g a.1 a.2.1 s t)
    (both_map (fun a => (a.1, a.2.1)) (fun a s h => ⟨h.base, h.hk, h.seed, h.offW, h.hoff⟩) (pX_ct G v hq))
    fun a s h => WP.mono (pX_ok G v hq h.base h.hk h.seed h.offW h.hoff) fun t X => ⟨s, h, X⟩) ?_
  -- p, and its guard.
  refine RelCT.assoc (RelCT.seq (both_post
    (Ψ := fun a t => ∃ s, PAIn' E g a s ∧ PAFront E g a.1 a.2.1 a.2.2.1 a.2.2.2 s t)
    (both_agree [.esp, .edi] (fun _ => baseVal E) (fun a t h => by obtain ⟨s, _, X⟩ := h; exact base_pins X.base)
      (RelCT.seq (pArith_ct G) (tcheck _ _ (by decide +kernel))))
    fun a t h => by
      obtain ⟨s, hs, X⟩ := h
      exact WP.mono (paMid_ok G v X hs.q hs.q0 hs.usedW hs.p4) fun u F => ⟨s, hs, F⟩) ?_)
  refine both_ite (fun a => decide (pcand g E a.1 a.2.1 a.2.2.1 < 2 ^ (8 * g.pLen - 1)))
    (fun a t h => by obtain ⟨s, _, F⟩ := h; exact F.zf) (RelCT.nil fun _ _ _ => trivial) ?_
  -- The candidate into the test's working space.
  refine RelCT.seq (both_post (Ψ := fun a t => TPre E (8 * g.pLen) (a.2.2.2, pcand g E a.1 a.2.1 a.2.2.1) t)
    (both_agree [.esp, .edi] (fun _ => baseVal E) (fun a t h => by obtain ⟨⟨s, _, F⟩, _⟩ := h; exact base_pins F.base)
      (tcheckE _ _ (copyS 0 0 1) (copyS_erase _ _ _) (by decide +kernel) (by decide +kernel)))
    fun a t h => by
      obtain ⟨⟨s, hs, F⟩, hb⟩ := h
      exact paCopy_ok G v F hs.hu (of_decide_eq_false hb)) ?_
  -- The test.
  refine RelCT.seq (both_post (Ψ := fun a t => ∃ u, TPre E (8 * g.pLen) (a.2.2.2, pcand g E a.1 a.2.1 a.2.2.1) u ∧
      TestPost E (8 * g.pLen) a.2.2.2 (pcand g E a.1 a.2.1 a.2.2.1) u t)
    (both_map (fun a => (a.2.2.2, pcand g E a.1 a.2.1 a.2.2.1)) (fun _ _ h => h) (test_ct G.pv G.pNoSp G.pStack v lay))
    fun a u h => WP.mono (test_ok G.pv G.pNoSp G.pStack v h.1 h.2.1 h.2.2.1 lay (by rw [h.2.2.2.1]; exact h.2.2.2.2.1)
      (by rw [h.2.2.2.1]; exact h.2.2.2.2.2)) fun t P => ⟨u, h, by
        have e := h.2.2.2.1
        simp only at e
        rw [e] at P
        exact P⟩) ?_
  -- Its status.
  have hb : ∀ (a : Nat × Nat × Nat × Nat) t, (∃ u, TPre E (8 * g.pLen) (a.2.2.2, pcand g E a.1 a.2.1 a.2.2.1) u ∧
      TestPost E (8 * g.pLen) a.2.2.2 (pcand g E a.1 a.2.1 a.2.2.1) u t) → Base E t :=
    fun a t h => by obtain ⟨u, _, P⟩ := h; exact P.base
  have hw : ∀ (a : Nat × Nat × Nat × Nat) t, (∃ u, TPre E (8 * g.pLen) (a.2.2.2, pcand g E a.1 a.2.1 a.2.2.1) u ∧
      TestPost E (8 * g.pLen) a.2.2.2 (pcand g E a.1 a.2.1 a.2.2.1) u t) →
      t.mem.readW (off E.base fRes) 32 = BitVec.ofNat 32 (Proof.Dsa.ProbablePrime.status
        (Spec.Dsa.probablePrime (pcand g E a.1 a.2.1 a.2.2.1) (E.witT.drop a.2.2.2))) :=
    fun a t h => by obtain ⟨u, _, P⟩ := h; exact P.res
  refine cmpF_ct (by simp only [fRes, hdr]; omega) (by decide) _ hb hw (fun _ => status_lt _)
    (stImm_ct (fun a t h => h.1.base hb) _ _) ?_
  refine cmpF_ct (Φ := fun a t => CmpAfter _ a t ∧ _) (by simp only [fRes, hdr]; omega) (by decide) _
    (fun a t h => h.1.base hb) (fun a t h => by obtain ⟨⟨u, hu, _, m, _⟩, _⟩ := h; rw [m]; exact hw a u hu)
    (fun _ => status_lt _) (stImm_ct (fun a t h => h.1.base (fun a t h => h.1.base hb)) _ _)
    (RelCT.nil fun _ _ _ => trivial)

end VG.Proof.Dsa.X86.Generation
