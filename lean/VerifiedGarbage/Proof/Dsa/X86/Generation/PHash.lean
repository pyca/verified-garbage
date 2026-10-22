module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.Q
public import VerifiedGarbage.Proof.Dsa.X86.Generation.AddBE
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.X86.Exec

/-! # One hash of p's candidate

The hash of `seed + offset + j` (A.1.1.2 step 11.1), into its place in `X`:
the `j`-th `qLen` bytes from `X`'s end. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation
open VG.Impl.Mont.X86 (sc)

/-- Where hash `j` goes. -/
def hashAt (g : Geo) (j : Nat) : Nat := sX + g.pLen - (j + 1) * g.qLen

/-- The ranges p's hashes change: the block, the hash's scratch and `X`
with the bytes below it the last hash spills into. -/
def pxRanges (g : Geo) : List (Nat × Nat) := [(sState, sX + g.pLen - sState)]

/-- The digest of `seed + offset + j`. -/
def pDig (g : Geo) (seed : List Byte) (offset j : Nat) : List Byte :=
  Spec.Dsa.seedHash (8 * g.qLen) (Spec.Dsa.encodeBE g.qLen (Spec.Dsa.decodeBE seed + offset + j))

/-- The ranges hash `j` changes. -/
def hRanges (g : Geo) (j : Nat) : List (Nat × Nat) := [(sState, 128), (sHScr, 560), (hashAt g j, g.qLen)]

/-- A change within ranges is one within ranges around them. -/
theorem Env.Chg.widen {E : Env} {os os' : List (Nat × Nat)} {m m' : Mem} (h : E.Chg os m m')
    (hw : ∀ o ∈ os, ∃ o' ∈ os', o'.1 ≤ o.1 ∧ o.1 + o.2 ≤ o'.1 + o'.2) : E.Chg os' m m' :=
  Env.Chg.of_frame h fun r hr => by
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hr
    rcases hr with ⟨o, ho, rfl⟩ | rfl
    · obtain ⟨o', ho', h1, h2⟩ := hw o ho; exact Env.in_range ho' h1 h2
    · exact Env.in_stack (fun _ h => h)

theorem GeoOk.bounds {g : Geo} (G : GeoOk g) :
    20 ≤ g.qLen ∧ g.qLen ≤ 32 ∧ 128 ≤ g.pLen ∧ g.pLen ≤ 384 ∧ (g.count + 1) * g.qLen ≤ g.pLen + 12 := by
  unfold Geo.count
  rcases G.lengths with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h, h'] <;> decide

theorem pxRanges_apart {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) : E.Apart (pxRanges g) := by
  have sz := v.size_ge
  have b := G.bounds
  intro o ho
  simp only [pxRanges, List.mem_singleton] at ho; subst ho
  simp only [sState, sX, fOut, fWitLen, hdr]; omega

theorem hRanges_apart {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) {j : Nat} (hj : j ≤ g.count) :
    E.Apart (hRanges g j) := by
  have sz := v.size_ge
  have b := G.bounds
  have hjq : (j + 1) * g.qLen ≤ (g.count + 1) * g.qLen := Nat.mul_le_mul_right _ (by omega)
  intro o ho
  simp only [hRanges, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl <;> simp only [hashAt, sState, sHScr, sX, fOut, fWitLen, hdr] <;> omega

theorem pHash_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hq : E.qLen = g.qLen)
    {s : State} (B : Base E s) {k : Nat} (hk : (k + 1) * E.qLen ≤ E.seedsLen)
    (hS : s.mem.readW (off E.base fSeed) 32 = (E.seeds + BitVec.ofNat 64 (k * E.qLen)).setWidth 32)
    {offset j : Nat} (hO : s.mem.readW (off E.base fOffset) 32 = BitVec.ofNat 32 offset)
    (hoj : offset + j + 256 ≤ 2 ^ 32) (hj : j ≤ g.count) :
    WP isa (g.pHash j) s fun t => Base E t ∧
      Spec.Rsa.bytesAt t.mem (off E.base (hashAt g j)) g.qLen = pDig g (chunk E k) offset j ∧
      E.Chg (hRanges g j) s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.syms = s.syms := by
  have sz := v.size_ge
  have nl := G.hash.N_le
  have bd := G.bounds
  have hN := G.N
  have hjq : (j + 1) * g.qLen ≤ (g.count + 1) * g.qLen := Nat.mul_le_mul_right _ (by omega)
  have Ap := hRanges_apart G v hj
  unfold Geo.pHash
  simp only [seqs]
  refine WP.seq (VG.X86.WP.mono_syms (seedIn_ok G v hq B hk hS) fun t₁ ⟨S₁, F₁, K₁⟩ sy₁ => ?_)
  have C₁ : E.Chg (hRanges g j) s.mem t₁.mem := Env.Chg.of_frame F₁ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Env.in_range (o := (sState, 128)) (by simp [hRanges]) (by omega) (by simp only [sState]; omega)
  have B₁ : Base E t₁ := B.keep v C₁ Ap (K₁.1 _ (by decide)) (K₁.1 _ (by decide)) K₁.2.1 K₁.2.2 sy₁
  have hO₁ : t₁.mem.readW (off E.base fOffset) 32 = BitVec.ofNat 32 offset := by
    rw [Env.Chg.word v C₁ (by simp only [fOffset, hdr]; omega) (fun o ho => ⟨(Ap o ho).1, by
      simp only [hRanges, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl <;> simp only [hashAt, sState, sHScr, sX, fOffset, hdr] <;> omega⟩), hO]
  refine WP.seq (scr_ok fun t₂ e₂ g₂ m₂ rd₂ wr₂ sy₂ =>
    ld_ok (Scr.of_eq B₁.scr (g₂ _ (by decide)) (g₂ _ (by decide)) wr₂) (d := fOffset)
      (by simp only [fOffset, hdr]; omega) fun t₃ u₃ => wp_addi fun t₄ u₄ => WP.block_nil ?_)
  have edi₄ : t₄.gpr .edi = t₁.gpr .edi := by rw [u₄.other _ (by decide), u₃.other _ (by decide), g₂ _ (by decide)]
  have esp₄ : t₄.gpr .esp = t₁.gpr .esp := by rw [u₄.other _ (by decide), u₃.other _ (by decide), g₂ _ (by decide)]
  have m₄ : t₄.mem = t₁.mem := by rw [u₄.mem, u₃.mem, m₂]
  have hs₄ : Scr t₄ E.base E.size := Scr.of_eq B₁.scr edi₄ esp₄ (by rw [u₄.wr, u₃.wr, wr₂])
  have edx₄ : t₄.gpr .edx = t₄.gpr .edi + BitVec.ofNat 32 (sState + g.H.N + g.qLen - 1) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), e₂, edi₄]
  have ecx₄ : t₄.gpr .ecx = BitVec.ofNat 32 (offset + j) := by
    rw [u₄.gpr, u₃.gpr, m₂, hO₁, BitVec.ofNat_add]
  refine WP.seq (VG.X86.WP.mono_syms (addBE_ok hs₄ (o := sState + g.H.N) (n := g.qLen) (c := offset + j)
    (by omega) (by simp only [sState]; omega) hoj (by rw [edx₄]) ecx₄) fun t₅ ⟨S₅, F₅, K₅, _⟩ sy₅ => ?_)
  rw [m₄, S₁] at S₅
  have C₅ : E.Chg (hRanges g j) s.mem t₅.mem := C₁.trans (Env.Chg.of_frame (m₄ ▸ F₅) fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Env.in_range (o := (sState, 128)) (by simp [hRanges]) (by omega) (by simp only [sState]; omega))
  have rd₅ : t₅.rd = s.rd := by rw [K₅.2.1, u₄.rd, u₃.rd, rd₂, K₁.2.1]
  have wr₅ : t₅.wr = s.wr := by rw [K₅.2.2, u₄.wr, u₃.wr, wr₂, K₁.2.2]
  have sy₅s : t₅.syms = s.syms := by rw [sy₅, u₄.syms, u₃.syms, sy₂, sy₁]
  have edi₅ : t₅.gpr .edi = s.gpr .edi := by rw [K₅.1 _ (by decide), edi₄, K₁.1 _ (by decide)]
  have esp₅ : t₅.gpr .esp = s.gpr .esp := by rw [K₅.1 _ (by decide), esp₄, K₁.1 _ (by decide)]
  have B₅ : Base E t₅ := B.keep v C₅ Ap edi₅ esp₅ rd₅ wr₅ sy₅s
  have sp₅ : t₅.gpr .esp = E.sp := B₅.sp
  have low := v.low
  have stk₅ : Region.Sub (VG.Proof.Pbkdf2.Stream.X86.stk t₅) E.stackRegion := by
    simp only [VG.Proof.Pbkdf2.Stream.X86.stk, sp₅, Env.stackRegion]; exact below_sub (by decide) (by omega)
  have so := G.hash.ok.sizes.so
  have sW := G.hash.ok.sizes.W
  have hd : sX + g.pLen - (j + 1) * g.qLen = hashAt g j := rfl
  rw [hd, ← hN]
  refine VG.X86.WP.mono_syms (hash_ok G.hash B₅.scr (dst := hashAt g j)
    (by simp only [sHScr]; omega) (by simp only [sHScr]; omega) (by simp only [hashAt, sX]; omega)
    (by simp only [hashAt, sState, sX]; omega) (by simp only [hashAt, sHScr, sX]; omega) (by rw [sp₅]; omega)
    (v.scratchStack.symm.sub_left stk₅)) fun t₆ ⟨H₆, F₆, G₆, rd₆, wr₆⟩ sy₆ => ?_
  have bsEq : ∀ m p n, Spec.Sha256.bytesAt m p n = Spec.Rsa.bytesAt m p n := fun _ _ _ => rfl
  simp only [bsEq] at H₆
  rw [← hN] at S₅
  rw [S₅, G.seedHash] at H₆
  have C₆ : E.Chg (hRanges g j) s.mem t₆.mem := C₅.trans (Env.Chg.of_frame F₆ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Env.in_range (o := (sState, 128)) (by simp [hRanges]) (by omega) (by omega)
    · exact Env.in_range (o := (sHScr, 560)) (by simp [hRanges]) (by omega) (by omega)
    · exact Env.in_range (o := (hashAt g j, g.qLen)) (by simp [hRanges]) (by omega) (by omega)
    · exact Env.in_stack stk₅)
  have edi₆ : t₆.gpr .edi = s.gpr .edi := by
    rw [G₆ _ (by decide) (by decide) (by decide) (by decide) (by decide), edi₅]
  have esp₆ : t₆.gpr .esp = s.gpr .esp := by
    rw [G₆ _ (by decide) (by decide) (by decide) (by decide) (by decide), esp₅]
  refine ⟨B.keep v C₆ Ap edi₆ esp₆ (by rw [rd₆, rd₅]) (by rw [wr₆, wr₅]) (by rw [sy₆, sy₅s]), ?_, C₆,
    by rw [rd₆, rd₅], by rw [wr₆, wr₅], by rw [sy₆, sy₅s]⟩
  rw [hN] at H₆ ⊢
  rw [H₆, pDig, Nat.add_assoc]

end VG.Proof.Dsa.X86.Generation
