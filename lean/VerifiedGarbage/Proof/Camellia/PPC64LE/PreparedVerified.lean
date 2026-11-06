module

public import VerifiedGarbage.Proof.Camellia.PPC64LE.PreparedBody
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Camellia.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Camellia.PPC64LE.PreparedBody
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Camellia.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RegSet

/-!
# Camellia's prepared subkeys and batches on PPC64LE meet their contracts

`crypt_correct`: `vg_camellia_crypt_prepared` against
`Proof.Camellia.Prepared`, with `layout`. (The modes run the preparation
inline, `prepareBody_wp`, rather than call it.) The body runs from the state
narrowed to ECB's scratch buffer (`cryptBody_wp`) and then from the whole
working space (`Exec.widen`), which it changes only where the narrowed run
may. A batch's blocks are ECB in the direction and under the subkeys of any
words whose table its working space holds: the run from it is the run from
the table the precondition gives (`Exec.det`).
-/

@[expose] public section

namespace VG.Proof.Camellia.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Impl.Camellia.PPC64LE
open VG.Proof.Camellia (blockFn)
open VG.Proof.Camellia.Prepared (Holds Keeps)

/-! ## Narrowing the working space -/

/-- `s` with its writable region the first `8 * slots` bytes of `ws`. -/
abbrev narrow (s : State) (ws : Addr) : State := s.withRegions s.rd [⟨ws, 8 * slots⟩]

theorem narrow_covers (s : State) {ws : Addr} {len : Nat} (hw : s.wr = [⟨ws, len⟩]) (hl : 8 * slots ≤ len) :
    Covers ((narrow s ws).rd ++ (narrow s ws).wr) (s.rd ++ s.wr) ∧ Covers (narrow s ws).wr s.wr := by
  have h : Covers [⟨ws, 8 * slots⟩] s.wr := Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨ws, len⟩, by rw [hw]; simp, 0, by rw [BitVec.add_zero], by show 0 + 8 * slots ≤ len; omega⟩
  exact ⟨Covers.append (fun _ _ h => h) h, h⟩

/-- A run from the narrowed state is a run from `s`, to the state with `s`'s regions. -/
theorem exec_widen {c : Prog isa} {s s' : State} {t : List Leak} {ws : Addr} {len : Nat}
    (hw : s.wr = [⟨ws, len⟩]) (hl : 8 * slots ≤ len) (h : Exec isa c (narrow s ws) t s') :
    Exec isa c s t (s'.withRegions s.rd s.wr) := by
  have := Exec.widen h (narrow_covers s hw hl).1 (narrow_covers s hw hl).2
  rwa [State.withRegions_withRegions, State.withRegions_self] at this

theorem size_eq : layout.size = 8 * slots := rfl

/-- The registers the bodies may write. -/
def bodyWrites : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20,
   .r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31]

/-- The callee-saved registers, from those the bodies restore and `r2`. -/
theorem helperAbi_of {c : Prog isa} {s s' : State} {t : List Leak} (he : Exec isa c s t s')
    (hlr : s'.lr = s.lr) (h₁ : ∀ i < 18, s'.gpr (sreg i) = s.gpr (sreg i)) (h₂ : s'.gpr .r2 = s.gpr .r2) :
    abiPreserved s s' := by
  refine ⟨fun r hr => ?_, Exec.sp he, hlr⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact h₂
  · exact h₁ 0 (by omega)
  · exact h₁ 1 (by omega)
  · exact h₁ 2 (by omega)
  · exact h₁ 3 (by omega)
  · exact h₁ 4 (by omega)
  · exact h₁ 5 (by omega)
  · exact h₁ 6 (by omega)
  · exact h₁ 7 (by omega)
  · exact h₁ 8 (by omega)
  · exact h₁ 9 (by omega)
  · exact h₁ 10 (by omega)
  · exact h₁ 11 (by omega)
  · exact h₁ 12 (by omega)
  · exact h₁ 13 (by omega)
  · exact h₁ 14 (by omega)
  · exact h₁ 15 (by omega)
  · exact h₁ 16 (by omega)
  · exact h₁ 17 (by omega)

/-! ## A batch -/

/-- `vg_camellia_crypt_prepared` on PPC64LE. -/
def cryptPPC64LE : Contract PPC64LE.isa where
  pre s :=
    let ws : Region := ⟨s.gpr .r4, (s.gpr .r5).toNat * 8⟩
    s.rd = [] ∧ s.wr = [ws] ∧ (s.gpr .r4).toNat + (s.gpr .r5).toNat * 8 ≤ 2 ^ 64 ∧
      ((s.gpr .r3).toNat = 18 ∨ (s.gpr .r3).toNat = 24) ∧ layout.size ≤ 8 * (s.gpr .r5).toNat ∧
      ∃ w d, Holds layout s.mem (s.gpr .r4) (s.gpr .r3).toNat w d
  post s s' :=
    (∀ w d, Holds layout s.mem (s.gpr .r4) (s.gpr .r3).toNat w d →
      Spec.Camellia.blocksAt s'.mem (s.gpr .r4 + BitVec.ofNat 64 layout.buf) layout.blocks =
        Spec.Camellia.ecb (Spec.Camellia.subkeysOfWords (s.gpr .r3).toNat w) d
          (Spec.Camellia.blocksAt s.mem (s.gpr .r4 + BitVec.ofNat 64 layout.buf) layout.blocks)) ∧
      Keeps (s.gpr .r4) (s.gpr .r5).toNat layout.cryptScratch s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧ s₁.sp = s₂.sp

theorem blocks_of (B : Addr) {m m' : Mem} {k : Spec.Camellia.Subkeys} {d : Spec.Camellia.Direction}
    (h : ∀ j < 8, Spec.Camellia.blockAt m' (B + BitVec.ofNat 64 (8 * tailSlot + 16 * j)) =
        blockFn k d (Spec.Camellia.blockAt m (B + BitVec.ofNat 64 (8 * tailSlot + 16 * j)))) :
    Spec.Camellia.blocksAt m' (B + BitVec.ofNat 64 layout.buf) layout.blocks =
      Spec.Camellia.ecb k d (Spec.Camellia.blocksAt m (B + BitVec.ofNat 64 layout.buf) layout.blocks) := by
  rw [Proof.Camellia.ecb_eq]
  simp only [Spec.Camellia.blocksAt, List.map_map]
  refine List.map_congr_left fun j hj => ?_
  simp only [List.mem_range] at hj
  simp only [Function.comp_apply, VG.Offset.add_add]
  exact h j hj

/-- The masks' bytes, the same in two working spaces holding tables. -/
theorem mask_byte {R : Nat} {m m' : Mem} {B : Addr} {w w' : List (BitVec 64)} {d d' : Dir}
    (h : TableWordsAt R m B w d) (h' : TableWordsAt R m' B w' d') {i : Nat} (hi : 8 * evenSlot ≤ i ∧ i < 8 * (m3Slot + 1)) :
    m' (B + BitVec.ofNat 64 i) = m (B + BitVec.ofNat 64 i) := by
  have hw : (evenSlot ≤ i / 8 ∧ i / 8 ≤ m3Slot) ∨ (keySlot ≤ i / 8 ∧ i / 8 < keySlot + 8 * (8 * (R / 6) + 2)) :=
    .inl (by omega)
  rw [word_byte_addr, byte_of_readW m' (wordAddr B (i / 8)) (j := i % 8) (by omega),
    byte_of_readW m (wordAddr B (i / 8)) (j := i % 8) (by omega), h _ hw, h' _ hw]
  have hm : ∀ (w : List (BitVec 64)) (d : Dir), preparedWord R w d (i / 8) =
      (layerMasks.find? (·.1 = i / 8)).elim 0 (·.2) := fun _ _ => by
    have hc : i / 8 < keySlot := by rw [keySlot_eq]; rw [m3Slot_eq] at hi; omega
    simp only [preparedWord, hc, ↓reduceIte]
  rw [hm, hm]

theorem crypt_correct (s : State) (hs : cryptPPC64LE.pre s) :
    ∃ t s', Exec isa cryptPrepared s t s' ∧ abiPreserved s s' ∧ cryptPPC64LE.post s s' := by
  obtain ⟨-, hwr, fitW, hR, hsz, w₀, d₀, hH⟩ := hs
  rw [size_eq] at hsz
  have hl : 8 * slots ≤ (s.gpr .r5).toNat * 8 := by omega
  have hwN : (⟨(narrow s (s.gpr .r4)).gpr .r4, 8 * slots⟩ : Region) ∈ (narrow s (s.gpr .r4)).wr := by simp
  have fitN : ((narrow s (s.gpr .r4)).gpr .r4).toNat + 8 * slots ≤ 2 ^ 64 := by
    show (s.gpr .r4).toNat + 8 * slots ≤ 2 ^ 64; omega
  have hn : cryptPrepared.noCalls = true := by lit_decide
  obtain ⟨t, s', he, ⟨h₁, hRd, hF, -, -, -, -⟩, h₃⟩ := WP.keep bodyWrites
    (cryptBody_wp hwN fitN hR (readyAt_of_words (words_of_holds hH))) (by lit_decide) hn
  have he' := exec_widen hwr hl he
  refine ⟨t, s'.withRegions s.rd s.wr, he', helperAbi_of he' (Exec.lr he' hn (by lit_decide)) h₁ (h₃.gpr (by decide)),
    fun w d hk => ?_, fun i hi hout => ?_⟩
  · obtain ⟨t₂, s₂, he₂, -, -, -, -, -, -, hB₂⟩ := cryptBody_wp hwN fitN hR (readyAt_of_words (words_of_holds hk))
    obtain ⟨-, rfl⟩ := Exec.det he he₂
    refine blocks_of _ fun j hj => ?_
    have := hB₂ j hj
    rw [specDir_ofSpecDir] at this
    exact this
  · have hfit := fitW
    simp only [layout, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hout
    rw [evenSlot_eq, m3Slot_eq, keySlot_eq, savedSlot_eq, tailSlot_eq] at hout
    by_cases hm : 384 ≤ i ∧ i < 424
    · exact mask_byte (words_of_holds hH) (words_of_readyAt hRd) (by rw [evenSlot_eq, m3Slot_eq]; omega)
    · refine hF _ fun r hr hc => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [Region.Contains, narrow, State.withRegions_gpr] at hc
      · rw [Mem.sub_ofNat_toNat _ (by omega), keySlot_eq] at hc; omega
      · rw [VG.Offset.sub_toNat' _ (by rw [savedSlot_eq]; omega) (by omega), savedSlot_eq] at hc
        split at hc <;> omega

end VG.Proof.Camellia.PPC64LE
