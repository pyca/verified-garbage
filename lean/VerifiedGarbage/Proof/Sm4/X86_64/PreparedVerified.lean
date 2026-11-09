module

public import VerifiedGarbage.Proof.Sm4.X86_64.PreparedBody
public import VerifiedGarbage.Proof.Framework.X86_64.Inline
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Sm4.X86_64.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Proof.Sm4.X86_64.LayersLit
meta import VerifiedGarbage.Proof.Sm4.X86_64.PreparedBody
meta import VerifiedGarbage.Proof.Framework.X86_64.Inline
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Sm4.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintSum
meta import VerifiedGarbage.Proof.Sm4.X86_64.LayersLit
public import VerifiedGarbage.Proof.Sm4.Prepared
meta import VerifiedGarbage.Proof.Sm4.Prepared

/-!
# SM4's batches under prepared round keys on x86-64 meet their contract

`crypt_correct`: `vg_sm4_crypt_prepared` meets `cryptX86_64`, with
`layout`. The body runs from the
state narrowed to ECB's scratch buffer (`cryptBody_wp`) and then from the
whole working space (`Exec.widen`), which it changes only where the
narrowed run may. A batch's blocks are ECB in the direction and under the
round keys of any table encoding that its working space holds: the run from
it is the run from the table the precondition gives (`Exec.det`).
-/

@[expose] public section

namespace VG.Proof.Sm4.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Sm4.X86_64
open VG.Proof.Sm4 (specDir)
open VG.Proof.Sm4.Prepared (Holds Keeps)

theorem size_eq : layout.size = 8 * slots := rfl

/-! ## Narrowing the working space -/

/-- `s` with its writable region the first `8 * slots` bytes of `ws`. -/
abbrev narrow (s : State) (ws : Addr) : State := s.withRegions s.rd [⟨ws, 8 * slots⟩]

theorem narrow_covers (s : State) {ws : Addr} {len : Nat} (hw : s.wr = [⟨ws, len⟩]) (hl : 8 * slots ≤ len) :
    Covers ((narrow s ws).rd ++ (narrow s ws).wr) (s.rd ++ s.wr) ∧ Covers (narrow s ws).wr s.wr := by
  have h : Covers [⟨ws, 8 * slots⟩] s.wr := Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨ws, len⟩, by rw [hw]; simp, 0, by rw [BitVec.add_zero], by show 0 + 8 * slots ≤ len; omega⟩
  exact ⟨Covers.append (Covers.refl _) h, h⟩

/-- A run from the narrowed state is a run from `s`, to the state with `s`'s regions. -/
theorem exec_widen {c : Prog isa} {s s' : State} {t : List Leak} {ws : Addr} {len : Nat}
    (hw : s.wr = [⟨ws, len⟩]) (hl : 8 * slots ≤ len) (h : Exec isa c (narrow s ws) t s') :
    Exec isa c s t (s'.withRegions s.rd s.wr) := by
  have := Exec.widen h (narrow_covers s hw hl).1 (narrow_covers s hw hl).2
  rwa [State.withRegions_withRegions, State.withRegions_self] at this

/-! ## A batch -/

/-- `vg_sm4_crypt_prepared` on x86-64. -/
def cryptX86_64 : Contract X86_64.isa where
  pre s :=
    let ws : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat * 8⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [] ∧ s.wr = [ws] ∧ ret.Disjoint ws ∧ (s.gpr .rdi).toNat + (s.gpr .rsi).toNat * 8 ≤ 2 ^ 64 ∧
      layout.size ≤ 8 * (s.gpr .rsi).toNat ∧ ∃ k d, Holds layout s.mem (s.gpr .rdi) k d
  post s s' :=
    (∀ k d, Holds layout s.mem (s.gpr .rdi) k d →
      Spec.Sm4.blocksAt s'.mem (s.gpr .rdi + BitVec.ofNat 64 layout.buf) layout.blocks =
        Spec.Sm4.ecb k d (Spec.Sm4.blocksAt s.mem (s.gpr .rdi + BitVec.ofNat 64 layout.buf) layout.blocks)) ∧
      Keeps (s.gpr .rdi) (s.gpr .rsi).toNat layout.cryptScratch s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rsp = s₂.gpr .rsp

theorem blocks_of (B : Addr) {m m' : Mem} {k : Spec.Sm4.Schedule} {d : Spec.Sm4.Direction}
    (h : ∀ j < 16, Spec.Sm4.blockAt m' (B + BitVec.ofNat 64 (8 * tailSlot + 16 * j)) =
        Proof.Sm4.blockFn k d (Spec.Sm4.blockAt m (B + BitVec.ofNat 64 (8 * tailSlot + 16 * j)))) :
    Spec.Sm4.blocksAt m' (B + BitVec.ofNat 64 layout.buf) layout.blocks =
      Spec.Sm4.ecb k d (Spec.Sm4.blocksAt m (B + BitVec.ofNat 64 layout.buf) layout.blocks) := by
  rw [Proof.Sm4.ecb_eq]
  simp only [Spec.Sm4.blocksAt, List.map_map]
  refine List.map_congr_left fun j hj => ?_
  simp only [List.mem_range] at hj
  simp only [Function.comp_apply, VG.Offset.add_add]
  exact h j hj

/-- The masks' bytes, the same in two working spaces holding tables. -/
theorem mask_byte {m m' : Mem} {B : Addr} {k k' : Spec.Sm4.Schedule} {d d' : Dir}
    (h : WordsAt m B k d) (h' : WordsAt m' B k' d') {i : Nat} (hi : 8 * evenSlot ≤ i ∧ i < 8 * (grpSlot + 1)) :
    m' (B + BitVec.ofNat 64 i) = m (B + BitVec.ofNat 64 i) := by
  have hw : (evenSlot ≤ i / 8 ∧ i / 8 ≤ grpSlot) ∨ (tableSlot ≤ i / 8 ∧ i / 8 < tableEnd) := .inl (by omega)
  rw [word_byte_addr, byte_of_readW m' (wordAddr B (i / 8)) (j := i % 8) (by omega),
    byte_of_readW m (wordAddr B (i / 8)) (j := i % 8) (by omega), h _ hw, h' _ hw]
  have hm : ∀ (k : Spec.Sm4.Schedule) (d : Dir), preparedWord k d (i / 8) =
      (keyMasks.find? (·.1 = i / 8)).elim 0 (·.2) := fun _ _ => by
    have hc : i / 8 < tableSlot := by rw [tableSlot_eq]; rw [grpSlot_eq] at hi; omega
    simp only [preparedWord, hc, ↓reduceIte]
  rw [hm, hm]

/-- The callee-saved registers, from those the body restores and `rsp`. -/
theorem helperGpr_of {s s' : State} (h₁ : ∀ i < 6, s'.gpr (sreg i) = s.gpr (sreg i))
    (h₂ : s'.gpr .rsp = s.gpr .rsp) (h₃ : s'.mem.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64) :
    gprPreserved s s' := by
  refine ⟨fun r hr => ?_, h₃⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h₁ 0 (by omega)
  · exact h₁ 1 (by omega)
  · exact h₂
  · exact h₁ 2 (by omega)
  · exact h₁ 3 (by omega)
  · exact h₁ 4 (by omega)
  · exact h₁ 5 (by omega)

theorem crypt_correct (s : State) (hs : cryptX86_64.pre s) :
    ∃ t s', Exec isa cryptPrepared s t s' ∧ abiPreserved s s' ∧ cryptX86_64.post s s' := by
  obtain ⟨-, hwr, dRW, fitW, hsz, k₀, d₀, hH⟩ := hs
  rw [size_eq] at hsz
  have hl : 8 * slots ≤ (s.gpr .rsi).toNat * 8 := by omega
  have hwN : (⟨(narrow s (s.gpr .rdi)).gpr .rdi, 8 * slots⟩ : Region) ∈ (narrow s (s.gpr .rdi)).wr := by simp
  have fitN : ((narrow s (s.gpr .rdi)).gpr .rdi).toNat + 8 * slots ≤ 2 ^ 64 := by
    show (s.gpr .rdi).toNat + 8 * slots ≤ 2 ^ 64; omega
  obtain ⟨t, s', he, h₁, hrsp, -, hR, hF, -, -, -⟩ := cryptBody_wp hwN fitN (readyAt_of_words (words_of_holds hH))
  have he' := exec_widen hwr hl he
  have hfit := fitW
  rw [slots_eq] at hl
  have hF' : Frame [⟨s.gpr .rdi, 8 * tableSlot⟩, ⟨wordAddr (s.gpr .rdi) savedSlot, 48⟩] s.mem s'.mem := hF
  refine ⟨t, s'.withRegions s.rd s.wr, he', abiPreserved_of_exec (c := cryptPrepared) (by lit_decide) he'
    (helperGpr_of h₁ hrsp ?_), fun k d hk => ?_, fun i hi hout => ?_⟩
  · refine hF'.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dRW.sub_right (Region.sub_prefix (by rw [tableSlot_eq]; omega))
    · exact dRW.sub_right (VG.Offset.sub_base _ (by rw [savedSlot_eq]; omega))
  · obtain ⟨t₂, s₂, he₂, -, -, -, -, -, -, -, hB₂⟩ :=
      cryptBody_wp hwN fitN (readyAt_of_words (words_of_holds hk))
    obtain ⟨-, rfl⟩ := Exec.det he he₂
    refine blocks_of _ fun j hj => ?_
    have := hB₂ j hj
    rw [specDir_ofSpecDir] at this
    exact this
  · simp only [layout, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hout
    rw [evenSlot_eq, grpSlot_eq, tableSlot_eq, savedSlot_eq, slots_eq] at hout
    by_cases hm : 384 ≤ i ∧ i < 408
    · exact mask_byte (words_of_holds hH) (words_of_readyAt hR) (by rw [evenSlot_eq, grpSlot_eq]; omega)
    · refine hF' _ fun r hr hc => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [Region.Contains, wordAddr] at hc
      · rw [Mem.sub_ofNat_toNat _ (by omega), tableSlot_eq] at hc; omega
      · rw [VG.Offset.sub_toNat' _ (by rw [savedSlot_eq]; omega) (by omega), savedSlot_eq] at hc
        split at hc <;> omega

/-- `cryptX86_64`, and what the body leaves in `sb`: the working space's
address, which the modes, calling it, keep there. -/
def cryptCallX86_64 : Contract X86_64.isa where
  pre := cryptX86_64.pre
  post s s' := cryptX86_64.post s s' ∧ s'.gpr VG.Impl.Aes.X86_64.sb = s.gpr .rdi
  pub := cryptX86_64.pub

theorem cryptCall_correct (s : State) (hs : cryptCallX86_64.pre s) :
    ∃ t s', Exec isa cryptPrepared s t s' ∧ abiPreserved s s' ∧ cryptCallX86_64.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := crypt_correct s hs
  obtain ⟨-, hwr, -, fitW, hsz, k₀, d₀, hH⟩ := hs
  rw [size_eq] at hsz
  have hl : 8 * slots ≤ (s.gpr .rsi).toNat * 8 := by omega
  obtain ⟨t₂, s₂, he₂, -, -, hsb, -⟩ := cryptBody_wp (s₀ := narrow s (s.gpr .rdi)) (by simp)
    (by show (s.gpr .rdi).toNat + 8 * slots ≤ 2 ^ 64; omega) (readyAt_of_words (words_of_holds hH))
  obtain ⟨-, rfl⟩ := Exec.det he (exec_widen hwr hl he₂)
  exact ⟨t, _, he, ha, hp, hsb⟩

end VG.Proof.Sm4.X86_64
