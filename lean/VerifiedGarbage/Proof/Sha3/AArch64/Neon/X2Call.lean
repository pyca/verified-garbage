module

public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit

/-! # Calling Keccak-f[1600] on two interleaved states -/

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Neon.X2

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Neon.X2
open VG.Spec.Sha3 (keccakF)

/-- The call's working space: the function's, and the return address. -/
def callR (q : Addr) : Region := ⟨q, 136⟩

/-- The registers the calling convention does not preserve. -/
def volatile : List Reg :=
  [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17]

theorem volatile_or : ∀ r : Reg, r ∉ volatile → r = .x30 ∨ (r ∈ preserved ∧ r ≠ .x30 ∧ r ∉ linkRegs) := by
  intro r h; cases r <;> revert h <;> decide

theorem noFrames : ∀ sha3, (code sha3).noFrames = true := by
  intro sha3; cases sha3 <;> lit_decide

theorem callAny_ok (sha3 : Bool) {s : State} {rp rb : Reg} {off : Nat} {p q : Addr} {A B : Spec.Sha3.State}
    (hoff : off < 8190) (h8 : off % 8 = 0) (hrp : rp ≠ .x1) (hrb : rb ∉ volatile) (hrb30 : rb ≠ .x30)
    (hp : s.gpr rp = p) (hq : s.gpr rb + BitVec.ofNat 64 off = q) (hd : (pairR p).Disjoint (callR q))
    (hP : PairAt s.mem p A B) (hc : Covers [pairR p, callR q] s.wr) :
    WP isa (Impl.Sha3.AArch64.Neon.X2.call sha3 rp rb off) s fun t => RegKeep volatile s t ∧
      (∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) ∧
      Frame [pairR p, callR q] s.mem t.mem ∧ PairAt t.mem p (keccakF A) (keccakF B) := by
  have hrb1 : rb ≠ .x1 ∧ rb ≠ .x0 := ⟨fun e => hrb (by rw [e]; decide), fun e => hrb (by rw [e]; decide)⟩
  have sub : Covers [pairR p, scrR q] [pairR p, callR q] := by
    intro a n ⟨R, hR, hcn⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact ⟨_, List.mem_cons_self, hcn⟩
    · exact ⟨callR q, by simp, by
        simp only [Region.Contains, scrR, callR] at hcn ⊢; omega⟩
  have slot : InRegions s.wr (q + BitVec.ofNat 64 128) 8 :=
    hc _ _ ⟨callR q, by simp, Offset.contains_base _ (by decide) (by decide)⟩
  have dps : (pairR p).Disjoint (scrR q) := fun a h1 h2 => hd a h1 (Region.sub_prefix (by decide) a h2)
  have dslot : ∀ r ∈ [pairR p, scrR q], (Region.mk (q + BitVec.ofNat 64 128) 8).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact fun a h1 h2 => hd a h2 (Offset.sub_base (k := 136) _ (by decide) a h1)
    · exact Offset.disjoint_base _ (by decide) (by decide)
  unfold Impl.Sha3.AArch64.Neon.X2.call
  refine WP.seq (wp_addImm (by omega) fun t₁ d₁ => wp_addImm (by omega) fun t₂ d₂ => ?_)
  have x1 : t₂.gpr .x1 = q := by
    rw [d₂.gpr, d₁.gpr, BitVec.add_assoc, ← BitVec.ofNat_add, show off / 2 + (off - off / 2) = off by omega, hq]
  refine wp_str (a := q + BitVec.ofNat 64 128) ⟨by decide, by decide⟩ (by rw [x1]) (by rw [d₂.wr, d₁.wr]; exact slot)
    fun t₃ d₃ => wp_addImm (by decide) fun t₄ d₄ => wp_nil ?_
  have g₄ : ∀ r, r ≠ .x0 → r ≠ .x1 → t₄.gpr r = s.gpr r := fun r h0 h1 => by
    rw [d₄.other r h0, d₃.gpr, d₂.other r h1, d₁.other r h1]
  have x0 : t₄.gpr .x0 = p := by
    rw [d₄.gpr, d₃.gpr, d₂.other rp hrp, d₁.other rp hrp, hp]; simp
  have x1' : t₄.gpr .x1 = q := by rw [d₄.other _ (by decide), d₃.gpr, x1]
  have m₄ : t₄.mem = s.mem.writeW (q + BitVec.ofNat 64 128) (s.gpr .x30) := by
    rw [d₄.mem, d₃.mem, d₂.mem, d₁.mem, d₂.other _ (by decide), d₁.other _ (by decide)]
  have wr₄ : t₄.wr = s.wr := by rw [d₄.wr, d₃.wr, d₂.wr, d₁.wr]
  have rd₄ : t₄.rd = s.rd := by rw [d₄.rd, d₃.rd, d₂.rd, d₁.rd]
  have sp₄ : t₄.sp = s.sp := by rw [d₄.sp, d₃.sp, d₂.sp, d₁.sp]
  have v₄ : t₄.v = s.v := by rw [d₄.vec, d₃.vec, d₂.vec, d₁.vec]
  have f₄ : Frame [callR q] s.mem t₄.mem := by
    rw [m₄]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  have P₄ : PairAt t₄.mem p A B := fun i hi => by
    rw [f₄.read (pair_contains p hi) (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hd) (by decide)]
    exact hP i hi
  have hcov : Covers [pairR p, scrR q] t₄.wr := by rw [wr₄]; exact sub.trans hc
  have hcr : Covers ([] ++ [pairR p, scrR q]) (t₄.rd ++ t₄.wr) := by
    intro a n h
    obtain ⟨R, hR, hh⟩ := hcov a n h
    exact ⟨R, List.mem_append_right _ hR, hh⟩
  have e0 : t₄.callEntry.gpr .x0 = p := by rw [State.callEntry_gpr _ (by decide), x0]
  have e1 : t₄.callEntry.gpr .x1 = q := by rw [State.callEntry_gpr _ (by decide), x1']
  refine WP.seq (WP.callV (k := x2K) (code_ok sha3) (rd := []) (wr := [pairR p, scrR q])
    ⟨rfl, by simp only [State.withRegions_wr, State.withRegions_gpr, e0, e1], by
      simp only [State.withRegions_gpr, e0, e1]; exact dps⟩
    hcr hcov (fun t₅ rd₅ wr₅ sp₅ f₅ g₅ _ v₅ post => ?_) (noFrames sha3))
  simp only [x2K, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, e0] at post
  have hA := stateX2_of_pairAt P₄
  rw [hA.1, hA.2] at post
  have hval : t₅.mem.readW (q + BitVec.ofNat 64 128) 64 = s.gpr .x30 := by
    rw [f₅.readW (r := ⟨q + BitVec.ofNat 64 128, 8⟩) (Region.contains_self _ _) dslot (by decide), m₄,
      Mem.readW_writeW_self64]
  have rb' : t₅.gpr rb = s.gpr rb := by
    rcases volatile_or rb hrb with h | h
    · exact absurd h hrb30
    · rw [g₅ rb h.1 h.2.1, g₄ rb hrb1.2 hrb1.1]
  refine wp_ldr (a := q + BitVec.ofNat 64 128) ⟨by omega, by omega⟩
    (by rw [rb', BitVec.ofNat_add, ← BitVec.add_assoc, hq])
    (by rw [rd₅, wr₅, rd₄, wr₄]; exact (let ⟨R, hR, hh⟩ := slot; ⟨R, List.mem_append_right _ hR, hh⟩)) fun t₆ d₆ => wp_nil
      ⟨⟨fun r hr => ?_, ?_, ?_, ?_⟩, fun r hr => ?_, ?_, ?_⟩
  · by_cases h30 : r = .x30
    · subst h30; rw [d₆.gpr, hval]
    · rcases volatile_or r hr with h | h
      · exact absurd h h30
      · rw [d₆.other r h30, g₅ r h.1 h.2.1, g₄ r (fun e => hr (by rw [e]; decide)) (fun e => hr (by rw [e]; decide))]
  · rw [d₆.rd, rd₅, rd₄]
  · rw [d₆.wr, wr₅, wr₄]
  · rw [d₆.sp, sp₅, sp₄]
  · rw [d₆.vec, v₅ r hr, v₄]
  · rw [d₆.mem]
    refine (f₄.sub fun r hr => ?_).trans (f₅.sub fun r hr => ?_)
    · rw [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨callR q, by simp, Region.sub_prefix (by decide)⟩
  · rw [d₆.mem, ← post.1, ← post.2]
    exact pairAt_stateX2 _ _

end VG.Proof.Sha3.AArch64.Neon.X2
