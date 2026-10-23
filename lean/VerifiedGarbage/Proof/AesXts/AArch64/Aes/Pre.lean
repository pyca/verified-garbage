module

public import VerifiedGarbage.Impl.AesXts.AArch64Aes
public import VerifiedGarbage.Proof.AesXts.AArch64.Aes.Word
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.AesXts.AArch64.Steps
import VerifiedGarbage.Proof.AesCbc.AArch64.Block
import VerifiedGarbage.Proof.Aes.AArch64.Aese.Ctr32
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# One-pass XTS-AES on AArch64: the tweaks XORed in

`mulA_run`: `AArch64Aes.mulA` multiplies the tweak in `x14` (low) and `x15`
(high) by `α` (`mulA128` of `x15 ++ x14`), through `x9` and `x10`.
`pre1_run`: one block loaded, XORed with the tweak, the tweak saved to the
scratch buffer, and the tweak multiplied by `α`. `pre_ok`: `pre rs j` does
that for each register of `rs`, with the tweaks `twW t k` from the tweak `t`
in `x14` and `x15`.
-/

@[expose] public section

namespace VG.Proof.AesXts.AArch64.Aes

open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Impl.AesXts.AArch64Aes (mulA pre1 pre post1 post preL1 preL genStep gen)
open VG.Proof.AesXts (mulA128)
open VG.Proof.Aes.AArch64.Aese (exec_ldrq exec_strq setV_v_self setV_v_of_ne)

/-- The tweak in `x14` (low) and `x15` (high). -/
abbrev tweakOf (s : State) : BitVec 128 := s.gpr .x15 ++ s.gpr .x14

theorem write16 (m : Mem) (a : Addr) (v : BitVec 128) : m.write a 16 v = m.writeW a v := by
  simp [Mem.writeW]

theorem mulA_run (s : State) :
    ∃ s', runBlock isa mulA s = some s' ∧ tweakOf s' = mulA128 (tweakOf s) ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x14 → r ≠ .x15 → s'.gpr r = s.gpr r) ∧
      s'.v = s.v ∧ s'.mem = s.mem ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [mulA, gpr_addWithCarry, c_addWithCarry, c_write, mem_addWithCarry, rd_addWithCarry,
    wr_addWithCarry, sp_addWithCarry], ?_⟩
  refine ⟨?_, fun r h₁ h₂ h₃ h₄ => by simp [gpr_write, gpr_addWithCarry, h₁, h₂, h₃, h₄], rfl, rfl, rfl, rfl, rfl⟩
  rw [tweakOf, tweakOf, mulA128_append]
  simp only [gpr_write, gpr_addWithCarry, reduceCtorEq, ↓reduceIte, BitVec.setWidth_eq, Size.bits]
  simp only [mulHi, mulLo, AesXts.AArch64.carry_c, AesXts.AArch64.add_bit, AesXts.AArch64.sel_87,
    Bool.false_eq_true, ↓reduceIte, AesXts.AArch64.or_zero']

theorem pre1_run (b : VReg) (j : Nat) (s : State) (hb : b ≠ .v31) (hj : j < 8)
    (hld : InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 (16 * j)) 16)
    (hst : InRegions s.wr (s.gpr .x5 + BitVec.ofNat 64 (16 * j)) 16) :
    ∃ s', runBlock isa (pre1 b j) s = some s' ∧
      s'.v b = s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 (16 * j)) 128 ^^^ tweakOf s ∧
      (∀ r, r ≠ b → r ≠ .v31 → s'.v r = s.v r) ∧
      s'.mem = s.mem.writeW (s.gpr .x5 + BitVec.ofNat 64 (16 * j)) (tweakOf s) ∧
      tweakOf s' = mulA128 (tweakOf s) ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x14 → r ≠ .x15 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let s₁ := s.setV b (s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 (16 * j)) 128)
  let s₂ := s₁.setV .v31 (ofVDwords (s.gpr .x14) (s.gpr .x14))
  let s₃ := s₂.setV .v31 (setLane (ofVDwords (s.gpr .x14) (s.gpr .x14)) 64 1 (s.gpr .x15))
  let s₄ : State := { s₃ with mem := s.mem.write (s.gpr .x5 + BitVec.ofNat 64 (16 * j)) 16 (tweakOf s) }
  let s₅ := s₄.setV b (s₄.v b ^^^ s₄.v .v31)
  have e₃ : s₃.v .v31 = tweakOf s := by simp [s₃, setV_v_self, setLane_dup]
  have x₁ : exec (.ldrq b .x2 (16 * j)) s = some s₁ := exec_ldrq ⟨by omega, by omega⟩ hld
  have x₂ : exec (.vop (.dup .d2 .v31 .x14)) s₁ = some s₂ := rfl
  have x₃ : exec (.vop (.ins .d2 .v31 1 .x15)) s₂ = some s₃ := by
    simp only [exec, VOp.eval, s₂, setV_v_self]; rfl
  have x₄ : exec (.strq .v31 .x5 (16 * j)) s₃ = some s₄ := by
    rw [exec_strq ⟨by omega, by omega⟩ (by simpa [s₃, s₂, s₁, State.setV] using hst), e₃]; rfl
  have x₅ : exec (.vop (.logic .eor b b .v31)) s₄ = some s₅ := rfl
  have h1 : runBlock isa (pre1 b j) s = runBlock isa mulA s₅ := by
    simp only [pre1, List.cons_append, List.nil_append, runBlock_cons]
    simp only [isa, x₁, runStep_some, runBlock_cons, x₂, x₃, x₄, x₅]
  obtain ⟨s', hr, ht, hg, hv, hm, hsp, hrd, hwr⟩ := mulA_run s₅
  have tw₅ : tweakOf s₅ = tweakOf s := rfl
  refine ⟨s', h1 ▸ hr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hv]; simp only [s₅, setV_v_self]
    rw [e₃]; simp [s₄, s₃, s₂, s₁, State.setV, hb]
  · intro r h₁ h₂; rw [hv]; simp [s₅, s₄, s₃, s₂, s₁, State.setV, h₁, h₂]
  · rw [hm, ← write16]; rfl
  · rw [ht, tw₅]
  · intro r h₁ h₂ h₃ h₄; rw [hg r h₁ h₂ h₃ h₄]; rfl
  · rw [hsp]; rfl
  · rw [hrd]; rfl
  · rw [hwr]; rfl

theorem twW_mulA (t : BitVec 128) : ∀ k, twW (mulA128 t) k = twW t (k + 1)
  | 0 => rfl
  | k + 1 => by rw [twW_succ, twW_mulA t k, ← twW_succ]

/-- `pre rs j`, from the data blocks `D + 16 (j + k)` and with the tweaks
saved at `S + 16 (j + k)`. -/
theorem pre_ok (D S : Addr) (hS : S.toNat + 128 ≤ 2 ^ 64) :
    ∀ (rs : List VReg) (j : Nat) (s : State), rs.Nodup → .v31 ∉ rs → j + rs.length ≤ 8 →
    s.gpr .x2 = D → s.gpr .x5 = S →
    (∀ k < rs.length, InRegions (s.rd ++ s.wr) (D + BitVec.ofNat 64 (16 * (j + k))) 16) →
    (∀ k < rs.length, InRegions s.wr (S + BitVec.ofNat 64 (16 * (j + k))) 16) →
    (∀ k < rs.length, Region.Disjoint ⟨D + BitVec.ofNat 64 (16 * (j + k)), 16⟩ ⟨S, 128⟩) →
    WP isa (.block (pre rs j)) s fun s' =>
      (∀ k (h : k < rs.length), s'.v rs[k] =
        s.mem.readW (D + BitVec.ofNat 64 (16 * (j + k))) 128 ^^^ twW (tweakOf s) k) ∧
      (∀ k < rs.length, s'.mem.readW (S + BitVec.ofNat 64 (16 * (j + k))) 128 = twW (tweakOf s) k) ∧
      Frame [⟨S + BitVec.ofNat 64 (16 * j), 16 * rs.length⟩] s.mem s'.mem ∧
      tweakOf s' = twW (tweakOf s) rs.length ∧
      (∀ r, r ∉ rs → r ≠ .v31 → s'.v r = s.v r) ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x14 → r ≠ .x15 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr
  | [], _, s, _, _, _, _, _, _, _, _ =>
    WP.block_nil ⟨fun _ h => absurd h (by simp), fun _ h => absurd h (by simp), Frame.refl _ _, rfl,
      fun _ _ _ => rfl, fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
  | b :: bs, j, s, hnd, h31, hj, hx2, hx5, hld, hst, hds => by
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    have hb31 : b ≠ .v31 := fun h => h31 (h ▸ List.mem_cons_self ..)
    simp only [List.length_cons] at hj
    have e0 : ∀ (p : Addr) (k : Nat), p + BitVec.ofNat 64 (16 * (j + 1 + k)) = p + BitVec.ofNat 64 (16 * (j + (k + 1))) :=
      fun p k => by rw [show j + 1 + k = j + (k + 1) by omega]
    obtain ⟨s₁, r₁, v₁, o₁, m₁, t₁, g₁, sp₁, rd₁, wr₁⟩ := pre1_run b j s hb31 (by omega)
      (by rw [hx2]; simpa using hld 0 (by simp)) (by rw [hx5]; simpa using hst 0 (by simp))
    rw [Impl.AesXts.AArch64Aes.pre, WP.block_append_iff]
    refine WP.of_runBlock ⟨s₁, r₁, ?_⟩
    have f₁ : Frame [⟨S + BitVec.ofNat 64 (16 * j), 16⟩] s.mem s₁.mem := by
      rw [m₁, hx5]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    refine WP.mono (pre_ok D S hS bs (j + 1) s₁ (List.nodup_cons.mp hnd).2 (fun h => h31 (List.mem_cons_of_mem _ h))
      (by omega) (by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), hx2])
      (by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), hx5])
      (fun k hk => by rw [rd₁, wr₁, e0]; exact hld (k + 1) (by simp; omega))
      (fun k hk => by rw [wr₁, e0]; exact hst (k + 1) (by simp; omega))
      (fun k hk => by rw [e0]; exact hds (k + 1) (by simp; omega)))
      fun s' ⟨v', m', f', t', o', g', sp', rd', wr'⟩ => ?_
    simp only [t₁, twW_mulA] at v' m' t'
    have hsl : ∀ k, k < 8 → Region.Sub ⟨S + BitVec.ofNat 64 (16 * k), 16⟩ ⟨S, 128⟩ :=
      fun k hk => Offset.sub_base S (by omega)
    have hdj : ∀ k < bs.length + 1, Region.Disjoint ⟨D + BitVec.ofNat 64 (16 * (j + k)), 16⟩
        ⟨S + BitVec.ofNat 64 (16 * j), 16⟩ :=
      fun k hk => (hds k (by simpa using hk)).sub_right (hsl j (by omega))
    refine ⟨fun k hk => ?_, fun k hk => ?_, ?_, ?_, fun r hr h => ?_, fun r h₁ h₂ h₃ h₄ => ?_,
      sp'.trans sp₁, rd'.trans rd₁, wr'.trans wr₁⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [o' _ hbs hb31, v₁, hx2]; rfl
      | succ k =>
        simp only [List.getElem_cons_succ]
        rw [v' k (by simpa using hk), e0,
          f₁.readW (r := ⟨D + BitVec.ofNat 64 (16 * (j + (k + 1))), 16⟩) (Region.contains_self _ _) (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact hdj (k + 1) (by simpa using hk)) (by decide)]
    · cases k with
      | zero =>
        rw [Nat.add_zero, f'.readW (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint S (by omega) (by omega) (by omega)) (by decide), m₁, hx5]
        exact Mem.readW_writeW_self _ _ 16 _ (by decide)
      | succ k =>
        rw [← e0]; exact m' k (by simpa using hk)
    · refine (f₁.sub fun r hr => ?_).trans (f'.sub fun r hr => ?_) <;>
        simp only [List.mem_singleton] at hr <;> subst hr <;> refine ⟨_, List.mem_singleton_self _, ?_⟩
      · exact Region.sub_prefix (by simp; omega)
      · exact Offset.sub S (by omega) (by simp; omega)
    · rw [t', List.length_cons, Nat.add_comm]
    · simp only [List.mem_cons, not_or] at hr
      rw [o' r hr.2 h, o₁ r hr.1 h]
    · rw [g' r h₁ h₂ h₃ h₄, g₁ r h₁ h₂ h₃ h₄]

/-- `post t rs j`: each register of `rs` XORed with the tweak saved at
`S + 16 (j + k)` (`t` holding `S`) and stored to the data block `D + 16 (j + k)`. -/
theorem post_ok (t : Reg) (D S : Addr) (hS : S.toNat + 128 ≤ 2 ^ 64) :
    ∀ (rs : List VReg) (j : Nat) (s : State), rs.Nodup → .v31 ∉ rs → j + rs.length ≤ 8 →
    D.toNat + 16 * (j + rs.length) ≤ 2 ^ 64 →
    s.gpr .x2 = D → s.gpr t = S →
    (∀ k < rs.length, InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 (16 * (j + k))) 16) →
    (∀ k < rs.length, InRegions s.wr (D + BitVec.ofNat 64 (16 * (j + k))) 16) →
    (∀ k < rs.length, Region.Disjoint ⟨D + BitVec.ofNat 64 (16 * (j + k)), 16⟩ ⟨S, 128⟩) →
    WP isa (.block (post t rs j)) s fun s' =>
      (∀ k (h : k < rs.length), s'.mem.readW (D + BitVec.ofNat 64 (16 * (j + k))) 128 =
        s.v rs[k] ^^^ s.mem.readW (S + BitVec.ofNat 64 (16 * (j + k))) 128) ∧
      Frame [⟨D + BitVec.ofNat 64 (16 * j), 16 * rs.length⟩] s.mem s'.mem ∧
      (∀ r, r ∉ rs → r ≠ .v31 → s'.v r = s.v r) ∧
      s'.gpr = s.gpr ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr
  | [], _, s, _, _, _, _, _, _, _, _, _ =>
    WP.block_nil ⟨fun _ h => absurd h (by simp), Frame.refl _ _, fun _ _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | b :: bs, j, s, hnd, h31, hj, hD, hx2, hx5, hld, hst, hds => by
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    have hb31 : b ≠ .v31 := fun h => h31 (h ▸ List.mem_cons_self ..)
    simp only [List.length_cons] at hj hD
    have e0 : ∀ (p : Addr) (k : Nat), p + BitVec.ofNat 64 (16 * (j + 1 + k)) = p + BitVec.ofNat 64 (16 * (j + (k + 1))) :=
      fun p k => by rw [show j + 1 + k = j + (k + 1) by omega]
    let T := s.mem.readW (S + BitVec.ofNat 64 (16 * j)) 128
    let s₁ := s.setV .v31 T
    let s₂ := s₁.setV b (s₁.v b ^^^ s₁.v .v31)
    let s₃ : State := { s₂ with mem := s.mem.write (D + BitVec.ofNat 64 (16 * j)) 16 (s.v b ^^^ T) }
    have x₁ : exec (.ldrq .v31 t (16 * j)) s = some s₁ := by
      rw [exec_ldrq ⟨by omega, by omega⟩ (by rw [hx5]; simpa using hld 0 (by simp)), hx5]
    have x₂ : exec (.vop (.logic .eor b b .v31)) s₁ = some s₂ := rfl
    have v₂ : s₂.v b = s.v b ^^^ T := by
      simp [s₂, s₁, State.setV, hb31]
    have x₃ : exec (.strq b .x2 (16 * j)) s₂ = some s₃ := by
      rw [exec_strq ⟨by omega, by omega⟩ (by simpa [s₂, s₁, State.setV, hx2] using hst 0 (by simp)), v₂]
      simp only [s₂, s₁, State.setV, hx2]; rfl
    rw [Impl.AesXts.AArch64Aes.post, Impl.AesXts.AArch64Aes.post1, WP.block_append_iff]
    refine WP.of_runBlock ⟨s₃, by simp only [runBlock_cons, isa, x₁, runStep_some,
      x₂, x₃, runBlock_nil], ?_⟩
    have hsl : ∀ k, k < 8 → Region.Sub ⟨S + BitVec.ofNat 64 (16 * k), 16⟩ ⟨S, 128⟩ :=
      fun k hk => Offset.sub_base S (by omega)
    have f₃ : Frame [⟨D + BitVec.ofNat 64 (16 * j), 16⟩] s.mem s₃.mem := by
      rw [show s₃.mem = s.mem.writeW (D + BitVec.ofNat 64 (16 * j)) (s.v b ^^^ T) from (write16 _ _ _)]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    have hT : ∀ k, k < bs.length + 1 → s₃.mem.readW (S + BitVec.ofNat 64 (16 * (j + k))) 128 =
        s.mem.readW (S + BitVec.ofNat 64 (16 * (j + k))) 128 := fun k hk =>
      f₃.readW (r := ⟨S + BitVec.ofNat 64 (16 * (j + k)), 16⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ((hds 0 (by simp)).sub_right (hsl (j + k) (by omega))).symm) (by decide)
    refine WP.mono (post_ok t D S hS bs (j + 1) s₃ (List.nodup_cons.mp hnd).2 (fun h => h31 (List.mem_cons_of_mem _ h))
      (by omega) (by omega) (by simpa [s₃, s₂, s₁, State.setV] using hx2)
      (by simpa [s₃, s₂, s₁, State.setV] using hx5)
      (fun k hk => by rw [e0]; simpa [s₃, s₂, s₁, State.setV] using hld (k + 1) (by simp; omega))
      (fun k hk => by rw [e0]; simpa [s₃, s₂, s₁, State.setV] using hst (k + 1) (by simp; omega))
      (fun k hk => by rw [e0]; exact hds (k + 1) (by simp; omega)))
      fun s' ⟨d', f', o', g', sp', rd', wr'⟩ => ?_
    refine ⟨fun k hk => ?_, ?_, fun r hr h => ?_, ?_, ?_, ?_, ?_⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [f'.readW (r := ⟨D + BitVec.ofNat 64 (16 * j), 16⟩) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint D (by omega) (by omega) (by omega)) (by decide)]
        exact (congrArg (fun m : Mem => m.readW _ 128) (write16 _ _ _)).trans
          (Mem.readW_writeW_self _ _ 16 _ (by decide))
      | succ k =>
        simp only [List.getElem_cons_succ]
        have hk' : k < bs.length := by simpa using hk
        rw [← e0, d' k hk', e0, hT (k + 1) (by simpa using hk)]
        have hv : s₃.v bs[k] = s.v bs[k] := by
          have hne : bs[k] ≠ b := fun h => hbs (h ▸ List.getElem_mem _)
          have hne' : bs[k] ≠ .v31 := fun h => h31 (h ▸ List.mem_cons_of_mem _ (List.getElem_mem _))
          simp [s₃, s₂, s₁, State.setV, hne, hne']
        rw [hv]
    · refine (f₃.sub fun r hr => ?_).trans (f'.sub fun r hr => ?_) <;>
        simp only [List.mem_singleton] at hr <;> subst hr <;> refine ⟨_, List.mem_singleton_self _, ?_⟩
      · exact Region.sub_prefix (by simp; omega)
      · exact Offset.sub D (by omega) (by simp; omega)
    · simp only [List.mem_cons, not_or] at hr
      rw [o' r hr.2 h]; simp [s₃, s₂, s₁, State.setV, hr.1, h]
    · rw [g']; rfl
    · rw [sp']; rfl
    · rw [rd']; rfl
    · rw [wr']; rfl

/-- `preL rs j`: each register of `rs` loaded from the data block
`D + 16 (j + k)` and XORed with the tweak at `S + 16 (j + k)` (`x12`
holding `S`). -/
theorem preL_ok (D S : Addr) :
    ∀ (rs : List VReg) (j : Nat) (s : State), rs.Nodup → .v31 ∉ rs → j + rs.length ≤ 8 →
    s.gpr .x2 = D → s.gpr .x12 = S →
    (∀ k < rs.length, InRegions (s.rd ++ s.wr) (D + BitVec.ofNat 64 (16 * (j + k))) 16) →
    (∀ k < rs.length, InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 (16 * (j + k))) 16) →
    WP isa (.block (preL rs j)) s fun s' =>
      (∀ k (h : k < rs.length), s'.v rs[k] =
        s.mem.readW (D + BitVec.ofNat 64 (16 * (j + k))) 128 ^^^
          s.mem.readW (S + BitVec.ofNat 64 (16 * (j + k))) 128) ∧
      (∀ r, r ∉ rs → r ≠ .v31 → s'.v r = s.v r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr
  | [], _, s, _, _, _, _, _, _, _ =>
    WP.block_nil ⟨fun _ h => absurd h (by simp), fun _ _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩
  | b :: bs, j, s, hnd, h31, hj, hx2, hx12, hld, hlt => by
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    have hb31 : b ≠ .v31 := fun h => h31 (h ▸ List.mem_cons_self ..)
    simp only [List.length_cons] at hj
    have e0 : ∀ (p : Addr) (k : Nat), p + BitVec.ofNat 64 (16 * (j + 1 + k)) = p + BitVec.ofNat 64 (16 * (j + (k + 1))) :=
      fun p k => by rw [show j + 1 + k = j + (k + 1) by omega]
    let d := s.mem.readW (D + BitVec.ofNat 64 (16 * j)) 128
    let T := s.mem.readW (S + BitVec.ofNat 64 (16 * j)) 128
    let s₁ := s.setV b d
    let s₂ := s₁.setV .v31 T
    let s₃ := s₂.setV b (s₂.v b ^^^ s₂.v .v31)
    have x₁ : exec (.ldrq b .x2 (16 * j)) s = some s₁ := by
      rw [exec_ldrq ⟨by omega, by omega⟩ (by rw [hx2]; simpa using hld 0 (by simp)), hx2]
    have x₂ : exec (.ldrq .v31 .x12 (16 * j)) s₁ = some s₂ := by
      rw [exec_ldrq ⟨by omega, by omega⟩ (by simpa [s₁, State.setV, hx12] using hlt 0 (by simp))]
      simp [s₁, State.setV, hx12, s₂, T]
    have x₃ : exec (.vop (.logic .eor b b .v31)) s₂ = some s₃ := rfl
    rw [preL, preL1, WP.block_append_iff]
    refine WP.of_runBlock ⟨s₃, by simp only [runBlock_cons, isa, x₁, runStep_some, x₂, x₃, runBlock_nil], ?_⟩
    have v₃ : s₃.v b = d ^^^ T := by simp [s₃, s₂, s₁, State.setV, hb31]
    have g₃ : s₃.gpr = s.gpr := rfl
    have m₃ : s₃.mem = s.mem := rfl
    refine WP.mono (preL_ok D S bs (j + 1) s₃ (List.nodup_cons.mp hnd).2 (fun h => h31 (List.mem_cons_of_mem _ h))
      (by omega) (by rw [g₃, hx2]) (by rw [g₃, hx12])
      (fun k hk => by rw [e0]; exact hld (k + 1) (by simp; omega))
      (fun k hk => by rw [e0]; exact hlt (k + 1) (by simp; omega)))
      fun s' ⟨v', o', g', m', sp', rd', wr'⟩ => ?_
    refine ⟨fun k hk => ?_, fun r hr h => ?_, g'.trans g₃, m'.trans m₃, sp', rd', wr'⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [o' _ hbs hb31, v₃]
      | succ k =>
        simp only [List.getElem_cons_succ]
        have hk' : k < bs.length := by simpa using hk
        rw [v' k hk', m₃, e0, e0]
    · simp only [List.mem_cons, not_or] at hr
      rw [o' r hr.2 h]; simp [s₃, s₂, s₁, State.setV, hr.1, h]

/-- The tweak in `lo`, `hi` stored as two words at `a`, read as one. -/
theorem readW_store2 (m : Mem) (a : Addr) (lo hi : BitVec 64) :
    ((m.writeW a lo).writeW (a + BitVec.ofNat 64 8) hi).readW a 128 = hi ++ lo := by
  have hs : Mem.Sep a (64 / 8) (a + BitVec.ofNat 64 8) (64 / 8) := by
    have := Offset.sep a (d := 0) (n := 8) (e := 8) (k := 8) (by decide) (by decide) (by decide)
    simpa using this
  rw [readW128, Mem.readW_writeW_self64, Mem.readW_writeW_sep hs (by decide), Mem.readW_writeW_self64]

/-- `genStep r j`: the tweak stored at `S + 16 j` (`r` holding `S`), and
multiplied by `α`. -/
theorem genStep_run (r : Reg) (S : Addr) (j : Nat) (s : State) (hj : j < 8) (hr : s.gpr r = S)
    (in0 : InRegions s.wr (S + BitVec.ofNat 64 (16 * j)) 8)
    (in8 : InRegions s.wr (S + BitVec.ofNat 64 (16 * j + 8)) 8) :
    ∃ s', runBlock isa (genStep r j) s = some s' ∧
      s'.mem = (s.mem.writeW (S + BitVec.ofNat 64 (16 * j)) (s.gpr .x14)).writeW
        (S + BitVec.ofNat 64 (16 * j + 8)) (s.gpr .x15) ∧
      tweakOf s' = mulA128 (tweakOf s) ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x14 → r ≠ .x15 → s'.gpr r = s.gpr r) ∧
      s'.v = s.v ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let s₁ : State := { s with mem := s.mem.writeW (S + BitVec.ofNat 64 (16 * j)) (s.gpr .x14) }
  let s₂ : State := { s₁ with mem := s₁.mem.writeW (S + BitVec.ofNat 64 (16 * j + 8)) (s.gpr .x15) }
  have x₁ : exec (.str .x .x14 r (16 * j)) s = some s₁ := by
    rw [exec_str_x ⟨by omega, by omega⟩ (by rw [hr]; exact in0), hr]
  have x₂ : exec (.str .x .x15 r (16 * j + 8)) s₁ = some s₂ := by
    rw [exec_str_x ⟨by omega, by omega⟩ (by simpa [s₁, hr] using in8)]
    simp [s₁, s₂, hr]
  obtain ⟨s', hr', ht, hg, hv, hm, hsp, hrd, hwr⟩ := mulA_run s₂
  refine ⟨s', ?_, by rw [hm], by rw [ht], fun r h1 h2 h3 h4 => by rw [hg r h1 h2 h3 h4],
    by rw [hv], by rw [hsp], by rw [hrd], by rw [hwr]⟩
  rw [genStep, List.cons_append, List.cons_append, List.nil_append]
  simp only [runBlock_cons, isa, x₁, runStep_some, x₂]
  exact hr'

/-- The first `k` steps of `gen r`, from the tweak `t`: the tweaks `twW t j`
at `S + 16 j` (`r` holding `S`). -/
theorem gen_ok (r : Reg) (S : Addr) (hS : S.toNat + 128 ≤ 2 ^ 64) (h9 : r ≠ .x9) (h10 : r ≠ .x10)
    (h14 : r ≠ .x14) (h15 : r ≠ .x15) (s : State) (hr : s.gpr r = S)
    (hin : ∀ d, d + 8 ≤ 128 → InRegions s.wr (S + BitVec.ofNat 64 d) 8) :
    ∀ k ≤ 8, WP isa (.block ((List.range k).flatMap (genStep r))) s fun s' =>
      (∀ j < k, s'.mem.readW (S + BitVec.ofNat 64 (16 * j)) 128 = twW (tweakOf s) j) ∧
      Frame [⟨S, 128⟩] s.mem s'.mem ∧ tweakOf s' = twW (tweakOf s) k ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x14 → r ≠ .x15 → s'.gpr r = s.gpr r) ∧
      s'.v = s.v ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (by omega), Frame.refl _ _, rfl, fun _ _ _ _ _ => rfl, rfl, rfl, rfl,
      rfl⟩
  | k + 1, hk => by
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (gen_ok r S hS h9 h10 h14 h15 s hr hin k (by omega))
      fun s₁ ⟨e₁, f₁, t₁, g₁, v₁, sp₁, rd₁, wr₁⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    obtain ⟨s', r', m', t', g', v', sp', rd', wr'⟩ := genStep_run r S k s₁ (by omega)
      (by rw [g₁ r h9 h10 h14 h15, hr]) (by rw [wr₁]; exact hin _ (by omega))
      (by rw [wr₁]; exact hin _ (by omega))
    refine WP.of_runBlock ⟨s', r', ?_⟩
    have hsep : ∀ j < k, Region.Disjoint ⟨S + BitVec.ofNat 64 (16 * j), 16⟩ ⟨S + BitVec.ofNat 64 (16 * k), 16⟩ :=
      fun j hj => Offset.disjoint S (by omega) (by omega) (by omega)
    have fk : Frame [⟨S + BitVec.ofNat 64 (16 * k), 16⟩] s₁.mem s'.mem := by
      rw [m']
      have c0 : Region.Contains ⟨S + BitVec.ofNat 64 (16 * k), 16⟩ (S + BitVec.ofNat 64 (16 * k)) (64 / 8) := by
        have := Offset.contains_base (S + BitVec.ofNat 64 (16 * k)) (d := 0) (n := 8) (k := 16) (by decide) (by decide)
        simpa using this
      have c8 : Region.Contains ⟨S + BitVec.ofNat 64 (16 * k), 16⟩ (S + BitVec.ofNat 64 (16 * k + 8)) (64 / 8) := by
        rw [← Offset.add_add_eq S (show 16 * k + 8 = 16 * k + 8 from rfl)]
        exact Offset.contains_base _ (d := 8) (n := 8) (k := 16) (by decide) (by decide)
      exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c0).writeW (List.mem_singleton_self _) _ c8
    refine ⟨fun j hj => ?_, ?_, by rw [t', t₁]; rfl, fun r h1 h2 h3 h4 => by rw [g' r h1 h2 h3 h4, g₁ r h1 h2 h3 h4],
      v'.trans v₁, sp'.trans sp₁, rd'.trans rd₁, wr'.trans wr₁⟩
    · by_cases hjk : j = k
      · subst hjk
        rw [m', ← Offset.add_add_eq S (show 16 * j + 8 = 16 * j + 8 from rfl), readW_store2, ← tweakOf, t₁]
      · rw [fk.readW (r := ⟨S + BitVec.ofNat 64 (16 * j), 16⟩) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact hsep j (by omega)) (by decide), e₁ j (by omega)]
    · exact f₁.trans (fk.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub_base S (by omega)⟩)

end VG.Proof.AesXts.AArch64.Aes
