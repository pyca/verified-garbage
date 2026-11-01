module

public import VerifiedGarbage.Impl.Weierstrass.AArch64.PubNaf
public import VerifiedGarbage.Proof.Mont.AArch64.Words
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombPublic
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Weierstrass.PointOpsContract
public import VerifiedGarbage.Proof.Weierstrass.InverseContract

/-!
# The public NAF's table: loads and stores through a pointer and an offset

The table of `PubNaf` may lie above the offsets `add` can encode, so its
entries are read and written through `x0 + stride · i` and the table's offset
in the load or store (`ldOff_ok`, `stOff_ok`, `entry_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.PubNaf

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Weierstrass.AArch64.PubNaf
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

/-- `k` words from `x16 + o` (`x16 = base + p`) to `dst`, apart. -/
theorem ldOff_ok {s : State} {base : Addr} {size p o dst n : Nat}
    (hs : Scr s base size) (hp : s.gpr .x16 = off base p)
    (hd : dst + 8 * n ≤ size) (hd8 : dst % 8 = 0) (ho8 : o % 8 = 0)
    (hsrc : p + o + 8 * n ≤ size)
    (hap : dst + 8 * n ≤ p + o ∨ p + o + 8 * n ≤ dst) :
    ∀ k ≤ n, WP isa (.block ((List.range k).flatMap fun i =>
      [.ldr .x .x4 .x16 (o + 8 * i), st .x4 (dst + 8 * i)])) s fun t =>
      (∀ i < k, word t.mem base (dst + 8 * i) = word s.mem base (p + o + 8 * i)) ∧
      KeepRegs [.x4] s t ∧ Outside base dst (8 * k) s.mem t.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _),
      ⟨fun _ _ => rfl, rfl, rfl, rfl⟩, Outside.refl _ _ _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (ldOff_ok hs hp hd hd8 ho8 hsrc hap k (by omega_using [hk])) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    rw [← List.singleton_append, WP.block_append_iff]
    have ha : off base p + BitVec.ofNat 64 (o + 8 * k) = off base (p + o + 8 * k) := by
      simp [off, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_assoc]
    have hr : InRegions (s₁.rd ++ s₁.wr) (off base p + BitVec.ofNat 64 (o + 8 * k)) 8 := by
      rw [ha]
      exact ⟨_, List.mem_append_right _ hs₁.wr, hs₁.contains (by omega_using [hsrc, hk]) (by decide)⟩
    refine WP.mono (direct_load (by rw [k₁.gpr _ (by decide), hp])
      (o := o + 8 * k) (by have := hs.enc; omega_using [ho8, hsrc, hk, this]) hr) fun s₂ ⟨e₂, k₂, _⟩ => ?_
    have hs₂ := hs₁.of_keeps k₂ (by decide)
    refine WP.mono (st_ok hs₂ (d := dst + 8 * k) (by omega_using [hd, hk]) (by omega_using [hd8]) .x4) fun t et => ?_
    have mt : t.mem = s₂.mem.writeW (off base (dst + 8 * k)) (s₂.gpr .x4) := by rw [et]
    have kt : KeepRegs [] s₂ t := by subst et; exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩
    have O₂ : Outside base (dst + 8 * k) 8 s₂.mem t.mem := by
      rw [mt]; exact writeW_outside _ _ _ (by omega_using [hd, hk, hn])
    have old : word s₁.mem (off base p) (o + 8 * k) = word s.mem base (p + o + 8 * k) := by
      simp only [word, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      change word s₁.mem base (p + (o + 8 * k)) = _
      rw [← Nat.add_assoc]
      exact O₁.word (by omega_using [hap, hk]) (by omega_using [hsrc, hk, hn])
    refine ⟨fun i hi => ?_, k₁.trans ((Keeps.regs k₂).trans (kt.mono (by simp))), ?_⟩
    · rcases Nat.lt_or_ge i k with h | h
      · rw [O₂.word (by omega_using [h]) (by omega_using [hd, hk, hn, h]), k₂.mem, e₁ i h]
      · obtain rfl : i = k := by omega_using [hi, h]
        rw [mt, word_writeW_self, e₂, old]
    · refine (O₁.mono (Nat.le_refl _) (by omega_using [])).trans ?_
      rw [← k₂.mem]
      exact O₂.mono (by omega_using []) (by omega_using [])

/-- One store through `x20 + o`. -/
theorem stOffWord_ok {s : State} {base : Addr} {size p o : Nat}
    (hs : Scr s base size) (hp : s.gpr .x20 = off base p) (ho8 : o % 8 = 0)
    (hd : p + o + 8 ≤ size) :
    WP isa (.block [.str .x .x4 .x20 o]) s fun t =>
      t = {s with mem := s.mem.writeW (off base (p + o)) (s.gpr .x4)} := by
  have ha : s.gpr .x20 + BitVec.ofNat 64 o = off base (p + o) := by
    rw [hp]; simp [off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  have hr : InRegions s.wr (s.gpr .x20 + BitVec.ofNat 64 o) 8 := by
    rw [ha]; exact ⟨_, hs.wr, hs.contains hd (by decide)⟩
  have he : o % 8 = 0 ∧ o < 32768 := by have := hs.enc; omega_using [ho8, hd, this]
  apply WP.of_runBlock
  simp only [runBlock_cons, exec_str_x he hr, ha, runStep_some, runBlock_nil,
    Option.some.injEq, exists_eq_left']

/-- `k` words from `src` to `x20 + o` (`x20 = base + p`), apart. -/
theorem stOff_ok {s : State} {base : Addr} {size src p o n : Nat}
    (hs : Scr s base size) (hp : s.gpr .x20 = off base p) (ho8 : o % 8 = 0)
    (hd : p + o + 8 * n ≤ size) (hsrc : src + 8 * n ≤ size) (hs8 : src % 8 = 0)
    (hap : p + o + 8 * n ≤ src ∨ src + 8 * n ≤ p + o) :
    ∀ k ≤ n, WP isa (.block ((List.range k).flatMap fun i =>
      [ld .x4 (src + 8 * i), .str .x .x4 .x20 (o + 8 * i)])) s fun t =>
      (∀ i < k, word t.mem base (p + o + 8 * i) = word s.mem base (src + 8 * i)) ∧
      KeepRegs [.x4] s t ∧ Outside base (p + o) (8 * k) s.mem t.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _),
      ⟨fun _ _ => rfl, rfl, rfl, rfl⟩, Outside.refl _ _ _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (stOff_ok hs hp ho8 hd hsrc hs8 hap k (by omega_using [hk])) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    rw [← List.singleton_append, WP.block_append_iff]
    refine WP.mono (ld_ok hs₁ (d := src + 8 * k) (by omega_using [hsrc, hk]) (by omega_using [hs8]) .x4) fun s₂ ⟨e₂, k₂, _⟩ => ?_
    have hs₂ := hs₁.of_keeps k₂ (by decide)
    have h20 : s₂.gpr .x20 = off base p := by rw [k₂.gpr _ (by decide), k₁.gpr _ (by decide), hp]
    refine WP.mono (stOffWord_ok hs₂ h20 (o := o + 8 * k) (by omega_using [ho8]) (by omega_using [hd, hk])) fun t et => ?_
    have mt : t.mem = s₂.mem.writeW (off base (p + o + 8 * k)) (s₂.gpr .x4) := by
      rw [et, Nat.add_assoc]
    have kt : KeepRegs [] s₂ t := by subst et; exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩
    have O₂ : Outside base (p + o + 8 * k) 8 s₂.mem t.mem := by
      rw [mt]; exact writeW_outside _ _ _ (by omega_using [hd, hk, hn])
    have old : word s₁.mem base (src + 8 * k) = word s.mem base (src + 8 * k) :=
      O₁.word (by omega_using [hap, hk]) (by omega_using [hsrc, hk, hn])
    refine ⟨fun i hi => ?_, k₁.trans ((Keeps.regs k₂).trans (kt.mono (by simp))), ?_⟩
    · rcases Nat.lt_or_ge i k with h | h
      · rw [O₂.word (by omega_using [h]) (by omega_using [hd, hk, hn, h]), k₂.mem, e₁ i h]
      · obtain rfl : i = k := by omega_using [hi, h]
        rw [mt, word_writeW_self, e₂, old]
    · refine (O₁.mono (Nat.le_refl _) (by omega_using [])).trans ?_
      rw [← k₂.mem]
      exact O₂.mono (by omega_using []) (by omega_using [])

/-- `x16 = base + stride (a - 1)` for entry `a ≥ 1` in `x2`. -/
theorem entryAddr_ok (K : WinCfg) {s : State} {base : Addr} {a : Nat}
    (h0 : s.gpr .x0 = base) (h2 : s.gpr .x2 = BitVec.ofNat 64 a) (ha : 1 ≤ a)
    (hst : stride K < 65536) :
    WP isa (.block [.subImm .x .x2 .x2 1, .movz .x .x17 (BitVec.ofNat 16 (stride K)) 0,
      .mul .x .x2 .x2 .x17, .add .x .x16 .x0 .x2]) s fun t =>
      t.gpr .x16 = off base (stride K * (a - 1)) ∧ Keeps [.x2, .x16, .x17] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write,
    BitVec.setWidth_eq, Size.bits, show 16 * 0 < 64 from by decide, show 1 < 4096 from by decide,
    ite_true, ite_false, reduceCtorEq, h0, h2, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · simp only [Nat.mul_zero, BitVec.shiftLeft_zero]
    rw [BitVec.ofNat_sub_ofNat_of_le a 1 (by decide) ha]
    have hw : BitVec.setWidth 64 (BitVec.ofNat 16 (stride K)) = BitVec.ofNat 64 (stride K) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      omega_using [hst]
    rw [hw, ← BitVec.ofNat_mul, Nat.mul_comm]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]

/-- The cache's entry `a` (in `x2`, `1 … 8`), at `x16`: `x2 = a - 1`. -/
theorem cacheAddr_ok {s : State} {base : Addr} {a c : Nat}
    (h0 : s.gpr .x0 = base) (h2 : s.gpr .x2 = BitVec.ofNat 64 a) (ha : 1 ≤ a) (hc : c < 65536) :
    WP isa (.block [.subImm .x .x2 .x2 1, .movz .x .x17 (BitVec.ofNat 16 c) 0,
      .mul .x .x17 .x2 .x17, .add .x .x16 .x0 .x17]) s fun t =>
      t.gpr .x16 = off base (c * (a - 1)) ∧ t.gpr .x2 = BitVec.ofNat 64 (a - 1) ∧
      Keeps [.x2, .x16, .x17] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write,
    BitVec.setWidth_eq, Size.bits, show 16 * 0 < 64 from by decide, show 1 < 4096 from by decide,
    ite_true, ite_false, reduceCtorEq, h0, h2, Option.some.injEq, exists_eq_left']
  have hw : BitVec.setWidth 64 (BitVec.ofNat 16 c) = BitVec.ofNat 64 c := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega_using [hc]
  refine ⟨?_, ?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · simp only [Nat.mul_zero, BitVec.shiftLeft_zero]
    rw [BitVec.ofNat_sub_ofNat_of_le a 1 (by decide) ha, hw, ← BitVec.ofNat_mul, Nat.mul_comm]
  · rw [BitVec.ofNat_sub_ofNat_of_le a 1 (by decide) ha]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]

/-- Entry `a` of the table at `x16`, from `x2 = a - 1`. -/
theorem entryAddr2_ok (K : WinCfg) {s : State} {base : Addr} {a : Nat}
    (h0 : s.gpr .x0 = base) (h2 : s.gpr .x2 = BitVec.ofNat 64 (a - 1)) (hst : stride K < 65536) :
    WP isa (.block [.movz .x .x17 (BitVec.ofNat 16 (stride K)) 0,
      .mul .x .x2 .x2 .x17, .add .x .x16 .x0 .x2]) s fun t =>
      t.gpr .x16 = off base (stride K * (a - 1)) ∧ Keeps [.x2, .x16, .x17] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write,
    BitVec.setWidth_eq, Size.bits, show 16 * 0 < 64 from by decide,
    ite_true, ite_false, reduceCtorEq, h0, h2, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · simp only [Nat.mul_zero, BitVec.shiftLeft_zero]
    have hw : BitVec.setWidth 64 (BitVec.ofNat 16 (stride K)) = BitVec.ofNat 64 (stride K) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      omega_using [hst]
    rw [hw, ← BitVec.ofNat_mul, Nat.mul_comm]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]

end VG.Proof.Weierstrass.AArch64.PubNaf
