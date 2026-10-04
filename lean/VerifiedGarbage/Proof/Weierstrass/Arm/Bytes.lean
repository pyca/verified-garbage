import VerifiedGarbage.Proof.Weierstrass.Arm.Copy
import VerifiedGarbage.Proof.Weierstrass.Words32

/-!
# Short Weierstrass curves on 32-bit ARM: numbers to and from big-endian bytes

`loadBE n o src` reads the `8 n` bytes at `src`, big-endian, into `[o]`
(`loadBE_ok`), and `storeBE n dst d a` writes `[a]` masked with `r10`, so the
number or zeros, big-endian, to the `8 n` bytes at `dst + d` (`storeBE_ok`):
a 32-bit word at a time, each byte-reversed (`rev`, which is `byteRev32`),
from the last.
-/

namespace VG.Proof.Weierstrass.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass
  VG.Proof.Mont.Arm VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_ldr wp_str wp_dp op2_reg dpVal)

theorem rev_eq (w : BitVec 32) : rev w = byteRev32 w := rfl

theorem wp_rev {s : State} {is : List Instr} {Q : State → Prop} {d m : Reg}
    (k : ∀ s', Upd s s' d (rev (s.gpr m)) → WP isa (.block is) s' Q) :
    WP isa (.block (.rev d m :: is)) s Q :=
  VG.Proof.X25519.Arm.WP.cons rfl (k _ (Upd.setReg _ _ _))

/-- A 32-bit word of a range whose bytes are kept. -/
theorem readW32_keep {m m' : Mem} {p : Addr} {d : Nat}
    (h : ∀ i < 4, m' (p + BitVec.ofNat 64 (d + i)) = m (p + BitVec.ofNat 64 (d + i))) :
    m'.readW (p + BitVec.ofNat 64 d) 32 = m.readW (p + BitVec.ofNat 64 d) 32 :=
  Mem.readW_congr fun i hi => by rw [Offset.add_add, h i hi]

/-! ## Loads -/

/-- One word of `loadBE`. -/
def ldStep (n o : Nat) (src : Reg) (j : Nat) : List Instr :=
  [.ldr .r4 src (4 * (2 * n - 1 - j)), .rev .r4 .r4, .str .r4 wb (o + 4 * j)]

theorem loadBE_eq (n o : Nat) (src : Reg) : loadBE n o src = (List.range (2 * n)).flatMap (ldStep n o src) :=
  rfl

theorem ldSteps_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {n o : Nat} {src : Reg}
    (hsrc : src ≠ .r4) (ho : o + 8 * n ≤ size) (hp : (s.gpr src).toNat + 8 * n ≤ 2 ^ 32)
    (hr : ∀ d, d + 4 ≤ 8 * n → InRegions (s.rd ++ s.wr) (State.addr (s.gpr src) + BitVec.ofNat 64 d) 4)
    (hd : Region.Disjoint ⟨State.addr (s.gpr src), 8 * n⟩ ⟨off base o, 8 * n⟩) : ∀ k, k ≤ 2 * n →
    WP isa (.block ((List.range k).flatMap (ldStep n o src))) s fun s' =>
      (∀ j < k, w32 s'.mem base (o + 4 * j) =
        (byteRev32 (s.mem.readW (State.addr (s.gpr src) + BitVec.ofNat 64 (4 * (2 * n - 1 - j))) 32)).toNat) ∧
      Rest [.r4] s s' ∧ Outside base o (4 * k) s.mem s'.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), Rest.refl _ _,
      VG.Proof.Mont.Outside.refl _ _ _ _⟩
  | k + 1, hk => by
    have hnw := hs.nowrap
    have hsm := hs.small
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine VG.Proof.X25519.Arm.WP.append (ldSteps_ok hs hsrc ho hp hr hd k (by omega)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    have hs₁ := hs.of_rest k₁ (by decide)
    have hp₁ : s₁.gpr src = s.gpr src := k₁.gpr _ (by simpa using hsrc)
    have ha₁ : State.addr (s₁.gpr src + BitVec.ofNat 32 (4 * (2 * n - 1 - k))) =
        State.addr (s.gpr src) + BitVec.ofNat 64 (4 * (2 * n - 1 - k)) := by
      rw [hp₁, addr_add (by omega)]
    have hr₁ : InRegions (s₁.rd ++ s₁.wr) (State.addr (s.gpr src) + BitVec.ofNat 64 (4 * (2 * n - 1 - k))) 4 := by
      rw [k₁.rd, k₁.wr]; exact hr _ (by omega)
    have hw : s₁.mem.readW (State.addr (s.gpr src) + BitVec.ofNat 64 (4 * (2 * n - 1 - k))) 32 =
        s.mem.readW (State.addr (s.gpr src) + BitVec.ofNat 64 (4 * (2 * n - 1 - k))) 32 :=
      readW32_keep fun i hi => keep_of_disjoint (O₁.mono (Nat.le_refl _) (by omega)) hd (by omega)
        (by omega) (by omega)
    rw [ldStep]
    refine wp_ldr (by omega) ha₁ hr₁ fun s₂ u₂ => ?_
    refine wp_rev fun s₃ u₃ => ?_
    have k₃ : Rest [.r4] s₁ s₃ := (u₂.rest (by simp)).trans (u₃.rest (by simp))
    have hs₃ := hs₁.of_rest k₃ (by decide)
    refine wp_str (hs.off_lt (by omega)) (hs₃.ea (d := o + 4 * k) (by omega))
      (hs₃.write (d := o + 4 * k) (n := 4) (by omega)) fun s₄ m₄ => WP.block_nil ?_
    have O₂ : Outside base (o + 4 * k) 4 s₁.mem s₄.mem := by
      rw [m₄.mem, u₃.mem, u₂.mem]; exact writeW32_outside _ _ _ (by omega)
    refine ⟨fun j hj => ?_, k₁.trans (k₃.trans (m₄.rest _)),
      (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))⟩
    rcases Nat.lt_or_ge j k with h | h
    · rw [O₂.w32 (by omega) (by omega), e₁ j h]
    · obtain rfl : j = k := by omega
      rw [m₄.mem, u₃.mem, u₂.mem, w32_write_self, u₃.gpr, u₂.gpr, hw, rev_eq]

/-- `[o] = ` the `8 n` bytes at `src`, big-endian. -/
theorem loadBE_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {n o : Nat} {src : Reg}
    (hsrc : src ≠ .r4) (ho : o + 8 * n ≤ size) (hp : (s.gpr src).toNat + 8 * n ≤ 2 ^ 32)
    (hr : ∀ d, d + 4 ≤ 8 * n → InRegions (s.rd ++ s.wr) (State.addr (s.gpr src) + BitVec.ofNat 64 d) 4)
    (hd : Region.Disjoint ⟨State.addr (s.gpr src), 8 * n⟩ ⟨off base o, 8 * n⟩) :
    WP isa (.block (loadBE n o src)) s fun s' =>
      wordsVal s'.mem base o n =
        Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt s.mem (State.addr (s.gpr src)) (8 * n)) ∧
      Rest [.r4] s s' ∧ Outside base o (8 * n) s.mem s'.mem := by
  rw [loadBE_eq]
  refine WP.mono (ldSteps_ok hs hsrc ho hp hr hd (2 * n) (Nat.le_refl _)) fun s' ⟨e, k, O⟩ =>
    ⟨?_, k, by rw [show 8 * n = 4 * (2 * n) by omega]; exact O⟩
  rw [wordsVal_eq_val32, show 8 * n = 4 * (2 * n) by omega]
  exact val32_eq_ofBytes _ _ _ _ o (2 * n) e

/-! ## Stores -/

/-- One word of `storeBE`. -/
def stStep (n : Nat) (dst : Reg) (d a j : Nat) : List Instr :=
  [.ldr .r4 wb (a + 4 * j), .dp .and .r4 .r4 (.reg .r10), .rev .r4 .r4, .str .r4 dst (d + 4 * (2 * n - 1 - j))]

theorem storeBE_eq (n : Nat) (dst : Reg) (d a : Nat) :
    storeBE n dst d a = (List.range (2 * n)).flatMap (stStep n dst d a) := rfl

theorem stSteps_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {n d a : Nat} {dst : Reg}
    (hdst : dst ≠ .r4) {c : Bool} (hc : s.gpr .r10 = (if c then BitVec.allOnes 32 else 0))
    (ha : a + 8 * n ≤ size) (hq : (s.gpr dst).toNat + d + 8 * n ≤ 2 ^ 32) (hd4 : d + 8 * n ≤ 4096)
    (hw : ∀ e, e + 4 ≤ 8 * n →
      InRegions s.wr (State.addr (s.gpr dst) + BitVec.ofNat 64 d + BitVec.ofNat 64 e) 4)
    (hd : Region.Disjoint ⟨off base a, 8 * n⟩ ⟨State.addr (s.gpr dst) + BitVec.ofNat 64 d, 8 * n⟩) :
    ∀ k, k ≤ 2 * n →
    WP isa (.block ((List.range k).flatMap (stStep n dst d a))) s fun s' =>
      (∀ j < k, s'.mem.readW (State.addr (s.gpr dst) + BitVec.ofNat 64 d +
          BitVec.ofNat 64 (4 * (2 * n - 1 - j))) 32 =
        byteRev32 (s.mem.readW (off base (a + 4 * j)) 32 &&& (if c then BitVec.allOnes 32 else 0))) ∧
      Rest [.r4] s s' ∧
      Outside (State.addr (s.gpr dst) + BitVec.ofNat 64 d) (4 * (2 * n - k)) (4 * k) s.mem s'.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), Rest.refl _ _,
      VG.Proof.Mont.Outside.refl _ _ _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine VG.Proof.X25519.Arm.WP.append (stSteps_ok hs hdst hc ha hq hd4 hw hd k (by omega))
      fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    have hs₁ := hs.of_rest k₁ (by decide)
    have hq₁ : s₁.gpr dst = s.gpr dst := k₁.gpr _ (by simpa using hdst)
    have hc₁ : s₁.gpr .r10 = (if c then BitVec.allOnes 32 else 0) := by rw [k₁.gpr _ (by decide), hc]
    have hword : s₁.mem.readW (off base (a + 4 * k)) 32 = s.mem.readW (off base (a + 4 * k)) 32 := by
      show s₁.mem.readW (base + BitVec.ofNat 64 (a + 4 * k)) 32 = s.mem.readW (base + BitVec.ofNat 64 (a + 4 * k)) 32
      rw [← Offset.add_add]
      exact readW32_keep fun i hi => keep_of_disjoint' (O₁.mono (Nat.zero_le _) (by omega)) hd (by omega)
        (by omega) (by omega)
    rw [stStep]
    refine wp_ldr (hs.off_lt (by omega)) (hs₁.ea (d := a + 4 * k) (by omega))
      (hs₁.read (d := a + 4 * k) (n := 4) (by omega)) fun s₂ u₂ => ?_
    refine wp_dp (op2_reg _ _) fun s₃ u₃ => ?_
    refine wp_rev fun s₄ u₄ => ?_
    have k₄ : Rest [.r4] s₁ s₄ := (u₂.rest (by simp)).trans ((u₃.rest (by simp)).trans (u₄.rest (by simp)))
    have hq₄ : s₄.gpr dst = s.gpr dst := by rw [k₄.gpr _ (by simpa using hdst), hq₁]
    have ha₄ : State.addr (s₄.gpr dst + BitVec.ofNat 32 (d + 4 * (2 * n - 1 - k))) =
        State.addr (s.gpr dst) + BitVec.ofNat 64 d + BitVec.ofNat 64 (4 * (2 * n - 1 - k)) := by
      rw [hq₄, addr_add (by omega), Offset.add_add]
    have hw₄ : InRegions s₄.wr (State.addr (s.gpr dst) + BitVec.ofNat 64 d +
        BitVec.ofNat 64 (4 * (2 * n - 1 - k))) 4 := by
      rw [k₄.wr, k₁.wr]; exact hw _ (by omega)
    refine wp_str (by omega) ha₄ hw₄ fun s₅ m₅ => WP.block_nil ?_
    have v₄ : s₄.gpr .r4 = byteRev32 (s.mem.readW (off base (a + 4 * k)) 32 &&&
        (if c then BitVec.allOnes 32 else 0)) := by
      rw [u₄.gpr, u₃.gpr, dpVal, u₂.gpr, u₂.other _ (by decide), hc₁, hword, rev_eq]
    have mem₄ : s₄.mem = s₁.mem := by rw [u₄.mem, u₃.mem, u₂.mem]
    have O₂ : Outside (State.addr (s.gpr dst) + BitVec.ofNat 64 d) (4 * (2 * n - 1 - k)) 4 s₁.mem s₅.mem := by
      rw [m₅.mem, mem₄]; exact writeW32_outside _ _ _ (by omega)
    refine ⟨fun j hj => ?_, k₁.trans (k₄.trans (m₅.rest _)),
      (O₁.mono (by omega) (by omega)).trans (O₂.mono (by omega) (by omega))⟩
    rcases Nat.lt_or_ge j k with h | h
    · rw [m₅.mem, mem₄, Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide),
        e₁ j h]
    · obtain rfl : j = k := by omega
      rw [m₅.mem, Mem.readW_writeW_self32, v₄]

/-- The `8 n` bytes at `dst + d` are `[a]` big-endian if the mask `r10` is all
ones (`c`), zeros if it is zero. -/
theorem storeBE_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {n d a : Nat} {dst : Reg}
    (hdst : dst ≠ .r4) (c : Bool) (hc : s.gpr .r10 = (if c then BitVec.allOnes 32 else 0))
    (ha : a + 8 * n ≤ size) (hq : (s.gpr dst).toNat + d + 8 * n ≤ 2 ^ 32) (hd4 : d + 8 * n ≤ 4096)
    (hw : ∀ e, e + 4 ≤ 8 * n →
      InRegions s.wr (State.addr (s.gpr dst) + BitVec.ofNat 64 d + BitVec.ofNat 64 e) 4)
    (hd : Region.Disjoint ⟨off base a, 8 * n⟩ ⟨State.addr (s.gpr dst) + BitVec.ofNat 64 d, 8 * n⟩) :
    WP isa (.block (storeBE n dst d a)) s fun s' =>
      Spec.Ecdsa.bytesAt s'.mem (State.addr (s.gpr dst) + BitVec.ofNat 64 d) (8 * n) =
        (if c then Spec.Weierstrass.toBytes (8 * n) (wordsVal s.mem base a n)
          else List.replicate (8 * n) 0) ∧
      Rest [.r4] s s' ∧ Outside (State.addr (s.gpr dst) + BitVec.ofNat 64 d) 0 (8 * n) s.mem s'.mem := by
  rw [storeBE_eq]
  refine WP.mono (stSteps_ok hs hdst hc ha hq hd4 hw hd (2 * n) (Nat.le_refl _)) fun s' ⟨e, k, O⟩ =>
    ⟨?_, k, ?_⟩
  · rw [wordsVal_eq_val32, show 8 * n = 4 * (2 * n) by omega]
    exact bytesAt_eq_toBytes32 _ _ _ _ c e
  · rw [Nat.sub_self, Nat.mul_zero, show 4 * (2 * n) = 8 * n by omega] at O
    exact O

end VG.Proof.Weierstrass.Arm
