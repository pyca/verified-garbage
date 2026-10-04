import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy

/-!
# Short Weierstrass curves on AArch64: numbers to and from big-endian bytes

`loadBE n o src` reads the `8 n` bytes at `src`, big-endian, into `[o]`
(`loadBE_ok`), and `storeBE n dst d a` writes `[a]` masked with `x3`, so the
number or zeros, big-endian, to the `8 n` bytes at `dst + d` (`storeBE_ok`):
a word at a time, each byte-reversed (`rev`, which is `byteRev64`), from the
last.
-/

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

theorem rev64_eq (w : BitVec 64) : rev64 w = byteRev64 w := rfl

/-- The words of a region are accessible. -/
theorem inRegions_words {rs : List Region} {p : Addr} {len : Nat} (h : (⟨p, len⟩ : Region) ∈ rs)
    (hl : len ≤ 2 ^ 64) : ∀ d, d + 8 ≤ len → InRegions rs (p + BitVec.ofNat 64 d) 8 :=
  fun _ hd => ⟨_, h, Offset.contains_base p hd (by omega)⟩

/-- `t = byteRev64 [r + e]`, through `t`. -/
theorem ldRev_ok (s : State) {r t : Reg} {e : Nat} (he : e % 8 = 0 ∧ e < 32768)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr r + BitVec.ofNat 64 e) 8) :
    WP isa (.block [.ldr .x t r e, .rev t t]) s fun s' =>
      s'.gpr t = byteRev64 (s.mem.readW (s.gpr r + BitVec.ofNat 64 e) 64) ∧ Keeps [t] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, exec_ldr_x he hr, runStep_some, runBlock_nil, exec_rev, read_x,
    RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, fun q hq => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hq
  rw [RegUpd.gpr_write_of_ne _ _ _ hq, RegUpd.gpr_write_of_ne _ _ _ hq]

/-! ## Loads -/

/-- One word of `loadBE`. -/
def ldStep (n o : Nat) (src : Reg) (j : Nat) : List Instr :=
  [.ldr .x .x5 src (8 * (n - 1 - j)), .rev .x5 .x5, st .x5 (o + 8 * j)]

theorem loadBE_eq (n o : Nat) (src : Reg) : loadBE n o src = (List.range n).flatMap (ldStep n o src) := rfl

theorem ldSteps_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {n o : Nat} {src : Reg}
    (hsrc : src ≠ .x5) (ho : o + 8 * n ≤ size) (ho8 : o % 8 = 0) (hn : 8 * n ≤ 32768)
    (hr : ∀ d, d + 8 ≤ 8 * n → InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 d) 8)
    (hd : Region.Disjoint ⟨s.gpr src, 8 * n⟩ ⟨off base o, 8 * n⟩) : ∀ k, k ≤ n →
    WP isa (.block ((List.range k).flatMap (ldStep n o src))) s fun s' =>
      (∀ j < k, word s'.mem base (o + 8 * j) =
        byteRev64 (s.mem.readW (s.gpr src + BitVec.ofNat 64 (8 * (n - 1 - j))) 64)) ∧
      KeepRegs [.x5] s s' ∧ Outside base o (8 * k) s.mem s'.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), ⟨fun _ _ => rfl, rfl, rfl, rfl⟩,
      Outside.refl _ _ _ _⟩
  | k + 1, hk => by
    have hnw := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (ldSteps_ok hs hsrc ho ho8 hn hr hd k (by omega)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    have hp₁ : s₁.gpr src = s.gpr src := k₁.gpr _ (by simpa using hsrc)
    have hr₁ : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr src + BitVec.ofNat 64 (8 * (n - 1 - k))) 8 := by
      rw [k₁.rd, k₁.wr, hp₁]; exact hr _ (by omega)
    have hw : s₁.mem.readW (s.gpr src + BitVec.ofNat 64 (8 * (n - 1 - k))) 64 =
        s.mem.readW (s.gpr src + BitVec.ofNat 64 (8 * (n - 1 - k))) 64 :=
      readW_keep fun i hi => keep_of_disjoint (O₁.mono (Nat.le_refl _) (by omega)) hd (by omega)
        (by omega) (by omega)
    rw [ldStep, show ([.ldr .x .x5 src (8 * (n - 1 - k)), .rev .x5 .x5, st .x5 (o + 8 * k)] : List Instr) =
      [.ldr .x .x5 src (8 * (n - 1 - k)), .rev .x5 .x5] ++ [st .x5 (o + 8 * k)] from rfl,
      WP.block_append_iff]
    refine WP.mono (ldRev_ok s₁ (t := .x5) ⟨by omega, by omega⟩ hr₁) fun s₂ ⟨v₂, k₂⟩ => ?_
    have hs₂ := hs₁.of_keeps k₂ (by decide)
    refine WP.mono (st_out hs₂ (o := o + 8 * k) (by omega) (by omega) .x5) fun s₃ ⟨m₃, k₃, _⟩ => ?_
    rw [v₂, k₂.mem, hp₁] at m₃
    have O₂ : Outside base (o + 8 * k) 8 s₁.mem s₃.mem := by
      rw [m₃]; exact writeW_outside _ _ _ (by omega)
    refine ⟨fun j hj => ?_, k₁.trans ((Keeps.regs k₂).trans (k₃.mono (by simp))),
      (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))⟩
    rcases Nat.lt_or_ge j k with h | h
    · rw [O₂.word (by omega) (by omega), e₁ j h]
    · obtain rfl : j = k := by omega
      rw [m₃, word_writeW_self, hw]

/-- `[o] = ` the `8 n` bytes at `src`, big-endian. -/
theorem loadBE_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {n o : Nat} {src : Reg}
    (hsrc : src ≠ .x5) (ho : o + 8 * n ≤ size) (ho8 : o % 8 = 0) (hn : 8 * n ≤ 32768)
    (hr : ∀ d, d + 8 ≤ 8 * n → InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 d) 8)
    (hd : Region.Disjoint ⟨s.gpr src, 8 * n⟩ ⟨off base o, 8 * n⟩) :
    WP isa (.block (loadBE n o src)) s fun s' =>
      wordsVal s'.mem base o n = Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt s.mem (s.gpr src) (8 * n)) ∧
      KeepRegs [.x5] s s' ∧ Outside base o (8 * n) s.mem s'.mem := by
  rw [loadBE_eq]
  exact WP.mono (ldSteps_ok hs hsrc ho ho8 hn hr hd n (Nat.le_refl _)) fun s' ⟨e, k, O⟩ =>
    ⟨wordsVal_eq_ofBytes _ _ _ _ o n e, k, O⟩

/-! ## Stores -/

/-- One word of `storeBE`. -/
def stStep (n : Nat) (dst : Reg) (d a j : Nat) : List Instr :=
  [ld .x1 (a + 8 * j), .logic .and .x .x1 .x1 .x3, .rev .x1 .x1, .str .x .x1 dst (d + 8 * (n - 1 - j))]

theorem storeBE_eq (n : Nat) (dst : Reg) (d a : Nat) :
    storeBE n dst d a = (List.range n).flatMap (stStep n dst d a) := rfl

/-- `x1 = byteRev64 (x1 & x3)`. -/
theorem andRev_ok (s : State) :
    WP isa (.block [.logic .and .x .x1 .x1 .x3, .rev .x1 .x1]) s fun s' =>
      s'.gpr .x1 = byteRev64 (s.gpr .x1 &&& s.gpr .x3) ∧ Keeps [.x1] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write_self,
    BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, fun q hq => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hq
  rw [RegUpd.gpr_write_of_ne _ _ _ hq, RegUpd.gpr_write_of_ne _ _ _ hq]

/-- `[r + e] = t`. -/
theorem strReg_ok (s : State) {r t : Reg} {e : Nat} (he : e % 8 = 0 ∧ e < 32768)
    (hw : InRegions s.wr (s.gpr r + BitVec.ofNat 64 e) 8) :
    WP isa (.block [.str .x t r e]) s fun s' =>
      s' = { s with mem := s.mem.writeW (s.gpr r + BitVec.ofNat 64 e) (s.gpr t) } := by
  apply WP.of_runBlock
  simp only [runBlock_cons, exec_str_x he hw, runStep_some, runBlock_nil, Option.some.injEq,
    exists_eq_left']

theorem stSteps_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {n d a : Nat} {dst : Reg}
    (hdst : dst ≠ .x1) {c : Bool} (hc : s.gpr .x3 = (if c then BitVec.allOnes 64 else 0))
    (ha : a + 8 * n ≤ size) (ha8 : a % 8 = 0) (hd8 : d % 8 = 0) (hdn : d + 8 * n ≤ 32768)
    (hw : ∀ e, e + 8 ≤ 8 * n → InRegions s.wr (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 e) 8)
    (hd : Region.Disjoint ⟨off base a, 8 * n⟩ ⟨s.gpr dst + BitVec.ofNat 64 d, 8 * n⟩) : ∀ k, k ≤ n →
    WP isa (.block ((List.range k).flatMap (stStep n dst d a))) s fun s' =>
      (∀ j < k, s'.mem.readW (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 (8 * (n - 1 - j))) 64 =
        byteRev64 (word s.mem base (a + 8 * j) &&& (if c then BitVec.allOnes 64 else 0))) ∧
      KeepRegs [.x1] s s' ∧ Outside (s.gpr dst + BitVec.ofNat 64 d) (8 * (n - k)) (8 * k) s.mem s'.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), ⟨fun _ _ => rfl, rfl, rfl, rfl⟩,
      Outside.refl _ _ _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (stSteps_ok hs hdst hc ha ha8 hd8 hdn hw hd k (by omega)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    have hq₁ : s₁.gpr dst = s.gpr dst := k₁.gpr _ (by simpa using hdst)
    have hc₁ : s₁.gpr .x3 = (if c then BitVec.allOnes 64 else 0) := by rw [k₁.gpr _ (by decide), hc]
    have hq : s.gpr dst + BitVec.ofNat 64 (d + 8 * (n - 1 - k)) =
        s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 (8 * (n - 1 - k)) := (Offset.add_add _ _ _).symm
    have hword : word s₁.mem base (a + 8 * k) = word s.mem base (a + 8 * k) := by
      show s₁.mem.readW (base + BitVec.ofNat 64 (a + 8 * k)) 64 = s.mem.readW (base + BitVec.ofNat 64 (a + 8 * k)) 64
      rw [← Offset.add_add]
      exact readW_keep fun i hi => keep_of_disjoint' (O₁.mono (Nat.zero_le _) (by omega)) hd (by omega)
        (by omega) (by omega)
    rw [stStep, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (ld_ok hs₁ (d := a + 8 * k) (by omega) (by omega) .x1) fun s₂ ⟨l₂, k₂, _⟩ => ?_
    rw [show ([.logic .and .x .x1 .x1 .x3, .rev .x1 .x1, .str .x .x1 dst (d + 8 * (n - 1 - k))] :
      List Instr) = [.logic .and .x .x1 .x1 .x3, .rev .x1 .x1] ++ [.str .x .x1 dst (d + 8 * (n - 1 - k))]
      from rfl, WP.block_append_iff]
    refine WP.mono (andRev_ok s₂) fun s₃ ⟨v₃, k₃⟩ => ?_
    have hq₃ : s₃.gpr dst = s.gpr dst := by
      rw [k₃.gpr _ (by simpa using hdst), k₂.gpr _ (by simpa using hdst), hq₁]
    have hw₃ : InRegions s₃.wr (s₃.gpr dst + BitVec.ofNat 64 (d + 8 * (n - 1 - k))) 8 := by
      rw [k₃.wr, k₂.wr, k₁.wr, hq₃, hq]; exact hw _ (by omega)
    refine WP.mono (strReg_ok s₃ ⟨by omega, by omega⟩ hw₃) fun s₄ e₄ => ?_
    subst e₄
    rw [v₃, l₂, k₂.gpr _ (by decide), hc₁, hq₃, hq, k₃.mem, k₂.mem]
    have O₂ : Outside (s.gpr dst + BitVec.ofNat 64 d) (8 * (n - 1 - k)) 8 s₁.mem
        (s₁.mem.writeW (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 (8 * (n - 1 - k)))
          (byteRev64 (word s₁.mem base (a + 8 * k) &&& if c = true then BitVec.allOnes 64 else 0))) :=
      writeW_outside _ _ _ (by omega)
    refine ⟨fun j hj => ?_, k₁.trans (((Keeps.regs k₂).trans (Keeps.regs k₃)).trans
      ⟨fun _ _ => rfl, rfl, rfl, rfl⟩), (O₁.mono (by omega) (by omega)).trans (O₂.mono (by omega) (by omega))⟩
    rcases Nat.lt_or_ge j k with h | h
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide), e₁ j h]
    · obtain rfl : j = k := by omega
      rw [Mem.readW_writeW_self64, hword]

/-- The `8 n` bytes at `dst + d` are `[a]` big-endian if the mask `x3` is all
ones (`c`), zeros if it is zero. -/
theorem storeBE_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {n d a : Nat} {dst : Reg}
    (hdst : dst ≠ .x1) (c : Bool) (hc : s.gpr .x3 = (if c then BitVec.allOnes 64 else 0))
    (ha : a + 8 * n ≤ size) (ha8 : a % 8 = 0) (hd8 : d % 8 = 0) (hdn : d + 8 * n ≤ 32768)
    (hw : ∀ e, e + 8 ≤ 8 * n → InRegions s.wr (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 e) 8)
    (hd : Region.Disjoint ⟨off base a, 8 * n⟩ ⟨s.gpr dst + BitVec.ofNat 64 d, 8 * n⟩) :
    WP isa (.block (storeBE n dst d a)) s fun s' =>
      Spec.Ecdsa.bytesAt s'.mem (s.gpr dst + BitVec.ofNat 64 d) (8 * n) =
        (if c then Spec.Weierstrass.toBytes (8 * n) (wordsVal s.mem base a n)
          else List.replicate (8 * n) 0) ∧
      KeepRegs [.x1] s s' ∧ Outside (s.gpr dst + BitVec.ofNat 64 d) 0 (8 * n) s.mem s'.mem := by
  rw [storeBE_eq]
  refine WP.mono (stSteps_ok hs hdst hc ha ha8 hd8 hdn hw hd n (Nat.le_refl _)) fun s' ⟨e, k, O⟩ =>
    ⟨bytesAt_eq_toBytes _ _ _ _ c e, k, ?_⟩
  rw [Nat.sub_self, Nat.mul_zero] at O
  exact O

end VG.Proof.Weierstrass.AArch64
