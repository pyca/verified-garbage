import VerifiedGarbage.Proof.Weierstrass.X86.TCombSelect
import VerifiedGarbage.Proof.Weierstrass.X86.Ladder
import VerifiedGarbage.Proof.Weierstrass.X86.TCombLay
import VerifiedGarbage.Proof.Weierstrass.X86.Rcb3
import VerifiedGarbage.Proof.Weierstrass.CombW
import VerifiedGarbage.Proof.Weierstrass.Law3

/-! ## `TCombEntry` -/

section

/-!
# The fixed-base comb from tables in memory on x86 (32-bit)

What the comb (`TCombJ.lean`) needs of its tables and constants
(`TCombVals`): the selection's words are the entries' coordinates in
Montgomery form (`tbl_entry`).
-/

namespace VG.Proof.Weierstrass.X86

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass
open Spec.Weierstrass

/-- What the comb needs of its tables `tbl` (affine points, whose Montgomery
forms `tcombWords` are in memory) and constants: `J` tables of `H` entries,
entry `m` of table `j` the point `[(m + 1) 2^(wj)]G`, the start (in
Montgomery form) `[H Σ_{i<J} 2^(wi)]G`, and `R mod p` one. -/
structure TCombVals (K : TCombCfg) (C : Curve) (tbl : List (List (Nat × Nat))) : Prop where
  len : tbl.length = K.J
  lenH : ∀ j < K.J, (tbl.getD j []).length = K.H
  unit : UnitMod C.p (2 ^ (64 * K.M.n))
  one_lt : K.one < C.p
  one : toM C.p (2 ^ (64 * K.M.n)) K.one = 1
  entry : ∀ j < K.J, ∀ m < K.H, Rep C (Fin.ofNat C.p (combAt tbl j m).1)
    (Fin.ofNat C.p (combAt tbl j m).2) 1 (combPtW C K.w j (m + 1))
  start_lt : K.start.1 < C.p ∧ K.start.2 < C.p
  start : Rep C (toM C.p (2 ^ (64 * K.M.n)) K.start.1) (toM C.p (2 ^ (64 * K.M.n)) K.start.2) 1
    (mul (K.H * geomW K.w K.J) (G C))
  /-- The functions of the field arithmetic, of `n` words modulo `p`. -/
  fn : K.F.k = K.M.n ∧ K.F.m = C.p ∧ Mont.FnOk K.F

/-- `x ∈ l` for the comb's lists, through `toComb`. -/
macro "tcomb_mem" : tactic => `(tactic| first
  | list_mem
  | (simp only [List.mem_cons, List.mem_append, List.mem_singleton, true_or, or_true, combSlots,
      combWs, combRo, rcbW, rcbR, List.cons_append, List.nil_append, TCombCfg.toComb]))

/-- `a ≠ b` (or a conjunction of such, or `a ∉ [b, …]`) from `h`, the conjunction of `¬ x = y`
that a `Nodup` of the slots simplifies to, in either orientation: not `grind`, which takes a tenth
of a second for each. -/
macro "nd_ne " h:ident : tactic => `(tactic| (
  try simp only [ne_eq, List.mem_cons, List.not_mem_nil, or_false, not_or]
  repeat' apply And.intro
  all_goals first
    | nd_find $h:ident
    | simp only [ne_eq, $h:ident, not_false_eq_true]
    | exact Ne.symm (by simp only [ne_eq, $h:ident, not_false_eq_true])))

end VG.Proof.Weierstrass.X86

end

/-! ## `TCombInv` -/

section

/-! # State and memory invariants for the x86 comb -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
  VG.Proof.Mont.X86 VG.Proof.Mont
open Spec.Weierstrass

structure TCombFixed (K : TCombCfg) (C : Curve) (base : Addr) (size : Nat) (s₀ : State) (k : Nat)
    (T : Addr) (ws : List (BitVec 64)) : Prop where
  a : tmv C K.M.n base s₀ K.S.a = Fin.ofNat C.p C.a
  b : tmv C K.M.n base s₀ K.S.b3 = Fin.ofNat C.p C.b
  ro_lt : ∀ x ∈ combRo K.toComb, wordsVal s₀.mem base x K.M.n < C.p
  zero : wordsVal s₀.mem base K.zero K.M.n = 0
  bits : ∀ t < K.kbytes, s₀.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0
  k_lt : k < 2 ^ K.kbytes
  tsym : (s₀.mem.readW (off base K.ptr) 32).setWidth 64 = T
  tbl : TblMem s₀ T ws
  out : ∀ i < ws.length, ∀ b < 8, size ≤ ofs base (T + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b)
  /-- The tables are apart from the writable regions and the stack the calls use. -/
  apart : ∀ r ∈ s₀.wr ++ [below (s₀.gpr .esp) 20], Region.Disjoint ⟨T, 8 * ws.length⟩ r
  sp_lo : 20 ≤ (s₀.gpr .esp).toNat

/-- The loop's invariant at `esi = j`: `A` represents `[combEW w k J j]G`, and
the table of bits (all `w J` bytes) and the tables are where the digits and
the selection read them. -/
structure TCombInv (K : TCombCfg) (C : Curve) (base : Addr) (size k : Nat) (T : Addr)
    (ws : List (BitVec 64)) (s₀ s : State) (j : Nat) : Prop where
  scr : Scr s base size
  esi : s.gpr .esi = BitVec.ofNat 32 j
  keep : KeepRegs powClob s₀ s
  unch : Unch base (tcombW K) s₀.mem s.mem
  mod : ModOkW K.M size C.p s.mem base
  lt : ∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s.mem base x K.M.n < C.p
  rep : Rep C (tmv C K.M.n base s K.A.x) (tmv C K.M.n base s K.A.y) (tmv C K.M.n base s K.A.z)
    (mul (combEW K.w k K.J j) (G C))
  bits : ∀ t < K.w * K.J, s.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0
  tbl : TblMem s T ws
  tsym : (s.mem.readW (off base K.ptr) 32).setWidth 64 = T

/-- The tables survive code from a state that keeps the regions and `esp` of
`s₀` and uses 20 bytes of stack. -/
theorem TCombFixed.tblAt {K : TCombCfg} {C : Curve} {base : Addr} {size : Nat} {s₀ : State} {k : Nat}
    {T : Addr} {ws : List (BitVec 64)} (hF : TCombFixed K C base size s₀ k T ws) {s s' : State}
    (hwr : s.wr = s₀.wr) (hsp : s.gpr .esp = s₀.gpr .esp) (h : TblMem s T ws)
    (hrd : s'.rd ++ s'.wr = s.rd ++ s.wr) (hf : Frame (s.wr ++ [below (s.gpr .esp) 20]) s.mem s'.mem) :
    TblMem s' T ws :=
  h.of_frame hrd hf (by rw [hwr, hsp]; exact hF.apart)

theorem tcombW_mo {K : TCombCfg} {size m : Nat} {mem : Mem} {base : Addr} (hL : TCombLay K size)
    (hM : ModOkW K.M size m mem base) : ∀ w ∈ tcombW K, K.M.mo + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ K.M.mo := by
  intro w hw
  simp only [tcombW, combWx, combW, List.mem_append, List.mem_map, List.mem_cons,
    List.not_mem_nil, or_false] at hw
  rcases hw with ((⟨y, hy, rfl⟩ | rfl) | rfl | rfl) | rfl
  · have := hL.comb.lay.mo y (combWs_slots _ y hy); dsimp only [TCombCfg.toComb] at this ⊢; omega
  · have := hM.sep; dsimp only [TCombCfg.toComb] at this ⊢; omega
  · exact .inl hL.wmo
  · have := hM.mo; have := hL.sz; exact .inl (by dsimp only [Mont.outW]; omega)
  · have := hL.bits_sl K.M.mo (List.mem_cons_self ..); dsimp only; omega

theorem tcombW_ro {K : TCombCfg} {size : Nat} (hL : TCombLay K size) {x : Nat}
    (hx : x ∈ combRo K.toComb) : ∀ w ∈ tcombW K, x + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x := by
  intro w hw
  have hxs := combRo_slots x hx
  simp only [tcombW, combWx, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with (hw | rfl | rfl) | rfl
  · exact combW_ro hL.comb hx w hw
  · exact .inl (hL.wsl x hxs)
  · have h1 := hL.comb.lay.le x hxs; have := hL.sz; dsimp only [TCombCfg.toComb] at h1
    exact .inl (by dsimp only [Mont.outW]; omega)
  · have := hL.bits_sl x (List.mem_cons_of_mem _ hxs); dsimp only; omega

theorem combW_bits {K : TCombCfg} {size : Nat} (hL : TCombLay K size) {t : Nat} (ht : t < K.w * K.J) :
    ∀ w ∈ combWx K, K.bits + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ K.bits + t := by
  have : K.w * K.J ≤ K.kbytes + 4 * K.zw := by unfold TCombCfg.zw; have := hL.kbytes; omega
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · have := hL.bits_w w hw; omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · rcases hL.wk_bits with h | h
      · exact .inl (by omega)
      · exact .inr (by omega)
    · have := hL.bits; have := hL.sz; exact .inl (by dsimp only [Mont.outW]; omega)

theorem combW_ptr {K : TCombCfg} {size : Nat} (hL : TCombLay K size) :
    ∀ w ∈ combWx K, K.ptr + 4 ≤ w.1 ∨ w.1 + w.2 ≤ K.ptr := by
  intro w hw
  simp only [combWx, combW, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil,
    or_false] at hw
  rcases hw with (⟨x, hx, rfl⟩ | rfl) | rfl | rfl
  · exact hL.ptr_sl x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (combWs_slots _ x hx)))
  · exact hL.ptr_sl K.M.tmp (by simp)
  · exact .inl hL.ptr_wk
  · have := hL.ptr_le; have := hL.sz; exact .inl (by dsimp only [Mont.outW]; omega)

theorem unch_read32 {base : Addr} {W : List (Nat × Nat)} {m m' : Mem} (h : Unch base W m m')
    {d : Nat} (hd : d + 4 ≤ 2 ^ 64) (hW : ∀ w ∈ W, d + 4 ≤ w.1 ∨ w.1 + w.2 ≤ d) :
    m'.readW (off base d) 32 = m.readW (off base d) 32 := by
  apply Mem.readW_congr
  intro i hi
  rw [off, Offset.add_add]
  exact h.byte (fun w hw => by have := hW w hw; omega) (by omega)

theorem copyWords_ok {s : State} {base : Addr} {size n o a : Nat} (hs : Scr s base size)
    (ho : o + 8 * n ≤ size) (ha : a + 8 * n ≤ size) (hsep : o ≤ a ∨ a + 8 * n ≤ o) :
    WP isa (.block (copy (2 * n) o a)) s fun t =>
      wordsVal t.mem base o n = wordsVal s.mem base a n ∧ Keeps [.eax] s t ∧
      Outside base o (8 * n) s.mem t.mem := by
  refine WP.mono (copy_ok (2 * n) hs (by omega) (by omega) (by omega)) fun t ⟨v, k, O⟩ =>
    ⟨by simpa only [wordsVal_eq_val32] using v, k, by simpa only [show 4 * (2 * n) = 8 * n by omega] using O⟩

/-- `o = a`, a point, for `o`'s slots apart from each other and from `a`'s. -/
theorem copyPt_ok {s : State} {base : Addr} {size n : Nat} (hs : Scr s base size) {o a : Pt}
    (hle : ∀ x ∈ [o.x, o.y, o.z, a.x, a.y, a.z], x + 8 * n ≤ size)
    (hap : ∀ x ∈ [o.x, o.y, o.z], ∀ y ∈ [o.x, o.y, o.z, a.x, a.y, a.z], x ≠ y →
      x + 8 * n ≤ y ∨ y + 8 * n ≤ x)
    (hne : ∀ x ∈ [o.x, o.y, o.z], x ∉ [a.x, a.y, a.z]) (ho : o.x ≠ o.y ∧ o.x ≠ o.z ∧ o.y ≠ o.z) :
    WP isa (.block (copyPt n o a)) s fun t =>
      wordsVal t.mem base o.x n = wordsVal s.mem base a.x n ∧
      wordsVal t.mem base o.y n = wordsVal s.mem base a.y n ∧
      wordsVal t.mem base o.z n = wordsVal s.mem base a.z n ∧
      KeepRegs [.eax] s t ∧ Unch base [(o.x, 8 * n), (o.y, 8 * n), (o.z, 8 * n)] s.mem t.mem := by
  have hn := hs.nowrap
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, not_or] at hle hap hne
  obtain ⟨⟨xa, xb, xc⟩, ⟨ya, yb, yc⟩, ⟨za, zb, zc⟩⟩ := hne
  have pxy := hap.1.2.1 ho.1
  have pxz := hap.1.2.2.1 ho.2.1
  have pyz := hap.2.1.2.2.1 ho.2.2
  have pxa := hap.1.2.2.2.1 xa
  have pxb := hap.1.2.2.2.2.1 xb
  have pxc := hap.1.2.2.2.2.2 xc
  have pyb := hap.2.1.2.2.2.2.1 yb
  have pyc := hap.2.1.2.2.2.2.2 yc
  have pzc := hap.2.2.2.2.2.2.2 zc
  rw [copyPt, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (copyWords_ok hs (o := o.x) (a := a.x) hle.1 hle.2.2.2.1 (by omega)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  refine WP.mono (copyWords_ok hs₁ (o := o.y) (a := a.y) hle.2.1 hle.2.2.2.2.1 (by omega)) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  refine WP.mono (copyWords_ok hs₂ (o := o.z) (a := a.z) hle.2.2.1 hle.2.2.2.2.2 (by omega))
    fun t ⟨e₃, k₃, O₃⟩ => ⟨?_, ?_, ?_, (k₁.trans k₂).trans k₃, ?_⟩
  · rw [O₃.wordsVal (by omega) (by omega), O₂.wordsVal (by omega) (by omega), e₁]
  · rw [O₃.wordsVal (by omega) (by omega), e₂, O₁.wordsVal (by omega) (by omega)]
  · rw [e₃, O₂.wordsVal (by omega) (by omega), O₁.wordsVal (by omega) (by omega)]
  · exact (O₁.unch.trans (O₂.unch.trans O₃.unch)).mono fun w hw => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
      rcases hw with h | h | h <;> simp [h]

theorem clob_powClob : ∀ r ∈ clob, r ∈ powClob := fun _ h => List.mem_cons_of_mem _ h


end VG.Proof.Weierstrass.X86

end

/-! ## `TCombInit` -/

section

namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
  VG.Proof.Mont.X86 VG.Proof.Mont
open Spec.Weierstrass

theorem tcombW_ptr {K : TCombCfg} {size : Nat} (hL : TCombLay K size) :
    ∀ w ∈ combWx K ++ [(K.bits + K.kbytes, 4 * K.zw)], K.ptr + 4 ≤ w.1 ∨ w.1 + w.2 ≤ K.ptr := by
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · exact combW_ptr hL w hw
  · simp only [List.mem_singleton] at hw; subst hw
    have := hL.ptr_bits; dsimp only; omega

/-- Zero stored to the `m` words at `o`, from `rax = 0`. -/
theorem zstores_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (hz : s.gpr .eax = 0)
    {o : Nat} : ∀ m, o + 4 * m ≤ size →
    WP isa (.block ((List.range m).map fun i => .store (sc (o + 4 * i)) .eax)) s fun s' =>
      KeepRegs [] s s' ∧ Outside base o (4 * m) s.mem s'.mem ∧
        ∀ d < 4 * m, s'.mem (off base (o + d)) = 0
  | 0, _ => WP.block_nil ⟨⟨fun _ _ => rfl, rfl, rfl⟩, Outside.refl _ _ _ _,
      fun d hd => absurd hd (by omega)⟩
  | m + 1, hm => by
    have hn := hs.nowrap
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (zstores_ok hs hz m (by omega)) fun s₁ ⟨k₁, O₁, z₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by simp)
    have hrax : s₁.gpr .eax = 0 := (k₁.gpr _ (by simp)).trans hz
    simp only [List.map_cons, List.map_nil]
    refine wp_storeS (hs₁.ea (d := o + 4 * m) (by omega)) (hs₁.write (d := o + 4 * m) (n := 4) (by omega))
      fun s₂ u₂ => WP.block_nil ?_
    have Ow : Outside base (o + 4 * m) 4 s₁.mem s₂.mem := by
      rw [u₂.mem]; exact writeW32_outside _ _ _ (by omega)
    refine ⟨k₁.trans (u₂.keeps _), fun x hx => (Ow x (by omega)).trans (O₁ x (by omega)),
      fun d hd => ?_⟩
    by_cases hd' : d < 4 * m
    · rw [Ow _ (by rw [ofs_off0 base (by omega)]; omega)]; exact z₁ d hd'
    · have e : off base (o + d) - off base (o + 4 * m) = BitVec.ofNat 64 (d - 4 * m) := by
        simp only [off]; rw [show o + d = o + 4 * m + (d - 4 * m) by omega, Offset.add_ofNat_add_sub]
      rw [u₂.mem, hrax]
      simp only [Mem.writeW, Mem.write, e, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show d - 4 * m < 2 ^ 64 by omega), show d - 4 * m < 32 / 8 by omega,
        ↓reduceIte]
      simp

theorem zeroEax_ok (s : State) :
    WP isa (.block [.mov .eax (.imm 0)]) s fun t => t.gpr .eax = 0 ∧ CKeeps [.eax] s t :=
  wp_movS rfl fun _t u _ => WP.block_nil ⟨u.gpr, u.keeps.1, u.mem, u.keeps.2⟩

theorem movEsi_ok (s : State) {j : Nat} (_hj : j < 2^31) :
    WP isa (.block [.mov .esi (.imm (BitVec.ofNat 32 j))]) s fun t =>
      t.gpr .esi = BitVec.ofNat 32 j ∧ CKeeps [.esi] s t :=
  wp_movS rfl fun _t u _ => WP.block_nil ⟨u.gpr, u.keeps.1, u.mem, u.keeps.2⟩

end VG.Proof.Weierstrass.X86

end

/-! ## `TComb` -/

section

/-! # Correctness of the 32-bit x86 fixed-base comb -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
  VG.Proof.Mont.X86 VG.Proof.Mont
open Spec.Weierstrass

/-- Save the table address in the scratch header before initializing the comb. -/
theorem savePtr_ok {K : TCombCfg} {s : State} {base : Addr} {size : Nat}
    (hs : Scr s base size) (hL : TCombLay K size) :
    WP isa (.block [.store (sc K.ptr) .eax]) s fun t =>
      t.mem.readW (off base K.ptr) 32 = s.gpr .eax ∧ Keeps [] s t ∧
        Outside base K.ptr 4 s.mem t.mem := by
  have hn := hs.nowrap
  have hp := hL.ptr_le
  refine wp_storeS (hs.ea (by omega)) (hs.write (n := 4) hp) fun t u => WP.block_nil ?_
  refine ⟨?_, u.keeps _, ?_⟩
  · rw [u.mem, Mem.readW_writeW_self32]
  · rw [u.mem]; exact writeW32_outside _ _ _ (by omega)

end VG.Proof.Weierstrass.X86

end
