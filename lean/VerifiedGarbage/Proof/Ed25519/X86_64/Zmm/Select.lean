import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.CombSelect
import VerifiedGarbage.Proof.Ed25519.X86_64.Zmm.Half
import VerifiedGarbage.Proof.Framework.X86_64.ZVecKeep

/-!
# The `zmm` comb: the selection

`zselect` keeps each 32-byte piece of each entry of a table, loaded once into
both halves of `zmm10`, under the mask of each half's magnitude (`r8` for half
0, `r10` for half 1) in `zmm11–zmm13`, as `vselect` does in one half: half `h`
then holds the words of the entry for its magnitude, or zero (`accQ`), with
the identity's `1`s or'd in for a zero magnitude, and `zmm14` holds the row
`ZK2`.
-/

namespace VG.Proof.Ed25519.X86_64.Zmm

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.Ed25519.X86_64.Zmm VG.Proof.Ed25519.X86_64
open VG.Impl.X25519.X86_64 (sc)
open VG.Impl.X25519.X86_64.Ifma (y v zero)
open VG.Proof.Ed25519.X86_64.Ifma (accQ accQ_step)
open VG.Proof.Poly1305.X86_64.Avx2 (xr qw qword_and qword_or qword_app0 qword_app1 qword256_eq)

/-- Quadword `k` (of four) of half `h` of `zmm r`. -/
def zq (s : State) (r : XReg) (h k : Nat) : BitVec 64 := qword (s.zlane r (2 * h + k / 2)) (k % 2)

/-- What a block keeps of the rest of the state: the general-purpose registers but `rs`, the
memory, the regions and the statics, and the vector registers but those of `xs`. -/
structure ZVKeep (rs : List Reg) (xs : XReg → Prop) (s t : State) : Prop where
  gpr : ∀ r, r ∉ rs → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  zl : ∀ r, ¬ xs r → ∀ i < 4, t.zlane r i = s.zlane r i
  syms : t.syms = s.syms

theorem ZVKeep.refl (rs : List Reg) (xs : XReg → Prop) (s : State) : ZVKeep rs xs s s :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ _ _ => rfl, rfl⟩

theorem ZVKeep.trans {rs : List Reg} {xs : XReg → Prop} {s₁ s₂ s₃ : State} (h₁ : ZVKeep rs xs s₁ s₂)
    (h₂ : ZVKeep rs xs s₂ s₃) : ZVKeep rs xs s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd,
    h₂.wr.trans h₁.wr, fun r hr i hi => (h₂.zl r hr i hi).trans (h₁.zl r hr i hi), h₂.syms.trans h₁.syms⟩

theorem ZVKeep.mono {rs rs' : List Reg} {xs xs' : XReg → Prop} {s t : State} (h : ZVKeep rs xs s t)
    (hr : ∀ r ∈ rs, r ∈ rs') (hx : ∀ r, xs r → xs' r) : ZVKeep rs' xs' s t :=
  ⟨fun r h' => h.gpr r fun h'' => h' (hr r h''), h.mem, h.rd, h.wr,
    fun r h' => h.zl r fun h'' => h' (hx r h''), h.syms⟩

theorem zlane_of {s t : State} (hx : t.xmm = s.xmm) (hy : t.ymmHi = s.ymmHi) (hz : t.zmmHi = s.zmmHi)
    (r : XReg) (i : Nat) : t.zlane r i = s.zlane r i := by
  simp only [State.zlane, State.lane, hx, hy, hz]

theorem zlane_setV256 (s : State) (d r : XReg) (lo hi : BitVec 128) {i : Nat} (hi4 : i < 4) :
    (s.setV .l256 d lo hi).zlane r i = if r = d then (if i = 0 then lo else if i = 1 then hi else 0)
      else s.zlane r i := by
  simp only [State.zlane, State.lane, State.setV]
  by_cases h : r = d
  · subst h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> simp
  · simp [h]

/-! ## The masks -/

/-- `rcx` all ones if `r10 = a` is `v`, else zero. -/
theorem eqMaskB_ok (s : State) {v a : Nat} (hv : v < 2 ^ 31) (ha : a < 2 ^ 31)
    (h10 : s.gpr .r10 = BitVec.ofNat 64 a) :
    WP isa (.block (eqMaskB v)) s fun t => t.gpr .rcx = cmask (decide (a = v)) ∧
      Proof.X25519.X86_64.Keeps [.rcx] s t ∧ t.syms = s.syms := by
  erun [eqMaskB, imm32_ofNat hv, h10]
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl⟩, rfl⟩
  · have h1 : (BitVec.signExtend 64 (1 : BitVec 32)).toNat = 1 := by decide
    have hx : decide ((BitVec.ofNat 64 v ^^^ BitVec.ofNat 64 a).toNat < 1) = decide (a = v) := by
      refine decide_eq_decide.mpr ⟨fun h => ?_, fun h => ?_⟩
      · have e0 : BitVec.ofNat 64 v ^^^ BitVec.ofNat 64 a = 0 :=
          BitVec.eq_of_toNat_eq ((Nat.lt_one_iff.mp h).trans rfl)
        have e := BitVec.xor_eq_zero_iff.mp e0
        have := congrArg BitVec.toNat e
        simp only [BitVec.toNat_ofNat] at this
        omega
      · subst h; rw [BitVec.xor_self, BitVec.toNat_zero]; decide
    rw [BitVec.sub_self, h1, hx]
    cases decide (a = v) <;> decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- A scalar block's facts, with the vector registers kept. -/
theorem zscal {c : Prog isa} (hc : scalCode c = true) {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun t => Q t ∧ ∀ r i, t.zlane r i = s.zlane r i :=
  WP.mono (WP.zvecKeep hc h) fun _ ⟨q, x, y, z⟩ => ⟨q, zlane_of x y z⟩

/-- `vmovq` and `vpbroadcastq`: a general-purpose register in every quadword of `zmm d`. -/
theorem zlane_dup (s : State) (d : XReg) (g : Reg) (r : XReg) {i : Nat} (hi : i < 4) :
    ((ZOp.vpbroadcastq d d).exec ((VOp.vmovq d g).exec s)).zlane r i =
      if r = d then s.gpr g ++ s.gpr g else s.zlane r i := by
  rw [zlane_vpbroadcastq _ _ _ _ hi]
  split
  · subst_vars; simp only [VOp.exec, State.setV, ite_true, qword_app0]
  · simp only [VOp.exec, State.zlane_setV128 _ _ _ _ _ hi]; rw [ite_eq_right (by assumption)]

/-- `zlo d a b`: the low halves of `zmm a` and `zmm b`. -/
theorem zlane_zlo (s : State) (d a b : Nat) (r : XReg) {i : Nat} (hi : i < 4) :
    ((ZOp.vshufi32x4 (y d) (y a) (y b) 0x44).exec s).zlane r i =
      if r = y d then (if i < 2 then s.zlane (y a) i else s.zlane (y b) (i - 2)) else s.zlane r i := by
  rw [zlane_vshufi32x4 _ _ _ _ _ _ hi]
  split
  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl
  · rfl

theorem combEqMask_scal (m : Nat) : scalCode (.block (combEqMask m)) = true := rfl
theorem eqMaskB_scal (m : Nat) : scalCode (.block (eqMaskB m)) = true := rfl

/-- Both masks: `zmm15` all ones in half 0 if `r8 = a` is `m`, and in half 1 if `r10 = b` is. -/
theorem zmasks_ok (s : State) {a b m : Nat} (hm : m < 2 ^ 31) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 a) (h10 : s.gpr .r10 = BitVec.ofNat 64 b) :
    WP isa (.block (combEqMask m ++ ([.vop (.vmovq (y 15) .rcx), .zop (.vpbroadcastq (y 15) (y 15))] : List Instr) ++
      eqMaskB m ++ ([.vop (.vmovq (y 14) .rcx), .zop (.vpbroadcastq (y 14) (y 14)), zlo 15 15 14] : List Instr))) s
      fun t => (∀ i < 4, t.zlane (xr 15) i = (cmask (decide ((if i < 2 then a else b) = m)) ++
          cmask (decide ((if i < 2 then a else b) = m)))) ∧
        ZVKeep [.rcx] (fun r => r = xr 14 ∨ r = xr 15) s t := by
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (zscal (combEqMask_scal m) (combEqMask_ok s hm ha h8)) fun s₁ ⟨⟨c₁, k₁, _, y₁⟩, z₁⟩ => ?_
  let s₂ := (ZOp.vpbroadcastq (y 15) (y 15)).exec ((VOp.vmovq (y 15) .rcx).exec s₁)
  refine WP.of_runBlock ⟨s₂, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec]; rfl, ?_⟩
  have l₂ : ∀ r, ∀ i < 4, s₂.zlane r i = if r = y 15 then cmask (decide (a = m)) ++ cmask (decide (a = m))
      else s₁.zlane r i := fun r i hi => by rw [zlane_dup _ _ _ _ hi, c₁]
  refine WP.mono (zscal (eqMaskB_scal m) (eqMaskB_ok s₂ hm hb (by
    show s₁.gpr .r10 = _; rw [k₁.1 _ (by decide), h10]))) fun s₃ ⟨⟨c₃, k₃, y₃⟩, z₃⟩ => ?_
  let s₄ := (ZOp.vshufi32x4 (y 15) (y 15) (y 14) 0x44).exec
    ((ZOp.vpbroadcastq (y 14) (y 14)).exec ((VOp.vmovq (y 14) .rcx).exec s₃))
  refine WP.of_runBlock ⟨s₄, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec, zlo]; rfl, ?_⟩
  have l₄ : ∀ r, ∀ i < 4, s₄.zlane r i = if r = y 15 then
      (if i < 2 then cmask (decide (a = m)) ++ cmask (decide (a = m))
        else cmask (decide (b = m)) ++ cmask (decide (b = m)))
      else if r = y 14 then cmask (decide (b = m)) ++ cmask (decide (b = m)) else s₁.zlane r i := by
    intro r i hi
    simp only [s₄, zlane_zlo _ _ _ _ _ hi, zlane_dup _ _ _ _ hi, zlane_dup _ _ _ _ (show i - 2 < 4 by omega),
      z₃, l₂ _ _ hi, c₃]
    have n1514 : y 15 ≠ y 14 := by decide
    by_cases h15 : r = y 15
    · subst h15; split <;> simp
    · by_cases h14 : r = y 14
      · subst h14; simp [n1514.symm]
      · simp [h15, h14]
  refine ⟨fun i hi => ?_, ⟨fun r hr => ?_, ?_, ?_, ?_, fun r hr i hi => ?_, ?_⟩⟩
  · rw [show xr 15 = y 15 from rfl, l₄ _ _ hi, ite_eq_left rfl]
    split <;> rfl
  · show s₃.gpr r = s.gpr r
    rw [k₃.1 r hr]; show s₁.gpr r = _; exact k₁.1 r hr
  · show s₃.mem = s.mem; rw [k₃.2.1]; show s₁.mem = _; exact k₁.2.1
  · show s₃.rd = s.rd; rw [k₃.2.2.1]; show s₁.rd = _; exact k₁.2.2.1
  · show s₃.wr = s.wr; rw [k₃.2.2.2]; show s₁.wr = _; exact k₁.2.2.2
  · simp only [not_or, show xr 14 = y 14 from rfl, show xr 15 = y 15 from rfl] at hr
    rw [l₄ _ _ hi, ite_eq_right hr.2, ite_eq_right hr.1, z₁]
  · show s₃.syms = s.syms; rw [y₃]; show s₁.syms = _; exact y₁

/-! ## The pieces -/

theorem qword_load (m : Mem) (a : Addr) {k : Nat} (hk : k < 4) :
    qword ((m.readW a 256).extractLsb' (128 * (k / 2)) 128) (k % 2) = m.readW (a + BitVec.ofNat 64 (8 * k)) 64 := by
  rw [← qword256_eq, qword256, show 64 * k = 8 * (8 * k) by omega]
  exact readW_extract _ _ (k := 8 * k) (n := 8) (by omega)

/-- Piece `c` of the 32 bytes at `rdx + d`, in both halves, kept under the masks `zmm15` in
`zmm (11 + c)`. -/
theorem zselLoad_ok (s : State) {X : Addr} (hx : s.gpr .rdx = X) {d c : Nat} (hc : c < 3)
    (hr : InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 d) 32) :
    WP isa (.block [.vmovdquLoad .l256 (y 10) (combTblAt d), zlo 10 10 10,
        .zop (.zbin .vpandq (y 10) (y 10) (y 15)), .zop (.zbin .vporq (y (11 + c)) (y (11 + c)) (y 10))]) s
      fun t => (∀ h < 2, ∀ k < 4, zq t (xr (11 + c)) h k = zq s (xr (11 + c)) h k |||
          (s.mem.readW (X + BitVec.ofNat 64 d + BitVec.ofNat 64 (8 * k)) 64 &&& zq s (xr 15) h k)) ∧
        ZVKeep [] (fun r => r = xr 10 ∨ r = xr (11 + c)) s t := by
  let w := s.mem.readW (X + BitVec.ofNat 64 d) 256
  let s₁ := s.setV .l256 (y 10) (w.extractLsb' 0 128) (w.extractLsb' 128 128)
  let s₂ := (ZOp.vshufi32x4 (y 10) (y 10) (y 10) 0x44).exec s₁
  let s₃ := (ZOp.zbin .vpandq (y 10) (y 10) (y 15)).exec s₂
  let s₄ := (ZOp.zbin .vporq (y (11 + c)) (y (11 + c)) (y 10)).exec s₃
  have h1015 : y 10 ≠ y 15 := by decide
  have hc10 : y (11 + c) ≠ y 10 := by rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;> decide
  have hc15 : y (11 + c) ≠ y 15 := by rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;> decide
  have l₃ : ∀ i < 4, s₃.zlane (y 10) i = w.extractLsb' (128 * (i % 2)) 128 &&& s.zlane (y 15) i := by
    intro i hi
    simp only [s₃, s₂, s₁, zlane_zbin _ _ _ _ _ _ hi, ite_true, zlane_zlo _ _ _ _ _ hi,
      zlane_setV256 _ _ _ _ _ hi, zlane_setV256 _ _ _ _ _ (show i - 2 < 4 by omega), ite_eq_right h1015.symm,
      ZBinOp.sse, XBinOp.eval]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl
  have l₄ : ∀ r, ∀ i < 4, s₄.zlane r i = if r = y (11 + c) then
      s.zlane (y (11 + c)) i ||| (w.extractLsb' (128 * (i % 2)) 128 &&& s.zlane (y 15) i)
      else if r = y 10 then w.extractLsb' (128 * (i % 2)) 128 &&& s.zlane (y 15) i else s.zlane r i := by
    intro r i hi
    simp only [s₄, zlane_zbin _ _ _ _ _ _ hi]
    split
    · next e =>
      subst e
      rw [l₃ i hi]
      simp only [s₃, s₂, s₁, zlane_zbin _ _ _ _ _ _ hi, zlane_zlo _ _ _ _ _ hi, zlane_setV256 _ _ _ _ _ hi,
        hc10, ite_false, ZBinOp.sse, XBinOp.eval]
    · next e =>
      by_cases e' : r = y 10
      · subst e'; rw [l₃ i hi, ite_eq_left rfl]
      · simp only [s₃, s₂, s₁, zlane_zbin _ _ _ _ _ _ hi, zlane_zlo _ _ _ _ _ hi, zlane_setV256 _ _ _ _ _ hi,
          e', ite_false]
  have hea : s.ea (combTblAt d) = X + BitVec.ofNat 64 d := by rw [ea_combTblAt, hx]
  refine WP.of_runBlock ⟨s₄, ?_, fun h hh k hk => ?_, ⟨fun _ _ => rfl, rfl, rfl, rfl, fun r hr i hi => ?_, rfl⟩⟩
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec, hea, State.load256, hr, ite_true,
      Option.map_some, zlo]
    rfl
  · simp only [zq]
    rw [show xr (11 + c) = y (11 + c) by rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;> rfl,
      l₄ _ _ (by omega), ite_eq_left rfl, qword_or, qword_and, show (2 * h + k / 2) % 2 = k / 2 by omega,
      qword_load _ _ hk]
    rfl
  · simp only [not_or, show xr 10 = y 10 from rfl] at hr
    rw [l₄ _ _ hi, ite_eq_right (by
        rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;> exact hr.2),
      ite_eq_right hr.1]

/-- The magnitude of half `h`. -/
abbrev hmag (a b h : Nat) : Nat := if h = 0 then a else b

/-- The pieces `c < n` of entry `m` of the table at `rdx = X` kept under the masks `zmm15`. -/
theorem zselLoads_ok {m : Nat} {X : Addr} : ∀ n ≤ 3, ∀ (s : State), s.gpr .rdx = X →
    (∀ c < 3, InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 (combEntryBytes * (m - 1) + 32 * c)) 32) →
    WP isa (.block ((List.range n).flatMap fun c =>
        [.vmovdquLoad .l256 (y 10) (combTblAt (combEntryBytes * (m - 1) + 32 * c)), zlo 10 10 10,
          .zop (.zbin .vpandq (y 10) (y 10) (y 15)), .zop (.zbin .vporq (y (11 + c)) (y (11 + c)) (y 10))])) s
      fun t => (∀ h < 2, ∀ c < 3, ∀ k < 4, zq t (xr (11 + c)) h k = if c < n then zq s (xr (11 + c)) h k |||
          (s.mem.readW (X + BitVec.ofNat 64 (combEntryBytes * (m - 1) + 32 * c) + BitVec.ofNat 64 (8 * k)) 64 &&&
            zq s (xr 15) h k)
        else zq s (xr (11 + c)) h k) ∧
      ZVKeep [] (fun r => r = xr 10 ∨ ∃ c < 3, r = xr (11 + c)) s t
  | 0, _, s, _, _ => WP.block_nil ⟨fun h _ c _ k _ => by simp, ZVKeep.refl _ _ _⟩
  | n + 1, hn, s, hx, hr => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (zselLoads_ok n (by omega) s hx hr) fun s₁ ⟨a₁, k₁⟩ => ?_
    have h15 : ∀ h < 2, ∀ k < 4, zq s₁ (xr 15) h k = zq s (xr 15) h k := fun h hh k hk => by
      simp only [zq]
      rw [k₁.zl _ (by
        rintro (h | ⟨c, hc, h⟩)
        · exact absurd h (by decide)
        · rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;> exact absurd h (by decide)) _
        (by omega)]
    refine WP.mono (zselLoad_ok s₁ ((k₁.gpr _ List.not_mem_nil).trans hx) (c := n) (by omega)
      (by rw [k₁.rd, k₁.wr]; exact hr n (by omega))) fun t ⟨a₂, k₂⟩ => ⟨fun h hh c hc k hk => ?_, ?_⟩
    · by_cases hcn : c = n
      · subst hcn
        rw [a₂ h hh k hk, a₁ h hh c hc k hk, h15 h hh k hk, k₁.mem]
        simp only [Nat.lt_irrefl, ↓reduceIte, Nat.lt_succ_self]
      · have hz : ∀ i < 4, t.zlane (xr (11 + c)) i = s₁.zlane (xr (11 + c)) i := k₂.zl _ (by
          rintro (h | h)
          · rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;> exact absurd h (by decide)
          · exact hcn (by
              rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;>
              rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2) with rfl | rfl | rfl <;>
              first | rfl | exact absurd h (by decide)))
        rw [show zq t (xr (11 + c)) h k = zq s₁ (xr (11 + c)) h k by simp only [zq]; rw [hz _ (by omega)],
          a₁ h hh c hc k hk]
        by_cases hlt : c < n
        · simp only [hlt, show c < n + 1 by omega, ↓reduceIte]
        · simp only [hlt, show ¬ c < n + 1 by omega, ↓reduceIte]
    · exact k₁.trans (k₂.mono (fun _ h => h) fun r h => by
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr ⟨n, by omega, h⟩)

/-- The registers the selection writes. -/
abbrev zselRegs (r : XReg) : Prop := r = xr 10 ∨ (∃ c < 3, r = xr (11 + c)) ∨ r = xr 14 ∨ r = xr 15

/-- Entry `m` of the table at `rdx = X` kept in the accumulators of each half under the mask of
its magnitude, `r8 = a` or `r10 = b`. -/
theorem zselEntry_ok {s : State} {X : Addr} {a b m : Nat} (hm1 : 1 ≤ m) (hm : m < 2 ^ 31)
    (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) (h8 : s.gpr .r8 = BitVec.ofNat 64 a)
    (h10 : s.gpr .r10 = BitVec.ofNat 64 b) (hx : s.gpr .rdx = X)
    (hr : ∀ c < 3, InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 (combEntryBytes * (m - 1) + 32 * c)) 32)
    (hacc : ∀ h < 2, ∀ c < 3, ∀ k < 4, zq s (xr (11 + c)) h k = accQ s.mem X (hmag a b h) (m - 1) c k) :
    WP isa (.block (zselEntry m)) s fun t =>
      (∀ h < 2, ∀ c < 3, ∀ k < 4, zq t (xr (11 + c)) h k = accQ s.mem X (hmag a b h) m c k) ∧
      ZVKeep [.rcx] zselRegs s t := by
  rw [zselEntry, WP.block_append_iff]
  refine WP.mono (zmasks_ok s hm ha hb h8 h10) fun s₁ ⟨x₁, k₁⟩ => ?_
  refine WP.mono (zselLoads_ok (X := X) 3 (Nat.le_refl _) s₁ (by rw [k₁.gpr _ (by decide), hx]) (by
      rw [k₁.rd, k₁.wr]; exact hr)) fun t ⟨a₃, k₃⟩ => ⟨fun h hh c hc k hk => ?_, ?_⟩
  · have hne : ∀ i < 4, s₁.zlane (xr (11 + c)) i = s.zlane (xr (11 + c)) i := k₁.zl _ (by
      rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;> decide)
    have hm15 : zq s₁ (xr 15) h k = cmask (decide (hmag a b h = m)) := by
      simp only [zq]
      rw [x₁ _ (by omega)]
      rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl <;>
        rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> simp [hmag]
    rw [a₃ h hh c hc k hk, ite_eq_left_of_eq_true _ _ (eq_true hc), hm15, k₁.mem,
      show zq s₁ (xr (11 + c)) h k = zq s (xr (11 + c)) h k by simp only [zq]; rw [hne _ (by omega)],
      hacc h hh c hc k hk]
    exact accQ_step _ _ _ _ _ _ hm1
  · refine k₁.mono (fun _ h => h) (fun r h => ?_) |>.trans (k₃.mono (fun _ h => by simp at h) fun r h => ?_)
    · rcases h with h | h <;> simp [zselRegs, h]
    · rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)

/-- The entries `1 … n` of the table at `rdx = X` kept in the cleared accumulators under the
masks of the halves' magnitudes. -/
theorem zselEntries_ok {X : Addr} {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    ∀ n, n < 2 ^ 31 → ∀ (s : State), s.gpr .r8 = BitVec.ofNat 64 a → s.gpr .r10 = BitVec.ofNat 64 b →
    s.gpr .rdx = X →
    (∀ e < n, ∀ c < 3, InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 (combEntryBytes * e + 32 * c)) 32) →
    (∀ h < 2, ∀ c < 3, ∀ k < 4, zq s (xr (11 + c)) h k = 0) →
    WP isa (.block ((List.range n).flatMap fun m => zselEntry (m + 1))) s fun t =>
      (∀ h < 2, ∀ c < 3, ∀ k < 4, zq t (xr (11 + c)) h k = accQ s.mem X (hmag a b h) n c k) ∧
      ZVKeep [.rcx] zselRegs s t
  | 0, _, s, _, _, _, _, h0 => WP.block_nil ⟨fun h hh c hc k hk => by
      rw [h0 h hh c hc k hk, accQ, ite_eq_right_of_eq_false _ _ (eq_false (by omega))], ZVKeep.refl _ _ _⟩
  | n + 1, hn, s, h8, h10, hx, hr, h0 => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (zselEntries_ok ha hb n (by omega) s h8 h10 hx (fun e he => hr e (by omega)) h0)
      fun s₁ ⟨a₁, k₁⟩ => ?_
    refine WP.mono (zselEntry_ok (X := X) (m := n + 1) (by omega) hn ha hb
      (by rw [k₁.gpr _ (by decide), h8]) (by rw [k₁.gpr _ (by decide), h10]) (by rw [k₁.gpr _ (by decide), hx])
      (fun c hc => by rw [k₁.rd, k₁.wr, Nat.add_sub_cancel]; exact hr n (by omega) c hc)
      (fun h hh c hc k hk => by rw [a₁ h hh c hc k hk, k₁.mem, Nat.add_sub_cancel])) fun t ⟨a₂, k₂⟩ =>
      ⟨fun h hh c hc k hk => by rw [a₂ h hh c hc k hk, k₁.mem], k₁.trans k₂⟩

/-- `zmm11–zmm13` cleared. -/
theorem zselClear_ok (s : State) :
    WP isa (.block [zero 11, zero 12, zero 13]) s fun t =>
      (∀ h < 2, ∀ c < 3, ∀ k < 4, zq t (xr (11 + c)) h k = 0) ∧ ZVKeep [] zselRegs s t := by
  apply WP.of_runBlock
  simp only [zero, v, runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq,
    exists_eq_left']
  refine ⟨fun h hh c hc k hk => ?_, ⟨fun _ _ => rfl, rfl, rfl, rfl, fun r hr i hi => ?_, rfl⟩⟩
  · simp only [zq]
    rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;>
      simp only [VOp.exec, zlane_setV256 _ _ _ _ _ (show 2 * h + k / 2 < 4 by omega), y, xr, Nat.reduceAdd,
        reduceCtorEq, ↓reduceIte, VBinOp.sse, XBinOp.eval, BitVec.xor_self] <;>
      split <;> (try split) <;> exact Ifma.qword_zero _
  · simp only [zselRegs, not_or, not_exists, not_and] at hr
    have h1 := hr.2.1 0 (by decide); have h2 := hr.2.1 1 (by decide); have h3 := hr.2.1 2 (by decide)
    simp only [Nat.reduceAdd] at h1 h2 h3
    simp only [VOp.exec, zlane_setV256 _ _ _ _ _ hi, show y 11 = xr 11 from rfl, show y 12 = xr 12 from rfl,
      show y 13 = xr 13 from rfl, h1, h2, h3, ite_false]

/-- `rax = 1` if `g = a` is zero, else `0`. -/
theorem isZero_ok (s : State) (g : Reg) {a : Nat} (ha : a < 2 ^ 64) (hg : s.gpr g = BitVec.ofNat 64 a) :
    WP isa (.block (isZero g)) s fun t => t.gpr .rax = (if a = 0 then 1 else 0) ∧
      Proof.X25519.X86_64.Keeps [.rax] s t ∧ t.syms = s.syms := by
  have hM : (BitVec.ofNat 64 a - BitVec.ofNat 64 a - BitVec.setWidth 64 (BitVec.ofBool
      (decide ((BitVec.ofNat 64 a).toNat < (BitVec.signExtend 64 (1 : BitVec 32)).toNat)))) &&&
      BitVec.signExtend 64 (1 : BitVec 32) = if a = 0 then 1 else 0 := by
    by_cases h : a = 0
    · subst h; decide
    · have h1 : (BitVec.signExtend 64 (1 : BitVec 32)).toNat = 1 := by decide
      rw [h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, decide_eq_false (by omega),
        ite_eq_right_iff.mpr (fun h2 => absurd h2 h)]
      simp
  erun [isZero, hg, hM]
  refine ⟨⟨fun r hr => ?_, rfl, rfl, rfl⟩, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem isZero_scal (g : Reg) : scalCode (.block (isZero g)) = true := rfl

/-- The word of entry `m` of table `j` the selection leaves in row `c`, word `k`: the identity's
`[1, 1, 0]` for a zero magnitude. -/
def selWord (j m c k : Nat) : BitVec 64 :=
  if 1 ≤ m then feWord (combField j m c) k else if c < 2 ∧ k = 0 then 1 else 0

theorem selWord_or (j m c k : Nat) (hm : m ≤ 16) :
    (if 1 ≤ m ∧ m ≤ 16 then feWord (combField j m c) k else 0) |||
      (if c < 2 ∧ k = 0 then (if m = 0 then 1 else 0) else 0) = selWord j m c k := by
  unfold selWord
  by_cases h : 1 ≤ m
  · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨h, hm⟩), ite_eq_left_of_eq_true _ _ (eq_true h)]
    split <;> simp [show m ≠ 0 by omega]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), ite_eq_right_of_eq_false _ _ (eq_false h)]
    split <;> simp [show m = 0 by omega]

theorem qword_zero' (i : Nat) : qword (0#128) i = 0 := Ifma.qword_zero i

theorem qword_load512 (m : Mem) (a : Addr) {i q : Nat} (hi : i < 4) (hq : q < 2) :
    qword ((m.readW a 512).extractLsb' (128 * i) 128) q = m.readW (a + BitVec.ofNat 64 (16 * i + 8 * q)) 64 := by
  have e := readW_extract m a (w := 512) (k := 16 * i + 8 * q) (n := 8) (by omega)
  rw [← e]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [qword, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and,
    decide_eq_true (show 64 * q + j < 128 by omega)]
  congr 1; omega

theorem zselect_split : zselect = combSelSetup ++ ([zero 11, zero 12, zero 13] : List Instr) ++
    (List.range 16).flatMap (fun m => zselEntry (m + 1)) ++ isZero .r8 ++
    ([.vop (.vmovq (y 10) .rax)] : List Instr) ++ isZero .r10 ++
    ([.vop (.vmovq (y 9) .rax), zlo 10 10 9, .zop (.zbin .vporq (y 11) (y 11) (y 10)),
      .zop (.zbin .vporq (y 12) (y 12) (y 10)), .vmovdqu32Load (y 14) (sc ZK2)] : List Instr) := by
  simp only [zselect, List.append_assoc, List.cons_append, List.nil_append]

theorem zlane_vmovq (s : State) (d : XReg) (g : Reg) (r : XReg) {i : Nat} (hi : i < 4) :
    ((VOp.vmovq d g).exec s).zlane r i = if r = d then (if i = 0 then (0 : BitVec 64) ++ s.gpr g else 0)
      else s.zlane r i := by
  simp only [VOp.exec, State.zlane_setV128 _ _ _ _ _ hi]

/-- The selection: in half `h`, the words of entry `m_h` (`r8` for half 0, `r10` for half 1) of
table `j`, or the identity's, in `zmm11–zmm13` (`selWord`), and the row `ZK2` in `zmm14`. -/
theorem zselect_ok {s : State} {base T : Addr} (hs : Scratch s base) (ht : CombTbl s T) {j a b : Nat}
    (hj : j < 26) (ha : a ≤ 16) (hb : b ≤ 16) (hd : s.gpr .rdx = BitVec.ofNat 64 j)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 a) (h10 : s.gpr .r10 = BitVec.ofNat 64 b) :
    WP isa (.block zselect) s fun t =>
      (∀ h < 2, ∀ c < 3, ∀ k < 4, zq t (xr (11 + c)) h k = selWord j (hmag a b h) c k) ∧
      (∀ h < 2, ∀ k < 4, zq t (xr 14) h k = s.mem.readW (base + BitVec.ofNat 64 (ZK2 + 32 * h + 8 * k)) 64) ∧
      ZVKeep [.rax, .rcx, .rdx] (fun r => zselRegs r ∨ r = xr 9) s t := by
  rw [zselect_split, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff,
    WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (zscal rfl (combSelSetup_ok s hd ht.sym)) fun s₁ ⟨⟨x₁, k₁, _, y₁⟩, z₁⟩ => ?_
  refine WP.mono (zselClear_ok s₁) fun s₂ ⟨a₂, k₂⟩ => ?_
  have hr : ∀ e < 16, ∀ c < 3, InRegions (s₂.rd ++ s₂.wr)
      (T + BitVec.ofNat 64 (j * combTblBytes) + BitVec.ofNat 64 (combEntryBytes * e + 32 * c)) 32 := by
    intro e he c hc
    rw [k₂.rd, k₂.wr, k₁.2.2.1, k₁.2.2.2, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    refine VG.CallLay.inRegions_sub ht.rd ?_ (by decide)
    simp only [combTblBytes, combEntryBytes, combWordCount]; omega
  refine WP.mono (zselEntries_ok (X := T + BitVec.ofNat 64 (j * combTblBytes)) (a := a) (b := b) (by omega)
    (by omega) 16 (by decide) s₂
    (by rw [k₂.gpr _ List.not_mem_nil, k₁.1 _ (by decide), h8])
    (by rw [k₂.gpr _ List.not_mem_nil, k₁.1 _ (by decide), h10])
    (by rw [k₂.gpr _ List.not_mem_nil, x₁]) hr a₂) fun s₃ ⟨a₃, k₃⟩ => ?_
  have g₃ : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → s₃.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [k₃.gpr r (by simpa using h2), k₂.gpr r List.not_mem_nil, k₁.1 r (by simp [h1, h2, h3])]
  refine WP.mono (zscal (isZero_scal .r8) (isZero_ok s₃ .r8 (a := a) (by omega)
    (by rw [g₃ _ (by decide) (by decide) (by decide), h8]))) fun s₄ ⟨⟨r₄, k₄, y₄⟩, z₄⟩ => ?_
  let s₅ := (VOp.vmovq (y 10) .rax).exec s₄
  refine WP.of_runBlock ⟨s₅, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec]; rfl, ?_⟩
  refine WP.mono (zscal (isZero_scal .r10) (isZero_ok s₅ .r10 (a := b) (by omega)
    (by show s₄.gpr .r10 = _; rw [k₄.1 _ (by decide), g₃ _ (by decide) (by decide) (by decide), h10])))
    fun s₆ ⟨⟨r₆, k₆, y₆⟩, z₆⟩ => ?_
  have hz2 : InRegions (s₆.rd ++ s₆.wr) (base + BitVec.ofNat 64 ZK2) 64 := by
    rw [k₆.2.2.1, k₆.2.2.2]
    show InRegions (s₄.rd ++ s₄.wr) _ 64
    rw [k₄.2.2.1, k₄.2.2.2, k₃.rd, k₃.wr, k₂.rd, k₂.wr, k₁.2.2.1, k₁.2.2.2]
    exact ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base base (by unfold ZK2; omega) (by unfold ZK2; omega)⟩
  have hrdi : s₆.gpr .rdi = base := by
    rw [k₆.1 _ (by decide)]; show s₄.gpr .rdi = _; rw [k₄.1 _ (by decide), g₃ _ (by decide) (by decide) (by decide),
      hs.rdi]
  have m₆ : s₆.mem = s.mem := by
    rw [k₆.2.1]; show s₄.mem = _; rw [k₄.2.1, k₃.mem, k₂.mem, k₁.2.1]
  let w := s₆.mem.readW (base + BitVec.ofNat 64 ZK2) 512
  let u₁ := (VOp.vmovq (y 9) .rax).exec s₆
  let u₂ := (ZOp.vshufi32x4 (y 10) (y 10) (y 9) 0x44).exec u₁
  let u₃ := (ZOp.zbin .vporq (y 11) (y 11) (y 10)).exec u₂
  let u₄ := (ZOp.zbin .vporq (y 12) (y 12) (y 10)).exec u₃
  let u₅ := u₄.setZ (y 14) (w.extractLsb' 0 128) (w.extractLsb' 128 128) (w.extractLsb' 256 128)
    (w.extractLsb' 384 128)
  have e5 : exec (.vmovdqu32Load (y 14) (sc ZK2)) u₄ = some u₅ := by
    have hea : u₄.ea (sc ZK2) = base + BitVec.ofNat 64 ZK2 := ea_sc' hrdi ZK2
    have hin : InRegions (u₄.rd ++ u₄.wr) (base + BitVec.ofNat 64 ZK2) 64 := hz2
    simp only [exec, hea, State.load512, hin, ite_true, Option.map_some]
    rfl
  refine WP.of_runBlock ⟨u₅, ?_, ?_⟩
  · rw [runBlock_cons, show exec _ s₆ = some u₁ from rfl, runStep_some, runBlock_cons,
      show exec (zlo 10 10 9) u₁ = some u₂ from rfl, runStep_some, runBlock_cons, show exec _ u₂ = some u₃ from rfl,
      runStep_some, runBlock_cons, show exec _ u₃ = some u₄ from rfl, runStep_some, runBlock_cons, e5, runStep_some,
      runBlock_nil]
  have l₂ : ∀ i < 4, u₂.zlane (y 10) i = if i % 2 = 0 then
      (0 : BitVec 64) ++ (if hmag a b (i / 2) = 0 then (1 : BitVec 64) else 0) else 0 := by
    intro i hi
    have r6 : s₆.gpr .rax = if b = 0 then 1 else 0 := r₆
    have r4 : s₄.gpr .rax = if a = 0 then 1 else 0 := r₄
    simp only [u₂, zlane_zlo _ _ _ _ _ hi, ite_true, u₁, zlane_vmovq _ _ _ _ (show i - 2 < 4 by omega),
      zlane_vmovq _ _ _ _ hi, show y 10 ≠ y 9 by decide, ite_false, z₆, s₅, r6, r4]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> simp [hmag]
  have l₃ : ∀ r, r ≠ y 9 → r ≠ y 10 → ∀ i < 4, u₂.zlane r i = s₃.zlane r i := fun r h9 h10 i hi => by
    simp only [u₂, zlane_zlo _ _ _ _ _ hi, h10, ite_false, u₁, zlane_vmovq _ _ _ _ hi, h9, z₆, s₅]
    exact z₄ r i
  have hacc : ∀ h < 2, ∀ c < 3, ∀ k < 4, zq s₃ (xr (11 + c)) h k =
      if 1 ≤ hmag a b h ∧ hmag a b h ≤ 16 then feWord (combField j (hmag a b h) c) k else 0 := by
    intro h hh c hc k hk
    rw [a₃ h hh c hc k hk, accQ, k₂.mem, k₁.2.1]
    have hm : hmag a b h ≤ 16 := by simp only [hmag]; split <;> omega
    by_cases h1 : 1 ≤ hmag a b h
    · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨h1, hm⟩), ite_eq_left_of_eq_true _ _ (eq_true ⟨h1, hm⟩)]
      have hw := combTbl_word ht hj h1 hm (i := 4 * c + k) (by omega)
      rw [Proof.X25519.X86_64.word, Proof.X25519.X86_64.off] at hw
      rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat,
        show combEntryBytes * (hmag a b h - 1) + 32 * c + 8 * k =
          combEntryBytes * (hmag a b h - 1) + 8 * (4 * c + k) by omega,
        hw, entryWords_getD _ c k hc hk, combField, combCached_succ j _ h1]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  have h3 : ∀ c < 3, ∀ i < 4, s₃.zlane (y (11 + c)) i = s₃.zlane (xr (11 + c)) i := fun c hc i _ => by
    rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;> rfl
  refine ⟨fun h hh c hc k hk => ?_, fun h hh k hk => ?_, ⟨fun r hr => ?_, ?_, ?_, ?_, fun r hr i hi => ?_, ?_⟩⟩
  · have hmh : hmag a b h ≤ 16 := by simp only [hmag]; split <;> omega
    rw [← selWord_or _ _ _ _ hmh, ← hacc h hh c hc k hk]
    have hi : 2 * h + k / 2 < 4 := by omega
    have L1 : ∀ i < 4, u₅.zlane (y 11) i = s₃.zlane (y 11) i ||| u₂.zlane (y 10) i := fun i hi => by
      simp only [u₅, zlane_load _ _ _ _ hi, show y 11 ≠ y 14 by decide, ite_false, u₄, zlane_zbin _ _ _ _ _ _ hi,
        show y 11 ≠ y 12 by decide, u₃, ite_true, ZBinOp.sse, XBinOp.eval, l₃ (y 11) (by decide) (by decide) _ hi]
    have L2 : ∀ i < 4, u₅.zlane (y 12) i = s₃.zlane (y 12) i ||| u₂.zlane (y 10) i := fun i hi => by
      simp only [u₅, zlane_load _ _ _ _ hi, show y 12 ≠ y 14 by decide, ite_false, u₄, zlane_zbin _ _ _ _ _ _ hi,
        ite_true, u₃, show y 10 ≠ y 11 by decide, show y 12 ≠ y 11 by decide, ZBinOp.sse, XBinOp.eval,
        l₃ (y 12) (by decide) (by decide) _ hi]
    have L3 : ∀ i < 4, u₅.zlane (y 13) i = s₃.zlane (y 13) i := fun i hi => by
      simp only [u₅, zlane_load _ _ _ _ hi, show y 13 ≠ y 14 by decide, ite_false, u₄, zlane_zbin _ _ _ _ _ _ hi,
        show y 13 ≠ y 12 by decide, u₃, show y 13 ≠ y 11 by decide, l₃ (y 13) (by decide) (by decide) _ hi]
    rw [show xr (11 + c) = y (11 + c) by rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;> rfl]
    simp only [zq]
    rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl
    · rw [L1 _ hi, qword_or, l₂ _ hi]
      rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl <;>
        rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
        simp [hmag, qword_zero']
    · rw [L2 _ hi, qword_or, l₂ _ hi]
      rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl <;>
        rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
        simp [hmag, qword_zero']
    · rw [L3 _ hi]; simp
  · simp only [zq, u₅, show xr 14 = y 14 from rfl, zlane_load _ _ _ _ (show 2 * h + k / 2 < 4 by omega),
      ite_true, w]
    rw [qword_load512 _ _ (by omega) (Nat.mod_lt _ (by decide)), show s₆.mem = s.mem from m₆,
      Offset.add_ofNat_add_ofNat]
    congr 3; omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    show s₆.gpr r = s.gpr r
    rw [k₆.1 r (by simp [hr.1])]
    show s₄.gpr r = s.gpr r
    rw [k₄.1 r (by simp [hr.1]), g₃ r hr.1 hr.2.1 hr.2.2]
  · exact m₆
  · show s₆.rd = s.rd; rw [k₆.2.2.1]; show s₄.rd = _; rw [k₄.2.2.1, k₃.rd, k₂.rd, k₁.2.2.1]
  · show s₆.wr = s.wr; rw [k₆.2.2.2]; show s₄.wr = _; rw [k₄.2.2.2, k₃.wr, k₂.wr, k₁.2.2.2]
  · simp only [zselRegs, not_or, not_exists, not_and] at hr
    have n9 : r ≠ y 9 := hr.2
    have n10 : r ≠ y 10 := hr.1.1
    have n11 : r ≠ y 11 := hr.1.2.1 0 (by decide)
    have n12 : r ≠ y 12 := hr.1.2.1 1 (by decide)
    have n14 : r ≠ y 14 := hr.1.2.2.1
    simp only [u₅, zlane_load _ _ _ _ hi, n14, ite_false, u₄, zlane_zbin _ _ _ _ _ _ hi, n12, u₃, n11,
      l₃ r n9 n10 _ hi]
    rw [k₃.zl r (by simp only [zselRegs, not_or, not_exists, not_and]; exact hr.1) i hi,
      k₂.zl r (by simp only [zselRegs, not_or, not_exists, not_and]; exact hr.1) i hi, z₁]
  · show s₆.syms = s.syms; rw [y₆]; show s₄.syms = _; rw [y₄, k₃.syms, k₂.syms, y₁]

end VG.Proof.Ed25519.X86_64.Zmm
