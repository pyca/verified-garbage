module

public import VerifiedGarbage.Proof.Sha3.AArch64.Permute
public import VerifiedGarbage.Proof.Sha3.X2Contract
public import VerifiedGarbage.Proof.Sha3.Stream
public import VerifiedGarbage.Proof.MlKem.AArch64.Vec
public import VerifiedGarbage.Impl.Sha3.AArch64.Neon.X2
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
import VerifiedGarbage.Proof.Framework.AArch64.StraightV
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.VectorCrypto

/-!
# Two interleaved Keccak states on AArch64

Where they are in memory (`PairAt`: lane `i` of both in the 16 bytes at
`wordAddr p i`) and in the vector registers (`Pairs`), and the code that
moves them between the two, and their first words to two outputs.
-/

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Neon

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Proof.MlKem.AArch64 (VUpd VMem VChg Only wp_vop wp_ldrq wp_strq vupd_setV)

/-! ## The layout -/

/-- Where lane `i` of both states is. -/
def wordAddr (p : Addr) (i : Nat) : Addr := p + BitVec.ofNat 64 (16 * i)

/-- Where word `i` of an output is. -/
def outAddr (p : Addr) (i : Nat) : Addr := p + BitVec.ofNat 64 (8 * i)

/-- The states' memory. -/
def pairR (p : Addr) : Region := ⟨p, 400⟩

/-- An output of the longest rate. -/
def outR (p : Addr) : Region := ⟨p, 168⟩

/-- The states at `p`. -/
def PairAt (m : Mem) (p : Addr) (A B : Spec.Sha3.State) : Prop :=
  ∀ i < 25, m.read (wordAddr p i) 16 = ofVDwords A[i]! B[i]!

/-- The states in the vector registers. -/
def Pairs (s : State) (A B : Spec.Sha3.State) : Prop := ∀ i < 25, s.v (vreg i) = ofVDwords A[i]! B[i]!

theorem pair_contains (p : Addr) {i : Nat} (hi : i < 25) : (pairR p).Contains (wordAddr p i) 16 :=
  Offset.contains_base p (by omega) (by omega)

theorem vreg_inj : ∀ i < 32, ∀ j < 32, vreg i = vreg j ↔ i = j := by decide +kernel

theorem pair_xor (a b c d : BitVec 64) : ofVDwords a b ^^^ ofVDwords c d = ofVDwords (a ^^^ c) (b ^^^ d) := by
  apply vec64_ext
  · rw [StraightV.vdword_xor, vdword_ofVDwords_0, vdword_ofVDwords_0, vdword_ofVDwords_0]
  · rw [StraightV.vdword_xor, vdword_ofVDwords_1, vdword_ofVDwords_1, vdword_ofVDwords_1]

theorem read_write16 (m : Mem) (p : Addr) (v : BitVec 128) : (m.write p 16 v).read p 16 = v :=
  VectorCrypto.read_write16 m p v

/-- All the vector registers. -/
def allV : List VReg := (List.range 32).map vreg

theorem allV_mem (r : VReg) : r ∈ allV := by cases r <;> decide

/-! ## What code keeps -/

/-- Only the general registers `rs`, vector registers and memory may differ. -/
structure RegKeep (rs : List Reg) (s t : State) : Prop where
  gpr : ∀ r, r ∉ rs → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

namespace RegKeep

theorem refl (rs : List Reg) (s : State) : RegKeep rs s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem trans {rs ts : List Reg} {s t u : State} (h : RegKeep rs s t) (g : RegKeep ts t u) : RegKeep (rs ++ ts) s u :=
  ⟨fun r hr => by
    rw [List.mem_append, not_or] at hr
    rw [g.gpr r hr.2, h.gpr r hr.1], g.rd.trans h.rd, g.wr.trans h.wr, g.sp.trans h.sp⟩

theorem mono {rs ts : List Reg} {s t : State} (h : RegKeep rs s t) (hs : ∀ r ∈ rs, r ∈ ts) : RegKeep ts s t :=
  ⟨fun r hr => h.gpr r fun hr' => hr (hs r hr'), h.rd, h.wr, h.sp⟩

theorem upd {s t : State} {r : Reg} {v : BitVec 64} (h : Upd s t r v) : RegKeep [r] s t :=
  ⟨fun q hq => h.other q fun e => hq (e ▸ List.mem_singleton_self _), h.rd, h.wr, h.sp⟩

theorem mupd {s t : State} {m : Mem} (h : Mupd s t m) : RegKeep [] s t :=
  ⟨fun _ _ => by rw [h.gpr], h.rd, h.wr, h.sp⟩

theorem vupd {s t : State} {r : VReg} {v : BitVec 128} (h : VUpd s t r v) : RegKeep [] s t :=
  ⟨fun _ _ => by rw [h.gpr], h.rd, h.wr, h.sp⟩

theorem vmem {s t : State} {m : Mem} (h : VMem s t m) : RegKeep [] s t :=
  ⟨fun _ _ => by rw [h.gpr], h.rd, h.wr, h.sp⟩

theorem only {rs : List Reg} {s t : State} (h : Only rs s t) : RegKeep rs s t := ⟨h.gpr, h.rd, h.wr, h.sp⟩

end RegKeep

/-- Only `x6`, `x7` and memory may differ. -/
structure OutKeep (s t : State) : Prop where
  gpr : ∀ r, r ≠ .x6 → r ≠ .x7 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  vec : t.v = s.v

theorem OutKeep.refl (s : State) : OutKeep s s := ⟨fun _ _ _ => rfl, rfl, rfl, rfl, rfl⟩
theorem OutKeep.trans {s t u : State} (h : OutKeep s t) (g : OutKeep t u) : OutKeep s u :=
  ⟨fun r h6 h7 => (g.gpr r h6 h7).trans (h.gpr r h6 h7), g.rd.trans h.rd, g.wr.trans h.wr, g.sp.trans h.sp,
    g.vec.trans h.vec⟩
theorem OutKeep.upd {s t : State} {d : Reg} {x : BitVec 64} (h : Upd s t d x) (hd : d = .x6 ∨ d = .x7) : OutKeep s t :=
  ⟨fun r h6 h7 => h.other r (by rintro rfl; rcases hd with rfl | rfl <;> contradiction), h.rd, h.wr, h.sp, h.vec⟩
theorem OutKeep.mupd {s t : State} {m : Mem} (h : Mupd s t m) : OutKeep s t :=
  ⟨fun r _ _ => by rw [h.gpr], h.rd, h.wr, h.sp, h.vec⟩

/-- The first 168 bytes of `A` at `p`. -/
def RateAt (m : Mem) (p : Addr) (A : Spec.Sha3.State) : Prop := ∀ i < 21, m.readW (outAddr p i) 64 = A[i]!

theorem RateAt.byte {m : Mem} {p : Addr} {A : Spec.Sha3.State} (h : RateAt m p A) {j : Nat} (hj : j < 168) :
    m (p + BitVec.ofNat 64 j) = Proof.Sha3.byteOf A j := by
  have e := congrArg (fun x : BitVec 64 => x.extractLsb' (8 * (j % 8)) 8) (h (j / 8) (by omega))
  simp only [Mem.readW] at e
  rw [BitVec.setWidth_eq, Mem.extractLsb'_read _ _ (show j % 8 < 64 / 8 by omega), outAddr, BitVec.add_assoc,
    ← BitVec.ofNat_add, Nat.div_add_mod] at e
  rw [e, Proof.Sha3.byteOf_eq' _ (by omega), getElem!_eq _ (by omega)]

/-! ## Loading and storing -/

theorem load_ok {s : State} {p : Addr} {r : Reg} {A B : Spec.Sha3.State} (hr : s.gpr r = p) (hp : PairAt s.mem p A B)
    (hin : ∀ i < 25, InRegions (s.rd ++ s.wr) (wordAddr p i) 16) :
    WP isa (.block (Impl.Sha3.AArch64.Neon.Pair.load r)) s fun s' => VChg allV s s' ∧ Pairs s' A B := by
  suffices h : ∀ k ≤ 25, WP isa (.block ((List.range k).map fun i => .ldrq (vreg i) r (16 * i))) s fun s' =>
      VChg allV s s' ∧ ∀ i < k, s'.v (vreg i) = ofVDwords A[i]! B[i]! from h 25 (Nat.le_refl _)
  intro k hk
  induction k with
  | zero => exact wp_nil ⟨.refl _ s, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ k ih =>
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨c, h⟩ => wp_ldrq (a := wordAddr p k) ⟨by omega, by omega⟩ (by rw [c.gpr, hr]; rfl)
      (by rw [c.rd, c.wr]; exact hin k (by omega)) fun u d => wp_nil ⟨(c.trans d.chg).mono fun r _ => allV_mem r, fun i hi => ?_⟩
    by_cases hik : i = k
    · subst hik; rw [d.v, c.mem, hp i (by omega)]
    · rw [d.other _ fun e => hik ((vreg_inj i (by omega) k (by omega)).mp e)]
      exact h i (by omega)

theorem store_ok {s : State} {p : Addr} {r : Reg} {A B : Spec.Sha3.State} (hr : s.gpr r = p) (hp : Pairs s A B)
    (hin : ∀ i < 25, InRegions s.wr (wordAddr p i) 16) :
    WP isa (.block (Impl.Sha3.AArch64.Neon.Pair.store r)) s fun s' =>
      VMem s s' s'.mem ∧ PairAt s'.mem p A B ∧ Frame [pairR p] s.mem s'.mem := by
  suffices h : ∀ k ≤ 25, WP isa (.block ((List.range k).map fun i => .strq (vreg i) r (16 * i))) s fun s' =>
      VMem s s' s'.mem ∧ (∀ i < k, s'.mem.read (wordAddr p i) 16 = ofVDwords A[i]! B[i]!) ∧ Frame [pairR p] s.mem s'.mem
    from h 25 (Nat.le_refl _)
  intro k hk
  induction k with
  | zero => exact wp_nil ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, fun i hi => absurd hi (Nat.not_lt_zero _), Frame.refl _ _⟩
  | succ k ih =>
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨c, h, f⟩ => wp_strq (a := wordAddr p k) ⟨by omega, by omega⟩ (by rw [c.gpr, hr]; rfl)
      (by rw [c.wr]; exact hin k (by omega)) fun u d => wp_nil ⟨⟨d.gpr.trans c.gpr, d.v.trans c.v, rfl, d.rd.trans c.rd,
        d.wr.trans c.wr, d.sp.trans c.sp⟩, fun i hi => ?_, ?_⟩
    · rw [d.mem, c.v]
      by_cases hik : i = k
      · subst hik; rw [read_write16, hp i (by omega)]
      · rw [wordAddr, wordAddr, Mem.read_write_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide)]
        exact h i (by omega)
    · rw [d.mem]
      exact f.write (List.mem_singleton_self _) _ (pair_contains p (by omega))

/-! ## Outputs -/

private theorem two_words {s t u : State} {a b : Addr} {x y : BitVec 64} (h₁ : Upd s t .x6 x) (h₂ : Upd t u .x7 y)
    {ra rb : Reg} {i : Nat} (hi : i < 4096) (ha : s.gpr ra = a) (hb : s.gpr rb = b) (ha6 : ra ≠ .x6) (ha7 : ra ≠ .x7) (hb6 : rb ≠ .x6)
    (hb7 : rb ≠ .x7) (hA : InRegions s.wr (outAddr a i) 8) (hB : InRegions s.wr (outAddr b i) 8) {Q : State → Prop}
    (hQ : ∀ t, OutKeep s t → t.mem = (s.mem.writeW (outAddr a i) x).writeW (outAddr b i) y → Q t) :
    WP isa (.block [.str .x .x6 ra (8 * i), .str .x .x7 rb (8 * i)]) u Q := by
  have g : ∀ r, r ≠ .x6 → r ≠ .x7 → u.gpr r = s.gpr r := fun r h6 h7 => (h₂.other r h7).trans (h₁.other r h6)
  have wr : u.wr = s.wr := h₂.wr.trans h₁.wr
  refine wp_str (a := outAddr a i) ⟨by omega, by omega⟩ (by rw [g ra ha6 ha7, ha]; rfl) (by rw [wr]; exact hA) fun v m₁ =>
    wp_str (a := outAddr b i) ⟨by omega, by omega⟩ (by rw [m₁.gpr, g rb hb6 hb7, hb]; rfl)
      (by rw [m₁.wr, wr]; exact hB) fun w m₂ => wp_nil (hQ w ((((OutKeep.upd h₁ (.inl rfl)).trans (.upd h₂ (.inr rfl))).trans
        (.mupd m₁)).trans (.mupd m₂)) ?_)
  rw [m₂.mem, m₁.mem, m₁.gpr, h₂.gpr, h₂.mem, h₁.mem, h₂.other _ (by decide), h₁.gpr]

theorem squeeze_step {s : State} {a b : Addr} {ra rb : Reg} {i : Nat} (hi : i < 21) (ha : s.gpr ra = a)
    (hb : s.gpr rb = b) (ha6 : ra ≠ .x6) (ha7 : ra ≠ .x7) (hb6 : rb ≠ .x6) (hb7 : rb ≠ .x7)
    (hA : InRegions s.wr (outAddr a i) 8) (hB : InRegions s.wr (outAddr b i) 8) :
    WP isa (.block [.umov .x .x6 (vreg i) 0, .umov .x .x7 (vreg i) 1, .str .x .x6 ra (8 * i),
      .str .x .x7 rb (8 * i)]) s fun t => OutKeep s t ∧
        t.mem = (s.mem.writeW (outAddr a i) (vdword (s.v (vreg i)) 0)).writeW (outAddr b i)
          (vdword (s.v (vreg i)) 1) :=
  WP.cons (s' := s.write .x .x6 (vdword (s.v (vreg i)) 0)) rfl <|
  WP.cons (s' := (s.write .x .x6 (vdword (s.v (vreg i)) 0)).write .x .x7 (vdword (s.v (vreg i)) 1)) rfl <|
    two_words (Upd.write64 _ _ _) (Upd.write64 _ _ _) (by omega) ha hb ha6 ha7 hb6 hb7 hA hB fun _ k m => ⟨k, m⟩

namespace X2

/-- The first `n` words of an output. -/
def outN (p : Addr) (n : Nat) : Region := ⟨p, 8 * n⟩

/-- Lane `i` of the first state. -/
theorem word0 {m : Mem} {p : Addr} {A B : Spec.Sha3.State} (h : PairAt m p A B) {i : Nat} (hi : i < 25) :
    m.readW (p + BitVec.ofNat 64 (16 * i)) 64 = A[i]! := by
  have e := congrArg (vdword · 0) (h i hi)
  simp only [vdword_ofVDwords_0] at e
  rw [vdword_read16 _ _ (by decide), wordAddr] at e
  simpa using e

/-- Lane `i` of the second. -/
theorem word1 {m : Mem} {p : Addr} {A B : Spec.Sha3.State} (h : PairAt m p A B) {i : Nat} (hi : i < 25) :
    m.readW (p + BitVec.ofNat 64 (16 * i + 8)) 64 = B[i]! := by
  have e := congrArg (vdword · 1) (h i hi)
  simp only [vdword_ofVDwords_1] at e
  rw [vdword_read16 _ _ (by decide), wordAddr, BitVec.add_assoc, ← BitVec.ofNat_add] at e
  exact e

/-- The interleaved states of `stateX2At` at `p`, lane by lane. -/
theorem pairAt_of_words {m : Mem} {p : Addr} {A B : Spec.Sha3.State}
    (hA : ∀ i < 25, m.readW (p + BitVec.ofNat 64 (16 * i)) 64 = A[i]!)
    (hB : ∀ i < 25, m.readW (p + BitVec.ofNat 64 (16 * i + 8)) 64 = B[i]!) : PairAt m p A B := fun i hi => by
  rw [read16_dwords, wordAddr, BitVec.add_assoc, ← BitVec.ofNat_add, hA i hi, hB i hi]

theorem stateX2_get (m : Mem) (p : Addr) {k i : Nat} (hi : i < 25) :
    (Proof.Sha3.stateX2At m p k)[i]! = m.readW (p + BitVec.ofNat 64 (16 * i + 8 * k)) 64 := by
  rw [getElem!_eq _ hi]
  simp only [Proof.Sha3.stateX2At, Vector.getElem_ofFn]
  rw [show 8 * (2 * i + k) = 16 * i + 8 * k by omega]

theorem pairAt_stateX2 (m : Mem) (p : Addr) :
    PairAt m p (Proof.Sha3.stateX2At m p 0) (Proof.Sha3.stateX2At m p 1) :=
  pairAt_of_words (fun i hi => by rw [stateX2_get m p hi, Nat.mul_zero, Nat.add_zero])
    fun i hi => by rw [stateX2_get m p hi, Nat.mul_one]

theorem stateX2_of_pairAt {m : Mem} {p : Addr} {A B : Spec.Sha3.State} (h : PairAt m p A B) :
    Proof.Sha3.stateX2At m p 0 = A ∧ Proof.Sha3.stateX2At m p 1 = B := by
  refine ⟨Vector.ext fun i hi => ?_, Vector.ext fun i hi => ?_⟩
  · rw [← getElem!_eq _ hi, ← getElem!_eq _ hi, stateX2_get _ _ hi, Nat.mul_zero, Nat.add_zero]; exact word0 h hi
  · rw [← getElem!_eq _ hi, ← getElem!_eq _ hi, stateX2_get _ _ hi, Nat.mul_one]; exact word1 h hi

theorem squeeze_ok {n : Nat} (hn : n ≤ 25) {s : State} {p a b : Addr} {rp ra rb : Reg} {A B : Spec.Sha3.State}
    (hp : s.gpr rp = p) (ha : s.gpr ra = a) (hb : s.gpr rb = b) (hp6 : rp ≠ .x6) (hp7 : rp ≠ .x7) (ha6 : ra ≠ .x6)
    (ha7 : ra ≠ .x7) (hb6 : rb ≠ .x6) (hb7 : rb ≠ .x7) (hP : PairAt s.mem p A B)
    (dab : (outN a n).Disjoint (outN b n)) (dpa : (pairR p).Disjoint (outN a n)) (dpb : (pairR p).Disjoint (outN b n))
    (hin : ∀ i < 25, InRegions (s.rd ++ s.wr) (wordAddr p i) 16)
    (hA : ∀ i < n, InRegions s.wr (outAddr a i) 8) (hB : ∀ i < n, InRegions s.wr (outAddr b i) 8) :
    WP isa (.block (Impl.Sha3.AArch64.Neon.X2.squeeze n rp ra rb)) s fun t => OutKeep s t ∧
      Frame [outN a n, outN b n] s.mem t.mem ∧ (∀ i < n, t.mem.readW (outAddr a i) 64 = A[i]!) ∧
        ∀ i < n, t.mem.readW (outAddr b i) 64 = B[i]! := by
  have cA : ∀ {q : Addr} {i : Nat}, i < n → (outN q n).Contains (outAddr q i) 8 := fun hi =>
    Offset.contains_base _ (by omega) (by omega)
  suffices h : ∀ k ≤ n, WP isa (.block ((List.range k).flatMap fun i => [.ldr .x .x6 rp (16 * i), .ldr .x .x7 rp (16 * i + 8),
      .str .x .x6 ra (8 * i), .str .x .x7 rb (8 * i)])) s fun t => OutKeep s t ∧
      Frame [outN a n, outN b n] s.mem t.mem ∧ (∀ i < k, t.mem.readW (outAddr a i) 64 = A[i]!) ∧
        ∀ i < k, t.mem.readW (outAddr b i) 64 = B[i]! from h n (Nat.le_refl _)
  intro k hk
  induction k with
  | zero =>
    exact wp_nil ⟨.refl s, Frame.refl _ _, fun i hi => absurd hi (Nat.not_lt_zero _), fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨kt, f, h1, h2⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have hPt : PairAt t.mem p A B := fun i hi => by
      rw [f.read (pair_contains p hi) (by simpa using ⟨dpa, dpb⟩) (by decide)]; exact hP i hi
    have inr : ∀ o, o + 8 ≤ 16 → InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (16 * k + o)) 8 := fun o ho => by
      obtain ⟨R, hR, hc⟩ := hin k (by omega)
      refine ⟨R, hR, ?_⟩
      rw [BitVec.ofNat_add, ← BitVec.add_assoc]
      exact CallLay.contains_trans hc ho (by decide)
    refine wp_ldr (a := p + BitVec.ofNat 64 (16 * k + 0)) ⟨by omega, by omega⟩ (by rw [kt.gpr rp hp6 hp7, hp]; rfl)
      (by rw [kt.rd, kt.wr]; exact inr 0 (by decide)) fun u₁ d₁ =>
      wp_ldr (a := p + BitVec.ofNat 64 (16 * k + 8)) ⟨by omega, by omega⟩
        (by rw [d₁.other rp hp6, kt.gpr rp hp6 hp7, hp]) (by rw [d₁.rd, d₁.wr, kt.rd, kt.wr]; exact inr 8 (by decide))
        fun u₂ d₂ => ?_
    rw [Nat.add_zero, word0 hPt (by omega)] at d₁
    rw [d₁.mem, word1 hPt (by omega)] at d₂
    refine two_words d₁ d₂ (by omega) (by rw [kt.gpr ra ha6 ha7, ha]) (by rw [kt.gpr rb hb6 hb7, hb]) ha6 ha7 hb6 hb7
      (by rw [kt.wr]; exact hA k (by omega)) (by rw [kt.wr]; exact hB k (by omega)) fun w kw mw => ⟨kt.trans kw, ?_, ?_, ?_⟩
    · rw [mw]
      exact (f.writeW List.mem_cons_self _ (cA (by omega))).writeW (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (cA (by omega))
    · intro i hi
      rw [mw, Mem.readW_writeW_sep (dab.sep (cA (by omega)) (cA (by omega))) (by decide)]
      by_cases hik : i = k
      · subst hik; exact Mem.readW_writeW_self64 _ _ _
      · rw [outAddr, outAddr, Mem.readW_writeW_sep (Offset.sep a (by omega) (by omega) (by omega)) (by decide)]
        exact h1 i (by omega)
    · intro i hi
      by_cases hik : i = k
      · subst hik; rw [mw]; exact Mem.readW_writeW_self64 _ _ _
      · rw [mw, show outAddr b k = b + BitVec.ofNat 64 (8 * k) from rfl, show outAddr b i = b + BitVec.ofNat 64 (8 * i) from rfl,
          Mem.readW_writeW_sep (Offset.sep b (by omega) (by omega) (by omega)) (by decide),
          Mem.readW_writeW_sep (dab.symm.sep (cA (by omega)) (cA (by omega))) (by decide)]
        exact h2 i (by omega)

end X2

end VG.Proof.Sha3.AArch64.Neon
