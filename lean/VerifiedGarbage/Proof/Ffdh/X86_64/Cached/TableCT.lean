module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.TableLoops
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.TableLoops
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # FFDH's context on x86-64: the table in constant time

Every address and count of the table's stage is a function of its public
data `TabP`; between Montgomery multiplications, which are constant time
(`Mont.ct`), the taint analysis checks the code from the registers that the
correctness facts pin. -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Cached

open VG VG.X86_64 VG.Impl.Bignum VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem Env.rdi {T : TabP} {s : State} (he : Env T s) : s.gpr .rdi = off T.B T.o := he.mc.sub.good.rdi

theorem pins_env {α : Type} {Φ : α → State → Prop} (f : α → TabP) (h : ∀ a s, Φ a s → Env (f a) s) :
    Pins Φ [.rdi] :=
  pins_of (fun a _ => off (f a).B (f a).o) fun a s ha r hr => by
    simp only [List.mem_singleton] at hr
    subst hr
    exact (h a s ha).rdi

/-- A Montgomery multiplication the backends make in constant time. -/
theorem mm_ct (Mo : Mont) {o a b : Nat} (hu : MmUse o a b) {α : Type} {Φ : α → State → Prop}
    (f : α → TabP) (h : ∀ a s, Φ a s → Env (f a) s) : RelCT isa (Two Φ) (Mo.mm o a b) fun _ _ => True :=
  two_map (fun x => (⟨off (f x).B (f x).o, slot (f x).w 8, (f x).w⟩ : Ws))
    (fun x s hx => ⟨(f x).mi, (h x s hx).mc.sub.good, Nat.le_refl _⟩) (Mo.ct hu)

/-- A row's index in `rax`. -/
def RowAt (q : TabP × Nat) (s : State) : Prop := Env q.1 s ∧ s.gpr .rax = BitVec.ofNat 64 q.2

theorem rowPtr_env {T : TabP} {s : State} (he : Env T s) {j : Nat} (hax : s.gpr .rax = BitVec.ofNat 64 j) :
    WP isa (.block rowPtr) s fun t => t.gpr .rbx = off T.cp (24 + 8 * T.w * j) ∧
      t.gpr .r12 = BitVec.ofNat 64 T.w ∧ t.mem = s.mem ∧ Keep [.rbx, .r12] s t :=
  rowPtr_ok he.mc.sub he.ctx hax

private theorem storeRow_ct' {a : Nat} (ha : a < 8) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi, .rax]) (.block (rowPtr ++ [.mov .rsi (.mem (hdr (sArr a)))])) hc).isSome
      = true) : RelCT isa (Two RowAt) (storeRow a) fun _ _ => True := by
  unfold storeRow
  refine RelCT.seq (two_piece (Ψ := fun q t => t.gpr .rsi = off (off q.1.B q.1.o) (slot q.1.w a) ∧
      t.gpr .rbx = off q.1.cp (24 + 8 * q.1.w * q.2) ∧ t.gpr .r12 = BitVec.ofNat 64 q.1.w) [.rdi, .rax]
    (pins_of (fun q r => if r = .rdi then off q.1.B q.1.o else BitVec.ofNat 64 q.2) fun q s h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.1.rdi
      · exact h.2) hT ?_)
    (two_taint [.rsi, .rbx, .r12] (pins_of (fun q r => if r = .rsi then off (off q.1.B q.1.o) (slot q.1.w a)
      else if r = .rbx then off q.1.cp (24 + 8 * q.1.w * q.2) else BitVec.ofNat 64 q.1.w) fun q s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact h.1
        · exact h.2.1
        · exact h.2.2) (by taint_decide))
  intro q s ⟨he, hax⟩
  rw [WP.block_append_iff]
  refine WP.mono (rowPtr_env he hax) fun t ⟨hb, h12, hm, k⟩ => ?_
  have hg := he.mc.sub.good
  have hA := hdr_lt_slot q.1.w 8 (show sArr a < 32 by unfold sArr; omega)
  have hdt : t.gpr .rdi = off q.1.B q.1.o := (k.gpr (by decide)).trans hg.rdi
  have hld : InRegions (t.rd ++ t.wr) (off (off q.1.B q.1.o) (8 * sArr a)) 8 := by
    rw [k.2.1, k.2.2]; exact hg.scr.ld (by omega)
  have hv : t.mem.readW (off (off q.1.B q.1.o) (8 * sArr a)) 64 = off (off q.1.B q.1.o) (slot q.1.w a) := by
    rw [hm]; exact hg.hdr.harr a ha
  refine WP.mono (WP.keep [.rsi] (Q := fun u => u.gpr .rsi = off (off q.1.B q.1.o) (slot q.1.w a)) (by
    xrun [State.ea, hdr, hdt, hdrOff, hld, hv]) rfl) fun u ⟨hs, ku⟩ => ⟨hs, ?_, ?_⟩
  · rw [ku.gpr (by decide)]; exact hb
  · rw [ku.gpr (by decide)]; exact h12

private theorem loadRow_ct' {a : Nat} (ha : a < 8) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi, .rax])
      (.block (rowPtr ++ [.mov .rsi (.reg .rbx), .mov .rbx (.mem (hdr (sArr a)))])) hc).isSome = true) :
    RelCT isa (Two RowAt) (loadRow a) fun _ _ => True := by
  unfold loadRow
  refine RelCT.seq (two_piece (Ψ := fun q t => t.gpr .rbx = off (off q.1.B q.1.o) (slot q.1.w a) ∧
      t.gpr .rsi = off q.1.cp (24 + 8 * q.1.w * q.2) ∧ t.gpr .r12 = BitVec.ofNat 64 q.1.w) [.rdi, .rax]
    (pins_of (fun q r => if r = .rdi then off q.1.B q.1.o else BitVec.ofNat 64 q.2) fun q s h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.1.rdi
      · exact h.2) hT ?_)
    (two_taint [.rsi, .rbx, .r12] (pins_of (fun q r => if r = .rbx then off (off q.1.B q.1.o) (slot q.1.w a)
      else if r = .rsi then off q.1.cp (24 + 8 * q.1.w * q.2) else BitVec.ofNat 64 q.1.w) fun q s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact h.2.1
        · exact h.1
        · exact h.2.2) (by taint_decide))
  intro q s ⟨he, hax⟩
  rw [WP.block_append_iff]
  refine WP.mono (rowPtr_env he hax) fun t ⟨hb, h12, hm, k⟩ => ?_
  have hg := he.mc.sub.good
  have hA := hdr_lt_slot q.1.w 8 (show sArr a < 32 by unfold sArr; omega)
  have hdt : t.gpr .rdi = off q.1.B q.1.o := (k.gpr (by decide)).trans hg.rdi
  have hld : InRegions (t.rd ++ t.wr) (off (off q.1.B q.1.o) (8 * sArr a)) 8 := by
    rw [k.2.1, k.2.2]; exact hg.scr.ld (by omega)
  have hv : t.mem.readW (off (off q.1.B q.1.o) (8 * sArr a)) 64 = off (off q.1.B q.1.o) (slot q.1.w a) := by
    rw [hm]; exact hg.hdr.harr a ha
  refine WP.mono (WP.keep [.rsi, .rbx] (Q := fun u => u.gpr .rbx = off (off q.1.B q.1.o) (slot q.1.w a) ∧
    u.gpr .rsi = off q.1.cp (24 + 8 * q.1.w * q.2)) (by
    xrun [State.ea, hdr, hdt, hdrOff, hld, hv, hb]) rfl) fun u ⟨hs, ku⟩ => ⟨hs.1, hs.2, ?_⟩
  rw [ku.gpr (by decide)]; exact h12

theorem storeRow_ct {a : Nat} (ha : a = aX ∨ a = aXm ∨ a = aY) :
    RelCT isa (Two RowAt) (storeRow a) fun _ _ => True := by
  rcases ha with rfl | rfl | rfl <;> exact storeRow_ct' (by decide) (by taint_decide)

theorem loadRow_ct {a : Nat} (ha : a = aX ∨ a = aXm ∨ a = aY) :
    RelCT isa (Two RowAt) (loadRow a) fun _ _ => True := by
  rcases ha with rfl | rfl | rfl <;> exact loadRow_ct' (by decide) (by taint_decide)

theorem eval_ne_step {s : State} {j N : Nat} (hj : j < N) (hz : s.zf = some (decide (j + 1 = N))) :
    isa.eval .ne s = some (decide (j + 1 < N)) := by
  simp only [eval, hz, Option.map_some]
  congr 1
  by_cases h : j + 1 = N <;> simp [h] <;> omega

/-! ## The squares -/

/-- The squares' data: the stage's and the exponent `E` of the entry in `aY`. -/
def SqStart (q : TabP × Nat) (s : State) : Prop :=
  Env q.1 s ∧ wv s.mem (off q.1.B q.1.o) (slot q.1.w aY) q.1.w = q.1.M q.2 ∧ 1 ≤ q.1.rows ∧ q.1.rows < 2 ^ 63

/-- After `j` squares from a start. -/
def SqAt (q : TabP × Nat) (j : Nat) (t : State) : Prop := ∃ s, SqStart q s ∧ SqInv q.1 s q.2 j t

theorem squares_ct (Mo : Mont) :
    RelCT isa (Two SqStart) (Precompute.squares Mo.mm) (Two fun q t => SqAt q q.1.rows t) := by
  unfold Precompute.squares
  refine RelCT.seq (R := Two fun (q : TabP × Nat) t => 0 < q.1.rows ∧ SqAt q 0 t)
    (two_piece [.rdi] (pins_env (fun q => q.1) fun _ _ h => h.1) (by taint_decide)
      fun q s h => WP.mono (squares_start h.1 h.2.1) fun t ht => ⟨by have := h.2.2.1; omega, s, h, ht⟩) ?_
  refine two_loop (Φ := SqAt) (N := fun q => q.1.rows) ?_ ?_
  · refine RelCT.seq (R := Two fun (p : (TabP × Nat) × Nat) u => Env p.1.1 u)
      (two_post (mm_ct Mo (.inr (.inl ⟨rfl, rfl, rfl⟩)) (fun p => p.1.1) fun _ _ h => by
        obtain ⟨_, _, _, hI⟩ := h; exact hI.1) ?_)
      (two_taint [.rdi] (pins_env (fun (p : (TabP × Nat) × Nat) => p.1.1) fun _ _ h => h) (by taint_decide))
    intro p t ⟨_, s, hs, hI⟩
    have hP : 0 < p.1.1.P := by have := hs.1.mc.x1; omega
    exact WP.mono (mm_env Mo hI.1 (Or.inr (Or.inr rfl)) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by rw [hI.2.2.1]; exact p.1.1.M_lt hP _)) fun u hu => hu.1
  · intro q j t hj ⟨s, hs, hI⟩
    refine WP.mono (squares_step Mo hs.1 hj hs.2.2.2 hI) fun u ⟨hz, hu⟩ =>
      ⟨eval_ne_step hj hz, fun _ => ⟨s, hs, hu⟩, fun e => ⟨s, hs, e ▸ hu⟩⟩

/-! ## A product -/

/-- `(T, d, J)`: entry `d + J := ` entry `J` times entry `d`, in `aY`. -/
def PrAt (q : TabP × Nat × Nat) (s : State) : Prop :=
  Env q.1 s ∧ word s.mem (off q.1.B q.1.o) (8 * iJ) = BitVec.ofNat 64 q.2.2 ∧
    word s.mem (off q.1.B q.1.o) (8 * iD) = BitVec.ofNat 64 q.2.1 ∧
    wv s.mem (off q.1.B q.1.o) (slot q.1.w aY) q.1.w < q.1.P ∧ 2 + q.2.1 + q.2.2 < 34

theorem prAt_rdi : Pins PrAt [.rdi] := pins_env (fun q => q.1) fun _ _ h => h.1

/-- `PrAt` after a change of only the array `aX` and nothing in the header. -/
theorem PrAt.of_env {q : TabP × Nat × Nat} {s t : State} (h : PrAt q s) (he : Env q.1 t)
    (hd : ∀ i, 17 ≤ i → i < 32 → word t.mem (off q.1.B q.1.o) (8 * i) = word s.mem (off q.1.B q.1.o) (8 * i))
    (hy : wv t.mem (off q.1.B q.1.o) (slot q.1.w aY) q.1.w = wv s.mem (off q.1.B q.1.o) (slot q.1.w aY) q.1.w) :
    PrAt q t :=
  ⟨he, by rw [hd _ (by decide) (by decide)]; exact h.2.1, by rw [hd _ (by decide) (by decide)]; exact h.2.2.1,
    by rw [hy]; exact h.2.2.2.1, h.2.2.2.2⟩

theorem product_ct (Mo : Mont) : RelCT isa (Two PrAt) (Precompute.product Mo.mm) fun _ _ => True := by
  unfold Precompute.product
  simp only [seqs]
  -- `rax := J + 2`.
  refine RelCT.seq (R := Two fun (q : TabP × Nat × Nat) t => PrAt q t ∧ t.gpr .rax = BitVec.ofNat 64 (q.2.2 + 2))
    (two_piece [.rdi] prAt_rdi (by taint_decide) fun q s h => ?_) ?_
  · have hg := h.1.mc.sub.good
    have hlJ := hdr_lt_slot q.1.w 8 (show iJ < 32 by decide)
    refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 (q.2.2 + 2) ∧ t.mem = s.mem) (by
      xrun [State.ea, hdr, hg.rdi, hdrOff, hg.scr.ld (d := 8 * iJ) (by omega), h.2.1]
      apply BitVec.eq_of_toNat_eq; simp) rfl) fun t ⟨⟨hax, hm⟩, k⟩ => ⟨?_, hax⟩
    exact h.of_env (h.1.of_outScr (by intro x _; rw [hm]) k.2.1 k.2.2 (k.gpr (by decide)))
      (fun i _ _ => by rw [hm]) (by rw [hm])
  -- Entry `J` to `aX`.
  refine RelCT.seq (R := Two PrAt) (two_post (two_map (fun (q : TabP × Nat × Nat) => (q.1, q.2.2 + 2)) (fun _ _ h => ⟨h.1.1, h.2⟩)
    (loadRow_ct (Or.inl rfl))) fun q s ⟨h, hax⟩ => ?_) ?_
  · have hw := h.1.mc.w2
    refine WP.mono (load_env h.1 hax (Or.inl rfl) (by have := h.2.2.2.2; omega)
      (row_of_words (fun i _ => rfl)) (wv_lt _ _ _ _)) fun t ⟨he, _, ha, _, hd, _, _⟩ =>
      h.of_env he (fun i _ hi => hd i hi) (ha _ (by decide) (by decide))
  -- `aX := aX aY`.
  refine RelCT.seq (R := Two PrAt) (two_post (mm_ct Mo (by unfold MmUse; decide) (fun q => q.1)
    fun _ _ h => h.1) fun q s h => ?_) ?_
  · exact WP.mono (mm_env Mo h.1 (Or.inl rfl) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) h.2.2.2.1) fun t ⟨he, _, _, ha, _, hd, _, _⟩ =>
      h.of_env he hd (ha.wv_of_not_mem (by decide) (by decide) h.1.mc.sub.good.scr.nowrap)
  -- `rax := J + d + 2`.
  refine RelCT.seq (R := Two fun (q : TabP × Nat × Nat) t => Env q.1 t ∧
      t.gpr .rax = BitVec.ofNat 64 (2 + q.2.1 + q.2.2) ∧ 2 + q.2.1 + q.2.2 < 34)
    (two_piece [.rdi] prAt_rdi (by taint_decide) fun q s h => ?_) ?_
  · have hg := h.1.mc.sub.good
    have hlJ := hdr_lt_slot q.1.w 8 (show iJ < 32 by decide)
    have hlD := hdr_lt_slot q.1.w 8 (show iD < 32 by decide)
    refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 (2 + q.2.1 + q.2.2) ∧
        t.mem = s.mem) (by
      xrun [State.ea, hdr, hg.rdi, hdrOff, hg.scr.ld (d := 8 * iJ) (by omega),
        hg.scr.ld (d := 8 * iD) (by omega), h.2.1, h.2.2.1]
      apply BitVec.eq_of_toNat_eq; simp; omega) rfl) fun t ⟨⟨hax, hm⟩, k⟩ =>
      ⟨h.1.of_outScr (by intro x _; rw [hm]) k.2.1 k.2.2 (k.gpr (by decide)), hax, h.2.2.2.2⟩
  -- Its row, and the counter.
  refine RelCT.seq (R := Two fun (q : TabP × Nat × Nat) t => Env q.1 t) (two_post (two_map (fun (q : TabP × Nat × Nat) => (q.1, 2 + q.2.1 + q.2.2))
    (fun _ _ h => ⟨h.1, h.2.1⟩) (storeRow_ct (Or.inl rfl))) fun q s h => ?_)
    (two_taint [.rdi] (pins_env (fun (q : TabP × Nat × Nat) => q.1) fun _ _ h => h) (by taint_decide))
  exact WP.mono (store_env h.1 h.2.1 (by decide) h.2.2) fun t ht => ht.1

end VG.Proof.Ffdh.X86_64.Cached
