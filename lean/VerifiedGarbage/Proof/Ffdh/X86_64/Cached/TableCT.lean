module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.TableLoops
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import VerifiedGarbage.Proof.Ffdh.X86_64.Ws
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.TableLoops
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad

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

/-- `p` and `R² mod p` to their rows. -/
theorem storeRow_ct₂ {a : Nat} (ha : a = aN ∨ a = aR2) :
    RelCT isa (Two RowAt) (storeRow a) fun _ _ => True := by
  rcases ha with rfl | rfl <;> exact storeRow_ct' (by decide) (by taint_decide)

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

/-! ## A tooth's column -/

/-- `(T, c)`: before the column of the tooth `2^(c+1)`. -/
def CoAt (q : TabP × Nat) (s : State) : Prop :=
  Env q.1 s ∧ word s.mem (off q.1.B q.1.o) (8 * iD) = BitVec.ofNat 64 (2 ^ (q.2 + 1)) ∧
    wv s.mem (off q.1.B q.1.o) (slot q.1.w aY) q.1.w = q.1.entry (2 ^ q.2) ∧
    Entries q.1 (2 ^ (q.2 + 1)) s.mem ∧ 1 ≤ q.1.rows ∧ q.1.rows < 2 ^ 63 ∧ q.2 < 4

/-- The tooth's entry in `aY` and in its row, with `J - 1 = j` products done. -/
def PrL (q : TabP × Nat) (j : Nat) (s : State) : Prop :=
  Env q.1 s ∧ word s.mem (off q.1.B q.1.o) (8 * iJ) = BitVec.ofNat 64 (j + 1) ∧
    word s.mem (off q.1.B q.1.o) (8 * iD) = BitVec.ofNat 64 (2 ^ (q.2 + 1)) ∧
    wv s.mem (off q.1.B q.1.o) (slot q.1.w aY) q.1.w = q.1.entry (2 ^ (q.2 + 1)) ∧
    Entries q.1 (2 ^ (q.2 + 1) + (j + 1)) s.mem ∧ q.2 < 4

theorem pow_facts {c : Nat} (hc : c < 4) : 2 ≤ 2 ^ (c + 1) ∧ 2 ^ (c + 1) ≤ 16 := by
  rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 by omega) with rfl | rfl | rfl | rfl <;> decide

theorem column_ct (Mo : Mont) : RelCT isa (Two CoAt) (Precompute.column Mo.mm) fun _ _ => True := by
  unfold Precompute.column
  simp only [seqs]
  -- The squares.
  refine RelCT.seq (R := Two fun (q : TabP × Nat) t => Env q.1 t ∧
      word t.mem (off q.1.B q.1.o) (8 * iD) = BitVec.ofNat 64 (2 ^ (q.2 + 1)) ∧
      wv t.mem (off q.1.B q.1.o) (slot q.1.w aY) q.1.w = q.1.entry (2 ^ (q.2 + 1)) ∧
      Entries q.1 (2 ^ (q.2 + 1)) t.mem ∧ q.2 < 4)
    (two_post (two_map (fun q => (q.1, Spec.Rsa.FixedBaseComb.exponent q.1.bits (2 ^ q.2)))
      (fun _ _ h => ⟨h.1, h.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩)
      ((squares_ct Mo).mono (fun _ _ h => h) fun _ _ _ => trivial)) fun q s h => ?_) ?_
  · obtain ⟨he, hD, hx, hE, hr, hr', hc⟩ := h
    refine WP.mono (squares_ok Mo he hx hr hr') fun t ⟨he₁, hx₁, hr₁, st₁, _⟩ => ⟨he₁, ?_, ?_, ?_, hc⟩
    · rw [st₁.hdr _ (by decide) (by decide) (by decide)]; exact hD
    · rw [← q.1.entry_tooth hc] at hx₁; exact hx₁
    · intro a ha; rw [hr₁ _ (rowFits_of (by have := (pow_facts hc).2; omega))]; exact hE a ha
  -- `rax := d + 2`.
  refine RelCT.seq (R := Two fun (q : TabP × Nat) t => (Env q.1 t ∧
      word t.mem (off q.1.B q.1.o) (8 * iD) = BitVec.ofNat 64 (2 ^ (q.2 + 1)) ∧
      wv t.mem (off q.1.B q.1.o) (slot q.1.w aY) q.1.w = q.1.entry (2 ^ (q.2 + 1)) ∧
      Entries q.1 (2 ^ (q.2 + 1)) t.mem ∧ q.2 < 4) ∧ t.gpr .rax = BitVec.ofNat 64 (2 + 2 ^ (q.2 + 1)))
    (two_piece [.rdi] (pins_env (fun q => q.1) fun _ _ h => h.1) (by taint_decide) fun q s h => ?_) ?_
  · have hg := h.1.mc.sub.good
    have hlD := hdr_lt_slot q.1.w 8 (show iD < 32 by decide)
    have hd := (pow_facts h.2.2.2.2).2
    refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 (2 + 2 ^ (q.2 + 1)) ∧
        t.mem = s.mem) (by
      xrun [State.ea, hdr, hg.rdi, hdrOff, hg.scr.ld (d := 8 * iD) (by omega), h.2.1]
      apply BitVec.eq_of_toNat_eq; simp; omega) rfl) fun t ⟨⟨hax, hm⟩, k⟩ =>
      ⟨⟨h.1.of_outScr (by intro x _; rw [hm]) k.2.1 k.2.2 (k.gpr (by decide)), by rw [hm]; exact h.2.1,
        by rw [hm]; exact h.2.2.1, by intro a ha; rw [hm]; exact h.2.2.2.1 a ha, h.2.2.2.2⟩, hax⟩
  -- The tooth's row.
  refine RelCT.seq (R := Two fun (q : TabP × Nat) t => Env q.1 t ∧
      word t.mem (off q.1.B q.1.o) (8 * iD) = BitVec.ofNat 64 (2 ^ (q.2 + 1)) ∧
      wv t.mem (off q.1.B q.1.o) (slot q.1.w aY) q.1.w = q.1.entry (2 ^ (q.2 + 1)) ∧
      Entries q.1 (2 ^ (q.2 + 1) + 1) t.mem ∧ q.2 < 4)
    (two_post (two_map (fun (q : TabP × Nat) => (q.1, 2 + 2 ^ (q.2 + 1))) (fun _ _ h => ⟨h.1.1, h.2⟩)
      (storeRow_ct (Or.inr (Or.inr rfl)))) fun q s h => ?_) ?_
  · obtain ⟨⟨he, hD, hx, hE, hc⟩, hax⟩ := h
    have hd := (pow_facts hc).2
    have hn := he.mc.sub.scr.nowrap
    have hio : ∀ i < 32, q.1.o + 8 * i + 8 ≤ q.1.Z := fun i hi => by
      have := hdr_lt_slot q.1.w 8 hi; have := he.mc.sub.lo; have := he.mc.sub.hi; omega
    have hwo : ∀ b < 8, q.1.o + slot q.1.w b + 8 * q.1.w ≤ q.1.Z := fun b hb => by
      have := slot_le (w := q.1.w) hb; have := he.mc.sub.hi; omega
    refine WP.mono (store_env he hax (by decide) (by omega)) fun t ⟨he₃, hrow₃, hr₃, hos₃, _, _⟩ =>
      ⟨he₃, ?_, ?_, fun a ha => ?_, hc⟩
    · rw [OutScr.wordAt hos₃ (hio _ (by decide)) hn]; exact hD
    · rw [OutScr.wvAt hos₃ (hwo _ (by decide)) hn]; exact hx
    · by_cases hlast : a = 2 ^ (q.2 + 1)
      · subst hlast
        rw [show 2 + 2 ^ (q.2 + 1) = 2 ^ (q.2 + 1) + 2 by omega] at hrow₃
        rw [show 2 + 2 ^ (q.2 + 1) = 2 ^ (q.2 + 1) + 2 by omega, hrow₃, hx]
      · rw [hr₃ _ (by omega) (rowFits_of (by omega))]; exact hE a (by omega)
  -- `J := 1`.
  refine RelCT.seq (R := Two fun (q : TabP × Nat) t => 0 < 2 ^ (q.2 + 1) - 1 ∧ PrL q 0 t)
    (two_piece [.rdi] (pins_env (fun q => q.1) fun _ _ h => h.1) (by taint_decide) fun q s h => ?_) ?_
  · obtain ⟨he, hD, hx, hE, hc⟩ := h
    have hg := he.mc.sub.good
    have hlJ := hdr_lt_slot q.1.w 8 (show iJ < 32 by decide)
    have hd := pow_facts hc
    refine WP.mono (WP.keep [.rax] (Q := fun t =>
        t.mem = s.mem.writeW (off (off q.1.B q.1.o) (8 * iJ)) (BitVec.ofNat 64 1)) (by
      xrun [State.ea, hdr, hg.rdi, hdrOff, hg.scr.st (d := 8 * iJ) (by omega),
        show BitVec.setWidth 64 (1 : BitVec 32) = BitVec.ofNat 64 1 from rfl]) rfl) fun t ⟨hm, k⟩ => ?_
    obtain ⟨he₄, hJ₄, hh₄, ha₄, hr₄, _⟩ := slot_env he (i := iJ) (by decide) (by decide) hm k.2.1 k.2.2
      (k.gpr (by decide))
    refine ⟨by omega, he₄, hJ₄, by rw [hh₄ _ (by decide) (by decide)]; exact hD,
      by rw [ha₄ _ (by decide)]; exact hx, fun a ha => ?_, hc⟩
    rw [hr₄ _ (rowFits_of (by omega))]; exact hE a ha
  -- The products.
  refine RelCT.seq (R := Two fun (q : TabP × Nat) t => Env q.1 t)
    ((two_loop (Φ := PrL) (Ψ := fun q t => Env q.1 t) (N := fun q => 2 ^ (q.2 + 1) - 1) ?_ ?_).mono
      (fun _ _ h => h) fun _ _ h => h)
    (two_taint [.rdi] (pins_env (fun (q : TabP × Nat) => q.1) fun _ _ h => h) (by taint_decide))
  · refine two_map (fun (p : (TabP × Nat) × Nat) => (p.1.1, 2 ^ (p.1.2 + 1), p.2 + 1))
      (fun p s ⟨hj, he, hJ, hD, hx, _, hc⟩ => ⟨he, hJ, hD, ?_, ?_⟩) (product_ct Mo)
    · have hP : 0 < p.1.1.P := by have := he.mc.x1; omega
      rw [hx]; exact p.1.1.M_lt hP _
    · have := (pow_facts hc).2; simp only at hj ⊢; omega
  · intro q j t hj ⟨he, hJ, hD, hx, hE, hc⟩
    have hd := pow_facts hc
    refine WP.mono (product_ok Mo he (jt := q.2 + 1) (J := j + 1) (by omega) (by omega) (by omega) (by omega)
      hJ hD hx hE) fun u ⟨heu, hz, hJu, hDu, hxu, hEu, _⟩ =>
      ⟨eval_ne_step hj (by rw [hz]; congr 1; apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_iff]; omega),
        fun _ => ⟨heu, hJu, hDu, hxu, hEu, hc⟩, fun _ => heu⟩

/-! ## The table -/

/-- `(T, gp, k)`: `table_ok`'s hypotheses, `g`'s `k` bytes at `gp`. -/
def TbAt (q : TabP × Addr × Nat) (s : State) : Prop := ∃ gb : List Byte,
  Env q.1 s ∧ 1 ≤ q.1.rows ∧ q.1.rows < 2 ^ 63 ∧ Spec.Rsa.os2ip gb = q.1.G ∧
    word s.mem q.1.B (8 * VG.Impl.Ffdh.X86_64.Domain.sG) = q.2.1 ∧
    word s.mem q.1.B (8 * sK) = BitVec.ofNat 64 gb.length ∧ gb.length = q.2.2 ∧ Src s q.1.B q.1.Z q.2.1 gb ∧
    (∀ i < gb.length, 8 * q.1.n ≤ ofs q.1.cp (q.2.1 + BitVec.ofNat 64 i)) ∧ 1 ≤ gb.length ∧
    (gb.length + 7) / 8 ≤ q.1.w

theorem TbAt.kept {q : TabP × Addr × Nat} {s t : State} (h : TbAt q s) (he : Env q.1 t) (hk : Kept q.1 s t)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) : TbAt q t := by
  obtain ⟨gb, _, hr, hr', hG, hsG, hsK, hl, hsrc, hgsep, hgl, hgw⟩ := h
  exact ⟨gb, he, hr, hr', hG, by rw [hk.outer _ (by decide)]; exact hsG, by rw [hk.outer _ (by decide)]; exact hsK,
    hl, Src.of_only hsrc hk.only hgsep hrd hwr, hgsep, hgl, hgw⟩

theorem pins_tb : Pins TbAt [.rdi] := pins_env (fun q => q.1) fun _ _ h => h.choose_spec.1

/-- `rax := n`, an immediate. -/
theorem rax_imm_ok {T : TabP} {s : State} (he : Env T s) (n : Nat) (hn : n < 2 ^ 32) :
    WP isa (.block [.mov32 .rax (.imm (BitVec.ofNat 32 n))]) s fun t =>
      t.gpr .rax = BitVec.ofNat 64 n ∧ t.mem = s.mem ∧ Env T t ∧ Keep [.rax] s t := by
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 n ∧ t.mem = s.mem) (by
    xrun [show (BitVec.ofNat 32 n).setWidth 64 = BitVec.ofNat 64 n from by
      apply BitVec.eq_of_toNat_eq; simp [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega)]]) rfl)
    fun t ⟨⟨hax, hm⟩, k⟩ => ⟨hax, hm, he.of_outScr (by intro x _; rw [hm]) k.2.1 k.2.2 (k.gpr (by decide)), k⟩

/-- Entries 0 and 1, and the tooth `2`. -/
theorem initial_ct (Mo : Mont) : RelCT isa (Two TbAt)
    (seqs (Precompute.initial Mo.mm ++ [.block [.mov32 .rax (.imm 2), .store (hdr iD) .rax]])) fun _ _ => True := by
  unfold Precompute.initial
  simp only [List.cons_append, List.append_assoc]
  -- Entry 0.
  refine seqs_cons_ct (by simp) (RelCT.seq (R := Two TbAt) (two_post (mm_ct Mo (by unfold MmUse; decide)
    (fun q => q.1) fun _ _ h => h.choose_spec.1) fun q s h => ?_) ?_)
  · have he := h.choose_spec.1
    exact WP.mono (mm_env Mo he (Or.inr (Or.inr rfl)) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by rw [he.mc.xv.one]; exact he.mc.x1))
      fun t ⟨het, _, _, _, _, _, kp, k⟩ => h.kept het kp k.2.1 k.2.2
  refine seqs_cons_ct (by simp) (RelCT.seq (R := Two fun (q : TabP × Addr × Nat) t =>
      TbAt q t ∧ t.gpr .rax = BitVec.ofNat 64 2)
    (two_piece [] (fun _ _ _ _ _ _ hr => absurd hr List.not_mem_nil) (by taint_decide) fun q s h =>
      WP.mono (rax_imm_ok h.choose_spec.1 2 (by decide)) fun t ⟨hax, hm, het, k⟩ =>
        ⟨h.kept het (Kept.of_eq hm) k.2.1 k.2.2, hax⟩) ?_)
  refine seqs_cons_ct (by simp [Crt.loadArr]) (RelCT.seq (R := Two TbAt) (two_post (two_map
    (fun (q : TabP × Addr × Nat) => (q.1, 2)) (fun _ _ h => ⟨h.1.choose_spec.1, h.2⟩)
    (storeRow_ct (Or.inr (Or.inr rfl)))) fun q s h' => ?_) ?_)
  · obtain ⟨h, hax⟩ := h'
    exact WP.mono (store_env h.choose_spec.1 hax (by decide) (by decide)) fun t ⟨het, _, _, _, kp, k⟩ =>
      h.kept het kp k.2.1 k.2.2
  -- `aX := g`.
  refine RelCT.seqs_append (a := Crt.loadArr aX VG.Impl.Ffdh.X86_64.Domain.sG sK) (by simp [Crt.loadArr])
    (by simp) (RelCT.seq (R := Two fun (q : TabP × Addr × Nat) t => Env q.1 t)
      (two_post (two_map (fun (q : TabP × Addr × Nat) => (⟨⟨q.1.B, q.1.Z, q.1.o, q.1.w, q.1.w⟩, q.2.1, q.2.2⟩ : BPub))
        (fun q s h => ?_) (loadArr_ct (by decide) (by taint_decide) (by taint_decide))) fun q s h => ?_) ?_)
  · obtain ⟨gb, he, _, _, _, hsG, hsK, hl, hsrc, _, hgl, hgw⟩ := h
    exact ⟨q.1.mi, gb, he.mc.sub, he.mc.w2, Nat.le_refl _, show q.1.w < 2 ^ 30 by have := he.mc.w28; omega,
      by decide, by decide, by decide, hsG, hsK, hl, hsrc, hgl,
      show gb.length < 2 ^ 31 by have := he.mc.w28; omega, hgw⟩
  · obtain ⟨gb, he, _, _, _, hsG, hsK, _, hsrc, _, hgl, hgw⟩ := h
    refine WP.mono (primeLoad_ok he.mc.sub he.mc.w2 (Nat.le_refl _)
      (by have := he.mc.w28; omega) (show aX < 8 by decide) (show VG.Impl.Ffdh.X86_64.Domain.sG < 32 by decide)
      (show sK < 32 by decide) hsG hsK hsrc hgl (by have := he.mc.w28; omega) hgw) fun t ⟨_, _, ho, k⟩ => ?_
    have hf : Frm (off q.1.B q.1.o) [(slot q.1.w aX, 8 * (q.1.w + 2))] s.mem t.mem := Frm.of_outside ho (by simp)
    have hd : ∀ i, i < 32 → word t.mem (off q.1.B q.1.o) (8 * i) = word s.mem (off q.1.B q.1.o) (8 * i) :=
      fun i hi => hf.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact Or.inl (hdr_lt_slot q.1.w aX hi))
        (by have := hdr_lt_slot q.1.w 8 hi; omega)
    exact he.of_inner (Frm.cover hf (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact ⟨(slot q.1.w aX, 3 * (8 * (q.1.w + 2))), by simp [innerR], by simp only; omega, by simp only; omega⟩))
      k.2.1 k.2.2 (k.gpr (by decide)) (hd _ (by decide)) (hd _ (by decide))
  simp only [seqs]
  -- Entry 1.
  refine RelCT.seq (R := Two fun (q : TabP × Addr × Nat) t => Env q.1 t) (two_post (mm_ct Mo
    (o := aXm) (a := aX) (b := aR2) (by unfold MmUse; decide) (fun (q : TabP × Addr × Nat) => q.1)
    fun _ _ h => h) fun q s he => ?_) ?_
  · exact WP.mono (mm_env Mo he (Or.inr (Or.inl rfl)) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) he.mc.r2l) fun t ht => ht.1
  refine RelCT.seq (R := Two fun (q : TabP × Addr × Nat) t => Env q.1 t ∧ t.gpr .rax = BitVec.ofNat 64 3)
    (two_piece [] (fun _ _ _ _ _ _ hr => absurd hr List.not_mem_nil) (by taint_decide) fun q s he =>
      WP.mono (rax_imm_ok he 3 (by decide)) fun t ⟨hax, _, het, _⟩ => ⟨het, hax⟩) ?_
  refine RelCT.seq (R := Two fun (q : TabP × Addr × Nat) t => Env q.1 t) (two_post (two_map
    (fun (q : TabP × Addr × Nat) => (q.1, 3)) (fun _ _ h => h) (storeRow_ct (Or.inr (Or.inl rfl))))
    fun q s ⟨he, hax⟩ => WP.mono (store_env he hax (by decide) (show 3 < 34 by decide)) fun t ht => ht.1) ?_
  -- `aY :=` entry 1.
  refine RelCT.seq (R := Two fun (q : TabP × Addr × Nat) t => Env q.1 t ∧ t.gpr .rax = BitVec.ofNat 64 3)
    (two_piece [] (fun _ _ _ _ _ _ hr => absurd hr List.not_mem_nil) (by taint_decide) fun q s he =>
      WP.mono (rax_imm_ok he 3 (by decide)) fun t ⟨hax, _, het, _⟩ => ⟨het, hax⟩) ?_
  refine RelCT.seq (R := Two fun (q : TabP × Addr × Nat) t => Env q.1 t) (two_post (two_map
    (fun (q : TabP × Addr × Nat) => (q.1, 3)) (fun _ _ h => h) (loadRow_ct (Or.inr (Or.inr rfl))))
    fun q s ⟨he, hax⟩ => WP.mono (load_env he hax (Or.inr (Or.inr rfl)) (show 3 < 34 by decide)
      (row_of_words (fun i _ => rfl)) (wv_lt _ _ _ _)) fun t ht => ht.1) ?_
  exact two_taint [.rdi] (pins_env (fun (q : TabP × Addr × Nat) => q.1) fun _ _ h => h) (by taint_decide)

theorem table_ct (Mo : Mont) : RelCT isa (Two TbAt) (seqs (Precompute.table Mo.mm)) fun _ _ => True := by
  unfold Precompute.table
  rw [show Precompute.initial Mo.mm ++ [.block [.mov32 .rax (.imm 2), .store (hdr iD) .rax],
      .loop (Precompute.column Mo.mm) .ne] = (Precompute.initial Mo.mm ++
      [.block [.mov32 .rax (.imm 2), .store (hdr iD) .rax]]) ++ [.loop (Precompute.column Mo.mm) .ne] by simp]
  refine RelCT.seqs_append (by simp) (by simp) (RelCT.seq (R := Two fun (q : TabP × Addr × Nat) t =>
      0 < 4 ∧ CoAt (q.1, 0) t)
    (two_post (initial_ct Mo) fun q s h => ?_) ?_)
  · obtain ⟨gb, he, hr, hr', hG, hsG, hsK, _, hsrc, hgsep, hgl, hgw⟩ := h
    exact WP.mono (initial_ok Mo he hG hsG hsK hsrc hgsep hgl hgw) fun t ⟨het, hD, hx, hE, _⟩ =>
      ⟨by decide, het, hD, hx, hE, hr, hr', Nat.zero_lt_succ 3⟩
  refine (two_loop (Φ := fun (q : TabP × Addr × Nat) c t => CoAt (q.1, c) t) (Ψ := fun _ _ => True)
    (N := fun _ => 4) ?_ ?_).mono (fun _ _ h => h) fun _ _ _ => trivial
  · exact two_map (fun (p : (TabP × Addr × Nat) × Nat) => (p.1.1, p.2)) (fun _ _ h => h.2) (column_ct Mo)
  · intro q c t hc ⟨he, hD, hx, hE, hr, hr', _⟩
    refine WP.mono (column_ok Mo he hc hD hx hE hr hr') fun u ⟨heu, hz, hDu, hxu, hEu, _⟩ =>
      ⟨eval_ne_step hc hz, fun hc' => ⟨heu, hDu, hxu, hEu, hr, hr', hc'⟩, fun _ => trivial⟩

end VG.Proof.Ffdh.X86_64.Cached
