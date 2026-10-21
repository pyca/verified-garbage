module

public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Step
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Table
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Readonly
public import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.RunU
public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Model
import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Ctx
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Mem
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block

/-!
# ML-KEM on AArch64: the 16-bit NTT of a polynomial stored with 32 bits, by the machine

Coefficient `p` of the polynomial at `x0` is the word at `4p`: the machine
follows its low halfword, `Wu p` (`initU_rel`), and finds the reduced
coefficients of `NTT` in the low halfwords and zero in the high ones
(`polyIs_of_outU`). So `ntt` (`ntt_run`), which first stores the table in the working space
(`halves_ok`), transforms the polynomial in place.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.NttR

open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Ntt16 (hw4 vhalf_table LRep vword_lo vword_halves toInt_lo halves_ok HInv)

/-- The low halfword of the input's coefficient `p`. -/
def Wu (s₀ : State) (p : Nat) : BitVec 16 := (coeffAt s₀.mem (s₀.gpr .x0) p).extractLsb' 0 16

/-- Coefficient `4 j + k` of a polynomial stored with 32 bits: word `k` of the vector at `16 j`. -/
theorem coeffAt_chunk (m : Mem) (p : Addr) (j : Nat) {k : Nat} (hk : k < 4) :
    coeffAt m p (4 * j + k) = vword (m.read (p + BitVec.ofNat 64 (16 * j)) 16) k := by
  have key : ∀ k, p + BitVec.ofNat 64 (16 * j) + BitVec.ofNat 64 (4 * k) = coeffAddr p (4 * j + k) :=
    fun k => by rw [ptr_add, coeffAddr]; exact congrArg (p + BitVec.ofNat 64 ·) (by omega)
  rw [read16, vword_ofVWords _ _ _ _ hk]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] <;> rw [key] <;> rfl

/-- The machine's state at the start holds of `s₀`, for regions laid out as `rsU` and `rsN`:
the polynomial at `x0`, the working space at `x1`, the table at `tb`. -/
theorem initU_rel {rs : List Rg} {s₀ : State} {tb : Addr} {tab : Nat} {H : List Nat}
    {L : Nat → Nat → BitVec 16} {O : Nat → BitVec 16} (hL : ∀ p, L 0 p = Wu s₀ p) (hlen : rs.length = 3)
    (hc0 : chunks rs 0 = 64) (hc2 : chunks rs 2 = 32)
    (h0 : rbase rs s₀ 0 = s₀.gpr .x0 + BitVec.ofNat 64 0) (h1 : rbase rs s₀ 1 = s₀.gpr .x1 + BitVec.ofNat 64 0)
    (h2 : rbase rs s₀ 2 = tb)
    (hT : ∀ {j e}, j < 32 → e < 8 → Y.get (slot yw tab j) e = cT (H.getD (8 * j + e) 0))
    (htab : ∀ j < 64, s₀.mem.readW (tb + BitVec.ofNat 64 (0 + 8 * j)) 64 = hw4 H j) :
    Rel rs s₀ L O (initUs tab) s₀ := by
  refine ⟨fun r e he => ?_, fun r => ?_, fun k hk j hj e he => ?_, rfl, rfl, rfl, rfl⟩
  · have : ((initUs tab).vreg r).get e = junkT := by
      show slot tw (slot yw 0 (vi r)) e = 0
      rw [slot_zero, slot_zero]
    rw [this]; exact Hd.junk _
  · unfold initUs
    rw [greg_setG, greg_setG]
    by_cases hx1 : r = .x1
    · subst hx1
      rw [ite_eq_left rfl]
      exact GHd.code (rs := rs) ⟨by rw [hlen]; decide, by decide, by decide, by rw [h1, ptr_zero, ptr_zero]⟩
    · rw [ite_eq_right hx1]
      by_cases hx0 : r = .x0
      · subst hx0
        rw [ite_eq_left rfl]
        exact GHd.code (rs := rs) ⟨by rw [hlen]; decide, by decide, by decide, by rw [h0, ptr_zero, ptr_zero]⟩
      · rw [ite_eq_right hx0]
        show GHd rs s₀ (G.ofCode (slot gw 0 (gi r))) _
        rw [slot_zero]
        trivial
  · rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
    · rw [hc0] at hj
      rw [show ((initUs tab).chunk 0 j).get e = _ from fInU_get j hj e he]
      have ea : caddr rs s₀ 0 j = s₀.gpr .x0 + BitVec.ofNat 64 (16 * j) := by
        rw [caddr, h0, ptr_zero]
      split
      · rename_i hev
        refine (Hd.mk (by decide)).2 ?_
        rw [eval_mk, Nat.zero_mod, Nat.mod_eq_of_lt (show 4 * j + e / 2 < 512 by omega)]
        rw [hL, Wu, coeffAt_chunk _ _ _ (show e / 2 < 4 by omega), vword_lo, ea,
          show 2 * (e / 2) = e by omega]
      · exact Hd.junk _
    · rw [show ((initUs tab).chunk 1 j).get e = 0 from by
        show slot tw (slot yw 0 j) e = 0; rw [slot_zero, slot_zero]]
      exact Hd.junk _
    · rw [hc2] at hj
      have ea : caddr rs s₀ 2 j = tb + BitVec.ofNat 64 (0 + 16 * j) := by
        rw [caddr, h2, Nat.zero_add]
      have hv := vhalf_table (m := s₀.mem) (p := tb) (off := 0) (N := 64) (H := H) htab (i := j) (by omega) he
      rw [show ((initUs tab).chunk 2 j).get e = _ from hT hj he, ea, hv]
      exact Hd.cT _

/-- The low halfwords of a reduced polynomial represent its coefficients. -/
theorem lrep_redU {m : Mem} {p : Addr} (h : Reduced m p) {i : Nat} (hi : i < 256) :
    LRep ((coeffAt m p i).extractLsb' 0 16) (polyAt m p)[i]! 3329 := by
  have hv := polyAt_val h (show i < n from hi)
  have hl : (coeffAt m p i).toNat < 3329 := h i hi
  rw [LRep, toInt_lo (by omega), ← hv]
  have hz : ((polyAt m p)[i]!).val < 3329 := ((polyAt m p)[i]!).isLt
  exact ⟨by omega, by omega, by simp⟩

/-- After a run that `outU` accepts, the polynomial at `x0` holds `O`'s coefficients. -/
theorem polyIs_of_outU {rs : List Rg} {s₀ s : State} {L : Nat → Nat → BitVec 16} {O : Nat → BitVec 16}
    {σ : St} {f : Poly} (hlen : rs.length = 3) (hc0 : chunks rs 0 = 64)
    (h0 : rbase rs s₀ 0 = s₀.gpr .x0 + BitVec.ofNat 64 0) (hr : Rel rs s₀ L O σ s) (ho : outU σ = true)
    (hO : ∀ p < 256, (O p).toNat = (f[p]!).val) : PolyIs s.mem (s₀.gpr .x0) f := by
  have hout : ∀ j < 64, ∀ e < 8, (σ.chunk 0 j).get e = if e % 2 = 0 then outT (4 * j + e / 2) else cT 0 := by
    simpa only [outU, List.all_eq_true, List.mem_range, Nat.beq_eq] using ho
  refine polyIs_of_toNat fun i hi => ?_
  have hi256 : i < 256 := hi
  have hj : i / 4 < chunks rs 0 := by rw [hc0]; omega
  have ea : caddr rs s₀ 0 (i / 4) = s₀.gpr .x0 + BitVec.ofNat 64 (16 * (i / 4)) := by
    rw [caddr, h0, ptr_zero]
  have hlo := hr.mem 0 (by rw [hlen]; decide) (i / 4) hj (2 * (i % 4)) (by omega)
  have hhi := hr.mem 0 (by rw [hlen]; decide) (i / 4) hj (2 * (i % 4) + 1) (by omega)
  rw [hout _ (by omega) _ (by omega), ite_eq_left (by omega), ea,
    show 4 * (i / 4) + 2 * (i % 4) / 2 = i by omega] at hlo
  rw [hout _ (by omega) _ (by omega), ite_eq_right (by omega), ea] at hhi
  have vlo := (Hd.mk (by decide)).1 hlo
  rw [eval_mk, Nat.mod_eq_of_lt (show i < 512 by omega)] at vlo
  have vhi : vhalf (s.mem.read (s₀.gpr .x0 + BitVec.ofNat 64 (16 * (i / 4))) 16) (2 * (i % 4) + 1) = 0 := by
    have := (Hd.mk (by decide)).1 hhi
    rw [eval_mk] at this
    exact this
  rw [show i = 4 * (i / 4) + i % 4 by omega, coeffAt_chunk _ _ _ (Nat.mod_lt _ (by decide)), vword_halves,
    vhi, vlo, BitVec.toNat_append, show 4 * (i / 4) + i % 4 = i by omega]
  rw [show (0 : BitVec 16).toNat = 0 from rfl, Nat.zero_shiftLeft, Nat.zero_or]
  exact hO i hi256

/-- What `fwd` and `inv` need: the polynomial at `x0` and the working space at `x1`, writable and
apart, the polynomial reduced, and the table `H` at `sym`, readable and apart from both. -/
structure InU (sym : String) (H : List Nat) (s : State) : Prop where
  wr : s.wr = [polyRegion (s.gpr .x0), polyRegion (s.gpr .x1)]
  disj : (polyRegion (s.gpr .x0)).Disjoint (polyRegion (s.gpr .x1))
  red : Reduced s.mem (s.gpr .x0)
  table : ∀ j < 64, s.mem.readW (s.syms sym + BitVec.ofNat 64 (8 * j)) 64 = hw4 H j
  readable : Covers [⟨s.syms sym, 512⟩] (s.rd ++ s.wr)
  apartOutput : (polyRegion (s.gpr .x0)).Disjoint ⟨s.syms sym, 512⟩
  apartScratch : (polyRegion (s.gpr .x1)).Disjoint ⟨s.syms sym, 512⟩

/-- A region within the first `n` bytes of a region of `m`. -/
theorem disjoint_prefix {a b : Addr} {n m k : Nat} (hn : n ≤ m) (h : Region.Disjoint ⟨a, m⟩ ⟨b, k⟩) :
    Region.Disjoint ⟨a, n⟩ ⟨b, k⟩ := fun x h₁ h₂ => h x (by simp only [Region.Contains] at h₁ ⊢; omega) h₂

theorem ctxU {sym : String} {H : List Nat} {s₀ : State} (hi : InU sym H s₀) : Ctx (rsUs sym) s₀ := by
  have h3 : (rsUs sym).length = 3 := rfl
  have cases3 : ∀ k < (rsUs sym).length, k = 0 ∨ k = 1 ∨ k = 2 := fun k hk => by rw [h3] at hk; omega
  have w0 : polyRegion (s₀.gpr .x0) ∈ s₀.wr := by rw [hi.wr]; exact List.mem_cons_self ..
  have w1 : polyRegion (s₀.gpr .x1) ∈ s₀.wr := by rw [hi.wr]; simp
  have c1 : ∀ a, Region.Contains ⟨s₀.gpr .x1, 512⟩ a 16 → (polyRegion (s₀.gpr .x1)).Contains a 16 :=
    fun a h => by simp only [Region.Contains] at h ⊢; omega
  refine Ctx.of (fun k => [polyRegion (s₀.gpr .x0), ⟨s₀.gpr .x1, 512⟩,
      ⟨s₀.syms sym, 512⟩].getD k ⟨0, 0⟩) (by simp [rsUs]) (fun k hk => ?_) (fun k hk => ?_)
    (fun k hk a ha => ?_) (fun k hk hw a ha => ?_) (fun k k' hk hk' hne => ?_)
  · rcases cases3 k hk with rfl | rfl | rfl <;> simp [rsUs, chunks]
  · rcases cases3 k hk with rfl | rfl | rfl <;> exact contains_off (by simp [rsUs, chunks]) (by decide)
  · rcases cases3 k hk with rfl | rfl | rfl
    · exact in_rd_wr (in_regions w0 ha)
    · exact in_rd_wr (in_regions w1 (c1 _ ha))
    · exact hi.readable _ _ (in_regions (List.mem_singleton_self _) ha)
  · rcases cases3 k hk with rfl | rfl | rfl
    · exact in_regions w0 ha
    · exact in_regions w1 (c1 _ ha)
    · exact absurd hw Bool.false_ne_true
  · have d01 : Region.Disjoint (polyRegion (s₀.gpr .x0)) ⟨s₀.gpr .x1, 512⟩ :=
      (disjoint_prefix (by decide) hi.disj.symm).symm
    have d12 : Region.Disjoint ⟨s₀.gpr .x1, 512⟩ ⟨s₀.syms sym, 512⟩ :=
      disjoint_prefix (by decide) hi.apartScratch
    rcases cases3 k hk with rfl | rfl | rfl <;> rcases cases3 k' hk' with rfl | rfl | rfl
    all_goals first
      | exact absurd rfl hne
      | exact d01 | exact d01.symm | exact hi.apartOutput | exact hi.apartOutput.symm
      | exact d12 | exact d12.symm

/-- What `ntt` needs: the polynomial at `x0` and the working space at `x1`, writable and apart,
and the polynomial reduced. -/
structure InN (s : State) : Prop where
  wr : s.wr = [polyRegion (s.gpr .x0), polyRegion (s.gpr .x1)]
  disj : (polyRegion (s.gpr .x0)).Disjoint (polyRegion (s.gpr .x1))
  red : Reduced s.mem (s.gpr .x0)

/-- A range within a region at an offset of `p`, within a region at `p` that holds both. -/
theorem contains_shift {p a : Addr} {d n k K : Nat} (h : Region.Contains ⟨p + BitVec.ofNat 64 d, k⟩ a n)
    (hK : d + k ≤ K) (hK64 : K < 2 ^ 64) : Region.Contains ⟨p, K⟩ a n := by
  simp only [Region.Contains] at h ⊢
  rw [Offset.sub_add_eq, Offset.toNat_sub_ofNat, Nat.mod_eq_of_lt (show d < 2 ^ 64 by omega)] at h
  have := (a - p).isLt
  by_cases hc : d ≤ (a - p).toNat
  · rw [show 2 ^ 64 - d + (a - p).toNat = (a - p).toNat - d + 2 ^ 64 by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)] at h
    omega
  · rw [Nat.mod_eq_of_lt (by omega)] at h
    omega

theorem contains_self {p : Addr} {n len : Nat} (h : n ≤ len) : Region.Contains ⟨p, len⟩ p n := by
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]
  exact h

theorem ctxN {s₀ : State} (hi : InN s₀) : Ctx rsN s₀ := by
  have h3 : rsN.length = 3 := rfl
  have cases3 : ∀ k < rsN.length, k = 0 ∨ k = 1 ∨ k = 2 := fun k hk => by rw [h3] at hk; omega
  have w0 : polyRegion (s₀.gpr .x0) ∈ s₀.wr := by rw [hi.wr]; exact List.mem_cons_self ..
  have w1 : polyRegion (s₀.gpr .x1) ∈ s₀.wr := by rw [hi.wr]; simp
  have c1 : ∀ d, d + 16 ≤ 1024 → ∀ a, Region.Contains ⟨s₀.gpr .x1 + BitVec.ofNat 64 d, 512⟩ a 16 →
      d = 0 ∨ d = 512 → (polyRegion (s₀.gpr .x1)).Contains a 16 := fun d _ a h hd =>
    contains_shift h (by rcases hd with rfl | rfl <;> decide) (by decide)
  refine Ctx.of (fun k => [polyRegion (s₀.gpr .x0), ⟨s₀.gpr .x1 + BitVec.ofNat 64 0, 512⟩,
      ⟨s₀.gpr .x1 + BitVec.ofNat 64 512, 512⟩].getD k ⟨0, 0⟩) (by decide) (fun k hk => ?_) (fun k hk => ?_)
    (fun k hk a ha => ?_) (fun k hk hw a ha => ?_) (fun k k' hk hk' hne => ?_)
  · rcases cases3 k hk with rfl | rfl | rfl <;> decide
  · rcases cases3 k hk with rfl | rfl | rfl
    · exact contains_off (by decide) (by decide)
    · exact contains_self (p := s₀.gpr .x1 + BitVec.ofNat 64 0) (by decide)
    · exact contains_self (p := s₀.gpr .x1 + BitVec.ofNat 64 512) (by decide)
  · rcases cases3 k hk with rfl | rfl | rfl
    · exact in_rd_wr (in_regions w0 ha)
    · exact in_rd_wr (in_regions w1 (c1 0 (by decide) _ ha (.inl rfl)))
    · exact in_rd_wr (in_regions w1 (c1 512 (by decide) _ ha (.inr rfl)))
  · rcases cases3 k hk with rfl | rfl | rfl
    · exact in_regions w0 ha
    · exact in_regions w1 (c1 0 (by decide) _ ha (.inl rfl))
    · exact absurd hw (by decide)
  · have d1 : ∀ d, d = 0 ∨ d = 512 →
        Region.Disjoint (polyRegion (s₀.gpr .x0)) ⟨s₀.gpr .x1 + BitVec.ofNat 64 d, 512⟩ := fun d hd x h₁ h₂ =>
      hi.disj x h₁ (contains_shift h₂ (by rcases hd with rfl | rfl <;> decide) (by decide))
    have d12 : Region.Disjoint ⟨s₀.gpr .x1 + BitVec.ofNat 64 0, 512⟩ ⟨s₀.gpr .x1 + BitVec.ofNat 64 512, 512⟩ :=
      Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
    rcases cases3 k hk with rfl | rfl | rfl <;> rcases cases3 k' hk' with rfl | rfl | rfl
    · exact absurd rfl hne
    · exact d1 0 (.inl rfl)
    · exact d1 512 (.inr rfl)
    · exact (d1 0 (.inl rfl)).symm
    · exact absurd rfl hne
    · exact d12
    · exact (d1 512 (.inr rfl)).symm
    · exact d12.symm
    · exact absurd rfl hne

theorem ntt_split : Impl.MlKem.AArch64.Ntt16.ntt =
    .seq (.block (Impl.MlKem.AArch64.Ntt16.halves Impl.MlKem.AArch64.Ntt16.tableHalves .x1 512 ++
      Impl.MlKem.AArch64.Ntt16.consts ++ ([Impl.MlKem.AArch64.mov .x2 .x0, .addImm .x .x3 .x1 0,
        .movz .x .x5 4 0] : List Instr))) nttRest := rfl

theorem ntt_run (s₀ : State) (hi : InN s₀) :
    WP isa Impl.MlKem.AArch64.Ntt16.ntt s₀ fun s' =>
      s'.sp = s₀.sp ∧ PolyIs s'.mem (s₀.gpr .x0) (ntt (polyAt s₀.mem (s₀.gpr .x0))) := by
  rw [ntt_split, List.append_assoc, WP.seq_iff, WP.block_append_iff]
  have hreg : polyRegion (s₀.gpr .x1) ∈ s₀.wr := by rw [hi.wr]; simp
  have hlen : Impl.MlKem.AArch64.Ntt16.tableHalves.length = 256 := by
    rw [Impl.MlKem.AArch64.Ntt16.tableHalves.lit_eq]; decide +kernel
  refine WP.mono (halves_ok Impl.MlKem.AArch64.Ntt16.tableHalves (r := .x1) (by decide) (off := 512)
    (by rw [hlen]) (by decide) hreg) fun s₁ h₁ => ?_
  change WP isa (.block nttHead) s₁ (fun s₂ => WP isa nttRest s₂ _)
  rw [← WP.seq_iff]
  change WP isa nttTail s₁ _
  have e0 : s₁.gpr .x0 = s₀.gpr .x0 := h₁.keep.get .x0 (by decide)
  have e1 : s₁.gpr .x1 = s₀.gpr .x1 := h₁.keep.get .x1 (by decide)
  have hm : ∀ k < 1024, s₁.mem (s₀.gpr .x0 + BitVec.ofNat 64 k) = s₀.mem (s₀.gpr .x0 + BitVec.ofNat 64 k) :=
    fun k hk => h₁.frame _ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact fun h => hi.disj _ (Offset.contains_base _ (show k + 1 ≤ 1024 by omega) (by omega)) h)
  have hp : ∀ i < n, coeffAt s₁.mem (s₀.gpr .x0) i = coeffAt s₀.mem (s₀.gpr .x0) i :=
    fun i hi' => coeffAt_congr hm hi'
  have hpoly : polyAt s₁.mem (s₀.gpr .x0) = polyAt s₀.mem (s₀.gpr .x0) :=
    Vector.ext fun i hi' => by simp only [polyAt, Vector.getElem_ofFn]; rw [hp i hi']
  have hi₁ : InN s₁ := ⟨by rw [h₁.keep.wr, hi.wr, e0, e1], by rw [e0, e1]; exact hi.disj,
    fun i hi' => by rw [e0, hp i hi']; exact hi.red i hi'⟩
  have hc := checkN_ok
  generalize hx : initU.runP fwdRules rsN 16 nttTail = x at hc
  cases x with
  | none => cases hc
  | some σ =>
    have hrel := initU_rel (rs := rsN) (s₀ := s₁) (tb := s₁.gpr .x1 + BitVec.ofNat 64 512) (L := Lf (Wu s₁))
      (O := Of (Wu s₁)) (fun _ => rfl) rfl rfl rfl rfl rfl rfl tabT_get (fun j hj => by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.zero_add, e1]
        exact h₁.tab j (by rw [hlen]; exact hj))
    refine WP.mono (runP_ok (model (Wu s₁)) (ctxN hi₁) 16 _ hrel hx) fun s' h' =>
      ⟨by rw [h'.sp, h₁.keep.sp], ?_⟩
    rw [← hpoly, ← e0]
    exact polyIs_of_outU rfl rfl rfl h' hc fun p hp => Of_ntt (Wu s₁) _ (fun p hp => lrep_redU hi₁.red hp) hp

end VG.Proof.MlKem.AArch64.NttR
