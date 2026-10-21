module

public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Rows
public import VerifiedGarbage.Proof.MlKem.AArch64.NttCommon
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Table
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Mem
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-!
# ML-KEM's 16-bit NTT on AArch64: pass 1

What the 16-bit NTTs' passes share: the polynomial at `f` and the working
space at `scratch` (`Pre`), what a pass keeps (`St`), the ranges it reads and
writes (`inF`, `inS`), and rows stored a vector at a time (`wp_storesN`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Ntt16

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem VG.Spec.MlKem
open Impl.MlKem.AArch64.Ntt16

section
variable (s₀ : State)

abbrev fP : Addr := s₀.gpr .x0
abbrev sP : Addr := s₀.gpr .x1
abbrev P₀ : Poly := polyAt s₀.mem (fP s₀)

end

/-- The precondition. -/
structure Pre (s₀ : State) : Prop where
  wr : s₀.wr = [polyRegion (fP s₀),polyRegion (sP s₀)]
  disj : (polyRegion (fP s₀)).Disjoint (polyRegion (sP s₀))
  red : Reduced s₀.mem (fP s₀)

theorem pre_of {s₀ : State} (h : Ntt.Pre s₀) : Pre s₀ := ⟨h.wr,h.disj,h.red⟩

/-- What holds throughout. -/
structure St (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x0 : s.gpr .x0 = fP s₀
  x1 : s.gpr .x1 = sP s₀

theorem St.keep {s₀ s s' : State} (h : St s₀ s) {rs : List Reg} (hk : Keep rs s s')
    (h0 : Reg.x0 ∉ rs := by decide) (h1 : Reg.x1 ∉ rs := by decide) : St s₀ s' :=
  ⟨by rw [hk.rd, h.rd], by rw [hk.wr, h.wr], by rw [hk.sp, h.sp], by rw [hk.gpr _ h0, h.x0],
    by rw [hk.gpr _ h1, h.x1]⟩

theorem St.vchg {s₀ s s' : State} (h : St s₀ s) {rs : List VReg} (hc : VChg rs s s') : St s₀ s' :=
  ⟨by rw [hc.rd, h.rd], by rw [hc.wr, h.wr], by rw [hc.sp, h.sp], by rw [hc.gpr, h.x0],
    by rw [hc.gpr, h.x1]⟩

theorem St.vmem {s₀ s s' : State} (h : St s₀ s) {m : Mem} (hc : VMem s s' m) : St s₀ s' :=
  ⟨by rw [hc.rd, h.rd], by rw [hc.wr, h.wr], by rw [hc.sp, h.sp], by rw [hc.gpr, h.x0],
    by rw [hc.gpr, h.x1]⟩

theorem inF {s₀ s : State} (hp : Pre s₀) (h : St s₀ s) {j : Nat} (hj : j + 4 ≤ 256) :
    InRegions (s.rd ++ s.wr) (coeffAddr (fP s₀) j) 16 := by
  apply in_rd_wr
  rw [h.wr,hp.wr]
  exact in_regions (List.mem_cons_self ..) (contains_off (by omega) (by decide))

theorem inF' {s₀ s : State} (hp : Pre s₀) (h : St s₀ s) {j : Nat} (hj : j + 4 ≤ 256) :
    InRegions s.wr (coeffAddr (fP s₀) j) 16 := by
  rw [h.wr, hp.wr]
  exact in_regions (List.mem_cons_self ..) (contains_off (by omega) (by decide))

theorem inS {s₀ s : State} (hp : Pre s₀) (h : St s₀ s) {o : Nat} (ho : o + 16 ≤ 1024) :
    InRegions s.wr (sP s₀ + BitVec.ofNat 64 o) 16 := by
  rw [h.wr, hp.wr]
  exact in_regions (R := polyRegion (sP s₀)) (by simp) (contains_off ho (by decide))

theorem inS' {s₀ s : State} (hp : Pre s₀) (h : St s₀ s) {o : Nat} (ho : o + 16 ≤ 1024) :
    InRegions (s.rd ++ s.wr) (sP s₀ + BitVec.ofNat 64 o) 16 := by
  exact in_rd_wr (inS hp h ho)

/-! ## Loads -/

section
variable {rest : List Instr} {Q : State → Prop}

/-- After the first `n` stores of vectors `x r` at `p + base r`, in a region of `len` bytes at `p`. -/
structure SInvN (len : Nat) (p : Addr) (base : Nat → Nat) (x : Nat → BitVec 128) (s : State) (n : Nat)
    (w : State) : Prop where
  gpr : w.gpr = s.gpr
  v : w.v = s.v
  keep : Keep [] s w
  frame : Frame [⟨p, len⟩] s.mem w.mem
  st : ∀ r < n, w.mem.read (p + BitVec.ofNat 64 (base r)) 16 = x r
  other : ∀ o k, o + k ≤ len → (∀ r < n, o + k ≤ base r ∨ base r + 16 ≤ o) →
    w.mem.read (p + BitVec.ofNat 64 o) k = s.mem.read (p + BitVec.ofNat 64 o) k

/-- `SInvN` in a region of 1024 bytes. -/
abbrev SInv := SInvN 1024

/-- Stores of the vectors `v` into a region of `len` bytes at `p`, at offsets `base r`, through `x`,
apart from each other. -/
theorem wp_storesN (len : Nat) (hlen : len < 2 ^ 64) {s : State} {p : Addr} {xr : Reg} {vr : Nat → VReg}
    {off base : Nat → Nat} {N : Nat}
    (hx : ∀ r < N, s.gpr xr + BitVec.ofNat 64 (off r) = p + BitVec.ofNat 64 (base r))
    (ho : ∀ r < N, off r % 16 = 0 ∧ off r < 4096 * 16) (hb : ∀ r < N, base r + 16 ≤ len)
    (hsep : ∀ r < N, ∀ r' < N, r ≠ r' → base r + 16 ≤ base r' ∨ base r' + 16 ≤ base r)
    (hin : ∀ r < N, InRegions s.wr (p + BitVec.ofNat 64 (base r)) 16)
    (k : ∀ s', SInvN len p base (fun r => s.v (vr r)) s N s' → WP isa (.block rest) s' Q) :
    WP isa (.block (((List.range N).map fun r => Instr.strq (vr r) xr (off r)) ++ rest)) s Q := by
  rw [List.map_eq_flatMap, WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (SInvN len p base (fun r => s.v (vr r)) s) (fun r w hr h => ?_) N
    (Nat.le_refl _) s ⟨rfl, rfl, Keep.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ _ _ _ => rfl⟩) fun s' h => k s' h
  refine wp_strq (a := p + BitVec.ofNat 64 (base r)) (ho r hr) (by rw [h.gpr]; exact hx r hr)
    (by rw [h.keep.wr]; exact hin r hr) fun w₁ h₁ => wp_nil ?_
  have hbr := hb r hr
  refine ⟨by rw [h₁.gpr, h.gpr], by rw [h₁.v, h.v], h.keep.trans h₁.keep |>.mono, ?_, fun r' hr' => ?_,
    fun o k ho' hs => ?_⟩
  · rw [h₁.mem]; exact h.frame.write (List.mem_singleton_self _) _ (contains_off hbr hlen)
  · rw [h₁.mem, h.v]
    by_cases e : r' = r
    · subst e; exact read_write16 _ _ _
    · have := hb r' (by omega)
      rw [Mem.read_write_sep (sep_off _ (hsep r' (by omega) r hr e) (by omega) (by omega)) (by decide)]
      exact h.st r' (by omega)
  · rw [h₁.mem, Mem.read_write_sep (sep_off _ (hs r (by omega)) (by omega) (by omega)) (by omega)]
    exact h.other o k ho' fun r' hr' => hs r' (by omega)

/-- `wp_storesN` in a region of 1024 bytes. -/
theorem wp_stores {s : State} {p : Addr} {xr : Reg} {vr : Nat → VReg} {off base : Nat → Nat} {N : Nat}
    (hx : ∀ r < N, s.gpr xr + BitVec.ofNat 64 (off r) = p + BitVec.ofNat 64 (base r))
    (ho : ∀ r < N, off r % 16 = 0 ∧ off r < 4096 * 16) (hb : ∀ r < N, base r + 16 ≤ 1024)
    (hsep : ∀ r < N, ∀ r' < N, r ≠ r' → base r + 16 ≤ base r' ∨ base r' + 16 ≤ base r)
    (hin : ∀ r < N, InRegions s.wr (p + BitVec.ofNat 64 (base r)) 16)
    (k : ∀ s', SInv p base (fun r => s.v (vr r)) s N s' → WP isa (.block rest) s' Q) :
    WP isa (.block (((List.range N).map fun r => Instr.strq (vr r) xr (off r)) ++ rest)) s Q :=
  wp_storesN 1024 (by decide) hx ho hb hsep hin k

end

theorem getD_rep_lt {n r a : Nat} (hr : r < n) : (List.replicate n a).getD r 0 = a := by
  simp [List.getD_eq_getElem?_getD, hr]

end VG.Proof.MlKem.AArch64.Ntt16
