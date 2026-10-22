module

public import VerifiedGarbage.Impl.RsaPss.X86
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Lay
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Vp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# RSASSA-PSS on x86: where everything is, for the pieces both functions share

`Geo L scr`: the layout `L` (`Proof/RsaPkcs1Sig/X86/Lay.lean`) has our
frame, and our part of `scratch` (`oRsa` bytes at `scr`) lies in one of its
writable buffers. `Ctx L scr σ s`: a state of the body with `scr` in `ebp`.
Every piece of code both functions share is proven from such a state,
keeping any fact about memory that its writes do not reach.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes

/-- Byte `o` of our part of `scratch`. -/
abbrev sa (scr : BitVec 32) (o : Nat) : Addr := scr.setWidth 64 + BitVec.ofNat 64 o

/-- Bytes `o … o + n - 1` of our part of `scratch`. -/
abbrev sR (scr : BitVec 32) (o n : Nat) : Region := ⟨sa scr o, n⟩

/-- A slot of the frame. -/
abbrev slotR (L : Lay) (d : Nat) : Region := ⟨L.fr d, 4⟩

/-- The layout has our frame, and our part of `scratch` lies in one of its
writable buffers. -/
structure Geo (L : Lay) (scr : BitVec 32) : Prop where
  F : L.F = frameBytes
  fit : scr.toNat + oRsa < 2 ^ 32
  sub : ∃ k, oRsa ≤ k ∧ (⟨scr.setWidth 64, k⟩ : Region) ∈ L.rw
  ok : ∃ σ, L.Ok σ
  C48 : 48 ≤ L.C

/-- A state of the body, with `scr` in `ebp`. -/
structure Ctx (L : Lay) (scr : BitVec 32) (σ s : State) : Prop where
  st : L.St σ s
  ebp : s.gpr .ebp = scr

theorem offs : oCW = 0 ∧ oSt = 512 ∧ oSel = 768 ∧ oDig = 832 ∧ oLen = 896 ∧ oEm = 1024 ∧ oY = 2048 ∧
    oRsa = 8192 ∧ frameBytes = 144 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

section
variable {L : Lay} {scr : BitVec 32}

theorem sR0 (scr : BitVec 32) (n : Nat) : sR scr 0 n = ⟨scr.setWidth 64, n⟩ := by
  simp only [sR, sa, BitVec.add_zero]

namespace Geo
variable (hg : Geo L scr)
include hg

theorem scr_lt {o : Nat} (h : o ≤ oRsa) : (scr + BitVec.ofNat 32 o).toNat = scr.toNat + o := by
  have := hg.fit; unfold oRsa at *
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem scrA {o : Nat} (h : o < oRsa) : (scr + BitVec.ofNat 32 o).setWidth 64 = sa scr o :=
  addr_eq (by have := hg.fit; unfold oRsa at *; omega)

theorem addrD {o d : Nat} (h : o + d < oRsa) : VG.X86.addr (scr + BitVec.ofNat 32 o) d = sa scr (o + d) := by
  rw [addr_eq (by rw [hg.scr_lt (by omega)]; have := hg.fit; omega), hg.scrA (by omega), sa,
    BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- A range of our part of `scratch` within a writable buffer. -/
theorem inR {o n : Nat} (h : o + n ≤ oRsa) : ∃ R ∈ L.rw, Region.Sub (sR scr o n) R := by
  obtain ⟨k, hk, hR⟩ := hg.sub
  exact ⟨_, hR, Offset.sub_base _ (by omega)⟩

theorem inW {o n : Nat} (h : o + n ≤ oRsa) : ∃ R ∈ L.W, Region.Sub (sR scr o n) R := by
  obtain ⟨R, hR, hs⟩ := hg.inR h
  exact ⟨R, by simp [Lay.W, hR], hs⟩

/-- Our part of `scratch` misses our stack. -/
theorem stk {σ : State} (ok : L.Ok σ) {o n : Nat} (h : o + n ≤ oRsa) : (sR scr o n).Disjoint L.STK := by
  obtain ⟨R, hR, hs⟩ := hg.inR h
  exact ((ok.stk R (List.mem_append_right _ hR)).sub_right hs).symm

theorem slot {σ : State} (ok : L.Ok σ) {o n d k : Nat} (h : o + n ≤ oRsa) (hd : d + k ≤ L.F + 16) :
    Region.Disjoint ⟨L.fr d, k⟩ (sR scr o n) :=
  ((hg.stk ok h).sub_right (Lay.sub_stk hd)).symm

theorem low {σ : State} (ok : L.Ok σ) {o n : Nat} (h : o + n ≤ oRsa) : (sR scr o n).Disjoint L.LOW :=
  (hg.stk ok h).sub_right Lay.low_stk

/-- And the buffers only read. -/
theorem ro {σ : State} (ok : L.Ok σ) {o n : Nat} (h : o + n ≤ oRsa) {R : Region} (hR : R ∈ L.ro) :
    (sR scr o n).Disjoint R := by
  obtain ⟨W, hW, hs⟩ := hg.inR h
  exact (ok.wro W hW R (List.mem_append_left _ hR)).sub_left hs

theorem wr {σ s : State} (hs : L.St σ s) {o n : Nat} (h : o + n ≤ oRsa) : InRegions s.wr (sa scr o) n := by
  obtain ⟨k, hk, hR⟩ := hg.sub
  exact ⟨_, by rw [hs.wr, hs.ok.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_append_left _ hR)), Offset.contains_base _ (by omega) (by have := hg.fit; unfold oRsa at *; omega)⟩

theorem rd {σ s : State} (hs : L.St σ s) {o n : Nat} (h : o + n ≤ oRsa) :
    InRegions (s.rd ++ s.wr) (sa scr o) n :=
  let ⟨r, hr, hc⟩ := hg.wr hs h
  ⟨r, List.mem_append_right _ hr, hc⟩

omit hg in
/-- Two ranges of our part of `scratch`. -/
theorem sep {o n e k : Nat} (h : o + n ≤ e ∨ e + k ≤ o) (ho : o + n ≤ oRsa) (he : e + k ≤ oRsa) :
    (sR scr o n).Disjoint (sR scr e k) :=
  Offset.disjoint _ h (by unfold oRsa at ho; omega) (by unfold oRsa at he; omega)

end Geo

/-! ## Keeping `Ctx` -/

namespace Ctx

theorem regs {σ s t : State} (h : Ctx L scr σ s) (rd : t.rd = s.rd) (wr : t.wr = s.wr)
    (sp : t.gpr .esp = s.gpr .esp) (bp : t.gpr .ebp = s.gpr .ebp) (m : t.mem = s.mem) : Ctx L scr σ t :=
  ⟨h.st.regs rd wr sp m, bp.trans h.ebp⟩

theorem upd {σ s t : State} (h : Ctx L scr σ s) {d : Reg} {v : BitVec 32} (u : Upd s t d v) (hd : d ≠ .esp)
    (hb : d ≠ .ebp) : Ctx L scr σ t :=
  ⟨h.st.upd u hd, (u.other _ (Ne.symm hb)).trans h.ebp⟩

theorem fupd {σ s t : State} (h : Ctx L scr σ s) (u : Fupd s t) : Ctx L scr σ t :=
  ⟨h.st.fupd u, by rw [u.gpr]; exact h.ebp⟩

/-- Memory changed within regions of what the body may write. -/
theorem write {σ s t : State} (h : Ctx L scr σ s) {rs : List Region} (hf : Frame rs s.mem t.mem)
    (hs : ∀ r ∈ rs, ∃ R ∈ L.W, Region.Sub r R) (rd : t.rd = s.rd) (wr : t.wr = s.wr)
    (sp : t.gpr .esp = s.gpr .esp) (bp : t.gpr .ebp = s.gpr .ebp) : Ctx L scr σ t :=
  ⟨h.st.write hf hs rd wr sp, bp.trans h.ebp⟩

end Ctx

end

/-! ## Facts that writes elsewhere keep -/

theorem bytes_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {a : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨a, n⟩ r) (hn : n ≤ 2 ^ 64) {f : Nat → Byte}
    (h : ∀ i < n, m (a + BitVec.ofNat 64 i) = f i) : ∀ i < n, m' (a + BitVec.ofNat 64 i) = f i :=
  fun i hi => (hf.bytes (R := ⟨a, n⟩) hd hn hi).trans (h i hi)

theorem slot_keep {L : Lay} {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {d : Nat} {v : BitVec 32}
    (hd : ∀ r ∈ rs, (slotR L d).Disjoint r) (h : m.readW (L.fr d) 32 = v) : m'.readW (L.fr d) 32 = v := by
  rw [hf.readW (r := slotR L d) (Region.contains_self _ _) hd (by decide)]; exact h

/-- A byte of our part of `scratch` after a byte is written there. -/
theorem sa_write (scr : BitVec 32) (m : Mem) {o i : Nat} (b : Byte) (ho : o < 2 ^ 64) (hi : i < 2 ^ 64) :
    (m.writeW (sa scr o) b) (sa scr i) = if i = o then b else m (sa scr i) := by
  rw [VG.WriteBytes.writeW8_apply]
  by_cases e : i = o
  · subst e; simp
  · rw [ite_eq_right (Offset.add_ofNat_ne _ hi ho e), ite_eq_right e]

/-- A byte written within a range of our part of `scratch`. -/
theorem frame_byte (scr : BitVec 32) (m : Mem) {o n x : Nat} (b : Byte) (h₁ : o ≤ x) (h₂ : x < o + n)
    (hn : o + n < 2 ^ 64) : Frame [sR scr o n] m (m.writeW (sa scr x) b) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ h₁ (by omega) (by omega))

/-- Bytes of our part of `scratch` kept by writes elsewhere. -/
theorem sbytes_keep {scr : BitVec 32} {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {o n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint (sR scr o n) r) (hn : o + n < 2 ^ 64) {f : Nat → Byte}
    (h : ∀ i < n, m (sa scr (o + i)) = f i) : ∀ i < n, m' (sa scr (o + i)) = f i := fun i hi => by
  rw [← h i hi]
  refine hf _ fun r hr hc => hd r hr _ (Offset.contains _ (Nat.le_add_right _ _) (by omega) (by omega)) hc

/-- A piece from no state. -/
theorem VP.empty {F G : State → State → Prop} {c : Prog isa} (h : ∀ σ s, ¬ F σ s) : VP F c G :=
  ⟨fun σ s hs => (h σ s hs).elim, fun _ _ _ _ _ _ ⟨σ, _, hs, _⟩ => (h σ _ hs).elim⟩

end VG.Proof.RsaPss.X86
