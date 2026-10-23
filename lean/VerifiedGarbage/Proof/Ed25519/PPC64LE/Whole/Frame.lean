module

public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Whole
public import VerifiedGarbage.Proof.X25519.PPC64LE.Instr
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Ed25519.PPC64LE.ScalarBase
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Ed25519's whole functions on PPC64LE: the saved registers

Each function saves the registers `rs` it uses and the link register in the
slots at `o(F)` (`slots o rs`), and keeps the values `v` it needs across calls
in `rs`. `Inv` is what holds between the steps of its body: the permissions
and the stack pointer of the entry state `s`, the registers, our caller's
other nonvolatile registers, the slots, and that memory changed only within
`W` (`save_ok`, `Inv.step`). `restore_ok` restores the registers and `lr`.
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE.Whole

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE.Whole VG.Proof.X25519.PPC64LE

/-- What the slots hold: the link register in `r0`'s, the registers on entry in the others. -/
def saveG (s : State) (r : Reg) : BitVec 64 := if r = .r0 then s.lr else s.gpr r

/-- The area of the slots. -/
abbrev slotArea (F : Addr) (o : Nat) (rs : List Reg) : Region := ⟨F + BitVec.ofNat 64 o, 8 * (rs.length + 1)⟩

/-- Between the steps of a body that started in `s`. -/
structure Inv (s : State) (F : Addr) (o : Nat) (rs : List Reg) (v : Reg → BitVec 64) (W : List Region)
    (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  regs : ∀ r ∈ rs, t.gpr r = v r
  pres : ∀ r ∈ preserved, r ∉ rs → t.gpr r = s.gpr r
  saved : Spill.Saved F (saveG s) (slots o rs) t.mem
  frame : Frame W s.mem t.mem

theorem slots_in (o : Nat) (rs : List Reg) : ∀ p ∈ slots o rs, o ≤ p.2 ∧ p.2 + 8 ≤ o + 8 * (rs.length + 1) := by
  intro p hp
  obtain ⟨⟨r, i⟩, hm, rfl⟩ := List.mem_map.mp hp
  have := (List.mem_zipIdx hm).2.1
  simp only [List.length_append, List.length_singleton, Nat.zero_add] at this
  dsimp only
  omega

/-- A step that keeps the registers our caller keeps and writes only within `W` and outside the
slots. -/
theorem Inv.step {s t t' : State} {F : Addr} {o : Nat} {rs : List Reg} {v : Reg → BitVec 64} {W Wc : List Region}
    (h : Inv s F o rs v W t) (hrs : ∀ r ∈ rs, r ∈ preserved) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hsp : t'.sp = t.sp) (hg : ∀ r ∈ preserved, t'.gpr r = t.gpr r) (hf : Frame Wc t.mem t'.mem)
    (hsub : ∀ r ∈ Wc, ∃ R ∈ W, Region.Sub r R) (hd : ∀ r ∈ Wc, Region.Disjoint (slotArea F o rs) r) :
    Inv s F o rs v W t' where
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  sp := hsp.trans h.sp
  regs r hr := (hg r (hrs r hr)).trans (h.regs r hr)
  pres r hr hn := (hg r hr).trans (h.pres r hr hn)
  saved := h.saved.frame_in (slots_in o rs) hf hd
  frame := h.frame.trans (hf.sub hsub)

/-! ## Saving -/

theorem saveRegs_eq (f : Reg) (o : Nat) (rs : List Reg) :
    saveRegs f o rs = .mflr .r0 :: Spill.saveCode f (slots o rs) := rfl

/-- The saves, at `o(F)` with `F` in `f`, then `rest`. -/
theorem save_ok {s : State} {f : Reg} {o : Nat} {rs : List Reg} {rest : List Instr} {Q : State → Prop}
    (hf0 : f ≠ .r0) (hfits : Spill.Fits (slots o rs)) (hlo : o + 8 * (rs.length + 1) < 2 ^ 64)
    (hin : ∀ p ∈ slots o rs, InRegions s.wr (s.gpr f + BitVec.ofNat 64 p.2) 8)
    (k : ∀ u, Rest [.r0] s u → u.lr = s.lr → Spill.Saved (s.gpr f) (saveG s) (slots o rs) u.mem →
      Frame [slotArea (s.gpr f) o rs] s.mem u.mem → WP isa (.block rest) u Q) :
    WP isa (.block (saveRegs f o rs ++ rest)) s Q := by
  rw [saveRegs_eq, List.cons_append]
  refine wp_mflr fun u hu hl => Spill.save_ok hf0 hfits.1 (fun p hp => by rw [hu.wr, hu.other f hf0]; exact hin p hp) ?_
  have e : u.gpr f = s.gpr f := hu.other f hf0
  refine k _ ⟨fun r hr => hu.other r (by simpa using hr), hu.rd, hu.wr, hu.sp⟩ hl ?_ ?_
  · intro p hp
    rw [e]
    have := Spill.saveMem_saved hfits u.mem (s.gpr f) u.gpr p hp
    rw [this, saveG]
    by_cases h0 : p.1 = .r0
    · rw [h0, hu.gpr]; simp only [↓reduceIte]
    · rw [hu.other _ h0]; simp only [h0, ↓reduceIte]
  · show Frame _ s.mem (Spill.saveMem u.mem (u.gpr f) u.gpr (slots o rs))
    rw [← hu.mem, e]
    exact Spill.saveMem_frame (slots_in o rs) hlo _ _ _

/-! ## Restoring -/

/-- The restores, of `lr` first. -/
def restoreList (o : Nat) (rs : List Reg) : List (Reg × Nat) := (.r0, o + 8 * rs.length) :: (slots o rs).dropLast

theorem restoreRegs_eq (f : Reg) (o : Nat) (rs : List Reg) :
    restoreRegs f o rs = Spill.restoreCode f (restoreList o rs) ++ ([.mtlr .r0] : List Instr) := rfl

theorem r0_pres : Reg.r0 ∉ preserved := by decide

/-- Restoring the registers and `lr`, `F` in `f`, the last of `rs`. -/
theorem restore_ok {s t : State} {F : Addr} {f : Reg} {o : Nat} {rs : List Reg} {v : Reg → BitVec 64}
    {W : List Region} (h : Inv s F o rs v W t) (hf0 : f ≠ .r0) (hf : t.gpr f = F)
    (hfits : ∀ p ∈ restoreList o rs, p.2 % 8 = 0 ∧ p.2 < 32768) (hr : Spill.Restorable f (restoreList o rs))
    (hsub : ∀ p ∈ restoreList o rs, p ∈ slots o rs) (hrl : (restoreList o rs).map Prod.fst = .r0 :: rs)
    (hin : ∀ p ∈ restoreList o rs, InRegions (t.rd ++ t.wr) (F + BitVec.ofNat 64 p.2) 8) {Q : State → Prop}
    (k : ∀ t', (∀ r ∈ preserved, t'.gpr r = s.gpr r) → t'.sp = s.sp → t'.lr = s.lr → t'.mem = t.mem →
      (∀ r, r ≠ .r0 → r ∉ rs → t'.gpr r = t.gpr r) → Q t') :
    WP isa (.block (restoreRegs f o rs)) t Q := by
  rw [restoreRegs_eq]
  refine Spill.restore_ok hf0 hf hfits hr hin (h.saved.sub hsub) fun u hu => wp_mtlr (WP.block_nil ?_)
  have hm : ∀ r, r ∈ (restoreList o rs).map Prod.fst → u.gpr r = saveG s r := fun r hr' =>
    hu.gpr_of (.inl hr')
  refine k _ (fun r hr' => ?_) (hu.sp.trans h.sp) ?_ hu.mem fun r h0 hn => hu.other r ?_
  · by_cases hn : r ∈ rs
    · show u.gpr r = s.gpr r
      have h0 : r ≠ .r0 := fun e => r0_pres (e ▸ hr')
      rw [hm r (by rw [hrl]; exact List.mem_cons_of_mem _ hn), saveG]
      simp only [h0, ↓reduceIte]
    · show u.gpr r = s.gpr r
      have h0 : r ≠ .r0 := fun e => r0_pres (e ▸ hr')
      have hn' : r ∉ (restoreList o rs).map Prod.fst := by
        rw [hrl]; simp only [List.mem_cons, not_or]; exact ⟨h0, hn⟩
      rw [hu.other r hn']
      exact h.pres r hr' hn
  · show u.gpr .r0 = s.lr
    rw [hm .r0 (by rw [hrl]; exact List.mem_cons_self), saveG]; simp only [↓reduceIte]
  · rw [hrl]; simp only [List.mem_cons, not_or]; exact ⟨h0, hn⟩

/-- Bytes outside the regions a frame writes. -/
theorem bytes_keep {W : List Region} {m m' : Mem} (hf : Frame W m m') {p : Addr} {n : Nat}
    (hn : n < 2 ^ 64) (hd : ∀ r ∈ W, Region.Disjoint ⟨p, n⟩ r) :
    Spec.Ed25519.bytesAt m' p n = Spec.Ed25519.bytesAt m p n := by
  simp only [Spec.Ed25519.bytesAt]
  refine List.map_congr_left fun i hi => hf _ fun r hr hc => ?_
  have hi' := List.mem_range.mp hi
  exact hd r hr _ (Offset.contains_base p (by omega) (by omega)) hc

end VG.Proof.Ed25519.PPC64LE.Whole
