module

public import VerifiedGarbage.Proof.X25519.AArch64.Hybrid.Fields
public import VerifiedGarbage.Proof.X25519.AArch64.Word.Ladder
import VerifiedGarbage.Proof.Ed25519.AArch64.Swap
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# X25519 on AArch64: the hybrid ladder's iterations

Untrusted: everything here is checked by Lean. One iteration
(`Hybrid.step`) is the four-word step's prefix and conditional swaps, then
`stepFields`, which computes the same formulas (`step_ok`); the ladder runs it
255 times (`ladder_ok`). The iterations change memory only in the slots, the
swap word and the vector buffers (`HLoopKeep`), so the constants of the
products stay.
-/

@[expose] public section

namespace VG.Proof.X25519.AArch64.Hybrid

open VG VG.AArch64 VG.Spec.X25519 VG.Proof.X25519
open VG.Impl.Ed25519.AArch64 (Slot offset)
open VG.Proof.Ed25519.AArch64 (Keep env F Outside ofs clob word off ofs_off' Keeps Small)
open VG.Proof.X25519.AArch64.Word (LoopKeep Good core swapped formula_ok bitOffset
  setCounter_ok)

/-- What the hybrid ladder keeps: `Word.LoopKeep`, with the vector buffers too. -/
structure HLoopKeep (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ∉ clob → r ≠ .x19 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : Outside base 64 1040 s.mem t.mem

theorem HLoopKeep.refl (base : Addr) (s : State) : HLoopKeep base s s :=
  ⟨fun _ _ _ => rfl, rfl, rfl, rfl, VG.Proof.Ed25519.AArch64.Outside.refl _ _ _ _⟩

theorem HLoopKeep.trans {base : Addr} {s t u : State} (h : HLoopKeep base s t) (k : HLoopKeep base t u) :
    HLoopKeep base s u :=
  ⟨fun r hr hc => (k.gpr r hr hc).trans (h.gpr r hr hc), k.rd.trans h.rd, k.wr.trans h.wr, k.sp.trans h.sp,
    h.mem.trans k.mem⟩

theorem HLoopKeep.of_loop {base : Addr} {s t : State} (h : LoopKeep base s t) : HLoopKeep base s t :=
  ⟨h.gpr, h.rd, h.wr, h.sp, h.mem.mono (by decide) (by decide)⟩

theorem HLoopKeep.of_fkeep {base : Addr} {s t : State} (h : FKeep base s t) : HLoopKeep base s t :=
  ⟨fun r hr _ => h.gpr r hr, h.rd, h.wr, h.sp, h.mem.outside⟩

theorem HLoopKeep.scratch {base : Addr} {s t : State} (h : HLoopKeep base s t) (hs : Scratch s base) :
    Scratch t base :=
  ⟨(h.gpr _ (by decide) (by decide)).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap⟩

theorem HLoopKeep.consts {base : Addr} {s t : State} (h : HLoopKeep base s t) (hc : Consts s.mem base) :
    Consts t.mem base :=
  consts_of_outside h.mem hc

theorem HLoopKeep.bit {base : Addr} {s t : State} (h : HLoopKeep base s t) {i : Nat} (hi : i < 255) :
    t.mem (off base (bitOffset + i)) = s.mem (off base (bitOffset + i)) := by
  apply h.mem
  rw [ofs_off' base (by simp [bitOffset, VG.Impl.X25519.AArch64.Word.BITS, VG.Impl.X25519.AArch64.BITS,
    VG.Impl.X25519.AArch64.slot, VG.Impl.X25519.AArch64.NSLOT]; omega)]
  right
  simp [bitOffset, VG.Impl.X25519.AArch64.Word.BITS, VG.Impl.X25519.AArch64.BITS,
    VG.Impl.X25519.AArch64.slot, VG.Impl.X25519.AArch64.NSLOT]
  omega

theorem HMem.swapWord {base : Addr} {m m' : Mem} (h : HMem base m m') : word m' base 768 = word m base 768 :=
  (Mem.readW_congr fun i hi => (h _ (by rw [VG.Proof.Ed25519.AArch64.ofs_off base (by omega)]; omega)).symm).symm

/-- `swapField_ok`, keeping the slots small when `x` and `y` both are or are not. -/
theorem swapField_okS {s : State} {base : Addr} (hs : Scratch s base)
    (x y : VG.Impl.Ed25519.AArch64.Slot) (hxy : x ≠ y) {sw : Bool} (hm : s.gpr .x3 = VG.Proof.Ed25519.Word64.mask sw)
    {S : VG.Impl.Ed25519.AArch64.Slot → Bool} (hS : Small s.mem base S) (hSxy : S x = S y) :
    WP isa (.block (VG.Impl.Ed25519.AArch64.cswap (offset x) (offset y))) s fun t =>
      Keep base s t ∧ env t.mem base = swapped (env s.mem base) x y sw ∧ t.gpr .x3 = s.gpr .x3 ∧
      Small t.mem base S := by
  have hne : x.val ≠ y.val := fun h => hxy (Fin.ext h)
  have hsep : offset x + 32 ≤ offset y ∨ offset y + 32 ≤ offset x := by
    simp only [offset]; omega
  refine WP.mono (VG.Proof.Ed25519.AArch64.cswap_ok hs
    (VG.Proof.Ed25519.AArch64.slot_rangeWith (large := false) x)
    (VG.Proof.Ed25519.AArch64.slot_rangeWith (large := false) y) hsep hm)
    fun t ⟨hg, hm3, hr, hw, hp, ⟨m, h₁, h₂, hx⟩, tx, ty⟩ => ?_
  refine ⟨⟨hg, hr, hw, hp, (h₁.mono (by simp [offset]) (by simp only [offset]; omega)).trans
    (h₂.mono (by simp [offset]) (by simp only [offset]; omega))⟩, ?_, hm3, ?_⟩
  · have ex : F m base (offset x) = if sw then env s.mem base y else env s.mem base x := by
      change Proof.X25519.toFe _ = _
      rw [hx]
      cases sw <;> rfl
    have ey : F t.mem base (offset y) = if sw then env s.mem base x else env s.mem base y := by
      change Proof.X25519.toFe _ = _
      rw [ty]
      cases sw <;> rfl
    rw [VG.Proof.Ed25519.AArch64.env_update y h₂, VG.Proof.Ed25519.AArch64.env_update x h₁, ex, ey]
    rfl
  · intro i hi
    by_cases iy : i = y
    · subst iy
      rw [ty]
      cases sw
      · exact hS _ hi
      · exact hS x (hSxy.trans hi)
    · by_cases ix : i = x
      · subst ix
        rw [tx]
        cases sw
        · exact hS _ hi
        · exact hS y (hSxy.symm.trans hi)
      · have hiy : i.val ≠ y.val := fun h => iy (Fin.ext h)
        have hix : i.val ≠ x.val := fun h => ix (Fin.ext h)
        rw [h₂.fe (by simp only [offset]; omega) (by simp only [offset]; omega),
          h₁.fe (by simp only [offset]; omega) (by simp only [offset]; omega)]
        exact hS i hi

theorem step_ok {base : Addr} {s : State} {k : Nat} {x1 : Fe} {st : Ladder} {i : Nat}
    (hs : Scratch s base) (hc : Consts s.mem base) (hi : i < 255) (hg : Good (env s.mem base) x1 st)
    (hsw : st.swap ≤ 1) (hcnt : s.gpr .x19 = BitVec.ofNat 64 (i+1))
    (hw : word s.mem base 768 = BitVec.ofNat 64 st.swap)
    (hb : s.mem (off base (bitOffset+i)) = BitVec.ofNat 8 (VG.Proof.X25519.bit k i))
    (hS : Small s.mem base S14) :
    WP isa (.block VG.Impl.X25519.AArch64.Hybrid.step) s fun t =>
      HLoopKeep base s t ∧ Good (env t.mem base) x1 (ladderStep k x1 st i) ∧
      t.gpr .x19 = BitVec.ofNat 64 i ∧ word t.mem base 768 = BitVec.ofNat 64 (VG.Proof.X25519.bit k i) ∧
      Small t.mem base S14 := by
  simp only [VG.Impl.X25519.AArch64.Hybrid.step, VG.Impl.X25519.AArch64.Word.stepHead,
    VG.Impl.X25519.AArch64.Word.cswap, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.AArch64.Word.prefix_ok hs hi hsw (bit_le k i) hcnt hw hb) fun a ⟨ka, ea, ca, ma, wa, oa⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (swapField_okS (ka.scratch hs) 1 3 (by decide) ma (hS.frame oa (by decide)) (by decide))
    fun b ⟨kb, eb, mb, sb⟩ => ?_
  have kab : LoopKeep base s b := ka.trans (LoopKeep.of_field kb)
  rw [WP.block_append_iff]
  refine WP.mono (swapField_okS (kab.scratch hs) 2 4 (by decide) (mb.trans ma) sb (by decide))
    fun c ⟨kc, ec, _, sc⟩ => ?_
  have kac : LoopKeep base s c := kab.trans (LoopKeep.of_field kc)
  have hcc : Consts c.mem base := (HLoopKeep.of_loop kac).consts hc
  refine WP.mono (stepFields_ok (kac.scratch hs) hcc (by rw [ec, eb, ea]; exact hg.2.2.2.2.2) sc)
    fun t ⟨kt, _, e1, e2, e3, e4, e0, e18, smt⟩ => ?_
  refine ⟨(HLoopKeep.of_loop kac).trans (HLoopKeep.of_fkeep kt), ?_, ?_, ?_, smt⟩
  · have := formula_ok (env s.mem base) k x1 st i hg
    have hcore := VG.Proof.X25519.AArch64.Word.stepOps_eval
      (swapped (swapped (env s.mem base) 1 3 ((st.swap ^^^ VG.Proof.X25519.bit k i) == 1)) 2 4
        ((st.swap ^^^ VG.Proof.X25519.bit k i) == 1))
    have hE : env c.mem base = swapped (swapped (env s.mem base) 1 3 ((st.swap ^^^ VG.Proof.X25519.bit k i) == 1)) 2 4
        ((st.swap ^^^ VG.Proof.X25519.bit k i) == 1) := by rw [ec, eb, ea]
    obtain ⟨g0, g1, g2, g3, g4, g18⟩ := this
    obtain ⟨c1, c2, c3, c4, c0, c18⟩ := hcore
    rw [hE] at e1 e2 e3 e4 e0 e18
    exact ⟨e0.trans (c0.symm.trans g0), e1.trans (c1.symm.trans g1), e2.trans (c2.symm.trans g2),
      e3.trans (c3.symm.trans g3), e4.trans (c4.symm.trans g4), e18.trans (c18.symm.trans g18)⟩
  · rw [kt.gpr _ (by decide), kc.gpr _ (by decide), kb.gpr _ (by decide), ca]
  · rw [kt.mem.swapWord, kc.mem.word (Or.inr (by decide : 64+704 ≤ 768)) (by decide : 768+8<2^64),
      kb.mem.word (Or.inr (by decide : 64+704 ≤ 768)) (by decide : 768+8<2^64), wa]


/-- The loop's invariant. -/
def LInv (base : Addr) (s₀ : State) (k : Nat) (x1 : Fe) (n : Nat) (s : State) : Prop :=
  HLoopKeep base s₀ s ∧ Good (env s.mem base) x1 (ladderAfter k x1 n) ∧
  s.gpr .x19 = BitVec.ofNat 64 n ∧ word s.mem base 768 = BitVec.ofNat 64 (ladderAfter k x1 n).swap ∧
  Small s.mem base S14

theorem ladder_ok {base : Addr} {s : State} {k : Nat} {x1 : Fe} (hs : Scratch s base) (hc : Consts s.mem base)
    (hg : Good (env s.mem base) x1 (init x1)) (hw : word s.mem base 768 = 0)
    (hb : ∀ i < 255, s.mem (off base (bitOffset+i)) = BitVec.ofNat 8 (VG.Proof.X25519.bit k i))
    (hS : Small s.mem base S14) :
    WP isa VG.Impl.X25519.AArch64.Hybrid.ladder s fun t =>
      HLoopKeep base s t ∧ Good (env t.mem base) x1 (ladderAfter k x1 0) ∧
      word t.mem base 768 = BitVec.ofNat 64 (ladderAfter k x1 0).swap := by
  refine WP.seq (WP.mono (setCounter_ok s 255) fun a ⟨ac, ka⟩ => ?_)
  have kla : HLoopKeep base s a := HLoopKeep.of_loop (LoopKeep.of_keeps ka (by decide))
  refine WP.loop (M := isa) (fun n t => 1 ≤ n ∧ n ≤ 255 ∧ LInv base s k x1 n t)
    ?_ 255 a ⟨by decide, by decide, kla, by simpa [ka.mem, ladderAfter_255] using hg, ac,
      by rw [ka.mem, ladderAfter_255]; exact hw, by rw [ka.mem]; exact hS⟩
  intro n t ⟨h1, h255, kt, gt, ct, wt, st⟩
  obtain ⟨i, rfl⟩ : ∃ i, n = i+1 := ⟨n-1, by omega⟩
  refine WP.mono (step_ok (k := k) (kt.scratch hs) (kt.consts hc) (by omega) gt
    (ladderAfter_swap_le _ _ (by omega)) ct wt (by rw [kt.bit (by omega)]; exact hb i (by omega)) st)
    fun u ⟨ku, gu, cu, wu, su⟩ => ?_
  have klu : HLoopKeep base s u := kt.trans ku
  rw [← ladderAfter_step k x1 (by omega)] at gu
  have ws : word u.mem base 768 = BitVec.ofNat 64 (ladderAfter k x1 i).swap := by
    rw [ladderAfter_step k x1 (by omega)]
    exact wu
  have he : isa.eval (.nonzero .x .x19) u = some (decide (i ≠ 0)) := by
    simp only [eval, VG.Proof.Ed25519.AArch64.read_x, cu, VG.Proof.Ed25519.AArch64.counter_nonzero (by omega : i < 2^64)]
  by_cases hi : i = 0
  · subst i; exact .inl ⟨by rw [he]; rfl, klu, gu, ws⟩
  · exact .inr ⟨by rw [he]; simp [hi], i, by omega, by omega, by omega, klu, gu, cu, ws, su⟩

end VG.Proof.X25519.AArch64.Hybrid
