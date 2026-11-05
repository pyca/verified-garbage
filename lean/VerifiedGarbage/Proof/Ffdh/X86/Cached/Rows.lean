module

public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops
public import VerifiedGarbage.Proof.Mont.X86.Csub
public import VerifiedGarbage.Impl.Bignum.X86.CrtRt
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops2
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-!
# FFDH's key-generation context on i686: copying its rows

A row of the context and a slot of the working space are copied, either way,
by `selectLoop` under a mask (`selectLoop_far_ok`): the source is any
readable span, apart from the destination, a span of a writable region.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cached

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Bignum.X86.PublicRt (countLoop ptr4)

/-- Memory changed only in `[d, d + n)` of `D` is framed by that span. -/
theorem Outside.frame_span {D : Addr} {d n : Nat} {m m' : Mem} (h : Outside D d n m m')
    (hn : D.toNat + d + n ≤ 2 ^ 64) : Frame [⟨off D d, n⟩] m m' := by
  intro x hx
  have hc := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at hc
  refine h x (Classical.byContradiction fun hne => hc ?_)
  have h₁ : d ≤ ofs D x := by omega
  have h₂ : ofs D x < d + n := by omega
  have e : (x - off D d).toNat = ofs D x - d := by
    simp only [ofs, off]
    rw [← BitVec.sub_sub]
    rw [BitVec.toNat_sub_of_le]
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    · rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact h₁
  omega

/-- A word read apart from a span that changed. -/
theorem Outside.readW_far {D : Addr} {d n : Nat} {m m' : Mem} (h : Outside D d n m m')
    (hn : D.toNat + d + n ≤ 2 ^ 64) {a : Addr} (ha : Region.Disjoint ⟨a, 4⟩ ⟨off D d, n⟩) :
    m'.readW a 32 = m.readW a 32 :=
  (Outside.frame_span h hn).readW (r := ⟨a, 4⟩) (Region.contains_self _ _)
    (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact ha) (by decide)

/-- `[r + 0]` for `r = S + x`, `S + x + 4` within 32 bits. -/
theorem ea_far {s : State} {S : Addr} {r : Reg} {x : Nat} (hp : PtrAt s S r x)
    (hx : S.toNat + x + 4 ≤ 2 ^ 32) : s.ea (at_ r 0) = off S x := by
  rw [at_, ea_mk, addr_eq (by omega)]
  apply BitVec.eq_of_toNat_eq
  simp only [off, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have hS : S.toNat < 2 ^ 64 := S.isLt
  rw [Nat.mod_eq_of_lt (a := (s.gpr r).toNat) (by have := (s.gpr r).isLt; omega), hp]
  repeat rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- A readable span at `S + x`. -/
structure Span (s : State) (S : Addr) (x n : Nat) : Prop where
  read : InRegions (s.rd ++ s.wr) (off S x) n
  fit : S.toNat + x + n ≤ 2 ^ 32

theorem Span.of_keeps {s t : State} {S : Addr} {x n : Nat} {rs : List Reg} (h : Span s S x n) (K : Keeps rs s t) :
    Span t S x n := ⟨by rw [K.2.1, K.2.2]; exact h.read, h.fit⟩

theorem Span.sub {s : State} {S : Addr} {x n : Nat} (h : Span s S x n) {y k : Nat} (hy : x ≤ y)
    (hk : y + k ≤ x + n) : Span s S y k := by
  refine ⟨?_, by have := h.fit; omega⟩
  have := VG.CallLay.inRegions_sub h.read (off := y - x) (l := k) (by omega) (by have := h.fit; omega)
  rwa [show off S x + BitVec.ofNat 64 (y - x) = off S y by
    rw [off, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega] at this

/-- A load through `r = S + x` of a readable span. -/
theorem readSrc_far {s : State} {S : Addr} {r : Reg} {x : Nat} (hp : PtrAt s S r x) (hs : Span s S x 4) :
    readSrc s (.mem (at_ r 0)) = some (s.mem.readW (off S x) 32) := by
  show s.load32 (s.ea (at_ r 0)) = _
  rw [ea_far hp hs.fit, State.load32, ite_eq_left_iff.mpr fun h => absurd hs.read h]

/-- `selectLoop`: the destination's `N` words (at `D + d`, of a writable
region) set to the source's (a readable span at `S + x`, apart from them)
where the mask `ecx` is all ones, else kept. -/
theorem selectLoop_far_ok {t₀ : State} {D S : Addr} {L : Nat} (hw : Ws t₀ D L) {x d N : Nat} (k : Bool)
    (hN : 0 < N) (hs : Span t₀ S x (4 * N)) (hd : d + 4 * N ≤ L)
    (hdx : Region.Disjoint ⟨off S x, 4 * N⟩ ⟨off D d, 4 * N⟩)
    (hebp : PtrAt t₀ S .ebp x) (hebx : PtrAt t₀ D .ebx d)
    (hedi : (t₀.gpr .edi).toNat = 4 * N) (hecx : t₀.gpr .ecx = cmask k) :
    WP isa VG.Impl.Bignum.X86.CrtRt.selectLoop t₀
      fun u => Outside D d (4 * N) t₀.mem u.mem ∧
        val32 u.mem D d N = (if k then val32 t₀.mem S x N else val32 t₀.mem D d N) ∧
        PtrAt u D .ebx (d + 4 * N) ∧ PtrAt u S .ebp (x + 4 * N) ∧ Keeps [.eax, .ebx, .edx, .ebp, .edi] t₀ u := by
  have hn := hw.nowrap
  have hsf := hs.fit
  unfold VG.Impl.Bignum.X86.CrtRt.selectLoop
  refine WP.mono (countLoop hN (fun j t => Keeps [.eax, .ebx, .edx, .ebp, .edi] t₀ t ∧
      PtrAt t S .ebp (x + 4 * j) ∧ PtrAt t D .ebx (d + 4 * j) ∧ (t.gpr .edi).toNat = 4 * (N - j) ∧
      Outside D d (4 * j) t₀.mem t.mem ∧
      val32 t.mem D d j = (if k then val32 t₀.mem S x j else val32 t₀.mem D d j)) ?_
    ⟨Keeps.refl _ _, by simpa using hebp, by simpa using hebx, by simpa using hedi, Outside.refl _ _ _ _,
      by cases k <;> rfl⟩) fun u ⟨K, pe, P, _, O, V⟩ => ⟨O, V, P, pe, K⟩
  rintro j t hj ⟨Kt, ebp, ebx, edi, O, V⟩
  have ht := hw.of_keeps Kt
  have ecx : t.gpr .ecx = cmask k := by rw [Kt.1 _ (by decide)]; exact hecx
  have sj : Span t S (x + 4 * j) 4 := (hs.of_keeps Kt).sub (by omega) (by omega)
  have xw : t.mem.readW (off S (x + 4 * j)) 32 = t₀.mem.readW (off S (x + 4 * j)) 32 :=
    Outside.readW_far (n := 4 * N) (O.mono (Nat.le_refl _) (by omega)) (by omega)
      (hdx.sub_left (Offset.sub S (by omega) (by omega)))
  have dw : w32 t.mem D (d + 4 * j) = w32 t₀.mem D (d + 4 * j) :=
    O.w32 (by omega_using []) (by omega_using [hd, hj, hn])
  refine wp_movS (readSrc_ptr ht ebx (d := 0) (by omega_using [hd, hj])) fun s₁ u₁ _ => ?_
  have ebp₁ : PtrAt s₁ S .ebp (x + 4 * j) := by rw [PtrAt, u₁.other _ (by decide)]; exact ebp
  refine wp_movS (readSrc_far ebp₁ (sj.of_keeps u₁.keeps)) fun s₂ u₂ _ => ?_
  refine wp_logicS (.inr rfl) rfl fun s₃ u₃ => ?_
  refine wp_logicS (.inl rfl) rfl fun s₄ u₄ => ?_
  refine wp_logicS (.inr rfl) rfl fun s₅ u₅ => ?_
  have K₅ : Keeps [.eax, .edx] t s₅ :=
    (((u₁.keeps.mono (by decide)).widen u₂.keeps).widen u₃.keeps |>.widen u₄.keeps).widen u₅.keeps
  have ht₅ := ht.of_keeps K₅
  have ebx₅ : PtrAt s₅ D .ebx (d + 4 * j) := by rw [PtrAt, K₅.1 _ (by decide)]; exact ebx
  refine wp_storeS (ea_ptr ht₅ ebx₅ (d := 0) (by omega_using [hd, hj]))
    (ws_write ht₅ (y := d + 4 * j + 0) (n := 4) (by omega_using [hd, hj])) fun s₆ m₆ => ?_
  refine wp_addS rfl fun s₇ u₇ _ => wp_addS rfl fun s₈ u₈ _ => wp_subZ rfl fun s₉ u₉ z₉ => WP.block_nil ?_
  obtain ⟨c₁, c₂⟩ := count_zf edi hj
  have r₆ : ∀ r, r = .ebp ∨ r = .ebx ∨ r = .edi → s₆.gpr r = t.gpr r := by
    intro r hr; rw [m₆.gpr]; apply K₅.1; rcases hr with rfl | rfl | rfl <;> decide
  have mem₅ : s₅.mem = t.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have ecx₃ : s₃.gpr .ecx = t.gpr .ecx := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have eax₅ : s₅.gpr .eax = t.mem.readW (off D (d + 4 * j)) 32 ^^^
      ((t.mem.readW (off S (x + 4 * j)) 32 ^^^ t.mem.readW (off D (d + 4 * j)) 32) &&&
        (if k then BitVec.allOnes 32 else 0)) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₄.gpr, ecx₃, ecx, u₃.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), u₂.gpr, u₁.gpr, u₁.mem, Nat.add_zero]
    rfl
  rw [select_val] at eax₅
  refine ⟨⟨Kt.trans ((((K₅.mono (by decide)).widen (m₆.keeps [])).widen u₇.keeps |>.widen u₈.keeps).widen u₉.keeps),
    ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [PtrAt, u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, r₆ _ (.inl rfl)]
    rw [VG.Proof.Mont.X86.Rt.ptr_add ebp]; congr 1
  · rw [PtrAt, u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), r₆ _ (.inr (.inl rfl))]; exact ptr4 ebx
  · rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), r₆ _ (.inr (.inr rfl))]; exact c₁
  · rw [u₉.mem, u₈.mem, u₇.mem, m₆.mem, mem₅, Nat.add_zero]
    exact (O.mono (Nat.le_refl _) (by omega_using [])).trans
      ((writeW32_outside _ _ _ (by omega_using [hd, hj, hn])).mono (by omega_using []) (by omega_using []))
  · rw [u₉.mem, u₈.mem, u₇.mem, m₆.mem, mem₅, Nat.add_zero, val32_store hn (by omega_using [hd, hj]), V, eax₅,
      val32_succ t₀.mem S x, val32_succ t₀.mem D d]
    have xw' : (t.mem.readW (off S (x + 4 * j)) 32).toNat = w32 t₀.mem S (x + 4 * j) := by rw [xw]
    have dw' : (t.mem.readW (off D (d + 4 * j)) 32).toNat = w32 t₀.mem D (d + 4 * j) := dw
    cases k
    · simp only [Bool.false_eq_true, ite_false, dw']
    · simp only [ite_true, xw']
  · rw [z₉, u₈.other _ (by decide), u₇.other _ (by decide), r₆ _ (.inr (.inr rfl)), c₂]

end VG.Proof.Ffdh.X86.Cached
