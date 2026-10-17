module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Hmac
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Words32
import VerifiedGarbage.Proof.Pbkdf2.Whole.Common
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.X25519.X86.Column

/-!
# Deterministic ECDSA on x86 (32-bit): `h = bits2octets(digest)`

The digest's leftmost `4 k` bytes, big-endian in `k` 32-bit words (`Xw`,
`k = 2 w`), less `n` (its words `nWn`) if that does not borrow: the words go
to `h`'s place, and those of the difference (`Dw`, with the borrows `cb`) to
`K`'s (`subWord_ok`); a mask of the last borrow selects, word by word, the
digest's word or the difference's, stored big-endian into `h`
(`selWord_ok`). As the number is below `2^(32 k) < 2n`, this is it modulo
`n` (`mod_mathK`, `reduce_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Ecdsa.Rfc6979.X86
open VG.Proof.Mont.X86 (wp_movS wp_subS wp_sbbS wp_storeS)
open VG.Impl.Pbkdf2.Stream.X86 (at_)

/-! ## The arithmetic -/

/-- `sbb`'s borrow. -/
theorem sbb32 (a b : BitVec 32) (c : Bool) :
    (a - b - (BitVec.ofBool c).setWidth 32).toNat + b.toNat + c.toNat =
      a.toNat + 2 ^ 32 * (decide (a.toNat < b.toNat + c.toNat)).toNat := by
  have := a.isLt; have := b.isLt; have := Bool.toNat_le c
  have hc : ((BitVec.ofBool c).setWidth 32).toNat = c.toNat := by cases c <;> rfl
  rw [BitVec.toNat_sub, BitVec.toNat_sub, hc]
  by_cases h : a.toNat < b.toNat + c.toNat <;>
    simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega_arith

/-- The `k` words of the digest, at `dg`, least significant first. -/
abbrev Xw (k : Nat) (m : Mem) (dg : Addr) (j : Nat) : BitVec 32 :=
  bswap (m.readW (dg + BitVec.ofNat 64 (4 * (k - 1 - j))) 32)

/-- The borrows of the digest less `N`. -/
def cb (N k : Nat) (m : Mem) (dg : Addr) : Nat → Bool
  | 0 => false
  | j + 1 => decide ((Xw k m dg j).toNat < (nWn N j).toNat + (cb N k m dg j).toNat)

/-- The words of the digest less `N`. -/
abbrev Dw (N k : Nat) (m : Mem) (dg : Addr) (j : Nat) : BitVec 32 :=
  Xw k m dg j - nWn N j - (BitVec.ofBool (cb N k m dg j)).setWidth 32

theorem chain (N k : Nat) (m : Mem) (dg : Addr) : ∀ i,
    wsum (Dw N k m dg) i + wsum (nWn N) i = wsum (Xw k m dg) i + 2 ^ (32 * i) * (cb N k m dg i).toNat
  | 0 => by simp [wsum, cb]
  | i + 1 => by
    have ih := chain N k m dg i
    have e := sbb32 (Xw k m dg i) (nWn N i) (cb N k m dg i)
    simp only [wsum, cb]
    rw [show 32 * (i + 1) = 32 + 32 * i by omega_arith, Nat.pow_add]
    generalize 2 ^ (32 * i) = P at *
    generalize (decide ((Xw k m dg i).toNat < (nWn N i).toNat + (cb N k m dg i).toNat)).toNat = c' at *
    generalize (cb N k m dg i).toNat = c at *
    generalize (Xw k m dg i - nWn N i - (BitVec.ofBool (cb N k m dg i)).setWidth 32).toNat = D at *
    generalize (Xw k m dg i).toNat = X at *
    generalize (nWn N i).toNat = M at *
    grind

/-! ## The code -/

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

theorem nWord_cfgOf (P : RfcHash) (j : Nat) : (cfgOf P).nWord j = nWn P.R.E.C.n j := rfl

theorem w_cfgOf (P : RfcHash) : (cfgOf P).w = P.k32 := rfl

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `bswap d`, keeping the carry. -/
theorem wp_bswapC {d : Reg} (k : ∀ t, Wp.Upd s t d (bswap (s.gpr d)) → t.cf = s.cf → WP isa (.block is) t Q) :
    WP isa (.block (.bswap d :: is)) s Q :=
  cons rfl (k _ (Upd.setReg _ _ _) rfl)

/-- `sub` or `sbb` of an immediate, with the borrow `c` in. -/
theorem wp_subsbb {j : Nat} {v : BitVec 32} {c : Bool} (h0 : j = 0 → c = false) (hc : 0 < j → s.cf = some c)
    (k : ∀ t, Wp.Upd s t .eax (s.gpr .eax - v - (BitVec.ofBool c).setWidth 32) →
      t.cf = some (decide ((s.gpr .eax).toNat < v.toNat + c.toNat)) → WP isa (.block is) t Q) :
    WP isa (.block (.alu (if j = 0 then .sub else .sbb) .eax (.imm v) :: is)) s Q := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have hc0 := h0 rfl; subst hc0
    simp only [ite_true]
    exact wp_subS rfl fun t ut hcf => k t (by simpa using ut) (by simpa using hcf)
  · simp only [show j ≠ 0 by omega_arith, ite_false]
    exact wp_sbbS rfl (hc hj) k

end

/-- `X`, in the frame. -/
abbrev xA {dn : Nat} (L : Lay dn) : Addr := L.B + BitVec.ofNat 64 340

/-- The regions `bits2octets` writes: `K`'s 128 bytes, and `h`'s 64. -/
abbrev HW {dn : Nat} (L : Lay dn) : List Region :=
  [⟨L.B + BitVec.ofNat 64 76, 128⟩, ⟨L.B + BitVec.ofNat 64 272, 64⟩]

/-- After `j` words of the subtraction of `N`'s `k` words, from `t`. -/
structure SubInv (N k : Nat) (L : Lay dn) (g : Reg → BitVec 32) (m₀ : Mem) (t : State) (j : Nat) (u : State) :
    Prop where
  ctx : Ctx L g m₀ u
  frame : Frame (HW L) t.mem u.mem
  x : ∀ i < j, u.mem.readW (L.B + BitVec.ofNat 64 (272 + 4 * (k - 1 - i))) 32 = Xw k t.mem (xA L) i
  d : ∀ i < j, u.mem.readW (L.B + BitVec.ofNat 64 (76 + 4 * (k - 1 - i))) 32 = Dw N k t.mem (xA L) i
  cf : 0 < j → u.cf = some (cb N k t.mem (xA L) j)

theorem fr_sep (B : Addr) {x y : Nat} (h : x + 4 ≤ y ∨ y + 4 ≤ x) (hx : x + 4 ≤ 564) (hy : y + 4 ≤ 564) :
    Mem.Sep (B + BitVec.ofNat 64 x) (32 / 8) (B + BitVec.ofNat 64 y) (32 / 8) :=
  Offset.sep B h (by omega_arith) (by omega_arith)

theorem subWord_ok (hA : P.R.wide = false) (hL : L.Ok) {t u : State} {j : Nat} (hj : j < P.k32)
    (h : SubInv P.R.E.C.n P.k32 L g m₀ t j u) :
    WP isa (.block ((cfgOf P).subWord j)) u (SubInv P.R.E.C.n P.k32 L g m₀ t (j + 1)) := by
  have nB := hL.nB
  have hc := h.ctx
  have hk := (P.sizesA hA).2
  have hx : u.mem.readW (xA L + BitVec.ofNat 64 (4 * (P.k32 - 1 - j))) 32 =
      t.mem.readW (xA L + BitVec.ofNat 64 (4 * (P.k32 - 1 - j))) 32 := by
    rw [Offset.add_add]
    exact h.frame.readW (r := ⟨L.B + BitVec.ofNat 64 340, 64⟩) (Offset.contains _ (by omega_arith) (by omega_arith)
      (by omega_arith)) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)
  have a0 : addr L.F (fX + 4 * (P.k32 - 1 - j)) = xA L + BitVec.ofNat 64 (4 * (P.k32 - 1 - j)) := by
    rw [hL.addrF (by simp only [fX]; omega_arith), Offset.add_add]; simp only [fX]; congr 2; omega_arith
  have a1 : addr L.F (fH + 4 * (P.k32 - 1 - j)) = L.B + BitVec.ofNat 64 (272 + 4 * (P.k32 - 1 - j)) := by
    rw [hL.addrF (by simp only [fH]; omega_arith)]; simp only [fH]; congr 2; omega_arith
  have a2 : addr L.F (fK + 4 * (P.k32 - 1 - j)) = L.B + BitVec.ofNat 64 (76 + 4 * (P.k32 - 1 - j)) := by
    rw [hL.addrF (by simp only [fK]; omega_arith)]; congr 2; simp only [fK]; omega_arith
  simp only [Cfg.subWord, stk, nWord_cfgOf, w_cfgOf]
  refine wp_movS (v := u.mem.readW (xA L + BitVec.ofNat 64 (4 * (P.k32 - 1 - j))) 32)
    (by rw [readSrc_mem hc.esp (by rw [a0, Offset.add_add]; exact hc.inFr (by omega_arith) (by omega_arith) hL), a0])
    fun u₁ v₁ c₁ => wp_bswapC fun u₂ v₂ c₂ => ?_
  rw [v₁.gpr, hx] at v₂
  have esp₂ : u₂.gpr .esp = L.F := by rw [v₂.other _ (by decide), v₁.other _ (by decide), hc.esp]
  refine wp_stm esp₂ (by rw [a1, v₂.wr, v₁.wr]; exact hc.inFrW (by omega_arith) (by omega_arith) hL) fun u₃ v₃ => ?_
  refine wp_subsbb (j := j) (c := cb P.R.E.C.n P.k32 t.mem (xA L) j) (fun e => by subst e; rfl)
    (fun hj => by rw [v₃.cf, c₂, c₁]; exact h.cf hj) fun u₄ v₄ c₄ => ?_
  rw [v₃.gpr, v₂.gpr] at v₄
  refine wp_stm (B := L.F) (by rw [v₄.other _ (by decide), v₃.gpr, esp₂])
    (by rw [a2, v₄.wr, v₃.wr, v₂.wr, v₁.wr]; exact hc.inFrW (by omega_arith) (by omega_arith) hL) fun u₅ v₅ => WP.block_nil ?_
  rw [a1] at v₃; rw [a2] at v₅
  have hm₅ : u₅.mem = (u.mem.writeW (L.B + BitVec.ofNat 64 (272 + 4 * (P.k32 - 1 - j))) (Xw P.k32 t.mem (xA L) j)).writeW
      (L.B + BitVec.ofNat 64 (76 + 4 * (P.k32 - 1 - j))) (Dw P.R.E.C.n P.k32 t.mem (xA L) j) := by
    rw [v₅.mem, v₄.gpr, v₄.mem, v₃.mem, v₂.gpr, v₂.mem, v₁.mem]
  have hf : Frame (HW L) u.mem u₅.mem := by
    rw [hm₅]
    exact ((Frame.refl _ _).writeW (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _
      (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))).writeW List.mem_cons_self _
      (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))
  refine ⟨hc.keep (hsy := by rw [v₅.syms, v₄.syms, v₃.syms, v₂.syms, v₁.syms]) hL
      (by rw [v₅.rd, v₄.rd, v₃.rd, v₂.rd, v₁.rd]) (by rw [v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr])
      (by rw [v₅.gpr, v₄.other _ (by decide), v₃.gpr, esp₂, hc.esp]) hf
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact safe_low L (by omega_arith)
        · exact safe_high L (by omega_arith) (by omega_arith)),
    h.frame.trans hf, fun i hi => ?_, fun i hi => ?_, fun _ => by rw [v₅.cf, c₄, v₃.gpr, v₂.gpr]; rfl⟩
  · rw [hm₅, Mem.readW_writeW_sep (fr_sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
    rcases Nat.lt_or_ge i j with hij | hij
    · rw [Mem.readW_writeW_sep (fr_sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]; exact h.x i hij
    · rw [show i = j by omega_arith, Mem.readW_writeW_self32]
  · rw [hm₅]
    rcases Nat.lt_or_ge i j with hij | hij
    · rw [Mem.readW_writeW_sep (fr_sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
        Mem.readW_writeW_sep (fr_sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]; exact h.d i hij
    · rw [show i = j by omega_arith, Mem.readW_writeW_self32]

/-- The words before `i`. -/
theorem subs_ok (hA : P.R.wide = false) (hL : L.Ok) {t : State} :
    ∀ i ≤ P.k32, ∀ u, SubInv P.R.E.C.n P.k32 L g m₀ t 0 u →
    WP isa (.block ((List.range i).flatMap (cfgOf P).subWord)) u (SubInv P.R.E.C.n P.k32 L g m₀ t i)
  | 0, _, u, h => WP.block_nil h
  | i + 1, hi, u, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    exact WP.mono (subs_ok hA hL i (by omega_arith) u h) fun u' h' =>
      subWord_ok hA hL (by omega_arith) h'

/-- After the mask and `j` words of the selection, from `t`. -/
structure SelInv (N k : Nat) (L : Lay dn) (g : Reg → BitVec 32) (m₀ : Mem) (t : State) (j : Nat) (u : State) :
    Prop where
  ctx : Ctx L g m₀ u
  edx : u.gpr .edx = if cb N k t.mem (xA L) k then BitVec.allOnes 32 else 0
  frame : Frame (HW L) t.mem u.mem
  h : ∀ i < j, u.mem.readW (L.B + BitVec.ofNat 64 (272 + 4 * (k - 1 - i))) 32 =
    bswap (if cb N k t.mem (xA L) k then Xw k t.mem (xA L) i else Dw N k t.mem (xA L) i)
  x : ∀ i, j ≤ i → i < k → u.mem.readW (L.B + BitVec.ofNat 64 (272 + 4 * (k - 1 - i))) 32 = Xw k t.mem (xA L) i
  d : ∀ i < k, u.mem.readW (L.B + BitVec.ofNat 64 (76 + 4 * (k - 1 - i))) 32 = Dw N k t.mem (xA L) i

theorem selWord_ok (hA : P.R.wide = false) (hL : L.Ok) {t u : State} {j : Nat} (hj : j < P.k32)
    (h : SelInv P.R.E.C.n P.k32 L g m₀ t j u) :
    WP isa (.block ((cfgOf P).selWord j)) u (SelInv P.R.E.C.n P.k32 L g m₀ t (j + 1)) := by
  have nB := hL.nB
  have hc := h.ctx
  have hk := (P.sizesA hA).2
  have a1 : addr L.F (fH + 4 * (P.k32 - 1 - j)) = L.B + BitVec.ofNat 64 (272 + 4 * (P.k32 - 1 - j)) := by
    rw [hL.addrF (by simp only [fH]; omega_arith)]; simp only [fH]; congr 2; omega_arith
  have a2 : addr L.F (fK + 4 * (P.k32 - 1 - j)) = L.B + BitVec.ofNat 64 (76 + 4 * (P.k32 - 1 - j)) := by
    rw [hL.addrF (by simp only [fK]; omega_arith)]; congr 2; simp only [fK]; omega_arith
  simp only [Cfg.selWord, stk, w_cfgOf]
  refine wp_ldm hc.esp (by rw [a1]; exact hc.inFr (by omega_arith) (by omega_arith) hL) fun u₁ v₁ => ?_
  refine wp_ldm (B := L.F) (by rw [v₁.other _ (by decide), hc.esp])
    (by rw [a2, v₁.rd, v₁.wr]; exact hc.inFr (by omega_arith) (by omega_arith) hL) fun u₂ v₂ => ?_
  refine wp_xor fun u₃ v₃ => wp_and fun u₄ v₄ => wp_xor fun u₅ v₅ => wp_bswap fun u₆ v₆ => ?_
  have esp₆ : u₆.gpr .esp = L.F := by
    rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.other _ (by decide), hc.esp]
  refine wp_stm esp₆ (by rw [a1, v₆.wr, v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr]; exact hc.inFrW (by omega_arith) (by omega_arith) hL)
    fun u₇ v₇ => WP.block_nil ?_
  rw [a1] at v₁ v₇; rw [a2] at v₂
  have val : u₆.gpr .eax =
      bswap (if cb P.R.E.C.n P.k32 t.mem (xA L) P.k32 then Xw P.k32 t.mem (xA L) j else Dw P.R.E.C.n P.k32 t.mem (xA L) j) := by
    rw [v₆.gpr, v₅.gpr, v₄.gpr, v₄.other .ecx (by decide), v₃.gpr, v₃.other .ecx (by decide),
      v₃.other .edx (by decide), v₂.gpr, v₂.other .eax (by decide), v₂.other .edx (by decide), v₁.gpr,
      v₁.other .edx (by decide), v₁.mem, h.x j (by omega_arith) hj, h.d j hj, h.edx, sel_mask32]
  have hm₇ : u₇.mem = u.mem.writeW (L.B + BitVec.ofNat 64 (272 + 4 * (P.k32 - 1 - j)))
      (bswap (if cb P.R.E.C.n P.k32 t.mem (xA L) P.k32 then Xw P.k32 t.mem (xA L) j else Dw P.R.E.C.n P.k32 t.mem (xA L) j)) := by
    rw [v₇.mem, val, v₆.mem, v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem]
  have hf : Frame (HW L) u.mem u₇.mem := by
    rw [hm₇]
    exact (Frame.refl _ _).writeW (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _
      (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))
  refine ⟨hc.keep (hsy := by rw [v₇.syms, v₆.syms, v₅.syms, v₄.syms, v₃.syms, v₂.syms, v₁.syms]) hL
      (by rw [v₇.rd, v₆.rd, v₅.rd, v₄.rd, v₃.rd, v₂.rd, v₁.rd])
      (by rw [v₇.wr, v₆.wr, v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr]) (by rw [v₇.gpr, esp₆, hc.esp]) hf
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact safe_low L (by omega_arith)
        · exact safe_high L (by omega_arith) (by omega_arith)),
    by rw [v₇.gpr, v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.other _ (by decide), h.edx],
    h.frame.trans hf, fun i hi => ?_, fun i hi hi' => ?_, fun i hi => ?_⟩
  · rw [hm₇]
    rcases Nat.lt_or_ge i j with hij | hij
    · rw [Mem.readW_writeW_sep (fr_sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]; exact h.h i hij
    · rw [show i = j by omega_arith, Mem.readW_writeW_self32]
  · rw [hm₇, Mem.readW_writeW_sep (fr_sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
    exact h.x i (by omega_arith) hi'
  · rw [hm₇, Mem.readW_writeW_sep (fr_sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
    exact h.d i hi

/-- The words before `i`. -/
theorem sels_ok (hA : P.R.wide = false) (hL : L.Ok) {t : State} :
    ∀ i ≤ P.k32, ∀ u, SelInv P.R.E.C.n P.k32 L g m₀ t 0 u →
    WP isa (.block ((List.range i).flatMap (cfgOf P).selWord)) u (SelInv P.R.E.C.n P.k32 L g m₀ t i)
  | 0, _, u, h => WP.block_nil h
  | i + 1, hi, u, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    exact WP.mono (sels_ok hA hL i (by omega_arith) u h) fun u' h' => selWord_ok hA hL (by omega_arith) h'

/-- `h`: `X` (`Q` bytes, big-endian in `k` words) modulo `n`, big-endian in the frame. -/
theorem reduce_ok (hA : P.R.wide = false) (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block (cfgOf P).reduce) t fun t' => Ctx L g m₀ t' ∧
      Frame (HW L) t.mem t'.mem ∧
      Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 272) (4 * P.k32)) =
        Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem (xA L) (4 * P.k32)) % P.R.E.C.n := by
  rw [Cfg.reduce, WP.block_append_iff, WP.block_append_iff, w_cfgOf]
  refine WP.mono (subs_ok (P := P) hA hL P.k32 (Nat.le_refl _) t
    ⟨hc, Frame.refl _ _, fun i hi => absurd hi (Nat.not_lt_zero _), fun i hi => absurd hi (Nat.not_lt_zero _),
      fun h => absurd h (Nat.lt_irrefl _)⟩) fun u hu => ?_
  have hk6 : 0 < P.k32 := by have := P.sizes; omega_arith
  refine wp_sbb_self (hu.cf hk6) fun u₁ v₁ => WP.block_nil ?_
  have hc₁ : Ctx L g m₀ u₁ := hu.ctx.regs (hsy := v₁.syms) hL v₁.rd v₁.wr v₁.mem (v₁.other _ (by decide))
  refine WP.mono (sels_ok hA hL P.k32 (Nat.le_refl _) u₁
    ⟨hc₁, v₁.gpr, by rw [v₁.mem]; exact hu.frame, fun i hi => absurd hi (Nat.not_lt_zero _),
      fun i _ hi => by rw [v₁.mem]; exact hu.x i hi, fun i hi => by rw [v₁.mem]; exact hu.d i hi⟩)
    fun t' h' => ⟨h'.ctx, h'.frame, ?_⟩
  -- The value.
  have hX := ofBytes_words t.mem (Xw P.k32 t.mem (xA L)) (xA L) P.k32 fun j hj => rfl
  have hH := ofBytes_words t'.mem
    (fun i => if cb P.R.E.C.n P.k32 t.mem (xA L) P.k32 then Xw P.k32 t.mem (xA L) i else Dw P.R.E.C.n P.k32 t.mem (xA L) i)
    (L.B + BitVec.ofNat 64 272) P.k32 fun j hj => by
      rw [Offset.add_add, h'.h j hj]
      exact Proof.Pbkdf2.Whole.byteRev32_byteRev32 _
  have hch := chain P.R.E.C.n P.k32 t.mem (xA L) P.k32
  have e32 : 32 * P.k32 = 8 * P.R.E.C.len := by have := (P.sizesA hA).1; simp only [RfcHash.Q] at this; omega_arith
  rw [wsum_nWn, Nat.mod_eq_of_lt (by rw [e32]; exact (Nat.log2_lt P.R.n_ne).mp (by rw [← (P.R.sizesA hA).2.2.1]; unfold Spec.Ecdsa.nBits; omega))] at hch
  change Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt _ _ (4 * P.k32)) =
    Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt _ _ (4 * P.k32)) % _
  rw [hH, hX, wsum_sel]
  exact mod_mathK _ _ _ _ _ hch (wsum_lt _ _) (wsum_lt _ _) (by rw [e32]; exact (P.R.sizesA hA).2.2.2)

end VG.Proof.Ecdsa.Rfc6979.X86
