module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Cand
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Hmac
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Search
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Prep
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Words32
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Regs
import VerifiedGarbage.Proof.Pbkdf2.Whole.Common
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! ### `Ecdsa.Rfc6979.X86.Reduce`, which this module and modules that import it used -/

section

/-!
# Deterministic ECDSA on x86 (32-bit): `h = bits2octets(digest)`

`X`'s `4 k` bytes (in the frame, at `xa`), big-endian in `k` 32-bit words
(`Xw`), less `n` (its words `nWn`) if that does not borrow: the words go to
`h`'s place, and those of the difference (`Dw`, with the borrows `cb`) to
`K`'s (`subWord_ok`); a mask of the last borrow selects, word by word, `X`'s
word or the difference's, stored big-endian into `h` (`selWord_ok`). As the
number is below `2^(32 k) < 2n`, this is it modulo `n` (`mod_mathK`,
`reduce_ok`).
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
  obtain hc : ((BitVec.ofBool c).setWidth 32).toNat = c.toNat := by cases c <;> rfl
  rw [BitVec.toNat_sub, BitVec.toNat_sub, hc]
  by_cases h : a.toNat < b.toNat + c.toNat <;>
    simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega_arith

/-- The `k` words of the number at `dg`, least significant first. -/
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
    obtain ih := chain N k m dg i
    obtain e := sbb32 (Xw k m dg i) (nWn N i) (cb N k m dg i)
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

theorem w_cfgOf (P : RfcHash) : (cfgOf P).w = P.k := rfl

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

/-- Where `X` is in the frame. -/
abbrev xa {dn : Nat} (L : Lay dn) : Addr := L.B + BitVec.ofNat 64 (76 + fX)

theorem Lay.Ok.xav (hL : L.Ok) {o : Nat} (ho : o + 4 ≤ 72) :
    addr (L.F + BitVec.ofNat 32 fX) o = xa L + BitVec.ofNat 64 o := by
  rw [show addr (L.F + BitVec.ofNat 32 fX) o = addr L.F (fX + o) by
      simp only [addr, BitVec.add_assoc, BitVec.ofNat_add_ofNat], hL.addrF (by simp only [fX]; omega_arith),
    Offset.add_add, Nat.add_assoc]

/-- The regions `bits2octets` writes: `K`'s 128 bytes, and `h`'s `4 k` at `hb`. -/
abbrev HW {dn : Nat} (L : Lay dn) (k hb : Nat) : List Region :=
  [⟨L.B + BitVec.ofNat 64 76, 128⟩, ⟨L.B + BitVec.ofNat 64 hb, 4 * k⟩]

/-- After `j` words of the subtraction of `N`'s `k` words, from `t`, with `h` at `hb`. -/
structure SubInv (N k hb : Nat) (L : Lay dn) (g : Reg → BitVec 32) (m₀ : Mem) (t : State) (j : Nat) (u : State) :
    Prop where
  ctx : Ctx L g m₀ u
  esi : u.gpr .esi = L.F + BitVec.ofNat 32 fX
  frame : Frame (HW L k hb) t.mem u.mem
  x : ∀ i < j, u.mem.readW (L.B + BitVec.ofNat 64 (hb + 4 * (k - 1 - i))) 32 = Xw k t.mem (xa L) i
  d : ∀ i < j, u.mem.readW (L.B + BitVec.ofNat 64 (76 + 4 * (k - 1 - i))) 32 = Dw N k t.mem (xa L) i
  cf : 0 < j → u.cf = some (cb N k t.mem (xa L) j)

theorem fr_sep (B : Addr) {x y : Nat} (h : x + 4 ≤ y ∨ y + 4 ≤ x) (hx : x + 4 ≤ 616) (hy : y + 4 ≤ 616) :
    Mem.Sep (B + BitVec.ofNat 64 x) (32 / 8) (B + BitVec.ofNat 64 y) (32 / 8) :=
  Offset.sep B h (by omega_arith) (by omega_arith)

/-- `h`'s place, from `B`. -/
abbrev hB : Nat := 76 + fH

theorem subWord_ok (hA : P.R.big = false) (hL : L.Ok) {t u : State}
    {j : Nat} (hj : j < P.k)
    (h : SubInv P.R.E.C.n P.k hB L g m₀ t j u) :
    WP isa (.block ((cfgOf P).subWord j)) u (SubInv P.R.E.C.n P.k hB L g m₀ t (j + 1)) := by
  have nB := hL.nB
  have hc := h.ctx
  have hBv : hB = 236 := rfl
  have hfH : fH = 160 := rfl
  have hfX : fX = 232 := rfl
  have hfK : fK = 0 := rfl
  obtain ⟨-, hk, -⟩ := P.sizesA hA
  obtain hdg : u.mem.readW (xa L + BitVec.ofNat 64 (4 * (P.k - 1 - j))) 32 =
      t.mem.readW (xa L + BitVec.ofNat 64 (4 * (P.k - 1 - j))) 32 :=
    h.frame.readW (r := ⟨xa L, 72⟩) (Offset.contains_base _ (by omega_arith) (by omega_arith))
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by omega_arith)
          (by omega_arith) (by omega_arith)) (by decide)
  obtain a1 : addr L.F (fH + 4 * (P.k - 1 - j)) = L.B + BitVec.ofNat 64 (hB + 4 * (P.k - 1 - j)) := by
    rw [hL.addrF (by omega_arith)]; congr 2; omega_arith
  obtain a2 : addr L.F (fK + 4 * (P.k - 1 - j)) = L.B + BitVec.ofNat 64 (76 + 4 * (P.k - 1 - j)) := by
    rw [hL.addrF (by simp only [fK]; omega_arith)]; congr 2; simp only [fK]; omega_arith
  simp only [Cfg.subWord, stk, nWord_cfgOf, w_cfgOf]
  refine wp_movS (v := u.mem.readW (xa L + BitVec.ofNat 64 (4 * (P.k - 1 - j))) 32)
    (by rw [show at_ .esi (4 * (P.k - 1 - j)) = ⟨.esi, 4 * (P.k - 1 - j)⟩ from rfl, readSrc_mem h.esi
        (by rw [hL.xav (by omega_arith), Offset.add_add]; exact hc.inFr (by omega_arith) (by omega_arith) hL),
        hL.xav (by omega_arith)])
    fun u₁ v₁ c₁ => wp_bswapC fun u₂ v₂ c₂ => ?_
  rw [v₁.gpr, hdg] at v₂
  obtain esp₂ : u₂.gpr .esp = L.F := by rw [v₂.other _ (by decide), v₁.other _ (by decide), hc.esp]
  refine wp_stm esp₂ (by rw [a1, v₂.wr, v₁.wr]; exact hc.inFrW (by omega_arith) (by omega_arith) hL) fun u₃ v₃ => ?_
  refine wp_subsbb (j := j) (c := cb P.R.E.C.n P.k t.mem (xa L) j) (fun e => by subst e; rfl)
    (fun hj => by rw [v₃.cf, c₂, c₁]; exact h.cf hj) fun u₄ v₄ c₄ => ?_
  rw [v₃.gpr, v₂.gpr] at v₄
  refine wp_stm (B := L.F) (by rw [v₄.other _ (by decide), v₃.gpr, esp₂])
    (by rw [a2, v₄.wr, v₃.wr, v₂.wr, v₁.wr]; exact hc.inFrW (by omega_arith) (by omega_arith) hL) fun u₅ v₅ => WP.block_nil ?_
  rw [a1] at v₃; rw [a2] at v₅
  obtain hm₅ : u₅.mem = (u.mem.writeW (L.B + BitVec.ofNat 64 (hB + 4 * (P.k - 1 - j))) (Xw P.k t.mem (xa L) j)).writeW
      (L.B + BitVec.ofNat 64 (76 + 4 * (P.k - 1 - j))) (Dw P.R.E.C.n P.k t.mem (xa L) j) := by
    rw [v₅.mem, v₄.gpr, v₄.mem, v₃.mem, v₂.gpr, v₂.mem, v₁.mem]
  obtain hf : Frame (HW L P.k hB) u.mem u₅.mem := by
    rw [hm₅]
    exact ((Frame.refl _ _).writeW (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _
      (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))).writeW List.mem_cons_self _
      (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))
  refine ⟨hc.keep (hsy := by rw [v₅.syms, v₄.syms, v₃.syms, v₂.syms, v₁.syms]) hL (by rw [v₅.rd, v₄.rd, v₃.rd, v₂.rd, v₁.rd]) (by rw [v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr])
      (by rw [v₅.gpr, v₄.other _ (by decide), v₃.gpr, esp₂, hc.esp]) hf
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact safe_low L (by omega_arith)
        · exact safe_high L (by omega_arith) (by omega_arith)),
    by rw [v₅.gpr, v₄.other _ (by decide), v₃.gpr, v₂.other _ (by decide), v₁.other _ (by decide), h.esi],
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
theorem subs_ok (hA : P.R.big = false) (hL : L.Ok) {t : State} :
    ∀ i ≤ P.k, ∀ u, SubInv P.R.E.C.n P.k hB L g m₀ t 0 u →
    WP isa (.block ((List.range i).flatMap (cfgOf P).subWord)) u (SubInv P.R.E.C.n P.k hB L g m₀ t i)
  | 0, _, u, h => WP.block_nil h
  | i + 1, hi, u, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    exact WP.mono (subs_ok hA hL i (by omega_arith) u h) fun u' h' =>
      subWord_ok hA hL (by omega_arith) h'

/-- After the mask and `j` words of the selection, from `t`, with `h` at `hb`. -/
structure SelInv (N k hb : Nat) (L : Lay dn) (g : Reg → BitVec 32) (m₀ : Mem) (t : State) (j : Nat) (u : State) :
    Prop where
  ctx : Ctx L g m₀ u
  edx : u.gpr .edx = if cb N k t.mem (xa L) k then BitVec.allOnes 32 else 0
  frame : Frame (HW L k hb) t.mem u.mem
  h : ∀ i < j, u.mem.readW (L.B + BitVec.ofNat 64 (hb + 4 * (k - 1 - i))) 32 =
    bswap (if cb N k t.mem (xa L) k then Xw k t.mem (xa L) i else Dw N k t.mem (xa L) i)
  x : ∀ i, j ≤ i → i < k → u.mem.readW (L.B + BitVec.ofNat 64 (hb + 4 * (k - 1 - i))) 32 = Xw k t.mem (xa L) i
  d : ∀ i < k, u.mem.readW (L.B + BitVec.ofNat 64 (76 + 4 * (k - 1 - i))) 32 = Dw N k t.mem (xa L) i

theorem selWord_ok (hA : P.R.big = false) (hL : L.Ok) {t u : State} {j : Nat} (hj : j < P.k)
    (h : SelInv P.R.E.C.n P.k hB L g m₀ t j u) :
    WP isa (.block ((cfgOf P).selWord j)) u (SelInv P.R.E.C.n P.k hB L g m₀ t (j + 1)) := by
  have nB := hL.nB
  have hc := h.ctx
  have hBv : hB = 236 := rfl
  have hfH : fH = 160 := rfl
  have hfX : fX = 232 := rfl
  have hfK : fK = 0 := rfl
  obtain ⟨-, hk, -⟩ := P.sizesA hA
  obtain a1 : addr L.F (fH + 4 * (P.k - 1 - j)) = L.B + BitVec.ofNat 64 (hB + 4 * (P.k - 1 - j)) := by
    rw [hL.addrF (by omega_arith)]; congr 2; omega_arith
  obtain a2 : addr L.F (fK + 4 * (P.k - 1 - j)) = L.B + BitVec.ofNat 64 (76 + 4 * (P.k - 1 - j)) := by
    rw [hL.addrF (by simp only [fK]; omega_arith)]; congr 2; simp only [fK]; omega_arith
  simp only [Cfg.selWord, stk, w_cfgOf]
  refine wp_ldm hc.esp (by rw [a1]; exact hc.inFr (by omega_arith) (by omega_arith) hL) fun u₁ v₁ => ?_
  refine wp_ldm (B := L.F) (by rw [v₁.other _ (by decide), hc.esp])
    (by rw [a2, v₁.rd, v₁.wr]; exact hc.inFr (by omega_arith) (by omega_arith) hL) fun u₂ v₂ => ?_
  refine wp_xor fun u₃ v₃ => wp_and fun u₄ v₄ => wp_xor fun u₅ v₅ => wp_bswap fun u₆ v₆ => ?_
  obtain esp₆ : u₆.gpr .esp = L.F := by
    rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.other _ (by decide), hc.esp]
  refine wp_stm esp₆ (by rw [a1, v₆.wr, v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr]; exact hc.inFrW (by omega_arith) (by omega_arith) hL)
    fun u₇ v₇ => WP.block_nil ?_
  rw [a1] at v₁ v₇; rw [a2] at v₂
  obtain val : u₆.gpr .eax =
      bswap (if cb P.R.E.C.n P.k t.mem (xa L) P.k then Xw P.k t.mem (xa L) j else Dw P.R.E.C.n P.k t.mem (xa L) j) := by
    rw [v₆.gpr, v₅.gpr, v₄.gpr, v₄.other .ecx (by decide), v₃.gpr, v₃.other .ecx (by decide),
      v₃.other .edx (by decide), v₂.gpr, v₂.other .eax (by decide), v₂.other .edx (by decide), v₁.gpr,
      v₁.other .edx (by decide), v₁.mem, h.x j (by omega_arith) hj, h.d j hj, h.edx, sel_mask32]
  obtain hm₇ : u₇.mem = u.mem.writeW (L.B + BitVec.ofNat 64 (hB + 4 * (P.k - 1 - j)))
      (bswap (if cb P.R.E.C.n P.k t.mem (xa L) P.k then Xw P.k t.mem (xa L) j else Dw P.R.E.C.n P.k t.mem (xa L) j)) := by
    rw [v₇.mem, val, v₆.mem, v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem]
  obtain hf : Frame (HW L P.k hB) u.mem u₇.mem := by
    rw [hm₇]
    exact (Frame.refl _ _).writeW (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _
      (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))
  refine ⟨hc.keep (hsy := by rw [v₇.syms, v₆.syms, v₅.syms, v₄.syms, v₃.syms, v₂.syms, v₁.syms]) hL (by rw [v₇.rd, v₆.rd, v₅.rd, v₄.rd, v₃.rd, v₂.rd, v₁.rd])
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
theorem sels_ok (hA : P.R.big = false) (hL : L.Ok) {t : State} :
    ∀ i ≤ P.k, ∀ u, SelInv P.R.E.C.n P.k hB L g m₀ t 0 u →
    WP isa (.block ((List.range i).flatMap (cfgOf P).selWord)) u (SelInv P.R.E.C.n P.k hB L g m₀ t i)
  | 0, _, u, h => WP.block_nil h
  | i + 1, hi, u, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    exact WP.mono (sels_ok hA hL i (by omega_arith) u h) fun u' h' => selWord_ok hA hL (by omega_arith) h'

/-- `h`: `X`'s `4 k` bytes modulo `n`, big-endian in the frame at `hB`. -/
theorem reduce_ok (hA : P.R.big = false) (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block (cfgOf P).reduce) t fun t' => Ctx L g m₀ t' ∧
      Frame (HW L P.k hB) t.mem t'.mem ∧
      Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 hB) (4 * P.k)) =
        Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem (xa L) (4 * P.k)) % P.R.E.C.n := by
  obtain hk6 : 6 ≤ P.k := by have := P.R.len_words; have := P.R.n3; simp only [RfcHash.k]; split <;> omega_arith
  rw [Cfg.reduce, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, w_cfgOf]
  refine WP.mono (fr_ok hL hc (d := .esi) (by decide) fX) fun u₀ h₀ => ?_
  rw [show t.mem = u₀.mem from h₀.mem.symm]
  refine WP.mono (subs_ok (P := P) hA hL P.k (Nat.le_refl _) u₀
    ⟨h₀.ctx, h₀.val, Frame.refl _ _, fun i hi => absurd hi (Nat.not_lt_zero _),
      fun i hi => absurd hi (Nat.not_lt_zero _), fun h => absurd h (Nat.lt_irrefl _)⟩) fun u hu => ?_
  refine wp_sbb_self (hu.cf (by omega_arith)) fun u₁ v₁ => WP.block_nil ?_
  obtain hc₁ : Ctx L g m₀ u₁ := hu.ctx.regs (hsy := v₁.syms) hL v₁.rd v₁.wr v₁.mem (v₁.other _ (by decide))
  refine WP.mono (sels_ok hA hL P.k (Nat.le_refl _) u₁
    ⟨hc₁, v₁.gpr, by rw [v₁.mem]; exact hu.frame, fun i hi => absurd hi (Nat.not_lt_zero _),
      fun i _ hi => by rw [v₁.mem]; exact hu.x i hi, fun i hi => by rw [v₁.mem]; exact hu.d i hi⟩)
    fun t' h' => ⟨h'.ctx, h'.frame, ?_⟩
  -- The value.
  obtain hX := ofBytes_words u₀.mem (Xw P.k u₀.mem (xa L)) (xa L) P.k fun j hj => rfl
  obtain hH := ofBytes_words t'.mem
    (fun i => if cb P.R.E.C.n P.k u₀.mem (xa L) P.k then Xw P.k u₀.mem (xa L) i else Dw P.R.E.C.n P.k u₀.mem (xa L) i)
    (L.B + BitVec.ofNat 64 hB) P.k fun j hj => by
      rw [Offset.add_add, h'.h j hj]
      exact Proof.Pbkdf2.Whole.byteRev32_byteRev32 _
  obtain hch := chain P.R.E.C.n P.k u₀.mem (xa L) P.k
  obtain e32 : 32 * P.k = 8 * P.R.E.C.len := by have := (P.sizesA hA).1; simp only [RfcHash.Q] at this; omega_arith
  rw [wsum_nWn, Nat.mod_eq_of_lt (by rw [e32]; exact (Nat.log2_lt P.R.n_ne).mp (by rw [← (P.R.sizesA hA).2.2.1]; unfold Spec.Ecdsa.nBits; omega_using []))] at hch
  change Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt _ _ (4 * P.k)) =
    Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt _ _ (4 * P.k)) % _
  rw [hH, hX, wsum_sel]
  exact mod_mathK _ _ _ _ _ hch (wsum_lt _ _) (wsum_lt _ _) (by rw [e32]; exact (P.R.sizesA hA).2.2.2)

end VG.Proof.Ecdsa.Rfc6979.X86

end

end

/-! ### `Ecdsa.Rfc6979.X86.Loop`, which only this module used -/

section

/-! ### `Ecdsa.Rfc6979.X86.Core`, which only this module used -/

section

/-!
# Deterministic ECDSA on x86 (32-bit): signing with a candidate

The call of `vg_ecdsa_<curve>_sign_k` with `k = T` from the frame, in a frame
of its five arguments, whose pop loads `ecx` so that the result stays in
`eax` (`core_ok`): it returns 1 and writes the signature, or returns 0 and
writes zeros, as `Spec.Ecdsa.signWith` gives for `d`, the leftmost `8 w`
bytes of the digest (`X`, or if `big` the shifted digest at `fXc`) and of
`T`, and changes only `out`, `scratch` and the 76 bytes below the frame.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.Impl.Ecdsa.Rfc6979.X86

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

/-- `WP.callWith`, for a frame popped into any register `r`: the registers
but `esp` and `r` are those the callee returns with. -/
theorem WP.callWithR {rs : List Reg} {r : Reg} {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsp : NoSp c) (hne : rs ≠ []) (hrs : Reg.esp ∉ rs) (hr : r ≠ .esp) {s : State}
    (hd : 4 * rs.length + stackUse c + 4 ≤ (s.gpr .esp).toNat) {rd wr : List Region}
    (hk : CallPre k rs rd wr s) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.gpr .esp = s.gpr .esp →
      Frame (wr ++ [below (s.gpr .esp) (4 * rs.length + stackUse c + 4)]) s.mem s'.mem →
      (∃ s₂ : State, Frame [below (s.gpr .esp) (4 * rs.length)] s₂.mem s'.mem ∧
        (∀ q, q ≠ .esp → q ≠ r → s₂.gpr q = s'.gpr q) ∧
        k.post ((pushed rs s).callEntry.withRegions rd wr) s₂) → Q s') :
    WP isa (.frame (.push rs) (.call n c) (.pop r rs.length)) s Q := by
  obtain hn : 4 * rs.length ≤ (s.gpr .esp).toNat := by omega_arith
  obtain e : ((pushed rs s).gpr .esp).toNat = (s.gpr .esp).toNat - 4 * rs.length := by
    rw [pushed_esp, sub_toNat hn]
  refine WP.frame hne hrs hr hn (fun i hi => hsp i hi) ?_
  refine WP.call hv hsp (by rw [e]; omega_arith) hk.pre (by rw [pushed_rd, pushed_wr]; exact hk.cov)
    (by rw [pushed_wr]; exact hk.covw) fun s₂ rd₂ wr₂ cs₂ f₂ _ ⟨s₃, m₃, g₃, post₃⟩ m u fl => ?_
  refine hQ _ (by rw [popped_rd, rd₂, pushed_rd]) (by rw [popped_wr, wr₂, pushed_wr]; rfl) ?_ ?_
    ⟨s₃, by rw [m₃]; exact fl, fun q h₁ h₂ => by rw [popped_gpr _ _ _ h₁ h₂]; exact g₃ q h₁, post₃⟩
  · rw [popped_esp, cs₂ .esp (by simp [calleeSaved]), pushed_esp]; exact BitVec.sub_add_cancel _ _
  · refine (((pushed_frame hrs hn).sub fun r hr => ?_).trans (f₂.sub fun r hr => ?_)).trans
      (fl.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), below_sub (by omega_arith) hd⟩
    rotate_left
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), below_sub (by omega_arith) hd⟩
    · rcases List.mem_append.mp hr with hr | hr
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · simp only [List.mem_singleton] at hr; subst hr
        refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
        rw [pushed_esp]
        exact below_inner (by omega_arith) hd

/-- The five words of `core`'s frame, last to first. -/
abbrev core5 : List Reg := [.ebp, .ecx, .edx, .esi, .edi]

/-- The signature `core` computes, or none. -/
abbrev coreSig (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) : Option (Nat × Nat) :=
  coreSigOf P.R.E m L.d (dgAddr P L) (kAddr L)

/-- `core` reads the private key, the digest and `k`, `Q` bytes each, and
its arguments, and writes `out` and `scratch`. -/
abbrev coreRd (P : RfcHash) {dn : Nat} (L : Lay dn) : List Region :=
  [⟨L.d, P.Q⟩, ⟨dgAddr P L, P.Q⟩, ⟨kAddr L, P.Q⟩, ⟨L.B + BitVec.ofNat 64 56, 20⟩] ++ L.TBLs
abbrev coreWr (P : RfcHash) {dn : Nat} (L : Lay dn) : List Region := [⟨L.out, 2 * P.Q⟩, L.SCR]

/-- What `core`'s arguments need of the layout: the scalars' bytes and the
comb's tables. -/
def CoreOk (P : RfcHash) {dn : Nat} (L : Lay dn) : Prop :=
  L.q = P.Q ∧ L.cs = P.R.E.combConsts

/-- `core`'s digest and `k`: in the frame, apart from `out`, `scratch` and
the stack below the frame, and not wrapping. -/
theorem coreArg_ok (hL : L.Ok) {v : BitVec 32} {x : Addr}
    (hx : (v = dgArg P L ∧ x = dgAddr P L) ∨ (v = kArg L ∧ x = kAddr L)) :
    Within ⟨x, P.Q⟩ L.FR ∧ Region.Disjoint ⟨x, P.Q⟩ L.OUT ∧
      Region.Disjoint ⟨x, P.Q⟩ L.SCR ∧ Region.Disjoint ⟨x, P.Q⟩ ⟨L.B, 76⟩ ∧ v.toNat + P.Q ≤ 2 ^ 32 := by
  have nB := hL.nB
  have e28 := hL.e28
  have e588 := hL.e588
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hQ66, -, -⟩ := P.sizes
  obtain key : ∀ o, o ≤ 376 → (Within ⟨L.B + BitVec.ofNat 64 (76 + o), P.Q⟩ L.FR ∧
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 (76 + o), P.Q⟩ L.OUT ∧
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 (76 + o), P.Q⟩ L.SCR ∧
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 (76 + o), P.Q⟩ ⟨L.B, 76⟩) ∧ (L.F + BitVec.ofNat 32 o).toNat + P.Q ≤ 2 ^ 32 :=
    fun o ho => ⟨⟨within_fr _ (by omega_arith) (by omega_arith), hL.stk_OUT (by omega_arith), hL.stk_SCR (by omega_arith),
      (Offset.base_disjoint _ (by omega_arith) (by omega_arith)).symm⟩, by rw [hL.frN (by omega_arith)]; omega_arith⟩
  obtain hd := fDg_le P
  rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨⟨a, b, c, d⟩, e⟩ := key (cfgOf P).fDg (by omega_arith); exact ⟨a, b, c, d, e⟩
  · obtain ⟨⟨a, b, c, d⟩, e⟩ := key fT (by decide); exact ⟨a, b, c, d, e⟩

/-- What a framed call of `core` needs of the registers. -/
structure CoreRegs (P : RfcHash) {dn : Nat} (L : Lay dn) (t : State) : Prop where
  edi : t.gpr .edi = L.a0
  esi : t.gpr .esi = L.a1
  edx : t.gpr .edx = dgArg P L
  ecx : t.gpr .ecx = kArg L
  ebp : t.gpr .ebp = L.sc

theorem core_fit (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) : 4 * core5.length + 4 ≤ (t.gpr .esp).toNat := by
  rw [hc.esp, hL.FN]; have := hL.e588; simp only [List.length_cons, List.length_nil]; omega_arith

theorem core_esp {t : State} (hc : Ctx L g m₀ t) :
    ((pushed core5 t).callEntry.gpr .esp) = L.F - BitVec.ofNat 32 24 := by
  rw [callEntry_esp', hc.esp]; rfl

/-- The 20 bytes below the frame, as an address. -/
theorem F_sub (hL : L.Ok) {k : Nat} (hk : k ≤ 76) :
    (L.F - BitVec.ofNat 32 k).setWidth 64 = L.B + BitVec.ofNat 64 (76 - k) := by
  have := hL.e588
  rw [Lay.F, BitVec.sub_sub, BitVec.ofNat_add_ofNat, Taint.sub_setWidth (by omega_arith), hL.B_eq,
    Offset.sub_ofNat_eq _ (show 512 + k ≤ 588 by omega_arith), show 588 - (512 + k) = 76 - k by omega_arith]

theorem core_args (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    argAddr (pushed core5 t).callEntry 0 = L.B + BitVec.ofNat 64 56 := by
  rw [callEntry_argAddr0, hc.esp, show 4 * core5.length = 20 from rfl, F_sub hL (by omega_arith)]

theorem core_ret (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    ((pushed core5 t).callEntry.gpr .esp).setWidth 64 = L.B + BitVec.ofNat 64 52 := by
  rw [core_esp hc, F_sub hL (by omega_arith)]

/-- The arguments `core` is called with. -/
theorem core_argv (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (hr : CoreRegs P L t) {rd wr : List Region} :
    arg ((pushed core5 t).callEntry.withRegions rd wr) 0 = L.a0 ∧
    arg ((pushed core5 t).callEntry.withRegions rd wr) 1 = L.a1 ∧
    arg ((pushed core5 t).callEntry.withRegions rd wr) 2 = dgArg P L ∧
    arg ((pushed core5 t).callEntry.withRegions rd wr) 3 = kArg L ∧
    arg ((pushed core5 t).callEntry.withRegions rd wr) 4 = L.sc := by
  obtain fit := core_fit hL hc
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [arg_withRegions, callEntry_arg fit (by decide) (by simp)]; simpa using hr.edi
  · rw [arg_withRegions, callEntry_arg fit (by decide) (by simp)]; simpa using hr.esi
  · rw [arg_withRegions, callEntry_arg fit (by decide) (by simp)]; simpa using hr.edx
  · rw [arg_withRegions, callEntry_arg fit (by decide) (by simp)]; simpa using hr.ecx
  · rw [arg_withRegions, callEntry_arg fit (by decide) (by simp)]; simpa using hr.ebp

/-- Symbols and static regions at the nested signing call. -/
theorem core_syms {t : State} (hc : Ctx L g m₀ t) {rd wr : List Region}
    {c : String × List (BitVec 64)} (h : c ∈ L.cs) :
    ((pushed core5 t).callEntry.withRegions rd wr).syms c.1 = L.sy c.1 := hc.sy c h

theorem core_tbls (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) {rd wr : List Region} :
    Abi.constRegions (fun n => (((pushed core5 t).callEntry.withRegions rd wr).syms n).setWidth 64)
      P.R.E.combConsts = L.TBLs := by
  rw [← hk.2]
  apply List.map_congr_left
  intro c hc'
  simp only [core_syms hc hc']

/-- The comb's four-byte PIC frame is within the reserved call area. -/
theorem core_below (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {rd wr : List Region} :
    below (((pushed core5 t).callEntry.withRegions rd wr).gpr .esp) 4 =
      ⟨L.B + BitVec.ofNat 64 48, 4⟩ := by
  show (⟨(((pushed core5 t).callEntry.gpr .esp) - BitVec.ofNat 32 4).setWidth 64, 4⟩ : Region) = _
  rw [core_esp hc, BitVec.sub_sub, BitVec.ofNat_add_ofNat, F_sub hL (by decide)]

/-- The `k ≤ 52` bytes below the return address, which the call's own calls
use, are within the reserved call area. -/
theorem core_belowK (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {rd wr : List Region} {k : Nat}
    (hk : k ≤ 52) :
    below (((pushed core5 t).callEntry.withRegions rd wr).gpr .esp) k =
      ⟨L.B + BitVec.ofNat 64 (52 - k), k⟩ := by
  show (⟨(((pushed core5 t).callEntry.gpr .esp) - BitVec.ofNat 32 k).setWidth 64, k⟩ : Region) = _
  rw [core_esp hc, BitVec.sub_sub, BitVec.ofNat_add_ofNat, F_sub hL (by omega_using [hk]),
    show 76 - (24 + k) = 52 - k by omega_using []]

theorem core_held (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) {rd wr : List Region} :
    Abi.constsHeld ((pushed core5 t).callEntry.withRegions rd wr).mem
      (fun n => (((pushed core5 t).callEntry.withRegions rd wr).syms n).setWidth 64) P.R.E.combConsts := by
  rw [← hk.2]
  intro c hmem i hi
  simp only [core_syms hc hmem, State.withRegions_mem]
  obtain hT : (⟨(L.sy c.1).setWidth 64, 8 * c.2.length⟩ : Region) ∈ L.TBLs :=
    List.mem_map.mpr ⟨c, hmem, rfl⟩
  obtain ht := hL.tbl _ hT
  obtain fitT : (L.sy c.1).toNat + 8 * c.2.length ≤ 2 ^ 32 := by
    simpa only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (L.sy c.1).isLt (by decide : 2 ^ 32 ≤ 2 ^ 64))] using ht.1
  obtain inT : (⟨(L.sy c.1).setWidth 64, 8 * c.2.length⟩ : Region).Contains
      ((L.sy c.1).setWidth 64 + BitVec.ofNat 64 (8 * i)) (64 / 8) :=
    Offset.contains_base _ (by omega_arith) (by omega_arith)
  obtain fr := callEntry_frame (core_fit hL hc) (by decide : Reg.esp ∉ core5)
  rw [fr.readW inT (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    apply ht.2.2.2.sub_right
    apply sub_trans (below_sub (b := 76) (by decide) (by rw [hc.esp, hL.FN]; have := hL.e588; omega_arith))
    rw [hc.esp, hL.below_F]
    exact Lay.sub_STK' (by omega_arith)) (by decide)]
  rw [hc.frame.readW inT (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ht.2.1
    · exact ht.2.2.1
    · exact ht.2.2.2) (by decide)]
  exact hc.held c hmem i hi

theorem core_pre (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) (hr : CoreRegs P L t) :
    (coreK P.R.E).pre ((pushed core5 t).callEntry.withRegions (coreRd P L) (coreWr P L)) := by
  obtain hst := VG.Proof.Ecdsa.X86.Cfg.stk_le P.R.E
  obtain fit := core_fit hL hc
  have nB := hL.nB
  have hq : L.q = P.R.E.C.len := hk.1
  obtain eD : (⟨L.d, P.R.E.C.len⟩ : Region) = L.D := by rw [Lay.D, hq]
  obtain eO : (⟨L.out, 2 * P.R.E.C.len⟩ : Region) = L.OUT := by rw [Lay.OUT, hq]
  obtain ⟨-, gO, gS, -, gN⟩ := coreArg_ok (P := P) hL (.inl ⟨rfl, rfl⟩)
  obtain ⟨-, kO, kS, -, kN⟩ := coreArg_ok (P := P) hL (.inr ⟨rfl, rfl⟩)
  obtain ⟨a0, a1, a2, a3, a4⟩ := core_argv hL hc hr (rd := coreRd P L) (wr := coreWr P L)
  simp only [coreK, a0, a1, a2, a3, a4, argAddr_withRegions, core_args hL hc,
    State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr, core_tbls hk hc, core_ret hL hc, dgArg_w hL, kArg_w hL]
  simp only [eD, eO]
  refine ⟨trivial, trivial, hL.oc, hL.od, gO.symm, kO.symm, hL.dc, gS, kS, hL.stk_OUT (by omega_arith),
    hL.stk_SCR (by omega_arith), hL.stk_OUT (by omega_arith), hL.stk_SCR (by omega_arith), by have := hL.no; rw [hq] at this; omega_arith,
    by have := hL.nd; rw [hq] at this; omega_arith, gN, kN, hL.nc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [core_esp hc, Lay.F, BitVec.sub_sub, BitVec.ofNat_add_ofNat, sub_toNat (by have := hL.e588; omega_arith)]
    have := hL.e28; omega_arith
  · rw [core_esp hc, Lay.F, BitVec.sub_sub, BitVec.ofNat_add_ofNat, sub_toNat (by have := hL.e588; omega_arith)]
    have := hL.e588; omega_arith
  · rw [Offset.add_ofNat_sub _ (by omega_arith)]; exact hL.stk_OUT (by omega_arith)
  · rw [Offset.add_ofNat_sub _ (by omega_arith)]; exact hL.stk_SCR (by omega_arith)
  · change L.D.Disjoint (below (((pushed core5 t).callEntry.withRegions (coreRd P L) (coreWr P L)).gpr .esp) 4)
    rw [core_below hL hc]
    exact hL.kd.symm.sub_right (Lay.sub_STK (by omega_arith))
  · change (⟨dgAddr P L, P.Q⟩ : Region).Disjoint (below (((pushed core5 t).callEntry.withRegions (coreRd P L) (coreWr P L)).gpr .esp) 4)
    rw [core_below hL hc]
    exact (coreArg_ok (P := P) hL (.inl ⟨rfl, rfl⟩)).2.2.2.1.sub_right (Offset.sub_base _ (by decide))
  · change (⟨kAddr L, P.Q⟩ : Region).Disjoint (below (((pushed core5 t).callEntry.withRegions (coreRd P L) (coreWr P L)).gpr .esp) 4)
    rw [core_below hL hc]
    exact (coreArg_ok (P := P) hL (.inr ⟨rfl, rfl⟩)).2.2.2.1.sub_right (Offset.sub_base _ (by decide))
  · refine ⟨core_held hL hk hc, ?_⟩
    rw [core_tbls hk hc]
    intro T hT
    obtain ht := hL.tbl T hT
    refine ⟨ht.1, ?_⟩
    intro r hr
    change r ∈ below (((pushed core5 t).callEntry.withRegions (coreRd P L) (coreWr P L)).gpr .esp) P.R.E.stk ::
      coreWr P L at hr
    rw [core_belowK hL hc (by omega_using [hst])] at hr
    simp only [coreWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ht.2.2.2.sub_right (Lay.sub_STK (by omega_arith))
    · simpa only [Lay.OUT, hk.1] using ht.2.1
    · exact ht.2.2.1

theorem core_callPre (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t)
    (hr : CoreRegs P L t) : CallPre (coreK P.R.E) core5 (coreRd P L) (coreWr P L) t := by
  have nB := hL.nB
  have hq : L.q = P.Q := hk.1
  obtain hb : below (t.gpr .esp) (4 * core5.length) = ⟨L.B + BitVec.ofNat 64 56, 20⟩ := by
    show (⟨(t.gpr .esp - BitVec.ofNat 32 20).setWidth 64, 20⟩ : Region) = _
    rw [hc.esp, F_sub hL (by omega_arith)]
  obtain hw : ∀ {x : Addr}, Within ⟨x, P.Q⟩ L.FR →
      ∃ R ∈ ([L.D, L.DG, L.TAB] ++ L.TBLs) ++ [⟨L.B + BitVec.ofNat 64 56, 20⟩, L.FR, L.OUT, L.SCR, L.ARGS],
        Within ⟨x, P.Q⟩ R :=
    fun hW => ⟨L.FR, by simp, hW⟩
  refine ⟨core_pre hL hk hc hr, covers_of fun q hq' => ?_, covers_of fun q hq' => ?_⟩
  · rw [hb, hc.rd, hc.wr]
    simp only [coreRd, coreWr, List.cons_append, List.nil_append, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hq'
    rcases hq' with rfl | rfl | rfl | rfl | ht | rfl | rfl
    · exact ⟨L.D, by simp, within_base _ (by omega_arith)⟩
    · exact hw (coreArg_ok (P := P) hL (.inl ⟨rfl, rfl⟩)).1
    · exact hw (coreArg_ok (P := P) hL (.inr ⟨rfl, rfl⟩)).1
    · exact ⟨⟨L.B + BitVec.ofNat 64 56, 20⟩, by simp, within_base _ (Nat.le_refl _)⟩
    · exact ⟨q, by simp [ht], within_base _ (Nat.le_refl _)⟩
    · exact ⟨L.OUT, by simp, within_base _ (by omega_arith)⟩
    · exact ⟨L.SCR, by simp, within_base _ (by omega_arith)⟩
  · rw [hb, hc.wr]
    simp only [coreWr, List.mem_cons, List.not_mem_nil, or_false] at hq'
    rcases hq' with rfl | rfl
    · exact ⟨L.OUT, by simp, within_base _ (by omega_arith)⟩
    · exact ⟨L.SCR, by simp, within_base _ (by omega_arith)⟩

/-- Bytes apart from the stack below the frame, on entry to the call. -/
theorem ce_bytesAt (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {p : Addr} {n : Nat}
    (hd : Region.Disjoint ⟨p, n⟩ ⟨L.B, 76⟩) (hn : n ≤ 2 ^ 64) :
    Spec.Sha256.bytesAt ((pushed core5 t).callEntry.withRegions (coreRd P L) (coreWr P L)).mem p n =
      Spec.Sha256.bytesAt t.mem p n := by
  rw [State.withRegions_mem]
  refine bytesAt_frame (callEntry_frame (core_fit hL hc) (by decide)) (fun r hr => ?_) hn
  simp only [List.mem_singleton] at hr; subst hr
  refine hd.sub_right (sub_trans (below_sub (b := 76) (by simp) (by rw [hc.esp, hL.FN]; have := hL.e588; omega_arith)) ?_)
  rw [hc.esp, hL.below_F]; exact sub_refl _

/-- `core(out, d, digest, k, scratch)`, in a frame of its arguments. -/
theorem core_ok (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) (hr : CoreRegs P L t) :
    WP isa (.frame (.push [.ebp, .ecx, .edx, .esi, .edi]) (.call (cfgOf P).coreN (cfgOf P).coreC) (.pop .ecx 5)) t
      fun t' => Ctx L g m₀ t' ∧ Frame [L.OUT, L.SCR, ⟨L.B, 76⟩] t.mem t'.mem ∧
      match coreSig P L t.mem with
      | some rs => t'.gpr .eax = 1 ∧ Spec.Sha256.bytesAt t'.mem L.out (2 * P.Q) = Spec.Ecdsa.encode P.R.E.C rs
      | none => t'.gpr .eax = 0 ∧ Spec.Sha256.bytesAt t'.mem L.out (2 * P.Q) = List.replicate (2 * P.Q) 0 := by
  have nB := hL.nB
  have hq : L.q = P.Q := hk.1
  obtain hsp : Region.Sub (below (t.gpr .esp) (4 * core5.length + stackUse P.R.coreC + 4)) ⟨L.B, 76⟩ := by
    have hs := P.R.coreStack
    have := VG.Proof.Ecdsa.X86.Cfg.stk_le P.R.E
    refine sub_trans (below_sub (b := 76) (by change 4 * 5 + _ + 4 ≤ 76; omega_arith) (by rw [hc.esp, hL.FN]; have := hL.e588; omega_arith)) ?_
    rw [hc.esp, hL.below_F]; exact sub_refl _
  obtain eW : coreWr P L = [L.OUT, L.SCR] := by simp only [coreWr, Lay.OUT, hq]
  obtain hd : 4 * core5.length + stackUse P.R.coreC + 4 ≤ (t.gpr .esp).toNat := by
    rw [hc.esp, hL.FN]; have := hL.e588; have := P.R.coreStack
    have := VG.Proof.Ecdsa.X86.Cfg.stk_le P.R.E; change 4 * 5 + _ + 4 ≤ _; omega_arith
  refine WP.of_syms ?_
  refine WP.callWithR (rs := core5) (k := coreK P.R.E) P.R.coreX P.R.coreNs (by decide) (by decide)
    (by decide) hd (core_callPre hL hk hc hr)
    fun t' hrd hwr hesp hf ⟨s₂, hm, hg₂, hpost⟩ hsy => ?_
  obtain hf' : Frame [L.OUT, L.SCR, ⟨L.B, 76⟩] t.mem t'.mem := hf.sub fun q hq' => by
    simp only [eW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq'
    rcases hq' with rfl | rfl | rfl
    · exact ⟨_, by simp, sub_refl _⟩
    · exact ⟨_, by simp, sub_refl _⟩
    · exact ⟨_, by simp, hsp⟩
  refine ⟨hc.keep (hsy := hsy) hL hrd hwr hesp hf' fun q hq' => ?_, hf', ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
    rcases hq' with rfl | rfl | rfl
    · exact .inl (sub_refl _)
    · exact .inr (.inl (sub_refl _))
    · exact .inr (.inr (.inl (Lay.sub_LOW' (by omega_arith))))
  · obtain ⟨a0, a1, a2, a3, a4⟩ := core_argv hL hc hr (rd := coreRd P L) (wr := coreWr P L)
    obtain ⟨-, -, -, gB, -⟩ := coreArg_ok (P := P) hL (.inl ⟨rfl, rfl⟩)
    obtain ⟨-, -, -, kB, -⟩ := coreArg_ok (P := P) hL (.inr ⟨rfl, rfl⟩)
    have hQe : P.Q = P.R.E.C.len := rfl
    obtain hQl : P.Q ≤ 72 := by have := P.R.len_words; have := P.R.n9; omega_arith
    obtain hs : coreSigOf P.R.E ((pushed core5 t).callEntry.withRegions (coreRd P L) (coreWr P L)).mem L.d
        (dgAddr P L) (kAddr L) = coreSig P L t.mem := by
      simp only [coreSigOf, coreSig, ecdsa_bytesAt]
      obtain h₁ : Region.Disjoint ⟨L.d, P.R.E.C.len⟩ ⟨L.B, 76⟩ :=
        (hL.kd.sub_left (Lay.sub_STK' (by omega_arith))).symm.sub_left (Region.sub_prefix (by omega_arith))
      rw [ce_bytesAt hL hc h₁ (by omega_arith), ce_bytesAt hL hc gB (by omega_arith), ce_bytesAt hL hc kB (by omega_arith)]
    obtain kO : Spec.Sha256.bytesAt t'.mem L.out (2 * P.Q) = Spec.Sha256.bytesAt s₂.mem L.out (2 * P.Q) := by
      refine bytesAt_frame hm (fun q hq' => ?_) (by omega_arith)
      simp only [List.mem_singleton] at hq'; subst hq'
      rw [← hq]
      exact (hL.ko.sub_left (sub_trans (sub_trans (below_sub (by omega_arith) hd) hsp)
        (Lay.sub_STK' (by omega_arith)))).symm
    have hp := hpost
    simp only [coreK, a0, a1, a2, a3, dgArg_w hL, kArg_w hL, hs, hg₂ .eax (by decide) (by decide),
      BitVec.setWidth_append_eq_right] at hp
    rw [kO]
    exact hp

end VG.Proof.Ecdsa.Rfc6979.X86

end

end


/-!
# Deterministic ECDSA on x86 (32-bit): the candidates

The values of a run, as RFC 6979 computes them from the private key and the
digest on entry (`kvI`, `candI`, `sigI`), with candidates of `nV` `V`s; the candidate's `k` for `core` (`cand_ok`); the loop's invariant
before candidate `i` (`LoopInv`): `K` and `V` are those before it, the count
is `tries - i`, every earlier candidate was unsuitable, and `core`'s digest is
the digest's (`DgOk`). One iteration either moves to candidate `i + 1`,
branching back, or leaves the loop with the signature of candidate `i`,
which is suitable or the last (`tryOne_ok`, `loop_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.Impl.Ecdsa.Rfc6979.X86
open VG.Proof.Ecdsa.Rfc6979 (kvAtB candAtB stepB)

variable {P : RfcHash} {L : Lay P.I.hashLen} {g : Reg → BitVec 32} {m₀ : Mem}

/-! ## The run's values -/

/-- The private key, the digest and its integer. -/
abbrev xOf (P : RfcHash) {dn : Nat} (L : Lay dn) (m₀ : Mem) : Nat :=
  Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.d P.Q)
abbrev hBOf (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte := Spec.Sha256.bytesAt m₀ L.dg P.F.H.D
abbrev eOf (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : Nat := Spec.Ecdsa.hashToInt P.R.E.C (hBOf P L m₀)

/-- `K` and `V` after steps b–g. -/
abbrev kv0 (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte × List Byte :=
  Spec.Ecdsa.Rfc6979.init P.R.E.C P.ok.hH.SH.H P.F.H.D (xOf P L m₀) (hBOf P L m₀)

/-- `K` and `V` before candidate `i`, candidate `i`'s `T`, and its signature. -/
abbrev kvI (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) : List Byte × List Byte :=
  kvAtB P.ok.hH.SH.H P.nV (kv0 P L m₀).1 (kv0 P L m₀).2 i
abbrev candI (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) : List Byte :=
  candAtB P.ok.hH.SH.H P.nV (kv0 P L m₀).1 (kv0 P L m₀).2 i
abbrev sigI (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) : Option (Nat × Nat) :=
  Spec.Ecdsa.signWith P.R.E.C (xOf P L m₀) (eOf P L m₀) (Spec.Ecdsa.Rfc6979.bits2int P.R.E.C (candI P L m₀ i))

/-- `core`'s digest is the digest's integer. -/
def DgOk (P : RfcHash) (L : Lay P.I.hashLen) (m₀ m : Mem) : Prop :=
  Spec.Ecdsa.hashToInt P.R.E.C (Spec.Sha256.bytesAt m (dgAddr P L) P.Q) = eOf P L m₀

/-- What the function's result is, for the signature `r` of the last candidate. -/
def ResultIs (P : RfcHash) {dn : Nat} (L : Lay dn) (r : Option (Nat × Nat)) (t : State) : Prop :=
  match r with
  | some rs => t.gpr .eax = 1 ∧
      Spec.Sha256.bytesAt t.mem L.out (2 * P.Q) = Spec.Ecdsa.encode P.R.E.C rs
  | none => t.gpr .eax = 0 ∧
      Spec.Sha256.bytesAt t.mem L.out (2 * P.Q) = List.replicate (2 * P.Q) 0

/-- Before candidate `i`. -/
structure LoopInv (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) (t : State) : Prop where
  lt : i < P.I.tries
  k : kOf P L t.mem = (kvI P L m₀ i).1
  v : vOf P L t.mem = (kvI P L m₀ i).2
  cnt : cnt L t.mem = BitVec.ofNat 32 (P.I.tries - i)
  fails : ∀ j < i, sigI P L m₀ j = none
  dg : DgOk P L m₀ t.mem
  saved : SavedK P L t.mem (kOf P L t.mem)

/-- After the loop, at candidate `i`: suitable or the last. -/
structure Exit (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) (t : State) : Prop where
  lt : i < P.I.tries
  fails : ∀ j < i, sigI P L m₀ j = none
  last : sigI P L m₀ i ≠ none ∨ i + 1 = P.I.tries
  res : ResultIs P L (sigI P L m₀ i) t

/-! ## Facts kept -/

theorem Ctx.dBytes (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {n : Nat} (hn : n ≤ L.q) :
    Spec.Sha256.bytesAt t.mem L.d n = Spec.Sha256.bytesAt m₀ L.d n := by
  simp only [Spec.Sha256.bytesAt]
  exact List.map_congr_left fun i hi => hc.d_byte hL (by have := List.mem_range.mp hi; omega_arith)

theorem Ctx.dgBytes (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {n : Nat} (hn : n ≤ P.I.hashLen) :
    Spec.Sha256.bytesAt t.mem L.dg n = Spec.Sha256.bytesAt m₀ L.dg n := by
  simp only [Spec.Sha256.bytesAt]
  exact List.map_congr_left fun i hi => hc.dg_byte hL (by have := List.mem_range.mp hi; omega_arith)

theorem hok_of (hk : CoreOk P L) (hT : TabL P L) : HOk P L := ⟨hk.1, hT⟩

/-- The count, kept by memory that changed elsewhere. -/
theorem cnt_frame {ws : List Region} {m m' : Mem} (hf : Frame ws m m')
    (hd : ∀ r ∈ ws, Region.Disjoint ⟨L.B + BitVec.ofNat 64 232, 4⟩ r) : cnt L m' = cnt L m :=
  hf.readW (Region.contains_self _ _) hd (by decide)

theorem kvw_cnt (hL : L.Ok) : ∀ r ∈ KVW L, Region.Disjoint ⟨L.B + BitVec.ofNat 64 232, 4⟩ r := by
  have := hL.nB
  simp only [KVW, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact hL.stk_SCR (by omega_arith)
  · exact Lay.LOW_disj (by omega_arith) (by omega_arith)

theorem cw_cnt (hL : L.Ok) : ∀ r ∈ CW L, Region.Disjoint ⟨L.B + BitVec.ofNat 64 232, 4⟩ r := by
  have := hL.nB
  have hfT : fT = 376 := rfl
  have hfTl : fTlen = 152 := rfl
  simp only [CW, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact hL.stk_SCR (by omega_arith)
  · exact Lay.LOW_disj (by omega_arith) (by omega_arith)
  · exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
  · exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)

/-- What `core` changes: `out`, `scratch` and the stack below the frame. -/
abbrev CoreW {dn : Nat} (L : Lay dn) : List Region := [L.OUT, L.SCR, ⟨L.B, 76⟩]

theorem corew_disj (hL : L.Ok) {d n : Nat} (h₁ : 76 ≤ d) (h₂ : d + n ≤ 588) :
    ∀ r ∈ CoreW L, Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r := by
  have := hL.nB
  simp only [CoreW, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact hL.stk_OUT h₂
  · exact hL.stk_SCR h₂
  · exact Offset.disjoint_base _ h₁ (by omega_arith)

/-- The regions the loop writes, which are apart from `core`'s digest. -/
def DgApart {dn : Nat} (L : Lay dn) (r : Region) : Prop :=
  r = L.SCR ∨ r = L.OUT ∨ r = L.LOW ∨ r = ⟨L.B, 76⟩ ∨ r = ⟨L.B + BitVec.ofNat 64 (76 + fTlen), 4⟩ ∨
    r = ⟨L.B + BitVec.ofNat 64 232, 4⟩ ∨ r = ⟨L.B + BitVec.ofNat 64 (76 + fT), 136⟩ ∨
    r = ⟨L.B + BitVec.ofNat 64 76, 128⟩

theorem dg_apart (hL : L.Ok) {r : Region} (h : DgApart L r) : Region.Disjoint ⟨dgAddr P L, P.Q⟩ r := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hQ66, -, -⟩ := P.sizes
  have := hL.nB
  have hfT : fT = 376 := rfl
  have hfTl : fTlen = 152 := rfl
  obtain key : ∀ o, 236 ≤ o → o + P.Q ≤ 76 + fT → Region.Disjoint ⟨L.B + BitVec.ofNat 64 o, P.Q⟩ r := by
    intro o h₁ h₂
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hL.stk_SCR (by omega_arith)
    · exact hL.stk_OUT (by omega_arith)
    · exact Lay.LOW_disj (by omega_arith) (by omega_arith)
    · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
    · exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
    · exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
    · exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
    · exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
  simp only [dgAddr, Cfg.fDg]
  split
  · exact key _ (by simp only [fXc]; omega_arith) (by simp only [fXc]; omega_arith)
  · exact key _ (by simp only [fX]; omega_arith) (by simp only [fX]; omega_arith)

theorem DgOk.frame {m m' : Mem} (h : DgOk P L m₀ m) {ws : List Region} (hf : Frame ws m m')
    (hd : ∀ r ∈ ws, Region.Disjoint ⟨dgAddr P L, P.Q⟩ r) : DgOk P L m₀ m' := by
  obtain hQ : P.Q ≤ 72 := by nums
  unfold DgOk; rw [bytesAt_frame hf hd (by omega_arith)]; exact h

theorem DgOk.frameOf (hL : L.Ok) {m m' : Mem} (h : DgOk P L m₀ m) {ws : List Region}
    (hf : Frame ws m m') (hd : ∀ r ∈ ws, DgApart L r) : DgOk P L m₀ m' :=
  h.frame hf fun r hr => dg_apart hL (hd r hr)

theorem cnt_sub {T i : Nat} (hi : i < T) :
    BitVec.ofNat 32 (T - i) - 1 = BitVec.ofNat 32 (T - (i + 1)) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (1 : BitVec 32).toNat = 1 := rfl
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, h1]
  omega_arith

theorem cnt_ne {T i : Nat} (hT : T < 2 ^ 32) : BitVec.ofNat 32 (T - (i + 1)) ≠ 0 ↔ i + 1 < T := by
  rw [Ne, ← BitVec.toNat_inj]
  have h0 : (0 : BitVec 32).toNat = 0 := rfl
  simp only [BitVec.toNat_ofNat, h0]
  omega_arith

/-- `core`'s signature is the candidate's: it reads the private key, its
digest, and `k`, whose number is `bits2int` of the candidate. -/
theorem coreSig_eq (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) (hdg : DgOk P L m₀ t.mem)
    {i : Nat} (hkv : Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem (kAddr L) P.Q) =
      Spec.Ecdsa.Rfc6979.bits2int P.R.E.C (candI P L m₀ i)) : coreSig P L t.mem = sigI P L m₀ i := by
  obtain e₄ : Spec.Sha256.bytesAt t.mem L.d P.Q = Spec.Sha256.bytesAt m₀ L.d P.Q := hc.dBytes hL (by rw [hk.1])
  simp only [coreSig, coreSigOf, ecdsa_bytesAt, sigI, xOf]
  rw [show Spec.Sha256.bytesAt t.mem (dgAddr P L) P.R.E.C.len = Spec.Sha256.bytesAt t.mem (dgAddr P L) P.Q from rfl,
    hdg, show Spec.Sha256.bytesAt t.mem L.d P.R.E.C.len = Spec.Sha256.bytesAt t.mem L.d P.Q from rfl, e₄,
    show Spec.Sha256.bytesAt t.mem (kAddr L) P.R.E.C.len = Spec.Sha256.bytesAt t.mem (kAddr L) P.Q from rfl, hkv]

theorem ResultIs.eax_zero {r : Option (Nat × Nat)} {t : State} (h : ResultIs P L r t) :
    t.gpr .eax = 0 ↔ r = none := by
  cases r with
  | none => exact ⟨fun _ => rfl, fun _ => h.1⟩
  | some rs => exact ⟨fun h' => by rw [h.1] at h'; exact absurd h' (by decide), fun h' => by cases h'⟩

/-- The result, kept by code that keeps `eax` and changes memory elsewhere. -/
theorem ResultIs.keep {r : Option (Nat × Nat)} {t t' : State} (h : ResultIs P L r t) (ha : t'.gpr .eax = t.gpr .eax)
    (hm : Spec.Sha256.bytesAt t'.mem L.out (2 * P.Q) = Spec.Sha256.bytesAt t.mem L.out (2 * P.Q)) :
    ResultIs P L r t' := by
  cases r with
  | none => exact ⟨by rw [ha]; exact h.1, by rw [hm]; exact h.2⟩
  | some rs => exact ⟨by rw [ha]; exact h.1, by rw [hm]; exact h.2⟩

/-! ## One candidate -/

/-- After the candidate: `k` for `core`. -/
structure P₁ (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) (u : State) : Prop where
  lt : i < P.I.tries
  k : kOf P L u.mem = (kvI P L m₀ i).1
  v : vOf P L u.mem = (Spec.Ecdsa.Rfc6979.genT P.ok.hH.SH.H (kvI P L m₀ i).1 P.nV (kvI P L m₀ i).2).2
  cnt : cnt L u.mem = BitVec.ofNat 32 (P.I.tries - i)
  fails : ∀ j < i, sigI P L m₀ j = none
  dg : DgOk P L m₀ u.mem
  kk : Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt u.mem (kAddr L) P.Q) =
    Spec.Ecdsa.Rfc6979.bits2int P.R.E.C (candI P L m₀ i)

/-- After `core`: its result. -/
structure P₃ (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) (u : State) : Prop where
  lt : i < P.I.tries
  k : kOf P L u.mem = (kvI P L m₀ i).1
  v : vOf P L u.mem = (Spec.Ecdsa.Rfc6979.genT P.ok.hH.SH.H (kvI P L m₀ i).1 P.nV (kvI P L m₀ i).2).2
  cnt : cnt L u.mem = BitVec.ofNat 32 (P.I.tries - i)
  fails : ∀ j < i, sigI P L m₀ j = none
  dg : DgOk P L m₀ u.mem
  res : ResultIs P L (sigI P L m₀ i) u

/-- After the decision: whether to go on. -/
structure Mid (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) (u : State) : Prop where
  lt : i < P.I.tries
  k : kOf P L u.mem = (kvI P L m₀ i).1
  v : vOf P L u.mem = (Spec.Ecdsa.Rfc6979.genT P.ok.hH.SH.H (kvI P L m₀ i).1 P.nV (kvI P L m₀ i).2).2
  cnt : cnt L u.mem = BitVec.ofNat 32 (P.I.tries - (i + 1))
  fails : ∀ j < i, sigI P L m₀ j = none
  dg : DgOk P L m₀ u.mem
  res : ResultIs P L (sigI P L m₀ i) u
  dec : isa.eval .ne u = some (decide (sigI P L m₀ i = none ∧ i + 1 < P.I.tries))

theorem kvw_apart : ∀ r ∈ KVW L, DgApart L r := by
  simp only [KVW, List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) <;> simp [DgApart]

theorem cw_apart : ∀ r ∈ CW L, DgApart L r := by
  simp only [CW, List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl | rfl | rfl) <;> simp [DgApart]

theorem corew_apart : ∀ r ∈ CoreW L, DgApart L r := by
  simp only [CoreW, List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl | rfl) <;> simp [DgApart]

theorem try₁_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) {i : Nat} (hi : LoopInv P L m₀ i t) :
    WP isa (cfgOf P).cand t fun u => Ctx L g m₀ u ∧ P₁ P L m₀ i u :=
  WP.mono (cand_ok hL hT hc hi.saved) fun u₁ ⟨hc₁, hf₁, hk₁, hv₁, hb₁, _⟩ => ⟨hc₁, hi.lt, hk₁.trans hi.k,
    by rw [hv₁, hi.k, hi.v], (cnt_frame hf₁ (cw_cnt hL)).trans hi.cnt, hi.fails,
    hi.dg.frameOf hL hf₁ cw_apart, by rw [hb₁, hi.k, hi.v]; rfl⟩

theorem try₂_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {i : Nat} (hi : P₁ P L m₀ i t) :
    WP isa (.block (cfgOf P).coreArgs) t fun u => Ctx L g m₀ u ∧ P₁ P L m₀ i u ∧ CoreRegs P L u :=
  WP.mono (coreArgs_ok hL hc) fun _ ⟨hc₂, hm₂, hdi, hsi, hdx, hcx, h8⟩ =>
    ⟨hc₂, ⟨hi.lt, hm₂ ▸ hi.k, hm₂ ▸ hi.v, hm₂ ▸ hi.cnt, hi.fails, hm₂ ▸ hi.dg, hm₂ ▸ hi.kk⟩, ⟨hdi, hsi, hdx, hcx, h8⟩⟩

theorem try₃_ok (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) {i : Nat}
    (hi : P₁ P L m₀ i t) (ha : CoreRegs P L t) :
    WP isa (.frame (.push init5) (.call (cfgOf P).coreN (cfgOf P).coreC) (.pop .ecx 5)) t fun u =>
      Ctx L g m₀ u ∧ P₃ P L m₀ i u := by
  obtain ⟨-, -, -, -, -, hD64, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := P.sizes
  refine WP.mono (core_ok (P := P) hL hk hc ha) fun u₃ ⟨hc₃, hf₃, hr₃⟩ => ?_
  rw [coreSig_eq hL hk hc hi.dg hi.kk] at hr₃
  exact ⟨hc₃, hi.lt, (bytesAt_frame hf₃ (corew_disj hL (d := 76) (by decide) (by omega_arith)) (by omega_arith)).trans hi.k,
    (bytesAt_frame hf₃ (corew_disj hL (d := 140) (by decide) (by omega_arith)) (by omega_arith)).trans hi.v,
    (cnt_frame hf₃ (corew_disj hL (by decide) (by decide))).trans hi.cnt, hi.fails,
    hi.dg.frameOf hL hf₃ corew_apart, hr₃⟩

theorem try₄_ok (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) {i : Nat} (hi : P₃ P L m₀ i t) :
    WP isa (.block Cfg.goOn) t fun u => Ctx L g m₀ u ∧ Mid P L m₀ i u := by
  obtain ⟨-, -, -, -, -, hD64, -, -, -, -, -, -, -, -, -, -, hQ66, -, -⟩ := P.sizes
  have := hL.nB
  refine WP.mono (goOn_ok hL hc) fun u₄ ⟨hc₄, hf₄, hn₄, ha₄, hz₄⟩ => ⟨hc₄, hi.lt, ?_, ?_, ?_, hi.fails,
    hi.dg.frameOf hL hf₄ (by simp [DgApart]), ?_, ?_⟩
  · exact (bytesAt_frame hf₄ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith))
      (by omega_arith)).trans hi.k
  · exact (bytesAt_frame hf₄ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith))
      (by omega_arith)).trans hi.v
  · rw [hn₄, hi.cnt, cnt_sub hi.lt]
  · exact hi.res.keep ha₄ (bytesAt_frame hf₄ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hL.stk_OUT (by omega_arith)).symm.sub_left (Region.sub_prefix (by rw [hk.1]))) (by omega_arith))
  · show u₄.zf.map (!·) = _
    rw [hz₄, hi.cnt, cnt_sub hi.lt]
    simp only [Option.map_some, Bool.not_not, hi.res.eax_zero, cnt_ne P.tries_lt]

/-- The branch: step h.3 and the next candidate, or the end. -/
theorem branch_ok (hL : L.Ok) (hk : CoreOk P L) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) {i : Nat} (hi : Mid P L m₀ i t) :
    WP isa (.ite .ne (.seq (cfgOf P).rekey (.block Cfg.again)) (.block Cfg.stop)) t fun t' => Ctx L g m₀ t' ∧
      ((isa.eval .ne t' = some false ∧ Exit P L m₀ i t') ∨
        (isa.eval .ne t' = some true ∧ LoopInv P L m₀ (i + 1) t')) := by
  by_cases hgo : sigI P L m₀ i = none ∧ i + 1 < P.I.tries
  · refine WP.ite true (by rw [hi.dec, decide_eq_true hgo]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine WP.seq (WP.mono (rekey_ok hL (hok_of hk hT) hc) fun u₅ ⟨hc₅, hf₅, hk₅, hv₅, hS₅⟩ => ?_)
    refine WP.mono (again_ok hL hc₅) fun u₆ ⟨hc₆, hm₆, hz₆⟩ => ⟨hc₆, .inr ⟨by show u₆.zf.map _ = _; rw [hz₆]; rfl, ?_⟩⟩
    have hkv : kvI P L m₀ (i + 1) = stepB P.ok.hH.SH.H P.nV (kvI P L m₀ i).1 (kvI P L m₀ i).2 := rfl
    refine ⟨hgo.2, ?_, ?_, ?_, fun j hj => ?_, ?_, by rw [hm₆]; exact hS₅⟩
    · rw [hm₆, hk₅, hi.k, hi.v, hkv]; rfl
    · rw [hm₆, hv₅, hk₅, hi.k, hi.v, hkv]; rfl
    · rw [hm₆, cnt_frame hf₅ (kvw_cnt hL), hi.cnt]
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact hi.fails j hj
      · exact hgo.1
    · rw [hm₆]; exact hi.dg.frameOf hL hf₅ kvw_apart
  · refine WP.ite false (by rw [hi.dec, decide_eq_false hgo]) (fun h => absurd h (by decide)) (fun _ => ?_)
    refine WP.mono (stop_ok hL hc) fun u₅ ⟨hc₅, hm₅, hz₅, ha₅⟩ => ⟨hc₅, .inl ⟨by show u₅.zf.map _ = _; rw [hz₅]; rfl,
      ⟨hi.lt, hi.fails, ?_, hi.res.keep ha₅ (by rw [hm₅])⟩⟩⟩
    by_cases hs : sigI P L m₀ i = none
    · exact .inr (by have := hi.lt; have : ¬ i + 1 < P.I.tries := fun h => hgo ⟨hs, h⟩; omega_arith)
    · exact .inl hs

theorem tryOne_ok (hL : L.Ok) (hk : CoreOk P L) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) {i : Nat}
    (hi : LoopInv P L m₀ i t) :
    WP isa (cfgOf P).tryOne t fun t' => Ctx L g m₀ t' ∧
      ((isa.eval .ne t' = some false ∧ Exit P L m₀ i t') ∨
        (isa.eval .ne t' = some true ∧ LoopInv P L m₀ (i + 1) t')) :=
  WP.seq (WP.mono (try₁_ok hL hT hc hi) fun _ ⟨h₁, p₁⟩ =>
    WP.seq (WP.mono (try₂_ok hL h₁ p₁) fun _ ⟨h₂, p₂, a₂⟩ =>
      WP.seq (WP.mono (try₃_ok hL hk h₂ p₂ a₂) fun _ ⟨h₃, p₃⟩ =>
        WP.seq (WP.mono (try₄_ok hL hk h₃ p₃) fun _ ⟨h₄, p₄⟩ => branch_ok hL hk hT h₄ p₄))))

end VG.Proof.Ecdsa.Rfc6979.X86

end

end


/-!
# Deterministic ECDSA on x86 (32-bit): correctness

The loop leaves it at a candidate that is suitable or the last (`loop_ok`);
before it, `h`, `K`, `V`, `core`'s digest and the count are as RFC 6979's
steps a–g make them (`stageB_ok` … `stageE_ok`); and the signature of that
candidate is RFC 6979's (`result_eq`), for the hash function `P`'s instance
of the contract.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.Impl.Ecdsa.Rfc6979.X86
open VG.Proof.Ecdsa.Rfc6979 (kvAtB candAtB stepB)

variable {P : RfcHash} {L : Lay P.I.hashLen} {g : Reg → BitVec 32} {m₀ : Mem}

/-! ## The frame's entry -/

section Entry

open VG.X86.Wp

variable {cs : List (String × List (BitVec 64))} {I : Proof.Ecdsa.Rfc6979.Instance}
  {H : Impl.Pbkdf2.Whole.X86.Fns} {f : Fns} {ns : List String} {s : State}

/-- A word of the stack, through a store elsewhere in it. -/
theorem stk_sep (B : Addr) (m : Mem) {x y : Nat} (v : BitVec 32)
    (h : x + 4 ≤ y ∨ y + 4 ≤ x) (hx : x + 4 ≤ 616) (hy : y + 4 ≤ 616) :
    (m.writeW (B + BitVec.ofNat 64 y) v).readW (B + BitVec.ofNat 64 x) 32 = m.readW (B + BitVec.ofNat 64 x) 32 :=
  Mem.readW_writeW_sep (Offset.sep _ h (by omega_arith) (by omega_arith)) (by decide)

/-- Our caller's registers, `hmac`'s address, and its `D` and `B` in the
frame: `Ctx` holds. -/
theorem entry_ok (h : (rfcX86 cs I 612 (tabFacts H f) ns).pre s) :
    WP isa (.block Cfg.entry) (entered s) fun t₁ => t₁.gpr .eax = arg s 5 ∧
      t₁.gpr .esp = (lay I.hashLen I.ecdsa.curve.len cs H f s).F ∧
      WP isa (.block Cfg.tabDB) t₁ (Ctx (lay I.hashLen I.ecdsa.curve.len cs H f s) s.gpr s.mem) := by
  obtain hL := lay_ok h
  have nB := hL.nB
  have nt : (arg s 5).toNat + 24 ≤ 2 ^ 32 := hL.nt
  have hh := h
  obtain ⟨e612, e28, hrd, hwr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hTb, -, -, -, -, -, -, hF⟩ := hh
  have e588 : 588 ≤ (s.gpr .esp).toNat := by omega_arith
  obtain ⟨tOk, tMem, tD, tB⟩ := hF
  obtain hesp : (entered s).gpr .esp = (lay I.hashLen I.ecdsa.curve.len cs H f s).F :=
    entered_esp _ _ cs H f s
  obtain hw : ∀ o, o + 4 ≤ 512 → InRegions (entered s).wr (addr (lay I.hashLen I.ecdsa.curve.len cs H f s).F o) 4 :=
    fun o ho => ⟨(lay I.hashLen I.ecdsa.curve.len cs H f s).FR, by rw [entered_wr h]; simp, by
      rw [hL.addrF (by omega_arith)]; exact Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)⟩
  obtain hg : ∀ r, r ≠ .esp → (entered s).gpr r = s.gpr r := fun r hr => allocState_gpr _ _ hr
  obtain a : ∀ o, o < 540 → addr (lay I.hashLen I.ecdsa.curve.len cs H f s).F o =
      (lay I.hashLen I.ecdsa.curve.len cs H f s).B + BitVec.ofNat 64 (76 + o) := fun o ho => hL.addrF ho
  obtain hA : ∀ i < 6, (lay I.hashLen I.ecdsa.curve.len cs H f s).B + BitVec.ofNat 64 (592 + 4 * i) = argAddr s i :=
    fun i hi => (lay_argAddr e588 e28 hi).symm
  -- The table's words, apart from the stack.
  obtain hTab : ∀ o, o + 4 ≤ 24 → (lay I.hashLen I.ecdsa.curve.len cs H f s).TAB.Contains
      (addr (arg s 5) o) (32 / 8) := fun o ho => by
    rw [addr_eq (by omega_arith)]; exact Offset.contains_base _ ho (by omega_arith)
  simp only [Cfg.entry, saved, fSave, List.map_cons, List.map_nil, List.cons_append, List.nil_append, stk,
    Nat.reduceAdd]
  refine wp_stm hesp (hw 128 (by omega_arith)) fun s₁ u₁ => ?_
  refine wp_stm (B := (lay I.hashLen I.ecdsa.curve.len cs H f s).F) (by rw [u₁.gpr, hesp])
    (by rw [u₁.wr]; exact hw 132 (by omega_arith)) fun s₂ u₂ => ?_
  refine wp_stm (B := (lay I.hashLen I.ecdsa.curve.len cs H f s).F) (by rw [u₂.gpr, u₁.gpr, hesp])
    (by rw [u₂.wr, u₁.wr]; exact hw 136 (by omega_arith)) fun s₃ u₃ => ?_
  refine wp_stm (B := (lay I.hashLen I.ecdsa.curve.len cs H f s).F) (by rw [u₃.gpr, u₂.gpr, u₁.gpr, hesp])
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact hw 140 (by omega_arith)) fun s₄ u₄ => ?_
  obtain esp₄ : s₄.gpr .esp = (lay I.hashLen I.ecdsa.curve.len cs H f s).F := by
    rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, hesp]
  obtain m₄ : s₄.mem = (((s.mem.writeW ((lay I.hashLen I.ecdsa.curve.len cs H f s).B + BitVec.ofNat 64 204) (s.gpr .ebx)).writeW
      ((lay I.hashLen I.ecdsa.curve.len cs H f s).B + BitVec.ofNat 64 208) (s.gpr .esi)).writeW
      ((lay I.hashLen I.ecdsa.curve.len cs H f s).B + BitVec.ofNat 64 212) (s.gpr .edi)).writeW
      ((lay I.hashLen I.ecdsa.curve.len cs H f s).B + BitVec.ofNat 64 216) (s.gpr .ebp) := by
    simp only [u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₃.gpr, u₂.gpr, u₁.gpr]
    rw [a 128 (by omega_arith), a 132 (by omega_arith), a 136 (by omega_arith), a 140 (by omega_arith),
      hg .ebx (by decide), hg .esi (by decide), hg .edi (by decide), hg .ebp (by decide)]
    rfl
  obtain ct : ∀ x, 204 ≤ x → x + 4 ≤ 228 → (⟨(lay I.hashLen I.ecdsa.curve.len cs H f s).B + BitVec.ofNat 64 204, 24⟩ :
      Region).Contains ((lay I.hashLen I.ecdsa.curve.len cs H f s).B + BitVec.ofNat 64 x) (32 / 8) :=
    fun x h₁ h₂ => Offset.contains _ h₁ (by omega_arith) (by omega_arith)
  obtain hf₄ : Frame [⟨(lay I.hashLen I.ecdsa.curve.len cs H f s).B + BitVec.ofNat 64 204, 24⟩] s.mem s₄.mem := by
    rw [m₄]
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (ct 204 (by omega_arith) (by omega_arith))).writeW
      (List.mem_singleton_self _) _ (ct 208 (by omega_arith) (by omega_arith))).writeW (List.mem_singleton_self _) _
      (ct 212 (by omega_arith) (by omega_arith))).writeW (List.mem_singleton_self _) _ (ct 216 (by omega_arith) (by omega_arith))
  obtain tabD : ∀ r ∈ [(⟨(lay I.hashLen I.ecdsa.curve.len cs H f s).B + BitVec.ofNat 64 204, 24⟩ : Region)],
      Region.Disjoint (lay I.hashLen I.ecdsa.curve.len cs H f s).TAB r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hL.tk.sub_right (Lay.sub_STK (by omega_arith))
  -- `eax = hmac`.
  refine wp_ldm (B := (lay I.hashLen I.ecdsa.curve.len cs H f s).F) (o := 512 + 4 + 4 * 5) esp₄
    ⟨(lay I.hashLen I.ecdsa.curve.len cs H f s).ARGS, by
      rw [u₄.rd, u₄.wr, u₃.wr, u₂.wr, u₁.wr, entered_wr h, hwr, lay_ARGS e588 e28]; simp, by
      rw [a _ (by omega_arith)]; exact Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)⟩
    fun s₅ u₅ => WP.block_nil ?_
  obtain eax₅ : s₅.gpr .eax = arg s 5 := by
    rw [u₅.gpr, a _ (by omega_arith), show 76 + (512 + 4 + 4 * 5) = 592 + 4 * 5 from rfl, hA 5 (by decide)]
    exact hf₄.readW (r := (lay I.hashLen I.ecdsa.curve.len cs H f s).ARGS)
      (by rw [← hA 5 (by decide)]; exact Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)) (by decide)
  refine ⟨eax₅, by rw [u₅.other _ (by decide), esp₄], ?_⟩
  -- `D` and `B`.
  simp only [Cfg.tabDB, stk, fDl, fBl, VG.Impl.Pbkdf2.Stream.X86.at_]
  obtain hrd₅ : s₅.rd = s.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]; rfl
  obtain hwr₅ : s₅.wr = (entered s).wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  obtain inTab : ∀ o, o + 4 ≤ 24 → InRegions (s₅.rd ++ s₅.wr) (addr (arg s 5) o) 4 := fun o ho =>
    ⟨(lay I.hashLen I.ecdsa.curve.len cs H f s).TAB, by rw [hrd₅, hrd]; simp [Lay.TAB, Lay.tab, lay], hTab o ho⟩
  refine wp_ldm eax₅ (inTab 16 (by omega_arith)) fun s₆ u₆ => ?_
  refine wp_stm (B := (lay I.hashLen I.ecdsa.curve.len cs H f s).F)
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), esp₄])
    (by rw [u₆.wr, hwr₅]; exact hw 144 (by omega_arith)) fun s₇ u₇ => ?_
  refine wp_ldm (B := arg s 5) (by rw [u₇.gpr, u₆.other _ (by decide), eax₅])
    (by rw [u₇.rd, u₇.wr, u₆.rd, u₆.wr]; exact inTab 20 (by omega_arith)) fun s₈ u₈ => ?_
  refine wp_stm (B := (lay I.hashLen I.ecdsa.curve.len cs H f s).F)
    (by rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), esp₄])
    (by rw [u₈.wr, u₇.wr, u₆.wr, hwr₅]; exact hw 148 (by omega_arith)) fun s₉ u₉ => WP.block_nil ?_
  -- The table's words, as on entry.
  obtain tw : ∀ o, o + 4 ≤ 24 → s₄.mem.readW (addr (arg s 5) o) 32 = s.mem.readW (addr (arg s 5) o) 32 :=
    fun o ho => hf₄.readW (hTab o ho) tabD (by decide)
  obtain vD : s₆.gpr .ecx = BitVec.ofNat 32 H.H.D := by rw [u₆.gpr, u₅.mem, tw 16 (by omega_arith), tD]
  obtain m₇ : s₇.mem = s₄.mem.writeW ((lay I.hashLen I.ecdsa.curve.len cs H f s).B + BitVec.ofNat 64 220)
      (BitVec.ofNat 32 H.H.D) := by rw [u₇.mem, u₆.mem, u₅.mem, vD, a 144 (by omega_arith)]
  obtain hf₇ : Frame [⟨(lay I.hashLen I.ecdsa.curve.len cs H f s).B + BitVec.ofNat 64 204, 24⟩] s.mem s₇.mem := by
    rw [m₇]; exact hf₄.writeW (List.mem_singleton_self _) _ (ct 220 (by omega_arith) (by omega_arith))
  obtain vB : s₈.gpr .ecx = BitVec.ofNat 32 H.H.B := by
    rw [u₈.gpr, hf₇.readW (hTab 20 (by omega_arith)) tabD (by decide), tB]
  obtain m₉ : s₉.mem = s₇.mem.writeW ((lay I.hashLen I.ecdsa.curve.len cs H f s).B + BitVec.ofNat 64 224)
      (BitVec.ofNat 32 H.H.B) := by rw [u₉.mem, u₈.mem, vB, a 148 (by omega_arith)]
  obtain hf₉ : Frame [⟨(lay I.hashLen I.ecdsa.curve.len cs H f s).B + BitVec.ofNat 64 204, 24⟩] s.mem s₉.mem := by
    rw [m₉]; exact hf₇.writeW (List.mem_singleton_self _) _ (ct 224 (by omega_arith) (by omega_arith))
  obtain sy₉ : s₉.syms = s.syms := by
    rw [u₉.syms, u₈.syms, u₇.syms, u₆.syms, u₅.syms, u₄.syms, u₃.syms, u₂.syms, u₁.syms]; rfl
  refine
    { rd := by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, hrd₅, hrd, lay_tbls]; rfl
      wr := by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, hwr₅, entered_wr h, hwr, lay_ARGS e588 e28]; rfl
      esp := by rw [u₉.gpr, u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), esp₄]
      saved := fun p hp => ?_
      pArg := fun i hi => ?_
      pDl := by
        rw [m₉, stk_sep _ _ _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith), m₇,
          Mem.readW_writeW_self32]; rfl
      pBl := by rw [m₉, Mem.readW_writeW_self32]; rfl
      frame := hf₉.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨(lay I.hashLen I.ecdsa.curve.len cs H f s).STK, by simp,
          Lay.sub_STK (d := 204) (n := 24) (by omega_arith)⟩
      sy := fun c hc => by rw [sy₉]; exact (lay_sy s hc).symm
      held := fun c hc => by
        change c ∈ cs at hc
        simpa only [lay_sy s hc] using hTb.1 c hc
      tabOk := by rw [sy₉]; exact tOk
      tabMem := by rw [sy₉]; exact tMem
      fsy := fun n hn => by rw [sy₉]; exact (ite_eq_left hn).symm }
  · simp only [saved, fSave, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> dsimp only [Nat.reduceAdd]
    · rw [m₉, stk_sep _ _ _ (x := 204) (y := 224) (by omega_arith) (by omega_arith) (by omega_arith), m₇, stk_sep _ _ _ (x := 204) (y := 220) (by omega_arith) (by omega_arith) (by omega_arith), m₄, stk_sep _ _ _ (x := 204) (y := 216) (by omega_arith) (by omega_arith) (by omega_arith), stk_sep _ _ _ (x := 204) (y := 212) (by omega_arith) (by omega_arith) (by omega_arith), stk_sep _ _ _ (x := 204) (y := 208) (by omega_arith) (by omega_arith) (by omega_arith), Mem.readW_writeW_self32]
    · rw [m₉, stk_sep _ _ _ (x := 208) (y := 224) (by omega_arith) (by omega_arith) (by omega_arith), m₇, stk_sep _ _ _ (x := 208) (y := 220) (by omega_arith) (by omega_arith) (by omega_arith), m₄, stk_sep _ _ _ (x := 208) (y := 216) (by omega_arith) (by omega_arith) (by omega_arith), stk_sep _ _ _ (x := 208) (y := 212) (by omega_arith) (by omega_arith) (by omega_arith), Mem.readW_writeW_self32]
    · rw [m₉, stk_sep _ _ _ (x := 212) (y := 224) (by omega_arith) (by omega_arith) (by omega_arith), m₇, stk_sep _ _ _ (x := 212) (y := 220) (by omega_arith) (by omega_arith) (by omega_arith), m₄, stk_sep _ _ _ (x := 212) (y := 216) (by omega_arith) (by omega_arith) (by omega_arith), Mem.readW_writeW_self32]
    · rw [m₉, stk_sep _ _ _ (x := 216) (y := 224) (by omega_arith) (by omega_arith) (by omega_arith), m₇, stk_sep _ _ _ (x := 216) (y := 220) (by omega_arith) (by omega_arith) (by omega_arith), m₄, Mem.readW_writeW_self32]
  · rw [hf₉.readW (r := ⟨(lay I.hashLen I.ecdsa.curve.len cs H f s).B + BitVec.ofNat 64 (592 + 4 * i), 4⟩)
      (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)) (by decide),
      hA i hi, lay_a s i hi]
    rfl

end Entry

/-! ## The loop -/

theorem tries_ok (hL : L.Ok) (hk : CoreOk P L) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) (h0 : LoopInv P L m₀ 0 t) :
    WP isa (.loop (cfgOf P).tryOne .ne) t fun t' => Ctx L g m₀ t' ∧ ∃ i, Exit P L m₀ i t' := by
  refine WP.loop (M := isa) (fun n (s : State) => Ctx L g m₀ s ∧ LoopInv P L m₀ (P.I.tries - n) s ∧ n ≤ P.I.tries)
    ?_ P.I.tries t
    ⟨hc, by rw [Nat.sub_self]; exact h0, Nat.le_refl _⟩
  rintro n s ⟨hcs, hi, hn⟩
  obtain hn1 : 1 ≤ n := by have := hi.lt; omega_using [this]
  refine WP.mono (tryOne_ok hL hk hT hcs hi) fun s' ⟨hc', h⟩ => ?_
  rcases h with ⟨he, hx⟩ | ⟨he, hx⟩
  · exact .inl ⟨he, hc', _, hx⟩
  · refine .inr ⟨he, n - 1, by omega_using [hn1], hc', ?_, by omega_using [hn]⟩
    rwa [show P.I.tries - (n - 1) = P.I.tries - n + 1 by omega_using [hn, hn1]]

/-! ## Steps a–g -/

/-- `rlen` is the scalars' `Q` bytes. -/
theorem rlen_eq (P : RfcHash) : Spec.Ecdsa.Rfc6979.rlen P.R.E.C = P.Q := by
  have := P.R.nBits_len
  exact rlenR (by show _ ≤ 8 * P.R.E.C.len; omega_using [this]) (by show 8 * P.R.E.C.len < _; omega_using [this])

/-- RFC 6979's `K` and `V` after step g, from the code's. -/
theorem kv0_eq (P : RfcHash) {x : Nat} {dB hB h : List Byte} (hd : dB.length = P.Q)
    (hx : x = Spec.Weierstrass.ofBytes dB) (hh : Spec.Ecdsa.Rfc6979.bits2octets P.R.E.C hB = h) :
    Spec.Ecdsa.Rfc6979.init P.R.E.C P.ok.hH.SH.H P.F.H.D x hB =
      let K₁ := P.mac (List.replicate P.F.H.D 0) (List.replicate P.F.H.D 1 ++ [BitVec.ofNat 8 0] ++ (dB ++ h))
      let V₁ := P.mac K₁ (List.replicate P.F.H.D 1)
      let K₂ := P.mac K₁ (V₁ ++ [BitVec.ofNat 8 1] ++ (dB ++ h))
      (K₂, P.mac K₂ V₁) := by
  obtain hi : Spec.Ecdsa.Rfc6979.int2octets P.R.E.C x = dB := by
    rw [Spec.Ecdsa.Rfc6979.int2octets, rlen_eq, hx, ← hd, toBytes_ofBytes]
  simp only [Spec.Ecdsa.Rfc6979.init, hi, hh, List.append_assoc, List.singleton_append]
  rfl

/-- `h`, RFC 6979's `bits2octets` of the digest. -/
abbrev hSpec (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte :=
  Spec.Ecdsa.Rfc6979.bits2octets P.R.E.C (hBOf P L m₀)
abbrev dB (P : RfcHash) {dn : Nat} (L : Lay dn) (m₀ : Mem) : List Byte := Spec.Sha256.bytesAt m₀ L.d P.Q

/-- `K` and `V` after steps d and e. -/
abbrev K₁ (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte :=
  P.mac (List.replicate P.F.H.D 0) (List.replicate P.F.H.D 1 ++ [BitVec.ofNat 8 0] ++ (dB P L m₀ ++ hSpec P L m₀))
abbrev V₁ (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte := P.mac (K₁ P L m₀) (List.replicate P.F.H.D 1)

/-- After step c: `h`, `V = 0x01…`, `K = 0x00…` and `core`'s digest. -/
structure QB (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (u : State) : Prop where
  h : hOf P L u.mem = hSpec P L m₀
  k : kOf P L u.mem = List.replicate P.F.H.D 0
  v : vOf P L u.mem = List.replicate P.F.H.D 1
  dg : DgOk P L m₀ u.mem

/-- After step e. -/
structure QC (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (u : State) : Prop where
  h : hOf P L u.mem = hSpec P L m₀
  k : kOf P L u.mem = K₁ P L m₀
  v : vOf P L u.mem = V₁ P L m₀
  dg : DgOk P L m₀ u.mem
  saved : SavedK P L u.mem (kOf P L u.mem)

/-- After step g. -/
structure QD (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (u : State) : Prop where
  k : kOf P L u.mem = (kv0 P L m₀).1
  v : vOf P L u.mem = (kv0 P L m₀).2
  dg : DgOk P L m₀ u.mem
  saved : SavedK P L u.mem (kOf P L u.mem)

theorem kv0_eq' (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) :
    kv0 P L m₀ = (P.mac (K₁ P L m₀) (V₁ P L m₀ ++ [BitVec.ofNat 8 1] ++ (dB P L m₀ ++ hSpec P L m₀)),
      P.mac (P.mac (K₁ P L m₀) (V₁ P L m₀ ++ [BitVec.ofNat 8 1] ++ (dB P L m₀ ++ hSpec P L m₀))) (V₁ P L m₀)) :=
  kv0_eq P (length_bytesAt _ _ _) rfl rfl

/-- The digest's integer is `X`'s, `Q - m` zero bytes then the digest's first
`m = min(D, Q)`, if the scalars have `8 Q` bits. -/
theorem x_eq {C : Spec.Weierstrass.Curve} {Q D : Nat} (hq : Spec.Ecdsa.nBits C = 8 * Q) (hn : C.n ≠ 0)
    {hB : List Byte} (hl : hB.length = D) :
    Spec.Weierstrass.ofBytes (List.replicate (Q - min D Q) 0 ++ hB.take (min D Q)) = Spec.Ecdsa.hashToInt C hB := by
  by_cases h : Q ≤ D
  · rw [Nat.min_eq_right h, Nat.sub_self, List.replicate_zero, List.nil_append,
      hashToInt_takeQ hq (by rw [hl]; exact h)]
  · rw [Nat.min_eq_left (by omega_using [h]), List.take_of_length_le (by rw [hl]), ofBytes_zeros,
      (hashToInt_short (by rw [hl, hq]; omega_using [h]) hn).1]

/-- After `X` and `h`: `h`, and `core`'s digest. -/
structure QA (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (u : State) : Prop where
  h : hOf P L u.mem = hSpec P L m₀
  dg : DgOk P L m₀ u.mem

/-- After `X`: `Q - m` zero bytes, then the digest's first `m = min(D, Q)`. -/
abbrev QX (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (u : State) : Prop :=
  Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (76 + fX)) P.Q =
    List.replicate (P.Q - min P.F.H.D P.Q) 0 ++ (hBOf P L m₀).take (min P.F.H.D P.Q)

theorem stageX_ok (hL : L.Ok) (hT : TabL P L) {u : State} (hc : Ctx L g m₀ u) :
    WP isa (cfgOf P).prepX u fun u' => Ctx L g m₀ u' ∧ QX P L m₀ u' := by
  have hD : P.F.H.D = P.I.hashLen := P.len.symm
  obtain ⟨-, -, -, -, hD16, hD64, -, -, -, -, -, -, -, -, -, hQ8, hQ66, -, -⟩ := P.sizes
  obtain hdg : Spec.Sha256.bytesAt u.mem L.dg (min P.F.H.D P.Q) =
      (hBOf P L m₀).take (min P.F.H.D P.Q) := by
    rw [hc.dgBytes hL (by rw [← hD]; omega_using []), hBOf, ← bytesAt_take _ _ (Nat.min_le_left _ _)]
  exact WP.mono (prepX_ok hL hT (by rw [← hD]) hc) fun u₁ ⟨hc₁, _, hx₁⟩ => ⟨hc₁, by show Spec.Sha256.bytesAt _ _ _ = _; rw [hx₁, hdg]⟩

/-- `h` (step c's `h1` as `bits2octets`), and `core`'s digest. -/
theorem stageH_ok (hL : L.Ok) (hT : TabL P L) {u₁ : State} (hc₁ : Ctx L g m₀ u₁) (hx₁ : QX P L m₀ u₁) :
    WP isa (cfgOf P).prepH u₁ fun u' => Ctx L g m₀ u' ∧ QA P L m₀ u' := by
  have hD : P.F.H.D = P.I.hashLen := P.len.symm
  have hl := P.R.nBits_len
  obtain ⟨-, -, -, -, hD16, hD64, -, -, -, -, -, -, -, -, -, hQ8, hQ66, -, -⟩ := P.sizes
  obtain hlB : (hBOf P L m₀).length = P.F.H.D := length_bytesAt _ _ _
  unfold QX at hx₁
  cases hb : P.R.big
  · have hq : Spec.Ecdsa.nBits P.R.E.C = 8 * P.Q := (P.R.sizesA hb).2.2.1
    obtain hX : Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt u₁.mem (xa L) P.Q) = eOf P L m₀ := by
      rw [show xa L = L.B + BitVec.ofNat 64 (76 + fX) from rfl, hx₁, x_eq hq P.R.n_ne hlB]
    rw [show (cfgOf P).prepH = .block (cfgOf P).reduce by simp only [Cfg.prepH, show (cfgOf P).big = false from hb,
      Bool.false_eq_true, ite_false]]
    obtain ⟨hQk, -, hQ64⟩ := P.sizesA hb
    refine WP.mono (reduce_ok hb hL hc₁) fun u₂ ⟨hc₂, hf₂, hh₂⟩ => ⟨hc₂, ?_, ?_⟩
    · rw [← hQk] at hh₂
      show Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 (76 + (cfgOf P).fHo)) P.Q = _
      rw [show (cfgOf P).fHo = fH by simp only [Cfg.fHo, show (cfgOf P).big = false from hb, Bool.false_eq_true,
        ite_false], show 76 + fH = hB from rfl]
      conv_lhs => rw [← toBytes_ofBytes (Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 hB) P.Q)]
      rw [length_bytesAt, hh₂, hX, hSpec, Spec.Ecdsa.Rfc6979.bits2octets,
        Spec.Ecdsa.Rfc6979.int2octets, Spec.Ecdsa.Rfc6979.bits2int, rlen_eq]
    · unfold DgOk
      simp only [dgAddr, Cfg.fDg, show (cfgOf P).big = false from hb, Bool.false_eq_true, ite_false]
      have := hL.nB
      have hfX : fX = 232 := rfl
      have hhB : hB = 236 := rfl
      rw [bytesAt_frame hf₂ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact Offset.disjoint _ (.inr (by omega_using [hfX])) (by omega_using [hQ66, hfX]) (by omega_using [])
          · exact Offset.disjoint _ (.inr (by omega)) (by omega_using [hQ66, hfX]) (by omega)) (by omega_using [hQ66]),
        hashToInt_takeQ hq (by rw [length_bytesAt]), List.take_of_length_le (by rw [length_bytesAt])]
      exact hX
  · obtain ⟨-, hQ66', -, hQD⟩ := P.sizesW hb
    obtain hN : 8 * P.F.H.D < Spec.Ecdsa.nBits P.R.E.C := by
      have : P.F.H.D < P.R.E.C.len := hQD
      omega_using [hl, this]
    obtain hm : min P.F.H.D P.Q = P.F.H.D := Nat.min_eq_left (by omega_using [hQD])
    rw [hm, List.take_of_length_le (by rw [hlB])] at hx₁
    rw [show (cfgOf P).prepH = (cfgOf P).prepC by simp only [Cfg.prepH, show (cfgOf P).big = true from hb, ite_true]]
    refine WP.mono (prepC_ok hL hT hb (by rw [← hD]) hc₁) fun u₂ ⟨hc₂, hf₂, hx₂⟩ => ⟨hc₂, ?_, ?_⟩
    · show Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 (76 + (cfgOf P).fHo)) P.Q = _
      rw [show (cfgOf P).fHo = fX by simp only [Cfg.fHo, show (cfgOf P).big = true from hb, ite_true],
        bytesAt_frame hf₂ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact hL.stk_scr (by simp only [fX]; omega_using [hQ66]) (by decide)
          · exact Offset.disjoint _ (.inl (by simp only [fX, fXc]; omega_using [hQ66])) (by simp only [fX]; omega_using [hQ66])
              (by simp only [fXc]; omega_using [])) (by omega_using [hQ66]),
        hx₁, hSpec, bits2octets_short (R := P.Q) (by show _ ≤ 8 * P.R.E.C.len; omega_using [hl])
          (by show 8 * P.R.E.C.len < _; omega_using [hl]) (by rw [hlB]; exact hN) P.R.n_ne, hlB]
    · -- `core`'s digest: the digest's number `e`, shifted left by `sh` bits.
      obtain e₂ : eOf P L m₀ = Spec.Weierstrass.ofBytes (hBOf P L m₀) :=
        (hashToInt_short (by rw [hlB]; exact hN) P.R.n_ne).1
      rw [hc₁.dgBytes hL (by rw [← hD])] at hx₂
      obtain hlt : Spec.Weierstrass.ofBytes (hBOf P L m₀) * 2 ^ P.R.sh < 2 ^ (8 * P.Q) := by
        have := ofBytes_lt (hBOf P L m₀)
        rw [hlB] at this
        calc _ < 2 ^ (8 * P.F.H.D) * 2 ^ P.R.sh := Nat.mul_lt_mul_of_pos_right this (Nat.two_pow_pos _)
          _ ≤ 2 ^ (8 * P.Q) := by
            rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by omega_using []) (by simp only [RfcHash.Q]; omega_using [hl, hN])
      obtain hl₁ : (Spec.Weierstrass.toBytes P.Q (Spec.Weierstrass.ofBytes (hBOf P L m₀) * 2 ^ P.R.sh)).length = P.Q := by
        simp [Spec.Weierstrass.toBytes]
      unfold DgOk
      simp only [dgAddr, Cfg.fDg, show (cfgOf P).big = true from hb, ite_true]
      rw [hx₂, hashToInt_takeR (R := P.Q) (by show _ ≤ 8 * P.R.E.C.len; omega_using [hl]) (by rw [hl₁]),
        List.take_of_length_le (by rw [hl₁]), ofBytes_toBytes _ _ hlt,
        show 8 * P.Q - Spec.Ecdsa.nBits P.R.E.C = P.R.sh from hl.2.2.symm, Nat.shiftRight_eq_div_pow,
        Nat.mul_div_cancel _ (Nat.two_pow_pos _), e₂]

/-- `h` in the message, kept by the steps on `K` and `V`. -/
theorem hOf_frame (hL : L.Ok) {ws : List Region} {m m' : Mem} (hf : Frame ws m m')
    (hd : ∀ r ∈ ws, r = L.SCR ∨ r = L.LOW ∨ ∃ o n, r = ⟨L.B + BitVec.ofNat 64 o, n⟩ ∧ o + n ≤ 76 + fH) :
    hOf P L m' = hOf P L m := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hQ66, -, -⟩ := P.sizes
  have := hL.nB
  obtain hho : 76 + fH ≤ 76 + (cfgOf P).fHo ∧ 76 + (cfgOf P).fHo + P.Q ≤ 76 + fXc := by
    simp only [Cfg.fHo]; split <;> simp only [fH, fX, fXc] <;> omega_using [hQ66]
  refine bytesAt_frame hf (fun r hr => ?_) (by omega_using [hQ66])
  rcases hd r hr with rfl | rfl | ⟨o, n, rfl, hon⟩
  · exact hL.stk_SCR (by simp only [fXc] at hho; omega_using [hho])
  · exact Lay.LOW_disj (by simp only [fH] at hho; omega_using [hho]) (by simp only [fXc] at hho; omega_using [hho])
  · exact Offset.disjoint _ (.inr (by omega_using [hho, hon])) (by simp only [fXc] at hho; omega_using [hho]) (by simp only [fH] at hon; omega_using [hon])

theorem hOf_kvw (hL : L.Ok) {m m' : Mem} (hf : Frame (KVW L) m m') : hOf P L m' = hOf P L m :=
  hOf_frame hL hf fun r hr => by
    simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inl rfl
    · exact .inr (.inl rfl)

/-- `V = 0x01…` and `K = 0x00…`. -/
theorem stageB_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (hq : QA P L m₀ u) :
    WP isa (.block Cfg.initKV) u fun u' => Ctx L g m₀ u' ∧ QB P L m₀ u' := by
  obtain ⟨-, -, -, -, -, hD64, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := P.sizes
  exact WP.mono (initKV_ok hL hc) fun u₂ ⟨hc₂, hf₂, hv₂, hk₂⟩ =>
    ⟨hc₂, ⟨(hOf_frame hL hf₂ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact .inr (.inr ⟨76, 128, rfl, by simp only [fH]; omega_using []⟩)).trans hq.h,
      hk₂ _ hD64, hv₂ _ hD64, hq.dg.frameOf hL hf₂ (by simp [DgApart])⟩⟩

theorem stageC_ok (hL : L.Ok) (hk : CoreOk P L) (hT : TabL P L) {u : State} (hc : Ctx L g m₀ u) (hq : QB P L m₀ u) :
    WP isa ((cfgOf P).rekeyFull 0) u fun u' => Ctx L g m₀ u' ∧ QC P L m₀ u' :=
  WP.mono (rekeyFull_ok hL (hok_of hk hT) hc 0 fun h => absurd rfl h) fun u' ⟨hc', hf', hk', hv', hS'⟩ =>
    ⟨(hOf_kvw hL hf').trans hq.h,
      by rw [hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.1])],
      by rw [hv', hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.1])], hq.dg.frameOf hL hf' kvw_apart, hS'⟩ |>
    fun h => ⟨hc', h⟩

theorem stageD_ok (hL : L.Ok) (hk : CoreOk P L) (hT : TabL P L) {u : State} (hc : Ctx L g m₀ u) (hq : QC P L m₀ u) :
    WP isa ((cfgOf P).rekeyFull 1) u fun u' => Ctx L g m₀ u' ∧ QD P L m₀ u' :=
  WP.mono (rekeyFull_ok hL (hok_of hk hT) hc 1 fun _ => hq.saved) fun u' ⟨hc', hf', hk', hv', hS'⟩ =>
    ⟨hc', by rw [kv0_eq', hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.1])],
      by rw [kv0_eq', hv', hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.1])], hq.dg.frameOf hL hf' kvw_apart, hS'⟩

theorem stageE_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (hq : QD P L m₀ u) :
    WP isa (.block (cfgOf P).initCnt) u fun u' => Ctx L g m₀ u' ∧ LoopInv P L m₀ 0 u' :=
  have := hL.nB
  have hD64 : P.F.H.D ≤ 64 := P.sizes.2.2.2.2.2.1
  WP.mono (initCnt_ok hL hc) fun u' ⟨hc', hf', hn'⟩ => ⟨hc', P.tries_pos,
    (bytesAt_frame hf' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (.inl (by omega_using [hD64])) (by omega_using [hD64]) (by omega_using []))
      (by omega_using [hD64])).trans hq.k,
    (bytesAt_frame hf' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (.inl (by omega_using [hD64])) (by omega_using [hD64]) (by omega_using []))
      (by omega_using [hD64])).trans hq.v,
    by rw [hn', Nat.sub_zero], fun j hj => absurd hj (Nat.not_lt_zero _), hq.dg.frameOf hL hf' (by simp [DgApart]),
    by
      obtain hk' : kOf P L u'.mem = kOf P L u.mem := bytesAt_frame hf' (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (.inl (by omega_using [hD64])) (by omega_using [hD64]) (by omega_using [])) (by omega_using [hD64])
      rw [hk']
      exact hq.saved.frame hf' fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (hL.stk_scr (d := 232) (n := 4) (by omega_using []) (by decide)).symm⟩

theorem stageG_ok (hL : L.Ok) (hk : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) {i : Nat}
    (hx : Exit P L m₀ i u) :
    WP isa (.block Cfg.wipe) u fun u' => Ctx L g m₀ u' ∧ Exit P L m₀ i u' ∧ ∀ p ∈ saved, u'.gpr p.1 = g p.1 :=
  have hQ66 : P.Q ≤ 66 := P.sizes.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  WP.mono (wipe_ok hL hc) fun _ ⟨hc₇, ha₇, hf₇, hs₇⟩ => ⟨hc₇, ⟨hx.lt, hx.fails, hx.last,
    hx.res.keep ha₇ (bytesAt_frame hf₇ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hL.stk_OUT (d := 76) (n := 128) (by omega_using [])).symm.sub_left (Region.sub_prefix (by rw [hk.1]))
      · exact (hL.stk_OUT (d := 228) (n := 360) (by omega_using [])).symm.sub_left
          (Region.sub_prefix (by rw [hk.1]))) (by omega_using [hQ66]))⟩, hs₇⟩

/-- The body after the frame's entry. -/
abbrev rest (P : RfcHash) : Prog isa :=
  .seq (cfgOf P).prepX (.seq (cfgOf P).prepH (.seq (.block Cfg.initKV) (.seq ((cfgOf P).rekeyFull 0)
    (.seq ((cfgOf P).rekeyFull 1) (.seq (.block (cfgOf P).initCnt) (.seq (.loop (cfgOf P).tryOne .ne)
      (.block Cfg.wipe)))))))

theorem body_eq (P : RfcHash) : (cfgOf P).body = .seq (.block Cfg.entry) (.seq (.block Cfg.tabDB) (rest P)) := rfl

theorem rest_ok (hL : L.Ok) (hk : CoreOk P L) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (rest P) t fun t' => Ctx L g m₀ t' ∧ (∃ i, Exit P L m₀ i t') ∧ ∀ p ∈ saved, t'.gpr p.1 = g p.1 :=
  WP.seq (WP.mono (stageX_ok hL hT hc) fun _ ⟨h₀, q₀⟩ =>
    WP.seq (WP.mono (stageH_ok hL hT h₀ q₀) fun _ ⟨h₁, q₁⟩ =>
    WP.seq (WP.mono (stageB_ok hL h₁ q₁) fun _ ⟨h₂, q₂⟩ =>
      WP.seq (WP.mono (stageC_ok hL hk hT h₂ q₂) fun _ ⟨h₃, q₃⟩ =>
        WP.seq (WP.mono (stageD_ok hL hk hT h₃ q₃) fun _ ⟨h₄, q₄⟩ =>
          WP.seq (WP.mono (stageE_ok hL h₄ q₄) fun _ ⟨h₅, q₅⟩ =>
            WP.seq (WP.mono (tries_ok hL hk hT h₅ q₅) fun _ ⟨h₆, i, q₆⟩ =>
              WP.mono (stageG_ok hL hk h₆ q₆) fun _ ⟨h₇, q₇, r₇⟩ => ⟨h₇, ⟨i, q₇⟩, r₇⟩)))))))

/-! ## RFC 6979's result -/

/-- RFC 6979's number of blocks is the candidates' `V`s. -/
theorem blocks_eq (P : RfcHash) : Spec.Ecdsa.Rfc6979.blocks P.R.E.C P.F.H.D = P.nV := nV_eq P

/-- The instance's signature and number of candidates, as the proof names its parts. -/
theorem result_unfold :
    result P.I m₀ L.d L.dg =
      if 1 ≤ xOf P L m₀ ∧ xOf P L m₀ < P.R.E.C.n then
        let (K, V) := kv0 P L m₀
        Spec.Ecdsa.Rfc6979.search P.R.E.C P.ok.hH.SH.H P.F.H.D (xOf P L m₀) (eOf P L m₀) K V P.I.tries
      else (none, 0) := by
  simp only [result, Proof.Ecdsa.Rfc6979.Instance.result, P.ecdsa, P.R.curve, P.hash, P.len,
    ecdsa_bytesAt, Spec.Ecdsa.Rfc6979.sign]

/-- The signature of the candidate the loop stopped at is RFC 6979's. -/
theorem result_eq {i : Nat} {t : State} (hx : Exit P L m₀ i t) :
    (result P.I m₀ L.d L.dg).1 = sigI P L m₀ i := by
  rw [result_unfold]
  by_cases hv : 1 ≤ xOf P L m₀ ∧ xOf P L m₀ < P.R.E.C.n
  · simp only [hv, and_self, ite_true]
    rw [Proof.Ecdsa.Rfc6979.searchB_shift (blocks_eq P) i P.I.tries (by have := hx.lt; omega_using [this]) hx.fails,
      show P.I.tries - i = (P.I.tries - 1 - i) + 1 by have := hx.lt; omega_using [this]]
    cases hs : sigI P L m₀ i with
    | some rs => rw [Proof.Ecdsa.Rfc6979.searchB_ok (blocks_eq P) hs]
    | none =>
      obtain h7 : i + 1 = P.I.tries := hx.last.resolve_left (by simp [hs])
      rw [Proof.Ecdsa.Rfc6979.searchB_fail (blocks_eq P) hs, show P.I.tries - 1 - i = 0 by omega_using [h7]]
      rfl
  · symm
    simp only [hv, ite_false, sigI, Spec.Ecdsa.signWith]
    split
    · rename_i h; exact absurd ⟨h.1, h.2.1⟩ hv
    · rfl

/-! ## How many candidates -/

theorem ite_le_of_not {c : Prop} [Decidable c] {a b i : Nat} (hc : ¬c) (hb : b ≤ i) :
    (if c then a else b) ≤ i := by
  simp only [hc, ite_false]; exact hb

/-- The candidate the loop stops at, from the number RFC 6979 tries. -/
def exitAt (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : Nat :=
  if (result P.I m₀ L.d L.dg).2 = 0 then P.I.tries - 1 else (result P.I m₀ L.d L.dg).2 - 1

/-- The loop goes on after candidate `i` iff it stops at a later one. -/
theorem go_iff {i : Nat} (hi : i < P.I.tries) (hf : ∀ j < i, sigI P L m₀ j = none) :
    (sigI P L m₀ i = none ∧ i + 1 < P.I.tries) ↔ i < exitAt P L m₀ := by
  unfold exitAt
  rw [result_unfold]
  by_cases hv : 1 ≤ xOf P L m₀ ∧ xOf P L m₀ < P.R.E.C.n
  · simp only [hv, and_self, ite_true]
    rw [Proof.Ecdsa.Rfc6979.searchB_shift (blocks_eq P) i P.I.tries (by omega_using [hi]) hf,
      show P.I.tries - i = (P.I.tries - 1 - i) + 1 by omega_using [hi]]
    cases hs : sigI P L m₀ i with
    | some rs =>
      rw [Proof.Ecdsa.Rfc6979.searchB_ok (blocks_eq P) hs]
      simp
    | none =>
      rw [Proof.Ecdsa.Rfc6979.searchB_fail (blocks_eq P) hs]
      by_cases h7 : i + 1 < P.I.tries
      · have := Proof.Ecdsa.Rfc6979.searchB_pos (C := P.R.E.C) (H := P.ok.hH.SH.H) (hlen := P.F.H.D)
          (d := xOf P L m₀) (e := eOf P L m₀) (n := P.I.tries - 2 - i)
          (K := (stepB P.ok.hH.SH.H P.nV (kvI P L m₀ i).1 (kvI P L m₀ i).2).1)
          (V := (stepB P.ok.hH.SH.H P.nV (kvI P L m₀ i).1 (kvI P L m₀ i).2).2) (blocks_eq P)
        rw [show P.I.tries - 1 - i = P.I.tries - 2 - i + 1 by omega_using [h7]]
        simp only [true_and, h7]
        simp only [kvI] at this
        rw [true_iff]
        split <;> omega_arith
      · rw [show P.I.tries - 1 - i = 0 by omega_using [h7]]
        simp only [Spec.Ecdsa.Rfc6979.search, h7, and_false, false_iff, Nat.not_lt]
        exact ite_le_of_not (by omega_using []) (by omega_using [])
  · simp only [hv, ite_false, ite_true]
    obtain hs : sigI P L m₀ i = none := by
      simp only [sigI, Spec.Ecdsa.signWith]
      split
      · rename_i h; exact absurd ⟨h.1, h.2.1⟩ hv
      · rfl
    simp only [hs, true_and]
    omega_using []

/-! ## The whole function -/

theorem released_gpr {s₂ : State} {r : Reg} (hr : r ≠ .esp) : (released s₂).gpr r = s₂.gpr r :=
  (Wp.Upd.setReg s₂ .esp _).other r hr

theorem released_esp (s₂ : State) : (released s₂).gpr .esp = s₂.gpr .esp + BitVec.ofNat 32 512 :=
  (Wp.Upd.setReg s₂ .esp _).gpr

/-- The contract the code for `P`'s hash function is proven against, with
`P`'s table and the functions `ns`' addresses public. -/
abbrev rfcP (P : RfcHash) (ns : List String) : Contract isa :=
  rfcX86 P.R.E.combConsts P.I 612 (tabFacts P.F P.f) ns

/-- The layout of a call from `s`. -/
abbrev layOf (P : RfcHash) (s : State) : Lay P.I.hashLen :=
  lay P.I.hashLen P.I.ecdsa.curve.len P.R.E.combConsts P.F P.f s

theorem coreOk_lay (P : RfcHash) (s : State) : CoreOk P (layOf P s) := ⟨P.curveLen, rfl⟩

theorem tabL_lay (P : RfcHash) (s : State) : TabL P (layOf P s) := ⟨rfl, rfl⟩

/-- `vg_ecdsa_<curve>_sign` for `P`'s hash function, whose body writes no
`esp`, meets `rfcP P` and keeps the callee-saved registers and its return
address. -/
theorem sign_ok {ns : List String} (hsp : NoSp (cfgOf P).body) {s : State} (h : (rfcP P ns).pre s) :
    WP isa (cfgOf P).sign s fun s' => abiPreserved s s' ∧ (rfcP P ns).post s s' := by
  obtain hL := lay_ok h
  have nB := hL.nB
  refine WP.alloc (by have := h.1; omega_arith) hsp ?_
  rw [body_eq]
  refine WP.seq (WP.mono (entry_ok h) fun t₁ h₁ => WP.seq (WP.mono h₁.2.2 fun t hc =>
    WP.mono (rest_ok hL (coreOk_lay P s) (tabL_lay P s) hc) fun u ⟨hu, ⟨i, hx⟩, hs⟩ m v fl => ?_))
  -- The frame is the layout's `FR`, apart from the return address and the output.
  obtain hFR : below (s.gpr .esp) 512 = (layOf P s).FR := by
    have := entered_wr h
    simp only [entered, allocState_wr] at this
    exact (List.cons.inj this).1
  obtain hFS : Region.Sub (layOf P s).FR (layOf P s).STK := Lay.sub_STK (by decide)
  rw [hFR] at fl
  obtain hdO : ∀ r ∈ [(layOf P s).FR], Region.Disjoint ⟨(arg s 0).setWidth 64, 2 * P.Q⟩ r := by
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    have e : (layOf P s).q = P.Q := (coreOk_lay P s).1
    have := hL.ko.symm.sub_right hFS
    dsimp only [Lay.OUT] at this
    rw [e] at this
    exact this
  obtain hnO : 2 * P.Q ≤ 2 ^ 64 := by
    have hQe : P.Q = P.R.E.C.len := rfl
    have := P.R.len_words; have := P.R.n9; omega_arith
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · show (released u).gpr r = s.gpr r
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [released_gpr (by decide)]; exact hs (.ebx, 128) (by decide)
    · rw [released_gpr (by decide)]; exact hs (.esi, 132) (by decide)
    · rw [released_gpr (by decide)]; exact hs (.edi, 136) (by decide)
    · rw [released_gpr (by decide)]; exact hs (.ebp, 140) (by decide)
    · rw [released_esp, hu.esp]; exact BitVec.sub_add_cancel _ _
  · have hret : (s.gpr .esp).setWidth 64 = (layOf P s).B + BitVec.ofNat 64 588 := by
      rw [hL.B_eq, BitVec.sub_add_cancel]; rfl
    show m.readW _ 32 = _
    rw [hret, fl.readW (r := (layOf P s).RET) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (Lay.disj24 _ (by omega_arith) (by omega_arith)).symm.sub_right hFS) (by decide)]
    refine hu.frame.readW (r := (layOf P s).RET) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.ro
    · exact hL.rc
    · exact (Lay.disj24 _ (by omega_arith) (by omega_arith)).symm
  · show match (result P.I s.mem (layOf P s).d (layOf P s).dg).1 with
      | some rs => _ | none => _
    rw [result_eq hx]
    obtain e₁ : 2 * P.I.ecdsa.curve.len = 2 * P.Q := by rw [P.curveLen]
    obtain e₂ : P.I.ecdsa.curve = P.R.E.C := by rw [P.ecdsa, P.R.curve]
    rw [e₁]
    have hr := hx.res
    obtain ha : (released u).gpr .eax = u.gpr .eax := released_gpr (by decide)
    revert hr
    cases sigI P (layOf P s) s.mem i with
    | some rs => exact fun ⟨h₁, h₂⟩ => ⟨by rw [BitVec.setWidth_append_eq_right, ha]; exact h₁,
        by rw [e₂]; exact (bytesAt_frame fl hdO hnO).trans h₂⟩
    | none => exact fun ⟨h₁, h₂⟩ => ⟨by rw [BitVec.setWidth_append_eq_right, ha]; exact h₁,
        (bytesAt_frame fl hdO hnO).trans h₂⟩

end VG.Proof.Ecdsa.Rfc6979.X86
