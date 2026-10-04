import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Hmac
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Pbkdf2.Whole.Common
import VerifiedGarbage.Proof.Weierstrass.Words32

/-!
# Deterministic ECDSA on x86 (32-bit): `h = bits2octets(digest)`

The digest, big-endian in eight 32-bit words (`Xw`), less `n` if that does
not borrow: the words go to `h`'s place, and those of the difference
(`Dw`, with the borrows `cb`) to `K`'s (`subWord_ok`); a mask of the last
borrow selects, word by word, the digest's word or the difference's, stored
big-endian into `h` (`selWord_ok`). As the digest is below `2^256 < 2n`,
this is the digest modulo `n` (`mod_math`, `reduce_ok`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Ecdsa.Rfc6979.X86
open VG.Proof.Mont.X86 (wp_movS wp_subS wp_sbbS wp_storeS)
open VG.Impl.Pbkdf2.Stream.X86 (at_)

/-! ## The arithmetic -/

/-- The words of `n`, least significant first. -/
def nW (j : Nat) : BitVec 32 := BitVec.ofNat 32 (Spec.P256.n >>> (32 * j))

/-- The words `j < k` of a number, least significant first. -/
def wsum (f : Nat → BitVec 32) : Nat → Nat
  | 0 => 0
  | k + 1 => (f k).toNat * 2 ^ (32 * k) + wsum f k

theorem wsum_lt (f : Nat → BitVec 32) : ∀ k, wsum f k < 2 ^ (32 * k)
  | 0 => by simp [wsum]
  | k + 1 => by
    have := wsum_lt f k
    have := (f k).isLt
    simp only [wsum]
    rw [show 32 * (k + 1) = 32 + 32 * k by omega, Nat.pow_add]
    have h1 : (f k).toNat * 2 ^ (32 * k) ≤ (2 ^ 32 - 1) * 2 ^ (32 * k) := Nat.mul_le_mul_right _ (by omega)
    have h2 : (2 ^ 32 - 1) * 2 ^ (32 * k) + 2 ^ (32 * k) = 2 ^ 32 * 2 ^ (32 * k) := by
      rw [Nat.sub_mul, Nat.one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left _ (by decide))]
    omega

theorem nW_sum : wsum nW 8 = Spec.P256.n := by
  simp only [wsum, nW]
  decide +kernel

theorem n_ge : 2 ^ 255 ≤ Spec.P256.n := by decide +kernel

/-- `sbb`'s borrow. -/
theorem sbb32 (a b : BitVec 32) (c : Bool) :
    (a - b - (BitVec.ofBool c).setWidth 32).toNat + b.toNat + c.toNat =
      a.toNat + 2 ^ 32 * (decide (a.toNat < b.toNat + c.toNat)).toNat := by
  have := a.isLt; have := b.isLt; have := Bool.toNat_le c
  have hc : ((BitVec.ofBool c).setWidth 32).toNat = c.toNat := by cases c <;> rfl
  rw [BitVec.toNat_sub, BitVec.toNat_sub, hc]
  by_cases h : a.toNat < b.toNat + c.toNat <;>
    simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega

/-- The digest's words, at `dg`, least significant first. -/
abbrev Xw (m : Mem) (dg : Addr) (j : Nat) : BitVec 32 := bswap (m.readW (dg + BitVec.ofNat 64 (28 - 4 * j)) 32)

/-- The borrows of the digest less `n`. -/
def cb (m : Mem) (dg : Addr) : Nat → Bool
  | 0 => false
  | j + 1 => decide ((Xw m dg j).toNat < (nW j).toNat + (cb m dg j).toNat)

/-- The words of the digest less `n`. -/
abbrev Dw (m : Mem) (dg : Addr) (j : Nat) : BitVec 32 := Xw m dg j - nW j - (BitVec.ofBool (cb m dg j)).setWidth 32

theorem chain (m : Mem) (dg : Addr) : ∀ k,
    wsum (Dw m dg) k + wsum nW k = wsum (Xw m dg) k + 2 ^ (32 * k) * (cb m dg k).toNat
  | 0 => by simp [wsum, cb]
  | k + 1 => by
    have ih := chain m dg k
    have e := sbb32 (Xw m dg k) (nW k) (cb m dg k)
    simp only [wsum, cb]
    rw [show 32 * (k + 1) = 32 + 32 * k by omega, Nat.pow_add]
    generalize 2 ^ (32 * k) = P at *
    generalize (decide ((Xw m dg k).toNat < (nW k).toNat + (cb m dg k).toNat)).toNat = c' at *
    generalize (cb m dg k).toNat = c at *
    generalize (Xw m dg k - nW k - (BitVec.ofBool (cb m dg k)).setWidth 32).toNat = D at *
    generalize (Xw m dg k).toNat = X at *
    generalize (nW k).toNat = N at *
    grind

theorem sel_mask32 (x d : BitVec 32) (c : Bool) :
    ((x ^^^ d) &&& (if c then BitVec.allOnes 32 else 0)) ^^^ d = if c then x else d := by
  cases c
  · simp
  · simp only [ite_true, BitVec.and_allOnes, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem wsum_sel (f g : Nat → BitVec 32) (c : Bool) :
    ∀ k, wsum (fun i => if c then f i else g i) k = if c then wsum f k else wsum g k := by
  intro k; cases c <;> simp

/-- The words of `4 k` bytes, each the byte reversal of a word, big-endian. -/
theorem ofBytes_words (m : Mem) (f : Nat → BitVec 32) : ∀ (p : Addr) (k : Nat),
    (∀ j < k, byteRev32 (m.readW (p + BitVec.ofNat 64 (4 * (k - 1 - j))) 32) = f j) →
    Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt m p (4 * k)) = wsum f k
  | _, 0, _ => rfl
  | p, k + 1, h => by
    have h0 := h k (by omega)
    simp only [Nat.add_sub_cancel, Nat.sub_self, Nat.mul_zero, BitVec.add_zero] at h0
    rw [show 4 * (k + 1) = 4 + 4 * k by omega, Proof.Weierstrass.bytesAt_add,
      Proof.Weierstrass.ofBytes_append, Proof.Weierstrass.length_bytesAt,
      ofBytes_words m f (p + BitVec.ofNat 64 4) k fun j hj => by
        rw [Offset.add_add, show 4 + 4 * (k - 1 - j) = 4 * (k + 1 - 1 - j) by omega]; exact h j (by omega),
      ← Proof.Weierstrass.byteRev32_ofBytes, h0, wsum, show (256 : Nat) ^ (4 * k) = 2 ^ (32 * k) by
        rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]; congr 1; omega]

/-! ## The code -/

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

theorem nWord_cfgOf (P : RfcHash) (j : Nat) : (cfgOf P).nWord j = nW j := rfl

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
  · simp only [show j ≠ 0 by omega, ite_false]
    exact wp_sbbS rfl (hc hj) k

end

theorem Lay.Ok.dgv (hL : L.Ok) (hn : 32 ≤ dn) {o : Nat} (ho : o + 4 ≤ 32) :
    addr L.a2 o = L.dg + BitVec.ofNat 64 o :=
  addr_eq (by have := hL.ng; omega)

/-- After `j` words of the subtraction, from `t`. -/
structure SubInv (L : Lay dn) (g : Reg → BitVec 32) (m₀ : Mem) (t : State) (j : Nat) (u : State) : Prop where
  ctx : Ctx L g m₀ u
  esi : u.gpr .esi = L.a2
  frame : Frame [⟨L.B + BitVec.ofNat 64 76, 160⟩] t.mem u.mem
  x : ∀ i < j, u.mem.readW (L.B + BitVec.ofNat 64 (232 - 4 * i)) 32 = Xw t.mem L.dg i
  d : ∀ i < j, u.mem.readW (L.B + BitVec.ofNat 64 (104 - 4 * i)) 32 = Dw t.mem L.dg i
  cf : 0 < j → u.cf = some (cb t.mem L.dg j)

theorem fr_sep (B : Addr) {x y : Nat} (h : x + 4 ≤ y ∨ y + 4 ≤ x) (hx : x + 4 ≤ 276) (hy : y + 4 ≤ 276) :
    Mem.Sep (B + BitVec.ofNat 64 x) (32 / 8) (B + BitVec.ofNat 64 y) (32 / 8) :=
  Offset.sep B h (by omega) (by omega)

theorem subWord_ok (hL : L.Ok) (hn : 32 ≤ dn) {t u : State} {j : Nat} (hj : j < 8) (h : SubInv L g m₀ t j u) :
    WP isa (.block ((cfgOf P).subWord j)) u (SubInv L g m₀ t (j + 1)) := by
  have nB := hL.nB
  have hc := h.ctx
  have hdg : u.mem.readW (L.dg + BitVec.ofNat 64 (28 - 4 * j)) 32 = t.mem.readW (L.dg + BitVec.ofNat 64 (28 - 4 * j)) 32 :=
    h.frame.readW (r := L.DG) (Offset.contains_base _ (by omega) (by omega)) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hL.kg.symm.sub_right (Offset.sub_base _ (by omega))) (by decide)
  have a1 : addr L.F (fH + 28 - 4 * j) = L.B + BitVec.ofNat 64 (232 - 4 * j) := by
    rw [hL.addrF (by simp only [fH]; omega)]; congr 2; simp only [fH]; omega
  have a2 : addr L.F (fK + 28 - 4 * j) = L.B + BitVec.ofNat 64 (104 - 4 * j) := by
    rw [hL.addrF (by simp only [fK]; omega)]; congr 2; simp only [fK]; omega
  simp only [Cfg.subWord, stk, nWord_cfgOf]
  refine wp_movS (v := u.mem.readW (L.dg + BitVec.ofNat 64 (28 - 4 * j)) 32)
    (by rw [show at_ .esi (28 - 4 * j) = ⟨.esi, 28 - 4 * j⟩ from rfl, readSrc_mem h.esi
        (by rw [hL.dgv hn (by omega)]; exact hc.inDg (by omega) (by omega)), hL.dgv hn (by omega)])
    fun u₁ v₁ c₁ => wp_bswapC fun u₂ v₂ c₂ => ?_
  rw [v₁.gpr, hdg] at v₂
  have esp₂ : u₂.gpr .esp = L.F := by rw [v₂.other _ (by decide), v₁.other _ (by decide), hc.esp]
  refine wp_stm esp₂ (by rw [a1, v₂.wr, v₁.wr]; exact hc.inFrW (by omega) (by omega) hL) fun u₃ v₃ => ?_
  refine wp_subsbb (j := j) (c := cb t.mem L.dg j) (fun e => by subst e; rfl)
    (fun hj => by rw [v₃.cf, c₂, c₁]; exact h.cf hj) fun u₄ v₄ c₄ => ?_
  rw [v₃.gpr, v₂.gpr] at v₄
  refine wp_stm (B := L.F) (by rw [v₄.other _ (by decide), v₃.gpr, esp₂])
    (by rw [a2, v₄.wr, v₃.wr, v₂.wr, v₁.wr]; exact hc.inFrW (by omega) (by omega) hL) fun u₅ v₅ => WP.block_nil ?_
  rw [a1] at v₃; rw [a2] at v₅
  have hm₅ : u₅.mem = (u.mem.writeW (L.B + BitVec.ofNat 64 (232 - 4 * j)) (Xw t.mem L.dg j)).writeW
      (L.B + BitVec.ofNat 64 (104 - 4 * j)) (Dw t.mem L.dg j) := by
    rw [v₅.mem, v₄.gpr, v₄.mem, v₃.mem, v₂.gpr, v₂.mem, v₁.mem]
  have hf : Frame [⟨L.B + BitVec.ofNat 64 76, 160⟩] u.mem u₅.mem := by
    rw [hm₅]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (by omega) (by omega) (by omega))).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (by omega) (by omega) (by omega))
  refine ⟨hc.keep hL (by rw [v₅.rd, v₄.rd, v₃.rd, v₂.rd, v₁.rd]) (by rw [v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr])
      (by rw [v₅.gpr, v₄.other _ (by decide), v₃.gpr, esp₂, hc.esp]) hf
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by omega)),
    by rw [v₅.gpr, v₄.other _ (by decide), v₃.gpr, v₂.other _ (by decide), v₁.other _ (by decide), h.esi],
    h.frame.trans hf, fun i hi => ?_, fun i hi => ?_, fun _ => by rw [v₅.cf, c₄, v₃.gpr, v₂.gpr]; rfl⟩
  · rw [hm₅, Mem.readW_writeW_sep (fr_sep _ (by omega) (by omega) (by omega)) (by decide)]
    rcases Nat.lt_or_ge i j with hij | hij
    · rw [Mem.readW_writeW_sep (fr_sep _ (by omega) (by omega) (by omega)) (by decide)]; exact h.x i hij
    · rw [show i = j by omega, Mem.readW_writeW_self32]
  · rw [hm₅]
    rcases Nat.lt_or_ge i j with hij | hij
    · rw [Mem.readW_writeW_sep (fr_sep _ (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_sep (fr_sep _ (by omega) (by omega) (by omega)) (by decide)]; exact h.d i hij
    · rw [show i = j by omega, Mem.readW_writeW_self32]

/-- The words before `k`. -/
theorem subs_ok (hL : L.Ok) (hn : 32 ≤ dn) {t : State} : ∀ k ≤ 8, ∀ u, SubInv L g m₀ t 0 u →
    WP isa (.block ((List.range k).flatMap (cfgOf P).subWord)) u (SubInv L g m₀ t k)
  | 0, _, u, h => WP.block_nil h
  | k + 1, hk, u, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    exact WP.mono (subs_ok hL hn k (by omega) u h) fun u' h' => subWord_ok hL hn (by omega) h'

/-- After the mask and `j` words of the selection, from `t`. -/
structure SelInv (L : Lay dn) (g : Reg → BitVec 32) (m₀ : Mem) (t : State) (j : Nat) (u : State) : Prop where
  ctx : Ctx L g m₀ u
  edx : u.gpr .edx = if cb t.mem L.dg 8 then BitVec.allOnes 32 else 0
  frame : Frame [⟨L.B + BitVec.ofNat 64 76, 160⟩] t.mem u.mem
  h : ∀ i < j, u.mem.readW (L.B + BitVec.ofNat 64 (232 - 4 * i)) 32 =
    bswap (if cb t.mem L.dg 8 then Xw t.mem L.dg i else Dw t.mem L.dg i)
  x : ∀ i, j ≤ i → i < 8 → u.mem.readW (L.B + BitVec.ofNat 64 (232 - 4 * i)) 32 = Xw t.mem L.dg i
  d : ∀ i < 8, u.mem.readW (L.B + BitVec.ofNat 64 (104 - 4 * i)) 32 = Dw t.mem L.dg i

theorem selWord_ok (hL : L.Ok) {t u : State} {j : Nat} (hj : j < 8) (h : SelInv L g m₀ t j u) :
    WP isa (.block (Cfg.selWord j)) u (SelInv L g m₀ t (j + 1)) := by
  have nB := hL.nB
  have hc := h.ctx
  have a1 : addr L.F (fH + 28 - 4 * j) = L.B + BitVec.ofNat 64 (232 - 4 * j) := by
    rw [hL.addrF (by simp only [fH]; omega)]; congr 2; simp only [fH]; omega
  have a2 : addr L.F (fK + 28 - 4 * j) = L.B + BitVec.ofNat 64 (104 - 4 * j) := by
    rw [hL.addrF (by simp only [fK]; omega)]; congr 2; simp only [fK]; omega
  simp only [Cfg.selWord, stk]
  refine wp_ldm hc.esp (by rw [a1]; exact hc.inFr (by omega) (by omega) hL) fun u₁ v₁ => ?_
  refine wp_ldm (B := L.F) (by rw [v₁.other _ (by decide), hc.esp])
    (by rw [a2, v₁.rd, v₁.wr]; exact hc.inFr (by omega) (by omega) hL) fun u₂ v₂ => ?_
  refine wp_xor fun u₃ v₃ => wp_and fun u₄ v₄ => wp_xor fun u₅ v₅ => wp_bswap fun u₆ v₆ => ?_
  have esp₆ : u₆.gpr .esp = L.F := by
    rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.other _ (by decide), hc.esp]
  refine wp_stm esp₆ (by rw [a1, v₆.wr, v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr]; exact hc.inFrW (by omega) (by omega) hL)
    fun u₇ v₇ => WP.block_nil ?_
  rw [a1] at v₁ v₇; rw [a2] at v₂
  have val : u₆.gpr .eax = bswap (if cb t.mem L.dg 8 then Xw t.mem L.dg j else Dw t.mem L.dg j) := by
    rw [v₆.gpr, v₅.gpr, v₄.gpr, v₄.other .ecx (by decide), v₃.gpr, v₃.other .ecx (by decide),
      v₃.other .edx (by decide), v₂.gpr, v₂.other .eax (by decide), v₂.other .edx (by decide), v₁.gpr,
      v₁.other .edx (by decide), v₁.mem, h.x j (by omega) hj, h.d j hj, h.edx, sel_mask32]
  have hm₇ : u₇.mem = u.mem.writeW (L.B + BitVec.ofNat 64 (232 - 4 * j))
      (bswap (if cb t.mem L.dg 8 then Xw t.mem L.dg j else Dw t.mem L.dg j)) := by
    rw [v₇.mem, val, v₆.mem, v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem]
  have hf : Frame [⟨L.B + BitVec.ofNat 64 76, 160⟩] u.mem u₇.mem := by
    rw [hm₇]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))
  refine ⟨hc.keep hL (by rw [v₇.rd, v₆.rd, v₅.rd, v₄.rd, v₃.rd, v₂.rd, v₁.rd])
      (by rw [v₇.wr, v₆.wr, v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr]) (by rw [v₇.gpr, esp₆, hc.esp]) hf
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by omega)),
    by rw [v₇.gpr, v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.other _ (by decide), h.edx],
    h.frame.trans hf, fun i hi => ?_, fun i hi hi' => ?_, fun i hi => ?_⟩
  · rw [hm₇]
    rcases Nat.lt_or_ge i j with hij | hij
    · rw [Mem.readW_writeW_sep (fr_sep _ (by omega) (by omega) (by omega)) (by decide)]; exact h.h i hij
    · rw [show i = j by omega, Mem.readW_writeW_self32]
  · rw [hm₇, Mem.readW_writeW_sep (fr_sep _ (by omega) (by omega) (by omega)) (by decide)]
    exact h.x i (by omega) hi'
  · rw [hm₇, Mem.readW_writeW_sep (fr_sep _ (by omega) (by omega) (by omega)) (by decide)]
    exact h.d i hi

/-- The words before `k`. -/
theorem sels_ok (hL : L.Ok) {t : State} : ∀ k ≤ 8, ∀ u, SelInv L g m₀ t 0 u →
    WP isa (.block ((List.range k).flatMap Cfg.selWord)) u (SelInv L g m₀ t k)
  | 0, _, u, h => WP.block_nil h
  | k + 1, hk, u, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    exact WP.mono (sels_ok hL k (by omega) u h) fun u' h' => selWord_ok hL (by omega) h'

theorem dg_ofBytes (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (hn : 32 ≤ dn) :
    Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.dg 32) =
      Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem L.dg 32) := by
  congr 1
  simp only [Spec.Sha256.bytesAt]
  exact List.map_congr_left fun i hi => (hc.dg_byte hL (by have := List.mem_range.mp hi; omega)).symm

/-- `h`: the digest (at `esi`) modulo `n`, big-endian in the frame. -/
theorem reduce_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (hsi : t.gpr .esi = L.a2) (hn : 32 ≤ dn) :
    WP isa (.block (cfgOf P).reduce) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 76, 160⟩] t.mem t'.mem ∧
      Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 204) 32) =
        Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.dg 32) % Spec.P256.n := by
  rw [Cfg.reduce, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (subs_ok (P := P) hL hn 8 (Nat.le_refl _) t
    ⟨hc, hsi, Frame.refl _ _, fun i hi => absurd hi (Nat.not_lt_zero _), fun i hi => absurd hi (Nat.not_lt_zero _),
      fun h => absurd h (Nat.lt_irrefl _)⟩) fun u hu => ?_
  refine wp_sbb_self (hu.cf (by omega)) fun u₁ v₁ => WP.block_nil ?_
  have hc₁ : Ctx L g m₀ u₁ := hu.ctx.regs hL v₁.rd v₁.wr v₁.mem (v₁.other _ (by decide))
  refine WP.mono (sels_ok hL 8 (Nat.le_refl _) u₁
    ⟨hc₁, v₁.gpr, by rw [v₁.mem]; exact hu.frame, fun i hi => absurd hi (Nat.not_lt_zero _),
      fun i _ hi => by rw [v₁.mem]; exact hu.x i hi, fun i hi => by rw [v₁.mem]; exact hu.d i hi⟩)
    fun t' h' => ⟨h'.ctx, h'.frame, ?_⟩
  -- The value.
  have hX := ofBytes_words t.mem (Xw t.mem L.dg) L.dg 8 fun j hj => by
    show byteRev32 _ = bswap _
    rw [show 4 * (8 - 1 - j) = 28 - 4 * j by omega]; rfl
  have hH := ofBytes_words t'.mem (fun i => if cb t.mem L.dg 8 then Xw t.mem L.dg i else Dw t.mem L.dg i)
    (L.B + BitVec.ofNat 64 204) 8 fun j hj => by
      rw [Offset.add_add, show 204 + 4 * (8 - 1 - j) = 232 - 4 * j by omega, h'.h j hj]
      exact Proof.Pbkdf2.Whole.byteRev32_byteRev32 _
  have hch := chain t.mem L.dg 8
  rw [nW_sum] at hch
  rw [dg_ofBytes hL hc hn]
  change Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt _ _ (4 * 8)) =
    Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt _ _ (4 * 8)) % _
  rw [hH, hX, wsum_sel]
  exact mod_math _ _ _ _ hch (by have := wsum_lt (Dw t.mem L.dg) 8; omega)
    (by have := wsum_lt (Xw t.mem L.dg) 8; omega) n_ge

end VG.Proof.Ecdsa.Rfc6979.X86
