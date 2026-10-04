import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Hmac
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Words32
import VerifiedGarbage.Proof.Pbkdf2.Whole.Common

/-!
# Deterministic ECDSA on 32-bit ARM: `h = bits2octets(digest)`

The digest, big-endian in eight 32-bit words (`Xw`), less `n`, computed as
the digest plus the complement of `n` plus 1, by 16-bit digits (the model's
`adc` sets no flags; `digits_ok`): the digest's words go to `h`'s place, and
those of the sum (`Dw`, with the carries `cc`) to `K`'s (`subWord_ok`).
The last carry is 1 exactly when the subtraction does not borrow; its
negation is a mask that selects, word by word, the difference's word or the
digest's, stored big-endian into `h` (`selWord_ok`). As the digest is below
`2^256 < 2n`, this is the digest modulo `n` (`mod_math`, `reduce_ok`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_ldr wp_str wp_dp wp_mov wp_movw op2_reg op2_imm op2_lsr op2_lsl
  dpVal toNat_add_lt toNat_sub_le toNat_shr toNat_shl toNat_and_mask16 mask16)

/-! ## The arithmetic -/

/-- One word of `x + (2³² - 1 - n) + c`. -/
abbrev wsub (x n : BitVec 32) (c : Nat) : Nat := x.toNat + (2 ^ 32 - 1 - n.toNat) + c

/-- The digest's words, at `dg`, least significant first. -/
abbrev Xw (m : Mem) (dg : Addr) (j : Nat) : BitVec 32 := rev (m.readW (dg + BitVec.ofNat 64 (28 - 4 * j)) 32)

/-- The carries of the digest plus the complement of `n` plus 1. -/
def cc (m : Mem) (dg : Addr) : Nat → Nat
  | 0 => 1
  | j + 1 => wsub (Xw m dg j) (nW j) (cc m dg j) / 2 ^ 32

/-- The words of the digest plus the complement of `n` plus 1. -/
abbrev Dw (m : Mem) (dg : Addr) (j : Nat) : BitVec 32 := BitVec.ofNat 32 (wsub (Xw m dg j) (nW j) (cc m dg j))

theorem cc_le (m : Mem) (dg : Addr) : ∀ j, cc m dg j ≤ 1
  | 0 => Nat.le_refl _
  | j + 1 => by
    have := cc_le m dg j; have := (Xw m dg j).isLt; have := (nW j).isLt
    simp only [cc, wsub]; omega

theorem chain (m : Mem) (dg : Addr) : ∀ k,
    wsum (Dw m dg) k + 2 ^ (32 * k) * cc m dg k + wsum nW k = wsum (Xw m dg) k + 2 ^ (32 * k)
  | 0 => by simp [wsum, cc]
  | k + 1 => by
    have ih := chain m dg k
    have hc := cc_le m dg k
    have hN := (nW k).isLt
    have hw : (Dw m dg k).toNat + 2 ^ 32 * cc m dg (k + 1) = wsub (Xw m dg k) (nW k) (cc m dg k) := by
      simp only [cc, BitVec.toNat_ofNat]; omega
    simp only [wsub] at hw
    simp only [wsum]
    rw [show 32 * (k + 1) = 32 + 32 * k by omega, Nat.pow_add]
    generalize 2 ^ (32 * k) = P at *
    generalize cc m dg (k + 1) = c' at *
    generalize cc m dg k = c at *
    generalize (Dw m dg k).toNat = D at *
    generalize (Xw m dg k).toNat = X at *
    generalize (nW k).toNat = N at *
    have e : 2 ^ 32 - 1 - N + N = 2 ^ 32 - 1 := by omega
    generalize 2 ^ 32 - 1 - N = M at *
    grind

/-- `x - n + 2²⁵⁶` or `x`, by the last carry `c`: `x mod n`. -/
theorem select_math {x d c : Nat} (hc : c ≤ 1) (hd : d < 2 ^ 256) (hx : x < 2 ^ 256)
    (hch : d + 2 ^ 256 * c + Spec.P256.n = x + 2 ^ 256) :
    (if c = 1 then d else x) = x % Spec.P256.n := by
  rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl
  · have := mod_math x Spec.P256.n d true (by simp only [Bool.toNat_true, Nat.mul_one]; omega) hd hx n_ge
    simp only [Nat.zero_ne_one, ↓reduceIte] at this ⊢
    exact this
  · have := mod_math x Spec.P256.n d false (by simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero]; omega)
      hd hx n_ge
    simp only [Bool.false_eq_true, ↓reduceIte] at this ⊢
    exact this

theorem wsum_ite (p : Prop) [Decidable p] (f g : Nat → BitVec 32) (k : Nat) :
    wsum (fun i => if p then f i else g i) k = if p then wsum f k else wsum g k := by
  by_cases h : p <;> simp only [h, ↓reduceIte]

/-- The difference's words or the digest's, by the last carry: the digest modulo `n`. -/
theorem reduce_math (m : Mem) (dg : Addr) :
    wsum (fun i => if cc m dg 8 = 1 then Dw m dg i else Xw m dg i) 8 = wsum (Xw m dg) 8 % Spec.P256.n := by
  have hch := chain m dg 8
  rw [nW_sum] at hch
  rw [wsum_ite]
  exact select_math (x := wsum (Xw m dg) 8) (d := wsum (Dw m dg) 8) (cc_le m dg 8) (wsum_lt _ 8) (wsum_lt _ 8) hch

/-! ## The code -/

/-- Two digits packed into a word. -/
theorem pack_toNat (x y : BitVec 32) (hx : x.toNat < 2 ^ 16) :
    (x ||| y <<< 16).toNat = x.toNat + y.toNat % 2 ^ 16 * 2 ^ 16 := by
  rw [BitVec.toNat_or, toNat_shl]
  have e : y.toNat * 2 ^ 16 % 2 ^ 32 = (y.toNat % 2 ^ 16) <<< 16 := by rw [Nat.shiftLeft_eq]; omega
  rw [e, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hx, Nat.shiftLeft_eq]
  omega

theorem toNat_m16 : mask16.toNat = 2 ^ 16 - 1 := rfl

/-- A word of `x + (2³² - 1 - n) + c`, by 16-bit digits, in `r2`, and its
carry in `r7`, from `x` in `r0`, `n` in `r1` and `c` in `r7`, with `r10 = 0xffff`. -/
theorem digits_ok {s : State} (h10 : s.gpr .r10 = mask16) (hc : (s.gpr .r7).toNat ≤ 1)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ u, (u.gpr .r2).toNat + 2 ^ 32 * (u.gpr .r7).toNat = wsub (s.gpr .r0) (s.gpr .r1) (s.gpr .r7).toNat →
      (u.gpr .r7).toNat ≤ 1 → u.mem = s.mem → Rest [.r2, .r3, .r7, .r12] s u → WP isa (.block is) u Q) :
    WP isa (.block (Cfg.subDigit 0 ++ (Cfg.subDigit 1 ++ (.dp .orr .r2 .r2 (.reg .r3) :: is)))) s Q := by
  simp only [Cfg.subDigit, ↓reduceIte, show (1 : Nat) ≠ 0 by decide, List.cons_append, List.nil_append]
  refine wp_dp (op2_reg _ _) fun s₁ u₁ => wp_dp (op2_reg _ _) fun s₂ u₂ => wp_dp (op2_reg _ _) fun s₃ u₃ => ?_
  refine wp_dp (op2_reg _ _) fun s₄ u₄ => wp_dp (op2_reg _ _) fun s₅ u₅ => ?_
  refine wp_mov (op2_lsr (by decide)) fun s₆ u₆ => wp_dp (op2_reg _ _) fun s₇ u₇ => ?_
  refine wp_mov (op2_lsr (by decide)) fun s₈ u₈ => wp_mov (op2_lsr (by decide)) fun s₉ u₉ => ?_
  refine wp_dp (op2_reg _ _) fun s₁₀ u₁₀ => wp_dp (op2_reg _ _) fun s₁₁ u₁₁ => wp_dp (op2_reg _ _) fun s₁₂ u₁₂ => ?_
  refine wp_mov (op2_lsr (by decide)) fun s₁₃ u₁₃ => wp_mov (op2_lsl (by decide)) fun s₁₄ u₁₄ => ?_
  refine wp_dp (op2_reg _ _) fun s₁₅ u₁₅ => ?_
  have K : Rest [.r2, .r3, .r7, .r12] s s₁₅ :=
    (u₁.rest (by simp)).trans <| (u₂.rest (by simp)).trans <| (u₃.rest (by simp)).trans <|
    (u₄.rest (by simp)).trans <| (u₅.rest (by simp)).trans <| (u₆.rest (by simp)).trans <|
    (u₇.rest (by simp)).trans <| (u₈.rest (by simp)).trans <| (u₉.rest (by simp)).trans <|
    (u₁₀.rest (by simp)).trans <| (u₁₁.rest (by simp)).trans <| (u₁₂.rest (by simp)).trans <|
    (u₁₃.rest (by simp)).trans <| (u₁₄.rest (by simp)).trans (u₁₅.rest (by simp))
  -- The registers read, as on entry.
  have x₁ : (s₁.gpr .r2).toNat = (s.gpr .r0).toNat % 2 ^ 16 := by
    rw [u₁.gpr, dpVal, h10, toNat_and_mask16]
  have n₂ : (s₂.gpr .r3).toNat = (s.gpr .r1).toNat % 2 ^ 16 := by
    rw [u₂.gpr, dpVal, u₁.other _ (by decide), u₁.other _ (by decide), h10, toNat_and_mask16]
  have r10₂ : s₂.gpr .r10 = mask16 := by rw [u₂.other _ (by decide), u₁.other _ (by decide), h10]
  have a₃ : (s₃.gpr .r2).toNat = (s.gpr .r0).toNat % 2 ^ 16 + (2 ^ 16 - 1) := by
    rw [u₃.gpr, dpVal, toNat_add_lt (by rw [u₂.other _ (by decide), x₁, r10₂, toNat_m16]; omega),
      u₂.other _ (by decide), x₁, r10₂, toNat_m16]
  have a₄ : (s₄.gpr .r2).toNat = (s.gpr .r0).toNat % 2 ^ 16 + (2 ^ 16 - 1) - (s.gpr .r1).toNat % 2 ^ 16 := by
    rw [u₄.gpr, dpVal, toNat_sub_le (by rw [a₃, u₃.other _ (by decide), n₂]; omega), a₃,
      u₃.other _ (by decide), n₂]
  have c₄ : s₄.gpr .r7 = s.gpr .r7 := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have lo : (s₅.gpr .r2).toNat = (s.gpr .r0).toNat % 2 ^ 16 + (2 ^ 16 - 1) - (s.gpr .r1).toNat % 2 ^ 16 +
      (s.gpr .r7).toNat := by
    rw [u₅.gpr, dpVal, toNat_add_lt (by rw [a₄, c₄]; omega), a₄, c₄]
  have c₆ : (s₆.gpr .r7).toNat = (s₅.gpr .r2).toNat / 2 ^ 16 := by
    rw [u₆.gpr, toNat_shr]
  have r10₆ : s₆.gpr .r10 = mask16 := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), r10₂]
  have l₇ : (s₇.gpr .r2).toNat = (s₅.gpr .r2).toNat % 2 ^ 16 := by
    rw [u₇.gpr, dpVal, r10₆, toNat_and_mask16, u₆.other _ (by decide)]
  have r0₇ : s₇.gpr .r0 = s.gpr .r0 := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have r1₈ : s₈.gpr .r1 = s.gpr .r1 := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have x₈ : (s₈.gpr .r3).toNat = (s.gpr .r0).toNat / 2 ^ 16 := by rw [u₈.gpr, toNat_shr, r0₇]
  have n₉ : (s₉.gpr .r12).toNat = (s.gpr .r1).toNat / 2 ^ 16 := by rw [u₉.gpr, toNat_shr, r1₈]
  have r10₉ : s₉.gpr .r10 = mask16 := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), r10₆]
  have hx := (s.gpr .r0).isLt; have hn := (s.gpr .r1).isLt
  have a₁₀ : (s₁₀.gpr .r3).toNat = (s.gpr .r0).toNat / 2 ^ 16 + (2 ^ 16 - 1) := by
    rw [u₁₀.gpr, dpVal, toNat_add_lt (by rw [u₉.other _ (by decide), x₈, r10₉, toNat_m16]; omega),
      u₉.other _ (by decide), x₈, r10₉, toNat_m16]
  have a₁₁ : (s₁₁.gpr .r3).toNat = (s.gpr .r0).toNat / 2 ^ 16 + (2 ^ 16 - 1) - (s.gpr .r1).toNat / 2 ^ 16 := by
    rw [u₁₁.gpr, dpVal, toNat_sub_le (by rw [a₁₀, u₁₀.other _ (by decide), n₉]; omega), a₁₀,
      u₁₀.other _ (by decide), n₉]
  have c₁₁ : (s₁₁.gpr .r7).toNat = (s₅.gpr .r2).toNat / 2 ^ 16 := by
    rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), c₆]
  have hi : (s₁₂.gpr .r3).toNat = (s.gpr .r0).toNat / 2 ^ 16 + (2 ^ 16 - 1) - (s.gpr .r1).toNat / 2 ^ 16 +
      (s₅.gpr .r2).toNat / 2 ^ 16 := by
    rw [u₁₂.gpr, dpVal, toNat_add_lt (by rw [a₁₁, c₁₁, lo]; omega), a₁₁, c₁₁]
  have c₁₃ : (s₁₃.gpr .r7).toNat = (s₁₂.gpr .r3).toNat / 2 ^ 16 := by
    rw [u₁₃.gpr, toNat_shr]
  have l₁₄ : (s₁₄.gpr .r2).toNat = (s₅.gpr .r2).toNat % 2 ^ 16 := by
    rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide),
      u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), l₇]
  have h₁₄ : s₁₄.gpr .r3 = s₁₂.gpr .r3 <<< 16 := by
    rw [u₁₄.gpr, u₁₃.other _ (by decide)]
  have w : (s₁₅.gpr .r2).toNat = (s₅.gpr .r2).toNat % 2 ^ 16 + (s₁₂.gpr .r3).toNat % 2 ^ 16 * 2 ^ 16 := by
    rw [u₁₅.gpr, dpVal, h₁₄, pack_toNat _ _ (by rw [l₁₄]; omega), l₁₄]
  have c₁₅ : (s₁₅.gpr .r7).toNat = (s₁₂.gpr .r3).toNat / 2 ^ 16 := by
    rw [u₁₅.other _ (by decide), u₁₄.other _ (by decide), c₁₃]
  refine k s₁₅ ?_ ?_ ?_ K
  · rw [w, c₁₅, hi, lo]; simp only [wsub]; omega
  · rw [c₁₅, hi, lo]; omega
  · rw [u₁₅.mem, u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem,
      u₃.mem, u₂.mem, u₁.mem]

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

theorem nWord_cfgOf (P : RfcHash) (j : Nat) : BitVec.ofNat 32 ((cfgOf P).nWord j) = nW j := by
  apply BitVec.eq_of_toNat_eq
  simp only [Cfg.nWord, cfgOf, nW, BitVec.toNat_ofNat]
  omega

theorem movw_movt_val {x : Nat} (hx : x < 2 ^ 32) :
    (BitVec.ofNat 16 (x >>> 16) ++ ((BitVec.ofNat 16 x).setWidth 32).extractLsb' 0 16 : BitVec 32) =
      BitVec.ofNat 32 x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_append, BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.shiftRight_zero]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega), Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  omega

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_movt {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d (imm ++ (s.gpr d).extractLsb' 0 16 : BitVec 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movt d imm :: is)) s Q :=
  VG.Proof.X25519.Arm.WP.cons (s' := s.setReg d (imm ++ (s.gpr d).extractLsb' 0 16 : BitVec 32)) rfl
    (k _ (Upd.setReg _ _ _))

theorem wp_rev {d m : Reg} (k : ∀ s', Upd s s' d (rev (s.gpr m)) → WP isa (.block is) s' Q) :
    WP isa (.block (.rev d m :: is)) s Q :=
  VG.Proof.X25519.Arm.WP.cons rfl (k _ (Upd.setReg _ _ _))

end

/-- After `j` words of the subtraction, from `t`. -/
structure SubInv (L : Lay dn) (g : Reg → BitVec 32) (m₀ : Mem) (M : Mem) (j : Nat) (u : State) : Prop where
  ctx : Ctx L g m₀ u
  r10 : u.gpr .r10 = mask16
  r7 : (u.gpr .r7).toNat = cc M (State.addr L.dg) j
  frame : Frame [⟨L.B + BitVec.ofNat 64 24, 160⟩] M u.mem
  x : ∀ i < j, u.mem.readW (L.B + BitVec.ofNat 64 (180 - 4 * i)) 32 = Xw M (State.addr L.dg) i
  d : ∀ i < j, u.mem.readW (L.B + BitVec.ofNat 64 (52 - 4 * i)) 32 = Dw M (State.addr L.dg) i

theorem fr_sep (B : Addr) {x y : Nat} (h : x + 4 ≤ y ∨ y + 4 ≤ x) (hx : x + 4 ≤ 224) (hy : y + 4 ≤ 224) :
    Mem.Sep (B + BitVec.ofNat 64 x) (32 / 8) (B + BitVec.ofNat 64 y) (32 / 8) :=
  Offset.sep B h (by omega) (by omega)

theorem fpA' (hL : L.Ok) {o e : Nat} (ho : o < 200) (he : 24 + o = e) :
    State.addr (L.fp + BitVec.ofNat 32 o) = L.B + BitVec.ofNat 64 e := by
  rw [hL.fpA ho, he]

theorem subWord_ok (hL : L.Ok) (hn : 32 ≤ dn) {M : Mem} {u : State} {j : Nat} (hj : j < 8) (h : SubInv L g m₀ M j u) :
    WP isa (.block ((cfgOf P).subWord j)) u (SubInv L g m₀ M (j + 1)) := by
  have hc := h.ctx
  have := hL.ng
  have hdg : u.mem.readW (State.addr L.dg + BitVec.ofNat 64 (28 - 4 * j)) 32 =
      M.readW (State.addr L.dg + BitVec.ofNat 64 (28 - 4 * j)) 32 :=
    h.frame.readW (r := L.DG) (Offset.contains_base _ (by omega) (by omega)) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hL.kg.symm.sub_right (Offset.sub_base _ (by omega))) (by decide)
  have o1 : fH + 28 - 4 * j < 4096 := by simp only [fH]; omega
  have o2 : fK + 28 - 4 * j < 4096 := by simp only [fK]; omega
  have a1 : State.addr (L.fp + BitVec.ofNat 32 (fH + 28 - 4 * j)) = L.B + BitVec.ofNat 64 (180 - 4 * j) :=
    fpA' hL (by simp only [fH]; omega) (by simp only [fH]; omega)
  have a2 : State.addr (L.fp + BitVec.ofNat 32 (fK + 28 - 4 * j)) = L.B + BitVec.ofNat 64 (52 - 4 * j) :=
    fpA' hL (by simp only [fK]; omega) (by simp only [fK]; omega)
  have a0 : State.addr (L.dg + BitVec.ofNat 32 (28 - 4 * j)) = State.addr L.dg + BitVec.ofNat 64 (28 - 4 * j) :=
    addr_add (by omega)
  simp only [Cfg.subWord, Cfg.movImm, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_ldr (a := State.addr L.dg + BitVec.ofNat 64 (28 - 4 * j)) (by omega)
    (by rw [hc.r6]; exact a0) (hc.inDg (by omega) (by omega)) fun u₁ v₁ => ?_
  refine wp_rev fun u₂ v₂ => ?_
  refine wp_str (a := L.B + BitVec.ofNat 64 (180 - 4 * j)) o1
    (by rw [v₂.other .r8 (by decide), v₁.other .r8 (by decide), hc.r8]; exact a1)
    (by rw [v₂.wr, v₁.wr]; exact hc.inFrW (by omega) (by omega)) fun u₃ v₃ => ?_
  refine wp_movw fun u₄ v₄ => wp_movt fun u₅ v₅ => ?_
  have hx : u₅.gpr .r0 = Xw M (State.addr L.dg) j := by
    rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr, v₂.gpr, v₁.gpr, hdg]
  have hnw : u₅.gpr .r1 = nW j := by
    rw [v₅.gpr, v₄.gpr, movw_movt_val (by simp only [Cfg.nWord]; omega), nWord_cfgOf]
  have h10 : u₅.gpr .r10 = mask16 := by
    rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr, v₂.other _ (by decide), v₁.other _ (by decide),
      h.r10]
  have h7 : (u₅.gpr .r7).toNat = cc M (State.addr L.dg) j := by
    rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr, v₂.other _ (by decide), v₁.other _ (by decide),
      h.r7]
  refine digits_ok h10 (by rw [h7]; exact cc_le _ _ _) fun u₆ e₆ c₆ m₆ K₆ => ?_
  have K₅ : Rest [.r0, .r1, .r2, .r3, .r7, .r12] u u₆ :=
    (v₁.rest (by simp)).trans <| (v₂.rest (by simp)).trans <| (v₃.rest _).trans <| (v₄.rest (by simp)).trans <|
    (v₅.rest (by simp)).trans (K₆.mono (by simp))
  refine wp_str (a := L.B + BitVec.ofNat 64 (52 - 4 * j)) o2
    (by rw [K₅.gpr .r8 (by decide), hc.r8]; exact a2)
    (by rw [K₅.wr]; exact hc.inFrW (by omega) (by omega)) fun u₇ v₇ => WP.block_nil ?_
  rw [hx, hnw, h7] at e₆
  have hd : u₆.gpr .r2 = Dw M (State.addr L.dg) j := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, ← e₆]
    have := (u₆.gpr .r2).isLt
    omega
  have hm₇ : u₇.mem = (u.mem.writeW (L.B + BitVec.ofNat 64 (180 - 4 * j)) (Xw M (State.addr L.dg) j)).writeW
      (L.B + BitVec.ofNat 64 (52 - 4 * j)) (Dw M (State.addr L.dg) j) := by
    rw [v₇.mem, hd, m₆, v₅.mem, v₄.mem, v₃.mem, v₂.gpr, v₂.mem, v₁.gpr, v₁.mem, hdg]
  have hf : Frame [⟨L.B + BitVec.ofNat 64 24, 160⟩] u.mem u₇.mem := by
    rw [hm₇]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (by omega) (by omega) (by omega))).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (by omega) (by omega) (by omega))
  refine ⟨hc.keep hL (by rw [v₇.rd, K₅.rd]) (by rw [v₇.wr, K₅.wr]) (by rw [v₇.sp, K₅.sp])
      (fun r hr => by rw [v₇.gpr, K₅.gpr r (by revert hr r; decide)]) hf
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by omega)),
    by rw [v₇.gpr, K₅.gpr _ (by decide), h.r10], by rw [v₇.gpr]; simp only [cc]; omega,
    h.frame.trans hf, fun i hi => ?_, fun i hi => ?_⟩
  · rw [hm₇, Mem.readW_writeW_sep (fr_sep _ (by omega) (by omega) (by omega)) (by decide)]
    rcases Nat.lt_or_ge i j with hij | hij
    · rw [Mem.readW_writeW_sep (fr_sep _ (by omega) (by omega) (by omega)) (by decide)]; exact h.x i hij
    · rw [show i = j by omega, Mem.readW_writeW_self32]
  · rw [hm₇]
    rcases Nat.lt_or_ge i j with hij | hij
    · rw [Mem.readW_writeW_sep (fr_sep _ (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_sep (fr_sep _ (by omega) (by omega) (by omega)) (by decide)]; exact h.d i hij
    · rw [show i = j by omega, Mem.readW_writeW_self32]

/-- The words before `k`. -/
theorem subs_ok (hL : L.Ok) (hn : 32 ≤ dn) {M : Mem} : ∀ k ≤ 8, ∀ u, SubInv L g m₀ M 0 u →
    WP isa (.block ((List.range k).flatMap (cfgOf P).subWord)) u (SubInv L g m₀ M k)
  | 0, _, u, h => WP.block_nil h
  | k + 1, hk, u, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    exact WP.mono (subs_ok hL hn k (by omega) u h) fun u' h' => subWord_ok hL hn (by omega) h'

/-- The mask of the last carry. -/
abbrev mask {dn : Nat} (L : Lay dn) (m : Mem) : BitVec 32 :=
  if cc m (State.addr L.dg) 8 = 1 then BitVec.allOnes 32 else 0

/-- The word selected. -/
abbrev Sw {dn : Nat} (L : Lay dn) (m : Mem) (i : Nat) : BitVec 32 :=
  if cc m (State.addr L.dg) 8 = 1 then Dw m (State.addr L.dg) i else Xw m (State.addr L.dg) i

/-- After the mask and `j` words of the selection, from `t`. -/
structure SelInv (L : Lay dn) (g : Reg → BitVec 32) (m₀ : Mem) (M : Mem) (j : Nat) (u : State) : Prop where
  ctx : Ctx L g m₀ u
  r7 : u.gpr .r7 = mask L M
  frame : Frame [⟨L.B + BitVec.ofNat 64 24, 160⟩] M u.mem
  h : ∀ i < j, u.mem.readW (L.B + BitVec.ofNat 64 (180 - 4 * i)) 32 = rev (Sw L M i)
  x : ∀ i, j ≤ i → i < 8 → u.mem.readW (L.B + BitVec.ofNat 64 (180 - 4 * i)) 32 = Xw M (State.addr L.dg) i
  d : ∀ i < 8, u.mem.readW (L.B + BitVec.ofNat 64 (52 - 4 * i)) 32 = Dw M (State.addr L.dg) i

theorem sel_val (x d : BitVec 32) (p : Prop) [Decidable p] :
    x ^^^ ((d ^^^ x) &&& (if p then BitVec.allOnes 32 else 0)) = if p then d else x := by
  by_cases h : p
  · simp only [h, ↓reduceIte, BitVec.and_allOnes]
    rw [BitVec.xor_comm d x, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  · simp only [h, ↓reduceIte]
    rw [show (0 : BitVec 32) = 0#32 from rfl]
    simp only [BitVec.and_zero, BitVec.xor_zero]

theorem selWord_ok (hL : L.Ok) {M : Mem} {u : State} {j : Nat} (hj : j < 8) (h : SelInv L g m₀ M j u) :
    WP isa (.block (Cfg.selWord j)) u (SelInv L g m₀ M (j + 1)) := by
  have hc := h.ctx
  have o1 : fH + 28 - 4 * j < 4096 := by simp only [fH]; omega
  have o2 : fK + 28 - 4 * j < 4096 := by simp only [fK]; omega
  have a1 : State.addr (L.fp + BitVec.ofNat 32 (fH + 28 - 4 * j)) = L.B + BitVec.ofNat 64 (180 - 4 * j) :=
    fpA' hL (by simp only [fH]; omega) (by simp only [fH]; omega)
  have a2 : State.addr (L.fp + BitVec.ofNat 32 (fK + 28 - 4 * j)) = L.B + BitVec.ofNat 64 (52 - 4 * j) :=
    fpA' hL (by simp only [fK]; omega) (by simp only [fK]; omega)
  simp only [Cfg.selWord]
  refine wp_ldr (a := L.B + BitVec.ofNat 64 (180 - 4 * j)) o1 (by rw [hc.r8]; exact a1)
    (hc.inFr (by omega) (by omega)) fun u₁ v₁ => ?_
  refine wp_ldr (a := L.B + BitVec.ofNat 64 (52 - 4 * j)) o2 (by rw [v₁.other .r8 (by decide), hc.r8]; exact a2)
    (by rw [v₁.rd, v₁.wr]; exact hc.inFr (by omega) (by omega)) fun u₂ v₂ => ?_
  refine wp_dp (op2_reg _ _) fun u₃ v₃ => wp_dp (op2_reg _ _) fun u₄ v₄ => wp_dp (op2_reg _ _) fun u₅ v₅ => ?_
  refine wp_rev fun u₆ v₆ => ?_
  have K₆ : Rest [.r0, .r1] u u₆ :=
    (v₁.rest (by simp)).trans <| (v₂.rest (by simp)).trans <| (v₃.rest (by simp)).trans <|
    (v₄.rest (by simp)).trans <| (v₅.rest (by simp)).trans (v₆.rest (by simp))
  refine wp_str (a := L.B + BitVec.ofNat 64 (180 - 4 * j)) o1
    (by rw [K₆.gpr .r8 (by decide), hc.r8]; exact a1)
    (by rw [K₆.wr]; exact hc.inFrW (by omega) (by omega)) fun u₇ v₇ => WP.block_nil ?_
  have val : u₆.gpr .r0 = rev (Sw L M j) := by
    rw [v₆.gpr, v₅.gpr, dpVal, v₄.gpr, dpVal, v₄.other .r0 (by decide), v₃.gpr, dpVal, v₃.other .r0 (by decide),
      v₃.other .r7 (by decide), v₂.gpr, v₂.other .r0 (by decide), v₂.other .r7 (by decide), v₁.gpr,
      v₁.other .r7 (by decide), v₁.mem, h.x j (by omega) hj, h.d j hj, h.r7, Sw, mask]
    exact congrArg rev (sel_val _ _ _)
  have hm₇ : u₇.mem = u.mem.writeW (L.B + BitVec.ofNat 64 (180 - 4 * j)) (rev (Sw L M j)) := by
    rw [v₇.mem, val, v₆.mem, v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem]
  have hf : Frame [⟨L.B + BitVec.ofNat 64 24, 160⟩] u.mem u₇.mem := by
    rw [hm₇]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))
  refine ⟨hc.keep hL (by rw [v₇.rd, K₆.rd]) (by rw [v₇.wr, K₆.wr]) (by rw [v₇.sp, K₆.sp])
      (fun r hr => by rw [v₇.gpr, K₆.gpr r (by revert hr r; decide)]) hf
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by omega)),
    by rw [v₇.gpr, K₆.gpr _ (by decide), h.r7], h.frame.trans hf, fun i hi => ?_, fun i hi hi' => ?_,
    fun i hi => ?_⟩
  · rw [hm₇]
    rcases Nat.lt_or_ge i j with hij | hij
    · rw [Mem.readW_writeW_sep (fr_sep _ (by omega) (by omega) (by omega)) (by decide)]; exact h.h i hij
    · rw [show i = j by omega, Mem.readW_writeW_self32]
  · rw [hm₇, Mem.readW_writeW_sep (fr_sep _ (by omega) (by omega) (by omega)) (by decide)]
    exact h.x i (by omega) hi'
  · rw [hm₇, Mem.readW_writeW_sep (fr_sep _ (by omega) (by omega) (by omega)) (by decide)]
    exact h.d i hi

/-- The words before `k`. -/
theorem sels_ok (hL : L.Ok) {M : Mem} : ∀ k ≤ 8, ∀ u, SelInv L g m₀ M 0 u →
    WP isa (.block ((List.range k).flatMap Cfg.selWord)) u (SelInv L g m₀ M k)
  | 0, _, u, h => WP.block_nil h
  | k + 1, hk, u, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    exact WP.mono (sels_ok hL k (by omega) u h) fun u' h' => selWord_ok hL (by omega) h'

theorem dg_ofBytes (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (hn : 32 ≤ dn) :
    Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ (State.addr L.dg) 32) =
      Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem (State.addr L.dg) 32) := by
  congr 1
  simp only [Spec.Sha256.bytesAt]
  exact List.map_congr_left fun i hi => (hc.dg_byte hL (by have := List.mem_range.mp hi; omega)).symm

theorem mask_val {c : BitVec 32} (h : c.toNat ≤ 1) :
    (0 : BitVec 32) - c = if c.toNat = 1 then BitVec.allOnes 32 else 0 := by
  rcases (by omega : c.toNat = 0 ∨ c.toNat = 1) with e | e
  · rw [show c = 0 from BitVec.eq_of_toNat_eq (by rw [e]; rfl)]; decide
  · rw [show c = 1 from BitVec.eq_of_toNat_eq (by rw [e]; rfl)]; decide

/-- `h`: the digest modulo `n`, big-endian in the frame. -/
theorem reduce_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (hn : 32 ≤ dn) :
    WP isa (.block (cfgOf P).reduce) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 24, 160⟩] t.mem t'.mem ∧
      Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 152) 32) =
        Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ (State.addr L.dg) 32) % Spec.P256.n := by
  simp only [Cfg.reduce, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_movw fun u₁ v₁ => wp_mov (op2_imm (by decide)) fun u₂ v₂ => ?_
  have hc₂ : Ctx L g m₀ u₂ := (hc.upd v₁ (by decide)).upd v₂ (by decide)
  rw [WP.block_append_iff]
  have hmu : u₂.mem = t.mem := by rw [v₂.mem, v₁.mem]
  refine WP.mono (subs_ok (P := P) (M := t.mem) hL hn 8 (Nat.le_refl _) u₂
    ⟨hc₂, by rw [v₂.other _ (by decide), v₁.gpr], by rw [v₂.gpr]; rfl, by rw [hmu]; exact Frame.refl _ _,
      fun i hi => absurd hi (Nat.not_lt_zero _), fun i hi => absurd hi (Nat.not_lt_zero _)⟩) fun u hu => ?_
  refine wp_mov (op2_imm (by decide)) fun u₃ v₃ => wp_dp (op2_reg _ _) fun u₄ v₄ => ?_
  have hc₄ : Ctx L g m₀ u₄ := (hu.ctx.upd v₃ (by decide)).upd v₄ (by decide)
  have h7 : u₄.gpr .r7 = mask L t.mem := by
    rw [v₄.gpr, dpVal, v₃.gpr, v₃.other _ (by decide), mask_val (by rw [hu.r7]; exact cc_le _ _ _), hu.r7]
  have hm₄ : u₄.mem = u.mem := by rw [v₄.mem, v₃.mem]
  refine WP.mono (sels_ok (M := t.mem) hL 8 (Nat.le_refl _) u₄
    ⟨hc₄, h7, by rw [hm₄]; exact hu.frame, fun i hi => absurd hi (Nat.not_lt_zero _),
      fun i _ hi => by rw [hm₄]; exact hu.x i hi, fun i hi => by rw [hm₄]; exact hu.d i hi⟩)
    fun t' h' => ⟨h'.ctx, h'.frame, ?_⟩
  have hX := ofBytes_words t.mem (Xw t.mem (State.addr L.dg)) (State.addr L.dg) 8 fun j hj => by
    show byteRev32 _ = rev _
    rw [show 4 * (8 - 1 - j) = 28 - 4 * j by omega]; rfl
  have hH := ofBytes_words t'.mem (Sw L t.mem) (L.B + BitVec.ofNat 64 152) 8 fun j hj => by
    rw [Offset.add_add, show 152 + 4 * (8 - 1 - j) = 180 - 4 * j by omega, h'.h j hj]
    exact Proof.Pbkdf2.Whole.byteRev32_byteRev32 _
  rw [dg_ofBytes hL hc hn]
  change Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt _ _ (4 * 8)) =
    Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt _ _ (4 * 8)) % _
  rw [hH, hX]
  exact reduce_math _ _

end VG.Proof.Ecdsa.Rfc6979.Arm
