module

public import VerifiedGarbage.Proof.Aes.RISCV64.WideCbc
public import VerifiedGarbage.Proof.AesCfb.Spec
import VerifiedGarbage.Proof.Aes.RISCV64.ChainModes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Aes.RISCV64.WideCbc
meta import VerifiedGarbage.Proof.AesCfb.Spec
meta import VerifiedGarbage.Proof.Aes.RISCV64.ChainModes
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.TCB.RISCV64.Target

-- separate module: CFB128 decryption's instance of `wide`, which only AES-CFB's `Verified` imports,
-- apart from the generic proof (`Wide.lean`) that the other modes' instances import too.

/-!
# AES-CFB128 decryption on RISC-V, four blocks at a time

`cfbDecWide` (`Impl/Aes/RISCV64/Wide.lean`) is `wide cfbLoad cfbStore
encrypt4`: `cfbLoad k` puts `Cⱼ₋₁` (`cbcP`, the IV for the first block)
in the state registers, from the state's slots (`stLo`) for the group's
first block and from the data block before it, which the group has not yet
overwritten, for the others; `encrypt4` enciphers the four; and
`cfbStore k` makes `Cⱼ` (`cbcC`) the state and stores
`Pⱼ = Cⱼ ⊕ CIPH_K(Cⱼ₋₁)` (`cfbD`) over it. Its invariants (`cfbL`, `cfbS`):
the data is `cfbD`'s up to the blocks stored, the state's slots hold
`Cⱼ₋₁` of the next block, and the group's registers its blocks' `Cⱼ₋₁`,
enciphered once `encrypt4` has run. `cfb_ok` is its `WideOk`, `cfb_out`
and `cfb_chain` that `cfbD` and `cbcP` are CFB128 decryption's
(`Spec.Cfb.decrypt`, and its last ciphertext block), and `cfbDecWide_k`
states it as a chain to call (`AesCbc.RISCV64.ChainK`).
-/

@[expose] public section

namespace VG.Proof.Aes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.RISCV64.Steps VG.Bitslice VG.Impl.Aes.RISCV64
  VG.Impl.Words.RISCV64 VG.Proof.Aes

/-! ## The blocks -/

/-- The plaintext block `Pⱼ = Cⱼ ⊕ CIPH_K(Cⱼ₋₁)`. -/
abbrev cfbD (R : Nat) (w : List Byte) (m₀ : Mem) (D : Addr) (iv : Spec.Aes.State) (j : Nat) :
    Spec.Aes.State :=
  vxor (cbcC m₀ D j) (Spec.Aes.cipher R w (cbcP m₀ D iv j))

/-- CFB128 decryption: block `j` from block `j` and the one before (the IV). -/
theorem cfbDecrypt_eq (ciph : Spec.Cbc.Cipher) : ∀ (xs : List (List Byte)) (iv : List Byte),
    Spec.Cfb.decrypt ciph iv xs =
      (List.range xs.length).map fun j => Spec.Cbc.xor (xs.getD j []) (ciph ((iv :: xs).getD j []))
  | [], _ => rfl
  | x :: xs, iv => by
    rw [Spec.Cfb.decrypt, cfbDecrypt_eq ciph xs x, List.length_cons, List.range_succ_eq_map, List.map_cons,
      List.map_map]
    simp only [List.getD_cons_zero, List.getD_cons_succ, Function.comp_def]

theorem cfb_out (R : Nat) (w : List Byte) (m : Mem) (D : Addr) (iv : Spec.Aes.State) (n : Nat) :
    (AesCfb.cfbMode false).out R w iv.toList (Spec.Cbc.blocksAt m D n) =
      (List.range n).map fun j => (cfbD R w m D iv j).toList := by
  rw [AesCfb.cfbMode_out, AesCfb.cfb, ite_eq_right Bool.false_ne_true, cfbDecrypt_eq,
    show (Spec.Cbc.blocksAt m D n).length = n by simp [Spec.Cbc.blocksAt]]
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.mp hj
  have e₁ : (Spec.Cbc.blocksAt m D n).getD j [] = (cbcC m D j).toList := by
    rw [blocksAt_cbcC]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj, Option.map_some,
      Option.getD_some]
  have e₂ : (iv.toList :: Spec.Cbc.blocksAt m D n).getD j [] = (cbcP m D iv j).toList := by
    cases j with
    | zero => rfl
    | succ j =>
      rw [List.getD_cons_succ, blocksAt_cbcC]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (show j < n by omega),
        Option.map_some, Option.getD_some]
      rfl
  rw [e₁, e₂, aesWith_toList, toList_vxor]
  rfl

theorem cfb_chain (R : Nat) (w : List Byte) (m : Mem) (D : Addr) (iv : Spec.Aes.State) (n : Nat) :
    (AesCfb.cfbMode false).chain R w iv.toList (Spec.Cbc.blocksAt m D n) = (cbcP m D iv n).toList := by
  rw [AesCfb.cfbMode_chain, AesCbc.cts, ite_eq_right Bool.false_ne_true, blocksAt_cbcC]
  exact next_range (fun j => (cbcP m D iv j).toList) n

/-! ## The invariants -/

/-- The loads of group `g`, after `k` of them: the data `cfbD`'s up to the
group, the state's slots `Cⱼ₋₁` of its first block, and the first `k` of
its blocks' `Cⱼ₋₁` in the registers. -/
def cfbL (m₀ : Mem) (D : Addr) (iv : Spec.Aes.State) (R : Nat) (w : List Byte) (n : Nat) (b : Addr)
    (g k : Nat) (m : Mem) (Q : Nat → BitVec 64) : Prop :=
  EcbInv m₀ m D n (4 * g) (cfbD R w m₀ D iv) ∧ slotBlk m b stLo = cbcP m₀ D iv (4 * g) ∧
    ∀ c < k, regBlock Q c = cbcP m₀ D iv (4 * g + c)

/-- The stores of group `g`, after `k` of them: the data `cfbD`'s up to
them, the state's slots `Cⱼ₋₁` of the next block, and the others' `Cⱼ₋₁`
enciphered in the registers. -/
def cfbS (m₀ : Mem) (D : Addr) (iv : Spec.Aes.State) (R : Nat) (w : List Byte) (n : Nat) (b : Addr)
    (g k : Nat) (m : Mem) (Q : Nat → BitVec 64) : Prop :=
  EcbInv m₀ m D n (4 * g + k) (cfbD R w m₀ D iv) ∧ slotBlk m b stLo = cbcP m₀ D iv (4 * g + k) ∧
    ∀ c < min 4 (n - 4 * g), k ≤ c → regBlock Q c = Spec.Aes.cipher R w (cbcP m₀ D iv (4 * g + c))

/-- Two doubleword writes at separate addresses commute. -/
theorem writeW64_comm (m : Mem) {a b : Addr} (h : Mem.Sep a 8 b 8) (v w : BitVec 64) :
    (m.writeW a v).writeW b w = (m.writeW b w).writeW a v := by
  funext x
  by_cases ha : (x - a).toNat < 8
  · simp only [Mem.writeW, Mem.write, ha, h x ha, ite_true, ite_false]
  · simp only [Mem.writeW, Mem.write, ha, ite_false]

section Steps

variable {s₀ s₉ : State} {X b : Addr} (hs : FSetup true (16 * ·) s₀ s₉ X b) {iv : Spec.Aes.State}
  {R : Nat} {w : List Byte}
include hs

/-- A doubleword of the data and a slot (of 78–87) are separate. -/
theorem data_sep_slot {j off : Nat} (hj : j < 88) (ho : off + 8 ≤ 16 * (s₀.gpr .a4).toNat) :
    Mem.Sep (s₀.gpr .a3 + BitVec.ofNat 64 off) 8 (b + BitVec.ofNat 64 (8 * j)) 8 :=
  (hs.slotW_data hj _ (List.mem_singleton_self _)).symm.sep
    (Offset.contains_base _ ho (by have := hs.n16; omega)) (Region.contains_self _ _)

omit hs in
/-- The end of a load: `Cⱼ₋₁` of block `k` in its registers. -/
theorem cfbLoad_fin {g k : Nat} (hk : k < 4) {s : State}
    (hd : EcbInv s₀.mem s.mem (s₀.gpr .a3) (s₀.gpr .a4).toNat (4 * g) (cfbD R w s₀.mem (s₀.gpr .a3) iv))
    (hst : slotBlk s.mem b stLo = cbcP s₀.mem (s₀.gpr .a3) iv (4 * g))
    (hblk : ∀ c < k, regBlock (Q s) c = cbcP s₀.mem (s₀.gpr .a3) iv (4 * g + c))
    (s' : State) (lo hi : BitVec 64) (hv : wBlk lo hi = cbcP s₀.mem (s₀.gpr .a3) iv (4 * g + k))
    (e₁ : s'.gpr (q k) = lo) (e₂ : s'.gpr (q (k + 4)) = hi)
    (o : ∀ r, r ≠ q k → r ≠ q (k + 4) → r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r) (m : s'.mem = s.mem)
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) (sp : s'.sp = s.sp) :
    Foot s₀ b s s' ∧ cfbL s₀.mem (s₀.gpr .a3) iv R w (s₀.gpr .a4).toNat b g (k + 1) s'.mem (Q s') := by
  refine ⟨⟨fun r h1 _ => o r (fun e => h1 (e ▸ q_mem k (by omega))) (fun e => h1 (e ▸ q_mem (k + 4) (by omega)))
      (fun e => h1 (e ▸ by decide)) (fun e => h1 (e ▸ by decide)), rd, wr, sp,
    by rw [m]; exact Frame.refl _ _⟩, by rw [m]; exact hd, by rw [m]; exact hst, fun c hc => ?_⟩
  by_cases hck : c = k
  · subst hck
    rw [regBlock_wBlk]
    show wBlk (s'.gpr (q c)) (s'.gpr (q (c + 4))) = _
    rw [e₁, e₂, hv]
  · obtain ⟨d1, d2, d3, d4⟩ := q_pairs c (by omega) k hk hck
    obtain ⟨-, -, -, -, -, -, -, d5, d6, d7, d8⟩ := q_c4 c (by omega)
    rw [regBlock_wBlk, ← hblk c (by omega), regBlock_wBlk]
    show wBlk (s'.gpr (q c)) (s'.gpr (q (c + 4))) = wBlk (s.gpr (q c)) (s.gpr (q (c + 4)))
    rw [o _ d1 d2 d5 d6, o _ d3 d4 d7 d8]

/-- `Cⱼ₋₁` of block `k` into the registers. -/
theorem cfbLoad_ok {g k : Nat} (hk : k < 4) (hkn : 4 * g + k < (s₀.gpr .a4).toNat) {s : State}
    (hb : WB s₀ s₉ b g s) (hl : cfbL s₀.mem (s₀.gpr .a3) iv R w (s₀.gpr .a4).toNat b g k s.mem (Q s)) :
    WP isa (.block (cfbLoad k)) s fun s' =>
      Foot s₀ b s s' ∧ cfbL s₀.mem (s₀.gpr .a3) iv R w (s₀.gpr .a4).toNat b g (k + 1) s'.mem (Q s') := by
  obtain ⟨hd, hst, hblk⟩ := hl
  have hn := hs.n16
  have hdat := hb.dat hs
  have hscr := hb.scr hs
  have hbase := hb.base hs
  obtain ⟨n1, n2, n3, -, -, -, -, n8, n9, n10, n11⟩ := q_c4 k hk
  by_cases h0 : k = 0
  · subst h0
    unfold cfbLoad
    rw [ite_eq_left rfl]
    refine slot_ld hscr hbase (by decide) fun s₁ u₁ => ?_
    refine slot_ld (hscr.congr u₁.wr (u₁.other _ (by decide))) ((u₁.other _ (by decide)).trans hbase)
      (by decide) fun s₂ u₂ => WP.block_nil ?_
    exact cfbLoad_fin hk hd hst hblk s₂ (s.mem.readW (b + BitVec.ofNat 64 (8 * stLo)) 64)
      (s.mem.readW (b + BitVec.ofNat 64 (8 * (stLo + 1))) 64) hst ((u₂.other _ (by decide)).trans u₁.gpr)
      (u₂.gpr.trans (by rw [u₁.mem])) (fun r h1 h2 _ _ => (u₂.other _ h2).trans (u₁.other _ h1))
      (u₂.mem.trans u₁.mem) (u₂.rd.trans u₁.rd) (u₂.wr.trans u₁.wr) (u₂.sp.trans u₁.sp)
  · unfold cfbLoad
    rw [ite_eq_right h0, WP.block_append_iff (M := isa)]
    refine WP.mono (data_ld (off := 16 * (k - 1)) hb.a3 (List.mem_append_right _ hdat) hn (by omega)
      (by omega) ⟨n1, n8, n9⟩) fun s₁ ⟨e₁, o₁, m₁, rd₁, wr₁, sp₁⟩ => ?_
    refine WP.mono (data_ld (D := s₀.gpr .a3) (g := g) (n := (s₀.gpr .a4).toNat) (off := 16 * (k - 1) + 8)
      (by rw [o₁ _ (Ne.symm n1) (by decide) (by decide)]; exact hb.a3)
      (by rw [rd₁, wr₁]; exact List.mem_append_right _ hdat) hn (by omega) (by omega) ⟨n2, n10, n11⟩)
      fun s₂ ⟨e₂, o₂, m₂, rd₂, wr₂, sp₂⟩ => ?_
    have hv : wBlk (s.mem.readW (s₀.gpr .a3 + BitVec.ofNat 64 (64 * g + 16 * (k - 1))) 64)
        (s.mem.readW (s₀.gpr .a3 + BitVec.ofNat 64 (64 * g + (16 * (k - 1) + 8))) 64) =
        cbcP s₀.mem (s₀.gpr .a3) iv (4 * g + k) := by
      rw [show 64 * g + 16 * (k - 1) = 16 * (4 * g + (k - 1)) by omega,
        show 64 * g + (16 * (k - 1) + 8) = 16 * (4 * g + (k - 1)) + 8 by omega, add_off8, ← stateAt_wBlk,
        ecbInv_orig hd (by omega) (by omega), show 4 * g + k = 4 * g + (k - 1) + 1 by omega]
      rfl
    exact cfbLoad_fin hk hd hst hblk s₂ _ _ hv (by rw [o₂ _ n3 n8 n9, e₁]) (by rw [e₂, m₁])
      (fun r h1 h2 h3 h4 => by rw [o₂ r h2 h3 h4, o₁ r h1 h3 h4]) (m₂.trans m₁) (rd₂.trans rd₁)
      (wr₂.trans wr₁) (sp₂.trans sp₁)

/-- `Cⱼ` of block `k` the state, and `Pⱼ` stored over it. -/
theorem cfbStore_ok {g k : Nat} (hk : k < 4) (hkn : 4 * g + k < (s₀.gpr .a4).toNat) {s : State}
    (hb : WB s₀ s₉ b g s) (hl : cfbS s₀.mem (s₀.gpr .a3) iv R w (s₀.gpr .a4).toNat b g k s.mem (Q s)) :
    WP isa (.block (cfbStore k)) s fun s' =>
      Foot s₀ b s s' ∧ cfbS s₀.mem (s₀.gpr .a3) iv R w (s₀.gpr .a4).toNat b g (k + 1) s'.mem (Q s') := by
  obtain ⟨hd, hst, hblk⟩ := hl
  have hn := hs.n16
  have hdat := hb.dat hs
  have hscr := hb.scr hs
  have hbase := hb.base hs
  have hkm : k < min 4 ((s₀.gpr .a4).toNat - 4 * g) := by omega
  obtain ⟨-, -, -, -, -, -, -, n8, n9, n10, n11⟩ := q_c4 k hk
  have eA : s₀.gpr .a3 + BitVec.ofNat 64 (64 * g + 16 * k) =
      s₀.gpr .a3 + BitVec.ofNat 64 (16 * (4 * g + k)) := by
    rw [show 64 * g + 16 * k = 16 * (4 * g + k) by omega]
  have eA8 : s₀.gpr .a3 + BitVec.ofNat 64 (64 * g + (16 * k + 8)) =
      s₀.gpr .a3 + BitVec.ofNat 64 (16 * (4 * g + k)) + 8 := by
    rw [show 64 * g + (16 * k + 8) = 16 * (4 * g + k) + 8 by omega, add_off8]
  unfold cfbStore
  repeat rw [WP.block_append_iff (M := isa)]
  -- The low doubleword of `Cⱼ`, into the state's slot, XORed, stored.
  refine WP.mono (data_ld (off := 16 * k) hb.a3 (List.mem_append_right _ hdat) hn (by omega) (by omega)
    (d := .t2) ⟨by decide, by decide, by decide⟩) fun s₁ ⟨e₁, o₁, m₁, rd₁, wr₁, sp₁⟩ => ?_
  have g₁ : s₁.gpr sb = s.gpr sb := o₁ _ (by decide) (by decide) (by decide)
  refine slot_st (hscr.congr wr₁ g₁) (g₁.trans hbase) (by decide) fun s₂ u₂ => wp_xor fun s₃ u₃ =>
    WP.block_nil ?_
  have o₃ : ∀ r, r ≠ .t2 → r ≠ t0 → r ≠ t1 → s₃.gpr r = s.gpr r := fun r h h0 h1 => by
    rw [u₃.other _ h, u₂.gpr, o₁ _ h h0 h1]
  refine WP.mono (data_st (D := s₀.gpr .a3) (g := g) (n := (s₀.gpr .a4).toNat) (off := 16 * k)
    (by rw [o₃ _ (by decide) (by decide) (by decide)]; exact hb.a3)
    (by rw [u₃.wr, u₂.wr, wr₁]; exact hdat) hn (by omega) (by omega) (by decide))
    fun s₄ ⟨m₄, o₄, rd₄, wr₄, sp₄⟩ => ?_
  -- The high doubleword.
  refine WP.mono (data_ld (D := s₀.gpr .a3) (g := g) (n := (s₀.gpr .a4).toNat) (off := 16 * k + 8)
    (by rw [o₄ _ (by decide) (by decide), o₃ _ (by decide) (by decide) (by decide)]; exact hb.a3)
    (by rw [rd₄, wr₄, u₃.rd, u₃.wr, u₂.rd, u₂.wr, rd₁, wr₁]; exact List.mem_append_right _ hdat)
    hn (by omega) (by omega) (d := .t2) ⟨by decide, by decide, by decide⟩)
    fun s₅ ⟨e₅, o₅, m₅, rd₅, wr₅, sp₅⟩ => ?_
  have o₅' : ∀ r, r ≠ .t2 → r ≠ t0 → r ≠ t1 → s₅.gpr r = s.gpr r := fun r h h0 h1 => by
    rw [o₅ _ h h0 h1, o₄ _ h0 h1, o₃ _ h h0 h1]
  have g₅ : s₅.gpr sb = s.gpr sb := o₅' _ (by decide) (by decide) (by decide)
  refine slot_st (hscr.congr (by rw [wr₅, wr₄, u₃.wr, u₂.wr, wr₁]) g₅) (g₅.trans hbase) (by decide)
    fun s₆ u₆ => wp_xor fun s₇ u₇ => WP.block_nil ?_
  have o₇ : ∀ r, r ≠ .t2 → r ≠ t0 → r ≠ t1 → s₇.gpr r = s.gpr r := fun r h h0 h1 => by
    rw [u₇.other _ h, u₆.gpr, o₅' _ h h0 h1]
  refine WP.mono (data_st (D := s₀.gpr .a3) (g := g) (n := (s₀.gpr .a4).toNat) (off := 16 * k + 8)
    (by rw [o₇ _ (by decide) (by decide) (by decide)]; exact hb.a3)
    (by rw [u₇.wr, u₆.wr, wr₅, wr₄, u₃.wr, u₂.wr, wr₁]; exact hdat) hn (by omega) (by omega) (by decide))
    fun s₈ ⟨m₈, o₈, rd₈, wr₈, sp₈⟩ => ?_
  -- The separations, and the values.
  have sAA : Mem.Sep (s₀.gpr .a3 + BitVec.ofNat 64 (16 * (4 * g + k)) + 8) 8
      (s₀.gpr .a3 + BitVec.ofNat 64 (16 * (4 * g + k))) 8 := by
    rw [← add_off8]; exact Offset.sep _ (Or.inr (by omega)) (by omega) (by omega)
  have sAS₀ : Mem.Sep (s₀.gpr .a3 + BitVec.ofNat 64 (16 * (4 * g + k)) + 8) 8
      (b + BitVec.ofNat 64 (8 * stLo)) 8 := by
    rw [← add_off8]; exact data_sep_slot hs (by decide) (by omega)
  have sAS₁ : Mem.Sep (s₀.gpr .a3 + BitVec.ofNat 64 (16 * (4 * g + k))) 8
      (b + BitVec.ofNat 64 (8 * (stLo + 1))) 8 := data_sep_slot hs (by decide) (by omega)
  have e₁' : s₁.gpr .t2 = s.mem.readW (s₀.gpr .a3 + BitVec.ofNat 64 (16 * (4 * g + k))) 64 := by
    rw [e₁, eA]
  have x₃ : s₃.gpr .t2 = s.mem.readW (s₀.gpr .a3 + BitVec.ofNat 64 (16 * (4 * g + k))) 64 ^^^
      s.gpr (q k) := by
    rw [u₃.gpr, u₂.gpr, e₁', o₁ _ (q_neW k).2.2.1 n8 n9]
  have t₅ : s₅.gpr .t2 = s.mem.readW (s₀.gpr .a3 + BitVec.ofNat 64 (16 * (4 * g + k)) + 8) 64 := by
    rw [e₅, eA8, m₄, u₃.mem, u₂.mem, m₁, eA, Mem.readW_writeW_sep sAA (by decide),
      Mem.readW_writeW_sep sAS₀ (by decide)]
  have x₇ : s₇.gpr .t2 = s.mem.readW (s₀.gpr .a3 + BitVec.ofNat 64 (16 * (4 * g + k)) + 8) 64 ^^^
      s.gpr (q (k + 4)) := by
    rw [u₇.gpr, u₆.gpr, t₅, o₅' _ (q_neW _).2.2.1 n10 n11]
  have hm₈ : s₈.mem = ((((s.mem.writeW (b + BitVec.ofNat 64 (8 * stLo))
      (s.mem.readW (s₀.gpr .a3 + BitVec.ofNat 64 (16 * (4 * g + k))) 64)).writeW
      (b + BitVec.ofNat 64 (8 * (stLo + 1)))
      (s.mem.readW (s₀.gpr .a3 + BitVec.ofNat 64 (16 * (4 * g + k)) + 8) 64)).writeW
      (s₀.gpr .a3 + BitVec.ofNat 64 (16 * (4 * g + k))) (s₃.gpr .t2)).writeW
      (s₀.gpr .a3 + BitVec.ofNat 64 (16 * (4 * g + k)) + 8) (s₇.gpr .t2)) := by
    rw [m₈, u₇.mem, u₆.mem, t₅, m₅, m₄, u₃.mem, u₂.mem, e₁', m₁, eA, eA8, writeW64_comm _ sAS₁]
  -- The block's values.
  have hC : wBlk (s.mem.readW (s₀.gpr .a3 + BitVec.ofNat 64 (16 * (4 * g + k))) 64)
      (s.mem.readW (s₀.gpr .a3 + BitVec.ofNat 64 (16 * (4 * g + k)) + 8) 64) =
      cbcC s₀.mem (s₀.gpr .a3) (4 * g + k) := by
    rw [← stateAt_wBlk]; exact ecbInv_orig hd (Nat.le_refl _) hkn
  have hv : wBlk (s₃.gpr .t2) (s₇.gpr .t2) = cfbD R w s₀.mem (s₀.gpr .a3) iv (4 * g + k) := by
    rw [x₃, x₇, wBlk_xor, hC]
    show vxor _ (wBlk (Q s k) (Q s (k + 4))) = _
    rw [← regBlock_wBlk, hblk k hkm (Nat.le_refl _)]
  have st := ecbInv_step (v₁ := s₃.gpr .t2) (v₂ := s₇.gpr .t2) (by omega) hkn
    (ecbInv_frame (slot2_frame s.mem b (j := stLo) (by decide)
      (s.mem.readW (s₀.gpr .a3 + BitVec.ofNat 64 (16 * (4 * g + k))) 64)
      (s.mem.readW (s₀.gpr .a3 + BitVec.ofNat 64 (16 * (4 * g + k)) + 8) 64)) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hs.dScr (by decide)) hn hd) (wBlk_bytes hv)
  have o₈' : ∀ r, r ≠ .t2 → r ≠ t0 → r ≠ t1 → s₈.gpr r = s.gpr r := fun r h h0 h1 => by
    rw [o₈ _ h0 h1, o₇ _ h h0 h1]
  have hQ : ∀ c, regBlock (Q s₈) c = regBlock (Q s) c := fun c => by
    rw [regBlock_wBlk, regBlock_wBlk]
    show wBlk (s₈.gpr (q c)) (s₈.gpr (q (c + 4))) = wBlk (s.gpr (q c)) (s.gpr (q (c + 4)))
    rw [o₈' _ (q_neW _).2.2.1 (q_neW _).1 (q_neW _).2.1, o₈' _ (q_neW _).2.2.1 (q_neW _).1 (q_neW _).2.1]
  refine ⟨⟨fun r h1 _ => o₈' r (fun e => h1 (e ▸ by decide)) (fun e => h1 (e ▸ by decide))
      (fun e => h1 (e ▸ by decide)),
    by rw [rd₈, u₇.rd, u₆.rd, rd₅, rd₄, u₃.rd, u₂.rd, rd₁],
    by rw [wr₈, u₇.wr, u₆.wr, wr₅, wr₄, u₃.wr, u₂.wr, wr₁],
    by rw [sp₈, u₇.sp, u₆.sp, sp₅, sp₄, u₃.sp, u₂.sp, sp₁], ?_⟩, ?_, ?_, fun c hc hkc => ?_⟩
  · rw [hm₈]
    exact ((wSlot_frame _ (by decide) (by decide) _).trans (wSlot_frame _ (by decide) (by decide) _)).trans
      (wData_frame st.2)
  · rw [hm₈]; exact st.1
  · rw [hm₈, slotBlk_frame st.2 (by decide) (hs.slot_data (by decide)), slot2_self _ _ (by decide), hC,
      show 4 * g + (k + 1) = 4 * g + k + 1 by omega]
    rfl
  · rw [hQ]; exact hblk c hc (by omega)

end Steps

/-! ## The mode -/

/-- CFB128 decryption as a mode of `wide`. -/
theorem cfb_ok (s₀ : State) :
    WideOk s₀ cfbLoad cfbStore Spec.Aes.cipher
      (cfbL s₀.mem (s₀.gpr .a3) (Spec.Aes.stateAt s₀.mem (s₀.gpr .a2)) (s₀.gpr .a1).toNat
        (Spec.Aes.bytesAt s₀.mem (s₀.gpr .a0) (16 * ((s₀.gpr .a1).toNat + 1))) (s₀.gpr .a4).toNat)
      (cfbS s₀.mem (s₀.gpr .a3) (Spec.Aes.stateAt s₀.mem (s₀.gpr .a2)) (s₀.gpr .a1).toNat
        (Spec.Aes.bytesAt s₀.mem (s₀.gpr .a0) (16 * ((s₀.gpr .a1).toNat + 1))) (s₀.gpr .a4).toNat)
      (cfbD (s₀.gpr .a1).toNat (Spec.Aes.bytesAt s₀.mem (s₀.gpr .a0) (16 * ((s₀.gpr .a1).toNat + 1)))
        s₀.mem (s₀.gpr .a3) (Spec.Aes.stateAt s₀.mem (s₀.gpr .a2)))
      (cbcP s₀.mem (s₀.gpr .a3) (Spec.Aes.stateAt s₀.mem (s₀.gpr .a2)) (s₀.gpr .a4).toNat) where
  init hs m Q hf hst :=
    ⟨ecbInv_frame (m := s₀.mem) hf (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hs.sep) hs.n16 fun i hi => by simp,
      hst, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  load hs _ _ hk hkn s hb hl := cfbLoad_ok hs hk hkn hb hl
  crypt := fun {s₉ X b} hs g m m' Q Q' hg hl hf hin => by
    obtain ⟨hd, hst, hblk⟩ := hl
    refine ⟨by rw [Nat.add_zero]; exact ecbInv_frame hf (by simpa using hs.d320) hs.n16 hd,
      by rw [Nat.add_zero, slotBlk_frame hf (by decide) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint_base b (by decide) (by decide)]; exact hst, fun c hc _ => ?_⟩
    rw [regBlock_of_inRel hin (by omega), hblk c hc]
  store hs _ _ hk hkn s hb hl := cfbStore_ok hs hk hkn hb hl
  next _ g m Q _ hl := by
    obtain ⟨hd, hst, -⟩ := hl
    exact ⟨by rw [show 4 * (g + 1) = 4 * g + 4 by omega]; exact hd,
      by rw [show 4 * (g + 1) = 4 * g + 4 by omega]; exact hst, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  done _ g m Q hg _ hl := by
    obtain ⟨hd, hst, -⟩ := hl
    rw [show 4 * g + ((s₀.gpr .a4).toNat - 4 * g) = (s₀.gpr .a4).toNat by omega] at hd hst
    exact ⟨hd, hst⟩

theorem cfbDecWide_correct {s₀ : State} (hp : (blockKRISCV64 (AesCfb.cfbMode false)).pre s₀) :
    WP isa cfbDecWide s₀ fun s' =>
      (∀ r ∈ RISCV64.preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
        (blockKRISCV64 (AesCfb.cfbMode false)).post s₀ s' := by
  unfold cfbDecWide
  exact wide_correct _ encrypt4_cryptOk hp (cfb_ok s₀)
    (by rw [AesCbc.bytesAt_toList]; exact cfb_out _ _ _ _ _ _)
    (by rw [AesCbc.bytesAt_toList]; exact cfb_chain _ _ _ _ _ _)

theorem cfbDecWide_ct : ConstantTime isa (blockKRISCV64 (AesCfb.cfbMode false)).pre
    (blockKRISCV64 (AesCfb.cfbMode false)).pub cfbDecWide :=
  wide_ct _ (by taint_decide)

theorem cfbDecWide_k :
    AesCbc.RISCV64.ChainK true (16 * ·) (blockKRISCV64 (AesCfb.cfbMode false)) cfbDecWide :=
  blockK_k cfbDecWide_correct cfbDecWide_ct rfl

end VG.Proof.Aes.RISCV64
