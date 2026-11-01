module

public import VerifiedGarbage.Proof.Aes.RISCV64.Wide
public import VerifiedGarbage.Proof.AesCbc.Spec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Aes.RISCV64.Wide
meta import VerifiedGarbage.Proof.AesCbc.Spec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.TCB.RISCV64.Target

-- separate module: CBC decryption's instance of `wide`, which only AES-CBC's `Verified` imports,
-- apart from the generic proof (`Wide.lean`) that the other modes' instances import too.

/-!
# AES-CBC decryption on RISC-V, four blocks at a time

`cbcDecWide` (`Impl/Aes/RISCV64/Wide.lean`) is `wide cbcLoad cbcStore
decrypt4`: `cbcLoad k` loads the ciphertext block `Cⱼ` (`cbcC`) into the
state registers and copies it to its slots (`blkLo k`), `decrypt4`
deciphers the four, and `cbcStore k` stores `Pⱼ = Cⱼ₋₁ ⊕ CIPH⁻¹_K(Cⱼ)`
(`cbcF`), with `Cⱼ₋₁` (`cbcP`, the IV for the first) from the state's
slots (`stLo`) for the group's first block and from the copy of the block
before for the others, and makes `Cⱼ` the state. Its invariants (`cbcL`,
`cbcS`): the data is `cbcF`'s up to the blocks stored, the state's slots
hold `Cⱼ₋₁` of the next block, and the group's slots and registers its
ciphertext blocks, deciphered once `decrypt4` has run. `cbc_ok` is its
`WideOk`, `cbc_out` and `cbc_chain` that `cbcF` and `cbcP` are CBC
decryption's (`Spec.Cbc.decrypt`, and its last ciphertext block), and
`cbcDecWide_k` states it as a chain to call (`AesCbc.RISCV64.ChainK`).
-/

@[expose] public section

namespace VG.Proof.Aes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.RISCV64.Steps VG.Bitslice VG.Impl.Aes.RISCV64
  VG.Impl.Words.RISCV64 VG.Proof.Aes

/-! ## The blocks -/

/-- The ciphertext block `Cⱼ` at `D` in `m₀`. -/
abbrev cbcC (m₀ : Mem) (D : Addr) (j : Nat) : Spec.Aes.State :=
  Spec.Aes.stateAt m₀ (D + BitVec.ofNat 64 (16 * j))

/-- `Cⱼ₋₁`: the IV for the first block. -/
def cbcP (m₀ : Mem) (D : Addr) (iv : Spec.Aes.State) : Nat → Spec.Aes.State
  | 0 => iv
  | j + 1 => cbcC m₀ D j

/-- The plaintext block `Pⱼ = Cⱼ₋₁ ⊕ CIPH⁻¹_K(Cⱼ)`. -/
abbrev cbcF (R : Nat) (w : List Byte) (m₀ : Mem) (D : Addr) (iv : Spec.Aes.State) (j : Nat) :
    Spec.Aes.State :=
  vxor (cbcP m₀ D iv j) (Spec.Aes.invCipher R w (cbcC m₀ D j))

/-- CBC decryption: block `j` from block `j` and the one before (the IV). -/
theorem decrypt_eq (ciph : Spec.Cbc.Cipher) : ∀ (xs : List (List Byte)) (iv : List Byte),
    Spec.Cbc.decrypt ciph iv xs =
      (List.range xs.length).map fun j => Spec.Cbc.xor (ciph (xs.getD j [])) ((iv :: xs).getD j [])
  | [], _ => rfl
  | x :: xs, iv => by
    rw [Spec.Cbc.decrypt, decrypt_eq ciph xs x, List.length_cons, List.range_succ_eq_map, List.map_cons,
      List.map_map]
    simp only [List.getD_cons_zero, List.getD_cons_succ, Function.comp_def]

theorem aesInvWith_toList (R : Nat) (w : List Byte) (x : Spec.Aes.State) :
    Spec.Cbc.aesInvWith R w x.toList = (Spec.Aes.invCipher R w x).toList := by
  rw [Spec.Cbc.aesInvWith, ofFn_toList]

theorem blocksAt_cbcC (m : Mem) (D : Addr) (n : Nat) :
    Spec.Cbc.blocksAt m D n = (List.range n).map fun j => (cbcC m D j).toList := by
  simp only [Spec.Cbc.blocksAt, AesCbc.bytesAt_toList]

theorem cbc_out (R : Nat) (w : List Byte) (m : Mem) (D : Addr) (iv : Spec.Aes.State) (n : Nat) :
    (AesCbc.cbcMode false).out R w iv.toList (Spec.Cbc.blocksAt m D n) =
      (List.range n).map fun j => (cbcF R w m D iv j).toList := by
  simp only [AesCbc.cbcMode_out, AesCbc.cbc, AesCbc.ciphOf, Bool.false_eq_true, ↓reduceIte]
  rw [decrypt_eq, show (Spec.Cbc.blocksAt m D n).length = n by simp [Spec.Cbc.blocksAt]]
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
  rw [e₁, e₂, aesInvWith_toList, cbcXor_comm, ← toList_vxor]

theorem cbc_chain (R : Nat) (w : List Byte) (m : Mem) (D : Addr) (iv : Spec.Aes.State) (n : Nat) :
    (AesCbc.cbcMode false).chain R w iv.toList (Spec.Cbc.blocksAt m D n) = (cbcP m D iv n).toList := by
  rw [AesCbc.cbcMode_chain, AesCbc.cts, ite_eq_right Bool.false_ne_true, blocksAt_cbcC]
  exact next_range (fun j => (cbcP m D iv j).toList) n

/-! ## The invariants -/

/-- The loads of group `g`, after `k` of them: the data `cbcF`'s up to
the group, the state's slots `Cⱼ₋₁` of its first block, and the first `k`
of its ciphertext blocks in their slots and registers. -/
def cbcL (m₀ : Mem) (D : Addr) (iv : Spec.Aes.State) (R : Nat) (w : List Byte) (n : Nat) (b : Addr)
    (g k : Nat) (m : Mem) (Q : Nat → BitVec 64) : Prop :=
  EcbInv m₀ m D n (4 * g) (cbcF R w m₀ D iv) ∧ slotBlk m b stLo = cbcP m₀ D iv (4 * g) ∧
    ∀ c < k, slotBlk m b (blkLo c) = cbcC m₀ D (4 * g + c) ∧ regBlock Q c = cbcC m₀ D (4 * g + c)

/-- The stores of group `g`, after `k` of them: the data `cbcF`'s up to
them, the state's slots `Cⱼ₋₁` of the next block, the group's ciphertext
blocks in their slots, and the others deciphered in the registers. -/
def cbcS (m₀ : Mem) (D : Addr) (iv : Spec.Aes.State) (R : Nat) (w : List Byte) (n : Nat) (b : Addr)
    (g k : Nat) (m : Mem) (Q : Nat → BitVec 64) : Prop :=
  EcbInv m₀ m D n (4 * g + k) (cbcF R w m₀ D iv) ∧ slotBlk m b stLo = cbcP m₀ D iv (4 * g + k) ∧
    ∀ c < min 4 (n - 4 * g), slotBlk m b (blkLo c) = cbcC m₀ D (4 * g + c) ∧
      (k ≤ c → regBlock Q c = Spec.Aes.invCipher R w (cbcC m₀ D (4 * g + c)))

theorem q_pairs : ∀ c < 4, ∀ k < 4, c ≠ k → q c ≠ q k ∧ q c ≠ q (k + 4) ∧ q (c + 4) ≠ q k ∧
    q (c + 4) ≠ q (k + 4) := by decide

section Steps

variable {s₀ s₉ : State} {X b : Addr} (hs : FSetup true (16 * ·) s₀ s₉ X b) {iv : Spec.Aes.State}
  {R : Nat} {w : List Byte}
include hs

/-- `Cⱼ` of block `k` loaded, and copied to its slots. -/
theorem cbcLoad_ok {g k : Nat} (hk : k < 4) (hkn : 4 * g + k < (s₀.gpr .a4).toNat) {s : State}
    (hb : WB s₀ s₉ b g s) (hl : cbcL s₀.mem (s₀.gpr .a3) iv R w (s₀.gpr .a4).toNat b g k s.mem (Q s)) :
    WP isa (.block (cbcLoad k)) s fun s' =>
      Foot s₀ b s s' ∧ cbcL s₀.mem (s₀.gpr .a3) iv R w (s₀.gpr .a4).toNat b g (k + 1) s'.mem (Q s') := by
  obtain ⟨hd, hst, hblk⟩ := hl
  have hn := hs.n16
  have hdat := hb.dat hs
  obtain ⟨n1, n2, n3, -, -, n6, n7, n8, n9, n10, n11⟩ := q_c4 k hk
  have hbl : blkLo k + 1 < 88 := by unfold blkLo; omega
  unfold cbcLoad loadBlock
  repeat rw [WP.block_append_iff (M := isa)]
  refine WP.mono (data_ld (off := 16 * k) hb.a3 (List.mem_append_right _ hdat) hn (by omega) (by omega)
    ⟨n1, n8, n9⟩) fun s₁ ⟨e₁, o₁, m₁, rd₁, wr₁, sp₁⟩ => ?_
  refine WP.mono (data_ld (D := s₀.gpr .a3) (g := g) (n := (s₀.gpr .a4).toNat) (off := 16 * k + 8) (by rw [o₁ _ (Ne.symm n1) (by decide) (by decide)]; exact hb.a3)
    (by rw [rd₁, wr₁]; exact List.mem_append_right _ hdat) hn (by omega) (by omega) ⟨n2, n10, n11⟩)
    fun s₂ ⟨e₂, o₂, m₂, rd₂, wr₂, sp₂⟩ => ?_
  have g₂ : ∀ r, r ≠ q k → r ≠ q (k + 4) → r ≠ t0 → r ≠ t1 → s₂.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 => by rw [o₂ r h2 h3 h4, o₁ r h1 h3 h4]
  have hb₂ : s₂.gpr sb = b := by
    rw [g₂ sb (Ne.symm n6) (Ne.symm n7) (by decide) (by decide)]; exact hb.base hs
  have hscr₂ : Scr s₂ X 2048 := (hb.scr hs).congr (by rw [wr₂, wr₁]) (by rw [hb₂, hb.base hs])
  refine slot_st hscr₂ hb₂ (by omega) fun s₃ u₃ => ?_
  refine slot_st (hscr₂.congr u₃.wr (by rw [u₃.gpr])) (by rw [u₃.gpr, hb₂]) (by omega)
    fun s₄ u₄ => WP.block_nil ?_
  have m₄ : s₄.mem = (s.mem.writeW (b + BitVec.ofNat 64 (8 * blkLo k)) (s₂.gpr (q k))).writeW
      (b + BitVec.ofNat 64 (8 * (blkLo k + 1))) (s₂.gpr (q (k + 4))) := by
    rw [u₄.mem, u₃.mem, u₃.gpr, m₂, m₁]
  have hQ : Q s₄ = Q s₂ := (Q_mupd u₄).trans (Q_mupd u₃)
  have hv : wBlk (s₂.gpr (q k)) (s₂.gpr (q (k + 4))) = cbcC s₀.mem (s₀.gpr .a3) (4 * g + k) := by
    rw [o₂ _ n3 n8 n9, e₁, e₂, m₁, show 64 * g + 16 * k = 16 * (4 * g + k) by omega,
      show 64 * g + (16 * k + 8) = 16 * (4 * g + k) + 8 by omega, add_off8, ← stateAt_wBlk]
    exact ecbInv_orig hd (by omega) hkn
  refine ⟨⟨fun r h1 h2 => ?_, by rw [u₄.rd, u₃.rd, rd₂, rd₁], by rw [u₄.wr, u₃.wr, wr₂, wr₁],
    by rw [u₄.sp, u₃.sp, sp₂, sp₁], ?_⟩, ?_, ?_, fun c hc => ?_⟩
  · rw [u₄.gpr, u₃.gpr]
    exact g₂ r (fun e => h1 (e ▸ q_mem k (by omega))) (fun e => h1 (e ▸ q_mem (k + 4) (by omega)))
      (fun e => h1 (e ▸ by decide)) (fun e => h1 (e ▸ by decide))
  · rw [m₄]
    exact (wSlot_frame _ (by unfold blkLo; omega) (by omega) _).trans
      (wSlot_frame _ (by unfold blkLo; omega) (by omega) _)
  · rw [m₄]
    exact ecbInv_frame (slot2_frame _ _ (by omega) _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hs.dScr (by omega)) hn hd
  · rw [m₄, slot2_other _ _ (by omega) (by decide) (by unfold blkLo stLo; omega)]; exact hst
  · by_cases hck : c = k
    · subst hck
      refine ⟨by rw [m₄, slot2_self _ _ (by omega)]; exact hv, ?_⟩
      rw [regBlock_wBlk, hQ]; exact hv
    · have hc' : c < k := by omega
      obtain ⟨d1, d2, d3, d4⟩ := q_pairs c (by omega) k hk hck
      obtain ⟨-, -, -, -, -, -, -, d5, d6, d7, d8⟩ := q_c4 c (by omega)
      refine ⟨?_, ?_⟩
      · rw [m₄, slot2_other _ _ (by omega) (by unfold blkLo; omega) (by unfold blkLo; omega)]
        exact (hblk c hc').1
      rw [regBlock_wBlk, hQ]
      show wBlk (s₂.gpr (q c)) (s₂.gpr (q (c + 4))) = _
      rw [g₂ _ d1 d2 d5 d6, g₂ _ d3 d4 d7 d8, ← (hblk c hc').2, regBlock_wBlk]

omit hs in
/-- The slots of `Cⱼ₋₁` for block `k`: the state's for the first. -/
theorem cbcPrev_slot {g k : Nat} {m : Mem} (hk : k < 4)
    (hst : slotBlk m b stLo = cbcP s₀.mem (s₀.gpr .a3) iv (4 * g + k))
    (hblk : ∀ c < k, slotBlk m b (blkLo c) = cbcC s₀.mem (s₀.gpr .a3) (4 * g + c)) :
    slotBlk m b (cbcPrev k) = cbcP s₀.mem (s₀.gpr .a3) iv (4 * g + k) := by
  unfold cbcPrev
  by_cases h0 : k = 0
  · rw [ite_eq_left h0]; exact hst
  · rw [ite_eq_right h0, hblk (k - 1) (by omega), show 4 * g + k = 4 * g + (k - 1) + 1 by omega]; rfl

/-- `Pⱼ` of block `k` stored, and `Cⱼ` the state. -/
theorem cbcStore_ok {g k : Nat} (hk : k < 4) (hkn : 4 * g + k < (s₀.gpr .a4).toNat) {s : State}
    (hb : WB s₀ s₉ b g s) (hl : cbcS s₀.mem (s₀.gpr .a3) iv R w (s₀.gpr .a4).toNat b g k s.mem (Q s)) :
    WP isa (.block (cbcStore k)) s fun s' =>
      Foot s₀ b s s' ∧ cbcS s₀.mem (s₀.gpr .a3) iv R w (s₀.gpr .a4).toNat b g (k + 1) s'.mem (Q s') := by
  obtain ⟨hd, hst, hblk⟩ := hl
  have hn := hs.n16
  have hdat := hb.dat hs
  have hscr := hb.scr hs
  have hbase := hb.base hs
  have hkm : k < min 4 ((s₀.gpr .a4).toNat - 4 * g) := by omega
  have hpk : cbcPrev k + 1 < 88 := by unfold cbcPrev blkLo stLo; split <;> omega
  have hpk' : 78 ≤ cbcPrev k := by unfold cbcPrev blkLo stLo; split <;> omega
  have hbl : blkLo k + 1 < 88 := by unfold blkLo; omega
  have hP : slotBlk s.mem b (cbcPrev k) = cbcP s₀.mem (s₀.gpr .a3) iv (4 * g + k) :=
    cbcPrev_slot (s₀ := s₀) hk hst fun c hc => (hblk c (by omega)).1
  obtain ⟨-, -, -, -, -, -, -, n8, n9, n10, n11⟩ := q_c4 k hk
  -- Every state until the end: only `t2`, `t0` and `t1` and the memory change.
  have sc : ∀ {t : State}, t.wr = s.wr → t.gpr sb = s.gpr sb → Scr t X 2048 ∧ t.gpr sb = b :=
    fun hw hg => ⟨hscr.congr hw hg, hg.trans hbase⟩
  unfold cbcStore
  repeat rw [WP.block_append_iff (M := isa)]
  refine slot_ld hscr hbase (by omega) fun s₁ u₁ => wp_xor fun s₂ u₂ => WP.block_nil ?_
  have o₂ : ∀ r, r ≠ .t2 → s₂.gpr r = s.gpr r := fun r h => by rw [u₂.other _ h, u₁.other _ h]
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  have x₂ : s₂.gpr .t2 = s.mem.readW (b + BitVec.ofNat 64 (8 * cbcPrev k)) 64 ^^^ s.gpr (q k) := by
    rw [u₂.gpr, u₁.gpr, u₁.other _ (q_neW k).2.2.1]
  refine WP.mono (data_st (D := s₀.gpr .a3) (g := g) (n := (s₀.gpr .a4).toNat) (off := 16 * k) (by rw [o₂ _ (by decide)]; exact hb.a3)
    (by rw [u₂.wr, u₁.wr]; exact hdat) hn (by omega) (by omega) (by decide))
    fun s₃ ⟨m₃, o₃, rd₃, wr₃, sp₃⟩ => ?_
  obtain ⟨scr₃, b₃⟩ := sc (t := s₃) (by rw [wr₃, u₂.wr, u₁.wr]) (by
    rw [o₃ _ (by decide) (by decide), o₂ _ (by decide)])
  refine slot_ld scr₃ b₃ (by omega) fun s₄ u₄ => wp_xor fun s₅ u₅ => WP.block_nil ?_
  have o₅ : ∀ r, r ≠ .t2 → r ≠ t0 → r ≠ t1 → s₅.gpr r = s.gpr r := fun r h h0 h1 => by
    rw [u₅.other _ h, u₄.other _ h, o₃ _ h0 h1, o₂ _ h]
  have m₅ : s₅.mem = s₃.mem := by rw [u₅.mem, u₄.mem]
  have x₅ : s₅.gpr .t2 = s₃.mem.readW (b + BitVec.ofNat 64 (8 * (cbcPrev k + 1))) 64 ^^^ s.gpr (q (k + 4)) := by
    rw [u₅.gpr, u₄.gpr, u₄.other _ (q_neW _).2.2.1, o₃ _ n10 n11, o₂ _ (q_neW _).2.2.1]
  refine WP.mono (data_st (D := s₀.gpr .a3) (g := g) (n := (s₀.gpr .a4).toNat) (off := 16 * k + 8) (by rw [o₅ _ (by decide) (by decide) (by decide)]; exact hb.a3)
    (by rw [u₅.wr, u₄.wr, wr₃, u₂.wr, u₁.wr]; exact hdat) hn (by omega) (by omega) (by decide))
    fun s₆ ⟨m₆, o₆, rd₆, wr₆, sp₆⟩ => ?_
  obtain ⟨scr₆, b₆⟩ := sc (t := s₆) (by rw [wr₆, u₅.wr, u₄.wr, wr₃, u₂.wr, u₁.wr]) (by
    rw [o₆ _ (by decide) (by decide), o₅ _ (by decide) (by decide) (by decide)])
  refine slot_ld scr₆ b₆ (by omega) fun s₇ u₇ => ?_
  refine slot_st (scr₆.congr u₇.wr (by rw [u₇.other _ (by decide)])) (by rw [u₇.other _ (by decide), b₆])
    (by decide) fun s₈ u₈ => ?_
  refine slot_ld (scr₆.congr (by rw [u₈.wr, u₇.wr]) (by rw [u₈.gpr, u₇.other _ (by decide)]))
    (by rw [u₈.gpr, u₇.other _ (by decide), b₆]) (by omega) fun s₉' u₉ => ?_
  refine slot_st (scr₆.congr (by rw [u₉.wr, u₈.wr, u₇.wr]) (by rw [u₉.other _ (by decide), u₈.gpr,
    u₇.other _ (by decide)])) (by rw [u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), b₆])
    (by decide) fun s₁₀ u₁₀ => WP.block_nil ?_
  -- The memory: the data block, then the state's slots.
  let A := s₀.gpr .a3 + BitVec.ofNat 64 (16 * (4 * g + k))
  have eA : s₀.gpr .a3 + BitVec.ofNat 64 (64 * g + 16 * k) = A := by
    rw [show 64 * g + 16 * k = 16 * (4 * g + k) by omega]
  have eA8 : s₀.gpr .a3 + BitVec.ofNat 64 (64 * g + (16 * k + 8)) = A + 8 := by
    rw [show 64 * g + (16 * k + 8) = 16 * (4 * g + k) + 8 by omega, add_off8]
  have fd₃ : Frame [⟨s₀.gpr .a3, 16 * (s₀.gpr .a4).toNat⟩] s.mem s₃.mem := by
    rw [m₃, m₂, eA]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega) (by omega))
  have slot₃ : ∀ j, j < 88 → s₃.mem.readW (b + BitVec.ofNat 64 (8 * j)) 64 =
      s.mem.readW (b + BitVec.ofNat 64 (8 * j)) 64 := fun j hj =>
    fd₃.readW (Region.contains_self _ _) (hs.slotW_data hj) (by decide)
  have hm₆ : s₆.mem = (s.mem.writeW A (s₂.gpr .t2)).writeW (A + 8) (s₅.gpr .t2) := by
    rw [m₆, m₅, m₃, m₂, eA, eA8]
  have hv : wBlk (s₂.gpr .t2) (s₅.gpr .t2) = cbcF R w s₀.mem (s₀.gpr .a3) iv (4 * g + k) := by
    rw [x₂, x₅, slot₃ _ hpk, wBlk_xor]
    show vxor (slotBlk s.mem b (cbcPrev k)) (wBlk (Q s k) (Q s (k + 4))) = _
    rw [hP, ← regBlock_wBlk, (hblk k hkm).2 (Nat.le_refl _)]
  have st := ecbInv_step (v₁ := s₂.gpr .t2) (v₂ := s₅.gpr .t2) (by omega) hkn hd (wBlk_bytes hv)
  rw [← hm₆] at st
  have slot₆ : ∀ j, j < 88 → s₆.mem.readW (b + BitVec.ofNat 64 (8 * j)) 64 =
      s.mem.readW (b + BitVec.ofNat 64 (8 * j)) 64 := fun j hj =>
    (st.2.readW (Region.contains_self _ _) (hs.slotW_data hj) (by decide))
  have hm₁₀ : s₁₀.mem = (s₆.mem.writeW (b + BitVec.ofNat 64 (8 * stLo))
      (s₆.mem.readW (b + BitVec.ofNat 64 (8 * blkLo k)) 64)).writeW (b + BitVec.ofNat 64 (8 * (stLo + 1)))
      (s₆.mem.readW (b + BitVec.ofNat 64 (8 * (blkLo k + 1))) 64) := by
    rw [u₁₀.mem, u₉.gpr, u₉.mem, u₈.mem, u₇.gpr, u₇.mem,
      slot_writeW_ne _ _ (by decide) (by omega) (by unfold blkLo stLo; omega)]
  have o₁₀ : ∀ r, r ≠ .t2 → r ≠ t0 → r ≠ t1 → s₁₀.gpr r = s.gpr r := fun r h h0 h1 => by
    rw [u₁₀.gpr, u₉.other _ h, u₈.gpr, u₇.other _ h, o₆ _ h0 h1, o₅ _ h h0 h1]
  have hQ : ∀ c, regBlock (Q s₁₀) c = regBlock (Q s) c := fun c => by
    rw [regBlock_wBlk, regBlock_wBlk]
    show wBlk (s₁₀.gpr (q c)) (s₁₀.gpr (q (c + 4))) = wBlk (s.gpr (q c)) (s.gpr (q (c + 4)))
    rw [o₁₀ _ (q_neW _).2.2.1 (q_neW _).1 (q_neW _).2.1, o₁₀ _ (q_neW _).2.2.1 (q_neW _).1 (q_neW _).2.1]
  have hd₆ : ∀ c, c < 4 → slotBlk s₆.mem b (blkLo c) = slotBlk s.mem b (blkLo c) := fun c hc => by
    unfold slotBlk; rw [slot₆ _ (by unfold blkLo; omega), slot₆ _ (by unfold blkLo; omega)]
  refine ⟨⟨fun r h1 h2 => o₁₀ r (fun e => h1 (e ▸ by decide)) (fun e => h1 (e ▸ by decide))
      (fun e => h1 (e ▸ by decide)),
    by rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, rd₆, u₅.rd, u₄.rd, rd₃, u₂.rd, u₁.rd],
    by rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, wr₆, u₅.wr, u₄.wr, wr₃, u₂.wr, u₁.wr],
    by rw [u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, sp₆, u₅.sp, u₄.sp, sp₃, u₂.sp, u₁.sp], ?_⟩, ?_, ?_, fun c hc => ?_⟩
  · rw [hm₁₀]
    exact ((wData_frame st.2).trans (wSlot_frame _ (by decide) (by decide) _)).trans
      (wSlot_frame _ (by decide) (by decide) _)
  · rw [hm₁₀]
    exact ecbInv_frame (slot2_frame _ _ (by decide) _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hs.dScr (by decide)) hn st.1
  · rw [hm₁₀, slot2_self _ _ (by decide)]
    show slotBlk s₆.mem b (blkLo k) = _
    rw [hd₆ k hk, (hblk k hkm).1]; rfl
  · refine ⟨?_, fun h => by rw [hQ]; exact (hblk c hc).2 (by omega)⟩
    rw [hm₁₀, slot2_other _ _ (by decide) (by unfold blkLo; omega) (by unfold blkLo stLo; omega),
      hd₆ c (by omega)]
    exact (hblk c hc).1

end Steps

/-! ## The mode -/

/-- CBC decryption as a mode of `wide`. -/
theorem cbc_ok (s₀ : State) :
    WideOk s₀ cbcLoad cbcStore Spec.Aes.invCipher
      (cbcL s₀.mem (s₀.gpr .a3) (Spec.Aes.stateAt s₀.mem (s₀.gpr .a2)) (s₀.gpr .a1).toNat
        (Spec.Aes.bytesAt s₀.mem (s₀.gpr .a0) (16 * ((s₀.gpr .a1).toNat + 1))) (s₀.gpr .a4).toNat)
      (cbcS s₀.mem (s₀.gpr .a3) (Spec.Aes.stateAt s₀.mem (s₀.gpr .a2)) (s₀.gpr .a1).toNat
        (Spec.Aes.bytesAt s₀.mem (s₀.gpr .a0) (16 * ((s₀.gpr .a1).toNat + 1))) (s₀.gpr .a4).toNat)
      (cbcF (s₀.gpr .a1).toNat (Spec.Aes.bytesAt s₀.mem (s₀.gpr .a0) (16 * ((s₀.gpr .a1).toNat + 1)))
        s₀.mem (s₀.gpr .a3) (Spec.Aes.stateAt s₀.mem (s₀.gpr .a2)))
      (cbcP s₀.mem (s₀.gpr .a3) (Spec.Aes.stateAt s₀.mem (s₀.gpr .a2)) (s₀.gpr .a4).toNat) where
  init hs m Q hf hst :=
    ⟨ecbInv_frame (m := s₀.mem) hf (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hs.sep) hs.n16 fun i hi => by simp,
      hst, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  load hs _ _ hk hkn s hb hl := cbcLoad_ok hs hk hkn hb hl
  crypt := fun {s₉ X b} hs g m m' Q Q' hg hl hf hin => by
    obtain ⟨hd, hst, hblk⟩ := hl
    refine ⟨by rw [Nat.add_zero]; exact ecbInv_frame hf (by simpa using hs.d320) hs.n16 hd,
      by rw [Nat.add_zero, slotBlk_frame hf (by decide) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint_base b (by decide) (by decide)]; exact hst, fun c hc => ⟨?_, fun _ => ?_⟩⟩
    · rw [slotBlk_frame hf (by unfold blkLo; omega) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint_base b (by unfold blkLo; omega) (by unfold blkLo; omega)]
      exact (hblk c hc).1
    · rw [regBlock_of_inRel hin (by omega), (hblk c hc).2]
  store hs _ _ hk hkn s hb hl := cbcStore_ok hs hk hkn hb hl
  next _ g m Q _ hl := by
    obtain ⟨hd, hst, -⟩ := hl
    exact ⟨by rw [show 4 * (g + 1) = 4 * g + 4 by omega]; exact hd,
      by rw [show 4 * (g + 1) = 4 * g + 4 by omega]; exact hst, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  done _ g m Q hg _ hl := by
    obtain ⟨hd, hst, -⟩ := hl
    rw [show 4 * g + ((s₀.gpr .a4).toNat - 4 * g) = (s₀.gpr .a4).toNat by omega] at hd hst
    exact ⟨hd, hst⟩

theorem cbcDecWide_correct {s₀ : State} (hp : (blockKRISCV64 (AesCbc.cbcMode false)).pre s₀) :
    WP isa cbcDecWide s₀ fun s' =>
      (∀ r ∈ RISCV64.preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
        (blockKRISCV64 (AesCbc.cbcMode false)).post s₀ s' := by
  unfold cbcDecWide
  exact wide_correct _ decrypt4_cryptOk hp (cbc_ok s₀)
    (by rw [AesCbc.bytesAt_toList]; exact cbc_out _ _ _ _ _ _)
    (by rw [AesCbc.bytesAt_toList]; exact cbc_chain _ _ _ _ _ _)

theorem cbcDecWide_ct : ConstantTime isa (blockKRISCV64 (AesCbc.cbcMode false)).pre
    (blockKRISCV64 (AesCbc.cbcMode false)).pub cbcDecWide :=
  wide_ct _ (by taint_decide)

theorem cbcDecWide_k :
    AesCbc.RISCV64.ChainK true (16 * ·) (blockKRISCV64 (AesCbc.cbcMode false)) cbcDecWide :=
  blockK_k cbcDecWide_correct cbcDecWide_ct rfl

end VG.Proof.Aes.RISCV64
