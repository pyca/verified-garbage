module

public import VerifiedGarbage.Proof.Aes.RISCV64.Wide
public import VerifiedGarbage.Proof.AesXts.Spec
import VerifiedGarbage.Proof.AesXts.Alpha
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Aes.RISCV64.Wide
meta import VerifiedGarbage.Proof.AesXts.Spec
meta import VerifiedGarbage.Proof.AesXts.Alpha
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.TCB.RISCV64.Target

-- separate module: XTS's instance of `wide`, which only XTS-AES's `Verified` imports, apart from
-- the generic proof (`Wide.lean`) that the other modes' instances import too.

/-!
# XTS-AES on RISC-V, four blocks at a time

`xtsEncWide` and `xtsDecWide` (`Impl/Aes/RISCV64/Wide.lean`) are
`wide xtsLoad xtsStore encrypt4` and `… decrypt4`: `xtsLoad k` copies the
tweak `Tⱼ` (`xtsT`, `T ⊗ αʲ`) from the state's slots (`stLo`) to block
`k`'s (`blkLo k`), puts `Pⱼ ⊕ Tⱼ` in the state registers, and multiplies the
tweak by `α` (`xtsMulA_ok`: `mulAlpha_words64` on the tweak's two
little-endian doublewords); `encrypt4` (`decrypt4`) enciphers (deciphers)
the four, and `xtsStore k` stores `Tⱼ ⊕ CIPH_K(Pⱼ ⊕ Tⱼ)` (`xtsF`). Their
invariants (`xtsL`, `xtsS`): the data is `xtsF`'s up to the blocks stored,
the state's slots hold the tweak of the next block to load, and the
group's slots and registers its tweaks and inputs, enciphered once the
cipher has run. `xts_ok` is its `WideOk`, `xts_out` and `xts_chain` that
`xtsF` and `xtsT` are XTS's (`Spec.Xts.crypt`, and the tweak after the
blocks), and `xtsEncWide_k`, `xtsDecWide_k` state them as chains to call
(`AesCbc.RISCV64.ChainK`).
-/

@[expose] public section

namespace VG.Proof.Aes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.RISCV64.Steps VG.Bitslice VG.Impl.Aes.RISCV64
  VG.Impl.Words.RISCV64 VG.Proof.Aes

/-! ## The tweaks and the blocks -/

theorem length_mulAlpha_step :
    ∀ (a : List Byte) (c : Bool), (Spec.Xts.mulAlpha.step a c).1.length = a.length
  | [], _ => rfl
  | _ :: rest, _ => by
    simp only [Spec.Xts.mulAlpha.step, List.length_cons, length_mulAlpha_step rest]

theorem length_mulAlpha (a : List Byte) : (Spec.Xts.mulAlpha a).length = a.length := by
  rw [← length_mulAlpha_step a false]
  unfold Spec.Xts.mulAlpha
  split <;> simp_all

/-- A block times `α`. -/
def mulAS (v : Spec.Aes.State) : Spec.Aes.State :=
  Vector.ofFn fun i => (Spec.Xts.mulAlpha v.toList).getD i.1 0

theorem toList_mulAS (v : Spec.Aes.State) : (mulAS v).toList = Spec.Xts.mulAlpha v.toList := by
  apply List.ext_getElem (by simp [mulAS, length_mulAlpha])
  intro i h₁ h₂
  simp [mulAS, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂]

/-- The tweak `T ⊗ αʲ` of block `j`, from `T = t`. -/
def xtsT (t : Spec.Aes.State) : Nat → Spec.Aes.State
  | 0 => t
  | j + 1 => mulAS (xtsT t j)

theorem xtsT_toList (t : Spec.Aes.State) : ∀ j, (xtsT t j).toList = Spec.Xts.next t.toList j
  | 0 => rfl
  | j + 1 => by rw [xtsT, toList_mulAS, xtsT_toList t j, AesXts.next_succ]

/-- The data block `Pⱼ` at `D` in `m₀`. -/
abbrev xtsC (m₀ : Mem) (D : Addr) (j : Nat) : Spec.Aes.State :=
  Spec.Aes.stateAt m₀ (D + BitVec.ofNat 64 (16 * j))

/-- The block `Tⱼ ⊕ f(Pⱼ ⊕ Tⱼ)`, for the block function `f`. -/
abbrev xtsF (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) (R : Nat) (w : List Byte)
    (m₀ : Mem) (D : Addr) (t : Spec.Aes.State) (j : Nat) : Spec.Aes.State :=
  vxor (xtsT t j) (f R w (vxor (xtsC m₀ D j) (xtsT t j)))

theorem tweaks_eq (t : List Byte) : ∀ n, Spec.Xts.tweaks t n = (List.range n).map (Spec.Xts.next t)
  | 0 => rfl
  | n + 1 => by rw [AesXts.tweaks_succ, tweaks_eq t n, List.range_succ, List.map_append]; rfl

theorem blocksAt_xtsC (m : Mem) (D : Addr) (n : Nat) :
    Spec.Cbc.blocksAt m D n = (List.range n).map fun j => (xtsC m D j).toList := by
  simp only [Spec.Cbc.blocksAt, AesCbc.bytesAt_toList]

theorem xts_out (enc : Bool) (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) (R : Nat)
    (w : List Byte) (hf : ∀ x : Spec.Aes.State, AesCbc.ciphOf enc R w x.toList = (f R w x).toList)
    (m : Mem) (D : Addr) (t : Spec.Aes.State) (n : Nat) :
    (AesXts.xtsMode enc).out R w t.toList (Spec.Cbc.blocksAt m D n) =
      (List.range n).map fun j => (xtsF f R w m D t j).toList := by
  rw [AesXts.xtsMode_out, Spec.Xts.crypt, blocksAt_xtsC, List.length_map, List.length_range, tweaks_eq,
    List.zipWith_map, List.zipWith_self]
  refine List.map_congr_left fun j _ => ?_
  rw [Spec.Xts.block, ← xtsT_toList, cbcXor_comm, AesCbc.xor_eq, ← toList_vxor, hf, toList_vxor,
    ← toList_vxor]

theorem xts_chain (enc : Bool) (R : Nat) (w : List Byte) (m : Mem) (D : Addr) (t : Spec.Aes.State)
    (n : Nat) : (AesXts.xtsMode enc).chain R w t.toList (Spec.Cbc.blocksAt m D n) = (xtsT t n).toList := by
  rw [AesXts.xtsMode_chain, xtsT_toList, show (Spec.Cbc.blocksAt m D n).length = n by
    simp [Spec.Cbc.blocksAt]]

/-! ## The tweak times `α` -/

theorem ushr63 (x : BitVec 64) : x >>> 63 = if x.msb then (1 : BitVec 64) else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.msb_eq_decide]
  have := x.isLt
  by_cases h : 2 ^ 63 ≤ x.toNat
  · rw [decide_eq_true h]; show _ = 1; omega
  · rw [decide_eq_false h]; show _ = 0; omega

theorem mask87 (b : Bool) :
    (BitVec.ofNat 64 0 - (if b then (1 : BitVec 64) else 0)) &&& BitVec.ofNat 64 0x87 =
      if b then (0x87 : BitVec 64) else 0 := by
  cases b <;> decide

theorem wp_and {is : List Instr} {s : State} {P : State → Prop} {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n &&& s.gpr m) → WP isa (.block is) s' P) :
    WP isa (.block (.logic .and d n m :: is)) s P :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

theorem slot_add8 (b : Addr) :
    b + BitVec.ofNat 64 (8 * (stLo + 1)) = b + BitVec.ofNat 64 (8 * stLo) + BitVec.ofNat 64 8 := by
  rw [Offset.add_add]; rfl

/-- The tweak in its slots times `α`. -/
theorem xtsMulA_ok {s : State} {X b : Addr} (hscr : Scr s X 2048) (hb : s.gpr sb = b) :
    WP isa (.block xtsMulA) s fun s' =>
      (∀ r, r ≠ t0 → r ≠ t1 → r ≠ .t2 → r ≠ .t3 → s'.gpr r = s.gpr r) ∧
      s'.mem = (s.mem.writeW (b + BitVec.ofNat 64 (8 * stLo))
        ((s.mem.readW (b + BitVec.ofNat 64 (8 * stLo)) 64 <<< 1) ^^^
          (if (s.mem.readW (b + BitVec.ofNat 64 (8 * (stLo + 1))) 64).msb then (0x87 : BitVec 64) else 0))).writeW
        (b + BitVec.ofNat 64 (8 * (stLo + 1)))
        ((s.mem.readW (b + BitVec.ofNat 64 (8 * (stLo + 1))) 64 <<< 1) |||
          (if (s.mem.readW (b + BitVec.ofNat 64 (8 * stLo)) 64).msb then (1 : BitVec 64) else 0)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  unfold xtsMulA
  refine slot_ld hscr hb (by decide) fun s₁ u₁ => ?_
  refine slot_ld (hscr.congr u₁.wr (by rw [u₁.other _ (by decide)])) (by rw [u₁.other _ (by decide), hb])
    (by decide) fun s₂ u₂ => ?_
  refine wp_srl (by decide) fun s₃ u₃ => wp_li (imm := 0) (by decide) fun s₄ u₄ => wp_sub fun s₅ u₅ => ?_
  refine wp_li (imm := 0x87) (by decide) fun s₆ u₆ => wp_and fun s₇ u₇ => ?_
  refine wp_srl (by decide) fun s₈ u₈ => wp_sll (by decide) fun s₉ u₉ => wp_xor fun s₁₀ u₁₀ => ?_
  refine wp_sll (by decide) fun s₁₁ u₁₁ => wp_or fun s₁₂ u₁₂ => ?_
  -- Only the temporaries change, up to here.
  have o₁₂ : ∀ r, r ≠ t0 → r ≠ t1 → r ≠ .t2 → r ≠ .t3 → s₁₂.gpr r = s.gpr r := fun r h0 h1 h2 h3 => by
    rw [u₁₂.other _ h1, u₁₁.other _ h1, u₁₀.other _ h0, u₉.other _ h0, u₈.other _ h3, u₇.other _ h2,
      u₆.other _ h3, u₅.other _ h2, u₄.other _ h3, u₃.other _ h2, u₂.other _ h1, u₁.other _ h0]
  have m₁₂ : s₁₂.mem = s.mem := by
    rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have wr₁₂ : s₁₂.wr = s.wr := by
    rw [u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have b₁₂ : s₁₂.gpr sb = b := by rw [o₁₂ _ (by decide) (by decide) (by decide) (by decide), hb]
  have scr₁₂ : Scr s₁₂ X 2048 := hscr.congr wr₁₂ (by rw [b₁₂, hb])
  generalize hL : s.mem.readW (b + BitVec.ofNat 64 (8 * stLo)) 64 = L
  generalize hH : s.mem.readW (b + BitVec.ofNat 64 (8 * (stLo + 1))) 64 = H
  have e₁ : s₁.gpr t0 = L := by rw [u₁.gpr, hL]
  have e₂ : s₂.gpr t1 = H := by rw [u₂.gpr, u₁.mem, hH]
  have v₀ : s₁₂.gpr t0 = (L <<< 1) ^^^ (if H.msb then (0x87 : BitVec 64) else 0) := by
    rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr, u₉.gpr, u₉.other .t2 (by decide),
      u₈.other t0 (by decide), u₈.other .t2 (by decide), u₇.gpr, u₇.other t0 (by decide), u₆.gpr,
      u₆.other t0 (by decide), u₆.other .t2 (by decide), u₅.gpr, u₅.other t0 (by decide), u₄.gpr,
      u₄.other t0 (by decide), u₄.other .t2 (by decide), u₃.gpr, u₃.other t0 (by decide), u₂.other t0 (by decide),
      e₁, e₂, ushr63, mask87]
  have v₁ : s₁₂.gpr t1 = (H <<< 1) ||| (if L.msb then (1 : BitVec 64) else 0) := by
    rw [u₁₂.gpr, u₁₁.gpr, u₁₁.other .t3 (by decide), u₁₀.other t1 (by decide), u₁₀.other .t3 (by decide),
      u₉.other t1 (by decide), u₉.other .t3 (by decide), u₈.gpr, u₈.other t1 (by decide),
      u₇.other t1 (by decide), u₇.other t0 (by decide), u₆.other t1 (by decide), u₆.other t0 (by decide),
      u₅.other t1 (by decide), u₅.other t0 (by decide), u₄.other t1 (by decide), u₄.other t0 (by decide),
      u₃.other t1 (by decide), u₃.other t0 (by decide), u₂.gpr, u₂.other t0 (by decide), u₁.mem, e₁, hH,
      ushr63]
  refine slot_st scr₁₂ b₁₂ (by decide) fun s₁₃ u₁₃ => ?_
  refine slot_st (scr₁₂.congr u₁₃.wr (by rw [u₁₃.gpr])) (by rw [u₁₃.gpr, b₁₂]) (by decide)
    fun s₁₄ u₁₄ => WP.block_nil ?_
  refine ⟨fun r h0 h1 h2 h3 => by rw [u₁₄.gpr, u₁₃.gpr, o₁₂ r h0 h1 h2 h3], ?_,
    by rw [u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd,
      u₁.rd],
    by rw [u₁₄.wr, u₁₃.wr, wr₁₂],
    by rw [u₁₄.sp, u₁₃.sp, u₁₂.sp, u₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp,
      u₁.sp]⟩
  rw [u₁₄.mem, u₁₃.gpr, u₁₃.mem, m₁₂, v₀, v₁]

/-- The tweak in its slots after `xtsMulA`'s stores: the block times `α`. -/
theorem slotBlk_mulA (m : Mem) (b : Addr) :
    slotBlk ((m.writeW (b + BitVec.ofNat 64 (8 * stLo))
        ((m.readW (b + BitVec.ofNat 64 (8 * stLo)) 64 <<< 1) ^^^
          (if (m.readW (b + BitVec.ofNat 64 (8 * (stLo + 1))) 64).msb then (0x87 : BitVec 64) else 0))).writeW
        (b + BitVec.ofNat 64 (8 * (stLo + 1)))
        ((m.readW (b + BitVec.ofNat 64 (8 * (stLo + 1))) 64 <<< 1) |||
          (if (m.readW (b + BitVec.ofNat 64 (8 * stLo)) 64).msb then (1 : BitVec 64) else 0))) b stLo =
      mulAS (slotBlk m b stLo) := by
  have hs (m' : Mem) : slotBlk m' b stLo = Spec.Aes.stateAt m' (b + BitVec.ofNat 64 (8 * stLo)) := by
    rw [stateAt_wBlk, slotBlk, slot_add8]; rfl
  rw [hs, hs, ← ofFn_toList (Spec.Aes.stateAt _ _), ← AesCbc.bytesAt_toList, slot_add8,
    AesXts.mulAlpha_words64, AesCbc.bytesAt_toList]
  rfl

/-! ## The invariants -/

/-- The loads of group `g`, after `k` of them: the data `xtsF`'s up to the
group, the state's slots the tweak of block `4 g + k`, and the first `k` of
the group's tweaks in their slots and inputs in their registers. -/
def xtsL (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) (m₀ : Mem) (D : Addr)
    (t : Spec.Aes.State) (R : Nat) (w : List Byte) (n : Nat) (b : Addr) (g k : Nat) (m : Mem)
    (Q : Nat → BitVec 64) : Prop :=
  EcbInv m₀ m D n (4 * g) (xtsF f R w m₀ D t) ∧ slotBlk m b stLo = xtsT t (4 * g + k) ∧
    ∀ c < k, slotBlk m b (blkLo c) = xtsT t (4 * g + c) ∧
      regBlock Q c = vxor (xtsC m₀ D (4 * g + c)) (xtsT t (4 * g + c))

/-- The stores of group `g`, after `k` of them: the data `xtsF`'s up to
them, the state's slots the tweak after the group, the group's tweaks in
their slots, and the others enciphered in the registers. -/
def xtsS (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) (m₀ : Mem) (D : Addr)
    (t : Spec.Aes.State) (R : Nat) (w : List Byte) (n : Nat) (b : Addr) (g k : Nat) (m : Mem)
    (Q : Nat → BitVec 64) : Prop :=
  EcbInv m₀ m D n (4 * g + k) (xtsF f R w m₀ D t) ∧ slotBlk m b stLo = xtsT t (4 * g + min 4 (n - 4 * g)) ∧
    ∀ c < min 4 (n - 4 * g), slotBlk m b (blkLo c) = xtsT t (4 * g + c) ∧
      (k ≤ c → regBlock Q c = f R w (vxor (xtsC m₀ D (4 * g + c)) (xtsT t (4 * g + c))))

theorem q_pairs' : ∀ c < 4, ∀ k < 4, c ≠ k → q c ≠ q k ∧ q c ≠ q (k + 4) ∧ q (c + 4) ≠ q k ∧
    q (c + 4) ≠ q (k + 4) := by decide

section Steps

variable {s₀ s₉ : State} {X b : Addr} (hs : FSetup true (16 * ·) s₀ s₉ X b) {t : Spec.Aes.State}
  {R : Nat} {w : List Byte} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
include hs

/-- A doubleword of the data, read through a store to a slot of 78–87. -/
theorem data_slot {m : Mem} {j : Nat} (hj : j < 88) (v : BitVec 64) {x : Nat}
    (hx : x + 8 ≤ 16 * (s₀.gpr .a4).toNat) :
    (m.writeW (b + BitVec.ofNat 64 (8 * j)) v).readW (s₀.gpr .a3 + BitVec.ofNat 64 x) 64 =
      m.readW (s₀.gpr .a3 + BitVec.ofNat 64 x) 64 :=
  Frame.readW ((Frame.refl _ _).writeW (r := ⟨b + BitVec.ofNat 64 (8 * j), 8⟩) (List.mem_singleton_self _) v
      (Region.contains_self _ _))
    (Offset.contains_base _ hx (by have := hs.n16; omega))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hs.dScr (by omega)) (by decide)

/-- Block `k` XORed with its tweak, the tweak copied to the block's slots,
and the tweak times `α`. -/
theorem xtsLoad_ok {g k : Nat} (hk : k < 4) (hkn : 4 * g + k < (s₀.gpr .a4).toNat) {s : State}
    (hb : WB s₀ s₉ b g s) (hl : xtsL f s₀.mem (s₀.gpr .a3) t R w (s₀.gpr .a4).toNat b g k s.mem (Q s)) :
    WP isa (.block (xtsLoad k)) s fun s' =>
      Foot s₀ b s s' ∧ xtsL f s₀.mem (s₀.gpr .a3) t R w (s₀.gpr .a4).toNat b g (k + 1) s'.mem (Q s') := by
  obtain ⟨hd, hst, hblk⟩ := hl
  have hn := hs.n16
  have hdat := hb.dat hs
  have hscr := hb.scr hs
  have hbase := hb.base hs
  obtain ⟨n1, n2, n3, -, -, n6, n7, n8, n9, n10, n11⟩ := q_c4 k hk
  have hbl : blkLo k + 1 < 88 := by unfold blkLo; omega
  have sc : ∀ {u : State}, u.wr = s.wr → u.gpr sb = s.gpr sb → Scr u X 2048 ∧ u.gpr sb = b :=
    fun hw hg => ⟨hscr.congr hw hg, hg.trans hbase⟩
  unfold xtsLoad
  repeat rw [WP.block_append_iff (M := isa)]
  -- The tweak's low doubleword to the block's slot.
  refine slot_ld hscr hbase (by decide) fun s₁ u₁ => ?_
  refine slot_st (hscr.congr u₁.wr (by rw [u₁.other _ (by decide)])) (by rw [u₁.other _ (by decide), hbase])
    (by omega) fun s₂ u₂ => WP.block_nil ?_
  -- The data's low doubleword, XORed with it.
  refine WP.mono (data_ld (D := s₀.gpr .a3) (g := g) (n := (s₀.gpr .a4).toNat) (off := 16 * k)
    (by rw [u₂.gpr, u₁.other _ (by decide)]; exact hb.a3)
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact List.mem_append_right _ hdat) hn (by omega) (by omega)
    ⟨n1, n8, n9⟩) fun s₃ ⟨e₃, o₃, m₃, rd₃, wr₃, sp₃⟩ => ?_
  refine wp_xor fun s₄ u₄ => ?_
  obtain ⟨scr₄, b₄⟩ := sc (u := s₄) (by rw [u₄.wr, wr₃, u₂.wr, u₁.wr]) (by
    rw [u₄.other _ (Ne.symm n6), o₃ _ (Ne.symm n6) (by decide) (by decide), u₂.gpr, u₁.other _ (by decide)])
  -- The high doubleword, the same way.
  refine slot_ld scr₄ b₄ (by decide) fun s₅ u₅ => ?_
  refine slot_st (scr₄.congr u₅.wr (by rw [u₅.other _ (by decide)])) (by rw [u₅.other _ (by decide), b₄])
    (by omega) fun s₆ u₆ => WP.block_nil ?_
  refine WP.mono (data_ld (D := s₀.gpr .a3) (g := g) (n := (s₀.gpr .a4).toNat) (off := 16 * k + 8)
    (by rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (Ne.symm n1), o₃ _ (Ne.symm n1) (by decide) (by decide),
      u₂.gpr, u₁.other _ (by decide)]; exact hb.a3)
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, rd₃, wr₃, u₂.rd, u₂.wr, u₁.rd, u₁.wr]
        exact List.mem_append_right _ hdat) hn (by omega) (by omega) ⟨n2, n10, n11⟩)
    fun s₇ ⟨e₇, o₇, m₇, rd₇, wr₇, sp₇⟩ => ?_
  refine wp_xor fun s₈ u₈ => WP.block_nil ?_
  obtain ⟨scr₈, b₈⟩ := sc (u := s₈) (by rw [u₈.wr, wr₇, u₆.wr, u₅.wr, u₄.wr, wr₃, u₂.wr, u₁.wr]) (by
    rw [u₈.other _ (Ne.symm n7), o₇ _ (Ne.symm n7) (by decide) (by decide), u₆.gpr, u₅.other _ (by decide),
      u₄.other _ (Ne.symm n6), o₃ _ (Ne.symm n6) (by decide) (by decide), u₂.gpr, u₁.other _ (by decide)])
  -- The tweak times `α`.
  refine WP.mono (xtsMulA_ok scr₈ b₈) fun s₁₀ ⟨o₁₀, m₁₀, rd₁₀, wr₁₀, sp₁₀⟩ => ?_
  have g₁₀ : ∀ r, r ≠ q k → r ≠ q (k + 4) → r ≠ t0 → r ≠ t1 → r ≠ .t2 → r ≠ .t3 → s₁₀.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 h6 => by
      rw [o₁₀ r h3 h4 h5 h6, u₈.other _ h2, o₇ _ h2 h3 h4, u₆.gpr, u₅.other _ h5, u₄.other _ h1, o₃ _ h1 h3 h4,
        u₂.gpr, u₁.other _ h5]
  have hm₈ : s₈.mem = (s.mem.writeW (b + BitVec.ofNat 64 (8 * blkLo k))
      (s.mem.readW (b + BitVec.ofNat 64 (8 * stLo)) 64)).writeW (b + BitVec.ofNat 64 (8 * (blkLo k + 1)))
      (s.mem.readW (b + BitVec.ofNat 64 (8 * (stLo + 1))) 64) := by
    rw [u₈.mem, m₇, u₆.mem, u₅.gpr, u₅.mem, u₄.mem, m₃, u₂.mem, u₁.gpr, u₁.mem,
      slot_writeW_ne _ _ (by omega) (by decide) (by unfold blkLo stLo; omega)]
  have hA : 64 * g + 16 * k + 8 ≤ 16 * (s₀.gpr .a4).toNat := by omega
  have hA8 : 64 * g + (16 * k + 8) + 8 ≤ 16 * (s₀.gpr .a4).toNat := by omega
  have vk : s₁₀.gpr (q k) = s.mem.readW (s₀.gpr .a3 + BitVec.ofNat 64 (64 * g + 16 * k)) 64 ^^^
      s.mem.readW (b + BitVec.ofNat 64 (8 * stLo)) 64 := by
    rw [o₁₀ _ (q_neW k).1 (q_neW k).2.1 (q_neW k).2.2.1 (q_neW k).2.2.2.1, u₈.other _ n3, o₇ _ n3 n8 n9, u₆.gpr,
      u₅.other _ (q_neW k).2.2.1, u₄.gpr, e₃, o₃ _ (Ne.symm (q_neW k).2.2.1) (by decide) (by decide), u₂.gpr,
      u₁.gpr, u₂.mem, u₁.mem, data_slot hs (j := blkLo k) (by omega) _ hA]
  have vk4 : s₁₀.gpr (q (k + 4)) = s.mem.readW (s₀.gpr .a3 + BitVec.ofNat 64 (64 * g + (16 * k + 8))) 64 ^^^
      s.mem.readW (b + BitVec.ofNat 64 (8 * (stLo + 1))) 64 := by
    rw [o₁₀ _ (q_neW (k + 4)).1 (q_neW (k + 4)).2.1 (q_neW (k + 4)).2.2.1 (q_neW (k + 4)).2.2.2.1, u₈.gpr, e₇,
      o₇ _ (Ne.symm (q_neW (k + 4)).2.2.1) (by decide) (by decide), u₆.mem, u₆.gpr, u₅.gpr, u₅.mem, u₄.mem, m₃,
      u₂.mem, u₁.mem, data_slot hs (j := blkLo k + 1) hbl _ hA8, data_slot hs (j := blkLo k) (by omega) _ hA8,
      slot_writeW_ne _ _ (by omega) (by decide) (by unfold blkLo stLo; omega)]
  have e₈ : EcbInv s₀.mem s₈.mem (s₀.gpr .a3) (s₀.gpr .a4).toNat (4 * g) (xtsF f R w s₀.mem (s₀.gpr .a3) t) := by
    rw [hm₈]
    exact ecbInv_frame (slot2_frame _ _ (by omega) _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hs.dScr (by unfold blkLo; omega)) hn hd
  have hs₈ : ∀ c, c < 4 → slotBlk s₁₀.mem b (blkLo c) = slotBlk s₈.mem b (blkLo c) := fun c hc => by
    rw [m₁₀]; exact slot2_other _ _ (by decide) (by unfold blkLo; omega) (by unfold blkLo stLo; omega) _ _
  refine ⟨⟨fun r h1 h2 => ?_, by rw [rd₁₀, u₈.rd, rd₇, u₆.rd, u₅.rd, u₄.rd, rd₃, u₂.rd, u₁.rd],
    by rw [wr₁₀, u₈.wr, wr₇, u₆.wr, u₅.wr, u₄.wr, wr₃, u₂.wr, u₁.wr],
    by rw [sp₁₀, u₈.sp, sp₇, u₆.sp, u₅.sp, u₄.sp, sp₃, u₂.sp, u₁.sp], ?_⟩, ?_, ?_, fun c hc => ?_⟩
  · exact g₁₀ r (fun e => h1 (e ▸ q_mem k (by omega))) (fun e => h1 (e ▸ q_mem (k + 4) (by omega)))
      (fun e => h1 (e ▸ by decide)) (fun e => h1 (e ▸ by decide)) (fun e => h1 (e ▸ by decide))
      (fun e => h1 (e ▸ by decide))
  · rw [m₁₀, hm₈]
    exact (((wSlot_frame _ (by unfold blkLo; omega) (by omega) _).trans
      (wSlot_frame _ (by unfold blkLo; omega) (by omega) _)).trans
      (wSlot_frame _ (by decide) (by decide) _)).trans (wSlot_frame _ (by decide) (by decide) _)
  · rw [m₁₀]
    exact ecbInv_frame (slot2_frame _ _ (by decide) _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hs.dScr (by decide)) hn e₈
  · rw [m₁₀, slotBlk_mulA, hm₈, slot2_other _ _ (by omega) (by decide) (by unfold blkLo stLo; omega), hst]
    rfl
  · by_cases hck : c = k
    · subst hck
      refine ⟨by rw [hs₈ c hk, hm₈, slot2_self _ _ (by omega)]; exact hst, ?_⟩
      rw [regBlock_wBlk]
      show wBlk (s₁₀.gpr (q c)) (s₁₀.gpr (q (c + 4))) = _
      rw [vk, vk4, wBlk_xor, show 64 * g + 16 * c = 16 * (4 * g + c) by omega,
        show 64 * g + (16 * c + 8) = 16 * (4 * g + c) + 8 by omega, add_off8, ← stateAt_wBlk,
        ecbInv_orig hd (by omega) hkn]
      exact congrArg _ hst
    · have hc' : c < k := by omega
      obtain ⟨d1, d2, d3, d4⟩ := q_pairs' c (by omega) k hk hck
      refine ⟨?_, ?_⟩
      · rw [hs₈ c (by omega), hm₈, slot2_other _ _ (by omega) (by unfold blkLo; omega) (by unfold blkLo; omega)]
        exact (hblk c hc').1
      rw [regBlock_wBlk]
      show wBlk (s₁₀.gpr (q c)) (s₁₀.gpr (q (c + 4))) = _
      rw [g₁₀ _ d1 d2 (q_neW _).1 (q_neW _).2.1 (q_neW _).2.2.1 (q_neW _).2.2.2.1,
        g₁₀ _ d3 d4 (q_neW _).1 (q_neW _).2.1 (q_neW _).2.2.1 (q_neW _).2.2.2.1, ← (hblk c hc').2, regBlock_wBlk]

/-- Block `k`'s result XORed with its tweak, stored. -/
theorem xtsStore_ok {g k : Nat} (hk : k < 4) (hkn : 4 * g + k < (s₀.gpr .a4).toNat) {s : State}
    (hb : WB s₀ s₉ b g s) (hl : xtsS f s₀.mem (s₀.gpr .a3) t R w (s₀.gpr .a4).toNat b g k s.mem (Q s)) :
    WP isa (.block (xtsStore k)) s fun s' =>
      Foot s₀ b s s' ∧ xtsS f s₀.mem (s₀.gpr .a3) t R w (s₀.gpr .a4).toNat b g (k + 1) s'.mem (Q s') := by
  obtain ⟨hd, hst, hblk⟩ := hl
  have hn := hs.n16
  have hdat := hb.dat hs
  have hscr := hb.scr hs
  have hbase := hb.base hs
  have hkm : k < min 4 ((s₀.gpr .a4).toNat - 4 * g) := by omega
  have hbl : blkLo k + 1 < 88 := by unfold blkLo; omega
  obtain ⟨-, -, -, -, -, -, -, n8, n9, n10, n11⟩ := q_c4 k hk
  have sc : ∀ {u : State}, u.wr = s.wr → u.gpr sb = s.gpr sb → Scr u X 2048 ∧ u.gpr sb = b :=
    fun hw hg => ⟨hscr.congr hw hg, hg.trans hbase⟩
  unfold xtsStore
  repeat rw [WP.block_append_iff (M := isa)]
  refine slot_ld hscr hbase (by omega) fun s₁ u₁ => wp_xor fun s₂ u₂ => WP.block_nil ?_
  have o₂ : ∀ r, r ≠ .t2 → s₂.gpr r = s.gpr r := fun r h => by rw [u₂.other _ h, u₁.other _ h]
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  have x₂ : s₂.gpr .t2 = s.mem.readW (b + BitVec.ofNat 64 (8 * blkLo k)) 64 ^^^ s.gpr (q k) := by
    rw [u₂.gpr, u₁.gpr, u₁.other _ (q_neW k).2.2.1]
  refine WP.mono (data_st (D := s₀.gpr .a3) (g := g) (n := (s₀.gpr .a4).toNat) (off := 16 * k)
    (by rw [o₂ _ (by decide)]; exact hb.a3) (by rw [u₂.wr, u₁.wr]; exact hdat) hn (by omega) (by omega)
    (by decide)) fun s₃ ⟨m₃, o₃, rd₃, wr₃, sp₃⟩ => ?_
  obtain ⟨scr₃, b₃⟩ := sc (u := s₃) (by rw [wr₃, u₂.wr, u₁.wr]) (by
    rw [o₃ _ (by decide) (by decide), o₂ _ (by decide)])
  refine slot_ld scr₃ b₃ (by omega) fun s₄ u₄ => wp_xor fun s₅ u₅ => WP.block_nil ?_
  have o₅ : ∀ r, r ≠ .t2 → r ≠ t0 → r ≠ t1 → s₅.gpr r = s.gpr r := fun r h h0 h1 => by
    rw [u₅.other _ h, u₄.other _ h, o₃ _ h0 h1, o₂ _ h]
  have m₅ : s₅.mem = s₃.mem := by rw [u₅.mem, u₄.mem]
  have x₅ : s₅.gpr .t2 = s₃.mem.readW (b + BitVec.ofNat 64 (8 * (blkLo k + 1))) 64 ^^^ s.gpr (q (k + 4)) := by
    rw [u₅.gpr, u₄.gpr, u₄.other _ (q_neW _).2.2.1, o₃ _ n10 n11, o₂ _ (q_neW _).2.2.1]
  refine WP.mono (data_st (D := s₀.gpr .a3) (g := g) (n := (s₀.gpr .a4).toNat) (off := 16 * k + 8)
    (by rw [o₅ _ (by decide) (by decide) (by decide)]; exact hb.a3)
    (by rw [u₅.wr, u₄.wr, wr₃, u₂.wr, u₁.wr]; exact hdat) hn (by omega) (by omega) (by decide))
    fun s₆ ⟨m₆, o₆, rd₆, wr₆, sp₆⟩ => ?_
  -- The memory: the data block.
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
  have hv : wBlk (s₂.gpr .t2) (s₅.gpr .t2) = xtsF f R w s₀.mem (s₀.gpr .a3) t (4 * g + k) := by
    rw [x₂, x₅, slot₃ _ hbl, wBlk_xor]
    show vxor (slotBlk s.mem b (blkLo k)) (wBlk (Q s k) (Q s (k + 4))) = _
    rw [(hblk k hkm).1, ← regBlock_wBlk, (hblk k hkm).2 (Nat.le_refl _)]
  have st := ecbInv_step (v₁ := s₂.gpr .t2) (v₂ := s₅.gpr .t2) (by omega) hkn hd (wBlk_bytes hv)
  rw [← hm₆] at st
  have slot₆ : ∀ j, j < 88 → s₆.mem.readW (b + BitVec.ofNat 64 (8 * j)) 64 =
      s.mem.readW (b + BitVec.ofNat 64 (8 * j)) 64 := fun j hj =>
    (st.2.readW (Region.contains_self _ _) (hs.slotW_data hj) (by decide))
  have hsl : ∀ j, j + 1 < 88 → slotBlk s₆.mem b j = slotBlk s.mem b j := fun j hj => by
    unfold slotBlk; rw [slot₆ _ (by omega), slot₆ _ hj]
  have o₆' : ∀ r, r ≠ .t2 → r ≠ t0 → r ≠ t1 → s₆.gpr r = s.gpr r := fun r h h0 h1 => by
    rw [o₆ _ h0 h1, o₅ _ h h0 h1]
  have hQ : ∀ c, regBlock (Q s₆) c = regBlock (Q s) c := fun c => by
    rw [regBlock_wBlk, regBlock_wBlk]
    show wBlk (s₆.gpr (q c)) (s₆.gpr (q (c + 4))) = wBlk (s.gpr (q c)) (s.gpr (q (c + 4)))
    rw [o₆' _ (q_neW _).2.2.1 (q_neW _).1 (q_neW _).2.1, o₆' _ (q_neW _).2.2.1 (q_neW _).1 (q_neW _).2.1]
  refine ⟨⟨fun r h1 h2 => o₆' r (fun e => h1 (e ▸ by decide)) (fun e => h1 (e ▸ by decide))
      (fun e => h1 (e ▸ by decide)),
    by rw [rd₆, u₅.rd, u₄.rd, rd₃, u₂.rd, u₁.rd], by rw [wr₆, u₅.wr, u₄.wr, wr₃, u₂.wr, u₁.wr],
    by rw [sp₆, u₅.sp, u₄.sp, sp₃, u₂.sp, u₁.sp], wData_frame st.2⟩, st.1, ?_, fun c hc => ?_⟩
  · rw [hsl _ (by decide)]; exact hst
  · refine ⟨by rw [hsl _ (by unfold blkLo; omega)]; exact (hblk c hc).1, fun h => ?_⟩
    rw [hQ]; exact (hblk c hc).2 (by omega)

end Steps

/-! ## The mode -/

/-- XTS, by the block function `f`, as a mode of `wide`. -/
theorem xts_ok (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) (s₀ : State) :
    WideOk s₀ xtsLoad xtsStore f
      (xtsL f s₀.mem (s₀.gpr .a3) (Spec.Aes.stateAt s₀.mem (s₀.gpr .a2)) (s₀.gpr .a1).toNat
        (Spec.Aes.bytesAt s₀.mem (s₀.gpr .a0) (16 * ((s₀.gpr .a1).toNat + 1))) (s₀.gpr .a4).toNat)
      (xtsS f s₀.mem (s₀.gpr .a3) (Spec.Aes.stateAt s₀.mem (s₀.gpr .a2)) (s₀.gpr .a1).toNat
        (Spec.Aes.bytesAt s₀.mem (s₀.gpr .a0) (16 * ((s₀.gpr .a1).toNat + 1))) (s₀.gpr .a4).toNat)
      (xtsF f (s₀.gpr .a1).toNat (Spec.Aes.bytesAt s₀.mem (s₀.gpr .a0) (16 * ((s₀.gpr .a1).toNat + 1)))
        s₀.mem (s₀.gpr .a3) (Spec.Aes.stateAt s₀.mem (s₀.gpr .a2)))
      (xtsT (Spec.Aes.stateAt s₀.mem (s₀.gpr .a2)) (s₀.gpr .a4).toNat) where
  init hs m Q hf hst :=
    ⟨ecbInv_frame (m := s₀.mem) hf (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hs.sep) hs.n16 fun i hi => by simp,
      hst, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  load hs _ _ hk hkn s hb hl := xtsLoad_ok hs hk hkn hb hl
  crypt := fun {s₉ X b} hs g m m' Q Q' hg hl hf hin => by
    obtain ⟨hd, hst, hblk⟩ := hl
    refine ⟨by rw [Nat.add_zero]; exact ecbInv_frame hf (by simpa using hs.d320) hs.n16 hd,
      by rw [slotBlk_frame hf (by decide) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint_base b (by decide) (by decide)]; exact hst, fun c hc => ⟨?_, fun _ => ?_⟩⟩
    · rw [slotBlk_frame hf (by unfold blkLo; omega) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint_base b (by unfold blkLo; omega) (by unfold blkLo; omega)]
      exact (hblk c hc).1
    · rw [regBlock_of_inRel hin (by omega), (hblk c hc).2]
  store hs _ _ hk hkn s hb hl := xtsStore_ok hs hk hkn hb hl
  next _ g m Q hg hl := by
    obtain ⟨hd, hst, -⟩ := hl
    exact ⟨by rw [show 4 * (g + 1) = 4 * g + 4 by omega]; exact hd,
      by rw [show 4 * (g + 1) + 0 = 4 * g + min 4 ((s₀.gpr .a4).toNat - 4 * g) by omega]; exact hst,
      fun _ h => absurd h (Nat.not_lt_zero _)⟩
  done _ g m Q hg hg' hl := by
    obtain ⟨hd, hst, -⟩ := hl
    rw [show 4 * g + ((s₀.gpr .a4).toNat - 4 * g) = (s₀.gpr .a4).toNat by omega] at hd
    rw [show 4 * g + min 4 ((s₀.gpr .a4).toNat - 4 * g) = (s₀.gpr .a4).toNat by omega] at hst
    exact ⟨hd, hst⟩

theorem aesWith_toList' (R : Nat) (w : List Byte) (x : Spec.Aes.State) :
    AesCbc.ciphOf true R w x.toList = (Spec.Aes.cipher R w x).toList := by
  rw [AesCbc.ciphOf, ite_eq_left rfl, Spec.Cbc.aesWith, ofFn_toList]

theorem aesInvWith_toList' (R : Nat) (w : List Byte) (x : Spec.Aes.State) :
    AesCbc.ciphOf false R w x.toList = (Spec.Aes.invCipher R w x).toList := by
  rw [AesCbc.ciphOf, ite_eq_right Bool.false_ne_true, Spec.Cbc.aesInvWith, ofFn_toList]

theorem xtsEncWide_correct {s₀ : State} (hp : (blockKRISCV64 (AesXts.xtsMode true)).pre s₀) :
    WP isa xtsEncWide s₀ fun s' =>
      (∀ r ∈ RISCV64.preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
        (blockKRISCV64 (AesXts.xtsMode true)).post s₀ s' := by
  unfold xtsEncWide
  exact wide_correct _ encrypt4_cryptOk hp (xts_ok _ s₀)
    (by rw [AesCbc.bytesAt_toList]; exact xts_out true _ _ _ (aesWith_toList' _ _) _ _ _ _)
    (by rw [AesCbc.bytesAt_toList]; exact xts_chain _ _ _ _ _ _ _)

theorem xtsDecWide_correct {s₀ : State} (hp : (blockKRISCV64 (AesXts.xtsMode false)).pre s₀) :
    WP isa xtsDecWide s₀ fun s' =>
      (∀ r ∈ RISCV64.preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
        (blockKRISCV64 (AesXts.xtsMode false)).post s₀ s' := by
  unfold xtsDecWide
  exact wide_correct _ decrypt4_cryptOk hp (xts_ok _ s₀)
    (by rw [AesCbc.bytesAt_toList]; exact xts_out false _ _ _ (aesInvWith_toList' _ _) _ _ _ _)
    (by rw [AesCbc.bytesAt_toList]; exact xts_chain _ _ _ _ _ _ _)

theorem xtsEncWide_ct : ConstantTime isa (blockKRISCV64 (AesXts.xtsMode true)).pre
    (blockKRISCV64 (AesXts.xtsMode true)).pub xtsEncWide :=
  wide_ct _ (by taint_decide)

theorem xtsDecWide_ct : ConstantTime isa (blockKRISCV64 (AesXts.xtsMode false)).pre
    (blockKRISCV64 (AesXts.xtsMode false)).pub xtsDecWide :=
  wide_ct _ (by taint_decide)

theorem xtsEncWide_k :
    AesCbc.RISCV64.ChainK true (16 * ·) (blockKRISCV64 (AesXts.xtsMode true)) xtsEncWide :=
  blockK_k xtsEncWide_correct xtsEncWide_ct rfl

theorem xtsDecWide_k :
    AesCbc.RISCV64.ChainK true (16 * ·) (blockKRISCV64 (AesXts.xtsMode false)) xtsDecWide :=
  blockK_k xtsDecWide_correct xtsDecWide_ct rfl

end VG.Proof.Aes.RISCV64
