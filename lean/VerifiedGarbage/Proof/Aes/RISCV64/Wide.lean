module

public import VerifiedGarbage.Proof.Aes.RISCV64.ChainModes
public import VerifiedGarbage.Impl.Aes.RISCV64.Wide
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.Words64
import VerifiedGarbage.Proof.Framework.RISCV64.Align
import VerifiedGarbage.Proof.Aes.RISCV64.Blocks
import VerifiedGarbage.Proof.AesCbc.Spec

-- separate module: the generic proof of `wide`, which each mode's (`WideCbc.lean`, and CFB128
-- decryption's and XTS's) imports, apart from them so that changing one rebuilds no other.

/-!
# AES modes four blocks at a time on RISC-V: the frame and the groups

`wide load store crypt4` (`Impl/Aes/RISCV64/Wide.lean`) runs `chain`'s frame
(`ChainFrame.lean`) with a loop of groups of up to four blocks, as
`vg_aes_encrypt_blocks`' (`Ecb.lean`): in each group, `load k` for the
blocks `k` of the group, `crypt4` on the four, and `store k` for each.

A mode is proven by its `WideOk`: its invariants, over the memory and the
state registers only (`Q`), `L b g k` after the first `k` loads of group `g`
and `S b g k` after the first `k` stores, at the rounded scratch buffer `b`,
and what each load and store does to them (with what it may change,
`Foot`: the registers of `sboxWrites` and the memory of `wRegions`, the
S-box's slots, slots 78–87 and the data), and what holds after the last
group: the data the blocks `F` (`EcbInv`), and the state's slots
(`slotBlk`) the block `Fin`. `wide_correct` proves the rest once: the frame
and its registers (`WB`, before group `g`), the branches of each group
(`wideLoad_wp`, `wideStore_wp`), `crypt4` (`wide_crypt`, from `CryptOk`),
the loop (`wideLoop_wp`), and `blockKRISCV64 M`, when `M`'s output is `F`'s
and its chaining value `Fin`. Constant time is each mode's `taint_decide`
on its code (`wide_ct` states it as `blockKRISCV64 M`'s).

The blocks in two doublewords, little-endian, are `wBlk` (`regBlock`'s
block `c` is `wBlk` of words `c` and `c + 4`, `regBlock_wBlk`), and in two
slots of the scratch buffer `slotBlk`, with the lemmas the modes' loads and
stores use (`slot_ld`, `slot_st`, `data_ld`, `data_st`, `slot2_self`, …).
-/

@[expose] public section

namespace VG.Proof.Aes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.RISCV64.Align VG.RISCV64.Steps VG.Bitslice
  VG.Impl.Aes.RISCV64 VG.Impl.Words.RISCV64 VG.Proof.Aes

/-! ## Blocks of two doublewords -/

/-- The block of the doublewords `lo` (bytes 0–7) and `hi` (bytes 8–15),
little-endian. -/
def wBlk (lo hi : BitVec 64) : Spec.Aes.State :=
  Vector.ofFn fun i => (if i.1 < 8 then lo else hi).extractLsb' (8 * (i.1 % 8)) 8

theorem regBlock_wBlk (Q : Nat → BitVec 64) (c : Nat) : regBlock Q c = wBlk (Q c) (Q (c + 4)) := by
  apply Vector.ext
  intro i hi
  simp only [regBlock, wBlk, Vector.getElem_ofFn]
  by_cases h8 : i < 8
  · rw [show i / 8 = 0 by omega, Nat.mul_zero, Nat.add_zero, ite_eq_left h8]
  · rw [show i / 8 = 1 by omega, Nat.mul_one, ite_eq_right h8]

theorem wBlk_xor (a b c d : BitVec 64) : wBlk (a ^^^ c) (b ^^^ d) = vxor (wBlk a b) (wBlk c d) := by
  apply Vector.ext
  intro i hi
  simp only [wBlk, vxor, Vector.getElem_ofFn]
  refine byte_ext fun j hj => ?_
  by_cases h8 : i < 8 <;> simp [h8, BitVec.getLsbD_xor, hj]

/-- The bytes of a block of two doublewords, as `ecbInv_step` takes them. -/
theorem wBlk_bytes {lo hi : BitVec 64} {v : Spec.Aes.State} (h : wBlk lo hi = v) :
    ∀ t < 16, (if t < 8 then lo.extractLsb' (8 * t) 8 else hi.extractLsb' (8 * (t - 8)) 8) =
      v.getD t 0 := by
  intro t ht
  rw [← h, getD_eq _ ht]
  simp only [wBlk, Vector.getElem_ofFn]
  by_cases h8 : t < 8
  · rw [ite_eq_left h8, ite_eq_left h8, show t % 8 = t by omega]
  · rw [ite_eq_right h8, ite_eq_right h8, show t % 8 = t - 8 by omega]

theorem stateAt_wBlk (m : Mem) (a : Addr) :
    Spec.Aes.stateAt m a = wBlk (m.readW a 64) (m.readW (a + 8) 64) := by
  rw [← regBlock_load (Q := fun i => if i = 0 then m.readW a 64 else m.readW (a + 8) 64) (c := 0) rfl rfl,
    regBlock_wBlk]
  rfl

/-- The block in slots `k` and `k + 1` of the scratch buffer at `b`. -/
def slotBlk (m : Mem) (b : Addr) (k : Nat) : Spec.Aes.State :=
  wBlk (m.readW (b + BitVec.ofNat 64 (8 * k)) 64) (m.readW (b + BitVec.ofNat 64 (8 * (k + 1))) 64)

/-- A slot after a write of another. -/
theorem slot_writeW_ne (m : Mem) (b : Addr) {j k : Nat} (hj : j < 256) (hk : k < 256) (h : j ≠ k)
    (v : BitVec 64) :
    (m.writeW (b + BitVec.ofNat 64 (8 * j)) v).readW (b + BitVec.ofNat 64 (8 * k)) 64 =
      m.readW (b + BitVec.ofNat 64 (8 * k)) 64 :=
  Mem.readW_writeW_sep (Offset.sep b (by omega) (by omega) (by omega)) (by decide)

/-- Two slots written. -/
theorem slot2_frame (m : Mem) (b : Addr) {j : Nat} (hj : j < 256) (v₁ v₂ : BitVec 64) :
    Frame [⟨b + BitVec.ofNat 64 (8 * j), 16⟩] m
      ((m.writeW (b + BitVec.ofNat 64 (8 * j)) v₁).writeW (b + BitVec.ofNat 64 (8 * (j + 1))) v₂) :=
  ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (Offset.contains b (by omega) (by omega) (by omega))).writeW (List.mem_singleton_self _) _
    (Offset.contains b (by omega) (by omega) (by omega))

theorem slot2_self (m : Mem) (b : Addr) {j : Nat} (hj : j < 256) (v₁ v₂ : BitVec 64) :
    slotBlk ((m.writeW (b + BitVec.ofNat 64 (8 * j)) v₁).writeW (b + BitVec.ofNat 64 (8 * (j + 1))) v₂)
      b j = wBlk v₁ v₂ := by
  unfold slotBlk
  rw [Mem.readW_writeW_self64, Mem.readW_writeW_sep (Offset.sep b (by omega) (by omega) (by omega)) (by decide),
    Mem.readW_writeW_self64]

/-- A block of slots outside a frame. -/
theorem slotBlk_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {b : Addr} {k : Nat}
    (hk : k < 256) (hd : ∀ r ∈ rs, Region.Disjoint ⟨b + BitVec.ofNat 64 (8 * k), 16⟩ r) :
    slotBlk m' b k = slotBlk m b k := by
  unfold slotBlk
  rw [hf.readW (Offset.contains b (by omega) (by omega) (by omega)) hd (by decide),
    hf.readW (Offset.contains b (by omega) (by omega) (by omega)) hd (by decide)]

theorem slot2_other (m : Mem) (b : Addr) {j k : Nat} (hj : j < 256) (hk : k < 256)
    (h : j + 2 ≤ k ∨ k + 2 ≤ j) (v₁ v₂ : BitVec 64) :
    slotBlk ((m.writeW (b + BitVec.ofNat 64 (8 * j)) v₁).writeW (b + BitVec.ofNat 64 (8 * (j + 1))) v₂)
      b k = slotBlk m b k :=
  slotBlk_frame (slot2_frame m b hj v₁ v₂) hk fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint b (by omega) (by omega) (by omega)

/-! ## The registers -/

theorem q_neW (i : Nat) : q i ≠ t0 ∧ q i ≠ t1 ∧ q i ≠ .t2 ∧ q i ≠ .t3 ∧ q i ≠ .a3 ∧ q i ≠ .a4 ∧
    q i ≠ sb ∧ q i ≠ .ra := by
  unfold q; split <;> decide

/-- The state registers after a write of another register. -/
theorem Q_upd {s s' : State} {d : Reg} {v : BitVec 64} (u : Upd s s' d v) (hd : ∀ i, q i ≠ d) :
    Q s' = Q s :=
  funext fun i => u.other _ (hd i)

theorem Q_mupd {s s' : State} {m : Mem} (u : Mupd s s' m) : Q s' = Q s :=
  funext fun i => by simp only [Q, u.gpr]

/-! ## Slots and data -/

section Slots

variable {s : State} {X b : Addr} {is : List Instr} {P : State → Prop}

theorem slot_ld (hscr : Scr s X 2048) (hb : s.gpr sb = b) {d : Reg} {k : Nat} (hk : 8 * k + 15 ≤ 2048)
    (h : ∀ s', Upd s s' d (s.mem.readW (b + BitVec.ofNat 64 (8 * k)) 64) → WP isa (.block is) s' P) :
    WP isa (.block (ldS d k :: is)) s P :=
  wp_ld (t := d) (n := sb) (off := 8 * k) (a := b + BitVec.ofNat 64 (8 * k)) (by omega) (by rw [hb])
    (by rw [← hb]; exact Align.al_add (k := 8) hscr.al (by decide) (by omega))
    ⟨_, List.mem_append_right _ hscr.wr, by rw [← hb]; exact hscr.contains (by omega) (by decide)⟩ h

theorem slot_st (hscr : Scr s X 2048) (hb : s.gpr sb = b) {r : Reg} {k : Nat} (hk : 8 * k + 15 ≤ 2048)
    (h : ∀ s', Mupd s s' (s.mem.writeW (b + BitVec.ofNat 64 (8 * k)) (s.gpr r)) → WP isa (.block is) s' P) :
    WP isa (.block (stS k r :: is)) s P :=
  wp_sd (t := r) (n := sb) (off := 8 * k) (a := b + BitVec.ofNat 64 (8 * k)) (by omega) (by rw [hb])
    (by rw [← hb]; exact Align.al_add (k := 8) hscr.al (by decide) (by omega))
    ⟨_, hscr.wr, by rw [← hb]; exact hscr.contains (by omega) (by decide)⟩ h

end Slots

section Data

variable {s : State} {D : Addr} {n g off : Nat}

/-- A doubleword of the data, at `D + 64 g + off`, from `a3 = D + 64 g`. -/
theorem data_ld (ha : s.gpr .a3 = D + BitVec.ofNat 64 (64 * g))
    (hin : (⟨D, 16 * n⟩ : Region) ∈ s.rd ++ s.wr) (hn : 16 * n < 2 ^ 64) (ho : 64 * g + off + 8 ≤ 16 * n)
    (ho' : off + 7 < 2048) {d : Reg} (hd : d ≠ .a3 ∧ d ≠ t0 ∧ d ≠ t1) :
    WP isa (.block (loadLE64 d t0 t1 .a3 off)) s fun s' =>
      s'.gpr d = s.mem.readW (D + BitVec.ofNat 64 (64 * g + off)) 64 ∧
      (∀ r, r ≠ d → r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have hA0 : s.gpr .a3 + BitVec.ofNat 64 off = D + BitVec.ofNat 64 (64 * g + off) := by
    rw [ha, Offset.add_add]
  have hA4 : s.gpr .a3 + BitVec.ofNat 64 (off + 4) = D + BitVec.ofNat 64 (64 * g + off + 4) := by
    simp only [ha, Offset.add_add, Nat.add_assoc]
  refine WP.mono (Bytes.loadLE64_ok (d := d) (tmp := t0) (hi := t1) (n := .a3) (off := off)
    hd.1 (by decide) (by decide) hd.2.1 hd.2.2 (by decide) ho'
    (by rw [hA0]; exact in_off hin (by omega) hn)
    (by rw [hA4]; exact in_off hin (by omega) hn)) fun s' ⟨e, o, m, rd, wr, sp⟩ => ⟨?_, o, m, rd, wr, sp⟩
  rw [e, hA0]

/-- A doubleword stored over the data, at `D + 64 g + off`, from `a3 = D + 64 g`. -/
theorem data_st (ha : s.gpr .a3 = D + BitVec.ofNat 64 (64 * g))
    (hin : (⟨D, 16 * n⟩ : Region) ∈ s.wr) (hn : 16 * n < 2 ^ 64) (ho : 64 * g + off + 8 ≤ 16 * n)
    (ho' : off + 7 < 2048) {v : Reg} (hv : t0 ≠ v) :
    WP isa (.block (storeLE64 v t0 t1 .a3 off)) s fun s' =>
      s'.mem = s.mem.writeW (D + BitVec.ofNat 64 (64 * g + off)) (s.gpr v) ∧
      (∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have hA0 : s.gpr .a3 + BitVec.ofNat 64 off = D + BitVec.ofNat 64 (64 * g + off) := by
    rw [ha, Offset.add_add]
  have hA4 : s.gpr .a3 + BitVec.ofNat 64 (off + 4) = D + BitVec.ofNat 64 (64 * g + off + 4) := by
    simp only [ha, Offset.add_add, Nat.add_assoc]
  refine WP.mono (Bytes.storeLE64_ok (v := v) (tmp := t0) (hi := t1) (n := .a3) (off := off)
    hv (by decide) (by decide) (by decide) ho'
    (by rw [hA0]; exact in_off hin (by omega) hn)
    (by rw [hA4]; exact in_off hin (by omega) hn)) fun s' ⟨m, o, rd, wr, sp⟩ => ⟨?_, o, rd, wr, sp⟩
  rw [m, hA0, show s.gpr .a3 + BitVec.ofNat 64 (off + 4) = D + BitVec.ofNat 64 (64 * g + off) + BitVec.ofNat 64 4 by
    simp only [ha, Offset.add_add, Nat.add_assoc], Words64.writeW64_split]

end Data

/-! ## What a group may change -/

/-- The memory `wide`'s loop writes: the S-box's slots, slots 78–87 and the data. -/
abbrev wRegions (b D : Addr) (n : Nat) : List Region :=
  [⟨b, 320⟩, ⟨b + BitVec.ofNat 64 624, 80⟩, ⟨D, 16 * n⟩]

/-- What a part of a group may change from `s` to `s'`, for the call from `s₀`. -/
structure Foot (s₀ : State) (b : Addr) (s s' : State) : Prop where
  keep : ∀ r, r ∉ sboxWrites → r ≠ kp → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame (wRegions b (s₀.gpr .a3) (s₀.gpr .a4).toNat) s.mem s'.mem

section Foot

variable {s₀ : State} {b : Addr} {s₁ s₂ s₃ : State}

theorem Foot.rfl' (s : State) : Foot s₀ b s s := ⟨fun _ _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩

theorem Foot.trans (h₁ : Foot s₀ b s₁ s₂) (h₂ : Foot s₀ b s₂ s₃) : Foot s₀ b s₁ s₃ :=
  ⟨fun r h h' => (h₂.keep r h h').trans (h₁.keep r h h'), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    h₂.sp.trans h₁.sp, h₁.frame.trans h₂.frame⟩

theorem Foot.upd {d : Reg} {v : BitVec 64} (u : Upd s₁ s₂ d v) (hd : d ∈ sboxWrites) : Foot s₀ b s₁ s₂ :=
  ⟨fun r h _ => u.other r (fun e => h (e ▸ hd)), u.rd, u.wr, u.sp, by rw [u.mem]; exact Frame.refl _ _⟩

theorem Foot.mupd {m : Mem} (u : Mupd s₁ s₂ m)
    (hf : Frame (wRegions b (s₀.gpr .a3) (s₀.gpr .a4).toNat) s₁.mem m) : Foot s₀ b s₁ s₂ :=
  ⟨fun r _ _ => by rw [u.gpr], u.rd, u.wr, u.sp, by rw [u.mem]; exact hf⟩

/-- A slot of 78–87 written. -/
theorem wSlot_frame (m : Mem) {k : Nat} (h₁ : 78 ≤ k) (h₂ : k < 88) (v : BitVec 64) :
    Frame (wRegions b (s₀.gpr .a3) (s₀.gpr .a4).toNat) m (m.writeW (b + BitVec.ofNat 64 (8 * k)) v) :=
  (Frame.refl _ _).writeW (r := ⟨b + BitVec.ofNat 64 624, 80⟩) (by simp) _
    (Offset.contains b (by omega) (by omega) (by omega))

/-- The data written. -/
theorem wData_frame {m m' : Mem} (h : Frame [⟨s₀.gpr .a3, 16 * (s₀.gpr .a4).toNat⟩] m m') :
    Frame (wRegions b (s₀.gpr .a3) (s₀.gpr .a4).toNat) m m' :=
  h.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp

end Foot

/-- During group `g`, for the call from `s₀`, from the state `s₉` the loop
starts from: the data's address and the blocks left in `a3` and `a4`, the
registers outside `sboxWrites` (but `kp`) kept, and the memory changed only
in `wRegions`. -/
structure WB (s₀ s₉ : State) (b : Addr) (g : Nat) (s : State) : Prop where
  a3 : s.gpr .a3 = s₀.gpr .a3 + BitVec.ofNat 64 (64 * g)
  a4 : s.gpr .a4 = BitVec.ofNat 64 ((s₀.gpr .a4).toNat - 4 * g)
  keep : ∀ r, r ∉ sboxWrites → r ≠ kp → r ≠ .a3 → r ≠ .a4 → s.gpr r = s₉.gpr r
  rd : s.rd = s₉.rd
  wr : s.wr = s₉.wr
  sp : s.sp = s₉.sp
  frame : Frame (wRegions b (s₀.gpr .a3) (s₀.gpr .a4).toNat) s₉.mem s.mem

section Setup

variable {s₀ s₉ : State} {X b : Addr} (hs : FSetup true (16 * ·) s₀ s₉ X b)
include hs

omit hs in
theorem WB.foot {g : Nat} {s s' : State} (h : WB s₀ s₉ b g s) (f : Foot s₀ b s s') : WB s₀ s₉ b g s' :=
  ⟨(f.keep _ (by decide) (by decide)).trans h.a3, (f.keep _ (by decide) (by decide)).trans h.a4,
    fun r h1 h2 h3 h4 => (f.keep r h1 h2).trans (h.keep r h1 h2 h3 h4), f.rd.trans h.rd, f.wr.trans h.wr,
    f.sp.trans h.sp, h.frame.trans f.frame⟩

theorem WB.base {g : Nat} {s : State} (h : WB s₀ s₉ b g s) : s.gpr sb = b :=
  (h.keep sb (by decide) (by decide) (by decide) (by decide)).trans hs.base

theorem WB.scr {g : Nat} {s : State} (h : WB s₀ s₉ b g s) : Scr s X 2048 :=
  hs.scr.congr h.wr (by rw [h.base hs, hs.base])

theorem WB.dat {g : Nat} {s : State} (h : WB s₀ s₉ b g s) :
    (⟨s₀.gpr .a3, 16 * (s₀.gpr .a4).toNat⟩ : Region) ∈ s.wr :=
  h.wr ▸ hs.dat rfl

theorem FSetup.n16 : 16 * (s₀.gpr .a4).toNat < 2 ^ 64 := hs.hn

/-- The scratch buffer's parts at the rounded base. -/
theorem FSetup.sub' {d l : Nat} (h : d + l + 7 ≤ 2048) :
    Region.Sub ⟨b + BitVec.ofNat 64 d, l⟩ ⟨X, 2048⟩ := by
  rw [← hs.base]; exact hs.scr.sub h

/-- The data and the scratch buffer's parts. -/
theorem FSetup.dScr {d l : Nat} (h : d + l + 7 ≤ 2048) :
    Region.Disjoint ⟨s₀.gpr .a3, 16 * (s₀.gpr .a4).toNat⟩ ⟨b + BitVec.ofNat 64 d, l⟩ :=
  hs.sep.sub_right (hs.sub' h)

theorem FSetup.d320 : Region.Disjoint ⟨s₀.gpr .a3, 16 * (s₀.gpr .a4).toNat⟩ ⟨b, 320⟩ := by
  have := hs.dScr (d := 0) (l := 320) (by omega)
  simpa using this

/-- A block of slots of 78–87, outside the data. -/
theorem FSetup.slot_data {k : Nat} (hk : k < 88) :
    ∀ r ∈ [(⟨s₀.gpr .a3, 16 * (s₀.gpr .a4).toNat⟩ : Region)],
      Region.Disjoint ⟨b + BitVec.ofNat 64 (8 * k), 16⟩ r := fun r hr => by
  simp only [List.mem_singleton] at hr; subst hr; exact (hs.dScr (by omega)).symm

/-- A slot, outside the data. -/
theorem FSetup.slotW_data {k : Nat} (hk : k < 88) :
    ∀ r ∈ [(⟨s₀.gpr .a3, 16 * (s₀.gpr .a4).toNat⟩ : Region)],
      Region.Disjoint ⟨b + BitVec.ofNat 64 (8 * k), 8⟩ r := fun r hr => by
  simp only [List.mem_singleton] at hr; subst hr; exact (hs.dScr (by omega)).symm

/-- The data outside slots 78–87. -/
theorem FSetup.data_slots :
    ∀ r ∈ [(⟨b + BitVec.ofNat 64 624, 80⟩ : Region)],
      Region.Disjoint ⟨s₀.gpr .a3, 16 * (s₀.gpr .a4).toNat⟩ r := fun r hr => by
  simp only [List.mem_singleton] at hr; subst hr; exact hs.dScr (by omega)

theorem FSetup.wMasks : ∀ r ∈ wRegions b (s₀.gpr .a3) (s₀.gpr .a4).toNat,
    Region.Disjoint ⟨b + BitVec.ofNat 64 416, 48⟩ r ∧ Region.Disjoint ⟨b + BitVec.ofNat 64 512, 96⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨Offset.disjoint_base b (by omega) (by omega), Offset.disjoint_base b (by omega) (by omega)⟩
  · exact ⟨Offset.disjoint b (by omega) (by omega) (by omega), Offset.disjoint b (by omega) (by omega) (by omega)⟩
  · exact ⟨(hs.dScr (by omega)).symm, (hs.dScr (by omega)).symm⟩

theorem FSetup.wKeys : ∀ r ∈ wRegions b (s₀.gpr .a3) (s₀.gpr .a4).toNat,
    Region.Disjoint ⟨b + 1024, 960⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact keys_disjoint b
  · exact Offset.disjoint b (d := 1024) (by omega) (by omega) (by omega)
  · exact (hs.dScr (d := 1024) (l := 960) (by omega)).symm

/-- `crypt4` on the state registers. -/
theorem wide_crypt {crypt4 : Prog isa} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    (hc : CryptOk crypt4 f) {g : Nat} {s : State} (hw : WB s₀ s₉ b g s) :
    WP isa crypt4 s fun s' => WB s₀ s₉ b g s' ∧ Frame [⟨b, 320⟩] s.mem s'.mem ∧
      InRel (Q s') fun c => f (s₀.gpr .a1).toNat
        (Spec.Aes.bytesAt s₀.mem (s₀.gpr .a0) (16 * ((s₀.gpr .a1).toNat + 1))) (regBlock (Q s) c) := by
  have hR : (s₀.gpr .a1).toNat ≤ 14 := by rcases hs.rounds with h | h | h <;> omega
  have hb := hw.base hs
  have a0 := hw.keep .a0 (by decide) (by decide) (by decide) (by decide)
  have hp : EncPre s X (s₀.gpr .a1).toNat
      (Spec.Aes.bytesAt s₀.mem (s₀.gpr .a0) (16 * ((s₀.gpr .a1).toNat + 1))) :=
    ⟨hw.scr hs, by rw [hb]; exact masks_frame hw.frame hs.wMasks hs.masks, hs.rounds,
      by rw [a0, hs.a0, hb], by rw [a0, hs.a0]; exact keysAt_frame hR hw.frame hs.wKeys hs.keys⟩
  refine WP.mono (hc hp (inRel_regBlock (Q s))) fun s' ⟨hc', hin⟩ => ?_
  have fr : Frame [⟨b, 320⟩] s.mem s'.mem := by have := hc'.frame; rw [hb] at this; exact this
  exact ⟨hw.foot ⟨hc'.keep, hc'.rd, hc'.wr, hc'.sp, fr.mono fun r hr => by simp at hr; simp [hr]⟩, fr, hin⟩

end Setup

/-! ## A mode -/

/-- A mode run by `wide load store crypt4` on the call from `s₀`, with the
invariants `L` (loads) and `S` (stores), the transformation `f` of
`crypt4` (`CryptOk`), and after the last group the data's blocks `F` and
the state's `Fin`. For the scratch buffer at `b`:

* `init`: `L b 0 0` holds once the state is in its slots (and the memory
  changed only in the scratch buffer);
* `load`, `store`: `load k` (`store k`) takes `L b g k` (`S b g k`) to
  `k + 1`, changing only `Foot`'s;
* `crypt`: after the loads (`min 4 (n - 4 g)` of them), `crypt4`, which
  writes only the S-box's slots and makes the state registers `f` of each
  block, gives `S b g 0`;
* `next`, `done`: after the stores, `L b (g + 1) 0`, or after the last
  group the data's blocks `F` and the state `Fin`. -/
structure WideOk (s₀ : State) (load store : Nat → List Instr)
    (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State)
    (L S : Addr → Nat → Nat → Mem → (Nat → BitVec 64) → Prop) (F : Nat → Spec.Aes.State)
    (Fin : Spec.Aes.State) : Prop where
  init : ∀ {s₉ X b}, FSetup true (16 * ·) s₀ s₉ X b → ∀ m Q, Frame [⟨X, 2048⟩] s₀.mem m →
    slotBlk m b stLo = Spec.Aes.stateAt s₀.mem (s₀.gpr .a2) → L b 0 0 m Q
  load : ∀ {s₉ X b}, FSetup true (16 * ·) s₀ s₉ X b → ∀ g k, k < 4 → 4 * g + k < (s₀.gpr .a4).toNat →
    ∀ s, WB s₀ s₉ b g s → L b g k s.mem (Q s) →
      WP isa (.block (load k)) s fun s' => Foot s₀ b s s' ∧ L b g (k + 1) s'.mem (Q s')
  crypt : ∀ {s₉ X b}, FSetup true (16 * ·) s₀ s₉ X b → ∀ g m m' Q Q', 4 * g < (s₀.gpr .a4).toNat →
    L b g (min 4 ((s₀.gpr .a4).toNat - 4 * g)) m Q → Frame [⟨b, 320⟩] m m' →
    InRel Q' (fun c => f (s₀.gpr .a1).toNat
      (Spec.Aes.bytesAt s₀.mem (s₀.gpr .a0) (16 * ((s₀.gpr .a1).toNat + 1))) (regBlock Q c)) →
    S b g 0 m' Q'
  store : ∀ {s₉ X b}, FSetup true (16 * ·) s₀ s₉ X b → ∀ g k, k < 4 → 4 * g + k < (s₀.gpr .a4).toNat →
    ∀ s, WB s₀ s₉ b g s → S b g k s.mem (Q s) →
      WP isa (.block (store k)) s fun s' => Foot s₀ b s s' ∧ S b g (k + 1) s'.mem (Q s')
  next : ∀ {s₉ X b}, FSetup true (16 * ·) s₀ s₉ X b → ∀ g m Q, 4 * g + 4 < (s₀.gpr .a4).toNat →
    S b g 4 m Q → L b (g + 1) 0 m Q
  done : ∀ {s₉ X b}, FSetup true (16 * ·) s₀ s₉ X b → ∀ g m Q, 4 * g < (s₀.gpr .a4).toNat →
    (s₀.gpr .a4).toNat ≤ 4 * g + 4 → S b g ((s₀.gpr .a4).toNat - 4 * g) m Q →
    EcbInv s₀.mem m (s₀.gpr .a3) (s₀.gpr .a4).toNat (s₀.gpr .a4).toNat F ∧ slotBlk m b stLo = Fin

/-- Before group `g`. -/
def WI (s₀ s₉ : State) (b : Addr) (L : Addr → Nat → Nat → Mem → (Nat → BitVec 64) → Prop) (g : Nat)
    (s : State) : Prop :=
  4 * g < (s₀.gpr .a4).toNat ∧ WB s₀ s₉ b g s ∧ L b g 0 s.mem (Q s)

/-- After the last group. -/
structure WD (s₀ s₉ : State) (b : Addr) (F : Nat → Spec.Aes.State) (Fin : Spec.Aes.State) (s : State) :
    Prop where
  keep : ∀ r, r ∉ sboxWrites → r ≠ kp → r ≠ .a3 → r ≠ .a4 → s.gpr r = s₉.gpr r
  rd : s.rd = s₉.rd
  wr : s.wr = s₉.wr
  sp : s.sp = s₉.sp
  frame : Frame (wRegions b (s₀.gpr .a3) (s₀.gpr .a4).toNat) s₉.mem s.mem
  data : EcbInv s₀.mem s.mem (s₀.gpr .a3) (s₀.gpr .a4).toNat (s₀.gpr .a4).toNat F
  fin : slotBlk s.mem b stLo = Fin

theorem wideLoadFull_eq (load : Nat → List Instr) :
    wideLoadFull load = load 0 ++ load 1 ++ load 2 ++ load 3 := by
  simp only [wideLoadFull, List.range_succ, List.range_zero, List.nil_append, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

theorem wideStoreFull_eq (store : Nat → List Instr) :
    wideStoreFull store = store 0 ++ store 1 ++ store 2 ++ store 3 ++
      ([.addi .a3 .a3 64, .addi .a4 .a4 (-4)] : List Instr) := by
  simp only [wideStoreFull, List.range_succ, List.range_zero, List.nil_append, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

section Group

variable {load store : Nat → List Instr} {crypt4 : Prog isa}
  {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
  {L S : Addr → Nat → Nat → Mem → (Nat → BitVec 64) → Prop} {F : Nat → Spec.Aes.State}
  {Fin : Spec.Aes.State} {s₀ s₉ : State} {X b : Addr}
  (hw : WideOk s₀ load store f L S F Fin) (hs : FSetup true (16 * ·) s₀ s₉ X b)
include hw hs

omit hw hs in
/-- `addi t0, a4, -imm` during a group. -/
theorem wide_t0 {I : Nat → Nat → Mem → (Nat → BitVec 64) → Prop} {g k : Nat} {s s' : State}
    {v : BitVec 64} (hb : WB s₀ s₉ b g s) (hl : I g k s.mem (Q s)) (u : Upd s s' t0 v) :
    WB s₀ s₉ b g s' ∧ I g k s'.mem (Q s') :=
  ⟨hb.foot (Foot.upd u (by decide)), by rw [u.mem, Q_upd u fun i => (q_neW i).1]; exact hl⟩

omit hw hs in
/-- `t0 := a4 - 3` is zero when three blocks are left, of two or three. -/
theorem sub3_zero {g : Nat} {s s' : State} (hb : WB s₀ s₉ b g s)
    (u : Upd s s' t0 (s.gpr .a4 - BitVec.ofNat 64 3)) (h2 : 2 ≤ (s₀.gpr .a4).toNat - 4 * g)
    (h3 : (s₀.gpr .a4).toNat - 4 * g < 4) :
    isa.eval (.zero t0) s' = some (decide ((s₀.gpr .a4).toNat - 4 * g = 3)) := by
  rw [eval_zero, u.gpr, hb.a4]
  congr 1
  have : (s₀.gpr .a4).toNat - 4 * g = 2 ∨ (s₀.gpr .a4).toNat - 4 * g = 3 := by omega
  rcases this with h | h <;> rw [h] <;> decide

/-- The loads of a group, after `srli t0, a4, 2`. -/
theorem wideLoad_wp {g : Nat} (hg : 4 * g < (s₀.gpr .a4).toNat) {s : State} (hb : WB s₀ s₉ b g s)
    (hl : L b g 0 s.mem (Q s))
    (hev : isa.eval (.nonzero t0) s = some (decide (4 ≤ (s₀.gpr .a4).toNat - 4 * g))) :
    WP isa (.ite (.nonzero t0) (.block (wideLoadFull load)) (wideLoadTail load)) s fun s' =>
      WB s₀ s₉ b g s' ∧ L b g (min 4 ((s₀.gpr .a4).toNat - 4 * g)) s'.mem (Q s') := by
  have hn : (s₀.gpr .a4).toNat < 2 ^ 64 := (s₀.gpr .a4).isLt
  have step : ∀ k, k < 4 → 4 * g + k < (s₀.gpr .a4).toNat → ∀ s, WB s₀ s₉ b g s → L b g k s.mem (Q s) →
      ∀ {P : State → Prop}, (∀ s', WB s₀ s₉ b g s' → L b g (k + 1) s'.mem (Q s') → P s') →
        WP isa (.block (load k)) s P :=
    fun k hk hkn s hb hl P h => WP.mono (hw.load hs g k hk hkn s hb hl) fun s' ⟨f', l⟩ => h s' (hb.foot f') l
  refine WP.ite (decide (4 ≤ (s₀.gpr .a4).toNat - 4 * g)) hev (fun hd => ?_) (fun hd => ?_)
  · have h4 : 4 ≤ (s₀.gpr .a4).toNat - 4 * g := by simpa using hd
    rw [wideLoadFull_eq]
    repeat rw [WP.block_append_iff (M := isa)]
    refine step 0 (by omega) (by omega) _ hb hl fun s₁ b₁ l₁ => ?_
    refine step 1 (by omega) (by omega) _ b₁ l₁ fun s₂ b₂ l₂ => ?_
    refine step 2 (by omega) (by omega) _ b₂ l₂ fun s₃ b₃ l₃ => ?_
    refine step 3 (by omega) (by omega) _ b₃ l₃ fun s₄ b₄ l₄ => ?_
    rw [show min 4 ((s₀.gpr .a4).toNat - 4 * g) = 3 + 1 by omega]; exact ⟨b₄, l₄⟩
  · have h4 : (s₀.gpr .a4).toNat - 4 * g < 4 := by simpa using hd
    unfold wideLoadTail
    refine WP.seq ?_
    rw [WP.block_append_iff (M := isa)]
    refine step 0 (by omega) (by omega) _ hb hl fun s₁ b₁ l₁ => ?_
    refine wp_subi (imm := 1) (by decide) fun s₂ u₂ => WP.block_nil ?_
    obtain ⟨b₂, l₂⟩ := wide_t0 (I := L b) b₁ l₁ u₂
    have t₂ : s₂.gpr t0 = BitVec.ofNat 64 ((s₀.gpr .a4).toNat - 4 * g - 1) := by
      rw [u₂.gpr, b₁.a4, ofNat_sub_ofNat' (by omega)]
    refine WP.ite (decide ((s₀.gpr .a4).toNat - 4 * g - 1 ≠ 0))
      (Steps.eval_nonzero_ofNat s₂ t0 (by omega) t₂) (fun hd => ?_) (fun hd => ?_)
    · have h2 : 2 ≤ (s₀.gpr .a4).toNat - 4 * g := by simp at hd; omega
      refine WP.seq ?_
      rw [WP.block_append_iff (M := isa)]
      refine step 1 (by omega) (by omega) _ b₂ l₂ fun s₃ b₃ l₃ => ?_
      refine wp_subi (imm := 3) (by decide) fun s₄ u₄ => WP.block_nil ?_
      obtain ⟨b₄, l₄⟩ := wide_t0 (I := L b) b₃ l₃ u₄
      have z₄ := sub3_zero b₃ u₄ h2 h4
      refine WP.ite (decide ((s₀.gpr .a4).toNat - 4 * g = 3)) z₄ (fun hd => ?_) (fun hd => ?_)
      · have h3 : min 4 ((s₀.gpr .a4).toNat - 4 * g) = 2 + 1 := by simp at hd; omega
        refine step 2 (by omega) (by omega) _ b₄ l₄ fun s₅ b₅ l₅ => ?_
        rw [h3]; exact ⟨b₅, l₅⟩
      · have h3 : min 4 ((s₀.gpr .a4).toNat - 4 * g) = 1 + 1 := by simp at hd; omega
        refine WP.block_nil ?_
        rw [h3]; exact ⟨b₄, l₄⟩
    · have h1 : min 4 ((s₀.gpr .a4).toNat - 4 * g) = 0 + 1 := by simp at hd; omega
      refine WP.block_nil ?_
      rw [h1]; exact ⟨b₂, l₂⟩

/-- After the stores of group `g` (`s₁`, before the last of `a3` and `a4`
are updated, in `s'`): after the last group, or before group `g + 1`. -/
theorem wide_end {g : Nat} (hg : 4 * g < (s₀.gpr .a4).toNat) {s₁ s' : State} (hb : WB s₀ s₉ b g s₁)
    (hl : S b g (min 4 ((s₀.gpr .a4).toNat - 4 * g)) s₁.mem (Q s₁)) (hm : s'.mem = s₁.mem)
    (hrd : s'.rd = s₁.rd) (hwr : s'.wr = s₁.wr) (hsp : s'.sp = s₁.sp)
    (ho : ∀ r, r ≠ .a3 → r ≠ .a4 → s'.gpr r = s₁.gpr r)
    (h4 : s'.gpr .a4 = BitVec.ofNat 64 ((s₀.gpr .a4).toNat - 4 * (g + 1)))
    (h3 : 4 * g + 4 < (s₀.gpr .a4).toNat → s'.gpr .a3 = s₀.gpr .a3 + BitVec.ofNat 64 (64 * (g + 1))) :
    (isa.eval (.nonzero .a4) s' = some false ∧ WD s₀ s₉ b F Fin s') ∨
      (isa.eval (.nonzero .a4) s' = some true ∧ WI s₀ s₉ b L (g + 1) s') := by
  have hn : (s₀.gpr .a4).toNat < 2 ^ 64 := (s₀.gpr .a4).isLt
  have hQ : Q s' = Q s₁ := funext fun i => ho _ (q_neW i).2.2.2.2.1 (q_neW i).2.2.2.2.2.1
  have keep : ∀ r, r ∉ sboxWrites → r ≠ kp → r ≠ .a3 → r ≠ .a4 → s'.gpr r = s₉.gpr r :=
    fun r h1 h2 h3 h4 => (ho r h3 h4).trans (hb.keep r h1 h2 h3 h4)
  by_cases hl4 : (s₀.gpr .a4).toNat ≤ 4 * g + 4
  · have e : min 4 ((s₀.gpr .a4).toNat - 4 * g) = (s₀.gpr .a4).toNat - 4 * g := by omega
    rw [e] at hl
    have d := hw.done hs g _ _ hg hl4 hl
    refine .inl ⟨by rw [Steps.eval_nonzero_ofNat s' .a4 (by omega) h4,
      show (s₀.gpr .a4).toNat - 4 * (g + 1) = 0 by omega]; rfl,
      ⟨keep, hrd.trans hb.rd, hwr.trans hb.wr, hsp.trans hb.sp, by rw [hm]; exact hb.frame,
        by rw [hm]; exact d.1, by rw [hm]; exact d.2⟩⟩
  · have e : min 4 ((s₀.gpr .a4).toNat - 4 * g) = 4 := by omega
    rw [e] at hl
    refine .inr ⟨by rw [Steps.eval_nonzero_ofNat s' .a4 (by omega) h4,
      decide_eq_true (show (s₀.gpr .a4).toNat - 4 * (g + 1) ≠ 0 by omega)], by omega,
      ⟨h3 (by omega), h4, keep, hrd.trans hb.rd, hwr.trans hb.wr, hsp.trans hb.sp,
        by rw [hm]; exact hb.frame⟩, ?_⟩
    rw [hm, hQ]; exact hw.next hs g _ _ (by omega) hl

/-- The stores of a group, from `srli t0, a4, 2`. -/
theorem wideStore_wp {g : Nat} (hg : 4 * g < (s₀.gpr .a4).toNat) {s : State} (hb : WB s₀ s₉ b g s)
    (hl : S b g 0 s.mem (Q s)) :
    WP isa (.seq (.block [shrI t0 .a4 2]) (.ite (.nonzero t0) (.block (wideStoreFull store))
      (wideStoreTail store))) s fun s' =>
      (isa.eval (.nonzero .a4) s' = some false ∧ WD s₀ s₉ b F Fin s') ∨
        (isa.eval (.nonzero .a4) s' = some true ∧ WI s₀ s₉ b L (g + 1) s') := by
  have hn : (s₀.gpr .a4).toNat < 2 ^ 64 := (s₀.gpr .a4).isLt
  have step : ∀ k, k < 4 → 4 * g + k < (s₀.gpr .a4).toNat → ∀ s, WB s₀ s₉ b g s → S b g k s.mem (Q s) →
      ∀ {P : State → Prop}, (∀ s', WB s₀ s₉ b g s' → S b g (k + 1) s'.mem (Q s') → P s') →
        WP isa (.block (store k)) s P :=
    fun k hk hkn s hb hl P h => WP.mono (hw.store hs g k hk hkn s hb hl) fun s' ⟨f', l⟩ => h s' (hb.foot f') l
  refine shr2_wp (k := (s₀.gpr .a4).toNat - 4 * g) (by omega) hb.a4 fun s₄ u₄ ev₄ => ?_
  have b₄ := hb.foot (Foot.upd u₄ (by decide))
  have l₄ : S b g 0 s₄.mem (Q s₄) := by rw [u₄.mem, Q_upd u₄ fun i => (q_neW i).1]; exact hl
  refine WP.ite (decide (4 ≤ (s₀.gpr .a4).toNat - 4 * g)) ev₄ (fun hd => ?_) (fun hd => ?_)
  · -- Four blocks.
    have h4 : 4 ≤ (s₀.gpr .a4).toNat - 4 * g := by simpa using hd
    rw [wideStoreFull_eq]
    repeat rw [WP.block_append_iff (M := isa)]
    refine step 0 (by omega) (by omega) _ b₄ l₄ fun s₅ b₅ l₅ => ?_
    refine step 1 (by omega) (by omega) _ b₅ l₅ fun s₆ b₆ l₆ => ?_
    refine step 2 (by omega) (by omega) _ b₆ l₆ fun s₇ b₇ l₇ => ?_
    refine step 3 (by omega) (by omega) _ b₇ l₇ fun s₈ b₈ l₈ => ?_
    refine wp_addi (imm := 64) (by decide) fun t₁ v₁ => wp_subi (imm := 4) (by decide)
      fun t₂ v₂ => WP.block_nil ?_
    refine wide_end hw hs hg b₈ (by rw [show min 4 ((s₀.gpr .a4).toNat - 4 * g) = 3 + 1 by omega]; exact l₈)
      (by rw [v₂.mem, v₁.mem]) (by rw [v₂.rd, v₁.rd]) (by rw [v₂.wr, v₁.wr]) (by rw [v₂.sp, v₁.sp])
      (fun r h3 h4 => by rw [v₂.other _ h4, v₁.other _ h3]) ?_ fun _ => ?_
    · rw [v₂.gpr, v₁.other _ (by decide), b₈.a4, ofNat_sub_ofNat' h4,
        show (s₀.gpr .a4).toNat - 4 * g - 4 = (s₀.gpr .a4).toNat - 4 * (g + 1) by omega]
    · rw [v₂.other _ (by decide), v₁.gpr, b₈.a3, off_add64]
  · -- The last one to three blocks.
    have h4 : (s₀.gpr .a4).toNat - 4 * g < 4 := by simpa using hd
    unfold wideStoreTail
    refine WP.seq ?_
    rw [WP.block_append_iff (M := isa)]
    refine step 0 (by omega) (by omega) _ b₄ l₄ fun s₅ b₅ l₅ => ?_
    refine wp_subi (imm := 1) (by decide) fun s₆ u₆ => WP.block_nil ?_
    obtain ⟨b₆, l₆⟩ := wide_t0 (I := S b) b₅ l₅ u₆
    have t₆ : s₆.gpr t0 = BitVec.ofNat 64 ((s₀.gpr .a4).toNat - 4 * g - 1) := by
      rw [u₆.gpr, b₅.a4, ofNat_sub_ofNat' (by omega)]
    refine WP.seq (WP.mono (Q := fun (s : State) => WB s₀ s₉ b g s ∧
      S b g ((s₀.gpr .a4).toNat - 4 * g) s.mem (Q s)) ?_ fun (s : State) ⟨bs, ls⟩ => ?_)
    · refine WP.ite (decide ((s₀.gpr .a4).toNat - 4 * g - 1 ≠ 0))
        (Steps.eval_nonzero_ofNat s₆ t0 (by omega) t₆) (fun hd => ?_) (fun hd => ?_)
      · have h2 : 2 ≤ (s₀.gpr .a4).toNat - 4 * g := by simp at hd; omega
        refine WP.seq ?_
        rw [WP.block_append_iff (M := isa)]
        refine step 1 (by omega) (by omega) _ b₆ l₆ fun s₇ b₇ l₇ => ?_
        refine wp_subi (imm := 3) (by decide) fun s₈ u₈ => WP.block_nil ?_
        obtain ⟨b₈, l₈⟩ := wide_t0 (I := S b) b₇ l₇ u₈
        have z₈ := sub3_zero b₇ u₈ h2 h4
        refine WP.ite (decide ((s₀.gpr .a4).toNat - 4 * g = 3)) z₈ (fun hd => ?_) (fun hd => ?_)
        · have h3 : (s₀.gpr .a4).toNat - 4 * g = 2 + 1 := by simp at hd; omega
          refine step 2 (by omega) (by omega) _ b₈ l₈ fun s₉' b₉ l₉ => ?_
          rw [h3]; exact ⟨b₉, l₉⟩
        · have h3 : (s₀.gpr .a4).toNat - 4 * g = 1 + 1 := by simp at hd; omega
          exact WP.block_nil (by rw [h3]; exact ⟨b₈, l₈⟩)
      · have h1 : (s₀.gpr .a4).toNat - 4 * g = 0 + 1 := by simp at hd; omega
        exact WP.block_nil (by rw [h1]; exact ⟨b₆, l₆⟩)
    · refine wp_li (imm := 0) (by decide) fun s' u' => WP.block_nil ?_
      refine wide_end hw hs hg bs (by rw [show min 4 ((s₀.gpr .a4).toNat - 4 * g) =
          (s₀.gpr .a4).toNat - 4 * g by omega]; exact ls) u'.mem u'.rd u'.wr u'.sp
        (fun r _ h4 => u'.other r h4) ?_ fun h => absurd h (by omega)
      rw [u'.gpr, show (s₀.gpr .a4).toNat - 4 * (g + 1) = 0 by omega]

/-- One group: from before group `g`, to after the last group (`a4 = 0`) or
before group `g + 1`. -/
theorem wideGroup_wp (hc : CryptOk crypt4 f) {g : Nat} {s : State} (hi : WI s₀ s₉ b L g s) :
    WP isa (wideGroup load store crypt4) s fun s' =>
      (isa.eval (.nonzero .a4) s' = some false ∧ WD s₀ s₉ b F Fin s') ∨
        (isa.eval (.nonzero .a4) s' = some true ∧ WI s₀ s₉ b L (g + 1) s') := by
  obtain ⟨hg, hb, hl⟩ := hi
  unfold wideGroup
  refine shr2_wp (k := (s₀.gpr .a4).toNat - 4 * g) (by have := (s₀.gpr .a4).isLt; omega) hb.a4
    fun s₁ u₁ ev₁ => ?_
  have b₁ := hb.foot (Foot.upd u₁ (by decide))
  refine WP.seq (WP.mono (wideLoad_wp hw hs hg b₁ (by rw [u₁.mem, Q_upd u₁ fun i => (q_neW i).1]; exact hl)
    ev₁) fun s₂ ⟨b₂, l₂⟩ => ?_)
  refine WP.seq (WP.mono (wide_crypt hs hc b₂) fun s₃ ⟨b₃, f₃, i₃⟩ => ?_)
  exact wideStore_wp hw hs hg b₃ (hw.crypt hs g _ _ _ _ hg l₂ f₃ i₃)

/-- The loop over the groups. -/
theorem wideLoop_wp (hc : CryptOk crypt4 f) {s : State} (hi : WI s₀ s₉ b L 0 s) :
    WP isa (.loop (wideGroup load store crypt4) (.nonzero .a4)) s (WD s₀ s₉ b F Fin) := by
  refine WP.loop (M := isa) (fun k s => ∃ g, k = (s₀.gpr .a4).toNat - 4 * g ∧ WI s₀ s₉ b L g s)
    (fun k s ⟨g, hk, hg⟩ => WP.mono (wideGroup_wp hw hs hc hg) fun s' h => ?_) (s₀.gpr .a4).toNat s
    ⟨0, by omega, hi⟩
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨z, d⟩
  · exact .inr ⟨z, (s₀.gpr .a4).toNat - 4 * (g + 1), by have := hg.1; omega, g + 1, rfl, d⟩

end Group

/-! ## The whole function -/

/-- A mode with `WideOk` meets `blockKRISCV64 M`, when `M` of the blocks is
`F`'s and its chaining value `Fin`. -/
theorem wide_correct (M : AesCbc.Mode) {load store : Nat → List Instr} {crypt4 : Prog isa}
    {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    {L S : Addr → Nat → Nat → Mem → (Nat → BitVec 64) → Prop} {F : Nat → Spec.Aes.State}
    {Fin : Spec.Aes.State} (hc : CryptOk crypt4 f) {s₀ : State} (hp : (blockKRISCV64 M).pre s₀)
    (hw : WideOk s₀ load store f L S F Fin)
    (hout : M.out (s₀.gpr .a1).toNat (Spec.Aes.bytesAt s₀.mem (s₀.gpr .a0) (16 * ((s₀.gpr .a1).toNat + 1)))
      (Spec.Aes.bytesAt s₀.mem (s₀.gpr .a2) 16) (Spec.Cbc.blocksAt s₀.mem (s₀.gpr .a3) (s₀.gpr .a4).toNat) =
        (List.range (s₀.gpr .a4).toNat).map fun j => (F j).toList)
    (hch : M.chain (s₀.gpr .a1).toNat (Spec.Aes.bytesAt s₀.mem (s₀.gpr .a0) (16 * ((s₀.gpr .a1).toNat + 1)))
      (Spec.Aes.bytesAt s₀.mem (s₀.gpr .a2) 16) (Spec.Cbc.blocksAt s₀.mem (s₀.gpr .a3) (s₀.gpr .a4).toNat) =
        Fin.toList) :
    WP isa (wide load store crypt4) s₀ fun s' =>
      (∀ r ∈ RISCV64.preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
        (blockKRISCV64 M).post s₀ s' := by
  let n := (s₀.gpr .a4).toNat
  let St := s₀.gpr .a2
  let D := s₀.gpr .a3
  have hp' : framePre true (16 * ·) s₀ := hp
  have dDSt : Region.Disjoint ⟨D, 16 * n⟩ ⟨St, 16⟩ := hp.2.2.2.1
  let Res : State → Prop := fun s => regBlock (Q s) 0 = Fin ∧ EcbInv s₀.mem s.mem D n n F
  refine WP.mono (frame_wp (Res := Res) hp' fun s₉ X b hsF => ?_) fun s' ⟨hg, hra, hm⟩ => ⟨hg, hra, ?_⟩
  · -- The state into its slots.
    have hb₉ := hsF.base
    unfold wideIn
    refine slot_st hsF.scr hb₉ (by decide) fun s₁ u₁ => ?_
    refine slot_st (hsF.scr.congr u₁.wr (by rw [u₁.gpr])) (by rw [u₁.gpr, hb₉]) (by decide)
      fun s₂ u₂ => WP.block_nil ?_
    have m₂ : s₂.mem = (s₉.mem.writeW (b + BitVec.ofNat 64 (8 * stLo)) (s₉.gpr (q 0))).writeW
        (b + BitVec.ofNat 64 (8 * (stLo + 1))) (s₉.gpr (q 4)) := by rw [u₂.mem, u₁.mem, u₁.gpr]
    have g₂ : s₂.gpr = s₉.gpr := by rw [u₂.gpr, u₁.gpr]
    have hi : WI s₀ s₉ b L 0 s₂ := by
      refine ⟨by have := hsF.hn0; omega, ⟨by rw [g₂, hsF.a3]; simp, by rw [g₂, hsF.a4]; simp,
        fun r _ _ _ _ => by rw [g₂], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr], by rw [u₂.sp, u₁.sp], ?_⟩,
        hw.init hsF _ _ ?_ ?_⟩
      · rw [m₂]
        exact (wSlot_frame (s₀ := s₀) _ (by decide) (by decide) _).trans
          (wSlot_frame (s₀ := s₀) _ (by decide) (by decide) _)
      · rw [m₂]
        refine hsF.f₀.trans ((slot2_frame _ _ (by decide) _ _).sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
        simp only [List.mem_singleton] at hr; subst hr; exact hsF.sub' (by decide)
      · rw [m₂, slot2_self _ _ (by decide)]; exact (regBlock_wBlk (Q s₉) 0).symm.trans hsF.st
    refine WP.mono (wideLoop_wp hw hsF hc hi) fun s₃ d₃ => ?_
    -- The state from its slots.
    have hb₃ : s₃.gpr sb = b := (d₃.keep sb (by decide) (by decide) (by decide) (by decide)).trans hb₉
    have hscr₃ : Scr s₃ X 2048 := hsF.scr.congr d₃.wr (by rw [hb₃, hb₉])
    unfold wideOut
    refine slot_ld hscr₃ hb₃ (by decide) fun s₄ u₄ => ?_
    refine slot_ld (hscr₃.congr u₄.wr (by rw [u₄.other _ (by decide)])) (by rw [u₄.other _ (by decide), hb₃])
      (by decide) fun s₅ u₅ => WP.block_nil ?_
    have o₅ : ∀ r, r ≠ q 0 → r ≠ q 4 → s₅.gpr r = s₃.gpr r := fun r h0 h4 => by
      rw [u₅.other _ h4, u₄.other _ h0]
    have m₅ : s₅.mem = s₃.mem := by rw [u₅.mem, u₄.mem]
    exact { base := by rw [o₅ _ (by decide) (by decide)]; exact hb₃
            ra := by rw [o₅ _ (by decide) (by decide), d₃.keep .ra (by decide) (by decide) (by decide) (by decide)]
            rd := by rw [u₅.rd, u₄.rd, d₃.rd]
            wr := by rw [u₅.wr, u₄.wr, d₃.wr]
            sp := by rw [u₅.sp, u₄.sp, d₃.sp]
            frame := by
              rw [m₅]
              refine d₃.frame.mono fun r hr => ?_
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
              rcases hr with rfl | rfl | rfl <;> simp
            res := ⟨by
                rw [regBlock_wBlk, ← d₃.fin]
                show wBlk (s₅.gpr (q 0)) (s₅.gpr (q 4)) = _
                rw [u₅.other _ (by decide), u₄.gpr, u₅.gpr, u₄.mem]; rfl,
              by rw [m₅]; exact d₃.data⟩ }
  · show Spec.Cbc.blocksAt s'.mem D n = M.out _ _ (Spec.Aes.bytesAt s₀.mem St 16) (Spec.Cbc.blocksAt s₀.mem D n) ∧
      Spec.Aes.bytesAt s'.mem St 16 = M.chain _ _ (Spec.Aes.bytesAt s₀.mem St 16) (Spec.Cbc.blocksAt s₀.mem D n)
    rcases hm with ⟨hn0, hmem⟩ | ⟨s, ⟨hst, hdat⟩, hmem⟩
    · rw [hmem, show n = 0 from hn0, show Spec.Cbc.blocksAt s₀.mem D 0 = [] from rfl, M.out_nil, M.chain_nil]
      exact ⟨rfl, rfl⟩
    have n16 : 16 * n < 2 ^ 64 := by
      refine Nat.lt_of_not_le fun hc => dDSt St ?_ (by simp [Region.Contains])
      simp only [Region.Contains]
      have := (St - D).isLt
      omega
    have hd : EcbInv s₀.mem s'.mem D n n F := by
      rw [hmem]
      refine ecbInv_frame (frame_writeW2 _ _ _ _) (fun r hr => ?_) n16 hdat
      simp only [List.mem_singleton] at hr; subst hr; exact dDSt
    refine ⟨?_, ?_⟩
    · rw [hout, blocksAt_states, statesAt_of_ecbInv hd, List.map_map]; rfl
    · rw [hmem, bytesAt_writeW2 _ _ _ _ (regBlock_bytes hst), hch]

/-! ## Constant time, and the call -/

/-- `wide load store crypt4`, when taint tracking accepts it, is constant
time for `blockKRISCV64 M`. -/
theorem wide_ct (M : AesCbc.Mode) {c : Prog isa} {h}
    (hck : (taint.check (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5]) c h).isSome = true) :
    ConstantTime isa (blockKRISCV64 M).pre (blockKRISCV64 M).pub c :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5]) (chain_agree true) hck

end VG.Proof.Aes.RISCV64
