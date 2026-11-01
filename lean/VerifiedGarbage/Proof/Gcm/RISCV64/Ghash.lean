module

public import VerifiedGarbage.Proof.Gcm.RISCV64.Mul
public import VerifiedGarbage.Spec.Gcm.Contract
public import VerifiedGarbage.Proof.Gcm.Contract
meta import VerifiedGarbage.Proof.Gcm.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
public import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Gcm.RISCV64.Lit
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Gcm.RISCV64.Mul
meta import VerifiedGarbage.Spec.Gcm.Contract
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Framework.RISCV64.Keep
meta import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
meta import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.CallLay
meta import VerifiedGarbage.Proof.Gcm.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit

/-!
# GHASH on RISC-V: the whole function

Untrusted: everything here is checked by Lean. A block (`block_ok`): `x`
from the data and `Y`, and the product by the table (`mul_loop`); the
blocks (`blocks_loop`); and the function (`ghash_ok`): the table, `Y` in,
the blocks, `Y` out and the table zeroed, in the frame of 2048 bytes below
the stack pointer, against a per-target contract (`ghashX`).
-/

@[expose] public section

namespace VG.Proof.Gcm.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Gcm.RISCV64 VG.WriteBytes
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom mul ofBytes)
open VG.Proof.Gcm (mulSteps)

/-! ## Blocks as words -/

theorem be8 (z : BitVec 64) :
    ((z >>> 56).setWidth 8 ++ (z >>> 48).setWidth 8 ++ (z >>> 40).setWidth 8 ++ (z >>> 32).setWidth 8 ++
      (z >>> 24).setWidth 8 ++ (z >>> 16).setWidth 8 ++ (z >>> 8).setWidth 8 ++ (z >>> 0).setWidth 8 :
        BitVec 64) = z := by
  apply BitVec.eq_of_toNat_eq
  simp only [Proof.Gcm.toNat_append, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  have := z.isLt
  omega

/-- A block, as the two words `loadBE64` reads. -/
theorem blockAt_hOf (m : Mem) (p : Addr) : blockAt m p = hOf m p := by
  simp only [blockAt, Spec.Aes.bytesAt, List.range_succ, List.range_zero, List.nil_append,
    List.map_cons, List.map_nil, List.cons_append, Proof.Gcm.ofBytes_16]
  rfl

/-- The block of the bytes of two words, the high word first. -/
theorem ofBytes_beBytes (z0 z1 : BitVec 64) :
    ofBytes (ByteLoad.beBytes 8 z0 ++ ByteLoad.beBytes 8 z1) = w2 z0 z1 := by
  simp only [ByteLoad.beBytes, List.range_succ, List.range_zero, List.nil_append,
    List.map_cons, List.map_nil, List.cons_append, Proof.Gcm.ofBytes_16, Nat.reduceMul, Nat.reduceSub]
  rw [be8 z0, be8 z1]

/-! ## The blocks -/

/-- The registers the blocks write. -/
def blkRegs : List Reg := [Z0, Z1, X0, X1, U0, U1, M, T, P, DP, N]

/-- After `i` of the `n₀` blocks at `D`, from `sY`: `Z` is `GHASH_H` from
`Y₀` over them (`H` and the blocks from the memory `m₀`). -/
structure BlkInv (H Y₀ : Block) (D : Addr) (m₀ : Mem) (n₀ : Nat) (B : Addr) (sY : State) (i : Nat)
    (s : State) : Prop where
  y : w2 (s.gpr Z0) (s.gpr Z1) = ghashFrom H Y₀ (blocksAt m₀ D i)
  dp : s.gpr DP = D + BitVec.ofNat 64 (16 * i)
  n : s.gpr N = BitVec.ofNat 64 (n₀ - i)
  e : s.gpr E = B + BitVec.ofNat 64 2048
  mem : s.mem = sY.mem
  keep : ∀ r, r ∉ blkRegs → s.gpr r = sY.gpr r
  rd : s.rd = sY.rd
  wr : s.wr = sY.wr
  sp : s.sp = sY.sp

theorem block_ok {H Y₀ : Block} {D B : Addr} {m₀ : Mem} {n₀ : Nat} {sY : State} (hF : FrameOk B sY)
    (ht : Tab H B sY.mem 128) (hsp : sY.sp = B)
    (hd : ∀ i < n₀, InRegions (sY.rd ++ sY.wr) (D + BitVec.ofNat 64 (16 * i)) 16)
    (hdm : ∀ i < n₀, hOf sY.mem (D + BitVec.ofNat 64 (16 * i)) = blockAt m₀ (D + BitVec.ofNat 64 (16 * i)))
    (hn₀ : n₀ < 2 ^ 64) {i : Nat} (hi : i < n₀) {s : State} (hs : BlkInv H Y₀ D m₀ n₀ B sY i s) :
    WP isa block s (BlkInv H Y₀ D m₀ n₀ B sY (i + 1)) := by
  refine WP.seq ?_
  rw [blockInit, List.append_assoc]
  refine load2_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [hs.rd, hs.wr, hs.dp]; exact hd i hi) fun s₁ h0 h1 g₁ m₁ rd₁ wr₁ sp₁ => ?_
  refine wp_xor fun s₂ u₂ => wp_xor fun s₃ u₃ => wp_li (imm := 0) (by decide) fun s₄ u₄ =>
    wp_li (imm := 0) (by decide) fun s₅ u₅ => wp_addSp (by decide) fun s₆ u₆ => WP.block_nil ?_
  -- The factor `x = Y ⊕ X`.
  let x : Block := ghashFrom H Y₀ (blocksAt m₀ D i) ^^^ blockAt m₀ (D + BitVec.ofNat 64 (16 * i))
  have g₆ : ∀ r, r ∉ mulRegs → s₆.gpr r = s.gpr r := fun r hr => by
    simp only [mulRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₆.other _ hr.2.2.2.2.2.2.2.2, u₅.other _ hr.2.1, u₄.other _ hr.1, u₃.other _ hr.2.2.2.1,
      u₂.other _ hr.2.2.1, g₁ _ hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2.2.2.2.1]
  have hm₆ : s₆.mem = sY.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁, hs.mem]
  have hM : MulInv x H B s₆ 0 s₆ := by
    refine ⟨?_, ?_, ?_, ?_, rfl, fun _ _ => rfl, rfl, rfl, rfl⟩
    · rw [u₆.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₅.other _ (by decide), u₄.gpr]
      exact w2_zero
    · rw [u₆.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₅.other _ (by decide),
        u₄.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₃.other _ (by decide), u₂.gpr,
        u₂.other _ (by decide), u₂.other _ (by decide), h0, h1, g₁ _ (by decide) (by decide) (by decide),
        g₁ _ (by decide) (by decide) (by decide), ← w2_xor, hs.y, hs.mem, hs.dp,
        show w2 (ByteLoad.be64 sY.mem (D + BitVec.ofNat 64 (16 * i)) 0)
          (ByteLoad.be64 sY.mem (D + BitVec.ofNat 64 (16 * i)) 8) = _ from hdm i hi,
        BitVec.xor_comm, Nat.mul_zero, BitVec.shiftLeft_zero]
    · rw [u₆.gpr, u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁, hs.sp, hsp]
    · rw [g₆ _ (by decide)]; exact hs.e
  refine WP.seq (WP.mono (mul_loop (hF.of_wr (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁, hs.wr]))
    (by rw [hm₆]; exact ht) hM) fun s₇ h₇ => ?_)
  refine wp_addi (by decide) fun s₈ u₈ => wp_subi (by decide) fun s₉ u₉ => WP.block_nil ?_
  have hz : w2 (s₇.gpr Z0) (s₇.gpr Z1) = mul x H := h₇.z
  refine ⟨?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [u₉.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₈.other _ (by decide), hz,
      Proof.Gcm.ghashFrom_blocksAt_succ]
  · rw [u₉.other _ (by decide), u₈.gpr, h₇.keep _ (by decide), g₆ _ (by decide), hs.dp, BitVec.add_assoc,
      BitVec.ofNat_add_ofNat]
    congr 2
  · rw [u₉.gpr, u₈.other _ (by decide), h₇.keep _ (by decide), g₆ _ (by decide), hs.n]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := n₀ - i) (by omega), Nat.mod_eq_of_lt (a := 1) (by decide)]
    omega
  · rw [u₉.other _ (by decide), u₈.other _ (by decide)]; exact h₇.e
  · rw [u₉.mem, u₈.mem, h₇.mem, hm₆]
  · simp only [blkRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    have hr' : r ∉ mulRegs := by
      simp only [mulRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.1⟩
    rw [u₉.other _ hr.2.2.2.2.2.2.2.2.2.2, u₈.other _ hr.2.2.2.2.2.2.2.2.2.1, h₇.keep _ hr', g₆ _ hr']
    exact hs.keep r (by simp only [blkRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]; exact hr)
  · rw [u₉.rd, u₈.rd, h₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]; exact hs.rd
  · rw [u₉.wr, u₈.wr, h₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]; exact hs.wr
  · rw [u₉.sp, u₈.sp, h₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]; exact hs.sp

theorem blocks_loop {H Y₀ : Block} {D B : Addr} {m₀ : Mem} {n₀ : Nat} {sY : State} (hF : FrameOk B sY)
    (ht : Tab H B sY.mem 128) (hsp : sY.sp = B)
    (hd : ∀ i < n₀, InRegions (sY.rd ++ sY.wr) (D + BitVec.ofNat 64 (16 * i)) 16)
    (hdm : ∀ i < n₀, hOf sY.mem (D + BitVec.ofNat 64 (16 * i)) = blockAt m₀ (D + BitVec.ofNat 64 (16 * i)))
    (hn₀ : n₀ < 2 ^ 64) (hpos : 0 < n₀) {s : State} (hs : BlkInv H Y₀ D m₀ n₀ B sY 0 s) :
    WP isa (.loop block (.nonzero N)) s (BlkInv H Y₀ D m₀ n₀ B sY n₀) := by
  refine WP.loop (M := isa) (fun k s' => ∃ i, k = n₀ - i ∧ i < n₀ ∧ BlkInv H Y₀ D m₀ n₀ B sY i s')
    (fun k s' ⟨i, hk, hi, hb⟩ => WP.mono (block_ok hF ht hsp hd hdm hn₀ hi hb) fun s'' hb' => ?_) n₀ s
    ⟨0, rfl, hpos, hs⟩
  have hev := eval_nonzero_ofNat s'' N (k := n₀ - (i + 1)) (by omega) hb'.n
  by_cases hl : i + 1 = n₀
  · exact .inl ⟨by rw [hev]; simp [hl], hl ▸ hb'⟩
  · exact .inr ⟨by rw [hev]; simp; omega, n₀ - (i + 1), by omega, i + 1, rfl, by omega, hb'⟩

/-! ## `Y` back -/

theorem bytesAt_writeBytes_self (m : Mem) (q : Addr) {zs : List Byte} {n : Nat} (hn : zs.length = n)
    (h : n < 2 ^ 64) : Spec.Aes.bytesAt (writeBytes m q zs) q n = zs := by
  subst hn
  refine List.ext_getElem (by simp [Spec.Aes.bytesAt]) fun i h₁ h₂ => ?_
  simp only [Spec.Aes.bytesAt, List.getElem_map, List.getElem_range, writeBytes,
    Mem.sub_ofNat_toNat q (show i < 2 ^ 64 by simp [Spec.Aes.bytesAt] at h₁; omega)]
  simp [Spec.Aes.bytesAt] at h₁
  simp [h₁, List.getD_eq_getElem?_getD]

/-- The block the two `storeBE`s write. -/
theorem blockAt_store (m : Mem) (q : Addr) (z0 z1 : BitVec 64) :
    blockAt (writeBytes (writeBytes m (q + BitVec.ofNat 64 0) (ByteLoad.beBytes 8 z0)) (q + BitVec.ofNat 64 8)
      (ByteLoad.beBytes 8 z1)) q = w2 z0 z1 := by
  have e := writeBytes_append m q (ByteLoad.beBytes 8 z0) (ByteLoad.beBytes 8 z1)
    (by simp [ByteLoad.beBytes_length])
  rw [ByteLoad.beBytes_length] at e
  rw [BitVec.add_zero, e, blockAt,
    bytesAt_writeBytes_self _ _ (by simp [ByteLoad.beBytes_length]) (by decide), ofBytes_beBytes]

/-! ## The function -/

/-- The contract the proof of `vg_ghash` is written against: as
`Proof.Gcm.ghashContract`, with the frame of 2048 bytes below the stack
pointer. -/
def ghashX : Contract isa where
  pre s :=
    let h : Region := ⟨s.gpr .a0, 16⟩
    let y : Region := ⟨s.gpr .a1, 16⟩
    let data : Region := ⟨s.gpr .a2, 16 * (s.gpr .a3).toNat⟩
    let scratch : Region := ⟨s.gpr .a4, 256⟩
    let stack : Region := ⟨s.sp - BitVec.ofNat 64 2048, 2048⟩
    s.rd = [h, data] ∧ s.wr = [y, scratch] ∧ y.Disjoint data ∧
    stack.Disjoint h ∧ stack.Disjoint y ∧ stack.Disjoint data ∧
    (s.gpr .a1).toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 16 * (s.gpr .a3).toNat ≤ 2 ^ 64 ∧
    s.sp.toNat % 16 = 0 ∧ 2048 ≤ s.sp.toNat
  post s s' :=
    blockAt s'.mem (s.gpr .a1) =
      ghashFrom (blockAt s.mem (s.gpr .a0)) (blockAt s.mem (s.gpr .a1))
        (blocksAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.sp = s₂.sp

/-- A byte of a region outside the frame at `B` is kept. -/
theorem out_byte {B : Addr} {m m' : Mem} (h : Out B m m') {R : Region} (hd : (⟨B, 2048⟩ : Region).Disjoint R)
    (hR : R.len ≤ 2 ^ 64) {i : Nat} (hi : i < R.len) :
    m' (R.base + BitVec.ofNat 64 i) = m (R.base + BitVec.ofNat 64 i) := by
  refine h _ fun hlt => hd _ hlt ?_
  simp only [Region.Contains]
  rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

/-- The block at `p`, within a region outside the frame. -/
theorem out_block {B : Addr} {m m' : Mem} (h : Out B m m') {p : Addr}
    (hd : (⟨B, 2048⟩ : Region).Disjoint ⟨p, 16⟩) : hOf m' p = hOf m p := by
  rw [← blockAt_hOf, ← blockAt_hOf]
  exact Proof.Gcm.blockAt_congr fun i hi => out_byte (R := ⟨p, 16⟩) h hd (by simp) hi

/-- The table zeroed. -/
theorem wipe_ok (u : State) {B : Addr} (hR : (⟨B, 2048⟩ : Region) ∈ u.wr) (hsp : u.sp = B)
    (hal : B.toNat % 16 = 0) :
    WP isa (.block (Impl.StackScratch.RISCV64.wipe 256)) u fun u' => Frame [⟨B, 2048⟩] u.mem u'.mem := by
  obtain ⟨u', he, hf, -, -, -, -⟩ := wipe_run ⟨B, 2048⟩ u 256 hR (by rw [hsp]; omega)
    (fun k hk => by rw [hsp]; exact Offset.contains_base _ (by omega) (by omega))
  exact ⟨_, _, Exec.block_iff.mpr he, hf⟩

theorem freed_mem (n : Nat) (u : State) : (freed n u).mem = u.mem := rfl

theorem ghash_ok (s : State) (hp : ghashX.pre s) : WP isa ghash s (ghashX.post s) := by
  obtain ⟨hrd, hwr, hyd, hsh, hsy, hsd, hfy, hfd, hal, hsp⟩ := hp
  refine WP.ite _ (eval_zero s N) (fun h0 => WP.block_nil ?_) (fun h0 => ?_)
  · have hn : (s.gpr .a3).toNat = 0 := by
      have := beq_iff_eq.mp h0; simp [N] at this; simp [this]
    show blockAt s.mem (s.gpr .a1) = _
    rw [hn]; rfl
  have hpos : 0 < (s.gpr .a3).toNat := by
    have := beq_eq_false_iff_ne.mp h0
    refine Nat.pos_of_ne_zero fun h => this ?_
    exact BitVec.eq_of_toNat_eq (by simpa [N] using h)
  refine WP.allocLe ⟨by decide, by decide, by decide⟩ hsp ?_
  -- The frame.
  have hBn : (s.sp - BitVec.ofNat 64 2048).toNat = s.sp.toNat - 2048 := toNat_sub_ofNat' hsp
  have hF : FrameOk (allocd 2048 s).sp (allocd 2048 s) :=
    ⟨by show (s.sp - BitVec.ofNat 64 2048).toNat % 16 = 0; omega,
     by show (s.sp - BitVec.ofNat 64 2048).toNat + 2048 ≤ 2 ^ 64; have := s.sp.isLt; omega,
     List.mem_cons_self⟩
  have hinH : InRegions ((allocd 2048 s).rd ++ (allocd 2048 s).wr) ((allocd 2048 s).gpr HP) 16 :=
    ⟨⟨s.gpr .a0, 16⟩, List.mem_append_left _ (by show _ ∈ s.rd; rw [hrd]; exact List.mem_cons_self),
      Region.contains_self _ _⟩
  refine WP.seq (WP.mono (table_ok hF hinH) fun sT hT => ?_)
  -- `Y` in.
  have hyT : InRegions (sT.rd ++ sT.wr) (sT.gpr YP) 16 := by
    rw [hT.rd, hT.wr, hT.keep _ (by decide)]
    exact ⟨⟨s.gpr .a1, 16⟩, List.mem_append_right _ (List.mem_cons_of_mem _ (by rw [hwr]; exact
      List.mem_cons_self)), Region.contains_self _ _⟩
  refine WP.seq ?_
  rw [show loadY = Impl.Words.RISCV64.loadBE64 Z0 T YP 0 ++ Impl.Words.RISCV64.loadBE64 Z1 T YP 8 ++ [] from
    (List.append_nil _).symm]
  refine load2_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hyT
    fun sY h0 h1 gY mY rdY wrY spY => WP.block_nil ?_
  -- The blocks.
  have hD : ∀ i < (s.gpr .a3).toNat, Region.Sub ⟨s.gpr .a2 + BitVec.ofNat 64 (16 * i), 16⟩
      ⟨s.gpr .a2, 16 * (s.gpr .a3).toNat⟩ := fun i hi => Offset.sub_base _ (by omega)
  have hFY : FrameOk (allocd 2048 s).sp sY := hF.of_wr (by rw [wrY, hT.wr])
  have hdR : ⟨s.gpr .a2, 16 * (s.gpr .a3).toNat⟩ ∈ sY.rd := by
    rw [rdY, hT.rd]; show _ ∈ s.rd; rw [hrd]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have hBL := blocks_loop (H := hOf (allocd 2048 s).mem ((allocd 2048 s).gpr HP))
    (Y₀ := blockAt s.mem (s.gpr .a1)) (D := s.gpr .a2) (m₀ := s.mem) (n₀ := (s.gpr .a3).toNat)
    hFY (by rw [mY]; exact hT.tab) (by rw [spY, hT.sp])
    (fun i hi => ⟨_, List.mem_append_left _ hdR,
      Offset.contains_base _ (by omega) (by have := (s.gpr .a3).isLt; omega)⟩)
    (fun i hi => by
      rw [mY, out_block hT.out (hsd.sub_right (hD i hi))]
      exact (blockAt_hOf _ _).symm)
    (s.gpr .a3).isLt hpos (s := sY)
  have hyp : sT.gpr YP = s.gpr .a1 := hT.keep _ (by decide)
  have hB0 : BlkInv (hOf (allocd 2048 s).mem ((allocd 2048 s).gpr HP)) (blockAt s.mem (s.gpr .a1))
      (s.gpr .a2) s.mem (s.gpr .a3).toNat (allocd 2048 s).sp sY 0 sY := by
    refine ⟨?_, ?_, ?_, ?_, rfl, fun _ _ => rfl, rfl, rfl, rfl⟩
    · rw [h0, h1, hyp, Proof.Gcm.ghashFrom_blocksAt_zero]
      show hOf sT.mem (s.gpr .a1) = _
      rw [out_block hT.out hsy, blockAt_hOf]; rfl
    · rw [gY _ (by decide) (by decide) (by decide), hT.keep _ (by decide), Nat.mul_zero, BitVec.add_zero]
      rfl
    · rw [gY _ (by decide) (by decide) (by decide), hT.keep _ (by decide), Nat.sub_zero,
        BitVec.ofNat_toNat, BitVec.setWidth_eq]; rfl
    · rw [gY _ (by decide) (by decide) (by decide)]; exact hT.e
  refine WP.seq (WP.mono (hBL hB0) fun sL hL => ?_)
  -- `Y` out.
  have hyL : sL.gpr YP = s.gpr .a1 := by
    rw [hL.keep _ (by decide), gY _ (by decide) (by decide) (by decide), hyp]
  have hwy : ∀ off, off ≤ 8 → ∀ j < 8, InRegions sL.wr (s.gpr .a1 + BitVec.ofNat 64 (off + j)) 1 :=
    fun off ho j hj => ⟨⟨s.gpr .a1, 16⟩, by
      rw [hL.wr, wrY, hT.wr]; show _ ∈ _ :: s.wr; rw [hwr]
      exact List.mem_cons_of_mem _ List.mem_cons_self,
      Offset.contains_base _ (by omega) (by omega)⟩
  refine WP.seq ?_
  rw [storeY, WP.block_append_iff]
  refine WP.mono (ByteLoad.storeBE_ok (s := sL) (v := Z0) (tmp := T) (n := YP) (off := 0) (w := 8)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by rw [hyL]; exact hwy 0 (by decide)))
    fun s₁ e₁ => ?_
  subst e₁
  refine WP.mono (ByteLoad.storeBE_ok (v := Z1) (tmp := T) (n := YP) (off := 8) (w := 8)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [RegUpd.gpr_write_of_ne _ _ (by decide)]; show ∀ j < 8, InRegions sL.wr _ 1
        rw [hyL]; exact hwy 8 (by decide)))
    fun s₂ e₂ => ?_
  subst e₂
  -- The wipe.
  have hR : (⟨(allocd 2048 s).sp, 2048⟩ : Region) ∈ sL.wr := by rw [hL.wr, wrY, hT.wr]; exact hF.wr
  have hspL : sL.sp = (allocd 2048 s).sp := by rw [hL.sp, spY, hT.sp]
  refine WP.mono (wipe_ok _ (by simp only [RegUpd.wr_write]; exact hR)
    (by simp only [RegUpd.sp_write]; exact hspL) hF.al) fun u hf => ?_
  simp only [ghashX, freed_mem]
  rw [Proof.Gcm.blockAt_congr (m := _) fun i hi => hf.bytes (R := ⟨s.gpr .a1, 16⟩)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsy.symm) (by simp) hi]
  simp only [RegUpd.mem_write, RegUpd.gpr_write_of_ne _ _ (show YP ≠ T by decide),
    RegUpd.gpr_write_of_ne _ _ (show Z1 ≠ T by decide), hyL]
  rw [blockAt_store, hL.y, blockAt_hOf s.mem (s.gpr .a0)]; rfl

/-- The registers the code writes: no preserved register, nor `ra`. -/
def written : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a2, .a3, .a4, .a5, .a6, .a7]

theorem ghash_correct (s : State) (hs : ghashX.pre s) :
    ∃ t s', Exec isa ghash s t s' ∧ abiPreserved s s' ∧ ghashX.post s s' := by
  obtain ⟨tr, t, he, hpost, hkeep⟩ := WP.keep written (ghash_ok s hs) (by lit_decide) (by lit_decide)
  exact ⟨tr, t, he, abiPreserved_of_keep he hkeep (by decide) (by decide), hpost⟩

theorem ghash_ct : ConstantTime isa ghashX.pre ghashX.pub ghash := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ h
  refine ⟨h.2.2.2.2.2, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2.1
  · exact h.2.2.2.2.1

def ghashSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | .a3 => 1 | .a4 => 0x4000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 16⟩, ⟨0x3000, 16⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x4000, 256⟩]

theorem ghash_verified : Verified RISCV64.target ghash (Proof.Gcm.ghashContract RISCV64.abi 2048) :=
  Verified.of_correct ghash_correct ghash_ct (by
    sig_implies [Proof.Gcm.ghashContract, Proof.Gcm.ghashSig, ghashX, RISCV64.abi, RISCV64.argRegs]
      [ghashSat]
      using ghashSat)

end VG.Proof.Gcm.RISCV64
