module

public import VerifiedGarbage.Proof.Gcm.RISCV64.Code
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad64
import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.Framework.RISCV64.Wp
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
meta import VerifiedGarbage.Proof.Gcm.RISCV64.Code
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

Untrusted: everything here is checked by Lean. The blocks (`blocks_loop`, from
`block_ok` and `Holes.mulK_eq`); and the function (`ghash_ok`): the registers
saved, the key prepared (`prep_ok`), `Y` in, the blocks, `Y` out, the
registers restored and the frame zeroed, in the frame of 2048 bytes below
the stack pointer, against a per-target contract (`ghashX`).
-/

@[expose] public section

namespace VG.Proof.Gcm.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Gcm.RISCV64 VG.WriteBytes
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom mul ofBytes)

/-! ## Blocks as words -/

/-- The block of the high word `a` and the low word `b`. -/
abbrev w2 (a b : BitVec 64) : Block := a ++ b

/-- The block of `H`, from its 16 bytes at `p`. -/
abbrev hOf (m : Mem) (p : Addr) : Block := w2 (ByteLoad.be64 m p 0) (ByteLoad.be64 m p 8)

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

/-! ## The frame -/

/-- The frame of 2048 bytes at `B`, writable, 16-byte aligned, not wrapping. -/
structure FrameOk (B : Addr) (s : State) : Prop where
  al : B.toNat % 16 = 0
  fit : B.toNat + 2048 ≤ 2 ^ 64
  wr : (⟨B, 2048⟩ : Region) ∈ s.wr

theorem FrameOk.of_wr {B : Addr} {s s' : State} (h : FrameOk B s) (hw : s'.wr = s.wr) : FrameOk B s' :=
  ⟨h.al, h.fit, hw ▸ h.wr⟩

theorem FrameOk.al8 {B : Addr} {s : State} (h : FrameOk B s) {d : Nat} (hd : d % 8 = 0) (hd' : d < 2048) :
    (B + BitVec.ofNat 64 d).toNat % 8 = 0 :=
  Wp.al8 h.al hd (by omega)

theorem FrameOk.inW {B : Addr} {s : State} (h : FrameOk B s) {d : Nat} (hd : d + 8 ≤ 2048) :
    InRegions s.wr (B + BitVec.ofNat 64 d) 8 :=
  ⟨_, h.wr, Offset.contains_base _ hd (by omega)⟩

theorem FrameOk.inR {B : Addr} {s : State} (h : FrameOk B s) {d : Nat} (hd : d + 8 ≤ 2048) :
    InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 d) 8 := by
  obtain ⟨r, hr, hc⟩ := h.inW hd
  exact ⟨r, List.mem_append_right _ hr, hc⟩

/-- The frame's slots, from a frame at `FP`. -/
theorem FrameOk.wr8 {s : State} (h : FrameOk (s.gpr FP) s) {k : Nat} (hk : k < 256) : Wr8 s (8 * k) :=
  ⟨by omega, h.al8 (by omega) (by omega), h.inW (by omega)⟩

theorem FrameOk.rd8 {s : State} (h : FrameOk (s.gpr FP) s) {k : Nat} (hk : k < 256) : Rd8 s (8 * k) :=
  ⟨by omega, h.al8 (by omega) (by omega), h.inR (by omega)⟩

/-! ## The blocks -/

/-- After `i` of the `n₀` blocks at `D`, from `sY`: `Y` is `GHASH_H` from
`Y₀` over them (`H` and the blocks from the memory `m₀`). -/
structure BlkInv (H Y₀ : Block) (D : Addr) (m₀ : Mem) (n₀ : Nat) (sY : State) (i : Nat) (s : State) : Prop where
  y : w2 (s.gpr Y0) (s.gpr Y1) = ghashFrom H Y₀ (blocksAt m₀ D i)
  dp : s.gpr DP = D + BitVec.ofNat 64 (16 * i)
  n : s.gpr N = BitVec.ofNat 64 (n₀ - i)
  keep : Keep blockRegs sY s
  sp : s.sp = sY.sp
  tab : ∀ k < 36, fw s (8 * k) = fw sY (8 * k)
  frame : Frame [⟨sY.gpr FP + BitVec.ofNat 64 288, 32⟩] sY.mem s.mem

/-- What the blocks need of the state they start from. -/
structure LoopPre (H : Block) (D : Addr) (m₀ : Mem) (n₀ : Nat) (sY : State) : Prop where
  frame : FrameOk (sY.gpr FP) sY
  masks : Masks sY
  key : ∃ h0 h1, H = h0 ++ h1 ∧ Tab (Holes.key0 h0 h1) (Holes.key1 h0 h1) (fw sY)
  dat : ∀ i < n₀, InRegions (sY.rd ++ sY.wr) (D + BitVec.ofNat 64 (16 * i)) 16
  bytes : ∀ i < n₀, ∀ j < 16, ∀ m : Mem, Frame [⟨sY.gpr FP + BitVec.ofNat 64 288, 32⟩] sY.mem m →
    m (D + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 j) = m₀ (D + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 j)

theorem blk_step {H Y₀ : Block} {D : Addr} {m₀ : Mem} {n₀ : Nat} {sY : State} (hL : LoopPre H D m₀ n₀ sY)
    (hn₀ : n₀ < 2 ^ 64) {i : Nat} (hi : i < n₀) {s : State} (hs : BlkInv H Y₀ D m₀ n₀ sY i s) :
    WP isa (.block blockCode) s (BlkInv H Y₀ D m₀ n₀ sY (i + 1)) := by
  obtain ⟨hF, hK, ⟨h0, h1, hH, ht⟩, hd, hb⟩ := hL
  have fp : s.gpr FP = sY.gpr FP := Keep.gpr hs.keep (by decide)
  have hF' : FrameOk (s.gpr FP) s := by rw [fp]; exact hF.of_wr hs.keep.2.2
  have pre : BlkPre s := ⟨Keep.masks hs.keep hK (fun j hj => by interval_cases j <;> decide),
    fun k hk => hF'.rd8 (by omega), fun k _ h2 => hF'.wr8 (by omega),
    by rw [hs.dp, hs.keep.2.1, hs.keep.2.2]; exact hd i hi⟩
  refine WP.mono (block_ok s pre) fun t ⟨ey, ed, en, kt, pt, tt, ft⟩ => ?_
  have tabs : Tab (Holes.key0 h0 h1) (Holes.key1 h0 h1) (fw s) := fun i' hi' j hj => by
    rw [hs.tab _ (by omega)]; exact ht i' hi' j hj
  -- The block, from the bytes at `DP`.
  have hx : ByteLoad.be64 s.mem (s.gpr DP) 0 ++ ByteLoad.be64 s.mem (s.gpr DP) 8 =
      blockAt m₀ (D + BitVec.ofNat 64 (16 * i)) := by
    rw [show ByteLoad.be64 s.mem (s.gpr DP) 0 ++ ByteLoad.be64 s.mem (s.gpr DP) 8 = hOf s.mem (s.gpr DP) from rfl,
      ← blockAt_hOf, hs.dp]
    exact Proof.Gcm.blockAt_congr fun j hj => hb i hi j hj _ hs.frame
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ey.trans ?_
    rw [mulT_tab tabs, Holes.mulK_eq, ← hH, ← BitVec.xor_append, hx, Proof.Gcm.ghashFrom_blocksAt_succ]
    exact congrArg (fun v => mul (v ^^^ _) H) hs.y
  · rw [ed, hs.dp, BitVec.add_assoc, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, BitVec.ofNat_add_ofNat]
    congr 2
  · rw [en, hs.n]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl,
      Nat.mod_eq_of_lt (a := n₀ - i) (by omega)]
    omega
  · exact Keep.mono (Keep.trans hs.keep kt) (by simp only [blockRegs]; decide)
  · rw [pt, hs.sp]
  · intro k hk; rw [tt k hk, hs.tab k hk]
  · rw [fp] at ft; exact hs.frame.trans ft

theorem blocks_loop {H Y₀ : Block} {D : Addr} {m₀ : Mem} {n₀ : Nat} {sY : State} (hL : LoopPre H D m₀ n₀ sY)
    (hn₀ : n₀ < 2 ^ 64) (hpos : 0 < n₀) {s : State} (hs : BlkInv H Y₀ D m₀ n₀ sY 0 s) :
    WP isa (.loop (.block blockCode) (.nonzero N)) s (BlkInv H Y₀ D m₀ n₀ sY n₀) := by
  refine WP.loop (M := isa) (fun k s' => ∃ i, k = n₀ - i ∧ i < n₀ ∧ BlkInv H Y₀ D m₀ n₀ sY i s')
    (fun k s' ⟨i, hk, hi, hb⟩ => WP.mono (blk_step hL hn₀ hi hb) fun s'' hb' => ?_) n₀ s
    ⟨0, rfl, hpos, hs⟩
  have hev := eval_nonzero_ofNat s'' N (k := n₀ - (i + 1)) (by omega) hb'.n
  by_cases hl : i + 1 = n₀
  · exact .inl ⟨by rw [hev]; simp [hl], hl ▸ hb'⟩
  · exact .inr ⟨by rw [hev]; simp; omega, n₀ - (i + 1), by omega, i + 1, rfl, by omega, hb'⟩

/-! ## The saved registers -/

/-- The registers `saved` lists. -/
def savedRegs : List Reg := saved.map Prod.fst

/-- The memory after the saves: each saved register at its slot. -/
def saveMem (m : Mem) (B : Addr) (g : Reg → BitVec 64) : Mem :=
  saved.foldl (fun m (r, d) => m.writeW (B + BitVec.ofNat 64 d) (g r)) m

theorem save_ok (s : State) (hF : FrameOk s.sp s) :
    WP isa (.block (.addSp .t0 0 :: saveRegs ++ [.addSp FP 0])) s fun t =>
      t.gpr FP = s.sp ∧ Keep [.t0, .s9] s t ∧ t.sp = s.sp ∧ t.mem = saveMem s.mem s.sp s.gpr := by
  have W : ∀ k, 40 ≤ k → k < 50 → (8 * k < 2048 ∧ (s.sp + BitVec.ofNat 64 (8 * k)).toNat % 8 = 0) ∧
      InRegions s.wr (s.sp + BitVec.ofNat 64 (8 * k)) 8 :=
    fun k h1 h2 => ⟨⟨by omega, hF.al8 (by omega) (by omega)⟩, hF.inW (by omega)⟩
  have W0 := W 40 (by decide) (by decide); have W1 := W 41 (by decide) (by decide)
  have W2 := W 42 (by decide) (by decide); have W3 := W 43 (by decide) (by decide)
  have W4 := W 44 (by decide) (by decide); have W5 := W 45 (by decide) (by decide)
  have W6 := W 46 (by decide) (by decide); have W7 := W 47 (by decide) (by decide)
  have W8 := W 48 (by decide) (by decide); have W9 := W 49 (by decide) (by decide)
  simp only [Nat.reduceMul] at W0 W1 W2 W3 W4 W5 W6 W7 W8 W9
  simp only [saveRegs, saved, slot, List.map, FP, List.cons_append, List.nil_append]
  mrun [W0.1, W1.1, W2.1, W3.1, W4.1, W5.1, W6.1, W7.1, W8.1, W9.1,
    W0.2, W1.2, W2.2, W3.2, W4.2, W5.2, W6.2, W7.2, W8.2, W9.2]
  simp only [saveMem, saved, slot, List.foldl, Nat.reduceMul]
  glue_close

theorem restore_ok (s : State) (hF : FrameOk s.sp s) (v : Reg → BitVec 64)
    (hm : ∀ p ∈ saved, s.mem.readW (s.sp + BitVec.ofNat 64 p.2) 64 = v p.1) :
    WP isa (.block (.addSp .t0 0 :: restoreRegs)) s fun t =>
      (∀ r ∈ savedRegs, t.gpr r = v r) ∧ Keep (.t0 :: savedRegs) s t ∧ t.mem = s.mem ∧ t.sp = s.sp := by
  have R : ∀ k, 40 ≤ k → k < 50 → (8 * k < 2048 ∧ (s.sp + BitVec.ofNat 64 (8 * k)).toNat % 8 = 0) ∧
      InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (8 * k)) 8 :=
    fun k h1 h2 => ⟨⟨by omega, hF.al8 (by omega) (by omega)⟩, hF.inR (by omega)⟩
  have R0 := R 40 (by decide) (by decide); have R1 := R 41 (by decide) (by decide)
  have R2 := R 42 (by decide) (by decide); have R3 := R 43 (by decide) (by decide)
  have R4 := R 44 (by decide) (by decide); have R5 := R 45 (by decide) (by decide)
  have R6 := R 46 (by decide) (by decide); have R7 := R 47 (by decide) (by decide)
  have R8 := R 48 (by decide) (by decide); have R9 := R 49 (by decide) (by decide)
  simp only [Nat.reduceMul] at R0 R1 R2 R3 R4 R5 R6 R7 R8 R9
  have m0 := hm (.s0, 320) (by decide)
  have m1 := hm (.s1, 328) (by decide)
  have m2 := hm (.s2, 336) (by decide)
  have m3 := hm (.s3, 344) (by decide)
  have m4 := hm (.s4, 352) (by decide)
  have m5 := hm (.s5, 360) (by decide)
  have m6 := hm (.s6, 368) (by decide)
  have m7 := hm (.s7, 376) (by decide)
  have m8 := hm (.s8, 384) (by decide)
  have m9 := hm (.s9, 392) (by decide)
  simp only at m0 m1 m2 m3 m4 m5 m6 m7 m8 m9
  simp only [restoreRegs, saved, slot, List.map, Nat.reduceMul]
  mrun [R0.1, R1.1, R2.1, R3.1, R4.1, R5.1, R6.1, R7.1, R8.1, R9.1,
    R0.2, R1.2, R2.2, R3.2, R4.2, R5.2, R6.2, R7.2, R8.2, R9.2, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9]
  refine ⟨fun r hr => ?_, ?_⟩
  · simp only [savedRegs, saved, List.map, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · simp only [savedRegs, saved, List.map]
    glue_close

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

/-- The saves, read back. -/
theorem readW_saveMem (m : Mem) (B : Addr) (g : Reg → BitVec 64) :
    ∀ p ∈ saved, (saveMem m B g).readW (B + BitVec.ofNat 64 p.2) 64 = g p.1 := by
  intro p hp
  simp only [saved, slot, List.mem_cons, List.not_mem_nil, or_false, Nat.reduceMul] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := omega) only [saveMem, saved, slot, List.foldl, Nat.reduceMul, readW_wr_ne,
      Mem.readW_writeW_self64]

/-- The saves write inside the frame. -/
theorem saveMem_frame (m : Mem) (B : Addr) (g : Reg → BitVec 64) :
    Frame [⟨B, 2048⟩] m (saveMem m B g) := by
  have c : ∀ d, d + 8 ≤ 2048 → (⟨B, 2048⟩ : Region).Contains (B + BitVec.ofNat 64 d) (64 / 8) :=
    fun d hd => Offset.contains_base _ hd (by omega)
  simp only [saveMem, saved, slot, List.foldl, Nat.reduceMul]
  repeat (first
    | exact Frame.refl _ _
    | refine Frame.writeW ?_ List.mem_cons_self _ (c _ (by decide)))

/-- Two ranges of the frame at `B` that do not overlap. -/
theorem slot_disj (B : Addr) {d e n : Nat} (hd : d + 8 ≤ 2048) (h : e + n ≤ d) :
    (⟨B + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint ⟨B + BitVec.ofNat 64 e, n⟩ := by
  intro x h₁ h₂
  simp only [Region.Contains, Offset.sub_add_eq, Offset.toNat_sub_ofNat] at h₁ h₂
  have := (x - B).isLt
  omega

theorem sub_disj {r R R' : Region} (hs : Region.Sub r R) (hd : R.Disjoint R') : r.Disjoint R' :=
  fun x hx => hd x (hs x hx)

/-- The frame zeroed. -/
theorem wipe50_ok (u : State) {B : Addr} (hR : (⟨B, 2048⟩ : Region) ∈ u.wr) (hsp : u.sp = B)
    (hal : B.toNat % 16 = 0) :
    WP isa (.block (Impl.StackScratch.RISCV64.wipe 50)) u fun u' => Frame [⟨B, 2048⟩] u.mem u'.mem ∧
      (∀ r, r ≠ .t5 → r ≠ .t6 → u'.gpr r = u.gpr r) ∧ u'.sp = u.sp := by
  obtain ⟨u', he, hf, ho, hs, -, -⟩ := wipe_run ⟨B, 2048⟩ u 50 hR (by rw [hsp]; omega)
    (fun k hk => by rw [hsp]; exact Offset.contains_base _ (by omega) (by omega))
  exact ⟨_, _, Exec.block_iff.mpr he, hf, ho, hs⟩

/-- What the code has set up when the blocks start, from `s` and its frame `a`. -/
structure HeadPost (s a sY : State) : Prop where
  loop : LoopPre (blockAt s.mem (s.gpr .a0)) (s.gpr .a2) s.mem (s.gpr .a3).toNat sY
  inv : BlkInv (blockAt s.mem (s.gpr .a0)) (blockAt s.mem (s.gpr .a1)) (s.gpr .a2) s.mem
    (s.gpr .a3).toNat sY 0 sY
  yp : sY.gpr YP = s.gpr .a1
  wr : sY.wr = a.wr
  sp : sY.sp = a.sp
  fp : sY.gpr FP = a.sp
  slots : ∀ p ∈ saved, sY.mem.readW (a.sp + BitVec.ofNat 64 p.2) 64 = s.gpr p.1
  fy : Frame [⟨a.sp, 2048⟩] s.mem sY.mem

/-- The pre-condition's facts on the frame, for `a := allocd 2048 s`. -/
structure Pre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .a0, 16⟩, ⟨s.gpr .a2, 16 * (s.gpr .a3).toNat⟩]
  wr : s.wr = [⟨s.gpr .a1, 16⟩, ⟨s.gpr .a4, 256⟩]
  sh : (⟨(allocd 2048 s).sp, 2048⟩ : Region).Disjoint ⟨s.gpr .a0, 16⟩
  sy : (⟨(allocd 2048 s).sp, 2048⟩ : Region).Disjoint ⟨s.gpr .a1, 16⟩
  sd : (⟨(allocd 2048 s).sp, 2048⟩ : Region).Disjoint ⟨s.gpr .a2, 16 * (s.gpr .a3).toNat⟩
  fd : (s.gpr .a2).toNat + 16 * (s.gpr .a3).toNat ≤ 2 ^ 64
  frame : FrameOk (allocd 2048 s).sp (allocd 2048 s)

theorem head_ok (s : State) (hp : Pre s) :
    WP isa (.block (.addSp .t0 0 :: saveRegs ++ [.addSp FP 0] ++ prep ++ loadY)) (allocd 2048 s)
      (HeadPost s (allocd 2048 s)) := by
  obtain ⟨hrd, hwr, hsh, hsy, hsd, hfd, hF⟩ := hp
  set a := allocd 2048 s with ha
  have ard : a.rd = s.rd := rfl
  have awr : a.wr = ⟨a.sp, 2048⟩ :: s.wr := rfl
  have agpr : a.gpr = s.gpr := rfl
  have amem : a.mem = s.mem := rfl
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (save_ok a hF) fun u1 ⟨f1, k1, p1, m1⟩ => ?_
  have hF1 : FrameOk (u1.gpr FP) u1 := by rw [f1]; exact hF.of_wr k1.2.2
  have hH : InRegions (u1.rd ++ u1.wr) (u1.gpr HP) 16 := by
    rw [k1.2.1, k1.2.2, Keep.gpr k1 (by decide)]
    exact ⟨⟨s.gpr .a0, 16⟩, List.mem_append_left _ (by rw [ard, hrd]; exact List.mem_cons_self),
      Region.contains_self _ _⟩
  refine WP.mono (prep_ok u1 hH fun k hk => hF1.wr8 (by omega)) fun u2 ⟨K2, T2, k2, p2, F2⟩ => ?_
  have hYr : InRegions (u2.rd ++ u2.wr) (u2.gpr YP) 16 := by
    rw [k2.2.1, k2.2.2, Keep.gpr k2 (by decide), k1.2.1, k1.2.2, Keep.gpr k1 (by decide)]
    exact ⟨⟨s.gpr .a1, 16⟩, List.mem_append_right _ (by rw [awr, hwr]; simp), Region.contains_self _ _⟩
  refine WP.mono (ld2_ok (d₀ := Y0) (d₁ := Y1) (tmp := .t2) (n := YP) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) u2 hYr) fun sY ⟨y0, y1, k3, m3, p3⟩ => ?_
  -- The memory before the blocks: the frame's changes only.
  have FY : Frame [⟨a.sp, 2048⟩] s.mem sY.mem := by
    rw [m3]
    have e1 : Frame [⟨a.sp, 2048⟩] s.mem u1.mem := by rw [m1, ← amem]; exact saveMem_frame _ _ _
    have e2 : Frame [⟨a.sp, 2048⟩] u1.mem u2.mem := by
      refine F2.sub fun r hr => ⟨_, List.mem_cons_self, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [f1]; simpa using Offset.sub_base a.sp (d := 0) (n := 288) (k := 2048) (by decide)
    exact e1.trans e2
  have kY : Keep (prepRegs ++ [.a4, .a5, .t2]) u1 sY := Keep.trans k2 k3
  have fpY : sY.gpr FP = a.sp := by rw [Keep.gpr kY (by decide), f1]
  have hFY : FrameOk (sY.gpr FP) sY := by rw [fpY]; exact hF.of_wr (by rw [kY.2.2, k1.2.2])
  have gY : ∀ r, r ∉ [.t0, .s9] ++ (prepRegs ++ [.a4, .a5, .t2]) → sY.gpr r = s.gpr r := fun r hr => by
    rw [Keep.gpr (Keep.trans k1 kY) hr]; rfl
  -- Bytes outside the frame.
  have out : ∀ {m : Mem}, Frame [⟨a.sp, 2048⟩] s.mem m → ∀ {R : Region}, (⟨a.sp, 2048⟩ : Region).Disjoint R →
      R.len ≤ 2 ^ 64 → ∀ i < R.len, m (R.base + BitVec.ofNat 64 i) = s.mem (R.base + BitVec.ofNat 64 i) :=
    fun hm R hd hR i hi => hm _ fun r hr hc => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact hd _ hc (Offset.contains_base _ (by omega) (by omega))
  have e1 : Frame [⟨a.sp, 2048⟩] s.mem u1.mem := by rw [m1, ← amem]; exact saveMem_frame _ _ _
  have hHk : blockAt s.mem (s.gpr .a0) =
      ByteLoad.be64 u1.mem (u1.gpr HP) 0 ++ ByteLoad.be64 u1.mem (u1.gpr HP) 8 := by
    have hk1 : u1.gpr HP = s.gpr .a0 := Keep.gpr k1 (by decide)
    rw [hk1]
    change blockAt s.mem (s.gpr .a0) = hOf u1.mem (s.gpr .a0)
    rw [← blockAt_hOf]
    exact (Proof.Gcm.blockAt_congr fun i hi => out e1 (R := ⟨s.gpr .a0, 16⟩) hsh (by simp) i hi).symm
  have hYk : blockAt s.mem (s.gpr .a1) = w2 (sY.gpr Y0) (sY.gpr Y1) := by
    rw [y0, y1, Keep.gpr k2 (by decide), Keep.gpr k1 (by decide),
      show w2 (ByteLoad.be64 u2.mem (a.gpr YP) 0) (ByteLoad.be64 u2.mem (a.gpr YP) 8) = hOf u2.mem (s.gpr .a1) from rfl,
      ← blockAt_hOf, ← m3]
    exact (Proof.Gcm.blockAt_congr fun i hi => out FY (R := ⟨s.gpr .a1, 16⟩) hsy (by simp) i hi).symm
  have hn₀ := (s.gpr .a3).isLt
  have hL : LoopPre (blockAt s.mem (s.gpr .a0)) (s.gpr .a2) s.mem (s.gpr .a3).toNat sY := by
    refine ⟨hFY, ?_, ⟨_, _, hHk, ?_⟩, ?_, ?_⟩
    · exact Keep.masks k3 K2 (fun i hi => by interval_cases i <;> decide)
    · intro i hi j hj
      rw [fw_congr m3 (Keep.gpr k3 (by decide))]; exact T2 i hi j hj
    · intro i hi
      rw [kY.2.1, kY.2.2, k1.2.1, k1.2.2, ard]
      exact ⟨⟨s.gpr .a2, 16 * (s.gpr .a3).toNat⟩, List.mem_append_left _ (by rw [hrd]; simp),
        Offset.contains_base _ (by omega) (by omega)⟩
    · intro i hi j hj m hm
      have hm' : Frame [⟨a.sp, 2048⟩] s.mem m := FY.trans (hm.sub fun r hr => ⟨_, List.mem_cons_self, by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; rw [fpY]; exact Offset.sub_base _ (by decide)⟩)
      have := out hm' hsd (by simp; omega) (16 * i + j) (by simp; omega)
      rwa [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  have hB0 : BlkInv (blockAt s.mem (s.gpr .a0)) (blockAt s.mem (s.gpr .a1)) (s.gpr .a2) s.mem
      (s.gpr .a3).toNat sY 0 sY := by
    refine ⟨?_, ?_, ?_, Keep.refl _ _, rfl, fun _ _ => rfl, Frame.refl _ _⟩
    · rw [Proof.Gcm.ghashFrom_blocksAt_zero, hYk]
    · rw [gY _ (by decide)]; simp; rfl
    · rw [gY _ (by decide), Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]; rfl
  refine ⟨hL, hB0, by rw [gY _ (by decide)]; rfl, by rw [kY.2.2, k1.2.2], by rw [p3, p2, p1], fpY,
    fun p hp => ?_, FY⟩
  have hd : 320 ≤ p.2 ∧ p.2 + 8 ≤ 400 := by
    simp only [saved, slot, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have c : (⟨a.sp + BitVec.ofNat 64 p.2, 8⟩ : Region).Contains (a.sp + BitVec.ofNat 64 p.2) 8 :=
    Region.contains_self _ _
  simp only [Mem.readW]
  rw [m3, Frame.read F2 c (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      rw [f1]; simpa using slot_disj a.sp (e := 0) (n := 288) (by omega) (by omega)) (by decide), m1]
  have := readW_saveMem a.mem a.sp a.gpr p hp
  simp only [Mem.readW] at this
  rw [this, agpr]

theorem tail_ok (s : State) (hp : Pre s) (u : State) {Y : Block} (hy : w2 (u.gpr Y0) (u.gpr Y1) = Y)
    (hyp : u.gpr YP = s.gpr .a1) (hwrU : u.wr = (allocd 2048 s).wr) (hsp : u.sp = (allocd 2048 s).sp)
    (hslot : ∀ p ∈ saved, u.mem.readW ((allocd 2048 s).sp + BitVec.ofNat 64 p.2) 64 = s.gpr p.1) :
    WP isa (.block (storeY ++ (.addSp .t0 0 :: restoreRegs) ++ Impl.StackScratch.RISCV64.wipe 50)) u
      fun t => blockAt t.mem (s.gpr .a1) = Y ∧ (∀ r ∈ savedRegs, t.gpr r = s.gpr r) ∧ t.sp = u.sp := by
  obtain ⟨hrd, hwr, hsh, hsy, hsd, hfd, hF⟩ := hp
  set a := allocd 2048 s with ha
  have awr : a.wr = ⟨a.sp, 2048⟩ :: s.wr := rfl
  have hwy : ∀ off, off ≤ 8 → ∀ j < 8, InRegions u.wr (s.gpr .a1 + BitVec.ofNat 64 (off + j)) 1 :=
    fun off ho j hj => ⟨⟨s.gpr .a1, 16⟩, by rw [hwrU, awr, hwr]; simp,
      Offset.contains_base _ (by omega) (by omega)⟩
  rw [WP.block_append_iff, WP.block_append_iff, storeY, WP.block_append_iff]
  refine WP.mono (ByteLoad.storeBE_ok (s := u) (v := Y0) (tmp := .t2) (n := YP) (off := 0) (w := 8)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by rw [hyp]; exact hwy 0 (by decide)))
    fun s₁ e₁ => ?_
  subst e₁
  refine WP.mono (ByteLoad.storeBE_ok (v := Y1) (tmp := .t2) (n := YP) (off := 8) (w := 8)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [RegUpd.gpr_write_of_ne _ _ (by decide)]; show ∀ j < 8, InRegions u.wr _ 1
        rw [hyp]; exact hwy 8 (by decide)))
    fun s₂ e₂ => ?_
  subst e₂
  simp only [RegUpd.gpr_write_of_ne _ _ (show YP ≠ .t2 by decide), RegUpd.gpr_write_of_ne _ _ (show Y1 ≠ .t2 by decide),
    hyp]
  have Fy : Frame [⟨s.gpr .a1, 16⟩] u.mem
      (writeBytes (writeBytes u.mem (s.gpr .a1 + BitVec.ofNat 64 0) (ByteLoad.beBytes 8 (u.gpr Y0)))
        (s.gpr .a1 + BitVec.ofNat 64 8) (ByteLoad.beBytes 8 (u.gpr Y1))) :=
    (writeBytes_frame _ _ _ (Offset.contains_base _ (by simp [ByteLoad.beBytes_length]) (by decide))).trans
      (writeBytes_frame _ _ _ (Offset.contains_base _ (by simp [ByteLoad.beBytes_length]) (by decide)))
  have hm : ∀ p ∈ saved, (writeBytes (writeBytes u.mem (s.gpr .a1 + BitVec.ofNat 64 0)
      (ByteLoad.beBytes 8 (u.gpr Y0))) (s.gpr .a1 + BitVec.ofNat 64 8)
        (ByteLoad.beBytes 8 (u.gpr Y1))).readW (a.sp + BitVec.ofNat 64 p.2) 64 = s.gpr p.1 := by
    intro p hp
    have hd : 320 ≤ p.2 ∧ p.2 + 8 ≤ 400 := by
      simp only [saved, slot, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have c : (⟨a.sp + BitVec.ofNat 64 p.2, 8⟩ : Region).Contains (a.sp + BitVec.ofNat 64 p.2) 8 :=
      Region.contains_self _ _
    simp only [Mem.readW]
    rw [Frame.read Fy c (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
          exact sub_disj (Offset.sub_base _ (by omega)) hsy) (by decide)]
    have := hslot p hp
    simp only [Mem.readW] at this
    exact this
  refine WP.mono (restore_ok _ ?_ s.gpr ?_) fun s₃ ⟨r3, k4, m4, p4⟩ => ?_
  · simp only [RegUpd.sp_write, RegUpd.wr_write]; rw [hsp]; exact hF.of_wr hwrU
  · simp only [RegUpd.sp_write, RegUpd.mem_write]; rw [hsp]; exact hm
  have sp3 : s₃.sp = a.sp := by rw [p4]; simp only [RegUpd.sp_write]; exact hsp
  have hRw : (⟨a.sp, 2048⟩ : Region) ∈ s₃.wr := by
    rw [k4.2.2]; simp only [RegUpd.wr_write]; rw [hwrU, awr]; exact List.mem_cons_self
  refine WP.mono (wipe50_ok s₃ hRw sp3 hF.al) fun t ⟨ft, gt, pt⟩ => ?_
  refine ⟨?_, fun r hr => ?_, ?_⟩
  · have hyb : blockAt t.mem (s.gpr .a1) = blockAt s₃.mem (s.gpr .a1) :=
      Proof.Gcm.blockAt_congr fun i hi => ft _ fun r hr hc => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
        exact hsy _ hc (Offset.contains_base _ (by omega) (by omega))
    rw [hyb, m4]
    simp only [RegUpd.mem_write]
    rw [blockAt_store, hy]
  · have h56 : r ≠ .t5 ∧ r ≠ .t6 := by
      simp only [savedRegs, saved, List.map, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [gt r h56.1 h56.2, r3 r hr]
  · rw [pt, p4]; simp only [RegUpd.sp_write]

theorem ghash_ok (s : State) (hp : ghashX.pre s) :
    WP isa ghash s fun s' => ghashX.post s s' ∧ ∀ r ∈ savedRegs, s'.gpr r = s.gpr r := by
  obtain ⟨hrd, hwr, hyd, hsh, hsy, hsd, hfy, hfd, hal, hsp⟩ := hp
  refine WP.ite _ (eval_zero s N) (fun h0 => WP.block_nil ⟨?_, fun _ _ => rfl⟩) (fun h0 => ?_)
  · have hn : (s.gpr .a3).toNat = 0 := by
      have := beq_iff_eq.mp h0; simp [N] at this; simp [this]
    show blockAt s.mem (s.gpr .a1) = _
    rw [hn]; rfl
  have hpos : 0 < (s.gpr .a3).toNat := by
    have := beq_eq_false_iff_ne.mp h0
    refine Nat.pos_of_ne_zero fun h => this ?_
    exact BitVec.eq_of_toNat_eq (by simpa [N] using h)
  have hF : FrameOk (allocd 2048 s).sp (allocd 2048 s) :=
    ⟨by show (s.sp - BitVec.ofNat 64 2048).toNat % 16 = 0; rw [toNat_sub_ofNat' hsp]; omega,
     by show (s.sp - BitVec.ofNat 64 2048).toNat + 2048 ≤ 2 ^ 64; rw [toNat_sub_ofNat' hsp]; have := s.sp.isLt; omega,
     List.mem_cons_self⟩
  have P : Pre s := ⟨hrd, hwr, hsh, hsy, hsd, hfd, hF⟩
  unfold frameBytes
  refine WP.allocLe ⟨by decide, by decide, by decide⟩ hsp ?_
  unfold body
  refine WP.seq (WP.mono (head_ok s P) fun sY hH => ?_)
  refine WP.seq (WP.mono (blocks_loop hH.loop (s.gpr .a3).isLt hpos hH.inv) fun sL hBL => ?_)
  have hfp := hH.fp
  have hslot : ∀ p ∈ saved, sL.mem.readW ((allocd 2048 s).sp + BitVec.ofNat 64 p.2) 64 = s.gpr p.1 := by
    intro p hp
    have hd : 320 ≤ p.2 ∧ p.2 + 8 ≤ 400 := by
      simp only [saved, slot, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have c : (⟨(allocd 2048 s).sp + BitVec.ofNat 64 p.2, 8⟩ : Region).Contains
        ((allocd 2048 s).sp + BitVec.ofNat 64 p.2) 8 := Region.contains_self _ _
    have := hH.slots p hp
    simp only [Mem.readW] at this ⊢
    rw [Frame.read hBL.frame c (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      rw [hfp]; exact slot_disj _ (by omega) (by omega)) (by decide)]
    exact this
  have hyp : sL.gpr YP = s.gpr .a1 := by rw [Keep.gpr hBL.keep (by decide), hH.yp]
  have hwrL : sL.wr = (allocd 2048 s).wr := by rw [hBL.keep.2.2, hH.wr]
  have hspL : sL.sp = (allocd 2048 s).sp := by rw [hBL.sp, hH.sp]
  have T := tail_ok s P sL hBL.y hyp hwrL hspL hslot
  refine WP.mono T fun t h => ?_
  refine ⟨?_, fun r hr => h.2.1 r hr⟩
  have h1 := h.1
  simp only [ghashX, freed]
  exact h1

/-- The registers the code writes: no preserved register but those it saves and restores, nor `ra`. -/
def written : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a2, .a3, .a4, .a5, .a6, .a7,
  .s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9]

theorem ghash_correct (s : State) (hs : ghashX.pre s) :
    ∃ t s', Exec isa ghash s t s' ∧ abiPreserved s s' ∧ ghashX.post s s' := by
  obtain ⟨tr, t, he, ⟨hpost, hsv⟩, hkeep⟩ := WP.keep written (ghash_ok s hs) (by lit_decide) (by lit_decide)
  refine ⟨tr, t, he, ⟨fun r hr => ?_, Exec.sp he, hkeep.gpr (by decide)⟩, hpost⟩
  by_cases h : r ∈ saved.map Prod.fst
  · exact hsv r h
  · exact hkeep.gpr (by revert hr h; revert r; decide)

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
