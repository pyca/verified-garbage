module

import VerifiedGarbage.Proof.Framework.OmegaNear
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Bignum.CrtExp
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSA with the CRT on x86-64: gathering a table entry with AVX2

`Crt.gatherPassV` (`Impl/Rsa/X86_64/Crt.lean`) is `Crt.gatherPass` with the
masks broadcast to whole `ymm` registers: each step replaces the words of
`[rbx]` at `r14`, four (`.l256`, two lanes) or two (`.l128`, one), by
`OR_j (mask_j & T_j) | (keep & [rbx])` (`gChunkV_ok`), the words read a
lane at a time (`q128` of `lane`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

/-- The lanes of a VEX length. -/
def nl : VLen → Nat
  | .l128 => 1
  | .l256 => 2

/-- Quadword `q` of lane `l` of a 256-bit read. -/
theorem q_read256 (m : Mem) (a : Addr) {l q : Nat} (hl : l < 2) (hq : q < 2) :
    q128 (if l = 0 then (m.readW a 256).extractLsb' 0 128 else (m.readW a 256).extractLsb' 128 128) q =
      m.readW (a + BitVec.ofNat 64 (16 * l + 8 * q)) 64 := by
  have e : (if l = 0 then (m.readW a 256).extractLsb' 0 128 else (m.readW a 256).extractLsb' 128 128) =
      (m.readW a 256).extractLsb' (128 * l) 128 := by
    rcases (by omega_near : l = 0 ∨ l = 1) with rfl | rfl <;> rfl
  rw [e, q128, qword, extract_extract _ _ _ _ _ (by omega_near), show 128 * l + 64 * q = 8 * (16 * l + 8 * q) by omega_near]
  exact readW_extract m a (k := 16 * l + 8 * q) (n := 8) (by omega_near)

/-- Quadword `q` of a 128-bit read. -/
theorem q_read128 (m : Mem) (a : Addr) {q : Nat} (hq : q < 2) :
    q128 (m.readW a 128) q = m.readW (a + BitVec.ofNat 64 (8 * q)) 64 := by
  rw [q128, qword, show 64 * q = 8 * (8 * q) by omega_near]
  exact readW_extract m a (k := 8 * q) (n := 8) (by omega_near)

/-- A 256-bit write of a register, read back a quadword at a time. -/
theorem read_write256 (m : Mem) (a : Addr) (hi lo : BitVec 128) {l q : Nat} (hl : l < 2) (hq : q < 2) :
    (m.writeW a (hi ++ lo)).readW (a + BitVec.ofNat 64 (16 * l + 8 * q)) 64 = q128 (if l = 0 then lo else hi) q := by
  have e := readW_writeW_inside m a (hi ++ lo) (k := 16 * l + 8 * q) (n := 8) (by omega_near) (by decide)
  rw [show 8 * 8 = 64 by rfl] at e
  rw [e]
  apply BitVec.eq_of_getLsbD_eq; intro i hi'
  simp only [q128, qword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, decide_eq_true hi', Bool.true_and]
  rcases (by omega_near : l = 0 ∨ l = 1) with rfl | rfl
  · simp only [show 8 * (16 * 0 + 8 * q) + i < 128 by omega_near, ↓reduceIte]
    exact congrArg _ (by omega_near)
  · simp only [show ¬ 8 * (16 * 1 + 8 * q) + i < 128 by omega_near, Nat.one_ne_zero, ↓reduceIte]
    exact congrArg _ (by omega_near)

/-- A 128-bit write, read back a quadword at a time. -/
theorem read_write128' (m : Mem) (a : Addr) (v : BitVec 128) {q : Nat} (hq : q < 2) :
    (m.writeW a v).readW (a + BitVec.ofNat 64 (8 * q)) 64 = q128 v q := by
  have e := readW_writeW_inside m a v (k := 8 * q) (n := 8) (by omega_near) (by decide)
  rw [show 8 * (8 * q) = 64 * q by omega_near, show 8 * 8 = 64 by rfl] at e
  exact e

/-- `n` bytes of the working space are readable and writable. -/
theorem inRegionsN {s : State} {B : Addr} {Z : Nat} (hs : Scr s B Z) {d n : Nat} (hd : d + n ≤ Z) (hn : 0 < n) :
    InRegions (s.rd ++ s.wr) (off B d) n ∧ InRegions s.wr (off B d) n := by
  obtain ⟨r, hr, hc⟩ := hs.region hd hn
  exact ⟨⟨r, List.mem_append_right _ hr, hc⟩, ⟨r, hr, hc⟩⟩

/-- What a step leaves of the vector registers but `xmm0` and `xmm1`. -/
def VKeep01 (s t : State) : Prop := ∀ y, y ≠ .xmm0 → y ≠ .xmm1 → ∀ l, t.lane y l = s.lane y l

/-! ## A step -/

/-- `xmm0 |= x & [b + 8 r14]`, lane by lane. -/
theorem gOrV_ok (L : VLen) {s : State} {B : Addr} {Z e c : Nat} (hs : Scr s B Z) {b : Reg} {x : XReg}
    (hb : s.gpr b = off B e) (h14 : s.gpr .r14 = BitVec.ofNat 64 c)
    (he : e + 8 * c + 16 * nl L ≤ Z) :
    WP isa (.block (Crt.gatherOrV L b x)) s fun t =>
      (∀ l < nl L, ∀ q < 2, q128 (t.lane .xmm0 l) q =
        q128 (s.lane .xmm0 l) q ||| (q128 (s.lane x l) q &&& word s.mem B (e + 8 * c + 16 * l + 8 * q))) ∧
      VKeep01 s t ∧ t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hn := hs.nowrap
  have eA : s.ea (ix b .r14) = off B (e + 8 * c) := ea_ix0 s hb h14
  cases L with
  | l256 =>
    obtain ⟨iA, -⟩ := inRegionsN hs (d := e + 8 * c) (n := 32) (by simp only [nl] at he; omega_near) (by decide)
    apply WP.of_runBlock
    simp only [Crt.gatherOrV, runBlock_cons, runStep_some, runBlock_nil, exec, eA, State.load256, iA, ite_true,
      Option.map_some, Option.some.injEq, exists_eq_left']
    refine ⟨fun l hl q hq => ?_, fun y h0 h1 l => ?_, rfl, rfl, rfl, rfl⟩
    · simp only [nl] at hl
      simp only [lane_vbin256, State.lane_setV256, ↓reduceIte, show XReg.xmm0 ≠ XReg.xmm1 by decide,
        VBinOp.sse, XBinOp.eval]
      rcases (by omega_near : l = 0 ∨ l = 1) with rfl | rfl
      · simp only [↓reduceIte]
        rw [q128_or, q128_and, show (s.mem.readW (off B (e + 8 * c)) 256).extractLsb' 0 128 =
          (if (0 : Nat) = 0 then (s.mem.readW (off B (e + 8 * c)) 256).extractLsb' 0 128 else
            (s.mem.readW (off B (e + 8 * c)) 256).extractLsb' 128 128) from rfl, q_read256 _ _ (by decide) hq,
          off_add_eq, ← Nat.add_assoc]
      · simp only [Nat.one_ne_zero, ↓reduceIte]
        rw [q128_or, q128_and, show (s.mem.readW (off B (e + 8 * c)) 256).extractLsb' 128 128 =
          (if (1 : Nat) = 0 then (s.mem.readW (off B (e + 8 * c)) 256).extractLsb' 0 128 else
            (s.mem.readW (off B (e + 8 * c)) 256).extractLsb' 128 128) from rfl, q_read256 _ _ (by decide) hq,
          off_add_eq, ← Nat.add_assoc]
    · simp only [lane_vbin256, State.lane_setV256, h0, h1, ↓reduceIte]
  | l128 =>
    obtain ⟨iA, -⟩ := inRegionsN hs (d := e + 8 * c) (n := 16) (by simp only [nl] at he; omega_near) (by decide)
    apply WP.of_runBlock
    simp only [Crt.gatherOrV, runBlock_cons, runStep_some, runBlock_nil, exec, eA, State.load128, iA, ite_true,
      Option.map_some, Option.some.injEq, exists_eq_left']
    refine ⟨fun l hl q hq => ?_, fun y h0 h1 l => ?_, rfl, rfl, rfl, rfl⟩
    · simp only [nl] at hl
      obtain rfl : l = 0 := by omega_near
      simp only [lane_vbin128, State.lane_setV128, ↓reduceIte, show XReg.xmm0 ≠ XReg.xmm1 by decide,
        VBinOp.sse, XBinOp.eval]
      rw [q128_or, q128_and, q_read128 _ _ hq, off_add_eq]
      simp only [Nat.mul_zero, Nat.add_zero]
    · simp only [lane_vbin128, State.lane_setV128, h0, h1, ↓reduceIte]

/-- A write of `w` bits changes only those bytes. -/
theorem writeW_outsideV (m : Mem) (base : Addr) {d w : Nat} (v : BitVec w) (h : d + w / 8 ≤ 2 ^ 64)
    (hw : 0 < w / 8) :
    Outside base d (w / 8) m (m.writeW (off base d) v) := by
  intro x hx
  apply Mem.write_apply
  simp only [ofs] at hx
  have : (x - off base d).toNat = (2 ^ 64 - d + (x - base).toNat) % 2 ^ 64 :=
    Offset.toNat_sub_add x base (by omega_near)
  rw [this]
  have := (x - base).isLt
  rcases hx with hx | hx
  · rw [Nat.mod_eq_of_lt (by omega_near)]; omega_near
  · rw [show 2 ^ 64 - d + (x - base).toNat = (x - base).toNat - d + 2 ^ 64 by omega_near,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_near)]
    omega_near

/-- `xmm0 := xmm8 & [rcx + 8 r14]`, lane by lane. -/
theorem gFirstV_ok (L : VLen) {s : State} {B : Addr} {Z e c : Nat} (hs : Scr s B Z)
    (hb : s.gpr .rcx = off B e) (h14 : s.gpr .r14 = BitVec.ofNat 64 c) (he : e + 8 * c + 16 * nl L ≤ Z) :
    WP isa (.block [.vbinLoad .vpand L .xmm0 .xmm8 (ix .rcx .r14)]) s fun t =>
      (∀ l < nl L, ∀ q < 2, q128 (t.lane .xmm0 l) q = q128 (s.lane .xmm8 l) q &&& word s.mem B (e + 8 * c + 16 * l + 8 * q)) ∧
      VKeep01 s t ∧ t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hn := hs.nowrap
  have eA : s.ea (ix .rcx .r14) = off B (e + 8 * c) := ea_ix0 s hb h14
  cases L with
  | l256 =>
    obtain ⟨iA, -⟩ := inRegionsN hs (d := e + 8 * c) (n := 32) (by simp only [nl] at he; omega_near) (by decide)
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, eA, State.load256, iA, ite_true,
      Option.map_some, Option.some.injEq, exists_eq_left']
    refine ⟨fun l hl q hq => ?_, fun y h0 _ l => ?_, rfl, rfl, rfl, rfl⟩
    · simp only [nl] at hl
      simp only [State.lane_setV256, ↓reduceIte, VBinOp.sse, XBinOp.eval]
      rcases (by omega_near : l = 0 ∨ l = 1) with rfl | rfl
      · simp only [↓reduceIte]
        rw [q128_and, show (s.mem.readW (off B (e + 8 * c)) 256).extractLsb' 0 128 =
          (if (0 : Nat) = 0 then (s.mem.readW (off B (e + 8 * c)) 256).extractLsb' 0 128 else
            (s.mem.readW (off B (e + 8 * c)) 256).extractLsb' 128 128) from rfl, q_read256 _ _ (by decide) hq,
          off_add_eq, ← Nat.add_assoc]
      · simp only [Nat.one_ne_zero, ↓reduceIte]
        rw [q128_and, show (s.mem.readW (off B (e + 8 * c)) 256).extractLsb' 128 128 =
          (if (1 : Nat) = 0 then (s.mem.readW (off B (e + 8 * c)) 256).extractLsb' 0 128 else
            (s.mem.readW (off B (e + 8 * c)) 256).extractLsb' 128 128) from rfl, q_read256 _ _ (by decide) hq,
          off_add_eq, ← Nat.add_assoc]
    · simp only [State.lane_setV256, h0, ↓reduceIte]
  | l128 =>
    obtain ⟨iA, -⟩ := inRegionsN hs (d := e + 8 * c) (n := 16) (by simp only [nl] at he; omega_near) (by decide)
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, eA, State.load128, iA, ite_true,
      Option.map_some, Option.some.injEq, exists_eq_left']
    refine ⟨fun l hl q hq => ?_, fun y h0 _ l => ?_, rfl, rfl, rfl, rfl⟩
    · simp only [nl] at hl
      obtain rfl : l = 0 := by omega_near
      simp only [State.lane_setV128, ↓reduceIte, VBinOp.sse, XBinOp.eval]
      rw [q128_and, q_read128 _ _ hq, off_add_eq]
      simp only [Nat.mul_zero, Nat.add_zero]
    · simp only [State.lane_setV128, h0, ↓reduceIte]

/-- The store of `xmm0` at `[rbx + 8 r14]`, and `r14 += n`. -/
theorem gStoreV_ok (L : VLen) {s : State} {B : Addr} {Z e c n : Nat} (hs : Scr s B Z)
    (hb : s.gpr .rbx = off B e) (h14 : s.gpr .r14 = BitVec.ofNat 64 c) (he : e + 8 * c + 16 * nl L ≤ Z)
    (hn : n = 2 ∨ n = 4) :
    WP isa (.block [.vmovdquStore L (ix .rbx .r14) .xmm0, .alu .add .r14 (.imm (BitVec.ofNat 32 n))]) s fun t =>
      (∀ l < nl L, ∀ q < 2, word t.mem B (e + 8 * c + 16 * l + 8 * q) = q128 (s.lane .xmm0 l) q) ∧
      Outside B (e + 8 * c) (16 * nl L) s.mem t.mem ∧ t.gpr .r14 = BitVec.ofNat 64 c + BitVec.ofNat 64 n ∧
      (∀ r, r ≠ .r14 → t.gpr r = s.gpr r) ∧ (∀ y l, t.lane y l = s.lane y l) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hnw := hs.nowrap
  have eO : s.ea (ix .rbx .r14) = off B (e + 8 * c) := ea_ix0 s hb h14
  have himm : (BitVec.ofNat 32 n).signExtend 64 = BitVec.ofNat 64 n := by
    rcases hn with rfl | rfl <;> decide
  have hadd : ∀ t : State, t.gpr .r14 = BitVec.ofNat 64 c →
      WP isa (.block [.alu .add .r14 (.imm (BitVec.ofNat 32 n))]) t fun t' =>
        t'.gpr .r14 = BitVec.ofNat 64 c + BitVec.ofNat 64 n ∧ (∀ r, r ≠ .r14 → t'.gpr r = t.gpr r) ∧
        t'.mem = t.mem ∧ (∀ y l, t'.lane y l = t.lane y l) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := fun t h => by
    refine WP.mono (WP.keep [.r14] (Q := fun t' => t'.gpr .r14 = BitVec.ofNat 64 c + BitVec.ofNat 64 n ∧
      t'.mem = t.mem ∧ ∀ y l, t'.lane y l = t.lane y l) (by xrun [h, himm]; exact fun _ _ => rfl) rfl)
      fun t' ⟨⟨h1, h2, h3⟩, k⟩ =>
      ⟨h1, fun r hr => k.1 r (by simpa using hr), h2, h3, k.2.1, k.2.2⟩
  cases L with
  | l256 =>
    obtain ⟨-, sO⟩ := inRegionsN hs (d := e + 8 * c) (n := 32) (by simp only [nl] at he; omega_near) (by decide)
    rw [WP.block_cons_iff]
    refine ⟨{ s with mem := s.mem.writeW (off B (e + 8 * c)) (s.ymm .xmm0) },
      by simp only [exec, eO, State.store256, sO, ite_true], ?_⟩
    refine WP.mono (hadd _ h14) fun t ⟨h1, h2, hm, hl, hrd, hwr⟩ => ⟨fun l hl' q hq => ?_, ?_, h1, h2, hl, hrd, hwr⟩
    · simp only [nl] at hl'
      rw [hm]
      show (s.mem.writeW (off B (e + 8 * c)) (s.ymm .xmm0)).readW (off B (e + 8 * c + 16 * l + 8 * q)) 64 = _
      rw [Nat.add_assoc (e + 8 * c), show off B (e + 8 * c + (16 * l + 8 * q)) =
        off B (e + 8 * c) + BitVec.ofNat 64 (16 * l + 8 * q) from (off_add_eq _ _ _).symm, State.ymm_eq,
        read_write256 _ _ _ _ hl' hq]
      rcases (by omega_near : l = 0 ∨ l = 1) with rfl | rfl <;> rfl
    · rw [hm]; exact writeW_outsideV s.mem B (d := e + 8 * c) (s.ymm .xmm0) (by simp only [nl] at he; omega_near) (by decide)
  | l128 =>
    obtain ⟨-, sO⟩ := inRegionsN hs (d := e + 8 * c) (n := 16) (by simp only [nl] at he; omega_near) (by decide)
    rw [WP.block_cons_iff]
    refine ⟨{ s with mem := s.mem.writeW (off B (e + 8 * c)) (s.xmm .xmm0) },
      by simp only [exec, eO, State.store128, sO, ite_true], ?_⟩
    refine WP.mono (hadd _ h14) fun t ⟨h1, h2, hm, hl, hrd, hwr⟩ => ⟨fun l hl' q hq => ?_, ?_, h1, h2, hl, hrd, hwr⟩
    · simp only [nl] at hl'
      obtain rfl : l = 0 := by omega_near
      rw [hm]
      show (s.mem.writeW (off B (e + 8 * c)) (s.xmm .xmm0)).readW (off B (e + 8 * c + 16 * 0 + 8 * q)) 64 = _
      rw [Nat.mul_zero, Nat.add_zero, show off B (e + 8 * c + 8 * q) = off B (e + 8 * c) + BitVec.ofNat 64 (8 * q)
        from (off_add_eq _ _ _).symm, read_write128' _ _ _ hq]
      rfl
    · rw [hm]; exact writeW_outsideV s.mem B (d := e + 8 * c) (s.xmm .xmm0) (by simp only [nl] at he; omega_near) (by decide)

/-! ## A chunk of words -/

/-- The registers of pass `p` of the selection with AVX2: as `GRegs`, the
masks in every lane, the keep mask that of `p ≠ 0`, and `r12` the words
below which the chunks have four. -/
structure GRegsV (B : Addr) (wx p v : Nat) (s : State) : Prop where
  base : ∀ k < 8, s.gpr (gReg k) = off B (slot wx (8 + 8 * p + k))
  bx : s.gpr .rbx = off B (slot wx Crt.aT)
  r13 : s.gpr .r13 = BitVec.ofNat 64 (2 * ((wx + 1) / 2))
  r12 : s.gpr .r12 = BitVec.ofNat 64 (4 * ((wx + 1) / 2 / 2))
  msk : ∀ k < 8, ∀ l < 2, ∀ q < 2, q128 (s.lane (gX k) l) q = mask (decide (8 * p + k = v))
  keep : ∀ l < 2, ∀ q < 2, q128 (s.lane .xmm7 l) q = mask (decide (p ≠ 0))

theorem GRegsV.congr {B : Addr} {wx p v : Nat} {s t : State} (h : GRegsV B wx p v s)
    (hg : ∀ r, r ≠ .r14 → t.gpr r = s.gpr r) (hx : VKeep01 s t) : GRegsV B wx p v t :=
  ⟨fun k hk => (hg _ (gReg_ne k hk)).trans (h.base k hk), (hg _ (by decide)).trans h.bx,
    (hg _ (by decide)).trans h.r13, (hg _ (by decide)).trans h.r12,
    fun k hk l hl q hq => by rw [hx _ (gX_ne k hk).1 (gX_ne k hk).2.1]; exact h.msk k hk l hl q hq,
    fun l hl q hq => by rw [hx _ (by decide) (by decide)]; exact h.keep l hl q hq⟩

/-- Word `k` of `[aT]` after pass `p` with AVX2, from memory `m`. -/
def gvalV (m : Mem) (B : Addr) (wx p v k : Nat) : BitVec 64 :=
  gacc (fun j => word m B (slot wx (8 + 8 * p + j) + 8 * k)) (8 * p) v 7 |||
    (word m B (slot wx Crt.aT + 8 * k) &&& mask (decide (p ≠ 0)))

/-- After the entries `8 p` to `8 p + n` of the chunk at word `c`, from `s`. -/
structure GathAccV (s : State) (B : Addr) (wx p v c : Nat) (L : VLen) (n : Nat) (t : State) : Prop where
  acc : ∀ l < nl L, ∀ q < 2, q128 (t.lane .xmm0 l) q =
    gacc (fun j => word s.mem B (slot wx (8 + 8 * p + j) + 8 * c + 16 * l + 8 * q)) (8 * p) v n
  xmm : VKeep01 s t
  gpr : t.gpr = s.gpr
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem nl_le (L : VLen) : nl L ≤ 2 := by cases L <;> decide

/-- The chunk at word `c` of an entry is within the table. -/
theorem gEntV_le (wx : Nat) {j c : Nat} (L : VLen) (hj : j < 32) (hc : c + 2 * nl L ≤ wx + 2) :
    slot wx (8 + j) + 8 * c + 16 * nl L ≤ slot wx 8 + tabBytes wx 32 := by
  have := ent_le wx hj; unfold slot at *; omega_near

/-- The chunk at word `c` of `[aT]` is within its array. -/
theorem gTV_le (wx : Nat) {c : Nat} (L : VLen) (hc : c + 2 * nl L ≤ wx + 2) :
    slot wx Crt.aT + 8 * c + 16 * nl L ≤ slot wx 8 + tabBytes wx 32 := by
  have := slot_succ wx Crt.aT
  have := slot_mono wx (show Crt.aT + 1 ≤ 8 by decide)
  unfold tabBytes; omega_near

theorem gAccV0 (L : VLen) {s : State} {B : Addr} {wx p v c : Nat} (hs : Scr s B (slot wx 8 + tabBytes wx 32))
    (hG : GRegsV B wx p v s) (hp : p < 4) (h14 : s.gpr .r14 = BitVec.ofNat 64 c) (hc : c + 2 * nl L ≤ wx + 2) :
    WP isa (.block [.vbinLoad .vpand L .xmm0 .xmm8 (ix .rcx .r14)]) s (GathAccV s B wx p v c L 0) := by
  have hb := hG.base 0 (by decide)
  rw [Nat.add_zero] at hb
  refine WP.mono (gFirstV_ok L hs hb h14 (gEntV_le wx (j := 8 * p) L (by omega_near) hc))
    fun t ⟨hx0, hx, hg, hm, hrd, hwr⟩ => ⟨fun l hl q hq => ?_, hx, hg, hm, hrd, hwr⟩
  rw [hx0 l hl q hq, show s.lane .xmm8 l = s.lane (gX 0) l from rfl,
    hG.msk 0 (by decide) l (by have := nl_le L; omega_near) q hq, BitVec.and_comm]
  rfl

theorem gAccV_step (L : VLen) {s t : State} {B : Addr} {wx p v c n : Nat} (hs : Scr s B (slot wx 8 + tabBytes wx 32))
    (hG : GRegsV B wx p v s) (hp : p < 4) (h14 : s.gpr .r14 = BitVec.ofNat 64 c) (hc : c + 2 * nl L ≤ wx + 2)
    (hn : n < 7) (hA : GathAccV s B wx p v c L n t) :
    WP isa (.block (Crt.gatherOrV L (gReg (n + 1)) (gX (n + 1)))) t (GathAccV s B wx p v c L (n + 1)) := by
  have hb : t.gpr (gReg (n + 1)) = off B (slot wx (8 + 8 * p + (n + 1))) := by
    rw [hA.gpr]; exact hG.base _ (by omega_near)
  have hnx := gX_ne (n + 1) (by omega_near)
  refine WP.mono (gOrV_ok L (hs.congr hA.wr) (Nat.add_assoc 8 (8 * p) (n + 1) ▸ hb) (by rw [hA.gpr]; exact h14)
      (gEntV_le wx (j := 8 * p + (n + 1)) L (by omega_near) hc))
    fun t' ⟨hx0, hx, hg, hm, hrd, hwr⟩ => ⟨fun l hl q hq => ?_, fun y h0 h1 l => (hx y h0 h1 l).trans (hA.xmm y h0 h1 l),
      hg.trans hA.gpr, hm.trans hA.mem, hrd.trans hA.rd, hwr.trans hA.wr⟩
  rw [hx0 l hl q hq, hA.acc l hl q hq, hA.xmm _ hnx.1 hnx.2.1, hG.msk _ (by omega_near) l (by have := nl_le L; omega_near) q hq,
    hA.mem, BitVec.and_comm]
  simp only [gacc, Nat.add_assoc]

/-- The chunk at word `c` of a pass: `[aT] := ([aT] & keep) | OR_j (T_(8p+j) & mask_j)`, and `r14 += n`. -/
theorem gChunkV_ok (L : VLen) {s : State} {B : Addr} {wx p v c n : Nat} (hs : Scr s B (slot wx 8 + tabBytes wx 32))
    (hG : GRegsV B wx p v s) (hp : p < 4) (h14 : s.gpr .r14 = BitVec.ofNat 64 c) (hc : c + 2 * nl L ≤ wx + 2)
    (hn : n = 2 * nl L) :
    WP isa (.block (Crt.gatherBodyV L n)) s fun t =>
      (∀ k < 2 * nl L, word t.mem B (slot wx Crt.aT + 8 * (c + k)) = gvalV s.mem B wx p v (c + k)) ∧
      Outside B (slot wx Crt.aT + 8 * c) (16 * nl L) s.mem t.mem ∧
      t.gpr .r14 = BitVec.ofNat 64 c + BitVec.ofNat 64 n ∧ (∀ r, r ≠ .r14 → t.gpr r = s.gpr r) ∧
      VKeep01 s t ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hnl := nl_le L
  simp only [Crt.gatherBodyV, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (gAccV0 L hs hG hp h14 hc) fun t₀ a₀ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (gAccV_step (n := 0) L hs hG hp h14 hc (by decide) a₀) fun t₁ a₁ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (gAccV_step (n := 1) L hs hG hp h14 hc (by decide) a₁) fun t₂ a₂ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (gAccV_step (n := 2) L hs hG hp h14 hc (by decide) a₂) fun t₃ a₃ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (gAccV_step (n := 3) L hs hG hp h14 hc (by decide) a₃) fun t₄ a₄ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (gAccV_step (n := 4) L hs hG hp h14 hc (by decide) a₄) fun t₅ a₅ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (gAccV_step (n := 5) L hs hG hp h14 hc (by decide) a₅) fun t₆ a₆ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (gAccV_step (n := 6) L hs hG hp h14 hc (by decide) a₆) fun t₇ a₇ => ?_
  rw [WP.block_append_iff]
  have hT := gTV_le wx L hc
  refine WP.mono (gOrV_ok L (hs.congr a₇.wr) (x := .xmm7) (by rw [a₇.gpr]; exact hG.bx) (by rw [a₇.gpr]; exact h14)
    hT) fun t₈ ⟨hx0, hx, hg, hm, hrd, hwr⟩ => ?_
  refine WP.mono (gStoreV_ok L (hs.congr (hwr.trans a₇.wr)) (by rw [hg, a₇.gpr]; exact hG.bx)
    (by rw [hg, a₇.gpr]; exact h14) hT (by cases L <;> simp only [nl] at hn <;> omega_near))
    fun t ⟨hw', ho, h14', hg', hl', hrd', hwr'⟩ => ⟨fun k hk => ?_, by rw [hm, a₇.mem] at ho; exact ho, h14',
      fun r hr => by rw [hg' r hr, hg, a₇.gpr], fun y h0 h1 l => by rw [hl', hx y h0 h1 l, a₇.xmm y h0 h1 l],
      by rw [hrd', hrd, a₇.rd], by rw [hwr', hwr, a₇.wr]⟩
  obtain ⟨l, q, hl, hq, rfl⟩ : ∃ l q, l < nl L ∧ q < 2 ∧ k = 2 * l + q :=
    ⟨k / 2, k % 2, by omega_near, Nat.mod_lt _ (by decide), by omega_near⟩
  rw [show slot wx Crt.aT + 8 * (c + (2 * l + q)) = slot wx Crt.aT + 8 * c + 16 * l + 8 * q by omega_near, hw' l hl q hq,
    hx0 l hl q hq, a₇.acc l hl q hq, a₇.xmm _ (by decide) (by decide), hG.keep l (by omega_near) q hq, a₇.mem,
    BitVec.and_comm]
  unfold gvalV
  simp only [show ∀ j, slot wx (8 + 8 * p + j) + 8 * c + 16 * l + 8 * q = slot wx (8 + 8 * p + j) + 8 * (c + (2 * l + q))
    from fun j => by omega_near, show slot wx Crt.aT + 8 * c + 16 * l + 8 * q = slot wx Crt.aT + 8 * (c + (2 * l + q)) by omega_near]

/-! ## The chunks of a pass -/

theorem gvalV_congr {m m' : Mem} {B : Addr} {wx p v k : Nat}
    (he : ∀ j < 8, word m' B (slot wx (8 + 8 * p + j) + 8 * k) = word m B (slot wx (8 + 8 * p + j) + 8 * k))
    (hT : word m' B (slot wx Crt.aT + 8 * k) = word m B (slot wx Crt.aT + 8 * k)) :
    gvalV m' B wx p v k = gvalV m B wx p v k := by
  unfold gvalV
  rw [hT, gacc_congr fun j hj => he j (by omega_near)]

/-- After the chunks of a pass below word `c`, from `s`. -/
structure GathInvV (s : State) (B : Addr) (wx p v c : Nat) (t : State) : Prop where
  r14 : t.gpr .r14 = BitVec.ofNat 64 c
  gpr : ∀ r, r ≠ .r14 → t.gpr r = s.gpr r
  xmm : VKeep01 s t
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  out : Outside B (slot wx Crt.aT) (8 * c) s.mem t.mem
  val : ∀ k < c, word t.mem B (slot wx Crt.aT + 8 * k) = gvalV s.mem B wx p v k

theorem GathInvV.init {s : State} {B : Addr} {wx p v : Nat} (h14 : s.gpr .r14 = BitVec.ofNat 64 0) :
    GathInvV s B wx p v 0 s :=
  ⟨h14, fun _ _ => rfl, fun _ _ _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩

/-- The chunk at word `c`, from the invariant below `c`. -/
theorem gStepV_ok (L : VLen) {s t : State} {B : Addr} {wx p v c n : Nat} (hs : Scr s B (slot wx 8 + tabBytes wx 32))
    (hG : GRegsV B wx p v s) (hp : p < 4) (hc : c + 2 * nl L ≤ wx + 2) (hn : n = 2 * nl L)
    (hI : GathInvV s B wx p v c t) :
    WP isa (.block (Crt.gatherBodyV L n)) t fun t' =>
      GathInvV s B wx p v (c + 2 * nl L) t' ∧ t'.gpr .r14 = BitVec.ofNat 64 c + BitVec.ofNat 64 n := by
  have hnw := hs.nowrap
  have hnl := nl_le L
  have hTa := slot_succ wx Crt.aT
  have hT8 := slot_mono wx (show Crt.aT + 1 ≤ 8 by decide)
  have hT0 := slot_le (w := wx) (show Crt.aT < 8 by decide)
  refine WP.mono (gChunkV_ok L (hs.congr hI.wr) (hG.congr hI.gpr hI.xmm) hp hI.r14 hc hn)
    fun t' ⟨hv, ho, h14, hg, hx, hrd, hwr⟩ => ⟨⟨by rw [h14, hn, ← BitVec.ofNat_add],
      fun r hr => (hg r hr).trans (hI.gpr r hr), fun y h0 h1 l => (hx y h0 h1 l).trans (hI.xmm y h0 h1 l),
      hrd.trans hI.rd, hwr.trans hI.wr, (hI.out.mono (Nat.le_refl _) (by omega_near)).trans (ho.mono (by omega_near) (by omega_near)),
      fun k hk => ?_⟩, h14⟩
  by_cases hkc : k < c
  · rw [ho.word (by omega_near) (by omega_near), hI.val k hkc]
  obtain ⟨i, hi, rfl⟩ : ∃ i, i < 2 * nl L ∧ k = c + i := ⟨k - c, by omega_near, by omega_near⟩
  rw [hv i hi]
  refine gvalV_congr (fun j hj => ?_) ?_
  · have := ent_le wx (n := 32) (j := 8 * p + j) (by omega_near)
    have := slot_mono wx (show 8 ≤ 8 + (8 * p + j) by omega_near)
    rw [show 8 + 8 * p + j = 8 + (8 * p + j) by omega_near]
    exact hI.out.word (by omega_near) (by unfold slot at *; omega_near)
  · exact hI.out.word (by omega_near) (by omega_near)

/-- The four-word chunks of a pass: every word below `4 N`. -/
theorem gLoopV_ok {s : State} {B : Addr} {wx p v N : Nat} (hs : Scr s B (slot wx 8 + tabBytes wx 32))
    (hG : GRegsV B wx p v s) (hp : p < 4) (h14 : s.gpr .r14 = BitVec.ofNat 64 0) (hN : 0 < N)
    (hN' : 4 * N ≤ wx + 1) (hw' : wx < 2 ^ 30) (h12 : s.gpr .r12 = BitVec.ofNat 64 (4 * N)) :
    WP isa (.loop (.block (Crt.gatherBodyV .l256 4 ++ ([.alu .cmp .r14 (.reg .r12)] : List Instr))) .ne) s
      (GathInvV s B wx p v (4 * N)) := by
  refine wp_upto (a := 0) (N := N) hN (fun j => GathInvV s B wx p v (4 * j)) (fun j _ hj t hI => ?_) (fun t h => h)
    (by simpa using GathInvV.init h14)
  rw [WP.block_append_iff]
  refine WP.mono (gStepV_ok .l256 hs hG hp (c := 4 * j) (by simp only [nl]; omega_near) rfl hI)
    fun t' ⟨hI', h14'⟩ => ?_
  have h12' : t'.gpr .r12 = BitVec.ofNat 64 (4 * N) := (hI'.gpr _ (by decide)).trans h12
  have hadd : BitVec.ofNat 64 (4 * j) + BitVec.ofNat 64 4 = BitVec.ofNat 64 (4 * (j + 1)) := by
    rw [← BitVec.ofNat_add]; congr 1
  refine WP.mono (WP.keep [.r14] (Q := fun t'' => t''.zf = some (decide (j + 1 = N)) ∧ t''.mem = t'.mem ∧
      (∀ y l, t''.lane y l = t'.lane y l) ∧ t''.gpr .r14 = t'.gpr .r14) (by
    xrun [h14', h12', hadd, ofNat_sub_beq (show 4 * (j + 1) < 2 ^ 64 by omega_near) (show 4 * N < 2 ^ 64 by omega_near)]
    exact ⟨decide_eq_decide.mpr ⟨fun h => by omega_near, fun h => by omega_near⟩, fun _ _ => rfl⟩) rfl) fun t'' ⟨⟨hz, hm, hl, h14''⟩, k⟩ => ⟨hz, ?_⟩
  have hk : ∀ r, r ≠ .r14 → t''.gpr r = t'.gpr r := fun r hr => k.1 r (by simpa using hr)
  exact ⟨by rw [h14'', h14', hadd], fun r hr => by rw [hk r hr]; exact hI'.gpr r hr,
    fun y h0 h1 l => (hl y l).trans (hI'.xmm y h0 h1 l), k.2.1.trans hI'.rd, k.2.2.trans hI'.wr,
    by rw [hm]; simpa [nl, Nat.mul_add] using hI'.out, fun k' hk' => by rw [hm]; exact hI'.val k' (by simp only [nl]; omega_near)⟩

end VG.Proof.Bignum.X86_64
