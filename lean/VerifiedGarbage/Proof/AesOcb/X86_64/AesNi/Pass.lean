module

public import VerifiedGarbage.Proof.AesOcb.X86_64.AesNi.Group
public import VerifiedGarbage.Proof.AesOcb.X86_64.AesNi.Setup
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.AesOcb.X86_64.Run
import VerifiedGarbage.Proof.AesCcm.X86_64.Env
import VerifiedGarbage.Proof.Ocb.State
-- separate module: the one-pass proofs are a chain of modules (`Pass`, `Front`, `Top`), so that a change rebuilds only the modules after it

/-!
# One-pass AES-OCB with AES-NI on x86-64: a group as OCB's blocks

Untrusted: everything here is checked by Lean. `group_okB`: `group_ok` with
the registers and the memory read as OCB's blocks (`rv`, `blockAtMem`),
AES as `ENCIPHER` and `DECIPHER` (`bF`), the offsets `o ⊕ c k` of a group
with the offset `o` in `xmm12` and the blocks `c k` of `C`, and the
checksum as a fold of blocks (`xorB`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64.AesNi

open VG VG.X86_64 VG.X86_64.RegUpd
open VG.Spec.Ocb (Block blockAtMem aesWith aesInvWith)
open VG.Proof.AesOcb.X86_64 (rv blockAtMem_eq rv_xor)
open VG.Impl.AesOcb.X86_64AesNi (Mode group cO ofO imcO)
open VG.Impl.Aes.X86_64.AesNi (regs8)
open VG.Proof.Aes.X86_64.AesNi (Keys st)
open VG.Proof.AesCcm.X86_64 (in_off in_left covers_off toNat_ofNat_of_lt eval_e eval_ne eval_b ofNat_sub)
open VG.Impl.AesOcb.X86_64 (addi)
open VG.Impl.AesOcb.X86_64AesNi (l2O l3O ljO c8 tail tailUp pass)
open VG.Spec.Ocb (lAt ntz)
open VG.Proof.Ocb (offAt)

/-- `f 0 ⊕ … ⊕ f (n − 1)`, of blocks. -/
def xorB (f : Nat → Block) : Nat → Block
  | 0 => 0
  | n + 1 => xorB f n ^^^ f n

theorem rv_zero : rv 0 = 0 := by decide

theorem rv_xorN (f : Nat → BitVec 128) (n : Nat) : rv (xorN f n) = xorB (fun k => rv (f k)) n := by
  induction n with
  | zero => exact rv_zero
  | succ n ih => rw [xorN, xorB, rv_xor, ih]

theorem xorB_congr {f g : Nat → Block} {n : Nat} (h : ∀ k < n, f k = g k) : xorB f n = xorB g n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [xorB, xorB, ih (fun k hk => h k (by omega_arith)), h n (by omega_arith)]

/-- AES of a group's mode on blocks: `DECIPHER` for `open`, `ENCIPHER` otherwise. -/
def bF (md : Mode) (nr : Nat) (w : List Byte) : Block → Block :=
  if md = .open then aesInvWith nr w else aesWith nr w

theorem bF_rv {md : Mode} {nr : Nat} {w : List Byte} {v y : BitVec 128}
    (h : st y = (if md = .open then Spec.Aes.invCipher nr w else Spec.Aes.cipher nr w) (st v)) :
    bF md nr w (rv v) = rv y := by
  unfold bF
  by_cases hm : md = .open
  · simp only [hm, ↓reduceIte] at h ⊢; exact aesInvWith_rv h
  · simp only [hm, ↓reduceIte] at h ⊢; exact aesWith_rv h

/-- What a block adds to `xmm10`: its ciphertext (`HASH`), the plaintext
block (`seal`), or the block decrypted (`open`). -/
def term (md : Mode) (F : Block → Block) (p o : Block) : Block :=
  match md with
  | .hash => F (p ^^^ o)
  | .seal => p
  | .open => o ^^^ F (p ^^^ o)

/-- `group_ok` in OCB's blocks: the offset `o` in `xmm12`, `C[k + 1]` the
block `c k`. -/
theorem group_okB (md : Mode) (r : Nat) (hr1 : 1 ≤ r) (hr8 : r ≤ 8) (s : State) {B W : Addr} {wn nr : Nat}
    {w : List Byte} {o : Block} {c : Nat → Block} (hnr : nr = 10 ∨ nr = 12 ∨ nr = 14) (hK : Keys nr w s)
    (hrsi : s.gpr .rsi = BitVec.ofNat 64 nr) (hr10 : s.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * nr))
    (hI : md = .open → ImcAt nr w W s.mem) (h11 : s.gpr .r11 = B) (h15 : s.gpr .r15 = W)
    (hwn : ofO + 128 ≤ wn) (hwo : md = .open → imcO + 224 ≤ wn) (hw : wn < 2 ^ 64)
    (hD : Covers [⟨B, 16 * r⟩] (s.rd ++ s.wr)) (hDw : md ≠ .hash → Covers [⟨B, 16 * r⟩] s.wr)
    (hW : Covers [⟨W, wn⟩] s.wr) (hDW : Region.Disjoint ⟨B, 16 * r⟩ ⟨W, wn⟩)
    (hKW : Region.Disjoint ⟨s.gpr .rdi, 240⟩ ⟨W, wn⟩)
    (hKD : md ≠ .hash → Region.Disjoint ⟨s.gpr .rdi, 240⟩ ⟨B, 16 * r⟩)
    (ho : rv (s.xmm .xmm12) = o) (hc : ∀ k < r, blockAtMem s.mem (at' W (cO + 16 * k)) = c k) :
    WP isa (group md r) s fun s' =>
      (md ≠ .hash → ∀ k < r, blockAtMem s'.mem (at' B (16 * k)) =
        (o ^^^ c k) ^^^ bF md nr w (blockAtMem s.mem (at' B (16 * k)) ^^^ (o ^^^ c k))) ∧
      rv (s'.xmm .xmm10) = rv (s.xmm .xmm10) ^^^
        xorB (fun k => term md (bF md nr w) (blockAtMem s.mem (at' B (16 * k))) (o ^^^ c k)) r ∧
      rv (s'.xmm .xmm12) = o ^^^ c (r - 1) ∧
      s'.gpr .r11 = B + (BitVec.ofNat 32 (16 * r)).signExtend 64 ∧
      (∀ x, x ≠ .r11 → x ≠ .r8 → s'.gpr x = s.gpr x) ∧
      Frame [⟨at' W ofO, 128⟩, ⟨B, 16 * r⟩] s.mem s'.mem ∧
      (md = .hash → Frame [⟨at' W ofO, 128⟩] s.mem s'.mem) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ x, x ∉ regs8 → x ≠ .xmm8 → x ≠ .xmm10 → x ≠ .xmm11 → x ≠ .xmm12 → s'.xmm x = s.xmm x) := by
  refine WP.mono (group_ok md r hr1 hr8 s hnr hK hrsi hr10 hI h11 h15 hwn hwo hw hD hDw hW hDW hKW hKD)
    fun s' ⟨Y, hY, hst, x10, x12, r11, g, fr, frh, rd, wr, xo⟩ => ?_
  have hO : ∀ k < r, rv (s.mem.readW (at' W (cO + 16 * k)) 128 ^^^ s.xmm .xmm12) = o ^^^ c k := fun k hk => by
    rw [rv_xor, ← blockAtMem_eq, hc k hk, ho, BitVec.xor_comm]
  have hYk : ∀ k < r, rv (Y k) = bF md nr w (blockAtMem s.mem (at' B (16 * k)) ^^^ (o ^^^ c k)) := fun k hk => by
    rw [← bF_rv (hY k hk), rv_xor, ← blockAtMem_eq, ← hO k hk]
  refine ⟨fun hm k hk => ?_, ?_, ?_, r11, g, fr, frh, rd, wr, xo⟩
  · rw [blockAtMem_eq, hst hm k hk, rv_xor, hYk k hk, hO k hk, BitVec.xor_comm]
  · rw [x10]
    rcases md with _ | _ | _
    · simp only [↓reduceIte]
      rw [rv_xor, rv_xorN]
      exact congrArg _ (xorB_congr fun k hk => by rw [hYk k hk]; rfl)
    · simp only [reduceCtorEq, ↓reduceIte]
      rw [rv_xor, rv_xorN]
      exact congrArg _ (xorB_congr fun k hk => by rw [← blockAtMem_eq]; rfl)
    · simp only [reduceCtorEq, ↓reduceIte]
      rw [rv_xor, rv_xorN]
      exact congrArg _ (xorB_congr fun k hk => by rw [rv_xor, hYk k hk, hO k hk, BitVec.xor_comm]; rfl)
  · rw [x12, hO (r - 1) (by omega_arith)]

/-! ## The counters -/

/-- After a group of eight: `r13 ← k + 1`, `r12 ← m − 8 (k + 1)`, and CF set
if fewer than eight blocks are left. -/
theorem cnt_ok (t : State) {m k : Nat} (h13 : t.gpr .r13 = BitVec.ofNat 64 k)
    (h12 : t.gpr .r12 = BitVec.ofNat 64 (m - 8 * k)) (hk : 8 * (k + 1) ≤ m) (hm : m < 2 ^ 64) :
    ∃ t', runBlock isa [addi .r13 1, .alu .sub .r12 (.imm 8), .alu .cmp .r12 (.imm 8)] t = some t' ∧
      t'.gpr .r13 = BitVec.ofNat 64 (k + 1) ∧ t'.gpr .r12 = BitVec.ofNat 64 (m - 8 * (k + 1)) ∧
      t'.cf = some (decide (m - 8 * (k + 1) < 8)) ∧ (∀ r, r ≠ .r13 → r ≠ .r12 → t'.gpr r = t.gpr r) ∧
      t'.mem = t.mem ∧ t'.xmm = t.xmm ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have e8 : BitVec.signExtend 64 (8 : BitVec 32) = BitVec.ofNat 64 8 := by decide
  have e1 : BitVec.ofNat 64 k + 1#64 = BitVec.ofNat 64 (k + 1) := BitVec.ofNat_add_ofNat k 1
  have hs : BitVec.ofNat 64 (m - 8 * k) - BitVec.ofNat 64 8 = BitVec.ofNat 64 (m - 8 * (k + 1)) := by
    rw [ofNat_sub (by omega_arith) (by omega_arith), show m - 8 * k - 8 = m - 8 * (k + 1) by omega_arith]
  refine ⟨_, by orun [h13, h12], ?_, ?_, ?_, fun r h1 h2 => ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, reduceCtorEq, ite_false, h13, e1]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, reduceCtorEq, ite_false, h12, e8, hs]
  · simp only [cf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, reduceCtorEq, ite_false, h12, e8, hs]
    rw [toNat_ofNat_of_lt (by omega_arith), toNat_ofNat_of_lt (by decide)]
  · simp only [gpr_setReg, gpr_arithFlags, h1, h2, ite_false]
  all_goals rfl

/-- The pass's start: `r13 ← 0`, and CF set if fewer than eight blocks. -/
theorem passStart_ok (t : State) {m : Nat} (h12 : t.gpr .r12 = BitVec.ofNat 64 m) (hm : m < 2 ^ 64) :
    ∃ t', runBlock isa [.mov .r13 (.imm 0), .alu .cmp .r12 (.imm 8)] t = some t' ∧
      t'.gpr .r13 = BitVec.ofNat 64 0 ∧ t'.cf = some (decide (m < 8)) ∧
      (∀ r, r ≠ .r13 → t'.gpr r = t.gpr r) ∧ t'.mem = t.mem ∧ t'.xmm = t.xmm ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have e8 : BitVec.signExtend 64 (8 : BitVec 32) = BitVec.ofNat 64 8 := by decide
  refine ⟨_, by orun [h12], ?_, ?_, fun r h1 => ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, ite_true]; rfl
  · simp only [cf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, reduceCtorEq, ite_false, h12, e8]
    rw [toNat_ofNat_of_lt hm, toNat_ofNat_of_lt (by decide)]
  · simp only [gpr_setReg, gpr_arithFlags, h1, ite_false]
  all_goals rfl

theorem xorB_add (f : Nat → Block) (a b : Nat) : xorB f (a + b) = xorB f a ^^^ xorB (fun i => f (a + i)) b := by
  induction b with
  | zero => simp [xorB]
  | succ b ih => rw [← Nat.add_assoc, xorB, ih, xorB, BitVec.xor_assoc]

/-- The blocks `C[1]` … `C[8]` of group `k`, from 0. -/
def cOf (l : Block) (k : Nat) (t : Nat) : Block :=
  if t < 7 then cAt l (t + 1) else lAt l 2 ^^^ lAt l (3 + ntz (k + 1))

/-- The offset of block `t` of group `k`. -/
theorem offAt_cOf (o0 l : Block) (k t : Nat) (ht : t < 8) :
    offAt o0 l (8 * k) ^^^ cOf l k t = offAt o0 l (8 * k + t + 1) := by
  unfold cOf
  by_cases h : t < 7
  · simp only [h, ↓reduceIte]
    rw [Nat.add_assoc, offAt_group o0 l k (t + 1) (by omega_arith) (by omega_arith)]
  · simp only [h, ↓reduceIte]
    rw [show 8 * k + t + 1 = 8 * (k + 1) by omega_arith, offAt_eighth]

theorem at'_add (B : Addr) (a b : Nat) : at' (B + BitVec.ofNat 64 a) b = at' B (a + b) :=
  Offset.add_add B a b

/-! ## The pass -/

/-- What a pass needs, from its start `s₀`: `m` blocks at `B`, `W` of `wn`
bytes, the key schedule, `C[1]` … `C[7]`, `L_2` and `L_3`. -/
structure PCtx (md : Mode) (s₀ : State) (B W : Addr) (wn nr : Nat) (w : List Byte) (l : Block) (m : Nat) :
    Prop where
  nrOk : nr = 10 ∨ nr = 12 ∨ nr = 14
  keys : Keys nr w s₀
  rsi : s₀.gpr .rsi = BitVec.ofNat 64 nr
  r10 : s₀.gpr .r10 = s₀.gpr .rdi + BitVec.ofNat 64 (16 * nr)
  imc : md = .open → ImcAt nr w W s₀.mem
  r15 : s₀.gpr .r15 = W
  wnLe : 640 ≤ wn
  wno : md = .open → imcO + 224 ≤ wn
  w64 : wn < 2 ^ 64
  m64 : 16 * m < 2 ^ 64
  D : Covers [⟨B, 16 * m⟩] (s₀.rd ++ s₀.wr)
  Dw : md ≠ .hash → Covers [⟨B, 16 * m⟩] s₀.wr
  wcov : Covers [⟨W, wn⟩] s₀.wr
  DW : Region.Disjoint ⟨B, 16 * m⟩ ⟨W, wn⟩
  KW : Region.Disjoint ⟨s₀.gpr .rdi, 240⟩ ⟨W, wn⟩
  KD : md ≠ .hash → Region.Disjoint ⟨s₀.gpr .rdi, 240⟩ ⟨B, 16 * m⟩
  C : ∀ t, 1 ≤ t → t ≤ 7 → blockAtMem s₀.mem (at' W (cSlot t)) = cAt l t
  L2 : blockAtMem s₀.mem (at' W l2O) = lAt l 2
  L3 : blockAtMem s₀.mem (at' W l3O) = lAt l 3

/-- What the pass writes, after `k` groups: the offsets, `C[8]`, `L_j` and
the data's first `8 k` blocks. -/
abbrev passR (md : Mode) (W B : Addr) (k : Nat) : List Region :=
  [⟨at' W ofO, 128⟩, ⟨at' W c8O, 16⟩, ⟨at' W ljO, 16⟩] ++ (if md = .hash then [] else [⟨B, 16 * (8 * k)⟩])

/-- The output block `i` of a pass: block `i` of the data at `s₀`, offset
`Offset_{i + 1}` from `o0`. -/
abbrev outB (md : Mode) (s₀ : State) (B : Addr) (nr : Nat) (w : List Byte) (l o0 : Block) (i : Nat) : Block :=
  offAt o0 l (i + 1) ^^^ bF md nr w (blockAtMem s₀.mem (at' B (16 * i)) ^^^ offAt o0 l (i + 1))

/-- What block `i` adds to `xmm10`. -/
abbrev termB (md : Mode) (s₀ : State) (B : Addr) (nr : Nat) (w : List Byte) (l o0 : Block) (i : Nat) : Block :=
  term md (bF md nr w) (blockAtMem s₀.mem (at' B (16 * i))) (offAt o0 l (i + 1))

/-- After `k` groups of eight. -/
structure PInv (md : Mode) (s₀ : State) (B W : Addr) (nr : Nat) (w : List Byte) (l o0 : Block) (m k : Nat)
    (t : State) : Prop where
  le : 8 * k ≤ m
  r13 : t.gpr .r13 = BitVec.ofNat 64 k
  r12 : t.gpr .r12 = BitVec.ofNat 64 (m - 8 * k)
  r11 : t.gpr .r11 = B + BitVec.ofNat 64 (16 * (8 * k))
  gpr : ∀ x, x ∉ [Reg.rax, .rdx, .rcx, .r8, .r9, .r11, .r12, .r13] → t.gpr x = s₀.gpr x
  x12 : rv (t.xmm .xmm12) = offAt o0 l (8 * k)
  x10 : rv (t.xmm .xmm10) = rv (s₀.xmm .xmm10) ^^^ xorB (termB md s₀ B nr w l o0) (8 * k)
  out : md ≠ .hash → ∀ i < 8 * k, blockAtMem t.mem (at' B (16 * i)) = outB md s₀ B nr w l o0 i
  fr : Frame (passR md W B k) s₀.mem t.mem
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  xmm : ∀ x, x ∉ regs8 → x ≠ .xmm8 → x ≠ .xmm10 → x ≠ .xmm11 → x ≠ .xmm12 → x ≠ .xmm13 → t.xmm x = s₀.xmm x

section
variable {md : Mode} {s₀ : State} {B W : Addr} {wn nr : Nat} {w : List Byte} {l o0 : Block} {m k : Nat}
  {t : State} (P : PCtx md s₀ B W wn nr w l m) (I : PInv md s₀ B W nr w l o0 m k t)
include P I

omit P I in
/-- A region the pass does not write, at a block of `W` apart from its
offsets, `C[8]` and `L_j`, or elsewhere apart from `W` and the data. -/
theorem PInv.frameDisj {r : Region} (hw' : ∀ q ∈ [(⟨at' W ofO, 128⟩ : Region), ⟨at' W c8O, 16⟩, ⟨at' W ljO, 16⟩],
      r.Disjoint q) (hd : md ≠ .hash → r.Disjoint ⟨B, 16 * (8 * k)⟩) :
    ∀ q ∈ passR md W B k, r.Disjoint q := by
  intro q hq
  simp only [passR, List.mem_append] at hq
  rcases hq with hq | hq
  · exact hw' q hq
  · by_cases hm : md = .hash
    · simp [hm] at hq
    · simp only [hm, ↓reduceIte, List.mem_singleton] at hq; subst hq; exact hd hm

/-- A block of `W` the pass does not write, at `[d, d + 16)`, is as at the start. -/
theorem PInv.wblk {d : Nat} (hd : d + 16 ≤ ofO) (hd' : d + 16 ≤ c8O ∨ c8O + 16 ≤ d)
    (hd'' : d + 16 ≤ ljO ∨ ljO + 16 ≤ d) :
    blockAtMem t.mem (at' W d) = blockAtMem s₀.mem (at' W d) := by
  have hw := P.w64
  have hwn := P.wnLe
  have e1 : ofO = 512 := rfl
  have e2 : c8O = 496 := rfl
  have e3 : ljO = 336 := rfl
  refine Proof.Ocb.blockAtMem_frame I.fr (PInv.frameDisj (fun q hq => ?_) fun _ => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact Offset.disjoint W (.inl hd) (by omega_arith) (by omega_arith)
    · exact Offset.disjoint W (hd'.imp id id) (by omega_arith) (by omega_arith)
    · exact Offset.disjoint W (hd''.imp id id) (by omega_arith) (by omega_arith)
  · exact (P.DW.symm.sub_left (Offset.sub_base W (by omega_arith))).sub_right
      (Region.sub_prefix (by have := I.le; omega_arith))

theorem PInv.c (t' : Nat) (h1 : 1 ≤ t') (h7 : t' ≤ 7) : blockAtMem t.mem (at' W (cSlot t')) = cAt l t' := by
  rw [I.wblk P (by simp only [cSlot, cO, ofO]; omega_arith) (by simp only [cSlot, c8O, cO]; omega_arith)
    (by simp only [cSlot, ljO, cO]; omega_arith), P.C t' h1 h7]

theorem PInv.l2 : blockAtMem t.mem (at' W l2O) = lAt l 2 := by
  rw [I.wblk P (by decide) (by decide) (by decide), P.L2]

theorem PInv.l3 : blockAtMem t.mem (at' W l3O) = lAt l 3 := by
  rw [I.wblk P (by decide) (by decide) (by decide), P.L3]

/-- The data's blocks from `8 k` on are as at the start. -/
theorem PInv.dblk {i : Nat} (hi : 8 * k ≤ i) (hi' : i < m) :
    blockAtMem t.mem (at' B (16 * i)) = blockAtMem s₀.mem (at' B (16 * i)) := by
  have hw := P.w64
  have hm := P.m64
  have hwn := P.wnLe
  have e1 : ofO = 512 := rfl
  have e2 : c8O = 496 := rfl
  have e3 : ljO = 336 := rfl
  have dW : (⟨at' B (16 * i), 16⟩ : Region).Disjoint ⟨W, wn⟩ :=
    P.DW.sub_left (Offset.sub_base B (by omega_arith))
  refine Proof.Ocb.blockAtMem_frame I.fr (PInv.frameDisj (fun q hq => ?_) fun _ => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact dW.sub_right (Offset.sub_base W (by omega_arith))
    · exact dW.sub_right (Offset.sub_base W (by omega_arith))
    · exact dW.sub_right (Offset.sub_base W (by omega_arith))
  · exact Offset.disjoint_base B (by omega_arith) (by omega_arith)

theorem PInv.keys : Keys nr w t := by
  have hw := P.w64
  have hm := P.m64
  have hwn := P.wnLe
  have e1 : ofO = 512 := rfl
  have e2 : c8O = 496 := rfl
  have e3 : ljO = 336 := rfl
  refine keys_of_frame P.keys (by rw [I.gpr _ (by decide)]) I.rd I.wr I.fr (PInv.frameDisj (fun q hq => ?_)
    fun hmd => (P.KD hmd).sub_right (Region.sub_prefix (by have := I.le; omega_arith)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  all_goals exact P.KW.sub_right (Offset.sub_base W (by omega_arith))


theorem PInv.imc (ho : md = .open) : ImcAt nr w W t.mem := by
  have hw := P.w64
  have hwo := P.wno ho
  have hwn := P.wnLe
  have e1 : ofO = 512 := rfl
  have e2 : c8O = 496 := rfl
  have e3 : ljO = 336 := rfl
  have e4 : imcO = 624 := rfl
  intro j h1 h2
  have hle := P.keys.le
  have hj : j ≤ 13 := by rcases P.nrOk with h | h | h <;> omega_arith
  rw [I.fr.readW (r := ⟨at' W (imcO + 16 * j), 16⟩) (Region.contains_self _ _) (PInv.frameDisj (fun q hq => ?_)
    fun _ => (P.DW.symm.sub_left (Offset.sub_base W (by omega_arith))).sub_right
      (Region.sub_prefix (by have := I.le; omega_arith))) (by decide)]
  · exact P.imc ho j h1 h2
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    all_goals exact Offset.disjoint W (.inr (by omega_arith)) (by omega_arith) (by omega_arith)

/-- A group of eight, `k`, with `C[8]` set for it, and the counters. -/
theorem PInv.step (hk : 8 * (k + 1) ≤ m) :
    WP isa (.seq c8 (.seq (group md 8) (.block [addi .r13 1, .alu .sub .r12 (.imm 8), .alu .cmp .r12 (.imm 8)])))
      t fun t' => PInv md s₀ B W nr w l o0 m (k + 1) t' ∧ t'.cf = some (decide (m - 8 * (k + 1) < 8)) := by
  have hw := P.w64
  have hm := P.m64
  have hwn := P.wnLe
  have e1 : ofO = 512 := rfl
  have e2 : c8O = 496 := rfl
  have e3 : ljO = 336 := rfl
  have e4 : imcO = 624 := rfl
  have hle := I.le
  have h15 : t.gpr .r15 = W := by rw [I.gpr _ (by decide), P.r15]
  have hWt : Covers [⟨W, wn⟩] t.wr := by rw [I.wr]; exact P.wcov
  -- `C[8]`.
  refine WP.seq (WP.mono (c8_ok t (W := W) (l := l) (k := k) h15 I.r13 (by omega_arith) hWt hwn hw (I.l2 P)
    (I.l3 P)) fun t₁ ⟨c8v, fr₁, g₁, rd₁, wr₁, x₁⟩ => ?_)
  have fr₁W : ∀ {r : Region}, r.Disjoint ⟨at' W ljO, 16⟩ → r.Disjoint ⟨at' W c8O, 16⟩ →
      ∀ q ∈ [(⟨at' W ljO, 16⟩ : Region), ⟨at' W c8O, 16⟩], r.Disjoint q := fun h1 h2 q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; rcases hq with rfl | rfl; exacts [h1, h2]
  have g₁' : ∀ x, x ∉ [Reg.rax, .rdx, .rcx, .r8, .r9, .r11, .r12, .r13] → t₁.gpr x = s₀.gpr x := fun x hx => by
    refine (g₁ x fun h => hx ?_).trans (I.gpr x hx)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
    rcases h with h | h | h | h | h <;> simp [h]
  have rdi₀ : t.gpr .rdi = s₀.gpr .rdi := I.gpr _ (by decide)
  have dLJ : ∀ {d : Nat}, d + 16 ≤ ljO ∨ ljO + 16 ≤ d → d + 16 ≤ wn →
      (⟨at' W d, 16⟩ : Region).Disjoint ⟨at' W ljO, 16⟩ := fun h hd =>
    Offset.disjoint W h (by omega_arith) (by omega_arith)
  have dC8 : ∀ {d : Nat}, d + 16 ≤ c8O ∨ c8O + 16 ≤ d → d + 16 ≤ wn →
      (⟨at' W d, 16⟩ : Region).Disjoint ⟨at' W c8O, 16⟩ := fun h hd =>
    Offset.disjoint W h (by omega_arith) (by omega_arith)
  have keys₁ : Keys nr w t₁ := keys_of_frame (I.keys P) (by rw [g₁ _ (by decide)]) rd₁ wr₁ fr₁ (fr₁W
    (by rw [rdi₀]; exact P.KW.sub_right (Offset.sub_base W (by omega_arith)))
    (by rw [rdi₀]; exact P.KW.sub_right (Offset.sub_base W (by omega_arith))))
  have rdi₁ : t₁.gpr .rdi = s₀.gpr .rdi := g₁' _ (by decide)
  have imc₁ : md = .open → ImcAt nr w W t₁.mem := fun ho j h1 h2 => by
    have hj : j ≤ 13 := by have := P.keys.le; rcases P.nrOk with h | h | h <;> omega_arith
    have hwo := P.wno ho
    rw [fr₁.readW (r := ⟨at' W (imcO + 16 * j), 16⟩) (Region.contains_self _ _)
      (fr₁W (dLJ (by omega_arith) (by omega_arith)) (dC8 (by omega_arith) (by omega_arith))) (by decide)]
    exact I.imc P ho j h1 h2
  have hc₁ : ∀ k' < 8, blockAtMem t₁.mem (at' W (cO + 16 * k')) = cOf l k k' := fun k' hk' => by
    unfold cOf
    by_cases h7 : k' < 7
    · simp only [h7, ↓reduceIte]
      rw [Proof.Ocb.blockAtMem_frame fr₁ (fr₁W (dLJ (by simp only [cO] at *; omega_arith) (by simp only [cO]; omega_arith))
        (dC8 (by simp only [cO] at *; omega_arith) (by simp only [cO]; omega_arith)))]
      have := I.c P (k' + 1) (by omega_arith) (by omega_arith)
      simpa [cSlot] using this
    · simp only [h7, ↓reduceIte]
      rw [show cO + 16 * k' = c8O by simp only [c8O]; omega_arith]
      exact c8v
  have B'eq : t₁.gpr .r11 = B + BitVec.ofNat 64 (16 * (8 * k)) := by rw [g₁ _ (by decide), I.r11]
  have sub8 : 16 * (8 * k) + 16 * 8 ≤ 16 * m := by omega_arith
  refine WP.seq (WP.mono (group_okB md 8 (by decide) (Nat.le_refl 8) t₁ (B := B + BitVec.ofNat 64 (16 * (8 * k)))
    (W := W) (wn := wn) (o := offAt o0 l (8 * k)) (c := cOf l k) P.nrOk keys₁
    (by rw [g₁' _ (by decide), P.rsi]) (by rw [g₁' _ (by decide), g₁' _ (by decide), P.r10]) imc₁ B'eq
    (by rw [g₁' _ (by decide), P.r15]) (by omega_arith) P.wno hw
    (by rw [rd₁, wr₁, I.rd, I.wr]; exact covers_off P.D sub8 hm)
    (fun hmd => by rw [wr₁, I.wr]; exact covers_off (P.Dw hmd) sub8 hm)
    (by rw [wr₁, I.wr]; exact P.wcov) (P.DW.sub_left (Offset.sub_base B sub8))
    (by rw [rdi₁]; exact P.KW) (fun hmd => by rw [rdi₁]; exact (P.KD hmd).sub_right (Offset.sub_base B sub8))
    (by rw [x₁ _ (by decide) (by decide), I.x12]) hc₁)
    fun t₂ ⟨out₂, x10₂, x12₂, r11₂, g₂, fr₂, frh₂, rd₂, wr₂, xo₂⟩ => ?_)
  have r13₂ : t₂.gpr .r13 = BitVec.ofNat 64 k := by rw [g₂ _ (by decide) (by decide), g₁ _ (by decide), I.r13]
  have r12₂ : t₂.gpr .r12 = BitVec.ofNat 64 (m - 8 * k) := by
    rw [g₂ _ (by decide) (by decide), g₁ _ (by decide), I.r12]
  obtain ⟨t₃, run₃, r13₃, r12₃, cf₃, g₃, m₃, x₃, rd₃, wr₃⟩ := cnt_ok t₂ r13₂ r12₂ hk (by omega_arith)
  refine WP.of_runBlock ⟨t₃, run₃, ?_, cf₃⟩
  have hB : ∀ k', at' (B + BitVec.ofNat 64 (16 * (8 * k))) (16 * k') = at' B (16 * (8 * k + k')) := fun k' => by
    rw [at'_add, show 16 * (8 * k) + 16 * k' = 16 * (8 * k + k') by omega_arith]
  have hP₁ : ∀ k' < 8, blockAtMem t₁.mem (at' B (16 * (8 * k + k'))) = blockAtMem s₀.mem (at' B (16 * (8 * k + k'))) :=
    fun k' hk' => by
      have dW : (⟨at' B (16 * (8 * k + k')), 16⟩ : Region).Disjoint ⟨W, wn⟩ :=
        P.DW.sub_left (Offset.sub_base B (by omega_arith))
      rw [Proof.Ocb.blockAtMem_frame fr₁ (fr₁W (dW.sub_right (Offset.sub_base W (by omega_arith)))
        (dW.sub_right (Offset.sub_base W (by omega_arith)))), I.dblk P (by omega_arith) (by omega_arith)]
  have e128 : (BitVec.ofNat 32 (16 * 8)).signExtend 64 = BitVec.ofNat 64 128 := by decide
  refine {
    le := by omega_arith
    r13 := r13₃
    r12 := r12₃
    r11 := by
      rw [g₃ _ (by decide) (by decide), r11₂, e128, Offset.add_add,
        show 16 * (8 * k) + 128 = 16 * (8 * (k + 1)) by omega_arith]
    gpr := fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      rw [g₃ x hx.2.2.2.2.2.2.2 hx.2.2.2.2.2.2.1, g₂ x hx.2.2.2.2.2.1 hx.2.2.2.1,
        g₁' x (by simp [hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2.1, hx.2.2.2.2.2.1, hx.2.2.2.2.2.2.1,
          hx.2.2.2.2.2.2.2])]
    x12 := by
      rw [x₃, x12₂, offAt_cOf o0 l k 7 (by decide), show 8 * k + 7 + 1 = 8 * (k + 1) by omega_arith]
    x10 := by
      rw [x₃, x10₂, x₁ _ (by decide) (by decide), I.x10, show 8 * (k + 1) = 8 * k + 8 by omega_arith, xorB_add,
        BitVec.xor_assoc]
      refine congrArg _ (congrArg _ (xorB_congr fun k' hk' => ?_))
      rw [hB, hP₁ k' hk', offAt_cOf o0 l k k' hk']
    out := fun hmd i hi => by
      rw [m₃]
      by_cases hlo : i < 8 * k
      · have dW : (⟨at' B (16 * i), 16⟩ : Region).Disjoint ⟨W, wn⟩ :=
          P.DW.sub_left (Offset.sub_base B (by omega_arith))
        rw [Proof.Ocb.blockAtMem_frame fr₂ (fun q hq => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
            rcases hq with rfl | rfl
            · exact dW.sub_right (Offset.sub_base W (by omega_arith))
            · exact Offset.disjoint B (.inl (by omega_arith)) (by omega_arith) (by omega_arith)),
          Proof.Ocb.blockAtMem_frame fr₁ (fr₁W (dW.sub_right (Offset.sub_base W (by omega_arith)))
            (dW.sub_right (Offset.sub_base W (by omega_arith))))]
        exact I.out hmd i hlo
      · have hk' : i - 8 * k < 8 := by omega_arith
        have e := out₂ hmd (i - 8 * k) hk'
        rw [hB, show 8 * k + (i - 8 * k) = i by omega_arith] at e
        have hp := hP₁ (i - 8 * k) hk'
        rw [show 8 * k + (i - 8 * k) = i by omega_arith] at hp
        rw [e, hp, offAt_cOf o0 l k _ hk', show 8 * k + (i - 8 * k) + 1 = i + 1 by omega_arith]
    fr := by
      rw [m₃]
      have sub : ∀ {rs : List Region}, (∀ r ∈ rs, ∃ r' ∈ passR md W B (k + 1), r.Sub r') →
          ∀ {a b : Mem}, Frame rs a b → Frame (passR md W B (k + 1)) a b := fun h _ _ f => Frame.sub f h
      have inR : ∀ q ∈ [(⟨at' W ofO, 128⟩ : Region), ⟨at' W c8O, 16⟩, ⟨at' W ljO, 16⟩],
          ∃ r' ∈ passR md W B (k + 1), q.Sub r' := fun q hq =>
        ⟨q, List.mem_append_left _ hq, fun _ h => h⟩
      refine Frame.trans (Frame.trans (sub (fun r hr => ?_) I.fr) (sub (fun r hr => ?_) fr₁)) ?_
      · simp only [passR, List.mem_append] at hr
        rcases hr with hr | hr
        · exact inR r hr
        · by_cases hmd : md = .hash
          · simp [hmd] at hr
          · simp only [hmd, ↓reduceIte, List.mem_singleton] at hr; subst hr
            exact ⟨⟨B, 16 * (8 * (k + 1))⟩, by simp [passR, hmd], Region.sub_prefix (by omega_arith)⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact inR _ (by simp)
        · exact inR _ (by simp)
      · by_cases hmd : md = .hash
        · refine sub (fun r hr => ?_) (frh₂ hmd)
          simp only [List.mem_singleton] at hr; subst hr; exact inR _ (by simp)
        · refine sub (fun r hr => ?_) fr₂
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact inR _ (by simp)
          · exact ⟨⟨B, 16 * (8 * (k + 1))⟩, by simp [passR, hmd], Offset.sub_base B (by omega_arith)⟩
    rd := by rw [rd₃, rd₂, rd₁, I.rd]
    wr := by rw [wr₃, wr₂, wr₁, I.wr]
    xmm := fun x h1 h2 h3 h4 h5 h6 => by rw [x₃, xo₂ x h1 h2 h3 h4 h5, x₁ x h4 h6, I.xmm x h1 h2 h3 h4 h5 h6] }
end

/-! ## The tail -/

/-- `s'` is `s` but for the flags. -/
structure Same (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  xmm : s'.xmm = s.xmm
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem cmpR12_ok (s : State) {r : Nat} (h12 : s.gpr .r12 = BitVec.ofNat 64 r) (hr : r < 8) (c : Nat) (hc : c < 8) :
    ∃ s', runBlock isa [.alu .cmp .r12 (.imm (BitVec.ofNat 32 c))] s = some s' ∧
      s'.zf = some (decide (r = c)) ∧ Same s s' := by
  refine ⟨_, by orun [h12], ?_, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · simp only [zf_arithFlags]
    rw [Offset.ofNat_sub_ofNat_beq (by omega_arith) (by omega_arith)]
  all_goals simp only [gpr_arithFlags, mem_arithFlags, xmm_arithFlags, rd_arithFlags, wr_arithFlags]

/-- The tail's chain: from `t`, a group of `r12`, if `t ≤ r12 ≤ 7`. -/
theorem tailUp_ok {md : Mode} {Q : State → Prop} : ∀ (f t : Nat) (s : State) {r : Nat},
    1 ≤ t → t + f = 7 → t ≤ r → r ≤ 7 → s.gpr .r12 = BitVec.ofNat 64 r →
    (∀ s', Same s s' → WP isa (group md r) s' Q) → WP isa (tailUp md t f) s Q
  | 0, t, s, r, h1, hf, htr, hr7, h12, H => by
    rw [show r = 7 by omega_arith] at H
    exact H s ⟨rfl, rfl, rfl, rfl, rfl⟩
  | f + 1, t, s, r, h1, hf, htr, hr7, h12, H => by
    unfold tailUp
    by_cases ht7 : t ≥ 7
    · simp only [ht7, ↓reduceIte]
      rw [show r = 7 by omega_arith] at H
      exact H s ⟨rfl, rfl, rfl, rfl, rfl⟩
    · simp only [ht7, ↓reduceIte]
      obtain ⟨s₁, run₁, zf₁, S₁⟩ := cmpR12_ok s h12 (by omega_arith) t (by omega_arith)
      refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
      by_cases he : r = t
      · subst he
        exact WP.ite true (by simp [isa, eval, zf₁]) (fun _ => H s₁ S₁) (fun h => absurd h (by decide))
      · refine WP.ite false (by simp [isa, eval, zf₁, he]) (fun h => absurd h (by decide)) fun _ => ?_
        exact tailUp_ok f (t + 1) s₁ (by omega_arith) (by omega_arith) (by omega_arith) hr7
          (by rw [S₁.gpr, h12]) fun s' S' => H s' ⟨by rw [S'.gpr, S₁.gpr], by rw [S'.mem, S₁.mem],
            by rw [S'.xmm, S₁.xmm], by rw [S'.rd, S₁.rd], by rw [S'.wr, S₁.wr]⟩

/-! ## A whole pass -/

/-- What a whole pass writes. -/
abbrev passW (md : Mode) (W B : Addr) (m : Nat) : List Region :=
  [⟨at' W ofO, 128⟩, ⟨at' W c8O, 16⟩, ⟨at' W ljO, 16⟩] ++ (if md = .hash then [] else [⟨B, 16 * m⟩])

/-- What a pass leaves. -/
structure PPost (md : Mode) (s₀ : State) (B W : Addr) (nr : Nat) (w : List Byte) (l o0 : Block) (m : Nat)
    (s' : State) : Prop where
  out : md ≠ .hash → ∀ i < m, blockAtMem s'.mem (at' B (16 * i)) = outB md s₀ B nr w l o0 i
  x10 : rv (s'.xmm .xmm10) = rv (s₀.xmm .xmm10) ^^^ xorB (termB md s₀ B nr w l o0) m
  x12 : rv (s'.xmm .xmm12) = offAt o0 l m
  r11 : s'.gpr .r11 = B + BitVec.ofNat 64 (16 * m)
  gpr : ∀ x, x ∉ [Reg.rax, .rdx, .rcx, .r8, .r9, .r11, .r12, .r13] → s'.gpr x = s₀.gpr x
  fr : Frame (passW md W B m) s₀.mem s'.mem
  rd : s'.rd = s₀.rd
  wr : s'.wr = s₀.wr
  xmm : ∀ x, x ∉ regs8 → x ≠ .xmm8 → x ≠ .xmm10 → x ≠ .xmm11 → x ≠ .xmm12 → x ≠ .xmm13 → s'.xmm x = s₀.xmm x

/-- The pass when no blocks are left after its groups. -/
theorem PInv.done {md : Mode} {s₀ : State} {B W : Addr} {nr : Nat} {w : List Byte} {l o0 : Block} {m k : Nat}
    {t : State} (I : PInv md s₀ B W nr w l o0 m k t) (he : 8 * k = m) : PPost md s₀ B W nr w l o0 m t where
  out := fun hmd i hi => I.out hmd i (by omega_arith)
  x10 := by rw [I.x10, he]
  x12 := by rw [I.x12, he]
  r11 := by rw [I.r11, he]
  gpr := I.gpr
  fr := by have := I.fr; simp only [passR, he] at this; exact this
  rd := I.rd
  wr := I.wr
  xmm := I.xmm

/-- The last `m − 8 k` blocks, from 1 to 7, in one group. -/
theorem PInv.tail {md : Mode} {s₀ : State} {B W : Addr} {wn nr : Nat} {w : List Byte} {l o0 : Block} {m k : Nat}
    {t : State} (P : PCtx md s₀ B W wn nr w l m) (I : PInv md s₀ B W nr w l o0 m k t)
    (h0 : 8 * k < m) (h8 : m - 8 * k < 8) {s' : State} (S : Same t s') :
    WP isa (group md (m - 8 * k)) s' (PPost md s₀ B W nr w l o0 m) := by
  have hw := P.w64
  have hm := P.m64
  have hwn := P.wnLe
  have e1 : ofO = 512 := rfl
  have e2 : c8O = 496 := rfl
  have e3 : ljO = 336 := rfl
  have hle := I.le
  have rdi₀ : t.gpr .rdi = s₀.gpr .rdi := I.gpr _ (by decide)
  have g' : ∀ x, x ∉ [Reg.rax, .rdx, .rcx, .r8, .r9, .r11, .r12, .r13] → s'.gpr x = s₀.gpr x := fun x hx => by
    rw [S.gpr, I.gpr x hx]
  have keys' : Keys nr w s' := by
    have K := I.keys P
    exact ⟨by rw [S.mem, S.gpr]; exact K.sched, K.le, by rw [S.rd, S.wr, S.gpr]; exact K.keys⟩
  have sub : 16 * (8 * k) + 16 * (m - 8 * k) ≤ 16 * m := by omega_arith
  have hc : ∀ k' < m - 8 * k, blockAtMem s'.mem (at' W (cO + 16 * k')) = cOf l k k' := fun k' hk' => by
    unfold cOf
    simp only [show k' < 7 by omega_arith, ↓reduceIte]
    rw [S.mem]
    have := I.c P (k' + 1) (by omega_arith) (by omega_arith)
    simpa [cSlot] using this
  have hKD' : md ≠ .hash → Region.Disjoint ⟨s'.gpr .rdi, 240⟩ ⟨B + BitVec.ofNat 64 (16 * (8 * k)), 16 * (m - 8 * k)⟩ :=
    fun hmd => by rw [g' _ (by decide)]; exact (P.KD hmd).sub_right (Offset.sub_base B sub)
  refine WP.mono (group_okB md (m - 8 * k) (by omega_arith) (by omega_arith) s' (B := B + BitVec.ofNat 64 (16 * (8 * k)))
    (W := W) (wn := wn) (o := offAt o0 l (8 * k)) (c := cOf l k) P.nrOk keys'
    (by rw [g' _ (by decide), P.rsi]) (by rw [g' _ (by decide), g' _ (by decide), P.r10])
    (fun ho => by rw [S.mem]; exact I.imc P ho) (by rw [S.gpr, I.r11]) (by rw [g' _ (by decide), P.r15])
    (by omega_arith) P.wno hw
    (by rw [S.rd, S.wr, I.rd, I.wr]; exact covers_off P.D sub hm)
    (fun hmd => by rw [S.wr, I.wr]; exact covers_off (P.Dw hmd) sub hm)
    (by rw [S.wr, I.wr]; exact P.wcov) (P.DW.sub_left (Offset.sub_base B sub))
    (by rw [g' _ (by decide)]; exact P.KW) hKD' (by rw [S.xmm, I.x12]) hc)
    fun s'' ⟨out₂, x10₂, x12₂, r11₂, g₂, fr₂, frh₂, rd₂, wr₂, xo₂⟩ => ?_
  have hB : ∀ k', at' (B + BitVec.ofNat 64 (16 * (8 * k))) (16 * k') = at' B (16 * (8 * k + k')) := fun k' => by
    rw [at'_add, show 16 * (8 * k) + 16 * k' = 16 * (8 * k + k') by omega_arith]
  have hP : ∀ k' < m - 8 * k, blockAtMem s'.mem (at' B (16 * (8 * k + k'))) =
      blockAtMem s₀.mem (at' B (16 * (8 * k + k'))) := fun k' hk' => by
    rw [S.mem, I.dblk P (by omega_arith) (by omega_arith)]
  have eR : (BitVec.ofNat 32 (16 * (m - 8 * k))).signExtend 64 = BitVec.ofNat 64 (16 * (m - 8 * k)) := by
    generalize m - 8 * k = r at h8 h0 ⊢
    have : r < 8 := h8
    revert r; decide
  exact {
    out := fun hmd i hi => by
      by_cases hlo : i < 8 * k
      · have dW : (⟨at' B (16 * i), 16⟩ : Region).Disjoint ⟨W, wn⟩ :=
          P.DW.sub_left (Offset.sub_base B (by omega_arith))
        rw [Proof.Ocb.blockAtMem_frame fr₂ (fun q hq => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
            rcases hq with rfl | rfl
            · exact dW.sub_right (Offset.sub_base W (by omega_arith))
            · exact Offset.disjoint B (.inl (by omega_arith)) (by omega_arith) (by omega_arith)), S.mem]
        exact I.out hmd i hlo
      · have hk' : i - 8 * k < m - 8 * k := by omega_arith
        have e := out₂ hmd (i - 8 * k) hk'
        rw [hB, show 8 * k + (i - 8 * k) = i by omega_arith] at e
        have hp := hP (i - 8 * k) hk'
        rw [show 8 * k + (i - 8 * k) = i by omega_arith] at hp
        rw [e, hp, offAt_cOf o0 l k _ (by omega_arith), show 8 * k + (i - 8 * k) + 1 = i + 1 by omega_arith]
    x10 := by
      have hsplit : xorB (termB md s₀ B nr w l o0) m = xorB (termB md s₀ B nr w l o0) (8 * k) ^^^
          xorB (fun i => termB md s₀ B nr w l o0 (8 * k + i)) (m - 8 * k) := by
        rw [← xorB_add, show 8 * k + (m - 8 * k) = m by omega_arith]
      rw [x10₂, S.xmm, I.x10, hsplit, BitVec.xor_assoc]
      refine congrArg _ (congrArg _ (xorB_congr fun k' hk' => ?_))
      rw [hB, hP k' hk', offAt_cOf o0 l k k' (by omega_arith)]
    x12 := by
      rw [x12₂, offAt_cOf o0 l k _ (by omega_arith), show 8 * k + (m - 8 * k - 1) + 1 = m by omega_arith]
    r11 := by rw [r11₂, eR, Offset.add_add, show 16 * (8 * k) + 16 * (m - 8 * k) = 16 * m by omega_arith]
    gpr := fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      rw [g₂ x hx.2.2.2.2.2.1 hx.2.2.2.1]
      exact g' x (by simp [hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2.1, hx.2.2.2.2.2.1, hx.2.2.2.2.2.2.1,
        hx.2.2.2.2.2.2.2])
    fr := by
      have sub' : ∀ {rs : List Region}, (∀ r ∈ rs, ∃ r' ∈ passW md W B m, r.Sub r') →
          ∀ {a b : Mem}, Frame rs a b → Frame (passW md W B m) a b := fun h _ _ f => Frame.sub f h
      have inR : ∀ q ∈ [(⟨at' W ofO, 128⟩ : Region), ⟨at' W c8O, 16⟩, ⟨at' W ljO, 16⟩],
          ∃ r' ∈ passW md W B m, q.Sub r' := fun q hq => ⟨q, List.mem_append_left _ hq, fun _ h => h⟩
      refine Frame.trans (sub' (fun r hr => ?_) I.fr) ?_
      · simp only [passR, List.mem_append] at hr
        rcases hr with hr | hr
        · exact inR r hr
        · by_cases hmd : md = .hash
          · simp [hmd] at hr
          · simp only [hmd, ↓reduceIte, List.mem_singleton] at hr; subst hr
            exact ⟨⟨B, 16 * m⟩, by simp [passW, hmd], Region.sub_prefix (by omega_arith)⟩
      · rw [← S.mem]
        by_cases hmd : md = .hash
        · refine sub' (fun r hr => ?_) (frh₂ hmd)
          simp only [List.mem_singleton] at hr; subst hr; exact inR _ (by simp)
        · refine sub' (fun r hr => ?_) fr₂
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact inR _ (by simp)
          · exact ⟨⟨B, 16 * m⟩, by simp [passW, hmd], Offset.sub_base B sub⟩
    rd := by rw [rd₂, S.rd, I.rd]
    wr := by rw [wr₂, S.wr, I.wr]
    xmm := fun x h1 h2 h3 h4 h5 h6 => by rw [xo₂ x h1 h2 h3 h4 h5, S.xmm, I.xmm x h1 h2 h3 h4 h5 h6] }

theorem eval_ae {s : State} {b : Bool} (h : s.cf = some b) : isa.eval .ae s = some !b := by
  show s.cf.map (!·) = _; rw [h]; rfl

theorem Same.trans {s s' s'' : State} (h : Same s s') (h' : Same s' s'') : Same s s'' :=
  ⟨h'.gpr.trans h.gpr, h'.mem.trans h.mem, h'.xmm.trans h.xmm, h'.rd.trans h.rd, h'.wr.trans h.wr⟩

theorem PInv.same {md : Mode} {s₀ : State} {B W : Addr} {nr : Nat} {w : List Byte} {l o0 : Block} {m k : Nat}
    {t t' : State} (I : PInv md s₀ B W nr w l o0 m k t) (S : Same t t') : PInv md s₀ B W nr w l o0 m k t' where
  le := I.le
  r13 := by rw [S.gpr, I.r13]
  r12 := by rw [S.gpr, I.r12]
  r11 := by rw [S.gpr, I.r11]
  gpr := fun x hx => by rw [S.gpr, I.gpr x hx]
  x12 := by rw [S.xmm, I.x12]
  x10 := by rw [S.xmm, I.x10]
  out := fun hmd i hi => by rw [S.mem, I.out hmd i hi]
  fr := by rw [S.mem]; exact I.fr
  rd := by rw [S.rd, I.rd]
  wr := by rw [S.wr, I.wr]
  xmm := fun x h1 h2 h3 h4 h5 h6 => by rw [S.xmm, I.xmm x h1 h2 h3 h4 h5 h6]

theorem testR12_ok (s : State) {r : Nat} (h12 : s.gpr .r12 = BitVec.ofNat 64 r) (hr : r < 2 ^ 64) :
    ∃ s', runBlock isa [.alu .test .r12 (.reg .r12)] s = some s' ∧ s'.zf = some (decide (r = 0)) ∧ Same s s' := by
  refine ⟨_, by orun [h12], ?_, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · simp only [zf_setFlags, zf_arithFlags, BitVec.and_self]
    by_cases h : r = 0
    · subst h; simp
    · have : BitVec.ofNat 64 r ≠ 0#64 := fun h' => h (by
        have := congrArg BitVec.toNat h'; rwa [toNat_ofNat_of_lt hr] at this)
      simp [h, this]
  all_goals simp only [gpr_arithFlags, mem_arithFlags, xmm_arithFlags, rd_arithFlags, wr_arithFlags,
    gpr_setFlags, mem_setFlags, xmm_setFlags, rd_setFlags, wr_setFlags]

/-- A pass over the `m` blocks at `B` (in `r11` and `r12`), from the offset
`o0` in `xmm12`. -/
theorem pass_ok {md : Mode} {s₀ : State} {B W : Addr} {wn nr : Nat} {w : List Byte} {l o0 : Block} {m : Nat}
    (P : PCtx md s₀ B W wn nr w l m) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 m) (h11 : s₀.gpr .r11 = B)
    (ho : rv (s₀.xmm .xmm12) = o0) :
    WP isa (pass md) s₀ (PPost md s₀ B W nr w l o0 m) := by
  have hm64 : m < 2 ^ 64 := by have := P.m64; omega_arith
  unfold pass
  obtain ⟨t₀, run₀, r13₀, cf₀, g₀, m₀, x₀, rd₀, wr₀⟩ := passStart_ok s₀ h12 hm64
  refine WP.seq (WP.of_runBlock ⟨t₀, run₀, ?_⟩)
  have I0 : PInv md s₀ B W nr w l o0 m 0 t₀ := {
    le := by omega_arith
    r13 := r13₀
    r12 := by rw [g₀ _ (by decide), h12, Nat.mul_zero, Nat.sub_zero]
    r11 := by rw [g₀ _ (by decide), h11]; simp
    gpr := fun x hx => g₀ x fun h => hx (by simp [h])
    x12 := by rw [x₀, ho]; rfl
    x10 := by rw [x₀]; simp [xorB]
    out := fun _ i hi => absurd hi (by omega_arith)
    fr := by rw [m₀]; exact Frame.refl _ _
    rd := rd₀
    wr := wr₀
    xmm := fun x _ _ _ _ _ _ => by rw [x₀] }
  have loopPart : WP isa (.ite .b (.block [])
      (.loop (.seq c8 (.seq (group md 8) (.block [addi .r13 1, .alu .sub .r12 (.imm 8), .alu .cmp .r12 (.imm 8)])))
        .ae)) t₀ fun t => ∃ k, PInv md s₀ B W nr w l o0 m k t ∧ m - 8 * k < 8 := by
    by_cases hlt : m < 8
    · exact WP.ite true (by rw [eval_b cf₀]; simp [hlt]) (fun _ => WP.block_nil ⟨0, I0, by omega_arith⟩)
        (fun h => absurd h (by decide))
    · refine WP.ite false (by rw [eval_b cf₀]; simp [hlt]) (fun h => absurd h (by decide)) fun _ => ?_
      refine WP.loop (M := isa) (c := .ae)
        (fun (n : Nat) (t : State) => ∃ k, n = m / 8 - k ∧ PInv md s₀ B W nr w l o0 m k t ∧ 8 * (k + 1) ≤ m)
        ?_ (m / 8 - 0) t₀ ⟨0, rfl, I0, by omega_arith⟩
      rintro n t ⟨k, rfl, I, hk⟩
      refine WP.mono (I.step P hk) fun t' ⟨I', cf'⟩ => ?_
      by_cases hlt' : m - 8 * (k + 1) < 8
      · exact .inl ⟨by rw [eval_ae cf']; simp [hlt'], k + 1, I', hlt'⟩
      · exact .inr ⟨by rw [eval_ae cf']; simp [hlt'], m / 8 - (k + 1), by omega_arith, k + 1, rfl, I',
          by omega_arith⟩
  refine WP.seq (WP.mono loopPart fun t ⟨K, I, hK⟩ => ?_)
  unfold tail
  obtain ⟨t₁, run₁, zf₁, S₁⟩ := testR12_ok t I.r12 (by omega_arith)
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  have hKle := I.le
  by_cases hr0 : m - 8 * K = 0
  · exact WP.ite true (by simp [isa, eval, zf₁, hr0]) (fun _ => WP.block_nil ((I.same S₁).done (by omega_arith)))
      (fun h => absurd h (by decide))
  · refine WP.ite false (by simp [isa, eval, zf₁, hr0]) (fun h => absurd h (by decide)) fun _ => ?_
    exact tailUp_ok 6 1 t₁ (by decide) (by decide) (by omega_arith) (by omega_arith) (by rw [S₁.gpr, I.r12])
      fun s' S' => I.tail P (by omega_arith) hK (S₁.trans S')

end VG.Proof.AesOcb.X86_64.AesNi
