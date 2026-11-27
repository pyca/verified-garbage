module

public import VerifiedGarbage.Impl.AesOcb.X86_64
public import VerifiedGarbage.Proof.Cmac.Mem
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Spec.Ocb
import VerifiedGarbage.Proof.AesOcb.X86_64.Run
import VerifiedGarbage.Proof.CmacAes.X86_64.Dbl
import VerifiedGarbage.Proof.Ocb.Spec
import VerifiedGarbage.Proof.AesCcm.X86_64.Env
import VerifiedGarbage.Proof.Gcm.X86_64.Bits
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.AesOcb.X86_64.Callee
public import VerifiedGarbage.Proof.AesOcb.X86_64.Env
import VerifiedGarbage.Proof.AesCcm.X86_64.Run

/-! ### `AesOcb.X86_64.Args`, which the modules that import this one used -/

section

/-!
# AES-OCB on x86-64: the calls of the block functions

Untrusted: everything here is checked by Lean. `callBlocks b args` sets up
a call of `b` (`vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks`) with the
key schedule of the key context, the rounds kept in `W`, the `n` blocks at
`D` that `args` sets (`Dst`: blocks of `W` below 512, `dstW`, or the data,
`dstD`) and the working space at `W + 512` (`callBlocks_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCcm.X86_64 (covers_left covers_cons covers_nil covers_append covers_off runBlock_append)

/-- `n` blocks at `D` for a call: apart from the key context, the working
space at `W + 512` and the stack below `SP`, and readable and writable. -/
structure Dst (K W SP : Addr) (s : State) (D : Addr) (n : Nat) : Prop where
  wrap : D.toNat + 16 * n ≤ 2 ^ 64
  k : (⟨K, 256⟩ : Region).Disjoint ⟨D, 16 * n⟩
  scr : (⟨D, 16 * n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 512, 2048⟩
  stk : (below SP 8).Disjoint ⟨D, 16 * n⟩
  rd : Covers [⟨D, 16 * n⟩] (s.rd ++ s.wr)
  wr : Covers [⟨D, 16 * n⟩] s.wr

theorem covers_prefix {p : Addr} {k n : Nat} {rs : List Region} (h : Covers [⟨p, k⟩] rs) (hn : n ≤ k) :
    Covers [⟨p, n⟩] rs := fun a m ⟨r, hr, hc⟩ => by
  simp only [List.mem_singleton] at hr; subst hr
  exact h a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega_using [hn, hc]⟩

theorem toNat_W {W : Addr} (hw : W.toNat + 3584 ≤ 2 ^ 64) {d : Nat} (hd : d < 3584) :
    (W + BitVec.ofNat 64 d).toNat = W.toNat + d := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega_using [hd]), Nat.mod_eq_of_lt (by omega_using [hw, hd])]

/-- Blocks of `W` below 512. -/
theorem dstW {K W SP : Addr} {s : State} (L : Lay K W SP) (P : Perm K W s) {d n : Nat} (h : d + 16 * n ≤ 512) :
    Dst K W SP s (W + BitVec.ofNat 64 d) n where
  wrap := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.mul_zero, Nat.add_zero]; exact Nat.le_of_lt (W + BitVec.ofNat 64 d).isLt
    · rw [toNat_W L.ww (by omega_using [h])]; have := L.ww; omega_using [h, this]
  k := L.k_w.sub_right (Lay.wSub (by omega_using [h]))
  scr := L.w_w (.inl (by omega_using [h])) (by omega_using [h]) (by decide)
  stk := L.stk_w' (by omega_using [h])
  rd := covers_left (P.wC (by omega_using [h]))
  wr := P.wC (by omega_using [h])

/-- Blocks of the data. -/
theorem dstD {K W SP : Addr} {s : State} {D : Addr} {n : Nat} (h : DBuf K W SP s D (16 * n)) :
    Dst K W SP s D n where
  wrap := h.wrap
  k := h.k
  scr := h.w.sub_right (Lay.wSub (by decide))
  stk := h.stk
  rd := h.rd
  wr := h.wr

theorem Dst.of_eq {K W SP : Addr} {s s' : State} {D : Addr} {n : Nat} (h : Dst K W SP s D n)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Dst K W SP s' D n :=
  { h with rd := by rw [hrd, hwr]; exact h.rd, wr := by rw [hwr]; exact h.wr }

/-- What the arguments `args` of a call set: `rdx` and `rcx` (to `D` and `n`),
nothing else but `rax`. -/
def ArgsOk (args : List Instr) (s : State) (D : Addr) (n : Nat) : Prop :=
  ∃ s₁, runBlock isa args s = some s₁ ∧ s₁.gpr .rdx = D ∧ s₁.gpr .rcx = BitVec.ofNat 64 n ∧
    (∀ r, r ≠ .rdx → r ≠ .rcx → r ≠ .rax → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧
    s₁.wr = s.wr

theorem wp_seq_assoc {a b c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa (.seq (.seq a b) c) s Q) :
    WP isa (.seq a (.seq b c)) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp (WP.seq_iff.mp h)) fun _ h => WP.seq h)

theorem sext1 : BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 1 := by decide

theorem sext0 : BitVec.signExtend 64 (0 : BitVec 32) = BitVec.ofNat 64 0 := by decide

/-- One block at `W + d`. -/
theorem oneBlock_ok {W : Addr} {s : State} (h15 : s.gpr .r15 = W) (d : Nat) (hd : d < 2 ^ 31) :
    ArgsOk (oneBlock d) s (W + BitVec.ofNat 64 d) 1 := by
  refine ⟨_, by orun [oneBlock, h15], ?_, ?_, fun r h1 h2 _ => ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, sext1]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, h1, h2]
  all_goals rfl

theorem BPost.congr {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s₀ s s' : State} {K D S : Addr}
    {R n : Nat} (h : BPost f s K D S R n s') (hm : s.mem = s₀.mem) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hg : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r) (hsp : s.gpr .rsp = s₀.gpr .rsp) :
    BPost f s₀ K D S R n s' where
  rd := by rw [h.rd, hrd]
  wr := by rw [h.wr, hwr]
  saved r hr := by rw [h.saved r hr, hg r hr]
  frame := by rw [← hm, ← hsp]; exact h.frame
  out := by rw [← hm]; exact h.out

/-- A call of `b`, after `args`. -/
theorem callArgs_ok {K W SP : Addr} (L : Lay K W SP) {s : State} (E : Env K W SP s) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (hrnd : s.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    {args : List Instr} {D : Addr} {n : Nat} (ha : ArgsOk args s D n) (hD : Dst K W SP s D n) :
    WP isa (.block (args ++ [mvr .rdi .r14, ld .rsi .r15 rndO, mvr .r8 .r15, addi .r8 scrO])) s fun s₂ =>
      BCall s₂ K D (W + BitVec.ofNat 64 512) R n ∧ s₂.gpr .rsp = SP ∧ s₂.mem = s.mem ∧ s₂.rd = s.rd ∧
        s₂.wr = s.wr ∧ ∀ r ∈ calleeSaved, s₂.gpr r = s.gpr r := by
  obtain ⟨s₁, run₁, rdx₁, rcx₁, g₁, m₁, rd₁, wr₁⟩ := ha
  have r₁ : InRegions (s₁.rd ++ s₁.wr) (W + BitVec.ofNat 64 232) 8 := by
    rw [rd₁, wr₁]; exact E.perm.wR (by decide)
  have h15 : s₁.gpr .r15 = W := by rw [g₁ _ (by decide) (by decide) (by decide), E.r15]
  have h14 : s₁.gpr .r14 = K := by rw [g₁ _ (by decide) (by decide) (by decide), E.r14]
  have hrnd₁ : s₁.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R := by rw [m₁, hrnd]
  obtain ⟨s₂, run₂, rdi₂, rsi₂, rdx₂, rcx₂, r8₂, g₂, m₂, rd₂, wr₂⟩ : ∃ s₂,
      runBlock isa [mvr .rdi .r14, ld .rsi .r15 rndO, mvr .r8 .r15, addi .r8 scrO] s₁ = some s₂ ∧
      s₂.gpr .rdi = K ∧ s₂.gpr .rsi = BitVec.ofNat 64 R ∧ s₂.gpr .rdx = D ∧ s₂.gpr .rcx = BitVec.ofNat 64 n ∧
      s₂.gpr .r8 = W + BitVec.ofNat 64 512 ∧
      (∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .r8 → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧
      s₂.wr = s₁.wr := by
    refine ⟨_, by orun [h14, h15, r₁, hrnd₁], ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h14]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h15, hrnd₁]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, rdx₁]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, rcx₁]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h15]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, h1, h2, h3]
    all_goals rfl
  have hs : s₂.gpr .rsp = SP := by
    rw [g₂ _ (by decide) (by decide) (by decide), g₁ _ (by decide) (by decide) (by decide), E.rsp]
  have hD₂ := hD.of_eq (s' := s₂) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])
  have hc : BCall s₂ K D (W + BitVec.ofNat 64 512) R n :=
    { rdi := rdi₂, rsi := rsi₂, rdx := rdx₂, rcx := rcx₂, r8 := r8₂, rounds := hR, wrap := hD.wrap
      kd := hD.k.sub_left (Region.sub_prefix (by decide))
      ks := (L.k_w.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide))
      ds := hD.scr
      stkK := by rw [hs]; exact L.stk_k.sub_right (Region.sub_prefix (by decide))
      stkD := by rw [hs]; exact hD.stk
      stkS := by rw [hs]; exact L.stk_w' (by decide)
      reads := covers_append (covers_cons (covers_prefix (by rw [rd₂, rd₁, wr₂, wr₁]; exact E.perm.k)
          (by decide)) covers_nil)
        (covers_cons hD₂.rd (covers_cons (covers_left (by rw [wr₂, wr₁]; exact E.perm.wC (by decide))) covers_nil))
      writes := covers_cons hD₂.wr (covers_cons (by rw [wr₂, wr₁]; exact E.perm.wC (by decide)) covers_nil) }
  refine WP.of_runBlock ⟨s₂, by rw [runBlock_append, run₁, Option.bind_some, run₂], hc, hs, by rw [m₂, m₁],
    by rw [rd₂, rd₁], by rw [wr₂, wr₁], fun r hr => ?_⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [g₂ _ (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
    g₁ _ (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]

theorem callBlocks_ok {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {b : Impl.Aes.X86_64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksX86_64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86_64 f).post s s')
    (nosp : NoSp b.code) (depth : b.code.depth = 0)
    {K W SP : Addr} (L : Lay K W SP) {s : State} (E : Env K W SP s) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (hrnd : s.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    {args : List Instr} {D : Addr} {n : Nat} (ha : ArgsOk args s D n) (hD : Dst K W SP s D n) :
    WP isa (callBlocks b args) s (BPost f s K D (W + BitVec.ofNat 64 512) R n) := by
  exact WP.seq (WP.mono (callArgs_ok L E hR hrnd ha hD) fun s₂ ⟨hc, hs, m₂, rd₂, wr₂, g₂⟩ =>
    WP.mono (blk_call ok nosp depth hc) fun s' h => h.congr m₂ rd₂ wr₂ g₂ (by rw [hs, E.rsp]))

end VG.Proof.AesOcb.X86_64

end

end

/-!
# AES-OCB on x86-64: blocks of `W`, two words at a time

Untrusted: everything here is checked by Lean. `zero16`, `copy16`, `xor16`
and `dbl` write a block of `W` (`BlkStep`; `dbl`, at any address in a
register): zeros, a copy, the XOR with a block and `double` of a block
(`zero16_ok`, `copy16_ok`, `xor16_ok`, `dbl_ok`), as blocks of memory
(`blockAtMem`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64
open VG.Spec.Ocb (Block blockAtMem double)
open VG.Proof.Cmac (le8 le8_readW xor_words bytesAt_store2)
open VG.Proof.AesCcm.X86_64 (in_left)

/-- What a step writing the block at `W + d` does: it writes only there,
the block `v`, and keeps the registers but `clob`. -/
structure BlkStep (W : Addr) (d : Nat) (v : Block) (clob : List Reg) (s s' : State) : Prop where
  frame : Frame [⟨W + BitVec.ofNat 64 d, 16⟩] s.mem s'.mem
  val : blockAtMem s'.mem (W + BitVec.ofNat 64 d) = v
  gpr : ∀ r, r ∉ clob → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem frame_store2 (m : Mem) (p : Addr) (w₀ w₁ : BitVec 64) :
    Frame [⟨p, 16⟩] m ((m.writeW p w₀).writeW (p + BitVec.ofNat 64 8) w₁) :=
  ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (by simpa using Offset.contains p (d := 0) (n := 8) (e := 0) (k := 16) (by decide) (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _
    (by simpa using Offset.contains p (d := 8) (n := 8) (e := 0) (k := 16) (by decide) (by decide) (by decide))

theorem blockAtMem_store2 (m : Mem) (p : Addr) (w₀ w₁ : BitVec 64) :
    blockAtMem ((m.writeW p w₀).writeW (p + BitVec.ofNat 64 8) w₁) p = Spec.Ocb.ofBytes (le8 w₀ ++ le8 w₁) := by
  rw [blockAtMem, bytesAt_store2]

/-- The two words of a block, XORed with those of another, are the XOR of
the blocks. -/
theorem blockAtMem_xor_words (m : Mem) (p q : Addr) :
    Spec.Ocb.ofBytes (le8 (m.readW p 64 ^^^ m.readW q 64) ++
      le8 (m.readW (p + BitVec.ofNat 64 8) 64 ^^^ m.readW (q + BitVec.ofNat 64 8) 64)) =
      blockAtMem m p ^^^ blockAtMem m q := by
  rw [xor_words, ← Proof.Ocb.xor_eq, Proof.Ocb.ofBytes_xor (by simp [Spec.Aes.bytesAt])
    (by simp [Spec.Aes.bytesAt])]
  rfl

theorem blockAtMem_words (m : Mem) (p : Addr) :
    Spec.Ocb.ofBytes (le8 (m.readW p 64) ++ le8 (m.readW (p + BitVec.ofNat 64 8) 64)) = blockAtMem m p := by
  rw [le8_readW, le8_readW, ← Proof.Cmac.bytesAt_split]; rfl

theorem addr8 (p : Addr) (d : Nat) : p + BitVec.ofNat 64 d + BitVec.ofNat 64 8 = p + BitVec.ofNat 64 (d + 8) :=
  Offset.add_add p d 8

/-- `zero16 d`: `W + d ← 0`. -/
theorem zero16_ok {W : Addr} {s : State} {d : Nat} (h15 : s.gpr .r15 = W)
    (w₀ : InRegions s.wr (W + BitVec.ofNat 64 d) 8) (w₁ : InRegions s.wr (W + BitVec.ofNat 64 (d + 8)) 8) :
    ∃ s', runBlock isa (zero16 d) s = some s' ∧ BlkStep W d 0 [.rax] s s' := by
  refine ⟨_, by orun [zero16, h15, w₀, w₁], ?_⟩
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl⟩
  · simp only [mem_setReg, mem_arithFlags, BitVec.xor_self]; rw [← addr8 W d]; exact frame_store2 _ _ _ _
  · simp only [mem_setReg, mem_arithFlags, BitVec.xor_self]; rw [← addr8 W d, blockAtMem_store2]; decide
  · simp only [List.mem_singleton] at hr
    simp only [gpr_setReg, gpr_arithFlags, hr, ite_false]

/-- `copy16 a d`: `W + d ← W + a`. -/
theorem copy16_ok {W : Addr} {s : State} {a d : Nat} (h15 : s.gpr .r15 = W)
    (r₀ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 a) 8)
    (r₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 (a + 8)) 8)
    (w₀ : InRegions s.wr (W + BitVec.ofNat 64 d) 8) (w₁ : InRegions s.wr (W + BitVec.ofNat 64 (d + 8)) 8) :
    ∃ s', runBlock isa (copy16 a d) s = some s' ∧
      BlkStep W d (blockAtMem s.mem (W + BitVec.ofNat 64 a)) [.rax, .rdx] s s' := by
  refine ⟨_, by orun [copy16, h15, r₀, r₁, w₀, w₁], ?_⟩
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl⟩
  · simp only [mem_setReg]; rw [← addr8 W d]; exact frame_store2 _ _ _ _
  · simp only [mem_setReg]; rw [← addr8 W d, blockAtMem_store2, ← addr8 W a, blockAtMem_words]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, hr.1, hr.2, ite_false]

/-- `xor16 b a d`: `W + d ← W + d ⊕ (B + a)`, `B` in `b`. -/
theorem xor16_ok {W B : Addr} {s : State} {b : Reg} {a d : Nat} (h15 : s.gpr .r15 = W) (hb : s.gpr b = B)
    (hba : b ≠ .rax) (hbd : b ≠ .rdx)
    (r₀ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 a) 8)
    (r₁ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (a + 8)) 8)
    (w₀ : InRegions s.wr (W + BitVec.ofNat 64 d) 8) (w₁ : InRegions s.wr (W + BitVec.ofNat 64 (d + 8)) 8) :
    ∃ s', runBlock isa (xor16 b a d) s = some s' ∧
      BlkStep W d (blockAtMem s.mem (W + BitVec.ofNat 64 d) ^^^ blockAtMem s.mem (B + BitVec.ofNat 64 a))
        [.rax, .rdx] s s' := by
  have v₀ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d) 8 := in_left w₀
  have v₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 (d + 8)) 8 := in_left w₁
  refine ⟨_, by orun [xor16, h15, hb, hba, hbd, r₀, r₁, v₀, v₁, w₀, w₁], ?_⟩
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl⟩
  · simp only [mem_setReg, mem_arithFlags]; rw [← addr8 W d]; exact frame_store2 _ _ _ _
  · simp only [mem_setReg, mem_arithFlags]
    rw [← addr8 W d, blockAtMem_store2, ← addr8 B a, blockAtMem_xor_words]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, gpr_arithFlags, hr.1, hr.2, ite_false]

theorem mask87 : BitVec.signExtend 64 (0x87 : BitVec 32) = BitVec.ofNat 64 135 := by decide

/-- `double` of the block at `p`, from its byte-reversed words. -/
theorem dbl_mem (m : Mem) (p : Addr) :
    let hi := bswap64 (m.readW p 64)
    let lo := bswap64 (m.readW (p + BitVec.ofNat 64 8) 64)
    Spec.Ocb.ofBytes (le8 (bswap64 ((hi + hi) ||| (lo >>> 63))) ++
      le8 (bswap64 ((lo + lo) ^^^ (((0 : BitVec 64) - (hi >>> 63)) &&& BitVec.ofNat 64 135)))) =
      double (blockAtMem m p) := by
  intro hi lo
  rw [Proof.CmacAes.X86_64.le8_bswap, ← Proof.Ocb.toBytes_eq, Proof.Ocb.ofBytes_toBytes, ← mask87,
    Proof.CmacAes.X86_64.dbl_words, Proof.Ocb.double_eq]
  congr 1
  have e0 : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p
  show hi ++ lo = Spec.Gcm.blockAt m p
  rw [← Proof.Gcm.X86_64.blockAt_bswap, e0]

/-- `dbl b a o d`: `O + d ← double(B + a)`, `B` in `b` and `O` in `o`. -/
theorem dbl_ok {W B : Addr} {s : State} {b o : Reg} {a d : Nat} (h15 : s.gpr o = W) (hb : s.gpr b = B)
    (hba : b ≠ .rax) (hoa : o ≠ .rax) (hod : o ≠ .rdx) (hoc : o ≠ .rcx) (ho8 : o ≠ .r8)
    (r₀ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 a) 8)
    (r₁ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (a + 8)) 8)
    (w₀ : InRegions s.wr (W + BitVec.ofNat 64 d) 8) (w₁ : InRegions s.wr (W + BitVec.ofNat 64 (d + 8)) 8) :
    ∃ s', runBlock isa (dbl b a o d) s = some s' ∧
      BlkStep W d (double (blockAtMem s.mem (B + BitVec.ofNat 64 a))) [.rax, .rdx, .rcx, .r8] s s' := by
  refine ⟨_, by orun [dbl, h15, hb, hba, hoa, hod, hoc, ho8, r₀, r₁, w₀, w₁], ?_⟩
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl⟩
  · simp only [mem_setReg, mem_arithFlags, mem_setFlags]; rw [← addr8 W d]; exact frame_store2 _ _ _ _
  · simp only [mem_setReg, mem_arithFlags, mem_setFlags, BitVec.xor_self]
    rw [← addr8 W d, blockAtMem_store2, ← addr8 B a]
    exact dbl_mem _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

/-- `dbl_ok`, and the SSE registers are kept. -/
theorem dbl_okX {W B : Addr} {s : State} {b o : Reg} {a d : Nat} (h15 : s.gpr o = W) (hb : s.gpr b = B)
    (hba : b ≠ .rax) (hoa : o ≠ .rax) (hod : o ≠ .rdx) (hoc : o ≠ .rcx) (ho8 : o ≠ .r8)
    (r₀ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 a) 8)
    (r₁ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (a + 8)) 8)
    (w₀ : InRegions s.wr (W + BitVec.ofNat 64 d) 8) (w₁ : InRegions s.wr (W + BitVec.ofNat 64 (d + 8)) 8) :
    ∃ s', runBlock isa (dbl b a o d) s = some s' ∧
      BlkStep W d (double (blockAtMem s.mem (B + BitVec.ofNat 64 a))) [.rax, .rdx, .rcx, .r8] s s' ∧
      s'.xmm = s.xmm := by
  refine ⟨_, by orun [dbl, h15, hb, hba, hoa, hod, hoc, ho8, r₀, r₁, w₀, w₁], ?_, ?_⟩
  rotate_left
  · simp only [xmm_setReg, xmm_arithFlags, xmm_setFlags]
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl⟩
  · simp only [mem_setReg, mem_arithFlags, mem_setFlags]; rw [← addr8 W d]; exact frame_store2 _ _ _ _
  · simp only [mem_setReg, mem_arithFlags, mem_setFlags, BitVec.xor_self]
    rw [← addr8 W d, blockAtMem_store2, ← addr8 B a]
    exact dbl_mem _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

/-- `copy16_ok`, and the SSE registers are kept. -/
theorem copy16_okX {W : Addr} {s : State} {a d : Nat} (h15 : s.gpr .r15 = W)
    (r₀ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 a) 8)
    (r₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 (a + 8)) 8)
    (w₀ : InRegions s.wr (W + BitVec.ofNat 64 d) 8) (w₁ : InRegions s.wr (W + BitVec.ofNat 64 (d + 8)) 8) :
    ∃ s', runBlock isa (copy16 a d) s = some s' ∧
      BlkStep W d (blockAtMem s.mem (W + BitVec.ofNat 64 a)) [.rax, .rdx] s s' ∧ s'.xmm = s.xmm := by
  refine ⟨_, by orun [copy16, h15, r₀, r₁, w₀, w₁], ?_, ?_⟩
  rotate_left
  · simp only [xmm_setReg]
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl⟩
  · simp only [mem_setReg]; rw [← addr8 W d]; exact frame_store2 _ _ _ _
  · simp only [mem_setReg]; rw [← addr8 W d, blockAtMem_store2, ← addr8 W a, blockAtMem_words]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, hr.1, hr.2, ite_false]

end VG.Proof.AesOcb.X86_64
