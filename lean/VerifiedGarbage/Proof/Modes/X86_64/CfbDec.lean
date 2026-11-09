module

public import VerifiedGarbage.Impl.Modes.X86_64.CfbDec
public import VerifiedGarbage.Proof.Modes.X86_64.Copy
public import VerifiedGarbage.Proof.Modes.Ctr
public import VerifiedGarbage.Proof.Modes.X86_64.CbcGroup
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Modes.Cbc
public import VerifiedGarbage.Proof.Modes.Fb
public import VerifiedGarbage.Proof.Modes.X86_64.Setup
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Spec.Cfb
import VerifiedGarbage.Proof.Modes.X86_64.Words
import VerifiedGarbage.Proof.Modes.X86_64.Steps
import VerifiedGarbage.Proof.Modes.Addr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Modes.CfbDec
import VerifiedGarbage.Proof.Modes.X86_64.Xor
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Modes.X86_64.CbcDecChained
import VerifiedGarbage.Proof.Modes.CbcNext
import VerifiedGarbage.Proof.Modes.X86_64.Ctr
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Lit

/-!
# Batched CFB128 decryption on x86-64 that updates the IV, for any core

`batched_wp`: `c.cfbDecryptBatched r` is CFB decryption of the data
(`Spec.Cfb.decrypt`), which also replaces the IV at `P` with the last block
of the data on entry (`Spec.Cbc.next`), as CBC decryption's does
(`cbcDecryptChained_wp`, whose entry, `cbcLastToIv` and exit it shares).

* `gather_wp`: `cfbDecGather` makes the core's buffer the group's `n ≥ 1`
  input blocks, the chaining value and then the group's ciphertext blocks
  but its last, which becomes the chaining value, and changes no other
  memory (`Gathered`); `copyBlocksEnd_wp` is `copyBlocks_wp`, with where
  `rbx` ends.
* `group_wp`: one iteration of the data loop gathers the group's input
  blocks, enciphers them in the buffer (`BlockSpec.crypt_wp`), XORs them
  into the group's ciphertext blocks (`xorBlocks_wp`) and steps to the next
  group. Block `j` of the data becomes CFB decryption's plaintext block `j`
  (`fbOut .cfbDec`), whose input block is CBC's chaining value
  (`CfbDec.input_eq`). `loop_wp`: the data loop.
-/

@[expose] public section
namespace VG.Proof.Modes.X86_64.CfbDec
open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Modes.X86_64
open VG.Impl.Aes.X86_64 (sb movR movS st)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Modes.CfbDec (input_eq of_dinv)
variable {c : Core}

/-- `copyBlocks_wp`, with `rbx` past the `n` blocks it copied from. -/
theorem copyBlocksEnd_wp {S T : Addr} {n : Nat} {s₀ : State} (hbw : 0 < c.bw) (hL : 8 * c.bw < 2 ^ 31)
    (hn : 0 < n) (hfit : 8 * c.bw * n < 2 ^ 63)
    (hS : ∀ t < c.bw * n, InRegions (s₀.rd ++ s₀.wr) (S + BitVec.ofNat 64 (8 * t)) 8)
    (hT : ∀ t < c.bw * n, InRegions s₀.wr (T + BitVec.ofNat 64 (8 * t)) 8)
    (hsep : Region.Disjoint ⟨S, 8 * c.bw * n⟩ ⟨T, 8 * c.bw * n⟩) (ha : s₀.gpr .rax = T) (hb : s₀.gpr .rbx = S)
    (hc : s₀.gpr .rcx = BitVec.ofNat 64 n) :
    WP isa c.copyBlocks s₀ fun s =>
      CopyInv c S T n s₀ n s ∧ s.gpr .rbx = S + BitVec.ofNat 64 (8 * c.bw * n) := by
  have hn64 : n ≤ 8 * c.bw * n := Nat.le_mul_of_pos_left n (by omega)
  refine WP.mono (blockLoop_wp (c := c) _ (CopyInv c S T n s₀) hL hn (by omega)
    (fun j s s' h hm hrd hwr hg => ⟨fun t ht => by rw [hm]; exact h.copied t ht, by rw [hm]; exact h.frame,
      fun r h1 h2 h3 h4 => by rw [hg r h1 h2 h3, h.regs r h1 h2 h3 h4], by rw [hrd, h.rd], by rw [hwr, h.wr]⟩)
    (fun j hj s hi hax hbx => ?_) ⟨fun t ht => by omega, Frame.refl _ _, fun _ _ _ _ _ => rfl, rfl, rfl⟩ ha hb hc)
    fun _ h => ⟨h.1, h.2.2⟩
  have hlt := idx_lt (L := 8 * c.bw) hj
  have hw : ∀ w, 8 * c.bw * j + 8 * w = 8 * (c.bw * j + w) := fun w => by rw [Nat.mul_add, Nat.mul_assoc]
  have hbj : ∀ w < c.bw, c.bw * j + w < c.bw * n := fun w hw' => by have := idx_lt (L := c.bw) hj; omega
  have hSs : ∀ t < 8 * c.bw * n, s.mem (S + BitVec.ofNat 64 t) = s₀.mem (S + BitVec.ofNat 64 t) := fun t ht =>
    hi.frame.bytes (R := ⟨S, 8 * c.bw * n⟩) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsep)
      (by simp only; omega) ht
  have hPT : Region.Sub ⟨T + BitVec.ofNat 64 (8 * c.bw * j), 8 * c.bw⟩ ⟨T, 8 * c.bw * n⟩ :=
    VG.Offset.sub_base T (by omega)
  refine WP.mono (copyN_wp (k := c.bw) (P := T + BitVec.ofNat 64 (8 * c.bw * j))
    (Q := S + BitVec.ofNat 64 (8 * c.bw * j)) ⟨by rw [hax]; simp, by rw [hbx]; simp,
    by decide, by decide, fun w hw' => by rw [hi.wr, addr_add, hw w]; exact hT _ (hbj w hw'),
    fun w hw' => by rw [hi.rd, hi.wr, addr_add, hw w]; exact hS _ (hbj w hw'),
    (hsep.symm.sub_left hPT).sub_right (VG.Offset.sub_base S (by omega)), by omega⟩) fun s' h' => ?_
  have hm : ∀ t < 8 * c.bw * n, s'.mem (T + BitVec.ofNat 64 t) =
      if 8 * c.bw * j ≤ t ∧ t < 8 * c.bw * j + 8 * c.bw then s.mem (S + BitVec.ofNat 64 t)
      else s.mem (T + BitVec.ofNat 64 t) := fun t ht => by
    rw [h'.mem]
    split
    · rename_i h1
      rw [show T + BitVec.ofNat 64 t = T + BitVec.ofNat 64 (8 * c.bw * j) + BitVec.ofNat 64 (t - 8 * c.bw * j) by
        rw [addr_add, show 8 * c.bw * j + (t - 8 * c.bw * j) = t by omega], over_at (by omega) (by omega), addr_add,
        show 8 * c.bw * j + (t - 8 * c.bw * j) = t by omega]
    · exact over_out (off_sub_not T (by omega) (by omega) (by omega) (by omega))
  refine ⟨⟨fun t ht => ?_, hi.frame.trans fun x hx => ?_, fun r h1 h2 h3 h4 => by rw [h'.regs r h4, hi.regs r h1 h2 h3 h4],
    by rw [h'.rd, hi.rd], by rw [h'.wr, hi.wr]⟩, h'.regs _ (by decide), h'.regs _ (by decide), h'.regs _ (by decide)⟩
  · have : 8 * c.bw * (j + 1) = 8 * c.bw * j + 8 * c.bw := Nat.mul_succ _ _
    rw [hm t (by omega)]
    split
    · rw [hSs t (by omega)]
    · exact hi.copied t (by omega)
  · rw [h'.mem]
    exact over_out fun h => hx _ (List.mem_singleton_self _) (hPT x (by simp only [Region.Contains]; omega))

/-- No blocks to copy when ZF is set; otherwise `copyBlocksEnd_wp`. -/
theorem copy_tail_wp {S T : Addr} {n : Nat} {s : State} (hbw : 0 < c.bw) (hL : 8 * c.bw < 2 ^ 31)
    (hfit : 8 * c.bw * n < 2 ^ 63)
    (hS : ∀ t < c.bw * n, InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 (8 * t)) 8)
    (hT : ∀ t < c.bw * n, InRegions s.wr (T + BitVec.ofNat 64 (8 * t)) 8)
    (hsep : Region.Disjoint ⟨S, 8 * c.bw * n⟩ ⟨T, 8 * c.bw * n⟩) (ha : s.gpr .rax = T) (hb : s.gpr .rbx = S)
    (hc : s.gpr .rcx = BitVec.ofNat 64 n) (hz : s.zf = some (decide (n = 0))) :
    WP isa (.ite .e (.block []) c.copyBlocks) s fun s' =>
      CopyInv c S T n s n s' ∧ s'.gpr .rbx = S + BitVec.ofNat 64 (8 * c.bw * n) := by
  refine WP.ite (decide (n = 0)) (by simp [X86_64.eval, hz]) (fun h => ?_) (fun h => ?_)
  · have hn0 : n = 0 := by simpa using h
    subst hn0
    exact WP.block_nil ⟨⟨fun t ht => by simp at ht, Frame.refl _ _, fun _ _ _ _ _ => rfl, rfl, rfl⟩,
      by simpa using hb⟩
  · have hn0 : n ≠ 0 := by simpa using h
    exact copyBlocksEnd_wp hbw hL (by omega) hfit hS hT hsep ha hb hc

/-- `cfbDecGatherArgs`: past the buffer's first block in `rax`, the data's
address in `rbx`, one fewer in `rcx`. -/
theorem gatherArgs_ok (hb : 8 * c.buf + 16 < 2 ^ 31) (hda : c.dataReg ≠ .rax) (s : State) {B : Addr}
    (hB : s.gpr sb = B) :
    ∃ s', runBlock isa c.cfbDecGatherArgs s = some s' ∧ s'.gpr .rax = B + BitVec.ofNat 64 (8 * c.buf + 16) ∧
      s'.gpr .rbx = s.gpr c.dataReg ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s .rax sb
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := addImm_ok s₁ .rax (BitVec.ofNat 32 (8 * c.buf + 16))
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := movR_ok s₂ .rbx c.dataReg
  obtain ⟨s₄, e₄, c₄, z₄, o₄, m₄, rd₄, wr₄⟩ := subImm_ok s₃ .rcx 1
  have hc : s₃.gpr .rcx = s.gpr .rcx := by rw [o₃ _ (by decide), o₂ _ (by decide), o₁ _ (by decide)]
  refine ⟨s₄, ?_, by rw [o₄ _ (by decide), o₃ _ (by decide), r₂, r₁, hB, signExtend_small hb],
    by rw [o₄ _ (by decide), r₃, o₂ _ hda, o₁ _ hda], by rw [c₄, hc]; rfl, by rw [z₄, hc]; rfl,
    fun r h1 h2 h3 => by rw [o₄ r h3, o₃ r h2, o₂ r h1, o₁ r h1], by rw [m₄, m₃, m₂, m₁],
    by rw [rd₄, rd₃, rd₂, rd₁], by rw [wr₄, wr₃, wr₂, wr₁]⟩
  rw [Core.cfbDecGatherArgs, show ([movR .rax sb, .alu .add .rax (.imm (BitVec.ofNat 32 (8 * c.buf + 16))),
      movR .rbx c.dataReg, .alu .sub .rcx (.imm 1)] : List Instr) =
      [movR .rax sb] ++ ([.alu .add .rax (.imm (BitVec.ofNat 32 (8 * c.buf + 16)))] ++
      ([movR .rbx c.dataReg] ++ [.alu .sub .rcx (.imm 1)])) from rfl,
    runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃, Option.bind_some, e₄]

/-- The gathered input blocks and the next chaining value, before they are
enciphered: the `n` blocks at `B + 8 buf` are the chaining value (at
`B + 8 hiSlot`) and the first `n - 1` blocks at `A`, and the chaining value
is the last. -/
structure Gathered (c : Core) (B A : Addr) (n : Nat) (s₀ s : State) : Prop where
  inputs : ∀ t < 16 * n, s.mem (B + BitVec.ofNat 64 (8 * c.buf) + BitVec.ofNat 64 t) =
    if t < 16 then s₀.mem (B + BitVec.ofNat 64 (8 * c.hiSlot) + BitVec.ofNat 64 t)
    else s₀.mem (A + BitVec.ofNat 64 (t - 16))
  chain : ∀ u < 16, s.mem (B + BitVec.ofNat 64 (8 * c.hiSlot) + BitVec.ofNat 64 u) =
    s₀.mem (A + BitVec.ofNat 64 (16 * (n - 1) + u))
  frame : Frame [⟨B + BitVec.ofNat 64 (8 * c.buf), 16 * n⟩,
    ⟨B + BitVec.ofNat 64 (8 * c.hiSlot), 16⟩] s₀.mem s.mem
  regs : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .rbp → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- `cfbDecGather` reads the group's ciphertext before writing anything but
the buffer and the chaining value, including in a short last group. -/
theorem gather_wp {B A : Addr} {n : Nat} {s : State}
    (hbw : c.bw = 2) (hn : 0 < n) (hfit : 16 * n < 2 ^ 63) (hbuf : 8 * c.buf + 16 < 2 ^ 31)
    (hda : c.dataReg ≠ .rax) (hdbp : c.dataReg ≠ .rbp)
    (hB : s.gpr sb = B) (hA : s.gpr c.dataReg = A) (hc : s.gpr .rcx = BitVec.ofNat 64 n)
    (inT : ∀ w < 2 * n, InRegions s.wr (B + BitVec.ofNat 64 (8 * c.buf) + BitVec.ofNat 64 (8 * w)) 8)
    (inH : ∀ w < 2, InRegions s.wr (B + BitVec.ofNat 64 (8 * c.hiSlot) + BitVec.ofNat 64 (8 * w)) 8)
    (inA : ∀ w < 2 * n, InRegions (s.rd ++ s.wr) (A + BitVec.ofNat 64 (8 * w)) 8)
    (dTA : Region.Disjoint ⟨B + BitVec.ofNat 64 (8 * c.buf), 16 * n⟩ ⟨A, 16 * n⟩)
    (dTH : Region.Disjoint ⟨B + BitVec.ofNat 64 (8 * c.buf), 16 * n⟩ ⟨B + BitVec.ofNat 64 (8 * c.hiSlot), 16⟩)
    (dHA : Region.Disjoint ⟨B + BitVec.ofNat 64 (8 * c.hiSlot), 16⟩ ⟨A, 16 * n⟩) :
    WP isa c.cfbDecGather s (Gathered c B A n s) := by
  let T := B + BitVec.ofNat 64 (8 * c.buf)
  let H := B + BitVec.ofNat 64 (8 * c.hiSlot)
  let U := T + BitVec.ofNat 64 16
  have h16 : 16 ≤ 16 * n := by omega_arith
  have subT : Region.Sub ⟨T, 16⟩ ⟨T, 16 * n⟩ := Region.sub_prefix h16
  have subU : Region.Sub ⟨U, 16 * (n - 1)⟩ ⟨T, 16 * n⟩ := VG.Offset.sub_base T (by omega_arith)
  have subA : Region.Sub ⟨A, 16 * (n - 1)⟩ ⟨A, 16 * n⟩ := Region.sub_prefix (by omega_arith)
  unfold Core.cfbDecGather
  -- The chaining value to the buffer's first block.
  refine WP.seq (WP.block_append (WP.mono (copyN_wp (k := 2) (P := T) (Q := H) (t := .rbp)
    ⟨by rw [hB], by rw [hB], by decide, by decide,
      fun w hw => inT w (by omega_arith), fun w hw => inRd (inH w hw), dTH.sub_left subT, by decide⟩)
    fun s₁ h₁ => ?_))
  obtain ⟨s₂, e₂, a₂, b₂, c₂, z₂, o₂, m₂, rd₂, wr₂⟩ := gatherArgs_ok hbuf hda s₁
    (by rw [h₁.regs _ (by decide), hB])
  refine WP.of_runBlock ⟨s₂, e₂, ?_⟩
  have cm₂ : s₂.mem = over s.mem T 16 (fun i => s.mem (H + BitVec.ofNat 64 i)) := by rw [m₂, h₁.mem]
  have rd₂' : s₂.rd = s.rd := by rw [rd₂, h₁.rd]
  have wr₂' : s₂.wr = s.wr := by rw [wr₂, h₁.wr]
  have rcx₁ : s₁.gpr .rcx = BitVec.ofNat 64 n := by rw [h₁.regs _ (by decide), hc]
  -- The group's ciphertext blocks but its last to the rest of the buffer.
  refine WP.seq (WP.mono (copy_tail_wp (c := c) (S := A) (T := U) (n := n - 1)
    (by omega_arith) (by omega_arith) (by rw [hbw]; omega_arith)
    (fun w hw => by rw [rd₂', wr₂']; exact inA w (by rw [hbw] at hw; omega_arith))
    (fun w hw => by
      rw [wr₂', addr_add, show 16 + 8 * w = 8 * (2 + w) by omega_arith]
      exact inT (2 + w) (by rw [hbw] at hw; omega_arith))
    (by simpa [hbw] using (dTA.symm.sub_left subA).sub_right subU)
    (by rw [a₂]; exact (addr_add B (8 * c.buf) 16).symm)
    (by rw [b₂, h₁.regs _ hdbp, hA])
    (by rw [c₂, rcx₁, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
      VG.Offset.ofNat_sub_ofNat (by omega_arith)])
    (by rw [z₂, rcx₁, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
      VG.Offset.ofNat_sub_ofNat_beq (by omega_arith) (by decide)]
        simp only [Option.some.injEq, decide_eq_decide]; omega_arith))
    fun s₃ ⟨h₃, p₃⟩ => ?_)
  have base₃ : s₃.gpr sb = B := by
    rw [h₃.regs _ (by decide) (by decide) (by decide) (by decide), o₂ _ (by decide) (by decide) (by decide),
      h₁.regs _ (by decide), hB]
  have A₂ : ∀ t < 16 * n, s₂.mem (A + BitVec.ofNat 64 t) = s.mem (A + BitVec.ofNat 64 t) := by
    intro t ht; rw [cm₂]; exact over_sep (dTA.sub_left subT) ht (by omega_arith)
  have A₃ : ∀ t < 16 * n, s₃.mem (A + BitVec.ofNat 64 t) = s.mem (A + BitVec.ofNat 64 t) := by
    intro t ht
    have fr := h₃.frame
    rw [hbw] at fr
    exact (fr.bytes (R := ⟨A, 16 * n⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dTA.symm.sub_right subU) (by simp only; omega_arith)
      ht).trans (A₂ t ht)
  -- The group's last ciphertext block to the chaining value.
  refine WP.mono (copyN_wp (k := 2) (P := H) (Q := A + BitVec.ofNat 64 (16 * (n - 1))) (t := .rbp)
    ⟨by rw [base₃], by rw [p₃, hbw]; simp, by decide, by decide,
      fun w hw => by rw [h₃.wr, wr₂']; exact inH w hw,
      fun w hw => by
        rw [h₃.rd, h₃.wr, rd₂', wr₂', addr_add, show 16 * (n - 1) + 8 * w = 8 * (2 * (n - 1) + w) by omega_arith]
        exact inA _ (by omega_arith),
      dHA.sub_right (VG.Offset.sub_base A (by omega_arith)), by decide⟩) fun s₄ h₄ => ?_
  have T₄ : ∀ t < 16 * n, s₄.mem (T + BitVec.ofNat 64 t) = s₃.mem (T + BitVec.ofNat 64 t) := by
    intro t ht; rw [h₄.mem]; exact over_sep dTH.symm ht (by omega_arith)
  refine ⟨?_, ?_, ?_, fun r h1 h2 h3 h4 => by
    rw [h₄.regs r h4, h₃.regs r h1 h2 h3 h4, o₂ r h1 h2 h3, h₁.regs r h4],
    by rw [h₄.rd, h₃.rd, rd₂'], by rw [h₄.wr, h₃.wr, wr₂']⟩
  · intro t ht
    rw [T₄ t ht]
    by_cases h : t < 16
    · rw [ite_eq_left h]
      have fr := h₃.frame
      rw [hbw] at fr
      have keep := fr.bytes (R := ⟨T, 16⟩) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact VG.Offset.base_disjoint T (e := 16) (n := 16 * (n - 1)) (by decide) (by omega_arith))
        (by simp only; decide) h
      rw [keep, cm₂, over_at h (by decide)]
    · rw [ite_eq_right h, show T + BitVec.ofNat 64 t = U + BitVec.ofNat 64 (t - 16) by
        change T + BitVec.ofNat 64 t = (T + BitVec.ofNat 64 16) + BitVec.ofNat 64 (t - 16)
        have e := addr_add T 16 (t - 16)
        rw [show 16 + (t - 16) = t by omega_arith] at e
        exact e.symm,
        h₃.copied _ (by rw [hbw]; omega_arith), A₂ _ (by omega_arith)]
  · intro u hu
    rw [h₄.mem, over_at hu (by decide), addr_add, A₃ _ (by omega_arith)]
  · have f₁ : Frame [⟨T, 16⟩] s.mem s₁.mem := by rw [h₁.mem]; exact over_frame _ _ _ _
    have f₂ : Frame [⟨T, 16⟩] s.mem s₂.mem := by rw [m₂]; exact f₁
    have f₃ := h₃.frame
    rw [hbw] at f₃
    refine ((f₂.sub (fun r hr => ⟨⟨T, 16 * n⟩, List.mem_cons_self, by
      simp only [List.mem_singleton] at hr; subst hr; exact subT⟩)).trans
      (f₃.sub (fun r hr => ⟨⟨T, 16 * n⟩, List.mem_cons_self, by
        simp only [List.mem_singleton] at hr; subst hr; exact subU⟩))).trans ?_
    rw [h₄.mem]
    exact (over_frame _ _ _ _).sub fun r hr => ⟨⟨H, 16⟩, List.mem_cons_of_mem _ List.mem_cons_self, by
      simp only [List.mem_singleton] at hr; subst hr; exact fun _ hx => hx⟩

/-- The data loop, before group `g`, from the IV `iv` with the key `k`. -/
structure Inv (cs : BlockSpec c) (s₀ : State) (B D : Addr) (n : Nat) (k : cs.Key) (iv : List Byte) (g : Nat)
    (s : State) : Prop where
  base : s.gpr sb = B
  rsp : s.gpr .rsp = s₀.gpr .rsp
  ready : cs.Ready s B k
  saved : ∀ i < 6, s.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64
  dataR : s.gpr c.dataReg = D + BitVec.ofNat 64 (8 * c.bw * (c.G * g))
  leftR : s.gpr c.leftReg = BitVec.ofNat 64 (n - c.G * g)
  lt : c.G * g < n
  chain : ∀ u < 8 * c.bw, s.mem (chainAddr c B + BitVec.ofNat 64 u) =
    (cbcPrev (8 * c.bw) s₀.mem D iv (c.G * g)).getD u 0
  data : DInv (8 * c.bw) s₀.mem s.mem D n (c.G * g) (fbOut .cfbDec (8 * c.bw) (cs.cipher k) s₀.mem D iv)
  frame : Frame ([⟨B, 8 * c.ctrSlots⟩, ⟨D, 8 * c.bw * n⟩] ++ stkList c (s₀.gpr .rsp)) s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The data loop, done. -/
structure Done (cs : BlockSpec c) (s₀ : State) (B D : Addr) (n : Nat) (k : cs.Key) (iv : List Byte) (s : State) :
    Prop where
  base : s.gpr sb = B
  rsp : s.gpr .rsp = s₀.gpr .rsp
  saved : ∀ i < 6, s.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64
  data : DInv (8 * c.bw) s₀.mem s.mem D n n (fbOut .cfbDec (8 * c.bw) (cs.cipher k) s₀.mem D iv)
  frame : Frame ([⟨B, 8 * c.ctrSlots⟩, ⟨D, 8 * c.bw * n⟩] ++ stkList c (s₀.gpr .rsp)) s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem group_wp (cs : BlockSpec c) (hbw : c.bw = 2) {s₀ : State} {B D : Addr} {n : Nat} {k : cs.Key}
    {iv : List Byte} (hiv : iv.length = 8 * c.bw) (hp : GPre c s₀ B D n (8 * c.bw)) {g : Nat} {s : State}
    (hi : Inv cs s₀ B D n k iv g s) :
    WP isa c.cfbDecGroup s fun s' => (s'.zf = some true ∧ Done cs s₀ B D n k iv s') ∨
      (s'.zf = some false ∧ Inv cs s₀ B D n k iv (g + 1) s') := by
  have hL := cs.layout
  have hsm := hL.small
  have hroom := hL.room
  have hbuf := hL.buf_le
  have hG0 := hL.G_pos
  have hbw0 := hL.bw_pos
  have hbw2 := hL.bw_le
  have hfit := hp.scr.fit
  have hfitD := hp.fitD
  have hk := hi.lt
  have hL0 : 0 < 8 * c.bw := by omega_using [hbw0]
  have hGb : c.G ≤ c.bw * c.G := Nat.le_mul_of_pos_left _ hbw0
  obtain ⟨hregs, hdl⟩ := regsOk_ne cs.regs_ok
  obtain ⟨da, db, dc, dbp, d10, dsb, dsp, -⟩ := hregs c.dataReg List.mem_cons_self
  obtain ⟨la, lb, lc, lbp, l10, lsb, lsp, -⟩ := hregs c.leftReg (List.mem_cons_of_mem _ List.mem_cons_self)
  have hN : 8 * c.ctrSlots < 2 ^ 64 := by simp only [Core.ctrSlots]; omega_using [hsm]
  let v := n - c.G * g
  let cc := min v c.G
  have h8n : 8 * n ≤ 8 * c.bw * n := Nat.mul_le_mul_right n (by omega_using [hL0])
  have hv : v < 2 ^ 64 := by omega_using [hfitD, h8n]
  have hc0 : 0 < cc := by omega_using [hG0, hk]
  have hcG : cc ≤ c.G := by omega_using []
  have hkc : 8 * c.bw * (c.G * g) + 8 * c.bw * cc ≤ 8 * c.bw * n := by
    rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by omega_using [hc0])
  have hbwcc : 8 * c.bw * cc = 8 * (c.bw * cc) := Nat.mul_assoc _ _ _
  have hbG : c.bw * cc ≤ c.bw * c.G := Nat.mul_le_mul_left _ hcG
  have hcc1 : 8 * c.bw ≤ 8 * c.bw * cc := Nat.le_mul_of_pos_right _ hc0
  have hccsmall : 16 * cc < 2 ^ 31 := by
    have h1 := hbuf; rw [hbw] at h1; omega_using [hsm, hroom, h1, hcG]
  let A := D + BitVec.ofNat 64 (8 * c.bw * (c.G * g))
  let T := B + BitVec.ofNat 64 (8 * c.buf)
  let H := chainAddr c B
  have hwS : (⟨B, 8 * c.ctrSlots⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.scr.wr
  have hwD : (⟨D, 8 * c.bw * n⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.dat
  have subS : ∀ {d l : Nat}, d + l ≤ 8 * c.ctrSlots → Region.Sub ⟨B + BitVec.ofNat 64 d, l⟩ ⟨B, 8 * c.ctrSlots⟩ :=
    fun h => VG.Offset.sub_base B h
  have subCore : Region.Sub (coreRegion c B) ⟨B, 8 * c.ctrSlots⟩ :=
    Region.sub_prefix (by simp only [Core.ctrSlots]; omega_using [hroom])
  have subA : Region.Sub ⟨A, 8 * c.bw * cc⟩ ⟨D, 8 * c.bw * n⟩ := VG.Offset.sub_base D hkc
  have subT : Region.Sub ⟨T, 8 * c.bw * cc⟩ ⟨B, 8 * c.ctrSlots⟩ :=
    subS (by simp only [Core.ctrSlots]; omega_using [hroom, hbuf, hbwcc, hbG])
  have subH : Region.Sub ⟨H, 8 * c.bw⟩ ⟨B, 8 * c.ctrSlots⟩ :=
    subS (by simp only [Core.hiSlot, Core.ctrSlots]; omega_using [hroom, hbw2])
  have subTbuf : Region.Sub ⟨T, 8 * c.bw * cc⟩ (blkRegion c B) := Region.sub_prefix (Nat.mul_le_mul_left _ hcG)
  have dDS : ∀ {r : Region}, Region.Sub r ⟨B, 8 * c.ctrSlots⟩ → Region.Disjoint ⟨D, 8 * c.bw * n⟩ r :=
    fun h => hp.sep.sub_right h
  have dAT : Region.Disjoint ⟨A, 8 * c.bw * cc⟩ ⟨T, 8 * c.bw * cc⟩ := (dDS subT).sub_left subA
  have dTH : Region.Disjoint ⟨T, 8 * c.bw * cc⟩ ⟨H, 8 * c.bw⟩ :=
    VG.Offset.disjoint B (.inl (by simp only [Core.hiSlot]; omega_using [hbuf, hbwcc, hbG]))
      (by omega_using [hsm, hroom, hbuf, hbwcc, hbG]) (by simp only [Core.hiSlot]; omega_using [hsm, hroom, hbw2])
  have dAH : Region.Disjoint ⟨A, 8 * c.bw * cc⟩ ⟨H, 8 * c.bw⟩ := (dDS subH).sub_left subA
  have dHcore : Region.Disjoint ⟨H, 8 * c.bw⟩ (coreRegion c B) :=
    VG.Offset.disjoint_base B (by simp only [Core.hiSlot]; omega_using [])
      (by simp only [Core.hiSlot]; omega_using [hsm, hroom, hbw2])
  have inT : ∀ t, t < c.bw * cc → InRegions s.wr (T + BitVec.ofNat 64 (8 * t)) 8 := fun t ht =>
    ⟨_, hwS, by
      rw [addr_add]
      exact VG.Offset.contains_base B (by simp only [Core.ctrSlots]; omega_using [hroom, hbuf, hbG, ht])
        (by omega_using [hsm, hroom, hbuf, hbG, ht])⟩
  have inA : ∀ t, t < c.bw * cc → InRegions s.wr (A + BitVec.ofNat 64 (8 * t)) 8 := fun t ht =>
    ⟨_, hwD, by
      rw [addr_add]
      exact VG.Offset.contains_base D (by omega_using [hkc, hbwcc, ht]) (by omega_using [hfitD, hkc, hbwcc, ht])⟩
  have inH : ∀ w < c.bw, InRegions s.wr (H + BitVec.ofNat 64 (8 * w)) 8 := fun w hw =>
    ⟨_, hwS, by
      rw [addr_add]
      exact VG.Offset.contains_base B (by simp only [Core.hiSlot, Core.ctrSlots]; omega_using [hroom, hbw2, hw])
        (by simp only [Core.hiSlot]; omega_using [hsm, hroom, hbw2, hw])⟩
  unfold Core.cfbDecGroup
  -- The count, and the group's input blocks, the preceding ciphertext blocks, to the buffer.
  refine WP.seq (WP.mono_syms (groupCount_wp (by omega_using [hsm, hroom, hbuf, hGb]) lc hi.leftR hv)
    fun s₁ ⟨c₁, o₁, m₁, rd₁, wr₁⟩ sy₁ => ?_)
  have base₁ : s₁.gpr sb = B := by rw [o₁ _ (by decide), hi.base]
  refine WP.seq (WP.mono_syms (gather_wp hbw hc0 (by omega_using [hccsmall])
    (by have h1 := hbuf; rw [hbw] at h1; omega_using [hsm, hroom, h1, hG0]) da dbp base₁
    (by rw [o₁ _ dc, hi.dataR]) c₁
    (fun w hw => by rw [wr₁]; exact inT w (by rw [hbw]; exact hw))
    (fun w hw => by rw [wr₁]; exact inH w (by rw [hbw]; exact hw))
    (fun w hw => by rw [rd₁, wr₁]; exact inRd (inA w (by rw [hbw]; exact hw)))
    (by simpa only [A, T, H, chainAddr, hbw, Nat.reduceMul] using dAT.symm)
    (by simpa only [A, T, H, chainAddr, hbw, Nat.reduceMul] using dTH)
    (by simpa only [A, T, H, chainAddr, hbw, Nat.reduceMul] using dAH.symm)) fun s₃ h₃ sy₃ => ?_)
  have keep₃ : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .rbp → s₃.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 => by rw [h₃.regs r h1 h2 h3 h4, o₁ r h3]
  have base₃ : s₃.gpr sb = B := by rw [keep₃ _ (by decide) (by decide) (by decide) (by decide), hi.base]
  have rd₃' : s₃.rd = s.rd := by rw [h₃.rd, rd₁]
  have wr₃' : s₃.wr = s.wr := by rw [h₃.wr, wr₁]
  have f₃ : Frame [⟨T, 8 * c.bw * cc⟩, ⟨H, 8 * c.bw⟩] s.mem s₃.mem := by
    simpa only [A, T, H, chainAddr, hbw, Nat.reduceMul, m₁] using h₃.frame
  have ready₃ : cs.Ready s₃ B k := cs.ready_frame hi.ready f₃ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr subTbuf
    · exact .inl dHcore.symm)
    ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, hwS, subT⟩
      · exact ⟨_, hwS, subH⟩,
      rd₃', wr₃', by rw [sy₃, sy₁]⟩ fun r hr => by
    obtain ⟨h1, h2, h3, h4, -⟩ := of_not_modeRegs hr
    exact keep₃ r h1 h2 h3 h4
  -- Enciphered.
  refine WP.seq (WP.mono (cs.crypt_wp base₃ ⟨by rw [wr₃']; exact hwS, hfit⟩ ready₃)
    fun s₄ ⟨base₄, rsp₄, dr₄, lr₄, ready₄, f₄, ks₄, rd₄, wr₄⟩ => ?_)
  rw [show s₃.gpr .rsp = s₀.gpr .rsp by
    rw [keep₃ _ (by decide) (by decide) (by decide) (by decide), hi.rsp]] at f₄
  have left₄ : s₄.gpr c.leftReg = BitVec.ofNat 64 v := by rw [lr₄, keep₃ _ la lb lc lbp, hi.leftR]
  have data₄ : s₄.gpr c.dataReg = A := by rw [dr₄, keep₃ _ da db dc dbp, hi.dataR]
  refine WP.seq (WP.mono_syms (groupCount_wp (by omega_using [hsm, hroom, hbuf, hGb]) lc left₄ hv)
    fun s₅ ⟨c₅, o₅, m₅, rd₅, wr₅⟩ sy₅ => ?_)
  have base₅ : s₅.gpr sb = B := by rw [o₅ _ (by decide), base₄]
  obtain ⟨s₆, e₆, a₆, b₆, t₆, o₆, m₆, rd₆, wr₆⟩ := xorArgs_ok (by omega_using [hsm, hroom, hbuf]) da s₅ base₅
  refine WP.seq (WP.of_runBlock ⟨s₆, e₆, ?_⟩)
  have mem₆ : s₆.mem = s₄.mem := by rw [m₆, m₅]
  have rd₆' : s₆.rd = s.rd := by rw [rd₆, rd₅, rd₄, rd₃']
  have wr₆' : s₆.wr = s.wr := by rw [wr₆, wr₅, wr₄, wr₃']
  -- The enciphered input blocks XORed into the ciphertext blocks.
  refine WP.seq (WP.mono_syms (xorBlocks_wp (A := T) (B := A) hc0 (by omega_using [hccsmall])
    (fun w hw => by rw [rd₆', wr₆']; exact inRd (inT w (by rw [hbw]; exact hw)))
    (fun w hw => by rw [wr₆']; exact inA w (by rw [hbw]; exact hw))
    (by simpa only [A, T, H, chainAddr, hbw, Nat.reduceMul] using dAT.symm)
    ⟨by rw [a₆]; simp [T], by rw [b₆, o₅ _ dc, data₄]; simp [A],
      by rw [o₆ _ (by decide) (by decide) (by decide), c₅, Nat.sub_zero], fun t ht => by omega_using [ht],
      fun t _ _ => rfl, Frame.refl _ _, fun _ _ _ _ _ => rfl, rfl, rfl⟩)
    fun s₇ h₇ sy₇ => ?_)
  have rbx₇ : s₇.gpr .rbx = A + BitVec.ofNat 64 (8 * c.bw * cc) := by
    rw [h₇.rbx, hbw]
  have f₇ : Frame [⟨A, 8 * c.bw * cc⟩] s₄.mem s₇.mem := by
    rw [hbw, ← mem₆]; exact h₇.frame
  have g₇ : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .rbp → r ≠ .r10 → s₇.gpr r = s₄.gpr r :=
    fun r h1 h2 h3 h4 h5 => by rw [h₇.regs r h1 h2 h3 h4, o₆ r h1 h2 h5, o₅ r h3]
  have left₇ : s₇.gpr c.leftReg = BitVec.ofNat 64 v := by rw [g₇ _ la lb lc lbp l10, left₄]
  have r10₇ : s₇.gpr .r10 = BitVec.ofNat 64 cc := by
    rw [h₇.regs _ (by decide) (by decide) (by decide) (by decide), t₆, c₅]
  -- On to the next group.
  obtain ⟨s₈, e₈, d₈, l₈, z₈, o₈, m₈, rd₈, wr₈⟩ := advance_ok hdl d10 s₇
  refine WP.of_runBlock ⟨s₈, e₈, ?_⟩
  have hz : s₈.zf = some (decide (v = cc)) := by
    rw [z₈, left₇, r10₇, VG.Offset.ofNat_sub_ofNat_beq hv (by omega_using [hfitD, h8n])]
  have keep₈ : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .rbp → r ≠ .r10 → r ≠ c.dataReg → r ≠ c.leftReg →
      s₈.gpr r = s₄.gpr r := fun r h1 h2 h3 h4 h5 h6 h7 => by rw [o₈ r h6 h7, g₇ r h1 h2 h3 h4 h5]
  have ready₈ : cs.Ready s₈ B k := by
    refine cs.ready_frame ready₄ (by rw [m₈]; exact f₇) (fun r hr => ?_) ⟨fun r hr => ?_, ?_, ?_, ?_⟩ fun r hr => ?_
    · simp only [List.mem_singleton] at hr; subst hr
      exact .inl (((dDS subCore).sub_left subA).symm)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, by rw [wr₄, wr₃']; exact hwD, subA⟩
    · rw [rd₈, h₇.rd, rd₆', rd₄, rd₃']
    · rw [wr₈, h₇.wr, wr₆', wr₄, wr₃']
    · rw [runBlock_syms e₈, sy₇, runBlock_syms e₆, sy₅]
    · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := of_not_modeRegs hr
      exact keep₈ r h1 h2 h3 h4 h5 h6 h7
  -- The bytes, through the steps.
  have hn64 : 8 * c.bw * n ≤ 2 ^ 64 := by omega_using [hfitD]
  have outCore : ∀ {R : Region}, Region.Disjoint R (coreRegion c B) → (∃ w ∈ s₀.wr, Region.Sub R w) →
      R.len ≤ 2 ^ 64 →
      ∀ i < R.len, s₄.mem (R.base + BitVec.ofNat 64 i) = s₃.mem (R.base + BitVec.ofNat 64 i) := fun hd hw hl i hi =>
    f₄.bytes (R := _) (hp.stk.coreFrame_disj hd hw) hl hi
  have outT : ∀ {R : Region}, Region.Disjoint R ⟨T, 8 * c.bw * cc⟩ → Region.Disjoint R ⟨H, 8 * c.bw⟩ →
      R.len ≤ 2 ^ 64 →
      ∀ i < R.len, s₃.mem (R.base + BitVec.ofNat 64 i) = s.mem (R.base + BitVec.ofNat 64 i) := fun hd hh hl i hi =>
    f₃.bytes (R := _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hd
      · exact hh) hl hi
  -- The data before the XOR: as on entry.
  have dat₄ : ∀ i < 8 * c.bw * n, s₄.mem (D + BitVec.ofNat 64 i) = s.mem (D + BitVec.ofNat 64 i) := fun i hin => by
    rw [outCore (R := ⟨D, 8 * c.bw * n⟩) (dDS subCore) ⟨_, hp.dat, fun _ h => h⟩ hn64 i hin,
      outT (R := ⟨D, 8 * c.bw * n⟩) (dDS subT) (dDS subH) hn64 i hin]
  have dat0 : ∀ i, 8 * c.bw * (c.G * g) ≤ i → i < 8 * c.bw * n →
      s.mem (D + BitVec.ofNat 64 i) = s₀.mem (D + BitVec.ofNat 64 i) :=
    fun i h1 h2 => by rw [hi.data i h2, ite_eq_right (by omega_using [h1])]
  -- Each enciphered block is that of the preceding ciphertext block (or the IV).
  have dec₄ : ∀ j < cc, ∀ u < 8 * c.bw, s₄.mem (T + BitVec.ofNat 64 (8 * c.bw * j + u)) =
      (cs.cipher k (cbcPrev (8 * c.bw) s₀.mem D iv (c.G * g + j))).getD u 0 := by
    intro j hj u hu
    have eT : T + BitVec.ofNat 64 (8 * c.bw * j + u) = blkAddr c B j + BitVec.ofNat 64 u := by
      simp only [T, blkAddr]; rw [addr_add, addr_add, Nat.add_assoc]
    rw [eT, ← bytesAt_getD s₄.mem _ hu, ks₄ _ (by omega_using [hj])]
    congr 2
    apply List.ext_getElem (by rw [cbcPrev]; split <;> simp [bytesAt, hiv])
    intro x h1 h2
    rw [show (cbcPrev (8 * c.bw) s₀.mem D iv (c.G * g + j))[x] =
      (cbcPrev (8 * c.bw) s₀.mem D iv (c.G * g + j)).getD x 0 from List.getElem_eq_getD 0]
    have hx : x < 8 * c.bw := by simpa [bytesAt] using h1
    simp only [bytesAt, List.getElem_map, List.getElem_range, blkAddr]
    rw [addr_add, show 8 * c.buf + 8 * c.bw * j + x = 8 * c.buf + (8 * c.bw * j + x) by omega_arith, ← addr_add]
    have inp := h₃.inputs (8 * c.bw * j + x) (by rw [hbw] at *; have := idx_lt (L := 16) hj; omega_arith)
    -- The gathered byte, with the block's length still `8 bw`.
    have inp' : s₃.mem (T + BitVec.ofNat 64 (8 * c.bw * j + x)) =
        if 8 * c.bw * j + x < 8 * c.bw then s.mem (H + BitVec.ofNat 64 (8 * c.bw * j + x))
        else s.mem (A + BitVec.ofNat 64 (8 * c.bw * j + x - 8 * c.bw)) := by
      simpa only [A, T, H, chainAddr, hbw, Nat.reduceMul, m₁] using inp
    rw [inp']
    by_cases hj0 : j = 0
    · subst j
      rw [Nat.mul_zero, Nat.zero_add, ite_eq_left hx, hi.chain x hx, Nat.add_zero]
    · have hjp : 0 < j := Nat.pos_of_ne_zero hj0
      have hmul := Nat.le_mul_of_pos_right (8 * c.bw) hjp
      rw [ite_eq_right (by omega_using [hmul]), addr_add,
        dat0 _ (by omega_using [hmul]) (by have := idx_lt (L := 8 * c.bw) hj; omega_using [hkc, this, hx]),
        cbcPrev, ite_eq_right (by omega_using [hj0])]
      rw [bytesAt_getD _ _ hx, addr_add]
      congr 1
      congr 1
      congr 1
      have := Nat.mul_sub_one (8 * c.bw) j
      have := Nat.mul_sub_one (8 * c.bw) (c.G * g + j)
      have := Nat.mul_add (8 * c.bw) (c.G * g) j
      omega_arith
  -- Offsets within the data.
  have eA : ∀ t, D + BitVec.ofNat 64 (8 * c.bw * (c.G * g) + t) = A + BitVec.ofNat 64 t := fun t => by
    rw [← addr_add]
  have prevEq : ∀ {j u : Nat}, 0 < j → 8 * c.bw * (c.G * g) + (8 * c.bw * (j - 1) + u) =
      8 * c.bw * (c.G * g + j - 1) + u := fun {j u} hj => by
    have := Nat.mul_sub_one (8 * c.bw) j
    have := Nat.mul_sub_one (8 * c.bw) (c.G * g + j)
    have := Nat.mul_add (8 * c.bw) (c.G * g) j
    have := Nat.le_mul_of_pos_right (8 * c.bw) hj
    omega_arith
  have hdata : DInv (8 * c.bw) s₀.mem s₈.mem D n (c.G * g + cc)
      (fbOut .cfbDec (8 * c.bw) (cs.cipher k) s₀.mem D iv) := by
    refine dinv_of_blocks hL0 fun q hq r hr => ?_
    rw [m₈]
    have hqn := idx_lt (L := 8 * c.bw) hq
    by_cases hin : c.G * g ≤ q ∧ q < c.G * g + cc
    · obtain ⟨j, rfl⟩ : ∃ j, q = c.G * g + j := ⟨q - c.G * g, by omega_using [hin]⟩
      have hjc : j < cc := by omega_using [hin]
      have hjl := idx_lt (L := 8 * c.bw) hjc
      have xx := h₇.xored (8 * c.bw * j + r) (by rw [hbw] at *; omega_using [hjl, hr])
      have xx' : s₇.mem (A + BitVec.ofNat 64 (8 * c.bw * j + r)) =
          s₆.mem (T + BitVec.ofNat 64 (8 * c.bw * j + r)) ^^^ s₆.mem (A + BitVec.ofNat 64 (8 * c.bw * j + r)) := xx
      rw [Nat.mul_add, Nat.add_assoc, eA, xx', mem₆, dec₄ j hjc r hr, ← eA,
        dat₄ _ (by omega_using [hr, hjl, hkc]), dat0 _ (by omega_using []) (by omega_using [hr, hjl, hkc]),
        ite_eq_left hin.2, fbOut_getD .cfbDec (cs.cipher_len k) _ _ _ _ hr, input_eq, BitVec.xor_comm]
      rw [Nat.mul_add, Nat.add_assoc]
    · have hlo : q < c.G * g → 8 * c.bw * q + r < 8 * c.bw * (c.G * g) := fun h => by
        have := idx_lt (L := 8 * c.bw) h; omega_using [hr, this]
      have hhi : c.G * g + cc ≤ q → 8 * c.bw * (c.G * g) + 8 * c.bw * cc ≤ 8 * c.bw * q := fun h => by
        rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ h
      have hout : ∀ R ∈ [(⟨A, 8 * c.bw * cc⟩ : Region)],
          ¬ R.Contains (D + BitVec.ofNat 64 (8 * c.bw * q + r)) 1 := fun R hR => by
        simp only [List.mem_singleton] at hR; subst hR
        exact not_contains_off D (by omega_using [hin, hlo, hhi]) (by omega_using [hn64, hr, hqn])
          (by omega_using [hcc1, hr]) (by omega_using [hkc, hn64])
      rw [f₇ _ hout, dat₄ _ (by omega_using [hr, hqn]), hi.data _ (by omega_using [hr, hqn]), idx_div hr, idx_mod hr]
      by_cases h2 : q < c.G * g
      · rw [ite_eq_left (hlo h2), ite_eq_left (by omega_using [h2])]
      · rw [ite_eq_right (by have := Nat.mul_le_mul_left (8 * c.bw) (Nat.le_of_not_lt h2); omega_using [this]),
          ite_eq_right (by omega_using [hin, h2])]
  -- The chaining value: the group's last ciphertext block.
  have chain₈ : ∀ u < 8 * c.bw, s₈.mem (H + BitVec.ofNat 64 u) =
      (cbcPrev (8 * c.bw) s₀.mem D iv (c.G * g + cc)).getD u 0 := by
    intro u hu
    have hl := idx_lt (L := 8 * c.bw) (show cc - 1 < cc by omega_using [hc0])
    have ch₃ : s₃.mem (H + BitVec.ofNat 64 u) = s.mem (A + BitVec.ofNat 64 (8 * c.bw * (cc - 1) + u)) := by
      simpa only [A, T, H, chainAddr, hbw, Nat.reduceMul, m₁] using
        h₃.chain u (by simpa only [A, T, H, chainAddr, hbw, Nat.reduceMul] using hu)
    rw [m₈, f₇.bytes (R := ⟨H, 8 * c.bw⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dAH.symm)
      (by simp only; omega_using [hbw2]) hu,
      outCore (R := ⟨H, 8 * c.bw⟩) dHcore ⟨_, hp.scr.wr, subH⟩ (by simp only; omega_using [hbw2]) u hu,
      ch₃, ← eA, dat0 _ (by omega_using []) (by omega_using [hkc, hu, hl]),
      cbcPrev, ite_eq_right (by omega_using [hc0]), bytesAt_getD _ _ hu, addr_add, prevEq hc0]
  -- The slots.
  have wS : ∀ j, c.slots ≤ j → j < c.slots + 6 → ∀ r ∈ [(⟨T, 8 * c.bw * cc⟩ : Region), ⟨A, 8 * c.bw * cc⟩,
      ⟨H, 8 * c.bw⟩], Region.Disjoint ⟨wordAddr B j, 8⟩ r := fun j h1 h2 r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact VG.Offset.disjoint B (.inr (by omega_using [hbuf, hbwcc, hbG, h1])) (by omega_using [hsm, hroom, h2])
        (by omega_using [hsm, hroom, hbuf, hbwcc, hbG])
    · exact (((dDS (subS (show 8 * j + 8 ≤ 8 * c.ctrSlots by simp only [Core.ctrSlots]; omega_using [hroom, h2]))).sub_left
        subA).symm)
    · exact VG.Offset.disjoint B (.inl (by simp only [Core.hiSlot]; omega_using [h2])) (by omega_using [hsm, hroom, h2])
        (by simp only [Core.hiSlot]; omega_using [hsm, hroom, hbw2])
  have saved₈ : ∀ i < 6, s₈.mem.readW (wordAddr B (c.slots + i)) 64 =
      s₀.mem.readW (wordAddr B (c.slots + i)) 64 := fun i hi6 => by
    rw [m₈, ← hi.saved i hi6]
    refine (f₇.readW (Region.contains_self _ _) (fun r hr => wS _ (by omega_using []) (by omega_using [hi6]) r (by
      simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_of_mem _ List.mem_cons_self))
      (by decide)).trans ?_
    refine (f₄.readW (Region.contains_self _ _) (hp.stk.coreFrame_disj
      (VG.Offset.disjoint_base B (by omega_using []) (by omega_using [hsm, hroom, hi6]))
      ⟨_, hp.scr.wr, VG.Offset.sub_base B (by simp only [Core.ctrSlots]; omega_using [hsm, hroom, hi6])⟩)
      (by decide)).trans ?_
    exact f₃.readW (Region.contains_self _ _) (fun r hr => wS _ (by omega_using []) (by omega_using [hi6]) r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))) (by decide)
  have fr : Frame ([⟨B, 8 * c.ctrSlots⟩, ⟨D, 8 * c.bw * n⟩] ++ stkList c (s₀.gpr .rsp)) s₀.mem s₈.mem := by
    rw [m₈]
    refine hi.frame.trans (((f₃.sub fun r hr => ⟨⟨B, 8 * c.ctrSlots⟩, List.mem_cons_self, by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact subT
      · exact subH⟩).trans
      (f₄.sub (coreFrame_sub ⟨⟨B, 8 * c.ctrSlots⟩, List.mem_cons_self, subCore⟩))).trans
      (f₇.sub fun r hr => ⟨⟨D, 8 * c.bw * n⟩, List.mem_cons_of_mem _ List.mem_cons_self, by
        simp only [List.mem_singleton] at hr; subst hr; exact subA⟩))
  have base₈ : s₈.gpr sb = B := by
    rw [o₈ _ (Ne.symm dsb) (Ne.symm lsb), g₇ _ (by decide) (by decide) (by decide) (by decide) (by decide), base₄]
  have rsp₈ : s₈.gpr .rsp = s₀.gpr .rsp := by
    rw [o₈ _ (Ne.symm dsp) (Ne.symm lsp), g₇ _ (by decide) (by decide) (by decide) (by decide) (by decide), rsp₄,
      keep₃ _ (by decide) (by decide) (by decide) (by decide), hi.rsp]
  have rd₈' : s₈.rd = s₀.rd := by rw [rd₈, h₇.rd, rd₆', hi.rd]
  have wr₈' : s₈.wr = s₀.wr := by rw [wr₈, h₇.wr, wr₆', hi.wr]
  by_cases hdone : v = cc
  · refine .inl ⟨by rw [hz, decide_eq_true hdone], base₈, rsp₈, saved₈, ?_, fr, rd₈', wr₈'⟩
    rw [show n = c.G * g + cc by omega_using [hc0, hdone]] at hdata ⊢
    exact hdata
  · have hcc : cc = c.G := by omega_using [hdone]
    have hg1 : c.G * (g + 1) = c.G * g + cc := by rw [hcc, Nat.mul_succ]
    refine .inr ⟨by rw [hz, decide_eq_false hdone], base₈, rsp₈, ready₈, saved₈, ?_, ?_,
      by omega_using [hdone, hg1], ?_, by rw [hg1]; exact hdata, fr, rd₈', wr₈'⟩
    · rw [d₈, rbx₇, addr_add, hg1, Nat.mul_add]
    · rw [l₈, left₇, r10₇, VG.Offset.ofNat_sub_ofNat (by omega_using []), hg1]; congr 1; omega_using []
    · rw [hg1]; exact chain₈

/-- The data loop. -/
theorem loop_wp (cs : BlockSpec c) (hbw : c.bw = 2) {s₀ : State} {B D : Addr} {n : Nat} {k : cs.Key}
    {iv : List Byte} (hiv : iv.length = 8 * c.bw) (hp : GPre c s₀ B D n (8 * c.bw)) {s : State}
    (hi : Inv cs s₀ B D n k iv 0 s) :
    WP isa (.loop c.cfbDecGroup .ne) s (Done cs s₀ B D n k iv) := by
  refine WP.loop (M := isa) (fun m s => ∃ g, m = n - c.G * g ∧ Inv cs s₀ B D n k iv g s) (fun m s hs => ?_) n s
    ⟨0, by simp, hi⟩
  obtain ⟨g, rfl, hg⟩ := hs
  refine WP.mono (group_wp cs hbw hiv hp hg) fun s' h => ?_
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨by simp [X86_64.eval, z], d⟩
  · have hG := cs.layout.G_pos
    exact .inr ⟨by simp [X86_64.eval, z], n - c.G * (g + 1),
      by have := d.lt; have := hg.lt; rw [Nat.mul_succ] at *; omega_arith, g + 1, rfl, d⟩

theorem batched_wp (cs : BlockSpec c) (hbw : c.bw = 2) {r : CtrRegs} (hr : RegsOk r) (hdn : c.dataReg ≠ r.n)
    {s₀ : State} {B P D : Addr} {n : Nat} {k : cs.Key} (hB : s₀.gpr r.scr = B) (hP : s₀.gpr r.ctr = P)
    (hD : s₀.gpr r.data = D) (hn : (s₀.gpr r.n).toNat = n) (hs : ScrIn s₀ B c.ctrSlots)
    (hwP : (⟨P, 8 * c.bw⟩ : Region) ∈ s₀.wr)
    (hwD : (⟨D, 8 * c.bw * n⟩ : Region) ∈ s₀.wr) (sPS : Region.Disjoint ⟨P, 8 * c.bw⟩ ⟨B, 8 * c.ctrSlots⟩)
    (sDS : Region.Disjoint ⟨D, 8 * c.bw * n⟩ ⟨B, 8 * c.ctrSlots⟩)
    (sPD : Region.Disjoint ⟨P, 8 * c.bw⟩ ⟨D, 8 * c.bw * n⟩)
    (fitD : D.toNat + 8 * c.bw * n ≤ 2 ^ 64) (hk : cs.KeyArgs s₀ [⟨B, 8 * c.ctrSlots⟩, ⟨P, 8 * c.bw⟩] k)
    (hstk : StkOk c s₀ := by exact Or.inl rfl) :
    WP isa (c.cfbDecryptBatched r) s₀ fun s' => (∀ x ∈ calleeSaved, s'.gpr x = s₀.gpr x) ∧
      blocksOf (8 * c.bw) s'.mem D n =
        Spec.Cfb.decrypt (cs.cipher k) (bytesAt s₀.mem P (8 * c.bw)) (blocksOf (8 * c.bw) s₀.mem D n) ∧
      bytesAt s'.mem P (8 * c.bw) = Spec.Cbc.next (bytesAt s₀.mem P (8 * c.bw)) (blocksOf (8 * c.bw) s₀.mem D n) ∧
      Frame ([⟨B, 8 * c.ctrSlots⟩, ⟨D, 8 * c.bw * n⟩, ⟨P, 8 * c.bw⟩] ++ stkList c (s₀.gpr .rsp)) s₀.mem s'.mem ∧
      s'.rd = s₀.rd ∧ s'.wr = s₀.wr := by
  have hL := cs.layout
  have hsm := hL.small
  have hroom := hL.room
  have hbw0 := hL.bw_pos
  have hbw2 := hL.bw_le
  have hN : 8 * c.ctrSlots < 2 ^ 64 := by simp only [Core.ctrSlots]; omega_arith
  have hn64 : 8 * c.bw * n ≤ 2 ^ 64 := by omega_arith
  obtain ⟨hregs, hdl⟩ := regsOk_ne cs.regs_ok
  obtain ⟨da, db, -, -, -, dsb, dsp, dk⟩ := hregs c.dataReg List.mem_cons_self
  obtain ⟨la, lb, -, -, -, lsb, lsp, lk⟩ := hregs c.leftReg (List.mem_cons_of_mem _ List.mem_cons_self)
  let H := chainAddr c B
  have subMode : Region.Sub (modeRegion c B) ⟨B, 8 * c.ctrSlots⟩ :=
    VG.Offset.sub_base B (by simp only [Core.ctrSlots]; omega_arith)
  have subH : Region.Sub ⟨H, 8 * c.bw⟩ (modeRegion c B) := VG.Offset.sub B (by simp only [Core.hiSlot]; omega_arith)
    (by simp only [Core.hiSlot]; omega_arith)
  have dPm : Region.Disjoint ⟨P, 8 * c.bw⟩ (modeRegion c B) := sPS.sub_right subMode
  -- The entry, and the IV to the chaining value.
  obtain ⟨sE, eE, bE, svE, fE, gE, rdE, wrE⟩ := entry_ok hsm hroom s₀ hB hs
  unfold Core.cfbDecryptBatched
  refine WP.seq (WP.block_append (WP.of_runBlock ⟨sE, eE, WP.mono_syms (copyN_wp (k := c.bw) (P := H)
    (Q := P) ⟨by rw [bE], by rw [gE _ hr.ctr.1, hP]; simp, by decide, Ne.symm hr.ctr.2.1,
      fun w hw => ⟨_, by rw [wrE]; exact hs.wr, by
        rw [addr_add]
        exact VG.Offset.contains_base B (by simp only [Core.hiSlot, Core.ctrSlots]; omega_arith)
          (by simp only [Core.hiSlot]; omega_arith)⟩,
      fun w hw => inRd ⟨_, by rw [wrE]; exact hwP, VG.Offset.contains_base P (by omega_arith) (by omega_arith)⟩,
      (dPm.sub_left (fun _ h => h)).symm.sub_left subH |>.symm.symm, by omega_arith⟩) fun sC hC syC => ?_⟩))
  have gC : ∀ x, x ≠ sb → x ≠ .rax → x ≠ .rbx → sC.gpr x = s₀.gpr x := fun x h1 h2 _ => by
    rw [hC.regs x h2, gE x h1]
  have memC : sC.mem = over sE.mem H (8 * c.bw) fun i => sE.mem (P + BitVec.ofNat 64 i) := hC.mem
  have fCH : Frame [⟨H, 8 * c.bw⟩] sE.mem sC.mem := by rw [memC]; exact over_frame _ _ _ _
  have fC : Frame [modeRegion c B] s₀.mem sC.mem :=
    fE.trans (fCH.sub fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact ⟨_, List.mem_singleton_self _, subH⟩)
  have mCD : ∀ i < 8 * c.bw * n, sC.mem (D + BitVec.ofNat 64 i) = s₀.mem (D + BitVec.ofNat 64 i) := fun i hi =>
    fC.bytes (R := ⟨D, 8 * c.bw * n⟩) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact sDS.sub_right subMode) hn64 hi
  have mCP : ∀ u < 8 * c.bw, sC.mem (P + BitVec.ofNat 64 u) = s₀.mem (P + BitVec.ofNat 64 u) := fun u hu =>
    fC.bytes (R := ⟨P, 8 * c.bw⟩) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact dPm) (show 8 * c.bw ≤ 2 ^ 64 by omega_arith) hu
  -- The last block to the IV.
  refine WP.seq (WP.mono_syms (cbcLastToIv_wp (m₀ := s₀.mem) hbw0 hbw2 hr (by rw [gC _ hr.ctr.1 hr.ctr.2.1 hr.ctr.2.2, hP])
    (by rw [gC _ hr.data.1 hr.data.2.1 hr.data.2.2, hD]) (by rw [gC _ hr.n.1 hr.n.2.1 hr.n.2.2, hn])
    (by rw [hC.wr, wrE]; exact hwP) (by rw [hC.wr, wrE]; exact hwD) sPD fitD mCD)
    fun sL ⟨gL, fL, ivL, rdL, wrL⟩ syL => ?_)
  have bytesP : bytesAt sC.mem P (8 * c.bw) = bytesAt s₀.mem P (8 * c.bw) :=
    bytesAt_of_getD (by simp [bytesAt]) fun u hu => by rw [mCP u hu]; exact (bytesAt_getD _ _ hu).symm
  rw [bytesP] at ivL
  obtain ⟨s₁, e₁b, dr₁, lr₁, g₁b, m₁b, rd₁b, wr₁b⟩ := ctrArgs_ok sL r hdn hdl
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁b, ?_⟩)
  have g₁a : ∀ x, x ≠ sb → x ≠ .rax → x ≠ .rbx → sL.gpr x = s₀.gpr x := fun x h1 h2 h3 => by
    rw [gL x h2 h3, gC x h1 h2 h3]
  have g₁ : ∀ x, x ≠ sb → x ≠ .rax → x ≠ .rbx → x ≠ c.dataReg → x ≠ c.leftReg → s₁.gpr x = s₀.gpr x :=
    fun x h1 h2 h3 h4 h5 => by rw [g₁b x h4 h5, g₁a x h1 h2 h3]
  have b₁ : s₁.gpr sb = B := by
    rw [g₁b _ (Ne.symm dsb) (Ne.symm lsb), gL _ (by decide) (by decide), hC.regs _ (by decide), bE]
  have rd₁ : s₁.rd = s₀.rd := by rw [rd₁b, rdL, hC.rd, rdE]
  have wr₁ : s₁.wr = s₀.wr := by rw [wr₁b, wrL, hC.wr, wrE]
  have mem₁ : s₁.mem = sL.mem := m₁b
  -- What the memory holds before the key.
  have dPH : Region.Disjoint ⟨P, 8 * c.bw⟩ ⟨H, 8 * c.bw⟩ := dPm.sub_right subH
  have sv₁ : ∀ i < 6, s₁.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.gpr (Core.savedRegs.getD i .rbx) :=
    fun i hi => by
      rw [← svE i hi, mem₁]
      refine (fL.readW (Region.contains_self _ _) (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx
        exact (sPS.sub_right (VG.Offset.sub_base B (show 8 * (c.slots + i) + 8 ≤ 8 * c.ctrSlots by
          simp only [Core.ctrSlots]; omega_arith))).symm)
        (by decide)).trans ?_
      exact fCH.readW (Region.contains_self _ _) (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx
        exact VG.Offset.disjoint B (.inl (by simp only [Core.hiSlot]; omega_arith)) (by omega_arith)
          (by simp only [Core.hiSlot]; omega_arith)) (by decide)
  have ch₁ : ∀ u < 8 * c.bw, s₁.mem (H + BitVec.ofNat 64 u) = s₀.mem (P + BitVec.ofNat 64 u) := fun u hu => by
    rw [mem₁, fL.bytes (R := ⟨H, 8 * c.bw⟩) (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact dPH.symm) (show 8 * c.bw ≤ 2 ^ 64 by omega_arith) hu,
      memC, over_at hu (by omega_arith)]
    exact fE.bytes (R := ⟨P, 8 * c.bw⟩) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact dPm) (show 8 * c.bw ≤ 2 ^ 64 by omega_arith) hu
  have kr := keyRegs_ne cs.keyRegs_ok
  have f₁' : Frame [⟨B, 8 * c.ctrSlots⟩, ⟨P, 8 * c.bw⟩] s₀.mem s₁.mem := by
    rw [mem₁]
    exact (fC.sub fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact ⟨_, List.mem_cons_self, subMode⟩).trans
      (fL.sub fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx
        exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩)
  have hk₁ : cs.KeyArgs s₁ [⟨B, 8 * c.ctrSlots⟩, ⟨P, 8 * c.bw⟩] k :=
    cs.keyArgs_congr hk (fun x hx => g₁ x (kr x hx).1 (kr x hx).2.1 (kr x hx).2.2 (fun e => dk (e ▸ hx))
      (fun e => lk (e ▸ hx))) rd₁ wr₁
      (by rw [runBlock_syms e₁b, syL, syC, runBlock_syms eE]) f₁'
  -- The key.
  refine WP.seq (WP.mono (cs.prepare_wp b₁ ⟨by rw [wr₁]; exact hs.wr, hs.fit⟩ List.mem_cons_self hk₁)
    fun s₂ ⟨ready₂, b₂, rsp₂, dr₂, lr₂, f₂, rd₂, wr₂⟩ => ?_)
  rw [show s₁.gpr .rsp = s₀.gpr .rsp from g₁ _ (by decide) (by decide) (by decide) (Ne.symm dsp) (Ne.symm lsp)] at f₂
  have keep₂ : ∀ j, c.slots ≤ j → j < c.ctrSlots →
      s₂.mem.readW (wordAddr B j) 64 = s₁.mem.readW (wordAddr B j) 64 := fun j h1 h2 =>
    f₂.readW (Region.contains_self _ _) (hstk.coreFrame_disj (VG.Offset.disjoint_base B (by omega_arith) (by omega_arith))
      ⟨_, hs.wr, VG.Offset.sub_base B (by omega_arith)⟩) (by decide)
  have wr₂' : s₂.wr = s₀.wr := by rw [wr₂, wr₁]
  have rd₂' : s₂.rd = s₀.rd := by rw [rd₂, rd₁]
  -- Any blocks?
  obtain ⟨s₃, e₃, z₃, g₃, m₃, rd₃, wr₃⟩ := testSelf_ok s₂ c.leftReg
  refine WP.seq (WP.of_runBlock ⟨s₃, e₃, ?_⟩)
  have left₃ : s₃.gpr c.leftReg = s₀.gpr r.n := by rw [g₃, lr₂, lr₁, g₁a _ hr.n.1 hr.n.2.1 hr.n.2.2]
  have hz₃ : s₃.zf = some (decide (n = 0)) := by
    rw [z₃, ← g₃, left₃]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    exact ⟨fun h => by rw [← hn, h]; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [hn, h]; rfl)⟩
  have mem₃ : s₃.mem = s₂.mem := m₃
  have b₃ : s₃.gpr sb = B := by rw [g₃, b₂]
  have rsp₃ : s₃.gpr .rsp = s₀.gpr .rsp := by
    rw [g₃, rsp₂, g₁ _ (by decide) (by decide) (by decide) (Ne.symm dsp) (Ne.symm lsp)]
  have rd₃' : s₃.rd = s₀.rd := by rw [rd₃, rd₂']
  have wr₃' : s₃.wr = s₀.wr := by rw [wr₃, wr₂']
  let iv := bytesAt s₀.mem P (8 * c.bw)
  have hiv : iv.length = 8 * c.bw := by simp [iv, bytesAt]
  have hp : GPre c s₃ B D n (8 * c.bw) :=
    ⟨⟨by rw [wr₃']; exact hs.wr, hs.fit⟩, by rw [wr₃']; exact hwD, sDS, fitD, hstk.congr rsp₃ wr₃'⟩
  -- The groups.
  refine WP.seq (WP.mono (M := isa) (Q := Done cs s₃ B D n k iv)
    (WP.ite (decide (n = 0)) (by simp [X86_64.eval, hz₃]) (fun h0 => ?_) (fun h0 => ?_)) fun s₄ d₄ => ?_)
  · have hn0 : n = 0 := by simpa using h0
    exact WP.block_nil ⟨b₃, rfl, fun _ _ => rfl, fun i hi' => by rw [hn0, Nat.mul_zero] at hi'; omega_arith, Frame.refl _ _, rfl, rfl⟩
  · have hn0 : n ≠ 0 := by simpa using h0
    refine loop_wp cs hbw hiv hp ⟨b₃, rfl, cs.ready_frame ready₂ (by rw [mem₃]; exact Frame.refl [] _)
        (fun _ h => by simp at h) ⟨fun _ h => by simp at h, rd₃, wr₃, runBlock_syms e₃⟩ (fun r _ => by rw [g₃]), fun _ _ => rfl, ?_, ?_, by omega_arith, fun u hu => ?_,
      fun i _ => by rw [ite_eq_right (by omega_arith)], Frame.refl _ _, rfl, rfl⟩
    · rw [g₃, dr₂, dr₁, g₁a _ hr.data.1 hr.data.2.1 hr.data.2.2, hD]; simp
    · rw [left₃, Nat.mul_zero, Nat.sub_zero, ← hn]; simp
    · have dH : Region.Disjoint ⟨chainAddr c B, 8 * c.bw⟩ (coreRegion c B) :=
        VG.Offset.disjoint_base B (by simp only [Core.hiSlot]; omega_arith) (by simp only [Core.hiSlot]; omega_arith)
      rw [Nat.mul_zero, cbcPrev, ite_eq_left rfl, mem₃,
        f₂.bytes (R := ⟨chainAddr c B, 8 * c.bw⟩) (hstk.coreFrame_disj dH ⟨_, hs.wr, VG.Offset.sub_base B
          (by simp only [Core.hiSlot, Core.ctrSlots]; omega_arith)⟩) (show 8 * c.bw ≤ 2 ^ 64 by omega_arith) hu,
        ch₁ u hu, bytesAt_getD _ _ hu]
  -- The exit.
  have hsv : ∀ i < 6, Core.savedRegs.getD i .rbx ≠ sb := by decide
  have hinj : ∀ i < 6, ∀ j < 6, Core.savedRegs.getD i .rbx = Core.savedRegs.getD j .rbx → i = j := by decide
  obtain ⟨s₅, e₅, v₅, o₅, m₅, rd₅, wr₅⟩ := loads_ok (B := B) c.slots (fun i => Core.savedRegs.getD i .rbx) 6 s₄
    d₄.base hsv hinj (fun i hi' => by
      rw [d₄.rd, d₄.wr, rd₃', wr₃']
      exact inRd (slot_wr hs.wr hN (by simp only [Core.ctrSlots]; omega_arith)))
  have subCore : Region.Sub (coreRegion c B) ⟨B, 8 * c.ctrSlots⟩ :=
    Region.sub_prefix (by simp only [Core.ctrSlots]; omega_arith)
  have f₄ : Frame ([⟨B, 8 * c.ctrSlots⟩, ⟨D, 8 * c.bw * n⟩, ⟨P, 8 * c.bw⟩] ++ stkList c (s₀.gpr .rsp))
      s₀.mem s₄.mem := by
    refine (((f₁'.mono fun x hx => List.mem_append_left _ hx).trans
      (f₂.sub (coreFrame_sub (rs := [⟨B, 8 * c.ctrSlots⟩, ⟨P, 8 * c.bw⟩]) ⟨_, List.mem_cons_self, subCore⟩))).mono
      fun x hx => by
        rcases List.mem_append.mp hx with hx | hx
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
        · exact List.mem_append_right _ hx).trans ?_
    rw [← mem₃]
    exact d₄.frame.mono fun x hx => by
      rw [rsp₃] at hx
      rcases List.mem_append.mp hx with hx | hx
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ List.mem_cons_self
      · exact List.mem_append_right _ hx
  refine WP.of_runBlock ⟨s₅, e₅, fun x hx => ?_, ?_, ?_, by rw [m₅]; exact f₄, by rw [rd₅, d₄.rd, rd₃'],
    by rw [wr₅, d₄.wr, wr₃']⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hx
    have hsaved : ∀ i < 6, s₅.gpr (Core.savedRegs.getD i .rbx) = s₀.gpr (Core.savedRegs.getD i .rbx) :=
      fun i hi' => by
        rw [v₅ i hi', d₄.saved i hi', mem₃, keep₂ _ (by omega_arith) (by simp only [Core.ctrSlots]; omega_arith), sv₁ i hi']
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsaved 0 (by decide)
    · exact hsaved 1 (by decide)
    · rw [o₅ _ (fun i hi' => by revert i; decide), d₄.rsp, rsp₃]
    · exact hsaved 2 (by decide)
    · exact hsaved 3 (by decide)
    · exact hsaved 4 (by decide)
    · exact hsaved 5 (by decide)
  · rw [m₅, of_dinv (cs.cipher_len k) d₄.data, mem₃,
      blocksOf_frame f₂ (by omega_arith) (hstk.coreFrame_disj (sDS.sub_right subCore) ⟨_, hwD, fun _ h => h⟩),
      blocksOf_frame f₁' (by omega_arith) (fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact sDS
        · exact sPD.symm)]
  · -- The IV: written before the blocks, and not since.
    rw [m₅]
    have fIv : ∀ u < 8 * c.bw, s₄.mem (P + BitVec.ofNat 64 u) = s₁.mem (P + BitVec.ofNat 64 u) := fun u hu => by
      have pStk := hstk.disj (R := ⟨P, 8 * c.bw⟩) ⟨_, hwP, fun _ h => h⟩
      rw [d₄.frame.bytes (R := ⟨P, 8 * c.bw⟩) (fun x hx => by
          rw [rsp₃] at hx
          rcases List.mem_append.mp hx with hx | hx
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with rfl | rfl
            · exact sPS
            · exact sPD
          · exact pStk x hx) (show 8 * c.bw ≤ 2 ^ 64 by omega_arith) hu, mem₃]
      exact f₂.bytes (R := ⟨P, 8 * c.bw⟩) (coreFrame_disj (sPS.sub_right subCore) pStk)
        (show 8 * c.bw ≤ 2 ^ 64 by omega_arith) hu
    have e : bytesAt s₄.mem P (8 * c.bw) = bytesAt sL.mem P (8 * c.bw) :=
      bytesAt_of_getD (by simp [bytesAt]) fun u hu => by rw [fIv u hu, mem₁]; exact (bytesAt_getD _ _ hu).symm
    rw [e]
    exact ivL

end VG.Proof.Modes.X86_64.CfbDec
