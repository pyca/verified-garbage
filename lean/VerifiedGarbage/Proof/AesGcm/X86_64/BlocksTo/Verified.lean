module

import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksVerifiedP
public import VerifiedGarbage.Spec.Gcm.OutOfPlace
public import VerifiedGarbage.Proof.Gcm.OutOfPlaceContract
public import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Contract
public import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Piece
public import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Call
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.SpecTo
import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb
public import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Mid
import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Piece
meta import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Mid
meta import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Call
meta import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Impl.AesGcm.X86_64
meta import VerifiedGarbage.Impl.AesGcm.X86_64.BlocksTo
meta import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksVerified
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.TCB.X86_64.Isa
meta import VerifiedGarbage.TCB.X86_64.State
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Gcm.Be64
meta import VerifiedGarbage.Impl.Gcm.X86_64
meta import VerifiedGarbage.Impl.Gcm.X86_64.Pclmul
meta import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Cmp
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Fn
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Gcm.Be64
meta import VerifiedGarbage.Proof.Gcm.Bits
meta import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.AesGcm.X86_64.Run
import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Full
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.SpecTo
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Full
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Run
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Env
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Gcm.Split
import VerifiedGarbage.Proof.Gcm.Ctr
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.AesGcm.X86_64.Mask
public import VerifiedGarbage.Impl.AesGcm.X86_64.BlocksTo
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.X86_64.Taint
public import VerifiedGarbage.Spec.Aes
meta import VerifiedGarbage.Proof.Framework.X86_64.Frame
meta import VerifiedGarbage.Proof.Gcm.Split
meta import VerifiedGarbage.Proof.Gcm.Ctr
meta import VerifiedGarbage.Proof.Gcm.Stream
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Mask
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Cmac.Stream
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Spec.Aes
public import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Stitch
import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Stitch
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
meta import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
meta import VerifiedGarbage.Proof.Aes.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.TacticTemplate

/-! ### `AesGcm.X86_64.BlocksTo.Stitch`, which this module and modules that import it used -/

section

/-!
# AES-GCM on whole blocks out of place, x86-64: the first `16 ⌊n / 16⌋` blocks in one pass

Untrusted: everything here is checked by Lean. After the entry, if there are
at least 16 blocks, `r9` becomes `16 ⌊n / 16⌋` and `r11` the working space
(`split_ok`), which with the output in `r10` and the other arguments still in
their registers meets what the out-of-place interleaved loops need
(`spreTo_of`); their result is `Mid` with `q = 16 ⌊n / 16⌋`
(`mid_of_postTo`). With fewer, `q = 0` (`stitch_ok`); then `rest`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.BlocksTo

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.BlocksTo
open VG.Proof.Gcm.X86_64.Stitch (CtxMode SPreTo EPostTo StitchToOkM)
open VG.Spec.Gcm (Block blockAt blocksAt ctxCiph ctxH ctr32 ghashFrom inc32)

/-- The registers the entry leaves as they were. -/
def argRegs : List Reg := [.rdi, .rsi, .rdx, .rcx, .r8, .rsp]

theorem contains_prefix (a : Addr) {k L : Nat} (h : k ≤ L) : (⟨a, L⟩ : Region).Contains a k := by
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; exact h

section
variable {aligned : Bool} {M : CtxMode} {s : State} (hp : BT M s)
include hp

/-- `r9 := 16 ⌊r9 / 16⌋` and `r11` at the powers. -/
theorem split_ok {s₁ : State} (h9 : s₁.gpr .r9 = s.gpr .r9) (h11 : s₁.gpr .r11 = S s) :
    WP isa (.block (([.mov .rax (.reg .r9), .alu .and .rax (imm 15), .alu .sub .r9 (.reg .rax)] : List Instr) ++
      Blocks.scratchSetup aligned)) s₁ fun s₃ =>
      s₃.gpr .r9 = BitVec.ofNat 64 (n s - n s % 16) ∧ s₃.gpr .r11 = S s + BitVec.ofNat 64 (AlignedScratch.offset aligned (S s)) ∧
      (∀ r, r ≠ .rax → r ≠ .r9 → r ≠ .r11 → s₃.gpr r = s₁.gpr r) ∧
      s₃.mem = s₁.mem ∧ s₃.rd = s₁.rd ∧ s₃.wr = s₁.wr := by
  exact WP.mono (Blocks.split_ok (aligned := aligned) (s := s) h9) fun st ⟨a, b, c, d, e, f⟩ =>
    ⟨a, by rw [b, h11]; exact AlignedScratch.ptr_eq aligned (S s) hp.w_s, c, d, e, f⟩

/-- What the out-of-place loops need, from the arguments in their
registers, `r9 = 16 ⌊n / 16⌋`, the output in `r10` and the working space in
`r11`. -/
theorem spreTo_of {q : Nat} {s₃ : State} (hq16 : 16 ≤ q) (hqle : q ≤ n s) (h9 : s₃.gpr .r9 = BitVec.ofNat 64 q)
    (hg : ∀ r ∈ argRegs, s₃.gpr r = s.gpr r) (h10 : s₃.gpr .r10 = Dst s)
    (h11 : s₃.gpr .r11 = S s + BitVec.ofNat 64 (AlignedScratch.offset aligned (S s))) (hrd : s₃.rd = s.rd)
    (hwr : s₃.wr = s.wr) (hf₃ : Frame [kR' s] s.mem s₃.mem) : SPreTo M s₃ := by
  obtain hn : n s < 2 ^ 64 := (s.gpr .r9).isLt
  obtain hq : (s₃.gpr .r9).toNat = q := by rw [h9, toNat_ofNat_of_lt (by omega_using [hqle, hn])]
  obtain hqn : 16 * q ≤ n s * 16 := by omega_using [hqle]
  obtain pd : Region.Sub ⟨Dst s, 16 * q⟩ (dR s) := Region.sub_prefix hqn
  obtain pr : Region.Sub ⟨Src s, 16 * q⟩ (srcR s) := Region.sub_prefix hqn
  obtain ps : Region.Sub ⟨S s + BitVec.ofNat 64 (AlignedScratch.offset aligned (S s)), 1024⟩ (sR s) := Offset.sub_base _ (by have := AlignedScratch.offset_bounds aligned (S s); omega_using [this])
  have hws := hp.w_s
  obtain ts : (S s + BitVec.ofNat 64 (AlignedScratch.offset aligned (S s))).toNat = (S s).toNat + AlignedScratch.offset aligned (S s) := by
    obtain ho := AlignedScratch.offset_bounds aligned (S s)
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [ho] : AlignedScratch.offset aligned (S s) < 2^64), Nat.mod_eq_of_lt (by omega_using [hws, ho])]
  obtain ek : s₃.gpr .rdi = K s := hg _ (by simp [argRegs])
  obtain er : s₃.gpr .rsi = s.gpr .rsi := hg _ (by simp [argRegs])
  obtain ec : s₃.gpr .rdx = C s := hg _ (by simp [argRegs])
  obtain ey : s₃.gpr .rcx = Y s := hg _ (by simp [argRegs])
  obtain ed : s₃.gpr .r8 = Src s := hg _ (by simp [argRegs])
  have rd : s.rd = [kR M s, srcR s, aR s] := hp.rd
  have wr : s.wr = wR s := hp.wr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩ <;>
  simp only [Gcm.X86_64.Stitch.nr, Gcm.X86_64.Stitch.nb, Gcm.X86_64.Stitch.kp,
    Gcm.X86_64.Stitch.cp, Gcm.X86_64.Stitch.yp, Gcm.X86_64.Stitch.sp, Gcm.X86_64.Stitch.op, Gcm.X86_64.Stitch.pp,
    Gcm.X86_64.Stitch.cR, Gcm.X86_64.Stitch.yR, Gcm.X86_64.Stitch.sR, Gcm.X86_64.Stitch.oR,
    Gcm.X86_64.Stitch.pR, ek, er, ec, ey, ed, h10, h11, hq, hrd, hwr]
  exacts [hp.rounds, by omega_using [hq16], ⟨kR M s, by rw [rd]; simp, Region.contains_self _ _⟩,
    ⟨cR s, by rw [wr]; simp, Region.contains_self _ _⟩, ⟨yR s, by rw [wr]; simp, Region.contains_self _ _⟩,
    ⟨srcR s, by rw [rd]; simp, contains_prefix _ hqn⟩, ⟨dR s, by rw [wr]; simp, contains_prefix _ hqn⟩,
    ⟨sR s, by rw [wr]; simp, Offset.contains_base _ (by have := AlignedScratch.offset_bounds aligned (S s); omega_using [this]) (by have := AlignedScratch.offset_bounds aligned (S s); omega_using [ts])⟩,
    hp.k_c, hp.k_y, hp.k_d.sub_right pd, hp.k_s.sub_right ps,
    hp.c_r.symm.sub_left pr, hp.y_r.symm.sub_left pr, (hp.r_d.sub_left pr).sub_right pd,
    (hp.r_s.sub_left pr).sub_right ps, hp.c_d.symm.sub_left pd, hp.y_d.symm.sub_left pd,
    (hp.d_s.sub_left pd).sub_right ps, hp.c_s.symm.sub_left ps, hp.y_s.symm.sub_left ps, hp.c_y,
    by have := hp.w_r; omega_using [hqle, this], by have := hp.w_d; omega_using [hqle, this], hp.w_k, by rw [ts]; have := AlignedScratch.offset_bounds aligned (S s); omega_using [hws, this],
    M.frame hf₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.k_s.sub_right kR'_sub) hp.w_k hp.ok]

/-- `Mid` after the out-of-place loops, from what they leave. -/
theorem mid_of_postTo {q k : Nat} {s₃ s₄ : State} (hqn : q ≤ n s) (h9 : s₃.gpr .r9 = BitVec.ofNat 64 q)
    (hg : ∀ r ∈ argRegs, s₃.gpr r = s.gpr r) (hcs : ∀ r ∈ calleeSaved, s₃.gpr r = s.gpr r)
    (h10 : s₃.gpr .r10 = Dst s) (h11 : s₃.gpr .r11 = S s + BitVec.ofNat 64 (AlignedScratch.offset aligned (S s)))
    (hrd : s₃.rd = s.rd) (hwr : s₃.wr = s.wr) (hkp : Kept s k s₃.mem) (hf₃ : Frame [kR' s] s.mem s₃.mem)
    (P : EPostTo s₃ s₄) : Mid s q k s₄ := by
  obtain hn : n s < 2 ^ 64 := (s.gpr .r9).isLt
  have data := P.data
  have ctr := P.ctr
  have frame := P.frame
  have y := P.y
  obtain hq9 : (s₃.gpr .r9).toNat = q := by rw [h9, toNat_ofNat_of_lt (by omega_using [hqn, hn])]
  obtain ek : s₃.gpr .rdi = K s := hg _ (by simp [argRegs])
  obtain er : s₃.gpr .rsi = s.gpr .rsi := hg _ (by simp [argRegs])
  obtain ec : s₃.gpr .rdx = C s := hg _ (by simp [argRegs])
  obtain ey : s₃.gpr .rcx = Y s := hg _ (by simp [argRegs])
  obtain ed : s₃.gpr .r8 = Src s := hg _ (by simp [argRegs])
  simp only [Gcm.X86_64.Stitch.cR, Gcm.X86_64.Stitch.yR, Gcm.X86_64.Stitch.oR, Gcm.X86_64.Stitch.pR,
    Gcm.X86_64.Stitch.cp, Gcm.X86_64.Stitch.yp, Gcm.X86_64.Stitch.op, Gcm.X86_64.Stitch.pp,
    Gcm.X86_64.Stitch.nb, ec, ey, h10, h11, hq9] at frame
  simp only [Gcm.X86_64.Stitch.op, Gcm.X86_64.Stitch.sp, Gcm.X86_64.Stitch.nb, Gcm.X86_64.Stitch.cb,
    Gcm.X86_64.Stitch.cp, Gcm.X86_64.Stitch.ciph, Gcm.X86_64.Stitch.sch, Gcm.X86_64.Stitch.nr,
    Gcm.X86_64.Stitch.kp, ek, er, ec, ed, h10, hq9] at data
  simp only [Gcm.X86_64.Stitch.cp, Gcm.X86_64.Stitch.cb, Gcm.X86_64.Stitch.nb, ec, hq9] at ctr
  simp only [Gcm.X86_64.Stitch.yp, Gcm.X86_64.Stitch.hk, Gcm.X86_64.Stitch.y₀, Gcm.X86_64.Stitch.kp,
    Gcm.X86_64.Stitch.op, Gcm.X86_64.Stitch.nb, ey, ek, h10, hq9] at y
  obtain kd : ∀ r ∈ [kR' s], (kR M s).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.k_s.sub_right kR'_sub
  obtain hRb : 16 * (R s + 1) ≤ 256 := by rcases hp.rounds with h | h | h <;> simp only [R, h] <;> decide
  obtain eK : Spec.Aes.bytesAt s₃.mem (K s) (16 * (R s + 1)) = Spec.Aes.bytesAt s.mem (K s) (16 * (R s + 1)) :=
    bytesAt_frame hf₃ (fun r hr => (kd r hr).sub_left (Region.sub_prefix (Nat.le_trans hRb M.ge)))
      (by have := hp.w_k; have := M.ge; omega_using [hRb])
  obtain eH : blockAt s₃.mem (K s + 240) = hk s :=
    block_kR' hf₃ ((hp.k_s.sub_right kR'_sub).sub_left (Offset.sub_base (d := 240) _ (by have := M.ge; omega_using [this])))
  obtain eC : blockAt s₃.mem (C s) = cb s := block_kR' hf₃ (kR'_disj hp _ (by simp)).symm
  obtain eY : blockAt s₃.mem (Y s) = y₀ s := block_kR' hf₃ (kR'_disj hp _ (by simp)).symm
  obtain pr : Region.Sub ⟨Src s, 16 * q⟩ (srcR s) := Region.sub_prefix (by omega_using [hqn])
  obtain eS : blocksAt s₃.mem (Src s) q = blocksAt s.mem (Src s) q := blocksAt_frame hf₃ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (hp.r_s.sub_left pr).sub_right kR'_sub)
    (by have := hp.w_r; omega_using [hqn, this])
  rw [eK, eC, eS] at data
  rw [eC] at ctr
  rw [eH, eY, data] at y
  obtain pd : Region.Sub ⟨Dst s, 16 * q⟩ (dR s) := Region.sub_prefix (by omega_using [hqn])
  obtain sk : Region.Disjoint (kR' s) ⟨S s + BitVec.ofNat 64 (AlignedScratch.offset aligned (S s)), 1024⟩ :=
    Offset.base_disjoint _ (by have := AlignedScratch.offset_bounds aligned (S s); omega_using [this]) (by have := hp.w_s; have := AlignedScratch.offset_bounds aligned (S s); omega_using [this])
  obtain fk : ∀ r ∈ [cR s, yR s, (⟨Dst s, 16 * q⟩ : Region), (⟨S s + BitVec.ofNat 64 (AlignedScratch.offset aligned (S s)), 1024⟩ : Region)],
      (kR' s).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact kR'_disj hp _ (by simp)
    · exact kR'_disj hp _ (by simp)
    · exact (kR'_disj hp (dR s) (by simp)).sub_right pd
    · exact sk
  obtain fw : Frame (wR s) s.mem s₄.mem := by
    refine (frame_kR' hf₃).trans (frame.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨cR s, by simp, fun _ h => h⟩
    · exact ⟨yR s, by simp, fun _ h => h⟩
    · exact ⟨dR s, by simp, pd⟩
    · exact ⟨sR s, by simp, Offset.sub_base _ (by have := AlignedScratch.offset_bounds aligned (S s); omega_using [this])⟩
  refine ⟨hqn, ?_, fun r hr => ?_, P.rd.trans hrd, P.wr.trans hwr, hkp.frame frame fk, fw, data, ctr, y⟩
  · rw [P.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hg _ (by simp [argRegs])
  · have hr' : r ≠ .rax ∧ r ≠ .rdx ∧ r ≠ .r8 ∧ r ≠ .r9 ∧ r ≠ .r10 := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [P.gpr r hr'.1 hr'.2.1 hr'.2.2.1 hr'.2.2.2.1 hr'.2.2.2.2]; exact hcs r hr

omit hp in
/-- `cmp r9, 16`. -/
theorem cmp16_ok {s₁ : State} (h9 : s₁.gpr .r9 = s.gpr .r9) :
    WP isa (.block [.alu .cmp .r9 (imm 16)]) s₁ fun s₂ => s₂.gpr = s₁.gpr ∧ s₂.mem = s₁.mem ∧
      s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr ∧ s₂.cf = some (decide (n s < 16)) := by
  obtain e16 : BitVec.signExtend 64 (BitVec.ofNat 32 16) = 16 := by decide
  apply WP.of_runBlock
  simp only [imm, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags,
    isa, e16, h9, Option.bind_some, Option.some.injEq, exists_eq_left']
  simp

/-- The interleaved part, from the state after the entry. -/
theorem stitch_ok {piece : Prog isa} (hpiece : StitchToOkM M piece)
    {s₁ : State} (h11 : s₁.gpr .r11 = S s) (h10 : s₁.gpr .r10 = Dst s)
    (hg : ∀ r, r ≠ .r11 → r ≠ .r10 → s₁.gpr r = s.gpr r)
    (hk : Kept s 0 s₁.mem) (hf : Frame [kR' s] s.mem s₁.mem) (hrd : s₁.rd = s.rd) (hwr : s₁.wr = s.wr) :
    WP isa (stitchPart piece aligned) s₁ (Mid s (n s - n s % 16) 0) := by
  refine WP.seq (WP.mono (cmp16_ok (hg _ (by decide) (by decide))) fun s₂ ⟨g₂, m₂, rd₂, wr₂, cf₂⟩ => ?_)
  refine WP.ite (decide (n s < 16)) (by simp only [eval, cf₂]) (fun h => ?_) (fun h => ?_)
  · have h0 : n s - n s % 16 = 0 := by simp at h; omega_using [h]
    rw [h0]
    refine WP.block_nil (mid_entry hp (by rw [g₂]; exact hg _ (by decide) (by decide))
      (fun r hr => by rw [g₂]; exact hg r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr))
      (by rw [m₂]; exact hk) (by rw [m₂]; exact hf) (rd₂.trans hrd) (wr₂.trans hwr))
  · have h16 : 16 ≤ n s := by simp at h; omega_using [h]
    refine WP.seq (WP.mono (split_ok hp (s := s) (s₁ := s₂) (by rw [g₂]; exact hg _ (by decide) (by decide))
      (by rw [g₂, h11])) fun s₃ ⟨h9, h11₃, g₃, m₃, rd₃, wr₃⟩ => ?_)
    obtain h10₃ : s₃.gpr .r10 = Dst s := by rw [g₃ _ (by decide) (by decide) (by decide), g₂, h10]
    obtain keepR : ∀ r, r ≠ .rax → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → s₃.gpr r = s.gpr r := fun r a b c d => by
      rw [g₃ r a b d, g₂, hg r d c]
    obtain ga : ∀ r ∈ argRegs, s₃.gpr r = s.gpr r := fun r hr => by
      simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact keepR _ (by decide) (by decide) (by decide) (by decide)
    obtain gc : ∀ r ∈ calleeSaved, s₃.gpr r = s.gpr r := fun r hr => by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact keepR _ (by decide) (by decide) (by decide) (by decide)
    obtain rd₃' : s₃.rd = s.rd := rd₃.trans (rd₂.trans hrd)
    obtain wr₃' : s₃.wr = s.wr := wr₃.trans (wr₂.trans hwr)
    obtain hk₃ : Kept s 0 s₃.mem := by rw [m₃, m₂]; exact hk
    obtain hf₃ : Frame [kR' s] s.mem s₃.mem := by rw [m₃, m₂]; exact hf
    obtain hm : Gcm.X86_64.Stitch.nb s₃ % 16 = 0 := by
      obtain hn : n s < 2 ^ 64 := (s.gpr .r9).isLt
      simp only [Gcm.X86_64.Stitch.nb, h9, toNat_ofNat_of_lt (show n s - n s % 16 < 2 ^ 64 by omega_using [hn])]; omega_using []
    exact WP.mono (hpiece s₃ (spreTo_of hp (by omega_using [h16]) (by omega_using []) h9 ga h10₃ h11₃ rd₃' wr₃' hf₃) hm) fun s₄ hP =>
      mid_of_postTo hp (by omega_using []) h9 ga gc h10₃ h11₃ rd₃' wr₃' hk₃ hf₃ hP

end

end VG.Proof.AesGcm.X86_64.BlocksTo

end

end

/-! ### `AesGcm.X86_64.BlocksTo.Tail`, which this module and modules that import it used -/

section

/-! ### `AesGcm.X86_64.BlocksTo.Copy`, which this module and modules that import it used -/

section

/-!
# AES-GCM out of place on x86-64: copying blocks (`BlocksTo.copyBlocks`)

Untrusted: everything here is checked by Lean. `copyBlocks` copies `k ≥ 1`
blocks from `rsi` to `rdi`, 16 bytes at a time through `xmm0`, with the
index in `r10` and the blocks left in `rcx` (`copyBlocks_wp`); the buffers do
not overlap.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.BlocksTo

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.BlocksTo VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac.Stream (bytesAt_append)

/-- What the loop needs of the state: `k` blocks at `Sp` to copy to `Dp`. -/
structure CopyPre (s : State) (Sp Dp : Addr) (k : Nat) : Prop where
  rsi : s.gpr .rsi = Sp
  rdi : s.gpr .rdi = Dp
  rcx : s.gpr .rcx = BitVec.ofNat 64 k
  pos : 1 ≤ k
  lt : 16 * k < 2 ^ 64
  rd : Covers [⟨Sp, 16 * k⟩] (s.rd ++ s.wr)
  wr : Covers [⟨Dp, 16 * k⟩] s.wr
  disj : (⟨Sp, 16 * k⟩ : Region).Disjoint ⟨Dp, 16 * k⟩

theorem copyStep_ok (s : State) {Sp Dp : Addr} {j w : Nat} (hs : s.gpr .rsi = Sp) (hd : s.gpr .rdi = Dp)
    (h10 : s.gpr .r10 = BitVec.ofNat 64 j) (hcx : s.gpr .rcx = BitVec.ofNat 64 w)
    (rq : InRegions (s.rd ++ s.wr) (Sp + BitVec.ofNat 64 j) 16) (wq : InRegions s.wr (Dp + BitVec.ofNat 64 j) 16) :
    ∃ s', runBlock isa [.movdquLoad .xmm0 srcB, .movdquStore dstB .xmm0, .alu .add .r10 (imm 16),
        .alu .sub .rcx (imm 1)] s = some s' ∧
      s'.mem = s.mem.writeW (Dp + BitVec.ofNat 64 j) (s.mem.readW (Sp + BitVec.ofNat 64 j) 128) ∧
      s'.gpr .r10 = BitVec.ofNat 64 j + 16 ∧ s'.gpr .rcx = BitVec.ofNat 64 w - 1 ∧
      s'.zf = some (BitVec.ofNat 64 w - 1 == 0) ∧
      (∀ r, r ≠ .r10 → r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e₁ : s.gpr .rsi + s.gpr .r10 * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 = Sp + BitVec.ofNat 64 j := by
    rw [hs, h10, BitVec.mul_one]; simp
  have e₂ : s.gpr .rdi + s.gpr .r10 * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 = Dp + BitVec.ofNat 64 j := by
    rw [hd, h10, BitVec.mul_one]; simp
  refine ⟨_, by mrun [srcB, dstB, e₁, e₂, rq, wq], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, mem_setXmm, xmm_setXmm', ite_true]
  · simp [gpr_setReg, gpr_setXmm, h10]
  · simp [gpr_setReg, gpr_setXmm, hcx]
  · simp [gpr_setReg, gpr_setXmm, hcx]
  · intro r h₁ h₂; simp [gpr_setReg, gpr_setXmm, h₁, h₂]
  all_goals rfl

/-- What the loop keeps: the first `j` bytes copied. -/
structure CInv (s t : State) (Sp Dp : Addr) (j : Nat) : Prop where
  r10 : t.gpr .r10 = BitVec.ofNat 64 j
  mem : t.mem = writeBytes s.mem Dp (bytesAt s.mem Sp j)
  keep : ∀ r, r ≠ .r10 → r ≠ .rcx → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr

/-- The block at `Sp + j` is not in the bytes copied so far. -/
theorem CInv.readW {s t : State} {Sp Dp : Addr} {j L : Nat} (h : CInv s t Sp Dp j)
    (hd : (⟨Sp, L⟩ : Region).Disjoint ⟨Dp, L⟩) (hj : j + 16 ≤ L) (hL : L < 2 ^ 64) :
    t.mem.readW (Sp + BitVec.ofNat 64 j) 128 = s.mem.readW (Sp + BitVec.ofNat 64 j) 128 := by
  refine Mem.readW_congr fun k hk => ?_
  rw [h.mem]
  refine (writeBytes_frame s.mem Dp (bytesAt s.mem Sp j) (R := ⟨Dp, j⟩)
    (by rw [Proof.Cmac.bytesAt_length]; exact Region.contains_self _ _)) _ fun r hr hcon => ?_
  simp only [List.mem_singleton] at hr; subst hr
  simp only [Offset.add_add] at hcon
  exact hd _ (Offset.contains_base Sp (show j + k + 1 ≤ L by omega_using [hj, hk]) (by omega_using [hj, hL, hk]))
    (Region.sub_prefix (show j ≤ L by omega_using [hj]) _ hcon)

theorem copyBlocks_wp (s : State) {Sp Dp : Addr} {k : Nat} (h : CopyPre s Sp Dp k) :
    WP isa copyBlocks s fun s' => s'.mem = writeBytes s.mem Dp (bytesAt s.mem Sp (16 * k)) ∧
      (∀ r, r ≠ .r10 → r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, r10₁, g₁⟩ : ∃ s₁, runBlock isa [.mov32 .r10 (imm 0)] s = some s₁ ∧
      s₁.gpr .r10 = BitVec.ofNat 64 0 ∧ s₁ = s.setReg .r10 (BitVec.setWidth 64 (BitVec.ofNat 32 0)) :=
    ⟨_, by simp only [imm, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
      State.setReg32], by simp [gpr_setReg], rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  subst g₁
  have hL := h.lt
  refine WP.loop (M := isa) (c := .ne)
    (fun (w : Nat) (t : State) => ∃ i, w = k - i ∧ i < k ∧ CInv s t Sp Dp (16 * i) ∧
      t.gpr .rcx = BitVec.ofNat 64 (k - i)) ?_ (k - 0) _
    ⟨0, rfl, h.pos, ⟨r10₁, by simp [bytesAt, writeBytes_nil, mem_setReg], fun r h₁ h₂ => by simp [gpr_setReg, h₁],
      rfl, rfl⟩, by simp [gpr_setReg, h.rcx]⟩
  rintro w t ⟨i, rfl, hi, ht, hcx⟩
  have hin : 16 * i + 16 ≤ 16 * k := by omega_using [hi]
  have cov (rs : List Region) (P : Addr) (hc : Covers [⟨P, 16 * k⟩] rs) : InRegions rs (P + BitVec.ofNat 64 (16 * i)) 16 :=
    hc _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base P hin (by omega_using [hL, hi])⟩
  obtain ⟨t', run', mem', r10', rcx', zf', g', rd', wr'⟩ := copyStep_ok t (Sp := Sp) (Dp := Dp) (j := 16 * i)
    (w := k - i) (by rw [ht.keep _ (by decide) (by decide), h.rsi]) (by rw [ht.keep _ (by decide) (by decide), h.rdi])
    ht.r10 hcx (by rw [ht.rd, ht.wr]; exact cov _ _ h.rd) (by rw [ht.wr]; exact cov _ _ h.wr)
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hb : (List.range 16).map (fun j => (s.mem.readW (Sp + BitVec.ofNat 64 (16 * i)) 128).extractLsb' (8 * j) 8) =
      bytesAt s.mem (Sp + BitVec.ofNat 64 (16 * i)) 16 := by
    simp only [bytesAt]
    refine List.map_congr_left fun j hj => ?_
    rw [List.mem_range] at hj
    rw [← Mem.extractLsb'_read s.mem _ (n := 16) hj]
    rfl
  have hmem : t'.mem = writeBytes s.mem Dp (bytesAt s.mem Sp (16 * (i + 1))) := by
    rw [mem', ht.readW h.disj hin (by omega_using [hL]), ht.mem, writeW_eq_writeBytes, hb,
      show 16 * (i + 1) = 16 * i + 16 by omega_using [], bytesAt_append,
      ← writeBytes_append _ _ _ _ (by simp [Proof.Cmac.bytesAt_length]; omega_using [hL, hi]), Proof.Cmac.bytesAt_length]
  have hsub : BitVec.ofNat 64 (k - i) - 1 = BitVec.ofNat 64 (k - (i + 1)) := by
    rw [show k - i = (k - (i + 1)) + 1 by omega_using [hi], ← succ_ofNat, BitVec.add_sub_cancel]
  have hcx' : t'.gpr .rcx = BitVec.ofNat 64 (k - (i + 1)) := by rw [rcx', hsub]
  have hz : t'.zf = some (decide (i + 1 = k)) := by
    rw [zf', hsub]
    by_cases he : i + 1 = k
    · rw [he, Nat.sub_self]; simp
    · have : BitVec.ofNat 64 (k - (i + 1)) ≠ 0 := fun e => by
        have := congrArg BitVec.toNat e
        rw [toNat_ofNat_of_lt (by omega_using [hL])] at this; simp at this; omega_using [hi, he, this]
      rw [beq_eq_false_iff_ne.mpr this]; simp [he]
  have ht' : CInv s t' Sp Dp (16 * (i + 1)) :=
    ⟨by rw [r10', show 16 * (i + 1) = 16 * i + 16 by omega_using [], BitVec.ofNat_add]; rfl, hmem,
      fun r h₁ h₂ => by rw [g' r h₁ h₂, ht.keep r h₁ h₂], by rw [rd', ht.rd], by rw [wr', ht.wr]⟩
  by_cases he : i + 1 = k
  · left
    refine ⟨(maskBlocks_wp.eval_ne hz).trans (by simp [he]), ?_, ht'.keep, ht'.rd, ht'.wr⟩
    rw [ht'.mem, he]
  · right
    exact ⟨(maskBlocks_wp.eval_ne hz).trans (by simp [he]), k - (i + 1), by omega_using [hi], i + 1, rfl, by omega_using [hi, he], ht', hcx'⟩

end VG.Proof.AesGcm.X86_64.BlocksTo

end

end

/-!
# AES-GCM on whole blocks out of place, x86-64: the blocks left

Untrusted: everything here is checked by Lean. From `Mid s q q`, the
`n - q` blocks left, if any, are copied from the plaintext to the output
(`copyBlocks_wp`) and encrypted and hashed there by a call of
`vg_aes_gcm_encrypt_blocks` (`blkE_call`), with `scratch` pushed for it
(`tail_ok`). Counter mode and GHASH of the two parts make those of all the
blocks (`ctr32_append`, `ghashFrom_append`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.BlocksTo

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.BlocksTo VG.WriteBytes
open VG.Impl.AesGcm.X86_64.Blocks (argCtx argRounds argCtr argY argN)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Gcm (Block blockAt blocksAt ctxCiph ctxH ctr32 ghashFrom inc32 aesWith)

/-- What the function returns with. -/
def Done (s s' : State) : Prop := gprPreserved s s' ∧ Proof.AesGcm.blocksToPost s s'

section
variable {M : CtxMode} {s : State} (hp : BT M s)
include hp

/-- The output is not all of memory: the key context is apart from it. -/
theorem n16_lt : n s * 16 < 2 ^ 64 := by
  have hw := hp.w_d
  refine Nat.lt_of_not_le fun hge => hp.k_d (K s) ?_ ?_
  · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; have := M.ge; omega_arith
  · simp only [Region.Contains]
    have := (K s - Dst s).isLt
    omega_arith

/-- With nothing left, `Mid` is the end. -/
theorem done_of {q : Nat} {st : State} (h : Mid s q q st) (h0 : n s - q = 0) : Done s st := by
  obtain hq : q = n s := by have := h.q_le; omega_arith
  subst hq
  exact ⟨⟨h.saved, keep_r hp h.frame⟩, h.data, h.ctr, h.y⟩

/-- The head of `tail`: `rcx` the number of blocks left, `ZF` if none. -/
theorem tailHead_ok {q : Nat} {st : State} (h : Mid s q q st) :
    WP isa (.block [.mov .r11 (.mem (at_ .rsp 24)), .mov .rcx (.mem (at_ .r11 argN)), .alu .test .rcx (.reg .rcx)])
      st fun st' => Mid s q q st' ∧ st'.zf = some (decide (n s - q = 0)) ∧
        st'.gpr .r11 = S s ∧ st'.gpr .rcx = BitVec.ofNat 64 (n s - q) ∧ st'.mem = st.mem := by
  obtain hn : n s < 2 ^ 64 := (s.gpr .r9).isLt
  obtain a₂ : InRegions (st.rd ++ st.wr) (st.gpr .rsp + BitVec.ofNat 64 24) 8 := by
    rw [h.rd, h.wr, h.rsp]; exact a_in hp (i := 2) (by decide)
  obtain hS : st.mem.readW (st.gpr .rsp + BitVec.ofNat 64 24) 64 = S s := by
    rw [h.rsp, show (24 : Nat) = 8 * (2 + 1) from rfl, keep_a hp h.frame (by decide)]; rfl
  obtain r₆ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 40) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  obtain hz := and_self_beq (show n s - q < 2 ^ 64 by omega_arith)
  apply WP.of_runBlock
  refine ⟨_, by simp only [argN]; xrun [a₂, hS, r₆, h.kept.n], ?_, by simp only [zf_arithFlags, hz],
    by simp [gpr_setReg, gpr_arithFlags], by simp [gpr_setReg, gpr_arithFlags], by rfl⟩
  exact h.slots hp (by simp [gpr_setReg, gpr_arithFlags]) (fun r hr => by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags])
    h.kept (Frame.refl _ _) rfl rfl

/-- The pointers of the copy. -/
theorem ptrs_ok {q : Nat} {st : State} (h : Mid s q q st) (h11 : st.gpr .r11 = S s) :
    WP isa (.block [.mov .rsi (.mem (at_ .r11 argSrc)), .mov .rdi (.mem (at_ .r11 argDst))]) st
      fun st' => st'.gpr .rsi = sq s q ∧ st'.gpr .rdi = dq s q ∧
        (∀ r, r ≠ .rsi → r ≠ .rdi → st'.gpr r = st.gpr r) ∧ st'.mem = st.mem ∧ st'.rd = st.rd ∧
        st'.wr = st.wr := by
  obtain r₅ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 32) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  obtain r₇ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 48) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  apply WP.of_runBlock
  refine ⟨_, by simp only [argSrc, argDst]; xrun [h11, r₅, r₇, h.kept.src, h.kept.dst], ?_, ?_, ?_, by rfl, by rfl,
    by rfl⟩
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]

/-- What the copy leaves: the plaintext left in the output, nothing else
written. -/
theorem copy_ok {q : Nat} {st : State} (h : Mid s q q st) (hlt : q < n s)
    (hsi : st.gpr .rsi = sq s q) (hdi : st.gpr .rdi = dq s q) (hcx : st.gpr .rcx = BitVec.ofNat 64 (n s - q)) :
    WP isa copyBlocks st fun st' =>
      blocksAt st'.mem (dq s q) (n s - q) = blocksAt s.mem (sq s q) (n s - q) ∧
      Frame [⟨dq s q, 16 * (n s - q)⟩] st.mem st'.mem ∧
      (∀ r, r ≠ .r10 → r ≠ .rcx → st'.gpr r = st.gpr r) ∧ st'.rd = st.rd ∧ st'.wr = st.wr := by
  have hq := h.q_le
  obtain h16 := n16_lt hp
  have hwr := hp.w_r
  have hwd := hp.w_d
  obtain ss : Region.Sub ⟨sq s q, 16 * (n s - q)⟩ (srcR s) := Offset.sub_base _ (by omega_arith)
  obtain ds : Region.Sub ⟨dq s q, 16 * (n s - q)⟩ (dR s) := Offset.sub_base _ (by omega_arith)
  obtain pre : CopyPre st (sq s q) (dq s q) (n s - q) :=
    ⟨hsi, hdi, hcx, by omega_arith, by omega_arith,
      Blocks.covers_off' (covers_of_mem (r := srcR s) (by rw [h.rd, h.wr, hp.rd]; simp)) (by omega_arith) (by omega_arith),
      Blocks.covers_off' (covers_of_mem (r := dR s) (by rw [h.wr, hp.wr]; simp)) (by omega_arith) (by omega_arith),
      (hp.r_d.sub_left ss).sub_right ds⟩
  refine WP.mono (copyBlocks_wp st pre) fun st' ⟨hm, hg, hrd, hwr'⟩ => ⟨?_, ?_, hg, hrd, hwr'⟩
  · have e := bytesAt_writeBytes_self st.mem (dq s q) (Spec.Aes.bytesAt st.mem (sq s q) (16 * (n s - q)))
      (by rw [length_bytesAt]; omega_arith)
    rw [length_bytesAt] at e
    rw [Proof.Gcm.blocksAt_eq, Proof.Gcm.blocksAt_eq, hm, e,
      bytesAt_frame h.frame (fun r hr => (src_wR hp r hr).sub_left ss) (by omega_arith)]
  · rw [hm]; exact writeBytes_frame' _ (length_bytesAt _ _ _)

/-- `Mid` through the copy, which writes only the output past the first `q`
blocks. -/
theorem Mid.copy {q : Nat} {st st' : State} (h : Mid s q q st)
    (hf : Frame [⟨dq s q, 16 * (n s - q)⟩] st.mem st'.mem) (hsp : st'.gpr .rsp = st.gpr .rsp)
    (hcs : ∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) (hrd : st'.rd = st.rd) (hwr : st'.wr = st.wr) :
    Mid s q q st' := by
  have hq := h.q_le
  have hwd := hp.w_d
  obtain h16 := n16_lt hp
  obtain ds : Region.Sub ⟨dq s q, 16 * (n s - q)⟩ (dR s) := Offset.sub_base _ (by omega_arith)
  obtain one : ∀ {r : Region}, r.Disjoint ⟨dq s q, 16 * (n s - q)⟩ →
      ∀ r' ∈ [(⟨dq s q, 16 * (n s - q)⟩ : Region)], r.Disjoint r' := fun hd r' hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hd
  refine ⟨hq, by rw [hsp, h.rsp], fun r hr => by rw [hcs r hr, h.saved r hr], hrd.trans h.rd, hwr.trans h.wr,
    h.kept.frame hf (one ((kR'_disj hp (dR s) (by simp)).sub_right ds)), h.frame.trans (hf.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨dR s, by simp, ds⟩), ?_, ?_, ?_⟩
  · rw [← h.data]
    exact blocksAt_frame hf (one (Offset.base_disjoint (Dst s) (k := 16 * q) (e := 16 * q) (n := 16 * (n s - q))
      (Nat.le_refl _) (by omega_arith))) (by omega_arith)
  · rw [← h.ctr]; exact blockAt_frame hf (one (hp.c_d.sub_right ds))
  · rw [← h.y]; exact blockAt_frame hf (one (hp.y_d.sub_right ds))

/-- The arguments of `vg_aes_gcm_encrypt_blocks` on the output left. -/
theorem args_ok {q : Nat} {st : State} (h : Mid s q q st) :
    WP isa (.block [.mov .r11 (.mem (at_ .rsp 24)), .mov .rdi (.mem (at_ .r11 argCtx)),
        .mov .rsi (.mem (at_ .r11 argRounds)), .mov .rdx (.mem (at_ .r11 argCtr)),
        .mov .rcx (.mem (at_ .r11 argY)), .mov .r8 (.mem (at_ .r11 argDst)), .mov .r9 (.mem (at_ .r11 argN)),
        .mov .rax (.reg .r11)]) st fun st' =>
      st'.gpr .rdi = K s ∧ st'.gpr .rsi = s.gpr .rsi ∧ st'.gpr .rdx = C s ∧ st'.gpr .rcx = Y s ∧
      st'.gpr .r8 = dq s q ∧ st'.gpr .r9 = BitVec.ofNat 64 (n s - q) ∧ st'.gpr .rax = S s ∧
      st'.gpr .rsp = SP s ∧ (∀ r ∈ calleeSaved, st'.gpr r = s.gpr r) ∧ st'.mem = st.mem ∧
      st'.rd = st.rd ∧ st'.wr = st.wr := by
  obtain a₂ : InRegions (st.rd ++ st.wr) (st.gpr .rsp + BitVec.ofNat 64 24) 8 := by
    rw [h.rd, h.wr, h.rsp]; exact a_in hp (i := 2) (by decide)
  obtain hS : st.mem.readW (st.gpr .rsp + BitVec.ofNat 64 24) 64 = S s := by
    rw [h.rsp, show (24 : Nat) = 8 * (2 + 1) from rfl, keep_a hp h.frame (by decide)]; rfl
  obtain r₁ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 0) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  obtain kc0 : st.mem.readW (S s + BitVec.ofNat 64 0) 64 = K s := by simpa using h.kept.ctx
  obtain r₂ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 8) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  obtain r₃ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 16) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  obtain r₄ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 24) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  obtain r₆ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 40) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  obtain r₇ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 48) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [argCtx, argRounds, argCtr, argY, argDst, argN]
    xrun [a₂, hS, r₁, r₂, r₃, r₄, r₆, r₇, kc0, h.kept.rounds, h.kept.ctr, h.kept.y, h.kept.dst, h.kept.n], ?_⟩
  refine ⟨by simp [gpr_setReg], by simp [gpr_setReg], by simp [gpr_setReg], by simp [gpr_setReg],
    by simp [gpr_setReg], by simp [gpr_setReg], by simp [gpr_setReg], by simp [gpr_setReg, h.rsp],
    fun r hr => ?_, by rfl, by rfl, by rfl⟩
  rw [← h.saved r hr]
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]

omit hp in
/-- The stack below the stack pointer after the push, as the call sees it. -/
theorem pushed_tR {st : State} (hsp : st.gpr .rsp = SP s) :
    (⟨(pushed [.rax] st).gpr .rsp - 16, 24⟩ : Region) = tR s := by
  rw [pushed_rsp, hsp]
  show (⟨SP s - BitVec.ofNat 64 8 - 16, 24⟩ : Region) = ⟨SP s - BitVec.ofNat 64 24, 24⟩
  rw [← Offset.sub_add_eq]; rfl

/-- What the call needs, after the push of `scratch`. -/
theorem blkCall_of {q : Nat} {st : State} (h : Mid s q q st) (hlt : q < n s)
    (h_di : st.gpr .rdi = K s) (h_si : st.gpr .rsi = s.gpr .rsi) (h_dx : st.gpr .rdx = C s) (h_cx : st.gpr .rcx = Y s)
    (h_8 : st.gpr .r8 = dq s q) (h_9 : st.gpr .r9 = BitVec.ofNat 64 (n s - q)) (h_ax : st.gpr .rax = S s) :
    BlkCall M (pushed [.rax] st) (K s) (C s) (Y s) (dq s q) (S s) (R s) (n s - q) := by
  have hq := h.q_le
  have hwd := hp.w_d
  obtain h16 := n16_lt hp
  have hsp := h.rsp
  have wt := hp.w_t
  obtain hn8 : 8 * [Reg.rax].length ≤ (st.gpr .rsp).toNat := by rw [hsp]; simp; omega_arith
  obtain ⟨hpf, hpj⟩ := pushRegs_mem st [.rax] (by decide) hn8
  obtain psp : (pushed [.rax] st).gpr .rsp = SP s - BitVec.ofNat 64 8 := by rw [pushed_rsp, hsp]; rfl
  obtain harg : (pushed [.rax] st).mem.readW ((pushed [.rax] st).gpr .rsp) 64 = S s := by
    have := hpj 0 (by decide); rw [← h_ax]; rw [pushed_rsp]; exact this
  obtain ds : Region.Sub ⟨dq s q, (n s - q) * 16⟩ (dR s) := Offset.sub_base _ (by omega_arith)
  obtain tt := pushed_tR (s := s) hsp
  obtain hdq : (dq s q).toNat = (Dst s).toNat + 16 * q := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * q) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  obtain hR : BitVec.ofNat 64 (R s) = s.gpr .rsi := by simp [R]
  obtain hok : M.ok st.mem (K s) := M.frame h.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [hp.k_c, hp.k_y, hp.k_d, hp.k_s]) hp.w_k hp.ok
  refine ⟨by rw [pushed_gpr _ _ (by decide)]; exact h_di, by rw [pushed_gpr _ _ (by decide), h_si, hR],
    by rw [pushed_gpr _ _ (by decide)]; exact h_dx, by rw [pushed_gpr _ _ (by decide)]; exact h_cx,
    by rw [pushed_gpr _ _ (by decide)]; exact h_8, by rw [pushed_gpr _ _ (by decide)]; exact h_9, harg, hp.rounds,
    hp.w_k, hp.w_c, hp.w_y, by rw [hdq]; omega_arith, hp.w_s, ?_,
    hp.k_c, hp.k_y, hp.k_d.sub_right ds, hp.k_s, hp.c_y, hp.c_d.sub_right ds, hp.c_s, hp.y_d.sub_right ds, hp.y_s,
    hp.d_s.sub_left ds, by rw [tt]; exact hp.b_k, by rw [tt]; exact hp.b_c, by rw [tt]; exact hp.b_y,
    by rw [tt]; exact hp.b_d.sub_right ds, by rw [tt]; exact hp.b_s, ?_, ?_, ?_⟩
  · rw [psp, show SP s - BitVec.ofNat 64 8 - 8 = SP s - BitVec.ofNat 64 16 by rw [← Offset.sub_add_eq]; rfl,
      toNat_sub_ofNat (by omega_arith)]
    omega_arith
  · simp only [pushed_rd, pushed_wr, h.rd, h.wr, hp.rd, hp.wr, hsp]
    refine covers_cons (covers_of_mem (by simp)) (covers_cons (covers_of_mem (by rw [pushed_rsp, hsp]; simp))
      (covers_cons (covers_of_mem (by simp)) (covers_cons (covers_of_mem (by simp))
      (covers_cons ?_ (covers_cons (covers_of_mem (by simp)) covers_nil)))))
    exact Blocks.covers_off' (covers_of_mem (r := dR s) (by simp)) (by omega_arith) (by omega_arith)
  · simp only [pushed_wr, h.wr, hp.wr, hsp]
    refine covers_cons (covers_of_mem (by simp)) (covers_cons (covers_of_mem (by simp))
      (covers_cons ?_ (covers_cons (covers_of_mem (by simp)) covers_nil)))
    exact Blocks.covers_off' (covers_of_mem (r := dR s) (by simp)) (by omega_arith) (by omega_arith)
  · exact M.frame hpf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [hsp]
      exact (hp.b_k.sub_left (below_sub (by decide) (by decide))).symm) hp.w_k hok

/-- What the call leaves, after the frame's pop. -/
theorem call_ok (B : BlkFn M) {q : Nat} {st : State} (h : Mid s q q st) (hlt : q < n s)
    (h_di : st.gpr .rdi = K s) (h_si : st.gpr .rsi = s.gpr .rsi) (h_dx : st.gpr .rdx = C s) (h_cx : st.gpr .rcx = Y s)
    (h_8 : st.gpr .r8 = dq s q) (h_9 : st.gpr .r9 = BitVec.ofNat 64 (n s - q)) (h_ax : st.gpr .rax = S s) :
    WP isa (.frame (.push [.rax]) (.call B.enc.name B.enc.code) (.pop .rax 1)) st fun st' =>
      (∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) ∧ st'.rd = st.rd ∧ st'.wr = st.wr ∧
      Frame [cR s, yR s, ⟨dq s q, (n s - q) * 16⟩, sR s, tR s] st.mem st'.mem ∧
      blocksAt st'.mem (dq s q) (n s - q) = ctr32 (aesWith (R s) (Spec.Aes.bytesAt st.mem (K s) (16 * (R s + 1))))
        (blockAt st.mem (C s)) (blocksAt st.mem (dq s q) (n s - q)) ∧
      blockAt st'.mem (C s) = Nat.repeat inc32 (n s - q) (blockAt st.mem (C s)) ∧
      blockAt st'.mem (Y s) = ghashFrom (blockAt st.mem (K s + 240)) (blockAt st.mem (Y s))
        (blocksAt st'.mem (dq s q) (n s - q)) := by
  have hq := h.q_le
  have hwd := hp.w_d
  obtain h16 := n16_lt hp
  have hsp := h.rsp
  have wt := hp.w_t
  obtain hn8 : 8 * [Reg.rax].length ≤ (st.gpr .rsp).toNat := by rw [hsp]; simp; omega_arith
  obtain ⟨hpf, -⟩ := pushRegs_mem st [.rax] (by decide) hn8
  obtain hpf' : Frame [below (SP s) 8] st.mem (pushed [.rax] st).mem := by rw [hsp] at hpf; exact hpf
  obtain b8 : Region.Sub (below (SP s) 8) (tR s) := below_sub (by decide) (by decide)
  obtain one : ∀ {r : Region}, (tR s).Disjoint r → ∀ r' ∈ [below (SP s) 8], r.Disjoint r' := fun hd r' hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (hd.sub_left b8).symm
  obtain hRb : 16 * (R s + 1) ≤ 256 := by rcases hp.rounds with h | h | h <;> simp only [R, h] <;> decide
  obtain ds : Region.Sub ⟨dq s q, (n s - q) * 16⟩ (dR s) := Offset.sub_base _ (by omega_arith)
  obtain eK : Spec.Aes.bytesAt (pushed [.rax] st).mem (K s) (16 * (R s + 1)) = Spec.Aes.bytesAt st.mem (K s) (16 * (R s + 1)) :=
    bytesAt_frame hpf' (one (hp.b_k.sub_right (Region.sub_prefix (Nat.le_trans hRb M.ge)))) (by have := hp.w_k; have := M.ge; omega_arith)
  obtain eC : blockAt (pushed [.rax] st).mem (C s) = blockAt st.mem (C s) := blockAt_frame hpf' (one hp.b_c)
  obtain eY : blockAt (pushed [.rax] st).mem (Y s) = blockAt st.mem (Y s) := blockAt_frame hpf' (one hp.b_y)
  obtain eD : blocksAt (pushed [.rax] st).mem (dq s q) (n s - q) = blocksAt st.mem (dq s q) (n s - q) :=
    blocksAt_frame hpf' (one (by rw [Nat.mul_comm]; exact hp.b_d.sub_right ds)) (by omega_arith)
  obtain eH : blockAt (pushed [.rax] st).mem (K s + 240) = blockAt st.mem (K s + 240) :=
    blockAt_frame hpf' (one (hp.b_k.sub_right (Offset.sub_base (d := 240) _ (by have := M.ge; omega_arith))))
  refine WP.frame (by simp) (by decide) (by decide) hn8
    (WP.mono (blkE_call B (blkCall_of hp h hlt h_di h_si h_dx h_cx h_8 h_9 h_ax)) fun s₃ ⟨bp, o₁, o₂, o₃⟩ => ?_)
  obtain psp : (pushed [.rax] st).gpr .rsp = SP s - BitVec.ofNat 64 8 := by rw [pushed_rsp, hsp]; rfl
  obtain r₃ := bp.saved _ (by decide : Reg.rsp ∈ calleeSaved)
  refine ⟨r₃, bp.wr, fun m u fm => ?_⟩
  -- The `pop` loses the frame's 8 bytes below `SP`, apart from the outputs.
  obtain fm' : Frame [below (SP s) 8] s₃.mem m := by have := fm; rw [hsp] at this; exact this
  obtain lD : blocksAt m (dq s q) (n s - q) = blocksAt s₃.mem (dq s q) (n s - q) :=
    blocksAt_frame fm' (one (by rw [Nat.mul_comm]; exact hp.b_d.sub_right ds)) (by omega_arith)
  obtain lC : blockAt m (C s) = blockAt s₃.mem (C s) := blockAt_frame fm' (one hp.b_c)
  obtain lY : blockAt m (Y s) = blockAt s₃.mem (Y s) := blockAt_frame fm' (one hp.b_y)
  dsimp only
  refine ⟨fun r hr => ?_, by rw [popped_rd, bp.rd, pushed_rd], by rw [popped_wr, bp.wr, pushed_wr]; rfl,
    ?_, ?_, ?_, ?_⟩
  · by_cases hr' : r = .rsp
    · subst hr'; rw [popped_rsp, r₃, psp, hsp]; exact BitVec.sub_add_cancel _ _
    · rw [popped_gpr _ _ _ hr' (fun e => by subst e; simp [calleeSaved] at hr), bp.saved r hr, pushed_gpr _ _ hr']
  · refine Frame.trans ?_ (fm'.sub fun r hr => ⟨tR s, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact b8⟩)
    refine (hpf'.sub fun r hr => ⟨tR s, by simp, by simp only [List.mem_singleton] at hr; subst hr; exact b8⟩).trans
      (bp.frame.sub fun r hr => ?_)
    simp only [BlkCall.wr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · refine ⟨tR s, by simp, ?_⟩
      obtain e : SP s - BitVec.ofNat 64 8 - BitVec.ofNat 64 16 = SP s - BitVec.ofNat 64 24 := by
        rw [← Offset.sub_add_eq, ← BitVec.ofNat_add]
      show Region.Sub ⟨(pushed [.rax] st).gpr .rsp - BitVec.ofNat 64 16, 16⟩ _
      rw [psp, e]; exact Region.sub_prefix (by decide)
  · rw [lD]; rw [eK, eC, eD] at o₁; exact o₁
  · rw [lC]; rw [eC] at o₂; exact o₂
  · rw [lY, lD]; rw [eH, eY] at o₃; exact o₃

/-- The blocks left, from `Mid s q q`: copied and encrypted in place. -/
theorem tail_ok (B : BlkFn M) {q : Nat} {st : State} (h : Mid s q q st) : WP isa (tail B.enc) st (Done s) := by
  have hq := h.q_le
  have hwd := hp.w_d
  have hwr := hp.w_r
  obtain h16 := n16_lt hp
  refine WP.seq (WP.mono (tailHead_ok hp h) fun st₁ ⟨M₁, hz, h11, hcx, hm₁⟩ => ?_)
  refine WP.ite (decide (n s - q = 0)) (by simp only [eval, hz]) (fun e => ?_) (fun e => ?_)
  · simp only [decide_eq_true_eq] at e
    exact WP.block_nil (done_of hp M₁ e)
  obtain hlt : q < n s := by simp at e; omega_arith
  refine WP.seq (WP.mono (ptrs_ok hp M₁ h11) fun st₂ ⟨hsi, hdi, g₂, m₂, rd₂, wr₂⟩ => ?_)
  obtain M₂ : Mid s q q st₂ := M₁.copy hp (by rw [m₂]; exact Frame.refl _ _) (g₂ _ (by decide) (by decide))
    (fun r hr => g₂ r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)) rd₂ wr₂
  refine WP.seq (WP.mono (copy_ok hp M₂ hlt hsi hdi (by rw [g₂ _ (by decide) (by decide), hcx]))
    fun st₃ ⟨hb₃, f₃, g₃, rd₃, wr₃⟩ => ?_)
  obtain M₃ : Mid s q q st₃ := M₂.copy hp f₃ (g₃ _ (by decide) (by decide))
    (fun r hr => g₃ r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)) rd₃ wr₃
  refine WP.seq (WP.mono (args_ok hp M₃) fun st₄ ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, sp₄, cs₄, m₄, rd₄, wr₄⟩ => ?_)
  obtain M₄ : Mid s q q st₄ := M₃.slots hp (by rw [sp₄, M₃.rsp]) (fun r hr => by rw [cs₄ r hr, M₃.saved r hr])
    (by rw [m₄]; exact M₃.kept) (by rw [m₄]; exact Frame.refl _ _) rd₄ wr₄
  refine WP.mono (call_ok hp B M₄ hlt a₁ a₂ a₃ a₄ a₅ a₆ a₇) fun st₅ ⟨cs₅, rd₅, wr₅, f₅, o₁, o₂, o₃⟩ => ?_
  -- The values the call read.
  obtain hK : Spec.Aes.bytesAt st₄.mem (K s) (16 * (R s + 1)) = Spec.Aes.bytesAt s.mem (K s) (16 * (R s + 1)) :=
    keep_sch hp M₄.frame
  obtain hH : blockAt st₄.mem (K s + 240) = hk s := keep_h hp M₄.frame
  obtain hD₄ : blocksAt st₄.mem (dq s q) (n s - q) = blocksAt s.mem (sq s q) (n s - q) := by rw [m₄]; exact hb₃
  rw [hK, M₄.ctr, hD₄] at o₁
  rw [M₄.ctr] at o₂
  rw [hH, M₄.y] at o₃
  -- What the call wrote is apart from the first `q` blocks and the return address.
  obtain ds : Region.Sub ⟨dq s q, (n s - q) * 16⟩ (dR s) := Offset.sub_base _ (by omega_arith)
  obtain keep : ∀ {r : Region}, r.Disjoint (cR s) → r.Disjoint (yR s) → r.Disjoint ⟨dq s q, (n s - q) * 16⟩ →
      r.Disjoint (sR s) → r.Disjoint (tR s) → ∀ r' ∈ [cR s, yR s, ⟨dq s q, (n s - q) * 16⟩, sR s, tR s],
        r.Disjoint r' := by
    intro r a b c d e r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption
  obtain pq : Region.Sub ⟨Dst s, 16 * q⟩ (dR s) := Region.sub_prefix (by omega_arith)
  obtain hfirst : blocksAt st₅.mem (Dst s) q = ct s q := by
    rw [← M₄.data]
    exact blocksAt_frame f₅ (keep (hp.c_d.symm.sub_left pq) (hp.y_d.symm.sub_left pq)
      (Offset.base_disjoint (Dst s) (k := 16 * q) (e := 16 * q) (Nat.le_refl _) (by omega_arith))
      (hp.d_s.sub_left pq) (hp.b_d.symm.sub_left pq)) (by omega_arith)
  obtain hall : ct s (n s) = ct s q ++ ctr32 (ciph s) (Nat.repeat inc32 q (cb s)) (blocksAt s.mem (sq s q) (n s - q)) := by
    rw [ct, ← Nat.add_sub_cancel' hq, Proof.Gcm.blocksAt_add, Proof.Gcm.ctr32_append, Blocks.length_blocksAt,
      Nat.add_sub_cancel' hq]
  refine ⟨⟨fun r hr => by rw [cs₅ r hr, M₄.saved r hr], ?_⟩, ?_, ?_, ?_⟩
  · show st₅.mem.readW (SP s) 64 = s.mem.readW (SP s) 64
    rw [f₅.readW (Region.contains_self _ _) (keep hp.t_c hp.t_y (hp.t_d.sub_right ds) hp.t_s
      (Offset.base_disjoint_below (SP s) (by omega_arith))) (by decide), keep_r hp M₄.frame]
  · show blocksAt st₅.mem (Dst s) (n s) = ct s (n s)
    rw [← Nat.add_sub_cancel' hq, Proof.Gcm.blocksAt_add, Nat.add_sub_cancel' hq]
    rw [hfirst]; exact (congrArg (ct s q ++ ·) o₁).trans hall.symm
  · show blockAt st₅.mem (C s) = Nat.repeat inc32 (n s) (cb s)
    rw [o₂, ← Proof.Gcm.repeat_add, Nat.sub_add_cancel hq]
  · show blockAt st₅.mem (Y s) = ghashFrom (hk s) (y₀ s) (ct s (n s))
    rw [o₃, o₁, ← Proof.Gcm.ghashFrom_append, hall]
    rfl

end

end VG.Proof.AesGcm.X86_64.BlocksTo

end

end

/-! ### `AesGcm.X86_64.BlocksTo.CT`, which this module and modules that import it used -/

section

/-! ### `AesGcm.X86_64.BlocksTo.Full`, which this module and modules that import it used -/

section

/-!
# AES-GCM on whole blocks out of place, x86-64: loops that take all the blocks

Untrusted: everything here is checked by Lean. With a `piece` that also
takes the blocks after the last 16 (`full`), at least 16 blocks are all
given to it, after `takeAllTo` makes the arguments kept those of no rest
(`takeAllTo_ok`): its result is `Mid` with `q = k = n` (`mid_of_postTo`),
which `rest` keeps (`restFullTo_ok`). With fewer, `q = 0`, as without `full`
(`stitchFullTo_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.BlocksTo

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.BlocksTo
open VG.Impl.AesGcm.X86_64.Blocks (argN)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode SPreTo EPostTo StitchToOkM)

/-- The blocks a `piece` that takes them all is given: all of them if at
least 16, else none. -/
def qf (s : State) : Nat := if n s < 16 then 0 else n s

section
variable {aligned : Bool} {M : CtxMode} {s : State} (hp : BT M s)
include hp

/-- `takeAllTo`: the arguments kept become those of no rest. -/
theorem takeAllTo_ok {s₂ : State} (h11 : s₂.gpr .r11 = S s) (h9 : s₂.gpr .r9 = s.gpr .r9)
    (h8 : s₂.gpr .r8 = Src s) (h10 : s₂.gpr .r10 = Dst s) (hk : Kept s 0 s₂.mem)
    (hf : Frame [kR' s] s.mem s₂.mem) (hwr : s₂.wr = s.wr) :
    WP isa (.block takeAllTo) s₂ fun s₃ => Kept s (n s) s₃.mem ∧ Frame [kR' s] s.mem s₃.mem ∧
      (∀ r, r ≠ .rax → s₃.gpr r = s₂.gpr r) ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
  have w₅ : InRegions s₂.wr (S s + BitVec.ofNat 64 32) 8 := by rw [hwr]; exact s_in hp (by decide)
  have w₆ : InRegions s₂.wr (S s + BitVec.ofNat 64 40) 8 := by rw [hwr]; exact s_in hp (by decide)
  have w₇ : InRegions s₂.wr (S s + BitVec.ofNat 64 48) 8 := by rw [hwr]; exact s_in hp (by decide)
  have e9 : s₂.gpr .r9 = BitVec.ofNat 64 (n s) := by rw [h9]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have sep : ∀ a d : Nat, a + 8 ≤ d ∨ d + 8 ≤ a → a + 8 ≤ 2112 → d + 8 ≤ 2112 →
      Mem.Sep (S s + BitVec.ofNat 64 a) (64 / 8) (S s + BitVec.ofNat 64 d) (64 / 8) :=
    fun a d h ha hd => Offset.sep _ h (by omega_using [ha]) (by omega_using [hd])
  have kp : ∀ d, d + 8 ≤ 32 → ∀ u v w : BitVec 64,
      (((s₂.mem.writeW (S s + BitVec.ofNat 64 32) u).writeW (S s + BitVec.ofNat 64 48) v).writeW
        (S s + BitVec.ofNat 64 40) w).readW (S s + BitVec.ofNat 64 d) 64 =
        s₂.mem.readW (S s + BitVec.ofNat 64 d) 64 := fun d h₁ u v w => by
    rw [Mem.readW_writeW_sep (sep d 40 (.inl (by omega_using [h₁])) (by omega_using [h₁]) (by decide)) (by decide),
      Mem.readW_writeW_sep (sep d 48 (.inl (by omega_using [h₁])) (by omega_using [h₁]) (by decide)) (by decide),
      Mem.readW_writeW_sep (sep d 32 (.inl (by omega_using [h₁])) (by omega_using [h₁]) (by decide)) (by decide)]
  apply WP.of_runBlock
  refine ⟨_, by simp only [takeAllTo, argSrc, argDst, argN]; xrun [h11, e9, h8, h10, w₅, w₆, w₇, times16_val], ?_⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, fun r hr => by simp [gpr_setReg, gpr_arithFlags, hr], rfl, rfl⟩
  · have := kp 0 (by decide); simp only [BitVec.add_zero] at this; rw [this]; exact hk.ctx
  · rw [kp 8 (by decide)]; exact hk.rounds
  · rw [kp 16 (by decide)]; exact hk.ctr
  · rw [kp 24 (by decide)]; exact hk.y
  · rw [Mem.readW_writeW_sep (sep 32 40 (.inl (by decide)) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (sep 32 48 (.inl (by decide)) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self64, BitVec.add_comm]
  · rw [Mem.readW_writeW_self64, Nat.sub_self]; rfl
  · rw [Mem.readW_writeW_sep (sep 48 40 (.inr (by decide)) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self64, BitVec.add_comm]
  · have c : ∀ d, d + 8 ≤ 56 → (kR' s).Contains (S s + BitVec.ofNat 64 d) (64 / 8) :=
      fun d h₁ => Offset.contains_base _ h₁ (by omega_using [h₁])
    exact ((hf.writeW (List.mem_singleton_self _) _ (c 32 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 48 (by decide))).writeW (List.mem_singleton_self _) _ (c 40 (by decide))

/-- `rest` with no blocks left: nothing changes. -/
theorem restZeroTo_ok {q : Nat} (hq : q = n s) {st : State} (h : Mid s q q st) :
    WP isa (.block rest) st (Mid s q q) := by
  have a₂ : InRegions (st.rd ++ st.wr) (st.gpr .rsp + BitVec.ofNat 64 24) 8 := by
    rw [h.rd, h.wr, h.rsp]; exact a_in hp (i := 2) (by decide)
  have hS : st.mem.readW (st.gpr .rsp + BitVec.ofNat 64 24) 64 = S s := by
    rw [h.rsp, show (24 : Nat) = 8 * (2 + 1) from rfl, keep_a hp h.frame (by decide)]; rfl
  have r₅ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 32) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have r₆ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 40) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have r₇ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 48) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have w₅ : InRegions st.wr (S s + BitVec.ofNat 64 32) 8 := by rw [h.wr]; exact s_in hp (by decide)
  have w₆ : InRegions st.wr (S s + BitVec.ofNat 64 40) 8 := by rw [h.wr]; exact s_in hp (by decide)
  have w₇ : InRegions st.wr (S s + BitVec.ofNat 64 48) 8 := by rw [h.wr]; exact s_in hp (by decide)
  have kr := h.kept.src
  have kn := h.kept.n
  have kd := h.kept.dst
  rw [hq, Nat.sub_self] at kn
  have e15 : 0#64 &&& 15#64 = 0#64 := by decide
  have sep : ∀ a d : Nat, a + 8 ≤ d ∨ d + 8 ≤ a → a + 8 ≤ 2112 → d + 8 ≤ 2112 →
      Mem.Sep (S s + BitVec.ofNat 64 a) (64 / 8) (S s + BitVec.ofNat 64 d) (64 / 8) :=
    fun a d h ha hd => Offset.sep _ h (by omega_using [ha]) (by omega_using [hd])
  have s₅₇ := sep 32 48 (by decide) (by decide) (by decide)
  have s₅₆ := sep 32 40 (by decide) (by decide) (by decide)
  have s₆₇ := sep 40 48 (by decide) (by decide) (by decide)
  have s₇₅ := sep 48 32 (by decide) (by decide) (by decide)
  have kp : ∀ d, d + 8 ≤ 32 → ∀ u v w : BitVec 64,
      (((st.mem.writeW (S s + BitVec.ofNat 64 32) u).writeW (S s + BitVec.ofNat 64 48) v).writeW
        (S s + BitVec.ofNat 64 40) w).readW (S s + BitVec.ofNat 64 d) 64 =
        st.mem.readW (S s + BitVec.ofNat 64 d) 64 := fun d h₁ u v w => by
    rw [Mem.readW_writeW_sep (sep d 40 (.inl (by omega_using [h₁])) (by omega_using [h₁]) (by decide)) (by decide),
      Mem.readW_writeW_sep (sep d 48 (.inl (by omega_using [h₁])) (by omega_using [h₁]) (by decide)) (by decide),
      Mem.readW_writeW_sep (sep d 32 (.inl (by omega_using [h₁])) (by omega_using [h₁]) (by decide)) (by decide)]
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [rest, argSrc, argN, argDst]
    xrun [a₂, hS, r₅, r₆, r₇, w₅, w₆, w₇, kn, e15, kr, kd, s₅₇, s₅₆, s₆₇, s₇₅, BitVec.sub_self,
      BitVec.add_zero, BitVec.zero_add, Mem.readW_writeW_sep, Mem.readW_writeW_self64], ?_⟩
  refine h.slots hp (by simp [gpr_setReg, gpr_arithFlags]) (fun r hr => ?_) ?_ ?_ rfl rfl
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := kp 0 (by decide); simp only [BitVec.add_zero] at this; rw [this]; exact h.kept.ctx
    · rw [kp 8 (by decide)]; exact h.kept.rounds
    · rw [kp 16 (by decide)]; exact h.kept.ctr
    · rw [kp 24 (by decide)]; exact h.kept.y
    · rw [Mem.readW_writeW_sep (sep 32 40 (.inl (by decide)) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_sep (sep 32 48 (.inl (by decide)) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_self64]
    · rw [Mem.readW_writeW_self64, hq, Nat.sub_self]
    · rw [Mem.readW_writeW_sep (sep 48 40 (.inr (by decide)) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_self64]
  · have c : ∀ d, d + 8 ≤ 56 → (kR' s).Contains (S s + BitVec.ofNat 64 d) (64 / 8) :=
      fun d h₁ => Offset.contains_base _ h₁ (by omega_using [h₁])
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 32 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 48 (by decide))).writeW (List.mem_singleton_self _) _ (c 40 (by decide))

/-- `rest` after all the blocks, or none if fewer than 16. -/
theorem restFullTo_ok {st : State} (h : Mid s (qf s) (qf s) st) :
    WP isa (.block rest) st (Mid s (qf s) (qf s)) := by
  by_cases h16 : n s < 16
  · have hq : qf s = 0 := by simp [qf, h16]
    rw [hq] at h ⊢
    exact rest_ok hp (by omega_using [h16]) h
  · exact restZeroTo_ok hp (by simp [qf, h16]) h

/-- With `full`, all the blocks by `piece` (if at least 16). -/
theorem stitchFullTo_ok {piece : Prog isa} (hpiece : StitchToOkM M piece 1)
    {s₁ : State} (h11 : s₁.gpr .r11 = S s) (h10 : s₁.gpr .r10 = Dst s)
    (hg : ∀ r, r ≠ .r11 → r ≠ .r10 → s₁.gpr r = s.gpr r)
    (hk : Kept s 0 s₁.mem) (hf : Frame [kR' s] s.mem s₁.mem) (hrd : s₁.rd = s.rd) (hwr : s₁.wr = s.wr) :
    WP isa (stitchPart piece aligned true) s₁ (Mid s (qf s) (qf s)) := by
  obtain hn : n s < 2 ^ 64 := (s.gpr .r9).isLt
  refine WP.seq (WP.mono (cmp16_ok (hg _ (by decide) (by decide))) fun s₂ ⟨g₂, m₂, rd₂, wr₂, cf₂⟩ => ?_)
  refine WP.ite (decide (n s < 16)) (by simp only [eval, cf₂]) (fun h => ?_) (fun h => ?_)
  · have h16 : n s < 16 := by simpa using h
    obtain hq : qf s = 0 := by simp [qf, h16]
    rw [hq]
    exact WP.block_nil (mid_entry hp (by rw [g₂]; exact hg _ (by decide) (by decide))
      (fun r hr => by rw [g₂]; exact hg r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr))
      (by rw [m₂]; exact hk) (by rw [m₂]; exact hf) (rd₂.trans hrd) (wr₂.trans hwr))
  · have h16 : 16 ≤ n s := by simp at h; omega_using [h]
    obtain hq : qf s = n s := by simp [qf, show ¬ n s < 16 by omega_using [h16]]
    rw [hq]
    refine WP.seq ?_
    rw [show ((if true = true then takeAllTo else [.mov .rax (.reg .r9), .alu .and .rax (imm 15),
      .alu .sub .r9 (.reg .rax)]) ++ Blocks.scratchSetup aligned : List Instr) =
      takeAllTo ++ Blocks.scratchSetup aligned from rfl, WP.block_append_iff]
    refine WP.mono (takeAllTo_ok hp (by rw [g₂, h11]) (by rw [g₂, hg _ (by decide) (by decide)])
      (by rw [g₂, hg _ (by decide) (by decide)]) (by rw [g₂, h10]) (by rw [m₂]; exact hk) (by rw [m₂]; exact hf)
      (by rw [wr₂, hwr])) fun s₃ ⟨k₃, f₃, g₃, rd₃, wr₃⟩ => ?_
    refine WP.mono (Blocks.scratch_ok (aligned := aligned) s₃) fun s₄ ⟨h11₄, g₄, m₄, rd₄, wr₄⟩ => ?_
    obtain keepR : ∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .r11 → s₄.gpr r = s.gpr r := fun r a b c => by
      rw [g₄ r c, g₃ r a, g₂, hg r c b]
    obtain ga : ∀ r ∈ argRegs, s₄.gpr r = s.gpr r := fun r hr => by
      simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact keepR _ (by decide) (by decide) (by decide)
    obtain gc : ∀ r ∈ calleeSaved, s₄.gpr r = s.gpr r := fun r hr => by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact keepR _ (by decide) (by decide) (by decide)
    obtain h10₄ : s₄.gpr .r10 = Dst s := by rw [g₄ _ (by decide), g₃ _ (by decide), g₂, h10]
    obtain g11 : s₄.gpr .r11 = S s + BitVec.ofNat 64 (AlignedScratch.offset aligned (S s)) := by
      rw [h11₄, g₃ _ (by decide), g₂, h11]; exact AlignedScratch.ptr_eq aligned (S s) hp.w_s
    obtain h9 : s₄.gpr .r9 = BitVec.ofNat 64 (n s) := by
      rw [keepR _ (by decide) (by decide) (by decide)]
      exact (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _) |>.symm
    obtain rd₄' : s₄.rd = s.rd := by rw [rd₄, rd₃, rd₂, hrd]
    obtain wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₃, wr₂, hwr]
    obtain hk₄ : Kept s (n s) s₄.mem := by rw [m₄]; exact k₃
    obtain hf₄ : Frame [kR' s] s.mem s₄.mem := by rw [m₄]; exact f₃
    exact WP.mono (hpiece s₄ (spreTo_of hp h16 (Nat.le_refl _) h9 ga h10₄ g11 rd₄' wr₄' hf₄) (Nat.mod_one _))
      fun s₅ hP => mid_of_postTo hp (Nat.le_refl _) h9 ga gc h10₄ g11 rd₄' wr₄' hk₄ hf₄ hP

end

end VG.Proof.AesGcm.X86_64.BlocksTo

end

end

/-!
# AES-GCM on whole blocks out of place, x86-64: constant time

Untrusted: everything here is checked by Lean. Two runs from states with the
same public arguments go through the same pieces: each load of `scratch`
from the stack gives both the same pointer (`rel_r11`), after which the taint
analysis checks the piece from it and `rsp`; the interleaved loops are checked
from the arguments in their registers and the output in `r10`; the branch on
the blocks left agrees (`tailHead_ok`); and the copy and the call get the same
pointers and lengths (`blkE_rel`), from what correctness says of each run
(`rel_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.BlocksTo

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.BlocksTo
open VG.Impl.AesGcm.X86_64.Blocks (argCtx argRounds argCtr argY argN)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)

/-- `scratch`, loaded from the stack into `r11`. -/
theorem loadR11_ok {s : State} (hr : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 24) 8) :
    WP isa (.block [.mov .r11 (.mem (at_ .rsp 24))]) s fun s' =>
      s'.gpr .r11 = s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 24) 64 ∧ ∀ r, r ≠ .r11 → s'.gpr r = s.gpr r := by
  refine WP.of_runBlock ⟨_, by xrun [hr], ?_, ?_⟩
  · simp [gpr_setReg]
  · intro r a; simp [gpr_setReg, a]

theorem loadR11_check : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block [.mov .r11 (.mem (at_ .rsp 24))]) hc).isSome =
    true := ⟨_, by taint_decide⟩

/-- A block that first loads `scratch` into `r11`, from states that agree on
`rs` (with `rsp`) and hold the same pointer there, checked from `r11` and
`rs`. -/
theorem rel_r11 {P : State → State → Prop} {l₀ l : List Instr}
    (hl : l₀ = ([.mov .r11 (.mem (at_ .rsp 24))] : List Instr) ++ l) (rs rs' : List Reg) (hrs : .rsp ∈ rs)
    (hag : ∀ s₁ s₂, P s₁ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hS : ∀ s₁ s₂, P s₁ s₂ → s₁.mem.readW (s₁.gpr .rsp + BitVec.ofNat 64 24) 64 =
      s₂.mem.readW (s₂.gpr .rsp + BitVec.ofNat 64 24) 64 ∧
      InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rsp + BitVec.ofNat 64 24) 8 ∧
      InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .rsp + BitVec.ofNat 64 24) 8)
    (hc : ∃ hc, ((taint.check (Taint.ofRegs (.r11 :: rs)) (.block l) hc).map fun τ' =>
      (RegSet.ofList rs').subset τ'.regs && (!false || τ'.flags)) = some true) :
    RelCT isa P (.block l₀) fun s₁ s₂ => ∀ r ∈ rs', s₁.gpr r = s₂.gpr r := by
  subst hl
  have l₁ := RelCT.wpDep (rel_taint (P := P) [.rsp] (fun s₁ s₂ h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hag _ _ h _ hrs) loadR11_check)
    (F := fun (σ s' : State) => s'.gpr .r11 = σ.mem.readW (σ.gpr .rsp + BitVec.ofNat 64 24) 64 ∧
      ∀ r, r ≠ .r11 → s'.gpr r = σ.gpr r)
    fun s₁ s₂ h => ⟨loadR11_ok (hS _ _ h).2.1, loadR11_ok (hS _ _ h).2.2⟩
  refine rel_block_split (RelCT.seq l₁ ((rel_regs (.r11 :: rs) rs' false (fun s₁ s₂ h r hr => ?_) hc).mono
    (fun _ _ h => h) fun _ _ h => h.1))
  obtain ⟨-, σ₁, σ₂, hσ, ⟨a₁, b₁⟩, ⟨a₂, b₂⟩⟩ := h
  rcases List.mem_cons.mp hr with rfl | hr
  · rw [a₁, a₂]; exact (hS _ _ hσ).1
  · by_cases hx : r = .r11
    · subst hx; rw [a₁, a₂]; exact (hS _ _ hσ).1
    · rw [b₁ r hx, b₂ r hx]; exact hag _ _ hσ r hr

/-- The blocks of `tail`. -/
abbrev headB : List Instr :=
  [.mov .r11 (.mem (at_ .rsp 24)), .mov .rcx (.mem (at_ .r11 argN)), .alu .test .rcx (.reg .rcx)]
abbrev ptrsB : List Instr := [.mov .rsi (.mem (at_ .r11 argSrc)), .mov .rdi (.mem (at_ .r11 argDst))]
abbrev argsB : List Instr :=
  [.mov .r11 (.mem (at_ .rsp 24)), .mov .rdi (.mem (at_ .r11 argCtx)), .mov .rsi (.mem (at_ .r11 argRounds)),
    .mov .rdx (.mem (at_ .r11 argCtr)), .mov .rcx (.mem (at_ .r11 argY)), .mov .r8 (.mem (at_ .r11 argDst)),
    .mov .r9 (.mem (at_ .r11 argN)), .mov .rax (.reg .r11)]

theorem tail_eq (enc : Fn) : tail enc = .seq (.block headB) (.ite .e (.block [])
    (.seq (.block ptrsB) (.seq copyBlocks (.seq (.block argsB)
      (.frame (.push [.rax]) (.call enc.name enc.code) (.pop .rax 1)))))) := rfl

/-- `Mid`, with the arguments of the call in their registers. -/
def AP (s : State) (q : Nat) (st : State) : Prop :=
  Mid s q q st ∧ st.gpr .rdi = K s ∧ st.gpr .rsi = s.gpr .rsi ∧ st.gpr .rdx = C s ∧ st.gpr .rcx = Y s ∧
    st.gpr .r8 = dq s q ∧ st.gpr .r9 = BitVec.ofNat 64 (n s - q) ∧ st.gpr .rax = S s

section
variable {M : CtxMode} {s : State} (hp : BT M s)
include hp

/-- `scratch` on the stack, at `Mid`. -/
theorem mid_S {q k : Nat} {st : State} (h : Mid s q k st) :
    st.mem.readW (st.gpr .rsp + BitVec.ofNat 64 24) 64 = S s ∧
      InRegions (st.rd ++ st.wr) (st.gpr .rsp + BitVec.ofNat 64 24) 8 := by
  refine ⟨?_, ?_⟩
  · rw [h.rsp, show (24 : Nat) = 8 * (2 + 1) from rfl, keep_a hp h.frame (by decide)]; rfl
  · rw [h.rd, h.wr, h.rsp]; exact a_in hp (i := 2) (by decide)

/-- `Mid` after the pointers of the copy. -/
theorem ptrsM_ok {q : Nat} {st : State} (h : Mid s q q st) (h11 : st.gpr .r11 = S s)
    (hcx : st.gpr .rcx = BitVec.ofNat 64 (n s - q)) :
    WP isa (.block ptrsB) st fun st' => Mid s q q st' ∧ st'.gpr .rsi = sq s q ∧ st'.gpr .rdi = dq s q ∧
      st'.gpr .rcx = BitVec.ofNat 64 (n s - q) :=
  WP.mono (ptrs_ok hp h h11) fun _ ⟨hsi, hdi, g₂, m₂, rd₂, wr₂⟩ =>
    ⟨h.copy hp (by rw [m₂]; exact Frame.refl _ _) (g₂ _ (by decide) (by decide))
      (fun r hr => g₂ r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)) rd₂ wr₂,
      hsi, hdi, by rw [g₂ _ (by decide) (by decide), hcx]⟩

/-- `Mid` after the copy. -/
theorem copyM_ok {q : Nat} {st : State} (h : Mid s q q st) (hlt : q < n s)
    (hsi : st.gpr .rsi = sq s q) (hdi : st.gpr .rdi = dq s q) (hcx : st.gpr .rcx = BitVec.ofNat 64 (n s - q)) :
    WP isa copyBlocks st (Mid s q q) :=
  WP.mono (copy_ok hp h hlt hsi hdi hcx) fun _ ⟨_, f₃, g₃, rd₃, wr₃⟩ =>
    h.copy hp f₃ (g₃ _ (by decide) (by decide))
      (fun r hr => g₃ r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)) rd₃ wr₃

/-- `Mid` after the arguments of the call. -/
theorem argsM_ok {q : Nat} {st : State} (h : Mid s q q st) : WP isa (.block argsB) st (AP s q) :=
  WP.mono (args_ok hp h) fun _ ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, sp₄, cs₄, m₄, rd₄, wr₄⟩ =>
    ⟨h.slots hp (by rw [sp₄, h.rsp]) (fun r hr => by rw [cs₄ r hr, h.saved r hr]) (by rw [m₄]; exact h.kept)
      (by rw [m₄]; exact Frame.refl _ _) rd₄ wr₄, a₁, a₂, a₃, a₄, a₅, a₆, a₇⟩

end

/-! ## Two runs -/

/-- What two entry states with the same public arguments share. -/
structure Pub (s₀ s₀' : State) : Prop where
  k : K s₀' = K s₀
  rsi : s₀'.gpr .rsi = s₀.gpr .rsi
  c : C s₀' = C s₀
  y : Y s₀' = Y s₀
  src : Src s₀' = Src s₀
  r9 : s₀'.gpr .r9 = s₀.gpr .r9
  sp : SP s₀' = SP s₀
  dst : Dst s₀' = Dst s₀
  sc : S s₀' = S s₀

theorem Pub.of {s₀ s₀' : State} (h : Proof.AesGcm.blocksToPub s₀ s₀') : Pub s₀ s₀' :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.1.symm, h.2.2.2.2.1.symm, h.2.2.2.2.2.1.symm,
    h.2.2.2.2.2.2.1.symm, h.2.2.2.2.2.2.2.1.symm, h.2.2.2.2.2.2.2.2.2.symm⟩

theorem Pub.en {s₀ s₀' : State} (pb : Pub s₀ s₀') : n s₀' = n s₀ := by simp only [n, pb.r9]
theorem Pub.eR {s₀ s₀' : State} (pb : Pub s₀ s₀') : R s₀' = R s₀ := by simp only [R, pb.rsi]
theorem Pub.esq {s₀ s₀' : State} (pb : Pub s₀ s₀') (q : Nat) : sq s₀' q = sq s₀ q := by simp only [sq, pb.src]
theorem Pub.edq {s₀ s₀' : State} (pb : Pub s₀ s₀') (q : Nat) : dq s₀' q = dq s₀ q := by simp only [dq, pb.dst]

/-- The registers of the arguments, which the entry keeps. -/
def args : List Reg := [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]

theorem entry_check : ∃ hc, ((taint.check (Taint.ofRegs (.r11 :: args)) (.block entry.tail) hc).map fun τ' =>
    (RegSet.ofList (.r11 :: args)).subset τ'.regs && (!false || τ'.flags)) = some true := ⟨_, by taint_decide⟩

theorem rest_check : ∃ hc, ((taint.check (Taint.ofRegs [.r11, .rsp]) (.block rest.tail) hc).map fun τ' =>
    (RegSet.ofList [Reg.rsp]).subset τ'.regs && (!false || τ'.flags)) = some true := ⟨_, by taint_decide⟩

theorem nil_check : ∃ hc, ((taint.check (Taint.ofRegs (.r11 :: args)) (.block []) hc).map
    fun τ' => (RegSet.ofList [Reg.rsp]).subset τ'.regs && (!false || τ'.flags)) = some true := ⟨_, by taint_decide⟩

theorem tailHead_check : ∃ hc, ((taint.check (Taint.ofRegs [.r11, .rsp]) (.block headB.tail) hc).map fun τ' =>
    (RegSet.ofList [Reg.rsp]).subset τ'.regs && (!false || τ'.flags)) = some true := ⟨_, by taint_decide⟩

theorem ptrs_check : ∃ hc, (taint.check (Taint.ofRegs [.r11]) (.block ptrsB) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem copy_check : ∃ hc, (taint.check (Taint.ofRegs [.rsi, .rdi, .rcx]) copyBlocks hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem args_check : ∃ hc, ((taint.check (Taint.ofRegs [.r11, .rsp]) (.block argsB.tail) hc).map fun τ' =>
    (RegSet.ofList [Reg.rsp]).subset τ'.regs && (!false || τ'.flags)) = some true := ⟨_, by taint_decide⟩

theorem empty_check : ∃ hc, (taint.check (Taint.ofRegs []) (.block []) hc).isSome = true := ⟨_, by taint_decide⟩

/-- What the head of `tail` leaves. -/
def TH (s : State) (q : Nat) (st : State) : Prop :=
  Mid s q q st ∧ st.zf = some (decide (n s - q = 0)) ∧ st.gpr .r11 = S s ∧
    st.gpr .rcx = BitVec.ofNat 64 (n s - q)

/-- What the entry leaves. -/
def EntryPost (s₀ s₁ : State) : Prop :=
  s₁.gpr .r11 = S s₀ ∧ s₁.gpr .r10 = Dst s₀ ∧ (∀ r, r ≠ .r11 → r ≠ .r10 → s₁.gpr r = s₀.gpr r) ∧
    Kept s₀ 0 s₁.mem ∧ Frame [kR' s₀] s₀.mem s₁.mem ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr

section
variable {M : CtxMode} {s₀ s₀' : State} (hp : BT M s₀) (hp' : BT M s₀') (pb : Pub s₀ s₀')
include hp hp' pb

/-- Loading `scratch` from the stack, in two runs at `Mid`. -/
theorem mid_hS {q k q' k' : Nat} {s₁ s₂ : State} (h₁ : Mid s₀ q k s₁) (h₂ : Mid s₀' q' k' s₂) :
    s₁.mem.readW (s₁.gpr .rsp + BitVec.ofNat 64 24) 64 = s₂.mem.readW (s₂.gpr .rsp + BitVec.ofNat 64 24) 64 ∧
      InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rsp + BitVec.ofNat 64 24) 8 ∧
      InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .rsp + BitVec.ofNat 64 24) 8 :=
  ⟨by rw [(mid_S hp h₁).1, (mid_S hp' h₂).1, pb.sc], (mid_S hp h₁).2, (mid_S hp' h₂).2⟩

omit hp hp' in
theorem mid_rsp {q k q' k' : Nat} {s₁ s₂ : State} (h₁ : Mid s₀ q k s₁) (h₂ : Mid s₀' q' k' s₂) :
    ∀ r ∈ [Reg.rsp], s₁.gpr r = s₂.gpr r := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr; rw [h₁.rsp, h₂.rsp, pb.sp]

/-- The entry, in two runs. -/
theorem entry_rel : RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (.block entry) fun s₁ s₂ =>
    (∀ r ∈ .r11 :: args, s₁.gpr r = s₂.gpr r) ∧ EntryPost s₀ s₁ ∧ EntryPost s₀' s₂ := by
  have ea : ∀ r ∈ args, s₀.gpr r = s₀'.gpr r := by
    intro r hr
    simp only [args, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pb.k.symm, pb.rsi.symm, pb.c.symm, pb.y.symm, pb.src.symm, pb.r9.symm, pb.sp.symm]
  refine rel_wp (rel_r11 (l₀ := entry) (l := entry.tail) rfl args (.r11 :: args) (by simp [args])
    (fun _ _ h => by obtain ⟨rfl, rfl⟩ := h; exact ea) (fun _ _ h => by
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨pb.sc.symm, a_in hp (i := 2) (by decide), a_in hp' (i := 2) (by decide)⟩) entry_check)
    (fun _ _ h => h) (fun s h => by subst h; exact entry_ok hp) (fun s h => by subst h; exact entry_ok hp')

/-- The interleaved part (or nothing) and `rest`, in two runs. -/
theorem part_rel {aligned : Bool} (st : Option (StitchToCode M aligned)) :
    RelCT isa (fun s₁ s₂ => (∀ r ∈ .r11 :: args, s₁.gpr r = s₂.gpr r) ∧ EntryPost s₀ s₁ ∧ EntryPost s₀' s₂)
      (head (st.map (·.enc)) aligned (encFullTo st))
      fun s₁ s₂ => ∃ q, Mid s₀ q q s₁ ∧ Mid s₀' q q s₂ := by
  have me : ∀ (s s₁ : State), BT M s → EntryPost s s₁ → Mid s 0 0 s₁ := fun s s₁ hp h => by
    obtain ⟨_, _, g₁, k₁, f₁, rd₁, wr₁⟩ := h
    exact mid_entry hp (g₁ _ (by decide) (by decide))
      (fun r hr => g₁ r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr))
      k₁ f₁ rd₁ wr₁
  cases st with
  | none =>
    refine ((rel_regs (.r11 :: args) [.rsp] false (fun _ _ h => h.1) nil_check).wp
      (F₁ := Mid s₀ 0 0) (F₂ := Mid s₀' 0 0) fun s₁ s₂ h => ⟨WP.block_nil (me _ _ hp h.2.1),
        WP.block_nil (me _ _ hp' h.2.2)⟩).mono (fun _ _ h => h) fun _ _ h => ⟨0, h.2.1, h.2.2⟩
  | some p =>
    have ag : ∀ s₁ s₂, ((∀ r ∈ .r11 :: args, s₁.gpr r = s₂.gpr r) ∧ EntryPost s₀ s₁ ∧ EntryPost s₀' s₂) →
        ∀ r ∈ [Reg.r10, .r11, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r := by
      intro s₁ s₂ h r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · rw [h.2.1.2.1, h.2.2.2.1, pb.dst]
      · exact h.1 r hr
    rcases p with ⟨enc, full, ok, P⟩
    cases full with
    | false =>
      have a := rel_wp (rel_regs _ [.rsp] false ag P.ct) (fun _ _ h => h.2)
        (fun _ h => stitch_ok hp ok h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2)
        (fun _ h => stitch_ok hp' ok h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2)
      have b := rel_wp (rel_r11 (l₀ := rest) (l := rest.tail) rfl
        (P := fun s₁ s₂ => (∀ r ∈ [Reg.rsp], s₁.gpr r = s₂.gpr r) ∧
          Mid s₀ (n s₀ - n s₀ % 16) 0 s₁ ∧ Mid s₀' (n s₀' - n s₀' % 16) 0 s₂) [.rsp] [.rsp] (by simp)
        (fun _ _ h => h.1) (fun _ _ h => mid_hS hp hp' pb h.2.1 h.2.2) rest_check)
        (fun _ _ h => h.2) (fun _ h => rest_ok hp rfl h) (fun _ h => rest_ok hp' rfl h)
      refine (RelCT.seq (a.mono (fun _ _ h => h) fun _ _ h => ⟨h.1.1, h.2⟩) b).mono (fun _ _ h => h)
        fun _ _ h => ⟨n s₀ - n s₀ % 16, h.2.1, ?_⟩
      rw [← pb.en]; exact h.2.2
    | true =>
      have eq : qf s₀' = qf s₀ := by simp only [qf, pb.en]
      have a := rel_wp (rel_regs _ [.rsp] false ag P.ct) (fun _ _ h => h.2)
        (fun _ h => stitchFullTo_ok hp ok h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2)
        (fun _ h => stitchFullTo_ok hp' ok h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2)
      have b := rel_wp (rel_r11 (l₀ := rest) (l := rest.tail) rfl
        (P := fun s₁ s₂ => (∀ r ∈ [Reg.rsp], s₁.gpr r = s₂.gpr r) ∧
          Mid s₀ (qf s₀) (qf s₀) s₁ ∧ Mid s₀' (qf s₀') (qf s₀') s₂) [.rsp] [.rsp] (by simp)
        (fun _ _ h => h.1) (fun _ _ h => mid_hS hp hp' pb h.2.1 h.2.2) rest_check)
        (fun _ _ h => h.2) (fun _ h => restFullTo_ok hp h) (fun _ h => restFullTo_ok hp' h)
      refine (RelCT.seq (a.mono (fun _ _ h => h) fun _ _ h => ⟨h.1.1, h.2⟩) b).mono (fun _ _ h => h)
        fun _ _ h => ⟨qf s₀, h.2.1, ?_⟩
      rw [← eq]; exact h.2.2

/-- The call, in two runs at the same point. -/
theorem frame_rel (B : BlkFn M) {q : Nat} (hlt : q < n s₀) :
    RelCT isa (fun s₁ s₂ => AP s₀ q s₁ ∧ AP s₀' q s₂)
      (.frame (.push [.rax]) (.call B.enc.name B.enc.code) (.pop .rax 1)) fun _ _ => True := by
  have hlt' : q < n s₀' := by rw [pb.en]; exact hlt
  refine RelCT.frame (fun _ _ h => by rw [h.1.1.rsp, h.2.1.rsp, pb.sp]) (blkE_rel B fun _ _ ⟨s₁, s₂, h, ha, hb⟩ => ?_)
  obtain ⟨⟨M₁, a₁, a₂, a₃, a₄, a₅, a₆, a₇⟩, ⟨M₂, b₁, b₂, b₃, b₄, b₅, b₆, b₇⟩⟩ := h
  have c₂ := blkCall_of hp' M₂ hlt' b₁ b₂ b₃ b₄ b₅ b₆ b₇
  rw [pb.k, pb.c, pb.y, pb.edq, pb.sc, pb.eR, pb.en] at c₂
  exact ⟨_, _, _, _, _, _, _, ha ▸ blkCall_of hp M₁ hlt a₁ a₂ a₃ a₄ a₅ a₆ a₇, hb ▸ c₂,
    by rw [ha, hb, pushed_rsp, pushed_rsp, M₁.rsp, M₂.rsp, pb.sp]⟩

/-- `tail`, from two runs at the same point. -/
theorem tail_rel (B : BlkFn M) {q : Nat} :
    RelCT isa (fun s₁ s₂ => Mid s₀ q q s₁ ∧ Mid s₀' q q s₂) (tail B.enc) fun _ _ => True := by
  have a := rel_wp (rel_r11 (l₀ := headB) (l := headB.tail) rfl
      (P := fun s₁ s₂ => Mid s₀ q q s₁ ∧ Mid s₀' q q s₂) [.rsp] [.rsp] (by simp)
      (fun _ _ h => mid_rsp pb h.1 h.2) (fun _ _ h => mid_hS hp hp' pb h.1 h.2) tailHead_check)
    (fun _ _ h => h) (G₁ := TH s₀ q) (G₂ := TH s₀' q)
    (fun _ h => WP.mono (tailHead_ok hp h) fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)
    (fun _ h => WP.mono (tailHead_ok hp' h) fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)
  rw [tail_eq]
  refine RelCT.seq a (rel_ite_e (fun _ _ h => by rw [h.2.1.2.1, h.2.2.2.1, pb.en]) ?_ ?_)
  · exact (rel_taint [] (fun _ _ _ r hr => by cases hr) empty_check).mono (fun _ _ h => h) fun _ _ h => h
  intro s₁ s₂ t₁ t₂ s₁' s₂' hP e₁ e₂
  obtain ⟨⟨-, ⟨M₁, z₁, r11₁, cx₁⟩, ⟨M₂, z₂, r11₂, cx₂⟩⟩, hz⟩ := hP
  have hlt : q < n s₀ := by
    rw [hz] at z₁; simp only [Option.some.injEq, Bool.false_eq, decide_eq_false_iff_not] at z₁; omega_using [z₁]
  have hlt' : q < n s₀' := by rw [pb.en]; exact hlt
  -- The pointers of the copy.
  have b := rel_wp (rel_taint (P := fun s₁ s₂ =>
      (Mid s₀ q q s₁ ∧ s₁.gpr .r11 = S s₀ ∧ s₁.gpr .rcx = BitVec.ofNat 64 (n s₀ - q)) ∧
      (Mid s₀' q q s₂ ∧ s₂.gpr .r11 = S s₀' ∧ s₂.gpr .rcx = BitVec.ofNat 64 (n s₀' - q))) (c := .block ptrsB)
      [.r11] (fun _ _ h r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2.1, h.2.2.1, pb.sc]) ptrs_check)
    (fun _ _ h => h) (fun _ h => ptrsM_ok hp h.1 h.2.1 h.2.2) (fun _ h => ptrsM_ok hp' h.1 h.2.1 h.2.2)
  have c := rel_wp (rel_taint (P := fun s₁ s₂ => True ∧
      (Mid s₀ q q s₁ ∧ s₁.gpr .rsi = sq s₀ q ∧ s₁.gpr .rdi = dq s₀ q ∧ s₁.gpr .rcx = BitVec.ofNat 64 (n s₀ - q)) ∧
      (Mid s₀' q q s₂ ∧ s₂.gpr .rsi = sq s₀' q ∧ s₂.gpr .rdi = dq s₀' q ∧
        s₂.gpr .rcx = BitVec.ofNat 64 (n s₀' - q))) (c := copyBlocks)
      [.rsi, .rdi, .rcx] (fun _ _ h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h.2.1.2.1, h.2.2.2.1, pb.esq]
        · rw [h.2.1.2.2.1, h.2.2.2.2.1, pb.edq]
        · rw [h.2.1.2.2.2, h.2.2.2.2.2, pb.en]) copy_check)
    (fun _ _ h => h.2) (fun _ h => copyM_ok hp h.1 hlt h.2.1 h.2.2.1 h.2.2.2)
    (fun _ h => copyM_ok hp' h.1 hlt' h.2.1 h.2.2.1 h.2.2.2)
  have d := rel_wp (rel_r11 (l₀ := argsB) (l := argsB.tail) rfl
      (P := fun s₁ s₂ => True ∧ Mid s₀ q q s₁ ∧ Mid s₀' q q s₂) [.rsp] [.rsp] (by simp)
      (fun _ _ h => mid_rsp pb h.2.1 h.2.2) (fun _ _ h => mid_hS hp hp' pb h.2.1 h.2.2) args_check)
    (fun _ _ h => h.2) (G₁ := AP s₀ q) (G₂ := AP s₀' q) (fun _ h => argsM_ok hp h) (fun _ h => argsM_ok hp' h)
  have e := (frame_rel hp hp' pb B hlt).mono (P' := fun (s₁ s₂ : State) => (∀ r ∈ [Reg.rsp], s₁.gpr r = s₂.gpr r) ∧
    AP s₀ q s₁ ∧ AP s₀' q s₂) (fun _ _ h => h.2) fun _ _ h => h
  exact (RelCT.seq b (RelCT.seq c (RelCT.seq d e))) _ _ _ _ _ _ ⟨⟨M₁, r11₁, cx₁⟩, ⟨M₂, r11₂, cx₂⟩⟩ e₁ e₂

end

theorem encrypt_ct {M : CtxMode} (B : BlkFn M) {aligned : Bool} (st : Option (StitchToCode M aligned)) :
    ConstantTime isa (Proof.AesGcm.encryptBlocksToX86_64M M).pre Proof.AesGcm.blocksToPub
      (encrypt B.enc (st.map (·.enc)) aligned (encFullTo st)) := by
  refine ct_of_rel fun s₀ s₀' h h' hq => ?_
  have hp := BT.ofM h
  have hp' := BT.ofM h'
  have pb := Pub.of hq
  refine RelCT.seq (entry_rel hp hp' pb) (RelCT.seq (part_rel hp hp' pb st) ?_)
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨q, M₁, M₂⟩ e₁ e₂
  exact tail_rel hp hp' pb B _ _ _ _ _ _ ⟨M₁, M₂⟩ e₁ e₂

end VG.Proof.AesGcm.X86_64.BlocksTo

end

end

/-! ### `AesGcm.X86_64.BlocksTo.Fn`, which only this module used -/

section

/-!
# AES-GCM on whole blocks out of place, x86-64: correctness

Untrusted: everything here is checked by Lean. The entry, the first
`16 ⌊n / 16⌋` blocks in one pass (with out-of-place interleaved loops, if
any), and the rest, copied and encrypted in place by a call (`encrypt_wp`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64.BlocksTo

open VG VG.X86_64 VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.BlocksTo
open VG.Proof.Gcm.X86_64.Stitch (CtxMode StitchToOkM)

theorem encrypt_wp {M : CtxMode} (B : BlkFn M) (aligned full : Bool) (st : Option (Prog isa))
    (hst : ∀ p, st = some p → StitchToOkM M p (if full then 1 else 16)) {s : State}
    (hpre : Proof.AesGcm.blocksToPreM M s) :
    WP isa (encrypt B.enc st aligned full) s (Done s) := by
  have hp := BT.ofM hpre
  refine WP.seq (WP.mono (entry_ok hp) fun s₁ ⟨h11, h10, hg, hk, hf, hrd, hwr⟩ => ?_)
  cases st with
  | none =>
    exact WP.seq (WP.block_nil (tail_ok hp B (mid_entry hp (hg _ (by decide) (by decide))
      (fun r hr => hg r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr))
      hk hf hrd hwr)))
  | some p =>
    cases full with
    | false =>
      exact WP.seq (WP.seq (WP.mono (stitch_ok hp (hst p rfl) h11 h10 hg hk hf hrd hwr) fun st M =>
        WP.mono (rest_ok hp rfl M) fun st' M' => tail_ok hp B M'))
    | true =>
      exact WP.seq (WP.seq (WP.mono (stitchFullTo_ok hp (hst p rfl) h11 h10 hg hk hf hrd hwr) fun st M =>
        WP.mono (restFullTo_ok hp M) fun st' M' => tail_ok hp B M'))

end VG.Proof.AesGcm.X86_64.BlocksTo

end

end


/-!
# AES-GCM on whole blocks out of place, x86-64: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant time
of `vg_aes_gcm_encrypt_blocks_to` calling any `vg_aes_gcm_encrypt_blocks` `B`
(with or without out-of-place interleaved loops `st`), its code's static
facts (no load of `mxcsr`, `rsp` kept, 24 bytes of stack), and the shared
contracts of `Spec/Gcm/OutOfPlace.lean`, for the key contexts of
`vg_aes_gcm_init` and `vg_aes_gcm_init_precomputed`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open Gcm.X86_64.Stitch (CtxMode)

section
variable {M : CtxMode} {aligned : Bool} (st : Option (StitchToCode M aligned))

theorem headTo_mx : (BlocksTo.head (st.map (·.enc)) aligned (encFullTo st)).allInstrs (fun i => !loadsMxcsr i) = true := by
  rcases st with _ | ⟨enc, full, ok, P⟩
  · rfl
  · simp only [Option.map, Option.any, encFullTo, BlocksTo.head, BlocksTo.stitchPart, Code.allInstrs, P.mxcsr]
    cases full <;> cases aligned <;> rfl

theorem headTo_spSafe : (BlocksTo.head (st.map (·.enc)) aligned (encFullTo st)).all (fun i => !X86_64.isa.writesSp i) = true := by
  rcases st with _ | ⟨enc, full, ok, P⟩
  · rfl
  · simp only [Option.map, Option.any, encFullTo, BlocksTo.head, BlocksTo.stitchPart, Code.all, P.spSafe]
    cases full <;> cases aligned <;> rfl

theorem headTo_xdepth : (BlocksTo.head (st.map (·.enc)) aligned (encFullTo st)).x86_64Depth = 0 := by
  rcases st with _ | ⟨enc, full, ok, P⟩
  · rfl
  · simp only [Option.map, Option.any, encFullTo, BlocksTo.head, BlocksTo.stitchPart, Code.x86_64Depth, P.xdepth]
    cases full <;> cases aligned <;> rfl

variable (B : BlkFn M)

theorem encryptTo_mx : (BlocksTo.encrypt B.enc (st.map (·.enc)) aligned (encFullTo st)).allInstrs (fun i => !loadsMxcsr i) = true := by
  have e := B.encMx
  simp only [BlocksTo.encrypt, BlocksTo.tail, BlocksTo.copyBlocks, Code.allInstrs, headTo_mx st, e,
    Bool.true_and, Bool.and_true]
  decide +kernel

theorem encryptTo_spSafe :
    (BlocksTo.encrypt B.enc (st.map (·.enc)) aligned (encFullTo st)).all (fun i => !X86_64.isa.writesSp i) = true := by
  have e := B.encSp
  simp only [BlocksTo.encrypt, BlocksTo.tail, BlocksTo.copyBlocks, Code.all, headTo_spSafe st, e,
    Bool.true_and, Bool.and_true]
  decide +kernel

theorem encryptTo_xdepth : (BlocksTo.encrypt B.enc (st.map (·.enc)) aligned (encFullTo st)).x86_64Depth ≤ 24 := by
  have e := B.encXd
  simp only [BlocksTo.encrypt, BlocksTo.tail, BlocksTo.copyBlocks, Code.x86_64Depth, X86_64.Instr.frameBytes,
    List.length_cons, List.length_nil, headTo_xdepth st, Nat.max_le]
  omega_using [e]

theorem encryptToM_correct (s : State) (hs : (Proof.AesGcm.encryptBlocksToX86_64M M).pre s) :
    ∃ t s', Exec isa (BlocksTo.encrypt B.enc (st.map (·.enc)) aligned (encFullTo st)) s t s' ∧ abiPreserved s s' ∧
      Proof.AesGcm.blocksToPost s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := BlocksTo.encrypt_wp B aligned (encFullTo st) (st.map (·.enc))
    (fun p e => by obtain ⟨i, rfl, rfl⟩ := Option.map_eq_some_iff.1 e; exact i.ok) hs
  exact ⟨t, s', he, abiPreserved_of_exec (encryptTo_mx st B) he hg, hp⟩

end

end VG.Proof.AesGcm.X86_64
