module

public import VerifiedGarbage.Proof.AesCbc.RISCV64.Loop
import VerifiedGarbage.Proof.Aes.RISCV64.BlocksVerified
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit
public import VerifiedGarbage.Impl.Aes.RISCV64.Blocks
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.RISCV64.Target

/-!
# AES modes on RISC-V, a block at a time: one block

What a body of `whole`'s loop (`Loop.lean`) needs to take the loop
invariant from `k` blocks to `k + 1` (`BodyOk`) around its call of a block
function, as on PPC64LE (`Proof/AesCbc/PPC64LE/Body.lean`): the call's
arguments (`callArgs_pre`) and the frames of the call and of the step
(`callFrame`, `stepFrame`). AES-CFB128 decryption's and XTS's bodies use
them (`Proof/AesCfb/RISCV64/Body.lean`, `Proof/AesXts/RISCV64/Body.lean`);
AES-CBC decryption runs four blocks at a time instead
(`Proof/Aes/RISCV64/WideCbc.lean`).
-/

@[expose] public section

namespace VG.Proof.AesCbc.RISCV64

open VG VG.RISCV64 VG.RISCV64.Align VG.Impl.AesCbc.RISCV64
open VG.Spec.Aes (bytesAt)

theorem encryptBlocks_noFrames : Impl.Aes.RISCV64.encryptBlocks.noFrames = true := by lit_decide

theorem decryptBlocks_noFrames : Impl.Aes.RISCV64.decryptBlocks.noFrames = true := by lit_decide

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.blk_toNat {k : Nat} (hk : k < N s₀) : (blk s₀ k).toNat = (Dp s₀).toNat + 16 * k := by
  have := hp.data_wrap
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * k) (by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem UPre.blk_wrap {k : Nat} (hk : k < N s₀) : (blk s₀ k).toNat + 16 ≤ 2 ^ 64 := by
  have := hp.data_wrap
  rw [hp.blk_toNat hk]; omega

/-- The regions the code reads and writes, from the invariant. -/
theorem LInv.regs {M : Mode} {k : Nat} {s : State} (h : LInv M s₀ k s) :
    s.rd ++ s.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by
  rw [h.rd, h.wr, hp.rd, hp.wr]; rfl

theorem LInv.wrs {M : Mode} {k : Nat} {s : State} (h : LInv M s₀ k s) :
    s.wr = [ivR s₀, dataR s₀, scrR s₀] := by
  rw [h.wr, hp.wr]

/-- The arguments of a call on block `k`, with the working space at the start
of the scratch buffer. -/
theorem UPre.callPre {k : Nat} (hk : k < N s₀) {s : State}
    (a0 : s.gpr .a0 = W s₀) (a1 : s.gpr .a1 = s₀.gpr .a1) (a2 : s.gpr .a2 = blk s₀ k)
    (a3 : s.gpr .a3 = BitVec.ofNat 64 1) (a4 : s.gpr .a4 = S s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    CallPre s (W s₀) (blk s₀ k) (S s₀) (R s₀) where
  a0 := a0
  a1 := by rw [a1, a1_ofNat]
  a2 := a2
  a3 := a3
  a4 := a4
  rounds := hp.rounds
  wd := hp.sch_data.sub_right (UPre.data_sub hk)
  ws := hp.sch_scr.sub_right wsR_sub
  ds := (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right wsR_sub
  wrap := hp.blk_wrap hk
  reads := by
    rw [hrd, hwr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨dataR s₀, by simp, 16 * k, rfl, by simp; omega⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩
  writes := by
    rw [hwr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨dataR s₀, by simp, 16 * k, rfl, by simp; omega⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩

theorem UPre.blk_iv {k : Nat} (hk : k < N s₀) : (⟨blk s₀ k, 16⟩ : Region).Disjoint (ivR s₀) :=
  hp.iv_data.symm.sub_left (UPre.data_sub hk)

/-- Block `k` is in a writable region. -/
theorem LInv.wBlk {M : Mode} {k : Nat} (hk : k < N s₀) {s : State} (h : LInv M s₀ k s) :
    ∃ r ∈ s.wr, Region.Sub ⟨blk s₀ k, 16⟩ r := ⟨dataR s₀, by rw [h.wrs hp]; simp, UPre.data_sub hk⟩

theorem LInv.rIv {M : Mode} {k : Nat} {s : State} (h : LInv M s₀ k s) :
    ∃ r ∈ s.rd ++ s.wr, Region.Sub (ivR s₀) r := ⟨ivR s₀, by rw [h.regs hp]; simp, fun _ h => h⟩

theorem LInv.wC {M : Mode} {k : Nat} {s : State} (h : LInv M s₀ k s) :
    ∃ r ∈ s.wr, Region.Sub (cR s₀) r := ⟨scrR s₀, by rw [h.wrs hp]; simp, cR_sub⟩

theorem LInv.rC {M : Mode} {k : Nat} {s : State} (h : LInv M s₀ k s) :
    ∃ r ∈ s.rd ++ s.wr, Region.Sub (cR s₀) r := ⟨scrR s₀, by rw [h.regs hp]; simp, cR_sub⟩

omit hp in
/-- The frame of a step, in the regions the invariant allows. -/
theorem stepFrame {k : Nat} (hk : k < N s₀) {m m' : Mem}
    (hf : Frame [⟨blk s₀ k, 16⟩, ivR s₀, wsR s₀, cR s₀] m m') : Frame (Mut s₀) m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨dataR s₀, by simp, UPre.data_sub hk⟩
    · exact ⟨ivR s₀, by simp, fun _ h => h⟩
    · exact ⟨wsR s₀, by simp, fun _ h => h⟩
    · exact ⟨cR s₀, by simp, fun _ h => h⟩

end

/-- A step's frame, from the frames of its pieces. -/
theorem frame_mono {rs rs' : List Region} {m m' : Mem} (hf : Frame rs m m') (h : ∀ r ∈ rs, r ∈ rs') :
    Frame rs' m m' := hf.mono h

/-- What the code before a call leaves: the call's arguments, the callee-saved
registers, and the memory `m`. -/
structure Pre (s₀ : State) (D : Addr) (m : Mem) (s s₁ : State) : Prop where
  pre : CallPre s₁ (W s₀) D (S s₀) (R s₀)
  saved : ∀ r ∈ preserved, s₁.gpr r = s.gpr r
  mem : s₁.mem = m
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr
  sp : s₁.sp = s.sp

theorem preserved_ne {r : Reg} (hr : r ∈ preserved) :
    r ∉ argRegs5 ∧ r ≠ .t0 ∧ r ≠ .t3 ∧ r ≠ .t4 := by
  revert hr; cases r <;> decide

/-- `callArgs` after code that keeps the callee-saved registers. -/
theorem callArgs_pre {M : Mode} {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s s₁ : State}
    {m : Mem} (h : LInv M s₀ k s) (g : ∀ r ∈ preserved, s₁.gpr r = s.gpr r) (hm : s₁.mem = m)
    (hrd : s₁.rd = s.rd) (hwr : s₁.wr = s.wr) (hsp : s₁.sp = s.sp) :
    WP isa (.block callArgs) s₁ (Pre s₀ (blk s₀ k) m s) :=
  callArgs_wp fun s₂ a0 a1 a2 a3 a4 o mem rd wr sp => by
    have keep (r : Reg) (hr : r ∈ preserved) : s₂.gpr r = s.gpr r := by
      rw [o r (preserved_ne hr).1, g r hr]
    exact ⟨hp.callPre hk (by rw [a0, g _ (by decide), h.s1]) (by rw [a1, g _ (by decide), h.s2])
      (by rw [a2, g _ (by decide), h.s4]) a3 (by rw [a4, g _ (by decide), h.s6])
      (by rw [rd, hrd, h.rd]) (by rw [wr, hwr, h.wr]), keep, by rw [mem, hm], by rw [rd, hrd],
      by rw [wr, hwr], by rw [sp, hsp]⟩

/-- A one-region frame's disjointness, from one fact. -/
theorem one {r : Region} {P : Addr} (hd : (⟨P, 16⟩ : Region).Disjoint r) :
    ∀ r' ∈ [r], (⟨P, 16⟩ : Region).Disjoint r' := fun r' hr' => by
  simp only [List.mem_singleton] at hr'; subst hr'; exact hd

/-- The frame of a call, in the step's regions. -/
theorem callFrame {s₀ : State} {k : Nat} {m m' : Mem}
    (hf : Frame [⟨blk s₀ k, 16⟩, ⟨S s₀, 2048⟩] m m') : Frame [⟨blk s₀ k, 16⟩, ivR s₀, wsR s₀, cR s₀] m m' :=
  hf.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp

end VG.Proof.AesCbc.RISCV64
