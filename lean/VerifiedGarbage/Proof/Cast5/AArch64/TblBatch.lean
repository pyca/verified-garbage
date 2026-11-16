module

public import VerifiedGarbage.Proof.Cast5.AArch64.TblCipher
public import VerifiedGarbage.Proof.Blowfish.AArch64.Batch
import VerifiedGarbage.Proof.Blowfish.Blocks
import VerifiedGarbage.Proof.Blowfish.Schedule
import VerifiedGarbage.Proof.Cast5.Memory
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset

/-!
# CAST5 on AArch64: a batch of sixteen blocks

`batch_ok`: `batch up` replaces each of the sixteen blocks at `x4` with its
encryption (`up`) or decryption, with the subkeys at `x0` and their number in
`x16`. The loads and stores are Blowfish's (`loadBatch`, `storeBatch`,
`Proof/Blowfish/AArch64/Batch.lean`), whose blocks have the same encoding.
-/

@[expose] public section

namespace VG.Proof.Cast5.AArch64.Tbl

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Cast5.AArch64.Tbl
open VG.Impl.Blowfish.AArch64 (aReg bReg c64 c128 loadBatch storeBatch)
open VG.Spec.Cast5 (Word Schedule Block)
open VG.Proof.Cast5 (encFold decFold)
open VG.Proof.Blowfish.AArch64 (lane Consts loadBatch_run storeBatch_run outByte cat_run halfRegs)
open VG.AArch64.Tbl (VOnly)

/-! ## The blocks' encoding -/

theorem cat4_byte (a b c d : BitVec 8) {j : Nat} (hj : j < 4) :
    (a ++ b ++ c ++ d : BitVec 32).extractLsb' (8 * j) 8 = [d, c, b, a].getD j 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, BitVec.getLsbD_append, BitVec.getLsbD_append]
  rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
  · simp [hi]
  · simp [hi, show ¬ 8 + i < 8 by omega]
  · simp [hi, show ¬ 16 + i < 8 by omega, show 16 + i - 8 = 8 + i by omega]
  · simp [hi, show ¬ 24 + i < 8 by omega, show 24 + i - 8 = 16 + i by omega, show 16 + i - 8 = 8 + i by omega,
      show ¬ 8 + i < 8 by omega, show ¬ 16 + i < 8 by omega]

/-- The halves of a block are Blowfish's big-endian words. -/
theorem decodeBlock_eq (b : Block) :
    Spec.Cast5.decodeBlock b = (Spec.Blowfish.decodeWord b 0, Spec.Blowfish.decodeWord b 4) := by
  refine Prod.ext (Proof.Blowfish.word_ext fun j hj => ?_) (Proof.Blowfish.word_ext fun j hj => ?_)
  · rw [Proof.Blowfish.decodeWord_byte _ _ hj]
    show (b[0] ++ b[1] ++ b[2] ++ b[3] : BitVec 32).extractLsb' (8 * j) 8 = _
    rw [cat4_byte _ _ _ _ hj]
    rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
      simp [Vector.getD, Array.getD]
  · rw [Proof.Blowfish.decodeWord_byte _ _ hj]
    show (b[4] ++ b[5] ++ b[6] ++ b[7] : BitVec 32).extractLsb' (8 * j) 8 = _
    rw [cat4_byte _ _ _ _ hj]
    rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
      simp [Vector.getD, Array.getD]

theorem encodeBlock_eq (x y : Word) : Spec.Cast5.encodeBlock (x, y) = Spec.Blowfish.encodeBlock x y := by
  refine congrArg Vector.ofFn (funext fun i => ?_)
  have := i.isLt
  by_cases h : i.val < 4
  · simp only [h, ite_true, show i.val % 4 = i.val by omega]
  · simp only [h, ite_false, show 3 - i.val % 4 = 7 - i.val by omega]

/-! ## The batch -/

/-- The halves after the rounds of encryption (`up`) or decryption. -/
def foldOut (k : Schedule) (n : Nat) (up : Bool) (lr : Word × Word) : Word × Word :=
  if up then encFold k n lr else decFold k n n lr

/-- A block's encryption (`up`) or decryption. -/
def blockOut (k : Schedule) (n : Nat) (up : Bool) (b : Block) : Block :=
  if up then Spec.Cast5.encryptBlock k n b else Spec.Cast5.decryptBlock k n b

theorem blockOut_eq (k : Schedule) (n : Nat) (up : Bool) (b : Block) :
    blockOut k n up b =
      Spec.Blowfish.encodeBlock (foldOut k n up (Spec.Blowfish.decodeWord b 0, Spec.Blowfish.decodeWord b 4)).2
        (foldOut k n up (Spec.Blowfish.decodeWord b 0, Spec.Blowfish.decodeWord b 4)).1 := by
  rw [← encodeBlock_eq, ← decodeBlock_eq]
  cases up <;> rfl

theorem cipher_ok (up : Bool) {s : State} {k : Schedule} {n : Nat} (P : CPre s k) (hn : n = 12 ∨ n = 16)
    (h16 : s.gpr .x16 = BitVec.ofNat 64 n) :
    WP isa (cipher up) s fun v =>
      Halves v.v (fun m => foldOut k n up (lane s.v aReg m, lane s.v bReg m)) ∧ RFrame cipherG roundV s v := by
  cases up
  · exact cipherDec_ok P hn h16
  · exact cipherEnc_ok P hn h16

/-- What the rounds read, in a state that keeps it. -/
theorem CPre.frame {s u : State} {k : Schedule} (P : CPre s k) {gs : List Reg} {vs : List VReg}
    (fr : RFrame gs vs s u) (h0 : Reg.x0 ∉ gs) (h9 : Reg.x9 ∉ gs) (hc : c64 ∉ vs ∧ c128 ∉ vs) : CPre u k :=
  ⟨by rw [fr.g _ h9, fr.syms]; exact P.x9,
    ⟨fun e he => by rw [fr.v _ hc.1]; exact P.consts.1 e he, fun e he => by rw [fr.v _ hc.2]; exact P.consts.2 e he⟩,
    by rw [fr.rd, fr.wr, fr.g _ h0]; exact P.sched, fun j hj => by rw [fr.mem, fr.g _ h0]; exact P.key j hj⟩

/-- The general-purpose registers a batch writes. -/
def batchG : List Reg := [.x4, .x5, .x6, .x7, .x8, .x13, .x14, .x15, .x17]

structure BatchPost (k : Schedule) (n : Nat) (up : Bool) (s s' : State) : Prop where
  out : ∀ j < 16, Spec.Cast5.blockAt s'.mem (s.gpr .x4 + BitVec.ofNat 64 (8 * j)) =
    blockOut k n up (Spec.Cast5.blockAt s.mem (s.gpr .x4 + BitVec.ofNat 64 (8 * j)))
  frame : Frame [⟨s.gpr .x4, 128⟩] s.mem s'.mem
  x4 : s'.gpr .x4 = s.gpr .x4
  gpr : ∀ r, r ∉ batchG → s'.gpr r = s.gpr r
  v : ∀ r, r ∉ roundV → s'.v r = s.v r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  syms : s'.syms = s.syms

theorem io_sub : ∀ r ∈ (VReg.v20 :: .v21 :: halfRegs), r ∈ roundV := by decide
theorem consts_notin_io : c64 ∉ (VReg.v20 :: .v21 :: halfRegs) ∧ c128 ∉ (VReg.v20 :: .v21 :: halfRegs) := by decide

theorem batch_ok (up : Bool) {s : State} {k : Schedule} {n : Nat} (P : CPre s k) (hn : n = 12 ∨ n = 16)
    (h16 : s.gpr .x16 = BitVec.ofNat 64 n)
    (hW : ∀ j < 8, InRegions s.wr (s.gpr .x4 + BitVec.ofNat 64 (16 * j)) 16) :
    WP isa (batch up) s (BatchPost k n up s) := by
  obtain ⟨s₁, r₁, a₁, b₁, o₁⟩ := loadBatch_run (s := s) fun j hj => by
    obtain ⟨r, hr, hc'⟩ := hW j hj; exact ⟨r, List.mem_append_right _ hr, hc'⟩
  let s₂ := s₁.write .x .x17 (s₁.read .x .x4 + BitVec.ofNat _ 0)
  have fr₂ : RFrame batchG roundV s s₂ :=
    ((RFrame.ofV o₁).mono (fun _ h => absurd h List.not_mem_nil) io_sub).write (by decide) _
  have fr₂' : RFrame [.x17] (VReg.v20 :: .v21 :: halfRegs) s s₂ :=
    ((RFrame.ofV o₁).mono (fun _ h => absurd h List.not_mem_nil) (fun _ h => h)).write (by decide) _
  have x17₂ : s₂.gpr .x17 = s.gpr .x4 := by
    show (s₁.write .x .x17 _).gpr .x17 = _
    rw [gpr_write_self]
    show s₁.gpr .x4 + BitVec.ofNat 64 0 = _
    rw [o₁.gpr]; exact BitVec.add_zero _
  rw [batch]
  apply WP.seq
  refine WP.of_runBlock ⟨s₂, cat_run r₁ (by
    rw [runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_nil]), ?_⟩
  have P₂ : CPre s₂ k := P.frame fr₂' (by decide) (by decide) consts_notin_io
  apply WP.seq
  refine WP.mono (cipher_ok up P₂ hn (by rw [fr₂.g _ (by decide)]; exact h16)) ?_
  rintro s₃ ⟨hl, fr₃⟩
  let s₄ := s₃.write .x .x4 (s₃.read .x .x17 + BitVec.ofNat _ 0)
  have x4₄ : s₄.gpr .x4 = s.gpr .x4 := by
    show (s₃.write .x .x4 _).gpr .x4 = _
    rw [gpr_write_self]
    show s₃.gpr .x17 + BitVec.ofNat 64 0 = _
    rw [fr₃.g _ (by decide), x17₂]; exact BitVec.add_zero _
  have fr₄ : RFrame batchG roundV s s₄ :=
    (fr₂.trans (fr₃.mono (by decide) (fun _ h => h))).write (by decide) _
  have hW₄ : ∀ j < 8, InRegions s₄.wr (s₄.gpr .x4 + BitVec.ofNat 64 (16 * j)) 16 := fun j hj => by
    rw [fr₄.wr, x4₄]; exact hW j hj
  obtain ⟨s₅, r₅, m₅, f₅, o₅⟩ := storeBatch_run hW₄
  refine WP.of_runBlock ⟨s₅, cat_run (by
    rw [runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_nil]) r₅, ?_⟩
  rw [x4₄] at m₅ f₅
  refine ⟨fun j hj => ?_, ?_, ?_, fun r hr => ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · refine Proof.Blowfish.blockAt_eq _ _ _ fun i hi => ?_
    have hj4 : j / 4 < 4 := by omega_using [hj]
    have hlj : (lane s₃.v aReg j, lane s₃.v bReg j) = foldOut k n up (lane s₂.v aReg j, lane s₂.v bReg j) :=
      hl j hj
    have ha : lane s₂.v aReg j = lane s₁.v aReg j := rfl
    have hb : lane s₂.v bReg j = lane s₁.v bReg j := rfl
    rw [ha, hb, a₁ j hj, b₁ j hj] at hlj
    have hA : lane s₄.v aReg j = lane s₃.v aReg j := rfl
    have hB : lane s₄.v bReg j = lane s₃.v bReg j := rfl
    rw [Offset.add_add, m₅ _ (by omega_using [hj, hi]), outByte, show (8 * j + i) / 8 = j by omega_using [hi],
      show (8 * j + i) % 8 = i by omega_using [hi], blockOut_eq, hA, hB]
    show _ = (Spec.Blowfish.encodeBlock (foldOut k n up _).2 (foldOut k n up _).1).getD i 0
    have e1 := congrArg Prod.fst hlj
    have e2 := congrArg Prod.snd hlj
    simp only at e1 e2
    rw [e1, e2]
    rfl
  · have m₄ : s₄.mem = s.mem := fr₄.mem
    rw [← m₄]; exact f₅
  · rw [o₅.gpr, x4₄]
  · rw [o₅.gpr, fr₄.g _ hr]
  · rw [o₅.v _ (fun h => hr (io_sub _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; rcases h with h | h <;> simp [h]))), fr₄.v _ hr]
  · rw [o₅.rd, fr₄.rd]
  · rw [o₅.wr, fr₄.wr]
  · rw [o₅.sp, fr₄.sp]
  · rw [o₅.eq, fr₄.syms]

end VG.Proof.Cast5.AArch64.Tbl
