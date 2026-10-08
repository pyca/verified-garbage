import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.HashBatch
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Cursor

/-! # One iteration of either public-length loop -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Spec.Gcm (Block)

def threshold (dec : Bool) : Nat := if dec then 16 else 24

def tailSize (dec : Bool) : Nat := if dec then 8 else 16

structure LoopInv (s₀ : State) (P : Nat → Block) (dec : Bool) (g : Nat) (s : State) : Prop where
  core : CoreInv s₀ P dec (g + lead dec) g s
  buffered : Buffered s₀ dec g s.mem
  multiple : g % 8 = 0
  tail_le : g + tailSize dec ≤ nb s₀

def body8 (dec : Bool) (nr : Nat) : Prog isa :=
  .seq (.block []) (.seq (Impl.Gcm.X86_64.StitchAvx8.batch nr 8 (lead dec)
    (Impl.Gcm.X86_64.StitchAvx8.q8 nr true))
    (.block [.alu .add .rdx (.imm 128), .alu .sub .r9 (.imm 8),
      .alu .cmp .r9 (.imm (if dec then 16 else 24))]))

theorem body8_enc (nr : Nat) : body8 false nr = Impl.Gcm.X86_64.StitchAvx8.encBody8 nr := rfl
theorem body8_dec (nr : Nat) : body8 true nr = Impl.Gcm.X86_64.StitchAvx8.decBody8 nr := rfl

theorem loopStep_ok {s₀ s : State} {P : Nat → Block} {dec : Bool} {g : Nat}
    (hp : SPre s₀) (hlaw : HashLaw s₀ P) (h : LoopInv s₀ P dec g s)
    (hn : g + threshold dec ≤ nb s₀) :
    WP isa (body8 dec (nr s₀)) s fun t => LoopInv s₀ P dec (g + 8) t ∧
      t.cf = some (decide (nb s₀ - (g + 8) < threshold dec)) := by
  have hc : g + lead dec + 8 ≤ nb s₀ := by cases dec <;> simp [threshold, lead] at hn ⊢ <;> omega
  have h16 : g + 16 ≤ nb s₀ := by cases dec <;> simp [threshold] at hn <;> omega
  have htail : g + 8 + tailSize dec ≤ nb s₀ := by cases dec <;> simp [threshold, tailSize] at hn ⊢ <;> omega
  have hec : g + lead dec + 8 = g + 8 + lead dec := by omega
  have hm := h.multiple
  have hn64 : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  refine WP.seq (WP.block_nil (WP.seq (WP.mono
    (h.core.hashBatch hp rfl h.buffered true hc (fun _ => h16)) fun u hu => ?_)))
  refine WP.mono (next8_ok u (if dec then 16 else 24)) fun t ⟨htD, htN, htC, htG, htX, htM, htR, htW⟩ => ?_
  have un : u.gpr .r9 = BitVec.ofNat 64 (nb s₀ - g) :=
    (hu.regs _ (by decide) (by decide)).trans h.core.remaining
  have un8 : u.gpr .r9 - 8 = BitVec.ofNat 64 (nb s₀ - (g + 8)) := by
    rw [un]
    change BitVec.ofNat 64 (nb s₀ - g) - BitVec.ofNat 64 8 = _
    rw [Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  have hlimit : ((if dec then 16 else 24 : BitVec 32).signExtend 64).toNat = threshold dec := by
    cases dec <;> rfl
  have hDt := h.core.data.batch hp hc (by rw [h.core.addr]) hu
  rw [hec] at hDt
  refine ⟨⟨⟨hu.env.move (fun r _ hdx _ h9 => htG r hdx h9) htM htR htW,
    htM ▸ hDt, ?_, ?_, ?_, htN.trans un8, ?_, by omega, by omega⟩, ?_, by omega, htail⟩, ?_⟩
  · rw [htM, ← hec]; exact hu.templates
  · rw [htG _ (by decide) (by decide), hu.counter]
    congr 2
    omega
  · rw [htD, hu.regs _ (by decide) (by decide), h.core.cursor]
    exact bAddr_add s₀ g 8
  · rw [htX, hu.hash]
    change VG.Proof.Gcm.X86_64.Pclmul.reduceB (accN (window s₀ dec g) P (hashPrefix s₀ dec g) 8) = _
    rw [hlaw]
    exact (ghash_append8 (hk s₀) (y₀ s₀) (hashBlock s₀ dec) g).symm
  · intro i hi
    rw [htM]
    have hb := hu.prepared.done i hi
    simpa only [window, Nat.add_assoc, Bool.true_eq, ite_true] using hb
  · rw [htC, un8, hlimit, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

end VG.Proof.Gcm.X86_64.StitchAvx8
