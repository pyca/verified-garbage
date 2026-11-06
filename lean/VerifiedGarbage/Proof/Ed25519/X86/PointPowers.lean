module

public import VerifiedGarbage.Proof.Ed25519.X86.PointTable
import VerifiedGarbage.Proof.Ed25519.X86.Points
public import VerifiedGarbage.Proof.Ed25519.X86.PowerEnv
public import VerifiedGarbage.Proof.Ed25519.ScalarMul
public import VerifiedGarbage.Impl.Ed25519.X86.PointPowers
import VerifiedGarbage.Proof.X25519.X86.Fold
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! Merged from `Proof.Ed25519.X86.PointPowersFrame`. -/

@[expose] public section

section
/-! Merged from `Proof.Ed25519.X86.PointTableAddr`. -/
section
/-! A public table index is multiplied by the point's 128 bytes. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem tableAddr_ok {x : BitVec 32} {s : State} (hc : Ctx x s) (off j : Nat)
    (hj : j < 2 ^ 25) (hb : s.gpr .esi = BitVec.ofNat 32 j) :
    WP isa (.block (tableAddr off)) s fun t =>
      Keep s t ∧ t.mem = s.mem ∧ t.gpr .edx = x + BitVec.ofNat 32 (off + 128 * j) := by
  refine Wp.wp_mov fun s₁ h₁ => Wp.wp_movi fun s₂ h₂ => wp_mul fun s₃ h₃ => ?_
  refine Wp.wp_add fun s₄ h₄ _ => Wp.wp_addi fun s₅ h₅ => Wp.wp_mov fun s₆ h₆ => WP.block_nil ?_
  have hk : Keep s s₆ := (updKeep h₁).trans ((updKeep h₂).trans (h₃.keep.trans
    ((updKeep h₄).trans ((updKeep h₅).trans (updKeep h₆)))))
  have hv : s₃.gpr .eax = BitVec.ofNat 32 (128 * j) := by
    apply BitVec.eq_of_toNat_eq
    change v s₃ .eax = _
    rw [h₃.eax]
    simp only [v, h₂.other .eax (by decide), h₁.gpr, hb, h₂.gpr, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show j < 2 ^ 32 by omega)]
    exact congrArg (fun n => n % 2 ^ 32) (Nat.mul_comm j 128)
  refine ⟨hk, by rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem], ?_⟩
  rw [h₆.gpr, h₅.gpr, h₄.gpr, hv, h₃.other .edi (by decide) (by decide),
    h₂.other .edi (by decide), h₁.other .edi (by decide), hc.edi]
  rw [BitVec.add_comm (BitVec.ofNat 32 (128 * j)) x, BitVec.add_assoc,
    ← BitVec.ofNat_add, Nat.add_comm (128 * j) off]

end VG.Proof.Ed25519.X86
end

/-! Merged from `Proof.Ed25519.X86.PointLoop`. -/

/-! Frames for public counters, arithmetic and point tables. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def PowersFrame (x : BitVec 32) (s : State) (o n : Nat) (m m' : Mem) : Prop :=
  Frame [sub x 24 4, sub x 64 960, sub x o n, callStk s] m m'

structure PowersKeep (x : BitVec 32) (o n : Nat) (s t : State) : Prop where
  edi : t.gpr .edi = s.gpr .edi
  esp : t.gpr .esp = s.gpr .esp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : PowersFrame x s o n s.mem t.mem

theorem PowersKeep.of_ikeep {x : BitVec 32} {s t : State} (h : IKeep x s t) (o n : Nat) :
    PowersKeep x o n s t :=
  ⟨h.edi, h.esp, h.rd, h.wr, h.frame.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl <;> simp only [true_or, or_true]⟩

theorem workspace_table {x : BitVec 32} {s t : State} (h : IKeep x s t) (hc : Ctx x s)
    (o : Nat) (hlo : 1024 ≤ o) (ho : o + 128 ≤ 8192) :
    tablePoint t.mem x o = tablePoint s.mem x o :=
  table_point_of_words fun k hk => wd_frame1s hc h.frame (by decide) (by omega) (Or.inr (by omega))

end VG.Proof.Ed25519.X86
end

/-! Merged from `Proof.Ed25519.X86.PointPowersCounter`. -/

/-! Write the current point, then advance one or sixteen doublings. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem IKeep.of_mem {x : BitVec 32} {s t : State} (h : Keep s t) (hm : t.mem = s.mem) :
    IKeep x s t := ⟨h.edi, h.esp, h.rd, h.wr, by rw [hm]; exact Frame.refl _ _⟩

end VG.Proof.Ed25519.X86
