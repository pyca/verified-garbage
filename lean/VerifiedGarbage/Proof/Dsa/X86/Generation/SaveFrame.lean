module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Entry
public import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameWords
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics

/-! # The outer sixteen-byte frame saves the four callee-saved registers -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86.Generation

structure SaveFrame (s : State) (base : Addr) : Prop where
  esp : (s.gpr .esp).setWidth 64 = base
  write : (⟨base, 16⟩ : Region) ∈ s.wr
  nowrap : base.toNat + 16 ≤ 2 ^ 32

theorem SaveFrame.keep {s t : State} {base : Addr} {rs : List Reg} (F : SaveFrame s base)
    (K : Keeps rs s t) (sp : .esp ∉ rs) : SaveFrame t base :=
  ⟨by rw [K.1 _ sp]; exact F.esp, by rw [K.2.2]; exact F.write, F.nowrap⟩

theorem SaveFrame.address {s : State} {base : Addr} (F : SaveFrame s base) {j : Nat} (h : j < 4) :
    s.ea (VG.Impl.Mont.X86.at_ .esp (4 * j)) = off base (4 * j) := by
  have eq : (s.gpr .esp).toNat = base.toNat := by
    rw [← F.esp, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (s.gpr .esp).isLt (by decide))]
  change addr (s.gpr .esp) (4 * j) = _
  rw [addr_eq (by have := F.nowrap; omega), F.esp]

theorem SaveFrame.read {s : State} {base : Addr} (F : SaveFrame s base) {j : Nat} (h : j < 4) :
    readSrc s (.mem (VG.Impl.Mont.X86.at_ .esp (4 * j))) = some (s.mem.readW (off base (4 * j)) 32) := by
  change s.load32 _ = _
  rw [F.address h, State.load32]
  apply ite_eq_left
  exact ⟨_, List.mem_append_right _ F.write, Offset.contains_base _ (by omega) (by omega)⟩

def SavedRegisters (original : State) (base : Addr) (mem : Mem) : Prop :=
  mem.readW (off base 0) 32 = original.gpr .ebx ∧ mem.readW (off base 4) 32 = original.gpr .ebp ∧
  mem.readW (off base 8) 32 = original.gpr .esi ∧ mem.readW (off base 12) 32 = original.gpr .edi

theorem saveWord_ok {s : State} {base : Addr} {W : Nat → BitVec 32} {j : Nat} (r : Reg)
    (F : SaveFrame s base) (words : FrameWords s.mem base W) (h : j < 4) :
    WP isa (.block [.store (VG.Impl.Mont.X86.at_ .esp (4 * j)) r]) s fun t =>
      SaveFrame t base ∧ FrameWords t.mem base (frameUpdate W j (s.gpr r)) ∧
      Frame [⟨base, 16⟩] s.mem t.mem ∧ Keeps [] s t := by
  refine wp_storeS (F.address h) ⟨_, F.write, Offset.contains_base _ (by omega) (by omega)⟩
    fun t st => WP.block_nil ?_
  exact ⟨F.keep (st.keeps []) (by decide), by rw [st.mem]; exact words.write (by omega) _,
    by rw [st.mem]; exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega)),
    st.keeps []⟩

theorem saveRegisters_ok {s : State} {base : Addr} (F : SaveFrame s base) :
    WP isa (.block saveRegisters) s fun t => SaveFrame t base ∧ SavedRegisters s base t.mem ∧
      Frame [⟨base, 16⟩] s.mem t.mem ∧ Keeps [] s t := by
  let W : Nat → BitVec 32 := fun i => s.mem.readW (off base (4 * i)) 32
  have words : FrameWords s.mem base W := fun _ _ => rfl
  change WP isa (.block ([_] ++ [_] ++ [_] ++ [_])) s _
  rw [List.append_assoc, List.append_assoc]
  refine WP.block_append (WP.mono (saveWord_ok .ebx F words (by decide : 0 < 4)) fun a ⟨Fa, Wa, Oa, Ka⟩ => ?_)
  refine WP.block_append (WP.mono (saveWord_ok .ebp Fa Wa (by decide : 1 < 4)) fun b ⟨Fb, Wb, Ob, Kb⟩ => ?_)
  refine WP.block_append (WP.mono (saveWord_ok .esi Fb Wb (by decide : 2 < 4)) fun c ⟨Fc, Wc, Oc, Kc⟩ => ?_)
  refine WP.mono (saveWord_ok .edi Fc Wc (by decide : 3 < 4)) fun t ⟨Ft, Wt, Ot, Kt⟩ => ?_
  have ab : a.gpr .ebp = s.gpr .ebp := Ka.1 _ (by decide)
  have bs : b.gpr .esi = s.gpr .esi := (Ka.trans Kb).1 _ (by decide)
  have cd : c.gpr .edi = s.gpr .edi := ((Ka.trans Kb).trans Kc).1 _ (by decide)
  refine ⟨Ft, ⟨Wt 0 (by decide), ?_, ?_, ?_⟩, Oa.trans (Ob.trans (Oc.trans Ot)), Ka.trans (Kb.trans (Kc.trans Kt))⟩
  · exact (Wt 1 (by decide)).trans ab
  · exact (Wt 2 (by decide)).trans bs
  · exact (Wt 3 (by decide)).trans cd
end VG.Proof.Dsa.X86.Generation
