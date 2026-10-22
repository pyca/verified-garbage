module

public import VerifiedGarbage.Proof.MillerRabin.X86.Taint
public import VerifiedGarbage.Proof.MillerRabin.X86.StageMemory
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Relate public inputs to a timing piece without releasing workspace secrets -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86

structure PieceInput (base : Addr) (bytes w : Nat) (sp len : BitVec 32) (s : State) : Prop where
  context : ProtectedContext s base bytes
  room : CallRoom (s.gpr .esp) base bytes
  wr : s.wr = [⟨byteAddr sp, 1132⟩, ⟨base, bytes⟩]
  stack : s.gpr .esp = sp
  capacity : 1600 ≤ bytes
  width : s.mem.readW (off base 48) 32 = BitVec.ofNat 32 w
  length : s.mem.readW (off (byteAddr sp) VG.Impl.MillerRabin.X86.savedLength) 32 = len

theorem public_word_bytes {m m' : Mem} {base : Addr} {d i : Nat}
    (word : m.readW (off base d) 32 = m'.readW (off base d) 32) (lo : d ≤ i) (hi : i < d + 4) :
    m (off base i) = m' (off base i) := by
  have address : off base i = off base d + BitVec.ofNat 64 (i - d) := by
    rw [Offset.add_add, Nat.add_sub_of_le lo]
  rw [address, Mem.readW_byte m (off base d) (i := i - d) (by omega),
    Mem.readW_byte m' (off base d) (i := i - d) (by omega), word]

namespace PieceInput

theorem wf {base : Addr} {bytes w : Nat} {sp len : BitVec 32} {s : State}
    (h : PieceInput base bytes w sp len s) : VG.X86.Taint.Wf pieceTaint s := by
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ?_, ?_, ?_, ?_, ?_⟩
  · rw [h.wr]
    refine ⟨.cons (Nat.le_refl _) (.cons h.capacity .nil), ?_, ?_⟩
    · apply List.pairwise_cons.mpr
      refine ⟨?_, by simp⟩
      intro r hr
      rw [List.mem_singleton.mp hr]
      simpa only [h.stack, VG.Impl.MillerRabin.X86.frameBytes] using h.context.apart.symm
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [byteAddr_toNat, ← h.stack]
        exact h.context.stackFit
      · exact h.context.ws.nowrap
  · intro p hp
    simp only [pieceTaint, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · simp only [VG.X86.Taint.region, h.wr, addr, h.stack]
      rw [BitVec.add_zero]
      rfl
    · simp only [VG.X86.Taint.region, h.wr, addr]
      rw [BitVec.add_zero]
      exact h.context.ws.edi
  · intro p hp
    cases hp
  · intro hp
    exact (Nat.lt_irrefl 0 hp).elim
  · intro p hp
    cases hp

theorem agree {base : Addr} {bytes w : Nat} {sp len : BitVec 32} {s t : State}
    (h : PieceInput base bytes w sp len s) (g : PieceInput base bytes w sp len t) :
    VG.X86.Taint.Agree pieceTaint s t := by
  refine ⟨⟨?_, fun h => nomatch h⟩, fun _ => h.wr.trans g.wr.symm, h.wf, g.wf, ?_, ?_, ?_, ?_⟩
  · intro r hr
    simp only [pieceTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact BitVec.eq_of_toNat_eq (h.context.ws.edi_toNat.trans g.context.ws.edi_toNat.symm)
    · exact h.stack.trans g.stack.symm
  · intro i k hk
    simp only [pieceTaint, Slots.has_add, Slots.has_empty, Bool.false_or, Bool.or_eq_true,
      Bool.and_eq_true, decide_eq_true_eq] at hk
    rcases hk with ⟨⟨rfl, lo⟩, hi⟩ | ⟨⟨rfl, lo⟩, hi⟩
    · change k < 1600
      omega
    · change k < 1132
      change 52 ≤ k at lo
      change k < 56 at hi
      omega
  · intro i k hk
    simp only [pieceTaint, Slots.has_add, Slots.has_empty, Bool.false_or, Bool.or_eq_true,
      Bool.and_eq_true, decide_eq_true_eq] at hk
    rcases hk with ⟨⟨rfl, lo⟩, hi⟩ | ⟨⟨rfl, lo⟩, hi⟩
    · dsimp only [VG.X86.Taint.byteAddr, VG.X86.Taint.region]
      rw [h.wr, g.wr]
      exact public_word_bytes (h.width.trans g.width.symm) lo hi
    · dsimp only [VG.X86.Taint.byteAddr, VG.X86.Taint.region]
      rw [h.wr, g.wr]
      exact public_word_bytes (h.length.trans g.length.symm) lo hi
  · intro hp
    exact (Nat.lt_irrefl 0 hp).elim
  · intro _ _ hp
    exact (Nat.not_lt_zero _ hp).elim

theorem agree_word {base : Addr} {bytes w i d : Nat} {sp len : BitVec 32} {s t : State}
    {rs : List Reg} (h : PieceInput base bytes w sp len s) (g : PieceInput base bytes w sp len t)
    (bounds : d + 4 ≤ pieceTaint.lens.getD i 0)
    (word : s.mem.readW (VG.X86.Taint.byteAddr s i d) 32 = t.mem.readW (VG.X86.Taint.byteAddr t i d) 32)
    (regs : ∀ r ∈ rs, s.gpr r = t.gpr r) : VG.X86.Taint.Agree (wordTaint rs i d) s t := by
  have baseAgree := h.agree g
  refine ⟨⟨?_, fun h => nomatch h⟩, baseAgree.wr, ?_, ?_, ?_, ?_, baseAgree.sp, baseAgree.argMem⟩
  · intro r hr
    simp only [wordTaint, RegSet.mem_ofList, List.mem_append] at hr
    rcases hr with hr | hr
    · exact baseAgree.rf.1 r (by simpa only [pieceTaint, RegSet.mem_ofList] using hr)
    · exact regs r hr
  · exact ⟨baseAgree.wf₁.lens, baseAgree.wf₁.bases, baseAgree.wf₁.wbases, baseAgree.wf₁.args,
      baseAgree.wf₁.argBases, baseAgree.wf₁.stk, baseAgree.wf₁.frames, baseAgree.wf₁.room⟩
  · exact ⟨baseAgree.wf₂.lens, baseAgree.wf₂.bases, baseAgree.wf₂.wbases, baseAgree.wf₂.args,
      baseAgree.wf₂.argBases, baseAgree.wf₂.stk, baseAgree.wf₂.frames, baseAgree.wf₂.room⟩
  · intro j k hk
    simp only [wordTaint, Slots.has_add, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hk
    rcases hk with hk | ⟨⟨eq, lo⟩, hi⟩
    · exact baseAgree.ok j k hk
    · subst j
      change k < pieceTaint.lens.getD i 0
      omega
  · intro j k hk
    simp only [wordTaint, Slots.has_add, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hk
    rcases hk with hk | ⟨⟨eq, lo⟩, hi⟩
    · exact baseAgree.slots j k hk
    · subst j
      have region : VG.X86.Taint.region t i = VG.X86.Taint.region s i := by
        rw [VG.X86.Taint.region, VG.X86.Taint.region, h.wr, g.wr]
      dsimp only [VG.X86.Taint.byteAddr] at word ⊢
      rw [region] at word ⊢
      exact public_word_bytes word lo hi

end PieceInput
end VG.Proof.MillerRabin.X86
