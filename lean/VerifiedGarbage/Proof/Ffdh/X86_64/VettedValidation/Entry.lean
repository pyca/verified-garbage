module

public import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.Geometry
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.State

/-! Saving public arguments writes only the existing scratch buffer. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86_64.VettedValidation
open VG VG.X86_64 VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.VettedValidation

def entryMem (s : State) : Mem :=
  (s.mem.writeW (s.gpr .rcx + BitVec.ofNat 64 128) (s.gpr .rsi)).writeW
    (s.gpr .rcx + BitVec.ofNat 64 136) (s.gpr .rdx)

theorem entry_ok {s : State} (g : Geometry s) :
    WP isa (.block entry) s fun t =>
      t.gpr .r9 = s.gpr .rcx ∧ t.mem = entryMem s ∧ Keep [.r9] s t := by
  have first : InRegions s.wr (s.gpr .rcx + BitVec.ofNat 64 128) 8 :=
    g.scratch.region (by have := g.room; omega) (by decide)
  have second : InRegions s.wr (s.gpr .rcx + BitVec.ofNat 64 136) 8 :=
    g.scratch.region (by have := g.room; omega) (by decide)
  refine WP.mono (WP.keep [.r9] (Q := fun t =>
    t.gpr .r9 = s.gpr .rcx ∧ t.mem = entryMem s) ?_ rfl) ?_
  · xrun [entry, entryMem, first, second]
  · rintro t ⟨⟨base, mem⟩, rest⟩
    exact ⟨base, mem, rest⟩

theorem entryMem_frame {s : State} (g : Geometry s) :
    Frame [⟨s.gpr .rcx, (s.gpr .r8).toNat * 8⟩] s.mem (entryMem s) := by
  unfold entryMem
  exact ((Frame.refl _ _).writeW List.mem_cons_self (s.gpr .rsi)
    (Offset.contains_base _ (by have := g.room; omega) (by decide))).writeW
      List.mem_cons_self (s.gpr .rdx)
        (Offset.contains_base _ (by have := g.room; omega) (by decide))

theorem entryMem_saved (s : State) :
    (entryMem s).readW (s.gpr .rcx + BitVec.ofNat 64 128) 64 = s.gpr .rsi ∧
    (entryMem s).readW (s.gpr .rcx + BitVec.ofNat 64 136) 64 = s.gpr .rdx := by
  constructor
  · rw [entryMem, Mem.readW_writeW_sep
      (Offset.sep _ (d := 128) (n := 8) (e := 136) (k := 8)
        (by decide) (by decide) (by decide)) (by decide), Mem.readW_writeW_self64]
  · exact Mem.readW_writeW_self64 _ _ _

theorem entry_context {s t : State} (g : Geometry s)
    (base : t.gpr .r9 = s.gpr .rcx) (mem : t.mem = entryMem s) (rest : Keep [.r9] s t) :
    Context (s.gpr .rcx) (s.gpr .rdi) (s.gpr .rdx).toNat (CheckDomain.cdDom s) t := by
  have length : (CheckDomain.cdDom s).length = (s.gpr .rsi).toNat := by
    simp only [CheckDomain.cdDom, Spec.Rsa.bytesAt, List.length_map, List.length_range]
  have frame := entryMem_frame g
  have same := entryMem_saved s
  have read (d : Nat) (fit : d + 8 ≤ (s.gpr .r8).toNat * 8) :
      InRegions (t.rd ++ t.wr) (s.gpr .rcx + BitVec.ofNat 64 d) 8 := by
    rw [rest.2.1, rest.2.2]
    obtain ⟨r, member, contains⟩ := g.scratch.region fit (by decide)
    exact ⟨r, List.mem_append_right _ member, contains⟩
  refine ⟨base, rest.gpr (by decide), ?_, ?_, read 128 (by have := g.room; omega),
    read 136 (by have := g.room; omega), ?_, ?_, by rw [length]; exact g.shape, g.lower, g.upper⟩
  · rw [mem, same.1, length, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [mem, same.2, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [rest.2.1, rest.2.2, length]
    exact g.read
  · rw [mem, length, VG.Proof.Rsa.rsa_bytes_frame frame
      (by have := (s.gpr .rsi).isLt; omega)
      (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact g.separate)]

end VG.Proof.Ffdh.X86_64.VettedValidation
