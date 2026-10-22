module

public import VerifiedGarbage.Proof.EcKey.Compressed.X86.Contract
public import VerifiedGarbage.Proof.Framework.X86.Taint

/-! # Public cdecl arguments and stack room for x86 point conversion -/

@[expose] public section
namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86

def codecT (outputLen : Nat) : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [outputLen, 8192],
    argLen := 16, argBases := [(4, 0), (12, 1)], room := 28 }

theorem codec_wf {inputLen outputLen : Nat} {s : State}
    (hp : codecPre inputLen outputLen false s) : VG.X86.Taint.Wf (codecT outputLen) s := by
  obtain ⟨_, hwr, how, _, _, hao, haw, hro, hrw, hof, _, hwf, hsf, hlo, hso, hsw⟩ := hp
  simp only [Bool.false_eq_true, ite_false] at hwr
  refine VG.X86.Taint.Wf.entryRoom rfl
    ⟨fun _ => ⟨by simp [hwr, codecT], ?_, ?_⟩,
      fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
      fun _ => ⟨hsf, ?_⟩, ?_⟩ fun _ => ⟨hlo, ?_⟩
  · simpa [hwr] using how
  · intro r hr
    rw [hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [BitVec.toNat_setWidth] <;> omega
  · intro r hr
    rw [hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact VG.X86.Taint.frame_disjoint (n := 12) (by omega) hro hao
    · exact VG.X86.Taint.frame_disjoint (n := 12) (by omega) hrw haw
  · intro p hp'
    simp only [codecT, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by simp [codecT], ?_⟩ <;>
      simp [VG.X86.Taint.region, hwr, addr, arg, argAddr]
  · intro r hr
    rw [hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hso
    · exact hsw

theorem codec_agree {inputLen outputLen : Nat} {s t : State}
    (hs : codecPre inputLen outputLen false s) (ht : codecPre inputLen outputLen false t)
    (hp : s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 ∧ arg s 1 = arg t 1 ∧ arg s 2 = arg t 2) :
    VG.X86.Taint.Agree (codecT outputLen) s t := by
  obtain ⟨hesp, a0, a1, a2⟩ := hp
  refine ⟨⟨?_, fun h => nomatch h⟩, (by intro _; rw [hs.2.1, ht.2.1, a0, a2]; rfl), codec_wf hs, codec_wf ht,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp, ?_⟩
  · intro r hr
    simp only [codecT, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr
    exact hesp
  · intro k h4 hk
    have hsf := hs.2.2.2.2.2.2.2.2.2.2.2.2.1
    have htf := ht.2.2.2.2.2.2.2.2.2.2.2.2.1
    change (s.gpr .esp).toNat + 16 ≤ 2 ^ 32 at hsf
    change (t.gpr .esp).toNat + 16 ≤ 2 ^ 32 at htf
    change k < 16 at hk
    rw [show VG.X86.Taint.depth (codecT outputLen).stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (by omega) h4 hk, VG.X86.Taint.argByte_eq (by omega) h4 hk,
      Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide))]
    have h : (k - 4) / 4 = 0 ∨ (k - 4) / 4 = 1 ∨ (k - 4) / 4 = 2 := by omega
    rcases h with h | h | h <;> rw [h]
    · exact congrArg _ a0
    · exact congrArg _ a1
    · exact congrArg _ a2

end VG.Proof.EcKey.Compressed.X86
