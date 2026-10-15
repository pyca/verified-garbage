module

public import VerifiedGarbage.Proof.Dsa.X86.StreamAgreement

/-! # Reusing the streaming certificate inside a larger caller workspace -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86

def streamNarrow (base : Addr) (size : Nat) (s : State) : State :=
  s.withRegions (s.rd ++ s.wr) [⟨base, size⟩]

theorem streamNarrow_context {s : State} {n m size : Nat} {base : Addr}
    (C : Context n m base size s) : Context n m base size (streamNarrow base size s) :=
  ⟨⟨C.scr.edi, List.mem_singleton_self _, C.scr.nowrap, C.scr.stk⟩,
    C.size_le, C.modulus, C.gt_one, C.inverse⟩

theorem streamNarrow_input {s : State} {n size len : Nat} {base : Addr} {ptr : BitVec 32}
    (I : StreamInput s base (contextBytes n) ptr len) :
    StreamInput (streamNarrow base size s) base (contextBytes n) ptr len := by
  refine ⟨I.fit, ?_, I.far⟩
  intro i hi
  obtain ⟨r, hr, hc⟩ := I.read i hi
  exact ⟨r, List.mem_append_left _ hr, hc⟩

theorem streamNarrow_trace {s t : State} {n size m len : Nat} {base : Addr} {ptr : BitVec 32} {trace : List Leak}
    (C : Context n m base size s) (hm : 255 < m) (hlen : len < 2 ^ 32)
    (I : StreamInput s base (contextBytes n) ptr len) (P : s.mem.readW (off base sourcePointer) 32 = ptr)
    (E : Exec isa (reduceStream n len) s trace t) :
    ∃ u, Exec isa (reduceStream n len) (streamNarrow base size s) trace u := by
  obtain ⟨tr, u, U, _⟩ := reduceStream_ok (streamNarrow_context C) hm hlen (streamNarrow_input I) P
  have W := Exec.widen U (rd := s.rd) (wr := s.wr) (by
    intro a k ⟨r, hr, hc⟩
    change r ∈ (s.rd ++ s.wr) ++ [⟨base, size⟩] at hr
    rcases List.mem_append.mp hr with h | h
    · exact ⟨r, h, hc⟩
    · obtain rfl := List.mem_singleton.mp h
      exact ⟨_, List.mem_append_right _ C.scr.wr, hc⟩) (by
    intro a k ⟨r, hr, hc⟩
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, C.scr.wr, hc⟩)
  have W' : Exec isa (reduceStream n len) s tr (u.withRegions s.rd s.wr) := W
  obtain ⟨rfl, _⟩ := Exec.det E W'
  exact ⟨u, U⟩

theorem reduceStream_relCT (n len size : Nat) (base : Addr) (ptr : BitVec 32)
    (hn : n = 3 ∨ n = 4) (hz : 1408 ≤ size) (hlen : len < 2 ^ 32) :
    RelCT isa (fun s t => ∃ m₁ m₂,
      Context n m₁ base size s ∧ Context n m₂ base size t ∧ 255 < m₁ ∧ 255 < m₂ ∧
      StreamInput s base (contextBytes n) ptr len ∧ StreamInput t base (contextBytes n) ptr len ∧
      s.mem.readW (off base sourcePointer) 32 = ptr ∧ t.mem.readW (off base sourcePointer) 32 = ptr)
      (reduceStream n len) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  intro s t tr ur sf tf ⟨m₁, m₂, C₁, C₂, M₁, M₂, I₁, I₂, P₁, P₂⟩ E F
  obtain ⟨u, U⟩ := streamNarrow_trace C₁ M₁ hlen I₁ P₁ E
  obtain ⟨v, V⟩ := streamNarrow_trace C₂ M₂ hlen I₂ P₂ F
  have A := stream_agree (streamNarrow_context C₁).scr (streamNarrow_context C₂).scr rfl rfl hz (P₁.trans P₂.symm)
  refine ⟨reduceStream_constantTime n len hn _ _ _ _ _ _ trivial trivial A U V, ?_⟩
  obtain ⟨D₁, _, _, _⟩ := wp_result (reduceStream_ok C₁ M₁ hlen I₁ P₁) E
  obtain ⟨D₂, _, _, _⟩ := wp_result (reduceStream_ok C₂ M₂ hlen I₂ P₂) F
  apply agree_regs (rs := [.edi])
  intro reg hr
  obtain rfl := List.mem_singleton.mp hr
  exact BitVec.eq_of_toNat_eq (D₁.scr.edi_toNat.trans D₂.scr.edi_toNat.symm)

end VG.Proof.Dsa.X86
