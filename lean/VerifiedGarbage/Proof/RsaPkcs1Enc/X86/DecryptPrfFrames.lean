module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptMacMemory

/-! # The HMAC stages of a PRF block write only their states and one digest -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt

def prfMacWrites (g : Geometry) (dst : Nat) : List Region :=
  [g.scratch sSt 96, g.scratch sOuter 96, g.scratch sHash 832,
    g.scratch dst 32, ⟨byteAddr g.stack, 80⟩, g.calleeRegion]

theorem initFrame_prf {g : Geometry} {m m' : Mem} (dst : Nat)
    (F : Frame ((macInitWr g ++ [g.calleeRegion]) ++ [⟨byteAddr g.stack, 80⟩]) m m') :
    Frame (prfMacWrites g dst) m m' := F.sub (by
  intro r hr
  simp only [List.mem_append, macInitWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with ((rfl | rfl | rfl | rfl) | rfl) | rfl
  · exact ⟨_, by simp [prfMacWrites], fun _ hx => hx⟩
  · exact ⟨_, by simp [prfMacWrites], fun _ hx => hx⟩
  · exact ⟨_, by simp [prfMacWrites], fun _ hx => hx⟩
  · exact ⟨⟨byteAddr g.stack, 80⟩, by simp [prfMacWrites], Region.sub_prefix (by decide : 20 ≤ 80)⟩
  · exact ⟨_, by simp [prfMacWrites], fun _ hx => hx⟩
  · exact ⟨_, by simp [prfMacWrites], fun _ hx => hx⟩)

theorem updateFrame_prf {g : Geometry} {m m' : Mem} (dst : Nat)
    (F : Frame ((updateWr g ++ [g.calleeRegion]) ++ [⟨byteAddr g.stack, 80⟩]) m m') :
    Frame (prfMacWrites g dst) m m' := F.sub (by
  intro r hr
  simp only [List.mem_append, updateWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with ((rfl | rfl | rfl) | rfl) | rfl
  · exact ⟨_, by simp [prfMacWrites], fun _ hx => hx⟩
  · exact ⟨g.scratch sHash 832, by simp [prfMacWrites], Region.sub_prefix (by decide : 608 ≤ 832)⟩
  · exact ⟨⟨byteAddr g.stack, 80⟩, by simp [prfMacWrites], Region.sub_prefix (by decide : 24 ≤ 80)⟩
  · exact ⟨_, by simp [prfMacWrites], fun _ hx => hx⟩
  · exact ⟨_, by simp [prfMacWrites], fun _ hx => hx⟩)

theorem finalizeFrame_prf {g : Geometry} {m m' : Mem} {dst : Nat}
    (F : Frame ((macFinalizeWr g dst ++ [g.calleeRegion]) ++ [⟨byteAddr g.stack, 80⟩]) m m') :
    Frame (prfMacWrites g dst) m m' := F.sub (by
  intro r hr
  simp only [List.mem_append, macFinalizeWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with ((rfl | rfl | rfl | rfl) | rfl) | rfl
  · exact ⟨_, by simp [prfMacWrites], fun _ hx => hx⟩
  · exact ⟨_, by simp [prfMacWrites], fun _ hx => hx⟩
  · exact ⟨_, by simp [prfMacWrites], fun _ hx => hx⟩
  · exact ⟨⟨byteAddr g.stack, 80⟩, by simp [prfMacWrites], Region.sub_prefix (by decide : 24 ≤ 80)⟩
  · exact ⟨_, by simp [prfMacWrites], fun _ hx => hx⟩
  · exact ⟨_, by simp [prfMacWrites], fun _ hx => hx⟩)

end VG.Proof.RsaPkcs1Enc.X86.Dec
