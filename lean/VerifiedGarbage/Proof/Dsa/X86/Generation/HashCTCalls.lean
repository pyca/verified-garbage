module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.HashCTState
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo

/-! # Streaming hash calls have identical traces for the same public buffers -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Pbkdf2.Stream.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)

theorem hashInit_ct {H : Hash} (K : HashOK H) (len : Nat) :
    RelCT isa (Two (HashBaseAt K len)) (H.callInit .ebx) (Two (HashBaseAt K len)) := by
  apply two_post
  · intro s t traceS traceT s' t' hp es et
    obtain ⟨p, Rs, Rt⟩ := hp
    exact init_rel K (P := fun a b => HashBaseAt K len p a ∧ HashBaseAt K len p b)
      (sp := p.sp) (st := p.scratch + 512#32)
      (fun _ _ h => ⟨h.1.1.resources.init h.1.2, h.2.1.resources.init h.2.2, h.1.1.esp, h.2.1.esp⟩)
      s t traceS traceT s' t' ⟨Rs, Rt⟩ es et
  · intro p s R
    exact init_frame K (R.1.resources.init R.2) fun t A _ =>
      ⟨R.1.after A, (A.cs .ebx (by decide)).trans R.2⟩

theorem hashUpdate_ct {H : Hash} (K : HashOK H) (len : Nat) :
    RelCT isa (Two (HashUpdateAt K len))
      (.frame (.push [.ebp, .ecx, .edx, .eax, .eax, .ebx]) (.call H.updN H.updC) (.pop .eax 6))
      (Two (HashBaseAt K len)) := by
  apply two_post
  · intro s t traceS traceT s' t' hp es et
    obtain ⟨p, Rs, Rt⟩ := hp
    exact upd_rel K (P := fun a b => HashUpdateAt K len p a ∧ HashUpdateAt K len p b)
      (sp := p.sp) (st := p.scratch + 512#32) (d := p.input) (sc := p.scratch) (c := 0) (len := len)
      (fun _ _ h => ⟨h.1.1.1.resources.update h.1.1.2 h.1.2.1 h.1.2.2.1 h.1.2.2.2 h.1.1.1.ebp,
        h.2.1.1.resources.update h.2.1.2 h.2.2.1 h.2.2.2.1 h.2.2.2.2 h.2.1.1.ebp,
        h.1.1.1.esp, h.2.1.1.esp⟩) s t traceS traceT s' t' ⟨Rs, Rt⟩ es et
  · intro p s R
    exact upd_frame K (R.1.1.resources.update R.1.2 R.2.1 R.2.2.1 R.2.2.2 R.1.1.ebp) fun t A _ =>
      ⟨R.1.1.after A, (A.cs .ebx (by decide)).trans R.1.2⟩

theorem hashFinal_ct {H : Hash} (K : HashOK H) (len : Nat) :
    RelCT isa (Two (HashFinalAt K len))
      (.frame (.push [.ebp, .edx, .ecx, .eax, .ebx]) (.call H.finN H.finC) (.pop .eax 5))
      (fun _ _ => True) := by
  intro s t traceS traceT s' t' hp es et
  obtain ⟨p, Rs, Rt⟩ := hp
  exact fin_rel K (P := fun a b => HashFinalAt K len p a ∧ HashFinalAt K len p b)
    (sp := p.sp) (st := p.scratch + 512#32) (o := p.output) (sc := p.scratch) (lo := BitVec.ofNat 32 len) (hi := 0)
    (fun _ _ h => ⟨h.1.1.1.resources.finalize h.1.1.2 h.1.2.1 h.1.2.2.1 h.1.2.2.2 h.1.1.1.ebp,
      h.2.1.1.resources.finalize h.2.1.2 h.2.2.1 h.2.2.2.1 h.2.2.2.2 h.2.1.1.ebp,
      h.1.1.1.esp, h.2.1.1.esp⟩) s t traceS traceT s' t' ⟨Rs, Rt⟩ es et
end VG.Proof.Dsa.X86.Generation
