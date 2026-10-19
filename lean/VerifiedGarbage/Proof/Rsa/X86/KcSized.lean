module

public import VerifiedGarbage.Proof.Rsa.X86.KcResult

/-! # Complete key validation at the selected public word width -/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.KeyCheck
open VG.Proof.Rsa.X86.Keys

theorem sized_ok {g : CallGeometry} {s : State} (h : Inputs g s) (k : Nat)
    (b : Bounds (geometry g) k (numbers g s.mem))
    (hm : Spec.Rsa.modulusValid (numbers g s.mem).n k = true)
    (he : Spec.Rsa.exponentValid (numbers g s.mem).e = true) :
    WP isa (sized g.full g.n) s fun t => Inputs g t ∧
      t.gpr .eax = BitVec.ofNat 32 (validity g.full k (numbers g s.mem)).toNat ∧
      Outside g.base 16 (g.size - 16) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold sized
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (loads_ok h) fun u ⟨hu, bu, fu, ru⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (checks_ok bu b hm he g.full) fun v ⟨A, live, hv⟩ => ?_
  have full := hu.keepOutside hv.keep (fun j hj => List.mem_range.mp hj) (by decide)
  have body := hu.keepBody hv.keep (fun j hj => List.mem_range.mp hj) (by decide)
  have iv := hu.after hv.rest (by decide) (by decide) (hu.scratchFrame full)
  refine wp_movS (readSrc_sc iv.ws.workspace (by have := iv.ws.hdr_le; unfold sMask hdr at *; omega))
    fun t T _ => WP.block_nil ?_
  refine ⟨iv.after T.keeps (by decide) (by decide) (by rw [T.mem]; exact Frame.refl _ _), ?_, ?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    rw [T.gpr]
    change slot v.mem (geometry g).B sMask = _
    rw [hv.mask]; cases validity g.full k (numbers g s.mem) <;> rfl
  · rw [T.mem]; exact fu.trans body
  · exact ru.trans ((hv.rest.mono (by decide)).trans (T.keeps.mono (by decide)))
end VG.Proof.Rsa.X86.KeyCheck
