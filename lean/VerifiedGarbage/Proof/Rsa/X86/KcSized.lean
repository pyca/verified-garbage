module

public import VerifiedGarbage.Proof.Rsa.X86.KcResult
public import VerifiedGarbage.Proof.Rsa.X86.KcLoads
import VerifiedGarbage.Proof.Rsa.X86.KcLoad
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
import VerifiedGarbage.Proof.Rsa.X86.InvParts
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Spec.RsaKeyGen

/-! # Complete key validation at the selected public word width -/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.KeyCheck
open VG.Proof.Rsa.X86.Keys

theorem sized_ok {g : CallGeometry} {s : State} (h : Inputs g s) (len : Lengths g)
    (b : Bounds (geometry g) (g.args 1).toNat (numbers g s.mem))
    (hm : Spec.Rsa.modulusValid (numbers g s.mem).n (g.args 1).toNat = true)
    (he : Spec.Rsa.exponentValid (numbers g s.mem).e = true) :
    WP isa (VG.Impl.Rsa.X86.KeyCheckRt.sized g.full) s fun t => Inputs g t ∧
      t.gpr .eax = BitVec.ofNat 32 (validity g.full (g.args 1).toNat (numbers g s.mem)).toNat ∧
      Outside g.base 16 (g.size - 16) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have kwEq : VG.Proof.Rsa.X86.KeyRt.kw (g.args 1).toNat = 2 * g.n := by rw [len.width]
  unfold VG.Impl.Rsa.X86.KeyCheckRt.sized
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (loads_ok h len) fun u ⟨hu, bu, fu, ru⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (checks_ok bu b hm he) fun v ⟨A, live, hv⟩ => ?_
  have full := VG.Proof.Rsa.X86.KeyRt.keep_outside bu.ws.ws hv.keep (fun j hj => List.mem_range.mp hj) (by decide)
  have keep' : Keep g.base (2 * g.n) (List.range nArr) bodySlots u.mem v.mem := by rw [← kwEq]; exact hv.keep
  have body := hu.keepBody keep' (fun j hj => List.mem_range.mp hj) (by decide)
  have iv := hu.after hv.rest (by decide) (by decide) (hu.scratchFrame full)
  refine wp_movS (readSrc_sc iv.ws.workspace (by have := iv.ws.hdr_le; unfold sMask hdr at *; omega))
    fun t T _ => WP.block_nil ?_
  refine ⟨iv.after T.keeps (by decide) (by decide) (by rw [T.mem]; exact Frame.refl _ _), ?_, ?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    rw [T.gpr]
    change slot v.mem (geometry g).B sMask = _
    rw [hv.mask, show (geometry g).full = g.full from rfl]; cases validity g.full (g.args 1).toNat (numbers g s.mem) <;> rfl
  · rw [T.mem]; exact fu.trans body
  · exact ru.trans ((hv.rest.mono (by decide)).trans (T.keeps.mono (by decide)))
/-- The checks run, whatever the numbers. -/
theorem bodies_ok {g : Geo} {v : Vals} {s : State} (h : BodyIn g v s) :
    WP isa (if g.full then VG.Impl.Rsa.X86.KeyCheckRt.keyBody g.full else VG.Impl.Rsa.X86.KeyCheckRt.crtBody g.full) s
      fun t => ∃ A live c, Stg g s A live c t := by
  obtain ⟨B, Z, len, full⟩ := g
  cases full
  · exact WP.mono (crtBody_ok h) fun _ ⟨_, _, _, _, _, _, _, ht⟩ => ⟨_, _, _, ht⟩
  · exact WP.mono (keyBody_ok h) fun _ ⟨_, _, _, _, _, _, _, _, _, _, _, A, live, ht⟩ => ⟨A, live, _, ht⟩

/-- `sized` runs from `Inputs`, whatever the numbers. -/
theorem sized_wp {g : CallGeometry} {s : State} (h : Inputs g s) (len : Lengths g) :
    WP isa (VG.Impl.Rsa.X86.KeyCheckRt.sized g.full) s fun t => Inputs g t := by
  unfold VG.Impl.Rsa.X86.KeyCheckRt.sized
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (loads_ok h len) fun u ⟨hu, bu, _, _⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (bodies_ok bu) fun v ⟨A, live, c, hv⟩ => ?_
  have full := VG.Proof.Rsa.X86.KeyRt.keep_outside bu.ws.ws hv.keep (fun j hj => List.mem_range.mp hj) (by decide)
  have iv := hu.after hv.rest (by decide) (by decide) (hu.scratchFrame full)
  refine wp_movS (readSrc_sc iv.ws.workspace (by have := iv.ws.hdr_le; unfold sMask hdr at *; omega))
    fun t T _ => WP.block_nil ?_
  exact iv.after T.keeps (by decide) (by decide) (by rw [T.mem]; exact Frame.refl _ _)

end VG.Proof.Rsa.X86.KeyCheck
