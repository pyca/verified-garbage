module

public import VerifiedGarbage.Proof.RsaPss.X86_64.Checks
public import VerifiedGarbage.Proof.RsaPss.X86_64.TabCall
public import VerifiedGarbage.Proof.RsaPss.X86_64.Safe
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaPss.X86_64.Checks
meta import VerifiedGarbage.Proof.RsaPss.X86_64.TabCall
meta import VerifiedGarbage.Proof.RsaPss.X86_64.Safe
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# RSASSA-PSS on x86-64: the facts of each hash function's shape

`encode` and `checkEncoding` are emitted once for each index of `idxs`, with
the streaming code's parameters and the digest length `shapeOf` gives it
(`ofIdx`): the taint checks of their pieces that depend on these
(`pss_shape`), and what their calls of the digest need of it (`dig_shape`),
for each.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Impl.MdStream.X86_64 (Params)

theorem pss_md5 : PssChecks Impl.Md5.X86_64.Stream.params 16 :=
  ⟨⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
      ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩,
    ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
      ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩,
    ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
      ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
      ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩,
    ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩⟩

theorem pss_sha1 : PssChecks Impl.Sha1.X86_64.Stream.params 20 :=
  ⟨⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
      ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩,
    ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
      ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩,
    ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
      ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
      ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩,
    ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩⟩

theorem pss_sha224 : PssChecks Impl.Sha256.X86_64.Stream.params 28 :=
  ⟨⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
      ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩,
    ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
      ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩,
    ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
      ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
      ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩,
    ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩⟩

theorem pss_sha256 : PssChecks Impl.Sha256.X86_64.Stream.params 32 :=
  ⟨⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
      ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩,
    ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
      ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩,
    ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
      ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
      ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩,
    ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩⟩

theorem pss_sha384 : PssChecks Impl.Sha512.X86_64.Stream.params 48 :=
  ⟨⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
      ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩,
    ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
      ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩,
    ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
      ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
      ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩,
    ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩⟩

theorem pss_sha512 : PssChecks Impl.Sha512.X86_64.Stream.params 64 :=
  ⟨⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
      ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩,
    ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
      ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩,
    ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
      ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
      ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩,
    ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩⟩

theorem pss_sha512_224 : PssChecks Impl.Sha512.X86_64.Stream.params 28 :=
  ⟨⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
      ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩,
    ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
      ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩,
    ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
      ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
      ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩,
    ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩⟩

theorem pss_sha512_256 : PssChecks Impl.Sha512.X86_64.Stream.params 32 :=
  ⟨⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
      ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩,
    ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
      ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩,
    ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
      ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
      ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩,
    ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩⟩

/-- The checks, for the shape of each index. -/
theorem pss_shape : ∀ i ∈ idxs, PssChecks (shapeOf i).1 (shapeOf i).2 := by
  intro i hi
  simp only [idxs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pss_md5
  · exact pss_sha1
  · exact pss_sha224
  · exact pss_sha256
  · exact pss_sha384
  · exact pss_sha512
  · exact pss_sha512_224
  · exact pss_sha512_256

/-! ## The digest -/

/-- `DigOK` depends only on the streaming code's parameters. -/
theorem DigOK.of_P {H H' : Impl.Pbkdf2.Md.X86_64.Hash} (h : H.P = H'.P) (d : DigOK H') : DigOK H := by
  cases H; cases H'; simp only at h; subst h; exact ⟨d.mx, d.sp, d.cl, d.ct⟩

/-- What the calls of the digest need of it, for the parameters `P`. -/
theorem dig_of (P : Params) (hmx : (Impl.MdHashTable.X86_64.digest P).allInstrs (fun i => !loadsMxcsr i) = true)
    (hsp : NoSp (Impl.MdHashTable.X86_64.digest P))
    (hcl : (instrs (Impl.MdHashTable.X86_64.digest P)).all (fun i =>
      [Reg.rcx, .rdx, .rsi, .rdi, .rsp, .r10, .r11, .r12, .r13, .r14, .r15].all fun r => !Taint.clobbers i r) = true)
    (hct : ∃ hc, (taint.check (Taint.ofRegs [.rdi, .rsi]) (Impl.MdHashTable.X86_64.digest P) hc).isSome = true) :
    DigOK (ckH P 0) :=
  ⟨hmx, hsp, fun r hr i hi => by
      have h := List.all_eq_true.mp (List.all_eq_true.mp hcl i hi) r (by cases r <;> simp_all)
      simpa using h, fun _ => VG.Taint.constantTime_of_exists (A := taint) (Taint.ofRegs [.rdi, .rsi])
    (fun _ _ _ _ hp => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.1
      · exact hp.2) hct⟩

theorem dig_md5 : DigOK (ckH Impl.Md5.X86_64.Stream.params 0) :=
  dig_of _ (by decide) (by decide) (by decide) ⟨_, by taint_decide⟩
theorem dig_sha1 : DigOK (ckH Impl.Sha1.X86_64.Stream.params 0) :=
  dig_of _ (by decide) (by decide) (by decide) ⟨_, by taint_decide⟩
theorem dig_sha256 : DigOK (ckH Impl.Sha256.X86_64.Stream.params 0) :=
  dig_of _ (by decide) (by decide) (by decide) ⟨_, by taint_decide⟩
theorem dig_sha512 : DigOK (ckH Impl.Sha512.X86_64.Stream.params 0) :=
  dig_of _ (by decide) (by decide) (by decide) ⟨_, by taint_decide⟩

/-- What the calls of the digest need of it, for the shape of each index. -/
theorem dig_shape : ∀ i ∈ idxs, DigOK (ckH (shapeOf i).1 0) := by
  intro i hi
  simp only [idxs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact dig_md5
  · exact dig_sha1
  · exact dig_sha256
  · exact dig_sha256
  · exact dig_sha512
  · exact dig_sha512
  · exact dig_sha512
  · exact dig_sha512

/-- The digest neither writes `rsp` nor loads MXCSR, and uses no stack, for
the shape of each index. -/
theorem dig_safe : ∀ i ∈ idxs, (Impl.MdHashTable.X86_64.digest (shapeOf i).1).allInstrs safeI = true ∧
    (Impl.MdHashTable.X86_64.digest (shapeOf i).1).x86_64Depth ≤ 0 := by
  intro i hi
  simp only [idxs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩

end VG.Proof.RsaPss.X86_64
