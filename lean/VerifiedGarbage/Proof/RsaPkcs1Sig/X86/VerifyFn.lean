module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyReturn
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignRestore

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyBody
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyNoSp
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyEntryCache

/-! # Callable PKCS #1 signing restores the i686 calling convention -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Ver
open VG VG.X86 VG.Impl.RsaPkcs1Sig.X86.Verify VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Proof.Dsa.X86 (allocated freed freed_esp freed_gpr)

theorem verifyFn_ok (v : PublicImpl) (s : State) {g : Geometry} {bs : Fin 5 → List Byte}
    (h : FnInput g bs s) :
    WP isa (code v.name v.code) s fun t => abiPreserved s t ∧
      (Precomputed g bs s → t.gpr .eax = verifiedResult g bs) := by
  have stackFit : 16 ≤ (s.gpr .esp).toNat := by
    have := h.stackFit; unfold verifyStack at this; omega
  have allocation : VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes ≤ ((pushed savedRegisters s).gpr .esp).toNat := by
    rw [pushed_esp, show 4 * savedRegisters.length = 16 from rfl, sub_toNat stackFit]
    have := h.stackFit
    simp only [verifyStack, VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes] at *
    omega
  unfold code
  refine WP.frame (rs := savedRegisters) (by decide) (by decide) (by decide) stackFit
    (inner_noSp v) ?_
  refine WP.seq ?_
  refine VG.Proof.Dsa.X86.WP.alloc (by decide) allocation (body_noSp v) ?_
  refine WP.mono (body_ok v (s := entered s) h.context) ?_
  rintro u ⟨_, frame, rest, result⟩
  have spU : (freed VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes u).gpr .esp =
      (pushed savedRegisters s).gpr .esp := by
    rw [freed_esp, rest.1 .esp (by decide)]
    exact BitVec.sub_add_cancel _ _
  have wrU : (freed VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes u).wr = (pushed savedRegisters s).wr := by
    change u.wr.tail = _
    rw [rest.2.2]; rfl
  have fit : ((pushed savedRegisters s).gpr .esp).toNat + 16 ≤ 2 ^ 32 := by
    rw [pushed_esp, show 4 * savedRegisters.length = 16 from rfl, sub_toNat stackFit]
    have := (s.gpr .esp).isLt
    omega
  have read (d : Nat) (hd : d + 4 ≤ 16) :
      InRegions ((freed VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes u).rd ++
        (freed VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes u).wr)
        (addr ((freed VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes u).gpr .esp) d) 4 := by
    rw [spU, wrU, pushed_wr]
    refine ⟨below (s.gpr .esp) 16, List.mem_append_right _ (List.mem_cons_self), ?_⟩
    change (⟨((s.gpr .esp - 16).setWidth 64), 16⟩ : Region).Contains
      (((pushed savedRegisters s).gpr .esp + BitVec.ofNat 32 d).setWidth 64) 4
    rw [show (s.gpr .esp - 16) = (pushed savedRegisters s).gpr .esp from (pushed_esp savedRegisters s).symm]
    change (⟨byteAddr ((pushed savedRegisters s).gpr .esp), 16⟩ : Region).Contains
      (byteAddr ((pushed savedRegisters s).gpr .esp + BitVec.ofNat 32 d)) 4
    rw [byteAddr_add (by omega : ((pushed savedRegisters s).gpr .esp).toNat + d < 2 ^ 32)]
    exact Offset.contains_base _ hd (by omega)
  refine WP.mono (VG.Proof.RsaPkcs1Sig.X86.Sgn.restore_ok (freed VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes u)
    (read 4 (by decide)) (read 8 (by decide)) (read 0 (by decide))) ?_
  rintro t ⟨edi, ebp, esi, memT, restT⟩
  have spT : t.gpr .esp = (pushed savedRegisters s).gpr .esp :=
    (restT.1 .esp (by decide)).trans spU
  have words (i : Nat) (hi : i < 4) := h.savedWord frame i hi
  have mem : t.mem = u.mem := memT
  have savedEdi : t.gpr .edi = s.gpr .edi := by
    rw [edi, spU]; exact words 0 (by decide)
  have savedEbp : t.gpr .ebp = s.gpr .ebp := by
    rw [ebp, spU]; exact words 2 (by decide)
  have savedEsi : t.gpr .esi = s.gpr .esi := by
    rw [esi, spU]; exact words 1 (by decide)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [show savedRegisters.length = 4 from rfl, popped_four_value, spT, mem]
      exact words 3 (by decide)
    · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact savedEsi
    · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact savedEdi
    · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact savedEbp
    · rw [popped_esp, spT, pushed_esp]; exact BitVec.sub_add_cancel _ _
  · rw [popped_mem, mem]; exact h.returnWord frame
  · rw [popped_gpr _ _ _ (by decide) (by decide),
      restT.1 .eax (by decide), freed_gpr _ _ (by decide)]
    intro pre
    exact result (h.enteredCache.mpr pre)
end VG.Proof.RsaPkcs1Sig.X86.Ver
