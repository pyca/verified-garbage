import VerifiedGarbage.Proof.Ed448.X86.ScalarIO
import VerifiedGarbage.TCB.X86.Target

/-!
# Ed448 scalar reduction on x86 (32-bit): the whole function

`vg_ed448_scalar_reduce(out = [esp + 4], wide = [esp + 8], scratch = [esp + 12])`
against a local contract (`scalarReduceLocal`: the arguments only read), the
ABI included: every write is in the working space but the result's, so the
arguments are read unchanged, the callee-saved registers restored from the
working space, and the return address kept.
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Proof.X448.Radix16 VG.Proof.X448.X86 VG.Proof.Ed448.Limbs16
open VG.Impl.Ed448.X86 (W TF RA SK SS SR scalarReduce)
open VG.Spec.Ed448 (L bytesAt decodeLE encodeLE)

/-- `vg_ed448_scalar_reduce(out, wide, scratch)`, whose arguments are on the
stack (cdecl). -/
def scalarReduceLocal : Contract isa where
  pre s :=
    let out : Region := ⟨(arg s 0).setWidth 64, 57⟩
    let wide : Region := ⟨(arg s 1).setWidth 64, 114⟩
    let scratch : Region := ⟨(arg s 2).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 12⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [wide, args] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧
      wide.Disjoint scratch ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch ∧ (arg s 0).toNat + 57 ≤ 2 ^ 32 ∧
      (arg s 1).toNat + 114 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 8192 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 16 ≤ 2 ^ 32
  post s t := bytesAt t.mem ((arg s 0).setWidth 64) 57 =
    Spec.Ed448.scalarReduce (bytesAt s.mem ((arg s 1).setWidth 64) 114)
  pub s t := s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 ∧ arg s 1 = arg t 1 ∧ arg s 2 = arg t 2

/-- The precondition, by name. -/
structure ReducePre (s : State) : Prop where
  rd : s.rd = [⟨(arg s 1).setWidth 64, 114⟩, ⟨argAddr s 0, 12⟩]
  wr : s.wr = [⟨(arg s 0).setWidth 64, 57⟩, scR (arg s 2)]
  out_sc : (⟨(arg s 0).setWidth 64, 57⟩ : Region).Disjoint (scR (arg s 2))
  wide_sc : (⟨(arg s 1).setWidth 64, 114⟩ : Region).Disjoint (scR (arg s 2))
  args_out : (⟨argAddr s 0, 12⟩ : Region).Disjoint ⟨(arg s 0).setWidth 64, 57⟩
  args_sc : (⟨argAddr s 0, 12⟩ : Region).Disjoint (scR (arg s 2))
  ret_out : (retR s).Disjoint ⟨(arg s 0).setWidth 64, 57⟩
  ret_sc : (retR s).Disjoint (scR (arg s 2))
  out_fit : (arg s 0).toNat + 57 ≤ 2 ^ 32
  wide_fit : (arg s 1).toNat + 114 ≤ 2 ^ 32
  sc_fit : (arg s 2).toNat + 8192 ≤ 2 ^ 32
  sp_fit : (s.gpr .esp).toNat + 16 ≤ 2 ^ 32

theorem ReducePre.of {s : State} (h : scalarReduceLocal.pre s) : ReducePre s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

theorem ReducePre.args {s : State} (h : ReducePre s) : Args s 3 2 :=
  ⟨by rw [h.rd]; simp, by have := h.sp_fit; omega, by decide, by rw [h.wr]; simp, h.sc_fit,
    h.args_sc, h.ret_sc⟩

theorem RA_buf : Buf RA := ⟨by decide, by decide⟩

/-- The return address and the callee-saved registers, across code that
writes only the working space and the output. -/
theorem abi_of {s₀ t : State} {sc : Nat} {base : Addr} (hbase : (arg s₀ sc).setWidth 64 = base)
    (hret_sc : (retR s₀).Disjoint (scR (arg s₀ sc)))
    (hret_out : (retR s₀).Disjoint ⟨(arg s₀ 0).setWidth 64, 57⟩)
    (hm : Outside base 0 8192 s₀.mem t.mem) {m : Mem}
    (ho : Outside ((arg s₀ 0).setWidth 64) 0 57 t.mem m) :
    m.readW ((s₀.gpr .esp).setWidth 64) 32 = s₀.mem.readW ((s₀.gpr .esp).setWidth 64) 32 := by
  have frame : Frame [scR (arg s₀ sc), ⟨(arg s₀ 0).setWidth 64, 57⟩] s₀.mem m := by
    rw [← hbase] at hm
    exact (hm.frame.mono (by simp)).trans (ho.frame.mono (by simp))
  have ret : (retR s₀).Contains ((s₀.gpr .esp).setWidth 64) 4 := by
    simpa only [BitVec.add_zero] using
      Offset.contains_base ((s₀.gpr .esp).setWidth 64) (d := 0) (n := 4) (k := 4) (by decide) (by decide)
  exact frame.readW ret
    (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl; exact hret_sc; exact hret_out) (by decide)

theorem scalarReduce_correct {s₀ : State} (h : ReducePre s₀) :
    WP isa scalarReduce s₀ fun t => abiPreserved s₀ t ∧ scalarReduceLocal.post s₀ t := by
  have hA := h.args
  obtain ⟨base, hbase⟩ : ∃ b, (arg s₀ 2).setWidth 64 = b := ⟨_, rfl⟩
  have hR := RA_buf
  unfold scalarReduce
  refine WP.seq (WP.block_append (WP.mono (save_ok hA) fun s1 ⟨hs1, sv1, o1, k1⟩ => ?_))
  rw [hbase] at hs1 sv1 o1
  have o1' : Outside base 0 8192 s₀.mem s1.mem := o1.mono (by omega) (by omega)
  refine hA.load (i := 1) (k1.1 _ (by decide)) k1.2.1 k1.2.2 (hbase ▸ o1') (by decide)
    fun s2 u2 => WP.block_nil ?_
  have hs2 := hs1.of_upd u2 (by decide)
  have hin : Input s2 base (arg s₀ 1) 114 := Input.of_region h.wide_fit
    (by rw [u2.rd, u2.wr, k1.2.1, h.rd]; simp) (hbase ▸ h.wide_sc)
  refine WP.seq (WP.mono (reduce114_ok hR hs2 u2.gpr hin) fun s3 ⟨k3, l3, v3⟩ => ?_)
  have hs3 := hs2.of_keeps k3.regs (by decide)
  have k03 : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s₀ s3 :=
    (k1.mono (by decide)).trans ((u2.rest (by decide)).trans (k3.regs.mono (by decide)))
  have m3 : Outside base 0 8192 s₀.mem s3.mem :=
    o1'.trans (by rw [← u2.mem]; exact k3.whole (by decide))
  have sv3 : Saved base s₀.gpr s3.mem := (u2.mem ▸ sv1).outside2 k3.mem (by decide) (by decide)
  refine WP.mono (finish_ok hA (by decide) (k03.1 _ (by decide)) k03.2.1 k03.2.2 hbase m3 hs3
    (by decide) l3 (by rw [h.wr]; simp) h.out_fit (fun j hj => far_out (hbase ▸ h.out_sc) hj)
    sv3) fun t ⟨tr, kt, ot, bt⟩ => ⟨⟨?_, abi_of hbase h.ret_sc h.ret_out m3 ot⟩, ?_⟩
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact tr (.ebx, 0) (by decide)
    · exact tr (.esi, 4) (by decide)
    · exact tr (.edi, 8) (by decide)
    · exact tr (.ebp, 12) (by decide)
    · rw [kt.1 _ (by decide), k03.1 _ (by decide)]
  · change bytesAt t.mem _ 57 = encodeLE 57 _
    rw [bt, v3, u2.mem, hin.bytes o1']

end VG.Proof.Ed448.X86
