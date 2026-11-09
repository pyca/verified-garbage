module
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Xor
public import VerifiedGarbage.Impl.ChaCha20.AArch64.Small

import VerifiedGarbage.Proof.ChaCha20.AArch64.Small.Chunk
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub

@[expose] public section

namespace VG.Proof.ChaCha20.AArch64.Small
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Small
open VG.Proof.ChaCha20.AArch64.Xor (TPre st dp tp L bp stR dR tR bR S0 D0 KS Dst Src)
open VG.Proof.ChaCha20 (ctr keystream_getD)
open VG.Spec.ChaCha20 (stateAt serialize block keystream)

/-- After `n` blocks of the vector kernel from `s₀` (where `x6` is the
destination): the destination done up to there and the source after it
intact, the pointers (the destination in `x4` and `x6`) advanced. -/
structure Prefix (s₀ : State) (n : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = st s₀
  x1 : s.gpr .x1 = dp s₀ + BitVec.ofNat 64 (64*n)
  x2 : s.gpr .x2 = BitVec.ofNat 64 (L s₀-64*n)
  x3 : s.gpr .x3 = bp s₀
  x4 : s.gpr .x4 = tp s₀ + BitVec.ofNat 64 (64*n)
  cs : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  cnt : stateAt s.mem (st s₀) = ctr (S0 s₀) n
  data : Dst s₀ (64*n) s.mem
  src : Src s₀ (64*n) s.mem

theorem next_ok (s : State) (n : Nat) (hn : n ≤ 4)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 48) 4)
    (hout : InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 48) 4) :
    WP isa (.block (next n)) s fun u =>
      u.gpr .x1 = s.gpr .x1 + BitVec.ofNat 64 (64*n) ∧
      u.gpr .x2 = s.gpr .x2 - BitVec.ofNat 64 (64*n) ∧
      u.gpr .x4 = s.gpr .x6 + BitVec.ofNat 64 (64*n) ∧
      (∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x4 → r ≠ .x6 → u.gpr r = s.gpr r) ∧
      stateAt u.mem (s.gpr .x0) = ctr (stateAt s.mem (s.gpr .x0)) n ∧
      Frame [⟨s.gpr .x0,64⟩] s.mem u.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp := by
  have hi : n < 4096 := by omega
  have hb : 64*n < 4096 := by omega
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceMul, Nat.reduceMod, and_self, next,runBlock_cons,runBlock_nil,exec,
    VG.Impl.ChaCha20.AArch64.Xor.mov,
    addr,Size.bytes,Size.bits,State.load,hin,State.read,RegUpd.gpr_write,
    RegUpd.wr_write,RegUpd.mem_write,RegUpd.rd_write,RegUpd.sp_write,
    Option.bind_some,Option.map_some,isa,runStep_some,BitVec.setWidth_setWidth_of_le,
    BitVec.setWidth_eq,State.store,hout,hi,hb,Option.some.injEq,exists_eq_left',BitVec.add_zero]
  refine ⟨trivial,trivial,trivial,?_,?_,?_,trivial⟩
  · intro r h1 h2 h4 h6; simp only [h1,h2,h4,h6,ite_false]
  · have ht := VG.Proof.ChaCha20.AArch64.Xor.stateAt_writeW_ctr s.mem (s.gpr .x0) n
    simp only [Mem.writeW,Mem.readW,BitVec.setWidth_eq] at ht
    exact ht
  · exact (Frame.refl _ _).write (List.mem_cons_self ..) _
      (Offset.contains_base _ (by decide : 48+4 ≤ 64) (by decide))

theorem step_ok {sve : Bool} (s₀ : State) (hp : TPre s₀) (h6 : s₀.gpr .x6 = tp s₀) (n : Nat) (hn : n ≤ 4)
    (hle : 64*n ≤ L s₀) :
    WP isa (step n sve) s₀ (Prefix s₀ n) := by
  have hl : L s₀ < 2^64 := (s₀.gpr .x2).isLt
  have hi : ∀ k : Fin 16, InRegions (s₀.rd ++ s₀.wr) (st s₀+BitVec.ofNat 64 (4*k)) 4 := by
    intro k; rw [hp.rd,hp.wr]
    exact ⟨stR s₀,by simp,Offset.contains_base _ (by omega) (by omega)⟩
  have hs : ∀ r : Fin 4, ∀ j ∈ lanes n, InRegions (s₀.rd ++ s₀.wr)
      (dp s₀+BitVec.ofNat 64 (64*j+16*r)) 16 := by
    intro r j hj
    have hjn : j.val < n := (List.mem_filter.mp hj).2 |> of_decide_eq_true
    rw [hp.rd,hp.wr]
    exact ⟨dR s₀,by simp,Offset.contains_base _ (by omega) (by omega)⟩
  have ho : ∀ r : Fin 4, ∀ j ∈ lanes n, InRegions s₀.wr
      (s₀.gpr .x6+BitVec.ofNat 64 (64*j+16*r)) 16 := by
    intro r j hj
    have hjn : j.val < n := (List.mem_filter.mp hj).2 |> of_decide_eq_true
    rw [hp.wr,h6]
    exact ⟨tR s₀,by simp,Offset.contains_base _ (by omega) (by omega)⟩
  have sub : Region.Sub ⟨tp s₀,64*n⟩ (tR s₀) := Region.sub_prefix hle
  have ssub : Region.Sub ⟨dp s₀,64*n⟩ (dR s₀) := Region.sub_prefix hle
  have halias : s₀.gpr .x1 = s₀.gpr .x6 ∨
      (⟨s₀.gpr .x1, 64*n⟩ : Region).Disjoint ⟨s₀.gpr .x6, 64*n⟩ := by
    rw [h6]
    rcases hp.alias with he | hd
    · exact .inl he.symm
    · exact .inr ((hd.sub_left ssub).sub_right sub)
  apply WP.seq
  refine (chunk_ok (sve := sve) n hn s₀ hi halias hs ho).mono fun a ⟨ha,hf,hk⟩ => ?_
  rw [h6] at ha hf
  have ia : InRegions (a.rd ++ a.wr) (a.gpr .x0+BitVec.ofNat 64 48) 4 := by
    rw [hk.rd,hk.wr,hk.gpr .x0 (by decide),hp.rd,hp.wr]
    exact ⟨stR s₀,by simp,Offset.contains_base _ (by decide) (by decide)⟩
  have oa : InRegions a.wr (a.gpr .x0+BitVec.ofNat 64 48) 4 := by
    rw [hk.wr,hk.gpr .x0 (by decide),hp.wr]
    exact ⟨stR s₀,by simp,Offset.contains_base _ (by decide) (by decide)⟩
  have hft : Frame [tR s₀] s₀.mem a.mem := hf.sub (fun r hr => by
    simp only [List.mem_singleton] at hr; subst r
    exact ⟨tR s₀,by simp,sub⟩)
  have hd : Dst s₀ (64*n) a.mem := by
    intro k hkl
    by_cases hk' : k < 64*n
    · rw [ha k hk',ite_eq_left hk',keystream_getD _ hkl]
    · rw [hf _ (by
        intro r hr; simp only [List.mem_singleton] at hr; subst r
        simp only [Region.Contains,tp,Mem.sub_ofNat_toNat _ (by omega : k < 2^64)]
        omega),ite_eq_right hk']
  have hsrc : Src s₀ (64*n) a.mem := Xor.src_step hp (Nat.zero_le _)
    (fun k _ _ => rfl) hft hd
  refine (next_ok a n hn ia oa).mono fun u ⟨h1,h2,h4,hg,hcnt,hf',hrd,hwr,hsp⟩ => ?_
  have h0 : u.gpr .x0 = st s₀ := (hg _ (by decide) (by decide) (by decide) (by decide)).trans (hk.gpr _ (by decide))
  have hnd : ∀ r ∈ [stR s₀], (tR s₀).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hp.st_t.symm
  have hns : ∀ r ∈ [stR s₀], (dR s₀).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hp.st_d.symm
  rw [hk.gpr _ (by decide)] at hcnt hf'
  refine ⟨h0,?_,?_,?_,?_,?_,hrd.trans hk.rd,hwr.trans hk.wr,hsp.trans hk.sp,?_,
    hd.frame hf' hnd,hsrc.frame hf' hns⟩
  · rw [h1,hk.gpr _ (by decide)]
  · rw [h2,hk.gpr _ (by decide)]
    apply BitVec.eq_of_toNat_eq
    simp only [L,BitVec.toNat_sub,BitVec.toNat_ofNat] at *
    omega
  · exact (hg _ (by decide) (by decide) (by decide) (by decide)).trans (hk.gpr _ (by decide))
  · rw [h4,hk.gpr _ (by decide),h6]
  · intro r hr
    have hne : r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x4 ∧ r ≠ .x6 := by revert hr; decide +revert
    exact (hg r hne.1 hne.2.1 hne.2.2.1 hne.2.2.2).trans (hk.gpr r hne.2.2.1)
  · rw [hcnt, VG.Proof.ChaCha20.AArch64.Xor.stateAt_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst r
      exact hp.st_t.sub_right sub)]

end VG.Proof.ChaCha20.AArch64.Small
