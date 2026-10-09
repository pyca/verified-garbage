import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Zero

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64

def tailBody : List Instr :=
  [.str .w .x9 .x3 0,.addImm .x .x3 .x3 4,.subImm .x .x4 .x4 1]

structure TailInv (p : Addr) (n : Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  keep : Keep [.x3,.x4] s₀ s
  ptr : s.gpr .x3=p+BitVec.ofNat 64 (4*k)
  count : (s.gpr .x4).toNat=n-k
  frame : Frame [⟨p,4*n⟩] s₀.mem s.mem

theorem tailStep_ok {p : Addr} {n k : Nat} {s₀ s : State} (hn : n≤256) (hk : k<n)
    (hw : ∀i<n,InRegions s₀.wr (p+BitVec.ofNat 64 (4*i)) 4)
    (h : TailInv p n s₀ k s) :
    WP isa (.block tailBody) s fun t => TailInv p n s₀ (k+1) t ∧
      ((t.gpr .x4).toNat≠0 ↔ k+1≠n) := by
  unfold tailBody
  refine wp_strw (a := p+BitVec.ofNat 64 (4*k)) (by decide)
    (by rw [h.ptr,ptr_zero]) (by rw [h.keep.wr]; exact hw k hk)
    fun a ha => wp_addImm (by decide) fun b hb eb => wp_subImm (by decide) fun t ht et => wp_nil ?_
  have hc : (b.gpr .x4).toNat=n-k := by rw [hb.get .x4,ha.gpr,h.count]
  have hct : (t.gpr .x4).toNat=n-(k+1) := by
    rw [et,toNat_sub_n (by rw [hc]; simp; omega),hc]
    simp
    omega
  refine ⟨⟨(h.keep.trans ((ha.keep.trans hb.keep).trans ht.keep)).mono,?_,hct,?_⟩,by rw [hct]; omega⟩
  · rw [ht.get .x3,eb,ha.gpr,h.ptr,Offset.add_add]
    congr 2
  · rw [ht.mem,hb.mem,ha.mem]
    exact h.frame.writeW (List.mem_singleton_self _) _
      (Offset.contains_base p (by omega) (by omega))

theorem tailLoop_ok {p : Addr} {n : Nat} {s : State} (hn : 0<n) (hn256 : n≤256)
    (hp : s.gpr .x3=p) (hc : (s.gpr .x4).toNat=n)
    (hw : ∀i<n,InRegions s.wr (p+BitVec.ofNat 64 (4*i)) 4) :
    WP isa (.loop (.block tailBody) (.nonzero .x .x4)) s fun t =>
      Keep [.x3,.x4] s t ∧ Frame [⟨p,4*n⟩] s.mem t.mem := by
  refine WP.mono (count_loop hn (TailInv p n s)
    (fun k hk t ht => tailStep_ok hn256 hk hw ht)
    ⟨Keep.refl _ _,by simpa only [Nat.mul_zero,BitVec.add_zero] using hp,
      by simpa only [Nat.sub_zero] using hc,Frame.refl _ _⟩) fun _ ht => ⟨ht.keep,ht.frame⟩

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
