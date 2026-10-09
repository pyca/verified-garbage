import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.CallSample
import VerifiedGarbage.Spec.MlDsa.RejNTT2
namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG.Impl.MlDsa.AArch64.Call
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
/-! ## `RejNTTPoly` -/

def rej2Chk (rbs wbs : List (Reg × Nat)) (seed a ss : Ptr) : Bool :=
  sepB rbs wbs seed 68 a 2048 && sepB rbs wbs seed 68 ss 8192 && sepB rbs wbs a 2048 ss 8192 &&
    inB (rbs ++ wbs) seed 68 && inB (rbs ++ wbs) a 2048 && inB (rbs ++ wbs) ss 8192 && inB wbs a 2048 &&
    inB wbs ss 8192

abbrev rej2Args (seed a ss : Ptr) : List (Reg × Arg) := [(.x0, .ptr seed), (.x1, .ptr a), (.x2, .ptr ss)]

section
variable {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {seed a ss : Ptr}
  (hc : rej2Chk rbs wbs seed a ss = true)
include L hc

theorem rej2_cov : Covers ([⟨pa s seed, 68⟩] ++ [⟨pa s a, 2048⟩, ⟨pa s ss, 8192⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨pa s a, 2048⟩, ⟨pa s ss, 8192⟩] s.wr := by
  simp only [rej2Chk, Bool.and_eq_true, and_assoc] at hc
  obtain ⟨_, _, _, c4, _, _, c7, c8⟩ := hc
  exact ⟨Covers.append_left (L.cR c4) (Covers.right (Covers.cons (L.cW c7) (L.cW c8))), Covers.cons (L.cW c7) (L.cW c8)⟩

theorem rej2_pre {s1 : State} (h1 : Args (rej2Args seed a ss) s s1) :
    (rejNTT2Contract AArch64.abi S).pre
      (s1.callEntry.withRegions [⟨pa s seed, 68⟩] [⟨pa s a, 2048⟩, ⟨pa s ss, 8192⟩]) := by
  simp only [rej2Chk, Bool.and_eq_true, and_assoc] at hc
  obtain ⟨c1, c2, c3, c4, c5, c6, _, _⟩ := hc
  sig_pre [rejNTT2Contract, rejNTT2Sig, AArch64.abi, VG.AArch64.argRegs]
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.sp h1]
  simp only [Arg.val]
  cpre L

end

theorem rej2_args {B : List Reg} {bs : List (Reg × Nat)} (L : LayIn B bs) {seed a ss : Ptr} (c4 : inB bs seed 68 = true)
    (c5 : inB bs a 2048 = true) (c6 : inB bs ss 8192 = true) :
    ∀ x ∈ rej2Args seed a ss, x.2.Ok ∧ x.1 ∈ argRegs := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok (ptr_kept L c4), by decide⟩, ⟨ptr_ok (ptr_kept L c5), by decide⟩, ⟨ptr_ok (ptr_kept L c6), by decide⟩⟩

theorem rej2At_ok {S : Nat} (hS : S < 2 ^ 64) {cd : Prog isa} {nm : String} (C : CalleeOk S cd (rejNTT2Contract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {seed a ss : Ptr}
    (hc : rej2Chk rbs wbs seed a ss = true) :
    WP isa (callAt nm cd (rej2Args seed a ss)) s fun s' => PPostB S s s' [(a, 2048), (ss, 8192)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      ((s'.gpr .x0).setWidth 32 = 1 → ∀ k < 2,Reduced s'.mem (poly4 (pa s a) k)) ∧
      (((s'.gpr .x0).setWidth 32 = 1 ∧ ∀ k < 2,∃ b : Bounds,rejNTTPoly b.rejNTT
          (seed4 s.mem (pa s seed) k) = some (polyAt s'.mem (poly4 (pa s a) k))) ∨
        ((s'.gpr .x0).setWidth 32 = 0 ∧ ∃ k < 2,rejNTTPoly minBounds.rejNTT
          (seed4 s.mem (pa s seed) k) = none)) := by
  have hc' := hc
  simp only [rej2Chk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  refine WP.mono (callAt_ok hS C (rej2_args L.ok c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => rej2_pre L hc h1) (rej2_cov L hc).1 (rej2_cov L hc).2)
    fun s' ⟨hP, s1, h1, hq⟩ => ⟨hP.b, hP.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [rejNTT2Contract, rejNTT2Sig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.r1 h1, Args.mem h1] at hq
  exact hq

theorem rej2At_tr {S : Nat} {cd : Prog isa} {nm : String} (C : CalleeOk S cd (rejNTT2Contract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} (hB : LayOk (rbs ++ wbs)) {seed a ss : Ptr} (hc : rej2Chk rbs wbs seed a ss = true)
    {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay S rbs wbs x ∧ Lay S rbs wbs y ∧
      bytesAt x.mem (pa x seed) 68 = bytesAt y.mem (pa y seed) 68 ∧ SameB x y) :
    RelCT isa Q (callAt nm cd (rej2Args seed a ss)) fun _ _ => True := by
  have hc' := hc
  simp only [rej2Chk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  have hb : seed.1 ∈ bases ∧ a.1 ∈ bases ∧ ss.1 ∈ bases := ⟨ptr_bs hB c4, ptr_bs hB c5, ptr_bs hB c6⟩
  refine callAt_tr C (rej2_args hB c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, hsd, e⟩ := hQ x y hp
  refine ⟨_, _, rej2_pre Lx hc h1, ?_, ?_, (rej2_cov Lx hc).1, (rej2_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact rej2_pre Ly hc h2
  · sig_pub [rejNTT2Contract, rejNTT2Sig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r0 h2, Args.r1 h2, Args.r2 h2, Args.sp h1, Args.sp h2,
      Args.mem h1, Args.mem h2]
    simp only [Arg.val]
    exact ⟨e.2, by rw [hsd], e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact (rej2_cov Ly hc).1
  · rw [e.pa hb.2.1, e.pa hb.2.2]; exact (rej2_cov Ly hc).2


end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
