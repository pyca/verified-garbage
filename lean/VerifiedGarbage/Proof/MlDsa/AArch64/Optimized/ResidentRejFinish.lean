import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTail
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejEpi
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejCore

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample

structure Result (v : Nat) (σ t : State) : Prop where
  abi : abiPreserved σ t
  frame : Frame [aR v σ,scrR σ] σ.mem t.mem
  rd : t.rd=σ.rd
  wr : t.wr=σ.wr
  stored : ∀k<v,Stored t.mem (polyP σ k) (prefixRow σ k 1008)
  status : t.gpr .x0=if (∀k<v,(prefixRow σ k 1008).length=256) then 1#64 else 0#64

 theorem finish_ok {v : Nat} {σ s : State} (hp : Pre v σ) (h : Done v σ s) :
    WP isa (.block (([.subImm .x .x27 .x27 1,.lsr .x .x27 .x27 63] : List Instr)++
      Impl.MlDsa.AArch64.Sample.Rej4.epi)) s (Result v σ) := by
  refine wp_subImm (by decide) fun a ha ea => wp_lsr (by decide) fun b hb eb => ?_
  have he : Env v σ b := h.env.lowStep (rs := [])
    (by rw [hb.mem,ha.mem]; exact Frame.refl _ _) (by simp)
    (hb.rd.trans ha.rd) (hb.wr.trans ha.wr) (hb.sp.trans ha.sp)
    (fun r hr => by
      have hn : r∉[Reg.x27] := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> decide
      rw [hb.get r hn,ha.get r hn])
  have eflag : b.gpr .x27=if (∀k<v,(prefixRow σ k 1008).length=256) then 1#64 else 0#64 := by
    rw [eb,ea,smallFlag_status _ h.flags.bound]
    by_cases hz : s.gpr .x27=0#64
    · simp only [ite_eq_left hz,ite_eq_left (h.flags.zero.mp hz)]
    · simp only [ite_eq_right hz,ite_eq_right (fun he => hz (h.flags.zero.mpr he))]
  refine WP.mono (epi_with he (fun d n hn => in_scr_rd hp he.wr hn)) fun t ht => ?_
  exact ⟨ht.1,by rw [ht.2.1]; exact he.frame,ht.2.2.2.1.trans he.rd,
    ht.2.2.2.2.trans he.wr,by simpa only [ht.2.1,hb.mem,ha.mem] using h.stored,
    ht.2.2.1.trans eflag⟩

theorem four_ok {σ : State} (hp : Pre 4 σ) :
    WP isa Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.code σ (Result 4 σ) := by
  apply four_of_finish hp
  intro s hs
  apply WP.seq
  exact WP.mono (tailZerosFour_ok hp hs) fun t ht => finish_ok hp ht

theorem two_ok {σ : State} (hp : Pre 2 σ) :
    WP isa Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.code σ (Result 2 σ) := by
  apply two_of_finish hp
  intro s hs
  apply WP.seq
  exact WP.mono (tailZerosTwo_ok hp hs) fun t ht => finish_ok hp ht

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
