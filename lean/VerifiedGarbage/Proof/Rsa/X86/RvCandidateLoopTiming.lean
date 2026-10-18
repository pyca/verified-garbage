module

public import VerifiedGarbage.Proof.Rsa.X86.RvSearchTiming

/-! # Initializing and running the bounded candidate search -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

theorem candInit_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat}
    (h : KS g s0 A liveM AW [wR] V [sInv, sTc, sCnt] s) (vc : V sCnt = 0) :
    WP isa (.block [.mov .eax (.imm 0), .store (VG.Impl.Mont.X86.sc sCand) .eax]) s
      (CI g s0 A AW V 0) := by
  refine wp_movS rfl fun u U _ => ?_
  have hu := h.of_rest U.keeps (by decide) U.mem
  refine WP.mono (hu.storeSlot (d := sCand) (by decide) .eax) fun v ⟨hv, _, _⟩ => ?_
  rw [U.gpr] at hv
  refine hv.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, rfl⟩) ?_
  intro d hd
  simp only [slotsExp, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl <;>
    simp [VJ, upd, sInv, sTc, sCnt, sCand] <;> exact vc

theorem CandidateData.search_ok {g : Geo} {m eLen dLen : Nat} (C : CandidateData g m eLen dLen)
    {s : State} (h : KS g C.s0 C.A liveM C.AW [wR] C.V [sInv, sTc, sCnt] s)
    (vc : C.V sCnt = 0) (tc : 1 ≤ C.V sTc) :
    WP isa (candLoop g.n) s (SearchResult g C.s0 C.A C.AW C.V m (8 * (dLen + eLen))) :=
  candLoop_ok C.zero C.value C.bound C.inverse C.odd C.large C.one C.neg C.r2
    C.ae C.ad C.tc C.rb C.count C.limit h vc tc

theorem candLoop_relCT {g : Geo} {m eLen dLen : Nat} (C D : CandidateData g m eLen dLen)
    (sp : C.s0.gpr .esp = D.s0.gpr .esp) (vcC : C.V sCnt = 0) (vcD : D.V sCnt = 0)
    (tcC : 1 ≤ C.V sTc) (tcD : 1 ≤ D.V sTc) (tries : C.tries = D.tries) :
    RelCT isa (fun s t =>
      KS g C.s0 C.A liveM C.AW [wR] C.V [sInv, sTc, sCnt] s ∧
      KS g D.s0 D.A liveM D.AW [wR] D.V [sInv, sTc, sCnt] t)
      (candLoop g.n) (fun _ _ => True) := by
  have init : WorkspacePublic (.block [.mov .eax (.imm 0), .store (VG.Impl.Mont.X86.sc sCand) .eax]) := by
    exact ⟨.block [], VG.Proof.Mont.X86.Dynamic.zeroTaint false, rfl, rfl⟩
  intro s t tr ur sf tf ⟨hs, ht⟩ es et
  cases es with
  | @seq _ _ _ u _ _ _ e1 e2 =>
    cases et with
    | @seq _ _ _ v _ _ _ f1 f2 =>
      have eq1 := (init.trace _ _ _ _ _ _ (ks_agree hs ht) e1 f1).1
      have cs := wp_result (candInit_ok hs vcC) e1
      have ds := wp_result (candInit_ok ht vcD) f1
      have eq2 := (searchLoop_relCT C D sp tcC tcD tries _ _ _ _ _ _ ⟨cs, ds⟩ e2 f2).1
      exact ⟨by rw [eq1, eq2], trivial⟩

end VG.Proof.Rsa.X86.Recover
