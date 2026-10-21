module

public import VerifiedGarbage.Proof.Rsa.X86.RvTimeBase
public import VerifiedGarbage.Proof.Rsa.X86.RvSearchTimingState
public import VerifiedGarbage.Proof.Rsa.X86.RvSquareStep
import VerifiedGarbage.Proof.Rsa.X86.RvTimeCheck
import VerifiedGarbage.Proof.Rsa.X86.RvTimeCandidate
import VerifiedGarbage.Proof.Rsa.X86.RvCandidateSquareInit
import VerifiedGarbage.Proof.Rsa.X86.RvSearchLoop
import VerifiedGarbage.Proof.Rsa.X86.RvSlots
import VerifiedGarbage.Proof.Rsa.RecoverTries
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # The candidate search leaks only public data

Two runs of the bounded search for a recovery candidate over the same
geometry, with the same declared attempt count, leak the same trace: each
candidate's exponentiation and masked squarings, and the search's stopping
condition, which the attempt count decides.
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa (sqStart sqIter)

/-- `sqBody`'s product: its precondition and the stage after it. -/
theorem SI.mulPre {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {m k c : Nat}
    {st : Nat × Bool × Bool} (h : SI g s0 A AW V m k c st s)
    (value : A mBase = m) (bound : m < 2 ^ (64 * g.n))
    (inverse : (m * V sInv + 1) % 2 ^ 32 = 0) (positive : 0 < m) :
    MulPre g mX mY mY s ∧ WP isa (VG.Impl.Rsa.X86.RecoverRt.mmul mX mY mY) s (MulPost g) := by
  unfold SI at h
  have mr := h.montReady (m := m) (by simp [liveSq, liveM]) (by simp [slotsSq])
    (by simpa only [upd_ne _ _ (by decide : mBase ≠ mY)] using value) bound
    (by simpa [VS, upd, sInv, sK, sCnt, sDone, sOk] using inverse)
  have lt : upd A mY (st.1 * 2 ^ (64 * g.n) % m) mY < m := by
    simpa only [upd_self] using Nat.mod_lt (st.1 * 2 ^ (64 * g.n)) positive
  refine ⟨⟨_, _, _, _, _, _, _, _, h, mr, by simp [liveSq], by simp [liveSq], lt, lt, by decide, by decide⟩, ?_⟩
  exact WP.mono (h.mmul mr (o := mX) (a := mY) (b := mY)
    (by decide) (by decide) (by decide) (by decide) (by simp [liveSq]) (by simp [liveSq]) lt lt
    (by decide) (by decide)) fun _ ⟨_, h1, _⟩ => KS.stage h1

theorem sqBody_relCT {g : Geo} (pg : PubG g) {s0 t0 : State} {A B AW BW V W : Nat → Nat}
    {m k k' c c' : Nat} {st st' : Nat × Bool × Bool}
    (valueA : A mBase = m) (valueB : B mBase = m) (bound : m < 2 ^ (64 * g.n))
    (invA : (m * V sInv + 1) % 2 ^ 32 = 0) (invB : (m * W sInv + 1) % 2 ^ 32 = 0) (positive : 0 < m) :
    RelCT isa (fun s t => SI g s0 A AW V m k c st s ∧ SI g t0 B BW W m k' c' st' t)
      VG.Impl.Rsa.X86.RecoverRt.sqBody (fun _ _ => True) := by
  intro s t tr ur sf tf ⟨hs, ht⟩ es et
  obtain ⟨ps, ws⟩ := hs.mulPre valueA bound invA positive
  obtain ⟨pt, wt⟩ := ht.mulPre valueB bound invB positive
  cases es with
  | @seq _ _ _ u _ _ _ e1 e2 =>
    cases et with
    | @seq _ _ _ v _ _ _ f1 f2 =>
      have eq1 := (mmul_relCT pg (by decide) (by decide) (by decide) (by decide) mulArgs_mX_mY_mYCheck
        ⟨_, clrTop_mXCheck⟩ _ _ _ _ _ _ ⟨ps, pt⟩ e1 f1).1
      obtain ⟨_, _, _, _, _, _, _, hu⟩ := wp_result ws e1
      obtain ⟨_, _, _, _, _, _, _, hv⟩ := wp_result wt f1
      exact ⟨by rw [eq1, pub_trace pg sqTailCheck hu hv e2 f2], trivial⟩

theorem sqLoop_relCT {g : Geo} (pg : PubG g) (s0 t0 : State) (A B AW BW V W : Nat → Nat)
    (m c : Nat) (st tt : Nat × Bool × Bool)
    (valueA : A mBase = m) (valueB : B mBase = m)
    (bound : m < 2 ^ (64 * g.n))
    (invA : (m * V sInv + 1) % 2 ^ 32 = 0) (invB : (m * W sInv + 1) % 2 ^ 32 = 0)
    (odd : m % 2 = 1) (large : 1 < m)
    (oneA : A aO = 2 ^ (64 * g.n) % m) (oneB : B aO = 2 ^ (64 * g.n) % m)
    (negA : A aNg = m - 2 ^ (64 * g.n) % m) (negB : B aNg = m - 2 ^ (64 * g.n) % m)
    (tcA : V sTc ≤ c) (tcB : W sTc ≤ c) (positive : 0 < c) (limit : c ≤ 16384) :
    RelCT isa (fun s t => SI g s0 A AW V m 0 c st s ∧ SI g t0 B BW W m 0 c tt t)
      (.loop VG.Impl.Rsa.X86.RecoverRt.sqBody .ne)
      (fun s t => SI g s0 A AW V m c 0 (sqIter m (V sTc) c st) s ∧
        SI g t0 B BW W m c 0 (sqIter m (W sTc) c tt) t) := by
  have loop := fixedLoop_relCT
    (fun k s => SI g s0 A AW V m k (c - k) (sqIter m (V sTc) k st) s)
    (fun k t => SI g t0 B BW W m k (c - k) (sqIter m (W sTc) k tt) t)
    positive (fun _ _ => sqBody_relCT pg valueA valueB bound invA invB (by omega))
    (fun k s hk hs => by
      refine WP.mono (sqBody_step hs valueA bound invA odd large oneA negA
        (by omega) (by omega) (by omega) (by omega)) fun t result => ?_
      simpa only [sqIter, Nat.sub_sub] using result)
    (fun k t hk ht => by
      refine WP.mono (sqBody_step ht valueB bound invB odd large oneB negB
        (by omega) (by omega) (by omega) (by omega)) fun u result => ?_
      simpa only [sqIter, Nat.sub_sub] using result)
  simpa only [sqIter, Function.iterate_zero, id_eq, Nat.sub_zero, Nat.sub_self] using loop

theorem candSquare_relCT {g : Geo} (pg : PubG g) {m eLen dLen : Nat} (C D : CandidateData g m eLen dLen)
    (y z : Nat) (yl : y < m) (zl : z < m) :
    RelCT isa (fun s t => C.SquareStart y s ∧ D.SquareStart z t) VG.Impl.Rsa.X86.RecoverRt.candSquare
      (fun s t => C.SquareEnd y s ∧ D.SquareEnd z t) := by
  unfold VG.Impl.Rsa.X86.RecoverRt.candSquare
  refine VG.RelCT.seq
    (R := fun s t => SI g C.s0 C.A C.AW (upd C.V sCnt 0) m 0 (8 * (dLen + eLen)) (sqStart m y) s ∧
      SI g D.s0 D.A D.AW (upd D.V sCnt 0) m 0 (8 * (dLen + eLen)) (sqStart m z) t)
    (pub_relCT (P := C.SquareStart y) (Q := D.SquareStart z) pg candSquareInitCheck
      (fun _ hs => KS.stage hs) (fun _ ht => KS.stage ht)
      (fun s hs => candSquareInit_ok hs C.odd (by have := C.large; omega) C.one C.neg yl C.ae C.ad C.limit)
      (fun t ht => candSquareInit_ok ht D.odd (by have := D.large; omega) D.one D.neg zl D.ae D.ad D.limit)) ?_
  refine (sqLoop_relCT pg C.s0 D.s0 C.A D.A C.AW D.AW
    (upd C.V sCnt 0) (upd D.V sCnt 0) m (8 * (dLen + eLen)) (sqStart m y) (sqStart m z)
    C.value D.value C.bound
    (by simpa only [upd_ne _ _ (by decide : sInv ≠ sCnt)] using C.inverse)
    (by simpa only [upd_ne _ _ (by decide : sInv ≠ sCnt)] using D.inverse)
    C.odd (by have := C.large; omega) C.one D.one C.neg D.neg
    (by simpa only [upd_ne _ _ (by decide : sTc ≠ sCnt)] using C.tc)
    (by simpa only [upd_ne _ _ (by decide : sTc ≠ sCnt)] using D.tc)
    C.count C.limit).mono (fun _ _ h => h) fun s t ⟨is, it⟩ => ⟨?_, ?_⟩
  · simpa only [CandidateData.SquareEnd, upd_ne _ _ (by decide : sTc ≠ sCnt)] using is
  · simpa only [CandidateData.SquareEnd, upd_ne _ _ (by decide : sTc ≠ sCnt)] using it

theorem candBody_relCT {g : Geo} (pg : PubG g) {m eLen dLen : Nat} (C D : CandidateData g m eLen dLen) :
    RelCT isa (fun s t => C.Start s ∧ D.Start t) VG.Impl.Rsa.X86.RecoverRt.candBody (fun _ _ => True) := by
  unfold VG.Impl.Rsa.X86.RecoverRt.candBody
  simp only [seqs]
  refine VG.RelCT.seq (R := fun s t => C.SquareStart C.y s ∧ D.SquareStart D.y t)
    ((candExp_relCT C D pg).mono (fun _ _ h => h) fun _ _ ⟨hs, ht⟩ => ⟨C.exp_toSquare hs, D.exp_toSquare ht⟩) ?_
  refine VG.RelCT.seq (R := fun s t => C.SquareEnd C.y s ∧ D.SquareEnd D.y t)
    (candSquare_relCT pg C D C.y D.y
      (by rw [CandidateData.y, VG.Proof.Bignum.powMod_eq]; exact Nat.mod_lt _ (by have := C.large; omega))
      (by rw [CandidateData.y, VG.Proof.Bignum.powMod_eq]; exact Nat.mod_lt _ (by have := D.large; omega))) ?_
  exact pub_relCT' pg candNextCheck (fun _ hs => KS.stage hs) (fun _ ht => KS.stage ht)

theorem searchLoop_relCT {g : Geo} (pg : PubG g) {m eLen dLen : Nat} (C D : CandidateData g m eLen dLen)
    (tcC : 1 ≤ C.V sTc) (tcD : 1 ≤ D.V sTc) (tries : C.tries = D.tries) :
    RelCT isa (fun s t => CI g C.s0 C.A C.AW C.V 0 s ∧ CI g D.s0 D.A D.AW D.V 0 t)
      (.loop VG.Impl.Rsa.X86.RecoverRt.candBody .ne) (fun _ _ => True) := by
  have top := VG.Proof.Rsa.go_le m (C.V sTc) (C.AW wR) 100 (by decide)
  change C.tries ≤ 100 at top
  have low := VG.Proof.Rsa.go_ge1 m (C.V sTc) (C.AW wR) (k := 99) (by decide)
  change 1 ≤ C.tries at low
  have loop := VG.RelCT.loop (M := isa) (body := VG.Impl.Rsa.X86.RecoverRt.candBody) (c := .ne)
    (Q := fun _ _ => True)
    (fun remaining s t => ∃ j, j + remaining = 100 ∧ 0 < remaining ∧
      SearchInvariant C j s ∧ SearchInvariant D j t)
    (fun remaining s t tr ur sf tf ⟨j, sum, pos, hs, ht⟩ es et => by
      have hj : j < 100 := by omega
      have trace := (candBody_relCT pg (C.atCandidate j hj) (D.atCandidate j hj)
        _ _ _ _ _ _ ⟨hs.1, ht.1⟩ es et).1
      obtain ⟨cs, cn⟩ := wp_result (searchBody_post C tcC hs) es
      obtain ⟨ds, dn⟩ := wp_result (searchBody_post D tcD ht) et
      refine ⟨trace, ?_, fun _ => trivial, ?_⟩
      · rw [cs, ds, tries]
      · intro more
        have next : j + 1 < C.tries := of_decide_eq_true (Option.some.inj (cs.symm.trans more))
        have moreD : isa.eval .ne tf = some true := ds.trans (by rw [← tries]; exact congrArg some (decide_eq_true next))
        exact ⟨remaining - 1, by omega, j + 1, by omega, by omega, cn more, dn moreD⟩) 100
  apply loop.mono
  · intro s t ⟨hs, ht⟩
    exact ⟨0, rfl, by decide, ⟨hs, by omega, rfl⟩, ⟨ht, by omega, rfl⟩⟩
  · intro s t h; exact h

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

theorem candLoop_relCT {g : Geo} (pg : PubG g) {m eLen dLen : Nat} (C D : CandidateData g m eLen dLen)
    (vcC : C.V sCnt = 0) (vcD : D.V sCnt = 0)
    (tcC : 1 ≤ C.V sTc) (tcD : 1 ≤ D.V sTc) (tries : C.tries = D.tries) :
    RelCT isa (fun s t =>
      KS g C.s0 C.A liveM C.AW [wR] C.V [sInv, sTc, sCnt] s ∧
      KS g D.s0 D.A liveM D.AW [wR] D.V [sInv, sTc, sCnt] t)
      VG.Impl.Rsa.X86.RecoverRt.candLoop (fun _ _ => True) :=
  VG.RelCT.seq (R := fun s t => CI g C.s0 C.A C.AW C.V 0 s ∧ CI g D.s0 D.A D.AW D.V 0 t)
    (pub_relCT pg candInitCheck (fun _ hs => KS.stage hs) (fun _ ht => KS.stage ht)
      (fun _ hs => candInit_ok hs vcC) (fun _ ht => candInit_ok ht vcD))
    (searchLoop_relCT pg C D tcC tcD tries)

end VG.Proof.Rsa.X86.Recover
