module

public import VerifiedGarbage.Proof.Rsa.X86.RvTimeFusedSmall
import VerifiedGarbage.Proof.Rsa.X86.RvTimeCheck
import VerifiedGarbage.Proof.Rsa.X86.RvOps
import VerifiedGarbage.Proof.Rsa.X86.RvScalarOps
import VerifiedGarbage.Proof.Rsa.X86.RvMontStage
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.Rsa.X86.RvFusedState
import VerifiedGarbage.Proof.Rsa.X86.RvFusedMasks
import VerifiedGarbage.Proof.Rsa.X86.RvFusedMultiply
import VerifiedGarbage.Proof.Rsa.X86.RvFusedScalar
import VerifiedGarbage.Proof.Rsa.X86.RvMontTracked
public import VerifiedGarbage.Proof.Rsa.X86.RvTimeFusedCheck -- shake: keep (public statements name the reducible fusedBefore/fusedAfter aliases)

/-! A fused bit has one constant-time Montgomery square and public candidate arithmetic. -/
@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa (b2n)

theorem fusedBefore_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {n j : Nat}
    {dn ok bit : Bool}
    (h : KS g s0 A (mX::fusedKeep) AW [wRc,wR] V (sBit::fusedKeepSlots) s)
    (value : A mBase=n) (modulus : A aN=n) (zero : A aZ=0)
    (bound : n<2^(64*g.n)) (inverse : (n*V sInv+1)%2^32=0)
    (positive : 0<n) (xl : A mX<n) (candidate : V sCand=j) (limit : j<100)
    (vd : V sDone=b2n dn) (vo : V sOk=b2n ok) (vb : V sBit=b2n bit) :
    WP isa fusedBefore s fun t => ∃ C : FusedMulData g n j, C.Pre t := by
  unfold fusedBefore VG.Impl.Rsa.X86.RecoverRt.eqAt
  apply WP.assoc'
  apply WP.assoc'
  refine WP.seq (WP.mono (h.eqS_w (d := sE1) (a := mX) (b := aO)
    (by simp) (by decide) (by decide) (by decide) (by decide) (by decide)) fun u1 ⟨h1,_⟩ => ?_)
  refine WP.seq (WP.mono (h1.eqS_w (d := sE2) (a := mX) (b := aNg)
    (by simp) (by decide) (by decide) (by decide) (by decide) (by decide)) fun u2 ⟨h2,_⟩ => ?_)
  refine WP.seq (WP.mono (fusedHit_ok (dn := dn) (ok := ok) (bit := bit)
    (e1 := decide (A mX=A aO)) (e2 := decide (A mX=A aNg)) h2
    (by decide) (by decide) (by decide) (by decide) (by decide)
    vd vo vb (by exact show (if A mX=A aO then 1 else 0)=b2n (decide (A mX=A aO)) from by simp [b2n])
    (by exact show (if A mX=A aNg then 1 else 0)=b2n (decide (A mX=A aNg)) from by simp [b2n])) fun u3 h3 => ?_)
  refine WP.mono (h3.sel_w (o := 0) (a := 0) (b := mY) (sl := sLive)
    (by decide) (by decide) (by decide) (by decide)
    (by exact VG.Proof.Rsa.b2n_le _) (.inr (by decide)) (by decide)) fun t ⟨ht,_⟩ => ?_
  have obs := ht.observe_w mXm (by decide)
  have ready := obs.mono (live' := fusedLive) (ls' := fusedSlots)
    (fun i hi => ⟨by revert i; decide,rfl⟩) (fun i hi => ⟨hi,rfl⟩)
    (fun d hd => ⟨by revert d; decide,rfl⟩)
  refine ⟨⟨s0,_,AW,_,?_,?_,?_,bound,?_,positive,?_,?_,limit⟩,ready⟩
  · exact value
  · exact modulus
  · exact zero
  · exact inverse
  · exact xl
  · exact candidate

theorem fusedMulSuffix_relCT {g : Geo} {n j : Nat} (pg : PubG g) :
    RelCT isa (fun s t => (∃ C : FusedMulData g n j, C.Pre s) ∧
      (∃ D : FusedMulData g n j, D.Pre t))
      (.seq VG.Impl.Rsa.X86.RecoverRt.fusedMultiply fusedAfter) (fun _ _ => True) := by
  intro s t tr ur sf tf ⟨⟨C,hs⟩,⟨D,ht⟩⟩ es et
  cases es with
  | @seq _ _ _ u _ _ _ e1 e2 =>
  cases et with
  | @seq _ _ _ v _ _ _ f1 f2 =>
  have eq1 := (fusedMultiply_relCT pg C D _ _ _ _ _ _ ⟨hs,ht⟩ e1 f1).1
  obtain ⟨_,hu⟩ := wp_result (fusedMultiply_ok hs C.value C.modulus C.zero C.bound C.inverse
    C.positive rfl C.xl (by rw [C.candidate]; exact C.limit)) e1
  obtain ⟨_,hv⟩ := wp_result (fusedMultiply_ok ht D.value D.modulus D.zero D.bound D.inverse
    D.positive rfl D.xl (by rw [D.candidate]; exact D.limit)) f1
  exact ⟨by rw [eq1,pub_trace pg fusedAfterCheck hu hv e2 f2],trivial⟩

theorem fusedBit_relCT {g : Geo} (pg : PubG g) {s0 t0 : State} {A B AW BW V W : Nat → Nat}
    {n k : Nat} {st tt : VG.Proof.Rsa.Fused.State}
    (valueA : A mBase=n) (valueB : B mBase=n)
    (modA : A aN=n) (modB : B aN=n) (zeroA : A aZ=0) (zeroB : B aZ=0)
    (bound : n<2^(64*g.n)) (invA : (n*V sInv+1)%2^32=0) (invB : (n*W sInv+1)%2^32=0)
    (positive : 0<n) (cand : V sCand=W sCand) (limit : V sCand<100)
    (smallA : V sWin<16) (smallB : W sWin<16) (hk : k≤3) :
    RelCT isa (fun s t => FI g s0 A AW V n st s ∧ FI g t0 B BW W n tt t)
      (VG.Impl.Rsa.X86.RecoverRt.fusedBit k) (fun _ _ => True) := by
  intro s t tr ur sf tf ⟨⟨z,zl,zr,hs⟩,⟨w,wl,wr,ht⟩⟩ es et
  cases es with
  | @seq _ _ _ u0 _ _ _ e0 er =>
  cases et with
  | @seq _ _ _ v0 _ _ _ f0 fr =>
  have eq0 := pub_trace pg (fusedBitHeadCheck k hk) hs ht e0 f0
  have hu0 := wp_result (hs.fusedBitHead_ok (by decide) (by exact smallA) k hk) e0
  have hv0 := wp_result (ht.fusedBitHead_ok (by decide) (by exact smallB) k hk) f0
  cases er with
  | @seq _ _ _ u1 _ _ _ e1 er =>
  cases fr with
  | @seq _ _ _ v1 _ _ _ f1 fr =>
  have mrA := hu0.montReady (by decide) (by decide) (by exact valueA) bound (by exact invA)
  have mrB := hv0.montReady (by decide) (by decide) (by exact valueB) bound (by exact invB)
  have ly : fusedA A n (2^(64*g.n)) st.value z mY<n := Nat.mod_lt _ positive
  have lz : fusedA B n (2^(64*g.n)) tt.value w mY<n := Nat.mod_lt _ positive
  have eq1 := (mmul_relCT pg (by decide) (by decide) (by decide) (by decide) mulArgs_mX_mY_mYCheck
    ⟨_,clrTop_mXCheck⟩ _ _ _ _ _ _
    ⟨⟨_,_,_,_,_,_,_,_,hu0,mrA,by decide,by decide,ly,ly,by decide,by decide⟩,
     ⟨_,_,_,_,_,_,_,_,hv0,mrB,by decide,by decide,lz,lz,by decide,by decide⟩⟩ e1 f1).1
  obtain ⟨X,hu1,_,_,xl,_⟩ := wp_result (hu0.mmul mrA (o := mX) (a := mY) (b := mY)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ly ly
    (by decide) (by decide)) e1
  obtain ⟨Y,hv1,_,_,yl,_⟩ := wp_result (hv0.mmul mrB (o := mX) (a := mY) (b := mY)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) lz lz
    (by decide) (by decide)) f1
  have bitA : ∃ bit, V sWin/2^k%2=b2n bit := by
    have h := Nat.mod_lt (V sWin/2^k) (by decide : 0<2)
    refine ⟨decide (V sWin/2^k%2=1),?_⟩
    simp only [b2n,decide_eq_true_eq]; split_ifs <;> omega
  have bitB : ∃ bit, W sWin/2^k%2=b2n bit := by
    have h := Nat.mod_lt (W sWin/2^k) (by decide : 0<2)
    refine ⟨decide (W sWin/2^k%2=1),?_⟩
    simp only [b2n,decide_eq_true_eq]; split_ifs <;> omega
  obtain ⟨ba,hba⟩ := bitA
  obtain ⟨bb,hbb⟩ := bitB
  have rest : RelCT isa (fun s t =>
      KS g s0 (upd (fusedA A n (2^(64*g.n)) st.value z) mX X) (mX::fusedKeep) AW [wRc,wR]
        (upd (fusedV V st) sBit (V sWin/2^k%2)) (sBit::fusedKeepSlots) s ∧
      KS g t0 (upd (fusedA B n (2^(64*g.n)) tt.value w) mX Y) (mX::fusedKeep) BW [wRc,wR]
        (upd (fusedV W tt) sBit (W sWin/2^k%2)) (sBit::fusedKeepSlots) t)
      (seqs [VG.Impl.Rsa.X86.RecoverRt.eqAt sE1 mX aO, VG.Impl.Rsa.X86.RecoverRt.eqAt sE2 mX aNg,
        VG.Impl.Rsa.X86.RecoverRt.fusedHit, VG.Impl.Rsa.X86.KeyRt.sel VG.Impl.Rsa.X86.RecoverRt.nar 0 0 mY sLive,
        VG.Impl.Rsa.X86.RecoverRt.fusedMultiply, VG.Impl.Rsa.X86.KeyRt.sel VG.Impl.Rsa.X86.RecoverRt.nar mY mX mXm sBit,
        VG.Impl.Rsa.X86.RecoverRt.eqAt sE1 mY aO, VG.Impl.Rsa.X86.RecoverRt.eqAt sE2 mY aNg,
        VG.Impl.Rsa.X86.RecoverRt.fusedTail]) (fun _ _ => True) := by
    simp only [seqs]
    apply VG.RelCT.assoc
    apply VG.RelCT.assoc
    apply VG.RelCT.assoc
    refine VG.RelCT.seq (R := fun s t => (∃ C : FusedMulData g n (V sCand), C.Pre s) ∧
      (∃ D : FusedMulData g n (V sCand), D.Pre t))
      (pub_relCT
        (P := KS g s0 (upd (fusedA A n (2^(64*g.n)) st.value z) mX X) (mX::fusedKeep) AW [wRc,wR]
          (upd (fusedV V st) sBit (V sWin/2^k%2)) (sBit::fusedKeepSlots))
        (Q := KS g t0 (upd (fusedA B n (2^(64*g.n)) tt.value w) mX Y) (mX::fusedKeep) BW [wRc,wR]
          (upd (fusedV W tt) sBit (W sWin/2^k%2)) (sBit::fusedKeepSlots))
        (P' := fun s => ∃ C : FusedMulData g n (V sCand), C.Pre s)
        (Q' := fun t => ∃ D : FusedMulData g n (V sCand), D.Pre t)
        pg fusedBeforeCheck (fun _ h => KS.stage h) (fun _ h => KS.stage h)
        (fun _ h => fusedBefore_ok h (by exact valueA) (by exact modA) (by exact zeroA) bound
          (by exact invA) positive (by exact xl) rfl limit rfl rfl hba)
        (fun _ h => fusedBefore_ok h (by exact valueB) (by exact modB) (by exact zeroB) bound
          (by exact invB) positive (by exact yl) cand.symm limit rfl rfl hbb)) ?_
    exact fusedMulSuffix_relCT pg
  have eq2 := (rest _ _ _ _ _ _ ⟨hu1,hv1⟩ er fr).1
  exact ⟨by rw [eq0,eq1,eq2],trivial⟩

end VG.Proof.Rsa.X86.Recover
