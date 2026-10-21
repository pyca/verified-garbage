module

public import VerifiedGarbage.Proof.Rsa.X86.RvFusedState
public import VerifiedGarbage.Proof.Rsa.X86.RvFusedScalar
import VerifiedGarbage.Proof.Rsa.X86.RvScalarOps
import VerifiedGarbage.Proof.Rsa.X86.RvOps
import VerifiedGarbage.Proof.Rsa.X86.RvFusedMultiply
import VerifiedGarbage.Proof.Rsa.X86.RvMontStage
import VerifiedGarbage.Proof.Bignum.Math
import Mathlib.Tactic.SplitIfs

/-! One binary exponentiation bit and its masked root-search transition. -/
@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa (b2n)

 theorem fusedBit_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {n k : Nat}
    {st : VG.Proof.Rsa.Fused.State} (h : FI g s0 A AW V n st s)
    (value : A mBase = n) (modulus : A aN = n) (zero : A aZ = 0)
    (bound : n < 2^(64*g.n)) (inverse : (n*V sInv+1)%2^32 = 0)
    (odd : n%2 = 1) (hn : 1 < n)
    (one : A aO = 2^(64*g.n)%n) (neg : A aNg = n-2^(64*g.n)%n)
    (candidate : V sCand < 100) (yl : st.value < n) (small : V sWin < 16) (hk : k ≤ 3) :
    WP isa (VG.Impl.Rsa.X86.RecoverRt.fusedBit k) s fun t =>
      FI g s0 A AW V n (VG.Proof.Rsa.Fused.step n (V sCand+2)
        (decide (V sWin/2^k%2 = 1)) st) t := by
  obtain ⟨z,zl,root,h⟩ := h
  let R := 2^(64*g.n)
  let x := st.value*st.value%n
  let bit := decide (V sWin/2^k%2 = 1)
  let hit := !st.done && decide (x=1) && !bit
  have bitword : V sWin/2^k%2 = b2n bit := by
    have := Nat.mod_lt (V sWin/2^k) (by decide : 0<2)
    dsimp only [bit,b2n]
    split_ifs <;> simp_all
  have positive : 0<n := by omega
  have cop := VG.Proof.Bignum.coprime_pow2 odd (64*g.n)
  unfold VG.Impl.Rsa.X86.RecoverRt.fusedBit
  simp only [seqs]
  refine WP.seq (WP.mono (h.fusedBitHead_ok (by decide) (by exact small) k hk) fun u0 h0 => ?_)
  change KS g s0 (fusedA A n R st.value z) fusedKeep AW [wRc,wR]
    (upd (fusedV V st) sBit (V sWin/2^k%2)) (sBit::fusedKeepSlots) u0 at h0
  rw [bitword] at h0
  have mr := h0.montReady (by decide) (by decide) (by exact value) bound (by exact inverse)
  refine WP.seq (WP.mono (h0.mmul mr (o := mX) (a := mY) (b := mY)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by change st.value*R%n<n; exact Nat.mod_lt _ positive)
    (by change st.value*R%n<n; exact Nat.mod_lt _ positive)
    (by decide) (by decide)) fun u1 ⟨X,h1,_,_,xl,xv⟩ => ?_)
  have square : X = x*R%n :=
    VG.Proof.Rsa.sq_mont cop (by rfl) xl xv
  rw [square] at h1
  unfold VG.Impl.Rsa.X86.RecoverRt.eqAt
  refine WP.seq (WP.mono (h1.eqS_w (d := sE1) (a := mX) (b := aO)
    (by simp) (by decide) (by decide) (by decide) (by decide) (by decide)) fun u2 ⟨h2,_⟩ => ?_)
  refine WP.seq (WP.mono (h2.eqS_w (d := sE2) (a := mX) (b := aNg)
    (by simp) (by decide) (by decide) (by decide) (by decide) (by decide)) fun u3 ⟨h3,_⟩ => ?_)
  have eo : (if x*R%n = A aO then 1 else 0) = b2n (decide (x=1)) := by
    rw [one]
    have eq : x*R%n = 2^(64*g.n)%n ↔ x=1 :=
      VG.Proof.Rsa.eq_one_mont cop hn (Nat.mod_lt _ positive) rfl
    simp only [eq,b2n,decide_eq_true_eq]
  have en : (if x*R%n = A aNg then 1 else 0) = b2n (decide (x=n-1)) := by
    rw [neg]
    have eq : x*R%n = n-2^(64*g.n)%n ↔ x=n-1 :=
      VG.Proof.Rsa.eq_neg_mont cop hn (Nat.mod_lt _ positive) rfl
    simp only [eq,b2n,decide_eq_true_eq]
  refine WP.seq (WP.mono (fusedHit_ok (dn := st.done) (ok := st.root.isSome) (bit := bit)
    (e1 := decide (x=1)) (e2 := decide (x=n-1)) h3
    (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl rfl eo en) fun u4 h4 => ?_)
  refine WP.seq (WP.mono (h4.sel_w (o := 0) (a := 0) (b := mY) (sl := sLive)
    (by decide) (by decide) (by decide) (by decide)
    (by change b2n hit ≤ 1; exact VG.Proof.Rsa.b2n_le _) (.inr (by decide)) (by decide))
    fun u5 ⟨h5,_⟩ => ?_)
  have observed := h5.observe_w mXm (by decide)
  have ready := observed.mono (live' := fusedLive) (ls' := fusedSlots)
    (fun j hj => ⟨by revert j; decide,rfl⟩) (fun j hj => ⟨hj,rfl⟩)
    (fun d hd => ⟨by revert d; decide,rfl⟩)
  refine WP.seq (WP.mono (fusedMultiply_ok (x := x*R%n) ready (by exact value) (by exact modulus) (by exact zero)
    bound (by exact inverse) positive (by rfl) (Nat.mod_lt _ positive)
    (by exact candidate)) fun u6 ⟨yTmp,h6⟩ => ?_)
  refine WP.seq (WP.mono (h6.sel_w (o := mY) (a := mX) (b := mXm) (sl := sBit)
    (by decide) (by decide) (by decide) (by decide)
    (by change b2n bit ≤ 1; exact VG.Proof.Rsa.b2n_le _) (.inl (by decide)) (by decide))
    fun u7 ⟨h7,_⟩ => ?_)
  let next := VG.Proof.Rsa.Fused.step n (V sCand+2) bit st
  let z' := if hit then st.value else z
  let VH := upd (upd (upd V sBit (b2n bit))
    sDone (b2n ((st.done || decide (x=1) || decide (x=n-1)) && !bit)))
    sOk (b2n ((st.root.isSome || hit) && !bit))
  have mul : (V sCand+2)*(x*R%n)%n = (x*(V sCand+2)%n)*R%n := by
    rw [Nat.mul_mod_mod,Nat.mod_mul_mod]
    congr 1
    ac_rfl
  have nv : next.value = if bit then x*(V sCand+2)%n else x :=
    VG.Proof.Rsa.Fused.step_value n (V sCand+2) bit st
  have nr : next.root = if bit then none else
      if !st.done && decide (x=1) then some st.value else st.root :=
    VG.Proof.Rsa.Fused.step_root n (V sCand+2) bit st
  have powerValue : (if b2n bit=0 then x*R%n else (V sCand+2)*(x*R%n)%n) = next.value*R%n := by
    rw [nv]
    cases bit
    · simp [b2n]
    · simpa only [b2n,↓reduceIte,show ¬(1:Nat)=0 by decide] using mul
  have saved : (if b2n hit=0 then z*R%n else st.value*R%n) = z'*R%n := by
    cases hh : hit <;> simp [z',hh,b2n]
  have h7' : KS g s0 (fusedA A n R next.value z') fusedKeep AW [wRc,wR] VH fusedSlots u7 := by
    refine h7.mono (fun j hj => ⟨by revert j; decide, ?_⟩)
      (fun j hj => ⟨hj,rfl⟩) (fun d hd => ⟨hd,?_⟩)
    · simp only [fusedKeep,liveM,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hj
      rcases hj with (rfl | rfl) | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact saved
      · exact powerValue
      all_goals rfl
    · simp only [fusedSlots,List.mem_cons,List.not_mem_nil,or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  refine WP.seq (WP.mono (h7'.eqS_w (d := sE1) (a := mY) (b := aO)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) fun u8 ⟨h8,_⟩ => ?_)
  refine WP.seq (WP.mono (h8.eqS_w (d := sE2) (a := mY) (b := aNg)
    (by simp) (by decide) (by decide) (by decide) (by decide) (by decide)) fun u9 ⟨h9,_⟩ => ?_)
  have nl : next.value<n := by
    rw [nv]
    split <;> exact Nat.mod_lt _ positive
  have eo' : (if next.value*R%n = A aO then 1 else 0) = b2n (decide (next.value=1)) := by
    rw [one]
    have eq : next.value*R%n = 2^(64*g.n)%n ↔ next.value=1 :=
      VG.Proof.Rsa.eq_one_mont cop hn nl rfl
    simp only [eq,b2n,decide_eq_true_eq]
  have en' : (if next.value*R%n = A aNg then 1 else 0) = b2n (decide (next.value=n-1)) := by
    rw [neg]
    have eq : next.value*R%n = n-2^(64*g.n)%n ↔ next.value=n-1 :=
      VG.Proof.Rsa.eq_neg_mont cop hn nl rfl
    simp only [eq,b2n,decide_eq_true_eq]
  refine WP.mono (fusedTail_ok (dn := (st.done || decide (x=1) || decide (x=n-1)) && !bit)
    (bit := bit) (e1 := decide (next.value=1)) (e2 := decide (next.value=n-1)) h9
    (by decide) (by decide) (by decide) rfl rfl eo' en') fun t ht => ?_
  refine ⟨z', ?_, ?_, ?_⟩
  · dsimp only [z']; split <;> with_reducible assumption
  · intro r hr
    change next.root=some r at hr
    rw [nr] at hr
    cases hb : bit
    · rw [hb] at hr
      change (if (!st.done && decide (x=1)) then some st.value else st.root) = some r at hr
      by_cases hh : (!st.done && decide (x=1)) = true
      · have hhit : hit = true := by simp [hit,hb,hh]
        rw [hh] at hr
        simp only [↓reduceIte,Option.some.injEq] at hr
        simpa only [z',hhit,↓reduceIte] using hr
      · have hhit : hit = false := by simp [hit,hb,hh]
        have old : st.root=some r := by simpa only [hh,↓reduceIte,Bool.false_eq_true] using hr
        simpa only [z',hhit,Bool.false_eq_true,↓reduceIte] using root r old
    · rw [hb] at hr
      cases hr
  · have flags := VG.Proof.Rsa.Fused.step_flags n (V sCand+2) bit st
    refine ht.mono (fun j hj => ⟨hj,rfl⟩) (fun j hj => ⟨hj,rfl⟩) fun d hd => ⟨by revert d; decide, ?_⟩
    simp only [fusedKeepSlots,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try rfl
    · change b2n _ = b2n next.done
      exact congrArg b2n flags.1.symm
    · change b2n _ = b2n next.root.isSome
      exact congrArg b2n flags.2.symm

end VG.Proof.Rsa.X86.Recover
