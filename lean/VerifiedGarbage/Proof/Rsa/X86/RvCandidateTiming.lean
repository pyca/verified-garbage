module
public import VerifiedGarbage.Proof.Bignum.X86.PublicArgumentTiming
public import VerifiedGarbage.Spec.Weierstrass.Point
public import VerifiedGarbage.Proof.Bignum.X86.PublicCall
public import VerifiedGarbage.Proof.Rsa.X86.RvMont
public import VerifiedGarbage.Proof.Rsa.X86.RvExpInvariant

<<<<<<< HEAD
import VerifiedGarbage.Proof.Rsa.X86.RvAddressTiming
import VerifiedGarbage.Proof.Rsa.X86.RvExpTiming
import VerifiedGarbage.Proof.Rsa.X86.RvCandidateExpInit
import VerifiedGarbage.Proof.Rsa.X86.RvLoopTiming
import VerifiedGarbage.Proof.Rsa.X86.RvCandidateSet
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.X86.RelCT
=======
public import VerifiedGarbage.Proof.Rsa.X86.RvAddressTiming
public import VerifiedGarbage.Proof.Rsa.X86.RvLoopTiming
public import VerifiedGarbage.Proof.Rsa.X86.RvHelperTiming
public import VerifiedGarbage.Proof.Rsa.X86.RvCandidateExp
>>>>>>> origin/claude/x86-rsa-crt-rt

/-! # Candidate exponentiation relates different private exponents -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Mont.X86.Dynamic (workspaceTaint)

structure CandidateData (g : Geo) (m eLen dLen : Nat) where
  s0 : State
  A : Nat → Nat
  AW : Nat → Nat
  V : Nat → Nat
  zero : A aZ = 0
  value : A mBase = m
  bound : m < 2 ^ (64 * g.n)
  inverse : (m * V sInv + 1) % 2 ^ 32 = 0
  odd : m % 2 = 1
  large : 101 < m
  one : A aO = 2 ^ (64 * g.n) % m
  neg : A aNg = m - 2 ^ (64 * g.n) % m
  r2 : A mR2 = 2 ^ (128 * g.n) % m
  candidate : V sCand < 100
  baseBound : V sCand + 2 < m
  ae : CallArgument s0 g.B g.Z 7 (BitVec.ofNat 32 eLen)
  ad : CallArgument s0 g.B g.Z 9 (BitVec.ofNat 32 dLen)
  tc : V sTc ≤ 8 * (dLen + eLen)
  rb : AW wR < 2 ^ (8 * (dLen + eLen))
  count : 0 < 8 * (dLen + eLen)
  limit : 8 * (dLen + eLen) ≤ 16384
  wide : 8 * (dLen + eLen) < 32 * g.W

def CandidateData.Start {g : Geo} {m eLen dLen : Nat} (C : CandidateData g m eLen dLen) (s : State) :=
  KS g C.s0 C.A liveM C.AW [wR] C.V slotsExp s

/-- The candidate's power, as the squaring loop takes it. -/
def CandidateData.Exp {g : Geo} {m eLen dLen : Nat} (C : CandidateData g m eLen dLen) (s : State) :=
  KS g C.s0 (upd C.A mY (Spec.Rsa.powMod (C.V sCand + 2) (C.AW wR) m * 2 ^ (64 * g.n) % m)) liveSq
    C.AW [wR] (upd C.V sCnt 0) slotsExp s

theorem ks_address_agree {g : Geo} {s0 t0 s t : State} {A B AW BW V W : Nat → Nat}
    {al bl aw bw sl tl : List Nat}
    (h : KS g s0 A al AW aw V sl s) (j : KS g t0 B bl BW bw W tl t)
    (sp : s0.gpr .esp = t0.gpr .esp) : VG.X86.Taint.Agree argumentTaint s t := by
  apply agree_regs (rs := [.edi, .esp])
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (ks_agree h j).rf.1 _ (by decide)
  · exact (h.rest.1 _ (by decide)).trans (sp.trans (j.rest.1 _ (by decide)).symm)

theorem workspace_relCT {c : Prog isa} (pub : WorkspacePublic c) {P Q P' Q' : State → Prop}
    (agree : ∀ s t, P s → Q t → VG.X86.Taint.Agree (workspaceTaint false) s t)
    (left : ∀ s, P s → WP isa c s P') (right : ∀ t, Q t → WP isa c t Q') :
    RelCT isa (fun s t => P s ∧ Q t) c (fun s t => P' s ∧ Q' t) := by
  intro s t tr ur sf tf ⟨hs, ht⟩ es et
  exact ⟨(pub.trace _ _ _ _ _ _ (agree s t hs ht) es et).1, wp_result (left s hs) es,
    wp_result (right t ht) et⟩

theorem address_relCT {c : Prog isa} (pub : AddressPublic c) {P Q P' Q' : State → Prop}
    (agree : ∀ s t, P s → Q t → VG.X86.Taint.Agree argumentTaint s t)
    (left : ∀ s, P s → WP isa c s P') (right : ∀ t, Q t → WP isa c t Q') :
    RelCT isa (fun s t => P s ∧ Q t) c (fun s t => P' s ∧ Q' t) := by
  intro s t tr ur sf tf ⟨hs, ht⟩ es et
  exact ⟨(pub.trace _ _ _ _ _ _ (agree s t hs ht) es et).1, wp_result (left s hs) es,
    wp_result (right t ht) et⟩

section
variable {g : Geo} {m eLen dLen : Nat} (C : CandidateData g m eLen dLen)

/-- The exponent's alignment after `k` shifts. -/
abbrev CandidateData.Align (k : Nat) (s : State) : Prop :=
  AI g C.s0 (candA C.A C.V) (upd C.AW wRc (C.AW wR)) C.V (C.AW wR) (alignShifts g eLen dLen) k s

abbrev CandidateData.Mont (s : State) : Prop :=
  KS g C.s0 (candMontA C.A C.V g.n m) liveExp (upd C.AW wRc (alignedExp g (C.AW wR) eLen dLen))
    [wRc, wR] (upd C.V sCnt 0) slotsExp s

abbrev CandidateData.Table (s : State) : Prop :=
  KS g C.s0 (tableA (candMontA C.A C.V g.n m) g.n m (C.V sCand + 2) 16) (List.range 16 ++ liveExp)
    (upd C.AW wRc (alignedExp g (C.AW wR) eLen dLen)) [wRc, wR] (upd C.V sCnt 0) slotsExp s

abbrev CandidateData.Window (k : Nat) (s : State) : Prop :=
  WI g C.s0 (tableA (candMontA C.A C.V g.n m) g.n m (C.V sCand + 2) 16) C.AW C.V m (C.V sCand + 2)
    (alignedExp g (C.AW wR) eLen dLen) (2 * (dLen + eLen)) k s

end

theorem candExp_relCT {g : Geo} {m eLen dLen : Nat} (C D : CandidateData g m eLen dLen)
    (sp : C.s0.gpr .esp = D.s0.gpr .esp) :
    RelCT isa (fun s t => C.Start s ∧ D.Start t) (candExp g.n)
      (fun s t => C.Exp s ∧ D.Exp t) := by
  have positive : 0 < m := by have := C.large; omega
  have shifts : ∀ {s : State} {k : Nat}, C.Align k s → alignShifts g eLen dLen < 2 ^ 32 :=
    fun hs => by have := geo_wide g (KS.upper hs); unfold alignShifts; omega
  have shifts' : ∀ {s : State} {k : Nat}, D.Align k s → alignShifts g eLen dLen < 2 ^ 32 :=
    fun hs => by have := geo_wide g (KS.upper hs); unfold alignShifts; omega
  unfold candExp
  simp only [seqs]
  refine VG.RelCT.seq (R := fun s t => C.Align 0 s ∧ D.Align 0 t)
    (address_relCT (P := C.Start) (Q := D.Start) (P' := C.Align 0) (Q' := D.Align 0)
      (alignStart_address g.n) (fun s t hs ht => ks_address_agree hs ht sp)
      (fun s hs => alignStart_ok hs C.zero C.candidate C.ae C.ad C.wide C.rb)
      (fun t ht => alignStart_ok ht D.zero D.candidate D.ae D.ad D.wide D.rb)) ?_
  refine VG.RelCT.seq (R := fun s t => C.Align (alignShifts g eLen dLen) s ∧
      D.Align (alignShifts g eLen dLen) t)
    (fixedLoop_relCT (body := alignBody g.n) (fun k s => C.Align k s) (fun k t => D.Align k t)
      (by unfold alignShifts; have := C.wide; omega) (alignBody_workspace g.n)
      (fun k s t hs ht => ks_agree hs ht)
      (fun k s hk hs => alignBody_ok hs hk (shifts hs))
      (fun k t hk ht => alignBody_ok ht hk (shifts' ht))) ?_
  refine VG.RelCT.seq (R := fun s t => C.Mont s ∧ D.Mont t)
    (workspace_relCT (P := C.Align (alignShifts g eLen dLen)) (Q := D.Align (alignShifts g eLen dLen))
      (P' := C.Mont) (Q' := D.Mont) (mmul_public g.n mG mG mR2) (fun s t hs ht => ks_agree hs ht)
      (fun s hs => candMont_ok hs C.value C.bound C.inverse C.odd C.r2 C.baseBound C.wide C.rb)
      (fun t ht => candMont_ok ht D.value D.bound D.inverse D.odd D.r2 D.baseBound D.wide D.rb)) ?_
  refine VG.RelCT.seq (R := fun s t => C.Table s ∧ D.Table t)
    (workspace_relCT (P := C.Mont) (Q := D.Mont) (P' := C.Table) (Q' := D.Table)
      (table_workspace g.n) (fun s t hs ht => ks_agree hs ht)
      (fun s hs => candTable_ok hs C.value C.bound C.inverse C.odd C.one positive)
      (fun t ht => candTable_ok ht D.value D.bound D.inverse D.odd D.one positive)) ?_
  refine VG.RelCT.seq (R := fun s t => C.Window 0 s ∧ D.Window 0 t)
    (address_relCT (P := C.Table) (Q := D.Table) (P' := C.Window 0) (Q' := D.Window 0)
      windowCount_address (fun s t hs ht => ks_address_agree hs ht sp)
      (fun s hs => tableStart_ok hs C.one C.ae C.ad C.wide C.rb)
      (fun t ht => tableStart_ok ht D.one D.ae D.ad D.wide D.rb)) ?_
  refine (fixedLoop_relCT (body := windowBody g.n) (fun k s => C.Window k s) (fun k t => D.Window k t)
      (by have := C.count; omega) (windowBody_workspace g.n)
      (fun k s t hs ht => ks_agree hs ht)
      (fun k s hk hs => windowBody_ok hs (fun j hj => by simp only [tableA, hj, ↓reduceIte])
        (by simp only [tableA, show ¬ mBase < 16 by decide, ↓reduceIte, candMontA]
            rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide)]; exact C.value)
        C.bound C.inverse C.odd positive hk (by have := C.limit; omega))
      (fun k t hk ht => windowBody_ok ht (fun j hj => by simp only [tableA, hj, ↓reduceIte])
        (by simp only [tableA, show ¬ mBase < 16 by decide, ↓reduceIte, candMontA]
            rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide)]; exact D.value)
        D.bound D.inverse D.odd positive hk (by have := D.limit; omega))).mono
    (fun s t h => h) (fun s t ⟨hs, ht⟩ => ⟨windows_done hs C.wide, windows_done ht D.wide⟩)

end VG.Proof.Rsa.X86.Recover
