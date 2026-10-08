import VerifiedGarbage.Proof.Weierstrass.X86.WinJacLayout
import VerifiedGarbage.Proof.Weierstrass.X86.WinJacSelect
import VerifiedGarbage.Proof.Weierstrass.X86.NafState

/-! Cached Jacobian points and their preservation through low-slot field programs. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

structure Cached (C : Curve) (base : Addr) (s : State) (o : Nat → Nat) (Q : Point C) : Prop where
  lt : ∀ c<5,wordsVal s.mem base (o c) 4<C.p
  jac : InvJ C (tmv C 4 base s (o 0)) (tmv C 4 base s (o 1)) (tmv C 4 base s (o 2)) Q
  z : tmv C 4 base s (o 2)≠0
  z2 : tmv C 4 base s (o 3)=tmv C 4 base s (o 2)*tmv C 4 base s (o 2)
  z3 : tmv C 4 base s (o 4)=tmv C 4 base s (o 3)*tmv C 4 base s (o 2)

theorem Cached.congr {C : Curve} {base : Addr} {s t : State} {o p : Nat → Nat} {Q : Point C}
    (h : Cached C base s o Q) (he : ∀ c<5,wordsVal t.mem base (p c) 4=wordsVal s.mem base (o c) 4) :
    Cached C base t p Q := by
  have e : ∀ c<5,tmv C 4 base t (p c)=tmv C 4 base s (o c) := fun c hc => by
    unfold tmv
    rw [he c hc]
  refine ⟨fun c hc => by rw [he c hc]; exact h.lt c hc,?_,?_,?_,?_⟩
  · rw [e 0 (by decide),e 1 (by decide),e 2 (by decide)]; exact h.jac
  · rw [e 2 (by decide)]; exact h.z
  · rw [e 3 (by decide),e 2 (by decide)]; exact h.z2
  · rw [e 4 (by decide),e 3 (by decide),e 2 (by decide)]; exact h.z3

def Table (K : JacWinCfg) (C : Curve) (base : Addr) (P : Point C) (M : Nat) (s : State) : Prop :=
  ∀ m,1≤m → m≤M → Cached C base s (K.entry (m-1)) (mul m P)

theorem Table.field_keep {K : JacWinCfg} {C : Curve} {base : Addr} {size wk M : Nat}
    (hL : Layout K size wk) {s t : State} {W : List Nat} (hs : Scr s base size)
    (hk : ProgKeep K.M base wk W s t) (hW : ∀ x∈W,x∈work K)
    {P : Point C} (hT : Table K C base P M s) (hM : M≤16) : Table K C base P M t := by
  intro m h1 hm
  exact (hT m h1 hm).congr fun c hc => field_keep_entry hL hs hk hW (by omega) hc

/-- The selected nonzero magnitude represents the corresponding point,
with both cached powers carried along by the two scans. -/
theorem select_nonzero_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size a : Nat}
    {s : State} (hs : Scr s base size) (ha : 1≤a) (ha16 : a≤16)
    (hb : s.gpr .ebx=BitVec.ofNat 32 a) (ht : K.tbl+2560≤size) (ho : K.T+160≤size)
    (hsep : K.T+160≤K.tbl) {P : Point C} (hT : Table K C base P 16 s) :
    WP isa (.block K.select) s fun t =>
      Cached C base t (fun c => K.T+32*c) (mul a P) ∧
      Outside base K.T 160 s.mem t.mem ∧ KeepRegs [.ecx,.edx] s t := by
  refine WP.mono (select_ok hs ha16 hb ht ho hsep) fun t ⟨et,ot,kt⟩ => ⟨?_,ot,kt⟩
  exact (hT a ha ha16).congr fun c hc => by simpa only [ha,ite_true] using et c hc

end VG.Proof.Weierstrass.X86.JWin
