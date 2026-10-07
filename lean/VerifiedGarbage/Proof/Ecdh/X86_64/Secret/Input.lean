import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.Prep
import VerifiedGarbage.Proof.Weierstrass.JacMadd

/-! Canonical field inputs and the affine peer survive scalar preparation. -/
namespace VG.Proof.Ecdh.X86_64.Secret
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Impl.Ecdsa.X86_64 VG.Impl.Ecdh.X86_64.Window5
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64 Spec.Weierstrass
open VG.Impl.Ecdh.X86_64 (PX PY BP)

theorem input_fields {c : Cfg} (hc : CfgOk c) {s : State} {base : Addr}
    (hs : Scr s base size) {g : Reg → BitVec 64} (F : Fixed c base g s.mem)
    (hbp : sv c base s BP=c.mont c.C.b)
    (hpx : sv c base s PX<c.C.p) (hpy : sv c base s PY<c.C.p) :
    Inv (cfg c).M base size c.C.p (·∈slots (cfg c)) (winRo (cfg c)) (tmv c.C c.n base s) s := by
  have hp := hc.p_ge
  have hm : ∀ x,c.mont x<c.C.p := fun _ => Nat.mod_lt _ (by omega)
  refine ⟨hs,modP_of hc F.mp,?_,?_,fun _ _ => rfl⟩
  · intro x hx
    exact List.mem_append_left _ (List.mem_append_left _ hx)
  · intro x hx
    simp only [winRo,cfg,Cfg.winCfg,Cfg.rcbSlots,Cfg.pt,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl
    · exact lt_of_eq_of_lt F.ap (hm _)
    · exact lt_of_eq_of_lt hbp (hm _)
    · exact lt_of_eq_of_lt F.zero (by omega)
    · exact hpx
    · exact hpy
    · exact lt_of_eq_of_lt F.onep (Nat.mod_lt _ (by omega))

theorem PrepPost.fields {c : Cfg} (hc : CfgOk c) {base : Addr} {k : Nat} {s t : State}
    (h : PrepPost c base k s t) {g : Reg → BitVec 64} (F : Fixed c base g s.mem)
    (hbp : sv c base s BP=c.mont c.C.b)
    (hpx : sv c base s PX<c.C.p) (hpy : sv c base s PY<c.C.p) :
    Inv (cfg c).M base size c.C.p (·∈slots (cfg c)) (winRo (cfg c)) (tmv c.C c.n base t) t := by
  have e : ∀ {i},i<45 → sv c base t i=sv c base s i :=
    fun hi => sv_unch h.unch hc.n10 h.scr.nowrap hi (apart_winX hi)
  exact input_fields hc h.scr (F.unch hc.n10 h.scr.nowrap fixedOk_winX h.unch)
    ((e (by decide)).trans hbp) (by rw [e (by decide)]; exact hpx)
    (by rw [e (by decide)]; exact hpy)

theorem PrepPost.peer {c : Cfg} (hc : CfgOk c) (hC : Law c.C)
    {base : Addr} {k : Nat} {s t : State} (h : PrepPost c base k s t)
    {g : Reg → BitVec 64} (F : Fixed c base g s.mem) {P : Point c.C}
    (hrep : Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY))
      (tmv c.C c.n base s (c.sl ONEP)) P) :
    InvJ c.C (tmv c.C c.n base t (cfg c).P.x) (tmv c.C c.n base t (cfg c).P.y)
      (tmv c.C c.n base t (cfg c).P.z) P ∧
      tmv c.C c.n base t (cfg c).P.z=1 ∧ P≠.infinity := by
  have hpR := unitMod_pow_two hc.p_odd (64*c.n)
  have e : ∀ {i},i<45 → tmv c.C c.n base t (c.sl i)=tmv c.C c.n base s (c.sl i) := by
    intro i hi
    change toM _ _ (sv c base t i)=toM _ _ (sv c base s i)
    have ei : sv c base t i=sv c base s i := sv_unch h.unch hc.n10 h.scr.nowrap hi (apart_winX hi)
    rw [ei]
  have hz : tmv c.C c.n base s (c.sl ONEP)=1 := by
    change toM _ _ (wordsVal s.mem base (c.sl ONEP) c.n)=1
    rw [F.onep,toM_one hpR]
  rw [hz] at hrep
  have he := hrep.eq_affine hC
  change InvJ c.C (tmv c.C c.n base t (c.sl PX)) (tmv c.C c.n base t (c.sl PY))
    (tmv c.C c.n base t (c.sl ONEP)) P ∧ tmv c.C c.n base t (c.sl ONEP)=1 ∧ P≠.infinity
  rw [e (by decide),e (by decide),e (by decide),hz,he]
  exact ⟨InvJ.affine hC _ _,rfl,by intro hn; cases hn⟩

end VG.Proof.Ecdh.X86_64.Secret
