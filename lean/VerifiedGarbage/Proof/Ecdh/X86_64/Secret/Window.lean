import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.TableBuild
import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.ScalarInit
import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.Finish

/-! Complete secret-window multiplication: table construction, initialization, scalar loop and X-only finish. -/
namespace VG.Proof.Ecdh.X86_64.Secret
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open Spec.Weierstrass

theorem SecretLay.ro_not_writes {K : WinCfg} {size : Nat} (hL : SecretLay K size) :
    ∀ x∈winRo K,x∉writes K := by
  intro x hx hw
  rcases List.mem_append.mp hw with hw|hw
  · exact hL.ro x hx hw
  · have hh := hL.tbl x (List.mem_append_left _ hx)
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hw
    have hi' := List.mem_range.mp hi
    omega

theorem writes_slots (K : WinCfg) : ∀ x∈writes K,x∈slots K := by
  intro x hx
  rcases List.mem_append.mp hx with hx|hx
  · exact local_slots K x hx
  · exact List.mem_append_right _ hx

theorem window_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat}
    (hCurve : C=Spec.P256.curve) (hL : SecretLay K size) (hm : UnitMod C.p (2^(64*K.M.n)))
    (hC : Law C) (ha : AM3 C) (hO : PeerOrder C)
    (ht : K.tbl<2^31) (hOne : K.one<C.p)
    (hOneVal : toM C.p (2^(64*K.M.n)) K.one=1)
    (hJ2 : 2≤K.J) (hfit : recoded K k<32^K.J)
    {P : Point C} (hP : onCurve C P=true) (hne : P≠.infinity)
    {s : State} {E : Nat → Fin C.p}
    (hI : Inv K.M base size C.p (·∈slots K) (winRo K) E s)
    (hJP : InvJ C (E K.P.x) (E K.P.y) (E K.P.z) P)
    (hAff : E K.P.z=1) (h0 : E K.zero=0) (hb : ScalarBits K base (recoded K k) s) :
    WP isa (Impl.Ecdh.X86_64.Window5.window K) s (WindowPost K C base size k P s) := by
  subst C
  rw [Impl.Ecdh.X86_64.Window5.window]
  apply WP.seq
  refine WP.mono (table_build_ok hL hm hC ha hO ht hOne hOneVal hP hne hI hJP hAff)
    fun a ia => ?_
  have ba := hb.keep hL hI.scr ia.keep (fun _ hx => hx)
  have za : tmv Spec.P256.curve K.M.n base a K.zero=0 := by
    rw [ia.keep.field_eq hL.lay hI ia.field (writes_slots K)
      (by simp [winRo]) (by simp [tableLive,winRo])
      (hL.ro_not_writes K.zero (by simp [winRo])),h0]
  have da : TableData K Spec.P256.curve (tmv Spec.P256.curve K.M.n base a) P :=
    ⟨za,ia.table,ia.cache⟩
  apply WP.seq
  have init := scalar_init_ok (C:=Spec.P256.curve) hL hm hC ht hOne hOneVal hfit hP
    ia.field da ba ia.keep
  refine WP.mono (by simpa only [List.append_assoc] using init) fun b ib => ?_
  apply WP.seq
  exact WP.mono (scalar_loop_ok hL hm hC ha hO ht hOne hOneVal (by omega) (by omega)
    hP hne ib) (fun _ il => scalar_finish_ok hL hm hC il)

end VG.Proof.Ecdh.X86_64.Secret
