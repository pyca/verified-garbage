import VerifiedGarbage.Proof.RsaPss.X86_64.FixedHashCT
import VerifiedGarbage.Proof.RsaPss.X86_64.MgfDirect

/-! A fixed one-block MGF1 hash never selects a secret final block. -/
namespace VG.Proof.RsaPss.X86_64
open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.Bignum.X86_64 (Two two_map two_post)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)

variable {H : Hash} (hH : HashOK H) (K : Callees H) (n : Nat)

theorem digestState_ct (hc : HashChecks H.P H.D n) :
    RelCT isa (Two (HB (H := H) n)) (.block (digestAt H oSt)) fun _ _ => True := by
  obtain ⟨_, hp⟩ := hc.digestState
  exact two_pub n [21] [] (fun p => p.1.F) (fun p => p.1.S) (fun p => p.1.rest)
    (fun p => [(21, p.1.S)]) (fun _ => [])
    (fun p t h => ⟨_, (hb_pub n h).sub (fun q hq => by
      rw [List.mem_singleton.mp hq]; simp) (fun _ h => h) (fun _ _ _ => True.intro)⟩)
    (fun p t h => h.2.1.1) (fun _ => rfl) (fun _ => rfl) (by decide) hp

include hH in
theorem directLen_ct (hc : HashChecks H.P H.D n) :
    RelCT isa (Two (HF H n)) (directLen H) (Two (HF H n)) := by
  obtain ⟨_, hp⟩ := hc.directLen
  refine two_post (two_pub n [21] [] HA.F HA.S HA.rest (fun a => [(21, a.S)]) (fun _ => [])
    (fun a t h => ⟨_, h.2.sub (mem21 (by simp [hws])) (fun _ h => h) fun _ _ h => h⟩)
    (fun a t h => h.1.1) (fun _ => rfl) (fun _ => rfl) (by decide) hp) fun a t h => ?_
  obtain ⟨V, W, R, hw, hx⟩ := h.2.W
  exact WP.mono (directLen_ok hH h.2.L R (len := (List.range H.P.L).map fun i => V (oLen + i))
    (fun i hi => by simp [List.getD_eq_getElem?_getD, hi])) fun u ⟨Lu, ku, Ru⟩ =>
      ⟨h.1, h.2.next Lu ku.2.2 Ru hw hx⟩

include hH K in
theorem mgfDirectHash_ct (hc : HashChecks H.P H.D n) (hfx : FixedChecks n) :
    RelCT isa (Two (HEFixed H n)) (mgfDirectHash H) fun _ _ => True := by
  unfold mgfDirectHash seqs seqs seqs seqs seqs seqs
  refine (fixedInit_ct hH K n hfx).seq ((fixedPad_ct n hc).seq ((lenField_ct hH n hc).seq
    ((directLen_ct hH n hc).seq ((startB_ct n hfx).seq ?_))))
  exact two_map (fun a : HA => (a, 0)) (fun _ _ h => h)
    ((compA_ct hH n hc).seq (digestState_ct n hc))

include hH K in
theorem mgfHash_ct (hc : HashChecks H.P H.D n) (hfx : FixedChecks n) :
    RelCT isa (Two (HEFixed H n)) (mgfHash H) fun _ _ => True := by
  unfold mgfHash
  split
  · exact mgfDirectHash_ct hH K n hc hfx
  · exact mgfGenericHash_ct hH K n hc hfx

end VG.Proof.RsaPss.X86_64
