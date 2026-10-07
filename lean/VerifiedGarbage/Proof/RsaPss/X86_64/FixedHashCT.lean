import VerifiedGarbage.Proof.RsaPss.X86_64.CtHashCT

/-! Constant time of MGF1's fixed-length padding. -/
namespace VG.Proof.RsaPss.X86_64
open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.Bignum.X86_64 (Two two_post two_map)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)

variable {H : Hash} (hH : HashOK H) (K : Callees H) (n : Nat)

/-- MGF1's hash has the compile-time length `D + 4`. -/
def HEFixed (H : Hash) (n : Nat) (a : HA) (t : State) : Prop :=
  HOk (H := H) n a ∧ Pub a.F a.S a.rest (hws a) []
    (fun _ W => W 27 = BitVec.ofNat 64 (H.D + 4) ∧ H.D + 4 + 1 + H.P.L ≤ a.nbm * H.P.B) t

theorem HEFixed.toHE {a : HA} {t : State} (h : HEFixed H n a t) : HE H n a t :=
  ⟨h.1, h.2.sub (fun _ h => h) (fun _ h => h) fun _ _ ⟨hl, hf⟩ => ⟨H.D + 4, hl, hf⟩⟩

include hH K in
theorem fixedInit_ct (hfx : FixedChecks n) :
    RelCT isa (Two (HEFixed H n)) (ctInit H) (Two (HEFixed H n)) := by
  refine two_post ((ctInit_ct hH K n hfx).mono (fun _ _ ⟨a, h1, h2⟩ =>
    ⟨a, HEFixed.toHE n h1, HEFixed.toHE n h2⟩) (fun _ _ _ => trivial)) fun a t h => ?_
  obtain ⟨V, W, R, hw, hx⟩ := h.2.W
  exact WP.mono (ctInit_ok hH K h.2.L R) fun u ⟨L', _, hwr, _, R', _⟩ =>
    ⟨h.1, h.2.next L' hwr R' hw hx⟩

theorem fixedPad_ct (hc : HashChecks H.P H.D n) :
    RelCT isa (Two (HEFixed H n)) (fixedPad80 (H.D + 4)) (Two (HE H n)) := by
  obtain ⟨_, hp⟩ := hc.fixedPad80
  refine two_post (two_pub n [21, 28] [] HA.F HA.S HA.rest hws (fun _ => []) (fun a t h => ⟨_, h.2⟩)
    (fun a t h => h.1.1) (fun _ => rfl) (fun _ => rfl) (by decide) hp) fun a t h => ?_
  obtain ⟨V, W, R, hw, hl, hfit⟩ := h.2.W
  obtain ⟨_, _, hnb⟩ := h.1
  refine WP.mono (fixedPad80_ok h.2.L R (N := a.nbm * H.P.B) (by omega) hnb) fun u P => ?_
  have h' : HEFixed H n a u := ⟨h.1, h.2.next P.L P.keep.2.2 P.R hw ⟨hl, hfit⟩⟩
  exact HEFixed.toHE n h'

include hH K in
theorem mgfGenericHash_ct (hc : HashChecks H.P H.D n) (hfx : FixedChecks n) :
    RelCT isa (Two (HEFixed H n)) (mgfGenericHash H) fun _ _ => True := by
  unfold mgfGenericHash ctHashWith seqs seqs seqs seqs seqs
  exact (fixedInit_ct hH K n hfx).seq ((fixedPad_ct n hc).seq ((lenField_ct hH n hc).seq
    ((lenLoop_ct hH n hc).seq ((compLoop_ct hH n hc hfx).seq (digestOut_ct n hc)))))
end VG.Proof.RsaPss.X86_64
