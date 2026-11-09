module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.Fprog
public import VerifiedGarbage.Proof.Weierstrass.JacMadd
public import VerifiedGarbage.Impl.Weierstrass.AArch64
public import VerifiedGarbage.Proof.Mont.AArch64.Ops
public import VerifiedGarbage.Proof.Weierstrass.Env
public import VerifiedGarbage.Proof.Weierstrass.Unch
import Batteries.Logic

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 Spec.Weierstrass

/-- A field compiler's exact values, bounds and memory frame at a fixed scratch size. -/
def FieldCompilerCorrect (arithmetic : Mod → List FOp → Prog isa) (size : Nat) : Prop :=
  ∀ (M : Mod) (base : Addr) (m : Nat) [NeZero m] (Sl : Nat → Prop),
    Lay M size Sl → Aligned M Sl → UnitMod m (2^(64*M.n)) →
    ∀ (ops : List FOp) (V : List Nat) (E : Nat → Fin m) (s : State),
    Inv M base size m Sl V E s →
    (∀ op∈ops,∀ x∈op.out::op.ins,Sl x) → (∀ op∈ops, Low M (op.out::op.ins)) → readsOk ops V=true →
    WP isa (arithmetic M ops) s fun t => ProgKeep M base (ops.map FOp.out) s t ∧
      Inv M base size m Sl (validAfter ops V) (runOps ops E) t

/-- `ProgKeep`, but for the registers `X` too, which the code may also change. -/
structure ProgKeepOn (X : List Reg) (M : Mod) (base : Addr) (W : List Nat) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ clob M.n ++ X → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  mem : ∀ x, (∀ w ∈ W, ofs base x < w ∨ w + 8 * M.n ≤ ofs base x) →
    (ofs base x < M.tmp ∨ M.tmp + 8 * M.n ≤ ofs base x) → s'.mem x = s.mem x

theorem ProgKeep.on {M : Mod} {base : Addr} {W : List Nat} {s s' : State} (h : ProgKeep M base W s s')
    (X : List Reg) : ProgKeepOn X M base W s s' :=
  ⟨fun r hr => h.gpr r fun h' => hr (List.mem_append_left _ h'), h.rd, h.wr, h.sp, h.mem⟩

theorem ProgKeepOn.mono {X : List Reg} {M : Mod} {base : Addr} {W W' : List Nat} {s s' : State}
    (h : ProgKeepOn X M base W s s') (hW : ∀ w ∈ W, w ∈ W') : ProgKeepOn X M base W' s s' :=
  ⟨h.gpr, h.rd, h.wr, h.sp, fun x hx ht => h.mem x (fun w hw => hx w (hW w hw)) ht⟩

theorem ProgKeepOn.keepRegs {X : List Reg} {M : Mod} {base : Addr} {W : List Nat} {s s' : State}
    (h : ProgKeepOn X M base W s s') : KeepRegs (clob M.n ++ X) s s' := ⟨h.gpr, h.rd, h.wr, h.sp⟩

theorem ProgKeepOn.unch {X : List Reg} {M : Mod} {base : Addr} {W : List Nat} {s s' : State}
    (h : ProgKeepOn X M base W s s') :
    Unch base (W.map (·, 8 * M.n) ++ [(M.tmp, 8 * M.n)]) s.mem s'.mem :=
  fun x hx => h.mem x (fun _ hw => hx _ (List.mem_append_left _ (List.mem_map_of_mem hw)))
    (hx _ (List.mem_append_right _ (List.mem_singleton_self _)))

/-- A field compiler's exact values, bounds and memory frame for one modulus
`M` and the field of `C`, changing the registers `X` besides `clob`. -/
def FieldCompilerOn (M : Mod) (C : Curve) (X : List Reg) (arithmetic : Mod → List FOp → Prog isa)
    (size : Nat) : Prop :=
  ∀ (base : Addr) (Sl : Nat → Prop),
    Lay M size Sl → Aligned M Sl → UnitMod C.p (2^(64*M.n)) →
    ∀ (ops : List FOp) (V : List Nat) (E : Nat → Fe C) (s : State),
    Inv M base size C.p Sl V E s →
    (∀ op∈ops,∀ x∈op.out::op.ins,Sl x) → (∀ op∈ops, Low M (op.out::op.ins)) → readsOk ops V=true →
    WP isa (arithmetic M ops) s fun t => ProgKeepOn X M base (ops.map FOp.out) s t ∧
      Inv M base size C.p Sl (validAfter ops V) (runOps ops E) t

theorem FieldCompilerCorrect.on {arithmetic : Mod → List FOp → Prog isa} {size : Nat}
    (hc : FieldCompilerCorrect arithmetic size) (M : Mod) (C : Curve) : FieldCompilerOn M C [] arithmetic size :=
  fun base Sl hL hAl hm ops V E s hI hS hLo hV =>
    WP.mono (hc M base C.p Sl hL hAl hm ops V E s hI hS hLo hV) fun _ ⟨k, I⟩ => ⟨k.on [], I⟩

/-- The mixed Jacobian addition (`maddJ`) computes `maddJF`, for a compiler for `M` and `C`. -/
theorem FieldCompilerOn.maddJ_values_ok {arithmetic : Mod → List FOp → Prog isa}
    {size : Nat} {M : Mod} {C : Curve} {X : List Reg} (hc : FieldCompilerOn M C X arithmetic size)
    {base : Addr} {Sl : Nat → Prop} (hL : Lay M size Sl) (hAl : Aligned M Sl)
    (hm : UnitMod C.p (2^(64*M.n))) {S : RcbSlots} {p q o : Pt}
    (hA : RcbApart S p q o) (hSl : ∀ x∈rcbW S o++rcbR S p q,Sl x) (hLow : Low M (rcbW S o++rcbR S p q))
    {V : List Nat} {E : Nat → Fe C} {s : State} (hI : Inv M base size C.p Sl V E s)
    (hV : ∀ x∈rcbR S p q,x∈V) :
    WP isa (arithmetic M (maddJ S p q o)) s fun t =>
      ProgKeepOn X M base (rcbW S o) s t ∧
      Inv M base size C.p Sl ([o.x,o.y,o.z]++V) (runOps (maddJ S p q o) E) t ∧
      (runOps (maddJ S p q o) E o.x,runOps (maddJ S p q o) E o.y,
        runOps (maddJ S p q o) E o.z)=maddJF (E p.x) (E p.y) (E p.z) (E q.x) (E q.y) := by
  rw [maddJ_eq]
  refine WP.mono (hc base Sl hL hAl hm _ V E s hI
    (fun op hop x hx => hSl x (ofN_slots op hop x hx)) (fun op hop => hLow.mono (ofN_slots op hop))
    (readsOk_mono (ofN_readsOk maddJN_ok S p q o) hV)) fun t ⟨hk,hi⟩ => ⟨hk.mono ?_,hi.sub ?_,?_⟩
  · intro w hw
    obtain ⟨op,hop,rfl⟩ := List.mem_map.mp hw
    exact ofN_out maddJN_ok op hop
  · intro x hx
    rw [mem_validAfter]
    rcases List.mem_append.mp hx with hx | hx
    · exact Or.inr (ofN_out_mem maddJN_ok hx)
    · exact Or.inl hx
  · exact (congrArg₂ Prod.mk (ofN_run maddJN_ok hA E 6)
      (congrArg₂ Prod.mk (ofN_run maddJN_ok hA E 7) (ofN_run maddJN_ok hA E 8))).trans (maddJN_run _)

end VG.Proof.Weierstrass.AArch64
