module

public import VerifiedGarbage.Impl.Ecdsa.P384.RISCV64Window
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.MulFn
public import VerifiedGarbage.Proof.Weierstrass.Jac
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.WindowA
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.Joint.Table
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.WindowAll

/-!
# `vg_p384_mul` by four-bit windows on RISC-V: the body

The curve's kit for `Proof/Ecdsa/RISCV64/WindowAll.lean`, and what that proof
gives of `vg_p384_mul`'s body: `WindowA.Cfg.body p384w dblJ` leaves in `R` a
representative of `[k]Q` (`body_ok`), for `k` at `K`'s slot and `Q` affine in
`R`'s first two. What stays here is what the kit takes of the curve: the
steps of `R = 16 R` on the field's programs (`toJStep_ok`, the doubling's
`dblStep_ok`, `fromJStep_ok`), and the statements other modules use
(`copyPt_ok`, `WPre`, `body_ok`).
-/

@[expose] public section

-- `p`, below `2^384`, is evaluated.
set_option exponentiation.threshold 1024

namespace VG.Proof.Ecdsa.RISCV64.P384.Window

open VG VG.RISCV64 VG.RISCV64.Steps VG.Proof.Mont VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdsa.RISCV64.WindowA
open VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdh.RISCV64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Proof.Ecdsa.RISCV64.P384 (W field_ok unit)
open VG.Proof.Ecdsa.RISCV64.WindowA
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Spec.Weierstrass (Point Fe mul onCurve)
open VG.Impl.Ecdsa.RISCV64.Window (windows)

/-- The curve as the code has it. -/
abbrev c : Cfg := p384w

/-! ## The complete additions -/

/-- P-384's `a` is `-3`, as the doublings need. -/
theorem am3 : AM3 W := by unfold AM3; decide

/-- A point in the slots `p`: its coordinates below `p`, representing `P`. -/
structure PtOk (base : Addr) (s : State) (p : Pt) (P : Point W) : Prop where
  rep : Rep W (tmv W 6 base s p.x) (tmv W 6 base s p.y) (tmv W 6 base s p.z) P
  x : wordsVal s.mem base p.x 6 < W.p
  y : wordsVal s.mem base p.y 6 < W.p
  z : wordsVal s.mem base p.z 6 < W.p

/-- The slots of the windows' additions. -/
abbrev jSl : List Nat :=
  [p384w.sl AP, p384w.sl B3P, p384w.sl T0, p384w.sl T1, p384w.sl T2, p384w.sl T3, p384w.sl T4, p384w.sl T5,
    p384w.sl RX, p384w.sl RY, p384w.sl RZ, p384w.sl DX, p384w.sl DY, p384w.sl DZ, p384w.sl TX, p384w.sl TY, p384w.sl TZ,
    p384w.sl ONEP, p384w.sl p384w.EX, p384w.sl p384w.EY, p384w.sl p384w.EZ]

theorem jLay : Lay p384w.MP' (own 6) (· ∈ jSl) :=
  ⟨by decide, fun x y hx hy => (by decide : ∀ x ∈ jSl, ∀ y ∈ jSl, x ≠ y → x + 8 * 6 ≤ y ∨ y + 8 * 6 ≤ x)
    x hx y hy, by decide, by decide⟩

theorem jShort : Short (· ∈ jSl) := by decide

/-- What the additions write. -/
abbrev addW (o : Pt) : List (Nat × Nat) :=
  (rcbW (Cfg.rcbSlots p384w) o).map (fun w => (w, 8 * 6)) ++ [(own 6, 64 * 6)]


/-- `o = p + q` by the complete addition, for points in slots of `jSl`. -/
theorem addPt_ok (hL : Law W) {base : Addr} {s : State} (hw : WsReg s base)
    (hap : wordsVal s.mem base (p384w.sl AP) 6 = W.a * 2 ^ 384 % W.p)
    (hbp : wordsVal s.mem base (p384w.sl B3P) 6 = 3 * W.b * 2 ^ 384 % W.p)
    {p q o : Pt} (hA : RcbApart (Cfg.rcbSlots p384w) p q o)
    (hsl : ∀ x ∈ rcbW (Cfg.rcbSlots p384w) o ++ rcbR (Cfg.rcbSlots p384w) p q, x ∈ jSl)
    {P P' : Point W} (hP : onCurve W P = true) (hP' : onCurve W P' = true)
    (hp : PtOk base s p P) (hq : PtOk base s q P') :
    WP isa (Verify.Cfg.addPt p384w p q o) s fun s' =>
      Kp s s' ∧ Unch base (addW o) s.mem s'.mem ∧ PtOk base s' o (Spec.Weierstrass.add P P') := by
  obtain hp0 : 0 < W.p := by decide
  rw [Verify.Cfg.addPt_gen _ rfl]
  obtain hI : Inv 6 base W.p (· ∈ jSl) (rcbR (Cfg.rcbSlots p384w) p q)
      (fun x => toM W.p (2 ^ (64 * 6)) (wordsVal s.mem base x 6)) s := by
    refine ⟨hw, fun x hx => hsl x (List.mem_append_right _ hx), fun x hx => ?_, fun x _ => rfl⟩
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · show wordsVal _ _ (p384w.sl AP) 6 < _; rw [hap]; exact Nat.mod_lt _ hp0
    · show wordsVal _ _ (p384w.sl B3P) 6 < _; rw [hbp]; exact Nat.mod_lt _ hp0
    exacts [hp.x, hp.y, hp.z, hq.x, hq.y, hq.z]
  refine WP.mono (rcb_ok (F := p384Field) field_ok rfl jLay jShort unit hA hsl hI (fun x hx => hx))
    fun s₁ ⟨k₁, I₁, t₁⟩ => ?_
  obtain ea : toM W.p (2 ^ (64 * 6)) (wordsVal s.mem base (p384w.sl AP) 6) = Fin.ofNat W.p W.a := by
    rw [hap, toM_mont unit]
  obtain eb : toM W.p (2 ^ (64 * 6)) (wordsVal s.mem base (p384w.sl B3P) 6) = Fin.ofNat W.p (3 * W.b) := by
    rw [hbp, toM_mont unit]
  generalize hE : (fun x => toM W.p (2 ^ (64 * 6)) (wordsVal s.mem base x 6)) = E at I₁ t₁
  obtain hrep := Rep.add hL hP hP' hp.rep hq.rep (X3 := runOps (rcb (Cfg.rcbSlots p384w) p q o) E o.x)
    (Y3 := runOps (rcb (Cfg.rcbSlots p384w) p q o) E o.y) (Z3 := runOps (rcb (Cfg.rcbSlots p384w) p q o) E o.z)
    (by
      subst hE
      show rcbAdd (Fin.ofNat W.p W.a) (Fin.ofNat W.p (3 * W.b)) _ _ _ _ _ _ = _
      rw [← ea, ← eb]
      exact t₁.1.symm)
  obtain hm : ∀ x ∈ [o.x, o.y, o.z], x ∈ rcbW (Cfg.rcbSlots p384w) o ++ rcbR (Cfg.rcbSlots p384w) p q :=
    fun x hx => List.mem_append_left _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp [rcbW])
  refine ⟨k₁.kp, k₁.mem, ⟨?_, I₁.lt _ (hm _ (by simp)), I₁.lt _ (hm _ (by simp)), I₁.lt _ (hm _ (by simp))⟩⟩
  obtain vx : tmv W 6 base s₁ o.x = _ := I₁.val _ (hm _ (by simp))
  obtain vy : tmv W 6 base s₁ o.y = _ := I₁.val _ (hm _ (by simp))
  obtain vz : tmv W 6 base s₁ o.z = _ := I₁.val _ (hm _ (by simp))
  rw [vx, vy, vz]
  exact hrep


/-! ## The slots -/

/-- The slots of `R = 16 R`'s arithmetic. -/
abbrev wSl : List Nat :=
  [c.sl AP, c.sl B3P, c.sl ZERO, c.sl T0, c.sl T1, c.sl T2, c.sl T3, c.sl T4, c.sl T5,
    c.sl RX, c.sl RY, c.sl RZ, c.sl DX, c.sl DY, c.sl DZ, c.sl TX, c.sl TY, c.sl TZ]

theorem wLay : Lay c.MP' (own 6) (· ∈ wSl) :=
  ⟨by decide, fun x y hx hy => (by decide : ∀ x ∈ wSl, ∀ y ∈ wSl, x ≠ y → x + 8 * 6 ≤ y ∨ y + 8 * 6 ≤ x)
    x hx y hy, by decide, by decide⟩

theorem wShort : Short (· ∈ wSl) := by decide

/-- The slots the windows' complete additions and Jacobian doublings use. -/
abbrev S : RcbSlots := Cfg.rcbSlots c

/-- The constants the windows read. -/
structure KC (base : Addr) (s : State) : Prop where
  ap : wordsVal s.mem base (c.sl AP) 6 = W.a * 2 ^ 384 % W.p
  bp : wordsVal s.mem base (c.sl B3P) 6 = 3 * W.b * 2 ^ 384 % W.p
  zero : wordsVal s.mem base (c.sl ZERO) 6 = 0
  onep : wordsVal s.mem base (c.sl ONEP) 6 = 2 ^ 384 % W.p

/-! ## `R = 16 R`: its steps -/

theorem toJ_apart : RcbApart S (c.pt RX RY RZ) (Cfg.zeroPt c) (c.pt DX DY DZ) := ⟨by decide, by decide⟩
theorem fromJ_apart : RcbApart S (c.pt DX DY DZ) (Cfg.zeroPt c) (c.pt RX RY RZ) := ⟨by decide, by decide⟩

/-- A Jacobian doubling from `p` to `o` (`D` to `T` or back), on `InvJ`,
with `a` at `AP`. -/
theorem dblStep_ok (hL : Law W) {base : Addr} {s : State} {p o : Pt} (hA : RcbApart S p p o)
    (hsl : ∀ x ∈ rcbW S o ++ rcbR S p p, x ∈ wSl) {V : List Nat} {E : Nat → Fe W}
    (hI : Inv 6 base W.p (· ∈ wSl) V E s) (hV : ∀ x ∈ rcbR S p p, x ∈ V)
    (_ha : E (c.sl AP) = Fin.ofNat W.p W.a) {P : Point W}
    (hP : onCurve W P = true) (hJ : InvJ W (E p.x) (E p.y) (E p.z) P) :
    WP isa (fprog p384Field (dblJ S p o)) s fun s' => KeepR 6 base (rcbW S o) s s' ∧
      ∃ E', Inv 6 base W.p (· ∈ wSl) ([o.x, o.y, o.z] ++ V) E' s' ∧ InvJ W (E' o.x) (E' o.y) (E' o.z) (d2 P) ∧
        ∀ x, x ∉ rcbW S o → E' x = E x := by
  rw [dblJ_eq]
  refine WP.mono (ofN_ok (F := p384Field) field_ok rfl wLay wShort unit dblJN_ok hA hsl hI hV)
    fun s' ⟨k, I, v, kp⟩ => ⟨k, _, I, InvJ.dbl' hL am3 hP hJ (v.trans (dblJN_run _)), kp⟩

/-- `R` into Jacobian coordinates in `D`. -/
theorem toJStep_ok (hL : Law W) {base : Addr} {s : State} {V : List Nat} {E : Nat → Fe W}
    (hI : Inv 6 base W.p (· ∈ wSl) V E s) (hV : ∀ x ∈ rcbR S (c.pt RX RY RZ) (Cfg.zeroPt c), x ∈ V) {P : Point W}
    (hR : Rep W (E (c.sl RX)) (E (c.sl RY)) (E (c.sl RZ)) P) (hz : E (c.sl ZERO) = 0) :
    WP isa (fprog p384Field (toJ S (c.pt RX RY RZ) (Cfg.zeroPt c) (c.pt DX DY DZ))) s fun s' =>
      KeepR 6 base (rcbW S (c.pt DX DY DZ)) s s' ∧
      ∃ E', Inv 6 base W.p (· ∈ wSl) ([c.sl DX, c.sl DY, c.sl DZ] ++ V) E' s' ∧
        InvJ W (E' (c.sl DX)) (E' (c.sl DY)) (E' (c.sl DZ)) P ∧
        ∀ x, x ∉ rcbW S (c.pt DX DY DZ) → E' x = E x := by
  rw [toJ_eq]
  refine WP.mono (ofN_ok (F := p384Field) field_ok rfl wLay wShort unit toJN_ok toJ_apart (by decide) hI hV)
    fun s' ⟨k, I, v, kp⟩ => ⟨k, _, I, InvJ.of_toJ hL hR hz (v.trans (toJN_run _)), kp⟩

/-- `D` back in projective coordinates in `R`. -/
theorem fromJStep_ok {base : Addr} {s : State} {V : List Nat} {E : Nat → Fe W}
    (hI : Inv 6 base W.p (· ∈ wSl) V E s) (hV : ∀ x ∈ rcbR S (c.pt DX DY DZ) (Cfg.zeroPt c), x ∈ V) :
    WP isa (fprog p384Field (fromJ S (c.pt DX DY DZ) (Cfg.zeroPt c) (c.pt RX RY RZ))) s fun s' =>
      KeepR 6 base (rcbW S (c.pt RX RY RZ)) s s' ∧
      ∃ E', Inv 6 base W.p (· ∈ wSl) ([c.sl RX, c.sl RY, c.sl RZ] ++ V) E' s' ∧
        (E' (c.sl RX), E' (c.sl RY), E' (c.sl RZ)) =
          (E (c.sl DX) * E (c.sl DZ), E (c.sl DY) + E (c.sl ZERO),
            E (c.sl DZ) * E (c.sl DZ) * E (c.sl DZ)) ∧
        ∀ x, x ∉ rcbW S (c.pt RX RY RZ) → E' x = E x := by
  rw [fromJ_eq]
  refine WP.mono (ofN_ok (F := p384Field) field_ok rfl wLay wShort unit fromJN_ok fromJ_apart (by decide) hI hV)
    fun s' ⟨k, I, v, kp⟩ => ⟨k, _, I, v.trans (fromJN_run _), kp⟩

/-! ## The kit -/

/-- The curve's kit. -/
def kit : WindowAll.Kit where
  c := c
  jSl := jSl
  l1 := 4095
  n1 := by decide
  n8 := by decide
  jt8 := by decide
  jt_lo := by decide
  jt_top := by decide
  jt_hi := by decide
  tab_own := by decide
  l1_lo := by decide
  l1_hi := by decide
  l1_jt := by decide
  ve := rfl
  jSl_adds := by decide
  jSl_step := by decide
  p0 := by decide
  unit := unit
  dbl := Impl.Weierstrass.dblJ
  dblStep_ok := dblStep_ok
  toJStep_ok := toJStep_ok
  fromJStep_ok := fromJStep_ok
  addPt_ok := fun hL => fun hw hap hbp => fun hA hsl => fun hP hP' hp hq =>
    WP.mono (addPt_ok hL hw hap hbp hA hsl hP hP' ⟨hp.rep, hp.x, hp.y, hp.z⟩ ⟨hq.rep, hq.x, hq.y, hq.z⟩)
      fun _ ⟨k, u, p⟩ => ⟨k, u, ⟨p.rep, p.x, p.y, p.z⟩⟩

/-! ## What other modules use -/

/-- `o = p`, the three coordinates one after the other, for `o`'s slots in
order and `p`'s apart from them all. -/
theorem copyPt_ok {s : State} {base : Addr} (hw : WsReg s base) {o p : Pt}
    (h8 : ∀ x ∈ [o.x, o.y, o.z, p.x, p.y, p.z], x % 8 = 0 ∧ x + 48 ≤ 4096)
    (hxy : o.x + 48 ≤ o.y) (hyz : o.y + 48 ≤ o.z)
    (hp : ∀ a ∈ [p.x, p.y, p.z], a + 48 ≤ o.x ∨ o.z + 48 ≤ a) :
    WP isa (.block (Cfg.copyPt c o p)) s fun s' =>
      wordsVal s'.mem base o.x 6 = wordsVal s.mem base p.x 6 ∧ wordsVal s'.mem base o.y 6 = wordsVal s.mem base p.y 6 ∧
      wordsVal s'.mem base o.z 6 = wordsVal s.mem base p.z 6 ∧ Rest [.t0] s s' ∧
      Unch base [(o.x, 48), (o.y, 48), (o.z, 48)] s.mem s'.mem :=
  kit.copyPt_ok hw h8 hxy hyz hp

/-- `Q`, the affine point of `R`'s first two slots. -/
abbrev qOf (base : Addr) (s : State) : Point W := .affine (tmv W 6 base s (c.sl RX)) (tmv W 6 base s (c.sl RY))

/-- What `vg_p384_mul`'s body reads at the start. -/
structure WPre (base : Addr) (s : State) : Prop where
  ws : WsReg s base
  kc : KC base s
  x : wordsVal s.mem base (c.sl RX) 6 < W.p
  y : wordsVal s.mem base (c.sl RY) 6 < W.p
  on : onCurve W (qOf base s) = true

/-- What the body writes. -/
abbrev bodyW : List (Nat × Nat) := [(736, 720), (2848, 144), (4096, 2304), (3712, 384)]

/-- `R = [k]Q`, for `k` at `K`'s slot and `Q` affine in `R`'s first two. -/
theorem body_ok (hL : Law W) {base : Addr} {s : State} (hp : WPre base s) :
    WP isa (Cfg.body c Impl.Weierstrass.dblJ) s fun s' => Kc s s' ∧ Unch base bodyW s.mem s'.mem ∧
      PtOk base s' (c.pt RX RY RZ) (mul (wordsVal s.mem base (c.sl K) 6) (qOf base s)) :=
  WP.mono (kit.body_ok hL ⟨hp.ws, ⟨hp.kc.ap, hp.kc.bp, hp.kc.zero, hp.kc.onep⟩, hp.x, hp.y, hp.on⟩)
    fun _ ⟨k, u, p⟩ => ⟨k, u, ⟨p.rep, p.x, p.y, p.z⟩⟩

end VG.Proof.Ecdsa.RISCV64.P384.Window
