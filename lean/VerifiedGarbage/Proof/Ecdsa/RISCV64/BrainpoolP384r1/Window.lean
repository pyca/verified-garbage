module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64.WindowA
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP384r1.Joint
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.WindowA
public import VerifiedGarbage.Proof.Weierstrass.JacDblA
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.WindowAll

/-!
# `vg_brainpoolp384r1_mul` by four-bit windows on RISC-V: the body

The curve's kit for `Proof/Ecdsa/RISCV64/WindowAll.lean`, and what that proof
gives of `vg_brainpoolp384r1_mul`'s body: `WindowA.Cfg.body brainpoolp384r1 dblJa` leaves in `R` a
representative of `[k]Q` (`body_ok`), for `k` at `K`'s slot and `Q` affine in
`R`'s first two. What stays here is what the kit takes of the curve: the
steps of `R = 16 R` on the field's programs (`toJStep_ok`, the doubling's
`dblStep_ok`, `fromJStep_ok`), and the statements other modules use
(`copyPt_ok`, `WPre`, `body_ok`).
-/

@[expose] public section

-- `p`, below `2^384`, is evaluated.
set_option exponentiation.threshold 512

namespace VG.Proof.Ecdsa.RISCV64.BrainpoolP384r1.Window

open VG VG.RISCV64 VG.RISCV64.Steps VG.Proof.Mont VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdsa.RISCV64.WindowA
open VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdh.RISCV64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Proof.Ecdsa.RISCV64.BrainpoolP384r1 (W field_ok unit)
open VG.Proof.Ecdsa.RISCV64.BrainpoolP384r1.Joint (PtOk addPt_ok addW keepU jSl)
open VG.Proof.Ecdsa.RISCV64.WindowA
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Spec.Weierstrass (Point Fe mul onCurve)
open VG.Impl.Ecdsa.RISCV64.Window (windows)

/-- The curve as the code has it. -/
abbrev c : Cfg := brainpoolp384r1

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

/-- What the field operations of `R = 16 R` write: `R`, `D`, `T`, the
temporaries and the functions' own working space. -/
abbrev quadW : List (Nat × Nat) := [(736, 720), (3712, 384)]

/-- The slots they write. -/
abbrev quadWl : List Nat :=
  [c.sl T0, c.sl T1, c.sl T2, c.sl T3, c.sl T4, c.sl T5, c.sl RX, c.sl RY, c.sl RZ,
    c.sl DX, c.sl DY, c.sl DZ, c.sl TX, c.sl TY, c.sl TZ]

/-- The constants the windows read. -/
structure KC (base : Addr) (s : State) : Prop where
  ap : wordsVal s.mem base (c.sl AP) 6 = W.a * 2 ^ 384 % W.p
  bp : wordsVal s.mem base (c.sl B3P) 6 = 3 * W.b * 2 ^ 384 % W.p
  zero : wordsVal s.mem base (c.sl ZERO) 6 = 0
  onep : wordsVal s.mem base (c.sl ONEP) 6 = 2 ^ 384 % W.p

/-! ## `R = 16 R`: its steps -/

theorem dbl_apart_DT : RcbApart S (c.pt DX DY DZ) (c.pt DX DY DZ) (c.pt TX TY TZ) := ⟨by decide, by decide⟩
theorem dbl_apart_TD : RcbApart S (c.pt TX TY TZ) (c.pt TX TY TZ) (c.pt DX DY DZ) := ⟨by decide, by decide⟩
theorem toJ_apart : RcbApart S (c.pt RX RY RZ) (Cfg.zeroPt c) (c.pt DX DY DZ) := ⟨by decide, by decide⟩
theorem fromJ_apart : RcbApart S (c.pt DX DY DZ) (Cfg.zeroPt c) (c.pt RX RY RZ) := ⟨by decide, by decide⟩

/-- A Jacobian doubling from `p` to `o` (`D` to `T` or back), on `InvJ`,
with `a` at `AP`. -/
theorem dblStep_ok (hL : Law W) {base : Addr} {s : State} {p o : Pt} (hA : RcbApart S p p o)
    (hsl : ∀ x ∈ rcbW S o ++ rcbR S p p, x ∈ wSl) {V : List Nat} {E : Nat → Fe W}
    (hI : Inv 6 base W.p (· ∈ wSl) V E s) (hV : ∀ x ∈ rcbR S p p, x ∈ V)
    (ha : E (c.sl AP) = Fin.ofNat W.p W.a) {P : Point W}
    (hP : onCurve W P = true) (hJ : InvJ W (E p.x) (E p.y) (E p.z) P) :
    WP isa (fprog brainpoolp384r1Field (dblJa S p o)) s fun s' => KeepR 6 base (rcbW S o) s s' ∧
      ∃ E', Inv 6 base W.p (· ∈ wSl) ([o.x, o.y, o.z] ++ V) E' s' ∧ InvJ W (E' o.x) (E' o.y) (E' o.z) (d2 P) ∧
        ∀ x, x ∉ rcbW S o → E' x = E x := by
  rw [dblJa_eq]
  refine WP.mono (ofN_ok (F := brainpoolp384r1Field) field_ok rfl wLay wShort unit dblJaN_ok hA hsl hI hV)
    fun s' ⟨k, I, v, kp⟩ => ⟨k, _, I, InvJ.dblA' hL hP hJ ha (v.trans (dblJaN_run _)), kp⟩

/-- `R` into Jacobian coordinates in `D`. -/
theorem toJStep_ok (hL : Law W) {base : Addr} {s : State} {V : List Nat} {E : Nat → Fe W}
    (hI : Inv 6 base W.p (· ∈ wSl) V E s) (hV : ∀ x ∈ rcbR S (c.pt RX RY RZ) (Cfg.zeroPt c), x ∈ V) {P : Point W}
    (hR : Rep W (E (c.sl RX)) (E (c.sl RY)) (E (c.sl RZ)) P) (hz : E (c.sl ZERO) = 0) :
    WP isa (fprog brainpoolp384r1Field (toJ S (c.pt RX RY RZ) (Cfg.zeroPt c) (c.pt DX DY DZ))) s fun s' =>
      KeepR 6 base (rcbW S (c.pt DX DY DZ)) s s' ∧
      ∃ E', Inv 6 base W.p (· ∈ wSl) ([c.sl DX, c.sl DY, c.sl DZ] ++ V) E' s' ∧
        InvJ W (E' (c.sl DX)) (E' (c.sl DY)) (E' (c.sl DZ)) P ∧
        ∀ x, x ∉ rcbW S (c.pt DX DY DZ) → E' x = E x := by
  rw [toJ_eq]
  refine WP.mono (ofN_ok (F := brainpoolp384r1Field) field_ok rfl wLay wShort unit toJN_ok toJ_apart (by decide) hI hV)
    fun s' ⟨k, I, v, kp⟩ => ⟨k, _, I, InvJ.of_toJ hL hR hz (v.trans (toJN_run _)), kp⟩

/-- `D` back in projective coordinates in `R`. -/
theorem fromJStep_ok {base : Addr} {s : State} {V : List Nat} {E : Nat → Fe W}
    (hI : Inv 6 base W.p (· ∈ wSl) V E s) (hV : ∀ x ∈ rcbR S (c.pt DX DY DZ) (Cfg.zeroPt c), x ∈ V) :
    WP isa (fprog brainpoolp384r1Field (fromJ S (c.pt DX DY DZ) (Cfg.zeroPt c) (c.pt RX RY RZ))) s fun s' =>
      KeepR 6 base (rcbW S (c.pt RX RY RZ)) s s' ∧
      ∃ E', Inv 6 base W.p (· ∈ wSl) ([c.sl RX, c.sl RY, c.sl RZ] ++ V) E' s' ∧
        (E' (c.sl RX), E' (c.sl RY), E' (c.sl RZ)) =
          (E (c.sl DX) * E (c.sl DZ), E (c.sl DY) + E (c.sl ZERO),
            E (c.sl DZ) * E (c.sl DZ) * E (c.sl DZ)) ∧
        ∀ x, x ∉ rcbW S (c.pt RX RY RZ) → E' x = E x := by
  rw [fromJ_eq]
  refine WP.mono (ofN_ok (F := brainpoolp384r1Field) field_ok rfl wLay wShort unit fromJN_ok fromJ_apart (by decide) hI hV)
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
  dbl := dblJa
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

/-- What `vg_brainpoolp384r1_mul`'s body reads at the start. -/
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
    WP isa (Cfg.body c dblJa) s fun s' => Kc s s' ∧ Unch base bodyW s.mem s'.mem ∧
      PtOk base s' (c.pt RX RY RZ) (mul (wordsVal s.mem base (c.sl K) 6) (qOf base s)) :=
  WP.mono (kit.body_ok hL ⟨hp.ws, ⟨hp.kc.ap, hp.kc.bp, hp.kc.zero, hp.kc.onep⟩, hp.x, hp.y, hp.on⟩)
    fun _ ⟨k, u, p⟩ => ⟨k, u, ⟨p.rep, p.x, p.y, p.z⟩⟩

end VG.Proof.Ecdsa.RISCV64.BrainpoolP384r1.Window
