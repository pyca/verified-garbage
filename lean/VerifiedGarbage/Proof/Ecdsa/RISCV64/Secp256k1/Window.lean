module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64.WindowA
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.Secp256k1.Joint
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.WindowA
public import VerifiedGarbage.Proof.Weierstrass.JacDbl0
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.WindowAll

/-!
# `vg_secp256k1_mul` by four-bit windows on RISC-V: the body

The curve's kit for `Proof/Ecdsa/RISCV64/WindowAll.lean`, and what that proof
gives of `vg_secp256k1_mul`'s body: `WindowA.Cfg.body secp256k1 dblJ0` leaves in `R` a
representative of `[k]Q` (`body_ok`), for `k` at `K`'s slot and `Q` affine in
`R`'s first two. What stays here is what the kit takes of the curve: the
steps of `R = 16 R` on the field's programs (`toJStep_ok`, the doubling's
`dblStep_ok`, `fromJStep_ok`), and the statements other modules use
(`copyPt_ok`, `WPre`, `body_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.Secp256k1.Window

open VG VG.RISCV64 VG.RISCV64.Steps VG.Proof.Mont VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdsa.RISCV64.WindowA
open VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdh.RISCV64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Proof.Ecdsa.RISCV64.Secp256k1 (W field_ok unit)
open VG.Proof.Ecdsa.RISCV64.Secp256k1.Joint (PtOk addPt_ok addW keepU jSl)
open VG.Proof.Ecdsa.RISCV64.WindowA
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Spec.Weierstrass (Point Fe mul onCurve)
open VG.Impl.Ecdsa.RISCV64.Window (windows)

/-- The curve as the code has it. -/
abbrev c : Cfg := secp256k1

/-! ## The slots -/

/-- The slots of `R = 16 R`'s arithmetic. -/
abbrev wSl : List Nat :=
  [c.sl AP, c.sl B3P, c.sl ZERO, c.sl T0, c.sl T1, c.sl T2, c.sl T3, c.sl T4, c.sl T5,
    c.sl RX, c.sl RY, c.sl RZ, c.sl DX, c.sl DY, c.sl DZ, c.sl TX, c.sl TY, c.sl TZ]

theorem wLay : Lay c.MP' (own 4) (· ∈ wSl) :=
  ⟨by decide, fun x y hx hy => (by decide : ∀ x ∈ wSl, ∀ y ∈ wSl, x ≠ y → x + 8 * 4 ≤ y ∨ y + 8 * 4 ≤ x)
    x hx y hy, by decide, by decide⟩

theorem wShort : Short (· ∈ wSl) := by decide

/-- The slots the windows' complete additions and Jacobian doublings use. -/
abbrev S : RcbSlots := Cfg.rcbSlots c

/-- The constants the windows read. -/
structure KC (base : Addr) (s : State) : Prop where
  ap : wordsVal s.mem base (c.sl AP) 4 = W.a * 2 ^ 256 % W.p
  bp : wordsVal s.mem base (c.sl B3P) 4 = 3 * W.b * 2 ^ 256 % W.p
  zero : wordsVal s.mem base (c.sl ZERO) 4 = 0
  onep : wordsVal s.mem base (c.sl ONEP) 4 = 2 ^ 256 % W.p

/-! ## `R = 16 R`: its steps -/

theorem toJ_apart : RcbApart S (c.pt RX RY RZ) (Cfg.zeroPt c) (c.pt DX DY DZ) := ⟨by decide, by decide⟩
theorem fromJ_apart : RcbApart S (c.pt DX DY DZ) (Cfg.zeroPt c) (c.pt RX RY RZ) := ⟨by decide, by decide⟩

/-- A Jacobian doubling from `p` to `o` (`D` to `T` or back), on `InvJ`,
with `a` at `AP`. -/
theorem dblStep_ok (hL : Law W) {base : Addr} {s : State} {p o : Pt} (hA : RcbApart S p p o)
    (hsl : ∀ x ∈ rcbW S o ++ rcbR S p p, x ∈ wSl) {V : List Nat} {E : Nat → Fe W}
    (hI : Inv 4 base W.p (· ∈ wSl) V E s) (hV : ∀ x ∈ rcbR S p p, x ∈ V)
    {P : Point W}
    (hP : onCurve W P = true) (hJ : InvJ W (E p.x) (E p.y) (E p.z) P) :
    WP isa (fprog secp256k1Field (dblJ0 S p o)) s fun s' => KeepR 4 base (rcbW S o) s s' ∧
      ∃ E', Inv 4 base W.p (· ∈ wSl) ([o.x, o.y, o.z] ++ V) E' s' ∧ InvJ W (E' o.x) (E' o.y) (E' o.z) (d2 P) ∧
        ∀ x, x ∉ rcbW S o → E' x = E x := by
  rw [dblJ0_eq]
  refine WP.mono (ofN_ok (F := secp256k1Field) field_ok rfl wLay wShort unit dblJ0N_ok hA hsl hI hV)
    fun s' ⟨k, I, v, kp⟩ => ⟨k, _, I, ?_, kp⟩
  obtain h := v.trans (dblJ0N_run _)
  simp only [Prod.ext_iff] at h
  obtain ⟨ex, ey, ez⟩ := h
  rw [ex, ey, ez]
  exact InvJ.dbl0 hL rfl hP hJ

/-- `R` into Jacobian coordinates in `D`. -/
theorem toJStep_ok (hL : Law W) {base : Addr} {s : State} {V : List Nat} {E : Nat → Fe W}
    (hI : Inv 4 base W.p (· ∈ wSl) V E s) (hV : ∀ x ∈ rcbR S (c.pt RX RY RZ) (Cfg.zeroPt c), x ∈ V) {P : Point W}
    (hR : Rep W (E (c.sl RX)) (E (c.sl RY)) (E (c.sl RZ)) P) (hz : E (c.sl ZERO) = 0) :
    WP isa (fprog secp256k1Field (toJ S (c.pt RX RY RZ) (Cfg.zeroPt c) (c.pt DX DY DZ))) s fun s' =>
      KeepR 4 base (rcbW S (c.pt DX DY DZ)) s s' ∧
      ∃ E', Inv 4 base W.p (· ∈ wSl) ([c.sl DX, c.sl DY, c.sl DZ] ++ V) E' s' ∧
        InvJ W (E' (c.sl DX)) (E' (c.sl DY)) (E' (c.sl DZ)) P ∧
        ∀ x, x ∉ rcbW S (c.pt DX DY DZ) → E' x = E x := by
  rw [toJ_eq]
  refine WP.mono (ofN_ok (F := secp256k1Field) field_ok rfl wLay wShort unit toJN_ok toJ_apart (by decide) hI hV)
    fun s' ⟨k, I, v, kp⟩ => ⟨k, _, I, InvJ.of_toJ hL hR hz (v.trans (toJN_run _)), kp⟩

/-- `D` back in projective coordinates in `R`. -/
theorem fromJStep_ok {base : Addr} {s : State} {V : List Nat} {E : Nat → Fe W}
    (hI : Inv 4 base W.p (· ∈ wSl) V E s) (hV : ∀ x ∈ rcbR S (c.pt DX DY DZ) (Cfg.zeroPt c), x ∈ V) :
    WP isa (fprog secp256k1Field (fromJ S (c.pt DX DY DZ) (Cfg.zeroPt c) (c.pt RX RY RZ))) s fun s' =>
      KeepR 4 base (rcbW S (c.pt RX RY RZ)) s s' ∧
      ∃ E', Inv 4 base W.p (· ∈ wSl) ([c.sl RX, c.sl RY, c.sl RZ] ++ V) E' s' ∧
        (E' (c.sl RX), E' (c.sl RY), E' (c.sl RZ)) =
          (E (c.sl DX) * E (c.sl DZ), E (c.sl DY) + E (c.sl ZERO),
            E (c.sl DZ) * E (c.sl DZ) * E (c.sl DZ)) ∧
        ∀ x, x ∉ rcbW S (c.pt RX RY RZ) → E' x = E x := by
  rw [fromJ_eq]
  refine WP.mono (ofN_ok (F := secp256k1Field) field_ok rfl wLay wShort unit fromJN_ok fromJ_apart (by decide) hI hV)
    fun s' ⟨k, I, v, kp⟩ => ⟨k, _, I, v.trans (fromJN_run _), kp⟩

/-! ## The kit -/

/-- The curve's kit. -/
def kit : WindowAll.Kit where
  c := c
  jSl := jSl
  l1 := 2048
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
  dbl := dblJ0
  dblStep_ok := fun hL => fun hA hsl => fun hI hV _ => fun hP hJ => dblStep_ok hL hA hsl hI hV hP hJ
  toJStep_ok := toJStep_ok
  fromJStep_ok := fromJStep_ok
  addPt_ok := fun hL => fun hw hap hbp => fun hA hsl => fun hP hP' hp hq =>
    WP.mono (addPt_ok hL hw hap hbp hA hsl hP hP' ⟨hp.rep, hp.x, hp.y, hp.z⟩ ⟨hq.rep, hq.x, hq.y, hq.z⟩)
      fun _ ⟨k, u, p⟩ => ⟨k, u, ⟨p.rep, p.x, p.y, p.z⟩⟩

/-! ## What other modules use -/

/-- `o = p`, the three coordinates one after the other, for `o`'s slots in
order and `p`'s apart from them all. -/
theorem copyPt_ok {s : State} {base : Addr} (hw : WsReg s base) {o p : Pt}
    (h8 : ∀ x ∈ [o.x, o.y, o.z, p.x, p.y, p.z], x % 8 = 0 ∧ x + 32 ≤ 2048)
    (hxy : o.x + 32 ≤ o.y) (hyz : o.y + 32 ≤ o.z)
    (hp : ∀ a ∈ [p.x, p.y, p.z], a + 32 ≤ o.x ∨ o.z + 32 ≤ a) :
    WP isa (.block (Cfg.copyPt c o p)) s fun s' =>
      wordsVal s'.mem base o.x 4 = wordsVal s.mem base p.x 4 ∧ wordsVal s'.mem base o.y 4 = wordsVal s.mem base p.y 4 ∧
      wordsVal s'.mem base o.z 4 = wordsVal s.mem base p.z 4 ∧ Rest [.t0] s s' ∧
      Unch base [(o.x, 32), (o.y, 32), (o.z, 32)] s.mem s'.mem :=
  kit.copyPt_ok hw h8 hxy hyz hp

/-- `Q`, the affine point of `R`'s first two slots. -/
abbrev qOf (base : Addr) (s : State) : Point W := .affine (tmv W 4 base s (c.sl RX)) (tmv W 4 base s (c.sl RY))

/-- What `vg_secp256k1_mul`'s body reads at the start. -/
structure WPre (base : Addr) (s : State) : Prop where
  ws : WsReg s base
  kc : KC base s
  x : wordsVal s.mem base (c.sl RX) 4 < W.p
  y : wordsVal s.mem base (c.sl RY) 4 < W.p
  on : onCurve W (qOf base s) = true

/-- What the body writes. -/
abbrev bodyW : List (Nat × Nat) := [(512, 480), (1920, 96), (2048, 1536), (3840, 256)]

/-- `R = [k]Q`, for `k` at `K`'s slot and `Q` affine in `R`'s first two. -/
theorem body_ok (hL : Law W) {base : Addr} {s : State} (hp : WPre base s) :
    WP isa (Cfg.body c dblJ0) s fun s' => Kc s s' ∧ Unch base bodyW s.mem s'.mem ∧
      PtOk base s' (c.pt RX RY RZ) (mul (wordsVal s.mem base (c.sl K) 4) (qOf base s)) :=
  WP.mono (kit.body_ok hL ⟨hp.ws, ⟨hp.kc.ap, hp.kc.bp, hp.kc.zero, hp.kc.onep⟩, hp.x, hp.y, hp.on⟩)
    fun _ ⟨k, u, p⟩ => ⟨k, u, ⟨p.rep, p.x, p.y, p.z⟩⟩

end VG.Proof.Ecdsa.RISCV64.Secp256k1.Window
