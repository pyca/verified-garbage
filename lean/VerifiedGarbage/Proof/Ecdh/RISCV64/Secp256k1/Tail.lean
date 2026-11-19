module

public import VerifiedGarbage.Proof.Ecdh.RISCV64.TailAll
public import VerifiedGarbage.Proof.Ecdh.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ecdsa.RISCV64.Secp256k1.MulLit
import VerifiedGarbage.Proof.Weierstrass.PointFacts
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Spec.Ecdsa.Generic
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.Secp256k1.Joint
public import VerifiedGarbage.Proof.Weierstrass.CheckPointContract
public import VerifiedGarbage.Impl.Ecdh.Secp256k1.RISCV64
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Ecdh.Exchange
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Secp256k1.Point
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.Secp256k1.Joint
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Weierstrass.PointFacts
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.Secp256k1.MulLit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.WindowA
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.WindowA
public import VerifiedGarbage.Proof.Weierstrass.JacDbl0
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.WindowAll
meta import VerifiedGarbage.Impl.Ecdsa.RISCV64.WindowA
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.WindowA
meta import VerifiedGarbage.Proof.Weierstrass.JacDbl0
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.WindowAll

/-! ### `Ecdsa.RISCV64.Secp256k1.MulVerified`, which this module and modules that import it used -/

section

/-! ### `Ecdsa.RISCV64.Secp256k1.Window`, which this module and modules that import it used -/

section

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

end

end

/-!
# `vg_secp256k1_mul` on RISC-V: the contract

The facts of `Impl.Weierstrass.Mul.Curve.mulInRangeContract` for secp256k1 on
RISC-V, by register (`mulRVc`: `ws` in `a0`), and `mulFn` meets them
(`mul_rv`), given the group law: the saves of `s0`, `s1` and `ra` (past the
numbered slots, in the contract's tail), the windows' `body_ok`, and the loads that
restore them. The coordinates the specification decodes are the proofs'
(`Point.dec_eq`, given Fermat's little theorem from the group law), and
`Represents` is `Rep`. What the function writes is its own working space or
the result's (`keeps_of_unch`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.Secp256k1

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Spec.Weierstrass (Curve Fe Point)

/-- secp256k1's curve of `Proof/Weierstrass/MulContract.lean`, as RISC-V's
windows use it: as P-256's (`Impl.Weierstrass.Mul.p256`), its working space
is every byte from slot 45 on too (`tail`), where the windows keep their
saves, and the result is stated for `k` in `[1, n - 1]` (`inRange`). -/
abbrev MC : Impl.Weierstrass.Mul.Curve :=
  { W := Spec.Secp256k1.curve, curve := "secp256k1", k := 4, desc := "secp256k1", tmp := 2, tail := true,
    inRange := true }

/-- `vg_secp256k1_mul(ws = a0)`. -/
def mulRVc : Contract isa where
  pre s := s.rd = [] ∧ s.wr = [⟨s.gpr .a0, 8192⟩] ∧ (s.gpr .a0).toNat + 8192 ≤ 2 ^ 64 ∧
    (s.gpr .a0).toNat % 8 = 0 ∧ MC.ConstsOk (s.gpr .a0) s.mem ∧ MC.PointOk (s.gpr .a0) s.mem
  post s s' := MC.ResultInRange (MC.scalar (s.gpr .a0) s.mem) (MC.point (s.gpr .a0) s.mem) (s.gpr .a0) s.mem s'.mem
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0

/-- `Represents` is the proofs' `Rep`. -/
theorem represents_of_rep {C : Curve} {X Y Z : Fe C} {P : Point C}
    (h : Rep C X Y Z P) : Impl.Weierstrass.MulBase.Represents X Y Z P := by
  cases P <;> exact h

/-- The coordinate at an offset below `2³²` is the number `wordsVal` reads. -/
theorem coordAt_eq (m : Mem) (ws : Addr) {o : Nat} (ho : o < 2 ^ 32) :
    MC.toPoint.coordAt m ws o = wordsVal m ws o 4 := by
  unfold Impl.Weierstrass.Point.Curve.coordAt
  rw [Impl.Weierstrass.Mont.numAt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho]
  exact read_eq_wordsVal m ws 4 o

/-- The saves, at `mulSave = 1504`. -/
abbrev saves : List (Nat × Nat) := [(1504, 8), (1512, 8), (1520, 8)]

/-- What the function writes is its own working space or the result's. -/
theorem keeps_of_unch {ws : Addr} {m m' : Mem} (hu : Unch ws (saves ++ Window.bodyW) m m') : MC.Keeps ws m m' := by
  intro i hi hown hp
  have h8 : Impl.Weierstrass.Mont.wsBytes = 8192 := rfl
  refine hu _ fun w hw => ?_
  rw [show ws + BitVec.ofNat 64 i = off ws i from rfl, ofs_off0 ws (by omega_using [hi, h8])]
  obtain hw' := (by decide : ∀ w ∈ saves ++ Window.bodyW, (512 ≤ w.1 ∧ w.1 + w.2 ≤ 1056) ∨ 1504 ≤ w.1) w hw
  simp only [Impl.Weierstrass.Mul.Curve.Own, Impl.Weierstrass.Mul.Curve.slot, Impl.Weierstrass.Mul.Curve.tmpAt,
    Impl.Weierstrass.Mul.Curve.bitsAt, Impl.Weierstrass.Mul.Curve.pAt, Impl.Weierstrass.Mul.Curve.ptBytes,
    true_and] at hown hp
  omega_using [hp, hw', hown]

/-- `vg_secp256k1_mul` meets `mulRVc`, given the group law. -/
theorem mul_rv (hL : VG.Proof.Weierstrass.Law W) (s : State) (hs : mulRVc.pre s) :
    ∃ t s', Exec isa mulSecp256k1 s t s' ∧ abiPreserved s s' ∧ mulRVc.post s s' := by
  obtain ⟨-, hwr, hfit, hal, ⟨-, hz, hone, ha, hb3⟩, ⟨hx, hy, hon⟩⟩ := hs
  generalize hb : s.gpr .a0 = base at hwr hfit hal hz hone ha hb3 hx hy hon
  obtain hwr' : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hwr]; exact List.mem_singleton_self _
  have hpR := unit
  obtain hp0 : 0 < W.p := by decide
  obtain ca : ∀ (m : Mem) {o : Nat}, o < 4096 → MC.toPoint.coordAt m base o = wordsVal m base o 4 :=
    fun m _ ho => coordAt_eq m base (by omega_using [ho])
  obtain dq : ∀ x, MC.toPoint.dec x = toM W.p (2 ^ 256) x :=
    VG.Proof.Weierstrass.Point.dec_eq MC.toPoint hL.one_ne_zero (VG.Proof.Weierstrass.Point.fermat_of_law hL) hpR
  -- The saves and `s0 = a0`.
  suffices h : WP isa mulSecp256k1 s fun s' => abiPreserved s s' ∧ mulRVc.post s s' by
    obtain ⟨t, s', he, h⟩ := h; exact ⟨t, s', he, h⟩
  rw [mulSecp256k1, WindowA.Cfg.mulFn, show secp256k1.mulSave = 1504 from rfl]
  refine WP.seq (sd_a0 hb hwr' hal (d := 1504) (by decide) (by decide) fun s₁ u₁ => ?_)
  refine sd_a0 (by rw [u₁.gpr]; exact hb) (by rw [u₁.wr]; exact hwr') hal (d := 1512) (by decide)
    (by decide) fun s₂ u₂ => ?_
  refine sd_a0 (by rw [u₂.gpr, u₁.gpr]; exact hb) (by rw [u₂.wr, u₁.wr]; exact hwr') hal (d := 1520)
    (by decide) (by decide) fun s₃ u₃ => wp_mv fun s₄ u₄ => WP.block_nil ?_
  obtain g₄ : ∀ r, r ≠ .s0 → s₄.gpr r = s.gpr r := fun r hr => by
    rw [u₄.other r hr, u₃.gpr, u₂.gpr, u₁.gpr]
  obtain hw₄ : WsReg s₄ base := ⟨by rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, hb],
    by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hwr', hfit, hal⟩
  obtain m₄ : s₄.mem = ((s.mem.writeW (off base 1504) (s.gpr .s0)).writeW (off base 1512) (s.gpr .s1)).writeW
      (off base 1520) (s.gpr .ra) := by
    simp only [u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₂.gpr, u₁.gpr]
  obtain O₄ : Unch base saves s.mem s₄.mem := by
    rw [m₄]
    exact (((writeW_outside _ _ _ (by omega_using [])).unch.trans (writeW_outside _ _ _ (by omega_using [])).unch).trans
      (writeW_outside _ _ _ (by omega_using [])).unch)
  obtain sv₄ : ∀ i, i < 45 → sv base s₄ i = sv base s i := fun i hi =>
    O₄.wordsVal (fun w hw => by
      simp only [saves, List.mem_cons, List.not_mem_nil, or_false] at hw
      have : secp256k1.sl i + 32 ≤ 1504 := by simp only [Cfg.sl, slot, secp256k1]; omega_using [hi]
      rcases hw with rfl | rfl | rfl <;> (simp only; omega_using [this])) (by simp only [Cfg.sl, slot, secp256k1]; omega_using [hi])
  obtain cs : ∀ i, i < 45 → MC.toPoint.coordAt s.mem base (secp256k1.sl i) = sv base s i := fun i hi =>
    ca s.mem (by simp only [Cfg.sl, slot, secp256k1]; omega_using [hi])
  -- The slots' values, from the contract's.
  obtain hz' : sv base s₄ ZERO = 0 := by rw [sv₄ _ (by decide)]; exact (cs ZERO (by decide)).symm.trans hz
  obtain hone' : sv base s₄ ONEP = 2 ^ 256 % W.p := by
    rw [sv₄ _ (by decide)]; refine (cs ONEP (by decide)).symm.trans (hone.trans ?_)
    simp only [Impl.Weierstrass.Mul.Curve.mont, Nat.one_mul]
  obtain ha' : sv base s₄ AP = 2 ^ 256 * W.a % W.p := by
    rw [sv₄ _ (by decide)]; refine (cs AP (by decide)).symm.trans (ha.trans ?_)
    simp only [Impl.Weierstrass.Mul.Curve.mont]; rw [Nat.mul_comm]
  obtain hb3' : sv base s₄ B3P = 2 ^ 256 * (3 * W.b) % W.p := by
    rw [sv₄ _ (by decide)]; refine (cs B3P (by decide)).symm.trans (hb3.trans ?_)
    simp only [Impl.Weierstrass.Mul.Curve.mont]; rw [Nat.mul_comm]
  obtain tm : ∀ x, toM W.p (2 ^ 256) (2 ^ 256 * x % W.p) = Fin.ofNat W.p x := fun x => by
    rw [Nat.mul_comm]; exact toM_mont hpR
  obtain qx : (MC.qCoords base s.mem).1 = sv base s₄ RX := by rw [sv₄ _ (by decide)]; exact cs RX (by decide)
  obtain qy : (MC.qCoords base s.mem).2 = sv base s₄ RY := by
    rw [sv₄ _ (by decide), ← cs RY (by decide)]; rfl
  obtain eP : MC.point base s.mem = .affine (toM W.p (2 ^ 256) (sv base s₄ RX)) (toM W.p (2 ^ 256) (sv base s₄ RY)) := by
    unfold Impl.Weierstrass.Mul.Curve.point
    rw [qx, qy, dq, dq]
  have hon' := hon
  rw [eP] at hon'
  -- The body.
  obtain hpre : Window.WPre base s₄ :=
    ⟨hw₄, ⟨show sv base s₄ AP = _ by rw [ha', Nat.mul_comm], show sv base s₄ B3P = _ by rw [hb3', Nat.mul_comm], hz',
      hone'⟩, show sv base s₄ RX < W.p from qx ▸ hx, show sv base s₄ RY < W.p from qy ▸ hy, hon'⟩
  refine WP.seq (WP.mono (Window.body_ok hL hpre) fun s₅ ⟨K₅, U₅, pR₅⟩ => ?_)
  obtain lt₅ : ∀ x ∈ [secp256k1.sl RX, secp256k1.sl RY, secp256k1.sl RZ], wordsVal s₅.mem base x 4 < W.p := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    exacts [pR₅.x, pR₅.y, pR₅.z]
  have R₅ := pR₅.rep
  -- The loads.
  obtain hw₅ := hw₄.of_kc K₅
  obtain far : ∀ d ∈ [1504, 1512, 1520], word s₅.mem base d = word s₄.mem base d := fun d hd =>
    U₅.word (fun w hw => by
      have := (by decide : ∀ w ∈ Window.bodyW, w.1 + w.2 ≤ 1504 ∨ 1528 ≤ w.1) w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      omega_using [this, hd]) (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; omega_using [hd])
  obtain w20 : word s₅.mem base 1520 = s.gpr .ra := by
    rw [far 1520 (by simp), m₄, word_writeW_self]
  obtain w12 : word s₅.mem base 1512 = s.gpr .s1 := by
    rw [far 1512 (by simp), m₄, (writeW_outside (d := 1520) _ base _ (by omega_using [])).word (by omega_using []) (by omega_using []), word_writeW_self]
  obtain w04 : word s₅.mem base 1504 = s.gpr .s0 := by
    rw [far 1504 (by simp), m₄, (writeW_outside (d := 1520) _ base _ (by omega_using [])).word (by omega_using []) (by omega_using []),
      (writeW_outside (d := 1512) _ base _ (by omega_using [])).word (by omega_using []) (by omega_using []), word_writeW_self]
  refine ld_ws hw₅ (d := 1520) (by decide) (by decide) fun s₆ u₆ => ?_
  refine ld_ws (hw₅.of_kp (Kp.of_upd u₆)) (d := 1512) (by decide) (by decide) fun s₇ u₇ => ?_
  obtain hw₇ : WsReg s₇ base := ⟨by rw [u₇.other .s0 (by decide), u₆.other .s0 (by decide)]; exact hw₅.s0,
    by rw [u₇.wr, u₆.wr]; exact hw₅.wr, hfit, hal⟩
  refine ld_ws hw₇ (d := 1504) (by decide) (by decide) fun s₈ u₈ => WP.block_nil ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · have m₇ : s₇.mem = s₅.mem := by rw [u₇.mem, u₆.mem]
    by_cases h0 : r = .s0
    · subst h0; rw [u₈.gpr, m₇, w04]
    by_cases h1 : r = .s1
    · subst h1; rw [u₈.other _ (by decide), u₇.gpr, u₆.mem, w12]
    rw [u₈.other _ h0, u₇.other _ h1, u₆.other _ (fun e => by subst e; revert hr; decide),
      K₅.gpr r hr h1, g₄ r h0]
  · rw [u₈.sp, u₇.sp, u₆.sp, K₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, w20]
  · have m₈ : s₈.mem = s₅.mem := by rw [u₈.mem, u₇.mem, u₆.mem]
    show MC.ResultInRange _ _ (s.gpr .a0) s.mem s₈.mem
    rw [hb, eP, m₈]
    refine ⟨fun _ _ => ?_, keeps_of_unch (O₄.trans U₅)⟩
    obtain e : MC.scalar base s.mem = sv base s₄ K := by rw [sv₄ _ (by decide)]; exact cs K (by decide)
    obtain c5 : ∀ i, i < 45 → MC.toPoint.coordAt s₅.mem base (secp256k1.sl i) = sv base s₅ i := fun i hi =>
      ca s₅.mem (by simp only [Cfg.sl, slot, secp256k1]; omega_using [hi])
    obtain x0 : MC.toPoint.coordAt s₅.mem base MC.pAt = sv base s₅ RX := c5 RX (by decide)
    obtain x1 : MC.toPoint.coordAt s₅.mem base (MC.pAt + Impl.Weierstrass.Point.elemBytes MC.toPoint.k) =
        sv base s₅ RY := c5 RY (by decide)
    obtain x2 : MC.toPoint.coordAt s₅.mem base (MC.pAt + 2 * Impl.Weierstrass.Point.elemBytes MC.toPoint.k) =
        sv base s₅ RZ := c5 RZ (by decide)
    rw [e]
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at lt₅
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · show _ < W.p; rw [Impl.Weierstrass.Point.Curve.pointAt, x0]; exact lt₅.1
    · show _ < W.p; rw [Impl.Weierstrass.Point.Curve.pointAt, x1]; exact lt₅.2.1
    · show _ < W.p; rw [Impl.Weierstrass.Point.Curve.pointAt, x2]; exact lt₅.2.2
    · rw [Impl.Weierstrass.Point.Curve.pointAt, x0, x1, x2, dq, dq, dq]
      exact represents_of_rep R₅

end VG.Proof.Ecdsa.RISCV64.Secp256k1

end

end

/-! ### `Ecdh.RISCV64.Secp256k1.Check`, which this module and modules that import it used -/

section

/-!
# `vg_secp256k1_check_point` on RISC-V: secp256k1's facts

The check (`Impl/Ecdh/RISCV64.lean`) is proven once for every curve in
`Proof/Ecdh/RISCV64/TailAll.lean` (`TKit.check_rv`), from what `tkit` says of
this one. Here are secp256k1's slots, and the facts about them that other proofs
name.
-/

@[expose] public section

namespace VG.Proof.Ecdh.RISCV64.Secp256k1

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64 VG.Proof.Ecdsa.RISCV64.Secp256k1
open VG.Proof.X25519.RISCV64 (Rest wp_and)
open VG.Spec.Weierstrass (Curve Fe Point)

/-- The flag's offset. -/
abbrev FL : Nat := 1472

theorem sl_FLAG : secp256k1.sl FLAG = FL := rfl

theorem sl_eq (i : Nat) : secp256k1.sl i = 64 + 32 * i := by simp only [Cfg.sl, slot, secp256k1]

/-- What the proofs shared by every curve (`TailAll.lean`) need of this one. -/
def tkit : TKit where
  c := secp256k1
  name := "secp256k1"
  cdesc := "secp256k1"
  mdesc := "secp256k1"
  n4 := by decide
  n9 := by decide
  p1 := by decide
  field_ok := field_ok
  FPk := rfl
  FPm := rfl
  unit := unit

/-- The flag `&=` the mask `a7`. -/
theorem andFlag_ok {s : State} {base : Addr} (hw : WsReg s base) :
    WP isa (.block (Cfg.andFlag secp256k1)) s fun s' =>
      word s'.mem base FL = word s.mem base FL &&& s.gpr .a7 ∧ Rest [.t0] s s' ∧ Outside base FL 8 s.mem s'.mem :=
  TKit.andFlag_ok secp256k1 (by decide) hw

/-! ## Slots and masks -/

/-- A slot apart from what changed. -/
theorem sv_unch {base : Addr} {W : List (Nat × Nat)} {m m' : Mem} (U : Unch base W m m') (i : Nat)
    (h : ∀ w ∈ W, secp256k1.sl i + 32 ≤ w.1 ∨ w.1 + w.2 ≤ secp256k1.sl i) (hi : i < 100 := by decide) :
    wordsVal m' base (secp256k1.sl i) 4 = wordsVal m base (secp256k1.sl i) 4 :=
  U.wordsVal h (by rw [sl_eq]; omega_using [hi])

theorem maskOf_and (a b : Bool) : maskOf a &&& maskOf b = maskOf (a && b) := by
  cases a <;> cases b <;> decide

/-- `toM` is injective on numbers below `m`. -/
theorem toM_inj {m R : Nat} [NeZero m] (hR : UnitMod m R) {x y : Nat} (hx : x < m) (hy : y < m)
    (h : toM m R x = toM m R y) : x = y :=
  Kit.toM_inj hR hx hy h

/-- A Montgomery multiplication by `R² mod p` gives `x R mod p`. -/
theorem mont_eq {r x : Nat} (hr : r < W.p) (h : r * 2 ^ 256 % W.p = x * (2 ^ 256 * 2 ^ 256 % W.p) % W.p) :
    r = x * 2 ^ 256 % W.p :=
  toM_inj unit hr (Nat.mod_lt _ (by decide)) ((toM_r2 unit h).trans (toM_mont unit).symm)

/-- secp256k1's check of `Proof/Weierstrass/CheckPointContract.lean`. -/
abbrev CC : Impl.Weierstrass.CheckPoint.Curve := Impl.Weierstrass.CheckPoint.secp256k1

end VG.Proof.Ecdh.RISCV64.Secp256k1

end

end

/-!
# ECDH and public keys over secp256k1 on RISC-V: the multiplication and after

What follows the point's setup in both functions (`tail`) is proven once for
every curve in `Proof/Ecdh/RISCV64/TailAll.lean` (`TKit.tail_ok`). Here is what
that proof needs of secp256k1, its chain of `p - 2` (`chainP_ok`) and its
multiplication's contract (`mulNF`, `mul_meets`), and that proof's statements
on secp256k1's slots that other proofs name.
-/

@[expose] public section

/-!
## ECDH and public keys over secp256k1 on RISC-V: the setup

The constants (`consts_ok`, by `TailAll.lean`'s), and what both functions'
setups share.
-/

namespace VG.Proof.Ecdh.RISCV64.Secp256k1

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdh.RISCV64.Cfg
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64 VG.Proof.Ecdsa.RISCV64.Secp256k1
open VG.Proof.X25519.RISCV64 (Rest)

/-- Constants to slots below 44, each its own. -/
theorem consts_ok : ∀ (L : List (Nat × Nat)) {s : State} {base : Addr}, WsReg s base → (∀ e ∈ L, e.1 < 44) →
    (L.map Prod.fst).Nodup →
    WP isa (.block (L.flatMap fun e => setConst 4 (secp256k1.sl e.1) e.2)) s fun s' =>
      Rest [.t0, .t1] s s' ∧ Unch base (L.map fun e => (secp256k1.sl e.1, 32)) s.mem s'.mem ∧
      ∀ e ∈ L, sv base s' e.1 = e.2 % 2 ^ 256 :=
  fun L _ _ hw hlt hnd =>
    TKit.consts_ok secp256k1 (by decide) L hw (fun e he => Nat.le_trans (Nat.le_of_lt (hlt e he)) (by decide)) hnd

/-- The constants, as `consts_ok` takes them. -/
theorem constCode_eq : constCode secp256k1 = (consts secp256k1).flatMap fun e => setConst 4 (secp256k1.sl e.1) e.2 := rfl

/-- The constants' slots. -/
theorem consts_slots : ∀ e ∈ consts secp256k1, e.1 < 44 := by decide

theorem consts_nodup : ((consts secp256k1).map Prod.fst).Nodup := by decide

/-- The constants are below `2²⁵⁶`. -/
theorem consts_lt : ∀ e ∈ consts secp256k1, e.2 < 2 ^ 256 := by decide

/-- The saves, `s0 = s3 = r` and `s2 = a0`. -/
theorem save_ok {s : State} {r : Reg} {base : Addr} (h0 : s.gpr r = base)
    (hwr : (⟨base, 8192⟩ : Region) ∈ s.wr) (hn : base.toNat + 8192 ≤ 2 ^ 64) (hal : base.toNat % 8 = 0) :
    WP isa (.block (saveCode r)) s fun s' => WsReg s' base ∧ s'.gpr .s3 = base ∧ s'.gpr .s2 = s.gpr .a0 ∧
      (∀ x, x ≠ .s0 → x ≠ .s2 → x ≠ .s3 → s'.gpr x = s.gpr x) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp ∧ Unch base [(0, 40)] s.mem s'.mem ∧
      word s'.mem base 0 = s.gpr .s0 ∧ word s'.mem base 8 = s.gpr .s1 ∧ word s'.mem base 16 = s.gpr .s2 ∧
      word s'.mem base 24 = s.gpr .ra ∧ word s'.mem base 32 = s.gpr .s3 :=
  TKit.save_ok h0 hwr hn hal

end VG.Proof.Ecdh.RISCV64.Secp256k1

namespace VG.Proof.Ecdh.RISCV64.Secp256k1

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdh.RISCV64.Cfg
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64 VG.Proof.Ecdsa.RISCV64.Secp256k1
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Spec.Weierstrass (Curve Fe Point)
open VG.Spec.Ecdsa (bytesAt)
open VG.WriteBytes (writeBytes)

/-- What `vg_secp256k1_mul` may write, as ranges of offsets. -/
abbrev mulKW : List (Nat × Nat) := [(512, 96), (608, 448), (128, 32), (1344, 32), (1504, 2 ^ 64)]

theorem unch_of_mulKeeps {base : Addr} {m m' : Mem} (h : MC.Keeps base m m') : Unch base mulKW m m' :=
  tkit.unch_of_mulKeeps h

/-- What `vg_secp256k1_check_point` may write, as ranges of offsets. -/
abbrev checkKW : List (Nat × Nat) :=
  [(128, 32), (1248, 32), (1376, 32), (1408, 32), (3840, 256), (1152, 32), (1184, 32), (1280, 32), (1440, 32),
    (FL, 8), (8192, 2 ^ 64)]

theorem not_mask (b : Bool) : maskOf b ^^^ BitVec.ofInt 64 (-1) = maskOf (!b) := by cases b <;> decide

/-- A call on the working space, then `s0` from `s3`. -/
theorem wsCallR_ok {f : String} {body : Prog isa} (hn : body.noFrames = true) {K : Contract isa}
    (hK : Meets body K) {s : State} {base : Addr} (hw : WsReg s base) (h3 : s.gpr .s3 = base)
    (hpre : ∀ t : State, t.rd = [] → t.wr = [⟨base, 8192⟩] → t.gpr .a0 = base → t.mem = s.mem → K.pre t)
    {Q : State → Prop}
    (hQ : ∀ s' s'' : State, Kp s s'' → s''.mem = s'.mem → ∀ t : State, t.gpr .a0 = base → t.mem = s.mem →
      K.post t (s'.withRegions [] [⟨base, 8192⟩]) → Q s'') :
    WP isa (Cfg.wsCall f body) s Q :=
  Kit.wsCallR_ok hn hK hw h3 hpre hQ

/-- A slot below the flag's. -/
theorem sl_lt {i : Nat} (hi : i < 44) : secp256k1.sl i % 8 = 0 ∧ secp256k1.sl i + 8 * 4 ≤ 2048 ∧ secp256k1.sl i + 8 * 4 ≤ FL := by
  simp only [Cfg.sl, slot, show secp256k1.n = 4 from rfl, FL]; omega_using [hi]

/-- The masks of `x < n` and `x ≠ 0` into the flag, for `x` at slot `i`. -/
theorem rangeOf_ok {i : Nat} (hi : i < 44) {s : State} {base : Addr} (hw : WsReg s base) :
    WP isa (.block (rangeOf secp256k1 i)) s fun s' =>
      Kp s s' ∧ Outside base FL 8 s.mem s'.mem ∧
      word s'.mem base FL = word s.mem base FL &&& maskOf (decide (sv base s i < sv base s MN)) &&&
        maskOf (!decide (sv base s i = 0)) :=
  TKit.rangeOf_ok secp256k1 (by decide) (Nat.lt_of_lt_of_le hi (by decide)) hw

/-- The constants `tail` reads. -/
structure TailConsts (base : Addr) (s : State) : Prop where
  mp : sv base s MP = W.p
  mn : sv base s MN = W.n
  zero : sv base s ZERO = 0
  one : sv base s ONE = 1
  onep : sv base s ONEP = 1 * 2 ^ 256 % W.p
  ap : sv base s AP = W.a * 2 ^ 256 % W.p
  b3p : sv base s B3P = 3 * W.b * 2 ^ 256 % W.p
  expp : sv base s EXPP = W.p - 2

theorem TailConsts.of_unch {base : Addr} {s s' : State} {W' : List (Nat × Nat)} (h : TailConsts base s)
    (U : Unch base W' s.mem s'.mem)
    (hW : ∀ i ∈ [MP, MN, ZERO, ONE, ONEP, AP, B3P, EXPP], ∀ w ∈ W', secp256k1.sl i + 32 ≤ w.1 ∨ w.1 + w.2 ≤ secp256k1.sl i) :
    TailConsts base s' :=
  have g := TKit.Consts.of_unch (c := secp256k1) (by decide) ⟨h.mp, h.mn, h.zero, h.one, h.onep, h.ap, h.b3p, h.expp⟩ U hW
  ⟨g.mp, g.mn, g.zero, g.one, g.onep, g.ap, g.b3p, g.expp⟩

theorem chainLay : ChainLayR (chainP secp256k1) 4 :=
  TKit.chainLay secp256k1 (by decide) (by decide)

/-- The chain is `p - 2`'s. -/
theorem chainP_ok : ChainOkR (chainP secp256k1) (W.p - 2) := ChainOkR.of_check (by lit_decide)

/-- The coordinate `[o] = [a] Z^(p-2)` out of Montgomery's form, `Z^(p-2) R` in `ACC`. -/
theorem affine_ok {s : State} {base : Addr} (hw : WsReg s base) {t o a : Nat} (ht : t < 44) (ho : o < 44)
    (ha : a < 44) (htm : t ≠ ONE ∧ t ≠ ACC) (hacc : sv base s ACC < W.p) (hone : sv base s ONE = 1) :
    WP isa (affineCoord secp256k1 t o a) s fun s' =>
      Kp s s' ∧ Unch base [(secp256k1.sl t, 32), (own 4, 256), (secp256k1.sl o, 32), (own 4, 256)] s.mem s'.mem ∧
      sv base s' o < W.p ∧
      Fin.ofNat W.p (sv base s' o) = toM W.p (2 ^ 256) (sv base s a) * toM W.p (2 ^ 256) (sv base s ACC) :=
  tkit.affine_ok hw ht ho ha htm hacc hone

/-- The coordinates the multiplication's contract decodes. -/
theorem dq (hL : VG.Proof.Weierstrass.Law W) (x : Nat) : MC.toPoint.dec x = toM W.p (2 ^ 256) x :=
  tkit.dq hL x

theorem coord_sv (m : Mem) (base : Addr) (i : Nat) (hi : i < 100 := by decide) :
    MC.toPoint.coordAt m base (secp256k1.sl i) = wordsVal m base (secp256k1.sl i) 4 :=
  tkit.coord_sv m base i hi

/-- The point the multiplication's contract reads. -/
theorem point_eq (hL : VG.Proof.Weierstrass.Law W) (m : Mem) (base : Addr) :
    MC.point base m = .affine (toM W.p (2 ^ 256) (wordsVal m base (secp256k1.sl RX) 4))
      (toM W.p (2 ^ 256) (wordsVal m base (secp256k1.sl RY) 4)) :=
  tkit.point_eq hL m base

theorem rep_of_represents {X Y Z : Fe W} {P : Point W} (h : Impl.Weierstrass.MulBase.Represents X Y Z P) :
    Rep W X Y Z P :=
  Kit.rep_of_represents h

/-- What `tail` writes. -/
abbrev tailW : List (Nat × Nat) :=
  [(FL, 8)] ++ mulKW ++ chainWx (chainP secp256k1) 4 ++
    [(secp256k1.sl XM, 32), (own 4, 256), (secp256k1.sl XO, 32), (own 4, 256)]

/-- `tail` with a call of `mulName`, whose code is `mulCode`, that computes
`R = [d]P` as `vg_secp256k1_mul`'s contract says (`hcall`, from the state after
the range's masks, which changes only the flag): the range of `d` into the
flag, `R = [d]P`, `Z^(p-2)`, and `x`. -/
theorem tailWith_ok (hL : VG.Proof.Weierstrass.Law W) {mulName : String} {mulCode : Prog isa} {s : State}
    {base : Addr} (hw : WsReg s base)
    (h3 : s.gpr .s3 = base) (hc : TailConsts base s)
    (hcall : ∀ s₁ : State, WsReg s₁ base → s₁.gpr .s3 = base → Kp s s₁ → Unch base [(FL, 8)] s.mem s₁.mem →
      s₁.syms = s.syms →
      WP isa (Cfg.wsCall mulName mulCode) s₁ fun s₂ => Kp s₁ s₂ ∧
        MC.ResultInRange (MC.scalar base s₁.mem) (MC.point base s₁.mem) base s₁.mem s₂.mem) :
    WP isa (tail secp256k1 mulName mulCode) s fun s' =>
      Kc s s' ∧ Unch base tailW s.mem s'.mem ∧
      word s'.mem base FL = word s.mem base FL &&& maskOf (decide (sv base s K < W.n)) &&&
        maskOf (!decide (sv base s K = 0)) ∧
      (1 ≤ sv base s K → sv base s K < W.n →
        Rep W (toM W.p (2 ^ 256) (sv base s' RX)) (toM W.p (2 ^ 256) (sv base s' RY))
          (toM W.p (2 ^ 256) (sv base s' RZ))
          (Spec.Weierstrass.mul (sv base s K) (.affine (toM W.p (2 ^ 256) (sv base s RX))
            (toM W.p (2 ^ 256) (sv base s RY)))) ∧
        sv base s' RX < W.p ∧ sv base s' RY < W.p ∧ sv base s' RZ < W.p) ∧
      sv base s' XO < W.p ∧
      Fin.ofNat W.p (sv base s' XO) =
        toM W.p (2 ^ 256) (sv base s' RX) * toM W.p (2 ^ 256) (sv base s' RZ) ^ (W.p - 2) ∧
      sv base s' ACC < W.p ∧
      toM W.p (2 ^ 256) (sv base s' ACC) = toM W.p (2 ^ 256) (sv base s' RZ) ^ (W.p - 2) :=
  tkit.tailWith_ok chainP_ok hL hw h3 ⟨hc.mp, hc.mn, hc.zero, hc.one, hc.onep, hc.ap, hc.b3p, hc.expp⟩ hcall

/-- A byte of a region apart from the working space. -/
theorem out_of_disj {p base : Addr} {n : Nat} (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩) (hn : p.toNat + n ≤ 2 ^ 64)
    {off i : Nat} (hi : off + i < n) : ¬ (⟨base, 8192⟩ : Region).Contains (p + BitVec.ofNat 64 (off + i)) 1 :=
  Kit.out_of_disj hd hn hi

/-- Eight bytes of a region. -/
theorem in_rd8 {rs : List Region} {p : Addr} {n : Nat} (hr : (⟨p, n⟩ : Region) ∈ rs) {off : Nat} (ho : off + 8 ≤ n)
    (hn : n ≤ 8192 := by decide) :
    InRegions rs (p + BitVec.ofNat 64 off) 8 :=
  Kit.in_rd8 hr ho hn

/-- Bytes apart from the working space survive changes within it. -/
theorem bytesAt_unch {base q : Addr} {W : List (Nat × Nat)} {n : Nat} {m m' : Mem} (U : Unch base W m m')
    (hW : ∀ w ∈ W, w.1 + w.2 ≤ 8192)
    (hsep : ∀ i < n, ¬ (⟨base, 8192⟩ : Region).Contains (q + BitVec.ofNat 64 i) 1) :
    bytesAt m' q n = bytesAt m q n :=
  Kit.bytesAt_unch U hW hsep

/-- The value of a constant's slot. -/
theorem const_at {base : Addr} {s : State} (hc : ∀ e ∈ consts secp256k1, sv base s e.1 = e.2) (k : Nat)
    (hk : k < (consts secp256k1).length := by decide) : sv base s (consts secp256k1)[k].1 = (consts secp256k1)[k].2 :=
  hc _ (List.getElem_mem hk)

/-- The bytes just written. -/
theorem bytesAt_writeBytes (m : Mem) (q : Addr) (xs : List Byte) (h : xs.length ≤ 2 ^ 64) :
    bytesAt (writeBytes m q xs) q xs.length = xs :=
  Kit.bytesAt_writeBytes m q xs h

theorem and_one (b : Bool) : maskOf b &&& BitVec.ofInt 64 1 = if b then 1 else 0 := by cases b <;> decide

/-- Bytes of a region apart from the working space, from an offset. -/
theorem sep_at' {p base : Addr} {n : Nat} (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩) (hn : p.toNat + n ≤ 2 ^ 64)
    {off k : Nat} (hk : off + k ≤ n) :
    ∀ i < k, ¬ (⟨base, 8192⟩ : Region).Contains (p + BitVec.ofNat 64 off + BitVec.ofNat 64 i) 1 := fun i hi => by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  exact out_of_disj hd hn (by omega_using [hk, hi])

/-- The multiplication's code pushes no frames. -/
theorem mulNF : mulSecp256k1.noFrames = true :=
  Impl.Ecdsa.RISCV64.mulSecp256k1_noFrames

/-- The multiplication meets the contract `tail` calls it by. -/
theorem mul_meets (hL : VG.Proof.Weierstrass.Law tkit.c.C) : Meets mulSecp256k1 (TKit.mulRVc tkit.MC) :=
  mul_rv hL

end VG.Proof.Ecdh.RISCV64.Secp256k1
