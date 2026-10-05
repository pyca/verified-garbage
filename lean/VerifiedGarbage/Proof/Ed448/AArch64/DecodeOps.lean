import VerifiedGarbage.Proof.X448.AArch64.Base.AddGen
import VerifiedGarbage.Proof.Ed448.VerifyFormulas
import VerifiedGarbage.Impl.Ed448.AArch64.VerifyEquation

/-!
# Ed448 verification's equation on AArch64: decoding's field operations

Untrusted: everything here is checked by Lean. The register-resident
operations of decoding around the square root: `decodeUVOps` leaves `u`,
`v`, `u³v` and `u⁵v³` where `decodeUV` does (`uvOps_ok`, `uvEnv_eval`), and
`decodeXOps` leaves `x` and `v x²` (`xOps_ok`, `xEnv_eval`).
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Impl.X448.AArch64 (slot)
open VG.Proof.X448.AArch64 (Scr)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd FKeep Same mulOp subOp)
open VG.Proof.Curve448.AArch64.Fast (Mb)
open VG.Proof.X448.AArch64.Base (mulS subS)
open VG.Impl.X448.AArch64.Fast (ops)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

/-- The slots after `decodeUVOps yo xo`. -/
def uvEnv (yo xo : Index) (e : Env) : Env :=
  mulS 12 xo 4 <| mulS xo 5 3 <| mulS 5 5 13 <| mulS 5 13 13 <| mulS 4 4 4 <| mulS 4 13 3 <|
  subS 3 4 10 <| mulS 4 11 12 <| subS 13 12 10 <| mulS 12 yo yo e

theorem decodeUVOps_eq (yo xo : Index) : decodeUVOps yo.val xo.val =
    [.mul (slot (12 : Index).val) (slot yo.val) (slot yo.val),
     .sub (slot (13 : Index).val) (slot (12 : Index).val) (slot (10 : Index).val),
     .mul (slot (4 : Index).val) (slot (11 : Index).val) (slot (12 : Index).val),
     .sub (slot (3 : Index).val) (slot (4 : Index).val) (slot (10 : Index).val),
     .mul (slot (4 : Index).val) (slot (13 : Index).val) (slot (3 : Index).val),
     .mul (slot (4 : Index).val) (slot (4 : Index).val) (slot (4 : Index).val),
     .mul (slot (5 : Index).val) (slot (13 : Index).val) (slot (13 : Index).val),
     .mul (slot (5 : Index).val) (slot (5 : Index).val) (slot (13 : Index).val),
     .mul (slot xo.val) (slot (5 : Index).val) (slot (3 : Index).val),
     .mul (slot (12 : Index).val) (slot xo.val) (slot (4 : Index).val)] := rfl

/-- `u`, `v`, `u³v` and `u⁵v³`, as `decodeUV_eval`. -/
theorem uvEnv_eval (xo yo : Fin 22) (h : (xo = 6 ∧ yo = 7) ∨ (xo = 8 ∧ yo = 9)) (e : Env) :
    let y := e yo
    let u := y * y - e 10
    let v := e 11 * (y * y) - e 10
    let t := u * u * u * v
    let e' := uvEnv yo xo e
    e' 13 = u ∧ e' 3 = v ∧ e' xo = t ∧ e' 12 = t * ((u * v) * (u * v)) ∧
      ∀ i : Fin 22, i ≠ 3 → i ≠ 4 → i ≠ 5 → i ≠ 12 → i ≠ 13 → i ≠ xo → e' i = e i := by
  have hk : ∀ i : Fin 22, i ≠ 3 → i ≠ 4 → i ≠ 5 → i ≠ 12 → i ≠ 13 → i ≠ xo → uvEnv yo xo e i = e i :=
    fun i h3 h4 h5 h12 h13 hx => by
      simp only [uvEnv, mulS, subS, Function.update_of_ne h3, Function.update_of_ne h4, Function.update_of_ne h5,
        Function.update_of_ne h12, Function.update_of_ne h13, Function.update_of_ne hx]
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, hk⟩
  · exact ⟨rfl, rfl, rfl, rfl, hk⟩

/-- **`u`, `v`, `u³v` and `u⁵v³`**, from `y` in slot `yo`, `d` in 11 and 1 (below the products'
bound) in 10. -/
theorem uvOps_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base)
    (h10 : Bnd Mb s.mem base (slot (10 : Index).val)) (xo yo : Index) (hxy : (xo = 6 ∧ yo = 7) ∨ (xo = 8 ∧ yo = 9)) :
    WP isa (ops (decodeUVOps yo.val xo.val)) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ EV t.mem base = uvEnv yo xo (EV s.mem base) := by
  have hx3 : xo ≠ 3 := by rcases hxy with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
  have hx5 : xo ≠ 5 := by rcases hxy with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
  rw [decodeUVOps_eq]
  refine mulOp hs hb 12 yo yo (Or.inl rfl) fun t1 k1 b1 m1 s1 e1 => ?_
  have hs1 := k1.scr hs
  refine subOp (o := 13) (a := 12) (b := 10) hs1 b1 m1 (s1.bnd (by decide) h10) (by decide) (by decide)
    fun t2 k2 b2 s2 e2 => ?_
  have hs2 := k2.scr hs1
  refine mulOp hs2 b2 4 11 12 (Or.inr (by decide)) fun t3 k3 b3 m3 s3 e3 => ?_
  have hs3 := k3.scr hs2
  refine subOp (o := 3) (a := 4) (b := 10) hs3 b3 m3 (s3.bnd (by decide) (s2.bnd (by decide) (s1.bnd (by decide) h10)))
    (by decide) (by decide) fun t4 k4 b4 s4 e4 => ?_
  have hs4 := k4.scr hs3
  refine mulOp hs4 b4 4 13 3 (Or.inr (by decide)) fun t5 k5 b5 _ s5 e5 => ?_
  have hs5 := k5.scr hs4
  refine mulOp hs5 b5 4 4 4 (Or.inl rfl) fun t6 k6 b6 _ s6 e6 => ?_
  have hs6 := k6.scr hs5
  refine mulOp hs6 b6 5 13 13 (Or.inl rfl) fun t7 k7 b7 _ s7 e7 => ?_
  have hs7 := k7.scr hs6
  refine mulOp hs7 b7 5 5 13 (Or.inr (by decide)) fun t8 k8 b8 _ s8 e8 => ?_
  have hs8 := k8.scr hs7
  refine mulOp hs8 b8 xo 5 3 (Or.inr hx3) fun t9 k9 b9 _ s9 e9 => ?_
  have hs9 := k9.scr hs8
  refine mulOp hs9 b9 12 xo 4 (Or.inr (by decide)) fun t10 k10 b10 _ s10 e10 => ?_
  refine WP.block_nil ⟨k1.trans (k2.trans (k3.trans (k4.trans (k5.trans (k6.trans (k7.trans (k8.trans
    (k9.trans k10)))))))), b10, ?_⟩
  exact e10.trans <| congrArg (mulS 12 xo 4) <| e9.trans <| congrArg (mulS xo 5 3) <| e8.trans <|
    congrArg (mulS 5 5 13) <| e7.trans <| congrArg (mulS 5 13 13) <| e6.trans <| congrArg (mulS 4 4 4) <|
    e5.trans <| congrArg (mulS 4 13 3) <| e4.trans <| congrArg (subS 3 4 10) <| e3.trans <|
    congrArg (mulS 4 11 12) <| e2.trans <| congrArg (subS 13 12 10) <| e1

/-- The slots after `decodeXOps xo`. -/
def xEnv (xo : Index) (e : Env) : Env := mulS 12 12 3 <| mulS 12 xo xo <| mulS xo xo 21 e

theorem decodeXOps_eq (xo : Index) : decodeXOps xo.val =
    [.mul (slot xo.val) (slot xo.val) (slot (21 : Index).val), .mul (slot (12 : Index).val) (slot xo.val) (slot xo.val),
     .mul (slot (12 : Index).val) (slot (12 : Index).val) (slot (3 : Index).val)] := rfl

/-- `x` and `v x²`, as `decodeXOps_eval`. -/
theorem xEnv_eval (xo : Fin 22) (h : xo = 6 ∨ xo = 8) (e : Env) :
    let x := e xo * e 21
    let e' := xEnv xo e
    e' xo = x ∧ e' 12 = e 3 * (x * x) ∧ e' 13 = e 13 ∧ ∀ i : Fin 22, i ≠ xo → i ≠ 12 → e' i = e i := by
  have hk : ∀ i : Fin 22, i ≠ xo → i ≠ 12 → xEnv xo e i = e i := fun i hx h12 => by
    simp only [xEnv, mulS, Function.update_of_ne hx, Function.update_of_ne h12]
  rcases h with rfl | rfl
  · exact ⟨rfl, Fin.mul_comm _ _, rfl, hk⟩
  · exact ⟨rfl, Fin.mul_comm _ _, rfl, hk⟩

/-- **`x` and `v x²`**, with `x` and `x² v` below the products' bound. -/
theorem xOps_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) (xo : Index)
    (hxo : xo = 6 ∨ xo = 8) :
    WP isa (ops (decodeXOps xo.val)) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ Bnd Mb t.mem base (slot xo.val) ∧ Same base [xo, 12] s.mem t.mem ∧
      EV t.mem base = xEnv xo (EV s.mem base) := by
  have hx21 : xo ≠ 21 := by rcases hxo with rfl | rfl <;> decide
  have hx12 : xo ∉ ([12] : List Index) := by rcases hxo with rfl | rfl <;> decide
  rw [decodeXOps_eq]
  refine mulOp hs hb xo xo 21 (Or.inr hx21) fun t1 k1 b1 m1 s1 e1 => ?_
  have hs1 := k1.scr hs
  refine mulOp hs1 b1 12 xo xo (Or.inl rfl) fun t2 k2 b2 _ s2 e2 => ?_
  have hs2 := k2.scr hs1
  refine mulOp hs2 b2 12 12 3 (Or.inr (by decide)) fun t3 k3 b3 _ s3 e3 => ?_
  refine WP.block_nil ⟨k1.trans (k2.trans k3), b3, s3.bnd hx12 (s2.bnd hx12 m1), ?_, ?_⟩
  · intro i hi j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    rw [s3 i (by simp [hi.2]) j hj, s2 i (by simp [hi.2]) j hj, s1 i (by simp [hi.1]) j hj]
  · exact e3.trans <| congrArg (mulS 12 12 3) <| e2.trans <| congrArg (mulS 12 xo xo) <| e1

end VG.Proof.Ed448.AArch64
