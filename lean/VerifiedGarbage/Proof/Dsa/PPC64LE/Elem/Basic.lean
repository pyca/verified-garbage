module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Ctx
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Eq
import VerifiedGarbage.Proof.Dsa.PPC64LE.Range
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Common
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Sel

/-!
# DSA on PPC64LE: helpers of the checks of p, q, g and y

* `keyLen_ok`: the key and `p_len` from the header, for `reduce`;
* `unmask_ok`: `r0 = 0` exactly when the mask in `r3` is all ones;
* `clear20_ok`: `r20 &= ¬r19`, of masks.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE
open VG.Proof.Bignum (slot)

theorem Lay.Ok.hdr {L : Lay} (hL : L.Ok) : 256 ≤ L.Z := by
  have := hL.room; rcases hL.pl with e | e | e <;> omega

theorem unmask_eq (b : Bool) :
    (mask b &&& BitVec.ofNat 64 1) ^^^ BitVec.ofNat 64 1 = BitVec.ofNat 64 (if b then 0 else 1) := by
  cases b <;> rfl

/-- `unmask`: `r0 = 0` exactly when the mask of `b` in `r3` is all ones. -/
theorem unmask_ok (s : State) {b : Bool} (h3 : s.gpr .r3 = mask b) :
    WP isa (.block unmask) s fun t => ((t.gpr .r0 = 0 ↔ b = true) ∧ t.mem = s.mem) ∧ Keep [.r0, .r3, .r4] s t := by
  refine WP.keep _ ?_ (by decide)
  unfold unmask
  prun [h3, unmask_eq]
  cases b <;> decide

/-- `clear19`: `r20 &= ¬r19` with masks. -/
theorem clear20_ok (s : State) {a b : Bool} (h20 : s.gpr .r20 = mask a) (h19 : s.gpr .r19 = mask b) :
    WP isa (.block clear19) s fun t => (t.gpr .r20 = mask (a && !b) ∧ t.mem = s.mem) ∧ Keep [.r20] s t := by
  refine WP.keep _ ?_ (by decide)
  unfold clear19
  prun [h20, h19, mask_clear]

/-- The key and `p_len`, for `reduce` and the like. -/
theorem keyLen_ok {s : State} {L : Lay} {key sig dig : Addr} (hr : Regs s L key sig dig) :
    WP isa (.block ([.addi .r30 .r27 0] ++ getP .r31)) s fun t =>
      (t.gpr .r30 = key ∧ t.gpr .r31 = BitVec.ofNat 64 L.pl ∧ t.mem = s.mem) ∧ Keep [.r30, .r31] s t := by
  refine WP.keep _ ?_ (by decide)
  unfold getP
  prun [hr.r27, Regs.p_eq hr, BitVec.add_zero]

/-- The first `k` bytes of a buffer, unchanged by a change in the body. -/
theorem Src.bytesPre {s : State} {L : Lay} {D : Addr} {n : Nat} (h : Src s L D n) {k : Nat} (hk : k ≤ n)
    {m m' : Mem} (hb : Body L m m') (hZ : 256 ≤ L.Z) :
    Spec.Rsa.bytesAt m' D k = Spec.Rsa.bytesAt m D k := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => hb _ (Or.inr ?_)
  have hi := List.mem_range.mp hi
  by_contra hc
  exact h.sep i (by omega) (D + BitVec.ofNat 64 i) (by omega) rfl

/-- `Env`, again after code that set `r31` back to the space. -/
theorem env_keep31 {s t : State} {B : Addr} {Z w : Nat} {rs : List Reg} (h : Env s B Z w) (k : Keep rs s t)
    (hr : ∀ r ∈ ([.r10, .r11, .r29] : List Reg), r ∉ rs) (h31 : t.gpr .r31 = B) : Env t B Z w :=
  ⟨h.hs.congr k.wr, (k.gpr _ (hr _ (by decide))).trans h.h10, (k.gpr _ (hr _ (by decide))).trans h.h29,
    (k.gpr _ (hr _ (by decide))).trans h.h11, h31, h.hw, h.hw', h.hZ⟩

end VG.Proof.Dsa.PPC64LE
