module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTable
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtBuild
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! Build all 32 Montgomery powers for five-bit CRT exponentiation. -/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.WindowFive

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep count_loop)

/-- The count in `sBit` decremented, into `x3`. -/
theorem crtBitEnd_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc b : Nat}
    (hc : TableCtx t P wx minv X Xc) (hb : word t.mem P (8 * Crt.sBit) = BitVec.ofNat 64 b) (hb1 : 1 ≤ b) :
    WP isa (.block [ldh .x3 Crt.sBit, .subImm .x .x3 .x3 1, sth .x3 Crt.sBit]) t
      fun t' => (t'.mem = t.mem.writeW (off P (8 * Crt.sBit)) (BitVec.ofNat 64 (b - 1)) ∧
        t'.gpr .x3 = BitVec.ofNat 64 (b - 1)) ∧ Keep [.x3] t t' :=
  VG.Proof.Bignum.AArch64.crtBitEnd_ok hc.toC hb hb1

/-- The count's register, not zero iff the count is not. -/
theorem cnt_ne {b : Nat} (hb : b < 2 ^ 64) : (BitVec.ofNat 64 b).toNat ≠ 0 ↔ b ≠ 0 :=
  VG.Proof.Bignum.AArch64.cnt_ne hb

/-! ## The table -/

/-- The table's base, past the last array, into `sTab` and `sEnt`. -/
theorem tabInit_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    (hc : TableCtx t P wx minv X Xc) (hw : wx < 2 ^ 30) :
    WP isa (.block [ldh .x3 (sArr aOne), ldh .x4 sW, .addImm .x .x4 .x4 2, .lsl .x .x4 .x4 3, .add .x .x3 .x3 .x4,
      sth .x3 Crt.sTab, sth .x3 Crt.sEnt]) t fun t' =>
      t'.mem = (t.mem.writeW (off P (8 * Crt.sTab)) (off P (slot wx 8))).writeW (off P (8 * Crt.sEnt))
        (off P (slot wx 8)) ∧ Keep [.x3, .x4] t t' :=
  VG.Proof.Bignum.AArch64.tabInit_ok hc.toC hw

/-- `sBit := 30`, the count of the table's products. -/
theorem cnt30_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    (hc : TableCtx t P wx minv X Xc) :
    WP isa (.block [movi .x3 30, sth .x3 Crt.sBit]) t fun t' =>
      t'.mem = t.mem.writeW (off P (8 * Crt.sBit)) (BitVec.ofNat 64 30) ∧ Keep [.x3] t t' := by
  refine WP.keep _ ?_ (by decide) (by decide) (by decide +kernel)
  brun [hc.good.x0, hdr_enc (show Crt.sBit < 32 by decide), hc.st (i := Crt.sBit) (by decide)]
  rfl

/-- After `i` of the table's products from `t₀`: entries `0 … i + 1`
written, `T ≡ x^(i+1) R` the last. -/
structure BuildInv (t₀ : State) (P : Addr) (wx : Nat) (minv : BitVec 64) (X Xc : Nat) (Q : Prop) (x : Nat)
    (i : Nat) (t : State) : Prop where
  ctx : TableCtx t P wx minv X Xc
  tab : word t.mem P (8 * Crt.sTab) = off P (slot wx 8)
  ent : word t.mem P (8 * Crt.sEnt) = off P (slot wx (8 + (i + 1)))
  cnt : word t.mem P (8 * Crt.sBit) = BitVec.ofNat 64 (30 - i)
  tlt : wv t.mem P (slot wx Crt.aT) wx < X
  tval : Q → wv t.mem P (slot wx Crt.aT) wx % X = x ^ (i + 1) * 2 ^ (64 * wx) % X
  elt : ∀ j < i + 2, wv t.mem P (slot wx (8 + j)) wx < X
  eval : Q → ∀ j < i + 2, wv t.mem P (slot wx (8 + j)) wx % X = x ^ j * 2 ^ (64 * wx) % X
  frm : Frm P (VG.Proof.Bignum.CrtWindowFive.buildRanges wx) t₀.mem t.mem
  keep : Keep mmRegs t₀ t

/-- A product of the table's build. -/
def tabBody (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) :=
  [mul Crt.aT Crt.aT Crt.aXc, nextEnt] ++ (toEnt Crt.aT ++
    [.block [ldh .x3 Crt.sBit, .subImm .x .x3 .x3 1, sth .x3 Crt.sBit]])

theorem BuildInv.toN {t₀ t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat} {Q : Prop} {x i : Nat}
    (h : BuildInv t₀ P wx minv X Xc Q x i t) : BuildInvN t₀ P wx minv X Xc Q x 32 30 i t :=
  ⟨h.ctx.toC, h.tab, h.ent, h.cnt, h.tlt, h.tval, h.elt, h.eval, h.frm, h.keep⟩

theorem BuildInv.ofN {t₀ t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat} {Q : Prop} {x i : Nat}
    (h : BuildInvN t₀ P wx minv X Xc Q x 32 30 i t) : BuildInv t₀ P wx minv X Xc Q x i t :=
  ⟨TableCtx.ofC h.ctx, h.tab, h.ent, h.cnt, h.tlt, h.tval, h.elt, h.eval, h.frm, h.keep⟩

/-- The table's product `i`. -/
theorem buildStep_ok (M : Mont) {t₀ t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat} {Q : Prop}
    {x : Nat} (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * wx)) X) (hXN : Xc < X)
    (hXc : Q → Xc % X = x * 2 ^ (64 * wx) % X) {i : Nat} (hi : i < 30)
    (hI : BuildInv t₀ P wx minv X Xc Q x i t) :
    WP isa (seqs (tabBody M.mm)) t
      fun t' => BuildInv t₀ P wx minv X Xc Q x (i + 1) t' ∧ ((t'.gpr .x3).toNat ≠ 0 ↔ i + 1 ≠ 30) :=
  WP.mono (buildStepN_ok M hw hw' hR hXN hXc rfl (by decide) hi hI.toN) fun _ ⟨h, k⟩ => ⟨BuildInv.ofN h, k⟩

/-- The table's first two entries, `T` and the count. -/
def tabPre : List (Prog isa) :=
  [.block [ldh .x3 (sArr aOne), ldh .x4 sW, .addImm .x .x4 .x4 2, .lsl .x .x4 .x4 3, .add .x .x3 .x3 .x4,
    sth .x3 Crt.sTab, sth .x3 Crt.sEnt]] ++ (toEnt aY ++ ([nextEnt] ++
    (toEnt Crt.aXc ++ (copyArr Crt.aT Crt.aXc ++ [.block [movi .x3 30, sth .x3 Crt.sBit]]))))

/-- The table's products. -/
def tabLoop (mul : Nat → Nat → Nat → Prog isa) : Prog isa := .loop (seqs (tabBody mul)) (.nonzero .x .x3)

theorem tabBuild_eq (mul : Nat → Nat → Nat → Prog isa) : VG.Impl.Rsa.AArch64.WindowFive.tabBuild32 mul = tabPre ++ [tabLoop mul] := by
  simp [VG.Impl.Rsa.AArch64.WindowFive.tabBuild32, tabPre, tabLoop, tabBody]

/-- The table's first two entries: `T_0 := Y ≡ R`, `T_1 := [aXc] ≡ x R`. -/
theorem tabPre_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat} {Q : Prop}
    {x : Nat} (hc : TableCtx t P wx minv X Xc) (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30)
    (hXN : Xc < X) (hXc : Q → Xc % X = x * 2 ^ (64 * wx) % X) (hY : wv t.mem P (slot wx aY) wx < X)
    (hYv : Q → wv t.mem P (slot wx aY) wx % X = 2 ^ (64 * wx) % X) :
    WP isa (seqs tabPre) t (BuildInv t P wx minv X Xc Q x 0) :=
  WP.mono (tabPreN_ok hc.toC hw hw' rfl (fun hu => cnt30_ok (TableCtx.ofC hu)) hXN hXc hY hYv) fun _ h => BuildInv.ofN h

/-- The table: `T_0 := Y ≡ R`, `T_1 := [aXc] ≡ x R` and `T_i := T_(i-1) [aXc] R⁻¹`. -/
theorem tabBuild_ok (M : Mont) {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat} {Q : Prop}
    {x : Nat} (hc : TableCtx t P wx minv X Xc) (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30)
    (hR : Nat.Coprime (2 ^ (64 * wx)) X)
    (hXN : Xc < X) (hXc : Q → Xc % X = x * 2 ^ (64 * wx) % X) (hY : wv t.mem P (slot wx aY) wx < X)
    (hYv : Q → wv t.mem P (slot wx aY) wx % X = 2 ^ (64 * wx) % X) :
    WP isa (seqs (VG.Impl.Rsa.AArch64.WindowFive.tabBuild32 M.mm)) t fun t' => TableCtx t' P wx minv X Xc ∧ VG.Proof.Bignum.CrtWindowFive.CTab t'.mem P wx X Q x ∧
      wv t'.mem P (slot wx aY) wx = wv t.mem P (slot wx aY) wx ∧
      (∀ k < 32, k ≠ Crt.sTab → k ≠ Crt.sEnt → k ≠ Crt.sBit → word t'.mem P (8 * k) = word t.mem P (8 * k)) ∧
      Frm P (VG.Proof.Bignum.CrtWindowFive.crtExpRanges wx) t.mem t'.mem ∧ Keep mmRegs t t' := by
  have e : VG.Impl.Rsa.AArch64.WindowFive.tabBuild32 M.mm =
      VG.Proof.Bignum.AArch64.tabPreN 30 ++ [VG.Proof.Bignum.AArch64.tabLoop M.mm] := by
    simp [VG.Impl.Rsa.AArch64.WindowFive.tabBuild32, VG.Proof.Bignum.AArch64.tabPreN,
      VG.Proof.Bignum.AArch64.tabLoop, VG.Proof.Bignum.AArch64.tabBody]
  rw [e]
  exact WP.mono (VG.Proof.Bignum.AArch64.tabBuildN_ok M hc.toC hw hw' rfl (by decide) (by decide)
    (fun hu => cnt30_ok (TableCtx.ofC hu)) hR hXN hXc hY hYv)
    fun _ ⟨c, tab, y, k, f, kp⟩ => ⟨TableCtx.ofC c, ⟨tab.tab, tab.lt, tab.val⟩, y, k, f, kp⟩

end VG.Proof.Bignum.AArch64.WindowFive
