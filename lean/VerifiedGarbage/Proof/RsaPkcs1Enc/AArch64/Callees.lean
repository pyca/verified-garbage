module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncVerified
public import VerifiedGarbage.Proof.Rsa.AArch64.PrivVerified
public import VerifiedGarbage.Impl.Rsa.AArch64
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Rsa.AArch64.PubChecked
import Mathlib.Data.List.Basic
public import VerifiedGarbage.Proof.Rsa.Contract
public import VerifiedGarbage.Proof.Rsa.AArch64.PrivPrecomputed
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecCTBase
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Rsa.PrivCheck
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncLay
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncEntry
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCall
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Rsa.AArch64.PrivPrecomputed
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecCTBase
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncVerified
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Rsa.PrivCheck
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncLay
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncEntry
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCall
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
public meta import VerifiedGarbage.Impl.RsaPkcs1Enc.AArch64.Decrypt
public import VerifiedGarbage.Proof.Framework.AArch64.ModeSim
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecMac
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecOut
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecKdk
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCorrect
import VerifiedGarbage.Proof.RsaPkcs1Enc.Decrypt
import Mathlib.Data.Fintype.Card
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecOut
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecIrprf
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.Bytes
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecIrprf
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.Bytes
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecKdk
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecMac
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecD
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Spec.RsaPkcs1Sig
import VerifiedGarbage.TCB.Registration
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecD
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCorrect
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Spec.RsaPkcs1Sig
meta import VerifiedGarbage.TCB.Registration
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.Decrypt
meta import Mathlib.Data.Fintype.Card

/-! ### `RsaPkcs1Enc.AArch64.DecPrecomputed`, which only this module used -/

section

/-! ### `RsaPkcs1Enc.AArch64.DecVerified`, which this module and modules that import it used -/

section

/-! ### `RsaPkcs1Enc.AArch64.DecCT1`, which this module and modules that import it used -/

section

/-!
# RSAES-PKCS1-v1_5 decryption on AArch64: constant time, to `D`

The setup (`setup_ct`), from two entry states whose public data agree, the
private-key operation (`priv_ct`), and `D` (`dBuild_ct`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Decrypt
open VG.Proof.RsaPkcs1Enc.AArch64.Enc (gpr_ce stackArg_ce leak_split bytesAt_length)

/-- Two calls whose public data agree, in the inner frame. -/
def Entered (S : Nat) (a b : State) : Prop :=
  ∃ s₁ s₂, (decSpec (S + 1)).pre s₁ ∧ (decSpec (S + 1)).pre s₂ ∧ (decSpec (S + 1)).pub s₁ s₂ ∧
    a = entered s₁ ∧ b = entered s₂

/-- After the setup. -/
abbrev CtxReady : Inv := fun L g vv m₀ t => Ctx L g vv m₀ t ∧ Ready L t

theorem setup_ct (S : Nat) : RelCT isa (Entered S) (.block setup) (Two S CtxReady) := by
  intro a b ta tb a' b' ⟨s₁, s₂, h₁, h₂, hp, ea, eb⟩ e₁ e₂
  subst ea eb
  sig_pub [Spec.RsaPkcs1Enc.decryptContract, Spec.RsaPkcs1Enc.decryptSig, AArch64.abi, AArch64.argRegs,
    _root_.List.range, _root_.List.range.loop, List.append_eq] at hp
  obtain ⟨hsp, hl, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13,
    a14⟩ := hp
  have ht := (RelCT.taint (A := taint) (P := fun x y => x.sp = y.sp) (Taint.ofRegs [])
    (fun _ _ h => ⟨h, fun _ hr => False.elim (by simp at hr)⟩) (by taint_decide)
    _ _ _ _ _ _ (by show (entered s₁).sp = (entered s₂).sp; rw [entered_sp (S + 1), entered_sp (S + 1)]; simp only [lay, hsp]) e₁ e₂).1
  obtain ⟨_, u₁, x₁, y₁⟩ := entry_ok h₁
  obtain ⟨_, u₂, x₂, y₂⟩ := entry_ok h₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  have e : lay (S + 1) s₂ = lay (S + 1) s₁ := by
    simp only [lay, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13,
      a14, hsp]
  obtain ⟨hn, he⟩ := leak_split hl (by rw [bytesAt_length, bytesAt_length, h4])
  refine ⟨ht, ⟨lay (S + 1) s₁, s₁.gpr, s₂.gpr, s₁.v, s₂.v, s₁.mem, s₂.mem⟩, lay_ok h₁, rfl, ⟨?_, ?_⟩, y₁, e ▸ y₂⟩
  · show Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x3) (s₁.gpr .x4).toNat = Spec.Rsa.bytesAt s₂.mem (s₁.gpr .x3) (s₁.gpr .x4).toNat
    rw [hn, h3, h4]
  · show Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x5) (s₁.gpr .x6).toNat = Spec.Rsa.bytesAt s₂.mem (s₁.gpr .x5) (s₁.gpr .x6).toNat
    rw [he, h5, h6]

theorem priv_pub' {L : Lay} {S : Nat} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}
    (hL : L.Ok) (hk : LeakEq L m₁ m₂) {a b : State} (ha : CtxReady L g₁ v₁ m₁ a) (hb : CtxReady L g₂ v₂ m₂ b) :
    (privK S).pub (a.callEntry.withRegions (privRd L) (privWr L))
      (b.callEntry.withRegions (privRd L) (privWr L)) := by
  have aa := priv_args ha.1 (privRd L) (privWr L)
  have ab := priv_args hb.1 (privRd L) (privWr L)
  simp only [privK, State.withRegions_sp, State.callEntry_sp, State.withRegions_mem, State.callEntry_mem,
    gpr_ce _ _ _ (by decide : Reg.x0 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x1 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x2 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x3 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x4 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x5 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x6 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x7 ∉ linkRegs),
    ha.2.x0, ha.2.x1, ha.2.x2, ha.2.x3, ha.2.x4, ha.2.x5, ha.2.x6, ha.2.x7, hb.2.x0, hb.2.x1, hb.2.x2, hb.2.x3,
    hb.2.x4, hb.2.x5, hb.2.x6, hb.2.x7, ha.1.sp, hb.1.sp, true_and]
  refine ⟨fun i hi => ?_, ?_, ?_⟩
  · obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ := ab
    obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11⟩ := aa
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i
    exacts [c0.trans b0.symm, c1.trans b1.symm, c2.trans b2.symm, c3.trans b3.symm, c4.trans b4.symm,
      c5.trans b5.symm, c6.trans b6.symm, c7.trans b7.symm, c8.trans b8.symm, c9.trans b9.symm,
      c10.trans b10.symm, c11.trans b11.symm, absurd hi (by omega_using [])]
  · rw [ha.1.bytes_ro hL (ro_N L), hb.1.bytes_ro hL (ro_N L)]; exact hk.1
  · rw [ha.1.bytes_ro hL (ro_E L), hb.1.bytes_ro hL (ro_E L)]; exact hk.2

theorem priv_ct (v : PrivImpl) : RelCT isa (Two v.S CtxReady) (.call v.name v.code) (Two v.S Called) :=
  two_wp (fun e => RelCT.call (n := v.name) v.correct v.ct (privRd e.L) (privWr e.L)
    fun _ _ ⟨hL, hP, hk, f₁, f₂⟩ =>
      ⟨priv_pre' hL hP f₁.1 f₁.2, priv_pre' hL hP f₂.1 f₂.2, priv_pub' hL hk f₁ f₂, (covers_priv f₁.1).1,
        (covers_priv f₁.1).2, (covers_priv f₂.1).1, (covers_priv f₂.1).2⟩)
    fun _ _ _ _ _ hL hP h => priv_call v hL hP h.1 h.2

/-! ## `D` -/

theorem dBuild_ct (S : Nat) :
    RelCT isa (Two S Called) dBuild (Two S fun L g vv m₀ t => ∃ R EM, DB L g vv m₀ R EM t) := by
  refine (two (Ψ := fun L g vv m₀ t => ∃ R EM, ZInv L g vv m₀ R EM 0 t) [] (by taint_decide)
    (fun _ _ _ _ _ _ _ _ _ _ f₁ f₂ => ⟨f₁.ctx.sp.trans f₂.ctx.sp.symm, fun _ h => absurd h List.not_mem_nil⟩)
    fun _ _ _ _ _ hL _ h => WP.mono (dPtrs₁_inv hL h) fun _ h' => ⟨_, _, h'⟩).seq
    ((two (Ψ := fun L g vv m₀ t => ∃ R EM, ZInv L g vv m₀ R EM L.k.toNat t) [.x11, .x12] (by taint_decide)
      (fun _ _ _ _ _ _ _ _ _ _ ⟨_, _, f₁⟩ ⟨_, _, f₂⟩ => ⟨f₁.post.ctx.sp.trans f₂.post.ctx.sp.symm, by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl)
        exacts [f₁.x11.trans f₂.x11.symm, f₁.x12.trans f₂.x12.symm]⟩)
      fun _ _ _ _ _ hL _ ⟨_, _, h⟩ => WP.mono (zeroLoop_ok hL h) fun _ h' => ⟨_, _, h'⟩).seq
    ((two (Ψ := fun L g vv m₀ t => ∃ R EM, CInv L g vv m₀ R EM 0 t) [] (by taint_decide)
      (fun _ _ _ _ _ _ _ _ _ _ ⟨_, _, f₁⟩ ⟨_, _, f₂⟩ =>
        ⟨f₁.post.ctx.sp.trans f₂.post.ctx.sp.symm, fun _ h => absurd h List.not_mem_nil⟩)
      fun _ _ _ _ _ hL _ ⟨_, _, h⟩ => WP.mono (dPtrs₂_inv hL h) fun _ h' => ⟨_, _, h'⟩).seq
    (two [.x14, .x11, .x12] (by taint_decide)
      (fun _ _ _ _ _ _ _ _ _ _ ⟨_, _, f₁⟩ ⟨_, _, f₂⟩ => ⟨f₁.post.ctx.sp.trans f₂.post.ctx.sp.symm, by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl | rfl)
        exacts [f₁.x14.trans f₂.x14.symm, f₁.x11.trans f₂.x11.symm, f₁.x12.trans f₂.x12.symm]⟩)
      fun _ _ _ _ _ hL _ ⟨_, _, h⟩ => WP.mono (copyLoop_ok hL h) fun _ h' => ⟨_, _, cinv_db hL h'⟩)))

end VG.Proof.RsaPkcs1Enc.AArch64.Dec

end

end

/-! ### `RsaPkcs1Enc.AArch64.DecCT4`, which this module and modules that import it used -/

section

/-! ### `RsaPkcs1Enc.AArch64.DecCT3`, which this module and modules that import it used -/

section

/-! ### `RsaPkcs1Enc.AArch64.DecCT2`, which this module and modules that import it used -/

section

/-! ### `RsaPkcs1Enc.AArch64.DecArgs`, which only this module used -/

section

/-!
# RSAES-PKCS1-v1_5 decryption on AArch64: the calls' arguments

The arguments of each call of SHA-256's and HMAC's functions, from `Post`
and the registers the block before it sets (`initA`, `updA`, `finA`,
`hinitA`, `hfinA`), what each call keeps of `Post` and of the frame's words
from `oI` on (`Weak`, `initW` …), and that two runs with the same layout
make the same call (`initR` …).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Decrypt
open VG.Proof.Sha256.AArch64 (Compress)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (After)

variable {v : Compress} {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {R : BitVec 64}
  {EM : List Byte}

/-- `Post` for some result and `EM`, and the frame's words from `oI` on as in `t₀`. -/
def Weak (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (t₀ t : State) : Prop :=
  (∃ R EM, Post L g vv m₀ R EM t) ∧
    ∀ d, oI ≤ d → d + 8 ≤ frameBytes →
      t.mem.readW (L.Q + BitVec.ofNat 64 d) 64 = t₀.mem.readW (L.Q + BitVec.ofNat 64 d) 64

/-- What a call writing only in `scratch` keeps. -/
theorem Post.weak (hL : L.Ok) (hP : 16 ≤ L.P) {t u : State} (hc : Post L g vv m₀ R EM t) {ws : List Region}
    (h : After t ws u) (hs : ∀ r ∈ ws, Region.Sub r L.SC) : Weak L g vv m₀ t u :=
  ⟨⟨_, _, hc.after hL hP h hs⟩, fun _ _ hd => hc.slotKeep hL hP h hs hd⟩

/-! ## SHA-256's functions -/

theorem initA (hL : L.Ok) {t : State} (hc : Post L g vv m₀ R EM t) :
    Covers [⟨scA L sSt, (HH v).stream.S⟩] t.wr :=
  scCov hL hc.ctx (a := sSt) (n := 96) (Nat.le_of_ble_eq_true rfl)

theorem initW (hL : L.Ok) (hP : 16 ≤ L.P) {t : State} (hc : Post L g vv m₀ R EM t) (hx0 : t.gpr .x0 = scA L sSt) :
    WP isa (.call (HH v).initN (HH v).initC) t (Weak L g vv m₀ t) :=
  Proof.Pbkdf2.Md.AArch64.Calls.init_call (OK v).stream hx0 (initA hL hc) fun _ a _ =>
    hc.weak hL hP a fun r hr => by rw [List.mem_singleton.mp hr]; exact scSub (Nat.le_of_ble_eq_true rfl)

/-- The arguments of `update` of `n` bytes at `d`. -/
theorem updA (hL : L.Ok) (hP : 16 ≤ L.P) {t : State} (hc : Post L g vv m₀ R EM t) {d : Addr} {n : Nat}
    (hx0 : t.gpr .x0 = scA L sSt) (hx2 : t.gpr .x2 = d) (hx3 : (t.gpr .x3).toNat = n)
    (hx4 : t.gpr .x4 = scA L sWork) (hcd : Covers [⟨d, n⟩] (t.rd ++ t.wr))
    (hds : ∀ a l, a + l ≤ 1024 → Region.Disjoint ⟨d, n⟩ ⟨scA L a, l⟩) (hdk : (below L.Q 16).Disjoint ⟨d, n⟩) :
    Proof.Pbkdf2.Md.AArch64.Calls.UpdArgs (OK v).stream t (scA L sSt) d (scA L sWork) n where
  x0 := hx0
  x2 := hx2
  x3 := hx3
  x4 := hx4
  cd := hcd
  cw := Covers.pair (scCov hL hc.ctx (a := sSt) (n := 96) (by decide))
    (scCov hL hc.ctx (a := sWork) (n := 160) (by decide))
  st_sc := scD hL (a := sSt) (n := 96) (b := sWork) (m := 160) (.inl (by decide)) (by decide) (by decide)
  d_st := hds sSt 96 (by decide)
  d_sc := hds sWork 160 (by decide)
  sp16 := hc.sp16 hL hP
  stk_st := hc.stk hL hP (a := sSt) (m := 96) (by decide)
  stk_d := by rw [hc.ctx.sp]; exact hdk
  stk_sc := hc.stk hL hP (a := sWork) (m := 160) (by decide)

theorem updW (hL : L.Ok) (hP : 16 ≤ L.P) {t : State} (hc : Post L g vv m₀ R EM t) {d : Addr} {n : Nat}
    (a : Proof.Pbkdf2.Md.AArch64.Calls.UpdArgs (OK v).stream t (scA L sSt) d (scA L sWork) n) :
    WP isa (.call (HH v).updN (HH v).updC) t (Weak L g vv m₀ t) :=
  Proof.Pbkdf2.Md.AArch64.Calls.upd_call (OK v).stream a fun _ a' _ =>
    hc.weak hL hP a' fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact scSub (a := sSt) (n := 96) (by decide)
      · exact scSub (a := sWork) (n := 160) (by decide)

/-- The arguments of `finalize` to `scratch + o`. -/
theorem finA (hL : L.Ok) (hP : 16 ≤ L.P) {t : State} (hc : Post L g vv m₀ R EM t) {o : Nat}
    (ho1 : sWork + 160 ≤ o) (ho2 : o + 32 ≤ scrBytes) (hx0 : t.gpr .x0 = scA L sSt) (hx2 : t.gpr .x2 = scA L o)
    (hx3 : t.gpr .x3 = scA L sWork) :
    Proof.Pbkdf2.Md.AArch64.Calls.FinArgs (OK v).stream t (scA L sSt) (scA L o) (scA L sWork) where
  x0 := hx0
  x2 := hx2
  x3 := hx3
  cw := (scCov hL hc.ctx (a := sSt) (n := 96) (by decide)).cons
    ((scCov hL hc.ctx (a := o) (n := 32) ho2).cons ((scCov hL hc.ctx (a := sWork) (n := 160) (by decide)).cons
      Covers.nil))
  st_o := scD hL (a := sSt) (n := 96) (b := o) (m := 32) (.inl (by unfold sWork sSt at *; omega_using [ho1])) (by decide) ho2
  st_sc := scD hL (a := sSt) (n := 96) (b := sWork) (m := 160) (.inl (by decide)) (by decide) (by decide)
  o_sc := scD hL (a := o) (n := 32) (b := sWork) (m := 160) (.inr ho1) ho2 (by decide)
  sp16 := hc.sp16 hL hP
  stk_st := hc.stk hL hP (a := sSt) (m := 96) (by decide)
  stk_o := hc.stk hL hP (a := o) (m := 32) ho2
  stk_sc := hc.stk hL hP (a := sWork) (m := 160) (by decide)

/-! ## HMAC's functions -/

/-- The arguments of HMAC's `init` with the key at `scratch + key`. -/
theorem hinitA (hL : L.Ok) (hP : 16 ≤ L.P) {t : State} (hc : Post L g vv m₀ R EM t) {key : Nat}
    (hk1 : 1024 ≤ key) (hk2 : key + 32 ≤ scrBytes) (x0 : t.gpr .x0 = scA L sSt) (x1 : t.gpr .x1 = scA L sOuter)
    (x2 : t.gpr .x2 = scA L key) (x3 : t.gpr .x3 = BitVec.ofNat 64 32) (x4 : t.gpr .x4 = scA L sWork) :
    Proof.Pbkdf2.Md.AArch64.Pbk.InitArgs (H := HH v) t (scA L sSt) (scA L sOuter) (scA L key) (scA L sWork) 32 where
  x0 := x0
  x1 := x1
  x2 := x2
  x3 := by rw [x3]; rfl
  x4 := x4
  klB := Nat.le_of_ble_eq_true rfl
  cr := Covers.right (scCov hL hc.ctx (by omega_using [hk2]))
  cw := (scCov hL hc.ctx (a := sSt) (n := 96) (by decide)).cons
    ((scCov hL hc.ctx (a := sOuter) (n := 96) (by decide)).cons
      ((scCov hL hc.ctx (a := sWork) (n := 832) (by decide)).cons Covers.nil))
  i_o := scD hL (a := sSt) (n := 96) (b := sOuter) (m := 96) (.inl (by decide)) (by decide) (by decide)
  i_s := scD hL (a := sSt) (n := 96) (b := sWork) (m := 832) (.inl (by decide)) (by decide) (by decide)
  o_s := scD hL (a := sOuter) (n := 96) (b := sWork) (m := 832) (.inl (by decide)) (by decide) (by decide)
  k_i := scD hL (b := sSt) (m := 96) (.inr (by unfold sSt; omega_using [hk1])) hk2 (by decide)
  k_o := scD hL (b := sOuter) (m := 96) (.inr (by unfold sOuter; omega_using [hk1])) hk2 (by decide)
  k_s := scD hL (b := sWork) (m := 832) (.inr (by unfold sWork; omega_using [hk1])) hk2 (by decide)
  sp16 := hc.sp16 hL hP
  stk_i := hc.stk hL hP (a := sSt) (m := 96) (by decide)
  stk_o := hc.stk hL hP (a := sOuter) (m := 96) (by decide)
  stk_k := hc.stk hL hP hk2
  stk_s := hc.stk hL hP (a := sWork) (m := 832) (by decide)
  scnw := by
    show (scA L sWork).toNat + 832 ≤ 2 ^ 64
    rw [scA_toNat hL (by decide)]; have := hL.bS; have := hL.s8192; unfold sWork; omega_arith

theorem hinitW (hL : L.Ok) (hP : 16 ≤ L.P) {t : State} (hc : Post L g vv m₀ R EM t) {key : Nat}
    (a : Proof.Pbkdf2.Md.AArch64.Pbk.InitArgs (H := HH v) t (scA L sSt) (scA L sOuter) (scA L key) (scA L sWork) 32) :
    WP isa (.call (HH v).hmacInitN (HH v).hmacInit) t (Weak L g vv m₀ t) :=
  Proof.Pbkdf2.Md.AArch64.Pbk.hinit_call (OK v) (hI v) (hId v) a fun _ a' _ _ =>
    hc.weak hL hP a' fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact scSub (a := sSt) (n := 96) (by decide)
      · exact scSub (a := sOuter) (n := 96) (by decide)
      · exact scSub (a := sWork) (n := 832) (by decide)

/-- The arguments of HMAC's `finalize` to `scratch + o`, with the count in `x2`. -/
theorem hfinA (hL : L.Ok) (hP : 16 ≤ L.P) {t : State} (hc : Post L g vv m₀ R EM t) {o : Nat}
    (ho1 : 1024 ≤ o) (ho2 : o + 32 ≤ scrBytes) (x0 : t.gpr .x0 = scA L sSt) (x1 : t.gpr .x1 = scA L sOuter)
    (x3 : t.gpr .x3 = scA L o) (x4 : t.gpr .x4 = scA L sWork) :
    Proof.Pbkdf2.Md.AArch64.Pbk.FinArgs (H := HH v) t (scA L sSt) (scA L sOuter) (t.gpr .x2) (scA L o)
      (scA L sWork) where
  x0 := x0
  x1 := x1
  x2 := rfl
  x3 := x3
  x4 := x4
  cr := Covers.right (scCov hL hc.ctx (a := sOuter) (n := 96) (by decide))
  cw := (scCov hL hc.ctx (a := sSt) (n := 96) (by decide)).cons
    ((scCov hL hc.ctx (a := o) (n := 32) ho2).cons
      ((scCov hL hc.ctx (a := sWork) (n := 832) (by decide)).cons Covers.nil))
  i_u := scD hL (a := sSt) (n := 96) (b := sOuter) (m := 96) (.inl (by decide)) (by decide) (by decide)
  i_o := scD hL (a := sSt) (n := 96) (b := o) (m := 32) (.inl (by unfold sSt; omega_using [ho1])) (by decide) ho2
  i_s := scD hL (a := sSt) (n := 96) (b := sWork) (m := 832) (.inl (by decide)) (by decide) (by decide)
  u_o := scD hL (a := sOuter) (n := 96) (b := o) (m := 32) (.inl (by unfold sOuter; omega_using [ho1])) (by decide) ho2
  u_s := scD hL (a := sOuter) (n := 96) (b := sWork) (m := 832) (.inl (by decide)) (by decide) (by decide)
  o_s := scD hL (a := o) (n := 32) (b := sWork) (m := 832) (.inr (by unfold sWork; omega_using [ho1])) ho2 (by decide)
  sp16 := hc.sp16 hL hP
  stk_i := hc.stk hL hP (a := sSt) (m := 96) (by decide)
  stk_u := hc.stk hL hP (a := sOuter) (m := 96) (by decide)
  stk_o := hc.stk hL hP (a := o) (m := 32) ho2
  stk_s := hc.stk hL hP (a := sWork) (m := 832) (by decide)
  scnw := by
    show (scA L sWork).toNat + 832 ≤ 2 ^ 64
    rw [scA_toNat hL (by decide)]; have := hL.bS; have := hL.s8192; unfold sWork; omega_arith

theorem hfinW (hL : L.Ok) (hP : 16 ≤ L.P) {t : State} (hc : Post L g vv m₀ R EM t) {o : Nat} (ho2 : o + 32 ≤ scrBytes)
    {cnt : Addr}
    (a : Proof.Pbkdf2.Md.AArch64.Pbk.FinArgs (H := HH v) t (scA L sSt) (scA L sOuter) cnt (scA L o) (scA L sWork)) :
    WP isa (.call (HH v).hmacFinN (HH v).hmacFin) t (Weak L g vv m₀ t) :=
  Proof.Pbkdf2.Md.AArch64.Pbk.hfin_call (OK v) (hF v) (hFd v) a fun _ a' _ =>
    hc.weak hL hP a' fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact scSub (a := sSt) (n := 96) (by decide)
      · exact scSub (a := o) (n := 32) ho2
      · exact scSub (a := sWork) (n := 832) (by decide)

end VG.Proof.RsaPkcs1Enc.AArch64.Dec

end

end

/-!
# RSAES-PKCS1-v1_5 decryption on AArch64: constant time, `DH` and `KDK`

Inside the pieces that call SHA-256's and HMAC's functions, two runs in a
layout are related by `PW`: each keeps `Post` (for some result and `EM`) and
satisfies `X`, which fixes the registers the next piece's addresses and
arguments depend on as functions of the layout. Each block is checked by the
taint analysis (`pw_blk`) and each call is the same call in both runs
(`Calls.init_rel` …): `hashD_ct`, `kdkMac_ct`.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Decrypt
open VG.Proof.Sha256.AArch64 (Compress)

variable {v : Compress}

/-- Two runs in the layout of `e`, each with `Post` and `X`. -/
def PW (S : Nat) (e : Env) (X : State → Prop) (a b : State) : Prop :=
  e.L.Ok ∧ e.L.P = S + 1 ∧ (∃ R EM, Post e.L e.g₁ e.v₁ e.m₁ R EM a) ∧ (∃ R EM, Post e.L e.g₂ e.v₂ e.m₂ R EM b) ∧
    X a ∧ X b

/-- What a piece keeps of `Post`, and establishes. -/
abbrev PWStep (S : Nat) (e : Env) (c : Prog isa) (X X' : State → Prop) : Prop :=
  ∀ g vv m₀ R EM (t : State), e.L.Ok → e.L.P = S + 1 → Post e.L g vv m₀ R EM t → X t →
    WP isa c t fun u => (∃ R EM, Post e.L g vv m₀ R EM u) ∧ X' u

theorem pw_wp {S : Nat} {e : Env} {c : Prog isa} {X X' : State → Prop}
    (hct : RelCT isa (PW S e X) c fun _ _ => True) (hw : PWStep S e c X X') : RelCT isa (PW S e X) c (PW S e X') := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨hL, hP, ⟨R₁, E₁, f₁⟩, ⟨R₂, E₂, f₂⟩, x₁, x₂⟩ := hp
  obtain ⟨_, u₁, y₁, z₁⟩ := hw _ _ _ _ _ s₁ hL hP f₁ x₁
  obtain ⟨_, u₂, y₂, z₂⟩ := hw _ _ _ _ _ s₂ hL hP f₂ x₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ y₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ y₂
  exact ⟨ht, hL, hP, z₁.1, z₂.1, z₁.2, z₂.2⟩

/-- A block checked by the taint analysis from the registers `rs`, which `X` fixes. -/
theorem pw_blk {S : Nat} {e : Env} {c : Prog isa} {X X' : State → Prop} (rs : List Reg)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T} (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true)
    (hag : ∀ a b, X a → X b → ∀ r ∈ rs, a.gpr r = b.gpr r) (hw : PWStep S e c X X') :
    RelCT isa (PW S e X) c (PW S e X') :=
  pw_wp (RelCT.taint (A := taint) (Taint.ofRegs rs) (fun _ _ ⟨_, _, ⟨_, _, f₁⟩, ⟨_, _, f₂⟩, x₁, x₂⟩ =>
    ⟨f₁.ctx.sp.trans f₂.ctx.sp.symm, fun r hr => hag _ _ x₁ x₂ r (Taint.mem_ofRegs.mp hr)⟩) h) hw

/-! ## `DH = SHA256(D)` -/

/-- The registers `shaUpdArgs` sets. -/
def XU (L : Lay) (t : State) : Prop :=
  t.gpr .x0 = scA L sSt ∧ t.gpr .x1 = 0 ∧ t.gpr .x2 = scA L sD ∧ t.gpr .x3 = L.k ∧ t.gpr .x4 = scA L sWork

/-- The registers `shaFinArgs` sets. -/
def XF (L : Lay) (t : State) : Prop :=
  t.gpr .x0 = scA L sSt ∧ t.gpr .x1 = L.k ∧ t.gpr .x2 = scA L sDH ∧ t.gpr .x3 = scA L sWork

theorem hashD_tr {S : Nat} (hS : 15 ≤ S) (e : Env) :
    RelCT isa (PW S e fun _ => True) (hashD (HH v)) fun _ _ => True := by
  refine (pw_blk (X' := fun t => t.gpr .x0 = scA e.L sSt) [] (by taint_decide)
    (fun _ _ _ _ _ h => absurd h List.not_mem_nil) fun g vv m₀ R EM t hL _ hc _ =>
      WP.mono (shaInitArgs_ok hc.ctx.sp hc.slots) fun u ⟨hs, x0⟩ =>
        ⟨⟨R, EM, hc.same hs⟩, by show u.gpr .x0 = _; simp only [x0, hc.ctx.kept.scr]⟩).seq ?_
  refine (pw_wp (X' := fun _ => True)
    (Proof.Pbkdf2.Md.AArch64.Calls.init_rel (OK v).stream (st := scA e.L sSt)
      fun a b h => by
        obtain ⟨hL, _, ⟨_, _, ha⟩, ⟨_, _, hb⟩, xa, xb⟩ := h
        exact ⟨xa, xb, initA hL ha, initA hL hb, ha.ctx.sp.trans hb.ctx.sp.symm⟩)
    fun g vv m₀ R EM t hL hP hc hx => WP.mono (initW (v := v) hL (by omega_using [hS, hP]) hc hx) fun u hu => ⟨hu.1, trivial⟩).seq ?_
  refine (pw_blk (X' := XU e.L) [] (by taint_decide) (fun _ _ _ _ _ h => absurd h List.not_mem_nil)
    fun g vv m₀ R EM t hL _ hc _ => WP.mono (shaUpdArgs_ok hc.ctx.sp hc.slots) fun u ⟨hs, x0, x1, x2, x3, x4⟩ =>
      ⟨⟨R, EM, hc.same hs⟩, by simp only [x0, hc.ctx.kept.scr], x1, by simp only [x2, hc.ctx.kept.scr],
        by simp only [x3, hc.ctx.kept.k], by simp only [x4, hc.ctx.kept.scr]⟩).seq ?_
  have hk := fun (hL : e.L.Ok) => hL.k1024
  have upA : ∀ (hL : e.L.Ok) (hP : 16 ≤ e.L.P) {g vv m₀ R EM} {t : State}, Post e.L g vv m₀ R EM t → XU e.L t →
      Proof.Pbkdf2.Md.AArch64.Calls.UpdArgs (OK v).stream t (scA e.L sSt) (scA e.L sD) (scA e.L sWork) e.L.k.toNat :=
    fun hL hP {_ _ _ _ _ _} hc ⟨x0, _, x2, x3, x4⟩ => updA hL hP hc x0 x2 (by rw [x3]) x4
      (Covers.right (scCov hL hc.ctx (by have := hL.k1024; unfold sD scrBytes; omega_using [this])))
      (fun a l hal => scD hL (.inr (by unfold sD; omega_using [hal])) (by have := hL.k1024; unfold sD scrBytes; omega_using [this])
        (by unfold scrBytes; omega_using [hal]))
      (stkD hL hP (by have := hL.k1024; unfold sD scrBytes; omega_using [this]))
  refine (pw_wp (X' := fun _ => True)
    (Proof.Pbkdf2.Md.AArch64.Calls.upd_rel (OK v).stream fun a b h => by
      obtain ⟨hL, hP, ⟨_, _, ha⟩, ⟨_, _, hb⟩, xa, xb⟩ := h
      exact ⟨upA hL (by omega_using [hS, hP]) ha xa, upA hL (by omega_using [hS, hP]) hb xb, xa.2.1.trans xb.2.1.symm,
        ha.ctx.sp.trans hb.ctx.sp.symm⟩)
    fun g vv m₀ R EM t hL hP hc hx => WP.mono (updW (v := v) hL (by omega_using [hS, hP]) hc (upA hL (by omega_using [hS, hP]) hc hx))
      fun u hu => ⟨hu.1, trivial⟩).seq ?_
  refine (pw_blk (X' := XF e.L) [] (by taint_decide) (fun _ _ _ _ _ h => absurd h List.not_mem_nil)
    fun g vv m₀ R EM t hL _ hc _ => WP.mono (shaFinArgs_ok hc.ctx.sp hc.slots) fun u ⟨hs, x0, x1, x2, x3⟩ =>
      ⟨⟨R, EM, hc.same hs⟩, by simp only [x0, hc.ctx.kept.scr], by simp only [x1, hc.ctx.kept.k],
        by simp only [x2, hc.ctx.kept.scr], by simp only [x3, hc.ctx.kept.scr]⟩).seq ?_
  exact Proof.Pbkdf2.Md.AArch64.Calls.fin_rel (OK v).stream fun a b h => by
    obtain ⟨hL, hP, ⟨_, _, ha⟩, ⟨_, _, hb⟩, ⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩⟩ := h
    exact ⟨finA (o := sDH) hL (by omega_using [hS, hP]) ha (by decide) (by decide) a0 a2 a3,
      finA (o := sDH) hL (by omega_using [hS, hP]) hb (by decide) (by decide) b0 b2 b3, a1.trans b1.symm,
      ha.ctx.sp.trans hb.ctx.sp.symm⟩

/-! ## HMAC's pieces

`G` is a fact about the frame's words from `oI` on (the counters), which no
piece changes. -/

/-- `G` holds of states with the same frame words from `oI` on. -/
def SlotsPred (L : Lay) (G : State → Prop) : Prop :=
  ∀ t u : State, G t → (∀ d, oI ≤ d → d + 8 ≤ frameBytes →
    u.mem.readW (L.Q + BitVec.ofNat 64 d) 64 = t.mem.readW (L.Q + BitVec.ofNat 64 d) 64) → G u

/-- The registers `macInitArgs key` sets. -/
def XI (key : Nat) (L : Lay) (t : State) : Prop :=
  t.gpr .x0 = scA L sSt ∧ t.gpr .x1 = scA L sOuter ∧ t.gpr .x2 = scA L key ∧ t.gpr .x3 = BitVec.ofNat 64 32 ∧
    t.gpr .x4 = scA L sWork

theorem macArgs_pw {S : Nat} {e : Env} {G : State → Prop} (hG : SlotsPred e.L G) (key : Nat) (hk : key < 4096)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (h : (taint.check (Taint.ofRegs []) (.block (macInitArgs key)) hc).isSome = true) :
    RelCT isa (PW S e G) (.block (macInitArgs key)) (PW S e fun t => G t ∧ XI key e.L t) :=
  pw_blk [] h (fun _ _ _ _ _ h => absurd h List.not_mem_nil) fun g vv m₀ R EM t _ _ hc hx =>
    WP.mono (macInitArgs_ok hc.ctx.sp hc.slots key hk) fun u ⟨hs, x0, x1, x2, x3, x4⟩ =>
      ⟨⟨R, EM, hc.same hs⟩, hG t u hx fun _ _ _ => by rw [hs.mem], by simp only [x0, hc.ctx.kept.scr],
        by simp only [x1, hc.ctx.kept.scr], by simp only [x2, hc.ctx.kept.scr], x3,
        by simp only [x4, hc.ctx.kept.scr]⟩

theorem hinit_pw {S : Nat} (hS : 15 ≤ S) {e : Env} {G : State → Prop} (hG : SlotsPred e.L G) {key : Nat}
    (hk1 : 1024 ≤ key) (hk2 : key + 32 ≤ scrBytes) :
    RelCT isa (PW S e fun t => G t ∧ XI key e.L t) (.call (HH v).hmacInitN (HH v).hmacInit) (PW S e G) :=
  pw_wp (Proof.Pbkdf2.Md.AArch64.Pbk.hinit_rel (OK v) (hI v) fun a b h => by
      obtain ⟨hL, hP, ⟨_, _, ha⟩, ⟨_, _, hb⟩, ⟨_, a0, a1, a2, a3, a4⟩, ⟨_, b0, b1, b2, b3, b4⟩⟩ := h
      exact ⟨hinitA hL (by omega_using [hS, hP]) ha hk1 hk2 a0 a1 a2 a3 a4, hinitA hL (by omega_using [hS, hP]) hb hk1 hk2 b0 b1 b2 b3 b4,
        ha.ctx.sp.trans hb.ctx.sp.symm⟩)
    fun g vv m₀ R EM t hL hP hc ⟨hx, x0, x1, x2, x3, x4⟩ =>
      WP.mono (hinitW (v := v) hL (by omega_using [hS, hP]) hc (hinitA hL (by omega_using [hS, hP]) hc hk1 hk2 x0 x1 x2 x3 x4)) fun u hu =>
        ⟨hu.1, hG t u hx hu.2⟩

/-- The registers before `update` of `n` bytes at `d`. -/
def XUp (d : Addr) (n : Nat) (L : Lay) (t : State) : Prop :=
  t.gpr .x0 = scA L sSt ∧ t.gpr .x1 = BitVec.ofNat 64 64 ∧ t.gpr .x2 = d ∧ (t.gpr .x3).toNat = n ∧
    t.gpr .x4 = scA L sWork

theorem upd_pw {S : Nat} (hS : 15 ≤ S) {e : Env} {G : State → Prop} (hG : SlotsPred e.L G) {d : Addr} {n : Nat}
    (hcd : e.L.Ok → ∀ g vv m₀ R EM (t : State), Post e.L g vv m₀ R EM t → Covers [⟨d, n⟩] (t.rd ++ t.wr))
    (hds : e.L.Ok → ∀ a l, a + l ≤ 1024 → Region.Disjoint ⟨d, n⟩ ⟨scA e.L a, l⟩)
    (hdk : e.L.Ok → e.L.P = S + 1 → (below e.L.Q 16).Disjoint ⟨d, n⟩) :
    RelCT isa (PW S e fun t => G t ∧ XUp d n e.L t) (.call (HH v).updN (HH v).updC) (PW S e G) :=
  pw_wp (Proof.Pbkdf2.Md.AArch64.Calls.upd_rel (OK v).stream fun a b h => by
      obtain ⟨hL, hP, ⟨_, _, ha⟩, ⟨_, _, hb⟩, ⟨_, a0, a1, a2, a3, a4⟩, ⟨_, b0, b1, b2, b3, b4⟩⟩ := h
      exact ⟨updA hL (by omega_using [hS, hP]) ha a0 a2 a3 a4 (hcd hL _ _ _ _ _ _ ha) (hds hL) (hdk hL hP),
        updA hL (by omega_using [hS, hP]) hb b0 b2 b3 b4 (hcd hL _ _ _ _ _ _ hb) (hds hL) (hdk hL hP), a1.trans b1.symm,
        ha.ctx.sp.trans hb.ctx.sp.symm⟩)
    fun g vv m₀ R EM t hL hP hc ⟨hx, x0, _, x2, x3, x4⟩ =>
      WP.mono (updW (v := v) hL (by omega_using [hS, hP]) hc (updA hL (by omega_using [hS, hP]) hc x0 x2 x3 x4 (hcd hL _ _ _ _ _ _ hc) (hds hL)
        (hdk hL hP))) fun u hu => ⟨hu.1, hG t u hx hu.2⟩

/-- The registers before HMAC's `finalize` to `scratch + o` with the count `cnt`. -/
def XHF (o : Nat) (cnt : BitVec 64) (L : Lay) (t : State) : Prop :=
  t.gpr .x0 = scA L sSt ∧ t.gpr .x1 = scA L sOuter ∧ t.gpr .x2 = cnt ∧ t.gpr .x3 = scA L o ∧
    t.gpr .x4 = scA L sWork

theorem hfin_pw {S : Nat} (hS : 15 ≤ S) {e : Env} {G : State → Prop} (hG : SlotsPred e.L G) {o : Nat}
    {cnt : BitVec 64} (ho1 : 1024 ≤ o) (ho2 : o + 32 ≤ scrBytes) :
    RelCT isa (PW S e fun t => G t ∧ XHF o cnt e.L t) (.call (HH v).hmacFinN (HH v).hmacFin) (PW S e G) :=
  pw_wp (Proof.Pbkdf2.Md.AArch64.Pbk.hfin_rel (OK v) (hF v) (cnt := cnt) fun a b h => by
      obtain ⟨hL, hP, ⟨_, _, ha⟩, ⟨_, _, hb⟩, ⟨_, a0, a1, a2, a3, a4⟩, ⟨_, b0, b1, b2, b3, b4⟩⟩ := h
      exact ⟨a2 ▸ hfinA hL (by omega_using [hS, hP]) ha ho1 ho2 a0 a1 a3 a4, b2 ▸ hfinA hL (by omega_using [hS, hP]) hb ho1 ho2 b0 b1 b3 b4,
        ha.ctx.sp.trans hb.ctx.sp.symm⟩)
    fun g vv m₀ R EM t hL hP hc ⟨hx, x0, x1, _, x3, x4⟩ =>
      WP.mono (hfinW (v := v) hL (by omega_using [hS, hP]) hc ho2 (hfinA hL (by omega_using [hS, hP]) hc ho1 ho2 x0 x1 x3 x4)) fun u hu =>
        ⟨hu.1, hG t u hx hu.2⟩

/-! ## `KDK` -/

theorem kdkMac_tr {S : Nat} (hS : 15 ≤ S) (e : Env) :
    RelCT isa (PW S e fun _ => True) (kdkMac (HH v)) fun _ _ => True := by
  have hG : SlotsPred e.L fun _ => True := fun _ _ _ _ => trivial
  refine (macArgs_pw hG sDH (by decide) (by taint_decide)).seq (((hinit_pw (v := v) hS hG (key := sDH) (by decide)
    (by decide)).mono (fun _ _ h => by
      obtain ⟨hL, hP, a, b, ⟨_, xa⟩, ⟨_, xb⟩⟩ := h
      exact ⟨hL, hP, a, b, ⟨trivial, xa⟩, ⟨trivial, xb⟩⟩) fun _ _ h => h).seq ?_)
  refine ((pw_blk (X' := fun t => True ∧ XUp e.L.inp e.L.k.toNat e.L t) [] (by taint_decide)
    (fun _ _ _ _ _ h => absurd h List.not_mem_nil) fun g vv m₀ R EM t _ _ hc _ =>
      WP.mono (kdkUpdArgs_ok hc.ctx.sp hc.slots) fun u ⟨hs, x0, x1, x2, x3, x4⟩ =>
        ⟨⟨R, EM, hc.same hs⟩, trivial, by simp only [x0, hc.ctx.kept.scr], x1, by simp only [x2, hc.ctx.kept.inp],
          by simp only [x3, hc.ctx.kept.k], by simp only [x4, hc.ctx.kept.scr]⟩)).seq ?_
  refine ((upd_pw (v := v) hS hG
    (fun _ _ _ _ _ _ _ hc => Covers.left (Covers.of_mem fun r hr => by
      rw [List.mem_singleton.mp hr, hc.ctx.rd]; simp))
    (fun hL a l hal => (hL.sR _ (ro_INP e.L)).symm.sub_right (sub_trans (scSub (by unfold scrBytes; omega_using [hal]))
      hL.sc_sub))
    (fun hL hP => (hL.kR _ (ro_INP e.L)).sub_left (below_low hL (by omega_using [hS, hP])))).seq ?_)
  refine ((pw_blk (X' := fun t => True ∧ XHF sKDK (e.L.k + BitVec.ofNat 64 64) e.L t) [] (by taint_decide)
    (fun _ _ _ _ _ h => absurd h List.not_mem_nil) fun g vv m₀ R EM t _ _ hc _ =>
      WP.mono (kdkFinArgs_ok hc.ctx.sp hc.slots) fun u ⟨hs, x0, x1, x2, x3, x4⟩ =>
        ⟨⟨R, EM, hc.same hs⟩, trivial, by simp only [x0, hc.ctx.kept.scr], by simp only [x1, hc.ctx.kept.scr],
          by simp only [x2, hc.ctx.kept.k], by simp only [x3, hc.ctx.kept.scr],
          by simp only [x4, hc.ctx.kept.scr]⟩)).seq ?_
  exact (hfin_pw (v := v) hS hG (o := sKDK) (by decide) (by decide)).mono (fun _ _ h => h) fun _ _ _ => trivial

/-! ## The pieces -/

theorem hashD_ct {S : Nat} (hS : 15 ≤ S) :
    RelCT isa (Two S fun L g vv m₀ t => ∃ R EM, DB L g vv m₀ R EM t) (hashD (HH v))
      (Two S fun L g vv m₀ t => ∃ R EM, HD L g vv m₀ R EM t) :=
  two_wp (fun e => (hashD_tr hS e).mono (fun _ _ ⟨hL, hP, _, ⟨_, _, f₁⟩, ⟨_, _, f₂⟩⟩ =>
      ⟨hL, hP, ⟨_, _, f₁.post⟩, ⟨_, _, f₂.post⟩, trivial, trivial⟩) fun _ _ h => h)
    fun _ _ _ _ _ hL hP ⟨_, _, h⟩ => WP.mono (hashD_ok hL (by omega_using [hS, hP]) h) fun _ h' => ⟨_, _, h'⟩

theorem kdkMac_ct {S : Nat} (hS : 15 ≤ S) :
    RelCT isa (Two S fun L g vv m₀ t => ∃ R EM, HD L g vv m₀ R EM t) (kdkMac (HH v))
      (Two S fun L g vv m₀ t => ∃ R EM, KD L g vv m₀ R EM t) :=
  two_wp (fun e => (kdkMac_tr hS e).mono (fun _ _ ⟨hL, hP, _, ⟨_, _, f₁⟩, ⟨_, _, f₂⟩⟩ =>
      ⟨hL, hP, ⟨_, _, f₁.post⟩, ⟨_, _, f₂.post⟩, trivial, trivial⟩) fun _ _ h => h)
    fun _ _ _ _ _ hL hP ⟨_, _, h⟩ => WP.mono (kdkMac_ok hL (by omega_using [hS, hP]) h) fun _ h' => ⟨_, _, h'⟩

end VG.Proof.RsaPkcs1Enc.AArch64.Dec

end

end

/-!
# RSAES-PKCS1-v1_5 decryption on AArch64: constant time, `CL` and `AM`

A block of IRPRF (`prfBody_tr`) from two runs with the same counter, whose
slot fixes the block's address, and the loops of blocks (`prfLoop_tr`),
whose counters agree: `clLoop_ct`, `amLoop_ct`.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Decrypt
open VG.Proof.Sha256.AArch64 (Compress)

variable {v : Compress}

/-- A loop counting down in `cr` from `n`, whose runs agree on `P k` after `k` iterations. -/
theorem count_ct {body : Prog isa} {cr : Reg} {n : Nat} (hn : 0 < n) (P : Nat → State → State → Prop)
    (hstep : ∀ k < n, RelCT isa (P k) body fun a b =>
      P (k + 1) a b ∧ (a.gpr cr != 0) = decide (k + 1 ≠ n) ∧ (b.gpr cr != 0) = decide (k + 1 ≠ n)) :
    RelCT isa (P 0) (.loop body (.nonzero .x cr)) (P n) := by
  refine (RelCT.loop (fun m a b => ∃ k, k < n ∧ m = n - k ∧ P k a b) (fun m => RelCT.exists_ fun k => ?_) n).mono
    (fun a b h => ⟨0, hn, rfl, h⟩) fun _ _ h => h
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨hk, hm, hp⟩ e₁ e₂
  obtain ⟨ht, hq, c₁, c₂⟩ := hstep k hk _ _ _ _ _ _ hp e₁ e₂
  refine ⟨ht, by rw [Bytes.eval_nonzero, Bytes.eval_nonzero, c₁, c₂], fun h => ?_, fun h => ?_⟩
  · rw [Bytes.eval_nonzero, c₁] at h
    have : k + 1 = n := by simpa using h
    exact this ▸ hq
  · rw [Bytes.eval_nonzero, c₁] at h
    have : k + 1 ≠ n := by simpa using h
    exact ⟨n - (k + 1), by omega_arith, k + 1, by omega_arith, rfl, hq⟩

/-- The counter `i` and the number of blocks `nbv` in their slots. -/
def Ctr (L : Lay) (i : Nat) (nbv : BitVec 64) (t : State) : Prop :=
  slot t L.Q oI = BitVec.ofNat 64 i ∧ slot t L.Q oNB = nbv

theorem ctr_slots (L : Lay) (i : Nat) (nbv : BitVec 64) : SlotsPred L (Ctr L i nbv) := fun _ _ ⟨a, b⟩ h =>
  ⟨(h oI (Nat.le_refl _) (by decide)).trans a, (h oNB (by decide) (by decide)).trans b⟩

/-- The registers `prfHead` sets. -/
def XH (L : Lay) (i : Nat) (t : State) : Prop :=
  t.gpr .x9 = scA L sMsg ∧ t.gpr .x11 = BitVec.ofNat 64 i ∧ t.gpr .x12 = L.k

theorem prfBody_tr {S : Nat} (hS : 15 ≤ S) (e : Env) {label : List Nat} {len count : List Instr} {dst i : Nat}
    {nbv C : BitVec 64} (hi : i < 256) (hd1 : 1040 ≤ dst) (hd2 : dst + 32 * i + 32 ≤ scrBytes) (hdst : dst < 4096)
    (hn : label.length + 4 ≤ 16) {h₁ h₂ h₃ h₄ : VG.Taint.Hint VG.AArch64.Taint.T}
    (tm : (taint.check (Taint.ofRegs [.x9]) (.block (msgBytes label len)) h₁).isSome = true)
    (tu : (taint.check (Taint.ofRegs []) (.block (prfUpdArgs (label.length + 4))) h₂).isSome = true)
    (tf : (taint.check (Taint.ofRegs []) (.block (prfFinArgs (label.length + 4) dst)) h₃).isSome = true)
    (tc : (taint.check (Taint.ofRegs []) (.block (incr count)) h₄).isSome = true)
    (hmsg : e.L.Ok → ∀ g vv m₀ R EM (u : State), Post e.L g vv m₀ R EM u → XH e.L i u →
      WP isa (.block (msgBytes label len)) u fun w => SameR u w ∧ Frame [⟨scA e.L sMsg, 16⟩] u.mem w.mem)
    (hcount : ∀ g vv m₀ R EM (u : State), Post e.L g vv m₀ R EM u → slot u e.L.Q oNB = nbv →
      WP isa (.block (incr count)) u fun w => SameR u w ∧
        w.mem = u.mem.writeW (e.L.Q + BitVec.ofNat 64 oI) (slot u e.L.Q oI + 1) ∧
        w.gpr .x12 = C - (slot u e.L.Q oI + 1)) :
    RelCT isa (PW S e (Ctr e.L i nbv)) (prfBody (HH v) label len dst count)
      (PW S e fun t => Ctr e.L (i + 1) nbv t ∧ t.gpr .x12 = C - BitVec.ofNat 64 (i + 1)) := by
  have hG := ctr_slots e.L i nbv
  have nil : ∀ {X : State → Prop} (a b : State), X a → X b → ∀ r ∈ ([] : List Reg), a.gpr r = b.gpr r :=
    fun _ _ _ _ _ h => absurd h List.not_mem_nil
  -- The message.
  refine (pw_blk (X' := fun t => Ctr e.L i nbv t ∧ XH e.L i t) [] (by taint_decide) nil
    fun g vv m₀ R EM t _ _ hc hx => WP.mono (prfHead_ok hc.ctx.sp hc.slots) fun u ⟨hs, x9, x11, x12⟩ =>
      ⟨⟨R, EM, hc.same hs⟩, hG t u hx fun _ _ _ => by rw [hs.mem], by simp only [x9, hc.ctx.kept.scr],
        by rw [x11, hx.1], by simp only [x12, hc.ctx.kept.k]⟩).seq ?_
  refine (pw_blk (X' := Ctr e.L i nbv) [.x9] tm (fun a b xa xb r hr => by
      rw [List.mem_singleton.mp hr]; exact xa.2.1.trans xb.2.1.symm)
    fun g vv m₀ R EM t hL _ hc ⟨hx, xh⟩ => WP.mono (hmsg hL _ _ _ _ _ t hc xh) fun w ⟨R₂, F₂⟩ =>
      ⟨⟨R, EM, hc.step hL R₂.rd R₂.wr R₂.sp (fun r _ => by rw [R₂.v]) (fun r hr _ => R₂.cs r hr) F₂
        fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (scSub (by decide))⟩,
      hG t w hx fun d _ hd => F₂.readW (Region.contains_self _ _) (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact hL.stk_buf (by unfold frameBytes at hd; omega_arith) (.inr (.inr (sub_trans (scSub (by decide))
          hL.sc_sub)))) (by decide)⟩).seq ?_
  -- HMAC's `init` with `KDK`.
  refine (macArgs_pw hG sKDK (by decide) (by taint_decide)).seq ((hinit_pw (v := v) hS hG (key := sKDK)
    (by decide) (by decide)).seq ?_)
  -- `update` with the message.
  refine (pw_blk (X' := fun t => Ctr e.L i nbv t ∧ XUp (scA e.L sMsg) (label.length + 4) e.L t) [] tu nil
    fun g vv m₀ R EM t _ _ hc hx => WP.mono (prfUpdArgs_ok hc.ctx.sp hc.slots (n := label.length + 4)
      (by omega_arith)) fun u ⟨hs, y0, y1, y2, y3, y4⟩ =>
      ⟨⟨R, EM, hc.same hs⟩, hG t u hx fun _ _ _ => by rw [hs.mem], by simp only [y0, hc.ctx.kept.scr], y1,
        by simp only [y2, hc.ctx.kept.scr], by rw [y3, BitVec.toNat_ofNat]; omega_arith,
        by simp only [y4, hc.ctx.kept.scr]⟩).seq ?_
  refine (upd_pw (v := v) hS hG (fun hL _ _ _ _ _ _ hc => Covers.right (scCov hL hc.ctx (by unfold sMsg scrBytes; omega_arith)))
    (fun hL a l hal => scD hL (.inr (by unfold sMsg; omega_arith)) (by unfold sMsg scrBytes; omega_arith)
      (by unfold scrBytes; omega_arith))
    (fun hL hP => stkD hL (by omega_arith) (by unfold sMsg scrBytes; omega_arith))).seq ?_
  -- HMAC's `finalize` to the block.
  refine (pw_blk (X' := fun t => Ctr e.L i nbv t ∧
      XHF (dst + 32 * i) (BitVec.ofNat 64 (64 + (label.length + 4))) e.L t) [] tf nil
    fun g vv m₀ R EM t _ _ hc hx => WP.mono (prfFinArgs_ok hc.ctx.sp hc.slots (n := label.length + 4)
      (dst := dst) (by omega_arith) hdst) fun u ⟨hs, z0, z1, z2, z3, z4⟩ =>
      ⟨⟨R, EM, hc.same hs⟩, hG t u hx fun _ _ _ => by rw [hs.mem], by simp only [z0, hc.ctx.kept.scr],
        by simp only [z1, hc.ctx.kept.scr], z2, by simp only [z3, hx.1, hc.ctx.kept.scr]; exact shl5 i dst _,
        by simp only [z4, hc.ctx.kept.scr]⟩).seq ?_
  refine (hfin_pw (v := v) hS hG (o := dst + 32 * i) (by omega_arith) (by omega_arith)).seq ?_
  -- The counter.
  refine pw_blk [] tc nil fun g vv m₀ R EM t hL _ hc hx => WP.mono (hcount _ _ _ _ _ t hc hx.2)
    fun w ⟨Sw, mw, xw⟩ => ?_
  have hnQ := hL.nQ
  have Fw : Frame [⟨e.L.Q + BitVec.ofNat 64 oI, 8⟩] t.mem w.mem := by
    rw [mw]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have one : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) := by
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add]
  refine ⟨⟨R, EM, hc.step hL Sw.rd Sw.wr Sw.sp (fun r _ => by rw [Sw.v]) (fun r hr _ => Sw.cs r hr) Fw
    fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inr (.inr ⟨oI, Nat.le_refl _, by show oI + 8 ≤ frameBytes; decide, rfl⟩)⟩,
    ⟨?_, ?_⟩, by rw [xw, hx.1, one]⟩
  · show w.mem.readW _ 64 = _
    rw [mw, Mem.readW_writeW_self64, hx.1, one]
  · show w.mem.readW _ 64 = _
    rw [mw, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide)]
    exact hx.2

theorem prfLoop_tr {S : Nat} (hS : 15 ≤ S) (e : Env) {label : List Nat} {len count : List Instr} {dst N : Nat}
    {nbv C : BitVec 64} (hN0 : 0 < N) (hN : N ≤ 256) (hd1 : 1040 ≤ dst) (hd2 : dst + 32 * N ≤ scrBytes)
    (hdst : dst < 4096) (hn : label.length + 4 ≤ 16) {h₁ h₂ h₃ h₄ : VG.Taint.Hint VG.AArch64.Taint.T}
    (tm : (taint.check (Taint.ofRegs [.x9]) (.block (msgBytes label len)) h₁).isSome = true)
    (tu : (taint.check (Taint.ofRegs []) (.block (prfUpdArgs (label.length + 4))) h₂).isSome = true)
    (tf : (taint.check (Taint.ofRegs []) (.block (prfFinArgs (label.length + 4) dst)) h₃).isSome = true)
    (tc : (taint.check (Taint.ofRegs []) (.block (incr count)) h₄).isSome = true)
    (hC : ∀ i < N, C - BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 (N - (i + 1)))
    (hmsg : ∀ i < N, e.L.Ok → ∀ g vv m₀ R EM (u : State), Post e.L g vv m₀ R EM u → XH e.L i u →
      WP isa (.block (msgBytes label len)) u fun w => SameR u w ∧ Frame [⟨scA e.L sMsg, 16⟩] u.mem w.mem)
    (hcount : ∀ g vv m₀ R EM (u : State), Post e.L g vv m₀ R EM u → slot u e.L.Q oNB = nbv →
      WP isa (.block (incr count)) u fun w => SameR u w ∧
        w.mem = u.mem.writeW (e.L.Q + BitVec.ofNat 64 oI) (slot u e.L.Q oI + 1) ∧
        w.gpr .x12 = C - (slot u e.L.Q oI + 1)) :
    RelCT isa (PW S e (Ctr e.L 0 nbv)) (.loop (prfBody (HH v) label len dst count) (.nonzero .x .x12))
      fun _ _ => True :=
  (count_ct hN0 (fun i => PW S e (Ctr e.L i nbv)) fun i hi =>
    (prfBody_tr (v := v) hS e (i := i) (C := C) (by omega_arith) (by omega_arith) (by omega_arith) hdst hn tm tu tf tc (hmsg i hi)
      hcount).mono (fun _ _ h => h) fun _ _ ⟨hL, hP, pa, pb, ⟨ca, xa⟩, ⟨cb, xb⟩⟩ =>
      ⟨⟨hL, hP, pa, pb, ca, cb⟩, by rw [xa, hC i hi]; exact Bytes.counter_ne hi (by omega_arith),
        by rw [xb, hC i hi]; exact Bytes.counter_ne hi (by omega_arith)⟩).mono (fun _ _ h => h) fun _ _ _ => trivial

/-! ## The loops -/

theorem clLoop_tr {S : Nat} (hS : 15 ≤ S) (e : Env) :
    RelCT isa (PW S e fun _ => True) (clLoop (HH v)) fun _ _ => True :=
  (pw_blk (X' := Ctr e.L 0 (BitVec.ofNat 64 ((e.L.k.toNat + 31) / 32))) [] (by taint_decide)
    (fun _ _ _ _ _ h => absurd h List.not_mem_nil) fun _ _ _ R EM t hL _ hc _ =>
      WP.mono (clStart_ok hL hc) fun _ ⟨hc₁, ct₁, nb₁, _⟩ => ⟨⟨R, EM, hc₁⟩, ct₁, nb₁⟩).seq
  (prfLoop_tr (v := v) hS e (N := 8) (C := BitVec.ofNat 64 8) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)
    (fun i hi => Offset.ofNat_sub_ofNat (by omega_arith))
    (fun i hi hL _ _ _ _ _ u hu ⟨x9, x11, _⟩ => WP.mono (msgCL_ok x9 x11 (by omega_arith) (hu.msgW hL))
      fun _ ⟨a, b, c, d, e, f, _⟩ => ⟨⟨a, b, c, d, e⟩, f⟩)
    fun _ _ _ _ _ u hu _ => WP.mono (incrCL_ok hu.ctx.sp hu.slots (hu.ctx.inFr (d := 200) (by decide)))
      fun _ hw => hw)

theorem amLoop_tr {S : Nat} (hS : 15 ≤ S) (e : Env) :
    RelCT isa (PW S e fun t => slot t e.L.Q oNB = BitVec.ofNat 64 ((e.L.k.toNat + 31) / 32)) (amLoop (HH v))
      fun _ _ => True := by
  refine (pw_blk (X' := Ctr e.L 0 (BitVec.ofNat 64 ((e.L.k.toNat + 31) / 32))) [] (by taint_decide)
    (fun _ _ _ _ _ h => absurd h List.not_mem_nil) fun _ _ _ R EM t hL _ hc hnb =>
      WP.mono (amStart_ok hL hc hnb) fun _ ⟨hc₁, ct₁, nb₁, _⟩ => ⟨⟨R, EM, hc₁⟩, ct₁, nb₁⟩).seq ?_
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  have hk := hp.1.k1024
  exact (prfLoop_tr (v := v) hS e (N := (e.L.k.toNat + 31) / 32)
    (C := BitVec.ofNat 64 ((e.L.k.toNat + 31) / 32)) (by have := hp.1.k64; omega_arith) (by omega_arith) (by decide)
    (by unfold sAM scrBytes; omega_arith) (by decide) (by decide)
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)
    (fun i hi => Offset.ofNat_sub_ofNat (by omega_arith))
    (fun i hi hL _ _ _ _ _ u hu ⟨x9, x11, x12⟩ => WP.mono (msgAM_ok x9 x11 x12 (by omega_arith) hk (hu.msgW hL))
      fun _ ⟨a, b, c, d, e, f, _⟩ => ⟨⟨a, b, c, d, e⟩, f⟩)
    fun _ _ _ _ _ u hu hnb => WP.mono (incrAM_ok hu.ctx.sp hu.slots (hu.ctx.inFr (d := 200) (by decide)))
      fun _ ⟨a, b, c⟩ => ⟨a, b, by rw [c, hnb]⟩) _ _ _ _ _ _ hp e₁ e₂

theorem clLoop_ct {S : Nat} (hS : 15 ≤ S) :
    RelCT isa (Two S fun L g vv m₀ t => ∃ R EM, KD L g vv m₀ R EM t) (clLoop (HH v))
      (Two S fun L g vv m₀ t => ∃ R EM kd, CLR L g vv m₀ R EM kd t) :=
  two_wp (fun e => (clLoop_tr hS e).mono (fun _ _ ⟨hL, hP, _, ⟨_, _, f₁⟩, ⟨_, _, f₂⟩⟩ =>
      ⟨hL, hP, ⟨_, _, f₁.post⟩, ⟨_, _, f₂.post⟩, trivial, trivial⟩) fun _ _ h => h)
    fun _ _ _ _ _ hL hP ⟨_, _, h⟩ => WP.mono (clLoop_ok hL (by omega_arith) h.post h.kdk) fun _ h' => ⟨_, _, _, h'⟩

theorem amLoop_ct {S : Nat} (hS : 15 ≤ S) :
    RelCT isa (Two S fun L g vv m₀ t => ∃ R EM kd, CLR L g vv m₀ R EM kd t) (amLoop (HH v))
      (Two S fun L g vv m₀ t => ∃ R EM kd, AMR L g vv m₀ R EM kd t) :=
  two_wp (fun e => (amLoop_tr hS e).mono (fun _ _ ⟨hL, hP, _, ⟨_, _, _, f₁⟩, ⟨_, _, _, f₂⟩⟩ =>
      ⟨hL, hP, ⟨_, _, f₁.post⟩, ⟨_, _, f₂.post⟩, f₁.nb, f₂.nb⟩) fun _ _ h => h)
    fun _ _ _ _ _ hL hP ⟨_, _, _, h⟩ => WP.mono (amLoop_ok hL (by omega_arith) h) fun _ h' => ⟨_, _, _, h'⟩

end VG.Proof.RsaPkcs1Enc.AArch64.Dec

end

end

/-!
# RSAES-PKCS1-v1_5 decryption on AArch64: constant time, the selection

The mask, the alternative length, the scan and the output: each loop is
checked by the taint analysis from the registers its setup pins as functions
of the layout (`RelCT.wp` with that setup's correctness), and so are the
pointers the output's setup loads from the frame (`ldrSp_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Decrypt

/-- `ldr r, [sp, #off]`. -/
theorem ldrSp_ok (r : Reg) {off : Nat} {t : State} {Q : Addr} (hsp : t.sp = Q) (ho : off % 8 = 0 ∧ off < 32768)
    (h : InRegions (t.rd ++ t.wr) (Q + BitVec.ofNat 64 off) 8) :
    WP isa (.block [.ldrSp r off]) t fun u => u.sp = t.sp ∧ u.mem = t.mem ∧ u.gpr r = slot t Q off := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.load, Size.bits,
    BitVec.setWidth_eq, ho, and_self, ite_true, hsp, h, Option.map_some, Option.some.injEq, exists_eq_left',
    RegUpd.gpr_write_self, RegUpd.sp_write, RegUpd.mem_write]
  exact ⟨trivial, trivial, rfl⟩

/-- Code checked by the taint analysis from the registers `rs`, with what
each run's correctness gives (`F`). -/
theorem taint_wp {P : State → State → Prop} {c : Prog isa} {F : State → Prop} (rs : List Reg)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T} (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true)
    (hag : ∀ a b, P a b → a.sp = b.sp ∧ ∀ r ∈ rs, a.gpr r = b.gpr r)
    (hw : ∀ a b, P a b → WP isa c a F ∧ WP isa c b F) : RelCT isa P c fun a b => F a ∧ F b :=
  ((RelCT.taint (A := taint) (Taint.ofRegs rs) (fun a b hp => ⟨(hag a b hp).1,
    fun r hr => (hag a b hp).2 r (Taint.mem_ofRegs.mp hr)⟩) h).wp hw).mono (fun _ _ h => h) fun _ _ h => h.2

theorem taint_of {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T} (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true)
    (hag : ∀ a b, P a b → a.sp = b.sp ∧ ∀ r ∈ rs, a.gpr r = b.gpr r) : RelCT isa P c fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs rs) (fun a b hp => ⟨(hag a b hp).1,
    fun r hr => (hag a b hp).2 r (Taint.mem_ofRegs.mp hr)⟩) h

theorem pair_eq {a b : State} {x y z : Reg} {vx vy : BitVec 64} (ha : a.gpr x = vx ∧ a.gpr y = vy)
    (hb : b.gpr x = vx ∧ b.gpr y = vy) (hz : z ∈ [x, y]) : a.gpr z = b.gpr z := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl
  exacts [ha.1.trans hb.1.symm, ha.2.trans hb.2.symm]

/-! ## The mask, the alternative length and the scan -/

abbrev AMΦ : Inv := fun L g vv m₀ t => ∃ R EM kd, AMR L g vv m₀ R EM kd t
abbrev MKΦ : Inv := fun L g vv m₀ t => ∃ R EM kd, MK L g vv m₀ R EM kd t
abbrev ALΦ : Inv := fun L g vv m₀ t => ∃ R EM kd, AL L g vv m₀ R EM kd t
abbrev SCΦ : Inv := fun L g vv m₀ t => ∃ R EM kd, SC L g vv m₀ R EM kd t

theorem k_sub {k : BitVec 64} {n : Nat} (h : n ≤ k.toNat) : k - BitVec.ofNat 64 n = BitVec.ofNat 64 (k.toNat - n) := by
  have := k.isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [h])]; omega_using [h]),
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [h]), Nat.mod_eq_of_lt (by omega_using [])]

/-- The mask's loop after `j` iterations. -/
def MG (L : Lay) (j : Nat) (u : State) : Prop :=
  u.sp = L.Q ∧ u.gpr .x8 = BitVec.ofNat 64 (2 ^ j - 1) ∧ u.gpr .x9 = BitVec.ofNat 64 (L.k.toNat - 11)

theorem maskPart_ct {S : Nat} : RelCT isa (Two S AMΦ) maskPart (Two S MKΦ) := by
  refine two_wp (fun e => ?_) fun _ _ _ _ _ hL _ ⟨_, _, _, h⟩ => WP.mono (maskPart_ok hL h) fun _ h' => ⟨_, _, _, h'⟩
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  have hk := hp.1.k1024
  have hk64 := hp.1.k64
  have hw : ∀ g vv m₀ (t : State), AMΦ e.L g vv m₀ t → WP isa (.block maskInit) t (MG e.L 0) :=
    fun _ _ _ t ⟨_, _, _, h⟩ => WP.mono (maskInit_ok h.post.ctx.sp h.post.slots) fun _ ⟨hs, x9, x8⟩ =>
      ⟨hs.sp.trans h.post.ctx.sp, x8, by rw [x9, slot, h.post.ctx.kept.k, k_sub (by omega_using [hk64])]⟩
  refine RelCT.seq (Q := fun _ _ => True) (taint_wp (F := MG e.L 0) [] (by taint_decide)
    (fun _ _ ⟨_, _, _, ⟨_, _, _, f₁⟩, ⟨_, _, _, f₂⟩⟩ =>
      ⟨f₁.post.ctx.sp.trans f₂.post.ctx.sp.symm, fun _ h => absurd h List.not_mem_nil⟩)
    fun _ _ ⟨_, _, _, f₁, f₂⟩ => ⟨hw _ _ _ _ f₁, hw _ _ _ _ f₂⟩) ?_ _ _ _ _ _ _ hp e₁ e₂
  refine (count_ct (bitLength_pos (x := e.L.k.toNat - 11) (by omega_using [hk64])) (fun j a b => MG e.L j a ∧ MG e.L j b)
    fun j hj => ?_).mono (fun _ _ h => h) fun _ _ _ => trivial
  refine (taint_wp (F := fun w => MG e.L (j + 1) w ∧
      (w.gpr .x10 != 0) = decide (j + 1 ≠ Spec.RsaPkcs1Enc.bitLength (e.L.k.toNat - 11))) [.x8, .x9]
    (by taint_decide) (fun _ _ ⟨⟨a, a8, a9⟩, ⟨b, b8, b9⟩⟩ => ⟨a.trans b.symm, fun _ => pair_eq ⟨a8, a9⟩ ⟨b8, b9⟩⟩)
    fun a b ⟨ga, gb⟩ => ⟨?_, ?_⟩).mono (fun _ _ h => h) fun _ _ ⟨⟨ga, ca⟩, ⟨gb, cb⟩⟩ => ⟨⟨ga, gb⟩, ca, cb⟩
  · exact WP.mono (maskStep_ok (by omega_using [hk64]) (by omega_using [hk]) hj ga.2.1 ga.2.2) fun _ ⟨hw, w8, w9, w10⟩ =>
      ⟨⟨hw.sp.trans ga.1, w8, w9⟩, w10⟩
  · exact WP.mono (maskStep_ok (by omega_using [hk64]) (by omega_using [hk]) hj gb.2.1 gb.2.2) fun _ ⟨hw, w8, w9, w10⟩ =>
      ⟨⟨hw.sp.trans gb.1, w8, w9⟩, w10⟩

/-- After `alInit`. -/
def AG (L : Lay) (u : State) : Prop :=
  u.sp = L.Q ∧ u.gpr .x11 = scA L sCL ∧ u.gpr .x12 = BitVec.ofNat 64 128

/-- After `scanInit`. -/
def SG₀ (L : Lay) (u : State) : Prop :=
  u.sp = L.Q ∧ u.gpr .x11 = L.out + BitVec.ofNat 64 2 ∧ u.gpr .x12 = L.k - BitVec.ofNat 64 2

theorem alPart_ct {S : Nat} : RelCT isa (Two S MKΦ) alPart (Two S ALΦ) := by
  refine two_wp (fun e => ?_) fun _ _ _ _ _ hL _ ⟨_, _, _, h⟩ => WP.mono (alPart_ok hL h) fun _ h' => ⟨_, _, _, h'⟩
  have hw : ∀ g vv m₀ (t : State), MKΦ e.L g vv m₀ t → WP isa (.block alInit) t fun u =>
      AG e.L u := fun _ _ _ t ⟨_, _, _, h⟩ =>
    WP.mono (alInit_ok h.amr.post.ctx.sp h.amr.post.slots) fun _ ⟨hs, x11, x12, _⟩ =>
      ⟨hs.sp.trans h.amr.post.ctx.sp, by rw [x11, slot, h.amr.post.ctx.kept.scr], x12⟩
  exact (taint_wp (F := AG e.L) [] (by taint_decide)
    (fun _ _ ⟨_, _, _, ⟨_, _, _, f₁⟩, ⟨_, _, _, f₂⟩⟩ =>
      ⟨f₁.amr.post.ctx.sp.trans f₂.amr.post.ctx.sp.symm, fun _ h => absurd h List.not_mem_nil⟩)
    fun _ _ ⟨_, _, _, f₁, f₂⟩ => ⟨hw _ _ _ _ f₁, hw _ _ _ _ f₂⟩).seq
    (taint_of [.x11, .x12] (by taint_decide) fun _ _ ⟨⟨a, a11, a12⟩, ⟨b, b11, b12⟩⟩ =>
      ⟨a.trans b.symm, fun _ => pair_eq ⟨a11, a12⟩ ⟨b11, b12⟩⟩)

theorem scanPart_ct {S : Nat} : RelCT isa (Two S ALΦ) scanPart (Two S SCΦ) := by
  refine two_wp (fun e => ?_) fun _ _ _ _ _ hL _ ⟨_, _, _, h⟩ => WP.mono (scanPart_ok hL h) fun _ h' => ⟨_, _, _, h'⟩
  have hw : ∀ g vv m₀ (t : State), ALΦ e.L g vv m₀ t → WP isa (.block scanInit) t fun u =>
      SG₀ e.L u :=
    fun _ _ _ t ⟨_, _, _, h⟩ => WP.mono (scanInit_ok h.amr.post.ctx.sp h.amr.post.slots)
      fun _ ⟨hs, x11, x12, _⟩ => ⟨hs.sp.trans h.amr.post.ctx.sp, by rw [x11, slot, h.amr.post.ctx.kept.out],
        by rw [x12, slot, h.amr.post.ctx.kept.k]⟩
  exact (taint_wp (F := SG₀ e.L) [] (by taint_decide)
    (fun _ _ ⟨_, _, _, ⟨_, _, _, f₁⟩, ⟨_, _, _, f₂⟩⟩ =>
      ⟨f₁.amr.post.ctx.sp.trans f₂.amr.post.ctx.sp.symm, fun _ h => absurd h List.not_mem_nil⟩)
    fun _ _ ⟨_, _, _, f₁, f₂⟩ => ⟨hw _ _ _ _ f₁, hw _ _ _ _ f₂⟩).seq
    (taint_of [.x11, .x12] (by taint_decide) fun _ _ ⟨⟨a, a11, a12⟩, ⟨b, b11, b12⟩⟩ =>
      ⟨a.trans b.symm, fun _ => pair_eq ⟨a11, a12⟩ ⟨b11, b12⟩⟩)

/-! ## The output -/

/-- What the output's setup leaves. -/
abbrev FinΦ : Inv := fun L g vv m₀ t => ∃ R EM kd,
  Fin L g vv m₀ R EM (amOf L kd) (vOfEM L EM) (decide (R = 1)) (lenOf L EM kd) t

theorem validSame_ok {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {R : BitVec 64}
    {EM kd : List Byte} (hL : L.Ok) {t : State} (h : SC L g vv m₀ R EM kd t) :
    WP isa (.block validBlock) t (Same t) := by
  have hk := hL.k1024
  have hk64 := hL.k64
  have hc := h.amr.post
  have hK : slot t L.Q oK = BitVec.ofNat 64 L.k.toNat := by
    rw [slot, hc.ctx.kept.k, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hO : slot t L.Q oOut = L.out := hc.ctx.kept.out
  exact WP.mono (validBlock_ok hc.ctx.sp hc.slots (by rw [hO]; exact hc.ctx.outR (by omega_using [hk64]))
    (by rw [hO]; exact hc.ctx.outR (by omega_using [hk64])) h.x17 h.x15 h.x16 h.al hK
    (by have := sep_lt EM (k := L.k.toNat) (by omega_using [hk64]); omega_using [this])) fun _ h => h.1

/-- Before `outInit`: where `*msg_len`'s pointer is. -/
def OH (L : Lay) (u : State) : Prop :=
  u.sp = L.Q ∧ u.mem.readW (L.Q + BitVec.ofNat 64 oML) 64 = L.ml ∧
    InRegions (u.rd ++ u.wr) (L.Q + BitVec.ofNat 64 oML) 8

/-- Before the selection's loop. -/
def SG (L : Lay) (u : State) : Prop :=
  u.sp = L.Q ∧ u.gpr .x10 = scA L sAM + BitVec.ofNat 64 0 ∧ u.gpr .x11 = L.out + BitVec.ofNat 64 0 ∧
    u.gpr .x12 = BitVec.ofNat 64 (L.k.toNat - 0)

theorem selPart_ct {S : Nat} : RelCT isa (Two S SCΦ) selPart (Two S FinΦ) := by
  refine two_wp (fun e => ?_) fun _ _ _ _ _ hL _ ⟨_, _, _, h⟩ => WP.mono (selPart_ok hL h) fun _ h' => ⟨_, _, _, h'⟩
  -- `out` into `x11`, then the validity.
  have vb : RelCT isa (TwoE S SCΦ e) (.block validBlock) fun _ _ => True :=
    RelCT.block_append (l₁ := ([.ldrSp .x11 oOut] : List Instr)) (l₂ := validBlock.tail)
      ((taint_wp (F := fun u => u.sp = e.L.Q ∧ u.gpr .x11 = e.L.out) [] (by taint_decide)
        (fun _ _ ⟨_, _, _, ⟨_, _, _, f₁⟩, ⟨_, _, _, f₂⟩⟩ =>
          ⟨f₁.amr.post.ctx.sp.trans f₂.amr.post.ctx.sp.symm, fun _ h => absurd h List.not_mem_nil⟩)
        fun _ _ ⟨_, _, _, ⟨_, _, _, f₁⟩, ⟨_, _, _, f₂⟩⟩ =>
          ⟨WP.mono (ldrSp_ok .x11 f₁.amr.post.ctx.sp (by decide) (f₁.amr.post.slots oOut (by decide)))
            fun _ ⟨hsp, _, hx⟩ => ⟨hsp.trans f₁.amr.post.ctx.sp, by rw [hx, slot, f₁.amr.post.ctx.kept.out]⟩,
          WP.mono (ldrSp_ok .x11 f₂.amr.post.ctx.sp (by decide) (f₂.amr.post.slots oOut (by decide)))
            fun _ ⟨hsp, _, hx⟩ => ⟨hsp.trans f₂.amr.post.ctx.sp, by rw [hx, slot, f₂.amr.post.ctx.kept.out]⟩⟩).seq
      (taint_of [.x11] (by taint_decide) fun _ _ ⟨⟨a0, a11⟩, ⟨b0, b11⟩⟩ =>
        ⟨a0.trans b0.symm, fun r hr => by rw [List.mem_singleton.mp hr, a11, b11]⟩))
  have oh : ∀ g vv m₀ (t : State), e.L.Ok → SCΦ e.L g vv m₀ t → WP isa (.block validBlock) t (OH e.L) :=
    fun _ _ _ _ hL ⟨_, _, _, h⟩ => WP.mono (validSame_ok hL h) fun _ hs =>
      ⟨hs.sp.trans h.amr.post.ctx.sp, by rw [hs.mem]; exact h.amr.post.ctx.kept.ml,
        by rw [hs.rd, hs.wr]; exact h.amr.post.slots oML (by decide)⟩
  -- `*msg_len`'s pointer into `x10`, then its store.
  have oi : RelCT isa (fun a b => True ∧ OH e.L a ∧ OH e.L b) (.block outInit) fun _ _ => True :=
    RelCT.block_append (l₁ := ([.ldrSp .x10 oML] : List Instr)) (l₂ := outInit.tail)
      ((taint_wp (F := fun u => u.sp = e.L.Q ∧ u.gpr .x10 = e.L.ml) [] (by taint_decide)
        (fun _ _ ⟨_, ha, hb⟩ => ⟨ha.1.trans hb.1.symm, fun _ h => absurd h List.not_mem_nil⟩)
        fun _ _ ⟨_, ha, hb⟩ =>
          ⟨WP.mono (ldrSp_ok .x10 ha.1 (by decide) ha.2.2) fun _ ⟨hsp, _, hx⟩ => ⟨hsp.trans ha.1, hx.trans ha.2.1⟩,
          WP.mono (ldrSp_ok .x10 hb.1 (by decide) hb.2.2) fun _ ⟨hsp, _, hx⟩ => ⟨hsp.trans hb.1, hx.trans hb.2.1⟩⟩).seq
      (taint_of [.x10] (by taint_decide) fun _ _ ⟨⟨a0, a10⟩, ⟨b0, b10⟩⟩ =>
        ⟨a0.trans b0.symm, fun r hr => by rw [List.mem_singleton.mp hr, a10, b10]⟩))
  refine RelCT.assoc ((((vb.wp fun _ _ ⟨hL, _, _, f₁, f₂⟩ => ⟨oh _ _ _ _ hL f₁, oh _ _ _ _ hL f₂⟩).seq oi).wp
    (F₁ := SG e.L) (F₂ := SG e.L) fun _ _ ⟨hL, _, _, ⟨_, _, _, f₁⟩, ⟨_, _, _, f₂⟩⟩ =>
      ⟨WP.mono (selInit_ok hL f₁) fun _ h => ⟨h.ctx.sp, h.x10, h.x11, h.x12⟩,
        WP.mono (selInit_ok hL f₂) fun _ h => ⟨h.ctx.sp, h.x10, h.x11, h.x12⟩⟩).seq ?_)
  exact taint_of [.x11, .x10, .x12] (by taint_decide) fun _ _ ⟨_, ⟨a0, a10, a11, a12⟩, ⟨b0, b10, b11, b12⟩⟩ =>
    ⟨a0.trans b0.symm, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [a11.trans b11.symm, a10.trans b10.symm, a12.trans b12.symm]⟩

end VG.Proof.RsaPkcs1Enc.AArch64.Dec

end

end

/-! ### `RsaPkcs1Enc.AArch64.DecCorrect`, which this module and modules that import it used -/

section

/-!
# RSAES-PKCS1-v1_5 decryption on AArch64: correctness

The frames' pushes, the setup (`entry_ok`), the private-key operation
(`priv_call`), `D`, `DH`, `KDK`, `CL`, `AM`, the alternative length, the scan
and the output (`dBuild_ok` … `selPart_ok`), and the pops: `dec_ok`, for
every implementation of SHA-256's compression function and of
`vg_rsa_private_checked`, against the shared contract (`result_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Decrypt
open VG.Proof.Sha256.AArch64 (Compress)
open VG.Proof.RsaPkcs1Enc (outByte)
open VG.Proof.RsaPkcs1Enc.AArch64.Enc (popped_mem popped_sp popped_v popped_gpr_self popped_gpr_ne freed_mem freed_sp
  freed_v freed_gpr add_add bytesAt_length)

theorem body_eq (stage : List Instr) (privN : String) (priv : Prog isa) (v : Compress) :
    bodyWith (HH v) stage privN priv = .seq (.block stage) (.seq (.call privN priv) (.seq dBuild (.seq (hashD (HH v))
      (.seq (kdkMac (HH v)) (.seq (clLoop (HH v)) (.seq (amLoop (HH v)) (.seq maskPart (.seq alPart
        (.seq scanPart selPart))))))))) := rfl

theorem rOf_setWidth (x : BitVec 64) : (rOf x).setWidth 32 = x.setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  simp only [rOf, BitVec.toNat_setWidth]
  omega_using []

theorem rOf_one (x : BitVec 64) : decide (rOf x = 1) = decide (x.setWidth 32 = 1) := by
  have : rOf x = 1 ↔ x.setWidth 32 = 1 := by
    constructor
    · intro h; rw [← rOf_setWidth, h]; rfl
    · intro h; simp only [rOf, h]; rfl
  simp only [this]

/-- RSADP, as the specification calls the private-key operation. -/
def rsadpOf (L : Lay) (m : Mem) (C : List Byte) : Spec.Rsa.Outcome :=
  Spec.Rsa.privateChecked (Spec.Rsa.bytesAt m L.n L.k.toNat) (Spec.Rsa.bytesAt m L.e L.el.toNat) C
    (Spec.Rsa.bytesAt m L.p L.pl.toNat) (Spec.Rsa.bytesAt m L.q L.ql.toNat) (Spec.Rsa.bytesAt m L.dp L.pl.toNat)
    (Spec.Rsa.bytesAt m L.dq L.ql.toNat) (Spec.Rsa.bytesAt m L.qi L.pl.toNat)

/-- The stack the contract gives. -/
theorem spec_sp {P : Nat} {s : State} (h : (decSpec P).pre s) : P + 240 ≤ s.sp.toNat := by
  sig_pre [Spec.RsaPkcs1Enc.decryptContract, Spec.RsaPkcs1Enc.decryptSig, AArch64.abi, AArch64.argRegs,
    _root_.List.range, _root_.List.range.loop, List.append_eq] at h
  exact h.1

/-- The postcondition, from what the private-key operation gave and the end. -/
theorem result_ok {P : Nat} {s : State} (h : (decSpec P).pre s) {x0c : BitVec 64} {mc : Mem} {t : State}
    {kd : List Byte} (hkd : kd = Spec.RsaPkcs1Enc.kdk (lay P s).k.toNat (dOf (lay P s) s.mem) (cOf (lay P s) s.mem))
    (hres : Spec.Rsa.writtenOutcome mc (lay P s).out (lay P s).k.toNat (x0c.setWidth 32) (privOut (lay P s) s.mem))
    (hx0 : t.gpr .x0 = rOf x0c)
    (hout : ∀ i < (lay P s).k.toNat, t.mem ((lay P s).out + BitVec.ofNat 64 i) =
      outByte (vOfEM (lay P s) (Spec.Rsa.bytesAt mc (lay P s).out (lay P s).k.toNat)) (decide (rOf x0c = 1))
        ((lay P s).k.toNat - lenOf (lay P s) (Spec.Rsa.bytesAt mc (lay P s).out (lay P s).k.toNat) kd) i
        ((Spec.Rsa.bytesAt mc (lay P s).out (lay P s).k.toNat).getD i 1) ((amOf (lay P s) kd).getD i 0))
    (hml : t.mem.readW (lay P s).ml 64 =
      BitVec.ofNat 64 (lenOf (lay P s) (Spec.Rsa.bytesAt mc (lay P s).out (lay P s).k.toNat) kd) &&&
        bm (decide (rOf x0c = 1)))
    (hAM : (amOf (lay P s) kd).length = (lay P s).k.toNat) :
    (decSpec P).post s t := by
  have hL := lay_ok h
  have hk64 := hL.k64
  sig_post [Spec.RsaPkcs1Enc.decryptContract, Spec.RsaPkcs1Enc.decryptSig, AArch64.abi, AArch64.argRegs,
    _root_.List.range, _root_.List.range.loop, List.append_eq]
  -- The buffers, as the layout names them.
  show Spec.RsaPkcs1Enc.writtenMsg t.mem (lay P s).out (lay P s).ml (lay P s).k.toNat ((t.gpr .x0).setWidth 32)
    (Spec.RsaPkcs1Enc.decrypt (Spec.Rsa.bytesAt s.mem (lay P s).n (lay P s).k.toNat)
      (Spec.Rsa.bytesAt s.mem (lay P s).e (lay P s).el.toNat) (dOf (lay P s) s.mem)
      (Spec.Rsa.bytesAt s.mem (lay P s).p (lay P s).pl.toNat) (Spec.Rsa.bytesAt s.mem (lay P s).q (lay P s).ql.toNat)
      (Spec.Rsa.bytesAt s.mem (lay P s).dp (lay P s).pl.toNat) (Spec.Rsa.bytesAt s.mem (lay P s).dq (lay P s).ql.toNat)
      (Spec.Rsa.bytesAt s.mem (lay P s).qi (lay P s).pl.toNat) (cOf (lay P s) s.mem))
  have hn : (Spec.Rsa.bytesAt s.mem (lay P s).n (lay P s).k.toNat).length = (lay P s).k.toNat := bytesAt_length _ _ _
  have hC : (cOf (lay P s) s.mem).length = (Spec.Rsa.bytesAt s.mem (lay P s).n (lay P s).k.toNat).length := by
    rw [hn]; exact bytesAt_length _ _ _
  have hbytes : Spec.Rsa.bytesAt t.mem (lay P s).out (lay P s).k.toNat =
      (List.range (lay P s).k.toNat).map fun i => t.mem ((lay P s).out + BitVec.ofNat 64 i) := rfl
  have hw : Spec.Rsa.wordsAt t.mem (lay P s).ml 1 = [t.mem.readW (lay P s).ml 64] := by
    simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero]
  simp only [Spec.RsaPkcs1Enc.decrypt]
  have eO : rsadpOf (lay P s) s.mem (cOf (lay P s) s.mem) = privOut (lay P s) s.mem := rfl
  show Spec.RsaPkcs1Enc.writtenMsg _ _ _ _ _ (Spec.RsaPkcs1Enc.decryptWith (rsadpOf (lay P s) s.mem)
    (Spec.Rsa.bytesAt s.mem (lay P s).n (lay P s).k.toNat).length (dOf (lay P s) s.mem) (cOf (lay P s) s.mem))
  cases hO : privOut (lay P s) s.mem with
  | ok EM' =>
    rw [hO] at hres
    obtain ⟨hr, hb⟩ := hres
    have hok : decide (rOf x0c = 1) = true := by rw [rOf_one, hr]; rfl
    rw [Proof.RsaPkcs1Enc.decryptWith_of_ok hC (by rw [hn]; omega_using [hk64]) (eO.trans hO)]
    subst hb
    have hEMl := bytesAt_length mc (lay P s).out (lay P s).k.toNat
    have hal := Proof.RsaPkcs1Enc.altLength_le (lay P s).k.toNat (clOf kd)
    obtain ⟨hL1, hmap⟩ := Proof.RsaPkcs1Enc.sel_eq hEMl hAM (by omega_using [hk64]) hal
    have hM : Spec.RsaPkcs1Enc.implicitDecode (dOf (lay P s) s.mem) (cOf (lay P s) s.mem)
        (Spec.Rsa.bytesAt mc (lay P s).out (lay P s).k.toNat) =
        (if Spec.RsaPkcs1Enc.valid (Spec.Rsa.bytesAt mc (lay P s).out (lay P s).k.toNat) then
          Spec.RsaPkcs1Enc.lastN (Spec.RsaPkcs1Enc.msgLength (Spec.Rsa.bytesAt mc (lay P s).out (lay P s).k.toNat))
            (Spec.Rsa.bytesAt mc (lay P s).out (lay P s).k.toNat)
        else Spec.RsaPkcs1Enc.lastN (Spec.RsaPkcs1Enc.altLength (lay P s).k.toNat (clOf kd)) (amOf (lay P s) kd)) := by
      simp only [Spec.RsaPkcs1Enc.implicitDecode, Spec.RsaPkcs1Enc.alternative, hEMl, hkd]
    rw [hM]
    refine ⟨by rw [hx0, rOf_setWidth, hr], ?_, ?_⟩
    · rw [hbytes, ← hmap]
      exact List.map_congr_left fun i hi => by rw [hout i (List.mem_range.mp hi), hok]
    · rw [hw, hml, hok, show bm true = BitVec.allOnes 64 from rfl, BitVec.and_allOnes, ← hL1]
  | invalid =>
    rw [hO] at hres
    obtain ⟨hr, -⟩ := hres
    have hok : decide (rOf x0c = 1) = false := by rw [rOf_one, hr]; rfl
    rw [Proof.RsaPkcs1Enc.decryptWith_of_invalid (eO.trans hO)]
    refine ⟨by rw [hx0, rOf_setWidth, hr], ?_, ?_⟩
    · rw [hbytes, List.map_congr_left (g := fun _ => (0 : Byte)) fun i hi => by
        rw [hout i (List.mem_range.mp hi), hok, Proof.RsaPkcs1Enc.outByte_false]]
      simp
    · rw [hw, hml, hok]; simp [bm]
  | fault =>
    rw [hO] at hres
    obtain ⟨hr, -⟩ := hres
    have hok : decide (rOf x0c = 1) = false := by rw [rOf_one, hr]; rfl
    rw [Proof.RsaPkcs1Enc.decryptWith_of_fault hC (by rw [hn]; omega_using [hk64]) (eO.trans hO)]
    refine ⟨by rw [hx0, rOf_setWidth, hr], ?_, ?_⟩
    · rw [hbytes, List.map_congr_left (g := fun _ => (0 : Byte)) fun i hi => by
        rw [hout i (List.mem_range.mp hi), hok, Proof.RsaPkcs1Enc.outByte_false]]
      simp
    · rw [hw, hml, hok]; simp [bm]

/-- `vg_rsa_pkcs1_decrypt` meets the shared contract and the calling convention. -/
theorem decW_ok (v : Compress) {P : Nat} (hP : 16 ≤ P) {s : State} {R₀ X : List Region} {pre : Addr}
    {prl : BitVec 64}
    (h : (decSpec P).pre (s.withRegions R₀ s.wr)) (stage : List Instr) (name : String) (priv : Prog isa)
    (hcall : WP isa (.block stage) (entered s) fun t =>
      WP isa (.call name priv) t (Called (layW P s X pre prl) s.gpr s.v s.mem)) :
    WP isa (codeWith (HH v) stage name priv) s fun s' =>
      abiPreserved s s' ∧ (decSpec P).post (s.withRegions R₀ s.wr) s' := by
  have hL : (layW P s X pre prl).Ok := (lay_ok h).withX X pre prl
  have hnQ := hL.nQ
  have hpQ := hL.pQ
  have hsp : P + 240 ≤ s.sp.toNat := spec_sp (s := s.withRegions R₀ s.wr) h
  have hP16 : 16 ≤ (layW P s X pre prl).P := hP
  refine WP.frameAlloc (by omega_using [hsp]) (by decide) ?_ ?_
  · show 224 ≤ (s.sp - 16).toNat
    rw [BitVec.toNat_sub_of_le (by show 16 ≤ s.sp.toNat; omega_using [hsp])]
    show 224 ≤ s.sp.toNat - 16
    omega_using [hsp]
  · show WP isa (bodyWith (HH v) stage name priv) (entered s) _
    rw [body_eq]
    refine WP.seq (WP.mono hcall fun t hw => ?_)
    refine WP.seq (WP.mono hw fun t₁ h₁ => ?_)
    refine WP.seq (WP.mono (dBuild_ok hL h₁) fun t₂ h₂ => ?_)
    refine WP.seq (WP.mono (hashD_ok hL hP16 h₂) fun t₃ h₃ => ?_)
    refine WP.seq (WP.mono (kdkMac_ok hL hP16 h₃) fun t₄ h₄ => ?_)
    refine WP.seq (WP.mono (clLoop_ok hL hP16 h₄.post h₄.kdk) fun t₅ h₅ => ?_)
    refine WP.seq (WP.mono (amLoop_ok hL hP16 h₅) fun t₆ h₆ => ?_)
    have hAM : Spec.Rsa.bytesAt t₆.mem (scA (layW P s X pre prl) sAM) (layW P s X pre prl).k.toNat =
        amOf (layW P s X pre prl) (Spec.RsaPkcs1Enc.kdk (layW P s X pre prl).k.toNat (dOf (layW P s X pre prl) s.mem)
          (cOf (layW P s X pre prl) s.mem)) := h₆.am
    refine WP.seq (WP.mono (maskPart_ok hL h₆) fun t₇ h₇ => ?_)
    refine WP.seq (WP.mono (alPart_ok hL h₇) fun t₈ h₈ => ?_)
    refine WP.seq (WP.mono (scanPart_ok hL h₈) fun t₉ h₉ => ?_)
    refine WP.mono (selPart_ok hL h₉) fun u hu mm uu fl => ?_
    have hc := hu.ctx
    have hsp' : (freed frameBytes u).sp = (layW P s X pre prl).Q + BitVec.ofNat 64 224 := by
      rw [freed_sp, hc.sp]; rfl
    -- What the postcondition reads lies apart from the stack, whose frames' bytes are lost.
    obtain hS : Region.Sub (below s.sp (224 + 16)) (layW P s X pre prl).STK := by
      obtain h0 := Lay.Ok.sub_stk (L := layW P s X pre prl) (d := 0) (n := 240) (by decide)
      rw [show (layW P s X pre prl).Q + BitVec.ofNat 64 0 = (layW P s X pre prl).Q from BitVec.add_zero _] at h0
      exact h0
    refine ⟨⟨fun r hr => ?_, ?_, fun r hr => ?_⟩, ?_⟩
    · show (popped .x30 (freed frameBytes u)).gpr r = s.gpr r
      by_cases h30 : r = .x30
      · subst r
        rw [popped_gpr_self, freed_mem, hsp']; exact hc.kept.lr
      · rw [popped_gpr_ne _ h30, freed_gpr]
        exact hc.cs r hr h30
    · show (popped .x30 (freed frameBytes u)).sp = s.sp
      rw [popped_sp, hsp']
      show (layW P s X pre prl).Q + BitVec.ofNat 64 224 + BitVec.ofNat 64 16 = s.sp
      rw [add_add]; exact lay_Q P s
    · exact hc.vs r hr
    · refine result_ok h rfl h₁.out ?_ (fun i hi => ?_) ?_ (by
        have := bytesAt_length t₆.mem (scA (layW P s X pre prl) sAM) (layW P s X pre prl).k.toNat
        rw [hAM] at this; exact this)
      · show (popped .x30 (freed frameBytes u)).gpr .x0 = _
        rw [popped_gpr_ne _ (by decide), freed_gpr]; exact hu.x0
      · exact (lost_byte (R := (layW P s X pre prl).OUT) fl (hL.kO.symm.sub_right hS) hi).trans (hu.out i hi)
      · exact (fl.readW (r := (layW P s X pre prl).ML) (Region.contains_self _ _) (fun R hR => by
          simp only [List.mem_singleton] at hR; subst hR; exact hL.kM.symm.sub_right hS) (by decide)).trans hu.ml

/-- `vg_rsa_pkcs1_decrypt` meets the shared contract and the calling convention. -/
theorem dec_ok (v : Compress) (pv : PrivImpl) {s : State} (h : (decSpec (pv.S + 1)).pre s) :
    WP isa (code (HH v) pv.name pv.code) s fun s' => abiPreserved s s' ∧ (decSpec (pv.S + 1)).post s s' := by
  have hS := pv.S15
  have hL := lay_ok h
  exact decW_ok v (by omega_using [hS]) (R₀ := s.rd) (X := []) h setup pv.name pv.code
    (WP.mono (entry_ok h) fun t ⟨hc, hr⟩ => priv_call pv hL rfl hc hr)

end VG.Proof.RsaPkcs1Enc.AArch64.Dec

end

end

/-!
# RSAES-PKCS1-v1_5 decryption on AArch64: verified

The pieces' relations put together (`dec_ct`), and with correctness
(`dec_ok`): `vg_rsa_pkcs1_decrypt`, for any implementation `v` of SHA-256's
compression function and `pv` of `vg_rsa_private_checked`, is verified
against the shared contract with the stack it and its callee use
(`dec_verified`), given that the contract is satisfiable for it (which the
registration file checks).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Decrypt
open VG.Proof.Sha256.AArch64 (Compress)

theorem pub_sp {P : Nat} {s₁ s₂ : State} (h : (decSpec P).pub s₁ s₂) : s₁.sp = s₂.sp := by
  sig_pub [Spec.RsaPkcs1Enc.decryptContract, Spec.RsaPkcs1Enc.decryptSig, AArch64.abi, AArch64.argRegs,
    _root_.List.range, _root_.List.range.loop, List.append_eq] at h
  exact h.1

theorem dec_ct (v : Compress) (pv : PrivImpl) :
    ConstantTime isa (decSpec (pv.S + 1)).pre (decSpec (pv.S + 1)).pub (code (HH v) pv.name pv.code) := by
  have hS := pv.S15
  refine RelCT.constantTime (RelCT.pushFrame (fun _ _ h => pub_sp h.2.2) (RelCT.alloc (R := fun _ _ => True) ?_))
  rw [body_eq]
  refine ((setup_ct pv.S).seq ((priv_ct pv).seq ((dBuild_ct pv.S).seq ((hashD_ct (v := v) hS).seq
    ((kdkMac_ct hS).seq ((clLoop_ct hS).seq ((amLoop_ct hS).seq (maskPart_ct.seq (alPart_ct.seq
      (scanPart_ct.seq selPart_ct)))))))))).mono ?_ fun _ _ _ => trivial
  rintro _ _ ⟨_, _, ⟨s₁, s₂, ⟨h₁, h₂, hp⟩, rfl, rfl⟩, rfl, rfl⟩
  exact ⟨s₁, s₂, h₁, h₂, hp, rfl, rfl⟩

/-- The stack the function uses: the callee's and the frames'. -/
def decStack (pv : PrivImpl) : Nat := pv.stack + 240

theorem decStack_eq (pv : PrivImpl) : decStack pv = pv.S + 1 + 240 := by rw [decStack, pv.stack_eq]

/-- `vg_rsa_pkcs1_decrypt`, with `v` and `pv`. -/
theorem dec_verified (v : Compress) (pv : PrivImpl)
    (hsat : ∃ s, (Spec.RsaPkcs1Enc.decryptContract AArch64.abi (decStack pv)).pre s) :
    Verified AArch64.target (code (HH v) pv.name pv.code)
      (Spec.RsaPkcs1Enc.decryptContract AArch64.abi (decStack pv)) := by
  rw [decStack_eq] at hsat ⊢
  exact Verified.of_correct (fun _ h => by
    obtain ⟨t, s', he, hp⟩ := dec_ok v pv h
    exact ⟨t, s', he, hp⟩) (dec_ct v pv) (Contract.Implies.refl hsat)

end VG.Proof.RsaPkcs1Enc.AArch64.Dec

end

end

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Decrypt
open VG.Proof.Sha256.AArch64 (Compress)

theorem stackArgs_seventeen (s : State) :
    List.map (stackArg s) (List.range 17) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11, stackArg s 12, stackArg s 13, stackArg s 14, stackArg s 15, stackArg s 16] := rfl

/-- The regions `vg_rsa_pkcs1_decrypt` reads: its buffers and stack arguments. -/
def rdD (s : State) : List Region :=
  [⟨s.gpr .x3, (s.gpr .x4).toNat⟩, ⟨s.gpr .x5, (s.gpr .x6).toNat⟩, ⟨s.gpr .x7, (stackArg s 0).toNat⟩,
    ⟨stackArg s 1, (stackArg s 2).toNat⟩, ⟨stackArg s 3, (stackArg s 4).toNat⟩,
    ⟨stackArg s 5, (stackArg s 6).toNat⟩, ⟨stackArg s 7, (stackArg s 8).toNat⟩,
    ⟨stackArg s 9, (stackArg s 10).toNat⟩, ⟨stackArg s 11, (stackArg s 12).toNat⟩, ⟨stackArgAddr s 0, 120⟩]

/-- `pre` and `pre_len`, our stack arguments 15 and 16, and `pre`. -/
def XD (s : State) : List Region :=
  [⟨stackArgAddr s 15, 16⟩, ⟨stackArg s 15, (stackArg s 16).toNat * 8⟩]

/-- What the contract says of `pre`, besides what `decSpec` says. -/
structure PreD (P : Nat) (s : State) : Prop where
  sp2 : s.sp.toNat + 136 ≤ 2 ^ 64
  rd : s.rd = (rdD s).take 9 ++ [⟨stackArg s 15, (stackArg s 16).toNat * 8⟩, ⟨stackArgAddr s 0, 136⟩]
  oa : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region).Disjoint ⟨stackArgAddr s 0, 136⟩
  ma : (⟨s.gpr .x2, 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 136⟩
  sa : (⟨stackArg s 13, (stackArg s 14).toNat * 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 136⟩
  ka : (⟨s.sp - BitVec.ofNat 64 (P + 240), P + 240⟩ : Region).Disjoint ⟨stackArgAddr s 0, 136⟩
  op : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region).Disjoint ⟨stackArg s 15, (stackArg s 16).toNat * 8⟩
  mp : (⟨s.gpr .x2, 8⟩ : Region).Disjoint ⟨stackArg s 15, (stackArg s 16).toNat * 8⟩
  sp : (⟨stackArg s 13, (stackArg s 14).toNat * 8⟩ : Region).Disjoint ⟨stackArg s 15, (stackArg s 16).toNat * 8⟩
  kp : (⟨s.sp - BitVec.ofNat 64 (P + 240), P + 240⟩ : Region).Disjoint ⟨stackArg s 15, (stackArg s 16).toNat * 8⟩
  wp : (stackArg s 15).toNat + (stackArg s 16).toNat * 8 ≤ 2 ^ 64
  prl : (stackArg s 16).toNat =
    Spec.Rsa.privatePrecomputedWords (s.gpr .x4).toNat (stackArg s 4).toNat (stackArg s 6).toNat
  key : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 6).toNat) =
    some (Spec.Rsa.wordsAt s.mem (stackArg s 15) (stackArg s 16).toNat)

theorem sub120 (s : State) : Region.Sub ⟨stackArgAddr s 0, 120⟩ ⟨stackArgAddr s 0, 136⟩ := by
  simpa using Offset.sub_base (stackArgAddr s 0) (d := 0) (n := 120) (k := 136) (by decide)

theorem decSpec_of {P : Nat} {s : State}
    (h : (Spec.RsaPkcs1Enc.decryptPrecomputedContract AArch64.abi (P + 240)).pre s) :
    (decSpec P).pre (s.withRegions (rdD s) s.wr) ∧ PreD P s := by
  sig_pre [Spec.RsaPkcs1Enc.decryptPrecomputedContract, Spec.RsaPkcs1Enc.decryptPrecomputedSig,
    Spec.RsaPkcs1Enc.decryptSig, AArch64.abi, AArch64.argRegs, stackArgs_seventeen, List.append_eq,
    _root_.List.range, _root_.List.range.loop] at h
  sig_pre [Spec.RsaPkcs1Enc.decryptPrecomputedContract, Spec.RsaPkcs1Enc.decryptPrecomputedSig,
    Spec.RsaPkcs1Enc.decryptSig, AArch64.abi, AArch64.argRegs, stackArgs_seventeen, List.append_eq,
    _root_.List.range, _root_.List.range.loop] at h
  sig_split h
  rename_i sp1 sp2 rd wr oM oN oE oD oI oP oQ oDP oDQ oQI oS oPr oA mN mE mD mI mP mQ mDP mDQ mQI mS mPr mA
    nS eS dS iS pS qS dpS dqS qiS sPr sA kO kM kN kE kD kI kP kQ kDP kDQ kQI kS kPr kA bO bM bN bE bD bI bP bQ
    bDP bDQ bQI bS bPr kv olk ilk el1 elk dl1 dlk pl1 plk ql1 qlk dpl qil dql slk prl
  obtain s1 := sub120 s
  obtain e : P + 239 + 1 = P + 240 := by omega_using []
  rw [e] at sp1 kO kM kN kE kD kI kP kQ kDP kDQ kQI kS kPr kA
  refine ⟨?_, ⟨sp2, by rw [rd]; rfl, oA, mA, sA, kA, oPr, mPr, sPr, kPr, bPr, prl, h⟩⟩
  sig_pre [Spec.RsaPkcs1Enc.decryptContract, Spec.RsaPkcs1Enc.decryptSig, AArch64.abi, AArch64.argRegs,
    _root_.List.range, _root_.List.range.loop, List.append_eq]
  simp only [Proof.Rsa.AArch64.stackArg_withRegions, Proof.Rsa.AArch64.stackArgAddr_withRegions, e]
  exact ⟨sp1, by omega_using [sp2], rfl, wr, oM, oN, oE, oD, oI, oP, oQ, oDP, oDQ, oQI, oS, oA.sub_right s1, mN, mE, mD, mI,
    mP, mQ, mDP, mDQ, mQI, mS, mA.sub_right s1, nS, eS, dS, iS, pS, qS, dpS, dqS, qiS, sA.sub_right s1, kO, kM,
    kN, kE, kD, kI, kP, kQ, kDP, kDQ, kQI, kS, kA.sub_right s1, bO, bM, bN, bE, bD, bI, bP, bQ, bDP, bDQ, bQI,
    bS, kv, olk, ilk, el1, elk, dl1, dlk, pl1, plk, ql1, qlk, dpl, qil, dql, slk⟩

/-! ## The callee -/

/-- An implementation of `vg_rsa_private_checked_precomputed`, as
`PrivImpl` is of `vg_rsa_private_checked`. -/
structure PrivPImpl where
  name : String
  code : Prog isa
  stack : Nat
  verified : Verified AArch64.target code (Proof.Rsa.privateCheckedPrecomputedContract AArch64.abi stack)
  pos : 16 ≤ stack
  depth : 16 * code.aarch64Depth ≤ stack
  noDit : code.all (fun i => !i.touchesDit) = true

namespace PrivPImpl

variable (v : PrivPImpl)

def S : Nat := v.stack - 1

theorem stack_eq : v.stack = v.S + 1 := by have := v.pos; unfold S; omega_using [this]

theorem verified' :
    Verified AArch64.target v.code (Proof.Rsa.privateCheckedPrecomputedContract AArch64.abi (v.S + 1)) :=
  v.stack_eq ▸ v.verified

theorem depth' : 16 * v.code.aarch64Depth ≤ v.S + 1 := v.stack_eq ▸ v.depth

theorem S15 : 15 ≤ v.S := by have := v.pos; unfold S; omega_using [this]

end PrivPImpl

/-! ## In the frames -/

/-- What the call of `vg_rsa_private_checked_precomputed` needs, besides
`Ctx`: our stack arguments 15 and 16, `pre` and `pre_len`, and `pre`, in the
memory `m₀` on entry. -/
structure PreX (L : Lay) (m₀ : Mem) : Prop where
  x : L.X = [⟨L.Q + BitVec.ofNat 64 360, 16⟩, ⟨L.pre, L.prl.toNat * 8⟩]
  nQ2 : L.Q.toNat + 376 ≤ 2 ^ 64
  a15 : m₀.readW (L.Q + BitVec.ofNat 64 360) 64 = L.pre
  a16 : m₀.readW (L.Q + BitVec.ofNat 64 368) 64 = L.prl
  ao : L.OUT.Disjoint ⟨L.Q + BitVec.ofNat 64 360, 16⟩
  am : L.ML.Disjoint ⟨L.Q + BitVec.ofNat 64 360, 16⟩
  as : L.SCR.Disjoint ⟨L.Q + BitVec.ofNat 64 360, 16⟩
  po : L.OUT.Disjoint ⟨L.pre, L.prl.toNat * 8⟩
  pm : L.ML.Disjoint ⟨L.pre, L.prl.toNat * 8⟩
  ps : L.SCR.Disjoint ⟨L.pre, L.prl.toNat * 8⟩
  pk : L.STK.Disjoint ⟨L.pre, L.prl.toNat * 8⟩
  wp : L.pre.toNat + L.prl.toNat * 8 ≤ 2 ^ 64
  prlv : L.prl.toNat = Spec.Rsa.privatePrecomputedWords L.k.toNat L.pl.toNat L.ql.toNat
  key : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt m₀ L.n L.k.toNat) (Spec.Rsa.bytesAt m₀ L.p L.pl.toNat)
      (Spec.Rsa.bytesAt m₀ L.q L.ql.toNat) =
    some (Spec.Rsa.wordsAt m₀ L.pre L.prl.toNat)

section
variable {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem}

/-- `Ctx` survives writes to the private-key operation's stack arguments 12
and 13, which no step reads but the call. -/
theorem Ctx.args2 (hL : L.Ok) {t t' : State} (hc : Ctx L g vv m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hsp : t'.sp = t.sp) (hv : t'.v = t.v) (hg : ∀ r ∈ preserved, r ≠ .x30 → t'.gpr r = t.gpr r)
    (hf : Frame [⟨L.Q + BitVec.ofNat 64 96, 16⟩] t.mem t'.mem) : Ctx L g vv m₀ t' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp, fun r hr hr' => (hg r hr hr').trans (hc.cs r hr hr'),
    fun r hr => by rw [hv]; exact hc.vs r hr,
    hc.kept.frame hf fun d hd R hR => by
      rw [List.mem_singleton.mp hR]
      unfold keptOff at hd
      exact hL.fr_sep (by omega_using [hd]) (by omega_using [hd]) (by omega_using []),
    hc.frame.trans (hf.sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨L.STK, by simp, Lay.Ok.sub_stk (by omega_using [])⟩)⟩

/-- A word of our stack arguments 15 and 16, as on entry. -/
theorem PreX.arg (hL : L.Ok) (hx : PreX L m₀) {t : State} (hc : Ctx L g vv m₀ t) {d : Nat}
    (hd : d = 360 ∨ d = 368) : t.mem.readW (L.Q + BitVec.ofNat 64 d) 64 = m₀.readW (L.Q + BitVec.ofNat 64 d) 64 := by
  have hpQ := hL.pQ
  have hn := hx.nQ2
  obtain hs : Region.Sub ⟨L.Q + BitVec.ofNat 64 d, 8⟩ ⟨L.Q + BitVec.ofNat 64 360, 16⟩ :=
    Offset.sub _ (by omega_using [hd]) (by omega_using [hd])
  refine hc.frame.readW (r := ⟨L.Q + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact (hx.ao.sub_right hs).symm
  · exact (hx.am.sub_right hs).symm
  · exact (hx.as.sub_right hs).symm
  · show Region.Disjoint _ ⟨L.Q - BitVec.ofNat 64 L.P, L.P + 240⟩
    rw [VG.Proof.RsaPkcs1Enc.AArch64.Enc.q_add L.Q L.P d]
    exact Offset.disjoint_base _ (by omega_using [hd]) (by omega_using [hd, hpQ, hn])


theorem extra_ok (hL : L.Ok) (hx : PreX L m₀) {t : State} (hc : Ctx L g vv m₀ t) (hr : Ready L t) :
    WP isa (.block extraMoves) t fun u => Ctx L g vv m₀ u ∧ Ready L u ∧
      u.mem.readW (L.Q + BitVec.ofNat 64 96) 64 = L.pre ∧ u.mem.readW (L.Q + BitVec.ofNat 64 104) 64 = L.prl := by
  have hpQ := hL.pQ
  have hn := hx.nQ2
  have hnQ := hL.nQ
  unfold extraMoves
  rw [WP.block_append_iff, WP.block_append_iff]
  obtain h0 : WP isa (.block [.addSp .x9 0]) t fun t₀ => t₀ = t.write .x .x9 L.Q := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Nat.reduceLT, ite_true, hc.sp,
      BitVec.add_zero, Option.some.injEq, exists_eq_left']
  refine WP.mono h0 fun t₀ ht₀ => ?_
  subst ht₀
  obtain x9 : (t.write .x .x9 L.Q).gpr .x9 = L.Q := by
    simp only [RegUpd.gpr_write, ite_true, Size.bits, BitVec.setWidth_eq]
  obtain inA : ∀ (u : State), u.rd = t.rd → u.wr = t.wr → ∀ d, d = 360 ∨ d = 368 →
      InRegions (u.rd ++ u.wr) (L.Q + BitVec.ofNat 64 d) 8 := fun u hu hw d hd =>
    ⟨⟨L.Q + BitVec.ofNat 64 360, 16⟩, by rw [hu, hw, hc.rd, hx.x]; simp,
      Offset.contains _ (by omega_using [hd]) (by omega_using [hd]) (by omega_using [])⟩
  obtain inF : ∀ (u : State), u.wr = t.wr → ∀ d, d + 8 ≤ frameBytes →
      InRegions u.wr (L.Q + BitVec.ofNat 64 d) 8 := fun u hw d hd => by rw [hw]; exact hc.inFr hd
  refine WP.mono (mv_step (j := 15) (d := 96) (by decide) (by decide)
    (by rw [RegUpd.sp_write, hc.sp]; exact inA _ (RegUpd.rd_write ..) (RegUpd.wr_write ..) 360 (.inl rfl))
    (by rw [x9]; exact inF _ (RegUpd.wr_write ..) 96 (by decide))) fun t₁ ⟨r₁, w₁, s₁, v₁, m₁, g₁⟩ => ?_
  obtain sp₁ : t₁.sp = L.Q := by rw [s₁, RegUpd.sp_write, hc.sp]
  refine WP.mono (mv_step (j := 16) (d := 104) (by decide) (by decide)
    (by rw [sp₁]; exact inA _ (r₁.trans (RegUpd.rd_write ..)) (w₁.trans (RegUpd.wr_write ..)) 368 (.inr rfl))
    (by rw [g₁ .x9 (by decide), x9]; exact inF _ (w₁.trans (RegUpd.wr_write ..)) 104 (by decide)))
    fun u ⟨r₂, w₂, s₂, v₂, m₂, g₂⟩ => ?_
  -- The values moved.
  obtain e15 : (t.write .x .x9 L.Q).mem.readW ((t.write .x .x9 L.Q).sp + BitVec.ofNat 64 (arg 15)) 64 = L.pre := by
    rw [RegUpd.mem_write, RegUpd.sp_write, hc.sp, show arg 15 = 360 from rfl, hx.arg hL hc (.inl rfl), hx.a15]
  obtain sep : Mem.Sep (L.Q + BitVec.ofNat 64 368) 8 (L.Q + BitVec.ofNat 64 96) 8 :=
    Offset.sep _ (by omega_using []) (by omega_using []) (by omega_using [])
  obtain e16 : t₁.mem.readW (t₁.sp + BitVec.ofNat 64 (arg 16)) 64 = L.prl := by
    rw [m₁, x9, e15, sp₁, show arg 16 = 368 from rfl, RegUpd.mem_write,
      Mem.readW_writeW_sep sep (by decide), hx.arg hL hc (.inr rfl), hx.a16]
  obtain mu : u.mem = (t.mem.writeW (L.Q + BitVec.ofNat 64 96) L.pre).writeW (L.Q + BitVec.ofNat 64 104) L.prl := by
    rw [m₂, e16, g₁ .x9 (by decide), x9, m₁, x9, e15, RegUpd.mem_write]
  obtain hr96 : Region.Contains ⟨L.Q + BitVec.ofNat 64 96, 16⟩ (L.Q + BitVec.ofNat 64 96) (64 / 8) :=
    Offset.contains _ (by omega_using []) (by omega_using []) (by omega_using [])
  obtain hr104 : Region.Contains ⟨L.Q + BitVec.ofNat 64 96, 16⟩ (L.Q + BitVec.ofNat 64 104) (64 / 8) :=
    Offset.contains _ (by omega_using []) (by omega_using []) (by omega_using [])
  obtain gu : ∀ r, r ≠ .x9 → r ≠ .x10 → u.gpr r = t.gpr r := fun r h9 h10 => by
    rw [g₂ r h10, g₁ r h10, RegUpd.gpr_write_of_ne _ _ _ h9]
  obtain hfr : Frame [⟨L.Q + BitVec.ofNat 64 96, 16⟩] t.mem u.mem := by
    rw [mu]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ hr96).writeW (List.mem_singleton_self _) _ hr104
  refine ⟨hc.args2 hL (r₂.trans (r₁.trans (RegUpd.rd_write ..))) (w₂.trans (w₁.trans (RegUpd.wr_write ..)))
    (by rw [s₂, sp₁, hc.sp]) (by rw [v₂, v₁, RegUpd.v_write])
    (fun r hr _ => gu r (Enc.preserved_ne hr (by decide)) (Enc.preserved_ne hr (by decide)))
    hfr, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [gu .x0 (by decide) (by decide)]; exact hr.x0
  · rw [gu .x1 (by decide) (by decide)]; exact hr.x1
  · rw [gu .x2 (by decide) (by decide)]; exact hr.x2
  · rw [gu .x3 (by decide) (by decide)]; exact hr.x3
  · rw [gu .x4 (by decide) (by decide)]; exact hr.x4
  · rw [gu .x5 (by decide) (by decide)]; exact hr.x5
  · rw [gu .x6 (by decide) (by decide)]; exact hr.x6
  · rw [gu .x7 (by decide) (by decide)]; exact hr.x7
  · rw [mu, Mem.readW_writeW_sep (Offset.sep L.Q (d := 96) (n := 8) (e := 104) (k := 8) (by omega_using []) (by omega_using [])
      (by omega_using [])) (by decide), Mem.readW_writeW_self64]
  · rw [mu, Mem.readW_writeW_self64]


/-- The regions the call of `vg_rsa_private_checked_precomputed` reads. -/
abbrev privRdP (L : Lay) : List Region :=
  [L.N, L.E, L.INP, L.PP, L.QQ, L.DP, L.DQ, L.QI, ⟨L.pre, L.prl.toNat * 8⟩, ⟨L.Q + BitVec.ofNat 64 0, 112⟩]

theorem privP_pre (hL : L.Ok) {S : Nat} (hP : L.P = S + 1) (hx : PreX L m₀) {t : State} (hc : Ctx L g vv m₀ t)
    (hr : Ready L t) (h96 : t.mem.readW (L.Q + BitVec.ofNat 64 96) 64 = L.pre)
    (h104 : t.mem.readW (L.Q + BitVec.ofNat 64 104) 64 = L.prl) :
    (Proof.Rsa.privateCheckedPrecomputedContract AArch64.abi (S + 1)).pre
      (t.callEntry.withRegions (privRdP L) (privWr L)) := by
  have hnQ := hL.nQ
  have hpQ := hL.pQ
  rw [hP] at hpQ
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := priv_args hc (privRdP L) (privWr L)
  obtain hlow : (⟨L.Q - BitVec.ofNat 64 (S + 1), S + 1⟩ : Region) = L.LOW := by
    show _ = (⟨L.Q - BitVec.ofNat 64 L.P, L.P⟩ : Region); rw [hP]
  obtain aa : stackArgAddr (t.callEntry.withRegions (privRdP L) (privWr L)) 0 = L.Q + BitVec.ofNat 64 0 := by
    simp only [stackArgAddr, State.withRegions_sp, State.callEntry_sp, hc.sp]
  obtain a12 : stackArg (t.callEntry.withRegions (privRdP L) (privWr L)) 12 = L.pre := by
    rw [VG.Proof.RsaPkcs1Enc.AArch64.Enc.stackArg_ce, hc.sp]; exact h96
  obtain a13 : stackArg (t.callEntry.withRegions (privRdP L) (privWr L)) 13 = L.prl := by
    rw [VG.Proof.RsaPkcs1Enc.AArch64.Enc.stackArg_ce, hc.sp]; exact h104
  obtain arS : Region.Sub ⟨L.Q + BitVec.ofNat 64 0, 112⟩ L.STK := Lay.Ok.sub_stk (by omega_arith)
  obtain lS := Lay.Ok.low_stk (L := L)
  obtain hw : Spec.Rsa.wordsAt t.mem L.pre L.prl.toNat = Spec.Rsa.wordsAt m₀ L.pre L.prl.toNat := by
    have := hx.wp
    simp only [Spec.Rsa.wordsAt]
    refine List.map_congr_left fun i hi => ?_
    obtain hi := List.mem_range.mp hi
    refine hc.frame.readW (r := ⟨L.pre, L.prl.toNat * 8⟩) (Offset.contains_base _ (by omega_using [hi]) (by omega_using [this, hi])) ?_
      (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    exacts [hx.po.symm, hx.pm.symm, hx.ps.symm, hx.pk.symm]
  sig_pre [Proof.Rsa.privateCheckedPrecomputedContract, Proof.Rsa.privateCheckedPrecomputedSig,
    Proof.Rsa.privateCheckedSig, AArch64.abi, AArch64.argRegs, Proof.Rsa.AArch64.stackArgs_fourteen,
    List.append_eq, _root_.List.range, _root_.List.range.loop]
  simp only [hc.sp,
    hr.x0, hr.x1, hr.x2, hr.x3, hr.x4, hr.x5, hr.x6, hr.x7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11,
    a12, a13, aa, hlow, hL.dpl, hL.qil, hL.dql, hc.bytes_ro hL (ro_N L), hc.bytes_ro hL (ro_PP L),
    hc.bytes_ro hL (ro_QQ L), hw]
  refine ⟨by omega_arith, by omega_arith, trivial, trivial,
    hL.oR _ (ro_N L), hL.oR _ (ro_E L), hL.oR _ (ro_INP L), hL.oR _ (ro_PP L), hL.oR _ (ro_QQ L),
    hL.oR _ (ro_DP L), hL.oR _ (ro_DQ L), hL.oR _ (ro_QI L), hL.oS, hx.po, (hL.kO.sub_left arS).symm,
    (hL.sR _ (ro_N L)).symm, (hL.sR _ (ro_E L)).symm, (hL.sR _ (ro_INP L)).symm, (hL.sR _ (ro_PP L)).symm,
    (hL.sR _ (ro_QQ L)).symm, (hL.sR _ (ro_DP L)).symm, (hL.sR _ (ro_DQ L)).symm, (hL.sR _ (ro_QI L)).symm,
    hx.ps, (hL.kS.sub_left arS).symm,
    hL.kO.sub_left lS, (hL.kR _ (ro_N L)).sub_left lS, (hL.kR _ (ro_E L)).sub_left lS,
    (hL.kR _ (ro_INP L)).sub_left lS, (hL.kR _ (ro_PP L)).sub_left lS, (hL.kR _ (ro_QQ L)).sub_left lS,
    (hL.kR _ (ro_DP L)).sub_left lS, (hL.kR _ (ro_DQ L)).sub_left lS, (hL.kR _ (ro_QI L)).sub_left lS,
    hL.kS.sub_left lS, hx.pk.sub_left lS, (hL.fr_low (by omega_arith)).symm,
    hL.bO, hL.bR _ (ro_N L), hL.bR _ (ro_E L), hL.bR _ (ro_INP L), hL.bR _ (ro_PP L), hL.bR _ (ro_QQ L),
    hL.bR _ (ro_DP L), hL.bR _ (ro_DQ L), hL.bR _ (ro_QI L), hL.bS, hx.wp,
    hL.kv, trivial, trivial, hL.el1, hL.elk, hL.pl1, hL.plk, hL.ql1, hL.qlk, trivial, trivial, trivial, hL.slk,
    hx.prlv, hx.key⟩


theorem covers_privP (hx : PreX L m₀) {t : State} (hc : Ctx L g vv m₀ t) :
    Covers (privRdP L ++ privWr L) (t.rd ++ t.wr) ∧ Covers (privWr L) t.wr := by
  obtain z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  rw [hc.rd, hc.wr, hx.x]
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · simp only [privRdP, privWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨L.N, by simp, 0, z _, by simp⟩
    · exact ⟨L.E, by simp, 0, z _, by simp⟩
    · exact ⟨L.INP, by simp, 0, z _, by simp⟩
    · exact ⟨L.PP, by simp, 0, z _, by simp⟩
    · exact ⟨L.QQ, by simp, 0, z _, by simp⟩
    · exact ⟨L.DP, by simp, 0, z _, by simp⟩
    · exact ⟨L.DQ, by simp, 0, z _, by simp⟩
    · exact ⟨L.QI, by simp, 0, z _, by simp⟩
    · exact ⟨⟨L.pre, L.prl.toNat * 8⟩, by simp, 0, z _, by simp⟩
    · exact ⟨L.FR, by simp, 0, rfl, by show 0 + 112 ≤ frameBytes; decide⟩
    · exact ⟨L.OUT, by simp, 0, z _, by simp⟩
    · exact ⟨L.SCR, by simp, 0, z _, by simp⟩
  · simp only [privWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨L.OUT, by simp, 0, z _, by simp⟩
    · exact ⟨L.SCR, by simp, 0, z _, by simp⟩

theorem privP_call (v : PrivPImpl) (hL : L.Ok) (hP : L.P = v.S + 1) (hx : PreX L m₀) {t : State}
    (hc : Ctx L g vv m₀ t) (hr : Ready L t) (h96 : t.mem.readW (L.Q + BitVec.ofNat 64 96) 64 = L.pre)
    (h104 : t.mem.readW (L.Q + BitVec.ofNat 64 104) 64 = L.prl) :
    WP isa (.call v.name v.code) t (Called L g vv m₀) := by
  have hnQ := hL.nQ
  have hdp := v.depth'
  have hpQ := hL.pQ
  rw [hP] at hpQ
  obtain ⟨hcov, hcovw⟩ := covers_privP hx hc
  refine WP.callFV v.verified'.1 (privP_pre hL hP hx hc hr h96 h104) hcov hcovw
    (fun s' hrd hwr hsp hf hcs hvs hpost => ?_) (by omega_arith)
  obtain hlow : Region.Sub (below t.sp (16 * v.code.aarch64Depth)) L.LOW := by
    rw [hc.sp]
    show Region.Sub _ ⟨L.Q - BitVec.ofNat 64 L.P, L.P⟩
    rw [hP]; exact Offset.sub_below _ hdp (by omega_arith)
  obtain hws : ∀ r ∈ privWr L ++ [below t.sp (16 * v.code.aarch64Depth)],
      (Region.Sub r L.OUT ∨ Region.Sub r L.SCR) ∨ Region.Sub r L.LOW := fun r hr => by
    simp only [privWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl (.inl fun _ h => h)
    · exact .inl (.inr fun _ h => h)
    · exact .inr hlow
  obtain hkept : ∀ d, keptOff d → ∀ R ∈ privWr L ++ [below t.sp (16 * v.code.aarch64Depth)],
      Region.Disjoint ⟨L.Q + BitVec.ofNat 64 d, 8⟩ R := fun d hd R hR => by
    rcases hws R hR with (hs | hs) | hs
    · exact hL.kept_buf hd (.inl hs)
    · exact hL.kept_buf hd (.inr (.inr hs))
    · exact (hL.fr_low (by unfold keptOff at hd; omega_arith)).sub_right hs
  obtain hc' : Ctx L g vv m₀ s' :=
    ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp, fun r hr h30 => (hcs r hr h30).trans (hc.cs r hr h30),
      fun r hr => (hvs r hr).trans (hc.vs r hr), hc.kept.frame hf hkept, hc.frame.trans (hf.sub fun r hr => by
        rcases hws r hr with (hs | hs) | hs
        · exact ⟨L.OUT, by simp, hs⟩
        · exact ⟨L.SCR, by simp, hs⟩
        · exact ⟨L.STK, by simp, fun x hx => (Lay.Ok.low_stk (L := L)) x (hs x hx)⟩)⟩
  refine ⟨hc', ?_⟩
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, -, -, -⟩ := priv_args hc (privRdP L) (privWr L)
  have hp := hpost
  sig_post [Proof.Rsa.privateCheckedPrecomputedContract, Proof.Rsa.privateCheckedPrecomputedSig,
    Proof.Rsa.privateCheckedSig, AArch64.abi, AArch64.argRegs, Proof.Rsa.AArch64.stackArgs_fourteen,
    List.append_eq, _root_.List.range, _root_.List.range.loop] at hp
  simp only [hr.x0, hr.x2, hr.x3, hr.x4, hr.x5, hr.x6, a0, a1, a2, a3, a4, a6, a8] at hp
  rw [hc.bytes_ro hL (ro_N L), hc.bytes_ro hL (ro_E L), hc.bytes_ro hL (ro_INP L), hc.bytes_ro hL (ro_PP L),
    hc.bytes_ro hL (ro_QQ L), hc.bytes_ro hL (ro_DP L), hc.bytes_ro hL (ro_DQ L), hc.bytes_ro hL (ro_QI L)] at hp
  exact hp

end

/-! ## The call, narrowed -/

theorem q360 (P : Nat) (s : State) : (lay P s).Q + BitVec.ofNat 64 360 = stackArgAddr s 15 := by
  rw [show (360 : Nat) = 240 + 120 from rfl, ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc, lay_Q]; rfl

theorem q368 (P : Nat) (s : State) : (lay P s).Q + BitVec.ofNat 64 368 = stackArgAddr s 16 := by
  rw [show (368 : Nat) = 240 + 128 from rfl, ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc, lay_Q]; rfl

theorem sub_arg15 (s : State) : Region.Sub ⟨stackArgAddr s 15, 16⟩ ⟨stackArgAddr s 0, 136⟩ :=
  Offset.sub s.sp (d := 120) (n := 16) (e := 0) (k := 136) (by decide) (by decide)

/-- The facts about `pre`, in the layout of the call. -/
theorem preX_of {P : Nat} {s : State} (hD : (decSpec P).pre (s.withRegions (rdD s) s.wr)) (hx : PreD P s) :
    PreX (layW P s (XD s) (stackArg s 15) (stackArg s 16)) s.mem := by
  obtain hL := lay_ok hD
  obtain hsp : P + 240 ≤ s.sp.toNat := spec_sp (s := s.withRegions (rdD s) s.wr) hD
  obtain hQ : (lay P s).Q.toNat = s.sp.toNat - 240 := by
    show (s.sp - BitVec.ofNat 64 240).toNat = _
    rw [BitVec.toNat_sub_of_le (by show 240 ≤ s.sp.toNat; omega_using [hsp])]; rfl
  have hsp2 := hx.sp2
  obtain hO : (layW P s (XD s) (stackArg s 15) (stackArg s 16)).OUT = ⟨s.gpr .x0, (s.gpr .x1).toNat⟩ := by
    have e : (s.gpr .x1).toNat = (s.gpr .x4).toNat := hL.olk
    show (⟨s.gpr .x0, (s.gpr .x4).toNat⟩ : Region) = _; rw [e]
  obtain hK : (layW P s (XD s) (stackArg s 15) (stackArg s 16)).STK =
      ⟨s.sp - BitVec.ofNat 64 (P + 240), P + 240⟩ := by
    show (⟨(lay P s).Q - BitVec.ofNat 64 P, P + 240⟩ : Region) = _; rw [lay_stk]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show XD s = [⟨(lay P s).Q + BitVec.ofNat 64 360, 16⟩, _]; rw [q360]; rfl
  · show (lay P s).Q.toNat + 376 ≤ 2 ^ 64; omega_using [hQ, hsp2]
  · show s.mem.readW ((lay P s).Q + BitVec.ofNat 64 360) 64 = _; rw [q360]; rfl
  · show s.mem.readW ((lay P s).Q + BitVec.ofNat 64 368) 64 = _; rw [q368]; rfl
  · rw [hO]; show Region.Disjoint _ ⟨(lay P s).Q + BitVec.ofNat 64 360, 16⟩
    rw [q360]; exact hx.oa.sub_right (sub_arg15 s)
  · show Region.Disjoint ⟨s.gpr .x2, 8⟩ ⟨(lay P s).Q + BitVec.ofNat 64 360, 16⟩
    rw [q360]; exact hx.ma.sub_right (sub_arg15 s)
  · show Region.Disjoint ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩ ⟨(lay P s).Q + BitVec.ofNat 64 360, 16⟩
    rw [q360]; exact hx.sa.sub_right (sub_arg15 s)
  · rw [hO]; exact hx.op
  · exact hx.mp
  · exact hx.sp
  · rw [hK]; exact hx.kp
  · exact hx.wp
  · exact hx.prl
  · exact hx.key

/-- Running from a state that permits more memory. -/
theorem wp_widen {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) {rd wr : List Region}
    (hc : Covers (s.rd ++ s.wr) (rd ++ wr)) (hw : Covers s.wr wr) :
    WP isa c (s.withRegions rd wr) fun u => ∃ t, Q t ∧ u = t.withRegions rd wr := by
  obtain ⟨tr, t, he, hq⟩ := h
  exact ⟨tr, _, Exec.widen he hc hw, t, hq, rfl⟩

/-- The call, reading only `vg_rsa_pkcs1_decrypt`'s regions and `XD`. -/
def narrowD (s : State) : State := s.withRegions (rdD s ++ XD s) s.wr

theorem narrowD_widen (s : State) : (narrowD s).withRegions s.rd s.wr = s := by
  simp only [narrowD, State.withRegions_withRegions, State.withRegions_self]

theorem narrowD_covers {P : Nat} {s : State} (hx : PreD P s) :
    Covers ((narrowD s).rd ++ (narrowD s).wr) (s.rd ++ s.wr) := by
  refine Covers.of_sub fun r hr => ?_
  obtain self : ∀ r ∈ s.rd ++ s.wr, ∃ r' ∈ s.rd ++ s.wr, ∃ off, r.base = r'.base + BitVec.ofNat 64 off ∧
      off + r.len ≤ r'.len := fun r hr => ⟨r, hr, 0, (BitVec.add_zero _).symm, by omega_using []⟩
  obtain m9 : ∀ r ∈ (rdD s).take 9, ∃ r' ∈ s.rd ++ s.wr, ∃ off, r.base = r'.base + BitVec.ofNat 64 off ∧
      off + r.len ≤ r'.len :=
    fun r hr => self r (by rw [hx.rd]; exact List.mem_append_left _ (List.mem_append_left _ hr))
  obtain ma : (⟨stackArgAddr s 0, 136⟩ : Region) ∈ s.rd ++ s.wr := by rw [hx.rd]; simp
  obtain mp : (⟨stackArg s 15, (stackArg s 16).toNat * 8⟩ : Region) ∈ s.rd ++ s.wr := by rw [hx.rd]; simp
  simp only [narrowD, State.withRegions_rd, State.withRegions_wr, rdD, XD, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)) | hw
  iterate 9 exact m9 _ (by simp [rdD])
  · exact ⟨_, ma, 0, (BitVec.add_zero _).symm, by dsimp only; omega_using []⟩
  · exact ⟨_, ma, 120, by simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat], by dsimp only; omega_using []⟩
  · exact ⟨_, mp, 0, (BitVec.add_zero _).symm, by dsimp only; omega_using []⟩
  · exact self _ (List.mem_append_right _ hw)

/-- After the setup and the moves of `pre` and `pre_len`. -/
abbrev CtxReadyP : Inv := fun L g vv m₀ t => Ctx L g vv m₀ t ∧ Ready L t ∧
  t.mem.readW (L.Q + BitVec.ofNat 64 96) 64 = L.pre ∧ t.mem.readW (L.Q + BitVec.ofNat 64 104) 64 = L.prl ∧
  PreX L m₀

/-- The setup, the moves of `pre` and `pre_len`, and the call, on the
narrowed call: `entry_ok` on the call narrowed further to
`vg_rsa_pkcs1_decrypt`'s regions, widened. -/
theorem blockP_ok {P : Nat} {s : State} (hD : (decSpec P).pre (s.withRegions (rdD s) s.wr))
    (hx : PreD P s) :
    WP isa (.block (setup ++ extraMoves)) (entered (narrowD s)) fun t =>
      CtxReadyP (layW P (narrowD s) (XD s) (stackArg s 15) (stackArg s 16)) (narrowD s).gpr
        (narrowD s).v (narrowD s).mem t := by
  obtain hL := lay_ok hD
  obtain ⟨hrd, hwr⟩ := spec_rdwr hD
  have eN : entered (narrowD s) =
      (entered (s.withRegions (rdD s) s.wr)).withRegions (rdD s ++ XD s) (entered (s.withRegions (rdD s) s.wr)).wr :=
    rfl
  rw [WP.block_append_iff, eN]
  refine WP.mono (wp_widen (entry_ok hD) (rd := rdD s ++ XD s) (wr := (entered (s.withRegions (rdD s) s.wr)).wr)
    (Covers.of_mem fun r hr => by
      rcases List.mem_append.mp hr with h | h
      · exact List.mem_append_left _ (List.mem_append_left _ h)
      · exact List.mem_append_right _ h) (Covers.refl _)) fun u ⟨t, ⟨hc, hr⟩, hu⟩ => ?_
  subst hu
  obtain hL' : (layW P (narrowD s) (XD s) (stackArg s 15) (stackArg s 16)).Ok :=
    hL.withX (XD s) (stackArg s 15) (stackArg s 16)
  obtain hX : PreX (layW P (narrowD s) (XD s) (stackArg s 15) (stackArg s 16)) (narrowD s).mem :=
    preX_of (s := s) hD hx
  obtain hc' : Ctx (layW P (narrowD s) (XD s) (stackArg s 15) (stackArg s 16)) (narrowD s).gpr
      (narrowD s).v (narrowD s).mem (t.withRegions (rdD s ++ XD s) (entered (s.withRegions (rdD s) s.wr)).wr) := by
    refine ⟨?_, ?_, hc.sp, hc.cs, hc.vs, { hc.kept with }, hc.frame⟩
    · show rdD s ++ XD s = _
      rw [show rdD s = (s.withRegions (rdD s) s.wr).rd from rfl, hrd]; rfl
    · rw [State.withRegions_wr, entered_wr P, hwr]; rfl
  exact WP.mono (extra_ok hL' hX hc' { hr with }) fun u ⟨hc'', hr'', h96, h104⟩ =>
    ⟨hc'', hr'', h96, h104, hX⟩

theorem stageP_ok (pv : PrivPImpl) {s : State} (hD : (decSpec (pv.S + 1)).pre (s.withRegions (rdD s) s.wr))
    (hx : PreD (pv.S + 1) s) :
    WP isa (.block (setup ++ extraMoves)) (entered (narrowD s)) fun t =>
      WP isa (.call pv.name pv.code) t
        (Called (layW (pv.S + 1) (narrowD s) (XD s) (stackArg s 15) (stackArg s 16)) (narrowD s).gpr
          (narrowD s).v (narrowD s).mem) :=
  WP.mono (blockP_ok hD hx) fun _ ⟨hc, hr, h96, h104, hX⟩ =>
    privP_call pv ((lay_ok hD).withX (XD s) (stackArg s 15) (stackArg s 16)) rfl hX hc hr h96 h104


theorem post_of {P : Nat} {s s' : State} (h : (decSpec P).post (s.withRegions (rdD s) s.wr) s') :
    (Spec.RsaPkcs1Enc.decryptPrecomputedContract AArch64.abi (P + 240)).post s (s'.withRegions s.rd s.wr) := by
  sig_post [Spec.RsaPkcs1Enc.decryptContract, Spec.RsaPkcs1Enc.decryptSig, AArch64.abi, AArch64.argRegs,
    _root_.List.range, _root_.List.range.loop, List.append_eq] at h
  sig_post [Spec.RsaPkcs1Enc.decryptPrecomputedContract, Spec.RsaPkcs1Enc.decryptPrecomputedSig,
    Spec.RsaPkcs1Enc.decryptSig, AArch64.abi, AArch64.argRegs, stackArgs_seventeen, List.append_eq,
    _root_.List.range, _root_.List.range.loop]
  exact h

theorem decP_correct (v : Compress) (pv : PrivPImpl) (s : State)
    (h : (Spec.RsaPkcs1Enc.decryptPrecomputedContract AArch64.abi (pv.S + 1 + 240)).pre s) :
    ∃ t s', Exec isa (codeP (HH v) pv.name pv.code) s t s' ∧ abiPreserved s s' ∧
      (Spec.RsaPkcs1Enc.decryptPrecomputedContract AArch64.abi (pv.S + 1 + 240)).post s s' := by
  have hS := pv.S15
  obtain ⟨hD, hx⟩ := decSpec_of h
  obtain ⟨t, s', he, ha, hp⟩ := decW_ok v (by omega_using [hS]) (s := narrowD s) (R₀ := rdD s) (X := XD s)
    (pre := stackArg s 15) (prl := stackArg s 16) hD (setup ++ extraMoves) pv.name pv.code (stageP_ok pv hD hx)
  obtain hw := Exec.widen he (narrowD_covers hx) (Covers.refl _)
  rw [narrowD_widen] at hw
  exact ⟨t, _, hw, ha, post_of hp⟩

/-! ## Constant time -/

section
variable {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem}

/-- `n`'s values, the first `2 w` words of `pre`. -/
theorem PreX.pub (hx : PreX L m₀) :
    Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt m₀ L.n L.k.toNat) =
      some (Spec.Rsa.wordsAt m₀ L.pre (Spec.Rsa.precomputedWords L.k.toNat)) := by
  obtain hle : Spec.Rsa.precomputedWords L.k.toNat ≤ L.prl.toNat := by
    rw [hx.prlv]; unfold Spec.Rsa.privatePrecomputedWords; omega_using []
  rw [Proof.Rsa.AArch64.publicPrecompute_of_private hx.key, Proof.Rsa.bytesAt_length',
    show 2 * Spec.Rsa.modulusWords L.k.toNat = Spec.Rsa.precomputedWords L.k.toNat from rfl,
    Proof.Rsa.AArch64.wordsAt_take _ _ hle]

/-- Words of `pre`, in the frames, as on entry. -/
theorem PreX.words (hx : PreX L m₀) {t : State} (hc : Ctx L g vv m₀ t) {n : Nat} (hn : n ≤ L.prl.toNat) :
    Spec.Rsa.wordsAt t.mem L.pre n = Spec.Rsa.wordsAt m₀ L.pre n := by
  have := hx.wp
  simp only [Spec.Rsa.wordsAt]
  refine List.map_congr_left fun i hi => ?_
  obtain hi := List.mem_range.mp hi
  refine hc.frame.readW (r := ⟨L.pre, L.prl.toNat * 8⟩) (Offset.contains_base _ (by omega_using [hn, hi]) (by omega_using [hn, this, hi])) ?_
    (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  exacts [hx.po.symm, hx.pm.symm, hx.ps.symm, hx.pk.symm]

end

theorem privP_pub {L : Lay} {S : Nat} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}
    (hL : L.Ok) (hk : LeakEq L m₁ m₂) {a b : State} (ha : CtxReadyP L g₁ v₁ m₁ a)
    (hb : CtxReadyP L g₂ v₂ m₂ b) :
    (Proof.Rsa.privateCheckedPrecomputedContract AArch64.abi S).pub
      (a.callEntry.withRegions (privRdP L) (privWr L))
      ((b.callEntry.withRegions (privRdP L) (privWr L)).withDit a.dit) := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11⟩ := priv_args ha.1 (privRdP L) (privWr L)
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11⟩ := priv_args hb.1 (privRdP L) (privWr L)
  obtain c12 : stackArg (a.callEntry.withRegions (privRdP L) (privWr L)) 12 = L.pre := by
    rw [VG.Proof.RsaPkcs1Enc.AArch64.Enc.stackArg_ce, ha.1.sp]; exact ha.2.2.1
  obtain c13 : stackArg (a.callEntry.withRegions (privRdP L) (privWr L)) 13 = L.prl := by
    rw [VG.Proof.RsaPkcs1Enc.AArch64.Enc.stackArg_ce, ha.1.sp]; exact ha.2.2.2.1
  obtain d12 : stackArg (b.callEntry.withRegions (privRdP L) (privWr L)) 12 = L.pre := by
    rw [VG.Proof.RsaPkcs1Enc.AArch64.Enc.stackArg_ce, hb.1.sp]; exact hb.2.2.1
  obtain d13 : stackArg (b.callEntry.withRegions (privRdP L) (privWr L)) 13 = L.prl := by
    rw [VG.Proof.RsaPkcs1Enc.AArch64.Enc.stackArg_ce, hb.1.sp]; exact hb.2.2.2.1
  have hxa := ha.2.2.2.2
  have hxb := hb.2.2.2.2
  obtain hle : Spec.Rsa.precomputedWords L.k.toNat ≤ L.prl.toNat := by
    rw [hxa.prlv]; unfold Spec.Rsa.privatePrecomputedWords; omega_using []
  obtain hw : Spec.Rsa.wordsAt a.mem L.pre (Spec.Rsa.precomputedWords L.k.toNat) =
      Spec.Rsa.wordsAt b.mem L.pre (Spec.Rsa.precomputedWords L.k.toNat) := by
    rw [hxa.words ha.1 hle, hxb.words hb.1 hle]
    exact Option.some.inj (hxa.pub.symm.trans (hk.1 ▸ hxb.pub))
  sig_pub [Proof.Rsa.privateCheckedPrecomputedContract, Proof.Rsa.privateCheckedPrecomputedSig,
    Proof.Rsa.privateCheckedSig, AArch64.abi, AArch64.argRegs, Proof.Rsa.AArch64.stackArgs_fourteen,
    List.append_eq, _root_.List.range, _root_.List.range.loop]
  simp only [stackArg_withDit, ha.1.sp, hb.1.sp, ha.2.1.x0, ha.2.1.x1, ha.2.1.x2, ha.2.1.x3, ha.2.1.x4, ha.2.1.x5, ha.2.1.x6,
    ha.2.1.x7, hb.2.1.x0, hb.2.1.x1, hb.2.1.x2, hb.2.1.x3, hb.2.1.x4, hb.2.1.x5, hb.2.1.x6, hb.2.1.x7,
    c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11,
    d12, d13, ha.1.bytes_ro hL (ro_N L), hb.1.bytes_ro hL (ro_N L), ha.1.bytes_ro hL (ro_E L),
    hb.1.bytes_ro hL (ro_E L), hk.1, hk.2, Spec.Rsa.privatePrecomputedLeak, hw, and_self]

theorem privP_ct (pv : PrivPImpl) : RelCT isa (Two pv.S CtxReadyP) (.call pv.name pv.code) (Two pv.S Called) :=
  two_wp (fun e => RelCT.callDit (n := pv.name) pv.verified'.1 pv.verified'.2.1 pv.noDit (fun _ _ h => h)
    (privRdP e.L) (privWr e.L)
    fun _ _ ⟨hL, hP, hk, f₁, f₂⟩ =>
      ⟨privP_pre hL hP f₁.2.2.2.2 f₁.1 f₁.2.1 f₁.2.2.1 f₁.2.2.2.1,
        privP_pre hL hP f₂.2.2.2.2 f₂.1 f₂.2.1 f₂.2.2.1 f₂.2.2.2.1, privP_pub hL hk f₁ f₂,
        (covers_privP f₁.2.2.2.2 f₁.1).1, (covers_privP f₁.2.2.2.2 f₁.1).2,
        (covers_privP f₂.2.2.2.2 f₂.1).1, (covers_privP f₂.2.2.2.2 f₂.1).2⟩)
    fun _ _ _ _ _ hL hP h => privP_call pv hL hP h.2.2.2.2 h.1 h.2.1 h.2.2.1 h.2.2.2.1

/-- The precomputed contract, for the callee's `S + 1` bytes of stack. -/
abbrev decPSpec (S : Nat) : Contract isa := Spec.RsaPkcs1Enc.decryptPrecomputedContract AArch64.abi (S + 1 + 240)

/-- Two calls whose public data agree, narrowed, in the inner frame. -/
def EnteredP (S : Nat) (a b : State) : Prop :=
  ∃ s₁ s₂, (decPSpec S).pre s₁ ∧ (decPSpec S).pre s₂ ∧ (decPSpec S).pub s₁ s₂ ∧
    a = entered (narrowD s₁) ∧ b = entered (narrowD s₂)

/-- The layout of the narrowed call. -/
abbrev layP (S : Nat) (s : State) : Lay := layW (S + 1) (narrowD s) (XD s) (stackArg s 15) (stackArg s 16)

theorem setupP_ct (S : Nat) : RelCT isa (EnteredP S) (.block (setup ++ extraMoves)) (Two S CtxReadyP) := by
  intro a b ta tb a' b' ⟨s₁, s₂, h₁, h₂, hp, ea, eb⟩ e₁ e₂
  subst ea eb
  obtain ⟨hD₁, hx₁⟩ := decSpec_of h₁
  obtain ⟨hD₂, hx₂⟩ := decSpec_of h₂
  sig_pub [Spec.RsaPkcs1Enc.decryptPrecomputedContract, Spec.RsaPkcs1Enc.decryptPrecomputedSig,
    Spec.RsaPkcs1Enc.decryptSig, AArch64.abi, AArch64.argRegs, stackArgs_seventeen, List.append_eq,
    _root_.List.range, _root_.List.range.loop] at hp
  obtain ⟨hsp, hl, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13,
    a14, a15, a16⟩ := hp
  obtain ht := (RelCT.taint (A := taint) (P := fun x y => x.sp = y.sp) (Taint.ofRegs [])
    (fun _ _ h => ⟨h, fun _ hr => False.elim (by simp at hr)⟩) (by taint_decide)
    _ _ _ _ _ _ (by
      show s₁.sp - 16 - BitVec.ofNat 64 frameBytes = s₂.sp - 16 - BitVec.ofNat 64 frameBytes
      rw [hsp]) e₁ e₂).1
  obtain ⟨_, u₁, x₁, y₁⟩ := blockP_ok hD₁ hx₁
  obtain ⟨_, u₂, x₂, y₂⟩ := blockP_ok hD₂ hx₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  obtain e : layP S s₂ = layP S s₁ := by
    simp only [layW, lay, narrowD, XD, State.withRegions_gpr, State.withRegions_sp,
      Proof.Rsa.AArch64.stackArg_withRegions, stackArgAddr, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4,
      a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, hsp]
  obtain hl₁ := (List.append_inj hl (by
    simp only [List.length_map, List.length_append, Proof.Rsa.bytesAt_length', h4, h6])).1
  obtain ⟨hn, he⟩ := VG.Proof.RsaPkcs1Enc.AArch64.Enc.leak_split hl₁
    (by rw [Proof.Rsa.bytesAt_length', Proof.Rsa.bytesAt_length', h4])
  obtain y₂' : CtxReadyP (layP S s₁) (narrowD s₂).gpr (narrowD s₂).v (narrowD s₂).mem b' := e ▸ y₂
  refine ⟨ht, ⟨layP S s₁, (narrowD s₁).gpr, (narrowD s₂).gpr, (narrowD s₁).v, (narrowD s₂).v,
    (narrowD s₁).mem, (narrowD s₂).mem⟩, (lay_ok hD₁).withX _ _ _, rfl, ⟨?_, ?_⟩, y₁, y₂'⟩
  · show Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x3) (s₁.gpr .x4).toNat = Spec.Rsa.bytesAt s₂.mem (s₁.gpr .x3) (s₁.gpr .x4).toNat
    rw [hn, h3, h4]
  · show Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x5) (s₁.gpr .x6).toNat = Spec.Rsa.bytesAt s₂.mem (s₁.gpr .x5) (s₁.gpr .x6).toNat
    rw [he, h5, h6]

/-- The narrowed calls are constant time. -/
theorem decPN_ct (v : Compress) (pv : PrivPImpl) :
    ConstantTime isa (fun a => ∃ s, (decPSpec pv.S).pre s ∧ a = narrowD s)
      (fun a b => ∃ s₁ s₂, (decPSpec pv.S).pre s₁ ∧ (decPSpec pv.S).pre s₂ ∧ (decPSpec pv.S).pub s₁ s₂ ∧
        a = narrowD s₁ ∧ b = narrowD s₂)
      (codeP (HH v) pv.name pv.code) := by
  have hS := pv.S15
  refine RelCT.constantTime (RelCT.pushFrame (fun _ _ ⟨_, _, ⟨s₁, s₂, _, _, hp, e₁, e₂⟩⟩ => by
      subst e₁ e₂
      sig_pub [Spec.RsaPkcs1Enc.decryptPrecomputedContract, Spec.RsaPkcs1Enc.decryptPrecomputedSig,
        Spec.RsaPkcs1Enc.decryptSig, AArch64.abi, AArch64.argRegs, stackArgs_seventeen, List.append_eq,
        _root_.List.range, _root_.List.range.loop] at hp
      exact hp.1) (RelCT.alloc (R := fun _ _ => True) ?_))
  show RelCT isa _ (bodyWith (HH v) (setup ++ extraMoves) pv.name pv.code) _
  rw [body_eq]
  refine ((setupP_ct pv.S).seq ((privP_ct pv).seq ((dBuild_ct pv.S).seq ((hashD_ct (v := v) hS).seq
    ((kdkMac_ct hS).seq ((clLoop_ct hS).seq ((amLoop_ct hS).seq (maskPart_ct.seq (alPart_ct.seq
      (scanPart_ct.seq selPart_ct)))))))))).mono ?_ fun _ _ _ => trivial
  rintro _ _ ⟨_, _, ⟨_, _, ⟨-, -, ⟨s₁, s₂, h₁, h₂, hp, rfl, rfl⟩⟩, rfl, rfl⟩, rfl, rfl⟩
  exact ⟨s₁, s₂, h₁, h₂, hp, rfl, rfl⟩

theorem decP_ct (v : Compress) (pv : PrivPImpl) :
    ConstantTime isa (decPSpec pv.S).pre (decPSpec pv.S).pub (codeP (HH v) pv.name pv.code) := by
  have hS := pv.S15
  refine Proof.Rsa.AArch64.ct_of_narrow narrowD (fun s h => ⟨?_, ?_, Covers.refl _, narrowD_widen s⟩)
    (decPN_ct v pv)
  · obtain ⟨hD, hx⟩ := decSpec_of h
    obtain ⟨t, s', he, -⟩ := decW_ok v (by omega_using [hS]) (s := narrowD s) (R₀ := rdD s) (X := XD s)
      (pre := stackArg s 15) (prl := stackArg s 16) hD (setup ++ extraMoves) pv.name pv.code (stageP_ok pv hD hx)
    exact ⟨t, s', he⟩
  · exact narrowD_covers (decSpec_of h).2

/-! ## `Verified` -/

/-- The stack the function uses: the callee's and the frames'. -/
def decStackP (pv : PrivPImpl) : Nat := pv.stack + 240

theorem decStackP_eq (pv : PrivPImpl) : decStackP pv = pv.S + 1 + 240 := by rw [decStackP, pv.stack_eq]

/-- `vg_rsa_pkcs1_decrypt_precomputed`, with `v` and `pv`. -/
theorem decP_verified (v : Compress) (pv : PrivPImpl)
    (hsat : ∃ s, (Spec.RsaPkcs1Enc.decryptPrecomputedContract AArch64.abi (decStackP pv)).pre s) :
    Verified AArch64.target (codeP (HH v) pv.name pv.code)
      (Spec.RsaPkcs1Enc.decryptPrecomputedContract AArch64.abi (decStackP pv)) := by
  rw [decStackP_eq] at hsat ⊢
  exact ⟨decP_correct v pv, decP_ct v pv, hsat⟩

/-! ## A state that meets the contract -/

open VG.Proof.Rsa.PreKey (keyIn keyMem key_pre_of)

/-- The stack arguments of `preStateD`; the key (`keyMem`) has `n` at
`0x2000`, `p` at `0x4200`, `q` at `0x4300` and `pre` at `0x4800`. -/
def preArgsD : List Nat :=
  [1, 0x4100, 64, 0x4200, 32, 0x4300, 32, 0x4400, 32, 0x4500, 32, 0x4600, 32, 0x20000, 0x420, 0x4800, 24]

def preMemD (a : Addr) : Byte :=
  let i := a.toNat
  bif Nat.ble 0x10000000000 i && Nat.blt i 0x10000000088 then
    BitVec.ofNat 8 (preArgsD.getD ((i - 0x10000000000) / 8) 0 / 256 ^ ((i - 0x10000000000) % 8))
  else bif keyIn i then keyMem a else 0

def preStateD : State where
  gpr r := match r with
    | .x0 => 0x5000 | .x1 => 64 | .x2 => 0x1800 | .x3 => 0x2000 | .x4 => 64 | .x5 => 0x3000 | .x6 => 1
    | .x7 => 0x4000 | _ => 0
  sp := 0x10000000000
  mem := preMemD
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4000, 1⟩, ⟨0x4100, 64⟩, ⟨0x4200, 32⟩, ⟨0x4300, 32⟩, ⟨0x4400, 32⟩,
    ⟨0x4500, 32⟩, ⟨0x4600, 32⟩, ⟨0x4800, 192⟩, ⟨0x10000000000, 136⟩]
  wr := [⟨0x5000, 64⟩, ⟨0x1800, 8⟩, ⟨0x20000, 8448⟩]

theorem preStateD_key : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt preStateD.mem 0x2000 64)
    (Spec.Rsa.bytesAt preStateD.mem 0x4200 32) (Spec.Rsa.bytesAt preStateD.mem 0x4300 32) =
      some (Spec.Rsa.wordsAt preStateD.mem 0x4800 24) :=
  key_pre_of fun a ha => by
    obtain hs : (Nat.ble 0x10000000000 a.toNat && Nat.blt a.toNat 0x10000000088) = false := by
      simp only [keyIn, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at ha
      refine Bool.eq_false_iff.mpr fun h => ?_
      simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
      omega
    show (bif _ then _ else _) = _
    rw [hs, Bool.cond_false, ha, Bool.cond_true]

theorem preD_args : stackArg preStateD 0 = 1 ∧ stackArg preStateD 1 = 0x4100 ∧ stackArg preStateD 2 = 64 ∧
    stackArg preStateD 3 = 0x4200 ∧ stackArg preStateD 4 = 32 ∧ stackArg preStateD 5 = 0x4300 ∧
    stackArg preStateD 6 = 32 ∧ stackArg preStateD 7 = 0x4400 ∧ stackArg preStateD 8 = 32 ∧
    stackArg preStateD 9 = 0x4500 ∧ stackArg preStateD 10 = 32 ∧ stackArg preStateD 11 = 0x4600 ∧
    stackArg preStateD 12 = 32 ∧ stackArg preStateD 13 = 0x20000 ∧ stackArg preStateD 14 = 0x420 ∧
    stackArg preStateD 15 = 0x4800 ∧ stackArg preStateD 16 = 24 := by
  decide

theorem decP_sat (K : Nat) (hK : K ≤ 2 ^ 20) :
    ∃ s, (Spec.RsaPkcs1Enc.decryptPrecomputedContract AArch64.abi (K + 240)).pre s := by
  refine ⟨preStateD, ?_⟩
  sig_pre [Spec.RsaPkcs1Enc.decryptPrecomputedContract, Spec.RsaPkcs1Enc.decryptPrecomputedSig,
    Spec.RsaPkcs1Enc.decryptSig, AArch64.abi, AArch64.argRegs, stackArgs_seventeen, List.append_eq,
    _root_.List.range, _root_.List.range.loop]
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16⟩ := preD_args
  obtain hsp : (0x10000000000 : BitVec 64).toNat = 2 ^ 40 := by decide
  obtain hkb : ((0x10000000000 : BitVec 64) - BitVec.ofNat 64 (K + 239 + 1)).toNat = 2 ^ 40 - (K + 240) := by
    rw [BitVec.toNat_sub, hsp, BitVec.toNat_ofNat]; omega_using [hK]
  obtain ha : stackArgAddr preStateD 0 = 0x10000000000 := by decide
  simp only [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, ha]
  obtain kd : ∀ (b : BitVec 64) (n : Nat), b.toNat + n ≤ 2 ^ 20 →
      Region.Disjoint ⟨0x10000000000 - BitVec.ofNat 64 (K + 239 + 1), K + 239 + 1⟩ ⟨b, n⟩ := fun b n h =>
    Region.disjoint_of_le (.inr (by dsimp only; rw [hkb]; omega_using [hK, h])) (by dsimp only; rw [hkb]; omega_using [hK])
      (by dsimp only; omega_using [h])
  obtain kt : Region.Disjoint ⟨0x10000000000 - BitVec.ofNat 64 (K + 239 + 1), K + 239 + 1⟩ ⟨0x10000000000, 136⟩ :=
    Region.disjoint_of_le (.inl (by dsimp only; rw [hkb, hsp]; omega_using [hK]))
      (by dsimp only; rw [hkb]; omega_using [hK]) (by dsimp only; rw [hsp]; omega_using [])
  sig_and_intros
  rotate_right
  · exact preStateD_key
  all_goals first
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact kd _ _ (by decide)
    | exact kt
    | (rw [hsp]; omega_using [hK])
    | (simp only [Spec.Rsa.lenValid]; decide)

end VG.Proof.RsaPkcs1Enc.AArch64.Dec

end

end

/-!
# `vg_rsa_private_checked` as decryption's callee on AArch64

For each implementation `c` of `vg_rsa_private_crt`
(a variant of `RsaPrivateCrt`), `vg_rsa_private_checked` calling it, the
internal function the padding functions call, is a `PrivImpl`
(`privOf`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64

open VG VG.AArch64

/-- `vg_rsa_private_checked` calling `c`, as decryption's callee. -/
def privOf (c : Proof.Rsa.AArch64.CrtImpl) : PrivImpl where
  name := Proof.Rsa.AArch64.privName c
  code := Proof.Rsa.AArch64.privCode c
  stack := Proof.Rsa.AArch64.stackBytes
  verified := Proof.Rsa.AArch64.code_verified c
  pos := by decide
  depth := by rw [Proof.Rsa.AArch64.privCode_depth]; decide
  spSafe := Code.all_of_forall (fun _ => rfl) _
  noDit := Proof.Rsa.AArch64.privCode_noDit c

theorem stackArgs_fifteen (s : State) :
    List.map (stackArg s) (List.range 15) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11, stackArg s 12, stackArg s 13, stackArg s 14] := rfl

/-- A state meeting decryption's contract with `privOf c`: a 512-bit modulus,
one-byte `e`, `d`, primes, exponents and `qInv`, and the stack arguments at
`0x10000`. -/
def decSatState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 64 | .x2 => 0x1800 | .x3 => 0x2000 | .x4 => 64 | .x5 => 0x3000 | .x6 => 1
    | .x7 => 0x4000 | _ => 0
  sp := 0x10000
  mem a := bif Nat.beq a.toNat 0x10070 then 0x20
    else bif Nat.beq a.toNat 0x10000 then 1 else bif Nat.beq a.toNat 0x10009 then 0x41
    else bif Nat.beq a.toNat 0x10010 then 64 else bif Nat.beq a.toNat 0x10019 then 0x42
    else bif Nat.beq a.toNat 0x10020 then 1 else bif Nat.beq a.toNat 0x10029 then 0x43
    else bif Nat.beq a.toNat 0x10030 then 1 else bif Nat.beq a.toNat 0x10039 then 0x44
    else bif Nat.beq a.toNat 0x10040 then 1 else bif Nat.beq a.toNat 0x10049 then 0x45
    else bif Nat.beq a.toNat 0x10050 then 1 else bif Nat.beq a.toNat 0x10059 then 0x46
    else bif Nat.beq a.toNat 0x10060 then 1 else bif Nat.beq a.toNat 0x1006A then 0x02
    else bif Nat.beq a.toNat 0x10071 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4000, 1⟩, ⟨0x4100, 64⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩, ⟨0x4400, 1⟩,
    ⟨0x4500, 1⟩, ⟨0x4600, 1⟩, ⟨0x10000, 120⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1800, 8⟩, ⟨0x20000, 8448⟩]

theorem dec_sat (c : Proof.Rsa.AArch64.CrtImpl) :
    ∃ s, (Spec.RsaPkcs1Enc.decryptContract AArch64.abi (Dec.decStack (privOf c))).pre s := by
  -- A literal stack lets `sig_sat_check` decide the precondition in the kernel.
  rw [show Dec.decStack (privOf c) = 3488 from rfl]
  sig_implies_sat [Spec.RsaPkcs1Enc.decryptContract, Spec.RsaPkcs1Enc.decryptSig, AArch64.abi, AArch64.argRegs,
    stackArgs_fifteen, List.append_eq, Spec.Rsa.lenValid] [decSatState] using decSatState

/-- `vg_rsa_private_checked_precomputed` calling `c`, as
`vg_rsa_pkcs1_decrypt_precomputed`'s callee. -/
def privPOf (c : Proof.Rsa.AArch64.CrtImpl) : Dec.PrivPImpl where
  name := Proof.Rsa.AArch64.privPName c
  code := Proof.Rsa.AArch64.privPCode c
  stack := Proof.Rsa.AArch64.stackBytes
  verified := Proof.Rsa.AArch64.codeP_verified c
  pos := by decide
  depth := by rw [Proof.Rsa.AArch64.privPCode_depth]; decide
  noDit := Proof.Rsa.AArch64.privPCode_noDit c

theorem decP_sat' (c : Proof.Rsa.AArch64.CrtImpl) :
    ∃ s, (Spec.RsaPkcs1Enc.decryptPrecomputedContract AArch64.abi (Dec.decStackP (privPOf c))).pre s :=
  Dec.decP_sat Proof.Rsa.AArch64.stackBytes (by decide)

end VG.Proof.RsaPkcs1Enc.AArch64
