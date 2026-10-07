import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecCTBase

/-!
# RSAES-PKCS1-v1_5 decryption on AArch64: the calls' arguments

The arguments of each call of SHA-256's and HMAC's functions, from `Post`
and the registers the block before it sets (`initA`, `updA`, `finA`,
`hinitA`, `hfinA`), what each call keeps of `Post` and of the frame's words
from `oI` on (`Weak`, `initW` …), and that two runs with the same layout
make the same call (`initR` …).
-/

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

theorem Weak.trans {t₀ t u : State} (h : Weak L g vv m₀ t₀ t) (h' : Weak L g vv m₀ t u) : Weak L g vv m₀ t₀ u :=
  ⟨h'.1, fun d h₁ h₂ => (h'.2 d h₁ h₂).trans (h.2 d h₁ h₂)⟩

theorem Weak.refl {t : State} (hc : Post L g vv m₀ R EM t) : Weak L g vv m₀ t t := ⟨⟨_, _, hc⟩, fun _ _ _ => rfl⟩

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
  st_o := scD hL (a := sSt) (n := 96) (b := o) (m := 32) (.inl (by unfold sWork sSt at *; omega)) (by decide) ho2
  st_sc := scD hL (a := sSt) (n := 96) (b := sWork) (m := 160) (.inl (by decide)) (by decide) (by decide)
  o_sc := scD hL (a := o) (n := 32) (b := sWork) (m := 160) (.inr ho1) ho2 (by decide)
  sp16 := hc.sp16 hL hP
  stk_st := hc.stk hL hP (a := sSt) (m := 96) (by decide)
  stk_o := hc.stk hL hP (a := o) (m := 32) ho2
  stk_sc := hc.stk hL hP (a := sWork) (m := 160) (by decide)

theorem finW (hL : L.Ok) (hP : 16 ≤ L.P) {t : State} (hc : Post L g vv m₀ R EM t) {o : Nat} (ho2 : o + 32 ≤ scrBytes)
    (a : Proof.Pbkdf2.Md.AArch64.Calls.FinArgs (OK v).stream t (scA L sSt) (scA L o) (scA L sWork)) :
    WP isa (.call (HH v).finN (HH v).finC) t (Weak L g vv m₀ t) :=
  Proof.Pbkdf2.Md.AArch64.Calls.fin_call (OK v).stream a fun _ a' _ =>
    hc.weak hL hP a' fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact scSub (a := sSt) (n := 96) (by decide)
      · exact scSub (a := o) (n := 32) ho2
      · exact scSub (a := sWork) (n := 160) (by decide)

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
  cr := Covers.right (scCov hL hc.ctx (by omega))
  cw := (scCov hL hc.ctx (a := sSt) (n := 96) (by decide)).cons
    ((scCov hL hc.ctx (a := sOuter) (n := 96) (by decide)).cons
      ((scCov hL hc.ctx (a := sWork) (n := 832) (by decide)).cons Covers.nil))
  i_o := scD hL (a := sSt) (n := 96) (b := sOuter) (m := 96) (.inl (by decide)) (by decide) (by decide)
  i_s := scD hL (a := sSt) (n := 96) (b := sWork) (m := 832) (.inl (by decide)) (by decide) (by decide)
  o_s := scD hL (a := sOuter) (n := 96) (b := sWork) (m := 832) (.inl (by decide)) (by decide) (by decide)
  k_i := scD hL (b := sSt) (m := 96) (.inr (by unfold sSt; omega)) hk2 (by decide)
  k_o := scD hL (b := sOuter) (m := 96) (.inr (by unfold sOuter; omega)) hk2 (by decide)
  k_s := scD hL (b := sWork) (m := 832) (.inr (by unfold sWork; omega)) hk2 (by decide)
  sp16 := hc.sp16 hL hP
  stk_i := hc.stk hL hP (a := sSt) (m := 96) (by decide)
  stk_o := hc.stk hL hP (a := sOuter) (m := 96) (by decide)
  stk_k := hc.stk hL hP hk2
  stk_s := hc.stk hL hP (a := sWork) (m := 832) (by decide)
  scnw := by
    show (scA L sWork).toNat + 832 ≤ 2 ^ 64
    rw [scA_toNat hL (by decide)]; have := hL.bS; have := hL.s8192; unfold sWork; omega

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
  i_o := scD hL (a := sSt) (n := 96) (b := o) (m := 32) (.inl (by unfold sSt; omega)) (by decide) ho2
  i_s := scD hL (a := sSt) (n := 96) (b := sWork) (m := 832) (.inl (by decide)) (by decide) (by decide)
  u_o := scD hL (a := sOuter) (n := 96) (b := o) (m := 32) (.inl (by unfold sOuter; omega)) (by decide) ho2
  u_s := scD hL (a := sOuter) (n := 96) (b := sWork) (m := 832) (.inl (by decide)) (by decide) (by decide)
  o_s := scD hL (a := o) (n := 32) (b := sWork) (m := 832) (.inr (by unfold sWork; omega)) ho2 (by decide)
  sp16 := hc.sp16 hL hP
  stk_i := hc.stk hL hP (a := sSt) (m := 96) (by decide)
  stk_u := hc.stk hL hP (a := sOuter) (m := 96) (by decide)
  stk_o := hc.stk hL hP (a := o) (m := 32) ho2
  stk_s := hc.stk hL hP (a := sWork) (m := 832) (by decide)
  scnw := by
    show (scA L sWork).toNat + 832 ≤ 2 ^ 64
    rw [scA_toNat hL (by decide)]; have := hL.bS; have := hL.s8192; unfold sWork; omega

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
