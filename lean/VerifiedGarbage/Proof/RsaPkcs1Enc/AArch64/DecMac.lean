module

import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecD
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hashes.Sha256
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCall
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Attr.Core
import Aesop.BuiltinRules
import Mathlib.Tactic.ToAdditive

/-! ### `RsaPkcs1Enc.AArch64.DecHash`, which this module and modules that import it used -/

section

/-!
# RSAES-PKCS1-v1_5 decryption on AArch64: `DH = SHA256(D)`

SHA-256's functions, with an implementation `v` of its compression function
(`HH v`), and what is proven of them; the blocks setting the calls'
arguments, and the hash of `D` (`hashD_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Decrypt
open VG.Proof.Sha256.AArch64 (Compress)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (initG finG After)

variable (v : Compress)

/-- SHA-256's functions, and what is proven of them. -/
abbrev HH : Impl.Pbkdf2.Md.AArch64.Hash := Proof.Pbkdf2.Md.AArch64.Sha256.hash v
abbrev OK : HashOK (HH v) := Proof.Pbkdf2.Md.AArch64.Sha256.ok v

theorem hI : Verified AArch64.target (HH v).hmacInit (initG (OK v).SH (HH v).W) :=
  Proof.Pbkdf2.Md.AArch64.hmacInit_ok (OK v) Proof.Pbkdf2.Md.AArch64.Sha256.coreOK
    Proof.Pbkdf2.Md.AArch64.Sha256.satI

theorem hF : Verified AArch64.target (HH v).hmacFin (finG (OK v).SH (HH v).W) :=
  Proof.Pbkdf2.Md.AArch64.hmacFin_ok (OK v) Proof.Pbkdf2.Md.AArch64.Sha256.coreOK
    Proof.Pbkdf2.Md.AArch64.Sha256.satF

theorem hId : (HH v).hmacInit.aarch64Depth ≤ 1 :=
  Proof.Pbkdf2.Md.AArch64.hmacInit_fdepth (OK v).stream.initDepth v.noFrames

theorem hFd : (HH v).hmacFin.aarch64Depth ≤ 1 :=
  Proof.Pbkdf2.Md.AArch64.hmacFin_fdepth (OK v).stream.finDepth v.noFrames

/-- The sizes. -/
theorem sizes : (HH v).S = 96 ∧ (HH v).W = 104 ∧ (HH v).D = 32 ∧ (HH v).P.B = 64 ∧ (HH v).stream.S = 96 ∧
    (HH v).stream.F = 32 ∧ (HH v).stream.D = 32 ∧ (OK v).stream.Wb = 160 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

variable {v}

/-! ## The arguments -/

/-- A block that changes only argument registers: what stays. -/
structure Same (t u : State) : Prop where
  rd : u.rd = t.rd
  wr : u.wr = t.wr
  sp : u.sp = t.sp
  v : u.v = t.v
  mem : u.mem = t.mem
  cs : ∀ r ∈ preserved, u.gpr r = t.gpr r

theorem Post.same {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {R : BitVec 64}
    {EM : List Byte} {t u : State} (hc : Post L g vv m₀ R EM t) (h : Same t u) : Post L g vv m₀ R EM u :=
  hc.regs h.rd h.wr h.sp h.mem h.v fun r hr _ => h.cs r hr

theorem preserved_cases {P : Reg → Prop} (h19 : P .x19) (h20 : P .x20) (h21 : P .x21) (h22 : P .x22)
    (h23 : P .x23) (h24 : P .x24) (h25 : P .x25) (h26 : P .x26) (h27 : P .x27) (h28 : P .x28) (h30 : P .x30) :
    ∀ r ∈ preserved, P r := by
  intro r hr
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- The frame's slots are readable. -/
abbrev Slots (t : State) (Q : Addr) : Prop := ∀ d, d + 8 ≤ 224 → InRegions (t.rd ++ t.wr) (Q + BitVec.ofNat 64 d) 8

theorem shaInitArgs_ok {t : State} {Q : Addr} (hsp : t.sp = Q) (h : Slots t Q) :
    WP isa (.block shaInitArgs) t fun u => Same t u ∧
      u.gpr .x0 = t.mem.readW (Q + BitVec.ofNat 64 oScr) 64 + BitVec.ofNat 64 sSt := by
  have h184 := h 184 (by decide)
  apply WP.of_runBlock
  simp only [shaInitArgs, scr, runBlock_cons, runStep_some, runBlock_nil, exec, State.read, State.load, Size.bits,
    BitVec.setWidth_eq, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self, ite_true, hsp, oScr, sSt, Option.map_some,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_write, h184]
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, preserved_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩, rfl⟩

/-- A word of the frame. -/
abbrev slot (t : State) (Q : Addr) (d : Nat) : BitVec 64 := t.mem.readW (Q + BitVec.ofNat 64 d) 64

theorem shaUpdArgs_ok {t : State} {Q : Addr} (hsp : t.sp = Q) (h : Slots t Q) :
    WP isa (.block shaUpdArgs) t fun u => Same t u ∧ u.gpr .x0 = slot t Q oScr + BitVec.ofNat 64 sSt ∧
      u.gpr .x1 = 0 ∧ u.gpr .x2 = slot t Q oScr + BitVec.ofNat 64 sD ∧ u.gpr .x3 = slot t Q oK ∧
      u.gpr .x4 = slot t Q oScr + BitVec.ofNat 64 sWork := by
  have h184 := h 184 (by decide)
  have h136 := h 136 (by decide)
  apply WP.of_runBlock
  simp only [shaUpdArgs, scr, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.read, State.load, Size.bits, BitVec.setWidth_eq, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self,
    ite_true, hsp, oScr, oK, sSt, sD, sWork, Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_write,
    RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, h184, h136]
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, preserved_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩, rfl, rfl, rfl,
    rfl, rfl⟩

theorem shaFinArgs_ok {t : State} {Q : Addr} (hsp : t.sp = Q) (h : Slots t Q) :
    WP isa (.block shaFinArgs) t fun u => Same t u ∧ u.gpr .x0 = slot t Q oScr + BitVec.ofNat 64 sSt ∧
      u.gpr .x1 = slot t Q oK ∧ u.gpr .x2 = slot t Q oScr + BitVec.ofNat 64 sDH ∧
      u.gpr .x3 = slot t Q oScr + BitVec.ofNat 64 sWork := by
  have h184 := h 184 (by decide)
  have h136 := h 136 (by decide)
  apply WP.of_runBlock
  simp only [shaFinArgs, scr, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.read, State.load, Size.bits, BitVec.setWidth_eq, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self,
    ite_true, hsp, oScr, oK, sSt, sDH, sWork, Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_write,
    RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, h184, h136]
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, preserved_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩, rfl, rfl, rfl, rfl⟩

/-! ## The hash of `D` -/

theorem bytes_keep {ws : List Region} {m m' : Mem} (hf : Frame ws m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ ws, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' p n = Spec.Rsa.bytesAt m p n :=
  Enc.bytesAt_eq fun _ hi => hf.bytes (R := ⟨p, n⟩) hd hn hi

section
variable {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {R : BitVec 64} {EM : List Byte}

theorem Post.slots {t : State} (hc : Post L g vv m₀ R EM t) : Slots t L.Q := fun _ hd =>
  hc.ctx.inFrR (by unfold frameBytes; omega_using [hd])

theorem Post.sp16 (hL : L.Ok) (hP : 16 ≤ L.P) {t : State} (hc : Post L g vv m₀ R EM t) : 16 ≤ t.sp.toNat := by
  rw [hc.ctx.sp]; have := hL.pQ; omega_using [hP, this]

/-- The 16 bytes below the stack pointer, from `Post`, miss a range of `scratch`. -/
theorem Post.stk (hL : L.Ok) (hP : 16 ≤ L.P) {t : State} (hc : Post L g vv m₀ R EM t) {a m : Nat}
    (ha : a + m ≤ scrBytes) : (below t.sp 16).Disjoint ⟨scA L a, m⟩ := by
  rw [hc.ctx.sp]; exact stkD hL hP ha

/-- A range of `scratch` that a call changing only `ws` and the stack misses keeps its bytes. -/
theorem Post.keep (hL : L.Ok) (hP : 16 ≤ L.P) {t t' : State} (hc : Post L g vv m₀ R EM t) {ws : List Region}
    (h : After t ws t') {a n : Nat} (ha : a + n ≤ scrBytes) (hd : ∀ r ∈ ws, Region.Disjoint ⟨scA L a, n⟩ r) :
    Spec.Rsa.bytesAt t'.mem (scA L a) n = Spec.Rsa.bytesAt t.mem (scA L a) n :=
  bytes_keep h.frame (fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact hd r hr
    · rw [List.mem_singleton.mp hr]; exact (hc.stk hL hP ha).symm) (by unfold scrBytes at ha; omega_using [ha])

end

/-- After `hashD`: `DH = SHA256(D)` at `scratch + sDH`. -/
structure HD (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (R : BitVec 64)
    (EM : List Byte) (t : State) : Prop where
  post : Post L g vv m₀ R EM t
  dh : Spec.Rsa.bytesAt t.mem (scA L sDH) 32 =
    Spec.Sha256.hash (Spec.Rsa.i2osp (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m₀ L.d L.dl.toNat)) L.k.toNat)

theorem hashD_ok {L : Lay} (hL : L.Ok) (hP : 16 ≤ L.P) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem}
    {R : BitVec 64} {EM : List Byte} {t : State} (h : DB L g vv m₀ R EM t) :
    WP isa (hashD (HH v)) t (HD L g vv m₀ R EM) := by
  have hk := hL.k1024
  have hc := h.post
  -- `init`
  refine WP.seq (WP.mono (shaInitArgs_ok hc.ctx.sp hc.slots) fun t₁ ⟨S₁, x0₁⟩ => ?_)
  have hc₁ := hc.same S₁
  simp only [hc.ctx.kept.scr] at x0₁
  refine WP.seq (Proof.Pbkdf2.Md.AArch64.Calls.init_call (OK v).stream x0₁
    (scCov hL hc₁.ctx (a := sSt) (n := 96) (Nat.le_of_ble_eq_true rfl)) fun t₂ a₂ hr₂ => ?_)
  have hc₂ := hc₁.after hL hP a₂ fun r hr => by rw [List.mem_singleton.mp hr]; exact scSub (Nat.le_of_ble_eq_true rfl)
  have hD₂ : Spec.Rsa.bytesAt t₂.mem (scA L sD) L.k.toNat = Spec.Rsa.bytesAt t.mem (scA L sD) L.k.toNat := by
    rw [hc₁.keep hL hP a₂ (by unfold sD scrBytes; omega_using [hk]) fun r hr => by
      rw [List.mem_singleton.mp hr]; exact scD hL (.inr (Nat.le_of_ble_eq_true rfl)) (by unfold sD scrBytes; omega_using [hk]) (Nat.le_of_ble_eq_true rfl),
      S₁.mem]
  -- `update`
  refine WP.seq (WP.mono (shaUpdArgs_ok hc₂.ctx.sp hc₂.slots) fun t₃ ⟨S₃, x0₃, x1₃, x2₃, x3₃, x4₃⟩ => ?_)
  have hc₃ := hc₂.same S₃
  simp only [slot, hc₂.ctx.kept.scr, hc₂.ctx.kept.k] at x0₃ x2₃ x3₃ x4₃
  refine WP.seq (Proof.Pbkdf2.Md.AArch64.Calls.upd_call (OK v).stream (len := L.k.toNat)
    { x0 := x0₃, x2 := x2₃, x3 := by rw [x3₃], x4 := x4₃
      cd := Covers.right (scCov hL hc₃.ctx (by unfold sD scrBytes; omega_using [hk]))
      cw := Covers.pair (scCov hL hc₃.ctx (a := sSt) (n := 96) (Nat.le_of_ble_eq_true rfl))
        (scCov hL hc₃.ctx (a := sWork) (n := 160) (Nat.le_of_ble_eq_true rfl))
      st_sc := scD hL (.inl (Nat.le_of_ble_eq_true rfl)) (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
      d_st := scD hL (.inr (Nat.le_of_ble_eq_true rfl)) (by unfold sD scrBytes; omega_using [hk]) (Nat.le_of_ble_eq_true rfl)
      d_sc := scD hL (.inr (Nat.le_of_ble_eq_true rfl)) (by unfold sD scrBytes; omega_using [hk]) (Nat.le_of_ble_eq_true rfl)
      sp16 := hc₃.sp16 hL hP
      stk_st := hc₃.stk hL hP (Nat.le_of_ble_eq_true rfl)
      stk_d := hc₃.stk hL hP (by unfold sD scrBytes; omega_using [hk])
      stk_sc := hc₃.stk hL hP (Nat.le_of_ble_eq_true rfl) } fun t₄ a₄ hu₄ => ?_)
  have hc₄ := hc₃.after hL hP a₄ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact scSub (Nat.le_of_ble_eq_true rfl)
    · exact scSub (Nat.le_of_ble_eq_true rfl)
  have hr₄ := hu₄ [] (by rw [S₃.mem]; exact hr₂) (by rw [x1₃]; rfl)
  -- `finalize`
  refine WP.seq (WP.mono (shaFinArgs_ok hc₄.ctx.sp hc₄.slots) fun t₅ ⟨S₅, x0₅, x1₅, x2₅, x3₅⟩ => ?_)
  have hc₅ := hc₄.same S₅
  simp only [slot, hc₄.ctx.kept.scr, hc₄.ctx.kept.k] at x0₅ x1₅ x2₅ x3₅
  refine Proof.Pbkdf2.Md.AArch64.Calls.fin_call (OK v).stream
    { x0 := x0₅, x2 := x2₅, x3 := x3₅
      cw := (scCov hL hc₅.ctx (a := sSt) (n := 96) (Nat.le_of_ble_eq_true rfl)).cons
        ((scCov hL hc₅.ctx (a := sDH) (n := 32) (Nat.le_of_ble_eq_true rfl)).cons
          ((scCov hL hc₅.ctx (a := sWork) (n := 160) (Nat.le_of_ble_eq_true rfl)).cons Covers.nil))
      st_o := scD hL (.inl (Nat.le_of_ble_eq_true rfl)) (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
      st_sc := scD hL (.inl (Nat.le_of_ble_eq_true rfl)) (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
      o_sc := scD hL (.inr (Nat.le_of_ble_eq_true rfl)) (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
      sp16 := hc₅.sp16 hL hP
      stk_st := hc₅.stk hL hP (Nat.le_of_ble_eq_true rfl)
      stk_o := hc₅.stk hL hP (Nat.le_of_ble_eq_true rfl)
      stk_sc := hc₅.stk hL hP (Nat.le_of_ble_eq_true rfl) } fun t₆ a₆ hf₆ => ?_
  have hc₆ := hc₅.after hL hP a₆ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact scSub (Nat.le_of_ble_eq_true rfl)
    · exact scSub (Nat.le_of_ble_eq_true rfl)
    · exact scSub (Nat.le_of_ble_eq_true rfl)
  refine ⟨hc₆, ?_⟩
  have := hf₆ _ (by rw [S₅.mem]; exact hr₄) (by simp [Spec.Sha256.bytesAt]; omega_using [])
    (by rw [x1₅]; simp [Spec.Sha256.bytesAt])
  obtain ⟨-, -, -, -, -, hF, hD, -⟩ := sizes v
  rw [hF, hD, List.take_of_length_le (by simp [Spec.Sha256.bytesAt])] at this
  rw [show Spec.Rsa.bytesAt t₆.mem (scA L sDH) 32 = Spec.Sha256.bytesAt t₆.mem (scA L sDH) 32 from rfl, this]
  show Spec.Sha256.hash ([] ++ Spec.Sha256.bytesAt t₃.mem (scA L sD) L.k.toNat) = _
  rw [List.nil_append, show Spec.Sha256.bytesAt t₃.mem (scA L sD) L.k.toNat =
    Spec.Rsa.bytesAt t₃.mem (scA L sD) L.k.toNat from rfl, S₃.mem, hD₂, h.D]

end VG.Proof.RsaPkcs1Enc.AArch64.Dec

end

end

/-!
# RSAES-PKCS1-v1_5 decryption on AArch64: the HMACs

The calls of an HMAC with a 32-byte key in `scratch`, as the key derivation
key and each block of IRPRF make them: HMAC's `init` (`mac_init`), the
streaming `update` (`mac_upd`) and HMAC's `finalize` (`mac_fin`). They write
the first 1024 bytes of `scratch` (the states and the working space) and the
output; every other range of `scratch` keeps its bytes (`Keep`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Decrypt
open VG.Proof.Sha256.AArch64 (Compress)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (initG finG After)

variable {v : Compress} {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {R : BitVec 64}
  {EM : List Byte}

/-- The ranges of `scratch` from 1024 on, but the output `[o, o + n)`, keep their bytes, and the frame's
words from `oI` on theirs. -/
structure Keep (L : Lay) (o n : Nat) (m m' : Mem) : Prop where
  scr : ∀ a l, 1024 ≤ a → a + l ≤ scrBytes → (a + l ≤ o ∨ o + n ≤ a) →
    Spec.Rsa.bytesAt m' (scA L a) l = Spec.Rsa.bytesAt m (scA L a) l
  slot : ∀ d, oI ≤ d → d + 8 ≤ frameBytes →
    m'.readW (L.Q + BitVec.ofNat 64 d) 64 = m.readW (L.Q + BitVec.ofNat 64 d) 64

theorem Keep.trans {o n : Nat} {m m' m'' : Mem} (h : Keep L o n m m') (h' : Keep L o n m' m'') : Keep L o n m m'' :=
  ⟨fun a l h₁ h₂ h₃ => (h'.scr a l h₁ h₂ h₃).trans (h.scr a l h₁ h₂ h₃),
    fun d h₁ h₂ => (h'.slot d h₁ h₂).trans (h.slot d h₁ h₂)⟩

theorem Keep.of_eq {o n : Nat} {m m' : Mem} (h : m' = m) : Keep L o n m m' :=
  ⟨fun _ _ _ _ _ => by rw [h], fun _ _ _ => by rw [h]⟩

/-- The frame's words miss what a call writing only in `scratch` (and below the frame) writes. -/
theorem Post.slotKeep (hL : L.Ok) (hP : 16 ≤ L.P) {t t' : State} (hc : Post L g vv m₀ R EM t) {ws : List Region}
    (h : After t ws t') (hs : ∀ r ∈ ws, Region.Sub r L.SC) {d : Nat} (hd : d + 8 ≤ frameBytes) :
    t'.mem.readW (L.Q + BitVec.ofNat 64 d) 64 = t.mem.readW (L.Q + BitVec.ofNat 64 d) 64 :=
  h.frame.readW (Region.contains_self _ _) (fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact hL.stk_buf (by unfold frameBytes at hd; omega_arith) (.inr (.inr (sub_trans (hs r hr) hL.sc_sub)))
    · rw [List.mem_singleton.mp hr, hc.ctx.sp]
      exact (hL.fr_low (by unfold frameBytes at hd; omega_arith)).sub_right
        (Offset.sub_below _ hP (by have := hL.pQ; omega_arith))) (by decide)

/-- A call writing below 1024 in `scratch` keeps the rest. -/
theorem Post.keepLow (hL : L.Ok) (hP : 16 ≤ L.P) {t t' : State} (hc : Post L g vv m₀ R EM t) {ws : List Region}
    (h : After t ws t') (hs : ∀ r ∈ ws, ∃ a n, a + n ≤ 1024 ∧ r = ⟨scA L a, n⟩) (o n : Nat) :
    Keep L o n t.mem t'.mem :=
  ⟨fun a l h₁ h₂ _ => hc.keep hL hP h h₂ fun r hr => by
    obtain ⟨b, k, hb, rfl⟩ := hs r hr
    exact scD hL (.inr (by omega_arith)) h₂ (by unfold scrBytes; omega_arith),
   fun _ _ hd => hc.slotKeep hL hP h (fun r hr => by
    obtain ⟨b, k, hb, rfl⟩ := hs r hr
    exact scSub (by unfold scrBytes; omega_arith)) hd⟩

/-- The streaming state at `scratch + a` represents what it did, if a call
missed it. -/
theorem Post.repr (hL : L.Ok) (hP : 16 ≤ L.P) {t t' : State} (hc : Post L g vv m₀ R EM t) {ws : List Region}
    (h : After t ws t') {a : Nat} (ha : a + 96 ≤ scrBytes)
    (hd : ∀ r ∈ ws, Region.Disjoint ⟨scA L a, 96⟩ r) {msg : List Byte}
    (hr : (OK v).SH.Repr t.mem (scA L a) msg) : (OK v).SH.Repr t'.mem (scA L a) msg :=
  (OK v).stream.repr _ _ _ _ _ (fun i hi => h.frame.bytes (R := ⟨scA L a, 96⟩) (fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact hd r hr
    · rw [List.mem_singleton.mp hr]; exact (hc.stk hL hP ha).symm) (Nat.le_of_ble_eq_true rfl)
    (Nat.lt_of_lt_of_le hi (Nat.le_of_ble_eq_true rfl))) hr

theorem blockKey_length {key : List Byte} (h : key.length ≤ 64) :
    (Spec.Hmac.blockKey Spec.Hmac.sha256 key).length = 64 := by
  have : ¬ 64 < key.length := by omega_arith
  simp only [Spec.Hmac.blockKey, Spec.Hmac.sha256, this, ite_false, List.length_append, List.length_replicate]
  omega_arith

/-! ## The arguments -/

theorem macInitArgs_ok {t : State} {Q : Addr} (hsp : t.sp = Q) (h : Slots t Q) (key : Nat) (hk : key < 4096) :
    WP isa (.block (macInitArgs key)) t fun u => Same t u ∧ u.gpr .x0 = slot t Q oScr + BitVec.ofNat 64 sSt ∧
      u.gpr .x1 = slot t Q oScr + BitVec.ofNat 64 sOuter ∧ u.gpr .x2 = slot t Q oScr + BitVec.ofNat 64 key ∧
      u.gpr .x3 = BitVec.ofNat 64 32 ∧ u.gpr .x4 = slot t Q oScr + BitVec.ofNat 64 sWork := by
  have h184 := h 184 (by decide)
  apply WP.of_runBlock
  simp only [macInitArgs, scr, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.read, State.load, Size.bits, BitVec.setWidth_eq, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self,
    ite_true, hsp, oScr, sSt, sOuter, sWork, hk, Option.map_some, Option.some.injEq, exists_eq_left',
    RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, h184]
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, preserved_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩, rfl, rfl, rfl,
    rfl, rfl⟩

theorem scA_toNat (hL : L.Ok) {a : Nat} (ha : a ≤ scrBytes) : (scA L a).toNat = L.scr.toNat + a := by
  have := hL.bS; have := hL.s8192
  rw [Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (by unfold scrBytes at ha; omega_arith),
    Nat.mod_eq_of_lt (by unfold scrBytes at ha; omega_arith)]

/-! ## HMAC's `init` -/

/-- After HMAC's `init` with the key `k0` (padded), from `t`. -/
structure MacInit (v : Compress) (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem)
    (R : BitVec 64) (EM : List Byte) (k0 : List Byte) (t u : State) : Prop where
  post : Post L g vv m₀ R EM u
  inner : (OK v).SH.Repr u.mem (scA L sSt) (Spec.Hmac.xorPad k0 Spec.Hmac.ipad)
  outer : (OK v).SH.Repr u.mem (scA L sOuter) (Spec.Hmac.xorPad k0 Spec.Hmac.opad)
  keep : Keep L 0 0 t.mem u.mem

theorem mac_init (hL : L.Ok) (hP : 16 ≤ L.P) {t : State} (hc : Post L g vv m₀ R EM t) {key : Nat}
    (hk1 : 1024 ≤ key) (hk2 : key + 32 ≤ scrBytes) {rest : Prog isa} {Q' : State → Prop}
    (hrest : ∀ u, MacInit v L g vv m₀ R EM
      (Spec.Hmac.blockKey Spec.Hmac.sha256 (Spec.Rsa.bytesAt t.mem (scA L key) 32)) t u → WP isa rest u Q') :
    WP isa (.seq (.block (macInitArgs key)) (.seq (.call (HH v).hmacInitN (HH v).hmacInit) rest)) t Q' := by
  have hs := hL.s8192
  refine WP.seq (WP.mono (macInitArgs_ok hc.ctx.sp hc.slots key (by unfold scrBytes at hk2; omega_arith))
    fun t₁ ⟨S₁, x0, x1, x2, x3, x4⟩ => ?_)
  have hc₁ := hc.same S₁
  simp only [hc.ctx.kept.scr] at x0 x1 x2 x4
  refine WP.seq (Proof.Pbkdf2.Md.AArch64.Pbk.hinit_call (OK v) (hI v) (hId v) (kl := 32)
    { x0 := x0, x1 := x1, x2 := x2, x3 := by rw [x3]; rfl, x4 := x4
      klB := Nat.le_of_ble_eq_true rfl
      cr := Covers.right (scCov hL hc₁.ctx (by omega_arith))
      cw := (scCov hL hc₁.ctx (a := sSt) (n := 96) (by decide)).cons
        ((scCov hL hc₁.ctx (a := sOuter) (n := 96) (by decide)).cons
          ((scCov hL hc₁.ctx (a := sWork) (n := 832) (by decide)).cons Covers.nil))
      i_o := scD hL (a := sSt) (n := 96) (b := sOuter) (m := 96) (.inl (by decide)) (by decide) (by decide)
      i_s := scD hL (a := sSt) (n := 96) (b := sWork) (m := 832) (.inl (by decide)) (by decide) (by decide)
      o_s := scD hL (a := sOuter) (n := 96) (b := sWork) (m := 832) (.inl (by decide)) (by decide) (by decide)
      k_i := scD hL (b := sSt) (m := 96) (.inr (by unfold sSt; omega_arith)) hk2 (by decide)
      k_o := scD hL (b := sOuter) (m := 96) (.inr (by unfold sOuter; omega_arith)) hk2 (by decide)
      k_s := scD hL (b := sWork) (m := 832) (.inr (by unfold sWork; omega_arith)) hk2 (by decide)
      sp16 := hc₁.sp16 hL hP
      stk_i := hc₁.stk hL hP (a := sSt) (m := 96) (by decide)
      stk_o := hc₁.stk hL hP (a := sOuter) (m := 96) (by decide)
      stk_k := hc₁.stk hL hP hk2
      stk_s := hc₁.stk hL hP (a := sWork) (m := 832) (by decide)
      scnw := by
        show (scA L sWork).toNat + 832 ≤ 2 ^ 64
        rw [scA_toNat hL (by decide)]; have := hL.bS; unfold sWork; omega_arith }
    fun t₂ a₂ hi₂ ho₂ => hrest t₂ ⟨hc₁.after hL hP a₂ fun r hr => ?_, ?_, ?_, ?_⟩)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact scSub (a := sSt) (n := 96) (by decide)
    · exact scSub (a := sOuter) (n := 96) (by decide)
    · exact scSub (a := sWork) (n := 832) (by decide)
  · rw [S₁.mem] at hi₂; exact hi₂
  · rw [S₁.mem] at ho₂; exact ho₂
  · refine (Keep.of_eq S₁.mem).trans (hc₁.keepLow hL hP a₂ (fun r hr => ?_) 0 0)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨sSt, 96, by decide, rfl⟩
    · exact ⟨sOuter, 96, by decide, rfl⟩
    · exact ⟨sWork, 832, by decide, rfl⟩

/-! ## `update` -/

theorem mac_upd (hL : L.Ok) (hP : 16 ≤ L.P) {t : State} (hc : Post L g vv m₀ R EM t) {d : Addr} {n : Nat}
    (hx0 : t.gpr .x0 = scA L sSt) (hx1 : t.gpr .x1 = BitVec.ofNat 64 64) (hx2 : t.gpr .x2 = d)
    (hx3 : (t.gpr .x3).toNat = n) (hx4 : t.gpr .x4 = scA L sWork) (hcd : Covers [⟨d, n⟩] (t.rd ++ t.wr))
    (hds : ∀ a l, a + l ≤ 1024 → Region.Disjoint ⟨d, n⟩ ⟨scA L a, l⟩) (hdk : (below L.Q 16).Disjoint ⟨d, n⟩)
    {k0 : List Byte} (hk0 : k0.length = 64)
    (hi : (OK v).SH.Repr t.mem (scA L sSt) (Spec.Hmac.xorPad k0 Spec.Hmac.ipad))
    (ho : (OK v).SH.Repr t.mem (scA L sOuter) (Spec.Hmac.xorPad k0 Spec.Hmac.opad)) :
    WP isa (.call (HH v).updN (HH v).updC) t fun u => Post L g vv m₀ R EM u ∧
      (OK v).SH.Repr u.mem (scA L sSt) (Spec.Hmac.xorPad k0 Spec.Hmac.ipad ++ Spec.Rsa.bytesAt t.mem d n) ∧
      (OK v).SH.Repr u.mem (scA L sOuter) (Spec.Hmac.xorPad k0 Spec.Hmac.opad) ∧ Keep L 0 0 t.mem u.mem := by
  refine Proof.Pbkdf2.Md.AArch64.Calls.upd_call (OK v).stream (len := n)
    { x0 := hx0, x2 := hx2, x3 := hx3, x4 := hx4
      cd := hcd
      cw := Covers.pair (scCov hL hc.ctx (a := sSt) (n := 96) (by decide))
        (scCov hL hc.ctx (a := sWork) (n := 160) (by decide))
      st_sc := scD hL (a := sSt) (n := 96) (b := sWork) (m := 160) (.inl (by decide)) (by decide) (by decide)
      d_st := hds sSt 96 (by decide)
      d_sc := hds sWork 160 (by decide)
      sp16 := hc.sp16 hL hP
      stk_st := hc.stk hL hP (a := sSt) (m := 96) (by decide)
      stk_d := by rw [hc.ctx.sp]; exact hdk
      stk_sc := hc.stk hL hP (a := sWork) (m := 160) (by decide) } fun u a hu => ⟨hc.after hL hP a fun r hr => ?_,
      hu _ hi (by rw [hx1, Spec.Hmac.xorPad, List.length_map, hk0]), hc.repr hL hP a (by decide) (fun r hr => ?_) ho,
      hc.keepLow hL hP a (fun r hr => ?_) 0 0⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact scSub (a := sSt) (n := 96) (by decide)
    · exact scSub (a := sWork) (n := 160) (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact scD hL (a := sOuter) (n := 96) (b := sSt) (m := 96) (.inr (by decide)) (by decide) (by decide)
    · exact scD hL (a := sOuter) (n := 96) (b := sWork) (m := 160) (.inl (by decide)) (by decide) (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨sSt, 96, by decide, rfl⟩
    · exact ⟨sWork, 160, by decide, rfl⟩

/-! ## HMAC's `finalize` -/

theorem mac_fin (hL : L.Ok) (hP : 16 ≤ L.P) {t : State} (hc : Post L g vv m₀ R EM t) {o : Nat}
    (ho1 : 1024 ≤ o) (ho2 : o + 32 ≤ scrBytes) {k0 text : List Byte} (hk0 : k0.length = 64)
    (htl : text.length < 2 ^ 32)
    (hx0 : t.gpr .x0 = scA L sSt) (hx1 : t.gpr .x1 = scA L sOuter)
    (hx2 : t.gpr .x2 = BitVec.ofNat 64 (64 + text.length)) (hx3 : t.gpr .x3 = scA L o)
    (hx4 : t.gpr .x4 = scA L sWork)
    (hi : (OK v).SH.Repr t.mem (scA L sSt) (Spec.Hmac.xorPad k0 Spec.Hmac.ipad ++ text))
    (ho : (OK v).SH.Repr t.mem (scA L sOuter) (Spec.Hmac.xorPad k0 Spec.Hmac.opad)) :
    WP isa (.call (HH v).hmacFinN (HH v).hmacFin) t fun u => Post L g vv m₀ R EM u ∧
      Spec.Rsa.bytesAt u.mem (scA L o) 32 = Spec.Hmac.hmacBlockKey Spec.Hmac.sha256 k0 text ∧
      Keep L o 32 t.mem u.mem := by
  have hs := hL.s8192
  refine Proof.Pbkdf2.Md.AArch64.Pbk.hfin_call (OK v) (hF v) (hFd v) (cnt := t.gpr .x2)
    { x0 := hx0, x1 := hx1, x2 := rfl, x3 := hx3, x4 := hx4
      cr := Covers.right (scCov hL hc.ctx (a := sOuter) (n := 96) (by decide))
      cw := (scCov hL hc.ctx (a := sSt) (n := 96) (by decide)).cons
        ((scCov hL hc.ctx (a := o) (n := 32) ho2).cons
          ((scCov hL hc.ctx (a := sWork) (n := 832) (by decide)).cons Covers.nil))
      i_u := scD hL (a := sSt) (n := 96) (b := sOuter) (m := 96) (.inl (by decide)) (by decide) (by decide)
      i_o := scD hL (a := sSt) (n := 96) (b := o) (m := 32) (.inl (by unfold sSt; omega_arith)) (by decide) ho2
      i_s := scD hL (a := sSt) (n := 96) (b := sWork) (m := 832) (.inl (by decide)) (by decide) (by decide)
      u_o := scD hL (a := sOuter) (n := 96) (b := o) (m := 32) (.inl (by unfold sOuter; omega_arith)) (by decide) ho2
      u_s := scD hL (a := sOuter) (n := 96) (b := sWork) (m := 832) (.inl (by decide)) (by decide) (by decide)
      o_s := scD hL (a := o) (n := 32) (b := sWork) (m := 832) (.inr (by unfold sWork; omega_arith)) ho2 (by decide)
      sp16 := hc.sp16 hL hP
      stk_i := hc.stk hL hP (a := sSt) (m := 96) (by decide)
      stk_u := hc.stk hL hP (a := sOuter) (m := 96) (by decide)
      stk_o := hc.stk hL hP (a := o) (m := 32) ho2
      stk_s := hc.stk hL hP (a := sWork) (m := 832) (by decide)
      scnw := by
        show (scA L sWork).toNat + 832 ≤ 2 ^ 64
        rw [scA_toNat hL (by decide)]; have := hL.bS; unfold sWork; omega_arith }
    fun u a hf => ⟨hc.after hL hP a fun r hr => ?_, ?_, ⟨fun b l h₁ h₂ h₃ => hc.keep hL hP a h₂ fun r hr => ?_,
      fun _ _ hd => hc.slotKeep hL hP a (fun r hr => ?_) hd⟩⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact scSub (a := sSt) (n := 96) (by decide)
    · exact scSub (a := o) (n := 32) ho2
    · exact scSub (a := sWork) (n := 832) (by decide)
  · exact hf k0 text hk0 (by rw [hk0]; omega_arith) hi (by rw [hx2]; rfl) ho
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact scD hL (b := sSt) (m := 96) (.inr (by unfold sSt; omega_arith)) h₂ (by decide)
    · exact scD hL (b := o) (m := 32) h₃ h₂ ho2
    · exact scD hL (b := sWork) (m := 832) (.inr (by unfold sWork; omega_arith)) h₂ (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact scSub (a := sSt) (n := 96) (by decide)
    · exact scSub (a := o) (n := 32) ho2
    · exact scSub (a := sWork) (n := 832) (by decide)

end VG.Proof.RsaPkcs1Enc.AArch64.Dec
