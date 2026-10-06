import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecD
import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hashes.Sha256
import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.PbkCalls
import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Core

/-!
# RSAES-PKCS1-v1_5 decryption on AArch64: `DH = SHA256(D)`

SHA-256's functions, with an implementation `v` of its compression function
(`HH v`), and what is proven of them; the blocks setting the calls'
arguments, and the hash of `D` (`hashD_ok`).
-/

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

theorem sh_hash : (OK v).SH.H = Spec.Hmac.sha256 := rfl

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
abbrev Slots (t : State) (Q : Addr) : Prop := ∀ d, d + 8 ≤ 208 → InRegions (t.rd ++ t.wr) (Q + BitVec.ofNat 64 d) 8

theorem shaInitArgs_ok {t : State} {Q : Addr} (hsp : t.sp = Q) (h : Slots t Q) :
    WP isa (.block shaInitArgs) t fun u => Same t u ∧
      u.gpr .x0 = t.mem.readW (Q + BitVec.ofNat 64 oScr) 64 + BitVec.ofNat 64 sSt := by
  have h168 := h 168 (by decide)
  apply WP.of_runBlock
  simp only [shaInitArgs, scr, runBlock_cons, runStep_some, runBlock_nil, exec, State.read, State.load, Size.bits,
    BitVec.setWidth_eq, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self, ite_true, hsp, oScr, sSt, Option.map_some,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_write, h168]
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, preserved_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩, rfl⟩

/-- A word of the frame. -/
abbrev slot (t : State) (Q : Addr) (d : Nat) : BitVec 64 := t.mem.readW (Q + BitVec.ofNat 64 d) 64

theorem shaUpdArgs_ok {t : State} {Q : Addr} (hsp : t.sp = Q) (h : Slots t Q) :
    WP isa (.block shaUpdArgs) t fun u => Same t u ∧ u.gpr .x0 = slot t Q oScr + BitVec.ofNat 64 sSt ∧
      u.gpr .x1 = 0 ∧ u.gpr .x2 = slot t Q oScr + BitVec.ofNat 64 sD ∧ u.gpr .x3 = slot t Q oK ∧
      u.gpr .x4 = slot t Q oScr + BitVec.ofNat 64 sWork := by
  have h168 := h 168 (by decide)
  have h120 := h 120 (by decide)
  apply WP.of_runBlock
  simp only [shaUpdArgs, scr, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.read, State.load, Size.bits, BitVec.setWidth_eq, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self,
    ite_true, hsp, oScr, oK, sSt, sD, sWork, Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_write,
    RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, h168, h120]
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, preserved_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩, rfl, rfl, rfl,
    rfl, rfl⟩

theorem shaFinArgs_ok {t : State} {Q : Addr} (hsp : t.sp = Q) (h : Slots t Q) :
    WP isa (.block shaFinArgs) t fun u => Same t u ∧ u.gpr .x0 = slot t Q oScr + BitVec.ofNat 64 sSt ∧
      u.gpr .x1 = slot t Q oK ∧ u.gpr .x2 = slot t Q oScr + BitVec.ofNat 64 sDH ∧
      u.gpr .x3 = slot t Q oScr + BitVec.ofNat 64 sWork := by
  have h168 := h 168 (by decide)
  have h120 := h 120 (by decide)
  apply WP.of_runBlock
  simp only [shaFinArgs, scr, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.read, State.load, Size.bits, BitVec.setWidth_eq, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self,
    ite_true, hsp, oScr, oK, sSt, sDH, sWork, Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_write,
    RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, h168, h120]
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, preserved_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩, rfl, rfl, rfl, rfl⟩

/-! ## The hash of `D` -/

theorem bytes_keep {ws : List Region} {m m' : Mem} (hf : Frame ws m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ ws, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' p n = Spec.Rsa.bytesAt m p n :=
  Enc.bytesAt_eq fun _ hi => hf.bytes (R := ⟨p, n⟩) hd hn hi

section
variable {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {R : BitVec 64} {EM : List Byte}

theorem Post.slots {t : State} (hc : Post L g vv m₀ R EM t) : Slots t L.Q := fun _ hd =>
  hc.ctx.inFrR (by unfold frameBytes; omega)

theorem Post.sp16 (hL : L.Ok) (hP : 16 ≤ L.P) {t : State} (hc : Post L g vv m₀ R EM t) : 16 ≤ t.sp.toNat := by
  rw [hc.ctx.sp]; have := hL.pQ; omega

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
    · rw [List.mem_singleton.mp hr]; exact (hc.stk hL hP ha).symm) (by unfold scrBytes at ha; omega)

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
    rw [hc₁.keep hL hP a₂ (by unfold sD scrBytes; omega) fun r hr => by
      rw [List.mem_singleton.mp hr]; exact scD hL (.inr (Nat.le_of_ble_eq_true rfl)) (by unfold sD scrBytes; omega) (Nat.le_of_ble_eq_true rfl),
      S₁.mem]
  -- `update`
  refine WP.seq (WP.mono (shaUpdArgs_ok hc₂.ctx.sp hc₂.slots) fun t₃ ⟨S₃, x0₃, x1₃, x2₃, x3₃, x4₃⟩ => ?_)
  have hc₃ := hc₂.same S₃
  simp only [slot, hc₂.ctx.kept.scr, hc₂.ctx.kept.k] at x0₃ x2₃ x3₃ x4₃
  refine WP.seq (Proof.Pbkdf2.Md.AArch64.Calls.upd_call (OK v).stream (len := L.k.toNat)
    { x0 := x0₃, x2 := x2₃, x3 := by rw [x3₃], x4 := x4₃
      cd := Covers.right (scCov hL hc₃.ctx (by unfold sD scrBytes; omega))
      cw := Covers.pair (scCov hL hc₃.ctx (a := sSt) (n := 96) (Nat.le_of_ble_eq_true rfl))
        (scCov hL hc₃.ctx (a := sWork) (n := 160) (Nat.le_of_ble_eq_true rfl))
      st_sc := scD hL (.inl (Nat.le_of_ble_eq_true rfl)) (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
      d_st := scD hL (.inr (Nat.le_of_ble_eq_true rfl)) (by unfold sD scrBytes; omega) (Nat.le_of_ble_eq_true rfl)
      d_sc := scD hL (.inr (Nat.le_of_ble_eq_true rfl)) (by unfold sD scrBytes; omega) (Nat.le_of_ble_eq_true rfl)
      sp16 := hc₃.sp16 hL hP
      stk_st := hc₃.stk hL hP (Nat.le_of_ble_eq_true rfl)
      stk_d := hc₃.stk hL hP (by unfold sD scrBytes; omega)
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
  have := hf₆ _ (by rw [S₅.mem]; exact hr₄) (by simp [Spec.Sha256.bytesAt]; omega)
    (by rw [x1₅]; simp [Spec.Sha256.bytesAt])
  obtain ⟨-, -, -, -, -, hF, hD, -⟩ := sizes v
  rw [hF, hD, List.take_of_length_le (by simp [Spec.Sha256.bytesAt])] at this
  rw [show Spec.Rsa.bytesAt t₆.mem (scA L sDH) 32 = Spec.Sha256.bytesAt t₆.mem (scA L sDH) 32 from rfl, this]
  show Spec.Sha256.hash ([] ++ Spec.Sha256.bytesAt t₃.mem (scA L sD) L.k.toNat) = _
  rw [List.nil_append, show Spec.Sha256.bytesAt t₃.mem (scA L sD) L.k.toNat =
    Spec.Rsa.bytesAt t₃.mem (scA L sD) L.k.toNat from rfl, S₃.mem, hD₂, h.D]

end VG.Proof.RsaPkcs1Enc.AArch64.Dec
