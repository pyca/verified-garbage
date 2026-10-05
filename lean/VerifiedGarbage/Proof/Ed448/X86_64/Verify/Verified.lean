import VerifiedGarbage.Impl.Ed448.X86_64.Verify
import VerifiedGarbage.Proof.MlKem.X86_64.SampleCT
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Ed448.X86_64.PublicKey.Verified
import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.Ed448.X86_64.ScalarVerified
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyVerified
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.TCB.X86_64.Target

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86_64.Verify.Layout`. -/
section

/-!
# Ed448 verification on x86-64: where everything is

The function's buffers and the 272 bytes of stack below its return address,
from `B` up (`Lay`): the frame (256 bytes, from `SP = B + 16`, `rsp` between
its push and pop), whose first 200 bytes (`DAT`: the header of `dom4`, the
hash and `k`) calls may write, and the 16 bytes below it that the calls use.
`Ctx` is what holds between the frame's push and pop: the permissions, `rsp`,
the callee-saved registers, the arguments in the frame, and that memory
changed only in `scratch` and the stack. `call_ok` runs a call of verified
code that writes only within `scratch` and `DAT` in such a state.
-/

namespace VG.Proof.Ed448.X86_64.Verify

open VG VG.X86_64 VG.Impl.Ed448.X86_64.Verify
open VG.Spec.Sha3 (bytesAt)

/-! ## Regions within others -/

/-- `r` lies at an offset within `R`. -/
def Within (r R : Region) : Prop := ∃ off, r.base = R.base + BitVec.ofNat 64 off ∧ off + r.len ≤ R.len

theorem Within.sub {r R : Region} (h : VG.Proof.Ed448.X86_64.Verify.Within r R) : Region.Sub r R := by
  obtain ⟨off, hb, hl⟩ := h
  obtain ⟨b, n⟩ := r
  simp only at hb hl
  subst hb
  exact Offset.sub_base _ hl

theorem add_add (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem Within.trans {r R R' : Region} (h : VG.Proof.Ed448.X86_64.Verify.Within r R) (h' : VG.Proof.Ed448.X86_64.Verify.Within R R') : VG.Proof.Ed448.X86_64.Verify.Within r R' := by
  obtain ⟨o, hb, hl⟩ := h
  obtain ⟨o', hb', hl'⟩ := h'
  exact ⟨o' + o, by rw [hb, hb', VG.Proof.Ed448.X86_64.Verify.add_add], by omega⟩

theorem within_off (p : Addr) {d n k : Nat} (h : d + n ≤ k) :
    VG.Proof.Ed448.X86_64.Verify.Within ⟨p + BitVec.ofNat 64 d, n⟩ ⟨p, k⟩ := ⟨d, rfl, h⟩

theorem within_base (p : Addr) {n k : Nat} (h : n ≤ k) : VG.Proof.Ed448.X86_64.Verify.Within ⟨p, n⟩ ⟨p, k⟩ :=
  ⟨0, (BitVec.add_zero p).symm, by simpa using h⟩

theorem within_self (r : Region) : VG.Proof.Ed448.X86_64.Verify.Within r r := ⟨0, (BitVec.add_zero _).symm, by simp⟩

theorem covers_of_within {rs rs' : List Region} (h : ∀ r ∈ rs, ∃ R ∈ rs', VG.Proof.Ed448.X86_64.Verify.Within r R) : Covers rs rs' :=
  Covers.of_sub fun r hr => by
    obtain ⟨R, hR, o, hb, hl⟩ := h r hr
    exact ⟨R, hR, o, hb, hl⟩

/-! ## Addresses -/

theorem ofInt_nat (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toInt_eq; simp

theorem ea_stk (t : State) (d : Nat) : t.ea (VG.Impl.Ed448.X86_64.Verify.stk d) = t.gpr .rsp + BitVec.ofNat 64 d := by
  show t.gpr .rsp + BitVec.ofInt 64 (d : Int) = _
  rw [VG.Proof.Ed448.X86_64.Verify.ofInt_nat]

theorem ea_base (t : State) (r : Reg) (d : Nat) :
    t.ea { base := r, disp := (d : Int) } = t.gpr r + BitVec.ofNat 64 d := by
  show t.gpr r + BitVec.ofInt 64 (d : Int) = _
  rw [VG.Proof.Ed448.X86_64.Verify.ofInt_nat]

theorem sx32 {n : Nat} (h : n < 2 ^ 31) : (BitVec.ofNat 32 n).signExtend 64 = BitVec.ofNat 64 n :=
  Proof.MlKem.X86_64.sx_ofNat h

theorem zx32 {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem gpr_ce (t : State) (rd wr : List Region) {r : Reg} (h : r ≠ .rsp) :
    (t.callEntry.withRegions rd wr).gpr r = t.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ h]

theorem rsp_ce (t : State) (rd wr : List Region) :
    (t.callEntry.withRegions rd wr).gpr .rsp = t.gpr .rsp - 8 := by
  rw [State.withRegions_gpr, State.callEntry_rsp]

theorem ne_cs {r d : Reg} (hr : r ∈ calleeSaved) (hd : d ∉ calleeSaved) : r ≠ d :=
  fun e => hd (e ▸ hr)

theorem bytesAt_congr {m m' : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < n, m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) : VG.Spec.Sha3.bytesAt m' p n = VG.Spec.Sha3.bytesAt m p n := by
  simp only [VG.Spec.Sha3.bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (VG.Spec.Sha3.bytesAt m p n).length = n := by
  simp [VG.Spec.Sha3.bytesAt]

/-! ## The layout -/

/-- The buffers, the lowest byte of the stack used (`rsp - 272` on entry),
and the permissions on entry. -/
structure Lay where
  B : Addr
  pk : Addr
  ctx : Addr
  ctxLen : BitVec 64
  msg : Addr
  len : BitVec 64
  sig : Addr
  scr : Addr
  rd : List Region
  wr : List Region

namespace Lay

variable (L : VG.Proof.Ed448.X86_64.Verify.Lay)

/-- `rsp` between the frame's push and pop. -/
abbrev SP : Addr := L.B + BitVec.ofNat 64 16
/-- The frame. -/
abbrev FR : Region := ⟨L.SP, 256⟩
/-- What calls may write in the frame: the header, the hash and `k`. -/
abbrev DAT : Region := ⟨L.SP, 200⟩
/-- The stack used: the frame and the 16 bytes below it. -/
abbrev STK : Region := ⟨L.B, 272⟩
/-- The return address. -/
abbrev RET : Region := ⟨L.B + BitVec.ofNat 64 272, 8⟩
/-- The Keccak state, the sponge functions' working space. -/
abbrev ST : Addr := L.scr
abbrev KS : Addr := L.scr + BitVec.ofNat 64 256
abbrev SCR : Region := ⟨L.scr, 8192⟩
abbrev PK : Region := ⟨L.pk, 57⟩
abbrev SIG : Region := ⟨L.sig, 114⟩
abbrev MSG : Region := ⟨L.msg, L.len.toNat⟩
abbrev CTX : Region := ⟨L.ctx, L.ctxLen.toNat⟩
/-- The hash and `k`, in the frame. -/
abbrev H : Addr := L.SP + BitVec.ofNat 64 16
abbrev K : Addr := L.SP + BitVec.ofNat 64 136

/-- What the contract says of where everything is. -/
structure Ok : Prop where
  ctxLt : L.ctxLen.toNat < 256
  nB : L.B.toNat + 280 < 2 ^ 64
  wr : L.wr = [L.SCR]
  inPk : L.PK ∈ L.rd
  inSig : L.SIG ∈ L.rd
  inMsg : L.MSG ∈ L.rd
  inCtx : L.CTX ∈ L.rd
  xPk : L.SCR.Disjoint L.PK
  xSig : L.SCR.Disjoint L.SIG
  xMsg : L.SCR.Disjoint L.MSG
  xCtx : L.SCR.Disjoint L.CTX
  kScr : L.STK.Disjoint L.SCR
  kPk : L.STK.Disjoint L.PK
  kSig : L.STK.Disjoint L.SIG
  kMsg : L.STK.Disjoint L.MSG
  kCtx : L.STK.Disjoint L.CTX
  rScr : L.RET.Disjoint L.SCR
  nPk : L.pk.toNat + 57 ≤ 2 ^ 64
  nSig : L.sig.toNat + 114 ≤ 2 ^ 64
  nMsg : L.msg.toNat + L.len.toNat ≤ 2 ^ 64
  nCtx : L.ctx.toNat + L.ctxLen.toNat ≤ 2 ^ 64
  nScr : L.scr.toNat + 8192 ≤ 2 ^ 64

end Lay

namespace Lay.Ok

variable {L : VG.Proof.Ed448.X86_64.Verify.Lay}

theorem stk_x (h : L.Ok) {d n e k : Nat} (h₁ : d + n ≤ 272) (h₂ : e + k ≤ 8192) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
  (h.kScr.sub_left (Offset.sub_base _ h₁)).sub_right (Offset.sub_base _ h₂)

theorem stk_r (_h : L.Ok) {r : Region} (hr : L.STK.Disjoint r) {d n : Nat} (h₁ : d + n ≤ 272) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r :=
  hr.sub_left (Offset.sub_base _ h₁)

theorem x_r (_h : L.Ok) {r : Region} (hr : L.SCR.Disjoint r) {e k : Nat} (h₂ : e + k ≤ 8192) :
    Region.Disjoint ⟨L.scr + BitVec.ofNat 64 e, k⟩ r :=
  hr.sub_left (Offset.sub_base _ h₂)

end Lay.Ok

/-- `B + 16 - 8 = B + 8`. -/
theorem sp_sub8 (B : Addr) : B + BitVec.ofNat 64 16 - 8 = B + BitVec.ofNat 64 8 := by
  bv_omega

theorem sp_sub8' (B : Addr) : B + BitVec.ofNat 64 16 - BitVec.ofNat 64 8 = B + BitVec.ofNat 64 8 :=
  VG.Proof.Ed448.X86_64.Verify.sp_sub8 B

theorem sub88 (B : Addr) : B + BitVec.ofNat 64 8 - 8 = B := by bv_omega

/-- The stack a call from `rsp = B + 16` uses. -/
theorem below_call_sub (B : Addr) {m : Nat} (hm : m ≤ 16) :
    Region.Sub (below (B + BitVec.ofNat 64 16) m) ⟨B, 16⟩ := by
  have : B + BitVec.ofNat 64 16 - BitVec.ofNat 64 m = B + BitVec.ofNat 64 (16 - m) := by
    rw [Offset.sub_ofNat_eq (B + BitVec.ofNat 64 16) (a := m) (b := 16) hm, BitVec.add_sub_cancel]
  show Region.Sub ⟨B + BitVec.ofNat 64 16 - BitVec.ofNat 64 m, m⟩ _
  rw [this]
  exact Offset.sub_base _ (by omega)

/-! ## Between the frame's push and pop -/

/-- The state between the frame's push and pop: `g` and `mx` are the
registers and MXCSR on entry, `m₀` the memory. -/
structure Ctx (L : VG.Proof.Ed448.X86_64.Verify.Lay) (g : Reg → BitVec 64) (mx : BitVec 32) (m₀ : Mem) (t : State) : Prop where
  rd : t.rd = L.rd
  wr : t.wr = L.FR :: L.wr
  rsp : t.gpr .rsp = L.SP
  cs : ∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = g r
  mx : t.mxcsr.extractLsb' 6 10 = mx.extractLsb' 6 10
  pPk : t.mem.readW (L.SP + BitVec.ofNat 64 fPk) 64 = L.pk
  pCtx : t.mem.readW (L.SP + BitVec.ofNat 64 fCtx) 64 = L.ctx
  pCtxLen : t.mem.readW (L.SP + BitVec.ofNat 64 fCtxLen) 64 = L.ctxLen
  pMsg : t.mem.readW (L.SP + BitVec.ofNat 64 fMsg) 64 = L.msg
  pLen : t.mem.readW (L.SP + BitVec.ofNat 64 fLen) 64 = L.len
  pSig : t.mem.readW (L.SP + BitVec.ofNat 64 fSig) 64 = L.sig
  pScr : t.mem.readW (L.SP + BitVec.ofNat 64 fScr) 64 = L.scr
  frame : VG.Frame [L.SCR, L.STK] m₀ t.mem

namespace Ctx

variable {L : VG.Proof.Ed448.X86_64.Verify.Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem} {t t' : State}

/-- Code that writes only caller-saved registers. -/
theorem regs (hc : VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hm : t'.mem = t.mem)
    (hmx : t'.mxcsr = t.mxcsr) (hg : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) : VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, (hg .rsp (by decide)).trans hc.rsp,
    fun r hr hr' => (hg r hr).trans (hc.cs r hr hr'), by rw [hmx]; exact hc.mx,
    by rw [hm]; exact hc.pPk, by rw [hm]; exact hc.pCtx, by rw [hm]; exact hc.pCtxLen,
    by rw [hm]; exact hc.pMsg, by rw [hm]; exact hc.pLen, by rw [hm]; exact hc.pSig,
    by rw [hm]; exact hc.pScr, by rw [hm]; exact hc.frame⟩

/-- The same state, with the entry registers, MXCSR and memory given by others equal to them. -/
theorem congr (hc : VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t) {g' : Reg → BitVec 64} {mx' : BitVec 32} {m₀' : Mem}
    (hg : ∀ r ∈ calleeSaved, r ≠ .rsp → g r = g' r) (hmx : mx = mx') (hm : m₀ = m₀') : VG.Proof.Ed448.X86_64.Verify.Ctx L g' mx' m₀' t := by
  subst hmx hm
  exact ⟨hc.rd, hc.wr, hc.rsp, fun r hr hr' => (hc.cs r hr hr').trans (hg r hr hr'), hc.mx, hc.pPk, hc.pCtx,
    hc.pCtxLen, hc.pMsg, hc.pLen, hc.pSig, hc.pScr, hc.frame⟩

/-- A word of the frame is readable. -/
theorem inFr (hc : VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t) {d : Nat} (h₂ : d + 8 ≤ 256) :
    InRegions (t.rd ++ t.wr) (L.SP + BitVec.ofNat 64 d) 8 :=
  ⟨L.FR, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ h₂ (by omega)⟩

theorem inFrW (hc : VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t) {d n : Nat} (h₂ : d + n ≤ 256) :
    InRegions t.wr (L.SP + BitVec.ofNat 64 d) n :=
  ⟨L.FR, by rw [hc.wr]; simp, Offset.contains_base _ h₂ (by omega)⟩

/-- The return address of a call from the frame. -/
theorem ret (hc : VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t) : below (t.gpr .rsp) 8 = ⟨L.B + BitVec.ofNat 64 8, 8⟩ := by
  rw [hc.rsp]
  show (⟨L.B + BitVec.ofNat 64 16 - BitVec.ofNat 64 8, 8⟩ : Region) = _
  rw [VG.Proof.Ed448.X86_64.Verify.sp_sub8']

/-- A byte of a region apart from `scratch` and the stack, as on entry. -/
theorem byte (hc : VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t) {R : Region} (hx : L.SCR.Disjoint R) (hk : L.STK.Disjoint R)
    (hR : R.len ≤ 2 ^ 64) {i : Nat} (hi : i < R.len) :
    t.mem (R.base + BitVec.ofNat 64 i) = m₀ (R.base + BitVec.ofNat 64 i) :=
  Frame.bytes (R := R) hc.frame (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hx.symm
    · exact hk.symm) hR hi

theorem bytesAt_eq (hc : VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t) {p : Addr} {n : Nat} (hx : L.SCR.Disjoint ⟨p, n⟩)
    (hk : L.STK.Disjoint ⟨p, n⟩) (hn : n ≤ 2 ^ 64) : VG.Spec.Sha3.bytesAt t.mem p n = VG.Spec.Sha3.bytesAt m₀ p n :=
  VG.Proof.Ed448.X86_64.Verify.bytesAt_congr fun _ hi => hc.byte (R := ⟨p, n⟩) hx hk hn hi

/-- A byte on entry to a call from the frame, if the return address misses it. -/
theorem ce_byte (t : State) {R : Region} (hd : (below (t.gpr .rsp) 8).Disjoint R)
    (hR : R.len ≤ 2 ^ 64) {i : Nat} (hi : i < R.len) :
    t.callEntry.mem (R.base + BitVec.ofNat 64 i) = t.mem (R.base + BitVec.ofNat 64 i) :=
  Frame.bytes (rs := [below (t.gpr .rsp) 8])
    (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (below_call _ (by omega) (by omega)))
    (by simpa using hd.symm) hR hi

theorem ce_bytesAt (hc : VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t) {p : Addr} {n : Nat}
    (hd : Region.Disjoint ⟨L.B + BitVec.ofNat 64 8, 8⟩ ⟨p, n⟩) (hn : n ≤ 2 ^ 64) :
    VG.Spec.Sha3.bytesAt t.callEntry.mem p n = VG.Spec.Sha3.bytesAt t.mem p n :=
  VG.Proof.Ed448.X86_64.Verify.bytesAt_congr fun _ hi => VG.Proof.Ed448.X86_64.Verify.Ctx.ce_byte t (R := ⟨p, n⟩) (by rw [hc.ret]; exact hd) hn hi

end Ctx

/-- The slots of the frame's arguments are apart from `DAT`, `scratch` and the stack below the frame. -/
theorem slot_disj {L : VG.Proof.Ed448.X86_64.Verify.Lay} (hL : L.Ok) {d : Nat} (h₁ : 200 ≤ d) (h₂ : d + 8 ≤ 256) {r : Region}
    (hr : VG.Proof.Ed448.X86_64.Verify.Within r L.SCR ∨ VG.Proof.Ed448.X86_64.Verify.Within r L.DAT ∨ r = ⟨L.B, 16⟩) :
    Region.Disjoint ⟨L.SP + BitVec.ofNat 64 d, 8⟩ r := by
  rw [Lay.SP, VG.Proof.Ed448.X86_64.Verify.add_add]
  rcases hr with hr | hr | rfl
  · exact (hL.stk_r hL.kScr (d := 16 + d) (n := 8) (by omega)).sub_right hr.sub
  · have := Offset.disjoint L.B (d := 16 + d) (n := 8) (e := 16) (k := 200) (by omega) (by omega) (by omega)
    exact this.sub_right (by simpa [Lay.DAT, Lay.SP] using hr.sub)
  · exact Offset.disjoint_base _ (by omega) (by omega)

/-- A state whose memory differs from that of a `Ctx` state only within
`scratch`, `DAT` and the 16 bytes below the frame. -/
theorem Ctx.of_frame {L : VG.Proof.Ed448.X86_64.Verify.Lay} (hL : L.Ok) {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem} {t t' : State}
    (hc : VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hcs : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r)
    (hmx : t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10) {rs : List Region}
    (hf : VG.Frame (rs ++ [⟨L.B, 16⟩]) t.mem t'.mem) (hrs : ∀ r ∈ rs, VG.Proof.Ed448.X86_64.Verify.Within r L.SCR ∨ VG.Proof.Ed448.X86_64.Verify.Within r L.DAT) :
    VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t' := by
  have keep : ∀ d, 200 ≤ d → d + 8 ≤ 256 →
      t'.mem.readW (L.SP + BitVec.ofNat 64 d) 64 = t.mem.readW (L.SP + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => hf.readW (Region.contains_self _ _) (fun r hr => VG.Proof.Ed448.X86_64.Verify.slot_disj hL h₁ h₂ (by
      rcases List.mem_append.mp hr with hr | hr
      · rcases hrs r hr with h | h
        exacts [.inl h, .inr (.inl h)]
      · simp only [List.mem_singleton] at hr; exact .inr (.inr hr))) (by decide)
  refine ⟨hrd.trans hc.rd, hwr.trans hc.wr, (hcs .rsp (by decide)).trans hc.rsp,
    fun r hr hr' => (hcs r hr).trans (hc.cs r hr hr'), hmx.trans hc.mx,
    (keep 200 (by decide) (by decide)).trans hc.pPk, (keep 208 (by decide) (by decide)).trans hc.pCtx,
    (keep 216 (by decide) (by decide)).trans hc.pCtxLen, (keep 224 (by decide) (by decide)).trans hc.pMsg,
    (keep 232 (by decide) (by decide)).trans hc.pLen, (keep 240 (by decide) (by decide)).trans hc.pSig,
    (keep 248 (by decide) (by decide)).trans hc.pScr, hc.frame.trans (Frame.sub hf fun r hr => ?_)⟩
  rcases List.mem_append.mp hr with hr | hr
  · rcases hrs r hr with h | h
    · exact ⟨L.SCR, by simp, h.sub⟩
    · have hd : Region.Sub L.DAT L.STK := by
        have := Offset.sub_base L.B (d := 16) (n := 200) (k := 272) (by omega)
        simpa [Lay.DAT, Lay.SP] using this
      exact ⟨L.STK, by simp, fun a ha => hd a (h.sub a ha)⟩
  · simp only [List.mem_singleton] at hr; subst hr
    refine ⟨L.STK, by simp, ?_⟩
    have := Offset.sub_base L.B (d := 0) (n := 16) (k := 272) (by omega)
    simpa using this

/-! ## Calls -/

/-- A call of verified code from the frame, which nests calls at most once
more, reading regions within the permissions and writing only within
`scratch` and `DAT`, keeps `Ctx`. -/
theorem call_ok {L : VG.Proof.Ed448.X86_64.Verify.Lay} (hL : L.Ok) {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}
    {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsp : NoSp c) (hd : c.depth ≤ 1) {t : State} (hc : VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t)
    {rd wr : List Region} (hpre : k.pre (t.callEntry.withRegions rd wr))
    (hsub : ∀ r ∈ rd, ∃ R ∈ L.rd ++ L.FR :: L.wr, VG.Proof.Ed448.X86_64.Verify.Within r R)
    (hwsub : ∀ r ∈ wr, VG.Proof.Ed448.X86_64.Verify.Within r L.SCR ∨ VG.Proof.Ed448.X86_64.Verify.Within r L.DAT) {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ s' → VG.Frame (wr ++ [⟨L.B, 16⟩]) t.mem s'.mem →
      (∀ r, (∀ i ∈ instrs c, Taint.clobbers i r = false) → s'.gpr r = t.gpr r) →
      (∃ s₂ : State, s₂.mem = s'.mem ∧ (∀ r, r ≠ .rsp → s₂.gpr r = s'.gpr r) ∧
        k.post (t.callEntry.withRegions rd wr) s₂) → Q s') :
    WP isa (.call n c) t Q := by
  have hwX : ∀ r ∈ wr, ∃ R ∈ L.FR :: L.wr, VG.Proof.Ed448.X86_64.Verify.Within r R := fun r hr => by
    rcases hwsub r hr with h | h
    · exact ⟨L.SCR, by simp [hL.wr], h⟩
    · exact ⟨L.FR, by simp, h.trans (VG.Proof.Ed448.X86_64.Verify.within_base _ (by decide))⟩
  have hcov : Covers (rd ++ wr) (t.rd ++ t.wr) := by
    rw [hc.rd, hc.wr]
    refine VG.Proof.Ed448.X86_64.Verify.covers_of_within fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · exact hsub r hr
    · obtain ⟨R, hR, hw⟩ := hwX r hr
      exact ⟨R, List.mem_append_right _ hR, hw⟩
  have hcovw : Covers wr t.wr := by
    rw [hc.wr]
    exact VG.Proof.Ed448.X86_64.Verify.covers_of_within hwX
  refine WP.call_mx hv hsp (by omega) hpre hcov hcovw fun s' hrd hwr hcs hf hg hpost hmx => ?_
  have hf' : VG.Frame (wr ++ [⟨L.B, 16⟩]) t.mem s'.mem := by
    refine Frame.sub hf fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
      rw [hc.rsp]
      exact VG.Proof.Ed448.X86_64.Verify.below_call_sub _ (by omega)
  exact hQ s' (hc.of_frame hL hrd hwr hcs hmx hf' hwsub) hf' hg hpost

end VG.Proof.Ed448.X86_64.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86_64.Verify.Args`. -/
section

/-!
# Ed448 verification on x86-64: the moves of a call's arguments

`setArgs as` moves each argument (a slot of the frame, a slot plus an offset,
an immediate, `rsp` plus an offset, or `rax`) into its register: afterwards
each argument register holds the argument's value in the state before the
moves (`setArgs_ok`), and nothing else changed but those registers and the
flags.
-/

namespace VG.Proof.Ed448.X86_64.Verify

open VG VG.X86_64 VG.Impl.Ed448.X86_64.Verify
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

/-- The value of an argument in the state `s`. -/
def _root_.VG.Impl.Ed448.X86_64.Verify.Arg.val (s : State) : Arg → BitVec 64
  | .slot f => s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 f) 64
  | .slotOff f o => s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 f) 64 + BitVec.ofNat 64 o
  | .imm v => BitVec.ofNat 64 v
  | .sp o => s.gpr .rsp + BitVec.ofNat 64 o
  | .ret => s.gpr .rax

/-- A slot within the frame, an offset or an immediate of 31 bits. -/
def _root_.VG.Impl.Ed448.X86_64.Verify.Arg.ok : Arg → Bool
  | .slot f => decide (f + 8 ≤ 256)
  | .slotOff f o => decide (f + 8 ≤ 256) && decide (o < 2 ^ 31)
  | .imm v => decide (v < 2 ^ 31)
  | .sp o => decide (o < 2 ^ 31)
  | .ret => true

/-- The slots of the frame are readable. -/
abbrev FrOk (s : State) : Prop := ∀ f, f + 8 ≤ 256 → InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 f) 8

theorem Arg.mov_ok (d : Reg) (a : Arg) (ha : a.ok = true) (hd : d ∈ argRegs6) (s : State) (hfr : VG.Proof.Ed448.X86_64.Verify.FrOk s) :
    WP isa (.block (a.mov d)) s fun s1 =>
      (s1.gpr d = a.val s ∧ s1.mem = s.mem ∧ s1.mxcsr = s.mxcsr) ∧ VG.Proof.MlKem.X86_64.Keep [d] s s1 := by
  refine WP.keep [d] ?_ (by
    simp only [argRegs6, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> cases a <;> rfl)
  have hsp : d ≠ .rsp := fun h => by subst h; revert hd; decide
  have hax : d ≠ .rax := fun h => by subst h; revert hd; decide
  cases a with
  | slot f =>
    simp only [Arg.ok, decide_eq_true_eq] at ha
    simp only [Arg.mov, Arg.val]
    xrun [VG.Proof.Ed448.X86_64.Verify.ea_stk, hfr f ha, RegUpd.gpr_setReg_self, RegUpd.mxcsr_setReg]
  | slotOff f o =>
    simp only [Arg.ok, Bool.and_eq_true, decide_eq_true_eq] at ha
    simp only [Arg.mov, Arg.val]
    xrun [VG.Proof.Ed448.X86_64.Verify.ea_stk, hfr f ha.1, VG.Proof.Ed448.X86_64.Verify.sx32 ha.2, RegUpd.gpr_setReg_self, RegUpd.mxcsr_setReg, RegUpd.mxcsr_setFlags]
  | imm v =>
    simp only [Arg.ok, decide_eq_true_eq] at ha
    simp only [Arg.mov, Arg.val]
    xrun [VG.Proof.Ed448.X86_64.Verify.zx32 (show v < 2 ^ 32 by omega), RegUpd.gpr_setReg_self, RegUpd.mxcsr_setReg]
  | sp o =>
    simp only [Arg.ok, decide_eq_true_eq] at ha
    simp only [Arg.mov, Arg.val]
    xrun [VG.Proof.Ed448.X86_64.Verify.sx32 ha, RegUpd.gpr_setReg_self, RegUpd.mxcsr_setReg, RegUpd.mxcsr_setFlags]
  | ret =>
    simp only [Arg.mov, Arg.val]
    xrun [RegUpd.gpr_setReg_self, RegUpd.mxcsr_setReg]

/-- The value of an argument is the same after moves into other argument registers. -/
theorem Arg.val_keep {d : Reg} (hd : d ∈ argRegs6) {s s1 : State} (hm : s1.mem = s.mem) (k : VG.Proof.MlKem.X86_64.Keep [d] s s1)
    (a : Arg) : a.val s1 = a.val s := by
  have hsp : Reg.rsp ∉ [d] := by
    simp only [List.mem_singleton]; intro h; subst h; revert hd; decide
  have hax : Reg.rax ∉ [d] := by
    simp only [List.mem_singleton]; intro h; subst h; revert hd; decide
  cases a <;> simp only [Arg.val, hm, k.gpr hsp, k.gpr hax]

theorem frOk_keep {d : Reg} (hd : d ∈ argRegs6) {s s1 : State} (k : VG.Proof.MlKem.X86_64.Keep [d] s s1) (h : VG.Proof.Ed448.X86_64.Verify.FrOk s) : VG.Proof.Ed448.X86_64.Verify.FrOk s1 := by
  have hsp : Reg.rsp ∉ [d] := by
    simp only [List.mem_singleton]; intro h; subst h; revert hd; decide
  intro f hf
  rw [k.2.1, k.2.2, k.gpr hsp]
  exact h f hf

theorem setArgsGen_ok : ∀ (ds : List Reg) (as : List Arg), ds.Nodup → (∀ d ∈ ds, d ∈ argRegs6) →
    as.all Arg.ok = true → ∀ s : State, VG.Proof.Ed448.X86_64.Verify.FrOk s →
    WP isa (.block ((ds.zip as).flatMap fun (d, a) => a.mov d)) s fun s1 =>
      ((∀ da ∈ ds.zip as, s1.gpr da.1 = da.2.val s) ∧ s1.mem = s.mem ∧ s1.mxcsr = s.mxcsr) ∧ VG.Proof.MlKem.X86_64.Keep ds s s1
  | [], _, _, _, _, s, _ => WP.block_nil ⟨⟨fun _ h => by simp at h, rfl, rfl⟩, Keep.refl _ _⟩
  | _ :: _, [], _, _, _, s, _ => WP.block_nil ⟨⟨fun _ h => by simp at h, rfl, rfl⟩, Keep.refl _ _⟩
  | d :: ds, a :: as, hn, hd, ha, s, hfr => by
    rw [List.nodup_cons] at hn
    simp only [List.all_cons, Bool.and_eq_true] at ha
    simp only [List.zip_cons_cons, List.flatMap_cons]
    rw [WP.block_append_iff]
    have hd0 := hd d (List.mem_cons_self ..)
    refine WP.mono (Arg.mov_ok d a ha.1 hd0 s hfr) fun s1 ⟨⟨h1, hm1, hx1⟩, k1⟩ => ?_
    refine WP.mono (VG.Proof.Ed448.X86_64.Verify.setArgsGen_ok ds as hn.2 (fun d' h => hd d' (List.mem_cons_of_mem _ h)) ha.2 s1
      (VG.Proof.Ed448.X86_64.Verify.frOk_keep hd0 k1 hfr))
      fun s2 ⟨⟨h2, hm2, hx2⟩, k2⟩ => ⟨⟨fun da hda => ?_, hm2.trans hm1, hx2.trans hx1⟩,
        (k1.trans k2).mono fun r hr => by simpa using hr⟩
    rcases List.mem_cons.mp hda with rfl | hda
    · rw [k2.gpr hn.1, h1]
    · rw [h2 da hda, Arg.val_keep hd0 hm1 k1]

theorem argRegs6_nodup : argRegs6.Nodup := by decide

/-- The registers the moves of arguments write. -/
abbrev argRegs : List Reg := [.rcx, .rdx, .rsi, .rdi, .r8, .r9]

theorem argRegs_cs : ∀ r ∈ calleeSaved, r ∉ VG.Proof.Ed448.X86_64.Verify.argRegs := by decide

/-- The moves of the arguments `as`. -/
theorem setArgs_ok (as : List Arg) (ha : as.all Arg.ok = true) (s : State) (hfr : VG.Proof.Ed448.X86_64.Verify.FrOk s) :
    WP isa (.block (setArgs as)) s fun s1 =>
      ((∀ da ∈ argRegs6.zip as, s1.gpr da.1 = da.2.val s) ∧ s1.mem = s.mem ∧ s1.mxcsr = s.mxcsr) ∧
        VG.Proof.MlKem.X86_64.Keep VG.Proof.Ed448.X86_64.Verify.argRegs s s1 := by
  refine WP.mono (VG.Proof.Ed448.X86_64.Verify.setArgsGen_ok argRegs6 as VG.Proof.Ed448.X86_64.Verify.argRegs6_nodup (fun _ h => h) ha s hfr) fun s1 ⟨h, k⟩ => ⟨h, ?_⟩
  refine ⟨fun r hr => k.gpr fun hm => hr ?_, k.2⟩
  simp only [argRegs6, VG.Proof.Ed448.X86_64.Verify.argRegs, List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
  rcases hm with h | h | h | h | h | h <;> simp [h]

/-- The arguments of `as`, in their registers after the moves. -/
abbrev ArgsIn (as : List Arg) (s s1 : State) : Prop := ∀ da ∈ argRegs6.zip as, s1.gpr da.1 = da.2.val s

theorem argsIn3 {a b c : Arg} {s s1 : State} (h : VG.Proof.Ed448.X86_64.Verify.ArgsIn [a, b, c] s s1) :
    s1.gpr .rdi = a.val s ∧ s1.gpr .rsi = b.val s ∧ s1.gpr .rdx = c.val s :=
  ⟨h (.rdi, a) (by simp [argRegs6]), h (.rsi, b) (by simp [argRegs6]), h (.rdx, c) (by simp [argRegs6])⟩

theorem argsIn4 {a b c d : Arg} {s s1 : State} (h : VG.Proof.Ed448.X86_64.Verify.ArgsIn [a, b, c, d] s s1) :
    s1.gpr .rdi = a.val s ∧ s1.gpr .rsi = b.val s ∧ s1.gpr .rdx = c.val s ∧ s1.gpr .rcx = d.val s :=
  ⟨h (.rdi, a) (by simp [argRegs6]), h (.rsi, b) (by simp [argRegs6]), h (.rdx, c) (by simp [argRegs6]),
    h (.rcx, d) (by simp [argRegs6])⟩

theorem argsIn5 {a b c d e : Arg} {s s1 : State} (h : VG.Proof.Ed448.X86_64.Verify.ArgsIn [a, b, c, d, e] s s1) :
    s1.gpr .rdi = a.val s ∧ s1.gpr .rsi = b.val s ∧ s1.gpr .rdx = c.val s ∧ s1.gpr .rcx = d.val s ∧
      s1.gpr .r8 = e.val s :=
  ⟨h (.rdi, a) (by simp [argRegs6]), h (.rsi, b) (by simp [argRegs6]), h (.rdx, c) (by simp [argRegs6]),
    h (.rcx, d) (by simp [argRegs6]), h (.r8, e) (by simp [argRegs6])⟩

theorem argsIn6 {a b c d e f : Arg} {s s1 : State} (h : VG.Proof.Ed448.X86_64.Verify.ArgsIn [a, b, c, d, e, f] s s1) :
    s1.gpr .rdi = a.val s ∧ s1.gpr .rsi = b.val s ∧ s1.gpr .rdx = c.val s ∧ s1.gpr .rcx = d.val s ∧
      s1.gpr .r8 = e.val s ∧ s1.gpr .r9 = f.val s :=
  ⟨h (.rdi, a) (by simp [argRegs6]), h (.rsi, b) (by simp [argRegs6]), h (.rdx, c) (by simp [argRegs6]),
    h (.rcx, d) (by simp [argRegs6]), h (.r8, e) (by simp [argRegs6]), h (.r9, f) (by simp [argRegs6])⟩

/-! ## The values of the arguments in the frame -/

section
variable {L : VG.Proof.Ed448.X86_64.Verify.Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem} {t : State}

theorem Ctx.frOk (hc : VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t) : VG.Proof.Ed448.X86_64.Verify.FrOk t := fun f hf => by
  rw [hc.rsp]; exact hc.inFr hf

theorem Ctx.slot (hc : VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t) (f : Nat) :
    (Arg.slot f).val t = t.mem.readW (L.SP + BitVec.ofNat 64 f) 64 := by
  simp only [Arg.val, hc.rsp]

theorem Ctx.sp (hc : VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t) (o : Nat) : (Arg.sp o).val t = L.SP + BitVec.ofNat 64 o := by
  simp only [Arg.val, hc.rsp]

/-- The Keccak state and the sponge functions' working space. -/
theorem Ctx.aSt (hc : VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t) : aSt.val t = L.ST := by
  simp only [Impl.Ed448.X86_64.Verify.aSt, hc.slot, hc.pScr]

theorem Ctx.aKs (hc : VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t) : aKs.val t = L.KS := by
  simp only [Impl.Ed448.X86_64.Verify.aKs, Arg.val, hc.rsp, hc.pScr]

end

end VG.Proof.Ed448.X86_64.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86_64.Verify.Rel`. -/
section

/-!
# Ed448 verification on x86-64: relating two runs

Two runs between the frame's
push and pop with the same layout, each in a `Ctx` state, whose inputs agree
on what the contract makes public (`I`), and each satisfying `Φ` (`Two`).
Blocks whose addresses are `rsp` plus offsets leak the same in both runs
(`block_rsp_tr`, and so the moves of a call's arguments, `setArgs_tr`); a
call whose callee's public data agree in both runs (`call_tr`); and what
each run satisfies by correctness carries over (`two_wp`).
-/

namespace VG.Proof.Ed448.X86_64.Verify

open VG VG.X86_64 VG.Impl.Ed448.X86_64.Verify
open VG.Proof.MlKem.X86_64 (Keep RelCT.postDep)

/-! ## Blocks addressed from `rsp` -/

/-- An instruction whose addresses are a function of `rsp`, which it keeps. -/
def SpOnly (i : Instr) : Prop :=
  (∀ s₁ s₂ : State, s₁.gpr .rsp = s₂.gpr .rsp → isa.addrs i s₁ = isa.addrs i s₂) ∧ Taint.clobbers i .rsp = false

theorem spOnly_nomem {i : Instr} (h : ∀ s, isa.addrs i s = []) (hc : Taint.clobbers i .rsp = false) : VG.Proof.Ed448.X86_64.Verify.SpOnly i :=
  ⟨fun s₁ s₂ _ => by rw [h, h], hc⟩

theorem execBlock_rsp_tr : ∀ {is : List Instr}, (∀ i ∈ is, VG.Proof.Ed448.X86_64.Verify.SpOnly i) →
    ∀ {s₁ s₂ s₁' s₂' : State} {t₁ t₂ : List Leak}, s₁.gpr .rsp = s₂.gpr .rsp →
      execBlock isa is s₁ = some (s₁', t₁) → execBlock isa is s₂ = some (s₂', t₂) →
      t₁ = t₂ ∧ s₁'.gpr .rsp = s₂'.gpr .rsp
  | [], _, _, _, _, _, _, _, hsp, e₁, e₂ => by
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e₁ e₂
    obtain ⟨rfl, rfl⟩ := e₁; obtain ⟨rfl, rfl⟩ := e₂
    exact ⟨rfl, hsp⟩
  | i :: is, h, s₁, s₂, s₁', s₂', t₁, t₂, hsp, e₁, e₂ => by
    simp only [execBlock] at e₁ e₂
    split at e₁ <;> [cases e₁; skip]
    rename_i a₁ ha₁
    split at e₂ <;> [cases e₂; skip]
    rename_i a₂ ha₂
    obtain ⟨⟨b₁, u₁⟩, eb₁, he₁⟩ := Option.map_eq_some_iff.mp e₁
    obtain ⟨⟨b₂, u₂⟩, eb₂, he₂⟩ := Option.map_eq_some_iff.mp e₂
    simp only [Prod.mk.injEq] at he₁ he₂
    obtain ⟨rfl, rfl⟩ := he₁; obtain ⟨rfl, rfl⟩ := he₂
    have hi := h i (List.mem_cons_self ..)
    have hsp' : a₁.gpr .rsp = a₂.gpr .rsp := by
      rw [exec_gpr hi.2 ha₁, exec_gpr hi.2 ha₂, hsp]
    obtain ⟨ht, hs⟩ := VG.Proof.Ed448.X86_64.Verify.execBlock_rsp_tr (fun j hj => h j (List.mem_cons_of_mem _ hj)) hsp' eb₁ eb₂
    exact ⟨by rw [show addrs i s₁ = addrs i s₂ from hi.1 _ _ hsp, ht], hs⟩

theorem block_rsp_tr {is : List Instr} (h : ∀ i ∈ is, VG.Proof.Ed448.X86_64.Verify.SpOnly i) {P : State → State → Prop}
    (hp : ∀ a b, P a b → a.gpr .rsp = b.gpr .rsp) : RelCT isa P (.block is) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hP e₁ e₂
  rw [Exec.block_iff] at e₁ e₂
  exact ⟨(VG.Proof.Ed448.X86_64.Verify.execBlock_rsp_tr h (hp _ _ hP) e₁ e₂).1, trivial⟩

theorem arg_spOnly (d : Reg) (hd : d ≠ .rsp) (a : Arg) : ∀ i ∈ a.mov d, VG.Proof.Ed448.X86_64.Verify.SpOnly i := by
  intro i hi
  cases a <;> simp only [Arg.mov, List.mem_cons, List.not_mem_nil, or_false] at hi <;>
    rcases hi with rfl | rfl <;>
    exact ⟨fun s₁ s₂ h => by simp [addrs, srcAddrs, State.ea, VG.Impl.Ed448.X86_64.Verify.stk, h],
      by cases d <;> simp_all [Taint.clobbers, Taint.dstOf]⟩

theorem setArgs_spOnly (as : List Arg) : ∀ i ∈ setArgs as, VG.Proof.Ed448.X86_64.Verify.SpOnly i := by
  intro i hi
  simp only [setArgs, List.mem_flatMap] at hi
  obtain ⟨⟨d, a⟩, hm, hi⟩ := hi
  have hd : d ∈ argRegs6 := (List.of_mem_zip hm).1
  exact VG.Proof.Ed448.X86_64.Verify.arg_spOnly d (fun e => by subst e; revert hd; decide) a i hi

/-! ## Runs related through their entry states -/

/-- Two runs whose states are related to entry states `x`, `y` by `A`, with
`P x y`. -/
def Ghost (P A : State → State → Prop) (a b : State) : Prop := ∃ x y, P x y ∧ A x a ∧ A y b

/-- What each run satisfies by correctness, from its entry state, carries over. -/
theorem ghost_step {P A B : State → State → Prop} {c : Prog isa}
    (hct : RelCT isa (VG.Proof.Ed448.X86_64.Verify.Ghost P A) c fun _ _ => True)
    (hw : ∀ x y a b, P x y → A x a → A y b → WP isa c a (B x) ∧ WP isa c b (B y)) :
    RelCT isa (VG.Proof.Ed448.X86_64.Verify.Ghost P A) c (VG.Proof.Ed448.X86_64.Verify.Ghost P B) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨x, y, hxy, a₁, a₂⟩ := hp
  obtain ⟨⟨_, u₁, x₁, y₁⟩, ⟨_, u₂, x₂, y₂⟩⟩ := hw x y s₁ s₂ hxy a₁ a₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, x, y, hxy, y₁, y₂⟩

/-! ## Two runs -/

/-- Two runs with the layout `L`, inputs related by `I`, each satisfying `Φ`. -/
def Two (I : VG.Proof.Ed448.X86_64.Verify.Lay → Mem → Mem → Prop) (Φ : VG.Proof.Ed448.X86_64.Verify.Lay → Mem → State → Prop) (a b : State) : Prop :=
  ∃ (L : VG.Proof.Ed448.X86_64.Verify.Lay) (g₁ g₂ : Reg → BitVec 64) (mx₁ mx₂ : BitVec 32) (m₁ m₂ : Mem), L.Ok ∧ I L m₁ m₂ ∧
    VG.Proof.Ed448.X86_64.Verify.Ctx L g₁ mx₁ m₁ a ∧ VG.Proof.Ed448.X86_64.Verify.Ctx L g₂ mx₂ m₂ b ∧ Φ L m₁ a ∧ Φ L m₂ b

section
variable {I : VG.Proof.Ed448.X86_64.Verify.Lay → Mem → Mem → Prop}

theorem Two.rsp {Φ : VG.Proof.Ed448.X86_64.Verify.Lay → Mem → State → Prop} {a b : State} (h : VG.Proof.Ed448.X86_64.Verify.Two I Φ a b) : a.gpr .rsp = b.gpr .rsp :=
  let ⟨_, _, _, _, _, _, _, _, _, c₁, c₂, _, _⟩ := h; c₁.rsp.trans c₂.rsp.symm

theorem two_wp {c : Prog isa} {Φ Ψ : VG.Proof.Ed448.X86_64.Verify.Lay → Mem → State → Prop}
    (hct : RelCT isa (VG.Proof.Ed448.X86_64.Verify.Two I Φ) c fun _ _ => True)
    (hw : ∀ (L : VG.Proof.Ed448.X86_64.Verify.Lay) g mx m₀ (t : State), L.Ok → VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t → Φ L m₀ t →
      WP isa c t fun t' => VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (VG.Proof.Ed448.X86_64.Verify.Two I Φ) c (VG.Proof.Ed448.X86_64.Verify.Two I Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨L, g₁, g₂, mx₁, mx₂, m₁, m₂, hL, hi, c₁, c₂, f₁, f₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw L g₁ mx₁ m₁ s₁ hL c₁ f₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw L g₂ mx₂ m₂ s₂ hL c₂ f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, L, g₁, g₂, mx₁, mx₂, m₁, m₂, hL, hi, y₁.1, y₂.1, y₁.2, y₂.2⟩

theorem two_mono {Φ Ψ : VG.Proof.Ed448.X86_64.Verify.Lay → Mem → State → Prop} (h : ∀ L m t, Φ L m t → Ψ L m t) {a b : State}
    (hp : VG.Proof.Ed448.X86_64.Verify.Two I Φ a b) : VG.Proof.Ed448.X86_64.Verify.Two I Ψ a b :=
  let ⟨L, g₁, g₂, mx₁, mx₂, m₁, m₂, hL, hi, c₁, c₂, f₁, f₂⟩ := hp
  ⟨L, g₁, g₂, mx₁, mx₂, m₁, m₂, hL, hi, c₁, c₂, h _ _ _ f₁, h _ _ _ f₂⟩

/-- What the moves of the arguments `as` leave. -/
abbrev Moved (as : List Arg) (t t1 : State) : Prop :=
  (VG.Proof.Ed448.X86_64.Verify.ArgsIn as t t1 ∧ t1.mem = t.mem ∧ t1.mxcsr = t.mxcsr) ∧ VG.Proof.MlKem.X86_64.Keep VG.Proof.Ed448.X86_64.Verify.argRegs t t1

/-- A call after the moves of its arguments, of verified code whose public
data agree in both runs. -/
theorem call_tr {Φ : VG.Proof.Ed448.X86_64.Verify.Lay → Mem → State → Prop} {as : List Arg} (hok : as.all Arg.ok = true) {n : String}
    {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (rd wr : VG.Proof.Ed448.X86_64.Verify.Lay → List Region)
    (hpre : ∀ (L : VG.Proof.Ed448.X86_64.Verify.Lay) g mx m₀ (t t1 : State), L.Ok → VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t → Φ L m₀ t → VG.Proof.Ed448.X86_64.Verify.Moved as t t1 →
      k.pre (t1.callEntry.withRegions (rd L) (wr L)))
    (hpub : ∀ (L : VG.Proof.Ed448.X86_64.Verify.Lay) g₁ g₂ mx₁ mx₂ m₁ m₂ (a b a1 b1 : State), L.Ok → I L m₁ m₂ → VG.Proof.Ed448.X86_64.Verify.Ctx L g₁ mx₁ m₁ a →
      VG.Proof.Ed448.X86_64.Verify.Ctx L g₂ mx₂ m₂ b → Φ L m₁ a → Φ L m₂ b → VG.Proof.Ed448.X86_64.Verify.Moved as a a1 → VG.Proof.Ed448.X86_64.Verify.Moved as b b1 →
      k.pub (a1.callEntry.withRegions (rd L) (wr L)) (b1.callEntry.withRegions (rd L) (wr L)))
    (hcov : ∀ (L : VG.Proof.Ed448.X86_64.Verify.Lay) g mx m₀ (t : State), L.Ok → VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t → Φ L m₀ t →
      (∀ r ∈ rd L, ∃ R ∈ L.rd ++ L.FR :: L.wr, VG.Proof.Ed448.X86_64.Verify.Within r R) ∧ (∀ r ∈ wr L, ∃ R ∈ L.FR :: L.wr, VG.Proof.Ed448.X86_64.Verify.Within r R)) :
    RelCT isa (VG.Proof.Ed448.X86_64.Verify.Two I Φ) (callA n c as) fun _ _ => True := by
  refine RelCT.seq (RelCT.postDep (Q := fun a1 b1 => ∃ a b, VG.Proof.Ed448.X86_64.Verify.Two I Φ a b ∧ VG.Proof.Ed448.X86_64.Verify.Moved as a a1 ∧ VG.Proof.Ed448.X86_64.Verify.Moved as b b1)
    (VG.Proof.Ed448.X86_64.Verify.block_rsp_tr (VG.Proof.Ed448.X86_64.Verify.setArgs_spOnly as) fun _ _ h => h.rsp)
    (fun x y ⟨_, _, _, _, _, _, _, _, _, c₁, c₂, _, _⟩ =>
      ⟨VG.Proof.Ed448.X86_64.Verify.setArgs_ok as hok x c₁.frOk, VG.Proof.Ed448.X86_64.Verify.setArgs_ok as hok y c₂.frOk⟩)
    fun x y x1 y1 hp f₁ f₂ => ⟨x, y, hp, f₁, f₂⟩) ?_
  refine RelCT.callEx hv hct fun a1 b1 ⟨a, b, hp, f₁, f₂⟩ => ?_
  obtain ⟨L, g₁, g₂, mx₁, mx₂, m₁, m₂, hL, hi, c₁, c₂, φ₁, φ₂⟩ := hp
  obtain ⟨hr, hw⟩ := hcov L g₁ mx₁ m₁ a hL c₁ φ₁
  have cov : ∀ {t t1 : State} {g mx m₀}, VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t → VG.Proof.Ed448.X86_64.Verify.Moved as t t1 →
      Covers (rd L ++ wr L) (t1.rd ++ t1.wr) ∧ Covers (wr L) t1.wr := fun hc f => by
    rw [f.2.2.1, f.2.2.2, hc.rd, hc.wr]
    refine ⟨VG.Proof.Ed448.X86_64.Verify.covers_of_within fun r hr' => ?_, VG.Proof.Ed448.X86_64.Verify.covers_of_within fun r hr' => ?_⟩
    · rcases List.mem_append.mp hr' with h' | h'
      · exact hr r h'
      · obtain ⟨R, hR, hW⟩ := hw r h'
        exact ⟨R, List.mem_append_right _ hR, hW⟩
    · exact hw r hr'
  exact ⟨rd L, wr L, rd L, wr L, hpre L g₁ mx₁ m₁ a a1 hL c₁ φ₁ f₁, hpre L g₂ mx₂ m₂ b b1 hL c₂ φ₂ f₂,
    hpub L g₁ g₂ mx₁ mx₂ m₁ m₂ a b a1 b1 hL hi c₁ c₂ φ₁ φ₂ f₁ f₂, (cov c₁ f₁).1, (cov c₁ f₁).2,
    (cov c₂ f₂).1, (cov c₂ f₂).2,
    by rw [f₁.2.gpr (by decide), f₂.2.gpr (by decide), c₁.rsp, c₂.rsp]⟩

end

end VG.Proof.Ed448.X86_64.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86_64.Verify.Hash`. -/
section

/-!
# Ed448 verification on x86-64: the hash

Between the frame's push and pop (`Ctx`): the first ten bytes of
`dom4(0, context)` written to the frame (`hdr_ok`), the Keccak state at
`scratch` zeroed (`zeroSt_ok`), and the calls of `vg_keccak_absorb`,
`vg_keccak_pad` and `vg_keccak_squeeze` on it, with their working space at
`scratch + 256` (`kabs_ok`, `kpad_ok`, `ksqz_ok`); then `hash`, which leaves
`SHAKE256(dom4(0, C) ‖ R ‖ A ‖ M, 114)` in the frame (`hash_ok`).
-/

namespace VG.Proof.Ed448.X86_64.Verify

open VG VG.X86_64 VG.Impl.Ed448.X86_64.Verify
open VG.Proof.MlKem.X86_64 (Keep WP.keep AbsorbArgs PadArgs SqueezeArgs absorb_pre pad_pre squeeze_pre absorb_nosp
  pad_nosp squeeze_nosp absorb_depth pad_depth squeeze_depth callEntry_repr callEntry_bytesAt callEntry_stateAt
  ofNat_toNat')
open VG.Spec.Sha3 (bytesAt stateAt absorb pad squeezeFrom Repr)

/-! ## Regions -/

theorem x0 (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero _

theorem H_eq (L : VG.Proof.Ed448.X86_64.Verify.Lay) : L.H = L.B + BitVec.ofNat 64 32 := VG.Proof.Ed448.X86_64.Verify.add_add _ _ _

theorem K_eq (L : VG.Proof.Ed448.X86_64.Verify.Lay) : L.K = L.B + BitVec.ofNat 64 152 := VG.Proof.Ed448.X86_64.Verify.add_add _ _ _

section
variable {L : VG.Proof.Ed448.X86_64.Verify.Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

/-- The 16 bytes below `rsp` that a call from the frame uses. -/
theorem k16 {t : State} (hc : VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t) {r : Region} (h : Region.Disjoint ⟨L.B, 16⟩ r) :
    (below (t.gpr .rsp) 16).Disjoint r := by
  rw [hc.rsp]; exact h.sub_left (VG.Proof.Ed448.X86_64.Verify.below_call_sub L.B (Nat.le_refl _))

theorem st_ks (L : VG.Proof.Ed448.X86_64.Verify.Lay) : Region.Disjoint ⟨L.ST, 200⟩ ⟨L.KS, 640⟩ := by
  have := Offset.disjoint L.scr (d := 0) (n := 200) (e := 256) (k := 640) (by omega) (by omega) (by omega)
  simpa only [VG.Proof.Ed448.X86_64.Verify.x0] using this

theorem st_h (hL : L.Ok) : Region.Disjoint ⟨L.ST, 200⟩ ⟨L.H, 114⟩ := by
  have := hL.stk_x (d := 32) (n := 114) (e := 0) (k := 200) (by omega) (by omega)
  rw [VG.Proof.Ed448.X86_64.Verify.H_eq]; simpa only [VG.Proof.Ed448.X86_64.Verify.x0] using this.symm

theorem h_ks (hL : L.Ok) : Region.Disjoint ⟨L.H, 114⟩ ⟨L.KS, 640⟩ := by
  rw [VG.Proof.Ed448.X86_64.Verify.H_eq]; exact hL.stk_x (by omega) (by omega)

/-- The 16 bytes below the frame, apart from `scratch`. -/
theorem k_x (hL : L.Ok) {e k : Nat} (h₂ : e + k ≤ 8192) :
    Region.Disjoint ⟨L.B, 16⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ := by
  have := hL.stk_x (d := 0) (n := 16) (by omega) h₂
  simpa only [VG.Proof.Ed448.X86_64.Verify.x0] using this

theorem k_st (hL : L.Ok) : Region.Disjoint ⟨L.B, 16⟩ ⟨L.ST, 200⟩ := by
  have := VG.Proof.Ed448.X86_64.Verify.k_x hL (e := 0) (k := 200) (by omega); simpa only [VG.Proof.Ed448.X86_64.Verify.x0] using this

theorem k_ks (hL : L.Ok) : Region.Disjoint ⟨L.B, 16⟩ ⟨L.KS, 640⟩ := VG.Proof.Ed448.X86_64.Verify.k_x hL (by omega)

theorem k_h : Region.Disjoint ⟨L.B, 16⟩ ⟨L.H, 114⟩ := by
  rw [VG.Proof.Ed448.X86_64.Verify.H_eq]; exact Offset.base_disjoint _ (by omega) (by omega)

/-- The 16 bytes below the frame, apart from a buffer apart from the stack. -/
theorem k_r (hL : L.Ok) {r : Region} (hr : L.STK.Disjoint r) : Region.Disjoint ⟨L.B, 16⟩ r := by
  have := hL.stk_r hr (d := 0) (n := 16) (by omega); simpa only [VG.Proof.Ed448.X86_64.Verify.x0] using this

theorem w_st : VG.Proof.Ed448.X86_64.Verify.Within ⟨L.ST, 200⟩ L.SCR := VG.Proof.Ed448.X86_64.Verify.within_base _ (by omega)
theorem w_ks : VG.Proof.Ed448.X86_64.Verify.Within ⟨L.KS, 640⟩ L.SCR := VG.Proof.Ed448.X86_64.Verify.within_off _ (by omega)
theorem w_h : VG.Proof.Ed448.X86_64.Verify.Within ⟨L.H, 114⟩ L.DAT := VG.Proof.Ed448.X86_64.Verify.within_off _ (by omega)

/-- The first 57 bytes of the signature, `R`. -/
abbrev R57 (L : VG.Proof.Ed448.X86_64.Verify.Lay) : Region := ⟨L.sig, 57⟩

theorem r57_sub : Region.Sub (VG.Proof.Ed448.X86_64.Verify.R57 L) L.SIG := (VG.Proof.Ed448.X86_64.Verify.within_base _ (by omega)).sub

/-! ## The header of `dom4` -/

/-- `"SigEd448" ‖ 0 ‖ ctx_len`, the first ten bytes of `dom4(0, context)`. -/
abbrev hdrBytes (L : VG.Proof.Ed448.X86_64.Verify.Lay) : List Byte :=
  "SigEd448".toList.map (fun c => BitVec.ofNat 8 c.toNat) ++ [BitVec.ofNat 8 0, BitVec.ofNat 8 L.ctxLen.toNat]

/-- `rax` doubled `n` times. -/
theorem dbl_ok : ∀ (n : Nat) (s : State),
    WP isa (.block (List.replicate n (.alu .add .rax (.reg .rax)))) s fun s' =>
      (s'.gpr .rax = s.gpr .rax * BitVec.ofNat 64 (2 ^ n) ∧ s'.mem = s.mem ∧ s'.mxcsr = s.mxcsr) ∧
        VG.Proof.MlKem.X86_64.Keep [.rax] s s'
  | 0, s => WP.block_nil ⟨⟨by simp, rfl, rfl⟩, Keep.refl _ _⟩
  | n + 1, s => by
    rw [List.replicate_succ', WP.block_append_iff]
    refine WP.mono (VG.Proof.Ed448.X86_64.Verify.dbl_ok n s) fun s1 ⟨⟨h1, hm1, hx1⟩, k1⟩ => ?_
    refine WP.mono (WP.keep [.rax] (Q := fun s2 => s2.gpr .rax = s1.gpr .rax + s1.gpr .rax ∧
        s2.mem = s1.mem ∧ s2.mxcsr = s1.mxcsr)
      (by xrun [RegUpd.mxcsr_setReg, RegUpd.mxcsr_setFlags]) (by decide))
      fun s2 ⟨⟨h2, hm2, hx2⟩, k2⟩ =>
        ⟨⟨?_, hm2.trans hm1, hx2.trans hx1⟩, (k1.trans k2).mono fun r hr => by simpa using hr⟩
    rw [h2, h1, ← BitVec.mul_add, BitVec.ofNat_add_ofNat, Nat.pow_succ, Nat.mul_two]

/-- The bytes of the two words of the header. -/
theorem hdr_bytes (m : Mem) (p : Addr) (c : BitVec 64) (hc : c.toNat < 256) :
    VG.Spec.Sha3.bytesAt ((m.writeW p (BitVec.ofNat 64 sigEd448)).writeW (p + BitVec.ofNat 64 8)
      (c * BitVec.ofNat 64 (2 ^ 8))) p 10 =
      "SigEd448".toList.map (fun ch => BitVec.ofNat 8 ch.toNat) ++ [BitVec.ofNat 8 0, BitVec.ofNat 8 c.toNat] := by
  generalize hM : (m.writeW p (BitVec.ofNat 64 sigEd448)).writeW (p + BitVec.ofNat 64 8)
    (c * BitVec.ofNat 64 (2 ^ 8)) = M
  have h0 : M.readW p 64 = BitVec.ofNat 64 sigEd448 := by
    rw [← hM, Mem.readW_writeW_sep (Offset.sep_base p (n := 8) (e := 8) (k := 8) (by omega) (by omega))
      (by decide), Mem.readW_writeW_self64]
  have h1 : M.readW (p + BitVec.ofNat 64 8) 64 = c * BitVec.ofNat 64 (2 ^ 8) := by
    rw [← hM, Mem.readW_writeW_self64]
  have hw : (c * BitVec.ofNat 64 (2 ^ 8)).toNat = c.toNat * 256 := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat]; omega
  have e10 : VG.Spec.Sha3.bytesAt M p 10 = VG.Spec.Sha3.bytesAt M p 8 ++ (VG.Spec.Sha3.bytesAt M (p + BitVec.ofNat 64 8) 8).take 2 := by
    have a := Proof.X25519.bytesAt_add M p 8 2
    have b := Proof.X25519.bytesAt_add M (p + BitVec.ofNat 64 8) 2 6
    have l := Proof.X25519.length_bytesAt M (p + BitVec.ofNat 64 8) 2
    change Spec.X25519.bytesAt M p 10 = Spec.X25519.bytesAt M p 8 ++
      (Spec.X25519.bytesAt M (p + BitVec.ofNat 64 8) 8).take 2
    rw [a, show (8 : Nat) = 2 + 6 from rfl, b, List.take_left' l]
  have b8 : ∀ q, VG.Spec.Sha3.bytesAt M q 8 = Proof.X25519.leBytes 8 (M.readW q 64).toNat :=
    fun q => Proof.X25519.bytesAt_leBytes_64 M q
  rw [e10, b8, b8, h0, h1, hw, show Proof.X25519.leBytes 8 (BitVec.ofNat 64 sigEd448).toNat =
    "SigEd448".toList.map (fun ch => BitVec.ofNat 8 ch.toNat) by decide]
  refine congrArg (List.append _) ?_
  simp only [Proof.X25519.leBytes_succ, List.take_succ_cons, List.take_zero]
  have e1 : BitVec.ofNat 8 (c.toNat * 256) = 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, show (0 : BitVec 8).toNat = 0 from rfl]; omega
  have e2 : c.toNat * 256 / 256 = c.toNat := by omega
  rw [e1, e2]
  rfl

theorem hdr_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t) :
    WP isa (.block hdr) t fun t' => VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t' ∧ VG.Spec.Sha3.bytesAt t'.mem L.SP 10 = VG.Proof.Ed448.X86_64.Verify.hdrBytes L := by
  have w0 : InRegions t.wr L.SP 8 := by simpa only [VG.Proof.Ed448.X86_64.Verify.x0] using hc.inFrW (d := 0) (n := 8) (by omega)
  have r216 := hc.inFr (d := 216) (by omega)
  have e : (t.mem.writeW L.SP (BitVec.ofNat 64 sigEd448)).readW (L.SP + BitVec.ofNat 64 216) 64 = L.ctxLen := by
    rw [Mem.readW_writeW_sep (fun x h₁ h₂ =>
      Offset.sep_base L.SP (n := 8) (e := 216) (k := 8) (by omega) (by omega) x h₂ h₁) (by decide)]
    exact hc.pCtxLen
  rw [hdr, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.rax] (Q := fun s1 => s1.mem = t.mem.writeW L.SP (BitVec.ofNat 64 sigEd448) ∧
      s1.gpr .rax = L.ctxLen ∧ s1.mxcsr = t.mxcsr)
    (by xrun [VG.Proof.Ed448.X86_64.Verify.ea_stk, fHdr, fCtxLen, hc.rsp, w0, r216, e, RegUpd.mxcsr_setReg]) (by decide))
    fun t1 ⟨⟨hm1, ha1, hx1⟩, k1⟩ => ?_
  refine WP.mono (VG.Proof.Ed448.X86_64.Verify.dbl_ok 8 t1) fun t2 ⟨⟨ha2, hm2, hx2⟩, k2⟩ => ?_
  have hsp2 : t2.gpr .rsp = L.SP := by rw [k2.gpr (by decide), k1.gpr (by decide), hc.rsp]
  have w8 : InRegions t2.wr (L.SP + BitVec.ofNat 64 8) 8 := by
    rw [k2.2.2, k1.2.2]; exact hc.inFrW (by omega)
  refine WP.mono (Q := fun t3 : State => t3.mem = t2.mem.writeW (L.SP + BitVec.ofNat 64 8) (t2.gpr .rax) ∧
      t3.gpr = t2.gpr ∧ t3.rd = t2.rd ∧ t3.wr = t2.wr ∧ t3.mxcsr = t2.mxcsr) ?_
    fun t3 ⟨hm3, hg3, hrd3, hwr3, hx3⟩ => ?_
  · apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store64, VG.Proof.Ed448.X86_64.Verify.ea_stk, fHdr, Nat.reduceAdd, hsp2,
      w8, ite_true, Option.some.injEq, exists_eq_left']
    exact ⟨trivial, trivial, trivial, trivial, trivial⟩
  have hm : t3.mem = (t.mem.writeW L.SP (BitVec.ofNat 64 sigEd448)).writeW (L.SP + BitVec.ofNat 64 8)
      (L.ctxLen * BitVec.ofNat 64 (2 ^ 8)) := by
    rw [hm3, ha2, ha1, hm2, hm1]
  have hf : VG.Frame ([⟨L.SP, 16⟩] ++ [⟨L.B, 16⟩]) t.mem t3.mem := by
    rw [hm]
    have c0 : (⟨L.SP, 16⟩ : Region).Contains L.SP 8 := by
      simpa only [VG.Proof.Ed448.X86_64.Verify.x0] using Offset.contains_base L.SP (d := 0) (n := 8) (k := 16) (by omega) (by omega)
    exact ((Frame.refl _ _).writeW (List.mem_cons_self ..) _ c0).writeW (List.mem_cons_self ..) _
      (Offset.contains_base _ (by omega) (by omega))
  refine ⟨hc.of_frame hL (hrd3.trans (k2.2.1.trans k1.2.1)) (hwr3.trans (k2.2.2.trans k1.2.2))
    (fun r hr => by
      rw [hg3, k2.gpr (by simp only [List.mem_singleton]; exact VG.Proof.Ed448.X86_64.Verify.ne_cs hr (by decide)),
        k1.gpr (by simp only [List.mem_singleton]; exact VG.Proof.Ed448.X86_64.Verify.ne_cs hr (by decide))])
    (by rw [hx3, hx2, hx1]) hf (fun r hr => ?_), ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact .inr (VG.Proof.Ed448.X86_64.Verify.within_base _ (by omega))
  · rw [hm]; exact VG.Proof.Ed448.X86_64.Verify.hdr_bytes _ _ _ hL.ctxLt

/-! ## Zeroing the state -/

/-- The first `n` stores of `zeroSt`. -/
abbrev zstores (n : Nat) : List Instr :=
  (List.range n).map fun k => .store { base := .rdi, disp := ((8 * k : Nat) : Int) } .rax

theorem zstore_ok {scr : Addr} {s : State} (hdi : s.gpr .rdi = scr) {k : Nat}
    (hw : InRegions s.wr (scr + BitVec.ofNat 64 (8 * k)) 8) :
    WP isa (.block [Instr.store { base := .rdi, disp := ((8 * k : Nat) : Int) } .rax]) s fun s' =>
      s'.mem = s.mem.writeW (scr + BitVec.ofNat 64 (8 * k)) (s.gpr .rax) ∧ s'.gpr = s.gpr ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store64, VG.Proof.Ed448.X86_64.Verify.ea_base, hdi, hw, ite_true,
    Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

theorem zstores_ok {scr : Addr} : ∀ n ≤ 25, ∀ s : State, s.gpr .rdi = scr → s.gpr .rax = 0 →
    (∀ j < 25, InRegions s.wr (scr + BitVec.ofNat 64 (8 * j)) 8) →
    WP isa (.block (VG.Proof.Ed448.X86_64.Verify.zstores n)) s fun s' => s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mxcsr = s.mxcsr ∧ VG.Frame [⟨scr, 200⟩] s.mem s'.mem ∧
      ∀ j < n, s'.mem.readW (scr + BitVec.ofNat 64 (8 * j)) 64 = 0
  | 0, _, _, _, _, _ => WP.block_nil ⟨rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hn, s, h1, h2, hw => by
    rw [VG.Proof.Ed448.X86_64.Verify.zstores, List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (VG.Proof.Ed448.X86_64.Verify.zstores_ok n (by omega) s h1 h2 hw) fun u ⟨ug, urd, uwr, umx, uf, uz⟩ => ?_
    refine WP.mono (VG.Proof.Ed448.X86_64.Verify.zstore_ok (scr := scr) (k := n) (by rw [ug]; exact h1) (by rw [uwr]; exact hw n (by omega)))
      fun v ⟨vm, vg, vrd, vwr, vmx⟩ => ?_
    have hf1 : VG.Frame [⟨scr, 200⟩] u.mem v.mem := by
      rw [vm]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    refine ⟨vg.trans ug, vrd.trans urd, vwr.trans uwr, vmx.trans umx, uf.trans hf1, fun j hj => ?_⟩
    rw [vm, ug, h2]
    by_cases hjk : j = n
    · subst hjk; exact Mem.readW_writeW_self64 _ _ _
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide), uz j (by omega)]

theorem zero_state {m : Mem} {p : Addr} (h : ∀ j < 25, m.readW (p + BitVec.ofNat 64 (8 * j)) 64 = 0) :
    stateAt m p = Spec.Sha3.zero := by
  apply Vector.ext
  intro i hi
  simp only [Spec.Sha3.stateAt, Spec.Sha3.zero, Vector.getElem_ofFn, Vector.getElem_replicate]
  exact h i hi

theorem zeroSt_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t) :
    WP isa VG.Impl.Ed448.X86_64.Verify.zeroSt t fun t' => VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t' ∧ VG.Frame [⟨L.ST, 200⟩] t.mem t'.mem ∧
      stateAt t'.mem L.ST = Spec.Sha3.zero := by
  refine WP.seq ?_
  show WP isa (.block (aSt.mov .rdi ++ [.mov32 .rax (.imm 0)])) t _
  rw [WP.block_append_iff]
  refine WP.mono (Arg.mov_ok .rdi VG.Impl.Ed448.X86_64.Verify.aSt (by decide) (by decide) t hc.frOk) fun t1 ⟨⟨h1, hm1, hx1⟩, k1⟩ => ?_
  refine WP.mono (WP.keep [.rax] (Q := fun s1 => s1.mem = t1.mem ∧ s1.gpr .rax = 0 ∧ s1.mxcsr = t1.mxcsr)
    (by xrun [RegUpd.mxcsr_setReg]) (by decide)) fun t2 ⟨⟨hm2, hax, hx2⟩, k2⟩ => ?_
  have hdi : t2.gpr .rdi = L.scr := (k2.gpr (by decide)).trans (h1.trans hc.aSt)
  have hw2 : t2.wr = L.FR :: L.wr := k2.2.2.trans (k1.2.2.trans hc.wr)
  refine WP.mono (VG.Proof.Ed448.X86_64.Verify.zstores_ok 25 (Nat.le_refl _) t2 hdi hax fun j hj => ?_)
    fun t3 ⟨g3, rd3, wr3, mx3, hf, hz⟩ => ?_
  · rw [hw2, hL.wr]
    exact ⟨L.SCR, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  · rw [hm2, hm1] at hf
    have hcs : ∀ r ∈ calleeSaved, t3.gpr r = t.gpr r := fun r hr => by
      rw [g3, k2.gpr (by simp only [List.mem_singleton]; exact VG.Proof.Ed448.X86_64.Verify.ne_cs hr (by decide)),
        k1.gpr (by simp only [List.mem_singleton]; exact VG.Proof.Ed448.X86_64.Verify.ne_cs hr (by decide))]
    have hf' : VG.Frame ([⟨L.ST, 200⟩] ++ [⟨L.B, 16⟩]) t.mem t3.mem :=
      hf.mono fun r hr => by simp at hr ⊢; exact .inl hr
    exact ⟨hc.of_frame hL (rd3.trans (k2.2.1.trans k1.2.1)) (wr3.trans (k2.2.2.trans k1.2.2)) hcs
      (by rw [mx3, hx2, hx1]) hf' (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact .inl VG.Proof.Ed448.X86_64.Verify.w_st), hf, VG.Proof.Ed448.X86_64.Verify.zero_state hz⟩

/-! ## Absorbing -/

/-- The arguments of a call of `vg_keccak_absorb`. -/
abbrev absArgs (src len pos : Arg) : List Arg := [VG.Impl.Ed448.X86_64.Verify.aSt, .imm 136, pos, src, len, VG.Impl.Ed448.X86_64.Verify.aKs]

theorem kabs_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t)
    {src len pos : Arg} (hok : (VG.Proof.Ed448.X86_64.Verify.absArgs src len pos).all Arg.ok = true)
    {dp : Addr} {n q : Nat} (hdp : src.val t = dp) (hn : len.val t = BitVec.ofNat 64 n)
    (hq : pos.val t = BitVec.ofNat 64 q) (hql : q < 136) (hnl : n < 2 ^ 64)
    (hin : ∃ R ∈ L.rd ++ L.FR :: L.wr, VG.Proof.Ed448.X86_64.Verify.Within ⟨dp, n⟩ R)
    (dS : Region.Disjoint ⟨dp, n⟩ ⟨L.ST, 200⟩) (dK : Region.Disjoint ⟨dp, n⟩ ⟨L.KS, 640⟩)
    (kD : Region.Disjoint ⟨L.B, 16⟩ ⟨dp, n⟩) :
    WP isa (VG.Impl.Ed448.X86_64.Verify.kabs src len pos) t fun t' => VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t' ∧
      VG.Frame [⟨L.ST, 200⟩, ⟨L.KS, 640⟩, ⟨L.B, 16⟩] t.mem t'.mem ∧
      (∀ msg, Repr t.mem L.ST 136 msg → q = msg.length % 136 →
        Repr t'.mem L.ST 136 (msg ++ VG.Spec.Sha3.bytesAt t.mem dp n)) ∧ (t'.gpr .rax).toNat = (q + n) % 136 := by
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86_64.Verify.setArgs_ok _ hok t hc.frOk) fun t1 ⟨⟨hA, hm, hx⟩, k⟩ => ?_)
  have hc1 : VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t1 := hc.regs k.2.1 k.2.2 hm hx fun r hr => k.gpr (VG.Proof.Ed448.X86_64.Verify.argRegs_cs r hr)
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := VG.Proof.Ed448.X86_64.Verify.argsIn6 hA
  rw [hc.aSt] at e1
  rw [hc.aKs] at e6
  rw [hdp] at e4
  rw [hn] at e5
  rw [hq] at e3
  have ha : AbsorbArgs t1 L.ST dp L.KS 136 q n :=
    ⟨e1, e2, e3, e4, e5, e6, by decide, hql, hnl, VG.Proof.Ed448.X86_64.Verify.st_ks L, dS, dK, VG.Proof.Ed448.X86_64.Verify.k16 hc1 (VG.Proof.Ed448.X86_64.Verify.k_st hL), VG.Proof.Ed448.X86_64.Verify.k16 hc1 kD,
      VG.Proof.Ed448.X86_64.Verify.k16 hc1 (VG.Proof.Ed448.X86_64.Verify.k_ks hL)⟩
  refine VG.Proof.Ed448.X86_64.Verify.call_ok hL Proof.Sha3.X86_64.Stream.Absorb.absorb_correct absorb_nosp (by rw [absorb_depth])
    hc1 (absorb_pre ha) (by simpa using hin) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [.inl VG.Proof.Ed448.X86_64.Verify.w_st, .inl VG.Proof.Ed448.X86_64.Verify.w_ks])
    fun s' hc' hf _ ⟨s₂, hm₂, hg₂, hpost, hrax⟩ => ?_
  have hn' := ofNat_toNat' hnl
  have hq' := ofNat_toNat' (show q < 2 ^ 64 by omega)
  simp only [State.withRegions_mem, VG.Proof.Ed448.X86_64.Verify.gpr_ce t1 _ _ (by decide : Reg.rdi ≠ .rsp),
    VG.Proof.Ed448.X86_64.Verify.gpr_ce t1 _ _ (by decide : Reg.rsi ≠ .rsp), VG.Proof.Ed448.X86_64.Verify.gpr_ce t1 _ _ (by decide : Reg.rdx ≠ .rsp),
    VG.Proof.Ed448.X86_64.Verify.gpr_ce t1 _ _ (by decide : Reg.rcx ≠ .rsp), VG.Proof.Ed448.X86_64.Verify.gpr_ce t1 _ _ (by decide : Reg.r8 ≠ .rsp),
    e1, e2, e3, e4, e5, hm₂, hn', hq'] at hpost hrax
  refine ⟨hc', by rw [← hm]; simpa using hf, fun msg hmsg hp => ?_, by rw [← hg₂ _ (by decide)]; exact hrax⟩
  have := hpost msg ((callEntry_repr t1 ha.k_st).mpr (hm ▸ hmsg)) hp
  rwa [callEntry_bytesAt t1 hnl ha.k_d, hm] at this

/-! ## Padding -/

/-- The arguments of a call of `vg_keccak_pad`. -/
abbrev padArgs (pos : Arg) : List Arg := [VG.Impl.Ed448.X86_64.Verify.aSt, .imm 136, pos, .imm 0x1f, VG.Impl.Ed448.X86_64.Verify.aKs]

theorem kpad_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t)
    {pos : Arg} (hok : (VG.Proof.Ed448.X86_64.Verify.padArgs pos).all Arg.ok = true) {q : Nat}
    (hq : pos.val t = BitVec.ofNat 64 q) (hql : q < 136) :
    WP isa (VG.Impl.Ed448.X86_64.Verify.kpad pos) t fun t' => VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t' ∧
      VG.Frame [⟨L.ST, 200⟩, ⟨L.KS, 640⟩, ⟨L.B, 16⟩] t.mem t'.mem ∧
      (∀ msg, Repr t.mem L.ST 136 msg → q = msg.length % 136 →
        stateAt t'.mem L.ST = absorb 136 (pad 136 Spec.Sha3.shakeSuffix msg)) := by
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86_64.Verify.setArgs_ok _ hok t hc.frOk) fun t1 ⟨⟨hA, hm, hx⟩, k⟩ => ?_)
  have hc1 : VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t1 := hc.regs k.2.1 k.2.2 hm hx fun r hr => k.gpr (VG.Proof.Ed448.X86_64.Verify.argRegs_cs r hr)
  obtain ⟨e1, e2, e3, e4, e5⟩ := VG.Proof.Ed448.X86_64.Verify.argsIn5 hA
  rw [hc.aSt] at e1
  rw [hc.aKs] at e5
  rw [hq] at e3
  have ha : PadArgs t1 L.ST L.KS 136 q :=
    ⟨e1, e2, e3, e5, by decide, hql, VG.Proof.Ed448.X86_64.Verify.st_ks L, VG.Proof.Ed448.X86_64.Verify.k16 hc1 (VG.Proof.Ed448.X86_64.Verify.k_st hL), VG.Proof.Ed448.X86_64.Verify.k16 hc1 (VG.Proof.Ed448.X86_64.Verify.k_ks hL)⟩
  refine VG.Proof.Ed448.X86_64.Verify.call_ok hL Proof.Sha3.X86_64.Stream.Pad.pad_correct pad_nosp (by rw [pad_depth])
    hc1 (pad_pre ha) (by simp) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [.inl VG.Proof.Ed448.X86_64.Verify.w_st, .inl VG.Proof.Ed448.X86_64.Verify.w_ks])
    fun s' hc' hf _ ⟨s₂, hm₂, _, hpost⟩ => ?_
  have hq' := ofNat_toNat' (show q < 2 ^ 64 by omega)
  simp only [Proof.Sha3.padX86_64, State.withRegions_mem, VG.Proof.Ed448.X86_64.Verify.gpr_ce t1 _ _ (by decide : Reg.rdi ≠ .rsp),
    VG.Proof.Ed448.X86_64.Verify.gpr_ce t1 _ _ (by decide : Reg.rsi ≠ .rsp), VG.Proof.Ed448.X86_64.Verify.gpr_ce t1 _ _ (by decide : Reg.rdx ≠ .rsp),
    VG.Proof.Ed448.X86_64.Verify.gpr_ce t1 _ _ (by decide : Reg.rcx ≠ .rsp), e1, e2, e3, e4, hm₂, hq'] at hpost
  refine ⟨hc', by rw [← hm]; simpa using hf, fun msg hmsg hp => ?_⟩
  have := hpost msg ((callEntry_repr t1 ha.k_st).mpr (hm ▸ hmsg)) hp
  rw [this]
  rfl

/-! ## Squeezing -/

/-- The arguments of a call of `vg_keccak_squeeze`. -/
abbrev sqzArgs : List Arg := [VG.Impl.Ed448.X86_64.Verify.aSt, .imm 136, .imm 0, .sp fH, .imm 114, VG.Impl.Ed448.X86_64.Verify.aKs]

theorem ksqz_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t) :
    WP isa VG.Impl.Ed448.X86_64.Verify.ksqz t fun t' => VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t' ∧
      VG.Frame [⟨L.ST, 200⟩, ⟨L.H, 114⟩, ⟨L.KS, 640⟩, ⟨L.B, 16⟩] t.mem t'.mem ∧
      VG.Spec.Sha3.bytesAt t'.mem L.H 114 = squeezeFrom 136 (stateAt t.mem L.ST) 0 114 := by
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86_64.Verify.setArgs_ok VG.Proof.Ed448.X86_64.Verify.sqzArgs (by decide) t hc.frOk) fun t1 ⟨⟨hA, hm, hx⟩, k⟩ => ?_)
  have hc1 : VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t1 := hc.regs k.2.1 k.2.2 hm hx fun r hr => k.gpr (VG.Proof.Ed448.X86_64.Verify.argRegs_cs r hr)
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := VG.Proof.Ed448.X86_64.Verify.argsIn6 hA
  rw [hc.aSt] at e1
  rw [hc.aKs] at e6
  rw [hc.sp] at e4
  change t1.gpr .rcx = L.H at e4
  have ha : SqueezeArgs t1 L.ST L.H L.KS 136 0 114 :=
    ⟨e1, e2, e3, e4, e5, e6, by decide, by decide, by decide, VG.Proof.Ed448.X86_64.Verify.st_h hL, VG.Proof.Ed448.X86_64.Verify.st_ks L, VG.Proof.Ed448.X86_64.Verify.h_ks hL, VG.Proof.Ed448.X86_64.Verify.k16 hc1 (VG.Proof.Ed448.X86_64.Verify.k_st hL),
      VG.Proof.Ed448.X86_64.Verify.k16 hc1 VG.Proof.Ed448.X86_64.Verify.k_h, VG.Proof.Ed448.X86_64.Verify.k16 hc1 (VG.Proof.Ed448.X86_64.Verify.k_ks hL)⟩
  refine VG.Proof.Ed448.X86_64.Verify.call_ok hL Proof.Sha3.X86_64.Stream.Squeeze.squeeze_correct squeeze_nosp
    (by rw [squeeze_depth]) hc1 (squeeze_pre ha) (by simp) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [.inl VG.Proof.Ed448.X86_64.Verify.w_st, .inr VG.Proof.Ed448.X86_64.Verify.w_h, .inl VG.Proof.Ed448.X86_64.Verify.w_ks])
    fun s' hc' hf _ ⟨s₂, hm₂, _, hpost, _⟩ => ?_
  simp only [State.withRegions_mem, VG.Proof.Ed448.X86_64.Verify.gpr_ce t1 _ _ (by decide : Reg.rdi ≠ .rsp),
    VG.Proof.Ed448.X86_64.Verify.gpr_ce t1 _ _ (by decide : Reg.rsi ≠ .rsp), VG.Proof.Ed448.X86_64.Verify.gpr_ce t1 _ _ (by decide : Reg.rdx ≠ .rsp),
    VG.Proof.Ed448.X86_64.Verify.gpr_ce t1 _ _ (by decide : Reg.rcx ≠ .rsp), VG.Proof.Ed448.X86_64.Verify.gpr_ce t1 _ _ (by decide : Reg.r8 ≠ .rsp),
    e1, e2, e3, e4, e5, hm₂, Arg.val, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hpost
  refine ⟨hc', by rw [← hm]; simpa using hf, ?_⟩
  rw [hpost, callEntry_stateAt t1 ha.k_st, hm]

/-! ## The hash -/

theorem ofNat_toNat_self (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt]

theorem ofNat_toNat_eq {x : BitVec 64} {n : Nat} (h : x.toNat = n) : x = BitVec.ofNat 64 n := by
  subst h; exact (VG.Proof.Ed448.X86_64.Verify.ofNat_toNat_self x).symm

/-- `SHAKE256(dom4(0, C) ‖ R ‖ A ‖ M, 114)` in the frame, with the first ten
bytes of `dom4` as the frame holds them. -/
theorem hash_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t) :
    WP isa hash t fun t' => VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t' ∧
      VG.Spec.Sha3.bytesAt t'.mem L.H 114 = Spec.Sha3.shake256 (VG.Spec.Sha3.bytesAt t.mem L.SP 10 ++
        VG.Spec.Sha3.bytesAt m₀ L.ctx L.ctxLen.toNat ++ VG.Spec.Sha3.bytesAt m₀ L.sig 57 ++ VG.Spec.Sha3.bytesAt m₀ L.pk 57 ++
        VG.Spec.Sha3.bytesAt m₀ L.msg L.len.toNat) 114 := by
  have hctx := hL.ctxLt
  have hS : Region.Disjoint ⟨L.SP, 10⟩ ⟨L.ST, 200⟩ := by
    have := hL.stk_x (d := 16) (n := 10) (e := 0) (k := 200) (by omega) (by omega)
    simpa only [VG.Proof.Ed448.X86_64.Verify.x0] using this
  have hK : Region.Disjoint ⟨L.SP, 10⟩ ⟨L.KS, 640⟩ := hL.stk_x (d := 16) (n := 10) (by omega) (by omega)
  have kH : Region.Disjoint ⟨L.B, 16⟩ ⟨L.SP, 10⟩ := Offset.base_disjoint _ (by omega) (by omega)
  -- Zero the state.
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86_64.Verify.zeroSt_ok hL hc) fun t1 ⟨hc1, hf1, hz⟩ => ?_)
  have eh : VG.Spec.Sha3.bytesAt t1.mem L.SP 10 = VG.Spec.Sha3.bytesAt t.mem L.SP 10 :=
    VG.Proof.Ed448.X86_64.Verify.bytesAt_congr fun i hi => hf1.bytes (R := ⟨L.SP, 10⟩) (by simpa using hS) (show (10 : Nat) ≤ 2 ^ 64 by decide) hi
  have hR1 : Repr t1.mem L.ST 136 [] := PublicKey.repr_nil hz
  -- The header of `dom4`, in the frame.
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86_64.Verify.kabs_ok hL hc1 (by decide) (dp := L.SP) (n := 10) (q := 0)
    (by rw [hc1.sp]; exact VG.Proof.Ed448.X86_64.Verify.x0 _) rfl rfl (by decide) (by decide) ⟨L.FR, by simp, VG.Proof.Ed448.X86_64.Verify.within_base _ (by omega)⟩
    hS hK kH) fun t2 ⟨hc2, _, hR2, hx2⟩ => ?_)
  have hR2 := hR2 [] hR1 rfl
  -- The context.
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86_64.Verify.kabs_ok hL hc2 (by decide) (dp := L.ctx) (n := L.ctxLen.toNat)
    (by rw [hc2.slot]; exact hc2.pCtx) (by rw [hc2.slot]; exact hc2.pCtxLen.trans (VG.Proof.Ed448.X86_64.Verify.ofNat_toNat_self _).symm)
    (VG.Proof.Ed448.X86_64.Verify.ofNat_toNat_eq hx2) (by omega) (by omega) ⟨L.CTX, List.mem_append_left _ hL.inCtx, VG.Proof.Ed448.X86_64.Verify.within_self _⟩
    (by have := hL.x_r hL.xCtx (e := 0) (k := 200) (by omega); simpa only [VG.Proof.Ed448.X86_64.Verify.x0] using this.symm)
    (hL.x_r hL.xCtx (e := 256) (k := 640) (by omega)).symm (VG.Proof.Ed448.X86_64.Verify.k_r hL hL.kCtx))
    fun t3 ⟨hc3, _, hR3, hx3⟩ => ?_)
  have hR3 := hR3 _ hR2 (by simp only [List.length_append, List.length_nil, VG.Proof.Ed448.X86_64.Verify.bytesAt_length] <;> omega)
  rw [hc2.bytesAt_eq hL.xCtx hL.kCtx (by have := hL.nCtx; omega)] at hR3
  -- `R`.
  have xR := hL.xSig.sub_right VG.Proof.Ed448.X86_64.Verify.r57_sub
  have kR := hL.kSig.sub_right VG.Proof.Ed448.X86_64.Verify.r57_sub
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86_64.Verify.kabs_ok hL hc3 (by decide) (dp := L.sig) (n := 57)
    (by rw [hc3.slot]; exact hc3.pSig) rfl (VG.Proof.Ed448.X86_64.Verify.ofNat_toNat_eq hx3) (Nat.mod_lt _ (by decide)) (by decide)
    ⟨L.SIG, List.mem_append_left _ hL.inSig, VG.Proof.Ed448.X86_64.Verify.within_base _ (by omega)⟩
    (by have := hL.x_r xR (e := 0) (k := 200) (by omega); simpa only [VG.Proof.Ed448.X86_64.Verify.x0] using this.symm)
    (hL.x_r xR (e := 256) (k := 640) (by omega)).symm (VG.Proof.Ed448.X86_64.Verify.k_r hL kR))
    fun t4 ⟨hc4, _, hR4, hx4⟩ => ?_)
  have hR4 := hR4 _ hR3 (by simp only [List.length_append, List.length_nil, VG.Proof.Ed448.X86_64.Verify.bytesAt_length] <;> omega)
  rw [hc3.bytesAt_eq xR kR (by decide)] at hR4
  -- `A`.
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86_64.Verify.kabs_ok hL hc4 (by decide) (dp := L.pk) (n := 57)
    (by rw [hc4.slot]; exact hc4.pPk) rfl (VG.Proof.Ed448.X86_64.Verify.ofNat_toNat_eq hx4) (Nat.mod_lt _ (by decide)) (by decide)
    ⟨L.PK, List.mem_append_left _ hL.inPk, VG.Proof.Ed448.X86_64.Verify.within_self _⟩
    (by have := hL.x_r hL.xPk (e := 0) (k := 200) (by omega); simpa only [VG.Proof.Ed448.X86_64.Verify.x0] using this.symm)
    (hL.x_r hL.xPk (e := 256) (k := 640) (by omega)).symm (VG.Proof.Ed448.X86_64.Verify.k_r hL hL.kPk))
    fun t5 ⟨hc5, _, hR5, hx5⟩ => ?_)
  have hR5 := hR5 _ hR4 (by simp only [List.length_append, List.length_nil, VG.Proof.Ed448.X86_64.Verify.bytesAt_length] <;> omega)
  rw [hc4.bytesAt_eq hL.xPk hL.kPk (by decide)] at hR5
  -- The message.
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86_64.Verify.kabs_ok hL hc5 (by decide) (dp := L.msg) (n := L.len.toNat)
    (by rw [hc5.slot]; exact hc5.pMsg) (by rw [hc5.slot]; exact hc5.pLen.trans (VG.Proof.Ed448.X86_64.Verify.ofNat_toNat_self _).symm)
    (VG.Proof.Ed448.X86_64.Verify.ofNat_toNat_eq hx5) (Nat.mod_lt _ (by decide)) L.len.isLt
    ⟨L.MSG, List.mem_append_left _ hL.inMsg, VG.Proof.Ed448.X86_64.Verify.within_self _⟩
    (by have := hL.x_r hL.xMsg (e := 0) (k := 200) (by omega); simpa only [VG.Proof.Ed448.X86_64.Verify.x0] using this.symm)
    (hL.x_r hL.xMsg (e := 256) (k := 640) (by omega)).symm (VG.Proof.Ed448.X86_64.Verify.k_r hL hL.kMsg))
    fun t6 ⟨hc6, _, hR6, hx6⟩ => ?_)
  have hR6 := hR6 _ hR5 (by simp only [List.length_append, List.length_nil, VG.Proof.Ed448.X86_64.Verify.bytesAt_length] <;> omega)
  rw [hc5.bytesAt_eq hL.xMsg hL.kMsg (by have := hL.nMsg; omega)] at hR6
  -- Pad and squeeze.
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86_64.Verify.kpad_ok hL hc6 (by decide) (VG.Proof.Ed448.X86_64.Verify.ofNat_toNat_eq hx6) (Nat.mod_lt _ (by decide)))
    fun t7 ⟨hc7, _, hS7⟩ => ?_)
  have hS7 := hS7 _ hR6 (by simp only [List.length_append, List.length_nil, VG.Proof.Ed448.X86_64.Verify.bytesAt_length] <;> omega)
  refine WP.mono (VG.Proof.Ed448.X86_64.Verify.ksqz_ok hL hc7) fun t8 ⟨hc8, _, hm8⟩ => ⟨hc8, ?_⟩
  rw [hm8, hS7, PublicKey.shake256_eq, List.nil_append, eh]

end

end VG.Proof.Ed448.X86_64.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86_64.Verify.HashCT`. -/
section

/-!
# Ed448 verification on x86-64: the hash leaks only the layout

Two runs (`Two`) of the zeroing of the Keccak state and of the calls of the
sponge functions, whose arguments are the same in both runs (functions of
the layout), leak the same (`zeroSt_tr`, `kabs_tr`, `kpad_tr`, `ksqz_tr`);
and so does `hash` (`hash_tr`), each absorption starting at the position the
previous one returned, a function of the lengths.
-/

namespace VG.Proof.Ed448.X86_64.Verify

open VG VG.X86_64 VG.Impl.Ed448.X86_64.Verify
open VG.Proof.MlKem.X86_64 (Keep WP.keep AbsorbArgs PadArgs SqueezeArgs absorb_pre pad_pre squeeze_pre)

section
variable {I : VG.Proof.Ed448.X86_64.Verify.Lay → Mem → Mem → Prop}

/-! ## Zeroing the state -/

theorem zhead_ok {L : VG.Proof.Ed448.X86_64.Verify.Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem} {t : State}
    (hc : VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t) :
    WP isa (.block [.mov .rdi (.mem (stk fScr)), .mov32 .rax (.imm 0)]) t fun t2 =>
      VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t2 ∧ t2.gpr .rdi = L.ST := by
  show WP isa (.block (aSt.mov .rdi ++ [.mov32 .rax (.imm 0)])) t _
  rw [WP.block_append_iff]
  refine WP.mono (Arg.mov_ok .rdi VG.Impl.Ed448.X86_64.Verify.aSt (by decide) (by decide) t hc.frOk) fun t1 ⟨⟨h1, hm1, hx1⟩, k1⟩ => ?_
  refine WP.mono (WP.keep [.rax] (Q := fun s1 => s1.mem = t1.mem ∧ s1.mxcsr = t1.mxcsr)
    (by xrun [RegUpd.mxcsr_setReg]) (by decide)) fun t2 ⟨⟨hm2, hx2⟩, k2⟩ => ?_
  have hc1 : VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t1 := hc.regs k1.2.1 k1.2.2 hm1 hx1 fun r hr => k1.gpr (by
    simp only [List.mem_singleton]; exact VG.Proof.Ed448.X86_64.Verify.ne_cs hr (by decide))
  exact ⟨hc1.regs k2.2.1 k2.2.2 hm2 hx2 fun r hr => k2.gpr (by
    simp only [List.mem_singleton]; exact VG.Proof.Ed448.X86_64.Verify.ne_cs hr (by decide)), (k2.gpr (by decide)).trans (h1.trans hc.aSt)⟩

theorem zeroSt_tr {Φ : VG.Proof.Ed448.X86_64.Verify.Lay → Mem → State → Prop} : RelCT isa (VG.Proof.Ed448.X86_64.Verify.Two I Φ) VG.Impl.Ed448.X86_64.Verify.zeroSt fun _ _ => True := by
  have h1 := VG.Proof.Ed448.X86_64.Verify.two_wp (I := I) (Φ := Φ) (Ψ := fun L _ t => t.gpr .rdi = L.ST)
    (c := .block [.mov .rdi (.mem (stk fScr)), .mov32 .rax (.imm 0)])
    (VG.Proof.Ed448.X86_64.Verify.block_rsp_tr (fun i hi => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · exact ⟨fun s₁ s₂ h => by simp [addrs, srcAddrs, State.ea, stk, h], rfl⟩
        · exact VG.Proof.Ed448.X86_64.Verify.spOnly_nomem (fun _ => rfl) rfl) fun _ _ h => h.rsp)
    fun _ _ _ _ _ _ hc _ => VG.Proof.Ed448.X86_64.Verify.zhead_ok hc
  refine RelCT.seq h1 (RelCT.taint (A := taint) (Taint.ofRegs [.rsp, .rdi]) (fun a b hab => ?_) (by taint_decide))
  obtain ⟨L, _, _, _, _, _, _, _, _, c₁, c₂, f₁, f₂⟩ := hab
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [c₁.rsp, c₂.rsp]
  · rw [f₁, f₂]

/-! ## The sponge functions -/

/-- The arguments of a call of `vg_keccak_absorb`, after the moves. -/
theorem kabsArgs {L : VG.Proof.Ed448.X86_64.Verify.Lay} (hL : L.Ok) {g mx m₀} {t t1 : State} (hc : VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t)
    {src len pos : Arg} (hm : VG.Proof.Ed448.X86_64.Verify.Moved (VG.Proof.Ed448.X86_64.Verify.absArgs src len pos) t t1) {dp : Addr} {n q : Nat}
    (hdp : src.val t = dp) (hn : len.val t = BitVec.ofNat 64 n) (hq : pos.val t = BitVec.ofNat 64 q)
    (hql : q < 136) (hnl : n < 2 ^ 64) (dS : Region.Disjoint ⟨dp, n⟩ ⟨L.ST, 200⟩)
    (dK : Region.Disjoint ⟨dp, n⟩ ⟨L.KS, 640⟩) (kD : Region.Disjoint ⟨L.B, 16⟩ ⟨dp, n⟩) :
    AbsorbArgs t1 L.ST dp L.KS 136 q n := by
  have hc1 : VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t1 := hc.regs hm.2.2.1 hm.2.2.2 hm.1.2.1 hm.1.2.2 fun r hr => hm.2.gpr (VG.Proof.Ed448.X86_64.Verify.argRegs_cs r hr)
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := VG.Proof.Ed448.X86_64.Verify.argsIn6 hm.1.1
  rw [hc.aSt] at e1
  rw [hc.aKs] at e6
  rw [hdp] at e4
  rw [hn] at e5
  rw [hq] at e3
  exact ⟨e1, e2, e3, e4, e5, e6, by decide, hql, hnl, VG.Proof.Ed448.X86_64.Verify.st_ks L, dS, dK, VG.Proof.Ed448.X86_64.Verify.k16 hc1 (VG.Proof.Ed448.X86_64.Verify.k_st hL), VG.Proof.Ed448.X86_64.Verify.k16 hc1 kD,
    VG.Proof.Ed448.X86_64.Verify.k16 hc1 (VG.Proof.Ed448.X86_64.Verify.k_ks hL)⟩

theorem w_scr {L : VG.Proof.Ed448.X86_64.Verify.Lay} (hL : L.Ok) {r : Region} (h : VG.Proof.Ed448.X86_64.Verify.Within r L.SCR) : ∃ R ∈ L.FR :: L.wr, VG.Proof.Ed448.X86_64.Verify.Within r R :=
  ⟨L.SCR, by simp [hL.wr], h⟩

/-- Two runs of a call of `vg_keccak_absorb` whose arguments are the same
functions of the layout in both. -/
theorem kabs_tr {Φ : VG.Proof.Ed448.X86_64.Verify.Lay → Mem → State → Prop} {src len pos : Arg}
    (hok : (VG.Proof.Ed448.X86_64.Verify.absArgs src len pos).all Arg.ok = true) (dp : VG.Proof.Ed448.X86_64.Verify.Lay → Addr) (n q : VG.Proof.Ed448.X86_64.Verify.Lay → Nat)
    (hv : ∀ (L : VG.Proof.Ed448.X86_64.Verify.Lay) g mx m (t : State), L.Ok → VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m t → Φ L m t →
      src.val t = dp L ∧ len.val t = BitVec.ofNat 64 (n L) ∧ pos.val t = BitVec.ofNat 64 (q L))
    (hs : ∀ L : VG.Proof.Ed448.X86_64.Verify.Lay, L.Ok → q L < 136 ∧ n L < 2 ^ 64 ∧ (∃ R ∈ L.rd ++ L.FR :: L.wr, VG.Proof.Ed448.X86_64.Verify.Within ⟨dp L, n L⟩ R) ∧
      Region.Disjoint ⟨dp L, n L⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨dp L, n L⟩ ⟨L.KS, 640⟩ ∧
      Region.Disjoint ⟨L.B, 16⟩ ⟨dp L, n L⟩) :
    RelCT isa (VG.Proof.Ed448.X86_64.Verify.Two I Φ) (VG.Impl.Ed448.X86_64.Verify.kabs src len pos) fun _ _ => True := by
  have args : ∀ (L : VG.Proof.Ed448.X86_64.Verify.Lay) g mx m₀ (t t1 : State), L.Ok → VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t → Φ L m₀ t →
      VG.Proof.Ed448.X86_64.Verify.Moved (VG.Proof.Ed448.X86_64.Verify.absArgs src len pos) t t1 → AbsorbArgs t1 L.ST (dp L) L.KS 136 (q L) (n L) :=
    fun L g mx m₀ t t1 hL hc hφ hm => by
      obtain ⟨h1, h2, h3⟩ := hv L g mx m₀ t hL hc hφ
      obtain ⟨s1, s2, _, s4, s5, s6⟩ := hs L hL
      exact VG.Proof.Ed448.X86_64.Verify.kabsArgs hL hc hm h1 h2 h3 s1 s2 s4 s5 s6
  refine VG.Proof.Ed448.X86_64.Verify.call_tr hok Proof.Sha3.X86_64.Stream.Absorb.absorb_correct
    Proof.Sha3.X86_64.Stream.Absorb.absorb_ct (fun L => [⟨dp L, n L⟩]) (fun L => [⟨L.ST, 200⟩, ⟨L.KS, 640⟩])
    (fun L g mx m₀ t t1 hL hc hφ hm => absorb_pre (args L g mx m₀ t t1 hL hc hφ hm))
    (fun L g₁ g₂ mx₁ mx₂ m₁ m₂ a b a1 b1 hL _ c₁ c₂ φ₁ φ₂ f₁ f₂ => ?_) fun L _ _ _ _ hL _ _ => ?_
  · have x := args L g₁ mx₁ m₁ a a1 hL c₁ φ₁ f₁
    have y := args L g₂ mx₂ m₂ b b1 hL c₂ φ₂ f₂
    simp only [Proof.Sha3.absorbX86_64, VG.Proof.Ed448.X86_64.Verify.gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp),
      VG.Proof.Ed448.X86_64.Verify.gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp), VG.Proof.Ed448.X86_64.Verify.gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp),
      VG.Proof.Ed448.X86_64.Verify.gpr_ce _ _ _ (by decide : Reg.rcx ≠ .rsp), VG.Proof.Ed448.X86_64.Verify.gpr_ce _ _ _ (by decide : Reg.r8 ≠ .rsp),
      VG.Proof.Ed448.X86_64.Verify.gpr_ce _ _ _ (by decide : Reg.r9 ≠ .rsp), VG.Proof.Ed448.X86_64.Verify.rsp_ce, x.rdi, x.rsi, x.rdx, x.rcx, x.r8, x.r9, y.rdi, y.rsi,
      y.rdx, y.rcx, y.r8, y.r9, f₁.2.gpr (by decide : Reg.rsp ∉ argRegs), f₂.2.gpr (by decide : Reg.rsp ∉ argRegs),
      c₁.rsp, c₂.rsp, and_self]
  · obtain ⟨_, _, hin, _, _, _⟩ := hs L hL
    refine ⟨fun r hr => ?_, fun r hr => ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact hin
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [VG.Proof.Ed448.X86_64.Verify.w_scr hL VG.Proof.Ed448.X86_64.Verify.w_st, VG.Proof.Ed448.X86_64.Verify.w_scr hL VG.Proof.Ed448.X86_64.Verify.w_ks]

/-- The position in `rax`, a function of the layout. -/
abbrev Pos (q : VG.Proof.Ed448.X86_64.Verify.Lay → Nat) : VG.Proof.Ed448.X86_64.Verify.Lay → Mem → State → Prop := fun L _ t => (t.gpr .rax).toNat = q L

/-- An absorption, with the position it returns. -/
theorem kabs_two {Φ : VG.Proof.Ed448.X86_64.Verify.Lay → Mem → State → Prop} {src len pos : Arg}
    (hok : (VG.Proof.Ed448.X86_64.Verify.absArgs src len pos).all Arg.ok = true) (dp : VG.Proof.Ed448.X86_64.Verify.Lay → Addr) (n q : VG.Proof.Ed448.X86_64.Verify.Lay → Nat)
    (hv : ∀ (L : VG.Proof.Ed448.X86_64.Verify.Lay) g mx m (t : State), L.Ok → VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m t → Φ L m t →
      src.val t = dp L ∧ len.val t = BitVec.ofNat 64 (n L) ∧ pos.val t = BitVec.ofNat 64 (q L))
    (hs : ∀ L : VG.Proof.Ed448.X86_64.Verify.Lay, L.Ok → q L < 136 ∧ n L < 2 ^ 64 ∧ (∃ R ∈ L.rd ++ L.FR :: L.wr, VG.Proof.Ed448.X86_64.Verify.Within ⟨dp L, n L⟩ R) ∧
      Region.Disjoint ⟨dp L, n L⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨dp L, n L⟩ ⟨L.KS, 640⟩ ∧
      Region.Disjoint ⟨L.B, 16⟩ ⟨dp L, n L⟩) :
    RelCT isa (VG.Proof.Ed448.X86_64.Verify.Two I Φ) (VG.Impl.Ed448.X86_64.Verify.kabs src len pos) (VG.Proof.Ed448.X86_64.Verify.Two I (VG.Proof.Ed448.X86_64.Verify.Pos fun L => (q L + n L) % 136)) :=
  VG.Proof.Ed448.X86_64.Verify.two_wp (VG.Proof.Ed448.X86_64.Verify.kabs_tr hok dp n q hv hs) fun L g mx m₀ t hL hc hφ => by
    obtain ⟨h1, h2, h3⟩ := hv L g mx m₀ t hL hc hφ
    obtain ⟨a, b, c, d, e, f⟩ := hs L hL
    exact WP.mono (VG.Proof.Ed448.X86_64.Verify.kabs_ok hL hc hok h1 h2 h3 a b c d e f) fun t' ⟨hc', _, _, hx⟩ => ⟨hc', hx⟩

theorem kpad_tr {Φ : VG.Proof.Ed448.X86_64.Verify.Lay → Mem → State → Prop} {pos : Arg}
    (hok : (VG.Proof.Ed448.X86_64.Verify.padArgs pos).all Arg.ok = true) (q : VG.Proof.Ed448.X86_64.Verify.Lay → Nat)
    (hv : ∀ (L : VG.Proof.Ed448.X86_64.Verify.Lay) g mx m (t : State), L.Ok → VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m t → Φ L m t → pos.val t = BitVec.ofNat 64 (q L))
    (hs : ∀ L : VG.Proof.Ed448.X86_64.Verify.Lay, L.Ok → q L < 136) :
    RelCT isa (VG.Proof.Ed448.X86_64.Verify.Two I Φ) (VG.Impl.Ed448.X86_64.Verify.kpad pos) fun _ _ => True := by
  have args : ∀ (L : VG.Proof.Ed448.X86_64.Verify.Lay) g mx m₀ (t t1 : State), L.Ok → VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t → Φ L m₀ t →
      VG.Proof.Ed448.X86_64.Verify.Moved (VG.Proof.Ed448.X86_64.Verify.padArgs pos) t t1 → PadArgs t1 L.ST L.KS 136 (q L) :=
    fun L g mx m₀ t t1 hL hc hφ hm => by
      have hc1 : VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t1 :=
        hc.regs hm.2.2.1 hm.2.2.2 hm.1.2.1 hm.1.2.2 fun r hr => hm.2.gpr (VG.Proof.Ed448.X86_64.Verify.argRegs_cs r hr)
      obtain ⟨e1, e2, e3, _, e5⟩ := VG.Proof.Ed448.X86_64.Verify.argsIn5 hm.1.1
      rw [hc.aSt] at e1
      rw [hc.aKs] at e5
      rw [hv L g mx m₀ t hL hc hφ] at e3
      exact ⟨e1, e2, e3, e5, by decide, hs L hL, VG.Proof.Ed448.X86_64.Verify.st_ks L, VG.Proof.Ed448.X86_64.Verify.k16 hc1 (VG.Proof.Ed448.X86_64.Verify.k_st hL), VG.Proof.Ed448.X86_64.Verify.k16 hc1 (VG.Proof.Ed448.X86_64.Verify.k_ks hL)⟩
  refine VG.Proof.Ed448.X86_64.Verify.call_tr hok Proof.Sha3.X86_64.Stream.Pad.pad_correct Proof.Sha3.X86_64.Stream.Pad.pad_ct
    (fun _ => []) (fun L => [⟨L.ST, 200⟩, ⟨L.KS, 640⟩])
    (fun L g mx m₀ t t1 hL hc hφ hm => pad_pre (args L g mx m₀ t t1 hL hc hφ hm))
    (fun L g₁ g₂ mx₁ mx₂ m₁ m₂ a b a1 b1 hL _ c₁ c₂ φ₁ φ₂ f₁ f₂ => ?_) fun L _ _ _ _ hL _ _ => ?_
  · have x := args L g₁ mx₁ m₁ a a1 hL c₁ φ₁ f₁
    have y := args L g₂ mx₂ m₂ b b1 hL c₂ φ₂ f₂
    simp only [Proof.Sha3.padX86_64, VG.Proof.Ed448.X86_64.Verify.gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp),
      VG.Proof.Ed448.X86_64.Verify.gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp), VG.Proof.Ed448.X86_64.Verify.gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp),
      VG.Proof.Ed448.X86_64.Verify.gpr_ce _ _ _ (by decide : Reg.r8 ≠ .rsp), VG.Proof.Ed448.X86_64.Verify.rsp_ce, x.rdi, x.rsi, x.rdx, x.r8, y.rdi, y.rsi, y.rdx, y.r8,
      f₁.2.gpr (by decide : Reg.rsp ∉ argRegs), f₂.2.gpr (by decide : Reg.rsp ∉ argRegs), c₁.rsp, c₂.rsp,
      and_self]
  · refine ⟨fun r hr => by simp at hr, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [VG.Proof.Ed448.X86_64.Verify.w_scr hL VG.Proof.Ed448.X86_64.Verify.w_st, VG.Proof.Ed448.X86_64.Verify.w_scr hL VG.Proof.Ed448.X86_64.Verify.w_ks]

theorem ksqz_tr {Φ : VG.Proof.Ed448.X86_64.Verify.Lay → Mem → State → Prop} : RelCT isa (VG.Proof.Ed448.X86_64.Verify.Two I Φ) VG.Impl.Ed448.X86_64.Verify.ksqz fun _ _ => True := by
  have args : ∀ (L : VG.Proof.Ed448.X86_64.Verify.Lay) g mx m₀ (t t1 : State), L.Ok → VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t → Φ L m₀ t →
      VG.Proof.Ed448.X86_64.Verify.Moved VG.Proof.Ed448.X86_64.Verify.sqzArgs t t1 → SqueezeArgs t1 L.ST L.H L.KS 136 0 114 :=
    fun L g mx m₀ t t1 hL hc _ hm => by
      have hc1 : VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t1 :=
        hc.regs hm.2.2.1 hm.2.2.2 hm.1.2.1 hm.1.2.2 fun r hr => hm.2.gpr (VG.Proof.Ed448.X86_64.Verify.argRegs_cs r hr)
      obtain ⟨e1, e2, e3, e4, e5, e6⟩ := VG.Proof.Ed448.X86_64.Verify.argsIn6 hm.1.1
      rw [hc.aSt] at e1
      rw [hc.aKs] at e6
      rw [hc.sp] at e4
      exact ⟨e1, e2, e3, e4, e5, e6, by decide, by decide, by decide, VG.Proof.Ed448.X86_64.Verify.st_h hL, VG.Proof.Ed448.X86_64.Verify.st_ks L, VG.Proof.Ed448.X86_64.Verify.h_ks hL,
        VG.Proof.Ed448.X86_64.Verify.k16 hc1 (VG.Proof.Ed448.X86_64.Verify.k_st hL), VG.Proof.Ed448.X86_64.Verify.k16 hc1 VG.Proof.Ed448.X86_64.Verify.k_h, VG.Proof.Ed448.X86_64.Verify.k16 hc1 (VG.Proof.Ed448.X86_64.Verify.k_ks hL)⟩
  refine VG.Proof.Ed448.X86_64.Verify.call_tr (by decide) Proof.Sha3.X86_64.Stream.Squeeze.squeeze_correct
    Proof.Sha3.X86_64.Stream.Squeeze.squeeze_ct (fun _ => []) (fun L => [⟨L.ST, 200⟩, ⟨L.H, 114⟩, ⟨L.KS, 640⟩])
    (fun L g mx m₀ t t1 hL hc hφ hm => squeeze_pre (args L g mx m₀ t t1 hL hc hφ hm))
    (fun L g₁ g₂ mx₁ mx₂ m₁ m₂ a b a1 b1 hL _ c₁ c₂ φ₁ φ₂ f₁ f₂ => ?_) fun L _ _ _ _ hL _ _ => ?_
  · have x := args L g₁ mx₁ m₁ a a1 hL c₁ φ₁ f₁
    have y := args L g₂ mx₂ m₂ b b1 hL c₂ φ₂ f₂
    simp only [Proof.Sha3.squeezeX86_64, VG.Proof.Ed448.X86_64.Verify.gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp),
      VG.Proof.Ed448.X86_64.Verify.gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp), VG.Proof.Ed448.X86_64.Verify.gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp),
      VG.Proof.Ed448.X86_64.Verify.gpr_ce _ _ _ (by decide : Reg.rcx ≠ .rsp), VG.Proof.Ed448.X86_64.Verify.gpr_ce _ _ _ (by decide : Reg.r8 ≠ .rsp),
      VG.Proof.Ed448.X86_64.Verify.gpr_ce _ _ _ (by decide : Reg.r9 ≠ .rsp), VG.Proof.Ed448.X86_64.Verify.rsp_ce, x.rdi, x.rsi, x.rdx, x.rcx, x.r8, x.r9, y.rdi, y.rsi,
      y.rdx, y.rcx, y.r8, y.r9, f₁.2.gpr (by decide : Reg.rsp ∉ argRegs), f₂.2.gpr (by decide : Reg.rsp ∉ argRegs),
      c₁.rsp, c₂.rsp, and_self]
  · refine ⟨fun r hr => by simp at hr, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [VG.Proof.Ed448.X86_64.Verify.w_scr hL VG.Proof.Ed448.X86_64.Verify.w_st, ⟨L.FR, by simp, w_h.trans (VG.Proof.Ed448.X86_64.Verify.within_base _ (by decide))⟩, VG.Proof.Ed448.X86_64.Verify.w_scr hL VG.Proof.Ed448.X86_64.Verify.w_ks]

/-! ## The hash -/

/-- Where each piece absorbed is. -/
theorem hdrSide {L : VG.Proof.Ed448.X86_64.Verify.Lay} (hL : L.Ok) : 0 < 136 ∧ 10 < 2 ^ 64 ∧
    (∃ R ∈ L.rd ++ L.FR :: L.wr, VG.Proof.Ed448.X86_64.Verify.Within ⟨L.SP, 10⟩ R) ∧
    Region.Disjoint ⟨L.SP, 10⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨L.SP, 10⟩ ⟨L.KS, 640⟩ ∧
    Region.Disjoint ⟨L.B, 16⟩ ⟨L.SP, 10⟩ :=
  ⟨by decide, by decide, ⟨L.FR, by simp, VG.Proof.Ed448.X86_64.Verify.within_base _ (by decide)⟩,
    by have := hL.stk_x (d := 16) (n := 10) (e := 0) (k := 200) (by decide) (by decide); simpa only [VG.Proof.Ed448.X86_64.Verify.x0] using this,
    hL.stk_x (d := 16) (n := 10) (by decide) (by decide), Offset.base_disjoint _ (by decide) (by decide)⟩

theorem ctxSide {L : VG.Proof.Ed448.X86_64.Verify.Lay} (hL : L.Ok) {q : Nat} (hq : q < 136) : q < 136 ∧ L.ctxLen.toNat < 2 ^ 64 ∧
    (∃ R ∈ L.rd ++ L.FR :: L.wr, VG.Proof.Ed448.X86_64.Verify.Within ⟨L.ctx, L.ctxLen.toNat⟩ R) ∧
    Region.Disjoint ⟨L.ctx, L.ctxLen.toNat⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨L.ctx, L.ctxLen.toNat⟩ ⟨L.KS, 640⟩ ∧
    Region.Disjoint ⟨L.B, 16⟩ ⟨L.ctx, L.ctxLen.toNat⟩ :=
  ⟨hq, L.ctxLen.isLt, ⟨L.CTX, List.mem_append_left _ hL.inCtx, VG.Proof.Ed448.X86_64.Verify.within_self _⟩,
    by have := hL.x_r hL.xCtx (e := 0) (k := 200) (by decide); simpa only [VG.Proof.Ed448.X86_64.Verify.x0] using this.symm,
    (hL.x_r hL.xCtx (e := 256) (k := 640) (by decide)).symm, VG.Proof.Ed448.X86_64.Verify.k_r hL hL.kCtx⟩

theorem sigSide {L : VG.Proof.Ed448.X86_64.Verify.Lay} (hL : L.Ok) {q : Nat} (hq : q < 136) : q < 136 ∧ 57 < 2 ^ 64 ∧
    (∃ R ∈ L.rd ++ L.FR :: L.wr, VG.Proof.Ed448.X86_64.Verify.Within ⟨L.sig, 57⟩ R) ∧
    Region.Disjoint ⟨L.sig, 57⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨L.sig, 57⟩ ⟨L.KS, 640⟩ ∧
    Region.Disjoint ⟨L.B, 16⟩ ⟨L.sig, 57⟩ :=
  have xR := hL.xSig.sub_right VG.Proof.Ed448.X86_64.Verify.r57_sub
  ⟨hq, by decide, ⟨L.SIG, List.mem_append_left _ hL.inSig, VG.Proof.Ed448.X86_64.Verify.within_base _ (by decide)⟩,
    by have := hL.x_r xR (e := 0) (k := 200) (by decide); simpa only [VG.Proof.Ed448.X86_64.Verify.x0] using this.symm,
    (hL.x_r xR (e := 256) (k := 640) (by decide)).symm, VG.Proof.Ed448.X86_64.Verify.k_r hL (hL.kSig.sub_right VG.Proof.Ed448.X86_64.Verify.r57_sub)⟩

theorem pkSide {L : VG.Proof.Ed448.X86_64.Verify.Lay} (hL : L.Ok) {q : Nat} (hq : q < 136) : q < 136 ∧ 57 < 2 ^ 64 ∧
    (∃ R ∈ L.rd ++ L.FR :: L.wr, VG.Proof.Ed448.X86_64.Verify.Within ⟨L.pk, 57⟩ R) ∧
    Region.Disjoint ⟨L.pk, 57⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨L.pk, 57⟩ ⟨L.KS, 640⟩ ∧
    Region.Disjoint ⟨L.B, 16⟩ ⟨L.pk, 57⟩ :=
  ⟨hq, by decide, ⟨L.PK, List.mem_append_left _ hL.inPk, VG.Proof.Ed448.X86_64.Verify.within_self _⟩,
    by have := hL.x_r hL.xPk (e := 0) (k := 200) (by decide); simpa only [VG.Proof.Ed448.X86_64.Verify.x0] using this.symm,
    (hL.x_r hL.xPk (e := 256) (k := 640) (by decide)).symm, VG.Proof.Ed448.X86_64.Verify.k_r hL hL.kPk⟩

theorem msgSide {L : VG.Proof.Ed448.X86_64.Verify.Lay} (hL : L.Ok) {q : Nat} (hq : q < 136) : q < 136 ∧ L.len.toNat < 2 ^ 64 ∧
    (∃ R ∈ L.rd ++ L.FR :: L.wr, VG.Proof.Ed448.X86_64.Verify.Within ⟨L.msg, L.len.toNat⟩ R) ∧
    Region.Disjoint ⟨L.msg, L.len.toNat⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨L.msg, L.len.toNat⟩ ⟨L.KS, 640⟩ ∧
    Region.Disjoint ⟨L.B, 16⟩ ⟨L.msg, L.len.toNat⟩ :=
  ⟨hq, L.len.isLt, ⟨L.MSG, List.mem_append_left _ hL.inMsg, VG.Proof.Ed448.X86_64.Verify.within_self _⟩,
    by have := hL.x_r hL.xMsg (e := 0) (k := 200) (by decide); simpa only [VG.Proof.Ed448.X86_64.Verify.x0] using this.symm,
    (hL.x_r hL.xMsg (e := 256) (k := 640) (by decide)).symm, VG.Proof.Ed448.X86_64.Verify.k_r hL hL.kMsg⟩

/-- The positions after the header, the context, `R`, `A` and the message. -/
abbrev qH (_ : VG.Proof.Ed448.X86_64.Verify.Lay) : Nat := (0 + 10) % 136
abbrev qC (L : VG.Proof.Ed448.X86_64.Verify.Lay) : Nat := (VG.Proof.Ed448.X86_64.Verify.qH L + L.ctxLen.toNat) % 136
abbrev qR (L : VG.Proof.Ed448.X86_64.Verify.Lay) : Nat := (VG.Proof.Ed448.X86_64.Verify.qC L + 57) % 136
abbrev qA (L : VG.Proof.Ed448.X86_64.Verify.Lay) : Nat := (VG.Proof.Ed448.X86_64.Verify.qR L + 57) % 136
abbrev qM (L : VG.Proof.Ed448.X86_64.Verify.Lay) : Nat := (VG.Proof.Ed448.X86_64.Verify.qA L + L.len.toNat) % 136

theorem slotLen {L : VG.Proof.Ed448.X86_64.Verify.Lay} {g mx m} {t : State} (hc : VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m t) {f : Nat} {x : BitVec 64}
    (h : t.mem.readW (L.SP + BitVec.ofNat 64 f) 64 = x) : (Arg.slot f).val t = BitVec.ofNat 64 x.toNat := by
  rw [hc.slot, h, VG.Proof.Ed448.X86_64.Verify.ofNat_toNat_self]

theorem hash_tr {Φ : VG.Proof.Ed448.X86_64.Verify.Lay → Mem → State → Prop} : RelCT isa (VG.Proof.Ed448.X86_64.Verify.Two I Φ) hash fun _ _ => True := by
  have z := VG.Proof.Ed448.X86_64.Verify.two_wp (I := I) (Φ := Φ) (Ψ := fun _ _ _ => True) VG.Proof.Ed448.X86_64.Verify.zeroSt_tr
    fun L g mx m₀ t hL hc _ => WP.mono (VG.Proof.Ed448.X86_64.Verify.zeroSt_ok hL hc) fun t' ⟨hc', _⟩ => ⟨hc', trivial⟩
  have a1 := VG.Proof.Ed448.X86_64.Verify.kabs_two (I := I) (Φ := fun _ _ _ => True) (src := .sp fHdr) (len := .imm 10) (pos := .imm 0)
    (by decide) (fun L => L.SP) (fun _ => 10) (fun _ => 0)
    (fun L g mx m t _ hc _ => ⟨by rw [hc.sp]; exact VG.Proof.Ed448.X86_64.Verify.x0 _, rfl, rfl⟩) fun L hL => VG.Proof.Ed448.X86_64.Verify.hdrSide hL
  have a2 := VG.Proof.Ed448.X86_64.Verify.kabs_two (I := I) (Φ := VG.Proof.Ed448.X86_64.Verify.Pos VG.Proof.Ed448.X86_64.Verify.qH) (src := .slot fCtx) (len := .slot fCtxLen) (pos := .ret)
    (by decide) (fun L => L.ctx) (fun L => L.ctxLen.toNat) VG.Proof.Ed448.X86_64.Verify.qH
    (fun L g mx m t _ hc hφ => ⟨by rw [hc.slot]; exact hc.pCtx, VG.Proof.Ed448.X86_64.Verify.slotLen hc hc.pCtxLen, VG.Proof.Ed448.X86_64.Verify.ofNat_toNat_eq hφ⟩)
    fun L hL => VG.Proof.Ed448.X86_64.Verify.ctxSide hL (show (0 + 10) % 136 < 136 by decide)
  have a3 := VG.Proof.Ed448.X86_64.Verify.kabs_two (I := I) (Φ := VG.Proof.Ed448.X86_64.Verify.Pos VG.Proof.Ed448.X86_64.Verify.qC) (src := .slot fSig) (len := .imm 57) (pos := .ret)
    (by decide) (fun L => L.sig) (fun _ => 57) VG.Proof.Ed448.X86_64.Verify.qC
    (fun L g mx m t _ hc hφ => ⟨by rw [hc.slot]; exact hc.pSig, rfl, VG.Proof.Ed448.X86_64.Verify.ofNat_toNat_eq hφ⟩)
    fun L hL => VG.Proof.Ed448.X86_64.Verify.sigSide hL (Nat.mod_lt _ (by decide))
  have a4 := VG.Proof.Ed448.X86_64.Verify.kabs_two (I := I) (Φ := VG.Proof.Ed448.X86_64.Verify.Pos VG.Proof.Ed448.X86_64.Verify.qR) (src := .slot fPk) (len := .imm 57) (pos := .ret)
    (by decide) (fun L => L.pk) (fun _ => 57) VG.Proof.Ed448.X86_64.Verify.qR
    (fun L g mx m t _ hc hφ => ⟨by rw [hc.slot]; exact hc.pPk, rfl, VG.Proof.Ed448.X86_64.Verify.ofNat_toNat_eq hφ⟩)
    fun L hL => VG.Proof.Ed448.X86_64.Verify.pkSide hL (Nat.mod_lt _ (by decide))
  have a5 := VG.Proof.Ed448.X86_64.Verify.kabs_two (I := I) (Φ := VG.Proof.Ed448.X86_64.Verify.Pos VG.Proof.Ed448.X86_64.Verify.qA) (src := .slot fMsg) (len := .slot fLen) (pos := .ret)
    (by decide) (fun L => L.msg) (fun L => L.len.toNat) VG.Proof.Ed448.X86_64.Verify.qA
    (fun L g mx m t _ hc hφ => ⟨by rw [hc.slot]; exact hc.pMsg, VG.Proof.Ed448.X86_64.Verify.slotLen hc hc.pLen, VG.Proof.Ed448.X86_64.Verify.ofNat_toNat_eq hφ⟩)
    fun L hL => VG.Proof.Ed448.X86_64.Verify.msgSide hL (Nat.mod_lt _ (by decide))
  have pd := VG.Proof.Ed448.X86_64.Verify.two_wp (I := I) (Φ := VG.Proof.Ed448.X86_64.Verify.Pos VG.Proof.Ed448.X86_64.Verify.qM) (Ψ := fun _ _ _ => True)
    (VG.Proof.Ed448.X86_64.Verify.kpad_tr (pos := .ret) (by decide) VG.Proof.Ed448.X86_64.Verify.qM (fun _ _ _ _ _ _ _ hφ => VG.Proof.Ed448.X86_64.Verify.ofNat_toNat_eq hφ)
      fun _ _ => Nat.mod_lt _ (by decide))
    fun L g mx m₀ t hL hc hφ => WP.mono (VG.Proof.Ed448.X86_64.Verify.kpad_ok hL hc (pos := .ret) (by decide) (VG.Proof.Ed448.X86_64.Verify.ofNat_toNat_eq hφ)
      (Nat.mod_lt _ (by decide))) fun t' ⟨hc', _⟩ => ⟨hc', trivial⟩
  exact RelCT.seq z (a1.seq (a2.seq (a3.seq (a4.seq (a5.seq (pd.seq VG.Proof.Ed448.X86_64.Verify.ksqz_tr))))))

end

end VG.Proof.Ed448.X86_64.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86_64.Verify.Calls`. -/
section

/-!
# Ed448 verification on x86-64: the challenge and the equation

Between the frame's push and pop (`Ctx`): the call of
`vg_ed448_scalar_reduce`, which leaves the hash in the frame reduced modulo
`L` at `k` (`reduce_ok`), and that of `vg_ed448_verify_equation` on the
public key, the signature and `k`, which leaves its result in `rax`
(`equation_ok`), for any proof that it meets its contract (`EqOk`): only the
whole function's `Verified` imports that proof, and the group theory it
imports.
-/

namespace VG.Proof.Ed448.X86_64.Verify

open VG VG.X86_64 VG.Impl.Ed448.X86_64.Verify
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Spec.Sha3 (bytesAt)

theorem reduce_nosp : NoSp Impl.Ed448.X86_64.scalarReduce := by
  have : ((instrs Impl.Ed448.X86_64.scalarReduce).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  intro i hi; simpa using List.all_eq_true.mp this i hi

theorem reduce_depth : Impl.Ed448.X86_64.scalarReduce.depth ≤ 1 := by lit_decide

theorem equation_nosp : NoSp Impl.Ed448.X86_64.verifyEquation := by
  have : ((instrs Impl.Ed448.X86_64.verifyEquation).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  intro i hi; simpa using List.all_eq_true.mp this i hi

theorem equation_depth : Impl.Ed448.X86_64.verifyEquation.depth ≤ 1 := by lit_decide

/-- `vg_ed448_verify_equation` meets the contract its proof is written against, and the ABI. -/
abbrev EqOk : Prop := ∀ s, Proof.Ed448.X86_64.verifyEquationLocal.pre s →
  ∃ t s', Exec isa Impl.Ed448.X86_64.verifyEquation s t s' ∧ abiPreserved s s' ∧
    Proof.Ed448.X86_64.verifyEquationLocal.post s s'

/-- `vg_ed448_verify_equation` is constant time for that contract. -/
abbrev EqCT : Prop := ConstantTime isa Proof.Ed448.X86_64.verifyEquationLocal.pre
  Proof.Ed448.X86_64.verifyEquationLocal.pub Impl.Ed448.X86_64.verifyEquation

section
variable {L : VG.Proof.Ed448.X86_64.Verify.Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

/-- The return address of a call from the frame, apart from `scratch`. -/
theorem ret_x (hL : L.Ok) : Region.Disjoint ⟨L.B + BitVec.ofNat 64 8, 8⟩ L.SCR := by
  have := hL.stk_x (d := 8) (n := 8) (e := 0) (k := 8192) (by omega) (by omega)
  simpa only [VG.Proof.Ed448.X86_64.Verify.x0] using this

/-- `k`, apart from `scratch`. -/
theorem k_x' (hL : L.Ok) : Region.Disjoint ⟨L.K, 57⟩ L.SCR := by
  have := hL.stk_x (d := 152) (n := 57) (e := 0) (k := 8192) (by omega) (by omega)
  rw [VG.Proof.Ed448.X86_64.Verify.K_eq]; simpa only [VG.Proof.Ed448.X86_64.Verify.x0] using this

theorem ret_k : Region.Disjoint ⟨L.B + BitVec.ofNat 64 8, 8⟩ ⟨L.K, 57⟩ := by
  rw [VG.Proof.Ed448.X86_64.Verify.K_eq]; exact Offset.disjoint _ (by omega) (by omega) (by omega)

theorem ret_h : Region.Disjoint ⟨L.B + BitVec.ofNat 64 8, 8⟩ ⟨L.H, 114⟩ := by
  rw [VG.Proof.Ed448.X86_64.Verify.H_eq]; exact Offset.disjoint _ (by omega) (by omega) (by omega)

theorem ret_r (hL : L.Ok) {r : Region} (hr : L.STK.Disjoint r) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 8, 8⟩ r :=
  hL.stk_r hr (by omega)

theorem sp_ce {t : State} (hc : VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t) (rd wr : List Region) :
    (t.callEntry.withRegions rd wr).gpr .rsp = L.B + BitVec.ofNat 64 8 := by
  rw [VG.Proof.Ed448.X86_64.Verify.rsp_ce, hc.rsp, VG.Proof.Ed448.X86_64.Verify.sp_sub8]

/-! ## `k` -/

/-- The arguments of `vg_ed448_scalar_reduce`. -/
abbrev redArgs : List Arg := [.sp fK, .sp fH, .slot fScr]

theorem reduce_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t) :
    WP isa (callA "vg_ed448_scalar_reduce" Impl.Ed448.X86_64.scalarReduce VG.Proof.Ed448.X86_64.Verify.redArgs) t fun t' =>
      VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t' ∧ Spec.Ed448.bytesAt t'.mem L.K 57 = Spec.Ed448.scalarReduce (bytesAt t.mem L.H 114) := by
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86_64.Verify.setArgs_ok VG.Proof.Ed448.X86_64.Verify.redArgs (by decide) t hc.frOk) fun t1 ⟨⟨hA, hm, hx⟩, k⟩ => ?_)
  have hc1 : VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t1 := hc.regs k.2.1 k.2.2 hm hx fun r hr => k.gpr (VG.Proof.Ed448.X86_64.Verify.argRegs_cs r hr)
  obtain ⟨e1, e2, e3⟩ := VG.Proof.Ed448.X86_64.Verify.argsIn3 hA
  rw [hc.sp] at e1 e2
  rw [hc.slot, hc.pScr] at e3
  change t1.gpr .rdi = L.K at e1
  change t1.gpr .rsi = L.H at e2
  have g1 := (VG.Proof.Ed448.X86_64.Verify.gpr_ce t1 [⟨L.H, 114⟩] [⟨L.K, 57⟩, L.SCR] (by decide : Reg.rdi ≠ .rsp)).trans e1
  have g2 := (VG.Proof.Ed448.X86_64.Verify.gpr_ce t1 [⟨L.H, 114⟩] [⟨L.K, 57⟩, L.SCR] (by decide : Reg.rsi ≠ .rsp)).trans e2
  have g3 := (VG.Proof.Ed448.X86_64.Verify.gpr_ce t1 [⟨L.H, 114⟩] [⟨L.K, 57⟩, L.SCR] (by decide : Reg.rdx ≠ .rsp)).trans e3
  have hpre : Proof.Ed448.X86_64.scalarReduceLocal.pre
      (t1.callEntry.withRegions [⟨L.H, 114⟩] [⟨L.K, 57⟩, L.SCR]) := by
    simp only [Proof.Ed448.X86_64.scalarReduceLocal, g1, g2, g3, VG.Proof.Ed448.X86_64.Verify.sp_ce hc1, State.withRegions_rd,
      State.withRegions_wr]
    refine ⟨trivial, trivial, ?_, VG.Proof.Ed448.X86_64.Verify.ret_k, VG.Proof.Ed448.X86_64.Verify.ret_x hL, VG.Proof.Ed448.X86_64.Verify.k_x' hL, hL.nScr⟩
    have := hL.stk_x (d := 32) (n := 114) (e := 0) (k := 8192) (by omega) (by omega)
    rw [VG.Proof.Ed448.X86_64.Verify.H_eq]; simpa only [VG.Proof.Ed448.X86_64.Verify.x0] using this
  refine VG.Proof.Ed448.X86_64.Verify.call_ok hL Proof.Ed448.X86_64.scalarReduce_ok VG.Proof.Ed448.X86_64.Verify.reduce_nosp VG.Proof.Ed448.X86_64.Verify.reduce_depth hc1 hpre
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨L.FR, by simp, VG.Proof.Ed448.X86_64.Verify.within_off _ (by omega)⟩)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [.inr (VG.Proof.Ed448.X86_64.Verify.within_off _ (by omega)), .inl (VG.Proof.Ed448.X86_64.Verify.within_self _)])
    fun s' hc' _ _ ⟨s₂, hm₂, _, hpost⟩ => ⟨hc', ?_⟩
  simp only [Proof.Ed448.X86_64.scalarReduceLocal, g1, g2, State.withRegions_mem, hm₂] at hpost
  rw [hpost]
  refine congrArg _ ?_
  change bytesAt t1.callEntry.mem L.H 114 = bytesAt t.mem L.H 114
  rw [hc1.ce_bytesAt VG.Proof.Ed448.X86_64.Verify.ret_h (by decide), hm]

/-! ## The equation -/

/-- The arguments of `vg_ed448_verify_equation`. -/
abbrev eqArgs : List Arg := [.slot fPk, .slot fSig, .sp fK, .slot fScr]

theorem equation_ok (hv : VG.Proof.Ed448.X86_64.Verify.EqOk) (hL : L.Ok) {t : State} (hc : VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t) :
    WP isa (callA "vg_ed448_verify_equation" Impl.Ed448.X86_64.verifyEquation VG.Proof.Ed448.X86_64.Verify.eqArgs) t fun t' =>
      VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t' ∧ t'.gpr .rax = if Spec.Ed448.verifyEquation (bytesAt m₀ L.pk 57) (bytesAt m₀ L.sig 114)
        (bytesAt t.mem L.K 57) then 1 else 0 := by
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86_64.Verify.setArgs_ok VG.Proof.Ed448.X86_64.Verify.eqArgs (by decide) t hc.frOk) fun t1 ⟨⟨hA, hm, hx⟩, k⟩ => ?_)
  have hc1 : VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t1 := hc.regs k.2.1 k.2.2 hm hx fun r hr => k.gpr (VG.Proof.Ed448.X86_64.Verify.argRegs_cs r hr)
  obtain ⟨e1, e2, e3, e4⟩ := VG.Proof.Ed448.X86_64.Verify.argsIn4 hA
  rw [hc.slot, hc.pPk] at e1
  rw [hc.slot, hc.pSig] at e2
  rw [hc.sp] at e3
  rw [hc.slot, hc.pScr] at e4
  change t1.gpr .rdx = L.K at e3
  have g1 := (VG.Proof.Ed448.X86_64.Verify.gpr_ce t1 [L.PK, L.SIG, ⟨L.K, 57⟩] [L.SCR] (by decide : Reg.rdi ≠ .rsp)).trans e1
  have g2 := (VG.Proof.Ed448.X86_64.Verify.gpr_ce t1 [L.PK, L.SIG, ⟨L.K, 57⟩] [L.SCR] (by decide : Reg.rsi ≠ .rsp)).trans e2
  have g3 := (VG.Proof.Ed448.X86_64.Verify.gpr_ce t1 [L.PK, L.SIG, ⟨L.K, 57⟩] [L.SCR] (by decide : Reg.rdx ≠ .rsp)).trans e3
  have g4 := (VG.Proof.Ed448.X86_64.Verify.gpr_ce t1 [L.PK, L.SIG, ⟨L.K, 57⟩] [L.SCR] (by decide : Reg.rcx ≠ .rsp)).trans e4
  have hpre : Proof.Ed448.X86_64.verifyEquationLocal.pre
      (t1.callEntry.withRegions [L.PK, L.SIG, ⟨L.K, 57⟩] [L.SCR]) := by
    simp only [Proof.Ed448.X86_64.verifyEquationLocal, g1, g2, g3, g4, VG.Proof.Ed448.X86_64.Verify.sp_ce hc1, State.withRegions_rd,
      State.withRegions_wr]
    exact ⟨trivial, trivial, hL.xPk.symm, hL.xSig.symm, VG.Proof.Ed448.X86_64.Verify.k_x' hL, VG.Proof.Ed448.X86_64.Verify.ret_x hL, hL.nScr⟩
  refine VG.Proof.Ed448.X86_64.Verify.call_ok hL hv VG.Proof.Ed448.X86_64.Verify.equation_nosp VG.Proof.Ed448.X86_64.Verify.equation_depth hc1 hpre
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨L.PK, List.mem_append_left _ hL.inPk, VG.Proof.Ed448.X86_64.Verify.within_self _⟩
      · exact ⟨L.SIG, List.mem_append_left _ hL.inSig, VG.Proof.Ed448.X86_64.Verify.within_self _⟩
      · exact ⟨L.FR, by simp, VG.Proof.Ed448.X86_64.Verify.within_off _ (by omega)⟩)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact .inl (VG.Proof.Ed448.X86_64.Verify.within_self _))
    fun s' hc' _ _ ⟨s₂, _, hg₂, hpost⟩ => ⟨hc', ?_⟩
  simp only [Proof.Ed448.X86_64.verifyEquationLocal, g1, g2, g3, State.withRegions_mem] at hpost
  rw [← hg₂ _ (by decide), hpost]
  have ep : Spec.Ed448.bytesAt t1.callEntry.mem L.pk 57 = bytesAt m₀ L.pk 57 := by
    change bytesAt t1.callEntry.mem L.pk 57 = _
    rw [hc1.ce_bytesAt (VG.Proof.Ed448.X86_64.Verify.ret_r hL hL.kPk) (by decide), hc1.bytesAt_eq hL.xPk hL.kPk (by decide)]
  have es : Spec.Ed448.bytesAt t1.callEntry.mem L.sig 114 = bytesAt m₀ L.sig 114 := by
    change bytesAt t1.callEntry.mem L.sig 114 = _
    rw [hc1.ce_bytesAt (VG.Proof.Ed448.X86_64.Verify.ret_r hL hL.kSig) (by decide), hc1.bytesAt_eq hL.xSig hL.kSig (by decide)]
  have ek : Spec.Ed448.bytesAt t1.callEntry.mem L.K 57 = bytesAt t.mem L.K 57 := by
    change bytesAt t1.callEntry.mem L.K 57 = _
    rw [hc1.ce_bytesAt VG.Proof.Ed448.X86_64.Verify.ret_k (by decide), hm]
  rw [ep, es, ek]

end

end VG.Proof.Ed448.X86_64.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86_64.Verify.Pre`. -/
section

/-!
# Ed448 verification on x86-64: the precondition and the layout

The precondition of `verifyContract X86_64.abi 272`, spelled out (`VPre`),
and the layout of a run from a state satisfying it (`vlay`), which is `Ok`
if the context is shorter than 256 bytes (`vlay_ok`).
-/

namespace VG.Proof.Ed448.X86_64.Verify

open VG VG.X86_64

section
variable (s : State)

abbrev vPk : Region := ⟨s.gpr .rdi, 57⟩
abbrev vCtx : Region := ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩
abbrev vMsg : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
abbrev vSig : Region := ⟨s.gpr .r9, 114⟩
abbrev vArgs : Region := ⟨stackArgAddr s 0, 8⟩
abbrev vScr : Region := ⟨stackArg s 0, 8192⟩
abbrev vRet : Region := ⟨s.gpr .rsp, 8⟩
abbrev vStk : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 272, 272⟩

end

/-- The precondition of `verifyContract X86_64.abi 272`. -/
structure VPre (s : State) : Prop where
  sp : 272 ≤ (s.gpr .rsp).toNat
  sp2 : (s.gpr .rsp).toNat + 16 ≤ 2 ^ 64
  rd : s.rd = [VG.Proof.Ed448.X86_64.Verify.vPk s, VG.Proof.Ed448.X86_64.Verify.vCtx s, VG.Proof.Ed448.X86_64.Verify.vMsg s, VG.Proof.Ed448.X86_64.Verify.vSig s, VG.Proof.Ed448.X86_64.Verify.vArgs s]
  wr : s.wr = [VG.Proof.Ed448.X86_64.Verify.vScr s]
  pkScr : (VG.Proof.Ed448.X86_64.Verify.vPk s).Disjoint (VG.Proof.Ed448.X86_64.Verify.vScr s)
  ctxScr : (VG.Proof.Ed448.X86_64.Verify.vCtx s).Disjoint (VG.Proof.Ed448.X86_64.Verify.vScr s)
  msgScr : (VG.Proof.Ed448.X86_64.Verify.vMsg s).Disjoint (VG.Proof.Ed448.X86_64.Verify.vScr s)
  sigScr : (VG.Proof.Ed448.X86_64.Verify.vSig s).Disjoint (VG.Proof.Ed448.X86_64.Verify.vScr s)
  scrArgs : (VG.Proof.Ed448.X86_64.Verify.vScr s).Disjoint (VG.Proof.Ed448.X86_64.Verify.vArgs s)
  retPk : (VG.Proof.Ed448.X86_64.Verify.vRet s).Disjoint (VG.Proof.Ed448.X86_64.Verify.vPk s)
  retCtx : (VG.Proof.Ed448.X86_64.Verify.vRet s).Disjoint (VG.Proof.Ed448.X86_64.Verify.vCtx s)
  retMsg : (VG.Proof.Ed448.X86_64.Verify.vRet s).Disjoint (VG.Proof.Ed448.X86_64.Verify.vMsg s)
  retSig : (VG.Proof.Ed448.X86_64.Verify.vRet s).Disjoint (VG.Proof.Ed448.X86_64.Verify.vSig s)
  retScr : (VG.Proof.Ed448.X86_64.Verify.vRet s).Disjoint (VG.Proof.Ed448.X86_64.Verify.vScr s)
  retArgs : (VG.Proof.Ed448.X86_64.Verify.vRet s).Disjoint (VG.Proof.Ed448.X86_64.Verify.vArgs s)
  stkPk : (VG.Proof.Ed448.X86_64.Verify.vStk s).Disjoint (VG.Proof.Ed448.X86_64.Verify.vPk s)
  stkCtx : (VG.Proof.Ed448.X86_64.Verify.vStk s).Disjoint (VG.Proof.Ed448.X86_64.Verify.vCtx s)
  stkMsg : (VG.Proof.Ed448.X86_64.Verify.vStk s).Disjoint (VG.Proof.Ed448.X86_64.Verify.vMsg s)
  stkSig : (VG.Proof.Ed448.X86_64.Verify.vStk s).Disjoint (VG.Proof.Ed448.X86_64.Verify.vSig s)
  stkScr : (VG.Proof.Ed448.X86_64.Verify.vStk s).Disjoint (VG.Proof.Ed448.X86_64.Verify.vScr s)
  stkArgs : (VG.Proof.Ed448.X86_64.Verify.vStk s).Disjoint (VG.Proof.Ed448.X86_64.Verify.vArgs s)
  nPk : (s.gpr .rdi).toNat + 57 ≤ 2 ^ 64
  nCtx : (s.gpr .rsi).toNat + (s.gpr .rdx).toNat ≤ 2 ^ 64
  nMsg : (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64
  nSig : (s.gpr .r9).toNat + 114 ≤ 2 ^ 64
  nScr : (stackArg s 0).toNat + 8192 ≤ 2 ^ 64

theorem vPre_of {s : State} (h : (Spec.Ed448.verifyContract X86_64.abi 272).pre s) : VG.Proof.Ed448.X86_64.Verify.VPre s := by
  sig_pre [Spec.Ed448.verifyContract, Spec.Ed448.verifySig, Spec.Ed448.scratchWords, X86_64.abi, X86_64.argRegs,
    List.range, List.range.loop] at h
  obtain ⟨sp, sp2, rd, wr, pkScr, ctxScr, msgScr, sigScr, scrArgs, retPk, retCtx, retMsg, retSig, retScr,
    retArgs, stkPk, stkCtx, stkMsg, stkSig, stkScr, stkArgs, nPk, nCtx, nMsg, nSig, nScr⟩ := h
  exact ⟨sp, sp2, rd, wr, pkScr, ctxScr, msgScr, sigScr, scrArgs, retPk, retCtx, retMsg, retSig, retScr,
    retArgs, stkPk, stkCtx, stkMsg, stkSig, stkScr, stkArgs, nPk, nCtx, nMsg, nSig, nScr⟩

/-- The layout of a run of `verify` from `s`. -/
def vlay (s : State) : VG.Proof.Ed448.X86_64.Verify.Lay where
  B := s.gpr .rsp - BitVec.ofNat 64 272
  pk := s.gpr .rdi
  ctx := s.gpr .rsi
  ctxLen := s.gpr .rdx
  msg := s.gpr .rcx
  len := s.gpr .r8
  sig := s.gpr .r9
  scr := stackArg s 0
  rd := s.rd
  wr := s.wr

theorem vlay_B (s : State) : (VG.Proof.Ed448.X86_64.Verify.vlay s).B + BitVec.ofNat 64 272 = s.gpr .rsp := BitVec.sub_add_cancel _ _

theorem vlay_ok {s : State} (h : VG.Proof.Ed448.X86_64.Verify.VPre s) (h8 : (s.gpr .rdx).toNat < 256) : (VG.Proof.Ed448.X86_64.Verify.vlay s).Ok := by
  have eR : (VG.Proof.Ed448.X86_64.Verify.vlay s).RET = VG.Proof.Ed448.X86_64.Verify.vRet s := by
    show (⟨(VG.Proof.Ed448.X86_64.Verify.vlay s).B + BitVec.ofNat 64 272, 8⟩ : Region) = _
    rw [VG.Proof.Ed448.X86_64.Verify.vlay_B]
  refine ⟨h8, ?_, h.wr, by simp [VG.Proof.Ed448.X86_64.Verify.vlay, h.rd], by simp [VG.Proof.Ed448.X86_64.Verify.vlay, h.rd], by simp [VG.Proof.Ed448.X86_64.Verify.vlay, h.rd], by simp [VG.Proof.Ed448.X86_64.Verify.vlay, h.rd],
    h.pkScr.symm, h.sigScr.symm, h.msgScr.symm, h.ctxScr.symm, h.stkScr, h.stkPk, h.stkSig, h.stkMsg, h.stkCtx,
    by rw [eR]; exact h.retScr, h.nPk, h.nSig, h.nMsg, h.nCtx, h.nScr⟩
  have := h.sp; have := h.sp2
  simp only [VG.Proof.Ed448.X86_64.Verify.vlay, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

end VG.Proof.Ed448.X86_64.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86_64.Verify.Correct`. -/
section

/-!
# Ed448 verification on x86-64: correctness

The frame's body leaves the result of the equation on the hash of the
signature's `R`, the public key and the message, with the context's `dom4`
prefix, in `rax` (`body_ok`); the frame's push gives `Ctx` (`entry_ctx`).
From a state satisfying `verifyContract X86_64.abi 272`, `verify` returns 0
if the context is longer than 255 bytes and otherwise that result, which is
`Spec.Ed448.verify`'s (`verify_wp`), for any proof of `vg_ed448_verify_equation`
(`EqOk`).
-/

namespace VG.Proof.Ed448.X86_64.Verify

open VG VG.X86_64 VG.Impl.Ed448.X86_64.Verify
open VG.Proof.MlKem.X86_64 (Keep WP.keep)
open VG.Spec.Sha3 (bytesAt)

/-! ## The frame's body -/

section
variable {L : VG.Proof.Ed448.X86_64.Verify.Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

/-- `R`, the first half of the signature. -/
theorem take_bytesAt (m : Mem) (p : Addr) : (bytesAt m p 114).take 57 = bytesAt m p 57 := by
  have a := Proof.X25519.bytesAt_add m p 57 57
  have l := Proof.X25519.length_bytesAt m p 57
  change (Spec.X25519.bytesAt m p (57 + 57)).take 57 = Spec.X25519.bytesAt m p 57
  rw [a, List.take_left' l]

theorem ed_bytesAt : Spec.Ed448.bytesAt = bytesAt := rfl

/-- The challenge of the signature in `m₀`. -/
abbrev chal (L : VG.Proof.Ed448.X86_64.Verify.Lay) (m₀ : Mem) : List Byte :=
  Spec.Ed448.scalarReduce (Spec.Ed448.hash (bytesAt m₀ L.ctx L.ctxLen.toNat)
    (bytesAt m₀ L.sig 57 ++ bytesAt m₀ L.pk 57 ++ bytesAt m₀ L.msg L.len.toNat))

theorem body_ok (hv : VG.Proof.Ed448.X86_64.Verify.EqOk) (hL : L.Ok) {t : State} (hc : VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t) :
    WP isa body t fun t' => VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t' ∧
      t'.gpr .rax = if Spec.Ed448.verifyEquation (bytesAt m₀ L.pk 57) (bytesAt m₀ L.sig 114) (VG.Proof.Ed448.X86_64.Verify.chal L m₀)
        then 1 else 0 := by
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86_64.Verify.hdr_ok hL hc) fun t1 ⟨hc1, hh⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86_64.Verify.hash_ok hL hc1) fun t2 ⟨hc2, hH⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86_64.Verify.reduce_ok hL hc2) fun t3 ⟨hc3, hK⟩ => ?_)
  refine WP.mono (VG.Proof.Ed448.X86_64.Verify.equation_ok hv hL hc3) fun t4 ⟨hc4, hr⟩ => ⟨hc4, ?_⟩
  have ek : bytesAt t3.mem L.K 57 = VG.Proof.Ed448.X86_64.Verify.chal L m₀ := by
    change Spec.Ed448.bytesAt t3.mem L.K 57 = _
    rw [hK, hH, hh]
    refine congrArg Spec.Ed448.scalarReduce ?_
    simp only [Spec.Ed448.hash, Spec.Ed448.dom4, VG.Proof.Ed448.X86_64.Verify.bytesAt_length, List.append_assoc, List.cons_append,
      List.nil_append]
  rw [hr, ek]

end

/-! ## The frame -/

/-- The registers pushed, at their slots. -/
theorem push_slot (B : Addr) (j : Nat) (hj : j < 32) :
    B + BitVec.ofNat 64 272 - BitVec.ofNat 64 (8 * (j + 1)) =
      B + BitVec.ofNat 64 16 + BitVec.ofNat 64 (248 - 8 * j) := by
  rw [VG.Proof.Ed448.X86_64.Verify.add_add, Offset.sub_ofNat_eq _ (a := 8 * (j + 1)) (b := 272) (by omega), BitVec.add_sub_cancel]
  congr 2; omega

theorem push_base (B : Addr) : B + BitVec.ofNat 64 272 - BitVec.ofNat 64 (8 * 32) = B + BitVec.ofNat 64 16 := by
  have := VG.Proof.Ed448.X86_64.Verify.push_slot B 31 (by omega); simpa using this

theorem regs_length : regs.length = 32 := rfl

/-- After the push of the registers holding `scratch`, `sig`, `len`, `msg`,
`ctx_len`, `ctx`, `pk` and 0: `Ctx`. -/
theorem entry_ctx {L : VG.Proof.Ed448.X86_64.Verify.Lay} (hL : L.Ok) {s : State} (hsp : s.gpr .rsp = L.B + BitVec.ofNat 64 272)
    (hrd : s.rd = L.rd) (hwr : s.wr = L.wr) (h11 : s.gpr .r11 = L.scr) (h9 : s.gpr .r9 = L.sig)
    (h8 : s.gpr .r8 = L.len) (hcx : s.gpr .rcx = L.msg) (hdx : s.gpr .rdx = L.ctxLen)
    (hsi : s.gpr .rsi = L.ctx) (hdi : s.gpr .rdi = L.pk) :
    VG.Proof.Ed448.X86_64.Verify.Ctx L s.gpr s.mxcsr s.mem (pushed VG.Impl.Ed448.X86_64.Verify.regs s) := by
  have hn : 8 * regs.length ≤ (s.gpr .rsp).toNat := by
    rw [hsp, VG.Proof.Ed448.X86_64.Verify.regs_length, BitVec.toNat_add, BitVec.toNat_ofNat]
    have := hL.nB
    rw [Nat.mod_eq_of_lt (a := 272) (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  obtain ⟨hf, hw⟩ := pushRegs_mem s VG.Impl.Ed448.X86_64.Verify.regs (by decide) hn
  have slot : ∀ j (hj : j < 32), (pushed VG.Impl.Ed448.X86_64.Verify.regs s).mem.readW (L.SP + BitVec.ofNat 64 (248 - 8 * j)) 64 =
      s.gpr (VG.Impl.Ed448.X86_64.Verify.regs[j]'(by rw [VG.Proof.Ed448.X86_64.Verify.regs_length]; omega)) := fun j hj => by
    rw [← hw j (by rw [VG.Proof.Ed448.X86_64.Verify.regs_length]; omega), hsp, VG.Proof.Ed448.X86_64.Verify.push_slot _ j hj]; rfl
  have base : s.gpr .rsp - BitVec.ofNat 64 (8 * regs.length) = L.SP := by
    rw [hsp, VG.Proof.Ed448.X86_64.Verify.regs_length]; exact VG.Proof.Ed448.X86_64.Verify.push_base L.B
  refine ⟨by simp [hrd], by rw [pushed_wr, base, hwr]; rfl, by rw [pushed_rsp, base], fun r _ hr' => pushed_gpr _ _ hr',
    by simp, (slot 6 (by omega)).trans hdi, (slot 5 (by omega)).trans hsi, (slot 4 (by omega)).trans hdx,
    (slot 3 (by omega)).trans hcx, (slot 2 (by omega)).trans h8, (slot 1 (by omega)).trans h9,
    (slot 0 (by omega)).trans h11, ?_⟩
  show VG.Frame [L.SCR, L.STK] s.mem (pushRegs s VG.Impl.Ed448.X86_64.Verify.regs).mem
  refine Frame.sub hf fun r hr => ?_
  simp only [List.mem_singleton] at hr; subst hr
  refine ⟨L.STK, by simp, ?_⟩
  rw [base, VG.Proof.Ed448.X86_64.Verify.regs_length]
  exact Offset.sub_base _ (by omega)

/-! ## Before the frame -/

theorem wp_ite_t {c : isa.Cond} {th el : Prog isa} {s : State} {Q : State → Prop}
    (hc : isa.eval c s = some true) (h : WP isa th s Q) : WP isa (.ite c th el) s Q :=
  let ⟨_, _, e, q⟩ := h; ⟨_, _, .iteT hc e, q⟩

theorem wp_ite_f {c : isa.Cond} {th el : Prog isa} {s : State} {Q : State → Prop}
    (hc : isa.eval c s = some false) (h : WP isa el s Q) : WP isa (.ite c th el) s Q :=
  let ⟨_, _, e, q⟩ := h; ⟨_, _, .iteF hc e, q⟩

/-- `cmp rdx, 256`. -/
theorem cmp_ok (s : State) :
    WP isa (.block [.alu .cmp .rdx (.imm 256)]) s fun s1 => s1.gpr = s.gpr ∧ s1.mem = s.mem ∧
      s1.rd = s.rd ∧ s1.wr = s.wr ∧ s1.mxcsr = s.mxcsr ∧
      isa.eval .b s1 = some (decide ((s.gpr .rdx).toNat < 256)) := by
  xrun [show BitVec.signExtend 64 (256 : BitVec 32) = 256 by decide]
  exact ⟨rfl, rfl⟩

theorem stackArgAddr0 (s : State) : stackArgAddr s 0 = s.gpr .rsp + BitVec.ofNat 64 8 := rfl

/-- `scratch` to `r11`, 0 to `rax`. -/
theorem verifyMov_ok {s s1 : State} (h : VG.Proof.Ed448.X86_64.Verify.VPre s) (hg : s1.gpr = s.gpr) (hm : s1.mem = s.mem)
    (hrd : s1.rd = s.rd) :
    WP isa (.block [.mov .r11 (.mem (stk 8)), .mov32 .rax (.imm 0)]) s1 fun s2 =>
      (s2.gpr .r11 = stackArg s 0 ∧ s2.gpr .rax = 0 ∧ s2.mem = s.mem ∧ s2.mxcsr = s1.mxcsr) ∧
        Keep [.r11, .rax] s1 s2 := by
  have h8 : InRegions (s1.rd ++ s1.wr) (s1.gpr .rsp + BitVec.ofNat 64 8) 8 := by
    refine ⟨VG.Proof.Ed448.X86_64.Verify.vArgs s, by simp [hrd, h.rd], ?_⟩
    rw [hg, ← VG.Proof.Ed448.X86_64.Verify.stackArgAddr0]
    exact Region.contains_self _ _
  refine WP.keep _ ?_ (by decide)
  xrun [VG.Proof.Ed448.X86_64.Verify.ea_stk, h8, RegUpd.mxcsr_setReg]
  rw [hm, hg]
  exact ⟨rfl, rfl⟩

theorem sw_ite (b : Bool) :
    BitVec.setWidth 32 (if b = true then (1 : BitVec 64) else 0) = if b = true then 1 else 0 := by
  cases b <;> rfl

theorem cs_r11 : ∀ r ∈ calleeSaved, r ≠ .r11 := by decide
theorem cs_tmp : ∀ r ∈ calleeSaved, r ∉ [Reg.r11, .rax] := by decide

/-! ## The function -/

theorem verify_wp (hv : VG.Proof.Ed448.X86_64.Verify.EqOk) {s : State} (hpre : (Spec.Ed448.verifyContract X86_64.abi 272).pre s) :
    WP isa verify s fun s' => abiPreserved s s' ∧ (Spec.Ed448.verifyContract X86_64.abi 272).post s s' := by
  have h := VG.Proof.Ed448.X86_64.Verify.vPre_of hpre
  unfold verify
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86_64.Verify.cmp_ok s) fun s1 ⟨hg1, hm1, hrd1, hwr1, hx1, hc1⟩ => ?_)
  by_cases h8 : (s.gpr .rdx).toNat < 256
  · rw [decide_eq_true h8] at hc1
    refine VG.Proof.Ed448.X86_64.Verify.wp_ite_t hc1 (WP.seq (WP.mono (VG.Proof.Ed448.X86_64.Verify.verifyMov_ok h hg1 hm1 hrd1) fun s2 ⟨⟨h11, hax, hm2, hx2⟩, k2⟩ => ?_))
    have hL := VG.Proof.Ed448.X86_64.Verify.vlay_ok h h8
    have hg2 : ∀ r, r ∉ [Reg.r11, .rax] → s2.gpr r = s.gpr r := fun r hr => (k2.gpr hr).trans (by rw [hg1])
    have hsp2 : s2.gpr .rsp = (VG.Proof.Ed448.X86_64.Verify.vlay s).B + BitVec.ofNat 64 272 := by
      rw [hg2 _ (by decide), VG.Proof.Ed448.X86_64.Verify.vlay_B]
    have hn : 8 * regs.length ≤ (s2.gpr .rsp).toNat := by
      rw [hg2 _ (by decide), VG.Proof.Ed448.X86_64.Verify.regs_length]; have := h.sp; omega
    refine WP.frame (by decide) (by decide) (by decide) hn ?_
    have hc := VG.Proof.Ed448.X86_64.Verify.entry_ctx hL hsp2 (k2.2.1.trans hrd1) (k2.2.2.trans hwr1) h11 (hg2 _ (by decide))
      (hg2 _ (by decide)) (hg2 _ (by decide)) (hg2 _ (by decide)) (hg2 _ (by decide)) (hg2 _ (by decide))
    refine WP.mono (VG.Proof.Ed448.X86_64.Verify.body_ok hv hL hc) fun s' ⟨hc', hr⟩ => ⟨by rw [hc'.rsp, hc.rsp], by rw [hc'.wr, hc.wr], ?_, ?_⟩
    · -- The calling convention.
      refine ⟨fun r hr => ?_, ?_, ?_⟩
      · by_cases hr' : r = .rsp
        · subst hr'
          rw [popped_rsp, hc'.rsp, Lay.SP, VG.Proof.Ed448.X86_64.Verify.add_add, VG.Proof.Ed448.X86_64.Verify.regs_length, VG.Proof.Ed448.X86_64.Verify.vlay_B]
        · rw [popped_gpr _ _ _ hr' (VG.Proof.Ed448.X86_64.Verify.cs_r11 r hr), hc'.cs r hr hr', hg2 r (VG.Proof.Ed448.X86_64.Verify.cs_tmp r hr)]
      · have eR : VG.Proof.Ed448.X86_64.Verify.vRet s = ⟨(VG.Proof.Ed448.X86_64.Verify.vlay s).B + BitVec.ofNat 64 272, 8⟩ := by rw [VG.Proof.Ed448.X86_64.Verify.vlay_B]
        rw [popped_mem, hc'.frame.readW (r := VG.Proof.Ed448.X86_64.Verify.vRet s) (Region.contains_self _ _) (fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl
            · exact h.retScr
            · rw [eR]; exact Offset.disjoint_base _ (by omega) (by have := hL.nB; omega)) (by decide), hm2]
      · rw [popped_mxcsr, hc'.mx, hx2, hx1]
    · sig_post [Spec.Ed448.verifyContract, Spec.Ed448.verifySig, Spec.Ed448.scratchWords, X86_64.abi,
        X86_64.argRegs, List.range, List.range.loop]
      rw [hr]
      simp only [VG.Proof.Ed448.X86_64.Verify.ed_bytesAt, Spec.Ed448.verify, VG.Proof.Ed448.X86_64.Verify.bytesAt_length, VG.Proof.Ed448.X86_64.Verify.take_bytesAt, VG.Proof.Ed448.X86_64.Verify.vlay, VG.Proof.Ed448.X86_64.Verify.chal, ← hm2,
        decide_eq_true (show (s.gpr .rdx).toNat ≤ 255 by omega), Bool.true_and]
      exact VG.Proof.Ed448.X86_64.Verify.sw_ite _
  · rw [decide_eq_false h8] at hc1
    refine VG.Proof.Ed448.X86_64.Verify.wp_ite_f hc1 ?_
    xrun
    refine ⟨⟨fun r hr => ?_, by rw [RegUpd.mem_setReg, hm1], by rw [RegUpd.mxcsr_setReg, hx1]⟩, ?_⟩
    · rw [RegUpd.gpr_setReg_of_ne _ _ (fun e => by subst e; revert hr; decide), hg1]
    · sig_post [Spec.Ed448.verifyContract, Spec.Ed448.verifySig, Spec.Ed448.scratchWords, X86_64.abi,
        X86_64.argRegs, List.range, List.range.loop]
      simp only [VG.Proof.Ed448.X86_64.Verify.ed_bytesAt, Spec.Ed448.verify, VG.Proof.Ed448.X86_64.Verify.bytesAt_length,
        decide_eq_false (show ¬ (s.gpr .rdx).toNat ≤ 255 by omega), Bool.false_and]
      rfl

end VG.Proof.Ed448.X86_64.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86_64.Verify.CT`. -/
section

/-!
# Ed448 verification on x86-64: constant time

Two runs from states that satisfy the contract and agree on its public data
leak the same: the branch on `ctx_len`, the moves and the frame depend only
on the pointers and the lengths; the hashing leaks only the layout
(`hash_tr`); and the calls of `vg_ed448_scalar_reduce` and
`vg_ed448_verify_equation` leak only their pointers (`red_tr`, `eq_tr`).
The contract makes the inputs public too, but no leak depends on them.
-/

namespace VG.Proof.Ed448.X86_64.Verify

open VG VG.X86_64 VG.Impl.Ed448.X86_64.Verify
open VG.Proof.MlKem.X86_64 (Keep)

section
variable {I : VG.Proof.Ed448.X86_64.Verify.Lay → Mem → Mem → Prop}

/-! ## The calls -/

theorem red_tr {Φ : VG.Proof.Ed448.X86_64.Verify.Lay → Mem → State → Prop} :
    RelCT isa (VG.Proof.Ed448.X86_64.Verify.Two I Φ) (callA "vg_ed448_scalar_reduce" Impl.Ed448.X86_64.scalarReduce VG.Proof.Ed448.X86_64.Verify.redArgs)
      fun _ _ => True := by
  have regs : ∀ (L : VG.Proof.Ed448.X86_64.Verify.Lay) g mx m₀ (t t1 : State), VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t → VG.Proof.Ed448.X86_64.Verify.Moved VG.Proof.Ed448.X86_64.Verify.redArgs t t1 →
      t1.gpr .rdi = L.K ∧ t1.gpr .rsi = L.H ∧ t1.gpr .rdx = L.scr ∧ t1.gpr .rsp = L.SP :=
    fun L g mx m₀ t t1 hc hm => by
      obtain ⟨e1, e2, e3⟩ := VG.Proof.Ed448.X86_64.Verify.argsIn3 hm.1.1
      rw [hc.sp] at e1 e2
      rw [hc.slot, hc.pScr] at e3
      exact ⟨e1, e2, e3, (hm.2.gpr (by decide)).trans hc.rsp⟩
  refine VG.Proof.Ed448.X86_64.Verify.call_tr (by decide) Proof.Ed448.X86_64.scalarReduce_ok Proof.Ed448.X86_64.scalarReduce_ct
    (fun L => [⟨L.H, 114⟩]) (fun L => [⟨L.K, 57⟩, L.SCR])
    (fun L g mx m₀ t t1 hL hc _ hm => ?_)
    (fun L g₁ g₂ mx₁ mx₂ m₁ m₂ a b a1 b1 _ _ c₁ c₂ _ _ f₁ f₂ => ?_) fun L _ _ _ _ hL _ _ => ?_
  · obtain ⟨g1, g2, g3, g4⟩ := regs L g mx m₀ t t1 hc hm
    simp only [Proof.Ed448.X86_64.scalarReduceLocal, VG.Proof.Ed448.X86_64.Verify.gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp),
      VG.Proof.Ed448.X86_64.Verify.gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp), VG.Proof.Ed448.X86_64.Verify.gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp), VG.Proof.Ed448.X86_64.Verify.rsp_ce, g1, g2, g3, g4,
      VG.Proof.Ed448.X86_64.Verify.sp_sub8, State.withRegions_rd, State.withRegions_wr]
    refine ⟨trivial, trivial, ?_, VG.Proof.Ed448.X86_64.Verify.ret_k, VG.Proof.Ed448.X86_64.Verify.ret_x hL, VG.Proof.Ed448.X86_64.Verify.k_x' hL, hL.nScr⟩
    have := hL.stk_x (d := 32) (n := 114) (e := 0) (k := 8192) (by omega) (by omega)
    rw [VG.Proof.Ed448.X86_64.Verify.H_eq]; simpa only [VG.Proof.Ed448.X86_64.Verify.x0] using this
  · obtain ⟨x1, x2, x3, x4⟩ := regs L g₁ mx₁ m₁ a a1 c₁ f₁
    obtain ⟨y1, y2, y3, y4⟩ := regs L g₂ mx₂ m₂ b b1 c₂ f₂
    simp only [Proof.Ed448.X86_64.scalarReduceLocal, VG.Proof.Ed448.X86_64.Verify.gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp),
      VG.Proof.Ed448.X86_64.Verify.gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp), VG.Proof.Ed448.X86_64.Verify.gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp), VG.Proof.Ed448.X86_64.Verify.rsp_ce,
      x1, x2, x3, x4, y1, y2, y3, y4, and_self]
  · refine ⟨fun r hr => ?_, fun r hr => ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨L.FR, by simp, VG.Proof.Ed448.X86_64.Verify.within_off _ (by omega)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [⟨L.FR, by simp, VG.Proof.Ed448.X86_64.Verify.within_off _ (by omega)⟩, VG.Proof.Ed448.X86_64.Verify.w_scr hL (VG.Proof.Ed448.X86_64.Verify.within_self _)]

theorem eq_tr (hv : VG.Proof.Ed448.X86_64.Verify.EqOk) (hct : VG.Proof.Ed448.X86_64.Verify.EqCT) {Φ : VG.Proof.Ed448.X86_64.Verify.Lay → Mem → State → Prop} :
    RelCT isa (VG.Proof.Ed448.X86_64.Verify.Two I Φ) (callA "vg_ed448_verify_equation" Impl.Ed448.X86_64.verifyEquation VG.Proof.Ed448.X86_64.Verify.eqArgs)
      fun _ _ => True := by
  have regs : ∀ (L : VG.Proof.Ed448.X86_64.Verify.Lay) g mx m₀ (t t1 : State), VG.Proof.Ed448.X86_64.Verify.Ctx L g mx m₀ t → VG.Proof.Ed448.X86_64.Verify.Moved VG.Proof.Ed448.X86_64.Verify.eqArgs t t1 →
      t1.gpr .rdi = L.pk ∧ t1.gpr .rsi = L.sig ∧ t1.gpr .rdx = L.K ∧ t1.gpr .rcx = L.scr ∧
        t1.gpr .rsp = L.SP :=
    fun L g mx m₀ t t1 hc hm => by
      obtain ⟨e1, e2, e3, e4⟩ := VG.Proof.Ed448.X86_64.Verify.argsIn4 hm.1.1
      rw [hc.slot, hc.pPk] at e1
      rw [hc.slot, hc.pSig] at e2
      rw [hc.sp] at e3
      rw [hc.slot, hc.pScr] at e4
      exact ⟨e1, e2, e3, e4, (hm.2.gpr (by decide)).trans hc.rsp⟩
  refine VG.Proof.Ed448.X86_64.Verify.call_tr (by decide) hv hct
    (fun L => [L.PK, L.SIG, ⟨L.K, 57⟩]) (fun L => [L.SCR])
    (fun L g mx m₀ t t1 hL hc _ hm => ?_)
    (fun L g₁ g₂ mx₁ mx₂ m₁ m₂ a b a1 b1 _ _ c₁ c₂ _ _ f₁ f₂ => ?_) fun L _ _ _ _ hL _ _ => ?_
  · obtain ⟨g1, g2, g3, g4, g5⟩ := regs L g mx m₀ t t1 hc hm
    simp only [Proof.Ed448.X86_64.verifyEquationLocal, VG.Proof.Ed448.X86_64.Verify.gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp),
      VG.Proof.Ed448.X86_64.Verify.gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp), VG.Proof.Ed448.X86_64.Verify.gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp),
      VG.Proof.Ed448.X86_64.Verify.gpr_ce _ _ _ (by decide : Reg.rcx ≠ .rsp), VG.Proof.Ed448.X86_64.Verify.rsp_ce, g1, g2, g3, g4, g5, VG.Proof.Ed448.X86_64.Verify.sp_sub8, State.withRegions_rd,
      State.withRegions_wr]
    exact ⟨trivial, trivial, hL.xPk.symm, hL.xSig.symm, VG.Proof.Ed448.X86_64.Verify.k_x' hL, VG.Proof.Ed448.X86_64.Verify.ret_x hL, hL.nScr⟩
  · obtain ⟨x1, x2, x3, x4, x5⟩ := regs L g₁ mx₁ m₁ a a1 c₁ f₁
    obtain ⟨y1, y2, y3, y4, y5⟩ := regs L g₂ mx₂ m₂ b b1 c₂ f₂
    simp only [Proof.Ed448.X86_64.verifyEquationLocal, VG.Proof.Ed448.X86_64.Verify.gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp),
      VG.Proof.Ed448.X86_64.Verify.gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp), VG.Proof.Ed448.X86_64.Verify.gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp),
      VG.Proof.Ed448.X86_64.Verify.gpr_ce _ _ _ (by decide : Reg.rcx ≠ .rsp), VG.Proof.Ed448.X86_64.Verify.rsp_ce, x1, x2, x3, x4, x5, y1, y2, y3, y4, y5, and_self]
  · refine ⟨fun r hr => ?_, fun r hr => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨L.PK, List.mem_append_left _ hL.inPk, VG.Proof.Ed448.X86_64.Verify.within_self _⟩
      · exact ⟨L.SIG, List.mem_append_left _ hL.inSig, VG.Proof.Ed448.X86_64.Verify.within_self _⟩
      · exact ⟨L.FR, by simp, VG.Proof.Ed448.X86_64.Verify.within_off _ (by omega)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact VG.Proof.Ed448.X86_64.Verify.w_scr hL (VG.Proof.Ed448.X86_64.Verify.within_self _)

/-- The frame's body, after the header. -/
theorem rest_tr (hv : VG.Proof.Ed448.X86_64.Verify.EqOk) (hct : VG.Proof.Ed448.X86_64.Verify.EqCT) :
    RelCT isa (VG.Proof.Ed448.X86_64.Verify.Two I fun _ _ _ => True)
      (.seq hash (.seq (callA "vg_ed448_scalar_reduce" Impl.Ed448.X86_64.scalarReduce VG.Proof.Ed448.X86_64.Verify.redArgs)
        (callA "vg_ed448_verify_equation" Impl.Ed448.X86_64.verifyEquation VG.Proof.Ed448.X86_64.Verify.eqArgs))) fun _ _ => True := by
  have h := VG.Proof.Ed448.X86_64.Verify.two_wp (I := I) (Φ := fun _ _ _ => True) (Ψ := fun _ _ _ => True) VG.Proof.Ed448.X86_64.Verify.hash_tr
    fun L g mx m₀ t hL hc _ => WP.mono (VG.Proof.Ed448.X86_64.Verify.hash_ok hL hc) fun t' ⟨hc', _⟩ => ⟨hc', trivial⟩
  have r := VG.Proof.Ed448.X86_64.Verify.two_wp (I := I) (Φ := fun _ _ _ => True) (Ψ := fun _ _ _ => True) VG.Proof.Ed448.X86_64.Verify.red_tr
    fun L g mx m₀ t hL hc _ => WP.mono (VG.Proof.Ed448.X86_64.Verify.reduce_ok hL hc) fun t' ⟨hc', _⟩ => ⟨hc', trivial⟩
  exact h.seq (r.seq (VG.Proof.Ed448.X86_64.Verify.eq_tr hv hct))

end

/-! ## The function -/

/-- The public data of the contract, spelled out. -/
structure VPub (s₁ s₂ : State) : Prop where
  rsp : s₁.gpr .rsp = s₂.gpr .rsp
  rdi : s₁.gpr .rdi = s₂.gpr .rdi
  rsi : s₁.gpr .rsi = s₂.gpr .rsi
  rdx : s₁.gpr .rdx = s₂.gpr .rdx
  rcx : s₁.gpr .rcx = s₂.gpr .rcx
  r8 : s₁.gpr .r8 = s₂.gpr .r8
  r9 : s₁.gpr .r9 = s₂.gpr .r9
  a0 : stackArg s₁ 0 = stackArg s₂ 0

theorem vPub_of {s₁ s₂ : State} (h : (Spec.Ed448.verifyContract X86_64.abi 272).pub s₁ s₂) : VG.Proof.Ed448.X86_64.Verify.VPub s₁ s₂ := by
  sig_pub [Spec.Ed448.verifyContract, Spec.Ed448.verifySig, Spec.Ed448.scratchWords, X86_64.abi, X86_64.argRegs,
    List.range, List.range.loop] at h
  obtain ⟨a, -, c, d, e, f, g, h, i⟩ := h
  exact ⟨a, c, d, e, f, g, h, i⟩

/-- Two runs from states agreeing on the public data have the same layout. -/
theorem vlay_eq {s₁ s₂ : State} (h₁ : VG.Proof.Ed448.X86_64.Verify.VPre s₁) (h₂ : VG.Proof.Ed448.X86_64.Verify.VPre s₂) (h : VG.Proof.Ed448.X86_64.Verify.VPub s₁ s₂) : VG.Proof.Ed448.X86_64.Verify.vlay s₁ = VG.Proof.Ed448.X86_64.Verify.vlay s₂ := by
  have e1 : s₁.rd = s₂.rd := by
    rw [h₁.rd, h₂.rd]; simp only [VG.Proof.Ed448.X86_64.Verify.vPk, VG.Proof.Ed448.X86_64.Verify.vCtx, VG.Proof.Ed448.X86_64.Verify.vMsg, VG.Proof.Ed448.X86_64.Verify.vSig, VG.Proof.Ed448.X86_64.Verify.vArgs, stackArgAddr, h.rdi, h.rsi, h.rdx, h.rcx, h.r8,
      h.r9, h.rsp]
  have e2 : s₁.wr = s₂.wr := by
    rw [h₁.wr, h₂.wr]; simp only [VG.Proof.Ed448.X86_64.Verify.vScr, h.a0]
  simp only [VG.Proof.Ed448.X86_64.Verify.vlay, h.rsp, h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, h.a0, e1, e2]

/-- The entry states of two runs: the precondition and the public data. -/
abbrev VP2 (x y : State) : Prop :=
  (Spec.Ed448.verifyContract X86_64.abi 272).pre x ∧ (Spec.Ed448.verifyContract X86_64.abi 272).pre y ∧
    (Spec.Ed448.verifyContract X86_64.abi 272).pub x y

/-- After `cmp rdx, 256`. -/
abbrev ACmp (x x1 : State) : Prop :=
  x1.gpr = x.gpr ∧ x1.mem = x.mem ∧ x1.rd = x.rd ∧ x1.wr = x.wr ∧ x1.mxcsr = x.mxcsr ∧
    isa.eval .b x1 = some (decide ((x.gpr .rdx).toNat < 256))

/-- After the moves before the push. -/
abbrev VMov (x x2 : State) : Prop :=
  (x.gpr .rdx).toNat < 256 ∧ ((x2.gpr .r11 = stackArg x 0 ∧ x2.gpr .rax = 0 ∧
    x2.mem = x.mem ∧ x2.mxcsr = x.mxcsr) ∧ (∀ r, r ∉ [Reg.r11, .rax] → x2.gpr r = x.gpr r) ∧
    x2.rd = x.rd ∧ x2.wr = x.wr)

theorem hdr_spOnly : ∀ i ∈ hdr, VG.Proof.Ed448.X86_64.Verify.SpOnly i := by
  intro i hi
  simp only [hdr, List.mem_append, List.mem_cons, List.mem_replicate, List.not_mem_nil, or_false] at hi
  rcases hi with ((rfl | rfl | rfl) | ⟨-, rfl⟩) | rfl
  · exact VG.Proof.Ed448.X86_64.Verify.spOnly_nomem (fun _ => rfl) rfl
  · exact ⟨fun s₁ s₂ h => by simp [addrs, State.ea, stk, h], rfl⟩
  · exact ⟨fun s₁ s₂ h => by simp [addrs, srcAddrs, State.ea, stk, h], rfl⟩
  · exact VG.Proof.Ed448.X86_64.Verify.spOnly_nomem (fun _ => rfl) rfl
  · exact ⟨fun s₁ s₂ h => by simp [addrs, State.ea, stk, h], rfl⟩

theorem verify_ct (hv : VG.Proof.Ed448.X86_64.Verify.EqOk) (hct : VG.Proof.Ed448.X86_64.Verify.EqCT) :
    ConstantTime isa (Spec.Ed448.verifyContract X86_64.abi 272).pre (Spec.Ed448.verifyContract X86_64.abi 272).pub
      verify := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  have e0 : (fun s₁ s₂ => (Spec.Ed448.verifyContract X86_64.abi 272).pre s₁ ∧
      (Spec.Ed448.verifyContract X86_64.abi 272).pre s₂ ∧ (Spec.Ed448.verifyContract X86_64.abi 272).pub s₁ s₂) =
      VG.Proof.Ed448.X86_64.Verify.Ghost VG.Proof.Ed448.X86_64.Verify.VP2 (fun x a => a = x) := by
    funext a b; apply propext
    exact ⟨fun h => ⟨a, b, h, rfl, rfl⟩, fun ⟨_, _, h, e₁, e₂⟩ => e₁ ▸ e₂ ▸ h⟩
  rw [e0]
  unfold verify
  -- `cmp rdx, 256`.
  have hcmp := VG.Proof.Ed448.X86_64.Verify.ghost_step (P := VG.Proof.Ed448.X86_64.Verify.VP2) (A := fun x a => a = x) (B := VG.Proof.Ed448.X86_64.Verify.ACmp) (c := .block [.alu .cmp .rdx (.imm 256)])
    (VG.Proof.Ed448.X86_64.Verify.block_rsp_tr (fun i hi => by
        simp only [List.mem_singleton] at hi; subst hi; exact VG.Proof.Ed448.X86_64.Verify.spOnly_nomem (fun _ => rfl) rfl)
      fun a b ⟨x, y, hxy, e₁, e₂⟩ => by subst e₁ e₂; exact (VG.Proof.Ed448.X86_64.Verify.vPub_of hxy.2.2).rsp)
    fun x y a b _ e₁ e₂ => by subst e₁ e₂; exact ⟨VG.Proof.Ed448.X86_64.Verify.cmp_ok _, VG.Proof.Ed448.X86_64.Verify.cmp_ok _⟩
  refine RelCT.seq hcmp (RelCT.ite (fun a b ⟨x, y, hxy, f₁, f₂⟩ => by
    rw [f₁.2.2.2.2.2, f₂.2.2.2.2.2, (VG.Proof.Ed448.X86_64.Verify.vPub_of hxy.2.2).rdx]) ?_ ?_)
  · -- `ctx_len < 256`.
    have hmov := VG.Proof.Ed448.X86_64.Verify.ghost_step (P := VG.Proof.Ed448.X86_64.Verify.VP2) (A := fun x a => VG.Proof.Ed448.X86_64.Verify.ACmp x a ∧ (x.gpr .rdx).toNat < 256) (B := VG.Proof.Ed448.X86_64.Verify.VMov)
      (c := .block [.mov .r11 (.mem (stk 8)), .mov32 .rax (.imm 0)])
      (VG.Proof.Ed448.X86_64.Verify.block_rsp_tr (fun i hi => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl
          · exact ⟨fun s₁ s₂ h => by simp [addrs, srcAddrs, State.ea, stk, h], rfl⟩
          · exact VG.Proof.Ed448.X86_64.Verify.spOnly_nomem (fun _ => rfl) rfl)
        fun a b ⟨x, y, hxy, f₁, f₂⟩ => by rw [f₁.1.1, f₂.1.1]; exact (VG.Proof.Ed448.X86_64.Verify.vPub_of hxy.2.2).rsp)
      fun x y a b hxy f₁ f₂ => by
        have mv : ∀ {x a : State}, (Spec.Ed448.verifyContract X86_64.abi 272).pre x → VG.Proof.Ed448.X86_64.Verify.ACmp x a →
            (x.gpr .rdx).toNat < 256 → WP isa (.block [.mov .r11 (.mem (stk 8)), .mov32 .rax (.imm 0)]) a
              (VG.Proof.Ed448.X86_64.Verify.VMov x) := fun hx f h8 =>
          WP.mono (VG.Proof.Ed448.X86_64.Verify.verifyMov_ok (VG.Proof.Ed448.X86_64.Verify.vPre_of hx) f.1 f.2.1 f.2.2.1) fun x2 ⟨h, k⟩ =>
            ⟨h8, ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.trans f.2.2.2.2.1⟩,
              fun r hr => (k.gpr hr).trans (by rw [f.1]), k.2.1.trans f.2.2.1, k.2.2.trans f.2.2.2.1⟩
        exact ⟨mv hxy.1 f₁.1 f₁.2, mv hxy.2.1 f₂.1 f₂.2⟩
    refine RelCT.seq (RelCT.mono hmov (fun a b ⟨⟨x, y, hxy, f₁, f₂⟩, hc⟩ => ⟨x, y, hxy, ⟨f₁, ?_⟩, ⟨f₂, ?_⟩⟩)
      fun _ _ h => h) ?_
    · rw [f₁.2.2.2.2.2] at hc; simpa using hc
    · rw [f₁.2.2.2.2.2, (VG.Proof.Ed448.X86_64.Verify.vPub_of hxy.2.2).rdx, ← f₂.2.2.2.2.2] at hc
      rw [f₂.2.2.2.2.2] at hc; simpa using hc
    refine RelCT.frame (R := fun _ _ => True) (fun a b ⟨x, y, hxy, f₁, f₂⟩ => by
      rw [f₁.2.2.1 _ (by decide), f₂.2.2.1 _ (by decide)]; exact (VG.Proof.Ed448.X86_64.Verify.vPub_of hxy.2.2).rsp) ?_
    -- The frame's body, from the push.
    let A : State → State → Prop := fun x a => ∃ s₁, VG.Proof.Ed448.X86_64.Verify.VMov x s₁ ∧ a = pushed VG.Impl.Ed448.X86_64.Verify.regs s₁
    let B : State → State → Prop := fun x t => (x.gpr .rdx).toNat < 256 ∧ VG.Proof.Ed448.X86_64.Verify.Ctx (VG.Proof.Ed448.X86_64.Verify.vlay x) x.gpr x.mxcsr x.mem t
    have hh := VG.Proof.Ed448.X86_64.Verify.ghost_step (P := VG.Proof.Ed448.X86_64.Verify.VP2) (A := A) (B := B) (c := .block hdr)
      (VG.Proof.Ed448.X86_64.Verify.block_rsp_tr VG.Proof.Ed448.X86_64.Verify.hdr_spOnly
        fun a b ⟨x, y, hxy, ⟨s₁, f₁, e₁⟩, ⟨s₂, f₂, e₂⟩⟩ => by
          subst e₁ e₂
          rw [pushed_rsp, pushed_rsp, f₁.2.2.1 _ (by decide), f₂.2.2.1 _ (by decide), (VG.Proof.Ed448.X86_64.Verify.vPub_of hxy.2.2).rsp])
      fun x y a b hxy fa fb => by
        have en : ∀ {x a : State}, (Spec.Ed448.verifyContract X86_64.abi 272).pre x → A x a →
            WP isa (.block hdr) a (B x) := fun hx ⟨s₁, f, e⟩ => by
          subst e
          have h := VG.Proof.Ed448.X86_64.Verify.vPre_of hx
          have hL := VG.Proof.Ed448.X86_64.Verify.vlay_ok h f.1
          have hc := VG.Proof.Ed448.X86_64.Verify.entry_ctx hL (by rw [f.2.2.1 _ (by decide), VG.Proof.Ed448.X86_64.Verify.vlay_B]) (f.2.2.2.1.trans rfl)
            (f.2.2.2.2.trans rfl) f.2.1.1 (f.2.2.1 _ (by decide)) (f.2.2.1 _ (by decide)) (f.2.2.1 _ (by decide))
            (f.2.2.1 _ (by decide)) (f.2.2.1 _ (by decide)) (f.2.2.1 _ (by decide))
          exact WP.mono (VG.Proof.Ed448.X86_64.Verify.hdr_ok hL hc) fun t ⟨hc', _⟩ =>
            ⟨f.1, hc'.congr (fun r hr _ => f.2.2.1 r (VG.Proof.Ed448.X86_64.Verify.cs_tmp r hr)) f.2.1.2.2.2 f.2.1.2.2.1⟩
        exact ⟨en hxy.1 fa, en hxy.2.1 fb⟩
    refine RelCT.seq (RelCT.mono hh (fun a b ⟨s₁, s₂, ⟨x, y, hxy, f₁, f₂⟩, e₁, e₂⟩ =>
      ⟨x, y, hxy, ⟨s₁, f₁, e₁⟩, ⟨s₂, f₂, e₂⟩⟩) fun a b ⟨x, y, hxy, ⟨h8x, ca⟩, ⟨_, cb⟩⟩ => ?_)
      (VG.Proof.Ed448.X86_64.Verify.rest_tr (I := fun _ _ _ => True) hv hct)
    have hx := VG.Proof.Ed448.X86_64.Verify.vPre_of hxy.1
    have e := VG.Proof.Ed448.X86_64.Verify.vlay_eq hx (VG.Proof.Ed448.X86_64.Verify.vPre_of hxy.2.1) (VG.Proof.Ed448.X86_64.Verify.vPub_of hxy.2.2)
    exact ⟨VG.Proof.Ed448.X86_64.Verify.vlay x, x.gpr, y.gpr, x.mxcsr, y.mxcsr, x.mem, y.mem, VG.Proof.Ed448.X86_64.Verify.vlay_ok hx h8x, trivial, ca, e ▸ cb,
      trivial, trivial⟩
  · exact VG.Proof.Ed448.X86_64.Verify.block_rsp_tr (fun i hi => by
        simp only [List.mem_singleton] at hi; subst hi; exact VG.Proof.Ed448.X86_64.Verify.spOnly_nomem (fun _ => rfl) rfl)
      fun a b ⟨⟨x, y, hxy, f₁, f₂⟩, _⟩ => by rw [f₁.1, f₂.1]; exact (VG.Proof.Ed448.X86_64.Verify.vPub_of hxy.2.2).rsp

end VG.Proof.Ed448.X86_64.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86_64.Verify.Verified`. -/
section

/-!
# Ed448 verification on x86-64: `Verified`

`verify` is verified against `verifyContract X86_64.abi 272`: correctness
including the ABI (`verify_wp`), constant time (`verify_ct`), and a state
satisfying the precondition, for any proof of `vg_ed448_verify_equation`
(`EqOk`, `EqCT`): the registration file passes its own, so that only it
imports that proof and the group theory it imports.
-/

namespace VG.Proof.Ed448.X86_64.Verify

open VG VG.X86_64 VG.Impl.Ed448.X86_64.Verify

/-- A state satisfying the precondition. -/
def verifySat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x3000 | .rcx => 0x3100 | .r9 => 0x3200 | .rsp => 0x80000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8000A then 0x01 else 0
  rd := [⟨0x1000, 57⟩, ⟨0x3000, 0⟩, ⟨0x3100, 0⟩, ⟨0x3200, 114⟩, ⟨0x80008, 8⟩]
  wr := [⟨0x10000, 8192⟩]

theorem verify_sat : ∃ s, (Spec.Ed448.verifyContract X86_64.abi 272).pre s := by
  sig_implies_sat [Spec.Ed448.verifyContract, Spec.Ed448.verifySig, Spec.Ed448.scratchWords, X86_64.abi,
    X86_64.argRegs, List.range, List.range.loop] [verifySat, stackArg, stackArgAddr, Mem.readW, Mem.read]
    using VG.Proof.Ed448.X86_64.Verify.verifySat

theorem verify_verified (hv : VG.Proof.Ed448.X86_64.Verify.EqOk) (hct : VG.Proof.Ed448.X86_64.Verify.EqCT) :
    Verified X86_64.target verify (Spec.Ed448.verifyContract X86_64.abi 272) :=
  ⟨fun _ h => let ⟨t, s', he, ha, hq⟩ := VG.Proof.Ed448.X86_64.Verify.verify_wp hv h; ⟨t, s', he, ha, hq⟩, VG.Proof.Ed448.X86_64.Verify.verify_ct hv hct, VG.Proof.Ed448.X86_64.Verify.verify_sat⟩

end VG.Proof.Ed448.X86_64.Verify

end
