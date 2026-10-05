import VerifiedGarbage.Impl.MlDsa.X86_64.Message
import VerifiedGarbage.Proof.MlKem.X86_64.SampleCT
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlDsa.Message.Common
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseOCT
import VerifiedGarbage.Proof.MlKem.KPke1024
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Verified

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Message.Layout`. -/
section

/-!
# ML-DSA on x86-64, `sign_message` and `verify_message`: where everything is

Untrusted: everything here is checked by Lean. The function's buffers and
the 112 bytes of stack below its return address, from `B` up (`Lay`): the
frame (72 bytes, from `SP = B + 32`, `rsp` between its push and pop) and the
32 bytes below it that the calls use. `X` is the 1 KiB of `scratch` after
the working space of the function on `μ`. `Ctx` is what holds between the
frame's setting of the formatted message's two bytes and its pop: the
permissions, `rsp`, the callee-saved registers, the arguments in the frame,
the two bytes, and that memory changed only in `X` and the stack. `call_ok`
runs a call of verified code that writes only within `X` in such a state.
-/

namespace VG.Proof.MlDsa.X86_64.Message

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Message
open VG.Proof.MlDsa.Message
open VG.Spec.Sha3 (bytesAt)

/-! ## Regions within others -/

theorem covers_of_within {rs rs' : List Region} (h : ∀ r ∈ rs, ∃ R ∈ rs', Within r R) : Covers rs rs' :=
  Covers.of_sub fun r hr => by
    obtain ⟨R, hR, o, hb, hl⟩ := h r hr
    exact ⟨R, hR, o, hb, hl⟩

/-! ## Addresses -/

theorem ofInt_nat (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toInt_eq; simp

theorem ea_stk (t : State) (d : Nat) : t.ea (VG.Impl.MlDsa.X86_64.Message.stk d) = t.gpr .rsp + BitVec.ofNat 64 d := by
  show t.gpr .rsp + BitVec.ofInt 64 (d : Int) = _
  rw [VG.Proof.MlDsa.X86_64.Message.ofInt_nat]

theorem ea_base (t : State) (r : Reg) (d : Nat) :
    t.ea { base := r, disp := (d : Int) } = t.gpr r + BitVec.ofNat 64 d := by
  show t.gpr r + BitVec.ofInt 64 (d : Int) = _
  rw [VG.Proof.MlDsa.X86_64.Message.ofInt_nat]

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

/-! ## The layout -/

/-- The buffers, the lowest byte of the stack used (`rsp - 112` on entry),
the offset `E` of the 1 KiB `X` in `scratch`, and the permissions on entry. -/
structure Lay where
  B : Addr
  key : Addr
  keyLen : Nat
  msg : Addr
  len : BitVec 64
  ctx : Addr
  ctxLen : BitVec 64
  rnd : Addr
  sig : Addr
  scr : Addr
  E : Nat
  rd : List Region
  wr : List Region

namespace Lay

variable (L : VG.Proof.MlDsa.X86_64.Message.Lay)

/-- `rsp` between the frame's push and pop. -/
abbrev SP : Addr := L.B + BitVec.ofNat 64 40
/-- The frame. -/
abbrev FR : Region := ⟨L.SP, 72⟩
/-- The stack used: the frame and the 40 bytes below it. -/
abbrev STK : Region := ⟨L.B, 112⟩
/-- The return address. -/
abbrev RET : Region := ⟨L.B + BitVec.ofNat 64 112, 8⟩
/-- The 1 KiB of the external function in `scratch`. -/
abbrev X : Addr := L.scr + BitVec.ofNat 64 L.E
abbrev XS : Region := ⟨L.X, 1024⟩
/-- The Keccak state, the sponge functions' working space and `μ`. -/
abbrev ST : Addr := L.X
abbrev KS : Addr := L.X + BitVec.ofNat 64 200
abbrev MU : Addr := L.X + BitVec.ofNat 64 840
abbrev KEY : Region := ⟨L.key, L.keyLen⟩
abbrev MSG : Region := ⟨L.msg, L.len.toNat⟩
abbrev CTX : Region := ⟨L.ctx, L.ctxLen.toNat⟩

/-- What the contract says of where everything is. -/
structure Ok : Prop where
  ctxLt : L.ctxLen.toNat < 256
  hE : L.E + 1024 < 2 ^ 31
  hKey : 128 ≤ L.keyLen ∧ L.keyLen < 2 ^ 31
  nB : L.B.toNat + 112 < 2 ^ 64
  inX : ∃ R ∈ L.wr, Within L.XS R
  inKey : L.KEY ∈ L.rd
  inMsg : L.MSG ∈ L.rd
  inCtx : L.CTX ∈ L.rd
  xKey : L.XS.Disjoint L.KEY
  xMsg : L.XS.Disjoint L.MSG
  xCtx : L.XS.Disjoint L.CTX
  kX : L.STK.Disjoint L.XS
  kKey : L.STK.Disjoint L.KEY
  kMsg : L.STK.Disjoint L.MSG
  kCtx : L.STK.Disjoint L.CTX
  nKey : L.key.toNat + L.keyLen ≤ 2 ^ 64
  nMsg : L.msg.toNat + L.len.toNat ≤ 2 ^ 64
  nCtx : L.ctx.toNat + L.ctxLen.toNat ≤ 2 ^ 64
  lenW : ∀ R ∈ L.wr, R.len ≤ 2 ^ 64

end Lay

namespace Lay.Ok

variable {L : VG.Proof.MlDsa.X86_64.Message.Lay}

theorem stk_x (h : L.Ok) {d n e k : Nat} (h₁ : d + n ≤ 112) (h₂ : e + k ≤ 1024) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.X + BitVec.ofNat 64 e, k⟩ :=
  (h.kX.sub_left (Offset.sub_base _ h₁)).sub_right (Offset.sub_base _ h₂)

theorem stk_r (_h : L.Ok) {r : Region} (hr : L.STK.Disjoint r) {d n : Nat} (h₁ : d + n ≤ 112) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r :=
  hr.sub_left (Offset.sub_base _ h₁)

theorem x_r (_h : L.Ok) {r : Region} (hr : L.XS.Disjoint r) {e k : Nat} (h₂ : e + k ≤ 1024) :
    Region.Disjoint ⟨L.X + BitVec.ofNat 64 e, k⟩ r :=
  hr.sub_left (Offset.sub_base _ h₂)

/-- The 1 KiB is writable. -/
theorem covX (h : L.Ok) {e k : Nat} (h₂ : e + k ≤ 1024) : ∃ R ∈ L.wr, Within ⟨L.X + BitVec.ofNat 64 e, k⟩ R := by
  obtain ⟨R, hR, hw⟩ := h.inX
  exact ⟨R, hR, (within_off L.X h₂).trans hw⟩

end Lay.Ok

/-- `B + 40 - 8 = B + 32`. -/
theorem sp_sub8 (B : Addr) : B + BitVec.ofNat 64 40 - 8 = B + BitVec.ofNat 64 32 := by
  bv_omega

/-- The stack a call from `rsp = B + 40` uses. -/
theorem below_call_sub (B : Addr) {m : Nat} (hm : m ≤ 40) :
    Region.Sub (below (B + BitVec.ofNat 64 40) m) ⟨B, 40⟩ := by
  have : B + BitVec.ofNat 64 40 - BitVec.ofNat 64 m = B + BitVec.ofNat 64 (40 - m) := by
    rw [Offset.sub_ofNat_eq (B + BitVec.ofNat 64 40) (a := m) (b := 40) hm, BitVec.add_sub_cancel]
  show Region.Sub ⟨B + BitVec.ofNat 64 40 - BitVec.ofNat 64 m, m⟩ _
  rw [this]
  exact Offset.sub_base _ (by omega)

theorem below24 (B : Addr) : below (B + BitVec.ofNat 64 32) 24 = ⟨B + BitVec.ofNat 64 8, 24⟩ := by
  show (⟨B + BitVec.ofNat 64 32 - BitVec.ofNat 64 24, 24⟩ : Region) = _
  congr 1; bv_omega

theorem below32 (B : Addr) : below (B + BitVec.ofNat 64 32) 32 = ⟨B, 32⟩ := by
  show (⟨B + BitVec.ofNat 64 32 - BitVec.ofNat 64 32, 32⟩ : Region) = _
  rw [BitVec.add_sub_cancel]

/-! ## Between the frame's push and pop -/

/-- The state between the setting of the formatted message's bytes and the
frame's pop: `g` and `mx` are the registers and MXCSR on entry, `m₀` the
memory. -/
structure Ctx (L : VG.Proof.MlDsa.X86_64.Message.Lay) (g : Reg → BitVec 64) (mx : BitVec 32) (m₀ : Mem) (t : State) : Prop where
  rd : t.rd = L.rd
  wr : t.wr = L.FR :: L.wr
  rsp : t.gpr .rsp = L.SP
  cs : ∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = g r
  mx : t.mxcsr.extractLsb' 6 10 = mx.extractLsb' 6 10
  pScr : t.mem.readW (L.SP + BitVec.ofNat 64 8) 64 = L.scr
  pRnd : t.mem.readW (L.SP + BitVec.ofNat 64 16) 64 = L.rnd
  pSig : t.mem.readW (L.SP + BitVec.ofNat 64 24) 64 = L.sig
  pCtxLen : t.mem.readW (L.SP + BitVec.ofNat 64 32) 64 = L.ctxLen
  pCtx : t.mem.readW (L.SP + BitVec.ofNat 64 40) 64 = L.ctx
  pLen : t.mem.readW (L.SP + BitVec.ofNat 64 48) 64 = L.len
  pMsg : t.mem.readW (L.SP + BitVec.ofNat 64 56) 64 = L.msg
  pKey : t.mem.readW (L.SP + BitVec.ofNat 64 64) 64 = L.key
  hdr : bytesAt t.mem L.SP 2 = [0, BitVec.ofNat 8 L.ctxLen.toNat]
  frame : Frame [L.XS, L.STK] m₀ t.mem

namespace Ctx

variable {L : VG.Proof.MlDsa.X86_64.Message.Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem} {t t' : State}

/-- Code that writes only caller-saved registers. -/
theorem regs (hc : VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hm : t'.mem = t.mem)
    (hmx : t'.mxcsr = t.mxcsr) (hg : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) : VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ t' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, (hg .rsp (by decide)).trans hc.rsp,
    fun r hr hr' => (hg r hr).trans (hc.cs r hr hr'), by rw [hmx]; exact hc.mx,
    by rw [hm]; exact hc.pScr, by rw [hm]; exact hc.pRnd, by rw [hm]; exact hc.pSig,
    by rw [hm]; exact hc.pCtxLen, by rw [hm]; exact hc.pCtx, by rw [hm]; exact hc.pLen,
    by rw [hm]; exact hc.pMsg, by rw [hm]; exact hc.pKey, by rw [hm]; exact hc.hdr,
    by rw [hm]; exact hc.frame⟩

/-- The same state, with the entry registers, MXCSR and memory given by others equal to them. -/
theorem congr (hc : VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ t) {g' : Reg → BitVec 64} {mx' : BitVec 32} {m₀' : Mem}
    (hg : ∀ r ∈ calleeSaved, r ≠ .rsp → g r = g' r) (hmx : mx = mx') (hm : m₀ = m₀') : VG.Proof.MlDsa.X86_64.Message.Ctx L g' mx' m₀' t := by
  subst hmx hm
  exact ⟨hc.rd, hc.wr, hc.rsp, fun r hr hr' => (hc.cs r hr hr').trans (hg r hr hr'), hc.mx, hc.pScr, hc.pRnd,
    hc.pSig, hc.pCtxLen, hc.pCtx, hc.pLen, hc.pMsg, hc.pKey, hc.hdr, hc.frame⟩

/-- A slot of the frame is readable. -/
theorem inFr (hc : VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ t) {d : Nat} (h₂ : d + 8 ≤ 72) :
    InRegions (t.rd ++ t.wr) (L.SP + BitVec.ofNat 64 d) 8 :=
  ⟨L.FR, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ h₂ (by omega)⟩

theorem inFrW (hc : VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ t) {d n : Nat} (h₂ : d + n ≤ 72) :
    InRegions t.wr (L.SP + BitVec.ofNat 64 d) n :=
  ⟨L.FR, by rw [hc.wr]; simp, Offset.contains_base _ h₂ (by omega)⟩

theorem ea_fr (hc : VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ t) (d : Nat) : t.ea (VG.Impl.MlDsa.X86_64.Message.stk d) = L.SP + BitVec.ofNat 64 d := by
  rw [VG.Proof.MlDsa.X86_64.Message.ea_stk, hc.rsp]

/-- The return address of a call from the frame. -/
theorem ret (hc : VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ t) : below (t.gpr .rsp) 8 = ⟨L.B + BitVec.ofNat 64 32, 8⟩ := by
  rw [hc.rsp]
  show (⟨L.B + BitVec.ofNat 64 40 - BitVec.ofNat 64 8, 8⟩ : Region) = _
  rw [show (BitVec.ofNat 64 8 : BitVec 64) = 8 from rfl, VG.Proof.MlDsa.X86_64.Message.sp_sub8]

/-- A byte of a region apart from `X` and the stack, as on entry. -/
theorem byte (hc : VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ t) {R : Region} (hx : L.XS.Disjoint R) (hk : L.STK.Disjoint R)
    (hR : R.len ≤ 2 ^ 64) {i : Nat} (hi : i < R.len) :
    t.mem (R.base + BitVec.ofNat 64 i) = m₀ (R.base + BitVec.ofNat 64 i) :=
  Frame.bytes (R := R) hc.frame (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hx.symm
    · exact hk.symm) hR hi

theorem bytesAt_eq (hc : VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ t) {p : Addr} {n : Nat} (hx : L.XS.Disjoint ⟨p, n⟩)
    (hk : L.STK.Disjoint ⟨p, n⟩) (hn : n ≤ 2 ^ 64) : bytesAt t.mem p n = bytesAt m₀ p n :=
  Proof.MlKem.bytesAt_congr fun _ hi => hc.byte (R := ⟨p, n⟩) hx hk hn hi

/-- A byte on entry to a call from the frame, if the return address misses it. -/
theorem ce_byte (t : State) {R : Region} (hd : (below (t.gpr .rsp) 8).Disjoint R)
    (hR : R.len ≤ 2 ^ 64) {i : Nat} (hi : i < R.len) :
    t.callEntry.mem (R.base + BitVec.ofNat 64 i) = t.mem (R.base + BitVec.ofNat 64 i) :=
  Frame.bytes (rs := [below (t.gpr .rsp) 8])
    (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (below_call _ (by omega) (by omega)))
    (by simpa using hd.symm) hR hi

theorem ce_bytesAt (hc : VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ t) {p : Addr} {n : Nat}
    (hd : Region.Disjoint ⟨L.B + BitVec.ofNat 64 32, 8⟩ ⟨p, n⟩) (hn : n ≤ 2 ^ 64) :
    bytesAt t.callEntry.mem p n = bytesAt t.mem p n :=
  Proof.MlKem.bytesAt_congr fun _ hi => VG.Proof.MlDsa.X86_64.Message.Ctx.ce_byte t (R := ⟨p, n⟩) (by rw [hc.ret]; exact hd) hn hi

end Ctx

/-- A state whose memory differs from that of a `Ctx` state only within `X`
and the 32 bytes below the frame. -/
theorem Ctx.of_frame {L : VG.Proof.MlDsa.X86_64.Message.Lay} (hL : L.Ok) {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem} {t t' : State}
    (hc : VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hcs : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r)
    (hmx : t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10) {rs : List Region}
    (hf : Frame (rs ++ [⟨L.B, 40⟩]) t.mem t'.mem) (hrs : ∀ r ∈ rs, Within r L.XS) : VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ t' := by
  have hdisj : ∀ d n, d + n ≤ 72 → ∀ r ∈ rs ++ [⟨L.B, 40⟩],
      Region.Disjoint ⟨L.SP + BitVec.ofNat 64 d, n⟩ r := by
    intro d n h₁ r hr
    rw [Lay.SP, add_add]
    rcases List.mem_append.mp hr with hr | hr
    · exact (hL.stk_r hL.kX (d := 40 + d) (n := n) (by omega)).sub_right (hrs r hr).sub
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base _ (by omega) (by omega)
  have keep : ∀ d, d + 8 ≤ 72 →
      t'.mem.readW (L.SP + BitVec.ofNat 64 d) 64 = t.mem.readW (L.SP + BitVec.ofNat 64 d) 64 :=
    fun d h => hf.readW (Region.contains_self _ _) (hdisj d 8 h) (by decide)
  have khdr : bytesAt t'.mem L.SP 2 = bytesAt t.mem L.SP 2 :=
    Proof.MlKem.bytesAt_congr fun i hi => by
      have := hf.bytes (R := ⟨L.SP + BitVec.ofNat 64 0, 2⟩) (fun r hr => hdisj 0 2 (by omega) r hr)
        (by show 2 ≤ 2 ^ 64; decide) hi
      simpa only [BitVec.add_zero] using this
  refine ⟨hrd.trans hc.rd, hwr.trans hc.wr, (hcs .rsp (by decide)).trans hc.rsp,
    fun r hr hr' => (hcs r hr).trans (hc.cs r hr hr'),
    hmx.trans hc.mx, (keep 8 (by omega)).trans hc.pScr, (keep 16 (by omega)).trans hc.pRnd,
    (keep 24 (by omega)).trans hc.pSig, (keep 32 (by omega)).trans hc.pCtxLen,
    (keep 40 (by omega)).trans hc.pCtx, (keep 48 (by omega)).trans hc.pLen,
    (keep 56 (by omega)).trans hc.pMsg, (keep 64 (by omega)).trans hc.pKey, khdr.trans hc.hdr,
    hc.frame.trans (Frame.sub hf fun r hr => ?_)⟩
  rcases List.mem_append.mp hr with hr | hr
  · exact ⟨L.XS, by simp, (hrs r hr).sub⟩
  · simp only [List.mem_singleton] at hr; subst hr
    refine ⟨L.STK, by simp, ?_⟩
    have := Offset.sub_base L.B (d := 0) (n := 40) (k := 112) (by omega)
    simpa using this

/-! ## Calls that write only within `X` -/

/-- A call of verified code from the frame, reading regions within the
permissions and writing only within `X`, keeps `Ctx`. -/
theorem call_ok {L : VG.Proof.MlDsa.X86_64.Message.Lay} (hL : L.Ok) {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}
    {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsp : NoSp c) (hd : c.depth ≤ 3) {t : State} (hc : VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ t)
    {rd wr : List Region} (hpre : k.pre (t.callEntry.withRegions rd wr))
    (hsub : ∀ r ∈ rd, ∃ R ∈ L.rd ++ L.FR :: L.wr, Within r R)
    (hwsub : ∀ r ∈ wr, Within r L.XS) {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ s' → Frame (wr ++ [⟨L.B, 40⟩]) t.mem s'.mem →
      (∀ r, (∀ i ∈ VG.instrs c, Taint.clobbers i r = false) → s'.gpr r = t.gpr r) →
      (∃ s₂ : State, s₂.mem = s'.mem ∧ (∀ r, r ≠ .rsp → s₂.gpr r = s'.gpr r) ∧
        k.post (t.callEntry.withRegions rd wr) s₂) → Q s') :
    WP isa (.call n c) t Q := by
  obtain ⟨RX, hRX, hX⟩ := hL.inX
  have hwX : ∀ r ∈ wr, ∃ R ∈ L.wr, Within r R := fun r hr => ⟨RX, hRX, (hwsub r hr).trans hX⟩
  have hcov : Covers (rd ++ wr) (t.rd ++ t.wr) := by
    rw [hc.rd, hc.wr]
    refine VG.Proof.MlDsa.X86_64.Message.covers_of_within fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · exact hsub r hr
    · obtain ⟨R, hR, hw⟩ := hwX r hr
      exact ⟨R, by simp [hR], hw⟩
  have hcovw : Covers wr t.wr := by
    rw [hc.wr]
    refine VG.Proof.MlDsa.X86_64.Message.covers_of_within fun r hr => ?_
    obtain ⟨R, hR, hw⟩ := hwX r hr
    exact ⟨R, List.mem_cons_of_mem _ hR, hw⟩
  refine WP.call_mx hv hsp (by omega) hpre hcov hcovw fun s' hrd hwr hcs hf hg hpost hmx => ?_
  have hf' : Frame (wr ++ [⟨L.B, 40⟩]) t.mem s'.mem := by
    refine Frame.sub hf fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
      rw [hc.rsp]
      exact VG.Proof.MlDsa.X86_64.Message.below_call_sub _ (by omega)
  -- The frame is apart from what the call writes.
  have hdisj : ∀ d n, d + n ≤ 72 → ∀ r ∈ wr ++ [⟨L.B, 40⟩],
      Region.Disjoint ⟨L.SP + BitVec.ofNat 64 d, n⟩ r := by
    intro d n h₁ r hr
    rw [Lay.SP, add_add]
    rcases List.mem_append.mp hr with hr | hr
    · exact (hL.stk_r hL.kX (d := 40 + d) (n := n) (by omega)).sub_right (hwsub r hr).sub
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base _ (by omega) (by omega)
  have keep : ∀ d, d + 8 ≤ 72 →
      s'.mem.readW (L.SP + BitVec.ofNat 64 d) 64 = t.mem.readW (L.SP + BitVec.ofNat 64 d) 64 :=
    fun d h => hf'.readW (Region.contains_self _ _) (hdisj d 8 h) (by decide)
  have khdr : bytesAt s'.mem L.SP 2 = bytesAt t.mem L.SP 2 :=
    Proof.MlKem.bytesAt_congr fun i hi => by
      have := hf'.bytes (R := ⟨L.SP + BitVec.ofNat 64 0, 2⟩) (fun r hr => hdisj 0 2 (by omega) r hr)
        (by show 2 ≤ 2 ^ 64; decide) hi
      simpa only [BitVec.add_zero] using this
  refine hQ s' ⟨hrd.trans hc.rd, hwr.trans hc.wr, ?_, fun r hr hr' => (hcs r hr).trans (hc.cs r hr hr'),
    hmx.trans hc.mx, (keep 8 (by omega)).trans hc.pScr, (keep 16 (by omega)).trans hc.pRnd,
    (keep 24 (by omega)).trans hc.pSig, (keep 32 (by omega)).trans hc.pCtxLen,
    (keep 40 (by omega)).trans hc.pCtx, (keep 48 (by omega)).trans hc.pLen,
    (keep 56 (by omega)).trans hc.pMsg, (keep 64 (by omega)).trans hc.pKey, khdr.trans hc.hdr,
    hc.frame.trans (Frame.sub hf' fun r hr => ?_)⟩ hf' hg hpost
  · rw [hcs .rsp (by simp [calleeSaved]), hc.rsp]
  · rcases List.mem_append.mp hr with hr | hr
    · exact ⟨L.XS, by simp, (hwsub r hr).sub⟩
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨L.STK, by simp, ?_⟩
      have := Offset.sub_base L.B (d := 0) (n := 40) (k := 112) (by omega)
      simpa using this

end VG.Proof.MlDsa.X86_64.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Message.Args`. -/
section

/-!
# ML-DSA on x86-64, `sign_message` and `verify_message`: the moves of a call's arguments

Untrusted: everything here is checked by Lean. `setArgs as` moves each
argument (a slot of the frame, a slot plus an offset, an immediate, `rsp`
or `rax`) into its register: afterwards each argument register holds the
argument's value in the state before the moves (`setArgs_ok`), and nothing
else changed but those registers and the flags.
-/

namespace VG.Proof.MlDsa.X86_64.Message

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly)

/-- The value of an argument in the state `s`. -/
def _root_.VG.Impl.MlDsa.X86_64.Message.Arg.val (s : State) : VG.Impl.MlDsa.X86_64.Message.Arg → BitVec 64
  | .slot f => s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 f) 64
  | .slotOff f o => s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 f) 64 + BitVec.ofNat 64 o
  | .imm v => BitVec.ofNat 64 v
  | .sp => s.gpr .rsp
  | .ret => s.gpr .rax

/-- A slot within the frame, an offset or an immediate of 31 bits. -/
def _root_.VG.Impl.MlDsa.X86_64.Message.Arg.ok : VG.Impl.MlDsa.X86_64.Message.Arg → Bool
  | .slot f => decide (f + 8 ≤ 72)
  | .slotOff f o => decide (f + 8 ≤ 72) && decide (o < 2 ^ 31)
  | .imm v => decide (v < 2 ^ 31)
  | .sp => true
  | .ret => true

/-- The slots of the frame are readable. -/
abbrev FrOk (s : State) : Prop := ∀ f, f + 8 ≤ 72 → InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 f) 8

theorem Arg.mov_ok (d : Reg) (a : VG.Impl.MlDsa.X86_64.Message.Arg) (ha : a.ok = true) (hd : d ∈ argRegs6) (s : State) (hfr : VG.Proof.MlDsa.X86_64.Message.FrOk s) :
    WP isa (.block (a.mov d)) s fun s1 =>
      (s1.gpr d = a.val s ∧ s1.mem = s.mem ∧ s1.mxcsr = s.mxcsr) ∧ Keep [d] s s1 := by
  refine WP.keep [d] ?_ (by cases a <;> cases d <;> rfl)
  have hsp : d ≠ .rsp := fun h => by subst h; revert hd; decide
  have hax : d ≠ .rax := fun h => by subst h; revert hd; decide
  cases a with
  | slot f =>
    simp only [Arg.ok, decide_eq_true_eq] at ha
    simp only [Arg.mov, Arg.val]
    xrun [VG.Proof.MlDsa.X86_64.Message.ea_stk, hfr f ha, RegUpd.gpr_setReg_self, RegUpd.mxcsr_setReg]
  | slotOff f o =>
    simp only [Arg.ok, Bool.and_eq_true, decide_eq_true_eq] at ha
    simp only [Arg.mov, Arg.val]
    xrun [VG.Proof.MlDsa.X86_64.Message.ea_stk, hfr f ha.1, VG.Proof.MlDsa.X86_64.Message.sx32 ha.2, RegUpd.gpr_setReg_self, RegUpd.mxcsr_setReg, RegUpd.mxcsr_setFlags]
  | imm v =>
    simp only [Arg.ok, decide_eq_true_eq] at ha
    simp only [Arg.mov, Arg.val]
    xrun [VG.Proof.MlDsa.X86_64.Message.zx32 (show v < 2 ^ 32 by omega), RegUpd.gpr_setReg_self, RegUpd.mxcsr_setReg]
  | sp =>
    simp only [Arg.mov, Arg.val]
    xrun [RegUpd.gpr_setReg_self, RegUpd.mxcsr_setReg]
  | ret =>
    simp only [Arg.mov, Arg.val]
    xrun [RegUpd.gpr_setReg_self, RegUpd.mxcsr_setReg]

/-- The value of an argument is the same after moves into other argument registers. -/
theorem Arg.val_keep {d : Reg} (hd : d ∈ argRegs6) {s s1 : State} (hm : s1.mem = s.mem) (k : Keep [d] s s1)
    (a : VG.Impl.MlDsa.X86_64.Message.Arg) : a.val s1 = a.val s := by
  have hsp : Reg.rsp ∉ [d] := by
    simp only [List.mem_singleton]; intro h; subst h; revert hd; decide
  have hax : Reg.rax ∉ [d] := by
    simp only [List.mem_singleton]; intro h; subst h; revert hd; decide
  cases a <;> simp only [Arg.val, hm, k.gpr hsp, k.gpr hax]

theorem frOk_keep {d : Reg} (hd : d ∈ argRegs6) {s s1 : State} (k : Keep [d] s s1) (h : VG.Proof.MlDsa.X86_64.Message.FrOk s) : VG.Proof.MlDsa.X86_64.Message.FrOk s1 := by
  have hsp : Reg.rsp ∉ [d] := by
    simp only [List.mem_singleton]; intro h; subst h; revert hd; decide
  intro f hf
  rw [k.2.1, k.2.2, k.gpr hsp]
  exact h f hf

theorem setArgsGen_ok : ∀ (ds : List Reg) (as : List VG.Impl.MlDsa.X86_64.Message.Arg), ds.Nodup → (∀ d ∈ ds, d ∈ argRegs6) →
    as.all Arg.ok = true → ∀ s : State, VG.Proof.MlDsa.X86_64.Message.FrOk s →
    WP isa (.block ((ds.zip as).flatMap fun (d, a) => a.mov d)) s fun s1 =>
      ((∀ da ∈ ds.zip as, s1.gpr da.1 = da.2.val s) ∧ s1.mem = s.mem ∧ s1.mxcsr = s.mxcsr) ∧ Keep ds s s1
  | [], _, _, _, _, s, _ => WP.block_nil ⟨⟨fun _ h => by simp at h, rfl, rfl⟩, Keep.refl _ _⟩
  | _ :: _, [], _, _, _, s, _ => WP.block_nil ⟨⟨fun _ h => by simp at h, rfl, rfl⟩, Keep.refl _ _⟩
  | d :: ds, a :: as, hn, hd, ha, s, hfr => by
    rw [List.nodup_cons] at hn
    simp only [List.all_cons, Bool.and_eq_true] at ha
    simp only [List.zip_cons_cons, List.flatMap_cons]
    rw [WP.block_append_iff]
    have hd0 := hd d (List.mem_cons_self ..)
    refine WP.mono (Arg.mov_ok d a ha.1 hd0 s hfr) fun s1 ⟨⟨h1, hm1, hx1⟩, k1⟩ => ?_
    refine WP.mono (VG.Proof.MlDsa.X86_64.Message.setArgsGen_ok ds as hn.2 (fun d' h => hd d' (List.mem_cons_of_mem _ h)) ha.2 s1
      (VG.Proof.MlDsa.X86_64.Message.frOk_keep hd0 k1 hfr))
      fun s2 ⟨⟨h2, hm2, hx2⟩, k2⟩ => ⟨⟨fun da hda => ?_, hm2.trans hm1, hx2.trans hx1⟩,
        (k1.trans k2).mono fun r hr => by simpa using hr⟩
    rcases List.mem_cons.mp hda with rfl | hda
    · rw [k2.gpr hn.1, h1]
    · rw [h2 da hda, Arg.val_keep hd0 hm1 k1]

theorem argRegs6_nodup : argRegs6.Nodup := by decide

/-- The registers the moves of arguments write. -/
abbrev argRegs : List Reg := [.rcx, .rdx, .rsi, .rdi, .r8, .r9]

theorem argRegs_cs : ∀ r ∈ calleeSaved, r ∉ VG.Proof.MlDsa.X86_64.Message.argRegs := by decide

/-- The moves of the arguments `as`. -/
theorem setArgs_ok (as : List VG.Impl.MlDsa.X86_64.Message.Arg) (ha : as.all Arg.ok = true) (s : State) (hfr : VG.Proof.MlDsa.X86_64.Message.FrOk s) :
    WP isa (.block (setArgs as)) s fun s1 =>
      ((∀ da ∈ argRegs6.zip as, s1.gpr da.1 = da.2.val s) ∧ s1.mem = s.mem ∧ s1.mxcsr = s.mxcsr) ∧
        Keep VG.Proof.MlDsa.X86_64.Message.argRegs s s1 := by
  refine WP.mono (VG.Proof.MlDsa.X86_64.Message.setArgsGen_ok argRegs6 as VG.Proof.MlDsa.X86_64.Message.argRegs6_nodup (fun _ h => h) ha s hfr) fun s1 ⟨h, k⟩ => ⟨h, ?_⟩
  refine ⟨fun r hr => k.gpr fun hm => hr ?_, k.2⟩
  simp only [argRegs6, VG.Proof.MlDsa.X86_64.Message.argRegs, List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
  rcases hm with h | h | h | h | h | h <;> simp [h]

/-- The arguments of `as`, in their registers after the moves. -/
abbrev ArgsIn (as : List VG.Impl.MlDsa.X86_64.Message.Arg) (s s1 : State) : Prop := ∀ da ∈ argRegs6.zip as, s1.gpr da.1 = da.2.val s

theorem argsIn4 {a b c d : VG.Impl.MlDsa.X86_64.Message.Arg} {s s1 : State} (h : VG.Proof.MlDsa.X86_64.Message.ArgsIn [a, b, c, d] s s1) :
    s1.gpr .rdi = a.val s ∧ s1.gpr .rsi = b.val s ∧ s1.gpr .rdx = c.val s ∧ s1.gpr .rcx = d.val s :=
  ⟨h (.rdi, a) (by simp [argRegs6]), h (.rsi, b) (by simp [argRegs6]), h (.rdx, c) (by simp [argRegs6]),
    h (.rcx, d) (by simp [argRegs6])⟩

theorem argsIn5 {a b c d e : VG.Impl.MlDsa.X86_64.Message.Arg} {s s1 : State} (h : VG.Proof.MlDsa.X86_64.Message.ArgsIn [a, b, c, d, e] s s1) :
    s1.gpr .rdi = a.val s ∧ s1.gpr .rsi = b.val s ∧ s1.gpr .rdx = c.val s ∧ s1.gpr .rcx = d.val s ∧
      s1.gpr .r8 = e.val s :=
  ⟨h (.rdi, a) (by simp [argRegs6]), h (.rsi, b) (by simp [argRegs6]), h (.rdx, c) (by simp [argRegs6]),
    h (.rcx, d) (by simp [argRegs6]), h (.r8, e) (by simp [argRegs6])⟩

theorem argsIn6 {a b c d e f : VG.Impl.MlDsa.X86_64.Message.Arg} {s s1 : State} (h : VG.Proof.MlDsa.X86_64.Message.ArgsIn [a, b, c, d, e, f] s s1) :
    s1.gpr .rdi = a.val s ∧ s1.gpr .rsi = b.val s ∧ s1.gpr .rdx = c.val s ∧ s1.gpr .rcx = d.val s ∧
      s1.gpr .r8 = e.val s ∧ s1.gpr .r9 = f.val s :=
  ⟨h (.rdi, a) (by simp [argRegs6]), h (.rsi, b) (by simp [argRegs6]), h (.rdx, c) (by simp [argRegs6]),
    h (.rcx, d) (by simp [argRegs6]), h (.r8, e) (by simp [argRegs6]), h (.r9, f) (by simp [argRegs6])⟩

/-! ## The values of the arguments in the frame -/

section
variable {L : VG.Proof.MlDsa.X86_64.Message.Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem} {t : State}

theorem Ctx.frOk (hc : VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ t) : VG.Proof.MlDsa.X86_64.Message.FrOk t := fun f hf => by
  rw [hc.rsp]; exact hc.inFr hf

theorem Ctx.slot (hc : VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ t) (f : Nat) :
    (Arg.slot f).val t = t.mem.readW (L.SP + BitVec.ofNat 64 f) 64 := by
  simp only [Arg.val, hc.rsp]

theorem Ctx.slotOff (hc : VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ t) (f o : Nat) :
    (Arg.slotOff f o).val t = t.mem.readW (L.SP + BitVec.ofNat 64 f) 64 + BitVec.ofNat 64 o := by
  simp only [Arg.val, hc.rsp]

/-- The Keccak state, the sponge functions' working space and `μ`. -/
theorem Ctx.aSt (hc : VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ t) (p : Spec.MlDsa.Params) (hE : oE p = L.E) :
    (VG.Impl.MlDsa.X86_64.Message.aSt p).val t = L.ST := by
  simp only [Impl.MlDsa.X86_64.Message.aSt, hc.slotOff, fScr, hc.pScr, hE]

theorem Ctx.aKs (hc : VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ t) (p : Spec.MlDsa.Params) (hE : oE p = L.E) :
    (VG.Impl.MlDsa.X86_64.Message.aKs p).val t = L.KS := by
  simp only [Impl.MlDsa.X86_64.Message.aKs, hc.slotOff, fScr]
  rw [hc.pScr, hE, Lay.KS, Lay.X, add_add]

theorem Ctx.aMu (hc : VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ t) (p : Spec.MlDsa.Params) (hE : oE p = L.E) :
    (VG.Impl.MlDsa.X86_64.Message.aMu p).val t = L.MU := by
  simp only [Impl.MlDsa.X86_64.Message.aMu, hc.slotOff, fScr]
  rw [hc.pScr, hE, Lay.MU, Lay.X, add_add]

end

end VG.Proof.MlDsa.X86_64.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Message.Hash`. -/
section

/-!
# ML-DSA on x86-64, `sign_message` and `verify_message`: SHAKE256 through the sponge functions

Untrusted: everything here is checked by Lean. Between the frame's push and
pop (`Ctx`): zeroing the Keccak state at `X` (`zeroSt_ok`), and the calls of
`vg_keccak_absorb`, `vg_keccak_pad` and `vg_keccak_squeeze` on it, with
their working space at `X + 200` (`kabs_ok`, `kpad_ok`, `ksqz_ok`); then
`muHash`, which leaves `μ = H(tr ‖ 0 ‖ ctx_len ‖ ctx ‖ M, 64)` at `X + 840`
(`muHash_ok`), and `trHash`, which leaves `H(pk, 64)` there (`trHash_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Message

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.X86_64 (Keep WP.keep AbsorbArgs PadArgs SqueezeArgs absorb_pre pad_pre squeeze_pre absorb_nosp
  pad_nosp squeeze_nosp absorb_depth pad_depth squeeze_depth callEntry_repr callEntry_bytesAt callEntry_stateAt
  ofNat_toNat' rate_lt)
open VG.Spec.Sha3 (bytesAt stateAt rates absorb pad squeezeFrom Repr)
open VG.Spec.MlDsa (Params)

section
variable {L : VG.Proof.MlDsa.X86_64.Message.Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem} {p : Params}

/-- The 16 bytes below `rsp` that a sponge function's call uses are in the
32 bytes below the frame. -/
theorem k16 {t : State} (hc : VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ t) {r : Region} (h : Region.Disjoint ⟨L.B, 40⟩ r) :
    (below (t.gpr .rsp) 16).Disjoint r := by
  rw [hc.rsp]; exact h.sub_left (VG.Proof.MlDsa.X86_64.Message.below_call_sub L.B (by omega))

theorem x0 (L : VG.Proof.MlDsa.X86_64.Message.Lay) : L.X + BitVec.ofNat 64 0 = L.X := BitVec.add_zero _

theorem k32x (hL : L.Ok) {e k : Nat} (h₂ : e + k ≤ 1024) :
    Region.Disjoint ⟨L.B, 40⟩ ⟨L.X + BitVec.ofNat 64 e, k⟩ := by
  have := hL.stk_x (d := 0) (n := 40) (by omega) h₂
  simpa only [BitVec.add_zero] using this

theorem st_ks : Region.Disjoint ⟨L.ST, 200⟩ ⟨L.KS, 640⟩ := by
  have := Offset.disjoint L.X (d := 0) (n := 200) (e := 200) (k := 640) (by omega) (by omega) (by omega)
  simpa only [VG.Proof.MlDsa.X86_64.Message.x0] using this

theorem st_mu : Region.Disjoint ⟨L.ST, 200⟩ ⟨L.MU, 64⟩ := by
  have := Offset.disjoint L.X (d := 0) (n := 200) (e := 840) (k := 64) (by omega) (by omega) (by omega)
  simpa only [VG.Proof.MlDsa.X86_64.Message.x0] using this

theorem mu_ks : Region.Disjoint ⟨L.MU, 64⟩ ⟨L.KS, 640⟩ :=
  Offset.disjoint L.X (d := 840) (n := 64) (e := 200) (k := 640) (by omega) (by omega) (by omega)

theorem w_st : Within ⟨L.ST, 200⟩ L.XS := within_base _ (by omega)
theorem w_ks : Within ⟨L.KS, 640⟩ L.XS := within_off _ (by omega)
theorem w_mu : Within ⟨L.MU, 64⟩ L.XS := within_off _ (by omega)

theorem k_st (hL : L.Ok) : Region.Disjoint ⟨L.B, 40⟩ ⟨L.ST, 200⟩ := by
  have := VG.Proof.MlDsa.X86_64.Message.k32x hL (e := 0) (k := 200) (by omega); simpa only [VG.Proof.MlDsa.X86_64.Message.x0] using this
theorem k_ks (hL : L.Ok) : Region.Disjoint ⟨L.B, 40⟩ ⟨L.KS, 640⟩ := VG.Proof.MlDsa.X86_64.Message.k32x hL (by omega)
theorem k_mu (hL : L.Ok) : Region.Disjoint ⟨L.B, 40⟩ ⟨L.MU, 64⟩ := VG.Proof.MlDsa.X86_64.Message.k32x hL (by omega)

/-- The return address of a call from the frame, apart from what a region
apart from the 32 bytes below the frame. -/
theorem ret_of_k {r : Region} (h : Region.Disjoint ⟨L.B, 40⟩ r) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 32, 8⟩ r :=
  h.sub_left (Offset.sub_base _ (by omega))

/-! ## Zeroing the state -/

theorem zeroSt_ok (hL : L.Ok) (hE : oE p = L.E) {t : State} (hc : VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ t) :
    WP isa (VG.Impl.MlDsa.X86_64.Message.zeroSt p) t fun t' => VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ t' ∧ Frame [⟨L.ST, 200⟩] t.mem t'.mem ∧
      stateAt t'.mem L.ST = Spec.Sha3.zero := by
  have hok : (VG.Impl.MlDsa.X86_64.Message.aSt p).ok = true := by
    simp only [Impl.MlDsa.X86_64.Message.aSt, Arg.ok, fScr, Bool.and_eq_true, decide_eq_true_eq]
    have := hL.hE; omega
  refine WP.seq (WP.mono (Arg.mov_ok .rdi (VG.Impl.MlDsa.X86_64.Message.aSt p) hok (by decide) t hc.frOk)
    fun t1 ⟨⟨h1, hm1, hx1⟩, k1⟩ => ?_)
  have hc1 : VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ t1 := hc.regs k1.2.1 k1.2.2 hm1 hx1 fun r hr => k1.gpr (by
    simp only [List.mem_singleton]; exact VG.Proof.MlDsa.X86_64.Message.ne_cs hr (by decide))
  rw [hc.aSt p hE] at h1
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (WP.keep [.rax] (Q := fun s1 => s1.mem = t1.mem ∧ s1.gpr .rax = 0 ∧ s1.mxcsr = t1.mxcsr)
    (by xrun [RegUpd.mxcsr_setReg]) (by decide)) fun t2 ⟨⟨hm2, hax, hx2⟩, k2⟩ => ?_
  have hdi : t2.gpr .rdi = L.ST := (k2.gpr (by decide)).trans h1
  have hw2 : t2.wr = L.FR :: L.wr := k2.2.2.trans hc1.wr
  obtain ⟨R, hR, hXR⟩ := hL.inX
  refine WP.mono_mx (by decide) (Proof.MlDsa.X86_64.Sign.zeroSt_ok .rdi 0 t2 hax fun i hi => ?_)
    fun t3 ⟨hz, hf, k3⟩ hx3 => ?_
  · rw [hw2, hdi, VG.Proof.MlDsa.X86_64.Message.x0]
    obtain ⟨o, hb, hl⟩ := (within_off L.X (d := 8 * i) (n := 8) (k := 1024) (by omega)).trans hXR
    refine ⟨R, List.mem_cons_of_mem _ hR, ?_⟩
    simp only at hb
    rw [hb]
    exact Offset.contains_base _ hl (by have := hL.lenW R hR; simp only at hl; omega)
  · rw [hdi, VG.Proof.MlDsa.X86_64.Message.x0] at hz hf
    rw [hm2] at hf
    have hcs : ∀ r ∈ calleeSaved, t3.gpr r = t1.gpr r := fun r hr => by
      rw [k3.gpr (by simp), k2.gpr (by simp only [List.mem_singleton]; exact VG.Proof.MlDsa.X86_64.Message.ne_cs hr (by decide))]
    have hf' : Frame ([⟨L.ST, 200⟩] ++ [⟨L.B, 40⟩]) t1.mem t3.mem := hf.mono fun r hr => by simp at hr ⊢; exact .inl hr
    refine ⟨hc1.of_frame hL (k3.2.1.trans k2.2.1) (k3.2.2.trans k2.2.2) hcs
      (by rw [hx3, hx2]) hf' (by simpa using VG.Proof.MlDsa.X86_64.Message.w_st), by rw [← hm1]; exact hf, hz⟩

/-! ## Absorbing -/

/-- The arguments of a call of `vg_keccak_absorb`. -/
abbrev absArgs (p : Params) (src len pos : VG.Impl.MlDsa.X86_64.Message.Arg) : List VG.Impl.MlDsa.X86_64.Message.Arg := [VG.Impl.MlDsa.X86_64.Message.aSt p, .imm 136, pos, src, len, VG.Impl.MlDsa.X86_64.Message.aKs p]

theorem kabs_ok (hL : L.Ok) (hE : oE p = L.E) {t : State} (hc : VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ t)
    {src len pos : VG.Impl.MlDsa.X86_64.Message.Arg} (hok : (VG.Proof.MlDsa.X86_64.Message.absArgs p src len pos).all Arg.ok = true)
    {dp : Addr} {n q : Nat} (hdp : src.val t = dp) (hn : len.val t = BitVec.ofNat 64 n)
    (hq : pos.val t = BitVec.ofNat 64 q) (hql : q < 136) (hnl : n < 2 ^ 64)
    (hin : ∃ R ∈ L.rd ++ L.FR :: L.wr, Within ⟨dp, n⟩ R)
    (dS : Region.Disjoint ⟨dp, n⟩ ⟨L.ST, 200⟩) (dK : Region.Disjoint ⟨dp, n⟩ ⟨L.KS, 640⟩)
    (kD : Region.Disjoint ⟨L.B, 40⟩ ⟨dp, n⟩) :
    WP isa (VG.Impl.MlDsa.X86_64.Message.kabs p src len pos) t fun t' => VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ t' ∧
      Frame [⟨L.ST, 200⟩, ⟨L.KS, 640⟩, ⟨L.B, 40⟩] t.mem t'.mem ∧
      (∀ msg, Repr t.mem L.ST 136 msg → q = msg.length % 136 →
        Repr t'.mem L.ST 136 (msg ++ bytesAt t.mem dp n)) ∧ (t'.gpr .rax).toNat = (q + n) % 136 := by
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Message.setArgs_ok _ hok t hc.frOk) fun t1 ⟨⟨hA, hm, hx⟩, k⟩ => ?_)
  have hc1 : VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ t1 := hc.regs k.2.1 k.2.2 hm hx fun r hr => k.gpr (VG.Proof.MlDsa.X86_64.Message.argRegs_cs r hr)
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := VG.Proof.MlDsa.X86_64.Message.argsIn6 hA
  rw [hc.aSt p hE] at e1
  rw [hc.aKs p hE] at e6
  rw [hdp] at e4
  rw [hn] at e5
  rw [hq] at e3
  have ha : AbsorbArgs t1 L.ST dp L.KS 136 q n :=
    ⟨e1, e2, e3, e4, e5, e6, by decide, hql, hnl, VG.Proof.MlDsa.X86_64.Message.st_ks, dS, dK, VG.Proof.MlDsa.X86_64.Message.k16 hc1 (VG.Proof.MlDsa.X86_64.Message.k_st hL), VG.Proof.MlDsa.X86_64.Message.k16 hc1 kD,
      VG.Proof.MlDsa.X86_64.Message.k16 hc1 (VG.Proof.MlDsa.X86_64.Message.k_ks hL)⟩
  refine VG.Proof.MlDsa.X86_64.Message.call_ok hL Proof.Sha3.X86_64.Stream.Absorb.absorb_correct absorb_nosp (by rw [absorb_depth]; decide)
    hc1 (absorb_pre ha) (by simpa using hin) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [VG.Proof.MlDsa.X86_64.Message.w_st, VG.Proof.MlDsa.X86_64.Message.w_ks])
    fun s' hc' hf _ ⟨s₂, hm₂, hg₂, hpost, hrax⟩ => ?_
  have hn' := ofNat_toNat' hnl
  have hq' := ofNat_toNat' (show q < 2 ^ 64 by omega)
  simp only [State.withRegions_mem, VG.Proof.MlDsa.X86_64.Message.gpr_ce t1 _ _ (by decide : Reg.rdi ≠ .rsp),
    VG.Proof.MlDsa.X86_64.Message.gpr_ce t1 _ _ (by decide : Reg.rsi ≠ .rsp), VG.Proof.MlDsa.X86_64.Message.gpr_ce t1 _ _ (by decide : Reg.rdx ≠ .rsp),
    VG.Proof.MlDsa.X86_64.Message.gpr_ce t1 _ _ (by decide : Reg.rcx ≠ .rsp), VG.Proof.MlDsa.X86_64.Message.gpr_ce t1 _ _ (by decide : Reg.r8 ≠ .rsp),
    e1, e2, e3, e4, e5, hm₂, hn', hq'] at hpost hrax
  refine ⟨hc', by rw [← hm]; simpa using hf, fun msg hmsg hp => ?_, by rw [← hg₂ _ (by decide)]; exact hrax⟩
  have := hpost msg ((callEntry_repr t1 ha.k_st).mpr (hm ▸ hmsg)) hp
  rwa [callEntry_bytesAt t1 hnl ha.k_d, hm] at this

/-! ## Padding -/

/-- The arguments of a call of `vg_keccak_pad`. -/
abbrev padArgs (p : Params) (pos : VG.Impl.MlDsa.X86_64.Message.Arg) : List VG.Impl.MlDsa.X86_64.Message.Arg := [VG.Impl.MlDsa.X86_64.Message.aSt p, .imm 136, pos, .imm 0x1f, VG.Impl.MlDsa.X86_64.Message.aKs p]

theorem kpad_ok (hL : L.Ok) (hE : oE p = L.E) {t : State} (hc : VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ t)
    {pos : VG.Impl.MlDsa.X86_64.Message.Arg} (hok : (VG.Proof.MlDsa.X86_64.Message.padArgs p pos).all Arg.ok = true) {q : Nat}
    (hq : pos.val t = BitVec.ofNat 64 q) (hql : q < 136) :
    WP isa (VG.Impl.MlDsa.X86_64.Message.kpad p pos) t fun t' => VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ t' ∧
      Frame [⟨L.ST, 200⟩, ⟨L.KS, 640⟩, ⟨L.B, 40⟩] t.mem t'.mem ∧
      (∀ msg, Repr t.mem L.ST 136 msg → q = msg.length % 136 →
        stateAt t'.mem L.ST = absorb 136 (pad 136 Spec.Sha3.shakeSuffix msg)) := by
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Message.setArgs_ok _ hok t hc.frOk) fun t1 ⟨⟨hA, hm, hx⟩, k⟩ => ?_)
  have hc1 : VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ t1 := hc.regs k.2.1 k.2.2 hm hx fun r hr => k.gpr (VG.Proof.MlDsa.X86_64.Message.argRegs_cs r hr)
  obtain ⟨e1, e2, e3, e4, e5⟩ := VG.Proof.MlDsa.X86_64.Message.argsIn5 hA
  rw [hc.aSt p hE] at e1
  rw [hc.aKs p hE] at e5
  rw [hq] at e3
  have ha : PadArgs t1 L.ST L.KS 136 q :=
    ⟨e1, e2, e3, e5, by decide, hql, VG.Proof.MlDsa.X86_64.Message.st_ks, VG.Proof.MlDsa.X86_64.Message.k16 hc1 (VG.Proof.MlDsa.X86_64.Message.k_st hL), VG.Proof.MlDsa.X86_64.Message.k16 hc1 (VG.Proof.MlDsa.X86_64.Message.k_ks hL)⟩
  refine VG.Proof.MlDsa.X86_64.Message.call_ok hL Proof.Sha3.X86_64.Stream.Pad.pad_correct pad_nosp (by rw [pad_depth]; decide)
    hc1 (pad_pre ha) (by simp) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [VG.Proof.MlDsa.X86_64.Message.w_st, VG.Proof.MlDsa.X86_64.Message.w_ks])
    fun s' hc' hf _ ⟨s₂, hm₂, _, hpost⟩ => ?_
  have hq' := ofNat_toNat' (show q < 2 ^ 64 by omega)
  simp only [Proof.Sha3.padX86_64, State.withRegions_mem, VG.Proof.MlDsa.X86_64.Message.gpr_ce t1 _ _ (by decide : Reg.rdi ≠ .rsp),
    VG.Proof.MlDsa.X86_64.Message.gpr_ce t1 _ _ (by decide : Reg.rsi ≠ .rsp), VG.Proof.MlDsa.X86_64.Message.gpr_ce t1 _ _ (by decide : Reg.rdx ≠ .rsp),
    VG.Proof.MlDsa.X86_64.Message.gpr_ce t1 _ _ (by decide : Reg.rcx ≠ .rsp), e1, e2, e3, e4, hm₂, hq'] at hpost
  refine ⟨hc', by rw [← hm]; simpa using hf, fun msg hmsg hp => ?_⟩
  have := hpost msg ((callEntry_repr t1 ha.k_st).mpr (hm ▸ hmsg)) hp
  rw [this]
  rfl

/-! ## Squeezing -/

/-- The arguments of a call of `vg_keccak_squeeze`. -/
abbrev sqzArgs (p : Params) : List VG.Impl.MlDsa.X86_64.Message.Arg := [VG.Impl.MlDsa.X86_64.Message.aSt p, .imm 136, .imm 0, VG.Impl.MlDsa.X86_64.Message.aMu p, .imm 64, VG.Impl.MlDsa.X86_64.Message.aKs p]

theorem ksqz_ok (hL : L.Ok) (hE : oE p = L.E) {t : State} (hc : VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ t) :
    WP isa (VG.Impl.MlDsa.X86_64.Message.ksqz p) t fun t' => VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ t' ∧
      Frame [⟨L.ST, 200⟩, ⟨L.MU, 64⟩, ⟨L.KS, 640⟩, ⟨L.B, 40⟩] t.mem t'.mem ∧
      bytesAt t'.mem L.MU 64 = squeezeFrom 136 (stateAt t.mem L.ST) 0 64 := by
  have hok : (VG.Proof.MlDsa.X86_64.Message.sqzArgs p).all Arg.ok = true := by
    simp only [VG.Proof.MlDsa.X86_64.Message.sqzArgs, Impl.MlDsa.X86_64.Message.aSt, Impl.MlDsa.X86_64.Message.aMu,
      Impl.MlDsa.X86_64.Message.aKs, List.all_cons, List.all_nil, Arg.ok, fScr, Bool.and_true,
      Bool.and_eq_true, decide_eq_true_eq]
    have := hL.hE; omega
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Message.setArgs_ok _ hok t hc.frOk) fun t1 ⟨⟨hA, hm, hx⟩, k⟩ => ?_)
  have hc1 : VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ t1 := hc.regs k.2.1 k.2.2 hm hx fun r hr => k.gpr (VG.Proof.MlDsa.X86_64.Message.argRegs_cs r hr)
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := VG.Proof.MlDsa.X86_64.Message.argsIn6 hA
  rw [hc.aSt p hE] at e1
  rw [hc.aKs p hE] at e6
  rw [hc.aMu p hE] at e4
  have ha : SqueezeArgs t1 L.ST L.MU L.KS 136 0 64 :=
    ⟨e1, e2, e3, e4, e5, e6, by decide, by decide, by decide, VG.Proof.MlDsa.X86_64.Message.st_mu, VG.Proof.MlDsa.X86_64.Message.st_ks, VG.Proof.MlDsa.X86_64.Message.mu_ks, VG.Proof.MlDsa.X86_64.Message.k16 hc1 (VG.Proof.MlDsa.X86_64.Message.k_st hL),
      VG.Proof.MlDsa.X86_64.Message.k16 hc1 (VG.Proof.MlDsa.X86_64.Message.k_mu hL), VG.Proof.MlDsa.X86_64.Message.k16 hc1 (VG.Proof.MlDsa.X86_64.Message.k_ks hL)⟩
  refine VG.Proof.MlDsa.X86_64.Message.call_ok hL Proof.Sha3.X86_64.Stream.Squeeze.squeeze_correct squeeze_nosp
    (by rw [squeeze_depth]; decide) hc1 (squeeze_pre ha) (by simp) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [VG.Proof.MlDsa.X86_64.Message.w_st, VG.Proof.MlDsa.X86_64.Message.w_mu, VG.Proof.MlDsa.X86_64.Message.w_ks])
    fun s' hc' hf _ ⟨s₂, hm₂, _, hpost, _⟩ => ?_
  simp only [State.withRegions_mem, VG.Proof.MlDsa.X86_64.Message.gpr_ce t1 _ _ (by decide : Reg.rdi ≠ .rsp),
    VG.Proof.MlDsa.X86_64.Message.gpr_ce t1 _ _ (by decide : Reg.rsi ≠ .rsp), VG.Proof.MlDsa.X86_64.Message.gpr_ce t1 _ _ (by decide : Reg.rdx ≠ .rsp),
    VG.Proof.MlDsa.X86_64.Message.gpr_ce t1 _ _ (by decide : Reg.rcx ≠ .rsp), VG.Proof.MlDsa.X86_64.Message.gpr_ce t1 _ _ (by decide : Reg.r8 ≠ .rsp),
    e1, e2, e3, e4, e5, hm₂, Arg.val, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hpost
  refine ⟨hc', by rw [← hm]; simpa using hf, ?_⟩
  rw [hpost, callEntry_stateAt t1 ha.k_st, hm]

/-! ## `μ` -/

/-- The two bytes `0 ‖ ctx_len` of the formatted message. -/
abbrev hdrBytes (L : VG.Proof.MlDsa.X86_64.Message.Lay) : List Byte := [0, BitVec.ofNat 8 L.ctxLen.toNat]

/-- A frame of regions within `X` and the 32 bytes below the frame. -/
theorem frameX {rs : List Region} {m m' : Mem} (h : Frame rs m m')
    (hs : ∀ r ∈ rs, r = ⟨L.B, 40⟩ ∨ Within r L.XS) : Frame [L.XS, ⟨L.B, 40⟩] m m' :=
  Frame.sub h fun r hr => by
    rcases hs r hr with rfl | hw
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, hw.sub⟩

theorem absOk (hL : L.Ok) (hE : oE p = L.E) {src len pos : VG.Impl.MlDsa.X86_64.Message.Arg} (h1 : src.ok = true) (h2 : len.ok = true)
    (h3 : pos.ok = true) : (VG.Proof.MlDsa.X86_64.Message.absArgs p src len pos).all Arg.ok = true := by
  have := hL.hE
  simp only [VG.Proof.MlDsa.X86_64.Message.absArgs, List.all_cons, List.all_nil, h1, h2, h3, Bool.and_true, Bool.true_and]
  simp only [Impl.MlDsa.X86_64.Message.aSt, Impl.MlDsa.X86_64.Message.aKs, Arg.ok, fScr, Bool.and_eq_true,
    decide_eq_true_eq, hE]
  omega

theorem ofNat_toNat_self (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt]

theorem ofNat_toNat_eq {x : BitVec 64} {n : Nat} (h : x.toNat = n) : x = BitVec.ofNat 64 n := by
  subst h; exact (VG.Proof.MlDsa.X86_64.Message.ofNat_toNat_self x).symm

theorem muHash_ok (hL : L.Ok) (hE : oE p = L.E) {t : State} (hc : VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ t)
    {tr : VG.Impl.MlDsa.X86_64.Message.Arg} (hok : tr.ok = true) {trp : Addr}
    (htr : ∀ t', VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ t' → tr.val t' = trp)
    (hin : ∃ R ∈ L.rd ++ L.FR :: L.wr, Within ⟨trp, 64⟩ R)
    (dS : Region.Disjoint ⟨trp, 64⟩ ⟨L.ST, 200⟩) (dK : Region.Disjoint ⟨trp, 64⟩ ⟨L.KS, 640⟩)
    (kD : Region.Disjoint ⟨L.B, 40⟩ ⟨trp, 64⟩) :
    WP isa (muHash p tr) t fun t' => VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ t' ∧ Frame [L.XS, ⟨L.B, 40⟩] t.mem t'.mem ∧
      bytesAt t'.mem L.MU 64 = Spec.MlDsa.H (bytesAt t.mem trp 64 ++ VG.Proof.MlDsa.X86_64.Message.hdrBytes L ++
        bytesAt m₀ L.ctx L.ctxLen.toNat ++ bytesAt m₀ L.msg L.len.toNat) 64 := by
  have hctx := hL.ctxLt
  -- Zero the state.
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Message.zeroSt_ok hL hE hc) fun t1 ⟨hc1, hf1, hz⟩ => ?_)
  have etr : bytesAt t1.mem trp 64 = bytesAt t.mem trp 64 :=
    Proof.MlKem.bytesAt_congr fun i hi => hf1.bytes (R := ⟨trp, 64⟩) (by simpa using dS) (by show 64 ≤ 2 ^ 64; decide) hi
  have hR1 : Repr t1.mem L.ST 136 [] := Proof.MlKem.repr_nil hz
  -- `tr`.
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Message.kabs_ok hL hE hc1 (VG.Proof.MlDsa.X86_64.Message.absOk hL hE hok rfl rfl) (htr t1 hc1) rfl rfl (by decide)
    (by decide) hin dS dK kD) fun t2 ⟨hc2, hf2, hR2, hx2⟩ => ?_)
  have hR2 := hR2 [] hR1 rfl
  rw [List.nil_append, etr] at hR2
  -- `0 ‖ ctx_len`, from the frame.
  have hsp2 : Arg.sp.val t2 = L.SP := hc2.rsp
  have wfr : ∃ R ∈ L.rd ++ L.FR :: L.wr, Within ⟨L.SP, 2⟩ R := ⟨L.FR, by simp, within_base _ (by omega)⟩
  have fS : Region.Disjoint ⟨L.SP, 2⟩ ⟨L.ST, 200⟩ := by
    have := hL.stk_x (d := 40) (n := 2) (e := 0) (k := 200) (by omega) (by omega); simpa only [VG.Proof.MlDsa.X86_64.Message.x0] using this
  have fK : Region.Disjoint ⟨L.SP, 2⟩ ⟨L.KS, 640⟩ := hL.stk_x (d := 40) (n := 2) (by omega) (by omega)
  have kF : Region.Disjoint ⟨L.B, 40⟩ ⟨L.SP, 2⟩ := Offset.base_disjoint _ (by omega) (by omega)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Message.kabs_ok hL hE hc2 (VG.Proof.MlDsa.X86_64.Message.absOk hL hE rfl rfl rfl) hsp2 rfl rfl (by decide) (by decide)
    wfr fS fK kF) fun t3 ⟨hc3, hf3, hR3, hx3⟩ => ?_)
  have hR3 := hR3 _ hR2 (by rw [Proof.MlKem.bytesAt_length])
  rw [hc2.hdr] at hR3
  -- The context string.
  have hcl : (Arg.slot fCtxLen).val t3 = BitVec.ofNat 64 L.ctxLen.toNat := by
    rw [hc3.slot, fCtxLen, hc3.pCtxLen, VG.Proof.MlDsa.X86_64.Message.ofNat_toNat_self]
  have wc : ∃ R ∈ L.rd ++ L.FR :: L.wr, Within ⟨L.ctx, L.ctxLen.toNat⟩ R :=
    ⟨L.CTX, List.mem_append_left _ hL.inCtx, within_self _⟩
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Message.kabs_ok hL hE hc3 (VG.Proof.MlDsa.X86_64.Message.absOk hL hE (by decide) (by decide) (by decide))
    (by rw [hc3.slot, fCtx, hc3.pCtx]) hcl rfl (by decide) (by omega) wc
    (by have := hL.x_r hL.xCtx (e := 0) (k := 200) (by omega); simpa only [VG.Proof.MlDsa.X86_64.Message.x0] using this.symm)
    (hL.x_r hL.xCtx (e := 200) (k := 640) (by omega)).symm
    (by have := hL.stk_r hL.kCtx (d := 0) (n := 40) (by omega); simpa only [BitVec.add_zero] using this))
    fun t4 ⟨hc4, hf4, hR4, hx4⟩ => ?_)
  have hR4 := hR4 _ hR3 (by simp only [List.length_append, Proof.MlKem.bytesAt_length, List.length_cons, List.length_nil])
  rw [hc3.bytesAt_eq hL.xCtx hL.kCtx (by have := hL.nCtx; omega)] at hR4
  -- The message.
  have hln : (Arg.slot fLen).val t4 = BitVec.ofNat 64 L.len.toNat := by
    rw [hc4.slot, fLen, hc4.pLen, VG.Proof.MlDsa.X86_64.Message.ofNat_toNat_self]
  have wm : ∃ R ∈ L.rd ++ L.FR :: L.wr, Within ⟨L.msg, L.len.toNat⟩ R :=
    ⟨L.MSG, List.mem_append_left _ hL.inMsg, within_self _⟩
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Message.kabs_ok hL hE hc4 (VG.Proof.MlDsa.X86_64.Message.absOk hL hE (by decide) (by decide) rfl)
    (by rw [hc4.slot, fMsg, hc4.pMsg]) hln (VG.Proof.MlDsa.X86_64.Message.ofNat_toNat_eq hx4) (Nat.mod_lt _ (by decide))
    (by have := L.len.isLt; omega) wm
    (by have := hL.x_r hL.xMsg (e := 0) (k := 200) (by omega); simpa only [VG.Proof.MlDsa.X86_64.Message.x0] using this.symm)
    (hL.x_r hL.xMsg (e := 200) (k := 640) (by omega)).symm
    (by have := hL.stk_r hL.kMsg (d := 0) (n := 40) (by omega); simpa only [BitVec.add_zero] using this))
    fun t5 ⟨hc5, hf5, hR5, hx5⟩ => ?_)
  have hR5 := hR5 _ hR4 (by simp only [List.length_append, Proof.MlKem.bytesAt_length, List.length_cons, List.length_nil])
  rw [hc4.bytesAt_eq hL.xMsg hL.kMsg (by have := hL.nMsg; omega)] at hR5
  -- Pad and squeeze.
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Message.kpad_ok hL hE hc5 (by
      have := hL.hE
      simp only [VG.Proof.MlDsa.X86_64.Message.padArgs, Impl.MlDsa.X86_64.Message.aSt, Impl.MlDsa.X86_64.Message.aKs, List.all_cons,
        List.all_nil, Arg.ok, fScr, Bool.and_true, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq, hE]
      omega) (VG.Proof.MlDsa.X86_64.Message.ofNat_toNat_eq hx5) (Nat.mod_lt _ (by decide)))
    fun t6 ⟨hc6, hf6, hS6⟩ => ?_)
  have hS6 := hS6 _ hR5 (by simp only [List.length_append, Proof.MlKem.bytesAt_length, List.length_cons, List.length_nil]; omega)
  refine WP.mono (VG.Proof.MlDsa.X86_64.Message.ksqz_ok hL hE hc6) fun t7 ⟨hc7, hf7, hm7⟩ => ⟨hc7, ?_, ?_⟩
  · have fx : ∀ {m m' : Mem} {rs : List Region}, Frame rs m m' →
        (∀ r ∈ rs, r = ⟨L.B, 40⟩ ∨ Within r L.XS) → Frame [L.XS, ⟨L.B, 40⟩] m m' := VG.Proof.MlDsa.X86_64.Message.frameX
    have a1 := fx hf1 (by simp [VG.Proof.MlDsa.X86_64.Message.w_st])
    have a2 := fx hf2 (by simp [VG.Proof.MlDsa.X86_64.Message.w_st, VG.Proof.MlDsa.X86_64.Message.w_ks])
    have a3 := fx hf3 (by simp [VG.Proof.MlDsa.X86_64.Message.w_st, VG.Proof.MlDsa.X86_64.Message.w_ks])
    have a4 := fx hf4 (by simp [VG.Proof.MlDsa.X86_64.Message.w_st, VG.Proof.MlDsa.X86_64.Message.w_ks])
    have a5 := fx hf5 (by simp [VG.Proof.MlDsa.X86_64.Message.w_st, VG.Proof.MlDsa.X86_64.Message.w_ks])
    have a6 := fx hf6 (by simp [VG.Proof.MlDsa.X86_64.Message.w_st, VG.Proof.MlDsa.X86_64.Message.w_ks])
    have a7 := fx hf7 (by simp [VG.Proof.MlDsa.X86_64.Message.w_st, VG.Proof.MlDsa.X86_64.Message.w_ks, VG.Proof.MlDsa.X86_64.Message.w_mu])
    exact a1.trans (a2.trans (a3.trans (a4.trans (a5.trans (a6.trans a7)))))
  · rw [hm7, hS6, Spec.MlDsa.H, Proof.MlKem.shake256_eq]

/-! ## `tr = H(pk, 64)` -/

theorem trHash_ok (hL : L.Ok) (hE : oE p = L.E) (hk : L.keyLen = p.pkLen) {t : State} (hc : VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ t) :
    WP isa (trHash p) t fun t' => VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ t' ∧ Frame [L.XS, ⟨L.B, 40⟩] t.mem t'.mem ∧
      bytesAt t'.mem L.MU 64 = Spec.MlDsa.H (bytesAt m₀ L.key L.keyLen) 64 := by
  have hkl := hL.hKey.2
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Message.zeroSt_ok hL hE hc) fun t1 ⟨hc1, hf1, hz⟩ => ?_)
  have hR1 : Repr t1.mem L.ST 136 [] := Proof.MlKem.repr_nil hz
  have wk : ∃ R ∈ L.rd ++ L.FR :: L.wr, Within ⟨L.key, L.keyLen⟩ R :=
    ⟨L.KEY, List.mem_append_left _ hL.inKey, within_self _⟩
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Message.kabs_ok hL hE hc1 (VG.Proof.MlDsa.X86_64.Message.absOk hL hE (by decide) (by simp [Arg.ok]; omega) rfl)
    (by rw [hc1.slot, fKey, hc1.pKey]) (by rw [hk]; rfl) rfl (by decide) (by omega) wk
    (by have := hL.x_r hL.xKey (e := 0) (k := 200) (by omega); simpa only [VG.Proof.MlDsa.X86_64.Message.x0] using this.symm)
    (hL.x_r hL.xKey (e := 200) (k := 640) (by omega)).symm
    (by have := hL.stk_r hL.kKey (d := 0) (n := 40) (by omega); simpa only [BitVec.add_zero] using this))
    fun t2 ⟨hc2, hf2, hR2, _⟩ => ?_)
  have hR2 := hR2 [] hR1 rfl
  rw [List.nil_append, hc1.bytesAt_eq hL.xKey hL.kKey (by have := hL.nKey; omega)] at hR2
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Message.kpad_ok hL hE hc2 (q := p.pkLen % 136) (by
      have := hL.hE
      simp only [VG.Proof.MlDsa.X86_64.Message.padArgs, Impl.MlDsa.X86_64.Message.aSt, Impl.MlDsa.X86_64.Message.aKs, List.all_cons,
        List.all_nil, Arg.ok, fScr, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq, hE]
      omega) rfl (Nat.mod_lt _ (by decide)))
    fun t3 ⟨hc3, hf3, hS3⟩ => ?_)
  have hS3 := hS3 _ hR2 (by rw [Proof.MlKem.bytesAt_length, hk])
  refine WP.mono (VG.Proof.MlDsa.X86_64.Message.ksqz_ok hL hE hc3) fun t4 ⟨hc4, hf4, hm4⟩ => ⟨hc4, ?_, ?_⟩
  · have a1 := VG.Proof.MlDsa.X86_64.Message.frameX (L := L) hf1 (by simp [VG.Proof.MlDsa.X86_64.Message.w_st])
    have a2 := VG.Proof.MlDsa.X86_64.Message.frameX (L := L) hf2 (by simp [VG.Proof.MlDsa.X86_64.Message.w_st, VG.Proof.MlDsa.X86_64.Message.w_ks])
    have a3 := VG.Proof.MlDsa.X86_64.Message.frameX (L := L) hf3 (by simp [VG.Proof.MlDsa.X86_64.Message.w_st, VG.Proof.MlDsa.X86_64.Message.w_ks])
    have a4 := VG.Proof.MlDsa.X86_64.Message.frameX (L := L) hf4 (by simp [VG.Proof.MlDsa.X86_64.Message.w_st, VG.Proof.MlDsa.X86_64.Message.w_ks, VG.Proof.MlDsa.X86_64.Message.w_mu])
    exact a1.trans (a2.trans (a3.trans a4))
  · rw [hm4, hS3, Spec.MlDsa.H, Proof.MlKem.shake256_eq]

end

end VG.Proof.MlDsa.X86_64.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Message.Entry`. -/
section

/-!
# ML-DSA on x86-64, `sign_message` and `verify_message`: the frame

Untrusted: everything here is checked by Lean. The frame's push of nine
registers (`rs`) holding the key, `msg`, `msg_len`, `ctx`, `ctx_len`, `sig`,
`rnd`, `scratch` and 0, then the store of `ctx_len` after the 0, give `Ctx`
(`entry_ok`); a frame whose body keeps `Ctx` returns with the permissions,
`rsp` and callee-saved registers of entry (`frame_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Message

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Message
open VG.Proof.MlDsa.Message
open VG.Spec.Sha3 (bytesAt)

/-- The values the frame's push stores, the first at `SP + 64`. -/
def Lay.vals (L : VG.Proof.MlDsa.X86_64.Message.Lay) : List (BitVec 64) := [L.key, L.msg, L.len, L.ctx, L.ctxLen, L.sig, L.rnd, L.scr, 0]

theorem push_slot (B : Addr) (j : Nat) (hj : j < 9) :
    B + BitVec.ofNat 64 112 - BitVec.ofNat 64 (8 * (j + 1)) = B + BitVec.ofNat 64 40 + BitVec.ofNat 64 (64 - 8 * j) := by
  rw [add_add, Offset.sub_ofNat_eq _ (a := 8 * (j + 1)) (b := 112) (by omega), BitVec.add_sub_cancel]
  congr 2; omega

theorem push_base (B : Addr) : B + BitVec.ofNat 64 112 - BitVec.ofNat 64 (8 * 9) = B + BitVec.ofNat 64 40 := by
  have := VG.Proof.MlDsa.X86_64.Message.push_slot B 8 (by omega); simpa using this

theorem setWidth8 (x : BitVec 64) (_h : x.toNat < 256) : x.setWidth 8 = BitVec.ofNat 8 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

/-- After the push of the registers `rs` holding `L.vals` and the store of
`ctx_len`: `Ctx`. -/
theorem entry_ok {L : VG.Proof.MlDsa.X86_64.Message.Lay} (hL : L.Ok) {rs : List Reg} (hlen : rs.length = 9) (hrs : .rsp ∉ rs) {s : State}
    (hsp : s.gpr .rsp = L.B + BitVec.ofNat 64 112) (hrd : s.rd = L.rd) (hwr : s.wr = L.wr)
    (hv : ∀ j (hj : j < 9), s.gpr (rs[j]'(by omega)) = L.vals[j]'(by simp [Lay.vals]; omega))
    (h8 : s.gpr .r8 = L.ctxLen) :
    WP isa (.block setHdr) (pushed rs s) fun t => VG.Proof.MlDsa.X86_64.Message.Ctx L s.gpr s.mxcsr s.mem t ∧
      t.wr = (pushed rs s).wr ∧ t.gpr .rsp = (pushed rs s).gpr .rsp := by
  have hn : 8 * rs.length ≤ (s.gpr .rsp).toNat := by
    rw [hsp, hlen, BitVec.toNat_add, BitVec.toNat_ofNat]
    have := hL.nB
    rw [Nat.mod_eq_of_lt (a := 112) (by omega), Nat.mod_eq_of_lt this]; omega
  obtain ⟨hf, hw⟩ := pushRegs_mem s rs hrs hn
  have hslot : ∀ j (hj : j < 9), (pushed rs s).mem.readW (L.SP + BitVec.ofNat 64 (64 - 8 * j)) 64 =
      L.vals[j]'(by simp [Lay.vals]; omega) := fun j hj => by
    rw [← hv j hj, ← hw j (by omega), hsp, VG.Proof.MlDsa.X86_64.Message.push_slot _ j hj]; rfl
  have hrsp : (pushed rs s).gpr .rsp = L.SP := by rw [pushed_rsp, hsp, hlen, VG.Proof.MlDsa.X86_64.Message.push_base]
  have hwr' : (pushed rs s).wr = L.FR :: L.wr := by rw [pushed_wr, hsp, hlen, VG.Proof.MlDsa.X86_64.Message.push_base, hwr]
  have hin : InRegions (pushed rs s).wr (L.SP + BitVec.ofNat 64 1) 1 :=
    ⟨L.FR, by rw [hwr']; simp, Offset.contains_base _ (by omega) (by omega)⟩
  have h8' : (pushed rs s).gpr .r8 = L.ctxLen := by rw [pushed_gpr _ _ (by decide), h8]
  apply WP.of_runBlock
  simp only [setHdr, fHdr, runBlock_cons, runStep_some, runBlock_nil, exec, State.store8, VG.Proof.MlDsa.X86_64.Message.ea_stk, hrsp,
    Nat.reduceAdd, hin, ite_true, Option.some.injEq, exists_eq_left', h8',
    VG.Proof.MlDsa.X86_64.Message.setWidth8 _ hL.ctxLt]
  -- The memory after the store.
  generalize hm : (pushed rs s).mem.writeW (L.SP + BitVec.ofNat 64 1) (BitVec.ofNat 8 L.ctxLen.toNat) = m'
  have hsep : ∀ j (hj : j < 8), m'.readW (L.SP + BitVec.ofNat 64 (64 - 8 * j)) 64 =
      (pushed rs s).mem.readW (L.SP + BitVec.ofNat 64 (64 - 8 * j)) 64 := fun j hj => by
    rw [← hm]
    exact Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)
  refine ⟨⟨by simp [hrd], hwr', hrsp, fun r hr hr' => pushed_gpr _ _ hr', by simp,
    (hsep 7 (by omega)).trans (hslot 7 (by omega)), (hsep 6 (by omega)).trans (hslot 6 (by omega)),
    (hsep 5 (by omega)).trans (hslot 5 (by omega)), (hsep 4 (by omega)).trans (hslot 4 (by omega)),
    (hsep 3 (by omega)).trans (hslot 3 (by omega)), (hsep 2 (by omega)).trans (hslot 2 (by omega)),
    (hsep 1 (by omega)).trans (hslot 1 (by omega)), (hsep 0 (by omega)).trans (hslot 0 (by omega)), ?_, ?_⟩,
    trivial, trivial⟩
  · -- The two bytes: the low byte of the pushed 0, and `ctx_len`.
    have h0 := hslot 8 (by omega)
    simp only [Lay.vals, Nat.reduceMul, Nat.sub_self, BitVec.add_zero] at h0
    have b0 : (pushed rs s).mem L.SP = 0 := by
      have := Mem.extractLsb'_read (pushed rs s).mem L.SP (n := 8) (j := 0) (by omega)
      simp only [BitVec.add_zero, Nat.mul_zero] at this
      rw [← this]
      have e : (pushed rs s).mem.read L.SP 8 = (pushed rs s).mem.readW L.SP 64 := by
        simp only [Mem.readW]; rfl
      rw [e, h0]; rfl
    rw [← hm]
    simp only [bytesAt, List.range, List.range.loop, List.map_cons, List.map_nil, BitVec.add_zero]
    refine List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, rfl⟩⟩
    · rw [Mem.writeW, Mem.write_apply (by
        rw [Offset.toNat_sub_add _ _ (by decide), BitVec.sub_self]; simp)]
      exact b0
    · simp only [Mem.writeW, Mem.write, BitVec.sub_self, BitVec.toNat_zero, Nat.reduceDiv, Nat.lt_add_one,
        ite_true]
      ext i hi
      simp
  · show Frame [L.XS, L.STK] s.mem m'
    rw [← hm]
    have hf1 : Frame [L.STK] s.mem (pushed rs s).mem := by
      refine Frame.sub hf fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr
      refine ⟨L.STK, by simp, ?_⟩
      rw [hsp, hlen, VG.Proof.MlDsa.X86_64.Message.push_base]
      exact Offset.sub_base _ (by omega)
    have hf2 : Frame [L.STK] s.mem ((pushed rs s).mem.writeW (L.SP + 1#64) (BitVec.ofNat 8 L.ctxLen.toNat)) :=
      hf1.writeW (List.mem_singleton_self _) _ (by
        rw [Lay.SP, add_add]; exact Offset.contains_base _ (by omega) (by omega))
    exact hf2.mono fun r hr => by simp at hr ⊢; exact .inr hr

end VG.Proof.MlDsa.X86_64.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Message.Rel`. -/
section

/-!
# ML-DSA on x86-64, `sign_message` and `verify_message`: relating two runs

Untrusted: everything here is checked by Lean. Two runs between the frame's
push and pop with the same layout, each in a `Ctx` state, whose inputs agree
on what the contract makes public (`I`), and each satisfying `Φ` (`Two`).
Blocks whose addresses are `rsp` plus offsets leak the same in both runs
(`block_rsp_tr`, and so the moves of a call's arguments, `setArgs_tr`); a
call whose callee's public data agree in both runs (`call_tr`); and what
each run satisfies by correctness carries over (`two_wp`).
-/

namespace VG.Proof.MlDsa.X86_64.Message

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.X86_64 (Keep RelCT.postDep)

/-! ## Blocks addressed from `rsp` -/

/-- An instruction whose addresses are a function of `rsp`, which it keeps. -/
def SpOnly (i : Instr) : Prop :=
  (∀ s₁ s₂ : State, s₁.gpr .rsp = s₂.gpr .rsp → isa.addrs i s₁ = isa.addrs i s₂) ∧ Taint.clobbers i .rsp = false

theorem execBlock_rsp_tr : ∀ {is : List Instr}, (∀ i ∈ is, VG.Proof.MlDsa.X86_64.Message.SpOnly i) →
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
      rw [VG.X86_64.exec_gpr hi.2 ha₁, VG.X86_64.exec_gpr hi.2 ha₂, hsp]
    obtain ⟨ht, hs⟩ := VG.Proof.MlDsa.X86_64.Message.execBlock_rsp_tr (fun j hj => h j (List.mem_cons_of_mem _ hj)) hsp' eb₁ eb₂
    exact ⟨by rw [show addrs i s₁ = addrs i s₂ from hi.1 _ _ hsp, ht], hs⟩

theorem block_rsp_tr {is : List Instr} (h : ∀ i ∈ is, VG.Proof.MlDsa.X86_64.Message.SpOnly i) {P : State → State → Prop}
    (hp : ∀ a b, P a b → a.gpr .rsp = b.gpr .rsp) : RelCT isa P (.block is) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hP e₁ e₂
  rw [Exec.block_iff] at e₁ e₂
  exact ⟨(VG.Proof.MlDsa.X86_64.Message.execBlock_rsp_tr h (hp _ _ hP) e₁ e₂).1, trivial⟩

theorem arg_spOnly (d : Reg) (hd : d ≠ .rsp) (a : VG.Impl.MlDsa.X86_64.Message.Arg) : ∀ i ∈ a.mov d, VG.Proof.MlDsa.X86_64.Message.SpOnly i := by
  intro i hi
  cases a <;> simp only [Arg.mov, List.mem_cons, List.not_mem_nil, or_false] at hi <;>
    rcases hi with rfl | rfl <;>
    exact ⟨fun s₁ s₂ h => by simp [addrs, srcAddrs, State.ea, VG.Impl.MlDsa.X86_64.Message.stk, h],
      by cases d <;> simp_all [Taint.clobbers, Taint.dstOf]⟩

theorem setArgs_spOnly (as : List VG.Impl.MlDsa.X86_64.Message.Arg) : ∀ i ∈ setArgs as, VG.Proof.MlDsa.X86_64.Message.SpOnly i := by
  intro i hi
  simp only [setArgs, List.mem_flatMap] at hi
  obtain ⟨⟨d, a⟩, hm, hi⟩ := hi
  have hd : d ∈ argRegs6 := (List.of_mem_zip hm).1
  exact VG.Proof.MlDsa.X86_64.Message.arg_spOnly d (fun e => by subst e; revert hd; decide) a i hi

/-! ## Runs related through their entry states -/

/-- Two runs whose states are related to entry states `x`, `y` by `A`, with
`P x y`. -/
def Ghost (P A : State → State → Prop) (a b : State) : Prop := ∃ x y, P x y ∧ A x a ∧ A y b

/-- What each run satisfies by correctness, from its entry state, carries over. -/
theorem ghost_step {P A B : State → State → Prop} {c : Prog isa}
    (hct : RelCT isa (VG.Proof.MlDsa.X86_64.Message.Ghost P A) c fun _ _ => True)
    (hw : ∀ x y a b, P x y → A x a → A y b → WP isa c a (B x) ∧ WP isa c b (B y)) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Message.Ghost P A) c (VG.Proof.MlDsa.X86_64.Message.Ghost P B) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨x, y, hxy, a₁, a₂⟩ := hp
  obtain ⟨⟨_, u₁, x₁, y₁⟩, ⟨_, u₂, x₂, y₂⟩⟩ := hw x y s₁ s₂ hxy a₁ a₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, x, y, hxy, y₁, y₂⟩

/-! ## Two runs -/

/-- Two runs with the layout `L`, inputs related by `I`, each satisfying `Φ`. -/
def Two (I : VG.Proof.MlDsa.X86_64.Message.Lay → Mem → Mem → Prop) (Φ : VG.Proof.MlDsa.X86_64.Message.Lay → Mem → State → Prop) (a b : State) : Prop :=
  ∃ (L : VG.Proof.MlDsa.X86_64.Message.Lay) (g₁ g₂ : Reg → BitVec 64) (mx₁ mx₂ : BitVec 32) (m₁ m₂ : Mem), L.Ok ∧ I L m₁ m₂ ∧
    VG.Proof.MlDsa.X86_64.Message.Ctx L g₁ mx₁ m₁ a ∧ VG.Proof.MlDsa.X86_64.Message.Ctx L g₂ mx₂ m₂ b ∧ Φ L m₁ a ∧ Φ L m₂ b

section
variable {I : VG.Proof.MlDsa.X86_64.Message.Lay → Mem → Mem → Prop}

theorem Two.rsp {Φ : VG.Proof.MlDsa.X86_64.Message.Lay → Mem → State → Prop} {a b : State} (h : VG.Proof.MlDsa.X86_64.Message.Two I Φ a b) : a.gpr .rsp = b.gpr .rsp :=
  let ⟨_, _, _, _, _, _, _, _, _, c₁, c₂, _, _⟩ := h; c₁.rsp.trans c₂.rsp.symm

theorem two_wp {c : Prog isa} {Φ Ψ : VG.Proof.MlDsa.X86_64.Message.Lay → Mem → State → Prop}
    (hct : RelCT isa (VG.Proof.MlDsa.X86_64.Message.Two I Φ) c fun _ _ => True)
    (hw : ∀ (L : VG.Proof.MlDsa.X86_64.Message.Lay) g mx m₀ (t : State), L.Ok → VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ t → Φ L m₀ t →
      WP isa c t fun t' => VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (VG.Proof.MlDsa.X86_64.Message.Two I Φ) c (VG.Proof.MlDsa.X86_64.Message.Two I Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨L, g₁, g₂, mx₁, mx₂, m₁, m₂, hL, hi, c₁, c₂, f₁, f₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw L g₁ mx₁ m₁ s₁ hL c₁ f₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw L g₂ mx₂ m₂ s₂ hL c₂ f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, L, g₁, g₂, mx₁, mx₂, m₁, m₂, hL, hi, y₁.1, y₂.1, y₁.2, y₂.2⟩

theorem two_mono {Φ Ψ : VG.Proof.MlDsa.X86_64.Message.Lay → Mem → State → Prop} (h : ∀ L m t, Φ L m t → Ψ L m t) {a b : State}
    (hp : VG.Proof.MlDsa.X86_64.Message.Two I Φ a b) : VG.Proof.MlDsa.X86_64.Message.Two I Ψ a b :=
  let ⟨L, g₁, g₂, mx₁, mx₂, m₁, m₂, hL, hi, c₁, c₂, f₁, f₂⟩ := hp
  ⟨L, g₁, g₂, mx₁, mx₂, m₁, m₂, hL, hi, c₁, c₂, h _ _ _ f₁, h _ _ _ f₂⟩

/-- What the moves of the arguments `as` leave. -/
abbrev Moved (as : List VG.Impl.MlDsa.X86_64.Message.Arg) (t t1 : State) : Prop :=
  (VG.Proof.MlDsa.X86_64.Message.ArgsIn as t t1 ∧ t1.mem = t.mem ∧ t1.mxcsr = t.mxcsr) ∧ Keep VG.Proof.MlDsa.X86_64.Message.argRegs t t1

/-- A call after the moves of its arguments, of verified code whose public
data agree in both runs. -/
theorem call_tr {Φ : VG.Proof.MlDsa.X86_64.Message.Lay → Mem → State → Prop} {as : List VG.Impl.MlDsa.X86_64.Message.Arg} (hok : as.all Arg.ok = true) {n : String}
    {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (rd wr : VG.Proof.MlDsa.X86_64.Message.Lay → List Region)
    (hpre : ∀ (L : VG.Proof.MlDsa.X86_64.Message.Lay) g mx m₀ (t t1 : State), L.Ok → VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ t → Φ L m₀ t → VG.Proof.MlDsa.X86_64.Message.Moved as t t1 →
      k.pre (t1.callEntry.withRegions (rd L) (wr L)))
    (hpub : ∀ (L : VG.Proof.MlDsa.X86_64.Message.Lay) g₁ g₂ mx₁ mx₂ m₁ m₂ (a b a1 b1 : State), L.Ok → I L m₁ m₂ → VG.Proof.MlDsa.X86_64.Message.Ctx L g₁ mx₁ m₁ a →
      VG.Proof.MlDsa.X86_64.Message.Ctx L g₂ mx₂ m₂ b → Φ L m₁ a → Φ L m₂ b → VG.Proof.MlDsa.X86_64.Message.Moved as a a1 → VG.Proof.MlDsa.X86_64.Message.Moved as b b1 →
      k.pub (a1.callEntry.withRegions (rd L) (wr L)) (b1.callEntry.withRegions (rd L) (wr L)))
    (hcov : ∀ (L : VG.Proof.MlDsa.X86_64.Message.Lay) g mx m₀ (t : State), L.Ok → VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ t → Φ L m₀ t →
      (∀ r ∈ rd L, ∃ R ∈ L.rd ++ L.FR :: L.wr, Within r R) ∧ (∀ r ∈ wr L, ∃ R ∈ L.wr, Within r R)) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Message.Two I Φ) (callA n c as) fun _ _ => True := by
  refine RelCT.seq (RelCT.postDep (Q := fun a1 b1 => ∃ a b, VG.Proof.MlDsa.X86_64.Message.Two I Φ a b ∧ VG.Proof.MlDsa.X86_64.Message.Moved as a a1 ∧ VG.Proof.MlDsa.X86_64.Message.Moved as b b1)
    (VG.Proof.MlDsa.X86_64.Message.block_rsp_tr (VG.Proof.MlDsa.X86_64.Message.setArgs_spOnly as) fun _ _ h => h.rsp)
    (fun x y ⟨_, _, _, _, _, _, _, _, _, c₁, c₂, _, _⟩ =>
      ⟨VG.Proof.MlDsa.X86_64.Message.setArgs_ok as hok x c₁.frOk, VG.Proof.MlDsa.X86_64.Message.setArgs_ok as hok y c₂.frOk⟩)
    fun x y x1 y1 hp f₁ f₂ => ⟨x, y, hp, f₁, f₂⟩) ?_
  refine RelCT.callEx hv hct fun a1 b1 ⟨a, b, hp, f₁, f₂⟩ => ?_
  obtain ⟨L, g₁, g₂, mx₁, mx₂, m₁, m₂, hL, hi, c₁, c₂, φ₁, φ₂⟩ := hp
  obtain ⟨hr, hw⟩ := hcov L g₁ mx₁ m₁ a hL c₁ φ₁
  have cov : ∀ {t t1 : State} {g mx m₀}, VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ t → VG.Proof.MlDsa.X86_64.Message.Moved as t t1 →
      Covers (rd L ++ wr L) (t1.rd ++ t1.wr) ∧ Covers (wr L) t1.wr := fun hc f => by
    rw [f.2.2.1, f.2.2.2, hc.rd, hc.wr]
    refine ⟨VG.Proof.MlDsa.X86_64.Message.covers_of_within fun r hr' => ?_, VG.Proof.MlDsa.X86_64.Message.covers_of_within fun r hr' => ?_⟩
    · rcases List.mem_append.mp hr' with h' | h'
      · exact hr r h'
      · obtain ⟨R, hR, hW⟩ := hw r h'
        exact ⟨R, by simp [hR], hW⟩
    · obtain ⟨R, hR, hW⟩ := hw r hr'
      exact ⟨R, List.mem_cons_of_mem _ hR, hW⟩
  exact ⟨rd L, wr L, rd L, wr L, hpre L g₁ mx₁ m₁ a a1 hL c₁ φ₁ f₁, hpre L g₂ mx₂ m₂ b b1 hL c₂ φ₂ f₂,
    hpub L g₁ g₂ mx₁ mx₂ m₁ m₂ a b a1 b1 hL hi c₁ c₂ φ₁ φ₂ f₁ f₂, (cov c₁ f₁).1, (cov c₁ f₁).2,
    (cov c₂ f₂).1, (cov c₂ f₂).2,
    by rw [f₁.2.gpr (by decide), f₂.2.gpr (by decide), c₁.rsp, c₂.rsp]⟩

end

end VG.Proof.MlDsa.X86_64.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Message.HashCT`. -/
section

/-!
# ML-DSA on x86-64, `sign_message` and `verify_message`: SHAKE256 leaks only the layout

Untrusted: everything here is checked by Lean. Two runs (`Two`) of the
zeroing of the Keccak state and of the calls of the sponge functions, whose
arguments are the same in both runs (functions of the layout), leak the
same (`zeroSt_tr`, `kabs_tr`, `kpad_tr`, `ksqz_tr`); and so do `muHash` and
`trHash` (`muHash_tr`, `trHash_tr`).
-/

namespace VG.Proof.MlDsa.X86_64.Message

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.X86_64 (Keep AbsorbArgs PadArgs SqueezeArgs absorb_pre pad_pre squeeze_pre absorb_nosp
  pad_nosp squeeze_nosp absorb_depth pad_depth squeeze_depth)
open VG.Spec.MlDsa (Params)

section
variable {p : Params} {I : VG.Proof.MlDsa.X86_64.Message.Lay → Mem → Mem → Prop}

/-- The 1 KiB of the external functions is where the code of `p` puts it. -/
abbrev EOk (p : Params) (L : VG.Proof.MlDsa.X86_64.Message.Lay) : Prop := oE p = L.E

/-! ## Zeroing the state -/

theorem zeroSt_tr {Φ : VG.Proof.MlDsa.X86_64.Message.Lay → Mem → State → Prop} (hΦ : ∀ L m t, Φ L m t → VG.Proof.MlDsa.X86_64.Message.EOk p L) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Message.Two I Φ) (VG.Impl.MlDsa.X86_64.Message.zeroSt p) fun _ _ => True := by
  have h1 := VG.Proof.MlDsa.X86_64.Message.two_wp (I := I) (Φ := Φ) (Ψ := fun L _ t => t.gpr .rdi = L.ST) (c := .block ((VG.Impl.MlDsa.X86_64.Message.aSt p).mov .rdi))
    (VG.Proof.MlDsa.X86_64.Message.block_rsp_tr (VG.Proof.MlDsa.X86_64.Message.arg_spOnly .rdi (by decide) _) fun _ _ h => h.rsp) fun L g mx m₀ t hL hc hφ => by
      have hok : (VG.Impl.MlDsa.X86_64.Message.aSt p).ok = true := by
        simp only [Impl.MlDsa.X86_64.Message.aSt, Arg.ok, fScr, Bool.and_eq_true, decide_eq_true_eq]
        have := hL.hE; rw [hΦ L m₀ t hφ]; omega
      refine WP.mono (Arg.mov_ok .rdi (VG.Impl.MlDsa.X86_64.Message.aSt p) hok (by decide) t hc.frOk) fun t1 ⟨⟨h1, hm1, hx1⟩, k1⟩ =>
        ⟨hc.regs k1.2.1 k1.2.2 hm1 hx1 fun r hr => k1.gpr (by
          simp only [List.mem_singleton]; exact VG.Proof.MlDsa.X86_64.Message.ne_cs hr (by decide)), by rw [h1, hc.aSt p (hΦ L m₀ t hφ)]⟩
  refine RelCT.seq h1 (RelCT.taint (A := taint) (Taint.ofRegs [.rsp, .rdi]) (fun a b hab => ?_) (by taint_decide))
  obtain ⟨L, _, _, _, _, _, _, _, _, c₁, c₂, f₁, f₂⟩ := hab
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [c₁.rsp, c₂.rsp]
  · rw [f₁, f₂]

/-! ## The sponge functions -/

/-- The arguments of a call of `vg_keccak_absorb`, after the moves. -/
theorem kabsArgs {L : VG.Proof.MlDsa.X86_64.Message.Lay} (hL : L.Ok) (hE : VG.Proof.MlDsa.X86_64.Message.EOk p L) {g mx m₀} {t t1 : State} (hc : VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ t)
    {src len pos : VG.Impl.MlDsa.X86_64.Message.Arg} (hm : VG.Proof.MlDsa.X86_64.Message.Moved (VG.Proof.MlDsa.X86_64.Message.absArgs p src len pos) t t1) {dp : Addr} {n q : Nat}
    (hdp : src.val t = dp) (hn : len.val t = BitVec.ofNat 64 n) (hq : pos.val t = BitVec.ofNat 64 q)
    (hql : q < 136) (hnl : n < 2 ^ 64) (dS : Region.Disjoint ⟨dp, n⟩ ⟨L.ST, 200⟩)
    (dK : Region.Disjoint ⟨dp, n⟩ ⟨L.KS, 640⟩) (kD : Region.Disjoint ⟨L.B, 40⟩ ⟨dp, n⟩) :
    AbsorbArgs t1 L.ST dp L.KS 136 q n := by
  have hc1 : VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ t1 := hc.regs hm.2.2.1 hm.2.2.2 hm.1.2.1 hm.1.2.2 fun r hr => hm.2.gpr (VG.Proof.MlDsa.X86_64.Message.argRegs_cs r hr)
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := VG.Proof.MlDsa.X86_64.Message.argsIn6 hm.1.1
  rw [hc.aSt p hE] at e1
  rw [hc.aKs p hE] at e6
  rw [hdp] at e4
  rw [hn] at e5
  rw [hq] at e3
  exact ⟨e1, e2, e3, e4, e5, e6, by decide, hql, hnl, VG.Proof.MlDsa.X86_64.Message.st_ks, dS, dK, VG.Proof.MlDsa.X86_64.Message.k16 hc1 (VG.Proof.MlDsa.X86_64.Message.k_st hL), VG.Proof.MlDsa.X86_64.Message.k16 hc1 kD,
    VG.Proof.MlDsa.X86_64.Message.k16 hc1 (VG.Proof.MlDsa.X86_64.Message.k_ks hL)⟩

/-- Two runs of a call of `vg_keccak_absorb` whose arguments are the same
functions of the layout in both. -/
theorem kabs_tr {Φ : VG.Proof.MlDsa.X86_64.Message.Lay → Mem → State → Prop} (hΦ : ∀ L m t, Φ L m t → VG.Proof.MlDsa.X86_64.Message.EOk p L) {src len pos : VG.Impl.MlDsa.X86_64.Message.Arg}
    (hok : (VG.Proof.MlDsa.X86_64.Message.absArgs p src len pos).all Arg.ok = true) (dp : VG.Proof.MlDsa.X86_64.Message.Lay → Addr) (n q : VG.Proof.MlDsa.X86_64.Message.Lay → Nat)
    (hv : ∀ (L : VG.Proof.MlDsa.X86_64.Message.Lay) g mx m (t : State), L.Ok → VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m t → Φ L m t →
      src.val t = dp L ∧ len.val t = BitVec.ofNat 64 (n L) ∧ pos.val t = BitVec.ofNat 64 (q L))
    (hs : ∀ L : VG.Proof.MlDsa.X86_64.Message.Lay, L.Ok → q L < 136 ∧ n L < 2 ^ 64 ∧ (∃ R ∈ L.rd ++ L.FR :: L.wr, Within ⟨dp L, n L⟩ R) ∧
      Region.Disjoint ⟨dp L, n L⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨dp L, n L⟩ ⟨L.KS, 640⟩ ∧
      Region.Disjoint ⟨L.B, 40⟩ ⟨dp L, n L⟩) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Message.Two I Φ) (VG.Impl.MlDsa.X86_64.Message.kabs p src len pos) fun _ _ => True := by
  have args : ∀ (L : VG.Proof.MlDsa.X86_64.Message.Lay) g mx m₀ (t t1 : State), L.Ok → VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ t → Φ L m₀ t →
      VG.Proof.MlDsa.X86_64.Message.Moved (VG.Proof.MlDsa.X86_64.Message.absArgs p src len pos) t t1 → AbsorbArgs t1 L.ST (dp L) L.KS 136 (q L) (n L) :=
    fun L g mx m₀ t t1 hL hc hφ hm => by
      obtain ⟨h1, h2, h3⟩ := hv L g mx m₀ t hL hc hφ
      obtain ⟨s1, s2, _, s4, s5, s6⟩ := hs L hL
      exact VG.Proof.MlDsa.X86_64.Message.kabsArgs hL (hΦ L m₀ t hφ) hc hm h1 h2 h3 s1 s2 s4 s5 s6
  refine VG.Proof.MlDsa.X86_64.Message.call_tr hok Proof.Sha3.X86_64.Stream.Absorb.absorb_correct
    Proof.Sha3.X86_64.Stream.Absorb.absorb_ct (fun L => [⟨dp L, n L⟩]) (fun L => [⟨L.ST, 200⟩, ⟨L.KS, 640⟩])
    (fun L g mx m₀ t t1 hL hc hφ hm => absorb_pre (args L g mx m₀ t t1 hL hc hφ hm))
    (fun L g₁ g₂ mx₁ mx₂ m₁ m₂ a b a1 b1 hL _ c₁ c₂ φ₁ φ₂ f₁ f₂ => ?_) fun L _ _ _ _ hL _ _ => ?_
  · have x := args L g₁ mx₁ m₁ a a1 hL c₁ φ₁ f₁
    have y := args L g₂ mx₂ m₂ b b1 hL c₂ φ₂ f₂
    simp only [Proof.Sha3.absorbX86_64, VG.Proof.MlDsa.X86_64.Message.gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp),
      VG.Proof.MlDsa.X86_64.Message.gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp), VG.Proof.MlDsa.X86_64.Message.gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp),
      VG.Proof.MlDsa.X86_64.Message.gpr_ce _ _ _ (by decide : Reg.rcx ≠ .rsp), VG.Proof.MlDsa.X86_64.Message.gpr_ce _ _ _ (by decide : Reg.r8 ≠ .rsp),
      VG.Proof.MlDsa.X86_64.Message.gpr_ce _ _ _ (by decide : Reg.r9 ≠ .rsp), VG.Proof.MlDsa.X86_64.Message.rsp_ce, x.rdi, x.rsi, x.rdx, x.rcx, x.r8, x.r9, y.rdi, y.rsi,
      y.rdx, y.rcx, y.r8, y.r9, f₁.2.gpr (by decide : Reg.rsp ∉ argRegs), f₂.2.gpr (by decide : Reg.rsp ∉ argRegs),
      c₁.rsp, c₂.rsp, and_self]
  · obtain ⟨_, _, hin, _, _, _⟩ := hs L hL
    obtain ⟨R, hR, hX⟩ := hL.inX
    refine ⟨fun r hr => ?_, fun r hr => ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact hin
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [⟨R, hR, w_st.trans hX⟩, ⟨R, hR, w_ks.trans hX⟩]

theorem kpad_tr {Φ : VG.Proof.MlDsa.X86_64.Message.Lay → Mem → State → Prop} (hΦ : ∀ L m t, Φ L m t → VG.Proof.MlDsa.X86_64.Message.EOk p L) {pos : VG.Impl.MlDsa.X86_64.Message.Arg}
    (hok : (VG.Proof.MlDsa.X86_64.Message.padArgs p pos).all Arg.ok = true) (q : VG.Proof.MlDsa.X86_64.Message.Lay → Nat)
    (hv : ∀ (L : VG.Proof.MlDsa.X86_64.Message.Lay) g mx m (t : State), L.Ok → VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m t → Φ L m t → pos.val t = BitVec.ofNat 64 (q L))
    (hs : ∀ L : VG.Proof.MlDsa.X86_64.Message.Lay, L.Ok → q L < 136) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Message.Two I Φ) (VG.Impl.MlDsa.X86_64.Message.kpad p pos) fun _ _ => True := by
  have args : ∀ (L : VG.Proof.MlDsa.X86_64.Message.Lay) g mx m₀ (t t1 : State), L.Ok → VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ t → Φ L m₀ t →
      VG.Proof.MlDsa.X86_64.Message.Moved (VG.Proof.MlDsa.X86_64.Message.padArgs p pos) t t1 → PadArgs t1 L.ST L.KS 136 (q L) :=
    fun L g mx m₀ t t1 hL hc hφ hm => by
      have hc1 : VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ t1 :=
        hc.regs hm.2.2.1 hm.2.2.2 hm.1.2.1 hm.1.2.2 fun r hr => hm.2.gpr (VG.Proof.MlDsa.X86_64.Message.argRegs_cs r hr)
      obtain ⟨e1, e2, e3, _, e5⟩ := VG.Proof.MlDsa.X86_64.Message.argsIn5 hm.1.1
      rw [hc.aSt p (hΦ L m₀ t hφ)] at e1
      rw [hc.aKs p (hΦ L m₀ t hφ)] at e5
      rw [hv L g mx m₀ t hL hc hφ] at e3
      exact ⟨e1, e2, e3, e5, by decide, hs L hL, VG.Proof.MlDsa.X86_64.Message.st_ks, VG.Proof.MlDsa.X86_64.Message.k16 hc1 (VG.Proof.MlDsa.X86_64.Message.k_st hL), VG.Proof.MlDsa.X86_64.Message.k16 hc1 (VG.Proof.MlDsa.X86_64.Message.k_ks hL)⟩
  refine VG.Proof.MlDsa.X86_64.Message.call_tr hok Proof.Sha3.X86_64.Stream.Pad.pad_correct Proof.Sha3.X86_64.Stream.Pad.pad_ct
    (fun _ => []) (fun L => [⟨L.ST, 200⟩, ⟨L.KS, 640⟩])
    (fun L g mx m₀ t t1 hL hc hφ hm => pad_pre (args L g mx m₀ t t1 hL hc hφ hm))
    (fun L g₁ g₂ mx₁ mx₂ m₁ m₂ a b a1 b1 hL _ c₁ c₂ φ₁ φ₂ f₁ f₂ => ?_) fun L _ _ _ _ hL _ _ => ?_
  · have x := args L g₁ mx₁ m₁ a a1 hL c₁ φ₁ f₁
    have y := args L g₂ mx₂ m₂ b b1 hL c₂ φ₂ f₂
    simp only [Proof.Sha3.padX86_64, VG.Proof.MlDsa.X86_64.Message.gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp),
      VG.Proof.MlDsa.X86_64.Message.gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp), VG.Proof.MlDsa.X86_64.Message.gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp),
      VG.Proof.MlDsa.X86_64.Message.gpr_ce _ _ _ (by decide : Reg.r8 ≠ .rsp), VG.Proof.MlDsa.X86_64.Message.rsp_ce, x.rdi, x.rsi, x.rdx, x.r8, y.rdi, y.rsi, y.rdx, y.r8,
      f₁.2.gpr (by decide : Reg.rsp ∉ argRegs), f₂.2.gpr (by decide : Reg.rsp ∉ argRegs), c₁.rsp, c₂.rsp,
      and_self]
  · obtain ⟨R, hR, hX⟩ := hL.inX
    refine ⟨fun r hr => by simp at hr, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [⟨R, hR, w_st.trans hX⟩, ⟨R, hR, w_ks.trans hX⟩]

theorem ksqz_tr {Φ : VG.Proof.MlDsa.X86_64.Message.Lay → Mem → State → Prop} (hΦ : ∀ L m t, Φ L m t → VG.Proof.MlDsa.X86_64.Message.EOk p L)
    (hok : (VG.Proof.MlDsa.X86_64.Message.sqzArgs p).all Arg.ok = true) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Message.Two I Φ) (VG.Impl.MlDsa.X86_64.Message.ksqz p) fun _ _ => True := by
  have args : ∀ (L : VG.Proof.MlDsa.X86_64.Message.Lay) g mx m₀ (t t1 : State), L.Ok → VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ t → Φ L m₀ t →
      VG.Proof.MlDsa.X86_64.Message.Moved (VG.Proof.MlDsa.X86_64.Message.sqzArgs p) t t1 → SqueezeArgs t1 L.ST L.MU L.KS 136 0 64 :=
    fun L g mx m₀ t t1 hL hc hφ hm => by
      have hc1 : VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ t1 :=
        hc.regs hm.2.2.1 hm.2.2.2 hm.1.2.1 hm.1.2.2 fun r hr => hm.2.gpr (VG.Proof.MlDsa.X86_64.Message.argRegs_cs r hr)
      obtain ⟨e1, e2, e3, e4, e5, e6⟩ := VG.Proof.MlDsa.X86_64.Message.argsIn6 hm.1.1
      rw [hc.aSt p (hΦ L m₀ t hφ)] at e1
      rw [hc.aKs p (hΦ L m₀ t hφ)] at e6
      rw [hc.aMu p (hΦ L m₀ t hφ)] at e4
      exact ⟨e1, e2, e3, e4, e5, e6, by decide, by decide, by decide, VG.Proof.MlDsa.X86_64.Message.st_mu, VG.Proof.MlDsa.X86_64.Message.st_ks, VG.Proof.MlDsa.X86_64.Message.mu_ks, VG.Proof.MlDsa.X86_64.Message.k16 hc1 (VG.Proof.MlDsa.X86_64.Message.k_st hL),
        VG.Proof.MlDsa.X86_64.Message.k16 hc1 (VG.Proof.MlDsa.X86_64.Message.k_mu hL), VG.Proof.MlDsa.X86_64.Message.k16 hc1 (VG.Proof.MlDsa.X86_64.Message.k_ks hL)⟩
  refine VG.Proof.MlDsa.X86_64.Message.call_tr hok Proof.Sha3.X86_64.Stream.Squeeze.squeeze_correct
    Proof.Sha3.X86_64.Stream.Squeeze.squeeze_ct (fun _ => []) (fun L => [⟨L.ST, 200⟩, ⟨L.MU, 64⟩, ⟨L.KS, 640⟩])
    (fun L g mx m₀ t t1 hL hc hφ hm => squeeze_pre (args L g mx m₀ t t1 hL hc hφ hm))
    (fun L g₁ g₂ mx₁ mx₂ m₁ m₂ a b a1 b1 hL _ c₁ c₂ φ₁ φ₂ f₁ f₂ => ?_) fun L _ _ _ _ hL _ _ => ?_
  · have x := args L g₁ mx₁ m₁ a a1 hL c₁ φ₁ f₁
    have y := args L g₂ mx₂ m₂ b b1 hL c₂ φ₂ f₂
    simp only [Proof.Sha3.squeezeX86_64, VG.Proof.MlDsa.X86_64.Message.gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp),
      VG.Proof.MlDsa.X86_64.Message.gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp), VG.Proof.MlDsa.X86_64.Message.gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp),
      VG.Proof.MlDsa.X86_64.Message.gpr_ce _ _ _ (by decide : Reg.rcx ≠ .rsp), VG.Proof.MlDsa.X86_64.Message.gpr_ce _ _ _ (by decide : Reg.r8 ≠ .rsp),
      VG.Proof.MlDsa.X86_64.Message.gpr_ce _ _ _ (by decide : Reg.r9 ≠ .rsp), VG.Proof.MlDsa.X86_64.Message.rsp_ce, x.rdi, x.rsi, x.rdx, x.rcx, x.r8, x.r9, y.rdi, y.rsi,
      y.rdx, y.rcx, y.r8, y.r9, f₁.2.gpr (by decide : Reg.rsp ∉ argRegs), f₂.2.gpr (by decide : Reg.rsp ∉ argRegs),
      c₁.rsp, c₂.rsp, and_self]
  · obtain ⟨R, hR, hX⟩ := hL.inX
    refine ⟨fun r hr => by simp at hr, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [⟨R, hR, w_st.trans hX⟩, ⟨R, hR, w_mu.trans hX⟩, ⟨R, hR, w_ks.trans hX⟩]

/-! ## `μ` and `tr` -/

/-- Where the two bytes of the formatted message are. -/
theorem hdrSide {L : VG.Proof.MlDsa.X86_64.Message.Lay} (hL : L.Ok) : 64 < 136 ∧ 2 < 2 ^ 64 ∧ (∃ R ∈ L.rd ++ L.FR :: L.wr, Within ⟨L.SP, 2⟩ R) ∧
    Region.Disjoint ⟨L.SP, 2⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨L.SP, 2⟩ ⟨L.KS, 640⟩ ∧
    Region.Disjoint ⟨L.B, 40⟩ ⟨L.SP, 2⟩ :=
  ⟨by decide, by decide, ⟨L.FR, by simp, within_base _ (by decide)⟩,
    by have := hL.stk_x (d := 40) (n := 2) (e := 0) (k := 200) (by decide) (by decide); simpa only [VG.Proof.MlDsa.X86_64.Message.x0] using this,
    hL.stk_x (d := 40) (n := 2) (by decide) (by decide), Offset.base_disjoint _ (by decide) (by decide)⟩

/-- Where the context string is. -/
theorem ctxSide {L : VG.Proof.MlDsa.X86_64.Message.Lay} (hL : L.Ok) : 66 < 136 ∧ L.ctxLen.toNat < 2 ^ 64 ∧
    (∃ R ∈ L.rd ++ L.FR :: L.wr, Within ⟨L.ctx, L.ctxLen.toNat⟩ R) ∧
    Region.Disjoint ⟨L.ctx, L.ctxLen.toNat⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨L.ctx, L.ctxLen.toNat⟩ ⟨L.KS, 640⟩ ∧
    Region.Disjoint ⟨L.B, 40⟩ ⟨L.ctx, L.ctxLen.toNat⟩ :=
  ⟨by decide, L.ctxLen.isLt, ⟨L.CTX, List.mem_append_left _ hL.inCtx, within_self _⟩,
    by have := hL.x_r hL.xCtx (e := 0) (k := 200) (by decide); simpa only [VG.Proof.MlDsa.X86_64.Message.x0] using this.symm,
    (hL.x_r hL.xCtx (e := 200) (k := 640) (by decide)).symm,
    hL.kCtx.sub_left (Region.sub_prefix (by decide))⟩

/-- Where the message is. -/
theorem msgSide {L : VG.Proof.MlDsa.X86_64.Message.Lay} (hL : L.Ok) {q : Nat} (hq : q < 136) : q < 136 ∧ L.len.toNat < 2 ^ 64 ∧
    (∃ R ∈ L.rd ++ L.FR :: L.wr, Within ⟨L.msg, L.len.toNat⟩ R) ∧
    Region.Disjoint ⟨L.msg, L.len.toNat⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨L.msg, L.len.toNat⟩ ⟨L.KS, 640⟩ ∧
    Region.Disjoint ⟨L.B, 40⟩ ⟨L.msg, L.len.toNat⟩ :=
  ⟨hq, L.len.isLt, ⟨L.MSG, List.mem_append_left _ hL.inMsg, within_self _⟩,
    by have := hL.x_r hL.xMsg (e := 0) (k := 200) (by decide); simpa only [VG.Proof.MlDsa.X86_64.Message.x0] using this.symm,
    (hL.x_r hL.xMsg (e := 200) (k := 640) (by decide)).symm,
    hL.kMsg.sub_left (Region.sub_prefix (by decide))⟩

theorem absOk' (hE : oE p + 1024 < 2 ^ 31) {src len pos : VG.Impl.MlDsa.X86_64.Message.Arg} (h1 : src.ok = true) (h2 : len.ok = true)
    (h3 : pos.ok = true) : (VG.Proof.MlDsa.X86_64.Message.absArgs p src len pos).all Arg.ok = true := by
  simp only [VG.Proof.MlDsa.X86_64.Message.absArgs, List.all_cons, List.all_nil, h1, h2, h3, Bool.and_true, Bool.true_and]
  simp only [Impl.MlDsa.X86_64.Message.aSt, Impl.MlDsa.X86_64.Message.aKs, Arg.ok, fScr, Bool.and_eq_true,
    decide_eq_true_eq]
  omega

/-- The position after the context string. -/
abbrev qCtx (L : VG.Proof.MlDsa.X86_64.Message.Lay) : Nat := (66 + L.ctxLen.toNat) % 136
/-- The position after the message. -/
abbrev qMsg (L : VG.Proof.MlDsa.X86_64.Message.Lay) : Nat := (VG.Proof.MlDsa.X86_64.Message.qCtx L + L.len.toNat) % 136

theorem muHash_tr (hE : oE p + 1024 < 2 ^ 31) {Φ : VG.Proof.MlDsa.X86_64.Message.Lay → Mem → State → Prop}
    (hΦ : ∀ L m t, Φ L m t → VG.Proof.MlDsa.X86_64.Message.EOk p L) {tr : VG.Impl.MlDsa.X86_64.Message.Arg} (hok : tr.ok = true) (trp : VG.Proof.MlDsa.X86_64.Message.Lay → Addr)
    (htr : ∀ (L : VG.Proof.MlDsa.X86_64.Message.Lay) g mx m (t : State), VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m t → VG.Proof.MlDsa.X86_64.Message.EOk p L → tr.val t = trp L)
    (hs : ∀ L : VG.Proof.MlDsa.X86_64.Message.Lay, L.Ok → (∃ R ∈ L.rd ++ L.FR :: L.wr, Within ⟨trp L, 64⟩ R) ∧
      Region.Disjoint ⟨trp L, 64⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨trp L, 64⟩ ⟨L.KS, 640⟩ ∧
      Region.Disjoint ⟨L.B, 40⟩ ⟨trp L, 64⟩) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Message.Two I Φ) (muHash p tr) fun _ _ => True := by
  -- The relation keeps only `EOk` and the position in `rax`.
  let Ψ : (VG.Proof.MlDsa.X86_64.Message.Lay → Nat) → VG.Proof.MlDsa.X86_64.Message.Lay → Mem → State → Prop := fun q L _ t => VG.Proof.MlDsa.X86_64.Message.EOk p L ∧ (t.gpr .rax).toNat = q L
  have z := VG.Proof.MlDsa.X86_64.Message.two_wp (I := I) (Ψ := fun L _ _ => VG.Proof.MlDsa.X86_64.Message.EOk p L) (VG.Proof.MlDsa.X86_64.Message.zeroSt_tr hΦ)
    fun L g mx m₀ t hL hc hφ => WP.mono (VG.Proof.MlDsa.X86_64.Message.zeroSt_ok hL (hΦ L m₀ t hφ) hc) fun t' ⟨hc', _⟩ => ⟨hc', hΦ L m₀ t hφ⟩
  have a1 := VG.Proof.MlDsa.X86_64.Message.two_wp (I := I) (Ψ := Ψ fun _ => 64)
    (VG.Proof.MlDsa.X86_64.Message.kabs_tr (Φ := fun L _ _ => VG.Proof.MlDsa.X86_64.Message.EOk p L) (fun _ _ _ h => h) (VG.Proof.MlDsa.X86_64.Message.absOk' hE hok rfl rfl) trp (fun _ => 64)
      (fun _ => 0) (fun L g mx m t _ hc hφ => ⟨htr L g mx m t hc hφ, rfl, rfl⟩)
      fun L hL => ⟨by decide, by decide, (hs L hL).1, (hs L hL).2.1, (hs L hL).2.2.1, (hs L hL).2.2.2⟩)
    fun L g mx m₀ t hL hc hφ => by
      obtain ⟨a, b, c, d⟩ := hs L hL
      exact WP.mono (VG.Proof.MlDsa.X86_64.Message.kabs_ok hL hφ hc (src := tr) (len := .imm 64) (pos := .imm 0) (n := 64) (q := 0)
        (VG.Proof.MlDsa.X86_64.Message.absOk' hE hok rfl rfl) (htr L g mx m₀ t hc hφ) rfl rfl (by decide)
        (by decide) a b c d) fun t' ⟨hc', _, _, hx⟩ => ⟨hc', hφ, hx⟩
  have a2 := VG.Proof.MlDsa.X86_64.Message.two_wp (I := I) (Φ := Ψ fun _ => 64) (Ψ := Ψ fun _ => 66)
    (VG.Proof.MlDsa.X86_64.Message.kabs_tr (src := .sp) (len := .imm 2) (pos := .imm 64) (fun _ _ _ h => h.1) (VG.Proof.MlDsa.X86_64.Message.absOk' hE rfl rfl rfl) (fun L => L.SP) (fun _ => 2) (fun _ => 64)
      (fun L g mx m t _ hc _ => ⟨hc.rsp, rfl, rfl⟩) fun L hL => VG.Proof.MlDsa.X86_64.Message.hdrSide hL)
    fun L g mx m₀ t hL hc hφ => by
      obtain ⟨a, b, c, d, e, f⟩ := VG.Proof.MlDsa.X86_64.Message.hdrSide hL
      exact WP.mono (VG.Proof.MlDsa.X86_64.Message.kabs_ok hL hφ.1 hc (src := .sp) (len := .imm 2) (pos := .imm 64) (n := 2) (q := 64)
        (VG.Proof.MlDsa.X86_64.Message.absOk' hE rfl rfl rfl) hc.rsp rfl rfl a b c d e f)
        fun t' ⟨hc', _, _, hx⟩ => ⟨hc', hφ.1, hx⟩
  have a3 := VG.Proof.MlDsa.X86_64.Message.two_wp (I := I) (Φ := Ψ fun _ => 66) (Ψ := Ψ VG.Proof.MlDsa.X86_64.Message.qCtx)
    (VG.Proof.MlDsa.X86_64.Message.kabs_tr (src := .slot fCtx) (len := .slot fCtxLen) (pos := .imm 66) (fun _ _ _ h => h.1)
      (VG.Proof.MlDsa.X86_64.Message.absOk' hE (by decide) (by decide) (by decide)) (fun L => L.ctx)
      (fun L => L.ctxLen.toNat) (fun _ => 66)
      (fun L g mx m t _ hc _ => ⟨by rw [hc.slot, fCtx, hc.pCtx], by rw [hc.slot, fCtxLen, hc.pCtxLen,
        VG.Proof.MlDsa.X86_64.Message.ofNat_toNat_self], rfl⟩) fun L hL => VG.Proof.MlDsa.X86_64.Message.ctxSide hL)
    fun L g mx m₀ t hL hc hφ => by
      obtain ⟨a, b, c, d, e, f⟩ := VG.Proof.MlDsa.X86_64.Message.ctxSide hL
      exact WP.mono (VG.Proof.MlDsa.X86_64.Message.kabs_ok hL hφ.1 hc (src := .slot fCtx) (len := .slot fCtxLen) (pos := .imm 66) (q := 66)
        (VG.Proof.MlDsa.X86_64.Message.absOk' hE (by decide) (by decide) (by decide))
        (by rw [hc.slot, fCtx, hc.pCtx]) (by rw [hc.slot, fCtxLen, hc.pCtxLen, VG.Proof.MlDsa.X86_64.Message.ofNat_toNat_self]) rfl a b c d e f)
        fun t' ⟨hc', _, _, hx⟩ => ⟨hc', hφ.1, hx⟩
  have a4 := VG.Proof.MlDsa.X86_64.Message.two_wp (I := I) (Φ := Ψ VG.Proof.MlDsa.X86_64.Message.qCtx) (Ψ := Ψ VG.Proof.MlDsa.X86_64.Message.qMsg)
    (VG.Proof.MlDsa.X86_64.Message.kabs_tr (src := .slot fMsg) (len := .slot fLen) (pos := .ret) (fun _ _ _ h => h.1)
      (VG.Proof.MlDsa.X86_64.Message.absOk' hE (by decide) (by decide) rfl) (fun L => L.msg)
      (fun L => L.len.toNat) VG.Proof.MlDsa.X86_64.Message.qCtx
      (fun L g mx m t _ hc hφ => ⟨by rw [hc.slot, fMsg, hc.pMsg], by rw [hc.slot, fLen, hc.pLen,
        VG.Proof.MlDsa.X86_64.Message.ofNat_toNat_self], VG.Proof.MlDsa.X86_64.Message.ofNat_toNat_eq hφ.2⟩) fun L hL => VG.Proof.MlDsa.X86_64.Message.msgSide hL (Nat.mod_lt _ (by decide)))
    fun L g mx m₀ t hL hc hφ => by
      obtain ⟨a, b, c, d, e, f⟩ := VG.Proof.MlDsa.X86_64.Message.msgSide hL (Nat.mod_lt (66 + L.ctxLen.toNat) (by decide : 136 > 0))
      exact WP.mono (VG.Proof.MlDsa.X86_64.Message.kabs_ok hL hφ.1 hc (src := .slot fMsg) (len := .slot fLen) (pos := .ret)
        (VG.Proof.MlDsa.X86_64.Message.absOk' hE (by decide) (by decide) rfl)
        (by rw [hc.slot, fMsg, hc.pMsg]) (by rw [hc.slot, fLen, hc.pLen, VG.Proof.MlDsa.X86_64.Message.ofNat_toNat_self])
        (VG.Proof.MlDsa.X86_64.Message.ofNat_toNat_eq hφ.2) a b c d e f)
        fun t' ⟨hc', _, _, hx⟩ => ⟨hc', hφ.1, hx⟩
  have pd := VG.Proof.MlDsa.X86_64.Message.kpad_tr (I := I) (Φ := Ψ VG.Proof.MlDsa.X86_64.Message.qMsg) (fun _ _ _ h => h.1) (pos := .ret) (by
      simp only [VG.Proof.MlDsa.X86_64.Message.padArgs, Impl.MlDsa.X86_64.Message.aSt, Impl.MlDsa.X86_64.Message.aKs, List.all_cons,
        List.all_nil, Arg.ok, fScr, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq, true_and]
      omega) VG.Proof.MlDsa.X86_64.Message.qMsg (fun L g mx m t _ _ hφ => VG.Proof.MlDsa.X86_64.Message.ofNat_toNat_eq hφ.2) fun L _ => Nat.mod_lt _ (by decide)
  have pd' := VG.Proof.MlDsa.X86_64.Message.two_wp (I := I) (Φ := Ψ VG.Proof.MlDsa.X86_64.Message.qMsg) (Ψ := fun L _ _ => VG.Proof.MlDsa.X86_64.Message.EOk p L) pd
    fun L g mx m₀ t hL hc hφ => WP.mono (VG.Proof.MlDsa.X86_64.Message.kpad_ok hL hφ.1 hc (pos := .ret) (by
      simp only [VG.Proof.MlDsa.X86_64.Message.padArgs, Impl.MlDsa.X86_64.Message.aSt, Impl.MlDsa.X86_64.Message.aKs, List.all_cons,
        List.all_nil, Arg.ok, fScr, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq, true_and]
      omega) (VG.Proof.MlDsa.X86_64.Message.ofNat_toNat_eq hφ.2) (Nat.mod_lt _ (by decide))) fun t' ⟨hc', _⟩ => ⟨hc', hφ.1⟩
  have sq := VG.Proof.MlDsa.X86_64.Message.ksqz_tr (I := I) (Φ := fun L _ _ => VG.Proof.MlDsa.X86_64.Message.EOk p L) (fun _ _ _ h => h) (by
    simp only [VG.Proof.MlDsa.X86_64.Message.sqzArgs, Impl.MlDsa.X86_64.Message.aSt, Impl.MlDsa.X86_64.Message.aMu,
      Impl.MlDsa.X86_64.Message.aKs, List.all_cons, List.all_nil, Arg.ok, fScr, Bool.and_true,
      Bool.and_eq_true, decide_eq_true_eq]
    omega)
  exact RelCT.seq (RelCT.mono z (fun a b h => h) fun _ _ h => h)
    (a1.seq (a2.seq (a3.seq (a4.seq (pd'.seq sq)))))

theorem trHash_tr (hE : oE p + 1024 < 2 ^ 31) (hk : p.pkLen < 2 ^ 31) {Φ : VG.Proof.MlDsa.X86_64.Message.Lay → Mem → State → Prop}
    (hΦ : ∀ L m t, Φ L m t → VG.Proof.MlDsa.X86_64.Message.EOk p L ∧ L.keyLen = p.pkLen) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Message.Two I Φ) (trHash p) fun _ _ => True := by
  have keySide : ∀ L : VG.Proof.MlDsa.X86_64.Message.Lay, L.Ok → 0 < 136 ∧ L.keyLen < 2 ^ 64 ∧
      (∃ R ∈ L.rd ++ L.FR :: L.wr, Within ⟨L.key, L.keyLen⟩ R) ∧
      Region.Disjoint ⟨L.key, L.keyLen⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨L.key, L.keyLen⟩ ⟨L.KS, 640⟩ ∧
      Region.Disjoint ⟨L.B, 40⟩ ⟨L.key, L.keyLen⟩ := fun L hL =>
    ⟨by decide, by have := hL.hKey.2; omega, ⟨L.KEY, List.mem_append_left _ hL.inKey, within_self _⟩,
      by have := hL.x_r hL.xKey (e := 0) (k := 200) (by decide); simpa only [VG.Proof.MlDsa.X86_64.Message.x0] using this.symm,
      (hL.x_r hL.xKey (e := 200) (k := 640) (by decide)).symm,
      hL.kKey.sub_left (Region.sub_prefix (by decide))⟩
  have z := VG.Proof.MlDsa.X86_64.Message.two_wp (I := I) (Ψ := fun L _ _ => VG.Proof.MlDsa.X86_64.Message.EOk p L ∧ L.keyLen = p.pkLen)
    (VG.Proof.MlDsa.X86_64.Message.zeroSt_tr fun L m t h => (hΦ L m t h).1)
    fun L g mx m₀ t hL hc hφ => WP.mono (VG.Proof.MlDsa.X86_64.Message.zeroSt_ok hL (hΦ L m₀ t hφ).1 hc) fun t' ⟨hc', _⟩ => ⟨hc', hΦ L m₀ t hφ⟩
  have a1 := VG.Proof.MlDsa.X86_64.Message.two_wp (I := I) (Φ := fun L _ _ => VG.Proof.MlDsa.X86_64.Message.EOk p L ∧ L.keyLen = p.pkLen) (Ψ := fun L _ _ => VG.Proof.MlDsa.X86_64.Message.EOk p L)
    (VG.Proof.MlDsa.X86_64.Message.kabs_tr (src := .slot fKey) (len := .imm p.pkLen) (pos := .imm 0) (fun _ _ _ h => h.1)
      (VG.Proof.MlDsa.X86_64.Message.absOk' hE (by decide) (by simp [Arg.ok]; omega) rfl) (fun L => L.key) (fun L => L.keyLen) (fun _ => 0)
      (fun L g mx m t _ hc hφ => ⟨by rw [hc.slot, fKey, hc.pKey], by rw [hφ.2]; rfl, rfl⟩) keySide)
    fun L g mx m₀ t hL hc hφ => by
      obtain ⟨a, b, c, d, e, f⟩ := keySide L hL
      exact WP.mono (VG.Proof.MlDsa.X86_64.Message.kabs_ok hL hφ.1 hc (src := .slot fKey) (len := .imm p.pkLen) (pos := .imm 0)
        (n := L.keyLen) (q := 0) (VG.Proof.MlDsa.X86_64.Message.absOk' hE (by decide) (by simp [Arg.ok]; omega) rfl)
        (by rw [hc.slot, fKey, hc.pKey]) (by rw [hφ.2]; rfl) rfl a b c d e f)
        fun t' ⟨hc', _⟩ => ⟨hc', hφ.1⟩
  have pd := VG.Proof.MlDsa.X86_64.Message.kpad_tr (I := I) (Φ := fun L _ _ => VG.Proof.MlDsa.X86_64.Message.EOk p L) (fun _ _ _ h => h) (pos := .imm (p.pkLen % 136)) (by
      simp only [VG.Proof.MlDsa.X86_64.Message.padArgs, Impl.MlDsa.X86_64.Message.aSt, Impl.MlDsa.X86_64.Message.aKs, List.all_cons,
        List.all_nil, Arg.ok, fScr, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
      omega) (fun _ => p.pkLen % 136) (fun _ _ _ _ _ _ _ _ => rfl) fun _ _ => Nat.mod_lt _ (by decide)
  have pd' := VG.Proof.MlDsa.X86_64.Message.two_wp (I := I) (Φ := fun L _ _ => VG.Proof.MlDsa.X86_64.Message.EOk p L) (Ψ := fun L _ _ => VG.Proof.MlDsa.X86_64.Message.EOk p L) pd
    fun L g mx m₀ t hL hc hφ => WP.mono (VG.Proof.MlDsa.X86_64.Message.kpad_ok hL hφ hc (pos := .imm (p.pkLen % 136)) (by
      simp only [VG.Proof.MlDsa.X86_64.Message.padArgs, Impl.MlDsa.X86_64.Message.aSt, Impl.MlDsa.X86_64.Message.aKs, List.all_cons,
        List.all_nil, Arg.ok, fScr, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
      omega) rfl (Nat.mod_lt _ (by decide))) fun t' ⟨hc', _⟩ => ⟨hc', hφ⟩
  have sq := VG.Proof.MlDsa.X86_64.Message.ksqz_tr (I := I) (Φ := fun L _ _ => VG.Proof.MlDsa.X86_64.Message.EOk p L) (fun _ _ _ h => h) (by
    simp only [VG.Proof.MlDsa.X86_64.Message.sqzArgs, Impl.MlDsa.X86_64.Message.aSt, Impl.MlDsa.X86_64.Message.aMu,
      Impl.MlDsa.X86_64.Message.aKs, List.all_cons, List.all_nil, Arg.ok, fScr, Bool.and_true,
      Bool.and_eq_true, decide_eq_true_eq]
    omega)
  exact RelCT.seq (RelCT.mono z (fun a b h => h) fun _ _ h => h) (a1.seq (pd'.seq sq))

end

end VG.Proof.MlDsa.X86_64.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignPre`. -/
section

/-!
# ML-DSA on x86-64, `sign_message`: the precondition and the layout

Untrusted: everything here is checked by Lean. The precondition of
`signMessageContract p X86_64.abi 112`, spelled out (`SPre`), and the layout
of a run from a state satisfying it (`slay`).
-/

namespace VG.Proof.MlDsa.X86_64.Message

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Message
open VG.Proof.MlDsa.Message
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- The parameter sets. -/
def params : List Params := [mlDsa44, mlDsa65, mlDsa87]

/-- The size of `scratch` in bytes. -/
abbrev mScrLen (p : Params) : Nat := messageScratchWords p * 8

section
variable (p : Params) (s : State)

abbrev rSk : Region := ⟨s.gpr .rdi, p.skLen⟩
abbrev rMsg : Region := ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩
abbrev rCtx : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
abbrev rRnd : Region := ⟨s.gpr .r9, 32⟩
abbrev rArgs : Region := ⟨stackArgAddr s 0, 16⟩
abbrev rSig : Region := ⟨stackArg s 0, p.sigLen⟩
abbrev rScr : Region := ⟨stackArg s 1, VG.Proof.MlDsa.X86_64.Message.mScrLen p⟩
abbrev rRet : Region := ⟨s.gpr .rsp, 8⟩
abbrev rStk : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 112, 112⟩

end

/-- The precondition of `signMessageContract p X86_64.abi 112`. -/
structure SPre (p : Params) (s : State) : Prop where
  sp : 112 ≤ (s.gpr .rsp).toNat
  sp2 : (s.gpr .rsp).toNat + 24 ≤ 2 ^ 64
  rd : s.rd = [VG.Proof.MlDsa.X86_64.Message.rSk p s, VG.Proof.MlDsa.X86_64.Message.rMsg s, VG.Proof.MlDsa.X86_64.Message.rCtx s, VG.Proof.MlDsa.X86_64.Message.rRnd s, VG.Proof.MlDsa.X86_64.Message.rArgs s]
  wr : s.wr = [VG.Proof.MlDsa.X86_64.Message.rSig p s, VG.Proof.MlDsa.X86_64.Message.rScr p s]
  skSig : (VG.Proof.MlDsa.X86_64.Message.rSk p s).Disjoint (VG.Proof.MlDsa.X86_64.Message.rSig p s)
  skScr : (VG.Proof.MlDsa.X86_64.Message.rSk p s).Disjoint (VG.Proof.MlDsa.X86_64.Message.rScr p s)
  msgSig : (VG.Proof.MlDsa.X86_64.Message.rMsg s).Disjoint (VG.Proof.MlDsa.X86_64.Message.rSig p s)
  msgScr : (VG.Proof.MlDsa.X86_64.Message.rMsg s).Disjoint (VG.Proof.MlDsa.X86_64.Message.rScr p s)
  ctxSig : (VG.Proof.MlDsa.X86_64.Message.rCtx s).Disjoint (VG.Proof.MlDsa.X86_64.Message.rSig p s)
  ctxScr : (VG.Proof.MlDsa.X86_64.Message.rCtx s).Disjoint (VG.Proof.MlDsa.X86_64.Message.rScr p s)
  rndSig : (VG.Proof.MlDsa.X86_64.Message.rRnd s).Disjoint (VG.Proof.MlDsa.X86_64.Message.rSig p s)
  rndScr : (VG.Proof.MlDsa.X86_64.Message.rRnd s).Disjoint (VG.Proof.MlDsa.X86_64.Message.rScr p s)
  sigScr : (VG.Proof.MlDsa.X86_64.Message.rSig p s).Disjoint (VG.Proof.MlDsa.X86_64.Message.rScr p s)
  sigArgs : (VG.Proof.MlDsa.X86_64.Message.rSig p s).Disjoint (VG.Proof.MlDsa.X86_64.Message.rArgs s)
  scrArgs : (VG.Proof.MlDsa.X86_64.Message.rScr p s).Disjoint (VG.Proof.MlDsa.X86_64.Message.rArgs s)
  retSk : (VG.Proof.MlDsa.X86_64.Message.rRet s).Disjoint (VG.Proof.MlDsa.X86_64.Message.rSk p s)
  retMsg : (VG.Proof.MlDsa.X86_64.Message.rRet s).Disjoint (VG.Proof.MlDsa.X86_64.Message.rMsg s)
  retCtx : (VG.Proof.MlDsa.X86_64.Message.rRet s).Disjoint (VG.Proof.MlDsa.X86_64.Message.rCtx s)
  retRnd : (VG.Proof.MlDsa.X86_64.Message.rRet s).Disjoint (VG.Proof.MlDsa.X86_64.Message.rRnd s)
  retSig : (VG.Proof.MlDsa.X86_64.Message.rRet s).Disjoint (VG.Proof.MlDsa.X86_64.Message.rSig p s)
  retScr : (VG.Proof.MlDsa.X86_64.Message.rRet s).Disjoint (VG.Proof.MlDsa.X86_64.Message.rScr p s)
  retArgs : (VG.Proof.MlDsa.X86_64.Message.rRet s).Disjoint (VG.Proof.MlDsa.X86_64.Message.rArgs s)
  stkSk : (VG.Proof.MlDsa.X86_64.Message.rStk s).Disjoint (VG.Proof.MlDsa.X86_64.Message.rSk p s)
  stkMsg : (VG.Proof.MlDsa.X86_64.Message.rStk s).Disjoint (VG.Proof.MlDsa.X86_64.Message.rMsg s)
  stkCtx : (VG.Proof.MlDsa.X86_64.Message.rStk s).Disjoint (VG.Proof.MlDsa.X86_64.Message.rCtx s)
  stkRnd : (VG.Proof.MlDsa.X86_64.Message.rStk s).Disjoint (VG.Proof.MlDsa.X86_64.Message.rRnd s)
  stkSig : (VG.Proof.MlDsa.X86_64.Message.rStk s).Disjoint (VG.Proof.MlDsa.X86_64.Message.rSig p s)
  stkScr : (VG.Proof.MlDsa.X86_64.Message.rStk s).Disjoint (VG.Proof.MlDsa.X86_64.Message.rScr p s)
  stkArgs : (VG.Proof.MlDsa.X86_64.Message.rStk s).Disjoint (VG.Proof.MlDsa.X86_64.Message.rArgs s)
  nSk : (s.gpr .rdi).toNat + p.skLen ≤ 2 ^ 64
  nMsg : (s.gpr .rsi).toNat + (s.gpr .rdx).toNat ≤ 2 ^ 64
  nCtx : (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64
  nRnd : (s.gpr .r9).toNat + 32 ≤ 2 ^ 64
  nSig : (stackArg s 0).toNat + p.sigLen ≤ 2 ^ 64
  nScr : (stackArg s 1).toNat + VG.Proof.MlDsa.X86_64.Message.mScrLen p ≤ 2 ^ 64

theorem sPre_of {p : Params} {s : State} (h : (signMessageContract p X86_64.abi 112).pre s) : VG.Proof.MlDsa.X86_64.Message.SPre p s := by
  sig_pre [signMessageContract, signMessageSig, X86_64.abi, X86_64.argRegs, List.range, List.range.loop] at h
  obtain ⟨sp, sp2, rd, wr, skSig, skScr, msgSig, msgScr, ctxSig, ctxScr, rndSig, rndScr, sigScr, sigArgs,
    scrArgs, retSk, retMsg, retCtx, retRnd, retSig, retScr, retArgs, stkSk, stkMsg, stkCtx, stkRnd, stkSig,
    stkScr, stkArgs, nSk, nMsg, nCtx, nRnd, nSig, nScr⟩ := h
  exact ⟨sp, sp2, rd, wr, skSig, skScr, msgSig, msgScr, ctxSig, ctxScr, rndSig, rndScr, sigScr, sigArgs,
    scrArgs, retSk, retMsg, retCtx, retRnd, retSig, retScr, retArgs, stkSk, stkMsg, stkCtx, stkRnd, stkSig,
    stkScr, stkArgs, nSk, nMsg, nCtx, nRnd, nSig, nScr⟩

/-! ## The layout -/

theorem mScr_eq (p : Params) : VG.Proof.MlDsa.X86_64.Message.mScrLen p = oE p + 1024 := by
  simp only [VG.Proof.MlDsa.X86_64.Message.mScrLen, messageScratchWords, oE]; omega

theorem oE_lt {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Message.params) : oE p + 1024 < 2 ^ 31 := by
  simp only [VG.Proof.MlDsa.X86_64.Message.params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> decide

theorem skLen_ge {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Message.params) : 128 ≤ p.skLen ∧ p.skLen < 2 ^ 31 := by
  simp only [VG.Proof.MlDsa.X86_64.Message.params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> decide

/-- The layout of a run of `sign_message` from `s`. -/
def slay (p : Params) (s : State) : VG.Proof.MlDsa.X86_64.Message.Lay where
  B := s.gpr .rsp - BitVec.ofNat 64 112
  key := s.gpr .rdi
  keyLen := p.skLen
  msg := s.gpr .rsi
  len := s.gpr .rdx
  ctx := s.gpr .rcx
  ctxLen := s.gpr .r8
  rnd := s.gpr .r9
  sig := stackArg s 0
  scr := stackArg s 1
  E := oE p
  rd := s.rd
  wr := s.wr

theorem slay_B (p : Params) (s : State) :
    (VG.Proof.MlDsa.X86_64.Message.slay p s).B + BitVec.ofNat 64 112 = s.gpr .rsp := BitVec.sub_add_cancel _ _

theorem slay_X (p : Params) (s : State) : Within (VG.Proof.MlDsa.X86_64.Message.slay p s).XS (VG.Proof.MlDsa.X86_64.Message.rScr p s) :=
  ⟨oE p, rfl, by show oE p + 1024 ≤ VG.Proof.MlDsa.X86_64.Message.mScrLen p; rw [VG.Proof.MlDsa.X86_64.Message.mScr_eq]⟩

theorem slay_ok {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Message.params) {s : State} (h : VG.Proof.MlDsa.X86_64.Message.SPre p s) (h8 : (s.gpr .r8).toNat < 256) :
    (VG.Proof.MlDsa.X86_64.Message.slay p s).Ok := by
  have hX := VG.Proof.MlDsa.X86_64.Message.slay_X p s
  have hXs := hX.sub
  refine ⟨h8, VG.Proof.MlDsa.X86_64.Message.oE_lt hp, VG.Proof.MlDsa.X86_64.Message.skLen_ge hp, ?_, ⟨VG.Proof.MlDsa.X86_64.Message.rScr p s, by simp [VG.Proof.MlDsa.X86_64.Message.slay, h.wr], hX⟩, by simp [VG.Proof.MlDsa.X86_64.Message.slay, h.rd],
    by simp [VG.Proof.MlDsa.X86_64.Message.slay, h.rd], by simp [VG.Proof.MlDsa.X86_64.Message.slay, h.rd], h.skScr.symm.sub_left hXs, h.msgScr.symm.sub_left hXs,
    h.ctxScr.symm.sub_left hXs, h.stkScr.sub_right hXs, h.stkSk, h.stkMsg, h.stkCtx, h.nSk, h.nMsg, h.nCtx, ?_⟩
  · have := h.sp; have := (s.gpr .rsp).isLt
    simp only [VG.Proof.MlDsa.X86_64.Message.slay, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  · intro R hR
    simp only [VG.Proof.MlDsa.X86_64.Message.slay, h.wr, List.mem_cons, List.not_mem_nil, or_false] at hR
    have := h.nSig; have := h.nScr
    rcases hR with rfl | rfl <;> simp only <;> omega

theorem mu_eq (p : Params) (s : State) :
    (VG.Proof.MlDsa.X86_64.Message.slay p s).MU = stackArg s 1 + BitVec.ofNat 64 (oE p + 840) := by
  simp only [Lay.MU, Lay.X, VG.Proof.MlDsa.X86_64.Message.slay, add_add]


theorem mu_nowrap {p : Params} {s : State} (h : VG.Proof.MlDsa.X86_64.Message.SPre p s) : (VG.Proof.MlDsa.X86_64.Message.slay p s).MU.toNat + 64 ≤ 2 ^ 64 := by
  have hn : (stackArg s 1).toNat + (oE p + 1024) ≤ 2 ^ 64 := by rw [← VG.Proof.MlDsa.X86_64.Message.mScr_eq]; exact h.nScr
  rw [VG.Proof.MlDsa.X86_64.Message.mu_eq]
  generalize oE p = e at hn ⊢
  generalize stackArg s 1 = x at hn ⊢
  clear h
  rw [toNat_add_ofNat (by omega), Nat.add_assoc]
  exact Nat.le_trans (Nat.add_le_add_left (by clear hn; omega) _) hn


end VG.Proof.MlDsa.X86_64.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignCall`. -/
section

/-!
# ML-DSA on x86-64, `sign_message`: the call of the signing function on `μ`

Untrusted: everything here is checked by Lean. Any code that meets the
contract the proof of `vg_mldsa*_sign` is written against (`signK p 32`),
never writes `rsp` and whose calls nest at most three deep (`SignFn`): its
call from the frame, on the key, `μ` at `X + 840`, `rnd`, `sig` and the
first `scratchWords p` words of `scratch` (`signCall_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Message

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Proof.MlDsa.X86_64.Sign (signK scrLen)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- A signing function on `μ` that `sign_message` can call. -/
structure SignFn (p : Params) (c : Prog isa) : Prop where
  ok : ∀ s, (signK p 32).pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (signK p 32).post s s'
  ct : ConstantTime isa (signK p 32).pre (signK p 32).pub c
  nosp : NoSp c
  depth : c.depth ≤ 4

/-- The arguments of the call of the signing function on `μ`. -/
abbrev signArgs (p : Params) : List Arg := [.slot fKey, VG.Impl.MlDsa.X86_64.Message.aMu p, .slot fRnd, .slot fSig, .slot fScr]

section
variable {p : Params} {s : State}

/-- The working space of the signing function on `μ`. -/
abbrev rScrMu (p : Params) (s : State) : Region := ⟨stackArg s 1, scrLen p⟩

theorem scrMu_sub (p : Params) (s : State) : Region.Sub (VG.Proof.MlDsa.X86_64.Message.rScrMu p s) (VG.Proof.MlDsa.X86_64.Message.rScr p s) :=
  Region.sub_prefix (by rw [VG.Proof.MlDsa.X86_64.Message.mScr_eq]; simp [scrLen, oE])

theorem mu_within (p : Params) (s : State) : Within ⟨(VG.Proof.MlDsa.X86_64.Message.slay p s).MU, 64⟩ (VG.Proof.MlDsa.X86_64.Message.rScr p s) :=
  (within_off (VG.Proof.MlDsa.X86_64.Message.slay p s).X (d := 840) (n := 64) (k := 1024) (by omega)).trans (VG.Proof.MlDsa.X86_64.Message.slay_X p s)

theorem mu_scrMu {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Message.params) (s : State) : Region.Disjoint ⟨(VG.Proof.MlDsa.X86_64.Message.slay p s).MU, 64⟩ (VG.Proof.MlDsa.X86_64.Message.rScrMu p s) := by
  show Region.Disjoint ⟨stackArg s 1 + BitVec.ofNat 64 (oE p) + BitVec.ofNat 64 840, 64⟩ ⟨stackArg s 1, scrLen p⟩
  rw [add_add]
  exact Offset.disjoint_base _ (by simp [scrLen, oE]) (by have := VG.Proof.MlDsa.X86_64.Message.oE_lt hp; omega)

/-- The regions the signing function on `μ` reads and writes. -/
abbrev signRd (p : Params) (s : State) : List Region :=
  [⟨s.gpr .rdi, p.skLen⟩, ⟨(VG.Proof.MlDsa.X86_64.Message.slay p s).MU, 64⟩, ⟨s.gpr .r9, 32⟩]
abbrev signWr (p : Params) (s : State) : List Region := [⟨stackArg s 0, p.sigLen⟩, VG.Proof.MlDsa.X86_64.Message.rScrMu p s]

theorem signArgs_ok (hp : p ∈ VG.Proof.MlDsa.X86_64.Message.params) : (VG.Proof.MlDsa.X86_64.Message.signArgs p).all Arg.ok = true := by
  have := VG.Proof.MlDsa.X86_64.Message.oE_lt hp
  simp only [VG.Proof.MlDsa.X86_64.Message.signArgs, Impl.MlDsa.X86_64.Message.aMu, List.all_cons, List.all_nil, Arg.ok, fKey, fRnd, fSig,
    fScr, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  omega

/-- The registers after the moves of the arguments. -/
theorem signRegs_of {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem} {t t1 : State}
    (hc : VG.Proof.MlDsa.X86_64.Message.Ctx (VG.Proof.MlDsa.X86_64.Message.slay p s) g mx m₀ t) (hm : VG.Proof.MlDsa.X86_64.Message.Moved (VG.Proof.MlDsa.X86_64.Message.signArgs p) t t1) :
    t1.gpr .rdi = s.gpr .rdi ∧ t1.gpr .rsi = (VG.Proof.MlDsa.X86_64.Message.slay p s).MU ∧ t1.gpr .rdx = s.gpr .r9 ∧
      t1.gpr .rcx = stackArg s 0 ∧ t1.gpr .r8 = stackArg s 1 := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := VG.Proof.MlDsa.X86_64.Message.argsIn5 hm.1.1
  rw [hc.slot, fKey, hc.pKey] at e1
  rw [hc.aMu p rfl] at e2
  rw [hc.slot, fRnd, hc.pRnd] at e3
  rw [hc.slot, fSig, hc.pSig] at e4
  rw [hc.slot, fScr, hc.pScr] at e5
  exact ⟨e1, e2, e3, e4, e5⟩

/-- The precondition of the signing function on `μ`, on entry to it. -/
theorem signK_pre (hp : p ∈ VG.Proof.MlDsa.X86_64.Message.params) (h : VG.Proof.MlDsa.X86_64.Message.SPre p s) (h8 : (s.gpr .r8).toNat < 256) {g : Reg → BitVec 64}
    {mx : BitVec 32} {m₀ : Mem} {t t1 : State} (hc : VG.Proof.MlDsa.X86_64.Message.Ctx (VG.Proof.MlDsa.X86_64.Message.slay p s) g mx m₀ t) (hm : VG.Proof.MlDsa.X86_64.Message.Moved (VG.Proof.MlDsa.X86_64.Message.signArgs p) t t1) :
    (signK p 32).pre (t1.callEntry.withRegions (VG.Proof.MlDsa.X86_64.Message.signRd p s) (VG.Proof.MlDsa.X86_64.Message.signWr p s)) := by
  have hL := VG.Proof.MlDsa.X86_64.Message.slay_ok hp h h8
  have hc1 : VG.Proof.MlDsa.X86_64.Message.Ctx (VG.Proof.MlDsa.X86_64.Message.slay p s) g mx m₀ t1 :=
    hc.regs hm.2.2.1 hm.2.2.2 hm.1.2.1 hm.1.2.2 fun r hr => hm.2.gpr (VG.Proof.MlDsa.X86_64.Message.argRegs_cs r hr)
  obtain ⟨e1, e2, e3, e4, e5⟩ := VG.Proof.MlDsa.X86_64.Message.signRegs_of hc hm
  simp only [signK, State.withRegions_rd, State.withRegions_wr, VG.Proof.MlDsa.X86_64.Message.gpr_ce t1 _ _ (by decide : Reg.rdi ≠ .rsp),
    VG.Proof.MlDsa.X86_64.Message.gpr_ce t1 _ _ (by decide : Reg.rsi ≠ .rsp), VG.Proof.MlDsa.X86_64.Message.gpr_ce t1 _ _ (by decide : Reg.rdx ≠ .rsp),
    VG.Proof.MlDsa.X86_64.Message.gpr_ce t1 _ _ (by decide : Reg.rcx ≠ .rsp), VG.Proof.MlDsa.X86_64.Message.gpr_ce t1 _ _ (by decide : Reg.r8 ≠ .rsp), VG.Proof.MlDsa.X86_64.Message.rsp_ce,
    e1, e2, e3, e4, e5, Sign.retR, hc1.rsp, VG.Proof.MlDsa.X86_64.Message.sp_sub8, VG.Proof.MlDsa.X86_64.Message.below32]
  have hsub := VG.Proof.MlDsa.X86_64.Message.scrMu_sub p s
  have hmu := (VG.Proof.MlDsa.X86_64.Message.mu_within p s).sub
  have hB := hL.nB
  have hn := h.nScr
  have hE := VG.Proof.MlDsa.X86_64.Message.oE_lt hp
  refine ⟨trivial, trivial, h.skSig, h.skScr.sub_right hsub, h.sigScr.symm.sub_left hmu, VG.Proof.MlDsa.X86_64.Message.mu_scrMu hp s, h.rndSig,
    h.rndScr.sub_right hsub, h.sigScr.sub_right hsub, hL.stk_r h.stkSk (by omega),
    hL.stk_x (d := 32) (n := 8) (e := 840) (k := 64) (by omega) (by omega), hL.stk_r h.stkRnd (by omega),
    hL.stk_r h.stkSig (by omega), hL.stk_r (h.stkScr.sub_right hsub) (by omega), ?_, ?_, ?_, ?_, ?_, h.nSk, ?_,
    h.nRnd, h.nSig, by simp only [VG.Proof.MlDsa.X86_64.Message.mScrLen, scrLen, messageScratchWords] at hn ⊢; omega, ?_⟩
  · exact h.stkSk.sub_left (Region.sub_prefix (by omega))
  · exact (hL.kX.sub_left (Region.sub_prefix (by omega))).sub_right (Offset.sub_base _ (by omega))
  · exact h.stkRnd.sub_left (Region.sub_prefix (by omega))
  · exact h.stkSig.sub_left (Region.sub_prefix (by omega))
  · exact (h.stkScr.sub_right hsub).sub_left (Region.sub_prefix (by omega))
  · exact VG.Proof.MlDsa.X86_64.Message.mu_nowrap h
  · rw [toNat_add_ofNat (by omega)]; omega


/-- The call of the signing function on `μ`. -/
theorem signCall_ok {n : String} {c : Prog isa} (hS : VG.Proof.MlDsa.X86_64.Message.SignFn p c) (hp : p ∈ VG.Proof.MlDsa.X86_64.Message.params) (h : VG.Proof.MlDsa.X86_64.Message.SPre p s)
    (h8 : (s.gpr .r8).toNat < 256) {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem} {t : State}
    (hc : VG.Proof.MlDsa.X86_64.Message.Ctx (VG.Proof.MlDsa.X86_64.Message.slay p s) g mx m₀ t) :
    WP isa (callA n c (VG.Proof.MlDsa.X86_64.Message.signArgs p)) t fun s' =>
      s'.rd = t.rd ∧ s'.wr = t.wr ∧ s'.gpr .rsp = t.gpr .rsp ∧ (∀ r ∈ calleeSaved, s'.gpr r = t.gpr r) ∧
      s'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 ∧
      Frame [VG.Proof.MlDsa.X86_64.Message.rSig p s, VG.Proof.MlDsa.X86_64.Message.rScrMu p s, ⟨(VG.Proof.MlDsa.X86_64.Message.slay p s).B, 40⟩] t.mem s'.mem ∧
      Outcome (fun b => signMu p b (bytesAt t.mem (s.gpr .rdi) p.skLen) (bytesAt t.mem (VG.Proof.MlDsa.X86_64.Message.slay p s).MU 64)
          (bytesAt t.mem (s.gpr .r9) 32)) ((s'.gpr .rax).setWidth 32)
        (bytesAt s'.mem (stackArg s 0) p.sigLen) := by
  have hL := VG.Proof.MlDsa.X86_64.Message.slay_ok hp h h8
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Message.setArgs_ok _ (VG.Proof.MlDsa.X86_64.Message.signArgs_ok hp) t hc.frOk) fun t1 hm => ?_)
  obtain ⟨⟨hA, hm', hx⟩, k⟩ := hm
  have hc1 : VG.Proof.MlDsa.X86_64.Message.Ctx (VG.Proof.MlDsa.X86_64.Message.slay p s) g mx m₀ t1 := hc.regs k.2.1 k.2.2 hm' hx fun r hr => k.gpr (VG.Proof.MlDsa.X86_64.Message.argRegs_cs r hr)
  obtain ⟨e1, e2, e3, e4, e5⟩ := VG.Proof.MlDsa.X86_64.Message.signRegs_of hc ⟨⟨hA, hm', hx⟩, k⟩
  have hpre := VG.Proof.MlDsa.X86_64.Message.signK_pre hp h h8 hc ⟨⟨hA, hm', hx⟩, k⟩
  have hm := hm'
  have hdep := hS.depth
  have hsub := VG.Proof.MlDsa.X86_64.Message.scrMu_sub p s
  have hrsp1 : t1.gpr .rsp = (VG.Proof.MlDsa.X86_64.Message.slay p s).SP := hc1.rsp
  refine WP.call_mx hS.ok hS.nosp (by omega) hpre ?_ ?_ fun s' hrd hwr hcs hf _ hpost hmx => ?_
  · rw [hc1.rd, hc1.wr]
    refine VG.Proof.MlDsa.X86_64.Message.covers_of_within fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨VG.Proof.MlDsa.X86_64.Message.rSk p s, by simp [VG.Proof.MlDsa.X86_64.Message.slay, h.rd], within_self _⟩
    · exact ⟨VG.Proof.MlDsa.X86_64.Message.rScr p s, by simp [VG.Proof.MlDsa.X86_64.Message.slay, h.wr], VG.Proof.MlDsa.X86_64.Message.mu_within p s⟩
    · exact ⟨VG.Proof.MlDsa.X86_64.Message.rRnd s, by simp [VG.Proof.MlDsa.X86_64.Message.slay, h.rd], within_self _⟩
    · exact ⟨VG.Proof.MlDsa.X86_64.Message.rSig p s, by simp [VG.Proof.MlDsa.X86_64.Message.slay, h.wr], within_self _⟩
    · exact ⟨VG.Proof.MlDsa.X86_64.Message.rScr p s, by simp [VG.Proof.MlDsa.X86_64.Message.slay, h.wr], within_base _ (by rw [VG.Proof.MlDsa.X86_64.Message.mScr_eq]; simp [scrLen, oE])⟩
  · rw [hc1.wr]
    refine VG.Proof.MlDsa.X86_64.Message.covers_of_within fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨VG.Proof.MlDsa.X86_64.Message.rSig p s, by simp [VG.Proof.MlDsa.X86_64.Message.slay, h.wr], within_self _⟩
    · exact ⟨VG.Proof.MlDsa.X86_64.Message.rScr p s, by simp [VG.Proof.MlDsa.X86_64.Message.slay, h.wr], within_base _ (by rw [VG.Proof.MlDsa.X86_64.Message.mScr_eq]; simp [scrLen, oE])⟩
  obtain ⟨s₂, hm₂, hg₂, hq⟩ := hpost
  refine ⟨hrd.trans k.2.1, hwr.trans k.2.2, by rw [hcs .rsp (by decide), k.gpr (by decide)],
    fun r hr => by rw [hcs r hr, k.gpr (VG.Proof.MlDsa.X86_64.Message.argRegs_cs r hr)], by rw [hmx, hx], ?_, ?_⟩
  · rw [← hm]
    refine Frame.sub hf fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨VG.Proof.MlDsa.X86_64.Message.rSig p s, List.mem_cons_self .., fun _ h => h⟩
      · exact ⟨VG.Proof.MlDsa.X86_64.Message.rScrMu p s, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨⟨(VG.Proof.MlDsa.X86_64.Message.slay p s).B, 40⟩, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), ?_⟩
      rw [hrsp1]
      exact VG.Proof.MlDsa.X86_64.Message.below_call_sub _ (by omega)
  · simp only [signK, State.withRegions_mem, VG.Proof.MlDsa.X86_64.Message.gpr_ce t1 _ _ (by decide : Reg.rdi ≠ .rsp),
      VG.Proof.MlDsa.X86_64.Message.gpr_ce t1 _ _ (by decide : Reg.rsi ≠ .rsp), VG.Proof.MlDsa.X86_64.Message.gpr_ce t1 _ _ (by decide : Reg.rdx ≠ .rsp),
      VG.Proof.MlDsa.X86_64.Message.gpr_ce t1 _ _ (by decide : Reg.rcx ≠ .rsp), e1, e2, e3, e4, hm₂] at hq
    have hL := VG.Proof.MlDsa.X86_64.Message.slay_ok hp h h8
    rw [hc1.ce_bytesAt (p := s.gpr .rdi) (hL.stk_r h.stkSk (by omega)) (by have := h.nSk; omega),
      hc1.ce_bytesAt (p := (VG.Proof.MlDsa.X86_64.Message.slay p s).MU) (hL.stk_x (d := 32) (n := 8) (e := 840) (k := 64) (by omega)
        (by omega)) (by omega),
      hc1.ce_bytesAt (p := s.gpr .r9) (hL.stk_r h.stkRnd (by omega)) (by omega), hm,
      hg₂ _ (by decide)] at hq
    exact hq
end
end VG.Proof.MlDsa.X86_64.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignCorrect`. -/
section

/-!
# ML-DSA on x86-64, `sign_message`: correctness

Untrusted: everything here is checked by Lean. From a state satisfying
`signMessageContract p X86_64.abi 112`, `signMessage n c p` returns 2 if
the context string is longer than 255 bytes; otherwise it computes `μ` of
the formatted message and calls the signing function on `μ` `c`, which
gives the signature of `ML-DSA.Sign_internal` on the formatted message
(`signMessage_correct`).
-/

namespace VG.Proof.MlDsa.X86_64.Message

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.X86_64 (Keep WP.keep)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## The branch on `ctx_len` -/

theorem wp_ite_t {c : isa.Cond} {th el : Prog isa} {s : State} {Q : State → Prop}
    (hc : isa.eval c s = some true) (h : WP isa th s Q) : WP isa (.ite c th el) s Q :=
  let ⟨_, _, e, q⟩ := h; ⟨_, _, .iteT hc e, q⟩

theorem wp_ite_f {c : isa.Cond} {th el : Prog isa} {s : State} {Q : State → Prop}
    (hc : isa.eval c s = some false) (h : WP isa el s Q) : WP isa (.ite c th el) s Q :=
  let ⟨_, _, e, q⟩ := h; ⟨_, _, .iteF hc e, q⟩

/-- `cmp r8, 256`. -/
theorem cmp_ok (s : State) :
    WP isa (.block [.alu .cmp .r8 (.imm 256)]) s fun s1 => s1.gpr = s.gpr ∧ s1.mem = s.mem ∧
      s1.rd = s.rd ∧ s1.wr = s.wr ∧ s1.mxcsr = s.mxcsr ∧
      isa.eval .b s1 = some (decide ((s.gpr .r8).toNat < 256)) := by
  xrun [show BitVec.signExtend 64 (256 : BitVec 32) = 256 by decide]
  exact ⟨rfl, rfl⟩

/-! ## Before the frame -/

theorem stackArgAddr0 (s : State) : stackArgAddr s 0 = s.gpr .rsp + BitVec.ofNat 64 8 := rfl

/-- `sig` to `r10`, `scratch` to `r11`, 0 to `rax`. -/
theorem signMov_ok {p : Params} {s s1 : State} (h : VG.Proof.MlDsa.X86_64.Message.SPre p s) (hg : s1.gpr = s.gpr) (hm : s1.mem = s.mem)
    (hrd : s1.rd = s.rd) :
    WP isa (.block [.mov .r10 (.mem (stk 8)), .mov .r11 (.mem (stk 16)), .mov32 .rax (.imm 0)]) s1 fun s2 =>
      (s2.gpr .r10 = stackArg s 0 ∧ s2.gpr .r11 = stackArg s 1 ∧ s2.gpr .rax = 0 ∧ s2.mem = s.mem ∧
        s2.mxcsr = s1.mxcsr) ∧ Keep [.r10, .r11, .rax] s1 s2 := by
  have hin : ∀ d, d + 8 ≤ 16 → InRegions (s1.rd ++ s1.wr) (s1.gpr .rsp + BitVec.ofNat 64 (8 + d)) 8 := by
    intro d hd
    refine ⟨VG.Proof.MlDsa.X86_64.Message.rArgs s, by simp [hrd, h.rd], ?_⟩
    rw [hg, ← add_add, ← VG.Proof.MlDsa.X86_64.Message.stackArgAddr0]
    exact Offset.contains_base _ hd (by omega)
  refine WP.keep _ ?_ (by decide)
  have h8 := hin 0 (by omega)
  have h16 := hin 8 (by omega)
  simp only [Nat.add_zero, Nat.reduceAdd] at h8 h16
  xrun [VG.Proof.MlDsa.X86_64.Message.ea_stk, h8, h16, RegUpd.mxcsr_setReg]
  rw [hm, hg]
  exact ⟨rfl, rfl, rfl⟩

/-! ## The function -/

theorem cs_r11 : ∀ r ∈ calleeSaved, r ≠ .r11 := by decide
theorem cs_tmp : ∀ r ∈ calleeSaved, r ∉ [Reg.r10, .r11, .rax] := by decide

/-- The arguments of `signRegs`, pushed. -/
theorem signRegs_vals {p : Params} {s s2 : State} (hk : ∀ r, r ∉ [Reg.r10, .r11, .rax] → s2.gpr r = s.gpr r)
    (h10 : s2.gpr .r10 = stackArg s 0) (h11 : s2.gpr .r11 = stackArg s 1) (hax : s2.gpr .rax = 0) :
    ∀ j (hj : j < 9), s2.gpr (signRegs[j]'(by simp [signRegs]; omega)) =
      (VG.Proof.MlDsa.X86_64.Message.slay p s).vals[j]'(by simp [Lay.vals]; omega) := by
  intro j hj
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [signRegs, Lay.vals, VG.Proof.MlDsa.X86_64.Message.slay, List.getElem_cons_zero, List.getElem_cons_succ, h10, h11, hax] <;>
    exact hk _ (by decide)

theorem signMessage_wp {p : Params} {n : String} {c : Prog isa} (hS : VG.Proof.MlDsa.X86_64.Message.SignFn p c) (hp : p ∈ VG.Proof.MlDsa.X86_64.Message.params)
    {s : State} (hpre : (signMessageContract p X86_64.abi 112).pre s) :
    WP isa (signMessage n c p) s fun s' =>
      abiPreserved s s' ∧ (signMessageContract p X86_64.abi 112).post s s' := by
  have h := VG.Proof.MlDsa.X86_64.Message.sPre_of hpre
  unfold signMessage top
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Message.cmp_ok s) fun s1 ⟨hg1, hm1, hrd1, hwr1, hx1, hc1⟩ => ?_)
  by_cases h8 : (s.gpr .r8).toNat < 256
  · rw [decide_eq_true h8] at hc1
    refine VG.Proof.MlDsa.X86_64.Message.wp_ite_t hc1 (WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Message.signMov_ok h hg1 hm1 hrd1) fun s2 ⟨⟨h10, h11, hax, hm2, hx2⟩, k2⟩ => ?_))
    have hL := VG.Proof.MlDsa.X86_64.Message.slay_ok hp h h8
    have hg2 : ∀ r, r ∉ [Reg.r10, .r11, .rax] → s2.gpr r = s.gpr r := fun r hr => (k2.gpr hr).trans (by rw [hg1])
    have hsp2 : s2.gpr .rsp = (VG.Proof.MlDsa.X86_64.Message.slay p s).B + BitVec.ofNat 64 112 := by
      rw [hg2 _ (by decide), VG.Proof.MlDsa.X86_64.Message.slay_B]
    have hn : 8 * signRegs.length ≤ (s2.gpr .rsp).toNat := by
      rw [hg2 _ (by decide)]; have := h.sp; simp only [signRegs, List.length_cons, List.length_nil]; omega
    refine WP.frame (by decide) (by decide) (by decide) hn ?_
    refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Message.entry_ok hL rfl (by decide) hsp2 (k2.2.1.trans hrd1) (k2.2.2.trans hwr1)
      (VG.Proof.MlDsa.X86_64.Message.signRegs_vals hg2 h10 h11 hax) (hg2 _ (by decide)))
      fun t ⟨hc, htw, htsp⟩ => ?_)
    have hsk := VG.Proof.MlDsa.X86_64.Message.skLen_ge hp
    have wtr : Within ⟨(VG.Proof.MlDsa.X86_64.Message.slay p s).key + BitVec.ofNat 64 64, 64⟩ (VG.Proof.MlDsa.X86_64.Message.slay p s).KEY :=
      within_off _ (show 64 + 64 ≤ p.skLen by omega)
    refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Message.muHash_ok hL rfl hc (tr := .slotOff fKey 64) (by decide)
      (fun t' hc' => by rw [hc'.slotOff, fKey, hc'.pKey]) ⟨_, List.mem_append_left _ hL.inKey, wtr⟩
      ((hL.xKey.symm.sub_left wtr.sub).sub_right (Region.sub_prefix (by decide : 200 ≤ 1024)))
      ((hL.xKey.symm.sub_left wtr.sub).sub_right (Offset.sub_base _ (by decide : 200 + 640 ≤ 1024)))
      ((hL.kKey.sub_left (Region.sub_prefix (by decide : 40 ≤ 112))).sub_right wtr.sub))
      fun t₁ ⟨hc₁, hf₁, hμ⟩ => ?_)
    refine WP.mono (VG.Proof.MlDsa.X86_64.Message.signCall_ok hS hp h h8 hc₁) fun s' ⟨hrd', hwr', hsp', hcs', hx', hf', hq⟩ => ?_
    have hm₀ : s2.mem = s.mem := hm2
    refine ⟨by rw [hsp', hc₁.rsp, ← htsp, hc.rsp], by rw [hwr', hc₁.wr, ← htw, hc.wr], ?_, ?_⟩
    · -- The calling convention.
      refine ⟨fun r hr => ?_, ?_, ?_⟩
      · by_cases hr' : r = .rsp
        · subst hr'
          rw [popped_rsp, hsp', hc₁.rsp, Lay.SP, add_add, show 40 + 8 * signRegs.length = 112 from rfl, VG.Proof.MlDsa.X86_64.Message.slay_B]
        · rw [popped_gpr _ _ _ hr' (VG.Proof.MlDsa.X86_64.Message.cs_r11 r hr), hcs' r hr, hc₁.cs r hr hr', hg2 r (VG.Proof.MlDsa.X86_64.Message.cs_tmp r hr)]
      · have eR : VG.Proof.MlDsa.X86_64.Message.rRet s = ⟨(VG.Proof.MlDsa.X86_64.Message.slay p s).B + BitVec.ofNat 64 112, 8⟩ := by rw [VG.Proof.MlDsa.X86_64.Message.slay_B]
        have dB : ∀ k, k ≤ 112 → (VG.Proof.MlDsa.X86_64.Message.rRet s).Disjoint ⟨(VG.Proof.MlDsa.X86_64.Message.slay p s).B, k⟩ := fun k hk => by
          rw [eR]; exact Offset.disjoint_base _ hk (by have := hL.nB; omega)
        rw [popped_mem, hf'.readW (r := VG.Proof.MlDsa.X86_64.Message.rRet s) (Region.contains_self _ _) (fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl
            · exact h.retSig
            · exact h.retScr.sub_right (VG.Proof.MlDsa.X86_64.Message.scrMu_sub p s)
            · exact dB 40 (by decide)) (by decide),
          hc₁.frame.readW (r := VG.Proof.MlDsa.X86_64.Message.rRet s) (Region.contains_self _ _) (fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl
            · exact h.retScr.sub_right (VG.Proof.MlDsa.X86_64.Message.slay_X p s).sub
            · exact dB 112 (by decide)) (by decide), hm₀]
      · rw [popped_mxcsr, hx', hc₁.mx, hx2, hx1]
    · sig_post [signMessageContract, signMessageSig, X86_64.abi, X86_64.argRegs, List.range, List.range.loop]
      rw [formatMessage_some (by rw [Proof.MlKem.bytesAt_length]; exact h8)]
      simp only [signInternal, messageRep, skTr]
      have ek : bytesAt t₁.mem (s.gpr .rdi) p.skLen = bytesAt s.mem (s.gpr .rdi) p.skLen := by
        rw [hc₁.bytesAt_eq (p := s.gpr .rdi) (n := p.skLen) hL.xKey hL.kKey (by have := h.nSk; omega), hm₀]
      have er : bytesAt t₁.mem (s.gpr .r9) 32 = bytesAt s.mem (s.gpr .r9) 32 := by
        rw [hc₁.bytesAt_eq (p := s.gpr .r9) (n := 32) (h.rndScr.symm.sub_left (VG.Proof.MlDsa.X86_64.Message.slay_X p s).sub) h.stkRnd (by decide), hm₀]
      have etr : bytesAt t.mem ((VG.Proof.MlDsa.X86_64.Message.slay p s).key + BitVec.ofNat 64 64) 64 =
          ((bytesAt s.mem (s.gpr .rdi) p.skLen).drop 64).take 64 := by
        rw [hc.bytesAt_eq (hL.xKey.sub_right wtr.sub) (hL.kKey.sub_right wtr.sub) (by decide), hm₀,
          Proof.MlKem.bytesAt_slice _ _ (by omega)]
        rfl
      rw [ek, er, hμ, etr, hm₀] at hq
      simp only [VG.Proof.MlDsa.X86_64.Message.hdrBytes, Proof.MlKem.bytesAt_length, List.append_assoc] at hq ⊢
      exact hq
  · rw [decide_eq_false h8] at hc1
    refine VG.Proof.MlDsa.X86_64.Message.wp_ite_f hc1 ?_
    xrun [show (2 : BitVec 32) = BitVec.ofNat 32 2 from rfl]
    refine ⟨⟨fun r hr => ?_, by rw [RegUpd.mem_setReg, hm1], by rw [RegUpd.mxcsr_setReg, hx1]⟩, ?_⟩
    · rw [RegUpd.gpr_setReg_of_ne _ _ (fun e => by subst e; revert hr; decide), hg1]
    · sig_post [signMessageContract, signMessageSig, X86_64.abi, X86_64.argRegs, List.range, List.range.loop]
      rw [formatMessage_none (by rw [Proof.MlKem.bytesAt_length]; omega)]
      rfl

end VG.Proof.MlDsa.X86_64.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignCT`. -/
section

/-!
# ML-DSA on x86-64, `sign_message`: constant time

Untrusted: everything here is checked by Lean. Two runs from states that
satisfy the contract and agree on its public data, which includes what
`signMessageLeak` says (`signI`), leak the same: the branch on `ctx_len`,
the moves and the frame depend only on the pointers and the lengths; the
hashing leaks only the layout (`muHash_tr`); and the call of the signing
function on `μ` leaks only `signLeak` of the key, `μ` and `rnd`, which is
`signMessageLeak` of the inputs (`signCall_tr`).
-/

namespace VG.Proof.MlDsa.X86_64.Message

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.X86_64 (Keep RelCT.postDep)
open VG.Proof.MlDsa.X86_64.Sign (signK scrLen)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable {p : Params}

/-- What the contract says two runs agree on, beyond the pointers and lengths. -/
def signI (p : Params) (L : VG.Proof.MlDsa.X86_64.Message.Lay) (m₁ m₂ : Mem) : Prop :=
  signMessageLeak p (bytesAt m₁ L.key p.skLen) (bytesAt m₁ L.msg L.len.toNat) (bytesAt m₁ L.ctx L.ctxLen.toNat)
      (bytesAt m₁ L.rnd 32) =
    signMessageLeak p (bytesAt m₂ L.key p.skLen) (bytesAt m₂ L.msg L.len.toNat)
      (bytesAt m₂ L.ctx L.ctxLen.toNat) (bytesAt m₂ L.rnd 32)

/-- The layout is that of a run of `sign_message` from a state with the
memory `m`, past the branch on `ctx_len`. -/
def SOk (p : Params) (L : VG.Proof.MlDsa.X86_64.Message.Lay) (m : Mem) : Prop :=
  ∃ σ, VG.Proof.MlDsa.X86_64.Message.SPre p σ ∧ (σ.gpr .r8).toNat < 256 ∧ VG.Proof.MlDsa.X86_64.Message.slay p σ = L ∧ σ.mem = m

/-- `μ` at `X + 840`. -/
def MuOk (L : VG.Proof.MlDsa.X86_64.Message.Lay) (m : Mem) (t : State) : Prop :=
  bytesAt t.mem L.MU 64 = H (bytesAt m (L.key + BitVec.ofNat 64 64) 64 ++ VG.Proof.MlDsa.X86_64.Message.hdrBytes L ++
    bytesAt m L.ctx L.ctxLen.toNat ++ bytesAt m L.msg L.len.toNat) 64

/-- What `sign_message` leaks is what the signing function on `μ` leaks, for
the `μ` it computes. -/
theorem leak_eq {L : VG.Proof.MlDsa.X86_64.Message.Lay} (hL : L.Ok) (hk : L.keyLen = p.skLen) (m : Mem) :
    signMessageLeak p (bytesAt m L.key p.skLen) (bytesAt m L.msg L.len.toNat) (bytesAt m L.ctx L.ctxLen.toNat)
        (bytesAt m L.rnd 32) =
      signLeak p (bytesAt m L.key p.skLen) (H (bytesAt m (L.key + BitVec.ofNat 64 64) 64 ++ VG.Proof.MlDsa.X86_64.Message.hdrBytes L ++
        bytesAt m L.ctx L.ctxLen.toNat ++ bytesAt m L.msg L.len.toNat) 64) (bytesAt m L.rnd 32) := by
  have := hL.hKey
  rw [signMessageLeak, formatMessage_some (by rw [Proof.MlKem.bytesAt_length]; exact hL.ctxLt)]
  simp only [messageRep, skTr, VG.Proof.MlDsa.X86_64.Message.hdrBytes, Proof.MlKem.bytesAt_length, List.append_assoc]
  rw [Proof.MlKem.bytesAt_slice _ _ (by omega)]

/-- What a layout of `sign_message` says of `rnd`, `sig` and `scratch`. -/
structure SFacts (p : Params) (L : VG.Proof.MlDsa.X86_64.Message.Lay) : Prop where
  key : L.keyLen = p.skLen
  e : oE p = L.E
  xRnd : L.XS.Disjoint ⟨L.rnd, 32⟩
  kRnd : L.STK.Disjoint ⟨L.rnd, 32⟩
  inRnd : (⟨L.rnd, 32⟩ : Region) ∈ L.rd
  inSig : (⟨L.sig, p.sigLen⟩ : Region) ∈ L.wr
  inScr : ∃ R ∈ L.wr, Within ⟨L.scr, scrLen p⟩ R
  inMu : ∃ R ∈ L.wr, Within ⟨L.MU, 64⟩ R

theorem SOk.facts {L : VG.Proof.MlDsa.X86_64.Message.Lay} {m : Mem} (h : VG.Proof.MlDsa.X86_64.Message.SOk p L m) : VG.Proof.MlDsa.X86_64.Message.SFacts p L := by
  obtain ⟨σ, hσ, _, rfl, -⟩ := h
  exact ⟨rfl, rfl, hσ.rndScr.symm.sub_left (VG.Proof.MlDsa.X86_64.Message.slay_X p σ).sub, hσ.stkRnd, by simp [VG.Proof.MlDsa.X86_64.Message.slay, hσ.rd],
    by simp [VG.Proof.MlDsa.X86_64.Message.slay, hσ.wr], ⟨VG.Proof.MlDsa.X86_64.Message.rScr p σ, by simp [VG.Proof.MlDsa.X86_64.Message.slay, hσ.wr], within_base _ (by rw [VG.Proof.MlDsa.X86_64.Message.mScr_eq]; simp [scrLen, oE])⟩,
    ⟨VG.Proof.MlDsa.X86_64.Message.rScr p σ, by simp [VG.Proof.MlDsa.X86_64.Message.slay, hσ.wr], VG.Proof.MlDsa.X86_64.Message.mu_within p σ⟩⟩

/-- The registers after the moves of the arguments of the signing function on `μ`. -/
theorem signRegsL {L : VG.Proof.MlDsa.X86_64.Message.Lay} (hE : oE p = L.E) {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem} {t t1 : State}
    (hc : VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ t) (hm : VG.Proof.MlDsa.X86_64.Message.Moved (VG.Proof.MlDsa.X86_64.Message.signArgs p) t t1) :
    t1.gpr .rdi = L.key ∧ t1.gpr .rsi = L.MU ∧ t1.gpr .rdx = L.rnd ∧ t1.gpr .rcx = L.sig ∧
      t1.gpr .r8 = L.scr := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := VG.Proof.MlDsa.X86_64.Message.argsIn5 hm.1.1
  rw [hc.slot, fKey, hc.pKey] at e1
  rw [hc.aMu p hE] at e2
  rw [hc.slot, fRnd, hc.pRnd] at e3
  rw [hc.slot, fSig, hc.pSig] at e4
  rw [hc.slot, fScr, hc.pScr] at e5
  exact ⟨e1, e2, e3, e4, e5⟩

/-- Two runs of the call of the signing function on `μ`. -/
theorem signCall_tr {n : String} {c : Prog isa} (hS : VG.Proof.MlDsa.X86_64.Message.SignFn p c) (hp : p ∈ VG.Proof.MlDsa.X86_64.Message.params) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Message.Two (VG.Proof.MlDsa.X86_64.Message.signI p) fun L m t => VG.Proof.MlDsa.X86_64.Message.SOk p L m ∧ VG.Proof.MlDsa.X86_64.Message.MuOk L m t) (callA n c (VG.Proof.MlDsa.X86_64.Message.signArgs p)) fun _ _ => True := by
  refine VG.Proof.MlDsa.X86_64.Message.call_tr (VG.Proof.MlDsa.X86_64.Message.signArgs_ok hp) hS.ok hS.ct
    (fun L => [⟨L.key, p.skLen⟩, ⟨L.MU, 64⟩, ⟨L.rnd, 32⟩]) (fun L => [⟨L.sig, p.sigLen⟩, ⟨L.scr, scrLen p⟩])
    (fun L g mx m₀ t t1 hL hc hφ hm => ?_) (fun L g₁ g₂ mx₁ mx₂ m₁ m₂ a b a1 b1 hL hi c₁ c₂ φ₁ φ₂ f₁ f₂ => ?_)
    (fun L g mx m₀ t hL hc hφ => ?_)
  · obtain ⟨⟨σ, hσ, h8, rfl, -⟩, -⟩ := hφ
    exact VG.Proof.MlDsa.X86_64.Message.signK_pre hp hσ h8 hc hm
  · have F := φ₁.1.facts
    obtain ⟨x1, x2, x3, x4, x5⟩ := VG.Proof.MlDsa.X86_64.Message.signRegsL F.e c₁ f₁
    obtain ⟨y1, y2, y3, y4, y5⟩ := VG.Proof.MlDsa.X86_64.Message.signRegsL F.e c₂ f₂
    have hc₁ := c₁.regs f₁.2.2.1 f₁.2.2.2 f₁.1.2.1 f₁.1.2.2 fun r hr => f₁.2.gpr (VG.Proof.MlDsa.X86_64.Message.argRegs_cs r hr)
    have hc₂ := c₂.regs f₂.2.2.1 f₂.2.2.2 f₂.1.2.1 f₂.1.2.2 fun r hr => f₂.2.gpr (VG.Proof.MlDsa.X86_64.Message.argRegs_cs r hr)
    simp only [signK, State.withRegions_mem, VG.Proof.MlDsa.X86_64.Message.gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp),
      VG.Proof.MlDsa.X86_64.Message.gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp), VG.Proof.MlDsa.X86_64.Message.gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp),
      VG.Proof.MlDsa.X86_64.Message.gpr_ce _ _ _ (by decide : Reg.rcx ≠ .rsp), VG.Proof.MlDsa.X86_64.Message.gpr_ce _ _ _ (by decide : Reg.r8 ≠ .rsp), VG.Proof.MlDsa.X86_64.Message.rsp_ce,
      x1, x2, x3, y1, y2, y3, f₁.2.gpr (by decide : Reg.rsp ∉ argRegs), f₂.2.gpr (by decide : Reg.rsp ∉ argRegs),
      c₁.rsp, c₂.rsp, true_and]
    refine ⟨x4.trans y4.symm, x5.trans y5.symm, ?_⟩
    have hk := hL.hKey
    have hkk := F.key
    have ek : ∀ {g mx m₀} {a a1 : State}, VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ a → VG.Proof.MlDsa.X86_64.Message.Moved (VG.Proof.MlDsa.X86_64.Message.signArgs p) a a1 →
        bytesAt a1.callEntry.mem L.key p.skLen = bytesAt m₀ L.key p.skLen := fun c f => by
      rw [(c.regs f.2.2.1 f.2.2.2 f.1.2.1 f.1.2.2 fun r hr => f.2.gpr (VG.Proof.MlDsa.X86_64.Message.argRegs_cs r hr)).ce_bytesAt
        (hL.stk_r (r := ⟨L.key, p.skLen⟩) (F.key ▸ hL.kKey) (d := 32) (n := 8) (by decide)) (by omega),
        f.1.2.1, c.bytesAt_eq (F.key ▸ hL.xKey) (F.key ▸ hL.kKey) (by omega)]
    have er : ∀ {g mx m₀} {a a1 : State}, VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ a → VG.Proof.MlDsa.X86_64.Message.Moved (VG.Proof.MlDsa.X86_64.Message.signArgs p) a a1 →
        bytesAt a1.callEntry.mem L.rnd 32 = bytesAt m₀ L.rnd 32 := fun c f => by
      rw [(c.regs f.2.2.1 f.2.2.2 f.1.2.1 f.1.2.2 fun r hr => f.2.gpr (VG.Proof.MlDsa.X86_64.Message.argRegs_cs r hr)).ce_bytesAt
        (hL.stk_r F.kRnd (d := 32) (n := 8) (by decide)) (by decide), f.1.2.1,
        c.bytesAt_eq F.xRnd F.kRnd (by decide)]
    have eμ : ∀ {g mx m₀} {a a1 : State}, VG.Proof.MlDsa.X86_64.Message.Ctx L g mx m₀ a → VG.Proof.MlDsa.X86_64.Message.Moved (VG.Proof.MlDsa.X86_64.Message.signArgs p) a a1 →
        bytesAt a1.callEntry.mem L.MU 64 = bytesAt a.mem L.MU 64 := fun c f => by
      rw [(c.regs f.2.2.1 f.2.2.2 f.1.2.1 f.1.2.2 fun r hr => f.2.gpr (VG.Proof.MlDsa.X86_64.Message.argRegs_cs r hr)).ce_bytesAt
        (hL.stk_x (d := 32) (n := 8) (e := 840) (k := 64) (by decide) (by decide)) (by decide), f.1.2.1]
    rw [ek c₁ f₁, ek c₂ f₂, er c₁ f₁, er c₂ f₂, eμ c₁ f₁, eμ c₂ f₂, φ₁.2, φ₂.2,
      Sign.signLeakT_eq_signLeak, Sign.signLeakT_eq_signLeak, ← VG.Proof.MlDsa.X86_64.Message.leak_eq hL F.key, ← VG.Proof.MlDsa.X86_64.Message.leak_eq hL F.key]
    exact hi
  · have F := hφ.1.facts
    refine ⟨fun r hr => ?_, fun r hr => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_append_left _ (F.key ▸ hL.inKey), within_self _⟩
      · obtain ⟨R, hR, hw⟩ := F.inMu; exact ⟨R, by simp [hR], hw⟩
      · exact ⟨_, List.mem_append_left _ F.inRnd, within_self _⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, F.inSig, within_self _⟩
      · exact F.inScr

/-- The public data of the contract, spelled out. -/
structure SPub (p : Params) (s₁ s₂ : State) : Prop where
  rsp : s₁.gpr .rsp = s₂.gpr .rsp
  leak : signMessageLeak p (bytesAt s₁.mem (s₁.gpr .rdi) p.skLen) (bytesAt s₁.mem (s₁.gpr .rsi) (s₁.gpr .rdx).toNat)
      (bytesAt s₁.mem (s₁.gpr .rcx) (s₁.gpr .r8).toNat) (bytesAt s₁.mem (s₁.gpr .r9) 32) =
    signMessageLeak p (bytesAt s₂.mem (s₂.gpr .rdi) p.skLen) (bytesAt s₂.mem (s₂.gpr .rsi) (s₂.gpr .rdx).toNat)
      (bytesAt s₂.mem (s₂.gpr .rcx) (s₂.gpr .r8).toNat) (bytesAt s₂.mem (s₂.gpr .r9) 32)
  rdi : s₁.gpr .rdi = s₂.gpr .rdi
  rsi : s₁.gpr .rsi = s₂.gpr .rsi
  rdx : s₁.gpr .rdx = s₂.gpr .rdx
  rcx : s₁.gpr .rcx = s₂.gpr .rcx
  r8 : s₁.gpr .r8 = s₂.gpr .r8
  r9 : s₁.gpr .r9 = s₂.gpr .r9
  a0 : stackArg s₁ 0 = stackArg s₂ 0
  a1 : stackArg s₁ 1 = stackArg s₂ 1

theorem sPub_of {s₁ s₂ : State} (h : (signMessageContract p X86_64.abi 112).pub s₁ s₂) : VG.Proof.MlDsa.X86_64.Message.SPub p s₁ s₂ := by
  sig_pub [signMessageContract, signMessageSig, X86_64.abi, X86_64.argRegs, List.range, List.range.loop] at h
  obtain ⟨a, b, c, d, e, f, g, h, i, j⟩ := h
  exact ⟨a, b, c, d, e, f, g, h, i, j⟩

/-- Two runs from states agreeing on the public data have the same layout. -/
theorem slay_eq {s₁ s₂ : State} (h₁ : VG.Proof.MlDsa.X86_64.Message.SPre p s₁) (h₂ : VG.Proof.MlDsa.X86_64.Message.SPre p s₂) (h : VG.Proof.MlDsa.X86_64.Message.SPub p s₁ s₂) : VG.Proof.MlDsa.X86_64.Message.slay p s₁ = VG.Proof.MlDsa.X86_64.Message.slay p s₂ := by
  have e1 : s₁.rd = s₂.rd := by
    rw [h₁.rd, h₂.rd]; simp only [VG.Proof.MlDsa.X86_64.Message.rSk, VG.Proof.MlDsa.X86_64.Message.rMsg, VG.Proof.MlDsa.X86_64.Message.rCtx, VG.Proof.MlDsa.X86_64.Message.rRnd, VG.Proof.MlDsa.X86_64.Message.rArgs, stackArgAddr, h.rdi, h.rsi, h.rdx, h.rcx, h.r8,
      h.r9, h.rsp]
  have e2 : s₁.wr = s₂.wr := by
    rw [h₁.wr, h₂.wr]; simp only [VG.Proof.MlDsa.X86_64.Message.rSig, VG.Proof.MlDsa.X86_64.Message.rScr, h.a0, h.a1]
  simp only [VG.Proof.MlDsa.X86_64.Message.slay, h.rsp, h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, h.a0, h.a1, e1, e2]

/-- The body of the frame. -/
theorem signBody_tr {n : String} {c : Prog isa} (hS : VG.Proof.MlDsa.X86_64.Message.SignFn p c) (hp : p ∈ VG.Proof.MlDsa.X86_64.Message.params) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Message.Two (VG.Proof.MlDsa.X86_64.Message.signI p) fun L m _ => VG.Proof.MlDsa.X86_64.Message.SOk p L m)
      (.seq (muHash p (.slotOff fKey 64)) (callA n c (VG.Proof.MlDsa.X86_64.Message.signArgs p))) fun _ _ => True := by
  have hE := VG.Proof.MlDsa.X86_64.Message.oE_lt hp
  have mh := VG.Proof.MlDsa.X86_64.Message.muHash_tr (I := VG.Proof.MlDsa.X86_64.Message.signI p) (Φ := fun L m _ => VG.Proof.MlDsa.X86_64.Message.SOk p L m) hE (fun _ _ _ h => h.facts.e)
    (tr := .slotOff fKey 64) (by decide) (fun L => L.key + BitVec.ofNat 64 64)
    (fun L g mx m t hc _ => by rw [hc.slotOff, fKey, hc.pKey])
    fun L hL => by
      have := hL.hKey
      have w : Within ⟨L.key + BitVec.ofNat 64 64, 64⟩ L.KEY := within_off _ (by omega)
      exact ⟨⟨_, List.mem_append_left _ hL.inKey, w⟩,
        (hL.xKey.symm.sub_left w.sub).sub_right (Region.sub_prefix (by decide : 200 ≤ 1024)),
        (hL.xKey.symm.sub_left w.sub).sub_right (Offset.sub_base _ (by decide : 200 + 640 ≤ 1024)),
        (hL.kKey.sub_left (Region.sub_prefix (by decide : 40 ≤ 112))).sub_right w.sub⟩
  have mh' := VG.Proof.MlDsa.X86_64.Message.two_wp (I := VG.Proof.MlDsa.X86_64.Message.signI p) (Φ := fun L m _ => VG.Proof.MlDsa.X86_64.Message.SOk p L m) (Ψ := fun L m t => VG.Proof.MlDsa.X86_64.Message.SOk p L m ∧ VG.Proof.MlDsa.X86_64.Message.MuOk L m t) mh
    fun L g mx m₀ t hL hc hφ => by
      have := hL.hKey
      have w : Within ⟨L.key + BitVec.ofNat 64 64, 64⟩ L.KEY := within_off _ (by omega)
      refine WP.mono (VG.Proof.MlDsa.X86_64.Message.muHash_ok hL hφ.facts.e hc (tr := .slotOff fKey 64) (by decide)
        (fun t' hc' => by rw [hc'.slotOff, fKey, hc'.pKey]) ⟨_, List.mem_append_left _ hL.inKey, w⟩
        ((hL.xKey.symm.sub_left w.sub).sub_right (Region.sub_prefix (by decide : 200 ≤ 1024)))
        ((hL.xKey.symm.sub_left w.sub).sub_right (Offset.sub_base _ (by decide : 200 + 640 ≤ 1024)))
        ((hL.kKey.sub_left (Region.sub_prefix (by decide : 40 ≤ 112))).sub_right w.sub))
        fun t' ⟨hc', _, hμ⟩ => ⟨hc', hφ, ?_⟩
      unfold VG.Proof.MlDsa.X86_64.Message.MuOk
      rw [hμ, hc.bytesAt_eq (hL.xKey.sub_right w.sub) (hL.kKey.sub_right w.sub) (by decide)]
  exact mh'.seq (VG.Proof.MlDsa.X86_64.Message.signCall_tr hS hp)

/-- The entry states of two runs: the precondition and the public data. -/
abbrev SP2 (p : Params) (x y : State) : Prop :=
  (signMessageContract p X86_64.abi 112).pre x ∧ (signMessageContract p X86_64.abi 112).pre y ∧
    (signMessageContract p X86_64.abi 112).pub x y

/-- After `cmp`. -/
abbrev ACmp (x x1 : State) : Prop :=
  x1.gpr = x.gpr ∧ x1.mem = x.mem ∧ x1.rd = x.rd ∧ x1.wr = x.wr ∧ x1.mxcsr = x.mxcsr ∧
    isa.eval .b x1 = some (decide ((x.gpr .r8).toNat < 256))

/-- After the moves before the push. -/
abbrev AMov (x x2 : State) : Prop :=
  (x.gpr .r8).toNat < 256 ∧ ((x2.gpr .r10 = stackArg x 0 ∧ x2.gpr .r11 = stackArg x 1 ∧ x2.gpr .rax = 0 ∧
    x2.mem = x.mem ∧ x2.mxcsr = x.mxcsr) ∧ (∀ r, r ∉ [Reg.r10, .r11, .rax] → x2.gpr r = x.gpr r) ∧
    x2.rd = x.rd ∧ x2.wr = x.wr)

theorem spOnly_nomem {i : Instr} (h : ∀ s, isa.addrs i s = []) (hc : Taint.clobbers i .rsp = false) : VG.Proof.MlDsa.X86_64.Message.SpOnly i :=
  ⟨fun s₁ s₂ _ => by rw [h, h], hc⟩

theorem signMessage_ct {n : String} {c : Prog isa} (hS : VG.Proof.MlDsa.X86_64.Message.SignFn p c) (hp : p ∈ VG.Proof.MlDsa.X86_64.Message.params) :
    ConstantTime isa (signMessageContract p X86_64.abi 112).pre (signMessageContract p X86_64.abi 112).pub
      (signMessage n c p) := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  have e0 : (fun s₁ s₂ => (signMessageContract p X86_64.abi 112).pre s₁ ∧
      (signMessageContract p X86_64.abi 112).pre s₂ ∧ (signMessageContract p X86_64.abi 112).pub s₁ s₂) =
      VG.Proof.MlDsa.X86_64.Message.Ghost (VG.Proof.MlDsa.X86_64.Message.SP2 p) (fun x a => a = x) := by
    funext a b; apply propext
    exact ⟨fun h => ⟨a, b, h, rfl, rfl⟩, fun ⟨_, _, h, e₁, e₂⟩ => e₁ ▸ e₂ ▸ h⟩
  rw [e0]
  unfold signMessage top
  -- `cmp r8, 256`.
  have hcmp := VG.Proof.MlDsa.X86_64.Message.ghost_step (P := VG.Proof.MlDsa.X86_64.Message.SP2 p) (A := fun x a => a = x) (B := VG.Proof.MlDsa.X86_64.Message.ACmp) (c := .block [.alu .cmp .r8 (.imm 256)])
    (VG.Proof.MlDsa.X86_64.Message.block_rsp_tr (fun i hi => by
        simp only [List.mem_singleton] at hi; subst hi; exact VG.Proof.MlDsa.X86_64.Message.spOnly_nomem (fun _ => rfl) rfl)
      fun a b ⟨x, y, hxy, e₁, e₂⟩ => by subst e₁ e₂; exact (VG.Proof.MlDsa.X86_64.Message.sPub_of hxy.2.2).rsp)
    fun x y a b _ e₁ e₂ => by subst e₁ e₂; exact ⟨VG.Proof.MlDsa.X86_64.Message.cmp_ok _, VG.Proof.MlDsa.X86_64.Message.cmp_ok _⟩
  refine RelCT.seq hcmp (RelCT.ite (fun a b ⟨x, y, hxy, f₁, f₂⟩ => by
    rw [f₁.2.2.2.2.2, f₂.2.2.2.2.2, (VG.Proof.MlDsa.X86_64.Message.sPub_of hxy.2.2).r8]) ?_ ?_)
  · -- `ctx_len < 256`.
    have hmov := VG.Proof.MlDsa.X86_64.Message.ghost_step (P := VG.Proof.MlDsa.X86_64.Message.SP2 p) (A := fun x a => VG.Proof.MlDsa.X86_64.Message.ACmp x a ∧ (x.gpr .r8).toNat < 256) (B := VG.Proof.MlDsa.X86_64.Message.AMov)
      (c := .block [.mov .r10 (.mem (stk 8)), .mov .r11 (.mem (stk 16)), .mov32 .rax (.imm 0)])
      (VG.Proof.MlDsa.X86_64.Message.block_rsp_tr (fun i hi => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl | rfl
          · exact ⟨fun s₁ s₂ h => by simp [addrs, srcAddrs, State.ea, stk, h], rfl⟩
          · exact ⟨fun s₁ s₂ h => by simp [addrs, srcAddrs, State.ea, stk, h], rfl⟩
          · exact VG.Proof.MlDsa.X86_64.Message.spOnly_nomem (fun _ => rfl) rfl)
        fun a b ⟨x, y, hxy, f₁, f₂⟩ => by rw [f₁.1.1, f₂.1.1]; exact (VG.Proof.MlDsa.X86_64.Message.sPub_of hxy.2.2).rsp)
      fun x y a b hxy f₁ f₂ => by
        have mv : ∀ {x a : State}, (signMessageContract p X86_64.abi 112).pre x → VG.Proof.MlDsa.X86_64.Message.ACmp x a →
            (x.gpr .r8).toNat < 256 → WP isa (.block [.mov .r10 (.mem (stk 8)), .mov .r11 (.mem (stk 16)),
              .mov32 .rax (.imm 0)]) a (VG.Proof.MlDsa.X86_64.Message.AMov x) := fun hx f h8 =>
          WP.mono (VG.Proof.MlDsa.X86_64.Message.signMov_ok (VG.Proof.MlDsa.X86_64.Message.sPre_of hx) f.1 f.2.1 f.2.2.1) fun x2 ⟨h, k⟩ =>
            ⟨h8, ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.trans f.2.2.2.2.1⟩,
              fun r hr => (k.gpr hr).trans (by rw [f.1]), k.2.1.trans f.2.2.1, k.2.2.trans f.2.2.2.1⟩
        exact ⟨mv hxy.1 f₁.1 f₁.2, mv hxy.2.1 f₂.1 f₂.2⟩
    refine RelCT.seq (RelCT.mono hmov (fun a b ⟨⟨x, y, hxy, f₁, f₂⟩, hc⟩ => ⟨x, y, hxy, ⟨f₁, ?_⟩, ⟨f₂, ?_⟩⟩)
      fun _ _ h => h) ?_
    · rw [f₁.2.2.2.2.2] at hc; simpa using hc
    · rw [f₁.2.2.2.2.2, (VG.Proof.MlDsa.X86_64.Message.sPub_of hxy.2.2).r8, ← f₂.2.2.2.2.2] at hc
      rw [f₂.2.2.2.2.2] at hc; simpa using hc
    refine RelCT.frame (R := fun _ _ => True) (fun a b ⟨x, y, hxy, f₁, f₂⟩ => by
      rw [f₁.2.2.1 _ (by decide), f₂.2.2.1 _ (by decide)]; exact (VG.Proof.MlDsa.X86_64.Message.sPub_of hxy.2.2).rsp) ?_
    -- The frame's body, from the push.
    let A : State → State → Prop := fun x a => ∃ s₁, VG.Proof.MlDsa.X86_64.Message.AMov x s₁ ∧ a = pushed signRegs s₁
    let B : State → State → Prop := fun x t => (x.gpr .r8).toNat < 256 ∧ VG.Proof.MlDsa.X86_64.Message.Ctx (VG.Proof.MlDsa.X86_64.Message.slay p x) x.gpr x.mxcsr x.mem t
    have hdr := VG.Proof.MlDsa.X86_64.Message.ghost_step (P := VG.Proof.MlDsa.X86_64.Message.SP2 p) (A := A) (B := B) (c := .block setHdr)
      (VG.Proof.MlDsa.X86_64.Message.block_rsp_tr (fun i hi => by
          simp only [setHdr, List.mem_singleton] at hi; subst hi
          exact ⟨fun s₁ s₂ h => by simp [addrs, State.ea, stk, h], rfl⟩)
        fun a b ⟨x, y, hxy, ⟨s₁, f₁, e₁⟩, ⟨s₂, f₂, e₂⟩⟩ => by
          subst e₁ e₂
          rw [pushed_rsp, pushed_rsp, f₁.2.2.1 _ (by decide), f₂.2.2.1 _ (by decide), (VG.Proof.MlDsa.X86_64.Message.sPub_of hxy.2.2).rsp])
      fun x y a b hxy fa fb => by
        have en : ∀ {x a : State}, (signMessageContract p X86_64.abi 112).pre x → A x a →
            WP isa (.block setHdr) a (B x) := fun hx ⟨s₁, f, e⟩ => by
          subst e
          have h := VG.Proof.MlDsa.X86_64.Message.sPre_of hx
          have hL := VG.Proof.MlDsa.X86_64.Message.slay_ok hp h f.1
          refine WP.mono (VG.Proof.MlDsa.X86_64.Message.entry_ok hL rfl (by decide) (by rw [f.2.2.1 _ (by decide), VG.Proof.MlDsa.X86_64.Message.slay_B])
            (f.2.2.2.1.trans rfl) (f.2.2.2.2.trans rfl) (VG.Proof.MlDsa.X86_64.Message.signRegs_vals f.2.2.1 f.2.1.1 f.2.1.2.1 f.2.1.2.2.1)
            (f.2.2.1 _ (by decide))) fun t ⟨hc, _, _⟩ =>
            ⟨f.1, hc.congr (fun r hr _ => f.2.2.1 r (VG.Proof.MlDsa.X86_64.Message.cs_tmp r hr)) f.2.1.2.2.2.2 f.2.1.2.2.2.1⟩
        exact ⟨en hxy.1 fa, en hxy.2.1 fb⟩
    refine RelCT.seq (RelCT.mono hdr (fun a b ⟨s₁, s₂, ⟨x, y, hxy, f₁, f₂⟩, e₁, e₂⟩ =>
      ⟨x, y, hxy, ⟨s₁, f₁, e₁⟩, ⟨s₂, f₂, e₂⟩⟩) fun a b ⟨x, y, hxy, ⟨h8x, ca⟩, ⟨h8y, cb⟩⟩ => ?_)
      (VG.Proof.MlDsa.X86_64.Message.signBody_tr hS hp)
    have hx := VG.Proof.MlDsa.X86_64.Message.sPre_of hxy.1
    have hy := VG.Proof.MlDsa.X86_64.Message.sPre_of hxy.2.1
    have hpub := VG.Proof.MlDsa.X86_64.Message.sPub_of hxy.2.2
    have e := VG.Proof.MlDsa.X86_64.Message.slay_eq hx hy hpub
    refine ⟨VG.Proof.MlDsa.X86_64.Message.slay p x, x.gpr, y.gpr, x.mxcsr, y.mxcsr, x.mem, y.mem, VG.Proof.MlDsa.X86_64.Message.slay_ok hp hx h8x, ?_, ca, e ▸ cb,
      ⟨x, hx, h8x, rfl, rfl⟩, ⟨y, hy, h8y, e.symm, rfl⟩⟩
    have lk := hpub.leak
    rw [← hpub.rdi, ← hpub.rsi, ← hpub.rdx, ← hpub.rcx, ← hpub.r8, ← hpub.r9] at lk
    exact lk
  · exact VG.Proof.MlDsa.X86_64.Message.block_rsp_tr (fun i hi => by
        simp only [List.mem_singleton] at hi; subst hi; exact VG.Proof.MlDsa.X86_64.Message.spOnly_nomem (fun _ => rfl) rfl)
      fun a b ⟨⟨x, y, hxy, f₁, f₂⟩, _⟩ => by rw [f₁.1, f₂.1]; exact (VG.Proof.MlDsa.X86_64.Message.sPub_of hxy.2.2).rsp

end

end VG.Proof.MlDsa.X86_64.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignVerified`. -/
section

/-!
# ML-DSA on x86-64, `sign_message`: verified

Untrusted: everything here is checked by Lean. `signMessage n c p`, for any
signing function on `μ` `c` that `sign_message` can call (`SignFn`), is
verified against `signMessageContract p X86_64.abi 112`.
-/

namespace VG.Proof.MlDsa.X86_64.Message

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Message
open VG.Proof.MlDsa.Message
open VG.Spec.MlDsa

/-- A state satisfying the precondition. -/
def signSat (p : Params) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x3000 | .rcx => 0x3100 | .r9 => 0x3200 | .rsp => 0x80000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x80009 then 0x40 else if a = 0x80012 then 0x01 else 0
  rd := [⟨0x1000, p.skLen⟩, ⟨0x3000, 0⟩, ⟨0x3100, 0⟩, ⟨0x3200, 32⟩, ⟨0x80008, 16⟩]
  wr := [⟨0x4000, p.sigLen⟩, ⟨0x10000, VG.Proof.MlDsa.X86_64.Message.mScrLen p⟩]

theorem signMessage_sat {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Message.params) : ∃ s, (signMessageContract p X86_64.abi 112).pre s := by
  simp only [VG.Proof.MlDsa.X86_64.Message.params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · sig_implies_sat [signMessageContract, signMessageSig, X86_64.abi, X86_64.argRegs, List.range,
      List.range.loop] [signSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using VG.Proof.MlDsa.X86_64.Message.signSat mlDsa44
  · sig_implies_sat [signMessageContract, signMessageSig, X86_64.abi, X86_64.argRegs, List.range,
      List.range.loop] [signSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using VG.Proof.MlDsa.X86_64.Message.signSat mlDsa65
  · sig_implies_sat [signMessageContract, signMessageSig, X86_64.abi, X86_64.argRegs, List.range,
      List.range.loop] [signSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using VG.Proof.MlDsa.X86_64.Message.signSat mlDsa87

theorem signMessage_verified {p : Params} {n : String} {c : Prog isa} (hS : VG.Proof.MlDsa.X86_64.Message.SignFn p c) (hp : p ∈ VG.Proof.MlDsa.X86_64.Message.params) :
    Verified X86_64.target (signMessage n c p) (signMessageContract p X86_64.abi 112) :=
  ⟨fun _ h => let ⟨t, s', he, ha, hq⟩ := VG.Proof.MlDsa.X86_64.Message.signMessage_wp hS hp h; ⟨t, s', he, ha, hq⟩,
    VG.Proof.MlDsa.X86_64.Message.signMessage_ct hS hp, VG.Proof.MlDsa.X86_64.Message.signMessage_sat hp⟩

end VG.Proof.MlDsa.X86_64.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignFn`. -/
section

/-!
# ML-DSA on x86-64, `sign_message`: the signing functions on `μ` it calls

Untrusted: everything here is checked by Lean. `vg_mldsa*_sign`, with any
implementation `v` of the polynomial arithmetic, is a function
`sign_message` can call (`signFn`): its proofs give its contract, it never
writes `rsp`, and its calls nest at most four deep, which, as whether it
writes `rsp`, is checked on the code with the arithmetic's functions empty
(`Same`), given that theirs nest at most three deep.
-/

namespace VG.Proof.MlDsa.X86_64.Message

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlDsa.X86_64 (Comp Same Same.ok ArithImpl Code.allInstrs_of_all)
open VG.Proof.MlDsa.X86_64.Sign (primsWith prims_okWith sign_correct sign_ct sign_ctl sign_same Ok3)
open VG.Spec.MlDsa

/-- Calls nesting at most `n + 1` deep, from functions whose calls nest at most `n` deep. -/
theorem depthCompN (n : Nat) : Comp (fun c => decide (c.depth ≤ n + 1)) (fun c => decide (c.depth ≤ n)) := by
  refine ⟨fun a b => ?_, fun _ t e => ?_, fun _ _ => rfl, fun _ b => ?_, rfl⟩
  · simp only [Code.depth, Nat.max_le, Bool.decide_and]
  · simp only [Code.depth, Nat.max_le, Bool.decide_and]
  · simp only [Code.depth]
    exact decide_eq_decide.mpr (by omega)

/-- `NoSp` from evaluating the code. -/
abbrev noSpB (c : Prog isa) : Bool := c.allInstrs fun i => !Taint.clobbers i .rsp

theorem noSp_of {c : Prog isa} (h : VG.Proof.MlDsa.X86_64.Message.noSpB c = true) : NoSp c := Proof.MlKem.X86_64.nosp_of h

theorem noSpB_of {c : Prog isa} (h : NoSp c) : VG.Proof.MlDsa.X86_64.Message.noSpB c = true := by
  rw [VG.Proof.MlDsa.X86_64.Message.noSpB, Code.allInstrs_eq, List.all_eq_true]
  intro i hi; simp [h i hi]

theorem ok3_of {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Message.params) : Ok3 p := by
  simp only [VG.Proof.MlDsa.X86_64.Message.params, List.mem_cons, List.not_mem_nil, or_false] at hp
  exact hp

theorem sign0_noSp {p : Params} (h3 : Ok3 p) :
    VG.Proof.MlDsa.X86_64.Message.noSpB (Impl.MlDsa.X86_64.Sign.sign (primsWith .empty) p) = true := by
  rcases h3 with rfl | rfl | rfl <;> decide +kernel

theorem sign0_depth {p : Params} (h3 : Ok3 p) :
    decide ((Impl.MlDsa.X86_64.Sign.sign (primsWith .empty) p).depth ≤ 4) = true := by
  rcases h3 with rfl | rfl | rfl <;> decide +kernel

/-- `vg_mldsa*_sign`, with the polynomial arithmetic of `v`. -/
theorem signFn (v : ArithImpl) {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Message.params) :
    VG.Proof.MlDsa.X86_64.Message.SignFn p (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) p) := by
  have h3 := VG.Proof.MlDsa.X86_64.Message.ok3_of hp
  have dep : ∀ {c : Prog isa}, c.depth ≤ 3 → decide (c.depth ≤ 3) = true := fun h => decide_eq_true h
  have dep2 : ∀ {c : Prog isa}, c.depth ≤ 2 → decide (c.depth ≤ 3) = true := fun h => decide_eq_true (by omega)
  refine ⟨sign_correct (prims_okWith v) h3 (Proof.MlDsa.X86_64.Sign.sign_ctl v h3), sign_ct (prims_okWith v) h3,
    VG.Proof.MlDsa.X86_64.Message.noSp_of (Same.ok (sign_same (Comp.all _) (VG.Proof.MlDsa.X86_64.Message.noSpB_of v.ok.ntt.nosp) (VG.Proof.MlDsa.X86_64.Message.noSpB_of v.ok.invNtt.nosp)
      (VG.Proof.MlDsa.X86_64.Message.noSpB_of v.ok.mul.nosp) (VG.Proof.MlDsa.X86_64.Message.noSpB_of v.ok.mulAdd.nosp) (VG.Proof.MlDsa.X86_64.Message.noSpB_of v.ok.add.nosp) (VG.Proof.MlDsa.X86_64.Message.noSpB_of v.ok.sub.nosp)
      (VG.Proof.MlDsa.X86_64.Message.noSpB_of v.ok.rej4.nosp) (VG.Proof.MlDsa.X86_64.Message.noSpB_of v.ok.expandMask4.nosp) (VG.Proof.MlDsa.X86_64.Message.noSpB_of v.ok.highBits.nosp)
      (VG.Proof.MlDsa.X86_64.Message.noSpB_of v.ok.lowBits.nosp) (VG.Proof.MlDsa.X86_64.Message.noSpB_of v.ok.normLt.nosp) (VG.Proof.MlDsa.X86_64.Message.noSpB_of v.ok.makeHint.nosp) p) (VG.Proof.MlDsa.X86_64.Message.sign0_noSp h3)),
    of_decide_eq_true (Same.ok (sign_same (VG.Proof.MlDsa.X86_64.Message.depthCompN 3) (dep2 v.ok.ntt.depth) (dep2 v.ok.invNtt.depth)
      (dep2 v.ok.mul.depth) (dep2 v.ok.mulAdd.depth) (dep2 v.ok.add.depth) (dep2 v.ok.sub.depth)
      (dep v.ok.rej4.depth) (dep v.ok.expandMask4.depth) (dep2 v.ok.highBits.depth) (dep2 v.ok.lowBits.depth)
      (dep2 v.ok.normLt.depth) (dep2 v.ok.makeHint.depth) p) (VG.Proof.MlDsa.X86_64.Message.sign0_depth h3))⟩

theorem kabs_spSafe : Impl.Sha3.X86_64.Stream.absorb.all (fun i => !isa.writesSp i) = true := by decide +kernel
theorem kpad_spSafe : Impl.Sha3.X86_64.Stream.pad.all (fun i => !isa.writesSp i) = true := by decide +kernel
theorem ksqz_spSafe : Impl.Sha3.X86_64.Stream.squeeze.all (fun i => !isa.writesSp i) = true := by decide +kernel

theorem arg_wsp (d : Reg) (hd : d ∈ argRegs6) (a : Arg) : (a.mov d).all (fun i => !isa.writesSp i) = true := by
  simp only [argRegs6, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> cases a <;> rfl

theorem setArgs_wsp (as : List Arg) : (setArgs as).all (fun i => !isa.writesSp i) = true := by
  rw [List.all_eq_true]
  intro i hi
  simp only [setArgs, List.mem_flatMap] at hi
  obtain ⟨⟨d, a⟩, hm, hi⟩ := hi
  exact List.all_eq_true.mp (VG.Proof.MlDsa.X86_64.Message.arg_wsp d (List.of_mem_zip hm).1 a) i hi

theorem signMessage_spSafe {p : Params} {n : String} {c : Prog isa} (hc : c.all (fun i => !isa.writesSp i) = true) :
    (Impl.MlDsa.X86_64.Message.signMessage n c p).all (fun i => !isa.writesSp i) = true := by
  generalize hq : (fun i => !isa.writesSp i) = q at hc ⊢
  have ha : Impl.Sha3.X86_64.Stream.absorb.all q = true := hq ▸ VG.Proof.MlDsa.X86_64.Message.kabs_spSafe
  have hp' : Impl.Sha3.X86_64.Stream.pad.all q = true := hq ▸ VG.Proof.MlDsa.X86_64.Message.kpad_spSafe
  have hs : Impl.Sha3.X86_64.Stream.squeeze.all q = true := hq ▸ VG.Proof.MlDsa.X86_64.Message.ksqz_spSafe
  have hsa : ∀ as, (setArgs as).all q = true := fun as => hq ▸ VG.Proof.MlDsa.X86_64.Message.setArgs_wsp as
  have hmv : ∀ a, (Arg.mov .rdi a).all q = true := fun a => hq ▸ VG.Proof.MlDsa.X86_64.Message.arg_wsp .rdi (by decide) a
  simp only [Impl.MlDsa.X86_64.Message.signMessage, Impl.MlDsa.X86_64.Message.top,
    Impl.MlDsa.X86_64.Message.muHash, Impl.MlDsa.X86_64.Message.zeroSt, Impl.MlDsa.X86_64.Message.kabs,
    Impl.MlDsa.X86_64.Message.kpad, Impl.MlDsa.X86_64.Message.ksqz, Impl.MlDsa.X86_64.Message.callA, Code.all,
    hc, ha, hp', hs, hsa, hmv, Bool.and_true, Bool.true_and]
  subst hq
  decide

end VG.Proof.MlDsa.X86_64.Message

end
