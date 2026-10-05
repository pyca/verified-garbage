import VerifiedGarbage.Impl.Ed448.X86_64.SignCached
import VerifiedGarbage.Proof.Ed448.X86_64.Verify.Verified
import VerifiedGarbage.Proof.Ed448.X86_64.BaseVerified
import VerifiedGarbage.Proof.Ed448.PruneBytes
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Ed448.Signing

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86_64.SignCached.Layout`. -/
section

/-!
# Ed448 signing with a cached public key on x86-64: where everything is

The function's buffers and the 464 bytes of stack below its return address,
from `B` up (`Lay`): the frame (448 bytes, from `SP = B + 16`, `rsp` between
its push and pop), whose first 136 bytes (`DAT₁`: the header of `dom4` and
the hash) and last 192 (`DAT₂`: `k`, `s` and `r`) the code writes, and the 16
bytes below it that the calls use. `Ctx` is what holds between the frame's
push and pop: the permissions, `rsp`, the callee-saved registers, the
arguments in the frame, and that memory changed only in `scratch`, `out` and
the stack. `call_ok` runs a call of verified code that writes only within
`scratch`, `out` and the data of the frame in such a state.
-/

namespace VG.Proof.Ed448.X86_64.SignCached

open VG VG.X86_64 VG.Impl.Ed448.X86_64.SignCached
open VG.Impl.Ed448.X86_64.Verify (stk fPk fCtx fCtxLen fMsg fLen fScr)
open VG.Proof.Ed448.X86_64.Verify (Within within_off within_base within_self covers_of_within add_add sp_sub8
  sp_sub8' below_call_sub bytesAt_congr)
open VG.Spec.Sha3 (bytesAt)

/-! ## The layout -/

/-- The buffers, the lowest byte of the stack used (`rsp - 464` on entry),
and the permissions on entry. -/
structure Lay where
  B : Addr
  out : Addr
  seed : Addr
  pk : Addr
  ctx : Addr
  ctxLen : BitVec 64
  msg : Addr
  len : BitVec 64
  scr : Addr
  rd : List Region
  wr : List Region

namespace Lay

variable (L : VG.Proof.Ed448.X86_64.SignCached.Lay)

/-- `rsp` between the frame's push and pop. -/
abbrev SP : Addr := L.B + BitVec.ofNat 64 16
/-- The frame. -/
abbrev FR : Region := ⟨L.SP, 448⟩
/-- What the code writes in the frame: the header and the hash; `k`, `s` and `r`. -/
abbrev DAT₁ : Region := ⟨L.SP, 136⟩
abbrev DAT₂ : Region := ⟨L.SP + BitVec.ofNat 64 256, 192⟩
/-- The stack used: the frame and the 16 bytes below it. -/
abbrev STK : Region := ⟨L.B, 464⟩
/-- The return address. -/
abbrev RET : Region := ⟨L.B + BitVec.ofNat 64 464, 8⟩
/-- The Keccak state, the sponge functions' working space. -/
abbrev ST : Addr := L.scr
abbrev KS : Addr := L.scr + BitVec.ofNat 64 256
abbrev SCR : Region := ⟨L.scr, 8192⟩
abbrev OUT : Region := ⟨L.out, 114⟩
abbrev SEED : Region := ⟨L.seed, 57⟩
abbrev PK : Region := ⟨L.pk, 57⟩
abbrev MSG : Region := ⟨L.msg, L.len.toNat⟩
abbrev CTX : Region := ⟨L.ctx, L.ctxLen.toNat⟩
/-- The hash, `k`, `s` and `r`, in the frame. -/
abbrev H : Addr := L.SP + BitVec.ofNat 64 16
abbrev K : Addr := L.SP + BitVec.ofNat 64 256
abbrev S : Addr := L.SP + BitVec.ofNat 64 320
abbrev R : Addr := L.SP + BitVec.ofNat 64 384

/-- What the contract says of where everything is. -/
structure Ok : Prop where
  ctxLt : L.ctxLen.toNat < 256
  nB : L.B.toNat + 472 < 2 ^ 64
  wr : L.wr = [L.OUT, L.SCR]
  inSeed : L.SEED ∈ L.rd
  inPk : L.PK ∈ L.rd
  inCtx : L.CTX ∈ L.rd
  inMsg : L.MSG ∈ L.rd
  xSeed : L.SCR.Disjoint L.SEED
  xPk : L.SCR.Disjoint L.PK
  xCtx : L.SCR.Disjoint L.CTX
  xMsg : L.SCR.Disjoint L.MSG
  xOut : L.SCR.Disjoint L.OUT
  oSeed : L.OUT.Disjoint L.SEED
  oPk : L.OUT.Disjoint L.PK
  oCtx : L.OUT.Disjoint L.CTX
  oMsg : L.OUT.Disjoint L.MSG
  kScr : L.STK.Disjoint L.SCR
  kOut : L.STK.Disjoint L.OUT
  kSeed : L.STK.Disjoint L.SEED
  kPk : L.STK.Disjoint L.PK
  kCtx : L.STK.Disjoint L.CTX
  kMsg : L.STK.Disjoint L.MSG
  rScr : L.RET.Disjoint L.SCR
  rOut : L.RET.Disjoint L.OUT
  nOut : L.out.toNat + 114 ≤ 2 ^ 64
  nSeed : L.seed.toNat + 57 ≤ 2 ^ 64
  nPk : L.pk.toNat + 57 ≤ 2 ^ 64
  nCtx : L.ctx.toNat + L.ctxLen.toNat ≤ 2 ^ 64
  nMsg : L.msg.toNat + L.len.toNat ≤ 2 ^ 64
  nScr : L.scr.toNat + 8192 ≤ 2 ^ 64

end Lay

namespace Lay.Ok

variable {L : VG.Proof.Ed448.X86_64.SignCached.Lay}

theorem stk_x (h : L.Ok) {d n e k : Nat} (h₁ : d + n ≤ 464) (h₂ : e + k ≤ 8192) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
  (h.kScr.sub_left (Offset.sub_base _ h₁)).sub_right (Offset.sub_base _ h₂)

theorem stk_r (_h : L.Ok) {r : Region} (hr : L.STK.Disjoint r) {d n : Nat} (h₁ : d + n ≤ 464) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r :=
  hr.sub_left (Offset.sub_base _ h₁)

theorem x_r (_h : L.Ok) {r : Region} (hr : L.SCR.Disjoint r) {e k : Nat} (h₂ : e + k ≤ 8192) :
    Region.Disjoint ⟨L.scr + BitVec.ofNat 64 e, k⟩ r :=
  hr.sub_left (Offset.sub_base _ h₂)

theorem o_r (_h : L.Ok) {r : Region} (hr : L.OUT.Disjoint r) {e k : Nat} (h₂ : e + k ≤ 114) :
    Region.Disjoint ⟨L.out + BitVec.ofNat 64 e, k⟩ r :=
  hr.sub_left (Offset.sub_base _ h₂)

end Lay.Ok

/-! ## Between the frame's push and pop -/

/-- The state between the frame's push and pop: `g` and `mx` are the
registers and MXCSR on entry, `m₀` the memory. -/
structure Ctx (L : VG.Proof.Ed448.X86_64.SignCached.Lay) (g : Reg → BitVec 64) (mx : BitVec 32) (m₀ : Mem) (t : State) : Prop where
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
  pOut : t.mem.readW (L.SP + BitVec.ofNat 64 VG.Impl.Ed448.X86_64.SignCached.fOut) 64 = L.out
  pScr : t.mem.readW (L.SP + BitVec.ofNat 64 fScr) 64 = L.scr
  pSeed : t.mem.readW (L.SP + BitVec.ofNat 64 VG.Impl.Ed448.X86_64.SignCached.fSeed) 64 = L.seed
  frame : VG.Frame [L.SCR, L.OUT, L.STK] m₀ t.mem

namespace Ctx

variable {L : VG.Proof.Ed448.X86_64.SignCached.Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem} {t t' : State}

/-- Code that writes only caller-saved registers. -/
theorem regs (hc : VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hm : t'.mem = t.mem)
    (hmx : t'.mxcsr = t.mxcsr) (hg : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) : VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, (hg .rsp (by decide)).trans hc.rsp,
    fun r hr hr' => (hg r hr).trans (hc.cs r hr hr'), by rw [hmx]; exact hc.mx,
    by rw [hm]; exact hc.pPk, by rw [hm]; exact hc.pCtx, by rw [hm]; exact hc.pCtxLen,
    by rw [hm]; exact hc.pMsg, by rw [hm]; exact hc.pLen, by rw [hm]; exact hc.pOut,
    by rw [hm]; exact hc.pScr, by rw [hm]; exact hc.pSeed, by rw [hm]; exact hc.frame⟩

/-- The same state, with the entry registers, MXCSR and memory given by others equal to them. -/
theorem congr (hc : VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t) {g' : Reg → BitVec 64} {mx' : BitVec 32} {m₀' : Mem}
    (hg : ∀ r ∈ calleeSaved, r ≠ .rsp → g r = g' r) (hmx : mx = mx') (hm : m₀ = m₀') : VG.Proof.Ed448.X86_64.SignCached.Ctx L g' mx' m₀' t := by
  subst hmx hm
  exact ⟨hc.rd, hc.wr, hc.rsp, fun r hr hr' => (hc.cs r hr hr').trans (hg r hr hr'), hc.mx, hc.pPk, hc.pCtx,
    hc.pCtxLen, hc.pMsg, hc.pLen, hc.pOut, hc.pScr, hc.pSeed, hc.frame⟩

/-- A word of the frame is readable. -/
theorem inFr (hc : VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t) {d : Nat} (h₂ : d + 8 ≤ 448) :
    InRegions (t.rd ++ t.wr) (L.SP + BitVec.ofNat 64 d) 8 :=
  ⟨L.FR, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ h₂ (by omega)⟩

theorem inFrW (hc : VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t) {d n : Nat} (h₂ : d + n ≤ 448) :
    InRegions t.wr (L.SP + BitVec.ofNat 64 d) n :=
  ⟨L.FR, by rw [hc.wr]; simp, Offset.contains_base _ h₂ (by omega)⟩

/-- The return address of a call from the frame. -/
theorem ret (hc : VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t) : below (t.gpr .rsp) 8 = ⟨L.B + BitVec.ofNat 64 8, 8⟩ := by
  rw [hc.rsp]
  show (⟨L.B + BitVec.ofNat 64 16 - BitVec.ofNat 64 8, 8⟩ : Region) = _
  rw [sp_sub8']

/-- A byte of a region apart from `scratch`, `out` and the stack, as on entry. -/
theorem byte (hc : VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t) {R : Region} (hx : L.SCR.Disjoint R) (ho : L.OUT.Disjoint R)
    (hk : L.STK.Disjoint R) (hR : R.len ≤ 2 ^ 64) {i : Nat} (hi : i < R.len) :
    t.mem (R.base + BitVec.ofNat 64 i) = m₀ (R.base + BitVec.ofNat 64 i) :=
  Frame.bytes (R := R) hc.frame (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hx.symm
    · exact ho.symm
    · exact hk.symm) hR hi

theorem bytesAt_eq (hc : VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t) {p : Addr} {n : Nat} (hx : L.SCR.Disjoint ⟨p, n⟩)
    (ho : L.OUT.Disjoint ⟨p, n⟩) (hk : L.STK.Disjoint ⟨p, n⟩) (hn : n ≤ 2 ^ 64) :
    VG.Spec.Sha3.bytesAt t.mem p n = VG.Spec.Sha3.bytesAt m₀ p n :=
  bytesAt_congr fun _ hi => hc.byte (R := ⟨p, n⟩) hx ho hk hn hi

theorem ce_bytesAt (hc : VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t) {p : Addr} {n : Nat}
    (hd : Region.Disjoint ⟨L.B + BitVec.ofNat 64 8, 8⟩ ⟨p, n⟩) (hn : n ≤ 2 ^ 64) :
    VG.Spec.Sha3.bytesAt t.callEntry.mem p n = VG.Spec.Sha3.bytesAt t.mem p n :=
  bytesAt_congr fun _ hi => Verify.Ctx.ce_byte t (R := ⟨p, n⟩) (by rw [hc.ret]; exact hd) hn hi

end Ctx

/-- Where the code may write: `scratch`, `out`, and the data of the frame. -/
def WOk (L : VG.Proof.Ed448.X86_64.SignCached.Lay) (r : Region) : Prop := VG.Proof.Ed448.X86_64.Verify.Within r L.SCR ∨ VG.Proof.Ed448.X86_64.Verify.Within r L.OUT ∨ VG.Proof.Ed448.X86_64.Verify.Within r L.DAT₁ ∨ VG.Proof.Ed448.X86_64.Verify.Within r L.DAT₂

/-- The slots of the frame's arguments are apart from where the code writes
and from the stack below the frame. -/
theorem slot_disj {L : VG.Proof.Ed448.X86_64.SignCached.Lay} (hL : L.Ok) {d : Nat} (h₁ : 136 ≤ d) (h₂ : d + 8 ≤ 256) {r : Region}
    (hr : VG.Proof.Ed448.X86_64.SignCached.WOk L r ∨ r = ⟨L.B, 16⟩) : Region.Disjoint ⟨L.SP + BitVec.ofNat 64 d, 8⟩ r := by
  rw [Lay.SP, VG.Proof.Ed448.X86_64.Verify.add_add]
  rcases hr with (hr | hr | hr | hr) | rfl
  · exact (hL.stk_r hL.kScr (d := 16 + d) (n := 8) (by omega)).sub_right hr.sub
  · exact (hL.stk_r hL.kOut (d := 16 + d) (n := 8) (by omega)).sub_right hr.sub
  · have := Offset.disjoint L.B (d := 16 + d) (n := 8) (e := 16) (k := 136) (by omega) (by omega) (by omega)
    exact this.sub_right (by simpa [Lay.DAT₁, Lay.SP] using hr.sub)
  · have := Offset.disjoint L.B (d := 16 + d) (n := 8) (e := 272) (k := 192) (by omega) (by omega) (by omega)
    exact this.sub_right (by simpa [Lay.DAT₂, Lay.SP, VG.Proof.Ed448.X86_64.Verify.add_add] using hr.sub)
  · exact Offset.disjoint_base _ (by omega) (by omega)

/-- A state whose memory differs from that of a `Ctx` state only where the
code writes and in the 16 bytes below the frame. -/
theorem Ctx.of_frame {L : VG.Proof.Ed448.X86_64.SignCached.Lay} (hL : L.Ok) {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem} {t t' : State}
    (hc : VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hcs : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r)
    (hmx : t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10) {rs : List Region}
    (hf : VG.Frame (rs ++ [⟨L.B, 16⟩]) t.mem t'.mem) (hrs : ∀ r ∈ rs, VG.Proof.Ed448.X86_64.SignCached.WOk L r) :
    VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t' := by
  have keep : ∀ d, 136 ≤ d → d + 8 ≤ 256 →
      t'.mem.readW (L.SP + BitVec.ofNat 64 d) 64 = t.mem.readW (L.SP + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => hf.readW (Region.contains_self _ _) (fun r hr => VG.Proof.Ed448.X86_64.SignCached.slot_disj hL h₁ h₂ (by
      rcases List.mem_append.mp hr with hr | hr
      · exact .inl (hrs r hr)
      · simp only [List.mem_singleton] at hr; exact .inr hr)) (by decide)
  have hd₁ : Region.Sub L.DAT₁ L.STK := by
    have := Offset.sub_base L.B (d := 16) (n := 136) (k := 464) (by omega)
    simpa [Lay.DAT₁, Lay.SP] using this
  have hd₂ : Region.Sub L.DAT₂ L.STK := by
    have := Offset.sub_base L.B (d := 272) (n := 192) (k := 464) (by omega)
    simpa [Lay.DAT₂, Lay.SP, VG.Proof.Ed448.X86_64.Verify.add_add] using this
  refine ⟨hrd.trans hc.rd, hwr.trans hc.wr, (hcs .rsp (by decide)).trans hc.rsp,
    fun r hr hr' => (hcs r hr).trans (hc.cs r hr hr'), hmx.trans hc.mx,
    (keep 200 (by decide) (by decide)).trans hc.pPk, (keep 208 (by decide) (by decide)).trans hc.pCtx,
    (keep 216 (by decide) (by decide)).trans hc.pCtxLen, (keep 224 (by decide) (by decide)).trans hc.pMsg,
    (keep 232 (by decide) (by decide)).trans hc.pLen, (keep 240 (by decide) (by decide)).trans hc.pOut,
    (keep 248 (by decide) (by decide)).trans hc.pScr, (keep 136 (by decide) (by decide)).trans hc.pSeed,
    hc.frame.trans (Frame.sub hf fun r hr => ?_)⟩
  rcases List.mem_append.mp hr with hr | hr
  · rcases hrs r hr with h | h | h | h
    · exact ⟨L.SCR, by simp, h.sub⟩
    · exact ⟨L.OUT, by simp, h.sub⟩
    · exact ⟨L.STK, by simp, fun a ha => hd₁ a (h.sub a ha)⟩
    · exact ⟨L.STK, by simp, fun a ha => hd₂ a (h.sub a ha)⟩
  · simp only [List.mem_singleton] at hr; subst hr
    refine ⟨L.STK, by simp, ?_⟩
    have := Offset.sub_base L.B (d := 0) (n := 16) (k := 464) (by omega)
    simpa using this

/-! ## Calls -/

/-- A call of verified code from the frame, which nests calls at most once
more, reading regions within the permissions and writing only where the code
may, keeps `Ctx`. -/
theorem call_ok {L : VG.Proof.Ed448.X86_64.SignCached.Lay} (hL : L.Ok) {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}
    {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsp : NoSp c) (hd : c.depth ≤ 1) {t : State} (hc : VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t)
    {rd wr : List Region} (hpre : k.pre (t.callEntry.withRegions rd wr))
    (hsub : ∀ r ∈ rd, ∃ R ∈ L.rd ++ L.FR :: L.wr, VG.Proof.Ed448.X86_64.Verify.Within r R)
    (hwsub : ∀ r ∈ wr, VG.Proof.Ed448.X86_64.SignCached.WOk L r) {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ s' → VG.Frame (wr ++ [⟨L.B, 16⟩]) t.mem s'.mem →
      (∀ r, (∀ i ∈ instrs c, Taint.clobbers i r = false) → s'.gpr r = t.gpr r) →
      (∃ s₂ : State, s₂.mem = s'.mem ∧ (∀ r, r ≠ .rsp → s₂.gpr r = s'.gpr r) ∧
        k.post (t.callEntry.withRegions rd wr) s₂) → Q s') :
    WP isa (.call n c) t Q := by
  have hwX : ∀ r ∈ wr, ∃ R ∈ L.FR :: L.wr, VG.Proof.Ed448.X86_64.Verify.Within r R := fun r hr => by
    rcases hwsub r hr with h | h | h | h
    · exact ⟨L.SCR, by simp [hL.wr], h⟩
    · exact ⟨L.OUT, by simp [hL.wr], h⟩
    · exact ⟨L.FR, by simp, h.trans (VG.Proof.Ed448.X86_64.Verify.within_base _ (by decide))⟩
    · exact ⟨L.FR, by simp, h.trans (VG.Proof.Ed448.X86_64.Verify.within_off _ (by decide))⟩
  have hcov : Covers (rd ++ wr) (t.rd ++ t.wr) := by
    rw [hc.rd, hc.wr]
    refine covers_of_within fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · exact hsub r hr
    · obtain ⟨R, hR, hw⟩ := hwX r hr
      exact ⟨R, List.mem_append_right _ hR, hw⟩
  have hcovw : Covers wr t.wr := by
    rw [hc.wr]
    exact covers_of_within hwX
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

end VG.Proof.Ed448.X86_64.SignCached

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86_64.SignCached.Hash`. -/
section

/-!
# Ed448 signing with a cached public key on x86-64: the hashes

Between the frame's push and pop (`Ctx`): the first ten bytes of
`dom4(0, context)` written to the frame (`hdr_ok`), the Keccak state at
`scratch` zeroed (`zeroSt_ok`), and the calls of the sponge functions on it
(`kabs_ok`, `kpad_ok`, `ksqz_ok`); then the three hashes, each into the frame:
`SHAKE256(seed, 114)` (`seedHash_ok`), `SHAKE256(dom4(0, C) ‖ prefix ‖ M, 114)`
(`nonceHash_ok`) and `SHAKE256(dom4(0, C) ‖ R ‖ A ‖ M, 114)` (`chalHash_ok`).
-/

namespace VG.Proof.Ed448.X86_64.SignCached

open VG VG.X86_64 VG.Impl.Ed448.X86_64.SignCached
open VG.Impl.Ed448.X86_64.Verify (stk Arg hdr zeroSt kabs kpad ksqz aSt aKs sigEd448 fHdr fH fPk fCtx fCtxLen
  fMsg fLen fScr)
open VG.Proof.Ed448.X86_64.Verify (Within within_off within_base within_self add_add ea_stk ea_base gpr_ce ne_cs
  bytesAt_length x0 dbl_ok hdr_bytes zstores zstores_ok zero_state ofNat_toNat_self ofNat_toNat_eq FrOk
  setArgs_ok argRegs_cs argsIn5 argsIn6 below_call_sub)
open VG.Proof.MlKem.X86_64 (Keep WP.keep AbsorbArgs PadArgs SqueezeArgs absorb_pre pad_pre squeeze_pre absorb_nosp
  pad_nosp squeeze_nosp absorb_depth pad_depth squeeze_depth callEntry_repr callEntry_bytesAt callEntry_stateAt
  ofNat_toNat')
open VG.Spec.Sha3 (bytesAt stateAt absorb pad squeezeFrom Repr)

theorem H_eq (L : VG.Proof.Ed448.X86_64.SignCached.Lay) : L.H = L.B + BitVec.ofNat 64 32 := add_add _ _ _

section
variable {L : VG.Proof.Ed448.X86_64.SignCached.Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

/-! ## The arguments in the frame -/

theorem Ctx.frOk {t : State} (hc : VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t) : FrOk t := fun f hf => by
  rw [hc.rsp]; exact hc.inFr (by omega)

theorem Ctx.slot {t : State} (hc : VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t) (f : Nat) :
    (Arg.slot f).val t = t.mem.readW (L.SP + BitVec.ofNat 64 f) 64 := by
  simp only [Arg.val, hc.rsp]

theorem Ctx.sp {t : State} (hc : VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t) (o : Nat) : (Arg.sp o).val t = L.SP + BitVec.ofNat 64 o := by
  simp only [Arg.val, hc.rsp]

theorem Ctx.aSt {t : State} (hc : VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t) : aSt.val t = L.ST := by
  simp only [Impl.Ed448.X86_64.Verify.aSt, hc.slot, hc.pScr]

theorem Ctx.aKs {t : State} (hc : VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t) : aKs.val t = L.KS := by
  simp only [Impl.Ed448.X86_64.Verify.aKs, Arg.val, hc.rsp, hc.pScr]

/-! ## Regions -/

/-- The 16 bytes below `rsp` that a call from the frame uses. -/
theorem k16 {t : State} (hc : VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t) {r : Region} (h : Region.Disjoint ⟨L.B, 16⟩ r) :
    (below (t.gpr .rsp) 16).Disjoint r := by
  rw [hc.rsp]; exact h.sub_left (below_call_sub L.B (Nat.le_refl _))

theorem st_ks (L : VG.Proof.Ed448.X86_64.SignCached.Lay) : Region.Disjoint ⟨L.ST, 200⟩ ⟨L.KS, 640⟩ := by
  have := Offset.disjoint L.scr (d := 0) (n := 200) (e := 256) (k := 640) (by omega) (by omega) (by omega)
  simpa only [x0] using this

theorem st_h (hL : L.Ok) : Region.Disjoint ⟨L.ST, 200⟩ ⟨L.H, 114⟩ := by
  have := hL.stk_x (d := 32) (n := 114) (e := 0) (k := 200) (by omega) (by omega)
  rw [VG.Proof.Ed448.X86_64.SignCached.H_eq]; simpa only [x0] using this.symm

theorem h_ks (hL : L.Ok) : Region.Disjoint ⟨L.H, 114⟩ ⟨L.KS, 640⟩ := by
  rw [VG.Proof.Ed448.X86_64.SignCached.H_eq]; exact hL.stk_x (by omega) (by omega)

/-- The 16 bytes below the frame, apart from `scratch`. -/
theorem k_x (hL : L.Ok) {e k : Nat} (h₂ : e + k ≤ 8192) :
    Region.Disjoint ⟨L.B, 16⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ := by
  have := hL.stk_x (d := 0) (n := 16) (by omega) h₂
  simpa only [x0] using this

theorem k_st (hL : L.Ok) : Region.Disjoint ⟨L.B, 16⟩ ⟨L.ST, 200⟩ := by
  have := VG.Proof.Ed448.X86_64.SignCached.k_x hL (e := 0) (k := 200) (by omega); simpa only [x0] using this

theorem k_ks (hL : L.Ok) : Region.Disjoint ⟨L.B, 16⟩ ⟨L.KS, 640⟩ := VG.Proof.Ed448.X86_64.SignCached.k_x hL (by omega)

theorem k_h : Region.Disjoint ⟨L.B, 16⟩ ⟨L.H, 114⟩ := by
  rw [VG.Proof.Ed448.X86_64.SignCached.H_eq]; exact Offset.base_disjoint _ (by omega) (by omega)

/-- The 16 bytes below the frame, apart from a buffer apart from the stack. -/
theorem k_r (hL : L.Ok) {r : Region} (hr : L.STK.Disjoint r) : Region.Disjoint ⟨L.B, 16⟩ r := by
  have := hL.stk_r hr (d := 0) (n := 16) (by omega); simpa only [x0] using this

theorem w_st : VG.Proof.Ed448.X86_64.SignCached.WOk L ⟨L.ST, 200⟩ := .inl (within_base _ (by omega))
theorem w_ks : VG.Proof.Ed448.X86_64.SignCached.WOk L ⟨L.KS, 640⟩ := .inl (within_off _ (by omega))
theorem w_h : VG.Proof.Ed448.X86_64.SignCached.WOk L ⟨L.H, 114⟩ := .inr (.inr (.inl (within_off _ (by omega))))

/-- The first 57 bytes of `out`, where `R` goes. -/
theorem o57_sub : Region.Sub ⟨L.out, 57⟩ L.OUT := (within_base _ (by omega)).sub

/-- Bytes apart from the Keccak state, the working space and the 16 bytes
below the frame are kept by a sponge function's call. -/
theorem keep3 {m m' : Mem} (hf : VG.Frame [⟨L.ST, 200⟩, ⟨L.KS, 640⟩, ⟨L.B, 16⟩] m m') {p : Addr} {n : Nat}
    (dS : Region.Disjoint ⟨p, n⟩ ⟨L.ST, 200⟩) (dK : Region.Disjoint ⟨p, n⟩ ⟨L.KS, 640⟩)
    (kD : Region.Disjoint ⟨L.B, 16⟩ ⟨p, n⟩) (hn : n ≤ 2 ^ 64) : VG.Spec.Sha3.bytesAt m' p n = VG.Spec.Sha3.bytesAt m p n :=
  Verify.bytesAt_congr fun _ hi => hf.bytes (R := ⟨p, n⟩) (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [dS, dK, kD.symm]) hn hi

theorem keep1 {m m' : Mem} (hf : VG.Frame [⟨L.ST, 200⟩] m m') {p : Addr} {n : Nat}
    (dS : Region.Disjoint ⟨p, n⟩ ⟨L.ST, 200⟩) (hn : n ≤ 2 ^ 64) : VG.Spec.Sha3.bytesAt m' p n = VG.Spec.Sha3.bytesAt m p n :=
  Verify.bytesAt_congr fun _ hi => hf.bytes (R := ⟨p, n⟩) (by simpa using dS) hn hi

/-! ## The header of `dom4` -/

/-- `"SigEd448" ‖ 0 ‖ ctx_len`, the first ten bytes of `dom4(0, context)`. -/
abbrev hdrBytes (L : VG.Proof.Ed448.X86_64.SignCached.Lay) : List Byte :=
  "SigEd448".toList.map (fun c => BitVec.ofNat 8 c.toNat) ++ [BitVec.ofNat 8 0, BitVec.ofNat 8 L.ctxLen.toNat]

theorem hdr_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t) :
    WP isa (.block hdr) t fun t' => VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t' ∧ VG.Spec.Sha3.bytesAt t'.mem L.SP 10 = VG.Proof.Ed448.X86_64.SignCached.hdrBytes L := by
  have w0 : InRegions t.wr L.SP 8 := by simpa only [x0] using hc.inFrW (d := 0) (n := 8) (by omega)
  have r216 := hc.inFr (d := 216) (by omega)
  have e : (t.mem.writeW L.SP (BitVec.ofNat 64 sigEd448)).readW (L.SP + BitVec.ofNat 64 216) 64 = L.ctxLen := by
    rw [Mem.readW_writeW_sep (fun x h₁ h₂ =>
      Offset.sep_base L.SP (n := 8) (e := 216) (k := 8) (by omega) (by omega) x h₂ h₁) (by decide)]
    exact hc.pCtxLen
  rw [hdr, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.rax] (Q := fun s1 => s1.mem = t.mem.writeW L.SP (BitVec.ofNat 64 sigEd448) ∧
      s1.gpr .rax = L.ctxLen ∧ s1.mxcsr = t.mxcsr)
    (by xrun [ea_stk, fHdr, fCtxLen, hc.rsp, w0, r216, e, RegUpd.mxcsr_setReg]) (by decide))
    fun t1 ⟨⟨hm1, ha1, hx1⟩, k1⟩ => ?_
  refine WP.mono (dbl_ok 8 t1) fun t2 ⟨⟨ha2, hm2, hx2⟩, k2⟩ => ?_
  have hsp2 : t2.gpr .rsp = L.SP := by rw [k2.gpr (by decide), k1.gpr (by decide), hc.rsp]
  have w8 : InRegions t2.wr (L.SP + BitVec.ofNat 64 8) 8 := by
    rw [k2.2.2, k1.2.2]; exact hc.inFrW (by omega)
  refine WP.mono (Q := fun t3 : State => t3.mem = t2.mem.writeW (L.SP + BitVec.ofNat 64 8) (t2.gpr .rax) ∧
      t3.gpr = t2.gpr ∧ t3.rd = t2.rd ∧ t3.wr = t2.wr ∧ t3.mxcsr = t2.mxcsr) ?_
    fun t3 ⟨hm3, hg3, hrd3, hwr3, hx3⟩ => ?_
  · apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store64, ea_stk, fHdr, Nat.reduceAdd, hsp2,
      w8, ite_true, Option.some.injEq, exists_eq_left']
    exact ⟨trivial, trivial, trivial, trivial, trivial⟩
  have hm : t3.mem = (t.mem.writeW L.SP (BitVec.ofNat 64 sigEd448)).writeW (L.SP + BitVec.ofNat 64 8)
      (L.ctxLen * BitVec.ofNat 64 (2 ^ 8)) := by
    rw [hm3, ha2, ha1, hm2, hm1]
  have hf : VG.Frame ([⟨L.SP, 16⟩] ++ [⟨L.B, 16⟩]) t.mem t3.mem := by
    rw [hm]
    have c0 : (⟨L.SP, 16⟩ : Region).Contains L.SP 8 := by
      simpa only [x0] using Offset.contains_base L.SP (d := 0) (n := 8) (k := 16) (by omega) (by omega)
    exact ((Frame.refl _ _).writeW (List.mem_cons_self ..) _ c0).writeW (List.mem_cons_self ..) _
      (Offset.contains_base _ (by omega) (by omega))
  refine ⟨hc.of_frame hL (hrd3.trans (k2.2.1.trans k1.2.1)) (hwr3.trans (k2.2.2.trans k1.2.2))
    (fun r hr => by
      rw [hg3, k2.gpr (by simp only [List.mem_singleton]; exact ne_cs hr (by decide)),
        k1.gpr (by simp only [List.mem_singleton]; exact ne_cs hr (by decide))])
    (by rw [hx3, hx2, hx1]) hf (fun r hr => ?_), ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact .inr (.inr (.inl (within_base _ (by omega))))
  · rw [hm]; exact hdr_bytes _ _ _ hL.ctxLt

/-! ## Zeroing the state -/

theorem zeroSt_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t) :
    WP isa VG.Impl.Ed448.X86_64.Verify.zeroSt t fun t' => VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t' ∧ VG.Frame [⟨L.ST, 200⟩] t.mem t'.mem ∧
      stateAt t'.mem L.ST = Spec.Sha3.zero := by
  refine WP.seq ?_
  show WP isa (.block (aSt.mov .rdi ++ [.mov32 .rax (.imm 0)])) t _
  rw [WP.block_append_iff]
  refine WP.mono (Verify.Arg.mov_ok .rdi VG.Impl.Ed448.X86_64.Verify.aSt (by decide) (by decide) t hc.frOk) fun t1 ⟨⟨h1, hm1, hx1⟩, k1⟩ => ?_
  refine WP.mono (WP.keep [.rax] (Q := fun s1 => s1.mem = t1.mem ∧ s1.gpr .rax = 0 ∧ s1.mxcsr = t1.mxcsr)
    (by xrun [RegUpd.mxcsr_setReg]) (by decide)) fun t2 ⟨⟨hm2, hax, hx2⟩, k2⟩ => ?_
  have hdi : t2.gpr .rdi = L.scr := (k2.gpr (by decide)).trans (h1.trans hc.aSt)
  have hw2 : t2.wr = L.FR :: L.wr := k2.2.2.trans (k1.2.2.trans hc.wr)
  refine WP.mono (zstores_ok 25 (Nat.le_refl _) t2 hdi hax fun j hj => ?_)
    fun t3 ⟨g3, rd3, wr3, mx3, hf, hz⟩ => ?_
  · rw [hw2, hL.wr]
    exact ⟨L.SCR, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  · rw [hm2, hm1] at hf
    have hcs : ∀ r ∈ calleeSaved, t3.gpr r = t.gpr r := fun r hr => by
      rw [g3, k2.gpr (by simp only [List.mem_singleton]; exact ne_cs hr (by decide)),
        k1.gpr (by simp only [List.mem_singleton]; exact ne_cs hr (by decide))]
    have hf' : VG.Frame ([⟨L.ST, 200⟩] ++ [⟨L.B, 16⟩]) t.mem t3.mem :=
      hf.mono fun r hr => by simp at hr ⊢; exact .inl hr
    exact ⟨hc.of_frame hL (rd3.trans (k2.2.1.trans k1.2.1)) (wr3.trans (k2.2.2.trans k1.2.2)) hcs
      (by rw [mx3, hx2, hx1]) hf' (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.Ed448.X86_64.SignCached.w_st), hf, zero_state hz⟩

/-! ## The sponge functions -/

/-- The arguments of a call of `vg_keccak_absorb`. -/
abbrev absArgs (src len pos : Arg) : List Arg := [VG.Impl.Ed448.X86_64.Verify.aSt, .imm 136, pos, src, len, VG.Impl.Ed448.X86_64.Verify.aKs]

theorem kabs_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t)
    {src len pos : Arg} (hok : (VG.Proof.Ed448.X86_64.SignCached.absArgs src len pos).all Arg.ok = true)
    {dp : Addr} {n q : Nat} (hdp : src.val t = dp) (hn : len.val t = BitVec.ofNat 64 n)
    (hq : pos.val t = BitVec.ofNat 64 q) (hql : q < 136) (hnl : n < 2 ^ 64)
    (hin : ∃ R ∈ L.rd ++ L.FR :: L.wr, Within ⟨dp, n⟩ R)
    (dS : Region.Disjoint ⟨dp, n⟩ ⟨L.ST, 200⟩) (dK : Region.Disjoint ⟨dp, n⟩ ⟨L.KS, 640⟩)
    (kD : Region.Disjoint ⟨L.B, 16⟩ ⟨dp, n⟩) :
    WP isa (VG.Impl.Ed448.X86_64.Verify.kabs src len pos) t fun t' => VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t' ∧
      VG.Frame [⟨L.ST, 200⟩, ⟨L.KS, 640⟩, ⟨L.B, 16⟩] t.mem t'.mem ∧
      (∀ msg, Repr t.mem L.ST 136 msg → q = msg.length % 136 →
        Repr t'.mem L.ST 136 (msg ++ VG.Spec.Sha3.bytesAt t.mem dp n)) ∧ (t'.gpr .rax).toNat = (q + n) % 136 := by
  refine WP.seq (WP.mono (setArgs_ok _ hok t hc.frOk) fun t1 ⟨⟨hA, hm, hx⟩, k⟩ => ?_)
  have hc1 : VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t1 := hc.regs k.2.1 k.2.2 hm hx fun r hr => k.gpr (argRegs_cs r hr)
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := argsIn6 hA
  rw [hc.aSt] at e1
  rw [hc.aKs] at e6
  rw [hdp] at e4
  rw [hn] at e5
  rw [hq] at e3
  have ha : AbsorbArgs t1 L.ST dp L.KS 136 q n :=
    ⟨e1, e2, e3, e4, e5, e6, by decide, hql, hnl, VG.Proof.Ed448.X86_64.SignCached.st_ks L, dS, dK, VG.Proof.Ed448.X86_64.SignCached.k16 hc1 (VG.Proof.Ed448.X86_64.SignCached.k_st hL), VG.Proof.Ed448.X86_64.SignCached.k16 hc1 kD,
      VG.Proof.Ed448.X86_64.SignCached.k16 hc1 (VG.Proof.Ed448.X86_64.SignCached.k_ks hL)⟩
  refine VG.Proof.Ed448.X86_64.SignCached.call_ok hL Proof.Sha3.X86_64.Stream.Absorb.absorb_correct absorb_nosp (by rw [absorb_depth])
    hc1 (absorb_pre ha) (by simpa using hin) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [VG.Proof.Ed448.X86_64.SignCached.w_st, VG.Proof.Ed448.X86_64.SignCached.w_ks])
    fun s' hc' hf _ ⟨s₂, hm₂, hg₂, hpost, hrax⟩ => ?_
  have hn' := ofNat_toNat' hnl
  have hq' := ofNat_toNat' (show q < 2 ^ 64 by omega)
  simp only [State.withRegions_mem, gpr_ce t1 _ _ (by decide : Reg.rdi ≠ .rsp),
    gpr_ce t1 _ _ (by decide : Reg.rsi ≠ .rsp), gpr_ce t1 _ _ (by decide : Reg.rdx ≠ .rsp),
    gpr_ce t1 _ _ (by decide : Reg.rcx ≠ .rsp), gpr_ce t1 _ _ (by decide : Reg.r8 ≠ .rsp),
    e1, e2, e3, e4, e5, hm₂, hn', hq'] at hpost hrax
  refine ⟨hc', by rw [← hm]; simpa using hf, fun msg hmsg hp => ?_, by rw [← hg₂ _ (by decide)]; exact hrax⟩
  have := hpost msg ((callEntry_repr t1 ha.k_st).mpr (hm ▸ hmsg)) hp
  rwa [callEntry_bytesAt t1 hnl ha.k_d, hm] at this

/-- The arguments of a call of `vg_keccak_pad`. -/
abbrev padArgs (pos : Arg) : List Arg := [VG.Impl.Ed448.X86_64.Verify.aSt, .imm 136, pos, .imm 0x1f, VG.Impl.Ed448.X86_64.Verify.aKs]

theorem kpad_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t)
    {pos : Arg} (hok : (VG.Proof.Ed448.X86_64.SignCached.padArgs pos).all Arg.ok = true) {q : Nat}
    (hq : pos.val t = BitVec.ofNat 64 q) (hql : q < 136) :
    WP isa (VG.Impl.Ed448.X86_64.Verify.kpad pos) t fun t' => VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t' ∧
      VG.Frame [⟨L.ST, 200⟩, ⟨L.KS, 640⟩, ⟨L.B, 16⟩] t.mem t'.mem ∧
      (∀ msg, Repr t.mem L.ST 136 msg → q = msg.length % 136 →
        stateAt t'.mem L.ST = absorb 136 (pad 136 Spec.Sha3.shakeSuffix msg)) := by
  refine WP.seq (WP.mono (setArgs_ok _ hok t hc.frOk) fun t1 ⟨⟨hA, hm, hx⟩, k⟩ => ?_)
  have hc1 : VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t1 := hc.regs k.2.1 k.2.2 hm hx fun r hr => k.gpr (argRegs_cs r hr)
  obtain ⟨e1, e2, e3, e4, e5⟩ := argsIn5 hA
  rw [hc.aSt] at e1
  rw [hc.aKs] at e5
  rw [hq] at e3
  have ha : PadArgs t1 L.ST L.KS 136 q :=
    ⟨e1, e2, e3, e5, by decide, hql, VG.Proof.Ed448.X86_64.SignCached.st_ks L, VG.Proof.Ed448.X86_64.SignCached.k16 hc1 (VG.Proof.Ed448.X86_64.SignCached.k_st hL), VG.Proof.Ed448.X86_64.SignCached.k16 hc1 (VG.Proof.Ed448.X86_64.SignCached.k_ks hL)⟩
  refine VG.Proof.Ed448.X86_64.SignCached.call_ok hL Proof.Sha3.X86_64.Stream.Pad.pad_correct pad_nosp (by rw [pad_depth])
    hc1 (pad_pre ha) (by simp) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [VG.Proof.Ed448.X86_64.SignCached.w_st, VG.Proof.Ed448.X86_64.SignCached.w_ks])
    fun s' hc' hf _ ⟨s₂, hm₂, _, hpost⟩ => ?_
  have hq' := ofNat_toNat' (show q < 2 ^ 64 by omega)
  simp only [Proof.Sha3.padX86_64, State.withRegions_mem, gpr_ce t1 _ _ (by decide : Reg.rdi ≠ .rsp),
    gpr_ce t1 _ _ (by decide : Reg.rsi ≠ .rsp), gpr_ce t1 _ _ (by decide : Reg.rdx ≠ .rsp),
    gpr_ce t1 _ _ (by decide : Reg.rcx ≠ .rsp), e1, e2, e3, e4, hm₂, hq'] at hpost
  refine ⟨hc', by rw [← hm]; simpa using hf, fun msg hmsg hp => ?_⟩
  have := hpost msg ((callEntry_repr t1 ha.k_st).mpr (hm ▸ hmsg)) hp
  rw [this]
  rfl

/-- The arguments of a call of `vg_keccak_squeeze`. -/
abbrev sqzArgs : List Arg := [VG.Impl.Ed448.X86_64.Verify.aSt, .imm 136, .imm 0, .sp fH, .imm 114, VG.Impl.Ed448.X86_64.Verify.aKs]

theorem ksqz_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t) :
    WP isa VG.Impl.Ed448.X86_64.Verify.ksqz t fun t' => VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t' ∧
      VG.Frame [⟨L.ST, 200⟩, ⟨L.H, 114⟩, ⟨L.KS, 640⟩, ⟨L.B, 16⟩] t.mem t'.mem ∧
      VG.Spec.Sha3.bytesAt t'.mem L.H 114 = squeezeFrom 136 (stateAt t.mem L.ST) 0 114 := by
  refine WP.seq (WP.mono (setArgs_ok VG.Proof.Ed448.X86_64.SignCached.sqzArgs (by decide) t hc.frOk) fun t1 ⟨⟨hA, hm, hx⟩, k⟩ => ?_)
  have hc1 : VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t1 := hc.regs k.2.1 k.2.2 hm hx fun r hr => k.gpr (argRegs_cs r hr)
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := argsIn6 hA
  rw [hc.aSt] at e1
  rw [hc.aKs] at e6
  rw [hc.sp] at e4
  change t1.gpr .rcx = L.H at e4
  have ha : SqueezeArgs t1 L.ST L.H L.KS 136 0 114 :=
    ⟨e1, e2, e3, e4, e5, e6, by decide, by decide, by decide, VG.Proof.Ed448.X86_64.SignCached.st_h hL, VG.Proof.Ed448.X86_64.SignCached.st_ks L, VG.Proof.Ed448.X86_64.SignCached.h_ks hL, VG.Proof.Ed448.X86_64.SignCached.k16 hc1 (VG.Proof.Ed448.X86_64.SignCached.k_st hL),
      VG.Proof.Ed448.X86_64.SignCached.k16 hc1 VG.Proof.Ed448.X86_64.SignCached.k_h, VG.Proof.Ed448.X86_64.SignCached.k16 hc1 (VG.Proof.Ed448.X86_64.SignCached.k_ks hL)⟩
  refine VG.Proof.Ed448.X86_64.SignCached.call_ok hL Proof.Sha3.X86_64.Stream.Squeeze.squeeze_correct squeeze_nosp
    (by rw [squeeze_depth]) hc1 (squeeze_pre ha) (by simp) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [VG.Proof.Ed448.X86_64.SignCached.w_st, VG.Proof.Ed448.X86_64.SignCached.w_h, VG.Proof.Ed448.X86_64.SignCached.w_ks])
    fun s' hc' hf _ ⟨s₂, hm₂, _, hpost, _⟩ => ?_
  simp only [State.withRegions_mem, gpr_ce t1 _ _ (by decide : Reg.rdi ≠ .rsp),
    gpr_ce t1 _ _ (by decide : Reg.rsi ≠ .rsp), gpr_ce t1 _ _ (by decide : Reg.rdx ≠ .rsp),
    gpr_ce t1 _ _ (by decide : Reg.rcx ≠ .rsp), gpr_ce t1 _ _ (by decide : Reg.r8 ≠ .rsp),
    e1, e2, e3, e4, e5, hm₂, Arg.val, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hpost
  refine ⟨hc', by rw [← hm]; simpa using hf, ?_⟩
  rw [hpost, callEntry_stateAt t1 ha.k_st, hm]

/-! ## Where the pieces are -/

/-- A piece in the frame, apart from the Keccak state, the working space and
the 16 bytes below the frame. -/
theorem frSide (hL : L.Ok) {d n : Nat} (h : d + n ≤ 448) :
    (∃ R ∈ L.rd ++ L.FR :: L.wr, Within ⟨L.SP + BitVec.ofNat 64 d, n⟩ R) ∧
    Region.Disjoint ⟨L.SP + BitVec.ofNat 64 d, n⟩ ⟨L.ST, 200⟩ ∧
    Region.Disjoint ⟨L.SP + BitVec.ofNat 64 d, n⟩ ⟨L.KS, 640⟩ ∧
    Region.Disjoint ⟨L.B, 16⟩ ⟨L.SP + BitVec.ofNat 64 d, n⟩ := by
  refine ⟨⟨L.FR, by simp, within_off _ h⟩, ?_, ?_, ?_⟩ <;> rw [Lay.SP, add_add]
  · have := hL.stk_x (d := 16 + d) (n := n) (e := 0) (k := 200) (by omega) (by omega)
    simpa only [x0] using this
  · exact hL.stk_x (d := 16 + d) (n := n) (by omega) (by omega)
  · exact Offset.base_disjoint _ (by omega) (by omega)

/-- A buffer apart from `scratch` and the stack. -/
theorem bufSide (hL : L.Ok) {r : Region} (hin : ∃ R ∈ L.rd ++ L.FR :: L.wr, Within r R)
    (hx : L.SCR.Disjoint r) (hk : L.STK.Disjoint r) :
    (∃ R ∈ L.rd ++ L.FR :: L.wr, Within r R) ∧ Region.Disjoint r ⟨L.ST, 200⟩ ∧
    Region.Disjoint r ⟨L.KS, 640⟩ ∧ Region.Disjoint ⟨L.B, 16⟩ r :=
  ⟨hin, by have := hL.x_r hx (e := 0) (k := 200) (by omega); simpa only [x0] using this.symm,
    (hL.x_r hx (e := 256) (k := 640) (by omega)).symm, VG.Proof.Ed448.X86_64.SignCached.k_r hL hk⟩

theorem sp0 (L : VG.Proof.Ed448.X86_64.SignCached.Lay) : L.SP + BitVec.ofNat 64 0 = L.SP := x0 _

/-! ## The hashes -/

/-- What the hashes write: `scratch`, the hash, and the 16 bytes below the
frame. -/
abbrev HW (L : VG.Proof.Ed448.X86_64.SignCached.Lay) : List Region := [L.SCR, ⟨L.H, 114⟩, ⟨L.B, 16⟩]

theorem frameH {rs : List Region} {m m' : Mem} (h : VG.Frame rs m m')
    (hs : ∀ r ∈ rs, r = ⟨L.B, 16⟩ ∨ Within r L.SCR ∨ Within r ⟨L.H, 114⟩) : VG.Frame (VG.Proof.Ed448.X86_64.SignCached.HW L) m m' :=
  Frame.sub h fun r hr => by
    rcases hs r hr with rfl | hw | hw
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, hw.sub⟩
    · exact ⟨_, by simp, hw.sub⟩

theorem fz {m m' : Mem} (h : VG.Frame [⟨L.ST, 200⟩] m m') : VG.Frame (VG.Proof.Ed448.X86_64.SignCached.HW L) m m' :=
  VG.Proof.Ed448.X86_64.SignCached.frameH h (by simp only [List.mem_singleton]; rintro r rfl; exact .inr (.inl (within_base _ (by omega))))

theorem fa {m m' : Mem} (h : VG.Frame [⟨L.ST, 200⟩, ⟨L.KS, 640⟩, ⟨L.B, 16⟩] m m') : VG.Frame (VG.Proof.Ed448.X86_64.SignCached.HW L) m m' :=
  VG.Proof.Ed448.X86_64.SignCached.frameH h (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    exacts [.inr (.inl (within_base _ (by omega))), .inr (.inl (within_off _ (by omega))), .inl rfl])

theorem fs {m m' : Mem} (h : VG.Frame [⟨L.ST, 200⟩, ⟨L.H, 114⟩, ⟨L.KS, 640⟩, ⟨L.B, 16⟩] m m') : VG.Frame (VG.Proof.Ed448.X86_64.SignCached.HW L) m m' :=
  VG.Proof.Ed448.X86_64.SignCached.frameH h (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    exacts [.inr (.inl (within_base _ (by omega))), .inr (.inr (within_self _)),
      .inr (.inl (within_off _ (by omega))), .inl rfl])

theorem seedHash_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t) :
    WP isa seedHash t fun t' => VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t' ∧ VG.Frame (VG.Proof.Ed448.X86_64.SignCached.HW L) t.mem t'.mem ∧
      VG.Spec.Sha3.bytesAt t'.mem L.H 114 = Spec.Sha3.shake256 (VG.Spec.Sha3.bytesAt m₀ L.seed 57) 114 := by
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86_64.SignCached.zeroSt_ok hL hc) fun t1 ⟨hc1, hf1, hz⟩ => ?_)
  obtain ⟨i, s, k, d⟩ := VG.Proof.Ed448.X86_64.SignCached.bufSide hL ⟨L.SEED, List.mem_append_left _ hL.inSeed, within_self _⟩ hL.xSeed hL.kSeed
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86_64.SignCached.kabs_ok hL hc1 (by decide) (dp := L.seed) (n := 57) (q := 0)
    (by rw [hc1.slot]; exact hc1.pSeed) rfl rfl (by decide) (by decide) i s k d)
    fun t2 ⟨hc2, hf2, hR2, _⟩ => ?_)
  have hR2 := hR2 [] (PublicKey.repr_nil hz) rfl
  rw [List.nil_append, hc1.bytesAt_eq hL.xSeed hL.oSeed hL.kSeed (by decide)] at hR2
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86_64.SignCached.kpad_ok hL hc2 (pos := .imm 57) (by decide) rfl (by decide))
    fun t3 ⟨hc3, hf3, hS3⟩ => ?_)
  have hS3 := hS3 _ hR2 (by rw [VG.Proof.Ed448.X86_64.Verify.bytesAt_length])
  refine WP.mono (VG.Proof.Ed448.X86_64.SignCached.ksqz_ok hL hc3) fun t4 ⟨hc4, hf4, hm4⟩ =>
    ⟨hc4, (VG.Proof.Ed448.X86_64.SignCached.fz hf1).trans ((VG.Proof.Ed448.X86_64.SignCached.fa hf2).trans ((VG.Proof.Ed448.X86_64.SignCached.fa hf3).trans (VG.Proof.Ed448.X86_64.SignCached.fs hf4))), ?_⟩
  rw [hm4, hS3, PublicKey.shake256_eq]

/-- The position after absorbing `b` after `a`. -/
theorem len_step {a : List Byte} {q n : Nat} (h : q = a.length % 136) (b : List Byte) (hb : b.length = n) :
    (q + n) % 136 = (a ++ b).length % 136 := by
  rw [List.length_append, hb, h]; omega

theorem nonceHash_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t) :
    WP isa nonceHash t fun t' => VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t' ∧ VG.Frame (VG.Proof.Ed448.X86_64.SignCached.HW L) t.mem t'.mem ∧
      VG.Spec.Sha3.bytesAt t'.mem L.H 114 = Spec.Sha3.shake256 (VG.Spec.Sha3.bytesAt t.mem L.SP 10 ++ VG.Spec.Sha3.bytesAt m₀ L.ctx L.ctxLen.toNat ++
        VG.Spec.Sha3.bytesAt t.mem (L.SP + BitVec.ofNat 64 73) 57 ++ VG.Spec.Sha3.bytesAt m₀ L.msg L.len.toNat) 114 := by
  have hctx := hL.ctxLt
  obtain ⟨hi, hs, hk, hd⟩ := VG.Proof.Ed448.X86_64.SignCached.frSide hL (d := 0) (n := 10) (by omega)
  obtain ⟨pi, ps, pk, pd⟩ := VG.Proof.Ed448.X86_64.SignCached.frSide hL (d := 73) (n := 57) (by omega)
  rw [VG.Proof.Ed448.X86_64.SignCached.sp0] at hi hs hk hd
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86_64.SignCached.zeroSt_ok hL hc) fun t1 ⟨hc1, hf1, hz⟩ => ?_)
  have eh := VG.Proof.Ed448.X86_64.SignCached.keep1 hf1 hs (by decide)
  have ep1 := VG.Proof.Ed448.X86_64.SignCached.keep1 hf1 ps (by decide)
  -- The header.
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86_64.SignCached.kabs_ok hL hc1 (by decide) (dp := L.SP) (n := 10) (q := 0)
    (by rw [hc1.sp]; exact x0 _) rfl rfl (by decide) (by decide) hi hs hk hd) fun t2 ⟨hc2, hf2, hR2, hx2⟩ => ?_)
  have hR2 := hR2 [] (PublicKey.repr_nil hz) rfl
  have ep2 := VG.Proof.Ed448.X86_64.SignCached.keep3 hf2 ps pk pd (by decide)
  -- The context.
  obtain ⟨ci, cs, ck, cd⟩ := VG.Proof.Ed448.X86_64.SignCached.bufSide hL ⟨L.CTX, List.mem_append_left _ hL.inCtx, within_self _⟩ hL.xCtx hL.kCtx
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86_64.SignCached.kabs_ok hL hc2 (by decide) (dp := L.ctx) (n := L.ctxLen.toNat)
    (by rw [hc2.slot]; exact hc2.pCtx) (by rw [hc2.slot]; exact hc2.pCtxLen.trans (ofNat_toNat_self _).symm)
    (ofNat_toNat_eq hx2) (by omega) (by omega) ci cs ck cd) fun t3 ⟨hc3, hf3, hR3, hx3⟩ => ?_)
  have hR3 := hR3 _ hR2 (by simp only [List.nil_append, VG.Proof.Ed448.X86_64.Verify.bytesAt_length])
  rw [hc2.bytesAt_eq hL.xCtx hL.oCtx hL.kCtx (by have := hL.nCtx; omega)] at hR3
  have ep3 := VG.Proof.Ed448.X86_64.SignCached.keep3 hf3 ps pk pd (by decide)
  -- The prefix.
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86_64.SignCached.kabs_ok hL hc3 (by decide) (dp := L.SP + BitVec.ofNat 64 73) (n := 57)
    (by rw [hc3.sp]; rfl) rfl (ofNat_toNat_eq hx3) (Nat.mod_lt _ (by decide)) (by decide) pi ps pk pd)
    fun t4 ⟨hc4, hf4, hR4, hx4⟩ => ?_)
  have hR4 := hR4 _ hR3 (VG.Proof.Ed448.X86_64.SignCached.len_step (by simp only [List.nil_append, VG.Proof.Ed448.X86_64.Verify.bytesAt_length]) _ (VG.Proof.Ed448.X86_64.Verify.bytesAt_length _ _ _))
  -- The message.
  obtain ⟨mi, ms, mk, md⟩ := VG.Proof.Ed448.X86_64.SignCached.bufSide hL ⟨L.MSG, List.mem_append_left _ hL.inMsg, within_self _⟩ hL.xMsg hL.kMsg
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86_64.SignCached.kabs_ok hL hc4 (by decide) (dp := L.msg) (n := L.len.toNat)
    (by rw [hc4.slot]; exact hc4.pMsg) (by rw [hc4.slot]; exact hc4.pLen.trans (ofNat_toNat_self _).symm)
    (ofNat_toNat_eq hx4) (Nat.mod_lt _ (by decide)) L.len.isLt mi ms mk md)
    fun t5 ⟨hc5, hf5, hR5, hx5⟩ => ?_)
  have hR5 := hR5 _ hR4 (VG.Proof.Ed448.X86_64.SignCached.len_step (VG.Proof.Ed448.X86_64.SignCached.len_step (by simp only [List.nil_append, VG.Proof.Ed448.X86_64.Verify.bytesAt_length]) _
    (VG.Proof.Ed448.X86_64.Verify.bytesAt_length _ _ _)) _ (VG.Proof.Ed448.X86_64.Verify.bytesAt_length _ _ _))
  rw [hc4.bytesAt_eq hL.xMsg hL.oMsg hL.kMsg (by have := hL.nMsg; omega)] at hR5
  -- Pad and squeeze.
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86_64.SignCached.kpad_ok hL hc5 (pos := .ret) (by decide) (ofNat_toNat_eq hx5) (Nat.mod_lt _ (by decide)))
    fun t6 ⟨hc6, hf6, hS6⟩ => ?_)
  have hS6 := hS6 _ hR5 (VG.Proof.Ed448.X86_64.SignCached.len_step (VG.Proof.Ed448.X86_64.SignCached.len_step (VG.Proof.Ed448.X86_64.SignCached.len_step (by simp only [List.nil_append, VG.Proof.Ed448.X86_64.Verify.bytesAt_length]) _
    (VG.Proof.Ed448.X86_64.Verify.bytesAt_length _ _ _)) _ (VG.Proof.Ed448.X86_64.Verify.bytesAt_length _ _ _)) _ (VG.Proof.Ed448.X86_64.Verify.bytesAt_length _ _ _))
  refine WP.mono (VG.Proof.Ed448.X86_64.SignCached.ksqz_ok hL hc6) fun t7 ⟨hc7, hf7, hm7⟩ => ⟨hc7, (VG.Proof.Ed448.X86_64.SignCached.fz hf1).trans ((VG.Proof.Ed448.X86_64.SignCached.fa hf2).trans ((VG.Proof.Ed448.X86_64.SignCached.fa hf3).trans
    ((VG.Proof.Ed448.X86_64.SignCached.fa hf4).trans ((VG.Proof.Ed448.X86_64.SignCached.fa hf5).trans ((VG.Proof.Ed448.X86_64.SignCached.fa hf6).trans (VG.Proof.Ed448.X86_64.SignCached.fs hf7)))))), ?_⟩
  rw [hm7, hS6, PublicKey.shake256_eq, List.nil_append, eh, ep3, ep2, ep1]

theorem chalHash_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t) :
    WP isa chalHash t fun t' => VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t' ∧ VG.Frame (VG.Proof.Ed448.X86_64.SignCached.HW L) t.mem t'.mem ∧
      VG.Spec.Sha3.bytesAt t'.mem L.H 114 = Spec.Sha3.shake256 (VG.Spec.Sha3.bytesAt t.mem L.SP 10 ++ VG.Spec.Sha3.bytesAt m₀ L.ctx L.ctxLen.toNat ++
        VG.Spec.Sha3.bytesAt t.mem L.out 57 ++ VG.Spec.Sha3.bytesAt m₀ L.pk 57 ++ VG.Spec.Sha3.bytesAt m₀ L.msg L.len.toNat) 114 := by
  have hctx := hL.ctxLt
  obtain ⟨hi, hs, hk, hd⟩ := VG.Proof.Ed448.X86_64.SignCached.frSide hL (d := 0) (n := 10) (by omega)
  rw [VG.Proof.Ed448.X86_64.SignCached.sp0] at hi hs hk hd
  have xR := hL.xOut.sub_right VG.Proof.Ed448.X86_64.SignCached.o57_sub
  have kR := hL.kOut.sub_right VG.Proof.Ed448.X86_64.SignCached.o57_sub
  obtain ⟨oi, os, ok, od⟩ := VG.Proof.Ed448.X86_64.SignCached.bufSide hL ⟨L.OUT, by simp [hL.wr], within_base _ (by omega)⟩ xR kR
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86_64.SignCached.zeroSt_ok hL hc) fun t1 ⟨hc1, hf1, hz⟩ => ?_)
  have eh := VG.Proof.Ed448.X86_64.SignCached.keep1 hf1 hs (by decide)
  have eo1 := VG.Proof.Ed448.X86_64.SignCached.keep1 hf1 os (by decide)
  -- The header.
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86_64.SignCached.kabs_ok hL hc1 (by decide) (dp := L.SP) (n := 10) (q := 0)
    (by rw [hc1.sp]; exact x0 _) rfl rfl (by decide) (by decide) hi hs hk hd) fun t2 ⟨hc2, hf2, hR2, hx2⟩ => ?_)
  have hR2 := hR2 [] (PublicKey.repr_nil hz) rfl
  have eo2 := VG.Proof.Ed448.X86_64.SignCached.keep3 hf2 os ok od (by decide)
  -- The context.
  obtain ⟨ci, cs, ck, cd⟩ := VG.Proof.Ed448.X86_64.SignCached.bufSide hL ⟨L.CTX, List.mem_append_left _ hL.inCtx, within_self _⟩ hL.xCtx hL.kCtx
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86_64.SignCached.kabs_ok hL hc2 (by decide) (dp := L.ctx) (n := L.ctxLen.toNat)
    (by rw [hc2.slot]; exact hc2.pCtx) (by rw [hc2.slot]; exact hc2.pCtxLen.trans (ofNat_toNat_self _).symm)
    (ofNat_toNat_eq hx2) (by omega) (by omega) ci cs ck cd) fun t3 ⟨hc3, hf3, hR3, hx3⟩ => ?_)
  have hR3 := hR3 _ hR2 (by simp only [List.nil_append, VG.Proof.Ed448.X86_64.Verify.bytesAt_length])
  rw [hc2.bytesAt_eq hL.xCtx hL.oCtx hL.kCtx (by have := hL.nCtx; omega)] at hR3
  have eo3 := VG.Proof.Ed448.X86_64.SignCached.keep3 hf3 os ok od (by decide)
  -- `R`.
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86_64.SignCached.kabs_ok hL hc3 (by decide) (dp := L.out) (n := 57)
    (by rw [hc3.slot]; exact hc3.pOut) rfl (ofNat_toNat_eq hx3) (Nat.mod_lt _ (by decide)) (by decide) oi os ok od)
    fun t4 ⟨hc4, hf4, hR4, hx4⟩ => ?_)
  have hR4 := hR4 _ hR3 (VG.Proof.Ed448.X86_64.SignCached.len_step (by simp only [List.nil_append, VG.Proof.Ed448.X86_64.Verify.bytesAt_length]) _ (VG.Proof.Ed448.X86_64.Verify.bytesAt_length _ _ _))
  -- `A`.
  obtain ⟨ai, as, ak, ad⟩ := VG.Proof.Ed448.X86_64.SignCached.bufSide hL ⟨L.PK, List.mem_append_left _ hL.inPk, within_self _⟩ hL.xPk hL.kPk
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86_64.SignCached.kabs_ok hL hc4 (by decide) (dp := L.pk) (n := 57)
    (by rw [hc4.slot]; exact hc4.pPk) rfl (ofNat_toNat_eq hx4) (Nat.mod_lt _ (by decide)) (by decide) ai as ak ad)
    fun t5 ⟨hc5, hf5, hR5, hx5⟩ => ?_)
  have hR5 := hR5 _ hR4 (VG.Proof.Ed448.X86_64.SignCached.len_step (VG.Proof.Ed448.X86_64.SignCached.len_step (by simp only [List.nil_append, VG.Proof.Ed448.X86_64.Verify.bytesAt_length]) _
    (VG.Proof.Ed448.X86_64.Verify.bytesAt_length _ _ _)) _ (VG.Proof.Ed448.X86_64.Verify.bytesAt_length _ _ _))
  rw [hc4.bytesAt_eq hL.xPk hL.oPk hL.kPk (by decide)] at hR5
  -- The message.
  obtain ⟨mi, ms, mk, md⟩ := VG.Proof.Ed448.X86_64.SignCached.bufSide hL ⟨L.MSG, List.mem_append_left _ hL.inMsg, within_self _⟩ hL.xMsg hL.kMsg
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86_64.SignCached.kabs_ok hL hc5 (by decide) (dp := L.msg) (n := L.len.toNat)
    (by rw [hc5.slot]; exact hc5.pMsg) (by rw [hc5.slot]; exact hc5.pLen.trans (ofNat_toNat_self _).symm)
    (ofNat_toNat_eq hx5) (Nat.mod_lt _ (by decide)) L.len.isLt mi ms mk md)
    fun t6 ⟨hc6, hf6, hR6, hx6⟩ => ?_)
  have hR6 := hR6 _ hR5 (VG.Proof.Ed448.X86_64.SignCached.len_step (VG.Proof.Ed448.X86_64.SignCached.len_step (VG.Proof.Ed448.X86_64.SignCached.len_step (by simp only [List.nil_append, VG.Proof.Ed448.X86_64.Verify.bytesAt_length]) _
    (VG.Proof.Ed448.X86_64.Verify.bytesAt_length _ _ _)) _ (VG.Proof.Ed448.X86_64.Verify.bytesAt_length _ _ _)) _ (VG.Proof.Ed448.X86_64.Verify.bytesAt_length _ _ _))
  rw [hc5.bytesAt_eq hL.xMsg hL.oMsg hL.kMsg (by have := hL.nMsg; omega)] at hR6
  -- Pad and squeeze.
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86_64.SignCached.kpad_ok hL hc6 (pos := .ret) (by decide) (ofNat_toNat_eq hx6) (Nat.mod_lt _ (by decide)))
    fun t7 ⟨hc7, hf7, hS7⟩ => ?_)
  have hS7 := hS7 _ hR6 (VG.Proof.Ed448.X86_64.SignCached.len_step (VG.Proof.Ed448.X86_64.SignCached.len_step (VG.Proof.Ed448.X86_64.SignCached.len_step (VG.Proof.Ed448.X86_64.SignCached.len_step (by simp only [List.nil_append, VG.Proof.Ed448.X86_64.Verify.bytesAt_length]) _
    (VG.Proof.Ed448.X86_64.Verify.bytesAt_length _ _ _)) _ (VG.Proof.Ed448.X86_64.Verify.bytesAt_length _ _ _)) _ (VG.Proof.Ed448.X86_64.Verify.bytesAt_length _ _ _)) _ (VG.Proof.Ed448.X86_64.Verify.bytesAt_length _ _ _))
  refine WP.mono (VG.Proof.Ed448.X86_64.SignCached.ksqz_ok hL hc7) fun t8 ⟨hc8, hf8, hm8⟩ => ⟨hc8, (VG.Proof.Ed448.X86_64.SignCached.fz hf1).trans ((VG.Proof.Ed448.X86_64.SignCached.fa hf2).trans ((VG.Proof.Ed448.X86_64.SignCached.fa hf3).trans
    ((VG.Proof.Ed448.X86_64.SignCached.fa hf4).trans ((VG.Proof.Ed448.X86_64.SignCached.fa hf5).trans ((VG.Proof.Ed448.X86_64.SignCached.fa hf6).trans ((VG.Proof.Ed448.X86_64.SignCached.fa hf7).trans (VG.Proof.Ed448.X86_64.SignCached.fs hf8))))))), ?_⟩
  rw [hm8, hS7, PublicKey.shake256_eq, List.nil_append, eh, eo3, eo2, eo1]

end

end VG.Proof.Ed448.X86_64.SignCached

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86_64.SignCached.Rel`. -/
section

/-!
# Ed448 signing with a cached public key on x86-64: relating two runs

Two runs between the frame's push and pop with the same layout, each in a
`Ctx` state, whose inputs agree on `I`, and each satisfying `Φ` (`Two`). What
each run satisfies by correctness carries over (`two_wp`), and a call of
code whose public data agree in both runs leaks the same (`call_tr`). Blocks
addressed from `rsp` and the moves of arguments are `Verify`'s
(`block_rsp_tr`, `setArgs_spOnly`).
-/

namespace VG.Proof.Ed448.X86_64.SignCached

open VG VG.X86_64
open VG.Impl.Ed448.X86_64.Verify (Arg setArgs callA)
open VG.Proof.Ed448.X86_64.Verify (Within covers_of_within block_rsp_tr setArgs_spOnly setArgs_ok ArgsIn Moved)
open VG.Proof.MlKem.X86_64 (Keep RelCT.postDep)

/-! ## Two runs -/

/-- Two runs with the layout `L`, inputs related by `I`, each satisfying `Φ`. -/
def Two (I : VG.Proof.Ed448.X86_64.SignCached.Lay → Mem → Mem → Prop) (Φ : VG.Proof.Ed448.X86_64.SignCached.Lay → Mem → State → Prop) (a b : State) : Prop :=
  ∃ (L : VG.Proof.Ed448.X86_64.SignCached.Lay) (g₁ g₂ : Reg → BitVec 64) (mx₁ mx₂ : BitVec 32) (m₁ m₂ : Mem), L.Ok ∧ I L m₁ m₂ ∧
    VG.Proof.Ed448.X86_64.SignCached.Ctx L g₁ mx₁ m₁ a ∧ VG.Proof.Ed448.X86_64.SignCached.Ctx L g₂ mx₂ m₂ b ∧ Φ L m₁ a ∧ Φ L m₂ b

section
variable {I : VG.Proof.Ed448.X86_64.SignCached.Lay → Mem → Mem → Prop}

theorem Two.rsp {Φ : VG.Proof.Ed448.X86_64.SignCached.Lay → Mem → State → Prop} {a b : State} (h : VG.Proof.Ed448.X86_64.SignCached.Two I Φ a b) : a.gpr .rsp = b.gpr .rsp :=
  let ⟨_, _, _, _, _, _, _, _, _, c₁, c₂, _, _⟩ := h; c₁.rsp.trans c₂.rsp.symm

theorem two_wp {c : Prog isa} {Φ Ψ : VG.Proof.Ed448.X86_64.SignCached.Lay → Mem → State → Prop}
    (hct : RelCT isa (VG.Proof.Ed448.X86_64.SignCached.Two I Φ) c fun _ _ => True)
    (hw : ∀ (L : VG.Proof.Ed448.X86_64.SignCached.Lay) g mx m₀ (t : State), L.Ok → VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t → Φ L m₀ t →
      WP isa c t fun t' => VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (VG.Proof.Ed448.X86_64.SignCached.Two I Φ) c (VG.Proof.Ed448.X86_64.SignCached.Two I Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨L, g₁, g₂, mx₁, mx₂, m₁, m₂, hL, hi, c₁, c₂, f₁, f₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw L g₁ mx₁ m₁ s₁ hL c₁ f₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw L g₂ mx₂ m₂ s₂ hL c₂ f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, L, g₁, g₂, mx₁, mx₂, m₁, m₂, hL, hi, y₁.1, y₂.1, y₁.2, y₂.2⟩

theorem two_mono {Φ Ψ : VG.Proof.Ed448.X86_64.SignCached.Lay → Mem → State → Prop} (h : ∀ L m t, Φ L m t → Ψ L m t) {a b : State}
    (hp : VG.Proof.Ed448.X86_64.SignCached.Two I Φ a b) : VG.Proof.Ed448.X86_64.SignCached.Two I Ψ a b :=
  let ⟨L, g₁, g₂, mx₁, mx₂, m₁, m₂, hL, hi, c₁, c₂, f₁, f₂⟩ := hp
  ⟨L, g₁, g₂, mx₁, mx₂, m₁, m₂, hL, hi, c₁, c₂, h _ _ _ f₁, h _ _ _ f₂⟩

/-- A call after the moves of its arguments, of verified code whose public
data agree in both runs. -/
theorem call_tr {Φ : VG.Proof.Ed448.X86_64.SignCached.Lay → Mem → State → Prop} {as : List Arg} (hok : as.all Arg.ok = true) {n : String}
    {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (rd wr : VG.Proof.Ed448.X86_64.SignCached.Lay → List Region)
    (hpre : ∀ (L : VG.Proof.Ed448.X86_64.SignCached.Lay) g mx m₀ (t t1 : State), L.Ok → VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t → Φ L m₀ t → Moved as t t1 →
      k.pre (t1.callEntry.withRegions (rd L) (wr L)))
    (hpub : ∀ (L : VG.Proof.Ed448.X86_64.SignCached.Lay) g₁ g₂ mx₁ mx₂ m₁ m₂ (a b a1 b1 : State), L.Ok → I L m₁ m₂ → VG.Proof.Ed448.X86_64.SignCached.Ctx L g₁ mx₁ m₁ a →
      VG.Proof.Ed448.X86_64.SignCached.Ctx L g₂ mx₂ m₂ b → Φ L m₁ a → Φ L m₂ b → Moved as a a1 → Moved as b b1 →
      k.pub (a1.callEntry.withRegions (rd L) (wr L)) (b1.callEntry.withRegions (rd L) (wr L)))
    (hcov : ∀ (L : VG.Proof.Ed448.X86_64.SignCached.Lay) g mx m₀ (t : State), L.Ok → VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t → Φ L m₀ t →
      (∀ r ∈ rd L, ∃ R ∈ L.rd ++ L.FR :: L.wr, Within r R) ∧ (∀ r ∈ wr L, ∃ R ∈ L.FR :: L.wr, Within r R)) :
    RelCT isa (VG.Proof.Ed448.X86_64.SignCached.Two I Φ) (callA n c as) fun _ _ => True := by
  refine RelCT.seq (RelCT.postDep (Q := fun a1 b1 => ∃ a b, VG.Proof.Ed448.X86_64.SignCached.Two I Φ a b ∧ Moved as a a1 ∧ Moved as b b1)
    (block_rsp_tr (setArgs_spOnly as) fun _ _ h => h.rsp)
    (fun x y ⟨_, _, _, _, _, _, _, _, _, c₁, c₂, _, _⟩ =>
      ⟨setArgs_ok as hok x c₁.frOk, setArgs_ok as hok y c₂.frOk⟩)
    fun x y x1 y1 hp f₁ f₂ => ⟨x, y, hp, f₁, f₂⟩) ?_
  refine RelCT.callEx hv hct fun a1 b1 ⟨a, b, hp, f₁, f₂⟩ => ?_
  obtain ⟨L, g₁, g₂, mx₁, mx₂, m₁, m₂, hL, hi, c₁, c₂, φ₁, φ₂⟩ := hp
  obtain ⟨hr, hw⟩ := hcov L g₁ mx₁ m₁ a hL c₁ φ₁
  have cov : ∀ {t t1 : State} {g mx m₀}, VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t → Moved as t t1 →
      Covers (rd L ++ wr L) (t1.rd ++ t1.wr) ∧ Covers (wr L) t1.wr := fun hc f => by
    rw [f.2.2.1, f.2.2.2, hc.rd, hc.wr]
    refine ⟨covers_of_within fun r hr' => ?_, covers_of_within fun r hr' => ?_⟩
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

end VG.Proof.Ed448.X86_64.SignCached

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86_64.SignCached.HashCT`. -/
section

/-!
# Ed448 signing with a cached public key on x86-64: the hashes leak only the layout

Two runs (`Two`) of the zeroing of the Keccak state and of the calls of the
sponge functions, whose arguments are the same in both runs (functions of
the layout), leak the same (`zeroSt_tr`, `kabs_tr`, `kpad_tr`, `ksqz_tr`); and
so do the three hashes (`seedHash_tr`, `nonceHash_tr`, `chalHash_tr`), each
absorption starting at the position the previous one returned, a function of
the lengths.
-/

namespace VG.Proof.Ed448.X86_64.SignCached

open VG VG.X86_64
open VG.Impl.Ed448.X86_64.Verify (stk Arg zeroSt kabs kpad ksqz aSt aKs fHdr fH fPk fCtx fCtxLen fMsg fLen fScr)
open VG.Impl.Ed448.X86_64.SignCached (fSeed fOut seedHash nonceHash chalHash)
open VG.Proof.Ed448.X86_64.Verify (Within within_off within_base within_self ne_cs x0 Moved block_rsp_tr
  spOnly_nomem SpOnly setArgs_ok argRegs_cs gpr_ce rsp_ce argsIn5 argsIn6 ofNat_toNat_self ofNat_toNat_eq)
open VG.Proof.MlKem.X86_64 (Keep WP.keep AbsorbArgs PadArgs SqueezeArgs absorb_pre pad_pre squeeze_pre)

section
variable {I : VG.Proof.Ed448.X86_64.SignCached.Lay → Mem → Mem → Prop}

/-! ## Zeroing the state -/

theorem zhead_ok {L : VG.Proof.Ed448.X86_64.SignCached.Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem} {t : State}
    (hc : VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t) :
    WP isa (.block [.mov .rdi (.mem (stk fScr)), .mov32 .rax (.imm 0)]) t fun t2 =>
      VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t2 ∧ t2.gpr .rdi = L.ST := by
  show WP isa (.block (aSt.mov .rdi ++ [.mov32 .rax (.imm 0)])) t _
  rw [WP.block_append_iff]
  refine WP.mono (Verify.Arg.mov_ok .rdi VG.Impl.Ed448.X86_64.Verify.aSt (by decide) (by decide) t hc.frOk) fun t1 ⟨⟨h1, hm1, hx1⟩, k1⟩ => ?_
  refine WP.mono (WP.keep [.rax] (Q := fun s1 => s1.mem = t1.mem ∧ s1.mxcsr = t1.mxcsr)
    (by xrun [RegUpd.mxcsr_setReg]) (by decide)) fun t2 ⟨⟨hm2, hx2⟩, k2⟩ => ?_
  have hc1 : VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t1 := hc.regs k1.2.1 k1.2.2 hm1 hx1 fun r hr => k1.gpr (by
    simp only [List.mem_singleton]; exact ne_cs hr (by decide))
  exact ⟨hc1.regs k2.2.1 k2.2.2 hm2 hx2 fun r hr => k2.gpr (by
    simp only [List.mem_singleton]; exact ne_cs hr (by decide)), (k2.gpr (by decide)).trans (h1.trans hc.aSt)⟩

theorem zeroSt_tr {Φ : VG.Proof.Ed448.X86_64.SignCached.Lay → Mem → State → Prop} : RelCT isa (VG.Proof.Ed448.X86_64.SignCached.Two I Φ) VG.Impl.Ed448.X86_64.Verify.zeroSt fun _ _ => True := by
  have h1 := VG.Proof.Ed448.X86_64.SignCached.two_wp (I := I) (Φ := Φ) (Ψ := fun L _ t => t.gpr .rdi = L.ST)
    (c := .block [.mov .rdi (.mem (stk fScr)), .mov32 .rax (.imm 0)])
    (block_rsp_tr (fun i hi => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · exact ⟨fun s₁ s₂ h => by simp [addrs, srcAddrs, State.ea, stk, h], rfl⟩
        · exact spOnly_nomem (fun _ => rfl) rfl) fun _ _ h => h.rsp)
    fun _ _ _ _ _ _ hc _ => VG.Proof.Ed448.X86_64.SignCached.zhead_ok hc
  refine RelCT.seq h1 (RelCT.taint (A := taint) (Taint.ofRegs [.rsp, .rdi]) (fun a b hab => ?_) (by taint_decide))
  obtain ⟨L, _, _, _, _, _, _, _, _, c₁, c₂, f₁, f₂⟩ := hab
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [c₁.rsp, c₂.rsp]
  · rw [f₁, f₂]

/-! ## The sponge functions -/

/-- The arguments of a call of `vg_keccak_absorb`, after the moves. -/
theorem kabsArgs {L : VG.Proof.Ed448.X86_64.SignCached.Lay} (hL : L.Ok) {g mx m₀} {t t1 : State} (hc : VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t)
    {src len pos : Arg} (hm : Moved (VG.Proof.Ed448.X86_64.SignCached.absArgs src len pos) t t1) {dp : Addr} {n q : Nat}
    (hdp : src.val t = dp) (hn : len.val t = BitVec.ofNat 64 n) (hq : pos.val t = BitVec.ofNat 64 q)
    (hql : q < 136) (hnl : n < 2 ^ 64) (dS : Region.Disjoint ⟨dp, n⟩ ⟨L.ST, 200⟩)
    (dK : Region.Disjoint ⟨dp, n⟩ ⟨L.KS, 640⟩) (kD : Region.Disjoint ⟨L.B, 16⟩ ⟨dp, n⟩) :
    AbsorbArgs t1 L.ST dp L.KS 136 q n := by
  have hc1 : VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t1 := hc.regs hm.2.2.1 hm.2.2.2 hm.1.2.1 hm.1.2.2 fun r hr => hm.2.gpr (argRegs_cs r hr)
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := argsIn6 hm.1.1
  rw [hc.aSt] at e1
  rw [hc.aKs] at e6
  rw [hdp] at e4
  rw [hn] at e5
  rw [hq] at e3
  exact ⟨e1, e2, e3, e4, e5, e6, by decide, hql, hnl, VG.Proof.Ed448.X86_64.SignCached.st_ks L, dS, dK, VG.Proof.Ed448.X86_64.SignCached.k16 hc1 (VG.Proof.Ed448.X86_64.SignCached.k_st hL), VG.Proof.Ed448.X86_64.SignCached.k16 hc1 kD,
    VG.Proof.Ed448.X86_64.SignCached.k16 hc1 (VG.Proof.Ed448.X86_64.SignCached.k_ks hL)⟩

theorem w_scr {L : VG.Proof.Ed448.X86_64.SignCached.Lay} (hL : L.Ok) {r : Region} (h : Within r L.SCR) : ∃ R ∈ L.FR :: L.wr, Within r R :=
  ⟨L.SCR, by simp [hL.wr], h⟩

/-- Two runs of a call of `vg_keccak_absorb` whose arguments are the same
functions of the layout in both. -/
theorem kabs_tr {Φ : VG.Proof.Ed448.X86_64.SignCached.Lay → Mem → State → Prop} {src len pos : Arg}
    (hok : (VG.Proof.Ed448.X86_64.SignCached.absArgs src len pos).all Arg.ok = true) (dp : VG.Proof.Ed448.X86_64.SignCached.Lay → Addr) (n q : VG.Proof.Ed448.X86_64.SignCached.Lay → Nat)
    (hv : ∀ (L : VG.Proof.Ed448.X86_64.SignCached.Lay) g mx m (t : State), L.Ok → VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m t → Φ L m t →
      src.val t = dp L ∧ len.val t = BitVec.ofNat 64 (n L) ∧ pos.val t = BitVec.ofNat 64 (q L))
    (hs : ∀ L : VG.Proof.Ed448.X86_64.SignCached.Lay, L.Ok → q L < 136 ∧ n L < 2 ^ 64 ∧ (∃ R ∈ L.rd ++ L.FR :: L.wr, Within ⟨dp L, n L⟩ R) ∧
      Region.Disjoint ⟨dp L, n L⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨dp L, n L⟩ ⟨L.KS, 640⟩ ∧
      Region.Disjoint ⟨L.B, 16⟩ ⟨dp L, n L⟩) :
    RelCT isa (VG.Proof.Ed448.X86_64.SignCached.Two I Φ) (VG.Impl.Ed448.X86_64.Verify.kabs src len pos) fun _ _ => True := by
  have args : ∀ (L : VG.Proof.Ed448.X86_64.SignCached.Lay) g mx m₀ (t t1 : State), L.Ok → VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t → Φ L m₀ t →
      Moved (VG.Proof.Ed448.X86_64.SignCached.absArgs src len pos) t t1 → AbsorbArgs t1 L.ST (dp L) L.KS 136 (q L) (n L) :=
    fun L g mx m₀ t t1 hL hc hφ hm => by
      obtain ⟨h1, h2, h3⟩ := hv L g mx m₀ t hL hc hφ
      obtain ⟨s1, s2, _, s4, s5, s6⟩ := hs L hL
      exact VG.Proof.Ed448.X86_64.SignCached.kabsArgs hL hc hm h1 h2 h3 s1 s2 s4 s5 s6
  refine VG.Proof.Ed448.X86_64.SignCached.call_tr hok Proof.Sha3.X86_64.Stream.Absorb.absorb_correct
    Proof.Sha3.X86_64.Stream.Absorb.absorb_ct (fun L => [⟨dp L, n L⟩]) (fun L => [⟨L.ST, 200⟩, ⟨L.KS, 640⟩])
    (fun L g mx m₀ t t1 hL hc hφ hm => absorb_pre (args L g mx m₀ t t1 hL hc hφ hm))
    (fun L g₁ g₂ mx₁ mx₂ m₁ m₂ a b a1 b1 hL _ c₁ c₂ φ₁ φ₂ f₁ f₂ => ?_) fun L _ _ _ _ hL _ _ => ?_
  · have x := args L g₁ mx₁ m₁ a a1 hL c₁ φ₁ f₁
    have y := args L g₂ mx₂ m₂ b b1 hL c₂ φ₂ f₂
    simp only [Proof.Sha3.absorbX86_64, gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp),
      gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp),
      gpr_ce _ _ _ (by decide : Reg.rcx ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.r8 ≠ .rsp),
      gpr_ce _ _ _ (by decide : Reg.r9 ≠ .rsp), rsp_ce, x.rdi, x.rsi, x.rdx, x.rcx, x.r8, x.r9, y.rdi, y.rsi,
      y.rdx, y.rcx, y.r8, y.r9, f₁.2.gpr (by decide : Reg.rsp ∉ Verify.argRegs), f₂.2.gpr (by decide : Reg.rsp ∉ Verify.argRegs),
      c₁.rsp, c₂.rsp, and_self]
  · obtain ⟨_, _, hin, _, _, _⟩ := hs L hL
    refine ⟨fun r hr => ?_, fun r hr => ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact hin
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [VG.Proof.Ed448.X86_64.SignCached.w_scr hL (within_base _ (by decide)), VG.Proof.Ed448.X86_64.SignCached.w_scr hL (within_off _ (by decide))]

/-- The position in `rax`, a function of the layout. -/
abbrev Pos (q : VG.Proof.Ed448.X86_64.SignCached.Lay → Nat) : VG.Proof.Ed448.X86_64.SignCached.Lay → Mem → State → Prop := fun L _ t => (t.gpr .rax).toNat = q L

/-- An absorption, with the position it returns. -/
theorem kabs_two {Φ : VG.Proof.Ed448.X86_64.SignCached.Lay → Mem → State → Prop} {src len pos : Arg}
    (hok : (VG.Proof.Ed448.X86_64.SignCached.absArgs src len pos).all Arg.ok = true) (dp : VG.Proof.Ed448.X86_64.SignCached.Lay → Addr) (n q : VG.Proof.Ed448.X86_64.SignCached.Lay → Nat)
    (hv : ∀ (L : VG.Proof.Ed448.X86_64.SignCached.Lay) g mx m (t : State), L.Ok → VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m t → Φ L m t →
      src.val t = dp L ∧ len.val t = BitVec.ofNat 64 (n L) ∧ pos.val t = BitVec.ofNat 64 (q L))
    (hs : ∀ L : VG.Proof.Ed448.X86_64.SignCached.Lay, L.Ok → q L < 136 ∧ n L < 2 ^ 64 ∧ (∃ R ∈ L.rd ++ L.FR :: L.wr, Within ⟨dp L, n L⟩ R) ∧
      Region.Disjoint ⟨dp L, n L⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨dp L, n L⟩ ⟨L.KS, 640⟩ ∧
      Region.Disjoint ⟨L.B, 16⟩ ⟨dp L, n L⟩) :
    RelCT isa (VG.Proof.Ed448.X86_64.SignCached.Two I Φ) (VG.Impl.Ed448.X86_64.Verify.kabs src len pos) (VG.Proof.Ed448.X86_64.SignCached.Two I (VG.Proof.Ed448.X86_64.SignCached.Pos fun L => (q L + n L) % 136)) :=
  VG.Proof.Ed448.X86_64.SignCached.two_wp (VG.Proof.Ed448.X86_64.SignCached.kabs_tr hok dp n q hv hs) fun L g mx m₀ t hL hc hφ => by
    obtain ⟨h1, h2, h3⟩ := hv L g mx m₀ t hL hc hφ
    obtain ⟨a, b, c, d, e, f⟩ := hs L hL
    exact WP.mono (VG.Proof.Ed448.X86_64.SignCached.kabs_ok hL hc hok h1 h2 h3 a b c d e f) fun t' ⟨hc', _, _, hx⟩ => ⟨hc', hx⟩

theorem kpad_tr {Φ : VG.Proof.Ed448.X86_64.SignCached.Lay → Mem → State → Prop} {pos : Arg}
    (hok : (VG.Proof.Ed448.X86_64.SignCached.padArgs pos).all Arg.ok = true) (q : VG.Proof.Ed448.X86_64.SignCached.Lay → Nat)
    (hv : ∀ (L : VG.Proof.Ed448.X86_64.SignCached.Lay) g mx m (t : State), L.Ok → VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m t → Φ L m t → pos.val t = BitVec.ofNat 64 (q L))
    (hs : ∀ L : VG.Proof.Ed448.X86_64.SignCached.Lay, L.Ok → q L < 136) :
    RelCT isa (VG.Proof.Ed448.X86_64.SignCached.Two I Φ) (VG.Impl.Ed448.X86_64.Verify.kpad pos) fun _ _ => True := by
  have args : ∀ (L : VG.Proof.Ed448.X86_64.SignCached.Lay) g mx m₀ (t t1 : State), L.Ok → VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t → Φ L m₀ t →
      Moved (VG.Proof.Ed448.X86_64.SignCached.padArgs pos) t t1 → PadArgs t1 L.ST L.KS 136 (q L) :=
    fun L g mx m₀ t t1 hL hc hφ hm => by
      have hc1 : VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t1 :=
        hc.regs hm.2.2.1 hm.2.2.2 hm.1.2.1 hm.1.2.2 fun r hr => hm.2.gpr (argRegs_cs r hr)
      obtain ⟨e1, e2, e3, _, e5⟩ := argsIn5 hm.1.1
      rw [hc.aSt] at e1
      rw [hc.aKs] at e5
      rw [hv L g mx m₀ t hL hc hφ] at e3
      exact ⟨e1, e2, e3, e5, by decide, hs L hL, VG.Proof.Ed448.X86_64.SignCached.st_ks L, VG.Proof.Ed448.X86_64.SignCached.k16 hc1 (VG.Proof.Ed448.X86_64.SignCached.k_st hL), VG.Proof.Ed448.X86_64.SignCached.k16 hc1 (VG.Proof.Ed448.X86_64.SignCached.k_ks hL)⟩
  refine VG.Proof.Ed448.X86_64.SignCached.call_tr hok Proof.Sha3.X86_64.Stream.Pad.pad_correct Proof.Sha3.X86_64.Stream.Pad.pad_ct
    (fun _ => []) (fun L => [⟨L.ST, 200⟩, ⟨L.KS, 640⟩])
    (fun L g mx m₀ t t1 hL hc hφ hm => pad_pre (args L g mx m₀ t t1 hL hc hφ hm))
    (fun L g₁ g₂ mx₁ mx₂ m₁ m₂ a b a1 b1 hL _ c₁ c₂ φ₁ φ₂ f₁ f₂ => ?_) fun L _ _ _ _ hL _ _ => ?_
  · have x := args L g₁ mx₁ m₁ a a1 hL c₁ φ₁ f₁
    have y := args L g₂ mx₂ m₂ b b1 hL c₂ φ₂ f₂
    simp only [Proof.Sha3.padX86_64, gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp),
      gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp),
      gpr_ce _ _ _ (by decide : Reg.r8 ≠ .rsp), rsp_ce, x.rdi, x.rsi, x.rdx, x.r8, y.rdi, y.rsi, y.rdx, y.r8,
      f₁.2.gpr (by decide : Reg.rsp ∉ Verify.argRegs), f₂.2.gpr (by decide : Reg.rsp ∉ Verify.argRegs), c₁.rsp, c₂.rsp,
      and_self]
  · refine ⟨fun r hr => by simp at hr, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [VG.Proof.Ed448.X86_64.SignCached.w_scr hL (within_base _ (by decide)), VG.Proof.Ed448.X86_64.SignCached.w_scr hL (within_off _ (by decide))]

theorem ksqz_tr {Φ : VG.Proof.Ed448.X86_64.SignCached.Lay → Mem → State → Prop} : RelCT isa (VG.Proof.Ed448.X86_64.SignCached.Two I Φ) VG.Impl.Ed448.X86_64.Verify.ksqz fun _ _ => True := by
  have args : ∀ (L : VG.Proof.Ed448.X86_64.SignCached.Lay) g mx m₀ (t t1 : State), L.Ok → VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t → Φ L m₀ t →
      Moved VG.Proof.Ed448.X86_64.SignCached.sqzArgs t t1 → SqueezeArgs t1 L.ST L.H L.KS 136 0 114 :=
    fun L g mx m₀ t t1 hL hc _ hm => by
      have hc1 : VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t1 :=
        hc.regs hm.2.2.1 hm.2.2.2 hm.1.2.1 hm.1.2.2 fun r hr => hm.2.gpr (argRegs_cs r hr)
      obtain ⟨e1, e2, e3, e4, e5, e6⟩ := argsIn6 hm.1.1
      rw [hc.aSt] at e1
      rw [hc.aKs] at e6
      rw [hc.sp] at e4
      exact ⟨e1, e2, e3, e4, e5, e6, by decide, by decide, by decide, VG.Proof.Ed448.X86_64.SignCached.st_h hL, VG.Proof.Ed448.X86_64.SignCached.st_ks L, VG.Proof.Ed448.X86_64.SignCached.h_ks hL,
        VG.Proof.Ed448.X86_64.SignCached.k16 hc1 (VG.Proof.Ed448.X86_64.SignCached.k_st hL), VG.Proof.Ed448.X86_64.SignCached.k16 hc1 VG.Proof.Ed448.X86_64.SignCached.k_h, VG.Proof.Ed448.X86_64.SignCached.k16 hc1 (VG.Proof.Ed448.X86_64.SignCached.k_ks hL)⟩
  refine VG.Proof.Ed448.X86_64.SignCached.call_tr (by decide) Proof.Sha3.X86_64.Stream.Squeeze.squeeze_correct
    Proof.Sha3.X86_64.Stream.Squeeze.squeeze_ct (fun _ => []) (fun L => [⟨L.ST, 200⟩, ⟨L.H, 114⟩, ⟨L.KS, 640⟩])
    (fun L g mx m₀ t t1 hL hc hφ hm => squeeze_pre (args L g mx m₀ t t1 hL hc hφ hm))
    (fun L g₁ g₂ mx₁ mx₂ m₁ m₂ a b a1 b1 hL _ c₁ c₂ φ₁ φ₂ f₁ f₂ => ?_) fun L _ _ _ _ hL _ _ => ?_
  · have x := args L g₁ mx₁ m₁ a a1 hL c₁ φ₁ f₁
    have y := args L g₂ mx₂ m₂ b b1 hL c₂ φ₂ f₂
    simp only [Proof.Sha3.squeezeX86_64, gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp),
      gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp),
      gpr_ce _ _ _ (by decide : Reg.rcx ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.r8 ≠ .rsp),
      gpr_ce _ _ _ (by decide : Reg.r9 ≠ .rsp), rsp_ce, x.rdi, x.rsi, x.rdx, x.rcx, x.r8, x.r9, y.rdi, y.rsi,
      y.rdx, y.rcx, y.r8, y.r9, f₁.2.gpr (by decide : Reg.rsp ∉ Verify.argRegs), f₂.2.gpr (by decide : Reg.rsp ∉ Verify.argRegs),
      c₁.rsp, c₂.rsp, and_self]
  · refine ⟨fun r hr => by simp at hr, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [VG.Proof.Ed448.X86_64.SignCached.w_scr hL (within_base _ (by decide)), ⟨L.FR, by simp, within_off _ (by decide)⟩,
      VG.Proof.Ed448.X86_64.SignCached.w_scr hL (within_off _ (by decide))]

/-! ## The hashes -/

/-- The positions after each piece absorbed. -/
abbrev q1 (_ : VG.Proof.Ed448.X86_64.SignCached.Lay) : Nat := (0 + 10) % 136
abbrev q2 (L : VG.Proof.Ed448.X86_64.SignCached.Lay) : Nat := (VG.Proof.Ed448.X86_64.SignCached.q1 L + L.ctxLen.toNat) % 136
abbrev q3 (L : VG.Proof.Ed448.X86_64.SignCached.Lay) : Nat := (VG.Proof.Ed448.X86_64.SignCached.q2 L + 57) % 136
abbrev q4 (L : VG.Proof.Ed448.X86_64.SignCached.Lay) : Nat := (VG.Proof.Ed448.X86_64.SignCached.q3 L + L.len.toNat) % 136
abbrev q4' (L : VG.Proof.Ed448.X86_64.SignCached.Lay) : Nat := (VG.Proof.Ed448.X86_64.SignCached.q3 L + 57) % 136
abbrev q5' (L : VG.Proof.Ed448.X86_64.SignCached.Lay) : Nat := (VG.Proof.Ed448.X86_64.SignCached.q4' L + L.len.toNat) % 136

/-- Where the pieces are, as `kabs_tr` needs them. -/
theorem side {L : VG.Proof.Ed448.X86_64.SignCached.Lay} (_hL : L.Ok) {q : Nat} (hq : q < 136) {r : Region} (hn : r.len < 2 ^ 64)
    (h : (∃ R ∈ L.rd ++ L.FR :: L.wr, Within r R) ∧ Region.Disjoint r ⟨L.ST, 200⟩ ∧
      Region.Disjoint r ⟨L.KS, 640⟩ ∧ Region.Disjoint ⟨L.B, 16⟩ r) :
    q < 136 ∧ r.len < 2 ^ 64 ∧ (∃ R ∈ L.rd ++ L.FR :: L.wr, Within ⟨r.base, r.len⟩ R) ∧
      Region.Disjoint ⟨r.base, r.len⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨r.base, r.len⟩ ⟨L.KS, 640⟩ ∧
      Region.Disjoint ⟨L.B, 16⟩ ⟨r.base, r.len⟩ :=
  ⟨hq, hn, h.1, h.2.1, h.2.2.1, h.2.2.2⟩

theorem zero_two {Φ : VG.Proof.Ed448.X86_64.SignCached.Lay → Mem → State → Prop} : RelCT isa (VG.Proof.Ed448.X86_64.SignCached.Two I Φ) VG.Impl.Ed448.X86_64.Verify.zeroSt (VG.Proof.Ed448.X86_64.SignCached.Two I fun _ _ _ => True) :=
  VG.Proof.Ed448.X86_64.SignCached.two_wp VG.Proof.Ed448.X86_64.SignCached.zeroSt_tr fun _ _ _ _ _ hL hc _ => WP.mono (VG.Proof.Ed448.X86_64.SignCached.zeroSt_ok hL hc) fun _ ⟨hc', _⟩ => ⟨hc', trivial⟩

theorem hdr_two : RelCT isa (VG.Proof.Ed448.X86_64.SignCached.Two I fun _ _ _ => True) (VG.Impl.Ed448.X86_64.Verify.kabs (.sp fHdr) (.imm 10) (.imm 0)) (VG.Proof.Ed448.X86_64.SignCached.Two I (VG.Proof.Ed448.X86_64.SignCached.Pos VG.Proof.Ed448.X86_64.SignCached.q1)) :=
  VG.Proof.Ed448.X86_64.SignCached.kabs_two (src := .sp fHdr) (len := .imm 10) (pos := .imm 0)
    (by decide) (fun L => L.SP + BitVec.ofNat 64 0) (fun _ => 10) (fun _ => 0)
    (fun L g mx m t _ hc _ => ⟨by rw [hc.sp]; rfl, rfl, rfl⟩)
    fun L hL => VG.Proof.Ed448.X86_64.SignCached.side hL (by decide) (show (10 : Nat) < 2 ^ 64 by decide) (VG.Proof.Ed448.X86_64.SignCached.frSide hL (d := 0) (n := 10) (by omega))

theorem ctx_two : RelCT isa (VG.Proof.Ed448.X86_64.SignCached.Two I (VG.Proof.Ed448.X86_64.SignCached.Pos VG.Proof.Ed448.X86_64.SignCached.q1)) (VG.Impl.Ed448.X86_64.Verify.kabs (.slot fCtx) (.slot fCtxLen) .ret) (VG.Proof.Ed448.X86_64.SignCached.Two I (VG.Proof.Ed448.X86_64.SignCached.Pos VG.Proof.Ed448.X86_64.SignCached.q2)) :=
  VG.Proof.Ed448.X86_64.SignCached.kabs_two (src := .slot fCtx) (len := .slot fCtxLen) (pos := .ret)
    (by decide) (fun L => L.ctx) (fun L => L.ctxLen.toNat) VG.Proof.Ed448.X86_64.SignCached.q1
    (fun L g mx m t _ hc hφ => ⟨by rw [hc.slot]; exact hc.pCtx,
      by rw [hc.slot, hc.pCtxLen, ofNat_toNat_self], ofNat_toNat_eq hφ⟩)
    fun L hL => VG.Proof.Ed448.X86_64.SignCached.side hL (show (0 + 10) % 136 < 136 by decide) L.ctxLen.isLt
      (VG.Proof.Ed448.X86_64.SignCached.bufSide hL ⟨L.CTX, List.mem_append_left _ hL.inCtx, within_self _⟩ hL.xCtx hL.kCtx)

theorem seedHash_tr {Φ : VG.Proof.Ed448.X86_64.SignCached.Lay → Mem → State → Prop} : RelCT isa (VG.Proof.Ed448.X86_64.SignCached.Two I Φ) seedHash fun _ _ => True := by
  have z := VG.Proof.Ed448.X86_64.SignCached.two_wp (I := I) (Φ := Φ) (Ψ := fun _ _ _ => True) VG.Proof.Ed448.X86_64.SignCached.zeroSt_tr
    fun L g mx m₀ t hL hc _ => WP.mono (VG.Proof.Ed448.X86_64.SignCached.zeroSt_ok hL hc) fun t' ⟨hc', _⟩ => ⟨hc', trivial⟩
  have a1 := VG.Proof.Ed448.X86_64.SignCached.kabs_two (I := I) (Φ := fun _ _ _ => True) (src := .slot fSeed) (len := .imm 57) (pos := .imm 0)
    (by decide) (fun L => L.seed) (fun _ => 57) (fun _ => 0)
    (fun L g mx m t _ hc _ => ⟨by rw [hc.slot]; exact hc.pSeed, rfl, rfl⟩)
    fun L hL => VG.Proof.Ed448.X86_64.SignCached.side hL (by decide) (show (57 : Nat) < 2 ^ 64 by decide)
      (VG.Proof.Ed448.X86_64.SignCached.bufSide hL ⟨L.SEED, List.mem_append_left _ hL.inSeed, within_self _⟩ hL.xSeed hL.kSeed)
  have pd := VG.Proof.Ed448.X86_64.SignCached.two_wp (I := I) (Φ := VG.Proof.Ed448.X86_64.SignCached.Pos fun _ => (0 + 57) % 136) (Ψ := fun _ _ _ => True)
    (VG.Proof.Ed448.X86_64.SignCached.kpad_tr (pos := .imm 57) (by decide) (fun _ => 57) (fun _ _ _ _ _ _ _ _ => rfl) fun _ _ => by decide)
    fun L g mx m₀ t hL hc _ => WP.mono (VG.Proof.Ed448.X86_64.SignCached.kpad_ok hL hc (pos := .imm 57) (by decide) rfl (by decide))
      fun t' ⟨hc', _⟩ => ⟨hc', trivial⟩
  exact RelCT.seq z (a1.seq (pd.seq VG.Proof.Ed448.X86_64.SignCached.ksqz_tr))

/-- The message, the padding and the squeezing, from the position `q`. -/
theorem msgTail_tr {q : VG.Proof.Ed448.X86_64.SignCached.Lay → Nat} (hq : ∀ L, q L < 136) :
    RelCT isa (VG.Proof.Ed448.X86_64.SignCached.Two I (VG.Proof.Ed448.X86_64.SignCached.Pos q)) (.seq (VG.Impl.Ed448.X86_64.Verify.kabs (.slot fMsg) (.slot fLen) .ret) (.seq (VG.Impl.Ed448.X86_64.Verify.kpad .ret) VG.Impl.Ed448.X86_64.Verify.ksqz))
      fun _ _ => True := by
  have a := VG.Proof.Ed448.X86_64.SignCached.kabs_two (I := I) (Φ := VG.Proof.Ed448.X86_64.SignCached.Pos q) (src := .slot fMsg) (len := .slot fLen) (pos := .ret)
    (by decide) (fun L => L.msg) (fun L => L.len.toNat) q
    (fun L g mx m t _ hc hφ => ⟨by rw [hc.slot]; exact hc.pMsg,
      by rw [hc.slot, hc.pLen, ofNat_toNat_self], ofNat_toNat_eq hφ⟩)
    fun L hL => VG.Proof.Ed448.X86_64.SignCached.side hL (hq L) L.len.isLt
      (VG.Proof.Ed448.X86_64.SignCached.bufSide hL ⟨L.MSG, List.mem_append_left _ hL.inMsg, within_self _⟩ hL.xMsg hL.kMsg)
  have pd := VG.Proof.Ed448.X86_64.SignCached.two_wp (I := I) (Φ := VG.Proof.Ed448.X86_64.SignCached.Pos fun L => (q L + L.len.toNat) % 136) (Ψ := fun _ _ _ => True)
    (VG.Proof.Ed448.X86_64.SignCached.kpad_tr (pos := .ret) (by decide) (fun L => (q L + L.len.toNat) % 136)
      (fun _ _ _ _ _ _ _ hφ => ofNat_toNat_eq hφ) fun _ _ => Nat.mod_lt _ (by decide))
    fun L g mx m₀ t hL hc hφ => WP.mono (VG.Proof.Ed448.X86_64.SignCached.kpad_ok hL hc (pos := .ret) (by decide) (ofNat_toNat_eq hφ)
      (Nat.mod_lt _ (by decide))) fun t' ⟨hc', _⟩ => ⟨hc', trivial⟩
  exact a.seq (pd.seq VG.Proof.Ed448.X86_64.SignCached.ksqz_tr)

theorem nonceHash_tr {Φ : VG.Proof.Ed448.X86_64.SignCached.Lay → Mem → State → Prop} : RelCT isa (VG.Proof.Ed448.X86_64.SignCached.Two I Φ) nonceHash fun _ _ => True := by
  have a3 := VG.Proof.Ed448.X86_64.SignCached.kabs_two (I := I) (Φ := VG.Proof.Ed448.X86_64.SignCached.Pos VG.Proof.Ed448.X86_64.SignCached.q2) (src := .sp (fH + 57)) (len := .imm 57) (pos := .ret)
    (by decide) (fun L => L.SP + BitVec.ofNat 64 73) (fun _ => 57) VG.Proof.Ed448.X86_64.SignCached.q2
    (fun L g mx m t _ hc hφ => ⟨by rw [hc.sp]; rfl, rfl, ofNat_toNat_eq hφ⟩)
    fun L hL => VG.Proof.Ed448.X86_64.SignCached.side hL (Nat.mod_lt _ (by decide)) (show (57 : Nat) < 2 ^ 64 by decide)
      (VG.Proof.Ed448.X86_64.SignCached.frSide hL (d := 73) (n := 57) (by omega))
  exact zero_two.seq (hdr_two.seq (ctx_two.seq (a3.seq (VG.Proof.Ed448.X86_64.SignCached.msgTail_tr (q := VG.Proof.Ed448.X86_64.SignCached.q3) fun _ => Nat.mod_lt _ (by decide)))))

theorem chalHash_tr {Φ : VG.Proof.Ed448.X86_64.SignCached.Lay → Mem → State → Prop} : RelCT isa (VG.Proof.Ed448.X86_64.SignCached.Two I Φ) chalHash fun _ _ => True := by
  have a3 := VG.Proof.Ed448.X86_64.SignCached.kabs_two (I := I) (Φ := VG.Proof.Ed448.X86_64.SignCached.Pos VG.Proof.Ed448.X86_64.SignCached.q2) (src := .slot fOut) (len := .imm 57) (pos := .ret)
    (by decide) (fun L => L.out) (fun _ => 57) VG.Proof.Ed448.X86_64.SignCached.q2
    (fun L g mx m t _ hc hφ => ⟨by rw [hc.slot]; exact hc.pOut, rfl, ofNat_toNat_eq hφ⟩)
    fun L hL => VG.Proof.Ed448.X86_64.SignCached.side hL (Nat.mod_lt _ (by decide)) (show (57 : Nat) < 2 ^ 64 by decide)
      (VG.Proof.Ed448.X86_64.SignCached.bufSide hL (r := ⟨L.out, 57⟩) ⟨L.OUT, by simp [hL.wr], within_base _ (by omega)⟩
      (hL.xOut.sub_right VG.Proof.Ed448.X86_64.SignCached.o57_sub) (hL.kOut.sub_right VG.Proof.Ed448.X86_64.SignCached.o57_sub))
  have a4 := VG.Proof.Ed448.X86_64.SignCached.kabs_two (I := I) (Φ := VG.Proof.Ed448.X86_64.SignCached.Pos VG.Proof.Ed448.X86_64.SignCached.q3) (src := .slot fPk) (len := .imm 57) (pos := .ret)
    (by decide) (fun L => L.pk) (fun _ => 57) VG.Proof.Ed448.X86_64.SignCached.q3
    (fun L g mx m t _ hc hφ => ⟨by rw [hc.slot]; exact hc.pPk, rfl, ofNat_toNat_eq hφ⟩)
    fun L hL => VG.Proof.Ed448.X86_64.SignCached.side hL (Nat.mod_lt _ (by decide)) (show (57 : Nat) < 2 ^ 64 by decide)
      (VG.Proof.Ed448.X86_64.SignCached.bufSide hL ⟨L.PK, List.mem_append_left _ hL.inPk, within_self _⟩ hL.xPk hL.kPk)
  exact zero_two.seq (hdr_two.seq (ctx_two.seq (a3.seq (a4.seq
    (VG.Proof.Ed448.X86_64.SignCached.msgTail_tr (q := VG.Proof.Ed448.X86_64.SignCached.q4') fun _ => Nat.mod_lt _ (by decide))))))

end

end VG.Proof.Ed448.X86_64.SignCached

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86_64.SignCached.Prune`. -/
section

/-!
# Ed448 signing with a cached public key on x86-64: `s`

The first 57 bytes of the hash in the frame, loaded into registers
(`loads_ok`), pruned (`mods_ok`) and stored at `s` (`stores_ok`): the number
of the 57 bytes at `s` is `Spec.Ed448.prune` of the hash (`prune_ok`).
-/

namespace VG.Proof.Ed448.X86_64.SignCached

open VG VG.X86_64 VG.Impl.Ed448.X86_64.SignCached
open VG.Impl.Ed448.X86_64.Verify (stk fH)
open VG.Proof.Ed448.X86_64.Verify (Within add_add ea_stk ne_cs)
open VG.Proof.MlKem.X86_64 (Keep WP.keep)
open VG.Proof.Ed448 (prune_nat)
open VG.Proof.Ed448.X86_64 (decode57 byte_of_zero take57)

section
variable {L : VG.Proof.Ed448.X86_64.SignCached.Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

/-- Word `k` of the hash. -/
abbrev hw (t : State) (L : VG.Proof.Ed448.X86_64.SignCached.Lay) (k : Nat) : BitVec 64 := t.mem.readW (L.SP + BitVec.ofNat 64 (16 + 8 * k)) 64

/-- The registers the pruning writes. -/
abbrev pRegs : List Reg := [.r8, .r9, .r10, .r11, .rax, .rcx, .rsi, .rdi]

theorem pRegs_cs : ∀ r ∈ calleeSaved, r ∉ VG.Proof.Ed448.X86_64.SignCached.pRegs := by decide
theorem mRegs_cs : ∀ r ∈ calleeSaved, r ∉ [Reg.r8, .rsi, .rdi] := by decide

theorem loads_ok {t : State} (hc : VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t) :
    WP isa (.block loads) t fun t' => (t'.mem = t.mem ∧ t'.mxcsr = t.mxcsr ∧
      t'.gpr .r8 = VG.Proof.Ed448.X86_64.SignCached.hw t L 0 ∧ t'.gpr .r9 = VG.Proof.Ed448.X86_64.SignCached.hw t L 1 ∧ t'.gpr .r10 = VG.Proof.Ed448.X86_64.SignCached.hw t L 2 ∧ t'.gpr .r11 = VG.Proof.Ed448.X86_64.SignCached.hw t L 3 ∧
      t'.gpr .rax = VG.Proof.Ed448.X86_64.SignCached.hw t L 4 ∧ t'.gpr .rcx = VG.Proof.Ed448.X86_64.SignCached.hw t L 5 ∧ t'.gpr .rsi = VG.Proof.Ed448.X86_64.SignCached.hw t L 6) ∧ Keep VG.Proof.Ed448.X86_64.SignCached.pRegs t t' := by
  have s0 := hc.inFr (d := 16) (by omega)
  have s1 := hc.inFr (d := 24) (by omega)
  have s2 := hc.inFr (d := 32) (by omega)
  have s3 := hc.inFr (d := 40) (by omega)
  have s4 := hc.inFr (d := 48) (by omega)
  have s5 := hc.inFr (d := 56) (by omega)
  have s6 := hc.inFr (d := 64) (by omega)
  refine WP.keep _ ?_ (by decide)
  xrun [loads, fH, ea_stk, hc.rsp, Nat.reduceAdd, s0, s1, s2, s3, s4, s5, s6, RegUpd.mxcsr_setReg]

theorem mods_ok (t : State) :
    WP isa (.block mods) t fun t' => (t'.mem = t.mem ∧ t'.mxcsr = t.mxcsr ∧
      t'.gpr .r8 = (t.gpr .r8 &&& BitVec.ofNat 64 (2 ^ 64 - 4)) ∧
      t'.gpr .rsi = (t.gpr .rsi ||| BitVec.ofNat 64 (2 ^ 63)) ∧ t'.gpr .rdi = 0) ∧
      Keep [.r8, .rsi, .rdi] t t' := by
  refine WP.keep _ ?_ (by decide)
  xrun [mods, RegUpd.mxcsr_setReg, RegUpd.mxcsr_setFlags]
  exact congrArg (_ &&& ·) (by decide : BitVec.signExtend 64 (BitVec.ofInt 32 (-4)) = BitVec.ofNat 64 (2 ^ 64 - 4))

/-- `s` lies in the data of the frame. -/
theorem w_s : VG.Proof.Ed448.X86_64.SignCached.WOk L ⟨L.S, 64⟩ :=
  .inr (.inr (.inr ⟨64, show L.SP + BitVec.ofNat 64 320 = L.SP + BitVec.ofNat 64 256 + BitVec.ofNat 64 64 from
    (add_add L.SP 256 64).symm, show 64 + 64 ≤ 192 by decide⟩))

theorem st_ok {t : State} (hc : VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t) {k : Nat} (hk : k < 8) (r : Reg) :
    WP isa (.block [Instr.store (stk (fS + 8 * k)) r]) t fun t' =>
      t'.mem = t.mem.writeW (L.SP + BitVec.ofNat 64 (320 + 8 * k)) (t.gpr r) ∧ t'.gpr = t.gpr ∧
        t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.mxcsr = t.mxcsr := by
  have w := hc.inFrW (d := 320 + 8 * k) (n := 8) (by omega)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store64, ea_stk, hc.rsp, fS, w,
    ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

/-- The first `n` stores of `stores`. -/
abbrev storesN (n : Nat) : List Instr := (List.range n).map fun k => .store (stk (fS + 8 * k)) (sRegs.getD k .r8)

theorem stores_ok (hL : L.Ok) : ∀ n ≤ 8, ∀ t : State, VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t →
    WP isa (.block (VG.Proof.Ed448.X86_64.SignCached.storesN n)) t fun t' => VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t' ∧ t'.gpr = t.gpr ∧
      VG.Frame [⟨L.S, 64⟩] t.mem t'.mem ∧
      ∀ j < n, t'.mem.readW (L.SP + BitVec.ofNat 64 (320 + 8 * j)) 64 = t.gpr (sRegs.getD j .r8)
  | 0, _, _, hc => WP.block_nil ⟨hc, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hn, t, hc => by
    rw [VG.Proof.Ed448.X86_64.SignCached.storesN, List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (VG.Proof.Ed448.X86_64.SignCached.stores_ok hL n (by omega) t hc) fun u ⟨hu, ug, uf, uw⟩ => ?_
    refine WP.mono (VG.Proof.Ed448.X86_64.SignCached.st_ok hu (k := n) (by omega) _) fun v ⟨vm, vg, vrd, vwr, vmx⟩ => ?_
    have hf1 : VG.Frame [⟨L.S, 64⟩] u.mem v.mem := by
      rw [vm]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by
        rw [Lay.S]; exact Offset.contains _ (by omega) (by omega) (by omega))
    have hc' : VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ v := hu.of_frame hL vrd vwr (fun r _ => by rw [vg]) (by rw [vmx])
      (hf1.mono fun r hr => List.mem_append_left _ hr) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.Ed448.X86_64.SignCached.w_s
    refine ⟨hc', by rw [vg, ug], uf.trans hf1, fun j hj => ?_⟩
    rw [vm]
    by_cases hjn : j = n
    · subst hjn; rw [Mem.readW_writeW_self64, ug]
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide), uw j (by omega)]

theorem prune_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t) :
    WP isa (.block prune) t fun t' => VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t' ∧ VG.Frame [⟨L.S, 64⟩] t.mem t'.mem ∧
      Spec.Ed448.decodeLE (Spec.Ed448.bytesAt t'.mem L.S 57) =
        Spec.Ed448.prune (Spec.Sha3.bytesAt t.mem L.H 114) := by
  rw [prune, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.SignCached.loads_ok hc) fun u ⟨⟨hmu, hxu, u8, u9, u10, u11, uax, ucx, usi⟩, ku⟩ => ?_
  have hu : VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ u := hc.regs ku.2.1 ku.2.2 hmu hxu fun r hr => ku.gpr (VG.Proof.Ed448.X86_64.SignCached.pRegs_cs r hr)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.SignCached.mods_ok u) fun v ⟨⟨hmv, hxv, v8, vsi, vdi⟩, kv⟩ => ?_
  have hv : VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ v := hu.regs kv.2.1 kv.2.2 hmv hxv fun r hr => kv.gpr (VG.Proof.Ed448.X86_64.SignCached.mRegs_cs r hr)
  have v9 : v.gpr .r9 = u.gpr .r9 := kv.gpr (by decide)
  have v10 : v.gpr .r10 = u.gpr .r10 := kv.gpr (by decide)
  have v11 : v.gpr .r11 = u.gpr .r11 := kv.gpr (by decide)
  have vax : v.gpr .rax = u.gpr .rax := kv.gpr (by decide)
  have vcx : v.gpr .rcx = u.gpr .rcx := kv.gpr (by decide)
  refine WP.mono (VG.Proof.Ed448.X86_64.SignCached.stores_ok hL 8 (by omega) v hv) fun w ⟨hw', _, hfw, ww⟩ => ⟨hw', by rw [← hmu, ← hmv]; exact hfw, ?_⟩
  have f0 : w.mem.readW (L.SP + BitVec.ofNat 64 320) 64 = v.gpr .r8 := ww 0 (by omega)
  have f1 : w.mem.readW (L.SP + BitVec.ofNat 64 328) 64 = v.gpr .r9 := ww 1 (by omega)
  have f2 : w.mem.readW (L.SP + BitVec.ofNat 64 336) 64 = v.gpr .r10 := ww 2 (by omega)
  have f3 : w.mem.readW (L.SP + BitVec.ofNat 64 344) 64 = v.gpr .r11 := ww 3 (by omega)
  have f4 : w.mem.readW (L.SP + BitVec.ofNat 64 352) 64 = v.gpr .rax := ww 4 (by omega)
  have f5 : w.mem.readW (L.SP + BitVec.ofNat 64 360) 64 = v.gpr .rcx := ww 5 (by omega)
  have f6 : w.mem.readW (L.SP + BitVec.ofNat 64 368) 64 = v.gpr .rsi := ww 6 (by omega)
  have f7 : w.mem.readW (L.SP + BitVec.ofNat 64 376) 64 = v.gpr .rdi := ww 7 (by omega)
  rw [VG.Proof.Ed448.X86_64.decode57]
  simp only [Lay.S, Lay.SP, add_add, Nat.reduceAdd] at f0 f1 f2 f3 f4 f5 f6 f7 ⊢
  rw [f0, f1, f2, f3, f4, f5, f6, byte_of_zero _ _ (f7.trans vdi), v8, v9, v10, v11, vax, vcx, vsi, u8, u9,
    u10, u11, uax, ucx, usi, Spec.Ed448.prune, take57, VG.Proof.Ed448.X86_64.decode57]
  simp only [VG.Proof.Ed448.X86_64.SignCached.hw, Lay.SP, add_add, Nat.reduceMul, Nat.reduceAdd]
  refine Eq.trans ?_ (prune_nat _ _ _ _ _ _ _ _ (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _)
    (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _)).symm
  have c₁ : (2 ^ 64 - 4) % 2 ^ 64 = 2 ^ 64 - 4 := by decide
  have c₂ : 2 ^ 63 % 2 ^ 64 = 2 ^ 63 := by decide
  rw [BitVec.toNat_and, BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat, c₁, c₂]

end

end VG.Proof.Ed448.X86_64.SignCached

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86_64.SignCached.Calls`. -/
section

/-!
# Ed448 signing with a cached public key on x86-64: the scalar calls

Between the frame's push and pop (`Ctx`): the calls of
`vg_ed448_scalar_reduce` into the frame (`red_ok`), of
`vg_ed448_scalar_base` from `r` into the first half of `out` (`base_ok`, for
any proof that it meets its contract, `BaseOk`: only the registration file
imports that proof, and the group theory it imports), and of
`vg_ed448_scalar_mul_add` into the second half (`mulAdd_ok`); and the
clearing of `s` and `r` (`wipe_ok`).
-/

namespace VG.Proof.Ed448.X86_64.SignCached

open VG VG.X86_64 VG.Impl.Ed448.X86_64.SignCached
open VG.Impl.Ed448.X86_64.Verify (stk Arg callA fH fScr)
open VG.Proof.Ed448.X86_64.Verify (Within within_off within_base within_self add_add ea_stk gpr_ce rsp_ce sp_sub8
  x0 setArgs_ok argRegs_cs argsIn3 argsIn5 reduce_nosp reduce_depth)
open VG.Proof.MlKem.X86_64 (Keep WP.keep)
open VG.Spec.Sha3 (bytesAt)

theorem base_nosp : NoSp Impl.Ed448.X86_64.scalarBase := by
  have : ((instrs Impl.Ed448.X86_64.scalarBase).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  intro i hi; simpa using List.all_eq_true.mp this i hi

theorem base_depth : Impl.Ed448.X86_64.scalarBase.depth ≤ 1 := by lit_decide

theorem mulAdd_nosp : NoSp Impl.Ed448.X86_64.scalarMulAdd := by
  have : ((instrs Impl.Ed448.X86_64.scalarMulAdd).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  intro i hi; simpa using List.all_eq_true.mp this i hi

theorem mulAdd_depth : Impl.Ed448.X86_64.scalarMulAdd.depth ≤ 1 := by lit_decide

/-- `vg_ed448_scalar_base` meets the contract its proof is written against, and the ABI. -/
abbrev BaseOk : Prop := ∀ s, Proof.Ed448.X86_64.scalarBaseLocal.pre s →
  ∃ t s', Exec isa Impl.Ed448.X86_64.scalarBase s t s' ∧ abiPreserved s s' ∧
    Proof.Ed448.X86_64.scalarBaseLocal.post s s'

/-- `vg_ed448_scalar_base` is constant time for that contract. -/
abbrev BaseCT : Prop := ConstantTime isa Proof.Ed448.X86_64.scalarBaseLocal.pre
  Proof.Ed448.X86_64.scalarBaseLocal.pub Impl.Ed448.X86_64.scalarBase

theorem ed_bytesAt : Spec.Ed448.bytesAt = bytesAt := rfl

section
variable {L : VG.Proof.Ed448.X86_64.SignCached.Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

theorem spd (L : VG.Proof.Ed448.X86_64.SignCached.Lay) (d : Nat) : L.SP + BitVec.ofNat 64 d = L.B + BitVec.ofNat 64 (16 + d) := add_add _ _ _

theorem sp_ce {t : State} (hc : VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t) (rd wr : List Region) :
    (t.callEntry.withRegions rd wr).gpr .rsp = L.B + BitVec.ofNat 64 8 := by
  rw [rsp_ce, hc.rsp, sp_sub8]

/-- A piece of the frame, apart from `scratch`. -/
theorem fr_x (hL : L.Ok) {d n : Nat} (h : d + n ≤ 448) :
    Region.Disjoint ⟨L.SP + BitVec.ofNat 64 d, n⟩ L.SCR := by
  have := hL.stk_x (d := 16 + d) (n := n) (e := 0) (k := 8192) (by omega) (by omega)
  rw [VG.Proof.Ed448.X86_64.SignCached.spd]; simpa only [x0] using this

/-- The return address of a call from the frame, apart from a piece of the frame. -/
theorem ret_fr {d n : Nat} (h : d + n ≤ 448) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 8, 8⟩ ⟨L.SP + BitVec.ofNat 64 d, n⟩ := by
  rw [VG.Proof.Ed448.X86_64.SignCached.spd]; exact Offset.disjoint _ (by omega) (by omega) (by omega)

theorem ret_x (hL : L.Ok) : Region.Disjoint ⟨L.B + BitVec.ofNat 64 8, 8⟩ L.SCR := by
  have := hL.stk_x (d := 8) (n := 8) (e := 0) (k := 8192) (by omega) (by omega)
  simpa only [x0] using this

theorem ret_r (hL : L.Ok) {r : Region} (hr : L.STK.Disjoint r) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 8, 8⟩ r :=
  hL.stk_r hr (by omega)

/-- The halves of `out`. -/
theorem o1_sub : Region.Sub ⟨L.out, 57⟩ L.OUT := (within_base _ (by omega)).sub
theorem o2_sub : Region.Sub ⟨L.out + BitVec.ofNat 64 57, 57⟩ L.OUT := (within_off _ (by omega)).sub

/-- A piece of the frame within its data. -/
theorem w_dat₂ {d n : Nat} (h₁ : 256 ≤ d) (h₂ : d + n ≤ 448) : VG.Proof.Ed448.X86_64.SignCached.WOk L ⟨L.SP + BitVec.ofNat 64 d, n⟩ :=
  .inr (.inr (.inr ⟨d - 256, show L.SP + BitVec.ofNat 64 d = L.SP + BitVec.ofNat 64 256 + BitVec.ofNat 64 (d - 256)
    by rw [add_add L.SP 256 (d - 256), Nat.add_sub_cancel' h₁], by show d - 256 + n ≤ 192; omega⟩))

theorem in_fr {d n : Nat} (h : d + n ≤ 448) :
    ∃ R ∈ L.rd ++ L.FR :: L.wr, Within ⟨L.SP + BitVec.ofNat 64 d, n⟩ R :=
  ⟨L.FR, by simp, within_off _ h⟩

/-! ## `vg_ed448_scalar_reduce` -/

theorem red_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t) {d : Nat} (h₁ : 256 ≤ d) (h₂ : d + 57 ≤ 448)
    (h₃ : d < 2 ^ 31) :
    WP isa (callA "vg_ed448_scalar_reduce" Impl.Ed448.X86_64.scalarReduce [.sp d, .sp fH, .slot fScr]) t
      fun t' => VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t' ∧ VG.Frame [⟨L.SP + BitVec.ofNat 64 d, 57⟩, L.SCR, ⟨L.B, 16⟩] t.mem t'.mem ∧
        Spec.Ed448.bytesAt t'.mem (L.SP + BitVec.ofNat 64 d) 57 =
          Spec.Ed448.scalarReduce (bytesAt t.mem L.H 114) := by
  refine WP.seq (WP.mono (setArgs_ok _ (by simp [Arg.ok, fScr, fH]; omega) t hc.frOk) fun t1 ⟨⟨hA, hm, hx⟩, k⟩ => ?_)
  have hc1 : VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t1 := hc.regs k.2.1 k.2.2 hm hx fun r hr => k.gpr (argRegs_cs r hr)
  obtain ⟨e1, e2, e3⟩ := argsIn3 hA
  rw [hc.sp] at e1 e2
  rw [hc.slot, hc.pScr] at e3
  change t1.gpr .rsi = L.H at e2
  have g1 := (gpr_ce t1 [⟨L.H, 114⟩] [⟨L.SP + BitVec.ofNat 64 d, 57⟩, L.SCR] (by decide : Reg.rdi ≠ .rsp)).trans e1
  have g2 := (gpr_ce t1 [⟨L.H, 114⟩] [⟨L.SP + BitVec.ofNat 64 d, 57⟩, L.SCR] (by decide : Reg.rsi ≠ .rsp)).trans e2
  have g3 := (gpr_ce t1 [⟨L.H, 114⟩] [⟨L.SP + BitVec.ofNat 64 d, 57⟩, L.SCR] (by decide : Reg.rdx ≠ .rsp)).trans e3
  have hpre : Proof.Ed448.X86_64.scalarReduceLocal.pre
      (t1.callEntry.withRegions [⟨L.H, 114⟩] [⟨L.SP + BitVec.ofNat 64 d, 57⟩, L.SCR]) := by
    simp only [Proof.Ed448.X86_64.scalarReduceLocal, g1, g2, g3, VG.Proof.Ed448.X86_64.SignCached.sp_ce hc1, State.withRegions_rd,
      State.withRegions_wr]
    exact ⟨trivial, trivial, VG.Proof.Ed448.X86_64.SignCached.fr_x hL (d := 16) (by omega), VG.Proof.Ed448.X86_64.SignCached.ret_fr h₂, VG.Proof.Ed448.X86_64.SignCached.ret_x hL, VG.Proof.Ed448.X86_64.SignCached.fr_x hL h₂, hL.nScr⟩
  refine VG.Proof.Ed448.X86_64.SignCached.call_ok hL Proof.Ed448.X86_64.scalarReduce_ok reduce_nosp reduce_depth hc1 hpre
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Proof.Ed448.X86_64.SignCached.in_fr (d := 16) (by omega))
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [VG.Proof.Ed448.X86_64.SignCached.w_dat₂ h₁ h₂, .inl (within_self _)])
    fun s' hc' hf _ ⟨s₂, hm₂, _, hpost⟩ => ⟨hc', by rw [← hm]; simpa using hf, ?_⟩
  simp only [Proof.Ed448.X86_64.scalarReduceLocal, g1, g2, State.withRegions_mem, hm₂] at hpost
  rw [hpost]
  refine congrArg _ ?_
  change bytesAt t1.callEntry.mem L.H 114 = bytesAt t.mem L.H 114
  rw [hc1.ce_bytesAt (VG.Proof.Ed448.X86_64.SignCached.ret_fr (d := 16) (by omega)) (by decide), hm]

/-! ## `vg_ed448_scalar_base` -/

theorem base_ok (hb : VG.Proof.Ed448.X86_64.SignCached.BaseOk) (hL : L.Ok) {t : State} (hc : VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t) :
    WP isa (callA "vg_ed448_scalar_base" Impl.Ed448.X86_64.scalarBase [.slot fOut, .sp fR, .slot fScr]) t
      fun t' => VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t' ∧ VG.Frame [⟨L.out, 57⟩, L.SCR, ⟨L.B, 16⟩] t.mem t'.mem ∧
        Spec.Ed448.bytesAt t'.mem L.out 57 = Spec.Ed448.scalarBase (Spec.Ed448.bytesAt t.mem L.R 57) := by
  refine WP.seq (WP.mono (setArgs_ok _ (by decide) t hc.frOk) fun t1 ⟨⟨hA, hm, hx⟩, k⟩ => ?_)
  have hc1 : VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t1 := hc.regs k.2.1 k.2.2 hm hx fun r hr => k.gpr (argRegs_cs r hr)
  obtain ⟨e1, e2, e3⟩ := argsIn3 hA
  rw [hc.slot, hc.pOut] at e1
  rw [hc.sp] at e2
  rw [hc.slot, hc.pScr] at e3
  change t1.gpr .rsi = L.R at e2
  have g1 := (gpr_ce t1 [⟨L.R, 57⟩] [⟨L.out, 57⟩, L.SCR] (by decide : Reg.rdi ≠ .rsp)).trans e1
  have g2 := (gpr_ce t1 [⟨L.R, 57⟩] [⟨L.out, 57⟩, L.SCR] (by decide : Reg.rsi ≠ .rsp)).trans e2
  have g3 := (gpr_ce t1 [⟨L.R, 57⟩] [⟨L.out, 57⟩, L.SCR] (by decide : Reg.rdx ≠ .rsp)).trans e3
  have hpre : Proof.Ed448.X86_64.scalarBaseLocal.pre (t1.callEntry.withRegions [⟨L.R, 57⟩] [⟨L.out, 57⟩, L.SCR]) := by
    simp only [Proof.Ed448.X86_64.scalarBaseLocal, g1, g2, g3, VG.Proof.Ed448.X86_64.SignCached.sp_ce hc1, State.withRegions_rd,
      State.withRegions_wr]
    exact ⟨trivial, trivial, VG.Proof.Ed448.X86_64.SignCached.fr_x hL (d := 384) (by omega), VG.Proof.Ed448.X86_64.SignCached.ret_r hL (hL.kOut.sub_right VG.Proof.Ed448.X86_64.SignCached.o1_sub), VG.Proof.Ed448.X86_64.SignCached.ret_x hL,
      (hL.xOut.sub_right VG.Proof.Ed448.X86_64.SignCached.o1_sub).symm, hL.nScr⟩
  refine VG.Proof.Ed448.X86_64.SignCached.call_ok hL hb VG.Proof.Ed448.X86_64.SignCached.base_nosp VG.Proof.Ed448.X86_64.SignCached.base_depth hc1 hpre
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Proof.Ed448.X86_64.SignCached.in_fr (d := 384) (by omega))
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [.inr (.inl (within_base _ (by omega))), .inl (within_self _)])
    fun s' hc' hf _ ⟨s₂, hm₂, _, hpost⟩ => ⟨hc', by rw [← hm]; simpa using hf, ?_⟩
  simp only [Proof.Ed448.X86_64.scalarBaseLocal, g1, g2, State.withRegions_mem, hm₂] at hpost
  rw [hpost]
  refine congrArg _ ?_
  rw [VG.Proof.Ed448.X86_64.SignCached.ed_bytesAt, hc1.ce_bytesAt (VG.Proof.Ed448.X86_64.SignCached.ret_fr (d := 384) (by omega)) (by decide), hm]

/-! ## `vg_ed448_scalar_mul_add` -/

theorem mulAdd_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t) :
    WP isa (callA "vg_ed448_scalar_mul_add" Impl.Ed448.X86_64.scalarMulAdd
        [.slotOff fOut 57, .sp fR, .sp fK, .sp fS, .slot fScr]) t
      fun t' => VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t' ∧
        VG.Frame [⟨L.out + BitVec.ofNat 64 57, 57⟩, L.SCR, ⟨L.B, 16⟩] t.mem t'.mem ∧
        Spec.Ed448.bytesAt t'.mem (L.out + BitVec.ofNat 64 57) 57 = Spec.Ed448.scalarMulAdd
          (Spec.Ed448.bytesAt t.mem L.R 57) (Spec.Ed448.bytesAt t.mem L.K 57) (Spec.Ed448.bytesAt t.mem L.S 57) := by
  refine WP.seq (WP.mono (setArgs_ok _ (by decide) t hc.frOk) fun t1 ⟨⟨hA, hm, hx⟩, k⟩ => ?_)
  have hc1 : VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t1 := hc.regs k.2.1 k.2.2 hm hx fun r hr => k.gpr (argRegs_cs r hr)
  obtain ⟨e1, e2, e3, e4, e5⟩ := argsIn5 hA
  simp only [Arg.val, hc.rsp, hc.pOut, hc.pScr] at e1 e5
  rw [hc.sp] at e2 e3 e4
  change t1.gpr .rsi = L.R at e2
  change t1.gpr .rdx = L.K at e3
  change t1.gpr .rcx = L.S at e4
  have g1 := (gpr_ce t1 [⟨L.R, 57⟩, ⟨L.K, 57⟩, ⟨L.S, 57⟩] [⟨L.out + BitVec.ofNat 64 57, 57⟩, L.SCR] (by decide : Reg.rdi ≠ .rsp)).trans e1
  have g2 := (gpr_ce t1 [⟨L.R, 57⟩, ⟨L.K, 57⟩, ⟨L.S, 57⟩] [⟨L.out + BitVec.ofNat 64 57, 57⟩, L.SCR] (by decide : Reg.rsi ≠ .rsp)).trans e2
  have g3 := (gpr_ce t1 [⟨L.R, 57⟩, ⟨L.K, 57⟩, ⟨L.S, 57⟩] [⟨L.out + BitVec.ofNat 64 57, 57⟩, L.SCR] (by decide : Reg.rdx ≠ .rsp)).trans e3
  have g4 := (gpr_ce t1 [⟨L.R, 57⟩, ⟨L.K, 57⟩, ⟨L.S, 57⟩] [⟨L.out + BitVec.ofNat 64 57, 57⟩, L.SCR] (by decide : Reg.rcx ≠ .rsp)).trans e4
  have g5 := (gpr_ce t1 [⟨L.R, 57⟩, ⟨L.K, 57⟩, ⟨L.S, 57⟩] [⟨L.out + BitVec.ofNat 64 57, 57⟩, L.SCR] (by decide : Reg.r8 ≠ .rsp)).trans e5
  have hpre : Proof.Ed448.X86_64.scalarMulAddLocal.pre
      (t1.callEntry.withRegions [⟨L.R, 57⟩, ⟨L.K, 57⟩, ⟨L.S, 57⟩] [⟨L.out + BitVec.ofNat 64 57, 57⟩, L.SCR]) := by
    simp only [Proof.Ed448.X86_64.scalarMulAddLocal, g1, g2, g3, g4, g5, VG.Proof.Ed448.X86_64.SignCached.sp_ce hc1, State.withRegions_rd,
      State.withRegions_wr]
    exact ⟨trivial, trivial, VG.Proof.Ed448.X86_64.SignCached.fr_x hL (d := 384) (by omega), VG.Proof.Ed448.X86_64.SignCached.fr_x hL (d := 256) (by omega),
      VG.Proof.Ed448.X86_64.SignCached.fr_x hL (d := 320) (by omega), VG.Proof.Ed448.X86_64.SignCached.ret_r hL (hL.kOut.sub_right VG.Proof.Ed448.X86_64.SignCached.o2_sub), VG.Proof.Ed448.X86_64.SignCached.ret_x hL,
      (hL.xOut.sub_right VG.Proof.Ed448.X86_64.SignCached.o2_sub).symm, hL.nScr⟩
  refine VG.Proof.Ed448.X86_64.SignCached.call_ok hL Proof.Ed448.X86_64.scalarMulAdd_ok VG.Proof.Ed448.X86_64.SignCached.mulAdd_nosp VG.Proof.Ed448.X86_64.SignCached.mulAdd_depth hc1 hpre
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [VG.Proof.Ed448.X86_64.SignCached.in_fr (d := 384) (by omega), VG.Proof.Ed448.X86_64.SignCached.in_fr (d := 256) (by omega), VG.Proof.Ed448.X86_64.SignCached.in_fr (d := 320) (by omega)])
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [.inr (.inl (within_off _ (by omega))), .inl (within_self _)])
    fun s' hc' hf _ ⟨s₂, hm₂, _, hpost⟩ => ⟨hc', by rw [← hm]; simpa using hf, ?_⟩
  simp only [Proof.Ed448.X86_64.scalarMulAddLocal, g1, g2, g3, g4, State.withRegions_mem, hm₂] at hpost
  rw [hpost, VG.Proof.Ed448.X86_64.SignCached.ed_bytesAt, hc1.ce_bytesAt (VG.Proof.Ed448.X86_64.SignCached.ret_fr (d := 384) (by omega)) (by decide),
    hc1.ce_bytesAt (VG.Proof.Ed448.X86_64.SignCached.ret_fr (d := 256) (by omega)) (by decide),
    hc1.ce_bytesAt (VG.Proof.Ed448.X86_64.SignCached.ret_fr (d := 320) (by omega)) (by decide), hm]

/-! ## Clearing `s` and `r` -/

/-- The first `n` stores of `wipe`. -/
abbrev wipesN (n : Nat) : List Instr := (List.range n).map fun k => .store (stk (fS + 8 * k)) .rax

theorem wipes_ok (hL : L.Ok) : ∀ n ≤ 16, ∀ t : State, VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t →
    WP isa (.block (VG.Proof.Ed448.X86_64.SignCached.wipesN n)) t fun t' => VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t' ∧ t'.gpr = t.gpr ∧
      VG.Frame [⟨L.S, 128⟩] t.mem t'.mem
  | 0, _, _, hc => WP.block_nil ⟨hc, rfl, Frame.refl _ _⟩
  | n + 1, hn, t, hc => by
    rw [VG.Proof.Ed448.X86_64.SignCached.wipesN, List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (VG.Proof.Ed448.X86_64.SignCached.wipes_ok hL n (by omega) t hc) fun u ⟨hu, ug, uf⟩ => ?_
    have w := hu.inFrW (d := 320 + 8 * n) (n := 8) (by omega)
    refine WP.mono (Q := fun v : State => v.mem = u.mem.writeW (L.SP + BitVec.ofNat 64 (320 + 8 * n)) (u.gpr .rax) ∧
      v.gpr = u.gpr ∧ v.rd = u.rd ∧ v.wr = u.wr ∧ v.mxcsr = u.mxcsr) ?_ fun v ⟨vm, vg, vrd, vwr, vmx⟩ => ?_
    · apply WP.of_runBlock
      simp only [List.map_cons, List.map_nil, runBlock_cons, runStep_some, runBlock_nil, exec, State.store64,
        ea_stk, hu.rsp, fS, w, ite_true, Option.some.injEq, exists_eq_left']
      exact ⟨trivial, trivial, trivial, trivial, trivial⟩
    have hf1 : VG.Frame [⟨L.S, 128⟩] u.mem v.mem := by
      rw [vm]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by
        rw [Lay.S]; exact Offset.contains _ (by omega) (by omega) (by omega))
    have ws : VG.Proof.Ed448.X86_64.SignCached.WOk L ⟨L.S, 128⟩ := VG.Proof.Ed448.X86_64.SignCached.w_dat₂ (d := 320) (by omega) (by omega)
    exact ⟨hu.of_frame hL vrd vwr (fun r _ => by rw [vg]) (by rw [vmx])
      (hf1.mono fun r hr => List.mem_append_left _ hr) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ws), by rw [vg, ug], uf.trans hf1⟩

theorem wipe_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t) :
    WP isa (.block wipe) t fun t' => VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t' ∧ VG.Frame [⟨L.S, 128⟩] t.mem t'.mem := by
  rw [wipe, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (WP.keep [.rax] (Q := fun s1 => s1.mem = t.mem ∧ s1.mxcsr = t.mxcsr)
    (by xrun [RegUpd.mxcsr_setReg]) (by decide)) fun t1 ⟨⟨hm1, hx1⟩, k1⟩ => ?_
  have hc1 : VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t1 := hc.regs k1.2.1 k1.2.2 hm1 hx1 fun r hr => k1.gpr (by
    simp only [List.mem_singleton]; exact Verify.ne_cs hr (by decide))
  exact WP.mono (VG.Proof.Ed448.X86_64.SignCached.wipes_ok hL 16 (by omega) t1 hc1) fun t2 ⟨hc2, _, hf⟩ => ⟨hc2, hm1 ▸ hf⟩

end

end VG.Proof.Ed448.X86_64.SignCached

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86_64.SignCached.Pre`. -/
section

/-!
# Ed448 signing with a cached public key on x86-64: the precondition and the layout

The precondition of `signCachedContract X86_64.abi 464`, spelled out
(`SPre`), and the layout of a run from a state satisfying it (`slay`, `Ok` by
`slay_ok`).
-/

namespace VG.Proof.Ed448.X86_64.SignCached

open VG VG.X86_64

section
variable (s : State)

abbrev sOut : Region := ⟨s.gpr .rdi, 114⟩
abbrev sSeed : Region := ⟨s.gpr .rsi, 57⟩
abbrev sPk : Region := ⟨s.gpr .rdx, 57⟩
abbrev sCtx : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
abbrev sMsg : Region := ⟨s.gpr .r9, (stackArg s 0).toNat⟩
abbrev sArgs : Region := ⟨stackArgAddr s 0, 16⟩
abbrev sScr : Region := ⟨stackArg s 1, 8192⟩
abbrev sRet : Region := ⟨s.gpr .rsp, 8⟩
abbrev sStk : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 464, 464⟩

end

/-- The precondition of `signCachedContract X86_64.abi 464`. -/
structure SPre (s : State) : Prop where
  sp : 464 ≤ (s.gpr .rsp).toNat
  sp2 : (s.gpr .rsp).toNat + 24 ≤ 2 ^ 64
  rd : s.rd = [VG.Proof.Ed448.X86_64.SignCached.sSeed s, VG.Proof.Ed448.X86_64.SignCached.sPk s, VG.Proof.Ed448.X86_64.SignCached.sCtx s, VG.Proof.Ed448.X86_64.SignCached.sMsg s, VG.Proof.Ed448.X86_64.SignCached.sArgs s]
  wr : s.wr = [VG.Proof.Ed448.X86_64.SignCached.sOut s, VG.Proof.Ed448.X86_64.SignCached.sScr s]
  outSeed : (VG.Proof.Ed448.X86_64.SignCached.sOut s).Disjoint (VG.Proof.Ed448.X86_64.SignCached.sSeed s)
  outPk : (VG.Proof.Ed448.X86_64.SignCached.sOut s).Disjoint (VG.Proof.Ed448.X86_64.SignCached.sPk s)
  outCtx : (VG.Proof.Ed448.X86_64.SignCached.sOut s).Disjoint (VG.Proof.Ed448.X86_64.SignCached.sCtx s)
  outMsg : (VG.Proof.Ed448.X86_64.SignCached.sOut s).Disjoint (VG.Proof.Ed448.X86_64.SignCached.sMsg s)
  outScr : (VG.Proof.Ed448.X86_64.SignCached.sOut s).Disjoint (VG.Proof.Ed448.X86_64.SignCached.sScr s)
  outArgs : (VG.Proof.Ed448.X86_64.SignCached.sOut s).Disjoint (VG.Proof.Ed448.X86_64.SignCached.sArgs s)
  seedScr : (VG.Proof.Ed448.X86_64.SignCached.sSeed s).Disjoint (VG.Proof.Ed448.X86_64.SignCached.sScr s)
  pkScr : (VG.Proof.Ed448.X86_64.SignCached.sPk s).Disjoint (VG.Proof.Ed448.X86_64.SignCached.sScr s)
  ctxScr : (VG.Proof.Ed448.X86_64.SignCached.sCtx s).Disjoint (VG.Proof.Ed448.X86_64.SignCached.sScr s)
  msgScr : (VG.Proof.Ed448.X86_64.SignCached.sMsg s).Disjoint (VG.Proof.Ed448.X86_64.SignCached.sScr s)
  scrArgs : (VG.Proof.Ed448.X86_64.SignCached.sScr s).Disjoint (VG.Proof.Ed448.X86_64.SignCached.sArgs s)
  retOut : (VG.Proof.Ed448.X86_64.SignCached.sRet s).Disjoint (VG.Proof.Ed448.X86_64.SignCached.sOut s)
  retSeed : (VG.Proof.Ed448.X86_64.SignCached.sRet s).Disjoint (VG.Proof.Ed448.X86_64.SignCached.sSeed s)
  retPk : (VG.Proof.Ed448.X86_64.SignCached.sRet s).Disjoint (VG.Proof.Ed448.X86_64.SignCached.sPk s)
  retCtx : (VG.Proof.Ed448.X86_64.SignCached.sRet s).Disjoint (VG.Proof.Ed448.X86_64.SignCached.sCtx s)
  retMsg : (VG.Proof.Ed448.X86_64.SignCached.sRet s).Disjoint (VG.Proof.Ed448.X86_64.SignCached.sMsg s)
  retScr : (VG.Proof.Ed448.X86_64.SignCached.sRet s).Disjoint (VG.Proof.Ed448.X86_64.SignCached.sScr s)
  retArgs : (VG.Proof.Ed448.X86_64.SignCached.sRet s).Disjoint (VG.Proof.Ed448.X86_64.SignCached.sArgs s)
  stkOut : (VG.Proof.Ed448.X86_64.SignCached.sStk s).Disjoint (VG.Proof.Ed448.X86_64.SignCached.sOut s)
  stkSeed : (VG.Proof.Ed448.X86_64.SignCached.sStk s).Disjoint (VG.Proof.Ed448.X86_64.SignCached.sSeed s)
  stkPk : (VG.Proof.Ed448.X86_64.SignCached.sStk s).Disjoint (VG.Proof.Ed448.X86_64.SignCached.sPk s)
  stkCtx : (VG.Proof.Ed448.X86_64.SignCached.sStk s).Disjoint (VG.Proof.Ed448.X86_64.SignCached.sCtx s)
  stkMsg : (VG.Proof.Ed448.X86_64.SignCached.sStk s).Disjoint (VG.Proof.Ed448.X86_64.SignCached.sMsg s)
  stkScr : (VG.Proof.Ed448.X86_64.SignCached.sStk s).Disjoint (VG.Proof.Ed448.X86_64.SignCached.sScr s)
  stkArgs : (VG.Proof.Ed448.X86_64.SignCached.sStk s).Disjoint (VG.Proof.Ed448.X86_64.SignCached.sArgs s)
  nOut : (s.gpr .rdi).toNat + 114 ≤ 2 ^ 64
  nSeed : (s.gpr .rsi).toNat + 57 ≤ 2 ^ 64
  nPk : (s.gpr .rdx).toNat + 57 ≤ 2 ^ 64
  nCtx : (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64
  nMsg : (s.gpr .r9).toNat + (stackArg s 0).toNat ≤ 2 ^ 64
  nScr : (stackArg s 1).toNat + 8192 ≤ 2 ^ 64
  pk : Spec.Ed448.bytesAt s.mem (s.gpr .rdx) 57 = Spec.Ed448.publicKey (Spec.Ed448.bytesAt s.mem (s.gpr .rsi) 57)
  ctxLe : (s.gpr .r8).toNat ≤ 255

theorem sPre_of {s : State} (h : (Spec.Ed448.signCachedContract X86_64.abi 464).pre s) : VG.Proof.Ed448.X86_64.SignCached.SPre s := by
  sig_pre [Spec.Ed448.signCachedContract, Spec.Ed448.signCachedSig, Spec.Ed448.scratchWords, X86_64.abi,
    X86_64.argRegs, List.range, List.range.loop] at h
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22,
    a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22,
    a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37⟩

/-- The layout of a run of `signCached` from `s`. -/
def slay (s : State) : VG.Proof.Ed448.X86_64.SignCached.Lay where
  B := s.gpr .rsp - BitVec.ofNat 64 464
  out := s.gpr .rdi
  seed := s.gpr .rsi
  pk := s.gpr .rdx
  ctx := s.gpr .rcx
  ctxLen := s.gpr .r8
  msg := s.gpr .r9
  len := stackArg s 0
  scr := stackArg s 1
  rd := s.rd
  wr := s.wr

theorem slay_B (s : State) : (VG.Proof.Ed448.X86_64.SignCached.slay s).B + BitVec.ofNat 64 464 = s.gpr .rsp := BitVec.sub_add_cancel _ _

theorem slay_ok {s : State} (h : VG.Proof.Ed448.X86_64.SignCached.SPre s) : (VG.Proof.Ed448.X86_64.SignCached.slay s).Ok := by
  have eR : (VG.Proof.Ed448.X86_64.SignCached.slay s).RET = VG.Proof.Ed448.X86_64.SignCached.sRet s := by
    show (⟨(VG.Proof.Ed448.X86_64.SignCached.slay s).B + BitVec.ofNat 64 464, 8⟩ : Region) = _
    rw [VG.Proof.Ed448.X86_64.SignCached.slay_B]
  refine ⟨by have := h.ctxLe; simp only [VG.Proof.Ed448.X86_64.SignCached.slay]; omega, ?_, h.wr, by simp [VG.Proof.Ed448.X86_64.SignCached.slay, h.rd], by simp [VG.Proof.Ed448.X86_64.SignCached.slay, h.rd],
    by simp [VG.Proof.Ed448.X86_64.SignCached.slay, h.rd], by simp [VG.Proof.Ed448.X86_64.SignCached.slay, h.rd], h.seedScr.symm, h.pkScr.symm, h.ctxScr.symm, h.msgScr.symm,
    h.outScr.symm, h.outSeed, h.outPk, h.outCtx, h.outMsg, h.stkScr, h.stkOut, h.stkSeed, h.stkPk, h.stkCtx,
    h.stkMsg, by rw [eR]; exact h.retScr, by rw [eR]; exact h.retOut, h.nOut, h.nSeed, h.nPk, h.nCtx, h.nMsg,
    h.nScr⟩
  have := h.sp; have := h.sp2
  simp only [VG.Proof.Ed448.X86_64.SignCached.slay, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

end VG.Proof.Ed448.X86_64.SignCached

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86_64.SignCached.Correct`. -/
section

/-!
# Ed448 signing with a cached public key on x86-64: correctness

The frame's body leaves `R ‖ S` in `out`, `Spec.Ed448.sign` of the private
key, the context and the message, given the public key of the private key
(`body_ok`): each piece is kept by the code that runs after it, which writes
elsewhere. The frame's push gives `Ctx` (`entry_ctx`). From a state
satisfying `signCachedContract X86_64.abi 464`, `signCached` meets the
contract and the ABI (`signCached_wp`), for any proof of
`vg_ed448_scalar_base` (`BaseOk`).
-/

namespace VG.Proof.Ed448.X86_64.SignCached

open VG VG.X86_64 VG.Impl.Ed448.X86_64.SignCached
open VG.Impl.Ed448.X86_64.Verify (stk)
open VG.Proof.Ed448.X86_64.Verify (add_add ea_stk x0 bytesAt_length bytesAt_congr)
open VG.Proof.MlKem.X86_64 (Keep WP.keep)
open VG.Spec.Sha3 (bytesAt)

section
variable {L : VG.Proof.Ed448.X86_64.SignCached.Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

/-- Bytes apart from every region of a frame are kept. -/
theorem keepB {rs : List Region} {m m' : Mem} (hf : VG.Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n :=
  bytesAt_congr fun _ hi => hf.bytes (R := ⟨p, n⟩) hd hn hi

/-- Two pieces of the frame. -/
theorem ff (L : VG.Proof.Ed448.X86_64.SignCached.Lay) {d n e k : Nat} (h : d + n ≤ e ∨ e + k ≤ d) (hd : d + n ≤ 448) (he : e + k ≤ 448) :
    Region.Disjoint ⟨L.SP + BitVec.ofNat 64 d, n⟩ ⟨L.SP + BitVec.ofNat 64 e, k⟩ :=
  Offset.disjoint _ h (by omega) (by omega)

/-- A piece of the frame and the 16 bytes below it. -/
theorem fb (L : VG.Proof.Ed448.X86_64.SignCached.Lay) {d n : Nat} (hd : d + n ≤ 448) :
    Region.Disjoint ⟨L.SP + BitVec.ofNat 64 d, n⟩ ⟨L.B, 16⟩ := by
  rw [VG.Proof.Ed448.X86_64.SignCached.spd]; exact Offset.disjoint_base _ (by omega) (by omega)

/-- A piece of the frame and one of `out`. -/
theorem fo (hL : L.Ok) {d n e k : Nat} (hd : d + n ≤ 448) (he : e + k ≤ 114) :
    Region.Disjoint ⟨L.SP + BitVec.ofNat 64 d, n⟩ ⟨L.out + BitVec.ofNat 64 e, k⟩ := by
  rw [VG.Proof.Ed448.X86_64.SignCached.spd]; exact (hL.stk_r hL.kOut (d := 16 + d) (n := n) (by omega)).sub_right (Offset.sub_base _ he)

/-- A piece of `out` and `scratch`; and the 16 bytes below the frame. -/
theorem ox (hL : L.Ok) {e k : Nat} (he : e + k ≤ 114) :
    Region.Disjoint ⟨L.out + BitVec.ofNat 64 e, k⟩ L.SCR :=
  (hL.o_r hL.xOut.symm he)

theorem ob (hL : L.Ok) {e k : Nat} (he : e + k ≤ 114) :
    Region.Disjoint ⟨L.out + BitVec.ofNat 64 e, k⟩ ⟨L.B, 16⟩ :=
  (VG.Proof.Ed448.X86_64.SignCached.k_r hL (hL.kOut.sub_right (Offset.sub_base _ he))).symm

theorem out0 (L : VG.Proof.Ed448.X86_64.SignCached.Lay) : L.out + BitVec.ofNat 64 0 = L.out := x0 _

/-- The header and the prefix after a hash into the frame. -/
theorem bytes_drop (m : Mem) (p : Addr) :
    (bytesAt m p 114).drop 57 = bytesAt m (p + BitVec.ofNat 64 57) 57 := by
  have a := Proof.X25519.bytesAt_add m p 57 57
  have l := Proof.X25519.length_bytesAt m p 57
  change (Spec.X25519.bytesAt m p (57 + 57)).drop 57 = Spec.X25519.bytesAt m (p + BitVec.ofNat 64 57) 57
  rw [a, List.drop_left' l]

theorem bytes_split (m : Mem) (p : Addr) :
    bytesAt m p 114 = bytesAt m p 57 ++ bytesAt m (p + BitVec.ofNat 64 57) 57 :=
  Proof.X25519.bytesAt_add m p 57 57

/-- The first ten bytes of `dom4(0, C)`, then `C`, are `dom4(0, C)`. -/
theorem hash_eq (L : VG.Proof.Ed448.X86_64.SignCached.Lay) (c X Y : List Byte) (hc : c.length = L.ctxLen.toNat) :
    Spec.Sha3.shake256 (VG.Proof.Ed448.X86_64.SignCached.hdrBytes L ++ c ++ X ++ Y) 114 = Spec.Ed448.hash c (X ++ Y) := by
  simp only [Spec.Ed448.hash, Spec.Ed448.dom4, VG.Proof.Ed448.X86_64.SignCached.hdrBytes, hc, List.append_assoc]

theorem hash_eq' (L : VG.Proof.Ed448.X86_64.SignCached.Lay) (c X P Y : List Byte) (hc : c.length = L.ctxLen.toNat) :
    Spec.Sha3.shake256 (VG.Proof.Ed448.X86_64.SignCached.hdrBytes L ++ c ++ X ++ P ++ Y) 114 = Spec.Ed448.hash c (X ++ P ++ Y) := by
  simp only [Spec.Ed448.hash, Spec.Ed448.dom4, VG.Proof.Ed448.X86_64.SignCached.hdrBytes, hc, List.append_assoc]

theorem body_ok (hb : VG.Proof.Ed448.X86_64.SignCached.BaseOk) (hL : L.Ok) {t : State} (hc : VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t)
    (hpk : Spec.Ed448.bytesAt m₀ L.pk 57 = Spec.Ed448.publicKey (Spec.Ed448.bytesAt m₀ L.seed 57)) :
    WP isa body t fun t' => VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t' ∧
      Spec.Ed448.bytesAt t'.mem L.out 114 = Spec.Ed448.sign (bytesAt m₀ L.seed 57)
        (bytesAt m₀ L.ctx L.ctxLen.toNat) (bytesAt m₀ L.msg L.len.toNat) := by
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86_64.SignCached.hdr_ok hL hc) fun t1 ⟨hc1, hh⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86_64.SignCached.seedHash_ok hL hc1) fun t2 ⟨hc2, f2, hS⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86_64.SignCached.prune_ok hL hc2) fun t3 ⟨hc3, f3, hs⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86_64.SignCached.nonceHash_ok hL hc3) fun t4 ⟨hc4, f4, hN⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86_64.SignCached.red_ok hL hc4 (d := 384) (by omega) (by omega) (by omega)) fun t5 ⟨hc5, f5, hR⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86_64.SignCached.base_ok hb hL hc5) fun t6 ⟨hc6, f6, hO⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86_64.SignCached.chalHash_ok hL hc6) fun t7 ⟨hc7, f7, hC⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86_64.SignCached.red_ok hL hc7 (d := 256) (by omega) (by omega) (by omega)) fun t8 ⟨hc8, f8, hK⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86_64.SignCached.mulAdd_ok hL hc8) fun t9 ⟨hc9, f9, hM⟩ => ?_)
  refine WP.mono (VG.Proof.Ed448.X86_64.SignCached.wipe_ok hL hc9) fun t10 ⟨hc10, f10⟩ => ⟨hc10, ?_⟩
  -- Facts about the regions.
  have xS : ∀ {d n : Nat}, d + n ≤ 448 → Region.Disjoint ⟨L.SP + BitVec.ofNat 64 d, n⟩ L.SCR :=
    fun h => VG.Proof.Ed448.X86_64.SignCached.fr_x hL h
  have rHW : ∀ {d n : Nat}, d + n ≤ 448 → (16 + 114 ≤ d) → ∀ r ∈ VG.Proof.Ed448.X86_64.SignCached.HW L,
      Region.Disjoint ⟨L.SP + BitVec.ofNat 64 d, n⟩ r := fun h h' r hr => by
    simp only [VG.Proof.Ed448.X86_64.SignCached.HW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [xS h, VG.Proof.Ed448.X86_64.SignCached.ff L (.inr h') h (by omega), VG.Proof.Ed448.X86_64.SignCached.fb L h]
  have oHW : ∀ {e k : Nat}, e + k ≤ 114 → ∀ r ∈ VG.Proof.Ed448.X86_64.SignCached.HW L, Region.Disjoint ⟨L.out + BitVec.ofNat 64 e, k⟩ r :=
    fun h r hr => by
      simp only [VG.Proof.Ed448.X86_64.SignCached.HW, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [VG.Proof.Ed448.X86_64.SignCached.ox hL h, (VG.Proof.Ed448.X86_64.SignCached.fo hL (d := 16) (n := 114) (by omega) h).symm, VG.Proof.Ed448.X86_64.SignCached.ob hL h]
  have three : ∀ {p : Addr} {n : Nat} {q : Region}, Region.Disjoint ⟨p, n⟩ q → Region.Disjoint ⟨p, n⟩ L.SCR →
      Region.Disjoint ⟨p, n⟩ ⟨L.B, 16⟩ → ∀ r ∈ [q, L.SCR, ⟨L.B, 16⟩], Region.Disjoint ⟨p, n⟩ r :=
    fun h₁ h₂ h₃ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [h₁, h₂, h₃]
  have one : ∀ {p : Addr} {n : Nat} {q : Region}, Region.Disjoint ⟨p, n⟩ q → ∀ r ∈ [q], Region.Disjoint ⟨p, n⟩ r :=
    fun h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h
  -- The header, through the hashes and the calls up to the challenge's hash.
  have hdr0 : ∀ r ∈ VG.Proof.Ed448.X86_64.SignCached.HW L, Region.Disjoint ⟨L.SP + BitVec.ofNat 64 0, 10⟩ r := fun r hr => by
    simp only [VG.Proof.Ed448.X86_64.SignCached.HW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [xS (by omega), VG.Proof.Ed448.X86_64.SignCached.ff L (.inl (by omega)) (by omega) (by omega), VG.Proof.Ed448.X86_64.SignCached.fb L (by omega)]
  rw [VG.Proof.Ed448.X86_64.SignCached.sp0] at hdr0
  have hx0 := xS (d := 0) (n := 10) (by omega); rw [VG.Proof.Ed448.X86_64.SignCached.sp0] at hx0
  have hb0 := VG.Proof.Ed448.X86_64.SignCached.fb L (d := 0) (n := 10) (by omega); rw [VG.Proof.Ed448.X86_64.SignCached.sp0] at hb0
  have e2 := VG.Proof.Ed448.X86_64.SignCached.keepB f2 hdr0 (by decide)
  have e3 := VG.Proof.Ed448.X86_64.SignCached.keepB f3 (one (q := ⟨L.S, 64⟩) (by
    have := VG.Proof.Ed448.X86_64.SignCached.ff L (d := 0) (n := 10) (e := 320) (k := 64) (.inl (by omega)) (by omega) (by omega)
    rwa [VG.Proof.Ed448.X86_64.SignCached.sp0] at this)) (by decide)
  have e4 := VG.Proof.Ed448.X86_64.SignCached.keepB f4 hdr0 (by decide)
  have e5 := VG.Proof.Ed448.X86_64.SignCached.keepB f5 (three (by
    have := VG.Proof.Ed448.X86_64.SignCached.ff L (d := 0) (n := 10) (e := 384) (k := 57) (.inl (by omega)) (by omega) (by omega)
    rwa [VG.Proof.Ed448.X86_64.SignCached.sp0] at this) hx0 hb0) (by decide)
  have e6 := VG.Proof.Ed448.X86_64.SignCached.keepB f6 (three (by
    have := VG.Proof.Ed448.X86_64.SignCached.fo hL (d := 0) (n := 10) (e := 0) (k := 57) (by omega) (by omega)
    rwa [VG.Proof.Ed448.X86_64.SignCached.sp0, VG.Proof.Ed448.X86_64.SignCached.out0] at this) hx0 hb0) (by decide)
  -- The prefix, through the pruning.
  have p3 := VG.Proof.Ed448.X86_64.SignCached.keepB f3 (one (q := ⟨L.S, 64⟩) (VG.Proof.Ed448.X86_64.SignCached.ff L (d := 73) (n := 57) (e := 320) (k := 64) (.inl (by omega))
    (by omega) (by omega))) (by decide)
  -- `R`, through the challenge's hash and its reduction, and the scalar product.
  have o1 : ∀ {e k : Nat}, e + k ≤ 114 → Region.Disjoint ⟨L.out + BitVec.ofNat 64 e, k⟩ L.SCR ∧
      Region.Disjoint ⟨L.out + BitVec.ofNat 64 e, k⟩ ⟨L.B, 16⟩ := fun h => ⟨VG.Proof.Ed448.X86_64.SignCached.ox hL h, VG.Proof.Ed448.X86_64.SignCached.ob hL h⟩
  have r7 := VG.Proof.Ed448.X86_64.SignCached.keepB f7 (p := L.out) (n := 57) (by have := oHW (e := 0) (k := 57) (by omega); rwa [VG.Proof.Ed448.X86_64.SignCached.out0] at this)
    (by decide)
  have r8 := VG.Proof.Ed448.X86_64.SignCached.keepB f8 (p := L.out) (n := 57) (three (by
      have := (VG.Proof.Ed448.X86_64.SignCached.fo hL (d := 256) (n := 57) (e := 0) (k := 57) (by omega) (by omega)).symm
      rwa [VG.Proof.Ed448.X86_64.SignCached.out0] at this) (by have := (o1 (e := 0) (k := 57) (by omega)).1; rwa [VG.Proof.Ed448.X86_64.SignCached.out0] at this)
      (by have := (o1 (e := 0) (k := 57) (by omega)).2; rwa [VG.Proof.Ed448.X86_64.SignCached.out0] at this)) (by decide)
  have r9 := VG.Proof.Ed448.X86_64.SignCached.keepB f9 (p := L.out) (n := 57) (three (by
      have := Offset.disjoint L.out (d := 0) (n := 57) (e := 57) (k := 57) (.inl (by omega)) (by omega) (by omega)
      rwa [VG.Proof.Ed448.X86_64.SignCached.out0] at this) (by have := (o1 (e := 0) (k := 57) (by omega)).1; rwa [VG.Proof.Ed448.X86_64.SignCached.out0] at this)
      (by have := (o1 (e := 0) (k := 57) (by omega)).2; rwa [VG.Proof.Ed448.X86_64.SignCached.out0] at this)) (by decide)
  have r10 := VG.Proof.Ed448.X86_64.SignCached.keepB f10 (p := L.out) (n := 57) (one (by
      have := (VG.Proof.Ed448.X86_64.SignCached.fo hL (d := 320) (n := 128) (e := 0) (k := 57) (by omega) (by omega)).symm
      rwa [VG.Proof.Ed448.X86_64.SignCached.out0] at this)) (by decide)
  have s10 := VG.Proof.Ed448.X86_64.SignCached.keepB f10 (p := L.out + BitVec.ofNat 64 57) (n := 57)
    (one (VG.Proof.Ed448.X86_64.SignCached.fo hL (d := 320) (n := 128) (e := 57) (k := 57) (by omega) (by omega)).symm) (by decide)
  -- `r` and `s`, through the code after them.
  have rr6 := VG.Proof.Ed448.X86_64.SignCached.keepB f6 (p := L.R) (n := 57) (three (VG.Proof.Ed448.X86_64.SignCached.fo hL (d := 384) (n := 57) (e := 0) (k := 57) (by omega)
    (by omega) |> fun h => by rwa [VG.Proof.Ed448.X86_64.SignCached.out0] at h) (xS (by omega)) (VG.Proof.Ed448.X86_64.SignCached.fb L (by omega))) (by decide)
  have rr7 := VG.Proof.Ed448.X86_64.SignCached.keepB f7 (p := L.R) (n := 57) (rHW (by omega) (by omega)) (by decide)
  have rr8 := VG.Proof.Ed448.X86_64.SignCached.keepB f8 (p := L.R) (n := 57) (three (VG.Proof.Ed448.X86_64.SignCached.ff L (.inr (by omega)) (by omega) (by omega)) (xS (by omega))
    (VG.Proof.Ed448.X86_64.SignCached.fb L (by omega))) (by decide)
  have ss4 := VG.Proof.Ed448.X86_64.SignCached.keepB f4 (p := L.S) (n := 57) (rHW (by omega) (by omega)) (by decide)
  have ss5 := VG.Proof.Ed448.X86_64.SignCached.keepB f5 (p := L.S) (n := 57) (three (VG.Proof.Ed448.X86_64.SignCached.ff L (.inl (by omega)) (by omega) (by omega)) (xS (by omega))
    (VG.Proof.Ed448.X86_64.SignCached.fb L (by omega))) (by decide)
  have ss6 := VG.Proof.Ed448.X86_64.SignCached.keepB f6 (p := L.S) (n := 57) (three (VG.Proof.Ed448.X86_64.SignCached.fo hL (d := 320) (n := 57) (e := 0) (k := 57) (by omega)
    (by omega) |> fun h => by rwa [VG.Proof.Ed448.X86_64.SignCached.out0] at h) (xS (by omega)) (VG.Proof.Ed448.X86_64.SignCached.fb L (by omega))) (by decide)
  have ss7 := VG.Proof.Ed448.X86_64.SignCached.keepB f7 (p := L.S) (n := 57) (rHW (by omega) (by omega)) (by decide)
  have ss8 := VG.Proof.Ed448.X86_64.SignCached.keepB f8 (p := L.S) (n := 57) (three (VG.Proof.Ed448.X86_64.SignCached.ff L (.inr (by omega)) (by omega) (by omega)) (xS (by omega))
    (VG.Proof.Ed448.X86_64.SignCached.fb L (by omega))) (by decide)
  -- The pieces.
  have pre : bytesAt t2.mem (L.SP + BitVec.ofNat 64 73) 57 = (bytesAt t2.mem L.H 114).drop 57 := by
    rw [VG.Proof.Ed448.X86_64.SignCached.bytes_drop, Lay.H, add_add L.SP 16 57]
  change Spec.Ed448.bytesAt t5.mem L.R 57 = _ at hR
  change Spec.Ed448.bytesAt t8.mem L.K 57 = _ at hK
  rw [VG.Proof.Ed448.X86_64.SignCached.ed_bytesAt] at hs hR hO hK hM hpk ⊢
  rw [VG.Proof.Ed448.X86_64.SignCached.bytes_split, r10, r9, r8, r7, s10, hM, rr8, rr7, rr6, hR, hK, hC, hN, ss8, ss7, ss6, ss5, ss4, e6, e5, e4,
    e3, p3, pre, e2, hh, hS, hO, hR, hN, e3, p3, pre, e2, hh, hS]
  rw [hS] at hs
  rw [VG.Proof.Ed448.X86_64.SignCached.hash_eq L _ _ _ (Verify.bytesAt_length _ _ _), VG.Proof.Ed448.X86_64.SignCached.hash_eq' L _ _ _ _ (Verify.bytesAt_length _ _ _)]
  exact Proof.Ed448.sign_pipeline _ _ _ _ _ hpk hs

end

/-! ## The frame -/

theorem push_slot (B : Addr) (j : Nat) (hj : j < 56) :
    B + BitVec.ofNat 64 464 - BitVec.ofNat 64 (8 * (j + 1)) =
      B + BitVec.ofNat 64 16 + BitVec.ofNat 64 (440 - 8 * j) := by
  rw [add_add, Offset.sub_ofNat_eq _ (a := 8 * (j + 1)) (b := 464) (by omega), BitVec.add_sub_cancel]
  congr 2; omega

theorem push_base (B : Addr) : B + BitVec.ofNat 64 464 - BitVec.ofNat 64 (8 * 56) = B + BitVec.ofNat 64 16 := by
  have := VG.Proof.Ed448.X86_64.SignCached.push_slot B 55 (by omega); simpa using this

theorem regs_length : regs.length = 56 := rfl

/-- After the push of the registers holding the arguments and 0: `Ctx`. -/
theorem entry_ctx {L : VG.Proof.Ed448.X86_64.SignCached.Lay} (hL : L.Ok) {s : State} (hsp : s.gpr .rsp = L.B + BitVec.ofNat 64 464)
    (hrd : s.rd = L.rd) (hwr : s.wr = L.wr) (h11 : s.gpr .r11 = L.scr) (hdi : s.gpr .rdi = L.out)
    (h10 : s.gpr .r10 = L.len) (h9 : s.gpr .r9 = L.msg) (h8 : s.gpr .r8 = L.ctxLen) (hcx : s.gpr .rcx = L.ctx)
    (hdx : s.gpr .rdx = L.pk) (hsi : s.gpr .rsi = L.seed) :
    VG.Proof.Ed448.X86_64.SignCached.Ctx L s.gpr s.mxcsr s.mem (pushed VG.Impl.Ed448.X86_64.SignCached.regs s) := by
  have hn : 8 * regs.length ≤ (s.gpr .rsp).toNat := by
    rw [hsp, VG.Proof.Ed448.X86_64.SignCached.regs_length, BitVec.toNat_add, BitVec.toNat_ofNat]
    have := hL.nB
    rw [Nat.mod_eq_of_lt (a := 464) (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  obtain ⟨hf, hw⟩ := pushRegs_mem s VG.Impl.Ed448.X86_64.SignCached.regs (by decide) hn
  have slot : ∀ j (hj : j < 56), (pushed VG.Impl.Ed448.X86_64.SignCached.regs s).mem.readW (L.SP + BitVec.ofNat 64 (440 - 8 * j)) 64 =
      s.gpr (VG.Impl.Ed448.X86_64.SignCached.regs[j]'(by rw [VG.Proof.Ed448.X86_64.SignCached.regs_length]; omega)) := fun j hj => by
    rw [← hw j (by rw [VG.Proof.Ed448.X86_64.SignCached.regs_length]; omega), hsp, VG.Proof.Ed448.X86_64.SignCached.push_slot _ j hj]; rfl
  have base : s.gpr .rsp - BitVec.ofNat 64 (8 * regs.length) = L.SP := by
    rw [hsp, VG.Proof.Ed448.X86_64.SignCached.regs_length]; exact VG.Proof.Ed448.X86_64.SignCached.push_base L.B
  refine ⟨by simp [hrd], by rw [pushed_wr, base, hwr]; rfl, by rw [pushed_rsp, base], fun r _ hr' => pushed_gpr _ _ hr',
    by simp, (slot 30 (by omega)).trans hdx, (slot 29 (by omega)).trans hcx, (slot 28 (by omega)).trans h8,
    (slot 27 (by omega)).trans h9, (slot 26 (by omega)).trans h10, (slot 25 (by omega)).trans hdi,
    (slot 24 (by omega)).trans h11, (slot 38 (by omega)).trans hsi, ?_⟩
  show VG.Frame [L.SCR, L.OUT, L.STK] s.mem (pushRegs s VG.Impl.Ed448.X86_64.SignCached.regs).mem
  refine Frame.sub hf fun r hr => ?_
  simp only [List.mem_singleton] at hr; subst hr
  refine ⟨L.STK, by simp, ?_⟩
  rw [base, VG.Proof.Ed448.X86_64.SignCached.regs_length]
  exact Offset.sub_base _ (by omega)

/-! ## Before the frame -/

theorem stackArgAddr0 (s : State) : stackArgAddr s 0 = s.gpr .rsp + BitVec.ofNat 64 8 := rfl

/-- `len` to `r10`, `scratch` to `r11`, 0 to `rax`. -/
theorem signMov_ok {s : State} (h : VG.Proof.Ed448.X86_64.SignCached.SPre s) :
    WP isa (.block [.mov .r10 (.mem (stk 8)), .mov .r11 (.mem (stk 16)), .mov32 .rax (.imm 0)]) s fun s2 =>
      (s2.gpr .r10 = stackArg s 0 ∧ s2.gpr .r11 = stackArg s 1 ∧ s2.mem = s.mem ∧ s2.mxcsr = s.mxcsr) ∧
        Keep [.r10, .r11, .rax] s s2 := by
  have hin : ∀ d, d + 8 ≤ 16 → InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 (8 + d)) 8 := by
    intro d hd
    refine ⟨VG.Proof.Ed448.X86_64.SignCached.sArgs s, by simp [h.rd], ?_⟩
    rw [← add_add, ← VG.Proof.Ed448.X86_64.SignCached.stackArgAddr0]
    exact Offset.contains_base _ hd (by omega)
  refine WP.keep _ ?_ (by decide)
  have h8 := hin 0 (by omega)
  have h16 := hin 8 (by omega)
  simp only [Nat.reduceAdd] at h8 h16
  xrun [ea_stk, h8, h16, RegUpd.mxcsr_setReg]
  exact ⟨rfl, rfl⟩

theorem cs_r11 : ∀ r ∈ calleeSaved, r ≠ .r11 := by decide
theorem cs_tmp : ∀ r ∈ calleeSaved, r ∉ [Reg.r10, .r11, .rax] := by decide

/-! ## The function -/

theorem signCached_wp (hb : VG.Proof.Ed448.X86_64.SignCached.BaseOk) {s : State} (hpre : (Spec.Ed448.signCachedContract X86_64.abi 464).pre s) :
    WP isa signCached s fun s' =>
      abiPreserved s s' ∧ (Spec.Ed448.signCachedContract X86_64.abi 464).post s s' := by
  have h := VG.Proof.Ed448.X86_64.SignCached.sPre_of hpre
  have hL := VG.Proof.Ed448.X86_64.SignCached.slay_ok h
  unfold signCached
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86_64.SignCached.signMov_ok h) fun s2 ⟨⟨h10, h11, hm2, hx2⟩, k2⟩ => ?_)
  have hg2 : ∀ r, r ∉ [Reg.r10, .r11, .rax] → s2.gpr r = s.gpr r := fun r hr => k2.gpr hr
  have hsp2 : s2.gpr .rsp = (VG.Proof.Ed448.X86_64.SignCached.slay s).B + BitVec.ofNat 64 464 := by rw [hg2 _ (by decide), VG.Proof.Ed448.X86_64.SignCached.slay_B]
  have hn : 8 * regs.length ≤ (s2.gpr .rsp).toNat := by
    rw [hg2 _ (by decide), VG.Proof.Ed448.X86_64.SignCached.regs_length]; have := h.sp; omega
  refine WP.frame (by decide) (by decide) (by decide) hn ?_
  have hc := VG.Proof.Ed448.X86_64.SignCached.entry_ctx hL hsp2 k2.2.1 k2.2.2 h11 (hg2 _ (by decide)) h10 (hg2 _ (by decide)) (hg2 _ (by decide))
    (hg2 _ (by decide)) (hg2 _ (by decide)) (hg2 _ (by decide))
  have hpk : Spec.Ed448.bytesAt s2.mem (VG.Proof.Ed448.X86_64.SignCached.slay s).pk 57 =
      Spec.Ed448.publicKey (Spec.Ed448.bytesAt s2.mem (VG.Proof.Ed448.X86_64.SignCached.slay s).seed 57) := by
    rw [hm2]; exact h.pk
  refine WP.mono (VG.Proof.Ed448.X86_64.SignCached.body_ok hb hL hc hpk) fun s' ⟨hc', hr⟩ => ⟨by rw [hc'.rsp, hc.rsp], by rw [hc'.wr, hc.wr], ?_, ?_⟩
  · -- The calling convention.
    refine ⟨fun r hr => ?_, ?_, ?_⟩
    · by_cases hr' : r = .rsp
      · subst hr'
        rw [popped_rsp, hc'.rsp, Lay.SP, add_add, VG.Proof.Ed448.X86_64.SignCached.regs_length, VG.Proof.Ed448.X86_64.SignCached.slay_B]
      · rw [popped_gpr _ _ _ hr' (VG.Proof.Ed448.X86_64.SignCached.cs_r11 r hr), hc'.cs r hr hr', hg2 r (VG.Proof.Ed448.X86_64.SignCached.cs_tmp r hr)]
    · have eR : VG.Proof.Ed448.X86_64.SignCached.sRet s = ⟨(VG.Proof.Ed448.X86_64.SignCached.slay s).B + BitVec.ofNat 64 464, 8⟩ := by rw [VG.Proof.Ed448.X86_64.SignCached.slay_B]
      rw [popped_mem, hc'.frame.readW (r := VG.Proof.Ed448.X86_64.SignCached.sRet s) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact h.retScr
          · exact h.retOut
          · rw [eR]; exact Offset.disjoint_base _ (by omega) (by have := hL.nB; omega)) (by decide), hm2]
    · rw [popped_mxcsr, hc'.mx, hx2]
  · sig_post [Spec.Ed448.signCachedContract, Spec.Ed448.signCachedSig, Spec.Ed448.scratchWords, X86_64.abi,
      X86_64.argRegs, List.range, List.range.loop]
    rw [hm2] at hr
    exact hr

end VG.Proof.Ed448.X86_64.SignCached

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86_64.SignCached.CT`. -/
section

/-!
# Ed448 signing with a cached public key on x86-64: constant time

Two runs from states that satisfy the contract and agree on its public data,
the pointers and the lengths, leak the same, whatever the private key, the
public key, the context and the message: the moves, the frame, the pruning
and the clearing address only the stack; the hashes leak only the layout
(`seedHash_tr`, `nonceHash_tr`, `chalHash_tr`); and the calls of
`vg_ed448_scalar_reduce`, `vg_ed448_scalar_base` and
`vg_ed448_scalar_mul_add` leak only their pointers (`red_tr`, `base_tr`,
`mulAdd_tr`).
-/

namespace VG.Proof.Ed448.X86_64.SignCached

open VG VG.X86_64 VG.Impl.Ed448.X86_64.SignCached
open VG.Impl.Ed448.X86_64.Verify (stk Arg callA hdr fH fScr)
open VG.Proof.Ed448.X86_64.Verify (Moved SpOnly spOnly_nomem block_rsp_tr ghost_step Ghost argsIn3 argsIn5 gpr_ce
  rsp_ce hdr_spOnly)
open VG.Proof.MlKem.X86_64 (Keep)

section
variable {I : VG.Proof.Ed448.X86_64.SignCached.Lay → Mem → Mem → Prop}

/-! ## The calls -/

theorem red_tr {Φ : VG.Proof.Ed448.X86_64.SignCached.Lay → Mem → State → Prop} {d : Nat} (h₂ : d + 57 ≤ 448) (h₃ : d < 2 ^ 31) :
    RelCT isa (VG.Proof.Ed448.X86_64.SignCached.Two I Φ) (callA "vg_ed448_scalar_reduce" Impl.Ed448.X86_64.scalarReduce [.sp d, .sp fH, .slot fScr])
      fun _ _ => True := by
  have regs : ∀ (L : VG.Proof.Ed448.X86_64.SignCached.Lay) g mx m₀ (t t1 : State), VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t → Moved [.sp d, .sp fH, .slot fScr] t t1 →
      t1.gpr .rdi = L.SP + BitVec.ofNat 64 d ∧ t1.gpr .rsi = L.H ∧ t1.gpr .rdx = L.scr ∧ t1.gpr .rsp = L.SP :=
    fun L g mx m₀ t t1 hc hm => by
      obtain ⟨e1, e2, e3⟩ := argsIn3 hm.1.1
      rw [hc.sp] at e1 e2
      rw [hc.slot, hc.pScr] at e3
      exact ⟨e1, e2, e3, (hm.2.gpr (by decide)).trans hc.rsp⟩
  refine VG.Proof.Ed448.X86_64.SignCached.call_tr (by simp [Arg.ok, fScr, fH]; omega) Proof.Ed448.X86_64.scalarReduce_ok
    Proof.Ed448.X86_64.scalarReduce_ct
    (fun L => [⟨L.H, 114⟩]) (fun L => [⟨L.SP + BitVec.ofNat 64 d, 57⟩, L.SCR])
    (fun L g mx m₀ t t1 hL hc _ hm => ?_)
    (fun L g₁ g₂ mx₁ mx₂ m₁ m₂ a b a1 b1 _ _ c₁ c₂ _ _ f₁ f₂ => ?_) fun L _ _ _ _ hL _ _ => ?_
  · obtain ⟨g1, g2, g3, g4⟩ := regs L g mx m₀ t t1 hc hm
    simp only [Proof.Ed448.X86_64.scalarReduceLocal, gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp),
      gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp), rsp_ce, g1, g2, g3, g4,
      Verify.sp_sub8, State.withRegions_rd, State.withRegions_wr]
    exact ⟨trivial, trivial, VG.Proof.Ed448.X86_64.SignCached.fr_x hL (d := 16) (by omega), VG.Proof.Ed448.X86_64.SignCached.ret_fr h₂, VG.Proof.Ed448.X86_64.SignCached.ret_x hL, VG.Proof.Ed448.X86_64.SignCached.fr_x hL h₂, hL.nScr⟩
  · obtain ⟨x1, x2, x3, x4⟩ := regs L g₁ mx₁ m₁ a a1 c₁ f₁
    obtain ⟨y1, y2, y3, y4⟩ := regs L g₂ mx₂ m₂ b b1 c₂ f₂
    simp only [Proof.Ed448.X86_64.scalarReduceLocal, gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp),
      gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp), rsp_ce,
      x1, x2, x3, x4, y1, y2, y3, y4, and_self]
  · refine ⟨fun r hr => ?_, fun r hr => ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact VG.Proof.Ed448.X86_64.SignCached.in_fr (d := 16) (by omega)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [⟨L.FR, by simp, Verify.within_off _ h₂⟩, ⟨L.SCR, by simp [hL.wr], Verify.within_self _⟩]

theorem base_tr (hb : VG.Proof.Ed448.X86_64.SignCached.BaseOk) (hct : VG.Proof.Ed448.X86_64.SignCached.BaseCT) {Φ : VG.Proof.Ed448.X86_64.SignCached.Lay → Mem → State → Prop} :
    RelCT isa (VG.Proof.Ed448.X86_64.SignCached.Two I Φ) (callA "vg_ed448_scalar_base" Impl.Ed448.X86_64.scalarBase [.slot fOut, .sp fR, .slot fScr])
      fun _ _ => True := by
  have regs : ∀ (L : VG.Proof.Ed448.X86_64.SignCached.Lay) g mx m₀ (t t1 : State), VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t → Moved [.slot fOut, .sp fR, .slot fScr] t t1 →
      t1.gpr .rdi = L.out ∧ t1.gpr .rsi = L.R ∧ t1.gpr .rdx = L.scr ∧ t1.gpr .rsp = L.SP :=
    fun L g mx m₀ t t1 hc hm => by
      obtain ⟨e1, e2, e3⟩ := argsIn3 hm.1.1
      rw [hc.slot, hc.pOut] at e1
      rw [hc.sp] at e2
      rw [hc.slot, hc.pScr] at e3
      exact ⟨e1, e2, e3, (hm.2.gpr (by decide)).trans hc.rsp⟩
  refine VG.Proof.Ed448.X86_64.SignCached.call_tr (by decide) hb hct (fun L => [⟨L.R, 57⟩]) (fun L => [⟨L.out, 57⟩, L.SCR])
    (fun L g mx m₀ t t1 hL hc _ hm => ?_)
    (fun L g₁ g₂ mx₁ mx₂ m₁ m₂ a b a1 b1 _ _ c₁ c₂ _ _ f₁ f₂ => ?_) fun L _ _ _ _ hL _ _ => ?_
  · obtain ⟨g1, g2, g3, g4⟩ := regs L g mx m₀ t t1 hc hm
    simp only [Proof.Ed448.X86_64.scalarBaseLocal, gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp),
      gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp), rsp_ce, g1, g2, g3, g4,
      Verify.sp_sub8, State.withRegions_rd, State.withRegions_wr]
    exact ⟨trivial, trivial, VG.Proof.Ed448.X86_64.SignCached.fr_x hL (d := 384) (by omega), VG.Proof.Ed448.X86_64.SignCached.ret_r hL (hL.kOut.sub_right VG.Proof.Ed448.X86_64.SignCached.o1_sub), VG.Proof.Ed448.X86_64.SignCached.ret_x hL,
      (hL.xOut.sub_right VG.Proof.Ed448.X86_64.SignCached.o1_sub).symm, hL.nScr⟩
  · obtain ⟨x1, x2, x3, x4⟩ := regs L g₁ mx₁ m₁ a a1 c₁ f₁
    obtain ⟨y1, y2, y3, y4⟩ := regs L g₂ mx₂ m₂ b b1 c₂ f₂
    simp only [Proof.Ed448.X86_64.scalarBaseLocal, gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp),
      gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp), rsp_ce,
      x1, x2, x3, x4, y1, y2, y3, y4, and_self]
  · refine ⟨fun r hr => ?_, fun r hr => ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact VG.Proof.Ed448.X86_64.SignCached.in_fr (d := 384) (by omega)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [⟨L.OUT, by simp [hL.wr], Verify.within_base _ (by omega)⟩,
        ⟨L.SCR, by simp [hL.wr], Verify.within_self _⟩]

theorem mulAdd_tr {Φ : VG.Proof.Ed448.X86_64.SignCached.Lay → Mem → State → Prop} :
    RelCT isa (VG.Proof.Ed448.X86_64.SignCached.Two I Φ) (callA "vg_ed448_scalar_mul_add" Impl.Ed448.X86_64.scalarMulAdd
      [.slotOff fOut 57, .sp fR, .sp fK, .sp fS, .slot fScr]) fun _ _ => True := by
  have regs : ∀ (L : VG.Proof.Ed448.X86_64.SignCached.Lay) g mx m₀ (t t1 : State), VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t →
      Moved [.slotOff fOut 57, .sp fR, .sp fK, .sp fS, .slot fScr] t t1 →
      t1.gpr .rdi = L.out + BitVec.ofNat 64 57 ∧ t1.gpr .rsi = L.R ∧ t1.gpr .rdx = L.K ∧ t1.gpr .rcx = L.S ∧
        t1.gpr .r8 = L.scr ∧ t1.gpr .rsp = L.SP :=
    fun L g mx m₀ t t1 hc hm => by
      obtain ⟨e1, e2, e3, e4, e5⟩ := argsIn5 hm.1.1
      simp only [Arg.val, hc.rsp, hc.pOut, hc.pScr] at e1 e5
      rw [hc.sp] at e2 e3 e4
      exact ⟨e1, e2, e3, e4, e5, (hm.2.gpr (by decide)).trans hc.rsp⟩
  refine VG.Proof.Ed448.X86_64.SignCached.call_tr (by decide) Proof.Ed448.X86_64.scalarMulAdd_ok Proof.Ed448.X86_64.scalarMulAdd_ct
    (fun L => [⟨L.R, 57⟩, ⟨L.K, 57⟩, ⟨L.S, 57⟩]) (fun L => [⟨L.out + BitVec.ofNat 64 57, 57⟩, L.SCR])
    (fun L g mx m₀ t t1 hL hc _ hm => ?_)
    (fun L g₁ g₂ mx₁ mx₂ m₁ m₂ a b a1 b1 _ _ c₁ c₂ _ _ f₁ f₂ => ?_) fun L _ _ _ _ hL _ _ => ?_
  · obtain ⟨g1, g2, g3, g4, g5, g6⟩ := regs L g mx m₀ t t1 hc hm
    simp only [Proof.Ed448.X86_64.scalarMulAddLocal, gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp),
      gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp),
      gpr_ce _ _ _ (by decide : Reg.rcx ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.r8 ≠ .rsp), rsp_ce,
      g1, g2, g3, g4, g5, g6, Verify.sp_sub8, State.withRegions_rd, State.withRegions_wr]
    exact ⟨trivial, trivial, VG.Proof.Ed448.X86_64.SignCached.fr_x hL (d := 384) (by omega), VG.Proof.Ed448.X86_64.SignCached.fr_x hL (d := 256) (by omega),
      VG.Proof.Ed448.X86_64.SignCached.fr_x hL (d := 320) (by omega), VG.Proof.Ed448.X86_64.SignCached.ret_r hL (hL.kOut.sub_right VG.Proof.Ed448.X86_64.SignCached.o2_sub), VG.Proof.Ed448.X86_64.SignCached.ret_x hL,
      (hL.xOut.sub_right VG.Proof.Ed448.X86_64.SignCached.o2_sub).symm, hL.nScr⟩
  · obtain ⟨x1, x2, x3, x4, x5, x6⟩ := regs L g₁ mx₁ m₁ a a1 c₁ f₁
    obtain ⟨y1, y2, y3, y4, y5, y6⟩ := regs L g₂ mx₂ m₂ b b1 c₂ f₂
    simp only [Proof.Ed448.X86_64.scalarMulAddLocal, gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp),
      gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp),
      gpr_ce _ _ _ (by decide : Reg.rcx ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.r8 ≠ .rsp), rsp_ce,
      x1, x2, x3, x4, x5, x6, y1, y2, y3, y4, y5, y6, and_self]
  · refine ⟨fun r hr => ?_, fun r hr => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [VG.Proof.Ed448.X86_64.SignCached.in_fr (d := 384) (by omega), VG.Proof.Ed448.X86_64.SignCached.in_fr (d := 256) (by omega), VG.Proof.Ed448.X86_64.SignCached.in_fr (d := 320) (by omega)]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [⟨L.OUT, by simp [hL.wr], Verify.within_off _ (by omega)⟩,
        ⟨L.SCR, by simp [hL.wr], Verify.within_self _⟩]

/-! ## The blocks -/

theorem stk_spOnly {d : Nat} (r : Reg) : SpOnly (.store (stk d) r) :=
  ⟨fun s₁ s₂ h => by simp [addrs, State.ea, stk, h], rfl⟩

theorem prune_spOnly : ∀ i ∈ prune, SpOnly i := by
  intro i hi
  simp only [prune, loads, mods, stores, sRegs, List.range, List.range.loop, List.map_cons, List.map_nil,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl) |
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals first
    | exact VG.Proof.Ed448.X86_64.SignCached.stk_spOnly _
    | exact spOnly_nomem (fun _ => rfl) rfl
    | exact ⟨fun s₁ s₂ h => by simp [addrs, srcAddrs, State.ea, stk, h], rfl⟩

theorem wipe_spOnly : ∀ i ∈ wipe, SpOnly i := by
  intro i hi
  simp only [wipe, List.mem_cons, List.mem_map, List.mem_range] at hi
  rcases hi with rfl | ⟨k, -, rfl⟩
  · exact spOnly_nomem (fun _ => rfl) rfl
  · exact VG.Proof.Ed448.X86_64.SignCached.stk_spOnly _

/-! ## The frame's body -/

abbrev T (I : VG.Proof.Ed448.X86_64.SignCached.Lay → Mem → Mem → Prop) : State → State → Prop := VG.Proof.Ed448.X86_64.SignCached.Two I fun _ _ _ => True

theorem blk_two {is : List Instr} (h : ∀ i ∈ is, SpOnly i)
    (hw : ∀ (L : VG.Proof.Ed448.X86_64.SignCached.Lay) g mx m₀ (t : State), L.Ok → VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t → WP isa (.block is) t (VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀)) :
    RelCT isa (VG.Proof.Ed448.X86_64.SignCached.T I) (.block is) (VG.Proof.Ed448.X86_64.SignCached.T I) :=
  VG.Proof.Ed448.X86_64.SignCached.two_wp (block_rsp_tr h fun _ _ h => h.rsp) fun L g mx m₀ t hL hc _ =>
    WP.mono (hw L g mx m₀ t hL hc) fun _ h => ⟨h, trivial⟩

theorem two_true {c : Prog isa} (hct : RelCT isa (VG.Proof.Ed448.X86_64.SignCached.T I) c fun _ _ => True)
    (hw : ∀ (L : VG.Proof.Ed448.X86_64.SignCached.Lay) g mx m₀ (t : State), L.Ok → VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀ t → WP isa c t (VG.Proof.Ed448.X86_64.SignCached.Ctx L g mx m₀)) :
    RelCT isa (VG.Proof.Ed448.X86_64.SignCached.T I) c (VG.Proof.Ed448.X86_64.SignCached.T I) :=
  VG.Proof.Ed448.X86_64.SignCached.two_wp hct fun L g mx m₀ t hL hc _ => WP.mono (hw L g mx m₀ t hL hc) fun _ h => ⟨h, trivial⟩

/-- The frame's body, after the header. -/
theorem rest_tr (hb : VG.Proof.Ed448.X86_64.SignCached.BaseOk) (hct : VG.Proof.Ed448.X86_64.SignCached.BaseCT) :
    RelCT isa (VG.Proof.Ed448.X86_64.SignCached.T I) (.seq seedHash <| .seq (.block prune) <| .seq nonceHash <|
      .seq (callA "vg_ed448_scalar_reduce" Impl.Ed448.X86_64.scalarReduce [.sp fR, .sp fH, .slot fScr]) <|
      .seq (callA "vg_ed448_scalar_base" Impl.Ed448.X86_64.scalarBase [.slot fOut, .sp fR, .slot fScr]) <|
      .seq chalHash <|
      .seq (callA "vg_ed448_scalar_reduce" Impl.Ed448.X86_64.scalarReduce [.sp fK, .sp fH, .slot fScr]) <|
      .seq (callA "vg_ed448_scalar_mul_add" Impl.Ed448.X86_64.scalarMulAdd
        [.slotOff fOut 57, .sp fR, .sp fK, .sp fS, .slot fScr]) (.block wipe)) fun _ _ => True := by
  have a := VG.Proof.Ed448.X86_64.SignCached.two_true (I := I) VG.Proof.Ed448.X86_64.SignCached.seedHash_tr fun _ _ _ _ _ hL hc => WP.mono (VG.Proof.Ed448.X86_64.SignCached.seedHash_ok hL hc) fun _ h => h.1
  have b := VG.Proof.Ed448.X86_64.SignCached.blk_two (I := I) VG.Proof.Ed448.X86_64.SignCached.prune_spOnly fun _ _ _ _ _ hL hc => WP.mono (VG.Proof.Ed448.X86_64.SignCached.prune_ok hL hc) fun _ h => h.1
  have c := VG.Proof.Ed448.X86_64.SignCached.two_true (I := I) VG.Proof.Ed448.X86_64.SignCached.nonceHash_tr fun _ _ _ _ _ hL hc => WP.mono (VG.Proof.Ed448.X86_64.SignCached.nonceHash_ok hL hc) fun _ h => h.1
  have d := VG.Proof.Ed448.X86_64.SignCached.two_true (I := I) (VG.Proof.Ed448.X86_64.SignCached.red_tr (d := 384) (by omega) (by omega))
    fun _ _ _ _ _ hL hc => WP.mono (VG.Proof.Ed448.X86_64.SignCached.red_ok hL hc (d := 384) (by omega) (by omega) (by omega)) fun _ h => h.1
  have e := VG.Proof.Ed448.X86_64.SignCached.two_true (I := I) (VG.Proof.Ed448.X86_64.SignCached.base_tr hb hct) fun _ _ _ _ _ hL hc => WP.mono (VG.Proof.Ed448.X86_64.SignCached.base_ok hb hL hc) fun _ h => h.1
  have f := VG.Proof.Ed448.X86_64.SignCached.two_true (I := I) VG.Proof.Ed448.X86_64.SignCached.chalHash_tr fun _ _ _ _ _ hL hc => WP.mono (VG.Proof.Ed448.X86_64.SignCached.chalHash_ok hL hc) fun _ h => h.1
  have g := VG.Proof.Ed448.X86_64.SignCached.two_true (I := I) (VG.Proof.Ed448.X86_64.SignCached.red_tr (d := 256) (by omega) (by omega))
    fun _ _ _ _ _ hL hc => WP.mono (VG.Proof.Ed448.X86_64.SignCached.red_ok hL hc (d := 256) (by omega) (by omega) (by omega)) fun _ h => h.1
  have h := VG.Proof.Ed448.X86_64.SignCached.two_true (I := I) VG.Proof.Ed448.X86_64.SignCached.mulAdd_tr fun _ _ _ _ _ hL hc => WP.mono (VG.Proof.Ed448.X86_64.SignCached.mulAdd_ok hL hc) fun _ h => h.1
  exact a.seq (b.seq (c.seq (d.seq (e.seq (f.seq (g.seq (h.seq (block_rsp_tr VG.Proof.Ed448.X86_64.SignCached.wipe_spOnly fun _ _ h => h.rsp))))))))

end

/-! ## The function -/

/-- The public data of the contract, spelled out. -/
structure SPub (s₁ s₂ : State) : Prop where
  rsp : s₁.gpr .rsp = s₂.gpr .rsp
  rdi : s₁.gpr .rdi = s₂.gpr .rdi
  rsi : s₁.gpr .rsi = s₂.gpr .rsi
  rdx : s₁.gpr .rdx = s₂.gpr .rdx
  rcx : s₁.gpr .rcx = s₂.gpr .rcx
  r8 : s₁.gpr .r8 = s₂.gpr .r8
  r9 : s₁.gpr .r9 = s₂.gpr .r9
  a0 : stackArg s₁ 0 = stackArg s₂ 0
  a1 : stackArg s₁ 1 = stackArg s₂ 1

theorem sPub_of {s₁ s₂ : State} (h : (Spec.Ed448.signCachedContract X86_64.abi 464).pub s₁ s₂) : VG.Proof.Ed448.X86_64.SignCached.SPub s₁ s₂ := by
  sig_pub [Spec.Ed448.signCachedContract, Spec.Ed448.signCachedSig, Spec.Ed448.scratchWords, X86_64.abi,
    X86_64.argRegs, List.range, List.range.loop] at h
  obtain ⟨a, b, c, d, e, f, g, h, i⟩ := h
  exact ⟨a, b, c, d, e, f, g, h, i⟩

/-- Two runs from states agreeing on the public data have the same layout. -/
theorem slay_eq {s₁ s₂ : State} (h₁ : VG.Proof.Ed448.X86_64.SignCached.SPre s₁) (h₂ : VG.Proof.Ed448.X86_64.SignCached.SPre s₂) (h : VG.Proof.Ed448.X86_64.SignCached.SPub s₁ s₂) : VG.Proof.Ed448.X86_64.SignCached.slay s₁ = VG.Proof.Ed448.X86_64.SignCached.slay s₂ := by
  have e1 : s₁.rd = s₂.rd := by
    rw [h₁.rd, h₂.rd]; simp only [VG.Proof.Ed448.X86_64.SignCached.sSeed, VG.Proof.Ed448.X86_64.SignCached.sPk, VG.Proof.Ed448.X86_64.SignCached.sCtx, VG.Proof.Ed448.X86_64.SignCached.sMsg, VG.Proof.Ed448.X86_64.SignCached.sArgs, stackArgAddr, h.rsi, h.rdx, h.rcx, h.r8, h.r9,
      h.a0, h.rsp]
  have e2 : s₁.wr = s₂.wr := by
    rw [h₁.wr, h₂.wr]; simp only [VG.Proof.Ed448.X86_64.SignCached.sOut, VG.Proof.Ed448.X86_64.SignCached.sScr, h.rdi, h.a1]
  simp only [VG.Proof.Ed448.X86_64.SignCached.slay, h.rsp, h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, h.a0, h.a1, e1, e2]

/-- The entry states of two runs: the precondition and the public data. -/
abbrev SP2 (x y : State) : Prop :=
  (Spec.Ed448.signCachedContract X86_64.abi 464).pre x ∧ (Spec.Ed448.signCachedContract X86_64.abi 464).pre y ∧
    (Spec.Ed448.signCachedContract X86_64.abi 464).pub x y

/-- After the moves before the push. -/
abbrev SMov (x x2 : State) : Prop :=
  (x2.gpr .r10 = stackArg x 0 ∧ x2.gpr .r11 = stackArg x 1 ∧ x2.mem = x.mem ∧ x2.mxcsr = x.mxcsr) ∧
    Keep [.r10, .r11, .rax] x x2

theorem signCached_ct (hb : VG.Proof.Ed448.X86_64.SignCached.BaseOk) (hct : VG.Proof.Ed448.X86_64.SignCached.BaseCT) :
    ConstantTime isa (Spec.Ed448.signCachedContract X86_64.abi 464).pre
      (Spec.Ed448.signCachedContract X86_64.abi 464).pub signCached := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  have e0 : (fun s₁ s₂ => (Spec.Ed448.signCachedContract X86_64.abi 464).pre s₁ ∧
      (Spec.Ed448.signCachedContract X86_64.abi 464).pre s₂ ∧
      (Spec.Ed448.signCachedContract X86_64.abi 464).pub s₁ s₂) = Ghost VG.Proof.Ed448.X86_64.SignCached.SP2 (fun x a => a = x) := by
    funext a b; apply propext
    exact ⟨fun h => ⟨a, b, h, rfl, rfl⟩, fun ⟨_, _, h, e₁, e₂⟩ => e₁ ▸ e₂ ▸ h⟩
  rw [e0]
  unfold signCached
  have hmov := ghost_step (P := VG.Proof.Ed448.X86_64.SignCached.SP2) (A := fun x a => a = x) (B := VG.Proof.Ed448.X86_64.SignCached.SMov)
    (c := .block [.mov .r10 (.mem (stk 8)), .mov .r11 (.mem (stk 16)), .mov32 .rax (.imm 0)])
    (block_rsp_tr (fun i hi => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl
        · exact ⟨fun s₁ s₂ h => by simp [addrs, srcAddrs, State.ea, stk, h], rfl⟩
        · exact ⟨fun s₁ s₂ h => by simp [addrs, srcAddrs, State.ea, stk, h], rfl⟩
        · exact spOnly_nomem (fun _ => rfl) rfl)
      fun a b ⟨x, y, hxy, e₁, e₂⟩ => by subst e₁ e₂; exact (VG.Proof.Ed448.X86_64.SignCached.sPub_of hxy.2.2).rsp)
    fun x y a b hxy e₁ e₂ => by
      subst e₁ e₂
      exact ⟨VG.Proof.Ed448.X86_64.SignCached.signMov_ok (VG.Proof.Ed448.X86_64.SignCached.sPre_of hxy.1), VG.Proof.Ed448.X86_64.SignCached.signMov_ok (VG.Proof.Ed448.X86_64.SignCached.sPre_of hxy.2.1)⟩
  refine RelCT.seq hmov ?_
  refine RelCT.frame (R := fun _ _ => True) (fun a b ⟨x, y, hxy, f₁, f₂⟩ => by
    rw [f₁.2.gpr (by decide), f₂.2.gpr (by decide)]; exact (VG.Proof.Ed448.X86_64.SignCached.sPub_of hxy.2.2).rsp) ?_
  -- The frame's body, from the push.
  let A : State → State → Prop := fun x a => ∃ s₁, VG.Proof.Ed448.X86_64.SignCached.SMov x s₁ ∧ a = pushed VG.Impl.Ed448.X86_64.SignCached.regs s₁
  let B : State → State → Prop := fun x t => VG.Proof.Ed448.X86_64.SignCached.Ctx (VG.Proof.Ed448.X86_64.SignCached.slay x) x.gpr x.mxcsr x.mem t
  have hh := ghost_step (P := VG.Proof.Ed448.X86_64.SignCached.SP2) (A := A) (B := B) (c := .block hdr)
    (block_rsp_tr hdr_spOnly
      fun a b ⟨x, y, hxy, ⟨s₁, f₁, e₁⟩, ⟨s₂, f₂, e₂⟩⟩ => by
        subst e₁ e₂
        rw [pushed_rsp, pushed_rsp, f₁.2.gpr (by decide), f₂.2.gpr (by decide), (VG.Proof.Ed448.X86_64.SignCached.sPub_of hxy.2.2).rsp])
    fun x y a b hxy fa fb => by
      have en : ∀ {x a : State}, (Spec.Ed448.signCachedContract X86_64.abi 464).pre x → A x a →
          WP isa (.block hdr) a (B x) := fun hx ⟨s₁, f, e⟩ => by
        subst e
        have h := VG.Proof.Ed448.X86_64.SignCached.sPre_of hx
        have hL := VG.Proof.Ed448.X86_64.SignCached.slay_ok h
        have hc := VG.Proof.Ed448.X86_64.SignCached.entry_ctx hL (by rw [f.2.gpr (by decide), VG.Proof.Ed448.X86_64.SignCached.slay_B]) f.2.2.1 f.2.2.2 f.1.2.1
          (f.2.gpr (by decide)) f.1.1 (f.2.gpr (by decide)) (f.2.gpr (by decide)) (f.2.gpr (by decide))
          (f.2.gpr (by decide)) (f.2.gpr (by decide))
        exact WP.mono (VG.Proof.Ed448.X86_64.SignCached.hdr_ok hL hc) fun t ⟨hc', _⟩ =>
          hc'.congr (fun r hr _ => f.2.gpr (VG.Proof.Ed448.X86_64.SignCached.cs_tmp r hr)) f.1.2.2.2 f.1.2.2.1
      exact ⟨en hxy.1 fa, en hxy.2.1 fb⟩
  refine RelCT.seq (RelCT.mono hh (fun a b ⟨s₁, s₂, ⟨x, y, hxy, f₁, f₂⟩, e₁, e₂⟩ =>
    ⟨x, y, hxy, ⟨s₁, f₁, e₁⟩, ⟨s₂, f₂, e₂⟩⟩) fun a b ⟨x, y, hxy, ca, cb⟩ => ?_)
    (VG.Proof.Ed448.X86_64.SignCached.rest_tr (I := fun _ _ _ => True) hb hct)
  have hx := VG.Proof.Ed448.X86_64.SignCached.sPre_of hxy.1
  have e := VG.Proof.Ed448.X86_64.SignCached.slay_eq hx (VG.Proof.Ed448.X86_64.SignCached.sPre_of hxy.2.1) (VG.Proof.Ed448.X86_64.SignCached.sPub_of hxy.2.2)
  exact ⟨VG.Proof.Ed448.X86_64.SignCached.slay x, x.gpr, y.gpr, x.mxcsr, y.mxcsr, x.mem, y.mem, VG.Proof.Ed448.X86_64.SignCached.slay_ok hx, trivial, ca, e ▸ cb, trivial, trivial⟩

end VG.Proof.Ed448.X86_64.SignCached

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86_64.SignCached.Verified`. -/
section

/-!
# Ed448 signing with a cached public key on x86-64: `Verified`

`signCached` is verified against `signCachedContract X86_64.abi 464`:
correctness including the ABI (`signCached_wp`), constant time
(`signCached_ct`), and a state satisfying the precondition, with a public key
matching the private key, for any proof of `vg_ed448_scalar_base` (`BaseOk`,
`BaseCT`): the registration file passes its own, so that only it imports that
proof and the group theory it imports.
-/

namespace VG.Proof.Ed448.X86_64.SignCached

open VG VG.X86_64 VG.Impl.Ed448.X86_64.SignCached

/-! ## A state satisfying the precondition -/

def satSeed : List Byte := Spec.Ed448.bytesAt (fun _ => 0) 0x2000 57
def satKey : List Byte := Spec.Ed448.publicKey VG.Proof.Ed448.X86_64.SignCached.satSeed

theorem satKey_length : satKey.length = 57 := by
  simp only [VG.Proof.Ed448.X86_64.SignCached.satKey, Spec.Ed448.publicKey, Spec.Ed448.encodePoint, Spec.Ed448.encodeLE, List.length_map,
    List.length_range]

/-- The public key at `0x3000`, `scratch`'s address `0x10000` as the second
argument on the stack, and 0 elsewhere. -/
def satMem (a : Addr) : Byte :=
  if a = 0x80012 then 1 else if a.toNat < 0x3000 ∨ 0x3039 ≤ a.toNat then 0 else VG.Proof.Ed448.X86_64.SignCached.satKey[a.toNat - 0x3000]?.getD 0

theorem sat_seed : Spec.Ed448.bytesAt VG.Proof.Ed448.X86_64.SignCached.satMem 0x2000 57 = VG.Proof.Ed448.X86_64.SignCached.satSeed := by
  unfold VG.Proof.Ed448.X86_64.SignCached.satSeed Spec.Ed448.bytesAt
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  have ha : ((0x2000 : Addr) + BitVec.ofNat 64 i).toNat = 0x2000 + i := by
    change (0x2000 + i % 2 ^ 64) % 2 ^ 64 = 0x2000 + i
    omega
  have hne : (0x2000 : Addr) + BitVec.ofNat 64 i ≠ 0x80012 := fun h => by
    have := congrArg BitVec.toNat h; rw [ha] at this; simp at this; omega
  simp only [VG.Proof.Ed448.X86_64.SignCached.satMem, hne, ↓reduceIte, ha, show 0x2000 + i < 0x3000 from by omega, true_or]

theorem sat_key : Spec.Ed448.bytesAt VG.Proof.Ed448.X86_64.SignCached.satMem 0x3000 57 = VG.Proof.Ed448.X86_64.SignCached.satKey := by
  apply List.ext_getElem
  · simp only [Spec.Ed448.bytesAt, List.length_map, List.length_range, VG.Proof.Ed448.X86_64.SignCached.satKey_length]
  · intro i hi hj
    have hi' : i < 57 := by simpa only [Spec.Ed448.bytesAt, List.length_map, List.length_range] using hi
    have ha : ((0x3000 : Addr) + BitVec.ofNat 64 i).toNat = 0x3000 + i := by
      change (0x3000 + i % 2 ^ 64) % 2 ^ 64 = 0x3000 + i
      omega
    have hne : (0x3000 : Addr) + BitVec.ofNat 64 i ≠ 0x80012 := fun h => by
      have := congrArg BitVec.toNat h; rw [ha] at this; simp at this; omega
    simp only [Spec.Ed448.bytesAt, List.getElem_map, List.getElem_range, VG.Proof.Ed448.X86_64.SignCached.satMem, hne, ↓reduceIte, ha,
      show ¬ (0x3000 + i < 0x3000 ∨ 0x3039 ≤ 0x3000 + i) from by omega, Nat.add_sub_cancel_left,
      List.getElem?_eq_getElem hj, Option.getD_some]

def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x4000
    | .r8 => 0 | .r9 => 0x5000 | .rsp => 0x80000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := VG.Proof.Ed448.X86_64.SignCached.satMem
  rd := [⟨0x2000, 57⟩, ⟨0x3000, 57⟩, ⟨0x4000, 0⟩, ⟨0x5000, 0⟩, ⟨0x80008, 16⟩]
  wr := [⟨0x1000, 114⟩, ⟨0x10000, 8192⟩]

theorem sat : ∃ s, (Spec.Ed448.signCachedContract X86_64.abi 464).pre s := by
  refine ⟨VG.Proof.Ed448.X86_64.SignCached.satState, ?_⟩
  sig_apply_check
  · decide +kernel
  · sig_reduce [Spec.Ed448.signCachedContract, Spec.Ed448.signCachedSig,
      Spec.Ed448.scratchWords, X86_64.abi, X86_64.argRegs, VG.Proof.Ed448.X86_64.SignCached.satState]
    sig_and_intros
    · decide
    · decide
    · rw [VG.Proof.Ed448.X86_64.SignCached.sat_seed, VG.Proof.Ed448.X86_64.SignCached.sat_key]
      rfl
    · decide

/-! ## `Verified` -/

theorem signCached_verified (hb : VG.Proof.Ed448.X86_64.SignCached.BaseOk) (hct : VG.Proof.Ed448.X86_64.SignCached.BaseCT) :
    Verified X86_64.target signCached (Spec.Ed448.signCachedContract X86_64.abi 464) :=
  ⟨fun _ h => let ⟨t, s', he, ha, hq⟩ := VG.Proof.Ed448.X86_64.SignCached.signCached_wp hb h; ⟨t, s', he, ha, hq⟩, VG.Proof.Ed448.X86_64.SignCached.signCached_ct hb hct, VG.Proof.Ed448.X86_64.SignCached.sat⟩

end VG.Proof.Ed448.X86_64.SignCached

end
