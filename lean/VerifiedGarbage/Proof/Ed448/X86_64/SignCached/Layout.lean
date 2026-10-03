import VerifiedGarbage.Impl.Ed448.X86_64.SignCached
import VerifiedGarbage.Proof.Ed448.X86_64.Verify.Args

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

variable (L : Lay)

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

variable {L : Lay}

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
structure Ctx (L : Lay) (g : Reg → BitVec 64) (mx : BitVec 32) (m₀ : Mem) (t : State) : Prop where
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
  pOut : t.mem.readW (L.SP + BitVec.ofNat 64 fOut) 64 = L.out
  pScr : t.mem.readW (L.SP + BitVec.ofNat 64 fScr) 64 = L.scr
  pSeed : t.mem.readW (L.SP + BitVec.ofNat 64 fSeed) 64 = L.seed
  frame : Frame [L.SCR, L.OUT, L.STK] m₀ t.mem

namespace Ctx

variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem} {t t' : State}

/-- Code that writes only caller-saved registers. -/
theorem regs (hc : Ctx L g mx m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hm : t'.mem = t.mem)
    (hmx : t'.mxcsr = t.mxcsr) (hg : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) : Ctx L g mx m₀ t' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, (hg .rsp (by decide)).trans hc.rsp,
    fun r hr hr' => (hg r hr).trans (hc.cs r hr hr'), by rw [hmx]; exact hc.mx,
    by rw [hm]; exact hc.pPk, by rw [hm]; exact hc.pCtx, by rw [hm]; exact hc.pCtxLen,
    by rw [hm]; exact hc.pMsg, by rw [hm]; exact hc.pLen, by rw [hm]; exact hc.pOut,
    by rw [hm]; exact hc.pScr, by rw [hm]; exact hc.pSeed, by rw [hm]; exact hc.frame⟩

/-- The same state, with the entry registers, MXCSR and memory given by others equal to them. -/
theorem congr (hc : Ctx L g mx m₀ t) {g' : Reg → BitVec 64} {mx' : BitVec 32} {m₀' : Mem}
    (hg : ∀ r ∈ calleeSaved, r ≠ .rsp → g r = g' r) (hmx : mx = mx') (hm : m₀ = m₀') : Ctx L g' mx' m₀' t := by
  subst hmx hm
  exact ⟨hc.rd, hc.wr, hc.rsp, fun r hr hr' => (hc.cs r hr hr').trans (hg r hr hr'), hc.mx, hc.pPk, hc.pCtx,
    hc.pCtxLen, hc.pMsg, hc.pLen, hc.pOut, hc.pScr, hc.pSeed, hc.frame⟩

/-- A word of the frame is readable. -/
theorem inFr (hc : Ctx L g mx m₀ t) {d : Nat} (h₂ : d + 8 ≤ 448) :
    InRegions (t.rd ++ t.wr) (L.SP + BitVec.ofNat 64 d) 8 :=
  ⟨L.FR, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ h₂ (by omega)⟩

theorem inFrW (hc : Ctx L g mx m₀ t) {d n : Nat} (h₂ : d + n ≤ 448) :
    InRegions t.wr (L.SP + BitVec.ofNat 64 d) n :=
  ⟨L.FR, by rw [hc.wr]; simp, Offset.contains_base _ h₂ (by omega)⟩

/-- The return address of a call from the frame. -/
theorem ret (hc : Ctx L g mx m₀ t) : below (t.gpr .rsp) 8 = ⟨L.B + BitVec.ofNat 64 8, 8⟩ := by
  rw [hc.rsp]
  show (⟨L.B + BitVec.ofNat 64 16 - BitVec.ofNat 64 8, 8⟩ : Region) = _
  rw [sp_sub8']

/-- A byte of a region apart from `scratch`, `out` and the stack, as on entry. -/
theorem byte (hc : Ctx L g mx m₀ t) {R : Region} (hx : L.SCR.Disjoint R) (ho : L.OUT.Disjoint R)
    (hk : L.STK.Disjoint R) (hR : R.len ≤ 2 ^ 64) {i : Nat} (hi : i < R.len) :
    t.mem (R.base + BitVec.ofNat 64 i) = m₀ (R.base + BitVec.ofNat 64 i) :=
  Frame.bytes (R := R) hc.frame (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hx.symm
    · exact ho.symm
    · exact hk.symm) hR hi

theorem bytesAt_eq (hc : Ctx L g mx m₀ t) {p : Addr} {n : Nat} (hx : L.SCR.Disjoint ⟨p, n⟩)
    (ho : L.OUT.Disjoint ⟨p, n⟩) (hk : L.STK.Disjoint ⟨p, n⟩) (hn : n ≤ 2 ^ 64) :
    bytesAt t.mem p n = bytesAt m₀ p n :=
  bytesAt_congr fun _ hi => hc.byte (R := ⟨p, n⟩) hx ho hk hn hi

theorem ce_bytesAt (hc : Ctx L g mx m₀ t) {p : Addr} {n : Nat}
    (hd : Region.Disjoint ⟨L.B + BitVec.ofNat 64 8, 8⟩ ⟨p, n⟩) (hn : n ≤ 2 ^ 64) :
    bytesAt t.callEntry.mem p n = bytesAt t.mem p n :=
  bytesAt_congr fun _ hi => Verify.Ctx.ce_byte t (R := ⟨p, n⟩) (by rw [hc.ret]; exact hd) hn hi

end Ctx

/-- Where the code may write: `scratch`, `out`, and the data of the frame. -/
def WOk (L : Lay) (r : Region) : Prop := Within r L.SCR ∨ Within r L.OUT ∨ Within r L.DAT₁ ∨ Within r L.DAT₂

/-- The slots of the frame's arguments are apart from where the code writes
and from the stack below the frame. -/
theorem slot_disj {L : Lay} (hL : L.Ok) {d : Nat} (h₁ : 136 ≤ d) (h₂ : d + 8 ≤ 256) {r : Region}
    (hr : WOk L r ∨ r = ⟨L.B, 16⟩) : Region.Disjoint ⟨L.SP + BitVec.ofNat 64 d, 8⟩ r := by
  rw [Lay.SP, add_add]
  rcases hr with (hr | hr | hr | hr) | rfl
  · exact (hL.stk_r hL.kScr (d := 16 + d) (n := 8) (by omega)).sub_right hr.sub
  · exact (hL.stk_r hL.kOut (d := 16 + d) (n := 8) (by omega)).sub_right hr.sub
  · have := Offset.disjoint L.B (d := 16 + d) (n := 8) (e := 16) (k := 136) (by omega) (by omega) (by omega)
    exact this.sub_right (by simpa [Lay.DAT₁, Lay.SP] using hr.sub)
  · have := Offset.disjoint L.B (d := 16 + d) (n := 8) (e := 272) (k := 192) (by omega) (by omega) (by omega)
    exact this.sub_right (by simpa [Lay.DAT₂, Lay.SP, add_add] using hr.sub)
  · exact Offset.disjoint_base _ (by omega) (by omega)

/-- A state whose memory differs from that of a `Ctx` state only where the
code writes and in the 16 bytes below the frame. -/
theorem Ctx.of_frame {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem} {t t' : State}
    (hc : Ctx L g mx m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hcs : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r)
    (hmx : t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10) {rs : List Region}
    (hf : Frame (rs ++ [⟨L.B, 16⟩]) t.mem t'.mem) (hrs : ∀ r ∈ rs, WOk L r) :
    Ctx L g mx m₀ t' := by
  have keep : ∀ d, 136 ≤ d → d + 8 ≤ 256 →
      t'.mem.readW (L.SP + BitVec.ofNat 64 d) 64 = t.mem.readW (L.SP + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => hf.readW (Region.contains_self _ _) (fun r hr => slot_disj hL h₁ h₂ (by
      rcases List.mem_append.mp hr with hr | hr
      · exact .inl (hrs r hr)
      · simp only [List.mem_singleton] at hr; exact .inr hr)) (by decide)
  have hd₁ : Region.Sub L.DAT₁ L.STK := by
    have := Offset.sub_base L.B (d := 16) (n := 136) (k := 464) (by omega)
    simpa [Lay.DAT₁, Lay.SP] using this
  have hd₂ : Region.Sub L.DAT₂ L.STK := by
    have := Offset.sub_base L.B (d := 272) (n := 192) (k := 464) (by omega)
    simpa [Lay.DAT₂, Lay.SP, add_add] using this
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
theorem call_ok {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}
    {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsp : NoSp c) (hd : c.depth ≤ 1) {t : State} (hc : Ctx L g mx m₀ t)
    {rd wr : List Region} (hpre : k.pre (t.callEntry.withRegions rd wr))
    (hsub : ∀ r ∈ rd, ∃ R ∈ L.rd ++ L.FR :: L.wr, Within r R)
    (hwsub : ∀ r ∈ wr, WOk L r) {Q : State → Prop}
    (hQ : ∀ s', Ctx L g mx m₀ s' → Frame (wr ++ [⟨L.B, 16⟩]) t.mem s'.mem →
      (∀ r, (∀ i ∈ instrs c, Taint.clobbers i r = false) → s'.gpr r = t.gpr r) →
      (∃ s₂ : State, s₂.mem = s'.mem ∧ (∀ r, r ≠ .rsp → s₂.gpr r = s'.gpr r) ∧
        k.post (t.callEntry.withRegions rd wr) s₂) → Q s') :
    WP isa (.call n c) t Q := by
  have hwX : ∀ r ∈ wr, ∃ R ∈ L.FR :: L.wr, Within r R := fun r hr => by
    rcases hwsub r hr with h | h | h | h
    · exact ⟨L.SCR, by simp [hL.wr], h⟩
    · exact ⟨L.OUT, by simp [hL.wr], h⟩
    · exact ⟨L.FR, by simp, h.trans (within_base _ (by decide))⟩
    · exact ⟨L.FR, by simp, h.trans (within_off _ (by decide))⟩
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
  have hf' : Frame (wr ++ [⟨L.B, 16⟩]) t.mem s'.mem := by
    refine Frame.sub hf fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
      rw [hc.rsp]
      exact below_call_sub _ (by omega)
  exact hQ s' (hc.of_frame hL hrd hwr hcs hmx hf' hwsub) hf' hg hpost

end VG.Proof.Ed448.X86_64.SignCached
