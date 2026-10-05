import VerifiedGarbage.Impl.MlDsa.Arm.Message
import VerifiedGarbage.Proof.MlKem.Arm.Mul
import VerifiedGarbage.Proof.MlKem.Arm.Add
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlDsa.Message.Common
import VerifiedGarbage.Proof.MlKem.Arm.SampleCT
import VerifiedGarbage.Proof.MlKem.KPke1024
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.MlKem.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Verified
import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Inst

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Message.Layout`. -/
section

/-!
# ML-DSA on ARMv7, `sign_message` and `verify_message`: where everything is

Untrusted: everything here is checked by Lean. The function's buffers, the
36 bytes of stack below the stack pointer on entry (`STK`, which the calls'
frames use), `scratch` (`SC`) and the 1 KiB `X` in it after the working
space of the function on `μ` (`Lay`): the Keccak state, the sponge
functions' working space and `μ` in its first 904 bytes (`W`), then the
saved registers and arguments and the two bytes of the formatted message.
`Ctx` is what holds from the entry's saves to the exit: the permissions,
the stack pointer, `r7` pointing at `X`, the callee-saved registers, the
saves, and that memory changed only in `scratch` and `STK`. `Ctx.keep`
carries it over code that writes only within `W` and `STK`.
-/

namespace VG.Proof.MlDsa.Arm.Message

open VG VG.Arm VG.Impl.MlDsa.Arm.Message
open VG.Proof.MlDsa.Message
open VG.Spec.Sha3 (bytesAt)

theorem covers_of_within {rs rs' : List Region} (h : ∀ r ∈ rs, ∃ R ∈ rs', Within r R) : Covers rs rs' :=
  Covers.of_sub fun r hr => by
    obtain ⟨R, hR, o, hb, hl⟩ := h r hr
    exact ⟨R, hR, o, hb, hl⟩

/-! ## The layout -/

/-- The stack pointer on entry, the arguments, the size of `scratch`, the
offset `E` of the 1 KiB `X` in it, and the permissions on entry. -/
structure Lay where
  SP : BitVec 32
  key : BitVec 32
  keyLen : Nat
  msg : BitVec 32
  len : BitVec 32
  ctx : BitVec 32
  ctxLen : BitVec 32
  rnd : BitVec 32
  sig : BitVec 32
  scr : BitVec 32
  scrLen : Nat
  E : Nat
  rd : List Region
  wr : List Region

namespace Lay

variable (L : VG.Proof.MlDsa.Arm.Message.Lay)

/-- The 36 bytes of stack the calls' frames use. -/
abbrev STK : Region := ⟨State.addr L.SP - BitVec.ofNat 64 36, 36⟩
/-- `scratch`. -/
abbrev SC : Region := ⟨State.addr L.scr, L.scrLen⟩
/-- The 1 KiB, as a register holds it and as an address. -/
abbrev X32 : BitVec 32 := L.scr + BitVec.ofNat 32 L.E
abbrev X : Addr := State.addr L.X32
abbrev XS : Region := ⟨L.X, 1024⟩
/-- What the calls write in it: the Keccak state, the sponge functions'
working space and `μ`. -/
abbrev W : Region := ⟨L.X, 904⟩
abbrev ST : Addr := L.X
abbrev KS : Addr := L.X + BitVec.ofNat 64 200
abbrev MU : Addr := L.X + BitVec.ofNat 64 840
abbrev KEY : Region := ⟨State.addr L.key, L.keyLen⟩
abbrev MSG : Region := ⟨State.addr L.msg, L.len.toNat⟩
abbrev CTX : Region := ⟨State.addr L.ctx, L.ctxLen.toNat⟩

/-- The saved arguments, at `X + 912 + 4j`. -/
def vals : List (BitVec 32) := [L.key, L.msg, L.len, L.ctx, L.ctxLen, L.rnd, L.sig, L.scr]

/-- What the contract says of where everything is. -/
structure Ok : Prop where
  ctxLt : L.ctxLen.toNat < 256
  hE : L.E + 1024 ≤ L.scrLen
  hKey : 128 ≤ L.keyLen ∧ L.keyLen < 2 ^ 16
  nSP : 36 ≤ L.SP.toNat
  nScr : L.scr.toNat + L.scrLen ≤ 2 ^ 32
  inSC : L.SC ∈ L.wr
  inKey : L.KEY ∈ L.rd
  inMsg : L.MSG ∈ L.rd
  inCtx : L.CTX ∈ L.rd
  xKey : L.SC.Disjoint L.KEY
  xMsg : L.SC.Disjoint L.MSG
  xCtx : L.SC.Disjoint L.CTX
  kX : L.STK.Disjoint L.SC
  kKey : L.STK.Disjoint L.KEY
  kMsg : L.STK.Disjoint L.MSG
  kCtx : L.STK.Disjoint L.CTX
  nKey : L.key.toNat + L.keyLen ≤ 2 ^ 32
  nMsg : L.msg.toNat + L.len.toNat ≤ 2 ^ 32
  nCtx : L.ctx.toNat + L.ctxLen.toNat ≤ 2 ^ 32

end Lay

namespace Lay.Ok

variable {L : VG.Proof.MlDsa.Arm.Message.Lay}

theorem x32_lt (h : L.Ok) : L.X32.toNat + 1024 ≤ 2 ^ 32 := by
  have := h.nScr; have := h.hE
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := L.E) (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-- `X` in `scratch`. -/
theorem x_eq (h : L.Ok) : L.X = State.addr L.scr + BitVec.ofNat 64 L.E :=
  addr_add (by have := h.nScr; have := h.hE; omega)

/-- An address in the 1 KiB, as an instruction computes it from `r7`. -/
theorem xo (h : L.Ok) {o : Nat} (ho : o < 1024) :
    State.addr (L.X32 + BitVec.ofNat 32 o) = L.X + BitVec.ofNat 64 o :=
  addr_add (by have := h.x32_lt; omega)

theorem x_toNat (h : L.Ok) : L.X.toNat + 1024 ≤ 2 ^ 32 := by
  rw [Proof.MlKem.Arm.addr_toNat]; exact h.x32_lt

theorem xs_sc (h : L.Ok) : Within L.XS L.SC := ⟨L.E, h.x_eq, h.hE⟩

theorem sub_sc (h : L.Ok) {e k : Nat} (h₂ : e + k ≤ 1024) : Region.Sub ⟨L.X + BitVec.ofNat 64 e, k⟩ L.SC :=
  (Within.trans (within_off L.X h₂) h.xs_sc).sub

theorem stk_x (h : L.Ok) {e k : Nat} (h₂ : e + k ≤ 1024) :
    Region.Disjoint L.STK ⟨L.X + BitVec.ofNat 64 e, k⟩ :=
  h.kX.sub_right (h.sub_sc h₂)

theorem x_r (h : L.Ok) {r : Region} (hr : L.SC.Disjoint r) {e k : Nat} (h₂ : e + k ≤ 1024) :
    Region.Disjoint ⟨L.X + BitVec.ofNat 64 e, k⟩ r :=
  hr.sub_left (h.sub_sc h₂)

/-- The 1 KiB is writable. -/
theorem covX (h : L.Ok) {e k : Nat} (h₂ : e + k ≤ 1024) : ∃ R ∈ L.wr, Within ⟨L.X + BitVec.ofNat 64 e, k⟩ R :=
  ⟨L.SC, h.inSC, (within_off L.X h₂).trans h.xs_sc⟩

/-- Bytes of the 1 KiB are writable. -/
theorem inW (h : L.Ok) {e k : Nat} (h₂ : e + k ≤ 1024) : InRegions L.wr (L.X + BitVec.ofNat 64 e) k := by
  refine ⟨L.SC, h.inSC, ?_⟩
  rw [h.x_eq, add_add]
  have := h.hE; have := h.nScr
  exact Offset.contains_base _ (by omega) (by omega)

/-- What lies within the first 904 bytes of `X`, or in `STK`, is apart from the saves. -/
theorem sv_disj (h : L.Ok) {r : Region} (hr : Within r L.W ∨ Region.Sub r L.STK) {d n : Nat} (hd : d + n ≤ 120) :
    Region.Disjoint ⟨L.X + BitVec.ofNat 64 (904 + d), n⟩ r := by
  rcases hr with hr | hr
  · obtain ⟨o, hb, hl⟩ := hr
    obtain ⟨b, k⟩ := r
    simp only at hb hl
    subst hb
    exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
  · exact (h.kX.symm.sub_left (h.sub_sc (by omega))).sub_right hr

end Lay.Ok

/-! ## From the entry's saves to the exit -/

/-- The state from the entry's saves to the exit: `g` the registers on
entry, `m₀` the memory. -/
structure Ctx (L : VG.Proof.MlDsa.Arm.Message.Lay) (g : Reg → BitVec 32) (m₀ : Mem) (t : State) : Prop where
  rd : t.rd = L.rd
  wr : t.wr = L.wr
  sp : t.sp = L.SP
  r7 : t.gpr .r7 = L.X32
  cs : ∀ r ∈ preserved, r ≠ .r7 → r ≠ .lr → t.gpr r = g r
  s7 : t.mem.readW (L.X + BitVec.ofNat 64 (904 + 0)) 32 = g .r7
  sLR : t.mem.readW (L.X + BitVec.ofNat 64 (904 + 4)) 32 = g .lr
  slot : ∀ j < 8, t.mem.readW (L.X + BitVec.ofNat 64 (904 + (8 + 4 * j))) 32 = L.vals.getD j 0
  hdr : bytesAt t.mem (L.X + BitVec.ofNat 64 (904 + 40)) 2 = [0, BitVec.ofNat 8 L.ctxLen.toNat]
  frame : Frame [L.SC, L.STK] m₀ t.mem

namespace Ctx

variable {L : VG.Proof.MlDsa.Arm.Message.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t t' : State}

/-- Code that writes only registers but `r7` and the callee-saved ones. -/
theorem regs (hc : VG.Proof.MlDsa.Arm.Message.Ctx L g m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp)
    (hm : t'.mem = t.mem) (hg : ∀ r ∈ preserved, r ≠ .lr → t'.gpr r = t.gpr r) : VG.Proof.MlDsa.Arm.Message.Ctx L g m₀ t' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp, (hg .r7 (by decide) (by decide)).trans hc.r7,
    fun r hr h7 hl => (hg r hr hl).trans (hc.cs r hr h7 hl),
    by rw [hm]; exact hc.s7, by rw [hm]; exact hc.sLR, fun j hj => by rw [hm]; exact hc.slot j hj,
    by rw [hm]; exact hc.hdr, by rw [hm]; exact hc.frame⟩

/-- Code that writes memory only within the first 904 bytes of `X` and in `STK`. -/
theorem keep (hc : VG.Proof.MlDsa.Arm.Message.Ctx L g m₀ t) (hL : L.Ok) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp)
    (hg : ∀ r ∈ preserved, r ≠ .lr → t'.gpr r = t.gpr r) {rs : List Region} (hf : Frame rs t.mem t'.mem)
    (hrs : ∀ r ∈ rs, Within r L.W ∨ Region.Sub r L.STK) : VG.Proof.MlDsa.Arm.Message.Ctx L g m₀ t' := by
  have keep : ∀ d, d + 4 ≤ 120 → t'.mem.readW (L.X + BitVec.ofNat 64 (904 + d)) 32 =
      t.mem.readW (L.X + BitVec.ofNat 64 (904 + d)) 32 :=
    fun d h => hf.readW (Region.contains_self _ _) (fun r hr => hL.sv_disj (hrs r hr) h) (by decide)
  have khdr : bytesAt t'.mem (L.X + BitVec.ofNat 64 (904 + 40)) 2 =
      bytesAt t.mem (L.X + BitVec.ofNat 64 (904 + 40)) 2 :=
    Proof.MlKem.bytesAt_congr fun i hi =>
      hf.bytes (R := ⟨_, 2⟩) (fun r hr => hL.sv_disj (hrs r hr) (by decide)) (by show 2 ≤ 2 ^ 64; decide) hi
  refine ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp, (hg .r7 (by decide) (by decide)).trans hc.r7,
    fun r hr h7 hl => (hg r hr hl).trans (hc.cs r hr h7 hl),
    (keep 0 (by decide)).trans hc.s7, (keep 4 (by decide)).trans hc.sLR,
    fun j hj => (keep _ (by omega)).trans (hc.slot j hj), khdr.trans hc.hdr,
    hc.frame.trans (Frame.sub hf fun r hr => ?_)⟩
  rcases hrs r hr with h | h
  · exact ⟨L.SC, by simp, (h.trans ((within_base L.X (by decide : 904 ≤ 1024)).trans hL.xs_sc)).sub⟩
  · exact ⟨L.STK, by simp, h⟩

/-- A byte of a region apart from `scratch` and `STK`, as on entry. -/
theorem bytesAt_eq (hc : VG.Proof.MlDsa.Arm.Message.Ctx L g m₀ t) {p : Addr} {n : Nat} (hx : L.SC.Disjoint ⟨p, n⟩)
    (hk : L.STK.Disjoint ⟨p, n⟩) (hn : n ≤ 2 ^ 64) : bytesAt t.mem p n = bytesAt m₀ p n :=
  Proof.MlKem.bytesAt_congr fun _ hi => Frame.bytes (R := ⟨p, n⟩) hc.frame (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hx.symm
    · exact hk.symm) hn hi

/-- Bytes of `X` are readable. -/
theorem inX (hc : VG.Proof.MlDsa.Arm.Message.Ctx L g m₀ t) (hL : L.Ok) {e k : Nat} (h₂ : e + k ≤ 1024) :
    InRegions (t.rd ++ t.wr) (L.X + BitVec.ofNat 64 e) k := by
  obtain ⟨R, hR, hc'⟩ := hL.inW h₂
  exact ⟨R, by rw [hc.rd, hc.wr]; exact List.mem_append_right _ hR, hc'⟩

end Ctx

end VG.Proof.MlDsa.Arm.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Message.Step`. -/
section

/-!
# ML-DSA on ARMv7, `sign_message` and `verify_message`: single instructions

Untrusted: everything here is checked by Lean. Each instruction the
functions run, as a step of a block that leaves its result and changes
nothing else (`Only` the register it writes, or `MemTo` the memory a store
leaves), passed on to the rest of the block.
-/

namespace VG.Proof.MlDsa.Arm.Message

open VG VG.Arm

/-- `s'` differs from `s` only in the registers `rs` (and the flags). -/
structure Only (rs : List Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ rs → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

namespace Only

theorem refl (rs : List Reg) (s : State) : VG.Proof.MlDsa.Arm.Message.Only rs s s := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem trans {rs : List Reg} {s₁ s₂ s₃ : State} (h₁ : VG.Proof.MlDsa.Arm.Message.Only rs s₁ s₂) (h₂ : VG.Proof.MlDsa.Arm.Message.Only rs s₂ s₃) : VG.Proof.MlDsa.Arm.Message.Only rs s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    h₂.sp.trans h₁.sp⟩

theorem mono {rs rs' : List Reg} {s s' : State} (h : VG.Proof.MlDsa.Arm.Message.Only rs s s') (hs : ∀ r ∈ rs, r ∈ rs') : VG.Proof.MlDsa.Arm.Message.Only rs' s s' :=
  ⟨fun r hr => h.gpr r fun h' => hr (hs r h'), h.mem, h.rd, h.wr, h.sp⟩

theorem get {rs : List Reg} {s s' : State} (h : VG.Proof.MlDsa.Arm.Message.Only rs s s') (r : Reg) (hr : r ∉ rs := by decide) :
    s'.gpr r = s.gpr r := h.gpr r hr

end Only

/-- `s'` is `s` with the memory `m`. -/
structure MemTo (s s' : State) (m : Mem) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = m
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem wp_nil {s : State} {Q : State → Prop} (h : Q s) : WP isa (.block []) s Q := WP.block_nil h

theorem only_setReg (s : State) (d : Reg) (x : BitVec 32) : VG.Proof.MlDsa.Arm.Message.Only [d] s (s.setReg d x) :=
  ⟨fun r hr => by
    simp only [List.mem_singleton] at hr
    simp [State.setReg, hr], rfl, rfl, rfl, rfl⟩

/-- An instruction that writes the register `d`. -/
theorem wp_setReg {i : Instr} {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {x : BitVec 32}
    (he : exec i s = some (s.setReg d x))
    (k : ∀ s1, VG.Proof.MlDsa.Arm.Message.Only [d] s s1 → s1.gpr d = x → WP isa (.block is) s1 Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨_, he, k _ (VG.Proof.MlDsa.Arm.Message.only_setReg s d x) (by simp [State.setReg])⟩

theorem wp_ldr {t n : Reg} {off : Nat} {is : List Instr} {s : State} {Q : State → Prop} (ho : off < 4096)
    (h : InRegions (s.rd ++ s.wr) (State.addr (s.gpr n + BitVec.ofNat 32 off)) 4)
    (k : ∀ s1, VG.Proof.MlDsa.Arm.Message.Only [t] s s1 → s1.gpr t = s.mem.readW (State.addr (s.gpr n + BitVec.ofNat 32 off)) 32 →
      WP isa (.block is) s1 Q) : WP isa (.block (.ldr t n off :: is)) s Q :=
  VG.Proof.MlDsa.Arm.Message.wp_setReg (exec_ldr ho h) k

theorem wp_ldrSp {t : Reg} {off : Nat} {is : List Instr} {s : State} {Q : State → Prop} (ho : off < 4096)
    (h : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 off)) 4)
    (k : ∀ s1, VG.Proof.MlDsa.Arm.Message.Only [t] s s1 → s1.gpr t = s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 off)) 32 →
      WP isa (.block is) s1 Q) : WP isa (.block (.ldrSp t off :: is)) s Q :=
  VG.Proof.MlDsa.Arm.Message.wp_setReg (by simp only [exec, ho, ite_true, State.load32, h, Option.map_some]) k

theorem wp_movw {d : Reg} {v : BitVec 16} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s1, VG.Proof.MlDsa.Arm.Message.Only [d] s s1 → s1.gpr d = v.setWidth 32 → WP isa (.block is) s1 Q) :
    WP isa (.block (.movw d v :: is)) s Q :=
  VG.Proof.MlDsa.Arm.Message.wp_setReg rfl k

theorem wp_movt {d : Reg} {v : BitVec 16} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s1, VG.Proof.MlDsa.Arm.Message.Only [d] s s1 → s1.gpr d = (v ++ (s.gpr d).extractLsb' 0 16 : BitVec 32) → WP isa (.block is) s1 Q) :
    WP isa (.block (.movt d v :: is)) s Q :=
  VG.Proof.MlDsa.Arm.Message.wp_setReg rfl k

theorem wp_movReg {d r : Reg} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s1, VG.Proof.MlDsa.Arm.Message.Only [d] s s1 → s1.gpr d = s.gpr r → WP isa (.block is) s1 Q) :
    WP isa (.block (.mov d (.reg r) :: is)) s Q :=
  VG.Proof.MlDsa.Arm.Message.wp_setReg rfl k

theorem wp_movImm {d : Reg} {v : BitVec 32} {is : List Instr} {s : State} {Q : State → Prop}
    (hv : encodable v = true) (k : ∀ s1, VG.Proof.MlDsa.Arm.Message.Only [d] s s1 → s1.gpr d = v → WP isa (.block is) s1 Q) :
    WP isa (.block (.mov d (.imm v) :: is)) s Q :=
  VG.Proof.MlDsa.Arm.Message.wp_setReg (by simp only [exec, Op2.eval, hv, ite_true, Option.map_some]) k

theorem wp_movLsr {d r : Reg} {n : Nat} {is : List Instr} {s : State} {Q : State → Prop} (h1 : 1 ≤ n)
    (h2 : n ≤ 31) (k : ∀ s1, VG.Proof.MlDsa.Arm.Message.Only [d] s s1 → s1.gpr d = s.gpr r >>> n → WP isa (.block is) s1 Q) :
    WP isa (.block (.mov d (.shifted r .lsr n) :: is)) s Q :=
  VG.Proof.MlDsa.Arm.Message.wp_setReg (by simp only [exec, Op2.eval, h1, h2, and_self, ite_true, Option.map_some]) k

theorem wp_addReg {d n m : Reg} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s1, VG.Proof.MlDsa.Arm.Message.Only [d] s s1 → s1.gpr d = s.gpr n + s.gpr m → WP isa (.block is) s1 Q) :
    WP isa (.block (.dp .add d n (.reg m) :: is)) s Q :=
  VG.Proof.MlDsa.Arm.Message.wp_setReg rfl k

theorem wp_addImm {d n : Reg} {v : BitVec 32} {is : List Instr} {s : State} {Q : State → Prop}
    (hv : encodable v = true) (k : ∀ s1, VG.Proof.MlDsa.Arm.Message.Only [d] s s1 → s1.gpr d = s.gpr n + v → WP isa (.block is) s1 Q) :
    WP isa (.block (.dp .add d n (.imm v) :: is)) s Q :=
  VG.Proof.MlDsa.Arm.Message.wp_setReg (by simp only [exec, Op2.eval, hv, ite_true, Option.map_some]) k

theorem wp_str {t n : Reg} {off : Nat} {is : List Instr} {s : State} {Q : State → Prop} (ho : off < 4096)
    (h : InRegions s.wr (State.addr (s.gpr n + BitVec.ofNat 32 off)) 4)
    (k : ∀ s1, VG.Proof.MlDsa.Arm.Message.MemTo s s1 (s.mem.writeW (State.addr (s.gpr n + BitVec.ofNat 32 off)) (s.gpr t)) →
      WP isa (.block is) s1 Q) : WP isa (.block (.str t n off :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨_, exec_str ho h, k _ ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

theorem wp_strb {t n : Reg} {off : Nat} {is : List Instr} {s : State} {Q : State → Prop} (ho : off < 4096)
    (h : InRegions s.wr (State.addr (s.gpr n + BitVec.ofNat 32 off)) 1)
    (k : ∀ s1, VG.Proof.MlDsa.Arm.Message.MemTo s s1 (s.mem.writeW (State.addr (s.gpr n + BitVec.ofNat 32 off)) ((s.gpr t).setWidth 8)) →
      WP isa (.block is) s1 Q) : WP isa (.block (.strb t n off :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨{ s with mem := s.mem.writeW (State.addr (s.gpr n + BitVec.ofNat 32 off)) ((s.gpr t).setWidth 8) },
    by simp only [exec, ho, ite_true, State.store8, h], k _ ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

/-- `cmp n, #v`: the flags only, `Z` set if `n = v`. -/
theorem wp_cmpImm {n : Reg} {v : BitVec 32} {is : List Instr} {s : State} {Q : State → Prop}
    (hv : encodable v = true)
    (k : ∀ s1, VG.Proof.MlDsa.Arm.Message.Only [] s s1 → s1.z = (s.gpr n - v == 0) → WP isa (.block is) s1 Q) :
    WP isa (.block (.cmp n (.imm v) :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨subFlags s (s.gpr n) v, by simp only [exec, Op2.eval, hv, ite_true, Option.map_some],
    k _ ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩ rfl⟩

end VG.Proof.MlDsa.Arm.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Message.Args`. -/
section

/-!
# ML-DSA on ARMv7, `sign_message` and `verify_message`: the moves of a call's arguments

Untrusted: everything here is checked by Lean. Each argument's value
(`Arg.val`): a saved argument (a slot at `r7 + f`), plus an offset, an
offset from `r7`, an immediate, or `r0`. The moves of a list of arguments
into distinct registers but `r7`, with `r0` read only before it is written
(`argsOk`), leave each its value and change nothing else (`setArgs_ok`).
-/

namespace VG.Proof.MlDsa.Arm.Message

open VG VG.Arm VG.Impl.MlDsa.Arm.Message
open VG.Proof.MlDsa.Message

/-- The value of an argument in the state `s`. -/
def _root_.VG.Impl.MlDsa.Arm.Message.Arg.val (s : State) : VG.Impl.MlDsa.Arm.Message.Arg → BitVec 32
  | .slot f => s.mem.readW (State.addr (s.gpr .r7 + BitVec.ofNat 32 f)) 32
  | .slotOff f o => s.mem.readW (State.addr (s.gpr .r7 + BitVec.ofNat 32 f)) 32 + BitVec.ofNat 32 o
  | .off o => s.gpr .r7 + BitVec.ofNat 32 o
  | .imm v => BitVec.ofNat 32 v
  | .ret => s.gpr .r0

/-- A slot within the 1 KiB, an offset or an immediate the instructions take. -/
def _root_.VG.Impl.MlDsa.Arm.Message.Arg.ok : VG.Impl.MlDsa.Arm.Message.Arg → Bool
  | .slot f => decide (f + 4 ≤ 1024)
  | .slotOff f o => decide (f + 4 ≤ 1024) && encodable (BitVec.ofNat 32 o)
  | .off o => decide (o < 65536)
  | .imm v => decide (v < 65536)
  | .ret => true

def _root_.VG.Impl.MlDsa.Arm.Message.Arg.isRet : VG.Impl.MlDsa.Arm.Message.Arg → Bool
  | .ret => true
  | _ => false

/-- The slots of the 1 KiB are readable. -/
abbrev XOk (s : State) : Prop :=
  ∀ f, f + 4 ≤ 1024 → InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r7 + BitVec.ofNat 32 f)) 4

theorem setWidth_ofNat16 {v : Nat} (h : v < 65536) : (BitVec.ofNat 16 v).setWidth 32 = BitVec.ofNat 32 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem Arg.mov_ok (d : Reg) (hd : d ≠ .r7) (a : VG.Impl.MlDsa.Arm.Message.Arg) (ha : a.ok = true) (s : State) (hx : VG.Proof.MlDsa.Arm.Message.XOk s) :
    WP isa (.block (a.mov d)) s fun s1 => s1.gpr d = a.val s ∧ VG.Proof.MlDsa.Arm.Message.Only [d] s s1 := by
  cases a with
  | slot f =>
    simp only [Arg.ok, decide_eq_true_eq] at ha
    exact VG.Proof.MlDsa.Arm.Message.wp_ldr (by omega) (hx f ha) fun s1 o1 e1 => VG.Proof.MlDsa.Arm.Message.wp_nil ⟨e1, o1⟩
  | slotOff f o =>
    simp only [Arg.ok, Bool.and_eq_true, decide_eq_true_eq] at ha
    refine VG.Proof.MlDsa.Arm.Message.wp_ldr (by omega) (hx f ha.1) fun s1 o1 e1 => ?_
    refine VG.Proof.MlDsa.Arm.Message.wp_addImm ha.2 fun s2 o2 e2 => VG.Proof.MlDsa.Arm.Message.wp_nil ⟨by rw [e2, e1]; rfl, ?_⟩
    exact (o1.trans o2).mono (fun r hr => by simpa using hr)
  | off o =>
    simp only [Arg.ok, decide_eq_true_eq] at ha
    refine VG.Proof.MlDsa.Arm.Message.wp_movw fun s1 o1 e1 => VG.Proof.MlDsa.Arm.Message.wp_addReg fun s2 o2 e2 => VG.Proof.MlDsa.Arm.Message.wp_nil ⟨?_, (o1.trans o2).mono fun r hr => by simpa using hr⟩
    rw [e2, e1, o1.get .r7 (by simpa using hd.symm), VG.Proof.MlDsa.Arm.Message.setWidth_ofNat16 ha]
    rfl
  | imm v =>
    simp only [Arg.ok, decide_eq_true_eq] at ha
    exact VG.Proof.MlDsa.Arm.Message.wp_movw fun s1 o1 e1 => VG.Proof.MlDsa.Arm.Message.wp_nil ⟨by rw [e1, VG.Proof.MlDsa.Arm.Message.setWidth_ofNat16 ha]; rfl, o1⟩
  | ret => exact VG.Proof.MlDsa.Arm.Message.wp_movReg fun s1 o1 e1 => VG.Proof.MlDsa.Arm.Message.wp_nil ⟨e1, o1⟩

/-- Distinct registers but `r7`, each argument fit for its instructions,
and `r0` read only before it is written. -/
def argsOk : List (Reg × VG.Impl.MlDsa.Arm.Message.Arg) → Bool
  | [] => true
  | (d, a) :: as => a.ok && d != .r7 &&
      as.all (fun da => da.1 != d && (d != .r0 || !da.2.isRet)) && VG.Proof.MlDsa.Arm.Message.argsOk as

/-- The value of an argument is the same after a move into another register
(not `r7`, and not `r0` if the argument is `r0`). -/
theorem Arg.val_only {d : Reg} (hd : d ≠ .r7) {s s1 : State} (o : VG.Proof.MlDsa.Arm.Message.Only [d] s s1) (a : VG.Impl.MlDsa.Arm.Message.Arg)
    (ha : d ≠ .r0 ∨ a.isRet = false) : a.val s1 = a.val s := by
  have h7 : s1.gpr .r7 = s.gpr .r7 := o.gpr _ (by simp only [List.mem_singleton]; exact fun h => hd h.symm)
  cases a with
  | ret =>
    simp only [Arg.isRet, Bool.true_eq_false, or_false] at ha
    simp only [Arg.val]
    exact o.gpr _ (by simp only [List.mem_singleton]; exact fun h => ha h.symm)
  | _ => simp only [Arg.val, h7, o.mem]

theorem XOk.only {d : Reg} (hd : d ≠ .r7) {s s1 : State} (o : VG.Proof.MlDsa.Arm.Message.Only [d] s s1) (h : VG.Proof.MlDsa.Arm.Message.XOk s) : VG.Proof.MlDsa.Arm.Message.XOk s1 := by
  intro f hf
  rw [o.rd, o.wr, o.gpr _ (by simp only [List.mem_singleton]; exact fun h => hd h.symm)]
  exact h f hf

/-- The moves of the arguments `as`. -/
theorem setArgs_ok : ∀ (as : List (Reg × VG.Impl.MlDsa.Arm.Message.Arg)), VG.Proof.MlDsa.Arm.Message.argsOk as = true → ∀ s : State, VG.Proof.MlDsa.Arm.Message.XOk s →
    WP isa (.block (VG.Impl.MlDsa.Arm.Message.setArgs as)) s fun s1 => (∀ da ∈ as, s1.gpr da.1 = da.2.val s) ∧ VG.Proof.MlDsa.Arm.Message.Only (as.map (·.1)) s s1
  | [], _, s, _ => VG.Proof.MlDsa.Arm.Message.wp_nil ⟨fun _ h => by simp at h, Only.refl _ _⟩
  | (d, a) :: as, h, s, hx => by
    simp only [VG.Proof.MlDsa.Arm.Message.argsOk, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true, Bool.or_eq_true,
      Bool.not_eq_true'] at h
    obtain ⟨⟨⟨ha, hd⟩, hall⟩, hrest⟩ := h
    simp only [VG.Impl.MlDsa.Arm.Message.setArgs, List.flatMap_cons]
    rw [WP.block_append_iff]
    refine WP.mono (Arg.mov_ok d hd a ha s hx) fun s1 ⟨h1, o1⟩ => ?_
    refine WP.mono (VG.Proof.MlDsa.Arm.Message.setArgs_ok as hrest s1 (hx.only hd o1)) fun s2 ⟨h2, o2⟩ => ⟨fun da hda => ?_, ?_⟩
    · rcases List.mem_cons.mp hda with rfl | hda
      · rw [o2.gpr _ (fun hm => by
          obtain ⟨x, hx', hx''⟩ := List.mem_map.mp hm
          exact (hall x hx').1 hx''), h1]
      · rw [h2 da hda, Arg.val_only hd o1 da.2 ((hall da hda).2.elim .inl fun h' => .inr h')]
    · exact (o1.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]).trans
        (o2.mono fun r hr => by simp only [List.map_cons]; exact List.mem_cons_of_mem _ hr)

/-! ## In `Ctx` -/

section
variable {L : VG.Proof.MlDsa.Arm.Message.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

theorem Ctx.xOk (hc : VG.Proof.MlDsa.Arm.Message.Ctx L g m₀ t) (hL : L.Ok) : VG.Proof.MlDsa.Arm.Message.XOk t := fun f hf => by
  rw [hc.r7, hL.xo (by omega)]; exact hc.inX hL hf

theorem Ctx.off (hc : VG.Proof.MlDsa.Arm.Message.Ctx L g m₀ t) (o : Nat) : (Arg.off o).val t = L.X32 + BitVec.ofNat 32 o := by
  simp only [Arg.val, hc.r7]

/-- The saved argument `j`. -/
theorem Ctx.slotV (hc : VG.Proof.MlDsa.Arm.Message.Ctx L g m₀ t) (hL : L.Ok) {f j : Nat} (hf : f = 912 + 4 * j) (hj : j < 8) :
    (Arg.slot f).val t = L.vals.getD j 0 := by
  subst hf
  have := hc.slot j hj
  simp only [Arg.val, hc.r7]
  rw [hL.xo (by omega), ← this, show 904 + (8 + 4 * j) = 912 + 4 * j by omega]

end

end VG.Proof.MlDsa.Arm.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Message.Hash`. -/
section

/-!
# ML-DSA on ARMv7, `sign_message` and `verify_message`: SHAKE256 through the sponge functions

Untrusted: everything here is checked by Lean. In `Ctx`: zeroing the Keccak
state at `X` (`zeroSt_ok`), and the calls of `vg_keccak_absorb`,
`vg_keccak_pad` and `vg_keccak_squeeze` in their frames on it, with their
working space at `X + 200` (`kabs_ok`, `kpad_ok`, `ksqz_ok`, from ML-KEM's
call lemmas, `Proof/MlKem/Arm/Keccak.lean`).
-/

namespace VG.Proof.MlDsa.Arm.Message

open VG VG.Arm VG.Impl.MlDsa.Arm.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.Arm (AbsorbArgs PadArgs SqueezeArgs absorb_ok pad_ok squeeze_ok regA below Kept)
open VG.Spec.Sha3 (bytesAt stateAt rates absorb pad squeezeFrom Repr)

section
variable {L : VG.Proof.MlDsa.Arm.Message.Lay} {g : Reg → BitVec 32} {m₀ : Mem}

theorem x0 (L : VG.Proof.MlDsa.Arm.Message.Lay) : L.X + BitVec.ofNat 64 0 = L.X := BitVec.add_zero _

theorem x0' (L : VG.Proof.MlDsa.Arm.Message.Lay) : L.X32 + BitVec.ofNat 32 0 = L.X32 := BitVec.add_zero _

theorem st_ks : Region.Disjoint ⟨L.ST, 200⟩ ⟨L.KS, 640⟩ := by
  have := Offset.disjoint L.X (d := 0) (n := 200) (e := 200) (k := 640) (by omega) (by omega) (by omega)
  simpa only [VG.Proof.MlDsa.Arm.Message.x0] using this

theorem st_mu : Region.Disjoint ⟨L.ST, 200⟩ ⟨L.MU, 64⟩ := by
  have := Offset.disjoint L.X (d := 0) (n := 200) (e := 840) (k := 64) (by omega) (by omega) (by omega)
  simpa only [VG.Proof.MlDsa.Arm.Message.x0] using this

theorem mu_ks : Region.Disjoint ⟨L.MU, 64⟩ ⟨L.KS, 640⟩ :=
  Offset.disjoint L.X (d := 840) (n := 64) (e := 200) (k := 640) (by omega) (by omega) (by omega)

theorem w_st : Within ⟨L.ST, 200⟩ L.W := within_base _ (by omega)
theorem w_ks : Within ⟨L.KS, 640⟩ L.W := within_off _ (by omega)
theorem w_mu : Within ⟨L.MU, 64⟩ L.W := within_off _ (by omega)

theorem k_st (hL : L.Ok) : L.STK.Disjoint ⟨L.ST, 200⟩ := by
  have := hL.stk_x (e := 0) (k := 200) (by omega); simpa only [VG.Proof.MlDsa.Arm.Message.x0] using this
theorem k_ks (hL : L.Ok) : L.STK.Disjoint ⟨L.KS, 640⟩ := hL.stk_x (by omega)
theorem k_mu (hL : L.Ok) : L.STK.Disjoint ⟨L.MU, 64⟩ := hL.stk_x (by omega)

/-- The 8 bytes a call's frame pushes lie in `STK`. -/
theorem below_stk {t : State} (hsp : t.sp = L.SP) : Region.Sub (below t 8) L.STK := by
  simp only [below, hsp]; exact Offset.sub_below _ (by omega) (by omega)

theorem cov_x (hL : L.Ok) {e k : Nat} (h₂ : e + k ≤ 1024) :
    ∃ R ∈ L.rd ++ L.wr, Within ⟨L.X + BitVec.ofNat 64 e, k⟩ R := by
  obtain ⟨R, hR, hw⟩ := hL.covX h₂; exact ⟨R, List.mem_append_right _ hR, hw⟩

theorem cov_x0 (hL : L.Ok) : ∃ R ∈ L.rd ++ L.wr, Within ⟨L.X, 200⟩ R := by
  have := VG.Proof.MlDsa.Arm.Message.cov_x hL (e := 0) (k := 200) (by omega); rwa [VG.Proof.MlDsa.Arm.Message.x0] at this

theorem cov_xw0 (hL : L.Ok) : ∃ R ∈ L.wr, Within ⟨L.X, 200⟩ R := by
  have := hL.covX (e := 0) (k := 200) (by omega); rwa [VG.Proof.MlDsa.Arm.Message.x0] at this

theorem not_pres {r : Reg} (hr : r ∈ preserved) (hl : r ≠ .lr) (rs : List Reg)
    (h : ∀ d ∈ rs, d ∉ preserved ∨ d = .lr := by decide) : r ∉ rs := fun hm => by
  rcases h r hm with h | h
  · exact h hr
  · exact hl h

/-- The address of the sponge functions' working space. -/
theorem ks_eq (hL : L.Ok) : State.addr (L.X32 + BitVec.ofNat 32 200) = L.KS := hL.xo (by decide)
theorem mu_eq (hL : L.Ok) : State.addr (L.X32 + BitVec.ofNat 32 840) = L.MU := hL.xo (by decide)

theorem x32_toNat (hL : L.Ok) {o : Nat} (ho : o < 1024) : (L.X32 + BitVec.ofNat 32 o).toNat = L.X32.toNat + o := by
  have := hL.x32_lt
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega), Nat.mod_eq_of_lt (by omega)]

/-- What a call that keeps `Kept` of regions within the first 904 bytes of
`X` and its frame leaves. -/
theorem Ctx.kept {t t' : State} (hc : VG.Proof.MlDsa.Arm.Message.Ctx L g m₀ t) (hL : L.Ok) {rs : List Region} (hk : Kept rs t t')
    (hrs : ∀ r ∈ rs, Within r L.W ∨ Region.Sub r L.STK) : VG.Proof.MlDsa.Arm.Message.Ctx L g m₀ t' :=
  hc.keep hL hk.rd hk.wr hk.sp hk.cs hk.frame hrs

/-! ## Zeroing the state -/

theorem zeroSt_ok (hL : L.Ok) {t : State} (hc : VG.Proof.MlDsa.Arm.Message.Ctx L g m₀ t) :
    WP isa (.block zeroSt) t fun t' => VG.Proof.MlDsa.Arm.Message.Ctx L g m₀ t' ∧ Frame [⟨L.ST, 200⟩] t.mem t'.mem ∧
      stateAt t'.mem L.ST = Spec.Sha3.zero := by
  rw [zeroSt, Impl.MlKem.Arm.zeroState, ← List.singleton_append, WP.block_append_iff]
  refine VG.Proof.MlDsa.Arm.Message.wp_movImm (d := .r12) (v := 0) (by decide) fun t1 o1 e1 => VG.Proof.MlDsa.Arm.Message.wp_nil ?_
  have e7 : t1.gpr .r7 = L.X32 := by rw [o1.get .r7, hc.r7]
  refine WP.mono (Proof.MlKem.Arm.Sample.zeroWords_ok .r7 (s₁ := t1) e1 (by rw [e7]; have := hL.x32_lt; omega)
    fun k hk => by rw [e7, o1.wr, hc.wr]; exact hL.inW (by omega)) fun t2 h₂ => ?_
  have hf := h₂.frame
  have hz := h₂.zero
  rw [e7] at hf hz
  have hc1 : VG.Proof.MlDsa.Arm.Message.Ctx L g m₀ t1 := hc.regs o1.rd o1.wr o1.sp o1.mem fun r hr hl => o1.gpr r (VG.Proof.MlDsa.Arm.Message.not_pres hr hl _)
  rw [o1.mem] at hf
  refine ⟨hc1.keep hL h₂.rd h₂.wr h₂.sp (fun r _ _ => by rw [h₂.gpr]) (by rwa [o1.mem])
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact .inl VG.Proof.MlDsa.Arm.Message.w_st), hf,
    Proof.MlKem.Arm.Sample.stateAt_zero hz⟩

/-! ## Absorbing -/

/-- The arguments of a call of `vg_keccak_absorb`. -/
abbrev absArgs (src len pos : VG.Impl.MlDsa.Arm.Message.Arg) : List (Reg × VG.Impl.MlDsa.Arm.Message.Arg) :=
  [(.r2, pos), (.r0, .off oST), (.r1, .imm 136), (.r3, src), (.r12, len), (.lr, .off oKS)]

theorem kabs_ok (hL : L.Ok) {t : State} (hc : VG.Proof.MlDsa.Arm.Message.Ctx L g m₀ t)
    {src len pos : VG.Impl.MlDsa.Arm.Message.Arg} (hok : VG.Proof.MlDsa.Arm.Message.argsOk (VG.Proof.MlDsa.Arm.Message.absArgs src len pos) = true)
    {dp : BitVec 32} {n q : Nat} (hdp : src.val t = dp) (hn : len.val t = BitVec.ofNat 32 n)
    (hq : pos.val t = BitVec.ofNat 32 q) (hql : q < 136) (hnl : n < 2 ^ 32) (hfit : dp.toNat + n ≤ 2 ^ 32)
    (hin : ∃ R ∈ L.rd ++ L.wr, Within ⟨State.addr dp, n⟩ R)
    (dS : Region.Disjoint ⟨State.addr dp, n⟩ ⟨L.ST, 200⟩) (dK : Region.Disjoint ⟨State.addr dp, n⟩ ⟨L.KS, 640⟩)
    (kD : L.STK.Disjoint ⟨State.addr dp, n⟩) :
    WP isa (VG.Impl.MlDsa.Arm.Message.kabs src len pos) t fun t' => VG.Proof.MlDsa.Arm.Message.Ctx L g m₀ t' ∧
      Frame [⟨L.ST, 200⟩, ⟨L.KS, 640⟩, L.STK] t.mem t'.mem ∧
      (∀ msg, Repr t.mem L.ST 136 msg → q = msg.length % 136 →
        Repr t'.mem L.ST 136 (msg ++ bytesAt t.mem (State.addr dp) n)) ∧ (t'.gpr .r0).toNat = (q + n) % 136 := by
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Message.setArgs_ok _ hok t (hc.xOk hL)) fun t1 ⟨hA, o⟩ => ?_)
  have hc1 : VG.Proof.MlDsa.Arm.Message.Ctx L g m₀ t1 := hc.regs o.rd o.wr o.sp o.mem fun r hr hl => o.gpr r (by simp only [List.map_cons, List.map_nil]; exact VG.Proof.MlDsa.Arm.Message.not_pres hr hl _)
  have e2 := hA (.r2, pos) (by simp)
  have e0 := hA (.r0, .off oST) (by simp)
  have e1 := hA (.r1, .imm 136) (by simp)
  have e3 := hA (.r3, src) (by simp)
  have e4 := hA (.r12, len) (by simp)
  have e5 := hA (.lr, .off oKS) (by simp)
  simp only [Arg.val, hc.r7, oST, oKS, VG.Proof.MlDsa.Arm.Message.x0'] at e0 e1 e5
  rw [hq] at e2
  rw [hdp] at e3
  rw [hn] at e4
  have hs1 : t1.sp = L.SP := hc1.sp
  have bs := VG.Proof.MlDsa.Arm.Message.below_stk hs1
  have hks := VG.Proof.MlDsa.Arm.Message.ks_eq hL
  refine absorb_ok (st := L.X32) (scr := L.X32 + BitVec.ofNat 32 200) (data := dp) (rate := 136) (pos := q)
    (len := n) ⟨e0, e1, e2, e3, e4, e5, by decide, hql, hnl, by rw [hs1]; have := hL.nSP; omega,
      by have := hL.x32_lt; omega, hfit, by rw [VG.Proof.MlDsa.Arm.Message.x32_toNat hL (by omega)]; have := hL.x32_lt; omega,
      by simp only [VG.Proof.MlKem.Arm.regA, hks]; exact VG.Proof.MlDsa.Arm.Message.st_ks, by simp only [VG.Proof.MlKem.Arm.regA]; exact dS,
      by simp only [VG.Proof.MlKem.Arm.regA, hks]; exact dK,
      by simp only [VG.Proof.MlKem.Arm.regA]; exact (VG.Proof.MlDsa.Arm.Message.k_st hL).sub_left bs, by simp only [VG.Proof.MlKem.Arm.regA, hks]; exact (VG.Proof.MlDsa.Arm.Message.k_ks hL).sub_left bs,
      by simp only [VG.Proof.MlKem.Arm.regA]; exact kD.sub_left bs, ?_, ?_⟩ fun s' hk hrep hx => ?_
  · simp only [VG.Proof.MlKem.Arm.regA, hks, hc1.wr]
    refine VG.Proof.MlDsa.Arm.Message.covers_of_within fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact VG.Proof.MlDsa.Arm.Message.cov_xw0 hL
    · exact hL.covX (e := 200) (by omega)
  · simp only [VG.Proof.MlKem.Arm.regA, hc1.rd, hc1.wr]
    refine VG.Proof.MlDsa.Arm.Message.covers_of_within fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hin
  · simp only [VG.Proof.MlKem.Arm.regA, hks] at hk hrep
    refine ⟨hc1.kept hL hk fun r hr => ?_, ?_, fun msg hm hp => ?_, hx⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [.inl VG.Proof.MlDsa.Arm.Message.w_st, .inl VG.Proof.MlDsa.Arm.Message.w_ks, .inr bs]
    · rw [← o.mem]
      exact hk.frame.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
        · exact ⟨_, by simp, bs⟩
    · have := hrep msg (by rw [o.mem]; exact hm) hp
      rwa [o.mem] at this

/-! ## Padding -/

/-- The arguments of a call of `vg_keccak_pad`. -/
abbrev padArgs (pos : VG.Impl.MlDsa.Arm.Message.Arg) : List (Reg × VG.Impl.MlDsa.Arm.Message.Arg) :=
  [(.r2, pos), (.r0, .off oST), (.r1, .imm 136), (.r3, .imm 0x1f), (.lr, .off oKS)]

theorem kpad_ok (hL : L.Ok) {t : State} (hc : VG.Proof.MlDsa.Arm.Message.Ctx L g m₀ t)
    {pos : VG.Impl.MlDsa.Arm.Message.Arg} (hok : VG.Proof.MlDsa.Arm.Message.argsOk (VG.Proof.MlDsa.Arm.Message.padArgs pos) = true) {q : Nat}
    (hq : pos.val t = BitVec.ofNat 32 q) (hql : q < 136) :
    WP isa (VG.Impl.MlDsa.Arm.Message.kpad pos) t fun t' => VG.Proof.MlDsa.Arm.Message.Ctx L g m₀ t' ∧
      Frame [⟨L.ST, 200⟩, ⟨L.KS, 640⟩, L.STK] t.mem t'.mem ∧
      (∀ msg, Repr t.mem L.ST 136 msg → q = msg.length % 136 →
        stateAt t'.mem L.ST = absorb 136 (pad 136 Spec.Sha3.shakeSuffix msg)) := by
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Message.setArgs_ok _ hok t (hc.xOk hL)) fun t1 ⟨hA, o⟩ => ?_)
  have hc1 : VG.Proof.MlDsa.Arm.Message.Ctx L g m₀ t1 := hc.regs o.rd o.wr o.sp o.mem fun r hr hl => o.gpr r (by simp only [List.map_cons, List.map_nil]; exact VG.Proof.MlDsa.Arm.Message.not_pres hr hl _)
  have e2 := hA (.r2, pos) (by simp)
  have e0 := hA (.r0, .off oST) (by simp)
  have e1 := hA (.r1, .imm 136) (by simp)
  have e3 := hA (.r3, .imm 0x1f) (by simp)
  have e4 := hA (.lr, .off oKS) (by simp)
  simp only [Arg.val, hc.r7, oST, oKS, VG.Proof.MlDsa.Arm.Message.x0'] at e0 e1 e3 e4
  rw [hq] at e2
  have hs1 : t1.sp = L.SP := hc1.sp
  have bs := VG.Proof.MlDsa.Arm.Message.below_stk hs1
  have hks := VG.Proof.MlDsa.Arm.Message.ks_eq hL
  refine pad_ok (st := L.X32) (scr := L.X32 + BitVec.ofNat 32 200) (rate := 136) (pos := q)
    ⟨e0, e1, e2, e3, e4, by decide, hql, by rw [hs1]; have := hL.nSP; omega,
      by have := hL.x32_lt; omega, by rw [VG.Proof.MlDsa.Arm.Message.x32_toNat hL (by omega)]; have := hL.x32_lt; omega,
      by simp only [VG.Proof.MlKem.Arm.regA, hks]; exact VG.Proof.MlDsa.Arm.Message.st_ks,
      by simp only [VG.Proof.MlKem.Arm.regA]; exact (VG.Proof.MlDsa.Arm.Message.k_st hL).sub_left bs, by simp only [VG.Proof.MlKem.Arm.regA, hks]; exact (VG.Proof.MlDsa.Arm.Message.k_ks hL).sub_left bs,
      ?_⟩ fun s' hk hpost => ?_
  · simp only [VG.Proof.MlKem.Arm.regA, hks, hc1.wr]
    refine VG.Proof.MlDsa.Arm.Message.covers_of_within fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact VG.Proof.MlDsa.Arm.Message.cov_xw0 hL
    · exact hL.covX (e := 200) (by omega)
  · simp only [VG.Proof.MlKem.Arm.regA, hks] at hk hpost
    refine ⟨hc1.kept hL hk fun r hr => ?_, ?_, fun msg hm hp => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [.inl VG.Proof.MlDsa.Arm.Message.w_st, .inl VG.Proof.MlDsa.Arm.Message.w_ks, .inr bs]
    · rw [← o.mem]
      exact hk.frame.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
        · exact ⟨_, by simp, bs⟩
    · rw [hpost msg (by rw [o.mem]; exact hm) hp]
      rfl

/-! ## Squeezing -/

/-- The arguments of a call of `vg_keccak_squeeze`. -/
abbrev sqzArgs : List (Reg × VG.Impl.MlDsa.Arm.Message.Arg) :=
  [(.r0, .off oST), (.r1, .imm 136), (.r2, .imm 0), (.r3, .off oMU), (.r12, .imm 64), (.lr, .off oKS)]

theorem ksqz_ok (hL : L.Ok) {t : State} (hc : VG.Proof.MlDsa.Arm.Message.Ctx L g m₀ t) :
    WP isa VG.Impl.MlDsa.Arm.Message.ksqz t fun t' => VG.Proof.MlDsa.Arm.Message.Ctx L g m₀ t' ∧
      Frame [⟨L.ST, 200⟩, ⟨L.MU, 64⟩, ⟨L.KS, 640⟩, L.STK] t.mem t'.mem ∧
      bytesAt t'.mem L.MU 64 = squeezeFrom 136 (stateAt t.mem L.ST) 0 64 := by
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Message.setArgs_ok VG.Proof.MlDsa.Arm.Message.sqzArgs (by decide) t (hc.xOk hL)) fun t1 ⟨hA, o⟩ => ?_)
  have hc1 : VG.Proof.MlDsa.Arm.Message.Ctx L g m₀ t1 := hc.regs o.rd o.wr o.sp o.mem fun r hr hl => o.gpr r (by simp only [List.map_cons, List.map_nil]; exact VG.Proof.MlDsa.Arm.Message.not_pres hr hl _)
  have e0 := hA (.r0, .off oST) (by simp)
  have e1 := hA (.r1, .imm 136) (by simp)
  have e2 := hA (.r2, .imm 0) (by simp)
  have e3 := hA (.r3, .off oMU) (by simp)
  have e4 := hA (.r12, .imm 64) (by simp)
  have e5 := hA (.lr, .off oKS) (by simp)
  simp only [Arg.val, hc.r7, oST, oKS, oMU, VG.Proof.MlDsa.Arm.Message.x0'] at e0 e1 e2 e3 e4 e5
  have hs1 : t1.sp = L.SP := hc1.sp
  have bs := VG.Proof.MlDsa.Arm.Message.below_stk hs1
  have hks := VG.Proof.MlDsa.Arm.Message.ks_eq hL
  have hmu := VG.Proof.MlDsa.Arm.Message.mu_eq hL
  refine squeeze_ok (st := L.X32) (scr := L.X32 + BitVec.ofNat 32 200) (out := L.X32 + BitVec.ofNat 32 840)
    (rate := 136) (pos := 0) (len := 64)
    ⟨e0, e1, e2, e3, e4, e5, by decide, by decide, by decide, by rw [hs1]; have := hL.nSP; omega,
      by have := hL.x32_lt; omega, by rw [VG.Proof.MlDsa.Arm.Message.x32_toNat hL (by omega)]; have := hL.x32_lt; omega,
      by rw [VG.Proof.MlDsa.Arm.Message.x32_toNat hL (by omega)]; have := hL.x32_lt; omega,
      by simp only [VG.Proof.MlKem.Arm.regA, hmu]; exact VG.Proof.MlDsa.Arm.Message.st_mu, by simp only [VG.Proof.MlKem.Arm.regA, hks]; exact VG.Proof.MlDsa.Arm.Message.st_ks,
      by simp only [VG.Proof.MlKem.Arm.regA, hks, hmu]; exact VG.Proof.MlDsa.Arm.Message.mu_ks,
      by simp only [VG.Proof.MlKem.Arm.regA]; exact (VG.Proof.MlDsa.Arm.Message.k_st hL).sub_left bs, by simp only [VG.Proof.MlKem.Arm.regA, hmu]; exact (VG.Proof.MlDsa.Arm.Message.k_mu hL).sub_left bs,
      by simp only [VG.Proof.MlKem.Arm.regA, hks]; exact (VG.Proof.MlDsa.Arm.Message.k_ks hL).sub_left bs, ?_⟩ fun s' hk hout _ _ => ?_
  · simp only [VG.Proof.MlKem.Arm.regA, hks, hmu, hc1.wr]
    refine VG.Proof.MlDsa.Arm.Message.covers_of_within fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact VG.Proof.MlDsa.Arm.Message.cov_xw0 hL
    · exact hL.covX (e := 840) (by omega)
    · exact hL.covX (e := 200) (by omega)
  · simp only [VG.Proof.MlKem.Arm.regA, hks, hmu] at hk hout
    refine ⟨hc1.kept hL hk fun r hr => ?_, ?_, by rw [hout, o.mem]⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [.inl VG.Proof.MlDsa.Arm.Message.w_st, .inl VG.Proof.MlDsa.Arm.Message.w_mu, .inl VG.Proof.MlDsa.Arm.Message.w_ks, .inr bs]
    · rw [← o.mem]
      exact hk.frame.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
        · exact ⟨_, by simp, fun _ h => h⟩
        · exact ⟨_, by simp, fun _ h => h⟩
        · exact ⟨_, by simp, bs⟩

end

end VG.Proof.MlDsa.Arm.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Message.HashMu`. -/
section

/-!
# ML-DSA on ARMv7, `sign_message` and `verify_message`: `μ` and `tr`

Untrusted: everything here is checked by Lean. In `Ctx`, `muHash` leaves
`μ = H(tr ‖ 0 ‖ ctx_len ‖ ctx ‖ M, 64)` at `X + 840` (`muHash_ok`), and
`trHash` leaves `H(pk, 64)` there (`trHash_ok`): from the zeroed state, each
absorb continues the message from the position the previous one returned.
-/

namespace VG.Proof.MlDsa.Arm.Message

open VG VG.Arm VG.Impl.MlDsa.Arm.Message
open VG.Proof.MlDsa.Message
open VG.Spec.Sha3 (bytesAt stateAt Repr)
open VG.Spec.MlDsa (Params)

section
variable {L : VG.Proof.MlDsa.Arm.Message.Lay} {g : Reg → BitVec 32} {m₀ : Mem}

/-- The two bytes `0 ‖ ctx_len` of the formatted message. -/
abbrev hdrBytes (L : VG.Proof.MlDsa.Arm.Message.Lay) : List Byte := [0, BitVec.ofNat 8 L.ctxLen.toNat]

theorem ofNat_toNat32 (x : BitVec 32) : BitVec.ofNat 32 x.toNat = x := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt]

theorem ofNat_toNat_eq32 {x : BitVec 32} {n : Nat} (h : x.toNat = n) : x = BitVec.ofNat 32 n := by
  subst h; exact (VG.Proof.MlDsa.Arm.Message.ofNat_toNat32 x).symm

/-- The arguments of an absorb are fit, if its data and length are not `r0`. -/
theorem absOk {src len pos : VG.Impl.MlDsa.Arm.Message.Arg} (h1 : src.ok = true) (h2 : len.ok = true) (h3 : pos.ok = true)
    (r1 : src.isRet = false) (r2 : len.isRet = false) : VG.Proof.MlDsa.Arm.Message.argsOk (VG.Proof.MlDsa.Arm.Message.absArgs src len pos) = true := by
  simp (config := { decide := true }) [VG.Proof.MlDsa.Arm.Message.argsOk, h1, h2, h3, r1, r2]

theorem padOk {pos : VG.Impl.MlDsa.Arm.Message.Arg} (h : pos.ok = true) : VG.Proof.MlDsa.Arm.Message.argsOk (VG.Proof.MlDsa.Arm.Message.padArgs pos) = true := by
  simp (config := { decide := true }) [VG.Proof.MlDsa.Arm.Message.argsOk, h]

theorem Ctx.hdrX {t : State} (hc : VG.Proof.MlDsa.Arm.Message.Ctx L g m₀ t) : bytesAt t.mem (L.X + BitVec.ofNat 64 944) 2 = VG.Proof.MlDsa.Arm.Message.hdrBytes L :=
  hc.hdr

theorem muHash_ok (hL : L.Ok) {t : State} (hc : VG.Proof.MlDsa.Arm.Message.Ctx L g m₀ t)
    {tr : VG.Impl.MlDsa.Arm.Message.Arg} (hok : tr.ok = true) (hret : tr.isRet = false) {trp : BitVec 32}
    (htr : ∀ t', VG.Proof.MlDsa.Arm.Message.Ctx L g m₀ t' → tr.val t' = trp) (hfit : trp.toNat + 64 ≤ 2 ^ 32)
    (hin : ∃ R ∈ L.rd ++ L.wr, Within ⟨State.addr trp, 64⟩ R)
    (dS : Region.Disjoint ⟨State.addr trp, 64⟩ ⟨L.ST, 200⟩) (dK : Region.Disjoint ⟨State.addr trp, 64⟩ ⟨L.KS, 640⟩)
    (kD : L.STK.Disjoint ⟨State.addr trp, 64⟩) :
    WP isa (muHash tr) t fun t' => VG.Proof.MlDsa.Arm.Message.Ctx L g m₀ t' ∧
      bytesAt t'.mem L.MU 64 = Spec.MlDsa.H (bytesAt t.mem (State.addr trp) 64 ++ VG.Proof.MlDsa.Arm.Message.hdrBytes L ++
        bytesAt m₀ (State.addr L.ctx) L.ctxLen.toNat ++ bytesAt m₀ (State.addr L.msg) L.len.toNat) 64 := by
  have hctx := hL.ctxLt
  -- Zero the state.
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Message.zeroSt_ok hL hc) fun t1 ⟨hc1, hf1, hz⟩ => ?_)
  have etr : bytesAt t1.mem (State.addr trp) 64 = bytesAt t.mem (State.addr trp) 64 :=
    Proof.MlKem.bytesAt_congr fun i hi =>
      hf1.bytes (R := ⟨State.addr trp, 64⟩) (by simpa using dS) (by show 64 ≤ 2 ^ 64; decide) hi
  have hR1 : Repr t1.mem L.ST 136 [] := Proof.MlKem.repr_nil hz
  -- `tr`.
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Message.kabs_ok hL hc1 (VG.Proof.MlDsa.Arm.Message.absOk hok rfl rfl hret rfl) (htr t1 hc1) rfl rfl (by decide)
    (by decide) hfit hin dS dK kD) fun t2 ⟨hc2, _, hR2, _⟩ => ?_)
  have hR2 := hR2 [] hR1 rfl
  rw [List.nil_append, etr] at hR2
  -- `0 ‖ ctx_len`.
  have fS : Region.Disjoint ⟨L.X + BitVec.ofNat 64 944, 2⟩ ⟨L.ST, 200⟩ := by
    have := Offset.disjoint L.X (d := 944) (n := 2) (e := 0) (k := 200) (by omega) (by omega) (by omega)
    simpa only [VG.Proof.MlDsa.Arm.Message.x0] using this
  have fK : Region.Disjoint ⟨L.X + BitVec.ofNat 64 944, 2⟩ ⟨L.KS, 640⟩ :=
    Offset.disjoint L.X (d := 944) (n := 2) (e := 200) (k := 640) (by omega) (by omega) (by omega)
  have ehd : State.addr (L.X32 + BitVec.ofNat 32 944) = L.X + BitVec.ofNat 64 944 := hL.xo (by decide)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Message.kabs_ok hL hc2 (dp := L.X32 + BitVec.ofNat 32 944) (VG.Proof.MlDsa.Arm.Message.absOk rfl rfl rfl rfl rfl)
    (by rw [hc2.off]; rfl) rfl rfl (by decide) (by decide) (by rw [VG.Proof.MlDsa.Arm.Message.x32_toNat hL (by decide)]; have := hL.x32_lt; omega)
    (by rw [ehd]; exact VG.Proof.MlDsa.Arm.Message.cov_x hL (e := 944) (k := 2) (by omega)) (by rw [ehd]; exact fS) (by rw [ehd]; exact fK)
    (by rw [ehd]; exact hL.stk_x (by omega)))
    fun t3 ⟨hc3, _, hR3, _⟩ => ?_)
  have hR3 := hR3 _ hR2 (by rw [Proof.MlKem.bytesAt_length])
  rw [ehd, hc2.hdrX] at hR3
  -- The context string.
  have hcl : (Arg.slot fCtxLen).val t3 = BitVec.ofNat 32 L.ctxLen.toNat := by
    rw [hc3.slotV hL (f := fCtxLen) (j := 4) rfl (by omega), VG.Proof.MlDsa.Arm.Message.ofNat_toNat32]; rfl
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Message.kabs_ok hL hc3 (VG.Proof.MlDsa.Arm.Message.absOk rfl rfl rfl rfl rfl)
    (by rw [hc3.slotV hL (f := fCtx) (j := 3) rfl (by omega)]; rfl) hcl rfl (by decide) (by omega) hL.nCtx
    ⟨L.CTX, List.mem_append_left _ hL.inCtx, within_self _⟩
    (by have := hL.x_r hL.xCtx (e := 0) (k := 200) (by omega); simpa only [VG.Proof.MlDsa.Arm.Message.x0] using this.symm)
    (hL.x_r hL.xCtx (e := 200) (k := 640) (by omega)).symm hL.kCtx)
    fun t4 ⟨hc4, _, hR4, hx4⟩ => ?_)
  have hR4 := hR4 _ hR3 (by simp only [List.length_append, Proof.MlKem.bytesAt_length, List.length_cons, List.length_nil])
  rw [hc3.bytesAt_eq hL.xCtx hL.kCtx (by have := hL.nCtx; omega)] at hR4
  -- The message.
  have hln : (Arg.slot fLen).val t4 = BitVec.ofNat 32 L.len.toNat := by
    rw [hc4.slotV hL (f := fLen) (j := 2) rfl (by omega), VG.Proof.MlDsa.Arm.Message.ofNat_toNat32]; rfl
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Message.kabs_ok hL hc4 (VG.Proof.MlDsa.Arm.Message.absOk rfl rfl rfl rfl rfl)
    (by rw [hc4.slotV hL (f := fMsg) (j := 1) rfl (by omega)]; rfl) hln (VG.Proof.MlDsa.Arm.Message.ofNat_toNat_eq32 hx4)
    (Nat.mod_lt _ (by decide)) L.len.isLt hL.nMsg ⟨L.MSG, List.mem_append_left _ hL.inMsg, within_self _⟩
    (by have := hL.x_r hL.xMsg (e := 0) (k := 200) (by omega); simpa only [VG.Proof.MlDsa.Arm.Message.x0] using this.symm)
    (hL.x_r hL.xMsg (e := 200) (k := 640) (by omega)).symm hL.kMsg)
    fun t5 ⟨hc5, _, hR5, hx5⟩ => ?_)
  have hR5 := hR5 _ hR4 (by simp only [List.length_append, Proof.MlKem.bytesAt_length, List.length_cons, List.length_nil])
  rw [hc4.bytesAt_eq hL.xMsg hL.kMsg (by have := hL.nMsg; omega)] at hR5
  -- Pad and squeeze.
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Message.kpad_ok hL hc5 (VG.Proof.MlDsa.Arm.Message.padOk rfl) (VG.Proof.MlDsa.Arm.Message.ofNat_toNat_eq32 hx5) (Nat.mod_lt _ (by decide)))
    fun t6 ⟨hc6, _, hS6⟩ => ?_)
  have hS6 := hS6 _ hR5 (by simp only [List.length_append, Proof.MlKem.bytesAt_length, List.length_cons, List.length_nil]; omega)
  refine WP.mono (VG.Proof.MlDsa.Arm.Message.ksqz_ok hL hc6) fun t7 ⟨hc7, _, hm7⟩ => ⟨hc7, ?_⟩
  rw [hm7, hS6, Spec.MlDsa.H, Proof.MlKem.shake256_eq]

/-! ## `tr = H(pk, 64)` -/

theorem trHash_ok {p : Params} (hL : L.Ok) (hk : L.keyLen = p.pkLen)
    {t : State} (hc : VG.Proof.MlDsa.Arm.Message.Ctx L g m₀ t) :
    WP isa (VG.Impl.MlDsa.Arm.Message.trHash p) t fun t' => VG.Proof.MlDsa.Arm.Message.Ctx L g m₀ t' ∧
      bytesAt t'.mem L.MU 64 = Spec.MlDsa.H (bytesAt m₀ (State.addr L.key) L.keyLen) 64 := by
  have hkl := hL.hKey.2
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Message.zeroSt_ok hL hc) fun t1 ⟨hc1, _, hz⟩ => ?_)
  have hR1 : Repr t1.mem L.ST 136 [] := Proof.MlKem.repr_nil hz
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Message.kabs_ok hL hc1 (n := L.keyLen) (q := 0)
    (VG.Proof.MlDsa.Arm.Message.absOk rfl (by simp only [Arg.ok, decide_eq_true_eq]; omega) rfl rfl rfl)
    (by rw [hc1.slotV hL (f := fKey) (j := 0) rfl (by omega)]; rfl) (by rw [hk]; rfl) rfl (by decide) (by omega)
    hL.nKey ⟨L.KEY, List.mem_append_left _ hL.inKey, within_self _⟩
    (by have := hL.x_r hL.xKey (e := 0) (k := 200) (by omega); simpa only [VG.Proof.MlDsa.Arm.Message.x0] using this.symm)
    (hL.x_r hL.xKey (e := 200) (k := 640) (by omega)).symm hL.kKey)
    fun t2 ⟨hc2, _, hR2, _⟩ => ?_)
  have hR2 := hR2 [] hR1 rfl
  rw [List.nil_append, hc1.bytesAt_eq hL.xKey hL.kKey (by have := hL.nKey; omega)] at hR2
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Message.kpad_ok hL hc2 (VG.Proof.MlDsa.Arm.Message.padOk (by simp only [Arg.ok, decide_eq_true_eq]; omega))
    (q := p.pkLen % 136) rfl (Nat.mod_lt _ (by decide))) fun t3 ⟨hc3, _, hS3⟩ => ?_)
  have hS3 := hS3 _ hR2 (by rw [Proof.MlKem.bytesAt_length, hk])
  refine WP.mono (VG.Proof.MlDsa.Arm.Message.ksqz_ok hL hc3) fun t4 ⟨hc4, _, hm4⟩ => ⟨hc4, ?_⟩
  rw [hm4, hS3, Spec.MlDsa.H, Proof.MlKem.shake256_eq]

end

end VG.Proof.MlDsa.Arm.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Message.Entry`. -/
section

/-!
# ML-DSA on ARMv7, `sign_message` and `verify_message`: entry and exit

Untrusted: everything here is checked by Lean. Stores of registers at
distinct offsets that are multiples of 4 from a base (`strs_ok`), and loads
of words on the stack into distinct registers (`lds_ok`). The entry: the
caller's `r7` kept in the first word of `scratch`, the address of `X` in
`r7`, the caller's `r7` and `lr` saved at `X + 904` and `X + 908`, the
arguments at `X + 912 + 4j` and `0 ‖ ctx_len` at `X + 944`, give `Ctx`
(`enter_ok`). The exit restores `lr` and `r7` (`leave_ok`).
-/

namespace VG.Proof.MlDsa.Arm.Message

open VG VG.Arm VG.Impl.MlDsa.Arm.Message
open VG.Proof.MlDsa.Message
open VG.Spec.Sha3 (bytesAt)

/-- Registers, permissions and stack pointer unchanged. -/
structure Same (t t' : State) : Prop where
  gpr : t'.gpr = t.gpr
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  sp : t'.sp = t.sp

theorem Same.refl (t : State) : VG.Proof.MlDsa.Arm.Message.Same t t := ⟨rfl, rfl, rfl, rfl⟩

theorem Same.trans {a b c : State} (h₁ : VG.Proof.MlDsa.Arm.Message.Same a b) (h₂ : VG.Proof.MlDsa.Arm.Message.Same b c) : VG.Proof.MlDsa.Arm.Message.Same a c :=
  ⟨h₂.gpr.trans h₁.gpr, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp⟩

theorem Same.of_memTo {a b : State} {m : Mem} (h : VG.Proof.MlDsa.Arm.Message.MemTo a b m) : VG.Proof.MlDsa.Arm.Message.Same a b := ⟨h.gpr, h.rd, h.wr, h.sp⟩

/-- Stores of registers at distinct offsets, multiples of 4, from `B` in `b`. -/
theorem strs_ok (b : Reg) (B : BitVec 32) (XB : Addr)
    (hB : ∀ o, o + 4 ≤ 1024 → State.addr (B + BitVec.ofNat 32 o) = XB + BitVec.ofNat 64 o) :
    ∀ (as : List (Reg × Nat)) (t : State), t.gpr b = B →
    (∀ a ∈ as, a.2 % 4 = 0 ∧ a.2 + 4 ≤ 1024 ∧ InRegions t.wr (XB + BitVec.ofNat 64 a.2) 4) →
    (as.map (·.2)).Nodup →
    WP isa (.block (as.map fun a => .str a.1 b a.2)) t fun t' => VG.Proof.MlDsa.Arm.Message.Same t t' ∧
      (∀ a ∈ as, t'.mem.readW (XB + BitVec.ofNat 64 a.2) 32 = t.gpr a.1) ∧
      Frame (as.map fun a => ⟨XB + BitVec.ofNat 64 a.2, 4⟩) t.mem t'.mem
  | [], t, _, _, _ => VG.Proof.MlDsa.Arm.Message.wp_nil ⟨Same.refl t, fun _ h => by simp at h, Frame.refl _ _⟩
  | (r, f) :: as, t, hb, ha, hn => by
    have h0 := ha (r, f) (List.mem_cons_self ..)
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    have ea : State.addr (t.gpr b + BitVec.ofNat 32 f) = XB + BitVec.ofNat 64 f := by rw [hb]; exact hB f h0.2.1
    refine VG.Proof.MlDsa.Arm.Message.wp_str (by omega) (by rw [ea]; exact h0.2.2) fun s1 m1 => ?_
    have hs1 := Same.of_memTo m1
    refine WP.mono (VG.Proof.MlDsa.Arm.Message.strs_ok b B XB hB as s1 (by rw [hs1.gpr, hb]) (fun a h => by
      rw [hs1.wr]; exact ha a (List.mem_cons_of_mem _ h)) hn.2) fun t' ⟨hs, hr, hf⟩ => ⟨hs1.trans hs, ?_, ?_⟩
    · intro a h
      rcases List.mem_cons.mp h with rfl | h
      · rw [hf.readW (r := ⟨XB + BitVec.ofNat 64 f, 4⟩) (Region.contains_self _ _) (fun r' hr' => by
            simp only [List.mem_map] at hr'
            obtain ⟨a', ha', rfl⟩ := hr'
            have := ha a' (List.mem_cons_of_mem _ ha')
            have hne : f ≠ a'.2 := fun e => hn.1 ⟨a', ha', e.symm⟩
            exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide),
          m1.mem, ea, Mem.readW_writeW_self32]
      · rw [hr a h, hs1.gpr]
    · have f1 : Frame [⟨XB + BitVec.ofNat 64 f, 4⟩] t.mem s1.mem := by
        rw [m1.mem, ea]
        exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
      refine (f1.mono fun r h => ?_).trans (hf.mono fun r h => ?_)
      · simp only [List.mem_singleton] at h; subst h; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ h

/-- Loads of words on the stack into distinct registers. -/
theorem lds_ok : ∀ (ss : List (Reg × Nat)) (t : State), (ss.map (·.1)).Nodup →
    (∀ a ∈ ss, a.2 < 4096 ∧ InRegions (t.rd ++ t.wr) (State.addr (t.sp + BitVec.ofNat 32 a.2)) 4) →
    WP isa (.block (ss.map fun a => .ldrSp a.1 a.2)) t fun t' => VG.Proof.MlDsa.Arm.Message.Only (ss.map (·.1)) t t' ∧
      ∀ a ∈ ss, t'.gpr a.1 = t.mem.readW (State.addr (t.sp + BitVec.ofNat 32 a.2)) 32
  | [], t, _, _ => VG.Proof.MlDsa.Arm.Message.wp_nil ⟨Only.refl _ _, fun _ h => by simp at h⟩
  | (r, o) :: ss, t, hn, ha => by
    have h0 := ha (r, o) (List.mem_cons_self ..)
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    refine VG.Proof.MlDsa.Arm.Message.wp_ldrSp h0.1 h0.2 fun s1 o1 e1 => ?_
    refine WP.mono (VG.Proof.MlDsa.Arm.Message.lds_ok ss s1 hn.2 fun a h => by
      rw [o1.rd, o1.wr, o1.sp]; exact ha a (List.mem_cons_of_mem _ h)) fun t' ⟨o, hv⟩ => ⟨?_, ?_⟩
    · exact (o1.mono fun x hx => by simp only [List.mem_singleton] at hx; simp [hx]).trans
        (o.mono fun x hx => by simp only [List.map_cons]; exact List.mem_cons_of_mem _ hx)
    · intro a h
      rcases List.mem_cons.mp h with rfl | h
      · rw [o.gpr _ (fun hm => by
          obtain ⟨x, hx', hx''⟩ := List.mem_map.mp hm
          exact hn.1 ⟨x, hx', hx''⟩), e1]
      · rw [hv a h, o1.mem, o1.sp]

theorem movi_val (v : Nat) :
    (BitVec.ofNat 16 (v / 65536) ++ ((BitVec.ofNat 16 v).setWidth 32).extractLsb' 0 16 : BitVec 32) =
      BitVec.ofNat 32 v := by
  have e1 : BitVec.ofNat 16 (v / 65536) = (BitVec.ofNat 32 v).extractLsb' 16 16 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega
  have e2 : BitVec.ofNat 16 v = (BitVec.ofNat 32 v).extractLsb' 0 16 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
    omega
  rw [e1, e2]; exact movw_movt _

theorem regSaves_ok : ∀ a ∈ regSaves, a.2 % 4 = 0 ∧ 904 ≤ a.2 ∧ a.2 + 4 ≤ 928 := by decide
theorem stkSaves_ok : ∀ a ∈ stkSaves, a.2 % 4 = 0 ∧ 928 ≤ a.2 ∧ a.2 + 4 ≤ 944 := by decide

/-- The entry, from a state whose registers and stack hold the layout's values. -/
theorem enter_ok {L : VG.Proof.MlDsa.Arm.Message.Lay} (hL : L.Ok) {p : Spec.MlDsa.Params} (hE : oE p = L.E) {so nA : Nat}
    {ss : List (Reg × Nat)} (hss : ss.map (·.1) = [.r0, .r1, .r2, .r3]) (hnA : nA ≤ 16) {s : State}
    (hsp : s.sp = L.SP) (hrd : s.rd = L.rd) (hwr : s.wr = L.wr)
    (h0 : s.gpr .r0 = L.key) (h1 : s.gpr .r1 = L.msg) (h2 : s.gpr .r2 = L.len) (h3 : s.gpr .r3 = L.ctx)
    (hA : ∀ o, o + 4 ≤ nA → InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 o)) 4)
    (hfA : s.sp.toNat + nA ≤ 2 ^ 32) (hdA : L.SC.Disjoint ⟨State.addr s.sp, nA⟩)
    (hso : so + 4 ≤ nA) (hscr : s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 so)) 32 = L.scr)
    (hsa : ∀ a ∈ ss, a.2 + 4 ≤ nA)
    (hv : ∀ j (hj : j < ss.length), s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 (ss[j]'hj).2)) 32 =
      L.vals.getD (4 + j) 0) :
    WP isa (.block (enter so p ss)) s fun t => VG.Proof.MlDsa.Arm.Message.Ctx L s.gpr s.mem t := by
  have hlen : ss.length = 4 := by rw [← List.length_map (f := (·.1)), hss]; rfl
  have hscL := hL.hE
  -- Words on the stack: in the arguments' region, apart from `scratch`.
  have estk : ∀ o, o + 4 ≤ nA → State.addr (s.sp + BitVec.ofNat 32 o) = State.addr s.sp + BitVec.ofNat 64 o :=
    fun o ho => addr_add (by omega)
  have dstk : ∀ o, o + 4 ≤ nA → L.SC.Disjoint ⟨State.addr (s.sp + BitVec.ofNat 32 o), 4⟩ := fun o ho => by
    rw [estk o ho]; exact hdA.sub_right (Offset.sub_base _ ho)
  have sc0 : State.addr (L.scr + BitVec.ofNat 32 0) = State.addr L.scr := by rw [BitVec.add_zero]
  have hsc4 : Region.Sub ⟨State.addr L.scr, 4⟩ L.SC := by
    have := Offset.sub_base (State.addr L.scr) (d := 0) (n := 4) (k := L.scrLen) (by omega)
    simpa only [BitVec.add_zero] using this
  have csc : L.SC.Contains (State.addr L.scr) 4 := by
    simpa using (Offset.contains_base (State.addr L.scr) (d := 0) (n := 4) (k := L.scrLen) (by omega) (by omega))
  have isc : InRegions L.wr (State.addr L.scr) 4 := ⟨L.SC, hL.inSC, csc⟩
  unfold enter
  simp only [List.append_assoc]
  -- `scratch` in `r12`, the caller's `r7` in its first word.
  refine VG.Proof.MlDsa.Arm.Message.wp_ldrSp (by omega) (hA so hso) fun s1 o1 e1 => ?_
  rw [hscr] at e1
  refine VG.Proof.MlDsa.Arm.Message.wp_str (by decide) (by rw [e1, sc0, o1.wr, hwr]; exact isc) fun s2 m2 => ?_
  have q2 := Same.of_memTo m2
  -- `X` in `r7`.
  refine VG.Proof.MlDsa.Arm.Message.wp_movw fun s3 o3 e3 => VG.Proof.MlDsa.Arm.Message.wp_movt fun s4 o4 e4 => VG.Proof.MlDsa.Arm.Message.wp_addReg fun s5 o5 e5 => ?_
  rw [o4.get .r12, o3.get .r12, q2.gpr, e1, e4, e3, VG.Proof.MlDsa.Arm.Message.movi_val, hE] at e5
  -- The caller's `r7` back in `r12`.
  have m5 : s5.mem = s1.mem.writeW (State.addr L.scr) (s.gpr .r7) := by
    rw [o5.mem, o4.mem, o3.mem, m2.mem, e1, sc0, o1.get .r7]
  have r12_5 : s5.gpr .r12 = L.scr := by rw [o5.get .r12, o4.get .r12, o3.get .r12, q2.gpr, e1]
  refine VG.Proof.MlDsa.Arm.Message.wp_ldr (by decide) (by
      rw [r12_5, sc0, o5.rd, o5.wr, o4.rd, o4.wr, o3.rd, o3.wr, q2.rd, q2.wr, o1.rd, o1.wr, hrd, hwr]
      exact ⟨L.SC, List.mem_append_right _ hL.inSC, csc⟩) fun s6 o6 e6 => ?_
  rw [r12_5, sc0, m5, Mem.readW_writeW_self32] at e6
  have e76 : s6.gpr .r7 = L.X32 := by rw [o6.get .r7, e5]
  have hw6 : s6.wr = L.wr := by rw [o6.wr, o5.wr, o4.wr, o3.wr, q2.wr, o1.wr, hwr]
  -- The registers.
  have g6 : ∀ r, r ≠ .r7 → r ≠ .r12 → s6.gpr r = s.gpr r := fun r h7 h12 => by
    rw [o6.get r (by simpa using h12), o5.get r (by simpa using h7), o4.get r (by simpa using h7),
      o3.get r (by simpa using h7), q2.gpr, o1.get r (by simpa using h12)]
  simp only [List.append_eq, List.nil_append]
  rw [WP.block_append_iff]
  have hxo : ∀ o, o + 4 ≤ 1024 → State.addr (L.X32 + BitVec.ofNat 32 o) = L.X + BitVec.ofNat 64 o :=
    fun o ho => hL.xo (by omega)
  refine WP.mono (VG.Proof.MlDsa.Arm.Message.strs_ok .r7 L.X32 L.X hxo regSaves s6 e76 (fun a ha => by
    have := VG.Proof.MlDsa.Arm.Message.regSaves_ok a ha; exact ⟨this.1, by omega, by rw [hw6]; exact hL.inW (by omega)⟩) (by decide))
    fun s7 ⟨q7, r7, f7⟩ => ?_
  rw [WP.block_append_iff]
  -- The arguments on the stack, unchanged since the entry.
  have m7 : ∀ o, o + 4 ≤ nA → s7.mem.readW (State.addr (s7.sp + BitVec.ofNat 32 o)) 32 =
      s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 o)) 32 := fun o ho => by
    have hs7 : s7.sp = s.sp := by rw [q7.sp, o6.sp, o5.sp, o4.sp, o3.sp, q2.sp, o1.sp]
    rw [hs7, f7.readW (r := ⟨State.addr (s.sp + BitVec.ofNat 32 o), 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_map] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      have := VG.Proof.MlDsa.Arm.Message.regSaves_ok a ha
      exact ((dstk o ho).sub_left (hL.sub_sc (e := a.2) (k := 4) (by omega))).symm) (by decide), o6.mem, m5,
      Mem.readW_writeW_sep (fun x h1 h2 => (dstk o ho).symm x h1 (hsc4 x h2)) (by decide), o1.mem]
  refine WP.mono (VG.Proof.MlDsa.Arm.Message.lds_ok ss s7 (by rw [hss]; decide) fun a ha => ⟨by have := hsa a ha; omega, by
    rw [q7.rd, q7.wr, q7.sp, o6.rd, o6.wr, o6.sp, o5.rd, o5.wr, o5.sp, o4.rd, o4.wr, o4.sp, o3.rd, o3.wr, o3.sp,
      q2.rd, q2.wr, q2.sp, o1.rd, o1.wr, o1.sp]; exact hA _ (hsa a ha)⟩) fun s8 ⟨o8, v8⟩ => ?_
  rw [hss] at o8
  -- The values loaded.
  have hl8 : ∀ j (hj : j < ss.length), s8.gpr (ss[j]'hj).1 = L.vals.getD (4 + j) 0 := fun j hj => by
    rw [v8 _ (List.getElem_mem hj), m7 _ (hsa _ (List.getElem_mem hj)), hv j hj]
  have hreg : ∀ j (hj : j < ss.length), (ss[j]'hj).1 = [Reg.r0, .r1, .r2, .r3].getD j .r0 := fun j hj => by
    have := congrArg (·[j]?) hss
    simp only [List.getElem?_map, List.getElem?_eq_getElem hj, Option.map_some] at this
    rw [List.getD_eq_getElem?_getD, ← this, Option.getD_some]
  have l8 : ∀ j < 4, s8.gpr ([Reg.r0, .r1, .r2, .r3].getD j .r0) = L.vals.getD (4 + j) 0 := fun j hj => by
    rw [← hreg j (by omega)]; exact hl8 j (by omega)
  have hw8 : s8.wr = L.wr := by rw [o8.wr, q7.wr, hw6]
  have e78 : s8.gpr .r7 = L.X32 := by rw [o8.get .r7, q7.gpr, e76]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.Arm.Message.strs_ok .r7 L.X32 L.X hxo stkSaves s8 e78 (fun a ha => by
    have := VG.Proof.MlDsa.Arm.Message.stkSaves_ok a ha; exact ⟨this.1, by omega, by rw [hw8]; exact hL.inW (by omega)⟩) (by decide))
    fun s9 ⟨q9, r9, f9⟩ => ?_
  -- `0 ‖ ctx_len`.
  have e79 : s9.gpr .r7 = L.X32 := by rw [q9.gpr, e78]
  simp only [oHdr, Nat.reduceAdd]
  refine VG.Proof.MlDsa.Arm.Message.wp_movImm (d := .r12) (v := 0) (by decide) fun s10 o10 e10 => ?_
  refine VG.Proof.MlDsa.Arm.Message.wp_strb (by decide) (by rw [o10.get .r7, e79, hxo 944 (by omega), o10.wr, q9.wr, hw8]; exact hL.inW (by omega))
    fun s11 m11 => ?_
  have q11 := Same.of_memTo m11
  refine VG.Proof.MlDsa.Arm.Message.wp_strb (by decide)
    (by rw [q11.gpr, o10.get .r7, e79, hxo 945 (by omega), q11.wr, o10.wr, q9.wr, hw8]; exact hL.inW (by omega))
    fun s12 m12 => VG.Proof.MlDsa.Arm.Message.wp_nil ?_
  have q12 := Same.of_memTo m12
  have x0_12 : s11.gpr .r0 = L.ctxLen := by
    rw [q11.gpr, o10.get .r0, q9.gpr]
    have := l8 0 (by omega); simpa [Lay.vals] using this
  have m12e : s12.mem = (s9.mem.writeW (L.X + BitVec.ofNat 64 944) ((0 : BitVec 32).setWidth 8)).writeW
      (L.X + BitVec.ofNat 64 945) (L.ctxLen.setWidth 8) := by
    rw [m12.mem, m11.mem, o10.mem, q11.gpr, o10.get .r7, e79, e10, hxo 944 (by omega), hxo 945 (by omega),
      ← q11.gpr, x0_12]
  -- Reads of the saves.
  have hdr2 : ∀ d, d + 4 ≤ 40 → s12.mem.readW (L.X + BitVec.ofNat 64 (904 + d)) 32 =
      s9.mem.readW (L.X + BitVec.ofNat 64 (904 + d)) 32 := fun d hd => by
    rw [m12e, Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
  have r9' : ∀ d, d + 4 ≤ 24 → s9.mem.readW (L.X + BitVec.ofNat 64 (904 + d)) 32 =
      s7.mem.readW (L.X + BitVec.ofNat 64 (904 + d)) 32 := fun d hd => by
    rw [f9.readW (r := ⟨L.X + BitVec.ofNat 64 (904 + d), 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_map] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      have := VG.Proof.MlDsa.Arm.Message.stkSaves_ok a ha
      exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide), o8.mem]
  have hX := hL.x_toNat
  refine ⟨by rw [q12.rd, q11.rd, o10.rd, q9.rd, o8.rd, q7.rd, o6.rd, o5.rd, o4.rd, o3.rd, q2.rd, o1.rd, hrd],
    by rw [q12.wr, q11.wr, o10.wr, q9.wr, hw8],
    by rw [q12.sp, q11.sp, o10.sp, q9.sp, o8.sp, q7.sp, o6.sp, o5.sp, o4.sp, o3.sp, q2.sp, o1.sp, hsp],
    by rw [q12.gpr, q11.gpr, o10.get .r7, e79], fun r hr h7 hl => ?_, ?_, ?_, fun j hj => ?_, ?_, ?_⟩
  · have hn : r ∉ [Reg.r0, .r1, .r2, .r3, .r12] := fun hm => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl <;> revert hr <;> decide
    rw [q12.gpr, q11.gpr, o10.get r (by simp at hn ⊢; exact hn.2.2.2.2), q9.gpr,
      o8.get r (by simp at hn ⊢; exact ⟨hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1⟩), q7.gpr,
      g6 r h7 (by simp at hn; exact hn.2.2.2.2)]
  · rw [hdr2 0 (by omega), r9' 0 (by omega)]; exact (r7 (.r12, oR7) (by decide)).trans e6
  · rw [hdr2 4 (by omega), r9' 4 (by omega)]
    exact (r7 (.lr, oLR) (by decide)).trans (g6 .lr (by decide) (by decide))
  · rw [hdr2 _ (by omega)]
    rcases (by omega : j < 4 ∨ 4 ≤ j) with hj4 | hj4
    · rw [r9' _ (by omega)]
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
      · refine (r7 (.r0, fKey) (by decide)).trans ?_; rw [g6 .r0 (by decide) (by decide), h0]; rfl
      · refine (r7 (.r1, fMsg) (by decide)).trans ?_; rw [g6 .r1 (by decide) (by decide), h1]; rfl
      · refine (r7 (.r2, fLen) (by decide)).trans ?_; rw [g6 .r2 (by decide) (by decide), h2]; rfl
      · refine (r7 (.r3, fCtx) (by decide)).trans ?_; rw [g6 .r3 (by decide) (by decide), h3]; rfl
    · obtain ⟨k, rfl⟩ : ∃ k, j = 4 + k := ⟨j - 4, by omega⟩
      have hk : k < 4 := by omega
      rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
      · exact (r9 (.r0, fCtxLen) (by decide)).trans (l8 0 (by omega))
      · exact (r9 (.r1, fRnd) (by decide)).trans (l8 1 (by omega))
      · exact (r9 (.r2, fSig) (by decide)).trans (l8 2 (by omega))
      · exact (r9 (.r3, fScr) (by decide)).trans (l8 3 (by omega))
  · have n45 : L.X + BitVec.ofNat 64 944 ≠ L.X + BitVec.ofNat 64 945 :=
      Offset.add_ofNat_ne _ (by omega) (by omega) (by omega)
    rw [show 904 + 40 = 944 from rfl, m12e]
    generalize L.X = X at n45 ⊢
    simp only [bytesAt, List.range, List.range.loop, List.map_cons, List.map_nil, add_add, Nat.reduceAdd]
    rw [byte_writeW_other _ n45, byte_writeW_self, byte_writeW_self]
    refine List.cons_eq_cons.mpr ⟨rfl, List.cons_eq_cons.mpr ⟨?_, rfl⟩⟩
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  · -- Memory changed only in `scratch`.
    have a2 : Frame [L.SC, L.STK] s.mem s5.mem := by
      rw [m5, o1.mem]
      exact (Frame.refl _ _).writeW (List.mem_cons_self ..) _ csc
    have a7 : Frame [L.SC, L.STK] s6.mem s7.mem := Frame.sub f7 fun r hr => by
      simp only [List.mem_map] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      have := VG.Proof.MlDsa.Arm.Message.regSaves_ok a ha
      exact ⟨L.SC, by simp, hL.sub_sc (by omega)⟩
    have a9 : Frame [L.SC, L.STK] s8.mem s9.mem := Frame.sub f9 fun r hr => by
      simp only [List.mem_map] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      have := VG.Proof.MlDsa.Arm.Message.stkSaves_ok a ha
      exact ⟨L.SC, by simp, hL.sub_sc (by omega)⟩
    have a12 : Frame [L.SC, L.STK] s9.mem s12.mem := by
      rw [m12e]
      exact ((Frame.refl _ _).writeW (List.mem_cons_self ..) _ (hL.sub_sc (e := 944) (k := 1) (by omega) _
          (Region.contains_self _ _))).writeW
        (List.mem_cons_self ..) _ (hL.sub_sc (e := 945) (k := 1) (by omega) _ (Region.contains_self _ _))
    rw [o6.mem] at a7
    rw [o8.mem] at a9
    exact a2.trans (a7.trans (a9.trans a12))

/-- What the exit needs: `r7` pointing at `X`, the callee-saved registers
but `r7` and `lr`, and the saves of those two. -/
structure Fin (L : VG.Proof.MlDsa.Arm.Message.Lay) (g : Reg → BitVec 32) (t : State) : Prop where
  rd : t.rd = L.rd
  wr : t.wr = L.wr
  sp : t.sp = L.SP
  r7 : t.gpr .r7 = L.X32
  cs : ∀ r ∈ preserved, r ≠ .r7 → r ≠ .lr → t.gpr r = g r
  s7 : t.mem.readW (L.X + BitVec.ofNat 64 (904 + 0)) 32 = g .r7
  sLR : t.mem.readW (L.X + BitVec.ofNat 64 (904 + 4)) 32 = g .lr

theorem Ctx.fin {L : VG.Proof.MlDsa.Arm.Message.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State} (hc : VG.Proof.MlDsa.Arm.Message.Ctx L g m₀ t) : VG.Proof.MlDsa.Arm.Message.Fin L g t :=
  ⟨hc.rd, hc.wr, hc.sp, hc.r7, hc.cs, hc.s7, hc.sLR⟩

/-- The exit: `lr`, then `r7`, from the saves. -/
theorem leave_ok {L : VG.Proof.MlDsa.Arm.Message.Lay} (hL : L.Ok) {g : Reg → BitVec 32} {t : State} (hc : VG.Proof.MlDsa.Arm.Message.Fin L g t) :
    WP isa (.block leave) t fun t' => (∀ r ∈ preserved, t'.gpr r = g r) ∧ t'.sp = L.SP ∧ t'.mem = t.mem ∧
      t'.gpr .r0 = t.gpr .r0 ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have hx : ∀ f, f + 4 ≤ 1024 → InRegions (t.rd ++ t.wr) (L.X + BitVec.ofNat 64 f) 4 := fun f hf => by
    obtain ⟨R, hR, hc'⟩ := hL.inW (e := f) (k := 4) hf
    exact ⟨R, by rw [hc.rd, hc.wr]; exact List.mem_append_right _ hR, hc'⟩
  refine VG.Proof.MlDsa.Arm.Message.wp_ldr (by decide) (by rw [hc.r7, hL.xo (by decide)]; exact hx 908 (by omega)) fun t1 o1 e1 => ?_
  refine VG.Proof.MlDsa.Arm.Message.wp_ldr (by decide) (by rw [o1.get .r7, hc.r7, hL.xo (by decide), o1.rd, o1.wr]; exact hx 904 (by omega))
    fun t2 o2 e2 => VG.Proof.MlDsa.Arm.Message.wp_nil ?_
  rw [hc.r7, hL.xo (by decide)] at e1
  rw [o1.get .r7, hc.r7, hL.xo (by decide), o1.mem] at e2
  refine ⟨fun r hr => ?_, by rw [o2.sp, o1.sp, hc.sp], by rw [o2.mem, o1.mem], by rw [o2.get .r0, o1.get .r0],
    by rw [o2.rd, o1.rd], by rw [o2.wr, o1.wr]⟩
  by_cases e7 : r = .r7
  · subst e7; rw [e2]; exact hc.s7
  · by_cases el : r = .lr
    · subst el; rw [o2.get .lr, e1]; exact hc.sLR
    · rw [o2.get r (by simpa using e7), o1.get r (by simpa using el), hc.cs r hr e7 el]

end VG.Proof.MlDsa.Arm.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Message.Pre`. -/
section

/-!
# ML-DSA on ARMv7, `sign_message` and `verify_message`: the preconditions and the layouts

Untrusted: everything here is checked by Lean. The preconditions of
`signMessageContract p Arm.abi 36` and `verifyMessageContract p Arm.abi
36`, spelled out (`SPre`, `VPre`), and the layouts of runs from states
satisfying them (`slay`, `vlay`).
-/

namespace VG.Proof.MlDsa.Arm.Message

open VG VG.Arm VG.Impl.MlDsa.Arm.Message
open VG.Proof.MlDsa.Message
open VG.Spec.MlDsa

/-- The parameter sets. -/
def params : List Params := [mlDsa44, mlDsa65, mlDsa87]

/-- The size of `scratch` in bytes. -/
abbrev mScrLen (p : Params) : Nat := messageScratchWords p * 8

theorem mScr_eq (p : Params) : VG.Proof.MlDsa.Arm.Message.mScrLen p = oE p + 1024 := by
  simp only [VG.Proof.MlDsa.Arm.Message.mScrLen, messageScratchWords, oE]; omega

theorem oE_lt {p : Params} (hp : p ∈ VG.Proof.MlDsa.Arm.Message.params) : oE p + 1024 < 2 ^ 31 := by
  simp only [VG.Proof.MlDsa.Arm.Message.params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> decide

theorem skLen_ge {p : Params} (hp : p ∈ VG.Proof.MlDsa.Arm.Message.params) : 128 ≤ p.skLen ∧ p.skLen < 2 ^ 16 := by
  simp only [VG.Proof.MlDsa.Arm.Message.params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> decide

theorem pkLen_ge {p : Params} (hp : p ∈ VG.Proof.MlDsa.Arm.Message.params) : 128 ≤ p.pkLen ∧ p.pkLen < 2 ^ 16 := by
  simp only [VG.Proof.MlDsa.Arm.Message.params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> decide

section
variable (s : State)

abbrev rKey (n : Nat) : Region := ⟨State.addr (s.gpr .r0), n⟩
abbrev rMsg : Region := ⟨State.addr (s.gpr .r1), (s.gpr .r2).toNat⟩
abbrev rCtx : Region := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩
/-- The `n` bytes below the stack pointer the calls use. -/
abbrev rStk : Region := ⟨State.addr s.sp - BitVec.ofNat 64 36, 36⟩
/-- The arguments on the stack. -/
abbrev rArgs (n : Nat) : Region := ⟨stackArgAddr s 0, n⟩
/-- The `j`-th argument on the stack, as an address. -/
abbrev sArg (j : Nat) : Addr := State.addr (stackArg s j)

end

theorem stackArgAddr0 (s : State) : stackArgAddr s 0 = State.addr s.sp := by
  simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]

/-! ## Signing -/

/-- The precondition of `signMessageContract p Arm.abi 36`. -/
structure SPre (p : Params) (s : State) : Prop where
  sp : 36 ≤ s.sp.toNat
  spA : s.sp.toNat + 16 ≤ 2 ^ 32
  rd : s.rd = [VG.Proof.MlDsa.Arm.Message.rKey s p.skLen, VG.Proof.MlDsa.Arm.Message.rMsg s, VG.Proof.MlDsa.Arm.Message.rCtx s, ⟨VG.Proof.MlDsa.Arm.Message.sArg s 1, 32⟩, VG.Proof.MlDsa.Arm.Message.rArgs s 16]
  wr : s.wr = [⟨VG.Proof.MlDsa.Arm.Message.sArg s 2, p.sigLen⟩, ⟨VG.Proof.MlDsa.Arm.Message.sArg s 3, VG.Proof.MlDsa.Arm.Message.mScrLen p⟩]
  skSig : (VG.Proof.MlDsa.Arm.Message.rKey s p.skLen).Disjoint ⟨VG.Proof.MlDsa.Arm.Message.sArg s 2, p.sigLen⟩
  skScr : (VG.Proof.MlDsa.Arm.Message.rKey s p.skLen).Disjoint ⟨VG.Proof.MlDsa.Arm.Message.sArg s 3, VG.Proof.MlDsa.Arm.Message.mScrLen p⟩
  msgSig : (VG.Proof.MlDsa.Arm.Message.rMsg s).Disjoint ⟨VG.Proof.MlDsa.Arm.Message.sArg s 2, p.sigLen⟩
  msgScr : (VG.Proof.MlDsa.Arm.Message.rMsg s).Disjoint ⟨VG.Proof.MlDsa.Arm.Message.sArg s 3, VG.Proof.MlDsa.Arm.Message.mScrLen p⟩
  ctxSig : (VG.Proof.MlDsa.Arm.Message.rCtx s).Disjoint ⟨VG.Proof.MlDsa.Arm.Message.sArg s 2, p.sigLen⟩
  ctxScr : (VG.Proof.MlDsa.Arm.Message.rCtx s).Disjoint ⟨VG.Proof.MlDsa.Arm.Message.sArg s 3, VG.Proof.MlDsa.Arm.Message.mScrLen p⟩
  rndSig : Region.Disjoint ⟨VG.Proof.MlDsa.Arm.Message.sArg s 1, 32⟩ ⟨VG.Proof.MlDsa.Arm.Message.sArg s 2, p.sigLen⟩
  rndScr : Region.Disjoint ⟨VG.Proof.MlDsa.Arm.Message.sArg s 1, 32⟩ ⟨VG.Proof.MlDsa.Arm.Message.sArg s 3, VG.Proof.MlDsa.Arm.Message.mScrLen p⟩
  sigScr : Region.Disjoint ⟨VG.Proof.MlDsa.Arm.Message.sArg s 2, p.sigLen⟩ ⟨VG.Proof.MlDsa.Arm.Message.sArg s 3, VG.Proof.MlDsa.Arm.Message.mScrLen p⟩
  sigArgs : Region.Disjoint ⟨VG.Proof.MlDsa.Arm.Message.sArg s 2, p.sigLen⟩ (VG.Proof.MlDsa.Arm.Message.rArgs s 16)
  scrArgs : Region.Disjoint ⟨VG.Proof.MlDsa.Arm.Message.sArg s 3, VG.Proof.MlDsa.Arm.Message.mScrLen p⟩ (VG.Proof.MlDsa.Arm.Message.rArgs s 16)
  stkSk : (VG.Proof.MlDsa.Arm.Message.rStk s).Disjoint (VG.Proof.MlDsa.Arm.Message.rKey s p.skLen)
  stkMsg : (VG.Proof.MlDsa.Arm.Message.rStk s).Disjoint (VG.Proof.MlDsa.Arm.Message.rMsg s)
  stkCtx : (VG.Proof.MlDsa.Arm.Message.rStk s).Disjoint (VG.Proof.MlDsa.Arm.Message.rCtx s)
  stkRnd : (VG.Proof.MlDsa.Arm.Message.rStk s).Disjoint ⟨VG.Proof.MlDsa.Arm.Message.sArg s 1, 32⟩
  stkSig : (VG.Proof.MlDsa.Arm.Message.rStk s).Disjoint ⟨VG.Proof.MlDsa.Arm.Message.sArg s 2, p.sigLen⟩
  stkScr : (VG.Proof.MlDsa.Arm.Message.rStk s).Disjoint ⟨VG.Proof.MlDsa.Arm.Message.sArg s 3, VG.Proof.MlDsa.Arm.Message.mScrLen p⟩
  stkArgs : (VG.Proof.MlDsa.Arm.Message.rStk s).Disjoint (VG.Proof.MlDsa.Arm.Message.rArgs s 16)
  nSk : (s.gpr .r0).toNat + p.skLen ≤ 2 ^ 32
  nMsg : (s.gpr .r1).toNat + (s.gpr .r2).toNat ≤ 2 ^ 32
  nCtx : (s.gpr .r3).toNat + (stackArg s 0).toNat ≤ 2 ^ 32
  nRnd : (stackArg s 1).toNat + 32 ≤ 2 ^ 32
  nSig : (stackArg s 2).toNat + p.sigLen ≤ 2 ^ 32
  nScr : (stackArg s 3).toNat + VG.Proof.MlDsa.Arm.Message.mScrLen p ≤ 2 ^ 32

theorem sPre_of {p : Params} {s : State} (h : (signMessageContract p Arm.abi 36).pre s) : VG.Proof.MlDsa.Arm.Message.SPre p s := by
  sig_pre [signMessageContract, signMessageSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨a1, a2, a3, a4, a5, h⟩ := h
  obtain ⟨a6, a7, a8, a9, a10, h⟩ := h
  obtain ⟨a11, a12, a13, a14, a15, h⟩ := h
  obtain ⟨a16, a17, a18, a19, a20, h⟩ := h
  obtain ⟨a21, a22, a23, a24, a25, h⟩ := h
  obtain ⟨a26, a27, a28⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22,
    a23, a24, a25, a26, a27, a28⟩

/-- The layout of a run of `sign_message` from `s`. -/
def slay (p : Params) (s : State) : VG.Proof.MlDsa.Arm.Message.Lay where
  SP := s.sp
  key := s.gpr .r0
  keyLen := p.skLen
  msg := s.gpr .r1
  len := s.gpr .r2
  ctx := s.gpr .r3
  ctxLen := stackArg s 0
  rnd := stackArg s 1
  sig := stackArg s 2
  scr := stackArg s 3
  scrLen := VG.Proof.MlDsa.Arm.Message.mScrLen p
  E := oE p
  rd := s.rd
  wr := s.wr

theorem slay_ok {p : Params} (hp : p ∈ VG.Proof.MlDsa.Arm.Message.params) {s : State} (h : VG.Proof.MlDsa.Arm.Message.SPre p s) (h8 : (stackArg s 0).toNat < 256) :
    (VG.Proof.MlDsa.Arm.Message.slay p s).Ok :=
  ⟨h8, by show oE p + 1024 ≤ VG.Proof.MlDsa.Arm.Message.mScrLen p; rw [VG.Proof.MlDsa.Arm.Message.mScr_eq], VG.Proof.MlDsa.Arm.Message.skLen_ge hp, h.sp, h.nScr, by simp [VG.Proof.MlDsa.Arm.Message.slay, h.wr], by simp [VG.Proof.MlDsa.Arm.Message.slay, h.rd],
    by simp [VG.Proof.MlDsa.Arm.Message.slay, h.rd], by simp [VG.Proof.MlDsa.Arm.Message.slay, h.rd], h.skScr.symm, h.msgScr.symm, h.ctxScr.symm, h.stkScr,
    h.stkSk, h.stkMsg, h.stkCtx, h.nSk, h.nMsg, h.nCtx⟩

/-! ## Verification -/

/-- The precondition of `verifyMessageContract p Arm.abi 36`. -/
structure VPre (p : Params) (s : State) : Prop where
  sp : 36 ≤ s.sp.toNat
  spA : s.sp.toNat + 12 ≤ 2 ^ 32
  rd : s.rd = [VG.Proof.MlDsa.Arm.Message.rKey s p.pkLen, VG.Proof.MlDsa.Arm.Message.rMsg s, VG.Proof.MlDsa.Arm.Message.rCtx s, ⟨VG.Proof.MlDsa.Arm.Message.sArg s 1, p.sigLen⟩, VG.Proof.MlDsa.Arm.Message.rArgs s 12]
  wr : s.wr = [⟨VG.Proof.MlDsa.Arm.Message.sArg s 2, VG.Proof.MlDsa.Arm.Message.mScrLen p⟩]
  pkScr : (VG.Proof.MlDsa.Arm.Message.rKey s p.pkLen).Disjoint ⟨VG.Proof.MlDsa.Arm.Message.sArg s 2, VG.Proof.MlDsa.Arm.Message.mScrLen p⟩
  msgScr : (VG.Proof.MlDsa.Arm.Message.rMsg s).Disjoint ⟨VG.Proof.MlDsa.Arm.Message.sArg s 2, VG.Proof.MlDsa.Arm.Message.mScrLen p⟩
  ctxScr : (VG.Proof.MlDsa.Arm.Message.rCtx s).Disjoint ⟨VG.Proof.MlDsa.Arm.Message.sArg s 2, VG.Proof.MlDsa.Arm.Message.mScrLen p⟩
  sigScr : Region.Disjoint ⟨VG.Proof.MlDsa.Arm.Message.sArg s 1, p.sigLen⟩ ⟨VG.Proof.MlDsa.Arm.Message.sArg s 2, VG.Proof.MlDsa.Arm.Message.mScrLen p⟩
  scrArgs : Region.Disjoint ⟨VG.Proof.MlDsa.Arm.Message.sArg s 2, VG.Proof.MlDsa.Arm.Message.mScrLen p⟩ (VG.Proof.MlDsa.Arm.Message.rArgs s 12)
  stkPk : (VG.Proof.MlDsa.Arm.Message.rStk s).Disjoint (VG.Proof.MlDsa.Arm.Message.rKey s p.pkLen)
  stkMsg : (VG.Proof.MlDsa.Arm.Message.rStk s).Disjoint (VG.Proof.MlDsa.Arm.Message.rMsg s)
  stkCtx : (VG.Proof.MlDsa.Arm.Message.rStk s).Disjoint (VG.Proof.MlDsa.Arm.Message.rCtx s)
  stkSig : (VG.Proof.MlDsa.Arm.Message.rStk s).Disjoint ⟨VG.Proof.MlDsa.Arm.Message.sArg s 1, p.sigLen⟩
  stkScr : (VG.Proof.MlDsa.Arm.Message.rStk s).Disjoint ⟨VG.Proof.MlDsa.Arm.Message.sArg s 2, VG.Proof.MlDsa.Arm.Message.mScrLen p⟩
  stkArgs : (VG.Proof.MlDsa.Arm.Message.rStk s).Disjoint (VG.Proof.MlDsa.Arm.Message.rArgs s 12)
  nPk : (s.gpr .r0).toNat + p.pkLen ≤ 2 ^ 32
  nMsg : (s.gpr .r1).toNat + (s.gpr .r2).toNat ≤ 2 ^ 32
  nCtx : (s.gpr .r3).toNat + (stackArg s 0).toNat ≤ 2 ^ 32
  nSig : (stackArg s 1).toNat + p.sigLen ≤ 2 ^ 32
  nScr : (stackArg s 2).toNat + VG.Proof.MlDsa.Arm.Message.mScrLen p ≤ 2 ^ 32

theorem vPre_of {p : Params} {s : State} (h : (verifyMessageContract p Arm.abi 36).pre s) : VG.Proof.MlDsa.Arm.Message.VPre p s := by
  sig_pre [verifyMessageContract, verifyMessageSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨a1, a2, a3, a4, a5, h⟩ := h
  obtain ⟨a6, a7, a8, a9, a10, h⟩ := h
  obtain ⟨a11, a12, a13, a14, a15, h⟩ := h
  obtain ⟨a16, a17, a18, a19, a20⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20⟩

/-- The layout of a run of `verify_message` from `s` (`sig` in the slot of `rnd` too). -/
def vlay (p : Params) (s : State) : VG.Proof.MlDsa.Arm.Message.Lay where
  SP := s.sp
  key := s.gpr .r0
  keyLen := p.pkLen
  msg := s.gpr .r1
  len := s.gpr .r2
  ctx := s.gpr .r3
  ctxLen := stackArg s 0
  rnd := stackArg s 1
  sig := stackArg s 1
  scr := stackArg s 2
  scrLen := VG.Proof.MlDsa.Arm.Message.mScrLen p
  E := oE p
  rd := s.rd
  wr := s.wr

theorem vlay_ok {p : Params} (hp : p ∈ VG.Proof.MlDsa.Arm.Message.params) {s : State} (h : VG.Proof.MlDsa.Arm.Message.VPre p s) (h8 : (stackArg s 0).toNat < 256) :
    (VG.Proof.MlDsa.Arm.Message.vlay p s).Ok :=
  ⟨h8, by show oE p + 1024 ≤ VG.Proof.MlDsa.Arm.Message.mScrLen p; rw [VG.Proof.MlDsa.Arm.Message.mScr_eq], VG.Proof.MlDsa.Arm.Message.pkLen_ge hp, h.sp, h.nScr, by simp [VG.Proof.MlDsa.Arm.Message.vlay, h.wr], by simp [VG.Proof.MlDsa.Arm.Message.vlay, h.rd],
    by simp [VG.Proof.MlDsa.Arm.Message.vlay, h.rd], by simp [VG.Proof.MlDsa.Arm.Message.vlay, h.rd], h.pkScr.symm, h.msgScr.symm, h.ctxScr.symm, h.stkScr,
    h.stkPk, h.stkMsg, h.stkCtx, h.nPk, h.nMsg, h.nCtx⟩

end VG.Proof.MlDsa.Arm.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Message.SignCall`. -/
section

/-!
# ML-DSA on ARMv7, `sign_message`: the call of the signing function on `μ`

Untrusted: everything here is checked by Lean. A call of verified code with
frames of its own, in a frame that pushes its fifth argument (`r12`) and
`lr` (`frameCall_ok`, as `callS_ok` of the signing function on `μ`, after
the moves of the arguments). Any code verified against `signContract p
Arm.abi 28` whose frames use at most 28 bytes of stack (`SignFn`): its call
on the key, `μ` at `X + 840`, `rnd`, `sig` and the first `scratchWords p`
words of `scratch` (`signCall_ok`), after which the saves are intact
(`Fin`).
-/

namespace VG.Proof.MlDsa.Arm.Message

open VG VG.Arm VG.Impl.MlDsa.Arm.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.Arm (push2_frame push2_arg addr_sub view_gpr below)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- A signing function on `μ` that `sign_message` can call. -/
structure SignFn (p : Params) (c : Prog isa) : Prop where
  ver : Verified Arm.target c (signContract p Arm.abi 28)
  su : stackUse c ≤ 28

/-- The size of the working space of the functions on `μ`. -/
abbrev sScr (p : Params) : Nat := scratchWords p * 8

/-- The argument on the stack of a call in a frame: the word at the stack
pointer of the callee. -/
abbrev argR (s : State) : Region := ⟨State.addr s.sp - BitVec.ofNat 64 8, 4⟩

theorem frame8 {s : State} (hsp : 8 ≤ s.sp.toNat) :
    (⟨State.addr (s.sp - BitVec.ofNat 32 (4 * [Reg.r12, Reg.lr].length)), 4 * [Reg.r12, Reg.lr].length⟩ : Region) =
      belowA s.sp 8 := by
  simp only [belowA, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul]
  rw [VG.Proof.MlKem.Arm.addr_sub hsp]

theorem ne12_pres : ∀ r ∈ preserved, r ≠ .lr → r ≠ .r12 := by decide

theorem sp_sub8 {sp : BitVec 32} (h : 8 ≤ sp.toNat) : (sp - BitVec.ofNat 32 8).toNat = sp.toNat - 8 := by
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

/-- A call of verified code in a frame that pushes `r12` (its fifth
argument) and `lr`, from the state after the moves of its arguments. -/
theorem frameCall_ok {D : Nat} {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsu : 8 + stackUse c ≤ D) {s : State} (hsp : D ≤ s.sp.toNat) {rd wr : List Region}
    (hpre : k.pre ((pushed [.r12, .lr] s).callEntry.withRegions (rd ++ [VG.Proof.MlDsa.Arm.Message.argR s]) wr))
    (hc : Covers rd (s.rd ++ s.wr)) (hw : Covers wr s.wr) :
    WP isa (.frame (.push [.r12, .lr]) (.call n c) (.pop .r12 8)) s fun s' =>
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) ∧
      Frame (wr ++ [belowA s.sp D]) s.mem s'.mem ∧
      ∃ s₂ : State, s₂.mem = s'.mem ∧ (∀ r, r ≠ .r12 → s₂.gpr r = s'.gpr r) ∧
        k.post ((pushed [.r12, .lr] s).callEntry.withRegions (rd ++ [VG.Proof.MlDsa.Arm.Message.argR s]) wr)
          (s₂.withRegions (rd ++ [VG.Proof.MlDsa.Arm.Message.argR s]) wr) := by
  have h8 : 8 ≤ s.sp.toNat := by omega
  refine WP.frame (rs := [.r12, .lr]) (r := .r12) rfl (by simpa using h8) (by decide) ?_
  have hwp : (pushed [.r12, .lr] s).wr = belowA s.sp 8 :: s.wr := by rw [VG.Arm.pushed_wr, VG.Proof.MlDsa.Arm.Message.frame8 h8]
  refine WP.callF hv hpre (fun x m hx => ?_) (fun x m hx => ?_) ?_ fun s₂ hrd hwr hsp₂ hf hcs hpost => ?_
  · rw [VG.Arm.pushed_rd, hwp]
    rcases (by simpa only [InRegions, List.mem_append, or_assoc] using hx : ∃ r, (r ∈ rd ∨ r ∈ [argR s] ∨ r ∈ wr) ∧
      r.Contains x m) with ⟨r, (hr | hr | hr), hcr⟩
    · obtain ⟨r', hr', hc'⟩ := hc x m ⟨r, hr, hcr⟩
      rcases List.mem_append.mp hr' with h | h
      · exact ⟨r', List.mem_append_left _ h, hc'⟩
      · exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ h), hc'⟩
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_append_right _ (List.mem_cons_self ..), ?_⟩
      simp only [Region.Contains, belowA] at hcr ⊢; omega
    · obtain ⟨r', hr', hc'⟩ := hw x m ⟨r, hr, hcr⟩
      exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ hr'), hc'⟩
  · rw [hwp]
    obtain ⟨r', hr', hc'⟩ := hw x m hx
    exact ⟨r', List.mem_cons_of_mem _ hr', hc'⟩
  · rw [VG.Arm.pushed_sp, show BitVec.ofNat 32 (4 * [Reg.r12, Reg.lr].length) = BitVec.ofNat 32 8 from rfl,
      VG.Proof.MlDsa.Arm.Message.sp_sub8 h8]; omega
  · have hsp₂' : s₂.sp = s.sp - BitVec.ofNat 32 8 := by rw [hsp₂, VG.Arm.pushed_sp]; rfl
    have f₁ := push2_frame h8
    have hsu' : 8 + stackUse c ≤ s.sp.toNat := by omega
    refine ⟨by simp only [popped_rd, hrd, VG.Arm.pushed_rd], by simp only [popped_wr, hwr, hwp, List.tail_cons],
      by rw [popped_sp, hsp₂']; exact BitVec.sub_add_cancel _ _,
      fun r hr hl => by rw [popped_gpr (VG.Proof.MlDsa.Arm.Message.ne12_pres r hr hl), hcs r hr hl, VG.Arm.pushed_gpr], ?_,
      s₂, rfl, fun r hr => (popped_gpr hr _ _).symm, hpost⟩
    rw [popped_mem]
    rw [VG.Arm.pushed_sp] at hf
    refine (f₁.sub fun r hr => ?_).trans (hf.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
      exact belowA_sub (show 8 ≤ D by omega)
    · simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _),
          fun x h => belowA_sub (show 8 + stackUse c ≤ D by omega) x (belowA_push hsu' x h)⟩

/-- The regions a callee in a frame of `r12` and `lr` is given, within the
state after the push. -/
theorem cov_pushed {t1 : State} (h8 : 8 ≤ t1.sp.toNat) {rd wr : List Region}
    (hr : ∀ r ∈ rd, ∃ R ∈ t1.rd ++ t1.wr, Within r R) (hw : ∀ r ∈ wr, ∃ R ∈ t1.wr, Within r R) :
    Covers ((rd ++ [VG.Proof.MlDsa.Arm.Message.argR t1]) ++ wr) ((pushed [.r12, .lr] t1).rd ++ (pushed [.r12, .lr] t1).wr) ∧
      Covers wr (pushed [.r12, .lr] t1).wr := by
  have hwp : (pushed [.r12, .lr] t1).wr = belowA t1.sp 8 :: t1.wr := by rw [VG.Arm.pushed_wr, VG.Proof.MlDsa.Arm.Message.frame8 h8]
  have cW : Covers wr (pushed [.r12, .lr] t1).wr := by
    rw [hwp]
    exact VG.Proof.MlDsa.Arm.Message.covers_of_within fun r h => let ⟨R, hR, w⟩ := hw r h; ⟨R, List.mem_cons_of_mem _ hR, w⟩
  refine ⟨fun x m ⟨r, hr', hc⟩ => ?_, cW⟩
  rcases List.mem_append.mp hr' with h | h
  · rcases List.mem_append.mp h with h | h
    · obtain ⟨R, hR, w⟩ := hr r h
      have hR' : R ∈ (pushed [.r12, .lr] t1).rd ++ (pushed [.r12, .lr] t1).wr := by
        rw [VG.Arm.pushed_rd, hwp]
        rcases List.mem_append.mp hR with h' | h'
        · exact List.mem_append_left _ h'
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ h')
      exact VG.Proof.MlDsa.Arm.Message.covers_of_within (rs := [r]) (fun r' h' => by
        simp only [List.mem_singleton] at h'; subst h'; exact ⟨R, hR', w⟩) x m ⟨r, List.mem_singleton_self _, hc⟩
    · simp only [List.mem_singleton] at h; subst h
      refine ⟨belowA t1.sp 8, by rw [hwp]; simp, ?_⟩
      simp only [Region.Contains, belowA] at hc ⊢; omega
  · obtain ⟨R, hR, c⟩ := cW x m ⟨r, h, hc⟩
    exact ⟨R, List.mem_append_right _ hR, c⟩

/-- The bytes of a region apart from the 8 the push writes, after the push. -/
theorem storeWords_bytes {t : State} (h8 : 8 ≤ t.sp.toNat) {a : Addr} {n : Nat}
    (hd : Region.Disjoint ⟨a, n⟩ (below t 8)) (hn : n ≤ 2 ^ 64) :
    bytesAt (storeWords t.mem (t.sp - 8#32) [t.gpr .r12, t.gpr .lr]) a n = bytesAt t.mem a n :=
  Proof.MlKem.bytesAt_frame (push2_frame h8) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hd) hn

/-- The precondition of `signContract p Arm.abi 28`, from its facts. -/
theorem signC_pre {p : Params} {E : State} (sp : 28 ≤ E.sp.toNat) (sp4 : E.sp.toNat + 4 ≤ 2 ^ 32)
    (rd : E.rd = [⟨State.addr (E.gpr .r0), p.skLen⟩, ⟨State.addr (E.gpr .r1), 64⟩, ⟨State.addr (E.gpr .r2), 32⟩,
      ⟨stackArgAddr E 0, 4⟩])
    (wr : E.wr = [⟨State.addr (E.gpr .r3), p.sigLen⟩, ⟨State.addr (stackArg E 0), VG.Proof.MlDsa.Arm.Message.sScr p⟩])
    (d03 : Region.Disjoint ⟨State.addr (E.gpr .r0), p.skLen⟩ ⟨State.addr (E.gpr .r3), p.sigLen⟩)
    (d0s : Region.Disjoint ⟨State.addr (E.gpr .r0), p.skLen⟩ ⟨State.addr (stackArg E 0), VG.Proof.MlDsa.Arm.Message.sScr p⟩)
    (d13 : Region.Disjoint ⟨State.addr (E.gpr .r1), 64⟩ ⟨State.addr (E.gpr .r3), p.sigLen⟩)
    (d1s : Region.Disjoint ⟨State.addr (E.gpr .r1), 64⟩ ⟨State.addr (stackArg E 0), VG.Proof.MlDsa.Arm.Message.sScr p⟩)
    (d23 : Region.Disjoint ⟨State.addr (E.gpr .r2), 32⟩ ⟨State.addr (E.gpr .r3), p.sigLen⟩)
    (d2s : Region.Disjoint ⟨State.addr (E.gpr .r2), 32⟩ ⟨State.addr (stackArg E 0), VG.Proof.MlDsa.Arm.Message.sScr p⟩)
    (d3s : Region.Disjoint ⟨State.addr (E.gpr .r3), p.sigLen⟩ ⟨State.addr (stackArg E 0), VG.Proof.MlDsa.Arm.Message.sScr p⟩)
    (d3a : Region.Disjoint ⟨State.addr (E.gpr .r3), p.sigLen⟩ ⟨stackArgAddr E 0, 4⟩)
    (dsa : Region.Disjoint ⟨State.addr (stackArg E 0), VG.Proof.MlDsa.Arm.Message.sScr p⟩ ⟨stackArgAddr E 0, 4⟩)
    (k0 : Region.Disjoint ⟨State.addr E.sp - BitVec.ofNat 64 28, 28⟩ ⟨State.addr (E.gpr .r0), p.skLen⟩)
    (k1 : Region.Disjoint ⟨State.addr E.sp - BitVec.ofNat 64 28, 28⟩ ⟨State.addr (E.gpr .r1), 64⟩)
    (k2 : Region.Disjoint ⟨State.addr E.sp - BitVec.ofNat 64 28, 28⟩ ⟨State.addr (E.gpr .r2), 32⟩)
    (k3 : Region.Disjoint ⟨State.addr E.sp - BitVec.ofNat 64 28, 28⟩ ⟨State.addr (E.gpr .r3), p.sigLen⟩)
    (ks : Region.Disjoint ⟨State.addr E.sp - BitVec.ofNat 64 28, 28⟩ ⟨State.addr (stackArg E 0), VG.Proof.MlDsa.Arm.Message.sScr p⟩)
    (ka : Region.Disjoint ⟨State.addr E.sp - BitVec.ofNat 64 28, 28⟩ ⟨stackArgAddr E 0, 4⟩)
    (n0 : (E.gpr .r0).toNat + p.skLen ≤ 2 ^ 32) (n1 : (E.gpr .r1).toNat + 64 ≤ 2 ^ 32)
    (n2 : (E.gpr .r2).toNat + 32 ≤ 2 ^ 32) (n3 : (E.gpr .r3).toNat + p.sigLen ≤ 2 ^ 32)
    (ns : (stackArg E 0).toNat + VG.Proof.MlDsa.Arm.Message.sScr p ≤ 2 ^ 32) :
    (signContract p Arm.abi 28).pre E := by
  sig_pre [signContract, signSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨sp, sp4, rd, wr, d03, d0s, d13, d1s, d23, d2s, d3s, d3a, dsa, k0, k1, k2, k3, ks, ka, n0, n1, n2, n3, ns⟩

/-- The arguments of the call of the signing function on `μ`. -/
abbrev signArgs : List (Reg × VG.Impl.MlDsa.Arm.Message.Arg) := [(.r0, .slot fKey), (.r1, .off oMU), (.r2, .slot fRnd), (.r3, .slot fSig),
  (.r12, .slot fScr)]

section
variable {p : Params} {s : State}

/-- The working space of the functions on `μ`: the start of `scratch`. -/
theorem sScr_sub (p : Params) (b : Addr) : Region.Sub ⟨b, VG.Proof.MlDsa.Arm.Message.sScr p⟩ ⟨b, VG.Proof.MlDsa.Arm.Message.mScrLen p⟩ :=
  Region.sub_prefix (by rw [VG.Proof.MlDsa.Arm.Message.mScr_eq]; simp only [VG.Proof.MlDsa.Arm.Message.sScr, oE]; omega)

/-- What lies in the 1 KiB is apart from it. -/
theorem x_sScr {L : VG.Proof.MlDsa.Arm.Message.Lay} (hL : L.Ok) (hE : L.E = oE p) {d n : Nat} (hd : d + n ≤ 1024) :
    Region.Disjoint ⟨L.X + BitVec.ofNat 64 d, n⟩ ⟨State.addr L.scr, VG.Proof.MlDsa.Arm.Message.sScr p⟩ := by
  rw [hL.x_eq, add_add, hE]
  have := hL.hE; have := hL.nScr
  exact Offset.disjoint_base _ (by simp only [VG.Proof.MlDsa.Arm.Message.sScr, oE]; omega) (by omega)

theorem mu_within {L : VG.Proof.MlDsa.Arm.Message.Lay} (hL : L.Ok) : Within ⟨L.MU, 64⟩ L.SC :=
  (within_off L.X (d := 840) (n := 64) (k := 1024) (by omega)).trans hL.xs_sc

/-- The stack below the callee's stack pointer, in `STK`. -/
theorem stkE_sub {L : VG.Proof.MlDsa.Arm.Message.Lay} (hL : L.Ok) :
    Region.Sub ⟨State.addr (L.SP - BitVec.ofNat 32 8) - BitVec.ofNat 64 28, 28⟩ L.STK := by
  rw [VG.Proof.MlKem.Arm.addr_sub (by have := hL.nSP; omega), BitVec.sub_sub, BitVec.ofNat_add_ofNat]
  exact Offset.sub_below _ (by omega) (by omega)

theorem argR_sub {L : VG.Proof.MlDsa.Arm.Message.Lay} {t : State} (ht : t.sp = L.SP) : Region.Sub (VG.Proof.MlDsa.Arm.Message.argR t) L.STK := by
  simp only [VG.Proof.MlDsa.Arm.Message.argR, ht]; exact Offset.sub_below _ (by omega) (by omega)

/-- The regions the signing function on `μ` reads and writes. -/
abbrev signRd (p : Params) (s : State) : List Region :=
  [⟨State.addr (s.gpr .r0), p.skLen⟩, ⟨(VG.Proof.MlDsa.Arm.Message.slay p s).MU, 64⟩, ⟨State.addr (stackArg s 1), 32⟩]
abbrev signWr (p : Params) (s : State) : List Region :=
  [⟨State.addr (stackArg s 2), p.sigLen⟩, ⟨State.addr (stackArg s 3), VG.Proof.MlDsa.Arm.Message.sScr p⟩]

/-- The registers after the moves of the arguments. -/
theorem signRegs_of (hL : (VG.Proof.MlDsa.Arm.Message.slay p s).Ok) {g : Reg → BitVec 32} {m₀ : Mem} {t t1 : State}
    (hc : VG.Proof.MlDsa.Arm.Message.Ctx (VG.Proof.MlDsa.Arm.Message.slay p s) g m₀ t) (hm : (∀ da ∈ VG.Proof.MlDsa.Arm.Message.signArgs, t1.gpr da.1 = da.2.val t)) :
    t1.gpr .r0 = s.gpr .r0 ∧ t1.gpr .r1 = (VG.Proof.MlDsa.Arm.Message.slay p s).X32 + BitVec.ofNat 32 840 ∧ t1.gpr .r2 = stackArg s 1 ∧
      t1.gpr .r3 = stackArg s 2 ∧ t1.gpr .r12 = stackArg s 3 := by
  have e0 := hm (.r0, .slot fKey) (by simp)
  have e1 := hm (.r1, .off oMU) (by simp)
  have e2 := hm (.r2, .slot fRnd) (by simp)
  have e3 := hm (.r3, .slot fSig) (by simp)
  have e4 := hm (.r12, .slot fScr) (by simp)
  rw [hc.slotV hL (f := fKey) (j := 0) rfl (by omega)] at e0
  rw [hc.off] at e1
  rw [hc.slotV hL (f := fRnd) (j := 5) rfl (by omega)] at e2
  rw [hc.slotV hL (f := fSig) (j := 6) rfl (by omega)] at e3
  rw [hc.slotV hL (f := fScr) (j := 7) rfl (by omega)] at e4
  simp only [Lay.vals, VG.Proof.MlDsa.Arm.Message.slay, List.getD_cons_zero, List.getD_cons_succ] at e0 e2 e3 e4
  exact ⟨e0, e1, e2, e3, e4⟩

/-- The precondition of the signing function on `μ`, on entry to it. -/
theorem signK_pre (hp : p ∈ VG.Proof.MlDsa.Arm.Message.params) (h : VG.Proof.MlDsa.Arm.Message.SPre p s) (h8 : (stackArg s 0).toNat < 256) {g : Reg → BitVec 32}
    {m₀ : Mem} {t t1 : State} (hc : VG.Proof.MlDsa.Arm.Message.Ctx (VG.Proof.MlDsa.Arm.Message.slay p s) g m₀ t)
    (hA : ∀ da ∈ VG.Proof.MlDsa.Arm.Message.signArgs, t1.gpr da.1 = da.2.val t) (hsp1 : t1.sp = s.sp) :
    (signContract p Arm.abi 28).pre
      ((pushed [.r12, .lr] t1).callEntry.withRegions (VG.Proof.MlDsa.Arm.Message.signRd p s ++ [VG.Proof.MlDsa.Arm.Message.argR t1]) (VG.Proof.MlDsa.Arm.Message.signWr p s)) := by
  have hL := VG.Proof.MlDsa.Arm.Message.slay_ok hp h h8
  obtain ⟨e0, e1, e2, e3, e4⟩ := VG.Proof.MlDsa.Arm.Message.signRegs_of hL hc hA
  have h8' : 8 ≤ t1.sp.toNat := by rw [hsp1]; have := h.sp; omega
  obtain ⟨a0, a1, -⟩ := push2_arg (t := (pushed [.r12, .lr] t1).callEntry.withRegions (VG.Proof.MlDsa.Arm.Message.signRd p s ++ [VG.Proof.MlDsa.Arm.Message.argR t1])
    (VG.Proof.MlDsa.Arm.Message.signWr p s)) h8' rfl rfl
  have hmu := VG.Proof.MlDsa.Arm.Message.mu_eq hL
  have hsub := VG.Proof.MlDsa.Arm.Message.sScr_sub p (State.addr (stackArg s 3))
  have hmuS : Region.Sub ⟨(VG.Proof.MlDsa.Arm.Message.slay p s).MU, 64⟩ ⟨State.addr (stackArg s 3), VG.Proof.MlDsa.Arm.Message.mScrLen p⟩ := (VG.Proof.MlDsa.Arm.Message.mu_within hL).sub
  have eSP : ((pushed [.r12, .lr] t1).callEntry.withRegions (VG.Proof.MlDsa.Arm.Message.signRd p s ++ [VG.Proof.MlDsa.Arm.Message.argR t1]) (VG.Proof.MlDsa.Arm.Message.signWr p s)).sp =
      s.sp - BitVec.ofNat 32 8 := by
    simp only [State.withRegions_sp, State.callEntry_sp, VG.Arm.pushed_sp, hsp1]; rfl
  have kE := VG.Proof.MlDsa.Arm.Message.stkE_sub (L := VG.Proof.MlDsa.Arm.Message.slay p s) hL
  have kA := VG.Proof.MlDsa.Arm.Message.argR_sub (L := VG.Proof.MlDsa.Arm.Message.slay p s) (t := t1) hsp1
  simp only [VG.Proof.MlDsa.Arm.Message.slay] at kE kA
  have hstk : ∀ {r : Region}, (VG.Proof.MlDsa.Arm.Message.rStk s).Disjoint r → Region.Disjoint ⟨State.addr (s.sp - BitVec.ofNat 32 8) -
      BitVec.ofNat 64 28, 28⟩ r := fun hr => hr.sub_left kE
  refine VG.Proof.MlDsa.Arm.Message.signC_pre ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp only [view_gpr _ _ _ _ (by decide : Reg.r0 ∉ linkRegs), view_gpr _ _ _ _ (by decide : Reg.r1 ∉ linkRegs),
      view_gpr _ _ _ _ (by decide : Reg.r2 ∉ linkRegs), view_gpr _ _ _ _ (by decide : Reg.r3 ∉ linkRegs),
      e0, e1, e2, e3, a0, a1, e4, eSP, hmu, State.withRegions_rd, State.withRegions_wr]
  · rw [VG.Proof.MlDsa.Arm.Message.sp_sub8 (by have := h.sp; omega)]; have := h.sp; omega
  · rw [VG.Proof.MlDsa.Arm.Message.sp_sub8 (by have := h.sp; omega)]; have := h.spA; omega
  · simp only [VG.Proof.MlDsa.Arm.Message.argR, hsp1, List.cons_append, List.nil_append]
  · exact h.skSig
  · exact h.skScr.sub_right hsub
  · exact h.sigScr.symm.sub_left hmuS
  · exact (VG.Proof.MlDsa.Arm.Message.x_sScr hL rfl (by omega) : Region.Disjoint ⟨(VG.Proof.MlDsa.Arm.Message.slay p s).X + BitVec.ofNat 64 840, 64⟩ _)
  · exact h.rndSig
  · exact h.rndScr.sub_right hsub
  · exact h.sigScr.sub_right hsub
  · exact (h.stkSig.sub_left kA).symm
  · exact ((h.stkScr.sub_left kA).sub_right hsub).symm
  · exact hstk h.stkSk
  · exact (VG.Proof.MlDsa.Arm.Message.k_mu hL).sub_left kE
  · exact hstk h.stkRnd
  · exact hstk h.stkSig
  · exact hstk (h.stkScr.sub_right hsub)
  · rw [hsp1, VG.Proof.MlKem.Arm.addr_sub (by have := h.sp; omega)]
    exact (Offset.base_disjoint_below _ (by omega)).symm
  · exact h.nSk
  · have := hL.x32_lt
    rw [VG.Proof.MlDsa.Arm.Message.x32_toNat hL (by omega)]; omega
  · exact h.nRnd
  · exact h.nSig
  · have := h.nScr; simp only [VG.Proof.MlDsa.Arm.Message.mScrLen, VG.Proof.MlDsa.Arm.Message.sScr, messageScratchWords] at this ⊢; omega

/-- The bytes of a region apart from the 8 the push writes, in the callee's entry state. -/
theorem pushed_bytes {t : State} (h8 : 8 ≤ t.sp.toNat) (rd wr : List Region) {a : Addr} {n : Nat}
    (hd : Region.Disjoint ⟨a, n⟩ (below t 8)) (hn : n ≤ 2 ^ 64) :
    bytesAt ((pushed [.r12, .lr] t).callEntry.withRegions rd wr).mem a n = bytesAt t.mem a n := by
  simp only [State.withRegions_mem, State.callEntry_mem]
  exact Proof.MlKem.bytesAt_frame (push2_frame h8) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hd) hn

/-- The call of the signing function on `μ`. -/
theorem signCall_ok {n : String} {c : Prog isa} (hS : VG.Proof.MlDsa.Arm.Message.SignFn p c) (hp : p ∈ VG.Proof.MlDsa.Arm.Message.params) (h : VG.Proof.MlDsa.Arm.Message.SPre p s)
    (h8 : (stackArg s 0).toNat < 256) {g : Reg → BitVec 32} {m₀ : Mem} {t : State}
    (hc : VG.Proof.MlDsa.Arm.Message.Ctx (VG.Proof.MlDsa.Arm.Message.slay p s) g m₀ t) :
    WP isa (.seq (.block (VG.Impl.MlDsa.Arm.Message.setArgs VG.Proof.MlDsa.Arm.Message.signArgs)) (.frame (.push [.r12, .lr]) (.call n c) (.pop .r12 8))) t fun s' =>
      VG.Proof.MlDsa.Arm.Message.Fin (VG.Proof.MlDsa.Arm.Message.slay p s) g s' ∧
      Outcome (fun b => signMu p b (bytesAt t.mem (State.addr (s.gpr .r0)) p.skLen) (bytesAt t.mem (VG.Proof.MlDsa.Arm.Message.slay p s).MU 64)
          (bytesAt t.mem (State.addr (stackArg s 1)) 32)) (s'.gpr .r0)
        (bytesAt s'.mem (State.addr (stackArg s 2)) p.sigLen) := by
  have hL := VG.Proof.MlDsa.Arm.Message.slay_ok hp h h8
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Message.setArgs_ok VG.Proof.MlDsa.Arm.Message.signArgs (by decide) t (hc.xOk hL)) fun t1 ⟨hA, o⟩ => ?_)
  have hc1 : VG.Proof.MlDsa.Arm.Message.Ctx (VG.Proof.MlDsa.Arm.Message.slay p s) g m₀ t1 := hc.regs o.rd o.wr o.sp o.mem fun r hr hl =>
    o.gpr r (by simp only [List.map_cons, List.map_nil]; exact VG.Proof.MlDsa.Arm.Message.not_pres hr hl _)
  obtain ⟨e0, e1, e2, e3, _⟩ := VG.Proof.MlDsa.Arm.Message.signRegs_of hL hc hA
  have hsp1 : t1.sp = s.sp := hc1.sp
  have hpre := VG.Proof.MlDsa.Arm.Message.signK_pre hp h h8 hc hA hsp1
  have hsub := VG.Proof.MlDsa.Arm.Message.sScr_sub p (State.addr (stackArg s 3))
  have hmuS : Region.Sub ⟨(VG.Proof.MlDsa.Arm.Message.slay p s).MU, 64⟩ ⟨State.addr (stackArg s 3), VG.Proof.MlDsa.Arm.Message.mScrLen p⟩ := (VG.Proof.MlDsa.Arm.Message.mu_within hL).sub
  refine WP.mono (VG.Proof.MlDsa.Arm.Message.frameCall_ok (D := 36) hS.ver.1 (by have := hS.su; omega) (by rw [hsp1]; exact h.sp) hpre ?_ ?_)
    fun s' ⟨hrd, hwr, hsp, hcs, hf, s₂, hm₂, hg₂, hpost⟩ => ?_
  · rw [hc1.rd, hc1.wr]
    refine VG.Proof.MlDsa.Arm.Message.covers_of_within fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp [VG.Proof.MlDsa.Arm.Message.slay, h.rd], within_self _⟩
    · exact ⟨_, by simp [VG.Proof.MlDsa.Arm.Message.slay, h.wr], VG.Proof.MlDsa.Arm.Message.mu_within hL⟩
    · exact ⟨_, by simp [VG.Proof.MlDsa.Arm.Message.slay, h.rd], within_self _⟩
  · rw [hc1.wr]
    refine VG.Proof.MlDsa.Arm.Message.covers_of_within fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by simp [VG.Proof.MlDsa.Arm.Message.slay, h.wr], within_self _⟩
    · exact ⟨⟨State.addr (stackArg s 3), VG.Proof.MlDsa.Arm.Message.mScrLen p⟩, by simp [VG.Proof.MlDsa.Arm.Message.slay, h.wr],
        within_base _ (by rw [VG.Proof.MlDsa.Arm.Message.mScr_eq]; simp only [VG.Proof.MlDsa.Arm.Message.sScr, oE]; omega)⟩
  -- After the call.
  have hsv : ∀ d, d + 4 ≤ 120 → s'.mem.readW ((VG.Proof.MlDsa.Arm.Message.slay p s).X + BitVec.ofNat 64 (904 + d)) 32 =
      t1.mem.readW ((VG.Proof.MlDsa.Arm.Message.slay p s).X + BitVec.ofNat 64 (904 + d)) 32 := fun d hd' =>
    hf.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h.sigScr.symm.sub_left ((within_off (VG.Proof.MlDsa.Arm.Message.slay p s).X (d := 904 + d) (n := 4) (k := 1024)
          (by omega)).trans hL.xs_sc).sub
      · exact VG.Proof.MlDsa.Arm.Message.x_sScr hL rfl (by omega)
      · rw [hsp1]
        exact hL.sv_disj (r := belowA s.sp 36) (.inr fun _ h => h) hd') (by decide)
  refine ⟨⟨hrd.trans hc1.rd, hwr.trans hc1.wr, hsp.trans hc1.sp, (hcs .r7 (by decide) (by decide)).trans hc1.r7,
    fun r hr h7 hl => (hcs r hr hl).trans (hc1.cs r hr h7 hl),
    (hsv 0 (by omega)).trans hc1.s7, (hsv 4 (by omega)).trans hc1.sLR⟩, ?_⟩
  have h8' : 8 ≤ t1.sp.toNat := by rw [hsp1]; have := h.sp; omega
  have kA := VG.Proof.MlDsa.Arm.Message.argR_sub (L := VG.Proof.MlDsa.Arm.Message.slay p s) (t := t1) hsp1
  have bk : Region.Sub (below t1 8) (VG.Proof.MlDsa.Arm.Message.slay p s).STK := VG.Proof.MlDsa.Arm.Message.below_stk hsp1
  sig_reduce [signContract, signSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hpost
  have pm : ∀ (x : BitVec 32) (n : Nat), Region.Disjoint ⟨State.addr x, n⟩ (below t1 8) → n ≤ 2 ^ 64 →
      bytesAt (storeWords t1.mem (t1.sp - 8#32) [t1.gpr .r12, t1.gpr .lr]) (BitVec.setWidth 64 x) n =
        bytesAt t1.mem (State.addr x) n := fun x n hd hn => VG.Proof.MlDsa.Arm.Message.storeWords_bytes h8' hd hn
  rw [e0, e1, e2, e3, pm _ _ (h.stkSk.symm.sub_right bk) (by have := h.nSk; omega),
    pm _ _ (by rw [VG.Proof.MlDsa.Arm.Message.mu_eq hL]; exact (VG.Proof.MlDsa.Arm.Message.k_mu hL).symm.sub_right bk) (by decide),
    pm _ _ (h.stkRnd.symm.sub_right bk) (by decide), VG.Proof.MlDsa.Arm.Message.mu_eq hL, hm₂, Proof.MlKem.Arm.setWidth_append32,
    hg₂ .r0 (by decide), o.mem] at hpost
  exact hpost

end

end VG.Proof.MlDsa.Arm.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Message.VerifyCall`. -/
section

/-!
# ML-DSA on ARMv7, `verify_message`: the call of the verification function on `μ`

Untrusted: everything here is checked by Lean. Any code verified against
`verifyContract p Arm.abi 36` whose frames use at most 36 bytes of stack
(`VerifyFn`): its call on the key, `μ` at `X + 840`, `sig` and the first
`scratchWords p` words of `scratch` (`verifyCall_ok`), after which the saves
are intact (`Fin`).
-/

namespace VG.Proof.MlDsa.Arm.Message

open VG VG.Arm VG.Impl.MlDsa.Arm.Message
open VG.Proof.MlDsa.Message
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- A verification function on `μ` that `verify_message` can call. -/
structure VerifyFn (p : Params) (c : Prog isa) : Prop where
  ver : Verified Arm.target c (verifyContract p Arm.abi 36)
  su : stackUse c ≤ 36

/-- The precondition of `verifyContract p Arm.abi 36`, from its facts. -/
theorem verifyC_pre {p : Params} {E : State} (sp : 36 ≤ E.sp.toNat)
    (rd : E.rd = [⟨State.addr (E.gpr .r0), p.pkLen⟩, ⟨State.addr (E.gpr .r1), 64⟩,
      ⟨State.addr (E.gpr .r2), p.sigLen⟩])
    (wr : E.wr = [⟨State.addr (E.gpr .r3), VG.Proof.MlDsa.Arm.Message.sScr p⟩])
    (d03 : Region.Disjoint ⟨State.addr (E.gpr .r0), p.pkLen⟩ ⟨State.addr (E.gpr .r3), VG.Proof.MlDsa.Arm.Message.sScr p⟩)
    (d13 : Region.Disjoint ⟨State.addr (E.gpr .r1), 64⟩ ⟨State.addr (E.gpr .r3), VG.Proof.MlDsa.Arm.Message.sScr p⟩)
    (d23 : Region.Disjoint ⟨State.addr (E.gpr .r2), p.sigLen⟩ ⟨State.addr (E.gpr .r3), VG.Proof.MlDsa.Arm.Message.sScr p⟩)
    (k0 : Region.Disjoint ⟨State.addr E.sp - BitVec.ofNat 64 36, 36⟩ ⟨State.addr (E.gpr .r0), p.pkLen⟩)
    (k1 : Region.Disjoint ⟨State.addr E.sp - BitVec.ofNat 64 36, 36⟩ ⟨State.addr (E.gpr .r1), 64⟩)
    (k2 : Region.Disjoint ⟨State.addr E.sp - BitVec.ofNat 64 36, 36⟩ ⟨State.addr (E.gpr .r2), p.sigLen⟩)
    (k3 : Region.Disjoint ⟨State.addr E.sp - BitVec.ofNat 64 36, 36⟩ ⟨State.addr (E.gpr .r3), VG.Proof.MlDsa.Arm.Message.sScr p⟩)
    (n0 : (E.gpr .r0).toNat + p.pkLen ≤ 2 ^ 32) (n1 : (E.gpr .r1).toNat + 64 ≤ 2 ^ 32)
    (n2 : (E.gpr .r2).toNat + p.sigLen ≤ 2 ^ 32) (n3 : (E.gpr .r3).toNat + VG.Proof.MlDsa.Arm.Message.sScr p ≤ 2 ^ 32) :
    (verifyContract p Arm.abi 36).pre E := by
  sig_pre [verifyContract, verifySig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨sp, by have := E.sp.isLt; omega, rd, wr, d03, d13, d23, k0, k1, k2, k3, n0, n1, n2, n3⟩

/-- The arguments of the call of the verification function on `μ`. -/
abbrev verifyArgs : List (Reg × VG.Impl.MlDsa.Arm.Message.Arg) := [(.r0, .slot fKey), (.r1, .off oMU), (.r2, .slot fSig), (.r3, .slot fScr)]

section
variable {p : Params} {s : State}

/-- The regions the verification function on `μ` reads and writes. -/
abbrev verifyRd (p : Params) (s : State) : List Region :=
  [⟨State.addr (s.gpr .r0), p.pkLen⟩, ⟨(VG.Proof.MlDsa.Arm.Message.vlay p s).MU, 64⟩, ⟨State.addr (stackArg s 1), p.sigLen⟩]
abbrev verifyWr (p : Params) (s : State) : List Region := [⟨State.addr (stackArg s 2), VG.Proof.MlDsa.Arm.Message.sScr p⟩]

/-- The registers after the moves of the arguments. -/
theorem verifyRegs_of (hL : (VG.Proof.MlDsa.Arm.Message.vlay p s).Ok) {g : Reg → BitVec 32} {m₀ : Mem} {t t1 : State}
    (hc : VG.Proof.MlDsa.Arm.Message.Ctx (VG.Proof.MlDsa.Arm.Message.vlay p s) g m₀ t) (hm : (∀ da ∈ VG.Proof.MlDsa.Arm.Message.verifyArgs, t1.gpr da.1 = da.2.val t)) :
    t1.gpr .r0 = s.gpr .r0 ∧ t1.gpr .r1 = (VG.Proof.MlDsa.Arm.Message.vlay p s).X32 + BitVec.ofNat 32 840 ∧ t1.gpr .r2 = stackArg s 1 ∧
      t1.gpr .r3 = stackArg s 2 := by
  have e0 := hm (.r0, .slot fKey) (by simp)
  have e1 := hm (.r1, .off oMU) (by simp)
  have e2 := hm (.r2, .slot fSig) (by simp)
  have e3 := hm (.r3, .slot fScr) (by simp)
  rw [hc.slotV hL (f := fKey) (j := 0) rfl (by omega)] at e0
  rw [hc.off] at e1
  rw [hc.slotV hL (f := fSig) (j := 6) rfl (by omega)] at e2
  rw [hc.slotV hL (f := fScr) (j := 7) rfl (by omega)] at e3
  simp only [Lay.vals, VG.Proof.MlDsa.Arm.Message.vlay, List.getD_cons_zero, List.getD_cons_succ] at e0 e2 e3
  exact ⟨e0, e1, e2, e3⟩

/-- The precondition of the verification function on `μ`, on entry to it. -/
theorem verifyK_pre (hp : p ∈ VG.Proof.MlDsa.Arm.Message.params) (h : VG.Proof.MlDsa.Arm.Message.VPre p s) (h8 : (stackArg s 0).toNat < 256) {g : Reg → BitVec 32}
    {m₀ : Mem} {t t1 : State} (hc : VG.Proof.MlDsa.Arm.Message.Ctx (VG.Proof.MlDsa.Arm.Message.vlay p s) g m₀ t)
    (hA : ∀ da ∈ VG.Proof.MlDsa.Arm.Message.verifyArgs, t1.gpr da.1 = da.2.val t) (hsp1 : t1.sp = s.sp) :
    (verifyContract p Arm.abi 36).pre (t1.callEntry.withRegions (VG.Proof.MlDsa.Arm.Message.verifyRd p s) (VG.Proof.MlDsa.Arm.Message.verifyWr p s)) := by
  have hL := VG.Proof.MlDsa.Arm.Message.vlay_ok hp h h8
  obtain ⟨e0, e1, e2, e3⟩ := VG.Proof.MlDsa.Arm.Message.verifyRegs_of hL hc hA
  have hsub := VG.Proof.MlDsa.Arm.Message.sScr_sub p (State.addr (stackArg s 2))
  generalize hE : t1.callEntry.withRegions (VG.Proof.MlDsa.Arm.Message.verifyRd p s) (VG.Proof.MlDsa.Arm.Message.verifyWr p s) = E
  have gr : ∀ {r : Reg}, r ∉ linkRegs → E.gpr r = t1.gpr r := fun hr => by
    rw [← hE, State.withRegions_gpr, State.callEntry_gpr _ hr]
  have g0 : E.gpr .r0 = s.gpr .r0 := by rw [gr (by decide), e0]
  have g1 : State.addr (E.gpr .r1) = (VG.Proof.MlDsa.Arm.Message.vlay p s).MU := by rw [gr (by decide), e1, VG.Proof.MlDsa.Arm.Message.mu_eq hL]
  have g2 : E.gpr .r2 = stackArg s 1 := by rw [gr (by decide), e2]
  have g3 : E.gpr .r3 = stackArg s 2 := by rw [gr (by decide), e3]
  have gsp : E.sp = s.sp := by rw [← hE, State.withRegions_sp, State.callEntry_sp, hsp1]
  have grd : E.rd = VG.Proof.MlDsa.Arm.Message.verifyRd p s := by rw [← hE]; rfl
  have gwr : E.wr = VG.Proof.MlDsa.Arm.Message.verifyWr p s := by rw [← hE]; rfl
  refine VG.Proof.MlDsa.Arm.Message.verifyC_pre ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> try simp only [g0, g1, g2, g3, gsp, grd, gwr]
  · exact h.sp
  · exact h.pkScr.sub_right hsub
  · exact VG.Proof.MlDsa.Arm.Message.x_sScr hL rfl (by omega)
  · exact h.sigScr.sub_right hsub
  · exact h.stkPk
  · have km := VG.Proof.MlDsa.Arm.Message.k_mu hL
    simp only [Lay.STK] at km
    rw [show (VG.Proof.MlDsa.Arm.Message.vlay p s).SP = s.sp from rfl] at km
    exact km
  · exact h.stkSig
  · exact h.stkScr.sub_right hsub
  · exact h.nPk
  · rw [gr (by decide), e1]
    have := hL.x32_lt
    rw [VG.Proof.MlDsa.Arm.Message.x32_toNat hL (by omega)]; omega
  · exact h.nSig
  · have := h.nScr; simp only [VG.Proof.MlDsa.Arm.Message.mScrLen, VG.Proof.MlDsa.Arm.Message.sScr, messageScratchWords] at this ⊢; omega

/-- The call of the verification function on `μ`. -/
theorem verifyCall_ok {n : String} {c : Prog isa} (hV : VG.Proof.MlDsa.Arm.Message.VerifyFn p c) (hp : p ∈ VG.Proof.MlDsa.Arm.Message.params) (h : VG.Proof.MlDsa.Arm.Message.VPre p s)
    (h8 : (stackArg s 0).toNat < 256) {g : Reg → BitVec 32} {m₀ : Mem} {t : State}
    (hc : VG.Proof.MlDsa.Arm.Message.Ctx (VG.Proof.MlDsa.Arm.Message.vlay p s) g m₀ t) :
    WP isa (.seq (.block (VG.Impl.MlDsa.Arm.Message.setArgs VG.Proof.MlDsa.Arm.Message.verifyArgs)) (.call n c)) t fun s' => VG.Proof.MlDsa.Arm.Message.Fin (VG.Proof.MlDsa.Arm.Message.vlay p s) g s' ∧
      (let w := fun b => verifyMu p b (bytesAt t.mem (State.addr (s.gpr .r0)) p.pkLen)
          (bytesAt t.mem (VG.Proof.MlDsa.Arm.Message.vlay p s).MU 64) (bytesAt t.mem (State.addr (stackArg s 1)) p.sigLen);
        (s'.gpr .r0 = 1 ∧ ∃ b, w b = some true) ∨ (s'.gpr .r0 = 0 ∧ w minBounds ≠ some true)) := by
  have hL := VG.Proof.MlDsa.Arm.Message.vlay_ok hp h h8
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Message.setArgs_ok VG.Proof.MlDsa.Arm.Message.verifyArgs (by decide) t (hc.xOk hL)) fun t1 ⟨hA, o⟩ => ?_)
  have hc1 : VG.Proof.MlDsa.Arm.Message.Ctx (VG.Proof.MlDsa.Arm.Message.vlay p s) g m₀ t1 := hc.regs o.rd o.wr o.sp o.mem fun r hr hl =>
    o.gpr r (by simp only [List.map_cons, List.map_nil]; exact VG.Proof.MlDsa.Arm.Message.not_pres hr hl _)
  obtain ⟨e0, e1, e2, _⟩ := VG.Proof.MlDsa.Arm.Message.verifyRegs_of hL hc hA
  have hsp1 : t1.sp = s.sp := hc1.sp
  have hpre := VG.Proof.MlDsa.Arm.Message.verifyK_pre hp h h8 hc hA hsp1
  refine WP.callF hV.ver.1 hpre ?_ ?_ (by rw [hsp1]; have := hV.su; have := h.sp; omega)
    fun s' hrd hwr hsp hf hcs hpost => ?_
  · rw [hc1.rd, hc1.wr]
    refine VG.Proof.MlDsa.Arm.Message.covers_of_within fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp [VG.Proof.MlDsa.Arm.Message.vlay, h.rd], within_self _⟩
    · exact ⟨_, by simp [VG.Proof.MlDsa.Arm.Message.vlay, h.wr], VG.Proof.MlDsa.Arm.Message.mu_within hL⟩
    · exact ⟨_, by simp [VG.Proof.MlDsa.Arm.Message.vlay, h.rd], within_self _⟩
    · exact ⟨⟨State.addr (stackArg s 2), VG.Proof.MlDsa.Arm.Message.mScrLen p⟩, by simp [VG.Proof.MlDsa.Arm.Message.vlay, h.wr],
        within_base _ (by rw [VG.Proof.MlDsa.Arm.Message.mScr_eq]; simp only [VG.Proof.MlDsa.Arm.Message.sScr, oE]; omega)⟩
  · rw [hc1.wr]
    refine VG.Proof.MlDsa.Arm.Message.covers_of_within fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact ⟨⟨State.addr (stackArg s 2), VG.Proof.MlDsa.Arm.Message.mScrLen p⟩, by simp [VG.Proof.MlDsa.Arm.Message.vlay, h.wr],
      within_base _ (by rw [VG.Proof.MlDsa.Arm.Message.mScr_eq]; simp only [VG.Proof.MlDsa.Arm.Message.sScr, oE]; omega)⟩
  -- After the call.
  have hsv : ∀ d, d + 4 ≤ 120 → s'.mem.readW ((VG.Proof.MlDsa.Arm.Message.vlay p s).X + BitVec.ofNat 64 (904 + d)) 32 =
      t1.mem.readW ((VG.Proof.MlDsa.Arm.Message.vlay p s).X + BitVec.ofNat 64 (904 + d)) 32 := fun d hd' =>
    hf.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact VG.Proof.MlDsa.Arm.Message.x_sScr hL rfl (by omega)
      · rw [hsp1]
        exact hL.sv_disj (r := belowA s.sp (stackUse c)) (.inr (belowA_sub hV.su)) hd') (by decide)
  refine ⟨⟨hrd.trans hc1.rd, hwr.trans hc1.wr, hsp.trans hc1.sp, (hcs .r7 (by decide) (by decide)).trans hc1.r7,
    fun r hr h7 hl => (hcs r hr hl).trans (hc1.cs r hr h7 hl),
    (hsv 0 (by omega)).trans hc1.s7, (hsv 4 (by omega)).trans hc1.sLR⟩, ?_⟩
  sig_reduce [verifyContract, verifySig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hpost
  rw [e0, e1, e2, Proof.MlKem.Arm.setWidth_append32, o.mem] at hpost
  rw [show BitVec.setWidth 64 ((VG.Proof.MlDsa.Arm.Message.vlay p s).X32 + 840#32) = (VG.Proof.MlDsa.Arm.Message.vlay p s).MU from VG.Proof.MlDsa.Arm.Message.mu_eq hL] at hpost
  exact hpost

end

end VG.Proof.MlDsa.Arm.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Message.SignCorrect`. -/
section

/-!
# ML-DSA on ARMv7, `sign_message`: correctness

Untrusted: everything here is checked by Lean. From a state satisfying
`signMessageContract p Arm.abi 36`, `signMessage n c p` returns 2 if the
context string is longer than 255 bytes; otherwise it computes `μ` of the
formatted message and calls the signing function on `μ` `c`, which gives
the signature of `ML-DSA.Sign_internal` on the formatted message
(`signMessage_wp`).
-/

namespace VG.Proof.MlDsa.Arm.Message

open VG VG.Arm VG.Impl.MlDsa.Arm.Message
open VG.Proof.MlDsa.Message
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

theorem wp_ite_t {c : isa.Cond} {th el : Prog isa} {s : State} {Q : State → Prop}
    (hc : isa.eval c s = some true) (h : WP isa th s Q) : WP isa (.ite c th el) s Q :=
  let ⟨_, _, e, q⟩ := h; ⟨_, _, .iteT hc e, q⟩

theorem wp_ite_f {c : isa.Cond} {th el : Prog isa} {s : State} {Q : State → Prop}
    (hc : isa.eval c s = some false) (h : WP isa el s Q) : WP isa (.ite c th el) s Q :=
  let ⟨_, _, e, q⟩ := h; ⟨_, _, .iteF hc e, q⟩

theorem lsr8_zero (x : BitVec 32) : (x >>> 8 - 0#32 == 0#32) = decide (x.toNat < 256) := by
  rw [BitVec.sub_zero]
  by_cases h : x.toNat < 256
  · rw [decide_eq_true h, beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    simp only [BitVec.toNat_zero]; omega
  · rw [decide_eq_false h, beq_eq_false_iff_ne]
    intro e
    have := congrArg BitVec.toNat e
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at this
    simp only [BitVec.toNat_zero] at this; omega

/-- `r12 ← ctx_len >> 8`, compared with 0, and the branch on it. -/
theorem chk_ok {s : State} (hin : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 0)) 4) :
    WP isa (.block [.ldrSp .r12 0, .mov .r12 (.shifted .r12 .lsr 8), .cmp .r12 (.imm 0)]) s fun s1 =>
      VG.Proof.MlDsa.Arm.Message.Only [.r12] s s1 ∧ isa.eval .ne s1 = some (decide ¬ (stackArg s 0).toNat < 256) := by
  refine VG.Proof.MlDsa.Arm.Message.wp_ldrSp (by decide) hin fun s1 o1 e1 => VG.Proof.MlDsa.Arm.Message.wp_movLsr (by decide) (by decide) fun s2 o2 e2 =>
    VG.Proof.MlDsa.Arm.Message.wp_cmpImm (by decide) fun s3 o3 e3 => VG.Proof.MlDsa.Arm.Message.wp_nil ⟨(o1.trans o2).trans (o3.mono fun r h => by simp at h), ?_⟩
  show some (!s3.z) = _
  rw [e3, e2, e1, show (0 : BitVec 32) = 0#32 from rfl, VG.Proof.MlDsa.Arm.Message.lsr8_zero]
  simp only [decide_not]
  rfl

/-- The words on the stack of a state satisfying `SPre` are readable. -/
theorem SPre.args {p : Params} {s : State} (h : VG.Proof.MlDsa.Arm.Message.SPre p s) {o : Nat} (ho : o + 4 ≤ 16) :
    InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 o)) 4 := by
  refine ⟨VG.Proof.MlDsa.Arm.Message.rArgs s 16, by simp [h.rd], ?_⟩
  simp only [VG.Proof.MlDsa.Arm.Message.rArgs, VG.Proof.MlDsa.Arm.Message.stackArgAddr0]
  rw [addr_add (by have := h.spA; omega)]
  exact Offset.contains_base _ ho (by omega)

theorem stackArg_eq (s : State) (j : Nat) :
    s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 (4 * j))) 32 = stackArg s j := rfl

theorem Ctx.slotOffV {L : VG.Proof.MlDsa.Arm.Message.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}
    (hc : VG.Proof.MlDsa.Arm.Message.Ctx L g m₀ t) (hL : L.Ok) (o : Nat) : (Arg.slotOff fKey o).val t = L.key + BitVec.ofNat 32 o := by
  have := hc.slotV hL (f := fKey) (j := 0) rfl (by omega)
  simp only [Arg.val] at this ⊢
  rw [this]; rfl

theorem signMessage_wp {p : Params} {n : String} {c : Prog isa}
    (hS : VG.Proof.MlDsa.Arm.Message.SignFn p c) (hp : p ∈ VG.Proof.MlDsa.Arm.Message.params) {s : State} (hpre : (signMessageContract p Arm.abi 36).pre s) :
    WP isa (signMessage n c p) s fun s' =>
      abiPreserved s s' ∧ (signMessageContract p Arm.abi 36).post s s' := by
  have h := VG.Proof.MlDsa.Arm.Message.sPre_of hpre
  unfold signMessage top
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Message.chk_ok (h.args (by omega))) fun s1 ⟨o1, hc1⟩ => ?_)
  by_cases h8 : (stackArg s 0).toNat < 256
  · rw [decide_eq_false (by simpa using h8)] at hc1
    have hL := VG.Proof.MlDsa.Arm.Message.slay_ok hp h h8
    have hs1 : ∀ o, o + 4 ≤ 16 → s1.mem.readW (State.addr (s1.sp + BitVec.ofNat 32 o)) 32 =
        s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 o)) 32 := fun _ _ => by rw [o1.mem, o1.sp]
    refine VG.Proof.MlDsa.Arm.Message.wp_ite_f hc1 (WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Message.enter_ok hL rfl (nA := 16) (by decide) (Nat.le_refl _) (o1.sp)
      (by rw [o1.rd]; rfl) (by rw [o1.wr]; rfl) (o1.get .r0) (o1.get .r1) (o1.get .r2) (o1.get .r3)
      (fun o ho => by rw [o1.rd, o1.wr, o1.sp]; exact h.args ho) (by rw [o1.sp]; exact h.spA)
      (by rw [o1.sp, ← VG.Proof.MlDsa.Arm.Message.stackArgAddr0]; exact h.scrArgs) (by omega)
      (by rw [hs1 12 (by omega)]; exact VG.Proof.MlDsa.Arm.Message.stackArg_eq s 3) (by decide) (fun j hj => by
        have hj4 : j < 4 := hj
        rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
        · exact (hs1 0 (by decide)).trans (VG.Proof.MlDsa.Arm.Message.stackArg_eq s 0)
        · exact (hs1 4 (by decide)).trans (VG.Proof.MlDsa.Arm.Message.stackArg_eq s 1)
        · exact (hs1 8 (by decide)).trans (VG.Proof.MlDsa.Arm.Message.stackArg_eq s 2)
        · exact (hs1 12 (by decide)).trans (VG.Proof.MlDsa.Arm.Message.stackArg_eq s 3))) fun t hc => ?_))
    have hsk := (VG.Proof.MlDsa.Arm.Message.skLen_ge hp).1
    have ekey : State.addr ((VG.Proof.MlDsa.Arm.Message.slay p s).key + BitVec.ofNat 32 64) = State.addr (VG.Proof.MlDsa.Arm.Message.slay p s).key + BitVec.ofNat 64 64 :=
      addr_add (by have := h.nSk; simp only [VG.Proof.MlDsa.Arm.Message.slay]; omega)
    have wtr : Within ⟨State.addr ((VG.Proof.MlDsa.Arm.Message.slay p s).key + BitVec.ofNat 32 64), 64⟩ (VG.Proof.MlDsa.Arm.Message.slay p s).KEY := by
      rw [ekey]; exact within_off _ (show 64 + 64 ≤ p.skLen by omega)
    have hfit : ((VG.Proof.MlDsa.Arm.Message.slay p s).key + BitVec.ofNat 32 64).toNat + 64 ≤ 2 ^ 32 := by
      have := h.nSk
      simp only [VG.Proof.MlDsa.Arm.Message.slay]
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 64) (by decide), Nat.mod_eq_of_lt (by omega)]
      omega
    have hst : Region.Sub ⟨(VG.Proof.MlDsa.Arm.Message.slay p s).ST, 200⟩ (VG.Proof.MlDsa.Arm.Message.slay p s).SC := by
      have := hL.sub_sc (e := 0) (k := 200) (by omega)
      simpa only [VG.Proof.MlDsa.Arm.Message.x0] using this
    refine WP.seq (WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Message.muHash_ok hL hc (tr := .slotOff fKey 64) (by decide) rfl
      (fun t' hc' => hc'.slotOffV hL 64) hfit ⟨_, List.mem_append_left _ hL.inKey, wtr⟩
      ((hL.xKey.symm.sub_left wtr.sub).sub_right hst)
      ((hL.xKey.symm.sub_left wtr.sub).sub_right (hL.sub_sc (by omega : 200 + 640 ≤ 1024)))
      (hL.kKey.sub_right wtr.sub)) fun t₁ ⟨hc₁, hμ⟩ => ?_))
    refine WP.mono (VG.Proof.MlDsa.Arm.Message.signCall_ok hS hp h h8 hc₁) fun s' ⟨hf, hq⟩ => ?_
    refine WP.mono (VG.Proof.MlDsa.Arm.Message.leave_ok hL hf) fun s'' ⟨hcs, hsp, hm, hx0, _, _⟩ => ?_
    refine ⟨⟨fun r hr => by rw [hcs r hr]; exact o1.get r (fun e => by
        simp only [List.mem_singleton] at e; subst e; revert hr; decide), by rw [hsp]; rfl⟩, ?_⟩
    sig_post [signMessageContract, signMessageSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    rw [formatMessage_some (by rw [Proof.MlKem.bytesAt_length]; exact h8)]
    simp only [signInternal, messageRep, skTr]
    have hm₀ : s1.mem = s.mem := o1.mem
    have ek : bytesAt t₁.mem (State.addr (s.gpr .r0)) p.skLen = bytesAt s.mem (State.addr (s.gpr .r0)) p.skLen :=
      (hc₁.bytesAt_eq (p := State.addr (VG.Proof.MlDsa.Arm.Message.slay p s).key) (n := p.skLen) hL.xKey hL.kKey (by have := h.nSk; omega)).trans
        (by rw [hm₀]; rfl)
    have er : bytesAt t₁.mem (State.addr (stackArg s 1)) 32 = bytesAt s.mem (State.addr (stackArg s 1)) 32 :=
      (hc₁.bytesAt_eq (p := State.addr (VG.Proof.MlDsa.Arm.Message.slay p s).rnd) (n := 32) h.rndScr.symm h.stkRnd (by decide)).trans
        (by rw [hm₀]; rfl)
    have etr : bytesAt t.mem (State.addr ((VG.Proof.MlDsa.Arm.Message.slay p s).key + BitVec.ofNat 32 64)) 64 =
        ((bytesAt s.mem (State.addr (s.gpr .r0)) p.skLen).drop 64).take 64 := by
      rw [hc.bytesAt_eq (hL.xKey.sub_right wtr.sub) (hL.kKey.sub_right wtr.sub) (by decide), hm₀, ekey,
        Proof.MlKem.bytesAt_slice _ _ (by omega)]
      rfl
    rw [ek, er, hμ, etr, hm₀] at hq
    rw [Proof.MlKem.Arm.setWidth_append32, hx0, hm]
    simp only [VG.Proof.MlDsa.Arm.Message.hdrBytes, Proof.MlKem.bytesAt_length, List.append_assoc] at hq ⊢
    exact hq
  · rw [decide_eq_true (by simpa using h8)] at hc1
    refine VG.Proof.MlDsa.Arm.Message.wp_ite_t hc1 (VG.Proof.MlDsa.Arm.Message.wp_movImm (by decide) fun s2 o2 e2 => VG.Proof.MlDsa.Arm.Message.wp_nil ⟨⟨fun r hr => ?_, by rw [o2.sp, o1.sp]⟩, ?_⟩)
    · have h0 : r ∉ [Reg.r0] := fun e => by simp only [List.mem_singleton] at e; subst e; revert hr; decide
      have h12 : r ∉ [Reg.r12] := fun e => by simp only [List.mem_singleton] at e; subst e; revert hr; decide
      rw [o2.gpr r h0, o1.gpr r h12]
    · sig_post [signMessageContract, signMessageSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
      rw [formatMessage_none (by rw [Proof.MlKem.bytesAt_length]; omega), Proof.MlKem.Arm.setWidth_append32, e2]

end VG.Proof.MlDsa.Arm.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Message.VerifyCorrect`. -/
section

/-!
# ML-DSA on ARMv7, `verify_message`: correctness

Untrusted: everything here is checked by Lean. From a state satisfying
`verifyMessageContract p Arm.abi 36`, `verifyMessage n c p` returns 2 if
the context string is longer than 255 bytes; otherwise it computes
`tr = H(pk, 64)`, then `μ` of the formatted message, and calls the
verification function on `μ` `c`, which gives the result of
`ML-DSA.Verify_internal` on the formatted message (`verifyMessage_wp`).
-/

namespace VG.Proof.MlDsa.Arm.Message

open VG VG.Arm VG.Impl.MlDsa.Arm.Message
open VG.Proof.MlDsa.Message
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- The words on the stack of a state satisfying `VPre` are readable. -/
theorem VPre.args {p : Params} {s : State} (h : VG.Proof.MlDsa.Arm.Message.VPre p s) {o : Nat} (ho : o + 4 ≤ 12) :
    InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 o)) 4 := by
  refine ⟨VG.Proof.MlDsa.Arm.Message.rArgs s 12, by simp [h.rd], ?_⟩
  simp only [VG.Proof.MlDsa.Arm.Message.rArgs, VG.Proof.MlDsa.Arm.Message.stackArgAddr0]
  rw [addr_add (by have := h.spA; omega)]
  exact Offset.contains_base _ ho (by omega)

theorem verifyMessage_wp {p : Params} {n : String} {c : Prog isa}
    (hV : VG.Proof.MlDsa.Arm.Message.VerifyFn p c) (hp : p ∈ VG.Proof.MlDsa.Arm.Message.params) {s : State} (hpre : (verifyMessageContract p Arm.abi 36).pre s) :
    WP isa (verifyMessage n c p) s fun s' =>
      abiPreserved s s' ∧ (verifyMessageContract p Arm.abi 36).post s s' := by
  have h := VG.Proof.MlDsa.Arm.Message.vPre_of hpre
  unfold verifyMessage top
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Message.chk_ok (h.args (by omega))) fun s1 ⟨o1, hc1⟩ => ?_)
  by_cases h8 : (stackArg s 0).toNat < 256
  · rw [decide_eq_false (by simpa using h8)] at hc1
    have hL := VG.Proof.MlDsa.Arm.Message.vlay_ok hp h h8
    have hs1 : ∀ o, o + 4 ≤ 12 → s1.mem.readW (State.addr (s1.sp + BitVec.ofNat 32 o)) 32 =
        s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 o)) 32 := fun _ _ => by rw [o1.mem, o1.sp]
    refine VG.Proof.MlDsa.Arm.Message.wp_ite_f hc1 (WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Message.enter_ok hL rfl (nA := 12) (by decide) (by omega) (o1.sp)
      (by rw [o1.rd]; rfl) (by rw [o1.wr]; rfl) (o1.get .r0) (o1.get .r1) (o1.get .r2) (o1.get .r3)
      (fun o ho => by rw [o1.rd, o1.wr, o1.sp]; exact h.args ho) (by rw [o1.sp]; exact h.spA)
      (by rw [o1.sp, ← VG.Proof.MlDsa.Arm.Message.stackArgAddr0]; exact h.scrArgs) (by omega)
      (by rw [hs1 8 (by omega)]; exact VG.Proof.MlDsa.Arm.Message.stackArg_eq s 2) (by decide) (fun j hj => by
        have hj4 : j < 4 := hj
        rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
        · exact (hs1 0 (by decide)).trans (VG.Proof.MlDsa.Arm.Message.stackArg_eq s 0)
        · exact (hs1 4 (by decide)).trans (VG.Proof.MlDsa.Arm.Message.stackArg_eq s 1)
        · exact (hs1 4 (by decide)).trans (VG.Proof.MlDsa.Arm.Message.stackArg_eq s 1)
        · exact (hs1 8 (by decide)).trans (VG.Proof.MlDsa.Arm.Message.stackArg_eq s 2))) fun t hc => ?_))
    refine WP.seq (WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Message.trHash_ok hL rfl hc) fun t₁ ⟨hc₁, htr⟩ => ?_))
    have hmu := VG.Proof.MlDsa.Arm.Message.mu_eq hL
    have hfit : ((VG.Proof.MlDsa.Arm.Message.vlay p s).X32 + BitVec.ofNat 32 840).toNat + 64 ≤ 2 ^ 32 := by
      have := hL.x32_lt; rw [VG.Proof.MlDsa.Arm.Message.x32_toNat hL (by omega)]; omega
    obtain ⟨R, hR, hw⟩ := hL.covX (e := 840) (k := 64) (by omega)
    refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Message.muHash_ok hL hc₁ (tr := .off oMU) (trp := (VG.Proof.MlDsa.Arm.Message.vlay p s).X32 + BitVec.ofNat 32 840)
      (by decide) rfl (fun t' hc' => hc'.off oMU) hfit
      (by rw [hmu]; exact ⟨R, by simp [hR], hw⟩) (by rw [hmu]; exact st_mu.symm) (by rw [hmu]; exact VG.Proof.MlDsa.Arm.Message.mu_ks)
      (by rw [hmu]; exact VG.Proof.MlDsa.Arm.Message.k_mu hL)) fun t₂ ⟨hc₂, hμ⟩ => ?_)
    refine WP.mono (VG.Proof.MlDsa.Arm.Message.verifyCall_ok hV hp h h8 hc₂) fun s' ⟨hf, hq⟩ => ?_
    refine WP.mono (VG.Proof.MlDsa.Arm.Message.leave_ok hL hf) fun s'' ⟨hcs, hsp, hm, hx0, _, _⟩ => ?_
    refine ⟨⟨fun r hr => by rw [hcs r hr]; exact o1.get r (fun e => by
        simp only [List.mem_singleton] at e; subst e; revert hr; decide), by rw [hsp]; rfl⟩, ?_⟩
    sig_post [verifyMessageContract, verifyMessageSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    rw [formatMessage_some (by rw [Proof.MlKem.bytesAt_length]; exact h8)]
    simp only [verifyInternal, messageRep, pkTr]
    have hm₀ : s1.mem = s.mem := o1.mem
    have ek : bytesAt t₂.mem (State.addr (s.gpr .r0)) p.pkLen = bytesAt s.mem (State.addr (s.gpr .r0)) p.pkLen :=
      (hc₂.bytesAt_eq (p := State.addr (VG.Proof.MlDsa.Arm.Message.vlay p s).key) (n := p.pkLen) hL.xKey hL.kKey
        (by have := h.nPk; omega)).trans (by rw [hm₀]; rfl)
    have es : bytesAt t₂.mem (State.addr (stackArg s 1)) p.sigLen =
        bytesAt s.mem (State.addr (stackArg s 1)) p.sigLen :=
      (hc₂.bytesAt_eq (p := State.addr (VG.Proof.MlDsa.Arm.Message.vlay p s).sig) (n := p.sigLen) h.sigScr.symm h.stkSig
        (by have := h.nSig; omega)).trans (by rw [hm₀]; rfl)
    have hμ' := hμ
    rw [hmu, htr, hm₀] at hμ'
    rw [ek, es, hμ'] at hq
    rw [Proof.MlKem.Arm.setWidth_append32, hx0]
    simp only [VG.Proof.MlDsa.Arm.Message.hdrBytes, Proof.MlKem.bytesAt_length, List.append_assoc] at hq ⊢
    exact hq
  · rw [decide_eq_true (by simpa using h8)] at hc1
    refine VG.Proof.MlDsa.Arm.Message.wp_ite_t hc1 (VG.Proof.MlDsa.Arm.Message.wp_movImm (by decide) fun s2 o2 e2 => VG.Proof.MlDsa.Arm.Message.wp_nil ⟨⟨fun r hr => ?_, by rw [o2.sp, o1.sp]⟩, ?_⟩)
    · have h0 : r ∉ [Reg.r0] := fun e => by simp only [List.mem_singleton] at e; subst e; revert hr; decide
      have h12 : r ∉ [Reg.r12] := fun e => by simp only [List.mem_singleton] at e; subst e; revert hr; decide
      rw [o2.gpr r h0, o1.gpr r h12]
    · sig_post [verifyMessageContract, verifyMessageSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
      rw [formatMessage_none (by rw [Proof.MlKem.bytesAt_length]; omega), Proof.MlKem.Arm.setWidth_append32, e2]

end VG.Proof.MlDsa.Arm.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Message.Rel`. -/
section

/-!
# ML-DSA on ARMv7, `sign_message` and `verify_message`: two runs

Untrusted: everything here is checked by Lean. Blocks whose addresses are
functions of `r7`, which they keep, leak the same in runs that agree on it
(`block_r7_tr`): the moves of a call's arguments are such (`setArgs_r7`).
Two runs with the same layout, each in `Ctx` with inputs related by `I`
(`Two`), and the moves of a call's arguments in them (`setArgs_two`).
-/

namespace VG.Proof.MlDsa.Arm.Message

open VG VG.Arm VG.Impl.MlDsa.Arm.Message
open VG.Proof.MlDsa.Message

/-! ## Blocks addressed from `r7` -/

/-- An instruction whose addresses are a function of `r7`, which it keeps. -/
def R7Only (i : Instr) : Prop :=
  (∀ s₁ s₂ : State, s₁.gpr .r7 = s₂.gpr .r7 → isa.addrs i s₁ = isa.addrs i s₂) ∧ dstOf i ≠ some .r7

theorem execBlock_r7_tr : ∀ {is : List Instr}, (∀ i ∈ is, VG.Proof.MlDsa.Arm.Message.R7Only i) →
    ∀ {s₁ s₂ s₁' s₂' : State} {t₁ t₂ : List Leak}, s₁.gpr .r7 = s₂.gpr .r7 →
      execBlock isa is s₁ = some (s₁', t₁) → execBlock isa is s₂ = some (s₂', t₂) → t₁ = t₂
  | [], _, _, _, _, _, _, _, _, e₁, e₂ => by
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e₁ e₂
    rw [← e₁.2, ← e₂.2]
  | i :: is, h, s₁, s₂, s₁', s₂', t₁, t₂, h7, e₁, e₂ => by
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
    have h7' : a₁.gpr .r7 = a₂.gpr .r7 := by rw [exec_gpr hi.2 ha₁, exec_gpr hi.2 ha₂, h7]
    have ht := VG.Proof.MlDsa.Arm.Message.execBlock_r7_tr (fun j hj => h j (List.mem_cons_of_mem _ hj)) h7' eb₁ eb₂
    rw [show addrs i s₁ = addrs i s₂ from hi.1 _ _ h7, ht]

theorem block_r7_tr {is : List Instr} (h : ∀ i ∈ is, VG.Proof.MlDsa.Arm.Message.R7Only i) {P : State → State → Prop}
    (hp : ∀ a b, P a b → a.gpr .r7 = b.gpr .r7) : RelCT isa P (.block is) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hP e₁ e₂
  rw [Exec.block_iff] at e₁ e₂
  exact ⟨VG.Proof.MlDsa.Arm.Message.execBlock_r7_tr h (hp _ _ hP) e₁ e₂, trivial⟩

theorem arg_r7 (d : Reg) (hd : d ≠ .r7) (a : VG.Impl.MlDsa.Arm.Message.Arg) : ∀ i ∈ a.mov d, VG.Proof.MlDsa.Arm.Message.R7Only i := by
  intro i hi
  cases a <;> simp only [Arg.mov, List.mem_cons, List.not_mem_nil, or_false] at hi <;>
    (try rcases hi with rfl | rfl) <;> (try subst hi) <;>
    exact ⟨fun s₁ s₂ h => by simp [addrs, h], by simpa [dstOf] using hd⟩

theorem setArgs_r7 {as : List (Reg × VG.Impl.MlDsa.Arm.Message.Arg)} (h : VG.Proof.MlDsa.Arm.Message.argsOk as = true) : ∀ i ∈ VG.Impl.MlDsa.Arm.Message.setArgs as, VG.Proof.MlDsa.Arm.Message.R7Only i := by
  induction as with
  | nil => intro i hi; simp [VG.Impl.MlDsa.Arm.Message.setArgs] at hi
  | cons da as ih =>
    obtain ⟨d, a⟩ := da
    simp only [VG.Proof.MlDsa.Arm.Message.argsOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    intro i hi
    simp only [VG.Impl.MlDsa.Arm.Message.setArgs, List.flatMap_cons, List.mem_append] at hi
    rcases hi with hi | hi
    · exact VG.Proof.MlDsa.Arm.Message.arg_r7 d h.1.1.2 a i hi
    · exact ih h.2 i hi

/-- A relation proved through the final states' facts, from those of each run. -/
theorem RelCT.postDep {P Q : State → State → Prop} {c : Prog isa} {F : State → State → Prop}
    (h : RelCT isa P c fun _ _ => True) (hw : ∀ x y, P x y → WP isa c x (F x) ∧ WP isa c y (F y))
    (hQ : ∀ x y x' y', P x y → F x x' → F y y' → Q x' y') : RelCT isa P c Q :=
  RelCT.mono (RelCT.wpDep h hw) (fun _ _ h => h) fun _ _ ⟨_, _, _, hp, f₁, f₂⟩ => hQ _ _ _ _ hp f₁ f₂

/-! ## Runs related through their entry states -/

/-- Two runs whose states are related to entry states `x`, `y` by `A`, with
`P x y`. -/
def Ghost (P A : State → State → Prop) (a b : State) : Prop := ∃ x y, P x y ∧ A x a ∧ A y b

/-- What each run satisfies by correctness, from its entry state, carries over. -/
theorem ghost_step {P A B : State → State → Prop} {c : Prog isa}
    (hct : RelCT isa (VG.Proof.MlDsa.Arm.Message.Ghost P A) c fun _ _ => True)
    (hw : ∀ x y a b, P x y → A x a → A y b → WP isa c a (B x) ∧ WP isa c b (B y)) :
    RelCT isa (VG.Proof.MlDsa.Arm.Message.Ghost P A) c (VG.Proof.MlDsa.Arm.Message.Ghost P B) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨x, y, hxy, a₁, a₂⟩ := hp
  obtain ⟨⟨_, u₁, x₁, y₁⟩, ⟨_, u₂, x₂, y₂⟩⟩ := hw x y s₁ s₂ hxy a₁ a₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, x, y, hxy, y₁, y₂⟩

/-- Code the taint analysis proves constant time from the registers `rs`
and the first `n` bytes of stack arguments, on which runs related by `R`
agree. -/
theorem argRel {R : State → State → Prop} {c : Prog isa} (rs : List Reg) (n : Nat)
    (hr : ∀ x y, R x y → VG.Arm.Taint.Agree (argTaint rs n) x y) {hc : VG.Taint.Hint VG.Arm.taint.T}
    (h : (VG.Arm.taint.check (argTaint rs n) c hc).isSome = true) : RelCT isa R c fun _ _ => True :=
  RelCT.taint (A := VG.Arm.taint) (argTaint rs n) hr h

/-- Code the taint analysis proves constant time from the registers `rs`. -/
theorem taintRel {R : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hr : ∀ x y, R x y → ∀ r ∈ rs, x.gpr r = y.gpr r) {hc : VG.Taint.Hint VG.Arm.taint.T}
    (h : (VG.Arm.taint.check (Taint.ofRegs rs) c hc).isSome = true) : RelCT isa R c fun _ _ => True :=
  RelCT.taint (A := VG.Arm.taint) (Taint.ofRegs rs) (fun a b hab => Taint.agree_ofRegs (hr a b hab)) h

/-! ## Two runs -/

/-- Two runs with the layout `L`, inputs related by `I`, each satisfying `Φ`. -/
def Two (I : VG.Proof.MlDsa.Arm.Message.Lay → Mem → Mem → Prop) (Φ : VG.Proof.MlDsa.Arm.Message.Lay → Mem → State → Prop) (a b : State) : Prop :=
  ∃ (L : VG.Proof.MlDsa.Arm.Message.Lay) (g₁ g₂ : Reg → BitVec 32) (m₁ m₂ : Mem), L.Ok ∧ I L m₁ m₂ ∧
    VG.Proof.MlDsa.Arm.Message.Ctx L g₁ m₁ a ∧ VG.Proof.MlDsa.Arm.Message.Ctx L g₂ m₂ b ∧ Φ L m₁ a ∧ Φ L m₂ b

section
variable {I : VG.Proof.MlDsa.Arm.Message.Lay → Mem → Mem → Prop}

theorem Two.r7 {Φ : VG.Proof.MlDsa.Arm.Message.Lay → Mem → State → Prop} {a b : State} (h : VG.Proof.MlDsa.Arm.Message.Two I Φ a b) :
    a.gpr .r7 = b.gpr .r7 ∧ a.sp = b.sp :=
  let ⟨_, _, _, _, _, _, _, c₁, c₂, _, _⟩ := h
  ⟨c₁.r7.trans c₂.r7.symm, c₁.sp.trans c₂.sp.symm⟩

theorem two_wp {c : Prog isa} {Φ Ψ : VG.Proof.MlDsa.Arm.Message.Lay → Mem → State → Prop}
    (hct : RelCT isa (VG.Proof.MlDsa.Arm.Message.Two I Φ) c fun _ _ => True)
    (hw : ∀ (L : VG.Proof.MlDsa.Arm.Message.Lay) g m₀ (t : State), L.Ok → VG.Proof.MlDsa.Arm.Message.Ctx L g m₀ t → Φ L m₀ t →
      WP isa c t fun t' => VG.Proof.MlDsa.Arm.Message.Ctx L g m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (VG.Proof.MlDsa.Arm.Message.Two I Φ) c (VG.Proof.MlDsa.Arm.Message.Two I Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨L, g₁, g₂, m₁, m₂, hL, hi, c₁, c₂, f₁, f₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw L g₁ m₁ s₁ hL c₁ f₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw L g₂ m₂ s₂ hL c₂ f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, L, g₁, g₂, m₁, m₂, hL, hi, y₁.1, y₂.1, y₁.2, y₂.2⟩

/-- What the moves of the arguments `as` leave. -/
abbrev Moved (as : List (Reg × VG.Impl.MlDsa.Arm.Message.Arg)) (t t1 : State) : Prop :=
  (∀ da ∈ as, t1.gpr da.1 = da.2.val t) ∧ VG.Proof.MlDsa.Arm.Message.Only (as.map (·.1)) t t1

/-- The moves of a call's arguments in two runs. -/
theorem setArgs_two {Φ : VG.Proof.MlDsa.Arm.Message.Lay → Mem → State → Prop} {as : List (Reg × VG.Impl.MlDsa.Arm.Message.Arg)} (hok : VG.Proof.MlDsa.Arm.Message.argsOk as = true) :
    RelCT isa (VG.Proof.MlDsa.Arm.Message.Two I Φ) (.block (VG.Impl.MlDsa.Arm.Message.setArgs as)) fun a1 b1 => ∃ a b, VG.Proof.MlDsa.Arm.Message.Two I Φ a b ∧ VG.Proof.MlDsa.Arm.Message.Moved as a a1 ∧ VG.Proof.MlDsa.Arm.Message.Moved as b b1 :=
  RelCT.postDep (VG.Proof.MlDsa.Arm.Message.block_r7_tr (VG.Proof.MlDsa.Arm.Message.setArgs_r7 hok) fun _ _ h => h.r7.1)
    (fun x y ⟨_, _, _, _, _, hL, _, c₁, c₂, _, _⟩ =>
      ⟨VG.Proof.MlDsa.Arm.Message.setArgs_ok as hok x (c₁.xOk hL), VG.Proof.MlDsa.Arm.Message.setArgs_ok as hok y (c₂.xOk hL)⟩)
    fun x y _ _ hp f₁ f₂ => ⟨x, y, hp, f₁, f₂⟩

end

end VG.Proof.MlDsa.Arm.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Message.HashCT`. -/
section

/-!
# ML-DSA on ARMv7, `sign_message` and `verify_message`: two runs of the hashing

Untrusted: everything here is checked by Lean. In two runs with the same
layout (`Two`), zeroing the state and each call of a sponge function leak
the same: their addresses and arguments are functions of the layout alone,
and ML-KEM's lemmas on two runs of the sponge functions' calls need just that
(`zeroSt_tr`, `kabs_tr`, `kpad_tr`, `ksqz_tr`); so do `muHash` and `trHash`.
-/

namespace VG.Proof.MlDsa.Arm.Message

open VG VG.Arm VG.Impl.MlDsa.Arm.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.Arm (AbsorbArgs PadArgs SqueezeArgs absorb_ct pad_ct squeeze_ct regA)
open VG.Spec.MlDsa (Params)

section
variable {I : VG.Proof.MlDsa.Arm.Message.Lay → Mem → Mem → Prop}

/-! ## Zeroing the state -/

theorem zeroSt_taint : (VG.Arm.taint.check (Taint.ofRegs [.r7]) (.block zeroSt) (.block [])).isSome = true := by
  rfl

theorem zeroSt_tr {Φ : VG.Proof.MlDsa.Arm.Message.Lay → Mem → State → Prop} : RelCT isa (VG.Proof.MlDsa.Arm.Message.Two I Φ) (.block zeroSt) fun _ _ => True :=
  VG.Proof.MlDsa.Arm.Message.taintRel [.r7] (fun _ _ h r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.r7.1) VG.Proof.MlDsa.Arm.Message.zeroSt_taint

/-! ## The sponge functions -/

theorem absA_of {L : VG.Proof.MlDsa.Arm.Message.Lay} (hL : L.Ok) {g : Reg → BitVec 32} {m₀ : Mem} {t t1 : State}
    (hc : VG.Proof.MlDsa.Arm.Message.Ctx L g m₀ t) {src len pos : VG.Impl.MlDsa.Arm.Message.Arg} (hm : VG.Proof.MlDsa.Arm.Message.Moved (VG.Proof.MlDsa.Arm.Message.absArgs src len pos) t t1) {dp : BitVec 32} {n q : Nat}
    (hdp : src.val t = dp) (hn : len.val t = BitVec.ofNat 32 n) (hq : pos.val t = BitVec.ofNat 32 q)
    (hql : q < 136) (hnl : n < 2 ^ 32) (hfit : dp.toNat + n ≤ 2 ^ 32)
    (hin : ∃ R ∈ L.rd ++ L.wr, Within ⟨State.addr dp, n⟩ R)
    (dS : Region.Disjoint ⟨State.addr dp, n⟩ ⟨L.ST, 200⟩) (dK : Region.Disjoint ⟨State.addr dp, n⟩ ⟨L.KS, 640⟩)
    (kD : L.STK.Disjoint ⟨State.addr dp, n⟩) :
    AbsorbArgs t1 L.X32 (L.X32 + BitVec.ofNat 32 200) dp 136 q n := by
  have hs1 : t1.sp = L.SP := hm.2.sp.trans hc.sp
  have e2 := hm.1 (.r2, pos) (by simp)
  have e0 := hm.1 (.r0, .off oST) (by simp)
  have e1 := hm.1 (.r1, .imm 136) (by simp)
  have e3 := hm.1 (.r3, src) (by simp)
  have e4 := hm.1 (.r12, len) (by simp)
  have e5 := hm.1 (.lr, .off oKS) (by simp)
  simp only [Arg.val, hc.r7, oST, oKS, VG.Proof.MlDsa.Arm.Message.x0'] at e0 e1 e5
  rw [hq] at e2
  rw [hdp] at e3
  rw [hn] at e4
  have bs := VG.Proof.MlDsa.Arm.Message.below_stk hs1
  have hks := VG.Proof.MlDsa.Arm.Message.ks_eq hL
  have hcw : Covers [VG.Proof.MlKem.Arm.regA L.X32 200, VG.Proof.MlKem.Arm.regA (L.X32 + BitVec.ofNat 32 200) 640] t1.wr := by
    simp only [VG.Proof.MlKem.Arm.regA, hks, hm.2.wr, hc.wr]
    refine VG.Proof.MlDsa.Arm.Message.covers_of_within fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact VG.Proof.MlDsa.Arm.Message.cov_xw0 hL
    · exact hL.covX (e := 200) (by omega)
  exact ⟨e0, e1, e2, e3, e4, e5, by decide, hql, hnl, by rw [hs1]; have := hL.nSP; omega,
    by have := hL.x32_lt; omega, hfit, by rw [VG.Proof.MlDsa.Arm.Message.x32_toNat hL (by omega)]; have := hL.x32_lt; omega,
    by simp only [VG.Proof.MlKem.Arm.regA, hks]; exact VG.Proof.MlDsa.Arm.Message.st_ks, by simp only [VG.Proof.MlKem.Arm.regA]; exact dS,
    by simp only [VG.Proof.MlKem.Arm.regA, hks]; exact dK,
    by simp only [VG.Proof.MlKem.Arm.regA]; exact (VG.Proof.MlDsa.Arm.Message.k_st hL).sub_left bs, by simp only [VG.Proof.MlKem.Arm.regA, hks]; exact (VG.Proof.MlDsa.Arm.Message.k_ks hL).sub_left bs,
    by simp only [VG.Proof.MlKem.Arm.regA]; exact kD.sub_left bs, hcw,
    by simp only [VG.Proof.MlKem.Arm.regA, hm.2.rd, hm.2.wr, hc.rd, hc.wr]
       exact VG.Proof.MlDsa.Arm.Message.covers_of_within fun r hr => by
         simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; exact hin⟩

/-- Two runs of a call of `vg_keccak_absorb` whose arguments are the same
functions of the layout in both. -/
theorem kabs_tr {Φ : VG.Proof.MlDsa.Arm.Message.Lay → Mem → State → Prop} {src len pos : VG.Impl.MlDsa.Arm.Message.Arg}
    (hok : VG.Proof.MlDsa.Arm.Message.argsOk (VG.Proof.MlDsa.Arm.Message.absArgs src len pos) = true) (dp : VG.Proof.MlDsa.Arm.Message.Lay → BitVec 32) (n q : VG.Proof.MlDsa.Arm.Message.Lay → Nat)
    (hv : ∀ (L : VG.Proof.MlDsa.Arm.Message.Lay) g m (t : State), L.Ok → VG.Proof.MlDsa.Arm.Message.Ctx L g m t → Φ L m t →
      src.val t = dp L ∧ len.val t = BitVec.ofNat 32 (n L) ∧ pos.val t = BitVec.ofNat 32 (q L))
    (hs : ∀ L : VG.Proof.MlDsa.Arm.Message.Lay, L.Ok → q L < 136 ∧ n L < 2 ^ 32 ∧ (dp L).toNat + n L ≤ 2 ^ 32 ∧
      (∃ R ∈ L.rd ++ L.wr, Within ⟨State.addr (dp L), n L⟩ R) ∧
      Region.Disjoint ⟨State.addr (dp L), n L⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨State.addr (dp L), n L⟩ ⟨L.KS, 640⟩ ∧
      L.STK.Disjoint ⟨State.addr (dp L), n L⟩) :
    RelCT isa (VG.Proof.MlDsa.Arm.Message.Two I Φ) (VG.Impl.MlDsa.Arm.Message.kabs src len pos) fun _ _ => True := by
  refine RelCT.seq (VG.Proof.MlDsa.Arm.Message.setArgs_two hok) (absorb_ct fun a1 b1 ⟨a, b, ⟨L, g₁, g₂, m₁, m₂, hL, _, c₁, c₂, φ₁, φ₂⟩, f₁, f₂⟩ =>
    ⟨by rw [f₁.2.sp, f₂.2.sp, c₁.sp, c₂.sp], L.X32, L.X32 + BitVec.ofNat 32 200, dp L, 136, q L, n L, ?_, ?_⟩)
  · obtain ⟨h1, h2, h3⟩ := hv L g₁ m₁ a hL c₁ φ₁
    obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := hs L hL
    exact VG.Proof.MlDsa.Arm.Message.absA_of hL c₁ f₁ h1 h2 h3 s1 s2 s3 s4 s5 s6 s7
  · obtain ⟨h1, h2, h3⟩ := hv L g₂ m₂ b hL c₂ φ₂
    obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := hs L hL
    exact VG.Proof.MlDsa.Arm.Message.absA_of hL c₂ f₂ h1 h2 h3 s1 s2 s3 s4 s5 s6 s7

theorem padA_of {L : VG.Proof.MlDsa.Arm.Message.Lay} (hL : L.Ok) {g : Reg → BitVec 32} {m₀ : Mem} {t t1 : State}
    (hc : VG.Proof.MlDsa.Arm.Message.Ctx L g m₀ t) {pos : VG.Impl.MlDsa.Arm.Message.Arg} (hm : VG.Proof.MlDsa.Arm.Message.Moved (VG.Proof.MlDsa.Arm.Message.padArgs pos) t t1) {q : Nat}
    (hq : pos.val t = BitVec.ofNat 32 q) (hql : q < 136) :
    PadArgs t1 L.X32 (L.X32 + BitVec.ofNat 32 200) 136 q (BitVec.ofNat 32 0x1f) := by
  have hs1 : t1.sp = L.SP := hm.2.sp.trans hc.sp
  have e2 := hm.1 (.r2, pos) (by simp)
  have e0 := hm.1 (.r0, .off oST) (by simp)
  have e1 := hm.1 (.r1, .imm 136) (by simp)
  have e3 := hm.1 (.r3, .imm 0x1f) (by simp)
  have e4 := hm.1 (.lr, .off oKS) (by simp)
  simp only [Arg.val, hc.r7, oST, oKS, VG.Proof.MlDsa.Arm.Message.x0'] at e0 e1 e3 e4
  rw [hq] at e2
  have bs := VG.Proof.MlDsa.Arm.Message.below_stk hs1
  have hks := VG.Proof.MlDsa.Arm.Message.ks_eq hL
  exact ⟨e0, e1, e2, e3, e4, by decide, hql, by rw [hs1]; have := hL.nSP; omega,
    by have := hL.x32_lt; omega, by rw [VG.Proof.MlDsa.Arm.Message.x32_toNat hL (by omega)]; have := hL.x32_lt; omega,
    by simp only [VG.Proof.MlKem.Arm.regA, hks]; exact VG.Proof.MlDsa.Arm.Message.st_ks,
    by simp only [VG.Proof.MlKem.Arm.regA]; exact (VG.Proof.MlDsa.Arm.Message.k_st hL).sub_left bs, by simp only [VG.Proof.MlKem.Arm.regA, hks]; exact (VG.Proof.MlDsa.Arm.Message.k_ks hL).sub_left bs,
    by simp only [VG.Proof.MlKem.Arm.regA, hks, hm.2.wr, hc.wr]
       exact VG.Proof.MlDsa.Arm.Message.covers_of_within fun r hr => by
         simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
         rcases hr with rfl | rfl
         · exact VG.Proof.MlDsa.Arm.Message.cov_xw0 hL
         · exact hL.covX (e := 200) (by omega)⟩

theorem kpad_tr {Φ : VG.Proof.MlDsa.Arm.Message.Lay → Mem → State → Prop} {pos : VG.Impl.MlDsa.Arm.Message.Arg}
    (hok : VG.Proof.MlDsa.Arm.Message.argsOk (VG.Proof.MlDsa.Arm.Message.padArgs pos) = true) (q : VG.Proof.MlDsa.Arm.Message.Lay → Nat)
    (hv : ∀ (L : VG.Proof.MlDsa.Arm.Message.Lay) g m (t : State), L.Ok → VG.Proof.MlDsa.Arm.Message.Ctx L g m t → Φ L m t → pos.val t = BitVec.ofNat 32 (q L))
    (hs : ∀ L : VG.Proof.MlDsa.Arm.Message.Lay, L.Ok → q L < 136) :
    RelCT isa (VG.Proof.MlDsa.Arm.Message.Two I Φ) (VG.Impl.MlDsa.Arm.Message.kpad pos) fun _ _ => True :=
  RelCT.seq (VG.Proof.MlDsa.Arm.Message.setArgs_two hok) (pad_ct fun a1 b1 ⟨a, b, ⟨L, g₁, g₂, m₁, m₂, hL, _, c₁, c₂, φ₁, φ₂⟩, f₁, f₂⟩ =>
    ⟨by rw [f₁.2.sp, f₂.2.sp, c₁.sp, c₂.sp], L.X32, L.X32 + BitVec.ofNat 32 200, 136, q L,
      BitVec.ofNat 32 0x1f, VG.Proof.MlDsa.Arm.Message.padA_of hL c₁ f₁ (hv L g₁ m₁ a hL c₁ φ₁) (hs L hL),
      VG.Proof.MlDsa.Arm.Message.padA_of hL c₂ f₂ (hv L g₂ m₂ b hL c₂ φ₂) (hs L hL)⟩)

theorem sqzA_of {L : VG.Proof.MlDsa.Arm.Message.Lay} (hL : L.Ok) {g : Reg → BitVec 32} {m₀ : Mem} {t t1 : State}
    (hc : VG.Proof.MlDsa.Arm.Message.Ctx L g m₀ t) (hm : VG.Proof.MlDsa.Arm.Message.Moved VG.Proof.MlDsa.Arm.Message.sqzArgs t t1) :
    SqueezeArgs t1 L.X32 (L.X32 + BitVec.ofNat 32 200) (L.X32 + BitVec.ofNat 32 840) 136 0 64 := by
  have hs1 : t1.sp = L.SP := hm.2.sp.trans hc.sp
  have e0 := hm.1 (.r0, .off oST) (by simp)
  have e1 := hm.1 (.r1, .imm 136) (by simp)
  have e2 := hm.1 (.r2, .imm 0) (by simp)
  have e3 := hm.1 (.r3, .off oMU) (by simp)
  have e4 := hm.1 (.r12, .imm 64) (by simp)
  have e5 := hm.1 (.lr, .off oKS) (by simp)
  simp only [Arg.val, hc.r7, oST, oKS, oMU, VG.Proof.MlDsa.Arm.Message.x0'] at e0 e1 e2 e3 e4 e5
  have bs := VG.Proof.MlDsa.Arm.Message.below_stk hs1
  have hks := VG.Proof.MlDsa.Arm.Message.ks_eq hL
  have hmu := VG.Proof.MlDsa.Arm.Message.mu_eq hL
  exact ⟨e0, e1, e2, e3, e4, e5, by decide, by decide, by decide, by rw [hs1]; have := hL.nSP; omega,
    by have := hL.x32_lt; omega, by rw [VG.Proof.MlDsa.Arm.Message.x32_toNat hL (by omega)]; have := hL.x32_lt; omega,
    by rw [VG.Proof.MlDsa.Arm.Message.x32_toNat hL (by omega)]; have := hL.x32_lt; omega,
    by simp only [VG.Proof.MlKem.Arm.regA, hmu]; exact VG.Proof.MlDsa.Arm.Message.st_mu, by simp only [VG.Proof.MlKem.Arm.regA, hks]; exact VG.Proof.MlDsa.Arm.Message.st_ks,
    by simp only [VG.Proof.MlKem.Arm.regA, hks, hmu]; exact VG.Proof.MlDsa.Arm.Message.mu_ks,
    by simp only [VG.Proof.MlKem.Arm.regA]; exact (VG.Proof.MlDsa.Arm.Message.k_st hL).sub_left bs, by simp only [VG.Proof.MlKem.Arm.regA, hmu]; exact (VG.Proof.MlDsa.Arm.Message.k_mu hL).sub_left bs,
    by simp only [VG.Proof.MlKem.Arm.regA, hks]; exact (VG.Proof.MlDsa.Arm.Message.k_ks hL).sub_left bs,
    by simp only [VG.Proof.MlKem.Arm.regA, hks, hmu, hm.2.wr, hc.wr]
       exact VG.Proof.MlDsa.Arm.Message.covers_of_within fun r hr => by
         simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
         rcases hr with rfl | rfl | rfl
         · exact VG.Proof.MlDsa.Arm.Message.cov_xw0 hL
         · exact hL.covX (e := 840) (by omega)
         · exact hL.covX (e := 200) (by omega)⟩

theorem ksqz_tr {Φ : VG.Proof.MlDsa.Arm.Message.Lay → Mem → State → Prop} : RelCT isa (VG.Proof.MlDsa.Arm.Message.Two I Φ) VG.Impl.MlDsa.Arm.Message.ksqz fun _ _ => True :=
  RelCT.seq (VG.Proof.MlDsa.Arm.Message.setArgs_two (by decide)) (squeeze_ct fun a1 b1 ⟨a, b, ⟨L, g₁, g₂, m₁, m₂, hL, _, c₁, c₂, _, _⟩, f₁, f₂⟩ =>
    ⟨by rw [f₁.2.sp, f₂.2.sp, c₁.sp, c₂.sp], L.X32, L.X32 + BitVec.ofNat 32 200, L.X32 + BitVec.ofNat 32 840,
      136, 0, 64, VG.Proof.MlDsa.Arm.Message.sqzA_of hL c₁ f₁, VG.Proof.MlDsa.Arm.Message.sqzA_of hL c₂ f₂⟩)

/-! ## `μ` and `tr` -/

/-- The position after the context string. -/
abbrev qCtx (L : VG.Proof.MlDsa.Arm.Message.Lay) : Nat := (66 + L.ctxLen.toNat) % 136
/-- The position after the message. -/
abbrev qMsg (L : VG.Proof.MlDsa.Arm.Message.Lay) : Nat := (VG.Proof.MlDsa.Arm.Message.qCtx L + L.len.toNat) % 136

theorem muHash_tr {Φ : VG.Proof.MlDsa.Arm.Message.Lay → Mem → State → Prop} {tr : VG.Impl.MlDsa.Arm.Message.Arg}
    (hok : tr.ok = true) (hret : tr.isRet = false) (trp : VG.Proof.MlDsa.Arm.Message.Lay → BitVec 32)
    (htr : ∀ (L : VG.Proof.MlDsa.Arm.Message.Lay) g m (t : State), L.Ok → VG.Proof.MlDsa.Arm.Message.Ctx L g m t → tr.val t = trp L)
    (hs : ∀ L : VG.Proof.MlDsa.Arm.Message.Lay, L.Ok → (trp L).toNat + 64 ≤ 2 ^ 32 ∧ (∃ R ∈ L.rd ++ L.wr, Within ⟨State.addr (trp L), 64⟩ R) ∧
      Region.Disjoint ⟨State.addr (trp L), 64⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨State.addr (trp L), 64⟩ ⟨L.KS, 640⟩ ∧
      L.STK.Disjoint ⟨State.addr (trp L), 64⟩) :
    RelCT isa (VG.Proof.MlDsa.Arm.Message.Two I Φ) (muHash tr) fun _ _ => True := by
  -- The relation keeps only the position in `r0`.
  let Ψ : (VG.Proof.MlDsa.Arm.Message.Lay → Nat) → VG.Proof.MlDsa.Arm.Message.Lay → Mem → State → Prop := fun q L _ t => (t.gpr .r0).toNat = q L
  have z := VG.Proof.MlDsa.Arm.Message.two_wp (I := I) (Φ := Φ) (Ψ := fun _ _ _ => True) VG.Proof.MlDsa.Arm.Message.zeroSt_tr
    fun L g m₀ t hL hc _ => WP.mono (VG.Proof.MlDsa.Arm.Message.zeroSt_ok hL hc) fun t' ⟨hc', _⟩ => ⟨hc', trivial⟩
  have a1 := VG.Proof.MlDsa.Arm.Message.two_wp (I := I) (Ψ := Ψ fun _ => 64)
    (VG.Proof.MlDsa.Arm.Message.kabs_tr (Φ := fun _ _ _ => True) (VG.Proof.MlDsa.Arm.Message.absOk hok rfl rfl hret rfl) trp (fun _ => 64)
      (fun _ => 0) (fun L g m t hL hc _ => ⟨htr L g m t hL hc, rfl, rfl⟩)
      fun L hL => ⟨by decide, by decide, (hs L hL).1, (hs L hL).2.1, (hs L hL).2.2.1, (hs L hL).2.2.2.1,
        (hs L hL).2.2.2.2⟩)
    fun L g m₀ t hL hc _ => by
      obtain ⟨a, b, c, d, e⟩ := hs L hL
      exact WP.mono (VG.Proof.MlDsa.Arm.Message.kabs_ok hL hc (src := tr) (len := .imm 64) (pos := .imm 0) (n := 64) (q := 0)
        (VG.Proof.MlDsa.Arm.Message.absOk hok rfl rfl hret rfl) (htr L g m₀ t hL hc) rfl rfl (by decide)
        (by decide) a b c d e) fun t' ⟨hc', _, _, hx⟩ => ⟨hc', hx⟩
  have hdr : ∀ L : VG.Proof.MlDsa.Arm.Message.Lay, L.Ok → 64 < 136 ∧ 2 < 2 ^ 32 ∧ (L.X32 + BitVec.ofNat 32 944).toNat + 2 ≤ 2 ^ 32 ∧
      (∃ R ∈ L.rd ++ L.wr, Within ⟨State.addr (L.X32 + BitVec.ofNat 32 944), 2⟩ R) ∧
      Region.Disjoint ⟨State.addr (L.X32 + BitVec.ofNat 32 944), 2⟩ ⟨L.ST, 200⟩ ∧
      Region.Disjoint ⟨State.addr (L.X32 + BitVec.ofNat 32 944), 2⟩ ⟨L.KS, 640⟩ ∧
      L.STK.Disjoint ⟨State.addr (L.X32 + BitVec.ofNat 32 944), 2⟩ := fun L hL => by
    rw [hL.xo (by decide)]
    exact ⟨by decide, by decide, by rw [VG.Proof.MlDsa.Arm.Message.x32_toNat hL (by decide)]; have := hL.x32_lt; omega, VG.Proof.MlDsa.Arm.Message.cov_x hL (by omega),
      by have := Offset.disjoint L.X (d := 944) (n := 2) (e := 0) (k := 200) (by omega) (by omega) (by omega)
         simpa only [VG.Proof.MlDsa.Arm.Message.x0] using this,
      Offset.disjoint L.X (d := 944) (n := 2) (e := 200) (k := 640) (by omega) (by omega) (by omega),
      hL.stk_x (by omega)⟩
  have a2 := VG.Proof.MlDsa.Arm.Message.two_wp (I := I) (Φ := Ψ fun _ => 64) (Ψ := Ψ fun _ => 66)
    (VG.Proof.MlDsa.Arm.Message.kabs_tr (src := .off oHdr) (len := .imm 2) (pos := .imm 64) (VG.Proof.MlDsa.Arm.Message.absOk rfl rfl rfl rfl rfl)
      (fun L => L.X32 + BitVec.ofNat 32 944) (fun _ => 2) (fun _ => 64)
      (fun L g m t _ hc _ => ⟨by rw [hc.off]; rfl, rfl, rfl⟩) hdr)
    fun L g m₀ t hL hc _ => by
      obtain ⟨a, b, c, d, e, f, k⟩ := hdr L hL
      exact WP.mono (VG.Proof.MlDsa.Arm.Message.kabs_ok hL hc (src := .off oHdr) (len := .imm 2) (pos := .imm 64) (n := 2) (q := 64)
        (VG.Proof.MlDsa.Arm.Message.absOk rfl rfl rfl rfl rfl) (by rw [hc.off]; rfl) rfl rfl a b c d e f k)
        fun t' ⟨hc', _, _, hx⟩ => ⟨hc', hx⟩
  have ctxS : ∀ L : VG.Proof.MlDsa.Arm.Message.Lay, L.Ok → 66 < 136 ∧ L.ctxLen.toNat < 2 ^ 32 ∧ L.ctx.toNat + L.ctxLen.toNat ≤ 2 ^ 32 ∧
      (∃ R ∈ L.rd ++ L.wr, Within ⟨State.addr L.ctx, L.ctxLen.toNat⟩ R) ∧
      Region.Disjoint ⟨State.addr L.ctx, L.ctxLen.toNat⟩ ⟨L.ST, 200⟩ ∧
      Region.Disjoint ⟨State.addr L.ctx, L.ctxLen.toNat⟩ ⟨L.KS, 640⟩ ∧
      L.STK.Disjoint ⟨State.addr L.ctx, L.ctxLen.toNat⟩ := fun L hL =>
    ⟨by decide, L.ctxLen.isLt, hL.nCtx, ⟨L.CTX, List.mem_append_left _ hL.inCtx, within_self _⟩,
      by have := hL.x_r hL.xCtx (e := 0) (k := 200) (by decide); simpa only [VG.Proof.MlDsa.Arm.Message.x0] using this.symm,
      (hL.x_r hL.xCtx (e := 200) (k := 640) (by decide)).symm, hL.kCtx⟩
  have a3 := VG.Proof.MlDsa.Arm.Message.two_wp (I := I) (Φ := Ψ fun _ => 66) (Ψ := Ψ VG.Proof.MlDsa.Arm.Message.qCtx)
    (VG.Proof.MlDsa.Arm.Message.kabs_tr (src := .slot fCtx) (len := .slot fCtxLen) (pos := .imm 66) (VG.Proof.MlDsa.Arm.Message.absOk rfl rfl rfl rfl rfl)
      (fun L => L.ctx) (fun L => L.ctxLen.toNat) (fun _ => 66)
      (fun L g m t hL hc _ => ⟨by rw [hc.slotV hL (f := fCtx) (j := 3) rfl (by omega)]; rfl,
        by rw [hc.slotV hL (f := fCtxLen) (j := 4) rfl (by omega), VG.Proof.MlDsa.Arm.Message.ofNat_toNat32]; rfl, rfl⟩) ctxS)
    fun L g m₀ t hL hc _ => by
      obtain ⟨a, b, c, d, e, f, k⟩ := ctxS L hL
      exact WP.mono (VG.Proof.MlDsa.Arm.Message.kabs_ok hL hc (src := .slot fCtx) (len := .slot fCtxLen) (pos := .imm 66) (q := 66)
        (VG.Proof.MlDsa.Arm.Message.absOk rfl rfl rfl rfl rfl) (by rw [hc.slotV hL (f := fCtx) (j := 3) rfl (by omega)]; rfl)
        (by rw [hc.slotV hL (f := fCtxLen) (j := 4) rfl (by omega), VG.Proof.MlDsa.Arm.Message.ofNat_toNat32]; rfl) rfl a b c d e f k)
        fun t' ⟨hc', _, _, hx⟩ => ⟨hc', hx⟩
  have msgS : ∀ L : VG.Proof.MlDsa.Arm.Message.Lay, L.Ok → VG.Proof.MlDsa.Arm.Message.qCtx L < 136 ∧ L.len.toNat < 2 ^ 32 ∧ L.msg.toNat + L.len.toNat ≤ 2 ^ 32 ∧
      (∃ R ∈ L.rd ++ L.wr, Within ⟨State.addr L.msg, L.len.toNat⟩ R) ∧
      Region.Disjoint ⟨State.addr L.msg, L.len.toNat⟩ ⟨L.ST, 200⟩ ∧
      Region.Disjoint ⟨State.addr L.msg, L.len.toNat⟩ ⟨L.KS, 640⟩ ∧
      L.STK.Disjoint ⟨State.addr L.msg, L.len.toNat⟩ := fun L hL =>
    ⟨Nat.mod_lt _ (by decide), L.len.isLt, hL.nMsg, ⟨L.MSG, List.mem_append_left _ hL.inMsg, within_self _⟩,
      by have := hL.x_r hL.xMsg (e := 0) (k := 200) (by decide); simpa only [VG.Proof.MlDsa.Arm.Message.x0] using this.symm,
      (hL.x_r hL.xMsg (e := 200) (k := 640) (by decide)).symm, hL.kMsg⟩
  have a4 := VG.Proof.MlDsa.Arm.Message.two_wp (I := I) (Φ := Ψ VG.Proof.MlDsa.Arm.Message.qCtx) (Ψ := Ψ VG.Proof.MlDsa.Arm.Message.qMsg)
    (VG.Proof.MlDsa.Arm.Message.kabs_tr (src := .slot fMsg) (len := .slot fLen) (pos := .ret) (VG.Proof.MlDsa.Arm.Message.absOk rfl rfl rfl rfl rfl)
      (fun L => L.msg) (fun L => L.len.toNat) VG.Proof.MlDsa.Arm.Message.qCtx
      (fun L g m t hL hc hφ => ⟨by rw [hc.slotV hL (f := fMsg) (j := 1) rfl (by omega)]; rfl,
        by rw [hc.slotV hL (f := fLen) (j := 2) rfl (by omega), VG.Proof.MlDsa.Arm.Message.ofNat_toNat32]; rfl, VG.Proof.MlDsa.Arm.Message.ofNat_toNat_eq32 hφ⟩) msgS)
    fun L g m₀ t hL hc hφ => by
      obtain ⟨a, b, c, d, e, f, k⟩ := msgS L hL
      exact WP.mono (VG.Proof.MlDsa.Arm.Message.kabs_ok hL hc (src := .slot fMsg) (len := .slot fLen) (pos := .ret)
        (VG.Proof.MlDsa.Arm.Message.absOk rfl rfl rfl rfl rfl) (by rw [hc.slotV hL (f := fMsg) (j := 1) rfl (by omega)]; rfl)
        (by rw [hc.slotV hL (f := fLen) (j := 2) rfl (by omega), VG.Proof.MlDsa.Arm.Message.ofNat_toNat32]; rfl) (VG.Proof.MlDsa.Arm.Message.ofNat_toNat_eq32 hφ)
        a b c d e f k) fun t' ⟨hc', _, _, hx⟩ => ⟨hc', hx⟩
  have pd := VG.Proof.MlDsa.Arm.Message.kpad_tr (I := I) (Φ := Ψ VG.Proof.MlDsa.Arm.Message.qMsg) (pos := .ret) (VG.Proof.MlDsa.Arm.Message.padOk rfl) VG.Proof.MlDsa.Arm.Message.qMsg
    (fun L g m t _ _ hφ => VG.Proof.MlDsa.Arm.Message.ofNat_toNat_eq32 hφ) fun L _ => Nat.mod_lt _ (by decide)
  have pd' := VG.Proof.MlDsa.Arm.Message.two_wp (I := I) (Φ := Ψ VG.Proof.MlDsa.Arm.Message.qMsg) (Ψ := fun _ _ _ => True) pd
    fun L g m₀ t hL hc hφ => WP.mono (VG.Proof.MlDsa.Arm.Message.kpad_ok hL hc (pos := .ret) (VG.Proof.MlDsa.Arm.Message.padOk rfl) (VG.Proof.MlDsa.Arm.Message.ofNat_toNat_eq32 hφ)
      (Nat.mod_lt _ (by decide))) fun t' ⟨hc', _⟩ => ⟨hc', trivial⟩
  exact RelCT.seq z (a1.seq (a2.seq (a3.seq (a4.seq (pd'.seq VG.Proof.MlDsa.Arm.Message.ksqz_tr)))))

theorem trHash_tr {p : Params} (hk : p.pkLen < 2 ^ 16)
    {Φ : VG.Proof.MlDsa.Arm.Message.Lay → Mem → State → Prop} (hΦ : ∀ L m t, Φ L m t → L.keyLen = p.pkLen) :
    RelCT isa (VG.Proof.MlDsa.Arm.Message.Two I Φ) (VG.Impl.MlDsa.Arm.Message.trHash p) fun _ _ => True := by
  have keySide : ∀ L : VG.Proof.MlDsa.Arm.Message.Lay, L.Ok → 0 < 136 ∧ L.keyLen < 2 ^ 32 ∧ L.key.toNat + L.keyLen ≤ 2 ^ 32 ∧
      (∃ R ∈ L.rd ++ L.wr, Within ⟨State.addr L.key, L.keyLen⟩ R) ∧
      Region.Disjoint ⟨State.addr L.key, L.keyLen⟩ ⟨L.ST, 200⟩ ∧
      Region.Disjoint ⟨State.addr L.key, L.keyLen⟩ ⟨L.KS, 640⟩ ∧
      L.STK.Disjoint ⟨State.addr L.key, L.keyLen⟩ := fun L hL =>
    ⟨by decide, by have := hL.hKey.2; omega, hL.nKey, ⟨L.KEY, List.mem_append_left _ hL.inKey, within_self _⟩,
      by have := hL.x_r hL.xKey (e := 0) (k := 200) (by decide); simpa only [VG.Proof.MlDsa.Arm.Message.x0] using this.symm,
      (hL.x_r hL.xKey (e := 200) (k := 640) (by decide)).symm, hL.kKey⟩
  have z := VG.Proof.MlDsa.Arm.Message.two_wp (I := I) (Φ := Φ) (Ψ := fun L _ _ => L.keyLen = p.pkLen) VG.Proof.MlDsa.Arm.Message.zeroSt_tr
    fun L g m₀ t hL hc hφ => WP.mono (VG.Proof.MlDsa.Arm.Message.zeroSt_ok hL hc) fun t' ⟨hc', _⟩ => ⟨hc', hΦ L m₀ t hφ⟩
  have a1 := VG.Proof.MlDsa.Arm.Message.two_wp (I := I) (Φ := fun L _ _ => L.keyLen = p.pkLen) (Ψ := fun _ _ _ => True)
    (VG.Proof.MlDsa.Arm.Message.kabs_tr (src := .slot fKey) (len := .imm p.pkLen) (pos := .imm 0)
      (VG.Proof.MlDsa.Arm.Message.absOk rfl (by simp only [Arg.ok, decide_eq_true_eq]; omega) rfl rfl rfl) (fun L => L.key) (fun L => L.keyLen)
      (fun _ => 0) (fun L g m t hL hc hφ => ⟨by rw [hc.slotV hL (f := fKey) (j := 0) rfl (by omega)]; rfl,
        by rw [hφ]; rfl, rfl⟩) keySide)
    fun L g m₀ t hL hc hφ => by
      obtain ⟨a, b, c, d, e, f, k⟩ := keySide L hL
      exact WP.mono (VG.Proof.MlDsa.Arm.Message.kabs_ok hL hc (src := .slot fKey) (len := .imm p.pkLen) (pos := .imm 0)
        (n := L.keyLen) (q := 0) (VG.Proof.MlDsa.Arm.Message.absOk rfl (by simp only [Arg.ok, decide_eq_true_eq]; omega) rfl rfl rfl)
        (by rw [hc.slotV hL (f := fKey) (j := 0) rfl (by omega)]; rfl) (by rw [hφ]; rfl) rfl a b c d e f k)
        fun t' ⟨hc', _⟩ => ⟨hc', trivial⟩
  have pd := VG.Proof.MlDsa.Arm.Message.kpad_tr (I := I) (Φ := fun _ _ _ => True) (pos := .imm (p.pkLen % 136))
    (VG.Proof.MlDsa.Arm.Message.padOk (by simp only [Arg.ok, decide_eq_true_eq]; omega)) (fun _ => p.pkLen % 136)
    (fun _ _ _ _ _ _ _ => rfl) fun _ _ => Nat.mod_lt _ (by decide)
  have pd' := VG.Proof.MlDsa.Arm.Message.two_wp (I := I) (Φ := fun _ _ _ => True) (Ψ := fun _ _ _ => True) pd
    fun L g m₀ t hL hc _ => WP.mono (VG.Proof.MlDsa.Arm.Message.kpad_ok hL hc (pos := .imm (p.pkLen % 136))
      (VG.Proof.MlDsa.Arm.Message.padOk (by simp only [Arg.ok, decide_eq_true_eq]; omega)) rfl (Nat.mod_lt _ (by decide)))
      fun t' ⟨hc', _⟩ => ⟨hc', trivial⟩
  exact RelCT.seq z (a1.seq (pd'.seq VG.Proof.MlDsa.Arm.Message.ksqz_tr))

end

end VG.Proof.MlDsa.Arm.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Message.SignCT`. -/
section

/-!
# ML-DSA on ARMv7, `sign_message`: constant time

Untrusted: everything here is checked by Lean. Two runs from states that
satisfy the contract and agree on its public data, which includes what
`signMessageLeak` says (`signI`), leak the same: the branch on `ctx_len`,
the entry and the exit depend only on the pointers and the lengths (the
taint analysis, with the arguments on the stack public); the hashing leaks
only the layout (`muHash_tr`); and the call of the signing function on `μ`
leaks only `signLeak` of the key, `μ` and `rnd`, which is `signMessageLeak`
of the inputs (`signCall_tr`).
-/

namespace VG.Proof.MlDsa.Arm.Message

open VG VG.Arm VG.Impl.MlDsa.Arm.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.Arm (push2_frame push2_arg view_gpr below push_eq)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable {p : Params}

/-- What the contract says two runs agree on, beyond the pointers and lengths. -/
def signI (p : Params) (L : VG.Proof.MlDsa.Arm.Message.Lay) (m₁ m₂ : Mem) : Prop :=
  signMessageLeak p (bytesAt m₁ (State.addr L.key) p.skLen) (bytesAt m₁ (State.addr L.msg) L.len.toNat)
      (bytesAt m₁ (State.addr L.ctx) L.ctxLen.toNat) (bytesAt m₁ (State.addr L.rnd) 32) =
    signMessageLeak p (bytesAt m₂ (State.addr L.key) p.skLen) (bytesAt m₂ (State.addr L.msg) L.len.toNat)
      (bytesAt m₂ (State.addr L.ctx) L.ctxLen.toNat) (bytesAt m₂ (State.addr L.rnd) 32)

/-- The layout is that of a run of `sign_message` from a state with the
memory `m`, past the branch on `ctx_len`. -/
def SOk (p : Params) (L : VG.Proof.MlDsa.Arm.Message.Lay) (m : Mem) : Prop :=
  ∃ σ, VG.Proof.MlDsa.Arm.Message.SPre p σ ∧ (stackArg σ 0).toNat < 256 ∧ VG.Proof.MlDsa.Arm.Message.slay p σ = L ∧ σ.mem = m

/-- `μ` at `X + 840`. -/
def MuOk (L : VG.Proof.MlDsa.Arm.Message.Lay) (m : Mem) (t : State) : Prop :=
  bytesAt t.mem L.MU 64 = VG.Spec.MlDsa.H (bytesAt m (State.addr (L.key + BitVec.ofNat 32 64)) 64 ++ VG.Proof.MlDsa.Arm.Message.hdrBytes L ++
    bytesAt m (State.addr L.ctx) L.ctxLen.toNat ++ bytesAt m (State.addr L.msg) L.len.toNat) 64

/-- What `sign_message` leaks is what the signing function on `μ` leaks, for
the `μ` it computes. -/
theorem leak_eq {L : VG.Proof.MlDsa.Arm.Message.Lay} (hL : L.Ok) (hk : L.keyLen = p.skLen) (m : Mem) :
    signMessageLeak p (bytesAt m (State.addr L.key) p.skLen) (bytesAt m (State.addr L.msg) L.len.toNat)
        (bytesAt m (State.addr L.ctx) L.ctxLen.toNat) (bytesAt m (State.addr L.rnd) 32) =
      signLeak p (bytesAt m (State.addr L.key) p.skLen) (VG.Spec.MlDsa.H (bytesAt m (State.addr (L.key + BitVec.ofNat 32 64)) 64 ++
        VG.Proof.MlDsa.Arm.Message.hdrBytes L ++ bytesAt m (State.addr L.ctx) L.ctxLen.toNat ++ bytesAt m (State.addr L.msg) L.len.toNat) 64)
        (bytesAt m (State.addr L.rnd) 32) := by
  have := hL.hKey
  have := hL.nKey
  rw [signMessageLeak, formatMessage_some (by rw [Proof.MlKem.bytesAt_length]; exact hL.ctxLt)]
  simp only [messageRep, skTr, VG.Proof.MlDsa.Arm.Message.hdrBytes, Proof.MlKem.bytesAt_length, List.append_assoc]
  rw [addr_add (by omega), Proof.MlKem.bytesAt_slice _ _ (by omega)]

/-- What a layout of `sign_message` says of `rnd`, `sig` and `scratch`. -/
structure SFacts (p : Params) (L : VG.Proof.MlDsa.Arm.Message.Lay) : Prop where
  key : L.keyLen = p.skLen
  xRnd : L.SC.Disjoint ⟨State.addr L.rnd, 32⟩
  kRnd : L.STK.Disjoint ⟨State.addr L.rnd, 32⟩
  inRnd : (⟨State.addr L.rnd, 32⟩ : Region) ∈ L.rd
  inSig : (⟨State.addr L.sig, p.sigLen⟩ : Region) ∈ L.wr

theorem SOk.facts {L : VG.Proof.MlDsa.Arm.Message.Lay} {m : Mem} (h : VG.Proof.MlDsa.Arm.Message.SOk p L m) : VG.Proof.MlDsa.Arm.Message.SFacts p L := by
  obtain ⟨σ, hσ, _, rfl, -⟩ := h
  exact ⟨rfl, hσ.rndScr.symm, hσ.stkRnd, by simp [VG.Proof.MlDsa.Arm.Message.slay, hσ.rd], by simp [VG.Proof.MlDsa.Arm.Message.slay, hσ.wr]⟩

/-- The regions the signing function on `μ` is given, as functions of the layout. -/
abbrev sRd (p : Params) (L : VG.Proof.MlDsa.Arm.Message.Lay) : List Region :=
  [⟨State.addr L.key, p.skLen⟩, ⟨L.MU, 64⟩, ⟨State.addr L.rnd, 32⟩, ⟨State.addr L.SP - BitVec.ofNat 64 8, 4⟩]
abbrev sWr (p : Params) (L : VG.Proof.MlDsa.Arm.Message.Lay) : List Region := [⟨State.addr L.sig, p.sigLen⟩, ⟨State.addr L.scr, VG.Proof.MlDsa.Arm.Message.sScr p⟩]

/-- The entry state of the signing function on `μ`, from either run. -/
theorem sView {σ : State} (hp : p ∈ VG.Proof.MlDsa.Arm.Message.params) (hσ : VG.Proof.MlDsa.Arm.Message.SPre p σ) (h8 : (stackArg σ 0).toNat < 256) {g : Reg → BitVec 32}
    {m₀ : Mem} {t t1 E : State} (hc : VG.Proof.MlDsa.Arm.Message.Ctx (VG.Proof.MlDsa.Arm.Message.slay p σ) g m₀ t) (f : VG.Proof.MlDsa.Arm.Message.Moved VG.Proof.MlDsa.Arm.Message.signArgs t t1)
    (hE : (pushed [.r12, .lr] t1).callEntry.withRegions (VG.Proof.MlDsa.Arm.Message.sRd p (VG.Proof.MlDsa.Arm.Message.slay p σ)) (VG.Proof.MlDsa.Arm.Message.sWr p (VG.Proof.MlDsa.Arm.Message.slay p σ)) = E) :
    E.sp = σ.sp - BitVec.ofNat 32 8 ∧ E.gpr .r0 = σ.gpr .r0 ∧
      E.gpr .r1 = (VG.Proof.MlDsa.Arm.Message.slay p σ).X32 + BitVec.ofNat 32 840 ∧ E.gpr .r2 = stackArg σ 1 ∧ E.gpr .r3 = stackArg σ 2 ∧
      stackArg E 0 = stackArg σ 3 ∧
      bytesAt E.mem (BitVec.setWidth 64 (σ.gpr .r0)) p.skLen = bytesAt m₀ (State.addr (σ.gpr .r0)) p.skLen ∧
      bytesAt E.mem (BitVec.setWidth 64 ((VG.Proof.MlDsa.Arm.Message.slay p σ).X32 + BitVec.ofNat 32 840)) 64 = bytesAt t.mem (VG.Proof.MlDsa.Arm.Message.slay p σ).MU 64 ∧
      bytesAt E.mem (BitVec.setWidth 64 (stackArg σ 1)) 32 = bytesAt m₀ (State.addr (stackArg σ 1)) 32 := by
  have hL := VG.Proof.MlDsa.Arm.Message.slay_ok hp hσ h8
  have F : VG.Proof.MlDsa.Arm.Message.SFacts p (VG.Proof.MlDsa.Arm.Message.slay p σ) := SOk.facts ⟨σ, hσ, h8, rfl, rfl⟩
  obtain ⟨e0, e1, e2, e3, e4⟩ := VG.Proof.MlDsa.Arm.Message.signRegs_of hL hc f.1
  have hsp1 : t1.sp = σ.sp := f.2.sp.trans hc.sp
  have h8' : 8 ≤ t1.sp.toNat := by rw [hsp1]; have := hσ.sp; omega
  obtain ⟨-, a1, -⟩ := push2_arg (t := E) h8' (by rw [← hE]; rfl) (by rw [← hE]; rfl)
  have bk : Region.Sub (below t1 8) (VG.Proof.MlDsa.Arm.Message.slay p σ).STK := VG.Proof.MlDsa.Arm.Message.below_stk hsp1
  have em : E.mem = storeWords t1.mem (t1.sp - 8#32) [t1.gpr .r12, t1.gpr .lr] := by rw [← hE]; rfl
  have g : ∀ {r : Reg}, r ∉ linkRegs → E.gpr r = t1.gpr r := fun hr => by
    rw [← hE]; exact view_gpr _ _ _ _ hr
  have sw : ∀ a : BitVec 32, BitVec.setWidth 64 a = State.addr a := fun _ => rfl
  refine ⟨by rw [← hE, State.withRegions_sp, State.callEntry_sp, VG.Arm.pushed_sp, hsp1]; rfl,
    by rw [g (by decide), e0], by rw [g (by decide), e1], by rw [g (by decide), e2], by rw [g (by decide), e3],
    by rw [a1, e4], ?_, ?_, ?_⟩ <;> rw [sw]
  · rw [em, VG.Proof.MlDsa.Arm.Message.storeWords_bytes h8' (hσ.stkSk.symm.sub_right bk) (by have := hσ.nSk; omega), f.2.mem]
    exact hc.bytesAt_eq (p := State.addr (VG.Proof.MlDsa.Arm.Message.slay p σ).key) hL.xKey hL.kKey (by have := hσ.nSk; omega)
  · rw [em, VG.Proof.MlDsa.Arm.Message.storeWords_bytes h8' (by rw [VG.Proof.MlDsa.Arm.Message.mu_eq hL]; exact (VG.Proof.MlDsa.Arm.Message.k_mu hL).symm.sub_right bk) (by decide), f.2.mem,
      VG.Proof.MlDsa.Arm.Message.mu_eq hL]
  · rw [em, VG.Proof.MlDsa.Arm.Message.storeWords_bytes h8' (hσ.stkRnd.symm.sub_right bk) (by decide), f.2.mem]
    exact hc.bytesAt_eq (p := State.addr (VG.Proof.MlDsa.Arm.Message.slay p σ).rnd) F.xRnd F.kRnd (by decide)

/-- Two runs of the call of the signing function on `μ`. -/
theorem signCall_tr {n : String} {c : Prog isa} (hS : VG.Proof.MlDsa.Arm.Message.SignFn p c) (hp : p ∈ VG.Proof.MlDsa.Arm.Message.params) :
    RelCT isa (VG.Proof.MlDsa.Arm.Message.Two (VG.Proof.MlDsa.Arm.Message.signI p) fun L m t => VG.Proof.MlDsa.Arm.Message.SOk p L m ∧ VG.Proof.MlDsa.Arm.Message.MuOk L m t)
      (.seq (.block (VG.Impl.MlDsa.Arm.Message.setArgs VG.Proof.MlDsa.Arm.Message.signArgs)) (.frame (.push [.r12, .lr]) (.call n c) (.pop .r12 8))) fun _ _ => True := by
  refine RelCT.seq (VG.Proof.MlDsa.Arm.Message.setArgs_two (by decide)) (VG.Arm.RelCT.frame (fun a b ⟨x, y, h, f₁, f₂⟩ => by
    rw [f₁.2.sp, f₂.2.sp]; exact h.r7.2) ?_)
  -- The layout, out of the relation, so that the call's regions are fixed.
  refine RelCT.mono (P := fun a b => ∃ L : VG.Proof.MlDsa.Arm.Message.Lay, ∃ x y a1 b1, (∃ g₁ g₂ m₁ m₂, L.Ok ∧ VG.Proof.MlDsa.Arm.Message.signI p L m₁ m₂ ∧
      VG.Proof.MlDsa.Arm.Message.Ctx L g₁ m₁ x ∧ VG.Proof.MlDsa.Arm.Message.Ctx L g₂ m₂ y ∧ (VG.Proof.MlDsa.Arm.Message.SOk p L m₁ ∧ VG.Proof.MlDsa.Arm.Message.MuOk L m₁ x) ∧ (VG.Proof.MlDsa.Arm.Message.SOk p L m₂ ∧ VG.Proof.MlDsa.Arm.Message.MuOk L m₂ y)) ∧
      VG.Proof.MlDsa.Arm.Message.Moved VG.Proof.MlDsa.Arm.Message.signArgs x a1 ∧ VG.Proof.MlDsa.Arm.Message.Moved VG.Proof.MlDsa.Arm.Message.signArgs y b1 ∧ a = pushed [.r12, .lr] a1 ∧ b = pushed [.r12, .lr] b1)
    (RelCT.exists_ fun L => RelCT.call hS.ver.1 hS.ver.2.1 (VG.Proof.MlDsa.Arm.Message.sRd p L) (VG.Proof.MlDsa.Arm.Message.sWr p L) fun a b h => ?_)
    (fun a b ⟨a1, b1, ⟨x, y, ⟨L, hp'⟩, f₁, f₂⟩, ea, eb⟩ => ⟨L, x, y, a1, b1, hp', f₁, f₂, VG.Proof.MlKem.Arm.push_eq ea, VG.Proof.MlKem.Arm.push_eq eb⟩)
    fun _ _ h => h
  obtain ⟨x, y, a1, b1, ⟨g₁, g₂, m₁, m₂, hL, hi, c₁, c₂, ⟨φ₁, μ₁⟩, ⟨_, μ₂⟩⟩, f₁, f₂, rfl, rfl⟩ := h
  have F := φ₁.facts
  obtain ⟨σ, hσ, h8, rfl, -⟩ := φ₁
  have hsx : a1.sp = σ.sp := f₁.2.sp.trans c₁.sp
  have hsy : b1.sp = σ.sp := f₂.2.sp.trans c₂.sp
  have eR : ∀ t1 : State, t1.sp = σ.sp → VG.Proof.MlDsa.Arm.Message.signRd p σ ++ [VG.Proof.MlDsa.Arm.Message.argR t1] = VG.Proof.MlDsa.Arm.Message.sRd p (VG.Proof.MlDsa.Arm.Message.slay p σ) := fun t1 ht => by
    simp only [VG.Proof.MlDsa.Arm.Message.argR, ht, List.cons_append, List.nil_append]; rfl
  have pre₁ := VG.Proof.MlDsa.Arm.Message.signK_pre hp hσ h8 c₁ f₁.1 hsx
  have pre₂ := VG.Proof.MlDsa.Arm.Message.signK_pre hp hσ h8 c₂ f₂.1 hsy
  rw [eR a1 hsx] at pre₁
  rw [eR b1 hsy] at pre₂
  have hL' := VG.Proof.MlDsa.Arm.Message.slay_ok hp hσ h8
  have cv : ∀ {t t1 : State} {g m₀}, VG.Proof.MlDsa.Arm.Message.Ctx (VG.Proof.MlDsa.Arm.Message.slay p σ) g m₀ t → VG.Proof.MlDsa.Arm.Message.Moved VG.Proof.MlDsa.Arm.Message.signArgs t t1 →
      Covers (VG.Proof.MlDsa.Arm.Message.sRd p (VG.Proof.MlDsa.Arm.Message.slay p σ) ++ VG.Proof.MlDsa.Arm.Message.sWr p (VG.Proof.MlDsa.Arm.Message.slay p σ)) ((pushed [.r12, .lr] t1).rd ++ (pushed [.r12, .lr] t1).wr) ∧
        Covers (VG.Proof.MlDsa.Arm.Message.sWr p (VG.Proof.MlDsa.Arm.Message.slay p σ)) (pushed [.r12, .lr] t1).wr := fun {t t1 _ _} hc f => by
    have ht : t1.sp = σ.sp := f.2.sp.trans hc.sp
    have h8' : 8 ≤ t1.sp.toNat := by rw [ht]; have := hσ.sp; omega
    have := VG.Proof.MlDsa.Arm.Message.cov_pushed h8' (rd := VG.Proof.MlDsa.Arm.Message.signRd p σ) (wr := VG.Proof.MlDsa.Arm.Message.signWr p σ) (fun r hr => by
        rw [f.2.rd, f.2.wr, hc.rd, hc.wr]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨_, List.mem_append_left _ (F.key ▸ hL'.inKey), within_self _⟩
        · exact ⟨_, List.mem_append_right _ hL'.inSC, VG.Proof.MlDsa.Arm.Message.mu_within hL'⟩
        · exact ⟨_, List.mem_append_left _ F.inRnd, within_self _⟩)
      (fun r hr => by
        rw [f.2.wr, hc.wr]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, F.inSig, within_self _⟩
        · exact ⟨_, hL'.inSC, within_base _ (by simp only [VG.Proof.MlDsa.Arm.Message.slay]; rw [VG.Proof.MlDsa.Arm.Message.mScr_eq]; simp only [VG.Proof.MlDsa.Arm.Message.sScr, oE]; omega)⟩)
    rwa [eR t1 ht] at this
  refine ⟨pre₁, pre₂, ?_, (cv c₁ f₁).1, (cv c₁ f₁).2, (cv c₂ f₂).1, (cv c₂ f₂).2⟩
  generalize hE₁ : (pushed [.r12, .lr] a1).callEntry.withRegions (VG.Proof.MlDsa.Arm.Message.sRd p (VG.Proof.MlDsa.Arm.Message.slay p σ)) (VG.Proof.MlDsa.Arm.Message.sWr p (VG.Proof.MlDsa.Arm.Message.slay p σ)) = E₁
  generalize hE₂ : (pushed [.r12, .lr] b1).callEntry.withRegions (VG.Proof.MlDsa.Arm.Message.sRd p (VG.Proof.MlDsa.Arm.Message.slay p σ)) (VG.Proof.MlDsa.Arm.Message.sWr p (VG.Proof.MlDsa.Arm.Message.slay p σ)) = E₂
  obtain ⟨s₁, x0, x1, x2, x3, x4, k₁, u₁, r₁⟩ := VG.Proof.MlDsa.Arm.Message.sView hp hσ h8 c₁ f₁ hE₁
  obtain ⟨s₂, y0, y1, y2, y3, y4, k₂, u₂, r₂⟩ := VG.Proof.MlDsa.Arm.Message.sView hp hσ h8 c₂ f₂ hE₂
  sig_pub [signContract, signSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  rw [x0, x1, x2, x3, x4, y0, y1, y2, y3, y4, s₁, s₂, k₁, k₂, u₁, u₂, r₁, r₂, μ₁, μ₂]
  refine ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
  have := hi
  unfold VG.Proof.MlDsa.Arm.Message.signI at this
  rw [VG.Proof.MlDsa.Arm.Message.leak_eq hL' F.key, VG.Proof.MlDsa.Arm.Message.leak_eq hL' F.key] at this
  exact this

/-- The public data of the contract, spelled out. -/
structure SPub (p : Params) (s₁ s₂ : State) : Prop where
  sp : s₁.sp = s₂.sp
  leak : signMessageLeak p (bytesAt s₁.mem (State.addr (s₁.gpr .r0)) p.skLen)
      (bytesAt s₁.mem (State.addr (s₁.gpr .r1)) (s₁.gpr .r2).toNat)
      (bytesAt s₁.mem (State.addr (s₁.gpr .r3)) (stackArg s₁ 0).toNat) (bytesAt s₁.mem (State.addr (stackArg s₁ 1)) 32) =
    signMessageLeak p (bytesAt s₂.mem (State.addr (s₂.gpr .r0)) p.skLen)
      (bytesAt s₂.mem (State.addr (s₂.gpr .r1)) (s₂.gpr .r2).toNat)
      (bytesAt s₂.mem (State.addr (s₂.gpr .r3)) (stackArg s₂ 0).toNat) (bytesAt s₂.mem (State.addr (stackArg s₂ 1)) 32)
  r0 : s₁.gpr .r0 = s₂.gpr .r0
  r1 : s₁.gpr .r1 = s₂.gpr .r1
  r2 : s₁.gpr .r2 = s₂.gpr .r2
  r3 : s₁.gpr .r3 = s₂.gpr .r3
  a0 : stackArg s₁ 0 = stackArg s₂ 0
  a1 : stackArg s₁ 1 = stackArg s₂ 1
  a2 : stackArg s₁ 2 = stackArg s₂ 2
  a3 : stackArg s₁ 3 = stackArg s₂ 3

theorem sPub_of {s₁ s₂ : State} (h : (signMessageContract p Arm.abi 36).pub s₁ s₂) : VG.Proof.MlDsa.Arm.Message.SPub p s₁ s₂ := by
  sig_pub [signMessageContract, signMessageSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨a, b, c, d, e, f, g, h, i, j⟩ := h
  exact ⟨a, b, c, d, e, f, g, h, i, j⟩

/-- Two runs from states agreeing on the public data have the same layout. -/
theorem slay_eq {s₁ s₂ : State} (h₁ : VG.Proof.MlDsa.Arm.Message.SPre p s₁) (h₂ : VG.Proof.MlDsa.Arm.Message.SPre p s₂) (h : VG.Proof.MlDsa.Arm.Message.SPub p s₁ s₂) : VG.Proof.MlDsa.Arm.Message.slay p s₁ = VG.Proof.MlDsa.Arm.Message.slay p s₂ := by
  have e1 : s₁.rd = s₂.rd := by
    rw [h₁.rd, h₂.rd]
    simp only [VG.Proof.MlDsa.Arm.Message.rKey, VG.Proof.MlDsa.Arm.Message.rMsg, VG.Proof.MlDsa.Arm.Message.rCtx, VG.Proof.MlDsa.Arm.Message.rArgs, VG.Proof.MlDsa.Arm.Message.sArg, VG.Proof.MlDsa.Arm.Message.stackArgAddr0, h.sp, h.r0, h.r1, h.r2, h.r3, h.a0, h.a1]
  have e2 : s₁.wr = s₂.wr := by
    rw [h₁.wr, h₂.wr]; simp only [VG.Proof.MlDsa.Arm.Message.sArg, h.a2, h.a3]
  simp only [VG.Proof.MlDsa.Arm.Message.slay, h.sp, h.r0, h.r1, h.r2, h.r3, h.a0, h.a1, h.a2, h.a3, e1, e2]

/-- The body, between the entry and the exit: its runs end with the same
`r7` and stack pointer. -/
theorem signBody_tr {n : String} {c : Prog isa} (hS : VG.Proof.MlDsa.Arm.Message.SignFn p c) (hp : p ∈ VG.Proof.MlDsa.Arm.Message.params) :
    RelCT isa (VG.Proof.MlDsa.Arm.Message.Two (VG.Proof.MlDsa.Arm.Message.signI p) fun L m _ => VG.Proof.MlDsa.Arm.Message.SOk p L m)
      (.seq (muHash (.slotOff fKey 64)) (.seq (.block (VG.Impl.MlDsa.Arm.Message.setArgs VG.Proof.MlDsa.Arm.Message.signArgs))
        (.frame (.push [.r12, .lr]) (.call n c) (.pop .r12 8))))
      fun a b => a.gpr .r7 = b.gpr .r7 ∧ a.sp = b.sp := by
  have side : ∀ L : VG.Proof.MlDsa.Arm.Message.Lay, L.Ok → (L.key + BitVec.ofNat 32 64).toNat + 64 ≤ 2 ^ 32 ∧
      (∃ R ∈ L.rd ++ L.wr, Within ⟨State.addr (L.key + BitVec.ofNat 32 64), 64⟩ R) ∧
      Region.Disjoint ⟨State.addr (L.key + BitVec.ofNat 32 64), 64⟩ ⟨L.ST, 200⟩ ∧
      Region.Disjoint ⟨State.addr (L.key + BitVec.ofNat 32 64), 64⟩ ⟨L.KS, 640⟩ ∧
      L.STK.Disjoint ⟨State.addr (L.key + BitVec.ofNat 32 64), 64⟩ := fun L hL => by
    have := hL.hKey
    have := hL.nKey
    have w : Within ⟨State.addr (L.key + BitVec.ofNat 32 64), 64⟩ L.KEY := by
      rw [addr_add (by omega)]; exact within_off _ (by omega)
    have hst : Region.Sub ⟨L.ST, 200⟩ L.SC := by
      have := hL.sub_sc (e := 0) (k := 200) (by omega)
      simpa only [VG.Proof.MlDsa.Arm.Message.x0] using this
    refine ⟨?_, ⟨_, List.mem_append_left _ hL.inKey, w⟩, (hL.xKey.symm.sub_left w.sub).sub_right hst,
      (hL.xKey.symm.sub_left w.sub).sub_right (hL.sub_sc (by decide : 200 + 640 ≤ 1024)),
      hL.kKey.sub_right w.sub⟩
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 64) (by decide), Nat.mod_eq_of_lt (by omega)]
    omega
  have mh := VG.Proof.MlDsa.Arm.Message.muHash_tr (I := VG.Proof.MlDsa.Arm.Message.signI p) (Φ := fun L m _ => VG.Proof.MlDsa.Arm.Message.SOk p L m) (tr := .slotOff fKey 64) (by decide) rfl
    (fun L => L.key + BitVec.ofNat 32 64) (fun L g m t hL hc => hc.slotOffV hL 64) side
  have mh' := VG.Proof.MlDsa.Arm.Message.two_wp (I := VG.Proof.MlDsa.Arm.Message.signI p) (Φ := fun L m _ => VG.Proof.MlDsa.Arm.Message.SOk p L m) (Ψ := fun L m t => VG.Proof.MlDsa.Arm.Message.SOk p L m ∧ VG.Proof.MlDsa.Arm.Message.MuOk L m t) mh
    fun L g m₀ t hL hc hφ => by
      have := hL.hKey
      have := hL.nKey
      have w : Within ⟨State.addr (L.key + BitVec.ofNat 32 64), 64⟩ L.KEY := by
        rw [addr_add (by omega)]; exact within_off _ (by omega)
      obtain ⟨a, b, c, d, e⟩ := side L hL
      refine WP.mono (VG.Proof.MlDsa.Arm.Message.muHash_ok hL hc (tr := .slotOff fKey 64) (by decide) rfl (fun t' hc' => hc'.slotOffV hL 64)
        a b c d e) fun t' ⟨hc', hμ⟩ => ⟨hc', hφ, ?_⟩
      unfold VG.Proof.MlDsa.Arm.Message.MuOk
      rw [hμ, hc.bytesAt_eq (hL.xKey.sub_right w.sub) (hL.kKey.sub_right w.sub) (by decide)]
  refine RelCT.postDep (F := fun x x' => x'.gpr .r7 = x.gpr .r7 ∧ x'.sp = x.sp)
    (mh'.seq (VG.Proof.MlDsa.Arm.Message.signCall_tr hS hp)) (fun x y hxy => ?_) fun x y x' y' hxy f₁ f₂ => ?_
  · have run : ∀ {L : VG.Proof.MlDsa.Arm.Message.Lay} {g m₀} {t : State}, L.Ok → VG.Proof.MlDsa.Arm.Message.Ctx L g m₀ t → VG.Proof.MlDsa.Arm.Message.SOk p L m₀ →
        WP isa (.seq (muHash (.slotOff fKey 64)) (.seq (.block (VG.Impl.MlDsa.Arm.Message.setArgs VG.Proof.MlDsa.Arm.Message.signArgs))
          (.frame (.push [.r12, .lr]) (.call n c) (.pop .r12 8)))) t
          fun t' => t'.gpr .r7 = t.gpr .r7 ∧ t'.sp = t.sp := fun hL hc hφ => by
      obtain ⟨σ, hσ, h8, rfl, -⟩ := hφ
      obtain ⟨a, b, c, d, e⟩ := side _ hL
      refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Message.muHash_ok hL hc (tr := .slotOff fKey 64) (by decide) rfl
        (fun t' hc' => hc'.slotOffV hL 64) a b c d e) fun t₁ ⟨hc₁, _⟩ => ?_)
      exact WP.mono (VG.Proof.MlDsa.Arm.Message.signCall_ok hS hp hσ h8 hc₁) fun s' ⟨hf, _⟩ =>
        ⟨hf.r7.trans hc.r7.symm, hf.sp.trans hc.sp.symm⟩
    obtain ⟨L, _, _, _, _, hL, _, c₁, c₂, φ₁, φ₂⟩ := hxy
    exact ⟨run hL c₁ φ₁, run hL c₂ φ₂⟩
  · obtain ⟨L, _, _, _, _, _, _, c₁, c₂, _, _⟩ := hxy
    exact ⟨by rw [f₁.1, f₂.1, c₁.r7, c₂.r7], by rw [f₁.2, f₂.2, c₁.sp, c₂.sp]⟩

/-- Two states with the stack pointer, permissions and memory of two entry
states agreeing on the public data agree on the first `n ≤ 16` bytes of the
arguments on the stack. -/
theorem sAgree {x y a b : State} (hx : VG.Proof.MlDsa.Arm.Message.SPre p x) (hy : VG.Proof.MlDsa.Arm.Message.SPre p y) (hpub : VG.Proof.MlDsa.Arm.Message.SPub p x y)
    (ha : a.sp = x.sp ∧ a.wr = x.wr ∧ a.mem = x.mem) (hb : b.sp = y.sp ∧ b.wr = y.wr ∧ b.mem = y.mem)
    {n : Nat} (hn : n ≤ 16) : VG.Arm.Taint.Agree (argTaint [] n) a b := by
  have w : ∀ {z c : State}, VG.Proof.MlDsa.Arm.Message.SPre p z → c.sp = z.sp ∧ c.wr = z.wr ∧ c.mem = z.mem →
      c.sp.toNat + n ≤ 2 ^ 32 ∧ ∀ r ∈ c.wr, Region.Disjoint ⟨State.addr c.sp, n⟩ r := fun {z c} hz hc => by
    refine ⟨by rw [hc.1]; have := hz.spA; omega, fun r hr => ?_⟩
    rw [hc.2.1, hz.wr] at hr
    have hs : Region.Sub ⟨State.addr c.sp, n⟩ (VG.Proof.MlDsa.Arm.Message.rArgs z 16) := by
      simp only [VG.Proof.MlDsa.Arm.Message.rArgs, VG.Proof.MlDsa.Arm.Message.stackArgAddr0, hc.1]; exact Region.sub_prefix hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hz.sigArgs.sub_right hs).symm
    · exact (hz.scrArgs.sub_right hs).symm
  have hsp : a.sp = b.sp := by rw [ha.1, hb.1, hpub.sp]
  refine agree_argTaint (fun r hr => by simp at hr) hsp (w hx ha) (w hy hb) fun k hk => ?_
  have := argMem_of (s₁ := a) (s₂ := b) (j := 4) hsp (by rw [ha.1]; have := hx.spA; omega) (fun i hi => by
    simp only [stackArg, stackArgAddr, ha.1, hb.1, ha.2.2, hb.2.2]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
    · exact hpub.a0
    · exact hpub.a1
    · exact hpub.a2
    · exact hpub.a3) k (by omega)
  exact this

/-- The entry states of two runs: the precondition and the public data. -/
abbrev SP2 (p : Params) (x y : State) : Prop :=
  (signMessageContract p Arm.abi 36).pre x ∧ (signMessageContract p Arm.abi 36).pre y ∧
    (signMessageContract p Arm.abi 36).pub x y

/-- After the shift of `ctx_len` and the comparison. -/
abbrev AChk (x s1 : State) : Prop := VG.Proof.MlDsa.Arm.Message.Only [.r12] x s1 ∧ isa.eval .ne s1 = some (decide ¬ (stackArg x 0).toNat < 256)

theorem chk_taint : (VG.Arm.taint.check (argTaint [] 4)
    (.block [.ldrSp .r12 0, .mov .r12 (.shifted .r12 .lsr 8), .cmp .r12 (.imm 0)]) (.block [])).isSome = true := by
  rfl

theorem mov2_taint : (VG.Arm.taint.check (Taint.ofRegs []) (.block [.mov .r0 (.imm 2)]) (.block [])).isSome = true := by
  rfl

theorem leave_taint : (VG.Arm.taint.check (Taint.ofRegs [.r7]) (.block leave) (.block [])).isSome = true := by
  rfl

theorem enterS_taint (p : Params) :
    (VG.Arm.taint.check (argTaint [] 16) (.block (enter 12 p signLoads)) (.block [])).isSome = true := by
  rfl

theorem signMessage_ct {n : String} {c : Prog isa} (hS : VG.Proof.MlDsa.Arm.Message.SignFn p c) (hp : p ∈ VG.Proof.MlDsa.Arm.Message.params) :
    ConstantTime isa (signMessageContract p Arm.abi 36).pre (signMessageContract p Arm.abi 36).pub
      (signMessage n c p) := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  have e0 : (fun s₁ s₂ => (signMessageContract p Arm.abi 36).pre s₁ ∧
      (signMessageContract p Arm.abi 36).pre s₂ ∧ (signMessageContract p Arm.abi 36).pub s₁ s₂) =
      VG.Proof.MlDsa.Arm.Message.Ghost (VG.Proof.MlDsa.Arm.Message.SP2 p) (fun x a => a = x) := by
    funext a b; apply propext
    exact ⟨fun h => ⟨a, b, h, rfl, rfl⟩, fun ⟨_, _, h, e₁, e₂⟩ => e₁ ▸ e₂ ▸ h⟩
  rw [e0]
  unfold signMessage top
  -- `r12 ← ctx_len >> 8`, compared with 0.
  have hchk := VG.Proof.MlDsa.Arm.Message.ghost_step (P := VG.Proof.MlDsa.Arm.Message.SP2 p) (A := fun x a => a = x) (B := VG.Proof.MlDsa.Arm.Message.AChk)
    (c := .block [.ldrSp .r12 0, .mov .r12 (.shifted .r12 .lsr 8), .cmp .r12 (.imm 0)])
    (VG.Proof.MlDsa.Arm.Message.argRel [] 4 (fun a b ⟨x, y, hxy, e₁, e₂⟩ => by
      subst e₁ e₂
      exact VG.Proof.MlDsa.Arm.Message.sAgree (VG.Proof.MlDsa.Arm.Message.sPre_of hxy.1) (VG.Proof.MlDsa.Arm.Message.sPre_of hxy.2.1) (VG.Proof.MlDsa.Arm.Message.sPub_of hxy.2.2) ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ (by omega))
      VG.Proof.MlDsa.Arm.Message.chk_taint)
    fun x y a b hxy e₁ e₂ => by
      subst e₁ e₂; exact ⟨VG.Proof.MlDsa.Arm.Message.chk_ok ((VG.Proof.MlDsa.Arm.Message.sPre_of hxy.1).args (by omega)), VG.Proof.MlDsa.Arm.Message.chk_ok ((VG.Proof.MlDsa.Arm.Message.sPre_of hxy.2.1).args (by omega))⟩
  refine RelCT.seq hchk (RelCT.ite (fun a b ⟨x, y, hxy, f₁, f₂⟩ => by
    rw [f₁.2, f₂.2, (VG.Proof.MlDsa.Arm.Message.sPub_of hxy.2.2).a0]) ?_ ?_)
  · -- `ctx_len ≥ 256`: return 2.
    exact VG.Proof.MlDsa.Arm.Message.taintRel [] (fun _ _ _ r hr => by simp at hr) VG.Proof.MlDsa.Arm.Message.mov2_taint
  · -- The entry.
    let A : State → State → Prop := fun x a => VG.Proof.MlDsa.Arm.Message.AChk x a ∧ isa.eval .ne a = some false
    let B : State → State → Prop := fun x t => (stackArg x 0).toNat < 256 ∧
      ∃ a : State, a.mem = x.mem ∧ VG.Proof.MlDsa.Arm.Message.Ctx (VG.Proof.MlDsa.Arm.Message.slay p x) a.gpr a.mem t
    have hent := VG.Proof.MlDsa.Arm.Message.ghost_step (P := VG.Proof.MlDsa.Arm.Message.SP2 p) (A := A) (B := B) (c := .block (enter 12 p signLoads))
      (VG.Proof.MlDsa.Arm.Message.argRel [] 16 (fun a b ⟨x, y, hxy, f₁, f₂⟩ =>
        VG.Proof.MlDsa.Arm.Message.sAgree (VG.Proof.MlDsa.Arm.Message.sPre_of hxy.1) (VG.Proof.MlDsa.Arm.Message.sPre_of hxy.2.1) (VG.Proof.MlDsa.Arm.Message.sPub_of hxy.2.2) ⟨f₁.1.1.sp, f₁.1.1.wr, f₁.1.1.mem⟩
          ⟨f₂.1.1.sp, f₂.1.1.wr, f₂.1.1.mem⟩ (Nat.le_refl _)) (VG.Proof.MlDsa.Arm.Message.enterS_taint p))
      fun x y a b hxy fa fb => by
        have en : ∀ (x' a' : State), (signMessageContract p Arm.abi 36).pre x' → A x' a' →
            WP isa (.block (enter 12 p signLoads)) a' (B x') := fun x' a' hx ⟨⟨o, e⟩, ef⟩ => by
          have h8 : (stackArg x' 0).toNat < 256 := by
            rw [e] at ef; simpa using ef
          have h := VG.Proof.MlDsa.Arm.Message.sPre_of hx
          have hL := VG.Proof.MlDsa.Arm.Message.slay_ok hp h h8
          have hs1 : ∀ o', o' + 4 ≤ 16 → a'.mem.readW (State.addr (a'.sp + BitVec.ofNat 32 o')) 32 =
              x'.mem.readW (State.addr (x'.sp + BitVec.ofNat 32 o')) 32 := fun _ _ => by rw [o.mem, o.sp]
          exact WP.mono (VG.Proof.MlDsa.Arm.Message.enter_ok hL rfl (nA := 16) (by decide) (Nat.le_refl _) o.sp
            (by rw [o.rd]; rfl) (by rw [o.wr]; rfl) (o.get .r0) (o.get .r1) (o.get .r2) (o.get .r3)
            (fun o' ho => by rw [o.rd, o.wr, o.sp]; exact h.args ho) (by rw [o.sp]; exact h.spA)
            (by rw [o.sp, ← VG.Proof.MlDsa.Arm.Message.stackArgAddr0]; exact h.scrArgs) (by omega)
            (by rw [hs1 12 (by omega)]; exact VG.Proof.MlDsa.Arm.Message.stackArg_eq x' 3) (by decide) (fun j hj => by
              have hj4 : j < 4 := hj
              rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
              · exact (hs1 0 (by decide)).trans (VG.Proof.MlDsa.Arm.Message.stackArg_eq x' 0)
              · exact (hs1 4 (by decide)).trans (VG.Proof.MlDsa.Arm.Message.stackArg_eq x' 1)
              · exact (hs1 8 (by decide)).trans (VG.Proof.MlDsa.Arm.Message.stackArg_eq x' 2)
              · exact (hs1 12 (by decide)).trans (VG.Proof.MlDsa.Arm.Message.stackArg_eq x' 3)))
            fun t hc => ⟨h8, a', o.mem, hc⟩
        exact ⟨en x a hxy.1 fa, en y b hxy.2.1 fb⟩
    refine RelCT.seq (RelCT.mono hent (fun a b ⟨⟨x, y, hxy, f₁, f₂⟩, hc⟩ => ⟨x, y, hxy, ⟨f₁, hc⟩, ⟨f₂, by
      rw [f₂.2, ← (VG.Proof.MlDsa.Arm.Message.sPub_of hxy.2.2).a0, ← f₁.2]; exact hc⟩⟩) fun _ _ h => h)
      (RelCT.seq (RelCT.mono (VG.Proof.MlDsa.Arm.Message.signBody_tr hS hp) (fun a b ⟨x, y, hxy, ⟨h8x, a', ma, ca⟩,
        ⟨h8y, b', mb, cb⟩⟩ => ?_) fun _ _ h => h) (VG.Proof.MlDsa.Arm.Message.taintRel [.r7] (fun a b h r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact h.1) VG.Proof.MlDsa.Arm.Message.leave_taint))
    have hx := VG.Proof.MlDsa.Arm.Message.sPre_of hxy.1
    have hy := VG.Proof.MlDsa.Arm.Message.sPre_of hxy.2.1
    have hpub := VG.Proof.MlDsa.Arm.Message.sPub_of hxy.2.2
    have e := VG.Proof.MlDsa.Arm.Message.slay_eq hx hy hpub
    refine ⟨VG.Proof.MlDsa.Arm.Message.slay p x, a'.gpr, b'.gpr, a'.mem, b'.mem, VG.Proof.MlDsa.Arm.Message.slay_ok hp hx h8x, ?_, ca, e ▸ cb,
      ⟨x, hx, h8x, rfl, ma.symm⟩, ⟨y, hy, h8y, e.symm, mb.symm⟩⟩
    have lk := hpub.leak
    rw [← hpub.r0, ← hpub.r1, ← hpub.r2, ← hpub.r3, ← hpub.a0, ← hpub.a1] at lk
    unfold VG.Proof.MlDsa.Arm.Message.signI
    rw [ma, mb]
    exact lk

end

end VG.Proof.MlDsa.Arm.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Message.VerifyCT`. -/
section

/-!
# ML-DSA on ARMv7, `verify_message`: constant time

Untrusted: everything here is checked by Lean. Two runs from states that
satisfy the contract and agree on its public data, which include `pk`, the
message, the context string and the signature (`verifyI`), leak the same:
the branch on `ctx_len`, the entry and the exit depend only on the pointers
and the lengths; the hashing leaks only the layout (`trHash_tr`,
`muHash_tr`); and the call of the verification function on `μ` leaks only
`pk`, `μ` and `sig`, which are the same in both runs (`verifyCall_tr`).
-/

namespace VG.Proof.MlDsa.Arm.Message

open VG VG.Arm VG.Impl.MlDsa.Arm.Message
open VG.Proof.MlDsa.Message
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable {p : Params}

/-- The inputs of a run, with the memory `m`. -/
abbrev vIn (p : Params) (L : VG.Proof.MlDsa.Arm.Message.Lay) (m : Mem) : List Byte :=
  bytesAt m (State.addr L.key) p.pkLen ++ bytesAt m (State.addr L.msg) L.len.toNat ++
    bytesAt m (State.addr L.ctx) L.ctxLen.toNat ++ bytesAt m (State.addr L.sig) p.sigLen

/-- What the contract says two runs agree on, beyond the pointers and lengths. -/
def verifyI (p : Params) (L : VG.Proof.MlDsa.Arm.Message.Lay) (m₁ m₂ : Mem) : Prop := leakBytes (VG.Proof.MlDsa.Arm.Message.vIn p L m₁) = leakBytes (VG.Proof.MlDsa.Arm.Message.vIn p L m₂)

theorem verifyI_eq {L : VG.Proof.MlDsa.Arm.Message.Lay} {m₁ m₂ : Mem} (h : VG.Proof.MlDsa.Arm.Message.verifyI p L m₁ m₂) :
    bytesAt m₁ (State.addr L.key) p.pkLen = bytesAt m₂ (State.addr L.key) p.pkLen ∧
      bytesAt m₁ (State.addr L.msg) L.len.toNat = bytesAt m₂ (State.addr L.msg) L.len.toNat ∧
      bytesAt m₁ (State.addr L.ctx) L.ctxLen.toNat = bytesAt m₂ (State.addr L.ctx) L.ctxLen.toNat ∧
      bytesAt m₁ (State.addr L.sig) p.sigLen = bytesAt m₂ (State.addr L.sig) p.sigLen :=
  leak4 (by simp only [Proof.MlKem.bytesAt_length]) (by simp only [Proof.MlKem.bytesAt_length])
    (by simp only [Proof.MlKem.bytesAt_length]) h

/-- The layout is that of a run of `verify_message` from a state with the
memory `m`, past the branch on `ctx_len`. -/
def VOk (p : Params) (L : VG.Proof.MlDsa.Arm.Message.Lay) (m : Mem) : Prop :=
  ∃ σ, VG.Proof.MlDsa.Arm.Message.VPre p σ ∧ (stackArg σ 0).toNat < 256 ∧ VG.Proof.MlDsa.Arm.Message.vlay p σ = L ∧ σ.mem = m

/-- `tr` at `X + 840`. -/
def TrOk (p : Params) (L : VG.Proof.MlDsa.Arm.Message.Lay) (m : Mem) (t : State) : Prop :=
  bytesAt t.mem L.MU 64 = VG.Spec.MlDsa.H (bytesAt m (State.addr L.key) p.pkLen) 64

/-- `μ` at `X + 840`. -/
def VMuOk (p : Params) (L : VG.Proof.MlDsa.Arm.Message.Lay) (m : Mem) (t : State) : Prop :=
  bytesAt t.mem L.MU 64 = VG.Spec.MlDsa.H (VG.Spec.MlDsa.H (bytesAt m (State.addr L.key) p.pkLen) 64 ++ VG.Proof.MlDsa.Arm.Message.hdrBytes L ++
    bytesAt m (State.addr L.ctx) L.ctxLen.toNat ++ bytesAt m (State.addr L.msg) L.len.toNat) 64

/-- What a layout of `verify_message` says of `sig` and `scratch`. -/
structure VFacts (p : Params) (L : VG.Proof.MlDsa.Arm.Message.Lay) : Prop where
  key : L.keyLen = p.pkLen
  xSig : L.SC.Disjoint ⟨State.addr L.sig, p.sigLen⟩
  kSig : L.STK.Disjoint ⟨State.addr L.sig, p.sigLen⟩
  nSig : L.sig.toNat + p.sigLen ≤ 2 ^ 32
  inSig : (⟨State.addr L.sig, p.sigLen⟩ : Region) ∈ L.rd

theorem VOk.facts {L : VG.Proof.MlDsa.Arm.Message.Lay} {m : Mem} (h : VG.Proof.MlDsa.Arm.Message.VOk p L m) : VG.Proof.MlDsa.Arm.Message.VFacts p L := by
  obtain ⟨σ, hσ, _, rfl, -⟩ := h
  exact ⟨rfl, hσ.sigScr.symm, hσ.stkSig, hσ.nSig, by simp [VG.Proof.MlDsa.Arm.Message.vlay, hσ.rd]⟩

/-- The regions the verification function on `μ` is given, as functions of the layout. -/
abbrev vRd (p : Params) (L : VG.Proof.MlDsa.Arm.Message.Lay) : List Region :=
  [⟨State.addr L.key, p.pkLen⟩, ⟨L.MU, 64⟩, ⟨State.addr L.sig, p.sigLen⟩]
abbrev vWr (p : Params) (L : VG.Proof.MlDsa.Arm.Message.Lay) : List Region := [⟨State.addr L.scr, VG.Proof.MlDsa.Arm.Message.sScr p⟩]

/-- Two runs of the call of the verification function on `μ`. -/
theorem verifyCall_tr {n : String} {c : Prog isa} (hV : VG.Proof.MlDsa.Arm.Message.VerifyFn p c) (hp : p ∈ VG.Proof.MlDsa.Arm.Message.params) :
    RelCT isa (VG.Proof.MlDsa.Arm.Message.Two (VG.Proof.MlDsa.Arm.Message.verifyI p) fun L m t => VG.Proof.MlDsa.Arm.Message.VOk p L m ∧ VG.Proof.MlDsa.Arm.Message.VMuOk p L m t)
      (.seq (.block (VG.Impl.MlDsa.Arm.Message.setArgs VG.Proof.MlDsa.Arm.Message.verifyArgs)) (.call n c)) fun _ _ => True := by
  refine RelCT.seq (VG.Proof.MlDsa.Arm.Message.setArgs_two (by decide)) ?_
  refine RelCT.mono (P := fun a1 b1 => ∃ L : VG.Proof.MlDsa.Arm.Message.Lay, ∃ x y, (∃ g₁ g₂ m₁ m₂, L.Ok ∧ VG.Proof.MlDsa.Arm.Message.verifyI p L m₁ m₂ ∧
      VG.Proof.MlDsa.Arm.Message.Ctx L g₁ m₁ x ∧ VG.Proof.MlDsa.Arm.Message.Ctx L g₂ m₂ y ∧ (VG.Proof.MlDsa.Arm.Message.VOk p L m₁ ∧ VG.Proof.MlDsa.Arm.Message.VMuOk p L m₁ x) ∧ (VG.Proof.MlDsa.Arm.Message.VOk p L m₂ ∧ VG.Proof.MlDsa.Arm.Message.VMuOk p L m₂ y)) ∧
      VG.Proof.MlDsa.Arm.Message.Moved VG.Proof.MlDsa.Arm.Message.verifyArgs x a1 ∧ VG.Proof.MlDsa.Arm.Message.Moved VG.Proof.MlDsa.Arm.Message.verifyArgs y b1)
    (RelCT.exists_ fun L => RelCT.call hV.ver.1 hV.ver.2.1 (VG.Proof.MlDsa.Arm.Message.vRd p L) (VG.Proof.MlDsa.Arm.Message.vWr p L) fun a1 b1 h => ?_)
    (fun a1 b1 ⟨x, y, ⟨L, hp'⟩, f₁, f₂⟩ => ⟨L, x, y, hp', f₁, f₂⟩) fun _ _ h => h
  obtain ⟨x, y, ⟨g₁, g₂, m₁, m₂, hL, hi, c₁, c₂, ⟨φ₁, μ₁⟩, ⟨_, μ₂⟩⟩, f₁, f₂⟩ := h
  have F := φ₁.facts
  obtain ⟨σ, hσ, h8, rfl, -⟩ := φ₁
  have hL' := VG.Proof.MlDsa.Arm.Message.vlay_ok hp hσ h8
  have pre₁ := VG.Proof.MlDsa.Arm.Message.verifyK_pre hp hσ h8 c₁ f₁.1 (f₁.2.sp.trans c₁.sp)
  have pre₂ := VG.Proof.MlDsa.Arm.Message.verifyK_pre hp hσ h8 c₂ f₂.1 (f₂.2.sp.trans c₂.sp)
  have cv : ∀ {t t1 : State} {g m₀}, VG.Proof.MlDsa.Arm.Message.Ctx (VG.Proof.MlDsa.Arm.Message.vlay p σ) g m₀ t → VG.Proof.MlDsa.Arm.Message.Moved VG.Proof.MlDsa.Arm.Message.verifyArgs t t1 →
      Covers (VG.Proof.MlDsa.Arm.Message.vRd p (VG.Proof.MlDsa.Arm.Message.vlay p σ) ++ VG.Proof.MlDsa.Arm.Message.vWr p (VG.Proof.MlDsa.Arm.Message.vlay p σ)) (t1.rd ++ t1.wr) ∧ Covers (VG.Proof.MlDsa.Arm.Message.vWr p (VG.Proof.MlDsa.Arm.Message.vlay p σ)) t1.wr :=
    fun hc f => by
      rw [f.2.rd, f.2.wr, hc.rd, hc.wr]
      have hw : ∀ r ∈ VG.Proof.MlDsa.Arm.Message.vWr p (VG.Proof.MlDsa.Arm.Message.vlay p σ), ∃ R ∈ (VG.Proof.MlDsa.Arm.Message.vlay p σ).wr, Within r R := fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
        exact ⟨_, hL'.inSC, within_base _ (by simp only [VG.Proof.MlDsa.Arm.Message.vlay]; rw [VG.Proof.MlDsa.Arm.Message.mScr_eq]; simp only [VG.Proof.MlDsa.Arm.Message.sScr, oE]; omega)⟩
      refine ⟨VG.Proof.MlDsa.Arm.Message.covers_of_within fun r hr => ?_, VG.Proof.MlDsa.Arm.Message.covers_of_within hw⟩
      rcases List.mem_append.mp hr with h | h
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl
        · exact ⟨_, List.mem_append_left _ (F.key ▸ hL'.inKey), within_self _⟩
        · exact ⟨_, List.mem_append_right _ hL'.inSC, VG.Proof.MlDsa.Arm.Message.mu_within hL'⟩
        · exact ⟨_, List.mem_append_left _ F.inSig, within_self _⟩
      · obtain ⟨R, hR, w⟩ := hw r h
        exact ⟨R, List.mem_append_right _ hR, w⟩
  refine ⟨pre₁, pre₂, ?_, (cv c₁ f₁).1, (cv c₁ f₁).2, (cv c₂ f₂).1, (cv c₂ f₂).2⟩
  obtain ⟨x0, x1, x2, x3⟩ := VG.Proof.MlDsa.Arm.Message.verifyRegs_of hL' c₁ f₁.1
  obtain ⟨y0, y1, y2, y3⟩ := VG.Proof.MlDsa.Arm.Message.verifyRegs_of hL' c₂ f₂.1
  have ek : ∀ {g m₀} {a a1 : State}, VG.Proof.MlDsa.Arm.Message.Ctx (VG.Proof.MlDsa.Arm.Message.vlay p σ) g m₀ a → VG.Proof.MlDsa.Arm.Message.Moved VG.Proof.MlDsa.Arm.Message.verifyArgs a a1 →
      bytesAt a1.mem (State.addr (σ.gpr .r0)) p.pkLen = bytesAt m₀ (State.addr (σ.gpr .r0)) p.pkLen := fun c f => by
    rw [f.2.mem]
    exact c.bytesAt_eq (p := State.addr (VG.Proof.MlDsa.Arm.Message.vlay p σ).key) hL'.xKey hL'.kKey (by have := hσ.nPk; omega)
  have es : ∀ {g m₀} {a a1 : State}, VG.Proof.MlDsa.Arm.Message.Ctx (VG.Proof.MlDsa.Arm.Message.vlay p σ) g m₀ a → VG.Proof.MlDsa.Arm.Message.Moved VG.Proof.MlDsa.Arm.Message.verifyArgs a a1 →
      bytesAt a1.mem (State.addr (stackArg σ 1)) p.sigLen = bytesAt m₀ (State.addr (stackArg σ 1)) p.sigLen :=
    fun c f => by
      rw [f.2.mem]
      exact c.bytesAt_eq (p := State.addr (VG.Proof.MlDsa.Arm.Message.vlay p σ).sig) F.xSig F.kSig (by have := F.nSig; omega)
  have eμ : ∀ {a a1 : State}, VG.Proof.MlDsa.Arm.Message.Moved VG.Proof.MlDsa.Arm.Message.verifyArgs a a1 →
      bytesAt a1.mem (State.addr ((VG.Proof.MlDsa.Arm.Message.vlay p σ).X32 + BitVec.ofNat 32 840)) 64 = bytesAt a.mem (VG.Proof.MlDsa.Arm.Message.vlay p σ).MU 64 :=
    fun f => by rw [f.2.mem, VG.Proof.MlDsa.Arm.Message.mu_eq hL']
  obtain ⟨ik, im, ic, is⟩ := VG.Proof.MlDsa.Arm.Message.verifyI_eq hi
  have sw : ∀ a : BitVec 32, BitVec.setWidth 64 a = State.addr a := fun _ => rfl
  sig_pub [verifyContract, verifySig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [x0, x1, x2, x3, y0, y1, y2, y3, sw, and_true]
  refine ⟨by rw [f₁.2.sp, f₂.2.sp, c₁.sp, c₂.sp], ?_⟩
  rw [ek c₁ f₁, ek c₂ f₂, es c₁ f₁, es c₂ f₂, eμ f₁, eμ f₂, μ₁, μ₂]
  have ik' : bytesAt m₁ (State.addr (σ.gpr .r0)) p.pkLen = bytesAt m₂ (State.addr (σ.gpr .r0)) p.pkLen := ik
  have is' : bytesAt m₁ (State.addr (stackArg σ 1)) p.sigLen = bytesAt m₂ (State.addr (stackArg σ 1)) p.sigLen := is
  rw [ik, im, ic, ik', is']

/-- The public data of the contract, spelled out. -/
structure VPub (p : Params) (s₁ s₂ : State) : Prop where
  sp : s₁.sp = s₂.sp
  leak : leakBytes (bytesAt s₁.mem (State.addr (s₁.gpr .r0)) p.pkLen ++
      bytesAt s₁.mem (State.addr (s₁.gpr .r1)) (s₁.gpr .r2).toNat ++
      bytesAt s₁.mem (State.addr (s₁.gpr .r3)) (stackArg s₁ 0).toNat ++
      bytesAt s₁.mem (State.addr (stackArg s₁ 1)) p.sigLen) =
    leakBytes (bytesAt s₂.mem (State.addr (s₂.gpr .r0)) p.pkLen ++
      bytesAt s₂.mem (State.addr (s₂.gpr .r1)) (s₂.gpr .r2).toNat ++
      bytesAt s₂.mem (State.addr (s₂.gpr .r3)) (stackArg s₂ 0).toNat ++
      bytesAt s₂.mem (State.addr (stackArg s₂ 1)) p.sigLen)
  r0 : s₁.gpr .r0 = s₂.gpr .r0
  r1 : s₁.gpr .r1 = s₂.gpr .r1
  r2 : s₁.gpr .r2 = s₂.gpr .r2
  r3 : s₁.gpr .r3 = s₂.gpr .r3
  a0 : stackArg s₁ 0 = stackArg s₂ 0
  a1 : stackArg s₁ 1 = stackArg s₂ 1
  a2 : stackArg s₁ 2 = stackArg s₂ 2

theorem vPub_of {s₁ s₂ : State} (h : (verifyMessageContract p Arm.abi 36).pub s₁ s₂) : VG.Proof.MlDsa.Arm.Message.VPub p s₁ s₂ := by
  sig_pub [verifyMessageContract, verifyMessageSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨a, b, c, d, e, f, g, h, i⟩ := h
  exact ⟨a, b, c, d, e, f, g, h, i⟩

/-- Two runs from states agreeing on the public data have the same layout. -/
theorem vlay_eq {s₁ s₂ : State} (h₁ : VG.Proof.MlDsa.Arm.Message.VPre p s₁) (h₂ : VG.Proof.MlDsa.Arm.Message.VPre p s₂) (h : VG.Proof.MlDsa.Arm.Message.VPub p s₁ s₂) : VG.Proof.MlDsa.Arm.Message.vlay p s₁ = VG.Proof.MlDsa.Arm.Message.vlay p s₂ := by
  have e1 : s₁.rd = s₂.rd := by
    rw [h₁.rd, h₂.rd]
    simp only [VG.Proof.MlDsa.Arm.Message.rKey, VG.Proof.MlDsa.Arm.Message.rMsg, VG.Proof.MlDsa.Arm.Message.rCtx, VG.Proof.MlDsa.Arm.Message.rArgs, VG.Proof.MlDsa.Arm.Message.sArg, VG.Proof.MlDsa.Arm.Message.stackArgAddr0, h.sp, h.r0, h.r1, h.r2, h.r3, h.a0, h.a1]
  have e2 : s₁.wr = s₂.wr := by
    rw [h₁.wr, h₂.wr]; simp only [VG.Proof.MlDsa.Arm.Message.sArg, h.a2]
  simp only [VG.Proof.MlDsa.Arm.Message.vlay, h.sp, h.r0, h.r1, h.r2, h.r3, h.a0, h.a1, h.a2, e1, e2]

/-- The body, between the entry and the exit: its runs end with the same
`r7` and stack pointer. -/
theorem verifyBody_tr {n : String} {c : Prog isa} (hV : VG.Proof.MlDsa.Arm.Message.VerifyFn p c) (hp : p ∈ VG.Proof.MlDsa.Arm.Message.params) :
    RelCT isa (VG.Proof.MlDsa.Arm.Message.Two (VG.Proof.MlDsa.Arm.Message.verifyI p) fun L m _ => VG.Proof.MlDsa.Arm.Message.VOk p L m)
      (.seq (VG.Impl.MlDsa.Arm.Message.trHash p) (.seq (muHash (.off oMU)) (.seq (.block (VG.Impl.MlDsa.Arm.Message.setArgs VG.Proof.MlDsa.Arm.Message.verifyArgs)) (.call n c))))
      fun a b => a.gpr .r7 = b.gpr .r7 ∧ a.sp = b.sp := by
  have th := VG.Proof.MlDsa.Arm.Message.trHash_tr (I := VG.Proof.MlDsa.Arm.Message.verifyI p) (Φ := fun L m _ => VG.Proof.MlDsa.Arm.Message.VOk p L m) (VG.Proof.MlDsa.Arm.Message.pkLen_ge hp).2
    (fun _ _ _ h => h.facts.key)
  have th' := VG.Proof.MlDsa.Arm.Message.two_wp (I := VG.Proof.MlDsa.Arm.Message.verifyI p) (Φ := fun L m _ => VG.Proof.MlDsa.Arm.Message.VOk p L m) (Ψ := fun L m t => VG.Proof.MlDsa.Arm.Message.VOk p L m ∧ VG.Proof.MlDsa.Arm.Message.TrOk p L m t) th
    fun L g m₀ t hL hc hφ => WP.mono (VG.Proof.MlDsa.Arm.Message.trHash_ok hL hφ.facts.key hc) fun t' ⟨hc', htr⟩ =>
      ⟨hc', hφ, by unfold VG.Proof.MlDsa.Arm.Message.TrOk; rw [htr, hφ.facts.key]⟩
  have side : ∀ L : VG.Proof.MlDsa.Arm.Message.Lay, L.Ok → (L.X32 + BitVec.ofNat 32 840).toNat + 64 ≤ 2 ^ 32 ∧
      (∃ R ∈ L.rd ++ L.wr, Within ⟨State.addr (L.X32 + BitVec.ofNat 32 840), 64⟩ R) ∧
      Region.Disjoint ⟨State.addr (L.X32 + BitVec.ofNat 32 840), 64⟩ ⟨L.ST, 200⟩ ∧
      Region.Disjoint ⟨State.addr (L.X32 + BitVec.ofNat 32 840), 64⟩ ⟨L.KS, 640⟩ ∧
      L.STK.Disjoint ⟨State.addr (L.X32 + BitVec.ofNat 32 840), 64⟩ := fun L hL => by
    obtain ⟨R, hR, hw⟩ := hL.covX (e := 840) (k := 64) (by omega)
    rw [VG.Proof.MlDsa.Arm.Message.mu_eq hL]
    exact ⟨by have := hL.x32_lt; rw [VG.Proof.MlDsa.Arm.Message.x32_toNat hL (by omega)]; omega, ⟨R, by simp [hR], hw⟩, st_mu.symm, VG.Proof.MlDsa.Arm.Message.mu_ks,
      VG.Proof.MlDsa.Arm.Message.k_mu hL⟩
  have mh := VG.Proof.MlDsa.Arm.Message.muHash_tr (I := VG.Proof.MlDsa.Arm.Message.verifyI p) (Φ := fun L m t => VG.Proof.MlDsa.Arm.Message.VOk p L m ∧ VG.Proof.MlDsa.Arm.Message.TrOk p L m t) (tr := .off oMU)
    (by decide) rfl (fun L => L.X32 + BitVec.ofNat 32 840) (fun L g m t _ hc => hc.off oMU) side
  have mh' := VG.Proof.MlDsa.Arm.Message.two_wp (I := VG.Proof.MlDsa.Arm.Message.verifyI p) (Φ := fun L m t => VG.Proof.MlDsa.Arm.Message.VOk p L m ∧ VG.Proof.MlDsa.Arm.Message.TrOk p L m t)
    (Ψ := fun L m t => VG.Proof.MlDsa.Arm.Message.VOk p L m ∧ VG.Proof.MlDsa.Arm.Message.VMuOk p L m t) mh fun L g m₀ t hL hc hφ => by
      obtain ⟨a, b, c, d, e⟩ := side L hL
      refine WP.mono (VG.Proof.MlDsa.Arm.Message.muHash_ok hL hc (tr := .off oMU) (trp := L.X32 + BitVec.ofNat 32 840) (by decide) rfl
        (fun t' hc' => hc'.off oMU) a b c d e) fun t' ⟨hc', hμ⟩ => ⟨hc', hφ.1, ?_⟩
      unfold VG.Proof.MlDsa.Arm.Message.VMuOk
      rw [hμ]
      have h2 := hφ.2
      unfold VG.Proof.MlDsa.Arm.Message.TrOk at h2
      rw [VG.Proof.MlDsa.Arm.Message.mu_eq hL, h2]
  refine RelCT.postDep (F := fun x x' => x'.gpr .r7 = x.gpr .r7 ∧ x'.sp = x.sp)
    (th'.seq (mh'.seq (VG.Proof.MlDsa.Arm.Message.verifyCall_tr hV hp))) (fun x y hxy => ?_) fun x y x' y' hxy f₁ f₂ => ?_
  · have run : ∀ {L : VG.Proof.MlDsa.Arm.Message.Lay} {g m₀} {t : State}, L.Ok → VG.Proof.MlDsa.Arm.Message.Ctx L g m₀ t → VG.Proof.MlDsa.Arm.Message.VOk p L m₀ →
        WP isa (.seq (VG.Impl.MlDsa.Arm.Message.trHash p) (.seq (muHash (.off oMU)) (.seq (.block (VG.Impl.MlDsa.Arm.Message.setArgs VG.Proof.MlDsa.Arm.Message.verifyArgs)) (.call n c)))) t
          fun t' => t'.gpr .r7 = t.gpr .r7 ∧ t'.sp = t.sp := fun hL hc hφ => by
      obtain ⟨σ, hσ, h8, rfl, -⟩ := hφ
      obtain ⟨a, b, c, d, e⟩ := side _ hL
      refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Message.trHash_ok hL rfl hc) fun t₁ ⟨hc₁, _⟩ => ?_)
      refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Message.muHash_ok hL hc₁ (tr := .off oMU) (trp := (VG.Proof.MlDsa.Arm.Message.vlay p σ).X32 + BitVec.ofNat 32 840)
        (by decide) rfl (fun t' hc' => hc'.off oMU) a b c d e) fun t₂ ⟨hc₂, _⟩ => ?_)
      exact WP.mono (VG.Proof.MlDsa.Arm.Message.verifyCall_ok hV hp hσ h8 hc₂) fun s' ⟨hf, _⟩ =>
        ⟨hf.r7.trans hc.r7.symm, hf.sp.trans hc.sp.symm⟩
    obtain ⟨L, _, _, _, _, hL, _, c₁, c₂, φ₁, φ₂⟩ := hxy
    exact ⟨run hL c₁ φ₁, run hL c₂ φ₂⟩
  · obtain ⟨L, _, _, _, _, _, _, c₁, c₂, _, _⟩ := hxy
    exact ⟨by rw [f₁.1, f₂.1, c₁.r7, c₂.r7], by rw [f₁.2, f₂.2, c₁.sp, c₂.sp]⟩

/-- Two states with the stack pointer, permissions and memory of two entry
states agreeing on the public data agree on the first `n ≤ 12` bytes of the
arguments on the stack. -/
theorem vAgree {x y a b : State} (hx : VG.Proof.MlDsa.Arm.Message.VPre p x) (hy : VG.Proof.MlDsa.Arm.Message.VPre p y) (hpub : VG.Proof.MlDsa.Arm.Message.VPub p x y)
    (ha : a.sp = x.sp ∧ a.wr = x.wr ∧ a.mem = x.mem) (hb : b.sp = y.sp ∧ b.wr = y.wr ∧ b.mem = y.mem)
    {n : Nat} (hn : n ≤ 12) : VG.Arm.Taint.Agree (argTaint [] n) a b := by
  have w : ∀ {z c : State}, VG.Proof.MlDsa.Arm.Message.VPre p z → c.sp = z.sp ∧ c.wr = z.wr ∧ c.mem = z.mem →
      c.sp.toNat + n ≤ 2 ^ 32 ∧ ∀ r ∈ c.wr, Region.Disjoint ⟨State.addr c.sp, n⟩ r := fun {z c} hz hc => by
    refine ⟨by rw [hc.1]; have := hz.spA; omega, fun r hr => ?_⟩
    rw [hc.2.1, hz.wr] at hr
    have hs : Region.Sub ⟨State.addr c.sp, n⟩ (VG.Proof.MlDsa.Arm.Message.rArgs z 12) := by
      simp only [VG.Proof.MlDsa.Arm.Message.rArgs, VG.Proof.MlDsa.Arm.Message.stackArgAddr0, hc.1]; exact Region.sub_prefix hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact (hz.scrArgs.sub_right hs).symm
  have hsp : a.sp = b.sp := by rw [ha.1, hb.1, hpub.sp]
  refine agree_argTaint (fun r hr => by simp at hr) hsp (w hx ha) (w hy hb) fun k hk => ?_
  exact argMem_of (s₁ := a) (s₂ := b) (j := 3) hsp (by rw [ha.1]; have := hx.spA; omega) (fun i hi => by
    simp only [stackArg, stackArgAddr, ha.1, hb.1, ha.2.2, hb.2.2]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · exact hpub.a0
    · exact hpub.a1
    · exact hpub.a2) k (by omega)

/-- The entry states of two runs: the precondition and the public data. -/
abbrev VP2 (p : Params) (x y : State) : Prop :=
  (verifyMessageContract p Arm.abi 36).pre x ∧ (verifyMessageContract p Arm.abi 36).pre y ∧
    (verifyMessageContract p Arm.abi 36).pub x y

theorem enterV_taint (p : Params) :
    (VG.Arm.taint.check (argTaint [] 12) (.block (enter 8 p verifyLoads)) (.block [])).isSome = true := by
  rfl

theorem verifyMessage_ct {n : String} {c : Prog isa} (hV : VG.Proof.MlDsa.Arm.Message.VerifyFn p c) (hp : p ∈ VG.Proof.MlDsa.Arm.Message.params) :
    ConstantTime isa (verifyMessageContract p Arm.abi 36).pre (verifyMessageContract p Arm.abi 36).pub
      (verifyMessage n c p) := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  have e0 : (fun s₁ s₂ => (verifyMessageContract p Arm.abi 36).pre s₁ ∧
      (verifyMessageContract p Arm.abi 36).pre s₂ ∧ (verifyMessageContract p Arm.abi 36).pub s₁ s₂) =
      VG.Proof.MlDsa.Arm.Message.Ghost (VG.Proof.MlDsa.Arm.Message.VP2 p) (fun x a => a = x) := by
    funext a b; apply propext
    exact ⟨fun h => ⟨a, b, h, rfl, rfl⟩, fun ⟨_, _, h, e₁, e₂⟩ => e₁ ▸ e₂ ▸ h⟩
  rw [e0]
  unfold verifyMessage top
  have hchk := VG.Proof.MlDsa.Arm.Message.ghost_step (P := VG.Proof.MlDsa.Arm.Message.VP2 p) (A := fun x a => a = x) (B := VG.Proof.MlDsa.Arm.Message.AChk)
    (c := .block [.ldrSp .r12 0, .mov .r12 (.shifted .r12 .lsr 8), .cmp .r12 (.imm 0)])
    (VG.Proof.MlDsa.Arm.Message.argRel [] 4 (fun a b ⟨x, y, hxy, e₁, e₂⟩ => by
      subst e₁ e₂
      exact VG.Proof.MlDsa.Arm.Message.vAgree (VG.Proof.MlDsa.Arm.Message.vPre_of hxy.1) (VG.Proof.MlDsa.Arm.Message.vPre_of hxy.2.1) (VG.Proof.MlDsa.Arm.Message.vPub_of hxy.2.2) ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ (by omega))
      VG.Proof.MlDsa.Arm.Message.chk_taint)
    fun x y a b hxy e₁ e₂ => by
      subst e₁ e₂; exact ⟨VG.Proof.MlDsa.Arm.Message.chk_ok ((VG.Proof.MlDsa.Arm.Message.vPre_of hxy.1).args (by omega)), VG.Proof.MlDsa.Arm.Message.chk_ok ((VG.Proof.MlDsa.Arm.Message.vPre_of hxy.2.1).args (by omega))⟩
  refine RelCT.seq hchk (RelCT.ite (fun a b ⟨x, y, hxy, f₁, f₂⟩ => by
    rw [f₁.2, f₂.2, (VG.Proof.MlDsa.Arm.Message.vPub_of hxy.2.2).a0]) ?_ ?_)
  · exact VG.Proof.MlDsa.Arm.Message.taintRel [] (fun _ _ _ r hr => by simp at hr) VG.Proof.MlDsa.Arm.Message.mov2_taint
  · let A : State → State → Prop := fun x a => VG.Proof.MlDsa.Arm.Message.AChk x a ∧ isa.eval .ne a = some false
    let B : State → State → Prop := fun x t => (stackArg x 0).toNat < 256 ∧
      ∃ a : State, a.mem = x.mem ∧ VG.Proof.MlDsa.Arm.Message.Ctx (VG.Proof.MlDsa.Arm.Message.vlay p x) a.gpr a.mem t
    have hent := VG.Proof.MlDsa.Arm.Message.ghost_step (P := VG.Proof.MlDsa.Arm.Message.VP2 p) (A := A) (B := B) (c := .block (enter 8 p verifyLoads))
      (VG.Proof.MlDsa.Arm.Message.argRel [] 12 (fun a b ⟨x, y, hxy, f₁, f₂⟩ =>
        VG.Proof.MlDsa.Arm.Message.vAgree (VG.Proof.MlDsa.Arm.Message.vPre_of hxy.1) (VG.Proof.MlDsa.Arm.Message.vPre_of hxy.2.1) (VG.Proof.MlDsa.Arm.Message.vPub_of hxy.2.2) ⟨f₁.1.1.sp, f₁.1.1.wr, f₁.1.1.mem⟩
          ⟨f₂.1.1.sp, f₂.1.1.wr, f₂.1.1.mem⟩ (Nat.le_refl _)) (VG.Proof.MlDsa.Arm.Message.enterV_taint p))
      fun x y a b hxy fa fb => by
        have en : ∀ (x' a' : State), (verifyMessageContract p Arm.abi 36).pre x' → A x' a' →
            WP isa (.block (enter 8 p verifyLoads)) a' (B x') := fun x' a' hx ⟨⟨o, e⟩, ef⟩ => by
          have h8 : (stackArg x' 0).toNat < 256 := by
            rw [e] at ef; simpa using ef
          have h := VG.Proof.MlDsa.Arm.Message.vPre_of hx
          have hL := VG.Proof.MlDsa.Arm.Message.vlay_ok hp h h8
          have hs1 : ∀ o', o' + 4 ≤ 12 → a'.mem.readW (State.addr (a'.sp + BitVec.ofNat 32 o')) 32 =
              x'.mem.readW (State.addr (x'.sp + BitVec.ofNat 32 o')) 32 := fun _ _ => by rw [o.mem, o.sp]
          exact WP.mono (VG.Proof.MlDsa.Arm.Message.enter_ok hL rfl (nA := 12) (by decide) (by omega) o.sp
            (by rw [o.rd]; rfl) (by rw [o.wr]; rfl) (o.get .r0) (o.get .r1) (o.get .r2) (o.get .r3)
            (fun o' ho => by rw [o.rd, o.wr, o.sp]; exact h.args ho) (by rw [o.sp]; exact h.spA)
            (by rw [o.sp, ← VG.Proof.MlDsa.Arm.Message.stackArgAddr0]; exact h.scrArgs) (by omega)
            (by rw [hs1 8 (by omega)]; exact VG.Proof.MlDsa.Arm.Message.stackArg_eq x' 2) (by decide) (fun j hj => by
              have hj4 : j < 4 := hj
              rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
              · exact (hs1 0 (by decide)).trans (VG.Proof.MlDsa.Arm.Message.stackArg_eq x' 0)
              · exact (hs1 4 (by decide)).trans (VG.Proof.MlDsa.Arm.Message.stackArg_eq x' 1)
              · exact (hs1 4 (by decide)).trans (VG.Proof.MlDsa.Arm.Message.stackArg_eq x' 1)
              · exact (hs1 8 (by decide)).trans (VG.Proof.MlDsa.Arm.Message.stackArg_eq x' 2)))
            fun t hc => ⟨h8, a', o.mem, hc⟩
        exact ⟨en x a hxy.1 fa, en y b hxy.2.1 fb⟩
    refine RelCT.seq (RelCT.mono hent (fun a b ⟨⟨x, y, hxy, f₁, f₂⟩, hc⟩ => ⟨x, y, hxy, ⟨f₁, hc⟩, ⟨f₂, by
      rw [f₂.2, ← (VG.Proof.MlDsa.Arm.Message.vPub_of hxy.2.2).a0, ← f₁.2]; exact hc⟩⟩) fun _ _ h => h)
      (RelCT.seq (RelCT.mono (VG.Proof.MlDsa.Arm.Message.verifyBody_tr hV hp) (fun a b ⟨x, y, hxy, ⟨h8x, a', ma, ca⟩,
        ⟨h8y, b', mb, cb⟩⟩ => ?_) fun _ _ h => h) (VG.Proof.MlDsa.Arm.Message.taintRel [.r7] (fun a b h r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact h.1) VG.Proof.MlDsa.Arm.Message.leave_taint))
    have hx := VG.Proof.MlDsa.Arm.Message.vPre_of hxy.1
    have hy := VG.Proof.MlDsa.Arm.Message.vPre_of hxy.2.1
    have hpub := VG.Proof.MlDsa.Arm.Message.vPub_of hxy.2.2
    have e := VG.Proof.MlDsa.Arm.Message.vlay_eq hx hy hpub
    refine ⟨VG.Proof.MlDsa.Arm.Message.vlay p x, a'.gpr, b'.gpr, a'.mem, b'.mem, VG.Proof.MlDsa.Arm.Message.vlay_ok hp hx h8x, ?_, ca, e ▸ cb,
      ⟨x, hx, h8x, rfl, ma.symm⟩, ⟨y, hy, h8y, e.symm, mb.symm⟩⟩
    have lk := hpub.leak
    rw [← hpub.r0, ← hpub.r1, ← hpub.r2, ← hpub.r3, ← hpub.a0, ← hpub.a1] at lk
    unfold VG.Proof.MlDsa.Arm.Message.verifyI
    rw [ma, mb]
    exact lk

end

end VG.Proof.MlDsa.Arm.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Message.Verified`. -/
section

/-!
# ML-DSA on ARMv7, `sign_message` and `verify_message`: verified

Untrusted: everything here is checked by Lean. `signMessage n c p` and
`verifyMessage n c p`, for any functions on `μ` `c` they can call
(`SignFn`, `VerifyFn`), are verified against `signMessageContract p Arm.abi
36` and `verifyMessageContract p Arm.abi 36`; `vg_mldsa*_sign` and
`vg_mldsa*_verify` are such functions (`sign44Fn`, …).
-/

namespace VG.Proof.MlDsa.Arm.Message

open VG VG.Arm VG.Impl.MlDsa.Arm.Message
open VG.Spec.MlDsa

/-- A state satisfying the precondition of signing: `ctx_len = 0`, `rnd`,
`sig` and `scratch` on the stack. -/
def signSat (p : Params) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x3000 | .r3 => 0x3100
    | _ => 0
  sp := 0x80000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x80005 then 0x32 else if a = 0x80009 then 0x40 else if a = 0x8000E then 1 else 0
  rd := [⟨0x1000, p.skLen⟩, ⟨0x3000, 0⟩, ⟨0x3100, 0⟩, ⟨0x3200, 32⟩, ⟨0x80000, 16⟩]
  wr := [⟨0x4000, p.sigLen⟩, ⟨0x10000, VG.Proof.MlDsa.Arm.Message.mScrLen p⟩]

theorem signMessage_sat {p : Params} (hp : p ∈ VG.Proof.MlDsa.Arm.Message.params) : ∃ s, (signMessageContract p Arm.abi 36).pre s := by
  simp only [VG.Proof.MlDsa.Arm.Message.params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · sig_implies_sat [signMessageContract, signMessageSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
      [signSat] using VG.Proof.MlDsa.Arm.Message.signSat mlDsa44
  · sig_implies_sat [signMessageContract, signMessageSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
      [signSat] using VG.Proof.MlDsa.Arm.Message.signSat mlDsa65
  · sig_implies_sat [signMessageContract, signMessageSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
      [signSat] using VG.Proof.MlDsa.Arm.Message.signSat mlDsa87

theorem signMessage_verified {p : Params} {n : String} {c : Prog isa} (hS : VG.Proof.MlDsa.Arm.Message.SignFn p c) (hp : p ∈ VG.Proof.MlDsa.Arm.Message.params) :
    Verified Arm.target (signMessage n c p) (signMessageContract p Arm.abi 36) :=
  ⟨fun _ h => let ⟨t, s', he, ha, hq⟩ := VG.Proof.MlDsa.Arm.Message.signMessage_wp hS hp h; ⟨t, s', he, ha, hq⟩,
    VG.Proof.MlDsa.Arm.Message.signMessage_ct hS hp, VG.Proof.MlDsa.Arm.Message.signMessage_sat hp⟩

/-- A state satisfying the precondition of verification: `ctx_len = 0`, `sig`
and `scratch` on the stack. -/
def verifySat (p : Params) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x3000 | .r3 => 0x3100
    | _ => 0
  sp := 0x80000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x80005 then 0x32 else if a = 0x8000A then 1 else 0
  rd := [⟨0x1000, p.pkLen⟩, ⟨0x3000, 0⟩, ⟨0x3100, 0⟩, ⟨0x3200, p.sigLen⟩, ⟨0x80000, 12⟩]
  wr := [⟨0x10000, VG.Proof.MlDsa.Arm.Message.mScrLen p⟩]

theorem verifyMessage_sat {p : Params} (hp : p ∈ VG.Proof.MlDsa.Arm.Message.params) : ∃ s, (verifyMessageContract p Arm.abi 36).pre s := by
  simp only [VG.Proof.MlDsa.Arm.Message.params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · sig_implies_sat [verifyMessageContract, verifyMessageSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] [verifySat] using VG.Proof.MlDsa.Arm.Message.verifySat mlDsa44
  · sig_implies_sat [verifyMessageContract, verifyMessageSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] [verifySat] using VG.Proof.MlDsa.Arm.Message.verifySat mlDsa65
  · sig_implies_sat [verifyMessageContract, verifyMessageSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] [verifySat] using VG.Proof.MlDsa.Arm.Message.verifySat mlDsa87

theorem verifyMessage_verified {p : Params} {n : String} {c : Prog isa} (hV : VG.Proof.MlDsa.Arm.Message.VerifyFn p c) (hp : p ∈ VG.Proof.MlDsa.Arm.Message.params) :
    Verified Arm.target (verifyMessage n c p) (verifyMessageContract p Arm.abi 36) :=
  ⟨fun _ h => let ⟨t, s', he, ha, hq⟩ := VG.Proof.MlDsa.Arm.Message.verifyMessage_wp hV hp h; ⟨t, s', he, ha, hq⟩,
    VG.Proof.MlDsa.Arm.Message.verifyMessage_ct hV hp, VG.Proof.MlDsa.Arm.Message.verifyMessage_sat hp⟩

/-! ## The functions on `μ` -/

theorem sign44Fn : VG.Proof.MlDsa.Arm.Message.SignFn mlDsa44 (Impl.MlDsa.Arm.Sign.sign Sign.prims mlDsa44) :=
  ⟨Sign.sign44_verified', by decide +kernel⟩
theorem sign65Fn : VG.Proof.MlDsa.Arm.Message.SignFn mlDsa65 (Impl.MlDsa.Arm.Sign.sign Sign.prims mlDsa65) :=
  ⟨Sign.sign65_verified', by decide +kernel⟩
theorem sign87Fn : VG.Proof.MlDsa.Arm.Message.SignFn mlDsa87 (Impl.MlDsa.Arm.Sign.sign Sign.prims mlDsa87) :=
  ⟨Sign.sign87_verified', by decide +kernel⟩

theorem verify44Fn : VG.Proof.MlDsa.Arm.Message.VerifyFn mlDsa44 Impl.MlDsa.Arm.Verify.verify44 :=
  ⟨Verify.verify44_verified, by decide +kernel⟩
theorem verify65Fn : VG.Proof.MlDsa.Arm.Message.VerifyFn mlDsa65 Impl.MlDsa.Arm.Verify.verify65 :=
  ⟨Verify.verify65_verified, by decide +kernel⟩
theorem verify87Fn : VG.Proof.MlDsa.Arm.Message.VerifyFn mlDsa87 Impl.MlDsa.Arm.Verify.verify87 :=
  ⟨Verify.verify87_verified, by decide +kernel⟩

end VG.Proof.MlDsa.Arm.Message

end
