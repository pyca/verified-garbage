module

public import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyTopSpec
public import VerifiedGarbage.Proof.SlhDsa.X86_64.Contracts
public import VerifiedGarbage.Impl.SlhDsa.X86_64.Verify
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsCorrect
import VerifiedGarbage.Proof.SlhDsa.X86_64.WotsBlocks
import VerifiedGarbage.Proof.SlhDsa.X86_64.Thash4AvxCorrect

/-!
# SLH-DSA (SHAKE) on x86-64, `verify`: where everything is

Untrusted: everything here is checked by Lean. A run of `verify` (`VL`):
the stack it uses, `st + 80` bytes from `B` up (the calls' `st + 8` bytes,
`CS`, then the frame of nine words, `FR`, from `SP`), `scratch` at `S`, and
the buffers. `Ctx` is what holds in the frame once its prologue has saved the
callee-saved registers and set up `scratch`: the permissions, `rsp`, `rbx`,
the callee-saved registers, the frame's slots and the formatted message's two
bytes, the saved registers, the round constants, `PK.seed` and `PK.root` and
`PK.seed` in every lane, and that memory changed only in `scratch` and the
stack. Writes elsewhere in `scratch`, or in `CS`, keep it (`Ctx.of_frame`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.VerifyTop

open VG VG.X86_64
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.X86_64 (Layout savedRegs)
open VG.Impl.SlhDsa.X86_64.Shake (oKgSave)

/-- A run of `verify`. -/
structure VL where
  /-- The lowest byte of the stack it uses. -/
  B : Addr
  /-- The stack of its calls but their return address. -/
  st : Nat
  S : Addr
  pk : Addr
  msg : Addr
  len : BitVec 64
  ctx : Addr
  ctxLen : BitVec 64
  sig : Addr
  sigL : Nat
  n : Nat

namespace VL

variable (L : VL)

abbrev SP : Addr := L.B + BitVec.ofNat 64 (L.st + 8)
abbrev FR : Region := ⟨L.SP, 72⟩
abbrev STK : Region := ⟨L.B, L.st + 80⟩
abbrev CS : Region := ⟨L.B, L.st + 8⟩
abbrev RET : Region := ⟨L.B + BitVec.ofNat 64 (L.st + 80), 8⟩
abbrev ARGS : Region := ⟨L.B + BitVec.ofNat 64 (L.st + 88), 16⟩
abbrev SCR : Region := ⟨L.S, 65536⟩
abbrev PK : Region := ⟨L.pk, 2 * L.n⟩
abbrev MSG : Region := ⟨L.msg, L.len.toNat⟩
abbrev CTX : Region := ⟨L.ctx, L.ctxLen.toNat⟩
abbrev SIG : Region := ⟨L.sig, L.sigL⟩
abbrev rd : List Region := [L.PK, L.MSG, L.CTX, L.SIG, L.ARGS]

/-- The parts of `scratch` `Ctx` keeps: the round constants, `PK.seed`,
`PK.root`, the saved registers, and the lanes' `PK.seed`. -/
def prot : List Region :=
  [⟨at' L.S 1600, 768⟩, ⟨at' L.S Layout.oPkSeed, L.n⟩, ⟨at' L.S Layout.oPkRoot, L.n⟩, ⟨at' L.S oKgSave, 48⟩] ++
    (List.range 4).flatMap fun k => [⟨at' L.S (Layout.laneA k), L.n⟩, ⟨at' L.S (Layout.laneB k), L.n⟩]

/-- What the precondition says of where everything is. -/
structure Ok : Prop where
  nB : L.B.toNat + L.st + 104 ≤ 2 ^ 64
  st62 : L.st < 2 ^ 62
  st16 : 16 ≤ L.st
  nS : L.S.toNat + 65536 ≤ 2 ^ 64
  nPk : L.pk.toNat + 2 * L.n ≤ 2 ^ 64
  nMsg : L.msg.toNat + L.len.toNat ≤ 2 ^ 64
  nCtx : L.ctx.toNat + L.ctxLen.toNat ≤ 2 ^ 64
  nSig : L.sig.toNat + L.sigL ≤ 2 ^ 64
  ctxLt : L.ctxLen.toNat < 256
  n : L.n = 16 ∨ L.n = 24 ∨ L.n = 32
  sPk : L.SCR.Disjoint L.PK
  sMsg : L.SCR.Disjoint L.MSG
  sCtx : L.SCR.Disjoint L.CTX
  sSig : L.SCR.Disjoint L.SIG
  sArgs : L.SCR.Disjoint L.ARGS
  kPk : L.STK.Disjoint L.PK
  kMsg : L.STK.Disjoint L.MSG
  kCtx : L.STK.Disjoint L.CTX
  kSig : L.STK.Disjoint L.SIG
  kScr : L.STK.Disjoint L.SCR
  rScr : L.RET.Disjoint L.SCR
  rPk : L.RET.Disjoint L.PK
  rMsg : L.RET.Disjoint L.MSG
  rCtx : L.RET.Disjoint L.CTX
  rSig : L.RET.Disjoint L.SIG

end VL

/-- A part of `scratch` `Ctx` does not keep, or of the calls' stack. -/
def Free (L : VL) (r : Region) : Prop :=
  (Region.Sub r L.SCR ∧ ∀ q ∈ L.prot, r.Disjoint q) ∨ Region.Sub r L.CS

/-- In the frame, after its prologue: `g` are the registers on entry, `m₀`
the memory. (MXCSR, which no code of `verify` loads, is kept by all of it.) -/
structure Ctx (L : VL) (g : Reg → BitVec 64) (m₀ : Mem) (t : State) : Prop where
  rd : t.rd = L.rd
  wr : t.wr = L.FR :: [L.SCR]
  rsp : t.gpr .rsp = L.SP
  rbx : t.gpr .rbx = L.S
  cs : ∀ r ∈ calleeSaved, r ≠ .rsp → r ≠ .rbx → t.gpr r = g r
  saved : ∀ i < 6, t.mem.readW (at' L.S (oKgSave + 8 * i)) 64 = g (savedRegs.getD i .rbx)
  pScr : t.mem.readW (L.SP + BitVec.ofNat 64 8) 64 = L.S
  pSig : t.mem.readW (L.SP + BitVec.ofNat 64 16) 64 = L.sig
  pSigL : t.mem.readW (L.SP + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 L.sigL
  pCtxLen : t.mem.readW (L.SP + BitVec.ofNat 64 32) 64 = L.ctxLen
  pCtx : t.mem.readW (L.SP + BitVec.ofNat 64 40) 64 = L.ctx
  pLen : t.mem.readW (L.SP + BitVec.ofNat 64 48) 64 = L.len
  pMsg : t.mem.readW (L.SP + BitVec.ofNat 64 56) 64 = L.msg
  pKey : t.mem.readW (L.SP + BitVec.ofNat 64 64) 64 = L.pk
  hdr : bytesAt t.mem L.SP 2 = [0, BitVec.ofNat 8 L.ctxLen.toNat]
  frame : Frame [L.SCR, L.STK] m₀ t.mem
  rc : RcTable t.mem L.S
  kSeed : bytesAt t.mem (at' L.S Layout.oPkSeed) L.n = bytesAt m₀ L.pk L.n
  kRoot : bytesAt t.mem (at' L.S Layout.oPkRoot) L.n = bytesAt m₀ (L.pk + BitVec.ofNat 64 L.n) L.n
  seedA : ∀ k < 4, bytesAt t.mem (at' L.S (Layout.laneA k)) L.n = bytesAt m₀ L.pk L.n
  seedB : ∀ k < 4, bytesAt t.mem (at' L.S (Layout.laneB k)) L.n = bytesAt m₀ L.pk L.n

namespace VL.Ok

variable {L : VL}

theorem n32 (h : L.Ok) : L.n ≤ 32 := by have := h.n; omega

/-- Two parts of the stack. -/
theorem stk (h : L.Ok) {d n e k : Nat} (h₁ : d + n ≤ e ∨ e + k ≤ d) (h₂ : d + n ≤ L.st + 80)
    (h₃ : e + k ≤ L.st + 80) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.B + BitVec.ofNat 64 e, k⟩ :=
  Offset.disjoint L.B h₁ (by have := h.nB; omega) (by have := h.nB; omega)

theorem stk_sub (_h : L.Ok) {d n : Nat} (h₂ : d + n ≤ L.st + 80) :
    Region.Sub ⟨L.B + BitVec.ofNat 64 d, n⟩ L.STK := Offset.sub_base L.B h₂

theorem scr_sub (_h : L.Ok) {o l : Nat} (h₂ : o + l ≤ 65536) : Region.Sub ⟨at' L.S o, l⟩ L.SCR :=
  Offset.sub_base L.S h₂

/-- The frame and the calls' stack, apart. -/
theorem fr_cs (h : L.Ok) {d n : Nat} (hd : d + n ≤ 72) :
    Region.Disjoint ⟨L.SP + BitVec.ofNat 64 d, n⟩ L.CS := by
  have e : L.SP + BitVec.ofNat 64 d = L.B + BitVec.ofNat 64 (L.st + 8 + d) := by
    rw [VL.SP, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  rw [e]
  have := h.stk (d := L.st + 8 + d) (n := n) (e := 0) (k := L.st + 8) (by omega) (by omega) (by omega)
  simpa only [BitVec.add_zero] using this

theorem fr_stk (h : L.Ok) {d n : Nat} (hd : d + n ≤ 72) :
    Region.Sub ⟨L.SP + BitVec.ofNat 64 d, n⟩ L.STK := by
  have e : L.SP + BitVec.ofNat 64 d = L.B + BitVec.ofNat 64 (L.st + 8 + d) := by
    rw [VL.SP, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  rw [e]; exact h.stk_sub (by omega)

theorem fr_scr (h : L.Ok) {d n : Nat} (hd : d + n ≤ 72) :
    Region.Disjoint ⟨L.SP + BitVec.ofNat 64 d, n⟩ L.SCR :=
  h.kScr.sub_left (h.fr_stk hd)

theorem cs_scr (h : L.Ok) : L.CS.Disjoint L.SCR := h.kScr.sub_left (Region.sub_prefix (by omega))

theorem prot_scr (h : L.Ok) : ∀ q ∈ L.prot, Region.Sub q L.SCR := by
  intro q hq
  have := h.n32
  have e1 : Layout.oPkSeed = 3232 := rfl
  have e2 : Layout.oPkRoot = 3264 := rfl
  have e3 : oKgSave = 34080 := rfl
  have e4 : ∀ k, Layout.laneA k = 3296 + 128 * k := fun _ => rfl
  have e5 : ∀ k, Layout.laneB k = 3808 + 2208 * k := fun _ => rfl
  simp only [VL.prot, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_flatMap,
    List.mem_range] at hq
  rcases hq with ((rfl | rfl | rfl | rfl) | ⟨k, hk, rfl | rfl⟩)
  · exact h.scr_sub (by omega)
  · exact h.scr_sub (by rw [e1]; omega)
  · exact h.scr_sub (by rw [e2]; omega)
  · exact h.scr_sub (by rw [e3]; omega)
  · exact h.scr_sub (by rw [e4]; omega)
  · exact h.scr_sub (by rw [e5]; omega)

end VL.Ok

theorem free_cs {L : VL} (hL : L.Ok) {r : Region} (h : Free L r) :
    (∀ d n, d + n ≤ 72 → r.Disjoint ⟨L.SP + BitVec.ofNat 64 d, n⟩) ∧ ∀ q ∈ L.prot, r.Disjoint q := by
  rcases h with ⟨hs, hq⟩ | hs
  · exact ⟨fun d n hd => (hL.fr_scr hd).symm.sub_left hs, hq⟩
  · exact ⟨fun d n hd => (hL.fr_cs hd).symm.sub_left hs,
      fun q hq => (hL.cs_scr.sub_left hs).sub_right (hL.prot_scr q hq)⟩

theorem free_stk {L : VL} (_hL : L.Ok) {r : Region} (h : Free L r) : ∃ r' ∈ [L.SCR, L.STK], Region.Sub r r' := by
  rcases h with ⟨hs, _⟩ | hs
  · exact ⟨_, List.mem_cons_self .., hs⟩
  · exact ⟨_, by simp, fun a ha => Region.sub_prefix (base := L.B) (by omega : L.st + 8 ≤ L.st + 80) a (hs a ha)⟩

namespace Ctx

variable {L : VL} {g : Reg → BitVec 64} {m₀ : Mem} {t t' : State}

/-- A state whose memory differs from that of a `Ctx` state only in free parts. -/
theorem of_frame (hL : L.Ok) (hc : Ctx L g m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hsp : t'.gpr .rsp = t.gpr .rsp) (hbx : t'.gpr .rbx = t.gpr .rbx)
    (hcs : ∀ r ∈ calleeSaved, r ≠ .rsp → r ≠ .rbx → t'.gpr r = t.gpr r)
    {rs : List Region}
    (hf : Frame rs t.mem t'.mem) (hrs : ∀ r ∈ rs, Free L r) : Ctx L g m₀ t' := by
  have hn := hL.n32
  have keepF : ∀ d, d + 8 ≤ 72 →
      t'.mem.readW (L.SP + BitVec.ofNat 64 d) 64 = t.mem.readW (L.SP + BitVec.ofNat 64 d) 64 :=
    fun d hd => Thash4Avx.readW_frame hf fun r hr => ((free_cs hL (hrs r hr)).1 d 8 hd).symm
  have pq : ∀ q ∈ L.prot, ∀ r ∈ rs, q.Disjoint r := fun q hq r hr => ((free_cs hL (hrs r hr)).2 q hq).symm
  have mem_prot : ∀ {q : Region}, q ∈ L.prot → ∀ r ∈ rs, q.Disjoint r := fun hq => pq _ hq
  have bq : ∀ {o l : Nat}, (⟨at' L.S o, l⟩ : Region) ∈ L.prot → l ≤ 32 →
      bytesAt t'.mem (at' L.S o) l = bytesAt t.mem (at' L.S o) l := fun {o l} hq hl =>
    bytesAt_frame hf (mem_prot hq) (by omega)
  refine ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.rsp, hbx.trans hc.rbx,
    fun r hr h1 h2 => (hcs r hr h1 h2).trans (hc.cs r hr h1 h2), fun i hi => ?_,
    (keepF 8 (by omega)).trans hc.pScr, (keepF 16 (by omega)).trans hc.pSig, (keepF 24 (by omega)).trans hc.pSigL,
    (keepF 32 (by omega)).trans hc.pCtxLen, (keepF 40 (by omega)).trans hc.pCtx, (keepF 48 (by omega)).trans hc.pLen,
    (keepF 56 (by omega)).trans hc.pMsg, (keepF 64 (by omega)).trans hc.pKey, ?_,
    hc.frame.trans (Frame.sub hf fun r hr => free_stk hL (hrs r hr)), fun r hr k hk => ?_, ?_, ?_,
    fun k hk => ?_, fun k hk => ?_⟩
  · rw [Thash4Avx.readW_frame hf fun r hr => (mem_prot (q := ⟨at' L.S oKgSave, 48⟩) (by simp [VL.prot]) r hr).sub_left
      (by rw [← Levels.at_add]; exact Offset.sub_base _ (by omega))]
    exact hc.saved i hi
  · have : bytesAt t'.mem L.SP 2 = bytesAt t.mem L.SP 2 :=
      bytesAt_frame hf (fun r hr => by
        have := ((free_cs hL (hrs r hr)).1 0 2 (by omega)).symm
        simpa only [BitVec.add_zero] using this) (by omega)
    rw [this]; exact hc.hdr
  · rw [Thash4Avx.readW_frame hf fun r' hr' => (mem_prot (q := ⟨at' L.S 1600, 768⟩) (by simp [VL.prot]) r' hr').sub_left
      (by rw [show L.S + BitVec.ofNat 64 (1600 + 32 * r + 8 * k) = at' L.S 1600 + BitVec.ofNat 64 (32 * r + 8 * k) by
            rw [Levels.at_add, Nat.add_assoc]]
          exact Offset.sub_base _ (by omega))]
    exact hc.rc r hr k hk
  · rw [bq (by simp [VL.prot]) hn]; exact hc.kSeed
  · rw [bq (by simp [VL.prot]) hn]; exact hc.kRoot
  · rw [bq (by simp only [VL.prot, List.mem_append, List.mem_flatMap, List.mem_range]; exact .inr ⟨k, hk, by simp⟩) hn]
    exact hc.seedA k hk
  · rw [bq (by simp only [VL.prot, List.mem_append, List.mem_flatMap, List.mem_range]; exact .inr ⟨k, hk, by simp⟩) hn]
    exact hc.seedB k hk

/-- Code that changes only caller-saved registers and flags. -/
theorem regs (hc : Ctx L g m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hm : t'.mem = t.mem)
    (hg : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) : Ctx L g m₀ t' where
  rd := hrd.trans hc.rd
  wr := hwr.trans hc.wr
  rsp := (hg .rsp (by decide)).trans hc.rsp
  rbx := (hg .rbx (by decide)).trans hc.rbx
  cs z hz h1 h2 := (hg z hz).trans (hc.cs z hz h1 h2)
  saved := by rw [hm]; exact hc.saved
  pScr := by rw [hm]; exact hc.pScr
  pSig := by rw [hm]; exact hc.pSig
  pSigL := by rw [hm]; exact hc.pSigL
  pCtxLen := by rw [hm]; exact hc.pCtxLen
  pCtx := by rw [hm]; exact hc.pCtx
  pLen := by rw [hm]; exact hc.pLen
  pMsg := by rw [hm]; exact hc.pMsg
  pKey := by rw [hm]; exact hc.pKey
  hdr := by rw [hm]; exact hc.hdr
  frame := by rw [hm]; exact hc.frame
  rc := by rw [hm]; exact hc.rc
  kSeed := by rw [hm]; exact hc.kSeed
  kRoot := by rw [hm]; exact hc.kRoot
  seedA := by rw [hm]; exact hc.seedA
  seedB := by rw [hm]; exact hc.seedB

/-- A slot of the frame is readable. -/
theorem inFr (hc : Ctx L g m₀ t) {d : Nat} (h₂ : d + 8 ≤ 72) :
    InRegions (t.rd ++ t.wr) (L.SP + BitVec.ofNat 64 d) 8 :=
  ⟨L.FR, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ h₂ (by omega)⟩

/-- `scratch` is writable. -/
theorem inScr (hc : Ctx L g m₀ t) : (⟨L.S, 2 ^ 16⟩ : Region) ∈ t.wr := by
  rw [hc.wr]; simp

/-- Bytes apart from `scratch` and the stack are as on entry. -/
theorem bytesAt_eq (hc : Ctx L g m₀ t) {a : Addr} {n : Nat} (hs : L.SCR.Disjoint ⟨a, n⟩)
    (hk : L.STK.Disjoint ⟨a, n⟩) (hn : n ≤ 2 ^ 64) : bytesAt t.mem a n = bytesAt m₀ a n :=
  bytesAt_frame hc.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [hs.symm, hk.symm]) hn

end Ctx

end VG.Proof.SlhDsa.X86_64.VerifyTop
