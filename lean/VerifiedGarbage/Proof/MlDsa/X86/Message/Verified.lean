import VerifiedGarbage.Impl.MlDsa.X86.Message
import VerifiedGarbage.Proof.MlKem.X86.Sample
import VerifiedGarbage.Proof.MlKem.X86.AddSub
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlDsa.Message.Common
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.MlKem.KPke1024
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.MlDsa.X86.Sign.Verified
import VerifiedGarbage.Proof.MlDsa.X86.Verify.Inst

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Message.Layout`. -/
section

/-!
# ML-DSA on x86 (32-bit), `sign_message` and `verify_message`: where everything is

Untrusted: everything here is checked by Lean. The stack pointer on entry,
the function's arguments, the `N` bytes of stack below it its contract gives
(the leaf's frame, then `STK`, which the calls use), `scratch` (`SC`) and the
1 KiB `X` in it after the working space of the function on `μ` (`Lay`): the
Keccak state, the sponge functions' working space and `μ` in its first 904
bytes (`W`), then the two bytes of the formatted message. `Ctx` is what
holds in the body of the leaf, from the entry's stores to the end: `esp`,
`esi` pointing at `X`, the permissions, the arguments, the two bytes, and
that memory changed only in `scratch` and `STK` since the frame's push.
-/

namespace VG.Proof.MlDsa.X86.Message

open VG VG.X86 VG.Impl.MlDsa.X86.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.X86 (E0 P0 frameR retR)
open VG.Spec.Sha3 (bytesAt)

theorem covers_of_within {rs rs' : List Region} (h : ∀ r ∈ rs, ∃ R ∈ rs', Within r R) : Covers rs rs' :=
  Covers.of_sub fun r hr => by
    obtain ⟨R, hR, o, hb, hl⟩ := h r hr
    exact ⟨R, hR, o, hb, hl⟩

/-! ## The layout -/

/-- The stack pointer on entry, the stack the contract gives, the number of
arguments, the arguments, the size of `scratch`, the offset `E` of the 1 KiB
`X` in it, and the permissions on entry. -/
structure Lay where
  SP : BitVec 32
  N : Nat
  nA : Nat
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
  argv : List (BitVec 32)
  rd : List Region
  wr : List Region

namespace Lay

variable (L : VG.Proof.MlDsa.X86.Message.Lay)

/-- `esp` in the leaf's body. -/
abbrev E1 : BitVec 32 := L.SP - BitVec.ofNat 32 16
/-- The stack the calls use, below the leaf's frame. -/
abbrev STK : Region := below L.E1 (L.N - 16)
/-- The arguments. -/
abbrev ARGS : Region := ⟨(L.SP + BitVec.ofNat 32 4).setWidth 64, 4 * L.nA⟩
/-- `scratch`. -/
abbrev SC : Region := ⟨L.scr.setWidth 64, L.scrLen⟩
/-- The 1 KiB, as a register holds it and as an address. -/
abbrev X32 : BitVec 32 := L.scr + BitVec.ofNat 32 L.E
abbrev X : Addr := L.X32.setWidth 64
abbrev W : Region := ⟨L.X, 904⟩
abbrev ST : Addr := L.X
abbrev KS : Addr := L.X + BitVec.ofNat 64 200
abbrev MU : Addr := L.X + BitVec.ofNat 64 840
abbrev KEY : Region := ⟨L.key.setWidth 64, L.keyLen⟩
abbrev MSG : Region := ⟨L.msg.setWidth 64, L.len.toNat⟩
abbrev CTX : Region := ⟨L.ctx.setWidth 64, L.ctxLen.toNat⟩

/-- What the contract says of where everything is. -/
structure Ok : Prop where
  ctxLt : L.ctxLen.toNat < 256
  hE : L.E + 1024 ≤ L.scrLen
  hKey : 128 ≤ L.keyLen ∧ L.keyLen < 2 ^ 16
  hN : 56 ≤ L.N
  nSP : L.N ≤ L.SP.toNat
  fArgs : L.SP.toNat + 4 + 4 * L.nA ≤ 2 ^ 32
  nScr : L.scr.toNat + L.scrLen ≤ 2 ^ 32
  inSC : L.SC ∈ L.wr
  inKey : L.KEY ∈ L.rd
  inMsg : L.MSG ∈ L.rd
  inCtx : L.CTX ∈ L.rd
  xKey : L.SC.Disjoint L.KEY
  xMsg : L.SC.Disjoint L.MSG
  xCtx : L.SC.Disjoint L.CTX
  kAll : ∀ r ∈ [L.SC, L.KEY, L.MSG, L.CTX, L.ARGS], (below L.SP L.N).Disjoint r
  rAll : ∀ r ∈ [L.SC, L.ARGS], (⟨L.SP.setWidth 64, 4⟩ : Region).Disjoint r
  aSC : L.ARGS.Disjoint L.SC
  inArgs : L.ARGS ∈ L.wr
  argvLen : L.argv.length = L.nA
  nA8 : L.nA ≤ 8
  nA5 : 5 ≤ L.nA
  a0 : L.argv.getD 0 0 = L.key
  a1 : L.argv.getD 1 0 = L.msg
  a2 : L.argv.getD 2 0 = L.len
  a3 : L.argv.getD 3 0 = L.ctx
  a4 : L.argv.getD 4 0 = L.ctxLen
  nKey : L.key.toNat + L.keyLen ≤ 2 ^ 32
  nMsg : L.msg.toNat + L.len.toNat ≤ 2 ^ 32
  nCtx : L.ctx.toNat + L.ctxLen.toNat ≤ 2 ^ 32

end Lay

namespace Lay.Ok

variable {L : VG.Proof.MlDsa.X86.Message.Lay}

theorem x32_lt (h : L.Ok) : L.X32.toNat + 1024 ≤ 2 ^ 32 := by
  have := h.nScr; have := h.hE
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := L.E) (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-- `X` in `scratch`. -/
theorem x_eq (h : L.Ok) : L.X = L.scr.setWidth 64 + BitVec.ofNat 64 L.E :=
  Proof.MlKem.X86.ea_off (by have := h.nScr; have := h.hE; omega)

/-- An address in the 1 KiB, as an instruction computes it from `esi`. -/
theorem xo (h : L.Ok) {o : Nat} (ho : o < 1024) : VG.X86.addr L.X32 o = L.X + BitVec.ofNat 64 o :=
  Proof.MlKem.X86.ea_off (by have := h.x32_lt; omega)

theorem x32_toNat (h : L.Ok) {o : Nat} (ho : o < 1024) : (L.X32 + BitVec.ofNat 32 o).toNat = L.X32.toNat + o := by
  have := h.x32_lt
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem xs_sc (h : L.Ok) : Within ⟨L.X, 1024⟩ L.SC := ⟨L.E, h.x_eq, h.hE⟩

theorem sub_sc (h : L.Ok) {e k : Nat} (h₂ : e + k ≤ 1024) : Region.Sub ⟨L.X + BitVec.ofNat 64 e, k⟩ L.SC :=
  (Within.trans (within_off L.X h₂) h.xs_sc).sub

/-- The calls' stack lies in the contract's. -/
theorem stk_sub (h : L.Ok) : Region.Sub L.STK (below L.SP L.N) := by
  have := h.nSP; have := h.hN
  rw [Lay.STK, Lay.E1]
  exact below_inner (by omega) (by omega)

/-- The leaf's frame lies in the contract's stack. -/
theorem fr_sub (h : L.Ok) : Region.Sub (below L.SP 16) (below L.SP L.N) := by
  have := h.nSP; have := h.hN
  exact below_sub (by omega) (by omega)

theorem kSC (h : L.Ok) : L.STK.Disjoint L.SC := (h.kAll _ (by simp)).sub_left h.stk_sub
theorem kKey (h : L.Ok) : L.STK.Disjoint L.KEY := (h.kAll _ (by simp)).sub_left h.stk_sub
theorem kMsg (h : L.Ok) : L.STK.Disjoint L.MSG := (h.kAll _ (by simp)).sub_left h.stk_sub
theorem kCtx (h : L.Ok) : L.STK.Disjoint L.CTX := (h.kAll _ (by simp)).sub_left h.stk_sub
theorem kArgs (h : L.Ok) : L.STK.Disjoint L.ARGS := (h.kAll _ (by simp)).sub_left h.stk_sub

theorem stk_x (h : L.Ok) {e k : Nat} (h₂ : e + k ≤ 1024) :
    Region.Disjoint L.STK ⟨L.X + BitVec.ofNat 64 e, k⟩ :=
  h.kSC.sub_right (h.sub_sc h₂)

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

/-- What lies within the first 904 bytes of `X`, or in `STK`, is apart from the two bytes. -/
theorem hdr_disj (h : L.Ok) {r : Region} (hr : Within r L.W ∨ Region.Sub r L.STK) :
    Region.Disjoint ⟨L.X + BitVec.ofNat 64 944, 2⟩ r := by
  rcases hr with hr | hr
  · obtain ⟨o, hb, hl⟩ := hr
    obtain ⟨b, k⟩ := r
    simp only at hb hl
    subst hb
    exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
  · exact (h.kSC.symm.sub_left (h.sub_sc (by omega))).sub_right hr

/-- Argument `i`, as an instruction in the body addresses it. -/
theorem argAt_eq (L : VG.Proof.MlDsa.X86.Message.Lay) (i : Nat) :
    VG.X86.addr L.E1 (20 + 4 * i) = (L.SP + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 := by
  simp only [VG.X86.addr, Lay.E1]
  congr 1
  rw [show (20 + 4 * i : Nat) = 16 + (4 + 4 * i) by omega, ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc,
    BitVec.sub_add_cancel]

/-- Argument `i` lies in the arguments. -/
theorem argIn (h : L.Ok) {i : Nat} (hi : i < L.nA) :
    L.ARGS.Contains ((L.SP + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64) 4 := by
  have := h.fArgs
  rw [Lay.ARGS, Proof.MlKem.X86.ea_off (x := L.SP) (d := 4) (by omega),
    Proof.MlKem.X86.ea_off (x := L.SP) (d := 4 + 4 * i) (by omega)]
  exact Offset.contains _ (by omega) (by omega) (by omega)

end Lay.Ok

/-! ## In the leaf's body -/

/-- The state in the leaf's body, from the entry's stores to the end: `m₁`
is the memory after the frame's push. -/
structure Ctx (L : VG.Proof.MlDsa.X86.Message.Lay) (m₁ : Mem) (t : State) : Prop where
  rd : t.rd = L.rd
  wr : t.wr = below L.SP 16 :: L.wr
  esp : t.gpr .esp = L.E1
  esi : t.gpr .esi = L.X32
  hdr : bytesAt t.mem (L.X + BitVec.ofNat 64 944) 2 = [0, BitVec.ofNat 8 L.ctxLen.toNat]
  args : ∀ i < L.nA, t.mem.readW ((L.SP + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64) 32 = L.argv.getD i 0
  frame : Frame [L.SC, L.STK] m₁ t.mem

namespace Ctx

variable {L : VG.Proof.MlDsa.X86.Message.Lay} {m₁ : Mem} {t t' : State}

/-- Code that writes only registers but `esp` and `esi`. -/
theorem regs (hc : VG.Proof.MlDsa.X86.Message.Ctx L m₁ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hm : t'.mem = t.mem)
    (hsp : t'.gpr .esp = t.gpr .esp) (hsi : t'.gpr .esi = t.gpr .esi) : VG.Proof.MlDsa.X86.Message.Ctx L m₁ t' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.esp, hsi.trans hc.esi, by rw [hm]; exact hc.hdr,
    fun i hi => by rw [hm]; exact hc.args i hi, by rw [hm]; exact hc.frame⟩

/-- Code that writes memory only within the first 904 bytes of `X` and in `STK`. -/
theorem keep (hc : VG.Proof.MlDsa.X86.Message.Ctx L m₁ t) (hL : L.Ok) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hsp : t'.gpr .esp = t.gpr .esp) (hsi : t'.gpr .esi = t.gpr .esi) {rs : List Region}
    (hf : Frame rs t.mem t'.mem) (hrs : ∀ r ∈ rs, Within r L.W ∨ Region.Sub r L.STK) : VG.Proof.MlDsa.X86.Message.Ctx L m₁ t' := by
  have khdr : bytesAt t'.mem (L.X + BitVec.ofNat 64 944) 2 = bytesAt t.mem (L.X + BitVec.ofNat 64 944) 2 :=
    Proof.MlKem.bytesAt_congr fun i hi =>
      hf.bytes (R := ⟨_, 2⟩) (fun r hr => hL.hdr_disj (hrs r hr)) (by show 2 ≤ 2 ^ 64; decide) hi
  refine ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.esp, hsi.trans hc.esi, khdr.trans hc.hdr,
    fun i hi => ?_, hc.frame.trans (Frame.sub hf fun r hr => ?_)⟩
  · rw [hf.readW (hL.argIn hi) (fun r hr => ?_) (by decide)]
    · exact hc.args i hi
    · rcases hrs r hr with h | h
      · exact hL.aSC.sub_right ((h.trans ((within_base L.X (by decide : 904 ≤ 1024)).trans hL.xs_sc)).sub)
      · exact hL.kArgs.symm.sub_right h
  rcases hrs r hr with h | h
  · exact ⟨L.SC, by simp, (h.trans ((within_base L.X (by decide : 904 ≤ 1024)).trans hL.xs_sc)).sub⟩
  · exact ⟨L.STK, by simp, h⟩

/-- Bytes apart from `scratch` and `STK`, as after the push. -/
theorem bytesAt_eq (hc : VG.Proof.MlDsa.X86.Message.Ctx L m₁ t) {p : Addr} {n : Nat} (hx : L.SC.Disjoint ⟨p, n⟩)
    (hk : L.STK.Disjoint ⟨p, n⟩) (hn : n ≤ 2 ^ 64) : bytesAt t.mem p n = bytesAt m₁ p n :=
  Proof.MlKem.bytesAt_congr fun _ hi => Frame.bytes (R := ⟨p, n⟩) hc.frame (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hx.symm
    · exact hk.symm) hn hi

/-- Bytes of `X` are readable. -/
theorem inX (hc : VG.Proof.MlDsa.X86.Message.Ctx L m₁ t) (hL : L.Ok) {e k : Nat} (h₂ : e + k ≤ 1024) :
    InRegions (t.rd ++ t.wr) (L.X + BitVec.ofNat 64 e) k := by
  obtain ⟨R, hR, hc'⟩ := hL.inW h₂
  exact ⟨R, by rw [hc.rd, hc.wr]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hR), hc'⟩

end Ctx

end VG.Proof.MlDsa.X86.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Message.Args`. -/
section

/-!
# ML-DSA on x86 (32-bit), `sign_message` and `verify_message`: the moves of a call's arguments

Untrusted: everything here is checked by Lean. Each argument's value
(`Arg.val`): an argument of the function (at `[esp + 20 + 4i]`), plus an
offset, an offset from `esi`, an immediate, or `eax`. The moves of a list
of arguments into distinct registers but `esp` and `esi`, with `eax` read
only before it is written (`argsOk`), leave each its value and change
nothing else (`setArgs_ok`).
-/

namespace VG.Proof.MlDsa.X86.Message

open VG VG.X86 VG.X86.Wp VG.Impl.MlDsa.X86.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.X86 (Only)

/-- The value of an argument in the state `s`. -/
def _root_.VG.Impl.MlDsa.X86.Message.Arg.val (s : State) : VG.Impl.MlDsa.X86.Message.Arg → BitVec 32
  | .arg i => s.mem.readW (VG.X86.addr (s.gpr .esp) (20 + 4 * i)) 32
  | .argOff i o => s.mem.readW (VG.X86.addr (s.gpr .esp) (20 + 4 * i)) 32 + BitVec.ofNat 32 o
  | .off o => s.gpr .esi + BitVec.ofNat 32 o
  | .imm v => BitVec.ofNat 32 v
  | .ret => s.gpr .eax

/-- An argument of the function among its `n`. -/
def _root_.VG.Impl.MlDsa.X86.Message.Arg.ok (n : Nat) : VG.Impl.MlDsa.X86.Message.Arg → Bool
  | .arg i => decide (i < n)
  | .argOff i _ => decide (i < n)
  | _ => true

def _root_.VG.Impl.MlDsa.X86.Message.Arg.isRet : VG.Impl.MlDsa.X86.Message.Arg → Bool
  | .ret => true
  | _ => false

/-- The arguments of the function are readable. -/
abbrev AOk (n : Nat) (s : State) : Prop := ∀ i < n, InRegions (s.rd ++ s.wr) (VG.X86.addr (s.gpr .esp) (20 + 4 * i)) 4

theorem only_upd {s s' : State} {d : Reg} {v : BitVec 32} (u : Upd s s' d v) : Only [d] s s' :=
  ⟨fun r hr => u.other r (by simpa using hr), u.mem, u.rd, u.wr⟩

theorem Arg.set_ok {n : Nat} (d : Reg) (a : VG.Impl.MlDsa.X86.Message.Arg) (ha : a.ok n = true) (s : State) (hx : VG.Proof.MlDsa.X86.Message.AOk n s) :
    WP isa (.block (a.set d)) s fun s1 => s1.gpr d = a.val s ∧ Only [d] s s1 := by
  cases a with
  | arg i =>
    simp only [Arg.ok, decide_eq_true_eq] at ha
    exact wp_ldm (b := .esp) rfl (hx i ha) fun s1 u => WP.block_nil ⟨u.gpr, VG.Proof.MlDsa.X86.Message.only_upd u⟩
  | argOff i o =>
    simp only [Arg.ok, decide_eq_true_eq] at ha
    refine wp_ldm (b := .esp) rfl (hx i ha) fun s1 u1 => VG.X86.Wp.wp_addi fun s2 u2 => WP.block_nil ⟨?_, ?_⟩
    · rw [u2.gpr, u1.gpr]; rfl
    · exact ((VG.Proof.MlDsa.X86.Message.only_upd u1).trans (VG.Proof.MlDsa.X86.Message.only_upd u2)).mono fun r hr => by simpa using hr
  | off o =>
    refine wp_mov fun s1 u1 => VG.X86.Wp.wp_addi fun s2 u2 => WP.block_nil ⟨?_, ?_⟩
    · rw [u2.gpr, u1.gpr]; rfl
    · exact ((VG.Proof.MlDsa.X86.Message.only_upd u1).trans (VG.Proof.MlDsa.X86.Message.only_upd u2)).mono fun r hr => by simpa using hr
  | imm v => exact VG.X86.Wp.wp_movi fun s1 u => WP.block_nil ⟨u.gpr, VG.Proof.MlDsa.X86.Message.only_upd u⟩
  | ret => exact wp_mov fun s1 u => WP.block_nil ⟨u.gpr, VG.Proof.MlDsa.X86.Message.only_upd u⟩

/-- Distinct registers but `esp` and `esi`, each argument fit, and `eax`
read only before it is written. -/
def argsOk (n : Nat) : List (Reg × VG.Impl.MlDsa.X86.Message.Arg) → Bool
  | [] => true
  | (d, a) :: as => a.ok n && d != .esp && d != .esi &&
      as.all (fun da => da.1 != d && (d != .eax || !da.2.isRet)) && VG.Proof.MlDsa.X86.Message.argsOk n as

/-- The value of an argument is the same after a move into another register
(not `esp` or `esi`, and not `eax` if the argument is `eax`). -/
theorem Arg.val_only {d : Reg} (hd : d ≠ .esp) (hs : d ≠ .esi) {s s1 : State} (o : Only [d] s s1) (a : VG.Impl.MlDsa.X86.Message.Arg)
    (ha : d ≠ .eax ∨ a.isRet = false) : a.val s1 = a.val s := by
  have hsp : s1.gpr .esp = s.gpr .esp := o.gpr _ (by simp only [List.mem_singleton]; exact fun h => hd h.symm)
  have hsi : s1.gpr .esi = s.gpr .esi := o.gpr _ (by simp only [List.mem_singleton]; exact fun h => hs h.symm)
  cases a with
  | ret =>
    simp only [Arg.isRet, Bool.true_eq_false, or_false] at ha
    simp only [Arg.val]
    exact o.gpr _ (by simp only [List.mem_singleton]; exact fun h => ha h.symm)
  | _ => simp only [Arg.val, hsp, hsi, o.mem]

theorem AOk.only {n : Nat} {d : Reg} (hd : d ≠ .esp) {s s1 : State} (o : Only [d] s s1) (h : VG.Proof.MlDsa.X86.Message.AOk n s) :
    VG.Proof.MlDsa.X86.Message.AOk n s1 := by
  intro i hi
  rw [o.rd, o.wr, o.gpr _ (by simp only [List.mem_singleton]; exact fun h => hd h.symm)]
  exact h i hi

/-- The moves of the arguments `as`. -/
theorem setArgs_ok {n : Nat} : ∀ (as : List (Reg × VG.Impl.MlDsa.X86.Message.Arg)), VG.Proof.MlDsa.X86.Message.argsOk n as = true → ∀ s : State, VG.Proof.MlDsa.X86.Message.AOk n s →
    WP isa (.block (VG.Impl.MlDsa.X86.Message.setArgs as)) s fun s1 => (∀ da ∈ as, s1.gpr da.1 = da.2.val s) ∧ Only (as.map (·.1)) s s1
  | [], _, s, _ => WP.block_nil ⟨fun _ h => by simp at h, Only.refl _ _⟩
  | (d, a) :: as, h, s, hx => by
    simp only [VG.Proof.MlDsa.X86.Message.argsOk, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true, Bool.or_eq_true,
      Bool.not_eq_true'] at h
    obtain ⟨⟨⟨⟨ha, hd⟩, hs⟩, hall⟩, hrest⟩ := h
    simp only [VG.Impl.MlDsa.X86.Message.setArgs, List.flatMap_cons]
    rw [WP.block_append_iff]
    refine WP.mono (Arg.set_ok d a ha s hx) fun s1 ⟨h1, o1⟩ => ?_
    refine WP.mono (VG.Proof.MlDsa.X86.Message.setArgs_ok as hrest s1 (hx.only hd o1)) fun s2 ⟨h2, o2⟩ => ⟨fun da hda => ?_, ?_⟩
    · rcases List.mem_cons.mp hda with rfl | hda
      · rw [o2.gpr _ (fun hm => by
          obtain ⟨x, hx', hx''⟩ := List.mem_map.mp hm
          exact (hall x hx').1 hx''), h1]
      · rw [h2 da hda, Arg.val_only hd hs o1 da.2 ((hall da hda).2.elim .inl fun h' => .inr h')]
    · exact (o1.trans o2).mono (by simp)

/-! ## In `Ctx` -/

section
variable {L : VG.Proof.MlDsa.X86.Message.Lay} {m₁ : Mem} {t : State}

theorem Ctx.aOk (hc : VG.Proof.MlDsa.X86.Message.Ctx L m₁ t) (hL : L.Ok) : VG.Proof.MlDsa.X86.Message.AOk L.nA t := fun i hi => by
  rw [hc.esp, Lay.Ok.argAt_eq, hc.rd, hc.wr]
  exact ⟨L.ARGS, List.mem_append_right _ (List.mem_cons_of_mem _ hL.inArgs), hL.argIn hi⟩

theorem Ctx.off (hc : VG.Proof.MlDsa.X86.Message.Ctx L m₁ t) (o : Nat) : (Arg.off o).val t = L.X32 + BitVec.ofNat 32 o := by
  simp only [Arg.val, hc.esi]

/-- Argument `i` of the function. -/
theorem Ctx.argV (hc : VG.Proof.MlDsa.X86.Message.Ctx L m₁ t) {i : Nat} (hi : i < L.nA) : (Arg.arg i).val t = L.argv.getD i 0 := by
  simp only [Arg.val, hc.esp, Lay.Ok.argAt_eq]; exact hc.args i hi

theorem Ctx.argOffV (hc : VG.Proof.MlDsa.X86.Message.Ctx L m₁ t) {i : Nat} (hi : i < L.nA) (o : Nat) :
    (Arg.argOff i o).val t = L.argv.getD i 0 + BitVec.ofNat 32 o := by
  simp only [Arg.val, hc.esp, Lay.Ok.argAt_eq]; rw [hc.args i hi]

end

end VG.Proof.MlDsa.X86.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Message.Call`. -/
section

/-!
# ML-DSA on x86 (32-bit), `sign_message` and `verify_message`: calls, correct and constant time

Untrusted: everything here is checked by Lean. The body is proven piece by
piece (`Piece`, `Proof/MlKem/X86/Piece.lean`) from the entry state `s₀` of
each run, with the layout `lay s₀`. Two runs whose entry states are related
by the contract's public data have layouts with the same public data
(`PubL`): the stack pointer, the arguments and the 1 KiB. In the body
(`CtxO`), the moves of a call's arguments (`setArgs_piece`) are checked by
the taint analysis, their addresses depending only on `esp` and `esi`; and a
call with them (`argsRet_piece`, `argsWith_piece`) is constant time when
correctness determines its arguments from public data.
-/

namespace VG.Proof.MlDsa.X86.Message

open VG VG.X86 VG.Impl.MlDsa.X86.Message
open VG.Proof.MlKem.X86 (Only Piece P0)

/-- Two layouts with the same public data. -/
structure PubL (L L' : VG.Proof.MlDsa.X86.Message.Lay) : Prop where
  sp : L.SP = L'.SP
  argv : L.argv = L'.argv
  x : L.X32 = L'.X32
  nA : L.nA = L'.nA
  key : L.key = L'.key
  msg : L.msg = L'.msg
  len : L.len = L'.len
  ctx : L.ctx = L'.ctx
  ctxLen : L.ctxLen = L'.ctxLen

/-- In the body of the leaf, from the entry state `s₀`, with the layout `lay s₀`. -/
structure CtxO (lay : State → VG.Proof.MlDsa.X86.Message.Lay) (s₀ s : State) : Prop where
  ok : (lay s₀).Ok
  ctx : VG.Proof.MlDsa.X86.Message.Ctx (lay s₀) (P0 s₀).mem s

/-- The moves of the arguments `as` from `s` to `s₁`. -/
def SetPost (as : List (Reg × VG.Impl.MlDsa.X86.Message.Arg)) (s s₁ : State) : Prop :=
  (∀ da ∈ as, s₁.gpr da.1 = da.2.val s) ∧ Only (as.map (·.1)) s s₁

theorem argsOk_regs {n : Nat} : ∀ {as : List (Reg × VG.Impl.MlDsa.X86.Message.Arg)}, VG.Proof.MlDsa.X86.Message.argsOk n as = true →
    ∀ r ∈ as.map (·.1), r ≠ .esp ∧ r ≠ .esi
  | [], _, _, h => by simp at h
  | (d, a) :: as, h, r, hr => by
    simp only [VG.Proof.MlDsa.X86.Message.argsOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    simp only [List.map_cons, List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact ⟨h.1.1.1.2, h.1.1.2⟩
    · exact VG.Proof.MlDsa.X86.Message.argsOk_regs h.2 r hr

theorem SetPost.esp {n : Nat} {as : List (Reg × VG.Impl.MlDsa.X86.Message.Arg)} (ho : VG.Proof.MlDsa.X86.Message.argsOk n as = true) {s s₁ : State}
    (h : VG.Proof.MlDsa.X86.Message.SetPost as s s₁) : s₁.gpr .esp = s.gpr .esp :=
  h.2.gpr _ fun hm => (VG.Proof.MlDsa.X86.Message.argsOk_regs ho _ hm).1 rfl

theorem SetPost.esi {n : Nat} {as : List (Reg × VG.Impl.MlDsa.X86.Message.Arg)} (ho : VG.Proof.MlDsa.X86.Message.argsOk n as = true) {s s₁ : State}
    (h : VG.Proof.MlDsa.X86.Message.SetPost as s s₁) : s₁.gpr .esi = s.gpr .esi :=
  h.2.gpr _ fun hm => (VG.Proof.MlDsa.X86.Message.argsOk_regs ho _ hm).2 rfl

/-- The value of an argument but `eax` is public. -/
theorem Arg.val_pub {L L' : VG.Proof.MlDsa.X86.Message.Lay} {m m' : Mem} {s s' : State} (hc : VG.Proof.MlDsa.X86.Message.Ctx L m s) (hc' : VG.Proof.MlDsa.X86.Message.Ctx L' m' s')
    (hp : VG.Proof.MlDsa.X86.Message.PubL L L') {a : VG.Impl.MlDsa.X86.Message.Arg} (ha : a.ok L.nA = true) (hr : a.isRet = false) : a.val s = a.val s' := by
  cases a with
  | arg i =>
    simp only [Arg.ok, decide_eq_true_eq] at ha
    rw [hc.argV ha, hc'.argV (hp.nA ▸ ha), hp.argv]
  | argOff i o =>
    simp only [Arg.ok, decide_eq_true_eq] at ha
    rw [hc.argOffV ha, hc'.argOffV (hp.nA ▸ ha), hp.argv]
  | off o => rw [hc.off, hc'.off, hp.x]
  | imm v => rfl
  | ret => simp [Arg.isRet] at hr

/-- Registers set by the moves of two runs agree, if the values do. -/
theorem SetPost.agree {as : List (Reg × VG.Impl.MlDsa.X86.Message.Arg)} {s s' s₁ s₁' : State} (h : VG.Proof.MlDsa.X86.Message.SetPost as s s₁)
    (h' : VG.Proof.MlDsa.X86.Message.SetPost as s' s₁') (hv : ∀ da ∈ as, da.2.val s = da.2.val s') {r : Reg} {a : VG.Impl.MlDsa.X86.Message.Arg}
    (hr : (r, a) ∈ as) : s₁.gpr r = s₁'.gpr r := by
  rw [h.1 _ hr, h'.1 _ hr]; exact hv _ hr

section
variable {Pre : State → Prop} {Pub : State → State → Prop} {lay : State → VG.Proof.MlDsa.X86.Message.Lay} {A B : State → State → Prop}

/-- The moves of a call's arguments. -/
theorem setArgs_piece (as : List (Reg × VG.Impl.MlDsa.X86.Message.Arg)) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (VG.Impl.MlDsa.X86.Message.setArgs as)) ht).isSome = true)
    (hpub : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → VG.Proof.MlDsa.X86.Message.PubL (lay s₀) (lay s₀'))
    (hA : ∀ s₀ s, Pre s₀ → A s₀ s → VG.Proof.MlDsa.X86.Message.CtxO lay s₀ s)
    (hok : ∀ s₀, Pre s₀ → VG.Proof.MlDsa.X86.Message.argsOk (lay s₀).nA as = true) :
    Piece Pre Pub A (fun s₀ s₁ => ∃ s, A s₀ s ∧ VG.Proof.MlDsa.X86.Message.SetPost as s s₁) (.block (VG.Impl.MlDsa.X86.Message.setArgs as)) :=
  Piece.taint [.esp, .esi] (fun s₀ s h₀ ha => by
      have h := hA s₀ s h₀ ha
      exact (VG.Proof.MlDsa.X86.Message.setArgs_ok as (hok s₀ h₀) s (h.ctx.aOk h.ok)).mono fun s₁ h₁ => ⟨s, ha, h₁⟩)
    (fun s₀ s₀' s s' h₀ h₀' hq ha ha' r hr => by
      have h := hA s₀ s h₀ ha
      have h' := hA s₀' s' h₀' ha'
      have hp := hpub s₀ s₀' h₀ h₀' hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.ctx.esp, h'.ctx.esp, Lay.E1, Lay.E1, hp.sp]
      · rw [h.ctx.esi, h'.ctx.esi, hp.x]) tt

/-- A call of verified code, returning a value in `eax`, with the arguments `as`. -/
theorem argsRet_piece {as : List (Reg × VG.Impl.MlDsa.X86.Message.Arg)} {rs : List Reg} {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (hsp : NoSp c) (hne : rs ≠ []) (hrs : Reg.esp ∉ rs)
    {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (VG.Impl.MlDsa.X86.Message.setArgs as)) ht).isSome = true)
    (hpub : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → VG.Proof.MlDsa.X86.Message.PubL (lay s₀) (lay s₀'))
    (hA : ∀ s₀ s, Pre s₀ → A s₀ s → VG.Proof.MlDsa.X86.Message.CtxO lay s₀ s)
    (hok : ∀ s₀, Pre s₀ → VG.Proof.MlDsa.X86.Message.argsOk (lay s₀).nA as = true)
    (rd wr : State → List Region)
    (hrw : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → rd s₀ = rd s₀' ∧ wr s₀ = wr s₀')
    (hd : ∀ s₀ s, Pre s₀ → A s₀ s → 4 * rs.length + stackUse c + 4 ≤ (lay s₀).E1.toNat)
    (hk : ∀ s₀ s s₁, Pre s₀ → A s₀ s → VG.Proof.MlDsa.X86.Message.SetPost as s s₁ → CallPre k rs (rd s₀) (wr s₀) s₁)
    (hkp : ∀ s₀ s₀' s s' s₁ s₁', Pre s₀ → Pre s₀' → Pub s₀ s₀' → A s₀ s → A s₀' s' →
      VG.Proof.MlDsa.X86.Message.SetPost as s s₁ → VG.Proof.MlDsa.X86.Message.SetPost as s' s₁' →
      k.pub ((pushed rs s₁).callEntry.withRegions (rd s₀) (wr s₀))
        ((pushed rs s₁').callEntry.withRegions (rd s₀) (wr s₀)))
    (hQ : ∀ s₀ s s₁ s', Pre s₀ → A s₀ s → VG.Proof.MlDsa.X86.Message.SetPost as s s₁ → s'.rd = s₁.rd → s'.wr = s₁.wr →
      (∀ r ∈ calleeSaved, s'.gpr r = s₁.gpr r) →
      Frame (wr s₀ ++ [below (s₁.gpr .esp) (4 * rs.length + stackUse c + 4)]) s₁.mem s'.mem →
      (∃ s₂ : State, s₂.mem = s'.mem ∧ s₂.gpr .eax = s'.gpr .eax ∧
        k.post ((pushed rs s₁).callEntry.withRegions (rd s₀) (wr s₀)) s₂) → B s₀ s') :
    Piece Pre Pub A B (.seq (.block (VG.Impl.MlDsa.X86.Message.setArgs as)) (Impl.MlKem.X86.callRet rs n c)) := by
  refine Piece.seq (VG.Proof.MlDsa.X86.Message.setArgs_piece as tt hpub hA hok) (Piece.callRet hv hct hsp hne hrs rd wr ?_ ?_ ?_ ?_)
  · rintro s₀ s₁ h₀ ⟨s, ha, hs⟩
    rw [hs.esp (hok s₀ h₀), (hA s₀ s h₀ ha).ctx.esp]
    exact hd s₀ s h₀ ha
  · rintro s₀ s₁ h₀ ⟨s, ha, hs⟩
    exact hk s₀ s s₁ h₀ ha hs
  · rintro s₀ s₀' s₁ s₁' h₀ h₀' hq ⟨s, ha, hs⟩ ⟨s', ha', hs'⟩
    obtain ⟨e₁, e₂⟩ := hrw s₀ s₀' h₀ h₀' hq
    refine ⟨e₁, e₂, ?_, hkp s₀ s₀' s s' s₁ s₁' h₀ h₀' hq ha ha' hs hs'⟩
    rw [hs.esp (hok s₀ h₀), hs'.esp (hok s₀' h₀'), (hA s₀ s h₀ ha).ctx.esp, (hA s₀' s' h₀' ha').ctx.esp,
      Lay.E1, Lay.E1, (hpub s₀ s₀' h₀ h₀' hq).sp]
  · rintro s₀ s₁ s' h₀ ⟨s, ha, hs⟩ e₁ e₂ e₃ fr post
    exact hQ s₀ s s₁ s' h₀ ha hs e₁ e₂ e₃ fr post

/-- A call of verified code, popping its frame into `eax`, with the arguments `as`. -/
theorem argsWith_piece {as : List (Reg × VG.Impl.MlDsa.X86.Message.Arg)} {rs : List Reg} {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (hsp : NoSp c) (hne : rs ≠ []) (hrs : Reg.esp ∉ rs)
    {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (VG.Impl.MlDsa.X86.Message.setArgs as)) ht).isSome = true)
    (hpub : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → VG.Proof.MlDsa.X86.Message.PubL (lay s₀) (lay s₀'))
    (hA : ∀ s₀ s, Pre s₀ → A s₀ s → VG.Proof.MlDsa.X86.Message.CtxO lay s₀ s)
    (hok : ∀ s₀, Pre s₀ → VG.Proof.MlDsa.X86.Message.argsOk (lay s₀).nA as = true)
    (rd wr : State → List Region)
    (hrw : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → rd s₀ = rd s₀' ∧ wr s₀ = wr s₀')
    (hd : ∀ s₀ s, Pre s₀ → A s₀ s → 4 * rs.length + stackUse c + 4 ≤ (lay s₀).E1.toNat)
    (hk : ∀ s₀ s s₁, Pre s₀ → A s₀ s → VG.Proof.MlDsa.X86.Message.SetPost as s s₁ → CallPre k rs (rd s₀) (wr s₀) s₁)
    (hkp : ∀ s₀ s₀' s s' s₁ s₁', Pre s₀ → Pre s₀' → Pub s₀ s₀' → A s₀ s → A s₀' s' →
      VG.Proof.MlDsa.X86.Message.SetPost as s s₁ → VG.Proof.MlDsa.X86.Message.SetPost as s' s₁' →
      k.pub ((pushed rs s₁).callEntry.withRegions (rd s₀) (wr s₀))
        ((pushed rs s₁').callEntry.withRegions (rd s₀) (wr s₀)))
    (hQ : ∀ s₀ s s₁ s', Pre s₀ → A s₀ s → VG.Proof.MlDsa.X86.Message.SetPost as s s₁ → s'.rd = s₁.rd → s'.wr = s₁.wr →
      (∀ r ∈ calleeSaved, s'.gpr r = s₁.gpr r) →
      Frame (wr s₀ ++ [below (s₁.gpr .esp) (4 * rs.length + stackUse c + 4)]) s₁.mem s'.mem →
      (∃ s₂ : State, s₂.mem = s'.mem ∧
        k.post ((pushed rs s₁).callEntry.withRegions (rd s₀) (wr s₀)) s₂) → B s₀ s') :
    Piece Pre Pub A B (.seq (.block (VG.Impl.MlDsa.X86.Message.setArgs as)) (Impl.MlKem.X86.callWith rs n c)) := by
  refine Piece.seq (VG.Proof.MlDsa.X86.Message.setArgs_piece as tt hpub hA hok) (Piece.callWith hv hct hsp hne hrs rd wr ?_ ?_ ?_ ?_)
  · rintro s₀ s₁ h₀ ⟨s, ha, hs⟩
    rw [hs.esp (hok s₀ h₀), (hA s₀ s h₀ ha).ctx.esp]
    exact hd s₀ s h₀ ha
  · rintro s₀ s₁ h₀ ⟨s, ha, hs⟩
    exact hk s₀ s s₁ h₀ ha hs
  · rintro s₀ s₀' s₁ s₁' h₀ h₀' hq ⟨s, ha, hs⟩ ⟨s', ha', hs'⟩
    obtain ⟨e₁, e₂⟩ := hrw s₀ s₀' h₀ h₀' hq
    refine ⟨e₁, e₂, ?_, hkp s₀ s₀' s s' s₁ s₁' h₀ h₀' hq ha ha' hs hs'⟩
    rw [hs.esp (hok s₀ h₀), hs'.esp (hok s₀' h₀'), (hA s₀ s h₀ ha).ctx.esp, (hA s₀' s' h₀' ha').ctx.esp,
      Lay.E1, Lay.E1, (hpub s₀ s₀' h₀ h₀' hq).sp]
  · rintro s₀ s₁ s' h₀ ⟨s, ha, hs⟩ e₁ e₂ e₃ fr post
    exact hQ s₀ s s₁ s' h₀ ha hs e₁ e₂ e₃ fr post

end

end VG.Proof.MlDsa.X86.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Message.Entry`. -/
section

/-!
# ML-DSA on x86 (32-bit), `sign_message` and `verify_message`: the check, the entry and the leaf

Untrusted: everything here is checked by Lean. What both functions' proofs
need of their layouts (`Shape`): where the arguments are, and the facts
their preconditions give. After the leaf's push, the body loads `ctx_len`
and compares it with 256 (`chk_piece`); if it is larger it returns 2
(`ret2_piece`), and otherwise points `esi` at the 1 KiB and stores
`0 ‖ ctx_len` there (`enter_piece`), which is where `Ctx` starts; then the
rest of the body, in a leaf (`top_piece`).
-/

namespace VG.Proof.MlDsa.X86.Message

open VG VG.X86 VG.X86.Wp VG.Impl.MlDsa.X86.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.X86 (Only Piece P0 E0 frameR retR P0_esp P0_wr P0_arg P0_argIn P0_argAddr LeafEnd LeafPost)
open VG.Spec.Sha3 (bytesAt)
open VG.Spec.MlDsa (Params)

/-- What the proofs need of the layouts of runs from states satisfying
`Pre`: the function's arguments, `scratch` among them (argument `si`), and
the facts the precondition gives. -/
structure Shape (Pre : State → Prop) (Pub : State → State → Prop) (lay : State → VG.Proof.MlDsa.X86.Message.Lay) (si : Nat) (p : Params) :
    Prop where
  sp : ∀ s₀, Pre s₀ → (lay s₀).SP = E0 s₀
  rd : ∀ s₀, Pre s₀ → (lay s₀).rd = s₀.rd
  wr : ∀ s₀, Pre s₀ → (lay s₀).wr = s₀.wr
  argv : ∀ s₀, Pre s₀ → ∀ i < (lay s₀).nA, (lay s₀).argv.getD i 0 = arg s₀ i
  ctxLen : ∀ s₀, Pre s₀ → (lay s₀).ctxLen = arg s₀ 4
  scr : ∀ s₀, Pre s₀ → (lay s₀).scr = arg s₀ si
  siLt : ∀ s₀, Pre s₀ → si < (lay s₀).nA
  E : ∀ s₀, Pre s₀ → (lay s₀).E = oE p
  ok : ∀ s₀, Pre s₀ → (arg s₀ 4).toNat < 256 → (lay s₀).Ok
  e16 : ∀ s₀, Pre s₀ → 16 ≤ (E0 s₀).toNat ∧ (E0 s₀).toNat + 4 ≤ 2 ^ 32
  fit : ∀ s₀, Pre s₀ → (E0 s₀).toNat + 4 + 4 * (lay s₀).nA ≤ 2 ^ 32
  fd : ∀ s₀, Pre s₀ → (⟨(E0 s₀).setWidth 64 - 16#64, 16⟩ : Region).Disjoint ⟨argAddr s₀ 0, 4 * (lay s₀).nA⟩
  ain : ∀ s₀, Pre s₀ → (⟨argAddr s₀ 0, 4 * (lay s₀).nA⟩ : Region) ∈ s₀.rd ++ s₀.wr
  n5 : ∀ s₀, Pre s₀ → 5 ≤ (lay s₀).nA
  pubE : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → E0 s₀ = E0 s₀'
  pubA : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → arg s₀ 4 = arg s₀' 4 ∧ arg s₀ si = arg s₀' si
  pubL : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → VG.Proof.MlDsa.X86.Message.PubL (lay s₀) (lay s₀')

/-- `mov [b + o], r8` -/
theorem wp_st8 {is : List Instr} {s : State} {Q : State → Prop} {b : Reg} {r : Reg8} {B : BitVec 32} {o : Nat}
    (hb : s.gpr b = B) (hout : InRegions s.wr (VG.X86.addr B o) 1)
    (k : ∀ s', Mupd s s' (s.mem.writeW (VG.X86.addr B o) ((s.gpr r.reg).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store8 ⟨b, o⟩ r :: is)) s Q := by
  refine cons (s' := { s with mem := s.mem.writeW (VG.X86.addr B o) ((s.gpr r.reg).setWidth 8) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
  simp [exec, State.store8, ea_mk, hb, hout]

section
variable {Pre : State → Prop} {Pub : State → State → Prop} {lay : State → VG.Proof.MlDsa.X86.Message.Lay} {si : Nat} {p : Params}

/-- After the check: `eax` is `ctx_len`, and the carry says whether it is below 256. -/
def Chk (s₀ s : State) : Prop :=
  Only [.eax] (P0 s₀) s ∧ s.cf = some (decide ((arg s₀ 4).toNat < 256))

theorem arg4_in (hS : VG.Proof.MlDsa.X86.Message.Shape Pre Pub lay si p) {s₀ : State} (h₀ : Pre s₀) {i : Nat} (hi : i < (lay s₀).nA) :
    InRegions ((P0 s₀).rd ++ (P0 s₀).wr) (VG.X86.addr (E0 s₀ - 16) (20 + 4 * i)) 4 := by
  rw [← P0_esp]
  show InRegions _ (((P0 s₀).gpr .esp + BitVec.ofNat 32 (20 + 4 * i)).setWidth 64) 4
  rw [P0_argAddr]
  exact P0_argIn hi (hS.fit s₀ h₀) (hS.ain s₀ h₀)

theorem arg_P0 (hS : VG.Proof.MlDsa.X86.Message.Shape Pre Pub lay si p) {s₀ : State} (h₀ : Pre s₀) {i : Nat} (hi : i < (lay s₀).nA) :
    (P0 s₀).mem.readW (VG.X86.addr (E0 s₀ - 16) (20 + 4 * i)) 32 = arg s₀ i := by
  rw [← P0_esp]
  show (P0 s₀).mem.readW (((P0 s₀).gpr .esp + BitVec.ofNat 32 (20 + 4 * i)).setWidth 64) 32 = _
  rw [P0_argAddr]
  exact P0_arg (hS.e16 s₀ h₀).1 hi (hS.fit s₀ h₀) (hS.fd s₀ h₀)

theorem chk_piece (hS : VG.Proof.MlDsa.X86.Message.Shape Pre Pub lay si p) :
    Piece Pre Pub (fun s₀ s => s = P0 s₀) VG.Proof.MlDsa.X86.Message.Chk (.block [.mov .eax (.mem (argAt 4)), .alu .cmp .eax (.imm 256)]) := by
  refine Piece.taint [.esp] (fun s₀ s h₀ e => ?_) (fun s₀ s₀' s s' h₀ h₀' hq e e' r hr => ?_) (by taint_decide)
  · subst e
    have h4 : 4 < (lay s₀).nA := by have := hS.n5 s₀ h₀; omega
    refine wp_ldm (b := .esp) (P0_esp s₀) (VG.Proof.MlDsa.X86.Message.arg4_in hS h₀ h4) fun s₁ u₁ => wp_cmpi fun s₂ f₂ c₂ _ => WP.block_nil ?_
    refine ⟨⟨fun r hr => ?_, by rw [f₂.mem, u₁.mem], by rw [f₂.rd, u₁.rd], by rw [f₂.wr, u₁.wr]⟩, ?_⟩
    · rw [f₂.gpr, u₁.other r (by simpa using hr)]
    · rw [c₂, u₁.gpr, VG.Proof.MlDsa.X86.Message.arg_P0 hS h₀ h4]; rfl
  · simp only [List.mem_singleton] at hr; subst hr
    rw [e, e', P0_esp, P0_esp, hS.pubE s₀ s₀' h₀ h₀' hq]

/-- `ctx_len ≥ 256`: return 2. -/
theorem ret2_piece {B : State → State → Prop}
    (hB : ∀ s₀ s, Pre s₀ → Only [.eax] (P0 s₀) s → 256 ≤ (arg s₀ 4).toNat → s.gpr .eax = 2 → B s₀ s) :
    Piece Pre Pub (fun s₀ s => VG.Proof.MlDsa.X86.Message.Chk s₀ s ∧ (!decide ((arg s₀ 4).toNat < 256)) = true) B
      (.block [.mov .eax (.imm 2)]) := by
  refine Piece.taint [] (fun s₀ s h₀ ⟨⟨o, _⟩, hb⟩ => VG.X86.Wp.wp_movi fun s₁ u₁ => WP.block_nil ?_)
    (fun _ _ _ _ _ _ _ _ _ _ h => absurd h List.not_mem_nil) (by taint_decide)
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, Nat.not_lt] at hb
  refine hB s₀ s₁ h₀ ⟨fun r hr => ?_, by rw [u₁.mem, o.mem], by rw [u₁.rd, o.rd], by rw [u₁.wr, o.wr]⟩ hb u₁.gpr
  rw [u₁.other r (by simpa using hr), o.gpr r hr]

/-- Bytes `0 ‖ c` at `X + 944`, from their stores. -/
theorem hdr_bytes (m : Mem) (X : Addr) (c : BitVec 32) :
    bytesAt ((m.writeW (X + BitVec.ofNat 64 944) ((0 : BitVec 32).setWidth 8)).writeW (X + BitVec.ofNat 64 945)
      (c.setWidth 8)) (X + BitVec.ofNat 64 944) 2 = [0, BitVec.ofNat 8 c.toNat] := by
  have n45 : X + BitVec.ofNat 64 944 ≠ X + BitVec.ofNat 64 945 :=
    Offset.add_ofNat_ne _ (by omega) (by omega) (by omega)
  simp only [bytesAt, List.range, List.range.loop, List.map_cons, List.map_nil, add_add, Nat.reduceAdd]
  rw [byte_writeW_other _ n45, byte_writeW_self, byte_writeW_self]
  refine List.cons_eq_cons.mpr ⟨rfl, List.cons_eq_cons.mpr ⟨?_, rfl⟩⟩
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

theorem E0_E1 (hS : VG.Proof.MlDsa.X86.Message.Shape Pre Pub lay si p) {s₀ : State} (h₀ : Pre s₀) : E0 s₀ - 16 = (lay s₀).E1 := by
  rw [Lay.E1, hS.sp s₀ h₀]; rfl

/-- `esi ← scratch + oE p`, and `0 ‖ ctx_len` at `esi + 944`. -/
theorem enter_piece (hS : VG.Proof.MlDsa.X86.Message.Shape Pre Pub lay si p) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp]) (.block [.mov .esi (.mem (argAt si)),
      .alu .add .esi (.imm (BitVec.ofNat 32 (oE p)))]) ht).isSome = true) :
    Piece Pre Pub (fun s₀ s => VG.Proof.MlDsa.X86.Message.Chk s₀ s ∧ (!decide ((arg s₀ 4).toNat < 256)) = false) (VG.Proof.MlDsa.X86.Message.CtxO lay) (enter si p) := by
  refine Piece.seq (B := fun s₀ s => Only [.eax, .esi] (P0 s₀) s ∧ s.gpr .esi = (lay s₀).X32 ∧ (lay s₀).Ok)
    (Piece.taint [.esp] (fun s₀ s h₀ ⟨⟨o, _⟩, hb⟩ => ?_) (fun s₀ s₀' s s' h₀ h₀' hq ⟨⟨o, _⟩, _⟩ ⟨⟨o', _⟩, _⟩ r hr => ?_) tt)
    (Piece.taint [.esp, .esi] (fun s₀ s h₀ ⟨o, hx, hL⟩ => ?_)
      (fun s₀ s₀' s s' h₀ h₀' hq ⟨o, hx, _⟩ ⟨o', hx', _⟩ r hr => ?_) (by taint_decide))
  · have hc : (arg s₀ 4).toNat < 256 := by simpa using hb
    have hsp : s.gpr .esp = E0 s₀ - 16 := by rw [o.gpr _ (by decide), P0_esp]
    have hin : InRegions (s.rd ++ s.wr) (VG.X86.addr (E0 s₀ - 16) (20 + 4 * si)) 4 := by
      rw [o.rd, o.wr]; exact VG.Proof.MlDsa.X86.Message.arg4_in hS h₀ (hS.siLt s₀ h₀)
    refine wp_ldm (b := .esp) hsp hin fun s₁ u₁ => VG.X86.Wp.wp_addi fun s₂ u₂ => WP.block_nil
      ⟨⟨fun r hr => ?_, by rw [u₂.mem, u₁.mem, o.mem], by rw [u₂.rd, u₁.rd, o.rd], by rw [u₂.wr, u₁.wr, o.wr]⟩,
        ?_, hS.ok s₀ h₀ hc⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [u₂.other r hr.2, u₁.other r hr.2, o.gpr r (by simpa using hr.1)]
    · rw [u₂.gpr, u₁.gpr, o.mem, VG.Proof.MlDsa.X86.Message.arg_P0 hS h₀ (hS.siLt s₀ h₀), Lay.X32, hS.scr s₀ h₀, hS.E s₀ h₀]
  · simp only [List.mem_singleton] at hr; subst hr
    rw [o.gpr _ (by decide), o'.gpr _ (by decide), P0_esp, P0_esp, hS.pubE s₀ s₀' h₀ h₀' hq]
  · have hsp : s.gpr .esp = E0 s₀ - 16 := by rw [o.gpr _ (by decide), P0_esp]
    have h4 : 4 < (lay s₀).nA := by have := hS.n5 s₀ h₀; omega
    have e944 : VG.X86.addr (lay s₀).X32 oHdr = (lay s₀).X + BitVec.ofNat 64 944 := hL.xo (by decide)
    have e945 : VG.X86.addr (lay s₀).X32 (oHdr + 1) = (lay s₀).X + BitVec.ofNat 64 945 := hL.xo (by decide)
    have hwr : s.wr = frameR s₀ :: (lay s₀).wr := by rw [o.wr, P0_wr, hS.wr s₀ h₀]
    have hout : ∀ e, e + 1 ≤ 1024 → InRegions s.wr ((lay s₀).X + BitVec.ofNat 64 e) 1 := fun e he => by
      obtain ⟨R, hR, c⟩ := hL.inW (e := e) (k := 1) he
      exact ⟨R, by rw [hwr]; exact List.mem_cons_of_mem _ hR, c⟩
    have cSC : ∀ e, e + 1 ≤ 1024 → (lay s₀).SC.Contains ((lay s₀).X + BitVec.ofNat 64 e) 1 := fun e he =>
      hL.sub_sc (e := e) (k := 1) he _ (Region.contains_self _ _)
    refine VG.X86.Wp.wp_movi fun s₁ u₁ => VG.Proof.MlDsa.X86.Message.wp_st8 (b := .esi) (B := (lay s₀).X32) (by rw [u₁.other _ (by decide), hx])
      (by rw [e944, u₁.wr]; exact hout 944 (by omega)) fun s₂ m₂ => ?_
    have f₂ : Frame [(lay s₀).SC, (lay s₀).STK] (P0 s₀).mem s₂.mem := by
      rw [m₂.mem, u₁.mem, o.mem, e944]
      exact (Frame.refl _ _).writeW (List.mem_cons_self ..) _ (cSC 944 (by omega))
    have hargs : ∀ {m : Mem}, Frame [(lay s₀).SC, (lay s₀).STK] (P0 s₀).mem m → ∀ i < (lay s₀).nA,
        m.readW (((lay s₀).SP + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64) 32 = arg s₀ i := by
      intro m fr i hi
      rw [fr.readW (hL.argIn hi) (fun r hr => ?_) (by decide), ← Lay.Ok.argAt_eq, ← VG.Proof.MlDsa.X86.Message.E0_E1 hS h₀]
      · exact VG.Proof.MlDsa.X86.Message.arg_P0 hS h₀ hi
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hL.aSC
        · exact hL.kArgs.symm
    refine wp_ldm (b := .esp) (by rw [m₂.gpr, u₁.other _ (by decide), hsp])
      (by rw [m₂.rd, m₂.wr, u₁.rd, u₁.wr, o.rd, o.wr]; exact VG.Proof.MlDsa.X86.Message.arg4_in hS h₀ h4) fun s₃ u₃ => ?_
    have v₃ : s₃.gpr .eax = arg s₀ 4 := by
      rw [u₃.gpr, VG.Proof.MlDsa.X86.Message.E0_E1 hS h₀, Lay.Ok.argAt_eq]; exact hargs f₂ 4 h4
    refine VG.Proof.MlDsa.X86.Message.wp_st8 (b := .esi) (B := (lay s₀).X32) (by rw [u₃.other _ (by decide), m₂.gpr, u₁.other _ (by decide), hx])
      (by rw [e945, u₃.wr, m₂.wr, u₁.wr]; exact hout 945 (by omega)) fun s₄ m₄ => WP.block_nil ⟨hL, ?_⟩
    have mm : s₄.mem = ((P0 s₀).mem.writeW ((lay s₀).X + BitVec.ofNat 64 944) ((0 : BitVec 32).setWidth 8)).writeW
        ((lay s₀).X + BitVec.ofNat 64 945) ((arg s₀ 4).setWidth 8) := by
      have ral : Reg8.al.reg = .eax := rfl
      rw [m₄.mem, u₃.mem, e945, m₂.mem, u₁.mem, o.mem, e944, ral, v₃, u₁.gpr]
    have f₄ : Frame [(lay s₀).SC, (lay s₀).STK] (P0 s₀).mem s₄.mem := by
      rw [m₄.mem, u₃.mem, e945]
      exact f₂.writeW (List.mem_cons_self ..) _ (cSC 945 (by omega))
    refine ⟨by rw [m₄.rd, u₃.rd, m₂.rd, u₁.rd, o.rd, pushed_rd, hS.rd s₀ h₀],
      by rw [m₄.wr, u₃.wr, m₂.wr, u₁.wr, hwr, hS.sp s₀ h₀], by rw [m₄.gpr, u₃.other _ (by decide), m₂.gpr,
        u₁.other _ (by decide), hsp, VG.Proof.MlDsa.X86.Message.E0_E1 hS h₀],
      by rw [m₄.gpr, u₃.other _ (by decide), m₂.gpr, u₁.other _ (by decide), hx],
      by rw [mm, VG.Proof.MlDsa.X86.Message.hdr_bytes, hS.ctxLen s₀ h₀], fun i hi => by rw [hargs f₄ i hi, hS.argv s₀ h₀ i hi], f₄⟩
  · have hp := hS.pubL s₀ s₀' h₀ h₀' hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [o.gpr _ (by decide), o'.gpr _ (by decide), P0_esp, P0_esp, hS.pubE s₀ s₀' h₀ h₀' hq]
    · rw [hx, hx', hp.x]

/-- The whole function: the check, and the entry and `rest` if `ctx_len < 256`, in a leaf
that changes memory only within `W`. -/
theorem top_piece (hS : VG.Proof.MlDsa.X86.Message.Shape Pre Pub lay si p) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp]) (.block [.mov .esi (.mem (argAt si)),
      .alu .add .esi (.imm (BitVec.ofNat 32 (oE p)))]) ht).isSome = true)
    {rest : Prog isa} {B : State → State → Prop} (W : State → List Region)
    (hW : ∀ s₀, Pre s₀ → ∀ r ∈ W s₀, (frameR s₀).Disjoint r ∧ (VG.Proof.MlKem.X86.retR s₀).Disjoint r)
    (hsp : NoSp (.seq (.block [.mov .eax (.mem (argAt 4)), .alu .cmp .eax (.imm 256)])
      (.ite .ae (.block [.mov .eax (.imm 2)]) (.seq (enter si p) rest))))
    (hr : Piece Pre Pub (VG.Proof.MlDsa.X86.Message.CtxO lay) (fun s₀ s => LeafEnd s₀ (W s₀) s ∧ B s₀ s) rest) :
    Piece Pre Pub (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (fun s => (256 ≤ (arg s₀ 4).toNat ∧
      s.gpr .eax = 2) ∨ B s₀ s) s₀ s') (top (enter si p) rest) := by
  refine Piece.leaf W hsp hS.e16 hW hS.pubE ?_
  refine Piece.seq (VG.Proof.MlDsa.X86.Message.chk_piece hS) (Piece.ite (fun s₀ => !decide ((arg s₀ 4).toNat < 256))
    (fun s₀ s h₀ h => ?_) (fun s₀ s₀' h₀ h₀' hq => ?_) (VG.Proof.MlDsa.X86.Message.ret2_piece fun s₀ s h₀ o hc h2 => ?_)
    (Piece.seq (VG.Proof.MlDsa.X86.Message.enter_piece hS tt) (hr.mono (fun _ _ _ h => h) fun s₀ s h₀ ⟨he, hb⟩ => ⟨he, .inr hb⟩)))
  · show s.cf.map (!·) = _
    rw [h.2]; rfl
  · rw [(hS.pubA s₀ s₀' h₀ h₀' hq).1]
  · exact ⟨⟨by rw [o.mem]; exact Frame.refl _ _, o.gpr _ (by decide), o.rd, o.wr⟩, .inl ⟨hc, h2⟩⟩

/-- `LeafEnd`, from `Ctx` and a frame of the memory from it. -/
theorem CtxO.leafEnd (hS : VG.Proof.MlDsa.X86.Message.Shape Pre Pub lay si p) {s₀ s s' : State} (h₀ : Pre s₀) (hc : VG.Proof.MlDsa.X86.Message.CtxO lay s₀ s)
    {W : List Region} (hW : ∀ r ∈ [(lay s₀).SC, (lay s₀).STK], r ∈ W) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hrs : ∀ r ∈ rs, ∃ R ∈ W, Region.Sub r R)
    (hsp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : LeafEnd s₀ W s' := by
  refine ⟨(hc.ctx.frame.sub fun r hr => ⟨r, hW r hr, fun _ h => h⟩).trans (hf.sub hrs),
    by rw [hsp, hc.ctx.esp, ← VG.Proof.MlDsa.X86.Message.E0_E1 hS h₀, P0_esp], by rw [hrd, hc.ctx.rd, hS.rd s₀ h₀, pushed_rd],
    by rw [hwr, hc.ctx.wr, P0_wr, hS.wr s₀ h₀, hS.sp s₀ h₀]⟩

end

end VG.Proof.MlDsa.X86.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Message.Hash`. -/
section

/-!
# ML-DSA on x86 (32-bit), `sign_message` and `verify_message`: SHAKE256 through the sponge functions

Untrusted: everything here is checked by Lean. In `Ctx`: zeroing the Keccak
state at `X` (`zeroSt_ok`), and the calls of `vg_keccak_absorb` (keeping the
position it returns in `eax`), `vg_keccak_pad` and `vg_keccak_squeeze` on it,
with their working space at `X + 200` (`kabs_ok`, `kpad_ok`, `ksqz_ok`, from
ML-KEM's lemmas on their calls, `Proof/MlKem/X86/Keccak.lean`).
-/

namespace VG.Proof.MlDsa.X86.Message

open VG VG.X86 VG.X86.Wp VG.Impl.MlDsa.X86.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.X86 (Piece Only AbsArgs KBufs PadArgs absorb_pre absorb_post pad_pre pad_post squeeze_pre squeeze_post
  absorb_stack pad_stack squeeze_stack absorb_nosp pad_nosp squeeze_nosp toNat_ofNat32)
open VG.Proof.Sha3.X86 (reg32)
open VG.Spec.Sha3 (bytesAt stateAt rates absorb pad squeezeFrom Repr)

section
variable {L : VG.Proof.MlDsa.X86.Message.Lay} {m₁ : Mem}

theorem x0 (L : VG.Proof.MlDsa.X86.Message.Lay) : L.X + BitVec.ofNat 64 0 = L.X := BitVec.add_zero _
theorem x0' (L : VG.Proof.MlDsa.X86.Message.Lay) : L.X32 + BitVec.ofNat 32 0 = L.X32 := BitVec.add_zero _

theorem st_ks : Region.Disjoint ⟨L.ST, 200⟩ ⟨L.KS, 640⟩ := by
  have := Offset.disjoint L.X (d := 0) (n := 200) (e := 200) (k := 640) (by omega) (by omega) (by omega)
  simpa only [VG.Proof.MlDsa.X86.Message.x0] using this

theorem st_mu : Region.Disjoint ⟨L.ST, 200⟩ ⟨L.MU, 64⟩ := by
  have := Offset.disjoint L.X (d := 0) (n := 200) (e := 840) (k := 64) (by omega) (by omega) (by omega)
  simpa only [VG.Proof.MlDsa.X86.Message.x0] using this

theorem mu_ks : Region.Disjoint ⟨L.MU, 64⟩ ⟨L.KS, 640⟩ :=
  Offset.disjoint L.X (d := 840) (n := 64) (e := 200) (k := 640) (by omega) (by omega) (by omega)

theorem w_st : Within ⟨L.ST, 200⟩ L.W := within_base _ (by omega)
theorem w_ks : Within ⟨L.KS, 640⟩ L.W := within_off _ (by omega)
theorem w_mu : Within ⟨L.MU, 64⟩ L.W := within_off _ (by omega)

theorem k_st (hL : L.Ok) : L.STK.Disjoint ⟨L.ST, 200⟩ := by
  have := hL.stk_x (e := 0) (k := 200) (by omega); simpa only [VG.Proof.MlDsa.X86.Message.x0] using this
theorem k_ks (hL : L.Ok) : L.STK.Disjoint ⟨L.KS, 640⟩ := hL.stk_x (by omega)
theorem k_mu (hL : L.Ok) : L.STK.Disjoint ⟨L.MU, 64⟩ := hL.stk_x (by omega)

/-- The 40 bytes a call of a sponge function uses lie in `STK`. -/
theorem b40 (hL : L.Ok) : Region.Sub (below L.E1 40) L.STK := by
  have := hL.nSP; have := hL.hN
  exact below_sub (by omega) (by rw [Lay.E1, sub_toNat (by omega)]; omega)

theorem e40 (hL : L.Ok) : 40 ≤ L.E1.toNat := by
  have := hL.nSP; have := hL.hN
  rw [Lay.E1, sub_toNat (by omega)]; omega

theorem ks_eq (hL : L.Ok) : (L.X32 + BitVec.ofNat 32 200).setWidth 64 = L.KS := hL.xo (by decide)
theorem regKS (hL : L.Ok) : reg32 (L.X32 + BitVec.ofNat 32 200) 640 = ⟨L.KS, 640⟩ := by
  show (⟨_, 640⟩ : Region) = _; rw [VG.Proof.MlDsa.X86.Message.ks_eq hL]
theorem mu_eq (hL : L.Ok) : (L.X32 + BitVec.ofNat 32 840).setWidth 64 = L.MU := hL.xo (by decide)

theorem cov_x (hL : L.Ok) {e k : Nat} (h₂ : e + k ≤ 1024) :
    ∃ R ∈ L.rd ++ L.wr, Within ⟨L.X + BitVec.ofNat 64 e, k⟩ R := by
  obtain ⟨R, hR, hw⟩ := hL.covX h₂; exact ⟨R, List.mem_append_right _ hR, hw⟩

/-- `Within` as ML-KEM's lemmas take it, in the body's writable regions. -/
theorem withinW {t : State} (hc : VG.Proof.MlDsa.X86.Message.Ctx L m₁ t) {r : Region} (h : ∃ R ∈ L.wr, Within r R) :
    Proof.MlKem.X86.Within r t.wr := by
  obtain ⟨R, hR, o, hb, hl⟩ := h
  exact ⟨R, by rw [hc.wr]; exact List.mem_cons_of_mem _ hR, o, hb, hl⟩

theorem withinRW {t : State} (hc : VG.Proof.MlDsa.X86.Message.Ctx L m₁ t) {r : Region} (h : ∃ R ∈ L.rd ++ L.wr, Within r R) :
    Proof.MlKem.X86.Within r (t.rd ++ t.wr) := by
  obtain ⟨R, hR, o, hb, hl⟩ := h
  refine ⟨R, ?_, o, hb, hl⟩
  rw [hc.rd, hc.wr]
  rcases List.mem_append.mp hR with h | h
  · exact List.mem_append_left _ h
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)

/-- The Keccak state and the working space, for ML-KEM's lemmas. -/
theorem kbufs (hL : L.Ok) : KBufs L.E1 L.X32 (L.X32 + BitVec.ofNat 32 200) := by
  have := hL.x32_lt
  refine ⟨VG.Proof.MlDsa.X86.Message.e40 hL, by omega, by rw [hL.x32_toNat (by omega)]; omega, ?_, ?_, ?_⟩
  · rw [VG.Proof.MlDsa.X86.Message.regKS hL]; exact VG.Proof.MlDsa.X86.Message.st_ks
  · exact (VG.Proof.MlDsa.X86.Message.k_st hL).sub_left (VG.Proof.MlDsa.X86.Message.b40 hL)
  · rw [VG.Proof.MlDsa.X86.Message.regKS hL]; exact (VG.Proof.MlDsa.X86.Message.k_ks hL).sub_left (VG.Proof.MlDsa.X86.Message.b40 hL)

/-! ## Zeroing the state -/

theorem zeroSt_ok (hL : L.Ok) {t : State} (hc : VG.Proof.MlDsa.X86.Message.Ctx L m₁ t) :
    WP isa (.block zeroSt) t fun t' => VG.Proof.MlDsa.X86.Message.Ctx L m₁ t' ∧ Frame [⟨L.ST, 200⟩] t.mem t'.mem ∧
      stateAt t'.mem L.ST = Spec.Sha3.zero := by
  rw [zeroSt]
  refine VG.X86.Wp.wp_movi fun t1 u1 => ?_
  have e1 : t1.gpr .esi = L.X32 := by rw [u1.other _ (by decide), hc.esi]
  let Inv : Nat → State → Prop := fun k s => s.gpr = t1.gpr ∧ s.rd = t1.rd ∧ s.wr = t1.wr ∧
    Frame [⟨L.ST, 200⟩] t1.mem s.mem ∧ ∀ j < k, s.mem.readW (L.X + BitVec.ofNat 64 (4 * j)) 32 = 0
  refine WP.mono (wp_range_flatMap (M := isa) Inv (fun k s hk h => ?_) 50 (Nat.le_refl _) t1
    ⟨rfl, rfl, rfl, Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero j)⟩) fun t' ⟨g, rd, wr, fr, z⟩ => ?_
  · have hb : s.gpr .esi = L.X32 := by rw [h.1, e1]
    have ea : VG.X86.addr L.X32 (4 * k) = L.X + BitVec.ofNat 64 (4 * k) := hL.xo (by omega)
    have hin : InRegions s.wr (VG.X86.addr L.X32 (4 * k)) 4 := by
      rw [ea, h.2.2.1, u1.wr, hc.wr]
      obtain ⟨R, hR, c⟩ := hL.inW (e := 4 * k) (k := 4) (by omega)
      exact ⟨R, List.mem_cons_of_mem _ hR, c⟩
    refine wp_stm (o := 4 * k) hb hin fun s' m => WP.block_nil ⟨by rw [m.gpr, h.1], by rw [m.rd, h.2.1], by rw [m.wr, h.2.2.1], ?_, fun j hj => ?_⟩
    · rw [m.mem, ea]
      exact h.2.2.2.1.writeW (List.mem_singleton_self _) _ (by
        have := Offset.contains_base L.X (d := 4 * k) (n := 4) (k := 200) (by omega) (by omega)
        simpa only [VG.Proof.MlDsa.X86.Message.x0] using this)
    · rw [m.mem, ea, h.1, u1.gpr]
      by_cases e : j = k
      · subst e; exact Mem.readW_writeW_self32 _ _ _
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
        exact h.2.2.2.2 j (by omega)
  · have hc1 : VG.Proof.MlDsa.X86.Message.Ctx L m₁ t1 := hc.regs u1.rd u1.wr u1.mem (u1.other _ (by decide)) (u1.other _ (by decide))
    refine ⟨hc1.keep hL rd wr (by rw [g]) (by rw [g]) fr fun r hr => ?_, by rw [← u1.mem]; exact fr,
      Proof.MlKem.X86.Sample.stateAt_zero fun j hj => ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact .inl VG.Proof.MlDsa.X86.Message.w_st
    · have e := Mem.readW_byte t'.mem (L.X + BitVec.ofNat 64 (4 * (j / 4))) (i := j % 4) (by omega)
      rw [add_add, show 4 * (j / 4) + j % 4 = j by omega, z (j / 4) (by omega)] at e
      rw [e]
      apply BitVec.eq_of_toNat_eq
      simp

/-! ## Absorbing -/

/-- The arguments of a call of `vg_keccak_absorb`. -/
abbrev absArgs (src len pos : VG.Impl.MlDsa.X86.Message.Arg) : List (Reg × VG.Impl.MlDsa.X86.Message.Arg) :=
  [(.edx, pos), (.eax, .off VG.Impl.MlDsa.X86.Message.oST), (.ecx, .imm 136), (.ebx, src), (.ebp, len), (.edi, .off oKS)]

/-- The position `vg_keccak_absorb` returns. -/
theorem absorb_eax {s s₂ : State} {E S D W : BitVec 32} {pos len : Nat} (hesp : s.gpr .esp = E)
    (ha : AbsArgs s S D W 136 pos len) (hE : 40 ≤ E.toNat) (hlen : len < 2 ^ 32) (hpos : pos < 2 ^ 32)
    {rd wr : List Region} (post : Proof.Sha3.absorbX86.post ((pushed Proof.MlKem.X86.rs6 s).callEntry.withRegions rd wr) s₂) :
    (s₂.gpr .eax).toNat = (pos + len) % 136 := by
  have fit : 4 * Proof.MlKem.X86.rs6.length + 4 ≤ (s.gpr .esp).toNat := by
    rw [hesp]; simp only [List.length_cons, List.length_nil]; omega
  have a1 : arg (pushed Proof.MlKem.X86.rs6 s).callEntry 1 = BitVec.ofNat 32 136 := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact ha.ecx
  have a2 : arg (pushed Proof.MlKem.X86.rs6 s).callEntry 2 = BitVec.ofNat 32 pos := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact ha.edx
  have a4 : arg (pushed Proof.MlKem.X86.rs6 s).callEntry 4 = BitVec.ofNat 32 len := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact ha.ebp
  have := post.2
  simp only [arg_withRegions, a1, a2, a4, VG.Proof.MlKem.X86.toNat_ofNat32 hlen, VG.Proof.MlKem.X86.toNat_ofNat32 hpos,
    VG.Proof.MlKem.X86.toNat_ofNat32 (show 136 < 2 ^ 32 by decide)] at this
  exact this

theorem regMU (hL : L.Ok) : reg32 (L.X32 + BitVec.ofNat 32 840) 64 = ⟨L.MU, 64⟩ := by
  show (⟨_, 64⟩ : Region) = _; rw [VG.Proof.MlDsa.X86.Message.mu_eq hL]

theorem SetPost.ctx {n : Nat} {as : List (Reg × VG.Impl.MlDsa.X86.Message.Arg)} (hok : VG.Proof.MlDsa.X86.Message.argsOk n as = true) {s s₁ : State}
    (hs : VG.Proof.MlDsa.X86.Message.SetPost as s s₁) (hc : VG.Proof.MlDsa.X86.Message.Ctx L m₁ s) : VG.Proof.MlDsa.X86.Message.Ctx L m₁ s₁ :=
  hc.regs hs.2.rd hs.2.wr hs.2.mem (hs.esp hok) (hs.esi hok)

end

/-! ## As pieces -/

section
variable {Pre : State → Prop} {Pub : State → State → Prop} {lay : State → VG.Proof.MlDsa.X86.Message.Lay} {A B : State → State → Prop}

theorem zeroSt_piece (hpub : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → VG.Proof.MlDsa.X86.Message.PubL (lay s₀) (lay s₀'))
    (hA : ∀ s₀ s, Pre s₀ → A s₀ s → VG.Proof.MlDsa.X86.Message.CtxO lay s₀ s)
    (hQ : ∀ s₀ s s', Pre s₀ → A s₀ s → VG.Proof.MlDsa.X86.Message.CtxO lay s₀ s' → Frame [⟨(lay s₀).ST, 200⟩] s.mem s'.mem →
      stateAt s'.mem (lay s₀).ST = Spec.Sha3.zero → B s₀ s') :
    Piece Pre Pub A B (.block zeroSt) :=
  Piece.taint [.esi] (fun s₀ s h₀ ha => by
      have h := hA s₀ s h₀ ha
      exact (VG.Proof.MlDsa.X86.Message.zeroSt_ok h.ok h.ctx).mono fun s' ⟨c, f, z⟩ => hQ s₀ s s' h₀ ha ⟨h.ok, c⟩ f z)
    (fun s₀ s₀' s s' h₀ h₀' hq ha ha' r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [(hA s₀ s h₀ ha).ctx.esi, (hA s₀' s' h₀' ha').ctx.esi, (hpub s₀ s₀' h₀ h₀' hq).x]) (by taint_decide)

/-- The stack the sponge functions' calls use. -/
theorem kb_stk {L : VG.Proof.MlDsa.X86.Message.Lay} (hL : L.Ok) {a : Nat} (ha : a ≤ 40) : Region.Sub (below L.E1 a) L.STK :=
  fun x h => VG.Proof.MlDsa.X86.Message.b40 hL x (below_sub (a := a) (b := 40) ha (VG.Proof.MlDsa.X86.Message.e40 hL) x h)

/-- A call of `vg_keccak_absorb`, continuing the message at the position `q s₀`
with the `n s₀` bytes at `dp s₀`. -/
theorem kabs_piece (src len pos : VG.Impl.MlDsa.X86.Message.Arg) (dp : State → BitVec 32) (n q : State → Nat)
    {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (VG.Impl.MlDsa.X86.Message.setArgs (VG.Proof.MlDsa.X86.Message.absArgs src len pos))) ht).isSome = true)
    (hpub : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → VG.Proof.MlDsa.X86.Message.PubL (lay s₀) (lay s₀'))
    (hA : ∀ s₀ s, Pre s₀ → A s₀ s → VG.Proof.MlDsa.X86.Message.CtxO lay s₀ s)
    (hok : ∀ s₀, Pre s₀ → VG.Proof.MlDsa.X86.Message.argsOk (lay s₀).nA (VG.Proof.MlDsa.X86.Message.absArgs src len pos) = true)
    (hv : ∀ s₀ s, Pre s₀ → A s₀ s → src.val s = dp s₀ ∧ len.val s = BitVec.ofNat 32 (n s₀) ∧
      pos.val s = BitVec.ofNat 32 (q s₀))
    (hdn : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → dp s₀ = dp s₀' ∧ n s₀ = n s₀' ∧ q s₀ = q s₀')
    (hb : ∀ s₀ s, Pre s₀ → A s₀ s → q s₀ < 136 ∧ n s₀ < 2 ^ 32 ∧ (dp s₀).toNat + n s₀ ≤ 2 ^ 32 ∧
      (∃ R ∈ (lay s₀).rd ++ (lay s₀).wr, Within ⟨(dp s₀).setWidth 64, n s₀⟩ R) ∧
      Region.Disjoint ⟨(dp s₀).setWidth 64, n s₀⟩ ⟨(lay s₀).ST, 200⟩ ∧
      Region.Disjoint ⟨(dp s₀).setWidth 64, n s₀⟩ ⟨(lay s₀).KS, 640⟩ ∧
      (lay s₀).STK.Disjoint ⟨(dp s₀).setWidth 64, n s₀⟩)
    (hQ : ∀ s₀ s s', Pre s₀ → A s₀ s → VG.Proof.MlDsa.X86.Message.CtxO lay s₀ s' →
      Frame [⟨(lay s₀).ST, 200⟩, ⟨(lay s₀).KS, 640⟩, (lay s₀).STK] s.mem s'.mem →
      (∀ msg, Repr s.mem (lay s₀).ST 136 msg → q s₀ = msg.length % 136 →
        Repr s'.mem (lay s₀).ST 136 (msg ++ bytesAt s.mem ((dp s₀).setWidth 64) (n s₀))) →
      (s'.gpr .eax).toNat = (q s₀ + n s₀) % 136 → B s₀ s') :
    Piece Pre Pub A B (kabs src len pos) := by
  have hargs : ∀ s₀ s s₁, Pre s₀ → A s₀ s → VG.Proof.MlDsa.X86.Message.SetPost (VG.Proof.MlDsa.X86.Message.absArgs src len pos) s s₁ →
      AbsArgs s₁ (lay s₀).X32 (dp s₀) ((lay s₀).X32 + BitVec.ofNat 32 200) 136 (q s₀) (n s₀) := by
    intro s₀ s s₁ h₀ ha hs
    have hc := (hA s₀ s h₀ ha).ctx
    obtain ⟨v₁, v₂, v₃⟩ := hv s₀ s h₀ ha
    have e2 := hs.1 (.edx, pos) (by simp)
    have e0 := hs.1 (.eax, .off VG.Impl.MlDsa.X86.Message.oST) (by simp)
    have e1 := hs.1 (.ecx, .imm 136) (by simp)
    have e3 := hs.1 (.ebx, src) (by simp)
    have e4 := hs.1 (.ebp, len) (by simp)
    have e5 := hs.1 (.edi, .off oKS) (by simp)
    simp only [Arg.val, hc.esi, VG.Impl.MlDsa.X86.Message.oST, oKS, VG.Proof.MlDsa.X86.Message.x0'] at e0 e1 e5
    rw [v₃] at e2
    rw [v₁] at e3
    rw [v₂] at e4
    exact ⟨e0, e1, e2, e3, e4, e5⟩
  refine VG.Proof.MlDsa.X86.Message.argsRet_piece Proof.Sha3.X86.Stream.Absorb.absorb_verified.1
    Proof.Sha3.X86.Stream.Absorb.absorb_verified.2.1 absorb_nosp (by decide) (by decide) tt hpub hA hok
    (fun s₀ => [reg32 (dp s₀) (n s₀)])
    (fun s₀ => [reg32 (lay s₀).X32 200, reg32 ((lay s₀).X32 + BitVec.ofNat 32 200) 640, below (lay s₀).E1 24])
    (fun s₀ s₀' h₀ h₀' hq => ?_) (fun s₀ s h₀ ha => ?_) (fun s₀ s s₁ h₀ ha hs => ?_)
    (fun s₀ s₀' s s' s₁ s₁' h₀ h₀' hq ha ha' hs hs' => ?_) (fun s₀ s s₁ s' h₀ ha hs e₁ e₂ e₃ fr post => ?_)
  · obtain ⟨d₁, d₂, -⟩ := hdn s₀ s₀' h₀ h₀' hq
    have hp := hpub s₀ s₀' h₀ h₀' hq
    refine ⟨by rw [d₁, d₂], ?_⟩
    simp only [Lay.E1, hp.x, hp.sp]
  · have := VG.Proof.MlDsa.X86.Message.e40 (hA s₀ s h₀ ha).ok
    rw [absorb_stack]; simp only [List.length_cons, List.length_nil]; omega
  · obtain ⟨hL, hc⟩ := hA s₀ s h₀ ha
    have hc1 := SetPost.ctx (hok s₀ h₀) hs hc
    obtain ⟨hql, hnl, hfit, hin, dS, dK, kD⟩ := hb s₀ s h₀ ha
    exact absorb_pre hc1.esp (hargs s₀ s s₁ h₀ ha hs) (VG.Proof.MlDsa.X86.Message.kbufs hL) hfit dS (by rw [VG.Proof.MlDsa.X86.Message.regKS hL]; exact dK)
      (kD.sub_left (VG.Proof.MlDsa.X86.Message.b40 hL)) (by decide) hql hnl (VG.Proof.MlDsa.X86.Message.withinRW hc1 hin)
      (VG.Proof.MlDsa.X86.Message.withinW hc1 (by have := hL.covX (e := 0) (k := 200) (by omega); rwa [VG.Proof.MlDsa.X86.Message.x0] at this))
      (VG.Proof.MlDsa.X86.Message.withinW hc1 (by rw [VG.Proof.MlDsa.X86.Message.regKS hL]; exact hL.covX (e := 200) (by omega)))
  · have a := hargs s₀ s s₁ h₀ ha hs
    have a' := hargs s₀' s' s₁' h₀' ha' hs'
    obtain ⟨d₁, d₂, d₃⟩ := hdn s₀ s₀' h₀ h₀' hq
    have hp := hpub s₀ s₀' h₀ h₀' hq
    rw [← d₁, ← d₂, ← d₃, ← hp.x] at a'
    have hsp : s₁.gpr .esp = s₁'.gpr .esp := by
      rw [hs.esp (hok s₀ h₀), hs'.esp (hok s₀' h₀'), (hA s₀ s h₀ ha).ctx.esp, (hA s₀' s' h₀' ha').ctx.esp,
        Lay.E1, Lay.E1, hp.sp]
    have hE : 40 ≤ (s₁.gpr .esp).toNat := by
      rw [hs.esp (hok s₀ h₀), (hA s₀ s h₀ ha).ctx.esp]; exact VG.Proof.MlDsa.X86.Message.e40 (hA s₀ s h₀ ha).ok
    exact Proof.MlKem.X86.args6_eq hE hsp (Proof.MlKem.X86.absArgs_eq a a') _ _
  · obtain ⟨hL, hc⟩ := hA s₀ s h₀ ha
    have hc1 := SetPost.ctx (hok s₀ h₀) hs hc
    have a := hargs s₀ s s₁ h₀ ha hs
    obtain ⟨hql, hnl, -, -, -, -, kD⟩ := hb s₀ s h₀ ha
    have hsp : s₁.gpr .esp = (lay s₀).E1 := hc1.esp
    have hE := VG.Proof.MlDsa.X86.Message.e40 hL
    have kb : ∀ r ∈ [reg32 (lay s₀).X32 200, reg32 ((lay s₀).X32 + BitVec.ofNat 32 200) 640, below (lay s₀).E1 24] ++
        [below (s₁.gpr .esp) (4 * Proof.MlKem.X86.rs6.length + stackUse Impl.Sha3.X86.Stream.absorb + 4)],
        Within r (lay s₀).W ∨ Region.Sub r (lay s₀).STK := fun r hr => by
      rw [absorb_stack, hsp] at hr
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, List.length_cons,
        List.length_nil] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact .inl VG.Proof.MlDsa.X86.Message.w_st
      · rw [VG.Proof.MlDsa.X86.Message.regKS hL]; exact .inl VG.Proof.MlDsa.X86.Message.w_ks
      · exact .inr (VG.Proof.MlDsa.X86.Message.kb_stk hL (by omega))
      · exact .inr (VG.Proof.MlDsa.X86.Message.b40 hL)
    obtain ⟨s₂, m₂, g₂, post⟩ := post
    refine hQ s₀ s s' h₀ ha ⟨hL, hc1.keep hL e₁ e₂ (e₃ .esp (by decide)) (e₃ .esi (by decide)) fr kb⟩ ?_
      (fun msg hm hp => ?_) ?_
    · rw [← hs.2.mem]
      refine fr.sub fun r hr => ?_
      rw [absorb_stack, hsp] at hr
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, List.length_cons,
        List.length_nil] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · rw [VG.Proof.MlDsa.X86.Message.regKS hL]; exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, VG.Proof.MlDsa.X86.Message.kb_stk hL (by omega)⟩
      · exact ⟨_, by simp, VG.Proof.MlDsa.X86.Message.b40 hL⟩
    · have := absorb_post hsp a hE hnl (by decide) (by omega) (VG.Proof.MlDsa.X86.Message.kbufs hL).bS (kD.sub_left (VG.Proof.MlDsa.X86.Message.b40 hL))
        ⟨s₂, m₂, post⟩ msg (by rw [hs.2.mem]; exact hm) hp
      rwa [hs.2.mem] at this
    · rw [← g₂]; exact VG.Proof.MlDsa.X86.Message.absorb_eax hsp a hE hnl (by omega) post

/-! ## Padding -/

/-- The arguments of a call of `vg_keccak_pad`. -/
abbrev padArgs (pos : VG.Impl.MlDsa.X86.Message.Arg) : List (Reg × VG.Impl.MlDsa.X86.Message.Arg) :=
  [(.edx, pos), (.eax, .off VG.Impl.MlDsa.X86.Message.oST), (.ecx, .imm 136), (.ebx, .imm 0x1f), (.edi, .off oKS)]

/-- A call of `vg_keccak_pad` at the position `q s₀`, with the suffix of SHAKE. -/
theorem kpad_piece (pos : VG.Impl.MlDsa.X86.Message.Arg) (q : State → Nat) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (VG.Impl.MlDsa.X86.Message.setArgs (VG.Proof.MlDsa.X86.Message.padArgs pos))) ht).isSome = true)
    (hpub : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → VG.Proof.MlDsa.X86.Message.PubL (lay s₀) (lay s₀'))
    (hA : ∀ s₀ s, Pre s₀ → A s₀ s → VG.Proof.MlDsa.X86.Message.CtxO lay s₀ s)
    (hok : ∀ s₀, Pre s₀ → VG.Proof.MlDsa.X86.Message.argsOk (lay s₀).nA (VG.Proof.MlDsa.X86.Message.padArgs pos) = true)
    (hv : ∀ s₀ s, Pre s₀ → A s₀ s → pos.val s = BitVec.ofNat 32 (q s₀))
    (hdn : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → q s₀ = q s₀')
    (hb : ∀ s₀ s, Pre s₀ → A s₀ s → q s₀ < 136)
    (hQ : ∀ s₀ s s', Pre s₀ → A s₀ s → VG.Proof.MlDsa.X86.Message.CtxO lay s₀ s' →
      Frame [⟨(lay s₀).ST, 200⟩, ⟨(lay s₀).KS, 640⟩, (lay s₀).STK] s.mem s'.mem →
      (∀ msg, Repr s.mem (lay s₀).ST 136 msg → q s₀ = msg.length % 136 →
        stateAt s'.mem (lay s₀).ST = absorb 136 (pad 136 Spec.Sha3.shakeSuffix msg)) → B s₀ s') :
    Piece Pre Pub A B (kpad pos) := by
  have hargs : ∀ s₀ s s₁, Pre s₀ → A s₀ s → VG.Proof.MlDsa.X86.Message.SetPost (VG.Proof.MlDsa.X86.Message.padArgs pos) s s₁ →
      PadArgs s₁ (lay s₀).X32 ((lay s₀).X32 + BitVec.ofNat 32 200) 136 (q s₀) 0x1f := by
    intro s₀ s s₁ h₀ ha hs
    have hc := (hA s₀ s h₀ ha).ctx
    have e2 := hs.1 (.edx, pos) (by simp)
    have e0 := hs.1 (.eax, .off VG.Impl.MlDsa.X86.Message.oST) (by simp)
    have e1 := hs.1 (.ecx, .imm 136) (by simp)
    have e3 := hs.1 (.ebx, .imm 0x1f) (by simp)
    have e4 := hs.1 (.edi, .off oKS) (by simp)
    simp only [Arg.val, hc.esi, VG.Impl.MlDsa.X86.Message.oST, oKS, VG.Proof.MlDsa.X86.Message.x0'] at e0 e1 e3 e4
    rw [hv s₀ s h₀ ha] at e2
    exact ⟨e0, e1, e2, e3, e4⟩
  refine VG.Proof.MlDsa.X86.Message.argsWith_piece Proof.Sha3.X86.Stream.Pad.pad_verified.1
    Proof.Sha3.X86.Stream.Pad.pad_verified.2.1 pad_nosp (by decide) (by decide) tt hpub hA hok
    (fun _ => [])
    (fun s₀ => [reg32 (lay s₀).X32 200, reg32 ((lay s₀).X32 + BitVec.ofNat 32 200) 640, below (lay s₀).E1 20])
    (fun s₀ s₀' h₀ h₀' hq => ?_) (fun s₀ s h₀ ha => ?_) (fun s₀ s s₁ h₀ ha hs => ?_)
    (fun s₀ s₀' s s' s₁ s₁' h₀ h₀' hq ha ha' hs hs' => ?_) (fun s₀ s s₁ s' h₀ ha hs e₁ e₂ e₃ fr post => ?_)
  · have hp := hpub s₀ s₀' h₀ h₀' hq
    refine ⟨rfl, ?_⟩
    simp only [Lay.E1, hp.x, hp.sp]
  · have := VG.Proof.MlDsa.X86.Message.e40 (hA s₀ s h₀ ha).ok
    rw [pad_stack]; simp only [List.length_cons, List.length_nil]; omega
  · obtain ⟨hL, hc⟩ := hA s₀ s h₀ ha
    have hc1 := SetPost.ctx (hok s₀ h₀) hs hc
    exact pad_pre hc1.esp (hargs s₀ s s₁ h₀ ha hs) (VG.Proof.MlDsa.X86.Message.kbufs hL) (by decide) (hb s₀ s h₀ ha)
      (VG.Proof.MlDsa.X86.Message.withinW hc1 (by have := hL.covX (e := 0) (k := 200) (by omega); rwa [VG.Proof.MlDsa.X86.Message.x0] at this))
      (VG.Proof.MlDsa.X86.Message.withinW hc1 (by rw [VG.Proof.MlDsa.X86.Message.regKS hL]; exact hL.covX (e := 200) (by omega)))
  · have a := hargs s₀ s s₁ h₀ ha hs
    have a' := hargs s₀' s' s₁' h₀' ha' hs'
    have hp := hpub s₀ s₀' h₀ h₀' hq
    rw [← hdn s₀ s₀' h₀ h₀' hq, ← hp.x] at a'
    have hsp : s₁.gpr .esp = s₁'.gpr .esp := by
      rw [hs.esp (hok s₀ h₀), hs'.esp (hok s₀' h₀'), (hA s₀ s h₀ ha).ctx.esp, (hA s₀' s' h₀' ha').ctx.esp,
        Lay.E1, Lay.E1, hp.sp]
    have hE : 40 ≤ (s₁.gpr .esp).toNat := by
      rw [hs.esp (hok s₀ h₀), (hA s₀ s h₀ ha).ctx.esp]; exact VG.Proof.MlDsa.X86.Message.e40 (hA s₀ s h₀ ha).ok
    exact Proof.MlKem.X86.args5_eq hE hsp (Proof.MlKem.X86.padArgs_eq a a') _ _
  · obtain ⟨hL, hc⟩ := hA s₀ s h₀ ha
    have hc1 := SetPost.ctx (hok s₀ h₀) hs hc
    have a := hargs s₀ s s₁ h₀ ha hs
    have hsp : s₁.gpr .esp = (lay s₀).E1 := hc1.esp
    have hE := VG.Proof.MlDsa.X86.Message.e40 hL
    have kb : ∀ r ∈ [reg32 (lay s₀).X32 200, reg32 ((lay s₀).X32 + BitVec.ofNat 32 200) 640, below (lay s₀).E1 20] ++
        [below (s₁.gpr .esp) (4 * Proof.MlKem.X86.rs5.length + stackUse Impl.Sha3.X86.Stream.pad + 4)],
        Within r (lay s₀).W ∨ Region.Sub r (lay s₀).STK := fun r hr => by
      rw [pad_stack, hsp] at hr
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, List.length_cons,
        List.length_nil] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact .inl VG.Proof.MlDsa.X86.Message.w_st
      · rw [VG.Proof.MlDsa.X86.Message.regKS hL]; exact .inl VG.Proof.MlDsa.X86.Message.w_ks
      · exact .inr (VG.Proof.MlDsa.X86.Message.kb_stk hL (by omega))
      · exact .inr (VG.Proof.MlDsa.X86.Message.kb_stk hL (by omega))
    obtain ⟨s₂, m₂, post⟩ := post
    refine hQ s₀ s s' h₀ ha ⟨hL, hc1.keep hL e₁ e₂ (e₃ .esp (by decide)) (e₃ .esi (by decide)) fr kb⟩ ?_
      (fun msg hm hp => ?_)
    · rw [← hs.2.mem]
      refine fr.sub fun r hr => ?_
      rw [pad_stack, hsp] at hr
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, List.length_cons,
        List.length_nil] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · rw [VG.Proof.MlDsa.X86.Message.regKS hL]; exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, VG.Proof.MlDsa.X86.Message.kb_stk hL (by omega)⟩
      · exact ⟨_, by simp, VG.Proof.MlDsa.X86.Message.kb_stk hL (by omega)⟩
    · have := pad_post hsp a hE (by decide) (by have := hb s₀ s h₀ ha; omega) (VG.Proof.MlDsa.X86.Message.kbufs hL).bS ⟨s₂, m₂, post⟩ msg
        (by rw [hs.2.mem]; exact hm) hp
      rw [this]; rfl

/-! ## Squeezing -/

/-- The arguments of a call of `vg_keccak_squeeze`. -/
abbrev sqzArgs : List (Reg × VG.Impl.MlDsa.X86.Message.Arg) :=
  [(.eax, .off VG.Impl.MlDsa.X86.Message.oST), (.ecx, .imm 136), (.edx, .imm 0), (.ebx, .off oMU), (.ebp, .imm 64), (.edi, .off oKS)]

/-- A call of `vg_keccak_squeeze`, of 64 bytes to `μ`. -/
theorem ksqz_piece (hpub : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → VG.Proof.MlDsa.X86.Message.PubL (lay s₀) (lay s₀'))
    (hA : ∀ s₀ s, Pre s₀ → A s₀ s → VG.Proof.MlDsa.X86.Message.CtxO lay s₀ s)
    (hok : ∀ s₀, Pre s₀ → VG.Proof.MlDsa.X86.Message.argsOk (lay s₀).nA VG.Proof.MlDsa.X86.Message.sqzArgs = true)
    (hQ : ∀ s₀ s s', Pre s₀ → A s₀ s → VG.Proof.MlDsa.X86.Message.CtxO lay s₀ s' →
      Frame [⟨(lay s₀).ST, 200⟩, ⟨(lay s₀).MU, 64⟩, ⟨(lay s₀).KS, 640⟩, (lay s₀).STK] s.mem s'.mem →
      bytesAt s'.mem (lay s₀).MU 64 = squeezeFrom 136 (stateAt s.mem (lay s₀).ST) 0 64 → B s₀ s') :
    Piece Pre Pub A B ksqz := by
  have hargs : ∀ s₀ s s₁, Pre s₀ → A s₀ s → VG.Proof.MlDsa.X86.Message.SetPost VG.Proof.MlDsa.X86.Message.sqzArgs s s₁ →
      AbsArgs s₁ (lay s₀).X32 ((lay s₀).X32 + BitVec.ofNat 32 840) ((lay s₀).X32 + BitVec.ofNat 32 200) 136 0 64 := by
    intro s₀ s s₁ h₀ ha hs
    have hc := (hA s₀ s h₀ ha).ctx
    have e0 := hs.1 (.eax, .off VG.Impl.MlDsa.X86.Message.oST) (by simp)
    have e1 := hs.1 (.ecx, .imm 136) (by simp)
    have e2 := hs.1 (.edx, .imm 0) (by simp)
    have e3 := hs.1 (.ebx, .off oMU) (by simp)
    have e4 := hs.1 (.ebp, .imm 64) (by simp)
    have e5 := hs.1 (.edi, .off oKS) (by simp)
    simp only [Arg.val, hc.esi, VG.Impl.MlDsa.X86.Message.oST, oKS, oMU, VG.Proof.MlDsa.X86.Message.x0'] at e0 e1 e2 e3 e4 e5
    exact ⟨e0, e1, e2, e3, e4, e5⟩
  refine VG.Proof.MlDsa.X86.Message.argsWith_piece Proof.Sha3.X86.Stream.Squeeze.squeeze_verified.1
    Proof.Sha3.X86.Stream.Squeeze.squeeze_verified.2.1 squeeze_nosp (by decide) (by decide) (by taint_decide) hpub hA hok
    (fun _ => [])
    (fun s₀ => [reg32 (lay s₀).X32 200, reg32 ((lay s₀).X32 + BitVec.ofNat 32 840) 64,
      reg32 ((lay s₀).X32 + BitVec.ofNat 32 200) 640, below (lay s₀).E1 24])
    (fun s₀ s₀' h₀ h₀' hq => ?_) (fun s₀ s h₀ ha => ?_) (fun s₀ s s₁ h₀ ha hs => ?_)
    (fun s₀ s₀' s s' s₁ s₁' h₀ h₀' hq ha ha' hs hs' => ?_) (fun s₀ s s₁ s' h₀ ha hs e₁ e₂ e₃ fr post => ?_)
  · have hp := hpub s₀ s₀' h₀ h₀' hq
    refine ⟨rfl, ?_⟩
    simp only [Lay.E1, hp.x, hp.sp]
  · have := VG.Proof.MlDsa.X86.Message.e40 (hA s₀ s h₀ ha).ok
    rw [squeeze_stack]; simp only [List.length_cons, List.length_nil]; omega
  · obtain ⟨hL, hc⟩ := hA s₀ s h₀ ha
    have hc1 := SetPost.ctx (hok s₀ h₀) hs hc
    have hX := hL.x32_lt
    exact squeeze_pre hc1.esp (hargs s₀ s s₁ h₀ ha hs) (VG.Proof.MlDsa.X86.Message.kbufs hL) (by rw [hL.x32_toNat (by omega)]; omega)
      (by rw [VG.Proof.MlDsa.X86.Message.regMU hL]; exact VG.Proof.MlDsa.X86.Message.st_mu) (by rw [VG.Proof.MlDsa.X86.Message.regMU hL, VG.Proof.MlDsa.X86.Message.regKS hL]; exact VG.Proof.MlDsa.X86.Message.mu_ks)
      (by rw [VG.Proof.MlDsa.X86.Message.regMU hL]; exact (VG.Proof.MlDsa.X86.Message.k_mu hL).sub_left (VG.Proof.MlDsa.X86.Message.b40 hL)) (by decide) (by decide) (by decide)
      (VG.Proof.MlDsa.X86.Message.withinW hc1 (by have := hL.covX (e := 0) (k := 200) (by omega); rwa [VG.Proof.MlDsa.X86.Message.x0] at this))
      (VG.Proof.MlDsa.X86.Message.withinW hc1 (by rw [VG.Proof.MlDsa.X86.Message.regMU hL]; exact hL.covX (e := 840) (by omega)))
      (VG.Proof.MlDsa.X86.Message.withinW hc1 (by rw [VG.Proof.MlDsa.X86.Message.regKS hL]; exact hL.covX (e := 200) (by omega)))
  · have a := hargs s₀ s s₁ h₀ ha hs
    have a' := hargs s₀' s' s₁' h₀' ha' hs'
    have hp := hpub s₀ s₀' h₀ h₀' hq
    rw [← hp.x] at a'
    have hsp : s₁.gpr .esp = s₁'.gpr .esp := by
      rw [hs.esp (hok s₀ h₀), hs'.esp (hok s₀' h₀'), (hA s₀ s h₀ ha).ctx.esp, (hA s₀' s' h₀' ha').ctx.esp,
        Lay.E1, Lay.E1, hp.sp]
    have hE : 40 ≤ (s₁.gpr .esp).toNat := by
      rw [hs.esp (hok s₀ h₀), (hA s₀ s h₀ ha).ctx.esp]; exact VG.Proof.MlDsa.X86.Message.e40 (hA s₀ s h₀ ha).ok
    exact Proof.MlKem.X86.args6_eq hE hsp (Proof.MlKem.X86.absArgs_eq a a') _ _
  · obtain ⟨hL, hc⟩ := hA s₀ s h₀ ha
    have hc1 := SetPost.ctx (hok s₀ h₀) hs hc
    have a := hargs s₀ s s₁ h₀ ha hs
    have hsp : s₁.gpr .esp = (lay s₀).E1 := hc1.esp
    have hE := VG.Proof.MlDsa.X86.Message.e40 hL
    have kb : ∀ r ∈ [reg32 (lay s₀).X32 200, reg32 ((lay s₀).X32 + BitVec.ofNat 32 840) 64,
        reg32 ((lay s₀).X32 + BitVec.ofNat 32 200) 640, below (lay s₀).E1 24] ++
        [below (s₁.gpr .esp) (4 * Proof.MlKem.X86.rs6.length + stackUse Impl.Sha3.X86.Stream.squeeze + 4)],
        Within r (lay s₀).W ∨ Region.Sub r (lay s₀).STK := fun r hr => by
      rw [squeeze_stack, hsp] at hr
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, List.length_cons,
        List.length_nil] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact .inl VG.Proof.MlDsa.X86.Message.w_st
      · rw [VG.Proof.MlDsa.X86.Message.regMU hL]; exact .inl VG.Proof.MlDsa.X86.Message.w_mu
      · rw [VG.Proof.MlDsa.X86.Message.regKS hL]; exact .inl VG.Proof.MlDsa.X86.Message.w_ks
      · exact .inr (VG.Proof.MlDsa.X86.Message.kb_stk hL (by omega))
      · exact .inr (VG.Proof.MlDsa.X86.Message.b40 hL)
    obtain ⟨s₂, m₂, post⟩ := post
    refine hQ s₀ s s' h₀ ha ⟨hL, hc1.keep hL e₁ e₂ (e₃ .esp (by decide)) (e₃ .esi (by decide)) fr kb⟩ ?_ ?_
    · rw [← hs.2.mem]
      refine fr.sub fun r hr => ?_
      rw [squeeze_stack, hsp] at hr
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, List.length_cons,
        List.length_nil] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · rw [VG.Proof.MlDsa.X86.Message.regMU hL]; exact ⟨_, by simp, fun _ h => h⟩
      · rw [VG.Proof.MlDsa.X86.Message.regKS hL]; exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, VG.Proof.MlDsa.X86.Message.kb_stk hL (by omega)⟩
      · exact ⟨_, by simp, VG.Proof.MlDsa.X86.Message.b40 hL⟩
    · have := (squeeze_post hsp a hE (by decide) (by decide) (by decide) (VG.Proof.MlDsa.X86.Message.kbufs hL).bS ⟨s₂, m₂, post⟩).1
      rw [VG.Proof.MlDsa.X86.Message.mu_eq hL, hs.2.mem] at this
      exact this

end

end VG.Proof.MlDsa.X86.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Message.HashMu`. -/
section

/-!
# ML-DSA on x86 (32-bit), `sign_message` and `verify_message`: `μ` and `tr`

Untrusted: everything here is checked by Lean. In the body, `muHash` leaves
`μ = H(tr ‖ 0 ‖ ctx_len ‖ ctx ‖ M, 64)` at `X + 840` (`muHash_piece`), and
`trHash` leaves `H(pk, 64)` there (`trHash_piece`): from the zeroed state,
each absorb continues the message from the position the previous one
returned, which is public, as the lengths are.
-/

namespace VG.Proof.MlDsa.X86.Message

open VG VG.X86 VG.Impl.MlDsa.X86.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.X86 (Within Piece P0)
open VG.Spec.Sha3 (bytesAt stateAt Repr)
open VG.Spec.MlDsa (Params)

/-- The two bytes `0 ‖ ctx_len` of the formatted message. -/
abbrev hdrBytes (L : VG.Proof.MlDsa.X86.Message.Lay) : List Byte := [0, BitVec.ofNat 8 L.ctxLen.toNat]

theorem ofNat_toNat32 (x : BitVec 32) : BitVec.ofNat 32 x.toNat = x := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt]

theorem ofNat_toNat_eq32 {x : BitVec 32} {n : Nat} (h : x.toNat = n) : x = BitVec.ofNat 32 n := by
  subst h; exact (VG.Proof.MlDsa.X86.Message.ofNat_toNat32 x).symm

/-- The arguments of an absorb are fit, if its data and length are not `eax`. -/
theorem absOk {n : Nat} {src len pos : VG.Impl.MlDsa.X86.Message.Arg} (h1 : src.ok n = true) (h2 : len.ok n = true) (h3 : pos.ok n = true)
    (r1 : src.isRet = false) (r2 : len.isRet = false) : VG.Proof.MlDsa.X86.Message.argsOk n (VG.Proof.MlDsa.X86.Message.absArgs src len pos) = true := by
  simp (config := { decide := true }) [VG.Proof.MlDsa.X86.Message.argsOk, h1, h2, h3, r1, r2]
  exact ⟨rfl, rfl, rfl⟩

theorem padOk {n : Nat} {pos : VG.Impl.MlDsa.X86.Message.Arg} (h : pos.ok n = true) : VG.Proof.MlDsa.X86.Message.argsOk n (VG.Proof.MlDsa.X86.Message.padArgs pos) = true := by
  simp (config := { decide := true }) [VG.Proof.MlDsa.X86.Message.argsOk, h]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem sqzOk {n : Nat} : VG.Proof.MlDsa.X86.Message.argsOk n VG.Proof.MlDsa.X86.Message.sqzArgs = true := by
  simp (config := { decide := true }) [VG.Proof.MlDsa.X86.Message.argsOk]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem argOk {L : VG.Proof.MlDsa.X86.Message.Lay} (hL : L.Ok) {i : Nat} (hi : i < 5) : (Arg.arg i).ok L.nA = true := by
  have := hL.nA5; simp only [Arg.ok, decide_eq_true_eq]; omega

theorem Ctx.arg' {L : VG.Proof.MlDsa.X86.Message.Lay} {m₁ : Mem} {t : State} (hc : VG.Proof.MlDsa.X86.Message.Ctx L m₁ t) (hL : L.Ok) {i : Nat} (hi : i < 5) :
    (Arg.arg i).val t = L.argv.getD i 0 :=
  hc.argV (by have := hL.nA5; omega)

section
variable (lay : State → VG.Proof.MlDsa.X86.Message.Lay) (s₀ : State)

/-- The context string and the message, as on entry. -/
abbrev ctxB : List Byte := bytesAt (P0 s₀).mem ((lay s₀).ctx.setWidth 64) (lay s₀).ctxLen.toNat
abbrev msgB : List Byte := bytesAt (P0 s₀).mem ((lay s₀).msg.setWidth 64) (lay s₀).len.toNat
abbrev keyB : List Byte := bytesAt (P0 s₀).mem ((lay s₀).key.setWidth 64) (lay s₀).keyLen

end

section
variable {Pre : State → Prop} {Pub : State → State → Prop} {lay : State → VG.Proof.MlDsa.X86.Message.Lay} {A : State → State → Prop}

theorem muHash_piece (tr : VG.Impl.MlDsa.X86.Message.Arg) (trp : State → BitVec 32) (trv : State → List Byte)
    {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (VG.Impl.MlDsa.X86.Message.setArgs (VG.Proof.MlDsa.X86.Message.absArgs tr (.imm 64) (.imm 0)))) ht).isSome =
      true)
    (hpub : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → VG.Proof.MlDsa.X86.Message.PubL (lay s₀) (lay s₀'))
    (hA : ∀ s₀ s, Pre s₀ → A s₀ s → VG.Proof.MlDsa.X86.Message.CtxO lay s₀ s)
    (hnA : ∀ s₀, Pre s₀ → 5 ≤ (lay s₀).nA) (hok : ∀ s₀, Pre s₀ → tr.ok (lay s₀).nA = true) (hret : tr.isRet = false)
    (htr : ∀ s₀ s, Pre s₀ → VG.Proof.MlDsa.X86.Message.CtxO lay s₀ s → tr.val s = trp s₀)
    (htp : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → trp s₀ = trp s₀')
    (hv : ∀ s₀ s, Pre s₀ → A s₀ s → bytesAt s.mem ((trp s₀).setWidth 64) 64 = trv s₀)
    (hv' : ∀ s₀, Pre s₀ → (trv s₀).length = 64)
    (hb : ∀ s₀, Pre s₀ → (lay s₀).Ok → (trp s₀).toNat + 64 ≤ 2 ^ 32 ∧
      (∃ R ∈ (lay s₀).rd ++ (lay s₀).wr, Within ⟨(trp s₀).setWidth 64, 64⟩ R) ∧
      Region.Disjoint ⟨(trp s₀).setWidth 64, 64⟩ ⟨(lay s₀).ST, 200⟩ ∧
      Region.Disjoint ⟨(trp s₀).setWidth 64, 64⟩ ⟨(lay s₀).KS, 640⟩ ∧
      (lay s₀).STK.Disjoint ⟨(trp s₀).setWidth 64, 64⟩) :
    Piece Pre Pub A (fun s₀ s => VG.Proof.MlDsa.X86.Message.CtxO lay s₀ s ∧ bytesAt s.mem (lay s₀).MU 64 =
      Spec.MlDsa.H (trv s₀ ++ VG.Proof.MlDsa.X86.Message.hdrBytes (lay s₀) ++ VG.Proof.MlDsa.X86.Message.ctxB lay s₀ ++ VG.Proof.MlDsa.X86.Message.msgB lay s₀) 64) (muHash tr) := by
  -- Zero the state.
  refine Piece.seq (VG.Proof.MlDsa.X86.Message.zeroSt_piece hpub hA (B := fun s₀ s => VG.Proof.MlDsa.X86.Message.CtxO lay s₀ s ∧ stateAt s.mem (lay s₀).ST =
      Spec.Sha3.zero ∧ bytesAt s.mem ((trp s₀).setWidth 64) 64 = trv s₀)
    fun s₀ s s' h₀ ha hc' hf hz => ⟨hc', hz, ?_⟩) ?_
  · obtain ⟨-, -, dS, -, -⟩ := hb s₀ h₀ hc'.ok
    rw [← hv s₀ s h₀ ha]
    exact Proof.MlKem.bytesAt_congr fun i hi =>
      hf.bytes (R := ⟨(trp s₀).setWidth 64, 64⟩) (by simpa using dS) (by show 64 ≤ 2 ^ 64; decide) hi
  -- `tr`.
  refine Piece.seq (VG.Proof.MlDsa.X86.Message.kabs_piece tr (.imm 64) (.imm 0) trp (fun _ => 64) (fun _ => 0) tt hpub (fun _ _ _ h => h.1)
    (fun s₀ h₀ => ?_) (fun s₀ s h₀ h => ⟨htr s₀ s h₀ h.1, rfl, rfl⟩)
    (fun s₀ s₀' h₀ h₀' hq => ⟨htp s₀ s₀' h₀ h₀' hq, rfl, rfl⟩) (fun s₀ s h₀ h => ?_)
    (B := fun s₀ s => VG.Proof.MlDsa.X86.Message.CtxO lay s₀ s ∧ Repr s.mem (lay s₀).ST 136 (trv s₀))
    fun s₀ s s' h₀ h hc' _ hR _ => ⟨hc', ?_⟩) ?_
  · exact VG.Proof.MlDsa.X86.Message.absOk (hok s₀ h₀) rfl rfl hret rfl
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hb s₀ h₀ h.1.ok
    exact ⟨by decide, by decide, h1, h2, h3, h4, h5⟩
  · have := hR [] (Proof.MlKem.repr_nil h.2.1) rfl
    rwa [List.nil_append, h.2.2] at this
  have argA : ∀ s₀, Pre s₀ → ∀ i < 5, (Arg.arg i).ok (lay s₀).nA = true := fun s₀ h₀ i hi => by
    have := hnA s₀ h₀; simp only [Arg.ok, decide_eq_true_eq]; omega
  -- `0 ‖ ctx_len`.
  refine Piece.seq (VG.Proof.MlDsa.X86.Message.kabs_piece (.off oHdr) (.imm 2) (.imm 64) (fun s₀ => (lay s₀).X32 + BitVec.ofNat 32 944)
    (fun _ => 2) (fun _ => 64) (by taint_decide) hpub (fun _ _ _ h => h.1)
    (fun _ _ => VG.Proof.MlDsa.X86.Message.absOk rfl rfl rfl rfl rfl) (fun s₀ s h₀ h => ⟨h.1.ctx.off _, rfl, rfl⟩)
    (fun s₀ s₀' h₀ h₀' hq => ⟨by rw [(hpub s₀ s₀' h₀ h₀' hq).x], rfl, rfl⟩) (fun s₀ s h₀ h => ?_)
    (B := fun s₀ s => VG.Proof.MlDsa.X86.Message.CtxO lay s₀ s ∧ Repr s.mem (lay s₀).ST 136 (trv s₀ ++ VG.Proof.MlDsa.X86.Message.hdrBytes (lay s₀)))
    fun s₀ s s' h₀ h hc' _ hR _ => ⟨hc', ?_⟩) ?_
  · have hL := h.1.ok
    have ehd : ((lay s₀).X32 + BitVec.ofNat 32 944).setWidth 64 = (lay s₀).X + BitVec.ofNat 64 944 :=
      hL.xo (by decide)
    refine ⟨by decide, by decide, by rw [hL.x32_toNat (by decide)]; have := hL.x32_lt; omega,
      by rw [ehd]; exact VG.Proof.MlDsa.X86.Message.cov_x hL (e := 944) (k := 2) (by omega), ?_, ?_, by rw [ehd]; exact hL.stk_x (by omega)⟩
    · rw [ehd]
      have := Offset.disjoint (lay s₀).X (d := 944) (n := 2) (e := 0) (k := 200) (by omega) (by omega) (by omega)
      simpa only [VG.Proof.MlDsa.X86.Message.x0] using this
    · rw [ehd]
      exact Offset.disjoint (lay s₀).X (d := 944) (n := 2) (e := 200) (k := 640) (by omega) (by omega) (by omega)
  · have ehd : ((lay s₀).X32 + BitVec.ofNat 32 944).setWidth 64 = (lay s₀).X + BitVec.ofNat 64 944 :=
      h.1.ok.xo (by decide)
    have := hR _ h.2 (by rw [hv' s₀ h₀])
    rwa [ehd, h.1.ctx.hdr] at this
  -- The context string.
  refine Piece.seq (VG.Proof.MlDsa.X86.Message.kabs_piece (.arg 3) (.arg 4) (.imm 66) (fun s₀ => (lay s₀).ctx)
    (fun s₀ => (lay s₀).ctxLen.toNat) (fun _ => 66) (by taint_decide) hpub (fun _ _ _ h => h.1)
    (fun s₀ h₀ => VG.Proof.MlDsa.X86.Message.absOk (argA s₀ h₀ 3 (by omega)) (argA s₀ h₀ 4 (by omega)) rfl rfl rfl)
    (fun s₀ s h₀ h => ⟨by rw [h.1.ctx.arg' h.1.ok (by omega), h.1.ok.a3],
      by rw [h.1.ctx.arg' h.1.ok (by omega), h.1.ok.a4, VG.Proof.MlDsa.X86.Message.ofNat_toNat32], rfl⟩)
    (fun s₀ s₀' h₀ h₀' hq => ⟨(hpub s₀ s₀' h₀ h₀' hq).ctx, by rw [(hpub s₀ s₀' h₀ h₀' hq).ctxLen], rfl⟩)
    (fun s₀ s h₀ h => ?_)
    (B := fun s₀ s => VG.Proof.MlDsa.X86.Message.CtxO lay s₀ s ∧ Repr s.mem (lay s₀).ST 136 (trv s₀ ++ VG.Proof.MlDsa.X86.Message.hdrBytes (lay s₀) ++ VG.Proof.MlDsa.X86.Message.ctxB lay s₀) ∧
      (s.gpr .eax).toNat = (66 + (lay s₀).ctxLen.toNat) % 136)
    fun s₀ s s' h₀ h hc' _ hR he => ⟨hc', ?_, he⟩) ?_
  · have hL := h.1.ok
    have := hL.ctxLt
    exact ⟨by decide, by omega, hL.nCtx, ⟨(lay s₀).CTX, List.mem_append_left _ hL.inCtx, within_self _⟩,
      by have := hL.x_r hL.xCtx (e := 0) (k := 200) (by omega); simpa only [VG.Proof.MlDsa.X86.Message.x0] using this.symm,
      (hL.x_r hL.xCtx (e := 200) (k := 640) (by omega)).symm, hL.kCtx⟩
  · have hL := h.1.ok
    have := hR _ h.2 (by simp only [List.length_append, hv' s₀ h₀, List.length_cons, List.length_nil])
    rwa [h.1.ctx.bytesAt_eq hL.xCtx hL.kCtx (by have := hL.nCtx; omega)] at this
  -- The message.
  refine Piece.seq (VG.Proof.MlDsa.X86.Message.kabs_piece (.arg 1) (.arg 2) .ret (fun s₀ => (lay s₀).msg)
    (fun s₀ => (lay s₀).len.toNat) (fun s₀ => (66 + (lay s₀).ctxLen.toNat) % 136) (by taint_decide) hpub
    (fun _ _ _ h => h.1)
    (fun s₀ h₀ => VG.Proof.MlDsa.X86.Message.absOk (argA s₀ h₀ 1 (by omega)) (argA s₀ h₀ 2 (by omega)) rfl rfl rfl)
    (fun s₀ s h₀ h => ⟨by rw [h.1.ctx.arg' h.1.ok (by omega), h.1.ok.a1],
      by rw [h.1.ctx.arg' h.1.ok (by omega), h.1.ok.a2, VG.Proof.MlDsa.X86.Message.ofNat_toNat32], VG.Proof.MlDsa.X86.Message.ofNat_toNat_eq32 h.2.2⟩)
    (fun s₀ s₀' h₀ h₀' hq => ⟨(hpub s₀ s₀' h₀ h₀' hq).msg, by rw [(hpub s₀ s₀' h₀ h₀' hq).len],
      by rw [(hpub s₀ s₀' h₀ h₀' hq).ctxLen]⟩)
    (fun s₀ s h₀ h => ?_)
    (B := fun s₀ s => VG.Proof.MlDsa.X86.Message.CtxO lay s₀ s ∧
      Repr s.mem (lay s₀).ST 136 (trv s₀ ++ VG.Proof.MlDsa.X86.Message.hdrBytes (lay s₀) ++ VG.Proof.MlDsa.X86.Message.ctxB lay s₀ ++ VG.Proof.MlDsa.X86.Message.msgB lay s₀) ∧
      (s.gpr .eax).toNat = ((66 + (lay s₀).ctxLen.toNat) % 136 + (lay s₀).len.toNat) % 136)
    fun s₀ s s' h₀ h hc' _ hR he => ⟨hc', ?_, he⟩) ?_
  · have hL := h.1.ok
    exact ⟨Nat.mod_lt _ (by decide), (lay s₀).len.isLt, hL.nMsg,
      ⟨(lay s₀).MSG, List.mem_append_left _ hL.inMsg, within_self _⟩,
      by have := hL.x_r hL.xMsg (e := 0) (k := 200) (by omega); simpa only [VG.Proof.MlDsa.X86.Message.x0] using this.symm,
      (hL.x_r hL.xMsg (e := 200) (k := 640) (by omega)).symm, hL.kMsg⟩
  · have hL := h.1.ok
    have := hR _ h.2.1 (by
      simp only [List.length_append, hv' s₀ h₀, List.length_cons, List.length_nil, Proof.MlKem.bytesAt_length])
    rwa [h.1.ctx.bytesAt_eq hL.xMsg hL.kMsg (by have := hL.nMsg; omega)] at this
  -- Pad and squeeze.
  refine Piece.seq (VG.Proof.MlDsa.X86.Message.kpad_piece .ret (fun s₀ => ((66 + (lay s₀).ctxLen.toNat) % 136 + (lay s₀).len.toNat) % 136)
    (by taint_decide) hpub (fun _ _ _ h => h.1) (fun _ _ => VG.Proof.MlDsa.X86.Message.padOk rfl) (fun s₀ s h₀ h => VG.Proof.MlDsa.X86.Message.ofNat_toNat_eq32 h.2.2)
    (fun s₀ s₀' h₀ h₀' hq => by rw [(hpub s₀ s₀' h₀ h₀' hq).ctxLen, (hpub s₀ s₀' h₀ h₀' hq).len])
    (fun _ _ _ _ => Nat.mod_lt _ (by decide))
    (B := fun s₀ s => VG.Proof.MlDsa.X86.Message.CtxO lay s₀ s ∧ stateAt s.mem (lay s₀).ST = Spec.Sha3.absorb 136
      (Spec.Sha3.pad 136 Spec.Sha3.shakeSuffix (trv s₀ ++ VG.Proof.MlDsa.X86.Message.hdrBytes (lay s₀) ++ VG.Proof.MlDsa.X86.Message.ctxB lay s₀ ++ VG.Proof.MlDsa.X86.Message.msgB lay s₀)))
    fun s₀ s s' h₀ h hc' _ hS => ⟨hc', hS _ h.2.1 ?_⟩) ?_
  · simp only [List.length_append, hv' s₀ h₀, List.length_cons, List.length_nil, Proof.MlKem.bytesAt_length]
    omega
  exact VG.Proof.MlDsa.X86.Message.ksqz_piece hpub (fun _ _ _ h => h.1) (fun _ _ => VG.Proof.MlDsa.X86.Message.sqzOk) fun s₀ s s' h₀ h hc' _ hm =>
    ⟨hc', by rw [hm, h.2, Spec.MlDsa.H, Proof.MlKem.shake256_eq]⟩

/-! ## `tr = H(pk, 64)` -/

theorem trHash_piece {p : Params} (hpub : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → VG.Proof.MlDsa.X86.Message.PubL (lay s₀) (lay s₀'))
    (hA : ∀ s₀ s, Pre s₀ → A s₀ s → VG.Proof.MlDsa.X86.Message.CtxO lay s₀ s) (hnA : ∀ s₀, Pre s₀ → 5 ≤ (lay s₀).nA)
    (hk : ∀ s₀, Pre s₀ → (lay s₀).keyLen = p.pkLen) {ht₁ ht₂ : Taint.Hint VG.X86.Taint.T}
    (tt₁ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (VG.Impl.MlDsa.X86.Message.setArgs (VG.Proof.MlDsa.X86.Message.absArgs (.arg 0) (.imm p.pkLen) (.imm 0)))) ht₁).isSome =
      true)
    (tt₂ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (VG.Impl.MlDsa.X86.Message.setArgs (VG.Proof.MlDsa.X86.Message.padArgs (.imm (p.pkLen % 136))))) ht₂).isSome =
      true) :
    Piece Pre Pub A (fun s₀ s => VG.Proof.MlDsa.X86.Message.CtxO lay s₀ s ∧ bytesAt s.mem (lay s₀).MU 64 = Spec.MlDsa.H (VG.Proof.MlDsa.X86.Message.keyB lay s₀) 64)
      (VG.Impl.MlDsa.X86.Message.trHash p) := by
  refine Piece.seq (VG.Proof.MlDsa.X86.Message.zeroSt_piece hpub hA (B := fun s₀ s => VG.Proof.MlDsa.X86.Message.CtxO lay s₀ s ∧ stateAt s.mem (lay s₀).ST =
      Spec.Sha3.zero) fun s₀ s s' h₀ ha hc' _ hz => ⟨hc', hz⟩) ?_
  refine Piece.seq (VG.Proof.MlDsa.X86.Message.kabs_piece (.arg 0) (.imm p.pkLen) (.imm 0) (fun s₀ => (lay s₀).key)
    (fun s₀ => (lay s₀).keyLen) (fun _ => 0) tt₁ hpub (fun _ _ _ h => h.1)
    (fun s₀ h₀ => VG.Proof.MlDsa.X86.Message.absOk (by have := hnA s₀ h₀; simp only [Arg.ok, decide_eq_true_eq]; omega) rfl rfl rfl rfl)
    (fun s₀ s h₀ h => ⟨by rw [h.1.ctx.arg' h.1.ok (by omega), h.1.ok.a0], by rw [hk s₀ h₀]; rfl, rfl⟩)
    (fun s₀ s₀' h₀ h₀' hq => ⟨(hpub s₀ s₀' h₀ h₀' hq).key, by rw [hk s₀ h₀, hk s₀' h₀'], rfl⟩)
    (fun s₀ s h₀ h => ?_)
    (B := fun s₀ s => VG.Proof.MlDsa.X86.Message.CtxO lay s₀ s ∧ Repr s.mem (lay s₀).ST 136 (VG.Proof.MlDsa.X86.Message.keyB lay s₀))
    fun s₀ s s' h₀ h hc' _ hR _ => ⟨hc', ?_⟩) ?_
  · have hL := h.1.ok
    have := hL.hKey
    exact ⟨by decide, by omega, hL.nKey, ⟨(lay s₀).KEY, List.mem_append_left _ hL.inKey, within_self _⟩,
      by have := hL.x_r hL.xKey (e := 0) (k := 200) (by omega); simpa only [VG.Proof.MlDsa.X86.Message.x0] using this.symm,
      (hL.x_r hL.xKey (e := 200) (k := 640) (by omega)).symm, hL.kKey⟩
  · have hL := h.1.ok
    have := hR [] (Proof.MlKem.repr_nil h.2) rfl
    rwa [List.nil_append, h.1.ctx.bytesAt_eq hL.xKey hL.kKey (by have := hL.nKey; omega)] at this
  refine Piece.seq (VG.Proof.MlDsa.X86.Message.kpad_piece (.imm (p.pkLen % 136)) (fun _ => p.pkLen % 136) tt₂ hpub
    (fun _ _ _ h => h.1) (fun _ _ => VG.Proof.MlDsa.X86.Message.padOk rfl) (fun _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
    (fun _ _ _ _ => Nat.mod_lt _ (by decide))
    (B := fun s₀ s => VG.Proof.MlDsa.X86.Message.CtxO lay s₀ s ∧ stateAt s.mem (lay s₀).ST = Spec.Sha3.absorb 136
      (Spec.Sha3.pad 136 Spec.Sha3.shakeSuffix (VG.Proof.MlDsa.X86.Message.keyB lay s₀)))
    fun s₀ s s' h₀ h hc' _ hS => ⟨hc', hS _ h.2 (by rw [Proof.MlKem.bytesAt_length, hk s₀ h₀])⟩) ?_
  exact VG.Proof.MlDsa.X86.Message.ksqz_piece hpub (fun _ _ _ h => h.1) (fun _ _ => VG.Proof.MlDsa.X86.Message.sqzOk) fun s₀ s s' h₀ h hc' _ hm =>
    ⟨hc', by rw [hm, h.2, Spec.MlDsa.H, Proof.MlKem.shake256_eq]⟩

end

end VG.Proof.MlDsa.X86.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Message.Pre`. -/
section

/-!
# ML-DSA on x86 (32-bit), `sign_message` and `verify_message`: the preconditions and the layouts

Untrusted: everything here is checked by Lean. The preconditions of
`signMessageContract p X86.abi 136` and `verifyMessageContract p X86.abi
132`, spelled out (`SPre`, `VPre`), the layouts of runs from states
satisfying them (`slay`, `vlay`), and what the contracts' public data say of
two runs (`spub_of`, `vpub_of`).
-/

namespace VG.Proof.MlDsa.X86.Message

open VG VG.X86 VG.Impl.MlDsa.X86.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.X86 (E0 P0)
open VG.Spec.MlDsa

/-- The parameter sets. -/
def params : List Params := [mlDsa44, mlDsa65, mlDsa87]

/-- The size of `scratch` in bytes. -/
abbrev mScrLen (p : Params) : Nat := messageScratchWords p * 8

theorem mScr_eq (p : Params) : VG.Proof.MlDsa.X86.Message.mScrLen p = oE p + 1024 := by
  simp only [VG.Proof.MlDsa.X86.Message.mScrLen, messageScratchWords, oE]; omega

theorem skLen_ge {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86.Message.params) : 128 ≤ p.skLen ∧ p.skLen < 2 ^ 16 := by
  simp only [VG.Proof.MlDsa.X86.Message.params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> decide

theorem pkLen_ge {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86.Message.params) : 128 ≤ p.pkLen ∧ p.pkLen < 2 ^ 16 := by
  simp only [VG.Proof.MlDsa.X86.Message.params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> decide

section
variable (s : State)

/-- Argument `i`, a pointer to `n` bytes. -/
abbrev aR (i n : Nat) : Region := ⟨(arg s i).setWidth 64, n⟩
abbrev msgRg : Region := ⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩
abbrev ctxRg : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
/-- The `n` bytes of arguments. -/
abbrev sArgs (n : Nat) : Region := ⟨argAddr s 0, n⟩
/-- The return address. -/
abbrev sRet : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
/-- The `n` bytes of stack the contract gives. -/
abbrev sStk (n : Nat) : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 n, n⟩

end

theorem stk_eq {s : State} {n : Nat} (h : n ≤ (s.gpr .esp).toNat) : VG.Proof.MlDsa.X86.Message.sStk s n = below (s.gpr .esp) n := by
  simp only [VG.Proof.MlDsa.X86.Message.sStk, below]; rw [Taint.sub_setWidth h]

theorem args_eq (s : State) (n : Nat) : VG.Proof.MlDsa.X86.Message.sArgs s n = ⟨((s.gpr .esp) + BitVec.ofNat 32 4).setWidth 64, n⟩ := rfl

/-! ## Signing -/

/-- The precondition of `signMessageContract p X86.abi 136`. -/
structure SPre (p : Params) (s : State) : Prop where
  sp : 136 ≤ (s.gpr .esp).toNat
  spA : (s.gpr .esp).toNat + 4 + 32 ≤ 2 ^ 32
  rd : s.rd = [VG.Proof.MlDsa.X86.Message.aR s 0 p.skLen, VG.Proof.MlDsa.X86.Message.msgRg s, VG.Proof.MlDsa.X86.Message.ctxRg s, VG.Proof.MlDsa.X86.Message.aR s 5 32]
  wr : s.wr = [VG.Proof.MlDsa.X86.Message.aR s 6 p.sigLen, VG.Proof.MlDsa.X86.Message.aR s 7 (VG.Proof.MlDsa.X86.Message.mScrLen p), VG.Proof.MlDsa.X86.Message.sArgs s 32]
  skSig : (VG.Proof.MlDsa.X86.Message.aR s 0 p.skLen).Disjoint (VG.Proof.MlDsa.X86.Message.aR s 6 p.sigLen)
  skScr : (VG.Proof.MlDsa.X86.Message.aR s 0 p.skLen).Disjoint (VG.Proof.MlDsa.X86.Message.aR s 7 (VG.Proof.MlDsa.X86.Message.mScrLen p))
  skArgs : (VG.Proof.MlDsa.X86.Message.aR s 0 p.skLen).Disjoint (VG.Proof.MlDsa.X86.Message.sArgs s 32)
  msgSig : (VG.Proof.MlDsa.X86.Message.msgRg s).Disjoint (VG.Proof.MlDsa.X86.Message.aR s 6 p.sigLen)
  msgScr : (VG.Proof.MlDsa.X86.Message.msgRg s).Disjoint (VG.Proof.MlDsa.X86.Message.aR s 7 (VG.Proof.MlDsa.X86.Message.mScrLen p))
  msgArgs : (VG.Proof.MlDsa.X86.Message.msgRg s).Disjoint (VG.Proof.MlDsa.X86.Message.sArgs s 32)
  ctxSig : (VG.Proof.MlDsa.X86.Message.ctxRg s).Disjoint (VG.Proof.MlDsa.X86.Message.aR s 6 p.sigLen)
  ctxScr : (VG.Proof.MlDsa.X86.Message.ctxRg s).Disjoint (VG.Proof.MlDsa.X86.Message.aR s 7 (VG.Proof.MlDsa.X86.Message.mScrLen p))
  ctxArgs : (VG.Proof.MlDsa.X86.Message.ctxRg s).Disjoint (VG.Proof.MlDsa.X86.Message.sArgs s 32)
  rndSig : (VG.Proof.MlDsa.X86.Message.aR s 5 32).Disjoint (VG.Proof.MlDsa.X86.Message.aR s 6 p.sigLen)
  rndScr : (VG.Proof.MlDsa.X86.Message.aR s 5 32).Disjoint (VG.Proof.MlDsa.X86.Message.aR s 7 (VG.Proof.MlDsa.X86.Message.mScrLen p))
  rndArgs : (VG.Proof.MlDsa.X86.Message.aR s 5 32).Disjoint (VG.Proof.MlDsa.X86.Message.sArgs s 32)
  sigScr : (VG.Proof.MlDsa.X86.Message.aR s 6 p.sigLen).Disjoint (VG.Proof.MlDsa.X86.Message.aR s 7 (VG.Proof.MlDsa.X86.Message.mScrLen p))
  sigArgs : (VG.Proof.MlDsa.X86.Message.aR s 6 p.sigLen).Disjoint (VG.Proof.MlDsa.X86.Message.sArgs s 32)
  scrArgs : (VG.Proof.MlDsa.X86.Message.aR s 7 (VG.Proof.MlDsa.X86.Message.mScrLen p)).Disjoint (VG.Proof.MlDsa.X86.Message.sArgs s 32)
  rSk : (VG.Proof.MlDsa.X86.Message.sRet s).Disjoint (VG.Proof.MlDsa.X86.Message.aR s 0 p.skLen)
  rMsg : (VG.Proof.MlDsa.X86.Message.sRet s).Disjoint (VG.Proof.MlDsa.X86.Message.msgRg s)
  rCtx : (VG.Proof.MlDsa.X86.Message.sRet s).Disjoint (VG.Proof.MlDsa.X86.Message.ctxRg s)
  rRnd : (VG.Proof.MlDsa.X86.Message.sRet s).Disjoint (VG.Proof.MlDsa.X86.Message.aR s 5 32)
  rSig : (VG.Proof.MlDsa.X86.Message.sRet s).Disjoint (VG.Proof.MlDsa.X86.Message.aR s 6 p.sigLen)
  rScr : (VG.Proof.MlDsa.X86.Message.sRet s).Disjoint (VG.Proof.MlDsa.X86.Message.aR s 7 (VG.Proof.MlDsa.X86.Message.mScrLen p))
  rArgs : (VG.Proof.MlDsa.X86.Message.sRet s).Disjoint (VG.Proof.MlDsa.X86.Message.sArgs s 32)
  kSk : (VG.Proof.MlDsa.X86.Message.sStk s 136).Disjoint (VG.Proof.MlDsa.X86.Message.aR s 0 p.skLen)
  kMsg : (VG.Proof.MlDsa.X86.Message.sStk s 136).Disjoint (VG.Proof.MlDsa.X86.Message.msgRg s)
  kCtx : (VG.Proof.MlDsa.X86.Message.sStk s 136).Disjoint (VG.Proof.MlDsa.X86.Message.ctxRg s)
  kRnd : (VG.Proof.MlDsa.X86.Message.sStk s 136).Disjoint (VG.Proof.MlDsa.X86.Message.aR s 5 32)
  kSig : (VG.Proof.MlDsa.X86.Message.sStk s 136).Disjoint (VG.Proof.MlDsa.X86.Message.aR s 6 p.sigLen)
  kScr : (VG.Proof.MlDsa.X86.Message.sStk s 136).Disjoint (VG.Proof.MlDsa.X86.Message.aR s 7 (VG.Proof.MlDsa.X86.Message.mScrLen p))
  kArgs : (VG.Proof.MlDsa.X86.Message.sStk s 136).Disjoint (VG.Proof.MlDsa.X86.Message.sArgs s 32)
  nSk : (arg s 0).toNat + p.skLen ≤ 2 ^ 32
  nMsg : (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32
  nCtx : (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32
  nRnd : (arg s 5).toNat + 32 ≤ 2 ^ 32
  nSig : (arg s 6).toNat + p.sigLen ≤ 2 ^ 32
  nScr : (arg s 7).toNat + VG.Proof.MlDsa.X86.Message.mScrLen p ≤ 2 ^ 32

theorem sPre_of {p : Params} {s : State} (h : (signMessageContract p X86.abi 136).pre s) : VG.Proof.MlDsa.X86.Message.SPre p s := by
  sig_pre [signMessageContract, signMessageSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39⟩

/-- The layout of a run of `sign_message` from `s`. -/
def slay (p : Params) (s : State) : VG.Proof.MlDsa.X86.Message.Lay where
  SP := s.gpr .esp
  N := 136
  nA := 8
  key := arg s 0
  keyLen := p.skLen
  msg := arg s 1
  len := arg s 2
  ctx := arg s 3
  ctxLen := arg s 4
  rnd := arg s 5
  sig := arg s 6
  scr := arg s 7
  scrLen := VG.Proof.MlDsa.X86.Message.mScrLen p
  E := oE p
  argv := [arg s 0, arg s 1, arg s 2, arg s 3, arg s 4, arg s 5, arg s 6, arg s 7]
  rd := s.rd
  wr := s.wr

theorem slay_ok {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86.Message.params) {s : State} (h : VG.Proof.MlDsa.X86.Message.SPre p s) (h8 : (arg s 4).toNat < 256) :
    (VG.Proof.MlDsa.X86.Message.slay p s).Ok := by
  have hk := VG.Proof.MlDsa.X86.Message.stk_eq (s := s) (n := 136) h.sp
  refine ⟨h8, by show oE p + 1024 ≤ VG.Proof.MlDsa.X86.Message.mScrLen p; rw [VG.Proof.MlDsa.X86.Message.mScr_eq], VG.Proof.MlDsa.X86.Message.skLen_ge hp, by show 56 ≤ 136; decide, h.sp,
    by show (s.gpr .esp).toNat + 4 + 4 * 8 ≤ _; have := h.spA; omega, h.nScr, by simp [VG.Proof.MlDsa.X86.Message.slay, h.wr], by simp [VG.Proof.MlDsa.X86.Message.slay, h.rd],
    by simp [VG.Proof.MlDsa.X86.Message.slay, h.rd], by simp [VG.Proof.MlDsa.X86.Message.slay, h.rd], h.skScr.symm, h.msgScr.symm, h.ctxScr.symm, ?_, ?_,
    h.scrArgs.symm, by show _ ∈ s.wr; rw [h.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)),
    rfl, by show 8 ≤ 8; decide, by show 5 ≤ 8; decide, rfl, rfl, rfl, rfl, rfl, h.nSk, h.nMsg, h.nCtx⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    show (below (s.gpr .esp) 136).Disjoint r
    rw [← hk]
    rcases hr with rfl | rfl | rfl | rfl | rfl
    exacts [h.kScr, h.kSk, h.kMsg, h.kCtx, h.kArgs]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [h.rScr, h.rArgs]

/-! ## Verification -/

/-- The precondition of `verifyMessageContract p X86.abi 132`. -/
structure VPre (p : Params) (s : State) : Prop where
  sp : 132 ≤ (s.gpr .esp).toNat
  spA : (s.gpr .esp).toNat + 4 + 28 ≤ 2 ^ 32
  rd : s.rd = [VG.Proof.MlDsa.X86.Message.aR s 0 p.pkLen, VG.Proof.MlDsa.X86.Message.msgRg s, VG.Proof.MlDsa.X86.Message.ctxRg s, VG.Proof.MlDsa.X86.Message.aR s 5 p.sigLen]
  wr : s.wr = [VG.Proof.MlDsa.X86.Message.aR s 6 (VG.Proof.MlDsa.X86.Message.mScrLen p), VG.Proof.MlDsa.X86.Message.sArgs s 28]
  pkScr : (VG.Proof.MlDsa.X86.Message.aR s 0 p.pkLen).Disjoint (VG.Proof.MlDsa.X86.Message.aR s 6 (VG.Proof.MlDsa.X86.Message.mScrLen p))
  pkArgs : (VG.Proof.MlDsa.X86.Message.aR s 0 p.pkLen).Disjoint (VG.Proof.MlDsa.X86.Message.sArgs s 28)
  msgScr : (VG.Proof.MlDsa.X86.Message.msgRg s).Disjoint (VG.Proof.MlDsa.X86.Message.aR s 6 (VG.Proof.MlDsa.X86.Message.mScrLen p))
  msgArgs : (VG.Proof.MlDsa.X86.Message.msgRg s).Disjoint (VG.Proof.MlDsa.X86.Message.sArgs s 28)
  ctxScr : (VG.Proof.MlDsa.X86.Message.ctxRg s).Disjoint (VG.Proof.MlDsa.X86.Message.aR s 6 (VG.Proof.MlDsa.X86.Message.mScrLen p))
  ctxArgs : (VG.Proof.MlDsa.X86.Message.ctxRg s).Disjoint (VG.Proof.MlDsa.X86.Message.sArgs s 28)
  sigScr : (VG.Proof.MlDsa.X86.Message.aR s 5 p.sigLen).Disjoint (VG.Proof.MlDsa.X86.Message.aR s 6 (VG.Proof.MlDsa.X86.Message.mScrLen p))
  sigArgs : (VG.Proof.MlDsa.X86.Message.aR s 5 p.sigLen).Disjoint (VG.Proof.MlDsa.X86.Message.sArgs s 28)
  scrArgs : (VG.Proof.MlDsa.X86.Message.aR s 6 (VG.Proof.MlDsa.X86.Message.mScrLen p)).Disjoint (VG.Proof.MlDsa.X86.Message.sArgs s 28)
  rPk : (VG.Proof.MlDsa.X86.Message.sRet s).Disjoint (VG.Proof.MlDsa.X86.Message.aR s 0 p.pkLen)
  rMsg : (VG.Proof.MlDsa.X86.Message.sRet s).Disjoint (VG.Proof.MlDsa.X86.Message.msgRg s)
  rCtx : (VG.Proof.MlDsa.X86.Message.sRet s).Disjoint (VG.Proof.MlDsa.X86.Message.ctxRg s)
  rSig : (VG.Proof.MlDsa.X86.Message.sRet s).Disjoint (VG.Proof.MlDsa.X86.Message.aR s 5 p.sigLen)
  rScr : (VG.Proof.MlDsa.X86.Message.sRet s).Disjoint (VG.Proof.MlDsa.X86.Message.aR s 6 (VG.Proof.MlDsa.X86.Message.mScrLen p))
  rArgs : (VG.Proof.MlDsa.X86.Message.sRet s).Disjoint (VG.Proof.MlDsa.X86.Message.sArgs s 28)
  kPk : (VG.Proof.MlDsa.X86.Message.sStk s 132).Disjoint (VG.Proof.MlDsa.X86.Message.aR s 0 p.pkLen)
  kMsg : (VG.Proof.MlDsa.X86.Message.sStk s 132).Disjoint (VG.Proof.MlDsa.X86.Message.msgRg s)
  kCtx : (VG.Proof.MlDsa.X86.Message.sStk s 132).Disjoint (VG.Proof.MlDsa.X86.Message.ctxRg s)
  kSig : (VG.Proof.MlDsa.X86.Message.sStk s 132).Disjoint (VG.Proof.MlDsa.X86.Message.aR s 5 p.sigLen)
  kScr : (VG.Proof.MlDsa.X86.Message.sStk s 132).Disjoint (VG.Proof.MlDsa.X86.Message.aR s 6 (VG.Proof.MlDsa.X86.Message.mScrLen p))
  kArgs : (VG.Proof.MlDsa.X86.Message.sStk s 132).Disjoint (VG.Proof.MlDsa.X86.Message.sArgs s 28)
  nPk : (arg s 0).toNat + p.pkLen ≤ 2 ^ 32
  nMsg : (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32
  nCtx : (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32
  nSig : (arg s 5).toNat + p.sigLen ≤ 2 ^ 32
  nScr : (arg s 6).toNat + VG.Proof.MlDsa.X86.Message.mScrLen p ≤ 2 ^ 32

theorem vPre_of {p : Params} {s : State} (h : (verifyMessageContract p X86.abi 132).pre s) : VG.Proof.MlDsa.X86.Message.VPre p s := by
  sig_pre [verifyMessageContract, verifyMessageSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30⟩

/-- The layout of a run of `verify_message` from `s` (`sig` in the place of `rnd` too). -/
def vlay (p : Params) (s : State) : VG.Proof.MlDsa.X86.Message.Lay where
  SP := s.gpr .esp
  N := 132
  nA := 7
  key := arg s 0
  keyLen := p.pkLen
  msg := arg s 1
  len := arg s 2
  ctx := arg s 3
  ctxLen := arg s 4
  rnd := arg s 5
  sig := arg s 5
  scr := arg s 6
  scrLen := VG.Proof.MlDsa.X86.Message.mScrLen p
  E := oE p
  argv := [arg s 0, arg s 1, arg s 2, arg s 3, arg s 4, arg s 5, arg s 6]
  rd := s.rd
  wr := s.wr

theorem vlay_ok {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86.Message.params) {s : State} (h : VG.Proof.MlDsa.X86.Message.VPre p s) (h8 : (arg s 4).toNat < 256) :
    (VG.Proof.MlDsa.X86.Message.vlay p s).Ok := by
  have hk := VG.Proof.MlDsa.X86.Message.stk_eq (s := s) (n := 132) h.sp
  refine ⟨h8, by show oE p + 1024 ≤ VG.Proof.MlDsa.X86.Message.mScrLen p; rw [VG.Proof.MlDsa.X86.Message.mScr_eq], VG.Proof.MlDsa.X86.Message.pkLen_ge hp, by show 56 ≤ 132; decide, h.sp,
    by show (s.gpr .esp).toNat + 4 + 4 * 7 ≤ _; have := h.spA; omega, h.nScr, by simp [VG.Proof.MlDsa.X86.Message.vlay, h.wr], by simp [VG.Proof.MlDsa.X86.Message.vlay, h.rd],
    by simp [VG.Proof.MlDsa.X86.Message.vlay, h.rd], by simp [VG.Proof.MlDsa.X86.Message.vlay, h.rd], h.pkScr.symm, h.msgScr.symm, h.ctxScr.symm, ?_, ?_,
    h.scrArgs.symm, by show _ ∈ s.wr; rw [h.wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _),
    rfl, by show 7 ≤ 8; decide, by show 5 ≤ 7; decide, rfl, rfl, rfl, rfl, rfl, h.nPk, h.nMsg, h.nCtx⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    show (below (s.gpr .esp) 132).Disjoint r
    rw [← hk]
    rcases hr with rfl | rfl | rfl | rfl | rfl
    exacts [h.kScr, h.kPk, h.kMsg, h.kCtx, h.kArgs]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [h.rScr, h.rArgs]

end VG.Proof.MlDsa.X86.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Message.Shapes`. -/
section

/-!
# ML-DSA on x86 (32-bit), `sign_message` and `verify_message`: the layouts' shapes

Untrusted: everything here is checked by Lean. The contracts' public data,
spelled out (`SPub`, `VPub`), and the layouts of `sign_message` and
`verify_message` (`slay`, `vlay`) meet what the proofs of the check, the
entry and the hashes need (`sShape`, `vShape`).
-/

namespace VG.Proof.MlDsa.X86.Message

open VG VG.X86 VG.Impl.MlDsa.X86.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.X86 (E0 P0)
open VG.Spec.Sha3 (bytesAt)
open VG.Spec.MlDsa

/-- The public data of `signMessageContract p X86.abi 136`. -/
structure SPub (p : Params) (s s' : State) : Prop where
  esp : s.gpr .esp = s'.gpr .esp
  leak : signMessageLeak p (bytesAt s.mem ((arg s 0).setWidth 64) p.skLen)
      (bytesAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat) (bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat)
      (bytesAt s.mem ((arg s 5).setWidth 64) 32) =
    signMessageLeak p (bytesAt s'.mem ((arg s' 0).setWidth 64) p.skLen)
      (bytesAt s'.mem ((arg s' 1).setWidth 64) (arg s' 2).toNat)
      (bytesAt s'.mem ((arg s' 3).setWidth 64) (arg s' 4).toNat) (bytesAt s'.mem ((arg s' 5).setWidth 64) 32)
  args : ∀ i < 8, arg s i = arg s' i

theorem spub_of {p : Params} {s s' : State} (h : (signMessageContract p X86.abi 136).pub s s') : VG.Proof.MlDsa.X86.Message.SPub p s s' := by
  sig_pub [signMessageContract, signMessageSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨e₁, e₂, a0, a1, a2, a3, a4, a5, a6, a7⟩ := h
  refine ⟨e₁, e₂, fun i hi => ?_⟩
  match i, hi with
  | 0, _ => exact a0
  | 1, _ => exact a1
  | 2, _ => exact a2
  | 3, _ => exact a3
  | 4, _ => exact a4
  | 5, _ => exact a5
  | 6, _ => exact a6
  | 7, _ => exact a7

/-- The public data of `verifyMessageContract p X86.abi 132`. -/
structure VPub (p : Params) (s s' : State) : Prop where
  esp : s.gpr .esp = s'.gpr .esp
  leak : leakBytes (bytesAt s.mem ((arg s 0).setWidth 64) p.pkLen ++
      bytesAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat ++ bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat ++
      bytesAt s.mem ((arg s 5).setWidth 64) p.sigLen) =
    leakBytes (bytesAt s'.mem ((arg s' 0).setWidth 64) p.pkLen ++
      bytesAt s'.mem ((arg s' 1).setWidth 64) (arg s' 2).toNat ++
      bytesAt s'.mem ((arg s' 3).setWidth 64) (arg s' 4).toNat ++ bytesAt s'.mem ((arg s' 5).setWidth 64) p.sigLen)
  args : ∀ i < 7, arg s i = arg s' i

theorem vpub_of {p : Params} {s s' : State} (h : (verifyMessageContract p X86.abi 132).pub s s') : VG.Proof.MlDsa.X86.Message.VPub p s s' := by
  sig_pub [verifyMessageContract, verifyMessageSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨e₁, e₂, a0, a1, a2, a3, a4, a5, a6⟩ := h
  refine ⟨e₁, e₂, fun i hi => ?_⟩
  match i, hi with
  | 0, _ => exact a0
  | 1, _ => exact a1
  | 2, _ => exact a2
  | 3, _ => exact a3
  | 4, _ => exact a4
  | 5, _ => exact a5
  | 6, _ => exact a6

/-- The leaf's frame, below the stack pointer on entry. -/
theorem frame_eq {s : State} (h : 16 ≤ (s.gpr .esp).toNat) :
    (⟨(E0 s).setWidth 64 - 16#64, 16⟩ : Region) = below (s.gpr .esp) 16 := by
  simp only [below]; rw [Taint.sub_setWidth h]

theorem sShape {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86.Message.params) : VG.Proof.MlDsa.X86.Message.Shape (VG.Proof.MlDsa.X86.Message.SPre p) (VG.Proof.MlDsa.X86.Message.SPub p) (VG.Proof.MlDsa.X86.Message.slay p) 7 p where
  sp _ _ := rfl
  rd _ _ := rfl
  wr _ _ := rfl
  argv s₀ _ i hi := by
    match i, hi with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | 3, _ => rfl
    | 4, _ => rfl
    | 5, _ => rfl
    | 6, _ => rfl
    | 7, _ => rfl
  ctxLen _ _ := rfl
  scr _ _ := rfl
  siLt _ _ := by show 7 < 8; decide
  E _ _ := rfl
  ok _ h₀ h8 := VG.Proof.MlDsa.X86.Message.slay_ok hp h₀ h8
  e16 s₀ h₀ := ⟨by show 16 ≤ (s₀.gpr .esp).toNat; have := h₀.sp; omega,
    by show (s₀.gpr .esp).toNat + 4 ≤ _; have := h₀.spA; omega⟩
  fit _ h₀ := by show _ + 4 + 4 * 8 ≤ _; have := h₀.spA; omega
  fd s₀ h₀ := by
    rw [VG.Proof.MlDsa.X86.Message.frame_eq (by have := h₀.sp; omega)]
    exact (VG.Proof.MlDsa.X86.Message.stk_eq h₀.sp ▸ h₀.kArgs).sub_left (below_sub (by omega) h₀.sp)
  ain _ h₀ := List.mem_append_right _ (by
    rw [h₀.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  n5 _ _ := by show 5 ≤ 8; decide
  pubE _ _ _ _ hq := hq.esp
  pubA _ _ _ _ hq := ⟨hq.args 4 (by decide), hq.args 7 (by decide)⟩
  pubL _ _ _ _ hq := ⟨hq.esp, by simp only [VG.Proof.MlDsa.X86.Message.slay, hq.args 0 (by decide), hq.args 1 (by decide),
      hq.args 2 (by decide), hq.args 3 (by decide), hq.args 4 (by decide), hq.args 5 (by decide),
      hq.args 6 (by decide), hq.args 7 (by decide)], by simp only [Lay.X32, VG.Proof.MlDsa.X86.Message.slay, hq.args 7 (by decide)], rfl,
    hq.args 0 (by decide), hq.args 1 (by decide), hq.args 2 (by decide), hq.args 3 (by decide),
    hq.args 4 (by decide)⟩

theorem vShape {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86.Message.params) : VG.Proof.MlDsa.X86.Message.Shape (VG.Proof.MlDsa.X86.Message.VPre p) (VG.Proof.MlDsa.X86.Message.VPub p) (VG.Proof.MlDsa.X86.Message.vlay p) 6 p where
  sp _ _ := rfl
  rd _ _ := rfl
  wr _ _ := rfl
  argv s₀ _ i hi := by
    match i, hi with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | 3, _ => rfl
    | 4, _ => rfl
    | 5, _ => rfl
    | 6, _ => rfl
  ctxLen _ _ := rfl
  scr _ _ := rfl
  siLt _ _ := by show 6 < 7; decide
  E _ _ := rfl
  ok _ h₀ h8 := VG.Proof.MlDsa.X86.Message.vlay_ok hp h₀ h8
  e16 s₀ h₀ := ⟨by show 16 ≤ (s₀.gpr .esp).toNat; have := h₀.sp; omega,
    by show (s₀.gpr .esp).toNat + 4 ≤ _; have := h₀.spA; omega⟩
  fit _ h₀ := by show _ + 4 + 4 * 7 ≤ _; have := h₀.spA; omega
  fd s₀ h₀ := by
    rw [VG.Proof.MlDsa.X86.Message.frame_eq (by have := h₀.sp; omega)]
    exact (VG.Proof.MlDsa.X86.Message.stk_eq h₀.sp ▸ h₀.kArgs).sub_left (below_sub (by omega) h₀.sp)
  ain _ h₀ := List.mem_append_right _ (by
    rw [h₀.wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _))
  n5 _ _ := by show 5 ≤ 7; decide
  pubE _ _ _ _ hq := hq.esp
  pubA _ _ _ _ hq := ⟨hq.args 4 (by decide), hq.args 6 (by decide)⟩
  pubL _ _ _ _ hq := ⟨hq.esp, by simp only [VG.Proof.MlDsa.X86.Message.vlay, hq.args 0 (by decide), hq.args 1 (by decide),
      hq.args 2 (by decide), hq.args 3 (by decide), hq.args 4 (by decide), hq.args 5 (by decide),
      hq.args 6 (by decide)], by simp only [Lay.X32, VG.Proof.MlDsa.X86.Message.vlay, hq.args 6 (by decide)], rfl,
    hq.args 0 (by decide), hq.args 1 (by decide), hq.args 2 (by decide), hq.args 3 (by decide),
    hq.args 4 (by decide)⟩

end VG.Proof.MlDsa.X86.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Message.SignCall`. -/
section

/-!
# ML-DSA on x86 (32-bit), `sign_message`: the call of the signing function on `μ`

Untrusted: everything here is checked by Lean. With `μ` at `X + 840`, the
call of `vg_mldsa*_sign(sk, μ, rnd, sig, scratch)` (`signCall_piece`): its
arguments in `eax`, `ecx`, `edx`, `ebx` and `edi`, pushed; its precondition
(`signContract p X86.abi 96`), from `sign_message`'s; what it leaks, which
is what `sign_message` may (`leak_eq`); and its result, which is
`sign_message`'s.
-/

namespace VG.Proof.MlDsa.X86.Message

open VG VG.X86 VG.Impl.MlDsa.X86.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.X86 (Only Piece P0 E0 frameR retR LeafEnd)
open VG.Proof.MlKem.X86.Top (entry_regions entry_self covers_of)
open VG.Spec.Sha3 (bytesAt)
open VG.Spec.MlDsa

/-- A signing function on `μ`, as `sign_message` calls it. -/
structure SignFn (p : Params) (c : Prog isa) : Prop where
  ver : Verified X86.target c (signContract p X86.abi 96)
  nosp : NoSp c
  su : stackUse c ≤ 96

/-- The size of the working space of the functions on `μ`. -/
abbrev sScr (p : Params) : Nat := scratchWords p * 8

/-- The arguments of the call of the signing function on `μ`. -/
abbrev signArgs : List (Reg × VG.Impl.MlDsa.X86.Message.Arg) :=
  [(.eax, .arg 0), (.ecx, .off oMU), (.edx, .arg 5), (.ebx, .arg 6), (.edi, .arg 7)]

section
variable (p : Params) (s₀ : State)

/-- The message representative of the run from `s₀`. -/
abbrev sMu : List Byte :=
  VG.Spec.MlDsa.H (bytesAt s₀.mem ((arg s₀ 0 + BitVec.ofNat 32 64).setWidth 64) 64 ++ VG.Proof.MlDsa.X86.Message.hdrBytes (VG.Proof.MlDsa.X86.Message.slay p s₀) ++
    bytesAt s₀.mem ((arg s₀ 3).setWidth 64) (arg s₀ 4).toNat ++ bytesAt s₀.mem ((arg s₀ 1).setWidth 64) (arg s₀ 2).toNat)
    64

/-- The regions the signing function on `μ` is given. -/
abbrev sRd : List Region :=
  [⟨(arg s₀ 0).setWidth 64, p.skLen⟩, ⟨((VG.Proof.MlDsa.X86.Message.slay p s₀).X32 + BitVec.ofNat 32 840).setWidth 64, 64⟩,
    ⟨(arg s₀ 5).setWidth 64, 32⟩]
abbrev sWr : List Region :=
  [⟨(arg s₀ 6).setWidth 64, p.sigLen⟩, ⟨(arg s₀ 7).setWidth 64, VG.Proof.MlDsa.X86.Message.sScr p⟩, below (VG.Proof.MlDsa.X86.Message.slay p s₀).E1 20]

/-- What `sign_message` changes: `scratch`, the stack, and `sig`. -/
abbrev sW : List Region := [(VG.Proof.MlDsa.X86.Message.slay p s₀).SC, (VG.Proof.MlDsa.X86.Message.slay p s₀).STK, ⟨(arg s₀ 6).setWidth 64, p.sigLen⟩]

/-- The result. -/
def SB (s : State) : Prop :=
  (arg s₀ 4).toNat < 256 ∧
    Outcome (fun b => signMu p b (bytesAt s₀.mem ((arg s₀ 0).setWidth 64) p.skLen) (VG.Proof.MlDsa.X86.Message.sMu p s₀)
      (bytesAt s₀.mem ((arg s₀ 5).setWidth 64) 32)) (s.gpr .eax) (bytesAt s.mem ((arg s₀ 6).setWidth 64) p.sigLen)

end

section
variable {p : Params}

/-- What `sign_message` leaks is what the signing function on `μ` leaks, for
the `μ` it computes. -/
theorem leak_eq {s₀ : State} (h₀ : VG.Proof.MlDsa.X86.Message.SPre p s₀) (h8 : (arg s₀ 4).toNat < 256) (hk : 128 ≤ p.skLen) :
    signMessageLeak p (bytesAt s₀.mem ((arg s₀ 0).setWidth 64) p.skLen)
        (bytesAt s₀.mem ((arg s₀ 1).setWidth 64) (arg s₀ 2).toNat)
        (bytesAt s₀.mem ((arg s₀ 3).setWidth 64) (arg s₀ 4).toNat) (bytesAt s₀.mem ((arg s₀ 5).setWidth 64) 32) =
      signLeak p (bytesAt s₀.mem ((arg s₀ 0).setWidth 64) p.skLen) (VG.Proof.MlDsa.X86.Message.sMu p s₀)
        (bytesAt s₀.mem ((arg s₀ 5).setWidth 64) 32) := by
  have := h₀.nSk
  rw [signMessageLeak, formatMessage_some (by rw [Proof.MlKem.bytesAt_length]; exact h8)]
  simp only [messageRep, skTr, Proof.MlKem.bytesAt_length]
  rw [Proof.MlKem.bytesAt_slice _ _ (by omega)]
  simp only [VG.Proof.MlDsa.X86.Message.sMu, VG.Proof.MlDsa.X86.Message.hdrBytes, VG.Proof.MlDsa.X86.Message.slay, List.append_assoc]
  rw [Proof.MlKem.X86.ea_off (by omega)]


/-- The values of the arguments. -/
theorem signArgs_val {s₀ s s₁ : State} (hc : VG.Proof.MlDsa.X86.Message.CtxO (VG.Proof.MlDsa.X86.Message.slay p) s₀ s) (hs : VG.Proof.MlDsa.X86.Message.SetPost VG.Proof.MlDsa.X86.Message.signArgs s s₁) :
    s₁.gpr .eax = arg s₀ 0 ∧ s₁.gpr .ecx = (VG.Proof.MlDsa.X86.Message.slay p s₀).X32 + BitVec.ofNat 32 840 ∧ s₁.gpr .edx = arg s₀ 5 ∧
      s₁.gpr .ebx = arg s₀ 6 ∧ s₁.gpr .edi = arg s₀ 7 := by
  have h8 : ∀ {i}, i < 8 → i < (VG.Proof.MlDsa.X86.Message.slay p s₀).nA := fun h => h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hs.1 (.eax, .arg 0) (by simp), hc.ctx.argV (h8 (by decide))]; rfl
  · rw [hs.1 (.ecx, .off oMU) (by simp), hc.ctx.off]; rfl
  · rw [hs.1 (.edx, .arg 5) (by simp), hc.ctx.argV (h8 (by decide))]; rfl
  · rw [hs.1 (.ebx, .arg 6) (by simp), hc.ctx.argV (h8 (by decide))]; rfl
  · rw [hs.1 (.edi, .arg 7) (by simp), hc.ctx.argV (h8 (by decide))]; rfl

theorem signArgs_ok : VG.Proof.MlDsa.X86.Message.argsOk 8 VG.Proof.MlDsa.X86.Message.signArgs = true := by decide

/-- The facts about regions the call needs. -/
structure SRegs (p : Params) (s₀ : State) : Prop where
  hE : 120 ≤ (VG.Proof.MlDsa.X86.Message.slay p s₀).E1.toNat
  scrSub : Region.Sub ⟨(arg s₀ 7).setWidth 64, VG.Proof.MlDsa.X86.Message.sScr p⟩ (VG.Proof.MlDsa.X86.Message.slay p s₀).SC
  argsSub : Region.Sub (below (VG.Proof.MlDsa.X86.Message.slay p s₀).E1 20) (VG.Proof.MlDsa.X86.Message.slay p s₀).STK
  muSub : Region.Sub ⟨((VG.Proof.MlDsa.X86.Message.slay p s₀).X32 + BitVec.ofNat 32 840).setWidth 64, 64⟩ (VG.Proof.MlDsa.X86.Message.slay p s₀).SC
  kSk : (VG.Proof.MlDsa.X86.Message.slay p s₀).STK.Disjoint ⟨(arg s₀ 0).setWidth 64, p.skLen⟩
  kMu : (VG.Proof.MlDsa.X86.Message.slay p s₀).STK.Disjoint ⟨((VG.Proof.MlDsa.X86.Message.slay p s₀).X32 + BitVec.ofNat 32 840).setWidth 64, 64⟩
  kRnd : (VG.Proof.MlDsa.X86.Message.slay p s₀).STK.Disjoint ⟨(arg s₀ 5).setWidth 64, 32⟩
  kSig : (VG.Proof.MlDsa.X86.Message.slay p s₀).STK.Disjoint ⟨(arg s₀ 6).setWidth 64, p.sigLen⟩
  kScr : (VG.Proof.MlDsa.X86.Message.slay p s₀).STK.Disjoint ⟨(arg s₀ 7).setWidth 64, VG.Proof.MlDsa.X86.Message.sScr p⟩
  muScr : Region.Disjoint ⟨((VG.Proof.MlDsa.X86.Message.slay p s₀).X32 + BitVec.ofNat 32 840).setWidth 64, 64⟩ ⟨(arg s₀ 7).setWidth 64, VG.Proof.MlDsa.X86.Message.sScr p⟩

theorem sregs {s₀ : State} (h₀ : VG.Proof.MlDsa.X86.Message.SPre p s₀) (hL : (VG.Proof.MlDsa.X86.Message.slay p s₀).Ok) : VG.Proof.MlDsa.X86.Message.SRegs p s₀ := by
  have hsp := h₀.sp
  have hE : 120 ≤ (VG.Proof.MlDsa.X86.Message.slay p s₀).E1.toNat := by
    show 120 ≤ (s₀.gpr .esp - BitVec.ofNat 32 16).toNat
    rw [sub_toNat (by omega)]; omega
  have hk : ∀ {R : Region}, (VG.Proof.MlDsa.X86.Message.sStk s₀ 136).Disjoint R → (VG.Proof.MlDsa.X86.Message.slay p s₀).STK.Disjoint R := fun h =>
    (VG.Proof.MlDsa.X86.Message.stk_eq hsp ▸ h).sub_left hL.stk_sub
  have scrSub : Region.Sub ⟨(arg s₀ 7).setWidth 64, VG.Proof.MlDsa.X86.Message.sScr p⟩ (VG.Proof.MlDsa.X86.Message.slay p s₀).SC :=
    (within_base _ (by show VG.Proof.MlDsa.X86.Message.sScr p ≤ VG.Proof.MlDsa.X86.Message.mScrLen p; simp only [VG.Proof.MlDsa.X86.Message.sScr, VG.Proof.MlDsa.X86.Message.mScrLen, messageScratchWords]; omega)).sub
  have muSub : Region.Sub ⟨((VG.Proof.MlDsa.X86.Message.slay p s₀).X32 + BitVec.ofNat 32 840).setWidth 64, 64⟩ (VG.Proof.MlDsa.X86.Message.slay p s₀).SC := by
    rw [VG.Proof.MlDsa.X86.Message.mu_eq hL]; exact hL.sub_sc (e := 840) (k := 64) (by omega)
  refine ⟨hE, scrSub, below_sub (by show 20 ≤ 136 - 16; decide) (by show 136 - 16 ≤ _; omega), muSub, hk h₀.kSk, by rw [VG.Proof.MlDsa.X86.Message.mu_eq hL]; exact VG.Proof.MlDsa.X86.Message.k_mu hL, hk h₀.kRnd,
    hk h₀.kSig, hL.kSC.sub_right scrSub, ?_⟩
  have hx := hL.x_eq
  have := h₀.nScr
  have := VG.Proof.MlDsa.X86.Message.mScr_eq p
  have e : ((VG.Proof.MlDsa.X86.Message.slay p s₀).X32 + BitVec.ofNat 32 840).setWidth 64 =
      (arg s₀ 7).setWidth 64 + BitVec.ofNat 64 (oE p + 840) := by
    rw [VG.Proof.MlDsa.X86.Message.mu_eq hL, Lay.MU, hx, add_add]; rfl
  rw [e]
  have d := Offset.disjoint ((arg s₀ 7).setWidth 64) (d := oE p + 840) (n := 64) (e := 0) (k := VG.Proof.MlDsa.X86.Message.sScr p)
    (.inr (by simp only [oE, VG.Proof.MlDsa.X86.Message.sScr]; omega)) (by omega) (by simp only [oE, VG.Proof.MlDsa.X86.Message.sScr] at *; omega)
  rwa [BitVec.add_zero] at d

/-- The callee's precondition. -/
theorem sign_callPre {s₀ s s₁ : State} (h₀ : VG.Proof.MlDsa.X86.Message.SPre p s₀) (hc : VG.Proof.MlDsa.X86.Message.CtxO (VG.Proof.MlDsa.X86.Message.slay p) s₀ s)
    (hs : VG.Proof.MlDsa.X86.Message.SetPost VG.Proof.MlDsa.X86.Message.signArgs s s₁) : CallPre (signContract p X86.abi 96) Proof.MlKem.X86.rs5 (VG.Proof.MlDsa.X86.Message.sRd p s₀) (VG.Proof.MlDsa.X86.Message.sWr p s₀) s₁ := by
  have hL := hc.ok
  have hc1 := SetPost.ctx VG.Proof.MlDsa.X86.Message.signArgs_ok hs hc.ctx
  obtain ⟨v0, v1, v2, v3, v4⟩ := VG.Proof.MlDsa.X86.Message.signArgs_val hc hs
  have R := VG.Proof.MlDsa.X86.Message.sregs h₀ hL
  have hE := R.hE
  have hsp1 : s₁.gpr .esp = (VG.Proof.MlDsa.X86.Message.slay p s₀).E1 := hc1.esp
  have fit : 4 * Proof.MlKem.X86.rs5.length + 4 ≤ (s₁.gpr .esp).toNat := by
    rw [hsp1]; simp only [List.length_cons, List.length_nil]; omega
  have a0 : arg (pushed Proof.MlKem.X86.rs5 s₁).callEntry 0 = arg s₀ 0 := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact v0
  have a1 : arg (pushed Proof.MlKem.X86.rs5 s₁).callEntry 1 = (VG.Proof.MlDsa.X86.Message.slay p s₀).X32 + BitVec.ofNat 32 840 := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact v1
  have a2 : arg (pushed Proof.MlKem.X86.rs5 s₁).callEntry 2 = arg s₀ 5 := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact v2
  have a3 : arg (pushed Proof.MlKem.X86.rs5 s₁).callEntry 3 = arg s₀ 6 := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact v3
  have a4 : arg (pushed Proof.MlKem.X86.rs5 s₁).callEntry 4 = arg s₀ 7 := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact v4
  have eA : argAddr (pushed Proof.MlKem.X86.rs5 s₁).callEntry 0 = ((VG.Proof.MlDsa.X86.Message.slay p s₀).E1 - BitVec.ofNat 32 20).setWidth 64 := by
    rw [callEntry_argAddr0, hsp1]; rfl
  have eSp : (pushed Proof.MlKem.X86.rs5 s₁).callEntry.gpr .esp = (VG.Proof.MlDsa.X86.Message.slay p s₀).E1 - BitVec.ofNat 32 (4 * 5 + 4) := by
    rw [callEntry_esp', hsp1]; rfl
  have cv := covers_of (s := s₁) (n := 5) (rd := VG.Proof.MlDsa.X86.Message.sRd p s₀) (wr := VG.Proof.MlDsa.X86.Message.sWr p s₀) (fun r hr => ?_) fun r hr => ?_
  rotate_left
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact VG.Proof.MlDsa.X86.Message.withinRW hc1 ⟨_, List.mem_append_left _ hL.inKey, within_self _⟩
    · exact VG.Proof.MlDsa.X86.Message.withinRW hc1 (by rw [VG.Proof.MlDsa.X86.Message.mu_eq hL]; exact VG.Proof.MlDsa.X86.Message.cov_x hL (e := 840) (k := 64) (by omega))
    · exact VG.Proof.MlDsa.X86.Message.withinRW hc1 ⟨_, List.mem_append_left _ (by show _ ∈ s₀.rd; rw [h₀.rd]; simp), within_self _⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr (VG.Proof.MlDsa.X86.Message.withinW hc1 ⟨_, by show _ ∈ s₀.wr; rw [h₀.wr]; simp, within_self _⟩)
    · exact .inr (VG.Proof.MlDsa.X86.Message.withinW hc1 ⟨_, hL.inSC, within_base _ (by show VG.Proof.MlDsa.X86.Message.sScr p ≤ VG.Proof.MlDsa.X86.Message.mScrLen p; simp only [VG.Proof.MlDsa.X86.Message.sScr, VG.Proof.MlDsa.X86.Message.mScrLen, messageScratchWords]; omega)⟩)
    · exact .inl (by rw [hsp1])
  refine ⟨?_, cv.1, cv.2⟩
  obtain ⟨rSk₁, rSk₂, rSk₃⟩ := entry_regions (E := (VG.Proof.MlDsa.X86.Message.slay p s₀).E1) (k := 5) (K := 96) (by omega) R.kSk
  obtain ⟨rMu₁, rMu₂, rMu₃⟩ := entry_regions (E := (VG.Proof.MlDsa.X86.Message.slay p s₀).E1) (k := 5) (K := 96) (by omega) R.kMu
  obtain ⟨rRnd₁, rRnd₂, rRnd₃⟩ := entry_regions (E := (VG.Proof.MlDsa.X86.Message.slay p s₀).E1) (k := 5) (K := 96) (by omega) R.kRnd
  obtain ⟨rSig₁, rSig₂, rSig₃⟩ := entry_regions (E := (VG.Proof.MlDsa.X86.Message.slay p s₀).E1) (k := 5) (K := 96) (by omega) R.kSig
  obtain ⟨rScr₁, rScr₂, rScr₃⟩ := entry_regions (E := (VG.Proof.MlDsa.X86.Message.slay p s₀).E1) (k := 5) (K := 96) (by omega) R.kScr
  obtain ⟨rA₂, rA₃⟩ := entry_self (E := (VG.Proof.MlDsa.X86.Message.slay p s₀).E1) (k := 5) (K := 96) (by omega)
  generalize he : (pushed Proof.MlKem.X86.rs5 s₁).callEntry = e at a0 a1 a2 a3 a4 eA eSp ⊢
  sig_pre [signContract, signSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  subst he
  simp only [arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, a4, eA, eSp]
  have hX := hL.x32_lt
  refine ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := (VG.Proof.MlDsa.X86.Message.slay p s₀).E1.isLt; omega,
    trivial, trivial, h₀.skSig, h₀.skScr.sub_right R.scrSub, rSk₁, h₀.sigScr.symm.sub_left R.muSub, R.muScr, rMu₁,
    h₀.rndSig, h₀.rndScr.sub_right R.scrSub, rRnd₁, h₀.sigScr.sub_right R.scrSub, rSig₁, rScr₁,
    rSk₂, rMu₂, rRnd₂, rSig₂, rScr₂, rA₂, rSk₃, rMu₃, rRnd₃, rSig₃, rScr₃, rA₃, h₀.nSk,
    by rw [hL.x32_toNat (by omega)]; omega, h₀.nRnd, h₀.nSig,
    by have := h₀.nScr; simp only [VG.Proof.MlDsa.X86.Message.mScrLen, messageScratchWords] at this ⊢; omega⟩

/-- What the signing function on `μ` sees on entry. -/
structure SView (p : Params) (s₀ s₁ : State) : Prop where
  a0 : arg (pushed Proof.MlKem.X86.rs5 s₁).callEntry 0 = arg s₀ 0
  a1 : arg (pushed Proof.MlKem.X86.rs5 s₁).callEntry 1 = (VG.Proof.MlDsa.X86.Message.slay p s₀).X32 + BitVec.ofNat 32 840
  a2 : arg (pushed Proof.MlKem.X86.rs5 s₁).callEntry 2 = arg s₀ 5
  a3 : arg (pushed Proof.MlKem.X86.rs5 s₁).callEntry 3 = arg s₀ 6
  a4 : arg (pushed Proof.MlKem.X86.rs5 s₁).callEntry 4 = arg s₀ 7
  esp : (pushed Proof.MlKem.X86.rs5 s₁).callEntry.gpr .esp = (VG.Proof.MlDsa.X86.Message.slay p s₀).E1 - BitVec.ofNat 32 (4 * 5 + 4)
  bSk : bytesAt (pushed Proof.MlKem.X86.rs5 s₁).callEntry.mem ((arg s₀ 0).setWidth 64) p.skLen =
    bytesAt s₀.mem ((arg s₀ 0).setWidth 64) p.skLen
  bMu : bytesAt (pushed Proof.MlKem.X86.rs5 s₁).callEntry.mem (((VG.Proof.MlDsa.X86.Message.slay p s₀).X32 + BitVec.ofNat 32 840).setWidth 64) 64 =
    VG.Proof.MlDsa.X86.Message.sMu p s₀
  bRnd : bytesAt (pushed Proof.MlKem.X86.rs5 s₁).callEntry.mem ((arg s₀ 5).setWidth 64) 32 =
    bytesAt s₀.mem ((arg s₀ 5).setWidth 64) 32

theorem sign_view {s₀ s s₁ : State} (h₀ : VG.Proof.MlDsa.X86.Message.SPre p s₀) (hc : VG.Proof.MlDsa.X86.Message.CtxO (VG.Proof.MlDsa.X86.Message.slay p) s₀ s)
    (hμ : bytesAt s.mem (VG.Proof.MlDsa.X86.Message.slay p s₀).MU 64 = VG.Proof.MlDsa.X86.Message.sMu p s₀) (hs : VG.Proof.MlDsa.X86.Message.SetPost VG.Proof.MlDsa.X86.Message.signArgs s s₁) : VG.Proof.MlDsa.X86.Message.SView p s₀ s₁ := by
  have hL := hc.ok
  have hc1 := SetPost.ctx VG.Proof.MlDsa.X86.Message.signArgs_ok hs hc.ctx
  obtain ⟨v0, v1, v2, v3, v4⟩ := VG.Proof.MlDsa.X86.Message.signArgs_val hc hs
  have R := VG.Proof.MlDsa.X86.Message.sregs h₀ hL
  have hE := R.hE
  have hsp1 : s₁.gpr .esp = (VG.Proof.MlDsa.X86.Message.slay p s₀).E1 := hc1.esp
  have fit : 4 * Proof.MlKem.X86.rs5.length + 4 ≤ (s₁.gpr .esp).toNat := by
    rw [hsp1]; simp only [List.length_cons, List.length_nil]; omega
  have fr := callEntry_frame fit (by decide : Reg.esp ∉ Proof.MlKem.X86.rs5)
  rw [hsp1] at fr
  have b24 : Region.Sub (below (VG.Proof.MlDsa.X86.Message.slay p s₀).E1 (4 * Proof.MlKem.X86.rs5.length + 4)) (VG.Proof.MlDsa.X86.Message.slay p s₀).STK :=
    below_sub (by show 24 ≤ 136 - 16; decide) (by show 136 - 16 ≤ _; omega)
  -- Bytes apart from the stack the call uses, as on entry.
  have ent : ∀ {R : Region}, (VG.Proof.MlDsa.X86.Message.slay p s₀).STK.Disjoint R → R.len ≤ 2 ^ 64 →
      bytesAt (pushed Proof.MlKem.X86.rs5 s₁).callEntry.mem R.base R.len = bytesAt s₁.mem R.base R.len :=
    fun {R} hR hn => Proof.MlKem.bytesAt_congr fun _ hi => fr.bytes (R := R) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hR.sub_left b24).symm) hn hi
  have hsp := h₀.sp
  have p0 : ∀ {R : Region}, (VG.Proof.MlDsa.X86.Message.sStk s₀ 136).Disjoint R → (VG.Proof.MlDsa.X86.Message.slay p s₀).SC.Disjoint R → R.len ≤ 2 ^ 64 →
      bytesAt s₁.mem R.base R.len = bytesAt s₀.mem R.base R.len := fun {R} hk hx hn => by
    have hf := pushed_frame (rs := Impl.MlKem.X86.saveRegs) (s := s₀) (by decide) (by show 16 ≤ _; omega)
    rw [hs.2.mem, hc.ctx.bytesAt_eq hx ((VG.Proof.MlDsa.X86.Message.stk_eq hsp ▸ hk).sub_left hL.stk_sub) hn]
    exact Proof.MlKem.bytesAt_congr fun _ hi => hf.bytes (R := R) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((VG.Proof.MlDsa.X86.Message.stk_eq hsp ▸ hk).sub_left (below_sub (by decide) hsp)).symm) hn hi
  refine ⟨by rw [callEntry_arg fit (by decide) (by decide)]; exact v0,
    by rw [callEntry_arg fit (by decide) (by decide)]; exact v1,
    by rw [callEntry_arg fit (by decide) (by decide)]; exact v2,
    by rw [callEntry_arg fit (by decide) (by decide)]; exact v3,
    by rw [callEntry_arg fit (by decide) (by decide)]; exact v4,
    by rw [callEntry_esp', hsp1]; rfl, ?_, ?_, ?_⟩
  · rw [ent (R := ⟨_, p.skLen⟩) R.kSk (by show p.skLen ≤ 2 ^ 64; have := h₀.nSk; omega)]
    exact p0 (R := ⟨_, p.skLen⟩) h₀.kSk h₀.skScr.symm (by show p.skLen ≤ 2 ^ 64; have := h₀.nSk; omega)
  · rw [ent (R := ⟨_, 64⟩) R.kMu (by show 64 ≤ 2 ^ 64; decide), hs.2.mem, VG.Proof.MlDsa.X86.Message.mu_eq hL]; exact hμ
  · rw [ent (R := ⟨_, 32⟩) R.kRnd (by show 32 ≤ 2 ^ 64; decide)]
    exact p0 (R := ⟨_, 32⟩) h₀.kRnd h₀.rndScr.symm (by show 32 ≤ 2 ^ 64; decide)

/-- The call of the signing function on `μ`. -/
theorem signCall_piece (hp : p ∈ VG.Proof.MlDsa.X86.Message.params) {n : String} {f : Prog isa} (hf : VG.Proof.MlDsa.X86.Message.SignFn p f) :
    Piece (VG.Proof.MlDsa.X86.Message.SPre p) (VG.Proof.MlDsa.X86.Message.SPub p) (fun s₀ s => VG.Proof.MlDsa.X86.Message.CtxO (VG.Proof.MlDsa.X86.Message.slay p) s₀ s ∧ bytesAt s.mem (VG.Proof.MlDsa.X86.Message.slay p s₀).MU 64 = VG.Proof.MlDsa.X86.Message.sMu p s₀)
      (fun s₀ s => LeafEnd s₀ (VG.Proof.MlDsa.X86.Message.sW p s₀) s ∧ VG.Proof.MlDsa.X86.Message.SB p s₀ s)
      (.seq (.block (VG.Impl.MlDsa.X86.Message.setArgs VG.Proof.MlDsa.X86.Message.signArgs)) (Impl.MlKem.X86.callRet rs5 n f)) := by
  refine VG.Proof.MlDsa.X86.Message.argsRet_piece hf.ver.1 hf.ver.2.1 hf.nosp (by decide) (by decide) (by taint_decide) (VG.Proof.MlDsa.X86.Message.sShape hp).pubL
    (fun _ _ _ h => h.1) (fun _ _ => by show VG.Proof.MlDsa.X86.Message.argsOk 8 VG.Proof.MlDsa.X86.Message.signArgs = true; decide) (VG.Proof.MlDsa.X86.Message.sRd p) (VG.Proof.MlDsa.X86.Message.sWr p)
    (fun s₀ s₀' h₀ h₀' hq => ?_) (fun s₀ s h₀ ha => ?_) (fun s₀ s s₁ h₀ ha hs => ?_)
    (fun s₀ s₀' s s' s₁ s₁' h₀ h₀' hq ha ha' hs hs' => ?_) (fun s₀ s s₁ s' h₀ ha hs e₁ e₂ e₃ fr post => ?_)
  · refine ⟨?_, ?_⟩
    · simp only [VG.Proof.MlDsa.X86.Message.sRd, Lay.X32, VG.Proof.MlDsa.X86.Message.slay, hq.args 0 (by decide), hq.args 5 (by decide), hq.args 7 (by decide)]
    · simp only [VG.Proof.MlDsa.X86.Message.sWr, Lay.E1, VG.Proof.MlDsa.X86.Message.slay, hq.esp, hq.args 6 (by decide), hq.args 7 (by decide)]
  · have := hf.su
    have := h₀.sp
    show _ ≤ (s₀.gpr .esp - BitVec.ofNat 32 16).toNat
    rw [sub_toNat (by omega)]
    simp only [List.length_cons, List.length_nil]
    omega
  · exact VG.Proof.MlDsa.X86.Message.sign_callPre h₀ ha.1 hs
  · obtain ⟨hc, hμ⟩ := ha
    obtain ⟨hc', hμ'⟩ := ha'
    have hp' := (VG.Proof.MlDsa.X86.Message.sShape hp).pubL s₀ s₀' h₀ h₀' hq
    have hk := (VG.Proof.MlDsa.X86.Message.skLen_ge hp).1
    have lk := (VG.Proof.MlDsa.X86.Message.leak_eq h₀ hc.ok.ctxLt hk).symm.trans (hq.leak.trans (VG.Proof.MlDsa.X86.Message.leak_eq h₀' hc'.ok.ctxLt hk))
    obtain ⟨a0, a1, a2, a3, a4, eS, bSk, bMu, bRnd⟩ := VG.Proof.MlDsa.X86.Message.sign_view h₀ hc hμ hs
    obtain ⟨a0', a1', a2', a3', a4', eS', bSk', bMu', bRnd'⟩ := VG.Proof.MlDsa.X86.Message.sign_view h₀' hc' hμ' hs'
    generalize (pushed Proof.MlKem.X86.rs5 s₁).callEntry = e at a0 a1 a2 a3 a4 eS bSk bMu bRnd ⊢
    generalize (pushed Proof.MlKem.X86.rs5 s₁').callEntry = e' at a0' a1' a2' a3' a4' eS' bSk' bMu' bRnd' ⊢
    sig_pub [signContract, signSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, a0, a1, a2, a3, a4, a0', a1', a2', a3', a4', eS, eS']
    rw [bSk, bMu, bRnd, bSk', bMu', bRnd']
    exact ⟨by simp only [Lay.E1, hp'.sp], lk, hq.args 0 (by decide), by rw [hp'.x], hq.args 5 (by decide),
      hq.args 6 (by decide), hq.args 7 (by decide)⟩
  · obtain ⟨hc, hμ⟩ := ha
    have hL := hc.ok
    have R := VG.Proof.MlDsa.X86.Message.sregs h₀ hL
    have hE := R.hE
    have hsp1 : s₁.gpr .esp = (VG.Proof.MlDsa.X86.Message.slay p s₀).E1 := (SetPost.ctx VG.Proof.MlDsa.X86.Message.signArgs_ok hs hc.ctx).esp
    refine ⟨CtxO.leafEnd (VG.Proof.MlDsa.X86.Message.sShape hp) h₀ hc (W := VG.Proof.MlDsa.X86.Message.sW p s₀) (by simp) (rs := VG.Proof.MlDsa.X86.Message.sWr p s₀ ++
        [below (s₁.gpr .esp) (4 * Proof.MlKem.X86.rs5.length + stackUse f + 4)]) (by rw [← hs.2.mem]; exact fr)
        (fun r hr => ?_) ((e₃ .esp (by decide)).trans (hs.esp VG.Proof.MlDsa.X86.Message.signArgs_ok)) (e₁.trans hs.2.rd)
        (e₂.trans hs.2.wr), ?_⟩
    · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨(arg s₀ 6).setWidth 64, p.sigLen⟩, by simp, fun _ h => h⟩
      · exact ⟨(VG.Proof.MlDsa.X86.Message.slay p s₀).SC, by simp, R.scrSub⟩
      · exact ⟨(VG.Proof.MlDsa.X86.Message.slay p s₀).STK, by simp, R.argsSub⟩
      · refine ⟨(VG.Proof.MlDsa.X86.Message.slay p s₀).STK, by simp, ?_⟩
        rw [hsp1]
        have := hf.su
        exact below_sub (by show _ ≤ 136 - 16; simp only [List.length_cons, List.length_nil]; omega)
          (by show 136 - 16 ≤ _; omega)
    · have v := VG.Proof.MlDsa.X86.Message.sign_view h₀ hc hμ hs
      obtain ⟨s₂, m₂, g₂, post⟩ := post
      obtain ⟨a0, a1, a2, a3, -, -, bSk, bMu, bRnd⟩ := v
      generalize (pushed Proof.MlKem.X86.rs5 s₁).callEntry = e at a0 a1 a2 a3 bSk bMu bRnd post
      sig_post [signContract, signSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
      simp only [arg_withRegions, a0, a1, a2, a3] at post
      rw [bSk, bMu, bRnd, Proof.MlKem.X86.setWidth_append32, g₂, m₂] at post
      exact ⟨hc.ok.ctxLt, post⟩

end

end VG.Proof.MlDsa.X86.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Message.Sign`. -/
section

/-!
# ML-DSA on x86 (32-bit), `sign_message`: correct and constant time

Untrusted: everything here is checked by Lean. The body past the entry:
`μ = H(tr ‖ 0 ‖ ctx_len ‖ ctx ‖ M, 64)`, for `tr` the 64 bytes of `sk` at
64, then the call of the signing function on it (`signRest_piece`); in the
leaf, after the check (`signMessage_piece`); and what that says of the
contract's postcondition (`signMessage_post`).
-/

namespace VG.Proof.MlDsa.X86.Message

open VG VG.X86 VG.Impl.MlDsa.X86.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.X86 (Piece P0 E0 frameR retR LeafEnd LeafPost)
open VG.Spec.Sha3 (bytesAt)
open VG.Spec.MlDsa

section
variable {p : Params}

/-- Bytes apart from the stack the contract gives, as on entry, after the leaf's push. -/
theorem p0_bytes {s₀ : State} {N : Nat} (hN : 16 ≤ N) (hN' : N ≤ (s₀.gpr .esp).toNat) {a : Addr} {n : Nat}
    (hk : (VG.Proof.MlDsa.X86.Message.sStk s₀ N).Disjoint ⟨a, n⟩) (hn : n ≤ 2 ^ 64) :
    bytesAt (P0 s₀).mem a n = bytesAt s₀.mem a n := by
  have hf := pushed_frame (rs := Impl.MlKem.X86.saveRegs) (s := s₀) (by decide) (by show 16 ≤ _; omega)
  exact Proof.MlKem.bytesAt_congr fun _ hi => hf.bytes (R := ⟨a, n⟩) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ((VG.Proof.MlDsa.X86.Message.stk_eq hN' ▸ hk).sub_left (below_sub hN hN')).symm) hn hi

/-- `μ` is the message representative of the formatted message. -/
theorem sMu_eq {s₀ : State} (h₀ : VG.Proof.MlDsa.X86.Message.SPre p s₀) (hk : 128 ≤ p.skLen) :
    messageRep (skTr (bytesAt s₀.mem ((arg s₀ 0).setWidth 64) p.skLen))
      ([0, BitVec.ofNat 8 (bytesAt s₀.mem ((arg s₀ 3).setWidth 64) (arg s₀ 4).toNat).length] ++
        bytesAt s₀.mem ((arg s₀ 3).setWidth 64) (arg s₀ 4).toNat ++
        bytesAt s₀.mem ((arg s₀ 1).setWidth 64) (arg s₀ 2).toNat) = VG.Proof.MlDsa.X86.Message.sMu p s₀ := by
  have := h₀.nSk
  simp only [messageRep, skTr, Proof.MlKem.bytesAt_length]
  rw [Proof.MlKem.bytesAt_slice _ _ (by omega)]
  simp only [VG.Proof.MlDsa.X86.Message.sMu, VG.Proof.MlDsa.X86.Message.hdrBytes, VG.Proof.MlDsa.X86.Message.slay, List.append_assoc]
  rw [Proof.MlKem.X86.ea_off (by omega)]

/-- `μ`, then the call of the signing function on it. -/
theorem signRest_piece (hp : p ∈ VG.Proof.MlDsa.X86.Message.params) {n : String} {f : Prog isa} (hf : VG.Proof.MlDsa.X86.Message.SignFn p f) :
    Piece (VG.Proof.MlDsa.X86.Message.SPre p) (VG.Proof.MlDsa.X86.Message.SPub p) (VG.Proof.MlDsa.X86.Message.CtxO (VG.Proof.MlDsa.X86.Message.slay p)) (fun s₀ s => LeafEnd s₀ (VG.Proof.MlDsa.X86.Message.sW p s₀) s ∧ VG.Proof.MlDsa.X86.Message.SB p s₀ s)
      (.seq (muHash (.argOff 0 64)) (.seq (.block (VG.Impl.MlDsa.X86.Message.setArgs VG.Proof.MlDsa.X86.Message.signArgs)) (Impl.MlKem.X86.callRet rs5 n f))) := by
  have hk := VG.Proof.MlDsa.X86.Message.skLen_ge hp
  refine Piece.seq ((VG.Proof.MlDsa.X86.Message.muHash_piece (lay := VG.Proof.MlDsa.X86.Message.slay p) (.argOff 0 64) (fun s₀ => arg s₀ 0 + BitVec.ofNat 32 64)
    (fun s₀ => bytesAt s₀.mem ((arg s₀ 0 + BitVec.ofNat 32 64).setWidth 64) 64) (by taint_decide) (VG.Proof.MlDsa.X86.Message.sShape hp).pubL
    (fun _ _ _ h => h) (fun _ _ => by show 5 ≤ 8; decide) (fun _ _ => rfl) rfl
    (fun s₀ s h₀ hc => hc.ctx.argOffV (by show 0 < 8; decide) 64)
    (fun s₀ s₀' h₀ h₀' hq => by rw [hq.args 0 (by decide)])
    (fun s₀ s h₀ hc => ?_) (fun _ _ => Proof.MlKem.bytesAt_length _ _ _) (fun s₀ h₀ hL => ?_)).mono
    (fun _ _ _ h => h) fun s₀ s h₀ ⟨hc, hm⟩ => ⟨hc, ?_⟩) (VG.Proof.MlDsa.X86.Message.signCall_piece hp hf)
  · have hL := hc.ok
    have := h₀.nSk
    have wtr : Within ⟨(arg s₀ 0 + BitVec.ofNat 32 64).setWidth 64, 64⟩ (VG.Proof.MlDsa.X86.Message.slay p s₀).KEY := by
      rw [Proof.MlKem.X86.ea_off (by omega)]; exact within_off _ (show 64 + 64 ≤ p.skLen by omega)
    rw [hc.ctx.bytesAt_eq (hL.xKey.sub_right wtr.sub) (hL.kKey.sub_right wtr.sub) (by decide)]
    exact VG.Proof.MlDsa.X86.Message.p0_bytes (by decide) h₀.sp (h₀.kSk.sub_right wtr.sub) (by decide)
  · have := h₀.nSk
    have wtr : Within ⟨(arg s₀ 0 + BitVec.ofNat 32 64).setWidth 64, 64⟩ (VG.Proof.MlDsa.X86.Message.slay p s₀).KEY := by
      rw [Proof.MlKem.X86.ea_off (by omega)]; exact within_off _ (show 64 + 64 ≤ p.skLen by omega)
    have hst : Region.Sub ⟨(VG.Proof.MlDsa.X86.Message.slay p s₀).ST, 200⟩ (VG.Proof.MlDsa.X86.Message.slay p s₀).SC := by
      have := hL.sub_sc (e := 0) (k := 200) (by omega)
      simpa only [VG.Proof.MlDsa.X86.Message.x0] using this
    refine ⟨?_, ⟨_, List.mem_append_left _ hL.inKey, wtr⟩, (hL.xKey.symm.sub_left wtr.sub).sub_right hst,
      (hL.xKey.symm.sub_left wtr.sub).sub_right (hL.sub_sc (by omega : 200 + 640 ≤ 1024)),
      hL.kKey.sub_right wtr.sub⟩
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 64) (by decide), Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [hm]
    simp only [VG.Proof.MlDsa.X86.Message.ctxB, VG.Proof.MlDsa.X86.Message.msgB]
    rw [VG.Proof.MlDsa.X86.Message.p0_bytes (a := (VG.Proof.MlDsa.X86.Message.slay p s₀).ctx.setWidth 64) (n := (VG.Proof.MlDsa.X86.Message.slay p s₀).ctxLen.toNat) (by decide) h₀.sp h₀.kCtx
        (by have := (arg s₀ 4).isLt; show (arg s₀ 4).toNat ≤ _; omega),
      VG.Proof.MlDsa.X86.Message.p0_bytes (a := (VG.Proof.MlDsa.X86.Message.slay p s₀).msg.setWidth 64) (n := (VG.Proof.MlDsa.X86.Message.slay p s₀).len.toNat) (by decide) h₀.sp h₀.kMsg
        (by have := (arg s₀ 2).isLt; show (arg s₀ 2).toNat ≤ _; omega)]
    rfl


/-- What `sign_message` changes is apart from its frame and return address. -/
theorem sign_hW : ∀ s₀, VG.Proof.MlDsa.X86.Message.SPre p s₀ → ∀ r ∈ VG.Proof.MlDsa.X86.Message.sW p s₀, (frameR s₀).Disjoint r ∧ (VG.Proof.MlKem.X86.retR s₀).Disjoint r := by
  intro s₀ h₀ r hr
  have hsp := h₀.sp
  have fr : Region.Sub (frameR s₀) (VG.Proof.MlDsa.X86.Message.sStk s₀ 136) := by rw [VG.Proof.MlDsa.X86.Message.stk_eq hsp]; exact below_sub (by decide) hsp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨h₀.kScr.sub_left fr, h₀.rScr⟩
  · exact ⟨Proof.MlKem.X86.Top.below_adj (sp := s₀.gpr .esp) (a := 16) (b := 136 - 16) (by omega),
      (Proof.MlKem.X86.Top.ret_below hsp).sub_right (below_inner (a := 136 - 16) (k := 16) (by omega) hsp)⟩
  · exact ⟨h₀.kSig.sub_left fr, h₀.rSig⟩

theorem nosp_seq {a b : Prog isa} (ha : NoSp a) (hb : NoSp b) : NoSp (.seq a b) := fun i hi => by
  simp only [VG.instrs, List.mem_append] at hi
  rcases hi with h | h
  exacts [ha i h, hb i h]

theorem nosp_ite {cnd : Cond} {a b : Prog isa} (ha : NoSp a) (hb : NoSp b) : NoSp (.ite cnd a b) := fun i hi => by
  simp only [VG.instrs, List.mem_append] at hi
  rcases hi with h | h
  exacts [ha i h, hb i h]

theorem enter_nosp (si : Nat) (p : Params) : NoSp (enter si p) := fun i hi => by
  simp only [enter, VG.instrs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with (rfl | rfl) | (rfl | rfl | rfl | rfl) <;> rfl

theorem callRet_nosp {rs : List Reg} {n : String} {c : Prog isa} (hc : NoSp c) :
    NoSp (Impl.MlKem.X86.callRet rs n c) := fun i hi => by
  simp only [Impl.MlKem.X86.callRet, VG.instrs, List.mem_cons, List.mem_append, List.not_mem_nil,
    or_false] at hi
  rcases hi with (rfl | hi) | rfl
  · rfl
  · exact hc i hi
  · rfl

/-- `sign_message`, in its leaf. -/
theorem signMessage_piece (hp : p ∈ VG.Proof.MlDsa.X86.Message.params) {n : String} {f : Prog isa} (hf : VG.Proof.MlDsa.X86.Message.SignFn p f)
    {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp]) (.block [.mov .esi (.mem (argAt 7)),
      .alu .add .esi (.imm (BitVec.ofNat 32 (oE p)))]) ht).isSome = true) :
    Piece (VG.Proof.MlDsa.X86.Message.SPre p) (VG.Proof.MlDsa.X86.Message.SPub p) (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (fun s => (256 ≤ (arg s₀ 4).toNat ∧
      s.gpr .eax = 2) ∨ VG.Proof.MlDsa.X86.Message.SB p s₀ s) s₀ s') (signMessage n f p) :=
  VG.Proof.MlDsa.X86.Message.top_piece (VG.Proof.MlDsa.X86.Message.sShape hp) tt (VG.Proof.MlDsa.X86.Message.sW p) VG.Proof.MlDsa.X86.Message.sign_hW
    (VG.Proof.MlDsa.X86.Message.nosp_seq (NoSp.of_all (by decide +kernel)) (VG.Proof.MlDsa.X86.Message.nosp_ite (NoSp.of_all (by decide +kernel))
      (VG.Proof.MlDsa.X86.Message.nosp_seq (VG.Proof.MlDsa.X86.Message.enter_nosp 7 p) (VG.Proof.MlDsa.X86.Message.nosp_seq (NoSp.of_all (by decide +kernel))
        (VG.Proof.MlDsa.X86.Message.nosp_seq (NoSp.of_all (by decide +kernel)) (VG.Proof.MlDsa.X86.Message.callRet_nosp hf.nosp))))))
    (VG.Proof.MlDsa.X86.Message.signRest_piece hp hf)

/-- Memory with the arguments `0`, `0x2000`, `0`, `0x2000`, `0`, `0x3000`,
`0x6000` and `0x10000` at `0x5004`. -/
def satMemS : Mem := fun a =>
  if a = 0x5009 then 0x20 else if a = 0x5011 then 0x20 else if a = 0x5019 then 0x30 else
  if a = 0x501d then 0x60 else if a = 0x5022 then 1 else 0

/-- A state satisfying the precondition of `sign_message`. -/
def signSat (p : Params) : State :=
  Proof.MlKem.X86.satState VG.Proof.MlDsa.X86.Message.satMemS [⟨0, p.skLen⟩, ⟨0x2000, 0⟩, ⟨0x2000, 0⟩, ⟨0x3000, 32⟩]
    [⟨0x6000, p.sigLen⟩, ⟨0x10000, VG.Proof.MlDsa.X86.Message.mScrLen p⟩, ⟨0x5004, 32⟩]

theorem signMessage_verified (hp : p ∈ VG.Proof.MlDsa.X86.Message.params) {n : String} {f : Prog isa} (hf : VG.Proof.MlDsa.X86.Message.SignFn p f)
    {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp]) (.block [.mov .esi (.mem (argAt 7)),
      .alu .add .esi (.imm (BitVec.ofNat 32 (oE p)))]) ht).isSome = true) :
    Verified X86.target (signMessage n f p) (signMessageContract p X86.abi 136) := by
  refine Piece.verified (((VG.Proof.MlDsa.X86.Message.signMessage_piece hp hf tt).pre_mono (fun _ h => VG.Proof.MlDsa.X86.Message.sPre_of h)
    fun _ _ _ _ h => VG.Proof.MlDsa.X86.Message.spub_of h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hB, hm, hax⟩ := hq
    refine ⟨habi, ?_⟩
    have h₀' := VG.Proof.MlDsa.X86.Message.sPre_of h₀
    sig_post [signMessageContract, signMessageSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [Proof.MlKem.X86.setWidth_append32, hax, hm]
    rcases hB with ⟨h8, h2⟩ | ⟨h8, hout⟩
    · rw [formatMessage_none (by rw [Proof.MlKem.bytesAt_length]; exact h8)]; exact h2
    · rw [formatMessage_some (by rw [Proof.MlKem.bytesAt_length]; exact h8)]
      simp only [signInternal]
      rw [VG.Proof.MlDsa.X86.Message.sMu_eq h₀' (VG.Proof.MlDsa.X86.Message.skLen_ge hp).1]
      exact hout
  · simp only [VG.Proof.MlDsa.X86.Message.params, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨VG.Proof.MlDsa.X86.Message.signSat mlDsa44, by sig_sat_check [signMessageContract, signMessageSig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes, VG.Proof.MlDsa.X86.Message.signSat, Proof.MlKem.X86.satState, VG.Proof.MlDsa.X86.Message.satMemS]⟩
    · exact ⟨VG.Proof.MlDsa.X86.Message.signSat mlDsa65, by sig_sat_check [signMessageContract, signMessageSig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes, VG.Proof.MlDsa.X86.Message.signSat, Proof.MlKem.X86.satState, VG.Proof.MlDsa.X86.Message.satMemS]⟩
    · exact ⟨VG.Proof.MlDsa.X86.Message.signSat mlDsa87, by sig_sat_check [signMessageContract, signMessageSig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes, VG.Proof.MlDsa.X86.Message.signSat, Proof.MlKem.X86.satState, VG.Proof.MlDsa.X86.Message.satMemS]⟩

end

end VG.Proof.MlDsa.X86.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Message.VerifyCall`. -/
section

/-!
# ML-DSA on x86 (32-bit), `verify_message`: the call of the verification function on `μ`

Untrusted: everything here is checked by Lean. With `μ` at `X + 840`, the
call of `vg_mldsa*_verify(pk, μ, sig, scratch)` (`verifyCall_piece`): its
arguments in `eax`, `ecx`, `edx` and `ebx`, pushed; its precondition
(`verifyContract p X86.abi 96`), from `verify_message`'s; what it leaks, its
inputs, which `verify_message`'s inputs determine; and its result, which is
`verify_message`'s.
-/

namespace VG.Proof.MlDsa.X86.Message

open VG VG.X86 VG.Impl.MlDsa.X86.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.X86 (Only Piece P0 E0 frameR retR LeafEnd)
open VG.Proof.MlKem.X86.Top (entry_regions entry_self covers_of)
open VG.Spec.Sha3 (bytesAt)
open VG.Spec.MlDsa

/-- A verification function on `μ`, as `verify_message` calls it. -/
structure VerifyFn (p : Params) (c : Prog isa) : Prop where
  ver : Verified X86.target c (verifyContract p X86.abi 96)
  nosp : NoSp c
  su : stackUse c ≤ 96

/-- The arguments of the call of the verification function on `μ`, and their registers. -/
abbrev verifyArgs : List (Reg × VG.Impl.MlDsa.X86.Message.Arg) := [(.eax, .arg 0), (.ecx, .off oMU), (.edx, .arg 5), (.ebx, .arg 6)]
abbrev rs4 : List Reg := [.ebx, .edx, .ecx, .eax]

section
variable (p : Params) (s₀ : State)

/-- The message representative of the run from `s₀`. -/
abbrev vMu : List Byte :=
  VG.Spec.MlDsa.H (VG.Spec.MlDsa.H (bytesAt s₀.mem ((arg s₀ 0).setWidth 64) p.pkLen) 64 ++ VG.Proof.MlDsa.X86.Message.hdrBytes (VG.Proof.MlDsa.X86.Message.vlay p s₀) ++
    bytesAt s₀.mem ((arg s₀ 3).setWidth 64) (arg s₀ 4).toNat ++ bytesAt s₀.mem ((arg s₀ 1).setWidth 64) (arg s₀ 2).toNat)
    64

/-- The regions the verification function on `μ` is given. -/
abbrev vRd : List Region :=
  [⟨(arg s₀ 0).setWidth 64, p.pkLen⟩, ⟨((VG.Proof.MlDsa.X86.Message.vlay p s₀).X32 + BitVec.ofNat 32 840).setWidth 64, 64⟩,
    ⟨(arg s₀ 5).setWidth 64, p.sigLen⟩]
abbrev vWr : List Region := [⟨(arg s₀ 6).setWidth 64, VG.Proof.MlDsa.X86.Message.sScr p⟩, below (VG.Proof.MlDsa.X86.Message.vlay p s₀).E1 16]

/-- What `verify_message` changes: `scratch` and the stack. -/
abbrev vW : List Region := [(VG.Proof.MlDsa.X86.Message.vlay p s₀).SC, (VG.Proof.MlDsa.X86.Message.vlay p s₀).STK]

/-- The result. -/
def VB (s : State) : Prop :=
  (arg s₀ 4).toNat < 256 ∧
    ((s.gpr .eax = 1 ∧ ∃ b, verifyMu p b (bytesAt s₀.mem ((arg s₀ 0).setWidth 64) p.pkLen) (VG.Proof.MlDsa.X86.Message.vMu p s₀)
        (bytesAt s₀.mem ((arg s₀ 5).setWidth 64) p.sigLen) = some true) ∨
      (s.gpr .eax = 0 ∧ verifyMu p minBounds (bytesAt s₀.mem ((arg s₀ 0).setWidth 64) p.pkLen) (VG.Proof.MlDsa.X86.Message.vMu p s₀)
        (bytesAt s₀.mem ((arg s₀ 5).setWidth 64) p.sigLen) ≠ some true))

end

section
variable {p : Params}

theorem verifyArgs_ok : VG.Proof.MlDsa.X86.Message.argsOk 7 VG.Proof.MlDsa.X86.Message.verifyArgs = true := by decide

/-- The values of the arguments. -/
theorem verifyArgs_val {s₀ s s₁ : State} (hc : VG.Proof.MlDsa.X86.Message.CtxO (VG.Proof.MlDsa.X86.Message.vlay p) s₀ s) (hs : VG.Proof.MlDsa.X86.Message.SetPost VG.Proof.MlDsa.X86.Message.verifyArgs s s₁) :
    s₁.gpr .eax = arg s₀ 0 ∧ s₁.gpr .ecx = (VG.Proof.MlDsa.X86.Message.vlay p s₀).X32 + BitVec.ofNat 32 840 ∧ s₁.gpr .edx = arg s₀ 5 ∧
      s₁.gpr .ebx = arg s₀ 6 := by
  have h7 : ∀ {i}, i < 7 → i < (VG.Proof.MlDsa.X86.Message.vlay p s₀).nA := fun h => h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hs.1 (.eax, .arg 0) (by simp), hc.ctx.argV (h7 (by decide))]; rfl
  · rw [hs.1 (.ecx, .off oMU) (by simp), hc.ctx.off]; rfl
  · rw [hs.1 (.edx, .arg 5) (by simp), hc.ctx.argV (h7 (by decide))]; rfl
  · rw [hs.1 (.ebx, .arg 6) (by simp), hc.ctx.argV (h7 (by decide))]; rfl

/-- The facts about regions the call needs. -/
structure VRegs (p : Params) (s₀ : State) : Prop where
  hE : 116 ≤ (VG.Proof.MlDsa.X86.Message.vlay p s₀).E1.toNat
  scrSub : Region.Sub ⟨(arg s₀ 6).setWidth 64, VG.Proof.MlDsa.X86.Message.sScr p⟩ (VG.Proof.MlDsa.X86.Message.vlay p s₀).SC
  argsSub : Region.Sub (below (VG.Proof.MlDsa.X86.Message.vlay p s₀).E1 16) (VG.Proof.MlDsa.X86.Message.vlay p s₀).STK
  muSub : Region.Sub ⟨((VG.Proof.MlDsa.X86.Message.vlay p s₀).X32 + BitVec.ofNat 32 840).setWidth 64, 64⟩ (VG.Proof.MlDsa.X86.Message.vlay p s₀).SC
  kPk : (VG.Proof.MlDsa.X86.Message.vlay p s₀).STK.Disjoint ⟨(arg s₀ 0).setWidth 64, p.pkLen⟩
  kMu : (VG.Proof.MlDsa.X86.Message.vlay p s₀).STK.Disjoint ⟨((VG.Proof.MlDsa.X86.Message.vlay p s₀).X32 + BitVec.ofNat 32 840).setWidth 64, 64⟩
  kSig : (VG.Proof.MlDsa.X86.Message.vlay p s₀).STK.Disjoint ⟨(arg s₀ 5).setWidth 64, p.sigLen⟩
  kScr : (VG.Proof.MlDsa.X86.Message.vlay p s₀).STK.Disjoint ⟨(arg s₀ 6).setWidth 64, VG.Proof.MlDsa.X86.Message.sScr p⟩
  muScr : Region.Disjoint ⟨((VG.Proof.MlDsa.X86.Message.vlay p s₀).X32 + BitVec.ofNat 32 840).setWidth 64, 64⟩ ⟨(arg s₀ 6).setWidth 64, VG.Proof.MlDsa.X86.Message.sScr p⟩

theorem vregs {s₀ : State} (h₀ : VG.Proof.MlDsa.X86.Message.VPre p s₀) (hL : (VG.Proof.MlDsa.X86.Message.vlay p s₀).Ok) : VG.Proof.MlDsa.X86.Message.VRegs p s₀ := by
  have hsp := h₀.sp
  have hE : 116 ≤ (VG.Proof.MlDsa.X86.Message.vlay p s₀).E1.toNat := by
    show 116 ≤ (s₀.gpr .esp - BitVec.ofNat 32 16).toNat
    rw [sub_toNat (by omega)]; omega
  have hk : ∀ {R : Region}, (VG.Proof.MlDsa.X86.Message.sStk s₀ 132).Disjoint R → (VG.Proof.MlDsa.X86.Message.vlay p s₀).STK.Disjoint R := fun h =>
    (VG.Proof.MlDsa.X86.Message.stk_eq hsp ▸ h).sub_left hL.stk_sub
  have scrSub : Region.Sub ⟨(arg s₀ 6).setWidth 64, VG.Proof.MlDsa.X86.Message.sScr p⟩ (VG.Proof.MlDsa.X86.Message.vlay p s₀).SC :=
    (within_base _ (by show VG.Proof.MlDsa.X86.Message.sScr p ≤ VG.Proof.MlDsa.X86.Message.mScrLen p; simp only [VG.Proof.MlDsa.X86.Message.sScr, VG.Proof.MlDsa.X86.Message.mScrLen, messageScratchWords]; omega)).sub
  have muSub : Region.Sub ⟨((VG.Proof.MlDsa.X86.Message.vlay p s₀).X32 + BitVec.ofNat 32 840).setWidth 64, 64⟩ (VG.Proof.MlDsa.X86.Message.vlay p s₀).SC := by
    rw [VG.Proof.MlDsa.X86.Message.mu_eq hL]; exact hL.sub_sc (e := 840) (k := 64) (by omega)
  refine ⟨hE, scrSub, below_sub (by show 16 ≤ 132 - 16; decide) (by show 132 - 16 ≤ _; omega), muSub, hk h₀.kPk,
    by rw [VG.Proof.MlDsa.X86.Message.mu_eq hL]; exact VG.Proof.MlDsa.X86.Message.k_mu hL, hk h₀.kSig, hL.kSC.sub_right scrSub, ?_⟩
  have hx := hL.x_eq
  have := h₀.nScr
  have := VG.Proof.MlDsa.X86.Message.mScr_eq p
  have e : ((VG.Proof.MlDsa.X86.Message.vlay p s₀).X32 + BitVec.ofNat 32 840).setWidth 64 =
      (arg s₀ 6).setWidth 64 + BitVec.ofNat 64 (oE p + 840) := by
    rw [VG.Proof.MlDsa.X86.Message.mu_eq hL, Lay.MU, hx, add_add]; rfl
  rw [e]
  have d := Offset.disjoint ((arg s₀ 6).setWidth 64) (d := oE p + 840) (n := 64) (e := 0) (k := VG.Proof.MlDsa.X86.Message.sScr p)
    (.inr (by simp only [oE, VG.Proof.MlDsa.X86.Message.sScr]; omega)) (by omega) (by simp only [oE, VG.Proof.MlDsa.X86.Message.sScr] at *; omega)
  rwa [BitVec.add_zero] at d

/-- The callee's precondition. -/
theorem verify_callPre {s₀ s s₁ : State} (h₀ : VG.Proof.MlDsa.X86.Message.VPre p s₀) (hc : VG.Proof.MlDsa.X86.Message.CtxO (VG.Proof.MlDsa.X86.Message.vlay p) s₀ s)
    (hs : VG.Proof.MlDsa.X86.Message.SetPost VG.Proof.MlDsa.X86.Message.verifyArgs s s₁) : CallPre (verifyContract p X86.abi 96) VG.Proof.MlDsa.X86.Message.rs4 (VG.Proof.MlDsa.X86.Message.vRd p s₀) (VG.Proof.MlDsa.X86.Message.vWr p s₀) s₁ := by
  have hL := hc.ok
  have hc1 := SetPost.ctx VG.Proof.MlDsa.X86.Message.verifyArgs_ok hs hc.ctx
  obtain ⟨v0, v1, v2, v3⟩ := VG.Proof.MlDsa.X86.Message.verifyArgs_val hc hs
  have R := VG.Proof.MlDsa.X86.Message.vregs h₀ hL
  have hE := R.hE
  have hsp1 : s₁.gpr .esp = (VG.Proof.MlDsa.X86.Message.vlay p s₀).E1 := hc1.esp
  have fit : 4 * rs4.length + 4 ≤ (s₁.gpr .esp).toNat := by
    rw [hsp1]; simp only [List.length_cons, List.length_nil]; omega
  have a0 : arg (pushed VG.Proof.MlDsa.X86.Message.rs4 s₁).callEntry 0 = arg s₀ 0 := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact v0
  have a1 : arg (pushed VG.Proof.MlDsa.X86.Message.rs4 s₁).callEntry 1 = (VG.Proof.MlDsa.X86.Message.vlay p s₀).X32 + BitVec.ofNat 32 840 := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact v1
  have a2 : arg (pushed VG.Proof.MlDsa.X86.Message.rs4 s₁).callEntry 2 = arg s₀ 5 := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact v2
  have a3 : arg (pushed VG.Proof.MlDsa.X86.Message.rs4 s₁).callEntry 3 = arg s₀ 6 := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact v3
  have eA : argAddr (pushed VG.Proof.MlDsa.X86.Message.rs4 s₁).callEntry 0 = ((VG.Proof.MlDsa.X86.Message.vlay p s₀).E1 - BitVec.ofNat 32 16).setWidth 64 := by
    rw [callEntry_argAddr0, hsp1]; rfl
  have eSp : (pushed VG.Proof.MlDsa.X86.Message.rs4 s₁).callEntry.gpr .esp = (VG.Proof.MlDsa.X86.Message.vlay p s₀).E1 - BitVec.ofNat 32 (4 * 4 + 4) := by
    rw [callEntry_esp', hsp1]; rfl
  have cv := covers_of (s := s₁) (n := 4) (rd := VG.Proof.MlDsa.X86.Message.vRd p s₀) (wr := VG.Proof.MlDsa.X86.Message.vWr p s₀) (fun r hr => ?_) fun r hr => ?_
  rotate_left
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact VG.Proof.MlDsa.X86.Message.withinRW hc1 ⟨_, List.mem_append_left _ hL.inKey, within_self _⟩
    · exact VG.Proof.MlDsa.X86.Message.withinRW hc1 (by rw [VG.Proof.MlDsa.X86.Message.mu_eq hL]; exact VG.Proof.MlDsa.X86.Message.cov_x hL (e := 840) (k := 64) (by omega))
    · exact VG.Proof.MlDsa.X86.Message.withinRW hc1 ⟨_, List.mem_append_left _ (by show _ ∈ s₀.rd; rw [h₀.rd]; simp), within_self _⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr (VG.Proof.MlDsa.X86.Message.withinW hc1 ⟨_, hL.inSC, within_base _
        (by show VG.Proof.MlDsa.X86.Message.sScr p ≤ VG.Proof.MlDsa.X86.Message.mScrLen p; simp only [VG.Proof.MlDsa.X86.Message.sScr, VG.Proof.MlDsa.X86.Message.mScrLen, messageScratchWords]; omega)⟩)
    · exact .inl (by rw [hsp1])
  refine ⟨?_, cv.1, cv.2⟩
  obtain ⟨rPk₁, rPk₂, rPk₃⟩ := entry_regions (E := (VG.Proof.MlDsa.X86.Message.vlay p s₀).E1) (k := 4) (K := 96) (by omega) R.kPk
  obtain ⟨rMu₁, rMu₂, rMu₃⟩ := entry_regions (E := (VG.Proof.MlDsa.X86.Message.vlay p s₀).E1) (k := 4) (K := 96) (by omega) R.kMu
  obtain ⟨rSig₁, rSig₂, rSig₃⟩ := entry_regions (E := (VG.Proof.MlDsa.X86.Message.vlay p s₀).E1) (k := 4) (K := 96) (by omega) R.kSig
  obtain ⟨rScr₁, rScr₂, rScr₃⟩ := entry_regions (E := (VG.Proof.MlDsa.X86.Message.vlay p s₀).E1) (k := 4) (K := 96) (by omega) R.kScr
  obtain ⟨rA₂, rA₃⟩ := entry_self (E := (VG.Proof.MlDsa.X86.Message.vlay p s₀).E1) (k := 4) (K := 96) (by omega)
  generalize he : (pushed VG.Proof.MlDsa.X86.Message.rs4 s₁).callEntry = e at a0 a1 a2 a3 eA eSp ⊢
  sig_pre [verifyContract, verifySig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  subst he
  simp only [arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, eA, eSp]
  have hX := hL.x32_lt
  refine ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := (VG.Proof.MlDsa.X86.Message.vlay p s₀).E1.isLt; omega,
    trivial, trivial, h₀.pkScr.sub_right R.scrSub, rPk₁, R.muScr, rMu₁, h₀.sigScr.sub_right R.scrSub, rSig₁, rScr₁,
    rPk₂, rMu₂, rSig₂, rScr₂, rA₂, rPk₃, rMu₃, rSig₃, rScr₃, rA₃, h₀.nPk,
    by rw [hL.x32_toNat (by omega)]; omega, h₀.nSig,
    by have := h₀.nScr; simp only [VG.Proof.MlDsa.X86.Message.mScrLen, messageScratchWords] at this ⊢; omega⟩


/-- What the verification function on `μ` sees on entry. -/
structure VView (p : Params) (s₀ s₁ : State) : Prop where
  a0 : arg (pushed VG.Proof.MlDsa.X86.Message.rs4 s₁).callEntry 0 = arg s₀ 0
  a1 : arg (pushed VG.Proof.MlDsa.X86.Message.rs4 s₁).callEntry 1 = (VG.Proof.MlDsa.X86.Message.vlay p s₀).X32 + BitVec.ofNat 32 840
  a2 : arg (pushed VG.Proof.MlDsa.X86.Message.rs4 s₁).callEntry 2 = arg s₀ 5
  a3 : arg (pushed VG.Proof.MlDsa.X86.Message.rs4 s₁).callEntry 3 = arg s₀ 6
  esp : (pushed VG.Proof.MlDsa.X86.Message.rs4 s₁).callEntry.gpr .esp = (VG.Proof.MlDsa.X86.Message.vlay p s₀).E1 - BitVec.ofNat 32 (4 * 4 + 4)
  bPk : bytesAt (pushed VG.Proof.MlDsa.X86.Message.rs4 s₁).callEntry.mem ((arg s₀ 0).setWidth 64) p.pkLen =
    bytesAt s₀.mem ((arg s₀ 0).setWidth 64) p.pkLen
  bMu : bytesAt (pushed VG.Proof.MlDsa.X86.Message.rs4 s₁).callEntry.mem (((VG.Proof.MlDsa.X86.Message.vlay p s₀).X32 + BitVec.ofNat 32 840).setWidth 64) 64 = VG.Proof.MlDsa.X86.Message.vMu p s₀
  bSig : bytesAt (pushed VG.Proof.MlDsa.X86.Message.rs4 s₁).callEntry.mem ((arg s₀ 5).setWidth 64) p.sigLen =
    bytesAt s₀.mem ((arg s₀ 5).setWidth 64) p.sigLen

theorem verify_view {s₀ s s₁ : State} (h₀ : VG.Proof.MlDsa.X86.Message.VPre p s₀) (hc : VG.Proof.MlDsa.X86.Message.CtxO (VG.Proof.MlDsa.X86.Message.vlay p) s₀ s)
    (hμ : bytesAt s.mem (VG.Proof.MlDsa.X86.Message.vlay p s₀).MU 64 = VG.Proof.MlDsa.X86.Message.vMu p s₀) (hs : VG.Proof.MlDsa.X86.Message.SetPost VG.Proof.MlDsa.X86.Message.verifyArgs s s₁) : VG.Proof.MlDsa.X86.Message.VView p s₀ s₁ := by
  have hL := hc.ok
  have hc1 := SetPost.ctx VG.Proof.MlDsa.X86.Message.verifyArgs_ok hs hc.ctx
  obtain ⟨v0, v1, v2, v3⟩ := VG.Proof.MlDsa.X86.Message.verifyArgs_val hc hs
  have R := VG.Proof.MlDsa.X86.Message.vregs h₀ hL
  have hE := R.hE
  have hsp1 : s₁.gpr .esp = (VG.Proof.MlDsa.X86.Message.vlay p s₀).E1 := hc1.esp
  have fit : 4 * rs4.length + 4 ≤ (s₁.gpr .esp).toNat := by
    rw [hsp1]; simp only [List.length_cons, List.length_nil]; omega
  have fr := callEntry_frame fit (by decide : Reg.esp ∉ rs4)
  rw [hsp1] at fr
  have b20 : Region.Sub (below (VG.Proof.MlDsa.X86.Message.vlay p s₀).E1 (4 * rs4.length + 4)) (VG.Proof.MlDsa.X86.Message.vlay p s₀).STK :=
    below_sub (by show 20 ≤ 132 - 16; decide) (by show 132 - 16 ≤ _; omega)
  have ent : ∀ {a : Addr} {n : Nat}, (VG.Proof.MlDsa.X86.Message.vlay p s₀).STK.Disjoint ⟨a, n⟩ → n ≤ 2 ^ 64 →
      bytesAt (pushed VG.Proof.MlDsa.X86.Message.rs4 s₁).callEntry.mem a n = bytesAt s₁.mem a n :=
    fun {a n} hR hn => Proof.MlKem.bytesAt_congr fun _ hi => fr.bytes (R := ⟨a, n⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hR.sub_left b20).symm) hn hi
  have hsp := h₀.sp
  have p0 : ∀ {a : Addr} {n : Nat}, (VG.Proof.MlDsa.X86.Message.sStk s₀ 132).Disjoint ⟨a, n⟩ → (VG.Proof.MlDsa.X86.Message.vlay p s₀).SC.Disjoint ⟨a, n⟩ → n ≤ 2 ^ 64 →
      bytesAt s₁.mem a n = bytesAt s₀.mem a n := fun {a n} hk hx hn => by
    rw [hs.2.mem, hc.ctx.bytesAt_eq hx ((VG.Proof.MlDsa.X86.Message.stk_eq hsp ▸ hk).sub_left hL.stk_sub) hn]
    exact VG.Proof.MlDsa.X86.Message.p0_bytes (by decide) hsp hk hn
  refine ⟨by rw [callEntry_arg fit (by decide) (by decide)]; exact v0,
    by rw [callEntry_arg fit (by decide) (by decide)]; exact v1,
    by rw [callEntry_arg fit (by decide) (by decide)]; exact v2,
    by rw [callEntry_arg fit (by decide) (by decide)]; exact v3,
    by rw [callEntry_esp', hsp1]; rfl, ?_, ?_, ?_⟩
  · rw [ent R.kPk (by have := h₀.nPk; omega)]
    exact p0 h₀.kPk h₀.pkScr.symm (by have := h₀.nPk; omega)
  · rw [ent R.kMu (by decide), hs.2.mem, VG.Proof.MlDsa.X86.Message.mu_eq hL]; exact hμ
  · rw [ent R.kSig (by have := h₀.nSig; omega)]
    exact p0 h₀.kSig h₀.sigScr.symm (by have := h₀.nSig; omega)

/-- Two runs with the same public data have the same `μ`, and the same inputs. -/
theorem vInputs_pub {s₀ s₀' : State} (hq : VG.Proof.MlDsa.X86.Message.VPub p s₀ s₀') :
    bytesAt s₀.mem ((arg s₀ 0).setWidth 64) p.pkLen = bytesAt s₀'.mem ((arg s₀' 0).setWidth 64) p.pkLen ∧
      VG.Proof.MlDsa.X86.Message.vMu p s₀ = VG.Proof.MlDsa.X86.Message.vMu p s₀' ∧
      bytesAt s₀.mem ((arg s₀ 5).setWidth 64) p.sigLen = bytesAt s₀'.mem ((arg s₀' 5).setWidth 64) p.sigLen := by
  obtain ⟨e₁, e₂, e₃, e₄⟩ := leak4 (by simp only [Proof.MlKem.bytesAt_length])
    (by simp only [Proof.MlKem.bytesAt_length, hq.args 2 (by decide)])
    (by simp only [Proof.MlKem.bytesAt_length, hq.args 4 (by decide)]) hq.leak
  refine ⟨e₁, ?_, e₄⟩
  simp only [VG.Proof.MlDsa.X86.Message.vMu, VG.Proof.MlDsa.X86.Message.hdrBytes, VG.Proof.MlDsa.X86.Message.vlay, e₁, e₂, e₃]
  rw [hq.args 4 (by decide)]

/-- The call of the verification function on `μ`. -/
theorem verifyCall_piece (hp : p ∈ VG.Proof.MlDsa.X86.Message.params) {n : String} {f : Prog isa} (hf : VG.Proof.MlDsa.X86.Message.VerifyFn p f) :
    Piece (VG.Proof.MlDsa.X86.Message.VPre p) (VG.Proof.MlDsa.X86.Message.VPub p) (fun s₀ s => VG.Proof.MlDsa.X86.Message.CtxO (VG.Proof.MlDsa.X86.Message.vlay p) s₀ s ∧ bytesAt s.mem (VG.Proof.MlDsa.X86.Message.vlay p s₀).MU 64 = VG.Proof.MlDsa.X86.Message.vMu p s₀)
      (fun s₀ s => LeafEnd s₀ (VG.Proof.MlDsa.X86.Message.vW p s₀) s ∧ VG.Proof.MlDsa.X86.Message.VB p s₀ s)
      (.seq (.block (VG.Impl.MlDsa.X86.Message.setArgs VG.Proof.MlDsa.X86.Message.verifyArgs)) (Impl.MlKem.X86.callRet VG.Proof.MlDsa.X86.Message.rs4 n f)) := by
  refine VG.Proof.MlDsa.X86.Message.argsRet_piece hf.ver.1 hf.ver.2.1 hf.nosp (by decide) (by decide) (by taint_decide) (VG.Proof.MlDsa.X86.Message.vShape hp).pubL
    (fun _ _ _ h => h.1) (fun _ _ => VG.Proof.MlDsa.X86.Message.verifyArgs_ok) (VG.Proof.MlDsa.X86.Message.vRd p) (VG.Proof.MlDsa.X86.Message.vWr p)
    (fun s₀ s₀' h₀ h₀' hq => ?_) (fun s₀ s h₀ ha => ?_) (fun s₀ s s₁ h₀ ha hs => VG.Proof.MlDsa.X86.Message.verify_callPre h₀ ha.1 hs)
    (fun s₀ s₀' s s' s₁ s₁' h₀ h₀' hq ha ha' hs hs' => ?_) (fun s₀ s s₁ s' h₀ ha hs e₁ e₂ e₃ fr post => ?_)
  · refine ⟨?_, ?_⟩
    · simp only [VG.Proof.MlDsa.X86.Message.vRd, Lay.X32, VG.Proof.MlDsa.X86.Message.vlay, hq.args 0 (by decide), hq.args 5 (by decide), hq.args 6 (by decide)]
    · simp only [VG.Proof.MlDsa.X86.Message.vWr, Lay.E1, VG.Proof.MlDsa.X86.Message.vlay, hq.esp, hq.args 6 (by decide)]
  · have := hf.su
    have := h₀.sp
    show _ ≤ (s₀.gpr .esp - BitVec.ofNat 32 16).toNat
    rw [sub_toNat (by omega)]
    simp only [List.length_cons, List.length_nil]
    omega
  · obtain ⟨hc, hμ⟩ := ha
    obtain ⟨hc', hμ'⟩ := ha'
    have hp' := (VG.Proof.MlDsa.X86.Message.vShape hp).pubL s₀ s₀' h₀ h₀' hq
    obtain ⟨i₁, i₂, i₃⟩ := VG.Proof.MlDsa.X86.Message.vInputs_pub hq
    obtain ⟨a0, a1, a2, a3, eS, bPk, bMu, bSig⟩ := VG.Proof.MlDsa.X86.Message.verify_view h₀ hc hμ hs
    obtain ⟨a0', a1', a2', a3', eS', bPk', bMu', bSig'⟩ := VG.Proof.MlDsa.X86.Message.verify_view h₀' hc' hμ' hs'
    generalize (pushed VG.Proof.MlDsa.X86.Message.rs4 s₁).callEntry = e at a0 a1 a2 a3 eS bPk bMu bSig ⊢
    generalize (pushed VG.Proof.MlDsa.X86.Message.rs4 s₁').callEntry = e' at a0' a1' a2' a3' eS' bPk' bMu' bSig' ⊢
    sig_pub [verifyContract, verifySig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, a0, a1, a2, a3, a0', a1', a2', a3', eS, eS']
    rw [bPk, bMu, bSig, bPk', bMu', bSig', i₁, i₂, i₃]
    exact ⟨by simp only [Lay.E1, hp'.sp], rfl, hq.args 0 (by decide), by rw [hp'.x], hq.args 5 (by decide),
      hq.args 6 (by decide)⟩
  · obtain ⟨hc, hμ⟩ := ha
    have hL := hc.ok
    have R := VG.Proof.MlDsa.X86.Message.vregs h₀ hL
    have hE := R.hE
    have hsp1 : s₁.gpr .esp = (VG.Proof.MlDsa.X86.Message.vlay p s₀).E1 := (SetPost.ctx VG.Proof.MlDsa.X86.Message.verifyArgs_ok hs hc.ctx).esp
    refine ⟨CtxO.leafEnd (VG.Proof.MlDsa.X86.Message.vShape hp) h₀ hc (W := VG.Proof.MlDsa.X86.Message.vW p s₀) (by simp) (rs := VG.Proof.MlDsa.X86.Message.vWr p s₀ ++
        [below (s₁.gpr .esp) (4 * rs4.length + stackUse f + 4)]) (by rw [← hs.2.mem]; exact fr)
        (fun r hr => ?_) ((e₃ .esp (by decide)).trans (hs.esp VG.Proof.MlDsa.X86.Message.verifyArgs_ok)) (e₁.trans hs.2.rd)
        (e₂.trans hs.2.wr), ?_⟩
    · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨(VG.Proof.MlDsa.X86.Message.vlay p s₀).SC, by simp, R.scrSub⟩
      · exact ⟨(VG.Proof.MlDsa.X86.Message.vlay p s₀).STK, by simp, R.argsSub⟩
      · refine ⟨(VG.Proof.MlDsa.X86.Message.vlay p s₀).STK, by simp, ?_⟩
        rw [hsp1]
        have := hf.su
        exact below_sub (by show _ ≤ 132 - 16; simp only [List.length_cons, List.length_nil]; omega)
          (by show 132 - 16 ≤ _; omega)
    · have v := VG.Proof.MlDsa.X86.Message.verify_view h₀ hc hμ hs
      obtain ⟨s₂, -, g₂, post⟩ := post
      obtain ⟨a0, a1, a2, -, -, bPk, bMu, bSig⟩ := v
      generalize (pushed VG.Proof.MlDsa.X86.Message.rs4 s₁).callEntry = e at a0 a1 a2 bPk bMu bSig post
      sig_post [verifyContract, verifySig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
      simp only [arg_withRegions, a0, a1, a2] at post
      rw [bPk, bMu, bSig, Proof.MlKem.X86.setWidth_append32, g₂] at post
      exact ⟨hc.ok.ctxLt, post⟩

end

end VG.Proof.MlDsa.X86.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Message.Verify`. -/
section

/-!
# ML-DSA on x86 (32-bit), `verify_message`: correct and constant time

Untrusted: everything here is checked by Lean. The body past the entry:
`tr = H(pk, 64)`, then `μ = H(tr ‖ 0 ‖ ctx_len ‖ ctx ‖ M, 64)`, then the call
of the verification function on it (`verifyRest_piece`); in the leaf, after
the check (`verifyMessage_piece`); and what that says of the contract's
postcondition (`verifyMessage_verified`).
-/

namespace VG.Proof.MlDsa.X86.Message

open VG VG.X86 VG.Impl.MlDsa.X86.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.X86 (Piece P0 E0 frameR retR LeafEnd LeafPost)
open VG.Spec.Sha3 (bytesAt)
open VG.Spec.MlDsa

section
variable {p : Params}

theorem H_length (s : List Byte) (n : Nat) : (VG.Spec.MlDsa.H s n).length = n :=
  Proof.Sha3.length_squeeze (by decide) (by decide) _ _

/-- `tr`, then `μ`, then the call of the verification function on it. -/
theorem verifyRest_piece (hp : p ∈ VG.Proof.MlDsa.X86.Message.params) {n : String} {f : Prog isa} (hf : VG.Proof.MlDsa.X86.Message.VerifyFn p f)
    {ht₁ ht₂ : Taint.Hint VG.X86.Taint.T}
    (tt₁ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (VG.Impl.MlDsa.X86.Message.setArgs (VG.Proof.MlDsa.X86.Message.absArgs (.arg 0) (.imm p.pkLen) (.imm 0)))) ht₁).isSome =
      true)
    (tt₂ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (VG.Impl.MlDsa.X86.Message.setArgs (VG.Proof.MlDsa.X86.Message.padArgs (.imm (p.pkLen % 136))))) ht₂).isSome =
      true) :
    Piece (VG.Proof.MlDsa.X86.Message.VPre p) (VG.Proof.MlDsa.X86.Message.VPub p) (VG.Proof.MlDsa.X86.Message.CtxO (VG.Proof.MlDsa.X86.Message.vlay p)) (fun s₀ s => LeafEnd s₀ (VG.Proof.MlDsa.X86.Message.vW p s₀) s ∧ VG.Proof.MlDsa.X86.Message.VB p s₀ s)
      (.seq (VG.Impl.MlDsa.X86.Message.trHash p) (.seq (muHash (.off oMU)) (.seq (.block (VG.Impl.MlDsa.X86.Message.setArgs VG.Proof.MlDsa.X86.Message.verifyArgs)) (Impl.MlKem.X86.callRet VG.Proof.MlDsa.X86.Message.rs4 n f)))) := by
  refine Piece.seq (VG.Proof.MlDsa.X86.Message.trHash_piece (VG.Proof.MlDsa.X86.Message.vShape hp).pubL (fun _ _ _ h => h) (fun _ _ => by show 5 ≤ 7; decide)
    (fun _ _ => rfl) tt₁ tt₂) (Piece.seq ((VG.Proof.MlDsa.X86.Message.muHash_piece (lay := VG.Proof.MlDsa.X86.Message.vlay p) (.off oMU)
    (fun s₀ => (VG.Proof.MlDsa.X86.Message.vlay p s₀).X32 + BitVec.ofNat 32 840) (fun s₀ => VG.Spec.MlDsa.H (bytesAt s₀.mem ((arg s₀ 0).setWidth 64) p.pkLen) 64)
    (by taint_decide) (VG.Proof.MlDsa.X86.Message.vShape hp).pubL (fun _ _ _ h => h.1) (fun _ _ => by show 5 ≤ 7; decide) (fun _ _ => rfl) rfl
    (fun s₀ s h₀ hc => hc.ctx.off 840) (fun s₀ s₀' h₀ h₀' hq => by rw [((VG.Proof.MlDsa.X86.Message.vShape hp).pubL s₀ s₀' h₀ h₀' hq).x])
    (fun s₀ s h₀ h => ?_) (fun _ _ => VG.Proof.MlDsa.X86.Message.H_length _ _) (fun s₀ h₀ hL => ?_)).mono
    (fun _ _ _ h => h) fun s₀ s h₀ ⟨hc, hm⟩ => ⟨hc, ?_⟩) (VG.Proof.MlDsa.X86.Message.verifyCall_piece hp hf))
  · rw [VG.Proof.MlDsa.X86.Message.mu_eq h.1.ok, h.2]
    simp only [VG.Proof.MlDsa.X86.Message.keyB]
    rw [VG.Proof.MlDsa.X86.Message.p0_bytes (a := (VG.Proof.MlDsa.X86.Message.vlay p s₀).key.setWidth 64) (n := (VG.Proof.MlDsa.X86.Message.vlay p s₀).keyLen) (by decide) h₀.sp h₀.kPk
      (by show p.pkLen ≤ _; have := h₀.nPk; omega)]
    rfl
  · have hX := hL.x32_lt
    refine ⟨by rw [hL.x32_toNat (by omega)]; omega, by rw [VG.Proof.MlDsa.X86.Message.mu_eq hL]; exact VG.Proof.MlDsa.X86.Message.cov_x hL (e := 840) (k := 64) (by omega),
      by rw [VG.Proof.MlDsa.X86.Message.mu_eq hL]; exact st_mu.symm, by rw [VG.Proof.MlDsa.X86.Message.mu_eq hL]; exact VG.Proof.MlDsa.X86.Message.mu_ks, by rw [VG.Proof.MlDsa.X86.Message.mu_eq hL]; exact VG.Proof.MlDsa.X86.Message.k_mu hL⟩
  · rw [hm]
    simp only [VG.Proof.MlDsa.X86.Message.ctxB, VG.Proof.MlDsa.X86.Message.msgB]
    rw [VG.Proof.MlDsa.X86.Message.p0_bytes (a := (VG.Proof.MlDsa.X86.Message.vlay p s₀).ctx.setWidth 64) (n := (VG.Proof.MlDsa.X86.Message.vlay p s₀).ctxLen.toNat) (by decide) h₀.sp h₀.kCtx
        (by have := (arg s₀ 4).isLt; show (arg s₀ 4).toNat ≤ _; omega),
      VG.Proof.MlDsa.X86.Message.p0_bytes (a := (VG.Proof.MlDsa.X86.Message.vlay p s₀).msg.setWidth 64) (n := (VG.Proof.MlDsa.X86.Message.vlay p s₀).len.toNat) (by decide) h₀.sp h₀.kMsg
        (by have := (arg s₀ 2).isLt; show (arg s₀ 2).toNat ≤ _; omega)]
    rfl

/-- What `verify_message` changes is apart from its frame and return address. -/
theorem verify_hW : ∀ s₀, VG.Proof.MlDsa.X86.Message.VPre p s₀ → ∀ r ∈ VG.Proof.MlDsa.X86.Message.vW p s₀, (frameR s₀).Disjoint r ∧ (VG.Proof.MlKem.X86.retR s₀).Disjoint r := by
  intro s₀ h₀ r hr
  have hsp := h₀.sp
  have fr : Region.Sub (frameR s₀) (VG.Proof.MlDsa.X86.Message.sStk s₀ 132) := by rw [VG.Proof.MlDsa.X86.Message.stk_eq hsp]; exact below_sub (by decide) hsp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨h₀.kScr.sub_left fr, h₀.rScr⟩
  · exact ⟨Proof.MlKem.X86.Top.below_adj (sp := s₀.gpr .esp) (a := 16) (b := 132 - 16) (by omega),
      (Proof.MlKem.X86.Top.ret_below hsp).sub_right (below_inner (a := 132 - 16) (k := 16) (by omega) hsp)⟩

/-- `verify_message`, in its leaf. -/
theorem verifyMessage_piece (hp : p ∈ VG.Proof.MlDsa.X86.Message.params) {n : String} {f : Prog isa} (hf : VG.Proof.MlDsa.X86.Message.VerifyFn p f)
    {ht ht₁ ht₂ : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp]) (.block [.mov .esi (.mem (argAt 6)),
      .alu .add .esi (.imm (BitVec.ofNat 32 (oE p)))]) ht).isSome = true)
    (tt₁ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (VG.Impl.MlDsa.X86.Message.setArgs (VG.Proof.MlDsa.X86.Message.absArgs (.arg 0) (.imm p.pkLen) (.imm 0)))) ht₁).isSome =
      true)
    (tt₂ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (VG.Impl.MlDsa.X86.Message.setArgs (VG.Proof.MlDsa.X86.Message.padArgs (.imm (p.pkLen % 136))))) ht₂).isSome =
      true) (htr : NoSp (VG.Impl.MlDsa.X86.Message.trHash p)) :
    Piece (VG.Proof.MlDsa.X86.Message.VPre p) (VG.Proof.MlDsa.X86.Message.VPub p) (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (fun s => (256 ≤ (arg s₀ 4).toNat ∧
      s.gpr .eax = 2) ∨ VG.Proof.MlDsa.X86.Message.VB p s₀ s) s₀ s') (verifyMessage n f p) :=
  VG.Proof.MlDsa.X86.Message.top_piece (VG.Proof.MlDsa.X86.Message.vShape hp) tt (VG.Proof.MlDsa.X86.Message.vW p) VG.Proof.MlDsa.X86.Message.verify_hW
    (VG.Proof.MlDsa.X86.Message.nosp_seq (NoSp.of_all (by decide +kernel)) (VG.Proof.MlDsa.X86.Message.nosp_ite (NoSp.of_all (by decide +kernel))
      (VG.Proof.MlDsa.X86.Message.nosp_seq (VG.Proof.MlDsa.X86.Message.enter_nosp 6 p) (VG.Proof.MlDsa.X86.Message.nosp_seq htr (VG.Proof.MlDsa.X86.Message.nosp_seq (NoSp.of_all (by decide +kernel))
        (VG.Proof.MlDsa.X86.Message.nosp_seq (NoSp.of_all (by decide +kernel)) (VG.Proof.MlDsa.X86.Message.callRet_nosp hf.nosp)))))))
    (VG.Proof.MlDsa.X86.Message.verifyRest_piece hp hf tt₁ tt₂)

/-- Memory with the arguments `0`, `0x2000`, `0`, `0x2000`, `0`, `0x3000` and
`0x10000` at `0x5004`. -/
def satMemV : Mem := fun a =>
  if a = 0x5009 then 0x20 else if a = 0x5011 then 0x20 else if a = 0x5019 then 0x30 else
  if a = 0x501e then 1 else 0

/-- A state satisfying the precondition of `verify_message`. -/
def verifySat (p : Params) : State :=
  Proof.MlKem.X86.satState VG.Proof.MlDsa.X86.Message.satMemV [⟨0, p.pkLen⟩, ⟨0x2000, 0⟩, ⟨0x2000, 0⟩, ⟨0x3000, p.sigLen⟩]
    [⟨0x10000, VG.Proof.MlDsa.X86.Message.mScrLen p⟩, ⟨0x5004, 28⟩]

theorem verifyMessage_verified (hp : p ∈ VG.Proof.MlDsa.X86.Message.params) {n : String} {f : Prog isa} (hf : VG.Proof.MlDsa.X86.Message.VerifyFn p f)
    {ht ht₁ ht₂ : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp]) (.block [.mov .esi (.mem (argAt 6)),
      .alu .add .esi (.imm (BitVec.ofNat 32 (oE p)))]) ht).isSome = true)
    (tt₁ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (VG.Impl.MlDsa.X86.Message.setArgs (VG.Proof.MlDsa.X86.Message.absArgs (.arg 0) (.imm p.pkLen) (.imm 0)))) ht₁).isSome =
      true)
    (tt₂ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (VG.Impl.MlDsa.X86.Message.setArgs (VG.Proof.MlDsa.X86.Message.padArgs (.imm (p.pkLen % 136))))) ht₂).isSome =
      true) (htr : NoSp (VG.Impl.MlDsa.X86.Message.trHash p)) :
    Verified X86.target (verifyMessage n f p) (verifyMessageContract p X86.abi 132) := by
  refine Piece.verified (((VG.Proof.MlDsa.X86.Message.verifyMessage_piece hp hf tt tt₁ tt₂ htr).pre_mono (fun _ h => VG.Proof.MlDsa.X86.Message.vPre_of h)
    fun _ _ _ _ h => VG.Proof.MlDsa.X86.Message.vpub_of h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hB, -, hax⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [verifyMessageContract, verifyMessageSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [Proof.MlKem.X86.setWidth_append32, hax]
    rcases hB with ⟨h8, h2⟩ | ⟨h8, hout⟩
    · rw [formatMessage_none (by rw [Proof.MlKem.bytesAt_length]; exact h8)]; exact h2
    · rw [formatMessage_some (by rw [Proof.MlKem.bytesAt_length]; exact h8)]
      simp only [verifyInternal, messageRep, pkTr, Proof.MlKem.bytesAt_length]
      simp only [VG.Proof.MlDsa.X86.Message.vMu, VG.Proof.MlDsa.X86.Message.hdrBytes, VG.Proof.MlDsa.X86.Message.vlay, List.append_assoc] at hout
      simp only [List.append_assoc]
      exact hout
  · simp only [VG.Proof.MlDsa.X86.Message.params, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨VG.Proof.MlDsa.X86.Message.verifySat mlDsa44, by sig_sat_check [verifyMessageContract, verifyMessageSig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes, VG.Proof.MlDsa.X86.Message.verifySat, Proof.MlKem.X86.satState, VG.Proof.MlDsa.X86.Message.satMemV]⟩
    · exact ⟨VG.Proof.MlDsa.X86.Message.verifySat mlDsa65, by sig_sat_check [verifyMessageContract, verifyMessageSig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes, VG.Proof.MlDsa.X86.Message.verifySat, Proof.MlKem.X86.satState, VG.Proof.MlDsa.X86.Message.satMemV]⟩
    · exact ⟨VG.Proof.MlDsa.X86.Message.verifySat mlDsa87, by sig_sat_check [verifyMessageContract, verifyMessageSig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes, VG.Proof.MlDsa.X86.Message.verifySat, Proof.MlKem.X86.satState, VG.Proof.MlDsa.X86.Message.satMemV]⟩

end

end VG.Proof.MlDsa.X86.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Message.Verified`. -/
section

/-!
# ML-DSA on x86 (32-bit), `sign_message` and `verify_message`: the functions

Untrusted: everything here is checked by Lean. `vg_mldsa{44,65,87}_sign_message`
and `_verify_message`, calling `vg_mldsa{44,65,87}_sign` and `_verify`
(`sign44Fn`, `verify44Fn`, …), meet `signMessageContract p X86.abi 136` and
`verifyMessageContract p X86.abi 132` (`signMessage44_verified`, …).
-/

namespace VG.Proof.MlDsa.X86.Message

open VG VG.X86 VG.Impl.MlDsa.X86.Message
open VG.Spec.MlDsa

/-! ## The functions on `μ` -/

theorem sign44Fn : VG.Proof.MlDsa.X86.Message.SignFn mlDsa44 (Impl.MlDsa.X86.Sign.sign Sign.prims mlDsa44) :=
  ⟨Sign.sign44_verified, NoSp.of_all (by decide +kernel), by decide +kernel⟩
theorem sign65Fn : VG.Proof.MlDsa.X86.Message.SignFn mlDsa65 (Impl.MlDsa.X86.Sign.sign Sign.prims mlDsa65) :=
  ⟨Sign.sign65_verified, NoSp.of_all (by decide +kernel), by decide +kernel⟩
theorem sign87Fn : VG.Proof.MlDsa.X86.Message.SignFn mlDsa87 (Impl.MlDsa.X86.Sign.sign Sign.prims mlDsa87) :=
  ⟨Sign.sign87_verified, NoSp.of_all (by decide +kernel), by decide +kernel⟩

theorem verify44Fn : VG.Proof.MlDsa.X86.Message.VerifyFn mlDsa44 Impl.MlDsa.X86.Verify.verify44 :=
  ⟨Verify.verify44_verified, NoSp.of_all (by decide +kernel), by decide +kernel⟩
theorem verify65Fn : VG.Proof.MlDsa.X86.Message.VerifyFn mlDsa65 Impl.MlDsa.X86.Verify.verify65 :=
  ⟨Verify.verify65_verified, NoSp.of_all (by decide +kernel), by decide +kernel⟩
theorem verify87Fn : VG.Proof.MlDsa.X86.Message.VerifyFn mlDsa87 Impl.MlDsa.X86.Verify.verify87 :=
  ⟨Verify.verify87_verified, NoSp.of_all (by decide +kernel), by decide +kernel⟩

/-! ## The functions on messages -/

theorem signMessage44_verified :
    Verified X86.target (signMessage sign44Api.name (Impl.MlDsa.X86.Sign.sign Sign.prims mlDsa44) mlDsa44)
      (signMessageContract mlDsa44 X86.abi 136) :=
  VG.Proof.MlDsa.X86.Message.signMessage_verified (List.mem_cons_self ..) VG.Proof.MlDsa.X86.Message.sign44Fn (by taint_decide)
theorem signMessage65_verified :
    Verified X86.target (signMessage sign65Api.name (Impl.MlDsa.X86.Sign.sign Sign.prims mlDsa65) mlDsa65)
      (signMessageContract mlDsa65 X86.abi 136) :=
  VG.Proof.MlDsa.X86.Message.signMessage_verified (List.mem_cons_of_mem _ (List.mem_cons_self ..)) VG.Proof.MlDsa.X86.Message.sign65Fn (by taint_decide)
theorem signMessage87_verified :
    Verified X86.target (signMessage sign87Api.name (Impl.MlDsa.X86.Sign.sign Sign.prims mlDsa87) mlDsa87)
      (signMessageContract mlDsa87 X86.abi 136) :=
  VG.Proof.MlDsa.X86.Message.signMessage_verified (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) VG.Proof.MlDsa.X86.Message.sign87Fn
    (by taint_decide)

theorem verifyMessage44_verified :
    Verified X86.target (verifyMessage verify44Api.name Impl.MlDsa.X86.Verify.verify44 mlDsa44)
      (verifyMessageContract mlDsa44 X86.abi 132) :=
  VG.Proof.MlDsa.X86.Message.verifyMessage_verified (List.mem_cons_self ..) VG.Proof.MlDsa.X86.Message.verify44Fn (by taint_decide) (by taint_decide) (by taint_decide)
    (NoSp.of_all (by decide +kernel))
theorem verifyMessage65_verified :
    Verified X86.target (verifyMessage verify65Api.name Impl.MlDsa.X86.Verify.verify65 mlDsa65)
      (verifyMessageContract mlDsa65 X86.abi 132) :=
  VG.Proof.MlDsa.X86.Message.verifyMessage_verified (List.mem_cons_of_mem _ (List.mem_cons_self ..)) VG.Proof.MlDsa.X86.Message.verify65Fn (by taint_decide)
    (by taint_decide) (by taint_decide) (NoSp.of_all (by decide +kernel))
theorem verifyMessage87_verified :
    Verified X86.target (verifyMessage verify87Api.name Impl.MlDsa.X86.Verify.verify87 mlDsa87)
      (verifyMessageContract mlDsa87 X86.abi 132) :=
  VG.Proof.MlDsa.X86.Message.verifyMessage_verified (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) VG.Proof.MlDsa.X86.Message.verify87Fn
    (by taint_decide) (by taint_decide) (by taint_decide) (NoSp.of_all (by decide +kernel))

end VG.Proof.MlDsa.X86.Message

end
