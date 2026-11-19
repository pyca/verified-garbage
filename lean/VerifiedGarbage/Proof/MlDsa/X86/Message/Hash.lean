module

public import VerifiedGarbage.Proof.MlKem.X86.Keccak
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.MlKem.X86.SampleSetup
import VerifiedGarbage.Proof.Sha3.X86.Stream.Absorb
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.MlKem.X86.Keccak
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.MlKem.X86.SampleSetup
meta import VerifiedGarbage.Proof.Sha3.X86.Stream.Absorb
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
public import VerifiedGarbage.Proof.Framework.X86.Wp
public import VerifiedGarbage.Proof.MlKem.X86.Common
public import VerifiedGarbage.Impl.MlDsa.X86.Message
public import VerifiedGarbage.Proof.MlKem.X86.Leaf
import VerifiedGarbage.Proof.MlKem.X86.CallRet
import VerifiedGarbage.Proof.Sha3.X86.Permute
public import VerifiedGarbage.Proof.MlDsa.Message.Common
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.TCB.X86.State
meta import VerifiedGarbage.Proof.Framework.X86.Wp
meta import VerifiedGarbage.Proof.MlKem.X86.Common
meta import VerifiedGarbage.Impl.MlDsa.X86.Message
meta import VerifiedGarbage.Proof.MlKem.X86.Leaf
meta import VerifiedGarbage.Proof.MlKem.X86.CallRet
meta import VerifiedGarbage.Proof.Sha3.X86.Permute
meta import VerifiedGarbage.Proof.MlDsa.Message.Common
meta import VerifiedGarbage.Proof.Framework.X86.Call
meta import VerifiedGarbage.Proof.Framework.X86.Exec
meta import VerifiedGarbage.TCB.X86.State

/-! ### `MlDsa.X86.Message.Call`, which this module and modules that import it used -/

section

/-! ### `MlDsa.X86.Message.Layout`, which this module and modules that import it used -/

section

/-!
# ML-DSA on x86 (32-bit), `sign_message` and `verify_message_cached`: where everything is

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

@[expose] public section

namespace VG.Proof.MlDsa.X86.Message

open VG VG.X86 VG.Impl.MlDsa.X86.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.X86 (E0 P0 frameR retR)
open VG.Spec.Sha3 (bytesAt)

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

variable (L : Lay)

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

variable {L : Lay}

theorem x32_lt (h : L.Ok) : L.X32.toNat + 1024 ≤ 2 ^ 32 := by
  have := h.nScr; have := h.hE
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := L.E) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  omega_arith

/-- `X` in `scratch`. -/
theorem x_eq (h : L.Ok) : L.X = L.scr.setWidth 64 + BitVec.ofNat 64 L.E :=
  Proof.MlKem.X86.ea_off (by have := h.nScr; have := h.hE; omega_arith)

/-- An address in the 1 KiB, as an instruction computes it from `esi`. -/
theorem xo (h : L.Ok) {o : Nat} (ho : o < 1024) : addr L.X32 o = L.X + BitVec.ofNat 64 o :=
  Proof.MlKem.X86.ea_off (by have := h.x32_lt; omega_using [ho, this])

theorem x32_toNat (h : L.Ok) {o : Nat} (ho : o < 1024) : (L.X32 + BitVec.ofNat 32 o).toNat = L.X32.toNat + o := by
  have := h.x32_lt
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega_using [ho]), Nat.mod_eq_of_lt (by omega_using [ho, this])]

theorem xs_sc (h : L.Ok) : Within ⟨L.X, 1024⟩ L.SC := ⟨L.E, h.x_eq, h.hE⟩

theorem sub_sc (h : L.Ok) {e k : Nat} (h₂ : e + k ≤ 1024) : Region.Sub ⟨L.X + BitVec.ofNat 64 e, k⟩ L.SC :=
  (Within.trans (within_off L.X h₂) h.xs_sc).sub

/-- The calls' stack lies in the contract's. -/
theorem stk_sub (h : L.Ok) : Region.Sub L.STK (below L.SP L.N) := by
  have := h.nSP; have := h.hN
  rw [Lay.STK, Lay.E1]
  exact below_inner (by omega_using [this]) (by omega_arith)

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
  exact Offset.contains_base _ (by omega_arith) (by omega_arith)

/-- What lies within the first 904 bytes of `X`, or in `STK`, is apart from the two bytes. -/
theorem hdr_disj (h : L.Ok) {r : Region} (hr : Within r L.W ∨ Region.Sub r L.STK) :
    Region.Disjoint ⟨L.X + BitVec.ofNat 64 944, 2⟩ r := by
  rcases hr with hr | hr
  · obtain ⟨o, hb, hl⟩ := hr
    obtain ⟨b, k⟩ := r
    simp only at hb hl
    subst hb
    exact Offset.disjoint _ (.inr (by omega_using [hl])) (by omega_using []) (by omega_using [hl])
  · exact (h.kSC.symm.sub_left (h.sub_sc (by omega_using []))).sub_right hr

/-- Argument `i`, as an instruction in the body addresses it. -/
theorem argAt_eq (L : Lay) (i : Nat) :
    addr L.E1 (20 + 4 * i) = (L.SP + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 := by
  simp only [addr, Lay.E1]
  congr 1
  rw [show (20 + 4 * i : Nat) = 16 + (4 + 4 * i) by omega_using [], ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc,
    BitVec.sub_add_cancel]

/-- Argument `i` lies in the arguments. -/
theorem argIn (h : L.Ok) {i : Nat} (hi : i < L.nA) :
    L.ARGS.Contains ((L.SP + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64) 4 := by
  have := h.fArgs
  rw [Lay.ARGS, Proof.MlKem.X86.ea_off (x := L.SP) (d := 4) (by omega_using [hi, this]),
    Proof.MlKem.X86.ea_off (x := L.SP) (d := 4 + 4 * i) (by omega_using [hi, this])]
  exact Offset.contains _ (by omega_using []) (by omega_using [hi]) (by omega_using [this])

end Lay.Ok

/-! ## In the leaf's body -/

/-- The state in the leaf's body, from the entry's stores to the end: `m₁`
is the memory after the frame's push. -/
structure Ctx (L : Lay) (m₁ : Mem) (t : State) : Prop where
  rd : t.rd = L.rd
  wr : t.wr = below L.SP 16 :: L.wr
  esp : t.gpr .esp = L.E1
  esi : t.gpr .esi = L.X32
  hdr : bytesAt t.mem (L.X + BitVec.ofNat 64 944) 2 = [0, BitVec.ofNat 8 L.ctxLen.toNat]
  args : ∀ i < L.nA, t.mem.readW ((L.SP + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64) 32 = L.argv.getD i 0
  frame : Frame [L.SC, L.STK] m₁ t.mem

namespace Ctx

variable {L : Lay} {m₁ : Mem} {t t' : State}

/-- Code that writes only registers but `esp` and `esi`. -/
theorem regs (hc : Ctx L m₁ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hm : t'.mem = t.mem)
    (hsp : t'.gpr .esp = t.gpr .esp) (hsi : t'.gpr .esi = t.gpr .esi) : Ctx L m₁ t' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.esp, hsi.trans hc.esi, by rw [hm]; exact hc.hdr,
    fun i hi => by rw [hm]; exact hc.args i hi, by rw [hm]; exact hc.frame⟩

/-- Code that writes memory only within the first 904 bytes of `X` and in `STK`. -/
theorem keep (hc : Ctx L m₁ t) (hL : L.Ok) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hsp : t'.gpr .esp = t.gpr .esp) (hsi : t'.gpr .esi = t.gpr .esi) {rs : List Region}
    (hf : Frame rs t.mem t'.mem) (hrs : ∀ r ∈ rs, Within r L.W ∨ Region.Sub r L.STK) : Ctx L m₁ t' := by
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
theorem bytesAt_eq (hc : Ctx L m₁ t) {p : Addr} {n : Nat} (hx : L.SC.Disjoint ⟨p, n⟩)
    (hk : L.STK.Disjoint ⟨p, n⟩) (hn : n ≤ 2 ^ 64) : bytesAt t.mem p n = bytesAt m₁ p n :=
  Proof.MlKem.bytesAt_congr fun _ hi => Frame.bytes (R := ⟨p, n⟩) hc.frame (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hx.symm
    · exact hk.symm) hn hi

end Ctx

end VG.Proof.MlDsa.X86.Message

end

end

/-! ### `MlDsa.X86.Message.Args`, which only this module used -/

section

/-!
# ML-DSA on x86 (32-bit), `sign_message` and `verify_message_cached`: the moves of a call's arguments

Untrusted: everything here is checked by Lean. Each argument's value
(`Arg.val`): an argument of the function (at `[esp + 20 + 4i]`), plus an
offset, an offset from `esi`, an immediate, or `eax`. The moves of a list
of arguments into distinct registers but `esp` and `esi`, with `eax` read
only before it is written (`argsOk`), leave each its value and change
nothing else (`setArgs_ok`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Message

open VG VG.X86 VG.X86.Wp VG.Impl.MlDsa.X86.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.X86 (Only)

/-- The value of an argument in the state `s`. -/
def _root_.VG.Impl.MlDsa.X86.Message.Arg.val (s : State) : Arg → BitVec 32
  | .arg i => s.mem.readW (addr (s.gpr .esp) (20 + 4 * i)) 32
  | .argOff i o => s.mem.readW (addr (s.gpr .esp) (20 + 4 * i)) 32 + BitVec.ofNat 32 o
  | .off o => s.gpr .esi + BitVec.ofNat 32 o
  | .imm v => BitVec.ofNat 32 v
  | .ret => s.gpr .eax

/-- An argument of the function among its `n`. -/
def _root_.VG.Impl.MlDsa.X86.Message.Arg.ok (n : Nat) : Arg → Bool
  | .arg i => decide (i < n)
  | .argOff i _ => decide (i < n)
  | _ => true

def _root_.VG.Impl.MlDsa.X86.Message.Arg.isRet : Arg → Bool
  | .ret => true
  | _ => false

/-- The arguments of the function are readable. -/
abbrev AOk (n : Nat) (s : State) : Prop := ∀ i < n, InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) (20 + 4 * i)) 4

theorem only_upd {s s' : State} {d : Reg} {v : BitVec 32} (u : Upd s s' d v) : Only [d] s s' :=
  ⟨fun r hr => u.other r (by simpa using hr), u.mem, u.rd, u.wr⟩

theorem Arg.set_ok {n : Nat} (d : Reg) (a : Arg) (ha : a.ok n = true) (s : State) (hx : AOk n s) :
    WP isa (.block (a.set d)) s fun s1 => s1.gpr d = a.val s ∧ Only [d] s s1 := by
  cases a with
  | arg i =>
    simp only [Arg.ok, decide_eq_true_eq] at ha
    exact wp_ldm (b := .esp) rfl (hx i ha) fun s1 u => WP.block_nil ⟨u.gpr, only_upd u⟩
  | argOff i o =>
    simp only [Arg.ok, decide_eq_true_eq] at ha
    refine wp_ldm (b := .esp) rfl (hx i ha) fun s1 u1 => wp_addi fun s2 u2 => WP.block_nil ⟨?_, ?_⟩
    · rw [u2.gpr, u1.gpr]; rfl
    · exact ((only_upd u1).trans (only_upd u2)).mono fun r hr => by simpa using hr
  | off o =>
    refine wp_mov fun s1 u1 => wp_addi fun s2 u2 => WP.block_nil ⟨?_, ?_⟩
    · rw [u2.gpr, u1.gpr]; rfl
    · exact ((only_upd u1).trans (only_upd u2)).mono fun r hr => by simpa using hr
  | imm v => exact wp_movi fun s1 u => WP.block_nil ⟨u.gpr, only_upd u⟩
  | ret => exact wp_mov fun s1 u => WP.block_nil ⟨u.gpr, only_upd u⟩

/-- Distinct registers but `esp` and `esi`, each argument fit, and `eax`
read only before it is written. -/
def argsOk (n : Nat) : List (Reg × Arg) → Bool
  | [] => true
  | (d, a) :: as => a.ok n && d != .esp && d != .esi &&
      as.all (fun da => da.1 != d && (d != .eax || !da.2.isRet)) && argsOk n as

/-- The value of an argument is the same after a move into another register
(not `esp` or `esi`, and not `eax` if the argument is `eax`). -/
theorem Arg.val_only {d : Reg} (hd : d ≠ .esp) (hs : d ≠ .esi) {s s1 : State} (o : Only [d] s s1) (a : Arg)
    (ha : d ≠ .eax ∨ a.isRet = false) : a.val s1 = a.val s := by
  have hsp : s1.gpr .esp = s.gpr .esp := o.gpr _ (by simp only [List.mem_singleton]; exact fun h => hd h.symm)
  have hsi : s1.gpr .esi = s.gpr .esi := o.gpr _ (by simp only [List.mem_singleton]; exact fun h => hs h.symm)
  cases a with
  | ret =>
    simp only [Arg.isRet, Bool.true_eq_false, or_false] at ha
    simp only [Arg.val]
    exact o.gpr _ (by simp only [List.mem_singleton]; exact fun h => ha h.symm)
  | _ => simp only [Arg.val, hsp, hsi, o.mem]

theorem AOk.only {n : Nat} {d : Reg} (hd : d ≠ .esp) {s s1 : State} (o : Only [d] s s1) (h : AOk n s) :
    AOk n s1 := by
  intro i hi
  rw [o.rd, o.wr, o.gpr _ (by simp only [List.mem_singleton]; exact fun h => hd h.symm)]
  exact h i hi

/-- The moves of the arguments `as`. -/
theorem setArgs_ok {n : Nat} : ∀ (as : List (Reg × Arg)), argsOk n as = true → ∀ s : State, AOk n s →
    WP isa (.block (setArgs as)) s fun s1 => (∀ da ∈ as, s1.gpr da.1 = da.2.val s) ∧ Only (as.map (·.1)) s s1
  | [], _, s, _ => WP.block_nil ⟨fun _ h => by simp at h, Only.refl _ _⟩
  | (d, a) :: as, h, s, hx => by
    simp only [argsOk, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true, Bool.or_eq_true,
      Bool.not_eq_true'] at h
    obtain ⟨⟨⟨⟨ha, hd⟩, hs⟩, hall⟩, hrest⟩ := h
    simp only [setArgs, List.flatMap_cons]
    rw [WP.block_append_iff]
    refine WP.mono (Arg.set_ok d a ha s hx) fun s1 ⟨h1, o1⟩ => ?_
    refine WP.mono (setArgs_ok as hrest s1 (hx.only hd o1)) fun s2 ⟨h2, o2⟩ => ⟨fun da hda => ?_, ?_⟩
    · rcases List.mem_cons.mp hda with rfl | hda
      · rw [o2.gpr _ (fun hm => by
          obtain ⟨x, hx', hx''⟩ := List.mem_map.mp hm
          exact (hall x hx').1 hx''), h1]
      · rw [h2 da hda, Arg.val_only hd hs o1 da.2 ((hall da hda).2.elim .inl fun h' => .inr h')]
    · exact (o1.trans o2).mono (by simp)

/-! ## In `Ctx` -/

section
variable {L : Lay} {m₁ : Mem} {t : State}

theorem Ctx.aOk (hc : Ctx L m₁ t) (hL : L.Ok) : AOk L.nA t := fun i hi => by
  rw [hc.esp, Lay.Ok.argAt_eq, hc.rd, hc.wr]
  exact ⟨L.ARGS, List.mem_append_right _ (List.mem_cons_of_mem _ hL.inArgs), hL.argIn hi⟩

theorem Ctx.off (hc : Ctx L m₁ t) (o : Nat) : (Arg.off o).val t = L.X32 + BitVec.ofNat 32 o := by
  simp only [Arg.val, hc.esi]

/-- Argument `i` of the function. -/
theorem Ctx.argV (hc : Ctx L m₁ t) {i : Nat} (hi : i < L.nA) : (Arg.arg i).val t = L.argv.getD i 0 := by
  simp only [Arg.val, hc.esp, Lay.Ok.argAt_eq]; exact hc.args i hi

theorem Ctx.argOffV (hc : Ctx L m₁ t) {i : Nat} (hi : i < L.nA) (o : Nat) :
    (Arg.argOff i o).val t = L.argv.getD i 0 + BitVec.ofNat 32 o := by
  simp only [Arg.val, hc.esp, Lay.Ok.argAt_eq]; rw [hc.args i hi]

end

end VG.Proof.MlDsa.X86.Message

end

end


/-!
# ML-DSA on x86 (32-bit), `sign_message` and `verify_message_cached`: calls, correct and constant time

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

@[expose] public section

namespace VG.Proof.MlDsa.X86.Message

open VG VG.X86 VG.Impl.MlDsa.X86.Message
open VG.Proof.MlKem.X86 (Only Piece P0)

/-- Two layouts with the same public data. -/
structure PubL (L L' : Lay) : Prop where
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
structure CtxO (lay : State → Lay) (s₀ s : State) : Prop where
  ok : (lay s₀).Ok
  ctx : Ctx (lay s₀) (P0 s₀).mem s

/-- The moves of the arguments `as` from `s` to `s₁`. -/
def SetPost (as : List (Reg × Arg)) (s s₁ : State) : Prop :=
  (∀ da ∈ as, s₁.gpr da.1 = da.2.val s) ∧ Only (as.map (·.1)) s s₁

theorem argsOk_regs {n : Nat} : ∀ {as : List (Reg × Arg)}, argsOk n as = true →
    ∀ r ∈ as.map (·.1), r ≠ .esp ∧ r ≠ .esi
  | [], _, _, h => by simp at h
  | (d, a) :: as, h, r, hr => by
    simp only [argsOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    simp only [List.map_cons, List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact ⟨h.1.1.1.2, h.1.1.2⟩
    · exact argsOk_regs h.2 r hr

theorem SetPost.esp {n : Nat} {as : List (Reg × Arg)} (ho : argsOk n as = true) {s s₁ : State}
    (h : SetPost as s s₁) : s₁.gpr .esp = s.gpr .esp :=
  h.2.gpr _ fun hm => (argsOk_regs ho _ hm).1 rfl

theorem SetPost.esi {n : Nat} {as : List (Reg × Arg)} (ho : argsOk n as = true) {s s₁ : State}
    (h : SetPost as s s₁) : s₁.gpr .esi = s.gpr .esi :=
  h.2.gpr _ fun hm => (argsOk_regs ho _ hm).2 rfl

section
variable {Pre : State → Prop} {Pub : State → State → Prop} {lay : State → Lay} {A B : State → State → Prop}

/-- The moves of a call's arguments. -/
theorem setArgs_piece (as : List (Reg × Arg)) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (setArgs as)) ht).isSome = true)
    (hpub : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → PubL (lay s₀) (lay s₀'))
    (hA : ∀ s₀ s, Pre s₀ → A s₀ s → CtxO lay s₀ s)
    (hok : ∀ s₀, Pre s₀ → argsOk (lay s₀).nA as = true) :
    Piece Pre Pub A (fun s₀ s₁ => ∃ s, A s₀ s ∧ SetPost as s s₁) (.block (setArgs as)) :=
  Piece.taint [.esp, .esi] (fun s₀ s h₀ ha => by
      have h := hA s₀ s h₀ ha
      exact (setArgs_ok as (hok s₀ h₀) s (h.ctx.aOk h.ok)).mono fun s₁ h₁ => ⟨s, ha, h₁⟩)
    (fun s₀ s₀' s s' h₀ h₀' hq ha ha' r hr => by
      have h := hA s₀ s h₀ ha
      have h' := hA s₀' s' h₀' ha'
      have hp := hpub s₀ s₀' h₀ h₀' hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.ctx.esp, h'.ctx.esp, Lay.E1, Lay.E1, hp.sp]
      · rw [h.ctx.esi, h'.ctx.esi, hp.x]) tt

/-- A call of verified code, returning a value in `eax`, with the arguments `as`. -/
theorem argsRet_piece {as : List (Reg × Arg)} {rs : List Reg} {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (hsp : NoSp c) (hne : rs ≠ []) (hrs : Reg.esp ∉ rs)
    {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (setArgs as)) ht).isSome = true)
    (hpub : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → PubL (lay s₀) (lay s₀'))
    (hA : ∀ s₀ s, Pre s₀ → A s₀ s → CtxO lay s₀ s)
    (hok : ∀ s₀, Pre s₀ → argsOk (lay s₀).nA as = true)
    (rd wr : State → List Region)
    (hrw : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → rd s₀ = rd s₀' ∧ wr s₀ = wr s₀')
    (hd : ∀ s₀ s, Pre s₀ → A s₀ s → 4 * rs.length + stackUse c + 4 ≤ (lay s₀).E1.toNat)
    (hk : ∀ s₀ s s₁, Pre s₀ → A s₀ s → SetPost as s s₁ → CallPre k rs (rd s₀) (wr s₀) s₁)
    (hkp : ∀ s₀ s₀' s s' s₁ s₁', Pre s₀ → Pre s₀' → Pub s₀ s₀' → A s₀ s → A s₀' s' →
      SetPost as s s₁ → SetPost as s' s₁' →
      k.pub ((pushed rs s₁).callEntry.withRegions (rd s₀) (wr s₀))
        ((pushed rs s₁').callEntry.withRegions (rd s₀) (wr s₀)))
    (hQ : ∀ s₀ s s₁ s', Pre s₀ → A s₀ s → SetPost as s s₁ → s'.rd = s₁.rd → s'.wr = s₁.wr →
      (∀ r ∈ calleeSaved, s'.gpr r = s₁.gpr r) →
      Frame (wr s₀ ++ [below (s₁.gpr .esp) (4 * rs.length + stackUse c + 4)]) s₁.mem s'.mem →
      (∃ s₂ : State, Frame [below (s₁.gpr .esp) (4 * rs.length)] s₂.mem s'.mem ∧ s₂.gpr .eax = s'.gpr .eax ∧
        k.post ((pushed rs s₁).callEntry.withRegions (rd s₀) (wr s₀)) s₂) → B s₀ s') :
    Piece Pre Pub A B (.seq (.block (setArgs as)) (Impl.MlKem.X86.callRet rs n c)) := by
  refine Piece.seq (setArgs_piece as tt hpub hA hok) (Piece.callRet hv hct hsp hne hrs rd wr ?_ ?_ ?_ ?_)
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
theorem argsWith_piece {as : List (Reg × Arg)} {rs : List Reg} {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (hsp : NoSp c) (hne : rs ≠ []) (hrs : Reg.esp ∉ rs)
    {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (setArgs as)) ht).isSome = true)
    (hpub : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → PubL (lay s₀) (lay s₀'))
    (hA : ∀ s₀ s, Pre s₀ → A s₀ s → CtxO lay s₀ s)
    (hok : ∀ s₀, Pre s₀ → argsOk (lay s₀).nA as = true)
    (rd wr : State → List Region)
    (hrw : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → rd s₀ = rd s₀' ∧ wr s₀ = wr s₀')
    (hd : ∀ s₀ s, Pre s₀ → A s₀ s → 4 * rs.length + stackUse c + 4 ≤ (lay s₀).E1.toNat)
    (hk : ∀ s₀ s s₁, Pre s₀ → A s₀ s → SetPost as s s₁ → CallPre k rs (rd s₀) (wr s₀) s₁)
    (hkp : ∀ s₀ s₀' s s' s₁ s₁', Pre s₀ → Pre s₀' → Pub s₀ s₀' → A s₀ s → A s₀' s' →
      SetPost as s s₁ → SetPost as s' s₁' →
      k.pub ((pushed rs s₁).callEntry.withRegions (rd s₀) (wr s₀))
        ((pushed rs s₁').callEntry.withRegions (rd s₀) (wr s₀)))
    (hQ : ∀ s₀ s s₁ s', Pre s₀ → A s₀ s → SetPost as s s₁ → s'.rd = s₁.rd → s'.wr = s₁.wr →
      (∀ r ∈ calleeSaved, s'.gpr r = s₁.gpr r) →
      Frame (wr s₀ ++ [below (s₁.gpr .esp) (4 * rs.length + stackUse c + 4)]) s₁.mem s'.mem →
      (∃ s₂ : State, Frame [below (s₁.gpr .esp) (4 * rs.length)] s₂.mem s'.mem ∧
        k.post ((pushed rs s₁).callEntry.withRegions (rd s₀) (wr s₀)) s₂) → B s₀ s') :
    Piece Pre Pub A B (.seq (.block (setArgs as)) (Impl.MlKem.X86.callWith rs n c)) := by
  refine Piece.seq (setArgs_piece as tt hpub hA hok) (Piece.callWith hv hct hsp hne hrs rd wr ?_ ?_ ?_ ?_)
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

end

/-!
# ML-DSA on x86 (32-bit), `sign_message` and `verify_message_cached`: SHAKE256 through the sponge functions

Untrusted: everything here is checked by Lean. In `Ctx`: zeroing the Keccak
state at `X` (`zeroSt_ok`), and the calls of `vg_keccak_absorb` (keeping the
position it returns in `eax`), `vg_keccak_pad` and `vg_keccak_squeeze` on it,
with their working space at `X + 200` (`kabs_ok`, `kpad_ok`, `ksqz_ok`, from
ML-KEM's lemmas on their calls, `Proof/MlKem/X86/Keccak.lean`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Message

open VG VG.X86 VG.X86.Wp VG.Impl.MlDsa.X86.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.X86 (Piece Only AbsArgs KBufs PadArgs absorb_pre absorb_post pad_pre pad_post squeeze_pre squeeze_post
  absorb_stack pad_stack squeeze_stack absorb_nosp pad_nosp squeeze_nosp toNat_ofNat32)
open VG.Proof.Sha3.X86 (reg32)
open VG.Spec.Sha3 (bytesAt stateAt rates absorb pad squeezeFrom Repr)

section
variable {L : Lay} {m₁ : Mem}

theorem x0 (L : Lay) : L.X + BitVec.ofNat 64 0 = L.X := BitVec.add_zero _
theorem x0' (L : Lay) : L.X32 + BitVec.ofNat 32 0 = L.X32 := BitVec.add_zero _

theorem st_ks : Region.Disjoint ⟨L.ST, 200⟩ ⟨L.KS, 640⟩ := by
  have := Offset.disjoint L.X (d := 0) (n := 200) (e := 200) (k := 640) (by omega_using []) (by omega_using []) (by omega_using [])
  simpa only [x0] using this

theorem st_mu : Region.Disjoint ⟨L.ST, 200⟩ ⟨L.MU, 64⟩ := by
  have := Offset.disjoint L.X (d := 0) (n := 200) (e := 840) (k := 64) (by omega_using []) (by omega_using []) (by omega_using [])
  simpa only [x0] using this

theorem mu_ks : Region.Disjoint ⟨L.MU, 64⟩ ⟨L.KS, 640⟩ :=
  Offset.disjoint L.X (d := 840) (n := 64) (e := 200) (k := 640) (by omega_using []) (by omega_using []) (by omega_using [])

theorem w_st : Within ⟨L.ST, 200⟩ L.W := within_base _ (by omega_using [])
theorem w_ks : Within ⟨L.KS, 640⟩ L.W := within_off _ (by omega_using [])
theorem w_mu : Within ⟨L.MU, 64⟩ L.W := within_off _ (by omega_using [])

theorem k_st (hL : L.Ok) : L.STK.Disjoint ⟨L.ST, 200⟩ := by
  have := hL.stk_x (e := 0) (k := 200) (by omega_using []); simpa only [x0] using this
theorem k_ks (hL : L.Ok) : L.STK.Disjoint ⟨L.KS, 640⟩ := hL.stk_x (by omega_using [])
theorem k_mu (hL : L.Ok) : L.STK.Disjoint ⟨L.MU, 64⟩ := hL.stk_x (by omega_using [])

/-- The 40 bytes a call of a sponge function uses lie in `STK`. -/
theorem b40 (hL : L.Ok) : Region.Sub (below L.E1 40) L.STK := by
  have := hL.nSP; have := hL.hN
  exact below_sub (by omega_using [this]) (by rw [Lay.E1, sub_toNat (by omega_arith)]; omega_arith)

theorem e40 (hL : L.Ok) : 40 ≤ L.E1.toNat := by
  have := hL.nSP; have := hL.hN
  rw [Lay.E1, sub_toNat (by omega_arith)]; omega_arith

theorem ks_eq (hL : L.Ok) : (L.X32 + BitVec.ofNat 32 200).setWidth 64 = L.KS := hL.xo (by decide)
theorem regKS (hL : L.Ok) : reg32 (L.X32 + BitVec.ofNat 32 200) 640 = ⟨L.KS, 640⟩ := by
  show (⟨_, 640⟩ : Region) = _; rw [ks_eq hL]
theorem mu_eq (hL : L.Ok) : (L.X32 + BitVec.ofNat 32 840).setWidth 64 = L.MU := hL.xo (by decide)

theorem cov_x (hL : L.Ok) {e k : Nat} (h₂ : e + k ≤ 1024) :
    ∃ R ∈ L.rd ++ L.wr, Within ⟨L.X + BitVec.ofNat 64 e, k⟩ R := by
  obtain ⟨R, hR, hw⟩ := hL.covX h₂; exact ⟨R, List.mem_append_right _ hR, hw⟩

/-- `Within` as ML-KEM's lemmas take it, in the body's writable regions. -/
theorem withinW {t : State} (hc : Ctx L m₁ t) {r : Region} (h : ∃ R ∈ L.wr, Within r R) :
    Proof.MlKem.X86.Within r t.wr := by
  obtain ⟨R, hR, o, hb, hl⟩ := h
  exact ⟨R, by rw [hc.wr]; exact List.mem_cons_of_mem _ hR, o, hb, hl⟩

theorem withinRW {t : State} (hc : Ctx L m₁ t) {r : Region} (h : ∃ R ∈ L.rd ++ L.wr, Within r R) :
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
  refine ⟨e40 hL, by omega_using [this], by rw [hL.x32_toNat (by omega_using [])]; omega_using [this], ?_, ?_, ?_⟩
  · rw [regKS hL]; exact st_ks
  · exact (k_st hL).sub_left (b40 hL)
  · rw [regKS hL]; exact (k_ks hL).sub_left (b40 hL)

/-! ## Zeroing the state -/

theorem zeroSt_ok (hL : L.Ok) {t : State} (hc : Ctx L m₁ t) :
    WP isa (.block zeroSt) t fun t' => Ctx L m₁ t' ∧ Frame [⟨L.ST, 200⟩] t.mem t'.mem ∧
      stateAt t'.mem L.ST = Spec.Sha3.zero := by
  rw [zeroSt]
  refine wp_movi fun t1 u1 => ?_
  obtain e1 : t1.gpr .esi = L.X32 := by rw [u1.other _ (by decide), hc.esi]
  let Inv : Nat → State → Prop := fun k s => s.gpr = t1.gpr ∧ s.rd = t1.rd ∧ s.wr = t1.wr ∧
    Frame [⟨L.ST, 200⟩] t1.mem s.mem ∧ ∀ j < k, s.mem.readW (L.X + BitVec.ofNat 64 (4 * j)) 32 = 0
  refine WP.mono (wp_range_flatMap (M := isa) Inv (fun k s hk h => ?_) 50 (Nat.le_refl _) t1
    ⟨rfl, rfl, rfl, Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero j)⟩) fun t' ⟨g, rd, wr, fr, z⟩ => ?_
  · have hb : s.gpr .esi = L.X32 := by rw [h.1, e1]
    obtain ea : addr L.X32 (4 * k) = L.X + BitVec.ofNat 64 (4 * k) := hL.xo (by omega_using [hk])
    obtain hin : InRegions s.wr (addr L.X32 (4 * k)) 4 := by
      rw [ea, h.2.2.1, u1.wr, hc.wr]
      obtain ⟨R, hR, c⟩ := hL.inW (e := 4 * k) (k := 4) (by omega_using [hk])
      exact ⟨R, List.mem_cons_of_mem _ hR, c⟩
    refine wp_stm (o := 4 * k) hb hin fun s' m => WP.block_nil ⟨by rw [m.gpr, h.1], by rw [m.rd, h.2.1], by rw [m.wr, h.2.2.1], ?_, fun j hj => ?_⟩
    · rw [m.mem, ea]
      exact h.2.2.2.1.writeW (List.mem_singleton_self _) _ (by
        have := Offset.contains_base L.X (d := 4 * k) (n := 4) (k := 200) (by omega_using [hk]) (by omega_using [hk])
        simpa only [x0] using this)
    · rw [m.mem, ea, h.1, u1.gpr]
      by_cases e : j = k
      · subst e; exact Mem.readW_writeW_self32 _ _ _
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega_using [e]) (by omega_using [hk, hj]) (by omega_using [hk])) (by decide)]
        exact h.2.2.2.2 j (by omega_using [hj, e])
  · have hc1 : Ctx L m₁ t1 := hc.regs u1.rd u1.wr u1.mem (u1.other _ (by decide)) (u1.other _ (by decide))
    refine ⟨hc1.keep hL rd wr (by rw [g]) (by rw [g]) fr fun r hr => ?_, by rw [← u1.mem]; exact fr,
      Proof.MlKem.X86.Sample.stateAt_zero fun j hj => ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact .inl w_st
    · have e := Mem.readW_byte t'.mem (L.X + BitVec.ofNat 64 (4 * (j / 4))) (i := j % 4) (by omega_using [])
      rw [add_add, show 4 * (j / 4) + j % 4 = j by omega_using [], z (j / 4) (by omega_using [hj])] at e
      rw [e]
      apply BitVec.eq_of_toNat_eq
      simp

/-! ## Absorbing -/

/-- The arguments of a call of `vg_keccak_absorb`. -/
abbrev absArgs (src len pos : Arg) : List (Reg × Arg) :=
  [(.edx, pos), (.eax, .off oST), (.ecx, .imm 136), (.ebx, src), (.ebp, len), (.edi, .off oKS)]

/-- The position `vg_keccak_absorb` returns. -/
theorem absorb_eax {s s₂ : State} {E S D W : BitVec 32} {pos len : Nat} (hesp : s.gpr .esp = E)
    (ha : AbsArgs s S D W 136 pos len) (hE : 40 ≤ E.toNat) (hlen : len < 2 ^ 32) (hpos : pos < 2 ^ 32)
    {rd wr : List Region} (post : Proof.Sha3.absorbX86.post ((pushed Proof.MlKem.X86.rs6 s).callEntry.withRegions rd wr) s₂) :
    (s₂.gpr .eax).toNat = (pos + len) % 136 := by
  obtain fit : 4 * Proof.MlKem.X86.rs6.length + 4 ≤ (s.gpr .esp).toNat := by
    rw [hesp]; simp only [List.length_cons, List.length_nil]; omega_using [hE]
  obtain a1 : arg (pushed Proof.MlKem.X86.rs6 s).callEntry 1 = BitVec.ofNat 32 136 := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact ha.ecx
  obtain a2 : arg (pushed Proof.MlKem.X86.rs6 s).callEntry 2 = BitVec.ofNat 32 pos := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact ha.edx
  obtain a4 : arg (pushed Proof.MlKem.X86.rs6 s).callEntry 4 = BitVec.ofNat 32 len := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact ha.ebp
  have := post.2
  simp only [arg_withRegions, a1, a2, a4, toNat_ofNat32 hlen, toNat_ofNat32 hpos,
    toNat_ofNat32 (show 136 < 2 ^ 32 by decide)] at this
  exact this

theorem regMU (hL : L.Ok) : reg32 (L.X32 + BitVec.ofNat 32 840) 64 = ⟨L.MU, 64⟩ := by
  show (⟨_, 64⟩ : Region) = _; rw [mu_eq hL]

theorem SetPost.ctx {n : Nat} {as : List (Reg × Arg)} (hok : argsOk n as = true) {s s₁ : State}
    (hs : SetPost as s s₁) (hc : Ctx L m₁ s) : Ctx L m₁ s₁ :=
  hc.regs hs.2.rd hs.2.wr hs.2.mem (hs.esp hok) (hs.esi hok)

end

/-! ## As pieces -/

section
variable {Pre : State → Prop} {Pub : State → State → Prop} {lay : State → Lay} {A B : State → State → Prop}

theorem zeroSt_piece (hpub : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → PubL (lay s₀) (lay s₀'))
    (hA : ∀ s₀ s, Pre s₀ → A s₀ s → CtxO lay s₀ s)
    (hQ : ∀ s₀ s s', Pre s₀ → A s₀ s → CtxO lay s₀ s' → Frame [⟨(lay s₀).ST, 200⟩] s.mem s'.mem →
      stateAt s'.mem (lay s₀).ST = Spec.Sha3.zero → B s₀ s') :
    Piece Pre Pub A B (.block zeroSt) :=
  Piece.taint [.esi] (fun s₀ s h₀ ha => by
      obtain h := hA s₀ s h₀ ha
      exact (zeroSt_ok h.ok h.ctx).mono fun s' ⟨c, f, z⟩ => hQ s₀ s s' h₀ ha ⟨h.ok, c⟩ f z)
    (fun s₀ s₀' s s' h₀ h₀' hq ha ha' r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [(hA s₀ s h₀ ha).ctx.esi, (hA s₀' s' h₀' ha').ctx.esi, (hpub s₀ s₀' h₀ h₀' hq).x]) (by native_taint_decide)

/-- The stack the sponge functions' calls use. -/
theorem kb_stk {L : Lay} (hL : L.Ok) {a : Nat} (ha : a ≤ 40) : Region.Sub (below L.E1 a) L.STK :=
  fun x h => b40 hL x (below_sub (a := a) (b := 40) ha (e40 hL) x h)

/-- A call of `vg_keccak_absorb`, continuing the message at the position `q s₀`
with the `n s₀` bytes at `dp s₀`. -/
theorem kabs_piece (src len pos : Arg) (dp : State → BitVec 32) (n q : State → Nat)
    {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (setArgs (absArgs src len pos))) ht).isSome = true)
    (hpub : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → PubL (lay s₀) (lay s₀'))
    (hA : ∀ s₀ s, Pre s₀ → A s₀ s → CtxO lay s₀ s)
    (hok : ∀ s₀, Pre s₀ → argsOk (lay s₀).nA (absArgs src len pos) = true)
    (hv : ∀ s₀ s, Pre s₀ → A s₀ s → src.val s = dp s₀ ∧ len.val s = BitVec.ofNat 32 (n s₀) ∧
      pos.val s = BitVec.ofNat 32 (q s₀))
    (hdn : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → dp s₀ = dp s₀' ∧ n s₀ = n s₀' ∧ q s₀ = q s₀')
    (hb : ∀ s₀ s, Pre s₀ → A s₀ s → q s₀ < 136 ∧ n s₀ < 2 ^ 32 ∧ (dp s₀).toNat + n s₀ ≤ 2 ^ 32 ∧
      (∃ R ∈ (lay s₀).rd ++ (lay s₀).wr, Within ⟨(dp s₀).setWidth 64, n s₀⟩ R) ∧
      Region.Disjoint ⟨(dp s₀).setWidth 64, n s₀⟩ ⟨(lay s₀).ST, 200⟩ ∧
      Region.Disjoint ⟨(dp s₀).setWidth 64, n s₀⟩ ⟨(lay s₀).KS, 640⟩ ∧
      (lay s₀).STK.Disjoint ⟨(dp s₀).setWidth 64, n s₀⟩)
    (hQ : ∀ s₀ s s', Pre s₀ → A s₀ s → CtxO lay s₀ s' →
      Frame [⟨(lay s₀).ST, 200⟩, ⟨(lay s₀).KS, 640⟩, (lay s₀).STK] s.mem s'.mem →
      (∀ msg, Repr s.mem (lay s₀).ST 136 msg → q s₀ = msg.length % 136 →
        Repr s'.mem (lay s₀).ST 136 (msg ++ bytesAt s.mem ((dp s₀).setWidth 64) (n s₀))) →
      (s'.gpr .eax).toNat = (q s₀ + n s₀) % 136 → B s₀ s') :
    Piece Pre Pub A B (kabs src len pos) := by
  obtain hargs : ∀ s₀ s s₁, Pre s₀ → A s₀ s → SetPost (absArgs src len pos) s s₁ →
      AbsArgs s₁ (lay s₀).X32 (dp s₀) ((lay s₀).X32 + BitVec.ofNat 32 200) 136 (q s₀) (n s₀) := by
    intro s₀ s s₁ h₀ ha hs
    obtain hc := (hA s₀ s h₀ ha).ctx
    obtain ⟨v₁, v₂, v₃⟩ := hv s₀ s h₀ ha
    obtain e2 := hs.1 (.edx, pos) (by simp)
    obtain e0 := hs.1 (.eax, .off oST) (by simp)
    obtain e1 := hs.1 (.ecx, .imm 136) (by simp)
    obtain e3 := hs.1 (.ebx, src) (by simp)
    obtain e4 := hs.1 (.ebp, len) (by simp)
    obtain e5 := hs.1 (.edi, .off oKS) (by simp)
    simp only [Arg.val, hc.esi, oST, oKS, x0'] at e0 e1 e5
    rw [v₃] at e2
    rw [v₁] at e3
    rw [v₂] at e4
    exact ⟨e0, e1, e2, e3, e4, e5⟩
  refine argsRet_piece Proof.Sha3.X86.Stream.Absorb.absorb_verified.1
    Proof.Sha3.X86.Stream.Absorb.absorb_verified.2.1 absorb_nosp (by decide) (by decide) tt hpub hA hok
    (fun s₀ => [reg32 (dp s₀) (n s₀)])
    (fun s₀ => [reg32 (lay s₀).X32 200, reg32 ((lay s₀).X32 + BitVec.ofNat 32 200) 640, below (lay s₀).E1 24])
    (fun s₀ s₀' h₀ h₀' hq => ?_) (fun s₀ s h₀ ha => ?_) (fun s₀ s s₁ h₀ ha hs => ?_)
    (fun s₀ s₀' s s' s₁ s₁' h₀ h₀' hq ha ha' hs hs' => ?_) (fun s₀ s s₁ s' h₀ ha hs e₁ e₂ e₃ fr post => ?_)
  · obtain ⟨d₁, d₂, -⟩ := hdn s₀ s₀' h₀ h₀' hq
    obtain hp := hpub s₀ s₀' h₀ h₀' hq
    refine ⟨by rw [d₁, d₂], ?_⟩
    simp only [Lay.E1, hp.x, hp.sp]
  · have := e40 (hA s₀ s h₀ ha).ok
    rw [absorb_stack]; simp only [List.length_cons, List.length_nil]; omega_using [this]
  · obtain ⟨hL, hc⟩ := hA s₀ s h₀ ha
    obtain hc1 := SetPost.ctx (hok s₀ h₀) hs hc
    obtain ⟨hql, hnl, hfit, hin, dS, dK, kD⟩ := hb s₀ s h₀ ha
    exact absorb_pre hc1.esp (hargs s₀ s s₁ h₀ ha hs) (kbufs hL) hfit dS (by rw [regKS hL]; exact dK)
      (kD.sub_left (b40 hL)) (by decide) hql hnl (withinRW hc1 hin)
      (withinW hc1 (by have := hL.covX (e := 0) (k := 200) (by omega_using []); rwa [x0] at this))
      (withinW hc1 (by rw [regKS hL]; exact hL.covX (e := 200) (by omega_using [])))
  · have a := hargs s₀ s s₁ h₀ ha hs
    obtain a' := hargs s₀' s' s₁' h₀' ha' hs'
    obtain ⟨d₁, d₂, d₃⟩ := hdn s₀ s₀' h₀ h₀' hq
    obtain hp := hpub s₀ s₀' h₀ h₀' hq
    rw [← d₁, ← d₂, ← d₃, ← hp.x] at a'
    obtain hsp : s₁.gpr .esp = s₁'.gpr .esp := by
      rw [hs.esp (hok s₀ h₀), hs'.esp (hok s₀' h₀'), (hA s₀ s h₀ ha).ctx.esp, (hA s₀' s' h₀' ha').ctx.esp,
        Lay.E1, Lay.E1, hp.sp]
    obtain hE : 40 ≤ (s₁.gpr .esp).toNat := by
      rw [hs.esp (hok s₀ h₀), (hA s₀ s h₀ ha).ctx.esp]; exact e40 (hA s₀ s h₀ ha).ok
    exact Proof.MlKem.X86.args6_eq hE hsp (Proof.MlKem.X86.absArgs_eq a a') _ _
  · obtain ⟨hL, hc⟩ := hA s₀ s h₀ ha
    obtain hc1 := SetPost.ctx (hok s₀ h₀) hs hc
    obtain a := hargs s₀ s s₁ h₀ ha hs
    obtain ⟨hql, hnl, -, -, -, -, kD⟩ := hb s₀ s h₀ ha
    have hsp : s₁.gpr .esp = (lay s₀).E1 := hc1.esp
    obtain hE := e40 hL
    obtain kb : ∀ r ∈ [reg32 (lay s₀).X32 200, reg32 ((lay s₀).X32 + BitVec.ofNat 32 200) 640, below (lay s₀).E1 24] ++
        [below (s₁.gpr .esp) (4 * Proof.MlKem.X86.rs6.length + stackUse Impl.Sha3.X86.Stream.absorb + 4)],
        Within r (lay s₀).W ∨ Region.Sub r (lay s₀).STK := fun r hr => by
      rw [absorb_stack, hsp] at hr
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, List.length_cons,
        List.length_nil] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact .inl w_st
      · rw [regKS hL]; exact .inl w_ks
      · exact .inr (kb_stk hL (by omega_using []))
      · exact .inr (b40 hL)
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
      · rw [regKS hL]; exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, kb_stk hL (by omega_using [])⟩
      · exact ⟨_, by simp, b40 hL⟩
    · have := absorb_post hsp a hE hnl (by decide) (by omega_using [hql]) (kbufs hL).bS (kD.sub_left (b40 hL))
        ⟨s₂, m₂, post⟩ msg (by rw [hs.2.mem]; exact hm) hp
      rwa [hs.2.mem] at this
    · rw [← g₂]; exact absorb_eax hsp a hE hnl (by omega_using [hql]) post

/-! ## Padding -/

/-- The arguments of a call of `vg_keccak_pad`. -/
abbrev padArgs (pos : Arg) : List (Reg × Arg) :=
  [(.edx, pos), (.eax, .off oST), (.ecx, .imm 136), (.ebx, .imm 0x1f), (.edi, .off oKS)]

/-- A call of `vg_keccak_pad` at the position `q s₀`, with the suffix of SHAKE. -/
theorem kpad_piece (pos : Arg) (q : State → Nat) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (setArgs (padArgs pos))) ht).isSome = true)
    (hpub : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → PubL (lay s₀) (lay s₀'))
    (hA : ∀ s₀ s, Pre s₀ → A s₀ s → CtxO lay s₀ s)
    (hok : ∀ s₀, Pre s₀ → argsOk (lay s₀).nA (padArgs pos) = true)
    (hv : ∀ s₀ s, Pre s₀ → A s₀ s → pos.val s = BitVec.ofNat 32 (q s₀))
    (hdn : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → q s₀ = q s₀')
    (hb : ∀ s₀ s, Pre s₀ → A s₀ s → q s₀ < 136)
    (hQ : ∀ s₀ s s', Pre s₀ → A s₀ s → CtxO lay s₀ s' →
      Frame [⟨(lay s₀).ST, 200⟩, ⟨(lay s₀).KS, 640⟩, (lay s₀).STK] s.mem s'.mem →
      (∀ msg, Repr s.mem (lay s₀).ST 136 msg → q s₀ = msg.length % 136 →
        stateAt s'.mem (lay s₀).ST = absorb 136 (pad 136 Spec.Sha3.shakeSuffix msg)) → B s₀ s') :
    Piece Pre Pub A B (kpad pos) := by
  obtain hargs : ∀ s₀ s s₁, Pre s₀ → A s₀ s → SetPost (padArgs pos) s s₁ →
      PadArgs s₁ (lay s₀).X32 ((lay s₀).X32 + BitVec.ofNat 32 200) 136 (q s₀) 0x1f := by
    intro s₀ s s₁ h₀ ha hs
    obtain hc := (hA s₀ s h₀ ha).ctx
    obtain e2 := hs.1 (.edx, pos) (by simp)
    obtain e0 := hs.1 (.eax, .off oST) (by simp)
    obtain e1 := hs.1 (.ecx, .imm 136) (by simp)
    obtain e3 := hs.1 (.ebx, .imm 0x1f) (by simp)
    obtain e4 := hs.1 (.edi, .off oKS) (by simp)
    simp only [Arg.val, hc.esi, oST, oKS, x0'] at e0 e1 e3 e4
    rw [hv s₀ s h₀ ha] at e2
    exact ⟨e0, e1, e2, e3, e4⟩
  refine argsWith_piece Proof.Sha3.X86.Stream.Pad.pad_verified.1
    Proof.Sha3.X86.Stream.Pad.pad_verified.2.1 pad_nosp (by decide) (by decide) tt hpub hA hok
    (fun _ => [])
    (fun s₀ => [reg32 (lay s₀).X32 200, reg32 ((lay s₀).X32 + BitVec.ofNat 32 200) 640, below (lay s₀).E1 20])
    (fun s₀ s₀' h₀ h₀' hq => ?_) (fun s₀ s h₀ ha => ?_) (fun s₀ s s₁ h₀ ha hs => ?_)
    (fun s₀ s₀' s s' s₁ s₁' h₀ h₀' hq ha ha' hs hs' => ?_) (fun s₀ s s₁ s' h₀ ha hs e₁ e₂ e₃ fr post => ?_)
  · have hp := hpub s₀ s₀' h₀ h₀' hq
    refine ⟨rfl, ?_⟩
    simp only [Lay.E1, hp.x, hp.sp]
  · have := e40 (hA s₀ s h₀ ha).ok
    rw [pad_stack]; simp only [List.length_cons, List.length_nil]; omega_using [this]
  · obtain ⟨hL, hc⟩ := hA s₀ s h₀ ha
    obtain hc1 := SetPost.ctx (hok s₀ h₀) hs hc
    exact pad_pre hc1.esp (hargs s₀ s s₁ h₀ ha hs) (kbufs hL) (by decide) (hb s₀ s h₀ ha)
      (withinW hc1 (by have := hL.covX (e := 0) (k := 200) (by omega_using []); rwa [x0] at this))
      (withinW hc1 (by rw [regKS hL]; exact hL.covX (e := 200) (by omega_using [])))
  · have a := hargs s₀ s s₁ h₀ ha hs
    obtain a' := hargs s₀' s' s₁' h₀' ha' hs'
    obtain hp := hpub s₀ s₀' h₀ h₀' hq
    rw [← hdn s₀ s₀' h₀ h₀' hq, ← hp.x] at a'
    obtain hsp : s₁.gpr .esp = s₁'.gpr .esp := by
      rw [hs.esp (hok s₀ h₀), hs'.esp (hok s₀' h₀'), (hA s₀ s h₀ ha).ctx.esp, (hA s₀' s' h₀' ha').ctx.esp,
        Lay.E1, Lay.E1, hp.sp]
    obtain hE : 40 ≤ (s₁.gpr .esp).toNat := by
      rw [hs.esp (hok s₀ h₀), (hA s₀ s h₀ ha).ctx.esp]; exact e40 (hA s₀ s h₀ ha).ok
    exact Proof.MlKem.X86.args5_eq hE hsp (Proof.MlKem.X86.padArgs_eq a a') _ _
  · obtain ⟨hL, hc⟩ := hA s₀ s h₀ ha
    obtain hc1 := SetPost.ctx (hok s₀ h₀) hs hc
    obtain a := hargs s₀ s s₁ h₀ ha hs
    have hsp : s₁.gpr .esp = (lay s₀).E1 := hc1.esp
    obtain hE := e40 hL
    obtain kb : ∀ r ∈ [reg32 (lay s₀).X32 200, reg32 ((lay s₀).X32 + BitVec.ofNat 32 200) 640, below (lay s₀).E1 20] ++
        [below (s₁.gpr .esp) (4 * Proof.MlKem.X86.rs5.length + stackUse Impl.Sha3.X86.Stream.pad + 4)],
        Within r (lay s₀).W ∨ Region.Sub r (lay s₀).STK := fun r hr => by
      rw [pad_stack, hsp] at hr
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, List.length_cons,
        List.length_nil] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact .inl w_st
      · rw [regKS hL]; exact .inl w_ks
      · exact .inr (kb_stk hL (by omega_using []))
      · exact .inr (kb_stk hL (by omega_using []))
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
      · rw [regKS hL]; exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, kb_stk hL (by omega_using [])⟩
      · exact ⟨_, by simp, kb_stk hL (by omega_using [])⟩
    · have := pad_post hsp a hE (by decide) (by have := hb s₀ s h₀ ha; omega_using [hp]) (kbufs hL).bS ⟨s₂, m₂, post⟩ msg
        (by rw [hs.2.mem]; exact hm) hp
      rw [this]; rfl

/-! ## Squeezing -/

/-- The arguments of a call of `vg_keccak_squeeze`. -/
abbrev sqzArgs : List (Reg × Arg) :=
  [(.eax, .off oST), (.ecx, .imm 136), (.edx, .imm 0), (.ebx, .off oMU), (.ebp, .imm 64), (.edi, .off oKS)]

/-- A call of `vg_keccak_squeeze`, of 64 bytes to `μ`. -/
theorem ksqz_piece (hpub : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → PubL (lay s₀) (lay s₀'))
    (hA : ∀ s₀ s, Pre s₀ → A s₀ s → CtxO lay s₀ s)
    (hok : ∀ s₀, Pre s₀ → argsOk (lay s₀).nA sqzArgs = true)
    (hQ : ∀ s₀ s s', Pre s₀ → A s₀ s → CtxO lay s₀ s' →
      Frame [⟨(lay s₀).ST, 200⟩, ⟨(lay s₀).MU, 64⟩, ⟨(lay s₀).KS, 640⟩, (lay s₀).STK] s.mem s'.mem →
      bytesAt s'.mem (lay s₀).MU 64 = squeezeFrom 136 (stateAt s.mem (lay s₀).ST) 0 64 → B s₀ s') :
    Piece Pre Pub A B ksqz := by
  obtain hargs : ∀ s₀ s s₁, Pre s₀ → A s₀ s → SetPost sqzArgs s s₁ →
      AbsArgs s₁ (lay s₀).X32 ((lay s₀).X32 + BitVec.ofNat 32 840) ((lay s₀).X32 + BitVec.ofNat 32 200) 136 0 64 := by
    intro s₀ s s₁ h₀ ha hs
    obtain hc := (hA s₀ s h₀ ha).ctx
    obtain e0 := hs.1 (.eax, .off oST) (by simp)
    obtain e1 := hs.1 (.ecx, .imm 136) (by simp)
    obtain e2 := hs.1 (.edx, .imm 0) (by simp)
    obtain e3 := hs.1 (.ebx, .off oMU) (by simp)
    obtain e4 := hs.1 (.ebp, .imm 64) (by simp)
    obtain e5 := hs.1 (.edi, .off oKS) (by simp)
    simp only [Arg.val, hc.esi, oST, oKS, oMU, x0'] at e0 e1 e2 e3 e4 e5
    exact ⟨e0, e1, e2, e3, e4, e5⟩
  refine argsWith_piece Proof.Sha3.X86.Stream.Squeeze.squeeze_verified.1
    Proof.Sha3.X86.Stream.Squeeze.squeeze_verified.2.1 squeeze_nosp (by decide) (by decide) (by native_taint_decide) hpub hA hok
    (fun _ => [])
    (fun s₀ => [reg32 (lay s₀).X32 200, reg32 ((lay s₀).X32 + BitVec.ofNat 32 840) 64,
      reg32 ((lay s₀).X32 + BitVec.ofNat 32 200) 640, below (lay s₀).E1 24])
    (fun s₀ s₀' h₀ h₀' hq => ?_) (fun s₀ s h₀ ha => ?_) (fun s₀ s s₁ h₀ ha hs => ?_)
    (fun s₀ s₀' s s' s₁ s₁' h₀ h₀' hq ha ha' hs hs' => ?_) (fun s₀ s s₁ s' h₀ ha hs e₁ e₂ e₃ fr post => ?_)
  · have hp := hpub s₀ s₀' h₀ h₀' hq
    refine ⟨rfl, ?_⟩
    simp only [Lay.E1, hp.x, hp.sp]
  · have := e40 (hA s₀ s h₀ ha).ok
    rw [squeeze_stack]; simp only [List.length_cons, List.length_nil]; omega_using [this]
  · obtain ⟨hL, hc⟩ := hA s₀ s h₀ ha
    obtain hc1 := SetPost.ctx (hok s₀ h₀) hs hc
    have hX := hL.x32_lt
    exact squeeze_pre hc1.esp (hargs s₀ s s₁ h₀ ha hs) (kbufs hL) (by rw [hL.x32_toNat (by omega_using [])]; omega_using [hX])
      (by rw [regMU hL]; exact st_mu) (by rw [regMU hL, regKS hL]; exact mu_ks)
      (by rw [regMU hL]; exact (k_mu hL).sub_left (b40 hL)) (by decide) (by decide) (by decide)
      (withinW hc1 (by have := hL.covX (e := 0) (k := 200) (by omega_using []); rwa [x0] at this))
      (withinW hc1 (by rw [regMU hL]; exact hL.covX (e := 840) (by omega_using [])))
      (withinW hc1 (by rw [regKS hL]; exact hL.covX (e := 200) (by omega_using [])))
  · have a := hargs s₀ s s₁ h₀ ha hs
    obtain a' := hargs s₀' s' s₁' h₀' ha' hs'
    obtain hp := hpub s₀ s₀' h₀ h₀' hq
    rw [← hp.x] at a'
    obtain hsp : s₁.gpr .esp = s₁'.gpr .esp := by
      rw [hs.esp (hok s₀ h₀), hs'.esp (hok s₀' h₀'), (hA s₀ s h₀ ha).ctx.esp, (hA s₀' s' h₀' ha').ctx.esp,
        Lay.E1, Lay.E1, hp.sp]
    obtain hE : 40 ≤ (s₁.gpr .esp).toNat := by
      rw [hs.esp (hok s₀ h₀), (hA s₀ s h₀ ha).ctx.esp]; exact e40 (hA s₀ s h₀ ha).ok
    exact Proof.MlKem.X86.args6_eq hE hsp (Proof.MlKem.X86.absArgs_eq a a') _ _
  · obtain ⟨hL, hc⟩ := hA s₀ s h₀ ha
    obtain hc1 := SetPost.ctx (hok s₀ h₀) hs hc
    obtain a := hargs s₀ s s₁ h₀ ha hs
    have hsp : s₁.gpr .esp = (lay s₀).E1 := hc1.esp
    obtain hE := e40 hL
    obtain kb : ∀ r ∈ [reg32 (lay s₀).X32 200, reg32 ((lay s₀).X32 + BitVec.ofNat 32 840) 64,
        reg32 ((lay s₀).X32 + BitVec.ofNat 32 200) 640, below (lay s₀).E1 24] ++
        [below (s₁.gpr .esp) (4 * Proof.MlKem.X86.rs6.length + stackUse Impl.Sha3.X86.Stream.squeeze + 4)],
        Within r (lay s₀).W ∨ Region.Sub r (lay s₀).STK := fun r hr => by
      rw [squeeze_stack, hsp] at hr
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, List.length_cons,
        List.length_nil] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact .inl w_st
      · rw [regMU hL]; exact .inl w_mu
      · rw [regKS hL]; exact .inl w_ks
      · exact .inr (kb_stk hL (by omega_using []))
      · exact .inr (b40 hL)
    obtain ⟨s₂, m₂, post⟩ := post
    refine hQ s₀ s s' h₀ ha ⟨hL, hc1.keep hL e₁ e₂ (e₃ .esp (by decide)) (e₃ .esi (by decide)) fr kb⟩ ?_ ?_
    · rw [← hs.2.mem]
      refine fr.sub fun r hr => ?_
      rw [squeeze_stack, hsp] at hr
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, List.length_cons,
        List.length_nil] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · rw [regMU hL]; exact ⟨_, by simp, fun _ h => h⟩
      · rw [regKS hL]; exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, kb_stk hL (by omega_using [])⟩
      · exact ⟨_, by simp, b40 hL⟩
    · have := (squeeze_post hsp a hE (by decide) (by decide) (by decide) (kbufs hL).bS
      (by rw [regMU hL]; exact (k_mu hL).sub_left (b40 hL)) ⟨s₂, m₂, post⟩).1
      rw [mu_eq hL, hs.2.mem] at this
      exact this

end

end VG.Proof.MlDsa.X86.Message
