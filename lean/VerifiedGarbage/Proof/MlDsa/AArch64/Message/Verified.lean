import VerifiedGarbage.Impl.MlDsa.AArch64.Message
import VerifiedGarbage.Proof.MlKem.AArch64.Sample
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlDsa.Message.Common
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Verified
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Inst
import VerifiedGarbage.Proof.MlKem.KPke1024
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Sample

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Message.Layout`. -/
section

/-!
# ML-DSA on AArch64, `sign_message` and `verify_message`: where everything is

Untrusted: everything here is checked by Lean. The function's buffers, the
16 bytes of stack below the stack pointer on entry (`STK`, which the calls'
frames use), and the 1 KiB `X` of `scratch` after the working space of the
function on `μ` (`Lay`): the Keccak state, the sponge functions' working
space and `μ` in its first 904 bytes (`W`), then the saved registers and
arguments and the two bytes of the formatted message (`SV`). `Ctx` is what
holds from the entry's saves to the exit: the permissions, the stack
pointer, `x28` pointing at `X`, the callee-saved registers, the saves, and
that memory changed only in `X` and `STK`. `Ctx.keep` carries it over code
that writes only within `W` and `STK`.
-/

namespace VG.Proof.MlDsa.AArch64.Message

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Spec.Sha3 (bytesAt)

theorem covers_of_within {rs rs' : List Region} (h : ∀ r ∈ rs, ∃ R ∈ rs', Within r R) : Covers rs rs' :=
  Covers.of_sub fun r hr => by
    obtain ⟨R, hR, o, hb, hl⟩ := h r hr
    exact ⟨R, hR, o, hb, hl⟩

/-! ## The layout -/

/-- The stack pointer on entry, the buffers, the offset `E` of the 1 KiB `X`
in `scratch`, and the permissions on entry. -/
structure Lay where
  SP : Addr
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

variable (L : VG.Proof.MlDsa.AArch64.Message.Lay)

/-- The 16 bytes of stack the calls' frames use. -/
abbrev STK : Region := below L.SP 16
/-- The 1 KiB. -/
abbrev X : Addr := L.scr + BitVec.ofNat 64 L.E
abbrev XS : Region := ⟨L.X, 1024⟩
/-- What the calls write in it: the Keccak state, the sponge functions'
working space and `μ`. -/
abbrev W : Region := ⟨L.X, 904⟩
/-- The saves and the two bytes of the formatted message. -/
abbrev SV : Region := ⟨L.X + BitVec.ofNat 64 904, 88⟩
abbrev ST : Addr := L.X
abbrev KS : Addr := L.X + BitVec.ofNat 64 200
abbrev MU : Addr := L.X + BitVec.ofNat 64 840
abbrev KEY : Region := ⟨L.key, L.keyLen⟩
abbrev MSG : Region := ⟨L.msg, L.len.toNat⟩
abbrev CTX : Region := ⟨L.ctx, L.ctxLen.toNat⟩

/-- The saved arguments, at `X + 920 + 8j`. -/
def vals : List (BitVec 64) := [L.key, L.msg, L.len, L.ctx, L.ctxLen, L.rnd, L.sig, L.scr]

/-- What the contract says of where everything is. -/
structure Ok : Prop where
  ctxLt : L.ctxLen.toNat < 256
  hE : L.E + 1024 < 2 ^ 31
  hKey : 128 ≤ L.keyLen ∧ L.keyLen < 2 ^ 16
  nSP : 16 ≤ L.SP.toNat
  nX : L.X.toNat + 1024 ≤ 2 ^ 64
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

variable {L : VG.Proof.MlDsa.AArch64.Message.Lay}

theorem stk_x (h : L.Ok) {e k : Nat} (h₂ : e + k ≤ 1024) :
    Region.Disjoint L.STK ⟨L.X + BitVec.ofNat 64 e, k⟩ :=
  h.kX.sub_right (Offset.sub_base _ h₂)

theorem x_r (_h : L.Ok) {r : Region} (hr : L.XS.Disjoint r) {e k : Nat} (h₂ : e + k ≤ 1024) :
    Region.Disjoint ⟨L.X + BitVec.ofNat 64 e, k⟩ r :=
  hr.sub_left (Offset.sub_base _ h₂)

/-- The 1 KiB is writable. -/
theorem covX (h : L.Ok) {e k : Nat} (h₂ : e + k ≤ 1024) : ∃ R ∈ L.wr, Within ⟨L.X + BitVec.ofNat 64 e, k⟩ R := by
  obtain ⟨R, hR, hw⟩ := h.inX
  exact ⟨R, hR, (within_off L.X h₂).trans hw⟩

/-- Bytes of the 1 KiB are writable. -/
theorem inW (h : L.Ok) {e k : Nat} (h₂ : e + k ≤ 1024) (hk : 0 < k) : InRegions L.wr (L.X + BitVec.ofNat 64 e) k := by
  obtain ⟨R, hR, o, hb, hl⟩ := h.covX h₂
  refine ⟨R, hR, ?_⟩
  simp only at hb hl
  rw [hb]
  exact Offset.contains_base _ hl (by have := h.lenW R hR; omega)

/-- What lies within the first 904 bytes of `X`, or in `STK`, is apart from the saves. -/
theorem sv_disj (h : L.Ok) {r : Region} (hr : Within r L.W ∨ Region.Sub r L.STK) {d n : Nat} (hd : d + n ≤ 88) :
    Region.Disjoint ⟨L.X + BitVec.ofNat 64 904 + BitVec.ofNat 64 d, n⟩ r := by
  rw [add_add]
  rcases hr with hr | hr
  · obtain ⟨o, hb, hl⟩ := hr
    obtain ⟨b, k⟩ := r
    simp only at hb hl
    subst hb
    exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
  · exact (h.kX.symm.sub_left (Offset.sub_base _ (by omega))).sub_right hr

end Lay.Ok

/-! ## From the entry's saves to the exit -/

/-- The state from the entry's saves to the exit: `g` and `v` are the
registers on entry, `m₀` the memory. -/
structure Ctx (L : VG.Proof.MlDsa.AArch64.Message.Lay) (g : Reg → BitVec 64) (v : VReg → BitVec 128) (m₀ : Mem) (t : State) : Prop where
  rd : t.rd = L.rd
  wr : t.wr = L.wr
  sp : t.sp = L.SP
  x28 : t.gpr .x28 = L.X
  cs : ∀ r ∈ preserved, r ≠ .x28 → r ≠ .x30 → t.gpr r = g r
  vs : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (v r).extractLsb' 0 64
  s28 : t.mem.readW (L.X + BitVec.ofNat 64 904 + BitVec.ofNat 64 0) 64 = g .x28
  s30 : t.mem.readW (L.X + BitVec.ofNat 64 904 + BitVec.ofNat 64 8) 64 = g .x30
  slot : ∀ j < 8, t.mem.readW (L.X + BitVec.ofNat 64 904 + BitVec.ofNat 64 (16 + 8 * j)) 64 = L.vals.getD j 0
  hdr : bytesAt t.mem (L.X + BitVec.ofNat 64 904 + BitVec.ofNat 64 80) 2 = [0, BitVec.ofNat 8 L.ctxLen.toNat]
  frame : Frame [L.XS, L.STK] m₀ t.mem

namespace Ctx

variable {L : VG.Proof.MlDsa.AArch64.Message.Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {t t' : State}

/-- Code that writes only registers but `x28` and the callee-saved ones. -/
theorem regs (hc : VG.Proof.MlDsa.AArch64.Message.Ctx L g v m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp)
    (hm : t'.mem = t.mem) (hvs : ∀ r ∈ preservedV, (t'.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64)
    (hg : ∀ r ∈ preserved, r ≠ .x30 → t'.gpr r = t.gpr r) : VG.Proof.MlDsa.AArch64.Message.Ctx L g v m₀ t' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp, (hg .x28 (by decide) (by decide)).trans hc.x28,
    fun r hr h28 h30 => (hg r hr h30).trans (hc.cs r hr h28 h30), fun r hr => (hvs r hr).trans (hc.vs r hr),
    by rw [hm]; exact hc.s28, by rw [hm]; exact hc.s30, fun j hj => by rw [hm]; exact hc.slot j hj,
    by rw [hm]; exact hc.hdr, by rw [hm]; exact hc.frame⟩

/-- Code that writes memory only within the first 904 bytes of `X` and in `STK`. -/
theorem keep (hc : VG.Proof.MlDsa.AArch64.Message.Ctx L g v m₀ t) (hL : L.Ok) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp)
    (hvs : ∀ r ∈ preservedV, (t'.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64)
    (hg : ∀ r ∈ preserved, r ≠ .x30 → t'.gpr r = t.gpr r) {rs : List Region} (hf : Frame rs t.mem t'.mem)
    (hrs : ∀ r ∈ rs, Within r L.W ∨ Region.Sub r L.STK) : VG.Proof.MlDsa.AArch64.Message.Ctx L g v m₀ t' := by
  have keep : ∀ d, d + 8 ≤ 88 → t'.mem.readW (L.X + BitVec.ofNat 64 904 + BitVec.ofNat 64 d) 64 =
      t.mem.readW (L.X + BitVec.ofNat 64 904 + BitVec.ofNat 64 d) 64 :=
    fun d h => hf.readW (Region.contains_self _ _) (fun r hr => hL.sv_disj (hrs r hr) h) (by decide)
  have khdr : bytesAt t'.mem (L.X + BitVec.ofNat 64 904 + BitVec.ofNat 64 80) 2 =
      bytesAt t.mem (L.X + BitVec.ofNat 64 904 + BitVec.ofNat 64 80) 2 :=
    Proof.MlKem.bytesAt_congr fun i hi =>
      hf.bytes (R := ⟨_, 2⟩) (fun r hr => hL.sv_disj (hrs r hr) (by decide)) (by show 2 ≤ 2 ^ 64; decide) hi
  refine ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp, (hg .x28 (by decide) (by decide)).trans hc.x28,
    fun r hr h28 h30 => (hg r hr h30).trans (hc.cs r hr h28 h30), fun r hr => (hvs r hr).trans (hc.vs r hr),
    (keep 0 (by decide)).trans hc.s28, (keep 8 (by decide)).trans hc.s30,
    fun j hj => (keep _ (by omega)).trans (hc.slot j hj), khdr.trans hc.hdr,
    hc.frame.trans (Frame.sub hf fun r hr => ?_)⟩
  rcases hrs r hr with h | h
  · exact ⟨L.XS, by simp, (h.trans (within_base L.X (by decide : 904 ≤ 1024))).sub⟩
  · exact ⟨L.STK, by simp, h⟩

/-- A byte of a region apart from `X` and `STK`, as on entry. -/
theorem bytesAt_eq (hc : VG.Proof.MlDsa.AArch64.Message.Ctx L g v m₀ t) {p : Addr} {n : Nat} (hx : L.XS.Disjoint ⟨p, n⟩)
    (hk : L.STK.Disjoint ⟨p, n⟩) (hn : n ≤ 2 ^ 64) : bytesAt t.mem p n = bytesAt m₀ p n :=
  Proof.MlKem.bytesAt_congr fun _ hi => Frame.bytes (R := ⟨p, n⟩) hc.frame (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hx.symm
    · exact hk.symm) hn hi

/-- Bytes of `X` are readable. -/
theorem inX (hc : VG.Proof.MlDsa.AArch64.Message.Ctx L g v m₀ t) (hL : L.Ok) {e k : Nat} (h₂ : e + k ≤ 1024) (hk : 0 < k) :
    InRegions (t.rd ++ t.wr) (L.X + BitVec.ofNat 64 e) k := by
  obtain ⟨R, hR, hc'⟩ := hL.inW h₂ hk
  exact ⟨R, by rw [hc.rd, hc.wr]; exact List.mem_append_right _ hR, hc'⟩

end Ctx

end VG.Proof.MlDsa.AArch64.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Message.Args`. -/
section

/-!
# ML-DSA on AArch64, `sign_message` and `verify_message`: the moves of a call's arguments

Untrusted: everything here is checked by Lean. Each argument's value
(`Arg.val`): a saved argument (a slot at `x28 + f`), plus an offset, an
offset from `x28`, an immediate, or `x0`. The moves of a list of arguments
into distinct registers but `x28`, with `x0` read only before it is written
(`argsOk`), leave each its value and change nothing else (`setArgs_ok`).
-/

namespace VG.Proof.MlDsa.AArch64.Message

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.AArch64 (Only wp_nil wp_ldrx wp_addImm wp_movz)

/-- The value of an argument in the state `s`. -/
def _root_.VG.Impl.MlDsa.AArch64.Message.Arg.val (s : State) : Arg → BitVec 64
  | .slot f => s.mem.readW (s.gpr .x28 + BitVec.ofNat 64 f) 64
  | .slotOff f o => s.mem.readW (s.gpr .x28 + BitVec.ofNat 64 f) 64 + BitVec.ofNat 64 o
  | .off o => s.gpr .x28 + BitVec.ofNat 64 o
  | .imm v => BitVec.ofNat 64 v
  | .ret => s.gpr .x0

/-- A slot within the 1 KiB, an offset or an immediate the instructions take. -/
def _root_.VG.Impl.MlDsa.AArch64.Message.Arg.ok : Arg → Bool
  | .slot f => decide (f % 8 = 0) && decide (f + 8 ≤ 1024)
  | .slotOff f o => decide (f % 8 = 0) && decide (f + 8 ≤ 1024) && decide (o < 4096)
  | .off o => decide (o < 4096)
  | .imm v => decide (v < 65536)
  | .ret => true

def _root_.VG.Impl.MlDsa.AArch64.Message.Arg.isRet : Arg → Bool
  | .ret => true
  | _ => false

/-- The slots of the 1 KiB are readable. -/
abbrev XOk (s : State) : Prop := ∀ f, f + 8 ≤ 1024 → InRegions (s.rd ++ s.wr) (s.gpr .x28 + BitVec.ofNat 64 f) 8

theorem Arg.mov_ok (d : Reg) (a : Arg) (ha : a.ok = true) (s : State) (hx : VG.Proof.MlDsa.AArch64.Message.XOk s) :
    WP isa (.block (a.mov d)) s fun s1 => s1.gpr d = a.val s ∧ Only [d] s s1 := by
  cases a with
  | slot f =>
    simp only [Arg.ok, Bool.and_eq_true, decide_eq_true_eq] at ha
    refine wp_ldrx ⟨ha.1, by omega⟩ rfl (hx f ha.2) fun s1 o1 e1 => wp_nil ⟨e1, o1⟩
  | slotOff f o =>
    simp only [Arg.ok, Bool.and_eq_true, decide_eq_true_eq] at ha
    refine wp_ldrx ⟨ha.1.1, by omega⟩ rfl (hx f ha.1.2) fun s1 o1 e1 => ?_
    refine wp_addImm ha.2 fun s2 o2 e2 => wp_nil ⟨by rw [e2, e1]; rfl, ?_⟩
    exact (o1.trans o2).mono (fun r hr => by simpa using hr)
  | off o =>
    simp only [Arg.ok, decide_eq_true_eq] at ha
    exact wp_addImm ha fun s1 o1 e1 => wp_nil ⟨e1, o1⟩
  | imm v =>
    simp only [Arg.ok, decide_eq_true_eq] at ha
    refine wp_movz fun s1 o1 e1 => wp_nil ⟨?_, o1⟩
    rw [e1]
    apply BitVec.eq_of_toNat_eq
    simp only [Arg.val, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  | ret =>
    exact wp_addImm (by decide) fun s1 o1 e1 => wp_nil ⟨by rw [e1, BitVec.add_zero]; rfl, o1⟩

/-- Distinct registers but `x28`, each argument fit for its instructions,
and `x0` read only before it is written. -/
def argsOk : List (Reg × Arg) → Bool
  | [] => true
  | (d, a) :: as => a.ok && d != .x28 &&
      as.all (fun da => da.1 != d && (d != .x0 || !da.2.isRet)) && VG.Proof.MlDsa.AArch64.Message.argsOk as

/-- The value of an argument is the same after a move into another register
(not `x28`, and not `x0` if the argument is `x0`). -/
theorem Arg.val_only {d : Reg} (hd : d ≠ .x28) {s s1 : State} (o : Only [d] s s1) (a : Arg)
    (ha : d ≠ .x0 ∨ a.isRet = false) : a.val s1 = a.val s := by
  have h28 : s1.gpr .x28 = s.gpr .x28 := o.gpr _ (by simp only [List.mem_singleton]; exact fun h => hd h.symm)
  cases a with
  | ret =>
    simp only [Arg.isRet, Bool.true_eq_false, or_false] at ha
    simp only [Arg.val]
    exact o.gpr _ (by simp only [List.mem_singleton]; exact fun h => ha h.symm)
  | _ => simp only [Arg.val, h28, o.mem]

theorem XOk.only {d : Reg} (hd : d ≠ .x28) {s s1 : State} (o : Only [d] s s1) (h : VG.Proof.MlDsa.AArch64.Message.XOk s) : VG.Proof.MlDsa.AArch64.Message.XOk s1 := by
  intro f hf
  rw [o.rd, o.wr, o.gpr _ (by simp only [List.mem_singleton]; exact fun h => hd h.symm)]
  exact h f hf

/-- The moves of the arguments `as`. -/
theorem setArgs_ok : ∀ (as : List (Reg × Arg)), VG.Proof.MlDsa.AArch64.Message.argsOk as = true → ∀ s : State, VG.Proof.MlDsa.AArch64.Message.XOk s →
    WP isa (.block (setArgs as)) s fun s1 => (∀ da ∈ as, s1.gpr da.1 = da.2.val s) ∧ Only (as.map (·.1)) s s1
  | [], _, s, _ => wp_nil ⟨fun _ h => by simp at h, Only.refl _ _⟩
  | (d, a) :: as, h, s, hx => by
    simp only [VG.Proof.MlDsa.AArch64.Message.argsOk, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true, Bool.or_eq_true,
      Bool.not_eq_true'] at h
    obtain ⟨⟨⟨ha, hd⟩, hall⟩, hrest⟩ := h
    simp only [setArgs, List.flatMap_cons]
    rw [WP.block_append_iff]
    refine WP.mono (Arg.mov_ok d a ha s hx) fun s1 ⟨h1, o1⟩ => ?_
    refine WP.mono (VG.Proof.MlDsa.AArch64.Message.setArgs_ok as hrest s1 (hx.only hd o1)) fun s2 ⟨h2, o2⟩ => ⟨fun da hda => ?_, ?_⟩
    · rcases List.mem_cons.mp hda with rfl | hda
      · rw [o2.gpr _ (fun hm => by
          obtain ⟨x, hx', hx''⟩ := List.mem_map.mp hm
          exact (hall x hx').1 hx''), h1]
      · rw [h2 da hda, Arg.val_only hd o1 da.2 ((hall da hda).2.elim .inl fun h' => .inr h')]
    · exact (o1.trans o2).mono (by simp)

/-! ## In `Ctx` -/

section
variable {L : VG.Proof.MlDsa.AArch64.Message.Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {t : State}

theorem Ctx.xOk (hc : VG.Proof.MlDsa.AArch64.Message.Ctx L g v m₀ t) (hL : L.Ok) : VG.Proof.MlDsa.AArch64.Message.XOk t := fun f hf => by
  rw [hc.x28]; exact hc.inX hL hf (by omega)

theorem Ctx.off (hc : VG.Proof.MlDsa.AArch64.Message.Ctx L g v m₀ t) (o : Nat) : (Arg.off o).val t = L.X + BitVec.ofNat 64 o := by
  simp only [Arg.val, hc.x28]

/-- The saved argument `j`. -/
theorem Ctx.slotJ (hc : VG.Proof.MlDsa.AArch64.Message.Ctx L g v m₀ t) {j : Nat} (hj : j < 8) :
    (Arg.slot (920 + 8 * j)).val t = L.vals.getD j 0 := by
  have := hc.slot j hj
  simp only [Arg.val, hc.x28]
  rw [add_add] at this
  rw [← this, show 904 + (16 + 8 * j) = 920 + 8 * j by omega]

end

end VG.Proof.MlDsa.AArch64.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Message.Depth`. -/
section

/-!
# ML-DSA on AArch64: how deep the frames of signing and verification nest

Untrusted: everything here is checked by Lean. Frames nest at most once in
`vg_mldsa*_sign` and `vg_mldsa*_verify`, with any implementation of the
Keccak permutation (`sign_dle`, `verify_dle`): their own code has no frames,
and those of the functions they call nest at most once (`DLe`, from the
structure of the code, `dle_tac`). So their calls use the 16 bytes of stack
below the stack pointer.
-/

namespace VG.Proof.MlDsa.AArch64.Message

open VG VG.AArch64

/-- Frames nest at most `d` deep in `c` and the functions it calls (a
structure, so that unification never unfolds it into a computation of the
depth). -/
structure DLe (d : Nat) (c : Prog isa) : Prop where
  le : c.aarch64Depth ≤ d

section
variable {d : Nat}

theorem DLe.block (is : List Instr) : VG.Proof.MlDsa.AArch64.Message.DLe d (.block is) := ⟨Nat.zero_le _⟩

theorem DLe.seq {a b : Prog isa} (ha : VG.Proof.MlDsa.AArch64.Message.DLe d a) (hb : VG.Proof.MlDsa.AArch64.Message.DLe d b) : VG.Proof.MlDsa.AArch64.Message.DLe d (.seq a b) := ⟨Nat.max_le.mpr ⟨ha.1, hb.1⟩⟩

theorem DLe.ite {c : isa.Cond} {a b : Prog isa} (ha : VG.Proof.MlDsa.AArch64.Message.DLe d a) (hb : VG.Proof.MlDsa.AArch64.Message.DLe d b) : VG.Proof.MlDsa.AArch64.Message.DLe d (.ite c a b) :=
  ⟨Nat.max_le.mpr ⟨ha.1, hb.1⟩⟩

theorem DLe.loop {c : isa.Cond} {a : Prog isa} (ha : VG.Proof.MlDsa.AArch64.Message.DLe d a) : VG.Proof.MlDsa.AArch64.Message.DLe d (.loop a c) := ⟨ha.1⟩

theorem DLe.call {c : Prog isa} (n : String) (h : VG.Proof.MlDsa.AArch64.Message.DLe d c) : VG.Proof.MlDsa.AArch64.Message.DLe d (.call n c) := ⟨h.1⟩

theorem DLe.seqR {f : Nat → Prog isa} (h : ∀ k, VG.Proof.MlDsa.AArch64.Message.DLe d (f k)) :
    ∀ a n, VG.Proof.MlDsa.AArch64.Message.DLe d (Impl.MlDsa.AArch64.Call.seqR f a n)
  | _, 0 => DLe.block _
  | a, n + 1 => DLe.seq (h a) (DLe.seqR h (a + 1) n)

theorem DLe.of_fd {c : Prog isa} (h : 16 * c.aarch64Depth ≤ 16) : VG.Proof.MlDsa.AArch64.Message.DLe 1 c := ⟨by omega⟩

end

/-- `DLe` of code from its structure, given that of the functions it calls. -/
macro "dle_tac" : tactic =>
  `(tactic| repeat' (first
    | (apply DLe.call; assumption)
    | apply DLe.seq
    | apply DLe.ite
    | apply DLe.loop
    | (apply DLe.seqR; intro)
    | apply DLe.block))

end VG.Proof.MlDsa.AArch64.Message

namespace VG.Proof.MlDsa.AArch64.Message
open VG VG.AArch64

section
variable (c : Impl.Sha3.AArch64.Callee) (P : Impl.MlDsa.AArch64.Sign.Prims) (p : Spec.MlDsa.Params)
    (ha : VG.Proof.MlDsa.AArch64.Message.DLe 1 (Impl.Sha3.AArch64.Stream.absorbWith c)) (hp : VG.Proof.MlDsa.AArch64.Message.DLe 1 (Impl.Sha3.AArch64.Stream.padWith c))
    (hs : VG.Proof.MlDsa.AArch64.Message.DLe 1 (Impl.Sha3.AArch64.Stream.squeezeWith c))
    (h1 : VG.Proof.MlDsa.AArch64.Message.DLe 1 P.ntt) (h2 : VG.Proof.MlDsa.AArch64.Message.DLe 1 P.invNtt) (h3 : VG.Proof.MlDsa.AArch64.Message.DLe 1 P.mul) (h4 : VG.Proof.MlDsa.AArch64.Message.DLe 1 P.mulAdd) (h5 : VG.Proof.MlDsa.AArch64.Message.DLe 1 P.add)
    (h6 : VG.Proof.MlDsa.AArch64.Message.DLe 1 P.sub) (h7 : VG.Proof.MlDsa.AArch64.Message.DLe 1 P.rejNTT) (h8 : VG.Proof.MlDsa.AArch64.Message.DLe 1 P.expandMask) (h9 : VG.Proof.MlDsa.AArch64.Message.DLe 1 P.ball)
    (h10 : VG.Proof.MlDsa.AArch64.Message.DLe 1 P.highBits) (h11 : VG.Proof.MlDsa.AArch64.Message.DLe 1 P.lowBits) (h12 : VG.Proof.MlDsa.AArch64.Message.DLe 1 P.normLt) (h13 : VG.Proof.MlDsa.AArch64.Message.DLe 1 P.makeHint)
    (h14 : VG.Proof.MlDsa.AArch64.Message.DLe 1 P.simpleBitPack) (h15 : VG.Proof.MlDsa.AArch64.Message.DLe 1 P.bitPack) (h16 : VG.Proof.MlDsa.AArch64.Message.DLe 1 P.bitUnpack) (h17 : VG.Proof.MlDsa.AArch64.Message.DLe 1 P.hintBitPack) (h18 : VG.Proof.MlDsa.AArch64.Message.DLe 1 P.rej4)
include ha hp hs h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 in
theorem sign_dle : VG.Proof.MlDsa.AArch64.Message.DLe 1 (Impl.MlDsa.AArch64.Sign.signWith c P p) := by
  unfold Impl.MlDsa.AArch64.Sign.signWith
  dle_tac
end

section
variable (c : Impl.Sha3.AArch64.Callee) (P : Impl.MlDsa.AArch64.KeyGen.Prims) (p : Spec.MlDsa.Params)
    (ha : VG.Proof.MlDsa.AArch64.Message.DLe 1 (Impl.Sha3.AArch64.Stream.absorbWith c)) (hp : VG.Proof.MlDsa.AArch64.Message.DLe 1 (Impl.Sha3.AArch64.Stream.padWith c))
    (hs : VG.Proof.MlDsa.AArch64.Message.DLe 1 (Impl.Sha3.AArch64.Stream.squeezeWith c))
    (h1 : VG.Proof.MlDsa.AArch64.Message.DLe 1 P.ntt) (h2 : VG.Proof.MlDsa.AArch64.Message.DLe 1 P.invNtt) (h3 : VG.Proof.MlDsa.AArch64.Message.DLe 1 P.mul) (h4 : VG.Proof.MlDsa.AArch64.Message.DLe 1 P.mulAdd)
    (h6 : VG.Proof.MlDsa.AArch64.Message.DLe 1 P.sub) (h7 : VG.Proof.MlDsa.AArch64.Message.DLe 1 P.rejNtt) (h9 : VG.Proof.MlDsa.AArch64.Message.DLe 1 P.ball)
    (h11 : VG.Proof.MlDsa.AArch64.Message.DLe 1 P.useHint) (h12 : VG.Proof.MlDsa.AArch64.Message.DLe 1 P.normLt) (h13 : VG.Proof.MlDsa.AArch64.Message.DLe 1 P.simpleBitPack) (h15 : VG.Proof.MlDsa.AArch64.Message.DLe 1 P.bitUnpack) (h16 : VG.Proof.MlDsa.AArch64.Message.DLe 1 P.unpackT1) (h17 : VG.Proof.MlDsa.AArch64.Message.DLe 1 P.hintUnpack) (h18 : VG.Proof.MlDsa.AArch64.Message.DLe 1 P.rej4)

include ha hp hs h1 h2 h3 h4 h6 h7 h9 h11 h12 h13 h15 h16 h17 h18 in
theorem verify_dle : VG.Proof.MlDsa.AArch64.Message.DLe 1 (Impl.MlDsa.AArch64.Verify.verifyWith c P p) := by
  unfold Impl.MlDsa.AArch64.Verify.verifyWith
  dle_tac
end

section
variable (v : Proof.Sha3.AArch64.Permutation)

theorem keccak_dle :
    VG.Proof.MlDsa.AArch64.Message.DLe 1 (Impl.Sha3.AArch64.Stream.absorbWith v.callee) ∧ VG.Proof.MlDsa.AArch64.Message.DLe 1 (Impl.Sha3.AArch64.Stream.padWith v.callee) ∧
      VG.Proof.MlDsa.AArch64.Message.DLe 1 (Impl.Sha3.AArch64.Stream.squeezeWith v.callee) :=
  ⟨⟨by rw [v.absorb_depth]⟩, ⟨by rw [v.pad_depth]⟩, ⟨by rw [v.squeeze_depth]⟩⟩

/-- `vg_mldsa*_sign`, with the Keccak permutation of `v`. -/
theorem signWith_dle (p : Spec.MlDsa.Params) :
    VG.Proof.MlDsa.AArch64.Message.DLe 1 (Impl.MlDsa.AArch64.Sign.signWith v.callee (Sign.primsWith v.callee) p) := by
  have C := Sign.prims_okWith (keccak := v)
  obtain ⟨ha, hp, hs⟩ := VG.Proof.MlDsa.AArch64.Message.keccak_dle v
  exact VG.Proof.MlDsa.AArch64.Message.sign_dle _ _ p ha hp hs (.of_fd C.ntt.fd) (.of_fd C.invNtt.fd) (.of_fd C.mul.fd) (.of_fd C.mulAdd.fd)
    (.of_fd C.add.fd) (.of_fd C.sub.fd) (.of_fd C.rejNTT.fd) (.of_fd C.expandMask.fd) (.of_fd C.ball.fd)
    (.of_fd C.highBits.fd) (.of_fd C.lowBits.fd) (.of_fd C.normLt.fd) (.of_fd C.makeHint.fd)
    (.of_fd C.simpleBitPack.fd) (.of_fd C.bitPack.fd) (.of_fd C.bitUnpack.fd) (.of_fd C.hintBitPack.fd) (.of_fd C.rej4.fd)

/-- `vg_mldsa*_verify`, with the Keccak permutation of `v`. -/
theorem verifyWith_dle (p : Spec.MlDsa.Params) :
    VG.Proof.MlDsa.AArch64.Message.DLe 1 (Impl.MlDsa.AArch64.Verify.verifyWith v.callee (Impl.MlDsa.AArch64.KeyGen.primsWith v.callee) p) := by
  have C := KeyGen.prims_okWith (keccak := v)
  obtain ⟨ha, hp, hs⟩ := VG.Proof.MlDsa.AArch64.Message.keccak_dle v
  exact VG.Proof.MlDsa.AArch64.Message.verify_dle _ _ p ha hp hs (.of_fd C.ntt.fd) (.of_fd C.invNtt.fd) (.of_fd C.mul.fd) (.of_fd C.mulAdd.fd)
    (.of_fd C.sub.fd) (.of_fd C.rejNtt.fd) (.of_fd C.ball.fd) (.of_fd C.useHint.fd) (.of_fd C.normLt.fd)
    (.of_fd C.simpleBitPack.fd) (.of_fd C.bitUnpack.fd) (.of_fd C.unpackT1.fd) (.of_fd C.hintUnpack.fd) (.of_fd C.rej4.fd)

end

end VG.Proof.MlDsa.AArch64.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Message.Hash`. -/
section

/-!
# ML-DSA on AArch64, `sign_message` and `verify_message`: SHAKE256 through the sponge functions

Untrusted: everything here is checked by Lean. In `Ctx`: zeroing the Keccak
state at `X` (`zeroSt_ok`), and the calls of `vg_keccak_absorb`,
`vg_keccak_pad` and `vg_keccak_squeeze` (with the permutation of `v`) on it,
with their working space at `X + 200` (`kabs_ok`, `kpad_ok`, `ksqz_ok`); then
`muHash`, which leaves `μ = H(tr ‖ 0 ‖ ctx_len ‖ ctx ‖ M, 64)` at `X + 840`
(`muHash_ok`), and `trHash`, which leaves `H(pk, 64)` there (`trHash_ok`).
-/

namespace VG.Proof.MlDsa.AArch64.Message

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.AArch64 (Only Kept HSetup Rg absorb_callWith pad_callWith squeeze_callWith zeroState_ok)
open VG.Spec.Sha3 (bytesAt stateAt rates absorb pad squeezeFrom Repr)
open VG.Spec.MlDsa (Params)

section
variable {L : VG.Proof.MlDsa.AArch64.Message.Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem}

theorem x0 (L : VG.Proof.MlDsa.AArch64.Message.Lay) : L.X + BitVec.ofNat 64 0 = L.X := BitVec.add_zero _

theorem st_ks : Region.Disjoint ⟨L.ST, 200⟩ ⟨L.KS, 640⟩ := by
  have := Offset.disjoint L.X (d := 0) (n := 200) (e := 200) (k := 640) (by omega) (by omega) (by omega)
  simpa only [VG.Proof.MlDsa.AArch64.Message.x0] using this

theorem st_mu : Region.Disjoint ⟨L.ST, 200⟩ ⟨L.MU, 64⟩ := by
  have := Offset.disjoint L.X (d := 0) (n := 200) (e := 840) (k := 64) (by omega) (by omega) (by omega)
  simpa only [VG.Proof.MlDsa.AArch64.Message.x0] using this

theorem mu_ks : Region.Disjoint ⟨L.MU, 64⟩ ⟨L.KS, 640⟩ :=
  Offset.disjoint L.X (d := 840) (n := 64) (e := 200) (k := 640) (by omega) (by omega) (by omega)

theorem w_st : Within ⟨L.ST, 200⟩ L.W := within_base _ (by omega)
theorem w_ks : Within ⟨L.KS, 640⟩ L.W := within_off _ (by omega)
theorem w_mu : Within ⟨L.MU, 64⟩ L.W := within_off _ (by omega)

theorem k_st (hL : L.Ok) : L.STK.Disjoint ⟨L.ST, 200⟩ := by
  have := hL.stk_x (e := 0) (k := 200) (by omega); simpa only [VG.Proof.MlDsa.AArch64.Message.x0] using this
theorem k_ks (hL : L.Ok) : L.STK.Disjoint ⟨L.KS, 640⟩ := hL.stk_x (by omega)
theorem k_mu (hL : L.Ok) : L.STK.Disjoint ⟨L.MU, 64⟩ := hL.stk_x (by omega)

theorem cov_x (hL : L.Ok) {e k : Nat} (h₂ : e + k ≤ 1024) :
    ∃ R ∈ L.rd ++ L.wr, Within ⟨L.X + BitVec.ofNat 64 e, k⟩ R := by
  obtain ⟨R, hR, hw⟩ := hL.covX h₂; exact ⟨R, List.mem_append_right _ hR, hw⟩

theorem cov_xw (hL : L.Ok) {e k : Nat} (h₂ : e + k ≤ 1024) :
    ∃ R ∈ L.wr, Within ⟨L.X + BitVec.ofNat 64 e, k⟩ R := hL.covX h₂

theorem not_pres {r : Reg} (hr : r ∈ preserved) (rs : List Reg) (h : ∀ d ∈ rs, d ∉ preserved := by decide) :
    r ∉ rs := fun hm => h r hm hr

/-- What a call that keeps `Kept` of regions within the first 904 bytes of
`X` and the stack frame leaves. -/
theorem Ctx.kept {t t' : State} (hc : VG.Proof.MlDsa.AArch64.Message.Ctx L g vv m₀ t) (hL : L.Ok) {rs : List Region} (hk : Kept rs t t')
    (hrs : ∀ r ∈ rs, Within r L.W ∨ Region.Sub r L.STK) : VG.Proof.MlDsa.AArch64.Message.Ctx L g vv m₀ t' :=
  hc.keep hL hk.rd hk.wr hk.sp hk.vcs hk.cs hk.frame hrs

/-! ## Zeroing the state -/

theorem zeroSt_ok (hL : L.Ok) {t : State} (hc : VG.Proof.MlDsa.AArch64.Message.Ctx L g vv m₀ t) :
    WP isa (.block zeroSt) t fun t' => VG.Proof.MlDsa.AArch64.Message.Ctx L g vv m₀ t' ∧ Frame [⟨L.ST, 200⟩] t.mem t'.mem ∧
      stateAt t'.mem L.ST = Spec.Sha3.zero := by
  have hS : HSetup .x28 0 200 136 t := by
    refine ⟨⟨by decide, by decide⟩, by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hc.x28, VG.Proof.MlDsa.AArch64.Message.x0]; exact VG.Proof.MlDsa.AArch64.Message.st_ks
    · rw [hc.sp]; exact hL.nSP
    · simp only [Proof.MlKem.AArch64.stk, hc.sp, hc.x28, VG.Proof.MlDsa.AArch64.Message.x0]; exact VG.Proof.MlDsa.AArch64.Message.k_st hL
    · simp only [Proof.MlKem.AArch64.stk, hc.sp, hc.x28]; exact VG.Proof.MlDsa.AArch64.Message.k_ks hL
    · rw [hc.x28, hc.wr, VG.Proof.MlDsa.AArch64.Message.x0]
      exact VG.Proof.MlDsa.AArch64.Message.covers_of_within fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · have := VG.Proof.MlDsa.AArch64.Message.cov_xw hL (e := 0) (k := 200) (by omega); rwa [VG.Proof.MlDsa.AArch64.Message.x0] at this
        · exact VG.Proof.MlDsa.AArch64.Message.cov_xw hL (e := 200) (by omega)
  refine WP.mono (zeroState_ok hS ⟨rfl, rfl, rfl, fun _ _ _ => rfl⟩) fun t' ⟨hk, hz⟩ => ?_
  simp only [Proof.MlKem.AArch64.STr, hc.x28, VG.Proof.MlDsa.AArch64.Message.x0] at hk hz
  exact ⟨hc.kept hL hk (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact .inl VG.Proof.MlDsa.AArch64.Message.w_st),
    hk.frame, hz⟩

/-! ## Absorbing -/

/-- The arguments of a call of `vg_keccak_absorb`. -/
abbrev absArgs (src len pos : Arg) : List (Reg × Arg) :=
  [(.x2, pos), (.x0, .off oST), (.x1, .imm 136), (.x3, src), (.x4, len), (.x5, .off oKS)]

theorem kabs_ok (v : Proof.Sha3.AArch64.Permutation) (hL : L.Ok) {t : State} (hc : VG.Proof.MlDsa.AArch64.Message.Ctx L g vv m₀ t)
    {src len pos : Arg} (hok : VG.Proof.MlDsa.AArch64.Message.argsOk (VG.Proof.MlDsa.AArch64.Message.absArgs src len pos) = true)
    {dp : Addr} {n q : Nat} (hdp : src.val t = dp) (hn : len.val t = BitVec.ofNat 64 n)
    (hq : pos.val t = BitVec.ofNat 64 q) (hql : q < 136) (hnl : n < 2 ^ 64)
    (hin : ∃ R ∈ L.rd ++ L.wr, Within ⟨dp, n⟩ R)
    (dS : Region.Disjoint ⟨dp, n⟩ ⟨L.ST, 200⟩) (dK : Region.Disjoint ⟨dp, n⟩ ⟨L.KS, 640⟩)
    (kD : L.STK.Disjoint ⟨dp, n⟩) :
    WP isa (kabs v.callee src len pos) t fun t' => VG.Proof.MlDsa.AArch64.Message.Ctx L g vv m₀ t' ∧
      Frame [⟨L.ST, 200⟩, ⟨L.KS, 640⟩, L.STK] t.mem t'.mem ∧
      (∀ msg, Repr t.mem L.ST 136 msg → q = msg.length % 136 →
        Repr t'.mem L.ST 136 (msg ++ bytesAt t.mem dp n)) ∧ (t'.gpr .x0).toNat = (q + n) % 136 := by
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Message.setArgs_ok _ hok t (hc.xOk hL)) fun t1 ⟨hA, o⟩ => ?_)
  have hc1 : VG.Proof.MlDsa.AArch64.Message.Ctx L g vv m₀ t1 := hc.regs o.rd o.wr o.sp o.mem o.vcs fun r hr _ => o.gpr r (by simp only [List.map_cons, List.map_nil]; exact VG.Proof.MlDsa.AArch64.Message.not_pres hr _)
  have e2 := hA (.x2, pos) (by simp)
  have e0 := hA (.x0, .off oST) (by simp)
  have e1 := hA (.x1, .imm 136) (by simp)
  have e3 := hA (.x3, src) (by simp)
  have e4 := hA (.x4, len) (by simp)
  have e5 := hA (.x5, .off oKS) (by simp)
  simp only [Arg.val, hc.x28, oST, oKS, VG.Proof.MlDsa.AArch64.Message.x0] at e0 e1 e5
  rw [hq] at e2
  rw [hdp] at e3
  rw [hn] at e4
  have hs1 : t1.sp = L.SP := hc1.sp
  refine absorb_callWith v (st := L.ST) (dt := dp) (sc := L.KS) (rate := 136) (pos := q) (len := n) e0
    (by rw [e1]; rfl) (by rw [e2, BitVec.toNat_ofNat]; omega) e3 (by rw [e4, BitVec.toNat_ofNat]; omega) e5
    (by decide) hql VG.Proof.MlDsa.AArch64.Message.st_ks dS dK (by rw [hs1]; exact hL.nSP) (by simp only [Proof.MlKem.AArch64.stk, hs1]; exact VG.Proof.MlDsa.AArch64.Message.k_st hL)
    (by simp only [Proof.MlKem.AArch64.stk, hs1]; exact kD) (by simp only [Proof.MlKem.AArch64.stk, hs1]; exact VG.Proof.MlDsa.AArch64.Message.k_ks hL) ?_ ?_ fun s' hk hrep hx => ?_
  · rw [hc1.rd, hc1.wr]
    refine VG.Proof.MlDsa.AArch64.Message.covers_of_within fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hin
    · have := VG.Proof.MlDsa.AArch64.Message.cov_x hL (e := 0) (k := 200) (by omega); rwa [VG.Proof.MlDsa.AArch64.Message.x0] at this
    · exact VG.Proof.MlDsa.AArch64.Message.cov_x hL (e := 200) (by omega)
  · rw [hc1.wr]
    refine VG.Proof.MlDsa.AArch64.Message.covers_of_within fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have := VG.Proof.MlDsa.AArch64.Message.cov_xw hL (e := 0) (k := 200) (by omega); rwa [VG.Proof.MlDsa.AArch64.Message.x0] at this
    · exact VG.Proof.MlDsa.AArch64.Message.cov_xw hL (e := 200) (by omega)
  · rw [hs1] at hk
    refine ⟨hc1.kept hL hk fun r hr => ?_, by rw [← o.mem]; exact hk.frame, fun msg hm hp => ?_, hx⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [.inl VG.Proof.MlDsa.AArch64.Message.w_st, .inl VG.Proof.MlDsa.AArch64.Message.w_ks, .inr fun _ h => h]
    · have := hrep msg (by rw [o.mem]; exact hm) hp
      rwa [o.mem] at this

/-! ## Padding -/

/-- The arguments of a call of `vg_keccak_pad`. -/
abbrev padArgs (pos : Arg) : List (Reg × Arg) :=
  [(.x2, pos), (.x0, .off oST), (.x1, .imm 136), (.x3, .imm 0x1f), (.x4, .off oKS)]

theorem kpad_ok (v : Proof.Sha3.AArch64.Permutation) (hL : L.Ok) {t : State} (hc : VG.Proof.MlDsa.AArch64.Message.Ctx L g vv m₀ t)
    {pos : Arg} (hok : VG.Proof.MlDsa.AArch64.Message.argsOk (VG.Proof.MlDsa.AArch64.Message.padArgs pos) = true) {q : Nat}
    (hq : pos.val t = BitVec.ofNat 64 q) (hql : q < 136) :
    WP isa (kpad v.callee pos) t fun t' => VG.Proof.MlDsa.AArch64.Message.Ctx L g vv m₀ t' ∧
      Frame [⟨L.ST, 200⟩, ⟨L.KS, 640⟩, L.STK] t.mem t'.mem ∧
      (∀ msg, Repr t.mem L.ST 136 msg → q = msg.length % 136 →
        stateAt t'.mem L.ST = absorb 136 (pad 136 Spec.Sha3.shakeSuffix msg)) := by
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Message.setArgs_ok _ hok t (hc.xOk hL)) fun t1 ⟨hA, o⟩ => ?_)
  have hc1 : VG.Proof.MlDsa.AArch64.Message.Ctx L g vv m₀ t1 := hc.regs o.rd o.wr o.sp o.mem o.vcs fun r hr _ => o.gpr r (by simp only [List.map_cons, List.map_nil]; exact VG.Proof.MlDsa.AArch64.Message.not_pres hr _)
  have e2 := hA (.x2, pos) (by simp)
  have e0 := hA (.x0, .off oST) (by simp)
  have e1 := hA (.x1, .imm 136) (by simp)
  have e3 := hA (.x3, .imm 0x1f) (by simp)
  have e4 := hA (.x4, .off oKS) (by simp)
  simp only [Arg.val, hc.x28, oST, oKS, VG.Proof.MlDsa.AArch64.Message.x0] at e0 e1 e3 e4
  rw [hq] at e2
  have hs1 : t1.sp = L.SP := hc1.sp
  refine pad_callWith v (st := L.ST) (sc := L.KS) (rate := 136) (pos := q) e0
    (by rw [e1]; rfl) (by rw [e2, BitVec.toNat_ofNat]; omega) e4
    (by decide) hql VG.Proof.MlDsa.AArch64.Message.st_ks (by rw [hs1]; exact hL.nSP) (by simp only [Proof.MlKem.AArch64.stk, hs1]; exact VG.Proof.MlDsa.AArch64.Message.k_st hL)
    (by simp only [Proof.MlKem.AArch64.stk, hs1]; exact VG.Proof.MlDsa.AArch64.Message.k_ks hL) ?_ ?_ fun s' hk hpost => ?_
  · rw [hc1.rd, hc1.wr]
    refine VG.Proof.MlDsa.AArch64.Message.covers_of_within fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have := VG.Proof.MlDsa.AArch64.Message.cov_x hL (e := 0) (k := 200) (by omega); rwa [VG.Proof.MlDsa.AArch64.Message.x0] at this
    · exact VG.Proof.MlDsa.AArch64.Message.cov_x hL (e := 200) (by omega)
  · rw [hc1.wr]
    refine VG.Proof.MlDsa.AArch64.Message.covers_of_within fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have := VG.Proof.MlDsa.AArch64.Message.cov_xw hL (e := 0) (k := 200) (by omega); rwa [VG.Proof.MlDsa.AArch64.Message.x0] at this
    · exact VG.Proof.MlDsa.AArch64.Message.cov_xw hL (e := 200) (by omega)
  · rw [hs1] at hk
    refine ⟨hc1.kept hL hk fun r hr => ?_, by rw [← o.mem]; exact hk.frame, fun msg hm hp => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [.inl VG.Proof.MlDsa.AArch64.Message.w_st, .inl VG.Proof.MlDsa.AArch64.Message.w_ks, .inr fun _ h => h]
    · rw [hpost msg (by rw [o.mem]; exact hm) hp, e3]
      rfl

/-! ## Squeezing -/

/-- The arguments of a call of `vg_keccak_squeeze`. -/
abbrev sqzArgs : List (Reg × Arg) :=
  [(.x0, .off oST), (.x1, .imm 136), (.x2, .imm 0), (.x3, .off oMU), (.x4, .imm 64), (.x5, .off oKS)]

theorem ksqz_ok (v : Proof.Sha3.AArch64.Permutation) (hL : L.Ok) {t : State} (hc : VG.Proof.MlDsa.AArch64.Message.Ctx L g vv m₀ t) :
    WP isa (ksqz v.callee) t fun t' => VG.Proof.MlDsa.AArch64.Message.Ctx L g vv m₀ t' ∧
      Frame [⟨L.ST, 200⟩, ⟨L.MU, 64⟩, ⟨L.KS, 640⟩, L.STK] t.mem t'.mem ∧
      bytesAt t'.mem L.MU 64 = squeezeFrom 136 (stateAt t.mem L.ST) 0 64 := by
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Message.setArgs_ok VG.Proof.MlDsa.AArch64.Message.sqzArgs (by decide) t (hc.xOk hL)) fun t1 ⟨hA, o⟩ => ?_)
  have hc1 : VG.Proof.MlDsa.AArch64.Message.Ctx L g vv m₀ t1 := hc.regs o.rd o.wr o.sp o.mem o.vcs fun r hr _ => o.gpr r (by simp only [List.map_cons, List.map_nil]; exact VG.Proof.MlDsa.AArch64.Message.not_pres hr _)
  have e0 := hA (.x0, .off oST) (by simp)
  have e1 := hA (.x1, .imm 136) (by simp)
  have e2 := hA (.x2, .imm 0) (by simp)
  have e3 := hA (.x3, .off oMU) (by simp)
  have e4 := hA (.x4, .imm 64) (by simp)
  have e5 := hA (.x5, .off oKS) (by simp)
  simp only [Arg.val, hc.x28, oST, oKS, oMU, VG.Proof.MlDsa.AArch64.Message.x0] at e0 e1 e2 e3 e4 e5
  have hs1 : t1.sp = L.SP := hc1.sp
  refine squeeze_callWith v (st := L.ST) (out := L.MU) (sc := L.KS) (rate := 136) (pos := 0) (len := 64) e0
    (by rw [e1]; rfl) (by rw [e2]; rfl) e3 (by rw [e4]; rfl) e5
    (by decide) (by decide) VG.Proof.MlDsa.AArch64.Message.st_mu VG.Proof.MlDsa.AArch64.Message.st_ks VG.Proof.MlDsa.AArch64.Message.mu_ks (by rw [hs1]; exact hL.nSP) (by simp only [Proof.MlKem.AArch64.stk, hs1]; exact VG.Proof.MlDsa.AArch64.Message.k_st hL)
    (by simp only [Proof.MlKem.AArch64.stk, hs1]; exact VG.Proof.MlDsa.AArch64.Message.k_mu hL)
    (by simp only [Proof.MlKem.AArch64.stk, hs1]; exact VG.Proof.MlDsa.AArch64.Message.k_ks hL) ?_ ?_ fun s' hk hout _ _ => ?_
  · rw [hc1.rd, hc1.wr]
    refine VG.Proof.MlDsa.AArch64.Message.covers_of_within fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · have := VG.Proof.MlDsa.AArch64.Message.cov_x hL (e := 0) (k := 200) (by omega); rwa [VG.Proof.MlDsa.AArch64.Message.x0] at this
    · exact VG.Proof.MlDsa.AArch64.Message.cov_x hL (e := 840) (by omega)
    · exact VG.Proof.MlDsa.AArch64.Message.cov_x hL (e := 200) (by omega)
  · rw [hc1.wr]
    refine VG.Proof.MlDsa.AArch64.Message.covers_of_within fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · have := VG.Proof.MlDsa.AArch64.Message.cov_xw hL (e := 0) (k := 200) (by omega); rwa [VG.Proof.MlDsa.AArch64.Message.x0] at this
    · exact VG.Proof.MlDsa.AArch64.Message.cov_xw hL (e := 840) (by omega)
    · exact VG.Proof.MlDsa.AArch64.Message.cov_xw hL (e := 200) (by omega)
  · rw [hs1] at hk
    refine ⟨hc1.kept hL hk fun r hr => ?_, by rw [← o.mem]; exact hk.frame, by rw [hout, o.mem]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [.inl VG.Proof.MlDsa.AArch64.Message.w_st, .inl VG.Proof.MlDsa.AArch64.Message.w_mu, .inl VG.Proof.MlDsa.AArch64.Message.w_ks, .inr fun _ h => h]

end

end VG.Proof.MlDsa.AArch64.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Message.HashMu`. -/
section

/-!
# ML-DSA on AArch64, `sign_message` and `verify_message`: `μ` and `tr`

Untrusted: everything here is checked by Lean. In `Ctx`, `muHash` leaves
`μ = H(tr ‖ 0 ‖ ctx_len ‖ ctx ‖ M, 64)` at `X + 840` (`muHash_ok`), and
`trHash` leaves `H(pk, 64)` there (`trHash_ok`): from the zeroed state, each
absorb continues the message from the position the previous one returned.
-/

namespace VG.Proof.MlDsa.AArch64.Message

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Spec.Sha3 (bytesAt stateAt Repr)
open VG.Spec.MlDsa (Params)

section
variable {L : VG.Proof.MlDsa.AArch64.Message.Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem}

/-- The two bytes `0 ‖ ctx_len` of the formatted message. -/
abbrev hdrBytes (L : VG.Proof.MlDsa.AArch64.Message.Lay) : List Byte := [0, BitVec.ofNat 8 L.ctxLen.toNat]

theorem ofNat_toNat_self (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt]

theorem ofNat_toNat_eq {x : BitVec 64} {n : Nat} (h : x.toNat = n) : x = BitVec.ofNat 64 n := by
  subst h; exact (VG.Proof.MlDsa.AArch64.Message.ofNat_toNat_self x).symm

/-- The arguments of an absorb are fit, if its data and length are not `x0`. -/
theorem absOk {src len pos : Arg} (h1 : src.ok = true) (h2 : len.ok = true) (h3 : pos.ok = true)
    (r1 : src.isRet = false) (r2 : len.isRet = false) : VG.Proof.MlDsa.AArch64.Message.argsOk (VG.Proof.MlDsa.AArch64.Message.absArgs src len pos) = true := by
  simp (config := { decide := true }) [VG.Proof.MlDsa.AArch64.Message.argsOk, h1, h2, h3, r1, r2]

theorem padOk {pos : Arg} (h : pos.ok = true) : VG.Proof.MlDsa.AArch64.Message.argsOk (VG.Proof.MlDsa.AArch64.Message.padArgs pos) = true := by
  simp (config := { decide := true }) [VG.Proof.MlDsa.AArch64.Message.argsOk, h]

theorem Ctx.slotV {t : State} (hc : VG.Proof.MlDsa.AArch64.Message.Ctx L g vv m₀ t) {f j : Nat} (hf : f = 920 + 8 * j) (hj : j < 8) :
    (Arg.slot f).val t = L.vals.getD j 0 := by
  subst hf; exact hc.slotJ hj

theorem Ctx.hdrX {t : State} (hc : VG.Proof.MlDsa.AArch64.Message.Ctx L g vv m₀ t) : bytesAt t.mem (L.X + BitVec.ofNat 64 984) 2 = VG.Proof.MlDsa.AArch64.Message.hdrBytes L := by
  have := hc.hdr; rwa [add_add] at this

theorem muHash_ok (v : Proof.Sha3.AArch64.Permutation) (hL : L.Ok) {t : State} (hc : VG.Proof.MlDsa.AArch64.Message.Ctx L g vv m₀ t)
    {tr : Arg} (hok : tr.ok = true) (hret : tr.isRet = false) {trp : Addr}
    (htr : ∀ t', VG.Proof.MlDsa.AArch64.Message.Ctx L g vv m₀ t' → tr.val t' = trp)
    (hin : ∃ R ∈ L.rd ++ L.wr, Within ⟨trp, 64⟩ R)
    (dS : Region.Disjoint ⟨trp, 64⟩ ⟨L.ST, 200⟩) (dK : Region.Disjoint ⟨trp, 64⟩ ⟨L.KS, 640⟩)
    (kD : L.STK.Disjoint ⟨trp, 64⟩) :
    WP isa (muHash v.callee tr) t fun t' => VG.Proof.MlDsa.AArch64.Message.Ctx L g vv m₀ t' ∧
      bytesAt t'.mem L.MU 64 = Spec.MlDsa.H (bytesAt t.mem trp 64 ++ VG.Proof.MlDsa.AArch64.Message.hdrBytes L ++
        bytesAt m₀ L.ctx L.ctxLen.toNat ++ bytesAt m₀ L.msg L.len.toNat) 64 := by
  have hctx := hL.ctxLt
  -- Zero the state.
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Message.zeroSt_ok hL hc) fun t1 ⟨hc1, hf1, hz⟩ => ?_)
  have etr : bytesAt t1.mem trp 64 = bytesAt t.mem trp 64 :=
    Proof.MlKem.bytesAt_congr fun i hi => hf1.bytes (R := ⟨trp, 64⟩) (by simpa using dS) (by show 64 ≤ 2 ^ 64; decide) hi
  have hR1 : Repr t1.mem L.ST 136 [] := Proof.MlKem.repr_nil hz
  -- `tr`.
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Message.kabs_ok v hL hc1 (VG.Proof.MlDsa.AArch64.Message.absOk hok rfl rfl hret rfl) (htr t1 hc1) rfl rfl (by decide)
    (by decide) hin dS dK kD) fun t2 ⟨hc2, _, hR2, _⟩ => ?_)
  have hR2 := hR2 [] hR1 rfl
  rw [List.nil_append, etr] at hR2
  -- `0 ‖ ctx_len`.
  have fS : Region.Disjoint ⟨L.X + BitVec.ofNat 64 984, 2⟩ ⟨L.ST, 200⟩ := by
    have := Offset.disjoint L.X (d := 984) (n := 2) (e := 0) (k := 200) (by omega) (by omega) (by omega)
    simpa only [VG.Proof.MlDsa.AArch64.Message.x0] using this
  have fK : Region.Disjoint ⟨L.X + BitVec.ofNat 64 984, 2⟩ ⟨L.KS, 640⟩ :=
    Offset.disjoint L.X (d := 984) (n := 2) (e := 200) (k := 640) (by omega) (by omega) (by omega)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Message.kabs_ok v hL hc2 (VG.Proof.MlDsa.AArch64.Message.absOk rfl rfl rfl rfl rfl) (by rw [hc2.off]; rfl) rfl rfl
    (by decide) (by decide) (VG.Proof.MlDsa.AArch64.Message.cov_x hL (e := 984) (k := 2) (by omega)) fS fK (hL.stk_x (by omega)))
    fun t3 ⟨hc3, _, hR3, _⟩ => ?_)
  have hR3 := hR3 _ hR2 (by rw [Proof.MlKem.bytesAt_length])
  rw [hc2.hdrX] at hR3
  -- The context string.
  have hcl : (Arg.slot fCtxLen).val t3 = BitVec.ofNat 64 L.ctxLen.toNat := by
    rw [hc3.slotV (f := fCtxLen) (j := 4) rfl (by omega), VG.Proof.MlDsa.AArch64.Message.ofNat_toNat_self]; rfl
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Message.kabs_ok v hL hc3 (VG.Proof.MlDsa.AArch64.Message.absOk rfl rfl rfl rfl rfl)
    (by rw [hc3.slotV (f := fCtx) (j := 3) rfl (by omega)]; rfl) hcl rfl (by decide) (by omega)
    ⟨L.CTX, List.mem_append_left _ hL.inCtx, within_self _⟩
    (by have := hL.x_r hL.xCtx (e := 0) (k := 200) (by omega); simpa only [VG.Proof.MlDsa.AArch64.Message.x0] using this.symm)
    (hL.x_r hL.xCtx (e := 200) (k := 640) (by omega)).symm hL.kCtx)
    fun t4 ⟨hc4, _, hR4, hx4⟩ => ?_)
  have hR4 := hR4 _ hR3 (by simp only [List.length_append, Proof.MlKem.bytesAt_length, List.length_cons, List.length_nil])
  rw [hc3.bytesAt_eq hL.xCtx hL.kCtx (by have := hL.nCtx; omega)] at hR4
  -- The message.
  have hln : (Arg.slot fLen).val t4 = BitVec.ofNat 64 L.len.toNat := by
    rw [hc4.slotV (f := fLen) (j := 2) rfl (by omega), VG.Proof.MlDsa.AArch64.Message.ofNat_toNat_self]; rfl
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Message.kabs_ok v hL hc4 (VG.Proof.MlDsa.AArch64.Message.absOk rfl rfl rfl rfl rfl)
    (by rw [hc4.slotV (f := fMsg) (j := 1) rfl (by omega)]; rfl) hln (VG.Proof.MlDsa.AArch64.Message.ofNat_toNat_eq hx4) (Nat.mod_lt _ (by decide))
    (by have := L.len.isLt; omega) ⟨L.MSG, List.mem_append_left _ hL.inMsg, within_self _⟩
    (by have := hL.x_r hL.xMsg (e := 0) (k := 200) (by omega); simpa only [VG.Proof.MlDsa.AArch64.Message.x0] using this.symm)
    (hL.x_r hL.xMsg (e := 200) (k := 640) (by omega)).symm hL.kMsg)
    fun t5 ⟨hc5, _, hR5, hx5⟩ => ?_)
  have hR5 := hR5 _ hR4 (by simp only [List.length_append, Proof.MlKem.bytesAt_length, List.length_cons, List.length_nil])
  rw [hc4.bytesAt_eq hL.xMsg hL.kMsg (by have := hL.nMsg; omega)] at hR5
  -- Pad and squeeze.
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Message.kpad_ok v hL hc5 (VG.Proof.MlDsa.AArch64.Message.padOk rfl) (VG.Proof.MlDsa.AArch64.Message.ofNat_toNat_eq hx5) (Nat.mod_lt _ (by decide)))
    fun t6 ⟨hc6, _, hS6⟩ => ?_)
  have hS6 := hS6 _ hR5 (by simp only [List.length_append, Proof.MlKem.bytesAt_length, List.length_cons, List.length_nil]; omega)
  refine WP.mono (VG.Proof.MlDsa.AArch64.Message.ksqz_ok v hL hc6) fun t7 ⟨hc7, _, hm7⟩ => ⟨hc7, ?_⟩
  rw [hm7, hS6, Spec.MlDsa.H, Proof.MlKem.shake256_eq]

/-! ## `tr = H(pk, 64)` -/

theorem trHash_ok (v : Proof.Sha3.AArch64.Permutation) {p : Params} (hL : L.Ok) (hk : L.keyLen = p.pkLen)
    {t : State} (hc : VG.Proof.MlDsa.AArch64.Message.Ctx L g vv m₀ t) :
    WP isa (trHash v.callee p) t fun t' => VG.Proof.MlDsa.AArch64.Message.Ctx L g vv m₀ t' ∧
      bytesAt t'.mem L.MU 64 = Spec.MlDsa.H (bytesAt m₀ L.key L.keyLen) 64 := by
  have hkl := hL.hKey.2
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Message.zeroSt_ok hL hc) fun t1 ⟨hc1, _, hz⟩ => ?_)
  have hR1 : Repr t1.mem L.ST 136 [] := Proof.MlKem.repr_nil hz
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Message.kabs_ok v hL hc1 (n := L.keyLen) (q := 0)
    (VG.Proof.MlDsa.AArch64.Message.absOk rfl (by simp only [Arg.ok, decide_eq_true_eq]; omega) rfl rfl rfl)
    (by rw [hc1.slotV (f := fKey) (j := 0) rfl (by omega)]; rfl) (by rw [hk]; rfl) rfl (by decide) (by omega)
    ⟨L.KEY, List.mem_append_left _ hL.inKey, within_self _⟩
    (by have := hL.x_r hL.xKey (e := 0) (k := 200) (by omega); simpa only [VG.Proof.MlDsa.AArch64.Message.x0] using this.symm)
    (hL.x_r hL.xKey (e := 200) (k := 640) (by omega)).symm hL.kKey)
    fun t2 ⟨hc2, _, hR2, _⟩ => ?_)
  have hR2 := hR2 [] hR1 rfl
  rw [List.nil_append, hc1.bytesAt_eq hL.xKey hL.kKey (by have := hL.nKey; omega)] at hR2
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Message.kpad_ok v hL hc2 (VG.Proof.MlDsa.AArch64.Message.padOk (by simp only [Arg.ok, decide_eq_true_eq]; omega))
    (q := p.pkLen % 136) rfl (Nat.mod_lt _ (by decide))) fun t3 ⟨hc3, _, hS3⟩ => ?_)
  have hS3 := hS3 _ hR2 (by rw [Proof.MlKem.bytesAt_length, hk])
  refine WP.mono (VG.Proof.MlDsa.AArch64.Message.ksqz_ok v hL hc3) fun t4 ⟨hc4, _, hm4⟩ => ⟨hc4, ?_⟩
  rw [hm4, hS3, Spec.MlDsa.H, Proof.MlKem.shake256_eq]

end

end VG.Proof.MlDsa.AArch64.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Message.Entry`. -/
section

/-!
# ML-DSA on AArch64, `sign_message` and `verify_message`: entry and exit

Untrusted: everything here is checked by Lean. Stores of registers at
distinct offsets that are multiples of 8 from a base (`strs_ok`). The entry:
the address of `X` in `x9` and then `x28`, the caller's `x28` and `x30`
saved at `X + 904` and `X + 912`, the arguments at `X + 920 + 8j` and
`0 ‖ ctx_len` at `X + 984`, give `Ctx` (`enter_ok`). The exit restores
`x30` and `x28` (`leave_ok`).
-/

namespace VG.Proof.MlDsa.AArch64.Message

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.AArch64 (Only MemTo wp_nil wp_strx wp_strb wp_ldrx wp_movz wp_add wp_addImm wp_movImm)
open VG.Spec.Sha3 (bytesAt)

/-- Registers, permissions, stack pointer and SIMD registers unchanged. -/
structure Same (t t' : State) : Prop where
  gpr : t'.gpr = t.gpr
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  sp : t'.sp = t.sp
  vcs : ∀ r ∈ preservedV, (t'.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64

theorem Same.refl (t : State) : VG.Proof.MlDsa.AArch64.Message.Same t t := ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem Same.trans {a b c : State} (h₁ : VG.Proof.MlDsa.AArch64.Message.Same a b) (h₂ : VG.Proof.MlDsa.AArch64.Message.Same b c) : VG.Proof.MlDsa.AArch64.Message.Same a c :=
  ⟨h₂.gpr.trans h₁.gpr, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp,
    fun r hr => (h₂.vcs r hr).trans (h₁.vcs r hr)⟩

theorem Same.of_memTo {a b : State} {m : Mem} (h : MemTo a b m) : VG.Proof.MlDsa.AArch64.Message.Same a b := ⟨h.gpr, h.rd, h.wr, h.sp, h.vcs⟩

/-- Stores of registers at distinct offsets, multiples of 8, from `B` in `b`. -/
theorem strs_ok (b : Reg) (B : Addr) : ∀ (as : List (Reg × Nat)) (t : State), t.gpr b = B →
    (∀ a ∈ as, a.2 % 8 = 0 ∧ a.2 + 8 ≤ 4096 ∧ InRegions t.wr (B + BitVec.ofNat 64 a.2) 8) →
    (as.map (·.2)).Nodup →
    WP isa (.block (as.map fun a => .str .x a.1 b a.2)) t fun t' => VG.Proof.MlDsa.AArch64.Message.Same t t' ∧
      (∀ a ∈ as, t'.mem.readW (B + BitVec.ofNat 64 a.2) 64 = t.gpr a.1) ∧
      Frame (as.map fun a => ⟨B + BitVec.ofNat 64 a.2, 8⟩) t.mem t'.mem
  | [], t, _, _, _ => wp_nil ⟨Same.refl t, fun _ h => by simp at h, Frame.refl _ _⟩
  | (r, f) :: as, t, hb, ha, hn => by
    have h0 := ha (r, f) (List.mem_cons_self ..)
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    refine wp_strx ⟨h0.1, by omega⟩ (by rw [hb]) h0.2.2 fun s1 m1 => ?_
    have hs1 := Same.of_memTo m1
    refine WP.mono (VG.Proof.MlDsa.AArch64.Message.strs_ok b B as s1 (by rw [hs1.gpr, hb]) (fun a h => by
      rw [hs1.wr]; exact ha a (List.mem_cons_of_mem _ h)) hn.2) fun t' ⟨hs, hr, hf⟩ => ⟨hs1.trans hs, ?_, ?_⟩
    · intro a h
      rcases List.mem_cons.mp h with rfl | h
      · rw [hf.readW (r := ⟨B + BitVec.ofNat 64 f, 8⟩) (Region.contains_self _ _) (fun r' hr' => by
            simp only [List.mem_map] at hr'
            obtain ⟨a', ha', rfl⟩ := hr'
            have := ha a' (List.mem_cons_of_mem _ ha')
            have hne : f ≠ a'.2 := fun e => hn.1 ⟨a', ha', e.symm⟩
            exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide),
          m1.mem, Mem.readW_writeW_self64]
      · rw [hr a h, hs1.gpr]
    · have f1 : Frame [⟨B + BitVec.ofNat 64 f, 8⟩] t.mem s1.mem := by
        rw [m1.mem]
        exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
      refine (f1.mono fun r h => ?_).trans (hf.mono fun r h => ?_)
      · simp only [List.mem_singleton] at h; subst h; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ h

/-- The values the entry saves at `X + 920 + 8j`, and the registers they are in. -/
theorem saves_ok {as : List (Reg × Nat)} (hf : as.map (·.2) = [920, 928, 936, 944, 952, 960, 968, 976]) :
    ∀ a ∈ as, a.2 % 8 = 0 ∧ 920 ≤ a.2 ∧ a.2 + 8 ≤ 984 := by
  intro a ha
  have : a.2 ∈ as.map (·.2) := List.mem_map_of_mem ha
  rw [hf] at this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  omega

/-- The entry, from a state whose registers hold the layout's values. -/
theorem enter_ok {L : VG.Proof.MlDsa.AArch64.Message.Lay} (hL : L.Ok) {p : Spec.MlDsa.Params} (hE : oE p = L.E) {sr : Reg}
    (hsr : sr ≠ .x9) {as : List (Reg × Nat)} (hf : as.map (·.2) = [920, 928, 936, 944, 952, 960, 968, 976])
    {s : State} (hs : s.gpr sr = L.scr) (hsp : s.sp = L.SP) (hrd : s.rd = L.rd) (hwr : s.wr = L.wr)
    (h4 : s.gpr .x4 = L.ctxLen) (hv : ∀ j (hj : j < as.length), s.gpr (as[j]'hj).1 = L.vals.getD j 0)
    (hreg : ∀ a ∈ as, a.1 ≠ .x9 ∧ a.1 ≠ .x28) :
    WP isa (.block (enter sr p as)) s fun t => VG.Proof.MlDsa.AArch64.Message.Ctx L s.gpr s.v s.mem t := by
  have hlen : as.length = 8 := by rw [← List.length_map (f := (·.2)), hf]; rfl
  have hsv := VG.Proof.MlDsa.AArch64.Message.saves_ok hf
  unfold enter
  simp only [List.append_assoc]
  refine wp_movImm fun s1 o1 e1 => ?_
  rw [List.singleton_append]
  refine wp_add fun s2 o2 e2 => ?_
  rw [o1.get sr (by simpa using hsr), e1, hs] at e2
  -- `X` in `x9`.
  have eX : s2.gpr .x9 = L.X := by rw [e2, hE]
  rw [WP.block_append_iff]
  have hw2 : s2.wr = L.wr := by rw [o2.wr, o1.wr, hwr]
  refine WP.mono (VG.Proof.MlDsa.AArch64.Message.strs_ok .x9 L.X [(.x28, 904), (.x30, 912)] s2 eX (fun a ha => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact ⟨by decide, by decide, by rw [hw2]; exact hL.inW (by omega) (by omega)⟩
    · exact ⟨by decide, by decide, by rw [hw2]; exact hL.inW (by omega) (by omega)⟩) (by decide))
    fun s3 ⟨q3, r3, f3⟩ => ?_
  refine wp_addImm (by decide) fun s4 o4 e4 => ?_
  rw [q3.gpr, eX, BitVec.add_zero] at e4
  simp only [List.append_eq, List.nil_append]
  rw [WP.block_append_iff]
  have hw4 : s4.wr = L.wr := by rw [o4.wr, q3.wr, hw2]
  refine WP.mono (VG.Proof.MlDsa.AArch64.Message.strs_ok .x28 L.X as s4 e4 (fun a ha => ⟨(hsv a ha).1, by have := hsv a ha; omega,
    by rw [hw4]; have := hsv a ha; exact hL.inW (by omega) (by omega)⟩) (by rw [hf]; decide))
    fun s5 ⟨q5, r5, f5⟩ => ?_
  have hw5 : s5.wr = L.wr := by rw [q5.wr, hw4]
  have e5 : s5.gpr .x28 = L.X := by rw [q5.gpr, e4]
  refine wp_movz fun s6 o6 e6 => wp_strb (a := L.X + BitVec.ofNat 64 984) (by decide) (by rw [o6.get .x28, e5]; rfl)
    (by rw [o6.wr, hw5]; exact hL.inW (by omega) (by omega)) fun s7 m7 => ?_
  have q7 := Same.of_memTo m7
  refine wp_strb (a := L.X + BitVec.ofNat 64 985) (by decide) (by rw [q7.gpr, o6.get .x28, e5]; rfl)
    (by rw [q7.wr, o6.wr, hw5]; exact hL.inW (by omega) (by omega)) fun s8 m8 => wp_nil ?_
  have q8 := Same.of_memTo m8
  -- The registers.
  have g8 : ∀ r, r ≠ .x9 → r ≠ .x28 → s8.gpr r = s.gpr r := fun r h9 h28 => by
    rw [q8.gpr, q7.gpr, o6.get r (by simpa using h9), q5.gpr, o4.get r (by simpa using h28), q3.gpr,
      o2.get r (by simpa using h9), o1.get r (by simpa using h9)]
  have x48 : s8.gpr .x4 = L.ctxLen := by rw [g8 .x4 (by decide) (by decide), h4]
  -- The memory.
  have m8e : s8.mem = (s5.mem.writeW (L.X + BitVec.ofNat 64 984) ((s6.gpr .x9).setWidth 8)).writeW
      (L.X + BitVec.ofNat 64 985) ((s7.gpr .x4).setWidth 8) := by
    rw [m8.mem, m7.mem, o6.mem, q7.gpr]
  have hdr2 : ∀ d, d + 8 ≤ 80 → s8.mem.readW (L.X + BitVec.ofNat 64 (904 + d)) 64 =
      s5.mem.readW (L.X + BitVec.ofNat 64 (904 + d)) 64 := fun d hd => by
    rw [m8e, Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
  -- Reads of the saves, from `s5`.
  have r5' : ∀ d, d + 8 ≤ 16 → s5.mem.readW (L.X + BitVec.ofNat 64 (904 + d)) 64 =
      s3.mem.readW (L.X + BitVec.ofNat 64 (904 + d)) 64 := fun d hd => by
    rw [f5.readW (r := ⟨L.X + BitVec.ofNat 64 (904 + d), 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_map] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      have := hsv a ha
      exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide), o4.mem]
  have sx28 : s3.mem.readW (L.X + BitVec.ofNat 64 904) 64 = s.gpr .x28 := by
    rw [r3 (.x28, 904) (by simp), o2.get .x28, o1.get .x28]
  have sx30 : s3.mem.readW (L.X + BitVec.ofNat 64 912) 64 = s.gpr .x30 := by
    rw [r3 (.x30, 912) (by simp), o2.get .x30, o1.get .x30]
  have hX := hL.nX
  refine ⟨by rw [q8.rd, q7.rd, o6.rd, q5.rd, o4.rd, q3.rd, o2.rd, o1.rd, hrd],
    by rw [q8.wr, q7.wr, o6.wr, hw5], by rw [q8.sp, q7.sp, o6.sp, q5.sp, o4.sp, q3.sp, o2.sp, o1.sp, hsp],
    by rw [q8.gpr, q7.gpr, o6.get .x28, e5], fun r hr h28 _ => g8 r (fun e => by subst e; revert hr; decide) h28,
    fun r hr => by rw [q8.vcs r hr, q7.vcs r hr, o6.vcs r hr, q5.vcs r hr, o4.vcs r hr, q3.vcs r hr, o2.vcs r hr,
      o1.vcs r hr], ?_, ?_, fun j hj => ?_, ?_, ?_⟩
  · rw [add_add, hdr2 0 (by omega), r5' 0 (by omega)]; exact sx28
  · rw [add_add, hdr2 8 (by omega), r5' 8 (by omega)]; exact sx30
  · have hj' : j < as.length := by omega
    have hm : as[j] ∈ as := List.getElem_mem hj'
    have hf2 : as[j].2 = 920 + 8 * j := by
      have := congrArg (·[j]?) hf
      simp only [List.getElem?_map, List.getElem?_eq_getElem hj', Option.map_some] at this
      have hj8 : j < 8 := hj
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simpa using this
    rw [add_add, hdr2 (16 + 8 * j) (by omega), show 904 + (16 + 8 * j) = as[j].2 by omega, r5 _ hm,
      o4.get _ (by simpa using (hreg _ hm).2), q3.gpr, o2.get _ (by simpa using (hreg _ hm).1),
      o1.get _ (by simpa using (hreg _ hm).1)]
    exact hv j hj'
  · have n45 : L.X + BitVec.ofNat 64 984 ≠ L.X + BitVec.ofNat 64 985 :=
      Offset.add_ofNat_ne _ (by omega) (by omega) (by omega)
    have x46 : s6.gpr .x4 = L.ctxLen := by rw [o6.get .x4, q5.gpr, o4.get .x4, q3.gpr, o2.get .x4, o1.get .x4, h4]
    rw [add_add, m8e, q7.gpr, x46, e6]
    generalize L.X = X at n45 ⊢
    simp only [bytesAt, List.range, List.range.loop, List.map_cons, List.map_nil, add_add, Nat.reduceAdd]
    rw [byte_writeW_other _ n45, byte_writeW_self, byte_writeW_self]
    refine List.cons_eq_cons.mpr ⟨rfl, List.cons_eq_cons.mpr ⟨?_, rfl⟩⟩
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  · have hs1 : s.mem = s2.mem := by rw [o2.mem, o1.mem]
    have hxs : ∀ d n, d + n ≤ 1024 → Region.Sub ⟨L.X + BitVec.ofNat 64 d, n⟩ L.XS := fun d n h =>
      Offset.sub_base _ h
    have a3 : Frame [L.XS, L.STK] s2.mem s3.mem := Frame.sub f3 fun r hr => by
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨L.XS, by simp, hxs 904 8 (by omega)⟩
      · exact ⟨L.XS, by simp, hxs 912 8 (by omega)⟩
    have a5 : Frame [L.XS, L.STK] s4.mem s5.mem := Frame.sub f5 fun r hr => by
      simp only [List.mem_map] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      have := hsv a ha
      exact ⟨L.XS, by simp, hxs a.2 8 (by omega)⟩
    have a8 : Frame [L.XS, L.STK] s5.mem s8.mem := by
      rw [m8e]
      exact ((Frame.refl _ _).writeW (List.mem_cons_self ..) _ (Offset.contains_base _ (by omega) (by omega))).writeW
        (List.mem_cons_self ..) _ (Offset.contains_base _ (by omega) (by omega))
    rw [hs1]
    exact a3.trans ((by rw [o4.mem] : Frame [L.XS, L.STK] s3.mem s4.mem ↔ _).mpr (Frame.refl _ _) |>.trans
      (a5.trans a8))

/-- What the exit needs: `x28` pointing at `X`, the callee-saved registers
but `x28` and `x30`, and the saves of those two. -/
structure Fin (L : VG.Proof.MlDsa.AArch64.Message.Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (t : State) : Prop where
  rd : t.rd = L.rd
  wr : t.wr = L.wr
  sp : t.sp = L.SP
  x28 : t.gpr .x28 = L.X
  cs : ∀ r ∈ preserved, r ≠ .x28 → r ≠ .x30 → t.gpr r = g r
  vs : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (vv r).extractLsb' 0 64
  s28 : t.mem.readW (L.X + BitVec.ofNat 64 904 + BitVec.ofNat 64 0) 64 = g .x28
  s30 : t.mem.readW (L.X + BitVec.ofNat 64 904 + BitVec.ofNat 64 8) 64 = g .x30

theorem Ctx.fin {L : VG.Proof.MlDsa.AArch64.Message.Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (hc : VG.Proof.MlDsa.AArch64.Message.Ctx L g vv m₀ t) : VG.Proof.MlDsa.AArch64.Message.Fin L g vv t :=
  ⟨hc.rd, hc.wr, hc.sp, hc.x28, hc.cs, hc.vs, hc.s28, hc.s30⟩

/-- The exit: `x30`, then `x28`, from the saves. -/
theorem leave_ok {L : VG.Proof.MlDsa.AArch64.Message.Lay} (hL : L.Ok) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {t : State}
    (hc : VG.Proof.MlDsa.AArch64.Message.Fin L g vv t) :
    WP isa (.block leave) t fun t' => (∀ r ∈ preserved, t'.gpr r = g r) ∧ t'.sp = L.SP ∧
      (∀ r ∈ preservedV, (t'.v r).extractLsb' 0 64 = (vv r).extractLsb' 0 64) ∧ t'.mem = t.mem ∧
      t'.gpr .x0 = t.gpr .x0 ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have h30 := hc.s30
  have h28 := hc.s28
  rw [add_add] at h30 h28
  have hx : ∀ f, f + 8 ≤ 1024 → InRegions (t.rd ++ t.wr) (L.X + BitVec.ofNat 64 f) 8 := fun f hf => by
    obtain ⟨R, hR, hc'⟩ := hL.inW (e := f) (k := 8) hf (by omega)
    exact ⟨R, by rw [hc.rd, hc.wr]; exact List.mem_append_right _ hR, hc'⟩
  refine wp_ldrx (a := L.X + BitVec.ofNat 64 (904 + 8)) (by decide) (by rw [hc.x28]; rfl)
    (hx 912 (by omega)) fun t1 o1 e1 => ?_
  refine wp_ldrx (a := L.X + BitVec.ofNat 64 (904 + 0)) (by decide) (by rw [o1.get .x28, hc.x28]; rfl)
    (by rw [o1.rd, o1.wr]; exact hx 904 (by omega)) fun t2 o2 e2 => wp_nil ?_
  refine ⟨fun r hr => ?_, by rw [o2.sp, o1.sp, hc.sp], fun r hr => by rw [o2.vcs r hr, o1.vcs r hr, hc.vs r hr],
    by rw [o2.mem, o1.mem], by rw [o2.get .x0, o1.get .x0], by rw [o2.rd, o1.rd], by rw [o2.wr, o1.wr]⟩
  by_cases e28 : r = .x28
  · subst e28; rw [e2, o1.mem, h28]
  · by_cases e30 : r = .x30
    · subst e30; rw [o2.get .x30, e1, h30]
    · rw [o2.get r (by simpa using e28), o1.get r (by simpa using e30), hc.cs r hr e28 e30]

end VG.Proof.MlDsa.AArch64.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Message.Pre`. -/
section

/-!
# ML-DSA on AArch64, `sign_message` and `verify_message`: the preconditions and the layouts

Untrusted: everything here is checked by Lean. The preconditions of
`signMessageContract p AArch64.abi 16` and `verifyMessageContract p
AArch64.abi 16`, spelled out (`SPre`, `VPre`), and the layouts of runs from
states satisfying them (`slay`, `vlay`).
-/

namespace VG.Proof.MlDsa.AArch64.Message

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Spec.MlDsa

/-- The parameter sets. -/
def params : List Params := [mlDsa44, mlDsa65, mlDsa87]

/-- The size of `scratch` in bytes. -/
abbrev mScrLen (p : Params) : Nat := messageScratchWords p * 8

theorem mScr_eq (p : Params) : VG.Proof.MlDsa.AArch64.Message.mScrLen p = oE p + 1024 := by
  simp only [VG.Proof.MlDsa.AArch64.Message.mScrLen, messageScratchWords, oE]; omega

theorem oE_lt {p : Params} (hp : p ∈ VG.Proof.MlDsa.AArch64.Message.params) : oE p + 1024 < 2 ^ 31 := by
  simp only [VG.Proof.MlDsa.AArch64.Message.params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> decide

section
variable (p : Params) (s : State)

abbrev rKey (n : Nat) : Region := ⟨s.gpr .x0, n⟩
abbrev rMsg : Region := ⟨s.gpr .x1, (s.gpr .x2).toNat⟩
abbrev rCtx : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
abbrev rStk : Region := ⟨s.sp - 16#64, 16⟩

end

/-! ## Signing -/

/-- The precondition of `signMessageContract p AArch64.abi 16`. -/
structure SPre (p : Params) (s : State) : Prop where
  sp : 16 ≤ s.sp.toNat
  rd : s.rd = [VG.Proof.MlDsa.AArch64.Message.rKey s p.skLen, VG.Proof.MlDsa.AArch64.Message.rMsg s, VG.Proof.MlDsa.AArch64.Message.rCtx s, ⟨s.gpr .x5, 32⟩]
  wr : s.wr = [⟨s.gpr .x6, p.sigLen⟩, ⟨s.gpr .x7, VG.Proof.MlDsa.AArch64.Message.mScrLen p⟩]
  skSig : (VG.Proof.MlDsa.AArch64.Message.rKey s p.skLen).Disjoint ⟨s.gpr .x6, p.sigLen⟩
  skScr : (VG.Proof.MlDsa.AArch64.Message.rKey s p.skLen).Disjoint ⟨s.gpr .x7, VG.Proof.MlDsa.AArch64.Message.mScrLen p⟩
  msgSig : (VG.Proof.MlDsa.AArch64.Message.rMsg s).Disjoint ⟨s.gpr .x6, p.sigLen⟩
  msgScr : (VG.Proof.MlDsa.AArch64.Message.rMsg s).Disjoint ⟨s.gpr .x7, VG.Proof.MlDsa.AArch64.Message.mScrLen p⟩
  ctxSig : (VG.Proof.MlDsa.AArch64.Message.rCtx s).Disjoint ⟨s.gpr .x6, p.sigLen⟩
  ctxScr : (VG.Proof.MlDsa.AArch64.Message.rCtx s).Disjoint ⟨s.gpr .x7, VG.Proof.MlDsa.AArch64.Message.mScrLen p⟩
  rndSig : Region.Disjoint ⟨s.gpr .x5, 32⟩ ⟨s.gpr .x6, p.sigLen⟩
  rndScr : Region.Disjoint ⟨s.gpr .x5, 32⟩ ⟨s.gpr .x7, VG.Proof.MlDsa.AArch64.Message.mScrLen p⟩
  sigScr : Region.Disjoint ⟨s.gpr .x6, p.sigLen⟩ ⟨s.gpr .x7, VG.Proof.MlDsa.AArch64.Message.mScrLen p⟩
  stkSk : (VG.Proof.MlDsa.AArch64.Message.rStk s).Disjoint (VG.Proof.MlDsa.AArch64.Message.rKey s p.skLen)
  stkMsg : (VG.Proof.MlDsa.AArch64.Message.rStk s).Disjoint (VG.Proof.MlDsa.AArch64.Message.rMsg s)
  stkCtx : (VG.Proof.MlDsa.AArch64.Message.rStk s).Disjoint (VG.Proof.MlDsa.AArch64.Message.rCtx s)
  stkRnd : (VG.Proof.MlDsa.AArch64.Message.rStk s).Disjoint ⟨s.gpr .x5, 32⟩
  stkSig : (VG.Proof.MlDsa.AArch64.Message.rStk s).Disjoint ⟨s.gpr .x6, p.sigLen⟩
  stkScr : (VG.Proof.MlDsa.AArch64.Message.rStk s).Disjoint ⟨s.gpr .x7, VG.Proof.MlDsa.AArch64.Message.mScrLen p⟩
  nSk : (s.gpr .x0).toNat + p.skLen ≤ 2 ^ 64
  nMsg : (s.gpr .x1).toNat + (s.gpr .x2).toNat ≤ 2 ^ 64
  nCtx : (s.gpr .x3).toNat + (s.gpr .x4).toNat ≤ 2 ^ 64
  nRnd : (s.gpr .x5).toNat + 32 ≤ 2 ^ 64
  nSig : (s.gpr .x6).toNat + p.sigLen ≤ 2 ^ 64
  nScr : (s.gpr .x7).toNat + VG.Proof.MlDsa.AArch64.Message.mScrLen p ≤ 2 ^ 64

theorem sPre_of {p : Params} {s : State} (h : (signMessageContract p AArch64.abi 16).pre s) : VG.Proof.MlDsa.AArch64.Message.SPre p s := by
  sig_pre [signMessageContract, signMessageSig, AArch64.abi, AArch64.argRegs, List.range, List.range.loop] at h
  obtain ⟨a1, a2, a3, a4, a5, h⟩ := h
  obtain ⟨a6, a7, a8, a9, a10, h⟩ := h
  obtain ⟨a11, a12, a13, a14, a15, h⟩ := h
  obtain ⟨a16, a17, a18, a19, a20, h⟩ := h
  obtain ⟨a21, a22, a23, a24⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22,
    a23, a24⟩

theorem skLen_ge {p : Params} (hp : p ∈ VG.Proof.MlDsa.AArch64.Message.params) : 128 ≤ p.skLen ∧ p.skLen < 2 ^ 16 := by
  simp only [VG.Proof.MlDsa.AArch64.Message.params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> decide

theorem pkLen_ge {p : Params} (hp : p ∈ VG.Proof.MlDsa.AArch64.Message.params) : 128 ≤ p.pkLen ∧ p.pkLen < 2 ^ 16 := by
  simp only [VG.Proof.MlDsa.AArch64.Message.params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> decide

/-- The layout of a run of `sign_message` from `s`. -/
def slay (p : Params) (s : State) : VG.Proof.MlDsa.AArch64.Message.Lay where
  SP := s.sp
  key := s.gpr .x0
  keyLen := p.skLen
  msg := s.gpr .x1
  len := s.gpr .x2
  ctx := s.gpr .x3
  ctxLen := s.gpr .x4
  rnd := s.gpr .x5
  sig := s.gpr .x6
  scr := s.gpr .x7
  E := oE p
  rd := s.rd
  wr := s.wr

theorem slay_X (p : Params) (s : State) : Within (VG.Proof.MlDsa.AArch64.Message.slay p s).XS ⟨s.gpr .x7, VG.Proof.MlDsa.AArch64.Message.mScrLen p⟩ :=
  ⟨oE p, rfl, by show oE p + 1024 ≤ VG.Proof.MlDsa.AArch64.Message.mScrLen p; rw [VG.Proof.MlDsa.AArch64.Message.mScr_eq]⟩

theorem toNat_X {scr : Addr} {e n : Nat} (h : scr.toNat + n ≤ 2 ^ 64) (he : e + 1024 ≤ n) :
    (scr + BitVec.ofNat 64 e).toNat + 1024 ≤ 2 ^ 64 := by
  rw [toNat_add_ofNat (by omega)]; omega

theorem slay_ok {p : Params} (hp : p ∈ VG.Proof.MlDsa.AArch64.Message.params) {s : State} (h : VG.Proof.MlDsa.AArch64.Message.SPre p s) (h8 : (s.gpr .x4).toNat < 256) :
    (VG.Proof.MlDsa.AArch64.Message.slay p s).Ok := by
  have hX := VG.Proof.MlDsa.AArch64.Message.slay_X p s
  have hXs := hX.sub
  have hE := VG.Proof.MlDsa.AArch64.Message.oE_lt hp
  refine ⟨h8, hE, VG.Proof.MlDsa.AArch64.Message.skLen_ge hp, h.sp, VG.Proof.MlDsa.AArch64.Message.toNat_X (e := oE p) h.nScr (by rw [VG.Proof.MlDsa.AArch64.Message.mScr_eq]),
    ⟨_, by simp [VG.Proof.MlDsa.AArch64.Message.slay, h.wr], hX⟩, by simp [VG.Proof.MlDsa.AArch64.Message.slay, h.rd], by simp [VG.Proof.MlDsa.AArch64.Message.slay, h.rd], by simp [VG.Proof.MlDsa.AArch64.Message.slay, h.rd],
    h.skScr.symm.sub_left hXs, h.msgScr.symm.sub_left hXs, h.ctxScr.symm.sub_left hXs, h.stkScr.sub_right hXs,
    h.stkSk, h.stkMsg, h.stkCtx, h.nSk, h.nMsg, h.nCtx, ?_⟩
  intro R hR
  simp only [VG.Proof.MlDsa.AArch64.Message.slay, h.wr, List.mem_cons, List.not_mem_nil, or_false] at hR
  have := h.nSig; have := h.nScr
  rcases hR with rfl | rfl <;> simp only <;> omega

/-! ## Verification -/

/-- The precondition of `verifyMessageContract p AArch64.abi 16`. -/
structure VPre (p : Params) (s : State) : Prop where
  sp : 16 ≤ s.sp.toNat
  rd : s.rd = [VG.Proof.MlDsa.AArch64.Message.rKey s p.pkLen, VG.Proof.MlDsa.AArch64.Message.rMsg s, VG.Proof.MlDsa.AArch64.Message.rCtx s, ⟨s.gpr .x5, p.sigLen⟩]
  wr : s.wr = [⟨s.gpr .x6, VG.Proof.MlDsa.AArch64.Message.mScrLen p⟩]
  pkScr : (VG.Proof.MlDsa.AArch64.Message.rKey s p.pkLen).Disjoint ⟨s.gpr .x6, VG.Proof.MlDsa.AArch64.Message.mScrLen p⟩
  msgScr : (VG.Proof.MlDsa.AArch64.Message.rMsg s).Disjoint ⟨s.gpr .x6, VG.Proof.MlDsa.AArch64.Message.mScrLen p⟩
  ctxScr : (VG.Proof.MlDsa.AArch64.Message.rCtx s).Disjoint ⟨s.gpr .x6, VG.Proof.MlDsa.AArch64.Message.mScrLen p⟩
  sigScr : Region.Disjoint ⟨s.gpr .x5, p.sigLen⟩ ⟨s.gpr .x6, VG.Proof.MlDsa.AArch64.Message.mScrLen p⟩
  stkPk : (VG.Proof.MlDsa.AArch64.Message.rStk s).Disjoint (VG.Proof.MlDsa.AArch64.Message.rKey s p.pkLen)
  stkMsg : (VG.Proof.MlDsa.AArch64.Message.rStk s).Disjoint (VG.Proof.MlDsa.AArch64.Message.rMsg s)
  stkCtx : (VG.Proof.MlDsa.AArch64.Message.rStk s).Disjoint (VG.Proof.MlDsa.AArch64.Message.rCtx s)
  stkSig : (VG.Proof.MlDsa.AArch64.Message.rStk s).Disjoint ⟨s.gpr .x5, p.sigLen⟩
  stkScr : (VG.Proof.MlDsa.AArch64.Message.rStk s).Disjoint ⟨s.gpr .x6, VG.Proof.MlDsa.AArch64.Message.mScrLen p⟩
  nPk : (s.gpr .x0).toNat + p.pkLen ≤ 2 ^ 64
  nMsg : (s.gpr .x1).toNat + (s.gpr .x2).toNat ≤ 2 ^ 64
  nCtx : (s.gpr .x3).toNat + (s.gpr .x4).toNat ≤ 2 ^ 64
  nSig : (s.gpr .x5).toNat + p.sigLen ≤ 2 ^ 64
  nScr : (s.gpr .x6).toNat + VG.Proof.MlDsa.AArch64.Message.mScrLen p ≤ 2 ^ 64

theorem vPre_of {p : Params} {s : State} (h : (verifyMessageContract p AArch64.abi 16).pre s) : VG.Proof.MlDsa.AArch64.Message.VPre p s := by
  sig_pre [verifyMessageContract, verifyMessageSig, AArch64.abi, AArch64.argRegs, List.range, List.range.loop] at h
  obtain ⟨a1, a2, a3, a4, a5, h⟩ := h
  obtain ⟨a6, a7, a8, a9, a10, h⟩ := h
  obtain ⟨a11, a12, a13, a14, a15, a16, a17⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17⟩

/-- The layout of a run of `verify_message` from `s` (`sig` in the slot of `rnd` too). -/
def vlay (p : Params) (s : State) : VG.Proof.MlDsa.AArch64.Message.Lay where
  SP := s.sp
  key := s.gpr .x0
  keyLen := p.pkLen
  msg := s.gpr .x1
  len := s.gpr .x2
  ctx := s.gpr .x3
  ctxLen := s.gpr .x4
  rnd := s.gpr .x5
  sig := s.gpr .x5
  scr := s.gpr .x6
  E := oE p
  rd := s.rd
  wr := s.wr

theorem vlay_X (p : Params) (s : State) : Within (VG.Proof.MlDsa.AArch64.Message.vlay p s).XS ⟨s.gpr .x6, VG.Proof.MlDsa.AArch64.Message.mScrLen p⟩ :=
  ⟨oE p, rfl, by show oE p + 1024 ≤ VG.Proof.MlDsa.AArch64.Message.mScrLen p; rw [VG.Proof.MlDsa.AArch64.Message.mScr_eq]⟩

theorem vlay_ok {p : Params} (hp : p ∈ VG.Proof.MlDsa.AArch64.Message.params) {s : State} (h : VG.Proof.MlDsa.AArch64.Message.VPre p s) (h8 : (s.gpr .x4).toNat < 256) :
    (VG.Proof.MlDsa.AArch64.Message.vlay p s).Ok := by
  have hX := VG.Proof.MlDsa.AArch64.Message.vlay_X p s
  have hXs := hX.sub
  have hE := VG.Proof.MlDsa.AArch64.Message.oE_lt hp
  refine ⟨h8, hE, VG.Proof.MlDsa.AArch64.Message.pkLen_ge hp, h.sp, VG.Proof.MlDsa.AArch64.Message.toNat_X (e := oE p) h.nScr (by rw [VG.Proof.MlDsa.AArch64.Message.mScr_eq]),
    ⟨_, by simp [VG.Proof.MlDsa.AArch64.Message.vlay, h.wr], hX⟩, by simp [VG.Proof.MlDsa.AArch64.Message.vlay, h.rd], by simp [VG.Proof.MlDsa.AArch64.Message.vlay, h.rd], by simp [VG.Proof.MlDsa.AArch64.Message.vlay, h.rd],
    h.pkScr.symm.sub_left hXs, h.msgScr.symm.sub_left hXs, h.ctxScr.symm.sub_left hXs, h.stkScr.sub_right hXs,
    h.stkPk, h.stkMsg, h.stkCtx, h.nPk, h.nMsg, h.nCtx, ?_⟩
  intro R hR
  simp only [VG.Proof.MlDsa.AArch64.Message.vlay, h.wr, List.mem_cons, List.not_mem_nil, or_false] at hR
  have := h.nScr
  subst hR; simp only; omega

end VG.Proof.MlDsa.AArch64.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Message.SignCall`. -/
section

/-!
# ML-DSA on AArch64, `sign_message`: the call of the signing function on `μ`

Untrusted: everything here is checked by Lean. Any code verified against
`signContract p AArch64.abi 16` whose frames nest at most once (`SignFn`):
its call on the key, `μ` at `X + 840`, `rnd`, `sig` and the first
`scratchWords p` words of `scratch` (`signCall_ok`), after which the saves
are intact (`Fin`).
-/

namespace VG.Proof.MlDsa.AArch64.Message

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.AArch64 (Only)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- A signing function on `μ` that `sign_message` can call. -/
structure SignFn (p : Params) (c : Prog isa) : Prop where
  ver : Verified AArch64.target c (signContract p AArch64.abi 16)
  dle : VG.Proof.MlDsa.AArch64.Message.DLe 1 c

/-- The size of the working space of the signing function on `μ`. -/
abbrev sScr (p : Params) : Nat := scratchWords p * 8

/-- The precondition of `signContract p AArch64.abi 16`, from its facts. -/
theorem signC_pre {p : Params} {s : State} (sp : 16 ≤ s.sp.toNat)
    (rd : s.rd = [⟨s.gpr .x0, p.skLen⟩, ⟨s.gpr .x1, 64⟩, ⟨s.gpr .x2, 32⟩])
    (wr : s.wr = [⟨s.gpr .x3, p.sigLen⟩, ⟨s.gpr .x4, VG.Proof.MlDsa.AArch64.Message.sScr p⟩])
    (d03 : Region.Disjoint ⟨s.gpr .x0, p.skLen⟩ ⟨s.gpr .x3, p.sigLen⟩)
    (d04 : Region.Disjoint ⟨s.gpr .x0, p.skLen⟩ ⟨s.gpr .x4, VG.Proof.MlDsa.AArch64.Message.sScr p⟩)
    (d13 : Region.Disjoint ⟨s.gpr .x1, 64⟩ ⟨s.gpr .x3, p.sigLen⟩)
    (d14 : Region.Disjoint ⟨s.gpr .x1, 64⟩ ⟨s.gpr .x4, VG.Proof.MlDsa.AArch64.Message.sScr p⟩)
    (d23 : Region.Disjoint ⟨s.gpr .x2, 32⟩ ⟨s.gpr .x3, p.sigLen⟩)
    (d24 : Region.Disjoint ⟨s.gpr .x2, 32⟩ ⟨s.gpr .x4, VG.Proof.MlDsa.AArch64.Message.sScr p⟩)
    (d34 : Region.Disjoint ⟨s.gpr .x3, p.sigLen⟩ ⟨s.gpr .x4, VG.Proof.MlDsa.AArch64.Message.sScr p⟩)
    (k0 : (VG.Proof.MlDsa.AArch64.Message.rStk s).Disjoint ⟨s.gpr .x0, p.skLen⟩) (k1 : (VG.Proof.MlDsa.AArch64.Message.rStk s).Disjoint ⟨s.gpr .x1, 64⟩)
    (k2 : (VG.Proof.MlDsa.AArch64.Message.rStk s).Disjoint ⟨s.gpr .x2, 32⟩) (k3 : (VG.Proof.MlDsa.AArch64.Message.rStk s).Disjoint ⟨s.gpr .x3, p.sigLen⟩)
    (k4 : (VG.Proof.MlDsa.AArch64.Message.rStk s).Disjoint ⟨s.gpr .x4, VG.Proof.MlDsa.AArch64.Message.sScr p⟩)
    (n0 : (s.gpr .x0).toNat + p.skLen ≤ 2 ^ 64) (n1 : (s.gpr .x1).toNat + 64 ≤ 2 ^ 64)
    (n2 : (s.gpr .x2).toNat + 32 ≤ 2 ^ 64) (n3 : (s.gpr .x3).toNat + p.sigLen ≤ 2 ^ 64)
    (n4 : (s.gpr .x4).toNat + VG.Proof.MlDsa.AArch64.Message.sScr p ≤ 2 ^ 64) :
    (signContract p AArch64.abi 16).pre s := by
  sig_pre [signContract, signSig, AArch64.abi, AArch64.argRegs, List.range, List.range.loop]
  exact ⟨sp, rd, wr, d03, d04, d13, d14, d23, d24, d34, k0, k1, k2, k3, k4, n0, n1, n2, n3, n4⟩

/-- The arguments of the call of the signing function on `μ`. -/
abbrev signArgs : List (Reg × Arg) := [(.x0, .slot fKey), (.x1, .off oMU), (.x2, .slot fRnd), (.x3, .slot fSig),
  (.x4, .slot fScr)]

section
variable {p : Params} {s : State}

theorem gpr_ce (t : State) {r : Reg} {rd wr : List Region} (h : r ∉ linkRegs := by decide) :
    (t.callEntry.withRegions rd wr).gpr r = t.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ h]

/-- The working space of the signing function on `μ`: the start of `scratch`. -/
theorem sScr_sub (p : Params) (s : State) :
    Region.Sub ⟨s.gpr .x7, VG.Proof.MlDsa.AArch64.Message.sScr p⟩ ⟨s.gpr .x7, VG.Proof.MlDsa.AArch64.Message.mScrLen p⟩ :=
  Region.sub_prefix (by rw [VG.Proof.MlDsa.AArch64.Message.mScr_eq]; simp only [VG.Proof.MlDsa.AArch64.Message.sScr, oE]; omega)

/-- The saves are apart from it. -/
theorem sv_sScr {p : Params} (hp : p ∈ VG.Proof.MlDsa.AArch64.Message.params) (s : State) {d n : Nat} (hd : d + n ≤ 88) :
    Region.Disjoint ⟨(VG.Proof.MlDsa.AArch64.Message.slay p s).X + BitVec.ofNat 64 904 + BitVec.ofNat 64 d, n⟩ ⟨s.gpr .x7, VG.Proof.MlDsa.AArch64.Message.sScr p⟩ := by
  show Region.Disjoint ⟨s.gpr .x7 + BitVec.ofNat 64 (oE p) + BitVec.ofNat 64 904 + BitVec.ofNat 64 d, n⟩ _
  rw [add_add, add_add]
  have := VG.Proof.MlDsa.AArch64.Message.oE_lt hp
  exact Offset.disjoint_base _ (by simp only [VG.Proof.MlDsa.AArch64.Message.sScr, oE]; omega) (by omega)

theorem mu_sScr {p : Params} (hp : p ∈ VG.Proof.MlDsa.AArch64.Message.params) (s : State) :
    Region.Disjoint ⟨(VG.Proof.MlDsa.AArch64.Message.slay p s).MU, 64⟩ ⟨s.gpr .x7, VG.Proof.MlDsa.AArch64.Message.sScr p⟩ := by
  show Region.Disjoint ⟨s.gpr .x7 + BitVec.ofNat 64 (oE p) + BitVec.ofNat 64 840, 64⟩ _
  rw [add_add]
  have := VG.Proof.MlDsa.AArch64.Message.oE_lt hp
  exact Offset.disjoint_base _ (by simp only [VG.Proof.MlDsa.AArch64.Message.sScr, oE]; omega) (by omega)

theorem mu_within (p : Params) (s : State) : Within ⟨(VG.Proof.MlDsa.AArch64.Message.slay p s).MU, 64⟩ ⟨s.gpr .x7, VG.Proof.MlDsa.AArch64.Message.mScrLen p⟩ :=
  (within_off (VG.Proof.MlDsa.AArch64.Message.slay p s).X (d := 840) (n := 64) (k := 1024) (by omega)).trans (VG.Proof.MlDsa.AArch64.Message.slay_X p s)

theorem mu_nowrap {L : VG.Proof.MlDsa.AArch64.Message.Lay} (hL : L.Ok) : L.MU.toNat + 64 ≤ 2 ^ 64 := by
  have := hL.nX
  show (L.X + BitVec.ofNat 64 840).toNat + 64 ≤ 2 ^ 64
  rw [toNat_add_ofNat (by omega)]; omega

/-- The regions the signing function on `μ` reads and writes. -/
abbrev signRd (p : Params) (s : State) : List Region :=
  [⟨s.gpr .x0, p.skLen⟩, ⟨(VG.Proof.MlDsa.AArch64.Message.slay p s).MU, 64⟩, ⟨s.gpr .x5, 32⟩]
abbrev signWr (p : Params) (s : State) : List Region := [⟨s.gpr .x6, p.sigLen⟩, ⟨s.gpr .x7, VG.Proof.MlDsa.AArch64.Message.sScr p⟩]

/-- The registers after the moves of the arguments. -/
theorem signRegs_of {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t t1 : State}
    (hc : VG.Proof.MlDsa.AArch64.Message.Ctx (VG.Proof.MlDsa.AArch64.Message.slay p s) g vv m₀ t) (hm : (∀ da ∈ VG.Proof.MlDsa.AArch64.Message.signArgs, t1.gpr da.1 = da.2.val t)) :
    t1.gpr .x0 = s.gpr .x0 ∧ t1.gpr .x1 = (VG.Proof.MlDsa.AArch64.Message.slay p s).MU ∧ t1.gpr .x2 = s.gpr .x5 ∧ t1.gpr .x3 = s.gpr .x6 ∧
      t1.gpr .x4 = s.gpr .x7 := by
  have e0 := hm (.x0, .slot fKey) (by simp)
  have e1 := hm (.x1, .off oMU) (by simp)
  have e2 := hm (.x2, .slot fRnd) (by simp)
  have e3 := hm (.x3, .slot fSig) (by simp)
  have e4 := hm (.x4, .slot fScr) (by simp)
  rw [hc.slotV (f := fKey) (j := 0) rfl (by omega)] at e0
  rw [hc.off] at e1
  rw [hc.slotV (f := fRnd) (j := 5) rfl (by omega)] at e2
  rw [hc.slotV (f := fSig) (j := 6) rfl (by omega)] at e3
  rw [hc.slotV (f := fScr) (j := 7) rfl (by omega)] at e4
  simp only [Lay.vals, VG.Proof.MlDsa.AArch64.Message.slay, List.getD_cons_zero, List.getD_cons_succ] at e0 e2 e3 e4
  exact ⟨e0, e1, e2, e3, e4⟩

/-- The precondition of the signing function on `μ`, on entry to it. -/
theorem signK_pre (hp : p ∈ VG.Proof.MlDsa.AArch64.Message.params) (h : VG.Proof.MlDsa.AArch64.Message.SPre p s) (h8 : (s.gpr .x4).toNat < 256) {g : Reg → BitVec 64}
    {vv : VReg → BitVec 128} {m₀ : Mem} {t t1 : State} (hc : VG.Proof.MlDsa.AArch64.Message.Ctx (VG.Proof.MlDsa.AArch64.Message.slay p s) g vv m₀ t)
    (hA : ∀ da ∈ VG.Proof.MlDsa.AArch64.Message.signArgs, t1.gpr da.1 = da.2.val t) (hsp1 : t1.sp = s.sp) :
    (signContract p AArch64.abi 16).pre (t1.callEntry.withRegions (VG.Proof.MlDsa.AArch64.Message.signRd p s) (VG.Proof.MlDsa.AArch64.Message.signWr p s)) := by
  have hL := VG.Proof.MlDsa.AArch64.Message.slay_ok hp h h8
  obtain ⟨e0, e1, e2, e3, e4⟩ := VG.Proof.MlDsa.AArch64.Message.signRegs_of hc hA
  have hmu := (VG.Proof.MlDsa.AArch64.Message.mu_within p s).sub
  have hsub := VG.Proof.MlDsa.AArch64.Message.sScr_sub p s
  have hstk : ∀ {rd wr : List Region} {r : Region}, (VG.Proof.MlDsa.AArch64.Message.rStk s).Disjoint r →
      (VG.Proof.MlDsa.AArch64.Message.rStk (t1.callEntry.withRegions rd wr)).Disjoint r := by
    intro rd wr r hr; simpa [VG.Proof.MlDsa.AArch64.Message.rStk, hsp1] using hr
  refine VG.Proof.MlDsa.AArch64.Message.signC_pre ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    try simp only [VG.Proof.MlDsa.AArch64.Message.gpr_ce t1 (r := .x0), VG.Proof.MlDsa.AArch64.Message.gpr_ce t1 (r := .x1), VG.Proof.MlDsa.AArch64.Message.gpr_ce t1 (r := .x2), VG.Proof.MlDsa.AArch64.Message.gpr_ce t1 (r := .x3),
      VG.Proof.MlDsa.AArch64.Message.gpr_ce t1 (r := .x4), e0, e1, e2, e3, e4, State.withRegions_rd, State.withRegions_wr]
  · simp only [State.withRegions_sp, State.callEntry_sp, hsp1]; exact h.sp
  · exact h.skSig
  · exact h.skScr.sub_right hsub
  · exact h.sigScr.symm.sub_left hmu
  · exact VG.Proof.MlDsa.AArch64.Message.mu_sScr hp s
  · exact h.rndSig
  · exact h.rndScr.sub_right hsub
  · exact h.sigScr.sub_right hsub
  · exact hstk h.stkSk
  · have km := VG.Proof.MlDsa.AArch64.Message.k_mu hL
    exact hstk km
  · exact hstk h.stkRnd
  · exact hstk h.stkSig
  · exact hstk (h.stkScr.sub_right hsub)
  · exact h.nSk
  · exact VG.Proof.MlDsa.AArch64.Message.mu_nowrap hL
  · exact h.nRnd
  · exact h.nSig
  · have := h.nScr; simp only [VG.Proof.MlDsa.AArch64.Message.mScrLen, VG.Proof.MlDsa.AArch64.Message.sScr, messageScratchWords] at this ⊢; omega

/-- The call of the signing function on `μ`. -/
theorem signCall_ok {n : String} {c : Prog isa} (hS : VG.Proof.MlDsa.AArch64.Message.SignFn p c) (hp : p ∈ VG.Proof.MlDsa.AArch64.Message.params) (h : VG.Proof.MlDsa.AArch64.Message.SPre p s)
    (h8 : (s.gpr .x4).toNat < 256) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (hc : VG.Proof.MlDsa.AArch64.Message.Ctx (VG.Proof.MlDsa.AArch64.Message.slay p s) g vv m₀ t) :
    WP isa (callA n c VG.Proof.MlDsa.AArch64.Message.signArgs) t fun s' => VG.Proof.MlDsa.AArch64.Message.Fin (VG.Proof.MlDsa.AArch64.Message.slay p s) g vv s' ∧
      Outcome (fun b => signMu p b (bytesAt t.mem (s.gpr .x0) p.skLen) (bytesAt t.mem (VG.Proof.MlDsa.AArch64.Message.slay p s).MU 64)
          (bytesAt t.mem (s.gpr .x5) 32)) ((s'.gpr .x0).setWidth 32) (bytesAt s'.mem (s.gpr .x6) p.sigLen) := by
  have hL := VG.Proof.MlDsa.AArch64.Message.slay_ok hp h h8
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Message.setArgs_ok VG.Proof.MlDsa.AArch64.Message.signArgs (by decide) t (hc.xOk hL)) fun t1 ⟨hA, o⟩ => ?_)
  have hc1 : VG.Proof.MlDsa.AArch64.Message.Ctx (VG.Proof.MlDsa.AArch64.Message.slay p s) g vv m₀ t1 :=
    hc.regs o.rd o.wr o.sp o.mem o.vcs fun r hr _ => o.gpr r (by simp only [List.map_cons, List.map_nil]; exact VG.Proof.MlDsa.AArch64.Message.not_pres hr _)
  obtain ⟨e0, e1, e2, e3, _⟩ := VG.Proof.MlDsa.AArch64.Message.signRegs_of hc hA
  have hsp1 : t1.sp = s.sp := hc1.sp
  have hd := hS.dle.1
  have hpre := VG.Proof.MlDsa.AArch64.Message.signK_pre hp h h8 hc hA hsp1
  refine WP.callFV hS.ver.1 hpre ?_ ?_ (fun s' hrd hwr hsp hf hcs hvs hpost => ?_) (by omega)
  · rw [hc1.rd, hc1.wr]
    refine VG.Proof.MlDsa.AArch64.Message.covers_of_within fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by simp [VG.Proof.MlDsa.AArch64.Message.slay, h.rd], within_self _⟩
    · exact ⟨_, by simp [VG.Proof.MlDsa.AArch64.Message.slay, h.wr], VG.Proof.MlDsa.AArch64.Message.mu_within p s⟩
    · exact ⟨_, by simp [VG.Proof.MlDsa.AArch64.Message.slay, h.rd], within_self _⟩
    · exact ⟨_, by simp [VG.Proof.MlDsa.AArch64.Message.slay, h.wr], within_self _⟩
    · exact ⟨⟨s.gpr .x7, VG.Proof.MlDsa.AArch64.Message.mScrLen p⟩, by simp [VG.Proof.MlDsa.AArch64.Message.slay, h.wr], within_base _ (by rw [VG.Proof.MlDsa.AArch64.Message.mScr_eq]; simp only [VG.Proof.MlDsa.AArch64.Message.sScr, oE]; omega)⟩
  · rw [hc1.wr]
    refine VG.Proof.MlDsa.AArch64.Message.covers_of_within fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by simp [VG.Proof.MlDsa.AArch64.Message.slay, h.wr], within_self _⟩
    · exact ⟨⟨s.gpr .x7, VG.Proof.MlDsa.AArch64.Message.mScrLen p⟩, by simp [VG.Proof.MlDsa.AArch64.Message.slay, h.wr], within_base _ (by rw [VG.Proof.MlDsa.AArch64.Message.mScr_eq]; simp only [VG.Proof.MlDsa.AArch64.Message.sScr, oE]; omega)⟩
  -- After the call.
  have hsv : ∀ d, d + 8 ≤ 88 → s'.mem.readW ((VG.Proof.MlDsa.AArch64.Message.slay p s).X + BitVec.ofNat 64 904 + BitVec.ofNat 64 d) 64 =
      t1.mem.readW ((VG.Proof.MlDsa.AArch64.Message.slay p s).X + BitVec.ofNat 64 904 + BitVec.ofNat 64 d) 64 := fun d hd' =>
    hf.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [add_add]
        exact (h.sigScr.symm.sub_left ((within_off (VG.Proof.MlDsa.AArch64.Message.slay p s).X (d := 904 + d) (n := 8) (k := 1024)
          (by omega)).trans (VG.Proof.MlDsa.AArch64.Message.slay_X p s)).sub)
      · exact VG.Proof.MlDsa.AArch64.Message.sv_sScr hp s hd'
      · rw [hsp1]
        exact (hL.sv_disj (r := below s.sp (16 * c.aarch64Depth)) (.inr (below_sub (by omega) (by decide))) hd'))
      (by decide)
  refine ⟨⟨hrd.trans hc1.rd, hwr.trans hc1.wr, hsp.trans hc1.sp, (hcs .x28 (by decide) (by decide)).trans hc1.x28,
    fun r hr h28 h30 => (hcs r hr h30).trans (hc1.cs r hr h28 h30), fun r hr => (hvs r hr).trans (hc1.vs r hr),
    (hsv 0 (by omega)).trans hc1.s28, (hsv 8 (by omega)).trans hc1.s30⟩, ?_⟩
  sig_reduce [signContract, signSig, AArch64.abi, AArch64.argRegs, List.range, List.range.loop] at hpost
  simp only [e0, e1, e2, e3, o.mem] at hpost
  exact hpost

end

end VG.Proof.MlDsa.AArch64.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Message.SignCorrect`. -/
section

/-!
# ML-DSA on AArch64, `sign_message`: correctness

Untrusted: everything here is checked by Lean. From a state satisfying
`signMessageContract p AArch64.abi 16`, `signMessage v.callee n c p`
returns 2 if the context string is longer than 255 bytes; otherwise it
computes `μ` of the formatted message and calls the signing function on `μ`
`c`, which gives the signature of `ML-DSA.Sign_internal` on the formatted
message (`signMessage_wp`).
-/

namespace VG.Proof.MlDsa.AArch64.Message

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.AArch64 (Only wp_nil wp_lsr wp_movz eval_nonzero ne_zero_iff)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

theorem wp_ite_t {c : isa.Cond} {th el : Prog isa} {s : State} {Q : State → Prop}
    (hc : isa.eval c s = some true) (h : WP isa th s Q) : WP isa (.ite c th el) s Q :=
  let ⟨_, _, e, q⟩ := h; ⟨_, _, .iteT hc e, q⟩

theorem wp_ite_f {c : isa.Cond} {th el : Prog isa} {s : State} {Q : State → Prop}
    (hc : isa.eval c s = some false) (h : WP isa el s Q) : WP isa (.ite c th el) s Q :=
  let ⟨_, _, e, q⟩ := h; ⟨_, _, .iteF hc e, q⟩

/-- `x9 ← ctx_len >> 8`, and the branch on it. -/
theorem lsr_ok (s : State) :
    WP isa (.block [.lsr .x .x9 .x4 8]) s fun s1 => Only [.x9] s s1 ∧
      isa.eval (.nonzero .x .x9) s1 = some (decide ¬ (s.gpr .x4).toNat < 256) := by
  refine wp_lsr (by decide) fun s1 o1 e1 => wp_nil ⟨o1, ?_⟩
  rw [eval_nonzero, e1, ne_zero_iff, Proof.MlKem.AArch64.toNat_lsr]
  congr 1
  rw [decide_eq_decide]
  constructor <;> intro h <;> omega

theorem Ctx.slotOffV {L : VG.Proof.MlDsa.AArch64.Message.Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (hc : VG.Proof.MlDsa.AArch64.Message.Ctx L g vv m₀ t) (o : Nat) : (Arg.slotOff fKey o).val t = L.key + BitVec.ofNat 64 o := by
  have := hc.slotV (f := fKey) (j := 0) rfl (by omega)
  simp only [Arg.val] at this ⊢
  rw [this]; rfl

theorem signSaves_vals {p : Params} {s s1 : State} (o : Only [.x9] s s1) :
    ∀ j (hj : j < signSaves.length), s1.gpr (signSaves[j]'hj).1 = (VG.Proof.MlDsa.AArch64.Message.slay p s).vals.getD j 0 := by
  intro j hj
  have : j < 8 := hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [signSaves, Lay.vals, VG.Proof.MlDsa.AArch64.Message.slay, List.getElem_cons_zero, List.getElem_cons_succ, List.getD_cons_zero,
      List.getD_cons_succ] <;> exact o.get _

theorem signMessage_wp (v : Proof.Sha3.AArch64.Permutation) {p : Params} {n : String} {c : Prog isa}
    (hS : VG.Proof.MlDsa.AArch64.Message.SignFn p c) (hp : p ∈ VG.Proof.MlDsa.AArch64.Message.params) {s : State} (hpre : (signMessageContract p AArch64.abi 16).pre s) :
    WP isa (signMessage v.callee n c p) s fun s' =>
      abiPreserved s s' ∧ (signMessageContract p AArch64.abi 16).post s s' := by
  have h := VG.Proof.MlDsa.AArch64.Message.sPre_of hpre
  unfold signMessage top
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Message.lsr_ok s) fun s1 ⟨o1, hc1⟩ => ?_)
  by_cases h8 : (s.gpr .x4).toNat < 256
  · rw [decide_eq_false (by simpa using h8)] at hc1
    have hL := VG.Proof.MlDsa.AArch64.Message.slay_ok hp h h8
    refine VG.Proof.MlDsa.AArch64.Message.wp_ite_f hc1 (WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Message.enter_ok hL rfl (by decide) rfl (o1.get .x7) (by rw [o1.sp]; rfl)
      (by rw [o1.rd]; rfl) (by rw [o1.wr]; rfl) (o1.get .x4) (VG.Proof.MlDsa.AArch64.Message.signSaves_vals o1) (by decide))
      fun t hc => ?_))
    have hsk := (VG.Proof.MlDsa.AArch64.Message.skLen_ge hp).1
    have wtr : Within ⟨(VG.Proof.MlDsa.AArch64.Message.slay p s).key + BitVec.ofNat 64 64, 64⟩ (VG.Proof.MlDsa.AArch64.Message.slay p s).KEY :=
      within_off _ (show 64 + 64 ≤ p.skLen by omega)
    have hst : Region.Sub ⟨(VG.Proof.MlDsa.AArch64.Message.slay p s).ST, 200⟩ (VG.Proof.MlDsa.AArch64.Message.slay p s).XS := by
      have := Offset.sub_base (VG.Proof.MlDsa.AArch64.Message.slay p s).X (d := 0) (n := 200) (k := 1024) (by omega)
      simpa only [VG.Proof.MlDsa.AArch64.Message.x0] using this
    refine WP.seq (WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Message.muHash_ok v hL hc (tr := .slotOff fKey 64) (by decide) rfl
      (fun t' hc' => hc'.slotOffV 64) ⟨_, List.mem_append_left _ hL.inKey, wtr⟩
      ((hL.xKey.symm.sub_left wtr.sub).sub_right hst)
      ((hL.xKey.symm.sub_left wtr.sub).sub_right (Offset.sub_base _ (by omega : 200 + 640 ≤ 1024)))
      (hL.kKey.sub_right wtr.sub)) fun t₁ ⟨hc₁, hμ⟩ => ?_))
    refine WP.mono (VG.Proof.MlDsa.AArch64.Message.signCall_ok hS hp h h8 hc₁) fun s' ⟨hf, hq⟩ => ?_
    refine WP.mono (VG.Proof.MlDsa.AArch64.Message.leave_ok hL hf) fun s'' ⟨hcs, hsp, hvs, hm, hx0, _, _⟩ => ?_
    refine ⟨⟨fun r hr => by rw [hcs r hr]; exact o1.get r (fun e => by
        simp only [List.mem_singleton] at e; subst e; revert hr; decide), hsp,
      fun r hr => (hvs r hr).trans (o1.vcs r hr)⟩, ?_⟩
    sig_post [signMessageContract, signMessageSig, AArch64.abi, AArch64.argRegs, List.range, List.range.loop]
    rw [formatMessage_some (by rw [Proof.MlKem.bytesAt_length]; exact h8)]
    simp only [signInternal, messageRep, skTr]
    have hm₀ : s1.mem = s.mem := o1.mem
    have ek : bytesAt t₁.mem (s.gpr .x0) p.skLen = bytesAt s.mem (s.gpr .x0) p.skLen :=
      (hc₁.bytesAt_eq (p := (VG.Proof.MlDsa.AArch64.Message.slay p s).key) (n := p.skLen) hL.xKey hL.kKey (by have := h.nSk; omega)).trans
        (by rw [hm₀]; rfl)
    have er : bytesAt t₁.mem (s.gpr .x5) 32 = bytesAt s.mem (s.gpr .x5) 32 :=
      (hc₁.bytesAt_eq (p := (VG.Proof.MlDsa.AArch64.Message.slay p s).rnd) (n := 32) (h.rndScr.symm.sub_left (VG.Proof.MlDsa.AArch64.Message.slay_X p s).sub) h.stkRnd
        (by decide)).trans (by rw [hm₀]; rfl)
    have etr : bytesAt t.mem ((VG.Proof.MlDsa.AArch64.Message.slay p s).key + BitVec.ofNat 64 64) 64 =
        ((bytesAt s.mem (s.gpr .x0) p.skLen).drop 64).take 64 := by
      rw [hc.bytesAt_eq (hL.xKey.sub_right wtr.sub) (hL.kKey.sub_right wtr.sub) (by decide), hm₀,
        Proof.MlKem.bytesAt_slice _ _ (by omega)]
      rfl
    rw [ek, er, hμ, etr, hm₀] at hq
    rw [hx0, hm]
    simp only [VG.Proof.MlDsa.AArch64.Message.hdrBytes, Proof.MlKem.bytesAt_length, List.append_assoc] at hq ⊢
    exact hq
  · rw [decide_eq_true (by simpa using h8)] at hc1
    refine VG.Proof.MlDsa.AArch64.Message.wp_ite_t hc1 (wp_movz fun s2 o2 e2 => wp_nil ⟨⟨fun r hr => ?_, by rw [o2.sp, o1.sp],
      fun r hr => by rw [o2.vcs r hr, o1.vcs r hr]⟩, ?_⟩)
    · have h0 : r ∉ [Reg.x0] := fun e => by simp only [List.mem_singleton] at e; subst e; revert hr; decide
      have h9 : r ∉ [Reg.x9] := fun e => by simp only [List.mem_singleton] at e; subst e; revert hr; decide
      rw [o2.get r h0, o1.get r h9]
    · sig_post [signMessageContract, signMessageSig, AArch64.abi, AArch64.argRegs, List.range, List.range.loop]
      rw [formatMessage_none (by rw [Proof.MlKem.bytesAt_length]; omega), e2]
      rfl

end VG.Proof.MlDsa.AArch64.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Message.VerifyCall`. -/
section

/-!
# ML-DSA on AArch64, `verify_message`: the call of the verification function on `μ`

Untrusted: everything here is checked by Lean. Any code verified against
`verifyContract p AArch64.abi 16` whose frames nest at most once
(`VerifyFn`): its call on `pk`, `μ` at `X + 840`, `sig` and the first
`scratchWords p` words of `scratch` (`verifyCall_ok`), after which the saves
are intact (`Fin`).
-/

namespace VG.Proof.MlDsa.AArch64.Message

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.AArch64 (Only)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- A verification function on `μ` that `verify_message` can call. -/
structure VerifyFn (p : Params) (c : Prog isa) : Prop where
  ver : Verified AArch64.target c (verifyContract p AArch64.abi 16)
  dle : VG.Proof.MlDsa.AArch64.Message.DLe 1 c

/-- The precondition of `verifyContract p AArch64.abi 16`, from its facts. -/
theorem verifyC_pre {p : Params} {s : State} (sp : 16 ≤ s.sp.toNat)
    (rd : s.rd = [⟨s.gpr .x0, p.pkLen⟩, ⟨s.gpr .x1, 64⟩, ⟨s.gpr .x2, p.sigLen⟩])
    (wr : s.wr = [⟨s.gpr .x3, VG.Proof.MlDsa.AArch64.Message.sScr p⟩])
    (d03 : Region.Disjoint ⟨s.gpr .x0, p.pkLen⟩ ⟨s.gpr .x3, VG.Proof.MlDsa.AArch64.Message.sScr p⟩)
    (d13 : Region.Disjoint ⟨s.gpr .x1, 64⟩ ⟨s.gpr .x3, VG.Proof.MlDsa.AArch64.Message.sScr p⟩)
    (d23 : Region.Disjoint ⟨s.gpr .x2, p.sigLen⟩ ⟨s.gpr .x3, VG.Proof.MlDsa.AArch64.Message.sScr p⟩)
    (k0 : (VG.Proof.MlDsa.AArch64.Message.rStk s).Disjoint ⟨s.gpr .x0, p.pkLen⟩) (k1 : (VG.Proof.MlDsa.AArch64.Message.rStk s).Disjoint ⟨s.gpr .x1, 64⟩)
    (k2 : (VG.Proof.MlDsa.AArch64.Message.rStk s).Disjoint ⟨s.gpr .x2, p.sigLen⟩) (k3 : (VG.Proof.MlDsa.AArch64.Message.rStk s).Disjoint ⟨s.gpr .x3, VG.Proof.MlDsa.AArch64.Message.sScr p⟩)
    (n0 : (s.gpr .x0).toNat + p.pkLen ≤ 2 ^ 64) (n1 : (s.gpr .x1).toNat + 64 ≤ 2 ^ 64)
    (n2 : (s.gpr .x2).toNat + p.sigLen ≤ 2 ^ 64) (n3 : (s.gpr .x3).toNat + VG.Proof.MlDsa.AArch64.Message.sScr p ≤ 2 ^ 64) :
    (verifyContract p AArch64.abi 16).pre s := by
  sig_pre [verifyContract, verifySig, AArch64.abi, AArch64.argRegs, List.range, List.range.loop]
  exact ⟨sp, rd, wr, d03, d13, d23, k0, k1, k2, k3, n0, n1, n2, n3⟩

/-- The arguments of the call of the verification function on `μ`. -/
abbrev verifyArgs : List (Reg × Arg) := [(.x0, .slot fKey), (.x1, .off oMU), (.x2, .slot fSig), (.x3, .slot fScr)]

section
variable {p : Params} {s : State}

theorem sScrV_sub (p : Params) (s : State) :
    Region.Sub ⟨s.gpr .x6, VG.Proof.MlDsa.AArch64.Message.sScr p⟩ ⟨s.gpr .x6, VG.Proof.MlDsa.AArch64.Message.mScrLen p⟩ :=
  Region.sub_prefix (by rw [VG.Proof.MlDsa.AArch64.Message.mScr_eq]; simp only [VG.Proof.MlDsa.AArch64.Message.sScr, oE]; omega)

theorem sv_sScrV {p : Params} (hp : p ∈ VG.Proof.MlDsa.AArch64.Message.params) (s : State) {d n : Nat} (hd : d + n ≤ 88) :
    Region.Disjoint ⟨(VG.Proof.MlDsa.AArch64.Message.vlay p s).X + BitVec.ofNat 64 904 + BitVec.ofNat 64 d, n⟩ ⟨s.gpr .x6, VG.Proof.MlDsa.AArch64.Message.sScr p⟩ := by
  show Region.Disjoint ⟨s.gpr .x6 + BitVec.ofNat 64 (oE p) + BitVec.ofNat 64 904 + BitVec.ofNat 64 d, n⟩ _
  rw [add_add, add_add]
  have := VG.Proof.MlDsa.AArch64.Message.oE_lt hp
  exact Offset.disjoint_base _ (by simp only [VG.Proof.MlDsa.AArch64.Message.sScr, oE]; omega) (by omega)

theorem mu_sScrV {p : Params} (hp : p ∈ VG.Proof.MlDsa.AArch64.Message.params) (s : State) :
    Region.Disjoint ⟨(VG.Proof.MlDsa.AArch64.Message.vlay p s).MU, 64⟩ ⟨s.gpr .x6, VG.Proof.MlDsa.AArch64.Message.sScr p⟩ := by
  show Region.Disjoint ⟨s.gpr .x6 + BitVec.ofNat 64 (oE p) + BitVec.ofNat 64 840, 64⟩ _
  rw [add_add]
  have := VG.Proof.MlDsa.AArch64.Message.oE_lt hp
  exact Offset.disjoint_base _ (by simp only [VG.Proof.MlDsa.AArch64.Message.sScr, oE]; omega) (by omega)

theorem mu_withinV (p : Params) (s : State) : Within ⟨(VG.Proof.MlDsa.AArch64.Message.vlay p s).MU, 64⟩ ⟨s.gpr .x6, VG.Proof.MlDsa.AArch64.Message.mScrLen p⟩ :=
  (within_off (VG.Proof.MlDsa.AArch64.Message.vlay p s).X (d := 840) (n := 64) (k := 1024) (by omega)).trans (VG.Proof.MlDsa.AArch64.Message.vlay_X p s)

/-- The regions the verification function on `μ` reads and writes. -/
abbrev verifyRd (p : Params) (s : State) : List Region :=
  [⟨s.gpr .x0, p.pkLen⟩, ⟨(VG.Proof.MlDsa.AArch64.Message.vlay p s).MU, 64⟩, ⟨s.gpr .x5, p.sigLen⟩]
abbrev verifyWr (p : Params) (s : State) : List Region := [⟨s.gpr .x6, VG.Proof.MlDsa.AArch64.Message.sScr p⟩]

/-- The registers after the moves of the arguments. -/
theorem verifyRegs_of {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t t1 : State}
    (hc : VG.Proof.MlDsa.AArch64.Message.Ctx (VG.Proof.MlDsa.AArch64.Message.vlay p s) g vv m₀ t) (hm : (∀ da ∈ VG.Proof.MlDsa.AArch64.Message.verifyArgs, t1.gpr da.1 = da.2.val t)) :
    t1.gpr .x0 = s.gpr .x0 ∧ t1.gpr .x1 = (VG.Proof.MlDsa.AArch64.Message.vlay p s).MU ∧ t1.gpr .x2 = s.gpr .x5 ∧ t1.gpr .x3 = s.gpr .x6 := by
  have e0 := hm (.x0, .slot fKey) (by simp)
  have e1 := hm (.x1, .off oMU) (by simp)
  have e2 := hm (.x2, .slot fSig) (by simp)
  have e3 := hm (.x3, .slot fScr) (by simp)
  rw [hc.slotV (f := fKey) (j := 0) rfl (by omega)] at e0
  rw [hc.off] at e1
  rw [hc.slotV (f := fSig) (j := 6) rfl (by omega)] at e2
  rw [hc.slotV (f := fScr) (j := 7) rfl (by omega)] at e3
  simp only [Lay.vals, VG.Proof.MlDsa.AArch64.Message.vlay, List.getD_cons_zero, List.getD_cons_succ] at e0 e2 e3
  exact ⟨e0, e1, e2, e3⟩

/-- The precondition of the verification function on `μ`, on entry to it. -/
theorem verifyK_pre (hp : p ∈ VG.Proof.MlDsa.AArch64.Message.params) (h : VG.Proof.MlDsa.AArch64.Message.VPre p s) (h8 : (s.gpr .x4).toNat < 256) {g : Reg → BitVec 64}
    {vv : VReg → BitVec 128} {m₀ : Mem} {t t1 : State} (hc : VG.Proof.MlDsa.AArch64.Message.Ctx (VG.Proof.MlDsa.AArch64.Message.vlay p s) g vv m₀ t)
    (hA : ∀ da ∈ VG.Proof.MlDsa.AArch64.Message.verifyArgs, t1.gpr da.1 = da.2.val t) (hsp1 : t1.sp = s.sp) :
    (verifyContract p AArch64.abi 16).pre (t1.callEntry.withRegions (VG.Proof.MlDsa.AArch64.Message.verifyRd p s) (VG.Proof.MlDsa.AArch64.Message.verifyWr p s)) := by
  have hL := VG.Proof.MlDsa.AArch64.Message.vlay_ok hp h h8
  obtain ⟨e0, e1, e2, e3⟩ := VG.Proof.MlDsa.AArch64.Message.verifyRegs_of hc hA
  have hsub := VG.Proof.MlDsa.AArch64.Message.sScrV_sub p s
  have hstk : ∀ {rd wr : List Region} {r : Region}, (VG.Proof.MlDsa.AArch64.Message.rStk s).Disjoint r →
      (VG.Proof.MlDsa.AArch64.Message.rStk (t1.callEntry.withRegions rd wr)).Disjoint r := by
    intro rd wr r hr; simpa [VG.Proof.MlDsa.AArch64.Message.rStk, hsp1] using hr
  refine VG.Proof.MlDsa.AArch64.Message.verifyC_pre ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    try simp only [VG.Proof.MlDsa.AArch64.Message.gpr_ce t1 (r := .x0), VG.Proof.MlDsa.AArch64.Message.gpr_ce t1 (r := .x1), VG.Proof.MlDsa.AArch64.Message.gpr_ce t1 (r := .x2), VG.Proof.MlDsa.AArch64.Message.gpr_ce t1 (r := .x3),
      e0, e1, e2, e3, State.withRegions_rd, State.withRegions_wr]
  · simp only [State.withRegions_sp, State.callEntry_sp, hsp1]; exact h.sp
  · exact h.pkScr.sub_right hsub
  · exact VG.Proof.MlDsa.AArch64.Message.mu_sScrV hp s
  · exact h.sigScr.sub_right hsub
  · exact hstk h.stkPk
  · have km := VG.Proof.MlDsa.AArch64.Message.k_mu hL
    exact hstk km
  · exact hstk h.stkSig
  · exact hstk (h.stkScr.sub_right hsub)
  · exact h.nPk
  · exact VG.Proof.MlDsa.AArch64.Message.mu_nowrap hL
  · exact h.nSig
  · have := h.nScr; simp only [VG.Proof.MlDsa.AArch64.Message.mScrLen, VG.Proof.MlDsa.AArch64.Message.sScr, messageScratchWords] at this ⊢; omega

/-- The call of the verification function on `μ`. -/
theorem verifyCall_ok {n : String} {c : Prog isa} (hV : VG.Proof.MlDsa.AArch64.Message.VerifyFn p c) (hp : p ∈ VG.Proof.MlDsa.AArch64.Message.params) (h : VG.Proof.MlDsa.AArch64.Message.VPre p s)
    (h8 : (s.gpr .x4).toNat < 256) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (hc : VG.Proof.MlDsa.AArch64.Message.Ctx (VG.Proof.MlDsa.AArch64.Message.vlay p s) g vv m₀ t) :
    WP isa (callA n c VG.Proof.MlDsa.AArch64.Message.verifyArgs) t fun s' => VG.Proof.MlDsa.AArch64.Message.Fin (VG.Proof.MlDsa.AArch64.Message.vlay p s) g vv s' ∧
      (let w := fun b => verifyMu p b (bytesAt t.mem (s.gpr .x0) p.pkLen) (bytesAt t.mem (VG.Proof.MlDsa.AArch64.Message.vlay p s).MU 64)
          (bytesAt t.mem (s.gpr .x5) p.sigLen);
        ((s'.gpr .x0).setWidth 32 = 1 ∧ ∃ b, w b = some true) ∨
          ((s'.gpr .x0).setWidth 32 = 0 ∧ w minBounds ≠ some true)) := by
  have hL := VG.Proof.MlDsa.AArch64.Message.vlay_ok hp h h8
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Message.setArgs_ok VG.Proof.MlDsa.AArch64.Message.verifyArgs (by decide) t (hc.xOk hL)) fun t1 ⟨hA, o⟩ => ?_)
  have hc1 : VG.Proof.MlDsa.AArch64.Message.Ctx (VG.Proof.MlDsa.AArch64.Message.vlay p s) g vv m₀ t1 :=
    hc.regs o.rd o.wr o.sp o.mem o.vcs fun r hr _ => o.gpr r (by simp only [List.map_cons, List.map_nil]; exact VG.Proof.MlDsa.AArch64.Message.not_pres hr _)
  obtain ⟨e0, e1, e2, _⟩ := VG.Proof.MlDsa.AArch64.Message.verifyRegs_of hc hA
  have hsp1 : t1.sp = s.sp := hc1.sp
  have hd := hV.dle.1
  have hpre := VG.Proof.MlDsa.AArch64.Message.verifyK_pre hp h h8 hc hA hsp1
  refine WP.callFV hV.ver.1 hpre ?_ ?_ (fun s' hrd hwr hsp hf hcs hvs hpost => ?_) (by omega)
  · rw [hc1.rd, hc1.wr]
    refine VG.Proof.MlDsa.AArch64.Message.covers_of_within fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp [VG.Proof.MlDsa.AArch64.Message.vlay, h.rd], within_self _⟩
    · exact ⟨_, by simp [VG.Proof.MlDsa.AArch64.Message.vlay, h.wr], VG.Proof.MlDsa.AArch64.Message.mu_withinV p s⟩
    · exact ⟨_, by simp [VG.Proof.MlDsa.AArch64.Message.vlay, h.rd], within_self _⟩
    · exact ⟨⟨s.gpr .x6, VG.Proof.MlDsa.AArch64.Message.mScrLen p⟩, by simp [VG.Proof.MlDsa.AArch64.Message.vlay, h.wr], within_base _ (by rw [VG.Proof.MlDsa.AArch64.Message.mScr_eq]; simp only [VG.Proof.MlDsa.AArch64.Message.sScr, oE]; omega)⟩
  · rw [hc1.wr]
    refine VG.Proof.MlDsa.AArch64.Message.covers_of_within fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact ⟨⟨s.gpr .x6, VG.Proof.MlDsa.AArch64.Message.mScrLen p⟩, by simp [VG.Proof.MlDsa.AArch64.Message.vlay, h.wr], within_base _ (by rw [VG.Proof.MlDsa.AArch64.Message.mScr_eq]; simp only [VG.Proof.MlDsa.AArch64.Message.sScr, oE]; omega)⟩
  -- After the call.
  have hsv : ∀ d, d + 8 ≤ 88 → s'.mem.readW ((VG.Proof.MlDsa.AArch64.Message.vlay p s).X + BitVec.ofNat 64 904 + BitVec.ofNat 64 d) 64 =
      t1.mem.readW ((VG.Proof.MlDsa.AArch64.Message.vlay p s).X + BitVec.ofNat 64 904 + BitVec.ofNat 64 d) 64 := fun d hd' =>
    hf.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact VG.Proof.MlDsa.AArch64.Message.sv_sScrV hp s hd'
      · rw [hsp1]
        exact (hL.sv_disj (r := below s.sp (16 * c.aarch64Depth)) (.inr (below_sub (by omega) (by decide))) hd'))
      (by decide)
  refine ⟨⟨hrd.trans hc1.rd, hwr.trans hc1.wr, hsp.trans hc1.sp, (hcs .x28 (by decide) (by decide)).trans hc1.x28,
    fun r hr h28 h30 => (hcs r hr h30).trans (hc1.cs r hr h28 h30), fun r hr => (hvs r hr).trans (hc1.vs r hr),
    (hsv 0 (by omega)).trans hc1.s28, (hsv 8 (by omega)).trans hc1.s30⟩, ?_⟩
  sig_reduce [verifyContract, verifySig, AArch64.abi, AArch64.argRegs, List.range, List.range.loop] at hpost
  simp only [e0, e1, e2, o.mem] at hpost
  exact hpost

end

end VG.Proof.MlDsa.AArch64.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Message.VerifyCorrect`. -/
section

/-!
# ML-DSA on AArch64, `verify_message`: correctness

Untrusted: everything here is checked by Lean. From a state satisfying
`verifyMessageContract p AArch64.abi 16`, `verifyMessage v.callee n c p`
returns 2 if the context string is longer than 255 bytes; otherwise it
computes `tr = H(pk, 64)`, then `μ` of the formatted message, and calls the
verification function on `μ` `c`, which gives `ML-DSA.Verify_internal` of
the formatted message (`verifyMessage_wp`).
-/

namespace VG.Proof.MlDsa.AArch64.Message

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.AArch64 (Only wp_nil wp_movz)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

theorem verifySaves_vals {p : Params} {s s1 : State} (o : Only [.x9] s s1) :
    ∀ j (hj : j < verifySaves.length), s1.gpr (verifySaves[j]'hj).1 = (VG.Proof.MlDsa.AArch64.Message.vlay p s).vals.getD j 0 := by
  intro j hj
  have : j < 8 := hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [verifySaves, Lay.vals, VG.Proof.MlDsa.AArch64.Message.vlay, List.getElem_cons_zero, List.getElem_cons_succ, List.getD_cons_zero,
      List.getD_cons_succ] <;> exact o.get _

theorem verifyMessage_wp (v : Proof.Sha3.AArch64.Permutation) {p : Params} {n : String} {c : Prog isa}
    (hV : VG.Proof.MlDsa.AArch64.Message.VerifyFn p c) (hp : p ∈ VG.Proof.MlDsa.AArch64.Message.params) {s : State} (hpre : (verifyMessageContract p AArch64.abi 16).pre s) :
    WP isa (verifyMessage v.callee n c p) s fun s' =>
      abiPreserved s s' ∧ (verifyMessageContract p AArch64.abi 16).post s s' := by
  have h := VG.Proof.MlDsa.AArch64.Message.vPre_of hpre
  unfold verifyMessage top
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Message.lsr_ok s) fun s1 ⟨o1, hc1⟩ => ?_)
  by_cases h8 : (s.gpr .x4).toNat < 256
  · rw [decide_eq_false (by simpa using h8)] at hc1
    have hL := VG.Proof.MlDsa.AArch64.Message.vlay_ok hp h h8
    refine VG.Proof.MlDsa.AArch64.Message.wp_ite_f hc1 (WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Message.enter_ok hL rfl (by decide) rfl (o1.get .x6) (by rw [o1.sp]; rfl)
      (by rw [o1.rd]; rfl) (by rw [o1.wr]; rfl) (o1.get .x4) (VG.Proof.MlDsa.AArch64.Message.verifySaves_vals o1) (by decide))
      fun t hc => ?_))
    refine WP.seq (WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Message.trHash_ok v hL rfl hc) fun t₁ ⟨hc₁, htr⟩ => ?_))
    have hst : Region.Sub ⟨(VG.Proof.MlDsa.AArch64.Message.vlay p s).ST, 200⟩ (VG.Proof.MlDsa.AArch64.Message.vlay p s).XS := by
      have := Offset.sub_base (VG.Proof.MlDsa.AArch64.Message.vlay p s).X (d := 0) (n := 200) (k := 1024) (by omega)
      simpa only [VG.Proof.MlDsa.AArch64.Message.x0] using this
    obtain ⟨R, hR, hw⟩ := hL.covX (e := 840) (k := 64) (by omega)
    refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Message.muHash_ok v hL hc₁ (tr := .off oMU) (by decide) rfl (fun t' hc' => hc'.off oMU)
      ⟨R, by simp [hR], hw⟩ st_mu.symm VG.Proof.MlDsa.AArch64.Message.mu_ks (VG.Proof.MlDsa.AArch64.Message.k_mu hL)) fun t₂ ⟨hc₂, hμ⟩ => ?_)
    refine WP.mono (VG.Proof.MlDsa.AArch64.Message.verifyCall_ok hV hp h h8 hc₂) fun s' ⟨hf, hq⟩ => ?_
    refine WP.mono (VG.Proof.MlDsa.AArch64.Message.leave_ok hL hf) fun s'' ⟨hcs, hsp, hvs, hm, hx0, _, _⟩ => ?_
    refine ⟨⟨fun r hr => by rw [hcs r hr]; exact o1.get r (fun e => by
        simp only [List.mem_singleton] at e; subst e; revert hr; decide), hsp,
      fun r hr => (hvs r hr).trans (o1.vcs r hr)⟩, ?_⟩
    sig_post [verifyMessageContract, verifyMessageSig, AArch64.abi, AArch64.argRegs, List.range, List.range.loop]
    rw [formatMessage_some (by rw [Proof.MlKem.bytesAt_length]; exact h8)]
    simp only [verifyInternal, messageRep, pkTr]
    have hm₀ : s1.mem = s.mem := o1.mem
    have ek : bytesAt t₂.mem (s.gpr .x0) p.pkLen = bytesAt s.mem (s.gpr .x0) p.pkLen :=
      (hc₂.bytesAt_eq (p := (VG.Proof.MlDsa.AArch64.Message.vlay p s).key) (n := p.pkLen) hL.xKey hL.kKey (by have := h.nPk; omega)).trans
        (by rw [hm₀]; rfl)
    have es : bytesAt t₂.mem (s.gpr .x5) p.sigLen = bytesAt s.mem (s.gpr .x5) p.sigLen :=
      (hc₂.bytesAt_eq (p := (VG.Proof.MlDsa.AArch64.Message.vlay p s).sig) (n := p.sigLen) (h.sigScr.symm.sub_left (VG.Proof.MlDsa.AArch64.Message.vlay_X p s).sub) h.stkSig
        (by have := h.nSig; omega)).trans (by rw [hm₀]; rfl)
    have hμ' := hμ
    rw [show (VG.Proof.MlDsa.AArch64.Message.vlay p s).X + BitVec.ofNat 64 oMU = (VG.Proof.MlDsa.AArch64.Message.vlay p s).MU from rfl, htr, hm₀] at hμ'
    rw [ek, es, hμ'] at hq
    rw [hx0]
    simp only [VG.Proof.MlDsa.AArch64.Message.hdrBytes, Proof.MlKem.bytesAt_length, List.append_assoc] at hq ⊢
    exact hq
  · rw [decide_eq_true (by simpa using h8)] at hc1
    refine VG.Proof.MlDsa.AArch64.Message.wp_ite_t hc1 (wp_movz fun s2 o2 e2 => wp_nil ⟨⟨fun r hr => ?_, by rw [o2.sp, o1.sp],
      fun r hr => by rw [o2.vcs r hr, o1.vcs r hr]⟩, ?_⟩)
    · have h0 : r ∉ [Reg.x0] := fun e => by simp only [List.mem_singleton] at e; subst e; revert hr; decide
      have h9 : r ∉ [Reg.x9] := fun e => by simp only [List.mem_singleton] at e; subst e; revert hr; decide
      rw [o2.get r h0, o1.get r h9]
    · sig_post [verifyMessageContract, verifyMessageSig, AArch64.abi, AArch64.argRegs, List.range,
        List.range.loop]
      rw [formatMessage_none (by rw [Proof.MlKem.bytesAt_length]; omega), e2]
      rfl

end VG.Proof.MlDsa.AArch64.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Message.Rel`. -/
section

/-!
# ML-DSA on AArch64, `sign_message` and `verify_message`: two runs

Untrusted: everything here is checked by Lean. Blocks whose addresses are
functions of `x28` and the stack pointer, which they keep, leak the same in
runs that agree on those (`block_x28_tr`): the moves of a call's arguments
are such (`setArgs_xOnly`). Two runs with the same layout, each in `Ctx`
with inputs related by `I` (`Two`), and a call in them of verified code
whose public data agree (`call_tr`).
-/

namespace VG.Proof.MlDsa.AArch64.Message

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.AArch64 (Only)

/-! ## Blocks addressed from `x28` -/

/-- An instruction whose addresses are a function of `x28` and the stack
pointer, which it keeps. -/
def XOnly (i : Instr) : Prop :=
  (∀ s₁ s₂ : State, s₁.gpr .x28 = s₂.gpr .x28 → s₁.sp = s₂.sp → isa.addrs i s₁ = isa.addrs i s₂) ∧
    dstOf i ≠ some .x28

theorem execBlock_x28_tr : ∀ {is : List Instr}, (∀ i ∈ is, VG.Proof.MlDsa.AArch64.Message.XOnly i) →
    ∀ {s₁ s₂ s₁' s₂' : State} {t₁ t₂ : List Leak}, s₁.gpr .x28 = s₂.gpr .x28 → s₁.sp = s₂.sp →
      execBlock isa is s₁ = some (s₁', t₁) → execBlock isa is s₂ = some (s₂', t₂) → t₁ = t₂
  | [], _, _, _, _, _, _, _, _, _, e₁, e₂ => by
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e₁ e₂
    rw [← e₁.2, ← e₂.2]
  | i :: is, h, s₁, s₂, s₁', s₂', t₁, t₂, h28, hsp, e₁, e₂ => by
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
    have h28' : a₁.gpr .x28 = a₂.gpr .x28 := by rw [exec_gpr hi.2 ha₁, exec_gpr hi.2 ha₂, h28]
    have hsp' : a₁.sp = a₂.sp := by rw [exec_sp ha₁, exec_sp ha₂, hsp]
    have ht := VG.Proof.MlDsa.AArch64.Message.execBlock_x28_tr (fun j hj => h j (List.mem_cons_of_mem _ hj)) h28' hsp' eb₁ eb₂
    rw [show addrs i s₁ = addrs i s₂ from hi.1 _ _ h28 hsp, ht]

theorem block_x28_tr {is : List Instr} (h : ∀ i ∈ is, VG.Proof.MlDsa.AArch64.Message.XOnly i) {P : State → State → Prop}
    (hp : ∀ a b, P a b → a.gpr .x28 = b.gpr .x28 ∧ a.sp = b.sp) : RelCT isa P (.block is) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hP e₁ e₂
  rw [Exec.block_iff] at e₁ e₂
  exact ⟨VG.Proof.MlDsa.AArch64.Message.execBlock_x28_tr h (hp _ _ hP).1 (hp _ _ hP).2 e₁ e₂, trivial⟩

theorem arg_xOnly (d : Reg) (hd : d ≠ .x28) (a : Arg) : ∀ i ∈ a.mov d, VG.Proof.MlDsa.AArch64.Message.XOnly i := by
  intro i hi
  cases a <;> simp only [Arg.mov, List.mem_cons, List.not_mem_nil, or_false] at hi <;>
    rcases hi with rfl | rfl <;>
    exact ⟨fun s₁ s₂ h _ => by simp [addrs, h], by simpa [dstOf] using hd⟩

theorem setArgs_xOnly {as : List (Reg × Arg)} (h : VG.Proof.MlDsa.AArch64.Message.argsOk as = true) : ∀ i ∈ setArgs as, VG.Proof.MlDsa.AArch64.Message.XOnly i := by
  induction as with
  | nil => intro i hi; simp [setArgs] at hi
  | cons da as ih =>
    obtain ⟨d, a⟩ := da
    simp only [VG.Proof.MlDsa.AArch64.Message.argsOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    intro i hi
    simp only [setArgs, List.flatMap_cons, List.mem_append] at hi
    rcases hi with hi | hi
    · exact VG.Proof.MlDsa.AArch64.Message.arg_xOnly d h.1.1.2 a i hi
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
    (hct : RelCT isa (VG.Proof.MlDsa.AArch64.Message.Ghost P A) c fun _ _ => True)
    (hw : ∀ x y a b, P x y → A x a → A y b → WP isa c a (B x) ∧ WP isa c b (B y)) :
    RelCT isa (VG.Proof.MlDsa.AArch64.Message.Ghost P A) c (VG.Proof.MlDsa.AArch64.Message.Ghost P B) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨x, y, hxy, a₁, a₂⟩ := hp
  obtain ⟨⟨_, u₁, x₁, y₁⟩, ⟨_, u₂, x₂, y₂⟩⟩ := hw x y s₁ s₂ hxy a₁ a₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, x, y, hxy, y₁, y₂⟩

/-! ## Two runs -/

/-- Two runs with the layout `L`, inputs related by `I`, each satisfying `Φ`. -/
def Two (I : VG.Proof.MlDsa.AArch64.Message.Lay → Mem → Mem → Prop) (Φ : VG.Proof.MlDsa.AArch64.Message.Lay → Mem → State → Prop) (a b : State) : Prop :=
  ∃ (L : VG.Proof.MlDsa.AArch64.Message.Lay) (g₁ g₂ : Reg → BitVec 64) (v₁ v₂ : VReg → BitVec 128) (m₁ m₂ : Mem), L.Ok ∧ I L m₁ m₂ ∧
    VG.Proof.MlDsa.AArch64.Message.Ctx L g₁ v₁ m₁ a ∧ VG.Proof.MlDsa.AArch64.Message.Ctx L g₂ v₂ m₂ b ∧ Φ L m₁ a ∧ Φ L m₂ b

section
variable {I : VG.Proof.MlDsa.AArch64.Message.Lay → Mem → Mem → Prop}

theorem Two.x28 {Φ : VG.Proof.MlDsa.AArch64.Message.Lay → Mem → State → Prop} {a b : State} (h : VG.Proof.MlDsa.AArch64.Message.Two I Φ a b) :
    a.gpr .x28 = b.gpr .x28 ∧ a.sp = b.sp :=
  let ⟨_, _, _, _, _, _, _, _, _, c₁, c₂, _, _⟩ := h
  ⟨c₁.x28.trans c₂.x28.symm, c₁.sp.trans c₂.sp.symm⟩

theorem two_wp {c : Prog isa} {Φ Ψ : VG.Proof.MlDsa.AArch64.Message.Lay → Mem → State → Prop}
    (hct : RelCT isa (VG.Proof.MlDsa.AArch64.Message.Two I Φ) c fun _ _ => True)
    (hw : ∀ (L : VG.Proof.MlDsa.AArch64.Message.Lay) g v m₀ (t : State), L.Ok → VG.Proof.MlDsa.AArch64.Message.Ctx L g v m₀ t → Φ L m₀ t →
      WP isa c t fun t' => VG.Proof.MlDsa.AArch64.Message.Ctx L g v m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (VG.Proof.MlDsa.AArch64.Message.Two I Φ) c (VG.Proof.MlDsa.AArch64.Message.Two I Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨L, g₁, g₂, v₁, v₂, m₁, m₂, hL, hi, c₁, c₂, f₁, f₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw L g₁ v₁ m₁ s₁ hL c₁ f₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw L g₂ v₂ m₂ s₂ hL c₂ f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, L, g₁, g₂, v₁, v₂, m₁, m₂, hL, hi, y₁.1, y₂.1, y₁.2, y₂.2⟩

theorem two_mono {Φ Ψ : VG.Proof.MlDsa.AArch64.Message.Lay → Mem → State → Prop} (h : ∀ L m t, Φ L m t → Ψ L m t) {a b : State}
    (hp : VG.Proof.MlDsa.AArch64.Message.Two I Φ a b) : VG.Proof.MlDsa.AArch64.Message.Two I Ψ a b :=
  let ⟨L, g₁, g₂, v₁, v₂, m₁, m₂, hL, hi, c₁, c₂, f₁, f₂⟩ := hp
  ⟨L, g₁, g₂, v₁, v₂, m₁, m₂, hL, hi, c₁, c₂, h _ _ _ f₁, h _ _ _ f₂⟩

/-- What the moves of the arguments `as` leave. -/
abbrev Moved (as : List (Reg × Arg)) (t t1 : State) : Prop :=
  (∀ da ∈ as, t1.gpr da.1 = da.2.val t) ∧ Only (as.map (·.1)) t t1

/-- A call after the moves of its arguments, of verified code whose public
data agree in both runs. -/
theorem call_tr {Φ : VG.Proof.MlDsa.AArch64.Message.Lay → Mem → State → Prop} {as : List (Reg × Arg)} (hok : VG.Proof.MlDsa.AArch64.Message.argsOk as = true) {n : String}
    {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (rd wr : VG.Proof.MlDsa.AArch64.Message.Lay → List Region)
    (hpre : ∀ (L : VG.Proof.MlDsa.AArch64.Message.Lay) g v m₀ (t t1 : State), L.Ok → VG.Proof.MlDsa.AArch64.Message.Ctx L g v m₀ t → Φ L m₀ t → VG.Proof.MlDsa.AArch64.Message.Moved as t t1 →
      k.pre (t1.callEntry.withRegions (rd L) (wr L)))
    (hpub : ∀ (L : VG.Proof.MlDsa.AArch64.Message.Lay) g₁ g₂ v₁ v₂ m₁ m₂ (a b a1 b1 : State), L.Ok → I L m₁ m₂ → VG.Proof.MlDsa.AArch64.Message.Ctx L g₁ v₁ m₁ a →
      VG.Proof.MlDsa.AArch64.Message.Ctx L g₂ v₂ m₂ b → Φ L m₁ a → Φ L m₂ b → VG.Proof.MlDsa.AArch64.Message.Moved as a a1 → VG.Proof.MlDsa.AArch64.Message.Moved as b b1 →
      k.pub (a1.callEntry.withRegions (rd L) (wr L)) (b1.callEntry.withRegions (rd L) (wr L)))
    (hcov : ∀ (L : VG.Proof.MlDsa.AArch64.Message.Lay) g v m₀ (t : State), L.Ok → VG.Proof.MlDsa.AArch64.Message.Ctx L g v m₀ t → Φ L m₀ t →
      (∀ r ∈ rd L, ∃ R ∈ L.rd ++ L.wr, Within r R) ∧ (∀ r ∈ wr L, ∃ R ∈ L.wr, Within r R)) :
    RelCT isa (VG.Proof.MlDsa.AArch64.Message.Two I Φ) (callA n c as) fun _ _ => True := by
  refine RelCT.seq (RelCT.postDep (Q := fun a1 b1 => ∃ a b, VG.Proof.MlDsa.AArch64.Message.Two I Φ a b ∧ VG.Proof.MlDsa.AArch64.Message.Moved as a a1 ∧ VG.Proof.MlDsa.AArch64.Message.Moved as b b1)
    (VG.Proof.MlDsa.AArch64.Message.block_x28_tr (VG.Proof.MlDsa.AArch64.Message.setArgs_xOnly hok) fun _ _ h => h.x28)
    (fun x y ⟨L, _, _, _, _, _, _, hL, _, c₁, c₂, _, _⟩ =>
      ⟨VG.Proof.MlDsa.AArch64.Message.setArgs_ok as hok x (c₁.xOk hL), VG.Proof.MlDsa.AArch64.Message.setArgs_ok as hok y (c₂.xOk hL)⟩)
    fun x y x1 y1 hp f₁ f₂ => ⟨x, y, hp, f₁, f₂⟩) ?_
  -- The layout, out of the relation, so that the call's regions are fixed.
  refine RelCT.mono (P := fun a1 b1 => ∃ L : VG.Proof.MlDsa.AArch64.Message.Lay, ∃ a b, (∃ (g₁ g₂ : Reg → BitVec 64) (v₁ v₂ : VReg → BitVec 128)
      (m₁ m₂ : Mem), L.Ok ∧ I L m₁ m₂ ∧ VG.Proof.MlDsa.AArch64.Message.Ctx L g₁ v₁ m₁ a ∧ VG.Proof.MlDsa.AArch64.Message.Ctx L g₂ v₂ m₂ b ∧ Φ L m₁ a ∧ Φ L m₂ b) ∧
      VG.Proof.MlDsa.AArch64.Message.Moved as a a1 ∧ VG.Proof.MlDsa.AArch64.Message.Moved as b b1)
    (RelCT.exists_ fun L => RelCT.call hv hct (rd L) (wr L) fun a1 b1 ⟨a, b, hp, f₁, f₂⟩ => ?_)
    (fun a1 b1 ⟨a, b, ⟨L, hp⟩, f₁, f₂⟩ => ⟨L, a, b, hp, f₁, f₂⟩) fun _ _ h => h
  obtain ⟨g₁, g₂, v₁, v₂, m₁, m₂, hL, hi, c₁, c₂, φ₁, φ₂⟩ := hp
  obtain ⟨hr, hw⟩ := hcov L g₁ v₁ m₁ a hL c₁ φ₁
  have cov : ∀ {t t1 : State} {g v m₀}, VG.Proof.MlDsa.AArch64.Message.Ctx L g v m₀ t → VG.Proof.MlDsa.AArch64.Message.Moved as t t1 →
      Covers (rd L ++ wr L) (t1.rd ++ t1.wr) ∧ Covers (wr L) t1.wr := fun hc f => by
    rw [f.2.rd, f.2.wr, hc.rd, hc.wr]
    refine ⟨VG.Proof.MlDsa.AArch64.Message.covers_of_within fun r hr' => ?_, VG.Proof.MlDsa.AArch64.Message.covers_of_within fun r hr' => ?_⟩
    · rcases List.mem_append.mp hr' with h' | h'
      · exact hr r h'
      · obtain ⟨R, hR, hW⟩ := hw r h'
        exact ⟨R, by simp [hR], hW⟩
    · exact hw r hr'
  exact ⟨hpre L g₁ v₁ m₁ a a1 hL c₁ φ₁ f₁, hpre L g₂ v₂ m₂ b b1 hL c₂ φ₂ f₂,
    hpub L g₁ g₂ v₁ v₂ m₁ m₂ a b a1 b1 hL hi c₁ c₂ φ₁ φ₂ f₁ f₂, (cov c₁ f₁).1, (cov c₁ f₁).2,
    (cov c₂ f₂).1, (cov c₂ f₂).2⟩

end

end VG.Proof.MlDsa.AArch64.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Message.HashCT`. -/
section

/-!
# ML-DSA on AArch64, `sign_message` and `verify_message`: two runs of the hashing

Untrusted: everything here is checked by Lean. In two runs with the same
layout (`Two`), zeroing the state and each call of a sponge function leak
the same: their addresses and arguments are functions of the layout alone,
and the sponge functions' public data are those arguments (`zeroSt_tr`,
`kabs_tr`, `kpad_tr`, `ksqz_tr`); so do `muHash` and `trHash`.
-/

namespace VG.Proof.MlDsa.AArch64.Message

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.AArch64 (Only)
open VG.Spec.Sha3 (rates)
open VG.Spec.MlDsa (Params)

section
variable {I : VG.Proof.MlDsa.AArch64.Message.Lay → Mem → Mem → Prop}

/-! ## Zeroing the state -/

theorem zeroSt_taint : (taint.check (AArch64.Taint.ofRegs [.x28]) (.block zeroSt) (.block [])).isSome = true := by
  rfl

theorem zeroSt_tr {Φ : VG.Proof.MlDsa.AArch64.Message.Lay → Mem → State → Prop} : RelCT isa (VG.Proof.MlDsa.AArch64.Message.Two I Φ) (.block zeroSt) fun _ _ => True :=
  AArch64.taintRel [.x28] (fun a b h => ⟨h.x28.2, fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.x28.1⟩) VG.Proof.MlDsa.AArch64.Message.zeroSt_taint

/-! ## The sponge functions -/

/-- The arguments of a call of `vg_keccak_absorb`, in its registers. -/
structure AbsA (s : State) (st dt sc : Addr) (pos len : Nat) : Prop where
  h0 : s.gpr .x0 = st
  h1 : (s.gpr .x1).toNat = 136
  h2 : (s.gpr .x2).toNat = pos
  h3 : s.gpr .x3 = dt
  h4 : (s.gpr .x4).toNat = len
  h5 : s.gpr .x5 = sc
  hp : pos < 136
  d₁ : Region.Disjoint ⟨st, 200⟩ ⟨sc, 640⟩
  d₂ : Region.Disjoint ⟨dt, len⟩ ⟨st, 200⟩
  d₃ : Region.Disjoint ⟨dt, len⟩ ⟨sc, 640⟩
  hsp : 16 ≤ s.sp.toNat
  k₁ : (Proof.MlKem.AArch64.stk s).Disjoint ⟨st, 200⟩
  k₂ : (Proof.MlKem.AArch64.stk s).Disjoint ⟨dt, len⟩
  k₃ : (Proof.MlKem.AArch64.stk s).Disjoint ⟨sc, 640⟩

theorem AbsA.pre {s : State} {st dt sc : Addr} {pos len : Nat} (h : VG.Proof.MlDsa.AArch64.Message.AbsA s st dt sc pos len) :
    Proof.Sha3.absorbAArch64.pre (s.callEntry.withRegions [⟨dt, len⟩] [⟨st, 200⟩, ⟨sc, 640⟩]) := by
  simp only [Proof.Sha3.absorbAArch64, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_sp, State.callEntry_sp, VG.Proof.MlDsa.AArch64.Message.gpr_ce s (r := .x0), VG.Proof.MlDsa.AArch64.Message.gpr_ce s (r := .x1), VG.Proof.MlDsa.AArch64.Message.gpr_ce s (r := .x2),
    VG.Proof.MlDsa.AArch64.Message.gpr_ce s (r := .x3), VG.Proof.MlDsa.AArch64.Message.gpr_ce s (r := .x4), VG.Proof.MlDsa.AArch64.Message.gpr_ce s (r := .x5), h.h0, h.h1, h.h2, h.h3, h.h4, h.h5]
  exact ⟨trivial, trivial, h.d₁, h.d₂, h.d₃, h.hsp, h.k₁, h.k₂, h.k₃, by decide, h.hp⟩

theorem absA_of {L : VG.Proof.MlDsa.AArch64.Message.Lay} (hL : L.Ok) {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {t t1 : State}
    (hc : VG.Proof.MlDsa.AArch64.Message.Ctx L g v m₀ t) {src len pos : Arg} (hm : VG.Proof.MlDsa.AArch64.Message.Moved (VG.Proof.MlDsa.AArch64.Message.absArgs src len pos) t t1) {dp : Addr} {n q : Nat}
    (hdp : src.val t = dp) (hn : len.val t = BitVec.ofNat 64 n) (hq : pos.val t = BitVec.ofNat 64 q)
    (hql : q < 136) (hnl : n < 2 ^ 64) (dS : Region.Disjoint ⟨dp, n⟩ ⟨L.ST, 200⟩)
    (dK : Region.Disjoint ⟨dp, n⟩ ⟨L.KS, 640⟩) (kD : L.STK.Disjoint ⟨dp, n⟩) : VG.Proof.MlDsa.AArch64.Message.AbsA t1 L.ST dp L.KS q n := by
  have hs1 : t1.sp = L.SP := hm.2.sp.trans hc.sp
  have e2 := hm.1 (.x2, pos) (by simp)
  have e0 := hm.1 (.x0, .off oST) (by simp)
  have e1 := hm.1 (.x1, .imm 136) (by simp)
  have e3 := hm.1 (.x3, src) (by simp)
  have e4 := hm.1 (.x4, len) (by simp)
  have e5 := hm.1 (.x5, .off oKS) (by simp)
  simp only [Arg.val, hc.x28, oST, oKS, VG.Proof.MlDsa.AArch64.Message.x0] at e0 e1 e5
  rw [hq] at e2
  rw [hdp] at e3
  rw [hn] at e4
  exact ⟨e0, by rw [e1]; rfl, by rw [e2, BitVec.toNat_ofNat]; omega, e3, by rw [e4, BitVec.toNat_ofNat]; omega, e5,
    hql, VG.Proof.MlDsa.AArch64.Message.st_ks, dS, dK, by rw [hs1]; exact hL.nSP, by simp only [Proof.MlKem.AArch64.stk, hs1]; exact VG.Proof.MlDsa.AArch64.Message.k_st hL,
    by simp only [Proof.MlKem.AArch64.stk, hs1]; exact kD, by simp only [Proof.MlKem.AArch64.stk, hs1]; exact VG.Proof.MlDsa.AArch64.Message.k_ks hL⟩

/-- Two runs of a call of `vg_keccak_absorb` whose arguments are the same
functions of the layout in both. -/
theorem kabs_tr (v : Proof.Sha3.AArch64.Permutation) {Φ : VG.Proof.MlDsa.AArch64.Message.Lay → Mem → State → Prop} {src len pos : Arg}
    (hok : VG.Proof.MlDsa.AArch64.Message.argsOk (VG.Proof.MlDsa.AArch64.Message.absArgs src len pos) = true) (dp : VG.Proof.MlDsa.AArch64.Message.Lay → Addr) (n q : VG.Proof.MlDsa.AArch64.Message.Lay → Nat)
    (hv : ∀ (L : VG.Proof.MlDsa.AArch64.Message.Lay) g vv m (t : State), L.Ok → VG.Proof.MlDsa.AArch64.Message.Ctx L g vv m t → Φ L m t →
      src.val t = dp L ∧ len.val t = BitVec.ofNat 64 (n L) ∧ pos.val t = BitVec.ofNat 64 (q L))
    (hs : ∀ L : VG.Proof.MlDsa.AArch64.Message.Lay, L.Ok → q L < 136 ∧ n L < 2 ^ 64 ∧ (∃ R ∈ L.rd ++ L.wr, Within ⟨dp L, n L⟩ R) ∧
      Region.Disjoint ⟨dp L, n L⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨dp L, n L⟩ ⟨L.KS, 640⟩ ∧
      L.STK.Disjoint ⟨dp L, n L⟩) :
    RelCT isa (VG.Proof.MlDsa.AArch64.Message.Two I Φ) (kabs v.callee src len pos) fun _ _ => True := by
  have args : ∀ (L : VG.Proof.MlDsa.AArch64.Message.Lay) g vv m₀ (t t1 : State), L.Ok → VG.Proof.MlDsa.AArch64.Message.Ctx L g vv m₀ t → Φ L m₀ t →
      VG.Proof.MlDsa.AArch64.Message.Moved (VG.Proof.MlDsa.AArch64.Message.absArgs src len pos) t t1 → VG.Proof.MlDsa.AArch64.Message.AbsA t1 L.ST (dp L) L.KS (q L) (n L) :=
    fun L g vv m₀ t t1 hL hc hφ hm => by
      obtain ⟨h1, h2, h3⟩ := hv L g vv m₀ t hL hc hφ
      obtain ⟨s1, s2, _, s4, s5, s6⟩ := hs L hL
      exact VG.Proof.MlDsa.AArch64.Message.absA_of hL hc hm h1 h2 h3 s1 s2 s4 s5 s6
  refine VG.Proof.MlDsa.AArch64.Message.call_tr hok (Proof.Sha3.AArch64.Stream.Absorb.absorb_correct v)
    (Proof.Sha3.AArch64.Stream.Absorb.absorb_ct v) (fun L => [⟨dp L, n L⟩]) (fun L => [⟨L.ST, 200⟩, ⟨L.KS, 640⟩])
    (fun L g vv m₀ t t1 hL hc hφ hm => (args L g vv m₀ t t1 hL hc hφ hm).pre)
    (fun L g₁ g₂ v₁ v₂ m₁ m₂ a b a1 b1 hL _ c₁ c₂ φ₁ φ₂ f₁ f₂ => ?_) fun L _ _ _ _ hL _ _ => ?_
  · have x := args L g₁ v₁ m₁ a a1 hL c₁ φ₁ f₁
    have y := args L g₂ v₂ m₂ b b1 hL c₂ φ₂ f₂
    simp only [Proof.Sha3.absorbAArch64, State.withRegions_sp, State.callEntry_sp,
      VG.Proof.MlDsa.AArch64.Message.gpr_ce a1 (r := .x0), VG.Proof.MlDsa.AArch64.Message.gpr_ce a1 (r := .x1), VG.Proof.MlDsa.AArch64.Message.gpr_ce a1 (r := .x2), VG.Proof.MlDsa.AArch64.Message.gpr_ce a1 (r := .x3),
      VG.Proof.MlDsa.AArch64.Message.gpr_ce a1 (r := .x4), VG.Proof.MlDsa.AArch64.Message.gpr_ce a1 (r := .x5), VG.Proof.MlDsa.AArch64.Message.gpr_ce b1 (r := .x0), VG.Proof.MlDsa.AArch64.Message.gpr_ce b1 (r := .x1),
      VG.Proof.MlDsa.AArch64.Message.gpr_ce b1 (r := .x2), VG.Proof.MlDsa.AArch64.Message.gpr_ce b1 (r := .x3), VG.Proof.MlDsa.AArch64.Message.gpr_ce b1 (r := .x4), VG.Proof.MlDsa.AArch64.Message.gpr_ce b1 (r := .x5),
      x.h0, x.h3, x.h5, y.h0, y.h3, y.h5, true_and]
    exact ⟨BitVec.eq_of_toNat_eq (x.h1.trans y.h1.symm), BitVec.eq_of_toNat_eq (x.h2.trans y.h2.symm),
      BitVec.eq_of_toNat_eq (x.h4.trans y.h4.symm), by rw [f₁.2.sp, f₂.2.sp, c₁.sp, c₂.sp]⟩
  · obtain ⟨_, _, hin, _, _, _⟩ := hs L hL
    refine ⟨fun r hr => ?_, fun r hr => ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact hin
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · have := VG.Proof.MlDsa.AArch64.Message.cov_xw hL (e := 0) (k := 200) (by omega); rwa [VG.Proof.MlDsa.AArch64.Message.x0] at this
      · exact VG.Proof.MlDsa.AArch64.Message.cov_xw hL (e := 200) (by omega)

/-- The arguments of a call of `vg_keccak_pad`, in its registers. -/
structure PadA (s : State) (st sc : Addr) (pos : Nat) : Prop where
  h0 : s.gpr .x0 = st
  h1 : (s.gpr .x1).toNat = 136
  h2 : (s.gpr .x2).toNat = pos
  h4 : s.gpr .x4 = sc
  hp : pos < 136
  d₁ : Region.Disjoint ⟨st, 200⟩ ⟨sc, 640⟩
  hsp : 16 ≤ s.sp.toNat
  k₁ : (Proof.MlKem.AArch64.stk s).Disjoint ⟨st, 200⟩
  k₃ : (Proof.MlKem.AArch64.stk s).Disjoint ⟨sc, 640⟩

theorem PadA.pre {s : State} {st sc : Addr} {pos : Nat} (h : VG.Proof.MlDsa.AArch64.Message.PadA s st sc pos) :
    Proof.Sha3.padAArch64.pre (s.callEntry.withRegions [] [⟨st, 200⟩, ⟨sc, 640⟩]) := by
  simp only [Proof.Sha3.padAArch64, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_sp, State.callEntry_sp, VG.Proof.MlDsa.AArch64.Message.gpr_ce s (r := .x0), VG.Proof.MlDsa.AArch64.Message.gpr_ce s (r := .x1), VG.Proof.MlDsa.AArch64.Message.gpr_ce s (r := .x2),
    VG.Proof.MlDsa.AArch64.Message.gpr_ce s (r := .x4), h.h0, h.h1, h.h2, h.h4]
  exact ⟨trivial, trivial, h.d₁, h.hsp, h.k₁, h.k₃, by decide, h.hp⟩

theorem kpad_tr (v : Proof.Sha3.AArch64.Permutation) {Φ : VG.Proof.MlDsa.AArch64.Message.Lay → Mem → State → Prop} {pos : Arg}
    (hok : VG.Proof.MlDsa.AArch64.Message.argsOk (VG.Proof.MlDsa.AArch64.Message.padArgs pos) = true) (q : VG.Proof.MlDsa.AArch64.Message.Lay → Nat)
    (hv : ∀ (L : VG.Proof.MlDsa.AArch64.Message.Lay) g vv m (t : State), L.Ok → VG.Proof.MlDsa.AArch64.Message.Ctx L g vv m t → Φ L m t → pos.val t = BitVec.ofNat 64 (q L))
    (hs : ∀ L : VG.Proof.MlDsa.AArch64.Message.Lay, L.Ok → q L < 136) :
    RelCT isa (VG.Proof.MlDsa.AArch64.Message.Two I Φ) (kpad v.callee pos) fun _ _ => True := by
  have args : ∀ (L : VG.Proof.MlDsa.AArch64.Message.Lay) g vv m₀ (t t1 : State), L.Ok → VG.Proof.MlDsa.AArch64.Message.Ctx L g vv m₀ t → Φ L m₀ t →
      VG.Proof.MlDsa.AArch64.Message.Moved (VG.Proof.MlDsa.AArch64.Message.padArgs pos) t t1 → VG.Proof.MlDsa.AArch64.Message.PadA t1 L.ST L.KS (q L) :=
    fun L g vv m₀ t t1 hL hc hφ hm => by
      have hs1 : t1.sp = L.SP := hm.2.sp.trans hc.sp
      have e2 := hm.1 (.x2, pos) (by simp)
      have e0 := hm.1 (.x0, .off oST) (by simp)
      have e1 := hm.1 (.x1, .imm 136) (by simp)
      have e4 := hm.1 (.x4, .off oKS) (by simp)
      simp only [Arg.val, hc.x28, oST, oKS, VG.Proof.MlDsa.AArch64.Message.x0] at e0 e1 e4
      rw [hv L g vv m₀ t hL hc hφ] at e2
      have := hs L hL
      exact ⟨e0, by rw [e1]; rfl, by rw [e2, BitVec.toNat_ofNat]; omega, e4, this, VG.Proof.MlDsa.AArch64.Message.st_ks,
        by rw [hs1]; exact hL.nSP, by simp only [Proof.MlKem.AArch64.stk, hs1]; exact VG.Proof.MlDsa.AArch64.Message.k_st hL,
        by simp only [Proof.MlKem.AArch64.stk, hs1]; exact VG.Proof.MlDsa.AArch64.Message.k_ks hL⟩
  refine VG.Proof.MlDsa.AArch64.Message.call_tr hok (Proof.Sha3.AArch64.Stream.Pad.pad_correct v) (Proof.Sha3.AArch64.Stream.Pad.pad_ct v)
    (fun _ => []) (fun L => [⟨L.ST, 200⟩, ⟨L.KS, 640⟩])
    (fun L g vv m₀ t t1 hL hc hφ hm => (args L g vv m₀ t t1 hL hc hφ hm).pre)
    (fun L g₁ g₂ v₁ v₂ m₁ m₂ a b a1 b1 hL _ c₁ c₂ φ₁ φ₂ f₁ f₂ => ?_) fun L _ _ _ _ hL _ _ => ?_
  · have x := args L g₁ v₁ m₁ a a1 hL c₁ φ₁ f₁
    have y := args L g₂ v₂ m₂ b b1 hL c₂ φ₂ f₂
    simp only [Proof.Sha3.padAArch64, State.withRegions_sp, State.callEntry_sp,
      VG.Proof.MlDsa.AArch64.Message.gpr_ce a1 (r := .x0), VG.Proof.MlDsa.AArch64.Message.gpr_ce a1 (r := .x1), VG.Proof.MlDsa.AArch64.Message.gpr_ce a1 (r := .x2), VG.Proof.MlDsa.AArch64.Message.gpr_ce a1 (r := .x4),
      VG.Proof.MlDsa.AArch64.Message.gpr_ce b1 (r := .x0), VG.Proof.MlDsa.AArch64.Message.gpr_ce b1 (r := .x1), VG.Proof.MlDsa.AArch64.Message.gpr_ce b1 (r := .x2), VG.Proof.MlDsa.AArch64.Message.gpr_ce b1 (r := .x4),
      x.h0, x.h4, y.h0, y.h4, true_and]
    exact ⟨BitVec.eq_of_toNat_eq (x.h1.trans y.h1.symm), BitVec.eq_of_toNat_eq (x.h2.trans y.h2.symm),
      by rw [f₁.2.sp, f₂.2.sp, c₁.sp, c₂.sp]⟩
  · refine ⟨fun r hr => by simp at hr, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have := VG.Proof.MlDsa.AArch64.Message.cov_xw hL (e := 0) (k := 200) (by omega); rwa [VG.Proof.MlDsa.AArch64.Message.x0] at this
    · exact VG.Proof.MlDsa.AArch64.Message.cov_xw hL (e := 200) (by omega)

/-- The arguments of a call of `vg_keccak_squeeze`, in its registers. -/
structure SqzA (s : State) (st out sc : Addr) : Prop where
  h0 : s.gpr .x0 = st
  h1 : (s.gpr .x1).toNat = 136
  h2 : (s.gpr .x2).toNat = 0
  h3 : s.gpr .x3 = out
  h4 : (s.gpr .x4).toNat = 64
  h5 : s.gpr .x5 = sc
  d₁ : Region.Disjoint ⟨st, 200⟩ ⟨out, 64⟩
  d₂ : Region.Disjoint ⟨st, 200⟩ ⟨sc, 640⟩
  d₃ : Region.Disjoint ⟨out, 64⟩ ⟨sc, 640⟩
  hsp : 16 ≤ s.sp.toNat
  k₁ : (Proof.MlKem.AArch64.stk s).Disjoint ⟨st, 200⟩
  k₂ : (Proof.MlKem.AArch64.stk s).Disjoint ⟨out, 64⟩
  k₃ : (Proof.MlKem.AArch64.stk s).Disjoint ⟨sc, 640⟩

theorem SqzA.pre {s : State} {st out sc : Addr} (h : VG.Proof.MlDsa.AArch64.Message.SqzA s st out sc) :
    Proof.Sha3.squeezeAArch64.pre (s.callEntry.withRegions [] [⟨st, 200⟩, ⟨out, 64⟩, ⟨sc, 640⟩]) := by
  simp only [Proof.Sha3.squeezeAArch64, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_sp, State.callEntry_sp, VG.Proof.MlDsa.AArch64.Message.gpr_ce s (r := .x0), VG.Proof.MlDsa.AArch64.Message.gpr_ce s (r := .x1), VG.Proof.MlDsa.AArch64.Message.gpr_ce s (r := .x2),
    VG.Proof.MlDsa.AArch64.Message.gpr_ce s (r := .x3), VG.Proof.MlDsa.AArch64.Message.gpr_ce s (r := .x4), VG.Proof.MlDsa.AArch64.Message.gpr_ce s (r := .x5), h.h0, h.h1, h.h2, h.h3, h.h4, h.h5]
  exact ⟨trivial, trivial, h.d₁, h.d₂, h.d₃, h.hsp, h.k₁, h.k₂, h.k₃, by decide, by decide⟩

theorem ksqz_tr (v : Proof.Sha3.AArch64.Permutation) {Φ : VG.Proof.MlDsa.AArch64.Message.Lay → Mem → State → Prop} :
    RelCT isa (VG.Proof.MlDsa.AArch64.Message.Two I Φ) (ksqz v.callee) fun _ _ => True := by
  have args : ∀ (L : VG.Proof.MlDsa.AArch64.Message.Lay) g vv m₀ (t t1 : State), L.Ok → VG.Proof.MlDsa.AArch64.Message.Ctx L g vv m₀ t →
      VG.Proof.MlDsa.AArch64.Message.Moved VG.Proof.MlDsa.AArch64.Message.sqzArgs t t1 → VG.Proof.MlDsa.AArch64.Message.SqzA t1 L.ST L.MU L.KS :=
    fun L g vv m₀ t t1 hL hc hm => by
      have hs1 : t1.sp = L.SP := hm.2.sp.trans hc.sp
      have e0 := hm.1 (.x0, .off oST) (by simp)
      have e1 := hm.1 (.x1, .imm 136) (by simp)
      have e2 := hm.1 (.x2, .imm 0) (by simp)
      have e3 := hm.1 (.x3, .off oMU) (by simp)
      have e4 := hm.1 (.x4, .imm 64) (by simp)
      have e5 := hm.1 (.x5, .off oKS) (by simp)
      simp only [Arg.val, hc.x28, oST, oKS, oMU, VG.Proof.MlDsa.AArch64.Message.x0] at e0 e1 e2 e3 e4 e5
      exact ⟨e0, by rw [e1]; rfl, by rw [e2]; rfl, e3, by rw [e4]; rfl, e5, VG.Proof.MlDsa.AArch64.Message.st_mu, VG.Proof.MlDsa.AArch64.Message.st_ks, VG.Proof.MlDsa.AArch64.Message.mu_ks,
        by rw [hs1]; exact hL.nSP, by simp only [Proof.MlKem.AArch64.stk, hs1]; exact VG.Proof.MlDsa.AArch64.Message.k_st hL,
        by simp only [Proof.MlKem.AArch64.stk, hs1]; exact VG.Proof.MlDsa.AArch64.Message.k_mu hL,
        by simp only [Proof.MlKem.AArch64.stk, hs1]; exact VG.Proof.MlDsa.AArch64.Message.k_ks hL⟩
  refine VG.Proof.MlDsa.AArch64.Message.call_tr (by decide) (Proof.Sha3.AArch64.Stream.Squeeze.squeeze_correct v)
    (Proof.Sha3.AArch64.Stream.Squeeze.squeeze_ct v) (fun _ => []) (fun L => [⟨L.ST, 200⟩, ⟨L.MU, 64⟩, ⟨L.KS, 640⟩])
    (fun L g vv m₀ t t1 hL hc _ hm => (args L g vv m₀ t t1 hL hc hm).pre)
    (fun L g₁ g₂ v₁ v₂ m₁ m₂ a b a1 b1 hL _ c₁ c₂ _ _ f₁ f₂ => ?_) fun L _ _ _ _ hL _ _ => ?_
  · have x := args L g₁ v₁ m₁ a a1 hL c₁ f₁
    have y := args L g₂ v₂ m₂ b b1 hL c₂ f₂
    simp only [Proof.Sha3.squeezeAArch64, State.withRegions_sp, State.callEntry_sp,
      VG.Proof.MlDsa.AArch64.Message.gpr_ce a1 (r := .x0), VG.Proof.MlDsa.AArch64.Message.gpr_ce a1 (r := .x1), VG.Proof.MlDsa.AArch64.Message.gpr_ce a1 (r := .x2), VG.Proof.MlDsa.AArch64.Message.gpr_ce a1 (r := .x3),
      VG.Proof.MlDsa.AArch64.Message.gpr_ce a1 (r := .x4), VG.Proof.MlDsa.AArch64.Message.gpr_ce a1 (r := .x5), VG.Proof.MlDsa.AArch64.Message.gpr_ce b1 (r := .x0), VG.Proof.MlDsa.AArch64.Message.gpr_ce b1 (r := .x1),
      VG.Proof.MlDsa.AArch64.Message.gpr_ce b1 (r := .x2), VG.Proof.MlDsa.AArch64.Message.gpr_ce b1 (r := .x3), VG.Proof.MlDsa.AArch64.Message.gpr_ce b1 (r := .x4), VG.Proof.MlDsa.AArch64.Message.gpr_ce b1 (r := .x5),
      x.h0, x.h3, x.h5, y.h0, y.h3, y.h5, true_and]
    exact ⟨BitVec.eq_of_toNat_eq (x.h1.trans y.h1.symm), BitVec.eq_of_toNat_eq (x.h2.trans y.h2.symm),
      BitVec.eq_of_toNat_eq (x.h4.trans y.h4.symm), by rw [f₁.2.sp, f₂.2.sp, c₁.sp, c₂.sp]⟩
  · refine ⟨fun r hr => by simp at hr, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · have := VG.Proof.MlDsa.AArch64.Message.cov_xw hL (e := 0) (k := 200) (by omega); rwa [VG.Proof.MlDsa.AArch64.Message.x0] at this
    · exact VG.Proof.MlDsa.AArch64.Message.cov_xw hL (e := 840) (by omega)
    · exact VG.Proof.MlDsa.AArch64.Message.cov_xw hL (e := 200) (by omega)

/-! ## `μ` and `tr` -/

/-- The position after the context string. -/
abbrev qCtx (L : VG.Proof.MlDsa.AArch64.Message.Lay) : Nat := (66 + L.ctxLen.toNat) % 136
/-- The position after the message. -/
abbrev qMsg (L : VG.Proof.MlDsa.AArch64.Message.Lay) : Nat := (VG.Proof.MlDsa.AArch64.Message.qCtx L + L.len.toNat) % 136

theorem muHash_tr (v : Proof.Sha3.AArch64.Permutation) {Φ : VG.Proof.MlDsa.AArch64.Message.Lay → Mem → State → Prop} {tr : Arg}
    (hok : tr.ok = true) (hret : tr.isRet = false) (trp : VG.Proof.MlDsa.AArch64.Message.Lay → Addr)
    (htr : ∀ (L : VG.Proof.MlDsa.AArch64.Message.Lay) g vv m (t : State), VG.Proof.MlDsa.AArch64.Message.Ctx L g vv m t → tr.val t = trp L)
    (hs : ∀ L : VG.Proof.MlDsa.AArch64.Message.Lay, L.Ok → (∃ R ∈ L.rd ++ L.wr, Within ⟨trp L, 64⟩ R) ∧
      Region.Disjoint ⟨trp L, 64⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨trp L, 64⟩ ⟨L.KS, 640⟩ ∧
      L.STK.Disjoint ⟨trp L, 64⟩) :
    RelCT isa (VG.Proof.MlDsa.AArch64.Message.Two I Φ) (muHash v.callee tr) fun _ _ => True := by
  -- The relation keeps only the position in `x0`.
  let Ψ : (VG.Proof.MlDsa.AArch64.Message.Lay → Nat) → VG.Proof.MlDsa.AArch64.Message.Lay → Mem → State → Prop := fun q L _ t => (t.gpr .x0).toNat = q L
  have z := VG.Proof.MlDsa.AArch64.Message.two_wp (I := I) (Φ := Φ) (Ψ := fun _ _ _ => True) VG.Proof.MlDsa.AArch64.Message.zeroSt_tr
    fun L g vv m₀ t hL hc _ => WP.mono (VG.Proof.MlDsa.AArch64.Message.zeroSt_ok hL hc) fun t' ⟨hc', _⟩ => ⟨hc', trivial⟩
  have a1 := VG.Proof.MlDsa.AArch64.Message.two_wp (I := I) (Ψ := Ψ fun _ => 64)
    (VG.Proof.MlDsa.AArch64.Message.kabs_tr v (Φ := fun _ _ _ => True) (VG.Proof.MlDsa.AArch64.Message.absOk hok rfl rfl hret rfl) trp (fun _ => 64)
      (fun _ => 0) (fun L g vv m t _ hc _ => ⟨htr L g vv m t hc, rfl, rfl⟩)
      fun L hL => ⟨by decide, by decide, (hs L hL).1, (hs L hL).2.1, (hs L hL).2.2.1, (hs L hL).2.2.2⟩)
    fun L g vv m₀ t hL hc _ => by
      obtain ⟨a, b, c, d⟩ := hs L hL
      exact WP.mono (VG.Proof.MlDsa.AArch64.Message.kabs_ok v hL hc (src := tr) (len := .imm 64) (pos := .imm 0) (n := 64) (q := 0)
        (VG.Proof.MlDsa.AArch64.Message.absOk hok rfl rfl hret rfl) (htr L g vv m₀ t hc) rfl rfl (by decide)
        (by decide) a b c d) fun t' ⟨hc', _, _, hx⟩ => ⟨hc', hx⟩
  have hdr : ∀ L : VG.Proof.MlDsa.AArch64.Message.Lay, L.Ok → 64 < 136 ∧ 2 < 2 ^ 64 ∧
      (∃ R ∈ L.rd ++ L.wr, Within ⟨L.X + BitVec.ofNat 64 984, 2⟩ R) ∧
      Region.Disjoint ⟨L.X + BitVec.ofNat 64 984, 2⟩ ⟨L.ST, 200⟩ ∧
      Region.Disjoint ⟨L.X + BitVec.ofNat 64 984, 2⟩ ⟨L.KS, 640⟩ ∧
      L.STK.Disjoint ⟨L.X + BitVec.ofNat 64 984, 2⟩ := fun L hL =>
    ⟨by decide, by decide, VG.Proof.MlDsa.AArch64.Message.cov_x hL (by omega),
      by have := Offset.disjoint L.X (d := 984) (n := 2) (e := 0) (k := 200) (by omega) (by omega) (by omega)
         simpa only [VG.Proof.MlDsa.AArch64.Message.x0] using this,
      Offset.disjoint L.X (d := 984) (n := 2) (e := 200) (k := 640) (by omega) (by omega) (by omega),
      hL.stk_x (by omega)⟩
  have a2 := VG.Proof.MlDsa.AArch64.Message.two_wp (I := I) (Φ := Ψ fun _ => 64) (Ψ := Ψ fun _ => 66)
    (VG.Proof.MlDsa.AArch64.Message.kabs_tr v (src := .off oHdr) (len := .imm 2) (pos := .imm 64) (VG.Proof.MlDsa.AArch64.Message.absOk rfl rfl rfl rfl rfl)
      (fun L => L.X + BitVec.ofNat 64 984) (fun _ => 2) (fun _ => 64)
      (fun L g vv m t _ hc _ => ⟨by rw [hc.off]; rfl, rfl, rfl⟩) hdr)
    fun L g vv m₀ t hL hc _ => by
      obtain ⟨a, b, c, d, e, f⟩ := hdr L hL
      exact WP.mono (VG.Proof.MlDsa.AArch64.Message.kabs_ok v hL hc (src := .off oHdr) (len := .imm 2) (pos := .imm 64) (n := 2) (q := 64)
        (VG.Proof.MlDsa.AArch64.Message.absOk rfl rfl rfl rfl rfl) (by rw [hc.off]; rfl) rfl rfl a b c d e f)
        fun t' ⟨hc', _, _, hx⟩ => ⟨hc', hx⟩
  have ctxS : ∀ L : VG.Proof.MlDsa.AArch64.Message.Lay, L.Ok → 66 < 136 ∧ L.ctxLen.toNat < 2 ^ 64 ∧
      (∃ R ∈ L.rd ++ L.wr, Within ⟨L.ctx, L.ctxLen.toNat⟩ R) ∧
      Region.Disjoint ⟨L.ctx, L.ctxLen.toNat⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨L.ctx, L.ctxLen.toNat⟩ ⟨L.KS, 640⟩ ∧
      L.STK.Disjoint ⟨L.ctx, L.ctxLen.toNat⟩ := fun L hL =>
    ⟨by decide, L.ctxLen.isLt, ⟨L.CTX, List.mem_append_left _ hL.inCtx, within_self _⟩,
      by have := hL.x_r hL.xCtx (e := 0) (k := 200) (by decide); simpa only [VG.Proof.MlDsa.AArch64.Message.x0] using this.symm,
      (hL.x_r hL.xCtx (e := 200) (k := 640) (by decide)).symm, hL.kCtx⟩
  have a3 := VG.Proof.MlDsa.AArch64.Message.two_wp (I := I) (Φ := Ψ fun _ => 66) (Ψ := Ψ VG.Proof.MlDsa.AArch64.Message.qCtx)
    (VG.Proof.MlDsa.AArch64.Message.kabs_tr v (src := .slot fCtx) (len := .slot fCtxLen) (pos := .imm 66) (VG.Proof.MlDsa.AArch64.Message.absOk rfl rfl rfl rfl rfl)
      (fun L => L.ctx) (fun L => L.ctxLen.toNat) (fun _ => 66)
      (fun L g vv m t _ hc _ => ⟨by rw [hc.slotV (f := fCtx) (j := 3) rfl (by omega)]; rfl,
        by rw [hc.slotV (f := fCtxLen) (j := 4) rfl (by omega), VG.Proof.MlDsa.AArch64.Message.ofNat_toNat_self]; rfl, rfl⟩) ctxS)
    fun L g vv m₀ t hL hc _ => by
      obtain ⟨a, b, c, d, e, f⟩ := ctxS L hL
      exact WP.mono (VG.Proof.MlDsa.AArch64.Message.kabs_ok v hL hc (src := .slot fCtx) (len := .slot fCtxLen) (pos := .imm 66) (q := 66)
        (VG.Proof.MlDsa.AArch64.Message.absOk rfl rfl rfl rfl rfl) (by rw [hc.slotV (f := fCtx) (j := 3) rfl (by omega)]; rfl)
        (by rw [hc.slotV (f := fCtxLen) (j := 4) rfl (by omega), VG.Proof.MlDsa.AArch64.Message.ofNat_toNat_self]; rfl) rfl a b c d e f)
        fun t' ⟨hc', _, _, hx⟩ => ⟨hc', hx⟩
  have msgS : ∀ L : VG.Proof.MlDsa.AArch64.Message.Lay, L.Ok → VG.Proof.MlDsa.AArch64.Message.qCtx L < 136 ∧ L.len.toNat < 2 ^ 64 ∧
      (∃ R ∈ L.rd ++ L.wr, Within ⟨L.msg, L.len.toNat⟩ R) ∧
      Region.Disjoint ⟨L.msg, L.len.toNat⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨L.msg, L.len.toNat⟩ ⟨L.KS, 640⟩ ∧
      L.STK.Disjoint ⟨L.msg, L.len.toNat⟩ := fun L hL =>
    ⟨Nat.mod_lt _ (by decide), L.len.isLt, ⟨L.MSG, List.mem_append_left _ hL.inMsg, within_self _⟩,
      by have := hL.x_r hL.xMsg (e := 0) (k := 200) (by decide); simpa only [VG.Proof.MlDsa.AArch64.Message.x0] using this.symm,
      (hL.x_r hL.xMsg (e := 200) (k := 640) (by decide)).symm, hL.kMsg⟩
  have a4 := VG.Proof.MlDsa.AArch64.Message.two_wp (I := I) (Φ := Ψ VG.Proof.MlDsa.AArch64.Message.qCtx) (Ψ := Ψ VG.Proof.MlDsa.AArch64.Message.qMsg)
    (VG.Proof.MlDsa.AArch64.Message.kabs_tr v (src := .slot fMsg) (len := .slot fLen) (pos := .ret) (VG.Proof.MlDsa.AArch64.Message.absOk rfl rfl rfl rfl rfl)
      (fun L => L.msg) (fun L => L.len.toNat) VG.Proof.MlDsa.AArch64.Message.qCtx
      (fun L g vv m t _ hc hφ => ⟨by rw [hc.slotV (f := fMsg) (j := 1) rfl (by omega)]; rfl,
        by rw [hc.slotV (f := fLen) (j := 2) rfl (by omega), VG.Proof.MlDsa.AArch64.Message.ofNat_toNat_self]; rfl, VG.Proof.MlDsa.AArch64.Message.ofNat_toNat_eq hφ⟩) msgS)
    fun L g vv m₀ t hL hc hφ => by
      obtain ⟨a, b, c, d, e, f⟩ := msgS L hL
      exact WP.mono (VG.Proof.MlDsa.AArch64.Message.kabs_ok v hL hc (src := .slot fMsg) (len := .slot fLen) (pos := .ret)
        (VG.Proof.MlDsa.AArch64.Message.absOk rfl rfl rfl rfl rfl) (by rw [hc.slotV (f := fMsg) (j := 1) rfl (by omega)]; rfl)
        (by rw [hc.slotV (f := fLen) (j := 2) rfl (by omega), VG.Proof.MlDsa.AArch64.Message.ofNat_toNat_self]; rfl) (VG.Proof.MlDsa.AArch64.Message.ofNat_toNat_eq hφ)
        a b c d e f) fun t' ⟨hc', _, _, hx⟩ => ⟨hc', hx⟩
  have pd := VG.Proof.MlDsa.AArch64.Message.kpad_tr v (I := I) (Φ := Ψ VG.Proof.MlDsa.AArch64.Message.qMsg) (pos := .ret) (VG.Proof.MlDsa.AArch64.Message.padOk rfl) VG.Proof.MlDsa.AArch64.Message.qMsg
    (fun L g vv m t _ _ hφ => VG.Proof.MlDsa.AArch64.Message.ofNat_toNat_eq hφ) fun L _ => Nat.mod_lt _ (by decide)
  have pd' := VG.Proof.MlDsa.AArch64.Message.two_wp (I := I) (Φ := Ψ VG.Proof.MlDsa.AArch64.Message.qMsg) (Ψ := fun _ _ _ => True) pd
    fun L g vv m₀ t hL hc hφ => WP.mono (VG.Proof.MlDsa.AArch64.Message.kpad_ok v hL hc (pos := .ret) (VG.Proof.MlDsa.AArch64.Message.padOk rfl) (VG.Proof.MlDsa.AArch64.Message.ofNat_toNat_eq hφ)
      (Nat.mod_lt _ (by decide))) fun t' ⟨hc', _⟩ => ⟨hc', trivial⟩
  exact RelCT.seq z (a1.seq (a2.seq (a3.seq (a4.seq (pd'.seq (VG.Proof.MlDsa.AArch64.Message.ksqz_tr v))))))

theorem trHash_tr (v : Proof.Sha3.AArch64.Permutation) {p : Params} (hk : p.pkLen < 2 ^ 16)
    {Φ : VG.Proof.MlDsa.AArch64.Message.Lay → Mem → State → Prop} (hΦ : ∀ L m t, Φ L m t → L.keyLen = p.pkLen) :
    RelCT isa (VG.Proof.MlDsa.AArch64.Message.Two I Φ) (trHash v.callee p) fun _ _ => True := by
  have keySide : ∀ L : VG.Proof.MlDsa.AArch64.Message.Lay, L.Ok → 0 < 136 ∧ L.keyLen < 2 ^ 64 ∧
      (∃ R ∈ L.rd ++ L.wr, Within ⟨L.key, L.keyLen⟩ R) ∧
      Region.Disjoint ⟨L.key, L.keyLen⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨L.key, L.keyLen⟩ ⟨L.KS, 640⟩ ∧
      L.STK.Disjoint ⟨L.key, L.keyLen⟩ := fun L hL =>
    ⟨by decide, by have := hL.hKey.2; omega, ⟨L.KEY, List.mem_append_left _ hL.inKey, within_self _⟩,
      by have := hL.x_r hL.xKey (e := 0) (k := 200) (by decide); simpa only [VG.Proof.MlDsa.AArch64.Message.x0] using this.symm,
      (hL.x_r hL.xKey (e := 200) (k := 640) (by decide)).symm, hL.kKey⟩
  have z := VG.Proof.MlDsa.AArch64.Message.two_wp (I := I) (Φ := Φ) (Ψ := fun L _ _ => L.keyLen = p.pkLen) VG.Proof.MlDsa.AArch64.Message.zeroSt_tr
    fun L g vv m₀ t hL hc hφ => WP.mono (VG.Proof.MlDsa.AArch64.Message.zeroSt_ok hL hc) fun t' ⟨hc', _⟩ => ⟨hc', hΦ L m₀ t hφ⟩
  have a1 := VG.Proof.MlDsa.AArch64.Message.two_wp (I := I) (Φ := fun L _ _ => L.keyLen = p.pkLen) (Ψ := fun _ _ _ => True)
    (VG.Proof.MlDsa.AArch64.Message.kabs_tr v (src := .slot fKey) (len := .imm p.pkLen) (pos := .imm 0)
      (VG.Proof.MlDsa.AArch64.Message.absOk rfl (by simp only [Arg.ok, decide_eq_true_eq]; omega) rfl rfl rfl) (fun L => L.key) (fun L => L.keyLen)
      (fun _ => 0) (fun L g vv m t _ hc hφ => ⟨by rw [hc.slotV (f := fKey) (j := 0) rfl (by omega)]; rfl,
        by rw [hφ]; rfl, rfl⟩) keySide)
    fun L g vv m₀ t hL hc hφ => by
      obtain ⟨a, b, c, d, e, f⟩ := keySide L hL
      exact WP.mono (VG.Proof.MlDsa.AArch64.Message.kabs_ok v hL hc (src := .slot fKey) (len := .imm p.pkLen) (pos := .imm 0)
        (n := L.keyLen) (q := 0) (VG.Proof.MlDsa.AArch64.Message.absOk rfl (by simp only [Arg.ok, decide_eq_true_eq]; omega) rfl rfl rfl)
        (by rw [hc.slotV (f := fKey) (j := 0) rfl (by omega)]; rfl) (by rw [hφ]; rfl) rfl a b c d e f)
        fun t' ⟨hc', _⟩ => ⟨hc', trivial⟩
  have pd := VG.Proof.MlDsa.AArch64.Message.kpad_tr v (I := I) (Φ := fun _ _ _ => True) (pos := .imm (p.pkLen % 136))
    (VG.Proof.MlDsa.AArch64.Message.padOk (by simp only [Arg.ok, decide_eq_true_eq]; omega)) (fun _ => p.pkLen % 136)
    (fun _ _ _ _ _ _ _ _ => rfl) fun _ _ => Nat.mod_lt _ (by decide)
  have pd' := VG.Proof.MlDsa.AArch64.Message.two_wp (I := I) (Φ := fun _ _ _ => True) (Ψ := fun _ _ _ => True) pd
    fun L g vv m₀ t hL hc _ => WP.mono (VG.Proof.MlDsa.AArch64.Message.kpad_ok v hL hc (pos := .imm (p.pkLen % 136))
      (VG.Proof.MlDsa.AArch64.Message.padOk (by simp only [Arg.ok, decide_eq_true_eq]; omega)) rfl (Nat.mod_lt _ (by decide)))
      fun t' ⟨hc', _⟩ => ⟨hc', trivial⟩
  exact RelCT.seq z (a1.seq (pd'.seq (VG.Proof.MlDsa.AArch64.Message.ksqz_tr v)))

end

end VG.Proof.MlDsa.AArch64.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Message.SignCT`. -/
section

/-!
# ML-DSA on AArch64, `sign_message`: constant time

Untrusted: everything here is checked by Lean. Two runs from states that
satisfy the contract and agree on its public data, which includes what
`signMessageLeak` says (`signI`), leak the same: the branch on `ctx_len`,
the entry and the exit depend only on the pointers and the lengths; the
hashing leaks only the layout (`muHash_tr`); and the call of the signing
function on `μ` leaks only `signLeak` of the key, `μ` and `rnd`, which is
`signMessageLeak` of the inputs (`signCall_tr`).
-/

namespace VG.Proof.MlDsa.AArch64.Message

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.AArch64 (Only)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable {p : Params}

/-- What the contract says two runs agree on, beyond the pointers and lengths. -/
def signI (p : Params) (L : VG.Proof.MlDsa.AArch64.Message.Lay) (m₁ m₂ : Mem) : Prop :=
  signMessageLeak p (bytesAt m₁ L.key p.skLen) (bytesAt m₁ L.msg L.len.toNat) (bytesAt m₁ L.ctx L.ctxLen.toNat)
      (bytesAt m₁ L.rnd 32) =
    signMessageLeak p (bytesAt m₂ L.key p.skLen) (bytesAt m₂ L.msg L.len.toNat)
      (bytesAt m₂ L.ctx L.ctxLen.toNat) (bytesAt m₂ L.rnd 32)

/-- The layout is that of a run of `sign_message` from a state with the
memory `m`, past the branch on `ctx_len`. -/
def SOk (p : Params) (L : VG.Proof.MlDsa.AArch64.Message.Lay) (m : Mem) : Prop :=
  ∃ σ, VG.Proof.MlDsa.AArch64.Message.SPre p σ ∧ (σ.gpr .x4).toNat < 256 ∧ VG.Proof.MlDsa.AArch64.Message.slay p σ = L ∧ σ.mem = m

/-- `μ` at `X + 840`. -/
def MuOk (L : VG.Proof.MlDsa.AArch64.Message.Lay) (m : Mem) (t : State) : Prop :=
  bytesAt t.mem L.MU 64 = H (bytesAt m (L.key + BitVec.ofNat 64 64) 64 ++ VG.Proof.MlDsa.AArch64.Message.hdrBytes L ++
    bytesAt m L.ctx L.ctxLen.toNat ++ bytesAt m L.msg L.len.toNat) 64

/-- What `sign_message` leaks is what the signing function on `μ` leaks, for
the `μ` it computes. -/
theorem leak_eq {L : VG.Proof.MlDsa.AArch64.Message.Lay} (hL : L.Ok) (hk : L.keyLen = p.skLen) (m : Mem) :
    signMessageLeak p (bytesAt m L.key p.skLen) (bytesAt m L.msg L.len.toNat) (bytesAt m L.ctx L.ctxLen.toNat)
        (bytesAt m L.rnd 32) =
      signLeak p (bytesAt m L.key p.skLen) (H (bytesAt m (L.key + BitVec.ofNat 64 64) 64 ++ VG.Proof.MlDsa.AArch64.Message.hdrBytes L ++
        bytesAt m L.ctx L.ctxLen.toNat ++ bytesAt m L.msg L.len.toNat) 64) (bytesAt m L.rnd 32) := by
  have := hL.hKey
  rw [signMessageLeak, formatMessage_some (by rw [Proof.MlKem.bytesAt_length]; exact hL.ctxLt)]
  simp only [messageRep, skTr, VG.Proof.MlDsa.AArch64.Message.hdrBytes, Proof.MlKem.bytesAt_length, List.append_assoc]
  rw [Proof.MlKem.bytesAt_slice _ _ (by omega)]

/-- What a layout of `sign_message` says of `rnd`, `sig` and `scratch`. -/
structure SFacts (p : Params) (L : VG.Proof.MlDsa.AArch64.Message.Lay) : Prop where
  key : L.keyLen = p.skLen
  xRnd : L.XS.Disjoint ⟨L.rnd, 32⟩
  kRnd : L.STK.Disjoint ⟨L.rnd, 32⟩
  inRnd : (⟨L.rnd, 32⟩ : Region) ∈ L.rd
  inSig : (⟨L.sig, p.sigLen⟩ : Region) ∈ L.wr
  inScr : ∃ R ∈ L.wr, Within ⟨L.scr, VG.Proof.MlDsa.AArch64.Message.sScr p⟩ R
  inMu : ∃ R ∈ L.wr, Within ⟨L.MU, 64⟩ R

theorem SOk.facts {L : VG.Proof.MlDsa.AArch64.Message.Lay} {m : Mem} (h : VG.Proof.MlDsa.AArch64.Message.SOk p L m) : VG.Proof.MlDsa.AArch64.Message.SFacts p L := by
  obtain ⟨σ, hσ, _, rfl, -⟩ := h
  exact ⟨rfl, hσ.rndScr.symm.sub_left (VG.Proof.MlDsa.AArch64.Message.slay_X p σ).sub, hσ.stkRnd, by simp [VG.Proof.MlDsa.AArch64.Message.slay, hσ.rd],
    by simp [VG.Proof.MlDsa.AArch64.Message.slay, hσ.wr], ⟨⟨σ.gpr .x7, VG.Proof.MlDsa.AArch64.Message.mScrLen p⟩, by simp [VG.Proof.MlDsa.AArch64.Message.slay, hσ.wr],
      within_base _ (by rw [VG.Proof.MlDsa.AArch64.Message.mScr_eq]; simp only [VG.Proof.MlDsa.AArch64.Message.sScr, oE]; omega)⟩,
    ⟨⟨σ.gpr .x7, VG.Proof.MlDsa.AArch64.Message.mScrLen p⟩, by simp [VG.Proof.MlDsa.AArch64.Message.slay, hσ.wr], VG.Proof.MlDsa.AArch64.Message.mu_within p σ⟩⟩

/-- Two runs of the call of the signing function on `μ`. -/
theorem signCall_tr {n : String} {c : Prog isa} (hS : VG.Proof.MlDsa.AArch64.Message.SignFn p c) (hp : p ∈ VG.Proof.MlDsa.AArch64.Message.params) :
    RelCT isa (VG.Proof.MlDsa.AArch64.Message.Two (VG.Proof.MlDsa.AArch64.Message.signI p) fun L m t => VG.Proof.MlDsa.AArch64.Message.SOk p L m ∧ VG.Proof.MlDsa.AArch64.Message.MuOk L m t) (callA n c VG.Proof.MlDsa.AArch64.Message.signArgs) fun _ _ => True := by
  refine VG.Proof.MlDsa.AArch64.Message.call_tr (by decide) hS.ver.1 hS.ver.2.1
    (fun L => [⟨L.key, p.skLen⟩, ⟨L.MU, 64⟩, ⟨L.rnd, 32⟩]) (fun L => [⟨L.sig, p.sigLen⟩, ⟨L.scr, VG.Proof.MlDsa.AArch64.Message.sScr p⟩])
    (fun L g v m₀ t t1 hL hc hφ hm => ?_) (fun L g₁ g₂ v₁ v₂ m₁ m₂ a b a1 b1 hL hi c₁ c₂ φ₁ φ₂ f₁ f₂ => ?_)
    (fun L g v m₀ t hL hc hφ => ?_)
  · obtain ⟨⟨σ, hσ, h8, rfl, -⟩, -⟩ := hφ
    exact VG.Proof.MlDsa.AArch64.Message.signK_pre hp hσ h8 hc hm.1 (hm.2.sp.trans hc.sp)
  · obtain ⟨σ, hσ, h8, rfl, -⟩ := φ₁.1
    have F := φ₁.1.facts
    obtain ⟨x0, x1, x2, x3, x4⟩ := VG.Proof.MlDsa.AArch64.Message.signRegs_of c₁ f₁.1
    obtain ⟨y0, y1, y2, y3, y4⟩ := VG.Proof.MlDsa.AArch64.Message.signRegs_of c₂ f₂.1
    have hk := hL.hKey
    have ek : ∀ {g v m₀} {a a1 : State}, VG.Proof.MlDsa.AArch64.Message.Ctx (VG.Proof.MlDsa.AArch64.Message.slay p σ) g v m₀ a → VG.Proof.MlDsa.AArch64.Message.Moved VG.Proof.MlDsa.AArch64.Message.signArgs a a1 →
        bytesAt a1.mem (σ.gpr .x0) p.skLen = bytesAt m₀ (σ.gpr .x0) p.skLen := fun c f => by
      rw [f.2.mem]
      exact c.bytesAt_eq (p := (VG.Proof.MlDsa.AArch64.Message.slay p σ).key) hL.xKey hL.kKey (by have := hL.nKey; simp only [VG.Proof.MlDsa.AArch64.Message.slay] at this ⊢; omega)
    have er : ∀ {g v m₀} {a a1 : State}, VG.Proof.MlDsa.AArch64.Message.Ctx (VG.Proof.MlDsa.AArch64.Message.slay p σ) g v m₀ a → VG.Proof.MlDsa.AArch64.Message.Moved VG.Proof.MlDsa.AArch64.Message.signArgs a a1 →
        bytesAt a1.mem (σ.gpr .x5) 32 = bytesAt m₀ (σ.gpr .x5) 32 := fun c f => by
      rw [f.2.mem]
      exact c.bytesAt_eq (p := (VG.Proof.MlDsa.AArch64.Message.slay p σ).rnd) F.xRnd F.kRnd (by decide)
    have eμ : ∀ {a a1 : State}, VG.Proof.MlDsa.AArch64.Message.Moved VG.Proof.MlDsa.AArch64.Message.signArgs a a1 →
        bytesAt a1.mem (VG.Proof.MlDsa.AArch64.Message.slay p σ).MU 64 = bytesAt a.mem (VG.Proof.MlDsa.AArch64.Message.slay p σ).MU 64 := fun f => by rw [f.2.mem]
    sig_pub [signContract, signSig, AArch64.abi, AArch64.argRegs, List.range, List.range.loop]
    simp only [x0, x1, x2, x3, x4, y0, y1, y2, y3, y4, and_true]
    refine ⟨by rw [f₁.2.sp, f₂.2.sp, c₁.sp, c₂.sp], ?_⟩
    rw [ek c₁ f₁, ek c₂ f₂, er c₁ f₁, er c₂ f₂, eμ f₁, eμ f₂, φ₁.2, φ₂.2]
    have := hi
    unfold VG.Proof.MlDsa.AArch64.Message.signI at this
    rw [VG.Proof.MlDsa.AArch64.Message.leak_eq hL F.key, VG.Proof.MlDsa.AArch64.Message.leak_eq hL F.key] at this
    exact this
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
  sp : s₁.sp = s₂.sp
  leak : signMessageLeak p (bytesAt s₁.mem (s₁.gpr .x0) p.skLen) (bytesAt s₁.mem (s₁.gpr .x1) (s₁.gpr .x2).toNat)
      (bytesAt s₁.mem (s₁.gpr .x3) (s₁.gpr .x4).toNat) (bytesAt s₁.mem (s₁.gpr .x5) 32) =
    signMessageLeak p (bytesAt s₂.mem (s₂.gpr .x0) p.skLen) (bytesAt s₂.mem (s₂.gpr .x1) (s₂.gpr .x2).toNat)
      (bytesAt s₂.mem (s₂.gpr .x3) (s₂.gpr .x4).toNat) (bytesAt s₂.mem (s₂.gpr .x5) 32)
  x0 : s₁.gpr .x0 = s₂.gpr .x0
  x1 : s₁.gpr .x1 = s₂.gpr .x1
  x2 : s₁.gpr .x2 = s₂.gpr .x2
  x3 : s₁.gpr .x3 = s₂.gpr .x3
  x4 : s₁.gpr .x4 = s₂.gpr .x4
  x5 : s₁.gpr .x5 = s₂.gpr .x5
  x6 : s₁.gpr .x6 = s₂.gpr .x6
  x7 : s₁.gpr .x7 = s₂.gpr .x7

theorem sPub_of {s₁ s₂ : State} (h : (signMessageContract p AArch64.abi 16).pub s₁ s₂) : VG.Proof.MlDsa.AArch64.Message.SPub p s₁ s₂ := by
  sig_pub [signMessageContract, signMessageSig, AArch64.abi, AArch64.argRegs, List.range, List.range.loop] at h
  obtain ⟨a, b, c, d, e, f, g, h, i, j⟩ := h
  exact ⟨a, b, c, d, e, f, g, h, i, j⟩

/-- Two runs from states agreeing on the public data have the same layout. -/
theorem slay_eq {s₁ s₂ : State} (h₁ : VG.Proof.MlDsa.AArch64.Message.SPre p s₁) (h₂ : VG.Proof.MlDsa.AArch64.Message.SPre p s₂) (h : VG.Proof.MlDsa.AArch64.Message.SPub p s₁ s₂) : VG.Proof.MlDsa.AArch64.Message.slay p s₁ = VG.Proof.MlDsa.AArch64.Message.slay p s₂ := by
  have e1 : s₁.rd = s₂.rd := by
    rw [h₁.rd, h₂.rd]; simp only [VG.Proof.MlDsa.AArch64.Message.rKey, VG.Proof.MlDsa.AArch64.Message.rMsg, VG.Proof.MlDsa.AArch64.Message.rCtx, h.x0, h.x1, h.x2, h.x3, h.x4, h.x5]
  have e2 : s₁.wr = s₂.wr := by
    rw [h₁.wr, h₂.wr]; simp only [h.x6, h.x7]
  simp only [VG.Proof.MlDsa.AArch64.Message.slay, h.sp, h.x0, h.x1, h.x2, h.x3, h.x4, h.x5, h.x6, h.x7, e1, e2]

/-- The body, between the entry and the exit: its runs end with the same
`x28` and stack pointer. -/
theorem signBody_tr (v : Proof.Sha3.AArch64.Permutation) {n : String} {c : Prog isa} (hS : VG.Proof.MlDsa.AArch64.Message.SignFn p c)
    (hp : p ∈ VG.Proof.MlDsa.AArch64.Message.params) :
    RelCT isa (VG.Proof.MlDsa.AArch64.Message.Two (VG.Proof.MlDsa.AArch64.Message.signI p) fun L m _ => VG.Proof.MlDsa.AArch64.Message.SOk p L m)
      (.seq (muHash v.callee (.slotOff fKey 64)) (callA n c VG.Proof.MlDsa.AArch64.Message.signArgs))
      fun a b => a.gpr .x28 = b.gpr .x28 ∧ a.sp = b.sp := by
  have side : ∀ L : VG.Proof.MlDsa.AArch64.Message.Lay, L.Ok → (∃ R ∈ L.rd ++ L.wr, Within ⟨L.key + BitVec.ofNat 64 64, 64⟩ R) ∧
      Region.Disjoint ⟨L.key + BitVec.ofNat 64 64, 64⟩ ⟨L.ST, 200⟩ ∧
      Region.Disjoint ⟨L.key + BitVec.ofNat 64 64, 64⟩ ⟨L.KS, 640⟩ ∧
      L.STK.Disjoint ⟨L.key + BitVec.ofNat 64 64, 64⟩ := fun L hL => by
    have := hL.hKey
    have w : Within ⟨L.key + BitVec.ofNat 64 64, 64⟩ L.KEY := within_off _ (by omega)
    have hst : Region.Sub ⟨L.ST, 200⟩ L.XS := by
      have := Offset.sub_base L.X (d := 0) (n := 200) (k := 1024) (by omega)
      simpa only [VG.Proof.MlDsa.AArch64.Message.x0] using this
    exact ⟨⟨_, List.mem_append_left _ hL.inKey, w⟩, (hL.xKey.symm.sub_left w.sub).sub_right hst,
      (hL.xKey.symm.sub_left w.sub).sub_right (Offset.sub_base _ (by decide : 200 + 640 ≤ 1024)),
      hL.kKey.sub_right w.sub⟩
  have mh := VG.Proof.MlDsa.AArch64.Message.muHash_tr v (I := VG.Proof.MlDsa.AArch64.Message.signI p) (Φ := fun L m _ => VG.Proof.MlDsa.AArch64.Message.SOk p L m) (tr := .slotOff fKey 64) (by decide) rfl
    (fun L => L.key + BitVec.ofNat 64 64) (fun L g vv m t hc => hc.slotOffV 64) side
  have mh' := VG.Proof.MlDsa.AArch64.Message.two_wp (I := VG.Proof.MlDsa.AArch64.Message.signI p) (Φ := fun L m _ => VG.Proof.MlDsa.AArch64.Message.SOk p L m) (Ψ := fun L m t => VG.Proof.MlDsa.AArch64.Message.SOk p L m ∧ VG.Proof.MlDsa.AArch64.Message.MuOk L m t) mh
    fun L g vv m₀ t hL hc hφ => by
      have := hL.hKey
      have w : Within ⟨L.key + BitVec.ofNat 64 64, 64⟩ L.KEY := within_off _ (by omega)
      obtain ⟨a, b, c, d⟩ := side L hL
      refine WP.mono (VG.Proof.MlDsa.AArch64.Message.muHash_ok v hL hc (tr := .slotOff fKey 64) (by decide) rfl (fun t' hc' => hc'.slotOffV 64)
        a b c d) fun t' ⟨hc', hμ⟩ => ⟨hc', hφ, ?_⟩
      unfold VG.Proof.MlDsa.AArch64.Message.MuOk
      rw [hμ, hc.bytesAt_eq (hL.xKey.sub_right w.sub) (hL.kKey.sub_right w.sub) (by decide)]
  refine RelCT.postDep (F := fun x x' => x'.gpr .x28 = x.gpr .x28 ∧ x'.sp = x.sp)
    (mh'.seq (VG.Proof.MlDsa.AArch64.Message.signCall_tr hS hp)) (fun x y hxy => ?_) fun x y x' y' hxy f₁ f₂ => ?_
  · have run : ∀ {L : VG.Proof.MlDsa.AArch64.Message.Lay} {g vv m₀} {t : State}, L.Ok → VG.Proof.MlDsa.AArch64.Message.Ctx L g vv m₀ t → VG.Proof.MlDsa.AArch64.Message.SOk p L m₀ →
        WP isa (.seq (muHash v.callee (.slotOff fKey 64)) (callA n c VG.Proof.MlDsa.AArch64.Message.signArgs)) t
          fun t' => t'.gpr .x28 = t.gpr .x28 ∧ t'.sp = t.sp := fun hL hc hφ => by
      obtain ⟨σ, hσ, h8, rfl, -⟩ := hφ
      obtain ⟨a, b, c, d⟩ := side _ hL
      refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Message.muHash_ok v hL hc (tr := .slotOff fKey 64) (by decide) rfl
        (fun t' hc' => hc'.slotOffV 64) a b c d) fun t₁ ⟨hc₁, _⟩ => ?_)
      exact WP.mono (VG.Proof.MlDsa.AArch64.Message.signCall_ok hS hp hσ h8 hc₁) fun s' ⟨hf, _⟩ =>
        ⟨hf.x28.trans hc.x28.symm, hf.sp.trans hc.sp.symm⟩
    obtain ⟨L, _, _, _, _, _, _, hL, _, c₁, c₂, φ₁, φ₂⟩ := hxy
    exact ⟨run hL c₁ φ₁, run hL c₂ φ₂⟩
  · obtain ⟨L, _, _, _, _, _, _, _, _, c₁, c₂, _, _⟩ := hxy
    exact ⟨by rw [f₁.1, f₂.1, c₁.x28, c₂.x28], by rw [f₁.2, f₂.2, c₁.sp, c₂.sp]⟩

/-- The entry states of two runs: the precondition and the public data. -/
abbrev SP2 (p : Params) (x y : State) : Prop :=
  (signMessageContract p AArch64.abi 16).pre x ∧ (signMessageContract p AArch64.abi 16).pre y ∧
    (signMessageContract p AArch64.abi 16).pub x y

/-- After the shift of `ctx_len`. -/
abbrev ALsr (x s1 : State) : Prop :=
  Only [.x9] x s1 ∧ isa.eval (.nonzero .x .x9) s1 = some (decide ¬ (x.gpr .x4).toNat < 256)

theorem lsr_taint :
    (taint.check (AArch64.Taint.ofRegs []) (.block [.lsr .x .x9 .x4 8]) (.block [])).isSome = true := by rfl

theorem movz2_taint :
    (taint.check (AArch64.Taint.ofRegs []) (.block [.movz .x .x0 2 0]) (.block [])).isSome = true := by rfl

theorem leave_taint : (taint.check (AArch64.Taint.ofRegs [.x28]) (.block leave) (.block [])).isSome = true := by
  rfl

theorem enterS_taint (p : Params) :
    (taint.check (AArch64.Taint.ofRegs [.x7]) (.block (enter .x7 p signSaves)) (.block [])).isSome = true := by
  rfl

theorem signMessage_ct (v : Proof.Sha3.AArch64.Permutation) {n : String} {c : Prog isa} (hS : VG.Proof.MlDsa.AArch64.Message.SignFn p c)
    (hp : p ∈ VG.Proof.MlDsa.AArch64.Message.params) :
    ConstantTime isa (signMessageContract p AArch64.abi 16).pre (signMessageContract p AArch64.abi 16).pub
      (signMessage v.callee n c p) := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  have e0 : (fun s₁ s₂ => (signMessageContract p AArch64.abi 16).pre s₁ ∧
      (signMessageContract p AArch64.abi 16).pre s₂ ∧ (signMessageContract p AArch64.abi 16).pub s₁ s₂) =
      VG.Proof.MlDsa.AArch64.Message.Ghost (VG.Proof.MlDsa.AArch64.Message.SP2 p) (fun x a => a = x) := by
    funext a b; apply propext
    exact ⟨fun h => ⟨a, b, h, rfl, rfl⟩, fun ⟨_, _, h, e₁, e₂⟩ => e₁ ▸ e₂ ▸ h⟩
  rw [e0]
  unfold signMessage top
  -- `x9 ← ctx_len >> 8`.
  have hlsr := VG.Proof.MlDsa.AArch64.Message.ghost_step (P := VG.Proof.MlDsa.AArch64.Message.SP2 p) (A := fun x a => a = x) (B := VG.Proof.MlDsa.AArch64.Message.ALsr) (c := .block [.lsr .x .x9 .x4 8])
    (AArch64.taintRel [] (fun a b ⟨x, y, hxy, e₁, e₂⟩ => by
      subst e₁ e₂; exact ⟨(VG.Proof.MlDsa.AArch64.Message.sPub_of hxy.2.2).sp, by simp⟩) VG.Proof.MlDsa.AArch64.Message.lsr_taint)
    fun x y a b _ e₁ e₂ => by subst e₁ e₂; exact ⟨VG.Proof.MlDsa.AArch64.Message.lsr_ok _, VG.Proof.MlDsa.AArch64.Message.lsr_ok _⟩
  refine RelCT.seq hlsr (RelCT.ite (fun a b ⟨x, y, hxy, f₁, f₂⟩ => by
    rw [f₁.2, f₂.2, (VG.Proof.MlDsa.AArch64.Message.sPub_of hxy.2.2).x4]) ?_ ?_)
  · -- `ctx_len ≥ 256`: return 2.
    exact AArch64.taintRel [] (fun a b ⟨⟨x, y, hxy, f₁, f₂⟩, _⟩ =>
      ⟨by rw [f₁.1.sp, f₂.1.sp]; exact (VG.Proof.MlDsa.AArch64.Message.sPub_of hxy.2.2).sp, by simp⟩) VG.Proof.MlDsa.AArch64.Message.movz2_taint
  · -- The entry.
    let A : State → State → Prop := fun x a => VG.Proof.MlDsa.AArch64.Message.ALsr x a ∧ isa.eval (.nonzero .x .x9) a = some false
    let B : State → State → Prop := fun x t => (x.gpr .x4).toNat < 256 ∧
      ∃ a : State, a.mem = x.mem ∧ VG.Proof.MlDsa.AArch64.Message.Ctx (VG.Proof.MlDsa.AArch64.Message.slay p x) a.gpr a.v a.mem t
    have hent := VG.Proof.MlDsa.AArch64.Message.ghost_step (P := VG.Proof.MlDsa.AArch64.Message.SP2 p) (A := A) (B := B) (c := .block (enter .x7 p signSaves))
      (AArch64.taintRel [.x7] (fun a b ⟨x, y, hxy, f₁, f₂⟩ => ⟨by rw [f₁.1.1.sp, f₂.1.1.sp]; exact (VG.Proof.MlDsa.AArch64.Message.sPub_of hxy.2.2).sp,
        fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          rw [f₁.1.1.get .x7, f₂.1.1.get .x7]; exact (VG.Proof.MlDsa.AArch64.Message.sPub_of hxy.2.2).x7⟩) (VG.Proof.MlDsa.AArch64.Message.enterS_taint p))
      fun x y a b hxy fa fb => by
        have en : ∀ (x' a' : State), (signMessageContract p AArch64.abi 16).pre x' → A x' a' →
            WP isa (.block (enter .x7 p signSaves)) a' (B x') := fun x' a' hx ⟨⟨o, e⟩, ef⟩ => by
          have h8 : (x'.gpr .x4).toNat < 256 := by
            rw [e] at ef; simpa using ef
          have hL := VG.Proof.MlDsa.AArch64.Message.slay_ok hp (VG.Proof.MlDsa.AArch64.Message.sPre_of hx) h8
          exact WP.mono (VG.Proof.MlDsa.AArch64.Message.enter_ok hL rfl (by decide) rfl (o.get .x7) (by rw [o.sp]; rfl) (by rw [o.rd]; rfl)
            (by rw [o.wr]; rfl) (o.get .x4) (VG.Proof.MlDsa.AArch64.Message.signSaves_vals o) (by decide)) fun t hc => ⟨h8, a', o.mem, hc⟩
        exact ⟨en x a hxy.1 fa, en y b hxy.2.1 fb⟩
    refine RelCT.seq (RelCT.mono hent (fun a b ⟨⟨x, y, hxy, f₁, f₂⟩, hc⟩ => ⟨x, y, hxy, ⟨f₁, hc⟩, ⟨f₂, by
      rw [f₂.2, ← (VG.Proof.MlDsa.AArch64.Message.sPub_of hxy.2.2).x4, ← f₁.2]; exact hc⟩⟩) fun _ _ h => h) (RelCT.seq (RelCT.mono (VG.Proof.MlDsa.AArch64.Message.signBody_tr v hS hp) (fun a b ⟨x, y, hxy, ⟨h8x, a', ma, ca⟩,
      ⟨h8y, b', mb, cb⟩⟩ => ?_) fun _ _ h => h) (AArch64.taintRel [.x28] (fun a b h => ⟨h.2, fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact h.1⟩) VG.Proof.MlDsa.AArch64.Message.leave_taint))
    have hx := VG.Proof.MlDsa.AArch64.Message.sPre_of hxy.1
    have hy := VG.Proof.MlDsa.AArch64.Message.sPre_of hxy.2.1
    have hpub := VG.Proof.MlDsa.AArch64.Message.sPub_of hxy.2.2
    have e := VG.Proof.MlDsa.AArch64.Message.slay_eq hx hy hpub
    refine ⟨VG.Proof.MlDsa.AArch64.Message.slay p x, a'.gpr, b'.gpr, a'.v, b'.v, a'.mem, b'.mem, VG.Proof.MlDsa.AArch64.Message.slay_ok hp hx h8x, ?_, ca, e ▸ cb,
      ⟨x, hx, h8x, rfl, ma.symm⟩, ⟨y, hy, h8y, e.symm, mb.symm⟩⟩
    have lk := hpub.leak
    rw [← hpub.x0, ← hpub.x1, ← hpub.x2, ← hpub.x3, ← hpub.x4, ← hpub.x5] at lk
    unfold VG.Proof.MlDsa.AArch64.Message.signI
    rw [ma, mb]
    exact lk

end

end VG.Proof.MlDsa.AArch64.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Message.VerifyCT`. -/
section

/-!
# ML-DSA on AArch64, `verify_message`: constant time

Untrusted: everything here is checked by Lean. Two runs from states that
satisfy the contract and agree on its public data, which include `pk`, the
message, the context string and the signature (`verifyI`), leak the same:
the branch on `ctx_len`, the entry and the exit depend only on the pointers
and the lengths; the hashing leaks only the layout (`trHash_tr`,
`muHash_tr`); and the call of the verification function on `μ` leaks only
`pk`, `μ` and `sig`, which are the same in both runs (`verifyCall_tr`).
-/

namespace VG.Proof.MlDsa.AArch64.Message

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.AArch64 (Only)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable {p : Params}

/-- The inputs of a run, with the memory `m`. -/
abbrev vIn (p : Params) (L : VG.Proof.MlDsa.AArch64.Message.Lay) (m : Mem) : List Byte :=
  bytesAt m L.key p.pkLen ++ bytesAt m L.msg L.len.toNat ++ bytesAt m L.ctx L.ctxLen.toNat ++
    bytesAt m L.sig p.sigLen

/-- What the contract says two runs agree on, beyond the pointers and lengths. -/
def verifyI (p : Params) (L : VG.Proof.MlDsa.AArch64.Message.Lay) (m₁ m₂ : Mem) : Prop := leakBytes (VG.Proof.MlDsa.AArch64.Message.vIn p L m₁) = leakBytes (VG.Proof.MlDsa.AArch64.Message.vIn p L m₂)

theorem verifyI_eq {L : VG.Proof.MlDsa.AArch64.Message.Lay} {m₁ m₂ : Mem} (h : VG.Proof.MlDsa.AArch64.Message.verifyI p L m₁ m₂) :
    bytesAt m₁ L.key p.pkLen = bytesAt m₂ L.key p.pkLen ∧
      bytesAt m₁ L.msg L.len.toNat = bytesAt m₂ L.msg L.len.toNat ∧
      bytesAt m₁ L.ctx L.ctxLen.toNat = bytesAt m₂ L.ctx L.ctxLen.toNat ∧
      bytesAt m₁ L.sig p.sigLen = bytesAt m₂ L.sig p.sigLen :=
  leak4 (by simp only [Proof.MlKem.bytesAt_length]) (by simp only [Proof.MlKem.bytesAt_length])
    (by simp only [Proof.MlKem.bytesAt_length]) h

/-- The layout is that of a run of `verify_message` from a state with the
memory `m`, past the branch on `ctx_len`. -/
def VOk (p : Params) (L : VG.Proof.MlDsa.AArch64.Message.Lay) (m : Mem) : Prop :=
  ∃ σ, VG.Proof.MlDsa.AArch64.Message.VPre p σ ∧ (σ.gpr .x4).toNat < 256 ∧ VG.Proof.MlDsa.AArch64.Message.vlay p σ = L ∧ σ.mem = m

/-- `tr` at `X + 840`. -/
def TrOk (p : Params) (L : VG.Proof.MlDsa.AArch64.Message.Lay) (m : Mem) (t : State) : Prop :=
  bytesAt t.mem L.MU 64 = H (bytesAt m L.key p.pkLen) 64

/-- `μ` at `X + 840`. -/
def VMuOk (p : Params) (L : VG.Proof.MlDsa.AArch64.Message.Lay) (m : Mem) (t : State) : Prop :=
  bytesAt t.mem L.MU 64 = H (H (bytesAt m L.key p.pkLen) 64 ++ VG.Proof.MlDsa.AArch64.Message.hdrBytes L ++
    bytesAt m L.ctx L.ctxLen.toNat ++ bytesAt m L.msg L.len.toNat) 64

/-- What a layout of `verify_message` says of `sig` and `scratch`. -/
structure VFacts (p : Params) (L : VG.Proof.MlDsa.AArch64.Message.Lay) : Prop where
  key : L.keyLen = p.pkLen
  xSig : L.XS.Disjoint ⟨L.sig, p.sigLen⟩
  kSig : L.STK.Disjoint ⟨L.sig, p.sigLen⟩
  nSig : L.sig.toNat + p.sigLen ≤ 2 ^ 64
  inSig : (⟨L.sig, p.sigLen⟩ : Region) ∈ L.rd
  inScr : ∃ R ∈ L.wr, Within ⟨L.scr, VG.Proof.MlDsa.AArch64.Message.sScr p⟩ R
  inMu : ∃ R ∈ L.wr, Within ⟨L.MU, 64⟩ R

theorem VOk.facts {L : VG.Proof.MlDsa.AArch64.Message.Lay} {m : Mem} (h : VG.Proof.MlDsa.AArch64.Message.VOk p L m) : VG.Proof.MlDsa.AArch64.Message.VFacts p L := by
  obtain ⟨σ, hσ, _, rfl, -⟩ := h
  exact ⟨rfl, hσ.sigScr.symm.sub_left (VG.Proof.MlDsa.AArch64.Message.vlay_X p σ).sub, hσ.stkSig, hσ.nSig, by simp [VG.Proof.MlDsa.AArch64.Message.vlay, hσ.rd],
    ⟨⟨σ.gpr .x6, VG.Proof.MlDsa.AArch64.Message.mScrLen p⟩, by simp [VG.Proof.MlDsa.AArch64.Message.vlay, hσ.wr], within_base _ (by rw [VG.Proof.MlDsa.AArch64.Message.mScr_eq]; simp only [VG.Proof.MlDsa.AArch64.Message.sScr, oE]; omega)⟩,
    ⟨⟨σ.gpr .x6, VG.Proof.MlDsa.AArch64.Message.mScrLen p⟩, by simp [VG.Proof.MlDsa.AArch64.Message.vlay, hσ.wr], VG.Proof.MlDsa.AArch64.Message.mu_withinV p σ⟩⟩

/-- Two runs of the call of the verification function on `μ`. -/
theorem verifyCall_tr {n : String} {c : Prog isa} (hV : VG.Proof.MlDsa.AArch64.Message.VerifyFn p c) (hp : p ∈ VG.Proof.MlDsa.AArch64.Message.params) :
    RelCT isa (VG.Proof.MlDsa.AArch64.Message.Two (VG.Proof.MlDsa.AArch64.Message.verifyI p) fun L m t => VG.Proof.MlDsa.AArch64.Message.VOk p L m ∧ VG.Proof.MlDsa.AArch64.Message.VMuOk p L m t) (callA n c VG.Proof.MlDsa.AArch64.Message.verifyArgs)
      fun _ _ => True := by
  refine VG.Proof.MlDsa.AArch64.Message.call_tr (by decide) hV.ver.1 hV.ver.2.1
    (fun L => [⟨L.key, p.pkLen⟩, ⟨L.MU, 64⟩, ⟨L.sig, p.sigLen⟩]) (fun L => [⟨L.scr, VG.Proof.MlDsa.AArch64.Message.sScr p⟩])
    (fun L g v m₀ t t1 hL hc hφ hm => ?_) (fun L g₁ g₂ v₁ v₂ m₁ m₂ a b a1 b1 hL hi c₁ c₂ φ₁ φ₂ f₁ f₂ => ?_)
    (fun L g v m₀ t hL hc hφ => ?_)
  · obtain ⟨⟨σ, hσ, h8, rfl, -⟩, -⟩ := hφ
    exact VG.Proof.MlDsa.AArch64.Message.verifyK_pre hp hσ h8 hc hm.1 (hm.2.sp.trans hc.sp)
  · obtain ⟨σ, hσ, h8, rfl, -⟩ := φ₁.1
    have F := φ₁.1.facts
    obtain ⟨x0, x1, x2, x3⟩ := VG.Proof.MlDsa.AArch64.Message.verifyRegs_of c₁ f₁.1
    obtain ⟨y0, y1, y2, y3⟩ := VG.Proof.MlDsa.AArch64.Message.verifyRegs_of c₂ f₂.1
    have ek : ∀ {g v m₀} {a a1 : State}, VG.Proof.MlDsa.AArch64.Message.Ctx (VG.Proof.MlDsa.AArch64.Message.vlay p σ) g v m₀ a → VG.Proof.MlDsa.AArch64.Message.Moved VG.Proof.MlDsa.AArch64.Message.verifyArgs a a1 →
        bytesAt a1.mem (σ.gpr .x0) p.pkLen = bytesAt m₀ (σ.gpr .x0) p.pkLen := fun c f => by
      rw [f.2.mem]
      exact c.bytesAt_eq (p := (VG.Proof.MlDsa.AArch64.Message.vlay p σ).key) hL.xKey hL.kKey (by have := hL.nKey; simp only [VG.Proof.MlDsa.AArch64.Message.vlay] at this ⊢; omega)
    have es : ∀ {g v m₀} {a a1 : State}, VG.Proof.MlDsa.AArch64.Message.Ctx (VG.Proof.MlDsa.AArch64.Message.vlay p σ) g v m₀ a → VG.Proof.MlDsa.AArch64.Message.Moved VG.Proof.MlDsa.AArch64.Message.verifyArgs a a1 →
        bytesAt a1.mem (σ.gpr .x5) p.sigLen = bytesAt m₀ (σ.gpr .x5) p.sigLen := fun c f => by
      rw [f.2.mem]
      exact c.bytesAt_eq (p := (VG.Proof.MlDsa.AArch64.Message.vlay p σ).sig) F.xSig F.kSig (by have := F.nSig; omega)
    have eμ : ∀ {a a1 : State}, VG.Proof.MlDsa.AArch64.Message.Moved VG.Proof.MlDsa.AArch64.Message.verifyArgs a a1 →
        bytesAt a1.mem (VG.Proof.MlDsa.AArch64.Message.vlay p σ).MU 64 = bytesAt a.mem (VG.Proof.MlDsa.AArch64.Message.vlay p σ).MU 64 := fun f => by rw [f.2.mem]
    obtain ⟨ik, im, ic, is⟩ := VG.Proof.MlDsa.AArch64.Message.verifyI_eq hi
    sig_pub [verifyContract, verifySig, AArch64.abi, AArch64.argRegs, List.range, List.range.loop]
    simp only [x0, x1, x2, x3, y0, y1, y2, y3, and_true]
    refine ⟨by rw [f₁.2.sp, f₂.2.sp, c₁.sp, c₂.sp], ?_⟩
    rw [ek c₁ f₁, ek c₂ f₂, es c₁ f₁, es c₂ f₂, eμ f₁, eμ f₂, φ₁.2, φ₂.2]
    have ik' : bytesAt m₁ (σ.gpr .x0) p.pkLen = bytesAt m₂ (σ.gpr .x0) p.pkLen := ik
    have is' : bytesAt m₁ (σ.gpr .x5) p.sigLen = bytesAt m₂ (σ.gpr .x5) p.sigLen := is
    rw [ik, im, ic, ik', is']
  · have F := hφ.1.facts
    refine ⟨fun r hr => ?_, fun r hr => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_append_left _ (F.key ▸ hL.inKey), within_self _⟩
      · obtain ⟨R, hR, hw⟩ := F.inMu; exact ⟨R, by simp [hR], hw⟩
      · exact ⟨_, List.mem_append_left _ F.inSig, within_self _⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact F.inScr

/-- The public data of the contract, spelled out. -/
structure VPub (p : Params) (s₁ s₂ : State) : Prop where
  sp : s₁.sp = s₂.sp
  leak : leakBytes (bytesAt s₁.mem (s₁.gpr .x0) p.pkLen ++ bytesAt s₁.mem (s₁.gpr .x1) (s₁.gpr .x2).toNat ++
      bytesAt s₁.mem (s₁.gpr .x3) (s₁.gpr .x4).toNat ++ bytesAt s₁.mem (s₁.gpr .x5) p.sigLen) =
    leakBytes (bytesAt s₂.mem (s₂.gpr .x0) p.pkLen ++ bytesAt s₂.mem (s₂.gpr .x1) (s₂.gpr .x2).toNat ++
      bytesAt s₂.mem (s₂.gpr .x3) (s₂.gpr .x4).toNat ++ bytesAt s₂.mem (s₂.gpr .x5) p.sigLen)
  x0 : s₁.gpr .x0 = s₂.gpr .x0
  x1 : s₁.gpr .x1 = s₂.gpr .x1
  x2 : s₁.gpr .x2 = s₂.gpr .x2
  x3 : s₁.gpr .x3 = s₂.gpr .x3
  x4 : s₁.gpr .x4 = s₂.gpr .x4
  x5 : s₁.gpr .x5 = s₂.gpr .x5
  x6 : s₁.gpr .x6 = s₂.gpr .x6

theorem vPub_of {s₁ s₂ : State} (h : (verifyMessageContract p AArch64.abi 16).pub s₁ s₂) : VG.Proof.MlDsa.AArch64.Message.VPub p s₁ s₂ := by
  sig_pub [verifyMessageContract, verifyMessageSig, AArch64.abi, AArch64.argRegs, List.range, List.range.loop] at h
  obtain ⟨a, b, c, d, e, f, g, h, i⟩ := h
  exact ⟨a, b, c, d, e, f, g, h, i⟩

/-- Two runs from states agreeing on the public data have the same layout. -/
theorem vlay_eq {s₁ s₂ : State} (h₁ : VG.Proof.MlDsa.AArch64.Message.VPre p s₁) (h₂ : VG.Proof.MlDsa.AArch64.Message.VPre p s₂) (h : VG.Proof.MlDsa.AArch64.Message.VPub p s₁ s₂) : VG.Proof.MlDsa.AArch64.Message.vlay p s₁ = VG.Proof.MlDsa.AArch64.Message.vlay p s₂ := by
  have e1 : s₁.rd = s₂.rd := by
    rw [h₁.rd, h₂.rd]; simp only [VG.Proof.MlDsa.AArch64.Message.rKey, VG.Proof.MlDsa.AArch64.Message.rMsg, VG.Proof.MlDsa.AArch64.Message.rCtx, h.x0, h.x1, h.x2, h.x3, h.x4, h.x5]
  have e2 : s₁.wr = s₂.wr := by
    rw [h₁.wr, h₂.wr]; simp only [h.x6]
  simp only [VG.Proof.MlDsa.AArch64.Message.vlay, h.sp, h.x0, h.x1, h.x2, h.x3, h.x4, h.x5, h.x6, e1, e2]

/-- The body, between the entry and the exit: its runs end with the same
`x28` and stack pointer. -/
theorem verifyBody_tr (v : Proof.Sha3.AArch64.Permutation) {n : String} {c : Prog isa} (hV : VG.Proof.MlDsa.AArch64.Message.VerifyFn p c)
    (hp : p ∈ VG.Proof.MlDsa.AArch64.Message.params) :
    RelCT isa (VG.Proof.MlDsa.AArch64.Message.Two (VG.Proof.MlDsa.AArch64.Message.verifyI p) fun L m _ => VG.Proof.MlDsa.AArch64.Message.VOk p L m)
      (.seq (trHash v.callee p) (.seq (muHash v.callee (.off oMU)) (callA n c VG.Proof.MlDsa.AArch64.Message.verifyArgs)))
      fun a b => a.gpr .x28 = b.gpr .x28 ∧ a.sp = b.sp := by
  have th := VG.Proof.MlDsa.AArch64.Message.trHash_tr v (I := VG.Proof.MlDsa.AArch64.Message.verifyI p) (Φ := fun L m _ => VG.Proof.MlDsa.AArch64.Message.VOk p L m) (VG.Proof.MlDsa.AArch64.Message.pkLen_ge hp).2
    (fun _ _ _ h => h.facts.key)
  have th' := VG.Proof.MlDsa.AArch64.Message.two_wp (I := VG.Proof.MlDsa.AArch64.Message.verifyI p) (Φ := fun L m _ => VG.Proof.MlDsa.AArch64.Message.VOk p L m) (Ψ := fun L m t => VG.Proof.MlDsa.AArch64.Message.VOk p L m ∧ VG.Proof.MlDsa.AArch64.Message.TrOk p L m t) th
    fun L g vv m₀ t hL hc hφ => WP.mono (VG.Proof.MlDsa.AArch64.Message.trHash_ok v hL hφ.facts.key hc) fun t' ⟨hc', htr⟩ =>
      ⟨hc', hφ, by unfold VG.Proof.MlDsa.AArch64.Message.TrOk; rw [htr, hφ.facts.key]⟩
  have side : ∀ L : VG.Proof.MlDsa.AArch64.Message.Lay, L.Ok → (∃ R ∈ L.rd ++ L.wr, Within ⟨L.MU, 64⟩ R) ∧
      Region.Disjoint ⟨L.MU, 64⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨L.MU, 64⟩ ⟨L.KS, 640⟩ ∧
      L.STK.Disjoint ⟨L.MU, 64⟩ := fun L hL => by
    obtain ⟨R, hR, hw⟩ := hL.covX (e := 840) (k := 64) (by omega)
    exact ⟨⟨R, by simp [hR], hw⟩, st_mu.symm, VG.Proof.MlDsa.AArch64.Message.mu_ks, VG.Proof.MlDsa.AArch64.Message.k_mu hL⟩
  have mh := VG.Proof.MlDsa.AArch64.Message.muHash_tr v (I := VG.Proof.MlDsa.AArch64.Message.verifyI p) (Φ := fun L m t => VG.Proof.MlDsa.AArch64.Message.VOk p L m ∧ VG.Proof.MlDsa.AArch64.Message.TrOk p L m t) (tr := .off oMU)
    (by decide) rfl (fun L => L.MU) (fun L g vv m t hc => hc.off oMU) side
  have mh' := VG.Proof.MlDsa.AArch64.Message.two_wp (I := VG.Proof.MlDsa.AArch64.Message.verifyI p) (Φ := fun L m t => VG.Proof.MlDsa.AArch64.Message.VOk p L m ∧ VG.Proof.MlDsa.AArch64.Message.TrOk p L m t)
    (Ψ := fun L m t => VG.Proof.MlDsa.AArch64.Message.VOk p L m ∧ VG.Proof.MlDsa.AArch64.Message.VMuOk p L m t) mh fun L g vv m₀ t hL hc hφ => by
      obtain ⟨a, b, c, d⟩ := side L hL
      refine WP.mono (VG.Proof.MlDsa.AArch64.Message.muHash_ok v hL hc (tr := .off oMU) (by decide) rfl (fun t' hc' => hc'.off oMU) a b c d)
        fun t' ⟨hc', hμ⟩ => ⟨hc', hφ.1, ?_⟩
      unfold VG.Proof.MlDsa.AArch64.Message.VMuOk
      rw [hμ]
      have h2 := hφ.2
      unfold VG.Proof.MlDsa.AArch64.Message.TrOk at h2
      rw [show L.X + BitVec.ofNat 64 oMU = L.MU from rfl, h2]
  refine RelCT.postDep (F := fun x x' => x'.gpr .x28 = x.gpr .x28 ∧ x'.sp = x.sp)
    (th'.seq (mh'.seq (VG.Proof.MlDsa.AArch64.Message.verifyCall_tr hV hp))) (fun x y hxy => ?_) fun x y x' y' hxy f₁ f₂ => ?_
  · have run : ∀ {L : VG.Proof.MlDsa.AArch64.Message.Lay} {g vv m₀} {t : State}, L.Ok → VG.Proof.MlDsa.AArch64.Message.Ctx L g vv m₀ t → VG.Proof.MlDsa.AArch64.Message.VOk p L m₀ →
        WP isa (.seq (trHash v.callee p) (.seq (muHash v.callee (.off oMU)) (callA n c VG.Proof.MlDsa.AArch64.Message.verifyArgs))) t
          fun t' => t'.gpr .x28 = t.gpr .x28 ∧ t'.sp = t.sp := fun hL hc hφ => by
      obtain ⟨σ, hσ, h8, rfl, -⟩ := hφ
      obtain ⟨a, b, c, d⟩ := side _ hL
      refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Message.trHash_ok v hL rfl hc) fun t₁ ⟨hc₁, _⟩ => ?_)
      refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Message.muHash_ok v hL hc₁ (tr := .off oMU) (by decide) rfl
        (fun t' hc' => hc'.off oMU) a b c d) fun t₂ ⟨hc₂, _⟩ => ?_)
      exact WP.mono (VG.Proof.MlDsa.AArch64.Message.verifyCall_ok hV hp hσ h8 hc₂) fun s' ⟨hf, _⟩ =>
        ⟨hf.x28.trans hc.x28.symm, hf.sp.trans hc.sp.symm⟩
    obtain ⟨L, _, _, _, _, _, _, hL, _, c₁, c₂, φ₁, φ₂⟩ := hxy
    exact ⟨run hL c₁ φ₁, run hL c₂ φ₂⟩
  · obtain ⟨L, _, _, _, _, _, _, _, _, c₁, c₂, _, _⟩ := hxy
    exact ⟨by rw [f₁.1, f₂.1, c₁.x28, c₂.x28], by rw [f₁.2, f₂.2, c₁.sp, c₂.sp]⟩

/-- The entry states of two runs: the precondition and the public data. -/
abbrev VP2 (p : Params) (x y : State) : Prop :=
  (verifyMessageContract p AArch64.abi 16).pre x ∧ (verifyMessageContract p AArch64.abi 16).pre y ∧
    (verifyMessageContract p AArch64.abi 16).pub x y

theorem enterV_taint (p : Params) :
    (taint.check (AArch64.Taint.ofRegs [.x6]) (.block (enter .x6 p verifySaves)) (.block [])).isSome = true := by
  rfl

theorem verifyMessage_ct (v : Proof.Sha3.AArch64.Permutation) {n : String} {c : Prog isa} (hV : VG.Proof.MlDsa.AArch64.Message.VerifyFn p c)
    (hp : p ∈ VG.Proof.MlDsa.AArch64.Message.params) :
    ConstantTime isa (verifyMessageContract p AArch64.abi 16).pre (verifyMessageContract p AArch64.abi 16).pub
      (verifyMessage v.callee n c p) := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  have e0 : (fun s₁ s₂ => (verifyMessageContract p AArch64.abi 16).pre s₁ ∧
      (verifyMessageContract p AArch64.abi 16).pre s₂ ∧ (verifyMessageContract p AArch64.abi 16).pub s₁ s₂) =
      VG.Proof.MlDsa.AArch64.Message.Ghost (VG.Proof.MlDsa.AArch64.Message.VP2 p) (fun x a => a = x) := by
    funext a b; apply propext
    exact ⟨fun h => ⟨a, b, h, rfl, rfl⟩, fun ⟨_, _, h, e₁, e₂⟩ => e₁ ▸ e₂ ▸ h⟩
  rw [e0]
  unfold verifyMessage top
  have hlsr := VG.Proof.MlDsa.AArch64.Message.ghost_step (P := VG.Proof.MlDsa.AArch64.Message.VP2 p) (A := fun x a => a = x) (B := VG.Proof.MlDsa.AArch64.Message.ALsr) (c := .block [.lsr .x .x9 .x4 8])
    (AArch64.taintRel [] (fun a b ⟨x, y, hxy, e₁, e₂⟩ => by
      subst e₁ e₂; exact ⟨(VG.Proof.MlDsa.AArch64.Message.vPub_of hxy.2.2).sp, by simp⟩) VG.Proof.MlDsa.AArch64.Message.lsr_taint)
    fun x y a b _ e₁ e₂ => by subst e₁ e₂; exact ⟨VG.Proof.MlDsa.AArch64.Message.lsr_ok _, VG.Proof.MlDsa.AArch64.Message.lsr_ok _⟩
  refine RelCT.seq hlsr (RelCT.ite (fun a b ⟨x, y, hxy, f₁, f₂⟩ => by
    rw [f₁.2, f₂.2, (VG.Proof.MlDsa.AArch64.Message.vPub_of hxy.2.2).x4]) ?_ ?_)
  · exact AArch64.taintRel [] (fun a b ⟨⟨x, y, hxy, f₁, f₂⟩, _⟩ =>
      ⟨by rw [f₁.1.sp, f₂.1.sp]; exact (VG.Proof.MlDsa.AArch64.Message.vPub_of hxy.2.2).sp, by simp⟩) VG.Proof.MlDsa.AArch64.Message.movz2_taint
  · let A : State → State → Prop := fun x a => VG.Proof.MlDsa.AArch64.Message.ALsr x a ∧ isa.eval (.nonzero .x .x9) a = some false
    let B : State → State → Prop := fun x t => (x.gpr .x4).toNat < 256 ∧
      ∃ a : State, a.mem = x.mem ∧ VG.Proof.MlDsa.AArch64.Message.Ctx (VG.Proof.MlDsa.AArch64.Message.vlay p x) a.gpr a.v a.mem t
    have hent := VG.Proof.MlDsa.AArch64.Message.ghost_step (P := VG.Proof.MlDsa.AArch64.Message.VP2 p) (A := A) (B := B) (c := .block (enter .x6 p verifySaves))
      (AArch64.taintRel [.x6] (fun a b ⟨x, y, hxy, f₁, f₂⟩ => ⟨by rw [f₁.1.1.sp, f₂.1.1.sp]; exact (VG.Proof.MlDsa.AArch64.Message.vPub_of hxy.2.2).sp,
        fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          rw [f₁.1.1.get .x6, f₂.1.1.get .x6]; exact (VG.Proof.MlDsa.AArch64.Message.vPub_of hxy.2.2).x6⟩) (VG.Proof.MlDsa.AArch64.Message.enterV_taint p))
      fun x y a b hxy fa fb => by
        have en : ∀ (x' a' : State), (verifyMessageContract p AArch64.abi 16).pre x' → A x' a' →
            WP isa (.block (enter .x6 p verifySaves)) a' (B x') := fun x' a' hx ⟨⟨o, e⟩, ef⟩ => by
          have h8 : (x'.gpr .x4).toNat < 256 := by
            rw [e] at ef; simpa using ef
          have hL := VG.Proof.MlDsa.AArch64.Message.vlay_ok hp (VG.Proof.MlDsa.AArch64.Message.vPre_of hx) h8
          exact WP.mono (VG.Proof.MlDsa.AArch64.Message.enter_ok hL rfl (by decide) rfl (o.get .x6) (by rw [o.sp]; rfl) (by rw [o.rd]; rfl)
            (by rw [o.wr]; rfl) (o.get .x4) (VG.Proof.MlDsa.AArch64.Message.verifySaves_vals o) (by decide)) fun t hc => ⟨h8, a', o.mem, hc⟩
        exact ⟨en x a hxy.1 fa, en y b hxy.2.1 fb⟩
    refine RelCT.seq (RelCT.mono hent (fun a b ⟨⟨x, y, hxy, f₁, f₂⟩, hc⟩ => ⟨x, y, hxy, ⟨f₁, hc⟩, ⟨f₂, by
      rw [f₂.2, ← (VG.Proof.MlDsa.AArch64.Message.vPub_of hxy.2.2).x4, ← f₁.2]; exact hc⟩⟩) fun _ _ h => h) (RelCT.seq
      (RelCT.mono (VG.Proof.MlDsa.AArch64.Message.verifyBody_tr v hV hp) (fun a b ⟨x, y, hxy, ⟨h8x, a', ma, ca⟩, ⟨h8y, b', mb, cb⟩⟩ => ?_)
        fun _ _ h => h) (AArch64.taintRel [.x28] (fun a b h => ⟨h.2, fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact h.1⟩) VG.Proof.MlDsa.AArch64.Message.leave_taint))
    have hx := VG.Proof.MlDsa.AArch64.Message.vPre_of hxy.1
    have hy := VG.Proof.MlDsa.AArch64.Message.vPre_of hxy.2.1
    have hpub := VG.Proof.MlDsa.AArch64.Message.vPub_of hxy.2.2
    have e := VG.Proof.MlDsa.AArch64.Message.vlay_eq hx hy hpub
    refine ⟨VG.Proof.MlDsa.AArch64.Message.vlay p x, a'.gpr, b'.gpr, a'.v, b'.v, a'.mem, b'.mem, VG.Proof.MlDsa.AArch64.Message.vlay_ok hp hx h8x, ?_, ca, e ▸ cb,
      ⟨x, hx, h8x, rfl, ma.symm⟩, ⟨y, hy, h8y, e.symm, mb.symm⟩⟩
    have lk := hpub.leak
    rw [← hpub.x0, ← hpub.x1, ← hpub.x2, ← hpub.x3, ← hpub.x4, ← hpub.x5] at lk
    unfold VG.Proof.MlDsa.AArch64.Message.verifyI
    rw [ma, mb]
    exact lk

end

end VG.Proof.MlDsa.AArch64.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Message.Verified`. -/
section

/-!
# ML-DSA on AArch64, `sign_message` and `verify_message`: verified

Untrusted: everything here is checked by Lean. `signMessage v.callee n c p`
and `verifyMessage v.callee n c p`, for any functions on `μ` `c` they can
call (`SignFn`, `VerifyFn`), are verified against `signMessageContract p
AArch64.abi 16` and `verifyMessageContract p AArch64.abi 16`; the functions
on `μ` with the Keccak permutation of `v` are such functions (`signFn`,
`verifyFn`).
-/

namespace VG.Proof.MlDsa.AArch64.Message

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Spec.MlDsa

/-- A state satisfying the precondition of signing. -/
def signSat (p : Params) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x3000 | .x3 => 0x3100 | .x5 => 0x3200 | .x6 => 0x4000 | .x7 => 0x10000
    | _ => 0
  sp := 0x80000
  mem _ := 0
  rd := [⟨0x1000, p.skLen⟩, ⟨0x3000, 0⟩, ⟨0x3100, 0⟩, ⟨0x3200, 32⟩]
  wr := [⟨0x4000, p.sigLen⟩, ⟨0x10000, VG.Proof.MlDsa.AArch64.Message.mScrLen p⟩]

theorem signMessage_sat {p : Params} (hp : p ∈ VG.Proof.MlDsa.AArch64.Message.params) : ∃ s, (signMessageContract p AArch64.abi 16).pre s := by
  simp only [VG.Proof.MlDsa.AArch64.Message.params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · sig_implies_sat [signMessageContract, signMessageSig, AArch64.abi, AArch64.argRegs, List.range,
      List.range.loop] [signSat] using VG.Proof.MlDsa.AArch64.Message.signSat mlDsa44
  · sig_implies_sat [signMessageContract, signMessageSig, AArch64.abi, AArch64.argRegs, List.range,
      List.range.loop] [signSat] using VG.Proof.MlDsa.AArch64.Message.signSat mlDsa65
  · sig_implies_sat [signMessageContract, signMessageSig, AArch64.abi, AArch64.argRegs, List.range,
      List.range.loop] [signSat] using VG.Proof.MlDsa.AArch64.Message.signSat mlDsa87

theorem signMessage_verified (v : Proof.Sha3.AArch64.Permutation) {p : Params} {n : String} {c : Prog isa}
    (hS : VG.Proof.MlDsa.AArch64.Message.SignFn p c) (hp : p ∈ VG.Proof.MlDsa.AArch64.Message.params) :
    Verified AArch64.target (signMessage v.callee n c p) (signMessageContract p AArch64.abi 16) :=
  ⟨fun _ h => let ⟨t, s', he, ha, hq⟩ := VG.Proof.MlDsa.AArch64.Message.signMessage_wp v hS hp h; ⟨t, s', he, ha, hq⟩,
    VG.Proof.MlDsa.AArch64.Message.signMessage_ct v hS hp, VG.Proof.MlDsa.AArch64.Message.signMessage_sat hp⟩

/-- A state satisfying the precondition of verification. -/
def verifySat (p : Params) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x3000 | .x3 => 0x3100 | .x5 => 0x3200 | .x6 => 0x10000
    | _ => 0
  sp := 0x80000
  mem _ := 0
  rd := [⟨0x1000, p.pkLen⟩, ⟨0x3000, 0⟩, ⟨0x3100, 0⟩, ⟨0x3200, p.sigLen⟩]
  wr := [⟨0x10000, VG.Proof.MlDsa.AArch64.Message.mScrLen p⟩]

theorem verifyMessage_sat {p : Params} (hp : p ∈ VG.Proof.MlDsa.AArch64.Message.params) :
    ∃ s, (verifyMessageContract p AArch64.abi 16).pre s := by
  simp only [VG.Proof.MlDsa.AArch64.Message.params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · sig_implies_sat [verifyMessageContract, verifyMessageSig, AArch64.abi, AArch64.argRegs, List.range,
      List.range.loop] [verifySat] using VG.Proof.MlDsa.AArch64.Message.verifySat mlDsa44
  · sig_implies_sat [verifyMessageContract, verifyMessageSig, AArch64.abi, AArch64.argRegs, List.range,
      List.range.loop] [verifySat] using VG.Proof.MlDsa.AArch64.Message.verifySat mlDsa65
  · sig_implies_sat [verifyMessageContract, verifyMessageSig, AArch64.abi, AArch64.argRegs, List.range,
      List.range.loop] [verifySat] using VG.Proof.MlDsa.AArch64.Message.verifySat mlDsa87

theorem verifyMessage_verified (v : Proof.Sha3.AArch64.Permutation) {p : Params} {n : String} {c : Prog isa}
    (hV : VG.Proof.MlDsa.AArch64.Message.VerifyFn p c) (hp : p ∈ VG.Proof.MlDsa.AArch64.Message.params) :
    Verified AArch64.target (verifyMessage v.callee n c p) (verifyMessageContract p AArch64.abi 16) :=
  ⟨fun _ h => let ⟨t, s', he, ha, hq⟩ := VG.Proof.MlDsa.AArch64.Message.verifyMessage_wp v hV hp h; ⟨t, s', he, ha, hq⟩,
    VG.Proof.MlDsa.AArch64.Message.verifyMessage_ct v hV hp, VG.Proof.MlDsa.AArch64.Message.verifyMessage_sat hp⟩

/-! ## The functions on `μ` -/

theorem params3 {p : Params} (hp : p ∈ VG.Proof.MlDsa.AArch64.Message.params) : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87 := by
  simpa only [VG.Proof.MlDsa.AArch64.Message.params, List.mem_cons, List.not_mem_nil, or_false] using hp

/-- `vg_mldsa*_sign`, with the Keccak permutation of `v`. -/
theorem signFn (v : Proof.Sha3.AArch64.Permutation) {p : Params} (hp : p ∈ VG.Proof.MlDsa.AArch64.Message.params) :
    VG.Proof.MlDsa.AArch64.Message.SignFn p (Impl.MlDsa.AArch64.Sign.signWith v.callee (Sign.primsWith v.callee) p) := by
  refine ⟨?_, VG.Proof.MlDsa.AArch64.Message.signWith_dle v p⟩
  rcases VG.Proof.MlDsa.AArch64.Message.params3 hp with rfl | rfl | rfl
  · exact Sign.sign44_verifiedWith' (keccak := v)
  · exact Sign.sign65_verifiedWith' (keccak := v)
  · exact Sign.sign87_verifiedWith' (keccak := v)

/-- `vg_mldsa*_verify`, with the Keccak permutation of `v`. -/
theorem verifyFn (v : Proof.Sha3.AArch64.Permutation) {p : Params} (hp : p ∈ VG.Proof.MlDsa.AArch64.Message.params) :
    VG.Proof.MlDsa.AArch64.Message.VerifyFn p (Impl.MlDsa.AArch64.Verify.verifyWith v.callee (Impl.MlDsa.AArch64.KeyGen.primsWith v.callee) p) := by
  refine ⟨?_, VG.Proof.MlDsa.AArch64.Message.verifyWith_dle v p⟩
  rcases VG.Proof.MlDsa.AArch64.Message.params3 hp with rfl | rfl | rfl
  · exact Verify.verify44_verifiedWith (keccak := v)
  · exact Verify.verify65_verifiedWith (keccak := v)
  · exact Verify.verify87_verifiedWith (keccak := v)

end VG.Proof.MlDsa.AArch64.Message

end
