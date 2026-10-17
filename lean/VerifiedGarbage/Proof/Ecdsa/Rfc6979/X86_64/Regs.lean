module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Layout
public import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.X86_64.Inline
public import VerifiedGarbage.Proof.Framework.X86_64.Syms
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.X86_64

/-!
# Deterministic ECDSA on x86-64: addresses and registers

The effective addresses of the code's memory operands, the immediates it
sign- or zero-extends, the stack below `rsp` the calls use, and the bytes of
a region a frame of writes misses.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64

theorem ofInt_nat (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toInt_eq; simp

theorem add_ofNat_zero (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

theorem ea_stk (t : State) (d : Nat) : t.ea (stk d) = t.gpr .rsp + BitVec.ofNat 64 d := by
  show t.gpr .rsp + BitVec.ofInt 64 (d : Int) = _
  rw [ofInt_nat]

theorem ea_at (t : State) (r : Reg) (d : Nat) : t.ea (at_ r d) = t.gpr r + BitVec.ofNat 64 d := by
  show t.gpr r + BitVec.ofInt 64 (d : Int) = _
  rw [ofInt_nat]

theorem sx32 {n : Nat} (h : n < 2 ^ 31) : (BitVec.ofNat 32 n).signExtend 64 = BitVec.ofNat 64 n := by
  have hm : (BitVec.ofNat 32 n).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem zx32 {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- The 32 bytes below the frame, which the calls use. -/
theorem below32 {dn : Nat} (L : Lay dn) : below (L.B + BitVec.ofNat 64 24) 32 = L.CALLS := by
  show (⟨L.B + BitVec.ofNat 64 24 - BitVec.ofNat 64 32, 32⟩ : Region) = _
  rw [L.shift, show L.A + BitVec.ofNat 64 (8 + 24) - BitVec.ofNat 64 32 = L.A from BitVec.add_sub_cancel _ _]

/-- Callee-saved registers, through writes of others. -/
macro "cs_tac" : tactic => `(tactic| plain_simp_names (
                   intro r hr
                   revert hr
                   simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false]
                   rintro (h | h | h | h | h | h | h) <;> subst h <;>
                     simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, reduceCtorEq, ite_false]))

/-- A fact `simp` has reduced to `True`, or an equation of definitionally equal sides. -/
macro "triv" : tactic => `(tactic| first | trivial | rfl)

theorem ne_cs {r d : Reg} (hr : r ∈ calleeSaved) (hd : d ∉ calleeSaved) : r ≠ d :=
  fun e => hd (e ▸ hr)

/-- The bytes of a region a frame of writes misses. -/
theorem bytesAt_frame {ws : List Region} {m m' : Mem} (hf : Frame ws m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ ws, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) :
    Spec.Sha256.bytesAt m' p n = Spec.Sha256.bytesAt m p n := by
  simp only [Spec.Sha256.bytesAt]
  exact List.map_congr_left fun i hi => Frame.bytes (R := ⟨p, n⟩) hf hd hn (List.mem_range.mp hi)

/-- Memory that changed only within `ws` changed only within `ws'`, if each
of `ws` lies within one of `ws'`. -/
theorem Frame.widen {ws ws' : List Region} {m m' : Mem} (hf : Frame ws m m')
    (h : ∀ r ∈ ws, ∃ r' ∈ ws', Region.Sub r r') : Frame ws' m m' := hf.sub h

theorem sub_refl (r : Region) : Region.Sub r r := fun _ h => h

theorem _root_.VG.Region.Sub.trans {a b c : Region} (h₁ : Region.Sub a b) (h₂ : Region.Sub b c) : Region.Sub a c :=
  fun x hx => h₂ x (h₁ x hx)

/-- `p + d` does not wrap. -/
theorem toNat_add_of {p : Addr} {d : Nat} (h : p.toNat + d < 2 ^ 64) :
    (p + BitVec.ofNat 64 d).toNat = p.toNat + d := by
  rw [Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt h]

/-- The stack below `rsp` a call uses, within the 32 bytes below the frame. -/
theorem Ctx.below_sub {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {m₀ : Mem} {u : State} (hc : Ctx L g m₀ u) {n : Nat}
    (hn : n ≤ 32) : Region.Sub (below (u.gpr .rsp) n) L.CALLS := by
  rw [hc.rsp, ← below32]; exact VG.X86_64.below_sub hn (by omega)

theorem Lay.Ok.low_scr {dn : Nat} {L : Lay dn} (h : L.Ok) {e k : Nat} (h₂ : e + k ≤ 8192) :
    Region.Disjoint L.CALLS ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
  (h.kc.sub_left (Region.sub_prefix (by omega))).sub_right (Offset.sub_base _ h₂)

/-- Code that writes no callee-saved register keeps them (`hc` is checked
by evaluating the code). -/
theorem WP.keepCs {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q)
    (hc : (instrs c).all (fun i => calleeSaved.all fun r => !Taint.clobbers i r) = true) :
    WP isa c s fun s' => Q s' ∧ ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r := by
  obtain ⟨t, s', he, hq⟩ := h
  refine ⟨t, s', he, hq, fun r hr => Exec.gpr (fun i hi => ?_) he⟩
  have h₁ := List.all_eq_true.mp (List.all_eq_true.mp hc i hi) r hr
  simpa using h₁

/-- Code that keeps the permissions and the callee-saved registers, and
writes only safe regions, keeps `Ctx`. -/
theorem Ctx.of_keep {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {m₀ : Mem} (hL : L.Ok) {t : State}
    (hc : Ctx L g m₀ t) {is : List Instr} {ws : List Region} {Q : State → Prop}
    (h : WP isa (.block is) t fun t' => t'.rd = t.rd ∧ t'.wr = t.wr ∧ Frame ws t.mem t'.mem ∧ Q t')
    (hk : (instrs (.block is : Prog isa)).all (fun i => calleeSaved.all fun r => !Taint.clobbers i r) = true)
    (hs : ∀ r ∈ ws, Safe L r) :
    WP isa (.block is) t fun t' => Ctx L g m₀ t' ∧ Frame ws t.mem t'.mem ∧ Q t' :=
  WP.mono_syms (WP.keepCs h hk) fun _ ⟨⟨hrd, hwr, hf, hq⟩, hcs⟩ hsy =>
    ⟨hc.keep hL hrd hwr (hcs .rsp (by decide)) (fun r hr _ => hcs r hr) hf hs hsy, hf, hq⟩

/-! ## Code that sets one register -/

/-- `u'` is `u` with only the caller-saved register `d` (and the flags)
changed, to `v`. -/
structure Upd {dn : Nat} (L : Lay dn) (g : Reg → BitVec 64) (m₀ : Mem) (u : State) (d : Reg) (v : BitVec 64)
    (u' : State) : Prop where
  ctx : Ctx L g m₀ u'
  mem : u'.mem = u.mem
  val : u'.gpr d = v
  keep : ∀ r, r ≠ d → u'.gpr r = u.gpr r

variable {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {m₀ : Mem}

theorem Ctx.set (hL : L.Ok) {u u' : State} (hc : Ctx L g m₀ u) {d : Reg} (hd : d ∉ calleeSaved)
    (hrd : u'.rd = u.rd) (hwr : u'.wr = u.wr) (hm : u'.mem = u.mem) (hsy : u'.syms = u.syms)
    (hk : ∀ r, r ≠ d → u'.gpr r = u.gpr r) : Ctx L g m₀ u' :=
  hc.regs hL hrd hwr hm hsy fun r hr => hk r (ne_cs hr hd)

/-- `d ← scratch + a`. -/
theorem scr_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {d : Reg} (hd : d ∉ calleeSaved) {a : Nat}
    (ha : a < 2 ^ 31) :
    WP isa (.block (Cfg.scr d a)) u (Upd L g m₀ u d (L.scr + BitVec.ofNat 64 a)) := by
  have h192 := hc.inFr (d := 208) (by omega) (by omega)
  have hrsp : d ≠ .rsp := fun h => hd (h ▸ by decide)
  apply WP.of_runBlock
  simp only [Cfg.scr, fScratch, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    State.load64, ea_stk, hc.rsp, Offset.add_add, Nat.reduceAdd, h192, ite_true, Option.map_some,
    Option.bind_some, RegUpd.gpr_setReg_self, hc.pScr, sx32 ha, Option.some.injEq, exists_eq_left']
  refine ⟨hc.set hL hd rfl rfl rfl rfl fun r hr => ?_, rfl, RegUpd.gpr_setReg_self _ _ _, fun r hr => ?_⟩
  · rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags, RegUpd.gpr_setReg_of_ne _ _ hr]
  · rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags, RegUpd.gpr_setReg_of_ne _ _ hr]

/-- `d ← rsp + o`, an address in the frame. -/
theorem fr_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {d : Reg} (hd : d ∉ calleeSaved) {o : Nat}
    (ho : o < 2 ^ 31) :
    WP isa (.block (Cfg.fr d o)) u (Upd L g m₀ u d (L.B + BitVec.ofNat 64 (24 + o))) := by
  apply WP.of_runBlock
  simp only [Cfg.fr, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    Option.map_some, Option.bind_some, RegUpd.gpr_setReg_self, hc.rsp, sx32 ho, Offset.add_add,
    Option.some.injEq, exists_eq_left']
  refine ⟨hc.set hL hd rfl rfl rfl rfl fun r hr => ?_, rfl, RegUpd.gpr_setReg_self _ _ _, fun r hr => ?_⟩
  · rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags, RegUpd.gpr_setReg_of_ne _ _ hr]
  · rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags, RegUpd.gpr_setReg_of_ne _ _ hr]

/-- `d ← n`, zero-extended from 32 bits. -/
theorem mov32_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {d : Reg} (hd : d ∉ calleeSaved) {n : Nat}
    (hn : n < 2 ^ 32) :
    WP isa (.block [.mov32 d (.imm (BitVec.ofNat 32 n))]) u (Upd L g m₀ u d (BitVec.ofNat 64 n)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32,
    Option.map_some, zx32 hn, Option.some.injEq, exists_eq_left']
  exact ⟨hc.set hL hd rfl rfl rfl rfl fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, RegUpd.gpr_setReg_self _ _ _,
    fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr⟩

/-- `d ← [rsp + o]`, a word of the frame. -/
theorem ld_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {d : Reg} (hd : d ∉ calleeSaved) {o : Nat}
    (ho : o + 8 ≤ 520) :
    WP isa (.block [.mov d (.mem (stk o))]) u
      (Upd L g m₀ u d (u.mem.readW (L.B + BitVec.ofNat 64 (24 + o)) 64)) := by
  have hr := hc.inFr (d := 24 + o) (by omega) (by have := L.he; omega)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, ea_stk, hc.rsp,
    Offset.add_add, hr, ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨hc.set hL hd rfl rfl rfl rfl fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, RegUpd.gpr_setReg_self _ _ _,
    fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr⟩

/-- `d ← d + a`. -/
theorem addImm_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {d : Reg} (hd : d ∉ calleeSaved) {a : Nat}
    (ha : a < 2 ^ 31) :
    WP isa (.block [.alu .add d (.imm (BitVec.ofNat 32 a))]) u (Upd L g m₀ u d (u.gpr d + BitVec.ofNat 64 a)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    Option.bind_some, sx32 ha, Option.some.injEq, exists_eq_left']
  refine ⟨hc.set hL hd rfl rfl rfl rfl fun r hr => ?_, rfl, RegUpd.gpr_setReg_self _ _ _, fun r hr => ?_⟩
  · rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]
  · rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]

/-- `d ← d + [rsp + o]`, a word of the frame. -/
theorem addMem_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {d : Reg} (hd : d ∉ calleeSaved) {o : Nat}
    (ho : o + 8 ≤ 520) :
    WP isa (.block [.alu .add d (.mem (stk o))]) u
      (Upd L g m₀ u d (u.gpr d + u.mem.readW (L.B + BitVec.ofNat 64 (24 + o)) 64)) := by
  have hr := hc.inFr (d := 24 + o) (by omega) (by have := L.he; omega)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, State.load64, ea_stk, hc.rsp,
    Offset.add_add, hr, ite_true, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨hc.set hL hd rfl rfl rfl rfl fun r hr => ?_, rfl, RegUpd.gpr_setReg_self _ _ _, fun r hr => ?_⟩
  · rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]
  · rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]

/-- `d ← d + r`. -/
theorem addReg_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {d : Reg} (hd : d ∉ calleeSaved) (r : Reg) :
    WP isa (.block [.alu .add d (.reg r)]) u (Upd L g m₀ u d (u.gpr d + u.gpr r)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨hc.set hL hd rfl rfl rfl rfl fun r hr => ?_, rfl, RegUpd.gpr_setReg_self _ _ _, fun r hr => ?_⟩
  · rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]
  · rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]

/-- Two pieces of code, each setting one register. -/
theorem upd_append {is js : List Instr} {u : State} {d e : Reg} {v w : BitVec 64}
    (h₁ : WP isa (.block is) u (Upd L g m₀ u d v))
    (h₂ : ∀ u', Ctx L g m₀ u' → WP isa (.block js) u' (Upd L g m₀ u' e w)) {Q : State → Prop}
    (hQ : ∀ u'', Ctx L g m₀ u'' → u''.mem = u.mem → u''.gpr e = w →
      (∀ r, r ≠ e → r ≠ d → u''.gpr r = u.gpr r) → (e ≠ d → u''.gpr d = v) → Q u'') :
    WP isa (.block (is ++ js)) u Q := by
  rw [WP.block_append_iff]
  refine WP.mono h₁ fun u' h => WP.mono (h₂ u' h.ctx) fun u'' h' => hQ u'' h'.ctx (h'.mem.trans h.mem) h'.val
    (fun r hre hrd => (h'.keep r hre).trans (h.keep r hrd)) fun hne => (h'.keep d hne.symm).trans h.val

/-- After the frame's allocation, `hash`, `D`, `B` and the pointers stored into
it establish `Ctx`. -/
theorem init_ctx {cs : List (String × List (BitVec 64))} {I : Spec.Ecdsa.Rfc6979.Instance} {k : Nat}
    {sel hl bs : Nat} {s s' : State} (h : (rfcX86_64 cs I k 552).pre s) (he : Entered s sel hl bs s') :
    WP isa (.block Impl.Ecdsa.Rfc6979.X86_64.Cfg.initFrame) (allocd 520 s')
      (Ctx (lay I.hashLen I.ecdsa.curve.len sel hl bs cs s) s.gpr s.mem) := by
  have ht := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hsp : 544 ≤ (s.gpr .rsp).toNat := by have := h.2.1; omega
  generalize hL : lay I.hashLen I.ecdsa.curve.len sel hl bs cs s = L
  have hB : L.B = s.gpr .rsp - BitVec.ofNat 64 544 := by rw [← hL]; rfl
  have hr : (allocd 520 s').gpr .rsp = L.B + BitVec.ofNat 64 24 := by rw [allocd_rsp, he.rsp, hB, frame_base]
  have hw : (allocd 520 s').wr = ⟨L.B + BitVec.ofNat 64 24, 520⟩ :: s.wr := by
    show (⟨s'.gpr .rsp - _, 520⟩ :: s'.wr : List Region) = _; rw [he.rsp, he.wr, hB, frame_base]
  have hn : (L.B + BitVec.ofNat 64 24).toNat + 520 < 2 ^ 64 := by
    rw [hB, ← frame_base, toNat_sub_ofNat (by omega)]; have := (s.gpr .rsp).isLt; omega
  have hin : ∀ o, o + 8 ≤ 520 → InRegions (allocd 520 s').wr (L.B + BitVec.ofNat 64 (24 + o)) 8 := fun o ho =>
    ⟨_, by rw [hw]; exact List.mem_cons_self .., by
      rw [← Offset.add_add]; exact Offset.contains_base _ ho (by omega)⟩
  apply WP.of_runBlock
  simp only [Impl.Ecdsa.Rfc6979.X86_64.Cfg.initFrame, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.store64, ea_stk, hr, Offset.add_add, Impl.Ecdsa.Rfc6979.X86_64.fSel, Impl.Ecdsa.Rfc6979.X86_64.fHL,
    Impl.Ecdsa.Rfc6979.X86_64.fBS, Impl.Ecdsa.Rfc6979.X86_64.fOut, Impl.Ecdsa.Rfc6979.X86_64.fD,
    Impl.Ecdsa.Rfc6979.X86_64.fDigest, Impl.Ecdsa.Rfc6979.X86_64.fScratch, hin 512 (by omega),
    hin 504 (by omega), hin 496 (by omega), hin 208 (by omega), hin 200 (by omega), hin 192 (by omega),
    hin 184 (by omega), ite_true, Option.some.injEq, exists_eq_left']
  have g : ∀ r, r ≠ .rsp → (allocd 520 s').gpr r = s'.gpr r := fun r hr' => allocd_gpr _ _ hr'
  have hf : Frame [⟨L.B + BitVec.ofNat 64 24, 520⟩] s.mem
      ((((((((allocd 520 s').mem.writeW (L.B + BitVec.ofNat 64 (24 + 512)) ((allocd 520 s').gpr .rax)).writeW (L.B + BitVec.ofNat 64 (24 + 504)) ((allocd 520 s').gpr .r10)).writeW (L.B + BitVec.ofNat 64 (24 + 496)) ((allocd 520 s').gpr .r11)).writeW (L.B + BitVec.ofNat 64 (24 + 208)) ((allocd 520 s').gpr .rdi)).writeW (L.B + BitVec.ofNat 64 (24 + 200)) ((allocd 520 s').gpr .rsi)).writeW (L.B + BitVec.ofNat 64 (24 + 192)) ((allocd 520 s').gpr .rdx)).writeW (L.B + BitVec.ofNat 64 (24 + 184)) ((allocd 520 s').gpr .rcx)) := by
    have c : ∀ o, o + 8 ≤ 520 → (⟨L.B + BitVec.ofNat 64 24, 520⟩ : Region).Contains (L.B + BitVec.ofNat 64 (24 + o)) 8 :=
      fun o ho => by rw [← Offset.add_add]; exact Offset.contains_base _ ho (by omega)
    have m : (allocd 520 s').mem = s.mem := he.mem
    rw [m]
    exact ((((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 512 (by omega))).writeW (List.mem_singleton_self _) _ (c 504 (by omega))).writeW (List.mem_singleton_self _) _ (c 496 (by omega))).writeW (List.mem_singleton_self _) _ (c 208 (by omega))).writeW (List.mem_singleton_self _) _ (c 200 (by omega))).writeW (List.mem_singleton_self _) _ (c 192 (by omega))).writeW (List.mem_singleton_self _) _ (c 184 (by omega)))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show s'.rd = _; rw [he.rd, h.2.2.1, ← hL, lay_tbls]; rfl
  · show (allocd 520 s').wr = _; rw [hw, h.2.2.2.1, ← hL]; rfl
  · exact hr
  · intro r hr' hr''; rw [g r hr'', he.cs r hr']
  all_goals try simp (disch := decide) only [rd_other, Mem.readW_writeW_self64]
  · rw [g _ (by decide), he.rcx, ← hL]; rfl
  · rw [g _ (by decide), he.rdx, ← hL]; rfl
  · rw [g _ (by decide), he.rsi, ← hL]; rfl
  · rw [g _ (by decide), he.rdi, ← hL]; rfl
  · rw [g _ (by decide), he.r11, ← hL]; rfl
  · rw [g _ (by decide), he.r10, ← hL]; rfl
  · rw [g _ (by decide), he.rax, ← hL]; rfl
  · refine hf.sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨L.STK, by simp, L.sub_stk (d := 24) (n := 520) (by rw [← hL]; show _ ≤ 240 + 8 * 38; omega)⟩
  · intro c hc
    have hc : c ∈ cs := by rw [← hL] at hc; exact hc
    show s'.syms c.1 = _
    rw [he.syms, ← hL, lay_sy I.hashLen I.ecdsa.curve.len sel hl bs (cs := cs) s c hc]
  · intro c hc i hi
    have hc : c ∈ cs := by rw [← hL] at hc; exact hc
    rw [← hL, lay_sy I.hashLen I.ecdsa.curve.len sel hl bs (cs := cs) s c hc]
    exact ht c hc i hi
end VG.Proof.Ecdsa.Rfc6979.X86_64
