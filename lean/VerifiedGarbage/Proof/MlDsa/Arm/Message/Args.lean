module

public import VerifiedGarbage.Impl.MlDsa.Arm.Message
public import VerifiedGarbage.Proof.MlDsa.Arm.Message.Layout
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.MlKem.Arm.Common
import VerifiedGarbage.Proof.Sha512.Arm.Rounds
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.Arm.Isa
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Lit

/-! ### `MlDsa.Arm.Message.Step`, which this module and modules that import it used -/

section

/-!
# ML-DSA on ARMv7, `sign_message` and `verify_message_cached`: single instructions

Untrusted: everything here is checked by Lean. Each instruction the
functions run, as a step of a block that leaves its result and changes
nothing else (`Only` the register it writes, or `MemTo` the memory a store
leaves), passed on to the rest of the block.
-/

@[expose] public section

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

theorem refl (rs : List Reg) (s : State) : Only rs s s := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem trans {rs : List Reg} {s₁ s₂ s₃ : State} (h₁ : Only rs s₁ s₂) (h₂ : Only rs s₂ s₃) : Only rs s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    h₂.sp.trans h₁.sp⟩

theorem mono {rs rs' : List Reg} {s s' : State} (h : Only rs s s') (hs : ∀ r ∈ rs, r ∈ rs') : Only rs' s s' :=
  ⟨fun r hr => h.gpr r fun h' => hr (hs r h'), h.mem, h.rd, h.wr, h.sp⟩

theorem get {rs : List Reg} {s s' : State} (h : Only rs s s') (r : Reg) (hr : r ∉ rs := by decide) :
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

theorem only_setReg (s : State) (d : Reg) (x : BitVec 32) : Only [d] s (s.setReg d x) :=
  ⟨fun r hr => by
    simp only [List.mem_singleton] at hr
    simp [State.setReg, hr], rfl, rfl, rfl, rfl⟩

/-- An instruction that writes the register `d`. -/
theorem wp_setReg {i : Instr} {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {x : BitVec 32}
    (he : exec i s = some (s.setReg d x))
    (k : ∀ s1, Only [d] s s1 → s1.gpr d = x → WP isa (.block is) s1 Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨_, he, k _ (only_setReg s d x) (by simp [State.setReg])⟩

theorem wp_ldr {t n : Reg} {off : Nat} {is : List Instr} {s : State} {Q : State → Prop} (ho : off < 4096)
    (h : InRegions (s.rd ++ s.wr) (State.addr (s.gpr n + BitVec.ofNat 32 off)) 4)
    (k : ∀ s1, Only [t] s s1 → s1.gpr t = s.mem.readW (State.addr (s.gpr n + BitVec.ofNat 32 off)) 32 →
      WP isa (.block is) s1 Q) : WP isa (.block (.ldr t n off :: is)) s Q :=
  wp_setReg (exec_ldr ho h) k

theorem wp_ldrSp {t : Reg} {off : Nat} {is : List Instr} {s : State} {Q : State → Prop} (ho : off < 4096)
    (h : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 off)) 4)
    (k : ∀ s1, Only [t] s s1 → s1.gpr t = s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 off)) 32 →
      WP isa (.block is) s1 Q) : WP isa (.block (.ldrSp t off :: is)) s Q :=
  wp_setReg (by simp only [exec, ho, ite_true, State.load32, h, Option.map_some]) k

theorem wp_movw {d : Reg} {v : BitVec 16} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s1, Only [d] s s1 → s1.gpr d = v.setWidth 32 → WP isa (.block is) s1 Q) :
    WP isa (.block (.movw d v :: is)) s Q :=
  wp_setReg rfl k

theorem wp_movt {d : Reg} {v : BitVec 16} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s1, Only [d] s s1 → s1.gpr d = (v ++ (s.gpr d).extractLsb' 0 16 : BitVec 32) → WP isa (.block is) s1 Q) :
    WP isa (.block (.movt d v :: is)) s Q :=
  wp_setReg rfl k

theorem wp_movReg {d r : Reg} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s1, Only [d] s s1 → s1.gpr d = s.gpr r → WP isa (.block is) s1 Q) :
    WP isa (.block (.mov d (.reg r) :: is)) s Q :=
  wp_setReg rfl k

theorem wp_movImm {d : Reg} {v : BitVec 32} {is : List Instr} {s : State} {Q : State → Prop}
    (hv : encodable v = true) (k : ∀ s1, Only [d] s s1 → s1.gpr d = v → WP isa (.block is) s1 Q) :
    WP isa (.block (.mov d (.imm v) :: is)) s Q :=
  wp_setReg (by simp only [exec, Op2.eval, hv, ite_true, Option.map_some]) k

theorem wp_movLsr {d r : Reg} {n : Nat} {is : List Instr} {s : State} {Q : State → Prop} (h1 : 1 ≤ n)
    (h2 : n ≤ 31) (k : ∀ s1, Only [d] s s1 → s1.gpr d = s.gpr r >>> n → WP isa (.block is) s1 Q) :
    WP isa (.block (.mov d (.shifted r .lsr n) :: is)) s Q :=
  wp_setReg (by simp only [exec, Op2.eval, h1, h2, and_self, ite_true, Option.map_some]) k

theorem wp_addReg {d n m : Reg} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s1, Only [d] s s1 → s1.gpr d = s.gpr n + s.gpr m → WP isa (.block is) s1 Q) :
    WP isa (.block (.dp .add d n (.reg m) :: is)) s Q :=
  wp_setReg rfl k

theorem wp_addImm {d n : Reg} {v : BitVec 32} {is : List Instr} {s : State} {Q : State → Prop}
    (hv : encodable v = true) (k : ∀ s1, Only [d] s s1 → s1.gpr d = s.gpr n + v → WP isa (.block is) s1 Q) :
    WP isa (.block (.dp .add d n (.imm v) :: is)) s Q :=
  wp_setReg (by simp only [exec, Op2.eval, hv, ite_true, Option.map_some]) k

theorem wp_str {t n : Reg} {off : Nat} {is : List Instr} {s : State} {Q : State → Prop} (ho : off < 4096)
    (h : InRegions s.wr (State.addr (s.gpr n + BitVec.ofNat 32 off)) 4)
    (k : ∀ s1, MemTo s s1 (s.mem.writeW (State.addr (s.gpr n + BitVec.ofNat 32 off)) (s.gpr t)) →
      WP isa (.block is) s1 Q) : WP isa (.block (.str t n off :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨_, exec_str ho h, k _ ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

theorem wp_strb {t n : Reg} {off : Nat} {is : List Instr} {s : State} {Q : State → Prop} (ho : off < 4096)
    (h : InRegions s.wr (State.addr (s.gpr n + BitVec.ofNat 32 off)) 1)
    (k : ∀ s1, MemTo s s1 (s.mem.writeW (State.addr (s.gpr n + BitVec.ofNat 32 off)) ((s.gpr t).setWidth 8)) →
      WP isa (.block is) s1 Q) : WP isa (.block (.strb t n off :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨{ s with mem := s.mem.writeW (State.addr (s.gpr n + BitVec.ofNat 32 off)) ((s.gpr t).setWidth 8) },
    by simp only [exec, ho, ite_true, State.store8, h], k _ ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

/-- `cmp n, #v`: the flags only, `Z` set if `n = v`. -/
theorem wp_cmpImm {n : Reg} {v : BitVec 32} {is : List Instr} {s : State} {Q : State → Prop}
    (hv : encodable v = true)
    (k : ∀ s1, Only [] s s1 → s1.z = (s.gpr n - v == 0) → WP isa (.block is) s1 Q) :
    WP isa (.block (.cmp n (.imm v) :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨subFlags s (s.gpr n) v, by simp only [exec, Op2.eval, hv, ite_true, Option.map_some],
    k _ ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩ rfl⟩

end VG.Proof.MlDsa.Arm.Message

end

end

/-!
# ML-DSA on ARMv7, `sign_message` and `verify_message_cached`: the moves of a call's arguments

Untrusted: everything here is checked by Lean. Each argument's value
(`Arg.val`): a saved argument (a slot at `r7 + f`), plus an offset, an
offset from `r7`, an immediate, or `r0`. The moves of a list of arguments
into distinct registers but `r7`, with `r0` read only before it is written
(`argsOk`), leave each its value and change nothing else (`setArgs_ok`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Message

open VG VG.Arm VG.Impl.MlDsa.Arm.Message
open VG.Proof.MlDsa.Message

/-- The value of an argument in the state `s`. -/
def _root_.VG.Impl.MlDsa.Arm.Message.Arg.val (s : State) : Arg → BitVec 32
  | .slot f => s.mem.readW (State.addr (s.gpr .r7 + BitVec.ofNat 32 f)) 32
  | .slotOff f o => s.mem.readW (State.addr (s.gpr .r7 + BitVec.ofNat 32 f)) 32 + BitVec.ofNat 32 o
  | .off o => s.gpr .r7 + BitVec.ofNat 32 o
  | .imm v => BitVec.ofNat 32 v
  | .ret => s.gpr .r0

/-- A slot within the 1 KiB, an offset or an immediate the instructions take. -/
def _root_.VG.Impl.MlDsa.Arm.Message.Arg.ok : Arg → Bool
  | .slot f => decide (f + 4 ≤ 1024)
  | .slotOff f o => decide (f + 4 ≤ 1024) && encodable (BitVec.ofNat 32 o)
  | .off o => decide (o < 65536)
  | .imm v => decide (v < 65536)
  | .ret => true

def _root_.VG.Impl.MlDsa.Arm.Message.Arg.isRet : Arg → Bool
  | .ret => true
  | _ => false

/-- The slots of the 1 KiB are readable. -/
abbrev XOk (s : State) : Prop :=
  ∀ f, f + 4 ≤ 1024 → InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r7 + BitVec.ofNat 32 f)) 4

theorem setWidth_ofNat16 {v : Nat} (h : v < 65536) : (BitVec.ofNat 16 v).setWidth 32 = BitVec.ofNat 32 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_using [h]

theorem Arg.mov_ok (d : Reg) (hd : d ≠ .r7) (a : Arg) (ha : a.ok = true) (s : State) (hx : XOk s) :
    WP isa (.block (a.mov d)) s fun s1 => s1.gpr d = a.val s ∧ Only [d] s s1 := by
  cases a with
  | slot f =>
    simp only [Arg.ok, decide_eq_true_eq] at ha
    exact wp_ldr (by omega_using [ha]) (hx f ha) fun s1 o1 e1 => wp_nil ⟨e1, o1⟩
  | slotOff f o =>
    simp only [Arg.ok, Bool.and_eq_true, decide_eq_true_eq] at ha
    refine wp_ldr (by omega) (hx f ha.1) fun s1 o1 e1 => ?_
    refine wp_addImm ha.2 fun s2 o2 e2 => wp_nil ⟨by rw [e2, e1]; rfl, ?_⟩
    exact (o1.trans o2).mono (fun r hr => by simpa using hr)
  | off o =>
    simp only [Arg.ok, decide_eq_true_eq] at ha
    refine wp_movw fun s1 o1 e1 => wp_addReg fun s2 o2 e2 => wp_nil ⟨?_, (o1.trans o2).mono fun r hr => by simpa using hr⟩
    rw [e2, e1, o1.get .r7 (by simpa using hd.symm), setWidth_ofNat16 ha]
    rfl
  | imm v =>
    simp only [Arg.ok, decide_eq_true_eq] at ha
    exact wp_movw fun s1 o1 e1 => wp_nil ⟨by rw [e1, setWidth_ofNat16 ha]; rfl, o1⟩
  | ret => exact wp_movReg fun s1 o1 e1 => wp_nil ⟨e1, o1⟩

/-- Distinct registers but `r7`, each argument fit for its instructions,
and `r0` read only before it is written. -/
def argsOk : List (Reg × Arg) → Bool
  | [] => true
  | (d, a) :: as => a.ok && d != .r7 &&
      as.all (fun da => da.1 != d && (d != .r0 || !da.2.isRet)) && argsOk as

/-- The value of an argument is the same after a move into another register
(not `r7`, and not `r0` if the argument is `r0`). -/
theorem Arg.val_only {d : Reg} (hd : d ≠ .r7) {s s1 : State} (o : Only [d] s s1) (a : Arg)
    (ha : d ≠ .r0 ∨ a.isRet = false) : a.val s1 = a.val s := by
  have h7 : s1.gpr .r7 = s.gpr .r7 := o.gpr _ (by simp only [List.mem_singleton]; exact fun h => hd h.symm)
  cases a with
  | ret =>
    simp only [Arg.isRet, Bool.true_eq_false, or_false] at ha
    simp only [Arg.val]
    exact o.gpr _ (by simp only [List.mem_singleton]; exact fun h => ha h.symm)
  | _ => simp only [Arg.val, h7, o.mem]

theorem XOk.only {d : Reg} (hd : d ≠ .r7) {s s1 : State} (o : Only [d] s s1) (h : XOk s) : XOk s1 := by
  intro f hf
  rw [o.rd, o.wr, o.gpr _ (by simp only [List.mem_singleton]; exact fun h => hd h.symm)]
  exact h f hf

/-- The moves of the arguments `as`. -/
theorem setArgs_ok : ∀ (as : List (Reg × Arg)), argsOk as = true → ∀ s : State, XOk s →
    WP isa (.block (setArgs as)) s fun s1 => (∀ da ∈ as, s1.gpr da.1 = da.2.val s) ∧ Only (as.map (·.1)) s s1
  | [], _, s, _ => wp_nil ⟨fun _ h => by simp at h, Only.refl _ _⟩
  | (d, a) :: as, h, s, hx => by
    simp only [argsOk, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true, Bool.or_eq_true,
      Bool.not_eq_true'] at h
    obtain ⟨⟨⟨ha, hd⟩, hall⟩, hrest⟩ := h
    simp only [setArgs, List.flatMap_cons]
    rw [WP.block_append_iff]
    refine WP.mono (Arg.mov_ok d hd a ha s hx) fun s1 ⟨h1, o1⟩ => ?_
    refine WP.mono (setArgs_ok as hrest s1 (hx.only hd o1)) fun s2 ⟨h2, o2⟩ => ⟨fun da hda => ?_, ?_⟩
    · rcases List.mem_cons.mp hda with rfl | hda
      · rw [o2.gpr _ (fun hm => by
          obtain ⟨x, hx', hx''⟩ := List.mem_map.mp hm
          exact (hall x hx').1 hx''), h1]
      · rw [h2 da hda, Arg.val_only hd o1 da.2 ((hall da hda).2.elim .inl fun h' => .inr h')]
    · exact (o1.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]).trans
        (o2.mono fun r hr => by simp only [List.map_cons]; exact List.mem_cons_of_mem _ hr)

/-! ## In `Ctx` -/

section
variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

theorem Ctx.xOk (hc : Ctx L g m₀ t) (hL : L.Ok) : XOk t := fun f hf => by
  rw [hc.r7, hL.xo (by omega_using [hf])]; exact hc.inX hL hf

theorem Ctx.off (hc : Ctx L g m₀ t) (o : Nat) : (Arg.off o).val t = L.X32 + BitVec.ofNat 32 o := by
  simp only [Arg.val, hc.r7]

/-- The saved argument `j`. -/
theorem Ctx.slotV (hc : Ctx L g m₀ t) (hL : L.Ok) {f j : Nat} (hf : f = 912 + 4 * j) (hj : j < 8) :
    (Arg.slot f).val t = L.vals.getD j 0 := by
  subst hf
  have := hc.slot j hj
  simp only [Arg.val, hc.r7]
  rw [hL.xo (by omega_using [hj]), ← this, show 904 + (8 + 4 * j) = 912 + 4 * j by omega_using []]

end

end VG.Proof.MlDsa.Arm.Message
