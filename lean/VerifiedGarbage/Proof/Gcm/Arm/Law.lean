module

public import VerifiedGarbage.Impl.Gcm.Arm
public import VerifiedGarbage.Proof.Gcm.Arm.Ghash
public import VerifiedGarbage.Proof.Gcm.Holes16
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Arm.Inline
public import VerifiedGarbage.Proof.Framework.Arm.RegUpd
public import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Bytes
import VerifiedGarbage.Proof.Framework.Arm.Reduce
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.KernelRfl

/-!
# GHASH on ARMv7 meets its contract

Untrusted: everything here is checked by Lean. What the blocks of
`Impl/Gcm/Arm.lean` compute, as the functions of `Proof/Gcm/Holes16.lean`.
-/

@[expose] public section

namespace VG.Proof.Gcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Gcm.Arm
open VG.Proof.Gcm (Holes16.h3 Holes16.W4)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom mul)

/-! ## What a block keeps

The registers a block does not write, by `dsts`; and the memory outside the
words it stores through `r12`, the scratch buffer's base: both are read off
the code (`okB`, `stOffs`), without running it. -/

/-- The word in slot `k` of the scratch buffer. -/
def sw (s : State) (k : Nat) : BitVec 32 :=
  s.mem.readW (State.addr (s.gpr .r12 + BitVec.ofNat 32 (4 * k))) 32

/-- Every instruction writes only registers among `rs`, and memory only by
`str` through `r12`. -/
def okI (rs : List Reg) (i : Instr) : Bool :=
  (dsts i).all rs.contains &&
    match i with
    | .str _ n _ => n == .r12
    | .strb .. => false
    | _ => true

def okB (rs : List Reg) (is : List Instr) : Bool := is.all (okI rs)

/-- The offsets of the block's stores. -/
def stOffs : List Instr → List Nat
  | [] => []
  | .str _ _ off :: is => off :: stOffs is
  | _ :: is => stOffs is

theorem stOffs_mem {i : Instr} {is : List Instr} (hi : i ∈ is) {off : Nat} (ho : off ∈ stOffs [i]) :
    off ∈ stOffs is := by
  induction is with
  | nil => cases hi
  | cons j is ih =>
    rcases List.mem_cons.mp hi with rfl | hi
    · cases i <;> simp only [stOffs, List.mem_cons, List.not_mem_nil, or_false] at ho ⊢ <;>
        first | exact .inl ho | exact ho.elim
    · have := ih hi
      cases j <;> simp only [stOffs, List.mem_cons] <;> first | exact .inr this | exact this

/-- An instruction that is not a store keeps the memory. -/
theorem exec_mem {i : Instr} {s s' : State} (h : exec i s = some s')
    (hs : match i with | .str .. => False | .strb .. => False | _ => True) : s'.mem = s.mem := by
  cases i with
  | str t n off | strb t n off => exact hs.elim
  | umaal lo hi n m =>
    simp only [reduceExec] at h
    split at h <;> [cases h; skip]
    simp only [Option.some.injEq] at h
    subst h; rfl
  | _ =>
    simp only [reduceExec, State.load32, State.load8, Option.map_eq_some_iff] at h
    (repeat' split at h) <;>
    (try simp only [Option.some.injEq, reduceCtorEq] at h) <;>
    first
    | (subst h; rfl)
    | (obtain ⟨_, _, rfl⟩ := h; rfl)
    | (cases h)

/-- `t` is `s` but for the registers `rs`, the flags and the slots `ks` of
the scratch buffer. -/
structure Step (rs : List Reg) (ks : List Nat) (s t : State) : Prop where
  gpr : ∀ r, r ∉ rs → t.gpr r = s.gpr r
  sb : t.gpr .r12 = s.gpr .r12
  mem : ∀ x, (∀ k ∈ ks, ¬ (x - State.addr (s.gpr .r12 + BitVec.ofNat 32 (4 * k))).toNat < 4) →
    t.mem x = s.mem x
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

/-- The memory outside the words at the offsets `offs` from `r12`, and `r12`. -/
noncomputable def outOf (offs : List Nat) (s : State) : BitVec 32 × Mem :=
  open Classical in
  (s.gpr .r12, fun x =>
    if ∀ off ∈ offs, ¬ (x - State.addr (s.gpr .r12 + BitVec.ofNat 32 off)).toNat < 4 then s.mem x else 0)

theorem exec_outOf {rs : List Reg} (hb : Reg.r12 ∉ rs) {offs : List Nat} {i : Instr} {s s' : State}
    (hi : okI rs i = true ∧ ∀ off ∈ stOffs [i], off ∈ offs) (h : exec i s = some s') :
    outOf offs s' = outOf offs s := by
  obtain ⟨hi, ho⟩ := hi
  simp only [okI, Bool.and_eq_true] at hi
  have hr : s'.gpr .r12 = s.gpr .r12 := exec_gpr (clobbers_eq_false_of_contains hi.1 hb) h
  simp only [outOf, hr]
  refine congrArg _ (funext fun x => ?_)
  split
  · rename_i hx
    cases i with
    | str t n off =>
      simp only [beq_iff_eq] at hi
      simp only [reduceExec, State.store32] at h
      split at h <;> [skip; cases h]
      split at h <;> [skip; cases h]
      simp only [Option.some.injEq] at h
      subst h
      have := hx off (ho off (by simp [stOffs]))
      rw [hi.2] at *
      exact Mem.write_apply this
    | strb t n off => simp at hi
    | _ => rw [exec_mem h trivial]
  · rfl

/-- What a block keeps, read off its code. -/
theorem WP.step {is : List Instr} {s : State} {Q : State → Prop} (rs : List Reg) (ks : List Nat)
    (h : WP isa (.block is) s Q) (hc : okB rs is = true) (ho : stOffs is = ks.map (4 * ·))
    (hb : rs.contains .r12 = false) :
    WP isa (.block is) s fun t => Q t ∧ Step rs ks s t := by
  obtain ⟨tr, t, he, hq⟩ := h
  have he' := Exec.block_iff.mp he
  have hb' : Reg.r12 ∉ rs := by simpa using hb
  obtain ⟨hrd, hwr, hsp, -⟩ := execBlock_regions he'
  have hk := execBlock_keep (M := isa) (outOf (stOffs is)) (ok := fun i => okI rs i = true ∧
    ∀ off ∈ stOffs [i], off ∈ stOffs is) (exec_outOf hb') (fun i hi =>
      ⟨List.all_eq_true.mp hc i hi, fun off ho => stOffs_mem hi ho⟩) he'
  simp only [outOf, Prod.mk.injEq] at hk
  refine ⟨tr, t, he, hq, fun r hr => execBlock_gpr (fun i hi =>
    clobbers_eq_false_of_contains (by
      have := List.all_eq_true.mp hc i hi
      simp only [okI, Bool.and_eq_true] at this
      exact this.1) hr) he', hk.1, fun x hx => ?_, hrd, hwr, hsp⟩
  have hx' : ∀ off ∈ stOffs is, ¬ (x - State.addr (s.gpr .r12 + BitVec.ofNat 32 off)).toNat < 4 := by
    rw [ho]
    intro off hoff
    obtain ⟨k, hk', rfl⟩ := List.mem_map.mp hoff
    exact hx k hk'
  have := congrFun hk.2 x
  simp only [hk.1] at this
  rwa [ite_eq_left hx', ite_eq_left hx'] at this

/-! ## The scratch buffer -/

/-- The scratch buffer: 256 writable bytes at `r12`. -/
structure Scr (s : State) : Prop where
  wr : (⟨State.addr (s.gpr .r12), 256⟩ : Region) ∈ s.wr
  fit : (s.gpr .r12).toNat + 256 ≤ 2 ^ 32

theorem Scr.addr {s : State} (h : Scr s) {k : Nat} (hk : k < 64) :
    State.addr (s.gpr .r12 + BitVec.ofNat 32 (4 * k)) = State.addr (s.gpr .r12) + BitVec.ofNat 64 (4 * k) :=
  addr_add (by have := h.fit; omega_using [this, hk])

theorem Scr.st {s : State} (h : Scr s) {k : Nat} (hk : k < 64) :
    InRegions s.wr (State.addr (s.gpr .r12 + BitVec.ofNat 32 (4 * k))) 4 := by
  rw [h.addr hk]
  exact ⟨_, h.wr, Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])⟩

theorem Scr.ld {s : State} (h : Scr s) {k : Nat} (hk : k < 64) :
    InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r12 + BitVec.ofNat 32 (4 * k))) 4 := by
  obtain ⟨r, hr, hc⟩ := h.st hk
  exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem Scr.lt {k : Nat} (hk : k < 64) : 4 * k < 4096 := by omega_using [hk]

theorem Step.scr {rs : List Reg} {ks : List Nat} {s t : State} (h : Step rs ks s t) (hs : Scr s) : Scr t :=
  ⟨by rw [h.sb, h.wr]; exact hs.wr, by rw [h.sb]; exact hs.fit⟩

/-- A slot the block does not store to keeps its word. -/
theorem Step.slot {rs : List Reg} {ks : List Nat} {s t : State} (h : Step rs ks s t) (hs : Scr s)
    (hk : ∀ k ∈ ks, k < 64) {j : Nat} (hj : j < 64) (hn : j ∉ ks) : sw t j = sw s j := by
  rw [sw, sw, h.sb]
  refine Mem.readW_congr fun i hi => h.mem _ fun k hkm => ?_
  have hk' := hk k hkm
  have hne : j ≠ k := fun e => hn (e ▸ hkm)
  rw [hs.addr hj, hs.addr hk', Offset.add_add, Offset.lt_iff _ _ (by omega_using [hk']),
    Mem.sub_ofNat_toNat _ (by omega_using [hj, hi])]
  omega_using [hne, hi]

/-- The block writes memory only in the scratch buffer. -/
theorem Step.frame {rs : List Reg} {ks : List Nat} {s t : State} (h : Step rs ks s t) (hs : Scr s)
    (hk : ∀ k ∈ ks, k < 64) : Frame [⟨State.addr (s.gpr .r12), 256⟩] s.mem t.mem := by
  intro x hx
  refine h.mem x fun k hkm hlt => hx _ (List.mem_singleton.mpr rfl) ?_
  have hk' := hk k hkm
  rw [hs.addr hk', Offset.lt_iff _ _ (by omega_using [hk'])] at hlt
  simp only [Region.Contains]
  omega_using [hlt, hk']

theorem Step.trans {rs rs' : List Reg} {ks ks' : List Nat} {s u t : State} (h₁ : Step rs ks s u)
    (h₂ : Step rs' ks' u t) : Step (rs ++ rs') (ks ++ ks') s t where
  gpr r hr := by
    rw [List.mem_append, not_or] at hr
    rw [h₂.gpr r hr.2, h₁.gpr r hr.1]
  sb := h₂.sb.trans h₁.sb
  mem x hx := by
    rw [h₂.mem x fun k hk => by rw [h₁.sb]; exact hx k (List.mem_append_right _ hk),
      h₁.mem x fun k hk => hx k (List.mem_append_left _ hk)]
  rd := h₂.rd.trans h₁.rd
  wr := h₂.wr.trans h₁.wr
  sp := h₂.sp.trans h₁.sp

/-- A store to another slot keeps a slot's word. -/
theorem Scr.rw_ne {s : State} (h : Scr s) {j k : Nat} (hj : j < 64) (hk : k < 64) (hne : j ≠ k) (m : Mem)
    (v : BitVec 32) :
    (m.writeW (State.addr (s.gpr .r12 + BitVec.ofNat 32 (4 * k))) v).readW
        (State.addr (s.gpr .r12 + BitVec.ofNat 32 (4 * j))) 32 =
      m.readW (State.addr (s.gpr .r12 + BitVec.ofNat 32 (4 * j))) 32 := by
  rw [h.addr hj, h.addr hk]
  exact Mem.readW_writeW_sep (Offset.sep _ (by omega_using [hne]) (by omega_using [hj]) (by omega_using [hk]))
    (by decide)

/-- The slots of a list are below 64. -/
macro "mb" : tactic => `(tactic| first
  | decide
  | (intro k hk
     simp only [List.mem_cons, List.not_mem_nil, or_false, List.mem_append] at hk <;> omega))

/-- A slot is not in a list. -/
macro "nm" : tactic => `(tactic| first
  | decide
  | (simp only [List.mem_cons, List.not_mem_nil, or_false, List.mem_append, not_or, not_false_eq_true] <;>
     omega))

/-! ## Running blocks -/

/-- `s` with the memory `m`: what a store leaves, kept folded. -/
def withMem (s : State) (m : Mem) : State := { s with mem := m }

theorem store32_eq (s : State) (a : Addr) (x : BitVec 32) :
    s.store32 a x = if InRegions s.wr a 4 then some (withMem s (s.mem.writeW a x)) else none := rfl
theorem gpr_withMem (s : State) (m : Mem) : (withMem s m).gpr = s.gpr := rfl
theorem mem_withMem (s : State) (m : Mem) : (withMem s m).mem = m := rfl
theorem rd_withMem (s : State) (m : Mem) : (withMem s m).rd = s.rd := rfl
theorem wr_withMem (s : State) (m : Mem) : (withMem s m).wr = s.wr := rfl
theorem sp_withMem (s : State) (m : Mem) : (withMem s m).sp = s.sp := rfl
theorem z_withMem (s : State) (m : Mem) : (withMem s m).z = s.z := rfl
theorem gpr_subFlags (s : State) (x y : BitVec 32) : (subFlags s x y).gpr = s.gpr := rfl
theorem mem_subFlags (s : State) (x y : BitVec 32) : (subFlags s x y).mem = s.mem := rfl
theorem rd_subFlags (s : State) (x y : BitVec 32) : (subFlags s x y).rd = s.rd := rfl
theorem wr_subFlags (s : State) (x y : BitVec 32) : (subFlags s x y).wr = s.wr := rfl
theorem sp_subFlags (s : State) (x y : BitVec 32) : (subFlags s x y).sp = s.sp := rfl
theorem z_subFlags (s : State) (x y : BitVec 32) : (subFlags s x y).z = (x - y == 0#32) := rfl

/-- The code's immediates. -/
theorem enc_0 : encodable (0 : BitVec 32) = true := by decide
theorem enc_1 : encodable (1 : BitVec 32) = true := by decide
theorem enc_16 : encodable (16 : BitVec 32) = true := by decide
theorem enc_c2 : encodable (0xC2000000 : BitVec 32) = true := by decide

/-- Runs a block of the code, with `facts`, reading through the writes. -/
syntax "grun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| grun) => `(tactic| grun [])
  | `(tactic| grun [$ls,*]) => `(tactic| plain_simp_names (
      apply WP.of_runBlock
      set_option linter.unusedSimpArgs false in
      simp (disch := decide) only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, Op2.eval,
        enc_0, enc_1, enc_16, enc_c2, SB, KS, KM,
        gpr_setReg, mem_setReg, rd_setReg, wr_setReg, sp_setReg, z_setReg,
        gpr_subFlags, mem_subFlags, rd_subFlags, wr_subFlags, sp_subFlags, z_subFlags,
        State.load32, store32_eq, gpr_withMem, mem_withMem, rd_withMem, wr_withMem, sp_withMem, z_withMem,
        ite_true, ite_false, ↓reduceIte, reduceCtorEq, Nat.reduceLeDiff, Nat.reduceLT, and_self, Option.map_some,
        Option.some.injEq, exists_eq_left', List.cons_append, List.nil_append, and_true, true_and, $ls,*]))

/-- Running `l ++ rest` by running `l` first. -/
theorem WP.append {l rest : List Instr} {s : State} {P Q : State → Prop}
    (h : WP isa (.block l) s P) (k : ∀ s', P s' → WP isa (.block rest) s' Q) :
    WP isa (.block (l ++ rest)) s Q :=
  WP.block_append_iff.mpr (WP.mono h k)

/-! ## A 64-bit product of words -/

theorem m32Load_ok {s : State} (hs : Scr s) {xs ks : Nat} (hx : xs < 64) (hk : ks < 64) :
    WP isa (.block (m32Load xs ks)) s fun t =>
      (t.gpr .r0 = sw s xs ∧ t.gpr .r1 = sw s ks) ∧ Step [.r0, .r1] [] s t := by
  refine WP.step _ _ ?_ rfl rfl rfl
  grun [m32Load, sw, Scr.lt hx, Scr.lt hk, hs.ld hx, hs.ld hk]

theorem m32Lo_ok {s : State} (hs : Scr s) (hks : s.gpr .r10 = 0x9249#32) (hkm : s.gpr .r11 = 0x49249249#32) :
    WP isa (.block m32Lo) s fun t =>
      sw t tSlot = Holes16.h3 (s.gpr .r0) (s.gpr .r1) ∧
        Step [.r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .lr] [tSlot] s t := by
  refine WP.step _ _ ?_ rfl rfl rfl
  grun [m32Lo, split, core, sw, Scr.lt (k := tSlot) (by decide), hs.st (k := tSlot) (by decide), hks, hkm,
    Mem.readW_writeW_self32]
  rfl

theorem m32Mid_ok {s : State} (hks : s.gpr .r10 = 0x9249#32) (hkm : s.gpr .r11 = 0x49249249#32) :
    WP isa (.block m32Mid) s fun t =>
      t.gpr .r8 = Holes16.h3 (s.gpr .r0 ^^^ s.gpr .r0 >>> 16) (s.gpr .r1 ^^^ s.gpr .r1 >>> 16) ∧
        Step [.r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .lr] [] s t := by
  refine WP.step _ _ ?_ rfl rfl rfl
  grun [m32Mid, split, core, hks, hkm]
  rfl

theorem m32Hi_ok {s : State} (hks : s.gpr .r10 = 0x9249#32) (hkm : s.gpr .r11 = 0x49249249#32) :
    WP isa (.block m32Hi) s fun t =>
      t.gpr .r0 = Holes16.h3 (s.gpr .r0 >>> 16) (s.gpr .r1 >>> 16) ∧
        Step [.r0, .r2, .r3, .r4, .r5, .r6, .r7, .r9, .lr] [] s t := by
  refine WP.step _ _ ?_ rfl rfl rfl
  grun [m32Hi, split, core, hks, hkm]
  rfl

theorem m32Join_ok {s : State} (hs : Scr s) :
    WP isa (.block m32Join) s fun t =>
      (t.gpr .r1 = sw s tSlot ^^^ (s.gpr .r8 ^^^ sw s tSlot ^^^ s.gpr .r0) <<< 16 ∧
        t.gpr .r0 = s.gpr .r0 ^^^ (s.gpr .r8 ^^^ sw s tSlot ^^^ s.gpr .r0) >>> 16) ∧
        Step [.r0, .r1, .r8] [] s t := by
  refine WP.step _ _ ?_ rfl rfl rfl
  grun [m32Join, sw, Scr.lt, hs.ld]

theorem m32_ok {s : State} (hs : Scr s) (hks : s.gpr .r10 = 0x9249#32) (hkm : s.gpr .r11 = 0x49249249#32)
    {xs ks : Nat} (hx : xs < 64) (hk : ks < 64) :
    WP isa (.block (m32 xs ks)) s fun t =>
      (t.gpr .r1 = (Holes16.m32 (sw s xs) (sw s ks)).1 ∧ t.gpr .r0 = (Holes16.m32 (sw s xs) (sw s ks)).2) ∧
        Step [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .lr] [tSlot] s t := by
  refine WP.step _ _ ?_ rfl rfl rfl
  unfold m32
  refine WP.append (m32Load_ok hs hx hk) fun u1 ⟨⟨a0, a1⟩, k1⟩ => ?_
  obtain s1 := k1.scr hs
  obtain ks1 : u1.gpr .r10 = 0x9249#32 := (k1.gpr _ (by decide)).trans hks
  obtain km1 : u1.gpr .r11 = 0x49249249#32 := (k1.gpr _ (by decide)).trans hkm
  refine WP.append (m32Lo_ok s1 ks1 km1) fun u2 ⟨b, k2⟩ => ?_
  obtain s2 := k2.scr s1
  obtain ks2 : u2.gpr .r10 = 0x9249#32 := (k2.gpr _ (by decide)).trans ks1
  obtain km2 : u2.gpr .r11 = 0x49249249#32 := (k2.gpr _ (by decide)).trans km1
  refine WP.append (m32Mid_ok ks2 km2) fun u3 ⟨c, k3⟩ => ?_
  obtain s3 := k3.scr s2
  obtain ks3 : u3.gpr .r10 = 0x9249#32 := (k3.gpr _ (by decide)).trans ks2
  obtain km3 : u3.gpr .r11 = 0x49249249#32 := (k3.gpr _ (by decide)).trans km2
  refine WP.append (m32Hi_ok ks3 km3) fun u4 ⟨d, k4⟩ => ?_
  refine WP.mono (m32Join_ok (k4.scr s3)) fun t ⟨⟨e1, e0⟩, _⟩ => ?_
  obtain r0_2 : u2.gpr .r0 = sw s xs := (k2.gpr _ (by decide)).trans a0
  obtain r1_2 : u2.gpr .r1 = sw s ks := (k2.gpr _ (by decide)).trans a1
  obtain r0_3 : u3.gpr .r0 = sw s xs := (k3.gpr _ (by decide)).trans r0_2
  obtain r1_3 : u3.gpr .r1 = sw s ks := (k3.gpr _ (by decide)).trans r1_2
  obtain hL : sw u4 tSlot = Holes16.h3 (sw s xs) (sw s ks) := by
    rw [k4.slot s3 (by decide) (by decide) (by decide), k3.slot s2 (by decide) (by decide) (by decide), b, a0, a1]
  obtain hM : u4.gpr .r8 = Holes16.h3 (sw s xs ^^^ sw s xs >>> 16) (sw s ks ^^^ sw s ks >>> 16) := by
    rw [k4.gpr _ (by decide), c, r0_2, r1_2]
  obtain hH : u4.gpr .r0 = Holes16.h3 (sw s xs >>> 16) (sw s ks >>> 16) := by rw [d, r0_3, r1_3]
  exact ⟨by rw [e1, hL, hM, hH]; rfl, by rw [e0, hL, hM, hH]; rfl⟩

/-! ## A 128-bit product -/

theorem st2_ok {s : State} (hs : Scr s) {os : Nat} (ho : os + 1 < 64) :
    WP isa (.block (st2 os)) s fun t =>
      (sw t os = s.gpr .r1 ∧ sw t (os + 1) = s.gpr .r0) ∧ Step [] [os, os + 1] s t := by
  refine WP.step _ _ ?_ rfl rfl rfl
  grun [st2, sw, Scr.lt (k := os) (by omega_using [ho]), Scr.lt (k := os + 1) ho,
    hs.st (k := os) (by omega_using [ho]), hs.st ho, Mem.readW_writeW_self32,
    hs.rw_ne (j := os) (k := os + 1) (by omega_using [ho]) ho (by omega_using [])]

theorem stMid_ok {s : State} (hs : Scr s) {os : Nat} (ho : os + 2 < 64) :
    WP isa (.block (stMid os)) s fun t =>
      (sw t (os + 1) = s.gpr .r3 ∧ sw t (os + 2) = s.gpr .r4) ∧ Step [] [os + 1, os + 2] s t := by
  refine WP.step _ _ ?_ rfl rfl rfl
  grun [stMid, sw, Scr.lt (k := os + 1) (by omega_using [ho]), Scr.lt (k := os + 2) ho,
    hs.st (k := os + 1) (by omega_using [ho]), hs.st ho, Mem.readW_writeW_self32,
    hs.rw_ne (j := os + 1) (k := os + 2) (by omega_using [ho]) ho (by omega_using [])]

theorem groupJoin_ok {s : State} (hs : Scr s) {os : Nat} (ho : os + 3 < 64) :
    WP isa (.block (groupJoin os)) s fun t =>
      (t.gpr .r2 = sw s os ∧
        t.gpr .r3 = sw s (os + 1) ^^^ (s.gpr .r1 ^^^ sw s os ^^^ sw s (os + 2)) ∧
        t.gpr .r4 = sw s (os + 2) ^^^ (s.gpr .r0 ^^^ sw s (os + 1) ^^^ sw s (os + 3)) ∧
        t.gpr .r5 = sw s (os + 3)) ∧ Step [.r0, .r1, .r2, .r3, .r4, .r5] [] s t := by
  refine WP.step _ _ ?_ rfl rfl rfl
  grun [groupJoin, sw, Scr.lt (k := os) (by omega_using [ho]), Scr.lt (k := os + 1) (by omega_using [ho]),
    Scr.lt (k := os + 2) (by omega_using [ho]), Scr.lt (k := os + 3) ho,
    hs.ld (k := os) (by omega_using [ho]), hs.ld (k := os + 1) (by omega_using [ho]),
    hs.ld (k := os + 2) (by omega_using [ho]), hs.ld ho]

theorem group_ok {s : State} (hs : Scr s) (hks : s.gpr .r10 = 0x9249#32) (hkm : s.gpr .r11 = 0x49249249#32)
    {xs ks os : Nat} (hx : xs + 2 < 30) (hk : ks + 2 < 30) (ho : 30 < os) (ho' : os + 3 < 64) :
    WP isa (.block (group xs ks os)) s fun t =>
      (t.gpr .r2 = (Holes16.m64 (sw s xs) (sw s (xs + 1)) (sw s (xs + 2)) (sw s ks) (sw s (ks + 1))
          (sw s (ks + 2))).1 ∧
        t.gpr .r3 = (Holes16.m64 (sw s xs) (sw s (xs + 1)) (sw s (xs + 2)) (sw s ks) (sw s (ks + 1))
          (sw s (ks + 2))).2.1 ∧
        t.gpr .r4 = (Holes16.m64 (sw s xs) (sw s (xs + 1)) (sw s (xs + 2)) (sw s ks) (sw s (ks + 1))
          (sw s (ks + 2))).2.2.1 ∧
        t.gpr .r5 = (Holes16.m64 (sw s xs) (sw s (xs + 1)) (sw s (xs + 2)) (sw s ks) (sw s (ks + 1))
          (sw s (ks + 2))).2.2.2 ∧
        sw t os = (Holes16.m64 (sw s xs) (sw s (xs + 1)) (sw s (xs + 2)) (sw s ks) (sw s (ks + 1))
          (sw s (ks + 2))).1 ∧
        sw t (os + 3) = (Holes16.m64 (sw s xs) (sw s (xs + 1)) (sw s (xs + 2)) (sw s ks) (sw s (ks + 1))
          (sw s (ks + 2))).2.2.2) ∧
      Step [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .lr]
        [tSlot, os, os + 1, tSlot, os + 2, os + 2 + 1, tSlot] s t := by
  obtain ht : tSlot = 30 := rfl
  refine WP.step _ _ ?_ (by kernel_rfl) (by kernel_rfl) rfl
  unfold group
  refine WP.append (m32_ok hs hks hkm (by omega_using [hx]) (by omega_using [hk])) fun u1 ⟨⟨a1, a0⟩, k1⟩ => ?_
  obtain s1 := k1.scr hs
  refine WP.append (st2_ok s1 (by omega_using [ho'])) fun u2 ⟨⟨b0, b1⟩, k2⟩ => ?_
  obtain k12 := k1.trans k2
  obtain s2 := k2.scr s1
  refine WP.append (m32_ok s2 ((k12.gpr _ (by decide)).trans hks) ((k12.gpr _ (by decide)).trans hkm)
    (xs := xs + 1) (ks := ks + 1) (by omega_using [hx]) (by omega_using [hk])) fun u3 ⟨⟨c1, c0⟩, k3⟩ => ?_
  obtain s3 := k3.scr s2
  refine WP.append (st2_ok s3 (os := os + 2) (by omega_using [ho'])) fun u4 ⟨⟨d0, d1⟩, k4⟩ => ?_
  obtain k14 := k12.trans (k3.trans k4)
  obtain s4 := k4.scr s3
  refine WP.append (m32_ok s4 ((k14.gpr _ (by decide)).trans hks) ((k14.gpr _ (by decide)).trans hkm)
    (xs := xs + 2) (ks := ks + 2) (by omega_using [hx]) (by omega_using [hk])) fun u5 ⟨⟨e1, e0⟩, k5⟩ => ?_
  obtain s5 := k5.scr s4
  refine WP.mono (groupJoin_ok s5 (os := os) ho') fun t ⟨⟨f2, f3, f4, f5⟩, k6⟩ => ?_
  obtain x1 : sw u2 (xs + 1) = sw s (xs + 1) := k12.slot hs (by mb) (by omega_using [hx]) (by nm)
  obtain y1 : sw u2 (ks + 1) = sw s (ks + 1) := k12.slot hs (by mb) (by omega_using [hk]) (by nm)
  obtain x2 : sw u4 (xs + 2) = sw s (xs + 2) := k14.slot hs (by mb) (by omega_using [hx]) (by nm)
  obtain y2 : sw u4 (ks + 2) = sw s (ks + 2) := k14.slot hs (by mb) (by omega_using [hk]) (by nm)
  rw [x1, y1] at c1 c0
  rw [x2, y2] at e1 e0
  obtain k35 := k3.trans (k4.trans k5)
  obtain l0 : sw u5 os = (Holes16.m32 (sw s xs) (sw s ks)).1 := by
    rw [k35.slot s2 (by mb) (by omega_using [ho']) (by nm), b0, a1]
  obtain l1 : sw u5 (os + 1) = (Holes16.m32 (sw s xs) (sw s ks)).2 := by
    rw [k35.slot s2 (by mb) (by omega_using [ho']) (by nm), b1, a0]
  obtain h0 : sw u5 (os + 2) = (Holes16.m32 (sw s (xs + 1)) (sw s (ks + 1))).1 := by
    rw [k5.slot s4 (by mb) (by omega_using [ho']) (by nm), d0, c1]
  obtain h1 : sw u5 (os + 3) = (Holes16.m32 (sw s (xs + 1)) (sw s (ks + 1))).2 := by
    rw [k5.slot s4 (by mb) (by omega_using [ho']) (by nm)]
    exact d1.trans c0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f2, l0]; rfl
  · rw [f3, l1, e1, l0, h0]; rfl
  · rw [f4, h0, e0, l1, h1]; rfl
  · rw [f5, h1]; rfl
  · rw [k6.slot s5 (by mb) (by omega_using [ho']) (by nm), l0]; rfl
  · rw [k6.slot s5 (by mb) (by omega_using [ho']) (by nm), h1]; rfl

/-! ## A block -/

/-- The nine words of Karatsuba's products of the block `w` are in the slots from `a`. -/
def Nine (s : State) (a : Nat) (w : Holes16.W4) : Prop :=
  sw s a = w.2.2.2 ∧ sw s (a + 1) = w.2.2.1 ∧ sw s (a + 2) = w.2.2.2 ^^^ w.2.2.1 ∧ sw s (a + 3) = w.2.1 ∧
  sw s (a + 4) = w.1 ∧ sw s (a + 5) = w.2.1 ^^^ w.1 ∧ sw s (a + 6) = w.2.2.2 ^^^ w.2.1 ∧
  sw s (a + 7) = w.2.2.1 ^^^ w.1 ∧ sw s (a + 8) = w.2.2.2 ^^^ w.2.1 ^^^ (w.2.2.1 ^^^ w.1)

theorem Nine.step {s t : State} {a : Nat} {w : Holes16.W4} (h : Nine s a w) {rs : List Reg} {ks : List Nat}
    (k : Step rs ks s t) (hs : Scr s) (hk : ∀ k ∈ ks, k < 64) (ha : a + 8 < 64)
    (hn : ∀ i ≤ 8, a + i ∉ ks) : Nine t a w := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨(k.slot hs hk (by omega_using [ha]) (hn 0 (by decide))).trans h0,
    (k.slot hs hk (by omega_using [ha]) (hn 1 (by decide))).trans h1,
    (k.slot hs hk (by omega_using [ha]) (hn 2 (by decide))).trans h2,
    (k.slot hs hk (by omega_using [ha]) (hn 3 (by decide))).trans h3,
    (k.slot hs hk (by omega_using [ha]) (hn 4 (by decide))).trans h4,
    (k.slot hs hk (by omega_using [ha]) (hn 5 (by decide))).trans h5,
    (k.slot hs hk (by omega_using [ha]) (hn 6 (by decide))).trans h6,
    (k.slot hs hk (by omega_using [ha]) (hn 7 (by decide))).trans h7,
    (k.slot hs hk ha (hn 8 (by decide))).trans h8⟩

theorem nineX_ok {s : State} (hs : Scr s) :
    WP isa (.block (nine .r1 .r0 .lr .r10 .r2 .r3 xSlot)) s fun t =>
      Nine t xSlot (s.gpr .r1, s.gpr .r0, s.gpr .lr, s.gpr .r10) ∧
        Step [.r2, .r3] [xSlot, xSlot + 1, xSlot + 2, xSlot + 3, xSlot + 4, xSlot + 5, xSlot + 6, xSlot + 7,
          xSlot + 8] s t := by
  refine WP.step _ _ ?_ rfl rfl rfl
  grun [nine, Nine, sw, Scr.lt, hs.st, hs.rw_ne, Mem.readW_writeW_self32]

theorem nineK_ok {s : State} (hs : Scr s) :
    WP isa (.block (nine .r8 .r9 .r2 .r3 .r4 .r5 kSlot)) s fun t =>
      Nine t kSlot (s.gpr .r8, s.gpr .r9, s.gpr .r2, s.gpr .r3) ∧
        Step [.r4, .r5] [kSlot, kSlot + 1, kSlot + 2, kSlot + 3, kSlot + 4, kSlot + 5, kSlot + 6, kSlot + 7,
          kSlot + 8] s t := by
  refine WP.step _ _ ?_ rfl rfl rfl
  grun [nine, Nine, sw, Scr.lt, hs.st, hs.rw_ne, Mem.readW_writeW_self32]

theorem xorBlock_ok {s : State} (hs : Scr s) (D : BitVec 32) (hD : sw s dSlot = D)
    (h0 : InRegions (s.rd ++ s.wr) (State.addr (D + BitVec.ofNat 32 0)) 4)
    (h4 : InRegions (s.rd ++ s.wr) (State.addr (D + BitVec.ofNat 32 4)) 4)
    (h8 : InRegions (s.rd ++ s.wr) (State.addr (D + BitVec.ofNat 32 8)) 4)
    (h12 : InRegions (s.rd ++ s.wr) (State.addr (D + BitVec.ofNat 32 12)) 4) :
    WP isa (.block xorBlock) s fun t =>
      (t.gpr .r1 = s.gpr .r1 ^^^ rev (s.mem.readW (State.addr (D + BitVec.ofNat 32 0)) 32) ∧
        t.gpr .r0 = s.gpr .r0 ^^^ rev (s.mem.readW (State.addr (D + BitVec.ofNat 32 4)) 32) ∧
        t.gpr .lr = s.gpr .lr ^^^ rev (s.mem.readW (State.addr (D + BitVec.ofNat 32 8)) 32) ∧
        t.gpr .r10 = s.gpr .r10 ^^^ rev (s.mem.readW (State.addr (D + BitVec.ofNat 32 12)) 32) ∧
        sw t dSlot = D + 16) ∧ Step [.r0, .r1, .r2, .r3, .r10, .lr] [dSlot] s t := by
  have hD' : s.mem.readW (State.addr (s.gpr .r12 + BitVec.ofNat 32 (4 * dSlot))) 32 = D := hD
  refine WP.step _ _ ?_ rfl rfl rfl
  grun [xorBlock, xorWord, sw, Scr.lt, hs.ld, hs.st, hD', h0, h4, h8, h12, Mem.readW_writeW_self32]

theorem movw_ok {s : State} :
    WP isa (.block ([.movw KS 0x9249] : List Instr)) s fun t =>
      t.gpr .r10 = 0x9249#32 ∧ Step [.r10] [] s t := by
  refine WP.step _ _ ?_ rfl rfl rfl
  grun
  rfl

theorem head_ok {s : State} (hs : Scr s) (D : BitVec 32) (hD : sw s dSlot = D)
    (h0 : InRegions (s.rd ++ s.wr) (State.addr (D + BitVec.ofNat 32 0)) 4)
    (h4 : InRegions (s.rd ++ s.wr) (State.addr (D + BitVec.ofNat 32 4)) 4)
    (h8 : InRegions (s.rd ++ s.wr) (State.addr (D + BitVec.ofNat 32 8)) 4)
    (h12 : InRegions (s.rd ++ s.wr) (State.addr (D + BitVec.ofNat 32 12)) 4) :
    WP isa (.block head) s fun t =>
      (Nine t xSlot (s.gpr .r1 ^^^ rev (s.mem.readW (State.addr (D + BitVec.ofNat 32 0)) 32),
          s.gpr .r0 ^^^ rev (s.mem.readW (State.addr (D + BitVec.ofNat 32 4)) 32),
          s.gpr .lr ^^^ rev (s.mem.readW (State.addr (D + BitVec.ofNat 32 8)) 32),
          s.gpr .r10 ^^^ rev (s.mem.readW (State.addr (D + BitVec.ofNat 32 12)) 32)) ∧
        t.gpr .r10 = 0x9249#32 ∧ sw t dSlot = D + 16) ∧
      Step [.r0, .r1, .r2, .r3, .r10, .lr] [dSlot, xSlot, xSlot + 1, xSlot + 2, xSlot + 3, xSlot + 4,
        xSlot + 5, xSlot + 6, xSlot + 7, xSlot + 8] s t := by
  refine WP.step _ _ ?_ rfl rfl rfl
  unfold head
  refine WP.append (xorBlock_ok hs D hD h0 h4 h8 h12) fun u1 ⟨⟨a1, a0, alr, a10, ad⟩, k1⟩ => ?_
  obtain s1 := k1.scr hs
  refine WP.append (nineX_ok s1) fun u2 ⟨b, k2⟩ => ?_
  rw [a1, a0, alr, a10] at b
  refine WP.mono movw_ok fun t ⟨c, k3⟩ => ?_
  exact ⟨b.step k3 (k2.scr s1) (by decide) (by decide) (by decide), c, by
    rw [(k2.trans k3).slot s1 (by decide) (by decide) (by decide), ad]⟩

/-- The 256-bit product the code joins: the low halves' in the slots from
`lSlot`, the high halves' in those from `hSlot`, Karatsuba's in `r2`–`r5`. -/
def finF (s : State) : Holes16.W4 × Holes16.W4 :=
  Holes16.kar (sw s lSlot, sw s (lSlot + 1), sw s (lSlot + 2), sw s (lSlot + 3))
    (sw s hSlot, sw s (hSlot + 1), sw s (hSlot + 2), sw s (hSlot + 3))
    (s.gpr .r2, s.gpr .r3, s.gpr .r4, s.gpr .r5)

theorem finJoin_ok {s : State} (hs : Scr s) :
    WP isa (.block finJoin) s fun t =>
      (t.gpr .r6 = (finF s).1.1 ∧ t.gpr .r7 = (finF s).1.2.1 ∧ t.gpr .r8 = (finF s).1.2.2.1 ∧
        t.gpr .r9 = (finF s).1.2.2.2 ∧ t.gpr .r10 = (finF s).2.1 ∧ t.gpr .lr = (finF s).2.2.1 ∧
        t.gpr .r0 = (finF s).2.2.2.1 ∧ t.gpr .r1 = (finF s).2.2.2.2) ∧
      Step [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .lr] [] s t := by
  refine WP.step _ _ ?_ rfl rfl rfl
  grun [finJoin, finF, Holes16.kar, sw, Scr.lt, hs.ld]

/-- The reduction of the product in the registers. -/
def finR (s : State) : Holes16.W4 :=
  Holes16.red (s.gpr .r6) (s.gpr .r7) (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .lr) (s.gpr .r0) (s.gpr .r1)

theorem finRed_ok {s : State} :
    WP isa (.block finRed) s fun t =>
      (t.gpr .r1 = (finR s).1 ∧ t.gpr .r0 = (finR s).2.1 ∧ t.gpr .lr = (finR s).2.2.1 ∧
        t.gpr .r10 = (finR s).2.2.2) ∧ Step [.r0, .r1, .r9, .r10, .lr] [] s t := by
  refine WP.step _ _ ?_ rfl rfl rfl
  grun [finRed, fold, finR, Holes16.red, Holes16.foldLo, Holes16.foldHi]

theorem count_ok {s : State} (hs : Scr s) :
    WP isa (.block count) s fun t =>
      (sw t nSlot = sw s nSlot - 1 ∧ t.z = (sw s nSlot - 1 == 0)) ∧ Step [.r2] [nSlot] s t := by
  refine WP.step _ _ ?_ rfl rfl rfl
  grun [count, sw, Scr.lt, hs.ld, hs.st, Mem.readW_writeW_self32]
  rfl

/-- The slots a block stores to, in order. -/
def bks : List Nat :=
  [19, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 30, 33, 34, 30, 32, 33, 30, 35, 36, 30, 37, 38, 30, 36, 37,
    30, 39, 40, 30, 41, 42, 30, 20]

theorem bks_lt : ∀ k ∈ bks, k < 64 := by decide

/-- A block after its head: the three 128-bit products, the 256-bit one, its
reduction, and the count. -/
theorem tail_ok {a : State} (sa : Scr a) (aks : a.gpr .r10 = 0x9249#32) (akm : a.gpr .r11 = 0x49249249#32)
    (w k : Holes16.W4) (xN : Nine a xSlot w) (kN : Nine a kSlot k) :
    WP isa (.block (group xSlot kSlot lSlot ++ (stMid lSlot ++ (group (xSlot + 3) (kSlot + 3) hSlot ++
      (stMid hSlot ++ (group (xSlot + 6) (kSlot + 6) mSlot ++ (finJoin ++ (finRed ++ count)))))))) a fun t =>
      (t.gpr .r1, t.gpr .r0, t.gpr .lr, t.gpr .r10) = Holes16.mulW w k ∧ sw t nSlot = sw a nSlot - 1 ∧
        t.z = (sw a nSlot - 1 == 0) ∧ sw t dSlot = sw a dSlot := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8⟩ := xN
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, q8⟩ := kN
  refine WP.append (group_ok sa aks akm (xs := xSlot) (ks := kSlot) (os := lSlot) (by decide) (by decide)
    (by decide) (by decide)) fun b1 ⟨⟨_, l1, l2, _, ls0, ls3⟩, kb1⟩ => ?_
  rw [x0, x1, x2, q0, q1, q2] at l1 l2 ls0 ls3
  obtain sb1 := kb1.scr sa
  refine WP.append (stMid_ok sb1 (os := lSlot) (by decide)) fun b2 ⟨⟨ls1, ls2⟩, kb2⟩ => ?_
  rw [l1] at ls1
  rw [l2] at ls2
  obtain kab2 := kb1.trans kb2
  obtain sb2 := kb2.scr sb1
  refine WP.append (group_ok sb2 ((kab2.gpr .r10 (by decide)).trans aks) ((kab2.gpr .r11 (by decide)).trans akm)
    (xs := xSlot + 3) (ks := kSlot + 3) (os := hSlot) (by decide) (by decide) (by decide) (by decide))
    fun c1 ⟨⟨_, g1, g2, _, hs0, hs3⟩, kc1⟩ => ?_
  have e3 : sw b2 (xSlot + 3) = w.2.1 := (kab2.slot sa (by decide) (by decide) (by decide)).trans x3
  have e4 : sw b2 (xSlot + 3 + 1) = w.1 := (kab2.slot sa (by decide) (by decide) (by decide)).trans x4
  have e5 : sw b2 (xSlot + 3 + 2) = w.2.1 ^^^ w.1 := (kab2.slot sa (by decide) (by decide) (by decide)).trans x5
  have p3 : sw b2 (kSlot + 3) = k.2.1 := (kab2.slot sa (by decide) (by decide) (by decide)).trans q3
  have p4 : sw b2 (kSlot + 3 + 1) = k.1 := (kab2.slot sa (by decide) (by decide) (by decide)).trans q4
  have p5 : sw b2 (kSlot + 3 + 2) = k.2.1 ^^^ k.1 := (kab2.slot sa (by decide) (by decide) (by decide)).trans q5
  rw [e3, e4, e5, p3, p4, p5] at g1 g2 hs0 hs3
  obtain sc1 := kc1.scr sb2
  refine WP.append (stMid_ok sc1 (os := hSlot) (by decide)) fun c2 ⟨⟨hs1, hs2⟩, kc2⟩ => ?_
  rw [g1] at hs1
  rw [g2] at hs2
  obtain kac2 := kab2.trans (kc1.trans kc2)
  obtain sc2 := kc2.scr sc1
  refine WP.append (group_ok sc2 ((kac2.gpr .r10 (by decide)).trans aks) ((kac2.gpr .r11 (by decide)).trans akm)
    (xs := xSlot + 6) (ks := kSlot + 6) (os := mSlot) (by decide) (by decide) (by decide) (by decide))
    fun d1 ⟨⟨m0, m1, m2, m3, _, _⟩, kd1⟩ => ?_
  have e6 : sw c2 (xSlot + 6) = w.2.2.2 ^^^ w.2.1 := (kac2.slot sa (by decide) (by decide) (by decide)).trans x6
  have e7 : sw c2 (xSlot + 6 + 1) = w.2.2.1 ^^^ w.1 := (kac2.slot sa (by decide) (by decide) (by decide)).trans x7
  have e8 : sw c2 (xSlot + 6 + 2) = w.2.2.2 ^^^ w.2.1 ^^^ (w.2.2.1 ^^^ w.1) :=
    (kac2.slot sa (by decide) (by decide) (by decide)).trans x8
  have p6 : sw c2 (kSlot + 6) = k.2.2.2 ^^^ k.2.1 := (kac2.slot sa (by decide) (by decide) (by decide)).trans q6
  have p7 : sw c2 (kSlot + 6 + 1) = k.2.2.1 ^^^ k.1 := (kac2.slot sa (by decide) (by decide) (by decide)).trans q7
  have p8 : sw c2 (kSlot + 6 + 2) = k.2.2.2 ^^^ k.2.1 ^^^ (k.2.2.1 ^^^ k.1) :=
    (kac2.slot sa (by decide) (by decide) (by decide)).trans q8
  rw [e6, e7, e8, p6, p7, p8] at m0 m1 m2 m3
  obtain sd1 := kd1.scr sc2
  -- The products of the low and high halves, in their slots.
  obtain k2d := kb2.trans (kc1.trans (kc2.trans kd1))
  obtain k3d := kc1.trans (kc2.trans kd1)
  obtain k4d := kc2.trans kd1
  have dl0 := (k2d.slot sb1 (by decide) (by decide) (by decide) : sw d1 lSlot = sw b1 lSlot).trans ls0
  have dl1 := (k3d.slot sb2 (by decide) (by decide) (by decide) : sw d1 (lSlot + 1) = sw b2 (lSlot + 1)).trans ls1
  have dl2 := (k3d.slot sb2 (by decide) (by decide) (by decide) : sw d1 (lSlot + 2) = sw b2 (lSlot + 2)).trans ls2
  have dl3 := (k2d.slot sb1 (by decide) (by decide) (by decide) : sw d1 (lSlot + 3) = sw b1 (lSlot + 3)).trans ls3
  have dh0 := (k4d.slot sc1 (by decide) (by decide) (by decide) : sw d1 hSlot = sw c1 hSlot).trans hs0
  have dh1 := (kd1.slot sc2 (by decide) (by decide) (by decide) : sw d1 (hSlot + 1) = sw c2 (hSlot + 1)).trans hs1
  have dh2 := (kd1.slot sc2 (by decide) (by decide) (by decide) : sw d1 (hSlot + 2) = sw c2 (hSlot + 2)).trans hs2
  have dh3 := (k4d.slot sc1 (by decide) (by decide) (by decide) : sw d1 (hSlot + 3) = sw c1 (hSlot + 3)).trans hs3
  have eF : finF d1 = Holes16.prod w k := by
    rw [finF, dl0, dl1, dl2, dl3, dh0, dh1, dh2, dh3, m0, m1, m2, m3]; rfl
  refine WP.append (finJoin_ok sd1) fun e ⟨⟨f0, f1, f2, f3, f4, f5, f6, f7⟩, ke⟩ => ?_
  rw [eF] at f0 f1 f2 f3 f4 f5 f6 f7
  refine WP.append finRed_ok fun f ⟨⟨y0, y1, y2, y3⟩, kf⟩ => ?_
  have eR : finR e = Holes16.mulW w k := by rw [finR, f0, f1, f2, f3, f4, f5, f6, f7]; rfl
  rw [eR] at y0 y1 y2 y3
  obtain sf := kf.scr (ke.scr sd1)
  refine WP.mono (count_ok sf) fun t ⟨⟨cn, cz⟩, kt⟩ => ?_
  obtain kaf := kac2.trans (kd1.trans (ke.trans kf))
  have en : sw f nSlot = sw a nSlot := kaf.slot sa (by decide) (by decide) (by decide)
  refine ⟨?_, by rw [cn, en], by rw [cz, en], ?_⟩
  · rw [kt.gpr .r1 (by decide), kt.gpr .r0 (by decide), kt.gpr .lr (by decide), kt.gpr .r10 (by decide), y0, y1,
      y2, y3]
  · exact (kaf.trans kt).slot sa (by decide) (by decide) (by decide)

theorem block_ok {s : State} (hs : Scr s) (hkm : s.gpr .r11 = 0x49249249#32) (D : BitVec 32)
    (hD : sw s dSlot = D)
    (h0 : InRegions (s.rd ++ s.wr) (State.addr (D + BitVec.ofNat 32 0)) 4)
    (h4 : InRegions (s.rd ++ s.wr) (State.addr (D + BitVec.ofNat 32 4)) 4)
    (h8 : InRegions (s.rd ++ s.wr) (State.addr (D + BitVec.ofNat 32 8)) 4)
    (h12 : InRegions (s.rd ++ s.wr) (State.addr (D + BitVec.ofNat 32 12)) 4)
    (k : Holes16.W4) (hk : Nine s kSlot k) :
    WP isa (.block blockCode) s fun t =>
      ((t.gpr .r1, t.gpr .r0, t.gpr .lr, t.gpr .r10) =
          Holes16.mulW (s.gpr .r1 ^^^ rev (s.mem.readW (State.addr (D + BitVec.ofNat 32 0)) 32),
            s.gpr .r0 ^^^ rev (s.mem.readW (State.addr (D + BitVec.ofNat 32 4)) 32),
            s.gpr .lr ^^^ rev (s.mem.readW (State.addr (D + BitVec.ofNat 32 8)) 32),
            s.gpr .r10 ^^^ rev (s.mem.readW (State.addr (D + BitVec.ofNat 32 12)) 32)) k ∧
        sw t dSlot = D + 16 ∧ sw t nSlot = sw s nSlot - 1 ∧ t.z = (sw s nSlot - 1 == 0)) ∧
      Step [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .lr] bks s t := by
  refine WP.step _ _ ?_ (by kernel_rfl) (by kernel_rfl) rfl
  unfold blockCode
  refine WP.append (head_ok hs D hD h0 h4 h8 h12) fun a ⟨⟨xN, aks, ad⟩, ka⟩ => ?_
  refine WP.mono (tail_ok (ka.scr hs) aks ((ka.gpr .r11 (by decide)).trans hkm) _ k xN
    (hk.step ka hs (by decide) (by decide) (by decide))) fun t ⟨hy, hn, hz, hd⟩ => ?_
  have en : sw a nSlot = sw s nSlot := ka.slot hs (by decide) (by decide) (by decide)
  exact ⟨hy, hd.trans ad, by rw [hn, en], by rw [hz, en]⟩

/-! ## The function -/

/-- An access at an offset into a region of the state. -/
theorem in_off {rs : List Region} {b : BitVec 32} {L : Nat} (hr : (⟨State.addr b, L⟩ : Region) ∈ rs)
    (hf : b.toNat + L ≤ 2 ^ 32) {d n : Nat} (hd : d + n ≤ L) (hn : 0 < n) :
    InRegions rs (State.addr (b + BitVec.ofNat 32 d)) n := by
  rw [addr_add (by omega_using [hf, hd, hn])]
  exact ⟨_, hr, Offset.contains_base _ hd (by omega_using [hf, hd, hn])⟩

/-- The words of the block at `p`, the first bytes first. -/
def wordsAt (m : Mem) (p : BitVec 32) : Holes16.W4 :=
  (rev (m.readW (State.addr (p + BitVec.ofNat 32 0)) 32), rev (m.readW (State.addr (p + BitVec.ofNat 32 4)) 32),
    rev (m.readW (State.addr (p + BitVec.ofNat 32 8)) 32), rev (m.readW (State.addr (p + BitVec.ofNat 32 12)) 32))

theorem blk_wordsAt (m : Mem) {p : BitVec 32} (hf : p.toNat + 16 ≤ 2 ^ 32) :
    Holes16.blk (wordsAt m p) = blockAt m (State.addr p) := by
  rw [blockAt_rev, wordsAt, BitVec.add_zero, addr_add (k := 4) (by omega_using [hf]),
    addr_add (k := 8) (by omega_using [hf]), addr_add (k := 12) (by omega_using [hf])]
  rfl

theorem blk_xor (a b : Holes16.W4) :
    Holes16.blk (a.1 ^^^ b.1, a.2.1 ^^^ b.2.1, a.2.2.1 ^^^ b.2.2.1, a.2.2.2 ^^^ b.2.2.2) =
      Holes16.blk a ^^^ Holes16.blk b :=
  (w4_xor a.1 a.2.1 a.2.2.1 a.2.2.2 b.1 b.2.1 b.2.2.1 b.2.2.2).symm

/-- The memory after storing four words at `p`. -/
def put4 (m : Mem) (p : Addr) (a b c d : BitVec 32) : Mem :=
  (((m.writeW p a).writeW (p + BitVec.ofNat 64 4) b).writeW (p + BitVec.ofNat 64 8) c).writeW
    (p + BitVec.ofNat 64 12) d

theorem frame_put4 {m : Mem} (p : Addr) (a b c d : BitVec 32) : Frame [⟨p, 16⟩] m (put4 m p a b c d) := by
  have c (d : Nat) (h : d + 4 ≤ 16) : (⟨p, 16⟩ : Region).Contains (p + BitVec.ofNat 64 d) 4 :=
    Offset.contains_base p h (by omega_using [h])
  have c0 : (⟨p, 16⟩ : Region).Contains p 4 := by simpa using c 0 (by decide)
  exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c0).writeW (List.mem_singleton_self _) _
    (c 4 (by decide))).writeW (List.mem_singleton_self _) _ (c 8 (by decide))).writeW
    (List.mem_singleton_self _) _ (c 12 (by decide))

theorem readW_writeW_disj {m : Mem} {a b : Addr} (v : BitVec 32) (h : (⟨a, 4⟩ : Region).Disjoint ⟨b, 4⟩) :
    (m.writeW a v).readW b 32 = m.readW b 32 :=
  Mem.readW_writeW_sep (h.symm.sep (Region.contains_self _ _) (Region.contains_self _ _)) (by decide)

/-- The block of four words stored at `p`. -/
theorem blockAt_put4 (m : Mem) (p : Addr) (a b c d : BitVec 32) :
    blockAt (put4 m p a b c d) p = w4 (rev a) (rev b) (rev c) (rev d) := by
  have dj : ∀ {x y : Nat}, x + 4 ≤ y ∨ y + 4 ≤ x → x + 4 ≤ 16 → y + 4 ≤ 16 →
      (⟨p + BitVec.ofNat 64 x, 4⟩ : Region).Disjoint ⟨p + BitVec.ofNat 64 y, 4⟩ :=
    fun h hx hy => Offset.disjoint p h (by omega_using [hx]) (by omega_using [hy])
  have d₀ : (⟨p, 4⟩ : Region).Disjoint ⟨p + BitVec.ofNat 64 4, 4⟩ := by
    simpa using dj (x := 0) (y := 4) (.inl (by decide)) (by decide) (by decide)
  have d₀' : (⟨p, 4⟩ : Region).Disjoint ⟨p + BitVec.ofNat 64 8, 4⟩ := by
    simpa using dj (x := 0) (y := 8) (.inl (by decide)) (by decide) (by decide)
  have d₀'' : (⟨p, 4⟩ : Region).Disjoint ⟨p + BitVec.ofNat 64 12, 4⟩ := by
    simpa using dj (x := 0) (y := 12) (.inl (by decide)) (by decide) (by decide)
  rw [blockAt_rev, put4]
  simp only [readW_writeW_disj _ (dj (x := 12) (y := 8) (.inr (by decide)) (by decide) (by decide)),
    readW_writeW_disj _ (dj (x := 12) (y := 4) (.inr (by decide)) (by decide) (by decide)),
    readW_writeW_disj _ (dj (x := 8) (y := 4) (.inr (by decide)) (by decide) (by decide)),
    readW_writeW_disj _ d₀.symm, readW_writeW_disj _ d₀'.symm,
    readW_writeW_disj _ d₀''.symm, Mem.readW_writeW_self32]

theorem ldrSp_ok {s : State} (B : BitVec 32)
    (ha : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 0)) 4)
    (hB : s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 0)) 32 = B) :
    WP isa (.block ([.ldrSp SB 0] : List Instr)) s fun t =>
      t.gpr .r12 = B ∧ (∀ r, r ≠ .r12 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
        t.sp = s.sp := by
  grun [ha, hB]
  exact fun r hr => by simp only [hr, ↓reduceIte]

theorem saves_ok {s : State} (hs : Scr s) :
    WP isa (.block (saves ++ ([.cmp .r3 (.imm 0)] : List Instr))) s fun t =>
      (sw t 0 = s.gpr .r4 ∧ sw t 1 = s.gpr .r5 ∧ sw t 2 = s.gpr .r6 ∧ sw t 3 = s.gpr .r7 ∧
        sw t 4 = s.gpr .r8 ∧ sw t 5 = s.gpr .r9 ∧ sw t 6 = s.gpr .r10 ∧ sw t 7 = s.gpr .r11 ∧
        sw t 8 = s.gpr .lr ∧ sw t ySlot = s.gpr .r1 ∧ sw t dSlot = s.gpr .r2 ∧ sw t nSlot = s.gpr .r3 ∧
        t.z = (s.gpr .r3 - 0 == 0)) ∧
      Step [] [0, 1, 2, 3, 4, 5, 6, 7, 8, ySlot, dSlot, nSlot] s t := by
  refine WP.step _ _ ?_ rfl rfl rfl
  grun [saves, savedRegs, List.map_cons, List.map_nil, sw, Scr.lt, hs.st, hs.rw_ne, Mem.readW_writeW_self32]
  rfl

theorem restores_ok {s : State} (hs : Scr s) :
    WP isa (.block restores) s fun t =>
      (t.gpr .r4 = sw s 0 ∧ t.gpr .r5 = sw s 1 ∧ t.gpr .r6 = sw s 2 ∧ t.gpr .r7 = sw s 3 ∧
        t.gpr .r8 = sw s 4 ∧ t.gpr .r9 = sw s 5 ∧ t.gpr .r10 = sw s 6 ∧ t.gpr .r11 = sw s 7 ∧
        t.gpr .lr = sw s 8) ∧
      Step [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr] [] s t := by
  refine WP.step _ _ ?_ rfl rfl rfl
  grun [restores, savedRegs, List.map_cons, List.map_nil, sw, Scr.lt, hs.ld]

theorem keyCode_ok {s : State}
    (h0 : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 0)) 4)
    (h4 : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 4)) 4)
    (h8 : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 8)) 4)
    (h12 : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 12)) 4) :
    WP isa (.block keyCode) s fun t =>
      (t.gpr .r8 = (Holes16.keyW (wordsAt s.mem (s.gpr .r0))).1 ∧
        t.gpr .r9 = (Holes16.keyW (wordsAt s.mem (s.gpr .r0))).2.1 ∧
        t.gpr .r2 = (Holes16.keyW (wordsAt s.mem (s.gpr .r0))).2.2.1 ∧
        t.gpr .r3 = (Holes16.keyW (wordsAt s.mem (s.gpr .r0))).2.2.2) ∧
      Step [.r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9] [] s t := by
  refine WP.step _ _ ?_ rfl rfl rfl
  grun [keyCode, wordsAt, Holes16.keyW, h0, h4, h8, h12]
  rfl

theorem loadY_ok {s : State}
    (h0 : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r1 + BitVec.ofNat 32 0)) 4)
    (h4 : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r1 + BitVec.ofNat 32 4)) 4)
    (h8 : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r1 + BitVec.ofNat 32 8)) 4)
    (h12 : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r1 + BitVec.ofNat 32 12)) 4) :
    WP isa (.block loadY) s fun t =>
      (t.gpr .r11 = 0x49249249#32 ∧ t.gpr .r1 = (wordsAt s.mem (s.gpr .r1)).1 ∧
        t.gpr .r0 = (wordsAt s.mem (s.gpr .r1)).2.1 ∧ t.gpr .lr = (wordsAt s.mem (s.gpr .r1)).2.2.1 ∧
        t.gpr .r10 = (wordsAt s.mem (s.gpr .r1)).2.2.2) ∧
      Step [.r0, .r1, .r10, .r11, .lr] [] s t := by
  refine WP.step _ _ ?_ rfl rfl rfl
  grun [loadY, wordsAt, h0, h4, h8, h12]
  decide

theorem prep_ok {s : State} (hs : Scr s)
    (hIn : (⟨State.addr (s.gpr .r0), 16⟩ : Region) ∈ s.rd ++ s.wr) (fH : (s.gpr .r0).toNat + 16 ≤ 2 ^ 32)
    (yIn : (⟨State.addr (s.gpr .r1), 16⟩ : Region) ∈ s.rd ++ s.wr) (fY : (s.gpr .r1).toNat + 16 ≤ 2 ^ 32)
    (dY : Region.Disjoint ⟨State.addr (s.gpr .r1), 16⟩ ⟨State.addr (s.gpr .r12), 256⟩) :
    WP isa (.block prep) s fun t =>
      (Nine t kSlot (Holes16.keyW (wordsAt s.mem (s.gpr .r0))) ∧ t.gpr .r11 = 0x49249249#32 ∧
        (t.gpr .r1, t.gpr .r0, t.gpr .lr, t.gpr .r10) = wordsAt s.mem (s.gpr .r1)) ∧
      Step [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr]
        [kSlot, kSlot + 1, kSlot + 2, kSlot + 3, kSlot + 4, kSlot + 5, kSlot + 6, kSlot + 7, kSlot + 8] s t := by
  refine WP.step _ _ ?_ rfl rfl rfl
  unfold prep
  refine WP.append (keyCode_ok (in_off hIn fH (by decide) (by decide)) (in_off hIn fH (by decide) (by decide))
    (in_off hIn fH (by decide) (by decide)) (in_off hIn fH (by decide) (by decide)))
    fun u1 ⟨⟨a8, a9, a2, a3⟩, k1⟩ => ?_
  obtain s1 := k1.scr hs
  refine WP.append (nineK_ok s1) fun u2 ⟨b, k2⟩ => ?_
  rw [a8, a9, a2, a3] at b
  obtain k12 := k1.trans k2
  have r1_2 : u2.gpr .r1 = s.gpr .r1 := k12.gpr .r1 (by decide)
  have yIn2 : (⟨State.addr (u2.gpr .r1), 16⟩ : Region) ∈ u2.rd ++ u2.wr := by rw [r1_2, k12.rd, k12.wr]; exact yIn
  have fY2 : (u2.gpr .r1).toNat + 16 ≤ 2 ^ 32 := by rw [r1_2]; exact fY
  refine WP.mono (loadY_ok (in_off yIn2 fY2 (by decide) (by decide)) (in_off yIn2 fY2 (by decide) (by decide))
    (in_off yIn2 fY2 (by decide) (by decide)) (in_off yIn2 fY2 (by decide) (by decide)))
    fun t ⟨⟨c11, c1, c0, clr, c10⟩, k3⟩ => ?_
  have em : wordsAt u2.mem (u2.gpr .r1) = wordsAt s.mem (s.gpr .r1) := by
    have fr := k12.frame hs (by decide)
    have rdw : ∀ d, d + 4 ≤ 16 → u2.mem.readW (State.addr (s.gpr .r1 + BitVec.ofNat 32 d)) 32 =
        s.mem.readW (State.addr (s.gpr .r1 + BitVec.ofNat 32 d)) 32 := fun d hd => by
      rw [addr_add (by omega_using [fY, hd])]
      exact fr.readW (r := ⟨State.addr (s.gpr .r1), 16⟩) (Offset.contains_base _ hd (by omega_using [hd]))
        (fun r' hr' => by simp only [List.mem_singleton] at hr'; subst hr'; exact dY) (by decide)
    rw [wordsAt, wordsAt, r1_2, rdw 0 (by decide), rdw 4 (by decide), rdw 8 (by decide), rdw 12 (by decide)]
  rw [em] at c1 c0 clr c10
  refine ⟨b.step k3 (k2.scr s1) (by decide) (by decide) (by decide), c11, ?_⟩
  rw [c1, c0, clr, c10]

theorem storeY_ok {s : State} (hs : Scr s) (Y : BitVec 32) (hY : sw s ySlot = Y)
    (h0 : InRegions s.wr (State.addr (Y + BitVec.ofNat 32 0)) 4)
    (h4 : InRegions s.wr (State.addr (Y + BitVec.ofNat 32 4)) 4)
    (h8 : InRegions s.wr (State.addr (Y + BitVec.ofNat 32 8)) 4)
    (h12 : InRegions s.wr (State.addr (Y + BitVec.ofNat 32 12)) 4) :
    WP isa (.block storeY) s fun t =>
      t.mem = (((s.mem.writeW (State.addr (Y + BitVec.ofNat 32 0)) (rev (s.gpr .r1))).writeW
        (State.addr (Y + BitVec.ofNat 32 4)) (rev (s.gpr .r0))).writeW
        (State.addr (Y + BitVec.ofNat 32 8)) (rev (s.gpr .lr))).writeW
        (State.addr (Y + BitVec.ofNat 32 12)) (rev (s.gpr .r10)) ∧
      t.gpr .r12 = s.gpr .r12 ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have hY' : s.mem.readW (State.addr (s.gpr .r12 + BitVec.ofNat 32 (4 * ySlot))) 32 = Y := hY
  grun [storeY, Scr.lt, hs.ld, hY', h0, h4, h8, h12]

theorem wordsAt_frame {R : Region} {m m' : Mem} (hf : Frame [R] m m') {p : BitVec 32}
    (fit : p.toNat + 16 ≤ 2 ^ 32) (hd : Region.Disjoint ⟨State.addr p, 16⟩ R) : wordsAt m' p = wordsAt m p := by
  have rdw : ∀ d, d + 4 ≤ 16 → m'.readW (State.addr (p + BitVec.ofNat 32 d)) 32 =
      m.readW (State.addr (p + BitVec.ofNat 32 d)) 32 := fun d hd' => by
    rw [addr_add (by omega_using [fit, hd'])]
    exact hf.readW (r := ⟨State.addr p, 16⟩) (Offset.contains_base _ hd' (by omega_using [hd']))
      (fun r' hr' => by simp only [List.mem_singleton] at hr'; subst hr'; exact hd) (by decide)
  rw [wordsAt, wordsAt, rdw 0 (by decide), rdw 4 (by decide), rdw 8 (by decide), rdw 12 (by decide)]

/-- Before block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop where
  sb : s.gpr .r12 = bp s₀
  km : s.gpr .r11 = 0x49249249#32
  key : Nine s kSlot (Holes16.keyW (wordsAt s₀.mem (hA s₀)))
  y : Holes16.blk (s.gpr .r1, s.gpr .r0, s.gpr .lr, s.gpr .r10) =
    ghashFrom (H₀ s₀) (Y₀ s₀) (blocksAt s₀.mem (State.addr (dp s₀)) i)
  ds : sw s dSlot = blk s₀ i
  ns : sw s nSlot = BitVec.ofNat 32 (nb s₀ - i)
  ys : sw s ySlot = yp s₀
  saved : ∀ j < 9, sw s j = s₀.gpr (greg j)
  frame : Frame [bR s₀] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

theorem LInv.scr {s₀ s : State} {i : Nat} (hp : Pre s₀) (h : LInv s₀ i s) : Scr s :=
  ⟨by rw [h.sb, h.wr, hp.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..), by
    rw [h.sb]; exact hp.fitB⟩

theorem bks_ge : ∀ j < 19, j ∉ bks := by decide

theorem beq_pred {a : Nat} (h0 : 0 < a) (h : a < 2 ^ 32) :
    (BitVec.ofNat 32 a - 1 == 0) = decide (a - 1 = 0) := by
  rw [show BitVec.ofNat 32 a - 1 = BitVec.ofNat 32 (a - 1) by bv_omega,
    VG.Proof.MdStream.Arm.ofNat_beq_zero (by omega_arith)]

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State} (hL : LInv s₀ i s) :
    WP isa (.block blockCode) s fun s' =>
      (isa.eval .ne s' = some false ∧ LInv s₀ (nb s₀) s') ∨
      (isa.eval .ne s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  have hs := hL.scr hp
  have hfD := hp.fitD
  have din : ∀ d, d + 4 ≤ 16 → InRegions (s.rd ++ s.wr) (State.addr (blk s₀ i + BitVec.ofNat 32 d)) 4 :=
    fun d hd => by
      rw [hL.rd, hp.rd]
      simp only [blk]
      rw [Offset.add_add, addr_add (by omega_using [hfD, hi, hd])]
      exact ⟨dR s₀, List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
        Offset.contains_base _ (by omega_using [hi, hd]) (by omega_using [hfD, hi, hd])⟩
  refine WP.mono (block_ok hs hL.km (blk s₀ i) hL.ds (din 0 (by decide)) (din 4 (by decide)) (din 8 (by decide))
    (din 12 (by decide)) _ hL.key) fun t ⟨⟨hy, hd, hn, hz⟩, kt⟩ => ?_
  have hnb : nb s₀ < 2 ^ 32 := (s₀.gpr .r3).isLt
  have hL' : LInv s₀ (i + 1) t := by
    refine ⟨kt.sb.trans hL.sb, (kt.gpr .r11 (by decide)).trans hL.km,
      hL.key.step kt hs bks_lt (by decide) (by decide), ?_, ?_, ?_,
      (kt.slot hs bks_lt (by decide) (by decide)).trans hL.ys,
      fun j hj => (kt.slot hs bks_lt (by omega_using [hj]) (bks_ge j (by omega_using [hj]))).trans (hL.saved j hj),
      ?_, kt.rd.trans hL.rd, kt.wr.trans hL.wr, kt.sp.trans hL.sp⟩
    · have ex : Holes16.blk (wordsAt s.mem (blk s₀ i)) =
          blockAt s₀.mem (State.addr (dp s₀) + BitVec.ofNat 64 (16 * i)) := by
        rw [blk_wordsAt _ (hp.blk_fit hi), ← hp.blk_addr hi]
        exact blockAt_congr fun j hj => hL.frame.bytes (R := ⟨State.addr (blk s₀ i), 16⟩) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact hp.dDB.sub_left (hp.blk_sub hi)) (by simp) hj
      rw [hy, Holes16.mulW_eq, ghashFrom_blocksAt_succ, ← hL.y]
      refine congr (congrArg mul ?_) (blk_wordsAt _ hp.fitH)
      rw [← ex]
      exact blk_xor (s.gpr .r1, s.gpr .r0, s.gpr .lr, s.gpr .r10) (wordsAt s.mem (blk s₀ i))
    · rw [hd]
      simp only [blk]
      bv_omega
    · rw [hn, hL.ns]
      bv_omega
    · have := kt.frame hs bks_lt
      rw [hL.sb] at this
      exact hL.frame.trans this
  have hz' : t.z = decide (nb s₀ - (i + 1) = 0) := by
    rw [hz, hL.ns, beq_pred (by omega_using [hi]) (by omega_using [hnb]), Nat.sub_sub]
  by_cases hl : i + 1 = nb s₀
  · exact .inl ⟨(VG.Proof.MdStream.Arm.eval_ne t).trans (by rw [hz', ← hl, Nat.sub_self]; rfl), hl ▸ hL'⟩
  · exact .inr ⟨(VG.Proof.MdStream.Arm.eval_ne t).trans (by
      rw [hz', decide_eq_false (by omega_using [hi, hl])]; rfl), by omega_using [hi, hl], hL'⟩

theorem blocks_ok {s₀ : State} (hp : Pre s₀) (hpos : 0 < nb s₀) {s : State} (hL : LInv s₀ 0 s) :
    WP isa (.loop (.block blockCode) .ne) s (LInv s₀ (nb s₀)) := by
  refine WP.loop (M := isa) (fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv s₀ i s)
    (fun m s ⟨i, hm, hi, hL⟩ => WP.mono (body_ok hp hi hL) fun s' h => ?_) _ s ⟨0, rfl, hpos, hL⟩
  rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
  · exact .inl ⟨he, hc⟩
  · exact .inr ⟨he, nb s₀ - (i + 1), by omega_using [hm, hi'], i + 1, rfl, hi', hL'⟩

theorem e0 (x : BitVec 32) : x - (0 : BitVec 32) = x := by bv_omega

theorem kslots_ge : ∀ j < 9, j ∉ [kSlot, kSlot + 1, kSlot + 2, kSlot + 3, kSlot + 4, kSlot + 5, kSlot + 6,
    kSlot + 7, kSlot + 8] := by decide

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa ghash s₀ fun s' =>
      (∀ i < 9, s'.gpr (greg i) = s₀.gpr (greg i)) ∧ Proof.Gcm.ghashArm.post s₀ s' := by
  have hfB := hp.fitB
  unfold ghash
  refine WP.seq ?_
  show WP isa (.block (([.ldrSp SB 0] : List Instr) ++ (saves ++ ([.cmp .r3 (.imm 0)] : List Instr)))) s₀ _
  refine WP.append (ldrSp_ok (bp s₀) ⟨aR s₀, by rw [hp.rd]; simp, Region.contains_self _ _⟩ rfl)
    fun s₁ ⟨b1, g1, m1, rd1, wr1, sp1⟩ => ?_
  have sc1 : Scr s₁ := ⟨by rw [b1, wr1, hp.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..), by
    rw [b1]; exact hfB⟩
  refine WP.mono (saves_ok sc1) fun s₂ ⟨⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, vy, vd, vn, vz⟩, k2⟩ => ?_
  have sc2 := k2.scr sc1
  have sb2 : s₂.gpr .r12 = bp s₀ := k2.sb.trans b1
  have g2 : ∀ r, r ≠ .r12 → s₂.gpr r = s₀.gpr r := fun r hr =>
    (k2.gpr r (List.not_mem_nil)).trans (g1 r hr)
  have fr2 : Frame [bR s₀] s₀.mem s₂.mem := by
    have := k2.frame sc1 (by decide)
    rw [b1, m1] at this
    exact this
  have rd2 : s₂.rd = s₀.rd := k2.rd.trans rd1
  have wr2 : s₂.wr = s₀.wr := k2.wr.trans wr1
  have sp2 : s₂.sp = s₀.sp := k2.sp.trans sp1
  have sv2 : ∀ j < 9, sw s₂ j = s₀.gpr (greg j) := by
    intro j hj
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
        j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 := by omega_using [hj]
    · exact v0.trans (g1 _ (by decide))
    · exact v1.trans (g1 _ (by decide))
    · exact v2.trans (g1 _ (by decide))
    · exact v3.trans (g1 _ (by decide))
    · exact v4.trans (g1 _ (by decide))
    · exact v5.trans (g1 _ (by decide))
    · exact v6.trans (g1 _ (by decide))
    · exact v7.trans (g1 _ (by decide))
    · exact v8.trans (g1 _ (by decide))
  refine WP.seq (WP.mono (Q := fun (s₄ : State) => Scr s₄ ∧ (∀ j < 9, sw s₄ j = s₀.gpr (greg j)) ∧
      blockAt s₄.mem (State.addr (yp s₀)) =
        ghashFrom (H₀ s₀) (Y₀ s₀) (blocksAt s₀.mem (State.addr (dp s₀)) (nb s₀))) ?_
    fun s₄ ⟨sc4, sv4, hy4⟩ => ?_)
  · have hev : isa.eval .eq s₂ = some (s₀.gpr .r3 == 0) := by
      show some s₂.z = _
      rw [vz, g1 .r3 (by decide), e0]
    refine WP.ite _ hev (fun h => WP.block_nil ?_) (fun h => ?_)
    · have h0 : nb s₀ = 0 := by simp at h; simp [nb, h]
      refine ⟨sc2, sv2, ?_⟩
      rw [h0, ghashFrom_blocksAt_zero]
      exact blockAt_congr fun j hj => fr2.bytes (R := yR s₀) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.dYB) (by simp) hj
    · have hpos : 0 < nb s₀ := by
        simp only [beq_eq_false_iff_ne, ne_eq] at h
        exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
      have r0_2 : s₂.gpr .r0 = hA s₀ := g2 .r0 (by decide)
      have r1_2 : s₂.gpr .r1 = yp s₀ := g2 .r1 (by decide)
      refine WP.seq (WP.mono (prep_ok sc2
        (by rw [r0_2, rd2, hp.rd]; exact List.mem_append_left _ (List.mem_cons_self ..))
        (by rw [r0_2]; exact hp.fitH)
        (by rw [r1_2, wr2, hp.wr]; exact List.mem_append_right _ (List.mem_cons_self ..))
        (by rw [r1_2]; exact hp.fitY)
        (by rw [r1_2, sb2]; exact hp.dYB)) fun s₃ ⟨⟨kN, km3, hy3⟩, k3⟩ => ?_)
      rw [r0_2, wordsAt_frame fr2 hp.fitH hp.dHB] at kN
      rw [r1_2, wordsAt_frame fr2 hp.fitY hp.dYB] at hy3
      have hL₀ : LInv s₀ 0 s₃ := by
        refine ⟨k3.sb.trans sb2, km3, kN, ?_, ?_, ?_,
          (k3.slot sc2 (by decide) (by decide) (by decide)).trans (vy.trans (g1 .r1 (by decide))),
          fun j hj => (k3.slot sc2 (by decide) (by omega_using [hj]) (kslots_ge j hj)).trans (sv2 j hj), ?_,
          k3.rd.trans rd2, k3.wr.trans wr2, k3.sp.trans sp2⟩
        · rw [hy3, blk_wordsAt _ hp.fitY, ghashFrom_blocksAt_zero]
        · rw [k3.slot sc2 (by decide) (by decide) (by decide), vd, g1 .r2 (by decide)]
          show dp s₀ = dp s₀ + BitVec.ofNat 32 (16 * 0)
          rw [Nat.mul_zero, BitVec.add_zero]
        · rw [k3.slot sc2 (by decide) (by decide) (by decide), vn, g1 .r3 (by decide)]
          show s₀.gpr .r3 = BitVec.ofNat 32 ((s₀.gpr .r3).toNat - 0)
          rw [Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
        · have := k3.frame sc2 (by decide)
          rw [sb2] at this
          exact fr2.trans this
      refine WP.seq (WP.mono (blocks_ok hp hpos hL₀) fun s₅ hL5 => ?_)
      have sc5 := hL5.scr hp
      have yw : (⟨State.addr (yp s₀), 16⟩ : Region) ∈ s₅.wr := by
        rw [hL5.wr, hp.wr]; exact List.mem_cons_self ..
      have hfY := hp.fitY
      refine WP.mono (storeY_ok sc5 (yp s₀) hL5.ys (in_off yw hfY (by decide) (by decide))
        (in_off yw hfY (by decide) (by decide)) (in_off yw hfY (by decide) (by decide))
        (in_off yw hfY (by decide) (by decide))) fun s₆ ⟨hm, hb, hrd, hwr, hsp⟩ => ?_
      have em : s₆.mem = put4 s₅.mem (State.addr (yp s₀)) (rev (s₅.gpr .r1)) (rev (s₅.gpr .r0))
          (rev (s₅.gpr .lr)) (rev (s₅.gpr .r10)) := by
        rw [hm, BitVec.add_zero, addr_add (k := 4) (by omega_using [hfY]), addr_add (k := 8) (by omega_using [hfY]),
          addr_add (k := 12) (by omega_using [hfY])]
        rfl
      refine ⟨⟨by rw [hb, hwr]; exact sc5.wr, by rw [hb]; exact sc5.fit⟩, fun j hj => ?_, ?_⟩
      · rw [← hL5.saved j hj, sw, sw, hb, em, sc5.addr (by omega_using [hj])]
        exact (frame_put4 (m := s₅.mem) (State.addr (yp s₀)) _ _ _ _).readW
          (r := ⟨State.addr (s₅.gpr .r12), 256⟩) (Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj]))
          (fun r' hr' => by
            simp only [List.mem_singleton] at hr'; subst hr'
            rw [hL5.sb]; exact hp.dYB.symm) (by decide)
      · rw [em, blockAt_put4, rev_rev, rev_rev, rev_rev, rev_rev]
        exact hL5.y
  · refine WP.mono (restores_ok sc4) fun t ⟨⟨w4', w5, w6, w7, w8, w9, w10, w11, wl⟩, k⟩ => ?_
    refine ⟨fun j hj => ?_, ?_⟩
    · obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
          j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 := by omega_using [hj]
      · exact w4'.trans (sv4 0 (by decide))
      · exact w5.trans (sv4 1 (by decide))
      · exact w6.trans (sv4 2 (by decide))
      · exact w7.trans (sv4 3 (by decide))
      · exact w8.trans (sv4 4 (by decide))
      · exact w9.trans (sv4 5 (by decide))
      · exact w10.trans (sv4 6 (by decide))
      · exact w11.trans (sv4 7 (by decide))
      · exact wl.trans (sv4 8 (by decide))
    · have em : t.mem = s₄.mem := funext fun x => k.mem x fun _ h => nomatch h
      show blockAt t.mem (State.addr (yp s₀)) = _
      rw [em]
      exact hy4

theorem law_correct (s : State) (hs : Proof.Gcm.ghashArm.pre s) :
    ∃ t s', Exec isa Impl.Gcm.Arm.ghash s t s' ∧ abiPreserved s s' ∧ Proof.Gcm.ghashArm.post s s' := by
  obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of hs)
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he⟩, h₂⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h₁ 0 (by decide)
  · exact h₁ 1 (by decide)
  · exact h₁ 2 (by decide)
  · exact h₁ 3 (by decide)
  · exact h₁ 4 (by decide)
  · exact h₁ 5 (by decide)
  · exact h₁ 6 (by decide)
  · exact h₁ 7 (by decide)
  · exact h₁ 8 (by decide)

instance : GhashLaw := ⟨law_correct⟩

end VG.Proof.Gcm.Arm
