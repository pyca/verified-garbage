module

public import VerifiedGarbage.Proof.Hkdf.Arm.Key
public import VerifiedGarbage.Proof.Framework.Arm.Spill
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Upd
import VerifiedGarbage.Proof.Pbkdf2.Whole.Common
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.CallWipeStack
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Hmac.Common
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Impl.Hkdf.Arm
meta import VerifiedGarbage.Proof.Hkdf.Arm.Key

/-!
# HKDF on 32-bit ARM: `vg_hkdf_extract`, correct and constant time

The contract the proof is written against (`extractR`), for the table `hmac`
of one hash function `w` (`HVar`), whose functions an indirect call of
`f`'s reaches: `extract(salt, salt_len, ikm, ikm_len, prk, prk_len, hmac)`
writes `HKDF-Extract(salt, IKM)` (`D` bytes) to `prk`.

As on AArch64 (`Proof/Hkdf/AArch64/Extract.lean`): the frame (`xFr` bytes:
the save area, HMAC's inner and outer states, then the working space)
allocated, the prologue saves our caller's registers and our return address
and keeps the arguments it needs after the calls in callee-saved registers
(`pro_ok`, from which on `XR` holds); then `init` with the salt as the key,
`update` with the input keying material and `finalize` into `prk`, each
through the table in the frame of its stack arguments (`init_ok`, `upd_ok`,
`fin_ok`); and the epilogue restores our caller's registers and our return
address (`epi_ok`), which nothing after the prologue writes.
-/

@[expose] public section

namespace VG.Proof.Hkdf.Arm.Extract

open VG VG.Arm VG.Arm.Steps
open VG.Impl.Hkdf.Arm
open VG.Impl.Ecdsa.Rfc6979.Arm (Fns tD tB)
open VG.Proof.HmacTable.Arm (HVar TabOK TabMem tA AnyArgs any_frame any_rel)
open VG.Proof.Hkdf.Arm (HOk StackAt base stackAt toNat_addr TabFn tcall_ok tcall_rel push_gpr Ck rel_ck
  rel_blk rel_sp rel_both contains_pre bytes_keep repr_keep reprOK stateBytes_eq work_eq blockKey_len append_zero)
open VG.Arm.FrameStack (armStack addr_sub' sub_toNat')
open VG.Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)
open VG.Spec.Sha256 (bytesAt)

/-- The stack `vg_hkdf_extract` uses: its frame, and the 32 bytes below it
that the calls use. -/
def xStack : Nat := xFr + 32

theorem xFr_eq : xFr = 3824 := rfl
theorem xStack_eq : xStack = 3856 := rfl
theorem xIn_eq : xIn = 32 := rfl
theorem xOut_eq : xOut = 224 := rfl
theorem xWork_eq : xWork = 416 := rfl

/-- `extract(salt, salt_len, ikm, ikm_len, prk, prk_len, hmac)`, with `N`
bytes of stack, for the table `hmac` of `w`, whose functions an indirect
call of `f`'s reaches, with the addresses of the functions `ns` public. -/
def extractR (w : HVar) (f : Fns) (ns : List String) (N : Nat) : Contract isa where
  pre s :=
    let salt : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
    let ikm : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
    let prk : Region := ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩
    let tab : Region := ⟨State.addr (stackArg s 2), 24⟩
    let args : Region := ⟨State.addr s.sp, 12⟩
    let stk : Region := ⟨State.addr s.sp - BitVec.ofNat 64 N, N⟩
    N ≤ s.sp.toNat ∧ s.sp.toNat + 12 ≤ 2 ^ 32 ∧ s.rd = [salt, ikm, tab, args] ∧ s.wr = [prk] ∧
      salt.Disjoint prk ∧ ikm.Disjoint prk ∧ prk.Disjoint tab ∧ prk.Disjoint args ∧
      stk.Disjoint salt ∧ stk.Disjoint ikm ∧ stk.Disjoint prk ∧ stk.Disjoint tab ∧ stk.Disjoint args ∧
      (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32 ∧
      (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 32 ∧ (stackArg s 2).toNat + 24 ≤ 2 ^ 32 ∧
      (stackArg s 1).toNat = w.F.H.D ∧ TabMem w.F s.syms (stackArg s 2) s.mem ∧
      s.mem.readW (tA (stackArg s 2) tB) 32 = BitVec.ofNat 32 w.F.H.B ∧ TabOK w.F f s.syms
  post s s' := bytesAt s'.mem (State.addr (stackArg s 0)) w.F.H.D =
    Spec.Hkdf.extract w.ok.hH.SH.H (bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat)
      (bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧
    stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2 ∧ ∀ n ∈ ns, s₁.syms n = s₂.syms n

/-! ## Where things are -/

section
variable (s : State)

/-- The stack's lowest byte. -/
abbrev B : Addr := base s.sp xFr
/-- The frame's base. -/
abbrev fb : BitVec 32 := s.sp - BitVec.ofNat 32 xFr
/-- An address in the frame. -/
abbrev fA (o : Nat) : Addr := B s + BitVec.ofNat 64 (32 + o)

abbrev saltR : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
abbrev ikmR : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
abbrev prkR : Region := ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩
abbrev tabR : Region := ⟨State.addr (stackArg s 2), 24⟩
abbrev argR : Region := ⟨State.addr s.sp, 12⟩
abbrev stkR : Region := ⟨B s, xStack⟩

/-- The salt, the input keying material, and `K₀`. -/
abbrev saltOf : List Byte := bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat
abbrev ikmOf : List Byte := bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat

end

abbrev k0Of (w : HVar) (s : State) : List Byte := blockKey w.ok.hH.SH.H (saltOf s)

/-- The facts of `extractR`'s precondition, by name. -/
structure XP (w : HVar) (f : Fns) (s : State) : Prop where
  st : StackAt s.sp xFr (B s)
  sp : xStack ≤ s.sp.toNat
  sp12 : s.sp.toNat + 12 ≤ 2 ^ 32
  rd : s.rd = [saltR s, ikmR s, tabR s, argR s]
  wr : s.wr = [prkR s]
  s_p : (saltR s).Disjoint (prkR s)
  i_p : (ikmR s).Disjoint (prkR s)
  p_t : (prkR s).Disjoint (tabR s)
  p_a : (prkR s).Disjoint (argR s)
  k_s : (stkR s).Disjoint (saltR s)
  k_i : (stkR s).Disjoint (ikmR s)
  k_p : (stkR s).Disjoint (prkR s)
  k_t : (stkR s).Disjoint (tabR s)
  k_a : (stkR s).Disjoint (argR s)
  ns : (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32
  ni : (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32
  np : (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 32
  nt : (stackArg s 2).toNat + 24 ≤ 2 ^ 32
  pl : (stackArg s 1).toNat = w.F.H.D
  tm : TabMem w.F s.syms (stackArg s 2) s.mem
  tB : s.mem.readW (tA (stackArg s 2) tB) 32 = BitVec.ofNat 32 w.F.H.B
  tok : TabOK w.F f s.syms

theorem xp_of {w : HVar} {f : Fns} {ns : List String} {s : State} (hp : (extractR w f ns xStack).pre s) :
    XP w f s :=
  let ⟨hsp, h12, hrd, hwr, sp, ip, pt, pa, ks, ki, kp, kt, ka, ns', ni, np, nt, pl, tm, tb, tok⟩ := hp
  ⟨stackAt hsp, hsp, h12, hrd, hwr, sp, ip, pt, pa, ks, ki, kp, kt, ka, ns', ni, np, nt, pl, tm, tb, tok⟩

/-! ## What the code keeps -/

/-- The registers the prologue sets, and the callee-saved ones it does not
save, which the code keeps from then on. -/
abbrev xRegs : List Reg := [.r4, .r5, .r6, .r7, .r8, .r9, .r11]

theorem xRegs_pres : ∀ r ∈ xRegs, r ∈ preserved ∧ r ≠ .lr := by decide

theorem xSaved_slots : Spill.Slots 0 24 xSaved := by decide

/-- What the code writes from the prologue on: the stack (the 32 bytes the
calls use, and the frame after the save area) and `prk`. -/
def Wk (s : State) (r : Region) : Prop :=
  Region.Sub r ⟨B s, 32⟩ ∨ Region.Sub r ⟨B s + BitVec.ofNat 64 64, xFr - 32⟩ ∨ Region.Sub r (prkR s)

/-- The registers and memory kept from the end of the prologue on. -/
structure XR (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = ⟨State.addr (fb s), xFr⟩ :: s.wr
  sp : t.sp = fb s
  sy : t.syms = s.syms
  r4 : t.gpr .r4 = s.gpr .r2
  r5 : t.gpr .r5 = stackArg s 2
  r6 : t.gpr .r6 = stackArg s 0
  r7 : t.gpr .r7 = s.gpr .r3
  cs : ∀ r ∈ [Reg.r8, .r9, .r11], t.gpr r = s.gpr r
  saved : Spill.Saved t.mem (State.addr (fb s)) s.gpr xSaved
  frame : Frame [stkR s, prkR s] s.mem t.mem

section
variable {w : HVar} {f : Fns} {s : State} (hp : XP w f s)
include hp

theorem fA_eq {o : Nat} (ho : o ≤ xFr) : State.addr (fb s + BitVec.ofNat 32 o) = fA s o := hp.st.fo ho

omit hp in
/-- A part of the frame, within the stack. -/
theorem fr_sub {o n : Nat} (h : o + n ≤ xFr) : Region.Sub ⟨fA s o, n⟩ (stkR s) :=
  Offset.sub_base _ (by simp only [xStack]; omega_using [h])

theorem fb_addr : State.addr (fb s) = fA s 0 := hp.st.fb

/-- A part of the frame, in its region. -/
theorem fr_in {t : State} (hwr : t.wr = ⟨State.addr (fb s), xFr⟩ :: s.wr) {o n : Nat} (h : o + n ≤ xFr) :
    InRegions t.wr (fA s o) n :=
  ⟨_, by rw [hwr]; exact List.mem_cons_self .., by
    rw [fb_addr hp]
    have := hp.st.bN; have := s.sp.isLt; have hfr := xFr_eq
    exact Offset.contains _ (by omega_using []) (by omega_using [h]) (by omega_using [h, this, hfr])⟩

theorem fr_in' {t : State} (hwr : t.wr = ⟨State.addr (fb s), xFr⟩ :: s.wr) {o n : Nat} (h : o + n ≤ xFr) :
    InRegions (t.rd ++ t.wr) (fA s o) n :=
  let ⟨r, hr, hc⟩ := fr_in hp hwr h; ⟨r, List.mem_append_right _ hr, hc⟩

/-- The save area is apart from what the code writes from the prologue on. -/
theorem wk_saved {r : Region} (h : Wk s r) : Region.Disjoint ⟨State.addr (fb s) + BitVec.ofNat 64 0, 24 - 0⟩ r := by
  have hs : (⟨State.addr (fb s) + BitVec.ofNat 64 0, 24 - 0⟩ : Region) = ⟨B s + BitVec.ofNat 64 32, 24⟩ := by
    rw [fb_addr hp, BitVec.add_zero]
  rw [hs]
  have hfr := xFr_eq
  rcases h with h | h | h
  · exact (Offset.disjoint_base _ (by decide) (by
      have := hp.st.bN; have := s.sp.isLt; omega_using [this])).sub_right h
  · exact (hp.st.disj (.inl (by decide)) (by omega_using [hfr]) (by omega_using [hfr])).sub_right h
  · exact (hp.k_p.sub_left (fr_sub (o := 0) (n := 24) (by omega_using [hfr]))).sub_right h

/-- What a piece of code leaves keeps `XR`, if it writes only `Wk` regions
and keeps the registers of `xRegs`. -/
theorem XR.keep {t t' : State} (h : XR s t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp)
    (hsy : t'.syms = t.syms) (hg : ∀ r ∈ xRegs, t'.gpr r = t.gpr r) {ws : List Region}
    (hf : Frame ws t.mem t'.mem) (hw : ∀ r ∈ ws, Wk s r) : XR s t' := by
  have hfr := xFr_eq
  refine ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, hsy.trans h.sy, (hg _ (by decide)).trans h.r4,
    (hg _ (by decide)).trans h.r5, (hg _ (by decide)).trans h.r6, (hg _ (by decide)).trans h.r7,
    fun r hr => (hg r (by revert r; decide)).trans (h.cs r hr), h.saved.frame xSaved_slots hf
      fun r hr => wk_saved hp (hw r hr), h.frame.trans (hf.sub fun r hr => ?_)⟩
  rcases hw r hr with h | h | h
  · exact ⟨_, List.mem_cons_self .., fun a ha => Region.sub_prefix (by decide) a (h a ha)⟩
  · exact ⟨_, List.mem_cons_self .., fun a ha => Offset.sub_base _ (by simp only [xStack]; omega_using [hfr])
      a (h a ha)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), h⟩

omit hp in
/-- The bytes of a region apart from the stack and `prk` are as on entry. -/
theorem XR.bytes {t : State} (h : XR s t) {p : Addr} {n : Nat} (hk : Region.Disjoint ⟨p, n⟩ (stkR s))
    (hq : Region.Disjoint ⟨p, n⟩ (prkR s)) (hn : n ≤ 2 ^ 64) : bytesAt t.mem p n = bytesAt s.mem p n :=
  bytes_keep h.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [hk, hq]) hn

theorem XR.saltB {t : State} (h : XR s t) : bytesAt t.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat = saltOf s :=
  h.bytes hp.k_s.symm hp.s_p (Nat.le_of_lt (Nat.lt_trans (s.gpr .r1).isLt (by decide)))

theorem XR.ikmB {t : State} (h : XR s t) : bytesAt t.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat = ikmOf s :=
  h.bytes hp.k_i.symm hp.i_p (Nat.le_of_lt (Nat.lt_trans (s.gpr .r3).isLt (by decide)))

/-- A word of the table is as on entry. -/
theorem XR.tabW {t : State} (h : XR s t) {o : Nat} (ho : o + 4 ≤ 24) :
    t.mem.readW (tA (stackArg s 2) o) 32 = s.mem.readW (tA (stackArg s 2) o) 32 := by
  have hn := hp.nt
  have ha : tA (stackArg s 2) o = State.addr (stackArg s 2) + BitVec.ofNat 64 o :=
    VG.Arm.addr_add (by omega_using [hn, ho])
  rw [ha]
  exact h.frame.readW (r := tabR s) (Offset.contains_base _ ho (by omega_using [ho])) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [hp.k_t.symm, hp.p_t.symm]) (by decide)

theorem tin {t : State} (h : XR s t) {o : Nat} (ho : o + 4 ≤ 24) :
    InRegions (t.rd ++ t.wr) (tA (stackArg s 2) o) 4 := by
  have hn := hp.nt
  have ha : tA (stackArg s 2) o = State.addr (stackArg s 2) + BitVec.ofNat 64 o :=
    VG.Arm.addr_add (by omega_using [hn, ho])
  rw [ha]
  exact ⟨tabR s, List.mem_append_left _ (by rw [h.rd, hp.rd]; simp), Offset.contains_base _ ho (by omega_using [ho])⟩

/-- The table's function `j`, through the table in `r5`. -/
theorem tabFn {t : State} (h : XR s t) {j : Nat} (hj : j < 3) {n : String} {c : Prog isa}
    {ts : List (String × Prog isa)} (hw : s.mem.readW (tA (stackArg s 2) (4 * j)) 32 = s.syms n)
    (hf : ts.find? (fun q => (s.syms q.1).setWidth 64 == (s.syms n).setWidth 64) = some (n, c)) :
    TabFn t .r5 j n c ts := by
  refine ⟨by omega_using [hj], ?_, ?_, ?_⟩
  · rw [h.r5]; exact tin hp h (by omega_using [hj])
  · rw [h.r5, h.sy]; exact (h.tabW hp (by omega_using [hj])).trans hw
  · rw [h.sy]; exact hf

end

/-! ## The prologue -/

theorem pro_eq : extractPro = .addSp .r12 0 :: (xSaved.map (fun p => Instr.str p.1 .r12 p.2) ++
    ([.mov .r4 (.reg .r2), .mov .r7 (.reg .r3), .ldr .r6 .r12 xFr, .ldr .r5 .r12 (xFr + 8), .mov .r2 (.reg .r0),
      .mov .r3 (.reg .r1), Impl.AesGcm.Arm.addI .r0 .r12 xIn, Impl.AesGcm.Arm.addI .r1 .r12 xOut,
      Impl.AesGcm.Arm.addI .r12 .r12 xWork] : List Instr)) := rfl

theorem argAddr0 (s : State) : stackArgAddr s 0 = State.addr s.sp := by
  simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]

theorem fb_xFr (s : State) : fb s + BitVec.ofNat 32 xFr = s.sp := BitVec.sub_add_cancel _ _

theorem fb_xFr8 (s : State) : fb s + BitVec.ofNat 32 (xFr + 8) = s.sp + BitVec.ofNat 32 (4 * 2) := by
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, fb_xFr]

/-- After the prologue: `XR`, and `init`'s arguments. -/
structure XA (s t : State) : Prop where
  xr : XR s t
  r0 : t.gpr .r0 = fb s + BitVec.ofNat 32 xIn
  r1 : t.gpr .r1 = fb s + BitVec.ofNat 32 xOut
  r2 : t.gpr .r2 = s.gpr .r0
  r3 : t.gpr .r3 = s.gpr .r1
  r12 : t.gpr .r12 = fb s + BitVec.ofNat 32 xWork

section
variable {w : HVar} {f : Fns} {s : State} (hp : XP w f s)
include hp

theorem fb_add (d : Nat) : State.addr (fb s) + BitVec.ofNat 64 d = fA s d := by
  rw [fb_addr hp, fA, fA, Offset.add_add, Nat.add_zero]

/-- The save area, as `Spill` states it, in the stack. -/
theorem saved_sub : Region.Sub ⟨State.addr (fb s) + BitVec.ofNat 64 0, 24 - 0⟩ (stkR s) := by
  rw [fb_add hp]; exact fr_sub (by decide)

theorem pro_ok : WP isa (.block extractPro) (allocated xFr s) (XA s) := by
  have hfr := xFr_eq
  apply WP.of_syms
  rw [pro_eq]
  refine wp_addSp (by decide) fun t₁ u₁ => ?_
  have h12 : t₁.gpr .r12 = fb s := by rw [u₁.gpr, BitVec.add_zero]; rfl
  refine Spill.saveList_ok xSaved t₁ _ (fun p hp' => by
      have hb := xSaved_slots.bound hp'
      have h1 : (fb s).toNat + xFr = s.sp.toNat := hp.st.fbN
      have h2 := s.sp.isLt
      refine ⟨by omega_using [hb], by rw [h12]; omega_using [hb, h1, h2, hfr], ?_⟩
      rw [h12, fb_add hp, u₁.wr]; exact fr_in hp rfl (by omega_using [hb, hfr]))
    fun t₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  have hsm : Spill.saveMem t₁.mem (State.addr (t₁.gpr .r12)) t₁.gpr xSaved =
      Spill.saveMem s.mem (State.addr (fb s)) s.gpr xSaved := by
    rw [h12, u₁.mem]
    exact Spill.saveMem_congr _ _ _ fun p hp' => by
      rw [u₁.other _ (by revert p; decide)]; rfl
  -- The stack arguments, apart from the save area.
  have hsa : ∀ (i : Nat), i < 3 → (Spill.saveMem s.mem (State.addr (fb s)) s.gpr xSaved).readW (stackArgAddr s i) 32 =
      stackArg s i := fun i hi => by
    have hc : (argR s).Contains (stackArgAddr s i) (32 / 8) := by
      have := hp.sp12
      rw [stackArgAddr, VG.Arm.addr_add (by omega_using [this, hi])]
      exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])
    exact (Spill.saveMem_frame_slots xSaved_slots _ _ _).readW hc (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.k_a.symm.sub_right (saved_sub hp)) (by decide)
  refine wp_movr fun t₃ u₃ => wp_movr fun t₄ u₄ => ?_
  have r12₄ : t₄.gpr .r12 = fb s := by rw [u₄.other _ (by decide), u₃.other _ (by decide), g₂]; exact h12
  have rd₄ : t₄.rd = s.rd := by rw [u₄.rd, u₃.rd, rd₂]; exact u₁.rd
  have m₄ : t₄.mem = Spill.saveMem s.mem (State.addr (fb s)) s.gpr xSaved := by
    rw [u₄.mem, u₃.mem, m₂]; exact hsm
  have ina : ∀ (i : Nat), i < 3 → InRegions (t₄.rd ++ t₄.wr) (stackArgAddr s i) 4 := fun i hi => by
    have := hp.sp12
    refine ⟨argR s, List.mem_append_left _ (by rw [rd₄, hp.rd]; simp), ?_⟩
    rw [stackArgAddr, VG.Arm.addr_add (by omega_using [this, hi])]
    exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])
  refine wp_ldr (a := stackArgAddr s 0) (by decide) (by rw [r12₄, fb_xFr, argAddr0]) (ina 0 (by decide))
    fun t₅ u₅ => ?_
  refine wp_ldr (a := stackArgAddr s 2) (by decide) (by rw [u₅.other _ (by decide), r12₄, fb_xFr8]; rfl)
    (by rw [u₅.rd, u₅.wr]; exact ina 2 (by decide)) fun t₆ u₆ => ?_
  refine wp_movr fun t₇ u₇ => wp_movr fun t₈ u₈ => wp_addi (by decide) fun t₉ u₉ =>
    wp_addi (by decide) fun t₁₀ u₁₀ => wp_addi (by decide) fun t₁₁ u₁₁ => WP.block_nil fun sy => ?_
  have m₁₁ : t₁₁.mem = Spill.saveMem s.mem (State.addr (fb s)) s.gpr xSaved := by
    rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, m₄]
  have r12₈ : t₈.gpr .r12 = fb s := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide)]
    exact r12₄
  have a0 : (allocated xFr s).gpr = s.gpr := rfl
  refine ⟨⟨?_, ?_, ?_, sy, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, rd₄]
  · rw [u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr]; rfl
  · rw [u₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp]; rfl
  · upd_simp [u₁₁.other, u₁₀.other, u₉.other, u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.gpr, g₂,
      u₁.other, a0]
  · upd_simp [u₁₁.other, u₁₀.other, u₉.other, u₈.other, u₇.other, u₆.gpr, u₅.mem, m₄]; exact hsa 2 (by decide)
  · upd_simp [u₁₁.other, u₁₀.other, u₉.other, u₈.other, u₇.other, u₆.other, u₅.gpr, m₄, argAddr0]
    have := hsa 0 (by decide); rwa [argAddr0] at this
  · upd_simp [u₁₁.other, u₁₀.other, u₉.other, u₈.other, u₇.other, u₆.other, u₅.other, u₄.gpr, u₃.other, g₂,
      u₁.other, a0]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    all_goals upd_simp [u₁₁.other, u₁₀.other, u₉.other, u₈.other, u₇.other, u₆.other, u₅.other, u₄.other,
      u₃.other, g₂, u₁.other, a0]
  · intro q hq
    rw [m₁₁]; exact Spill.saveMem_saved (State.addr (fb s)) s.gpr s.mem xSaved xSaved_slots q hq
  · rw [m₁₁]
    exact (Spill.saveMem_frame_slots xSaved_slots _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., saved_sub hp⟩
  · upd_simp [u₁₁.other, u₁₀.other, u₉.gpr, r12₈]
  · upd_simp [u₁₁.other, u₁₀.gpr, u₉.other, r12₈]
  · upd_simp [u₁₁.other, u₁₀.other, u₉.other, u₈.other, u₇.gpr, u₆.other, u₅.other, u₄.other, u₃.other, g₂,
      u₁.other, a0]
  · upd_simp [u₁₁.other, u₁₀.other, u₉.other, u₈.gpr, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, g₂,
      u₁.other, a0]
  · upd_simp [u₁₁.gpr, u₁₀.other, u₉.other, r12₈]

omit hp in
/-- A part of the frame after the save area. -/
theorem wk_fr {o n : Nat} (h₁ : 32 ≤ o) (h₂ : o + n ≤ xFr) : Wk s ⟨fA s o, n⟩ := by
  have hfr := xFr_eq
  exact .inr (.inl (Offset.sub _ (by omega_using [h₁]) (by omega_using [h₂, hfr])))

/-- What writes only a register outside `xRegs` keeps `XR`. -/
theorem XR.upd {t t' : State} (h : XR s t) {d : Reg} {v : BitVec 32} (u : Upd t t' d v) (hd : d ∉ xRegs) :
    XR s t' :=
  h.keep hp u.rd u.wr u.sp u.syms (fun r hr => u.other r fun e => hd (e ▸ hr)) (ws := [])
    (by rw [u.mem]; exact Frame.refl _ _) fun _ h => absurd h List.not_mem_nil

/-- The 32 bytes below the frame, from a stack pointer at the frame's base. -/
theorem below32 {t : State} (ht : t.sp = fb s) :
    (⟨State.addr t.sp - BitVec.ofNat 64 32, 32⟩ : Region) = ⟨B s, 32⟩ := by
  rw [ht, hp.st.below32]

/-- The 24 bytes below the frame, from a stack pointer at the frame's base. -/
theorem stk24 {t : State} (ht : t.sp = fb s) : Proof.Pbkdf2.Whole.Arm.stk t = ⟨B s + BitVec.ofNat 64 8, 24⟩ := by
  show (⟨State.addr t.sp - 24, 24⟩ : Region) = _
  rw [ht, hp.st.stk24]

theorem stk24_wk {t : State} (ht : t.sp = fb s) : Wk s (Proof.Pbkdf2.Whole.Arm.stk t) := by
  rw [stk24 hp ht]; exact .inl (Offset.sub_base _ (by decide))

/-- The 16 bytes below the frame, from a stack pointer at the frame's base. -/
theorem stk16 {t : State} (ht : t.sp = fb s) :
    Pbkdf2.Stream.Arm.below t = ⟨B s + BitVec.ofNat 64 16, 16⟩ := by
  show (⟨State.addr t.sp - 16, 16⟩ : Region) = _
  rw [ht, hp.st.stk16]

theorem stk16_wk {t : State} (ht : t.sp = fb s) : Wk s (Pbkdf2.Stream.Arm.below t) := by
  rw [stk16 hp ht]; exact .inl (Offset.sub_base _ (by decide))

/-- An offset in the frame, as a number. -/
theorem fbN {o : Nat} (ho : o ≤ xFr) : (fb s + BitVec.ofNat 32 o).toNat = (fb s).toNat + o := hp.st.foN ho

theorem fbN' : (fb s).toNat + xFr ≤ 2 ^ 32 := by
  have h1 : (fb s).toNat + xFr = s.sp.toNat := hp.st.fbN
  have := s.sp.isLt; omega_using [h1, this]

/-- Two parts of the frame apart. -/
theorem fr_disj {o n o' n' : Nat} (h₁ : o + n ≤ o' ∨ o' + n' ≤ o) (h₂ : o + n ≤ xFr) (h₃ : o' + n' ≤ xFr) :
    Region.Disjoint ⟨fA s o, n⟩ ⟨fA s o', n'⟩ := by
  have hfr := xFr_eq
  exact hp.st.disj (.imp (fun h => by omega_using [h]) (fun h => by omega_using [h]) h₁) (by omega_using [h₂, hfr])
    (by omega_using [h₃, hfr])

/-- The 32 bytes below the frame, apart from a part of it. -/
theorem b32_fr {o n : Nat} (h : o + n ≤ xFr) : Region.Disjoint ⟨B s, 32⟩ ⟨fA s o, n⟩ := by
  have hfr := xFr_eq; have := hp.st.bN; have := s.sp.isLt
  exact Offset.base_disjoint _ (by omega_using []) (by omega_using [h, hfr, this])

/-- A part of the frame, among the writable regions. -/
theorem fr_cov {t : State} (hwr : t.wr = ⟨State.addr (fb s), xFr⟩ :: s.wr) {o n : Nat} (h : o + n ≤ xFr) :
    ∃ r' ∈ t.wr, ∃ off, fA s o = r'.base + BitVec.ofNat 64 off ∧ off + n ≤ r'.len :=
  ⟨_, by rw [hwr]; exact List.mem_cons_self .., o, (fb_add hp o).symm, h⟩

/-- After `init`: `XR`, and HMAC's states for `K₀`. -/
structure XI (w : HVar) (s t : State) : Prop where
  xr : XR s t
  inn : w.ok.hH.SH.Repr t.mem (fA s xIn) (xorPad (k0Of w s) ipad)
  out : w.ok.hH.SH.Repr t.mem (fA s xOut) (xorPad (k0Of w s) opad)

theorem init_args (hw : HOk w) {t u : State} (h : XA s t) {v : BitVec 32} (hu : Upd t u .lr v) :
    AnyArgs w.ok.hH.SH (w.F.W + w.F.H.S) u (fb s + BitVec.ofNat 32 xIn) (fb s + BitVec.ofNat 32 xOut) (s.gpr .r0)
      (fb s + BitVec.ofNat 32 xWork) (s.gpr .r1).toNat := by
  have k := h.xr
  have hfr := xFr_eq; have hS := hw.hS; have hA := hw.hA; have hwk := work_eq
  have hsb := stateBytes_eq w; have hxi := xIn_eq; have hxo := xOut_eq; have hxw := xWork_eq
  have hS' : w.ok.hH.SH.stateBytes ≤ 192 := by omega_using [hS, hsb]
  have hfN := fbN' hp
  have ku : XR s u := k.upd hp hu (by decide)
  have e0 := fA_eq hp (o := xIn) (by decide)
  have e1 := fA_eq hp (o := xOut) (by decide)
  have e3 := fA_eq hp (o := xWork) (by decide)
  have hb := below32 hp ku.sp
  exact
    { r0 := by rw [hu.other _ (by decide)]; exact h.r0
      r1 := by rw [hu.other _ (by decide)]; exact h.r1
      r2 := by rw [hu.other _ (by decide)]; exact h.r2
      r3 := by rw [hu.other _ (by decide), h.r3, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      r12 := by rw [hu.other _ (by decide)]; exact h.r12
      kl32 := (s.gpr .r1).isLt
      sp := by rw [ku.sp]; have h1 : (fb s).toNat + xFr = s.sp.toNat := hp.st.fbN; have := hp.sp
               simp only [xStack] at this; omega_using [h1, this]
      cr := VG.Covers.left (by rw [ku.rd, hp.rd]; exact VG.Covers.of_mem fun r hr => by simp at hr; subst hr; simp)
      cw := by
        refine VG.Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [e0]; exact fr_cov hp ku.wr (o := xIn) (n := w.ok.hH.SH.stateBytes) (by omega_using [hS', hfr, hxi])
        · rw [e1]; exact fr_cov hp ku.wr (o := xOut) (n := w.ok.hH.SH.stateBytes) (by omega_using [hS', hfr, hxo])
        · rw [e3]; exact fr_cov hp ku.wr (o := xWork) (n := (w.F.W + w.F.H.S) * 8) (by omega_using [hA, hwk, hfr, hxw])
      i_o := by rw [e0, e1]; exact fr_disj hp (.inl (by omega_using [hS', hxi, hxo])) (by omega_using [hS', hfr, hxi])
                  (by omega_using [hS', hfr, hxo])
      i_k := by rw [e0]; exact hp.k_s.symm.sub_right (fr_sub (o := xIn) (n := w.ok.hH.SH.stateBytes)
                  (by omega_using [hS', hfr, hxi])) |>.symm
      i_s := by rw [e0, e3]; exact fr_disj hp (.inl (by omega_using [hS', hxi, hxw])) (by omega_using [hS', hfr, hxi])
                  (by omega_using [hA, hwk, hfr, hxw])
      o_k := by rw [e1]; exact hp.k_s.symm.sub_right (fr_sub (o := xOut) (n := w.ok.hH.SH.stateBytes)
                  (by omega_using [hS', hfr, hxo])) |>.symm
      o_s := by rw [e1, e3]; exact fr_disj hp (.inl (by omega_using [hS', hxo, hxw])) (by omega_using [hS', hfr, hxo])
                  (by omega_using [hA, hwk, hfr, hxw])
      k_s := by rw [e3]; exact hp.k_s.symm.sub_right (fr_sub (o := xWork) (n := (w.F.W + w.F.H.S) * 8)
                  (by omega_using [hA, hwk, hfr, hxw]))
      b_i := by rw [hb, e0]; exact b32_fr hp (o := xIn) (n := w.ok.hH.SH.stateBytes) (by omega_using [hS', hfr, hxi])
      b_o := by rw [hb, e1]; exact b32_fr hp (o := xOut) (n := w.ok.hH.SH.stateBytes) (by omega_using [hS', hfr, hxo])
      b_k := by rw [hb]; exact hp.k_s.sub_left (Region.sub_prefix (by decide))
      b_s := by rw [hb, e3]; exact b32_fr hp (o := xWork) (n := (w.F.W + w.F.H.S) * 8)
                  (by omega_using [hA, hwk, hfr, hxw])
      ni := by rw [fbN hp (by decide)]; omega_using [hS', hfr, hfN, hxi]
      no := by rw [fbN hp (by decide)]; omega_using [hS', hfr, hfN, hxo]
      nk := hp.ns
      nsc := by rw [fbN hp (by decide)]; omega_using [hA, hwk, hfr, hfN, hxw] }

theorem init_ok (hw : HOk w) {t : State} (h : XA s t) :
    WP isa (tcall .r5 0 f.init [.r12, .lr] .r12 8) t (XI w s) := by
  have k := h.xr
  have hfr := xFr_eq; have hS := hw.hS; have hA := hw.hA; have hwk := work_eq
  have hsb := stateBytes_eq w; have hxi := xIn_eq; have hxo := xOut_eq; have hxw := xWork_eq
  have hS' : w.ok.hH.SH.stateBytes ≤ 192 := by omega_using [hS, hsb]
  have hfN := fbN' hp
  refine tcall_ok (n := w.F.hiAnyN) (c := w.F.hmacInitAny) (tabFn hp k (j := 0) (by decide) hp.tm.1 hp.tok.i)
    fun u hu => ?_
  have ku : XR s u := k.upd hp hu (by decide)
  have e0 := fA_eq hp (o := xIn) (by decide)
  have e1 := fA_eq hp (o := xOut) (by decide)
  have e3 := fA_eq hp (o := xWork) (by decide)
  have hb := below32 hp ku.sp
  apply WP.of_syms
  refine any_frame (reprOK w) (by rw [hsb]; have := w.ok.hH.hSB; omega_using [this]) w.any w.scrub.1.1
    (s := u) (inn := fb s + BitVec.ofNat 32 xIn) (out := fb s + BitVec.ofNat 32 xOut) (k := s.gpr .r0)
    (sc := fb s + BitVec.ofNat 32 xWork) (kl := (s.gpr .r1).toNat)
    (init_args hp hw h hu) fun s' ha hi ho sy => ?_
  have k' : XR s s' := ku.keep hp ha.rd ha.wr ha.sp sy (fun r hr => ha.cs r (xRegs_pres r hr).1 (xRegs_pres r hr).2)
    ha.frame fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [e0]; exact wk_fr (o := xIn) (n := w.ok.hH.SH.stateBytes) (by decide) (by omega_using [hS', hfr, hxi])
      · rw [e1]; exact wk_fr (o := xOut) (n := w.ok.hH.SH.stateBytes) (by decide) (by omega_using [hS', hfr, hxo])
      · rw [e3]; exact wk_fr (o := xWork) (n := (w.F.W + w.F.H.S) * 8) (by decide)
          (by omega_using [hA, hwk, hfr, hxw])
      · exact stk24_wk hp ku.sp
  rw [hu.mem, k.saltB hp, e0] at hi
  rw [hu.mem, k.saltB hp, e1] at ho
  exact ⟨k', hi, ho⟩

/-! ## `update` -/

/-- After `update`'s arguments. -/
structure XUA (w : HVar) (s t : State) : Prop where
  xi : XI w s t
  r0 : t.gpr .r0 = fb s + BitVec.ofNat 32 xIn
  r1 : t.gpr .r1 = s.gpr .r2
  r2 : t.gpr .r2 = BitVec.ofNat 32 w.F.H.B
  r3 : t.gpr .r3 = 0
  r10 : t.gpr .r10 = fb s + BitVec.ofNat 32 xWork

/-- After `update`: the inner state holds the input keying material too. -/
structure XU (w : HVar) (s t : State) : Prop where
  xr : XR s t
  inn : w.ok.hH.SH.Repr t.mem (fA s xIn) (xorPad (k0Of w s) ipad ++ ikmOf s)
  out : w.ok.hH.SH.Repr t.mem (fA s xOut) (xorPad (k0Of w s) opad)

theorem updArgs_ok {t : State} (h : XI w s t) : WP isa (.block extractUpd) t (XUA w s) := by
  obtain ⟨k, hI, hO⟩ := h
  unfold extractUpd
  refine wp_addSp (by decide) fun t₁ u₁ => wp_addi (by decide) fun t₂ u₂ => wp_movr fun t₃ u₃ => ?_
  have k₃ : XR s t₃ := ((k.upd hp u₁ (by decide)).upd hp u₂ (by decide)).upd hp u₃ (by decide)
  refine wp_ldr (a := tA (stackArg s 2) tB) (by decide) (by rw [k₃.r5]) (tin hp k₃ (by decide))
    fun t₄ u₄ => ?_
  refine wp_movi (by decide) fun t₅ u₅ => wp_addi (by decide) fun t₆ u₆ => WP.block_nil ?_
  have k₆ : XR s t₆ := ((k₃.upd hp u₄ (by decide)).upd hp u₅ (by decide)).upd hp u₆ (by decide)
  have m₆ : t₆.mem = t.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have h12 : t₁.gpr .r12 = fb s := by rw [u₁.gpr, k.sp, BitVec.add_zero]
  refine ⟨⟨k₆, by rw [m₆]; exact hI, by rw [m₆]; exact hO⟩, ?_, ?_, ?_, ?_, ?_⟩
  · upd_simp [u₆.other, u₅.other, u₄.other, u₃.other, u₂.gpr, h12]
  · upd_simp [u₆.other, u₅.other, u₄.other, u₃.gpr, u₂.other, u₁.other, k.r4]
  · upd_simp [u₆.other, u₅.other, u₄.gpr, u₃.mem, u₂.mem, u₁.mem]
    rw [k.tabW hp (by decide)]; exact hp.tB
  · upd_simp [u₆.other, u₅.gpr]; rfl
  · upd_simp [u₆.gpr, u₅.other, u₄.other, u₃.other, u₂.other, h12]

/-- The input keying material fits HMAC's count with a block of key. -/
theorem ikm_lt : w.F.H.B + (s.gpr .r3).toNat < 2 ^ 32 := by
  have h := Proof.Pbkdf2.Whole.len_add_le hp.k_i (N := 2 ^ 32) (by
      show (B s).toNat + xStack ≤ 2 ^ 32
      have h1 := hp.st.bN; have h2 := s.sp.isLt; have hx : xStack = xFr + 32 := rfl
      omega_using [h1, h2, hx])
    (by show (State.addr (s.gpr .r2)).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32; rw [toNat_addr]; exact hp.ni)
  have hB := w.ok.hH.hBB
  have h' : xStack + (s.gpr .r3).toNat ≤ 2 ^ 32 := h
  have hx := xStack_eq
  omega_using [h', hB, hx]

theorem upd_args (hw : HOk w) {t u : State} (h : XUA w s t) {v : BitVec 32} (hu : Upd t u .lr v) :
    Proof.Pbkdf2.Whole.Arm.UpdL w.ok.hH u (fb s + BitVec.ofNat 32 xIn) (s.gpr .r2) (fb s + BitVec.ofNat 32 xWork)
      (s.gpr .r3).toNat := by
  have k := h.xi.xr
  have hfr := xFr_eq; have hS := hw.hS; have hWb := hw.hWb; have hxi := xIn_eq; have hxw := xWork_eq
  have hfN := fbN' hp
  have ku : XR s u := k.upd hp hu (by decide)
  have e0 := fA_eq hp (o := xIn) (by decide)
  have e3 := fA_eq hp (o := xWork) (by decide)
  have hb := stk16 hp ku.sp
  have hbs : Region.Sub ⟨B s + BitVec.ofNat 64 16, 16⟩ (stkR s) := Offset.sub_base _ (by decide)
  exact
    { r0 := by rw [hu.other _ (by decide)]; exact h.r0
      r1 := by rw [hu.other _ (by decide)]; exact h.r1
      r7 := by rw [hu.other _ (by decide), k.r7, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      r10 := by rw [hu.other _ (by decide)]; exact h.r10
      hlen := (s.gpr .r3).isLt
      sp16 := by
        rw [ku.sp]; have h1 : (fb s).toNat + xFr = s.sp.toNat := hp.st.fbN; have := hp.sp
        simp only [xStack] at this; omega_using [h1, this]
      cd := VG.Covers.left (by rw [ku.rd, hp.rd]; exact VG.Covers.of_mem fun r hr => by simp at hr; subst hr; simp)
      cw := by
        refine VG.Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [e0]; exact fr_cov hp ku.wr (o := xIn) (n := w.F.H.S) (by omega_using [hS, hfr, hxi])
        · rw [e3]; exact fr_cov hp ku.wr (o := xWork) (n := w.ok.hH.Wb) (by omega_using [hWb, hfr, hxw])
      st_sc := by rw [e0, e3]; exact fr_disj hp (.inl (by omega_using [hS, hxi, hxw])) (by omega_using [hS, hfr, hxi])
                      (by omega_using [hWb, hfr, hxw])
      d_st := by rw [e0]; exact hp.k_i.symm.sub_right (fr_sub (o := xIn) (n := w.F.H.S) (by omega_using [hS, hfr, hxi]))
      d_sc := by rw [e3]; exact hp.k_i.symm.sub_right (fr_sub (o := xWork) (n := w.ok.hH.Wb)
                      (by omega_using [hWb, hfr, hxw]))
      b_st := by rw [hb, e0]; exact hp.st.disj (.inl (by omega_using [hxi])) (by decide)
                      (by omega_using [hS, hfr, hxi])
      b_d := by rw [hb]; exact hp.k_i.sub_left hbs
      b_sc := by rw [hb, e3]; exact hp.st.disj (.inl (by omega_using [hxw])) (by decide)
                      (by omega_using [hWb, hfr, hxw])
      nst := by rw [fbN hp (by decide)]; omega_using [hS, hfr, hfN, hxi]
      nd := hp.ni
      nsc := by rw [fbN hp (by decide)]; omega_using [hWb, hfr, hfN, hxw] }

theorem upd_ok (hw : HOk w) {t : State} (h : XUA w s t) : WP isa (callUpd .r5 f) t (XU w s) := by
  have k := h.xi.xr
  have hfr := xFr_eq; have hS := hw.hS; have hWb := hw.hWb; have hxi := xIn_eq; have hxw := xWork_eq
  have hfN := fbN' hp
  refine tcall_ok (n := w.F.H.updN) (c := w.F.H.updC) (tabFn hp k (j := 1) (by decide) hp.tm.2.1 hp.tok.u)
    fun u hu => ?_
  have ku : XR s u := k.upd hp hu (by decide)
  have e0 := fA_eq hp (o := xIn) (by decide)
  have e3 := fA_eq hp (o := xWork) (by decide)
  have hb := stk16 hp ku.sp
  have hbs : Region.Sub ⟨B s + BitVec.ofNat 64 16, 16⟩ (stkR s) := Offset.sub_base _ (by decide)
  apply WP.of_syms
  refine Proof.Pbkdf2.Whole.Arm.upd_frame w.ok.hH (s := u) (st := fb s + BitVec.ofNat 32 xIn) (d := s.gpr .r2)
    (sc := fb s + BitVec.ofNat 32 xWork) (len := (s.gpr .r3).toNat)
    (upd_args hp hw h hu) fun s' af hr sy => ?_
  have k' : XR s s' := ku.keep hp af.rd af.wr af.sp sy (fun r hr => af.cs r (xRegs_pres r hr).1 (xRegs_pres r hr).2)
    af.frame fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [e0]; exact wk_fr (o := xIn) (n := w.F.H.S) (by decide) (by omega_using [hS, hfr, hxi])
      · rw [e3]; exact wk_fr (o := xWork) (n := w.ok.hH.Wb) (by decide) (by omega_using [hWb, hfr, hxw])
      · exact stk16_wk hp ku.sp
  have hm : u.mem = t.mem := hu.mem
  have hl : (xorPad (k0Of w s) ipad).length = w.F.H.B := by
    rw [Proof.Hmac.Common.xorPad_length, blockKey_len hw]
  have hBl := ikm_lt hp (w := w)
  refine ⟨k', ?_, ?_⟩
  · have := hr (xorPad (k0Of w s) ipad) (by rw [hm, e0]; exact h.xi.inn) (by
      rw [Pbkdf2.Stream.Arm.count, hu.other _ (by decide), hu.other _ (by decide), h.r3, h.r2, hl]
      exact append_zero (by omega_using [hBl]))
    rwa [e0, hm, k.ikmB hp] at this
  · refine repr_keep w af.frame (fun r hr => ?_) (by rw [hm]; exact h.xi.out)
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · have hxo := xOut_eq
      rw [e0]; exact fr_disj hp (.inr (by omega_using [hS, hxi, hxo])) (by omega_using [hS, hfr, hxo])
        (by omega_using [hS, hfr, hxi])
    · have hxo := xOut_eq
      rw [e3]; exact fr_disj hp (.inl (by omega_using [hS, hxw, hxo])) (by omega_using [hS, hfr, hxo])
        (by omega_using [hWb, hfr, hxw])
    · have hxo := xOut_eq
      rw [hb]; exact (hp.st.disj (.inl (by omega_using [hxo])) (by decide) (by omega_using [hS, hfr, hxo])).symm

/-! ## `finalize` -/

/-- After `finalize`'s arguments. -/
structure XFA (w : HVar) (s t : State) : Prop where
  xu : XU w s t
  r0 : t.gpr .r0 = fb s + BitVec.ofNat 32 xIn
  r1 : t.gpr .r1 = fb s + BitVec.ofNat 32 xOut
  r2 : t.gpr .r2 = BitVec.ofNat 32 w.F.H.B + s.gpr .r3
  r3 : t.gpr .r3 = 0
  r10 : t.gpr .r10 = stackArg s 0
  r12 : t.gpr .r12 = fb s + BitVec.ofNat 32 xWork

/-- After `finalize`: `PRK`. -/
structure XF (w : HVar) (s t : State) : Prop where
  xr : XR s t
  prk : bytesAt t.mem (State.addr (stackArg s 0)) w.F.H.D = hmacBlockKey w.ok.hH.SH.H (k0Of w s) (ikmOf s)

theorem finArgs_ok {t : State} (h : XU w s t) : WP isa (.block extractFin) t (XFA w s) := by
  obtain ⟨k, hI, hO⟩ := h
  unfold extractFin
  refine wp_addSp (by decide) fun t₁ u₁ => wp_addi (by decide) fun t₂ u₂ => wp_addi (by decide) fun t₃ u₃ => ?_
  have k₃ : XR s t₃ := ((k.upd hp u₁ (by decide)).upd hp u₂ (by decide)).upd hp u₃ (by decide)
  refine wp_ldr (a := tA (stackArg s 2) tB) (by decide) (by rw [k₃.r5]) (tin hp k₃ (by decide))
    fun t₄ u₄ => ?_
  refine wp_addr fun t₅ u₅ => wp_movi (by decide) fun t₆ u₆ => wp_movr fun t₇ u₇ =>
    wp_addi (by decide) fun t₈ u₈ => WP.block_nil ?_
  have k₈ : XR s t₈ :=
    ((((k₃.upd hp u₄ (by decide)).upd hp u₅ (by decide)).upd hp u₆ (by decide)).upd hp u₇ (by decide)).upd hp u₈
      (by decide)
  have m₈ : t₈.mem = t.mem := by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have h12 : t₁.gpr .r12 = fb s := by rw [u₁.gpr, k.sp, BitVec.add_zero]
  refine ⟨⟨k₈, by rw [m₈]; exact hI, by rw [m₈]; exact hO⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · upd_simp [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.gpr, h12]
  · upd_simp [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.gpr, u₂.other, h12]
  · upd_simp [u₈.other, u₇.other, u₆.other, u₅.gpr, u₄.gpr, u₄.other, u₃.other, u₂.other, u₁.other, k.r7,
      u₃.mem, u₂.mem, u₁.mem]
    rw [k.tabW hp (by decide), hp.tB]
  · upd_simp [u₈.other, u₇.other, u₆.gpr]; rfl
  · upd_simp [u₈.other, u₇.gpr, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other, u₁.other, k.r6]
  · upd_simp [u₈.gpr, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other, h12]

theorem fin_args (hw : HOk w) {t u : State} (h : XFA w s t) {v : BitVec 32} (hu : Upd t u .lr v) :
    Proof.Pbkdf2.Whole.Arm.HfArgs w.ok.hH.SH w.ok.Wf u (fb s + BitVec.ofNat 32 xIn) (fb s + BitVec.ofNat 32 xOut)
      (stackArg s 0) (fb s + BitVec.ofNat 32 xWork) := by
  have k := h.xu.xr
  have hfr := xFr_eq; have hS := hw.hS; have hW := hw.hW; have hxi := xIn_eq; have hxo := xOut_eq
  have hxw := xWork_eq; have hfN := fbN' hp; have hsb := stateBytes_eq w
  have hdb : w.ok.hH.SH.digestBytes = w.F.H.D := w.ok.hH.hD
  have hS' : w.ok.hH.SH.stateBytes ≤ 192 := by omega_using [hS, hsb]
  have ku : XR s u := k.upd hp hu (by decide)
  have e0 := fA_eq hp (o := xIn) (by decide)
  have e1 := fA_eq hp (o := xOut) (by decide)
  have e3 := fA_eq hp (o := xWork) (by decide)
  have hb := stk24 hp ku.sp
  have hbs : Region.Sub ⟨B s + BitVec.ofNat 64 8, 24⟩ (stkR s) := Offset.sub_base _ (by decide)
  have hpS : Region.Sub ⟨State.addr (stackArg s 0), w.ok.hH.SH.digestBytes⟩ (prkR s) :=
    Region.sub_prefix (by rw [hdb, hp.pl])
  exact
    { r0 := by rw [hu.other _ (by decide)]; exact h.r0
      r1 := by rw [hu.other _ (by decide)]; exact h.r1
      r10 := by rw [hu.other _ (by decide)]; exact h.r10
      r12 := by rw [hu.other _ (by decide)]; exact h.r12
      sp := by
        rw [ku.sp]; have h1 : (fb s).toNat + xFr = s.sp.toNat := hp.st.fbN; have := hp.sp
        simp only [xStack] at this; omega_using [h1, this]
      cr := VG.Covers.right (VG.Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [e1]; exact fr_cov hp ku.wr (o := xOut) (n := w.ok.hH.SH.stateBytes) (by omega_using [hS', hfr, hxo]))
      cw := by
        refine VG.Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [e0]; exact fr_cov hp ku.wr (o := xIn) (n := w.ok.hH.SH.stateBytes) (by omega_using [hS', hfr, hxi])
        · exact ⟨prkR s, by rw [ku.wr, hp.wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _), 0,
            (BitVec.add_zero _).symm, by dsimp only; have hpl := hp.pl; omega_using [hdb, hpl]⟩
        · rw [e3]; exact fr_cov hp ku.wr (o := xWork) (n := w.ok.Wf * 8) (by omega_using [hW, hfr, hxw])
      i_u := by rw [e0, e1]; exact fr_disj hp (.inl (by omega_using [hS', hxi, hxo])) (by omega_using [hS', hfr, hxi])
                    (by omega_using [hS', hfr, hxo])
      i_o := by rw [e0]; exact (hp.k_p.sub_left (fr_sub (o := xIn) (n := w.ok.hH.SH.stateBytes)
                    (by omega_using [hS', hfr, hxi]))).sub_right hpS
      i_s := by rw [e0, e3]; exact fr_disj hp (.inl (by omega_using [hS', hxi, hxw])) (by omega_using [hS', hfr, hxi])
                    (by omega_using [hW, hfr, hxw])
      u_o := by rw [e1]; exact (hp.k_p.sub_left (fr_sub (o := xOut) (n := w.ok.hH.SH.stateBytes)
                    (by omega_using [hS', hfr, hxo]))).sub_right hpS
      u_s := by rw [e1, e3]; exact fr_disj hp (.inl (by omega_using [hS', hxo, hxw])) (by omega_using [hS', hfr, hxo])
                    (by omega_using [hW, hfr, hxw])
      o_s := by rw [e3]; exact (hp.k_p.sub_left (fr_sub (o := xWork) (n := w.ok.Wf * 8)
                    (by omega_using [hW, hfr, hxw]))).sub_right hpS |>.symm
      b_i := by rw [hb, e0]; exact hp.st.disj (.inl (by omega_using [hxi])) (by decide)
                    (by omega_using [hS', hfr, hxi])
      b_u := by rw [hb, e1]; exact hp.st.disj (.inl (by omega_using [hxo])) (by decide)
                    (by omega_using [hS', hfr, hxo])
      b_o := by rw [hb]; exact (hp.k_p.sub_left hbs).sub_right hpS
      b_s := by rw [hb, e3]; exact hp.st.disj (.inl (by omega_using [hxw])) (by decide)
                    (by omega_using [hW, hfr, hxw])
      ni := by rw [fbN hp (by decide)]; omega_using [hS', hfr, hfN, hxi]
      nu := by rw [fbN hp (by decide)]; omega_using [hS', hfr, hfN, hxo]
      no := by rw [hdb, ← hp.pl]; exact hp.np
      nsc := by rw [fbN hp (by decide)]; omega_using [hW, hfr, hfN, hxw] }

theorem fin_ok (hw : HOk w) {t : State} (h : XFA w s t) : WP isa (callFin .r5 f) t (XF w s) := by
  have k := h.xu.xr
  have hfr := xFr_eq; have hS := hw.hS; have hW := hw.hW; have hxi := xIn_eq; have hxo := xOut_eq
  have hxw := xWork_eq; have hfN := fbN' hp; have hsb := stateBytes_eq w
  have hdb : w.ok.hH.SH.digestBytes = w.F.H.D := w.ok.hH.hD
  have hS' : w.ok.hH.SH.stateBytes ≤ 192 := by omega_using [hS, hsb]
  refine tcall_ok (n := w.F.hfN) (c := w.F.hfC) (tabFn hp k (j := 2) (by decide) hp.tm.2.2 hp.tok.f)
    fun u hu => ?_
  have ku : XR s u := k.upd hp hu (by decide)
  have e0 := fA_eq hp (o := xIn) (by decide)
  have e1 := fA_eq hp (o := xOut) (by decide)
  have e3 := fA_eq hp (o := xWork) (by decide)
  have hb := stk24 hp ku.sp
  have hbs : Region.Sub ⟨B s + BitVec.ofNat 64 8, 24⟩ (stkR s) := Offset.sub_base _ (by decide)
  have hpS : Region.Sub ⟨State.addr (stackArg s 0), w.ok.hH.SH.digestBytes⟩ (prkR s) :=
    Region.sub_prefix (by rw [hdb, hp.pl])
  apply WP.of_syms
  refine Proof.Pbkdf2.Whole.Arm.hf_frame (reprOK w) (by rw [hsb]; have := w.ok.hH.hSB; omega_using [this])
    w.ok.hf w.ok.hfSt (s := u) (inn := fb s + BitVec.ofNat 32 xIn) (ou := fb s + BitVec.ofNat 32 xOut)
    (o := stackArg s 0) (sc := fb s + BitVec.ofNat 32 xWork)
    (fin_args hp hw h hu) fun s' ha hpost sy => ?_
  have k' : XR s s' := ku.keep hp ha.rd ha.wr ha.sp sy (fun r hr => ha.cs r (xRegs_pres r hr).1 (xRegs_pres r hr).2)
    ha.frame fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [e0]; exact wk_fr (o := xIn) (n := w.ok.hH.SH.stateBytes) (by decide) (by omega_using [hS', hfr, hxi])
      · exact .inr (.inr hpS)
      · rw [e3]; exact wk_fr (o := xWork) (n := w.ok.Wf * 8) (by decide) (by omega_using [hW, hfr, hxw])
      · exact stk24_wk hp ku.sp
  have hm : u.mem = t.mem := hu.mem
  have hl : (k0Of w s).length = w.ok.hH.SH.H.blockSize := by rw [blockKey_len hw, w.ok.hH.hB]
  have hil : (ikmOf s).length = (s.gpr .r3).toNat := Proof.Hmac.Common.bytesAt_length _ _ _
  have hBl := ikm_lt hp (w := w)
  have := hpost (k0Of w s) (ikmOf s) hl (by rw [hl, hil, w.ok.hH.hB]; omega_using [hBl])
    (by rw [hm, e0]; exact h.xu.inn)
    (by rw [hu.other _ (by decide), hu.other _ (by decide), h.r3, h.r2, hil, w.ok.hH.hB,
          show BitVec.ofNat 32 w.F.H.B + s.gpr .r3 = BitVec.ofNat 32 (w.F.H.B + (s.gpr .r3).toNat) by
            rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]]
        exact append_zero (by omega_using [hBl]))
    (by rw [hm, e1]; exact h.xu.out)
  rw [hdb] at this
  exact ⟨k', this⟩

/-! ## The epilogue, and the function -/

omit hp in
theorem epi_eq : extractEpi = .addSp .r12 0 :: xSaved.map (fun p => Instr.ldr p.1 .r12 p.2) := rfl

omit hp in
theorem xSaved_restorable : Spill.Restorable .r12 xSaved := by decide

/-- The epilogue restores our caller's registers and our return address. -/
theorem epi_ok {t : State} (k : XR s t) :
    WP isa (.block extractEpi) t fun u => (∀ r ∈ preserved, u.gpr r = s.gpr r) ∧ u.sp = fb s ∧ u.mem = t.mem := by
  have hfr := xFr_eq
  rw [epi_eq]
  refine wp_addSp (by decide) fun t₁ u₁ => ?_
  have h12 : t₁.gpr .r12 = fb s := by rw [u₁.gpr, k.sp, BitVec.add_zero]
  rw [← List.append_nil (List.map _ xSaved)]
  refine Spill.restore_slots_ok xSaved_slots xSaved_restorable (g := s.gpr) (by
      rw [h12]; have h1 : (fb s).toNat + xFr = s.sp.toNat := hp.st.fbN; have := s.sp.isLt
      omega_using [h1, this, hfr])
    (fun d _ hd => by rw [h12, fb_add hp, u₁.rd, u₁.wr]; exact fr_in' hp k.wr (by omega_using [hd, hfr]))
    (by rw [h12, u₁.mem]; exact k.saved) fun u hr ho hm _ _ hsp => WP.block_nil ⟨fun r hr' => ?_, ?_, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Spill.restored_reg hr (by decide)
      | (rw [ho _ (by decide), u₁.other _ (by decide)]; exact k.cs _ (by decide))
  · rw [hsp, u₁.sp, k.sp]
  · rw [hm, u₁.mem]

end

/-- `vg_hkdf_extract` meets `extractR` and keeps the callee-saved registers
and the stack pointer. -/
theorem extract_correct {w : HVar} {f : Fns} {ns : List String} {s : State} (hw : HOk w)
    (hp : (extractR w f ns xStack).pre s) :
    WP isa (extract f) s fun s' => abiPreserved s s' ∧ (extractR w f ns xStack).post s s' := by
  have p := xp_of hp
  have hfr := xFr_eq
  unfold extract
  refine WP.alloc (by decide) (by have := p.sp; simp only [xStack] at this; omega_using [this]) ?_
  unfold extractMain
  refine WP.seq (WP.mono (pro_ok p) fun t₁ h₁ => WP.seq (WP.mono (init_ok p hw h₁) fun t₂ h₂ =>
    WP.seq (WP.mono (updArgs_ok p h₂) fun t₃ h₃ => WP.seq (WP.mono (upd_ok p hw h₃) fun t₄ h₄ =>
    WP.seq (WP.mono (finArgs_ok p h₄) fun t₅ h₅ => WP.seq (WP.mono (fin_ok p hw h₅) fun t₆ h₆ => ?_))))))
  refine WP.mono (epi_ok p h₆.xr) fun u ⟨hcs, hsp, hm⟩ m uk hfm => ⟨⟨fun r hr => hcs r hr, ?_⟩, ?_⟩
  · show u.sp + BitVec.ofNat 32 xFr = s.sp
    rw [hsp]; exact fb_xFr s
  · show bytesAt m (State.addr (stackArg s 0)) w.F.H.D = _
    have e : bytesAt m (State.addr (stackArg s 0)) w.F.H.D = bytesAt u.mem (State.addr (stackArg s 0)) w.F.H.D :=
      bytes_keep hfm (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [fb_addr p]; exact (p.k_p.sub_left (fr_sub (o := 0) (n := xFr) (by omega_using []))).symm.sub_left
          (Region.sub_prefix (by rw [p.pl])))
        (by have := (stackArg s 1).isLt; rw [← p.pl]; omega_using [this])
    rw [e, hm]
    exact h₆.prk

/-! ## Constant time -/

theorem pro_ck : Ck [.r12] (.block extractPro.tail) := ⟨_, by taint_decide⟩
theorem upd_ck : Ck [.r12, .r5] (.block extractUpd.tail) := ⟨_, by taint_decide⟩
theorem fin_ck : Ck [.r12, .r5] (.block extractFin.tail) := ⟨_, by taint_decide⟩
theorem epi_ck : Ck [.r12] (.block extractEpi.tail) := ⟨_, by taint_decide⟩

section
variable {w : HVar} {f : Fns} {ns : List String}

/-- `vg_hkdf_extract` is constant time: two runs whose public data agree leak
the same trace. -/
theorem extract_ct (hw : HOk w) (hns : ∀ n ∈ [w.F.hiAnyN, w.F.H.updN, w.F.hfN], n ∈ ns) :
    ConstantTime isa (extractR w f ns xStack).pre (extractR w f ns xStack).pub (extract f) := by
  refine RelCT.constantTime (Q := fun _ _ => True) fun e e' t₁ t₂ a b ⟨h, h', hpub⟩ e₁ e₂ => ?_
  obtain ⟨qsp, q0, q1, q2, q3, qa0, qa1, qa2, qn⟩ := hpub
  have hp := xp_of h
  have hp' := xp_of h'
  have hfb : fb e' = fb e := by simp only [fb, qsp]
  revert e₁ e₂
  generalize hP : (fun x y : State => x = e ∧ y = e') = Q
  suffices hr : RelCT isa Q (extract f) fun _ _ => True by
    intro e₁ e₂; exact hr _ _ _ _ _ _ (hP ▸ ⟨rfl, rfl⟩) e₁ e₂
  subst hP
  unfold extract extractMain
  refine RelCT.allocFrame ?_
  have r1 : RelCT isa (fun x y => ∃ s₁ s₂, (s₁ = e ∧ s₂ = e') ∧ x = allocated xFr s₁ ∧ y = allocated xFr s₂)
      (.block extractPro) fun x y => XA e x ∧ XA e' y := by
    refine ((rel_blk pro_ck fun x y hxy => ?_).wp fun x y hxy => ?_).mono (fun _ _ h => h) fun _ _ h => h.2
    · obtain ⟨s₁, s₂, ⟨e₁, e₂⟩, hx, hy⟩ := hxy
      subst e₁ e₂ hx hy; exact ⟨by simp only [allocated, qsp], fun _ h => absurd h List.not_mem_nil⟩
    · obtain ⟨s₁, s₂, ⟨e₁, e₂⟩, hx, hy⟩ := hxy
      subst e₁ e₂ hx hy; exact ⟨pro_ok hp, pro_ok hp'⟩
  have hsy : ∀ n ∈ [w.F.hiAnyN, w.F.H.updN, w.F.hfN], e.syms n = e'.syms n := fun n hn => qn n (hns n hn)
  -- `init`.
  have c1 : RelCT isa (fun x y => XA e x ∧ XA e' y) (tcall .r5 0 f.init [.r12, .lr] .r12 8) fun _ _ => True :=
    tcall_rel (fun x y ⟨xa, xa'⟩ => ⟨tabFn hp xa.xr (j := 0) (by decide) hp.tm.1 hp.tok.i,
        tabFn hp' xa'.xr (j := 0) (by decide) hp'.tm.1 hp'.tok.i, by rw [xa.xr.r5, xa'.xr.r5, qa2],
        by rw [xa.xr.sy, xa'.xr.sy, hsy _ (by simp)], by rw [xa.xr.sp, xa'.xr.sp, hfb]⟩)
      (any_rel w.any (sp := fb e) fun u u' hu => by
        obtain ⟨x, x', ⟨xa, xa'⟩, v, v'⟩ := hu
        have := init_args hp' hw xa' v'
        rw [hfb, ← q0, ← q1] at this
        exact ⟨init_args hp hw xa v, this, by rw [v.sp, xa.xr.sp], by rw [v'.sp, xa'.xr.sp, hfb]⟩)
  -- `update`'s arguments and `update`.
  have b2 : RelCT isa (fun x y => XI w e x ∧ XI w e' y) (.block extractUpd) fun _ _ => True :=
    rel_blk upd_ck fun x y ⟨xi, xi'⟩ => ⟨by rw [xi.xr.sp, xi'.xr.sp, hfb], fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [xi.xr.r5, xi'.xr.r5, qa2]⟩
  have c2 : RelCT isa (fun x y => XUA w e x ∧ XUA w e' y) (callUpd .r5 f) fun _ _ => True :=
    tcall_rel (fun x y ⟨xa, xa'⟩ => ⟨tabFn hp xa.xi.xr (j := 1) (by decide) hp.tm.2.1 hp.tok.u,
        tabFn hp' xa'.xi.xr (j := 1) (by decide) hp'.tm.2.1 hp'.tok.u, by rw [xa.xi.xr.r5, xa'.xi.xr.r5, qa2],
        by rw [xa.xi.xr.sy, xa'.xi.xr.sy, hsy _ (by simp)], by rw [xa.xi.xr.sp, xa'.xi.xr.sp, hfb]⟩)
      (Proof.Pbkdf2.Whole.Arm.upd_rel w.ok.hH (sp := fb e) fun u u' hu => by
        obtain ⟨x, x', ⟨xa, xa'⟩, v, v'⟩ := hu
        have := upd_args hp' hw xa' v'
        rw [hfb, ← q2, ← q3] at this
        refine ⟨upd_args hp hw xa v, this, ?_, by rw [v.sp, xa.xi.xr.sp], by rw [v'.sp, xa'.xi.xr.sp, hfb]⟩
        simp only [Pbkdf2.Stream.Arm.count]
        rw [v.other _ (by decide), v.other _ (by decide), v'.other _ (by decide), v'.other _ (by decide), xa.r2,
          xa.r3, xa'.r2, xa'.r3])
  -- `finalize`'s arguments and `finalize`.
  have b3 : RelCT isa (fun x y => XU w e x ∧ XU w e' y) (.block extractFin) fun _ _ => True :=
    rel_blk fin_ck fun x y ⟨xu, xu'⟩ => ⟨by rw [xu.xr.sp, xu'.xr.sp, hfb], fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [xu.xr.r5, xu'.xr.r5, qa2]⟩
  have c3 : RelCT isa (fun x y => XFA w e x ∧ XFA w e' y) (callFin .r5 f) fun _ _ => True :=
    tcall_rel (fun x y ⟨xa, xa'⟩ => ⟨tabFn hp xa.xu.xr (j := 2) (by decide) hp.tm.2.2 hp.tok.f,
        tabFn hp' xa'.xu.xr (j := 2) (by decide) hp'.tm.2.2 hp'.tok.f, by rw [xa.xu.xr.r5, xa'.xu.xr.r5, qa2],
        by rw [xa.xu.xr.sy, xa'.xu.xr.sy, hsy _ (by simp)], by rw [xa.xu.xr.sp, xa'.xu.xr.sp, hfb]⟩)
      (Proof.Pbkdf2.Whole.Arm.hf_rel w.ok.hf (sp := fb e) fun u u' hu => by
        obtain ⟨x, x', ⟨xa, xa'⟩, v, v'⟩ := hu
        have := fin_args hp' hw xa' v'
        rw [hfb, ← qa0] at this
        exact ⟨fin_args hp hw xa v, this, by rw [v.other _ (by decide), v'.other _ (by decide), xa.r2, xa'.r2, q3],
          by rw [v.other _ (by decide), v'.other _ (by decide), xa.r3, xa'.r3],
          by rw [v.sp, xa.xu.xr.sp], by rw [v'.sp, xa'.xu.xr.sp, hfb]⟩)
  have b4 : RelCT isa (fun x y => XF w e x ∧ XF w e' y) (.block extractEpi) fun _ _ => True :=
    rel_blk epi_ck fun x y ⟨xf, xf'⟩ => ⟨by rw [xf.xr.sp, xf'.xr.sp, hfb], fun _ h => absurd h List.not_mem_nil⟩
  exact r1.seq ((rel_both c1 (fun _ h => init_ok hp hw h) (fun _ h => init_ok hp' hw h)).seq
    ((rel_both b2 (fun _ h => updArgs_ok hp h) (fun _ h => updArgs_ok hp' h)).seq
    ((rel_both c2 (fun _ h => upd_ok hp hw h) (fun _ h => upd_ok hp' hw h)).seq
    ((rel_both b3 (fun _ h => finArgs_ok hp h) (fun _ h => finArgs_ok hp' h)).seq
    ((rel_both c3 (fun _ h => fin_ok hp hw h) (fun _ h => fin_ok hp' hw h)).seq b4)))))

end

end VG.Proof.Hkdf.Arm.Extract
