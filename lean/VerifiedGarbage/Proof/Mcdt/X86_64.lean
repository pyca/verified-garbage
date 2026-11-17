module

public import VerifiedGarbage.Impl.Mcdt.X86_64
public import VerifiedGarbage.Spec.Mcdt
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubOr
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.MlKem.X86_64.Rel
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Impl.Mcdt.X86_64
meta import VerifiedGarbage.Spec.Mcdt
meta import VerifiedGarbage.Proof.MlKem.X86_64.Wp
meta import VerifiedGarbage.Proof.MlKem.X86_64.Rel
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86_64.ResidueTaintSound

/-!
# Entering Intel's MXCSR mitigation of MCDT on x86-64: the proofs

`verified` proves `vg_mcdt_enter` against its contract (`Spec/Mcdt.lean`),
which says what every contract can: no memory written but its stack, the
calling convention's preserved state kept (MXCSR's control bits among it),
constant time with MXCSR public, as the contract makes it: it branches on
whether MXCSR held `0x1FBF` (`head_rel`), and otherwise its addresses are
`rsp`'s.

`enterReg` registers it, returning without secret residue.

`enter_mxcsr` proves what the contract cannot name, of every run of its
code in the model: MXCSR then holds the value it held on entry, but for its
reserved bits, with its six status flags set, and `eax` is 1 if that is
`0x1FBF` and 0 if not.
-/

@[expose] public section

namespace VG.Proof.Mcdt.X86_64
open VG VG.X86_64 VG.Impl.Mcdt.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep taintRel)

/-- What MXCSR holds after `vg_mcdt_enter`, from `x` on entry. -/
def flagged (x : BitVec 32) : BitVec 32 := (x &&& 0xFFFF) ||| 0x3F

/-- Its result, from MXCSR `x` on entry. -/
def res (x : BitVec 32) : BitVec 64 := if flagged x = 0x1FBF then 1 else 0

theorem flagged_hi (x : BitVec 32) : (flagged x).extractLsb' 16 16 = 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [flagged, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_and, hi,
    decide_true, Bool.true_and]
  rw [show (0xFFFF : BitVec 32).getLsbD (16 + i) = false by revert i; decide,
    show (0x3F : BitVec 32).getLsbD (16 + i) = false by revert i; decide]
  simp

/-- MXCSR's control bits (15:6) are those on entry. -/
theorem flagged_ctl (x : BitVec 32) : (flagged x).extractLsb' 6 10 = x.extractLsb' 6 10 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [flagged, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_and, hi,
    decide_true, Bool.true_and]
  rw [show (0xFFFF : BitVec 32).getLsbD (6 + i) = true by revert i; decide,
    show (0x3F : BitVec 32).getLsbD (6 + i) = false by revert i; decide]
  simp

theorem flagged_hi' (x : BitVec 32) : (x &&& 65535 ||| 63).extractLsb' 16 16 = 0 := flagged_hi x

theorem xor_beq (x : BitVec 32) :
    ((x &&& 65535 ||| 63) ^^^ 8127 == 0) = decide (flagged x = 0x1FBF) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  exact BitVec.xor_eq_zero_iff

theorem ea_slot (s : State) : s.ea slot = s.gpr .rsp := by
  simp [State.ea, slot]

theorem sub_beq (x : BitVec 32) : (x - 8127 == 0) = (x == 8127) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  constructor <;> intro h <;> bv_omega

/-- `head`: MXCSR in `eax`, compared with `0x1FBF`, through the slot. -/
theorem head_ok {s : State} (w0 : InRegions s.wr (s.gpr .rsp) 4) (w8 : InRegions s.wr (s.gpr .rsp) 8)
    (l0 : InRegions (s.rd ++ s.wr) (s.gpr .rsp) 4) :
    WP isa (.block head) s fun t => (t.mxcsr = s.mxcsr ∧ t.zf = some (s.mxcsr == 8127) ∧
      t.gpr .rax = s.mxcsr.setWidth 64 ∧
      t.mem = (s.mem.writeW (s.gpr .rsp) ((0 : BitVec 32).setWidth 64)).writeW (s.gpr .rsp) s.mxcsr) ∧
      Keep [.rax, .rdx] s t := by
  refine WP.keep [.rax, .rdx] ?_ rfl
  xrun [head, ea_slot, w0, w8, l0, Mem.readW_writeW_self32, RegUpd.mxcsr_setReg, RegUpd.mxcsr_setFlags,
    sub_beq]

/-- The memory after the frame's body, from `m` with the slot at `S` and
MXCSR `x`: the slot zeroed, then MXCSR stored in it, and `flagged x` unless
`x` is `0x1FBF`. -/
def slotW (m : Mem) (S : Addr) (x : BitVec 32) : Mem :=
  if x = 0x1FBF then (m.writeW S ((0 : BitVec 32).setWidth 64)).writeW S x
  else ((m.writeW S ((0 : BitVec 32).setWidth 64)).writeW S x).writeW S (flagged x)

/-- `slotW` leaves the bytes of the slot as functions of `S` and `x` alone. -/
theorem slotW_slot (m₁ m₂ : Mem) {S y : Addr} (x : BitVec 32) (hy : (y - S).toNat < 8) :
    slotW m₁ S x y = slotW m₂ S x y := by
  have hy' : ((y - S).toNat < 64 / 8) = True := eq_true hy
  unfold slotW
  split <;> simp only [Mem.writeW, Mem.write, hy', ↓reduceIte]

/-- `slotW` writes only the slot. -/
theorem slotW_frame {m : Mem} {S : Addr} {F : Region} (x : BitVec 32) (h0 : F.Contains S 4)
    (h8 : F.Contains S 8) : Frame [F] m (slotW m S x) := by
  have f1 : Frame [F] m ((m.writeW S ((0 : BitVec 32).setWidth 64)).writeW S x) :=
    ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ h8).writeW (List.mem_singleton_self _) _ h0
  unfold slotW
  split
  · exact f1
  · exact f1.writeW (List.mem_singleton_self _) _ h0

/-- The frame's body, from a state whose 8 bytes at `rsp` are writable. -/
theorem body_ok {s : State} {F : Region} (hF : F ∈ s.wr) (h0 : F.Contains (s.gpr .rsp) 4)
    (h8 : F.Contains (s.gpr .rsp) 8) :
    WP isa body s fun s' => (s'.mxcsr = flagged s.mxcsr ∧ s'.gpr .rax = res s.mxcsr ∧
      s'.mem = slotW s.mem (s.gpr .rsp) s.mxcsr) ∧ Keep [.rax, .rdx] s s' := by
  have w0 : InRegions s.wr (s.gpr .rsp) 4 := ⟨F, hF, h0⟩
  have w8 : InRegions s.wr (s.gpr .rsp) 8 := ⟨F, hF, h8⟩
  have l0 : InRegions (s.rd ++ s.wr) (s.gpr .rsp) 4 := ⟨F, List.mem_append_right _ hF, h0⟩
  unfold body
  refine WP.seq (WP.mono (head_ok w0 w8 l0) fun t ⟨⟨hmx, hzf, hax, hm⟩, k1⟩ => ?_)
  have tsp : t.gpr .rsp = s.gpr .rsp := k1.gpr (by decide)
  have tw0 : InRegions t.wr (t.gpr .rsp) 4 := by rw [tsp, k1.2.2]; exact w0
  have tl0 : InRegions (t.rd ++ t.wr) (t.gpr .rsp) 4 := by rw [tsp, k1.2.1, k1.2.2]; exact l0
  by_cases hf : s.mxcsr = 0x1FBF
  · have hfl : flagged s.mxcsr = s.mxcsr := by rw [hf]; decide
    have hr : res s.mxcsr = 1 := by rw [res, hf]; decide
    refine WP.ite true (by simp [eval, hzf, hf]) (fun _ => ?_) (fun h => nomatch h)
    refine WP.mono (WP.keep [.rax, .rdx] (Q := fun u => u.mxcsr = t.mxcsr ∧ u.gpr .rax = 1 ∧ u.mem = t.mem)
      (by xrun [RegUpd.mxcsr_setReg]) rfl) fun u ⟨⟨hu, hua, hum⟩, k2⟩ => ⟨⟨by rw [hu, hmx, hfl], by rw [hua, hr],
        by rw [hum, hm, slotW]; simp only [hf, ↓reduceIte]⟩, (k1.trans k2).mono (by decide)⟩
  · have hx := xor_beq s.mxcsr
    have hax32 : (t.gpr .rax).setWidth 32 = s.mxcsr := by rw [hax]; exact RegUpd.setWidth_setWidth_32 _
    refine WP.ite false (by simp only [eval, hzf, beq_eq_false_iff_ne.mpr hf]) (fun h => nomatch h) (fun _ => ?_)
    by_cases hg : flagged s.mxcsr = 0x1FBF
    · have hr : res s.mxcsr = 1 := by simp only [res, hg, ite_true]
      rw [decide_eq_true hg] at hx
      refine WP.mono (WP.keep [.rax, .rdx] (Q := fun u => u.mxcsr = flagged s.mxcsr ∧ u.gpr .rax = res s.mxcsr ∧
        u.mem = t.mem.writeW (t.gpr .rsp) (flagged s.mxcsr)) (by
          xrun [raise, answer, List.cons_append, List.nil_append, ea_slot, tw0, tl0, hax32, Mem.readW_writeW_self32,
            flagged_hi', execCmov, eval, hx, hr, RegUpd.mxcsr_setReg, RegUpd.mxcsr_setFlags, flagged]) rfl)
        fun u ⟨⟨hu, hua, hum⟩, k2⟩ => ⟨⟨hu, hua, by rw [hum, hm, tsp, slotW]; simp only [hf, ↓reduceIte]⟩,
          (k1.trans k2).mono (by decide)⟩
    · have hr : res s.mxcsr = 0 := by simp only [res, hg, ite_false]
      rw [decide_eq_false hg] at hx
      refine WP.mono (WP.keep [.rax, .rdx] (Q := fun u => u.mxcsr = flagged s.mxcsr ∧ u.gpr .rax = res s.mxcsr ∧
        u.mem = t.mem.writeW (t.gpr .rsp) (flagged s.mxcsr)) (by
          xrun [raise, answer, List.cons_append, List.nil_append, ea_slot, tw0, tl0, hax32, Mem.readW_writeW_self32,
            flagged_hi', execCmov, eval, hx, hr, RegUpd.mxcsr_setReg, RegUpd.mxcsr_setFlags, flagged]) rfl)
        fun u ⟨⟨hu, hua, hum⟩, k2⟩ => ⟨⟨hu, hua, by rw [hum, hm, tsp, slotW]; simp only [hf, ↓reduceIte]⟩,
          (k1.trans k2).mono (by decide)⟩

/-- Two 8-byte regions, the second just below the first. -/
theorem disj8 (S : Addr) : Region.Disjoint ⟨S, 8⟩ ⟨S - 8, 8⟩ := by
  intro x hx hy
  simp only [Region.Contains] at hx hy
  bv_omega

/-- From a state with 8 bytes of stack below `rsp`, `vg_mcdt_enter` runs and
ends with MXCSR `flagged`, `rax` `res` of MXCSR on entry, the callee-saved
registers and the return address kept, and the regions as they were. -/
theorem enter_wp (s : State) (hS : 8 ≤ (s.gpr .rsp).toNat) :
    WP isa enter s fun t => t.mxcsr = flagged s.mxcsr ∧ t.gpr .rax = res s.mxcsr ∧
      gprPreserved s t ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  generalize hSdef : s.gpr .rsp = S at *
  let F : Region := ⟨S - 8, 8⟩
  have s1sp : (pushed [.rax] s).gpr .rsp = S - 8 := by rw [pushed_rsp, hSdef]; rfl
  have hF : F ∈ (pushed [.rax] s).wr := by
    rw [pushed_wr, hSdef]; exact List.mem_cons_self
  have h0' : F.Contains (S - 8) 4 := by
    simp only [F, Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  have h8' : F.Contains (S - 8) 8 := by
    simp only [F, Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  have h0 : F.Contains ((pushed [.rax] s).gpr .rsp) 4 := by rw [s1sp]; exact h0'
  have h8 : F.Contains ((pushed [.rax] s).gpr .rsp) 8 := by rw [s1sp]; exact h8'
  obtain ⟨pf, -⟩ := pushRegs_mem s [.rax] (by decide) (by rw [hSdef]; simpa using hS)
  rw [hSdef] at pf
  unfold enter
  refine WP.frame (by decide) (by decide) (by decide) (by rw [hSdef]; simpa using hS) ?_
  refine WP.mono (body_ok hF h0 h8) fun t ⟨⟨hmx, hax, hm⟩, hk⟩ => ?_
  have tsp : t.gpr .rsp = S - 8 := by rw [hk.gpr (by decide), s1sp]
  refine ⟨by rw [tsp, s1sp], by rw [hk.2.2], fun m u fm => ?_⟩
  have fr : Frame [F] s.mem t.mem := pf.trans (hm ▸ slotW_frame _ h0 h8)
  -- The `pop` loses the frame's bytes, which are `F`'s.
  rw [hSdef] at fm
  have fr' : Frame [F] s.mem m := fr.trans fm
  dsimp only
  refine ⟨by rw [popped_mxcsr, hmx, pushed_mxcsr], ?_, ⟨fun r hr => ?_, ?_⟩, ?_, ?_⟩
  · rw [popped_gpr _ _ _ (by decide) (by decide), hax, pushed_mxcsr]
  · have hrc : r ≠ .rcx := by intro h; subst h; simp [calleeSaved] at hr
    by_cases hsp : r = .rsp
    · subst hsp; rw [popped_rsp, tsp, hSdef]; exact BitVec.sub_add_cancel S 8
    · rw [popped_gpr _ _ _ hsp hrc, hk.gpr (by cases r <;> simp_all [calleeSaved]), pushed_gpr _ _ hsp]
  · rw [hSdef]
    exact fr'.readW (r := ⟨S, 8⟩) (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact disj8 S) (by decide)
  · rw [popped_rd, hk.2.1, pushed_rd]
  · rw [popped_wr, hk.2.2, pushed_wr]; rfl

/-- No instruction of the release of a frame. -/
def notRelease : Instr → Bool
  | .pop .. | .free _ => false
  | _ => true

theorem pop_release {j : Instr} {s₁ s₂ s' : State} (hj : notRelease j = true)
    (hq : isa.pop j s₁ s₂ = some s') : False := by
  cases j <;> simp only [notRelease, Bool.false_eq_true] at hj <;>
    simp only [isa, pop, reduceCtorEq] at hq

/-- The frame's body, which releases no frame, keeps the unknowns. -/
theorem body_unk {s s' : State} {t : List Leak} (h : Exec isa body s t s') : s'.unknowns = s.unknowns :=
  Exec.keep (fun s : State => s.unknowns) (ok := fun i => notRelease i = true)
    (fun _ he => RTaint.exec_unknowns he)
    (fun hj _ hq _ => (pop_release hj hq).elim)
    (fun i hi => List.all_eq_true.mp (by decide : (instrs body).all notRelease = true) i hi)
    (.inl (by decide)) h

/-- `enter_wp`, with the registers `vg_mcdt_enter` keeps (all but `rax`,
`rcx` and `rdx`) and its memory: the stack, as the frame's body leaves it,
the 8 bytes below `rsp` (`slotW`), whose bytes the frame's pop then loses
(`lose`, with the two unknowns it takes). -/
theorem enter_wpX (s : State) (hS : 8 ≤ (s.gpr .rsp).toNat) :
    WP isa enter s fun t => t.mxcsr = flagged s.mxcsr ∧ t.gpr .rax = res s.mxcsr ∧
      t.gpr .rsp = s.gpr .rsp ∧ (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧
      t.mem = lose (slotW (pushed [.rax] s).mem (s.gpr .rsp - 8) s.mxcsr) (s.gpr .rsp - 8) 8 s.unknowns ∧
      t.unknowns = fun n => s.unknowns (n + 2) := by
  generalize hSdef : s.gpr .rsp = S at *
  let F : Region := ⟨S - 8, 8⟩
  have s1sp : (pushed [.rax] s).gpr .rsp = S - 8 := by rw [pushed_rsp, hSdef]; rfl
  have hF : F ∈ (pushed [.rax] s).wr := by
    rw [pushed_wr, hSdef]; exact List.mem_cons_self
  have h0' : F.Contains (S - 8) 4 := by
    simp only [F, Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  have h8' : F.Contains (S - 8) 8 := by
    simp only [F, Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  have h0 : F.Contains ((pushed [.rax] s).gpr .rsp) 4 := by rw [s1sp]; exact h0'
  have h8 : F.Contains ((pushed [.rax] s).gpr .rsp) 8 := by rw [s1sp]; exact h8'
  unfold enter
  refine WP.frameMem (by decide) (by decide) (by decide) (by rw [hSdef]; simpa using hS) ?_
  obtain ⟨tr, t, he, ⟨hmx, hax, hm⟩, hk⟩ := body_ok hF h0 h8
  have hu : t.unknowns = s.unknowns := (body_unk he).trans rfl
  refine ⟨tr, t, he, ?_⟩
  have tsp : t.gpr .rsp = S - 8 := by rw [hk.gpr (by decide), s1sp]
  refine ⟨by rw [tsp, s1sp], by rw [hk.2.2], ?_⟩
  dsimp only [released]
  refine ⟨by rw [popped_mxcsr, hmx, pushed_mxcsr], ?_, ?_, fun r h1 h2 h3 => ?_, ?_, ?_, ?_, ?_⟩
  · rw [popped_gpr _ _ _ (by decide) (by decide), hax, pushed_mxcsr]
  · rw [popped_rsp, tsp]; exact BitVec.sub_add_cancel S 8
  · by_cases hsp : r = .rsp
    · subst hsp; rw [popped_rsp, tsp, hSdef]; exact BitVec.sub_add_cancel S 8
    · rw [popped_gpr _ _ _ hsp h2, hk.gpr (by simp [h1, h3]), pushed_gpr _ _ hsp]
  · rw [popped_rd, hk.2.1, pushed_rd]
  · rw [popped_wr, hk.2.2, pushed_wr]; rfl
  · rw [hm, s1sp, pushed_mxcsr, tsp, hu, List.length_singleton]
  · rw [hu, List.length_singleton]

/-- MXCSR after `vg_mcdt_enter` is `0x1FBF` exactly when its control bits
on entry are the default, `0x1F80`'s. -/
theorem flagged_eq_iff (x : BitVec 32) :
    flagged x = 0x1FBF ↔ x.extractLsb' 6 10 = (0x1F80 : BitVec 32).extractLsb' 6 10 := by
  constructor
  · intro h; rw [← flagged_ctl, h]; decide
  · intro h
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    have hb := congrArg (fun v : BitVec 10 => v.getLsbD (i - 6)) h
    simp only [BitVec.getLsbD_extractLsb'] at hb
    simp only [flagged, BitVec.getLsbD_or, BitVec.getLsbD_and]
    by_cases h6 : i < 6
    · clear hb
      have a : (63 : BitVec 32).getLsbD i = true := by revert i; decide
      have b : (8127 : BitVec 32).getLsbD i = true := by revert i; decide
      rw [a, b, Bool.or_true]
    · by_cases h16 : i < 16
      · have e : 6 + (i - 6) = i := by omega
        have hl : i - 6 < 10 := by omega
        simp only [hl, decide_true, Bool.true_and, e] at hb
        rw [hb]; clear hb; revert i; decide
      · clear hb
        have a : (63 : BitVec 32).getLsbD i = false := by revert i; decide
        have b : (8127 : BitVec 32).getLsbD i = false := by revert i; decide
        have c : (65535 : BitVec 32).getLsbD i = false := by revert i; decide
        rw [a, b, c, Bool.and_false, Bool.or_false]

/-- Every run of `vg_mcdt_enter`, from a state with 8 bytes of stack below
`rsp`, ends with MXCSR the value it held on entry, but for its reserved
bits, with its six status flags set (`flagged`), and with `eax` 1 if that is
`0x1FBF` (`flagged_eq_iff`: MXCSR's control bits on entry were the
default) and 0 if not. -/
theorem enter_mxcsr {s s' : State} {t : List Leak} (hS : 8 ≤ (s.gpr .rsp).toNat)
    (h : Exec isa enter s t s') :
    s'.mxcsr = flagged s.mxcsr ∧ s'.gpr .rax = if flagged s.mxcsr = 0x1FBF then 1 else 0 := by
  obtain ⟨_, _, he, hq⟩ := enter_wp s hS
  rw [(Exec.det h he).2]
  exact ⟨hq.1, hq.2.1⟩

/-- The contract `vg_mcdt_enter` is proven against, which implies its own:
no buffer, 8 bytes of stack, the stack pointer and MXCSR public. -/
def contract : Contract isa where
  pre s := s.rd = [] ∧ s.wr = [] ∧ 8 ≤ (s.gpr .rsp).toNat
  post _ _ := True
  pub s t := s.gpr .rsp = t.gpr .rsp ∧ s.mxcsr = t.mxcsr

/-- After `head`, two runs from states agreeing on `rsp` and MXCSR agree on
`rsp` and ZF: they take the same branch. -/
theorem head_rel :
    RelCT isa (fun a b => ∃ s₁ s₂, (contract.pre s₁ ∧ contract.pre s₂ ∧ contract.pub s₁ s₂) ∧
      a = pushed [.rax] s₁ ∧ b = pushed [.rax] s₂) (.block head)
      fun x y => x.gpr .rsp = y.gpr .rsp ∧ x.zf = y.zf := by
  have h₀ := taintRel (P := fun a b => ∃ s₁ s₂, (contract.pre s₁ ∧ contract.pre s₂ ∧ contract.pub s₁ s₂) ∧
      a = pushed [.rax] s₁ ∧ b = pushed [.rax] s₂) (c := .block head) [.rsp] (fun x y h r hr => by
    obtain ⟨s₁, s₂, ⟨-, -, hp, -⟩, rfl, rfl⟩ := h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
    rw [pushed_rsp, pushed_rsp, hp]) (by taint_decide)
  have hw : ∀ σ : State, 8 ≤ (σ.gpr .rsp).toNat → WP isa (.block head) (pushed [.rax] σ) fun t =>
      t.gpr .rsp = (pushed [.rax] σ).gpr .rsp ∧ t.zf = some ((pushed [.rax] σ).mxcsr == 8127) := fun σ hS => by
    have s1sp : (pushed [.rax] σ).gpr .rsp = σ.gpr .rsp - 8 := by rw [pushed_rsp]; rfl
    have hF : (⟨σ.gpr .rsp - 8, 8⟩ : Region) ∈ (pushed [.rax] σ).wr := by
      rw [pushed_wr]; exact List.mem_cons_self
    have c4 : (⟨σ.gpr .rsp - 8, 8⟩ : Region).Contains ((pushed [.rax] σ).gpr .rsp) 4 := by
      rw [s1sp]; simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
    have c8 : (⟨σ.gpr .rsp - 8, 8⟩ : Region).Contains ((pushed [.rax] σ).gpr .rsp) 8 := by
      rw [s1sp]; simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
    exact WP.mono (head_ok ⟨_, hF, c4⟩ ⟨_, hF, c8⟩ ⟨_, List.mem_append_right _ hF, c4⟩)
      fun t ⟨⟨_, hz, _⟩, k⟩ => ⟨k.gpr (by decide), hz⟩
  refine (RelCT.wpDep h₀ (F := fun (σ t : State) => t.gpr .rsp = σ.gpr .rsp ∧ t.zf = some (σ.mxcsr == 8127))
    fun a b h => ?_).mono (fun _ _ h => h) ?_
  · obtain ⟨s₁, s₂, ⟨h₁, h₂, -⟩, rfl, rfl⟩ := h
    exact ⟨hw s₁ h₁.2.2, hw s₂ h₂.2.2⟩
  · rintro x y ⟨-, σ₁, σ₂, ⟨s₁, s₂, ⟨-, -, hsp, hmx⟩, rfl, rfl⟩, ⟨r₁, z₁⟩, ⟨r₂, z₂⟩⟩
    exact ⟨by rw [r₁, r₂, pushed_rsp, pushed_rsp, hsp], by rw [z₁, z₂, pushed_mxcsr, pushed_mxcsr, hmx]⟩

/-- A state satisfying `contract.pre`. -/
def sat : State where
  gpr r := match r with | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := []

/-- `vg_mcdt_enter` against `contract`: its runs keep what the calling
convention preserves. -/
theorem enter_correct : ∀ s, contract.pre s → ∃ t s', Exec isa enter s t s' ∧ abiPreserved s s' ∧
    contract.post s s' := by
  intro s hp
  obtain ⟨tr, t, he, hmx, -, hg, -⟩ := enter_wp s hp.2.2
  exact ⟨tr, t, he, ⟨hg.1, hg.2, by rw [hmx, flagged_ctl]⟩, trivial⟩

/-- `vg_mcdt_enter` is constant time, with `rsp` and MXCSR public. -/
theorem enter_ct : ConstantTime isa contract.pre contract.pub enter := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  unfold enter body
  refine RelCT.frame (R := fun _ _ => True) (fun _ _ h => h.2.2.1) ?_
  refine RelCT.seq head_rel (RelCT.ite (fun x y h => by simp only [eval, h.2]) ?_ ?_) <;>
  · exact taintRel [.rsp] (fun x y h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; exact h.1.1) (by taint_decide)

theorem verified : Verified target enter (Spec.Mcdt.enterContract abi 8) := by
  apply Verified.of_correct (k := contract) enter_correct enter_ct
  · exact {
      pre := by sig_implies_pre [Spec.Mcdt.enterContract, Spec.Mcdt.enterSig, Abi.withMode, contract, abi,
        argRegs]
      -- Both postconditions are `True`.
      post := fun _ _ _ _ => trivial
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Spec.Mcdt.enterContract, Spec.Mcdt.enterSig, Abi.withMode, abi, argRegs] at h
        sig_split h
        exact ⟨by with_reducible assumption, BitVec.eq_of_toNat_eq (by with_reducible assumption)⟩
      sat := by sig_implies_sat [Spec.Mcdt.enterContract, Spec.Mcdt.enterSig, Abi.withMode, contract, abi,
        argRegs] [sat] using sat }

theorem enterOut : Scrub.PostOut (Spec.Mcdt.enterContract abi 8) (Spec.Mcdt.enterSig.retBits 64) :=
  Scrub.postOut_of_local (leak := none) (Scrub.ScrubAbi.plain.mode true) fun vs _ _ _ _ hlen _ h => by
    obtain rfl := List.eq_nil_of_length_eq_zero hlen
    exact h

/-- `vg_mcdt_enter`, its registers and its 8 bytes of stack cleared before
it returns (`RScrub.withScrubAllR`, which follows MXCSR through the code:
every `ldmxcsr` loads what two runs agree on). -/
def enterReg : Registration Spec.Mcdt.enterApi X86_64.target :=
  RScrub.withScrubAllR { code := enter, stack := 8, verified := verified } enterOut

end VG.Proof.Mcdt.X86_64
